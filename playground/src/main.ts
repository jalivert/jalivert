import './styles.css'
import { marked } from 'marked'
import { PROJECTS, type ProjectDef } from './projects'
import type { Engine } from './engines/engine'
import { CrtTerminal } from './ui/terminal'
import { createEditor, type CodeEditor } from './ui/editor'
import { FileStore } from './ui/files'

const $ = <T extends HTMLElement = HTMLElement>(id: string): T => {
  const el = document.getElementById(id)
  if (!el) throw new Error(`missing #${id}`)
  return el as T
}

const extOf = (p: ProjectDef): string => p.defaultFile.split('.').pop() ?? 'txt'

let project: ProjectDef = PROJECTS[0]!
let engine: Engine = project.engine()
let editor: CodeEditor
let term: CrtTerminal
let store: FileStore
let currentFile = ''
let halted = false
let busy = false
// Bumped on every engine (re)boot (project switch, `start`, file reset).
// An in-flight `handle()` that resolves after the bump belongs to the old
// engine: its output/prompt/halted state must not leak into the new REPL.
let replGen = 0

function renderReadme(): void {
  $('readme-body').innerHTML = marked.parse(project.readme) as string
  $('quickref').innerHTML = project.quickref
  $('readme-title').textContent = project.name
  const gh = $('proj-gh') as HTMLAnchorElement
  gh.href = project.github
  gh.title = `${project.name} upstream repository`
}

function setReplState(s: string): void {
  $('repl-state').textContent = s
  $('run-lamp').classList.toggle('on', s.startsWith('running'))
}

function dismissBoot(): void {
  const boot = $('boot')
  if (boot.hidden) return
  boot.hidden = true
  term.focus()
}

function bootEngine(printBanner: boolean): void {
  // Stop any in-flight computation on the outgoing engine before replacing it.
  engine.interrupt()
  replGen++
  busy = false
  engine = project.engine()
  store.syncEngine((n, c) => engine.provideFile(n, c))
  engine.setEditorContent(store.readSaved(currentFile))
  halted = false
  term.setHalted(false)
  setReplState('ready')
  if (printBanner) {
    term.clear()
    term.println(engine.banner())
    term.println('Files live in the sidebar — Ctrl+S saves. See the command bar above for how to run them.')
    term.showPrompt(engine.prompt())
  }
}

// ------------------------------------------------------------ REPL ---

async function submitLine(line: string): Promise<void> {
  if (line === '\x03') {
    // Ctrl+C: interrupt a running computation, otherwise drop to a fresh prompt
    if (busy) {
      engine.interrupt()
      return
    }
    if (!halted) term.showPrompt(engine.prompt())
    return
  }
  if (busy) return // input echo stays, but nothing is submitted mid-computation
  if (halted) {
    if (line.trim() === 'start') {
      bootEngine(true)
      return
    }
    term.println('Program has terminated. Type `start` to start it again.')
    return
  }
  busy = true
  setReplState('running… (Ctrl+C interrupts)')
  const gen = replGen
  const eng = engine
  let res
  try {
    res = await eng.handle(line)
  } finally {
    if (gen === replGen) busy = false
  }
  if (gen !== replGen) return // project switched (or engine rebooted) mid-computation: drop the stale result
  if (res.output) term.println(res.output)
  if (res.interrupted) {
    setReplState('ready')
    term.showPrompt(engine.prompt())
    return
  }
  if (res.halted) {
    halted = true
    term.setHalted(true)
    setReplState('halted — type `start`');
    term.println('-- PROGRAM TERMINATED -- Type `start` to start it again.')
    return
  }
  setReplState('ready')
  term.showPrompt(engine.prompt())
}

// ------------------------------------------------------------ files ---

function openFile(name: string): void {
  if (!store.list().includes(name)) return
  if (currentFile) store.stash(currentFile, editor.getValue())
  currentFile = name
  editor.setValue(store.readOpen(name))
  engine.setEditorContent(store.readSaved(name))
  renderFilebar()
  updateSaveState()
}

function saveCurrent(): void {
  if (!currentFile) return
  store.save(currentFile, editor.getValue())
  engine.provideFile(currentFile, store.readSaved(currentFile))
  engine.setEditorContent(store.readSaved(currentFile))
  renderFilebar()
  updateSaveState()
}

/** Re-push all saved files; drop engine copies of files that no longer exist. */
function resyncFiles(before: string[]): void {
  store.syncEngine((n, c) => engine.provideFile(n, c))
  for (const name of before) {
    if (!store.list().includes(name)) engine.dropFile(name)
  }
  if (currentFile) engine.setEditorContent(store.readSaved(currentFile))
}

function updateSaveState(): void {
  const el = $('save-state')
  const dirty = !!currentFile && store.isDirty(currentFile, editor.getValue())
  el.textContent = dirty ? '● UNSAVED' : 'SAVED'
  el.classList.toggle('dirty', dirty)
  // light dot update without rebuilding the list (safe during rename)
  document.querySelectorAll<HTMLLIElement>('#file-list li').forEach((li) => {
    const name = li.dataset.file!
    const d = li.querySelector('.dirty')
    const isDirty =
      name === currentFile ? dirty : store.isDirty(name)
    d?.classList.toggle('clean', !isDirty)
  })
}

function renderFilebar(): void {
  const ul = $('file-list')
  ul.innerHTML = ''
  for (const name of store.list()) {
    const li = document.createElement('li')
    li.dataset.file = name
    if (name === currentFile) li.classList.add('active')

    const dot = document.createElement('span')
    dot.className = 'dirty' + (store.isDirty(name, name === currentFile ? editor.getValue() : undefined) ? '' : ' clean')
    dot.textContent = '●'
    li.appendChild(dot)

    const label = document.createElement('span')
    label.className = 'fname'
    label.textContent = name
    label.title = `${name} — double-click to rename`
    label.ondblclick = (e) => {
      e.stopPropagation()
      startRename(li, name)
    }
    li.appendChild(label)

    const del = document.createElement('button')
    del.className = 'del'
    del.textContent = '×'
    del.title = `Delete ${name}`
    del.onclick = (e) => {
      e.stopPropagation()
      const before = store.list()
      const idx = before.indexOf(name)
      store.remove(name)
      engine.dropFile(name)
      resyncFiles(before)
      if (currentFile === name) {
        const rest = store.list()
        currentFile = rest[Math.min(idx, rest.length - 1)]!
        editor.setValue(store.readOpen(currentFile))
        engine.setEditorContent(store.readSaved(currentFile))
      }
      renderFilebar()
      updateSaveState()
      editorLayout()
    }
    li.appendChild(del)

    li.onclick = () => {
      if (currentFile !== name) {
        openFile(name)
        editorLayout()
      }
    }
    ul.appendChild(li)
  }
}

function startRename(li: HTMLLIElement, oldName: string): void {
  const label = li.querySelector('.fname')
  if (!label || li.querySelector('.rename-box')) return
  const input = document.createElement('input')
  input.className = 'rename-box'
  input.value = oldName
  input.setAttribute('spellcheck', 'false')
  const commit = () => {
    const before = store.list()
    const finalName = store.rename(oldName, input.value)
    if (finalName !== oldName) {
      engine.provideFile(finalName, store.readSaved(finalName))
      resyncFiles([...before])
      if (currentFile === oldName) currentFile = finalName
    }
    renderFilebar()
    updateSaveState()
  }
  input.onkeydown = (e) => {
    e.stopPropagation()
    if (e.key === 'Enter') commit()
    if (e.key === 'Escape') {
      renderFilebar()
      updateSaveState()
    }
  }
  input.onblur = commit
  label.replaceWith(input)
  input.focus()
  input.select()
}

function editorLayout(): void {
  editor.layout()
  term.fit()
}

// ------------------------------------------------------------ layout ---

interface LayoutState {
  readmeW: number
  termW: number
  collapsed: boolean
}

const layout: LayoutState = { readmeW: 340, termW: 430, collapsed: false }

const STORAGE_VERSION = 'v2'
const layoutKey = `pltt.${STORAGE_VERSION}.layout`

function loadLayout(): void {
  try {
    const raw = localStorage.getItem(layoutKey) ?? localStorage.getItem('pltt.layout')
    if (!raw) return
    const o = JSON.parse(raw) as Partial<LayoutState>
    if (typeof o.readmeW === 'number') layout.readmeW = Math.min(700, Math.max(180, o.readmeW))
    if (typeof o.termW === 'number') layout.termW = Math.min(900, Math.max(260, o.termW))
    layout.collapsed = !!o.collapsed
    try {
      localStorage.setItem(layoutKey, raw)
      localStorage.removeItem('pltt.layout')
    } catch {
      /* ignore */
    }
  } catch {
    /* corrupted storage: ignore */
  }
}

function persistLayout(): void {
  try {
    localStorage.setItem(layoutKey, JSON.stringify(layout))
  } catch {
    /* storage blocked: session-only */
  }
}

function applyLayout(): void {
  $('readme-pane').style.width = `${layout.readmeW}px`
  $('term-pane').style.width = `${layout.termW}px`
  $('readme-pane').hidden = layout.collapsed
  $('gutter-1').style.display = layout.collapsed ? 'none' : ''
  $('readme-rail').hidden = !layout.collapsed
  editorLayout()
}

let fitQueued = false
function refitSoon(): void {
  if (fitQueued) return
  fitQueued = true
  requestAnimationFrame(() => {
    fitQueued = false
    editorLayout()
  })
}

function makeDraggable(gutterId: string, onDrag: (dx: number) => void): void {
  const gutter = $(gutterId)
  gutter.addEventListener('pointerdown', (e) => {
    e.preventDefault()
    try {
      gutter.setPointerCapture(e.pointerId)
    } catch {
      /* ignore */
    }
    let lastX = e.clientX
    gutter.classList.add('drag')
    const move = (ev: PointerEvent) => {
      onDrag(ev.clientX - lastX)
      lastX = ev.clientX
      refitSoon()
    }
    const up = () => {
      gutter.classList.remove('drag')
      gutter.removeEventListener('pointermove', move)
      gutter.removeEventListener('pointerup', up)
      gutter.removeEventListener('pointercancel', up)
      persistLayout()
      editorLayout()
    }
    gutter.addEventListener('pointermove', move)
    gutter.addEventListener('pointerup', up)
    gutter.addEventListener('pointercancel', up)
  })
}

// ------------------------------------------------------------ chrome ---

function switchProject(id: string): void {
  const next = PROJECTS.find((p) => p.id === id)
  if (!next) return
  if (currentFile) store.stash(currentFile, editor.getValue())
  project = next
  document.querySelectorAll('#picker button').forEach((b) => {
    b.classList.toggle('active', (b as HTMLButtonElement).dataset.id === id)
  })
  renderReadme()
  store = new FileStore(project.id, extOf(project), project.examples)
  editor.setLanguage(project.editorLang)
  currentFile = store.list()[0]!
  editor.setValue(store.readOpen(currentFile))
  renderFilebar()
  updateSaveState()
  refreshSymbolBar()
  bootEngine(true)
  term.focus()
}

function refreshSymbolBar(): void {
  const bar = $('symbol-bar')
  bar.innerHTML = ''
  bar.hidden = project.symbols.length === 0
  for (const s of project.symbols) {
    const b = document.createElement('button')
    b.textContent = s
    b.title = `Insert ${s}`
    b.onclick = () => editor.insert(s)
    bar.appendChild(b)
  }
}

function main(): void {
  // picker
  const picker = $('picker')
  for (const p of PROJECTS) {
    const b = document.createElement('button')
    b.textContent = p.name
    b.dataset.id = p.id
    b.title = p.tagline
    b.onclick = () => switchProject(p.id)
    picker.appendChild(b)
  }

  // terminal + editor + files
  term = new CrtTerminal($('terminal'))
  term.onSubmit(submitLine)
  store = new FileStore(project.id, extOf(project), project.examples)
  editor = createEditor($('editor'), project.editorLang, '')
  currentFile = store.list()[0]!
  editor.setValue(store.readOpen(currentFile))
  editor.onChange(() => {
    store.stash(currentFile, editor.getValue())
    updateSaveState()
  })
  editor.onSave(() => saveCurrent())
  window.addEventListener('keydown', (e) => {
    if ((e.ctrlKey || e.metaKey) && e.key.toLowerCase() === 's') {
      const t = e.target as HTMLElement | null
      if (t && (t.tagName === 'INPUT' || t.tagName === 'TEXTAREA' || t.tagName === 'SELECT')) return
      if (t && t.closest('.monaco-editor')) return // monaco command handles it
      e.preventDefault()
      saveCurrent()
    }
  })

  renderReadme()
  renderFilebar()
  updateSaveState()
  refreshSymbolBar()
  document.querySelectorAll('#picker button')[0]?.classList.add('active')

  loadLayout()
  bootEngine(true)
  applyLayout()

  makeDraggable('gutter-1', (dx) => {
    layout.readmeW = Math.min(700, Math.max(180, layout.readmeW + dx))
    $('readme-pane').style.width = `${layout.readmeW}px`
  })
  makeDraggable('gutter-2', (dx) => {
    layout.termW = Math.min(900, Math.max(260, layout.termW - dx))
    $('term-pane').style.width = `${layout.termW}px`
  })
  $('readme-collapse').onclick = () => {
    layout.collapsed = true
    persistLayout()
    applyLayout()
  }
  $('readme-expand').onclick = () => {
    layout.collapsed = false
    persistLayout()
    applyLayout()
  }

  $('new-file-btn').onclick = () => {
    if (currentFile) store.stash(currentFile, editor.getValue())
    const name = store.create()
    engine.provideFile(name, '')
    currentFile = name
    editor.setValue('')
    engine.setEditorContent('')
    renderFilebar()
    updateSaveState()
    editorLayout()
  }
  $('reset-files-btn').onclick = () => {
    const before = store.list()
    store.reset(project.examples)
    resyncFiles(before)
    if (!store.list().includes(currentFile)) {
      currentFile = store.list()[0]!
      editor.setValue(store.readOpen(currentFile))
      engine.setEditorContent(store.readSaved(currentFile))
    }
    renderFilebar()
    updateSaveState()
    editorLayout()
  }

  // boot splash: the machine wakes up behind it; ENTER (or a click) enters
  $('boot').addEventListener('click', dismissBoot)
  window.addEventListener(
    'keydown',
    (e) => {
      if (e.key === 'Enter' && !$('boot').hidden) {
        e.preventDefault()
        dismissBoot()
      }
    },
    { capture: true },
  )

  term.focus()
}

main()
