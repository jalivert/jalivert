import type { ExampleFile } from '../projects'

/** In-memory file store with saved-vs-buffer (dirty) semantics.
 *
 *  The engine only ever sees *saved* content (`:load`/`:check` read the
 *  saved version, like a real file on disk). Unsaved buffers live for the
 *  session; saved content persists in localStorage.
 *
 *  Storage is versioned (`STORE_VERSION`): when the bundled examples change,
 *  old saved copies are migrated forward once instead of shadowing the new
 *  vendor content forever.
 */
const STORE_VERSION = 'v2'
const keyFor = (projectId: string): string => `pltt.${STORE_VERSION}.files.${projectId}`
const legacyKeyFor = (projectId: string): string => `pltt.files.${projectId}`

export class FileStore {
  private saved = new Map<string, string>()
  private buffers = new Map<string, string>()
  private order: string[] = []

  constructor(
    private projectId: string,
    private ext: string,
    defaults: ExampleFile[],
  ) {
    const versioned = localStorage.getItem(keyFor(projectId))
    const raw = versioned ?? localStorage.getItem(legacyKeyFor(projectId))
    if (raw) {
      try {
        const obj = JSON.parse(raw) as Record<string, string>
        const bundled = new Set(defaults.map((d) => d.file))
        for (const [name, content] of Object.entries(obj)) {
          if (typeof content !== 'string') continue
          // On a version bump, bundled examples refresh from the new vendor
          // content; only the user's own files (and their current-version
          // saves, including edits to bundled files) carry over.
          if (versioned === null && bundled.has(name)) continue
          this.saved.set(name, content)
          this.order.push(name)
        }
        for (const ex of defaults) {
          if (!this.saved.has(ex.file)) {
            this.saved.set(ex.file, ex.content)
            this.order.push(ex.file)
          }
        }
        // migrated (or just loaded): persist under the versioned key and drop the legacy one
        this.persist()
        try {
          localStorage.removeItem(legacyKeyFor(projectId))
        } catch {
          /* ignore */
        }
      } catch {
        /* corrupted storage: fall through to defaults */
      }
    }
    if (this.order.length === 0) {
      for (const ex of defaults) {
        this.saved.set(ex.file, ex.content)
        this.order.push(ex.file)
      }
      this.persist()
    }
  }

  list(): string[] {
    return [...this.order]
  }

  readSaved(name: string): string {
    return this.saved.get(name) ?? ''
  }

  /** Current buffer if the file has unsaved edits, else saved content. */
  readOpen(name: string): string {
    return this.buffers.get(name) ?? this.readSaved(name)
  }

  isDirty(name: string, currentValue?: string): boolean {
    const buf = currentValue !== undefined ? currentValue : this.buffers.get(name)
    if (buf === undefined) return false
    return buf !== this.readSaved(name)
  }

  /** Cache the live editor buffer (called on every keystroke, not a save). */
  stash(name: string, value: string): void {
    this.buffers.set(name, value)
  }

  save(name: string, value: string): void {
    this.saved.set(name, value)
    this.buffers.set(name, value)
    this.persist()
  }

  create(): string {
    let i = 1
    let name = `untitled-${i}.${this.ext}`
    while (this.saved.has(name)) {
      i++
      name = `untitled-${i}.${this.ext}`
    }
    this.saved.set(name, '')
    this.order.push(name)
    this.persist()
    return name
  }

  rename(oldName: string, newName: string): string {
    let name = newName.trim()
    if (!name) return oldName
    if (!name.endsWith(`.${this.ext}`)) name = `${name}.${this.ext}`
    if (name === oldName) return oldName
    if (this.saved.has(name)) return oldName // no clobbering
    const idx = this.order.indexOf(oldName)
    if (idx === -1) return oldName
    this.order[idx] = name
    this.saved.set(name, this.saved.get(oldName) ?? '')
    this.saved.delete(oldName)
    if (this.buffers.has(oldName)) {
      this.buffers.set(name, this.buffers.get(oldName)!)
      this.buffers.delete(oldName)
    }
    this.persist()
    return name
  }

  remove(name: string): void {
    if (this.order.length <= 1) return // always keep at least one file
    this.order = this.order.filter((n) => n !== name)
    this.saved.delete(name)
    this.buffers.delete(name)
    this.persist()
  }

  reset(defaults: ExampleFile[]): void {
    this.saved.clear()
    this.buffers.clear()
    this.order = []
    for (const ex of defaults) {
      this.saved.set(ex.file, ex.content)
      this.order.push(ex.file)
    }
    this.persist()
  }

  /** Push every saved file into the engine's virtual FS. */
  syncEngine(provide: (name: string, content: string) => void): void {
    for (const name of this.order) provide(name, this.saved.get(name) ?? '')
  }

  private persist(): void {
    const obj: Record<string, string> = {}
    for (const name of this.order) obj[name] = this.saved.get(name) ?? ''
    try {
      localStorage.setItem(keyFor(this.projectId), JSON.stringify(obj))
    } catch {
      /* storage full/blocked: session-only mode */
    }
  }
}
