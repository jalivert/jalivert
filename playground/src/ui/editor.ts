import * as monaco from 'monaco-editor/esm/vs/editor/editor.api'
import 'monaco-editor/min/vs/editor/editor.main.css'
import editorWorker from 'monaco-editor/esm/vs/editor/editor.worker?worker'

(self as unknown as { MonacoEnvironment: unknown }).MonacoEnvironment = { getWorker: () => new editorWorker() }

let registered = false

function registerLanguages(): void {
  if (registered) return
  registered = true

  monaco.languages.register({ id: 'minilog' })
  monaco.languages.setMonarchTokensProvider('minilog', {
    tokenizer: {
      root: [
        [/%.*$/, 'comment'],
        [/:-/, 'keyword'],
        [/[a-z]+/, 'type'],
        [/[A-Z]+/, 'variable'],
        [/[(),.=]/, 'delimiter'],
        [/\d+/, 'number'],
      ],
    },
  } as never)

  monaco.languages.register({ id: 'plover' })
  monaco.languages.setMonarchTokensProvider('plover', {
    tokenizer: {
      root: [
        [/%.*$/, 'comment'],
        [/:-/, 'keyword'],
        [/-{2,}/, 'keyword'],
        [/[a-z][a-z \-]*/, 'type'],
        [/[A-Z][A-Z \-]*/, 'variable'],
        [/[(),.=]/, 'delimiter'],
        [/\d+/, 'number'],
      ],
    },
  } as never)

  monaco.languages.register({ id: 'frea' })
  monaco.languages.setMonarchTokensProvider('frea', {
    tokenizer: {
      root: [
        [/--.*$/, 'comment'],
        [/\b(module|where|data|type|let|in|if|then|else|lambda|assume|rec|match|with|the|claim|define|fix)\b/, 'keyword'],
        [/[A-Z][A-Za-z0-9_'\-!#$%&*+./<=>?@\\^|~:]*/, 'type'],
        [/[a-z][a-zA-Z0-9_'\-!#$%&*+./<=>?@\\^|~:]*/, 'variable'],
        [/"([^"\\]|\\.)*"/, 'string'],
        [/'([^'\\]|\\.)*'/, 'string'],
        [/\d+\.\d+(?:[eE][+-]?\d+)?|\d+[eE][+-]?\d+/, 'number'],
        [/0[xX][0-9a-fA-F]+|0[oO][0-7]+|-?\d+/, 'number'],
        [/[(),.;=\[\]{}]/, 'delimiter'],
        [/[-+*/<>=!|&]+/, 'operator'],
      ],
    },
  } as never)
  monaco.languages.register({ id: 'lambdapie' })
  monaco.languages.setMonarchTokensProvider('lambdapie', {
    tokenizer: {
      root: [
        [/\b(assume|lambda|forall)\b/, 'keyword'],
        [/[∀Πλ]/, 'keyword'],
        [/\/\\/, 'keyword'],
        [/[A-Z][A-Za-z0-9_'\-]*/, 'type'],
        [/[a-z][A-Za-z0-9_'\-]*/, 'variable'],
        [/[0-9]+/, 'number'],
        [/::|->|\.|[(),\[\]*]/, 'operator'],
      ],
    },
  } as never)
  monaco.languages.register({ id: 'resin' })
  monaco.languages.setMonarchTokensProvider('resin', {
    tokenizer: {
      root: [
        [/%.*$/, 'comment'],
        [/\b(constants|aliases|axioms|theorem|lemma|proof|using|forall|exists|True|Tautology|False|Contradiction|AND|OR|NOT)\b/, 'keyword'],
        [/[∀∃⊤⊥∧∨¬⟹⟺⊢ᶜ]/, 'keyword'],
        [/[A-Z][A-Za-z0-9_'\-]*/, 'type'],
        [/[a-z][A-Za-z0-9_'\-]*/, 'variable'],
        [/[0-9]+/, 'number'],
        [/==>|=>|<==>|<=>/, 'operator'],
        [/[:,.=()[\]{}]/, 'delimiter'],
      ],
    },
  } as never)

  monaco.languages.register({ id: 'detour' })
  monaco.languages.setMonarchTokensProvider('detour', {
    tokenizer: {
      root: [
        [/--.*$/, 'comment'],
        [/\b(module|constants|aliases|axiom|syntax|judgment|schema|theorem|rule|for|all|any|some|object|objects|proposition|propositions|by|induction|unproved|case|analysis|on|prove|use)\b/, 'keyword'],
        [/\b(forall|exists|TRUE|True|Tautology|TAUTOLOGY|FALSE|CONTRADICTION|Contradiction|NOT|AND|OR)\b/, 'keyword'],
        [/[∀∃⊤⊥¬∧∨⟹⟺⊢]/, 'keyword'],
        [/[A-Z][A-Za-z0-9_'\-!#$%&*+./<=>?@\\^|~:]*/, 'type'],
        [/[a-z0-9_][a-zA-Z0-9_'\-!#$%&*+./<=>?@\\^|~:]*/, 'variable'],
        [/\|[-]+/, 'keyword'],
        [/[(),.;=\[\]{}]/, 'delimiter'],
        [/==>|=>|<==>|<=>|->|:=/, 'operator'],
      ],
    },
  } as never)

  monaco.languages.register({ id: 'glask' })
  monaco.languages.setMonarchTokensProvider('glask', {
    tokenizer: {
      root: [
        [/--.*$/, 'comment'],
        [/\b(module|where|data|type|class|instance|fixity|infix|infixl|infixr|prefix|prefixr|postfix|let|in|if|then|else|case|of|forall)\b/, 'keyword'],
        [/\\/, 'keyword'],
        [/[A-Z][A-Za-z0-9_']*/, 'type'],
        [/[a-z_][a-zA-Z0-9_']*/, 'variable'],
        [/_[a-zA-Z0-9_']+/, 'variable'],
        [/"([^"\\]|\\.)*"/, 'string'],
        [/'([^'\\]|\\.)*'/, 'string'],
        [/\d+\.\d+(?:[eE][+-]?\d+)?|\d+[eE][+-]?\d+/, 'number'],
        [/0[xX][0-9a-fA-F]+|0[oO][0-7]+|-?\d+/, 'number'],
        [/::|=>|->|\.\.|[(),.;=\[\]{}]/, 'delimiter'],
        [/[-+*/<>=!|&$:.]+/, 'operator'],
        [/`[a-zA-Z_][a-zA-Z0-9_']*`/, 'operator'],
      ],
    },
  } as never)

  monaco.editor.defineTheme('pltt-dark', {
    base: 'vs-dark',
    inherit: true,
    rules: [
      { token: '', foreground: 'e09c1f' },
      { token: 'comment', foreground: '8a6a24', fontStyle: 'italic' },
      { token: 'keyword', foreground: 'ffb000', fontStyle: 'bold' },
      { token: 'type', foreground: 'ffd257' },
      { token: 'variable', foreground: 'e09c1f' },
      { token: 'number', foreground: 'ff7b00' },
      { token: 'operator', foreground: 'ffb000' },
      { token: 'delimiter', foreground: '8a6a24' },
    ],
    colors: {
      'editor.background': '#060402',
      'editor.foreground': '#e09c1f',
      'editor.lineHighlightBackground': '#171006',
      'editorLineNumber.foreground': '#6e4c08',
      'editorLineNumber.activeForeground': '#ffb000',
      'editorCursor.foreground': '#ffb000',
      'editor.selectionBackground': '#4a3508',
      'editor.inactiveSelectionBackground': '#2b2005',
      'editorWidget.background': '#0b0803',
      'editorWidget.border': '#4a3508',
    },
  })
}

export interface CodeEditor {
  setLanguage(lang: string): void
  setValue(v: string): void
  getValue(): string
  insert(text: string): void
  onChange(fn: () => void): void
  onSave(fn: () => void): void
  layout(): void
}

export function createEditor(el: HTMLElement, lang: string, value: string): CodeEditor {
  registerLanguages()
  const ed = monaco.editor.create(el, {
    value,
    language: lang,
    theme: 'pltt-dark',
    minimap: { enabled: false },
    fontSize: 13.5,
    lineHeight: 1.5,
    scrollBeyondLastLine: false,
    automaticLayout: true,
    padding: { top: 10 },
    renderLineHighlight: 'all',
  })
  return {
    setLanguage(l: string) {
      const m = ed.getModel()
      if (m) monaco.editor.setModelLanguage(m, l)
    },
    setValue(v: string) {
      ed.setValue(v)
    },
    getValue() {
      return ed.getValue()
    },
    insert(text: string) {
      const sel = ed.getSelection()
      if (!sel) return
      ed.executeEdits('symbol-bar', [{ range: sel, text, forceMoveMarkers: true }])
      ed.focus()
    },
    onChange(fn: () => void) {
      ed.onDidChangeModelContent(() => fn())
    },
    onSave(fn: () => void) {
      ed.addCommand(monaco.KeyMod.CtrlCmd | monaco.KeyCode.KeyS, () => fn())
    },
    layout() {
      ed.layout()
    },
  }
}
