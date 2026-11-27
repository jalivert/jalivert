import { Terminal } from '@xterm/xterm'
import { FitAddon } from '@xterm/addon-fit'
import '@xterm/xterm/css/xterm.css'

export interface LineHandler {
  (line: string): void
}

/** Orange-phosphor CRT terminal with simple line editing. */
export class CrtTerminal {
  readonly term: Terminal
  private fitAddon = new FitAddon()
  private buf = ''
  private cursor = 0
  private onLine: LineHandler = () => {}
  private promptText = ''
  private halted = false
  private haltMessage = '-- PROGRAM TERMINATED -- Type `start` to start it again.'

  constructor(private el: HTMLElement) {
    this.term = new Terminal({
      cursorBlink: true,
      cursorStyle: 'block',
      fontFamily: '"JetBrains Mono", ui-monospace, SFMono-Regular, Menlo, Consolas, monospace',
      fontSize: 14,
      lineHeight: 1.25,
      theme: {
        background: '#050302',
        foreground: '#ffa21f',
        cursor: '#ffb03a',
        cursorAccent: '#050302',
        selectionBackground: 'rgba(255,162,31,0.28)',
        black: '#050302',
        brightYellow: '#ffc25e',
      },
      allowProposedApi: true,
    })
    this.term.loadAddon(this.fitAddon)
    this.term.open(el)
    this.fit()
    this.term.onData((d) => this.handleData(d))
    new ResizeObserver(() => this.fit()).observe(el)
    window.addEventListener('resize', () => this.fit())
  }

  onSubmit(fn: LineHandler): void {
    this.onLine = fn
  }

  fit(): void {
    try {
      this.fitAddon.fit()
    } catch {
      /* not laid out yet */
    }
  }

  clear(): void {
    this.term.clear()
    this.buf = ''
    this.cursor = 0
  }

  /** Print raw text (\\n are converted). */
  print(text: string): void {
    this.term.write(text.replace(/\r?\n/g, '\r\n'))
  }

  println(text = ''): void {
    this.print(text + '\n')
  }

  showPrompt(prompt: string): void {
    this.promptText = prompt
    this.buf = ''
    this.cursor = 0
    this.print(prompt)
  }

  focus(): void {
    this.term.focus()
  }

  setHalted(halted: boolean): void {
    this.halted = halted
  }

  private handleData(d: string): void {
    if (d === '\x0c') {
      // Ctrl+L: clear screen, reprint prompt (or halt notice)
      this.clear()
      this.print(this.halted ? this.haltMessage + '\n' : this.promptText)
      return
    }
    if (d === '\r') {
      // submit
      this.print('\r\n')
      const line = this.buf
      this.buf = ''
      this.cursor = 0
      this.onLine(line)
      return
    }
    if (d === '\x7f') {
      // backspace
      if (this.cursor > 0) {
        this.buf = this.buf.slice(0, this.cursor - 1) + this.buf.slice(this.cursor)
        this.cursor--
        this.term.write('\b')
        const rest = this.buf.slice(this.cursor)
        this.term.write(rest + ' ')
        this.term.write(`\x1b[${rest.length + 1}D`)
      }
      return
    }
    if (d === '\x03') {
      // Ctrl+C: drop current line, reprint prompt
      this.print('^C\r\n')
      const line = ''
      this.buf = ''
      this.cursor = 0
      this.onLine(line + '\x03')
      return
    }
    // ignore escape sequences & control chars; echo printable runs
    if (d.startsWith('\x1b') || (d.length === 1 && d < ' ')) return
    this.buf = this.buf.slice(0, this.cursor) + d + this.buf.slice(this.cursor)
    this.cursor += d.length
    const rest = this.buf.slice(this.cursor - d.length)
    this.term.write(rest)
    if (rest.length > d.length) this.term.write(`\x1b[${rest.length - d.length}D`)
  }
}
