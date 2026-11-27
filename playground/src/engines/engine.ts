/** Line-based REPL engine.
 *
 *  `handle` is async and yields to the UI thread periodically during long
 *  searches, so Ctrl+C (see `interrupt`) can land mid-computation.
 *  A real `minilog.wasm` / `resin.wasm` build can implement this same
 *  interface later (see scripts/build-wasm.sh) without touching the UI.
 */
export interface EngineResult {
  /** Text to print (may contain newlines). */
  output: string
  /** True when the program has exited and the terminal should halt. */
  halted?: boolean
  /** True when the computation was aborted via `interrupt` (program alive). */
  interrupted?: boolean
}

export interface Engine {
  readonly id: string
  /** Banner printed once when the program (re)starts. */
  banner(): string
  /** Current prompt string (e.g. "?- " or "⊤ ⊢ "). */
  prompt(): string
  /** Handle one submitted input line. */
  handle(line: string): Promise<EngineResult>
  /** Abort the in-flight `handle` computation; program state is kept. */
  interrupt(): void
  /** Reset to a fresh program. */
  restart(): void
  /** Make editor content available as a virtual file. */
  provideFile(name: string, content: string): void
  /** Forget a virtual file (rename/delete). */
  dropFile(name: string): void
  /** Keep the editor-backed file in sync as the user types. */
  setEditorContent(content: string): void
  /** Names the engine will accept for the editor-backed file. */
  editorAliases(): string[]
}

/** Yield to the browser event loop so input (e.g. Ctrl+C) stays live. */
export const yieldToUI = (): Promise<void> => new Promise((r) => setTimeout(r, 0))
