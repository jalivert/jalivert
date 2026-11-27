import { parseGlaskModule } from '../src/engines/glask'
import * as fs from 'fs'
import * as path from 'path'

const VENDOR = '/Users/liam/Projects/PL&TT/web-demo/vendor/glask/examples/positive'

function tagOf(d: { k: string }): string {
  switch (d.k) {
    case 'binding': return 'Binding'
    case 'sig': return 'Signature'
    case 'data': return 'Data\'Decl'
    case 'alias': return 'Type\'Alias'
    case 'fixity': return 'Fixity'
    case 'class': return 'Class\'Decl'
    case 'instance': return 'Instance'
    default: return '?'
  }
}

function walk(dir: string, out: string[]): void {
  for (const f of fs.readdirSync(dir).sort()) {
    const p = path.join(dir, f)
    if (fs.statSync(p).isDirectory()) walk(p, out)
    else if (f.endsWith('.glask')) out.push(p)
  }
}

async function main(): Promise<void> {
  const files: string[] = []
  walk(VENDOR, files)
  let ok = 0
  let fail = 0
  for (const f of files) {
    const rel = path.relative('/Users/liam/Projects/PL&TT/web-demo/vendor/glask/examples/positive', f)
    const parts = rel.split('/')
    const dir = parts.slice(0, -1).join('').replace(/-/g, '')
    const file = parts[parts.length - 1]!.replace(/\.layout\.glask$/, '-layout').replace(/\.glask$/, '')
    const golden = `/Users/liam/Projects/PL&TT/glask/test/golden/parse/${dir ? dir + '-' : ''}${file}.golden`
    let goldenHeader = ''
    try {
      const g = fs.readFileSync(golden, 'utf8').split('\n')
      goldenHeader = g[1] ?? ''
    } catch {
      console.log(`NOGOLDEN ${rel}`)
      continue
    }
    const m = /-- decls: (\d+) (\[.*\])/.exec(goldenHeader)
    if (!m) {
      console.log(`BADGOLDEN ${rel}: ${goldenHeader.slice(0, 80)}`)
      continue
    }
    const src = fs.readFileSync(f, 'utf8')
    try {
      const decls = parseGlaskModule(src)
      const mine = `-- decls: ${decls.length} [${decls.map((d) => `"${tagOf(d)}"`).join(',')}]`
      if (mine === m[0].replace(/, /g, ',')) {
        ok++
      } else {
        fail++
        console.log(`DIFF ${rel}\n  golden: ${m[0].slice(0, 200)}\n  mine:   ${mine.slice(0, 200)}`)
      }
    } catch (e) {
      fail++
      console.log(`PARSE-ERROR ${rel}: ${(e as Error).message.slice(0, 120)}`)
    }
  }
  console.log(`\nmatch=${ok} diff=${fail}`)
}

void main()
