# Core

- Repo root is a research/formalization workspace for hypertranscendental functions. Main Lean tree is `formal/`.
- Formal-local agent entrypoints are `formal/CLAUDE.md`, `formal/AGENTS.md`, `formal/README.md`, and generated `formal/LEAN_OVERVIEW.md`.
- `formal/GaloisForLFunctions.lean` is the Lean library entrypoint; `formal/GaloisForLFunctions/MainTheorems.lean` imports Hurwitz, U0, and Böttcher.
- Project conduct and append/edit constraints are in `AGENTS.md` / `CLAUDE.md`; read them before research/formalization work.
- Use `scripts/formal_tools.py research "<query>"` before proving reusable formal infrastructure.
- For Böttcher-specific state, read `mem:formal/bottcher` before changing `formal/GaloisForLFunctions/Bottcher/**`.
- Tech/build details: `mem:tech_stack`; completion checks: `mem:task_completion`; local conventions: `mem:conventions`.
