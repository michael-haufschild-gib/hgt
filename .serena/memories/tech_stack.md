# Tech Stack

- Lean 4 project under `formal/`, toolchain `leanprover/lean4:v4.32.2`.
- Lake package name: `GaloisForLFunctions`; default target `GaloisForLFunctions`.
- Dependencies pinned in `formal/lakefile.toml`: `mathlib` rev `v4.32.2`, `aesop` rev `v4.32.0` (the compatible release selected for this toolchain).
- Shell environment is Darwin/zsh; run Lean commands from `formal/` unless using absolute paths.