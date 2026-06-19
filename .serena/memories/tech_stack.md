# Tech Stack

- Primary formal language: Lean 4 via Lake.
- Toolchain pin: `formal/lean-toolchain` = `leanprover/lean4:v4.30.0`.
- Lake package: `formal/lakefile.toml`; package/lib name `GaloisForLFunctions`; default target `GaloisForLFunctions`.
- Mathlib dependency: `mathlib` from `leanprover-community/mathlib4.git`, rev `v4.30.0`.
- Verified local tools on 2026-06-19: Lean `4.30.0` arm64 Darwin; Lake `5.0.0-src+d024af0`.
- Main non-formal artifacts: Markdown research drafts/cards under `docs/drafts/`.
- Scripts: `scripts/check_axioms.sh` is the authoritative Lean audit; `scripts/numerics/` holds numerical helpers.
- Git ignore notable paths: `/formal/.lake`, `logs/`, `agentchattr/`, TeX build products, `.DS_Store`.