# PNTPlus provenance

Vendored unconditional core of
<https://github.com/AlexKontorovich/PrimeNumberTheoremAnd>, Apache-2.0
(`LICENSE` here).

The integration request targeted the tree at commit
`a5040887e6bb24f7c201db8568e7755c138b3878` (2025-08-10, toolchain v4.21.0).
The source text was taken from upstream `main` at commit
`6ea1a1532f758dd27be222d3314e798cb8a0b61c` (2026-08-03), which carries the
same theorems matured onto **exactly our toolchain and mathlib pin**
(Lean `v4.32.2`, mathlib rev `v4.32.2`), eliminating an 11-release API port.
Scope is the module set that existed at the pinned commit; post-pin upstream
additions (Backlund/, IEANTN/, BorelCaratheodory, HadamardFactorization
machinery, EulerMascheroniBounds, …) are out of scope and not vendored.

## Deviations from upstream

1. Imports rewritten `PrimeNumberTheoremAnd.*` → `GaloisForLFunctions.PNTPlus.*`.
2. LeanArchitect dependency dropped: `import Architect` removed; 264
   `@[blueprint …]` attribute blocks and all `blueprint_comment` commands
   stripped; 23 LeanArchitect-only in-proof doc comments demoted to plain
   block comments (LaTeX blueprint metadata only — no proof content touched).
3. `set_option autoImplicit false` added after each file's imports (upstream
   sets this in its lakefile; ours does not).
4. `Wiener.lean`: the sorried and downstream-unused chain `prelim_decay_2`,
   `AbsolutelyContinuous`, `prelim_decay_3`, `decay_alt` was excised.  No
   vendored declaration depended on it.
5. `Tactic/AdditiveCombination.lean`: a docstring example block containing
   `axiom qc` / `axiom hqc` lines was removed (doc-comment text only, but it
   would false-positive the repo's line-based proof-debt lint).
6. Upstream modules **excluded**: `StrongPNT` (6 live sorries),
   `GeneralMeromorphic` (commented-out scaffold), `HadamardFactorization` and
   `HoffsteinLockhart` (empty stubs at the pinned commit), `Tactic/Simprocs`
   and the remaining `Tactic/*` (unused by the vendored set), and every
   `Mathlib/*` helper not in the vendored set's import closure.

The result is sorry/axiom/admit-free; `MediumPNT` and the endpoints below
audit to `[propext, Classical.choice, Quot.sound]`.

## Key endpoints

* `MediumPNT` — `ψ(x) = x + O(x·exp(-c(log x)^{1/10}))` (quantitative PNT).
* `WeakPNT`, `WeakPNT'`, `WeakPNT''` — `ψ(x) ~ x` via Wiener–Ikehara.
* `WienerIkeharaTheorem'`, `WienerIkeharaTheorem''` — the Tauberian theorem.
* `WeakPNT_AP`, `chebyshev_asymptotic_pnt` — PNT in arithmetic progressions.
* `chebyshev_asymptotic` (`θ ~ x`), `pi_asymp` (`π(x)` asymptotics),
  `mu_pnt`, `mu_pnt_alt`, `lambda_pnt` — PNT consequences.
* `BrunTitchmarsh.*` — Brun–Titchmarsh via the vendored Selberg sieve
  (`Mathlib/NumberTheory/Sieve/*`, namespaces `Sieve`/`SelbergSieve`/`Aux`).
* `Perron.*`, `MellinCalculus`, `ResidueCalcOnRectangles`, `Rectangle` —
  contour/Mellin machinery; `ZetaBounds` — explicit zero-free region;
  `ZetaConj` — `ζ(s̄) = conj (ζ s)`; `EulerMaclaurin` — 1st-order formula.

## Intentional overlaps (same fact, independent proofs)

Kept because each side is load-bearing inside its own dependency cone; names
never collide (corpus copies live under `RHTower.*` namespaces, PNTPlus root
declarations match upstream).  Corpus versions stay authoritative for corpus
research; cite PNTPlus versions for PNT+-derived work.

| PNTPlus (root namespace) | Existing counterpart |
|---|---|
| `WeakPNT`, `WeakPNT''` | `RHTower` `tendsto_sum_vonMangoldt_div` (`RHTower/Sieve/ChebyshevPNT.lean`) |
| `mu_pnt` | `RHTower` `tendsto_norm_sum_moebius_div` (`RHTower/Sieve/MoebiusSharpLittleO.lean`) |
| `norm_zeta_product_ge_one`, zero-free region in `ZetaBounds` | `RHTower.norm_zeta_product_ge_one` (`RHTower/ZetaThreeFourOne.lean`) and the `zetaLowerA/log⁹T` box |
| `Sieve`/`SelbergSieve` namespaces | mathlib `Mathlib.NumberTheory.SelbergSieve` (they coexist upstream against the same mathlib rev) |
| `BrunTitchmarsh.*` | `RHTower.Sieve.card_coprime_Ioc_le_log` (weaker Brun-shape bound) |

Strictly new to the tree: the quantitative error term of `MediumPNT`,
`pi_asymp`, `chebyshev_asymptotic`, `lambda_pnt`, `mu_pnt_alt`, the
Wiener–Ikehara theorem, PNT in APs, the Selberg sieve with bounds, and
Brun–Titchmarsh proper.
