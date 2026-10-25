# ACS conjecture loop (2026-10-25)

- **ID:** acs-conjecture-loop-2026-10-25
- **Stage:** 1-in-progress
- **Type:** CONJECTURE (loop card; each item becomes a THEOREM (Lean) or a recorded failure)
- **Source:** `formal/GaloisForLFunctions/ArithmeticCastelnuovoSeveri/README.md` §§6–8; review-2410 Mechanism C
- **Statement:** Conjecture loop for significant contributions to ACS open questions; log in
  `logs/acs-250-2026-10-25.md`.

## Goal
Each item: an unconditional Lean theorem in ACS that answers an open question, builds a missing
tool, or exposes a mechanism, calibrated over `𝔽_q`.

## Gates
- [x] 0 → 1 in-progress: loop opened, README and frontier map read.

## Items
- **C1 (one-sided Lefschetz bounds).** Lower point-count bounds force unitarity; upper bounds
  force it except when a top outer eigenvalue is a positive real (a real zero). Golden datum =
  real-zero fake satisfying every upper bound. Lag tests: difference tests see every impurity,
  sum tests are blind exactly to real outer eigenvalues. Status: DONE (Lean, contribution 1).
- **C2 (genus one: defect of a graph = 2·degree).** Window `{Δ, Γ_F}`: isotropic graph classes
  of `m − nF` with `x·V = 1` have defect `2 deg(m − nF)`; Hasse ⟺ integer degree positivity;
  golden `deg(2 − F) = −1`; theorem of the square in genus one vs. numerical freedom of Hecke
  scales over `ℤ`. Status: Lean in progress.
- **C3 (README Open 5: one prime suffices for ζ).** Conjecture: for every prime `p`,
  `sup_g` (p-tower defect of `g`) = #{distinct outer p-eigenvalues of right zeros of ζ}.
  Paper proof plan: (i) choose finitely many classes `b_1..b_n`, one zero `τ_j` each, depth
  `δ₀ = min_j (Re τ_j − ½)`; (ii) `A` = right zeros of depth ≥ δ₀ other than the `τ_j`;
  zero density (`exists_zetaZeroDensity_powerSaving`) gives `Σ_{a∈A} |a|^{-s} < ∞` for some
  `s < 1`; (iii) annihilating test: Ingham bump `φ` (infinite convolution of `1_{[−ε_n,ε_n]}`,
  `ε_n = n^{-1/α}`, `s < α < 1`) has `|φ̂(z)| ≤ C e^{−c|Re z|^α}` in the strip; `P = Π_{a∈A}(1 − z/a)`
  has `|P(x)| ≤ e^{C|x|^s}`; `g = lim_N Π_{k≤N}(1 + iD/a_k) φ` is `C²`, supported in `supp φ`,
  with `ĝ = P φ̂` vanishing on `A` and not at `τ_j, τ̄_j`; (iv) above level `δ₀` only the `τ_j` are
  visible, so `visibleFrobSet_above_subset_wfVisibleSet_of_finite` gives tower defect ≥ n.
  Mechanism: Wolff blindness needs dense deep zeros; zero-density sparseness plus Paley–Wiener
  annihilation defeats it. Status: paper plan; Lean infrastructure (Ingham bump, annihilator)
  not in corpus.

## Avoid (other agents active 2026-10-25)
Q-II Meyer source modules; biarithmetic; rh-closing-producer Stepanov tracks (HTGeometry Stepanov).

## Log
- 2026-10-25 — created.
