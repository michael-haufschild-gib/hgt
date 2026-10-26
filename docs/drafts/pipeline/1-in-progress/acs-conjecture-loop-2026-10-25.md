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
  scales over `ℤ`. Status: DONE (Lean, contribution 2).
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
  annihilation defeats it. Status: step (iii) formalized
  (`AnnihilatingTestsForSparseSpectra.exists_annihilating_test`); steps (ii) zero-density
  summability and (iv) restricted configuration + tower law remain. Note: `upperLevels Z ρ` is
  defined from all right zeros of `Z`, so the killed zeros must be removed from the
  configuration (`Z'`, with `W_Z = W_{Z'}` on tests vanishing there) before applying
  `mem_wfVisibleSet_of_finite_above`.
  Status: DONE (Lean, contribution 3, `OnePrimeSeesTheWholeDefectOfZeta.lean`). No restricted
  configuration was needed: the extraction was generalised to levels where the test is nonzero.

- **C4 (fixed-seed towers: Wolff blindness is separation).** Replace the top-down Cesàro
  extraction (needs no increasing real parts above the level) by complex analysis: the discrete
  Cauchy transform `Σ q_τ/(1 − c_τ z)` of a vector orthogonal to the tower vanishes near 0 (moments),
  hence on the component of the complement of its closed poles containing 0; at an accessible
  isolated pole its residue (the class sum) vanishes. Tower law: every visible `b` with `b⁻¹`
  accessible from 0 off the closed active folded spectrum `{β_τ⁻¹}` is seen; blindness forces
  separation; countable folded spectra in the unit disc do not blind a fixed test.
  Status: Lean written (`WolffBlindnessRequiresSeparation.lean`), compiling.
- **C5 (one test, one prime carries the whole defect of ζ).** Cases: (i) finitely many outer
  eigenvalues: C3's test with `O = outerEig`; (ii) infinitely many classes of depth `≥ δ` for some
  `δ > 0`: kill depth `≥ δ/2` except an infinite set `F` of representatives whose folded points
  converge (Bolzano–Weierstrass); inside the disc of radius `p^{−δ/2}` the active spectrum is
  `F` ∪ {limit}, countable with isolated points ⇒ C4 sees all of `F`; (iii) depths of classes → 0
  with finitely many classes per depth: every disc of radius `< 1` meets finitely many folded points,
  so C4 applies to every test; need one test with infinitely many nonzero class weights (genericity:
  Baire on an ℓ¹ family of single-class killers, or probes with nonvanishing class transforms).
  Status: open; (iii) needs a genericity tool.

## Avoid (other agents active 2026-10-25)
Q-II Meyer source modules; `MaximalBlindIdealOfTheMeyerSource.lean` (another agent); biarithmetic; rh-closing-producer Stepanov tracks (HTGeometry Stepanov).

## Log
- 2026-10-25 — created; C1, C2 done; C3 step (iii) done; paused on user request.
- 2026-10-25 — C3 done.
