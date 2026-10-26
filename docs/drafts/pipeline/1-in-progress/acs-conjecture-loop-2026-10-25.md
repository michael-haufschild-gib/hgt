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
  Status: DONE (Lean, contribution 4).
- **C5 (one test, one prime carries the whole defect of ζ).** Cases: (i) finitely many outer
  eigenvalues: C3's test with `O = outerEig`; (ii) infinitely many classes of depth `≥ δ` for some
  `δ > 0`: kill depth `≥ δ/2` except an infinite set `F` of representatives whose folded points
  converge (Bolzano–Weierstrass); inside the disc of radius `p^{−δ/2}` the active spectrum is
  `F` ∪ {limit}, countable with isolated points ⇒ C4 sees all of `F`; (iii) depths of classes → 0
  with finitely many classes per depth: every disc of radius `< 1` meets finitely many folded points,
  so C4 applies to every test; need one test with infinitely many nonzero class weights (genericity:
  Baire on an ℓ¹ family of single-class killers, or probes with nonvanishing class transforms).
  Status: DONE (Lean, contributions 5–6): the genericity tool is the probe class weight, an
  entire function positive on `Im s = δ` (`OneProbeSeesEveryOuterEigenvalue.lean`).

- **C7 (Weil's two-element windows at one prime).** The Lefschetz sequence `c_m = W(T_{p^m}g, g)`
  of one test grows exactly like `p^{wm}` (`w` = zero width); RH ⟺ `|c_m| ≤ c_0` ∀ m. Mechanism:
  `O(R^m)` moments continue the Cauchy transform to `|z| < 1/R`; a test keeping a top zero (or a
  sequence increasing to the top with convergent folded points) makes the top pole accessible.
  Status: DONE (Lean, contribution 7).

- **C8 (towers of a curve at every scale).** Curves have exponent-1 deep zeros but finitely many
  real parts: one probe sees every tower. Defect finite ⟺ `ℓ/log q ∈ ℚ`; at `a log q` it is the
  Frobenius span of the base change. Status: DONE (Lean, contribution 8).

- **C9 (one cycle for every prime).** One test reads `p^w` at every prime: attained tops via Cesàro
  growth extraction with a probe (no isolation), non-attained via a diagonal (product-space)
  subsequence and a prime-free killing test. Status: DONE (Lean, contribution 9).
- **C10 (candidate: Frobenius eigenvalues are Lefschetz ratio limits).** For each right zero `ρ`
  of ζ, the test keeping `ρ` alone among zeros of depth ≥ δ_ρ/2 has `c_{m+1}/c_m → p^{ρ−½}` at
  every prime; two primes determine `ρ` (no period over ℤ). Status: DONE (Lean, contribution 10).

- **C11 (resonant scales).** Countable for every configuration; off them one tower carries the
  Hodge defect; ζ: finitely many resonant primes; curves: arithmetic scales resonant.
  Status: DONE (Lean, contribution 11).

- **C12 (one-sided bounds at two primes).** Rotating-phase Cesàro lemma + isolating tests: width
  `≤ θ` ⟺ one-sided `O(p^{θm})`, `O(q^{θm})` for every test; RH ⟺ upper (or lower) one-sided Weil
  inequalities at two primes. Status: DONE (Lean, contribution 12).

- **C13 (one-sided bounds at one prime).** Two-term tests rotate the weight of a kept zero; real
  eigenvalues handled along even exponents. Status: DONE (Lean, contribution 13).

- **C14 (short cycles).** Dilated annihilators give killing tests of support `ε`; RH ⟺
  `Re W(g − T_{p^m} g) ≥ 0` on tests of support `≤ η`, each window Weil positive for `η ≤ 3/10`.
  Status: DONE (Lean, contribution 14).

## Avoid (other agents active 2026-10-25)
Q-II Meyer source modules; `MaximalBlindIdealOfTheMeyerSource.lean` (another agent); biarithmetic; rh-closing-producer Stepanov tracks (HTGeometry Stepanov).

## Log
- 2026-10-25 — created; C1, C2 done; C3 step (iii) done; paused on user request.
- 2026-10-25 — C3 done.
- 2026-10-26 — C4 done; C5 scoped.
- 2026-10-26 — C6 (probe tool) and C5 done.
- 2026-10-26 — C7 done.
- 2026-10-26 — C8 done.
- 2026-10-26 — C9 done.
- 2026-10-26 — C10 done.
- 2026-10-26 — C11 done.
- 2026-10-26 — C12 done.
- 2026-10-26 — C13 done.
- 2026-10-26 — C14 done.
