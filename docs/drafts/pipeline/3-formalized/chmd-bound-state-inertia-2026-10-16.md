# CHMD: bound-state inertia of the arithmetic resolvent (lower Birman–Schwinger bound)

- **ID:** chmd-bound-state-inertia-2026-10-16
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean), unconditional
- **Source:** CHMD route; continuation of chmd-even-sector-point-spectrum-2026-10-16 and chmd-birman-schwinger-bound; corpus inputs: `zeta_weil_inertia_law` / `weilNegIndex` (ZetaWeilFiniteLevelInertia), `paperFT_ofRealFun_I_div_two`, `integral_mul_exp_half_eq_cosh_add_sinh`, `zeta_W_eq_weilFullFunctional`, `re_weilFullFunctional_split` (MUST-1556)
- **Statement:** (1) `P := closure span{w : Rw = μw, μ > ½}` is closed, `R`-invariant, `R ≤ ½` on `Pᗮ`, `1 ∈ P`, and `RH ⟺ P = ℝ·1`. (2) `E(p) < 0 ⟹ ⟪R Sp, Sp⟫ > ½‖Sp‖² ⟹ Sp ∉ Pᗮ`. (3) For real `C²_c` `g` with `ĝ(i/2) = ĝ(−i/2) = 0`: `E(lift(g/K)) = Re W(g,g)` (polar terms = cosh/sinh moments = 0). (4) For a complex subspace `V` of polar-constrained `C²_c` tests with `Re W` negative definite: `dim_ℂ V ≤ dim_ℝ P` (and the cardinal version without finiteness). (5) `weilNegIndex ζ a ε ≤ dim P` for all `a`, `ε ≥ 0`; under the hypotheses of the corpus inertia law, every visible separated set `T` of deep off-line zeros satisfies `|T| ≤ dim P + 2`.
- **Status:** STATUS MUST-1557. One leaf (`CHMDBoundStateInertia`; 37 declarations), axioms propext/Classical.choice/Quot.sound; plain `lake env lean` audit clean; `lake build --old` green; wired; global lint passed; index refreshed.

## Gates
- [x] 0 → 1  in-progress
- [x] 1 → 2  fully-proven (paper proof below = the Lean development)
- [x] 2 → 3  formalized: `half_bound_on_orthogonal_boundStateSpace`, `riemannHypothesis_iff_boundStateSpace_eq_span_oneL`, `sourceEnergy_phiDoobInv_eq_re_W`, `finrank_le_finrank_boundStateSpace_of_negative_subspace`, `weilNegIndex_le_finrank_boundStateSpace`, `card_le_finrank_boundStateSpace_add_two`
- [ ] 3 → 4  publication-ready

## Obstacle addressed
The frontier recorded the Birman–Schwinger bound (MUST-1553) as "an upper index bound, not … an
orbit bijection, or exclusion of bound states", and the spectral criterion (MUST-1552) as "not an
orbit-by-orbit correspondence with nonreal Xi zeros". The missing half was the lower bound:
nothing forced bound states from zeros. The obstacle was that negativity of the Weil form does not
give negativity of the Doob energy (the sinh polar term has the wrong sign), and the corpus
negative index is built from complex, non-even tests. Two structural facts remove it: on the
polar-constrained hyperplane (both Fourier samples at `±i/2` vanish, exactly the class used by the
corpus negative index) both polar terms vanish identically, so Weil form = Doob energy; and a
complex negative-definite subspace doubles into a real subspace of `P × P` whose kernel would carry
a test with `Re W(Re f) + Re W(Im f) ≥ 0`. The count `2·dim_ℂ V ≤ 2·dim P` needs no inertia
theorem. The bound states of `R` above the essential threshold are now squeezed between the
finite-level negative index of the Weil form (hence visible separated deep zeros, by the corpus
inertia law) and twice the number of off-line zeros.

## Paper proof
*Bound-state space.* `P` is a topological closure, hence closed. Generators are mapped by `R` to
multiples of themselves, so the span is `R`-invariant, and `R` is continuous, so the closure is.
`Pᗮ` is closed and `R`-invariant (`R` symmetric); an eigenvector in `Pᗮ` above `½` lies in
`P ∩ Pᗮ = 0`, so the invariant-subspace dictionary gives `R ≤ ½` on `Pᗮ`. Under RH every
eigenvector above `½` is a multiple of `1` (MUST-1556), so `P ⊆ ℝ·1`, and `1 ∈ P`; conversely
`P = ℝ·1` leaves no primitive bound state.

*Energy versus numerical range.* `⟪R w, w⟫ ≤ ½‖w‖²` for all multiples of `w = Sp` gives
`E(p) ≥ 0` (MUST-1555 dictionary on `ℝ·w`); contrapositive: `E(p) < 0 ⟹ ⟪R Sp, Sp⟫ > ½‖Sp‖²`.

*Polar-constrained tests.* `⟪Sp, tanh⟫ = ∫ v·tanh(x/2) dμ = ∫ K v sinh(x/2) = phiDoobSinhMass v`
since `μ = K cosh(x/2) dx`; with `v = g/K`: cosh and sinh moments of `g`. The two Fourier samples
are `∫ g e^{∓x/2} = C(g) ∓ S(g)`, so both vanish iff `C(g) = S(g) = 0`, and then
`weilForm(p) = E(p)`, while `weilForm(p) = Re W(g,g)` by polar transfer.

*Complex tests.* At `z = ±i/2` the character `e^{izu}` is real, so the transform of `Re f`
(`Im f`) is the real (imaginary) part of the transform; polar constraints pass to `Re f`, `Im f`.
`Re W(f,f) = Re W(Re f) + Re W(Im f)` (MUST-1556 split through `weilFullFunctional`).

*Dimension count.* Let `Ψ : V → P × P`, `f ↦ (π S lift(Re f/K), π S lift(Im f/K))`, `ℝ`-linear
(sources of lifts are additive and homogeneous a.e.). If `dim P < dim_ℂ V` then
`dim_ℝ(P × P) = 2 dim P < 2 dim_ℂ V = dim_ℝ V`, so `Ψ` has a nonzero kernel element `f`: both
sources lie in `Pᗮ`, so both Doob energies are `≥ 0`, so `Re W(f,f) ≥ 0`, contradicting negative
definiteness. The cardinal version adds the trivial infinite-dimensional case.

*Corollaries.* Every member `n` of the set defining `weilNegIndex ζ a ε` (ε ≥ 0) satisfies
`n ≤ dim P` (`tsupport ⊆ [−a,a]` gives compact support; `Re W < −ε∫|f|² ≤ 0`), so `sSup ≤ dim P`.
The corpus inertia law gives `|T| ≤ weilNegIndex + 2` for visible separated deep zero sets.

## Lean module (namespace `RHTower.CHMDPolar`)
`RHTower/CHMDBoundStateInertia.lean` — `boundStateSpace`, `isClosed_boundStateSpace`,
`mem_boundStateSpace_of_eigen`, `oneL_mem_boundStateSpace`, `resolventInvariant_boundStateSpace`,
`resolventInvariant_orthogonal`, `half_bound_on_orthogonal_boundStateSpace`,
`riemannHypothesis_iff_boundStateSpace_eq_span_oneL`, `sourceEnergy_nonneg_of_inner_resolvent_le`,
`half_lt_inner_resolvent_of_energy_neg`, `fst_notMem_orthogonal_of_energy_neg`, `inner_compactLift_tanhL`,
`weilForm_compactLift_eq_sourceEnergy_of_polar`, `coshHalfMoment_eq_zero_and_sinhHalfMoment_eq_zero`,
`sourceEnergy_phiDoobInv_eq_re_W`, `rePart`, `imPart`, `contDiff_rePart/imPart`,
`hasCompactSupport_rePart/imPart`, `paperFT_rePart_imPart_of_exp_real`, `exp_I_mul_I_div_two`,
`exp_I_mul_neg_I_div_two`, `paperFT_rePart_imPart_I_div_two`, `paperFT_rePart_imPart_neg_I_div_two`,
`testSource`, `testSource_eq`, `testSource_ae`, `testSource_add`, `testSource_smul`, `doubledSource`,
`doubledSource_apply`, `finrank_le_finrank_boundStateSpace_of_negative_subspace`,
`finrank_le_rank_boundStateSpace_of_negative_subspace`, `weilNegIndex_le_finrank_boundStateSpace`,
`card_le_finrank_boundStateSpace_add_two`.

## Big picture
- Two-sided bound-state count: `weilNegIndex ζ a ε ≤ dim P` (all `a`, `ε ≥ 0`), `|T| − 2 ≤ dim P`
  for visible separated deep zero sets `T`, and (MUST-1553) orthonormal primitive eigenfamilies
  have size `≤ 2·#off-line zeros` when that set is finite. `RH ⟺ P = ℝ·1`.
- The polar-constrained hyperplane is the natural domain where the Weil form and the Doob energy
  coincide; the even sector (MUST-1556) is the other such domain (after primitive projection).

## Next conjectures
1. Finite off-line zero set ⟹ `P` finite-dimensional with `dim P ≤ 2·#off-line + 1`
   (orthogonal decomposition of `P` into eigenspaces; needs that `P` is spanned by an orthonormal
   eigenfamily).
2. Sharp count: eigenvalue multiplicities equal the number of zero pairs in a window, via the
   corpus upper inertia law (`weilNegIndex ≤ #offLinePairsBelow`).
3. Eigenvalue–zero quantitative dictionary: bound the top eigenvalue below in terms of the depth
   `δ` of a visible zero (Rayleigh quotient of the corpus `sinhTest` lift).
