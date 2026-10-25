import GaloisForLFunctions.SignedSuccessorArithmetic.TheForwardDilatedHypercubeForm
import GaloisForLFunctions.BezoutValuationIncidence.CyclotomicLogarithmFormulaForThePronicGram

/-!
# Forward–backward dilation normality, subsequence admission, Möbius sieve uniqueness, and the folded zero-damping profile

This module establishes four structural laws connecting the forward- and backward-dilated
realizations of `sizeHypercubeForm`, subsequence (`liminf`) receiver admission, harmonic uniqueness
of the Möbius sieve weights, and the explicit trigonometric zero-damping profile at `r = 2`:

1. **Forward–backward dilation normality (`norm_sq_weightedForwardVector_eq_backward`,
   `norm_backwardDilatedVector_eq_forwardDilatedVector`).**
   Because the positive ray dilations `{D_t}_{t > 0}` form a commutative unitary group on `SoninL2`
   with `D_d^* = D_{1/d}`, the Gram matrices of `{D_d v_r}` and `{D_{1/d} v_r}` are transposes of
   one another (`Φ_r(d₁/d₂)` vs `Φ_r(d₂/d₁)`). Every real-weighted forward dilation combination
   `∑_{d ∈ S} a_d D_d v_r` therefore has the exact same `SoninL2` norm as its backward-dilated
   counterpart `∑_{d ∈ S} a_d D_{1/d} v_r`.

2. **Cutoff-independence of the natural head and subsequence (`∃ᶠ D in atTop`) admission
   (`pronicNorm_naturalDilationPrimitive_mono`,
   `mem_receiverDampings_of_frequently_bounded_sizeHypercubeForm`,
   `riemannHypothesis_of_cofinal_frequently_bounded_sizeHypercubeForm`,
   `riemannHypothesis_of_cofinal_frequently_bounded_forwardDilated_Ioo`,
   `riemannHypothesis_of_cofinal_frequently_bounded_alternating_moebius_Ioo`).**
   For `n ≤ N`, `naturalDilationPrimitive ε N r n` coincides with a cutoff-independent arithmetic
   profile `naturalDilationLimit ε r n`, making the head pronic norm
   `N ↦ pronicNorm (naturalDilationPrimitive ε N r) N` monotone nondecreasing in `N`. Consequently,
   boundedness of `sizeHypercubeForm hp.one_lt ε D` (or `∫_1^D G_{ε,D}(1/u)² du`) along **any
   unbounded subsequence** `D_k → ∞` (`∃ᶠ D in atTop`) suffices to force `ε ∈ receiverDampings`,
   self-improving to uniform head boundedness across **all** cutoffs `N` and **all** moduli `r > 1`.

3. **Uniqueness of Möbius weights from the integer-dilate sieve equation
   (`eq_moebiusReal_of_sieve_functional_equation`).**
   Among all bounded real arithmetic sequences `w : ℕ → ℝ` (`w 0 = 0`), `moebiusReal` is the unique
   weight whose forward-dilated series `F_w(x) = ∑_{d ≥ 1} w(d) d^{−1−ε} C_r(⌊d x⌋)` satisfies the
   sieve functional equation `∑_{m ≥ 1} m^{−1−ε} F_w(m x) = C_r(⌊x⌋)` on `[0, ∞)`, proved for every
   modulus `r > 1` by strong induction on the finite-cell Fourier modes on `[0, r]`.

4. **Explicit `ε = 0` folded trigonometric profile and all-harmonic sieve identity at `r = 2`
   (`foldedZeroDampingProfile_eq_sin_cube`, `sum_dilated_foldedZeroDampingProfile_fourier_eq`).**
   The two-harmonic profile `G_0(x) = (2/π) sin(π x) − (1/π) sin(2π x) = (4/π) sin(π x) sin²(π x / 2)`
   is `2`-periodic, odd, strictly positive on `(0, 1)`, strictly negative on `(1, 2)`, orthogonal to
   every higher sine harmonic `sin(π n x)` (`n ≥ 3`), and satisfies the exact `ε = 0` dilated sieve
   identity in every sine Fourier mode `n ≥ 1` on `[0, 2]`:
   `∑_{m=1}^n (1/m) ∫_0^2 G_0(m u) sin(π n u) du = ∫_0^2 C_2(⌊u⌋) sin(π n u) du`.
-/

namespace GaloisForLFunctions.SignedSuccessorArithmetic

open MeasureTheory Set Finset Filter Topology
open _root_.RHTower GaloisForLFunctions.BezoutValuationIncidence
open scoped BigOperators

/-! ## §1. Forward–backward dilation normality on `SoninL2` -/

/-- General real-weighted forward-dilated `SoninL2` vector `∑_{d ∈ S} a_d D_d v_r`. -/
noncomputable def weightedForwardVector {r : ℕ} (hr : 1 < r) (S : Finset ℕ) (a : ℕ → ℝ) : SoninL2 :=
  ∑ d ∈ S, ((a d : ℝ) : ℂ) • rayDilate (d : ℝ) (pmRamanujanStepVector r hr)

/-- General real-weighted backward-dilated `SoninL2` vector `∑_{d ∈ S} a_d D_{1/d} v_r`. -/
noncomputable def weightedBackwardVector {r : ℕ} (hr : 1 < r) (S : Finset ℕ) (a : ℕ → ℝ) :
    SoninL2 :=
  ∑ d ∈ S, ((a d : ℝ) : ℂ) • rayDilate (d : ℝ)⁻¹ (pmRamanujanStepVector r hr)

/-- Quadratic-form expansion of `‖weightedForwardVector hr S a‖²`. -/
theorem norm_sq_weightedForwardVector_eq {r : ℕ} (hr : 1 < r) {S : Finset ℕ}
    (hS : ∀ d ∈ S, 0 < d) (a : ℕ → ℝ) :
    ‖weightedForwardVector hr S a‖ ^ 2 =
      ∑ d₁ ∈ S, ∑ d₂ ∈ S, a d₁ * a d₂ * pmRamanujanDilationProfile r hr ((d₁ : ℝ) / d₂) := by
  have hre : ‖weightedForwardVector hr S a‖ ^ 2 =
      (inner ℂ (weightedForwardVector hr S a) (weightedForwardVector hr S a)).re := by
    rw [inner_self_eq_norm_sq_to_K]
    norm_cast
  rw [hre, weightedForwardVector, sum_inner, Complex.re_sum]
  refine Finset.sum_congr rfl fun d₁ hd₁ => ?_
  rw [inner_sum, Complex.re_sum]
  refine Finset.sum_congr rfl fun d₂ hd₂ => ?_
  have hd₁0 : (0 : ℝ) < d₁ := by exact_mod_cast hS d₁ hd₁
  have hd₂0 : (0 : ℝ) < d₂ := by exact_mod_cast hS d₂ hd₂
  rw [inner_smul_left, inner_smul_right, Complex.conj_ofReal, ← mul_assoc,
    ← Complex.ofReal_mul, Complex.re_ofReal_mul, re_inner_rayDilate_self hr hd₁0 hd₂0]

/-- Quadratic-form expansion of `‖weightedBackwardVector hr S a‖²`. -/
theorem norm_sq_weightedBackwardVector_eq {r : ℕ} (hr : 1 < r) {S : Finset ℕ}
    (hS : ∀ d ∈ S, 0 < d) (a : ℕ → ℝ) :
    ‖weightedBackwardVector hr S a‖ ^ 2 =
      ∑ d₁ ∈ S, ∑ d₂ ∈ S, a d₁ * a d₂ * pmRamanujanDilationProfile r hr ((d₂ : ℝ) / d₁) := by
  have hre : ‖weightedBackwardVector hr S a‖ ^ 2 =
      (inner ℂ (weightedBackwardVector hr S a) (weightedBackwardVector hr S a)).re := by
    rw [inner_self_eq_norm_sq_to_K]
    norm_cast
  rw [hre, weightedBackwardVector, sum_inner, Complex.re_sum]
  refine Finset.sum_congr rfl fun d₁ hd₁ => ?_
  rw [inner_sum, Complex.re_sum]
  refine Finset.sum_congr rfl fun d₂ hd₂ => ?_
  have hd₁0 : (0 : ℝ) < d₁ := by exact_mod_cast hS d₁ hd₁
  have hd₂0 : (0 : ℝ) < d₂ := by exact_mod_cast hS d₂ hd₂
  rw [inner_smul_left, inner_smul_right, Complex.conj_ofReal, ← mul_assoc,
    ← Complex.ofReal_mul, Complex.re_ofReal_mul,
    re_inner_rayDilate_self hr (inv_pos.mpr hd₁0) (inv_pos.mpr hd₂0),
    show (d₁ : ℝ)⁻¹ / (d₂ : ℝ)⁻¹ = (d₂ : ℝ) / d₁ by field_simp]

/-- **Forward–backward dilation normality on `SoninL2`.**
For every modulus `r > 1`, finite set `S` of positive integers, and real weight `a : ℕ → ℝ`, the
forward-dilated combination `∑_{d ∈ S} a_d D_d v_r` and the backward-dilated combination
`∑_{d ∈ S} a_d D_{1/d} v_r` have identical squared `SoninL2` norms. -/
theorem norm_sq_weightedForwardVector_eq_backward {r : ℕ} (hr : 1 < r) {S : Finset ℕ}
    (hS : ∀ d ∈ S, 0 < d) (a : ℕ → ℝ) :
    ‖weightedForwardVector hr S a‖ ^ 2 = ‖weightedBackwardVector hr S a‖ ^ 2 := by
  rw [norm_sq_weightedForwardVector_eq hr hS a, norm_sq_weightedBackwardVector_eq hr hS a]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun d₁ _ => Finset.sum_congr rfl fun d₂ _ => by ring

/-- Norm equality `‖∑_{d ∈ S} a_d D_d v_r‖ = ‖∑_{d ∈ S} a_d D_{1/d} v_r‖`. -/
theorem norm_weightedForwardVector_eq_backward {r : ℕ} (hr : 1 < r) {S : Finset ℕ}
    (hS : ∀ d ∈ S, 0 < d) (a : ℕ → ℝ) :
    ‖weightedForwardVector hr S a‖ = ‖weightedBackwardVector hr S a‖ := by
  have hsq := norm_sq_weightedForwardVector_eq_backward hr hS a
  have h1 := norm_nonneg (weightedForwardVector hr S a)
  have h2 := norm_nonneg (weightedBackwardVector hr S a)
  nlinarith

/-- Size-truncated backward-dilated Möbius–Ramanujan vector
`∑_{1 ≤ d ≤ D} μ(d) d^{−1/2−ε} D_{1/d} v_r`. -/
noncomputable def backwardDilatedVector {r : ℕ} (hr : 1 < r) (ε : ℝ) (D : ℕ) : SoninL2 :=
  weightedBackwardVector hr (Finset.Icc 1 D) (fun d => moebiusReal d * (d : ℝ) ^ (-(1 / 2 : ℝ) - ε))

/-- Backward-dilated Hilbert-norm realization of `sizeHypercubeForm`. -/
theorem norm_sq_backwardDilatedVector_eq_sizeHypercubeForm {r : ℕ} (hr : 1 < r)
    (ε : ℝ) (D : ℕ) :
    ‖backwardDilatedVector hr ε D‖ ^ 2 = sizeHypercubeForm hr ε D := by
  have heq : forwardDilatedVector hr ε D =
      weightedForwardVector hr (Finset.Icc 1 D)
        (fun d => moebiusReal d * (d : ℝ) ^ (-(1 / 2 : ℝ) - ε)) := rfl
  rw [backwardDilatedVector,
    ← norm_sq_weightedForwardVector_eq_backward hr (fun _ hd => (Finset.mem_Icc.mp hd).1),
    ← heq, norm_sq_forwardDilatedVector_eq_sizeHypercubeForm]

/-- Exact norm symmetry between the backward- and forward-dilated Möbius vectors. -/
theorem norm_backwardDilatedVector_eq_forwardDilatedVector {r : ℕ} (hr : 1 < r)
    (ε : ℝ) (D : ℕ) :
    ‖backwardDilatedVector hr ε D‖ = ‖forwardDilatedVector hr ε D‖ := by
  have heq : forwardDilatedVector hr ε D =
      weightedForwardVector hr (Finset.Icc 1 D)
        (fun d => moebiusReal d * (d : ℝ) ^ (-(1 / 2 : ℝ) - ε)) := rfl
  rw [backwardDilatedVector, heq,
    norm_weightedForwardVector_eq_backward hr (fun _ hd => (Finset.mem_Icc.mp hd).1)]

/-! ## §2. Cutoff-independence of the natural head, monotonicity, and subsequence admission -/

/-- The cutoff-independent arithmetic limit profile of `naturalDilationPrimitive` below its horizon:
`G_r(n) = α_ε Re C_r(n) + ∑_{ab = r} a μ(b) A_ε(⌊n / a⌋)`. -/
noncomputable def naturalDilationLimit (ε : ℝ) (r n : ℕ) : ℝ :=
  (pmPowerDampedDivisorDensity ε).re * (pmRamanujanPrimitive r n).re +
    ∑ x ∈ r.divisorsAntidiagonal,
      (x.1 : ℝ) * moebiusReal x.2 * pmPowerDampedCenteredDivisorPrefix ε (n / x.1)

/-- Below the cutoff `n ≤ N`, `naturalDilationPrimitive ε N r n` is completely independent of `N`. -/
theorem naturalDilationPrimitive_eq_limit (ε : ℝ) (r : ℕ) {N n : ℕ} (hn : n ≤ N) :
    naturalDilationPrimitive ε N r n = naturalDilationLimit ε r n := by
  rw [naturalDilationPrimitive_eq ε r hn, naturalDilationLimit, pmRamanujanPrimitive_re_eq_floor,
    Finset.mul_sum, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun _ _ => by ring

/-- The head pronic norm of `naturalDilationPrimitive ε N r` coincides with the `N`-truncated
pronic norm of the single `N`-independent sequence `naturalDilationLimit ε r`. -/
theorem pronicNorm_naturalDilationPrimitive_eq_limit (ε : ℝ) (r N : ℕ) :
    TransHorizonIncidenceMechanics.pronicNorm (naturalDilationPrimitive ε N r) N =
      TransHorizonIncidenceMechanics.pronicNorm (naturalDilationLimit ε r) N :=
  BezoutValuationIncidence.pnorm_congr fun _ hn =>
    naturalDilationPrimitive_eq_limit ε r (Finset.mem_Icc.mp hn).2

/-- Monotonicity of `pronicNorm f` in the window cutoff `N`. -/
theorem pronicNorm_mono_cutoff (f : ℕ → ℝ) {M N : ℕ} (hMN : M ≤ N) :
    TransHorizonIncidenceMechanics.pronicNorm f M ≤
      TransHorizonIncidenceMechanics.pronicNorm f N := by
  unfold TransHorizonIncidenceMechanics.pronicNorm
  exact Real.sqrt_le_sqrt (Finset.sum_le_sum_of_subset_of_nonneg
    (Finset.Icc_subset_Icc_right hMN) fun _ _ _ => by positivity)

/-- **Monotonicity of the natural dilation head norm in the cutoff `N`.**
Because `naturalDilationPrimitive ε N r` stabilizes pointwise on `1 ≤ n ≤ N`, its head pronic norm
is monotone nondecreasing in `N` at every damping `ε ∈ ℝ` and every modulus `r`. -/
theorem pronicNorm_naturalDilationPrimitive_mono (ε : ℝ) (r : ℕ) {M N : ℕ} (hMN : M ≤ N) :
    TransHorizonIncidenceMechanics.pronicNorm (naturalDilationPrimitive ε M r) M ≤
      TransHorizonIncidenceMechanics.pronicNorm (naturalDilationPrimitive ε N r) N := by
  rw [pronicNorm_naturalDilationPrimitive_eq_limit, pronicNorm_naturalDilationPrimitive_eq_limit]
  exact pronicNorm_mono_cutoff _ hMN

/-- **Subsequence (`∃ᶠ D in atTop`) admission theorem.**
If at a prime core `p` and damping `ε > 0`, `sizeHypercubeForm hp.one_lt ε D ≤ B` holds merely
infinitely often (`∃ᶠ D in atTop`, i.e., `liminf_{D → ∞} sizeHypercubeForm hp.one_lt ε D < ∞`),
then `ε ∈ receiverDampings`. -/
theorem mem_receiverDampings_of_frequently_bounded_sizeHypercubeForm {p : ℕ} (hp : p.Prime)
    {ε : ℝ} (hε0 : 0 < ε) {B : ℝ}
    (hfreq : ∃ᶠ D : ℕ in atTop, sizeHypercubeForm hp.one_lt ε D ≤ B) :
    ε ∈ receiverDampings := by
  refine mem_receiverDampings_of_bounded_naturalDilationHeadEnergy hp hε0
    ⟨Real.sqrt (max B 0), fun N => ?_⟩
  obtain ⟨D, hND, hBD⟩ := Filter.frequently_atTop.mp hfreq N
  refine (pronicNorm_naturalDilationPrimitive_mono ε p hND).trans ?_
  rw [← Real.sqrt_sq (TransHorizonIncidenceMechanics.pronicNorm_nonneg _ _)]
  exact Real.sqrt_le_sqrt
    ((pronicNorm_naturalDilationPrimitive_sq_le_sizeHypercubeForm hp.one_lt ε D).trans
      (hBD.trans (le_max_left _ _)))

/-- **Subsequence self-improvement across all cutoffs and all moduli.**
If `sizeHypercubeForm hp.one_lt ε D ≤ B` holds infinitely often at a single prime `p` (`ε > 0`),
then for **every** modulus `r > 1` (prime or composite) the natural head pronic norm is bounded
uniformly across **all** cutoffs `N : ℕ`. -/
theorem bounded_all_naturalDilationHeadEnergy_of_frequently_bounded_sizeHypercubeForm
    {p : ℕ} (hp : p.Prime) {ε : ℝ} (hε0 : 0 < ε) {B : ℝ}
    (hfreq : ∃ᶠ D : ℕ in atTop, sizeHypercubeForm hp.one_lt ε D ≤ B)
    {r : ℕ} (hr : 1 < r) :
    ∃ K : ℝ, ∀ N : ℕ,
      TransHorizonIncidenceMechanics.pronicNorm (naturalDilationPrimitive ε N r) N ≤ K :=
  bounded_naturalDilationHeadEnergy_of_mem_receiverDampings
    (mem_receiverDampings_of_frequently_bounded_sizeHypercubeForm hp hε0 hfreq) hr

/-- **Subsequence forward-dilated `L²(1, D)` admission.**
If `∫_1^D G_{ε,D}(1/u)² du ≤ B` holds infinitely often at a prime core `p` (`ε > 0`), then
`ε ∈ receiverDampings`. -/
theorem mem_receiverDampings_of_frequently_bounded_forwardDilated_Ioo {p : ℕ} (hp : p.Prime)
    {ε : ℝ} (hε0 : 0 < ε) {B : ℝ}
    (hfreq : ∃ᶠ D : ℕ in atTop,
      (∫ u in Set.Ioo (1 : ℝ) D, forwardDilatedPrimitive p ε D u⁻¹ ^ 2) ≤ B) :
    ε ∈ receiverDampings := by
  refine mem_receiverDampings_of_frequently_bounded_sizeHypercubeForm hp hε0
    (B := B + (pmRamanujanPrimitiveBound p * ∑' d : ℕ, ((d : ℝ) ^ (1 + ε))⁻¹) ^ 2) ?_
  exact hfreq.mono fun D hD =>
    (sizeHypercubeForm_le_forwardDilated_Ioo_add_const hp.one_lt hε0 D).trans
      (add_le_add hD le_rfl)

/-- **Cofinal subsequence (`liminf`) `sizeHypercubeForm` criterion for `RiemannHypothesis`.** -/
theorem riemannHypothesis_of_cofinal_frequently_bounded_sizeHypercubeForm {p : ℕ} (hp : p.Prime)
    (h : ∀ δ : ℝ, 0 < δ → ∃ ε : ℝ, 0 < ε ∧ ε < δ ∧
      ∃ B : ℝ, ∃ᶠ D : ℕ in atTop, sizeHypercubeForm hp.one_lt ε D ≤ B) :
    RiemannHypothesis := by
  refine riemannHypothesis_of_accPt_zero_receiverDampings (accPt_zero_receiverDampings_iff.mpr ?_)
  intro δ hδ
  obtain ⟨ε, hε0, hεδ, B, hfreq⟩ := h δ hδ
  exact ⟨ε, hε0, hεδ,
    (mem_receiverDampings_of_frequently_bounded_sizeHypercubeForm hp hε0 hfreq).2⟩

/-- **Cofinal subsequence (`liminf`) forward-dilated `L²(1, D)` criterion for `RiemannHypothesis`.** -/
theorem riemannHypothesis_of_cofinal_frequently_bounded_forwardDilated_Ioo {p : ℕ} (hp : p.Prime)
    (h : ∀ δ : ℝ, 0 < δ → ∃ ε : ℝ, 0 < ε ∧ ε < δ ∧
      ∃ B : ℝ, ∃ᶠ D : ℕ in atTop,
        (∫ u in Set.Ioo (1 : ℝ) D, forwardDilatedPrimitive p ε D u⁻¹ ^ 2) ≤ B) :
    RiemannHypothesis := by
  refine riemannHypothesis_of_accPt_zero_receiverDampings (accPt_zero_receiverDampings_iff.mpr ?_)
  intro δ hδ
  obtain ⟨ε, hε0, hεδ, B, hfreq⟩ := h δ hδ
  exact ⟨ε, hε0, hεδ,
    (mem_receiverDampings_of_frequently_bounded_forwardDilated_Ioo hp hε0 hfreq).2⟩

/-- **Cofinal subsequence alternating-Möbius `L²(1, D)` criterion for `RiemannHypothesis` (`r = 2`).** -/
theorem riemannHypothesis_of_cofinal_frequently_bounded_alternating_moebius_Ioo
    (h : ∀ δ : ℝ, 0 < δ → ∃ ε : ℝ, 0 < ε ∧ ε < δ ∧ ∃ B : ℝ, ∃ᶠ D : ℕ in atTop,
      (∫ u in Set.Ioo (1 : ℝ) D,
        (∑ d ∈ Finset.Icc 1 D,
          moebiusReal d * (d : ℝ) ^ (-1 - ε) * ((⌊(d : ℝ) / u⌋₊ % 2 : ℕ) : ℝ)) ^ 2) ≤ B) :
    RiemannHypothesis := by
  refine riemannHypothesis_of_cofinal_frequently_bounded_forwardDilated_Ioo Nat.prime_two
    fun δ hδ => ?_
  obtain ⟨ε, hε0, hεδ, B, hfreq⟩ := h δ hδ
  refine ⟨ε, hε0, hεδ, B, hfreq.mono fun D hD => ?_⟩
  refine hD.trans_eq' (setIntegral_congr_fun measurableSet_Ioo fun u _ => ?_)
  rw [forwardDilatedPrimitive_two_eq, neg_sq]
  simp only [div_eq_mul_inv]

/-! ## §3. Uniqueness of Möbius weights from the integer-dilate sieve equation -/

/-- Forward-dilated Ramanujan series `F_w(x) = ∑_{d ≥ 1} w(d) d^{−1−ε} C_r(⌊d x⌋)` with general
arithmetic weight `w : ℕ → ℝ`. -/
noncomputable def weightedForwardDilatedLimit (w : ℕ → ℝ) (r : ℕ) (ε : ℝ) (x : ℝ) : ℝ :=
  ∑' d : ℕ, w d * (d : ℝ) ^ (-1 - ε) * (pmRamanujanPrimitive r ⌊(d : ℝ) * x⌋₊).re

theorem summable_weightedForwardDilatedLimit_term {w : ℕ → ℝ} {W : ℝ} (hw : ∀ d, |w d| ≤ W)
    {r : ℕ} (hr : 1 < r) {ε : ℝ} (hε : 0 < ε) (x : ℝ) :
    Summable (fun d : ℕ =>
      w d * (d : ℝ) ^ (-1 - ε) * (pmRamanujanPrimitive r ⌊(d : ℝ) * x⌋₊).re) := by
  have hW0 : 0 ≤ W := (abs_nonneg (w 0)).trans (hw 0)
  have hsum : Summable (fun d : ℕ => (W * pmRamanujanPrimitiveBound r) * ((d : ℝ) ^ (1 + ε))⁻¹) :=
    (Real.summable_nat_rpow_inv.mpr (by linarith)).mul_left _
  refine hsum.of_norm_bounded fun d => ?_
  rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg d) _),
    show (-1 - ε : ℝ) = -(1 + ε) by ring, Real.rpow_neg (Nat.cast_nonneg d)]
  have hC : |(pmRamanujanPrimitive r ⌊(d : ℝ) * x⌋₊).re| ≤ pmRamanujanPrimitiveBound r :=
    (Complex.abs_re_le_norm _).trans (norm_pmRamanujanPrimitive_le hr _)
  calc |w d| * ((d : ℝ) ^ (1 + ε))⁻¹ * |(pmRamanujanPrimitive r ⌊(d : ℝ) * x⌋₊).re|
      ≤ W * ((d : ℝ) ^ (1 + ε))⁻¹ * pmRamanujanPrimitiveBound r :=
        mul_le_mul (mul_le_mul_of_nonneg_right (hw d)
          (inv_nonneg.mpr (Real.rpow_nonneg (Nat.cast_nonneg d) _))) hC (abs_nonneg _)
          (by positivity)
    _ = _ := by ring

/-- **General Dirichlet convolution expansion of `∑_{m ≥ 1} m^{−1−ε} F_w(m x)`.** -/
theorem hasSum_weightedForwardDilatedLimit_mul {w : ℕ → ℝ} (hw0 : w 0 = 0) {W : ℝ}
    (hw : ∀ d, |w d| ≤ W) {r : ℕ} (hr : 1 < r) {ε : ℝ} (hε : 0 < ε) (x : ℝ) :
    HasSum (fun m : ℕ =>
        if m = 0 then 0 else (m : ℝ) ^ (-1 - ε) * weightedForwardDilatedLimit w r ε ((m : ℝ) * x))
      (∑' j : ℕ,
        (∑ d ∈ j.divisors, w d) * (j : ℝ) ^ (-1 - ε) *
          (pmRamanujanPrimitive r ⌊(j : ℝ) * x⌋₊).re) := by
  have hW0 : 0 ≤ W := (abs_nonneg (w 0)).trans (hw 0)
  set H : ℕ × ℕ → ℝ := fun p =>
    if p.1 = 0 then 0
    else (p.1 : ℝ) ^ (-1 - ε) *
      (w p.2 * (p.2 : ℝ) ^ (-1 - ε) *
        (pmRamanujanPrimitive r ⌊((p.1 * p.2 : ℕ) : ℝ) * x⌋₊).re)
  have hz : Summable (fun m : ℕ => ‖(m : ℝ) ^ (-1 - ε)‖) := by
    simpa [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _)] using
      (Real.summable_nat_rpow.mpr (by linarith : -1 - ε < -1))
  have hprod : Summable (fun p : ℕ × ℕ => (p.1 : ℝ) ^ (-1 - ε) * (p.2 : ℝ) ^ (-1 - ε)) :=
    summable_mul_of_summable_norm (f := fun m : ℕ => (m : ℝ) ^ (-1 - ε))
      (g := fun m : ℕ => (m : ℝ) ^ (-1 - ε)) hz hz
  have hB0 : 0 ≤ pmRamanujanPrimitiveBound r :=
    (abs_nonneg _).trans ((Complex.abs_re_le_norm _).trans (norm_pmRamanujanPrimitive_le hr 0))
  have hHb : ∀ p : ℕ × ℕ, ‖H p‖ ≤
      (W * pmRamanujanPrimitiveBound r) * ((p.1 : ℝ) ^ (-1 - ε) * (p.2 : ℝ) ^ (-1 - ε)) :=
    fun p => by
      rw [Real.norm_eq_abs]
      dsimp only [H]
      split_ifs with hp1
      · rw [abs_zero]
        exact mul_nonneg (mul_nonneg hW0 hB0)
          (mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _)
            (Real.rpow_nonneg (Nat.cast_nonneg _) _))
      · rw [abs_mul, abs_mul, abs_mul,
          abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _),
          abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _)]
        have hC : |(pmRamanujanPrimitive r ⌊((p.1 * p.2 : ℕ) : ℝ) * x⌋₊).re| ≤
            pmRamanujanPrimitiveBound r :=
          (Complex.abs_re_le_norm _).trans (norm_pmRamanujanPrimitive_le hr _)
        calc (p.1 : ℝ) ^ (-1 - ε) *
              (|w p.2| * (p.2 : ℝ) ^ (-1 - ε) *
                |(pmRamanujanPrimitive r ⌊((p.1 * p.2 : ℕ) : ℝ) * x⌋₊).re|)
            ≤ (p.1 : ℝ) ^ (-1 - ε) *
              (W * (p.2 : ℝ) ^ (-1 - ε) * pmRamanujanPrimitiveBound r) :=
              mul_le_mul_of_nonneg_left
                (mul_le_mul (mul_le_mul_of_nonneg_right (hw p.2)
                  (Real.rpow_nonneg (Nat.cast_nonneg _) _)) hC (abs_nonneg _)
                  (by positivity))
                (Real.rpow_nonneg (Nat.cast_nonneg _) _)
          _ = _ := by ring
  have hH : Summable H := (hprod.mul_left _).of_norm_bounded hHb
  have hrow : ∀ m : ℕ, HasSum (fun d => H (m, d))
      (if m = 0 then 0
        else (m : ℝ) ^ (-1 - ε) * weightedForwardDilatedLimit w r ε ((m : ℝ) * x)) := by
    intro m
    rcases eq_or_ne m 0 with rfl | hm
    · simp [H]
    · simp only [if_neg hm, H]
      refine ((summable_weightedForwardDilatedLimit_term hw hr hε ((m : ℝ) * x)).hasSum.mul_left
        ((m : ℝ) ^ (-1 - ε))).congr_fun fun d => ?_
      rw [show ((m * d : ℕ) : ℝ) * x = (d : ℝ) * ((m : ℝ) * x) by push_cast; ring]
  have hval : ∀ j : ℕ, ∑' p : ((fun p : ℕ × ℕ => p.1 * p.2) ⁻¹' {j}), H p =
      (∑ d ∈ j.divisors, w d) * (j : ℝ) ^ (-1 - ε) *
        (pmRamanujanPrimitive r ⌊(j : ℝ) * x⌋₊).re := by
    intro j
    rcases eq_or_ne j 0 with rfl | hj
    · have h0 : ∀ p : ((fun p : ℕ × ℕ => p.1 * p.2) ⁻¹' {0}), H p = 0 := fun p => by
        rcases Nat.mul_eq_zero.mp p.2 with hp1 | hp2
        · simp [H, hp1]
        · simp [H, hp2, hw0]
      rw [tsum_congr h0, tsum_zero, Nat.divisors_zero, Finset.sum_empty, zero_mul, zero_mul]
    · rw [show (fun p : ℕ × ℕ => p.1 * p.2) ⁻¹' {j} = j.divisorsAntidiagonal by ext; simp [hj],
        Finset.tsum_subtype' j.divisorsAntidiagonal H]
      have hfac : ∀ p ∈ j.divisorsAntidiagonal, H p =
          ((j : ℝ) ^ (-1 - ε) * (pmRamanujanPrimitive r ⌊(j : ℝ) * x⌋₊).re) * w p.2 :=
        fun p hp => by
          have hmul : p.1 * p.2 = j := (Nat.mem_divisorsAntidiagonal.mp hp).1
          have hp1 : p.1 ≠ 0 := fun h0 => hj (by rw [← hmul, h0, zero_mul])
          dsimp only [H]
          rw [if_neg hp1, hmul]
          have hrp : (p.1 : ℝ) ^ (-1 - ε) * (p.2 : ℝ) ^ (-1 - ε) = (j : ℝ) ^ (-1 - ε) := by
            rw [← Real.mul_rpow (Nat.cast_nonneg _) (Nat.cast_nonneg _), ← Nat.cast_mul, hmul]
          linear_combination w p.2 * (pmRamanujanPrimitive r ⌊(j : ℝ) * x⌋₊).re * hrp
      rw [Finset.sum_congr rfl hfac, ← Finset.mul_sum,
        Nat.sum_divisorsAntidiagonal' (fun _ b => w b)]
      ring
  have hfib := hH.hasSum.tsum_fiberwise (fun p : ℕ × ℕ => p.1 * p.2)
  rw [show (fun j : ℕ => ∑' p : ((fun p : ℕ × ℕ => p.1 * p.2) ⁻¹' {j}), H p) =
    fun j : ℕ => (∑ d ∈ j.divisors, w d) * (j : ℝ) ^ (-1 - ε) *
      (pmRamanujanPrimitive r ⌊(j : ℝ) * x⌋₊).re from funext hval] at hfib
  rw [hfib.tsum_eq]
  exact hH.hasSum.prod_fiberwise hrow

private theorem summable_divisorSum_rpow {w : ℕ → ℝ} {W : ℝ} (hw : ∀ d, |w d| ≤ W)
    {ε : ℝ} (hε : 0 < ε) :
    Summable (fun j : ℕ => |(∑ d ∈ j.divisors, w d) * (j : ℝ) ^ (-1 - ε)|) := by
  have hW0 : 0 ≤ W := (abs_nonneg (w 0)).trans (hw 0)
  have hz : Summable (fun m : ℕ => ‖(m : ℝ) ^ (-1 - ε)‖) := by
    simpa [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _)] using
      (Real.summable_nat_rpow.mpr (by linarith : -1 - ε < -1))
  have hprod : Summable (fun p : ℕ × ℕ => W * ((p.1 : ℝ) ^ (-1 - ε) * (p.2 : ℝ) ^ (-1 - ε))) :=
    (summable_mul_of_summable_norm (f := fun m : ℕ => (m : ℝ) ^ (-1 - ε))
      (g := fun m : ℕ => (m : ℝ) ^ (-1 - ε)) hz hz).mul_left W
  set H₀ : ℕ × ℕ → ℝ := fun p =>
    if p.1 = 0 ∨ p.2 = 0 then 0 else W * ((p.1 : ℝ) ^ (-1 - ε) * (p.2 : ℝ) ^ (-1 - ε))
  have hH₀ : Summable H₀ := hprod.of_norm_bounded fun p => by
    dsimp only [H₀]
    split_ifs <;> rw [Real.norm_eq_abs]
    · rw [abs_zero]
      exact mul_nonneg hW0 (mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _)
        (Real.rpow_nonneg (Nat.cast_nonneg _) _))
    · rw [abs_of_nonneg (mul_nonneg hW0 (mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _)
        (Real.rpow_nonneg (Nat.cast_nonneg _) _)))]
  have hfib := (hH₀.hasSum.tsum_fiberwise (fun p : ℕ × ℕ => p.1 * p.2)).summable
  refine hfib.of_nonneg_of_le (fun _ => abs_nonneg _) fun j => ?_
  rcases eq_or_ne j 0 with rfl | hj
  · simp only [Nat.divisors_zero, Finset.sum_empty, zero_mul, abs_zero]
    exact tsum_nonneg fun p => by dsimp only [H₀]; split_ifs <;> positivity
  · rw [show (fun p : ℕ × ℕ => p.1 * p.2) ⁻¹' {j} = j.divisorsAntidiagonal by ext; simp [hj],
      Finset.tsum_subtype' j.divisorsAntidiagonal H₀]
    have hfac : ∀ p ∈ j.divisorsAntidiagonal, H₀ p = W * (j : ℝ) ^ (-1 - ε) := fun p hp => by
      have hmul : p.1 * p.2 = j := (Nat.mem_divisorsAntidiagonal.mp hp).1
      have hp1 : p.1 ≠ 0 := fun h0 => hj (by rw [← hmul, h0, zero_mul])
      have hp2 : p.2 ≠ 0 := fun h0 => hj (by rw [← hmul, h0, mul_zero])
      dsimp only [H₀]
      rw [if_neg (by tauto), ← Real.mul_rpow (Nat.cast_nonneg _) (Nat.cast_nonneg _),
        ← Nat.cast_mul, hmul]
    have hcard : j.divisorsAntidiagonal.card = j.divisors.card := by
      rw [Finset.card_eq_sum_ones, Finset.card_eq_sum_ones]
      exact Nat.sum_divisorsAntidiagonal' (fun _ _ => 1)
    rw [Finset.sum_congr rfl hfac, Finset.sum_const, nsmul_eq_mul, hcard,
      abs_mul, abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg j) _)]
    have hsum_le : |∑ d ∈ j.divisors, w d| ≤ (j.divisors.card : ℝ) * W := by
      calc |∑ d ∈ j.divisors, w d|
          ≤ ∑ d ∈ j.divisors, |w d| := Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ _d ∈ j.divisors, W := Finset.sum_le_sum fun d _ => hw d
        _ = (j.divisors.card : ℝ) * W := by rw [Finset.sum_const, nsmul_eq_mul]
    calc |∑ d ∈ j.divisors, w d| * (j : ℝ) ^ (-1 - ε)
        ≤ ((j.divisors.card : ℝ) * W) * (j : ℝ) ^ (-1 - ε) :=
          mul_le_mul_of_nonneg_right hsum_le (Real.rpow_nonneg (Nat.cast_nonneg j) _)
      _ = (j.divisors.card : ℝ) * (W * (j : ℝ) ^ (-1 - ε)) := by ring

/-- Real-integral complex Fourier pairing `∫_a^b g(u) e^{−i ω u} du`. -/
private noncomputable def fourierPair (g : ℝ → ℝ) (a b ω : ℝ) : ℂ :=
  ((∫ u in a..b, g u * Real.cos (ω * u) : ℝ) : ℂ) -
    Complex.I * ((∫ u in a..b, g u * Real.sin (ω * u) : ℝ) : ℂ)

private theorem intervalIntegrable_of_bounded_measurable {g : ℝ → ℝ} (hg : Measurable g)
    {M : ℝ} (hM : ∀ u, |g u| ≤ M) {a b : ℝ} (hab : a ≤ b) :
    IntervalIntegrable g volume a b := by
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hab]
  refine (integrableOn_const (hs := measure_Ioc_lt_top.ne) (C := M)).mono'
    hg.aestronglyMeasurable ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with u _
  rw [Real.norm_eq_abs]
  exact hM u

private theorem intervalIntegrable_translated_cells {f : ℝ → ℝ} {M : ℝ}
    (hf : Measurable f) (hM : ∀ u, |f u| ≤ M) {L : ℝ} (hL : 0 ≤ L) (k : ℕ) :
    (∫ u in (0 : ℝ)..(k : ℝ) * L, f u) =
      ∑ m ∈ Finset.range k, ∫ θ in (0 : ℝ)..L, f (θ + (m : ℝ) * L) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Finset.sum_range_succ, ← ih]
    have hshift := intervalIntegral.integral_comp_add_right f ((k : ℝ) * L) (a := 0) (b := L)
    have he : L + (k : ℝ) * L = ((k + 1 : ℕ) : ℝ) * L := by push_cast; ring
    rw [zero_add, he] at hshift
    rw [hshift]
    exact (intervalIntegral.integral_add_adjacent_intervals
      (intervalIntegrable_of_bounded_measurable hf hM (mul_nonneg (Nat.cast_nonneg k) hL))
      (intervalIntegrable_of_bounded_measurable hf hM (by linarith))).symm

private theorem fourierPair_cells {g : ℝ → ℝ} {M : ℝ} (hg : Measurable g) (hM : ∀ u, |g u| ≤ M)
    {L : ℝ} (hL : 0 ≤ L) (ω : ℝ) (k : ℕ)
    (hper : ∀ m : ℕ, ∀ θ : ℝ, 0 ≤ θ → g (θ + (m : ℝ) * L) = g θ) :
    fourierPair g 0 ((k : ℝ) * L) ω =
      (∑ m ∈ Finset.range k, Complex.exp (-Complex.I * ((ω * L : ℝ) : ℂ)) ^ m) *
        fourierPair g 0 L ω := by
  have hM0 : 0 ≤ M := (abs_nonneg (g 0)).trans (hM 0)
  have hbc : ∀ u, |g u * Real.cos (ω * u)| ≤ M := fun u => by
    rw [abs_mul]; exact (mul_le_mul_of_nonneg_left (Real.abs_cos_le_one _) (abs_nonneg _)).trans
      (by linarith [hM u])
  have hbs : ∀ u, |g u * Real.sin (ω * u)| ≤ M := fun u => by
    rw [abs_mul]; exact (mul_le_mul_of_nonneg_left (Real.abs_sin_le_one _) (abs_nonneg _)).trans
      (by linarith [hM u])
  have hmc : Measurable (fun u => g u * Real.cos (ω * u)) :=
    hg.mul (Real.continuous_cos.measurable.comp (measurable_const.mul measurable_id))
  have hms : Measurable (fun u => g u * Real.sin (ω * u)) :=
    hg.mul (Real.continuous_sin.measurable.comp (measurable_const.mul measurable_id))
  unfold fourierPair
  rw [intervalIntegrable_translated_cells hmc hbc hL k,
    intervalIntegrable_translated_cells hms hbs hL k,
    Complex.ofReal_sum, Complex.ofReal_sum, Finset.mul_sum, ← Finset.sum_sub_distrib,
    Finset.sum_mul]
  refine Finset.sum_congr rfl fun m _ => ?_
  set α : ℝ := (m : ℝ) * (ω * L)
  have hexp : Complex.exp (-Complex.I * ((ω * L : ℝ) : ℂ)) ^ m =
      (Real.cos α : ℂ) - Complex.I * (Real.sin α : ℂ) := by
    rw [← Complex.exp_nat_mul, show (m : ℂ) * (-Complex.I * ((ω * L : ℝ) : ℂ)) =
        ((-α : ℝ) : ℂ) * Complex.I by push_cast [α]; ring,
      Complex.exp_mul_I, Complex.ofReal_neg, Complex.cos_neg, Complex.sin_neg,
      ← Complex.ofReal_cos, ← Complex.ofReal_sin]
    ring
  have hc_cell : (∫ θ in (0 : ℝ)..L, g (θ + (m : ℝ) * L) * Real.cos (ω * (θ + (m : ℝ) * L))) =
      Real.cos α * (∫ θ in (0 : ℝ)..L, g θ * Real.cos (ω * θ)) -
        Real.sin α * (∫ θ in (0 : ℝ)..L, g θ * Real.sin (ω * θ)) := by
    have hcongr : EqOn (fun θ => g (θ + (m : ℝ) * L) * Real.cos (ω * (θ + (m : ℝ) * L)))
        (fun θ => Real.cos α * (g θ * Real.cos (ω * θ)) -
          Real.sin α * (g θ * Real.sin (ω * θ))) (uIcc 0 L) := by
      intro θ hθ
      dsimp only
      rw [uIcc_of_le hL] at hθ
      rw [hper m θ hθ.1, show ω * (θ + (m : ℝ) * L) = ω * θ + α by dsimp [α]; ring,
        Real.cos_add]
      ring
    rw [intervalIntegral.integral_congr hcongr,
      intervalIntegral.integral_sub
        ((intervalIntegrable_of_bounded_measurable hmc hbc hL).const_mul _)
        ((intervalIntegrable_of_bounded_measurable hms hbs hL).const_mul _),
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
  have hs_cell : (∫ θ in (0 : ℝ)..L, g (θ + (m : ℝ) * L) * Real.sin (ω * (θ + (m : ℝ) * L))) =
      Real.sin α * (∫ θ in (0 : ℝ)..L, g θ * Real.cos (ω * θ)) +
        Real.cos α * (∫ θ in (0 : ℝ)..L, g θ * Real.sin (ω * θ)) := by
    have hcongr : EqOn (fun θ => g (θ + (m : ℝ) * L) * Real.sin (ω * (θ + (m : ℝ) * L)))
        (fun θ => Real.sin α * (g θ * Real.cos (ω * θ)) +
          Real.cos α * (g θ * Real.sin (ω * θ))) (uIcc 0 L) := by
      intro θ hθ
      dsimp only
      rw [uIcc_of_le hL] at hθ
      rw [hper m θ hθ.1, show ω * (θ + (m : ℝ) * L) = ω * θ + α by dsimp [α]; ring,
        Real.sin_add]
      ring
    rw [intervalIntegral.integral_congr hcongr,
      intervalIntegral.integral_add
        ((intervalIntegrable_of_bounded_measurable hmc hbc hL).const_mul _)
        ((intervalIntegrable_of_bounded_measurable hms hbs hL).const_mul _),
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
  rw [hc_cell, hs_cell, hexp]
  simp only [Complex.ofReal_sub, Complex.ofReal_add, Complex.ofReal_mul]
  have hI2 : Complex.I ^ 2 = -1 := Complex.I_sq
  linear_combination
    (-(Real.sin α : ℂ) * ((∫ θ in (0 : ℝ)..L, g θ * Real.sin (ω * θ) : ℝ) : ℂ)) * hI2

private theorem measurable_ramanujanFloor (r j : ℕ) :
    Measurable (fun u : ℝ => (pmRamanujanPrimitive r ⌊(j : ℝ) * u⌋₊).re) :=
  (measurable_of_countable (fun n : ℕ => (pmRamanujanPrimitive r n).re)).comp
    ((measurable_const.mul measurable_id).nat_floor)

private theorem fourierPair_ramanujanFloor_eq_zero_of_lt {r N j : ℕ} (hr : 1 < r)
    (hN : 1 ≤ N) (hj : N < j) :
    fourierPair (fun u => (pmRamanujanPrimitive r ⌊(j : ℝ) * u⌋₊).re)
      0 r (2 * Real.pi * N / r) = 0 := by
  have hj0 : (0 : ℝ) < j := by exact_mod_cast (by omega : 0 < j)
  have hr0 : (0 : ℝ) < r := by exact_mod_cast (lt_trans zero_lt_one hr)
  set L : ℝ := (r : ℝ) / j
  have hL : 0 ≤ L := div_nonneg hr0.le hj0.le
  have hkL : (j : ℝ) * L = r := mul_div_cancel₀ _ hj0.ne'
  have hper : ∀ m : ℕ, ∀ θ : ℝ, 0 ≤ θ →
      (pmRamanujanPrimitive r ⌊(j : ℝ) * (θ + (m : ℝ) * L)⌋₊).re =
        (pmRamanujanPrimitive r ⌊(j : ℝ) * θ⌋₊).re := by
    intro m θ hθ
    have hmul : (j : ℝ) * (θ + (m : ℝ) * L) = (j : ℝ) * θ + ((m * r : ℕ) : ℝ) := by
      dsimp [L]; push_cast; field_simp
    rw [hmul, Nat.floor_add_natCast (mul_nonneg hj0.le hθ) (m * r),
      pmRamanujanPrimitive_re_add_mul_self hr]
  have hcells := fourierPair_cells (measurable_ramanujanFloor r j)
    (fun u => (Complex.abs_re_le_norm _).trans (norm_pmRamanujanPrimitive_le hr _))
    hL (2 * Real.pi * N / r) j hper
  rw [hkL] at hcells
  rw [hcells]
  set ζ : ℂ := Complex.exp (-Complex.I * (((2 * Real.pi * N / r) * L : ℝ) : ℂ))
  have hωL : (2 * Real.pi * N / r) * L = 2 * Real.pi * N / j := by
    dsimp [L]; field_simp
  have hζ_pow : ζ ^ j = 1 := by
    dsimp [ζ]
    rw [hωL, ← Complex.exp_nat_mul]
    have hexp : (j : ℂ) * (-Complex.I * ((2 * Real.pi * (N : ℝ) / j : ℝ) : ℂ)) =
        ((-N : ℤ) : ℂ) * (2 * Real.pi * Complex.I) := by
      have hjC : (j : ℂ) ≠ 0 := by exact_mod_cast hj0.ne'
      push_cast; field_simp
    rw [hexp, Complex.exp_int_mul_two_pi_mul_I]
  have hζ_ne : ζ ≠ 1 := by
    intro h1
    dsimp [ζ] at h1
    rw [hωL, Complex.exp_eq_one_iff] at h1
    obtain ⟨n, hn⟩ := h1
    have h2pi : (2 * Real.pi * Complex.I : ℂ) ≠ 0 :=
      mul_ne_zero (mul_ne_zero two_ne_zero (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero))
        Complex.I_ne_zero
    have hrat : ((- (N : ℝ) / j : ℝ) : ℂ) * (2 * Real.pi * Complex.I) =
        (n : ℂ) * (2 * Real.pi * Complex.I) := by
      push_cast at hn ⊢
      simp only [div_eq_mul_inv] at hn ⊢
      linear_combination hn
    have hEqC := mul_right_cancel₀ h2pi hrat
    have hEqR : -(N : ℝ) / (j : ℝ) = (n : ℝ) := by exact_mod_cast hEqC
    have hmulR : (N : ℝ) = ((-n : ℤ) : ℝ) * (j : ℝ) := by
      push_cast
      calc (N : ℝ) = -(-(N : ℝ) / (j : ℝ)) * (j : ℝ) := by
            rw [neg_div, neg_neg, div_mul_cancel₀ _ hj0.ne']
        _ = -(n : ℝ) * (j : ℝ) := by rw [hEqR]
    have hmulZ : (N : ℤ) = (-n) * (j : ℤ) := by exact_mod_cast hmulR
    have hdvdZ : (j : ℤ) ∣ (N : ℤ) := ⟨-n, by linarith⟩
    have hdvdN : j ∣ N := Int.ofNat_dvd.mp hdvdZ
    exact absurd (Nat.le_of_dvd (by omega) hdvdN) (by omega)
  change (∑ m ∈ Finset.range j, ζ ^ m) * _ = 0
  rw [geom_sum_eq hζ_ne, hζ_pow, sub_self, zero_div, zero_mul]

private theorem fourierPair_ramanujanFloor_diag {r N : ℕ} (hr : 1 < r) (hN : 1 ≤ N) :
    fourierPair (fun u => (pmRamanujanPrimitive r ⌊(N : ℝ) * u⌋₊).re)
      0 r (2 * Real.pi * N / r) =
      fourierPair (fun u => (pmRamanujanPrimitive r ⌊u⌋₊).re) 0 r (2 * Real.pi / r) := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hr0 : (0 : ℝ) < r := by exact_mod_cast (lt_trans zero_lt_one hr)
  set L : ℝ := (r : ℝ) / N
  have hL : 0 ≤ L := div_nonneg hr0.le hN0.le
  have hkL : (N : ℝ) * L = r := mul_div_cancel₀ _ hN0.ne'
  have hper : ∀ m : ℕ, ∀ θ : ℝ, 0 ≤ θ →
      (pmRamanujanPrimitive r ⌊(N : ℝ) * (θ + (m : ℝ) * L)⌋₊).re =
        (pmRamanujanPrimitive r ⌊(N : ℝ) * θ⌋₊).re := by
    intro m θ hθ
    have hmul : (N : ℝ) * (θ + (m : ℝ) * L) = (N : ℝ) * θ + ((m * r : ℕ) : ℝ) := by
      dsimp [L]; push_cast; field_simp
    rw [hmul, Nat.floor_add_natCast (mul_nonneg hN0.le hθ) (m * r),
      pmRamanujanPrimitive_re_add_mul_self hr]
  have hcells := fourierPair_cells (measurable_ramanujanFloor r N)
    (fun u => (Complex.abs_re_le_norm _).trans (norm_pmRamanujanPrimitive_le hr _))
    hL (2 * Real.pi * N / r) N hper
  rw [hkL] at hcells
  rw [hcells]
  have hζ1 : Complex.exp (-Complex.I * (((2 * Real.pi * N / r) * L : ℝ) : ℂ)) = 1 := by
    have hωL : (2 * Real.pi * N / r) * L = 2 * Real.pi := by dsimp [L]; field_simp
    rw [hωL]
    have : -Complex.I * ((2 * Real.pi : ℝ) : ℂ) = ((-1 : ℤ) : ℂ) * (2 * Real.pi * Complex.I) := by
      push_cast; ring
    rw [this, Complex.exp_int_mul_two_pi_mul_I]
  rw [hζ1]
  simp only [one_pow, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
  unfold fourierPair
  have hc : (N : ℝ) * (∫ u in (0 : ℝ)..L,
      (pmRamanujanPrimitive r ⌊(N : ℝ) * u⌋₊).re * Real.cos (2 * Real.pi * N / r * u)) =
      ∫ v in (0 : ℝ)..r, (pmRamanujanPrimitive r ⌊v⌋₊).re * Real.cos (2 * Real.pi / r * v) := by
    have hcomp := intervalIntegral.smul_integral_comp_mul_left
      (f := fun v => (pmRamanujanPrimitive r ⌊v⌋₊).re * Real.cos (2 * Real.pi / r * v))
      (a := 0) (b := L) (N : ℝ)
    rw [smul_eq_mul, mul_zero, hkL] at hcomp
    rw [← hcomp]
    congr 1
    refine intervalIntegral.integral_congr fun u _ => ?_
    congr 2
    ring
  have hs : (N : ℝ) * (∫ u in (0 : ℝ)..L,
      (pmRamanujanPrimitive r ⌊(N : ℝ) * u⌋₊).re * Real.sin (2 * Real.pi * N / r * u)) =
      ∫ v in (0 : ℝ)..r, (pmRamanujanPrimitive r ⌊v⌋₊).re * Real.sin (2 * Real.pi / r * v) := by
    have hcomp := intervalIntegral.smul_integral_comp_mul_left
      (f := fun v => (pmRamanujanPrimitive r ⌊v⌋₊).re * Real.sin (2 * Real.pi / r * v))
      (a := 0) (b := L) (N : ℝ)
    rw [smul_eq_mul, mul_zero, hkL] at hcomp
    rw [← hcomp]
    congr 1
    refine intervalIntegral.integral_congr fun u _ => ?_
    congr 2
    ring
  rw [← hc, ← hs]
  push_cast
  ring

private theorem fourierPair_ramanujanFloor_one_ne_zero {r : ℕ} (hr : 1 < r) :
    fourierPair (fun u => (pmRamanujanPrimitive r ⌊u⌋₊).re) 0 r (2 * Real.pi / r) ≠ 0 := by
  have hr0 : 0 < r := lt_trans zero_lt_one hr
  have hrR : (0 : ℝ) < r := by exact_mod_cast hr0
  set ω : ℝ := 2 * Real.pi / r
  have hω0 : ω ≠ 0 := div_ne_zero (mul_ne_zero two_ne_zero Real.pi_ne_zero) hrR.ne'
  set g : ℝ → ℝ := fun u => (pmRamanujanPrimitive r ⌊u⌋₊).re
  have hg_meas : Measurable g := by simpa [g] using measurable_ramanujanFloor r 1
  have hg_bdd : ∀ u, |g u| ≤ pmRamanujanPrimitiveBound r := fun u =>
    (Complex.abs_re_le_norm _).trans (norm_pmRamanujanPrimitive_le hr _)
  have hbc : ∀ u, |g u * Real.cos (ω * u)| ≤ pmRamanujanPrimitiveBound r := fun u => by
    rw [abs_mul]; exact (mul_le_mul_of_nonneg_left (Real.abs_cos_le_one _) (abs_nonneg _)).trans
      (by linarith [hg_bdd u])
  have hbs : ∀ u, |g u * Real.sin (ω * u)| ≤ pmRamanujanPrimitiveBound r := fun u => by
    rw [abs_mul]; exact (mul_le_mul_of_nonneg_left (Real.abs_sin_le_one _) (abs_nonneg _)).trans
      (by linarith [hg_bdd u])
  have hmc : Measurable (fun u => g u * Real.cos (ω * u)) :=
    hg_meas.mul (Real.continuous_cos.measurable.comp (measurable_const.mul measurable_id))
  have hms : Measurable (fun u => g u * Real.sin (ω * u)) :=
    hg_meas.mul (Real.continuous_sin.measurable.comp (measurable_const.mul measurable_id))
  -- Split `0..r` into `r` unit intervals `0..1`
  have hunit_eq : ∀ (h : ℝ → ℝ) (m : ℕ),
      (∫ θ in (0 : ℝ)..1, g (θ + (m : ℝ)) * h (θ + (m : ℝ))) =
        (pmRamanujanPrimitive r m).re * ∫ θ in (0 : ℝ)..1, h (θ + (m : ℝ)) := by
    intro h m
    rw [intervalIntegral.integral_of_le zero_le_one, intervalIntegral.integral_of_le zero_le_one,
      ← setIntegral_congr_set Ico_ae_eq_Ioc, ← setIntegral_congr_set Ico_ae_eq_Ioc,
      ← integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ico fun θ hθ => ?_
    have hfl : ⌊θ + (m : ℝ)⌋₊ = m := by
      rw [Nat.floor_add_natCast hθ.1 m, Nat.floor_eq_zero.mpr hθ.2, zero_add]
    simp [g, hfl]
  set ω₀ : ℂ := Complex.exp (2 * (Real.pi : ℂ) * Complex.I / (r : ℂ))
  have hfac : fourierPair g 0 r ω =
      fourierPair (fun _ => 1) 0 1 ω *
        ∑ m ∈ Finset.range r, ((pmRamanujanPrimitive r m).re : ℂ) * ω₀⁻¹ ^ m := by
    unfold fourierPair
    rw [show (r : ℝ) = (r : ℝ) * 1 by ring,
      intervalIntegrable_translated_cells hmc hbc zero_le_one r,
      intervalIntegrable_translated_cells hms hbs zero_le_one r]
    simp only [mul_one, one_mul]
    rw [Finset.sum_congr rfl fun m _ => hunit_eq (fun u => Real.cos (ω * u)) m,
      Finset.sum_congr rfl fun m _ => hunit_eq (fun u => Real.sin (ω * u)) m,
      Complex.ofReal_sum, Complex.ofReal_sum, Finset.mul_sum, ← Finset.sum_sub_distrib,
      Finset.mul_sum]
    refine Finset.sum_congr rfl fun m _ => ?_
    set α : ℝ := (m : ℝ) * ω
    have hroot : ω₀⁻¹ ^ m = (Real.cos α : ℂ) - Complex.I * (Real.sin α : ℂ) := by
      dsimp only [ω₀]
      rw [← Complex.exp_neg, ← Complex.exp_nat_mul,
        show (m : ℂ) * -(2 * (Real.pi : ℂ) * Complex.I / (r : ℂ)) =
          ((-α : ℝ) : ℂ) * Complex.I by dsimp [α, ω]; push_cast; simp only [div_eq_mul_inv]; ring,
        Complex.exp_mul_I, Complex.ofReal_neg, Complex.cos_neg, Complex.sin_neg,
        ← Complex.ofReal_cos, ← Complex.ofReal_sin]
      ring
    have hc_m : (∫ θ in (0 : ℝ)..1, Real.cos (ω * (θ + (m : ℝ)))) =
        Real.cos α * (∫ θ in (0 : ℝ)..1, Real.cos (ω * θ)) -
          Real.sin α * (∫ θ in (0 : ℝ)..1, Real.sin (ω * θ)) := by
      have hcongr : EqOn (fun θ => Real.cos (ω * (θ + (m : ℝ))))
          (fun θ => Real.cos α * Real.cos (ω * θ) - Real.sin α * Real.sin (ω * θ)) (uIcc 0 1) := by
        intro θ _
        dsimp only
        rw [show ω * (θ + (m : ℝ)) = ω * θ + α by dsimp [α]; ring, Real.cos_add]
        ring
      have hint_c : IntervalIntegrable (fun x => Real.cos α * Real.cos (ω * x)) volume 0 1 :=
        (((Real.continuous_cos.comp (continuous_const.mul continuous_id)).const_mul _).intervalIntegrable 0 1)
      have hint_s : IntervalIntegrable (fun x => Real.sin α * Real.sin (ω * x)) volume 0 1 :=
        (((Real.continuous_sin.comp (continuous_const.mul continuous_id)).const_mul _).intervalIntegrable 0 1)
      rw [intervalIntegral.integral_congr hcongr, intervalIntegral.integral_sub hint_c hint_s,
        intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
    have hs_m : (∫ θ in (0 : ℝ)..1, Real.sin (ω * (θ + (m : ℝ)))) =
        Real.sin α * (∫ θ in (0 : ℝ)..1, Real.cos (ω * θ)) +
          Real.cos α * (∫ θ in (0 : ℝ)..1, Real.sin (ω * θ)) := by
      have hcongr : EqOn (fun θ => Real.sin (ω * (θ + (m : ℝ))))
          (fun θ => Real.sin α * Real.cos (ω * θ) + Real.cos α * Real.sin (ω * θ)) (uIcc 0 1) := by
        intro θ _
        dsimp only
        rw [show ω * (θ + (m : ℝ)) = ω * θ + α by dsimp [α]; ring, Real.sin_add]
        ring
      have hint_c : IntervalIntegrable (fun x => Real.sin α * Real.cos (ω * x)) volume 0 1 :=
        (((Real.continuous_cos.comp (continuous_const.mul continuous_id)).const_mul _).intervalIntegrable 0 1)
      have hint_s : IntervalIntegrable (fun x => Real.cos α * Real.sin (ω * x)) volume 0 1 :=
        (((Real.continuous_sin.comp (continuous_const.mul continuous_id)).const_mul _).intervalIntegrable 0 1)
      rw [intervalIntegral.integral_congr hcongr, intervalIntegral.integral_add hint_c hint_s,
        intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
    rw [hc_m, hs_m, hroot]
    simp only [Complex.ofReal_sub, Complex.ofReal_add, Complex.ofReal_mul]
    have hI2 : Complex.I ^ 2 = -1 := Complex.I_sq
    linear_combination
      (-((pmRamanujanPrimitive r m).re : ℂ) * (Real.sin α : ℂ) *
        ((∫ θ in (0 : ℝ)..1, Real.sin (ω * θ) : ℝ) : ℂ)) * hI2
  rw [hfac]
  refine mul_ne_zero ?_ ?_
  · -- First factor `∫_0^1 e^{-i ω θ} dθ ≠ 0`
    intro h0
    unfold fourierPair at h0
    simp only [one_mul] at h0
    have hcos_int : (∫ u in (0 : ℝ)..1, Real.cos (ω * u)) = Real.sin ω / ω := by
      have hd : ∀ x ∈ uIcc (0 : ℝ) 1,
          HasDerivAt (fun y => Real.sin (ω * y) / ω) (Real.cos (ω * x)) x := fun x _ => by
        have h1 := ((hasDerivAt_id x).const_mul ω).sin.div_const ω
        refine h1.congr_deriv ?_; dsimp only [id]; field_simp
      rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd
        ((Real.continuous_cos.comp (continuous_const.mul continuous_id)).intervalIntegrable 0 1)]
      simp
    have hsin_int : (∫ u in (0 : ℝ)..1, Real.sin (ω * u)) = (1 - Real.cos ω) / ω := by
      have hd : ∀ x ∈ uIcc (0 : ℝ) 1,
          HasDerivAt (fun y => -Real.cos (ω * y) / ω) (Real.sin (ω * x)) x := fun x _ => by
        have h1 := (((hasDerivAt_id x).const_mul ω).cos.neg).div_const ω
        refine h1.congr_deriv ?_; dsimp only [id]; field_simp
      rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd
        ((Real.continuous_sin.comp (continuous_const.mul continuous_id)).intervalIntegrable 0 1)]
      simp; ring
    have hre0 := congrArg Complex.re h0
    have him0 := congrArg Complex.im h0
    simp only [Complex.sub_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, zero_mul,
      Complex.I_im, one_mul, Complex.ofReal_im, mul_zero, sub_self, sub_zero, Complex.zero_re,
      Complex.sub_im, Complex.mul_im, zero_add, zero_sub, Complex.zero_im, neg_eq_zero] at hre0 him0
    rw [hcos_int, div_eq_zero_iff] at hre0
    rw [hsin_int, div_eq_zero_iff] at him0
    have hsin0 : Real.sin ω = 0 := hre0.resolve_right hω0
    have hcos1 : Real.cos ω = 1 := by linarith [him0.resolve_right hω0]
    have hω₀1 : ω₀ = 1 := by
      dsimp only [ω₀]
      rw [show 2 * (Real.pi : ℂ) * Complex.I / (r : ℂ) = (ω : ℂ) * Complex.I by
        dsimp [ω]; push_cast; simp only [div_eq_mul_inv]; ring,
        Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin, hcos1, hsin0]
      simp
    exact (Complex.isPrimitiveRoot_exp r hr0.ne').ne_one hr hω₀1
  · -- Second factor `∑_{m < r} C_r(m) ω₀^{-m} = r * ω₀ / (ω₀ - 1) ≠ 0`
    have hprim_ω : IsPrimitiveRoot ω₀ r := Complex.isPrimitiveRoot_exp r hr0.ne'
    have hmem_ω : ω₀ ∈ primitiveRoots r ℂ := (mem_primitiveRoots hr0).mpr hprim_ω
    have hre_eq : ∀ m : ℕ, ((pmRamanujanPrimitive r m).re : ℂ) = pmRamanujanPrimitive r m := by
      intro m
      apply Complex.ext <;> simp [RHTower.pmRamanujanPrimitive_im]
    have hsum_eval : ∑ m ∈ Finset.range r,
        ((pmRamanujanPrimitive r m).re : ℂ) * ω₀⁻¹ ^ m =
        (r : ℂ) * (ω₀ / (ω₀ - 1)) := by
      simp_rw [hre_eq, pmRamanujanPrimitive_eq_spectral hr, Finset.sum_mul]
      rw [Finset.sum_comm]
      have hterm : ∀ ζ ∈ primitiveRoots r ℂ,
          ∑ m ∈ Finset.range r, ζ / (ζ - 1) * (ζ ^ m - 1) * ω₀⁻¹ ^ m =
            if ζ = ω₀ then (r : ℂ) * (ω₀ / (ω₀ - 1)) else 0 := by
        intro ζ hζ
        have hζp : IsPrimitiveRoot ζ r := (mem_primitiveRoots hr0).mp hζ
        have hinv_ne : ω₀⁻¹ ≠ 1 := by
          intro h1
          exact hprim_ω.ne_one hr (inv_eq_one.mp h1)
        have hinv_pow : ω₀⁻¹ ^ r = 1 := by
          rw [inv_pow, hprim_ω.pow_eq_one, inv_one]
        have hinv_sum : ∑ m ∈ Finset.range r, ω₀⁻¹ ^ m = 0 := by
          rw [geom_sum_eq hinv_ne, hinv_pow, sub_self, zero_div]
        by_cases heq : ζ = ω₀
        · subst heq
          have h1 : ∀ m ∈ Finset.range r,
              ω₀ / (ω₀ - 1) * (ω₀ ^ m - 1) * ω₀⁻¹ ^ m =
                ω₀ / (ω₀ - 1) * (1 - ω₀⁻¹ ^ m) := fun m _ => by
            have hne0 : ω₀ ≠ 0 := hprim_ω.ne_zero hr0.ne'
            have hpow1 : ω₀ ^ m * ω₀⁻¹ ^ m = 1 := by
              rw [← mul_pow, mul_inv_cancel₀ hne0, one_pow]
            linear_combination ω₀ / (ω₀ - 1) * hpow1
          rw [if_pos rfl, Finset.sum_congr rfl h1, ← Finset.mul_sum, Finset.sum_sub_distrib,
            Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one, hinv_sum, sub_zero]
          ring
        · rw [if_neg heq]
          have hratio_ne : ζ * ω₀⁻¹ ≠ 1 := by
            intro h1
            have hne0 : ω₀ ≠ 0 := hprim_ω.ne_zero hr0.ne'
            have := congrArg (· * ω₀) h1
            rw [mul_assoc, inv_mul_cancel₀ hne0, mul_one, one_mul] at this
            exact heq this
          have hratio_pow : (ζ * ω₀⁻¹) ^ r = 1 := by
            rw [mul_pow, hζp.pow_eq_one, hinv_pow, mul_one]
          have hratio_sum : ∑ m ∈ Finset.range r, (ζ * ω₀⁻¹) ^ m = 0 := by
            rw [geom_sum_eq hratio_ne, hratio_pow, sub_self, zero_div]
          have hsplit : ∀ m ∈ Finset.range r,
              ζ / (ζ - 1) * (ζ ^ m - 1) * ω₀⁻¹ ^ m =
                ζ / (ζ - 1) * ((ζ * ω₀⁻¹) ^ m - ω₀⁻¹ ^ m) := fun m _ => by
            rw [mul_pow]; ring
          rw [Finset.sum_congr rfl hsplit, ← Finset.mul_sum, Finset.sum_sub_distrib,
            hratio_sum, hinv_sum, sub_zero, mul_zero]
      rw [Finset.sum_congr rfl hterm, Finset.sum_ite_eq' (primitiveRoots r ℂ) ω₀]
      simp [hmem_ω]
    rw [hsum_eval]
    exact mul_ne_zero (Nat.cast_ne_zero.mpr hr0.ne')
      (div_ne_zero (hprim_ω.ne_zero hr0.ne') (sub_ne_zero.mpr (hprim_ω.ne_one hr)))

/-- **Harmonic uniqueness for integer-dilate Ramanujan step series.**
If `b : ℕ → ℝ` (`b 0 = 0`, `∑ |b_j| < ∞`) satisfies
`∑_{j ≥ 1} b_j C_r(⌊j u⌋) = 0` for all `u ≥ 0` at some modulus `r > 1`, then `b = 0`. -/
theorem eq_zero_of_tsum_pmRamanujanPrimitive_floor_eq_zero {r : ℕ} (hr : 1 < r)
    {b : ℕ → ℝ} (hb0 : b 0 = 0) (hb : Summable (fun j => |b j|))
    (hzero : ∀ u : ℝ, 0 ≤ u →
      (∑' j : ℕ, b j * (pmRamanujanPrimitive r ⌊(j : ℝ) * u⌋₊).re) = 0) :
    ∀ j : ℕ, b j = 0 := by
  intro j
  induction j using Nat.strong_induction_on with
  | h N ih =>
    rcases eq_or_ne N 0 with rfl | hN0
    · exact hb0
    have hN1 : 1 ≤ N := Nat.one_le_iff_ne_zero.mpr hN0
    have hr0 : (0 : ℝ) ≤ r := Nat.cast_nonneg r
    set ω : ℝ := 2 * Real.pi * N / r
    set H : ℝ → ℝ := fun u => ∑' j : ℕ, b j * (pmRamanujanPrimitive r ⌊(j : ℝ) * u⌋₊).re
    have hH_zero : fourierPair H 0 r ω = 0 := by
      unfold fourierPair
      have hc0 : (∫ u in (0 : ℝ)..r, H u * Real.cos (ω * u)) = 0 := by
        calc (∫ u in (0 : ℝ)..r, H u * Real.cos (ω * u))
            = ∫ _u in (0 : ℝ)..r, (0 : ℝ) := by
              refine intervalIntegral.integral_congr fun u hu => ?_
              dsimp only [H]
              rw [uIcc_of_le hr0] at hu
              rw [hzero u hu.1, zero_mul]
          _ = 0 := by simp
      have hs0 : (∫ u in (0 : ℝ)..r, H u * Real.sin (ω * u)) = 0 := by
        calc (∫ u in (0 : ℝ)..r, H u * Real.sin (ω * u))
            = ∫ _u in (0 : ℝ)..r, (0 : ℝ) := by
              refine intervalIntegral.integral_congr fun u hu => ?_
              dsimp only [H]
              rw [uIcc_of_le hr0] at hu
              rw [hzero u hu.1, zero_mul]
          _ = 0 := by simp
      rw [hc0, hs0]
      simp
    have hB0 : 0 ≤ pmRamanujanPrimitiveBound r :=
      (abs_nonneg _).trans ((Complex.abs_re_le_norm _).trans (norm_pmRamanujanPrimitive_le hr 0))
    have hterm_sum : ∀ u : ℝ,
        Summable (fun j : ℕ => b j * (pmRamanujanPrimitive r ⌊(j : ℝ) * u⌋₊).re) := fun u => by
      refine (hb.mul_right (pmRamanujanPrimitiveBound r)).of_norm_bounded fun j => ?_
      rw [Real.norm_eq_abs, abs_mul]
      exact mul_le_mul_of_nonneg_left
        ((Complex.abs_re_le_norm _).trans (norm_pmRamanujanPrimitive_le hr _)) (abs_nonneg _)
    have hH_meas : Measurable H :=
      Measurable.tsum fun j => measurable_const.mul (measurable_ramanujanFloor r j)
    have hH_bdd : ∀ u : ℝ, |H u| ≤ pmRamanujanPrimitiveBound r * ∑' j : ℕ, |b j| := fun u => by
      dsimp [H]
      rw [← Real.norm_eq_abs, ← tsum_mul_left]
      refine (norm_tsum_le_tsum_norm (hterm_sum u).norm).trans
        (Summable.tsum_le_tsum (fun j => ?_) (hterm_sum u).norm (hb.mul_left _))
      rw [Real.norm_eq_abs, abs_mul, mul_comm]
      exact mul_le_mul_of_nonneg_right
        ((Complex.abs_re_le_norm _).trans (norm_pmRamanujanPrimitive_le hr _)) (abs_nonneg _)
    -- Partial Fourier sums stabilize for `J ≥ N + 1` at `(b N : ℂ) * I_1`
    set I₁ : ℂ := fourierPair (fun u => (pmRamanujanPrimitive r ⌊u⌋₊).re) 0 r (2 * Real.pi / r)
    have hpart_eq : ∀ J : ℕ, N + 1 ≤ J →
        (∑ k ∈ Finset.range J, (b k : ℂ) *
          fourierPair (fun u => (pmRamanujanPrimitive r ⌊(k : ℝ) * u⌋₊).re) 0 r ω) =
        (b N : ℂ) * I₁ := by
      intro J hJ
      have hterm_k : ∀ k ∈ Finset.range J,
          (b k : ℂ) * fourierPair (fun u => (pmRamanujanPrimitive r ⌊(k : ℝ) * u⌋₊).re) 0 r ω =
            if k = N then (b N : ℂ) * I₁ else 0 := by
        intro k _
        rcases lt_trichotomy k N with hlt | rfl | hgt
        · rw [if_neg hlt.ne, ih k hlt, Complex.ofReal_zero, zero_mul]
        · rw [if_pos rfl, fourierPair_ramanujanFloor_diag hr hN1]
        · rw [if_neg hgt.ne', fourierPair_ramanujanFloor_eq_zero_of_lt hr hN1 hgt, mul_zero]
      rw [Finset.sum_congr rfl hterm_k, Finset.sum_ite_eq' (Finset.range J) N]
      simp [Finset.mem_range.mpr (by omega : N < J)]
    -- Difference between `fourierPair H 0 r ω` and partial sum `J` tends to `0`
    have hdiff_bound : ∀ J : ℕ,
        ‖fourierPair H 0 r ω - ∑ k ∈ Finset.range J, (b k : ℂ) *
          fourierPair (fun u => (pmRamanujanPrimitive r ⌊(k : ℝ) * u⌋₊).re) 0 r ω‖ ≤
        2 * (r : ℝ) * pmRamanujanPrimitiveBound r * ∑' m : ℕ, |b (m + J)| := by
      intro J
      set R_J : ℝ → ℝ := fun u =>
        H u - ∑ k ∈ Finset.range J, b k * (pmRamanujanPrimitive r ⌊(k : ℝ) * u⌋₊).re
      have hR_meas : Measurable R_J := hH_meas.sub
        (Finset.measurable_sum _ fun k _ => measurable_const.mul (measurable_ramanujanFloor r k))
      have hR_bdd : ∀ u : ℝ, |R_J u| ≤ pmRamanujanPrimitiveBound r * ∑' m : ℕ, |b (m + J)| := by
        intro u
        have hsplit := (hterm_sum u).sum_add_tsum_nat_add J
        have hR_eq : R_J u =
            ∑' m : ℕ, b (m + J) * (pmRamanujanPrimitive r ⌊((m + J : ℕ) : ℝ) * u⌋₊).re := by
          dsimp [R_J, H]; linarith
        have hdom_J : Summable (fun m : ℕ => pmRamanujanPrimitiveBound r * |b (m + J)|) :=
          (hb.comp_injective (add_left_injective J)).mul_left _
        rw [hR_eq, ← Real.norm_eq_abs, ← tsum_mul_left]
        refine (norm_tsum_le_tsum_norm ((hterm_sum u).comp_injective
          (add_left_injective J)).norm).trans
          (Summable.tsum_le_tsum (fun m => ?_)
            ((hterm_sum u).comp_injective (add_left_injective J)).norm hdom_J)
        dsimp only [Function.comp_apply]
        rw [Real.norm_eq_abs, abs_mul, mul_comm]
        exact mul_le_mul_of_nonneg_right
          ((Complex.abs_re_le_norm _).trans (norm_pmRamanujanPrimitive_le hr _)) (abs_nonneg _)
      set B_J : ℝ := pmRamanujanPrimitiveBound r * ∑' m : ℕ, |b (m + J)|
      have hBJ0 : 0 ≤ B_J := mul_nonneg hB0 (tsum_nonneg fun _ => abs_nonneg _)
      have hlin_c : (∫ u in (0 : ℝ)..r, H u * Real.cos (ω * u)) -
          ∑ k ∈ Finset.range J, b k *
            (∫ u in (0 : ℝ)..r,
              (pmRamanujanPrimitive r ⌊(k : ℝ) * u⌋₊).re * Real.cos (ω * u)) =
          ∫ u in (0 : ℝ)..r, R_J u * Real.cos (ω * u) := by
        have hsum_int : ∑ k ∈ Finset.range J, b k *
            (∫ u in (0 : ℝ)..r,
              (pmRamanujanPrimitive r ⌊(k : ℝ) * u⌋₊).re * Real.cos (ω * u)) =
            ∫ u in (0 : ℝ)..r,
              (∑ k ∈ Finset.range J, b k * (pmRamanujanPrimitive r ⌊(k : ℝ) * u⌋₊).re) *
                Real.cos (ω * u) := by
          simp_rw [Finset.sum_mul, mul_assoc]
          rw [intervalIntegral.integral_finsetSum]
          · exact Finset.sum_congr rfl fun k _ => (intervalIntegral.integral_const_mul _ _).symm
          · intro k _
            exact (intervalIntegrable_of_bounded_measurable
              (g := fun u => (pmRamanujanPrimitive r ⌊(k : ℝ) * u⌋₊).re * Real.cos (ω * u))
              ((measurable_ramanujanFloor r k).mul
                (Real.continuous_cos.measurable.comp (measurable_const.mul measurable_id)))
              (M := pmRamanujanPrimitiveBound r)
              (fun u => by
                rw [abs_mul]
                exact (mul_le_mul_of_nonneg_left (Real.abs_cos_le_one _) (abs_nonneg _)).trans
                  (by linarith [(Complex.abs_re_le_norm _).trans (norm_pmRamanujanPrimitive_le hr ⌊(k : ℝ) * u⌋₊)]))
              hr0).const_mul _
        rw [hsum_int, ← intervalIntegral.integral_sub]
        · exact intervalIntegral.integral_congr fun u _ => by dsimp [R_J]; ring
        · exact intervalIntegrable_of_bounded_measurable
            (g := fun u => H u * Real.cos (ω * u))
            (hH_meas.mul (Real.continuous_cos.measurable.comp (measurable_const.mul measurable_id)))
            (M := pmRamanujanPrimitiveBound r * ∑' j : ℕ, |b j|)
            (fun u => by
              rw [abs_mul]
              exact (mul_le_mul_of_nonneg_left (Real.abs_cos_le_one _) (abs_nonneg _)).trans
                (by linarith [hH_bdd u])) hr0
        · refine intervalIntegrable_of_bounded_measurable
            (g := fun u =>
              (∑ k ∈ Finset.range J, b k * (pmRamanujanPrimitive r ⌊(k : ℝ) * u⌋₊).re) *
                Real.cos (ω * u))
            ((Finset.measurable_sum _ fun k _ =>
              measurable_const.mul (measurable_ramanujanFloor r k)).mul
                (Real.continuous_cos.measurable.comp (measurable_const.mul measurable_id)))
            (M := ∑ k ∈ Finset.range J, |b k| * pmRamanujanPrimitiveBound r) (fun u => ?_) hr0
          rw [abs_mul]
          refine (mul_le_mul_of_nonneg_left (Real.abs_cos_le_one _) (abs_nonneg _)).trans ?_
          rw [mul_one]
          exact (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun k _ => by
            rw [abs_mul]
            exact mul_le_mul_of_nonneg_left
              ((Complex.abs_re_le_norm _).trans (norm_pmRamanujanPrimitive_le hr _))
              (abs_nonneg _))
      have hlin_s : (∫ u in (0 : ℝ)..r, H u * Real.sin (ω * u)) -
          ∑ k ∈ Finset.range J, b k *
            (∫ u in (0 : ℝ)..r,
              (pmRamanujanPrimitive r ⌊(k : ℝ) * u⌋₊).re * Real.sin (ω * u)) =
          ∫ u in (0 : ℝ)..r, R_J u * Real.sin (ω * u) := by
        have hsum_int : ∑ k ∈ Finset.range J, b k *
            (∫ u in (0 : ℝ)..r,
              (pmRamanujanPrimitive r ⌊(k : ℝ) * u⌋₊).re * Real.sin (ω * u)) =
            ∫ u in (0 : ℝ)..r,
              (∑ k ∈ Finset.range J, b k * (pmRamanujanPrimitive r ⌊(k : ℝ) * u⌋₊).re) *
                Real.sin (ω * u) := by
          simp_rw [Finset.sum_mul, mul_assoc]
          rw [intervalIntegral.integral_finsetSum]
          · exact Finset.sum_congr rfl fun k _ => (intervalIntegral.integral_const_mul _ _).symm
          · intro k _
            exact (intervalIntegrable_of_bounded_measurable
              (g := fun u => (pmRamanujanPrimitive r ⌊(k : ℝ) * u⌋₊).re * Real.sin (ω * u))
              ((measurable_ramanujanFloor r k).mul
                (Real.continuous_sin.measurable.comp (measurable_const.mul measurable_id)))
              (M := pmRamanujanPrimitiveBound r)
              (fun u => by
                rw [abs_mul]
                exact (mul_le_mul_of_nonneg_left (Real.abs_sin_le_one _) (abs_nonneg _)).trans
                  (by linarith [(Complex.abs_re_le_norm _).trans (norm_pmRamanujanPrimitive_le hr ⌊(k : ℝ) * u⌋₊)]))
              hr0).const_mul _
        rw [hsum_int, ← intervalIntegral.integral_sub]
        · exact intervalIntegral.integral_congr fun u _ => by dsimp [R_J]; ring
        · exact intervalIntegrable_of_bounded_measurable
            (g := fun u => H u * Real.sin (ω * u))
            (hH_meas.mul (Real.continuous_sin.measurable.comp (measurable_const.mul measurable_id)))
            (M := pmRamanujanPrimitiveBound r * ∑' j : ℕ, |b j|)
            (fun u => by
              rw [abs_mul]
              exact (mul_le_mul_of_nonneg_left (Real.abs_sin_le_one _) (abs_nonneg _)).trans
                (by linarith [hH_bdd u])) hr0
        · refine intervalIntegrable_of_bounded_measurable
            (g := fun u =>
              (∑ k ∈ Finset.range J, b k * (pmRamanujanPrimitive r ⌊(k : ℝ) * u⌋₊).re) *
                Real.sin (ω * u))
            ((Finset.measurable_sum _ fun k _ =>
              measurable_const.mul (measurable_ramanujanFloor r k)).mul
                (Real.continuous_sin.measurable.comp (measurable_const.mul measurable_id)))
            (M := ∑ k ∈ Finset.range J, |b k| * pmRamanujanPrimitiveBound r) (fun u => ?_) hr0
          rw [abs_mul]
          refine (mul_le_mul_of_nonneg_left (Real.abs_sin_le_one _) (abs_nonneg _)).trans ?_
          rw [mul_one]
          exact (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun k _ => by
            rw [abs_mul]
            exact mul_le_mul_of_nonneg_left
              ((Complex.abs_re_le_norm _).trans (norm_pmRamanujanPrimitive_le hr _))
              (abs_nonneg _))
      have hrew : fourierPair H 0 r ω - ∑ k ∈ Finset.range J, (b k : ℂ) *
          fourierPair (fun u => (pmRamanujanPrimitive r ⌊(k : ℝ) * u⌋₊).re) 0 r ω =
          fourierPair R_J 0 r ω := by
        unfold fourierPair
        rw [← hlin_c, ← hlin_s]
        push_cast
        simp only [mul_sub, Finset.mul_sum, Finset.sum_sub_distrib]
        ring
      have hbound_int : ∀ h : ℝ → ℝ, (∀ u, |h u| ≤ 1) →
          |∫ u in (0 : ℝ)..r, R_J u * h u| ≤ (r : ℝ) * B_J := by
        intro h hh
        rw [intervalIntegral.integral_of_le hr0, ← Real.norm_eq_abs]
        calc ‖∫ u in Set.Ioc (0 : ℝ) r, R_J u * h u‖
            ≤ ∫ u in Set.Ioc (0 : ℝ) r, B_J := by
              refine norm_integral_le_of_norm_le
                (integrableOn_const (hs := measure_Ioc_lt_top.ne)) ?_
              filter_upwards [ae_restrict_mem measurableSet_Ioc] with u _
              rw [Real.norm_eq_abs, abs_mul]
              exact (mul_le_mul_of_nonneg_left (hh u) (abs_nonneg _)).trans
                (by linarith [hR_bdd u])
          _ = (r : ℝ) * B_J := by
              rw [setIntegral_const, Real.volume_real_Ioc_of_le hr0, sub_zero, smul_eq_mul]
      rw [hrew]
      unfold fourierPair
      calc ‖((∫ u in (0 : ℝ)..r, R_J u * Real.cos (ω * u) : ℝ) : ℂ) -
              Complex.I * ((∫ u in (0 : ℝ)..r, R_J u * Real.sin (ω * u) : ℝ) : ℂ)‖
          ≤ ‖((∫ u in (0 : ℝ)..r, R_J u * Real.cos (ω * u) : ℝ) : ℂ)‖ +
              ‖Complex.I * ((∫ u in (0 : ℝ)..r, R_J u * Real.sin (ω * u) : ℝ) : ℂ)‖ :=
            norm_sub_le _ _
        _ = |∫ u in (0 : ℝ)..r, R_J u * Real.cos (ω * u)| +
              |∫ u in (0 : ℝ)..r, R_J u * Real.sin (ω * u)| := by
            rw [Complex.norm_real, Real.norm_eq_abs, norm_mul, Complex.norm_I, one_mul,
              Complex.norm_real, Real.norm_eq_abs]
        _ ≤ (r : ℝ) * B_J + (r : ℝ) * B_J :=
            add_le_add
              (hbound_int (fun u => Real.cos (ω * u)) (fun u => Real.abs_cos_le_one (ω * u)))
              (hbound_int (fun u => Real.sin (ω * u)) (fun u => Real.abs_sin_le_one (ω * u)))
        _ = 2 * (r : ℝ) * pmRamanujanPrimitiveBound r * ∑' m : ℕ, |b (m + J)| := by
            dsimp [B_J]; ring
    -- Pass to `J → ∞`: tail tends to `0`, forcing `‖(b N : ℂ) * I₁‖ = 0`
    have htail_tendsto : Tendsto (fun J : ℕ => ∑' m : ℕ, |b (m + J)|) atTop (𝓝 0) := by
      have h1 := hb.hasSum.tendsto_sum_nat
      have h2 : (fun J : ℕ => ∑' m : ℕ, |b (m + J)|) =
          fun J : ℕ => (∑' j : ℕ, |b j|) - ∑ k ∈ Finset.range J, |b k| := by
        ext J; linarith [hb.sum_add_tsum_nat_add J]
      rw [h2, show (0 : ℝ) = (∑' j : ℕ, |b j|) - (∑' j : ℕ, |b j|) by ring]
      exact tendsto_const_nhds.sub h1
    have hconst_le : ∀ᶠ J : ℕ in atTop,
        ‖(b N : ℂ) * I₁‖ ≤
          2 * (r : ℝ) * pmRamanujanPrimitiveBound r * ∑' m : ℕ, |b (m + J)| := by
      filter_upwards [eventually_ge_atTop (N + 1)] with J hJ
      have hd := hdiff_bound J
      rw [hH_zero, hpart_eq J hJ, zero_sub, norm_neg] at hd
      exact hd
    have hlim0 : Tendsto (fun J : ℕ =>
        2 * (r : ℝ) * pmRamanujanPrimitiveBound r * ∑' m : ℕ, |b (m + J)|) atTop (𝓝 0) := by
      simpa using htail_tendsto.const_mul (2 * (r : ℝ) * pmRamanujanPrimitiveBound r)
    have hle0 : ‖(b N : ℂ) * I₁‖ ≤ 0 := ge_of_tendsto hlim0 hconst_le
    have hmul0 : (b N : ℂ) * I₁ = 0 := norm_le_zero_iff.mp hle0
    exact Complex.ofReal_eq_zero.mp
      ((mul_eq_zero.mp hmul0).resolve_right (fourierPair_ramanujanFloor_one_ne_zero hr))

/-- **Uniqueness of Möbius weights from the integer-dilate sieve functional equation.**
For every modulus `r > 1`, damping `ε > 0`, and bounded real sequence `w : ℕ → ℝ` with `w 0 = 0`,
`w` satisfies the additive sieve functional equation
`∑_{m ≥ 1} m^{−1−ε} F_w(m x) = C_r(⌊x⌋)` for all `x ≥ 0` if and only if `w = moebiusReal`. -/
theorem eq_moebiusReal_of_sieve_functional_equation {r : ℕ} (hr : 1 < r) {ε : ℝ} (hε : 0 < ε)
    {w : ℕ → ℝ} (hw0 : w 0 = 0) (hw_bdd : ∃ W : ℝ, ∀ d, |w d| ≤ W) :
    (∀ x : ℝ, 0 ≤ x →
      (∑' m : ℕ,
        if m = 0 then 0
        else (m : ℝ) ^ (-1 - ε) * weightedForwardDilatedLimit w r ε ((m : ℝ) * x)) =
        (pmRamanujanPrimitive r ⌊x⌋₊).re) ↔
      w = moebiusReal := by
  constructor
  · intro hsieve
    obtain ⟨W, hw⟩ := hw_bdd
    set c : ℕ → ℝ := fun j =>
      if j = 0 then 0 else ((∑ d ∈ j.divisors, w d) - if j = 1 then 1 else 0) * (j : ℝ) ^ (-1 - ε)
    have hc0 : c 0 = 0 := by simp [c]
    have hc_sum : Summable (fun j => |c j|) := by
      have hs1 := summable_divisorSum_rpow hw hε
      have hs2 : Summable (fun j : ℕ => |(if j = 1 then (1 : ℝ) else 0) * (j : ℝ) ^ (-1 - ε)|) :=
        summable_of_ne_finset_zero (s := {1}) fun j hj => by
          simp at hj; simp [hj]
      refine (hs1.add hs2).of_nonneg_of_le (fun _ => abs_nonneg _) fun j => ?_
      dsimp only [c]
      rcases eq_or_ne j 0 with rfl | hj0
      · rw [if_pos rfl, abs_zero]
        exact add_nonneg (abs_nonneg _) (abs_nonneg _)
      · rw [if_neg hj0, sub_mul]
        simpa only [Real.norm_eq_abs] using norm_sub_le
          ((∑ d ∈ j.divisors, w d) * (j : ℝ) ^ (-1 - ε))
          ((if j = 1 then (1 : ℝ) else 0) * (j : ℝ) ^ (-1 - ε))
    have hc_zero : ∀ u : ℝ, 0 ≤ u →
        (∑' j : ℕ, c j * (pmRamanujanPrimitive r ⌊(j : ℝ) * u⌋₊).re) = 0 := by
      intro u hu
      have h1 := (hasSum_weightedForwardDilatedLimit_mul hw0 hw hr hε u).tsum_eq
      rw [hsieve u hu] at h1
      have hB0 : 0 ≤ pmRamanujanPrimitiveBound r :=
        (abs_nonneg _).trans ((Complex.abs_re_le_norm _).trans (norm_pmRamanujanPrimitive_le hr 0))
      have hsum_w : Summable (fun j : ℕ =>
          (∑ d ∈ j.divisors, w d) * (j : ℝ) ^ (-1 - ε) *
            (pmRamanujanPrimitive r ⌊(j : ℝ) * u⌋₊).re) := by
        refine ((summable_divisorSum_rpow hw hε).mul_right
          (pmRamanujanPrimitiveBound r)).of_norm_bounded fun j => ?_
        rw [Real.norm_eq_abs, abs_mul]
        exact mul_le_mul_of_nonneg_left
          ((Complex.abs_re_le_norm _).trans (norm_pmRamanujanPrimitive_le hr _)) (abs_nonneg _)
      have hsum_one : HasSum (fun j : ℕ =>
          (if j = 1 then (1 : ℝ) else 0) * (j : ℝ) ^ (-1 - ε) *
            (pmRamanujanPrimitive r ⌊(j : ℝ) * u⌋₊).re)
          ((pmRamanujanPrimitive r ⌊u⌋₊).re) := by
        refine (hasSum_ite_eq (1 : ℕ) ((pmRamanujanPrimitive r ⌊u⌋₊).re)).congr_fun fun j => ?_
        split_ifs with hj1
        · subst hj1; simp
        · simp
      have hsub := hsum_w.hasSum.sub hsum_one
      rw [← h1, sub_self] at hsub
      refine (hsub.congr_fun fun j => ?_).tsum_eq
      dsimp only [c]
      rcases eq_or_ne j 0 with rfl | hj0
      · simp
      · rw [if_neg hj0]; ring
    have hc_all := eq_zero_of_tsum_pmRamanujanPrimitive_floor_eq_zero hr hc0 hc_sum hc_zero
    have hdiv_eq : ∀ j : ℕ, j ≠ 0 → ∑ d ∈ j.divisors, w d = if j = 1 then 1 else 0 := by
      intro j hj0
      have hcj := hc_all j
      dsimp only [c] at hcj
      rw [if_neg hj0, mul_eq_zero] at hcj
      have hjpos : (0 : ℝ) < j := by exact_mod_cast (Nat.pos_of_ne_zero hj0)
      have hrp_ne : (j : ℝ) ^ (-1 - ε) ≠ 0 := (Real.rpow_pos_of_pos hjpos _).ne'
      linarith [hcj.resolve_right hrp_ne]
    -- Invert Dirichlet convolution `W * ζ = 1` via `ζ * μ = 1`
    set W_af : ArithmeticFunction ℝ := ⟨w, hw0⟩
    have hW_zeta : W_af * (ArithmeticFunction.zeta : ArithmeticFunction ℝ) = 1 := by
      ext j
      rcases eq_or_ne j 0 with rfl | hj0
      · simp
      · rw [ArithmeticFunction.coe_mul_zeta_apply, ArithmeticFunction.one_apply]
        exact hdiv_eq j hj0
    have hW_eq_mu : W_af = (ArithmeticFunction.moebius : ArithmeticFunction ℝ) := by
      calc W_af = W_af * 1 := (mul_one W_af).symm
        _ = W_af * ((ArithmeticFunction.zeta : ArithmeticFunction ℝ) *
              (ArithmeticFunction.moebius : ArithmeticFunction ℝ)) := by
            rw [mul_comm (ArithmeticFunction.zeta : ArithmeticFunction ℝ),
              ArithmeticFunction.coe_moebius_mul_coe_zeta]
        _ = (W_af * (ArithmeticFunction.zeta : ArithmeticFunction ℝ)) *
              (ArithmeticFunction.moebius : ArithmeticFunction ℝ) := (mul_assoc _ _ _).symm
        _ = (ArithmeticFunction.moebius : ArithmeticFunction ℝ) := by rw [hW_zeta, one_mul]
    ext d
    have hd := congrArg (fun F : ArithmeticFunction ℝ => F d) hW_eq_mu
    simpa [W_af, moebiusReal] using hd
  · rintro rfl x _
    have hEq : weightedForwardDilatedLimit moebiusReal r ε = forwardDilatedLimit r ε := rfl
    rw [hEq]
    exact (hasSum_forwardDilatedLimit_mul hr hε x).tsum_eq

/-! ## §4. Explicit `ε = 0` folded trigonometric profile and all-harmonic sieve identity -/

/-- The explicit two-harmonic zero-damping profile at `r = 2`:
`G_0(x) = (2/π) sin(π x) − (1/π) sin(2π x)`. -/
noncomputable def foldedZeroDampingProfile (x : ℝ) : ℝ :=
  (2 / Real.pi) * Real.sin (Real.pi * x) - (1 / Real.pi) * Real.sin (2 * Real.pi * x)

/-- Factored cubic-sine form `G_0(x) = (4/π) sin(π x) sin²(π x / 2)`. -/
theorem foldedZeroDampingProfile_eq_sin_cube (x : ℝ) :
    foldedZeroDampingProfile x =
      (4 / Real.pi) * Real.sin (Real.pi * x) * Real.sin (Real.pi * x / 2) ^ 2 := by
  unfold foldedZeroDampingProfile
  have h2 : Real.sin (2 * Real.pi * x) = 2 * Real.sin (Real.pi * x) * Real.cos (Real.pi * x) := by
    rw [show 2 * Real.pi * x = 2 * (Real.pi * x) by ring, Real.sin_two_mul]
  have hhalf : 2 * Real.sin (Real.pi * x / 2) ^ 2 = 1 - Real.cos (Real.pi * x) := by
    have hc := Real.cos_two_mul (Real.pi * x / 2)
    have hs := Real.sin_sq_add_cos_sq (Real.pi * x / 2)
    rw [show 2 * (Real.pi * x / 2) = Real.pi * x by ring] at hc
    linarith
  rw [h2]
  linear_combination -(2 / Real.pi) * Real.sin (Real.pi * x) * hhalf

/-- `2`-periodicity of `foldedZeroDampingProfile`. -/
theorem foldedZeroDampingProfile_add_two (x : ℝ) :
    foldedZeroDampingProfile (x + 2) = foldedZeroDampingProfile x := by
  unfold foldedZeroDampingProfile
  rw [show Real.pi * (x + 2) = Real.pi * x + 2 * Real.pi by ring,
    show 2 * Real.pi * (x + 2) = 2 * Real.pi * x + (2 : ℕ) * (2 * Real.pi) by push_cast; ring,
    Real.sin_add_two_pi, Real.sin_add_nat_mul_two_pi]

/-- Oddness of `foldedZeroDampingProfile`. -/
theorem foldedZeroDampingProfile_neg (x : ℝ) :
    foldedZeroDampingProfile (-x) = -foldedZeroDampingProfile x := by
  unfold foldedZeroDampingProfile
  rw [mul_neg, mul_neg, Real.sin_neg, Real.sin_neg]
  ring

/-- Strict positivity on `(0, 1)`: `G_0(x) > 0` for all `x ∈ (0, 1)`. -/
theorem foldedZeroDampingProfile_pos_on_Ioo_zero_one {x : ℝ} (hx : x ∈ Set.Ioo (0 : ℝ) 1) :
    0 < foldedZeroDampingProfile x := by
  rw [foldedZeroDampingProfile_eq_sin_cube]
  have hpi : 0 < Real.pi := Real.pi_pos
  have hs1 : 0 < Real.sin (Real.pi * x) :=
    Real.sin_pos_of_pos_of_lt_pi (by nlinarith [hx.1]) (by nlinarith [hx.2])
  have hs2 : 0 < Real.sin (Real.pi * x / 2) :=
    Real.sin_pos_of_pos_of_lt_pi (by nlinarith [hx.1]) (by nlinarith [hx.2])
  positivity

/-- Strict negativity on `(1, 2)`: `G_0(x) < 0` for all `x ∈ (1, 2)`. -/
theorem foldedZeroDampingProfile_neg_on_Ioo_one_two {x : ℝ} (hx : x ∈ Set.Ioo (1 : ℝ) 2) :
    foldedZeroDampingProfile x < 0 := by
  have hsub : 2 - x ∈ Set.Ioo (0 : ℝ) 1 := ⟨by linarith [hx.2], by linarith [hx.1]⟩
  have hpos := foldedZeroDampingProfile_pos_on_Ioo_zero_one hsub
  have hid : foldedZeroDampingProfile (2 - x) = -foldedZeroDampingProfile x := by
    rw [show (2 - x : ℝ) = -x + 2 by ring, foldedZeroDampingProfile_add_two,
      foldedZeroDampingProfile_neg]
  linarith

private theorem integral_zero_two_sin_mul_sin {a b : ℕ} (ha : 1 ≤ a) (hb : 1 ≤ b) :
    (∫ u in (0 : ℝ)..2,
      Real.sin (Real.pi * (a : ℝ) * u) * Real.sin (Real.pi * (b : ℝ) * u)) =
      if a = b then 1 else 0 := by
  have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  by_cases hab : a = b
  · subst hab
    rw [if_pos rfl]
    set ω : ℝ := Real.pi * (a : ℝ)
    have hω : ω ≠ 0 := mul_ne_zero hpi (Nat.cast_ne_zero.mpr (by omega))
    have hd : ∀ x ∈ uIcc (0 : ℝ) 2,
        HasDerivAt (fun y => y / 2 - Real.sin (2 * ω * y) / (4 * ω))
          (Real.sin (ω * x) * Real.sin (ω * x)) x := fun x _ => by
      have h1 := (hasDerivAt_id x).div_const (2 : ℝ)
      have h2 := (((hasDerivAt_id x).const_mul (2 * ω)).sin).div_const (4 * ω)
      refine (h1.sub h2).congr_deriv ?_
      dsimp only [id]
      have hc := Real.cos_two_mul (ω * x)
      have hs := Real.sin_sq_add_cos_sq (ω * x)
      rw [show 2 * ω * x = 2 * (ω * x) by ring, Real.cos_two_mul]
      field_simp
      nlinarith
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd
      (((Real.continuous_sin.comp (continuous_const.mul continuous_id)).mul
        (Real.continuous_sin.comp (continuous_const.mul continuous_id))).intervalIntegrable 0 2)]
    have hs4 : Real.sin (2 * ω * 2) = 0 := by
      rw [show 2 * ω * 2 = ((2 * a : ℕ) : ℝ) * (2 * Real.pi) by dsimp [ω]; push_cast; ring]
      simpa using Real.sin_add_nat_mul_two_pi 0 (2 * a)
    simp [hs4]
  · rw [if_neg hab]
    set c₁ : ℝ := Real.pi * ((a : ℝ) - (b : ℝ))
    set c₂ : ℝ := Real.pi * ((a : ℝ) + (b : ℝ))
    have hc₁ : c₁ ≠ 0 := mul_ne_zero hpi (sub_ne_zero.mpr (by exact_mod_cast hab))
    have hc₂ : c₂ ≠ 0 := mul_ne_zero hpi (by positivity)
    have hd : ∀ x ∈ uIcc (0 : ℝ) 2,
        HasDerivAt (fun y => Real.sin (c₁ * y) / (2 * c₁) - Real.sin (c₂ * y) / (2 * c₂))
          (Real.sin (Real.pi * (a : ℝ) * x) * Real.sin (Real.pi * (b : ℝ) * x)) x := fun x _ => by
      have h1 := (((hasDerivAt_id x).const_mul c₁).sin).div_const (2 * c₁)
      have h2 := (((hasDerivAt_id x).const_mul c₂).sin).div_const (2 * c₂)
      refine (h1.sub h2).congr_deriv ?_
      dsimp only [id]
      have htrig : Real.cos (c₁ * x) - Real.cos (c₂ * x) =
          2 * (Real.sin (Real.pi * (a : ℝ) * x) * Real.sin (Real.pi * (b : ℝ) * x)) := by
        rw [show c₁ * x = Real.pi * (a : ℝ) * x - Real.pi * (b : ℝ) * x by dsimp [c₁]; ring,
          show c₂ * x = Real.pi * (a : ℝ) * x + Real.pi * (b : ℝ) * x by dsimp [c₂]; ring,
          Real.cos_sub, Real.cos_add]
        ring
      have hdiv : Real.cos (c₁ * x) * (c₁ * 1) / (2 * c₁) -
          Real.cos (c₂ * x) * (c₂ * 1) / (2 * c₂) =
          (Real.cos (c₁ * x) - Real.cos (c₂ * x)) / 2 := by
        field_simp
      rw [hdiv, htrig]
      ring
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd
      (((Real.continuous_sin.comp (continuous_const.mul continuous_id)).mul
        (Real.continuous_sin.comp (continuous_const.mul continuous_id))).intervalIntegrable 0 2)]
    have hs₁ : Real.sin (c₁ * 2) = 0 := by
      rw [show c₁ * 2 = (((a : ℤ) - (b : ℤ)) : ℝ) * (2 * Real.pi) by dsimp [c₁]; push_cast; ring]
      simpa using Real.sin_add_int_mul_two_pi 0 ((a : ℤ) - (b : ℤ))
    have hs₂ : Real.sin (c₂ * 2) = 0 := by
      rw [show c₂ * 2 = ((a + b : ℕ) : ℝ) * (2 * Real.pi) by dsimp [c₂]; push_cast; ring]
      simpa using Real.sin_add_nat_mul_two_pi 0 (a + b)
    simp [hs₁, hs₂]

/-- Exact sine Fourier coefficients of `foldedZeroDampingProfile` on `[0, 2]`:
`2/π` at `n = 1`, `−1/π` at `n = 2`, and `0` for every `n ≥ 3`. -/
theorem integral_foldedZeroDampingProfile_mul_sin {n : ℕ} (hn : 1 ≤ n) :
    (∫ u in (0 : ℝ)..2, foldedZeroDampingProfile u * Real.sin (Real.pi * (n : ℝ) * u)) =
      if n = 1 then 2 / Real.pi else if n = 2 then -(1 / Real.pi) else 0 := by
  have hrew : EqOn (fun u => foldedZeroDampingProfile u * Real.sin (Real.pi * (n : ℝ) * u))
      (fun u => (2 / Real.pi) * (Real.sin (Real.pi * (1 : ℕ) * u) * Real.sin (Real.pi * (n : ℝ) * u)) -
        (1 / Real.pi) * (Real.sin (Real.pi * (2 : ℕ) * u) * Real.sin (Real.pi * (n : ℝ) * u)))
      (uIcc 0 2) := by
    intro u _
    dsimp only
    unfold foldedZeroDampingProfile
    push_cast; ring
  have hint₁ : IntervalIntegrable
      (fun u => (2 / Real.pi) * (Real.sin (Real.pi * (1 : ℕ) * u) * Real.sin (Real.pi * (n : ℝ) * u)))
      volume 0 2 :=
    ((((Real.continuous_sin.comp (continuous_const.mul continuous_id)).mul
      (Real.continuous_sin.comp (continuous_const.mul continuous_id))).const_mul _).intervalIntegrable 0 2)
  have hint₂ : IntervalIntegrable
      (fun u => (1 / Real.pi) * (Real.sin (Real.pi * (2 : ℕ) * u) * Real.sin (Real.pi * (n : ℝ) * u)))
      volume 0 2 :=
    ((((Real.continuous_sin.comp (continuous_const.mul continuous_id)).mul
      (Real.continuous_sin.comp (continuous_const.mul continuous_id))).const_mul _).intervalIntegrable 0 2)
  rw [intervalIntegral.integral_congr hrew, intervalIntegral.integral_sub hint₁ hint₂,
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
    integral_zero_two_sin_mul_sin le_rfl hn, integral_zero_two_sin_mul_sin (by omega) hn]
  rcases eq_or_ne n 1 with rfl | hn1
  · simp
  · rcases eq_or_ne n 2 with rfl | hn2
    · simp
    · simp [hn1, hn2, Ne.symm hn1, Ne.symm hn2]

/-- Exact sine Fourier coefficients of `(pmRamanujanPrimitive 2 ⌊u⌋₊).re` on `[0, 2]`:
`2 / (π n)` when `n` is odd and `0` when `n` is even. -/
theorem integral_pmRamanujanPrimitive_two_mul_sin {n : ℕ} (hn : 1 ≤ n) :
    (∫ u in (0 : ℝ)..2, (pmRamanujanPrimitive 2 ⌊u⌋₊).re * Real.sin (Real.pi * (n : ℝ) * u)) =
      if n % 2 = 1 then 2 / (Real.pi * (n : ℝ)) else 0 := by
  have hg1 : Measurable (fun u : ℝ => (pmRamanujanPrimitive 2 ⌊u⌋₊).re) := by
    simpa using measurable_ramanujanFloor 2 1
  have hg_meas : Measurable (fun u : ℝ =>
      (pmRamanujanPrimitive 2 ⌊u⌋₊).re * Real.sin (Real.pi * (n : ℝ) * u)) :=
    hg1.mul (Real.continuous_sin.measurable.comp (measurable_const.mul measurable_id))
  have hg_bdd : ∀ u : ℝ,
      |(pmRamanujanPrimitive 2 ⌊u⌋₊).re * Real.sin (Real.pi * (n : ℝ) * u)| ≤ 1 := fun u => by
    rw [pmRamanujanPrimitive_two_re, abs_mul, abs_neg]
    have hm : ((⌊u⌋₊ % 2 : ℕ) : ℝ) ≤ 1 := by exact_mod_cast Nat.le_of_lt_succ (Nat.mod_lt _ two_pos)
    rw [abs_of_nonneg (Nat.cast_nonneg _)]
    exact (mul_le_mul hm (Real.abs_sin_le_one _) (abs_nonneg _) zero_le_one).trans (by norm_num)
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (intervalIntegrable_of_bounded_measurable hg_meas hg_bdd zero_le_one)
    (intervalIntegrable_of_bounded_measurable hg_meas hg_bdd one_le_two)]
  have h01 : (∫ u in (0 : ℝ)..1,
      (pmRamanujanPrimitive 2 ⌊u⌋₊).re * Real.sin (Real.pi * (n : ℝ) * u)) = 0 := by
    rw [intervalIntegral.integral_of_le zero_le_one, ← setIntegral_congr_set Ico_ae_eq_Ioc]
    have h0 : EqOn (fun u : ℝ =>
        (pmRamanujanPrimitive 2 ⌊u⌋₊).re * Real.sin (Real.pi * (n : ℝ) * u))
        (fun _ => 0) (Set.Ico 0 1) := fun u hu => by
      dsimp only
      rw [Nat.floor_eq_zero.mpr hu.2, pmRamanujanPrimitive_two_re]; simp
    rw [setIntegral_congr_fun measurableSet_Ico h0]
    simp
  have h12 : (∫ u in (1 : ℝ)..2,
      (pmRamanujanPrimitive 2 ⌊u⌋₊).re * Real.sin (Real.pi * (n : ℝ) * u)) =
      -(∫ u in (1 : ℝ)..2, Real.sin (Real.pi * (n : ℝ) * u)) := by
    rw [intervalIntegral.integral_of_le one_le_two, intervalIntegral.integral_of_le one_le_two,
      ← setIntegral_congr_set Ico_ae_eq_Ioc, ← setIntegral_congr_set Ico_ae_eq_Ioc,
      ← integral_neg]
    refine setIntegral_congr_fun measurableSet_Ico fun u hu => ?_
    have hfl : ⌊u⌋₊ = 1 := (Nat.floor_eq_iff (by linarith [hu.1])).mpr
      ⟨by norm_cast; exact hu.1, by norm_cast; exact hu.2⟩
    change (pmRamanujanPrimitive 2 ⌊u⌋₊).re * Real.sin (Real.pi * (n : ℝ) * u) =
      -Real.sin (Real.pi * (n : ℝ) * u)
    rw [hfl, pmRamanujanPrimitive_two_re]; norm_num
  rw [h01, zero_add, h12]
  set ω : ℝ := Real.pi * (n : ℝ)
  have hω : ω ≠ 0 := mul_ne_zero Real.pi_ne_zero (Nat.cast_ne_zero.mpr (by omega))
  have hd : ∀ x ∈ uIcc (1 : ℝ) 2,
      HasDerivAt (fun y => -Real.cos (ω * y) / ω) (Real.sin (ω * x)) x := fun x _ => by
    have h1 := (((hasDerivAt_id x).const_mul ω).cos.neg).div_const ω
    refine h1.congr_deriv ?_; dsimp only [id]; field_simp
  rw [show (fun u => Real.sin (Real.pi * (n : ℝ) * u)) = fun u => Real.sin (ω * u) from rfl,
    intervalIntegral.integral_eq_sub_of_hasDerivAt hd
      ((Real.continuous_sin.comp (continuous_const.mul continuous_id)).intervalIntegrable 1 2)]
  have hc2 : Real.cos (ω * 2) = 1 := by
    rw [show ω * 2 = (n : ℝ) * (2 * Real.pi) by dsimp [ω]; ring]
    simp
  have hc1 : Real.cos (ω * 1) = (-1 : ℝ) ^ n := by
    rw [mul_one, show ω = (n : ℝ) * Real.pi by dsimp [ω]; ring]
    simpa using Real.cos_add_nat_mul_pi 0 n
  rw [hc2, hc1]
  rcases Nat.mod_two_eq_zero_or_one n with hmod | hmod
  · obtain ⟨k, rfl⟩ : ∃ k, n = 2 * k := ⟨n / 2, by omega⟩
    rw [if_neg (by omega), pow_mul, neg_one_sq, one_pow]
    ring
  · obtain ⟨k, rfl⟩ : ∃ k, n = 2 * k + 1 := ⟨n / 2, by omega⟩
    rw [if_pos (by omega), pow_add, pow_mul, neg_one_sq, one_pow, pow_one, one_mul]
    dsimp [ω]
    field_simp
    ring

/-- **All-harmonic folded sieve identity at zero damping (`ε = 0`, `r = 2`).**
For every sine harmonic `n ≥ 1`, the finite dilated sum of `foldedZeroDampingProfile` reproduces the
exact Fourier mode of `(pmRamanujanPrimitive 2 ⌊u⌋₊).re` on `[0, 2]`:
`∑_{m=1}^n (1/m) ∫_0^2 G_0(m u) sin(π n u) du = ∫_0^2 C_2(⌊u⌋) sin(π n u) du`. -/
theorem sum_dilated_foldedZeroDampingProfile_fourier_eq {n : ℕ} (hn : 1 ≤ n) :
    ∑ m ∈ Finset.Icc 1 n, (1 / (m : ℝ)) *
      (∫ u in (0 : ℝ)..2, foldedZeroDampingProfile ((m : ℝ) * u) * Real.sin (Real.pi * (n : ℝ) * u)) =
      ∫ u in (0 : ℝ)..2, (pmRamanujanPrimitive 2 ⌊u⌋₊).re * Real.sin (Real.pi * (n : ℝ) * u) := by
  rw [integral_pmRamanujanPrimitive_two_mul_sin hn]
  have hterm : ∀ m ∈ Finset.Icc 1 n,
      (1 / (m : ℝ)) *
        (∫ u in (0 : ℝ)..2, foldedZeroDampingProfile ((m : ℝ) * u) *
          Real.sin (Real.pi * (n : ℝ) * u)) =
        (if m = n then 2 / (Real.pi * (n : ℝ)) else 0) +
          (if 2 * m = n then -(2 / (Real.pi * (n : ℝ))) else 0) := by
    intro m hm
    have hm1 : 1 ≤ m := (Finset.mem_Icc.mp hm).1
    have hrew : EqOn
        (fun u => foldedZeroDampingProfile ((m : ℝ) * u) * Real.sin (Real.pi * (n : ℝ) * u))
        (fun u => (2 / Real.pi) *
            (Real.sin (Real.pi * (m : ℝ) * u) * Real.sin (Real.pi * (n : ℝ) * u)) -
          (1 / Real.pi) *
            (Real.sin (Real.pi * ((2 * m : ℕ) : ℝ) * u) * Real.sin (Real.pi * (n : ℝ) * u)))
        (uIcc 0 2) := by
      intro u _
      dsimp only
      unfold foldedZeroDampingProfile
      push_cast; ring
    have hint₁ : IntervalIntegrable
        (fun u => (2 / Real.pi) *
          (Real.sin (Real.pi * (m : ℝ) * u) * Real.sin (Real.pi * (n : ℝ) * u)))
        volume 0 2 :=
      ((((Real.continuous_sin.comp (continuous_const.mul continuous_id)).mul
        (Real.continuous_sin.comp (continuous_const.mul continuous_id))).const_mul _).intervalIntegrable 0 2)
    have hint₂ : IntervalIntegrable
        (fun u => (1 / Real.pi) *
          (Real.sin (Real.pi * ((2 * m : ℕ) : ℝ) * u) * Real.sin (Real.pi * (n : ℝ) * u)))
        volume 0 2 :=
      ((((Real.continuous_sin.comp (continuous_const.mul continuous_id)).mul
        (Real.continuous_sin.comp (continuous_const.mul continuous_id))).const_mul _).intervalIntegrable 0 2)
    rw [intervalIntegral.integral_congr hrew, intervalIntegral.integral_sub hint₁ hint₂,
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
      integral_zero_two_sin_mul_sin hm1 hn, integral_zero_two_sin_mul_sin (by omega) hn]
    by_cases hmn : m = n
    · subst hmn
      have h2m : 2 * m ≠ m := by omega
      simp only [ite_true, if_neg h2m, mul_one, mul_zero, sub_zero, add_zero]
      ring
    · by_cases h2mn : 2 * m = n
      · subst h2mn
        have hm0 : (m : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
        have hpi0 : Real.pi ≠ 0 := Real.pi_ne_zero
        simp only [if_neg hmn, ite_true, mul_zero, mul_one, zero_sub, zero_add]
        push_cast; field_simp
      · simp only [if_neg hmn, if_neg h2mn, mul_zero, sub_zero, add_zero]
  rw [Finset.sum_congr rfl hterm, Finset.sum_add_distrib]
  have hmem_n : n ∈ Finset.Icc 1 n := Finset.mem_Icc.mpr ⟨hn, le_rfl⟩
  have hs1 : (∑ m ∈ Finset.Icc 1 n,
      if m = n then 2 / (Real.pi * (n : ℝ)) else 0) = 2 / (Real.pi * (n : ℝ)) := by
    rw [Finset.sum_ite_eq' (Finset.Icc 1 n) n]
    simp [hmem_n]
  rw [hs1]
  rcases Nat.mod_two_eq_zero_or_one n with hmod | hmod
  · rw [if_neg (by omega : n % 2 ≠ 1)]
    have hmem2 : n / 2 ∈ Finset.Icc 1 n := Finset.mem_Icc.mpr ⟨by omega, by omega⟩
    have hs2 : (∑ m ∈ Finset.Icc 1 n,
        if 2 * m = n then -(2 / (Real.pi * (n : ℝ))) else 0) = -(2 / (Real.pi * (n : ℝ))) := by
      have hiff : ∀ m, (2 * m = n) ↔ (m = n / 2) := fun m => by omega
      simp_rw [hiff]
      rw [Finset.sum_ite_eq' (Finset.Icc 1 n) (n / 2)]
      simp [hmem2]
    rw [hs2]; ring
  · rw [if_pos hmod]
    have hs2 : (∑ m ∈ Finset.Icc 1 n,
        if 2 * m = n then -(2 / (Real.pi * (n : ℝ))) else 0) = 0 :=
      Finset.sum_eq_zero fun m _ => if_neg (by omega)
    rw [hs2]; ring

end GaloisForLFunctions.SignedSuccessorArithmetic
