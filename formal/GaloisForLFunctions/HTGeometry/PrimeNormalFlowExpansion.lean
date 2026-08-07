import GaloisForLFunctions.HTGeometry.PrimeNormalFlowEquation

/-!
# The all-grade expansion of the prime normal flow

The scalar binomial series for `(1 - z)^{-1/2}` has central binomial coefficients graded by `8^{-k}`
after the substitution `z = t/(2L)`.  Transporting it through the functional calculus expands the
prime normal flow into a norm-convergent series in the powers of `T`, valid on `L > ‖T‖/2`: every
length-`k` word of the generator appears with the universal coefficient `binom(2k,k)/8^k`.
-/

namespace GaloisForLFunctions.HTGeometry

open Filter Topology

theorem rpow_neg_half_eq {x : ℝ} (hx : 0 ≤ x) : x ^ (-(1 : ℝ) / 2) = (Real.sqrt x)⁻¹ := by
  rw [show (-(1 : ℝ) / 2) = -((1 : ℝ) / 2) by ring, Real.rpow_neg hx, Real.sqrt_eq_rpow]

/-- The grade coefficient of the card's `(4)`: `theta_k L^(-k-1/2)`. -/
noncomputable def gradeCoeff (L : ℝ) (k : ℕ) : ℝ :=
  primeNormalCoeff k * ((L ^ k)⁻¹ * (Real.sqrt L)⁻¹)

theorem gradeCoeff_nonneg {L : ℝ} (hL : 0 < L) (k : ℕ) : 0 ≤ gradeCoeff L k := by
  unfold gradeCoeff
  have := primeNormalCoeff_pos k
  positivity

/-- **The scalar expansion `(13)` in the spectral variable.** -/
theorem hasSum_flowSymbol {L t : ℝ} (hL : 0 < L) (ht : |t| < 2 * L) :
    HasSum (fun k : ℕ => gradeCoeff L k * t ^ k) (flowSymbol L t) := by
  have hz : |t / (2 * L)| < 1 := by
    rw [abs_div, abs_of_pos (by linarith : (0:ℝ) < 2 * L), div_lt_one (by linarith)]
    exact ht
  have h := hasSum_centralBinom_rpow hz
  have hzle : t / (2 * L) ≤ 1 := le_of_lt (lt_of_le_of_lt (le_abs_self _) hz)
  have hu : 0 < L - t / 2 := by
    have h1 : t < 2 * L := lt_of_le_of_lt (le_abs_self t) ht
    linarith
  have hsplit : (Real.sqrt L)⁻¹ * ((1 - t / (2 * L)) ^ (-(1:ℝ) / 2)) = flowSymbol L t := by
    have hprod : L * (1 - t / (2 * L)) = L - t / 2 := by field_simp
    have hmul : (L - t / 2) ^ (-(1:ℝ) / 2)
        = L ^ (-(1:ℝ) / 2) * (1 - t / (2 * L)) ^ (-(1:ℝ) / 2) := by
      rw [← hprod]
      exact Real.mul_rpow hL.le (by linarith)
    rw [flowSymbol, ← rpow_neg_half_eq hu.le, hmul, rpow_neg_half_eq hL.le]
  rw [← hsplit]
  have h2 := h.mul_left ((Real.sqrt L)⁻¹)
  refine h2.congr_fun ?_
  intro k
  unfold gradeCoeff primeNormalCoeff
  rw [div_pow, mul_pow]
  have hL8 : (8:ℝ) ^ k = 4 ^ k * 2 ^ k := by rw [← mul_pow]; norm_num
  field_simp
  rw [hL8]
  ring

section Banach

variable {B : Type*} [NormedRing B] [NormOneClass B] [NormedAlgebra ℝ B] [CompleteSpace B]

omit [NormOneClass B] [NormedAlgebra ℝ B] [CompleteSpace B] in
/-- The majorant series of the expansion. -/
theorem summable_gradeMajorant {T : B} {L : ℝ} (hL : ‖T‖ / 2 < L) :
    Summable (fun k : ℕ => gradeCoeff L k * ‖T‖ ^ k) := by
  have hL0 : 0 < L := lt_of_le_of_lt (by positivity) hL
  have hs := (hasSum_primeNormalCoeff (norm_nonneg T) hL).summable
  have hc := hs.mul_left ((Real.sqrt L)⁻¹)
  refine hc.congr fun k => ?_
  unfold gradeCoeff
  rw [div_pow]
  field_simp

omit [CompleteSpace B] in
theorem norm_gradeTerm_le {T : B} {L : ℝ} (hL : 0 < L) (k : ℕ) :
    ‖gradeCoeff L k • T ^ k‖ ≤ gradeCoeff L k * ‖T‖ ^ k := by
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (gradeCoeff_nonneg hL k)]
  exact mul_le_mul_of_nonneg_left (norm_pow_le T k) (gradeCoeff_nonneg hL k)

theorem summable_gradeTerm {T : B} {L : ℝ} (hL : ‖T‖ / 2 < L) :
    Summable (fun k : ℕ => gradeCoeff L k • T ^ k) := by
  have hL0 : 0 < L := lt_of_le_of_lt (by positivity) hL
  exact (summable_gradeMajorant hL).of_norm_bounded (fun k => norm_gradeTerm_le hL0 k)

omit [NormOneClass B] [NormedAlgebra ℝ B] [CompleteSpace B] in
/-- **The grade-mass identity `(19)`:** the majorant sums to `L^(-1/2)(1 - ‖T‖/(2L))^(-1/2)`. -/
theorem tsum_gradeMajorant {T : B} {L : ℝ} (hL : ‖T‖ / 2 < L) :
    ∑' k : ℕ, gradeCoeff L k * ‖T‖ ^ k
      = (Real.sqrt L)⁻¹ * (1 - ‖T‖ / (2 * L)) ^ (-(1 : ℝ) / 2) := by
  have hL0 : 0 < L := lt_of_le_of_lt (by positivity) hL
  have hs := (hasSum_primeNormalCoeff (norm_nonneg T) hL).mul_left ((Real.sqrt L)⁻¹)
  have hcongr : ∀ k : ℕ, (Real.sqrt L)⁻¹ * (primeNormalCoeff k * (‖T‖ / L) ^ k)
      = gradeCoeff L k * ‖T‖ ^ k := by
    intro k
    unfold gradeCoeff
    rw [div_pow]
    field_simp
  simp only [hcongr] at hs
  exact hs.tsum_eq

omit [CompleteSpace B] in
/-- **The `l^1` grade bound `(6)`--`(7)`:** in any Banach algebra the expansion converges
absolutely for `L > ‖T‖/2`, with total mass `L^(-1/2)(1 - ‖T‖/(2L))^(-1/2)`. -/
theorem norm_tsum_gradeTerm_le {T : B} {L : ℝ} (hL : ‖T‖ / 2 < L) :
    ‖∑' k : ℕ, gradeCoeff L k • T ^ k‖
      ≤ (Real.sqrt L)⁻¹ * (1 - ‖T‖ / (2 * L)) ^ (-(1 : ℝ) / 2) := by
  have hL0 : 0 < L := lt_of_le_of_lt (by positivity) hL
  have hns : Summable (fun k : ℕ => ‖gradeCoeff L k • T ^ k‖) :=
    (summable_gradeMajorant hL).of_nonneg_of_le (fun _ => norm_nonneg _)
      (fun k => norm_gradeTerm_le hL0 k)
  calc ‖∑' k : ℕ, gradeCoeff L k • T ^ k‖
      ≤ ∑' k : ℕ, ‖gradeCoeff L k • T ^ k‖ := norm_tsum_le_tsum_norm hns
    _ ≤ ∑' k : ℕ, gradeCoeff L k * ‖T‖ ^ k :=
        hns.tsum_le_tsum (fun k => norm_gradeTerm_le hL0 k) (summable_gradeMajorant hL)
    _ = (Real.sqrt L)⁻¹ * (1 - ‖T‖ / (2 * L)) ^ (-(1 : ℝ) / 2) := tsum_gradeMajorant hL

end Banach

variable {A : Type*} [CStarAlgebra A] [Nontrivial A]

omit [Nontrivial A] in
/-- The functional calculus of a polynomial partial sum is the operator partial sum. -/
theorem cfc_gradePartial {T : A} (hT : IsSelfAdjoint T) (L : ℝ) (n : ℕ) :
    cfc (fun t : ℝ => ∑ k ∈ Finset.range n, gradeCoeff L k * t ^ k) T
      = ∑ k ∈ Finset.range n, gradeCoeff L k • T ^ k := by
  have hfun : (fun t : ℝ => ∑ k ∈ Finset.range n, gradeCoeff L k * t ^ k)
      = ∑ k ∈ Finset.range n, (fun t : ℝ => gradeCoeff L k * t ^ k) := by
    funext t; simp
  rw [hfun, cfc_sum _ T _ (fun k _ => by fun_prop)]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [cfc_const_mul _ _ T (by fun_prop), cfc_pow (fun t : ℝ => t) k T, cfc_id' ℝ T hT]

omit [Nontrivial A] in
theorem continuousOn_gradePartial {T : A} (L : ℝ) (n : ℕ) :
    ContinuousOn (fun t : ℝ => ∑ k ∈ Finset.range n, gradeCoeff L k * t ^ k) (spectrum ℝ T) := by
  fun_prop

/-- **The all-grade expansion `(4)`.**  The prime normal flow is the norm-convergent sum of the
central-binomial graded powers of `T`. -/
theorem hasSum_primeNormalFlow {T : A} (hT : IsSelfAdjoint T) {L : ℝ} (hL : ‖T‖ / 2 < L) :
    HasSum (fun k : ℕ => gradeCoeff L k • T ^ k) (primeNormalFlow T L) := by
  have hL0 : 0 < L := lt_of_le_of_lt (by positivity) hL
  have hsum := summable_gradeTerm (T := T) hL
  have hmaj := summable_gradeMajorant (T := T) hL
  rw [hsum.hasSum_iff_tendsto_nat]
  -- the tail of the majorant controls the error uniformly on the spectrum
  have htail : ∀ n : ℕ,
      ‖primeNormalFlow T L - ∑ k ∈ Finset.range n, gradeCoeff L k • T ^ k‖
        ≤ ∑' k : ℕ, gradeCoeff L (k + n) * ‖T‖ ^ (k + n) := by
    intro n
    have hrepr : primeNormalFlow T L - ∑ k ∈ Finset.range n, gradeCoeff L k • T ^ k
        = cfc (fun t : ℝ => flowSymbol L t
            - ∑ k ∈ Finset.range n, gradeCoeff L k * t ^ k) T := by
      rw [cfc_sub _ _ T (continuousOn_flowSymbol hL) (continuousOn_gradePartial L n),
        cfc_gradePartial hT L n]
      rfl
    rw [hrepr]
    refine norm_cfc_le_of_forall_le (𝕜 := ℝ) _ T
      ((continuousOn_flowSymbol hL).sub (continuousOn_gradePartial L n)) hT ?_
    intro t ht
    have habs : |t| ≤ ‖T‖ := abs_le_norm_of_mem_spectrum ht
    have hlt : |t| < 2 * L := by linarith
    have hscal := hasSum_flowSymbol hL0 hlt
    have hsplit := hscal.summable.sum_add_tsum_nat_add n
    have heq : flowSymbol L t - ∑ k ∈ Finset.range n, gradeCoeff L k * t ^ k
        = ∑' k : ℕ, gradeCoeff L (k + n) * t ^ (k + n) := by
      rw [← hscal.tsum_eq, ← hsplit]
      ring
    have hb1 : ∀ k : ℕ, ‖gradeCoeff L (k + n) * t ^ (k + n)‖
        ≤ gradeCoeff L (k + n) * ‖T‖ ^ (k + n) := by
      intro k
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (gradeCoeff_nonneg hL0 _), abs_pow]
      exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (abs_nonneg t) habs _)
        (gradeCoeff_nonneg hL0 _)
    have hsummable_shift : Summable (fun k : ℕ => gradeCoeff L (k + n) * ‖T‖ ^ (k + n)) :=
      (summable_nat_add_iff n).mpr hmaj
    have hns : Summable (fun k : ℕ => ‖gradeCoeff L (k + n) * t ^ (k + n)‖) :=
      hsummable_shift.of_nonneg_of_le (fun _ => norm_nonneg _) hb1
    show ‖flowSymbol L t - ∑ k ∈ Finset.range n, gradeCoeff L k * t ^ k‖ ≤ _
    rw [heq]
    calc ‖∑' k : ℕ, gradeCoeff L (k + n) * t ^ (k + n)‖
        ≤ ∑' k : ℕ, ‖gradeCoeff L (k + n) * t ^ (k + n)‖ := norm_tsum_le_tsum_norm hns
      _ ≤ ∑' k : ℕ, gradeCoeff L (k + n) * ‖T‖ ^ (k + n) :=
          hns.tsum_le_tsum hb1 hsummable_shift
  -- the majorant tail vanishes
  have hzero : Tendsto (fun n : ℕ => ∑' k : ℕ, gradeCoeff L (k + n) * ‖T‖ ^ (k + n))
      atTop (𝓝 0) := tendsto_sum_nat_add (fun k => gradeCoeff L k * ‖T‖ ^ k)
  rw [← tendsto_sub_nhds_zero_iff, tendsto_zero_iff_norm_tendsto_zero]
  refine squeeze_zero' (Eventually.of_forall fun n => norm_nonneg _) ?_ hzero
  filter_upwards with n
  rw [norm_sub_rev]
  exact htail n

end GaloisForLFunctions.HTGeometry
