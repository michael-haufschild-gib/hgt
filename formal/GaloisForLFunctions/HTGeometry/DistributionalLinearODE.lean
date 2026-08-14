import GaloisForLFunctions.HTGeometry.ExponentialTwistInversion
import Mathlib.Analysis.Normed.Algebra.Exponential
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Distributional solutions of a constant-coefficient transport equation are classical

If a vector-valued tempered distribution `u` satisfies `u' = A u` on an interval for a bounded
operator `A`, then on that interval it is the locally integrable function `t ↦ exp(t A) c` for a
single vector `c`.  The proof is the exponential twist: the twist of `u` is constant by the du
Bois-Reymond lemma, and the twist is inverted by the opposite twist, which reconstructs `u` as the
power series of the propagator against the moments of the test function.
-/

open Set SchwartzMap MeasureTheory

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]

omit [CompleteSpace X] in
theorem coordPow_coordPow (n k : ℕ) (φ : SchwartzMap ℝ ℂ) :
    coordPow n (coordPow k φ) = coordPow (n + k) φ := by
  refine SchwartzMap.ext fun x => ?_
  rw [coordPow_apply, coordPow_apply, coordPow_apply, pow_add]
  ring

/-- The exponential of a scalar multiple of a bounded operator, expanded on a vector. -/
theorem exp_smul_apply_eq_tsum (A : X →L[ℂ] X) (z : ℂ) (c : X) :
    NormedSpace.exp (z • A) c = ∑' k : ℕ, (((k.factorial : ℂ))⁻¹ * z ^ k) • ((A ^ k) c) := by
  have hsum : Summable (fun k : ℕ => ((k.factorial : ℂ))⁻¹ • ((z • A) ^ k)) :=
    NormedSpace.expSeries_summable' (𝕂 := ℂ) (z • A)
  have hexp : NormedSpace.exp (z • A) = ∑' k : ℕ, ((k.factorial : ℂ))⁻¹ • ((z • A) ^ k) := by
    rw [NormedSpace.exp_eq_tsum ℂ]
  have hmap := ContinuousLinearMap.map_tsum
    (ContinuousLinearMap.apply ℂ X c) hsum
  rw [hexp]
  rw [show ((ContinuousLinearMap.apply ℂ X c)
      (∑' k : ℕ, ((k.factorial : ℂ))⁻¹ • ((z • A) ^ k)))
      = (∑' k : ℕ, ((k.factorial : ℂ))⁻¹ • ((z • A) ^ k)) c from rfl] at hmap
  rw [hmap]
  refine tsum_congr fun k => ?_
  rw [ContinuousLinearMap.apply_apply]
  show (((k.factorial : ℂ))⁻¹ • ((z • A) ^ k)) c = _
  rw [smul_pow, smul_apply, smul_apply, smul_smul]

/-- The propagator integral against a compactly supported test function is the moment series of the
propagator. -/
theorem intervalIntegral_smul_exp (A : X →L[ℂ] X) (c : X) {a b : ℝ} (hab : a ≤ b)
    (φ : SchwartzMap ℝ ℂ) :
    (∫ t in a..b, (φ : ℝ → ℂ) t • (NormedSpace.exp ((t : ℂ) • A) c))
      = ∑' k : ℕ, ((k.factorial : ℂ))⁻¹ •
          ((A ^ k) ((∫ t in a..b, ((coordPow k φ : SchwartzMap ℝ ℂ) : ℝ → ℂ) t) • c)) := by
  set B : ℝ := max |a| |b| with hB
  have hBnn : 0 ≤ B := le_trans (abs_nonneg a) (le_max_left _ _)
  set M : ℝ := SchwartzMap.seminorm ℂ 0 0 φ with hM
  have hMnn : 0 ≤ M := apply_nonneg _ _
  have hMbd : ∀ t : ℝ, ‖(φ : ℝ → ℂ) t‖ ≤ M := fun t => SchwartzMap.norm_le_seminorm ℂ φ t
  set F : ℕ → ℝ → X := fun k t =>
    (((k.factorial : ℂ))⁻¹ * (t : ℂ) ^ k * (φ : ℝ → ℂ) t) • ((A ^ k) c) with hF
  -- the pointwise expansion
  have hpoint : ∀ t : ℝ, (φ : ℝ → ℂ) t • (NormedSpace.exp ((t : ℂ) • A) c) = ∑' k : ℕ, F k t := by
    intro t
    have hsum : Summable (fun k : ℕ => (((k.factorial : ℂ))⁻¹ * ((t : ℂ)) ^ k) • ((A ^ k) c)) := by
      have h := (NormedSpace.expSeries_summable' (𝕂 := ℂ) (((t : ℂ)) • A)).map
        (ContinuousLinearMap.apply ℂ X c) (ContinuousLinearMap.apply ℂ X c).continuous
      refine h.congr fun k => ?_
      show ((((k.factorial : ℂ))⁻¹ • ((((t : ℂ)) • A) ^ k)) c) = _
      rw [smul_pow, smul_apply, smul_apply, smul_smul]
    rw [exp_smul_apply_eq_tsum, ← hsum.tsum_const_smul ((φ : ℝ → ℂ) t)]
    refine tsum_congr fun k => ?_
    rw [hF]
    simp only [smul_smul]
    congr 1
    ring
  -- each term is integrable and the norms are summable
  have hcont : ∀ k : ℕ, Continuous (F k) := by
    intro k
    refine Continuous.smul ?_ continuous_const
    exact (continuous_const.mul (Complex.continuous_ofReal.pow k)).mul φ.continuous
  have hintegrable : ∀ k : ℕ, IntegrableOn (F k) (Ioc a b) volume := fun k =>
    (hcont k).integrableOn_Ioc
  have hnormbd : ∀ (k : ℕ), ∀ t ∈ Ioc a b,
      ‖F k t‖ ≤ M * ‖c‖ * ((B * ‖A‖) ^ k / (k.factorial : ℝ)) := by
    intro k t ht
    have htB : |t| ≤ B := abs_le_max_abs_of_mem_Icc ⟨ht.1.le, ht.2⟩
    have h1 : ‖(((k.factorial : ℂ))⁻¹ * (t : ℂ) ^ k * (φ : ℝ → ℂ) t)‖
        ≤ ((k.factorial : ℝ))⁻¹ * B ^ k * M := by
      rw [norm_mul, norm_mul]
      have hc1 : ‖((k.factorial : ℂ))⁻¹‖ = ((k.factorial : ℝ))⁻¹ := by simp
      have hc2 : ‖((t : ℂ)) ^ k‖ = |t| ^ k := by
        rw [norm_pow, Complex.norm_real, Real.norm_eq_abs]
      rw [hc1, hc2]
      refine mul_le_mul (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (abs_nonneg t) htB k)
        (by positivity)) (hMbd t) (norm_nonneg _) (by positivity)
    have h2 : ‖(A ^ k) c‖ ≤ ‖A‖ ^ k * ‖c‖ := norm_pow_apply_le A k c
    rw [hF]
    simp only
    rw [norm_smul]
    calc ‖(((k.factorial : ℂ))⁻¹ * (t : ℂ) ^ k * (φ : ℝ → ℂ) t)‖ * ‖(A ^ k) c‖
        ≤ (((k.factorial : ℝ))⁻¹ * B ^ k * M) * (‖A‖ ^ k * ‖c‖) :=
          mul_le_mul h1 h2 (norm_nonneg _) (by positivity)
      _ = M * ‖c‖ * ((B * ‖A‖) ^ k / (k.factorial : ℝ)) := by
          rw [mul_pow, div_eq_mul_inv]
          ring
  have hintnorm : ∀ k : ℕ, (∫ t in Ioc a b, ‖F k t‖)
      ≤ (b - a) * (M * ‖c‖ * ((B * ‖A‖) ^ k / (k.factorial : ℝ))) := by
    intro k
    have hmono : (∫ t in Ioc a b, ‖F k t‖)
        ≤ ∫ _t in Ioc a b, M * ‖c‖ * ((B * ‖A‖) ^ k / (k.factorial : ℝ)) := by
      refine MeasureTheory.setIntegral_mono_on ((hintegrable k).norm)
        (continuous_const.integrableOn_Ioc) measurableSet_Ioc (hnormbd k)
    refine le_trans hmono ?_
    rw [MeasureTheory.setIntegral_const, Real.volume_real_Ioc_of_le hab, smul_eq_mul]
  have hsummable : Summable (fun k : ℕ => ∫ t in Ioc a b, ‖F k t‖) := by
    refine Summable.of_nonneg_of_le (fun k => MeasureTheory.integral_nonneg fun _ => norm_nonneg _)
      hintnorm ?_
    exact ((Real.summable_pow_div_factorial (B * ‖A‖)).mul_left (M * ‖c‖)).mul_left (b - a)
  -- interchange the sum and the integral
  rw [intervalIntegral.integral_of_le hab]
  have hswap : (∑' k : ℕ, ∫ t in Ioc a b, F k t) = ∫ t in Ioc a b, ∑' k : ℕ, F k t :=
    MeasureTheory.integral_tsum_of_summable_integral_norm hintegrable hsummable
  have hcongr : (∫ t in Ioc a b, (φ : ℝ → ℂ) t • (NormedSpace.exp ((t : ℂ) • A) c))
      = ∫ t in Ioc a b, ∑' k : ℕ, F k t :=
    MeasureTheory.setIntegral_congr_fun measurableSet_Ioc fun t _ => hpoint t
  rw [hcongr, ← hswap]
  refine tsum_congr fun k => ?_
  have hterm : (∫ t in Ioc a b, F k t)
      = (∫ t in Ioc a b, (((k.factorial : ℂ))⁻¹ * (t : ℂ) ^ k * (φ : ℝ → ℂ) t)) • ((A ^ k) c) :=
    integral_smul_const _ _
  rw [hterm, map_smul]
  have hmoment : (∫ t in Ioc a b, (((k.factorial : ℂ))⁻¹ * (t : ℂ) ^ k * (φ : ℝ → ℂ) t))
      = ((k.factorial : ℂ))⁻¹ * ∫ t in Ioc a b, ((coordPow k φ : SchwartzMap ℝ ℂ) : ℝ → ℂ) t := by
    rw [← MeasureTheory.integral_const_mul]
    refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioc fun t _ => ?_
    rw [coordPow_apply]
    ring
  rw [hmoment, intervalIntegral.integral_of_le hab, smul_smul, mul_smul]

/-- **A distributional solution of `u' = A u` on an interval is the propagator applied to a single
vector.** -/
theorem exists_exp_representation (A : X →L[ℂ] X) (u : SchwartzMap ℝ ℂ →L[ℂ] X) {a b : ℝ}
    (hab : a < b)
    (hode : ∀ ψ : SchwartzMap ℝ ℂ, (∀ x, x ∉ Ioo a b → (ψ : ℝ → ℂ) x = 0) →
      u (SchwartzMap.derivCLM ℂ ℂ ψ) = -(A (u ψ))) :
    ∃ c : X, ∀ φ : SchwartzMap ℝ ℂ, (∀ x, x ∉ Ioo a b → (φ : ℝ → ℂ) x = 0) →
      u φ = ∫ t in a..b, (φ : ℝ → ℂ) t • (NormedSpace.exp ((t : ℂ) • A) c) := by
  obtain ⟨c, hc⟩ := exists_expTwist_const A u hab hode
  refine ⟨c, fun φ hsupp => ?_⟩
  obtain ⟨C, D, hC, hD, hbd⟩ := exists_bound_coordPow u hsupp
  have hw : ∀ k : ℕ,
      (∑' n : ℕ, ((n.factorial : ℂ))⁻¹ • (((-A) ^ n) (u (coordPow (n + k) φ))))
        = (∫ t in a..b, ((coordPow k φ : SchwartzMap ℝ ℂ) : ℝ → ℂ) t) • c := by
    intro k
    have hexp : expTwist A u (coordPow k φ)
        = ∑' n : ℕ, ((n.factorial : ℂ))⁻¹ • (((-A) ^ n) (u (coordPow (n + k) φ))) := by
      rw [expTwist]
      exact tsum_congr fun n => by rw [expTwistTerm_eq, coordPow_coordPow]
    rw [← hexp]
    exact hc (coordPow k φ) (coordPow_eq_zero_of_notMem hsupp k)
  have key : (∑' k : ℕ, ((k.factorial : ℂ))⁻¹ •
      ((A ^ k) ((∫ t in a..b, ((coordPow k φ : SchwartzMap ℝ ℂ) : ℝ → ℂ) t) • c))) = u φ := by
    have hinv := tsum_twistInv A (fun j => u (coordPow j φ)) hC hD hbd
    simp only [coordPow_zero] at hinv
    rw [← hinv]
    exact tsum_congr fun k => by rw [hw k]
  rw [intervalIntegral_smul_exp A c hab.le φ]
  exact key.symm

end

end GaloisForLFunctions.HTGeometry
