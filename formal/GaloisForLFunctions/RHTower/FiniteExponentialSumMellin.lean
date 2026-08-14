import GaloisForLFunctions.RHTower.MellinLinePolarization

/-!
# Finite exponential sums on the Mellin line

A finite sum `∑ c_i exp(-m_i x)` with positive rates has Mellin transform
`Γ(s) ∑ c_i m_i^{-s}` on the open right half-plane, and its logarithmic Mellin source lies in
`L¹ ∩ L²` on every line `Re s = σ > 0`.  These are the hypotheses of the polarized line law, so
finite exponential sums pair exactly between the half-line and the vertical line.
-/

open Complex MeasureTheory Real Set Filter
open scoped FourierTransform Topology

noncomputable section

namespace RHTower

/-- A finite exponential sum with prescribed coefficients and decay rates. -/
def expDecaySum {ι : Type*} (s : Finset ι) (c m : ι → ℝ) (x : ℝ) : ℝ :=
  ∑ i ∈ s, c i * Real.exp (-(m i * x))

theorem continuous_expDecaySum {ι : Type*} (s : Finset ι) (c m : ι → ℝ) :
    Continuous (expDecaySum s c m) := by
  unfold expDecaySum
  exact continuous_finsetSum _ fun i _ => by fun_prop

/-- A common decay rate majorizes the whole sum. -/
theorem abs_expDecaySum_le {ι : Type*} (s : Finset ι) (c m : ι → ℝ) {a x : ℝ}
    (ha : ∀ i ∈ s, a ≤ m i) (hx : 0 ≤ x) :
    |expDecaySum s c m x| ≤ (∑ i ∈ s, |c i|) * Real.exp (-(a * x)) := by
  rw [expDecaySum, Finset.sum_mul]
  refine le_trans (Finset.abs_sum_le_sum_abs _ _) (Finset.sum_le_sum fun i hi => ?_)
  rw [abs_mul, abs_of_pos (Real.exp_pos _)]
  have hexp : Real.exp (-(m i * x)) ≤ Real.exp (-(a * x)) := by
    refine Real.exp_le_exp.mpr ?_
    have := ha i hi
    nlinarith
  exact mul_le_mul_of_nonneg_left hexp (abs_nonneg _)

/-! ## The Mellin transform -/

theorem mellinConvergent_exp_neg_mul {m : ℝ} (hm : 0 < m) {σ : ℂ} (hσ : 0 < σ.re) :
    MellinConvergent (fun x : ℝ => ((Real.exp (-(m * x)) : ℝ) : ℂ)) σ := by
  have hbase : MellinConvergent (fun x : ℝ => ((Real.exp (-x) : ℝ) : ℂ)) σ := by
    have h := Complex.GammaIntegral_convergent hσ
    rw [MellinConvergent]
    refine h.congr_fun (fun x _ => ?_) measurableSet_Ioi
    rw [smul_eq_mul, mul_comm]
  exact (MellinConvergent.comp_mul_left hm).2 hbase

theorem mellin_exp_neg_mul {m : ℝ} (hm : 0 < m) {σ : ℂ} (hσ : 0 < σ.re) :
    mellin (fun x : ℝ => ((Real.exp (-(m * x)) : ℝ) : ℂ)) σ
      = (m : ℂ) ^ (-σ) * Complex.Gamma σ := by
  have hbase : mellin (fun x : ℝ => ((Real.exp (-x) : ℝ) : ℂ)) σ = Complex.Gamma σ := by
    rw [Complex.Gamma_eq_integral hσ, Complex.GammaIntegral, mellin]
    refine setIntegral_congr_fun measurableSet_Ioi fun x _ => ?_
    rw [smul_eq_mul, mul_comm]
  have h := mellin_comp_mul_left (fun x : ℝ => ((Real.exp (-x) : ℝ) : ℂ)) σ hm
  rw [hbase] at h
  rw [h, smul_eq_mul]

/-- **Mellin transform of a finite exponential sum.** -/
theorem mellin_expDecaySum {ι : Type*} (s : Finset ι) (c m : ι → ℝ)
    (hm : ∀ i ∈ s, 0 < m i) {σ : ℂ} (hσ : 0 < σ.re) :
    mellin (fun x : ℝ => ((expDecaySum s c m x : ℝ) : ℂ)) σ
      = Complex.Gamma σ * ∑ i ∈ s, (c i : ℂ) * (m i : ℂ) ^ (-σ) := by
  have hconv : ∀ i ∈ s, IntegrableOn
      (fun x : ℝ => (x : ℂ) ^ (σ - 1) • ((Real.exp (-(m i * x)) : ℝ) : ℂ)) (Ioi 0) volume :=
    fun i hi => mellinConvergent_exp_neg_mul (hm i hi) hσ
  have hint : ∀ i ∈ s, IntegrableOn
      (fun x : ℝ => (c i : ℂ) • ((x : ℂ) ^ (σ - 1) • ((Real.exp (-(m i * x)) : ℝ) : ℂ)))
      (Ioi 0) volume := fun i hi => Integrable.smul (c i : ℂ) (hconv i hi)
  have hmellin : ∀ i : ι,
      (∫ x in Ioi (0 : ℝ), (x : ℂ) ^ (σ - 1) • ((Real.exp (-(m i * x)) : ℝ) : ℂ))
        = mellin (fun x : ℝ => ((Real.exp (-(m i * x)) : ℝ) : ℂ)) σ := fun i => rfl
  rw [mellin]
  have hpoint : ∀ x : ℝ, (x : ℂ) ^ (σ - 1) • ((expDecaySum s c m x : ℝ) : ℂ)
      = ∑ i ∈ s, (c i : ℂ) • ((x : ℂ) ^ (σ - 1) • ((Real.exp (-(m i * x)) : ℝ) : ℂ)) := by
    intro x
    simp only [expDecaySum, smul_eq_mul]
    push_cast
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [setIntegral_congr_fun measurableSet_Ioi (fun x _ => hpoint x),
    MeasureTheory.integral_finsetSum s hint, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [MeasureTheory.integral_smul, hmellin i, mellin_exp_neg_mul (hm i hi) hσ, smul_eq_mul]
  ring

/-! ## The logarithmic source lies in `L¹ ∩ L²` -/

/-- The doubly exponential logarithmic majorant is integrable. -/
theorem integrable_exp_neg_mul_exp_neg_exp {σ a : ℝ} (hσ : 0 < σ) (ha : 0 < a) :
    Integrable (fun u : ℝ => Real.exp (-σ * u) * Real.exp (-(a * Real.exp (-u)))) := by
  have hmeas : Continuous (fun u : ℝ => Real.exp (-σ * u) * Real.exp (-(a * Real.exp (-u)))) := by
    fun_prop
  have hIoi : IntegrableOn
      (fun u : ℝ => Real.exp (-σ * u) * Real.exp (-(a * Real.exp (-u)))) (Ioi 0) volume := by
    refine Integrable.mono' (exp_neg_integrableOn_Ioi 0 hσ) hmeas.aestronglyMeasurable.restrict ?_
    refine Filter.Eventually.of_forall fun u => ?_
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    have hle : Real.exp (-(a * Real.exp (-u))) ≤ 1 := by
      rw [Real.exp_le_one_iff]
      have : (0 : ℝ) < a * Real.exp (-u) := by positivity
      linarith
    nlinarith [Real.exp_pos (-σ * u), hle]
  have hIic : IntegrableOn
      (fun u : ℝ => Real.exp (-σ * u) * Real.exp (-(a * Real.exp (-u)))) (Iic 0) volume := by
    have hmaj : IntegrableOn
        (fun u : ℝ => Real.exp ((σ + 1) ^ 2 / a) * Real.exp u) (Iic 0) volume :=
      (integrableOn_exp_Iic 0).const_mul _
    refine Integrable.mono' hmaj hmeas.aestronglyMeasurable.restrict ?_
    refine (ae_restrict_iff' measurableSet_Iic).2 (Filter.Eventually.of_forall fun u hu => ?_)
    have hu0 : u ≤ 0 := hu
    obtain ⟨v, hv0, rfl⟩ : ∃ v : ℝ, 0 ≤ v ∧ u = -v := ⟨-u, by linarith, by ring⟩
    -- `e^v ≥ (1 + v/2)²`
    have hhalf : (1 : ℝ) + v / 2 ≤ Real.exp (v / 2) := by
      have := Real.add_one_le_exp (v / 2)
      linarith
    have hquad : (1 : ℝ) + v + v ^ 2 / 4 ≤ Real.exp v := by
      have hsq : ((1 : ℝ) + v / 2) ^ 2 ≤ Real.exp (v / 2) ^ 2 := by
        have h0 : (0 : ℝ) ≤ 1 + v / 2 := by linarith
        exact pow_le_pow_left₀ h0 hhalf 2
      have hexp : Real.exp (v / 2) ^ 2 = Real.exp v := by
        rw [← Real.exp_nat_mul]
        congr 1
        ring
      nlinarith [hsq, hexp]
    have h2 : (σ + 1) * v ≤ a * ((1 : ℝ) + v + v ^ 2 / 4) + (σ + 1) ^ 2 / a := by
      have hsq : 0 ≤ (a * v / 2 - (σ + 1)) ^ 2 := sq_nonneg _
      have hstep : (σ + 1) * v - a * v ^ 2 / 4 ≤ (σ + 1) ^ 2 / a := by
        rw [le_div_iff₀ ha]
        nlinarith [hsq]
      have hpos : 0 ≤ a * (1 + v) := by positivity
      nlinarith [hstep, hpos]
    have hkey : (σ + 1) * v ≤ a * Real.exp v + (σ + 1) ^ 2 / a := by
      have h1 : a * ((1 : ℝ) + v + v ^ 2 / 4) ≤ a * Real.exp v :=
        mul_le_mul_of_nonneg_left hquad ha.le
      linarith
    have hval : Real.exp (-σ * -v) * Real.exp (-(a * Real.exp (-(-v))))
        = Real.exp (σ * v - a * Real.exp v) := by
      rw [neg_neg, ← Real.exp_add]
      congr 1
      ring
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity), hval, ← Real.exp_add]
    refine Real.exp_le_exp.mpr ?_
    linarith
  have hunion : IntegrableOn
      (fun u : ℝ => Real.exp (-σ * u) * Real.exp (-(a * Real.exp (-u)))) (Iic 0 ∪ Ioi 0) volume :=
    hIic.union hIoi
  rw [Iic_union_Ioi] at hunion
  rwa [integrableOn_univ] at hunion

/-- Every exponentially dominated continuous field has an `L¹` logarithmic Mellin source. -/
theorem integrable_logMellinLineSource_of_exp_bound {f : ℝ → ℂ} {sigma C a : ℝ}
    (hsigma : 0 < sigma) (ha : 0 < a) (hf : Continuous f)
    (hbound : ∀ x : ℝ, 0 < x → ‖f x‖ ≤ C * Real.exp (-(a * x))) :
    Integrable (logMellinLineSource f sigma) := by
  have hC : 0 ≤ C := by
    have h := hbound 1 one_pos
    have h0 : (0 : ℝ) ≤ ‖f 1‖ := norm_nonneg _
    nlinarith [Real.exp_pos (-(a * 1)), h, h0]
  have hmeas : Continuous (logMellinLineSource f sigma) := by
    unfold logMellinLineSource
    fun_prop
  have hmaj := (integrable_exp_neg_mul_exp_neg_exp hsigma ha).const_mul C
  refine Integrable.mono' hmaj hmeas.aestronglyMeasurable ?_
  refine Filter.Eventually.of_forall fun u => ?_
  have hx : (0 : ℝ) < Real.exp (-u) := Real.exp_pos _
  have hb := hbound (Real.exp (-u)) hx
  have hnorm : ‖logMellinLineSource f sigma u‖
      = Real.exp (-sigma * u) * ‖f (Real.exp (-u))‖ := by
    rw [logMellinLineSource, norm_smul, Real.norm_eq_abs, abs_of_nonneg (Real.exp_pos _).le]
  rw [hnorm]
  calc Real.exp (-sigma * u) * ‖f (Real.exp (-u))‖
      ≤ Real.exp (-sigma * u) * (C * Real.exp (-(a * Real.exp (-u)))) :=
        mul_le_mul_of_nonneg_left hb (Real.exp_pos _).le
    _ = C * (Real.exp (-sigma * u) * Real.exp (-(a * Real.exp (-u)))) := by ring

/-- Every exponentially dominated continuous field has an `L²` logarithmic Mellin source. -/
theorem memLp_two_logMellinLineSource_of_exp_bound {f : ℝ → ℂ} {sigma C a : ℝ}
    (hsigma : 0 < sigma) (ha : 0 < a) (hf : Continuous f)
    (hbound : ∀ x : ℝ, 0 < x → ‖f x‖ ≤ C * Real.exp (-(a * x))) :
    MemLp (logMellinLineSource f sigma) 2 volume := by
  have hC : 0 ≤ C := by
    have h := hbound 1 one_pos
    have h0 : (0 : ℝ) ≤ ‖f 1‖ := norm_nonneg _
    nlinarith [Real.exp_pos (-(a * 1)), h, h0]
  have hmeas : Continuous (logMellinLineSource f sigma) := by
    unfold logMellinLineSource
    fun_prop
  refine (memLp_two_iff_integrable_sq_norm hmeas.aestronglyMeasurable).2 ?_
  have hmaj := (integrable_exp_neg_mul_exp_neg_exp
    (show (0 : ℝ) < 2 * sigma by linarith) (show (0 : ℝ) < 2 * a by linarith)).const_mul (C ^ 2)
  refine Integrable.mono' hmaj (by fun_prop) ?_
  refine Filter.Eventually.of_forall fun u => ?_
  have hx : (0 : ℝ) < Real.exp (-u) := Real.exp_pos _
  have hb := hbound (Real.exp (-u)) hx
  have hnorm : ‖logMellinLineSource f sigma u‖
      = Real.exp (-sigma * u) * ‖f (Real.exp (-u))‖ := by
    rw [logMellinLineSource, norm_smul, Real.norm_eq_abs, abs_of_nonneg (Real.exp_pos _).le]
  have hsq : Real.exp (-(2 * sigma) * u) = Real.exp (-sigma * u) ^ 2 := by
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  have hsq2 : Real.exp (-(2 * a * Real.exp (-u))) = Real.exp (-(a * Real.exp (-u))) ^ 2 := by
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity), hnorm, hsq, hsq2]
  have h0 : (0 : ℝ) ≤ Real.exp (-sigma * u) := (Real.exp_pos _).le
  have hfn : (0 : ℝ) ≤ ‖f (Real.exp (-u))‖ := norm_nonneg _
  calc (Real.exp (-sigma * u) * ‖f (Real.exp (-u))‖) ^ 2
      ≤ (Real.exp (-sigma * u) * (C * Real.exp (-(a * Real.exp (-u))))) ^ 2 := by
        have := mul_le_mul_of_nonneg_left hb h0
        exact pow_le_pow_left₀ (by positivity) this 2
    _ = C ^ 2 * (Real.exp (-sigma * u) ^ 2 * Real.exp (-(a * Real.exp (-u))) ^ 2) := by ring

end RHTower
