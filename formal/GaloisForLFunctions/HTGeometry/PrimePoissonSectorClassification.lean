import GaloisForLFunctions.HTGeometry.PrimePoissonSuperselectionScreen

/-!
# Equivalence classes of the prime Poisson sectors

The prime Poisson law `P_{σ,t}` is the product over primes of the Poisson measures with parameter
`p^{-σ+it}`.  By Kakutani's dichotomy, two such laws are either equivalent or mutually singular,
according to whether `Σ_p ‖p^{-σ+it} − p^{-σ'+it'}‖²` converges.  That sum converges exactly when
both sectors lie strictly right of the critical line or the sectors coincide
(`summable_normSq_primePoissonParameterValue_sub_iff`):

* `σ, σ' > ½`: each term is at most `2(p^{-2σ} + p^{-2σ'})`;
* `σ < σ'`, `σ ≤ ½`: the moduli alone give `≥ (1 − 2^{σ−σ'})² p^{-2σ}`, and `Σ p^{-2σ} = ∞`;
* `σ = σ' ≤ ½`, `t ≠ t'`: the term is `p^{1−2σ} ≥ 1` times the critical prime-clock defect
  `2(1 − cos((t−t') log p))/p`, which diverges.

Hence `P_{σ,t} ~ P_{σ',t'}` iff `(σ, σ' > ½) ∨ (σ, t) = (σ', t')`
(`primePoissonMeasure_mutuallyAbsolutelyContinuous_iff`), and the laws are mutually singular
otherwise (`primePoissonMeasure_mutuallySingular_of_not`).
-/

open Complex MeasureTheory Filter Set
open scoped Topology

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- Off the critical sector, the parameter is a real dilation of the critical one. -/
theorem primePoissonParameterValue_eq_exp_mul_half (σ t : ℝ) (p : Nat.Primes) :
    primePoissonParameterValue σ t p =
      ((Real.exp (-(σ - 1 / 2) * Real.log (p : ℝ)) : ℝ) : ℂ) *
        primePoissonParameterValue (1 / 2) t p := by
  rw [primePoissonParameterValue_eq_radius_mul_phase,
    primePoissonParameterValue_eq_radius_mul_phase, ← mul_assoc, ← Complex.ofReal_mul,
    ← Real.exp_add]
  congr 3
  ring

theorem normSq_primePoissonParameterValue_sub_same (σ t t' : ℝ) (p : Nat.Primes) :
    ‖primePoissonParameterValue σ t p - primePoissonParameterValue σ t' p‖ ^ 2 =
      Real.exp ((1 - 2 * σ) * Real.log (p : ℝ)) *
        ‖primePoissonParameterValue (1 / 2) t p - primePoissonParameterValue (1 / 2) t' p‖ ^ 2 := by
  rw [primePoissonParameterValue_eq_exp_mul_half σ t, primePoissonParameterValue_eq_exp_mul_half σ t',
    ← mul_sub, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), mul_pow,
    ← Real.exp_nat_mul]
  congr 2
  push_cast
  ring

theorem not_summable_exp_neg_two_mul_log {σ : ℝ} (hσ : 0 < σ) (hσ2 : σ ≤ 1 / 2) :
    ¬ Summable (fun p : Nat.Primes => Real.exp (-(2 * σ) * Real.log (p : ℝ))) := by
  intro h
  have h' := (summable_normSq_primePoissonParameter_zero_iff σ 0 hσ).1 (h.congr fun p => by
    rw [sub_zero, coe_primePoissonParameter, norm_primePoissonParameterValue, ← Real.exp_nat_mul]
    congr 1
    push_cast
    ring)
  linarith

/-- **Kakutani summability for prime Poisson sectors.** -/
theorem summable_normSq_primePoissonParameterValue_sub_iff {σ σ' : ℝ} (hσ : 0 < σ) (hσ' : 0 < σ')
    (t t' : ℝ) :
    Summable (fun p : Nat.Primes =>
      ‖primePoissonParameterValue σ t p - primePoissonParameterValue σ' t' p‖ ^ 2) ↔
      ((1 / 2 < σ ∧ 1 / 2 < σ') ∨ (σ = σ' ∧ t = t')) := by
  constructor
  · intro hsum
    by_contra hnot
    push Not at hnot
    obtain ⟨hhalf, hsame⟩ := hnot
    have hmin : σ ≤ 1 / 2 ∨ σ' ≤ 1 / 2 := by
      by_cases h : 1 / 2 < σ
      · exact Or.inr (hhalf h)
      · exact Or.inl (not_lt.1 h)
    -- the strict-modulus case, with the smaller exponent `a ≤ ½`
    have hmod : ∀ {a b ta tb : ℝ}, 0 < a → a < b → a ≤ 1 / 2 →
        Summable (fun p : Nat.Primes =>
          ‖primePoissonParameterValue a ta p - primePoissonParameterValue b tb p‖ ^ 2) → False := by
      intro a b ta tb ha hab ha2 hs
      set ρ := Real.exp (-(b - a) * Real.log 2) with hρ
      have hρ1 : ρ < 1 := by
        rw [hρ, Real.exp_lt_one_iff]
        exact mul_neg_of_neg_of_pos (by linarith) (Real.log_pos one_lt_two)
      have hρ0 : 0 < 1 - ρ := by linarith
      have hc : 0 < (1 - ρ) ^ 2 := by positivity
      apply not_summable_exp_neg_two_mul_log ha ha2
      refine ((hs.div_const ((1 - ρ) ^ 2)).of_nonneg_of_le (fun p => (Real.exp_pos _).le)
        fun p => ?_)
      rw [le_div_iff₀ hc]
      have hL : Real.log 2 ≤ Real.log (p : ℝ) :=
        Real.log_le_log two_pos (by exact_mod_cast p.prop.two_le)
      have hrev := abs_norm_sub_norm_le (primePoissonParameterValue a ta p)
        (primePoissonParameterValue b tb p)
      rw [norm_primePoissonParameterValue, norm_primePoissonParameterValue] at hrev
      set A := Real.exp (-a * Real.log (p : ℝ))
      set B := Real.exp (-b * Real.log (p : ℝ))
      have hBA : B ≤ A * ρ := by
        rw [hρ, ← Real.exp_add]
        exact Real.exp_le_exp.2 (by nlinarith)
      have hA : 0 < A := Real.exp_pos _
      have hgap : A * (1 - ρ) ≤ |A - B| := by
        rw [abs_of_nonneg (by nlinarith)]
        linarith
      have h1ρ : 0 ≤ 1 - ρ := by linarith
      have hnn : 0 ≤ A * (1 - ρ) := mul_nonneg hA.le h1ρ
      have hsq : (A * (1 - ρ)) ^ 2 ≤ ‖primePoissonParameterValue a ta p -
          primePoissonParameterValue b tb p‖ ^ 2 :=
        pow_le_pow_left₀ hnn (hgap.trans hrev) 2
      have hA2 : Real.exp (-(2 * a) * Real.log (p : ℝ)) = A ^ 2 := by
        rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
      calc Real.exp (-(2 * a) * Real.log (p : ℝ)) * (1 - ρ) ^ 2 = (A * (1 - ρ)) ^ 2 := by
            rw [hA2]; ring
        _ ≤ _ := hsq
    rcases lt_trichotomy σ σ' with hlt | heq | hgt
    · exact hmod hσ hlt (by rcases hmin with h | h <;> linarith) hsum
    · subst heq
      have htt : t ≠ t' := hsame rfl
      have hσ2 : σ ≤ 1 / 2 := by rcases hmin with h | h <;> linarith
      apply not_summable_normSq_primePoissonParameter_half_sub_of_ne htt
      refine hsum.of_nonneg_of_le (fun p => by positivity) fun p => ?_
      rw [normSq_primePoissonParameterValue_sub_same σ t t' p]
      have hL : 0 ≤ Real.log (p : ℝ) := Real.log_nonneg (by exact_mod_cast p.prop.one_lt.le)
      have h1 : 1 ≤ Real.exp ((1 - 2 * σ) * Real.log (p : ℝ)) :=
        Real.one_le_exp (mul_nonneg (by linarith) hL)
      exact le_mul_of_one_le_left (by positivity) h1
    · exact hmod hσ' hgt (by rcases hmin with h | h <;> linarith)
        (hsum.congr fun p => by rw [← norm_neg, neg_sub])
  · rintro (⟨h1, h2⟩ | ⟨rfl, rfl⟩)
    · have hs1 := (summable_normSq_primePoissonParameter_zero_iff σ t hσ).2 h1
      have hs2 := (summable_normSq_primePoissonParameter_zero_iff σ' t' hσ').2 h2
      simp only [sub_zero, coe_primePoissonParameter] at hs1 hs2
      refine ((hs1.add hs2).mul_left 2).of_nonneg_of_le (fun p => by positivity) fun p => ?_
      have h3 := pow_le_pow_left₀ (norm_nonneg _)
        (norm_sub_le (primePoissonParameterValue σ t p) (primePoissonParameterValue σ' t' p)) 2
      nlinarith [sq_nonneg (‖primePoissonParameterValue σ t p‖ -
        ‖primePoissonParameterValue σ' t' p‖)]
    · simp

/-- **Equivalence of prime Poisson sectors.**  `P_{σ,t}` and `P_{σ',t'}` are mutually absolutely
continuous iff both lie strictly right of the critical line or they coincide. -/
theorem primePoissonMeasure_mutuallyAbsolutelyContinuous_iff (σ σ' t t' : ℝ) (hσ : 0 < σ)
    (hσ' : 0 < σ') :
    (primePoissonMeasure σ t hσ ≪ primePoissonMeasure σ' t' hσ' ∧
        primePoissonMeasure σ' t' hσ' ≪ primePoissonMeasure σ t hσ) ↔
      ((1 / 2 < σ ∧ 1 / 2 < σ') ∨ (σ = σ' ∧ t = t')) := by
  rw [primePoissonMeasure, primePoissonMeasure,
    torusPoissonMeasure_mutuallyAbsolutelyContinuous_iff_summable_normSq _ _
      (tendsto_primePoissonParameter_natEquivPrimes_zero σ t hσ)
      (tendsto_primePoissonParameter_natEquivPrimes_zero σ' t' hσ')]
  simp only [coe_primePoissonParameter]
  exact summable_normSq_primePoissonParameterValue_sub_iff hσ hσ' t t'

/-- **Kakutani dichotomy for prime Poisson sectors.**  Inequivalent sectors are mutually
singular. -/
theorem primePoissonMeasure_mutuallySingular_of_not {σ σ' t t' : ℝ} (hσ : 0 < σ) (hσ' : 0 < σ')
    (h : ¬((1 / 2 < σ ∧ 1 / 2 < σ') ∨ (σ = σ' ∧ t = t'))) :
    (primePoissonMeasure σ t hσ).MutuallySingular (primePoissonMeasure σ' t' hσ') := by
  unfold primePoissonMeasure
  apply torusPoissonMeasure_mutuallySingular_of_not_summable_normSq
  simp only [coe_primePoissonParameter]
  rwa [summable_normSq_primePoissonParameterValue_sub_iff hσ hσ' t t']

end

end GaloisForLFunctions.HTGeometry
