import GaloisForLFunctions.RHTower.ChenGuptaLiLemma62PrincipalRegularizedContour
import GaloisForLFunctions.RHTower.ChenGuptaLiLemma62MellinKernel
import GaloisForLFunctions.HTGeometry.GammaCosineCriticalModulus

/-!
# Chen--Gupta--Li Lemma 6.2, principal branch: the critical line

On `Re s = 1/2` the principal finite reflected integrand
`H(s) N^s · χ_reg(s − it) · E_Q(s − it) · D_M(1 − s + it)` has every factor under control: the
regularized functional multiplier `χ_reg` and the finite Euler correction `E_Q` have unit modulus
there (both are `f(z)/conj f(z)`-shaped at `Re z = 1/2`), the Dirichlet head `D_M` is a finite sum of
`M + 1` terms of modulus at most one, `|N^s| = N^{1/2}`, and the Mellin factor decays faster than any
power of `Im s`.  Hence the integrand is continuous and absolutely integrable along the critical
line, which is the input to the principal finite-window bound.
-/

open Complex MeasureTheory Filter Set
open scoped LSeries.notation BigOperators

namespace RHTower

noncomputable section

/-- `1 − z = conj z` on the critical line. -/
theorem cglLemma62_one_sub_eq_conj_of_critical {z : ℂ} (hz : z.re = 1 / 2) :
    1 - z = (starRingEnd ℂ) z := by
  apply Complex.ext
  · simp [hz]; norm_num
  · simp

/-- The regularized functional multiplier has unit modulus on the critical line. -/
theorem norm_cglLemma62PrincipalRegularizedFunctionalFactor_critical {z : ℂ} (hz : z.re = 1 / 2) :
    ‖cglLemma62PrincipalRegularizedFunctionalFactor z‖ = 1 := by
  have hsub : 1 - z = (1 / 2 : ℂ) - (z.im : ℂ) * I := by
    apply Complex.ext
    · simp [hz]; norm_num
    · simp
  unfold cglLemma62PrincipalRegularizedFunctionalFactor
  rw [hsub]
  exact GaloisForLFunctions.HTGeometry.norm_zetaFunctionalFactor_critical z.im

/-- `p^{−(1−z)} = conj (p^{−z})` on the critical line. -/
theorem cglLemma62_principal_nat_cpow_reflects_critical (p : ℕ) {z : ℂ} (hz : z.re = 1 / 2) :
    (p : ℂ) ^ (-(1 - z)) = (starRingEnd ℂ) ((p : ℂ) ^ (-z)) := by
  have hreflect := cglLemma62_one_sub_eq_conj_of_critical hz
  calc (p : ℂ) ^ (-(1 - z)) = (p : ℂ) ^ ((starRingEnd ℂ) (-z)) := by rw [hreflect]; simp
    _ = (starRingEnd ℂ) ((starRingEnd ℂ) (p : ℂ) ^ (-z)) :=
        Complex.cpow_conj (p : ℂ) (-z) (by rw [Complex.natCast_arg]; positivity)
    _ = (starRingEnd ℂ) ((p : ℂ) ^ (-z)) := by simp

/-- On the critical line the right principal Euler factor is the conjugate of the left one. -/
theorem cglLemma62_principalEulerRightFactorAt_critical_conj (Q : CGLPositiveModulus) {z : ℂ}
    (hz : z.re = 1 / 2) :
    cglLemma62PrincipalEulerRightFactorAt Q z =
      (starRingEnd ℂ) (cglLemma62PrincipalEulerLeftFactorAt Q z) := by
  unfold cglLemma62PrincipalEulerRightFactorAt cglLemma62PrincipalEulerLeftFactorAt
  rw [map_prod]
  refine Finset.prod_congr rfl fun p _ => ?_
  rw [cglLemma62_principal_nat_cpow_reflects_critical p hz, map_sub, map_one]

/-- The left principal Euler factor does not vanish on the critical line. -/
theorem cglLemma62_principalEulerLeftFactorAt_critical_ne_zero (Q : CGLPositiveModulus) {z : ℂ}
    (hz : z.re = 1 / 2) : cglLemma62PrincipalEulerLeftFactorAt Q z ≠ 0 := by
  unfold cglLemma62PrincipalEulerLeftFactorAt
  refine Finset.prod_ne_zero_iff.mpr fun p hp => ?_
  have hprime : p.Prime := Nat.prime_of_mem_primeFactors hp
  have hpow : ‖(p : ℂ) ^ (-z)‖ < 1 := by
    rw [Complex.norm_natCast_cpow_of_pos hprime.pos]
    apply Real.rpow_lt_one_of_one_lt_of_neg
    · exact_mod_cast hprime.one_lt
    · simp [hz]
  intro hzero
  have hone : (p : ℂ) ^ (-z) = 1 := (sub_eq_zero.mp hzero).symm
  have := congrArg norm hone
  rw [norm_one] at this
  linarith

/-- The principal finite Euler correction has unit modulus on the critical line. -/
theorem norm_cglLemma62PrincipalEulerCorrectionAt_critical (Q : CGLPositiveModulus) {z : ℂ}
    (hz : z.re = 1 / 2) : ‖cglLemma62PrincipalEulerCorrectionAt Q z‖ = 1 := by
  unfold cglLemma62PrincipalEulerCorrectionAt
  rw [norm_div, cglLemma62_principalEulerRightFactorAt_critical_conj Q hz, Complex.norm_conj,
    div_self (norm_ne_zero_iff.mpr (cglLemma62_principalEulerLeftFactorAt_critical_ne_zero Q hz))]

/-- A Dirichlet head of length `M` has modulus at most `M + 1` on `Re s ≥ 0`. -/
theorem norm_cglLemma62DirichletHead_le {q : ℕ} (χ : DirichletCharacter ℂ q) (M : ℕ) {s : ℂ}
    (hs : 0 ≤ s.re) : ‖cglLemma62DirichletHead χ M s‖ ≤ (M : ℝ) + 1 := by
  unfold cglLemma62DirichletHead
  refine (norm_sum_le _ _).trans ?_
  have hterm : ∀ n ∈ Finset.range (M + 1), ‖LSeries.term (↗χ) s n‖ ≤ 1 := by
    intro n _
    rcases Nat.eq_zero_or_pos n with hn | hn
    · subst hn; simp [LSeries.term_zero]
    · rw [LSeries.term_of_ne_zero hn.ne', norm_div, Complex.norm_natCast_cpow_of_pos hn]
      have hχ : ‖(↗χ) n‖ ≤ 1 := χ.norm_le_one _
      have hden : (1 : ℝ) ≤ (n : ℝ) ^ s.re := Real.one_le_rpow (by exact_mod_cast hn) hs
      calc ‖(↗χ) n‖ / (n : ℝ) ^ s.re ≤ 1 / 1 := by gcongr
        _ = 1 := by norm_num
  calc ∑ n ∈ Finset.range (M + 1), ‖LSeries.term (↗χ) s n‖
      ≤ ∑ _n ∈ Finset.range (M + 1), (1 : ℝ) := Finset.sum_le_sum hterm
    _ = (M : ℝ) + 1 := by simp

/-- Pointwise bound on the critical line: `‖integrand‖ ≤ ‖H(1/2+iv)‖ · N^{1/2} · (M+1)`. -/
theorem norm_cglLemma62PrincipalRegularizedFiniteContourIntegrand_critical_le
    (w : CGLRealSmoothBump) (N : CGLPositiveLength) (Q : CGLPositiveModulus) (t : ℝ) (M : ℕ)
    (v : ℝ) :
    ‖cglLemma62PrincipalRegularizedFiniteContourIntegrand w N Q t M ((1 / 2 : ℂ) + (v : ℂ) * I)‖
      ≤ ‖cglLemma62MellinTransform w ((1 / 2 : ℂ) + (v : ℂ) * I)‖ *
          (N.value : ℝ) ^ (1 / 2 : ℝ) * ((M : ℝ) + 1) := by
  unfold cglLemma62PrincipalRegularizedFiniteContourIntegrand
  have hre1 : ((1 / 2 : ℂ) + (v : ℂ) * I - (t : ℂ) * I).re = 1 / 2 := by simp
  have hre2 : 0 ≤ (1 - ((1 / 2 : ℂ) + (v : ℂ) * I) + (t : ℂ) * I).re := by simp; norm_num
  have hN : ‖(N.value : ℂ) ^ ((1 / 2 : ℂ) + (v : ℂ) * I)‖ = (N.value : ℝ) ^ (1 / 2 : ℝ) := by
    rw [Complex.norm_natCast_cpow_of_pos N.positive]; simp
  rw [norm_mul, norm_mul, norm_mul, norm_mul, hN,
    norm_cglLemma62PrincipalRegularizedFunctionalFactor_critical hre1,
    norm_cglLemma62PrincipalEulerCorrectionAt_critical Q hre1]
  have hhead := norm_cglLemma62DirichletHead_le (1 : DirichletCharacter ℂ Q.value) M hre2
  have hM0 : 0 ≤ ‖cglLemma62MellinTransform w ((1 / 2 : ℂ) + (v : ℂ) * I)‖ *
      (N.value : ℝ) ^ (1 / 2 : ℝ) := by positivity
  calc ‖cglLemma62MellinTransform w ((1 / 2 : ℂ) + (v : ℂ) * I)‖ * (N.value : ℝ) ^ (1 / 2 : ℝ)
        * 1 * 1 * ‖cglLemma62DirichletHead (1 : DirichletCharacter ℂ Q.value) M
            (1 - ((1 / 2 : ℂ) + (v : ℂ) * I) + (t : ℂ) * I)‖
      = ‖cglLemma62MellinTransform w ((1 / 2 : ℂ) + (v : ℂ) * I)‖ * (N.value : ℝ) ^ (1 / 2 : ℝ)
        * ‖cglLemma62DirichletHead (1 : DirichletCharacter ℂ Q.value) M
            (1 - ((1 / 2 : ℂ) + (v : ℂ) * I) + (t : ℂ) * I)‖ := by ring
    _ ≤ ‖cglLemma62MellinTransform w ((1 / 2 : ℂ) + (v : ℂ) * I)‖ * (N.value : ℝ) ^ (1 / 2 : ℝ)
        * ((M : ℝ) + 1) := mul_le_mul_of_nonneg_left hhead hM0

/-- The principal finite integrand is continuous along the critical line. -/
theorem cglLemma62PrincipalRegularizedFinite_critical_continuous
    (w : CGLRealSmoothBump) (N : CGLPositiveLength) (Q : CGLPositiveModulus) (t : ℝ) (M : ℕ) :
    Continuous (fun v : ℝ =>
      cglLemma62PrincipalRegularizedFiniteContourIntegrand w N Q t M ((1 / 2 : ℂ) + (v : ℂ) * I)) := by
  let line : ℝ → ℂ := fun v => (1 / 2 : ℂ) + (v : ℂ) * I
  have hline : Continuous line := by dsimp [line]; fun_prop
  have hmaps : ∀ v : ℝ, line v ∈ GaloisForLFunctions.HTGeometry.verticalStrip (-1) (1 / 2) := by
    intro v
    change (-1 : ℝ) ≤ (line v).re ∧ (line v).re ≤ 1 / 2
    dsimp [line]
    simp
    norm_num
  have hcont := (cglLemma62PrincipalRegularizedFiniteContourIntegrand_differentiableOn w N Q t M).continuousOn
  change Continuous (cglLemma62PrincipalRegularizedFiniteContourIntegrand w N Q t M ∘ line)
  exact hcont.comp_continuous hline hmaps

/-- **Integrability along the critical line** of the principal finite integrand: the Mellin factor
supplies `|v|^{−2}` decay, the remaining factors are bounded. -/
theorem cglLemma62PrincipalRegularizedFinite_critical_integrable
    (w : CGLRealSmoothBump) (N : CGLPositiveLength) (Q : CGLPositiveModulus) (t : ℝ) (M : ℕ) :
    Integrable (fun v : ℝ =>
      cglLemma62PrincipalRegularizedFiniteContourIntegrand w N Q t M ((1 / 2 : ℂ) + (v : ℂ) * I)) := by
  set f : ℝ → ℂ := fun v =>
    cglLemma62PrincipalRegularizedFiniteContourIntegrand w N Q t M ((1 / 2 : ℂ) + (v : ℂ) * I)
    with hf
  have hcont : Continuous f := cglLemma62PrincipalRegularizedFinite_critical_continuous w N Q t M
  -- the Mellin decay budget at order two on the critical line
  obtain ⟨K, hKdef⟩ : ∃ K : ℝ, K = cglLemma62MellinLineDecayBudget w (1 / 2) 2 := ⟨_, rfl⟩
  have hK0 : 0 ≤ K := by
    rw [hKdef]
    exact le_trans (by positivity) (cglLemma62_mellinTransform_vertical_rapidDecay w (1 / 2) 2 0)
  have hMellin : ∀ v : ℝ, |v| ^ 2 * ‖cglLemma62MellinTransform w ((1 / 2 : ℂ) + (v : ℂ) * I)‖ ≤ K := by
    intro v
    have := cglLemma62_mellinTransform_vertical_rapidDecay w (1 / 2) 2 v
    rw [← hKdef] at this
    simpa using this
  obtain ⟨A, hAdef⟩ : ∃ A : ℝ, A = K * (N.value : ℝ) ^ (1 / 2 : ℝ) * ((M : ℝ) + 1) := ⟨_, rfl⟩
  have hA0 : 0 ≤ A := by rw [hAdef]; positivity
  -- tail domination by `A |v|^{-2}` on `|v| > 1`
  have htailMeas : MeasurableSet {v : ℝ | (1 : ℝ) < |v|} :=
    measurableSet_lt continuous_const.measurable continuous_abs.measurable
  have hset : {v : ℝ | (1 : ℝ) < |v|} = Iio (-1) ∪ Ioi 1 := by
    ext v
    simp only [Set.mem_setOf_eq, Set.mem_union, Set.mem_Iio, Set.mem_Ioi]
    constructor
    · intro h
      rcases le_or_gt v 0 with hv | hv
      · left; rw [abs_of_nonpos hv] at h; linarith
      · right; rw [abs_of_pos hv] at h; exact h
    · rintro (h | h)
      · rw [abs_of_nonpos (by linarith)]; linarith
      · rw [abs_of_pos (by linarith)]; exact h
  have hmajor : IntegrableOn (fun v : ℝ => A * |v| ^ (-(2 : ℝ))) {v : ℝ | (1 : ℝ) < |v|} := by
    rw [hset]
    have hpos : IntegrableOn (fun v : ℝ => |v| ^ (-(2 : ℝ))) (Ioi 1) := by
      have hbase : IntegrableOn (fun v : ℝ => v ^ (-(2 : ℝ))) (Ioi 1) :=
        (integrableOn_Ioi_rpow_iff zero_lt_one).mpr (by norm_num)
      refine hbase.congr_fun (fun v hv => ?_) measurableSet_Ioi
      show v ^ (-(2 : ℝ)) = |v| ^ (-(2 : ℝ))
      rw [abs_of_pos (lt_trans zero_lt_one hv)]
    have hneg : IntegrableOn (fun v : ℝ => |v| ^ (-(2 : ℝ))) (Iio (-1)) := by
      have h := (Measure.measurePreserving_neg (volume : Measure ℝ)).integrableOn_comp_preimage
        (f := fun v : ℝ => |v| ^ (-(2 : ℝ))) (s := Iio (-1)) (measurableEmbedding_neg (α := ℝ))
      have hpre : (Neg.neg : ℝ → ℝ) ⁻¹' (Iio (-1) : Set ℝ) = Ioi 1 := by ext v; simp
      rw [hpre] at h
      have hfun : ((fun v : ℝ => |v| ^ (-(2 : ℝ))) ∘ (Neg.neg : ℝ → ℝ)) =
          fun v : ℝ => |v| ^ (-(2 : ℝ)) := by funext v; simp
      rw [hfun] at h
      exact h.mp hpos
    exact (hneg.union hpos).const_mul A
  have htail : IntegrableOn f {v : ℝ | (1 : ℝ) < |v|} := by
    refine Integrable.mono' hmajor (hcont.continuousOn.aestronglyMeasurable htailMeas) ?_
    filter_upwards [ae_restrict_mem htailMeas] with v hv
    have hv1 : (1 : ℝ) < |v| := hv
    have hvpos : 0 < |v| := lt_trans zero_lt_one hv1
    have hsq : 0 < |v| ^ 2 := by positivity
    have hM : ‖cglLemma62MellinTransform w ((1 / 2 : ℂ) + (v : ℂ) * I)‖ ≤ K / |v| ^ 2 := by
      rw [le_div_iff₀ hsq]; linarith [hMellin v]
    have hbound := norm_cglLemma62PrincipalRegularizedFiniteContourIntegrand_critical_le w N Q t M v
    have hNM : 0 ≤ (N.value : ℝ) ^ (1 / 2 : ℝ) * ((M : ℝ) + 1) := by positivity
    calc ‖f v‖ ≤ ‖cglLemma62MellinTransform w ((1 / 2 : ℂ) + (v : ℂ) * I)‖ *
          (N.value : ℝ) ^ (1 / 2 : ℝ) * ((M : ℝ) + 1) := hbound
      _ ≤ K / |v| ^ 2 * (N.value : ℝ) ^ (1 / 2 : ℝ) * ((M : ℝ) + 1) := by
          rw [mul_assoc, mul_assoc]
          exact mul_le_mul_of_nonneg_right hM hNM
      _ = A * |v| ^ (-(2 : ℝ)) := by
          rw [hAdef, Real.rpow_neg hvpos.le, Real.rpow_two]; ring
  have hmiddle : IntegrableOn f (Icc (-1) 1) := hcont.continuousOn.integrableOn_Icc
  have hcover : {v : ℝ | (1 : ℝ) < |v|} ∪ Icc (-1) 1 = univ := by
    ext v
    simp only [Set.mem_union, Set.mem_setOf_eq, Set.mem_Icc, Set.mem_univ, iff_true]
    by_cases hv : (1 : ℝ) < |v|
    · exact Or.inl hv
    · exact Or.inr (abs_le.mp (le_of_not_gt hv))
  rw [← integrableOn_univ, ← hcover]
  exact htail.union hmiddle

end

end RHTower
