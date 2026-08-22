import GaloisForLFunctions.RHTower.ChenGuptaLiLemma62PrincipalResidue
import GaloisForLFunctions.RHTower.ZetaVerticalLineGrowth

/-!
# Chen--Gupta--Li Lemma 6.2: principal vertical-edge bounds

The first CGL shift needs integrability of the principal-character integrand
on both vertical edges.  The trivial character's `L`-function is a finite
Euler factor times zeta away from its sole pole.  This module transfers the
corpus's unconditional zeta vertical-line bound through that finite factor,
then absorbs its polynomial growth with the all-order Mellin decay of `H`.
-/

open Complex
open MeasureTheory Filter Set
open scoped BigOperators

noncomputable section

namespace RHTower

/-- Uniform finite Euler-factor budget on CGL's first-shift strip. -/
def cglLemma62PrincipalEulerBudget (Q : CGLPositiveModulus) : ℝ :=
  ∏ p ∈ Q.value.primeFactors, (1 + (p : ℝ))

private theorem cglLemma62_principalEulerFactor_norm_le
    (Q : CGLPositiveModulus) {z : ℂ} (hz : (-1 : ℝ) ≤ z.re)
    (p : ↑Q.value.primeFactors) :
    ‖1 - (p.1 : ℂ) ^ (-z)‖ ≤ 1 + (p.1 : ℝ) := by
  have hpprime : p.1.Prime := Nat.prime_of_mem_primeFactors p.2
  have hppos : (0 : ℝ) < p.1 := by exact_mod_cast hpprime.pos
  have hpone : (1 : ℝ) ≤ p.1 := by exact_mod_cast hpprime.one_le
  have hpow : ‖(p.1 : ℂ) ^ (-z)‖ ≤ (p.1 : ℝ) := by
    change ‖((p.1 : ℝ) : ℂ) ^ (-z)‖ ≤ (p.1 : ℝ)
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hppos]
    have hre : (-z).re = -z.re := by simp
    rw [hre]
    have hexp : -z.re ≤ (1 : ℝ) := by linarith
    calc
      (p.1 : ℝ) ^ (-z.re) ≤ (p.1 : ℝ) ^ (1 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le hpone hexp
      _ = p.1 := Real.rpow_one _
  calc
    ‖1 - (p.1 : ℂ) ^ (-z)‖ ≤ ‖(1 : ℂ)‖ + ‖(p.1 : ℂ) ^ (-z)‖ :=
      norm_sub_le _ _
    _ ≤ 1 + (p.1 : ℝ) := by
      rw [norm_one]
      linarith

private theorem cglLemma62_principalEulerProduct_norm_le
    (Q : CGLPositiveModulus) {z : ℂ} (hz : (-1 : ℝ) ≤ z.re) :
    ‖∏ p ∈ Q.value.primeFactors, (1 - (p : ℂ) ^ (-z))‖ ≤
      cglLemma62PrincipalEulerBudget Q := by
  rw [norm_prod]
  refine Finset.prod_le_prod (fun p hp => norm_nonneg _) ?_
  intro p hp
  exact cglLemma62_principalEulerFactor_norm_le Q hz ⟨p, hp⟩

private theorem cglLemma62_exists_bound_principalLFunction_vertical_at
    (Q : CGLPositiveModulus) (σ : ℝ) (hσlow : (-1 : ℝ) ≤ σ) (hσ : σ ≠ 1) :
    ∃ E : ℝ, ∃ N : ℕ, 0 < E ∧ ∀ v : ℝ,
      ‖DirichletCharacter.LFunctionTrivChar Q.value ((σ : ℂ) + (v : ℂ) * I)‖ ≤
        E * (1 + |v|) ^ N := by
  letI : NeZero Q.value := ⟨Nat.ne_of_gt Q.positive⟩
  obtain ⟨C, N, hC, hzeta⟩ := exists_bound_norm_riemannZeta_vertical σ hσ
  have hbudget : 0 < cglLemma62PrincipalEulerBudget Q := by
    unfold cglLemma62PrincipalEulerBudget
    refine Finset.prod_pos fun p hp => ?_
    positivity
  refine ⟨cglLemma62PrincipalEulerBudget Q * (C + 1), N, mul_pos hbudget (by linarith), ?_⟩
  intro v
  let z : ℂ := (σ : ℂ) + (v : ℂ) * I
  have hzre : (-1 : ℝ) ≤ z.re := by
    dsimp [z]
    simp
    exact hσlow
  have hne : z ≠ 1 := by
    intro h
    have hre := congrArg Complex.re h
    dsimp [z] at hre
    simp at hre
    exact hσ (by linarith)
  have heuler := cglLemma62_principalEulerProduct_norm_le Q hzre
  have hchange : DirichletCharacter.LFunctionTrivChar Q.value z =
      (∏ p ∈ Q.value.primeFactors, (1 - (p : ℂ) ^ (-z))) * riemannZeta z := by
    exact DirichletCharacter.LFunctionTrivChar_eq_mul_riemannZeta hne
  have hζ : ‖riemannZeta z‖ ≤ C * (1 + |v|) ^ N := by
    exact hzeta v
  rw [hchange, norm_mul]
  calc
    ‖∏ p ∈ Q.value.primeFactors, (1 - (p : ℂ) ^ (-z))‖ * ‖riemannZeta z‖ ≤
        cglLemma62PrincipalEulerBudget Q * (C * (1 + |v|) ^ N) :=
      mul_le_mul heuler hζ (norm_nonneg _) (by positivity)
    _ ≤ (cglLemma62PrincipalEulerBudget Q * (C + 1)) * (1 + |v|) ^ N := by
      have hpow : (0 : ℝ) ≤ (1 + |v|) ^ N := by positivity
      nlinarith

/-- A closed polynomial vertical-line bound for the principal CGL `L` factor
on the shifted left edge. -/
theorem cglLemma62_exists_bound_principalLFunction_left
    (Q : CGLPositiveModulus) :
    ∃ E : ℝ, ∃ N : ℕ, 0 < E ∧ ∀ v : ℝ,
      ‖DirichletCharacter.LFunctionTrivChar Q.value ((-1 : ℂ) + (v : ℂ) * I)‖ ≤
        E * (1 + |v|) ^ N := by
  simpa using cglLemma62_exists_bound_principalLFunction_vertical_at Q (-1) (by norm_num) (by norm_num)

/-- A closed polynomial vertical-line bound for the principal CGL `L` factor
on the initial right edge. -/
theorem cglLemma62_exists_bound_principalLFunction_right
    (Q : CGLPositiveModulus) :
    ∃ E : ℝ, ∃ N : ℕ, 0 < E ∧ ∀ v : ℝ,
      ‖DirichletCharacter.LFunctionTrivChar Q.value ((2 : ℂ) + (v : ℂ) * I)‖ ≤
        E * (1 + |v|) ^ N := by
  simpa using cglLemma62_exists_bound_principalLFunction_vertical_at Q 2 (by norm_num) (by norm_num)

/-- A closed polynomial bound for the principal CGL `L` factor uniformly on
the first-shift strip above unit height. -/
theorem cglLemma62_exists_bound_principalLFunction_strip
    (Q : CGLPositiveModulus) :
    ∃ E : ℝ, ∃ N : ℕ, 0 < E ∧ ∀ x v : ℝ,
      (-1 : ℝ) ≤ x → x ≤ 2 → 1 ≤ |v| →
      ‖DirichletCharacter.LFunctionTrivChar Q.value ((x : ℂ) + (v : ℂ) * I)‖ ≤
        E * (1 + |v|) ^ N := by
  letI : NeZero Q.value := ⟨Nat.ne_of_gt Q.positive⟩
  obtain ⟨C, N, hC, hzeta⟩ := exists_bound_norm_riemannZeta_strip 2
  have hbudget : 0 < cglLemma62PrincipalEulerBudget Q := by
    unfold cglLemma62PrincipalEulerBudget
    refine Finset.prod_pos fun p hp => ?_
    positivity
  refine ⟨cglLemma62PrincipalEulerBudget Q * (C + 1), N,
    mul_pos hbudget (by linarith), ?_⟩
  intro x v hxlo hxhi hv
  let z : ℂ := (x : ℂ) + (v : ℂ) * I
  have hzre : (-1 : ℝ) ≤ z.re := by
    dsimp [z]
    simp
    exact hxlo
  have hne : z ≠ 1 := by
    intro h
    have him := congrArg Complex.im h
    dsimp [z] at him
    simp at him
    have hvpos : 0 < |v| := lt_of_lt_of_le zero_lt_one hv
    exact (ne_of_gt hvpos) (by simpa using congrArg abs him)
  have heuler := cglLemma62_principalEulerProduct_norm_le Q hzre
  have hchange : DirichletCharacter.LFunctionTrivChar Q.value z =
      (∏ p ∈ Q.value.primeFactors, (1 - (p : ℂ) ^ (-z))) * riemannZeta z := by
    exact DirichletCharacter.LFunctionTrivChar_eq_mul_riemannZeta hne
  have hζ : ‖riemannZeta z‖ ≤ C * |v| ^ N := by
    apply hzeta x v
    · exact abs_le.mpr ⟨by linarith, hxhi⟩
    · exact hv
  rw [hchange, norm_mul]
  have hmono : |v| ^ N ≤ (1 + |v|) ^ N := by
    exact pow_le_pow_left₀ (abs_nonneg v) (by linarith) N
  calc
    ‖∏ p ∈ Q.value.primeFactors, (1 - (p : ℂ) ^ (-z))‖ * ‖riemannZeta z‖ ≤
        cglLemma62PrincipalEulerBudget Q * (C * |v| ^ N) :=
      mul_le_mul heuler hζ (norm_nonneg _) (by positivity)
    _ ≤ (cglLemma62PrincipalEulerBudget Q * (C + 1)) * (1 + |v|) ^ N := by
      have hC' : C ≤ C + 1 := by linarith
      have hpow : (0 : ℝ) ≤ (1 + |v|) ^ N := by positivity
      have hstep : C * |v| ^ N ≤ (C + 1) * (1 + |v|) ^ N := by
        calc
          C * |v| ^ N ≤ C * (1 + |v|) ^ N :=
            mul_le_mul_of_nonneg_left hmono hC
          _ ≤ (C + 1) * (1 + |v|) ^ N :=
            mul_le_mul_of_nonneg_right hC' hpow
      calc
        cglLemma62PrincipalEulerBudget Q * (C * |v| ^ N) ≤
            cglLemma62PrincipalEulerBudget Q * ((C + 1) * (1 + |v|) ^ N) :=
          mul_le_mul_of_nonneg_left hstep hbudget.le
        _ = _ := by ring

private theorem cglLemma62_principalKernel_one_add_absPow_integrable
    (w : CGLRealSmoothBump) (σ : ℝ) (n : ℕ) :
    Integrable (fun v : ℝ => (1 + |v|) ^ n *
      ‖cglLemma62MellinTransform w ((σ : ℂ) + (v : ℂ) * I)‖) := by
  have h0 := cglLemma62_mellinTransform_vertical_integrable_absPow_norm w σ 0
  have hn := cglLemma62_mellinTransform_vertical_integrable_absPow_norm w σ n
  have h0' : Integrable (fun v : ℝ =>
      ‖cglLemma62MellinTransform w ((σ : ℂ) + (v : ℂ) * I)‖) := by
    simpa using h0
  have hsum := (h0'.add hn).const_mul ((2 : ℝ) ^ (n - 1))
  refine Integrable.mono' hsum ?_ ?_
  · have hdiff : Differentiable ℂ (cglLemma62MellinTransform w) := fun s =>
      (cglLemma62_mellinTransform_analyticOnNhd w s (mem_univ s)).differentiableAt
    have hline : Continuous (fun v : ℝ => (σ : ℂ) + (v : ℂ) * I) := by fun_prop
    have hweight : Continuous (fun v : ℝ => (1 + |v|) ^ n) := by fun_prop
    exact (hweight.mul (hdiff.continuous.comp hline).norm).aestronglyMeasurable
  filter_upwards with v
  have hpow := add_pow_le (a := (1 : ℝ)) (b := |v|) zero_le_one (abs_nonneg v) n
  rw [Real.norm_eq_abs, abs_of_nonneg
    (mul_nonneg (pow_nonneg (by positivity) _) (norm_nonneg _))]
  calc
    (1 + |v|) ^ n * ‖cglLemma62MellinTransform w ((σ : ℂ) + (v : ℂ) * I)‖ ≤
        (2 ^ (n - 1) * (1 + |v| ^ n)) *
          ‖cglLemma62MellinTransform w ((σ : ℂ) + (v : ℂ) * I)‖ :=
      mul_le_mul_of_nonneg_right (by simpa using hpow) (norm_nonneg _)
    _ = 2 ^ (n - 1) * (‖cglLemma62MellinTransform w ((σ : ℂ) + (v : ℂ) * I)‖ +
        |v| ^ n * ‖cglLemma62MellinTransform w ((σ : ℂ) + (v : ℂ) * I)‖) := by ring

private theorem cglLemma62_principal_shifted_weight_le (t v : ℝ) (n : ℕ) :
    (1 + |v - t|) ^ n ≤ (1 + |t|) ^ n * (1 + |v|) ^ n := by
  have hbase : 1 + |v - t| ≤ (1 + |t|) * (1 + |v|) := by
    rw [abs_sub_comm]
    have htri : |t - v| ≤ |t| + |v| := by
      calc
        |t - v| = |t + (-v)| := by rw [sub_eq_add_neg]
        _ ≤ |t| + |-v| := abs_add_le _ _
        _ = |t| + |v| := by rw [abs_neg]
    nlinarith [abs_nonneg t, abs_nonneg v]
  have hpow := pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ 1 + |v - t|) hbase n
  rw [mul_pow] at hpow
  exact hpow

private theorem cglLemma62_principalContourIntegrand_vertical_integrable_at
    (w : CGLRealSmoothBump) (N : CGLPositiveLength) (Q : CGLPositiveModulus) (t σ : ℝ)
    (hσlow : (-1 : ℝ) ≤ σ) (hσ : σ ≠ 1) :
    Integrable (fun v : ℝ => cglLemma62PrincipalContourIntegrand w N Q t
      ((σ : ℂ) + (v : ℂ) * I)) := by
  letI : NeZero Q.value := ⟨Nat.ne_of_gt Q.positive⟩
  obtain ⟨E, n, hE, hLbound⟩ :=
    cglLemma62_exists_bound_principalLFunction_vertical_at Q σ hσlow hσ
  have hkernel := cglLemma62_principalKernel_one_add_absPow_integrable w σ n
  let Hline : ℝ → ℂ := fun v => cglLemma62MellinTransform w ((σ : ℂ) + (v : ℂ) * I)
  have hkernel' : Integrable (fun v : ℝ => (1 + |v|) ^ n * ‖Hline v‖) := by
    apply hkernel.congr
    filter_upwards with v
    congr 3
  have hNpos : (0 : ℝ) < N.value := by exact_mod_cast N.positive
  have hHdiff : Differentiable ℂ (cglLemma62MellinTransform w) := fun s =>
    (cglLemma62_mellinTransform_analyticOnNhd w s (mem_univ s)).differentiableAt
  have hline : Continuous (fun v : ℝ => (σ : ℂ) + (v : ℂ) * I) := by fun_prop
  have hpow : Continuous (fun v : ℝ => (N.value : ℂ) ^
      ((σ : ℂ) + (v : ℂ) * I)) :=
    Continuous.const_cpow hline (Or.inl (Nat.cast_ne_zero.mpr (Nat.ne_of_gt N.positive)))
  have hLmeas : AEStronglyMeasurable (fun v : ℝ =>
      DirichletCharacter.LFunctionTrivChar Q.value
        ((σ : ℂ) + (v : ℂ) * I - (t : ℂ) * I)) := by
    let zline : ℝ → ℂ := fun v => (σ : ℂ) + (v : ℂ) * I - (t : ℂ) * I
    have hzline : Continuous zline := by
      dsimp [zline]
      fun_prop
    have hzeta : Continuous (fun v : ℝ => riemannZeta (zline v)) := by
      rw [continuous_iff_continuousAt]
      intro v
      apply ContinuousAt.comp _ hzline.continuousAt
      apply (differentiableAt_riemannZeta ?_).continuousAt
      intro h
      have hre := congrArg Complex.re h
      dsimp [zline] at hre
      simp at hre
      exact hσ (by linarith)
    have heuler : Continuous (fun v : ℝ =>
        ∏ p ∈ Q.value.primeFactors, (1 - (p : ℂ) ^ (-zline v))) := by
      apply continuous_finsetProd
      intro p hp
      letI : NeZero p := ⟨(Nat.prime_of_mem_primeFactors hp).ne_zero⟩
      fun_prop
    apply (heuler.mul hzeta).aestronglyMeasurable.congr
    filter_upwards with v
    have hne : zline v ≠ 1 := by
      intro h
      have hre := congrArg Complex.re h
      dsimp [zline] at hre
      simp at hre
      exact hσ (by linarith)
    symm
    exact DirichletCharacter.LFunctionTrivChar_eq_mul_riemannZeta hne
  have hmeas : AEStronglyMeasurable (fun v : ℝ =>
      cglLemma62PrincipalContourIntegrand w N Q t ((σ : ℂ) + (v : ℂ) * I)) := by
    unfold cglLemma62PrincipalContourIntegrand
    exact ((hHdiff.continuous.comp hline).mul hpow).aestronglyMeasurable.mul hLmeas
  refine Integrable.mono' (hkernel'.const_mul ((N.value : ℝ) ^ σ * E * (1 + |t|) ^ n)) hmeas ?_
  filter_upwards with v
  have hL : ‖DirichletCharacter.LFunctionTrivChar Q.value
      (((σ : ℂ) + (v : ℂ) * I) - (t : ℂ) * I)‖ ≤
      E * (1 + |v - t|) ^ n := by
    convert hLbound (v - t) using 1
    push_cast
    ring
  have hshift := cglLemma62_principal_shifted_weight_le t v n
  have hL' : ‖DirichletCharacter.LFunctionTrivChar Q.value
      (((σ : ℂ) + (v : ℂ) * I) - (t : ℂ) * I)‖ ≤
      E * (1 + |t|) ^ n * (1 + |v|) ^ n := by
    calc
      _ ≤ E * (1 + |v - t|) ^ n := hL
      _ ≤ E * ((1 + |t|) ^ n * (1 + |v|) ^ n) :=
        mul_le_mul_of_nonneg_left hshift hE.le
      _ = _ := by ring
  change ‖Hline v * (N.value : ℂ) ^ ((σ : ℂ) + (v : ℂ) * I) *
      DirichletCharacter.LFunctionTrivChar Q.value
        (((σ : ℂ) + (v : ℂ) * I - (t : ℂ) * I))‖ ≤ _
  have hNcast : (N.value : ℂ) = ((N.value : ℝ) : ℂ) := by norm_cast
  rw [norm_mul, norm_mul, hNcast,
    Complex.norm_cpow_eq_rpow_re_of_pos hNpos]
  have hre : ((σ : ℂ) + (v : ℂ) * I).re = σ := by simp
  rw [hre]
  calc
    ‖Hline v‖ * (N.value : ℝ) ^ σ *
        ‖DirichletCharacter.LFunctionTrivChar Q.value
          (((σ : ℂ) + (v : ℂ) * I - (t : ℂ) * I))‖ ≤
      ‖Hline v‖ * (N.value : ℝ) ^ σ *
        (E * (1 + |t|) ^ n * (1 + |v|) ^ n) := by
          refine mul_le_mul_of_nonneg_left hL' ?_
          positivity
    _ = ((N.value : ℝ) ^ σ * E * (1 + |t|) ^ n) *
        ((1 + |v|) ^ n * ‖Hline v‖) := by ring

/-- The principal CGL integrand is absolutely integrable on the shifted left
vertical edge. -/
theorem cglLemma62_principalContourIntegrand_left_integrable
    (w : CGLRealSmoothBump) (N : CGLPositiveLength) (Q : CGLPositiveModulus) (t : ℝ) :
    Integrable (fun v : ℝ => cglLemma62PrincipalContourIntegrand w N Q t
      ((-1 : ℂ) + (v : ℂ) * I)) := by
  simpa using cglLemma62_principalContourIntegrand_vertical_integrable_at w N Q t (-1)
    (by norm_num) (by norm_num)

/-- The principal CGL integrand is absolutely integrable on the initial right
vertical edge. -/
theorem cglLemma62_principalContourIntegrand_right_integrable
    (w : CGLRealSmoothBump) (N : CGLPositiveLength) (Q : CGLPositiveModulus) (t : ℝ) :
    Integrable (fun v : ℝ => cglLemma62PrincipalContourIntegrand w N Q t
      ((2 : ℂ) + (v : ℂ) * I)) := by
  simpa using cglLemma62_principalContourIntegrand_vertical_integrable_at w N Q t 2
    (by norm_num) (by norm_num)

end RHTower
