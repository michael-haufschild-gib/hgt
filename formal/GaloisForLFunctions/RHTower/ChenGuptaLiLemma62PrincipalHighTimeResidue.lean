import GaloisForLFunctions.RHTower.ChenGuptaLiLemma62PrincipalReflection
import GaloisForLFunctions.RHTower.ChenGuptaLiLemma62LargeTimeSourceRegime

/-!
# Chen--Gupta--Li Lemma 6.2: principal high-time residue

The principal residue crossed in CGL's first contour shift is negligible in
the source high-time regime.  This module packages the source's height
separation as certified data, uses the already closed arbitrary-order Mellin
decay, and proves the paper's `O(X⁻¹⁰⁰)` residue saving without a caller
premise.
-/

open Complex MeasureTheory Filter Set Asymptotics
open scoped Topology BigOperators

namespace RHTower

noncomputable section

/-- The principal branch's character-independent portion of CGL's high-time
source data.  Its lower ordinate separation is the exact datum used to make
the explicitly crossed residue negligible. -/
structure CGLLemma62PrincipalHighTimeSourceRegime
    (N : CGLPositiveLength) (Q : CGLPositiveModulus) (t : ℝ) where
  base : ℝ
  base_one : 1 ≤ base
  epsilon : ℝ
  epsilon_pos : 0 < epsilon
  residue_separated : 2 + base ^ (epsilon / 2) ≤ |t|

/-- The existing nonprincipal large-time packet supplies the same principal
high-time scale at its ambient modulus. -/
def CGLLemma62LargeTimeSourceRegime.toPrincipalHighTimeSourceRegime
    {B : CGLLemma62InducedCharacter} {N : CGLPositiveLength} {t : ℝ}
    (S : CGLLemma62LargeTimeSourceRegime B N t) :
    CGLLemma62PrincipalHighTimeSourceRegime N B.ambient t where
  base := S.base
  base_one := S.base_one
  epsilon := S.epsilon
  epsilon_pos := S.epsilon_pos
  residue_separated := S.truncation_separated

/-- A closed Mellin-decay order sufficient to turn the source high-time
separation into an `X⁻¹⁰⁰` principal-residue saving. -/
noncomputable def CGLLemma62PrincipalHighTimeSourceRegime.residueDecayRate
    {N : CGLPositiveLength} {Q : CGLPositiveModulus} {t : ℝ}
    (S : CGLLemma62PrincipalHighTimeSourceRegime N Q t) : ℕ :=
  Nat.ceil (200 / S.epsilon)

private theorem cglLemma62_principal_residueDecayRate_exponent_le
    {N : CGLPositiveLength} {Q : CGLPositiveModulus} {t : ℝ}
    (S : CGLLemma62PrincipalHighTimeSourceRegime N Q t) :
    (S.epsilon / 2) * (-(S.residueDecayRate : ℝ)) ≤ -100 := by
  have hceil : 200 / S.epsilon ≤ (S.residueDecayRate : ℝ) := Nat.le_ceil _
  have heps : 0 < S.epsilon := S.epsilon_pos
  have hmul := mul_le_mul_of_nonneg_left hceil heps.le
  have hdiv : S.epsilon * (200 / S.epsilon) = 200 := by field_simp
  rw [hdiv] at hmul
  nlinarith

private theorem cglLemma62_principal_residue_radius_le_abs
    {N : CGLPositiveLength} {Q : CGLPositiveModulus} {t : ℝ}
    (S : CGLLemma62PrincipalHighTimeSourceRegime N Q t) :
    S.base ^ (S.epsilon / 2) ≤ |t| := by
  linarith [S.residue_separated]

private theorem cglLemma62_principal_residue_inverse_power_le
    {N : CGLPositiveLength} {Q : CGLPositiveModulus} {t : ℝ}
    (S : CGLLemma62PrincipalHighTimeSourceRegime N Q t) :
    |t| ^ (-(S.residueDecayRate : ℝ)) ≤ S.base ^ (-100 : ℝ) := by
  have hbase : 0 ≤ S.base := le_trans zero_le_one S.base_one
  have hradius : S.base ^ (S.epsilon / 2) ≤ |t| :=
    cglLemma62_principal_residue_radius_le_abs S
  have hbasepos : 0 < S.base := lt_of_lt_of_le zero_lt_one S.base_one
  have hradiuspos : 0 < S.base ^ (S.epsilon / 2) :=
    Real.rpow_pos_of_pos hbasepos _
  have hleft : |t| ^ (-(S.residueDecayRate : ℝ)) ≤
      (S.base ^ (S.epsilon / 2)) ^ (-(S.residueDecayRate : ℝ)) := by
    have hrate : 0 ≤ (S.residueDecayRate : ℝ) := Nat.cast_nonneg _
    exact Real.rpow_le_rpow_of_nonpos hradiuspos hradius (neg_nonpos.mpr hrate)
  calc
    |t| ^ (-(S.residueDecayRate : ℝ)) ≤
        (S.base ^ (S.epsilon / 2)) ^ (-(S.residueDecayRate : ℝ)) := hleft
    _ = S.base ^ ((S.epsilon / 2) * (-(S.residueDecayRate : ℝ))) := by
      rw [← Real.rpow_mul hbase]
    _ ≤ S.base ^ (-100 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le S.base_one
        (cglLemma62_principal_residueDecayRate_exponent_le S)

/-- A finite, height-independent Euler-product budget for the principal
residue coefficient. -/
noncomputable def cglLemma62PrincipalResidueEulerBudget (Q : CGLPositiveModulus) : ℝ :=
  ∏ p ∈ Q.value.primeFactors, (1 + (p : ℝ))

private theorem cglLemma62_principal_residueEuler_norm_le (Q : CGLPositiveModulus) :
    ‖∏ p ∈ Q.value.primeFactors, (1 - (p : ℂ)⁻¹)‖ ≤
      cglLemma62PrincipalResidueEulerBudget Q := by
  rw [norm_prod]
  refine Finset.prod_le_prod (fun p hp => norm_nonneg _) ?_
  intro p hp
  have hpprime : p.Prime := Nat.prime_of_mem_primeFactors hp
  have hpone : (1 : ℝ) ≤ p := by exact_mod_cast hpprime.one_le
  calc
    ‖1 - (p : ℂ)⁻¹‖ ≤ ‖(1 : ℂ)‖ + ‖(p : ℂ)⁻¹‖ := norm_sub_le _ _
    _ = 1 + (p : ℝ)⁻¹ := by rw [norm_one, norm_inv, norm_natCast]
    _ ≤ 1 + 1 := by
      have hinv : (p : ℝ)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hpone
      linarith
    _ ≤ 1 + (p : ℝ) := by linarith

private theorem cglLemma62_principal_residueEulerBudget_nonneg (Q : CGLPositiveModulus) :
    0 ≤ cglLemma62PrincipalResidueEulerBudget Q := by
  unfold cglLemma62PrincipalResidueEulerBudget
  positivity

/-- CGL's explicit principal residue is `O(X⁻¹⁰⁰)` in the certified
large-time branch.  The internally constructed constant is independent of
the source height and ordinate. -/
theorem cglLemma62_principal_highTime_residue_bound
    {N : CGLPositiveLength} {Q : CGLPositiveModulus} {t : ℝ}
    (S : CGLLemma62PrincipalHighTimeSourceRegime N Q t) (w : CGLRealSmoothBump) :
    ∃ C : ℝ, 0 ≤ C ∧
      ‖cglLemma62PrincipalResidueCoefficient w N Q t‖ ≤ C * S.base ^ (-100 : ℝ) := by
  let K : ℝ := cglLogFourierAmplitudeAllOrderBudget w.toCGLSmoothBump S.residueDecayRate
  let C : ℝ := (N.value : ℝ) * cglLemma62PrincipalResidueEulerBudget Q * K
  have hbudget : 0 ≤ K := by
    exact le_trans (by positivity) (cglLemma62_mellinTransform_one_add_it_rapidDecay
      w S.residueDecayRate 0)
  have hN : 0 ≤ (N.value : ℝ) := by positivity
  have hE := cglLemma62_principal_residueEulerBudget_nonneg Q
  have hC : 0 ≤ C := by
    dsimp [C]
    exact mul_nonneg (mul_nonneg hN hE) hbudget
  have hbasepos : 0 < S.base := lt_of_lt_of_le zero_lt_one S.base_one
  have hradiuspos : 0 < S.base ^ (S.epsilon / 2) :=
    Real.rpow_pos_of_pos hbasepos _
  have hradius : S.base ^ (S.epsilon / 2) ≤ |t| :=
    cglLemma62_principal_residue_radius_le_abs S
  have habspos : 0 < |t| := lt_of_lt_of_le hradiuspos hradius
  have hrapid : ‖cglLemma62MellinTransform w ((1 : ℂ) + (t : ℂ) * I)‖ ≤
      K * |t| ^ (-(S.residueDecayRate : ℝ)) := by
    have h := cglLemma62_mellinTransform_one_add_it_rapidDecay w S.residueDecayRate t
    have hdiv : ‖cglLemma62MellinTransform w ((1 : ℂ) + (t : ℂ) * I)‖ ≤
        K / |t| ^ S.residueDecayRate := by
      apply (le_div_iff₀ (pow_pos habspos _)).mpr
      simpa [K, mul_comm] using h
    calc
      _ ≤ K / |t| ^ S.residueDecayRate := hdiv
      _ = K * |t| ^ (-(S.residueDecayRate : ℝ)) := by
        rw [Real.rpow_neg (abs_nonneg t), Real.rpow_natCast]
        ring
  have hpower := cglLemma62_principal_residue_inverse_power_le S
  have hNnorm : ‖(N.value : ℂ) ^ cglLemma62PrincipalPole t‖ = (N.value : ℝ) := by
    change ‖((N.value : ℝ) : ℂ) ^ cglLemma62PrincipalPole t‖ = (N.value : ℝ)
    rw [Complex.norm_cpow_eq_rpow_re_of_pos (by exact_mod_cast N.positive)]
    simp [cglLemma62PrincipalPole]
  refine ⟨C, hC, ?_⟩
  unfold cglLemma62PrincipalResidueCoefficient
  rw [norm_mul, norm_mul, hNnorm]
  calc
    ‖cglLemma62MellinTransform w (cglLemma62PrincipalPole t)‖ * (N.value : ℝ) *
        ‖∏ p ∈ Q.value.primeFactors, (1 - (p : ℂ)⁻¹)‖ ≤
      (K * |t| ^ (-(S.residueDecayRate : ℝ))) * (N.value : ℝ) *
        cglLemma62PrincipalResidueEulerBudget Q := by
          have hpole : cglLemma62PrincipalPole t = (1 : ℂ) + (t : ℂ) * I := rfl
          rw [hpole]
          gcongr
          exact cglLemma62_principal_residueEuler_norm_le Q
    _ = C * |t| ^ (-(S.residueDecayRate : ℝ)) := by
      dsimp [C]
      ring
    _ ≤ C * S.base ^ (-100 : ℝ) :=
      mul_le_mul_of_nonneg_left hpower hC

end

end RHTower
