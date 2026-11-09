import GaloisForLFunctions.ArithmeticPositiveDuality.HarmonicZeroPacketsForcePositiveAnnihilatorMass
import GaloisForLFunctions.HTGeometry.MontgomeryVaughanBandPerturbation
import GaloisForLFunctions.HTGeometry.SteinhausRotationInvariance

/-!
# Odd ordinate relations force logarithmic frequency cost

An odd collection of almost cancelling phases has product near minus one.
An approximate additive relation among its ordinates instead puts that product
near one. Positive phase energy bounds the resulting discrepancy by the tail
mass excess; the relation error is paid by the first logarithmic moment.
-/

noncomputable section
set_option autoImplicit false

open Complex Finset
open scoped NNReal

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PositiveAnnihilator

/-- First logarithmic moment of the positive nonconstant coefficient mass. -/
def dirichletTailLogMoment (P : MvPolynomial (Fin 2) ℝ≥0) (β : ℝ) : ℝ :=
  ∑ d ∈ P.support.erase 0, ((P.coeff d : ℝ≥0) : ℝ) *
    Real.exp (-monomialLog d * β) * monomialLog d

private theorem unit_product_defect {ι : Type*} (S : Finset ι) (u : ι → ℂ)
    (hu : ∀ i ∈ S, ‖u i‖ = 1) :
    ‖(∏ i ∈ S, u i) - (-1 : ℂ) ^ S.card‖ ≤ ∑ i ∈ S, ‖u i + 1‖ := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | @insert a S ha ih =>
    have hua := hu a (Finset.mem_insert_self a S)
    have hS := ih (fun i hi => hu i (Finset.mem_insert_of_mem hi))
    rw [Finset.prod_insert ha, Finset.card_insert_of_notMem ha, Finset.sum_insert ha]
    have he : u a * (∏ i ∈ S, u i) - (-1 : ℂ) ^ (S.card + 1) =
        u a * ((∏ i ∈ S, u i) - (-1 : ℂ) ^ S.card) +
          (u a + 1) * (-1 : ℂ) ^ S.card := by rw [pow_succ]; ring
    rw [he]
    calc
      _ ≤ ‖u a * ((∏ i ∈ S, u i) - (-1 : ℂ) ^ S.card)‖ +
          ‖(u a + 1) * (-1 : ℂ) ^ S.card‖ := norm_add_le _ _
      _ = ‖(∏ i ∈ S, u i) - (-1 : ℂ) ^ S.card‖ + ‖u a + 1‖ := by
        simp only [norm_mul, hua, one_mul, norm_pow, norm_neg, norm_one, one_pow, mul_one]
      _ ≤ _ := by linarith only [hS]

private theorem prod_monomialPhase {ι : Type*} (S : Finset ι) (γ : ι → ℝ)
    (d : Fin 2 →₀ ℕ) :
    (∏ j ∈ S, monomialPhase (γ j) d) = monomialPhase (∑ j ∈ S, γ j) d := by
  classical
  induction S using Finset.induction_on with
  | empty => simp [monomialPhase]
  | @insert a S ha ih =>
    rw [Finset.prod_insert ha, Finset.sum_insert ha, ih]
    unfold monomialPhase
    rw [← Complex.exp_add]
    congr 1
    rw [Complex.ofReal_add]
    ring

/-- Odd ordinate relations obstruct simultaneous concentration at the cancelling phase. -/
theorem odd_ordinate_phase_defect {q : ℕ} (hq : Odd q) (γ : Fin q → ℝ)
    (d : Fin 2 →₀ ℕ) (hd : d ≠ 0) :
    2 ≤ monomialLog d * |∑ j, γ j| + ∑ j, ‖monomialPhase (γ j) d + 1‖ := by
  have hp := unit_product_defect Finset.univ (fun j => monomialPhase (γ j) d)
    (fun j _ => norm_monomialPhase (γ j) d)
  rw [Finset.card_univ, Fintype.card_fin, hq.neg_one_pow, sub_neg_eq_add,
    prod_monomialPhase] at hp
  have hL : 0 ≤ monomialLog d :=
    (Real.log_pos (by norm_num : (1 : ℝ) < 2)).le.trans (log_two_le_monomialLog d hd)
  have he := _root_.HTGeometry.norm_exp_ofReal_mul_I_sub_one_le
    (-monomialLog d * ∑ j, γ j)
  have hc : Complex.exp (((-monomialLog d * ∑ j, γ j : ℝ) : ℂ) * I) =
      monomialPhase (∑ j, γ j) d := by
    simp only [monomialPhase, Complex.ofReal_mul, Complex.ofReal_neg]
  rw [hc, abs_mul, abs_neg, abs_of_nonneg hL] at he
  have ht := norm_sub_le (monomialPhase (∑ j, γ j) d + 1)
    (monomialPhase (∑ j, γ j) d - 1)
  have hid : monomialPhase (∑ j, γ j) d + 1 -
      (monomialPhase (∑ j, γ j) d - 1) = (2 : ℂ) := by ring
  rw [hid] at ht
  norm_num only [norm_ofNat] at ht
  linarith only [ht, hp, he]

private theorem eval_re_phase {P : MvPolynomial (Fin 2) ℝ≥0}
    (hP : MvPolynomial.constantCoeff P = 1) (β γ : ℝ) :
    (dirichletEval (harmonicPacketPoint β γ 1) P).re = 1 +
      ∑ d ∈ P.support.erase 0, ((P.coeff d : ℝ≥0) : ℝ) *
        Real.exp (-monomialLog d * β) * (monomialPhase γ d).re := by
  rw [dirichletEval_eq_one_add_tail hP, Complex.add_re, Complex.one_re]
  congr 1
  change Complex.reAddGroupHom (∑ d ∈ P.support.erase 0,
    (((P.coeff d : ℝ≥0) : ℝ) : ℂ) *
      Complex.exp (-(monomialLog d : ℂ) * harmonicPacketPoint β γ 1)) = _
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro d _
  change ((((P.coeff d : ℝ≥0) : ℝ) : ℂ) *
    Complex.exp (-(monomialLog d : ℂ) * harmonicPacketPoint β γ 1)).re = _
  simp only [harmonicPacketPoint, monomialPhase, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, sub_zero, Complex.exp_re, Complex.neg_re,
    Complex.neg_im, Complex.mul_im, Complex.add_re, Complex.add_im, Nat.cast_one,
    Complex.I_re, Complex.I_im, mul_zero, add_zero,
    zero_add, mul_one, one_mul, neg_zero, Real.exp_zero]
  ring

private theorem unit_phase_sq_defect (γ : ℝ) (d : Fin 2 →₀ ℕ) :
    ‖monomialPhase γ d + 1‖ ^ 2 = 2 * (1 + (monomialPhase γ d).re) := by
  have hu := Complex.normSq_eq_norm_sq (monomialPhase γ d)
  rw [norm_monomialPhase, one_pow] at hu
  rw [← Complex.normSq_eq_norm_sq]
  simp only [Complex.normSq_apply, Complex.add_re, Complex.add_im, Complex.one_re,
    Complex.one_im, add_zero] at hu ⊢
  nlinarith only [hu]

/-- Exact squared defect at an arbitrary target, including nonzero evaluation error. -/
theorem ordinate_phase_energy {P : MvPolynomial (Fin 2) ℝ≥0}
    (hP : MvPolynomial.constantCoeff P = 1) (β γ : ℝ) :
    (∑ d ∈ P.support.erase 0, ((P.coeff d : ℝ≥0) : ℝ) * Real.exp (-monomialLog d * β) *
      ‖monomialPhase γ d + 1‖ ^ 2) =
        2 * (dirichletTailMass P β - 1 +
          (dirichletEval (harmonicPacketPoint β γ 1) P).re) := by
  rw [eval_re_phase hP]
  simp_rw [unit_phase_sq_defect]
  have hs : (∑ d ∈ P.support.erase 0, ((P.coeff d : ℝ≥0) : ℝ) * Real.exp (-monomialLog d * β) *
      (2 * (1 + (monomialPhase γ d).re))) =
      ∑ d ∈ P.support.erase 0,
        (2 * (((P.coeff d : ℝ≥0) : ℝ) * Real.exp (-monomialLog d * β)) +
          2 * (((P.coeff d : ℝ≥0) : ℝ) * Real.exp (-monomialLog d * β) *
            (monomialPhase γ d).re)) := by
    apply Finset.sum_congr rfl
    intro d _
    ring
  rw [hs, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
  unfold dirichletTailMass
  ring

private theorem ordinate_first_defect_le {P : MvPolynomial (Fin 2) ℝ≥0}
    (hP : MvPolynomial.constantCoeff P = 1) (β γ ε : ℝ)
    (he : ‖dirichletEval (harmonicPacketPoint β γ 1) P‖ ≤ ε) :
    (∑ d ∈ P.support.erase 0, ((P.coeff d : ℝ≥0) : ℝ) * Real.exp (-monomialLog d * β) *
      ‖monomialPhase γ d + 1‖) ≤
        Real.sqrt (2 * dirichletTailMass P β * (dirichletTailMass P β - 1 + ε)) := by
  have hcs := GaloisForLFunctions.HTGeometry.sq_sum_weighted_le (P.support.erase 0)
    (fun d => ((P.coeff d : ℝ≥0) : ℝ) * Real.exp (-monomialLog d * β))
    (fun d => ‖monomialPhase γ d + 1‖)
    (fun d _ => mul_nonneg (P.coeff d).coe_nonneg (Real.exp_pos _).le)
  change _ ≤ dirichletTailMass P β * _ at hcs
  rw [ordinate_phase_energy hP] at hcs
  have hr := (Complex.re_le_norm _).trans he
  have hm := mul_le_mul_of_nonneg_left
    (show 2 * (dirichletTailMass P β - 1 +
      (dirichletEval (harmonicPacketPoint β γ 1) P).re) ≤
        2 * (dirichletTailMass P β - 1 + ε) by linarith only [hr])
    (dirichletTailMass_nonneg P β)
  apply Real.le_sqrt_of_sq_le
  nlinarith only [hcs, hm]

/-- Joint accuracy at an odd list of ordinates costs mass excess or logarithmic frequency.
Signed repetitions allow this bound to test every odd integer relation. -/
theorem odd_ordinate_accuracy_frequency_tradeoff {P : MvPolynomial (Fin 2) ℝ≥0}
    (hP : MvPolynomial.constantCoeff P = 1) {q : ℕ} (hq : Odd q)
    (β ε : ℝ) (γ : Fin q → ℝ)
    (he : ∀ j, ‖dirichletEval (harmonicPacketPoint β (γ j) 1) P‖ ≤ ε) :
    2 * dirichletTailMass P β ≤ |∑ j, γ j| * dirichletTailLogMoment P β +
      (q : ℝ) * Real.sqrt (2 * dirichletTailMass P β * (dirichletTailMass P β - 1 + ε)) := by
  let w : (Fin 2 →₀ ℕ) → ℝ := fun d => ((P.coeff d : ℝ≥0) : ℝ) * Real.exp (-monomialLog d * β)
  have hw (d : Fin 2 →₀ ℕ) : 0 ≤ w d :=
    mul_nonneg (P.coeff d).coe_nonneg (Real.exp_pos _).le
  have hfirst : (∑ d ∈ P.support.erase 0, w d * (monomialLog d * |∑ j, γ j|)) =
      |∑ j, γ j| * dirichletTailLogMoment P β := by
    simp only [← mul_assoc, ← Finset.sum_mul, dirichletTailLogMoment, w]
    ring
  have hsecond : (∑ d ∈ P.support.erase 0, w d * ∑ j, ‖monomialPhase (γ j) d + 1‖) =
      ∑ j, ∑ d ∈ P.support.erase 0, w d * ‖monomialPhase (γ j) d + 1‖ := by
    simp_rw [Finset.mul_sum]
    exact Finset.sum_comm
  calc
    2 * dirichletTailMass P β = ∑ d ∈ P.support.erase 0, w d * 2 := by
      rw [← Finset.sum_mul]
      change 2 * dirichletTailMass P β = dirichletTailMass P β * 2
      ring
    _ ≤ ∑ d ∈ P.support.erase 0,
        w d * (monomialLog d * |∑ j, γ j| + ∑ j, ‖monomialPhase (γ j) d + 1‖) := by
      apply Finset.sum_le_sum
      intro d hd
      exact mul_le_mul_of_nonneg_left
        (odd_ordinate_phase_defect hq γ d (Finset.mem_erase.mp hd).1) (hw d)
    _ = |∑ j, γ j| * dirichletTailLogMoment P β +
        ∑ j, ∑ d ∈ P.support.erase 0, w d * ‖monomialPhase (γ j) d + 1‖ := by
      simp_rw [mul_add]
      rw [Finset.sum_add_distrib, hfirst, hsecond]
    _ ≤ |∑ j, γ j| * dirichletTailLogMoment P β +
        ∑ _j : Fin q, Real.sqrt
          (2 * dirichletTailMass P β * (dirichletTailMass P β - 1 + ε)) := by
      exact add_le_add le_rfl
        (Finset.sum_le_sum fun j _ => ordinate_first_defect_le hP β (γ j) ε (he j))
    _ = _ := by simp

/-- An exact odd additive relation forces a bandwidth-independent positive mass gap. -/
theorem odd_ordinate_zero_relation_mass_gap {P : MvPolynomial (Fin 2) ℝ≥0}
    (hP : MvPolynomial.constantCoeff P = 1) {q : ℕ} (hq : Odd q)
    (β : ℝ) (γ : Fin q → ℝ) (hs : ∑ j, γ j = 0)
    (hz : ∀ j, dirichletEval (harmonicPacketPoint β (γ j) 1) P = 0) :
    (q ^ 2 - 2 : ℝ) * dirichletTailMass P β ≥ (q : ℝ) ^ 2 := by
  have hm := one_le_dirichletTailMass_of_zero hP (hz ⟨0, hq.pos⟩)
  have hre : (harmonicPacketPoint β (γ ⟨0, hq.pos⟩) 1).re = β := by
    simp [harmonicPacketPoint]
  rw [hre] at hm
  have h := odd_ordinate_accuracy_frequency_tradeoff hP hq β 0 γ
    (fun j => by rw [hz j, norm_zero])
  rw [hs, abs_zero, zero_mul, zero_add, add_zero] at h
  have hH : 0 < dirichletTailMass P β := lt_of_lt_of_le (by norm_num) hm
  have hn : 0 ≤ 2 * dirichletTailMass P β * (dirichletTailMass P β - 1) :=
    mul_nonneg (by positivity) (sub_nonneg.mpr hm)
  have hsq := (sq_le_sq₀ (by positivity : 0 ≤ 2 * dirichletTailMass P β)
    (by positivity : 0 ≤ (q : ℝ) * Real.sqrt
      (2 * dirichletTailMass P β * (dirichletTailMass P β - 1)))).mpr h
  simp only [mul_pow, Real.sq_sqrt hn] at hsq
  have hc : 2 * dirichletTailMass P β *
      ((q ^ 2 - 2 : ℝ) * dirichletTailMass P β - (q : ℝ) ^ 2) ≥ 0 := by
    nlinarith only [hsq]
  exact sub_nonneg.mp (nonneg_of_mul_nonneg_right hc
    (by positivity : 0 < 2 * dirichletTailMass P β))

/-- Near-unit annihilation forces inverse-relation-error growth of mean logarithmic frequency. -/
theorem odd_ordinate_near_unit_frequency_cost {P : MvPolynomial (Fin 2) ℝ≥0}
    (hP : MvPolynomial.constantCoeff P = 1) {q : ℕ} (hq : Odd q)
    (β : ℝ) (γ : Fin q → ℝ)
    (hz : ∀ j, dirichletEval (harmonicPacketPoint β (γ j) 1) P = 0)
    (hnear : 2 * (q : ℝ) ^ 2 * (dirichletTailMass P β - 1) ≤ 1) :
    dirichletTailMass P β ≤ |∑ j, γ j| * dirichletTailLogMoment P β := by
  have hm := one_le_dirichletTailMass_of_zero hP (hz ⟨0, hq.pos⟩)
  have hre : (harmonicPacketPoint β (γ ⟨0, hq.pos⟩) 1).re = β := by
    simp [harmonicPacketPoint]
  rw [hre] at hm
  have hH := dirichletTailMass_nonneg P β
  have hn : 0 ≤ 2 * dirichletTailMass P β * (dirichletTailMass P β - 1) :=
    mul_nonneg (by positivity) (sub_nonneg.mpr hm)
  have hb := mul_le_mul_of_nonneg_right hnear hH
  have hsq : ((q : ℝ) * Real.sqrt
      (2 * dirichletTailMass P β * (dirichletTailMass P β - 1))) ^ 2 ≤
        dirichletTailMass P β ^ 2 := by
    rw [mul_pow, Real.sq_sqrt hn]
    nlinarith only [hb, mul_nonneg hH (sub_nonneg.mpr hm)]
  have hsmall := (sq_le_sq₀ (by positivity : 0 ≤ (q : ℝ) * Real.sqrt
    (2 * dirichletTailMass P β * (dirichletTailMass P β - 1))) hH).mp hsq
  have h := odd_ordinate_accuracy_frequency_tradeoff hP hq β 0 γ
    (fun j => by rw [hz j, norm_zero])
  rw [add_zero] at h
  linarith only [h, hsmall]

/-- An exact odd zero-sum relation excludes unit tail mass. -/
theorem one_lt_mass_of_odd_zero_relation {P : MvPolynomial (Fin 2) ℝ≥0}
    (hP : MvPolynomial.constantCoeff P = 1) {q : ℕ} (hq : Odd q)
    (β : ℝ) (γ : Fin q → ℝ) (hs : ∑ j, γ j = 0)
    (hz : ∀ j, dirichletEval (harmonicPacketPoint β (γ j) 1) P = 0) :
    1 < dirichletTailMass P β := by
  have h := odd_ordinate_zero_relation_mass_gap hP hq β γ hs hz
  have hm := one_le_dirichletTailMass_of_zero hP (hz ⟨0, hq.pos⟩)
  have hre : (harmonicPacketPoint β (γ ⟨0, hq.pos⟩) 1).re = β := by
    simp [harmonicPacketPoint]
  rw [hre] at hm
  by_contra hn
  have he : dirichletTailMass P β = 1 := le_antisymm (not_lt.mp hn) hm
  rw [he, mul_one] at h
  linarith only [h]

#print axioms odd_ordinate_accuracy_frequency_tradeoff
#print axioms odd_ordinate_zero_relation_mass_gap
#print axioms odd_ordinate_near_unit_frequency_cost
#print axioms one_lt_mass_of_odd_zero_relation

end GaloisForLFunctions.ArithmeticPositiveDuality.PositiveAnnihilator
