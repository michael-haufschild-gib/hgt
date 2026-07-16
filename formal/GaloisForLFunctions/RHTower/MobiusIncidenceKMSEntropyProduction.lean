import GaloisForLFunctions.HTGeometry.ThermodynamicAffinityHolonomy
import GaloisForLFunctions.RHTower.MobiusCriticalFisherSteinContact
import Mathlib.Tactic

/-!
# Finite Möbius-incidence KMS entropy production

This module realizes every finite positive-integer incidence packet as an exact Hermitian KMS
entropy-production system.  With Gibbs energy `ε log d`, inverse temperature `σ / ε`, and the
canonical symmetric edge amplitude, each transition intensity is

`4 ε pₐ p_b |log dₐ - log d_b|`.

Consequently the total entropy production is exactly the finite Gini/incidence energy, and its
passive response is the corresponding finite gap resolvent.  The final section also records the
universal critical gap density `2 |x| exp (-|x|)` and proves its total mass is exactly four.
-/

open scoped BigOperators

namespace RHTower

noncomputable section

def finiteIncidencePartition
    {α : Type*} [Fintype α] (sigma : ℝ) (d : α → ℕ) : ℝ :=
  ∑ i, (d i : ℝ) ^ (-sigma)

def finiteIncidenceProbability
    {α : Type*} [Fintype α] (sigma : ℝ) (d : α → ℕ) (i : α) : ℝ :=
  (d i : ℝ) ^ (-sigma) / finiteIncidencePartition sigma d

def finiteIncidenceEnergy
    {α : Type*} (epsilon : ℝ) (d : α → ℕ) (i : α) : ℝ :=
  epsilon * Real.log (d i)

def finiteIncidenceInverseTemperature (sigma epsilon : ℝ) : ℝ :=
  sigma / epsilon

theorem finiteIncidencePartition_pos
    {α : Type*} [Fintype α] [Nonempty α]
    {sigma : ℝ} {d : α → ℕ} (hd : ∀ i, 0 < d i) :
    0 < finiteIncidencePartition sigma d := by
  unfold finiteIncidencePartition
  exact Finset.sum_pos (fun i _ => Real.rpow_pos_of_pos (by exact_mod_cast hd i) _)
    Finset.univ_nonempty

theorem finiteIncidenceProbability_pos
    {α : Type*} [Fintype α] [Nonempty α]
    {sigma : ℝ} {d : α → ℕ} (hd : ∀ i, 0 < d i) (i : α) :
    0 < finiteIncidenceProbability sigma d i := by
  exact div_pos (Real.rpow_pos_of_pos (by exact_mod_cast hd i) _)
    (finiteIncidencePartition_pos hd)

theorem sum_finiteIncidenceProbability
    {α : Type*} [Fintype α] [Nonempty α]
    {sigma : ℝ} {d : α → ℕ} (hd : ∀ i, 0 < d i) :
    ∑ i, finiteIncidenceProbability sigma d i = 1 := by
  rw [show (∑ i, finiteIncidenceProbability sigma d i) =
      (∑ i, (d i : ℝ) ^ (-sigma)) / finiteIncidencePartition sigma d by
    simp only [finiteIncidenceProbability, Finset.sum_div]]
  exact div_self (ne_of_gt (finiteIncidencePartition_pos hd))

theorem exp_neg_inverseTemperature_mul_energy
    {α : Type*} {sigma epsilon : ℝ} (hsigma : 0 < sigma)
    (hepsilon : 0 < epsilon) {d : α → ℕ} (hd : ∀ i, 0 < d i) (i : α) :
    Real.exp (-(finiteIncidenceInverseTemperature sigma epsilon *
      finiteIncidenceEnergy epsilon d i)) =
      (d i : ℝ) ^ (-sigma) := by
  rw [Real.rpow_def_of_pos (by exact_mod_cast hd i)]
  unfold finiteIncidenceInverseTemperature finiteIncidenceEnergy
  congr 1
  field_simp [ne_of_gt hepsilon]
  ring

theorem finiteGibbsPartition_incidence
    {α : Type*} [Fintype α]
    {sigma epsilon : ℝ} (hsigma : 0 < sigma) (hepsilon : 0 < epsilon)
    {d : α → ℕ} (hd : ∀ i, 0 < d i) :
    _root_.HTGeometry.finiteGibbsPartition
        (finiteIncidenceInverseTemperature sigma epsilon)
        (finiteIncidenceEnergy epsilon d) =
      finiteIncidencePartition sigma d := by
  unfold _root_.HTGeometry.finiteGibbsPartition finiteIncidencePartition
  apply Finset.sum_congr rfl
  intro i hi
  exact exp_neg_inverseTemperature_mul_energy hsigma hepsilon hd i

theorem finiteGibbsStateWeight_incidence
    {α : Type*} [Fintype α] [Nonempty α]
    {sigma epsilon : ℝ} (hsigma : 0 < sigma) (hepsilon : 0 < epsilon)
    {d : α → ℕ} (hd : ∀ i, 0 < d i) (i : α) :
    _root_.HTGeometry.finiteGibbsStateWeight
        (finiteIncidenceInverseTemperature sigma epsilon)
        (finiteIncidenceEnergy epsilon d) i =
      finiteIncidenceProbability sigma d i := by
  rw [_root_.HTGeometry.finiteGibbsStateWeight,
    exp_neg_inverseTemperature_mul_energy hsigma hepsilon hd,
    finiteGibbsPartition_incidence hsigma hepsilon hd]
  rfl

theorem finiteIncidenceProbability_ne
    {α : Type*} [Fintype α] [Nonempty α]
    {sigma : ℝ} (hsigma : 0 < sigma) {d : α → ℕ}
    (hd : ∀ i, 0 < d i) (hinj : Function.Injective d)
    {a b : α} (hab : a ≠ b) :
    finiteIncidenceProbability sigma d a ≠
      finiteIncidenceProbability sigma d b := by
  have hdab : d a ≠ d b := fun h => hab (hinj h)
  have hpow : (d a : ℝ) ^ (-sigma) ≠ (d b : ℝ) ^ (-sigma) := by
    intro h
    have hcast : (d a : ℝ) = (d b : ℝ) :=
      (Real.strictAntiOn_rpow_Ioi_of_exponent_neg (neg_neg_of_pos hsigma)).injective
        (by exact_mod_cast hd a) (by exact_mod_cast hd b) h
    exact hdab (by exact_mod_cast hcast)
  unfold finiteIncidenceProbability
  exact (div_ne_div_iff_of_pos_right (finiteIncidencePartition_pos hd)).mpr hpow

def finiteIncidenceKMSAmplitude
    {α : Type*} [Fintype α]
    (sigma epsilon : ℝ) (d : α → ℕ) (a b : α) : ℂ :=
  if a = b then 0 else
    Real.sqrt
      (4 * epsilon * finiteIncidenceProbability sigma d a *
          finiteIncidenceProbability sigma d b /
        (sigma * |finiteIncidenceProbability sigma d b -
          finiteIncidenceProbability sigma d a|))

theorem finiteIncidenceKMSAmplitude_hermitian
    {α : Type*} [Fintype α]
    (sigma epsilon : ℝ) (d : α → ℕ) (a b : α) :
    finiteIncidenceKMSAmplitude sigma epsilon d b a =
      star (finiteIncidenceKMSAmplitude sigma epsilon d a b) := by
  by_cases hab : a = b
  · subst b
    simp [finiteIncidenceKMSAmplitude]
  · simp [finiteIncidenceKMSAmplitude, hab, Ne.symm hab, abs_sub_comm,
      mul_comm, mul_left_comm]

theorem finiteIncidenceKMSAmplitude_normSq
    {α : Type*} [Fintype α] [Nonempty α]
    {sigma epsilon : ℝ} (hsigma : 0 < sigma) (hepsilon : 0 < epsilon)
    {d : α → ℕ} (hd : ∀ i, 0 < d i) (hinj : Function.Injective d)
    {a b : α} (hab : a ≠ b) :
    Complex.normSq (finiteIncidenceKMSAmplitude sigma epsilon d a b) =
      4 * epsilon * finiteIncidenceProbability sigma d a *
          finiteIncidenceProbability sigma d b /
        (sigma * |finiteIncidenceProbability sigma d b -
          finiteIncidenceProbability sigma d a|) := by
  rw [finiteIncidenceKMSAmplitude, if_neg hab, Complex.normSq_ofReal,
    Real.sq_sqrt]
  positivity

theorem finiteIncidenceProbability_lt_iff
    {α : Type*} [Fintype α] [Nonempty α]
    {sigma : ℝ} (hsigma : 0 < sigma) {d : α → ℕ}
    (hd : ∀ i, 0 < d i) (a b : α) :
    finiteIncidenceProbability sigma d a <
        finiteIncidenceProbability sigma d b ↔
      d b < d a := by
  rw [finiteIncidenceProbability, finiteIncidenceProbability,
    div_lt_div_iff_of_pos_right (finiteIncidencePartition_pos hd)]
  have ha : 0 < (d a : ℝ) := by exact_mod_cast hd a
  have hb : 0 < (d b : ℝ) := by exact_mod_cast hd b
  rw [Real.rpow_lt_rpow_iff_of_neg ha hb (neg_neg_of_pos hsigma)]
  exact_mod_cast Iff.rfl

theorem mul_div_abs_eq_abs_of_pos_pos {x y : ℝ}
    (hx : 0 < x) (hy : 0 < y) :
    x * y / |x| = |y| := by
  rw [abs_of_pos hx, abs_of_pos hy]
  field_simp [hx.ne']

theorem mul_div_abs_eq_abs_of_neg_neg {x y : ℝ}
    (hx : x < 0) (hy : y < 0) :
    x * y / |x| = |y| := by
  rw [abs_of_neg hx, abs_of_neg hy]
  field_simp [hx.ne]
  ring

theorem finiteIncidence_gap_mul_logGap_div_abs
    {α : Type*} [Fintype α] [Nonempty α]
    {sigma : ℝ} (hsigma : 0 < sigma) {d : α → ℕ}
    (hd : ∀ i, 0 < d i) (hinj : Function.Injective d)
    {a b : α} (hab : a ≠ b) :
    (finiteIncidenceProbability sigma d b -
        finiteIncidenceProbability sigma d a) *
        (Real.log (d a) - Real.log (d b)) /
      |finiteIncidenceProbability sigma d b -
        finiteIncidenceProbability sigma d a| =
      |Real.log (d a) - Real.log (d b)| := by
  have hdab : d a ≠ d b := fun h => hab (hinj h)
  rcases lt_or_gt_of_ne hdab with hdalt | hdbla
  · have hp : finiteIncidenceProbability sigma d b <
        finiteIncidenceProbability sigma d a :=
      (finiteIncidenceProbability_lt_iff hsigma hd b a).2 hdalt
    have hlog : Real.log (d a) < Real.log (d b) :=
      Real.strictMonoOn_log (by exact_mod_cast hd a) (by exact_mod_cast hd b)
        (by exact_mod_cast hdalt)
    exact mul_div_abs_eq_abs_of_neg_neg (sub_neg.mpr hp) (sub_neg.mpr hlog)
  · have hp : finiteIncidenceProbability sigma d a <
        finiteIncidenceProbability sigma d b :=
      (finiteIncidenceProbability_lt_iff hsigma hd a b).2 hdbla
    have hlog : Real.log (d b) < Real.log (d a) :=
      Real.strictMonoOn_log (by exact_mod_cast hd b) (by exact_mod_cast hd a)
        (by exact_mod_cast hdbla)
    exact mul_div_abs_eq_abs_of_pos_pos (sub_pos.mpr hp) (sub_pos.mpr hlog)

theorem finiteKMSEntropyProductionTransitionIntensity_incidence
    {α : Type*} [Fintype α] [Nonempty α]
    {sigma epsilon : ℝ} (hsigma : 0 < sigma) (hepsilon : 0 < epsilon)
    {d : α → ℕ} (hd : ∀ i, 0 < d i) (hinj : Function.Injective d)
    (a b : α) :
    GaloisForLFunctions.HTGeometry.finiteKMSEntropyProductionTransitionIntensity
        (finiteIncidenceInverseTemperature sigma epsilon)
        (finiteIncidenceEnergy epsilon d)
        (finiteIncidenceKMSAmplitude sigma epsilon d) a b =
      4 * epsilon * finiteIncidenceProbability sigma d a *
        finiteIncidenceProbability sigma d b *
          |Real.log (d a) - Real.log (d b)| := by
  by_cases hab : a = b
  · subst b
    simp [finiteIncidenceKMSAmplitude]
  · rw [GaloisForLFunctions.HTGeometry.
      finiteKMSEntropyProductionTransitionIntensity_eq_beta_mul_dissipative
        _ _ _ (finiteIncidenceKMSAmplitude_hermitian sigma epsilon d),
      _root_.HTGeometry.
        finiteKMSDissipativeTransitionIntensity_eq_gap_mul_stateWeight_sub_mul_normSq,
      finiteGibbsStateWeight_incidence hsigma hepsilon hd,
      finiteGibbsStateWeight_incidence hsigma hepsilon hd,
      finiteIncidenceKMSAmplitude_normSq hsigma hepsilon hd hinj hab]
    unfold finiteIncidenceInverseTemperature finiteIncidenceEnergy
    have hgap := finiteIncidence_gap_mul_logGap_div_abs hsigma hd hinj hab
    field_simp [ne_of_gt hsigma, ne_of_gt hepsilon,
      finiteIncidenceProbability_ne hsigma hd hinj hab]
    field_simp [finiteIncidenceProbability_ne hsigma hd hinj hab] at hgap
    nlinarith

def finiteIncidenceGiniEnergy
    {α : Type*} [Fintype α]
    (sigma epsilon : ℝ) (d : α → ℕ) : ℝ :=
  4 * epsilon * ∑ a, ∑ b,
    finiteIncidenceProbability sigma d a *
      finiteIncidenceProbability sigma d b *
        |Real.log (d a) - Real.log (d b)|

theorem sum_finiteKMSEntropyProductionTransitionIntensity_incidence
    {α : Type*} [Fintype α] [Nonempty α]
    {sigma epsilon : ℝ} (hsigma : 0 < sigma) (hepsilon : 0 < epsilon)
    {d : α → ℕ} (hd : ∀ i, 0 < d i) (hinj : Function.Injective d) :
    (∑ a, ∑ b,
      GaloisForLFunctions.HTGeometry.finiteKMSEntropyProductionTransitionIntensity
        (finiteIncidenceInverseTemperature sigma epsilon)
        (finiteIncidenceEnergy epsilon d)
        (finiteIncidenceKMSAmplitude sigma epsilon d) a b) =
      finiteIncidenceGiniEnergy sigma epsilon d := by
  simp_rw [finiteKMSEntropyProductionTransitionIntensity_incidence
    hsigma hepsilon hd hinj]
  unfold finiteIncidenceGiniEnergy
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a ha
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro b hb
  ring

def finiteIncidenceKMSResponse
    {α : Type*} [Fintype α]
    (sigma epsilon : ℝ) (d : α → ℕ) (z : ℂ) : ℂ :=
  _root_.HTGeometry.finiteTransitionPassiveResponse
    (GaloisForLFunctions.HTGeometry.finiteKMSEntropyProductionTransitionIntensity
      (finiteIncidenceInverseTemperature sigma epsilon)
      (finiteIncidenceEnergy epsilon d)
      (finiteIncidenceKMSAmplitude sigma epsilon d))
    (finiteIncidenceEnergy epsilon d) z

theorem finiteIncidenceKMSResponse_eq
    {α : Type*} [Fintype α] [Nonempty α]
    {sigma epsilon : ℝ} (hsigma : 0 < sigma) (hepsilon : 0 < epsilon)
    {d : α → ℕ} (hd : ∀ i, 0 < d i) (hinj : Function.Injective d)
    (z : ℂ) :
    finiteIncidenceKMSResponse sigma epsilon d z =
      ∑ a, ∑ b,
        ((4 * epsilon * finiteIncidenceProbability sigma d a *
          finiteIncidenceProbability sigma d b *
            |Real.log (d a) - Real.log (d b)| : ℝ) : ℂ) /
          (z - ((epsilon * (Real.log (d a) - Real.log (d b)) : ℝ) : ℂ)) := by
  unfold finiteIncidenceKMSResponse _root_.HTGeometry.finiteTransitionPassiveResponse
  apply Finset.sum_congr rfl
  intro a ha
  apply Finset.sum_congr rfl
  intro b hb
  rw [finiteKMSEntropyProductionTransitionIntensity_incidence
    hsigma hepsilon hd hinj]
  congr 2
  unfold finiteIncidenceEnergy
  congr 2
  ring

theorem finiteIncidenceKMSResponse_im_nonpos
    {α : Type*} [Fintype α] [Nonempty α]
    {sigma epsilon : ℝ} (hsigma : 0 < sigma) (hepsilon : 0 < epsilon)
    {d : α → ℕ} (hd : ∀ i, 0 < d i)
    {z : ℂ} (hz : 0 < z.im) :
    (finiteIncidenceKMSResponse sigma epsilon d z).im ≤ 0 := by
  unfold finiteIncidenceKMSResponse
  exact _root_.HTGeometry.finiteTransitionPassiveResponse_im_nonpos _ _
    (GaloisForLFunctions.HTGeometry.
      finiteKMSEntropyProductionTransitionIntensity_nonneg
        _ _ _ (finiteIncidenceKMSAmplitude_hermitian sigma epsilon d)) hz

def mobiusIncidenceUniversalGapDensity (x : ℝ) : ℝ :=
  2 * |x| * Real.exp (-|x|)

theorem mobiusIncidenceUniversalGapDensity_nonneg (x : ℝ) :
    0 ≤ mobiusIncidenceUniversalGapDensity x := by
  positivity

theorem integral_mobiusIncidenceUniversalGapDensity :
    (∫ x : ℝ, mobiusIncidenceUniversalGapDensity x) = 4 := by
  rw [show mobiusIncidenceUniversalGapDensity =
      fun x : ℝ => 2 * (|x| * Real.exp (-|x|)) by
    funext x
    rfl]
  rw [integral_const_mul, integral_comp_abs]
  have h := integral_Ioi_pow_mul_exp_neg_rate 1 (show (0 : ℝ) < 1 by norm_num)
  simp only [pow_one, one_mul] at h
  rw [h]
  norm_num

end

end RHTower
