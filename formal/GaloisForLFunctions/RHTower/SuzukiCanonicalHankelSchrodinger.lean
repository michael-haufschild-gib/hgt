import GaloisForLFunctions.RHTower.SuzukiCanonicalHankelEquation418
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts

/-!
# Suzuki (2012), Theorem 4: distributional Schrödinger pair

This module closes the final clause of Suzuki's Theorem 4 without differentiating the continuous
coupling `μ` at its arithmetic cusps.  The globally meaningful operators are the Miura
factorizations

`-(δ - μ)(δ + μ)` and `-(δ + μ)(δ - μ)`, where `δ = a ∂ₐ`.

The normalized modes `ψ⁺ = m⁻¹ A` and `ψ⁻ = m B` satisfy both factorized equations pointwise on
the entire printed axis `a > 0`.  Integration by parts then proves their weak distributional
forms against every compact-interval `C¹` test function.  Away from the exact cusp locus
`a = √n`, the factorizations expand to Suzuki's printed potentials

`V⁺ = μ² - δμ` and `V⁻ = μ² + δμ`.

No derivative of `μ` is totalized across a cusp and no regularity premise is imposed on the
global factorized or weak equations.
-/

open Complex Real MeasureTheory Set Filter Topology

noncomputable section
namespace RHTower

def suzukiHankelPsiPlus
    (omega : ℝ) (homega : 1 < omega) (z : ℂ) (a : ℝ) : ℂ :=
  (suzukiHankelM omega homega a : ℂ)⁻¹ *
    suzukiHankelCompletedARight omega homega a z

def suzukiHankelPsiMinus
    (omega : ℝ) (homega : 1 < omega) (z : ℂ) (a : ℝ) : ℂ :=
  (suzukiHankelM omega homega a : ℂ) *
    suzukiHankelCompletedBRight omega homega a z

theorem hasDerivAt_suzukiHankelPsiPlus
    {omega a : ℝ} (homega : 1 < omega) (ha : 0 < a) (z : ℂ) :
    HasDerivAt (suzukiHankelPsiPlus omega homega z)
      ((-(suzukiHankelMuScalar omega homega a : ℂ) *
          suzukiHankelPsiPlus omega homega z a +
        z * suzukiHankelPsiMinus omega homega z a) / (a : ℂ)) a := by
  have hm := (hasDerivAt_suzukiHankelM (a := a) homega).ofReal_comp
  have hm0 : (suzukiHankelM omega homega a : ℂ) ≠ 0 := by
    exact_mod_cast suzukiHankelM_ne_zero homega a
  have hminv := hm.inv hm0
  have hA := hasDerivAt_suzukiHankelCompletedARight_all_positive homega ha z
  have h := hminv.mul hA
  change HasDerivAt
    (fun b : ℝ => (suzukiHankelM omega homega b : ℂ)⁻¹ *
      suzukiHankelCompletedARight omega homega b z) _ a
  apply h.congr_deriv
  have haC : (a : ℂ) ≠ 0 := by exact_mod_cast ha.ne'
  simp only [suzukiHankelPsiPlus, suzukiHankelPsiMinus]
  simp only [Pi.inv_apply]
  push_cast
  field_simp [haC, hm0]

theorem hasDerivAt_suzukiHankelPsiMinus
    {omega a : ℝ} (homega : 1 < omega) (ha : 0 < a) (z : ℂ) :
    HasDerivAt (suzukiHankelPsiMinus omega homega z)
      (((suzukiHankelMuScalar omega homega a : ℂ) *
          suzukiHankelPsiMinus omega homega z a -
        z * suzukiHankelPsiPlus omega homega z a) / (a : ℂ)) a := by
  have hm := (hasDerivAt_suzukiHankelM (a := a) homega).ofReal_comp
  have hB := hasDerivAt_suzukiHankelCompletedBRight_all_positive homega ha z
  have h := hm.mul hB
  have hm0 : (suzukiHankelM omega homega a : ℂ) ≠ 0 := by
    exact_mod_cast suzukiHankelM_ne_zero homega a
  change HasDerivAt
    (fun b : ℝ => (suzukiHankelM omega homega b : ℂ) *
      suzukiHankelCompletedBRight omega homega b z) _ a
  apply h.congr_deriv
  have haC : (a : ℂ) ≠ 0 := by exact_mod_cast ha.ne'
  simp only [suzukiHankelPsiPlus, suzukiHankelPsiMinus]
  push_cast
  field_simp [haC, hm0]
  ring

def suzukiEulerDerivative (f : ℝ → ℂ) (a : ℝ) : ℂ :=
  (a : ℂ) * deriv f a

def suzukiHankelPsiPlusQuasiDerivative
    (omega : ℝ) (homega : 1 < omega) (z : ℂ) (a : ℝ) : ℂ :=
  suzukiEulerDerivative (suzukiHankelPsiPlus omega homega z) a +
    (suzukiHankelMuScalar omega homega a : ℂ) *
      suzukiHankelPsiPlus omega homega z a

def suzukiHankelPsiMinusQuasiDerivative
    (omega : ℝ) (homega : 1 < omega) (z : ℂ) (a : ℝ) : ℂ :=
  suzukiEulerDerivative (suzukiHankelPsiMinus omega homega z) a -
    (suzukiHankelMuScalar omega homega a : ℂ) *
      suzukiHankelPsiMinus omega homega z a

theorem suzukiHankelPsiPlusQuasiDerivative_eq
    {omega a : ℝ} (homega : 1 < omega) (ha : 0 < a) (z : ℂ) :
    suzukiHankelPsiPlusQuasiDerivative omega homega z a =
      z * suzukiHankelPsiMinus omega homega z a := by
  rw [suzukiHankelPsiPlusQuasiDerivative, suzukiEulerDerivative,
    (hasDerivAt_suzukiHankelPsiPlus homega ha z).deriv]
  have haC : (a : ℂ) ≠ 0 := by exact_mod_cast ha.ne'
  field_simp [haC]
  ring

theorem suzukiHankelPsiMinusQuasiDerivative_eq
    {omega a : ℝ} (homega : 1 < omega) (ha : 0 < a) (z : ℂ) :
    suzukiHankelPsiMinusQuasiDerivative omega homega z a =
      -z * suzukiHankelPsiPlus omega homega z a := by
  rw [suzukiHankelPsiMinusQuasiDerivative, suzukiEulerDerivative,
    (hasDerivAt_suzukiHankelPsiMinus homega ha z).deriv]
  have haC : (a : ℂ) ≠ 0 := by exact_mod_cast ha.ne'
  field_simp [haC]
  ring

def suzukiHankelSchrodingerPlusFactorized
    (omega : ℝ) (homega : 1 < omega) (z : ℂ) (a : ℝ) : ℂ :=
  -suzukiEulerDerivative
      (suzukiHankelPsiPlusQuasiDerivative omega homega z) a +
    (suzukiHankelMuScalar omega homega a : ℂ) *
      suzukiHankelPsiPlusQuasiDerivative omega homega z a

def suzukiHankelSchrodingerMinusFactorized
    (omega : ℝ) (homega : 1 < omega) (z : ℂ) (a : ℝ) : ℂ :=
  -suzukiEulerDerivative
      (suzukiHankelPsiMinusQuasiDerivative omega homega z) a -
    (suzukiHankelMuScalar omega homega a : ℂ) *
      suzukiHankelPsiMinusQuasiDerivative omega homega z a

theorem hasDerivAt_suzukiHankelPsiPlusQuasiDerivative
    {omega a : ℝ} (homega : 1 < omega) (ha : 0 < a) (z : ℂ) :
    HasDerivAt (suzukiHankelPsiPlusQuasiDerivative omega homega z)
      (z * (((suzukiHankelMuScalar omega homega a : ℂ) *
          suzukiHankelPsiMinus omega homega z a -
        z * suzukiHankelPsiPlus omega homega z a) / (a : ℂ))) a := by
  have hbase := (hasDerivAt_suzukiHankelPsiMinus homega ha z).const_mul z
  apply hbase.congr_of_eventuallyEq
  filter_upwards [Ioi_mem_nhds ha] with b hb
  exact suzukiHankelPsiPlusQuasiDerivative_eq homega hb z

theorem hasDerivAt_suzukiHankelPsiMinusQuasiDerivative
    {omega a : ℝ} (homega : 1 < omega) (ha : 0 < a) (z : ℂ) :
    HasDerivAt (suzukiHankelPsiMinusQuasiDerivative omega homega z)
      ((-z) * ((-(suzukiHankelMuScalar omega homega a : ℂ) *
          suzukiHankelPsiPlus omega homega z a +
        z * suzukiHankelPsiMinus omega homega z a) / (a : ℂ))) a := by
  have hbase := (hasDerivAt_suzukiHankelPsiPlus homega ha z).const_mul (-z)
  apply hbase.congr_of_eventuallyEq
  filter_upwards [Ioi_mem_nhds ha] with b hb
  exact suzukiHankelPsiMinusQuasiDerivative_eq homega hb z

def suzukiHankelPsiPlusQuasiDerivativeField
    (omega : ℝ) (homega : 1 < omega) (z : ℂ) (a : ℝ) : ℂ :=
  z * (((suzukiHankelMuScalar omega homega a : ℂ) *
      suzukiHankelPsiMinus omega homega z a -
    z * suzukiHankelPsiPlus omega homega z a) / (a : ℂ))

def suzukiHankelPsiMinusQuasiDerivativeField
    (omega : ℝ) (homega : 1 < omega) (z : ℂ) (a : ℝ) : ℂ :=
  (-z) * ((-(suzukiHankelMuScalar omega homega a : ℂ) *
      suzukiHankelPsiPlus omega homega z a +
    z * suzukiHankelPsiMinus omega homega z a) / (a : ℂ))

theorem hasDerivAt_suzukiHankelPsiPlusQuasiDerivativeField
    {omega a : ℝ} (homega : 1 < omega) (ha : 0 < a) (z : ℂ) :
    HasDerivAt (suzukiHankelPsiPlusQuasiDerivative omega homega z)
      (suzukiHankelPsiPlusQuasiDerivativeField omega homega z a) a := by
  exact hasDerivAt_suzukiHankelPsiPlusQuasiDerivative homega ha z

theorem hasDerivAt_suzukiHankelPsiMinusQuasiDerivativeField
    {omega a : ℝ} (homega : 1 < omega) (ha : 0 < a) (z : ℂ) :
    HasDerivAt (suzukiHankelPsiMinusQuasiDerivative omega homega z)
      (suzukiHankelPsiMinusQuasiDerivativeField omega homega z a) a := by
  exact hasDerivAt_suzukiHankelPsiMinusQuasiDerivative homega ha z

theorem continuousOn_suzukiHankelPsiPlus
    {omega : ℝ} (homega : 1 < omega) (z : ℂ) :
    ContinuousOn (suzukiHankelPsiPlus omega homega z) (Ioi 0) := by
  intro a ha
  exact (hasDerivAt_suzukiHankelPsiPlus homega ha z).continuousAt.continuousWithinAt

theorem continuousOn_suzukiHankelPsiMinus
    {omega : ℝ} (homega : 1 < omega) (z : ℂ) :
    ContinuousOn (suzukiHankelPsiMinus omega homega z) (Ioi 0) := by
  intro a ha
  exact (hasDerivAt_suzukiHankelPsiMinus homega ha z).continuousAt.continuousWithinAt

theorem continuousOn_suzukiHankelPsiPlusQuasiDerivativeField
    {omega : ℝ} (homega : 1 < omega) (z : ℂ) :
    ContinuousOn
      (suzukiHankelPsiPlusQuasiDerivativeField omega homega z) (Ioi 0) := by
  intro a ha
  have hμ : ContinuousAt
      (fun b : ℝ => (suzukiHankelMuScalar omega homega b : ℂ)) a :=
    Complex.continuous_ofReal.continuousAt.comp
      (continuous_suzukiHankelMuScalar homega).continuousAt
  have hp := (hasDerivAt_suzukiHankelPsiPlus homega ha z).continuousAt
  have hm := (hasDerivAt_suzukiHankelPsiMinus homega ha z).continuousAt
  have haC : (a : ℂ) ≠ 0 := by exact_mod_cast ha.ne'
  exact (continuousAt_const.mul
    (((hμ.mul hm).sub (continuousAt_const.mul hp)).div
      Complex.continuous_ofReal.continuousAt haC)).continuousWithinAt

theorem continuousOn_suzukiHankelPsiMinusQuasiDerivativeField
    {omega : ℝ} (homega : 1 < omega) (z : ℂ) :
    ContinuousOn
      (suzukiHankelPsiMinusQuasiDerivativeField omega homega z) (Ioi 0) := by
  intro a ha
  have hμ : ContinuousAt
      (fun b : ℝ => (suzukiHankelMuScalar omega homega b : ℂ)) a :=
    Complex.continuous_ofReal.continuousAt.comp
      (continuous_suzukiHankelMuScalar homega).continuousAt
  have hp : ContinuousAt (suzukiHankelPsiPlus omega homega z) a :=
    (hasDerivAt_suzukiHankelPsiPlus homega ha z).continuousAt
  have hm : ContinuousAt (suzukiHankelPsiMinus omega homega z) a :=
    (hasDerivAt_suzukiHankelPsiMinus homega ha z).continuousAt
  have haC : (a : ℂ) ≠ 0 := by exact_mod_cast ha.ne'
  have hnum : ContinuousAt (fun b : ℝ =>
      -(suzukiHankelMuScalar omega homega b : ℂ) *
          suzukiHankelPsiPlus omega homega z b +
        z * suzukiHankelPsiMinus omega homega z b) a :=
    (hμ.neg.mul hp).add (continuousAt_const.mul hm)
  have hquot := hnum.div Complex.continuous_ofReal.continuousAt haC
  exact (continuousAt_const.mul hquot).continuousWithinAt

theorem suzukiHankelSchrodingerPlusFactorized_eq
    {omega a : ℝ} (homega : 1 < omega) (ha : 0 < a) (z : ℂ) :
    suzukiHankelSchrodingerPlusFactorized omega homega z a =
      z ^ (2 : ℕ) * suzukiHankelPsiPlus omega homega z a := by
  rw [suzukiHankelSchrodingerPlusFactorized, suzukiEulerDerivative,
    (hasDerivAt_suzukiHankelPsiPlusQuasiDerivative homega ha z).deriv,
    suzukiHankelPsiPlusQuasiDerivative_eq homega ha z]
  have haC : (a : ℂ) ≠ 0 := by exact_mod_cast ha.ne'
  field_simp [haC]
  ring

theorem suzukiHankelSchrodingerMinusFactorized_eq
    {omega a : ℝ} (homega : 1 < omega) (ha : 0 < a) (z : ℂ) :
    suzukiHankelSchrodingerMinusFactorized omega homega z a =
      z ^ (2 : ℕ) * suzukiHankelPsiMinus omega homega z a := by
  rw [suzukiHankelSchrodingerMinusFactorized, suzukiEulerDerivative,
    (hasDerivAt_suzukiHankelPsiMinusQuasiDerivative homega ha z).deriv,
    suzukiHankelPsiMinusQuasiDerivative_eq homega ha z]
  have haC : (a : ℂ) ≠ 0 := by exact_mod_cast ha.ne'
  field_simp [haC]
  ring

theorem suzukiHankelPsiPlusQuasiDerivativeField_eq_residual
    {omega a : ℝ} (homega : 1 < omega) (ha : 0 < a) (z : ℂ) :
    suzukiHankelPsiPlusQuasiDerivativeField omega homega z a =
      (((suzukiHankelMuScalar omega homega a : ℂ) *
          suzukiHankelPsiPlusQuasiDerivative omega homega z a -
        z ^ (2 : ℕ) * suzukiHankelPsiPlus omega homega z a) / (a : ℂ)) := by
  have h := suzukiHankelSchrodingerPlusFactorized_eq homega ha z
  rw [suzukiHankelSchrodingerPlusFactorized, suzukiEulerDerivative,
    (hasDerivAt_suzukiHankelPsiPlusQuasiDerivativeField homega ha z).deriv] at h
  have haC : (a : ℂ) ≠ 0 := by exact_mod_cast ha.ne'
  rw [eq_div_iff haC]
  linear_combination -h

theorem suzukiHankelPsiMinusQuasiDerivativeField_eq_residual
    {omega a : ℝ} (homega : 1 < omega) (ha : 0 < a) (z : ℂ) :
    suzukiHankelPsiMinusQuasiDerivativeField omega homega z a =
      ((-(suzukiHankelMuScalar omega homega a : ℂ) *
          suzukiHankelPsiMinusQuasiDerivative omega homega z a -
        z ^ (2 : ℕ) * suzukiHankelPsiMinus omega homega z a) / (a : ℂ)) := by
  have h := suzukiHankelSchrodingerMinusFactorized_eq homega ha z
  rw [suzukiHankelSchrodingerMinusFactorized, suzukiEulerDerivative,
    (hasDerivAt_suzukiHankelPsiMinusQuasiDerivativeField homega ha z).deriv] at h
  have haC : (a : ℂ) ≠ 0 := by exact_mod_cast ha.ne'
  rw [eq_div_iff haC]
  linear_combination -h

theorem integral_quasiDerivative_mul_test_add_eq_zero
    {Q Q' φ : ℝ → ℂ} {p q : ℝ} (hpq : p ≤ q)
    (hQ : ∀ x ∈ Icc p q, HasDerivAt Q (Q' x) x)
    (hQ' : ContinuousOn Q' (Icc p q))
    (hφ : ContDiff ℝ 1 φ) (hφp : φ p = 0) (hφq : φ q = 0) :
    (∫ x in p..q, Q x * deriv φ x) +
      (∫ x in p..q, Q' x * φ x) = 0 := by
  have hφderiv : ∀ x ∈ Icc p q, HasDerivAt φ (deriv φ x) x := by
    intro x _
    exact ((hφ.differentiable (by norm_num)) x).hasDerivAt
  have hQ'int : IntervalIntegrable Q' volume p q :=
    hQ'.intervalIntegrable_of_Icc hpq
  have hφ'int : IntervalIntegrable (deriv φ) volume p q :=
    hφ.continuous_deriv_one.intervalIntegrable p q
  have hibp := intervalIntegral.integral_mul_deriv_eq_deriv_mul
    (a := p) (b := q)
    (fun x hx => hQ x (by simpa [uIcc_of_le hpq] using hx))
    (fun x hx => hφderiv x (by simpa [uIcc_of_le hpq] using hx))
    hQ'int hφ'int
  rw [hibp, hφp, hφq]
  ring

theorem suzukiHankelSchrodingerPlus_weak
    {omega p q : ℝ} (homega : 1 < omega) (hp : 0 < p) (hpq : p ≤ q)
    (z : ℂ) (φ : ℝ → ℂ) (hφ : ContDiff ℝ 1 φ)
    (hφp : φ p = 0) (hφq : φ q = 0) :
    (∫ x in p..q,
        suzukiHankelPsiPlusQuasiDerivative omega homega z x * deriv φ x) +
      (∫ x in p..q,
        (((suzukiHankelMuScalar omega homega x : ℂ) *
            suzukiHankelPsiPlusQuasiDerivative omega homega z x -
          z ^ (2 : ℕ) * suzukiHankelPsiPlus omega homega z x) / (x : ℂ)) * φ x) = 0 := by
  have hpos : Icc p q ⊆ Ioi (0 : ℝ) := fun x hx => lt_of_lt_of_le hp hx.1
  have hbase := integral_quasiDerivative_mul_test_add_eq_zero hpq
    (fun x hx => hasDerivAt_suzukiHankelPsiPlusQuasiDerivativeField
      homega (hpos hx) z)
    ((continuousOn_suzukiHankelPsiPlusQuasiDerivativeField homega z).mono hpos)
    hφ hφp hφq
  have hInt : (∫ x in p..q,
        (((suzukiHankelMuScalar omega homega x : ℂ) *
            suzukiHankelPsiPlusQuasiDerivative omega homega z x -
          z ^ (2 : ℕ) * suzukiHankelPsiPlus omega homega z x) / (x : ℂ)) * φ x) =
      ∫ x in p..q,
        suzukiHankelPsiPlusQuasiDerivativeField omega homega z x * φ x := by
    apply intervalIntegral.integral_congr
    intro x hx
    change (((suzukiHankelMuScalar omega homega x : ℂ) *
          suzukiHankelPsiPlusQuasiDerivative omega homega z x -
        z ^ (2 : ℕ) * suzukiHankelPsiPlus omega homega z x) / (x : ℂ)) * φ x =
      suzukiHankelPsiPlusQuasiDerivativeField omega homega z x * φ x
    rw [suzukiHankelPsiPlusQuasiDerivativeField_eq_residual
      homega (hpos (by simpa [uIcc_of_le hpq] using hx)) z]
  rw [hInt]
  exact hbase

theorem suzukiHankelSchrodingerMinus_weak
    {omega p q : ℝ} (homega : 1 < omega) (hp : 0 < p) (hpq : p ≤ q)
    (z : ℂ) (φ : ℝ → ℂ) (hφ : ContDiff ℝ 1 φ)
    (hφp : φ p = 0) (hφq : φ q = 0) :
    (∫ x in p..q,
        suzukiHankelPsiMinusQuasiDerivative omega homega z x * deriv φ x) +
      (∫ x in p..q,
        ((-(suzukiHankelMuScalar omega homega x : ℂ) *
            suzukiHankelPsiMinusQuasiDerivative omega homega z x -
          z ^ (2 : ℕ) * suzukiHankelPsiMinus omega homega z x) / (x : ℂ)) * φ x) = 0 := by
  have hpos : Icc p q ⊆ Ioi (0 : ℝ) := fun x hx => lt_of_lt_of_le hp hx.1
  have hbase := integral_quasiDerivative_mul_test_add_eq_zero hpq
    (fun x hx => hasDerivAt_suzukiHankelPsiMinusQuasiDerivativeField
      homega (hpos hx) z)
    ((continuousOn_suzukiHankelPsiMinusQuasiDerivativeField homega z).mono hpos)
    hφ hφp hφq
  have hInt : (∫ x in p..q,
        ((-(suzukiHankelMuScalar omega homega x : ℂ) *
            suzukiHankelPsiMinusQuasiDerivative omega homega z x -
          z ^ (2 : ℕ) * suzukiHankelPsiMinus omega homega z x) / (x : ℂ)) * φ x) =
      ∫ x in p..q,
        suzukiHankelPsiMinusQuasiDerivativeField omega homega z x * φ x := by
    apply intervalIntegral.integral_congr
    intro x hx
    change ((-(suzukiHankelMuScalar omega homega x : ℂ) *
          suzukiHankelPsiMinusQuasiDerivative omega homega z x -
        z ^ (2 : ℕ) * suzukiHankelPsiMinus omega homega z x) / (x : ℂ)) * φ x =
      suzukiHankelPsiMinusQuasiDerivativeField omega homega z x * φ x
    rw [suzukiHankelPsiMinusQuasiDerivativeField_eq_residual
      homega (hpos (by simpa [uIcc_of_le hpq] using hx)) z]
  rw [hInt]
  exact hbase

theorem suzukiEulerDerivative_suzukiHankelPsiPlus_eq
    {omega a : ℝ} (homega : 1 < omega) (ha : 0 < a) (z : ℂ) :
    suzukiEulerDerivative (suzukiHankelPsiPlus omega homega z) a =
      -(suzukiHankelMuScalar omega homega a : ℂ) *
          suzukiHankelPsiPlus omega homega z a +
        z * suzukiHankelPsiMinus omega homega z a := by
  have h := suzukiHankelPsiPlusQuasiDerivative_eq homega ha z
  rw [suzukiHankelPsiPlusQuasiDerivative] at h
  linear_combination h

theorem suzukiEulerDerivative_suzukiHankelPsiMinus_eq
    {omega a : ℝ} (homega : 1 < omega) (ha : 0 < a) (z : ℂ) :
    suzukiEulerDerivative (suzukiHankelPsiMinus omega homega z) a =
      (suzukiHankelMuScalar omega homega a : ℂ) *
          suzukiHankelPsiMinus omega homega z a -
        z * suzukiHankelPsiPlus omega homega z a := by
  have h := suzukiHankelPsiMinusQuasiDerivative_eq homega ha z
  rw [suzukiHankelPsiMinusQuasiDerivative] at h
  linear_combination h

theorem differentiableAt_suzukiHankelMuComplex_of_regular
    {omega a : ℝ} (homega : 1 < omega) (ha : 1 < a)
    (hsquare : ∀ n : ℕ, a ≠ Real.sqrt n) :
    DifferentiableAt ℝ
      (fun b : ℝ => (suzukiHankelMuScalar omega homega b : ℂ)) a := by
  have hmu : ContDiffAt ℝ 1 (suzukiHankelMuReal omega homega) a :=
    (contDiffAt_one_suzukiHankelBoundaryTraceReal_of_regular
      SuzukiHankelSign.positive homega ha hsquare).add
      (contDiffAt_one_suzukiHankelBoundaryTraceReal_of_regular
        SuzukiHankelSign.negative homega ha hsquare)
  have hd := hmu.differentiableAt (by norm_num : (1 : WithTop ℕ∞) ≠ 0)
  simpa only [ofReal_suzukiHankelMuScalar_eq] using hd

theorem differentiableAt_suzukiEulerDerivativePsiPlus_of_regular
    {omega a : ℝ} (homega : 1 < omega) (ha : 1 < a)
    (hsquare : ∀ n : ℕ, a ≠ Real.sqrt n) (z : ℂ) :
    DifferentiableAt ℝ
      (fun b => suzukiEulerDerivative
        (suzukiHankelPsiPlus omega homega z) b) a := by
  have hmu := differentiableAt_suzukiHankelMuComplex_of_regular
    homega ha hsquare
  have hp := (hasDerivAt_suzukiHankelPsiPlus homega
    (lt_trans zero_lt_one ha) z).differentiableAt
  have hm := (hasDerivAt_suzukiHankelPsiMinus homega
    (lt_trans zero_lt_one ha) z).differentiableAt
  have hz : DifferentiableAt ℝ (fun _ : ℝ => z) a := differentiableAt_const z
  have hrhs := (hmu.mul hp).neg.add (hz.mul hm)
  apply hrhs.congr_of_eventuallyEq
  filter_upwards [Ioi_mem_nhds (lt_trans zero_lt_one ha)] with b hb
  simp only [Pi.neg_apply, Pi.mul_apply, Pi.add_apply]
  rw [suzukiEulerDerivative_suzukiHankelPsiPlus_eq homega hb z]
  ring

theorem differentiableAt_suzukiEulerDerivativePsiMinus_of_regular
    {omega a : ℝ} (homega : 1 < omega) (ha : 1 < a)
    (hsquare : ∀ n : ℕ, a ≠ Real.sqrt n) (z : ℂ) :
    DifferentiableAt ℝ
      (fun b => suzukiEulerDerivative
        (suzukiHankelPsiMinus omega homega z) b) a := by
  have hmu := differentiableAt_suzukiHankelMuComplex_of_regular
    homega ha hsquare
  have hp := (hasDerivAt_suzukiHankelPsiPlus homega
    (lt_trans zero_lt_one ha) z).differentiableAt
  have hm := (hasDerivAt_suzukiHankelPsiMinus homega
    (lt_trans zero_lt_one ha) z).differentiableAt
  have hz : DifferentiableAt ℝ (fun _ : ℝ => z) a := differentiableAt_const z
  have hrhs := (hmu.mul hm).sub (hz.mul hp)
  apply hrhs.congr_of_eventuallyEq
  filter_upwards [Ioi_mem_nhds (lt_trans zero_lt_one ha)] with b hb
  exact suzukiEulerDerivative_suzukiHankelPsiMinus_eq homega hb z

def suzukiHankelSchrodingerPlusExpanded
    (omega : ℝ) (homega : 1 < omega) (z : ℂ) (a : ℝ) : ℂ :=
  -suzukiEulerDerivative
      (fun b => suzukiEulerDerivative
        (suzukiHankelPsiPlus omega homega z) b) a +
    ((suzukiHankelMuScalar omega homega a : ℂ) ^ (2 : ℕ) -
      suzukiEulerDerivative
        (fun b => (suzukiHankelMuScalar omega homega b : ℂ)) a) *
      suzukiHankelPsiPlus omega homega z a

def suzukiHankelSchrodingerMinusExpanded
    (omega : ℝ) (homega : 1 < omega) (z : ℂ) (a : ℝ) : ℂ :=
  -suzukiEulerDerivative
      (fun b => suzukiEulerDerivative
        (suzukiHankelPsiMinus omega homega z) b) a +
    ((suzukiHankelMuScalar omega homega a : ℂ) ^ (2 : ℕ) +
      suzukiEulerDerivative
        (fun b => (suzukiHankelMuScalar omega homega b : ℂ)) a) *
      suzukiHankelPsiMinus omega homega z a

theorem suzukiHankelSchrodingerPlusExpanded_eq_factorized_of_regular
    {omega a : ℝ} (homega : 1 < omega) (ha : 1 < a)
    (hsquare : ∀ n : ℕ, a ≠ Real.sqrt n) (z : ℂ) :
    suzukiHankelSchrodingerPlusExpanded omega homega z a =
      suzukiHankelSchrodingerPlusFactorized omega homega z a := by
  let μ : ℝ → ℂ := fun b => (suzukiHankelMuScalar omega homega b : ℂ)
  let ψ : ℝ → ℂ := suzukiHankelPsiPlus omega homega z
  let δψ : ℝ → ℂ := fun b => suzukiEulerDerivative ψ b
  have hμ := (differentiableAt_suzukiHankelMuComplex_of_regular
    homega ha hsquare).hasDerivAt
  have hψ := (hasDerivAt_suzukiHankelPsiPlus homega
    (lt_trans zero_lt_one ha) z).differentiableAt.hasDerivAt
  have hδψ := (differentiableAt_suzukiEulerDerivativePsiPlus_of_regular
    homega ha hsquare z).hasDerivAt
  have hsum := hδψ.add (hμ.mul hψ)
  have hQ := hsum.congr_of_eventuallyEq (f₁ :=
      suzukiHankelPsiPlusQuasiDerivative omega homega z) (by
    filter_upwards with b
    rfl)
  have hQderiv := hQ.deriv
  have hQderiv' := hQderiv
  simp only [suzukiEulerDerivative] at hQderiv'
  rw [suzukiHankelSchrodingerPlusExpanded,
    suzukiHankelSchrodingerPlusFactorized]
  simp only [suzukiEulerDerivative]
  rw [hQderiv']
  rw [suzukiHankelPsiPlusQuasiDerivative]
  simp only [suzukiEulerDerivative]
  ring

theorem suzukiHankelSchrodingerMinusExpanded_eq_factorized_of_regular
    {omega a : ℝ} (homega : 1 < omega) (ha : 1 < a)
    (hsquare : ∀ n : ℕ, a ≠ Real.sqrt n) (z : ℂ) :
    suzukiHankelSchrodingerMinusExpanded omega homega z a =
      suzukiHankelSchrodingerMinusFactorized omega homega z a := by
  let μ : ℝ → ℂ := fun b => (suzukiHankelMuScalar omega homega b : ℂ)
  let ψ : ℝ → ℂ := suzukiHankelPsiMinus omega homega z
  let δψ : ℝ → ℂ := fun b => suzukiEulerDerivative ψ b
  have hμ := (differentiableAt_suzukiHankelMuComplex_of_regular
    homega ha hsquare).hasDerivAt
  have hψ := (hasDerivAt_suzukiHankelPsiMinus homega
    (lt_trans zero_lt_one ha) z).differentiableAt.hasDerivAt
  have hδψ := (differentiableAt_suzukiEulerDerivativePsiMinus_of_regular
    homega ha hsquare z).hasDerivAt
  have hdiff := hδψ.sub (hμ.mul hψ)
  have hQ := hdiff.congr_of_eventuallyEq (f₁ :=
      suzukiHankelPsiMinusQuasiDerivative omega homega z) (by
    filter_upwards with b
    rfl)
  have hQderiv := hQ.deriv
  have hQderiv' := hQderiv
  simp only [suzukiEulerDerivative] at hQderiv'
  rw [suzukiHankelSchrodingerMinusExpanded,
    suzukiHankelSchrodingerMinusFactorized]
  simp only [suzukiEulerDerivative]
  rw [hQderiv']
  rw [suzukiHankelPsiMinusQuasiDerivative]
  simp only [suzukiEulerDerivative]
  ring

theorem suzukiHankelSchrodingerPlusExpanded_eq_of_regular
    {omega a : ℝ} (homega : 1 < omega) (ha : 1 < a)
    (hsquare : ∀ n : ℕ, a ≠ Real.sqrt n) (z : ℂ) :
    suzukiHankelSchrodingerPlusExpanded omega homega z a =
      z ^ (2 : ℕ) * suzukiHankelPsiPlus omega homega z a := by
  rw [suzukiHankelSchrodingerPlusExpanded_eq_factorized_of_regular
    homega ha hsquare z,
    suzukiHankelSchrodingerPlusFactorized_eq homega
      (lt_trans zero_lt_one ha) z]

theorem suzukiHankelSchrodingerMinusExpanded_eq_of_regular
    {omega a : ℝ} (homega : 1 < omega) (ha : 1 < a)
    (hsquare : ∀ n : ℕ, a ≠ Real.sqrt n) (z : ℂ) :
    suzukiHankelSchrodingerMinusExpanded omega homega z a =
      z ^ (2 : ℕ) * suzukiHankelPsiMinus omega homega z a := by
  rw [suzukiHankelSchrodingerMinusExpanded_eq_factorized_of_regular
    homega ha hsquare z,
    suzukiHankelSchrodingerMinusFactorized_eq homega
      (lt_trans zero_lt_one ha) z]

/-- **Suzuki (2012), Theorem 4, Schrödinger clause.**  Both distributional Miura
factorizations hold on the complete positive aperture axis, including the seam and every
arithmetic cusp. -/
theorem suzuki2012_theorem_four_schrodinger_pair :
    ∀ (omega : ℝ) (homega : 1 < omega) (a : ℝ), 0 < a → ∀ (z : ℂ),
      suzukiHankelSchrodingerPlusFactorized omega homega z a =
          z ^ (2 : ℕ) * suzukiHankelPsiPlus omega homega z a ∧
        suzukiHankelSchrodingerMinusFactorized omega homega z a =
          z ^ (2 : ℕ) * suzukiHankelPsiMinus omega homega z a := by
  intro omega homega a ha z
  exact ⟨suzukiHankelSchrodingerPlusFactorized_eq homega ha z,
    suzukiHankelSchrodingerMinusFactorized_eq homega ha z⟩

/-- The same pair in its exact compact-interval weak form.  This quantifies over every `C¹`
test function vanishing at the interval endpoints, hence records the distributional content
without assigning an artificial classical value to `δμ` at a cusp. -/
theorem suzuki2012_theorem_four_schrodinger_pair_weak :
    ∀ (omega : ℝ) (homega : 1 < omega) (p q : ℝ),
      0 < p → p ≤ q → ∀ (z : ℂ) (φ : ℝ → ℂ),
      ContDiff ℝ 1 φ → φ p = 0 → φ q = 0 →
      ((∫ x in p..q,
          suzukiHankelPsiPlusQuasiDerivative omega homega z x * deriv φ x) +
        (∫ x in p..q,
          (((suzukiHankelMuScalar omega homega x : ℂ) *
              suzukiHankelPsiPlusQuasiDerivative omega homega z x -
            z ^ (2 : ℕ) * suzukiHankelPsiPlus omega homega z x) / (x : ℂ)) * φ x) = 0) ∧
      ((∫ x in p..q,
          suzukiHankelPsiMinusQuasiDerivative omega homega z x * deriv φ x) +
        (∫ x in p..q,
          ((-(suzukiHankelMuScalar omega homega x : ℂ) *
              suzukiHankelPsiMinusQuasiDerivative omega homega z x -
            z ^ (2 : ℕ) * suzukiHankelPsiMinus omega homega z x) / (x : ℂ)) * φ x) = 0) := by
  intro omega homega p q hp hpq z φ hφ hφp hφq
  exact ⟨suzukiHankelSchrodingerPlus_weak homega hp hpq z φ hφ hφp hφq,
    suzukiHankelSchrodingerMinus_weak homega hp hpq z φ hφ hφp hφq⟩

end RHTower
