import GaloisForLFunctions.RHTower.RealJetsOfHolomorphic
import GaloisForLFunctions.HTGeometry.SampledSmallSmooth
import GaloisForLFunctions.RHTower.LiEvenCrossTwoScaleRadialGeneratingLaw
import GaloisForLFunctions.RHTower.LiReciprocalChebyshevKernel

/-!
# Local Bernstein shape does not orient the Li tower

The exact LI two-scale generating law reduces adjacent-current orientation to the radial atom
`z b / (z+b)^(2 : ℕ)`. This module gives a finite conjugation-symmetric squared-node packet whose
real radial response is strictly Bernstein at every order on the full physical interval
`0 ≤ v ≤ 1/4`, while its fourth completed-Abel even-cross mode is strictly negative.

Thus even the complete local alternating derivative tower cannot supply the remaining LI
coefficient orientation. Any surviving radial-shape route must use global analytic continuation
or singularity-support exhaustion capable of excluding off-axis squared nodes.
-/

open Complex Filter Topology Set

namespace RHTower

noncomputable section

def liLocalRadialAtom (b z : ℂ) : ℂ := z * b / (z + b) ^ (2 : ℕ)

theorem iteratedDeriv_invSq_add_const (b : ℂ) (m : ℕ) (z : ℂ) (hz : z + b ≠ 0) :
    iteratedDeriv m (fun w : ℂ => ((w + b) ^ (2 : ℕ))⁻¹) z =
      (-1 : ℂ) ^ m * ((m + 1).factorial : ℂ) *
        ((z + b) ^ (m + 2))⁻¹ := by
  have hev : ∀ᶠ w in 𝓝 z, w + b ≠ 0 :=
    (continuousAt_id.add continuousAt_const).eventually_ne hz
  have hderiv : deriv (fun w : ℂ => (w + b)⁻¹) =ᶠ[𝓝 z]
      fun w => -((w + b) ^ (2 : ℕ))⁻¹ := by
    filter_upwards [hev] with w hw
    have h := ((hasDerivAt_id w).add_const b).inv hw
    change deriv ((fun x : ℂ => x + b)⁻¹) w = -((w + b) ^ (2 : ℕ))⁻¹
    simpa only [Pi.inv_apply, id_eq, one_div, neg_div, one_mul] using h.deriv
  have hs := GaloisForLFunctions.iteratedDeriv_inv_add_const b (m + 1) z hz
  rw [iteratedDeriv_succ'] at hs
  rw [hderiv.iteratedDeriv_eq m] at hs
  rw [show (fun w : ℂ => -((w + b) ^ (2 : ℕ))⁻¹) =
      -(fun w : ℂ => ((w + b) ^ (2 : ℕ))⁻¹) by rfl, iteratedDeriv_neg] at hs
  apply neg_injective
  rw [hs]
  rw [show m + 1 + 1 = m + 2 by omega, pow_succ]
  ring

theorem iteratedDeriv_liLocalRadialAtom (b : ℂ) (m : ℕ) (z : ℂ) (hz : z + b ≠ 0) :
    iteratedDeriv (m + 1) (liLocalRadialAtom b) z =
      (-1 : ℂ) ^ m * ((m + 1).factorial : ℂ) * b *
        (((m + 1 : ℕ) : ℂ) * b - z) / (z + b) ^ (m + 3) := by
  have hev : ∀ᶠ w in 𝓝 z, w + b ≠ 0 :=
    (continuousAt_id.add continuousAt_const).eventually_ne hz
  have hdecomp : liLocalRadialAtom b =ᶠ[𝓝 z]
      fun w => b * (w + b)⁻¹ - b ^ (2 : ℕ) * ((w + b) ^ (2 : ℕ))⁻¹ := by
    filter_upwards [hev] with w hw
    simp only [liLocalRadialAtom]
    field_simp
    ring
  rw [hdecomp.iteratedDeriv_eq (m + 1)]
  have hsimple : ContDiffAt ℂ (m + 1) (fun w : ℂ => (w + b)⁻¹) z := by
    exact (contDiffAt_id.add contDiffAt_const).inv hz
  have hsq : ContDiffAt ℂ (m + 1) (fun w : ℂ => ((w + b) ^ (2 : ℕ))⁻¹) z := by
    exact ((contDiffAt_id.add contDiffAt_const).pow 2).inv (pow_ne_zero 2 hz)
  have hb : ContDiffAt ℂ (m + 1) (fun w : ℂ => b * (w + b)⁻¹) z :=
    contDiffAt_const.mul hsimple
  have hb2 : ContDiffAt ℂ (m + 1) (fun w : ℂ => b ^ (2 : ℕ) * ((w + b) ^ (2 : ℕ))⁻¹) z :=
    contDiffAt_const.mul hsq
  change iteratedDeriv (m + 1)
      ((fun w : ℂ => b * (w + b)⁻¹) -
        (fun w : ℂ => b ^ (2 : ℕ) * ((w + b) ^ (2 : ℕ))⁻¹)) z = _
  rw [iteratedDeriv_sub hb hb2]
  rw [iteratedDeriv_const_mul b hsimple]
  rw [iteratedDeriv_const_mul (b ^ (2 : ℕ)) hsq]
  rw [GaloisForLFunctions.iteratedDeriv_inv_add_const b (m + 1) z hz]
  rw [iteratedDeriv_invSq_add_const b (m + 1) z hz]
  simp only [pow_succ]
  rw [show (m + 1 + 1).factorial = (m + 2) * (m + 1).factorial by
    rw [show m + 1 + 1 = (m + 1) + 1 by omega, Nat.factorial_succ]]
  push_cast
  field_simp
  ring

def liLocalRadialSignedJet (b : ℂ) (m : ℕ) (v : ℝ) : ℂ :=
  ((m + 1).factorial : ℂ) * b *
    (((m + 1 : ℕ) : ℂ) * b - (v : ℂ)) / ((v : ℂ) + b) ^ (m + 3)

def liLocalOnLineNode : ℂ := 1 / 2

def liLocalOffLineNode : ℂ := 3 / 4 + I

def liLocalOffLineNodeConj : ℂ := 3 / 4 - I

theorem norm_liLocalOffLineNode : ‖liLocalOffLineNode‖ = 5 / 4 := by
  rw [Complex.norm_def]
  simp [liLocalOffLineNode, Complex.normSq_apply]
  norm_num

theorem norm_liLocalOffLineNodeConj : ‖liLocalOffLineNodeConj‖ = 5 / 4 := by
  rw [Complex.norm_def]
  simp [liLocalOffLineNodeConj, Complex.normSq_apply]
  norm_num

theorem liLocalRadialSignedJet_base_eq_ofReal (m : ℕ) (v : ℝ) (hv : 0 ≤ v) :
    liLocalRadialSignedJet liLocalOnLineNode m v =
      (((m + 1).factorial : ℝ) * (1 / 2) * (((m + 1 : ℕ) : ℝ) / 2 - v) /
        (v + 1 / 2) ^ (m + 3) : ℝ) := by
  have hden : v + 1 / 2 ≠ 0 := by linarith
  simp only [liLocalRadialSignedJet, liLocalOnLineNode]
  have hnum : (((m + 1 : ℕ) : ℂ) * (1 / 2 : ℂ) - (v : ℂ)) =
      ((((m + 1 : ℕ) : ℝ) / 2 - v : ℝ) : ℂ) := by
    norm_num
    ring
  have hdenpow : ((v : ℂ) + (1 / 2 : ℂ)) ^ (m + 3) =
      (((v + 1 / 2) ^ (m + 3) : ℝ) : ℂ) := by
    calc
      ((v : ℂ) + (1 / 2 : ℂ)) ^ (m + 3) =
          (((v + 1 / 2 : ℝ) : ℂ)) ^ (m + 3) := by norm_num
      _ = (((v + 1 / 2) ^ (m + 3) : ℝ) : ℂ) :=
        (Complex.ofReal_pow _ _).symm
  rw [hnum, hdenpow]
  norm_num [Complex.ofReal_mul, Complex.ofReal_div]

theorem liLocalRadialSignedJet_base_re (m : ℕ) (v : ℝ) (hv : 0 ≤ v) :
    (liLocalRadialSignedJet liLocalOnLineNode m v).re =
      ((m + 1).factorial : ℝ) * (1 / 2) * (((m + 1 : ℕ) : ℝ) / 2 - v) /
        (v + 1 / 2) ^ (m + 3) := by
  rw [liLocalRadialSignedJet_base_eq_ofReal m v hv]
  rfl

theorem norm_add_liLocalOffLineNode_ofReal_lower (v : ℝ) (hv : 0 ≤ v) :
    5 / 4 ≤ ‖(v : ℂ) + liLocalOffLineNode‖ := by
  rw [Complex.norm_def]
  rw [Real.le_sqrt (by norm_num)]
  simp [liLocalOffLineNode, Complex.normSq_apply]
  all_goals try exact Complex.normSq_nonneg _
  nlinarith

theorem norm_add_liLocalOffLineNodeConj_ofReal_lower (v : ℝ) (hv : 0 ≤ v) :
    5 / 4 ≤ ‖(v : ℂ) + liLocalOffLineNodeConj‖ := by
  rw [Complex.norm_def]
  rw [Real.le_sqrt (by norm_num)]
  simp [liLocalOffLineNodeConj, Complex.normSq_apply]
  all_goals try exact Complex.normSq_nonneg _
  nlinarith

theorem norm_liLocalRadialSignedJet_offPlus_le (m : ℕ) {v : ℝ}
    (hv : 0 ≤ v) (hv4 : v ≤ 1 / 4) :
    ‖liLocalRadialSignedJet liLocalOffLineNode m v‖ ≤
      ((m + 1).factorial : ℝ) * (5 / 4) * (3 * ((m + 1 : ℕ) : ℝ) / 2) /
        (5 / 4) ^ (m + 3) := by
  have hk : (1 : ℝ) ≤ ((m + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (by omega)
  have hknorm : ‖((m + 1 : ℕ) : ℂ)‖ = ((m + 1 : ℕ) : ℝ) := by
    rw [show ((m + 1 : ℕ) : ℂ) = ((((m + 1 : ℕ) : ℝ) : ℂ)) by norm_cast,
      Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  have hnum : ‖(((m + 1 : ℕ) : ℂ) * liLocalOffLineNode - (v : ℂ))‖ ≤
      3 * ((m + 1 : ℕ) : ℝ) / 2 := by
    calc
      ‖(((m + 1 : ℕ) : ℂ) * liLocalOffLineNode - (v : ℂ))‖ ≤
          ‖(((m + 1 : ℕ) : ℂ) * liLocalOffLineNode)‖ + ‖(v : ℂ)‖ := norm_sub_le _ _
      _ = ((m + 1 : ℕ) : ℝ) * (5 / 4) + v := by
        rw [norm_mul, hknorm, norm_liLocalOffLineNode, Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg hv]
      _ ≤ 3 * ((m + 1 : ℕ) : ℝ) / 2 := by nlinarith
  have hden : (5 / 4 : ℝ) ^ (m + 3) ≤
      ‖(v : ℂ) + liLocalOffLineNode‖ ^ (m + 3) :=
    pow_le_pow_left₀ (by norm_num) (norm_add_liLocalOffLineNode_ofReal_lower v hv) _
  rw [liLocalRadialSignedJet, norm_div, norm_mul, norm_mul, norm_pow, norm_liLocalOffLineNode]
  norm_num
  gcongr
  simpa only [Nat.cast_add, Nat.cast_one] using hnum

theorem norm_liLocalRadialSignedJet_offMinus_le (m : ℕ) {v : ℝ}
    (hv : 0 ≤ v) (hv4 : v ≤ 1 / 4) :
    ‖liLocalRadialSignedJet liLocalOffLineNodeConj m v‖ ≤
      ((m + 1).factorial : ℝ) * (5 / 4) * (3 * ((m + 1 : ℕ) : ℝ) / 2) /
        (5 / 4) ^ (m + 3) := by
  have hk : (1 : ℝ) ≤ ((m + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (by omega)
  have hknorm : ‖((m + 1 : ℕ) : ℂ)‖ = ((m + 1 : ℕ) : ℝ) := by
    rw [show ((m + 1 : ℕ) : ℂ) = ((((m + 1 : ℕ) : ℝ) : ℂ)) by norm_cast,
      Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  have hnum : ‖(((m + 1 : ℕ) : ℂ) * liLocalOffLineNodeConj - (v : ℂ))‖ ≤
      3 * ((m + 1 : ℕ) : ℝ) / 2 := by
    calc
      ‖(((m + 1 : ℕ) : ℂ) * liLocalOffLineNodeConj - (v : ℂ))‖ ≤
          ‖(((m + 1 : ℕ) : ℂ) * liLocalOffLineNodeConj)‖ + ‖(v : ℂ)‖ := norm_sub_le _ _
      _ = ((m + 1 : ℕ) : ℝ) * (5 / 4) + v := by
        rw [norm_mul, hknorm, norm_liLocalOffLineNodeConj, Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg hv]
      _ ≤ 3 * ((m + 1 : ℕ) : ℝ) / 2 := by nlinarith
  have hden : (5 / 4 : ℝ) ^ (m + 3) ≤
      ‖(v : ℂ) + liLocalOffLineNodeConj‖ ^ (m + 3) :=
    pow_le_pow_left₀ (by norm_num) (norm_add_liLocalOffLineNodeConj_ofReal_lower v hv) _
  rw [liLocalRadialSignedJet, norm_div, norm_mul, norm_mul, norm_pow, norm_liLocalOffLineNodeConj]
  norm_num
  gcongr
  simpa only [Nat.cast_add, Nat.cast_one] using hnum

theorem liLocalRadialSignedJet_base_lower (m : ℕ) {v : ℝ}
    (hv : 0 ≤ v) (hv4 : v ≤ 1 / 4) :
    ((m + 1).factorial : ℝ) * (((m + 1 : ℕ) : ℝ) / 8) /
        (3 / 4) ^ (m + 3) ≤
      (liLocalRadialSignedJet liLocalOnLineNode m v).re := by
  rw [liLocalRadialSignedJet_base_re m v hv]
  have hk : (1 : ℝ) ≤ ((m + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (by omega)
  have hnum : ((m + 1 : ℕ) : ℝ) / 4 ≤ ((m + 1 : ℕ) : ℝ) / 2 - v := by
    nlinarith
  have hbase : 0 < v + 1 / 2 := by linarith
  have hden : (v + 1 / 2) ^ (m + 3) ≤ (3 / 4 : ℝ) ^ (m + 3) := by
    gcongr
    linarith
  have hnpos : 0 ≤ ((m + 1 : ℕ) : ℝ) / 2 - v := by
    have : 0 ≤ ((m + 1 : ℕ) : ℝ) / 4 := by positivity
    linarith
  calc
    ((m + 1).factorial : ℝ) * (((m + 1 : ℕ) : ℝ) / 8) /
          (3 / 4) ^ (m + 3) =
        ((m + 1).factorial : ℝ) * (1 / 2) * (((m + 1 : ℕ) : ℝ) / 4) /
          (3 / 4) ^ (m + 3) := by ring
    _ ≤ ((m + 1).factorial : ℝ) * (1 / 2) *
          (((m + 1 : ℕ) : ℝ) / 2 - v) / (v + 1 / 2) ^ (m + 3) := by
      gcongr

theorem liLocal_two_mul_offUpper_lt_seven_mul_baseLower (m : ℕ) :
    2 * (((m + 1).factorial : ℝ) * (5 / 4) *
          (3 * ((m + 1 : ℕ) : ℝ) / 2) / (5 / 4) ^ (m + 3)) <
      7 * (((m + 1).factorial : ℝ) * (((m + 1 : ℕ) : ℝ) / 8) /
        (3 / 4) ^ (m + 3)) := by
  have hpow : (3 / 5 : ℝ) ^ (m + 3) ≤ (3 / 5 : ℝ) ^ (3 : ℕ) := by
    apply pow_le_pow_of_le_one (by norm_num) (by norm_num)
    omega
  have hthirty : 30 * (3 / 5 : ℝ) ^ (m + 3) < 7 := by
    calc
      30 * (3 / 5 : ℝ) ^ (m + 3) ≤ 30 * (3 / 5 : ℝ) ^ (3 : ℕ) := by gcongr
      _ < 7 := by norm_num
  have hA : 0 < (3 / 4 : ℝ) ^ (m + 3) := by positivity
  have hB : 0 < (5 / 4 : ℝ) ^ (m + 3) := by positivity
  have hratio : (3 / 4 : ℝ) ^ (m + 3) / (5 / 4 : ℝ) ^ (m + 3) =
      (3 / 5 : ℝ) ^ (m + 3) := by
    rw [← div_pow]
    norm_num
  have hquot : 30 * (3 / 4 : ℝ) ^ (m + 3) / (5 / 4 : ℝ) ^ (m + 3) < 7 := by
    rw [show 30 * (3 / 4 : ℝ) ^ (m + 3) / (5 / 4 : ℝ) ^ (m + 3) =
      30 * ((3 / 4 : ℝ) ^ (m + 3) / (5 / 4 : ℝ) ^ (m + 3)) by ring,
      hratio]
    exact hthirty
  have hcross : 30 * (3 / 4 : ℝ) ^ (m + 3) <
      7 * (5 / 4 : ℝ) ^ (m + 3) := (div_lt_iff₀ hB).mp hquot
  have hcore : (15 / 4 : ℝ) / (5 / 4) ^ (m + 3) <
      (7 / 8 : ℝ) / (3 / 4) ^ (m + 3) := by
    rw [div_lt_div_iff₀ hB hA]
    nlinarith
  have hF : 0 < ((m + 1).factorial : ℝ) * ((m + 1 : ℕ) : ℝ) := by positivity
  have hscaled := mul_lt_mul_of_pos_left hcore hF
  calc
    2 * (((m + 1).factorial : ℝ) * (5 / 4) *
          (3 * ((m + 1 : ℕ) : ℝ) / 2) / (5 / 4) ^ (m + 3)) =
        (((m + 1).factorial : ℝ) * ((m + 1 : ℕ) : ℝ)) *
          ((15 / 4 : ℝ) / (5 / 4) ^ (m + 3)) := by ring
    _ < (((m + 1).factorial : ℝ) * ((m + 1 : ℕ) : ℝ)) *
          ((7 / 8 : ℝ) / (3 / 4) ^ (m + 3)) := hscaled
    _ = 7 * (((m + 1).factorial : ℝ) * (((m + 1 : ℕ) : ℝ) / 8) /
        (3 / 4) ^ (m + 3)) := by ring

theorem signedJetCounterexample_pos (m : ℕ) {v : ℝ}
    (hv : 0 ≤ v) (hv4 : v ≤ 1 / 4) :
    0 < (7 * liLocalRadialSignedJet liLocalOnLineNode m v +
      liLocalRadialSignedJet liLocalOffLineNode m v + liLocalRadialSignedJet liLocalOffLineNodeConj m v).re := by
  let L : ℝ := ((m + 1).factorial : ℝ) * (((m + 1 : ℕ) : ℝ) / 8) /
    (3 / 4) ^ (m + 3)
  let U : ℝ := ((m + 1).factorial : ℝ) * (5 / 4) *
    (3 * ((m + 1 : ℕ) : ℝ) / 2) / (5 / 4) ^ (m + 3)
  have hb : L ≤ (liLocalRadialSignedJet liLocalOnLineNode m v).re :=
    liLocalRadialSignedJet_base_lower m hv hv4
  have hp : ‖liLocalRadialSignedJet liLocalOffLineNode m v‖ ≤ U :=
    norm_liLocalRadialSignedJet_offPlus_le m hv hv4
  have hm : ‖liLocalRadialSignedJet liLocalOffLineNodeConj m v‖ ≤ U :=
    norm_liLocalRadialSignedJet_offMinus_le m hv hv4
  have hpair : |(liLocalRadialSignedJet liLocalOffLineNode m v +
      liLocalRadialSignedJet liLocalOffLineNodeConj m v).re| ≤ 2 * U := by
    calc
      |(liLocalRadialSignedJet liLocalOffLineNode m v + liLocalRadialSignedJet liLocalOffLineNodeConj m v).re| ≤
          ‖liLocalRadialSignedJet liLocalOffLineNode m v + liLocalRadialSignedJet liLocalOffLineNodeConj m v‖ :=
        Complex.abs_re_le_norm _
      _ ≤ ‖liLocalRadialSignedJet liLocalOffLineNode m v‖ + ‖liLocalRadialSignedJet liLocalOffLineNodeConj m v‖ :=
        norm_add_le _ _
      _ ≤ U + U := add_le_add hp hm
      _ = 2 * U := by ring
  have hdom : 2 * U < 7 * L := liLocal_two_mul_offUpper_lt_seven_mul_baseLower m
  have hpairlower : -2 * U ≤
      (liLocalRadialSignedJet liLocalOffLineNode m v + liLocalRadialSignedJet liLocalOffLineNodeConj m v).re := by
    linarith [neg_abs_le (liLocalRadialSignedJet liLocalOffLineNode m v + liLocalRadialSignedJet liLocalOffLineNodeConj m v).re]
  have hpairlower' : -2 * U ≤
      (liLocalRadialSignedJet liLocalOffLineNode m v).re + (liLocalRadialSignedJet liLocalOffLineNodeConj m v).re := by
    simpa only [Complex.add_re] using hpairlower
  simp only [Complex.add_re, Complex.mul_re]
  norm_num
  linarith

theorem negOnePow_mul_iteratedDeriv_liLocalRadialAtom (b : ℂ) (m : ℕ) (v : ℝ)
    (hz : (v : ℂ) + b ≠ 0) :
    (-1 : ℂ) ^ m * iteratedDeriv (m + 1) (liLocalRadialAtom b) (v : ℂ) =
      liLocalRadialSignedJet b m v := by
  rw [iteratedDeriv_liLocalRadialAtom b m (v : ℂ) hz]
  have hsign : (-1 : ℂ) ^ m * (-1 : ℂ) ^ m = 1 := by
    rw [← pow_add, ← two_mul, pow_mul]
    norm_num
  rw [liLocalRadialSignedJet]
  calc
    (-1 : ℂ) ^ m *
        ((-1 : ℂ) ^ m * ((m + 1).factorial : ℂ) * b *
          (((m + 1 : ℕ) : ℂ) * b - (v : ℂ)) / ((v : ℂ) + b) ^ (m + 3)) =
      ((-1 : ℂ) ^ m * (-1 : ℂ) ^ m) *
        (((m + 1).factorial : ℂ) * b *
          (((m + 1 : ℕ) : ℂ) * b - (v : ℂ)) / ((v : ℂ) + b) ^ (m + 3)) := by ring
    _ = ((m + 1).factorial : ℂ) * b *
          (((m + 1 : ℕ) : ℂ) * b - (v : ℂ)) / ((v : ℂ) + b) ^ (m + 3) := by
      rw [hsign, one_mul]

def liLocalBernsteinComplexResponse (z : ℂ) : ℂ :=
  7 * liLocalRadialAtom liLocalOnLineNode z + liLocalRadialAtom liLocalOffLineNode z + liLocalRadialAtom liLocalOffLineNodeConj z

def liLocalBernsteinResponse (v : ℝ) : ℝ := (liLocalBernsteinComplexResponse v).re

theorem add_liLocalOnLineNode_ne_zero {v : ℝ} (hv : -(1 / 2) < v) :
    (v : ℂ) + liLocalOnLineNode ≠ 0 := by
  intro h
  have hr := congrArg Complex.re h
  simp [liLocalOnLineNode] at hr
  linarith

theorem add_liLocalOffLineNode_ne_zero (v : ℝ) : (v : ℂ) + liLocalOffLineNode ≠ 0 := by
  intro h
  have hi := congrArg Complex.im h
  norm_num [liLocalOffLineNode] at hi

theorem add_liLocalOffLineNodeConj_ne_zero (v : ℝ) : (v : ℂ) + liLocalOffLineNodeConj ≠ 0 := by
  intro h
  have hi := congrArg Complex.im h
  norm_num [liLocalOffLineNodeConj] at hi

theorem contDiffAt_liLocalRadialAtom (b z : ℂ) (hz : z + b ≠ 0) (n : ℕ∞) :
    ContDiffAt ℂ n (liLocalRadialAtom b) z := by
  exact (contDiffAt_id.mul contDiffAt_const).div
    ((contDiffAt_id.add contDiffAt_const).pow 2) (pow_ne_zero 2 hz)

theorem signed_iteratedDeriv_liLocalBernsteinComplexResponse (m : ℕ) {v : ℝ}
    (hv : -(1 / 2) < v) :
    (-1 : ℂ) ^ m * iteratedDeriv (m + 1) liLocalBernsteinComplexResponse (v : ℂ) =
      7 * liLocalRadialSignedJet liLocalOnLineNode m v + liLocalRadialSignedJet liLocalOffLineNode m v +
        liLocalRadialSignedJet liLocalOffLineNodeConj m v := by
  have h0 := add_liLocalOnLineNode_ne_zero hv
  have hp := add_liLocalOffLineNode_ne_zero v
  have hm := add_liLocalOffLineNodeConj_ne_zero v
  have hc0 := contDiffAt_liLocalRadialAtom liLocalOnLineNode (v : ℂ) h0 (m + 1)
  have hcp := contDiffAt_liLocalRadialAtom liLocalOffLineNode (v : ℂ) hp (m + 1)
  have hcm := contDiffAt_liLocalRadialAtom liLocalOffLineNodeConj (v : ℂ) hm (m + 1)
  have h7 : ContDiffAt ℂ (m + 1) (fun z => 7 * liLocalRadialAtom liLocalOnLineNode z) (v : ℂ) :=
    contDiffAt_const.mul hc0
  change (-1 : ℂ) ^ m * iteratedDeriv (m + 1)
      (fun z => (7 * liLocalRadialAtom liLocalOnLineNode z + liLocalRadialAtom liLocalOffLineNode z) +
        liLocalRadialAtom liLocalOffLineNodeConj z) (v : ℂ) = _
  rw [show (fun z => (7 * liLocalRadialAtom liLocalOnLineNode z + liLocalRadialAtom liLocalOffLineNode z) +
      liLocalRadialAtom liLocalOffLineNodeConj z) =
      (((fun z => 7 * liLocalRadialAtom liLocalOnLineNode z) + liLocalRadialAtom liLocalOffLineNode) +
        liLocalRadialAtom liLocalOffLineNodeConj) by rfl]
  have hsplit0 : iteratedDeriv (m + 1)
      (fun z => 7 * liLocalRadialAtom liLocalOnLineNode z + liLocalRadialAtom liLocalOffLineNode z) (v : ℂ) =
      iteratedDeriv (m + 1) (fun z => 7 * liLocalRadialAtom liLocalOnLineNode z) (v : ℂ) +
        iteratedDeriv (m + 1) (liLocalRadialAtom liLocalOffLineNode) (v : ℂ) := by
    rw [show (fun z => 7 * liLocalRadialAtom liLocalOnLineNode z + liLocalRadialAtom liLocalOffLineNode z) =
      (fun z => 7 * liLocalRadialAtom liLocalOnLineNode z) + liLocalRadialAtom liLocalOffLineNode by rfl]
    exact iteratedDeriv_add h7 hcp
  have hsplit : iteratedDeriv (m + 1)
      (fun z => (7 * liLocalRadialAtom liLocalOnLineNode z + liLocalRadialAtom liLocalOffLineNode z) +
        liLocalRadialAtom liLocalOffLineNodeConj z) (v : ℂ) =
      iteratedDeriv (m + 1)
          (fun z => 7 * liLocalRadialAtom liLocalOnLineNode z + liLocalRadialAtom liLocalOffLineNode z) (v : ℂ) +
        iteratedDeriv (m + 1) (liLocalRadialAtom liLocalOffLineNodeConj) (v : ℂ) := by
    rw [show (fun z => (7 * liLocalRadialAtom liLocalOnLineNode z + liLocalRadialAtom liLocalOffLineNode z) +
        liLocalRadialAtom liLocalOffLineNodeConj z) =
      (fun z => 7 * liLocalRadialAtom liLocalOnLineNode z + liLocalRadialAtom liLocalOffLineNode z) +
        liLocalRadialAtom liLocalOffLineNodeConj by rfl]
    exact iteratedDeriv_add (h7.add hcp) hcm
  rw [show iteratedDeriv (m + 1)
      (((fun z => 7 * liLocalRadialAtom liLocalOnLineNode z) + liLocalRadialAtom liLocalOffLineNode) +
        liLocalRadialAtom liLocalOffLineNodeConj) (v : ℂ) =
      iteratedDeriv (m + 1)
        (fun z => (7 * liLocalRadialAtom liLocalOnLineNode z + liLocalRadialAtom liLocalOffLineNode z) +
          liLocalRadialAtom liLocalOffLineNodeConj z) (v : ℂ) by rfl,
    hsplit, hsplit0]
  rw [iteratedDeriv_const_mul 7 hc0]
  calc
    (-1 : ℂ) ^ m *
        (7 * iteratedDeriv (m + 1) (liLocalRadialAtom liLocalOnLineNode) (v : ℂ) +
          iteratedDeriv (m + 1) (liLocalRadialAtom liLocalOffLineNode) (v : ℂ) +
          iteratedDeriv (m + 1) (liLocalRadialAtom liLocalOffLineNodeConj) (v : ℂ)) =
      7 * ((-1 : ℂ) ^ m * iteratedDeriv (m + 1) (liLocalRadialAtom liLocalOnLineNode) (v : ℂ)) +
        ((-1 : ℂ) ^ m * iteratedDeriv (m + 1) (liLocalRadialAtom liLocalOffLineNode) (v : ℂ)) +
        ((-1 : ℂ) ^ m * iteratedDeriv (m + 1) (liLocalRadialAtom liLocalOffLineNodeConj) (v : ℂ)) := by ring
    _ = 7 * liLocalRadialSignedJet liLocalOnLineNode m v + liLocalRadialSignedJet liLocalOffLineNode m v +
        liLocalRadialSignedJet liLocalOffLineNodeConj m v := by
      rw [negOnePow_mul_iteratedDeriv_liLocalRadialAtom liLocalOnLineNode m v h0,
        negOnePow_mul_iteratedDeriv_liLocalRadialAtom liLocalOffLineNode m v hp,
        negOnePow_mul_iteratedDeriv_liLocalRadialAtom liLocalOffLineNodeConj m v hm]

theorem analyticAt_liLocalRadialAtom (b z : ℂ) (hz : z + b ≠ 0) :
    AnalyticAt ℂ (liLocalRadialAtom b) z := by
  exact (analyticAt_id.mul analyticAt_const).div
    ((analyticAt_id.add analyticAt_const).pow 2) (pow_ne_zero 2 hz)

theorem analyticAt_liLocalBernsteinComplexResponse_of_gt {v : ℝ} (hv : -(1 / 2) < v) :
    AnalyticAt ℂ liLocalBernsteinComplexResponse (v : ℂ) := by
  have h0 := analyticAt_liLocalRadialAtom liLocalOnLineNode (v : ℂ) (add_liLocalOnLineNode_ne_zero hv)
  have hp := analyticAt_liLocalRadialAtom liLocalOffLineNode (v : ℂ) (add_liLocalOffLineNode_ne_zero v)
  have hm := analyticAt_liLocalRadialAtom liLocalOffLineNodeConj (v : ℂ) (add_liLocalOffLineNodeConj_ne_zero v)
  exact ((analyticAt_const.mul h0).add hp).add hm

theorem iteratedDeriv_re_comp_ofReal_of_analyticAt {F : ℂ → ℂ} {T : ℝ}
    (hF : ∀ t : ℝ, T < t → AnalyticAt ℂ F (t : ℂ)) :
    ∀ (n : ℕ) {x : ℝ}, T < x →
      iteratedDeriv n (fun y : ℝ => (F (y : ℂ)).re) x =
        (iteratedDeriv n F (x : ℂ)).re := by
  intro n
  induction n with
  | zero =>
      intro x hx
      simp
  | succ n ih =>
      intro x hx
      rw [iteratedDeriv_succ]
      have hEq : iteratedDeriv n (fun y : ℝ => (F (y : ℂ)).re) =ᶠ[𝓝 x]
          fun y => (iteratedDeriv n F (y : ℂ)).re := by
        filter_upwards [Ioi_mem_nhds hx] with y hy
        exact ih hy
      rw [hEq.deriv_eq]
      have han := GaloisForLFunctions.RHTower.analyticAt_iteratedDeriv_complex (hF x hx) n
      have hdc : HasDerivAt (fun y : ℝ => iteratedDeriv n F (y : ℂ))
          (deriv (iteratedDeriv n F) (x : ℂ)) x :=
        HasDerivAt.comp_ofReal han.differentiableAt.hasDerivAt
      have hdr := (Complex.reCLM.hasFDerivAt).comp_hasDerivAt x hdc
      rw [show deriv (fun y : ℝ => (iteratedDeriv n F (y : ℂ)).re) x =
          (deriv (iteratedDeriv n F) (x : ℂ)).re by
        rw [show (fun y : ℝ => (iteratedDeriv n F (y : ℂ)).re) =
          Complex.reCLM ∘ (fun y : ℝ => iteratedDeriv n F (y : ℂ)) by rfl]
        exact hdr.deriv]
      rw [← iteratedDeriv_succ]

theorem contDiffOn_liLocalBernsteinComplexResponse_comp_ofReal :
    ContDiffOn ℝ (⊤ : ℕ∞) (fun v : ℝ => liLocalBernsteinComplexResponse (v : ℂ)) (Ioi (-(1 / 2))) :=
  HTGeometry.contDiffOn_comp_ofReal_of_analyticAt fun _ hv =>
    analyticAt_liLocalBernsteinComplexResponse_of_gt hv

theorem iteratedDeriv_liLocalBernsteinResponse (n : ℕ) {v : ℝ} (hv : -(1 / 2) < v) :
    iteratedDeriv n liLocalBernsteinResponse v =
      (iteratedDeriv n liLocalBernsteinComplexResponse (v : ℂ)).re := by
  exact iteratedDeriv_re_comp_ofReal_of_analyticAt
    (T := -(1 / 2)) (fun t ht => analyticAt_liLocalBernsteinComplexResponse_of_gt ht) n hv

theorem alternating_iteratedDeriv_liLocalBernsteinResponse_pos (m : ℕ) {v : ℝ}
    (hv : 0 ≤ v) (hv4 : v ≤ 1 / 4) :
    0 < (-1 : ℝ) ^ m * iteratedDeriv (m + 1) liLocalBernsteinResponse v := by
  rw [iteratedDeriv_liLocalBernsteinResponse (m + 1) (by linarith)]
  have hcomplex := signed_iteratedDeriv_liLocalBernsteinComplexResponse m (v := v) (by linarith)
  have hre := congrArg Complex.re hcomplex
  have hpos := signedJetCounterexample_pos m hv hv4
  rw [← hcomplex] at hpos
  have hsigncast : (-1 : ℂ) ^ m = (((-1 : ℝ) ^ m : ℝ) : ℂ) := by
    calc
      (-1 : ℂ) ^ m = (((-1 : ℝ) : ℂ)) ^ m := by norm_num
      _ = (((-1 : ℝ) ^ m : ℝ) : ℂ) := (Complex.ofReal_pow _ _).symm
  have hsignre : ((-1 : ℂ) ^ m).re = (-1 : ℝ) ^ m := by rw [hsigncast]; rfl
  have hsignim : ((-1 : ℂ) ^ m).im = 0 := by
    calc
      ((-1 : ℂ) ^ m).im = (((( -1 : ℝ) ^ m : ℝ) : ℂ)).im :=
        congrArg Complex.im hsigncast
      _ = 0 := Complex.ofReal_im _
  simpa only [Complex.mul_re, hsignre, hsignim, zero_mul, sub_zero] using hpos

def StrictBernsteinOnLIInterval (f : ℝ → ℝ) : Prop :=
  (∀ v ∈ Icc (0 : ℝ) (1 / 4), 0 ≤ f v) ∧
    ∀ m : ℕ, ∀ v ∈ Icc (0 : ℝ) (1 / 4),
      0 < (-1 : ℝ) ^ m * iteratedDeriv (m + 1) f v

theorem liLocalBernsteinResponse_zero : liLocalBernsteinResponse 0 = 0 := by
  norm_num [liLocalBernsteinResponse, liLocalBernsteinComplexResponse, liLocalRadialAtom]

theorem strictMonoOn_liLocalBernsteinResponse :
    StrictMonoOn liLocalBernsteinResponse (Icc (0 : ℝ) (1 / 4)) := by
  apply strictMonoOn_of_deriv_pos (D := Icc (0 : ℝ) (1 / 4))
    (convex_Icc (0 : ℝ) (1 / 4))
  · have hc : ContinuousOn (fun v : ℝ => liLocalBernsteinComplexResponse (v : ℂ))
        (Icc (0 : ℝ) (1 / 4)) :=
      contDiffOn_liLocalBernsteinComplexResponse_comp_ofReal.continuousOn.mono
        (by intro x hx; simp only [mem_Ioi]; linarith [hx.1])
    change ContinuousOn (fun v : ℝ => (liLocalBernsteinComplexResponse (v : ℂ)).re)
      (Icc (0 : ℝ) (1 / 4))
    exact Complex.continuous_re.continuousOn.comp hc (mapsTo_univ _ _)
  · intro v hv
    rw [interior_Icc] at hv
    rw [← iteratedDeriv_one]
    simpa using alternating_iteratedDeriv_liLocalBernsteinResponse_pos 0
      (le_of_lt hv.1) (le_of_lt hv.2)

theorem strictBernsteinOnLIInterval_liLocalBernsteinResponse :
    StrictBernsteinOnLIInterval liLocalBernsteinResponse := by
  constructor
  · intro v hv
    by_cases hzero : v = 0
    · rw [hzero, liLocalBernsteinResponse_zero]
    · have hvpos : 0 < v := lt_of_le_of_ne hv.1 (Ne.symm hzero)
      have hlt := strictMonoOn_liLocalBernsteinResponse (by constructor <;> norm_num) hv hvpos
      rw [liLocalBernsteinResponse_zero] at hlt
      exact le_of_lt hlt
  · intro m v hv
    exact alternating_iteratedDeriv_liLocalBernsteinResponse_pos m hv.1 hv.2

theorem evalRealPolynomial_chebyshevT_eq (n : ℤ) (z : ℂ) :
    evalRealPolynomial (Polynomial.Chebyshev.T ℝ n) z =
      (Polynomial.Chebyshev.T ℂ n).eval z := by
  simp [evalRealPolynomial]

def liLocalCompletedAbelModeAtom (n : ℕ) (v : ℝ) (b : ℂ) : ℂ :=
  (1 - evalRealPolynomial
    (Polynomial.Chebyshev.T ℝ (2 * ((n : ℤ) + 1)))
      (((v : ℂ) - b) / ((v : ℂ) + b))) / 4

def liLocalCompletedAbelEndpointMode (n : ℕ) : ℂ :=
  7 * liLocalCompletedAbelModeAtom n (1 / 4) liLocalOnLineNode +
    liLocalCompletedAbelModeAtom n (1 / 4) liLocalOffLineNode +
    liLocalCompletedAbelModeAtom n (1 / 4) liLocalOffLineNodeConj

def liLocalCayleyPhasePlus : ℂ := -1 - I

def liLocalCayleyPhaseMinus : ℂ := -1 + I

theorem liLocalCayleyPhasePlus_ne_zero : liLocalCayleyPhasePlus ≠ 0 := by
  intro h
  have hi := congrArg Complex.im h
  norm_num [liLocalCayleyPhasePlus] at hi

theorem liLocalCayleyPhaseMinus_ne_zero : liLocalCayleyPhaseMinus ≠ 0 := by
  intro h
  have hi := congrArg Complex.im h
  norm_num [liLocalCayleyPhaseMinus] at hi

theorem liLocalCayleyPhasePlus_pow_eight : liLocalCayleyPhasePlus ^ (8 : ℕ) = 16 := by
  have hsq : liLocalCayleyPhasePlus ^ (2 : ℕ) = 2 * I := by
    calc
      liLocalCayleyPhasePlus ^ (2 : ℕ) = 1 + 2 * I + I ^ (2 : ℕ) := by
        simp only [liLocalCayleyPhasePlus]
        ring
      _ = 2 * I := by linear_combination Complex.I_sq
  have hfour : (2 * I : ℂ) ^ (4 : ℕ) = 16 := by
    calc
      (2 * I : ℂ) ^ (4 : ℕ) = ((2 * I : ℂ) ^ (2 : ℕ)) ^ (2 : ℕ) := by ring
      _ = (-4 : ℂ) ^ (2 : ℕ) := by
        rw [show (2 * I : ℂ) ^ (2 : ℕ) = -4 by
          rw [pow_two]
          linear_combination 4 * Complex.I_sq]
      _ = 16 := by norm_num
  rw [show liLocalCayleyPhasePlus ^ (8 : ℕ) = (liLocalCayleyPhasePlus ^ (2 : ℕ)) ^ (4 : ℕ) by ring, hsq]
  exact hfour

theorem liLocalCayleyPhaseMinus_pow_eight : liLocalCayleyPhaseMinus ^ (8 : ℕ) = 16 := by
  have hsq : liLocalCayleyPhaseMinus ^ (2 : ℕ) = -(2 * I) := by
    calc
      liLocalCayleyPhaseMinus ^ (2 : ℕ) = 1 - 2 * I + I ^ (2 : ℕ) := by
        simp only [liLocalCayleyPhaseMinus]
        ring
      _ = -(2 * I) := by linear_combination Complex.I_sq
  have hfour : (-(2 * I) : ℂ) ^ (4 : ℕ) = 16 := by
    calc
      (-(2 * I) : ℂ) ^ (4 : ℕ) = ((-(2 * I) : ℂ) ^ (2 : ℕ)) ^ (2 : ℕ) := by ring
      _ = (-4 : ℂ) ^ (2 : ℕ) := by
        rw [show (-(2 * I) : ℂ) ^ (2 : ℕ) = -4 by
          rw [pow_two]
          linear_combination 4 * Complex.I_sq]
      _ = 16 := by norm_num
  rw [show liLocalCayleyPhaseMinus ^ (8 : ℕ) = (liLocalCayleyPhaseMinus ^ (2 : ℕ)) ^ (4 : ℕ) by ring, hsq]
  exact hfour

theorem liLocalOffLineNode_endpoint_coordinate :
    (((1 / 4 : ℝ) : ℂ) - liLocalOffLineNode) /
        (((1 / 4 : ℝ) : ℂ) + liLocalOffLineNode) =
      (liLocalCayleyPhasePlus + liLocalCayleyPhasePlus⁻¹) / 2 := by
  apply Complex.ext <;>
    norm_num [liLocalOffLineNode, liLocalCayleyPhasePlus, Complex.div_re, Complex.div_im,
      Complex.inv_re, Complex.inv_im, Complex.normSq_apply]

theorem liLocalOffLineNodeConj_endpoint_coordinate :
    (((1 / 4 : ℝ) : ℂ) - liLocalOffLineNodeConj) /
        (((1 / 4 : ℝ) : ℂ) + liLocalOffLineNodeConj) =
      (liLocalCayleyPhaseMinus + liLocalCayleyPhaseMinus⁻¹) / 2 := by
  apply Complex.ext <;>
    norm_num [liLocalOffLineNodeConj, liLocalCayleyPhaseMinus, Complex.div_re, Complex.div_im,
      Complex.inv_re, Complex.inv_im, Complex.normSq_apply]

theorem evalRealPolynomial_chebyshevT_eight_liLocalOffLineNode :
    evalRealPolynomial (Polynomial.Chebyshev.T ℝ 8)
      ((((1 / 4 : ℝ) : ℂ) - liLocalOffLineNode) /
        (((1 / 4 : ℝ) : ℂ) + liLocalOffLineNode)) = 257 / 32 := by
  rw [evalRealPolynomial_chebyshevT_eq, liLocalOffLineNode_endpoint_coordinate]
  have h := GaloisForLFunctions.two_mul_chebyshevT_eval_half_add_inv
    8 liLocalCayleyPhasePlus_ne_zero
  have hinv : liLocalCayleyPhasePlus⁻¹ ^ (8 : ℕ) = 1 / 16 := by
    rw [inv_pow, liLocalCayleyPhasePlus_pow_eight]
    norm_num
  rw [liLocalCayleyPhasePlus_pow_eight, hinv] at h
  apply (eq_div_iff (by norm_num : (32 : ℂ) ≠ 0)).2
  linear_combination 16 * h

theorem evalRealPolynomial_chebyshevT_eight_liLocalOffLineNodeConj :
    evalRealPolynomial (Polynomial.Chebyshev.T ℝ 8)
      ((((1 / 4 : ℝ) : ℂ) - liLocalOffLineNodeConj) /
        (((1 / 4 : ℝ) : ℂ) + liLocalOffLineNodeConj)) = 257 / 32 := by
  rw [evalRealPolynomial_chebyshevT_eq, liLocalOffLineNodeConj_endpoint_coordinate]
  have h := GaloisForLFunctions.two_mul_chebyshevT_eval_half_add_inv
    8 liLocalCayleyPhaseMinus_ne_zero
  have hinv : liLocalCayleyPhaseMinus⁻¹ ^ (8 : ℕ) = 1 / 16 := by
    rw [inv_pow, liLocalCayleyPhaseMinus_pow_eight]
    norm_num
  rw [liLocalCayleyPhaseMinus_pow_eight, hinv] at h
  apply (eq_div_iff (by norm_num : (32 : ℂ) ≠ 0)).2
  linear_combination 16 * h

theorem evalRealPolynomial_chebyshevT_eight_neg_third :
    evalRealPolynomial (Polynomial.Chebyshev.T ℝ 8) (-(1 / 3 : ℝ) : ℂ) =
      -(5983 / 6561 : ℝ) := by
  let x : ℂ := (-(1 / 3 : ℝ) : ℂ)
  have hrec (n : ℤ) :
      evalRealPolynomial (Polynomial.Chebyshev.T ℝ (n + 2)) x =
        2 * x * evalRealPolynomial (Polynomial.Chebyshev.T ℝ (n + 1)) x -
          evalRealPolynomial (Polynomial.Chebyshev.T ℝ n) x := by
    rw [Polynomial.Chebyshev.T_add_two]
    simp [evalRealPolynomial]
  have h0 : evalRealPolynomial (Polynomial.Chebyshev.T ℝ 0) x = 1 := by
    simp [evalRealPolynomial]
  have h1 : evalRealPolynomial (Polynomial.Chebyshev.T ℝ 1) x = -(1 / 3 : ℝ) := by
    simp [x, evalRealPolynomial]
  have h2 : evalRealPolynomial (Polynomial.Chebyshev.T ℝ 2) x = -(7 / 9 : ℝ) := by
    rw [show (2 : ℤ) = 0 + 2 by norm_num, hrec, show (0 : ℤ) + 1 = 1 by norm_num,
      h0, h1]
    norm_num [x]
  have h3 : evalRealPolynomial (Polynomial.Chebyshev.T ℝ 3) x = 23 / 27 := by
    rw [show (3 : ℤ) = 1 + 2 by norm_num, hrec, show (1 : ℤ) + 1 = 2 by norm_num,
      h1, h2]
    norm_num [x]
  have h4 : evalRealPolynomial (Polynomial.Chebyshev.T ℝ 4) x = 17 / 81 := by
    rw [show (4 : ℤ) = 2 + 2 by norm_num, hrec, show (2 : ℤ) + 1 = 3 by norm_num,
      h2, h3]
    norm_num [x]
  have h5 : evalRealPolynomial (Polynomial.Chebyshev.T ℝ 5) x = -(241 / 243 : ℝ) := by
    rw [show (5 : ℤ) = 3 + 2 by norm_num, hrec, show (3 : ℤ) + 1 = 4 by norm_num,
      h3, h4]
    norm_num [x]
  have h6 : evalRealPolynomial (Polynomial.Chebyshev.T ℝ 6) x = 329 / 729 := by
    rw [show (6 : ℤ) = 4 + 2 by norm_num, hrec, show (4 : ℤ) + 1 = 5 by norm_num,
      h4, h5]
    norm_num [x]
  have h7 : evalRealPolynomial (Polynomial.Chebyshev.T ℝ 7) x = 1511 / 2187 := by
    rw [show (7 : ℤ) = 5 + 2 by norm_num, hrec, show (5 : ℤ) + 1 = 6 by norm_num,
      h5, h6]
    norm_num [x]
  rw [show (8 : ℤ) = 6 + 2 by norm_num, hrec, show (6 : ℤ) + 1 = 7 by norm_num,
    h6, h7]
  norm_num [x]

theorem liLocalOnLineNode_endpoint_coordinate :
    (((1 / 4 : ℝ) : ℂ) - liLocalOnLineNode) /
        (((1 / 4 : ℝ) : ℂ) + liLocalOnLineNode) = (-(1 / 3 : ℝ) : ℂ) := by
  norm_num [liLocalOnLineNode]

theorem liLocalCompletedAbelModeAtom_three_base :
    liLocalCompletedAbelModeAtom 3 (1 / 4) liLocalOnLineNode = (3136 / 6561 : ℝ) := by
  rw [liLocalCompletedAbelModeAtom]
  norm_num only [Nat.cast_ofNat, Int.reduceOfNat, Int.reduceAdd, Int.reduceMul]
  rw [liLocalOnLineNode_endpoint_coordinate, evalRealPolynomial_chebyshevT_eight_neg_third]
  norm_num

theorem liLocalCompletedAbelModeAtom_three_offPlus :
    liLocalCompletedAbelModeAtom 3 (1 / 4) liLocalOffLineNode = -(225 / 128 : ℝ) := by
  rw [liLocalCompletedAbelModeAtom]
  norm_num only [Nat.cast_ofNat, Int.reduceOfNat, Int.reduceAdd, Int.reduceMul]
  rw [evalRealPolynomial_chebyshevT_eight_liLocalOffLineNode]
  norm_num

theorem liLocalCompletedAbelModeAtom_three_offMinus :
    liLocalCompletedAbelModeAtom 3 (1 / 4) liLocalOffLineNodeConj = -(225 / 128 : ℝ) := by
  rw [liLocalCompletedAbelModeAtom]
  norm_num only [Nat.cast_ofNat, Int.reduceOfNat, Int.reduceAdd, Int.reduceMul]
  rw [evalRealPolynomial_chebyshevT_eight_liLocalOffLineNodeConj]
  norm_num

theorem liLocalCompletedAbelEndpointMode_three_re_neg : (liLocalCompletedAbelEndpointMode 3).re < 0 := by
  rw [liLocalCompletedAbelEndpointMode, liLocalCompletedAbelModeAtom_three_base, liLocalCompletedAbelModeAtom_three_offPlus,
    liLocalCompletedAbelModeAtom_three_offMinus]
  norm_num [Complex.mul_re, Complex.add_re]

theorem liLocalBernstein_counterexample_and_negative_fourthMode :
    StrictBernsteinOnLIInterval liLocalBernsteinResponse ∧ (liLocalCompletedAbelEndpointMode 3).re < 0 :=
  ⟨strictBernsteinOnLIInterval_liLocalBernsteinResponse, liLocalCompletedAbelEndpointMode_three_re_neg⟩

def LocalBernsteinShapeForcesEndpointModes : Prop :=
  StrictBernsteinOnLIInterval liLocalBernsteinResponse →
    ∀ n : ℕ, 0 ≤ (liLocalCompletedAbelEndpointMode n).re

theorem not_localBernsteinShapeForcesEndpointModes :
    ¬ LocalBernsteinShapeForcesEndpointModes := by
  intro h
  have hnonneg := h strictBernsteinOnLIInterval_liLocalBernsteinResponse 3
  linarith [liLocalCompletedAbelEndpointMode_three_re_neg]

end


end RHTower

