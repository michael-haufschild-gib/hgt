import GaloisForLFunctions.HTGeometry.MeromorphicPlaneReflection
import GaloisForLFunctions.RHTower.XiCriticalStripFactorRoots
import GaloisForLFunctions.HTGeometry.EntireOddDivisorSquareClass

/-!
# Divisors of the two functional-equation orientations

The reflected factors `F_n(1-s)` remain globally nonsquare and have odd zeros.
Their divisors are pairwise separated and disjoint from every original factor
with label at least two. A common zero would lie in the strip where the factors
are already proved nonvanishing. Reflection fixes the actual Xi field element.
-/

open Complex Filter Topology
noncomputable section
namespace RHTower.XiGlobalKummer
open GaloisForLFunctions.HTGeometry

def reflectedFactor (n : ℕ) (s : ℂ) : ℂ := deletionFactor n (1 - s)

theorem reflectedFactor_differentiable (n : ℕ) : Differentiable ℂ (reflectedFactor n) :=
  (deletionFactor_differentiable n).comp ((differentiable_const 1).sub differentiable_id)

def reflectedElement (n : ℕ) : K := planeReflectEquiv 1 (factorElement n)

theorem reflectedElement_eq_ofMeromorphic (n : ℕ) :
    reflectedElement n = ofMeromorphic (reflectedFactor n)
      (fun z => ((reflectedFactor_differentiable n).analyticAt z).meromorphicAt) := rfl

theorem planeReflectEquiv_xiElement : planeReflectEquiv 1 xiElement = xiElement := by
  rw [xiElement, planeReflectEquiv_ofMeromorphic]
  apply (ofMeromorphic_eq_iff _ _).mpr
  intro z
  exact Filter.Eventually.of_forall xi_one_sub

theorem reflectedElement_not_isSquare {n : ℕ} (hn : 2 ≤ n) :
    ¬ IsSquare (reflectedElement n) := by
  intro h
  have hh := h.map (planeReflectEquiv 1).toRingHom
  change IsSquare (planeReflectEquiv 1 (planeReflectEquiv 1 (factorElement n))) at hh
  rw [planeReflectEquiv_involutive 1 (factorElement n)] at hh
  exact factorElement_not_isSquare hn hh

theorem reflectedFactor_ne_zero_at_zero {n : ℕ} (hn : 1 ≤ n) : reflectedFactor n 0 ≠ 0 := by
  have h := deletionFactor_re_ge_half hn (s := 1) (by norm_num) (by norm_num)
  intro hz
  have hz' : deletionFactor n 1 = 0 := by simpa only [reflectedFactor, sub_zero] using hz
  rw [hz'] at h
  norm_num at h

theorem exists_odd_zero_reflectedFactor {n : ℕ} (hn : 2 ≤ n) :
    ∃ s : ℂ, reflectedFactor n s = 0 ∧
      Odd (analyticOrderAt (reflectedFactor n) s).toNat := by
  apply exists_odd_zero_of_not_isSquare_plane (reflectedFactor_differentiable n)
    (reflectedFactor_ne_zero_at_zero (by omega))
  rw [← reflectedElement_eq_ofMeromorphic]
  exact reflectedElement_not_isSquare hn

/-- Original and functionally reflected source factors have disjoint divisors. -/
theorem deletionFactor_ne_zero_of_reflectedFactor_zero {m n : ℕ} {s : ℂ}
    (hm : 2 ≤ m) (hn : 2 ≤ n) (hz : reflectedFactor n s = 0) :
    deletionFactor m s ≠ 0 := by
  intro hw
  have he₁ := deletionFactor_mul_exp m s
  rw [hw, zero_mul] at he₁
  have he₂ := deletionFactor_mul_exp n (1 - s)
  rw [show deletionFactor n (1 - s) = 0 from hz, zero_mul, xi_one_sub] at he₂
  have he : Complex.exp ((Real.log m : ℂ) * s) =
      Complex.exp ((Real.log n : ℂ) * (1 - s)) := by linear_combination he₂ - he₁
  have he' := congrArg norm he
  simp only [Complex.norm_exp, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    Complex.sub_re, Complex.one_re, zero_mul, sub_zero] at he'
  have hr := Real.exp_injective he'
  have hm0 : 0 < Real.log m := Real.log_pos (by exact_mod_cast (show 1 < m by omega))
  have hn0 : 0 < Real.log n := Real.log_pos (by exact_mod_cast (show 1 < n by omega))
  have hs : s.re = Real.log n / (Real.log m + Real.log n) := by
    apply (eq_div_iff (ne_of_gt (add_pos hm0 hn0))).mpr
    linear_combination hr
  have hs0 : 0 < s.re := by rw [hs]; exact div_pos hn0 (add_pos hm0 hn0)
  have hs1 : s.re < 1 := by
    rw [hs]
    apply (div_lt_one (add_pos hm0 hn0)).mpr
    linarith
  have hb := deletionFactor_re_ge_half (n := m) (by omega) hs0.le hs1.le
  rw [hw] at hb
  norm_num at hb

theorem reflectedFactor_label_injective_at_zero {m n : ℕ} {s : ℂ}
    (hm : 0 < m) (hn : 0 < n)
    (hmz : reflectedFactor m s = 0) (hnz : reflectedFactor n s = 0) : m = n :=
  deletionFactor_label_injective_at_zero hm hn hmz hnz

theorem xi_ne_zero_of_reflectedFactor_zero {n : ℕ} {s : ℂ}
    (hz : reflectedFactor n s = 0) : xi s ≠ 0 := by
  intro hx
  simp only [reflectedFactor, deletionFactor, xi_one_sub, hx, mul_zero, sub_zero] at hz
  exact one_ne_zero hz

end RHTower.XiGlobalKummer
