import GaloisForLFunctions.SelbergClass.FiniteEulerLogarithmicPositivity
import GaloisForLFunctions.InfiniteRankPurityTheory.TheZerosContainNoClassOfOneFrobenius

/-!
# Rational Euler twins cannot have positive logarithms

The zeros of ξ contain no complete fibre of one Euler coordinate. Thus ξ cannot
cancel an uncancelled rational Euler pole. Once denominators are removed,
logarithmic positivity and reflection exclude every nonconstant numerator.
-/

noncomputable section
set_option autoImplicit false
open Complex Filter Topology

namespace GaloisForLFunctions.SelbergClass.FiniteEuler

open GaloisForLFunctions.InfiniteRankPurityTheory
open _root_.RHTower

theorem multiplier_eq_zero_iff (W : Multiset ℂ) (x : ℂ) :
    multiplier W x = 0 ↔ ∃ a ∈ W, a * x = 1 := by
  rw [multiplier, Multiset.prod_eq_zero_iff, Multiset.mem_map]
  constructor
  · rintro ⟨a, ha, h⟩
    exact ⟨a, ha, (sub_eq_zero.mp h).symm⟩
  · rintro ⟨a, ha, h⟩
    exact ⟨a, ha, sub_eq_zero.mpr h.symm⟩

/-- Every denominator root in a completed Euler identity must also occur in its numerator.
The witness is a point of the same Euler fibre at which ξ does not vanish. -/
theorem denominator_root_mem_numerator {q : ℝ} (hq : 1 < q)
    (W V : Multiset ℂ) (c : ℂ) (F : ℂ → ℂ)
    (hid : ∀ s : ℂ, multiplier V ((q : ℂ) ^ (-s)) * F s =
      Complex.exp (c * s) * multiplier W ((q : ℂ) ^ (-s)) * xi s)
    {v : ℂ} (hv : v ∈ V) (hv0 : v ≠ 0) : v ∈ W := by
  obtain ⟨s, hs, hxi⟩ := exists_zero_localFactor_not_zero hq (inv_ne_zero hv0)
  have hden : multiplier V ((q : ℂ) ^ (-s)) = 0 :=
    (multiplier_eq_zero_iff V _).mpr ⟨v, hv, by rw [hs, mul_inv_cancel₀ hv0]⟩
  have hnum : multiplier W ((q : ℂ) ^ (-s)) = 0 := by
    have h := hid s
    rw [hden, zero_mul] at h
    exact (mul_eq_zero.mp ((mul_eq_zero.mp h.symm).resolve_right hxi)).resolve_left
      (Complex.exp_ne_zero _)
  obtain ⟨a, ha, hav⟩ := (multiplier_eq_zero_iff W _).mp hnum
  rw [hs] at hav
  have heq : a = v := by
    calc a = (a * v⁻¹) * v := by rw [mul_assoc, inv_mul_cancel₀ hv0, mul_one]
      _ = v := by rw [hav, one_mul]
  exact heq ▸ ha

/-- A reduced rational Euler multiplier of a completed entire identity has no denominator. -/
theorem denominator_eq_zero {q : ℝ} (hq : 1 < q)
    (W V : Multiset ℂ) (c : ℂ) (F : ℂ → ℂ)
    (hV : ∀ v ∈ V, v ≠ 0) (hred : ∀ v ∈ V, v ∉ W)
    (hid : ∀ s : ℂ, multiplier V ((q : ℂ) ^ (-s)) * F s =
      Complex.exp (c * s) * multiplier W ((q : ℂ) ^ (-s)) * xi s) : V = 0 := by
  induction V using Multiset.induction_on with
  | empty => rfl
  | cons v V _ih =>
    exact False.elim (hred v (Multiset.mem_cons_self _ _)
      (denominator_root_mem_numerator hq W (v ::ₘ V) c F hid
        (Multiset.mem_cons_self _ _) (hV v (Multiset.mem_cons_self _ _))))

/-- A reflected polynomial multiplier whose roots lie in the unit disk is constant.
At a zero chosen off the divisor of ξ, reflection produces a root with reciprocal
radius multiplied by the Euler base. -/
theorem numerator_eq_zero_of_reflection {p : ℕ} (hp : 1 < p)
    (W : Multiset ℂ) (c : ℂ) (F : ℂ → ℂ)
    (hW : ∀ a ∈ W, a ≠ 0) (hunit : ∀ a ∈ W, ‖a‖ ≤ 1)
    (hid : ∀ s : ℂ, F s = Complex.exp (c * s) * multiplier W ((p : ℂ) ^ (-s)) * xi s)
    (hfe : ∀ s : ℂ, F (1 - s) = F s) : W = 0 := by
  have hpR : (1 : ℝ) < p := by exact_mod_cast hp
  have hpc : (p : ℂ) ≠ 0 := by exact_mod_cast (by omega : p ≠ 0)
  have hno (a : ℂ) (ha : a ∈ W) : False := by
    have ha0 := hW a ha
    obtain ⟨s, hs, hxi⟩ := exists_zero_localFactor_not_zero hpR (inv_ne_zero ha0)
    simp only [Complex.ofReal_natCast] at hs
    have hXa : a * (p : ℂ) ^ (-s) = 1 := by rw [hs, mul_inv_cancel₀ ha0]
    have hzero : multiplier W ((p : ℂ) ^ (-s)) = 0 :=
      (multiplier_eq_zero_iff W _).mpr ⟨a, ha, hXa⟩
    have hFs : F s = 0 := by rw [hid s, hzero, mul_zero, zero_mul]
    have hnum : multiplier W ((p : ℂ) ^ (-(1 - s))) = 0 := by
      have h := hid (1 - s)
      rw [hfe s, hFs, xi_one_sub] at h
      exact (mul_eq_zero.mp ((mul_eq_zero.mp h.symm).resolve_right hxi)).resolve_left
        (Complex.exp_ne_zero _)
    obtain ⟨d, hd, hXd⟩ := (multiplier_eq_zero_iff W _).mp hnum
    have hcoord : (p : ℂ) ^ (-s) * (p : ℂ) ^ (-(1 - s)) = (p : ℂ)⁻¹ := by
      rw [← Complex.cpow_add _ _ hpc, show -s + -(1 - s) = -(1 : ℂ) by ring,
        Complex.cpow_neg, Complex.cpow_one]
    have hprod : (a * d) * (p : ℂ)⁻¹ = 1 := by
      rw [← hcoord]
      calc _ = (a * (p : ℂ) ^ (-s)) * (d * (p : ℂ) ^ (-(1 - s))) := by ring
        _ = 1 := by rw [hXa, hXd, one_mul]
    have had : a * d = (p : ℂ) := by
      calc
        a * d = ((a * d) * (p : ℂ)⁻¹) * p := by
          rw [mul_assoc, inv_mul_cancel₀ hpc, mul_one]
        _ = p := by rw [hprod, one_mul]
    have hnorm : ‖a‖ * ‖d‖ = (p : ℝ) := by
      simpa only [norm_mul, Complex.norm_natCast] using congrArg norm had
    have hle : ‖a‖ * ‖d‖ ≤ 1 := by
      simpa only [one_mul] using mul_le_mul (hunit a ha) (hunit d hd)
        (norm_nonneg d) (by norm_num : (0 : ℝ) ≤ 1)
    exact hpR.not_ge (hnorm ▸ hle)
  induction W using Multiset.induction_on with
  | empty => rfl
  | cons a W _ih => exact False.elim (hno a (Multiset.mem_cons_self _ _))

/-- At one prime, a reduced rational Euler deformation preserving completed reflection
and a nonnegative logarithmic Dirichlet representation is the trivial deformation. -/
theorem rational_twin_rigidity {p : ℕ} (hp : p.Prime)
    (W V : Multiset ℂ) (c : ℂ) (F : ℂ → ℂ) (b : ℕ → ℂ) (B : ℝ)
    (hW : ∀ a ∈ W, a ≠ 0) (hV : ∀ a ∈ V, a ≠ 0)
    (hred : ∀ v ∈ V, v ∉ W)
    (hid : ∀ s : ℂ, multiplier V ((p : ℂ) ^ (-s)) * F s =
      Complex.exp (c * s) * multiplier W ((p : ℂ) ^ (-s)) * xi s)
    (hfe : ∀ s : ℂ, F (1 - s) = F s)
    (hpos : ∀ n : ℕ, 0 ≤ (b n).re)
    (hb : ∀ s : ℂ, B < s.re → LSeriesSummable b s ∧
      Complex.exp (LSeries b s) = riemannZeta s * multiplier W ((p : ℂ) ^ (-s)) /
        multiplier V ((p : ℂ) ^ (-s))) : W = 0 ∧ V = 0 := by
  have hVzero := denominator_eq_zero (by exact_mod_cast hp.one_lt : (1 : ℝ) < p)
    W V c F hV hred (by simpa only [Complex.ofReal_natCast] using hid)
  subst V
  simp only [multiplier, Multiset.map_zero, Multiset.prod_zero, one_mul, div_one] at hid hb
  have hunit := norm_le_one_of_nonnegative_logarithm hp W hpos hb
  exact ⟨numerator_eq_zero_of_reflection hp.one_lt W c F hW hunit hid hfe, rfl⟩

private theorem differentiable_multiplier {p : ℕ} (hp : p ≠ 0) (W : Multiset ℂ) :
    Differentiable ℂ (fun s : ℂ => multiplier W ((p : ℂ) ^ (-s))) := by
  have hpow : Differentiable ℂ (fun s : ℂ => (p : ℂ) ^ (-s)) :=
    differentiable_id.neg.const_cpow (.inl (by exact_mod_cast hp))
  induction W using Multiset.induction_on with
  | empty => simpa only [multiplier, Multiset.map_zero, Multiset.prod_zero] using
      (differentiable_const (1 : ℂ))
  | cons a W ih =>
    simp only [multiplier, Multiset.map_cons, Multiset.prod_cons]
    exact ((differentiable_const (1 : ℂ)).sub (hpow.const_mul a)).mul ih

/-- Holomorphic continuation makes the cross-multiplied Euler identity global. -/
theorem completed_identity_of_halfplane {p : ℕ} (hp : p ≠ 0)
    (W V : Multiset ℂ) (c : ℂ) (F : ℂ → ℂ) (hF : Differentiable ℂ F) (B : ℝ)
    (hid : ∀ s : ℂ, B < s.re → multiplier V ((p : ℂ) ^ (-s)) * F s =
      Complex.exp (c * s) * multiplier W ((p : ℂ) ^ (-s)) * xi s) :
    ∀ s : ℂ, multiplier V ((p : ℂ) ^ (-s)) * F s =
      Complex.exp (c * s) * multiplier W ((p : ℂ) ^ (-s)) * xi s := by
  have hL := Complex.analyticOnNhd_univ_iff_differentiable.mpr
    ((differentiable_multiplier hp V).mul hF)
  have hR := Complex.analyticOnNhd_univ_iff_differentiable.mpr
    ((((differentiable_id.const_mul c).cexp).mul (differentiable_multiplier hp W)).mul
      xi_differentiable)
  have heq := hL.eq_of_eventuallyEq hR (z₀ := ((B + 1 : ℝ) : ℂ)) (by
    have hU : IsOpen {s : ℂ | B < s.re} := isOpen_lt continuous_const Complex.continuous_re
    have hmem : ((B + 1 : ℝ) : ℂ) ∈ {s : ℂ | B < s.re} := by
      simp only [Set.mem_setOf_eq, Complex.ofReal_re]
      linarith
    filter_upwards [hU.mem_nhds hmem] with s hs
    exact hid s hs)
  exact fun s => congrFun heq s

/-- No nontrivial reduced rational modification at one prime has both an entire
reflection-symmetric completion and nonnegative logarithmic Dirichlet coefficients.
Only a right-half-plane Euler identity is needed; holomorphic continuation and
the aperiodicity of the zeros of ξ supply the global obstruction. -/
theorem not_exists_nontrivial_positive_rational_twin {p : ℕ} (hp : p.Prime) :
    ¬ ∃ (W V : Multiset ℂ) (c : ℂ) (F : ℂ → ℂ) (b : ℕ → ℂ) (B : ℝ),
      (W ≠ 0 ∨ V ≠ 0) ∧ (∀ a ∈ W, a ≠ 0) ∧ (∀ a ∈ V, a ≠ 0) ∧
      (∀ v ∈ V, v ∉ W) ∧ Differentiable ℂ F ∧
      (∀ s : ℂ, F (1 - s) = F s) ∧ (∀ n : ℕ, 0 ≤ (b n).re) ∧
      (∀ s : ℂ, B < s.re → multiplier V ((p : ℂ) ^ (-s)) * F s =
        Complex.exp (c * s) * multiplier W ((p : ℂ) ^ (-s)) * xi s) ∧
      (∀ s : ℂ, B < s.re → LSeriesSummable b s ∧
        Complex.exp (LSeries b s) = riemannZeta s * multiplier W ((p : ℂ) ^ (-s)) /
          multiplier V ((p : ℂ) ^ (-s))) := by
  rintro ⟨W, V, c, F, b, B, hne, hW, hV, hred, hF, hfe, hpos, hid, hb⟩
  obtain ⟨hWzero, hVzero⟩ := rational_twin_rigidity hp W V c F b B hW hV hred
    (completed_identity_of_halfplane hp.ne_zero W V c F hF B hid) hfe hpos hb
  exact hne.elim (fun h => h hWzero) (fun h => h hVzero)

end GaloisForLFunctions.SelbergClass.FiniteEuler
