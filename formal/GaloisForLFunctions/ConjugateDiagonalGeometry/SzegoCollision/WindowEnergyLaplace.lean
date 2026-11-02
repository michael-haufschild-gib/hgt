import GaloisForLFunctions.ConjugateDiagonalGeometry.SzegoCollision.PolynomialPrefixStabilization
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Integral.ExpDecay

/-!
# Window exponential energy of a collision loop: Laplace identity, abscissa and index law

For a finite zero window `Z` with multiplicities, closed under the horizontal reflection
`z ↦ 1 - z̄`, put `𝒵(t) = ∑_z m_z e^{t(z - 1/2)}`.

1. **Pair energy** (`pairExpSum_eq_normSq`): reflection turns the pair exponential sum into a
   modulus square, `∑_{z,w} m_z m_w e^{t(z - w)} = |𝒵(t)|²`.
2. **Laplace identity** (`pairResolvent_eq_integral`): the resolvent of the pair-difference divisor,
   i.e. the logarithmic derivative of the collision polynomial `∏ (x - (z - w))^{m_z m_w}`, is the
   Laplace transform of the nonnegative energy `|𝒵(t)|²` on `Re x > 2 max (Re z - 1/2)`.
3. **Abscissa law** (`integrableOn_energy_iff`): `e^{-xt}|𝒵(t)|²` is integrable on `(0, ∞)` exactly
   when `x` exceeds twice the maximal depth; the horizontal pair `(z, 1 - z̄)` of a deepest zero is a
   real pole of the resolvent at the abscissa.
4. **Energy–index law** (`fredholmIndex_eq_zero_of_integrableOn_energy`,
   `integrableOn_energy_of_fredholmIndex_eq_zero`): the stage-`n` Zhukovsky collision index vanishes
   when the energy is integrable against `e^{-(1/2 - a_n)t}`, and an index-zero window without
   horizontal pair beyond the far vertex has integrable energy against every `e^{-xt}`,
   `x > 1/2 - a_n`.
-/

set_option autoImplicit false

open Complex MeasureTheory Set Filter
open scoped BigOperators Topology

noncomputable section

namespace GaloisForLFunctions.ConjugateDiagonalGeometry.SzegoCollision

/-- A finite zero window with positive multiplicities, closed under `z ↦ 1 - z̄`. -/
structure ReflectedWindow where
  Z : Finset ℂ
  mult : ℂ → ℕ
  mult_pos : ∀ z ∈ Z, 0 < mult z
  refl_mem : ∀ z ∈ Z, 1 - star z ∈ Z
  refl_mult : ∀ z ∈ Z, mult (1 - star z) = mult z

namespace ReflectedWindow

variable (W : ReflectedWindow)

/-- Window exponential sum `𝒵(t) = ∑_z m_z e^{t(z - 1/2)}`. -/
def expSum (t : ℝ) : ℂ :=
  ∑ z ∈ W.Z, (W.mult z : ℂ) * cexp ((t : ℂ) * (z - 1 / 2))

/-- Pair resolvent `∑_{z,w} m_z m_w / (x - (z - w))` of the pair-difference divisor. -/
def pairResolvent (x : ℂ) : ℂ :=
  ∑ z ∈ W.Z, ∑ w ∈ W.Z, ((W.mult z * W.mult w : ℕ) : ℂ) / (x - (z - w))

/-- Total multiplicity `D = ∑_z m_z`. -/
def degree : ℕ :=
  ∑ z ∈ W.Z, W.mult z

theorem sum_refl {β : Type*} [AddCommMonoid β] (f : ℂ → β) :
    ∑ w ∈ W.Z, f (1 - star w) = ∑ w ∈ W.Z, f w :=
  Finset.sum_nbij' (fun w => 1 - star w) (fun w => 1 - star w) W.refl_mem W.refl_mem
    (fun w _ => by simp) (fun w _ => by simp) (fun _ _ => rfl)

theorem prod_refl {M : Type*} [CommMonoid M] (f : ℂ → M) :
    ∏ w ∈ W.Z, f (1 - star w) = ∏ w ∈ W.Z, f w :=
  Finset.prod_nbij' (fun w => 1 - star w) (fun w => 1 - star w) W.refl_mem W.refl_mem
    (fun w _ => by simp) (fun w _ => by simp) (fun _ _ => rfl)

/-- The pair-difference divisor is closed under conjugation: `(z, w) ↦ (1 - w̄, 1 - z̄)` sends
`z - w` to `conj (z - w)` and preserves `m_z m_w`. -/
theorem prod_pair_conj {M : Type*} [CommMonoid M] (f : ℂ → M) :
    ∏ z ∈ W.Z, ∏ w ∈ W.Z, f (z - w) ^ (W.mult z * W.mult w) =
      ∏ z ∈ W.Z, ∏ w ∈ W.Z, f (star (z - w)) ^ (W.mult z * W.mult w) := by
  set G : ℂ → ℂ → M := fun z w => f (star (z - w)) ^ (W.mult z * W.mult w) with hG
  have hreidx : ∏ z ∈ W.Z, ∏ w ∈ W.Z, G z w =
      ∏ z ∈ W.Z, ∏ w ∈ W.Z, G (1 - star z) (1 - star w) :=
    (W.prod_refl (fun z => ∏ w ∈ W.Z, G z w)).symm.trans
      (Finset.prod_congr rfl fun z _ => (W.prod_refl (fun w => G (1 - star z) w)).symm)
  symm
  calc ∏ z ∈ W.Z, ∏ w ∈ W.Z, G z w
      = ∏ z ∈ W.Z, ∏ w ∈ W.Z, G (1 - star z) (1 - star w) := hreidx
    _ = ∏ z ∈ W.Z, ∏ w ∈ W.Z, f (w - z) ^ (W.mult z * W.mult w) := by
        refine Finset.prod_congr rfl fun z hz => Finset.prod_congr rfl fun w hw => ?_
        simp only [hG, W.refl_mult z hz, W.refl_mult w hw]
        congr 2
        simp only [star_sub, star_one, star_star]
        ring
    _ = ∏ w ∈ W.Z, ∏ z ∈ W.Z, f (w - z) ^ (W.mult z * W.mult w) := Finset.prod_comm
    _ = ∏ z ∈ W.Z, ∏ w ∈ W.Z, f (z - w) ^ (W.mult z * W.mult w) :=
        Finset.prod_congr rfl fun _ _ => Finset.prod_congr rfl fun _ _ => by rw [mul_comm]

/-- Every pair difference has real part at most twice a depth bound. -/
theorem re_sub_le {δ : ℝ} (hδ : ∀ z ∈ W.Z, z.re - 1 / 2 ≤ δ) {z w : ℂ} (hz : z ∈ W.Z)
    (hw : w ∈ W.Z) : (z - w).re ≤ 2 * δ := by
  have h1 := hδ z hz
  have h2 := hδ (1 - star w) (W.refl_mem w hw)
  have hre : (1 - star w).re = 1 - w.re := by simp
  rw [hre] at h2
  rw [Complex.sub_re]
  linarith

theorem continuous_expSum : Continuous W.expSum := by
  unfold expSum
  fun_prop

/-- `|𝒵(t)| ≤ D e^{δ t}` for `t ≥ 0` under a depth bound `δ`. -/
theorem norm_expSum_le {δ : ℝ} (hδ : ∀ z ∈ W.Z, z.re - 1 / 2 ≤ δ) {t : ℝ} (ht : 0 ≤ t) :
    ‖W.expSum t‖ ≤ (W.degree : ℝ) * Real.exp (δ * t) := by
  unfold expSum degree
  rw [Nat.cast_sum, Finset.sum_mul]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun z hz => ?_)
  rw [norm_mul, Complex.norm_natCast, Complex.norm_exp]
  refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (Nat.cast_nonneg _)
  have hre : ((t : ℂ) * (z - 1 / 2)).re = t * (z.re - 1 / 2) := by simp
  rw [hre, mul_comm δ t]
  exact mul_le_mul_of_nonneg_left (hδ z hz) ht

/-- **Pair energy.** `∑_{z,w} m_z m_w e^{t(z - w)} = |𝒵(t)|²`. -/
theorem pairExpSum_eq_normSq (t : ℝ) :
    ∑ z ∈ W.Z, ∑ w ∈ W.Z, ((W.mult z * W.mult w : ℕ) : ℂ) * cexp ((t : ℂ) * (z - w)) =
      ((‖W.expSum t‖ ^ 2 : ℝ) : ℂ) := by
  set S : ℂ := ∑ z ∈ W.Z, (W.mult z : ℂ) * cexp ((t : ℂ) * z)
  have hstar : star S = ∑ z ∈ W.Z, (W.mult z : ℂ) * cexp ((t : ℂ) * star z) := by
    simp only [S, star_sum, star_mul', star_natCast, Complex.star_def, ← Complex.exp_conj,
      map_mul, Complex.conj_ofReal]
  have hneg : ∑ w ∈ W.Z, (W.mult w : ℂ) * cexp (-((t : ℂ) * w)) =
      cexp (-(t : ℂ)) * star S := by
    rw [← W.sum_refl (fun w => (W.mult w : ℂ) * cexp (-((t : ℂ) * w))), hstar, Finset.mul_sum]
    refine Finset.sum_congr rfl fun w hw => ?_
    rw [W.refl_mult w hw, mul_left_comm, ← Complex.exp_add]
    congr 2
    ring
  have hlhs : ∑ z ∈ W.Z, ∑ w ∈ W.Z, ((W.mult z * W.mult w : ℕ) : ℂ) * cexp ((t : ℂ) * (z - w)) =
      S * ∑ w ∈ W.Z, (W.mult w : ℂ) * cexp (-((t : ℂ) * w)) := by
    rw [Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun z _ => Finset.sum_congr rfl fun w _ => ?_
    rw [Nat.cast_mul, show (t : ℂ) * (z - w) = (t : ℂ) * z + -((t : ℂ) * w) by ring,
      Complex.exp_add]
    ring
  have hE : W.expSum t = cexp (-((t : ℂ) / 2)) * S := by
    unfold expSum
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun z _ => ?_
    rw [show (t : ℂ) * (z - 1 / 2) = -((t : ℂ) / 2) + (t : ℂ) * z by ring, Complex.exp_add]
    ring
  have hstar_half : star (cexp (-((t : ℂ) / 2))) = cexp (-((t : ℂ) / 2)) := by
    rw [Complex.star_def, ← Complex.exp_conj]
    simp [map_ofNat]
  rw [hlhs, hneg, Complex.ofReal_pow, ← Complex.mul_conj', ← Complex.star_def, hE, star_mul',
    hstar_half]
  have hsq : cexp (-((t : ℂ) / 2)) * cexp (-((t : ℂ) / 2)) = cexp (-(t : ℂ)) := by
    rw [← Complex.exp_add]
    congr 1
    ring
  calc S * (cexp (-(t : ℂ)) * star S)
      = (cexp (-((t : ℂ) / 2)) * cexp (-((t : ℂ) / 2))) * (S * star S) := by rw [hsq]; ring
    _ = cexp (-((t : ℂ) / 2)) * S * (cexp (-((t : ℂ) / 2)) * star S) := by ring

/-- **Laplace identity.** On `Re x > 2δ` the pair resolvent is the Laplace transform of `|𝒵|²`. -/
theorem pairResolvent_eq_integral {δ : ℝ} (hδ : ∀ z ∈ W.Z, z.re - 1 / 2 ≤ δ) {x : ℂ}
    (hx : 2 * δ < x.re) :
    W.pairResolvent x =
      ∫ t in Ioi (0 : ℝ), cexp (-(x * t)) * ((‖W.expSum t‖ ^ 2 : ℝ) : ℂ) := by
  have hneg : ∀ z ∈ W.Z, ∀ w ∈ W.Z, (z - w - x).re < 0 := by
    intro z hz w hw
    have h := W.re_sub_le hδ hz hw
    rw [Complex.sub_re]
    linarith
  have hterm : ∀ z ∈ W.Z, ∀ w ∈ W.Z,
      (fun t : ℝ => cexp (-(x * t)) *
        (((W.mult z * W.mult w : ℕ) : ℂ) * cexp ((t : ℂ) * (z - w)))) =
      fun t : ℝ => ((W.mult z * W.mult w : ℕ) : ℂ) * cexp ((z - w - x) * t) := by
    intro z _ w _
    funext t
    rw [mul_left_comm, ← Complex.exp_add]
    congr 2
    ring
  have hint : ∀ z ∈ W.Z, ∀ w ∈ W.Z, IntegrableOn
      (fun t : ℝ => cexp (-(x * t)) *
        (((W.mult z * W.mult w : ℕ) : ℂ) * cexp ((t : ℂ) * (z - w)))) (Ioi 0) := by
    intro z hz w hw
    rw [hterm z hz w hw]
    exact (integrableOn_exp_mul_complex_Ioi (hneg z hz w hw) 0).const_mul _
  simp_rw [← W.pairExpSum_eq_normSq, Finset.mul_sum]
  rw [integral_finsetSum _ fun z hz => integrable_finsetSum _ fun w hw => hint z hz w hw]
  unfold pairResolvent
  refine Finset.sum_congr rfl fun z hz => ?_
  rw [integral_finsetSum _ fun w hw => hint z hz w hw]
  refine Finset.sum_congr rfl fun w hw => ?_
  rw [hterm z hz w hw, integral_const_mul, integral_exp_mul_complex_Ioi (hneg z hz w hw) 0]
  have hne : z - w - x ≠ 0 := by
    intro h0
    have := hneg z hz w hw
    rw [h0, Complex.zero_re] at this
    exact lt_irrefl 0 this
  have hne' : x - (z - w) ≠ 0 := by
    intro h0
    exact hne (by linear_combination -h0)
  simp only [Complex.ofReal_zero, mul_zero, Complex.exp_zero]
  field_simp
  ring

/-- Real form of the Laplace identity at real `y > 2δ`. -/
theorem pairResolvent_ofReal_eq {δ : ℝ} (hδ : ∀ z ∈ W.Z, z.re - 1 / 2 ≤ δ) {y : ℝ}
    (hy : 2 * δ < y) :
    W.pairResolvent y =
      ((∫ t in Ioi (0 : ℝ), Real.exp (-(y * t)) * ‖W.expSum t‖ ^ 2 : ℝ) : ℂ) := by
  rw [W.pairResolvent_eq_integral hδ (by simpa using hy), ← integral_complex_ofReal]
  refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
  push_cast
  ring_nf

/-- Integrability of the weighted energy beyond twice the depth bound. -/
theorem integrableOn_energy_of_lt {δ : ℝ} (hδ : ∀ z ∈ W.Z, z.re - 1 / 2 ≤ δ) {x : ℝ}
    (hx : 2 * δ < x) :
    IntegrableOn (fun t : ℝ => Real.exp (-(x * t)) * ‖W.expSum t‖ ^ 2) (Ioi 0) := by
  have hdom : IntegrableOn
      (fun t : ℝ => (W.degree : ℝ) ^ 2 * Real.exp (-(x - 2 * δ) * t)) (Ioi 0) :=
    (exp_neg_integrableOn_Ioi 0 (by linarith)).const_mul _
  refine hdom.mono' ?_ ?_
  · exact ((Real.continuous_exp.comp (continuous_const.mul continuous_id).neg).mul
      (W.continuous_expSum.norm.pow 2)).aestronglyMeasurable
  · refine ae_restrict_of_forall_mem measurableSet_Ioi fun t ht => ?_
    have ht0 : 0 ≤ t := (mem_Ioi.mp ht).le
    have hE := W.norm_expSum_le hδ ht0
    have hsq : ‖W.expSum t‖ ^ 2 ≤ ((W.degree : ℝ) * Real.exp (δ * t)) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) hE 2
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (Real.exp_pos _).le (sq_nonneg _))]
    calc Real.exp (-(x * t)) * ‖W.expSum t‖ ^ 2
        ≤ Real.exp (-(x * t)) * ((W.degree : ℝ) * Real.exp (δ * t)) ^ 2 :=
          mul_le_mul_of_nonneg_left hsq (Real.exp_pos _).le
      _ = (W.degree : ℝ) ^ 2 * Real.exp (-(x - 2 * δ) * t) := by
          have hexp : Real.exp (δ * t) ^ 2 = Real.exp (2 * δ * t) := by
            rw [sq, ← Real.exp_add]
            ring_nf
          rw [mul_pow, hexp, show -(x - 2 * δ) * t = -(x * t) + 2 * δ * t by ring, Real.exp_add]
          ring


/-- The horizontal pair `(z, 1 - z̄)` has the real difference `2 (Re z - 1/2)`. -/
theorem sub_one_sub_star (z : ℂ) : z - (1 - star z) = ((2 * (z.re - 1 / 2) : ℝ) : ℂ) := by
  apply Complex.ext
  · simp; ring
  · simp

/-- Each pair resolvent term has nonnegative real part at real `y` beyond `2δ`. -/
theorem re_pairResolvent_term_nonneg {δ : ℝ} (hδ : ∀ z ∈ W.Z, z.re - 1 / 2 ≤ δ) {y : ℝ}
    (hy : 2 * δ < y) {z w : ℂ} (hz : z ∈ W.Z) (hw : w ∈ W.Z) :
    0 ≤ (((W.mult z * W.mult w : ℕ) : ℂ) / ((y : ℂ) - (z - w))).re := by
  have hre : 0 ≤ ((y : ℂ) - (z - w)).re := by
    have h := W.re_sub_le hδ hz hw
    rw [Complex.sub_re, Complex.ofReal_re]
    linarith
  rw [div_eq_mul_inv, ← Complex.ofReal_natCast, Complex.re_ofReal_mul, Complex.inv_re]
  exact mul_nonneg (Nat.cast_nonneg _) (div_nonneg hre (Complex.normSq_nonneg _))

/-- The horizontal pair of a zero of depth `δ` bounds the real pair resolvent below by
`1 / (y - 2δ)`. -/
theorem inv_le_re_pairResolvent {δ : ℝ} (hδ : ∀ z ∈ W.Z, z.re - 1 / 2 ≤ δ) {z₀ : ℂ}
    (hz₀ : z₀ ∈ W.Z) (hz₀δ : z₀.re - 1 / 2 = δ) {y : ℝ} (hy : 2 * δ < y) :
    1 / (y - 2 * δ) ≤ (W.pairResolvent y).re := by
  set w₀ := 1 - star z₀ with hw₀_def
  have hw₀ : w₀ ∈ W.Z := W.refl_mem z₀ hz₀
  have hpos : 0 < y - 2 * δ := by linarith
  have hterm : (((W.mult z₀ * W.mult w₀ : ℕ) : ℂ) / ((y : ℂ) - (z₀ - w₀))).re =
      ((W.mult z₀ * W.mult w₀ : ℕ) : ℝ) / (y - 2 * δ) := by
    rw [hw₀_def, sub_one_sub_star, hz₀δ, ← Complex.ofReal_sub, ← Complex.ofReal_natCast,
      ← Complex.ofReal_div, Complex.ofReal_re]
  have hm : (1 : ℝ) ≤ ((W.mult z₀ * W.mult w₀ : ℕ) : ℝ) := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr
      (Nat.mul_ne_zero (W.mult_pos z₀ hz₀).ne' (W.mult_pos w₀ hw₀).ne')
  have hrow : ∀ z ∈ W.Z, 0 ≤ (∑ w ∈ W.Z,
      ((W.mult z * W.mult w : ℕ) : ℂ) / ((y : ℂ) - (z - w))).re := fun z hz => by
    rw [Complex.re_sum]
    exact Finset.sum_nonneg fun w hw => W.re_pairResolvent_term_nonneg hδ hy hz hw
  unfold pairResolvent
  calc 1 / (y - 2 * δ)
      ≤ ((W.mult z₀ * W.mult w₀ : ℕ) : ℝ) / (y - 2 * δ) :=
        div_le_div_of_nonneg_right hm hpos.le
    _ = (((W.mult z₀ * W.mult w₀ : ℕ) : ℂ) / ((y : ℂ) - (z₀ - w₀))).re := hterm.symm
    _ ≤ ∑ w ∈ W.Z, (((W.mult z₀ * W.mult w : ℕ) : ℂ) / ((y : ℂ) - (z₀ - w))).re :=
        Finset.single_le_sum (f := fun w => (((W.mult z₀ * W.mult w : ℕ) : ℂ) /
          ((y : ℂ) - (z₀ - w))).re) (fun w hw => W.re_pairResolvent_term_nonneg hδ hy hz₀ hw) hw₀
    _ = (∑ w ∈ W.Z, ((W.mult z₀ * W.mult w : ℕ) : ℂ) / ((y : ℂ) - (z₀ - w))).re :=
        (Complex.re_sum _ _).symm
    _ ≤ ∑ z ∈ W.Z, (∑ w ∈ W.Z, ((W.mult z * W.mult w : ℕ) : ℂ) / ((y : ℂ) - (z - w))).re :=
        Finset.single_le_sum (f := fun z => (∑ w ∈ W.Z,
          ((W.mult z * W.mult w : ℕ) : ℂ) / ((y : ℂ) - (z - w))).re) hrow hz₀
    _ = (∑ z ∈ W.Z, ∑ w ∈ W.Z, ((W.mult z * W.mult w : ℕ) : ℂ) / ((y : ℂ) - (z - w))).re :=
        (Complex.re_sum _ _).symm

/-- **Abscissa law, converse half.** Integrability of `e^{-xt}|𝒵(t)|²` forces `x > 2δ` when `δ` is
the depth of some window zero bounding all depths. -/
theorem lt_of_integrableOn_energy {δ : ℝ} (hδ : ∀ z ∈ W.Z, z.re - 1 / 2 ≤ δ) {z₀ : ℂ}
    (hz₀ : z₀ ∈ W.Z) (hz₀δ : z₀.re - 1 / 2 = δ) {x : ℝ}
    (hint : IntegrableOn (fun t : ℝ => Real.exp (-(x * t)) * ‖W.expSum t‖ ^ 2) (Ioi 0)) :
    2 * δ < x := by
  by_contra hle
  replace hle : x ≤ 2 * δ := not_lt.mp hle
  set I := ∫ t in Ioi (0 : ℝ), Real.exp (-(x * t)) * ‖W.expSum t‖ ^ 2
  have hI : 0 ≤ I := setIntegral_nonneg measurableSet_Ioi fun t _ =>
    mul_nonneg (Real.exp_pos _).le (sq_nonneg _)
  have hpos : 0 < 1 / (I + 1) := by positivity
  set y := 2 * δ + 1 / (I + 1)
  have hy : 2 * δ < y := by linarith
  have hlow := W.inv_le_re_pairResolvent hδ hz₀ hz₀δ hy
  rw [W.pairResolvent_ofReal_eq hδ hy, Complex.ofReal_re] at hlow
  have hmono : ∫ t in Ioi (0 : ℝ), Real.exp (-(y * t)) * ‖W.expSum t‖ ^ 2 ≤ I := by
    refine setIntegral_mono_on (W.integrableOn_energy_of_lt hδ hy) hint measurableSet_Ioi
      fun t ht => ?_
    have ht0 : 0 ≤ t := (mem_Ioi.mp ht).le
    exact mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (by nlinarith)) (sq_nonneg _)
  have hyd : y - 2 * δ = 1 / (I + 1) := by ring
  rw [hyd, one_div_one_div] at hlow
  linarith

/-- **Abscissa law.** `e^{-xt}|𝒵(t)|²` is integrable on `(0, ∞)` iff `x > 2 max (Re z - 1/2)`. -/
theorem integrableOn_energy_iff {δ : ℝ} (hδ : ∀ z ∈ W.Z, z.re - 1 / 2 ≤ δ) {z₀ : ℂ}
    (hz₀ : z₀ ∈ W.Z) (hz₀δ : z₀.re - 1 / 2 = δ) {x : ℝ} :
    IntegrableOn (fun t : ℝ => Real.exp (-(x * t)) * ‖W.expSum t‖ ^ 2) (Ioi 0) ↔ 2 * δ < x :=
  ⟨W.lt_of_integrableOn_energy hδ hz₀ hz₀δ, W.integrableOn_energy_of_lt hδ⟩

/-! ### Energy–index law at a Zhukovsky stage -/

/-- Pair differences of a window whose doubled depth stays below the vertex gap `1/2 - a_n` lie
strictly outside the `n`-th Zhukovsky ellipse. -/
theorem one_lt_zhukovskyEllipseForm_of_lt_gap {n : ℕ} {δ : ℝ}
    (hδ : ∀ z ∈ W.Z, z.re - 1 / 2 ≤ δ) (hgap : 2 * δ < 1 / 2 - zhukovskyMajorAxis n) {z w : ℂ}
    (hz : z ∈ W.Z) (hw : w ∈ W.Z) : 1 < zhukovskyEllipseForm n (z - w) := by
  have h := W.re_sub_le hδ hz hw
  have ha := zhukovskyMajorAxis_pos n
  have hs : zhukovskyMajorAxis n < 1 / 2 - (z - w).re := by linarith
  have hsq : zhukovskyMajorAxis n ^ 2 < ((z - w).re - 1 / 2) ^ 2 := by
    rw [show ((z - w).re - 1 / 2) ^ 2 = (1 / 2 - (z - w).re) ^ 2 by ring]
    exact pow_lt_pow_left₀ hs ha.le two_ne_zero
  have h1 : 1 < ((z - w).re - 1 / 2) ^ 2 / zhukovskyMajorAxis n ^ 2 :=
    (one_lt_div (by positivity)).mpr hsq
  have h2 : 0 ≤ (z - w).im ^ 2 / zhukovskyMinorAxis n ^ 2 := by positivity
  unfold zhukovskyEllipseForm
  linarith

/-- **Index zero below the vertex gap.** If `2 max (Re z - 1/2) < 1/2 - a_n`, the stage-`n`
Wiener–Hopf collision index of the window's collision polynomial vanishes. -/
theorem fredholmIndex_eq_zero_of_two_mul_depth_lt_gap {P : Polynomial ℂ} {n : ℕ}
    (heval : ∀ x : ℂ, P.eval x = ∏ z ∈ W.Z, ∏ w ∈ W.Z, (x - (z - w)) ^ (W.mult z * W.mult w))
    {δ : ℝ} (hδ : ∀ z ∈ W.Z, z.re - 1 / 2 ≤ δ) (hgap : 2 * δ < 1 / 2 - zhukovskyMajorAxis n) :
    HTGeometry.fredholmIndex
      (HTGeometry.wienerHopfLift (unitNormalizeSymbol (polyZhukovskyLaurentLoop n P))) = 0 := by
  have hgt := fun z hz w hw => W.one_lt_zhukovskyEllipseForm_of_lt_gap hδ hgap (z := z) (w := w) hz hw
  have hell : ∀ z ∈ W.Z, ∀ w ∈ W.Z, zhukovskyEllipseForm n (z - w) ≠ 1 :=
    fun z hz w hw => (hgt z hz w hw).ne'
  have h := exists_birkhoffSzego_of_prod_eval heval hell
  dsimp only at h
  obtain ⟨-, -, -, -, -, -, -, -, hind, -, -⟩ := h
  rw [hind]
  have hk : (∑ z ∈ W.Z, ∑ w ∈ W.Z, W.mult z * W.mult w *
      (if zhukovskyEllipseForm n (z - w) < 1 then 1 else 0)) = 0 :=
    Finset.sum_eq_zero fun z hz => Finset.sum_eq_zero fun w hw => by
      rw [if_neg (not_lt.mpr (hgt z hz w hw).le), mul_zero]
  rw [hk]
  simp

/-- **Index at least two above the vertex gap.** A zero whose horizontal pair difference
`2 (Re z₀ - 1/2)` lies in `(1/2 - a_n, 1/2 + a_n)` forces collision index `≥ 2`. -/
theorem two_le_fredholmIndex_of_gap_lt_two_mul_depth {P : Polynomial ℂ} {n : ℕ}
    (heval : ∀ x : ℂ, P.eval x = ∏ z ∈ W.Z, ∏ w ∈ W.Z, (x - (z - w)) ^ (W.mult z * W.mult w))
    (hnz : ∀ u : HTGeometry.UnitCircle, (P.eval (zhukovskyLoop n u)) ^ 2 ≠ 0) {z₀ : ℂ}
    (hz₀ : z₀ ∈ W.Z) (hlo : 1 / 2 - zhukovskyMajorAxis n < 2 * (z₀.re - 1 / 2))
    (hhi : 2 * (z₀.re - 1 / 2) < 1 / 2 + zhukovskyMajorAxis n) :
    2 ≤ HTGeometry.fredholmIndex
      (HTGeometry.wienerHopfLift (unitNormalizeSymbol (polyZhukovskyLaurentLoop n P))) := by
  have hell := ellipse_nondegenerate_of_prod_eval_ne_zero heval W.mult_pos hnz
  have h := exists_birkhoffSzego_of_prod_eval heval hell
  dsimp only at h
  obtain ⟨-, -, -, -, -, -, -, -, hind, -, -⟩ := h
  rw [hind]
  set w₀ := 1 - star z₀ with hw₀_def
  have hw₀ : w₀ ∈ W.Z := W.refl_mem z₀ hz₀
  have ha := zhukovskyMajorAxis_pos n
  have hin : zhukovskyEllipseForm n (z₀ - w₀) < 1 := by
    rw [hw₀_def, sub_one_sub_star]
    unfold zhukovskyEllipseForm
    simp only [Complex.ofReal_re, Complex.ofReal_im]
    have hsq : (2 * (z₀.re - 1 / 2) - 1 / 2) ^ 2 < zhukovskyMajorAxis n ^ 2 :=
      sq_lt_sq' (by linarith) (by linarith)
    rw [zero_pow two_ne_zero, zero_div, add_zero]
    exact (div_lt_one (by positivity)).mpr hsq
  have hm : 1 ≤ W.mult z₀ * W.mult w₀ :=
    Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (W.mult_pos z₀ hz₀).ne' (W.mult_pos w₀ hw₀).ne')
  have hk : 1 ≤ ∑ z ∈ W.Z, ∑ w ∈ W.Z, W.mult z * W.mult w *
      (if zhukovskyEllipseForm n (z - w) < 1 then 1 else 0) := by
    calc 1 ≤ W.mult z₀ * W.mult w₀ * (if zhukovskyEllipseForm n (z₀ - w₀) < 1 then 1 else 0) := by
          rw [if_pos hin, mul_one]; exact hm
      _ ≤ ∑ w ∈ W.Z, W.mult z₀ * W.mult w *
            (if zhukovskyEllipseForm n (z₀ - w) < 1 then 1 else 0) :=
          Finset.single_le_sum (f := fun w => W.mult z₀ * W.mult w *
            (if zhukovskyEllipseForm n (z₀ - w) < 1 then 1 else 0)) (fun _ _ => Nat.zero_le _) hw₀
      _ ≤ _ := Finset.single_le_sum (f := fun z => ∑ w ∈ W.Z, W.mult z * W.mult w *
            (if zhukovskyEllipseForm n (z - w) < 1 then 1 else 0)) (fun _ _ => Nat.zero_le _) hz₀
  have hk' : (1 : ℤ) ≤ ((∑ z ∈ W.Z, ∑ w ∈ W.Z, W.mult z * W.mult w *
      (if zhukovskyEllipseForm n (z - w) < 1 then 1 else 0) : ℕ) : ℤ) := by exact_mod_cast hk
  linarith

/-- **Energy–index law, forward.** Integrable window energy against `e^{-(1/2 - a_n)t}` forces the
stage-`n` collision index to vanish. -/
theorem fredholmIndex_eq_zero_of_integrableOn_energy {P : Polynomial ℂ} {n : ℕ}
    (heval : ∀ x : ℂ, P.eval x = ∏ z ∈ W.Z, ∏ w ∈ W.Z, (x - (z - w)) ^ (W.mult z * W.mult w))
    (hint : IntegrableOn (fun t : ℝ => Real.exp (-((1 / 2 - zhukovskyMajorAxis n) * t)) *
      ‖W.expSum t‖ ^ 2) (Ioi 0)) :
    HTGeometry.fredholmIndex
      (HTGeometry.wienerHopfLift (unitNormalizeSymbol (polyZhukovskyLaurentLoop n P))) = 0 := by
  rcases W.Z.eq_empty_or_nonempty with hZ | hZ
  · exact W.fredholmIndex_eq_zero_of_two_mul_depth_lt_gap heval
      (δ := (1 / 2 - zhukovskyMajorAxis n) / 2 - 1) (fun z hz => by simp [hZ] at hz)
      (by linarith)
  · obtain ⟨z₀, hz₀, hmax⟩ := Finset.exists_max_image W.Z (fun z => z.re - 1 / 2) hZ
    exact W.fredholmIndex_eq_zero_of_two_mul_depth_lt_gap heval hmax
      (W.lt_of_integrableOn_energy hmax hz₀ rfl hint)

/-- **Energy–index law, converse.** An index-zero window with no horizontal pair beyond the far
vertex `1/2 + a_n` has integrable energy against every `e^{-xt}`, `x > 1/2 - a_n`. -/
theorem integrableOn_energy_of_fredholmIndex_eq_zero {P : Polynomial ℂ} {n : ℕ}
    (heval : ∀ x : ℂ, P.eval x = ∏ z ∈ W.Z, ∏ w ∈ W.Z, (x - (z - w)) ^ (W.mult z * W.mult w))
    (hnz : ∀ u : HTGeometry.UnitCircle, (P.eval (zhukovskyLoop n u)) ^ 2 ≠ 0)
    (hdeep : ∀ z ∈ W.Z, 2 * (z.re - 1 / 2) < 1 / 2 + zhukovskyMajorAxis n)
    (hind : HTGeometry.fredholmIndex
      (HTGeometry.wienerHopfLift (unitNormalizeSymbol (polyZhukovskyLaurentLoop n P))) = 0)
    {x : ℝ} (hx : 1 / 2 - zhukovskyMajorAxis n < x) :
    IntegrableOn (fun t : ℝ => Real.exp (-(x * t)) * ‖W.expSum t‖ ^ 2) (Ioi 0) := by
  rcases W.Z.eq_empty_or_nonempty with hZ | hZ
  · have hfun : (fun t : ℝ => Real.exp (-(x * t)) * ‖W.expSum t‖ ^ 2) = fun _ => 0 := by
      funext t
      simp [expSum, hZ]
    rw [hfun]
    exact integrableOn_zero
  · obtain ⟨z₀, hz₀, hmax⟩ := Finset.exists_max_image W.Z (fun z => z.re - 1 / 2) hZ
    refine W.integrableOn_energy_of_lt hmax ?_
    by_contra hge
    replace hge : x ≤ 2 * (z₀.re - 1 / 2) := not_lt.mp hge
    have h2 := W.two_le_fredholmIndex_of_gap_lt_two_mul_depth heval hnz hz₀
      (lt_of_lt_of_le hx hge) (hdeep z₀ hz₀)
    rw [hind] at h2
    norm_num at h2

end ReflectedWindow

end GaloisForLFunctions.ConjugateDiagonalGeometry.SzegoCollision
