import GaloisForLFunctions.HTGeometry.WeightedComplexSumConcentration
import GaloisForLFunctions.QuantumAlg.Util.Complex
import Mathlib.Algebra.Field.GeomSum

/-!
# Off-grid cyclic phase bias

Prime-torsion polygon arguments previously controlled only integer vertices.  At a real time `t`,
the uniform cyclic frequency has a nonzero Dirichlet-kernel mean.  This module proves a sharp
return-excised bound directly: throughout `4 ≤ t ≤ p - 4`, its mean has norm at most `1/8`.
The proof is deterministic and does not require primality.
-/

open scoped BigOperators

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- One-step character ratio for a cyclic spectrum of period `p`. -/
def cyclicPhaseRatio (p : ℕ) (t : ℝ) : ℂ :=
  Complex.exp (((2 * Real.pi * t / p : ℝ) : ℂ) * Complex.I)

/-- Mean character of the complete cyclic spectrum at an arbitrary real time. -/
def cyclicPhaseMean (p : ℕ) (t : ℝ) : ℂ :=
  ((p : ℂ)⁻¹) * ∑ q : Fin p, (cyclicPhaseRatio p t) ^ q.val

lemma norm_cyclicPhaseRatio (p : ℕ) (t : ℝ) : ‖cyclicPhaseRatio p t‖ = 1 := by
  simp [cyclicPhaseRatio, Complex.norm_exp]

lemma norm_cyclicPhaseMean_le_one {p : ℕ} (hp : 0 < p) (t : ℝ) :
    ‖cyclicPhaseMean p t‖ ≤ 1 := by
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp
  have hsum : ‖∑ q : Fin p, cyclicPhaseRatio p t ^ q.val‖ ≤ (p : ℝ) := by
    calc
      ‖∑ q : Fin p, cyclicPhaseRatio p t ^ q.val‖ ≤
          ∑ q : Fin p, ‖cyclicPhaseRatio p t ^ q.val‖ := norm_sum_le _ _
      _ = (p : ℝ) := by simp [norm_pow, norm_cyclicPhaseRatio]
  rw [cyclicPhaseMean, norm_mul, norm_inv, norm_natCast]
  change (p : ℝ)⁻¹ * ‖∑ q : Fin p, cyclicPhaseRatio p t ^ q.val‖ ≤ 1
  rw [inv_mul_le_iff₀ hpR]
  simpa using hsum

/-- Exact geometric-sum estimate before the unit-circle chord is bounded below. -/
lemma cyclicPhaseMean_mul_gap_le_two {p : ℕ} (hp : 0 < p) (t : ℝ)
    (hne : cyclicPhaseRatio p t ≠ 1) :
    (p : ℝ) * ‖cyclicPhaseRatio p t - 1‖ * ‖cyclicPhaseMean p t‖ ≤ 2 := by
  let z := cyclicPhaseRatio p t
  have hsum : (∑ q : Fin p, z ^ q.val) = (z ^ p - 1) / (z - 1) := by
    rw [Fin.sum_univ_eq_sum_range, geom_sum_eq hne]
  have hz : ‖z‖ = 1 := norm_cyclicPhaseRatio p t
  have hnum : ‖z ^ p - 1‖ ≤ 2 := by
    calc
      ‖z ^ p - 1‖ ≤ ‖z ^ p‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
      _ = 2 := by rw [norm_pow, hz]; norm_num
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp
  have hgap : 0 < ‖z - 1‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hne)
  rw [cyclicPhaseMean, hsum, norm_mul, norm_inv, norm_natCast, norm_div]
  change (p : ℝ) * ‖z - 1‖ *
    ((p : ℝ)⁻¹ * (‖z ^ p - 1‖ / ‖z - 1‖)) ≤ 2
  field_simp
  exact hnum

/-- Forward half-period Dirichlet bias. -/
lemma two_mul_time_mul_norm_cyclicPhaseMean_le_one {p : ℕ} (hp : 0 < p)
    {t : ℝ} (ht : 0 < t) (htHalf : 2 * t ≤ p) :
    2 * t * ‖cyclicPhaseMean p t‖ ≤ 1 := by
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp
  let x : ℝ := 2 * Real.pi * t / p
  have hx0 : 0 < x := by dsimp [x]; positivity
  have hxpi : |x| ≤ Real.pi := by
    rw [abs_of_pos hx0]
    dsimp [x]
    rw [div_le_iff₀ hpR]
    nlinarith [Real.pi_pos]
  have hchord :=
    QuantumAlg.two_div_pi_mul_abs_le_norm_exp_ofReal_mul_I_sub_one hxpi
  have hratio : cyclicPhaseRatio p t = Complex.exp ((x : ℂ) * Complex.I) := by
    simp only [cyclicPhaseRatio, x]
  have hgapLower : 4 * t / p ≤ ‖cyclicPhaseRatio p t - 1‖ := by
    rw [hratio]
    convert hchord using 1
    rw [abs_of_pos hx0]
    dsimp [x]
    field_simp
    ring
  have hgapPos : 0 < ‖cyclicPhaseRatio p t - 1‖ := by
    have : 0 < 4 * t / p := by positivity
    exact this.trans_le hgapLower
  have hne : cyclicPhaseRatio p t ≠ 1 :=
    sub_ne_zero.mp (norm_pos_iff.mp hgapPos)
  have hmean := cyclicPhaseMean_mul_gap_le_two hp t hne
  have hmean0 : 0 ≤ ‖cyclicPhaseMean p t‖ := norm_nonneg _
  have hprod : (p : ℝ) * (4 * t / p) * ‖cyclicPhaseMean p t‖ ≤ 2 := by
    calc
      (p : ℝ) * (4 * t / p) * ‖cyclicPhaseMean p t‖ =
          ((p : ℝ) * ‖cyclicPhaseMean p t‖) * (4 * t / p) := by ring
      _ ≤ ((p : ℝ) * ‖cyclicPhaseMean p t‖) *
          ‖cyclicPhaseRatio p t - 1‖ :=
        mul_le_mul_of_nonneg_left hgapLower (mul_nonneg hpR.le hmean0)
      _ = (p : ℝ) * ‖cyclicPhaseRatio p t - 1‖ *
          ‖cyclicPhaseMean p t‖ := by ring
      _ ≤ 2 := hmean
  have hsimp : (p : ℝ) * (4 * t / p) * ‖cyclicPhaseMean p t‖ =
      4 * t * ‖cyclicPhaseMean p t‖ := by field_simp
  rw [hsimp] at hprod
  linarith

lemma cyclicPhaseRatio_period_sub {p : ℕ} (hp : 0 < p) (t : ℝ) :
    cyclicPhaseRatio p (p - t) = (cyclicPhaseRatio p t)⁻¹ := by
  have hpC : (p : ℂ) ≠ 0 := by exact_mod_cast hp.ne'
  rw [cyclicPhaseRatio, cyclicPhaseRatio]
  have harg : (((2 * Real.pi * ((p : ℝ) - t) / p : ℝ) : ℂ) * Complex.I) =
      2 * Real.pi * Complex.I -
        (((2 * Real.pi * t / p : ℝ) : ℂ) * Complex.I) := by
    push_cast
    field_simp
  rw [harg, sub_eq_add_neg, Complex.exp_add, Complex.exp_two_pi_mul_I,
    one_mul, Complex.exp_neg]

lemma norm_cyclicPhaseMean_period_sub {p : ℕ} (hp : 0 < p) (t : ℝ) :
    ‖cyclicPhaseMean p (p - t)‖ = ‖cyclicPhaseMean p t‖ := by
  have hz := norm_cyclicPhaseRatio p t
  rw [cyclicPhaseMean, cyclicPhaseMean, cyclicPhaseRatio_period_sub hp]
  have hsum : (∑ q : Fin p, ((cyclicPhaseRatio p t)⁻¹) ^ q.val) =
      (starRingEnd ℂ) (∑ q : Fin p, (cyclicPhaseRatio p t) ^ q.val) := by
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro q _hq
    rw [map_pow, ← Complex.inv_eq_conj hz]
  rw [hsum]
  have hpconj : (starRingEnd ℂ) ((p : ℂ)⁻¹) = (p : ℂ)⁻¹ := by simp
  calc
    ‖(p : ℂ)⁻¹ * (starRingEnd ℂ) (∑ q : Fin p,
        cyclicPhaseRatio p t ^ q.val)‖ =
        ‖(starRingEnd ℂ) ((p : ℂ)⁻¹ * ∑ q : Fin p,
          cyclicPhaseRatio p t ^ q.val)‖ := by rw [map_mul, hpconj]
    _ = ‖(p : ℂ)⁻¹ * ∑ q : Fin p, cyclicPhaseRatio p t ^ q.val‖ :=
      Complex.norm_conj _

/-- Backward half-period Dirichlet bias. -/
lemma two_mul_period_sub_time_mul_norm_cyclicPhaseMean_le_one
    {p : ℕ} (hp : 0 < p) {t : ℝ} (htHalf : (p : ℝ) ≤ 2 * t) (htp : t < p) :
    2 * ((p : ℝ) - t) * ‖cyclicPhaseMean p t‖ ≤ 1 := by
  have hspos : 0 < (p : ℝ) - t := sub_pos.mpr htp
  have hsHalf : 2 * ((p : ℝ) - t) ≤ p := by linarith
  have hforward := two_mul_time_mul_norm_cyclicPhaseMean_le_one hp hspos hsHalf
  rw [norm_cyclicPhaseMean_period_sub hp] at hforward
  exact hforward

/-- Uniform off-grid bias throughout a complete cyclic period after removing only four time units
at each return endpoint. -/
theorem eight_mul_norm_cyclicPhaseMean_le_one_of_returnExcised
    {p : ℕ} (hp : 0 < p) {t : ℝ} (ht0 : 4 ≤ t) (htp : t ≤ (p : ℝ) - 4) :
    8 * ‖cyclicPhaseMean p t‖ ≤ 1 := by
  have hnorm0 : 0 ≤ ‖cyclicPhaseMean p t‖ := norm_nonneg _
  rcases le_total (2 * t) (p : ℝ) with hleft | hright
  · have h := two_mul_time_mul_norm_cyclicPhaseMean_le_one hp (by linarith) hleft
    nlinarith
  · have htp' : t < (p : ℝ) := by linarith
    have h := two_mul_period_sub_time_mul_norm_cyclicPhaseMean_le_one hp hright htp'
    nlinarith

end

end GaloisForLFunctions.HTGeometry
