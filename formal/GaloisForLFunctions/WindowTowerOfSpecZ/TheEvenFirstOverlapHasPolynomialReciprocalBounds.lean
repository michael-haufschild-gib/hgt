import Mathlib.Tactic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# Polynomial reciprocal bounds on the first even overlap

The outside polynomial is refined by a quadratic residual correction.
On the reflected strip, Taylor bounds of degree eight reduce reciprocal
positivity to homogeneous polynomials of degree twelve.
-/

noncomputable section
open Real MeasureTheory Set
namespace GaloisForLFunctions.WindowTowerOfSpecZ

private def outsidePotentialHom (l u v t : ℝ) : ℝ :=
  (3029 / 3000 : ℝ) * (v + t) ^ 16 +
    (l * v + u * t) ^ 1 * (v + t) ^ 15 / 2 +
    (l * v + u * t) ^ 2 * (v + t) ^ 14 / 4 +
    (l * v + u * t) ^ 3 * (v + t) ^ 13 / 6 +
    (l * v + u * t) ^ 4 * (v + t) ^ 12 / 8 +
    (l * v + u * t) ^ 5 * (v + t) ^ 11 / 10 +
    (l * v + u * t) ^ 6 * (v + t) ^ 10 / 12 +
    (l * v + u * t) ^ 7 * (v + t) ^ 9 / 14 +
    (l * v + u * t) ^ 8 * (v + t) ^ 8 / 16 +
    (l * v + u * t) ^ 9 * (v + t) ^ 7 / 18 +
    (l * v + u * t) ^ 10 * (v + t) ^ 6 / 20 +
    (l * v + u * t) ^ 11 * (v + t) ^ 5 / 22 +
    (l * v + u * t) ^ 12 * (v + t) ^ 4 / 24 +
    (l * v + u * t) ^ 13 * (v + t) ^ 3 / 26 +
    (l * v + u * t) ^ 14 * (v + t) ^ 2 / 28 +
    (l * v + u * t) ^ 15 * (v + t) ^ 1 / 30 +
    (l * v + u * t) ^ 16 * (v + t) ^ 0 / 32
private def outsideReciprocalHom (l u v t : ℝ) : ℝ :=
  (3000 / 3029 : ℝ) * (v + t) ^ 4 -
    (2449 / 5000) * (l * v + u * t) * (v + t) ^ 3 -
    (1 / 20) * (l * v + u * t) ^ 3 * (v + t) - (3 / 100) * (l * v + u * t) ^ 4
private def outsideResidualHom (l u v t : ℝ) : ℝ :=
  outsidePotentialHom l u v t * outsideReciprocalHom l u v t - (v + t) ^ 20
private theorem outside_lower_first {v t : ℝ} (hv : 0 ≤ v) (ht : 0 ≤ t) : 0 ≤ outsideResidualHom 0 (1 / 4) v t := by
  unfold outsideResidualHom outsidePotentialHom outsideReciprocalHom
  ring_nf
  positivity
private theorem outside_lower_middle {v t : ℝ} (hv : 0 ≤ v) (ht : 0 ≤ t) : 0 ≤ outsideResidualHom (1 / 4) (1 / 2) v t := by
  unfold outsideResidualHom outsidePotentialHom outsideReciprocalHom
  ring_nf
  positivity
private theorem outside_lower_last {v t : ℝ} (hv : 0 ≤ v) (ht : 0 ≤ t) : 0 ≤ outsideResidualHom (1 / 2) (71 / 100) v t := by
  unfold outsideResidualHom outsidePotentialHom outsideReciprocalHom
  ring_nf
  positivity

private def outsideUpperResidualHom (l u v t : ℝ) : ℝ :=
  (101 / 100 : ℝ) * (v + t) ^ 20 -
    outsidePotentialHom l u v t * outsideReciprocalHom l u v t
private theorem outside_upper_first {v t : ℝ} (hv : 0 ≤ v) (ht : 0 ≤ t) : 0 ≤ outsideUpperResidualHom 0 (1 / 4) v t := by
  unfold outsideUpperResidualHom outsidePotentialHom outsideReciprocalHom
  ring_nf
  positivity
private theorem outside_upper_middle {v t : ℝ} (hv : 0 ≤ v) (ht : 0 ≤ t) : 0 ≤ outsideUpperResidualHom (1 / 4) (1 / 2) v t := by
  unfold outsideUpperResidualHom outsidePotentialHom outsideReciprocalHom
  ring_nf
  positivity
private theorem outside_upper_last {v t : ℝ} (hv : 0 ≤ v) (ht : 0 ≤ t) : 0 ≤ outsideUpperResidualHom (1 / 2) (71 / 100) v t := by
  unfold outsideUpperResidualHom outsidePotentialHom outsideReciprocalHom
  ring_nf
  positivity

private def outsidePotential (x : ℝ) : ℝ :=
  (3029 / 3000 : ℝ) +
    x ^ 1 / 2 +
    x ^ 2 / 4 +
    x ^ 3 / 6 +
    x ^ 4 / 8 +
    x ^ 5 / 10 +
    x ^ 6 / 12 +
    x ^ 7 / 14 +
    x ^ 8 / 16 +
    x ^ 9 / 18 +
    x ^ 10 / 20 +
    x ^ 11 / 22 +
    x ^ 12 / 24 +
    x ^ 13 / 26 +
    x ^ 14 / 28 +
    x ^ 15 / 30 +
    x ^ 16 / 32

private def outsideReciprocal (x : ℝ) : ℝ :=
  3000 / 3029 - (2449 / 5000) * x - x ^ 3 / 20 - 3 * x ^ 4 / 100

private theorem outsideResidualHom_identity (l u x : ℝ) :
    (u - l) ^ 20 * (outsidePotential x * outsideReciprocal x - 1) =
      outsideResidualHom l u (u - x) (x - l) := by
  unfold outsideResidualHom outsidePotentialHom outsideReciprocalHom
  rw [show (u - x) + (x - l) = u - l by ring,
    show l * (u - x) + u * (x - l) = x * (u - l) by ring]
  unfold outsidePotential outsideReciprocal
  generalize u - l = s
  ring

private theorem outsideUpperResidualHom_identity (l u x : ℝ) :
    (u - l) ^ 20 * (101 / 100 - outsidePotential x * outsideReciprocal x) =
      outsideUpperResidualHom l u (u - x) (x - l) := by
  unfold outsideUpperResidualHom outsidePotentialHom outsideReciprocalHom
  rw [show (u - x) + (x - l) = u - l by ring,
    show l * (u - x) + u * (x - l) = x * (u - l) by ring]
  unfold outsidePotential outsideReciprocal
  generalize u - l = s
  ring

private theorem outside_interval_bounds {l u x : ℝ} (hlu : l < u) (hx : l ≤ x) (hxu : x ≤ u)
    (hl : ∀ v t : ℝ, 0 ≤ v → 0 ≤ t → 0 ≤ outsideResidualHom l u v t)
    (hu : ∀ v t : ℝ, 0 ≤ v → 0 ≤ t → 0 ≤ outsideUpperResidualHom l u v t) :
    1 ≤ outsidePotential x * outsideReciprocal x ∧
      outsidePotential x * outsideReciprocal x ≤ 101 / 100 := by
  have h1 := hl (u - x) (x - l) (sub_nonneg.mpr hxu) (sub_nonneg.mpr hx)
  have h2 := hu (u - x) (x - l) (sub_nonneg.mpr hxu) (sub_nonneg.mpr hx)
  rw [← outsideResidualHom_identity] at h1
  rw [← outsideUpperResidualHom_identity] at h2
  have hp := pow_pos (sub_pos.mpr hlu) 20
  exact ⟨sub_nonneg.mp (nonneg_of_mul_nonneg_right h1 hp),
    sub_nonneg.mp (nonneg_of_mul_nonneg_right h2 hp)⟩

private theorem outside_product_bounds {x : ℝ} (hx : 0 ≤ x) (hx1 : x ≤ 71 / 100) :
    1 ≤ outsidePotential x * outsideReciprocal x ∧
      outsidePotential x * outsideReciprocal x ≤ 101 / 100 := by
  by_cases h1 : x ≤ 1 / 4
  · exact outside_interval_bounds (by norm_num) hx h1
      (fun _ _ hv ht => outside_lower_first hv ht)
      (fun _ _ hv ht => outside_upper_first hv ht)
  by_cases h2 : x ≤ 1 / 2
  · exact outside_interval_bounds (by norm_num) (le_of_not_ge h1) h2
      (fun _ _ hv ht => outside_lower_middle hv ht)
      (fun _ _ hv ht => outside_upper_middle hv ht)
  exact outside_interval_bounds (by norm_num) (le_of_not_ge h2) hx1
    (fun _ _ hv ht => outside_lower_last hv ht)
    (fun _ _ hv ht => outside_upper_last hv ht)

private def refinedOutsideReciprocal (x : ℝ) : ℝ :=
  outsideReciprocal x * (201 - 100 * outsidePotential x * outsideReciprocal x) / 101

private theorem refinedOutsideReciprocal_bound {x : ℝ} (hx : 0 ≤ x) (hx1 : x ≤ 71 / 100) :
    0 < refinedOutsideReciprocal x ∧ 1 ≤ outsidePotential x * refinedOutsideReciprocal x := by
  have hp := outside_product_bounds hx hx1
  have hV : 0 < outsidePotential x := by unfold outsidePotential; positivity
  have hprod := mul_nonneg (sub_nonneg.mpr hp.1)
    (show 0 ≤ 101 - 100 * outsidePotential x * outsideReciprocal x by linarith only [hp.2])
  have hn : 1 ≤ outsidePotential x * refinedOutsideReciprocal x := by
    unfold refinedOutsideReciprocal
    nlinarith only [hprod]
  refine ⟨?_, hn⟩
  by_contra h
  have hz := mul_nonpos_of_nonneg_of_nonpos hV.le (le_of_not_gt h)
  linarith only [hn, hz]

private def stripTaylorCoefficient (l : ℝ) (k : ℕ) : ℝ :=
  (if k = 0 then 3029 / 3000 else 0) +
    ∑ j ∈ Finset.range 32,
      (Nat.choose (2 * (j + 1)) k : ℝ) * l ^ (2 * (j + 1) - k) / (2 * ((j : ℝ) + 1))

private def stripTaylorHom (l u v t : ℝ) : ℝ :=
  ∑ k ∈ Finset.range 9, stripTaylorCoefficient l k *
    (u - l) ^ k * t ^ k * (v + t) ^ (8 - k)

private def stripReciprocalHom (l u v t : ℝ) : ℝ :=
  (309 / 500 : ℝ) * (v + t) ^ 4 -
    (21 / 20) * ((l * v + u * t) - (337 / 400) * (v + t)) * (v + t) ^ 3 -
    (18 / 5) * ((l * v + u * t) - (337 / 400) * (v + t)) ^ 2 * (v + t) ^ 2 -
    150 * ((l * v + u * t) - (337 / 400) * (v + t)) ^ 2 *
      ((l * v + u * t) - (23 / 25) * (v + t)) ^ 2

private def stripTaylorResidual (l u v t : ℝ) : ℝ :=
  stripTaylorHom l u v t * stripReciprocalHom l u v t - (v + t) ^ 12

private theorem strip_lower_first {v t : ℝ} (hv : 0 ≤ v) (ht : 0 ≤ t) : 0 ≤ stripTaylorResidual (84249 / 100000) (9 / 10) v t := by
  unfold stripTaylorResidual stripTaylorHom
  norm_num [stripTaylorCoefficient, Finset.sum_range_succ, Nat.choose]
  apply sub_nonneg.mp
  unfold stripReciprocalHom
  ring_nf
  positivity

private theorem strip_lower_middle {v t : ℝ} (hv : 0 ≤ v) (ht : 0 ≤ t) : 0 ≤ stripTaylorResidual (9 / 10) (47 / 50) v t := by
  unfold stripTaylorResidual stripTaylorHom
  norm_num [stripTaylorCoefficient, Finset.sum_range_succ, Nat.choose]
  apply sub_nonneg.mp
  unfold stripReciprocalHom
  ring_nf
  positivity

private theorem strip_lower_last {v t : ℝ} (hv : 0 ≤ v) (ht : 0 ≤ t) : 0 ≤ stripTaylorResidual (47 / 50) 1 v t := by
  unfold stripTaylorResidual stripTaylorHom
  norm_num [stripTaylorCoefficient, Finset.sum_range_succ, Nat.choose]
  apply sub_nonneg.mp
  unfold stripReciprocalHom
  ring_nf
  positivity


/-- Polynomial reciprocal on the reflected strip. -/
def firstOverlapEvenStripReciprocal (x : ℝ) : ℝ :=
  309 / 500 - (21 / 20) * (x - 337 / 400) - (18 / 5) * (x - 337 / 400) ^ 2 -
    150 * (x - 337 / 400) ^ 2 * (x - 23 / 25) ^ 2

private theorem qStrip_bounds {x : ℝ} (hx : 84249 / 100000 ≤ x) (hx1 : x ≤ 1) :
    (1 / 3 : ℝ) ≤ firstOverlapEvenStripReciprocal x ∧ firstOverlapEvenStripReciprocal x ≤ 31 / 50 := by
  let d := x - 337 / 400
  let y := x - 23 / 25
  have hd : |d| ≤ 63 / 400 := by
    rw [abs_le]
    dsimp [d]
    constructor <;> linarith only [hx, hx1]
  have hy : |y| ≤ 2 / 25 := by
    rw [abs_le]
    dsimp [y]
    constructor <;> linarith only [hx, hx1]
  have hd2 : d ^ 2 ≤ (63 / 400 : ℝ) ^ 2 := by
    have h := pow_le_pow_left₀ (abs_nonneg d) hd 2
    simpa only [sq_abs] using h
  have hy2 : y ^ 2 ≤ (2 / 25 : ℝ) ^ 2 := by
    have h := pow_le_pow_left₀ (abs_nonneg y) hy 2
    simpa only [sq_abs] using h
  have hprod := mul_le_mul hd2 hy2 (sq_nonneg y) (by positivity : 0 ≤ (63 / 400 : ℝ) ^ 2)
  have hdup : d ≤ 63 / 400 := (le_abs_self d).trans hd
  have hdlo : -(1 / 100000 : ℝ) ≤ d := by dsimp [d]; linarith only [hx]
  change 1 / 3 ≤ 309 / 500 - (21 / 20) * d - (18 / 5) * d ^ 2 - 150 * d ^ 2 * y ^ 2 ∧
    309 / 500 - (21 / 20) * d - (18 / 5) * d ^ 2 - 150 * d ^ 2 * y ^ 2 ≤ 31 / 50
  constructor
  · nlinarith only [hdup, hd2, hprod]
  · nlinarith only [hdlo, sq_nonneg d, mul_nonneg (sq_nonneg d) (sq_nonneg y)]


private theorem binomial_prefix_le (n m : ℕ) {l h : ℝ} (hl : 0 ≤ l) (hh : 0 ≤ h) :
    (∑ k ∈ Finset.range m, (Nat.choose n k : ℝ) * l ^ (n - k) * h ^ k) ≤ (l + h) ^ n := by
  let f : ℕ → ℝ := fun k => (Nat.choose n k : ℝ) * l ^ (n - k) * h ^ k
  have he : (∑ k ∈ Finset.range (n + 1), f k) = (l + h) ^ n := by
    rw [add_comm l h, add_pow]
    apply Finset.sum_congr rfl
    intro k _
    dsimp [f]
    ring
  have hext : (∑ k ∈ Finset.range (n + 1), f k) =
      ∑ k ∈ Finset.range (n + m + 1), f k := by
    apply Finset.sum_subset (Finset.range_mono (by omega))
    intro k _ hk
    have hnk : n < k := by simp only [Finset.mem_range] at hk; omega
    dsimp [f]
    rw [Nat.choose_eq_zero_of_lt hnk]
    simp
  change (∑ k ∈ Finset.range m, f k) ≤ _
  rw [← he, hext]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (by omega))
    (fun k _ _ => by dsimp [f]; positivity)

/-- Logarithmic boundary potential retained through degree sixty-four. -/
def firstOverlapEvenPotential (x : ℝ) : ℝ :=
  3029 / 3000 + ∑ j ∈ Finset.range 32, x ^ (2 * (j + 1)) / (2 * ((j : ℝ) + 1))
private def stripTaylor (l x : ℝ) : ℝ :=
  ∑ k ∈ Finset.range 9, stripTaylorCoefficient l k * (x - l) ^ k

private theorem stripTaylor_expansion (l x : ℝ) :
    stripTaylor l x = 3029 / 3000 +
      ∑ j ∈ Finset.range 32, (∑ k ∈ Finset.range 9,
        (Nat.choose (2 * (j + 1)) k : ℝ) * l ^ (2 * (j + 1) - k) * (x - l) ^ k) /
          (2 * ((j : ℝ) + 1)) := by
  unfold stripTaylor stripTaylorCoefficient
  simp_rw [add_mul, Finset.sum_mul]
  rw [Finset.sum_add_distrib, Finset.sum_comm]
  have hc : (∑ k ∈ Finset.range 9,
      (if k = 0 then (3029 / 3000 : ℝ) else 0) * (x - l) ^ k) = 3029 / 3000 := by
    simp [ite_mul]
  rw [hc]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  simp_rw [div_mul_eq_mul_div]
  rw [Finset.sum_div]

private theorem stripTaylor_le_potential {l x : ℝ} (hl : 0 ≤ l) (hx : l ≤ x) :
    stripTaylor l x ≤ firstOverlapEvenPotential x := by
  rw [stripTaylor_expansion]
  unfold firstOverlapEvenPotential
  apply add_le_add le_rfl
  apply Finset.sum_le_sum
  intro j _
  have h := binomial_prefix_le (2 * (j + 1)) 9 hl (sub_nonneg.mpr hx)
  rw [add_sub_cancel] at h
  exact div_le_div_of_nonneg_right h (by positivity)

private theorem stripTaylorHom_identity (l u x : ℝ) :
    (u - l) ^ 8 * stripTaylor l x = stripTaylorHom l u (u - x) (x - l) := by
  unfold stripTaylor stripTaylorHom
  rw [Finset.mul_sum, show (u - x) + (x - l) = u - l by ring]
  apply Finset.sum_congr rfl
  intro k hk
  have hkle : k ≤ 8 := by simpa only [Finset.mem_range, Nat.lt_succ_iff] using hk
  have hp : (u - l) ^ 8 = (u - l) ^ k * (u - l) ^ (8 - k) := by
    rw [← pow_add, Nat.add_sub_of_le hkle]
  rw [hp]
  ring

private theorem stripReciprocalHom_identity (l u x : ℝ) :
    (u - l) ^ 4 * firstOverlapEvenStripReciprocal x = stripReciprocalHom l u (u - x) (x - l) := by
  unfold stripReciprocalHom
  rw [show (u - x) + (x - l) = u - l by ring,
    show l * (u - x) + u * (x - l) = x * (u - l) by ring]
  unfold firstOverlapEvenStripReciprocal
  generalize u - l = s
  ring

private theorem stripTaylorResidual_identity (l u x : ℝ) :
    (u - l) ^ 12 * (stripTaylor l x * firstOverlapEvenStripReciprocal x - 1) =
      stripTaylorResidual l u (u - x) (x - l) := by
  unfold stripTaylorResidual
  rw [← stripTaylorHom_identity, ← stripReciprocalHom_identity,
    show (u - x) + (x - l) = u - l by ring]
  ring

private theorem strip_interval_bound {l u x : ℝ} (hlu : l < u) (hl : 0 ≤ l)
    (hx : l ≤ x) (hxu : x ≤ u) (hx0 : 84249 / 100000 ≤ x) (hx1 : x ≤ 1)
    (hp : ∀ v t : ℝ, 0 ≤ v → 0 ≤ t → 0 ≤ stripTaylorResidual l u v t) :
    1 ≤ firstOverlapEvenPotential x * firstOverlapEvenStripReciprocal x := by
  have h := hp (u - x) (x - l) (sub_nonneg.mpr hxu) (sub_nonneg.mpr hx)
  rw [← stripTaylorResidual_identity] at h
  have ht : 1 ≤ stripTaylor l x * firstOverlapEvenStripReciprocal x :=
    sub_nonneg.mp (nonneg_of_mul_nonneg_right h (pow_pos (sub_pos.mpr hlu) 12))
  have hq := (qStrip_bounds hx0 hx1).1
  exact ht.trans (mul_le_mul_of_nonneg_right (stripTaylor_le_potential hl hx)
    (by linarith only [hq]))

private theorem strip_reciprocal_bound {x : ℝ} (hx : 84249 / 100000 ≤ x) (hx1 : x ≤ 1) :
    0 < firstOverlapEvenStripReciprocal x ∧ 1 ≤ firstOverlapEvenPotential x * firstOverlapEvenStripReciprocal x := by
  have hq := (qStrip_bounds hx hx1).1
  refine ⟨by linarith only [hq], ?_⟩
  by_cases h1 : x ≤ 9 / 10
  · exact strip_interval_bound (by norm_num) (by norm_num) hx h1 hx hx1
      (fun _ _ hv ht => strip_lower_first hv ht)
  by_cases h2 : x ≤ 47 / 50
  · exact strip_interval_bound (by norm_num) (by norm_num) (le_of_not_ge h1) h2 hx hx1
      (fun _ _ hv ht => strip_lower_middle hv ht)
  exact strip_interval_bound (by norm_num) (by norm_num) (le_of_not_ge h2) hx1 hx hx1
    (fun _ _ hv ht => strip_lower_last hv ht)

/-- Refined reciprocal outside the reflected strip. -/
def firstOverlapEvenOutsideReciprocal (x : ℝ) : ℝ := refinedOutsideReciprocal (x ^ 2)

private theorem outsidePotential_le_full (x : ℝ) :
    outsidePotential (x ^ 2) ≤ firstOverlapEvenPotential x := by
  have he : firstOverlapEvenPotential x - outsidePotential (x ^ 2) =
      ∑ j ∈ Finset.range 16, x ^ (2 * (j + 17)) / (2 * ((j : ℝ) + 17)) := by
    unfold firstOverlapEvenPotential outsidePotential
    norm_num [Finset.sum_range_succ]
    ring
  apply sub_nonneg.mp
  rw [he]
  apply Finset.sum_nonneg
  intro j _
  apply div_nonneg
  · rw [pow_mul]
    exact pow_nonneg (sq_nonneg x) _
  · positivity

/-- The refined outside polynomial majorizes the reciprocal of the retained potential. -/
theorem firstOverlapEvenOutsideReciprocal_bound {x : ℝ}
    (hx : 0 ≤ x) (hx1 : x ≤ 337 / 400) :
    0 < firstOverlapEvenOutsideReciprocal x ∧
      1 ≤ firstOverlapEvenPotential x * firstOverlapEvenOutsideReciprocal x := by
  have hx2 : x ^ 2 ≤ 71 / 100 := by nlinarith only [hx, hx1]
  have h := refinedOutsideReciprocal_bound (sq_nonneg x) hx2
  refine ⟨h.1, h.2.trans ?_⟩
  exact mul_le_mul_of_nonneg_right (outsidePotential_le_full x) h.1.le

/-- The strip polynomial majorizes the reciprocal of the retained potential. -/
theorem firstOverlapEvenStripReciprocal_bound {x : ℝ}
    (hx : 84249 / 100000 ≤ x) (hx1 : x ≤ 1) :
    0 < firstOverlapEvenStripReciprocal x ∧
      1 ≤ firstOverlapEvenPotential x * firstOverlapEvenStripReciprocal x :=
  strip_reciprocal_bound hx hx1

/-- Uniform bounds keep the reflected pair inverse away from its pole. -/
theorem firstOverlapEvenStripReciprocal_range {x : ℝ}
    (hx : 84249 / 100000 ≤ x) (hx1 : x ≤ 1) :
    1 / 3 ≤ firstOverlapEvenStripReciprocal x ∧ firstOverlapEvenStripReciprocal x ≤ 31 / 50 :=
  qStrip_bounds hx hx1

/-- The finite boundary potential lies below the logarithmic boundary term. -/
theorem firstOverlapEvenPotential_le_log {x : ℝ} (hx : 0 ≤ x) (hx1 : x < 1) :
    firstOverlapEvenPotential x ≤ 3029 / 3000 - Real.log (1 - x ^ 2) / 2 := by
  have hx2 : |x ^ 2| < 1 := by rw [abs_of_nonneg (sq_nonneg x)]; nlinarith only [hx, hx1]
  have hs := Real.hasSum_pow_div_log_of_abs_lt_one hx2
  have hb := Summable.sum_le_tsum (Finset.range 32)
    (fun n _ => show 0 ≤ (x ^ 2) ^ (n + 1) / ((n : ℝ) + 1) by positivity) hs.summable
  rw [hs.tsum_eq] at hb
  have he : (∑ n ∈ Finset.range 32, (x ^ 2) ^ (n + 1) / ((n : ℝ) + 1)) =
      2 * (firstOverlapEvenPotential x - 3029 / 3000) := by
    unfold firstOverlapEvenPotential
    rw [add_sub_cancel_left, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro n _
    rw [← pow_mul]
    field_simp [show (n : ℝ) + 1 ≠ 0 by positivity]
  rw [he] at hb
  linarith only [hb]

end GaloisForLFunctions.WindowTowerOfSpecZ

#print axioms GaloisForLFunctions.WindowTowerOfSpecZ.firstOverlapEvenOutsideReciprocal_bound
#print axioms GaloisForLFunctions.WindowTowerOfSpecZ.firstOverlapEvenStripReciprocal_bound
#print axioms GaloisForLFunctions.WindowTowerOfSpecZ.firstOverlapEvenPotential_le_log
