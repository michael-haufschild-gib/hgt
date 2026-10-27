import Mathlib.Data.Real.Basic
import Mathlib.Tactic

/-!
# Reflection pairing for transverse work

Pairing a charge with its critical-line reflection separates transverse work
into a nonnegative angular energy and a mixed term. The mixed term is controlled
by height separation even when charges approach one another. All quotients use
the totalized real division, so coincident charges require no exclusion.
-/

noncomputable section

namespace GaloisForLFunctions.ArithmeticElectrostatics

/-- The transverse fraction of a squared displacement. -/
def transverseAngular (x d : ℝ) : ℝ := x ^ 2 / (x ^ 2 + d ^ 2)

/-- The angular energy of a pair and its reflection. -/
def reflectedEnergy (x y d : ℝ) : ℝ :=
  transverseAngular x d + transverseAngular y d

/-- The mixed term introduced by unequal height weights. -/
def reflectedCross (x y d : ℝ) : ℝ :=
  x * y * (1 / (x ^ 2 + d ^ 2) + 1 / (y ^ 2 + d ^ 2))

/-- Reflection-paired work, in sum and difference coordinates. -/
def reflectedWork (x y d v w : ℝ) : ℝ :=
  ((v + w) * reflectedEnergy x y d + (v - w) * reflectedCross x y d) / 2

theorem transverseAngular_nonneg (x d : ℝ) : 0 ≤ transverseAngular x d :=
  div_nonneg (sq_nonneg x) (add_nonneg (sq_nonneg x) (sq_nonneg d))

theorem reflectedEnergy_nonneg (x y d : ℝ) : 0 ≤ reflectedEnergy x y d :=
  add_nonneg (transverseAngular_nonneg x d) (transverseAngular_nonneg y d)

/-- Expanding the pair and its reflection gives the mixed-term decomposition. -/
theorem reflectedWork_eq_pair (a b d v w : ℝ) :
    reflectedWork (a - b) (a + b) d v w =
      (v * a - w * b) * (a - b) / ((a - b) ^ 2 + d ^ 2) +
      (v * a + w * b) * (a + b) / ((a + b) ^ 2 + d ^ 2) := by
  unfold reflectedWork reflectedEnergy reflectedCross transverseAngular
  ring

/-- The mixed term multiplied by height separation stays controlled near a collision. -/
theorem reflectedCross_near (x y d : ℝ)
    (hxy : x ^ 2 + y ^ 2 ≤ 1) (hd : d ^ 2 ≤ 1) :
    |d * reflectedCross x y d| ≤ 2 * reflectedEnergy x y d := by
  have hE := reflectedEnergy_nonneg x y d
  by_cases hd0 : d = 0
  · simpa only [hd0, zero_mul, abs_zero] using mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hE
  have hx : 0 < x ^ 2 + d ^ 2 := add_pos_of_nonneg_of_pos (sq_nonneg x) (sq_pos_of_ne_zero hd0)
  have hy : 0 < y ^ 2 + d ^ 2 := add_pos_of_nonneg_of_pos (sq_nonneg y) (sq_pos_of_ne_zero hd0)
  let B := y ^ 2 / (x ^ 2 + d ^ 2) + x ^ 2 / (y ^ 2 + d ^ 2)
  have hcs : reflectedCross x y d ^ 2 ≤ reflectedEnergy x y d * B := by
    have hid : reflectedEnergy x y d * B - reflectedCross x y d ^ 2 =
        (1 / (x ^ 2 + d ^ 2)) * (1 / (y ^ 2 + d ^ 2)) * (x ^ 2 - y ^ 2) ^ 2 := by
      dsimp only [B, reflectedEnergy, transverseAngular, reflectedCross]
      ring
    have hn : 0 ≤ (1 / (x ^ 2 + d ^ 2)) * (1 / (y ^ 2 + d ^ 2)) *
        (x ^ 2 - y ^ 2) ^ 2 := by positivity
    linarith only [hid, hn]
  have hB : d ^ 2 * B ≤ (d ^ 2 + x ^ 2 + y ^ 2) * reflectedEnergy x y d := by
    have hid : (d ^ 2 + x ^ 2 + y ^ 2) * reflectedEnergy x y d - d ^ 2 * B =
        2 * x ^ 2 * y ^ 2 * (2 * d ^ 2 + x ^ 2 + y ^ 2) /
          ((x ^ 2 + d ^ 2) * (y ^ 2 + d ^ 2)) := by
      dsimp only [B, reflectedEnergy, transverseAngular]
      field_simp
      ring
    have hn : 0 ≤ 2 * x ^ 2 * y ^ 2 * (2 * d ^ 2 + x ^ 2 + y ^ 2) /
        ((x ^ 2 + d ^ 2) * (y ^ 2 + d ^ 2)) := by positivity
    linarith only [hid, hn]
  have hbound : (d * reflectedCross x y d) ^ 2 ≤ 2 * reflectedEnergy x y d ^ 2 := by
    have h1 := mul_le_mul_of_nonneg_left hcs (sq_nonneg d)
    have h2 := mul_le_mul_of_nonneg_left hB hE
    have h3 : d ^ 2 + x ^ 2 + y ^ 2 ≤ 2 := by linarith only [hxy, hd]
    have h4 := mul_le_mul_of_nonneg_right h3 (sq_nonneg (reflectedEnergy x y d))
    nlinarith only [h1, h2, h4]
  apply (sq_le_sq₀ (abs_nonneg _) (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hE)).mp
  rw [sq_abs]
  nlinarith only [hbound, sq_nonneg (reflectedEnergy x y d)]

/-- Beyond unit height separation, the mixed term is bounded by angular energy. -/
theorem reflectedCross_far (x y d : ℝ)
    (hxy : x ^ 2 + y ^ 2 ≤ 1) (hd : 1 ≤ d ^ 2) :
    |reflectedCross x y d| ≤ reflectedEnergy x y d := by
  have hx : 0 < x ^ 2 + d ^ 2 := by nlinarith only [sq_nonneg x, hd]
  have hy : 0 < y ^ 2 + d ^ 2 := by nlinarith only [sq_nonneg y, hd]
  have hm : 0 ≤ d ^ 2 - x * y := by nlinarith only [hxy, hd, sq_nonneg (x - y)]
  have hp : 0 ≤ d ^ 2 + x * y := by nlinarith only [hxy, hd, sq_nonneg (x + y)]
  have hminus : reflectedEnergy x y d - reflectedCross x y d =
      (x - y) ^ 2 * (d ^ 2 - x * y) / ((x ^ 2 + d ^ 2) * (y ^ 2 + d ^ 2)) := by
    unfold reflectedEnergy transverseAngular reflectedCross
    field_simp
    ring
  have hplus : reflectedEnergy x y d + reflectedCross x y d =
      (x + y) ^ 2 * (d ^ 2 + x * y) / ((x ^ 2 + d ^ 2) * (y ^ 2 + d ^ 2)) := by
    unfold reflectedEnergy transverseAngular reflectedCross
    field_simp
    ring
  have hn : 0 ≤ reflectedEnergy x y d - reflectedCross x y d := by rw [hminus]; positivity
  have hp' : 0 ≤ reflectedEnergy x y d + reflectedCross x y d := by rw [hplus]; positivity
  exact abs_le.mpr ⟨by linarith only [hp'], by linarith only [hn]⟩

/-- A relative bound on the mixed term makes the paired work nonnegative. -/
theorem reflectedWork_bounds (x y d v w : ℝ)
    (hcross : |(v - w) * reflectedCross x y d| ≤ (v + w) * reflectedEnergy x y d) :
    0 ≤ reflectedWork x y d v w ∧
      reflectedWork x y d v w ≤ (v + w) * reflectedEnergy x y d := by
  obtain ⟨hlo, hhi⟩ := abs_le.mp hcross
  unfold reflectedWork
  constructor <;> linarith only [hlo, hhi]

/-- Rational height damping has a summable quadratic tail after angular row bounds. -/
def heightDamping (R t : ℝ) : ℝ := R ^ 4 / (R ^ 2 + t ^ 2) ^ 2

theorem heightDamping_nonneg (R t : ℝ) : 0 ≤ heightDamping R t := by
  unfold heightDamping
  positivity

theorem heightDamping_le_one {R : ℝ} (hR : 0 < R) (t : ℝ) :
    heightDamping R t ≤ 1 := by
  have hden : 0 < (R ^ 2 + t ^ 2) ^ 2 := by positivity
  unfold heightDamping
  apply (div_le_iff₀ hden).mpr
  nlinarith only [mul_nonneg (sq_nonneg R) (sq_nonneg t), sq_nonneg (t ^ 2)]

/-- The relative variation of rational damping is bounded by height separation. -/
theorem heightDamping_relative {R : ℝ} (hR : 0 < R) (t u : ℝ) :
    R * |heightDamping R t - heightDamping R u| ≤
      |t - u| * (heightDamping R t + heightDamping R u) := by
  let A := R ^ 2 + t ^ 2
  let B := R ^ 2 + u ^ 2
  have hA : 0 < A := by dsimp only [A]; positivity
  have hB : 0 < B := by dsimp only [B]; positivity
  have hsum : 0 ≤ A + B := by linarith only [hA, hB]
  have hlinear : 2 * R * |t + u| ≤ A + B := by
    have htri := mul_le_mul_of_nonneg_left (abs_add_le t u)
      (show 0 ≤ 2 * R by positivity)
    dsimp only [A, B]
    nlinarith only [htri, sq_nonneg (R - |t|), sq_nonneg (R - |u|), sq_abs t, sq_abs u]
  have hquadratic : R * |t + u| * (A + B) ≤ A ^ 2 + B ^ 2 := by
    have hm := mul_le_mul_of_nonneg_right hlinear hsum
    nlinarith only [hm, sq_nonneg (A - B)]
  let c := R ^ 4 / (A ^ 2 * B ^ 2)
  have hc : 0 ≤ c := by dsimp only [c]; positivity
  have hdiff : heightDamping R t - heightDamping R u =
      -c * (t - u) * (t + u) * (A + B) := by
    dsimp only [heightDamping, c, A, B]
    field_simp
    ring
  have hadd : heightDamping R t + heightDamping R u = c * (A ^ 2 + B ^ 2) := by
    dsimp only [heightDamping, c, A, B]
    field_simp
    ring
  calc
    R * |heightDamping R t - heightDamping R u| =
        (c * |t - u|) * (R * |t + u| * (A + B)) := by
      rw [hdiff]
      simp only [abs_mul, abs_neg, abs_of_nonneg hc, abs_of_nonneg hsum]
      ring
    _ ≤ (c * |t - u|) * (A ^ 2 + B ^ 2) :=
      mul_le_mul_of_nonneg_left hquadratic (mul_nonneg hc (abs_nonneg _))
    _ = |t - u| * (heightDamping R t + heightDamping R u) := by rw [hadd]; ring

/-- Rational damping controls the mixed term both near and far from a collision. -/
theorem heightDamping_cross_bound {R : ℝ} (hR : 4 ≤ R) (x y t u : ℝ)
    (hxy : x ^ 2 + y ^ 2 ≤ 1) :
    |(heightDamping R t - heightDamping R u) * reflectedCross x y (t - u)| ≤
      (heightDamping R t + heightDamping R u) * reflectedEnergy x y (t - u) := by
  have ht := heightDamping_nonneg R t
  have hu := heightDamping_nonneg R u
  by_cases hd : (t - u) ^ 2 ≤ 1
  · have h1 := mul_le_mul_of_nonneg_right
      (heightDamping_relative (show 0 < R by linarith only [hR]) t u)
      (abs_nonneg (reflectedCross x y (t - u)))
    have h2 := mul_le_mul_of_nonneg_left (reflectedCross_near x y (t - u) hxy hd)
      (add_nonneg ht hu)
    rw [abs_mul] at h2 ⊢
    have h3 := mul_nonneg (show 0 ≤ R - 2 by linarith only [hR])
      (mul_nonneg (abs_nonneg (heightDamping R t - heightDamping R u))
        (abs_nonneg (reflectedCross x y (t - u))))
    nlinarith only [h1, h2, h3]
  · have hdiff : |heightDamping R t - heightDamping R u| ≤
        heightDamping R t + heightDamping R u := by
      apply abs_le.mpr
      constructor <;> linarith only [ht, hu]
    rw [abs_mul]
    exact mul_le_mul hdiff (reflectedCross_far x y (t - u) hxy (le_of_not_ge hd))
      (abs_nonneg _) (add_nonneg ht hu)

/-- Reflection-paired rationally damped work is nonnegative and angularly dominated. -/
theorem heightDamping_work_bounds {R : ℝ} (hR : 4 ≤ R) (x y t u : ℝ)
    (hxy : x ^ 2 + y ^ 2 ≤ 1) :
    0 ≤ reflectedWork x y (t - u) (heightDamping R t) (heightDamping R u) ∧
      reflectedWork x y (t - u) (heightDamping R t) (heightDamping R u) ≤
        (heightDamping R t + heightDamping R u) * reflectedEnergy x y (t - u) :=
  reflectedWork_bounds x y (t - u) _ _ (heightDamping_cross_bound hR x y t u hxy)

end GaloisForLFunctions.ArithmeticElectrostatics
