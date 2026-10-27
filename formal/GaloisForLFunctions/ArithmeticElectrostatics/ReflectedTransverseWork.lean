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

/-- An angular row has at most quadratic growth in its base height. -/
theorem transverseAngular_height_bound (x t u : ℝ) (hx : x ^ 2 ≤ 1) :
    transverseAngular x (t - u) ≤ 2 * (1 + t ^ 2) / (1 + u ^ 2) := by
  have hu : 0 < 1 + u ^ 2 := by positivity
  by_cases hd : x ^ 2 + (t - u) ^ 2 = 0
  · unfold transverseAngular
    rw [hd, div_zero]
    positivity
  have hdpos : 0 < x ^ 2 + (t - u) ^ 2 :=
    lt_of_le_of_ne (add_nonneg (sq_nonneg x) (sq_nonneg (t - u))) (Ne.symm hd)
  have huBound : u ^ 2 ≤ 2 * t ^ 2 + 2 * (t - u) ^ 2 := by
    nlinarith only [sq_nonneg (2 * t - u)]
  have hm := mul_le_mul_of_nonneg_right huBound (sq_nonneg x)
  have hn := mul_nonneg (sq_nonneg (t - u))
    (show 0 ≤ 1 + t ^ 2 - x ^ 2 by nlinarith only [hx, sq_nonneg t])
  unfold transverseAngular
  apply (div_le_iff₀ hdpos).mpr
  calc
    x ^ 2 ≤ (2 * (1 + t ^ 2) * (x ^ 2 + (t - u) ^ 2)) / (1 + u ^ 2) :=
      (le_div_iff₀ hu).mpr (by nlinarith only [hm, hn, sq_nonneg x])
    _ = (2 * (1 + t ^ 2) / (1 + u ^ 2)) * (x ^ 2 + (t - u) ^ 2) := by ring

/-- Damping turns the row estimate into a product of inverse quadratic tails. -/
theorem heightDamping_angular_bound {R : ℝ} (hR : 1 ≤ R) (x t u : ℝ)
    (hx : x ^ 2 ≤ 1) :
    heightDamping R t * transverseAngular x (t - u) ≤
      2 * R ^ 4 / ((1 + t ^ 2) * (1 + u ^ 2)) := by
  have hRt : 0 < R ^ 2 + t ^ 2 := by nlinarith only [hR, sq_nonneg t]
  have ht : 0 < 1 + t ^ 2 := by positivity
  have hu : 0 < 1 + u ^ 2 := by positivity
  have hden : (1 + t ^ 2) ^ 2 ≤ (R ^ 2 + t ^ 2) ^ 2 := by
    apply (sq_le_sq₀ ht.le hRt.le).mpr
    nlinarith only [hR]
  have hw : heightDamping R t ≤ R ^ 4 / (1 + t ^ 2) ^ 2 := by
    unfold heightDamping
    exact div_le_div_of_nonneg_left (by positivity) (by positivity) hden
  calc
    heightDamping R t * transverseAngular x (t - u) ≤
        (R ^ 4 / (1 + t ^ 2) ^ 2) * (2 * (1 + t ^ 2) / (1 + u ^ 2)) :=
      mul_le_mul hw (transverseAngular_height_bound x t u hx)
        (transverseAngular_nonneg _ _) (by positivity)
    _ = 2 * R ^ 4 / ((1 + t ^ 2) * (1 + u ^ 2)) := by
      field_simp

/-- The full weighted reflected energy has an inverse-quadratic product majorant. -/
theorem heightDamping_energy_bound {R : ℝ} (hR : 1 ≤ R) (x y t u : ℝ)
    (hxy : x ^ 2 + y ^ 2 ≤ 1) :
    (heightDamping R t + heightDamping R u) * reflectedEnergy x y (t - u) ≤
      8 * R ^ 4 / ((1 + t ^ 2) * (1 + u ^ 2)) := by
  have hx : x ^ 2 ≤ 1 := by linarith only [hxy, sq_nonneg y]
  have hy : y ^ 2 ≤ 1 := by linarith only [hxy, sq_nonneg x]
  have h1 := heightDamping_angular_bound hR x t u hx
  have h2 := heightDamping_angular_bound hR y t u hy
  have h3 := heightDamping_angular_bound hR x u t hx
  have h4 := heightDamping_angular_bound hR y u t hy
  have hrev (z : ℝ) : transverseAngular z (u - t) = transverseAngular z (t - u) := by
    unfold transverseAngular
    rw [show (u - t) ^ 2 = (t - u) ^ 2 by ring]
  rw [hrev, mul_comm (1 + u ^ 2) (1 + t ^ 2)] at h3 h4
  unfold reflectedEnergy
  calc
    _ = (heightDamping R t * transverseAngular x (t - u) +
        heightDamping R t * transverseAngular y (t - u)) +
        (heightDamping R u * transverseAngular x (t - u) +
        heightDamping R u * transverseAngular y (t - u)) := by ring
    _ ≤ (2 * R ^ 4 / ((1 + t ^ 2) * (1 + u ^ 2)) +
        2 * R ^ 4 / ((1 + t ^ 2) * (1 + u ^ 2))) +
        (2 * R ^ 4 / ((1 + t ^ 2) * (1 + u ^ 2)) +
        2 * R ^ 4 / ((1 + t ^ 2) * (1 + u ^ 2))) :=
      add_le_add (add_le_add h1 h2) (add_le_add h3 h4)
    _ = _ := by ring

/-- A compact height taper, increasing pointwise to one. -/
def heightTaper (N : ℕ) (t : ℝ) : ℝ := max 0 (1 - |t| / ((N : ℝ) + 1))

theorem heightTaper_bounds (N : ℕ) (t : ℝ) :
    0 ≤ heightTaper N t ∧ heightTaper N t ≤ 1 := by
  refine ⟨le_max_left _ _, max_le (by norm_num) ?_⟩
  have h : 0 ≤ |t| / ((N : ℝ) + 1) := by positivity
  linarith only [h]

theorem heightTaper_eq_zero {N : ℕ} {t : ℝ} (ht : (N : ℝ) + 1 ≤ |t|) :
    heightTaper N t = 0 := by
  apply max_eq_left
  have hden : 0 < (N : ℝ) + 1 := by positivity
  have h := (le_div_iff₀ hden).mpr (show 1 * ((N : ℝ) + 1) ≤ |t| by simpa using ht)
  linarith only [h]

/-- All height tapers have Lipschitz constant at most one. -/
theorem heightTaper_lipschitz (N : ℕ) (t u : ℝ) :
    |heightTaper N t - heightTaper N u| ≤ |t - u| := by
  have hden : 0 < (N : ℝ) + 1 := by positivity
  calc
    |heightTaper N t - heightTaper N u| ≤
        |(1 - |t| / ((N : ℝ) + 1)) - (1 - |u| / ((N : ℝ) + 1))| := by
      unfold heightTaper
      rw [max_comm 0 (1 - |t| / ((N : ℝ) + 1)), max_comm 0 (1 - |u| / ((N : ℝ) + 1))]
      exact abs_max_sub_max_le_abs (1 - |t| / ((N : ℝ) + 1))
        (1 - |u| / ((N : ℝ) + 1)) 0
    _ = abs (|t| - |u|) / ((N : ℝ) + 1) := by
      rw [show (1 - |t| / ((N : ℝ) + 1)) - (1 - |u| / ((N : ℝ) + 1)) =
        -((|t| - |u|) / ((N : ℝ) + 1)) by ring]
      rw [abs_neg, abs_div, abs_of_pos hden]
    _ ≤ |t - u| / ((N : ℝ) + 1) :=
      div_le_div_of_nonneg_right (abs_abs_sub_abs_le_abs_sub t u) hden.le
    _ ≤ |t - u| := by
      apply (div_le_iff₀ hden).mpr
      have h := mul_nonneg (show (0 : ℝ) ≤ N by positivity) (abs_nonneg (t - u))
      nlinarith only [h]

private theorem heightDamping_taper_relative {R : ℝ} (hR : 0 < R)
    (t u c e : ℝ) (hc : 0 ≤ c ∧ c ≤ 1) (hce : |c - e| ≤ |t - u|) :
    R * |heightDamping R t * c - heightDamping R u * e| ≤
      (R + 1) * |t - u| * (heightDamping R t + heightDamping R u) := by
  have ht := heightDamping_nonneg R t
  have hu := heightDamping_nonneg R u
  have hdiff : |heightDamping R t * c - heightDamping R u * e| ≤
      |heightDamping R t - heightDamping R u| + heightDamping R u * |t - u| := by
    rw [show heightDamping R t * c - heightDamping R u * e =
      c * (heightDamping R t - heightDamping R u) + heightDamping R u * (c - e) by ring]
    apply (abs_add_le _ _).trans
    simp only [abs_mul, abs_of_nonneg hc.1, abs_of_nonneg hu]
    exact add_le_add (by simpa only [one_mul] using
      mul_le_mul_of_nonneg_right hc.2 (abs_nonneg (heightDamping R t - heightDamping R u)))
      (mul_le_mul_of_nonneg_left hce hu)
  have h1 := mul_le_mul_of_nonneg_left hdiff hR.le
  have h2 := heightDamping_relative hR t u
  have h3 := mul_nonneg (mul_nonneg hR.le (abs_nonneg (t - u))) ht
  nlinarith only [h1, h2, h3]

/-- Compact Lipschitz tapering preserves one summable absolute bound, uniformly in the cutoff. -/
theorem heightDamping_taper_work_bound {R : ℝ} (hR : 4 ≤ R) (x y t u c e : ℝ)
    (hxy : x ^ 2 + y ^ 2 ≤ 1) (hc : 0 ≤ c ∧ c ≤ 1) (he : 0 ≤ e ∧ e ≤ 1)
    (hce : |c - e| ≤ |t - u|) :
    |reflectedWork x y (t - u) (heightDamping R t * c) (heightDamping R u * e)| ≤
      2 * (heightDamping R t + heightDamping R u) * reflectedEnergy x y (t - u) := by
  have hRpos : 0 < R := by linarith only [hR]
  have ht := heightDamping_nonneg R t
  have hu := heightDamping_nonneg R u
  have hE := reflectedEnergy_nonneg x y (t - u)
  have hv := mul_nonneg ht hc.1
  have hw := mul_nonneg hu he.1
  have hvle : heightDamping R t * c ≤ heightDamping R t := by
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hc.2 ht
  have hwle : heightDamping R u * e ≤ heightDamping R u := by
    simpa only [mul_one] using mul_le_mul_of_nonneg_left he.2 hu
  have hcross : |(heightDamping R t * c - heightDamping R u * e) *
      reflectedCross x y (t - u)| ≤
      3 * (heightDamping R t + heightDamping R u) * reflectedEnergy x y (t - u) := by
    by_cases hd : (t - u) ^ 2 ≤ 1
    · have h1 := mul_le_mul_of_nonneg_right (heightDamping_taper_relative hRpos t u c e hc hce)
        (abs_nonneg (reflectedCross x y (t - u)))
      have h2 := mul_le_mul_of_nonneg_left (reflectedCross_near x y (t - u) hxy hd)
        (mul_nonneg (show 0 ≤ R + 1 by linarith only [hR]) (add_nonneg ht hu))
      have h3 := mul_nonneg (show 0 ≤ R - 2 by linarith only [hR])
        (mul_nonneg (add_nonneg ht hu) hE)
      apply (mul_le_mul_iff_right₀ hRpos).mp
      rw [abs_mul] at h2 ⊢
      nlinarith only [h1, h2, h3]
    · have hdiff : |heightDamping R t * c - heightDamping R u * e| ≤
          heightDamping R t + heightDamping R u := by
        apply abs_le.mpr
        constructor <;> linarith only [hv, hw, hvle, hwle]
      have h := mul_le_mul hdiff (reflectedCross_far x y (t - u) hxy (le_of_not_ge hd))
        (abs_nonneg _) (add_nonneg ht hu)
      rw [abs_mul]
      have hn := mul_nonneg (add_nonneg ht hu) hE
      linarith only [h, hn]
  have hmain := mul_le_mul_of_nonneg_right (add_le_add hvle hwle) hE
  have hsum := abs_add_le
    ((heightDamping R t * c + heightDamping R u * e) * reflectedEnergy x y (t - u))
    ((heightDamping R t * c - heightDamping R u * e) * reflectedCross x y (t - u))
  rw [abs_of_nonneg (mul_nonneg (add_nonneg hv hw) hE)] at hsum
  unfold reflectedWork
  rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  apply (div_le_iff₀ (by norm_num : (0 : ℝ) < 2)).mpr
  linarith only [hsum, hmain, hcross]

end GaloisForLFunctions.ArithmeticElectrostatics
