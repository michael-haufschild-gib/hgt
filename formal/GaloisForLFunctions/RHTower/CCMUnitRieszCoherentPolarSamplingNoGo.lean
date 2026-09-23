import GaloisForLFunctions.RHTower.CCMUnitRieszExponentialCoherentTrace

/-!
# Fixed-sample no-go for the bare unit-Riesz polar frame

The exact unit-Riesz coherent trace suggests comparing an atomic coherent projector with the
continuous polar average of the same increment frame.  This file proves that no finite Loewner
constant can make that comparison, even at the fixed lag `u = 1` and even on finite coherent
source-span packets.

The witness uses four equally spaced lags and coefficients

`[-1, 1 + exp(h/2) + exp(-h/2), -(1 + exp(h/2) + exp(-h/2)), 1]`.

Its three exponential moments cancel, so its Gram response is supported on a lag window of width
`3h`.  The fixed sample is `exp(h/2) - exp(-h/2)`, whereas its weighted polar energy is at most
`3h` times the sample square.  Letting `h` shrink rules out every finite domination constant.

The obstruction has a sharp positive survivor.  The source-Gram quadratic is positive and equals
one quarter of the packet's piecewise weak-generator graph energy

`integral (4 * |g'|^(2 : ℕ) + |g|^(2 : ℕ))`.

Thus bare polar averaging loses precisely the first-order anti-concentration channel; generator or
boundary-slope energy is forced.  This is an unconditional source-side theorem.  It does not bound
the arithmetic von-Mangoldt packet, construct the CCM ground-state transport, or prove RH.
-/

open Set MeasureTheory

noncomputable section

namespace GaloisForLFunctions.RHTower

def unitExponentialThirdDifferenceCoefficient (h : ℝ) : ℝ :=
  1 + Real.exp (h / 2) + Real.exp (-h / 2)

def unitExponentialThirdDifferenceResponse (a h u : ℝ) : ℝ :=
  -unitExponentialIncrementKernel a u +
    unitExponentialThirdDifferenceCoefficient h *
      unitExponentialIncrementKernel (a + h) u -
    unitExponentialThirdDifferenceCoefficient h *
      unitExponentialIncrementKernel (a + 2 * h) u +
    unitExponentialIncrementKernel (a + 3 * h) u

private theorem exp_half_mul_exp_neg_half (h : ℝ) :
    Real.exp (h / 2) * Real.exp (-h / 2) = 1 := by
  rw [← Real.exp_add]
  convert Real.exp_zero using 1
  ring

theorem unitExponentialThirdDifferenceResponse_eq_distancePacket
    (a h u : ℝ) :
    unitExponentialThirdDifferenceResponse a h u =
      -Real.exp (-|a - u| / 2) +
        unitExponentialThirdDifferenceCoefficient h *
          Real.exp (-|a + h - u| / 2) -
        unitExponentialThirdDifferenceCoefficient h *
          Real.exp (-|a + 2 * h - u| / 2) +
        Real.exp (-|a + 3 * h - u| / 2) := by
  have ea1 : Real.exp (-(a + h) / 2) =
      Real.exp (-a / 2) * Real.exp (-h / 2) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have ea2 : Real.exp (-(a + 2 * h) / 2) =
      Real.exp (-a / 2) * Real.exp (-h / 2) ^ (2 : ℕ) := by
    rw [pow_two, ← Real.exp_add, ← Real.exp_add]
    congr 1
    ring
  have ea3 : Real.exp (-(a + 3 * h) / 2) =
      Real.exp (-a / 2) * Real.exp (-h / 2) ^ (3 : ℕ) := by
    rw [pow_succ, pow_two, ← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
    congr 1
    ring
  simp only [unitExponentialThirdDifferenceResponse,
    unitExponentialThirdDifferenceCoefficient, unitExponentialIncrementKernel,
    ea1, ea2, ea3]
  have eh := exp_half_mul_exp_neg_half h
  have eh2 : Real.exp (h / 2) * Real.exp (-h / 2) ^ (2 : ℕ) =
      Real.exp (-h / 2) := by
    calc
      Real.exp (h / 2) * Real.exp (-h / 2) ^ (2 : ℕ) =
          (Real.exp (h / 2) * Real.exp (-h / 2)) * Real.exp (-h / 2) := by ring
      _ = _ := by rw [eh]; ring
  ring_nf at eh eh2 ⊢
  rw [eh2, eh]
  ring

theorem unitExponentialThirdDifferenceResponse_eq_first
    {a h u : ℝ} (hu0 : a ≤ u) (hu1 : u ≤ a + h) :
    unitExponentialThirdDifferenceResponse a h u =
      Real.exp ((u - a) / 2) - Real.exp (-(u - a) / 2) := by
  have h0 : |a - u| = u - a := by rw [abs_of_nonpos (sub_nonpos.mpr hu0)]; ring
  have h1 : |a + h - u| = a + h - u := by rw [abs_of_nonneg (sub_nonneg.mpr hu1)]
  have h2u : u ≤ a + 2 * h := by linarith
  have h2 : |a + 2 * h - u| = a + 2 * h - u := by rw [abs_of_nonneg (sub_nonneg.mpr h2u)]
  have h3u : u ≤ a + 3 * h := by linarith
  have h3 : |a + 3 * h - u| = a + 3 * h - u := by rw [abs_of_nonneg (sub_nonneg.mpr h3u)]
  have ea1 : Real.exp (-(a + h) / 2) = Real.exp (-a / 2) * Real.exp (-h / 2) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have ea2 : Real.exp (-(a + 2 * h) / 2) =
      Real.exp (-a / 2) * Real.exp (-h / 2) ^ (2 : ℕ) := by
    rw [pow_two, ← Real.exp_add, ← Real.exp_add]
    congr 1
    ring
  have ea3 : Real.exp (-(a + 3 * h) / 2) =
      Real.exp (-a / 2) * Real.exp (-h / 2) ^ (3 : ℕ) := by
    rw [pow_succ, pow_two, ← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
    congr 1
    ring
  have ec0 : Real.exp (-(a - u) / 2) =
      Real.exp (-a / 2) * Real.exp (u / 2) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have ec1 : Real.exp (-(a + h - u) / 2) =
      Real.exp (-a / 2) * Real.exp (-h / 2) * Real.exp (u / 2) := by
    rw [← Real.exp_add, ← Real.exp_add]
    congr 1
    ring
  have ec2 : Real.exp (-(a + 2 * h - u) / 2) =
      Real.exp (-a / 2) * Real.exp (-h / 2) ^ (2 : ℕ) * Real.exp (u / 2) := by
    rw [pow_two, ← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
    congr 1
    ring
  have ec3 : Real.exp (-(a + 3 * h - u) / 2) =
      Real.exp (-a / 2) * Real.exp (-h / 2) ^ (3 : ℕ) * Real.exp (u / 2) := by
    rw [pow_succ, pow_two, ← Real.exp_add, ← Real.exp_add, ← Real.exp_add,
      ← Real.exp_add]
    congr 1
    ring
  have erhs1 : Real.exp ((u - a) / 2) =
      Real.exp (-a / 2) * Real.exp (u / 2) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have erhs2 : Real.exp (-(u - a) / 2) =
      Real.exp (a / 2) * Real.exp (-u / 2) := by
    rw [← Real.exp_add]
    congr 1
    ring
  simp only [unitExponentialThirdDifferenceResponse,
    unitExponentialThirdDifferenceCoefficient, unitExponentialIncrementKernel,
    h0, h1, h2, h3, ea1, ea2, ea3, ec0, ec1, ec2, ec3, erhs1, erhs2]
  have eh := exp_half_mul_exp_neg_half h
  have eh2 : Real.exp (h / 2) * Real.exp (-h / 2) ^ (2 : ℕ) =
      Real.exp (-h / 2) := by
    calc
      Real.exp (h / 2) * Real.exp (-h / 2) ^ (2 : ℕ) =
          (Real.exp (h / 2) * Real.exp (-h / 2)) * Real.exp (-h / 2) := by ring
      _ = _ := by rw [eh]; ring
  ring_nf at eh eh2 ⊢
  rw [eh2, eh]
  ring

theorem unitExponentialThirdDifferenceResponse_eq_middle
    {a h u : ℝ} (hu1 : a + h ≤ u) (hu2 : u ≤ a + 2 * h) :
    unitExponentialThirdDifferenceResponse a h u =
      (1 + Real.exp (h / 2)) *
        (Real.exp ((a + h - u) / 2) -
          Real.exp ((u - a - 2 * h) / 2)) := by
  have h0u : a ≤ u := by linarith
  have hu3 : u ≤ a + 3 * h := by linarith
  have h0 : |a - u| = u - a := by
    rw [abs_of_nonpos (sub_nonpos.mpr h0u)]
    ring
  have h1 : |a + h - u| = u - a - h := by
    rw [abs_of_nonpos (sub_nonpos.mpr hu1)]
    ring
  have h2 : |a + 2 * h - u| = a + 2 * h - u := by
    rw [abs_of_nonneg (sub_nonneg.mpr hu2)]
  have h3 : |a + 3 * h - u| = a + 3 * h - u := by
    rw [abs_of_nonneg (sub_nonneg.mpr hu3)]
  have e0 : Real.exp (-(u - a) / 2) =
      Real.exp ((a + h - u) / 2) * Real.exp (-h / 2) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have e3 : Real.exp (-(a + 3 * h - u) / 2) =
      Real.exp ((u - a - 2 * h) / 2) * Real.exp (-h / 2) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [unitExponentialThirdDifferenceResponse_eq_distancePacket, h0, h1, h2, h3,
    e0, e3]
  simp only [unitExponentialThirdDifferenceCoefficient]
  ring

theorem unitExponentialThirdDifferenceResponse_eq_last
    {a h u : ℝ} (hu2 : a + 2 * h ≤ u) (hu3 : u ≤ a + 3 * h) :
    unitExponentialThirdDifferenceResponse a h u =
      Real.exp ((u - a - 3 * h) / 2) -
        Real.exp ((a + 3 * h - u) / 2) := by
  have h0u : a ≤ u := by linarith
  have h1u : a + h ≤ u := by linarith
  have h0 : |a - u| = u - a := by
    rw [abs_of_nonpos (sub_nonpos.mpr h0u)]
    ring
  have h1 : |a + h - u| = u - a - h := by
    rw [abs_of_nonpos (sub_nonpos.mpr h1u)]
    ring
  have h2 : |a + 2 * h - u| = u - a - 2 * h := by
    rw [abs_of_nonpos (sub_nonpos.mpr hu2)]
    ring
  have h3 : |a + 3 * h - u| = a + 3 * h - u := by
    rw [abs_of_nonneg (sub_nonneg.mpr hu3)]
  let W := Real.exp ((a + 3 * h - u) / 2)
  have e0 : Real.exp (-(u - a) / 2) = W * Real.exp (-h / 2) ^ (3 : ℕ) := by
    dsimp only [W]
    rw [pow_succ, pow_two, ← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
    congr 1
    ring
  have e1 : Real.exp (-(u - a - h) / 2) = W * Real.exp (-h / 2) ^ (2 : ℕ) := by
    dsimp only [W]
    rw [pow_two, ← Real.exp_add, ← Real.exp_add]
    congr 1
    ring
  have e2 : Real.exp (-(u - a - 2 * h) / 2) = W * Real.exp (-h / 2) := by
    dsimp only [W]
    rw [← Real.exp_add]
    congr 1
    ring
  rw [unitExponentialThirdDifferenceResponse_eq_distancePacket, h0, h1, h2, h3,
    e0, e1, e2]
  simp only [unitExponentialThirdDifferenceCoefficient, W]
  have eh := exp_half_mul_exp_neg_half h
  have eh2 : Real.exp (h / 2) * Real.exp (-h / 2) ^ (2 : ℕ) =
      Real.exp (-h / 2) := by
    calc
      Real.exp (h / 2) * Real.exp (-h / 2) ^ (2 : ℕ) =
          (Real.exp (h / 2) * Real.exp (-h / 2)) * Real.exp (-h / 2) := by ring
      _ = _ := by rw [eh]; ring
  ring_nf at eh eh2 ⊢
  rw [eh2, eh]
  ring

theorem unitExponentialThirdDifferenceResponse_eq_zero_of_le
    {a h u : ℝ} (hh : 0 ≤ h) (hu : u ≤ a) :
    unitExponentialThirdDifferenceResponse a h u = 0 := by
  have hu1 : u ≤ a + h := by linarith
  have hu2 : u ≤ a + 2 * h := by linarith
  have hu3 : u ≤ a + 3 * h := by linarith
  have h0 : |a - u| = a - u := abs_of_nonneg (sub_nonneg.mpr hu)
  have h1 : |a + h - u| = a + h - u := abs_of_nonneg (sub_nonneg.mpr hu1)
  have h2 : |a + 2 * h - u| = a + 2 * h - u := abs_of_nonneg (sub_nonneg.mpr hu2)
  have h3 : |a + 3 * h - u| = a + 3 * h - u := abs_of_nonneg (sub_nonneg.mpr hu3)
  let Z := Real.exp ((u - a) / 2)
  have e0 : Real.exp (-(a - u) / 2) = Z := by
    dsimp only [Z]
    congr 1
    ring
  have e1 : Real.exp (-(a + h - u) / 2) = Z * Real.exp (-h / 2) := by
    dsimp only [Z]
    rw [← Real.exp_add]
    congr 1
    ring
  have e2 : Real.exp (-(a + 2 * h - u) / 2) = Z * Real.exp (-h / 2) ^ (2 : ℕ) := by
    dsimp only [Z]
    rw [pow_two, ← Real.exp_add, ← Real.exp_add]
    congr 1
    ring
  have e3 : Real.exp (-(a + 3 * h - u) / 2) = Z * Real.exp (-h / 2) ^ (3 : ℕ) := by
    dsimp only [Z]
    rw [pow_succ, pow_two, ← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
    congr 1
    ring
  rw [unitExponentialThirdDifferenceResponse_eq_distancePacket, h0, h1, h2, h3,
    e0, e1, e2, e3]
  simp only [unitExponentialThirdDifferenceCoefficient, Z]
  have eh := exp_half_mul_exp_neg_half h
  have eh2 : Real.exp (h / 2) * Real.exp (-h / 2) ^ (2 : ℕ) =
      Real.exp (-h / 2) := by
    calc
      Real.exp (h / 2) * Real.exp (-h / 2) ^ (2 : ℕ) =
          (Real.exp (h / 2) * Real.exp (-h / 2)) * Real.exp (-h / 2) := by ring
      _ = _ := by rw [eh]; ring
  ring_nf at eh eh2 ⊢
  rw [eh2, eh]
  ring

theorem unitExponentialThirdDifferenceResponse_eq_zero_of_ge
    {a h u : ℝ} (hh : 0 ≤ h) (hu : a + 3 * h ≤ u) :
    unitExponentialThirdDifferenceResponse a h u = 0 := by
  have h0u : a ≤ u := by linarith
  have h1u : a + h ≤ u := by linarith
  have h2u : a + 2 * h ≤ u := by linarith
  have h0 : |a - u| = u - a := by rw [abs_of_nonpos (sub_nonpos.mpr h0u)]; ring
  have h1 : |a + h - u| = u - a - h := by rw [abs_of_nonpos (sub_nonpos.mpr h1u)]; ring
  have h2 : |a + 2 * h - u| = u - a - 2 * h := by rw [abs_of_nonpos (sub_nonpos.mpr h2u)]; ring
  have h3 : |a + 3 * h - u| = u - a - 3 * h := by rw [abs_of_nonpos (sub_nonpos.mpr hu)]; ring
  let Y := Real.exp ((a - u) / 2)
  have e0 : Real.exp (-(u - a) / 2) = Y := by dsimp only [Y]; congr 1 <;> ring
  have e1 : Real.exp (-(u - a - h) / 2) = Y * Real.exp (h / 2) := by
    dsimp only [Y]
    rw [← Real.exp_add]
    congr 1
    ring
  have e2 : Real.exp (-(u - a - 2 * h) / 2) = Y * Real.exp (h / 2) ^ (2 : ℕ) := by
    dsimp only [Y]
    rw [pow_two, ← Real.exp_add, ← Real.exp_add]
    congr 1
    ring
  have e3 : Real.exp (-(u - a - 3 * h) / 2) = Y * Real.exp (h / 2) ^ (3 : ℕ) := by
    dsimp only [Y]
    rw [pow_succ, pow_two, ← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
    congr 1
    ring
  rw [unitExponentialThirdDifferenceResponse_eq_distancePacket, h0, h1, h2, h3,
    e0, e1, e2, e3]
  simp only [unitExponentialThirdDifferenceCoefficient, Y]
  have eh := exp_half_mul_exp_neg_half h
  have ehq2 : Real.exp (-h / 2) * Real.exp (h / 2) ^ (2 : ℕ) =
      Real.exp (h / 2) := by
    calc
      Real.exp (-h / 2) * Real.exp (h / 2) ^ (2 : ℕ) =
          (Real.exp (h / 2) * Real.exp (-h / 2)) * Real.exp (h / 2) := by ring
      _ = _ := by rw [eh]; ring
  ring_nf at eh ehq2 ⊢
  rw [ehq2, eh]
  ring

theorem unitExponentialThirdDifferenceResponse_at_firstNode
    (a : ℝ) {h : ℝ} (hh : 0 ≤ h) :
    unitExponentialThirdDifferenceResponse a h (a + h) =
      Real.exp (h / 2) - Real.exp (-h / 2) := by
  rw [unitExponentialThirdDifferenceResponse_eq_first (by linarith) (le_refl _)]
  congr 1 <;> ring

theorem unitExponentialThirdDifferenceResponse_eq_gramPacket
    {a h u : ℝ} (ha : 0 ≤ a) (hh : 0 ≤ h) (hu : 0 ≤ u) :
    unitExponentialThirdDifferenceResponse a h u =
      -unitExponentialCoherentIncrementGram 0 (-a) (-u) +
        unitExponentialThirdDifferenceCoefficient h *
          unitExponentialCoherentIncrementGram 0 (-(a + h)) (-u) -
        unitExponentialThirdDifferenceCoefficient h *
          unitExponentialCoherentIncrementGram 0 (-(a + 2 * h)) (-u) +
        unitExponentialCoherentIncrementGram 0 (-(a + 3 * h)) (-u) := by
  rw [← unitExponentialIncrementKernel_eq_gram ha hu,
    ← unitExponentialIncrementKernel_eq_gram (by linarith : 0 ≤ a + h) hu,
    ← unitExponentialIncrementKernel_eq_gram (by linarith : 0 ≤ a + 2 * h) hu,
    ← unitExponentialIncrementKernel_eq_gram (by linarith : 0 ≤ a + 3 * h) hu]
  rfl

private theorem abs_exp_sub_exp_neg_le
    {h x : ℝ} (hh : 0 ≤ h) (hx0 : 0 ≤ x) (hxh : x ≤ h / 2) :
    |Real.exp x - Real.exp (-x)| ≤
      Real.exp (h / 2) - Real.exp (-h / 2) := by
  have hnonneg : 0 ≤ Real.exp x - Real.exp (-x) := by
    exact sub_nonneg.mpr (Real.exp_le_exp.mpr (by linarith))
  rw [abs_of_nonneg hnonneg]
  have hupper : Real.exp x ≤ Real.exp (h / 2) := Real.exp_le_exp.mpr hxh
  have hlower : Real.exp (-h / 2) ≤ Real.exp (-x) :=
    Real.exp_le_exp.mpr (by linarith)
  linarith

theorem unitExponentialThirdDifferenceSample_pos
    {h : ℝ} (hh : 0 < h) :
    0 < Real.exp (h / 2) - Real.exp (-h / 2) := by
  exact sub_pos.mpr (Real.exp_lt_exp.mpr (by linarith))

theorem abs_unitExponentialThirdDifferenceResponse_le
    {a h u : ℝ} (hh : 0 ≤ h) (hu0 : a ≤ u) (hu3 : u ≤ a + 3 * h) :
    |unitExponentialThirdDifferenceResponse a h u| ≤
      Real.exp (h / 2) - Real.exp (-h / 2) := by
  by_cases hu1 : u ≤ a + h
  · rw [unitExponentialThirdDifferenceResponse_eq_first hu0 hu1]
    convert abs_exp_sub_exp_neg_le (h := h) (x := (u - a) / 2)
      hh (by linarith) (by linarith) using 1 <;> ring
  by_cases hu2 : u ≤ a + 2 * h
  · have hfirst : a + h ≤ u := le_of_not_ge hu1
    rw [unitExponentialThirdDifferenceResponse_eq_middle hfirst hu2]
    have hqpos : 0 < 1 + Real.exp (h / 2) := by positivity
    have hE_le_one : Real.exp ((a + h - u) / 2) ≤ 1 := by
      rw [← Real.exp_zero]
      exact Real.exp_le_exp.mpr (by linarith)
    have hE_ge_r : Real.exp (-h / 2) ≤ Real.exp ((a + h - u) / 2) :=
      Real.exp_le_exp.mpr (by linarith)
    have hF_le_one : Real.exp ((u - a - 2 * h) / 2) ≤ 1 := by
      rw [← Real.exp_zero]
      exact Real.exp_le_exp.mpr (by linarith)
    have hF_ge_r : Real.exp (-h / 2) ≤ Real.exp ((u - a - 2 * h) / 2) :=
      Real.exp_le_exp.mpr (by linarith)
    have hupper : (1 + Real.exp (h / 2)) *
          (Real.exp ((a + h - u) / 2) - Real.exp ((u - a - 2 * h) / 2)) ≤
        (1 + Real.exp (h / 2)) * (1 - Real.exp (-h / 2)) :=
      mul_le_mul_of_nonneg_left (sub_le_sub hE_le_one hF_ge_r) hqpos.le
    have hlower : (1 + Real.exp (h / 2)) *
          (Real.exp (-h / 2) - 1) ≤
        (1 + Real.exp (h / 2)) *
          (Real.exp ((a + h - u) / 2) - Real.exp ((u - a - 2 * h) / 2)) :=
      mul_le_mul_of_nonneg_left (sub_le_sub hE_ge_r hF_le_one) hqpos.le
    have eh := exp_half_mul_exp_neg_half h
    have hright : (1 + Real.exp (h / 2)) * (1 - Real.exp (-h / 2)) =
        Real.exp (h / 2) - Real.exp (-h / 2) := by
      nlinarith
    rw [abs_le]
    constructor
    · rw [← hright]
      nlinarith
    · rwa [hright] at hupper
  · have hlast : a + 2 * h ≤ u := le_of_not_ge hu2
    rw [unitExponentialThirdDifferenceResponse_eq_last hlast hu3]
    rw [abs_sub_comm]
    convert abs_exp_sub_exp_neg_le (h := h) (x := (a + 3 * h - u) / 2)
      hh (by linarith) (by linarith) using 1 <;> ring

def unitExponentialThirdDifferencePolarEnergy (a h : ℝ) : ℝ :=
  ∫ u in Ioi (0 : ℝ), Real.exp (-u) *
    unitExponentialThirdDifferenceResponse a h u ^ (2 : ℕ)

theorem unitExponentialThirdDifferencePolarEnergy_eq_interval
    {a h : ℝ} (ha : 0 ≤ a) (hh : 0 ≤ h) :
    unitExponentialThirdDifferencePolarEnergy a h =
      ∫ u in a..(a + 3 * h), Real.exp (-u) *
        unitExponentialThirdDifferenceResponse a h u ^ (2 : ℕ) := by
  rw [unitExponentialThirdDifferencePolarEnergy]
  have hsub : Ioc a (a + 3 * h) ⊆ Ioi (0 : ℝ) := by
    intro u hu
    exact lt_of_le_of_lt ha hu.1
  rw [setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioi hsub]
  · rw [← intervalIntegral.integral_of_le (by linarith : a ≤ a + 3 * h)]
  · intro u hu
    simp only [mem_sdiff, mem_Ioi, mem_Ioc] at hu
    by_cases hua : u ≤ a
    · rw [unitExponentialThirdDifferenceResponse_eq_zero_of_le hh hua]
      ring
    · have hub : a + 3 * h ≤ u := by
        have hau : a < u := lt_of_not_ge hua
        exact le_of_not_gt (fun hub => hu.2 ⟨hau, le_of_lt hub⟩)
      rw [unitExponentialThirdDifferenceResponse_eq_zero_of_ge hh hub]
      ring

theorem unitExponentialThirdDifferencePolarEnergy_nonneg
    (a h : ℝ) :
    0 ≤ unitExponentialThirdDifferencePolarEnergy a h := by
  rw [unitExponentialThirdDifferencePolarEnergy]
  exact integral_nonneg_of_ae (Filter.Eventually.of_forall fun u => by positivity)

theorem unitExponentialThirdDifferencePolarEnergy_le
    {a h : ℝ} (ha : 0 ≤ a) (hh : 0 ≤ h) :
    unitExponentialThirdDifferencePolarEnergy a h ≤
      3 * h * (Real.exp (h / 2) - Real.exp (-h / 2)) ^ (2 : ℕ) := by
  rw [unitExponentialThirdDifferencePolarEnergy_eq_interval ha hh]
  let d := Real.exp (h / 2) - Real.exp (-h / 2)
  have hd : 0 ≤ d := sub_nonneg.mpr (Real.exp_le_exp.mpr (by linarith))
  have hbound : ∀ u ∈ Set.uIoc a (a + 3 * h),
      ‖Real.exp (-u) * unitExponentialThirdDifferenceResponse a h u ^ (2 : ℕ)‖ ≤ d ^ (2 : ℕ) := by
    intro u hu
    rw [Set.uIoc_of_le (by linarith : a ≤ a + 3 * h)] at hu
    have hu0 : 0 ≤ u := ha.trans hu.1.le
    have hexp : Real.exp (-u) ≤ 1 := by
      rw [← Real.exp_zero]
      exact Real.exp_le_exp.mpr (by linarith)
    have hr := abs_unitExponentialThirdDifferenceResponse_le hh hu.1.le hu.2
    have hrsq : unitExponentialThirdDifferenceResponse a h u ^ (2 : ℕ) ≤ d ^ (2 : ℕ) := by
      dsimp only [d] at hr ⊢
      nlinarith [sq_abs (unitExponentialThirdDifferenceResponse a h u),
        abs_nonneg (unitExponentialThirdDifferenceResponse a h u)]
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    nlinarith [Real.exp_pos (-u)]
  have hnorm := intervalIntegral.norm_integral_le_of_norm_le_const hbound
  have hnonneg : 0 ≤ ∫ u in a..(a + 3 * h), Real.exp (-u) *
      unitExponentialThirdDifferenceResponse a h u ^ (2 : ℕ) :=
    intervalIntegral.integral_nonneg (by linarith) (fun u _hu => by positivity)
  rw [Real.norm_eq_abs, abs_of_nonneg hnonneg] at hnorm
  dsimp only [d] at hnorm ⊢
  rw [abs_of_nonneg (by linarith : 0 ≤ a + 3 * h - a)] at hnorm
  nlinarith

/-- At the fixed lag `u = 1`, coherent point sampling beats every finite multiple of the bare
continuous polar-frame energy.  The witness is an actual four-column packet in the increment-Gram
span, localized to a window of width `3h` around that fixed lag. -/
theorem exists_unitExponentialThirdDifference_fixedSample_gt_polarEnergy
    (C : ℝ) (hC : 0 ≤ C) :
    ∃ h : ℝ, 0 < h ∧ 0 < 1 - h ∧
      C * unitExponentialThirdDifferencePolarEnergy (1 - h) h <
        unitExponentialThirdDifferenceResponse (1 - h) h 1 ^ (2 : ℕ) := by
  let h : ℝ := 1 / (6 * (C + 1))
  have hden : 0 < 6 * (C + 1) := by positivity
  have hh : 0 < h := by dsimp only [h]; positivity
  have hhlt : h < 1 := by
    dsimp only [h]
    rw [div_lt_iff₀ hden]
    nlinarith
  have ha : 0 ≤ 1 - h := by linarith
  let d := Real.exp (h / 2) - Real.exp (-h / 2)
  have hd : 0 < d := by
    dsimp only [d]
    exact unitExponentialThirdDifferenceSample_pos hh
  have hsample : unitExponentialThirdDifferenceResponse (1 - h) h 1 = d := by
    have hs := unitExponentialThirdDifferenceResponse_at_firstNode (1 - h) hh.le
    dsimp only [d]
    convert hs using 1 <;> ring
  have henergy := unitExponentialThirdDifferencePolarEnergy_le ha hh.le
  have hfactor : C * (3 * h) < 1 := by
    dsimp only [h]
    have hden2 : 0 < 2 * (C + 1) := by positivity
    rw [show C * (3 * (1 / (6 * (C + 1)))) = C / (2 * (C + 1)) by
      field_simp
      <;> ring]
    rw [div_lt_one hden2]
    linarith
  have hmul : C * unitExponentialThirdDifferencePolarEnergy (1 - h) h ≤
      C * (3 * h * d ^ (2 : ℕ)) := by
    apply mul_le_mul_of_nonneg_left _ hC
    simpa only [d] using henergy
  refine ⟨h, hh, by linarith, ?_⟩
  rw [hsample]
  have hd2 : 0 < d ^ (2 : ℕ) := sq_pos_of_pos hd
  calc
    C * unitExponentialThirdDifferencePolarEnergy (1 - h) h ≤
        C * (3 * h * d ^ (2 : ℕ)) := hmul
    _ = (C * (3 * h)) * d ^ (2 : ℕ) := by ring
    _ < d ^ (2 : ℕ) := (mul_lt_iff_lt_one_left hd2).2 hfactor

/-- No finite Loewner constant can dominate the fixed lag-one coherent projector by the bare
continuous polar frame, even after restricting to finite source-span packets. -/
theorem no_unitExponentialCoherent_fixedSample_polarDomination :
    ¬ ∃ C : ℝ, ∀ a h : ℝ, 0 ≤ a → 0 < h → a + h = 1 →
      unitExponentialThirdDifferenceResponse a h 1 ^ (2 : ℕ) ≤
        C * unitExponentialThirdDifferencePolarEnergy a h := by
  rintro ⟨C, hdom⟩
  let D := max C 0
  have hD : 0 ≤ D := le_max_right C 0
  obtain ⟨h, hh, ha, hwitness⟩ :=
    exists_unitExponentialThirdDifference_fixedSample_gt_polarEnergy D hD
  have hbase := hdom (1 - h) h ha.le hh (by ring)
  have hCD : C ≤ D := le_max_left C 0
  have henergy := unitExponentialThirdDifferencePolarEnergy_nonneg (1 - h) h
  have hscale : C * unitExponentialThirdDifferencePolarEnergy (1 - h) h ≤
      D * unitExponentialThirdDifferencePolarEnergy (1 - h) h :=
    mul_le_mul_of_nonneg_right hCD henergy
  exact (not_lt_of_ge (hbase.trans hscale)) hwitness

theorem unitExponentialThirdDifferenceResponse_at_leftNode
    (a : ℝ) {h : ℝ} (hh : 0 ≤ h) :
    unitExponentialThirdDifferenceResponse a h a = 0 :=
  unitExponentialThirdDifferenceResponse_eq_zero_of_le hh (le_refl _)

theorem unitExponentialThirdDifferenceResponse_at_secondNode
    (a : ℝ) {h : ℝ} (hh : 0 ≤ h) :
    unitExponentialThirdDifferenceResponse a h (a + 2 * h) =
      -(Real.exp (h / 2) - Real.exp (-h / 2)) := by
  rw [unitExponentialThirdDifferenceResponse_eq_middle (by linarith) (le_refl _)]
  have he1 : Real.exp ((a + h - (a + 2 * h)) / 2) = Real.exp (-h / 2) := by
    congr 1
    ring
  have he2 : Real.exp ((a + 2 * h - a - 2 * h) / 2) = 1 := by
    convert Real.exp_zero using 1
    ring
  rw [he1, he2]
  have eh := exp_half_mul_exp_neg_half h
  nlinarith

theorem unitExponentialThirdDifferenceResponse_at_rightNode
    (a : ℝ) {h : ℝ} (hh : 0 ≤ h) :
    unitExponentialThirdDifferenceResponse a h (a + 3 * h) = 0 :=
  unitExponentialThirdDifferenceResponse_eq_zero_of_ge hh (le_refl _)

/-- Coherent source-Gram norm of the four-column third-difference packet.  Since the response is
`Kc`, this is the quadratic form `cᵀ K c`, written without introducing a finite-index wrapper. -/
def unitExponentialThirdDifferenceSourceGram (a h : ℝ) : ℝ :=
  -unitExponentialThirdDifferenceResponse a h a +
    unitExponentialThirdDifferenceCoefficient h *
      unitExponentialThirdDifferenceResponse a h (a + h) -
    unitExponentialThirdDifferenceCoefficient h *
      unitExponentialThirdDifferenceResponse a h (a + 2 * h) +
    unitExponentialThirdDifferenceResponse a h (a + 3 * h)

theorem unitExponentialThirdDifferenceSourceGram_eq
    (a : ℝ) {h : ℝ} (hh : 0 ≤ h) :
    unitExponentialThirdDifferenceSourceGram a h =
      2 * unitExponentialThirdDifferenceCoefficient h *
        (Real.exp (h / 2) - Real.exp (-h / 2)) := by
  rw [unitExponentialThirdDifferenceSourceGram,
    unitExponentialThirdDifferenceResponse_at_leftNode a hh,
    unitExponentialThirdDifferenceResponse_at_firstNode a hh,
    unitExponentialThirdDifferenceResponse_at_secondNode a hh,
    unitExponentialThirdDifferenceResponse_at_rightNode a hh]
  ring

theorem unitExponentialThirdDifferenceSourceGram_pos
    (a : ℝ) {h : ℝ} (hh : 0 < h) :
    0 < unitExponentialThirdDifferenceSourceGram a h := by
  rw [unitExponentialThirdDifferenceSourceGram_eq a hh.le]
  have hcoeff : 0 < unitExponentialThirdDifferenceCoefficient h := by
    simp only [unitExponentialThirdDifferenceCoefficient]
    positivity
  exact mul_pos (mul_pos (by norm_num) hcoeff)
    (unitExponentialThirdDifferenceSample_pos hh)

/-- Exact anti-concentration supplied by the source Gram norm.  The bare polar average loses this
channel, whereas the source norm recovers the fixed sample with the sharp four-packet factor. -/
theorem unitExponentialThirdDifference_fixedSample_eq_sourceGram
    {h : ℝ} (hh : 0 < h) :
    unitExponentialThirdDifferenceResponse (1 - h) h 1 ^ (2 : ℕ) =
      ((Real.exp (h / 2) - Real.exp (-h / 2)) /
        (2 * unitExponentialThirdDifferenceCoefficient h)) *
          unitExponentialThirdDifferenceSourceGram (1 - h) h := by
  have hs := unitExponentialThirdDifferenceResponse_at_firstNode (1 - h) hh.le
  have hpoint : unitExponentialThirdDifferenceResponse (1 - h) h 1 =
      Real.exp (h / 2) - Real.exp (-h / 2) := by
    convert hs using 1 <;> ring
  rw [hpoint, unitExponentialThirdDifferenceSourceGram_eq (1 - h) hh.le]
  have hcoeff : unitExponentialThirdDifferenceCoefficient h ≠ 0 := by
    simp only [unitExponentialThirdDifferenceCoefficient]
    positivity
  field_simp

private theorem integral_exp_forward (a h : ℝ) :
    (∫ u in a..(a + h), Real.exp (u - a)) = Real.exp h - 1 := by
  have hderiv : ∀ u : ℝ,
      HasDerivAt (fun v : ℝ => Real.exp (v - a)) (Real.exp (u - a)) u := by
    intro u
    simpa using ((hasDerivAt_id u).sub_const a).exp
  have hint : IntervalIntegrable (fun u : ℝ => Real.exp (u - a)) volume a (a + h) :=
    (Real.continuous_exp.comp (continuous_id.sub continuous_const)).intervalIntegrable a (a + h)
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun u _hu => hderiv u) hint]
  rw [show a + h - a = h by ring, show a - a = 0 by ring, Real.exp_zero]

private theorem integral_exp_backward (a h : ℝ) :
    (∫ u in a..(a + h), Real.exp (a - u)) = 1 - Real.exp (-h) := by
  have hderiv : ∀ u : ℝ,
      HasDerivAt (fun v : ℝ => -Real.exp (a - v)) (Real.exp (a - u)) u := by
    intro u
    have hi : HasDerivAt (fun v : ℝ => a - v) (-1) u := by
      simpa using! ((hasDerivAt_const u a).sub (hasDerivAt_id u))
    simpa using! hi.exp.neg
  have hint : IntervalIntegrable (fun u : ℝ => Real.exp (a - u)) volume a (a + h) :=
    (Real.continuous_exp.comp (continuous_const.sub continuous_id)).intervalIntegrable a (a + h)
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun u _hu => hderiv u) hint]
  rw [show a - (a + h) = -h by ring, show a - a = 0 by ring, Real.exp_zero]
  ring

def unitExponentialThirdDifferenceFirstGenerator (a u : ℝ) : ℝ :=
  (Real.exp ((u - a) / 2) + Real.exp (-(u - a) / 2)) / 2

def unitExponentialThirdDifferenceMiddleGenerator (a h u : ℝ) : ℝ :=
  -(1 + Real.exp (h / 2)) *
    (Real.exp ((a + h - u) / 2) +
      Real.exp ((u - a - 2 * h) / 2)) / 2

def unitExponentialThirdDifferenceLastGenerator (a h u : ℝ) : ℝ :=
  (Real.exp ((u - a - 3 * h) / 2) +
    Real.exp ((a + 3 * h - u) / 2)) / 2

theorem hasDerivAt_unitExponentialThirdDifferenceResponse_first
    {a h u : ℝ} (hu0 : a < u) (hu1 : u < a + h) :
    HasDerivAt (unitExponentialThirdDifferenceResponse a h)
      (unitExponentialThirdDifferenceFirstGenerator a u) u := by
  have heq : ∀ v ∈ Ioo a (a + h),
      unitExponentialThirdDifferenceResponse a h v =
        Real.exp ((v - a) / 2) - Real.exp (-(v - a) / 2) := by
    intro v hv
    exact unitExponentialThirdDifferenceResponse_eq_first hv.1.le hv.2.le
  have hp : HasDerivAt (fun v : ℝ => (v - a) / 2) (1 / 2) u := by
    simpa using! (((hasDerivAt_id u).sub_const a).div_const 2)
  have hn : HasDerivAt (fun v : ℝ => -(v - a) / 2) (-1 / 2) u := by
    simpa using! (((((hasDerivAt_id u).sub_const a).neg).div_const 2))
  have hbase : HasDerivAt
      (fun v : ℝ => Real.exp ((v - a) / 2) - Real.exp (-(v - a) / 2))
      (unitExponentialThirdDifferenceFirstGenerator a u) u := by
    have hdeq : Real.exp ((u - a) / 2) * (1 / 2) -
        Real.exp (-(u - a) / 2) * (-1 / 2) =
          unitExponentialThirdDifferenceFirstGenerator a u := by
      simp only [unitExponentialThirdDifferenceFirstGenerator]
      ring
    simpa using! (hp.exp.sub hn.exp).congr_deriv hdeq
  apply hbase.congr_of_eventuallyEq
  · filter_upwards [Ioo_mem_nhds hu0 hu1] with v hv
    exact heq v hv

theorem hasDerivAt_unitExponentialThirdDifferenceResponse_middle
    {a h u : ℝ} (hu1 : a + h < u) (hu2 : u < a + 2 * h) :
    HasDerivAt (unitExponentialThirdDifferenceResponse a h)
      (unitExponentialThirdDifferenceMiddleGenerator a h u) u := by
  have heq : ∀ v ∈ Ioo (a + h) (a + 2 * h),
      unitExponentialThirdDifferenceResponse a h v =
        (1 + Real.exp (h / 2)) *
          (Real.exp ((a + h - v) / 2) -
            Real.exp ((v - a - 2 * h) / 2)) := by
    intro v hv
    exact unitExponentialThirdDifferenceResponse_eq_middle hv.1.le hv.2.le
  have hleft : HasDerivAt (fun v : ℝ => (a + h - v) / 2) (-1 / 2) u := by
    simpa using! (((hasDerivAt_const u (a + h)).sub (hasDerivAt_id u)).div_const 2)
  have hright : HasDerivAt (fun v : ℝ => (v - a - 2 * h) / 2) (1 / 2) u := by
    simpa using! ((((hasDerivAt_id u).sub_const a).sub_const (2 * h)).div_const 2)
  have hbase : HasDerivAt
      (fun v : ℝ => (1 + Real.exp (h / 2)) *
        (Real.exp ((a + h - v) / 2) - Real.exp ((v - a - 2 * h) / 2)))
      (unitExponentialThirdDifferenceMiddleGenerator a h u) u := by
    have hdeq : (1 + Real.exp (h / 2)) *
        (Real.exp ((a + h - u) / 2) * (-1 / 2) -
          Real.exp ((u - a - 2 * h) / 2) * (1 / 2)) =
        unitExponentialThirdDifferenceMiddleGenerator a h u := by
      simp only [unitExponentialThirdDifferenceMiddleGenerator]
      ring
    simpa using! ((hleft.exp.sub hright.exp).const_mul
      (1 + Real.exp (h / 2))).congr_deriv hdeq
  apply hbase.congr_of_eventuallyEq
  · filter_upwards [Ioo_mem_nhds hu1 hu2] with v hv
    exact heq v hv

theorem hasDerivAt_unitExponentialThirdDifferenceResponse_last
    {a h u : ℝ} (hu2 : a + 2 * h < u) (hu3 : u < a + 3 * h) :
    HasDerivAt (unitExponentialThirdDifferenceResponse a h)
      (unitExponentialThirdDifferenceLastGenerator a h u) u := by
  have heq : ∀ v ∈ Ioo (a + 2 * h) (a + 3 * h),
      unitExponentialThirdDifferenceResponse a h v =
        Real.exp ((v - a - 3 * h) / 2) -
          Real.exp ((a + 3 * h - v) / 2) := by
    intro v hv
    exact unitExponentialThirdDifferenceResponse_eq_last hv.1.le hv.2.le
  have hleft : HasDerivAt (fun v : ℝ => (v - a - 3 * h) / 2) (1 / 2) u := by
    simpa using! ((((hasDerivAt_id u).sub_const a).sub_const (3 * h)).div_const 2)
  have hright : HasDerivAt (fun v : ℝ => (a + 3 * h - v) / 2) (-1 / 2) u := by
    simpa using! (((hasDerivAt_const u (a + 3 * h)).sub (hasDerivAt_id u)).div_const 2)
  have hbase : HasDerivAt
      (fun v : ℝ => Real.exp ((v - a - 3 * h) / 2) -
        Real.exp ((a + 3 * h - v) / 2))
      (unitExponentialThirdDifferenceLastGenerator a h u) u := by
    have hdeq : Real.exp ((u - a - 3 * h) / 2) * (1 / 2) -
        Real.exp ((a + 3 * h - u) / 2) * (-1 / 2) =
          unitExponentialThirdDifferenceLastGenerator a h u := by
      simp only [unitExponentialThirdDifferenceLastGenerator]
      ring
    simpa using! (hleft.exp.sub hright.exp).congr_deriv hdeq
  apply hbase.congr_of_eventuallyEq
  · filter_upwards [Ioo_mem_nhds hu2 hu3] with v hv
    exact heq v hv

theorem unitExponentialThirdDifference_first_graphDensity
    {a h u : ℝ} (hu0 : a ≤ u) (hu1 : u ≤ a + h) :
    4 * unitExponentialThirdDifferenceFirstGenerator a u ^ (2 : ℕ) +
        unitExponentialThirdDifferenceResponse a h u ^ (2 : ℕ) =
      2 * (Real.exp (u - a) + Real.exp (a - u)) := by
  rw [unitExponentialThirdDifferenceResponse_eq_first hu0 hu1]
  simp only [unitExponentialThirdDifferenceFirstGenerator]
  have ep : Real.exp ((u - a) / 2) ^ (2 : ℕ) = Real.exp (u - a) := by
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  have em : Real.exp (-(u - a) / 2) ^ (2 : ℕ) = Real.exp (a - u) := by
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  ring_nf at ep em ⊢
  rw [ep, em]

theorem unitExponentialThirdDifference_middle_graphDensity
    {a h u : ℝ} (hu1 : a + h ≤ u) (hu2 : u ≤ a + 2 * h) :
    4 * unitExponentialThirdDifferenceMiddleGenerator a h u ^ (2 : ℕ) +
        unitExponentialThirdDifferenceResponse a h u ^ (2 : ℕ) =
      2 * (1 + Real.exp (h / 2)) ^ (2 : ℕ) *
        (Real.exp (a + h - u) + Real.exp (u - a - 2 * h)) := by
  rw [unitExponentialThirdDifferenceResponse_eq_middle hu1 hu2]
  simp only [unitExponentialThirdDifferenceMiddleGenerator]
  have ep : Real.exp ((a + h - u) / 2) ^ (2 : ℕ) = Real.exp (a + h - u) := by
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  have em : Real.exp ((u - a - 2 * h) / 2) ^ (2 : ℕ) =
      Real.exp (u - a - 2 * h) := by
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  ring_nf at ep em ⊢
  rw [ep, em]
  ring

theorem unitExponentialThirdDifference_last_graphDensity
    {a h u : ℝ} (hu2 : a + 2 * h ≤ u) (hu3 : u ≤ a + 3 * h) :
    4 * unitExponentialThirdDifferenceLastGenerator a h u ^ (2 : ℕ) +
        unitExponentialThirdDifferenceResponse a h u ^ (2 : ℕ) =
      2 * (Real.exp (u - a - 3 * h) + Real.exp (a + 3 * h - u)) := by
  rw [unitExponentialThirdDifferenceResponse_eq_last hu2 hu3]
  simp only [unitExponentialThirdDifferenceLastGenerator]
  have ep : Real.exp ((u - a - 3 * h) / 2) ^ (2 : ℕ) =
      Real.exp (u - a - 3 * h) := by
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  have em : Real.exp ((a + 3 * h - u) / 2) ^ (2 : ℕ) =
      Real.exp (a + 3 * h - u) := by
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  ring_nf at ep em ⊢
  rw [ep, em]

/-- Piecewise weak-generator graph energy of the coherent packet.  Knots have measure zero; the
three displayed generators are the classical derivative on each open cell. -/
def unitExponentialThirdDifferenceGeneratorEnergy (a h : ℝ) : ℝ :=
  (∫ u in a..(a + h),
      4 * unitExponentialThirdDifferenceFirstGenerator a u ^ (2 : ℕ) +
        unitExponentialThirdDifferenceResponse a h u ^ (2 : ℕ)) +
  (∫ u in (a + h)..(a + 2 * h),
      4 * unitExponentialThirdDifferenceMiddleGenerator a h u ^ (2 : ℕ) +
        unitExponentialThirdDifferenceResponse a h u ^ (2 : ℕ)) +
  ∫ u in (a + 2 * h)..(a + 3 * h),
      4 * unitExponentialThirdDifferenceLastGenerator a h u ^ (2 : ℕ) +
        unitExponentialThirdDifferenceResponse a h u ^ (2 : ℕ)

theorem unitExponentialThirdDifferenceGeneratorEnergy_eq_sourceGram
    (a : ℝ) {h : ℝ} (hh : 0 ≤ h) :
    unitExponentialThirdDifferenceGeneratorEnergy a h =
      4 * unitExponentialThirdDifferenceSourceGram a h := by
  have hfirst : (∫ u in a..(a + h),
      4 * unitExponentialThirdDifferenceFirstGenerator a u ^ (2 : ℕ) +
        unitExponentialThirdDifferenceResponse a h u ^ (2 : ℕ)) =
      2 * (Real.exp h - Real.exp (-h)) := by
    have hcongr : ∀ u ∈ Set.uIcc a (a + h),
        4 * unitExponentialThirdDifferenceFirstGenerator a u ^ (2 : ℕ) +
            unitExponentialThirdDifferenceResponse a h u ^ (2 : ℕ) =
          2 * (Real.exp (u - a) + Real.exp (a - u)) := by
      intro u hu
      rw [Set.uIcc_of_le (by linarith : a ≤ a + h)] at hu
      exact unitExponentialThirdDifference_first_graphDensity hu.1 hu.2
    rw [intervalIntegral.integral_congr hcongr]
    have hIntF : IntervalIntegrable (fun u : ℝ => Real.exp (u - a)) volume a (a + h) :=
      (Real.continuous_exp.comp (continuous_id.sub continuous_const)).intervalIntegrable a (a + h)
    have hIntB : IntervalIntegrable (fun u : ℝ => Real.exp (a - u)) volume a (a + h) :=
      (Real.continuous_exp.comp (continuous_const.sub continuous_id)).intervalIntegrable a (a + h)
    rw [intervalIntegral.integral_const_mul,
      intervalIntegral.integral_add hIntF hIntB,
      integral_exp_forward, integral_exp_backward]
    ring
  have hmiddle : (∫ u in (a + h)..(a + 2 * h),
      4 * unitExponentialThirdDifferenceMiddleGenerator a h u ^ (2 : ℕ) +
        unitExponentialThirdDifferenceResponse a h u ^ (2 : ℕ)) =
      4 * (1 + Real.exp (h / 2)) ^ (2 : ℕ) * (1 - Real.exp (-h)) := by
    have hcongr : ∀ u ∈ Set.uIcc (a + h) (a + 2 * h),
        4 * unitExponentialThirdDifferenceMiddleGenerator a h u ^ (2 : ℕ) +
            unitExponentialThirdDifferenceResponse a h u ^ (2 : ℕ) =
          2 * (1 + Real.exp (h / 2)) ^ (2 : ℕ) *
            (Real.exp (a + h - u) + Real.exp (u - a - 2 * h)) := by
      intro u hu
      rw [Set.uIcc_of_le (by linarith : a + h ≤ a + 2 * h)] at hu
      exact unitExponentialThirdDifference_middle_graphDensity hu.1 hu.2
    rw [intervalIntegral.integral_congr hcongr]
    have hIntB : IntervalIntegrable (fun u : ℝ => Real.exp (a + h - u)) volume
        (a + h) (a + 2 * h) :=
      (Real.continuous_exp.comp (continuous_const.sub continuous_id)).intervalIntegrable
        (a + h) (a + 2 * h)
    have hIntF : IntervalIntegrable (fun u : ℝ => Real.exp (u - a - 2 * h)) volume
        (a + h) (a + 2 * h) :=
      (Real.continuous_exp.comp ((continuous_id.sub continuous_const).sub
        continuous_const)).intervalIntegrable (a + h) (a + 2 * h)
    rw [intervalIntegral.integral_const_mul,
      intervalIntegral.integral_add hIntB hIntF]
    have hb := integral_exp_backward (a + h) h
    have hf := integral_exp_forward (a + h) h
    have hbeq : (∫ u in (a + h)..(a + 2 * h), Real.exp (a + h - u)) =
        1 - Real.exp (-h) := by convert hb using 1 <;> ring
    have hfeq : (∫ u in (a + h)..(a + 2 * h), Real.exp (u - a - 2 * h)) =
        1 - Real.exp (-h) := by
      have hshift : ∀ u : ℝ, Real.exp (u - a - 2 * h) =
          Real.exp (u - (a + h)) * Real.exp (-h) := by
        intro u
        rw [← Real.exp_add]
        congr 1
        ring
      have hf' : (∫ u in (a + h)..(a + 2 * h), Real.exp (u - (a + h))) =
          Real.exp h - 1 := by convert hf using 1 <;> ring
      rw [intervalIntegral.integral_congr (fun u _hu => hshift u),
        intervalIntegral.integral_mul_const, hf']
      have eh := exp_half_mul_exp_neg_half h
      have ehfull : Real.exp h * Real.exp (-h) = 1 := by
        rw [← Real.exp_add]
        convert Real.exp_zero using 1
        ring
      nlinarith
    rw [hbeq, hfeq]
    ring
  have hlast : (∫ u in (a + 2 * h)..(a + 3 * h),
      4 * unitExponentialThirdDifferenceLastGenerator a h u ^ (2 : ℕ) +
        unitExponentialThirdDifferenceResponse a h u ^ (2 : ℕ)) =
      2 * (Real.exp h - Real.exp (-h)) := by
    have hcongr : ∀ u ∈ Set.uIcc (a + 2 * h) (a + 3 * h),
        4 * unitExponentialThirdDifferenceLastGenerator a h u ^ (2 : ℕ) +
            unitExponentialThirdDifferenceResponse a h u ^ (2 : ℕ) =
          2 * (Real.exp (u - a - 3 * h) + Real.exp (a + 3 * h - u)) := by
      intro u hu
      rw [Set.uIcc_of_le (by linarith : a + 2 * h ≤ a + 3 * h)] at hu
      exact unitExponentialThirdDifference_last_graphDensity hu.1 hu.2
    rw [intervalIntegral.integral_congr hcongr]
    have hIntF : IntervalIntegrable (fun u : ℝ => Real.exp (u - a - 3 * h)) volume
        (a + 2 * h) (a + 3 * h) :=
      (Real.continuous_exp.comp ((continuous_id.sub continuous_const).sub
        continuous_const)).intervalIntegrable (a + 2 * h) (a + 3 * h)
    have hIntB : IntervalIntegrable (fun u : ℝ => Real.exp (a + 3 * h - u)) volume
        (a + 2 * h) (a + 3 * h) :=
      (Real.continuous_exp.comp (continuous_const.sub continuous_id)).intervalIntegrable
        (a + 2 * h) (a + 3 * h)
    rw [intervalIntegral.integral_const_mul,
      intervalIntegral.integral_add hIntF hIntB]
    have hb := integral_exp_backward (a + 2 * h) h
    have hf := integral_exp_forward (a + 2 * h) h
    have h1 : (∫ u in (a + 2 * h)..(a + 3 * h), Real.exp (u - a - 3 * h)) =
        1 - Real.exp (-h) := by
      have hshift : ∀ u : ℝ, Real.exp (u - a - 3 * h) =
          Real.exp (u - (a + 2 * h)) * Real.exp (-h) := by
        intro u
        rw [← Real.exp_add]
        congr 1
        ring
      have hf' : (∫ u in (a + 2 * h)..(a + 3 * h),
          Real.exp (u - (a + 2 * h))) = Real.exp h - 1 := by
        convert hf using 1 <;> ring
      rw [intervalIntegral.integral_congr (fun u _hu => hshift u),
        intervalIntegral.integral_mul_const, hf']
      have ehfull : Real.exp h * Real.exp (-h) = 1 := by
        rw [← Real.exp_add]
        convert Real.exp_zero using 1
        ring
      nlinarith
    have h2 : (∫ u in (a + 2 * h)..(a + 3 * h), Real.exp (a + 3 * h - u)) =
        Real.exp h - 1 := by
      have hshift : ∀ u : ℝ, Real.exp (a + 3 * h - u) =
          Real.exp (a + 2 * h - u) * Real.exp h := by
        intro u
        rw [← Real.exp_add]
        congr 1
        ring
      rw [intervalIntegral.integral_congr (fun u _hu => hshift u),
        intervalIntegral.integral_mul_const]
      have hbeq : (∫ u in (a + 2 * h)..(a + 3 * h),
          Real.exp (a + 2 * h - u)) = 1 - Real.exp (-h) := by
        convert hb using 1 <;> ring
      rw [hbeq]
      have ehfull : Real.exp h * Real.exp (-h) = 1 := by
        rw [← Real.exp_add]
        convert Real.exp_zero using 1
        ring
      nlinarith
    rw [h1, h2]
    ring
  rw [unitExponentialThirdDifferenceGeneratorEnergy, hfirst, hmiddle, hlast,
    unitExponentialThirdDifferenceSourceGram_eq a hh]
  simp only [unitExponentialThirdDifferenceCoefficient]
  have eh := exp_half_mul_exp_neg_half h
  have hq2 : Real.exp (h / 2) ^ (2 : ℕ) = Real.exp h := by
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  have hr2 : Real.exp (-h / 2) ^ (2 : ℕ) = Real.exp (-h) := by
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  have hqr2 : Real.exp (h / 2) * Real.exp (-h / 2) ^ (2 : ℕ) =
      Real.exp (-h / 2) := by
    calc
      _ = (Real.exp (h / 2) * Real.exp (-h / 2)) * Real.exp (-h / 2) := by ring
      _ = _ := by rw [eh]; ring
  have hq2r2 : Real.exp (h / 2) ^ (2 : ℕ) * Real.exp (-h / 2) ^ (2 : ℕ) = 1 := by
    calc
      _ = (Real.exp (h / 2) * Real.exp (-h / 2)) ^ (2 : ℕ) := by ring
      _ = _ := by rw [eh]; norm_num
  rw [← hq2, ← hr2]
  ring_nf at hqr2 hq2r2 ⊢
  rw [hqr2, hq2r2]
  ring

end GaloisForLFunctions.RHTower
