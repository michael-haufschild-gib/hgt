import GaloisForLFunctions.HTGeometry.SecondDerivativeDeviationSeries
import GaloisForLFunctions.HTGeometry.MaximumTermWindowMoments

/-!
# The order-two Wiman--Valiron estimate at a window

At a maximum-modulus point of the circle, `z² f″/f` is within `(2ν+1)` times the order-one defect
plus the normalised second moment of `ν(ν−1)`.  Both ingredients are already proved: the second
moment is `MaximumTermProfileMoments.tsum_index_sq_le_gaussian`, and the window mass it consumes is
`MaximumTermWindowMoments.sum_window_le_sqrt_card_mul_bound`.

The statement takes the order-one defect as an abstract bound, so it composes with any of the
corpus's Wiman--Valiron selections.
-/

namespace GaloisForLFunctions.HTGeometry

open Filter

variable {a : ℕ → ℂ}

/-- The window carries at most `sqrt (2N+1)` times the value. -/
theorem window_mass_le_sqrt (ha : EntireCoeffs a) {x : ℝ} (N : ℕ)
    {z : ℂ} (_hz : ‖z‖ = Real.exp x)
    (hmax : ∀ θ : ℝ, ‖coeffFun a (circleMap 0 (Real.exp x) θ)‖ ≤ ‖coeffFun a z‖) :
    ∑ n ∈ Finset.Ico (centralIndex a (Real.exp x) - N)
        (centralIndex a (Real.exp x) + N + 1), ‖a n‖ * Real.exp x ^ n
      ≤ Real.sqrt (2 * (N : ℝ) + 1) * ‖coeffFun a z‖ := by
  classical
  set r : ℝ := Real.exp x with hr
  set v : ℕ := centralIndex a r with hv
  have hcard : ((Finset.Ico (v - N) (v + N + 1)).card : ℝ) ≤ 2 * (N : ℝ) + 1 := by
    rw [Nat.card_Ico]
    have : v + N + 1 - (v - N) ≤ 2 * N + 1 := by omega
    calc ((v + N + 1 - (v - N) : ℕ) : ℝ) ≤ ((2 * N + 1 : ℕ) : ℝ) := by exact_mod_cast this
      _ = 2 * (N : ℝ) + 1 := by push_cast; ring
  refine le_trans (sum_window_le_sqrt_card_mul_bound ha (Real.exp_pos x).le (norm_nonneg _)
    hmax _) ?_
  exact mul_le_mul_of_nonneg_right
    (Real.sqrt_le_sqrt hcard) (norm_nonneg _)

/-- **The order-two Wiman--Valiron estimate.**  Given any bound `E` for the order-one defect at a
maximum-modulus point, the order-two defect is at most `(2ν+1)·E` plus the normalised second
moment. -/
theorem norm_mul_sq_deriv2_div_sub_le
    (ha : EntireCoeffs a) {n₀ : ℕ} (hn₀ : a n₀ ≠ 0) {x H L v₀ : ℝ} (hH : 0 < H) (hL : 0 < L)
    {N : ℕ} (hN0 : 0 < N) (hNK : (N : ℝ) ≤ 2 * L * H) (hNv : 2 * L * v₀ ≤ (N : ℝ))
    (hlipA : ∀ v : ℝ, v₀ ≤ v → v ≤ H →
      (centralIndex a (Real.exp (x + v)) : ℝ) ≤ (centralIndex a (Real.exp x) : ℝ) + L * v)
    (hlipB : ∀ v : ℝ, v₀ ≤ v → v ≤ H →
      (centralIndex a (Real.exp x) : ℝ) - L * v ≤ (centralIndex a (Real.exp (x - v)) : ℝ))
    {z : ℂ} (hz : ‖z‖ = Real.exp x)
    (hfz : maxTerm a (Real.exp x) ≤ ‖coeffFun a z‖)
    (hmax : ∀ θ : ℝ, ‖coeffFun a (circleMap 0 (Real.exp x) θ)‖ ≤ ‖coeffFun a z‖)
    {G₂ : ℝ}
    (hG₂ : ∑' j : ℕ, ((N : ℝ) + 1 + j) ^ (2 : ℕ)
        * Real.exp (-((N : ℝ) / (4 * L))) ^ (N + 1 + j) ≤ G₂)
    {E : ℝ}
    (hE : ‖z * deriv (coeffFun a) z / coeffFun a z
        - (centralIndex a (Real.exp x) : ℂ)‖ ≤ E) :
    ‖z ^ (2 : ℕ) * deriv (deriv (coeffFun a)) z / coeffFun a z
        - ((centralIndex a (Real.exp x) : ℂ) * ((centralIndex a (Real.exp x) : ℂ) - 1))‖
      ≤ ((N : ℝ) ^ (2 : ℕ) * Real.sqrt (2 * (N : ℝ) + 1) + 2 * G₂)
        + (2 * (centralIndex a (Real.exp x) : ℝ) + 1) * E := by
  classical
  set r : ℝ := Real.exp x with hr
  have hrpos : (0 : ℝ) < r := Real.exp_pos x
  set v : ℕ := centralIndex a r with hv
  obtain ⟨-, -, hμpos⟩ := exists_maxTerm_eq ha hrpos hn₀
  have hfpos : 0 < ‖coeffFun a z‖ := lt_of_lt_of_le hμpos hfz
  have hfne : coeffFun a z ≠ 0 := norm_pos_iff.mp hfpos
  have hzn : 0 < ‖z‖ := by rw [hz]; exact hrpos
  -- the second moment against the value
  have hW := window_mass_le_sqrt ha N hz hmax
  have hM2 := tsum_index_sq_le_gaussian ha hn₀ hH hL hN0 hNK hNv hlipA hlipB hW
  have hM2' : ∑' n : ℕ, ((n : ℝ) - (v : ℝ)) ^ (2 : ℕ) * (‖a n‖ * r ^ n)
      ≤ ((N : ℝ) ^ (2 : ℕ) * Real.sqrt (2 * (N : ℝ) + 1) + 2 * G₂) * ‖coeffFun a z‖ := by
    refine le_trans hM2 ?_
    have h1 : (N : ℝ) ^ (2 : ℕ) * (Real.sqrt (2 * (N : ℝ) + 1) * ‖coeffFun a z‖)
        ≤ (N : ℝ) ^ (2 : ℕ) * Real.sqrt (2 * (N : ℝ) + 1) * ‖coeffFun a z‖ := by ring_nf; rfl
    have h2 : 2 * maxTerm a r * (∑' j : ℕ, ((N : ℝ) + 1 + j) ^ (2 : ℕ)
          * Real.exp (-((N : ℝ) / (4 * L))) ^ (N + 1 + j))
        ≤ 2 * G₂ * ‖coeffFun a z‖ := by
      have hμle : maxTerm a r ≤ ‖coeffFun a z‖ := hfz
      have hGnn : (0 : ℝ) ≤ ∑' j : ℕ, ((N : ℝ) + 1 + j) ^ (2 : ℕ)
          * Real.exp (-((N : ℝ) / (4 * L))) ^ (N + 1 + j) := by
        refine tsum_nonneg fun j => ?_
        positivity
      nlinarith [hμpos, hGnn, hG₂, hμle]
    nlinarith [h1, h2, norm_nonneg (coeffFun a z)]
  -- the order-one defect against the value
  have hE' : ‖z * deriv (coeffFun a) z - (v : ℂ) * coeffFun a z‖ ≤ E * ‖coeffFun a z‖ := by
    have hsplit : z * deriv (coeffFun a) z / coeffFun a z - (v : ℂ)
        = (z * deriv (coeffFun a) z - (v : ℂ) * coeffFun a z) / coeffFun a z := by
      field_simp
    rw [hsplit, norm_div, div_le_iff₀ hfpos] at hE
    exact hE
  -- combine
  have hdev := norm_mul_sq_deriv2_sub_le ha hzn v
  have hsplit2 : z ^ (2 : ℕ) * deriv (deriv (coeffFun a)) z / coeffFun a z
        - ((v : ℂ) * ((v : ℂ) - 1))
      = (z ^ (2 : ℕ) * deriv (deriv (coeffFun a)) z - ((v : ℂ) * ((v : ℂ) - 1)) * coeffFun a z)
          / coeffFun a z := by
    field_simp
  rw [hz] at hdev
  rw [hsplit2, norm_div, div_le_iff₀ hfpos]
  have hνnn : (0 : ℝ) ≤ 2 * (v : ℝ) + 1 := by positivity
  have h3 : (2 * (v : ℝ) + 1) * ‖z * deriv (coeffFun a) z - (v : ℂ) * coeffFun a z‖
      ≤ (2 * (v : ℝ) + 1) * (E * ‖coeffFun a z‖) :=
    mul_le_mul_of_nonneg_left hE' hνnn
  calc ‖z ^ (2 : ℕ) * deriv (deriv (coeffFun a)) z - (v : ℂ) * ((v : ℂ) - 1) * coeffFun a z‖
      ≤ (∑' n : ℕ, ((n : ℝ) - (v : ℝ)) ^ (2 : ℕ) * (‖a n‖ * r ^ n))
        + (2 * (v : ℝ) + 1) * ‖z * deriv (coeffFun a) z - (v : ℂ) * coeffFun a z‖ := hdev
    _ ≤ ((N : ℝ) ^ (2 : ℕ) * Real.sqrt (2 * (N : ℝ) + 1) + 2 * G₂) * ‖coeffFun a z‖
        + (2 * (v : ℝ) + 1) * (E * ‖coeffFun a z‖) := by linarith [hM2', h3]
    _ = (((N : ℝ) ^ (2 : ℕ) * Real.sqrt (2 * (N : ℝ) + 1) + 2 * G₂)
        + (2 * (v : ℝ) + 1) * E) * ‖coeffFun a z‖ := by ring

end GaloisForLFunctions.HTGeometry
