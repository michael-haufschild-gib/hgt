import Mathlib

/-!
# The first Laguerre inequality does not force real zeros

For `0 < c < b`, the real even polynomial `p(t) = (t² + b²)(t² − c²)` has the non-real zeros `± i b`,
yet its first Laguerre expression is strictly positive at every real point:

`p'(t)² − p(t) p''(t) = 4t⁶ + 2B t⁴ + (2B² + 12D) t² + 2BD > 0`,   `B = b² − c²`, `D = b² c²`.

The mechanism is the exact pair law: the pair `± i b` contributes `−2/b²` at `t = 0`, and the two
real zeros `± c` contribute `2/c² > 2/b²`.  A companion real zero closer than the pair's offset
restores the inequality everywhere.  So the first Laguerre inequality at every real point is a
companion law for non-real zeros, not a real-rootedness certificate; only the full family of
Laguerre inequalities characterizes the Laguerre–Pólya class.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- The countermodel `(t² + b²)(t² − c²)`. -/
def laguerreCompanionPoly (b c t : ℝ) : ℝ := (t ^ 2 + b ^ 2) * (t ^ 2 - c ^ 2)

theorem hasDerivAt_laguerreCompanionPoly (b c t : ℝ) :
    HasDerivAt (laguerreCompanionPoly b c)
      (4 * t ^ 3 + 2 * (b ^ 2 - c ^ 2) * t) t := by
  have h := ((hasDerivAt_pow 2 t).add_const (b ^ 2)).mul ((hasDerivAt_pow 2 t).sub_const (c ^ 2))
  exact h.congr_deriv (by norm_num; ring)

theorem deriv_laguerreCompanionPoly (b c : ℝ) :
    deriv (laguerreCompanionPoly b c) = fun t => 4 * t ^ 3 + 2 * (b ^ 2 - c ^ 2) * t := by
  funext t
  exact (hasDerivAt_laguerreCompanionPoly b c t).deriv

theorem deriv_deriv_laguerreCompanionPoly (b c t : ℝ) :
    deriv (deriv (laguerreCompanionPoly b c)) t = 12 * t ^ 2 + 2 * (b ^ 2 - c ^ 2) := by
  rw [deriv_laguerreCompanionPoly]
  have h' : HasDerivAt (fun t => 4 * t ^ 3 + 2 * (b ^ 2 - c ^ 2) * t)
      (12 * t ^ 2 + 2 * (b ^ 2 - c ^ 2)) t := by
    have h := ((hasDerivAt_pow 3 t).const_mul 4).add
      ((hasDerivAt_id' t).const_mul (2 * (b ^ 2 - c ^ 2)))
    exact h.congr_deriv (by norm_num; ring)
  exact h'.deriv

/-- **The first Laguerre expression is strictly positive everywhere.** -/
theorem laguerre_laguerreCompanionPoly_pos {b c : ℝ} (hc : 0 < c) (hcb : c < b) (t : ℝ) :
    0 < deriv (laguerreCompanionPoly b c) t ^ 2 -
      laguerreCompanionPoly b c t * deriv (deriv (laguerreCompanionPoly b c)) t := by
  rw [deriv_deriv_laguerreCompanionPoly, deriv_laguerreCompanionPoly]
  unfold laguerreCompanionPoly
  set B := b ^ 2 - c ^ 2 with hB
  set D := b ^ 2 * c ^ 2 with hD
  have hBpos : 0 < B := by rw [hB]; nlinarith
  have hDpos : 0 < D := by rw [hD]; exact mul_pos (pow_pos (by linarith) 2) (pow_pos hc 2)
  have hid : (4 * t ^ 3 + 2 * B * t) ^ 2 - (t ^ 2 + b ^ 2) * (t ^ 2 - c ^ 2) *
      (12 * t ^ 2 + 2 * B) = 4 * t ^ 6 + 2 * B * t ^ 4 + (2 * B ^ 2 + 12 * D) * t ^ 2 +
        2 * B * D := by
    rw [hB, hD]
    ring
  rw [hid]
  have h6 : 0 ≤ t ^ 6 := by positivity
  have h4 : 0 ≤ t ^ 4 := by positivity
  have h2 : 0 ≤ t ^ 2 := by positivity
  nlinarith [mul_nonneg hBpos.le h4, mul_nonneg (by positivity : (0:ℝ) ≤ 2 * B ^ 2 + 12 * D) h2,
    mul_pos hBpos hDpos]

/-- The complexified countermodel vanishes at the non-real point `i b`. -/
theorem laguerreCompanionPoly_complex_root (b c : ℝ) :
    (((Complex.I * b) ^ 2 + (b : ℂ) ^ 2) * ((Complex.I * b) ^ 2 - (c : ℂ) ^ 2)) = 0 := by
  have : (Complex.I * b) ^ 2 + (b : ℂ) ^ 2 = 0 := by
    rw [mul_pow, Complex.I_sq]
    ring
  rw [this, zero_mul]

/-- **The first Laguerre inequality is not a real-rootedness certificate.**  There is a real even
polynomial of degree four whose first Laguerre expression is positive at every real point but which
has a non-real zero. -/
theorem exists_laguerre_pos_with_nonreal_zero :
    ∃ p : ℝ → ℝ, ∃ q : ℂ → ℂ, (∀ t : ℝ, (q t) = p t) ∧ (∃ z : ℂ, z.im ≠ 0 ∧ q z = 0) ∧
      ∀ t : ℝ, 0 < deriv p t ^ 2 - p t * deriv (deriv p) t := by
  refine ⟨laguerreCompanionPoly 2 1, fun z => (z ^ 2 + (2 : ℂ) ^ 2) * (z ^ 2 - (1 : ℂ) ^ 2),
    fun t => ?_, ⟨Complex.I * 2, by simp, ?_⟩, fun t => laguerre_laguerreCompanionPoly_pos
      (by norm_num) (by norm_num) t⟩
  · unfold laguerreCompanionPoly
    push_cast
    ring
  · have := laguerreCompanionPoly_complex_root 2 1
    push_cast at this
    exact this

end

end GaloisForLFunctions.HTGeometry
