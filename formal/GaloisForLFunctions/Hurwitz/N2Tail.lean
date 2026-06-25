/-
# Hurwitz N=2 — the corrected analytic tail (factored, cut-free)

The principal-`cpow` tail `∑_{m≠n} (m−n+x)^{−(s+k)}` is NOT analytic near `a=−n` (for `m<n` the base
crosses the branch cut `(-∞,0]` along `Im z = 0`). The branch points `x = n−m` all have `|n−m| ≥ 1`, so
on the unit disk `{|x|<1}` an analytic branch exists — the **factored** form

  `R_{n,k}(x) = ∑_{m≠n} (m−n)^{−(s+k)} · (1 + x/(m−n))^{−(s+k)}`,

whose second factor's base `1 + x/(m−n)` lies in the right half-plane (`|x/(m−n)| < 1`), so principal
`cpow` is analytic there. This is the genuine analytic continuation of the Hurwitz tail; it is what the
N=2 separation/`split_extend` continuation requires.
-/
import GaloisForLFunctions.Hurwitz.HurwitzZeta

open Complex

namespace HurwitzN2Tail

/-- The factored analytic Hurwitz tail near `a = −n`. -/
noncomputable def tailFactored (s : ℂ) (k n : ℕ) (x : ℂ) : ℂ :=
  ∑' m : ℕ, (if m = n then 0
    else ((m : ℂ) - (n : ℂ)) ^ (-(s + (k : ℂ))) * (1 + x / ((m : ℂ) - (n : ℂ))) ^ (-(s + (k : ℂ))))

/-- **The factored tail is `2πi`-periodic in `z`** (it is a function of `x = e^z`). Supplies the tail
periodicity inputs of the block eigenvector lemmas. -/
theorem tailFactored_periodic (s : ℂ) (k n : ℕ) (z : ℂ) :
    tailFactored s k n (Complex.exp (z + 2 * (Real.pi : ℂ) * Complex.I))
      = tailFactored s k n (Complex.exp z) := by
  rw [Complex.exp_add, Complex.exp_two_pi_mul_I, mul_one]

/-- Each term is the constant `(m−n)^{−(s+k)}` times an analytic factor whose base `1 + x/(m−n)` has
positive real part on the unit disk (`m ≠ n`, `|x| < 1` ⟹ `|x/(m−n)| < 1`), so principal `cpow` is
analytic — the per-term input to the locally-uniform-limit analyticity of the tail. -/
theorem tailTerm_base_re_pos {m n : ℕ} (hmn : m ≠ n) {x : ℂ} (hx : ‖x‖ < 1) :
    0 < (1 + x / ((m : ℂ) - (n : ℂ))).re := by
  set w := x / ((m : ℂ) - (n : ℂ)) with hw
  have hd1 : (1 : ℝ) ≤ ‖((m : ℂ) - (n : ℂ))‖ := by
    have hne : ((m : ℤ) - (n : ℤ)) ≠ 0 := fun h => hmn (by omega)
    have hcast : ((m : ℂ) - (n : ℂ)) = (((m : ℤ) - (n : ℤ) : ℤ) : ℂ) := by push_cast; ring
    rw [hcast, Complex.norm_intCast]
    exact_mod_cast Int.one_le_abs hne
  have hwlt : ‖w‖ < 1 := by
    rw [hw, norm_div]
    exact lt_of_le_of_lt (div_le_self (norm_nonneg x) hd1) hx
  have hre : -‖w‖ ≤ w.re := (abs_le.mp (Complex.abs_re_le_norm w)).1
  rw [Complex.add_re, Complex.one_re]
  linarith

end HurwitzN2Tail
