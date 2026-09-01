import GaloisForLFunctions.RHTower.EntireDirichletPolynomial
import GaloisForLFunctions.HTGeometry.UniformZeroCountBound

/-!
# The analytic real trace of a finite Dirichlet polynomial

Backlund's estimate for the argument variation of a function along a horizontal segment counts the
sign changes of its real part.  For a function with real Dirichlet coefficients the real trace
`σ ↦ Re Ψ(σ + iT)` extends to the entire function `(Ψ(z+iT) + Ψ(z−iT))/2`, by Schwarz symmetry, and
Jensen's inequality bounds its zeros in a disc by the logarithm of the ratio of a sphere bound to
the value at the centre.

For a Dirichlet polynomial both bounds are explicit: the sphere bound is the `ℓ¹` mass weighted by
`n^{-x}` at the leftmost real part `x` of the sphere, and the centre value is bounded below by head
dominance.  The resulting count is `O(log(length))`, which is `O(log T)` at mollifier length `T^θ`.
-/

open Complex Metric Set MeromorphicOn
open GaloisForLFunctions.HTGeometry

noncomputable section

namespace RHTower

/-- Schwarz symmetry for a Dirichlet polynomial with self-conjugate coefficients. -/
theorem edPoly_conj (a : ℕ → ℂ) {s : Finset ℕ} (hs : ∀ n ∈ s, 1 ≤ n)
    (hreal : ∀ n ∈ s, (starRingEnd ℂ) (a n) = a n) (z : ℂ) :
    edPoly a s ((starRingEnd ℂ) z) = (starRingEnd ℂ) (edPoly a s z) := by
  unfold edPoly
  rw [map_sum]
  refine Finset.sum_congr rfl fun n hn => ?_
  have hpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hs n hn
  have hne : (((n : ℝ) : ℂ)) ≠ 0 := Complex.ofReal_ne_zero.2 (ne_of_gt hpos)
  have hlog : Complex.log ((n : ℝ) : ℂ) = ((Real.log n : ℝ) : ℂ) :=
    (Complex.ofReal_log hpos.le).symm
  rw [map_mul, hreal n hn, Complex.cpow_def_of_ne_zero hne,
    Complex.cpow_def_of_ne_zero hne, hlog, ← Complex.exp_conj]
  congr 2
  rw [map_mul, Complex.conj_ofReal, map_neg]

/-- The analytic real trace of a Dirichlet polynomial at height `T`. -/
def edPolyTrace (a : ℕ → ℂ) (s : Finset ℕ) (T : ℝ) (z : ℂ) : ℂ :=
  (edPoly a s (z + (T : ℂ) * I) + edPoly a s (z - (T : ℂ) * I)) / 2

theorem differentiable_edPolyTrace (a : ℕ → ℂ) {s : Finset ℕ} (hs : ∀ n ∈ s, 1 ≤ n) (T : ℝ) :
    Differentiable ℂ (edPolyTrace a s T) := by
  have hd := differentiable_edPoly a hs
  exact fun z => (((hd _).comp z (differentiableAt_id.add_const _)).add
    ((hd _).comp z (differentiableAt_id.sub_const _))).div_const 2

theorem analyticOnNhd_edPolyTrace (a : ℕ → ℂ) {s : Finset ℕ} (hs : ∀ n ∈ s, 1 ≤ n) (T : ℝ)
    (K : Set ℂ) : AnalyticOnNhd ℂ (edPolyTrace a s T) K :=
  fun z _ => (analyticOnNhd_univ_iff_differentiable.mpr
    (differentiable_edPolyTrace a hs T)) z (Set.mem_univ z)

/-- On the real axis the trace is the real part of the polynomial on the line of height `T`. -/
theorem edPolyTrace_ofReal (a : ℕ → ℂ) {s : Finset ℕ} (hs : ∀ n ∈ s, 1 ≤ n)
    (hreal : ∀ n ∈ s, (starRingEnd ℂ) (a n) = a n) (T x : ℝ) :
    edPolyTrace a s T (x : ℂ) = (((edPoly a s ((x : ℂ) + (T : ℂ) * I)).re : ℝ) : ℂ) := by
  have hconj : ((x : ℂ) - (T : ℂ) * I) = (starRingEnd ℂ) ((x : ℂ) + (T : ℂ) * I) := by
    simp [Complex.ext_iff]
  rw [edPolyTrace, hconj, edPoly_conj a hs hreal, Complex.add_conj]
  push_cast
  ring

/-- A uniform bound on any half-plane `Re z ≥ x`, valid for the trace since both shifted points
have the same real part. -/
theorem norm_edPolyTrace_le_of_re_ge (a : ℕ → ℂ) {s : Finset ℕ} (hs : ∀ n ∈ s, 1 ≤ n)
    (T : ℝ) {x : ℝ} {z : ℂ} (hz : x ≤ z.re) :
    ‖edPolyTrace a s T z‖ ≤ ∑ n ∈ s, ‖a n‖ * ((n : ℝ) ^ (-x)) := by
  have hkey : ∀ w : ℂ, w.re = z.re →
      ‖edPoly a s w‖ ≤ ∑ n ∈ s, ‖a n‖ * ((n : ℝ) ^ (-x)) := by
    intro w hw
    refine (norm_edPoly_le a hs w).trans (Finset.sum_le_sum fun n hn => ?_)
    have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hs n hn
    have hmono : ((n : ℝ) ^ (-w.re)) ≤ ((n : ℝ) ^ (-x)) := by
      refine Real.rpow_le_rpow_of_exponent_le hn1 ?_
      rw [hw]; linarith
    exact mul_le_mul_of_nonneg_left hmono (norm_nonneg _)
  have h1 : ‖edPoly a s (z + (T : ℂ) * I)‖ ≤ ∑ n ∈ s, ‖a n‖ * ((n : ℝ) ^ (-x)) :=
    hkey _ (by simp)
  have h2 : ‖edPoly a s (z - (T : ℂ) * I)‖ ≤ ∑ n ∈ s, ‖a n‖ * ((n : ℝ) ^ (-x)) :=
    hkey _ (by simp)
  rw [edPolyTrace, norm_div, show ‖(2 : ℂ)‖ = 2 by norm_num]
  have := norm_add_le (edPoly a s (z + (T : ℂ) * I)) (edPoly a s (z - (T : ℂ) * I))
  linarith [this, h1, h2]

/-- **Head dominance for the real part.**  If the coefficient at `n = 1` is a positive real and
dominates the rest of the polynomial on the line `Re z = x`, then the real part of the polynomial
is bounded below there. -/
theorem re_edPoly_ge (a : ℕ → ℂ) {s : Finset ℕ} (hs : ∀ n ∈ s, 1 ≤ n) (h1 : 1 ∈ s) (z : ℂ) :
    (a 1).re - (∑ n ∈ s.erase 1, ‖a n‖ * ((n : ℝ) ^ (-z.re))) ≤ (edPoly a s z).re := by
  classical
  have hsplit : edPoly a s z = a 1 + ∑ n ∈ s.erase 1, a n * ((n : ℝ) : ℂ) ^ (-z) := by
    unfold edPoly
    rw [← Finset.sum_erase_add _ _ h1]
    have hone : a 1 * (((1 : ℕ) : ℝ) : ℂ) ^ (-z) = a 1 := by norm_num
    rw [hone]
    ring
  have htail : ‖∑ n ∈ s.erase 1, a n * ((n : ℝ) : ℂ) ^ (-z)‖
      ≤ ∑ n ∈ s.erase 1, ‖a n‖ * ((n : ℝ) ^ (-z.re)) := by
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun n hn => ?_)
    have hpos : (0 : ℝ) < (n : ℝ) := by
      exact_mod_cast hs n (Finset.mem_of_mem_erase hn)
    rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hpos]
    simp
  have hre := Complex.abs_re_le_norm (∑ n ∈ s.erase 1, a n * ((n : ℝ) : ℂ) ^ (-z))
  rw [hsplit, Complex.add_re]
  have := abs_le.mp (le_trans hre htail)
  linarith [this.1]

/-- **Jensen's disc count for the trace.**  On the sphere of radius `8` about `4` the real part is
at least `−4`, so the `ℓ¹` mass weighted by `n^4` is a uniform bound there. -/
theorem edPolyTrace_count_le (a : ℕ → ℂ) {s : Finset ℕ} (hs : ∀ n ∈ s, 1 ≤ n) (T : ℝ)
    {r m Mb : ℝ} (hr : 0 < r) (hrlt : r < 8) (hm : 0 < m) (hM1 : 1 ≤ Mb)
    (hcentre : m ≤ ‖edPolyTrace a s T 4‖)
    (hmass : (∑ n ∈ s, ‖a n‖ * ((n : ℝ) ^ (4 : ℝ))) ≤ Mb) :
    ∑ᶠ u, MeromorphicOn.divisor (edPolyTrace a s T) (closedBall (4 : ℂ) |r|) u
      ≤ Real.log (Mb / m) / Real.log (8 / r) := by
  have hsphere : ∀ z ∈ sphere (4 : ℂ) |(8 : ℝ)|, ‖edPolyTrace a s T z‖ ≤ Mb := by
    intro z hz
    rw [mem_sphere_iff_norm, abs_of_pos (by norm_num : (0 : ℝ) < 8)] at hz
    have hre : (-4 : ℝ) ≤ z.re := by
      have h := Complex.abs_re_le_norm (z - 4)
      have hrz : (z - 4).re = z.re - 4 := by simp
      rw [hrz, hz] at h
      rw [abs_le] at h
      linarith [h.1]
    refine le_trans (norm_edPolyTrace_le_of_re_ge a hs T hre) (le_trans ?_ hmass)
    exact le_of_eq (Finset.sum_congr rfl fun n _ => by norm_num)
  have hbound := sum_divisor_le_of_bounds (c := (4 : ℂ)) (r := r) (R := (8 : ℝ))
    (M := Mb) (m := m) (f := edPolyTrace a s T)
    (by rwa [abs_of_pos hr]) (by rw [abs_of_pos hr, abs_of_pos (by norm_num : (0:ℝ) < 8)]; exact hrlt)
    hM1 hm (analyticOnNhd_edPolyTrace a hs T _) hcentre hsphere
  exact hbound

end RHTower

end
