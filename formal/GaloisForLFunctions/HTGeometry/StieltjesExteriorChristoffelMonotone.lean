import GaloisForLFunctions.HTGeometry.ChristoffelKernel
import GaloisForLFunctions.HTGeometry.GaussNodeDenominator
import GaloisForLFunctions.HTGeometry.StieltjesMomentProblem

/-!
# Exterior Christoffel monotonicity for a Stieltjes bulk

For a positive moment form whose shifted functional `p ↦ L((X - a) p²)` is also nonnegative — the
Stieltjes condition, satisfied by any representing measure supported in `[a, ∞)` — every root of the
orthogonal polynomial `Pₙ₊₁` lies in `[a, ∞)`.  The proof is the pairing of `Pₙ₊₁` with the cofactor
of a root: `0 = L((X - a) g²) + (a - r) L(g²)` forces `a ≤ r`.

To the left of `a` every linear factor `x - rⱼ` therefore lengthens as `x` decreases, so
`Pₙ(x)²` is strictly decreasing there for `n ≥ 1`, and the Christoffel--Darboux diagonal
`K_d(x, x) = ∑_{k ≤ d} P_k(x)² / h_k` inherits the same monotonicity.  Its reciprocal, the
Christoffel function `λ_d(x)`, is therefore nondecreasing on `(-∞, a)`: the rank-one Schur threshold
grows as the boundary point moves toward the support.
-/

open scoped BigOperators
open MeasureTheory Polynomial

namespace HTGeometry

variable {s : ℕ → ℝ} {a : ℝ}

/-- **Stieltjes shift positivity at `a`.**  The moment functional is nonnegative on `(X - a) p²`.
For a representing measure this is exactly support in `[a, ∞)`. -/
def ShiftedPositiveAt (s : ℕ → ℝ) (a : ℝ) : Prop :=
  ∀ p : Polynomial ℝ, 0 ≤ momentFunctional s ((X - C a) * p ^ (2 : ℕ))

/-- A representing measure supported in `[a, ∞)` gives shift positivity at `a`. -/
theorem shiftedPositiveAt_of_measure {μ : Measure ℝ} (s : ℕ → ℝ) (a : ℝ)
    (hs : ∀ k, s k = ∫ x, (x : ℝ) ^ k ∂μ)
    (hint : ∀ k, Integrable (fun x : ℝ => (x : ℝ) ^ k) μ)
    (hμ : ∀ᵐ x ∂μ, a ≤ x) : ShiftedPositiveAt s a := by
  intro p
  rw [momentFunctional_eq_integral s hs hint]
  have hcongr : ∫ x, Polynomial.eval x ((X - C a) * p ^ (2 : ℕ)) ∂μ
      = ∫ x, (x - a) * (Polynomial.eval x p) ^ (2 : ℕ) ∂μ := by
    refine integral_congr_ae (ae_of_all μ (fun x => ?_))
    show Polynomial.eval x ((X - C a) * p ^ (2 : ℕ)) = (x - a) * (Polynomial.eval x p) ^ (2 : ℕ)
    rw [eval_mul, eval_sub, eval_X, eval_C, eval_pow]
  rw [hcongr]
  exact integral_nonneg_of_ae (hμ.mono (fun x hx => mul_nonneg (by linarith) (sq_nonneg _)))

/-- **Zero location.**  Every root of the orthogonal polynomial of a Stieltjes bulk lies to the
right of the shift point.  If `r` were a root with `r < a`, then writing `Q = (X - r) g` and pairing
`Q` with the lower-degree factor `g` gives `0 = L((X - a) g²) + (a - r) L(g²)`, a sum of a
nonnegative and a strictly positive term. -/
theorem monicOrtho_root_ge (h : PositiveMomentForm s) (hst : ShiftedPositiveAt s a) (n : ℕ)
    {r : ℝ} (hr : (monicOrtho s (n + 1)).eval r = 0) : a ≤ r := by
  obtain ⟨g, hg⟩ : (X - C r) ∣ monicOrtho s (n + 1) :=
    dvd_iff_isRoot.mpr hr
  have hgne : g ≠ 0 := by
    intro h0
    rw [h0, mul_zero] at hg
    exact monicOrtho_ne_zero s (n + 1) hg
  have hQnd : (monicOrtho s (n + 1)).natDegree = n + 1 :=
    natDegree_eq_of_degree_eq_some (monicOrtho_degree s (n + 1))
  have hnd : (monicOrtho s (n + 1)).natDegree = 1 + g.natDegree := by
    rw [hg, natDegree_mul (X_sub_C_ne_zero r) hgne, natDegree_X_sub_C]
  have hgdeg : g.degree < ((n + 1 : ℕ) : WithBot ℕ) := by
    rw [degree_eq_natDegree hgne]
    exact_mod_cast (by omega : g.natDegree < n + 1)
  have hzero : momentInner s (monicOrtho s (n + 1)) g = 0 :=
    monicOrtho_inner_eq_zero_of_degree_lt h (n + 1) (n + 1) le_rfl g hgdeg
  have hkey : (X - C r) * g * g = (X - C a) * g ^ (2 : ℕ) + (a - r) • g ^ (2 : ℕ) := by
    rw [Polynomial.smul_eq_C_mul, map_sub]
    ring
  have hexp : momentInner s (monicOrtho s (n + 1)) g
      = momentFunctional s ((X - C a) * g ^ (2 : ℕ)) + (a - r) * momentFunctional s (g ^ (2 : ℕ)) := by
    rw [hg, momentInner_def, hkey, momentFunctional_add, momentFunctional_smul]
  have hA : 0 ≤ momentFunctional s ((X - C a) * g ^ (2 : ℕ)) := hst g
  have hB : 0 < momentFunctional s (g ^ (2 : ℕ)) := by
    have := h.pos_of_ne_zero g hgne
    rwa [momentInner_self] at this
  rw [hexp] at hzero
  nlinarith

/-- **Exterior square decay.**  Outside the shift point the square of the orthogonal polynomial is
strictly decreasing: every node lies at distance at least `a - x` from `x`, and moving right
shortens every factor. -/
theorem monicOrtho_eval_sq_lt (h : PositiveMomentForm s) (hst : ShiftedPositiveAt s a) (n : ℕ)
    {x y : ℝ} (hxy : x < y) (hya : y < a) :
    (monicOrtho s (n + 1)).eval y ^ (2 : ℕ) < (monicOrtho s (n + 1)).eval x ^ (2 : ℕ) := by
  classical
  have hnode : ∀ t ∈ gaussNodes s n, a ≤ t := by
    intro t ht
    exact monicOrtho_root_ge h hst n ((mem_gaussNodes_iff n t).mp ht)
  rw [eval_monicOrtho_eq_prod_gaussNodes h n, eval_monicOrtho_eq_prod_gaussNodes h n,
    ← Finset.prod_pow, ← Finset.prod_pow]
  refine Finset.prod_lt_prod_of_nonempty (fun t ht => ?_) (fun t ht => ?_) ?_
  · have hat := hnode t ht
    exact sq_pos_of_ne_zero (sub_ne_zero.mpr (ne_of_lt (by linarith : y < t)))
  · have hat := hnode t ht
    have h1 : 0 ≤ t - y := by linarith
    have h2 : t - y < t - x := by linarith
    nlinarith
  · rw [← Finset.card_pos, gaussNodes_card h n]
    omega

/-- Every level of the kernel sum is nonincreasing outside the shift point. -/
theorem monicOrtho_eval_sq_le (h : PositiveMomentForm s) (hst : ShiftedPositiveAt s a) (k : ℕ)
    {x y : ℝ} (hxy : x < y) (hya : y < a) :
    (monicOrtho s k).eval y ^ (2 : ℕ) ≤ (monicOrtho s k).eval x ^ (2 : ℕ) := by
  cases k with
  | zero => simp
  | succ m => exact (monicOrtho_eval_sq_lt h hst m hxy hya).le

/-- **Exterior Christoffel--Darboux monotonicity.**  The kernel diagonal is nonincreasing on the
half line to the left of the Stieltjes support. -/
theorem cdKernel_eval_self_le (h : PositiveMomentForm s) (hst : ShiftedPositiveAt s a) (n : ℕ)
    {x y : ℝ} (hxy : x < y) (hya : y < a) :
    (cdKernel s n y).eval y ≤ (cdKernel s n x).eval x := by
  rw [cdKernel_eval_self, cdKernel_eval_self]
  refine Finset.sum_le_sum fun k _ => ?_
  exact (div_le_div_iff_of_pos_right (monicOrtho_inner_self_pos h k)).mpr
    (monicOrtho_eval_sq_le h hst k hxy hya)

/-- **Strict exterior decay.**  From level one on, the kernel diagonal is strictly decreasing. -/
theorem cdKernel_eval_self_lt (h : PositiveMomentForm s) (hst : ShiftedPositiveAt s a) {n : ℕ}
    (hn : 1 ≤ n) {x y : ℝ} (hxy : x < y) (hya : y < a) :
    (cdKernel s n y).eval y < (cdKernel s n x).eval x := by
  rw [cdKernel_eval_self, cdKernel_eval_self]
  refine Finset.sum_lt_sum (fun k _ => ?_) ⟨1, Finset.mem_range.mpr (by omega), ?_⟩
  · exact (div_le_div_iff_of_pos_right (monicOrtho_inner_self_pos h k)).mpr
      (monicOrtho_eval_sq_le h hst k hxy hya)
  · exact (div_lt_div_iff_of_pos_right (monicOrtho_inner_self_pos h 1)).mpr
      (monicOrtho_eval_sq_lt h hst 0 hxy hya)

theorem cdKernel_diag_antitoneOn (h : PositiveMomentForm s) (hst : ShiftedPositiveAt s a) (n : ℕ) :
    AntitoneOn (fun x => (cdKernel s n x).eval x) (Set.Iio a) := by
  intro x hx y hy hxy
  rcases eq_or_lt_of_le hxy with rfl | hlt
  · exact le_rfl
  · exact cdKernel_eval_self_le h hst n hlt hy

theorem cdKernel_diag_strictAntiOn (h : PositiveMomentForm s) (hst : ShiftedPositiveAt s a)
    {n : ℕ} (hn : 1 ≤ n) :
    StrictAntiOn (fun x => (cdKernel s n x).eval x) (Set.Iio a) :=
  fun _ _ _ hy hxy => cdKernel_eval_self_lt h hst hn hxy hy

/-- **The Schur threshold is nondecreasing outside the support.** -/
theorem christoffel_monotoneOn (h : PositiveMomentForm s) (hst : ShiftedPositiveAt s a) (n : ℕ) :
    MonotoneOn (christoffel s n) (Set.Iio a) := by
  intro x hx y hy hxy
  have hpx : 0 < (cdKernel s n x).eval x := cdKernel_eval_self_pos h n x
  have hpy : 0 < (cdKernel s n y).eval y := cdKernel_eval_self_pos h n y
  have hle : (cdKernel s n y).eval y ≤ (cdKernel s n x).eval x :=
    cdKernel_diag_antitoneOn h hst n hx hy hxy
  unfold christoffel
  exact inv_anti₀ hpy hle

/-- **Strict version.** -/
theorem christoffel_strictMonoOn (h : PositiveMomentForm s) (hst : ShiftedPositiveAt s a)
    {n : ℕ} (hn : 1 ≤ n) : StrictMonoOn (christoffel s n) (Set.Iio a) := by
  intro x hx y hy hxy
  have hpy : 0 < (cdKernel s n y).eval y := cdKernel_eval_self_pos h n y
  have hlt : (cdKernel s n y).eval y < (cdKernel s n x).eval x :=
    cdKernel_diag_strictAntiOn h hst hn hx hy hxy
  unfold christoffel
  exact inv_strictAnti₀ hpy hlt

/-- **Boundary-channel corollary.**  For two exterior boundary points, the farther-left point has
the larger kernel diagonal and the smaller Schur threshold. -/
theorem exterior_boundary_comparison (h : PositiveMomentForm s) (hst : ShiftedPositiveAt s a)
    (n : ℕ) {x y : ℝ} (hxy : x < y) (hya : y < a) :
    (cdKernel s n y).eval y ≤ (cdKernel s n x).eval x ∧
      christoffel s n x ≤ christoffel s n y :=
  ⟨cdKernel_eval_self_le h hst n hxy hya,
    christoffel_monotoneOn h hst n (Set.mem_Iio.mpr (hxy.trans hya)) (Set.mem_Iio.mpr hya)
      hxy.le⟩

end HTGeometry
