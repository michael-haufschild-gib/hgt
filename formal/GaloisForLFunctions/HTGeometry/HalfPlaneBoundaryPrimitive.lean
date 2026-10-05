import GaloisForLFunctions.HTGeometry.RightHalfPlanePrimitive

/-!
# A primitive continuous up to the boundary of a half-plane

Let `f` be continuous on the closed half-plane `Re z ≥ a` and holomorphic on `Re z > a`.  Fix
`b > a`.  The path integral along `b → b + i Im s → s`,

`P(s) = ∫_0^{Im s} i f(b + iv) dv + ∫_b^{Re s} f(u + i Im s) du`

(`pathPrimitive`), with `f` clamped to the half-plane outside it, has the following properties.

* `P` is continuous on all of `ℂ` (`continuous_pathPrimitive`).
* `P' = f` on `Re s > a` (`hasDerivAt_pathPrimitive`).  It agrees there with any primitive,
  normalized at `b`.
* **Boundary increment** (`pathPrimitive_boundary_sub`):
  `P(a + iy) − P(a + iy₀) = i ∫_{y₀}^{y} f(a + iv) dv`.  This is Cauchy's theorem on the rectangle
  `[a, b] × [y₀, y]`, which needs `f` only continuous on the closed rectangle.
* **Real structure** (`pathPrimitive_conj`): if `f(z̄) = conj f(z)` on `Re z ≥ a`, then
  `P(s̄) = conj P(s)`.

So on the boundary line `Im P(a + iy) − Im P(a + iy₀) = ∫_{y₀}^{y} Re f(a + iv) dv`.  For a
Carathéodory function `f` (`Re f ≥ 0`) this phase is monotone.
-/

open Complex Set

noncomputable section

namespace GaloisForLFunctions.HTGeometry

/-- `f` clamped to the closed half-plane `Re z ≥ a`: `z ↦ f(max(Re z, a) + i Im z)`. -/
def clampRe (a : ℝ) (f : ℂ → ℂ) (z : ℂ) : ℂ := f (((max z.re a : ℝ) : ℂ) + (z.im : ℂ) * I)

theorem clampRe_eq {a : ℝ} (f : ℂ → ℂ) {z : ℂ} (hz : a ≤ z.re) : clampRe a f z = f z := by
  unfold clampRe
  rw [max_eq_left hz, Complex.re_add_im]

theorem continuous_clampRe {a : ℝ} {f : ℂ → ℂ} (hf : ContinuousOn f {z : ℂ | a ≤ z.re}) :
    Continuous (clampRe a f) := by
  unfold clampRe
  refine hf.comp_continuous (by fun_prop) fun z => ?_
  show a ≤ (((max z.re a : ℝ) : ℂ) + (z.im : ℂ) * I).re
  simp

/-- The path primitive along `b → b + i Im s → s`. -/
def pathPrimitive (a b : ℝ) (f : ℂ → ℂ) (s : ℂ) : ℂ :=
  (∫ v in (0 : ℝ)..s.im, I * clampRe a f ((b : ℂ) + (v : ℂ) * I)) +
    ∫ u in b..s.re, clampRe a f ((u : ℂ) + (s.im : ℂ) * I)

theorem continuous_pathPrimitive {a b : ℝ} {f : ℂ → ℂ}
    (hf : ContinuousOn f {z : ℂ | a ≤ z.re}) : Continuous (pathPrimitive a b f) := by
  have hg := continuous_clampRe hf
  unfold pathPrimitive
  refine Continuous.add ?_ ?_
  · have hv : Continuous fun v : ℝ => I * clampRe a f ((b : ℂ) + (v : ℂ) * I) :=
      continuous_const.mul (hg.comp (by fun_prop))
    exact (intervalIntegral.continuous_primitive (fun _ _ => hv.intervalIntegrable _ _) 0).comp
      Complex.continuous_im
  · -- substitute `u = b + θ (Re s − b)`, `θ ∈ [0, 1]`
    have e : (fun s : ℂ => ∫ u in b..s.re, clampRe a f ((u : ℂ) + (s.im : ℂ) * I)) =
        fun s : ℂ => ((s.re - b : ℝ) : ℂ) * ∫ θ in (0 : ℝ)..1,
          clampRe a f (((b + θ * (s.re - b) : ℝ) : ℂ) + (s.im : ℂ) * I) := by
      funext s
      by_cases hs : s.re - b = 0
      · have : s.re = b := by linarith
        rw [this, intervalIntegral.integral_same, sub_self]; simp
      · have h := intervalIntegral.integral_comp_mul_add
          (fun u : ℝ => clampRe a f ((u : ℂ) + (s.im : ℂ) * I)) hs b (a := 0) (b := 1)
        simp only [mul_zero, zero_add, mul_one, sub_add_cancel] at h
        rw [show (fun x : ℝ => clampRe a f (((((s.re - b) * x + b : ℝ)) : ℂ) + (s.im : ℂ) * I)) =
          fun θ : ℝ => clampRe a f (((b + θ * (s.re - b) : ℝ) : ℂ) + (s.im : ℂ) * I) by
            funext θ; congr 2; push_cast; ring] at h
        rw [h, Complex.real_smul, ← mul_assoc, Complex.ofReal_inv,
          mul_inv_cancel₀ (by exact_mod_cast hs), one_mul]
    rw [e]
    refine Continuous.mul (by fun_prop) ?_
    exact intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
      (f := fun (s : ℂ) (θ : ℝ) => clampRe a f (((b + θ * (s.re - b) : ℝ) : ℂ) + (s.im : ℂ) * I))
      (hg.comp (by fun_prop)) 0 1

/-- On `Re s > a`, the path primitive is the primitive normalized at `b`. -/
theorem pathPrimitive_eq_sub {a b : ℝ} (hab : a < b) {f P₀ : ℂ → ℂ}
    (hfc : ContinuousOn f {z : ℂ | a ≤ z.re})
    (hP₀ : ∀ z : ℂ, a < z.re → HasDerivAt P₀ (f z) z) {s : ℂ} (hs : a < s.re) :
    pathPrimitive a b f s = P₀ s - P₀ b := by
  have hg := continuous_clampRe hfc
  -- the vertical leg
  have hvert : ∫ v in (0 : ℝ)..s.im, I * clampRe a f ((b : ℂ) + (v : ℂ) * I) =
      P₀ ((b : ℂ) + (s.im : ℂ) * I) - P₀ b := by
    have hd : ∀ v ∈ uIcc (0 : ℝ) s.im, HasDerivAt (fun v : ℝ => P₀ ((b : ℂ) + (v : ℂ) * I))
        (I * clampRe a f ((b : ℂ) + (v : ℂ) * I)) v := by
      intro v _
      have hre : a < ((b : ℂ) + (v : ℂ) * I).re := by simp; exact hab
      have h1 : HasDerivAt (fun z : ℂ => (b : ℂ) + z * I) I (v : ℂ) := by
        simpa using ((hasDerivAt_id (v : ℂ)).mul_const I).const_add (b : ℂ)
      have h2 := ((hP₀ _ hre).comp (v : ℂ) h1).comp_ofReal
      rw [clampRe_eq f hre.le, mul_comm]
      exact h2
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd
      ((continuous_const.mul (hg.comp (by fun_prop))).intervalIntegrable _ _)]
    simp
  -- the horizontal leg
  have hhor : ∫ u in b..s.re, clampRe a f ((u : ℂ) + (s.im : ℂ) * I) =
      P₀ s - P₀ ((b : ℂ) + (s.im : ℂ) * I) := by
    have hd : ∀ u ∈ uIcc b s.re, HasDerivAt (fun u : ℝ => P₀ ((u : ℂ) + (s.im : ℂ) * I))
        (clampRe a f ((u : ℂ) + (s.im : ℂ) * I)) u := by
      intro u hu
      have hu' : a < u := by
        rcases le_total b s.re with h | h
        · rw [uIcc_of_le h] at hu; linarith [hu.1]
        · rw [uIcc_of_ge h] at hu; linarith [hu.1]
      have hre : a < ((u : ℂ) + (s.im : ℂ) * I).re := by simp; exact hu'
      have h1 : HasDerivAt (fun z : ℂ => z + (s.im : ℂ) * I) 1 (u : ℂ) :=
        (hasDerivAt_id (u : ℂ)).add_const _
      have h2 := ((hP₀ _ hre).comp (u : ℂ) h1).comp_ofReal
      rw [clampRe_eq f hre.le]
      simpa using h2
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd
      ((hg.comp (by fun_prop)).intervalIntegrable _ _), Complex.re_add_im]
  unfold pathPrimitive
  rw [hvert, hhor]; ring

/-- `P' = f` on `Re s > a`. -/
theorem hasDerivAt_pathPrimitive {a b : ℝ} (hab : a < b) {f : ℂ → ℂ}
    (hfc : ContinuousOn f {z : ℂ | a ≤ z.re}) (hfd : DifferentiableOn ℂ f {z : ℂ | a < z.re})
    {s : ℂ} (hs : a < s.re) : HasDerivAt (pathPrimitive a b f) (f s) s := by
  obtain ⟨P₀, hP₀⟩ := isExactOn_rightHalfPlane hfd
  have hU : IsOpen {z : ℂ | a < z.re} := isOpen_lt continuous_const Complex.continuous_re
  have hev : (fun z => P₀ z - P₀ b) =ᶠ[nhds s] pathPrimitive a b f := by
    filter_upwards [hU.mem_nhds hs] with z hz
    exact (pathPrimitive_eq_sub hab hfc (fun z hz => hP₀ z hz) hz).symm
  exact ((hP₀ s hs).sub_const (P₀ b)).congr_of_eventuallyEq hev.symm

/-- **The boundary increment.**  `P(a + iy) − P(a + iy₀) = i ∫_{y₀}^{y} f(a + iv) dv`. -/
theorem pathPrimitive_boundary_sub {a b : ℝ} (hab : a < b) {f : ℂ → ℂ}
    (hfc : ContinuousOn f {z : ℂ | a ≤ z.re}) (hfd : DifferentiableOn ℂ f {z : ℂ | a < z.re})
    (y₀ y : ℝ) :
    pathPrimitive a b f ((a : ℂ) + (y : ℂ) * I) - pathPrimitive a b f ((a : ℂ) + (y₀ : ℂ) * I) =
      I * ∫ v in y₀..y, f ((a : ℂ) + (v : ℂ) * I) := by
  have hg := continuous_clampRe hfc
  have hrect := integral_boundary_rect_eq_zero_of_continuousOn_of_differentiableOn f
    ((a : ℂ) + (y₀ : ℂ) * I) ((b : ℂ) + (y : ℂ) * I) ?_ ?_
  · simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.I_im,
      Complex.ofReal_im, mul_zero, mul_one, sub_zero, add_zero, Complex.add_im, Complex.mul_im,
      zero_add, smul_eq_mul] at hrect
    -- replace the clamped integrands by `f`
    have hc1 : ∀ y' : ℝ, ∫ u in b..a, clampRe a f ((u : ℂ) + (y' : ℂ) * I) =
        -∫ u in a..b, f ((u : ℂ) + (y' : ℂ) * I) := by
      intro y'
      rw [intervalIntegral.integral_symm]
      congr 1
      refine intervalIntegral.integral_congr fun u hu => ?_
      rw [uIcc_of_le hab.le] at hu
      exact clampRe_eq f (by simp; exact hu.1)
    have hc2 : ∫ v in y₀..y, I * clampRe a f ((b : ℂ) + (v : ℂ) * I) =
        I * ∫ v in y₀..y, f ((b : ℂ) + (v : ℂ) * I) := by
      rw [intervalIntegral.integral_const_mul]
      congr 1
      refine intervalIntegral.integral_congr fun v _ => ?_
      exact clampRe_eq f (by simp; exact hab.le)
    unfold pathPrimitive
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.I_im,
      Complex.ofReal_im, mul_zero, mul_one, sub_zero, add_zero, Complex.add_im, Complex.mul_im,
      zero_add]
    have hsplit : (∫ v in (0 : ℝ)..y, I * clampRe a f ((b : ℂ) + (v : ℂ) * I)) -
        ∫ v in (0 : ℝ)..y₀, I * clampRe a f ((b : ℂ) + (v : ℂ) * I) =
        ∫ v in y₀..y, I * clampRe a f ((b : ℂ) + (v : ℂ) * I) :=
      intervalIntegral.integral_interval_sub_left
        ((continuous_const.mul (hg.comp (by fun_prop))).intervalIntegrable _ _)
        ((continuous_const.mul (hg.comp (by fun_prop))).intervalIntegrable _ _)
    rw [hc1 y, hc1 y₀]
    linear_combination hsplit + hc2 + hrect
  · refine hfc.mono fun z hz => ?_
    simp only [mem_reProdIm] at hz
    show a ≤ z.re
    have := hz.1
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.I_im,
      Complex.ofReal_im, mul_zero, mul_one, sub_zero, add_zero] at this
    rw [uIcc_of_le hab.le] at this
    exact this.1
  · refine hfd.mono fun z hz => ?_
    simp only [mem_reProdIm] at hz
    show a < z.re
    have := hz.1
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.I_im,
      Complex.ofReal_im, mul_zero, mul_one, sub_zero, add_zero, min_eq_left hab.le] at this
    exact this.1

private theorem intervalIntegral_conj (g : ℝ → ℂ) (x₀ x₁ : ℝ) :
    ∫ x in x₀..x₁, starRingEnd ℂ (g x) = starRingEnd ℂ (∫ x in x₀..x₁, g x) := by
  simp only [intervalIntegral, integral_conj, map_sub]

/-- **Real structure.**  If `f(z̄) = conj f(z)` on `Re z ≥ a`, then `P(s̄) = conj P(s)`. -/
theorem pathPrimitive_conj {a b : ℝ} {f : ℂ → ℂ}
    (hconj : ∀ z : ℂ, a ≤ z.re → f (starRingEnd ℂ z) = starRingEnd ℂ (f z)) (s : ℂ) :
    pathPrimitive a b f (starRingEnd ℂ s) = starRingEnd ℂ (pathPrimitive a b f s) := by
  have hcl : ∀ z : ℂ, clampRe a f (starRingEnd ℂ z) = starRingEnd ℂ (clampRe a f z) := by
    intro z
    unfold clampRe
    have e : (((max (starRingEnd ℂ z).re a : ℝ) : ℂ) + ((starRingEnd ℂ z).im : ℂ) * I) =
        starRingEnd ℂ (((max z.re a : ℝ) : ℂ) + (z.im : ℂ) * I) := by
      apply Complex.ext <;> simp
    rw [e, hconj _ (by simp)]
  unfold pathPrimitive
  rw [map_add]
  congr 1
  · -- vertical leg: substitute `v ↦ −v`
    rw [Complex.conj_im]
    have h1 : ∫ v in (0 : ℝ)..-s.im, I * clampRe a f ((b : ℂ) + (v : ℂ) * I) =
        -∫ w in (0 : ℝ)..s.im, I * clampRe a f ((b : ℂ) + ((-w : ℝ) : ℂ) * I) := by
      rw [intervalIntegral.integral_comp_neg
        (fun v : ℝ => I * clampRe a f ((b : ℂ) + (v : ℂ) * I)), neg_zero,
        intervalIntegral.integral_symm]
    have h2 : ∀ w : ℝ, I * clampRe a f ((b : ℂ) + ((-w : ℝ) : ℂ) * I) =
        I * starRingEnd ℂ (clampRe a f ((b : ℂ) + (w : ℂ) * I)) := by
      intro w
      have e : (b : ℂ) + ((-w : ℝ) : ℂ) * I = starRingEnd ℂ ((b : ℂ) + (w : ℂ) * I) := by
        apply Complex.ext <;> simp
      rw [e, hcl]
    rw [h1, intervalIntegral.integral_congr (fun w _ => h2 w), intervalIntegral.integral_const_mul,
      intervalIntegral_conj, intervalIntegral.integral_const_mul, map_mul, Complex.conj_I]
    ring
  · rw [Complex.conj_re, Complex.conj_im, ← intervalIntegral_conj]
    refine intervalIntegral.integral_congr fun u _ => ?_
    have e : (u : ℂ) + ((-s.im : ℝ) : ℂ) * I = starRingEnd ℂ ((u : ℂ) + (s.im : ℂ) * I) := by
      apply Complex.ext <;> simp
    rw [e, hcl]

end GaloisForLFunctions.HTGeometry
