import Mathlib.LinearAlgebra.Lagrange
import Zeta23.FromPNTPlus.ResidueCalcOnRectangles

/-!
# Lagrange interpolation of holomorphic data through a rectangle contour

Let `v` be distinct nodes, `ω(t) = Π (t - vᵢ)` the nodal polynomial and `wᵢ = Π_{j≠i}(vᵢ - vⱼ)⁻¹`
the nodal weights.  The barycentric part of the Lagrange interpolant carried by the nodes inside a
rectangle `R` is a contour integral whenever the data are the values of a function `G`
holomorphic on a neighbourhood of `R`:

`Σ_{vᵢ ∈ R} wᵢ (x - vᵢ)⁻¹ G(vᵢ) = (2πi)⁻¹ ∮_{∂R} G(t) / ((x - t) ω(t)) dt`

for every `x ∉ R`, provided every node lies either in the interior of `R` or outside `R`
(`sum_nodalWeight_inside_eq_rectangleIntegral`).  The proof is the partial fraction expansion
`Σ wᵢ/(t - vᵢ) = 1/ω(t)` (from `Lagrange.interpolate_one`), the rectangle Cauchy formula at
interior nodes and Cauchy–Goursat at exterior ones.

The contour form bounds the interpolant of clustered nodes without any separation between them:
only the distance from the nodes to `∂R` enters (`norm_rectangleIntegral_le`).
-/

open Complex Set Filter Topology Polynomial Lagrange
open scoped Interval

noncomputable section

namespace HTGeometry

/-! ### Partial fractions of the nodal polynomial -/

/-- `Σ wᵢ (t - vᵢ)⁻¹ = ω(t)⁻¹` away from the nodes. -/
theorem sum_nodalWeight_mul_inv_sub_eq_inv_nodal {ι : Type*} [DecidableEq ι] {s : Finset ι}
    {v : ι → ℂ} (hvs : Set.InjOn v s) (hs : s.Nonempty) {t : ℂ} (ht : ∀ i ∈ s, t ≠ v i) :
    ∑ i ∈ s, nodalWeight s v i * (t - v i)⁻¹ = (eval t (nodal s v))⁻¹ := by
  have h := eval_interpolate_not_at_node (s := s) (v := v) (x := t) 1 ht
  rw [interpolate_one hvs hs, eval_one] at h
  simp only [Pi.one_apply, mul_one] at h
  exact eq_inv_of_mul_eq_one_right h.symm

/-! ### Rectangle integrals of finite sums and their size -/

theorem rectangleIntegral_finsetSum_of_borderIntegrable {ι : Type*} (s : Finset ι)
    (f : ι → ℂ → ℂ) (z w : ℂ)
    (hf : ∀ i ∈ s, RectangleBorderIntegrable (f i) z w) :
    RectangleIntegral (fun t => ∑ i ∈ s, f i t) z w = ∑ i ∈ s, RectangleIntegral (f i) z w := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    simp [RectangleIntegral, HIntegral, VIntegral]
  | insert a s ha ih =>
    have hs : ∀ i ∈ s, RectangleBorderIntegrable (f i) z w := fun i hi =>
      hf i (Finset.mem_insert_of_mem hi)
    have hint : RectangleBorderIntegrable (fun t => ∑ i ∈ s, f i t) z w := by
      refine ⟨?_, ?_, ?_, ?_⟩
      · have := IntervalIntegrable.sum s fun i hi => (hs i hi).1
        simpa [Finset.sum_fn] using this
      · have := IntervalIntegrable.sum s fun i hi => (hs i hi).2.1
        simpa [Finset.sum_fn] using this
      · have := IntervalIntegrable.sum s fun i hi => (hs i hi).2.2.1
        simpa [Finset.sum_fn] using this
      · have := IntervalIntegrable.sum s fun i hi => (hs i hi).2.2.2
        simpa [Finset.sum_fn] using this
    simp only [Finset.sum_insert ha]
    have h := RectangleBorderIntegrable.add (hf a (Finset.mem_insert_self a s)) hint
    rw [← ih hs]
    exact h

theorem rectangleIntegral_const_mul (c : ℂ) (f : ℂ → ℂ) (z w : ℂ) :
    RectangleIntegral (fun t => c * f t) z w = c * RectangleIntegral f z w := by
  simp only [RectangleIntegral, HIntegral, VIntegral, intervalIntegral.integral_const_mul,
    smul_eq_mul]
  ring

/-- `‖∮_{∂R} f‖ ≤ 2(|Δ re| + |Δ im|)·M` when `‖f‖ ≤ M` on `∂R`. -/
theorem norm_rectangleIntegral_le {f : ℂ → ℂ} {z w : ℂ} {M : ℝ}
    (hM : ∀ t ∈ RectangleBorder z w, ‖f t‖ ≤ M) :
    ‖RectangleIntegral f z w‖ ≤ 2 * (|w.re - z.re| + |w.im - z.im|) * M := by
  have h1 : ‖HIntegral f z.re w.re z.im‖ ≤ M * |w.re - z.re| := by
    refine intervalIntegral.norm_integral_le_of_norm_le_const fun x hx => hM _ ?_
    refine Or.inl (Or.inl (Or.inl ⟨?_, ?_⟩)) <;>
      simp [uIoc_subset_uIcc hx]
  have h2 : ‖HIntegral f z.re w.re w.im‖ ≤ M * |w.re - z.re| := by
    refine intervalIntegral.norm_integral_le_of_norm_le_const fun x hx => hM _ ?_
    refine Or.inl (Or.inr ⟨?_, ?_⟩) <;>
      simp [uIoc_subset_uIcc hx]
  have h3 : ‖VIntegral f w.re z.im w.im‖ ≤ M * |w.im - z.im| := by
    rw [VIntegral, norm_smul, Complex.norm_I, one_mul]
    refine intervalIntegral.norm_integral_le_of_norm_le_const fun y hy => hM _ ?_
    refine Or.inr ⟨?_, ?_⟩ <;>
      simp [uIoc_subset_uIcc hy]
  have h4 : ‖VIntegral f z.re z.im w.im‖ ≤ M * |w.im - z.im| := by
    rw [VIntegral, norm_smul, Complex.norm_I, one_mul]
    refine intervalIntegral.norm_integral_le_of_norm_le_const fun y hy => hM _ ?_
    refine Or.inl (Or.inl (Or.inr ⟨?_, ?_⟩)) <;>
      simp [uIoc_subset_uIcc hy]
  unfold RectangleIntegral
  set A := HIntegral f z.re w.re z.im
  set B := HIntegral f z.re w.re w.im
  set C := VIntegral f w.re z.im w.im
  set D := VIntegral f z.re z.im w.im
  have e1 := norm_sub_le (A - B + C) D
  have e2 := norm_add_le (A - B) C
  have e3 := norm_sub_le A B
  have hM0 : 0 ≤ M := le_trans (norm_nonneg _) (hM _ (Or.inl (Or.inl (Or.inl
    ⟨left_mem_uIcc, rfl⟩))))
  nlinarith [abs_nonneg (w.re - z.re), abs_nonneg (w.im - z.im)]

/-! ### Cauchy's formula on a rectangle -/

/-- For `h` holomorphic on an open `U ⊇ R` and `p` interior to `R`,
`(2πi)⁻¹ ∮_{∂R} h(t)/(t - p) dt = h(p)`. -/
theorem rectangleIntegral'_div_sub_eq {h : ℂ → ℂ} {z w p : ℂ} {U : Set ℂ}
    (hRU : Rectangle z w ⊆ U) (hh : DifferentiableOn ℂ h U) (hzw : z.re ≤ w.re)
    (hzw' : z.im ≤ w.im) (hp : Rectangle z w ∈ 𝓝 p) :
    RectangleIntegral' (fun t => h t / (t - p)) z w = h p := by
  have hpU : U ∈ 𝓝 p := Filter.mem_of_superset hp hRU
  have hg : DifferentiableOn ℂ (dslope h p) U := (differentiableOn_dslope hpU).mpr hh
  refine ResidueTheoremOnRectangleWithSimplePole hzw hzw' hp (hg.mono hRU) ?_
  intro t ht
  have htp : t ≠ p := ht.2
  simp only [Pi.sub_apply]
  rw [dslope_of_ne _ htp, slope_def_field]
  field_simp [sub_ne_zero.mpr htp]

/-- For `h` holomorphic on an open `U ⊇ R` and `q ∉ R`, `∮_{∂R} h(t)/(t - q) dt = 0`. -/
theorem rectangleIntegral_div_sub_eq_zero {h : ℂ → ℂ} {z w q : ℂ} {U : Set ℂ}
    (hRU : Rectangle z w ⊆ U) (hh : DifferentiableOn ℂ h U) (hq : q ∉ Rectangle z w) :
    RectangleIntegral (fun t => h t / (t - q)) z w = 0 := by
  have hd : DifferentiableOn ℂ (fun t => h t / (t - q)) (U ∩ {q}ᶜ) := by
    refine (hh.mono inter_subset_left).div (by fun_prop) fun t ht => sub_ne_zero.mpr ht.2
  exact HolomorphicOn.vanishesOnRectangle hd fun t ht => ⟨hRU ht, fun h => hq (h ▸ ht)⟩

/-! ### The contour form of the barycentric sum -/

open scoped Classical in
/-- **Contour form of the interior barycentric sum.**  Let the nodes `vᵢ` (`i ∈ s`) be distinct,
each either interior to the rectangle `R = [z, w]` or outside it, and let `G` be holomorphic on an
open `U ⊇ R`.  For `x ∉ R`,
`Σ_{vᵢ ∈ R} wᵢ (x - vᵢ)⁻¹ G(vᵢ) = (2πi)⁻¹ ∮_{∂R} G(t) / ((x - t) ω(t)) dt`. -/
theorem sum_nodalWeight_inside_eq_rectangleIntegral {ι : Type*} [DecidableEq ι] {s : Finset ι}
    {v : ι → ℂ} (hvs : Set.InjOn v s) (hs : s.Nonempty) {G : ℂ → ℂ} {z w x : ℂ} {U : Set ℂ}
    (hU : IsOpen U) (hRU : Rectangle z w ⊆ U) (hG : DifferentiableOn ℂ G U) (hzw : z.re ≤ w.re)
    (hzw' : z.im ≤ w.im)
    (hnode : ∀ i ∈ s, Rectangle z w ∈ 𝓝 (v i) ∨ v i ∉ Rectangle z w)
    (hx : x ∉ Rectangle z w) :
    ∑ i ∈ s.filter (fun i => v i ∈ Rectangle z w), nodalWeight s v i * (x - v i)⁻¹ * G (v i)
      = RectangleIntegral' (fun t => G t / ((x - t) * eval t (nodal s v))) z w := by
  classical
  set R := Rectangle z w
  set U' := U ∩ {x}ᶜ with hU'
  have hU'o : IsOpen U' := hU.inter isOpen_compl_singleton
  have hRU' : R ⊆ U' := fun t ht => ⟨hRU ht, fun h => hx (h ▸ ht)⟩
  set h : ℂ → ℂ := fun t => G t / (x - t) with hh
  have hhd : DifferentiableOn ℂ h U' := by
    refine (hG.mono inter_subset_left).div (by fun_prop) fun t ht => ?_
    exact sub_ne_zero.mpr fun e => ht.2 e.symm
  -- nodes are not on the border
  have hborder : ∀ t ∈ RectangleBorder z w, ∀ i ∈ s, t ≠ v i := by
    intro t ht i hi e
    rcases hnode i hi with h1 | h1
    · exact not_mem_rectangleBorder_of_rectangle_mem_nhds h1 (e ▸ ht)
    · exact h1 (e ▸ rectangleBorder_subset_rectangle z w ht)
  -- rewrite the integrand on the border by partial fractions
  have heq : Set.EqOn (fun t => G t / ((x - t) * eval t (nodal s v)))
      (fun t => ∑ i ∈ s, nodalWeight s v i * (h t / (t - v i))) (RectangleBorder z w) := by
    intro t ht
    have hpf := sum_nodalWeight_mul_inv_sub_eq_inv_nodal hvs hs (hborder t ht)
    simp only [hh]
    rw [div_mul_eq_div_div, div_eq_mul_inv (G t / (x - t)), ← hpf, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    ring
  have hint : ∀ i ∈ s, RectangleBorderIntegrable
      (fun t => nodalWeight s v i * (h t / (t - v i))) z w := by
    intro i hi
    refine ContinuousOn.rectangleBorder_integrable ?_
    refine continuousOn_const.mul ?_
    refine ((hhd.continuousOn).mono ?_).div (by fun_prop) fun t ht =>
      sub_ne_zero.mpr (hborder t ht i hi)
    exact (rectangleBorder_subset_rectangle z w).trans hRU'
  rw [RectangleIntegral'_congr heq, RectangleIntegral',
    rectangleIntegral_finsetSum_of_borderIntegrable _ _ _ _ hint,
    Finset.smul_sum]
  -- evaluate each term
  have hterm : ∀ i ∈ s, (1 / (2 * (Real.pi : ℂ) * I)) •
      RectangleIntegral (fun t => nodalWeight s v i * (h t / (t - v i))) z w =
      if v i ∈ R then nodalWeight s v i * (x - v i)⁻¹ * G (v i) else 0 := by
    intro i hi
    rw [rectangleIntegral_const_mul, smul_eq_mul]
    split_ifs with hin
    · rcases hnode i hi with hint' | hout
      · have := rectangleIntegral'_div_sub_eq hRU' hhd hzw hzw' hint'
        rw [RectangleIntegral', smul_eq_mul] at this
        rw [mul_left_comm, this]
        simp only [hh]
        ring
      · exact absurd hin hout
    · rw [rectangleIntegral_div_sub_eq_zero hRU' hhd hin, mul_zero, mul_zero]
  rw [Finset.sum_congr rfl hterm, Finset.sum_ite, Finset.sum_const_zero, add_zero]

end HTGeometry
