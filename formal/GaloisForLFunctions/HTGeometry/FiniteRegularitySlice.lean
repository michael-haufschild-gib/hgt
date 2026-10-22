import GaloisForLFunctions.HTGeometry.FiniteRegularityWienerFamily
import GaloisForLFunctions.HTGeometry.KleinGordon.KleinGordonSupportBounds

/-!
# Derivatives of a time slice of a jointly differentiable function

A potential of finite regularity is cut off to a compactly supported function `H` of the event, and
the curve of spatial potentials is the family of its time slices. The two bounds an admissible
family asks for — uniform in time, and Lipschitz in time — are statements about the spatial
derivatives of those slices.

The slice map `y ↦ (t, y)` is affine with linear part the inclusion, whose norm is one, so the
`i`-th derivative of a slice is the `i`-th derivative of `H` composed with that inclusion. Hence it
is dominated by the full derivative at the same event, which is continuous and compactly supported;
that gives the uniform bound, and the mean value inequality in the time direction gives the
Lipschitz bound.
-/

namespace GaloisForLFunctions.HTGeometry

open MeasureTheory

section Slice

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem norm_inr_le : ‖(ContinuousLinearMap.inr ℝ ℝ E)‖ ≤ 1 := by
  refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun x => ?_
  rw [one_mul]
  show ‖((0 : ℝ), x)‖ ≤ ‖x‖
  rw [Prod.norm_def]
  simp

/-- **The `i`-th spatial derivative of a time slice is the `i`-th derivative of the function,
restricted to the spatial directions.** -/
theorem iteratedFDeriv_slice {i : ℕ} {n : WithTop ℕ∞} {H : ℝ × E → F} (hH : ContDiff ℝ n H)
    (hi : (i : WithTop ℕ∞) ≤ n) (t : ℝ) (x : E) :
    iteratedFDeriv ℝ i (fun y : E => H (t, y)) x
      = (iteratedFDeriv ℝ i H (t, x)).compContinuousLinearMap
          fun _ => (ContinuousLinearMap.inr ℝ ℝ E) := by
  have hshift : (fun y : E => H (t, y))
      = (fun p : ℝ × E => H (p + (t, 0))) ∘ (ContinuousLinearMap.inr ℝ ℝ E) := by
    funext y
    show H (t, y) = H ((0, y) + (t, 0))
    congr 1
    exact Prod.ext (by simp) (by simp)
  have hcd : ContDiff ℝ n fun p : ℝ × E => H (p + (t, 0)) :=
    hH.comp (contDiff_id.add contDiff_const)
  rw [hshift, ContinuousLinearMap.iteratedFDeriv_comp_right _ hcd x hi,
    iteratedFDeriv_comp_add_right]
  congr 2
  show ((0 : ℝ), x) + (t, 0) = (t, x)
  exact Prod.ext (by simp) (by simp)

theorem norm_iteratedFDeriv_slice_le {i : ℕ} {n : WithTop ℕ∞} {H : ℝ × E → F} (hH : ContDiff ℝ n H)
    (hi : (i : WithTop ℕ∞) ≤ n) (t : ℝ) (x : E) :
    ‖iteratedFDeriv ℝ i (fun y : E => H (t, y)) x‖ ≤ ‖iteratedFDeriv ℝ i H (t, x)‖ := by
  rw [iteratedFDeriv_slice hH hi t x]
  refine (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans ?_
  have hprod : (∏ _i : Fin i, ‖(ContinuousLinearMap.inr ℝ ℝ E)‖) ≤ 1 := by
    rw [Finset.prod_const]
    exact pow_le_one₀ (norm_nonneg _) norm_inr_le
  calc ‖iteratedFDeriv ℝ i H (t, x)‖ * ∏ _i : Fin i, ‖(ContinuousLinearMap.inr ℝ ℝ E)‖
      ≤ ‖iteratedFDeriv ℝ i H (t, x)‖ * 1 :=
        mul_le_mul_of_nonneg_left hprod (norm_nonneg _)
    _ = ‖iteratedFDeriv ℝ i H (t, x)‖ := mul_one _

theorem norm_iteratedFDeriv_slice_sub_le {i : ℕ} {n : WithTop ℕ∞} {H : ℝ × E → F}
    (hH : ContDiff ℝ n H) (hi : (i : WithTop ℕ∞) ≤ n) (t t' : ℝ) (x : E) :
    ‖iteratedFDeriv ℝ i (fun y : E => H (t, y)) x
        - iteratedFDeriv ℝ i (fun y : E => H (t', y)) x‖
      ≤ ‖iteratedFDeriv ℝ i H (t, x) - iteratedFDeriv ℝ i H (t', x)‖ := by
  have hsub : iteratedFDeriv ℝ i (fun y : E => H (t, y)) x
      - iteratedFDeriv ℝ i (fun y : E => H (t', y)) x
      = (iteratedFDeriv ℝ i H (t, x) - iteratedFDeriv ℝ i H (t', x)).compContinuousLinearMap
          fun _ => (ContinuousLinearMap.inr ℝ ℝ E) := by
    rw [iteratedFDeriv_slice hH hi t x, iteratedFDeriv_slice hH hi t' x]
    ext m
    simp
  rw [hsub]
  refine (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans ?_
  have hprod : (∏ _i : Fin i, ‖(ContinuousLinearMap.inr ℝ ℝ E)‖) ≤ 1 := by
    rw [Finset.prod_const]
    exact pow_le_one₀ (norm_nonneg _) norm_inr_le
  calc ‖iteratedFDeriv ℝ i H (t, x) - iteratedFDeriv ℝ i H (t', x)‖
        * ∏ _i : Fin i, ‖(ContinuousLinearMap.inr ℝ ℝ E)‖
      ≤ ‖iteratedFDeriv ℝ i H (t, x) - iteratedFDeriv ℝ i H (t', x)‖ * 1 :=
        mul_le_mul_of_nonneg_left hprod (norm_nonneg _)
    _ = ‖iteratedFDeriv ℝ i H (t, x) - iteratedFDeriv ℝ i H (t', x)‖ := mul_one _

/-! ## Uniform and Lipschitz bounds -/

/-- The time derivative of a jointly `C¹` function of the event, read as a function of the event. -/
noncomputable def timePartial (G : ℝ × E → F) (p : ℝ × E) : F :=
  fderiv ℝ (fun s : ℝ => G (s, p.2)) p.1 1

theorem contDiff_timePartial {G : ℝ × E → F} (hG : ContDiff ℝ (1 : ℕ) G) :
    ContDiff ℝ (0 : ℕ) (timePartial G) := by
  have hslice : ContDiff ℝ (1 : ℕ) fun q : (ℝ × E) × ℝ => G (q.2, q.1.2) := by
    have hmap : ContDiff ℝ (1 : ℕ) fun q : (ℝ × E) × ℝ => ((q.2, q.1.2) : ℝ × E) := by fun_prop
    exact hG.comp hmap
  have hfd : ContDiff ℝ (0 : ℕ) fun p : ℝ × E => fderiv ℝ (fun s : ℝ => G (s, p.2)) p.1 := by
    refine hslice.fderiv contDiff_fst ?_
    norm_num
  exact hfd.clm_apply contDiff_const

omit [NormedSpace ℝ E] in
theorem timePartial_eq_zero_of_notMem {G : ℝ × E → F} {S : Set (ℝ × E)} (hS : IsClosed S)
    (hzero : ∀ p : ℝ × E, p ∉ S → G p = 0) {p : ℝ × E} (hp : p ∉ S) : timePartial G p = 0 := by
  have hmem : {t : ℝ | (t, p.2) ∈ Sᶜ} ∈ nhds p.1 := by
    have hcont : Continuous fun t : ℝ => ((t, p.2) : ℝ × E) := by fun_prop
    exact (hS.isOpen_compl.preimage hcont).mem_nhds (by simpa using hp)
  have hnhds : (fun s : ℝ => G (s, p.2)) =ᶠ[nhds p.1] fun _ : ℝ => (0 : F) :=
    Filter.eventually_of_mem hmem fun s hs => hzero (s, p.2) hs
  show fderiv ℝ (fun s : ℝ => G (s, p.2)) p.1 1 = 0
  rw [hnhds.fderiv_eq]
  simp

/-- **A jointly `C¹` function with compact support is Lipschitz in time, uniformly in space.** -/
theorem exists_lipschitz_time {G : ℝ × E → F} (hG : ContDiff ℝ (1 : ℕ) G)
    (hsupp : HasCompactSupport G) :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ (t t' : ℝ) (x : E), ‖G (t, x) - G (t', x)‖ ≤ L * |t - t'| := by
  have hDcont : Continuous (timePartial G) := (contDiff_timePartial hG).continuous
  have hDzero : ∀ p : ℝ × E, p ∉ tsupport G → timePartial G p = 0 :=
    fun p hp => timePartial_eq_zero_of_notMem (isClosed_tsupport G) (fun q hq =>
      image_eq_zero_of_notMem_tsupport hq) hp
  obtain ⟨L, hL⟩ := hDcont.bounded_above_of_compact_support
    (HasCompactSupport.intro hsupp (K := tsupport G) hDzero)
  refine ⟨L, le_trans (norm_nonneg (timePartial G (0, 0))) (hL (0, 0)), ?_⟩
  intro t t' x
  have hderiv : ∀ s : ℝ, HasDerivAt (fun r : ℝ => G (r, x)) (timePartial G (s, x)) s := by
    intro s
    have hsl : ContDiff ℝ (1 : ℕ) fun r : ℝ => ((r, x) : ℝ × E) := by fun_prop
    have hdiff : DifferentiableAt ℝ (fun r : ℝ => G (r, x)) s :=
      (hG.comp hsl).differentiable (by norm_num) s
    exact hdiff.hasFDerivAt.hasDerivAt
  have hmv := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (f := fun r : ℝ => G (r, x)) (f' := fun s : ℝ => timePartial G (s, x)) (s := Set.univ)
    (fun s _ => (hderiv s).hasDerivWithinAt) (fun s _ => hL (s, x)) convex_univ
    (Set.mem_univ t') (Set.mem_univ t)
  rw [Real.norm_eq_abs] at hmv
  exact hmv

end Slice

end GaloisForLFunctions.HTGeometry
