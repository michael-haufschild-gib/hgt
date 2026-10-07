import GaloisForLFunctions.HTGeometry.CosineCornerSequence

/-!
# The remaining marked fibers escape the real lattice

The analytic corner has an injective discrete specialization in a nontrivial
cube-root fiber. Reciprocal reflection supplies the other fiber. All exhibited
points have nonzero homogeneous denominator and are genuinely holomorphic.
-/

namespace GaloisForLFunctions.HTGeometry.CosineProductNonrealFibers

open Complex Filter LabeledCosineDescent CosineCornerUnfolding CosineCornerMarker
open CosineCornerCoordinates CosineCornerSequence
open scoped Topology

noncomputable section

theorem exists_nonreal_mark_family :
    ∃ w : ℕ → ℂ, Function.Injective w ∧ ∀ n,
      (w n).im ≠ 0 ∧ CosineProductRepair.denominator (w n) ≠ 0 ∧
        CosineProductRepair.repair (w n) = mark := by
  obtain ⟨E, u, hE, _, hrel, hu, hu0, huf⟩ :=
    exists_corner_branch (source 0) conicConstant slope root root_cos_ne_source
      root_sin_ne_zero root_slope
  let v (n : ℕ) := u (parameters n)
  have hv : Tendsto v atTop (𝓝 root) := by
    simpa only [Function.comp_def, hu0] using hu.continuousAt.tendsto.comp parameters_limit
  have heinput : Tendsto (fun n : ℕ ↦ ((n : ℂ)⁻¹, v n)) atTop (𝓝 (0, root)) := by
    rw [nhds_prod_eq]
    exact inverse_parameter_limit.prodMk hv
  have he := heinput.eventually hrel
  have hf := parameters_limit.eventually huf
  let z (n : ℕ) := smallCoordinate E (parameters n, v n)
  have hpair : Tendsto (fun n ↦ (parameters n, v n)) atTop (𝓝 ((0, 0), root)) := by
    rw [nhds_prod_eq]
    exact parameters_limit.prodMk hv
  have hz : Tendsto z atTop (𝓝 0) := by
    simpa only [Function.comp_def, smallCoordinate_corner] using
      (smallCoordinate_analyticAt hE).continuousAt.tendsto.comp hpair
  have hden : Tendsto (fun n ↦ 1 - 2 * source 0 * z n + z n ^ 2) atTop (𝓝 1) := by
    simpa using (tendsto_const_nhds.sub (tendsto_const_nhds.mul hz)).add (hz.pow 2)
  have hp : Tendsto (fun n ↦ cos (v n) - source 0) atTop (𝓝 (cos root - source 0)) :=
    (Complex.continuous_cos.continuousAt.tendsto.comp hv).sub_const _
  have hs : -sin root ≠ 0 := neg_ne_zero.mpr root_sin_ne_zero
  let g := (Complex.hasStrictDerivAt_cos root).localInverse cos (-sin root) root hs
  have hleft : ∀ᶠ n in atTop, g (cos (v n)) = v n :=
    hv.eventually ((Complex.hasStrictDerivAt_cos root).eventually_left_inverse hs)
  have hP : ∀ᶠ n in atTop,
      (v n).im ≠ 0 ∧ g (cos (v n)) = v n ∧ (point n (v n)).im ≠ 0 ∧
      CosineProductRepair.denominator (point n (v n)) ≠ 0 ∧
        CosineProductRepair.repair (point n (v n)) = mark := by
    filter_upwards [he, hf, hp.eventually_ne (sub_ne_zero.mpr root_cos_ne_source),
      hden.eventually_ne (one_ne_zero : (1 : ℂ) ≠ 0), eventually_nonreal hv, hleft,
      eventually_gt_atTop (0 : ℕ)] with n hen hfn hpn hdn hnr hln hn
    have hnc : (n : ℂ) ≠ 0 := by exact_mod_cast Nat.ne_zero_of_lt hn
    have hwn : point n (v n) ≠ 0 := by
      intro h
      exact hnr.2 (by rw [h]; simp)
    have hresult := fiber_of_corner hnc hen hpn
      (by simpa only [z, smallCoordinate, parameters] using hdn)
      (by simpa only [fiberEquation, smallCoordinate, parameters, v] using hfn) hwn
    exact ⟨hnr.1, hln, hnr.2, hresult.1, hresult.2⟩
  obtain ⟨N, hN⟩ := eventually_atTop.mp hP
  refine ⟨fun n ↦ point (N + n) (v (N + n)), ?_, ?_⟩
  · intro n m h
    have hn := hN (N + n) (by omega)
    have hm := hN (N + m) (by omega)
    have hc : cos (v (N + n)) = cos (v (N + m)) :=
      (source_point (N + n) (v (N + n))).symm.trans
        ((congrArg source h).trans (source_point (N + m) (v (N + m))))
    have huv : v (N + n) = v (N + m) :=
      hn.2.1.symm.trans ((congrArg g hc).trans hm.2.1)
    have hi : N + n = N + m := index_eq_of_point_eq hn.1 (by simpa only [← huv] using h)
    omega
  · intro n
    exact (hN (N + n) (by omega)).2.2

theorem infinite_nonreal_mark_fiber : Set.Infinite {w : ℂ |
    w.im ≠ 0 ∧ AnalyticAt ℂ CosineProductRepair.repair w ∧ CosineProductRepair.repair w = mark} := by
  obtain ⟨w, hw, h⟩ := exists_nonreal_mark_family
  apply (Set.infinite_range_of_injective hw).mono
  rintro x ⟨n, rfl⟩
  exact ⟨(h n).1, (CosineProductRepair.numerator_entire.analyticAt _).div
    (CosineProductRepair.denominator_entire.analyticAt _) (h n).2.1, (h n).2.2⟩

theorem infinite_nonreal_inverse_mark_fiber : Set.Infinite {w : ℂ |
    w.im ≠ 0 ∧ AnalyticAt ℂ CosineProductRepair.repair w ∧
      CosineProductRepair.repair w = mark⁻¹} := by
  obtain ⟨w, hw, h⟩ := exists_nonreal_mark_family
  apply (Set.infinite_range_of_injective (neg_injective.comp hw)).mono
  rintro x ⟨n, rfl⟩
  have hnum : CosineProductRepair.numerator (w n) = mark * CosineProductRepair.denominator (w n) :=
    (div_eq_iff (h n).2.1).mp (h n).2.2
  have hd : CosineProductRepair.denominator (-w n) ≠ 0 := by
    rw [(CosineProductRepair.neg_coordinates (w n)).2, hnum]
    exact mul_ne_zero mark_ne_zero (h n).2.1
  refine ⟨by simpa using neg_ne_zero.mpr (h n).1,
    (CosineProductRepair.numerator_entire.analyticAt _).div
      (CosineProductRepair.denominator_entire.analyticAt _) hd, ?_⟩
  rw [Function.comp_apply, CosineProductRepair.repair_reciprocal, (h n).2.2]

theorem two_nonreal_cube_root_fibers :
    mark ^ 3 = 1 ∧ mark ≠ 1 ∧ (mark⁻¹) ^ 3 = 1 ∧ mark⁻¹ ≠ 1 ∧ mark ≠ mark⁻¹ ∧
    Set.Infinite {w : ℂ | w.im ≠ 0 ∧ AnalyticAt ℂ CosineProductRepair.repair w ∧
      CosineProductRepair.repair w = mark} ∧
    Set.Infinite {w : ℂ | w.im ≠ 0 ∧ AnalyticAt ℂ CosineProductRepair.repair w ∧
      CosineProductRepair.repair w = mark⁻¹} :=
  ⟨mark_cube, mark_ne_one, inverse_mark_cube, inverse_mark_ne_one, mark_ne_inverse,
    infinite_nonreal_mark_fiber, infinite_nonreal_inverse_mark_fiber⟩

end

end GaloisForLFunctions.HTGeometry.CosineProductNonrealFibers
