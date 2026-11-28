import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.ReturnExcursions.AngularWindings.PhysicalTubes.UnitaryMidpoint

/-! # Equality in the squared midpoint bound -/

open Matrix Finset Complex
open scoped Matrix.Norms.L2Operator ComplexConjugate
namespace GaloisForLFunctions.HTGeometry.ReturnExcursions.AngularWindings.PhysicalTubes
open private chord_sum from
  GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.ReturnExcursions.AngularWindings.PhysicalTubes.UnitaryMidpoint
noncomputable section
variable {I : Type*} [Fintype I] [DecidableEq I]
private abbrev Mat (I : Type*) := Matrix I I ℂ

/-- At an active midpoint eigenphase, the eigenvector vanishes wherever the
two diagonal endpoint phases differ from the midpoint. -/
theorem active_coordinate {W : unitary (Mat I)} {u : I → ℂ} (hu : ∀ i, ‖u i‖=1)
    {ε : ℝ} (hcut : ε^2<2) (hp : ‖diagonal u-W.val‖≤ε)
    (hm : ‖diagonal (fun i => conj (u i))-W.val‖≤ε)
    {z : ℂ} (hz : ‖z‖=1) (hd : ‖1-z‖=ε) {v : I → ℂ} (he : W.val *ᵥ v=z • v) :
    ∀ j, v j≠0 → (u j).re=1 := by
  classical
  have hsq := congrArg (fun t : ℝ => t^2) hd
  change ‖1-z‖^2=ε^2 at hsq
  rw [Complex.sq_norm,Complex.normSq_sub] at hsq
  simp only [map_one,Complex.normSq_eq_norm_sq,hz,one_pow,one_mul,Complex.conj_re] at hsq
  have hpos : 0<z.re := by linarith only [hsq,hcut]
  have hle (i : I) : (u i).re≤1 := (le_abs_self _).trans ((Complex.abs_re_le_norm _).trans_eq (hu i))
  have hch (i : I) : ‖u i-z‖^2+‖conj (u i)-z‖^2=4-4*(u i).re*z.re := by
    rw [Complex.sq_norm,Complex.sq_norm,Complex.normSq_sub,Complex.normSq_sub,Complex.normSq_conj]
    simp only [Complex.normSq_eq_norm_sq,hz,hu,one_pow,Complex.mul_re,Complex.conj_im,Complex.conj_re]
    ring
  have hbase (i : I) : 2*ε^2≤‖u i-z‖^2+‖conj (u i)-z‖^2 := by
    rw [hch]
    linarith only [mul_nonneg (sub_nonneg.mpr (hle i)) hpos.le,hsq]
  intro j hj
  by_contra h
  have hgt : 2*ε^2<‖u j-z‖^2+‖conj (u j)-z‖^2 := by
    rw [hch]
    linarith only [mul_pos (sub_pos.mpr ((hle j).lt_of_ne h)) hpos,hsq]
  have hs : (∑ i, (2*ε^2)*‖v i‖^2) < ∑ i, (‖u i-z‖^2+‖conj (u i)-z‖^2)*‖v i‖^2 := by
    apply sum_lt_sum (fun i _ => mul_le_mul_of_nonneg_right (hbase i) (sq_nonneg _))
    exact ⟨j,mem_univ j,mul_lt_mul_of_pos_right hgt (sq_pos_of_pos (norm_pos_iff.mpr hj))⟩
  simp only [add_mul,sum_add_distrib,←mul_sum] at hs
  linarith only [hs,chord_sum W u he hp,chord_sum W (fun i => conj (u i)) he hm]

/-- If at most one coordinate is stationary, all active midpoint eigenvectors
have the same eigenvalue, the circuit's diagonal entry at that coordinate. -/
theorem active_phase_unique {W : unitary (Mat I)} {u : I → ℂ} (hu : ∀ i, ‖u i‖=1)
    (hsingle : ∀ i j, (u i).re=1 → (u j).re=1 → i=j)
    {ε : ℝ} (hcut : ε^2<2) (hp : ‖diagonal u-W.val‖≤ε)
    (hm : ‖diagonal (fun i => conj (u i))-W.val‖≤ε)
    {z w : ℂ} (hz : ‖z‖=1) (hw : ‖w‖=1) (hdz : ‖1-z‖=ε) (hdw : ‖1-w‖=ε)
    {v a : I → ℂ} (hv : v≠0) (ha : a≠0) (he : W.val *ᵥ v=z • v)
    (hf : W.val *ᵥ a=w • a) : z=w := by
  classical
  obtain ⟨j,hj⟩ : ∃ j, v j≠0 := by by_contra! h; exact hv (funext h)
  have hstat := active_coordinate hu hcut hp hm hz hdz he j hj
  have diag_of_active {b : I → ℂ} {c : ℂ} (hb : b≠0) (hc : ‖c‖=1) (hd : ‖1-c‖=ε)
      (h : W.val *ᵥ b=c • b) : W.val j j=c := by
    have hzero (i : I) (hne : i≠j) : b i=0 := by
      by_contra hi
      exact hne (hsingle i j (active_coordinate hu hcut hp hm hc hd h i hi) hstat)
    have hbj : b j≠0 := by
      intro h0
      apply hb
      funext i
      by_cases hi : i=j
      · exact hi ▸ h0
      · exact hzero i hi
    have hcomp := congrFun h j
    change (∑ i, W.val j i*b i)=c*b j at hcomp
    rw [sum_eq_single j (fun i _ hi => by rw [hzero i hi,mul_zero]) (by simp)] at hcomp
    exact mul_right_cancel₀ hbj hcomp
  exact (diag_of_active hv hz hdz he).symm.trans (diag_of_active ha hw hdw hf)

#print axioms active_phase_unique
end
end GaloisForLFunctions.HTGeometry.ReturnExcursions.AngularWindings.PhysicalTubes
