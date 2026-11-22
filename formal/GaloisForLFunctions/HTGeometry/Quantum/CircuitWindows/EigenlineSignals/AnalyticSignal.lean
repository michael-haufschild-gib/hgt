import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.SpanningDensity.CutEcho
import GaloisForLFunctions.HTGeometry.AnalyticImageFinitenessComplex

/-! # Local finiteness of the zeros of a witnessed Heisenberg signal -/
open Matrix Set
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.EigenlineSignals
noncomputable section
private abbrev Reg (N : ℕ) := Matrix (Fin N→Bool) (Fin N→Bool) ℂ

theorem analytic_evolution {N : ℕ} (H : Reg N) (t : ℝ) :
    AnalyticAt ℝ (unitaryEvolution H) t := by
  letI : CStarAlgebra (Reg N) := {}
  letI : NormedAlgebra ℚ (Reg N) := NormedAlgebra.restrictScalars ℚ ℂ _
  exact (NormedSpace.exp_analytic (𝕂:=ℝ) _).comp
    (show AnalyticAt ℝ (fun s : ℝ => s • ((-Complex.I) • H)) t from analyticAt_id.smul analyticAt_const)

theorem adjoint_evolution {N : ℕ} (H : selfAdjoint (Reg N)) (t : ℝ) :
    unitaryEvolution H.val (-t)=star (unitaryEvolution H.val t) := by
  let U (s : ℝ) : Matrix.unitaryGroup (Fin N→Bool) ℂ := ⟨_,unitaryEvolution_mem_unitary H.property s⟩
  have h : U (-t)*U t=1 := by
    apply Subtype.ext
    simpa only [U,Submonoid.coe_mul,Submonoid.coe_one,zero_sub,unitaryEvolution,zero_smul,
      NormedSpace.exp_zero] using unitaryEvolution_sub_mul H 0 t
  exact congrArg Subtype.val (eq_inv_of_mul_eq_one_left h)

/-- Once a pair of probes transmits at any date, the dates at which the
same probes commute are finite on each compact interval. -/
theorem finite_silent_dates {N : ℕ} (H : selfAdjoint (Reg N)) (A B : Reg N) {u : ℝ}
    (h : ¬Commute (star (unitaryEvolution H.val u)*A*unitaryEvolution H.val u) B) (a b : ℝ) :
    (Icc a b ∩ {t | Commute (star (unitaryEvolution H.val t)*A*unitaryEvolution H.val t) B}).Finite := by
  let Y (t : ℝ) := unitaryEvolution H.val (-t)*A*unitaryEvolution H.val t
  let X (t : ℝ) := Y t*B-B*Y t
  have hne : X u ≠ 0 := by
    intro hz
    apply h
    change (star (unitaryEvolution H.val u)*A*unitaryEvolution H.val u)*B=
      B*(star (unitaryEvolution H.val u)*A*unitaryEvolution H.val u)
    simpa only [Y,adjoint_evolution] using sub_eq_zero.mp hz
  obtain ⟨i,j,hij⟩ : ∃ i j, X u i j ≠ 0 := by
    by_contra! hh
    exact hne (Matrix.ext fun i j => hh i j)
  let e : Reg N →ₗ[ℝ] ℂ :=
    { toFun := fun M => M i j
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  let L := e.mkContinuous 1 fun M => (norm_entry_le_l2_opNorm M i j).trans_eq (one_mul ‖M‖).symm
  have hy (s : ℝ) : AnalyticAt ℝ Y s :=
    (((analytic_evolution H.val (-s)).comp analyticAt_id.neg).mul analyticAt_const).mul (analytic_evolution H.val s)
  have hx (s : ℝ) : AnalyticAt ℝ X s :=
    ((hy s).mul analyticAt_const).sub (analyticAt_const.mul (hy s))
  have hf := finite_zeros_of_analyticOnNhd_complex isPreconnected_univ
    (L.comp_analyticOnNhd (show AnalyticOnNhd ℝ X univ from fun t _ => hx t))
    (mem_univ u) hij (isCompact_Icc (a:=a) (b:=b)) (subset_univ _)
  refine hf.subset fun t ht => ⟨ht.1,?_⟩
  have hzero : X t=0 := by
    dsimp only [X,Y]; rw [adjoint_evolution H,ht.2.eq,sub_self]
  change L (X t)=0
  rw [hzero,map_zero]

end
end GaloisForLFunctions.HTGeometry.EigenlineSignals
