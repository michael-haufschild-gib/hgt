import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.SpanningDensity.SignedWeights
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.SpanningDensity.DiagonalPhases

/-! # Pairs of computational configurations with a prescribed energy difference -/
open Matrix
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.ReturnSpacing.PhysicalComponents
open SpanningDensity
noncomputable section
variable {n : ℕ}

/-- Reversing every spin cancels the entire diagonal bond energy. -/
theorem opposite_energy (u : PathShell n) (x : Fin (n+2) → Bool) :
    pathDiagEnergy u x - pathDiagEnergy u (fun i => !(x i)) =
      2 * ∑ i, u (.inl (i,2)) * spin (x i) := by
  have flip_pair (a b : Bool) : spin (!a) * spin (!b) = spin a * spin b := by
    cases a <;> cases b <;> norm_num [spin]
  have hedge (e : Fin (n+1)) :
      zSetSign {e.castSucc,e.succ} (fun i => !(x i)) = zSetSign {e.castSucc,e.succ} x := by
    have he : e.castSucc ≠ e.succ := fun h => by have := congrArg Fin.val h; simp at this
    simp only [zSetSign,Finset.prod_insert (Finset.notMem_singleton.mpr he),Finset.prod_singleton]
    exact flip_pair _ _
  simp only [pathDiagEnergy,hedge,add_sub_add_right_eq_sub,← Finset.sum_sub_distrib,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  simp only [zSetSign_singleton,spin]
  cases x i <;> simp <;> ring

/-- Every target difference up to twice the longitudinal mass is within
four coupling norms of some opposite pair. This error is subextensive. -/
theorem pair_near (u : PathShell n) (y : ℝ)
    (hy : |y| ≤ 2 * ∑ i : Fin (n+2), |u (.inl (i,2))|) :
    ∃ x : Fin (n+2) → Bool,
      |(pathDiagEnergy u x - pathDiagEnergy u (fun i => !(x i))) - y| ≤ 4*‖u‖ := by
  let J (i : Fin (n+2)) := u (.inl (i,2))
  have hJ (i : Fin (n+2)) : |J i| ≤ ‖u‖ := by
    simpa only [J,Real.norm_eq_abs] using PiLp.norm_apply_le u (.inl (i,2))
  have hhalf : |y/2| ≤ ∑ i, |J i| := by
    rw [abs_div,show |(2:ℝ)|=2 from abs_of_pos zero_lt_two]
    exact (div_le_iff₀ zero_lt_two).mpr (by simpa only [J,mul_comm] using hy)
  obtain ⟨v,hv⟩ := realize_signed_energy Finset.univ J ‖u‖ (y/2) (norm_nonneg _) (fun i _ => hJ i) hhalf
  let x (i : Fin (n+2)) := xor (v i.castSucc) (v i.succ)
  have he (i : Fin (n+2)) : spin (x i) = spin (v i.castSucc)*spin (v i.succ) := by
    dsimp only [x]; cases v i.castSucc <;> cases v i.succ <;> norm_num [spin]
  refine ⟨x,?_⟩
  rw [opposite_energy]
  simp_rw [he]
  change |2*(∑ i, J i*(spin (v i.castSucc)*spin (v i.succ)))-y| ≤ _
  rw [abs_le] at hv ⊢
  constructor <;> linarith only [hv.1,hv.2]

end
end GaloisForLFunctions.HTGeometry.ReturnSpacing.PhysicalComponents
