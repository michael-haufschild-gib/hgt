import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.BlockDilations.BoundaryError

/-! # Selecting a common light boundary for all binary packet dilations -/

open Finset
namespace GaloisForLFunctions.HTGeometry.BlockDilations
noncomputable section
variable {n : ℕ}

/-- Squared interaction energy in the overlap rows of one seam class. -/
def seamEnergy {L : ℕ} (color : PathLabel n→Fin (L+1)) (p : Fin (L+1)) (u : PathShell n) : ℝ :=
  ∑ q, if color q=p then ∑ l ∈ pathOverlaps q, ((u q)^2+(u l)^2) else 0

/-- One seam class controls every dilation whose outer boundary is
contained in it. The estimate uses the same class for every choice
of internal coefficients. -/
theorem exists_light_seam {L : ℕ} (color : PathLabel n→Fin (L+1)) (u : PathShell n) :
    ∃ p, ((L+1:ℕ):ℝ)*seamEnergy color p u≤84*‖u‖^2 ∧
      ∀ S : Finset (PathLabel n),
        (∀ q∉S, ∀ l∈S, l∈pathOverlaps q → color q=p) →
        boundaryMass u S≤seamEnergy color p u := by
  classical
  have hsum : (∑ p, seamEnergy color p u)≤84*‖u‖^2 := by
    unfold seamEnergy
    rw [sum_comm]
    simpa using path_sum_overlap_squares_le u
  obtain ⟨p,_,hp⟩ := exists_min_image univ (fun p => seamEnergy color p u) univ_nonempty
  refine ⟨p,?_,?_⟩
  · have hh := sum_le_sum (s:=univ) (fun i hi => hp i hi)
    simpa only [sum_const,card_univ,Fintype.card_fin,nsmul_eq_mul] using hh.trans hsum
  · intro S hS
    let W (q : PathLabel n) := if color q=p then ∑ l ∈ pathOverlaps q, ((u q)^2+(u l)^2) else 0
    have hW (q : PathLabel n) : 0≤W q := by dsimp only [W]; split <;> positivity
    apply le_trans _ (sum_le_sum_of_subset_of_nonneg (f:=W) (subset_univ Sᶜ) (fun q _ _ => hW q))
    apply sum_le_sum
    intro q hq
    by_cases hc : color q=p
    · rw [show W q=_ from if_pos hc]
      apply le_trans _ (sum_le_sum_of_subset_of_nonneg (f:=fun l => (u q)^2+(u l)^2)
        (inter_subset_right (s₁:=S) (s₂:=pathOverlaps q)) (fun _ _ _ => by positivity))
      exact sum_le_sum fun l _ => by nlinarith only [sq_nonneg (|u q|-|u l|),sq_abs (u q),sq_abs (u l)]
    · have he : S∩pathOverlaps q=∅ := by
        apply eq_empty_iff_forall_notMem.mpr
        intro l hl
        exact hc (hS q (mem_compl.mp hq) l (mem_inter.mp hl).1 (mem_inter.mp hl).2)
      simp only [he,sum_empty,W,if_neg hc,le_refl]

#print axioms exists_light_seam
end
end GaloisForLFunctions.HTGeometry.BlockDilations
