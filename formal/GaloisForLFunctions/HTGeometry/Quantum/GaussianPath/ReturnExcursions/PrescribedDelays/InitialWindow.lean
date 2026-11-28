import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.PrescribedTimes.ShortWindows.AllDelays

/-! # Polynomial observation windows inside the original first excursion -/

open MeasureTheory Filter Set
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.ReturnExcursions.PrescribedDelays
open PrescribedTimes ShortWindows
noncomputable section

private theorem cube_le_travel (N : ℕ) (hh : 64 ≤ N.sqrt) :
    2*(N:ℝ)^3 ≤ (2:ℝ)^(N-10*N.sqrt) := by
  let h := N.sqrt
  have hN : N+1 ≤ (h+1)^2 := by rw [pow_two]; exact Nat.lt_succ_sqrt N
  have hn : N ≤ 2^h := (Nat.le_succ N).trans (hN.trans
    ((by omega : (h+1)^2 ≤ 64*(h+1)^2).trans (dimension_dominates_speed hh)))
  have hsq : h*h ≤ N := Nat.sqrt_le N
  have hmul := Nat.mul_le_mul_right h (show 14 ≤ h by exact (by decide : 14≤64).trans hh)
  have he : h*3+1 ≤ N-10*h := by dsimp only [h] at *; omega
  have hb := Nat.mul_le_mul_left 2 (Nat.pow_le_pow_left hn 3)
  rw [←pow_mul,Nat.mul_comm 2 ((2:ℕ)^(h*3)),←pow_succ] at hb
  exact_mod_cast hb.trans (Nat.pow_le_pow_right (by decide : 0<2) he)

/-- From the actual first crossing, all budgets through half the plateau
threshold miss the entire initial interval of length twice K cubed. -/
theorem initial_cubic_window :
    ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ᶠ k : ℕ in atTop,
      let K := k+3
      let P := nearHilbertContinuousCircuitBudget K
      ∀ s ≤ P/2, prefixPoint k ω ∉ hitWindow (k+1) P s 0 (2*(K:ℝ)^3) := by
  obtain ⟨_,hfirst⟩ := gaussian_initial_crossing_short_return_tradeoff
  filter_upwards [hfirst] with ω hf
  filter_upwards [hf,eventually_ge_atTop (64*64)] with k hk hsize
  intro K P s hs
  let x := prefixPoint k ω
  let H : selfAdjoint (Matrix (Fin K→Bool) (Fin K→Bool) ℂ) :=
    ⟨pathHamiltonian (pathPauliDisorderShell ω (k+1)),isSelfAdjoint_pathHamiltonian _⟩
  have hd (j : ℕ) (t : ℝ) : pathGateDistance (k+1) j x t=orbitCircuitDistance H j t := by
    unfold pathGateDistance orbitCircuitDistance
    rw [show numberedGenerator (k+1) x=H.val from numberedGenerator_shell _]
  obtain ⟨σ,hσ,he,hbefore,_,hnext⟩ := hk
  have hpos : 0 ≤ σ := (show 0 ≤ (2:ℝ)^(K-10*K.sqrt) by positivity).trans hσ.le
  have hor := crossingOrigin_eq_of_first hpos ((hd P σ).trans he) (fun t ht => (hd P t).trans_lt (hbefore t ht))
  obtain ⟨v,hv,hmin,_⟩ := hnext s hs
  rintro ⟨t,ht,htc⟩
  change t ∈ Icc (crossingOrigin (k+1) P (9/80) x+0) _ at ht
  rw [hor,add_zero] at ht
  have hvt := hmin.2 ⟨ht.1,(hasProjectiveCircuitApproximation_iff_infDist _ s _).mpr ((hd s t).symm.trans_le htc)⟩
  have hB := cube_le_travel K (Nat.le_sqrt.mpr (by dsimp only [K]; omega))
  exact hv.not_ge (hvt.trans (ht.2.trans (add_le_add le_rfl hB)))

#print axioms initial_cubic_window
end
end GaloisForLFunctions.HTGeometry.ReturnExcursions.PrescribedDelays
