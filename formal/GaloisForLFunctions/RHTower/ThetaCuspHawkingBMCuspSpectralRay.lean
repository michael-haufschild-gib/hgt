import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMCuspPacketApproximation

/-!
The actual modular cusp ray excludes bounded left inversion, by a constructed unit sequence.
-/

open MeasureTheory Set Filter Topology
namespace RHTower.D4BMModularCore
noncomputable section

/-- The actual modular operator has no bounded left inverse at any point of
its constructed cusp approximate-spectral ray. -/
theorem energyOperator_cusp_no_bounded_left_inverse (tau : ℝ) :
    ¬ ∃ R : Space →L[ℂ] Space, ∀ x : energyOperator.domain,
      R (energyOperator x-((5/4:ℂ)+(tau:ℂ)^(2 : ℕ)) • (x : Space)) = (x : Space) := by
  rintro ⟨R,hR⟩
  have hl := (cuspApproximateVector_residual_tendsto tau).const_mul ‖R‖
  have hb : (1:ℝ) ≤ ‖R‖*0 := ge_of_tendsto' hl (fun n => by
    have hn := R.le_opNorm (energyOperator (cuspApproximateVector tau n)-
      ((5/4:ℂ)+(tau:ℂ)^(2 : ℕ)) • (cuspApproximateVector tau n : Space))
    rw [hR,cuspApproximateVector_norm] at hn
    exact hn)
  norm_num at hb

/-- Every real point at or above the actual cusp threshold is excluded from
the bounded-left-inverse set, including the endpoint. -/
theorem energyOperator_cusp_ray_no_bounded_left_inverse :
    ∀ lam : ℝ, 5/4 ≤ lam →
      ¬ ∃ R : Space →L[ℂ] Space, ∀ x : energyOperator.domain,
        R (energyOperator x-(lam:ℂ) • (x : Space)) = (x : Space) := by
  intro lam hlam
  have hs : (5/4:ℂ)+(Real.sqrt (lam-5/4):ℂ)^(2 : ℕ) = (lam:ℂ) := by
    rw [← Complex.ofReal_pow,Real.sq_sqrt (sub_nonneg.mpr hlam)]
    push_cast
    ring
  simpa only [hs] using energyOperator_cusp_no_bounded_left_inverse (Real.sqrt (lam-5/4))

/-- At the critical real part of doubled time rate, the exact physical
quadratic shift meets the constructed modular cusp ray. -/
theorem energyOperator_critical_time_no_bounded_left_inverse (tau : ℝ) :
    ¬ ∃ R : Space →L[ℂ] Space, ∀ x : energyOperator.domain,
      R (energyOperator x-
        (1-((-3/2+(tau:ℂ)*Complex.I)+1)*((-3/2+(tau:ℂ)*Complex.I)+2)) •
          (x : Space)) = (x : Space) := by
  have hs : (1-((-3/2+(tau:ℂ)*Complex.I)+1)*((-3/2+(tau:ℂ)*Complex.I)+2)) =
      (5/4:ℂ)+(tau:ℂ)^(2 : ℕ) := by
    linear_combination -(tau:ℂ)^(2 : ℕ)*Complex.I_sq
  rw [hs]
  exact energyOperator_cusp_no_bounded_left_inverse tau

end
end RHTower.D4BMModularCore
