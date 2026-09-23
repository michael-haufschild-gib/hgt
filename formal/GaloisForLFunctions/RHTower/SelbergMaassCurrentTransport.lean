import GaloisForLFunctions.RHTower.SelbergMaassPairPhaseEnergy

/-!
# Actual modular transport of Maass pair and phase currents

The original quotient-form pullback and actual Möbius differential transport every
source derivative and both pair-current indices. Finite quotient permutations then
give exact covariance of the total phase current and directional pair energy.
The full reciprocal-square Jacobian is retained. No quotient period vanishing or
global quarter comparison is asserted.
-/


open Complex Set Filter Topology UpperHalfPlane ModularGroup
open scoped MatrixGroups ContDiff
namespace GaloisForLFunctions.RHTower.SelbergMaassCurrentTransport
open SelbergMaassCongruenceTrace SelbergMaassTraceEnergy SelbergMaassCuspTransport
  SelbergMaassSourceCurrents SelbergMaassPairPhaseEnergy
noncomputable section

variable (N : ℕ) {lam : ℝ}
    (f : MaassCuspEigenform (realImage (CongruenceSubgroup.Gamma (N + 1))) lam)

/-- The literal source fields transform by the actual right quotient permutation. -/
theorem field_modular (q : Deck N) (A : SL2Z) (z : ℍ) :
    field N f q (A • z : ℍ) = field N f (q * QuotientGroup.mk A) (z : ℂ) := by
  simp only [field, Function.comp_apply, ofComplex_apply, quotientForm_mul, translate_apply]

/-- Actual directional derivatives retain the full Möbius differential and source permutation. -/
theorem field_dir_modular (q : Deck N) (A : SL2Z) (z : ℍ) (v : ℂ) :
    dir ((1 / (denom A z) ^ (2 : ℕ)) * v) (field N f q) (A • z : ℍ) =
      dir v (field N f (q * QuotientGroup.mk A)) (z : ℂ) := by
  let G : ℂ → ℂ := fun w => ((A • ofComplex w : ℍ) : ℂ)
  have hG : HasFDerivAt G (UpperHalfPlane.smulFDeriv (A : GL (Fin 2) ℝ) (z : ℂ)) (z : ℂ) :=
    (UpperHalfPlane.hasStrictFDerivAt_smul (A : GL (Fin 2) ℝ) z).hasFDerivAt
  have hF : DifferentiableAt ℝ (field N f q) (G (z : ℂ)) := by
    simpa only [G, ofComplex_apply] using
      (field_smooth N f q (A • z)).differentiableAt (by norm_num)
  have he : field N f q ∘ G = field N f (q * QuotientGroup.mk A) := by
    funext w
    simp only [Function.comp_apply, G, field, quotientForm_mul,
      translate_apply, ofComplex_apply]
  have hc := hF.hasFDerivAt.comp (z : ℂ) hG
  rw [he] at hc
  have h := congrArg (fun L => L v) hc.fderiv
  have hj : UpperHalfPlane.smulFDeriv (A : GL (Fin 2) ℝ) (z : ℂ) v =
      (1 / (denom A z) ^ (2 : ℕ)) * v := by
    simp [UpperHalfPlane.smulFDeriv, UpperHalfPlane.σ, mul_comm]
  simpa only [ContinuousLinearMap.comp_apply, G, ofComplex_apply, hj, dir] using h.symm

/-- Every original complex pair current transforms with the actual differential and both source indices. -/
theorem bracket_modular (q r : Deck N) (A : SL2Z) (z : ℍ) (v : ℂ) :
    bracket (field N f q) (field N f r) ((1 / (denom A z) ^ (2 : ℕ)) * v) (A • z : ℍ) =
      bracket (field N f (q * QuotientGroup.mk A))
        (field N f (r * QuotientGroup.mk A)) v (z : ℂ) := by
  simp only [bracket, field_modular, field_dir_modular]

/-- The total phase-current one-form descends with its full Möbius differential. -/
theorem phase_current_modular (A : SL2Z) (z : ℍ) (v : ℂ) :
    phaseCurrent N f ((1 / (denom A z) ^ (2 : ℕ)) * v) (A • z : ℍ) =
      phaseCurrent N f v (z : ℂ) := by
  unfold phaseCurrent
  simp_rw [field_modular, field_dir_modular]
  exact Equiv.sum_comp (Equiv.mulRight (QuotientGroup.mk A : Deck N))
    (fun q : Deck N => (dir v (field N f q) (z : ℂ) * (starRingEnd ℂ) (field N f q (z : ℂ))).im)

/-- The full pair-current directional energy is invariant under simultaneous point and tangent transport. -/
theorem pair_energy_modular (A : SL2Z) (z : ℍ) (v : ℂ) :
    pairEnergy N f ((1 / (denom A z) ^ (2 : ℕ)) * v) (A • z : ℍ) =
      pairEnergy N f v (z : ℂ) := by
  unfold pairEnergy
  simp_rw [bracket_modular]
  congr 1
  have hr (q : Deck N) :
      (∑ r : Deck N, normSq (bracket (field N f q)
        (field N f (r * QuotientGroup.mk A)) v (z : ℂ))) =
      ∑ r : Deck N, normSq (bracket (field N f q) (field N f r) v (z : ℂ)) :=
    Equiv.sum_comp (Equiv.mulRight (QuotientGroup.mk A : Deck N))
      (fun r : Deck N => normSq (bracket (field N f q) (field N f r) v (z : ℂ)))
  simp_rw [hr]
  exact Equiv.sum_comp (Equiv.mulRight (QuotientGroup.mk A : Deck N))
    (fun q : Deck N => ∑ r : Deck N, normSq (bracket (field N f q) (field N f r) v (z : ℂ)))

end
end GaloisForLFunctions.RHTower.SelbergMaassCurrentTransport
