import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.CompositionBoundary.Realization
import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.CompositionBoundary.ClockTransfer
import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.CompositionBoundary.Regularity

/-! # The isometry line as a physical natural boundary -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.ShellMixing

open Filter Topology U0 U0NaturalBoundary

/-- The absolutely convergent boundary values belong to a response continuous on the closed half-plane. -/
theorem lacunary_response_continuous (p : Nat.Primes) :
    ContinuousOn (compositionResponse (lacunaryOmission p)) {s : ℂ | 1/2 ≤ s.re} :=
  compositionResponse_continuous_from _ ((lacunary_split_iff p ((1/2:ℝ):ℂ)).mpr le_rfl)

/-- Every height on the critical line obstructs continuation from the interior for this one physical wave. -/
theorem lacunary_response_natural_boundary (p : Nat.Primes) (s : ℂ) (h : s.re = 1/2) :
    ¬ ContinuesAcross (compositionResponse (lacunaryOmission p)) compositionRight s := by
  rintro ⟨g,hg,he⟩
  apply clock_natural_boundary p s h
  refine ⟨g,hg,?_⟩
  filter_upwards [he,self_mem_nhdsWithin] with z hz hr
  have hh : 1/2 < z.re := hr
  exact hz.trans ((lacunary_response_eq p hh.le).trans (congrArg u0 (compositionClock_heat p z)))

/-- For one prime-supported wave, finite split mass together with failure of local analytic continuation characterizes global split isometry. -/
theorem finite_singular_iff_split_isometric (p : Nat.Primes) (s : ℂ) :
    (finiteSplit (lacunaryOmission p) s ∧
      ¬ ContinuesAcross (compositionResponse (lacunaryOmission p)) compositionRight s) ↔
      ∃ T : Gas →ₗᵢ[ℂ] PairGas, ∀ f x, T f x = split s f x := by
  rw [split_isometric_iff]
  constructor
  · rintro ⟨hf,hn⟩
    have hl := (lacunary_split_iff p s).mp hf
    refine le_antisymm (le_of_not_gt fun hh => hn ?_) hl
    exact ⟨_,compositionResponse_analytic_at _ ((splitAbscissa_bounds _).2.trans_lt hh),Filter.Eventually.of_forall (fun _ => rfl)⟩
  · intro h
    exact ⟨(lacunary_split_iff p s).mpr h.ge,lacunary_response_natural_boundary p s h⟩

#print axioms lacunary_response_continuous
#print axioms lacunary_response_natural_boundary
#print axioms finite_singular_iff_split_isometric

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.ShellMixing
