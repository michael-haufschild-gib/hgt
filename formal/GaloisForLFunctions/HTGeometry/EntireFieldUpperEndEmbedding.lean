import GaloisForLFunctions.HTGeometry.EntireFunctionField
import GaloisForLFunctions.HTGeometry.FractionFieldFunctorial
import GaloisForLFunctions.HTGeometry.UpperEndMeromorphicField

/-!
# Restricting global meromorphic fractions to the complex upper end

An entire function defines an analytic germ at the complex upper end.  This restriction is
faithful by the identity theorem, hence extends injectively from the entire-function ring to its
fraction field.  The resulting embedding is the carrier map needed to use global meromorphic
coefficient fields in upper-end Dirichlet-series identities.
-/

namespace GaloisForLFunctions.HTGeometry

open Filter Set Topology

noncomputable section

/-- Restriction of an entire function to its analytic germ at the complex upper end. -/
def entireToUpperEndAnalytic : entireSubring ℂ →+* upperEndAnalyticSubring where
  toFun f :=
    ⟨Germ.coeRingHom upperEndFilter (f : ℂ → ℂ),
      ⟨(f : ℂ → ℂ), 0, f.2.mono (subset_univ (upperTail 0)), rfl⟩⟩
  map_one' := by
    apply Subtype.ext
    change Germ.coeRingHom upperEndFilter (1 : ℂ → ℂ) = 1
    exact map_one (Germ.coeRingHom upperEndFilter)
  map_mul' f g := by
    apply Subtype.ext
    change Germ.coeRingHom upperEndFilter ((f : ℂ → ℂ) * (g : ℂ → ℂ)) = _
    exact map_mul (Germ.coeRingHom upperEndFilter) (f : ℂ → ℂ) (g : ℂ → ℂ)
  map_zero' := by
    apply Subtype.ext
    change Germ.coeRingHom upperEndFilter (0 : ℂ → ℂ) = 0
    exact map_zero (Germ.coeRingHom upperEndFilter)
  map_add' f g := by
    apply Subtype.ext
    change Germ.coeRingHom upperEndFilter ((f : ℂ → ℂ) + (g : ℂ → ℂ)) = _
    exact map_add (Germ.coeRingHom upperEndFilter) (f : ℂ → ℂ) (g : ℂ → ℂ)

@[simp]
theorem entireToUpperEndAnalytic_coe (f : entireSubring ℂ) :
    ((entireToUpperEndAnalytic f : upperEndAnalyticSubring) : Germ upperEndFilter ℂ) =
      Germ.coeRingHom upperEndFilter (f : ℂ → ℂ) :=
  rfl

/-- Restriction to the upper end is faithful on entire functions. -/
theorem entireToUpperEndAnalytic_injective : Function.Injective entireToUpperEndAnalytic := by
  intro f g hfg
  apply Subtype.ext
  have hgerm := congrArg (fun h : upperEndAnalyticSubring =>
    (h : Germ upperEndFilter ℂ)) hfg
  rw [entireToUpperEndAnalytic_coe, entireToUpperEndAnalytic_coe] at hgerm
  change ((f : ℂ → ℂ) : Germ upperEndFilter ℂ) =
    ((g : ℂ → ℂ) : Germ upperEndFilter ℂ) at hgerm
  rw [Germ.coe_eq] at hgerm
  change ∀ᶠ z in upperEndFilter, (f : ℂ → ℂ) z = (g : ℂ → ℂ) z at hgerm
  rw [upperEndFilter_basis.eventually_iff] at hgerm
  obtain ⟨H, -, hH⟩ := hgerm
  let z₀ : ℂ := ⟨0, H + 1⟩
  have hz₀ : z₀ ∈ upperTail H := by
    simp only [upperTail, mem_setOf_eq, z₀]
    linarith
  have hlocal : (f : ℂ → ℂ) =ᶠ[𝓝 z₀] (g : ℂ → ℂ) :=
    Filter.mem_of_superset ((upperTail_isOpen H).mem_nhds hz₀) hH
  exact f.2.eq_of_eventuallyEq g.2 hlocal

local instance entireUpperEndDomain : IsDomain upperEndAnalyticSubring :=
  isDomain_upperEndAnalyticSubring

/-- Faithful restriction of global meromorphic fractions to the upper-end meromorphic field. -/
def entireFieldToUpperEndMero : EntireField ℂ →+* upperEndMeroField :=
  fracLift entireToUpperEndAnalytic_injective

theorem entireFieldToUpperEndMero_injective :
    Function.Injective entireFieldToUpperEndMero :=
  fracLift_injective entireToUpperEndAnalytic_injective

@[simp]
theorem entireFieldToUpperEndMero_algebraMap (f : entireSubring ℂ) :
    entireFieldToUpperEndMero (algebraMap (entireSubring ℂ) (EntireField ℂ) f) =
      algebraMap upperEndAnalyticSubring upperEndMeroField (entireToUpperEndAnalytic f) :=
  fracLift_algebraMap entireToUpperEndAnalytic_injective f

@[simp]
theorem entireFieldToUpperEndMero_ofEntire (f : ℂ → ℂ)
    (hf : AnalyticOnNhd ℂ f Set.univ) :
    entireFieldToUpperEndMero (ofEntire f hf) =
      algebraMap upperEndAnalyticSubring upperEndMeroField
        (entireToUpperEndAnalytic ⟨f, hf⟩) := by
  exact entireFieldToUpperEndMero_algebraMap ⟨f, hf⟩

end

end GaloisForLFunctions.HTGeometry
