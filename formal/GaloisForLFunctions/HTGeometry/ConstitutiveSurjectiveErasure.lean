import GaloisForLFunctions.HTGeometry.ConstitutiveGammaResponseLifetime
import Mathlib.LinearAlgebra.FiniteDimensional.Basic

/-!
# Surjective erasure forces infinite dimensionality

A surjective linear endomorphism that kills a nonzero law class cannot act on a finite-dimensional
carrier.  The fixed-corona Gamma response is surjective and kills every nonzero Bockstein class
strictly after its exact lifetime, so its full death mechanism has no faithful finite-dimensional
linear realization.

No computation proof, project postulate, or unproved source premise is used.
-/

namespace GaloisForLFunctions.HTGeometry

open _root_.RHTower

noncomputable section

/-- A same-carrier surjective linear response with nonzero erasure forces infinite dimension. -/
theorem constitutiveSurjectiveErasure_not_finiteDimensional
    {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (T : V →ₗ[K] V) (hT : Function.Surjective T)
    {x : V} (hx : x ≠ 0) (hkill : T x = 0) :
    ¬ FiniteDimensional K V := by
  intro hfinite
  letI : FiniteDimensional K V := hfinite
  have hinjective : Function.Injective T := LinearMap.injective_iff_surjective.mpr hT
  exact hx (hinjective (hkill.trans T.map_zero.symm))

/-- Every genuine Gamma-Bockstein death event forces the fixed prime corona to be
infinite-dimensional. -/
theorem constitutiveGammaCorona_not_finiteDimensional_of_bockstein_death
    (s : NNReal) {t : ℝ} (ht : t ≠ 0) (hdeath : |t| / 2 < (s : ℝ)) :
    ¬ FiniteDimensional ℂ ConstitutiveGammaCorona := by
  have hnonzero : primeGammaCofinalBockstein t ≠ 0 := by
    intro hzero
    have hcritical := constitutiveGammaBockstein_critical_survival ht
    rw [hzero, map_zero] at hcritical
    exact hcritical rfl
  have hkill : constitutiveGammaCoronaResponse s (primeGammaCofinalBockstein t) = 0 :=
    (constitutiveGammaBockstein_death_iff s ht).2 hdeath
  exact constitutiveSurjectiveErasure_not_finiteDimensional
    (constitutiveGammaCoronaResponse s)
    (constitutiveGammaCoronaResponse_surjective s) hnonzero hkill

/-- The literal fixed prime corona supporting Gamma-Bockstein lifetime is not finite-dimensional. -/
theorem constitutiveGammaCorona_not_finiteDimensional :
    ¬ FiniteDimensional ℂ ConstitutiveGammaCorona := by
  exact constitutiveGammaCorona_not_finiteDimensional_of_bockstein_death
    (1 : NNReal) (t := (1 : ℝ)) one_ne_zero (by norm_num)

end


end GaloisForLFunctions.HTGeometry
