import GaloisForLFunctions.HTGeometry.CriticalBiprojectiveBoundary
import GaloisForLFunctions.HTGeometry.LaurentSeriesNormalization
import GaloisForLFunctions.HTGeometry.PowerSeriesCriticalDeformation

/-!
# Integrality of the one-parameter critical fibre

The critical fibre over a Laurent-series field has no points outside the power-series lattice.
The proof normalizes both coefficient blocks projectively.  Reduction modulo the uniformizer would
produce a point on the boundary of the pure critical biprojective fibre unless both affine
coordinates remained nonzero.  Boundary exclusion therefore forces every Laurent coefficient to
be integral.
-/

namespace GaloisForLFunctions.HTGeometry

open Polynomial
open scoped LaurentSeries

/-! ## Base change of critical fibres -/

/-- Critical compatibility is functorial under scalar extension. -/
noncomputable def criticalFibreMap
    {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S)
    (m n : ℕ) (U V : R[X]) :
    criticalFibre R m n U V →
      criticalFibre S m n (U.map f) (V.map f) := fun p =>
  ⟨(p.1.1.map f, p.1.2.map f),
    lt_of_le_of_lt Polynomial.degree_map_le p.2.1,
    lt_of_le_of_lt Polynomial.degree_map_le p.2.2.1, by
      have h := Polynomial.map_dvd f p.2.2.2
      simpa [criticalLowProduct] using h⟩

theorem criticalFibreMap_injective
    {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S)
    (hf : Function.Injective f) (m n : ℕ) (U V : R[X]) :
    Function.Injective (criticalFibreMap f m n U V) := by
  intro p q hpq
  apply Subtype.ext
  apply Prod.ext
  · apply Polynomial.map_injective f hf
    exact congrArg (fun z => z.1.1) hpq
  · apply Polynomial.map_injective f hf
    exact congrArg (fun z => z.1.2) hpq

theorem powerSeriesToLaurent_injective (E : Type*) [Field E] :
    Function.Injective (algebraMap (PowerSeries E) E⸨X⸩) :=
  HahnSeries.ofPowerSeries_injective (Γ := ℤ)

noncomputable def powerSeriesCriticalFibreToLaurent
    (E : Type*) [Field E] (m n : ℕ) (u : Fin n → E) (v : Fin m → E) :
    criticalFibre (PowerSeries E) m n
        (X ^ m + powerSeriesRawDeformation E m n u)
        (X ^ n + powerSeriesReciprocalDeformation E m n v) →
      criticalFibre E⸨X⸩ m n
        ((X ^ m + powerSeriesRawDeformation E m n u).map
          (algebraMap (PowerSeries E) E⸨X⸩))
        ((X ^ n + powerSeriesReciprocalDeformation E m n v).map
          (algebraMap (PowerSeries E) E⸨X⸩)) :=
  criticalFibreMap (algebraMap (PowerSeries E) E⸨X⸩) m n _ _

theorem powerSeriesCriticalFibreToLaurent_injective
    (E : Type*) [Field E] (m n : ℕ) (u : Fin n → E) (v : Fin m → E) :
    Function.Injective (powerSeriesCriticalFibreToLaurent E m n u v) :=
  criticalFibreMap_injective _ (powerSeriesToLaurent_injective E) m n _ _

end GaloisForLFunctions.HTGeometry
