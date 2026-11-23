import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.NormalizedPrimeTraceDuality
import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.HeightOneNormalization
import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.RegularFormLattice
import Mathlib.RingTheory.IntegralClosure.GoingDown

/-! The complementary module of the normalized polynomial chart
is its lattice of regular top differential forms. -/

noncomputable section

open KaehlerDifferential GlobalTheory.CechDR GlobalTheory.SchemeCohomology
open scoped GlobalTheory.SchemeCohomology

namespace GlobalTheory.PD

variable {k F E : Type} [Field k] [CharZero k] [Field F] [Field E]
  [Algebra k F] [Algebra k E] [Algebra F E] [IsScalarTower k F E]
  [FiniteDimensional F E] [Algebra.IsSeparable F E]
  (A : Subalgebra k F) [IsNoetherianRing A] [IsIntegrallyClosed A] [IsFractionRing A F]

local notation "B" => integralClosure A E
local notation "C" => ((B).restrictScalars k)

variable [Algebra.Smooth k C]

theorem mem_algebraMap_range_subalgebra {R F : Type*} [CommRing R] [CommRing F]
    [Algebra R F] (S : Subalgebra R F) (y : F) :
    y ∈ (algebraMap S F).range ↔ y ∈ S :=
  ⟨fun ⟨s, hs⟩ => hs ▸ s.property, fun hy => ⟨⟨y, hy⟩, rfl⟩⟩

/-- The trace pairing against the normalized chart takes values in the
polynomial ring exactly for coefficients of regular top forms. -/
theorem normalized_affine_trace_dual_iff {d : ℕ}
    (e : MvPolynomial (Fin d) k ≃ₐ[k] A)
    (bE : Module.Basis (Fin d) E Ω[E⁄k]) (z : E) :
    (∀ b : B, Algebra.trace F E (z * (b : E)) ∈ A) ↔
      z • (ExteriorAlgebra.ιMulti E d fun j => D k E (algebraMap A E (e (MvPolynomial.X j)))) ∈
        omB k E C d := by
  let w : ExteriorDifferentials k E d :=
    z • exteriorPower.ιMulti E d (fun j => D k E (algebraMap A E (e (MvPolynomial.X j))))
  change _ ↔ (w : DR k E) ∈ _
  letI : IsNoetherianRing B := integralClosure.isNoetherianRing (K := F) (L := E)
  letI : IsFractionRing B E := integralClosure.isFractionRing_of_finite_extension F E
  letI : IsIntegrallyClosed B := integralClosure.isIntegrallyClosedOfFiniteExtension F
  constructor
  · intro h
    haveI : IsNoetherianRing C := inferInstanceAs (IsNoetherianRing B)
    haveI : IsIntegrallyClosed C := inferInstanceAs (IsIntegrallyClosed B)
    haveI : IsFractionRing C E := inferInstanceAs (IsFractionRing B E)
    refine mem_omB_of_forall_height_one C d w fun Q _ hQ => ?_
    let P := Q.comap (algebraMap A B)
    letI : P.IsPrime := Ideal.comap_isPrime _ Q
    have hP : P.height = 1 := height_comap_eq_one_of_integral (A := A) (B := B) Q hQ
    let R := primeLocalizationInField F P
    have hlocal (b : B) : Algebra.trace F E (z * (b : E)) ∈ (algebraMap R F).range :=
      ⟨algebraMap A R ⟨_, h b⟩, (IsScalarTower.algebraMap_apply A R F _).symm⟩
    obtain ⟨s, hs, hw⟩ :=
      (trace_pairing_at_chartPrime_iff_regular (F := F) (E := E) A e bE P hP z).mp hlocal Q rfl
    exact ⟨s, hs, (mem_omB_iff_pullback_range C (s • w)).mpr hw⟩
  · intro hw b
    have hr := (mem_omB_iff_pullback_range C w).mp hw
    let t := Algebra.trace F E (z * (b : E))
    apply (mem_algebraMap_range_subalgebra A t).mp
    refine mem_algebraMap_range_of_forall_height_one t fun P _ hP => ?_
    let R := primeLocalizationInField F P
    obtain ⟨a, ha⟩ := (trace_pairing_at_chartPrime_iff_regular (F := F) (E := E) A e bE P hP z).mpr
      (fun Q hQ _ => ⟨1, hQ.ne_top ∘ (Ideal.eq_top_iff_one Q).mpr, by simpa only [one_smul] using hr⟩) b
    obtain ⟨⟨c, s⟩, hcs⟩ := IsLocalization.surj P.primeCompl a
    refine ⟨s, s.property, c, ?_⟩
    simpa only [map_mul, ← IsScalarTower.algebraMap_apply A R F, ha, mul_comm t] using
      congrArg (algebraMap R F) hcs

end GlobalTheory.PD
