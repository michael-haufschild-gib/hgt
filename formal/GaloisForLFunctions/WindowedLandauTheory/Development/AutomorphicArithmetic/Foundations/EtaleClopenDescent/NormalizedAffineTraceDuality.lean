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
  (A : Type) [CommRing A] [IsDomain A] [IsNoetherianRing A] [IsIntegrallyClosed A]
  [Algebra A F] [IsFractionRing A F] [Algebra A E] [IsScalarTower A F E]
  [Algebra k A] [IsScalarTower k A F] [IsScalarTower k A E]

local notation "B₀" => integralClosure A E
local notation "C" => Subalgebra.restrictScalars k (integralClosure A E)

variable [Algebra.Smooth k ((integralClosure A E).restrictScalars k)]

theorem mem_algebraMap_range_subalgebra {R F : Type*} [CommRing R] [CommRing F]
    [Algebra R F] (S : Subalgebra R F) (y : F) :
    y ∈ (algebraMap S F).range ↔ y ∈ S :=
  ⟨fun ⟨s, hs⟩ => hs ▸ s.property, fun hy => ⟨⟨y, hy⟩, rfl⟩⟩

/-- The trace pairing against the normalized chart takes values in the
polynomial ring exactly for coefficients of regular top forms. -/
theorem normalized_affine_trace_dual_iff {d : ℕ}
    (e : MvPolynomial (Fin d) k ≃ₐ[k] A)
    (bE : Module.Basis (Fin d) E Ω[E⁄k]) (z : E) :
    (∀ b : B₀, Algebra.trace F E (z * (b : E)) ∈ (algebraMap A F).range) ↔
      z • (ExteriorAlgebra.ιMulti E d fun j => D k E (algebraMap A E (e (MvPolynomial.X j)))) ∈
        omB k E C d := by
  let w : ExteriorDifferentials k E d :=
    z • exteriorPower.ιMulti E d (fun j => D k E (algebraMap A E (e (MvPolynomial.X j))))
  change _ ↔ (w : DR k E) ∈ _
  letI : IsNoetherianRing B₀ := integralClosure.isNoetherianRing (K := F) (L := E)
  letI : IsFractionRing B₀ E := integralClosure.isFractionRing_of_finite_extension F E
  letI : IsIntegrallyClosed B₀ := integralClosure.isIntegrallyClosedOfFiniteExtension F
  letI : Algebra.Smooth k B₀ := ‹Algebra.Smooth k C›
  constructor
  · intro h
    letI : FaithfulSMul A B₀ := (faithfulSMul_iff_algebraMap_injective A B₀).mpr (by
      intro a a' h
      apply IsFractionRing.injective A F
      apply (algebraMap F E).injective
      simpa only [← IsScalarTower.algebraMap_apply A B₀ E, IsScalarTower.algebraMap_apply A F E] using
        congrArg (algebraMap B₀ E) h)
    letI : Algebra.HasGoingDown A B₀ := inferInstance
    haveI : IsNoetherianRing C := inferInstanceAs (IsNoetherianRing B₀)
    haveI : IsIntegrallyClosed C := inferInstanceAs (IsIntegrallyClosed B₀)
    haveI : IsFractionRing C E := inferInstanceAs (IsFractionRing B₀ E)
    refine mem_omB_of_forall_height_one C d w fun Q₀ hprime hQ => ?_
    let Q : Ideal B₀ := Q₀
    letI : Q.IsPrime := hprime
    let P := Q.comap (algebraMap A B₀)
    letI : P.IsPrime := Ideal.comap_isPrime _ Q
    have hP : P.height = 1 := height_comap_eq_one_of_integral (A := A) (B := B₀) Q hQ
    let R := primeLocalizationInField F P
    have hlocal (b : B₀) : Algebra.trace F E (z * (b : E)) ∈ (algebraMap R F).range := by
      obtain ⟨a, ha⟩ := h b
      exact ⟨algebraMap A R a, (IsScalarTower.algebraMap_apply A R F a).symm.trans ha⟩
    obtain ⟨s, hs, hw⟩ :=
      (trace_pairing_at_chartPrime_iff_regular (F := F) (E := E) A e bE P hP z).mp hlocal Q rfl
    exact ⟨s, hs, (mem_omB_iff_pullback_range C (s • w)).mpr hw⟩
  · intro hw b
    have hr : w ∈ LinearMap.range (algebraFormPullback k B₀ E d) :=
      (mem_omB_iff_pullback_range C w).mp hw
    let t := Algebra.trace F E (z * (b : E))
    refine mem_algebraMap_range_of_forall_height_one t fun P _ hP => ?_
    let R := primeLocalizationInField F P
    obtain ⟨a, ha⟩ := (trace_pairing_at_chartPrime_iff_regular (F := F) (E := E) A e bE P hP z).mpr
      (fun Q hQ _ => ⟨1, hQ.ne_top ∘ (Ideal.eq_top_iff_one Q).mpr, by simpa only [one_smul] using hr⟩) b
    obtain ⟨⟨c, s⟩, hcs⟩ := IsLocalization.surj P.primeCompl a
    refine ⟨s, s.property, c, ?_⟩
    change algebraMap R F a = t at ha
    rw [mul_comm]
    have hcomp (b : A) : algebraMap R F (algebraMap A R b) = algebraMap A F b :=
      (IsScalarTower.algebraMap_apply A R F b).symm
    have hmul : a * algebraMap A R (s : A) = algebraMap A R c := hcs
    calc
      t * algebraMap A F (s : A) =
          algebraMap R F a * algebraMap R F (algebraMap A R (s : A)) := by rw [ha, hcomp]
      _ = algebraMap R F (a * algebraMap A R (s : A)) := (map_mul _ _ _).symm
      _ = algebraMap R F (algebraMap A R c) := congrArg (algebraMap R F) hmul
      _ = algebraMap A F c := hcomp c

end GlobalTheory.PD
