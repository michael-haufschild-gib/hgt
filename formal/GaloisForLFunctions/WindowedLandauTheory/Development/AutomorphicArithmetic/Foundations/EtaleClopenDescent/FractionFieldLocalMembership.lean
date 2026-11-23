import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.NormalHeightOneLattice
import Mathlib.RingTheory.LocalProperties.Submodule

/-! Denominators in fraction fields can be tested at maximal ideals,
or at height-one primes of a normal Noetherian domain. -/

noncomputable section

namespace GlobalTheory.PD

variable {A F : Type*} [CommRing A] [Field F] [Algebra A F]

/-- If a fraction has a denominator outside each maximal ideal, it
belongs to the original ring. -/
theorem mem_algebraMap_range_of_forall_maximal (x : F)
    (h : ∀ (P : Ideal A) [P.IsMaximal],
      ∃ s : A, s ∉ P ∧ ∃ a : A, algebraMap A F s * x = algebraMap A F a) :
    x ∈ (algebraMap A F).range := by
  let N := LinearMap.range (Algebra.linearMap A F)
  have hN : x ∈ N := by
    refine Submodule.mem_of_localization_maximal (R := A) (fun P _ => LocalizedModule P.primeCompl F)
      (fun P _ => LocalizedModule.mkLinearMap P.primeCompl F) x N (fun P _ => ?_)
    obtain ⟨s, hs, a, ha⟩ := h P
    let f := LocalizedModule.mkLinearMap P.primeCompl F
    let t : P.primeCompl := ⟨s, hs⟩
    refine ⟨algebraMap A F a, ⟨a, rfl⟩, t, ?_⟩
    change IsLocalizedModule.mk' f (algebraMap A F a) t = f x
    rw [← IsLocalizedModule.mk'_one P.primeCompl, IsLocalizedModule.mk'_eq_mk'_iff]
    exact ⟨1, by simpa only [one_smul, Submonoid.smul_def, Algebra.smul_def, t] using ha⟩
  exact hN

variable [IsDomain A] [IsNoetherianRing A] [IsIntegrallyClosed A] [IsFractionRing A F]

/-- For a normal Noetherian domain, it suffices to clear denominators
locally at the height-one primes. -/
theorem mem_algebraMap_range_of_forall_height_one (x : F)
    (h : ∀ (P : Ideal A) [P.IsPrime], P.height = 1 →
      ∃ s : A, s ∉ P ∧ ∃ a : A, algebraMap A F s * x = algebraMap A F a) :
    x ∈ (algebraMap A F).range := by
  let f := Algebra.linearMap A F
  obtain ⟨a, b, hb, hab⟩ := IsFractionRing.div_surjective A x
  have hb0 := mem_nonZeroDivisors_iff_ne_zero.mp hb
  have hbx : b • x ∈ LinearMap.range f := by
    refine ⟨a, ?_⟩
    change algebraMap A F a = b • x
    rw [← hab, Algebra.smul_def, mul_comm, div_mul_cancel₀ _
      (fun hb' => hb0 ((IsFractionRing.injective A F) (hb'.trans (map_zero _).symm)))]
  have hx := mem_range_of_forall_height_one_of_projective f (IsFractionRing.injective A F) hb0 hbx
    (by
      intro P _ hP
      obtain ⟨s, hs, c, hc⟩ := h P hP
      refine ⟨s, hs, c, ?_⟩
      exact hc.symm.trans (Algebra.smul_def s x).symm)
  exact hx

end GlobalTheory.PD
