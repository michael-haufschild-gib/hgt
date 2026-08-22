import Mathlib.RingTheory.AdicCompletion.Algebra
import Mathlib.RingTheory.Filtration
import Mathlib.RingTheory.AdicCompletion.Completeness
import Mathlib.RingTheory.AdicCompletion.LocalRing
import Mathlib.RingTheory.LocalRing.Basic
import Mathlib.RingTheory.LocalRing.ResidueField.Basic

/-!
# Locality of an adic completion

Deninger, *Dynamical systems for arithmetic schemes* (arXiv:1807.06400v4), Proposition 14.14(1)
(`t1213`): for a local ring `A` whose maximal ideal contains `p`, the `p`-adic completion `Â` is
again local, and `A / 𝔪 ≅ Â / 𝔪̂`.

The mechanism is that the completion is complete for the extended ideal, so that ideal lies in the
Jacobson radical; a ring admitting a surjection onto a local ring with kernel inside the Jacobson
radical is local, since every maximal ideal then contains the kernel and so is the preimage of the
maximal ideal downstairs.  The residue-field statement follows because a surjection of local rings
is a local homomorphism inducing a surjection — hence a bijection — of residue fields.
-/

namespace RHTower

open IsLocalRing

/-- A ring admitting a surjection onto a local ring whose kernel lies in the Jacobson radical is
itself local. -/
theorem deningerIsLocalRing_of_surjective_of_ker_le_jacobson
    {S K : Type*} [CommRing S] [CommRing K] [IsLocalRing K] (f : S →+* K)
    (hf : Function.Surjective f) (hker : RingHom.ker f ≤ Ideal.jacobson (⊥ : Ideal S)) :
    IsLocalRing S := by
  refine IsLocalRing.of_unique_max_ideal
    ⟨Ideal.comap f (IsLocalRing.maximalIdeal K), Ideal.comap_isMaximal_of_surjective f hf, ?_⟩
  intro J hJ
  have hkerJ : RingHom.ker f ≤ J := hker.trans (sInf_le ⟨bot_le, hJ⟩)
  haveI : J.IsMaximal := hJ
  have hmapmax : (J.map f).IsMaximal := Ideal.IsMaximal.map_of_surjective_of_ker_le hf hkerJ
  have hmax : J.map f = IsLocalRing.maximalIdeal K := IsLocalRing.eq_maximalIdeal hmapmax
  rw [← hmax, Ideal.comap_map_of_surjective' f hf J, sup_eq_left.mpr hkerJ]

/-- **Deninger, Proposition 14.14(1) (`t1213`).**  For a local ring `R` and an ideal `I` contained
in the maximal ideal, the `I`-adic completion of `R` is again a local ring. -/
theorem deningerAdicCompletion_isLocalRing {R : Type*} [CommRing R] [IsLocalRing R]
    (I : Ideal R) (hfg : I.FG) (hI : I ≤ IsLocalRing.maximalIdeal R) :
    IsLocalRing (AdicCompletion I R) := by
  haveI : IsAdicComplete (I.map (algebraMap R (AdicCompletion I R))) (AdicCompletion I R) :=
    AdicCompletion.isAdicComplete_self I hfg
  haveI hIne : I ≠ ⊤ := fun h => (IsLocalRing.maximalIdeal.isMaximal R).ne_top
    (top_le_iff.mp (h ▸ hI))
  haveI : Nontrivial (R ⧸ I) := Ideal.Quotient.nontrivial_iff.mpr hIne
  haveI : IsLocalRing (R ⧸ I) :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective
  refine deningerIsLocalRing_of_surjective_of_ker_le_jacobson
    (AdicCompletion.evalOneₐ I).toRingHom (AdicCompletion.evalOneₐ_surjective I) ?_
  rw [AdicCompletion.ker_evalOneₐ_eq_map I hfg]
  exact IsAdicComplete.le_jacobson_bot _

/-- A surjection of local rings identifies the maximal ideal of the source with the preimage of
the maximal ideal of the target. -/
theorem deningerMaximalIdeal_eq_comap {S K : Type*} [CommRing S] [CommRing K] [IsLocalRing S]
    [IsLocalRing K] (f : S →+* K) (hf : Function.Surjective f) :
    IsLocalRing.maximalIdeal S = Ideal.comap f (IsLocalRing.maximalIdeal K) :=
  (IsLocalRing.eq_maximalIdeal (Ideal.comap_isMaximal_of_surjective f hf)).symm

/-- A surjection of local rings is a local homomorphism. -/
theorem deningerIsLocalHom_of_surjective {S K : Type*} [CommRing S] [CommRing K] [IsLocalRing S]
    [IsLocalRing K] (f : S →+* K) (hf : Function.Surjective f) : IsLocalHom f := by
  refine ⟨fun a ha => ?_⟩
  rw [← IsLocalRing.notMem_maximalIdeal] at ha ⊢
  rw [deningerMaximalIdeal_eq_comap f hf]
  exact ha

/-- A surjection of local rings induces an isomorphism of residue fields. -/
theorem deningerResidueField_bijective_of_surjective {S K : Type*} [CommRing S] [CommRing K]
    [IsLocalRing S] [IsLocalRing K] (f : S →+* K) (hf : Function.Surjective f) :
    letI := deningerIsLocalHom_of_surjective f hf
    Function.Bijective (IsLocalRing.ResidueField.map f) := by
  letI := deningerIsLocalHom_of_surjective f hf
  refine ⟨(IsLocalRing.ResidueField.map f).injective, ?_⟩
  intro y
  obtain ⟨k, rfl⟩ := IsLocalRing.residue_surjective (R := K) y
  obtain ⟨s, rfl⟩ := hf k
  exact ⟨IsLocalRing.residue _ s, IsLocalRing.ResidueField.map_residue f s⟩

/-- **Deninger, Proposition 14.14(1), `p`-adic case.**  The `p`-adic completion of a local ring in
whose maximal ideal `p` lies is again local. -/
theorem deningerPAdicCompletion_isLocalRing {R : Type*} [CommRing R] [IsLocalRing R] (p : R)
    (hp : p ∈ IsLocalRing.maximalIdeal R) :
    IsLocalRing (AdicCompletion (Ideal.span {p}) R) :=
  deningerAdicCompletion_isLocalRing _ ⟨{p}, by simp⟩
    (Ideal.span_le.mpr (by simpa using hp))

/-- **Deninger, Proposition 14.3 (`t123`).**  On a Noetherian local domain the `I`-adic topology
is separated for every proper ideal `I`: the canonical map to the `I`-adic completion is
injective.  Applied to `I = (p)` this is the statement of the source that the `p`-adic topology on
the local ring `𝒪_{closure {x}, y}` is separated. -/
theorem deningerAdicCompletion_of_injective {R : Type*} [CommRing R] [IsNoetherianRing R]
    [IsLocalRing R] [IsDomain R] (I : Ideal R) (hI : I ≠ ⊤) :
    Function.Injective (AdicCompletion.of I R) := by
  refine AdicCompletion.of_injective_iff.mpr ⟨fun x hx => ?_⟩
  have hbot : ⨅ n : ℕ, I ^ n = ⊥ := Ideal.iInf_pow_eq_bot_of_isLocalRing I hI
  have hmem : x ∈ ⨅ n : ℕ, I ^ n := by
    refine Submodule.mem_iInf _ |>.2 fun n => ?_
    have h := hx n
    rw [SModEq.zero] at h
    simpa using h
  rw [hbot] at hmem
  simpa using hmem

/-- **Deninger, Proposition 14.3 (`t123`), `p`-adic case.** -/
theorem deningerPAdicCompletion_of_injective {R : Type*} [CommRing R] [IsNoetherianRing R]
    [IsLocalRing R] [IsDomain R] (p : R) (hp : p ∈ IsLocalRing.maximalIdeal R) :
    Function.Injective (AdicCompletion.of (Ideal.span {p}) R) :=
  deningerAdicCompletion_of_injective _ (fun h =>
    (IsLocalRing.maximalIdeal.isMaximal R).ne_top
      (top_le_iff.mp (h ▸ Ideal.span_le.mpr (by simpa using hp))))

end RHTower
