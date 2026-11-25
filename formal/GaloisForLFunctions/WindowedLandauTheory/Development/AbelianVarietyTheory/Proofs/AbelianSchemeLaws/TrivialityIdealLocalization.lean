import GaloisForLFunctions.HTGeometry.LocalizationIdealClearing
import Mathlib.RingTheory.Finiteness.Ideal
import Mathlib.RingTheory.Localization.AtPrime.Basic
import Mathlib.RingTheory.LocalRing.RingHom.Basic
import Mathlib.RingTheory.Nakayama

/-! A finite ideal that vanishes through all small extensions vanishes near the prime. -/

namespace GlobalTheory.AbLaw.Seesaw

-- Remove generators one at a time while keeping the lower ideal fixed.
private theorem le_of_drop_generators {S : Type} [CommRing S] (N J : Ideal S) (hN : N ≤ J)
    (H : ∀ (I : Ideal S) (e : S), e ∈ J → N ≤ I →
      I ≤ J → J ≤ I ⊔ Ideal.span {e} → J ≤ I)
    (s : Finset S) : (s : Set S) ⊆ J → J ≤ N ⊔ Ideal.span (s : Set S) → J ≤ N := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    intro _ h
    rwa [Finset.coe_empty, Ideal.span_empty, sup_bot_eq] at h
  | insert a s _ ih =>
    intro hs h
    rw [Finset.coe_insert] at hs h
    have hs' : (s : Set S) ⊆ J := (Set.subset_insert _ _).trans hs
    refine ih hs' (H _ a (hs (Set.mem_insert _ _)) le_sup_left
      (sup_le hN (Ideal.span_le.2 hs')) ?_)
    rwa [Ideal.span_insert, sup_comm (Ideal.span {a}), ← sup_assoc] at h

private theorem eq_bot_of_small {S : Type} [CommRing S] [IsLocalRing S]
    (J : Ideal S) (hJ : J.FG)
    (H : ∀ (I : Ideal S) (e : S), e ∈ J → IsLocalRing.maximalIdeal S * J ≤ I →
      I ≤ J → J ≤ I ⊔ Ideal.span {e} → J ≤ I) : J = ⊥ := by
  let m := IsLocalRing.maximalIdeal S
  obtain ⟨s, hs⟩ := id hJ
  have hs' : Ideal.span (s : Set S) = J := hs
  have hset : (s : Set S) ⊆ (J : Set S) := by
    rw [← hs']
    exact Ideal.subset_span
  have hincl : Ideal.span (s : Set S) ≤ m * J ⊔ Ideal.span (s : Set S) := le_sup_right
  have hle : J ≤ m * J ⊔ Ideal.span (s : Set S) := hs'.ge.trans hincl
  have hmul : m * J ≤ J := Ideal.mul_le_left
  have hsmall : J ≤ m * J := le_of_drop_generators (m * J) J hmul H s hset hle
  have hsmul : J ≤ m • J := (Ideal.smul_eq_mul m J).symm ▸ hsmall
  exact Submodule.eq_bot_of_le_smul_of_le_jacobson_bot (R := S) (M := S) m J hJ hsmul
    (IsLocalRing.maximalIdeal_le_jacobson (⊥ : Ideal S))

/-- Small extensions of local rings detect vanishing of a finite ideal at a prime. -/
theorem exists_annihilator_of_small_extensions {R : Type} [CommRing R]
    (p : Ideal R) [p.IsPrime] (I : Ideal R) (hI : I.FG) (hIp : I ≤ p)
    (lift_zero : ∀ (T : Type) [CommRing T] [IsLocalRing T] (g : R →+* T) (e : T),
      (∀ r ∉ p, IsUnit (g r)) →
      (∀ a ∈ IsLocalRing.maximalIdeal T, a * e = 0) →
      e ∈ IsLocalRing.maximalIdeal T →
      I ≤ RingHom.ker ((Ideal.Quotient.mk (Ideal.span {e})).comp g) → I ≤ RingHom.ker g) :
    ∃ c ∉ p, ∀ x ∈ I, c * x = 0 := by
  let S := Localization.AtPrime p
  let J := I.map (algebraMap R S)
  have hpJ : J ≤ IsLocalRing.maximalIdeal S := by
    rw [← Localization.AtPrime.map_eq_maximalIdeal]
    exact Ideal.map_mono hIp
  have hJ : J = ⊥ := by
    refine eq_bot_of_small J (hI.map _) fun Q e he hmul hQ hspan => ?_
    have hne : Q ≠ ⊤ := ne_top_of_le_ne_top
      (IsLocalRing.maximalIdeal.isMaximal S).ne_top (hQ.trans hpJ)
    haveI : Nontrivial (S ⧸ Q) := Ideal.Quotient.nontrivial_iff.2 hne
    let q := Ideal.Quotient.mk Q
    haveI : IsLocalRing (S ⧸ Q) := IsLocalRing.of_surjective' q Ideal.Quotient.mk_surjective
    haveI : IsLocalHom q := IsLocalHom.of_surjective _ Ideal.Quotient.mk_surjective
    have hunit (r : R) (hr : r ∉ p) : IsUnit (q (algebraMap R S r)) :=
      (IsLocalization.map_units S (⟨r, hr⟩ : p.primeCompl)).map q
    have hann (a : S ⧸ Q) (ha : a ∈ IsLocalRing.maximalIdeal (S ⧸ Q)) : a * q e = 0 := by
      obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective a
      rw [← map_mul, Ideal.Quotient.eq_zero_iff_mem]
      exact hmul (Ideal.mul_mem_mul (fun hb => ha (hb.map q)) he)
    have hmax : q e ∈ IsLocalRing.maximalIdeal (S ⧸ Q) :=
      fun hu => hpJ he (IsUnit.of_map _ _ hu)
    have hzero : I ≤ RingHom.ker ((Ideal.Quotient.mk (Ideal.span {q e})).comp
        (q.comp (algebraMap R S))) := by
      intro x hx
      obtain ⟨y, hy, z, hz, hyz⟩ := Submodule.mem_sup.1
        (hspan (Ideal.mem_map_of_mem _ hx))
      obtain ⟨w, rfl⟩ := Ideal.mem_span_singleton'.1 hz
      rw [RingHom.mem_ker, RingHom.comp_apply, RingHom.comp_apply, ← hyz, map_add,
        Ideal.Quotient.eq_zero_iff_mem.2 hy, zero_add, Ideal.Quotient.eq_zero_iff_mem, map_mul]
      exact Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _)
    change I.map (algebraMap R S) ≤ Q
    rw [Ideal.map_le_iff_le_comap]
    intro x hx
    change algebraMap R S x ∈ Q
    exact (Ideal.Quotient.eq_zero_iff_mem (I := Q)).1
      (lift_zero _ (q.comp (algebraMap R S)) (q e) hunit hann hmax hzero hx)
  obtain ⟨c, hc⟩ := GaloisForLFunctions.HTGeometry.exists_denominator_mul_le_of_localized_ideal_le
    (S := S) p.primeCompl I (⊥ : Ideal R) hI (by rw [Ideal.map_bot]; exact hJ.le)
  exact ⟨c, c.2, fun x hx => Ideal.mem_bot.1 (hc x hx)⟩

end GlobalTheory.AbLaw.Seesaw
