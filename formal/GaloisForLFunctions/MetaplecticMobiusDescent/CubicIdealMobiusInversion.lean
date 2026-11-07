/-
Ideal Möbius inversion adapted from OpenAI's formalization,
Apache-2.0. See LICENSE and NOTICE for source attribution.
-/
import GaloisForLFunctions.MetaplecticMobiusDescent.CubicIdealTotients
import Mathlib.Data.Nat.Choose.Sum

/-!
# Möbius inversion for Eisenstein ideals

Squarefree ideal divisors are exactly products of subsets of prime
support. The alternating powerset sum proves divisor inversion.
Counting quotient units with this identity yields the ideal totient
formula, while multiplicative fibres give the convolution identity.
-/
noncomputable section
open MeasureTheory Set Filter UniqueFactorizationMonoid
open scoped BigOperators Classical
namespace GaloisForLFunctions.MetaplecticMobiusDescent.CubicEisenstein
open Eisenstein CubicJacobi CubicKubota CubicRamified

def idealDivisors (I : Ideal O) : Finset (Ideal O) :=
  (Ideal.finite_setOf_absNorm_le (S := O) (Ideal.absNorm I)).toFinset.filter
    (fun J => J ∣ I)

theorem mem_idealDivisors {I J : Ideal O} (hI : I ≠ ⊥) :
    J ∈ idealDivisors I ↔ J ∣ I := by
  simp only [idealDivisors, Finset.mem_filter, Set.Finite.mem_toFinset, Set.mem_setOf_eq]
  constructor
  · exact And.right
  · intro hJI
    have hn : 0 < Ideal.absNorm I := Nat.pos_iff_ne_zero.mpr
      (fun hz => hI (Ideal.absNorm_eq_zero_iff.mp hz))
    exact ⟨Nat.le_of_dvd hn (map_dvd Ideal.absNorm hJI), hJI⟩

def primeSupport (I : Ideal O) : Finset (Ideal O) := (normalizedFactors I).toFinset

theorem support_prime {I : Ideal O} {P : Ideal O} (hP : P ∈ primeSupport I) : Prime P :=
  prime_of_normalized_factor P (Multiset.mem_toFinset.mp hP)

theorem support_product_ne_zero {I : Ideal O} {S : Finset (Ideal O)}
    (hS : S ⊆ primeSupport I) : (∏ P ∈ S, P) ≠ 0 :=
  Finset.prod_ne_zero_iff.mpr (fun _P hP => (support_prime (hS hP)).ne_zero)

theorem factors_support_product {I : Ideal O} {S : Finset (Ideal O)}
    (hS : S ⊆ primeSupport I) : normalizedFactors (∏ P ∈ S, P) = S.val := by
  have hp : ∀ P ∈ S.val, Prime P := fun P hP => support_prime (hS hP)
  simpa using normalizedFactors_prod_of_prime hp

theorem squarefree_support_product {I : Ideal O} {S : Finset (Ideal O)}
    (hS : S ⊆ primeSupport I) : Squarefree (∏ P ∈ S, P) := by
  apply (squarefree_iff_nodup_normalizedFactors (support_product_ne_zero hS)).mpr
  rw [factors_support_product hS]
  exact S.nodup

theorem support_product_dvd {I : Ideal O} (hI : I ≠ ⊥) {S : Finset (Ideal O)}
    (hS : S ⊆ primeSupport I) : (∏ P ∈ S, P) ∣ I := by
  apply (dvd_iff_normalizedFactors_le_normalizedFactors (support_product_ne_zero hS) hI).mpr
  rw [factors_support_product hS]
  apply (Multiset.le_iff_subset S.nodup).mpr
  intro P hP
  exact Multiset.mem_toFinset.mp (hS hP)

theorem moebius_support_product {I : Ideal O} {S : Finset (Ideal O)}
    (hS : S ⊆ primeSupport I) :
    (moebius (∏ P ∈ S, P) : ℂ) = (-1 : ℂ) ^ S.card := by
  rw [(squarefree_support_product hS).moebius_eq, factors_eq_normalizedFactors,
    factors_support_product hS]
  simp

theorem support_product_injective {I : Ideal O}
    {S T : Finset (Ideal O)} (hS : S ⊆ primeSupport I) (hT : T ⊆ primeSupport I)
    (h : (∏ P ∈ S, P) = ∏ P ∈ T, P) : S = T := by
  have hf := congrArg normalizedFactors h
  rw [factors_support_product hS, factors_support_product hT] at hf
  exact Finset.val_inj.mp hf

theorem squarefree_divisor_support {I J : Ideal O} (hI : I ≠ ⊥)
    (hJ : Squarefree J) (hJI : J ∣ I) : primeSupport J ⊆ primeSupport I := by
  have hf := (dvd_iff_normalizedFactors_le_normalizedFactors hJ.ne_zero hI).mp hJI
  intro P hP
  exact Multiset.mem_toFinset.mpr (Multiset.mem_of_le hf (Multiset.mem_toFinset.mp hP))

theorem squarefree_support_product_self {J : Ideal O} (hJ : Squarefree J) :
    (∏ P ∈ primeSupport J, P) = J := by
  have hn : (normalizedFactors J).Nodup :=
    (squarefree_iff_nodup_normalizedFactors hJ.ne_zero).mp hJ
  have hv : (primeSupport J).val = normalizedFactors J := by
    simpa only [primeSupport, Multiset.toFinset_val] using hn.dedup
  calc
    _ = (primeSupport J).val.prod := (Finset.prod_val _).symm
    _ = (normalizedFactors J).prod := by rw [hv]
    _ = J := Ideal.prod_normalizedFactors_eq_self hJ.ne_zero

theorem squarefree_divisors_eq_image (I : Ideal O) (hI : I ≠ ⊥) :
    (idealDivisors I).filter Squarefree =
      (primeSupport I).powerset.image (fun S => ∏ P ∈ S, P) := by
  ext J
  simp only [Finset.mem_filter, mem_idealDivisors hI, Finset.mem_image, Finset.mem_powerset]
  constructor
  · rintro ⟨hJI, hJ⟩
    exact ⟨primeSupport J, squarefree_divisor_support hI hJ hJI,
      squarefree_support_product_self hJ⟩
  · rintro ⟨S, hS, rfl⟩
    exact ⟨support_product_dvd hI hS, squarefree_support_product hS⟩

theorem primeSupport_empty_iff (I : Ideal O) (hI : I ≠ ⊥) :
    primeSupport I = ∅ ↔ I = ⊤ := by
  constructor
  · intro h
    have hz : normalizedFactors I = 0 := by
      apply Multiset.toFinset_eq_empty.mp
      exact h
    have hp := Ideal.prod_normalizedFactors_eq_self hI
    rw [hz, Multiset.prod_zero] at hp
    simpa only [Ideal.one_eq_top] using hp.symm
  · intro h
    subst I
    simp [primeSupport, ← Ideal.one_eq_top]

theorem sum_moebius_divisors (I : Ideal O) (hI : I ≠ ⊥) :
    (∑ J ∈ idealDivisors I, (moebius J : ℂ)) = if I = ⊤ then 1 else 0 := by
  have hfilter : (∑ J ∈ idealDivisors I, (moebius J : ℂ)) =
      ∑ J ∈ (idealDivisors I).filter Squarefree, (moebius J : ℂ) := by
    symm
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro J hJ hnot
    have hn : ¬ Squarefree J := by simpa [hJ] using hnot
    rw [moebius_of_not_squarefree hn, Int.cast_zero]
  rw [hfilter, squarefree_divisors_eq_image I hI, Finset.sum_image]
  · have heq : (∑ S ∈ (primeSupport I).powerset, (moebius (∏ P ∈ S, P) : ℂ)) =
        ∑ S ∈ (primeSupport I).powerset, (-1 : ℂ) ^ S.card := by
      exact Finset.sum_congr rfl (fun S hS => moebius_support_product (Finset.mem_powerset.mp hS))
    have hsign : (∑ S ∈ (primeSupport I).powerset, (-1 : ℂ) ^ S.card) =
        if primeSupport I = ∅ then 1 else 0 := by
      exact_mod_cast (Finset.sum_powerset_neg_one_pow_card (x := primeSupport I))
    rw [heq, hsign]
    simp only [primeSupport_empty_iff I hI]
  · intro S hS T hT hST
    exact support_product_injective (Finset.mem_powerset.mp hS)
      (Finset.mem_powerset.mp hT) hST

lemma isUnit_quotient_iff_sup (I : Ideal O) (x : O) :
    IsUnit (Ideal.Quotient.mk I x) ↔ I ⊔ Ideal.span {x}=⊤ := by
  constructor
  · intro hx
    obtain ⟨b,hb⟩ := isUnit_iff_exists_inv.mp hx
    obtain ⟨b,rfl⟩ := Ideal.Quotient.mk_surjective b
    have hI : x*b-1 ∈ I := by
      apply Ideal.Quotient.eq_zero_iff_mem.mp
      simpa only [map_sub,map_mul,map_one,sub_eq_zero] using hb
    apply (Ideal.eq_top_iff_one _).mpr
    have hx' : x*b ∈ I ⊔ Ideal.span {x} :=
      (le_sup_right : Ideal.span {x} ≤ I ⊔ Ideal.span {x})
        ((Ideal.span {x}).mul_mem_right b (Ideal.subset_span (by simp)))
    convert (I ⊔ Ideal.span {x}).sub_mem hx' ((le_sup_left : I ≤ I ⊔ Ideal.span {x}) hI) using 1 ; ring
  · intro h
    have h1 : (1:O) ∈ I ⊔ Ideal.span {x} := by rw [h]; trivial
    obtain ⟨a,ha,b,hb,hab⟩ := Submodule.mem_sup.mp h1
    obtain ⟨k,rfl⟩ := Ideal.mem_span_singleton.mp hb
    apply isUnit_iff_exists_inv.mpr
    refine ⟨Ideal.Quotient.mk I k, ?_⟩
    have ha0 := Ideal.Quotient.eq_zero_iff_mem.mpr ha
    have hh := congrArg (Ideal.Quotient.mk I) hab
    simpa only [map_add,map_mul,map_one,ha0,zero_add] using hh

lemma residue_unit_mobius (I : Ideal O) (hI : I ≠ 0) (r : O ⧸ I) :
    (if IsUnit r then (1:ℂ) else 0) =
      ∑ J ∈ idealDivisors I, if Quotient.out r ∈ J then (moebius J:ℂ) else 0 := by
  let G : Ideal O := I ⊔ Ideal.span {Quotient.out r}
  have hG : G ≠ 0 := by
    intro hG
    apply hI
    apply le_antisymm _ bot_le
    calc
      I ≤ G := le_sup_left
      _ = ⊥ := hG
  have hdiv : (idealDivisors I).filter (fun J => Quotient.out r ∈ J)=idealDivisors G := by
    ext J
    simp only [Finset.mem_filter,mem_idealDivisors hI,mem_idealDivisors hG,
      Ideal.dvd_iff_le,G,sup_le_iff,Ideal.span_le,Set.singleton_subset_iff,SetLike.mem_coe]
  rw [← Finset.sum_filter,hdiv,sum_moebius_divisors G hG]
  have hu : IsUnit r ↔ G=⊤ := by
    rw [← Ideal.Quotient.mk_out r]
    exact isUnit_quotient_iff_sup I (Quotient.out r)
  simp only [hu]

lemma sum_indicator_const {R : Type*} [Fintype R] (P : R → Prop) (z : ℂ) :
    (∑ r : R, if P r then z else 0)=(Nat.card {r : R // P r}:ℂ)*z := by
  rw [← Finset.sum_filter]
  simp only [Finset.sum_const,nsmul_eq_mul,Nat.card_eq_fintype_card,Fintype.card_subtype]

lemma card_quotient_multiples (I J : Ideal O) (hI : I ≠ 0) (hIJ : I ≤ J) :
    (Nat.card {r : O ⧸ I // Quotient.out r ∈ J}:ℂ)=
      (Ideal.absNorm I:ℂ)/(Ideal.absNorm J:ℂ) := by
  let f : (O ⧸ I) →+* (O ⧸ J) := Ideal.Quotient.factor hIJ
  have hf : Function.Surjective f := Ideal.Quotient.factor_surjective hIJ
  have hpred (r : O ⧸ I) : Quotient.out r ∈ J ↔ f r=0 := by
    have hfr : f r=Ideal.Quotient.mk J (Quotient.out r) := by
      calc
        f r = f (Ideal.Quotient.mk I (Quotient.out r)) :=
          congrArg f (Ideal.Quotient.mk_out r).symm
        _ = _ := Ideal.Quotient.factor_mk hIJ _
    rw [← Ideal.Quotient.eq_zero_iff_mem,hfr]
  let e : {r : O ⧸ I // Quotient.out r ∈ J} ≃ f.toAddMonoidHom.ker :=
    Equiv.subtypeEquivRight hpred
  have hcard := card_ring_eq_card_mul_kernel f hf
  have hJ : J ≠ 0 := fun h => hI (le_antisymm (h ▸ hIJ) bot_le)
  have hnJ : (Ideal.absNorm J:ℂ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr hJ)
  rw [Nat.card_congr e]
  apply (eq_div_iff hnJ).mpr
  have hh : Nat.card f.toAddMonoidHom.ker * Ideal.absNorm J = Ideal.absNorm I :=
    (Nat.mul_comm _ _).trans hcard.symm
  exact_mod_cast hh

theorem idealTotient_moebius (I : Ideal O) (hI : I ≠ 0) :
    (idealTotient I:ℂ)=(Ideal.absNorm I:ℂ)*
      ∑ J ∈ idealDivisors I, (moebius J:ℂ)/(Ideal.absNorm J:ℂ) := by
  let : Finite (O ⧸ I) := I.finiteQuotientOfFreeOfNeBot hI
  let : Fintype (O ⧸ I) := Fintype.ofFinite _
  classical
  have hcount : (idealTotient I:ℂ)=∑ r : O ⧸ I,
      @ite ℂ (IsUnit r) (Classical.propDecidable _) 1 0 := by
    have h := sum_indicator_const (R := O ⧸ I) IsUnit (1:ℂ)
    rw [mul_one] at h
    calc
      _ = (Nat.card {r : O ⧸ I // IsUnit r}:ℂ) := by
        exact_mod_cast Nat.card_congr (unitsSubtypeEquiv (O ⧸ I))
      _ = _ := h.symm
  rw [hcount]
  have hs : (∑ r : O ⧸ I, @ite ℂ (IsUnit r) (Classical.propDecidable _) 1 0) =
      ∑ r : O ⧸ I, ∑ J ∈ idealDivisors I,
        if Quotient.out r ∈ J then (moebius J:ℂ) else 0 := by
    apply Finset.sum_congr rfl
    intro r hr
    exact residue_unit_mobius I hI r
  rw [hs]
  rw [Finset.sum_comm]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro J hJ
  rw [sum_indicator_const,card_quotient_multiples I J hI
    (Ideal.dvd_iff_le.mp ((mem_idealDivisors hI).mp hJ))]
  ring

def MulFiber (B : Ideal O) := {p : Ideal O × Ideal O // p.1 * p.2 = B}

def mulFiberDivisorEquiv (B : Ideal O) (hB : B ≠ 0) :
    MulFiber B ≃ {D : Ideal O // D ∈ idealDivisors B} := by
  let f : MulFiber B → {D : Ideal O // D ∈ idealDivisors B} :=
    fun p => ⟨p.val.1, (mem_idealDivisors hB).mpr ⟨p.val.2, p.property.symm⟩⟩
  apply Equiv.ofBijective f
  constructor
  · intro p q hpq
    have hfst : p.val.1 = q.val.1 := congrArg Subtype.val hpq
    apply Subtype.ext
    apply Prod.ext hfst
    have hn : p.val.1 ≠ 0 := by
      intro hz
      have he := p.property
      rw [hz, zero_mul] at he
      exact hB he.symm
    apply mul_left_cancel₀ hn
    rw [p.property, hfst, q.property]
  · intro D
    obtain ⟨J, hJ⟩ := (mem_idealDivisors hB).mp D.property
    exact ⟨⟨(D.val, J), hJ.symm⟩, rfl⟩

theorem mulFiber_moebius_sum (B : Ideal O) (hB : B ≠ 0) :
    (∑' p : MulFiber B, (UniqueFactorizationMonoid.moebius p.val.1 : ℂ)) =
      if B = 1 then 1 else 0 := by
  let e := mulFiberDivisorEquiv B hB
  calc
    _ = ∑' D : {D : Ideal O // D ∈ idealDivisors B},
        (UniqueFactorizationMonoid.moebius D.val : ℂ) := by
      exact e.tsum_eq (fun D => (UniqueFactorizationMonoid.moebius D.val : ℂ))
    _ = ∑ D ∈ idealDivisors B, (UniqueFactorizationMonoid.moebius D : ℂ) := by
      rw [tsum_fintype]
      exact (Finset.sum_subtype (idealDivisors B) (fun D => Iff.rfl)
        (fun D => (UniqueFactorizationMonoid.moebius D : ℂ))).symm
    _ = if B = 1 then 1 else 0 := by
      simpa only [Ideal.one_eq_top] using sum_moebius_divisors B hB


#print axioms sum_moebius_divisors
#print axioms idealTotient_moebius
#print axioms mulFiber_moebius_sum
end GaloisForLFunctions.MetaplecticMobiusDescent.CubicEisenstein
