import GaloisForLFunctions.RHTower.DeningerFiniteFrobeniusOrbitEvaluationSpan
import GaloisForLFunctions.RHTower.DeningerPacketFrobeniusQuotientNontrivial
import Mathlib.Topology.Instances.ZMod

/-!
# A source-visible transverse mode on every literal Deninger prime packet

This module connects finite Frobenius-orbit root evaluations to the actual profinite packet

`DeningerPacketUnits p / closure(⟨p⟩)`.

For odd `p`, reduce the `2`-adic coordinate modulo `8`.  At `p = 2`, reduce the `3`- and
`5`-adic coordinates and recombine them modulo `15` by the Chinese remainder theorem.  In both
cases the resulting map is a continuous surjective homomorphism onto the explicit noncyclic
finite detector from `DeningerFiniteFrobeniusOrbitEvaluationSpan`.  It sends the literal diagonal
packet Frobenius to `p mod n`, so it descends through the closure quotient.

The final theorem pulls the finite Fourier spanning result back along this quotient and produces
a nonconstant finite linear combination of Frobenius-orbit root evaluations on the literal
packet.  This is an unconditional source-visible transverse mode at every prime: the cyclotomic
evaluation channel cannot collapse to scalar packet average.
-/

namespace RHTower

open Set
open scoped BigOperators

noncomputable section

/-- Uniform finite reduction of packet units: modulo `8` at odd primes and modulo `15` at `2`. -/
noncomputable def deningerPrimeTransverseReduction (p : Nat.Primes) :
    DeningerPacketUnits p →*
      (ZMod (deningerPrimeTransverseCyclotomicStage p))ˣ := by
  by_cases hp : (p : ℕ) = 2
  · have hp' : p = ⟨2, Nat.prime_two⟩ := Subtype.ext hp
    subst p
    let p2 : Nat.Primes := ⟨2, Nat.prime_two⟩
    let l3 : {l : Nat.Primes // (l : ℕ) ≠ (p2 : ℕ)} :=
      ⟨⟨3, Nat.prime_three⟩, by norm_num [p2]⟩
    let l5 : {l : Nat.Primes // (l : ℕ) ≠ (p2 : ℕ)} :=
      ⟨⟨5, Nat.prime_five⟩, by norm_num [p2]⟩
    let E : (ZMod 15)ˣ ≃* (ZMod 3)ˣ × (ZMod 5)ˣ :=
      (Units.mapEquiv
        (ZMod.chineseRemainder (m := 3) (n := 5) (by norm_num)).toMulEquiv).trans
        MulEquiv.prodUnits
    change DeningerPacketUnits p2 →* (ZMod 15)ˣ
    exact E.symm.toMonoidHom.comp
      ((deningerPacketCoordinateReduction p2 l3 1).prod
        (deningerPacketCoordinateReduction p2 l5 1))
  · let l2 : {l : Nat.Primes // (l : ℕ) ≠ (p : ℕ)} :=
      ⟨⟨2, Nat.prime_two⟩, Ne.symm hp⟩
    let hmod : (l2.1 : ℕ) ^ 3 =
        deningerPrimeTransverseCyclotomicStage p := by
      simp [deningerPrimeTransverseCyclotomicStage, hp, l2]
    exact
      (Units.mapEquiv (ZMod.ringEquivCongr hmod).toMulEquiv).toMonoidHom.comp
        (deningerPacketCoordinateReduction p l2 3)

/-- The uniform transverse reduction is continuous. -/
theorem deningerPrimeTransverseReduction_continuous (p : Nat.Primes) :
    Continuous (deningerPrimeTransverseReduction p) := by
  by_cases hp : (p : ℕ) = 2
  · have hp' : p = ⟨2, Nat.prime_two⟩ := Subtype.ext hp
    subst p
    let p2 : Nat.Primes := ⟨2, Nat.prime_two⟩
    let l3 : {l : Nat.Primes // (l : ℕ) ≠ (p2 : ℕ)} :=
      ⟨⟨3, Nat.prime_three⟩, by norm_num [p2]⟩
    let l5 : {l : Nat.Primes // (l : ℕ) ≠ (p2 : ℕ)} :=
      ⟨⟨5, Nat.prime_five⟩, by norm_num [p2]⟩
    let E : (ZMod 15)ˣ ≃* (ZMod 3)ˣ × (ZMod 5)ˣ :=
      (Units.mapEquiv
        (ZMod.chineseRemainder (m := 3) (n := 5) (by norm_num)).toMulEquiv).trans
        MulEquiv.prodUnits
    change Continuous
      (E.symm.toMonoidHom.comp
        ((deningerPacketCoordinateReduction p2 l3 1).prod
          (deningerPacketCoordinateReduction p2 l5 1)))
    have hE : Continuous (E.symm : ((ZMod 3)ˣ × (ZMod 5)ˣ) → (ZMod 15)ˣ) :=
      continuous_of_discreteTopology
    exact hE.comp
      ((deningerPacketCoordinateReduction_continuous p2 l3 1).prodMk
        (deningerPacketCoordinateReduction_continuous p2 l5 1))
  · let l2 : {l : Nat.Primes // (l : ℕ) ≠ (p : ℕ)} :=
      ⟨⟨2, Nat.prime_two⟩, Ne.symm hp⟩
    let hmod : (l2.1 : ℕ) ^ 3 =
        deningerPrimeTransverseCyclotomicStage p := by
      simp [deningerPrimeTransverseCyclotomicStage, hp, l2]
    let E8 : (ZMod ((l2.1 : ℕ) ^ 3))ˣ ≃*
        (ZMod (deningerPrimeTransverseCyclotomicStage p))ˣ :=
      Units.mapEquiv (ZMod.ringEquivCongr hmod).toMulEquiv
    have hred : deningerPrimeTransverseReduction p =
        E8.toMonoidHom.comp (deningerPacketCoordinateReduction p l2 3) := by
      simp [deningerPrimeTransverseReduction, hp, E8, l2]
    rw [hred]
    have hE : Continuous
        (E8 : (ZMod ((l2.1 : ℕ) ^ 3))ˣ →
          (ZMod (deningerPrimeTransverseCyclotomicStage p))ˣ) :=
      continuous_of_discreteTopology
    exact hE.comp (deningerPacketCoordinateReduction_continuous p l2 3)

/-- The uniform transverse reduction is surjective. -/
theorem deningerPrimeTransverseReduction_surjective (p : Nat.Primes) :
    Function.Surjective (deningerPrimeTransverseReduction p) := by
  by_cases hp : (p : ℕ) = 2
  · have hp' : p = ⟨2, Nat.prime_two⟩ := Subtype.ext hp
    subst p
    let p2 : Nat.Primes := ⟨2, Nat.prime_two⟩
    let l3 : {l : Nat.Primes // (l : ℕ) ≠ (p2 : ℕ)} :=
      ⟨⟨3, Nat.prime_three⟩, by norm_num [p2]⟩
    let l5 : {l : Nat.Primes // (l : ℕ) ≠ (p2 : ℕ)} :=
      ⟨⟨5, Nat.prime_five⟩, by norm_num [p2]⟩
    let E : (ZMod 15)ˣ ≃* (ZMod 3)ˣ × (ZMod 5)ˣ :=
      (Units.mapEquiv
        (ZMod.chineseRemainder (m := 3) (n := 5) (by norm_num)).toMulEquiv).trans
        MulEquiv.prodUnits
    letI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
    have hpair : Function.Surjective
        ((deningerPacketCoordinateReduction p2 l3 1).prod
          (deningerPacketCoordinateReduction p2 l5 1)) := by
      rintro ⟨v3, v5⟩
      obtain ⟨w3, hw3⟩ :=
        deningerPadicUnitReduction_surjective 3 1 (by omega) v3
      obtain ⟨w5, hw5⟩ :=
        deningerPadicUnitReduction_surjective 5 1 (by omega) v5
      have h35 : l3 ≠ l5 := by
        intro h
        have := congrArg (fun l => (l.1 : ℕ)) h
        norm_num [l3, l5] at this
      let u : DeningerPacketUnits p2 :=
        Function.update (Function.update (fun _ => 1) l3 w3) l5 w5
      refine ⟨u, ?_⟩
      apply Prod.ext
      · change deningerPadicUnitReduction 3 1 (u l3) = v3
        simpa [u, h35] using hw3
      · change deningerPadicUnitReduction 5 1 (u l5) = v5
        simpa [u] using hw5
    change Function.Surjective
      (E.symm.toMonoidHom.comp
        ((deningerPacketCoordinateReduction p2 l3 1).prod
          (deningerPacketCoordinateReduction p2 l5 1)))
    exact E.symm.surjective.comp hpair
  · let l2 : {l : Nat.Primes // (l : ℕ) ≠ (p : ℕ)} :=
      ⟨⟨2, Nat.prime_two⟩, Ne.symm hp⟩
    let hmod : (l2.1 : ℕ) ^ 3 =
        deningerPrimeTransverseCyclotomicStage p := by
      simp [deningerPrimeTransverseCyclotomicStage, hp, l2]
    let E8 : (ZMod ((l2.1 : ℕ) ^ 3))ˣ ≃*
        (ZMod (deningerPrimeTransverseCyclotomicStage p))ˣ :=
      Units.mapEquiv (ZMod.ringEquivCongr hmod).toMulEquiv
    have hred : deningerPrimeTransverseReduction p =
        E8.toMonoidHom.comp (deningerPacketCoordinateReduction p l2 3) := by
      simp [deningerPrimeTransverseReduction, hp, E8, l2]
    rw [hred]
    exact E8.surjective.comp
      (deningerPacketCoordinateReduction_surjective p l2 3 (by omega))

/-- Uniform reduction sends literal diagonal packet Frobenius to `p mod n`. -/
theorem deningerPrimeTransverseReduction_frobenius (p : Nat.Primes) :
    deningerPrimeTransverseReduction p (deningerPacketFrobeniusUnit p) =
      ZMod.unitOfCoprime (p : ℕ)
        (deningerPrimeTransverseCyclotomicStage_coprime p) := by
  by_cases hp : (p : ℕ) = 2
  · have hp' : p = ⟨2, Nat.prime_two⟩ := Subtype.ext hp
    subst p
    let p2 : Nat.Primes := ⟨2, Nat.prime_two⟩
    let l3 : {l : Nat.Primes // (l : ℕ) ≠ (p2 : ℕ)} :=
      ⟨⟨3, Nat.prime_three⟩, by norm_num [p2]⟩
    let l5 : {l : Nat.Primes // (l : ℕ) ≠ (p2 : ℕ)} :=
      ⟨⟨5, Nat.prime_five⟩, by norm_num [p2]⟩
    let E : (ZMod 15)ˣ ≃* (ZMod 3)ˣ × (ZMod 5)ˣ :=
      (Units.mapEquiv
        (ZMod.chineseRemainder (m := 3) (n := 5) (by norm_num)).toMulEquiv).trans
        MulEquiv.prodUnits
    letI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
    change E.symm
      (deningerPacketCoordinateReduction p2 l3 1
          (deningerPacketFrobeniusUnit p2),
        deningerPacketCoordinateReduction p2 l5 1
          (deningerPacketFrobeniusUnit p2)) =
      ZMod.unitOfCoprime 2
        (deningerPrimeTransverseCyclotomicStage_coprime p2)
    apply E.injective
    rw [E.apply_symm_apply]
    have h3 :
        deningerPacketCoordinateReduction p2 l3 1
            (deningerPacketFrobeniusUnit p2) =
          ZMod.unitOfCoprime (p2 : ℕ)
            (deningerPrime_coprime_awayPrime_pow p2 l3 1) := by
      change Units.map (PadicInt.toZModPow 1).toMonoidHom
          (deningerPacketFrobeniusUnit p2 l3) =
        ZMod.unitOfCoprime (p2 : ℕ)
          (deningerPrime_coprime_awayPrime_pow p2 l3 1)
      exact deningerPacketFrobeniusUnit_toZModPow p2 l3 1
    have h5 :
        deningerPacketCoordinateReduction p2 l5 1
            (deningerPacketFrobeniusUnit p2) =
          ZMod.unitOfCoprime (p2 : ℕ)
            (deningerPrime_coprime_awayPrime_pow p2 l5 1) := by
      change Units.map (PadicInt.toZModPow 1).toMonoidHom
          (deningerPacketFrobeniusUnit p2 l5) =
        ZMod.unitOfCoprime (p2 : ℕ)
          (deningerPrime_coprime_awayPrime_pow p2 l5 1)
      exact deningerPacketFrobeniusUnit_toZModPow p2 l5 1
    apply Prod.ext
    · rw [h3]
      apply Units.ext
      change (2 : ZMod 3) =
        ((ZMod.chineseRemainder (m := 3) (n := 5) (by norm_num))
          (2 : ZMod 15)).1
      exact (congrArg Prod.fst
        (map_ofNat
          (ZMod.chineseRemainder (m := 3) (n := 5) (by norm_num)) 2)).symm
    · rw [h5]
      apply Units.ext
      change (2 : ZMod 5) =
        ((ZMod.chineseRemainder (m := 3) (n := 5) (by norm_num))
          (2 : ZMod 15)).2
      exact (congrArg Prod.snd
        (map_ofNat
          (ZMod.chineseRemainder (m := 3) (n := 5) (by norm_num)) 2)).symm
  · let l2 : {l : Nat.Primes // (l : ℕ) ≠ (p : ℕ)} :=
      ⟨⟨2, Nat.prime_two⟩, Ne.symm hp⟩
    let hmod : (l2.1 : ℕ) ^ 3 =
        deningerPrimeTransverseCyclotomicStage p := by
      simp [deningerPrimeTransverseCyclotomicStage, hp, l2]
    let E8 : (ZMod ((l2.1 : ℕ) ^ 3))ˣ ≃*
        (ZMod (deningerPrimeTransverseCyclotomicStage p))ˣ :=
      Units.mapEquiv (ZMod.ringEquivCongr hmod).toMulEquiv
    have hred : deningerPrimeTransverseReduction p =
        E8.toMonoidHom.comp (deningerPacketCoordinateReduction p l2 3) := by
      simp [deningerPrimeTransverseReduction, hp, E8, l2]
    rw [hred]
    change E8
        (deningerPacketCoordinateReduction p l2 3
          (deningerPacketFrobeniusUnit p)) =
      ZMod.unitOfCoprime (p : ℕ)
        (deningerPrimeTransverseCyclotomicStage_coprime p)
    have hcoord :
        deningerPacketCoordinateReduction p l2 3
            (deningerPacketFrobeniusUnit p) =
          ZMod.unitOfCoprime (p : ℕ)
            (deningerPrime_coprime_awayPrime_pow p l2 3) := by
      change Units.map (PadicInt.toZModPow 3).toMonoidHom
          (deningerPacketFrobeniusUnit p l2) =
        ZMod.unitOfCoprime (p : ℕ)
          (deningerPrime_coprime_awayPrime_pow p l2 3)
      exact deningerPacketFrobeniusUnit_toZModPow p l2 3
    rw [hcoord]
    apply Units.ext
    simp [E8, ZMod.unitOfCoprime]

/-- Frobenius closure lies in the preimage of the finite Frobenius subgroup. -/
theorem deningerPrimeFrobeniusClosure_le_transverseReduction_comap
    (p : Nat.Primes) :
    deningerPacketFrobeniusClosure p ≤
      Subgroup.comap (deningerPrimeTransverseReduction p)
        (deningerFiniteFrobeniusSubgroup
          (p : ℕ) (deningerPrimeTransverseCyclotomicStage p)
          (deningerPrimeTransverseCyclotomicStage_coprime p)) := by
  apply Subgroup.topologicalClosure_minimal
  · change Subgroup.zpowers (deningerPacketFrobeniusUnit p) ≤
      Subgroup.comap (deningerPrimeTransverseReduction p)
        (deningerFiniteFrobeniusSubgroup
          (p : ℕ) (deningerPrimeTransverseCyclotomicStage p)
          (deningerPrimeTransverseCyclotomicStage_coprime p))
    rw [Subgroup.zpowers_le]
    change deningerPrimeTransverseReduction p (deningerPacketFrobeniusUnit p) ∈
      deningerFiniteFrobeniusSubgroup
        (p : ℕ) (deningerPrimeTransverseCyclotomicStage p)
        (deningerPrimeTransverseCyclotomicStage_coprime p)
    rw [deningerPrimeTransverseReduction_frobenius]
    exact Subgroup.mem_zpowers _
  · change IsClosed
      ((deningerPrimeTransverseReduction p) ⁻¹'
        (deningerFiniteFrobeniusSubgroup
          (p : ℕ) (deningerPrimeTransverseCyclotomicStage p)
          (deningerPrimeTransverseCyclotomicStage_coprime p) :
            Set (ZMod (deningerPrimeTransverseCyclotomicStage p))ˣ))
    exact (Set.toFinite _).isClosed.preimage
      (deningerPrimeTransverseReduction_continuous p)

/-- Continuous finite quotient of the literal Frobenius-closure packet. -/
noncomputable def deningerPrimeTransverseQuotientReduction (p : Nat.Primes) :
    DeningerPacketFrobeniusQuotient p →*
      DeningerPrimeTransverseFinitePacket p :=
  QuotientGroup.map
    (deningerPacketFrobeniusClosure p)
    (deningerFiniteFrobeniusSubgroup
      (p : ℕ) (deningerPrimeTransverseCyclotomicStage p)
      (deningerPrimeTransverseCyclotomicStage_coprime p))
    (deningerPrimeTransverseReduction p)
    (deningerPrimeFrobeniusClosure_le_transverseReduction_comap p)

/-- Finite reduction remains surjective after dividing both sides by Frobenius. -/
theorem deningerPrimeTransverseQuotientReduction_surjective (p : Nat.Primes) :
    Function.Surjective (deningerPrimeTransverseQuotientReduction p) := by
  intro q
  obtain ⟨v, rfl⟩ := QuotientGroup.mk_surjective q
  obtain ⟨u, hu⟩ := deningerPrimeTransverseReduction_surjective p v
  refine ⟨(QuotientGroup.mk u : DeningerPacketFrobeniusQuotient p), ?_⟩
  rw [deningerPrimeTransverseQuotientReduction, QuotientGroup.map_mk, hu]

/-- Finite quotient reduction is continuous on the literal packet quotient. -/
theorem deningerPrimeTransverseQuotientReduction_continuous (p : Nat.Primes) :
    Continuous (deningerPrimeTransverseQuotientReduction p) := by
  rw [(QuotientGroup.isQuotientMap_mk
    (deningerPacketFrobeniusClosure p)).continuous_iff]
  change Continuous
    ((deningerPrimeTransverseQuotientReduction p) ∘
      (QuotientGroup.mk :
        DeningerPacketUnits p → DeningerPacketFrobeniusQuotient p))
  have hfun :
      (deningerPrimeTransverseQuotientReduction p) ∘
          (QuotientGroup.mk :
            DeningerPacketUnits p → DeningerPacketFrobeniusQuotient p) =
        (QuotientGroup.mk :
          (ZMod (deningerPrimeTransverseCyclotomicStage p))ˣ →
            DeningerPrimeTransverseFinitePacket p) ∘
          deningerPrimeTransverseReduction p := by
    funext u
    exact QuotientGroup.map_mk _ _ _ _ u
  rw [hfun]
  exact continuous_quot_mk.comp
    (deningerPrimeTransverseReduction_continuous p)

/-- Frobenius-orbit root evaluation pulled back to the literal packet quotient. -/
noncomputable def deningerPrimeTransverseOrbitEvaluation
    (p : Nat.Primes)
    (j : ZMod (deningerPrimeTransverseCyclotomicStage p))
    (x : DeningerPacketFrobeniusQuotient p) : ℂ :=
  deningerFiniteFrobeniusOrbitEvaluation
    (p : ℕ) (deningerPrimeTransverseCyclotomicStage p)
    (deningerPrimeTransverseCyclotomicStage_coprime p) j
    (deningerPrimeTransverseQuotientReduction p x)

/-- Pulled-back orbit root evaluations are continuous on the literal packet. -/
theorem deningerPrimeTransverseOrbitEvaluation_continuous
    (p : Nat.Primes)
    (j : ZMod (deningerPrimeTransverseCyclotomicStage p)) :
    Continuous (deningerPrimeTransverseOrbitEvaluation p j) := by
  apply Continuous.comp _ (deningerPrimeTransverseQuotientReduction_continuous p)
  exact continuous_of_discreteTopology

/-- Pullback along the finite quotient is faithful on its whole function space. -/
theorem deningerPrimeTransverseQuotientReduction_pullback_injective
    (p : Nat.Primes) :
    Function.Injective
      (fun F : DeningerPrimeTransverseFinitePacket p → ℂ =>
        fun x : DeningerPacketFrobeniusQuotient p =>
          F (deningerPrimeTransverseQuotientReduction p x)) := by
  intro F G hFG
  funext q
  obtain ⟨x, hx⟩ := deningerPrimeTransverseQuotientReduction_surjective p q
  have hpoint := congrFun hFG x
  simpa [hx] using hpoint

/-- **Full finite source subspace on the actual packet.**  Pullback of every function on the
explicit finite detector is a finite linear combination of pulled-back Frobenius-orbit root
evaluations. -/
theorem deningerPrimeTransverseOrbitEvaluation_span_pullback
    (p : Nat.Primes)
    (F : DeningerPrimeTransverseFinitePacket p → ℂ) :
    ∃ c : ZMod (deningerPrimeTransverseCyclotomicStage p) → ℂ,
      ∀ x : DeningerPacketFrobeniusQuotient p,
        F (deningerPrimeTransverseQuotientReduction p x) =
          ∑ j : ZMod (deningerPrimeTransverseCyclotomicStage p),
            c j * deningerPrimeTransverseOrbitEvaluation p j x := by
  obtain ⟨c, hc⟩ :=
    deningerFiniteFrobeniusOrbitEvaluation_span
      (p : ℕ) (deningerPrimeTransverseCyclotomicStage p)
      (deningerPrimeTransverseCyclotomicStage_coprime p) F
  exact ⟨c, fun x => hc (deningerPrimeTransverseQuotientReduction p x)⟩

/-- **Actual-packet transverse source visibility.**  At every prime, a finite linear combination
of Frobenius-orbit root evaluations is nonconstant on the literal profinite packet quotient. -/
theorem deningerPrimeTransverseOrbitEvaluation_exists_nonconstant
    (p : Nat.Primes) :
    ∃ (c : ZMod (deningerPrimeTransverseCyclotomicStage p) → ℂ)
      (x y : DeningerPacketFrobeniusQuotient p),
      (∑ j : ZMod (deningerPrimeTransverseCyclotomicStage p),
        c j * deningerPrimeTransverseOrbitEvaluation p j x) ≠
      ∑ j : ZMod (deningerPrimeTransverseCyclotomicStage p),
        c j * deningerPrimeTransverseOrbitEvaluation p j y := by
  classical
  obtain ⟨c, hsum, q₀, hq₀⟩ :=
    deningerPrimeTransverseFinitePacket_exists_zeroSum_nonzero p
  let S : DeningerPrimeTransverseFinitePacket p → ℂ := fun q =>
    ∑ j : ZMod (deningerPrimeTransverseCyclotomicStage p),
      c j * deningerFiniteFrobeniusOrbitEvaluation
        (p : ℕ) (deningerPrimeTransverseCyclotomicStage p)
        (deningerPrimeTransverseCyclotomicStage_coprime p) j q
  have hnotconstant : ¬ ∀ q, S q = S q₀ := by
    intro hconst
    have hcardNat : Fintype.card (DeningerPrimeTransverseFinitePacket p) ≠ 0 :=
      Fintype.card_ne_zero
    have hcard :
        (Fintype.card (DeningerPrimeTransverseFinitePacket p) : ℂ) ≠ 0 := by
      exact_mod_cast hcardNat
    have hmul :
        (Fintype.card (DeningerPrimeTransverseFinitePacket p) : ℂ) * S q₀ = 0 := by
      rw [← hsum]
      simp_rw [show ∀ q, (∑ j : ZMod (deningerPrimeTransverseCyclotomicStage p),
        c j * deningerFiniteFrobeniusOrbitEvaluation
          (p : ℕ) (deningerPrimeTransverseCyclotomicStage p)
          (deningerPrimeTransverseCyclotomicStage_coprime p) j q) = S q from
            fun q => rfl]
      simp_rw [hconst]
      simp
    exact hq₀ ((mul_eq_zero.mp hmul).resolve_left hcard)
  push Not at hnotconstant
  obtain ⟨q₁, hq₁⟩ := hnotconstant
  obtain ⟨x, hx⟩ := deningerPrimeTransverseQuotientReduction_surjective p q₀
  obtain ⟨y, hy⟩ := deningerPrimeTransverseQuotientReduction_surjective p q₁
  refine ⟨c, x, y, ?_⟩
  change S (deningerPrimeTransverseQuotientReduction p x) ≠
    S (deningerPrimeTransverseQuotientReduction p y)
  rw [hx, hy]
  exact hq₁.symm

end

end RHTower
