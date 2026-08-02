import GaloisForLFunctions.RHTower.DeningerFiniteFrobeniusEvaluationSystem
import GaloisForLFunctions.RHTower.DeningerPacketFrobeniusQuotientNontrivial
import GaloisForLFunctions.RHTower.DeningerPrimeMultiplicativeAutomorphismTopology
import GaloisForLFunctions.RHTower.DeningerPrimePacketHaarL2Green
import Mathlib.Algebra.Group.Pi.Units
import Mathlib.Data.ZMod.QuotientRing
import Mathlib.MeasureTheory.Function.ContinuousMapDense
import Mathlib.Topology.ContinuousMap.StoneWeierstrass

/-!
# Cofinal finite cyclotomic detection of the literal Deninger packet

Let

`Pₚ = (∏_{ℓ ≠ p} ℤ_ℓˣ) / closure(⟨p⟩)`.

For every nonzero modulus `n` coprime to `p`, prime-factor CRT and independent `ℓ`-adic
coordinates construct a continuous surjection

`Pₚ → (ZMod n)ˣ / ⟨p mod n⟩`.

The central theorem proves the exact closure identity

`closure(⟨p⟩) = ⋂ₙ redₙ⁻¹(⟨p mod n⟩)`.

Its hard direction uses the faithful pointwise action on every actual prime-power cyclotomic
stage.  A point outside the Frobenius closure has a basic product neighborhood controlled by
finitely many root stages; multiplying their moduli produces one finite stage that detects the
point.

Consequences:

* finite quotient reductions jointly inject the literal packet quotient;
* finite-stage real pullbacks form a subalgebra (not merely a generated algebra);
* that subalgebra is uniformly dense by Stone--Weierstrass;
* each of its elements is one exact finite linear combination of Frobenius-orbit root
  evaluations; and
* its image is dense in normalized packet Haar `L²`.

Thus the complete continuous and Haar packet channels are recovered from finite
rational-cyclotomic evaluations.  No inverse-limit identification is assumed.
-/

namespace RHTower

open Set
open Topology

noncomputable section

def deningerPrimeStageAwayFactor (p : Nat.Primes)
    (s : DeningerFiniteFrobeniusStage (p : ℕ))
    (q : s.modulus.primeFactors) :
    {l : Nat.Primes // (l : ℕ) ≠ (p : ℕ)} := by
  have hqprime : Nat.Prime (q : ℕ) :=
    (Nat.mem_primeFactors.mp q.property).1
  refine ⟨⟨q, hqprime⟩, ?_⟩
  intro hqp
  apply (p.property.coprime_iff_not_dvd.mp s.coprime)
  obtain ⟨k, hk⟩ := (Nat.mem_primeFactors.mp q.property).2.1
  refine ⟨k, ?_⟩
  calc
    s.modulus = (q : ℕ) * k := hk
    _ = (p : ℕ) * k := by rw [hqp]

@[simp] theorem deningerPrimeStageAwayFactor_coe (p : Nat.Primes)
    (s : DeningerFiniteFrobeniusStage (p : ℕ))
    (q : s.modulus.primeFactors) :
    ((deningerPrimeStageAwayFactor p s q).1 : ℕ) = (q : ℕ) :=
  by simp [deningerPrimeStageAwayFactor]

def deningerFiniteFrobeniusStageExponent (s : DeningerFiniteFrobeniusStage (p : ℕ))
    (q : s.modulus.primeFactors) : ℕ :=
  s.modulus.factorization q

theorem deningerFiniteFrobeniusStageExponent_ne_zero (s : DeningerFiniteFrobeniusStage (p : ℕ))
    (q : s.modulus.primeFactors) : deningerFiniteFrobeniusStageExponent s q ≠ 0 := by
  exact (Nat.Prime.factorization_pos_of_dvd
    (Nat.mem_primeFactors.mp q.property).1 s.modulus_ne_zero
    (Nat.mem_primeFactors.mp q.property).2.1).ne'

noncomputable def deningerFiniteFrobeniusStageCRTMulEquiv (s : DeningerFiniteFrobeniusStage (p : ℕ)) :
    (ZMod s.modulus)ˣ ≃*
      ∀ q : s.modulus.primeFactors,
        (ZMod ((q : ℕ) ^ deningerFiniteFrobeniusStageExponent s q))ˣ :=
  (Units.mapEquiv
    (ZMod.equivPi s.modulus s.modulus_ne_zero).toMulEquiv).trans
      MulEquiv.piUnits

theorem deningerPrimeStageFactorModulus_eq (p : Nat.Primes)
    (s : DeningerFiniteFrobeniusStage (p : ℕ))
    (q : s.modulus.primeFactors) :
    ((deningerPrimeStageAwayFactor p s q).1 : ℕ) ^ deningerFiniteFrobeniusStageExponent s q =
      (q : ℕ) ^ deningerFiniteFrobeniusStageExponent s q := by
  rw [deningerPrimeStageAwayFactor_coe]

noncomputable def deningerPrimeStageFactorTransport (p : Nat.Primes)
    (s : DeningerFiniteFrobeniusStage (p : ℕ))
    (q : s.modulus.primeFactors) :
    (ZMod (((deningerPrimeStageAwayFactor p s q).1 : ℕ) ^ deningerFiniteFrobeniusStageExponent s q))ˣ ≃*
      (ZMod ((q : ℕ) ^ deningerFiniteFrobeniusStageExponent s q))ˣ :=
  Units.mapEquiv
    (ZMod.ringEquivCongr (deningerPrimeStageFactorModulus_eq p s q)).toMulEquiv

noncomputable def deningerPrimeStageFactorReduction (p : Nat.Primes)
    (s : DeningerFiniteFrobeniusStage (p : ℕ))
    (q : s.modulus.primeFactors) :
    DeningerPacketUnits p →*
      (ZMod ((q : ℕ) ^ deningerFiniteFrobeniusStageExponent s q))ˣ := by
  exact
    (deningerPrimeStageFactorTransport p s q).toMonoidHom.comp
        (deningerPacketCoordinateReduction p (deningerPrimeStageAwayFactor p s q)
          (deningerFiniteFrobeniusStageExponent s q))

theorem deningerPrimeStageFactorReduction_continuous (p : Nat.Primes)
    (s : DeningerFiniteFrobeniusStage (p : ℕ))
    (q : s.modulus.primeFactors) :
    Continuous (deningerPrimeStageFactorReduction p s q) := by
  have hE : Continuous
      (deningerPrimeStageFactorTransport p s q :
        (ZMod (((deningerPrimeStageAwayFactor p s q).1 : ℕ) ^ deningerFiniteFrobeniusStageExponent s q))ˣ →
          (ZMod ((q : ℕ) ^ deningerFiniteFrobeniusStageExponent s q))ˣ) :=
    continuous_of_discreteTopology
  exact hE.comp
    (deningerPacketCoordinateReduction_continuous p
      (deningerPrimeStageAwayFactor p s q) (deningerFiniteFrobeniusStageExponent s q))

theorem deningerPrimeStageFactorReduction_surjective (p : Nat.Primes)
    (s : DeningerFiniteFrobeniusStage (p : ℕ))
    (q : s.modulus.primeFactors) :
    Function.Surjective (deningerPrimeStageFactorReduction p s q) := by
  intro v
  obtain ⟨u, hu⟩ :=
    deningerPacketCoordinateReduction_surjective p
      (deningerPrimeStageAwayFactor p s q) (deningerFiniteFrobeniusStageExponent s q)
      (deningerFiniteFrobeniusStageExponent_ne_zero s q) ((deningerPrimeStageFactorTransport p s q).symm v)
  refine ⟨u, ?_⟩
  change deningerPrimeStageFactorTransport p s q
      (deningerPacketCoordinateReduction p (deningerPrimeStageAwayFactor p s q)
        (deningerFiniteFrobeniusStageExponent s q) u) = v
  rw [hu, MulEquiv.apply_symm_apply]

def deningerPrimeStageFactorReductionTuple (p : Nat.Primes)
    (s : DeningerFiniteFrobeniusStage (p : ℕ)) :
    DeningerPacketUnits p →*
      ∀ q : s.modulus.primeFactors,
        (ZMod ((q : ℕ) ^ deningerFiniteFrobeniusStageExponent s q))ˣ where
  toFun u q := deningerPrimeStageFactorReduction p s q u
  map_one' := by
    funext q
    exact map_one _
  map_mul' u v := by
    funext q
    exact map_mul _ _ _

theorem deningerPrimeStageFactorReductionTuple_surjective (p : Nat.Primes)
    (s : DeningerFiniteFrobeniusStage (p : ℕ)) :
    Function.Surjective (deningerPrimeStageFactorReductionTuple p s) := by
  intro v
  let localPacket : ∀ q : s.modulus.primeFactors,
      DeningerPacketUnits p :=
    fun q => Classical.choose (deningerPrimeStageFactorReduction_surjective p s q (v q))
  have localSpec (q : s.modulus.primeFactors) :
      deningerPrimeStageFactorReduction p s q (localPacket q) = v q :=
    Classical.choose_spec (deningerPrimeStageFactorReduction_surjective p s q (v q))
  let u : DeningerPacketUnits p := fun l =>
    if h : (l.1 : ℕ) ∈ s.modulus.primeFactors then
      localPacket ⟨(l.1 : ℕ), h⟩ l
    else 1
  refine ⟨u, ?_⟩
  funext q
  change deningerPrimeStageFactorReduction p s q u = v q
  have hu :
      u (deningerPrimeStageAwayFactor p s q) =
        localPacket q (deningerPrimeStageAwayFactor p s q) := by
    simp only [u]
    split_ifs with hmem
    · congr 2
    · exact False.elim
        (hmem (deningerPrimeStageAwayFactor_coe p s q ▸ q.property))
  change deningerPrimeStageFactorTransport p s q
      (deningerPacketCoordinateReduction p (deningerPrimeStageAwayFactor p s q)
        (deningerFiniteFrobeniusStageExponent s q) u) = v q
  rw [show deningerPacketCoordinateReduction p (deningerPrimeStageAwayFactor p s q)
      (deningerFiniteFrobeniusStageExponent s q) u =
      deningerPacketCoordinateReduction p (deningerPrimeStageAwayFactor p s q)
        (deningerFiniteFrobeniusStageExponent s q) (localPacket q) by
    change deningerPadicUnitReduction
      ((deningerPrimeStageAwayFactor p s q).1 : ℕ) (deningerFiniteFrobeniusStageExponent s q)
        (u (deningerPrimeStageAwayFactor p s q)) =
      deningerPadicUnitReduction
        ((deningerPrimeStageAwayFactor p s q).1 : ℕ) (deningerFiniteFrobeniusStageExponent s q)
        (localPacket q (deningerPrimeStageAwayFactor p s q))
    rw [hu]]
  exact localSpec q

/-- Canonical CRT reduction from literal packet units to units modulo an arbitrary
prime-to-`p` stage. -/
noncomputable def deningerPrimeFiniteStageReduction (p : Nat.Primes)
    (s : DeningerFiniteFrobeniusStage (p : ℕ)) :
    DeningerPacketUnits p →* (ZMod s.modulus)ˣ :=
  (deningerFiniteFrobeniusStageCRTMulEquiv s).symm.toMonoidHom.comp (deningerPrimeStageFactorReductionTuple p s)

theorem deningerPrimeStageFactorReductionTuple_continuous (p : Nat.Primes)
    (s : DeningerFiniteFrobeniusStage (p : ℕ)) :
    Continuous (deningerPrimeStageFactorReductionTuple p s) := by
  exact continuous_pi fun q =>
    deningerPrimeStageFactorReduction_continuous p s q

theorem deningerPrimeFiniteStageReduction_continuous (p : Nat.Primes)
    (s : DeningerFiniteFrobeniusStage (p : ℕ)) :
    Continuous (deningerPrimeFiniteStageReduction p s) := by
  have hcrt : Continuous
      ((deningerFiniteFrobeniusStageCRTMulEquiv s).symm :
        (∀ q : s.modulus.primeFactors,
          (ZMod ((q : ℕ) ^ deningerFiniteFrobeniusStageExponent s q))ˣ) →
          (ZMod s.modulus)ˣ) :=
    continuous_of_discreteTopology
  exact hcrt.comp (deningerPrimeStageFactorReductionTuple_continuous p s)

theorem deningerPrimeFiniteStageReduction_surjective (p : Nat.Primes)
    (s : DeningerFiniteFrobeniusStage (p : ℕ)) :
    Function.Surjective (deningerPrimeFiniteStageReduction p s) :=
  (deningerFiniteFrobeniusStageCRTMulEquiv s).symm.surjective.comp (deningerPrimeStageFactorReductionTuple_surjective p s)

theorem deningerFiniteStageFactor_dvd (p : Nat.Primes)
    (s : DeningerFiniteFrobeniusStage (p : ℕ))
    (q : s.modulus.primeFactors) :
    (q : ℕ) ^ deningerFiniteFrobeniusStageExponent s q ∣ s.modulus := by
  exact ((Nat.mem_primeFactors.mp q.property).1.pow_dvd_iff_le_factorization
    s.modulus_ne_zero).2 le_rfl

theorem deningerFiniteStageFactor_coprime (p : Nat.Primes)
    (s : DeningerFiniteFrobeniusStage (p : ℕ))
    (q : s.modulus.primeFactors) :
    (p : ℕ).Coprime ((q : ℕ) ^ deningerFiniteFrobeniusStageExponent s q) :=
  s.coprime.coprime_dvd_right (deningerFiniteStageFactor_dvd p s q)

theorem deningerPrimeStageFactorReduction_frobenius (p : Nat.Primes)
    (s : DeningerFiniteFrobeniusStage (p : ℕ))
    (q : s.modulus.primeFactors) :
    deningerPrimeStageFactorReduction p s q (deningerPacketFrobeniusUnit p) =
      ZMod.unitOfCoprime (p : ℕ) (deningerFiniteStageFactor_coprime p s q) := by
  change deningerPrimeStageFactorTransport p s q
      (deningerPacketCoordinateReduction p (deningerPrimeStageAwayFactor p s q)
        (deningerFiniteFrobeniusStageExponent s q) (deningerPacketFrobeniusUnit p)) =
    ZMod.unitOfCoprime (p : ℕ) (deningerFiniteStageFactor_coprime p s q)
  rw [show deningerPacketCoordinateReduction p (deningerPrimeStageAwayFactor p s q)
      (deningerFiniteFrobeniusStageExponent s q) (deningerPacketFrobeniusUnit p) =
      ZMod.unitOfCoprime (p : ℕ)
        (deningerPrime_coprime_awayPrime_pow p
          (deningerPrimeStageAwayFactor p s q) (deningerFiniteFrobeniusStageExponent s q)) by
    exact deningerPacketFrobeniusUnit_toZModPow p
      (deningerPrimeStageAwayFactor p s q) (deningerFiniteFrobeniusStageExponent s q)]
  apply Units.ext
  simp [deningerPrimeStageFactorTransport, ZMod.unitOfCoprime]

theorem deningerFiniteStageCRT_frobenius_component (p : Nat.Primes)
    (s : DeningerFiniteFrobeniusStage (p : ℕ))
    (q : s.modulus.primeFactors) :
    deningerFiniteFrobeniusStageCRTMulEquiv s (ZMod.unitOfCoprime (p : ℕ) s.coprime) q =
      ZMod.unitOfCoprime (p : ℕ) (deningerFiniteStageFactor_coprime p s q) := by
  apply Units.ext
  change
    ZMod.equivPi s.modulus s.modulus_ne_zero
        ((p : ℕ) : ZMod s.modulus) q =
      ((p : ℕ) :
        ZMod ((q : ℕ) ^ deningerFiniteFrobeniusStageExponent s q))
  simp
  rfl

theorem deningerPrimeFiniteStageReduction_frobenius (p : Nat.Primes)
    (s : DeningerFiniteFrobeniusStage (p : ℕ)) :
    deningerPrimeFiniteStageReduction p s (deningerPacketFrobeniusUnit p) =
      ZMod.unitOfCoprime (p : ℕ) s.coprime := by
  apply (deningerFiniteFrobeniusStageCRTMulEquiv s).injective
  change deningerFiniteFrobeniusStageCRTMulEquiv s
      ((deningerFiniteFrobeniusStageCRTMulEquiv s).symm
        (deningerPrimeStageFactorReductionTuple p s (deningerPacketFrobeniusUnit p))) =
    deningerFiniteFrobeniusStageCRTMulEquiv s (ZMod.unitOfCoprime (p : ℕ) s.coprime)
  rw [MulEquiv.apply_symm_apply]
  funext q
  change deningerPrimeStageFactorReduction p s q (deningerPacketFrobeniusUnit p) =
    deningerFiniteFrobeniusStageCRTMulEquiv s (ZMod.unitOfCoprime (p : ℕ) s.coprime) q
  rw [deningerPrimeStageFactorReduction_frobenius, deningerFiniteStageCRT_frobenius_component]

theorem deningerPacketFrobeniusClosure_le_finiteStageReduction_comap (p : Nat.Primes)
    (s : DeningerFiniteFrobeniusStage (p : ℕ)) :
    deningerPacketFrobeniusClosure p ≤
      Subgroup.comap (deningerPrimeFiniteStageReduction p s)
        (deningerFiniteFrobeniusSubgroup
          (p : ℕ) s.modulus s.coprime) := by
  apply Subgroup.topologicalClosure_minimal
  · change Subgroup.zpowers (deningerPacketFrobeniusUnit p) ≤
      Subgroup.comap (deningerPrimeFiniteStageReduction p s)
        (Subgroup.zpowers (ZMod.unitOfCoprime (p : ℕ) s.coprime))
    rw [Subgroup.zpowers_le]
    change deningerPrimeFiniteStageReduction p s (deningerPacketFrobeniusUnit p) ∈
      Subgroup.zpowers (ZMod.unitOfCoprime (p : ℕ) s.coprime)
    rw [deningerPrimeFiniteStageReduction_frobenius]
    exact Subgroup.mem_zpowers _
  · change IsClosed
      ((deningerPrimeFiniteStageReduction p s) ⁻¹'
        (deningerFiniteFrobeniusSubgroup
          (p : ℕ) s.modulus s.coprime :
            Set (ZMod s.modulus)ˣ))
    exact (Set.toFinite _).isClosed.preimage
      (deningerPrimeFiniteStageReduction_continuous p s)

noncomputable def deningerPrimeFiniteStageQuotientReduction (p : Nat.Primes)
    (s : DeningerFiniteFrobeniusStage (p : ℕ)) :
    DeningerPacketFrobeniusQuotient p →*
      DeningerFiniteFrobeniusStageQuotient (p : ℕ) s :=
  QuotientGroup.map
    (deningerPacketFrobeniusClosure p)
    (deningerFiniteFrobeniusSubgroup
      (p : ℕ) s.modulus s.coprime)
    (deningerPrimeFiniteStageReduction p s) (deningerPacketFrobeniusClosure_le_finiteStageReduction_comap p s)

theorem deningerPrimeFiniteStageQuotientReduction_surjective (p : Nat.Primes)
    (s : DeningerFiniteFrobeniusStage (p : ℕ)) :
    Function.Surjective (deningerPrimeFiniteStageQuotientReduction p s) := by
  intro q
  obtain ⟨v, rfl⟩ := QuotientGroup.mk_surjective q
  obtain ⟨u, hu⟩ := deningerPrimeFiniteStageReduction_surjective p s v
  refine
    ⟨(QuotientGroup.mk u : DeningerPacketFrobeniusQuotient p), ?_⟩
  rw [deningerPrimeFiniteStageQuotientReduction, QuotientGroup.map_mk, hu]

theorem deningerPrimeFiniteStageQuotientReduction_continuous (p : Nat.Primes)
    (s : DeningerFiniteFrobeniusStage (p : ℕ)) :
    Continuous (deningerPrimeFiniteStageQuotientReduction p s) := by
  rw [(QuotientGroup.isQuotientMap_mk
    (deningerPacketFrobeniusClosure p)).continuous_iff]
  change Continuous
    ((deningerPrimeFiniteStageQuotientReduction p s) ∘
      (QuotientGroup.mk :
        DeningerPacketUnits p → DeningerPacketFrobeniusQuotient p))
  have hfun :
      (deningerPrimeFiniteStageQuotientReduction p s) ∘
          (QuotientGroup.mk :
            DeningerPacketUnits p → DeningerPacketFrobeniusQuotient p) =
        (QuotientGroup.mk :
          (ZMod s.modulus)ˣ →
            DeningerFiniteFrobeniusStageQuotient (p : ℕ) s) ∘
          deningerPrimeFiniteStageReduction p s := by
    funext u
    exact QuotientGroup.map_mk _ _ _ _ u
  rw [hfun]
  exact continuous_quot_mk.comp
    (deningerPrimeFiniteStageReduction_continuous p s)

theorem deningerPrimeFiniteStageReduction_component (p : Nat.Primes)
    (s : DeningerFiniteFrobeniusStage (p : ℕ))
    (q : s.modulus.primeFactors) (u : DeningerPacketUnits p) :
    ZMod.unitsMap (deningerFiniteStageFactor_dvd p s q) (deningerPrimeFiniteStageReduction p s u) =
      deningerPrimeStageFactorReduction p s q u := by
  have hcrt :
      deningerFiniteFrobeniusStageCRTMulEquiv s (deningerPrimeFiniteStageReduction p s u) q =
        deningerPrimeStageFactorReduction p s q u := by
    change deningerFiniteFrobeniusStageCRTMulEquiv s ((deningerFiniteFrobeniusStageCRTMulEquiv s).symm (deningerPrimeStageFactorReductionTuple p s u)) q =
      deningerPrimeStageFactorReduction p s q u
    rw [MulEquiv.apply_symm_apply]
    rfl
  rw [← hcrt]
  apply Units.ext
  change ZMod.cast (deningerPrimeFiniteStageReduction p s u : ZMod s.modulus) =
    ZMod.equivPi s.modulus s.modulus_ne_zero
      (deningerPrimeFiniteStageReduction p s u : ZMod s.modulus) q
  let M := ∏ r : s.modulus.primeFactors,
    (r : ℕ) ^ s.modulus.factorization r
  have hprod : s.modulus = M :=
    Nat.prod_primeFactors_coe_pow_factorization s.modulus_ne_zero
  have hqprod :
      (q : ℕ) ^ s.modulus.factorization q ∣ M := by
    exact Finset.dvd_prod_of_mem
      (fun r : s.modulus.primeFactors =>
        (r : ℕ) ^ s.modulus.factorization r)
      (Finset.mem_univ q)
  have hhom :
      ZMod.castHom (deningerFiniteStageFactor_dvd p s q)
          (ZMod ((q : ℕ) ^ s.modulus.factorization q)) =
        (ZMod.castHom hqprod
          (ZMod ((q : ℕ) ^ s.modulus.factorization q))).comp
          (ZMod.ringEquivCongr hprod).toRingHom :=
    Subsingleton.elim _ _
  unfold ZMod.equivPi
  rw [RingEquiv.trans_apply, ZMod.prodEquivPi_apply]
  exact RingHom.congr_fun hhom _

theorem deningerPacketCoordinateReduction_transition (p : Nat.Primes)
    (l : {l : Nat.Primes // (l : ℕ) ≠ (p : ℕ)})
    {k₁ k₂ : ℕ} (hk : k₁ ≤ k₂) (u : DeningerPacketUnits p) :
    ZMod.unitsMap (pow_dvd_pow (l.1 : ℕ) hk)
        (deningerPacketCoordinateReduction p l k₂ u) =
      deningerPacketCoordinateReduction p l k₁ u := by
  apply Units.ext
  simp only [ZMod.unitsMap_val, deningerPacketCoordinateReduction,
    MonoidHom.comp_apply, deningerPadicUnitReduction, Units.coe_map]
  exact PadicInt.cast_toZModPow k₁ k₂ hk (u l : ℤ_[l.1])

theorem deningerPrimeFiniteStageReduction_eq_implies_coordinateReduction_eq (p : Nat.Primes)
    (s : DeningerFiniteFrobeniusStage (p : ℕ))
    (l : {l : Nat.Primes // (l : ℕ) ≠ (p : ℕ)})
    (k : ℕ) (hpow : (l.1 : ℕ) ^ k ∣ s.modulus)
    (u v : DeningerPacketUnits p)
    (huv : deningerPrimeFiniteStageReduction p s u = deningerPrimeFiniteStageReduction p s v) :
    deningerPacketCoordinateReduction p l k u =
      deningerPacketCoordinateReduction p l k v := by
  cases k with
  | zero =>
      apply Units.ext
      simp only [deningerPacketCoordinateReduction,
        MonoidHom.comp_apply, deningerPadicUnitReduction, Units.coe_map]
      have h :
          PadicInt.toZModPow 0 (u l : ℤ_[l.1]) =
            PadicInt.toZModPow 0 (v l : ℤ_[l.1]) := by
        change (_ : ZMod 1) = _
        exact Subsingleton.elim _ _
      exact h
  | succ k =>
      have hldvd : (l.1 : ℕ) ∣ s.modulus :=
        dvd_trans (dvd_pow_self (l.1 : ℕ) (Nat.succ_ne_zero k)) hpow
      let q : s.modulus.primeFactors :=
        ⟨(l.1 : ℕ), Nat.mem_primeFactors.mpr
          ⟨l.1.property, hldvd, s.modulus_ne_zero⟩⟩
      have haway : deningerPrimeStageAwayFactor p s q = l := by
        apply Subtype.ext
        apply Subtype.ext
        exact deningerPrimeStageAwayFactor_coe p s q
      have hK :
          k + 1 ≤ deningerFiniteFrobeniusStageExponent s q := by
        exact (l.1.property.pow_dvd_iff_le_factorization
          s.modulus_ne_zero).mp hpow
      have hfactor :
          deningerPrimeStageFactorReduction p s q u = deningerPrimeStageFactorReduction p s q v := by
        rw [← deningerPrimeFiniteStageReduction_component p s q u,
          ← deningerPrimeFiniteStageReduction_component p s q v, huv]
      have hhigh :
          deningerPacketCoordinateReduction p (deningerPrimeStageAwayFactor p s q)
              (deningerFiniteFrobeniusStageExponent s q) u =
            deningerPacketCoordinateReduction p (deningerPrimeStageAwayFactor p s q)
              (deningerFiniteFrobeniusStageExponent s q) v := by
        apply (deningerPrimeStageFactorTransport p s q).injective
        exact hfactor
      rw [haway] at hhigh
      calc
        deningerPacketCoordinateReduction p l (k + 1) u =
            ZMod.unitsMap (pow_dvd_pow (l.1 : ℕ) hK)
              (deningerPacketCoordinateReduction p l
                (deningerFiniteFrobeniusStageExponent s q) u) :=
          (deningerPacketCoordinateReduction_transition p l hK u).symm
        _ = ZMod.unitsMap (pow_dvd_pow (l.1 : ℕ) hK)
              (deningerPacketCoordinateReduction p l
                (deningerFiniteFrobeniusStageExponent s q) v) := congrArg _ hhigh
        _ = deningerPacketCoordinateReduction p l (k + 1) v :=
          deningerPacketCoordinateReduction_transition p l hK v

theorem deningerPacket_mem_frobeniusClosure_of_mem_all_finiteStages (p : Nat.Primes) (u : DeningerPacketUnits p)
    (hall : ∀ s : DeningerFiniteFrobeniusStage (p : ℕ),
      deningerPrimeFiniteStageReduction p s u ∈
        deningerFiniteFrobeniusSubgroup
          (p : ℕ) s.modulus s.coprime) :
    u ∈ deningerPacketFrobeniusClosure p := by
  by_contra huC
  let A := deningerPrimePacketCyclotomicTowerAction p
  have hAcont : Continuous A :=
    (continuous_pi fun l =>
      continuous_pi fun k =>
        deningerPrimePacketCyclotomicStageAction_continuous p l k)
  have hAinj : Function.Injective A :=
    deningerPrimePacketCyclotomicTowerAction_injective p
  have hAemb : IsEmbedding A :=
    (hAcont.isClosedEmbedding hAinj).isEmbedding
  obtain ⟨V, hVopen, hpre⟩ :=
    hAemb.isInducing.isOpen_iff.mp
      (show IsOpen
        ((deningerPacketFrobeniusClosure p :
          Set (DeningerPacketUnits p))ᶜ) from
        (inferInstance :
          IsClosed (deningerPacketFrobeniusClosure p :
            Set (DeningerPacketUnits p))).isOpen_compl)
  have huV : A u ∈ V := by
    have hucompl :
        u ∈ (deningerPacketFrobeniusClosure p :
          Set (DeningerPacketUnits p))ᶜ := huC
    rw [← hpre] at hucompl
    exact hucompl
  obtain ⟨I, U, hIU, hIV⟩ :=
    isOpen_pi_iff.mp hVopen (A u) huV
  let L := {l : {l : Nat.Primes // (l : ℕ) ≠ (p : ℕ)} // l ∈ I}
  have innerExists (li : L) :
      ∃ (K : Finset ℕ)
        (W : ∀ k : ℕ,
          Set (MulAut (DeningerPrimeArithmeticRoots p li.1.1 k))),
        (∀ k, k ∈ K →
          IsOpen (W k) ∧ A u li.1 k ∈ W k) ∧
        (K : Set ℕ).pi W ⊆ U li.1 := by
    exact isOpen_pi_iff.mp (hIU li.1 li.2).1
      (A u li.1) (hIU li.1 li.2).2
  let K : L → Finset ℕ := fun li =>
    Classical.choose (innerExists li)
  let W : ∀ li : L, ∀ k : ℕ,
      Set (MulAut (DeningerPrimeArithmeticRoots p li.1.1 k)) :=
    fun li => Classical.choose (Classical.choose_spec (innerExists li))
  have hKW (li : L) :
      (∀ k, k ∈ K li →
        IsOpen (W li k) ∧ A u li.1 k ∈ W li k) ∧
      (K li : Set ℕ).pi (W li) ⊆ U li.1 :=
    Classical.choose_spec (Classical.choose_spec (innerExists li))
  let e : L → ℕ := fun li => (K li).sup id + 1
  let n : ℕ := ∏ li : L, (li.1.1 : ℕ) ^ e li
  have hn0 : n ≠ 0 := by
    rw [show n = ∏ li : L, (li.1.1 : ℕ) ^ e li from rfl,
      Finset.prod_ne_zero_iff]
    intro li _
    exact pow_ne_zero _ li.1.1.property.ne_zero
  have hpn : (p : ℕ).Coprime n := by
    rw [Nat.coprime_fintype_prod_right_iff]
    intro li
    exact deningerPrime_coprime_awayPrime_pow p li.1 (e li)
  let s : DeningerFiniteFrobeniusStage (p : ℕ) :=
    ⟨n, hn0, hpn⟩
  have huStage := hall s
  change deningerPrimeFiniteStageReduction p s u ∈
    Subgroup.zpowers (ZMod.unitOfCoprime (p : ℕ) s.coprime) at huStage
  obtain ⟨z, hz⟩ := Subgroup.mem_zpowers_iff.mp huStage
  let w : DeningerPacketUnits p :=
    deningerPacketFrobeniusUnit p ^ z
  have hred :
      deningerPrimeFiniteStageReduction p s u = deningerPrimeFiniteStageReduction p s w := by
    change deningerPrimeFiniteStageReduction p s u =
      deningerPrimeFiniteStageReduction p s (deningerPacketFrobeniusUnit p ^ z)
    rw [map_zpow, deningerPrimeFiniteStageReduction_frobenius]
    exact hz.symm
  have hwV : A w ∈ V := by
    apply hIV
    intro l hl
    let li : L := ⟨l, hl⟩
    apply (hKW li).2
    intro k hk
    have hke : k ≤ e li := by
      change k ≤ (K li).sup (fun x : ℕ => x) + 1
      exact ((K li).le_sup (f := fun x : ℕ => x) hk).trans
        (Nat.le_succ _)
    have hfactor :
        (li.1.1 : ℕ) ^ e li ∣ n := by
      exact Finset.dvd_prod_of_mem
        (fun lj : L => (lj.1.1 : ℕ) ^ e lj)
        (Finset.mem_univ li)
    have hpow : (l.1 : ℕ) ^ k ∣ s.modulus := by
      exact dvd_trans (pow_dvd_pow (l.1 : ℕ) hke) hfactor
    have hcoord :=
      deningerPrimeFiniteStageReduction_eq_implies_coordinateReduction_eq p s l k hpow u w hred
    have haction :
        A w l k = A u l k := by
      change deningerPrimePacketCyclotomicStageAction p l k w =
        deningerPrimePacketCyclotomicStageAction p l k u
      change deningerFiniteCyclicUnitActionOfCardEq
          (DeningerPrimeArithmeticRoots p l.1 k) ((l.1 : ℕ) ^ k)
          (deningerPrimeArithmeticRoots_card p l k)
          (deningerPacketCoordinateReduction p l k w) =
        deningerFiniteCyclicUnitActionOfCardEq
          (DeningerPrimeArithmeticRoots p l.1 k) ((l.1 : ℕ) ^ k)
          (deningerPrimeArithmeticRoots_card p l k)
          (deningerPacketCoordinateReduction p l k u)
      rw [hcoord]
    rw [haction]
    exact (hKW li).1 k hk |>.2
  have hwcompl : w ∈
      (deningerPacketFrobeniusClosure p :
        Set (DeningerPacketUnits p))ᶜ := by
    rw [← hpre]
    exact hwV
  exact hwcompl
    (Subgroup.le_topologicalClosure _
      (Subgroup.zpow_mem_zpowers (deningerPacketFrobeniusUnit p) z))

/-- **Cofinality theorem.**  Membership in every finite Frobenius preimage is equivalent to
membership in the closed diagonal Frobenius subgroup. -/
theorem deningerPacketFrobeniusClosure_eq_iInf_finiteStages (p : Nat.Primes) :
    deningerPacketFrobeniusClosure p =
      ⨅ s : DeningerFiniteFrobeniusStage (p : ℕ),
        Subgroup.comap (deningerPrimeFiniteStageReduction p s)
          (deningerFiniteFrobeniusSubgroup
            (p : ℕ) s.modulus s.coprime) := by
  apply le_antisymm
  · exact le_iInf fun s => deningerPacketFrobeniusClosure_le_finiteStageReduction_comap p s
  · intro u hu
    apply deningerPacket_mem_frobeniusClosure_of_mem_all_finiteStages p u
    intro s
    exact (Subgroup.mem_iInf.mp hu) s

/-- Finite prime-to-`p` Frobenius quotient reductions jointly distinguish all literal packet
classes. -/
theorem deningerPrimeFiniteStageQuotientReduction_jointly_injective (p : Nat.Primes)
    (x y : DeningerPacketFrobeniusQuotient p)
    (hxy : ∀ s : DeningerFiniteFrobeniusStage (p : ℕ),
      deningerPrimeFiniteStageQuotientReduction p s x = deningerPrimeFiniteStageQuotientReduction p s y) :
    x = y := by
  obtain ⟨u, rfl⟩ := QuotientGroup.mk_surjective x
  obtain ⟨v, rfl⟩ := QuotientGroup.mk_surjective y
  rw [QuotientGroup.eq_iff_div_mem]
  apply deningerPacket_mem_frobeniusClosure_of_mem_all_finiteStages p (u / v)
  intro s
  have hs := hxy s
  change
    (QuotientGroup.mk (deningerPrimeFiniteStageReduction p s u) :
      DeningerFiniteFrobeniusStageQuotient (p : ℕ) s) =
    QuotientGroup.mk (deningerPrimeFiniteStageReduction p s v) at hs
  rw [QuotientGroup.eq_iff_div_mem] at hs
  simpa only [map_div] using hs

theorem deningerPrimeFiniteStageQuotientReduction_separates (p : Nat.Primes)
    {x y : DeningerPacketFrobeniusQuotient p} (hxy : x ≠ y) :
    ∃ s : DeningerFiniteFrobeniusStage (p : ℕ),
      deningerPrimeFiniteStageQuotientReduction p s x ≠ deningerPrimeFiniteStageQuotientReduction p s y := by
  by_contra hall
  push Not at hall
  exact hxy (deningerPrimeFiniteStageQuotientReduction_jointly_injective p x y hall)

noncomputable def deningerPrimeFiniteStageRealPullback (p : Nat.Primes)
    (s : DeningerFiniteFrobeniusStage (p : ℕ))
    (F : DeningerFiniteFrobeniusStageQuotient (p : ℕ) s → ℝ) :
    C(DeningerPacketFrobeniusQuotient p, ℝ) where
  toFun x := F (deningerPrimeFiniteStageQuotientReduction p s x)
  continuous_toFun :=
    continuous_of_discreteTopology.comp
      (deningerPrimeFiniteStageQuotientReduction_continuous p s)

def deningerPrimeFiniteStageRealGenerator (p : Nat.Primes) :
    Set C(DeningerPacketFrobeniusQuotient p, ℝ) :=
  {f | ∃ (s : DeningerFiniteFrobeniusStage (p : ℕ))
    (F : DeningerFiniteFrobeniusStageQuotient (p : ℕ) s → ℝ),
      f = deningerPrimeFiniteStageRealPullback p s F}

noncomputable def deningerPrimeFiniteStageGeneratedAlgebra (p : Nat.Primes) :
    Subalgebra ℝ C(DeningerPacketFrobeniusQuotient p, ℝ) :=
  Algebra.adjoin ℝ (deningerPrimeFiniteStageRealGenerator p)

theorem deningerPrimeFiniteStageGeneratedAlgebra_separates (p : Nat.Primes) :
    (deningerPrimeFiniteStageGeneratedAlgebra p).SeparatesPoints := by
  classical
  intro x y hxy
  obtain ⟨s, hs⟩ := deningerPrimeFiniteStageQuotientReduction_separates p hxy
  let F : DeningerFiniteFrobeniusStageQuotient (p : ℕ) s → ℝ :=
    fun q => if q = deningerPrimeFiniteStageQuotientReduction p s x then 0 else 1
  let f := deningerPrimeFiniteStageRealPullback p s F
  refine ⟨(f : DeningerPacketFrobeniusQuotient p → ℝ), ?_, ?_⟩
  · refine ⟨f, ?_, rfl⟩
    exact Algebra.subset_adjoin ⟨s, F, rfl⟩
  · change F (deningerPrimeFiniteStageQuotientReduction p s x) ≠
      F (deningerPrimeFiniteStageQuotientReduction p s y)
    have hsy :
        deningerPrimeFiniteStageQuotientReduction p s y ≠ deningerPrimeFiniteStageQuotientReduction p s x :=
      Ne.symm hs
    simp [F, hsy]

theorem deningerPrimeFiniteStageGeneratedAlgebra_dense (p : Nat.Primes) :
    (deningerPrimeFiniteStageGeneratedAlgebra p).topologicalClosure = ⊤ :=
  ContinuousMap.subalgebra_topologicalClosure_eq_top_of_separatesPoints
    (deningerPrimeFiniteStageGeneratedAlgebra p)
    (deningerPrimeFiniteStageGeneratedAlgebra_separates p)

theorem deningerPrimeFiniteStageGeneratedAlgebra_exists_near (p : Nat.Primes)
    (f : C(DeningerPacketFrobeniusQuotient p, ℝ))
    (ε : ℝ) (hε : 0 < ε) :
    ∃ g : deningerPrimeFiniteStageGeneratedAlgebra p,
      ‖(g : C(DeningerPacketFrobeniusQuotient p, ℝ)) - f‖ < ε :=
  ContinuousMap.exists_mem_subalgebra_near_continuousMap_of_separatesPoints
    (deningerPrimeFiniteStageGeneratedAlgebra p)
    (deningerPrimeFiniteStageGeneratedAlgebra_separates p) f ε hε

noncomputable def deningerPrimeFiniteStageOrbitEvaluation (p : Nat.Primes)
    (s : DeningerFiniteFrobeniusStage (p : ℕ))
    (j : ZMod s.modulus)
    (x : DeningerPacketFrobeniusQuotient p) : ℂ :=
  deningerFiniteFrobeniusOrbitEvaluation
    (p : ℕ) s.modulus s.coprime j
    (deningerPrimeFiniteStageQuotientReduction p s x)

theorem deningerPrimeFiniteStageComplexPullback_orbitEvaluation_span
    (p : Nat.Primes)
    (s : DeningerFiniteFrobeniusStage (p : ℕ))
    (F : DeningerFiniteFrobeniusStageQuotient (p : ℕ) s → ℂ) :
    ∃ c : ZMod s.modulus → ℂ,
      ∀ x : DeningerPacketFrobeniusQuotient p,
        F (deningerPrimeFiniteStageQuotientReduction p s x) =
          ∑ j : ZMod s.modulus,
            c j * deningerPrimeFiniteStageOrbitEvaluation p s j x := by
  obtain ⟨c, hc⟩ :=
    deningerFiniteFrobeniusOrbitEvaluation_span
      (p : ℕ) s.modulus s.coprime F
  exact ⟨c, fun x => hc (deningerPrimeFiniteStageQuotientReduction p s x)⟩

theorem deningerPrimeFiniteStageReduction_eq_of_le (p : Nat.Primes)
    {s t : DeningerFiniteFrobeniusStage (p : ℕ)} (hst : s ≤ t)
    {u v : DeningerPacketUnits p}
    (huv : deningerPrimeFiniteStageReduction p t u = deningerPrimeFiniteStageReduction p t v) :
    deningerPrimeFiniteStageReduction p s u = deningerPrimeFiniteStageReduction p s v := by
  apply (deningerFiniteFrobeniusStageCRTMulEquiv s).injective
  funext q
  change deningerFiniteFrobeniusStageCRTMulEquiv s ((deningerFiniteFrobeniusStageCRTMulEquiv s).symm (deningerPrimeStageFactorReductionTuple p s u)) q =
    deningerFiniteFrobeniusStageCRTMulEquiv s ((deningerFiniteFrobeniusStageCRTMulEquiv s).symm (deningerPrimeStageFactorReductionTuple p s v)) q
  rw [MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply]
  change deningerPrimeStageFactorReduction p s q u = deningerPrimeStageFactorReduction p s q v
  exact congrArg (deningerPrimeStageFactorTransport p s q)
    (deningerPrimeFiniteStageReduction_eq_implies_coordinateReduction_eq p t
      (deningerPrimeStageAwayFactor p s q) (deningerFiniteFrobeniusStageExponent s q)
      (dvd_trans (deningerFiniteStageFactor_dvd p s q) hst) u v huv)

theorem deningerPrimeFiniteStageQuotientReduction_eq_of_le (p : Nat.Primes)
    {s t : DeningerFiniteFrobeniusStage (p : ℕ)} (hst : s ≤ t)
    {x y : DeningerPacketFrobeniusQuotient p}
    (hxy : deningerPrimeFiniteStageQuotientReduction p t x =
      deningerPrimeFiniteStageQuotientReduction p t y) :
    deningerPrimeFiniteStageQuotientReduction p s x = deningerPrimeFiniteStageQuotientReduction p s y := by
  obtain ⟨u, rfl⟩ := QuotientGroup.mk_surjective x
  obtain ⟨v, rfl⟩ := QuotientGroup.mk_surjective y
  change
    (QuotientGroup.mk (deningerPrimeFiniteStageReduction p t u) :
      DeningerFiniteFrobeniusStageQuotient (p : ℕ) t) =
    QuotientGroup.mk (deningerPrimeFiniteStageReduction p t v) at hxy
  rw [QuotientGroup.eq_iff_div_mem] at hxy
  change deningerPrimeFiniteStageReduction p t u / deningerPrimeFiniteStageReduction p t v ∈
    Subgroup.zpowers (ZMod.unitOfCoprime (p : ℕ) t.coprime) at hxy
  obtain ⟨z, hz⟩ := Subgroup.mem_zpowers_iff.mp hxy
  let w : DeningerPacketUnits p :=
    v * deningerPacketFrobeniusUnit p ^ z
  have htuw :
      deningerPrimeFiniteStageReduction p t u = deningerPrimeFiniteStageReduction p t w := by
    change deningerPrimeFiniteStageReduction p t u =
      deningerPrimeFiniteStageReduction p t
        (v * deningerPacketFrobeniusUnit p ^ z)
    rw [map_mul, map_zpow, deningerPrimeFiniteStageReduction_frobenius]
    calc
      deningerPrimeFiniteStageReduction p t u =
          (deningerPrimeFiniteStageReduction p t u / deningerPrimeFiniteStageReduction p t v) *
            deningerPrimeFiniteStageReduction p t v := (div_mul_cancel _ _).symm
      _ = ZMod.unitOfCoprime (p : ℕ) t.coprime ^ z *
          deningerPrimeFiniteStageReduction p t v := by rw [hz]
      _ = deningerPrimeFiniteStageReduction p t v *
          ZMod.unitOfCoprime (p : ℕ) t.coprime ^ z := mul_comm _ _
  have hsuw :
      deningerPrimeFiniteStageReduction p s u = deningerPrimeFiniteStageReduction p s w :=
    deningerPrimeFiniteStageReduction_eq_of_le p hst htuw
  change
    (QuotientGroup.mk (deningerPrimeFiniteStageReduction p s u) :
      DeningerFiniteFrobeniusStageQuotient (p : ℕ) s) =
    QuotientGroup.mk (deningerPrimeFiniteStageReduction p s v)
  rw [hsuw]
  rw [QuotientGroup.eq_iff_div_mem]
  change deningerPrimeFiniteStageReduction p s w / deningerPrimeFiniteStageReduction p s v ∈
    Subgroup.zpowers (ZMod.unitOfCoprime (p : ℕ) s.coprime)
  change
    deningerPrimeFiniteStageReduction p s
      (v * deningerPacketFrobeniusUnit p ^ z) /
        deningerPrimeFiniteStageReduction p s v ∈
      Subgroup.zpowers (ZMod.unitOfCoprime (p : ℕ) s.coprime)
  rw [map_mul, map_zpow, deningerPrimeFiniteStageReduction_frobenius, mul_div_cancel_left]
  exact Subgroup.zpow_mem_zpowers _ z

noncomputable def deningerPrimeFiniteStageQuotientFactor (p : Nat.Primes)
    {s t : DeningerFiniteFrobeniusStage (p : ℕ)} (_hst : s ≤ t)
    (q : DeningerFiniteFrobeniusStageQuotient (p : ℕ) t) :
    DeningerFiniteFrobeniusStageQuotient (p : ℕ) s :=
  deningerPrimeFiniteStageQuotientReduction p s
    (Classical.choose (deningerPrimeFiniteStageQuotientReduction_surjective p t q))

theorem deningerPrimeFiniteStageQuotientFactor_spec (p : Nat.Primes)
    {s t : DeningerFiniteFrobeniusStage (p : ℕ)} (hst : s ≤ t)
    (x : DeningerPacketFrobeniusQuotient p) :
    deningerPrimeFiniteStageQuotientFactor p hst
        (deningerPrimeFiniteStageQuotientReduction p t x) =
      deningerPrimeFiniteStageQuotientReduction p s x := by
  apply deningerPrimeFiniteStageQuotientReduction_eq_of_le p hst
  exact Classical.choose_spec
    (deningerPrimeFiniteStageQuotientReduction_surjective p t (deningerPrimeFiniteStageQuotientReduction p t x))

/-- Real continuous functions that factor through one finite cyclotomic Frobenius quotient.
Directed refinement makes this union of finite-dimensional spaces a subalgebra. -/
noncomputable def deningerPrimeFiniteStageRealSubalgebra (p : Nat.Primes) :
    Subalgebra ℝ C(DeningerPacketFrobeniusQuotient p, ℝ) where
  carrier := deningerPrimeFiniteStageRealGenerator p
  zero_mem' := by
    let s : DeningerFiniteFrobeniusStage (p : ℕ) :=
      ⟨1, one_ne_zero, Nat.coprime_one_right (p : ℕ)⟩
    exact ⟨s, 0, by ext; rfl⟩
  one_mem' := by
    let s : DeningerFiniteFrobeniusStage (p : ℕ) :=
      ⟨1, one_ne_zero, Nat.coprime_one_right (p : ℕ)⟩
    exact ⟨s, 1, by ext; rfl⟩
  add_mem' := by
    rintro f g ⟨s, F, rfl⟩ ⟨t, G, rfl⟩
    obtain ⟨r, hsr, htr⟩ := exists_ge_ge s t
    let H :
        DeningerFiniteFrobeniusStageQuotient (p : ℕ) r → ℝ :=
      fun q =>
        F (deningerPrimeFiniteStageQuotientFactor p hsr q) +
          G (deningerPrimeFiniteStageQuotientFactor p htr q)
    refine ⟨r, H, ?_⟩
    ext x
    change
      F (deningerPrimeFiniteStageQuotientReduction p s x) +
          G (deningerPrimeFiniteStageQuotientReduction p t x) =
        F (deningerPrimeFiniteStageQuotientFactor p hsr
            (deningerPrimeFiniteStageQuotientReduction p r x)) +
          G (deningerPrimeFiniteStageQuotientFactor p htr
            (deningerPrimeFiniteStageQuotientReduction p r x))
    rw [deningerPrimeFiniteStageQuotientFactor_spec,
      deningerPrimeFiniteStageQuotientFactor_spec]
  mul_mem' := by
    rintro f g ⟨s, F, rfl⟩ ⟨t, G, rfl⟩
    obtain ⟨r, hsr, htr⟩ := exists_ge_ge s t
    let H :
        DeningerFiniteFrobeniusStageQuotient (p : ℕ) r → ℝ :=
      fun q =>
        F (deningerPrimeFiniteStageQuotientFactor p hsr q) *
          G (deningerPrimeFiniteStageQuotientFactor p htr q)
    refine ⟨r, H, ?_⟩
    ext x
    change
      F (deningerPrimeFiniteStageQuotientReduction p s x) *
          G (deningerPrimeFiniteStageQuotientReduction p t x) =
        F (deningerPrimeFiniteStageQuotientFactor p hsr
            (deningerPrimeFiniteStageQuotientReduction p r x)) *
          G (deningerPrimeFiniteStageQuotientFactor p htr
            (deningerPrimeFiniteStageQuotientReduction p r x))
    rw [deningerPrimeFiniteStageQuotientFactor_spec,
      deningerPrimeFiniteStageQuotientFactor_spec]
  algebraMap_mem' a := by
    let s : DeningerFiniteFrobeniusStage (p : ℕ) :=
      ⟨1, one_ne_zero, Nat.coprime_one_right (p : ℕ)⟩
    refine ⟨s, fun _ => a, ?_⟩
    ext x
    change a = a
    rfl

theorem deningerPrimeFiniteStageRealSubalgebra_separates (p : Nat.Primes) :
    (deningerPrimeFiniteStageRealSubalgebra p).SeparatesPoints := by
  classical
  intro x y hxy
  obtain ⟨s, hs⟩ := deningerPrimeFiniteStageQuotientReduction_separates p hxy
  let F : DeningerFiniteFrobeniusStageQuotient (p : ℕ) s → ℝ :=
    fun q => if q = deningerPrimeFiniteStageQuotientReduction p s x then 0 else 1
  let f := deningerPrimeFiniteStageRealPullback p s F
  refine ⟨(f : DeningerPacketFrobeniusQuotient p → ℝ), ?_, ?_⟩
  · exact ⟨f, ⟨s, F, rfl⟩, rfl⟩
  · change F (deningerPrimeFiniteStageQuotientReduction p s x) ≠
      F (deningerPrimeFiniteStageQuotientReduction p s y)
    have hsy :
        deningerPrimeFiniteStageQuotientReduction p s y ≠ deningerPrimeFiniteStageQuotientReduction p s x :=
      Ne.symm hs
    simp [F, hsy]

/-- One-stage finite cyclotomic pullbacks are uniformly dense in all real continuous packet
functions. -/
theorem deningerPrimeFiniteStageRealSubalgebra_dense (p : Nat.Primes) :
    (deningerPrimeFiniteStageRealSubalgebra p).topologicalClosure = ⊤ :=
  ContinuousMap.subalgebra_topologicalClosure_eq_top_of_separatesPoints
    (deningerPrimeFiniteStageRealSubalgebra p)
    (deningerPrimeFiniteStageRealSubalgebra_separates p)

theorem deningerPrimeFiniteStageRealSubalgebra_exists_near (p : Nat.Primes)
    (f : C(DeningerPacketFrobeniusQuotient p, ℝ))
    (ε : ℝ) (hε : 0 < ε) :
    ∃ g : deningerPrimeFiniteStageRealSubalgebra p,
      ‖(g : C(DeningerPacketFrobeniusQuotient p, ℝ)) - f‖ < ε :=
  ContinuousMap.exists_mem_subalgebra_near_continuousMap_of_separatesPoints
    (deningerPrimeFiniteStageRealSubalgebra p)
    (deningerPrimeFiniteStageRealSubalgebra_separates p) f ε hε

/-- Every element of the dense finite-stage subalgebra is one exact finite linear combination of
pulled-back Frobenius-orbit root evaluations. -/
theorem deningerPrimeFiniteStageRealSubalgebra_orbitEvaluation_span
    (p : Nat.Primes) (g : deningerPrimeFiniteStageRealSubalgebra p) :
    ∃ (s : DeningerFiniteFrobeniusStage (p : ℕ))
      (c : ZMod s.modulus → ℂ),
      ∀ x : DeningerPacketFrobeniusQuotient p,
        (((g : C(DeningerPacketFrobeniusQuotient p, ℝ)) x : ℝ) : ℂ) =
          ∑ j : ZMod s.modulus,
            c j * deningerPrimeFiniteStageOrbitEvaluation p s j x := by
  obtain ⟨s, F, hg⟩ := g.property
  obtain ⟨c, hc⟩ :=
    deningerPrimeFiniteStageComplexPullback_orbitEvaluation_span p s
      (fun q => (F q : ℂ))
  refine ⟨s, c, ?_⟩
  intro x
  rw [show (g : C(DeningerPacketFrobeniusQuotient p, ℝ)) =
      deningerPrimeFiniteStageRealPullback p s F from hg]
  exact hc x

/-- Canonical inclusion of finite-stage real packet functions into normalized Haar `L²`. -/
def deningerPrimeFiniteStageRealSubalgebraToHaarL2 (p : Nat.Primes) :
    deningerPrimeFiniteStageRealSubalgebra p →L[ℝ]
      DeningerPrimePacketHaarL2 p :=
  (deningerPrimePacketContinuousToHaarL2 p).comp
    (deningerPrimeFiniteStageRealSubalgebra p).toSubmodule.subtypeL

/-- **Haar completeness of finite source modes.**  Finite cyclotomic packet functions, hence
finite orbit-evaluation combinations, are dense in the full packet Haar `L²` fibre. -/
theorem deningerPrimeFiniteStageRealSubalgebraToHaarL2_denseRange
    (p : Nat.Primes) :
    DenseRange (deningerPrimeFiniteStageRealSubalgebraToHaarL2 p) := by
  letI : (deningerPrimePacketHaarMeasure p).Regular := by
    unfold deningerPrimePacketHaarMeasure
    infer_instance
  letI : (deningerPrimePacketHaarMeasure p).WeaklyRegular :=
    inferInstance
  have hDense :
      Dense (deningerPrimeFiniteStageRealSubalgebra p :
        Set C(DeningerPacketFrobeniusQuotient p, ℝ)) := by
    rw [dense_iff_closure_eq,
      ← Subalgebra.topologicalClosure_coe,
      deningerPrimeFiniteStageRealSubalgebra_dense]
    rfl
  have hSubtype :
      DenseRange
        ((deningerPrimeFiniteStageRealSubalgebra p).toSubmodule.subtypeL :
          deningerPrimeFiniteStageRealSubalgebra p →L[ℝ]
            C(DeningerPacketFrobeniusQuotient p, ℝ)) :=
    hDense.denseRange_val
  have hLp :
      DenseRange (deningerPrimePacketContinuousToHaarL2 p) :=
    ContinuousMap.toLp_denseRange ℝ
      (deningerPrimePacketHaarMeasure p) ℝ (by norm_num)
  exact hLp.comp hSubtype
    (deningerPrimePacketContinuousToHaarL2 p).continuous

end
end RHTower
