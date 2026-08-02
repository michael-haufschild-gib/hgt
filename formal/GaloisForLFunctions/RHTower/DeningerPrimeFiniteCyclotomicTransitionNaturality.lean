import GaloisForLFunctions.RHTower.DeningerPrimeFiniteCyclotomicReductionSystem

/-!
# Canonical transition naturality for finite Deninger packet reductions

The literal Deninger packet reduction at a prime-to-`p` modulus is assembled independently
from prime-power `ℓ`-adic coordinates by CRT.  This module proves that those independently
assembled reductions commute with the canonical `ZMod.unitsMap` along every divisibility
transition.

The proof is not a formal consequence of the previously known fiber-monotonicity theorem.
It compares the prime-factor refinements, transports their `ℓ`-adic coordinate reductions
through unequal CRT presentations, and proves the resulting ring-hom square by uniqueness.

Consequently the finite reductions of the actual packet form the canonical inverse system,
and the older choice-defined quotient factor is exactly the canonical Frobenius-stage map.
-/

namespace RHTower

open Set
open Topology

noncomputable section

/-- A CRT coordinate is the canonical unit reduction to the corresponding prime-power
factor. -/
theorem deningerFiniteFrobeniusStageCRT_component
    (p : Nat.Primes)
    (s : DeningerFiniteFrobeniusStage (p : ℕ))
    (q : s.modulus.primeFactors) (v : (ZMod s.modulus)ˣ) :
    deningerFiniteFrobeniusStageCRTMulEquiv s v q =
      ZMod.unitsMap (deningerFiniteStageFactor_dvd p s q) v := by
  apply Units.ext
  change
    ZMod.equivPi s.modulus s.modulus_ne_zero
        (v : ZMod s.modulus) q =
      ZMod.cast (v : ZMod s.modulus)
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
  exact (RingHom.congr_fun hhom (v : ZMod s.modulus)).symm

/-- A prime factor of a smaller stage, regarded as a prime factor of a divisible larger
stage. -/
def deningerPrimeStageFactorRefinement
    (p : Nat.Primes)
    {s t : DeningerFiniteFrobeniusStage (p : ℕ)} (hst : s ≤ t)
    (q : s.modulus.primeFactors) : t.modulus.primeFactors :=
  ⟨(q : ℕ), Nat.mem_primeFactors.mpr
    ⟨(Nat.mem_primeFactors.mp q.property).1,
      dvd_trans (Nat.mem_primeFactors.mp q.property).2.1 hst,
      t.modulus_ne_zero⟩⟩

/-- Prime-factor multiplicity is monotone along a stage refinement. -/
theorem deningerPrimeStageFactorRefinement_exponent_le
    (p : Nat.Primes)
    {s t : DeningerFiniteFrobeniusStage (p : ℕ)} (hst : s ≤ t)
    (q : s.modulus.primeFactors) :
    deningerFiniteFrobeniusStageExponent s q ≤
      deningerFiniteFrobeniusStageExponent t
        (deningerPrimeStageFactorRefinement p hst q) := by
  exact ((Nat.mem_primeFactors.mp q.property).1.pow_dvd_iff_le_factorization
    t.modulus_ne_zero).mp
      (dvd_trans (deningerFiniteStageFactor_dvd p s q) hst)

/-- Refining a prime factor does not change its underlying away-prime packet coordinate. -/
theorem deningerPrimeStageFactorRefinement_away
    (p : Nat.Primes)
    {s t : DeningerFiniteFrobeniusStage (p : ℕ)} (hst : s ≤ t)
    (q : s.modulus.primeFactors) :
    deningerPrimeStageAwayFactor p t
        (deningerPrimeStageFactorRefinement p hst q) =
      deningerPrimeStageAwayFactor p s q := by
  rfl

/-- Coordinate reduction respects equality of the typed away-prime index, including its
induced equality of prime-power moduli. -/
theorem deningerPacketCoordinateReduction_congr
    (p : Nat.Primes)
    (l₁ l₂ : {l : Nat.Primes // (l : ℕ) ≠ (p : ℕ)})
    (hl : l₁ = l₂) (k : ℕ) (u : DeningerPacketUnits p) :
    ZMod.ringEquivCongr
        (congrArg (fun l :
          {l : Nat.Primes // (l : ℕ) ≠ (p : ℕ)} =>
            (l.1 : ℕ) ^ k) hl)
        (((deningerPacketCoordinateReduction p l₁ k u :
          (ZMod ((l₁.1 : ℕ) ^ k))ˣ) : ZMod ((l₁.1 : ℕ) ^ k))) =
      ((deningerPacketCoordinateReduction p l₂ k u :
        (ZMod ((l₂.1 : ℕ) ^ k))ˣ) : ZMod ((l₂.1 : ℕ) ^ k)) := by
  subst l₂
  exact ZMod.ringEquivCongr_refl_apply _

/-- Prime-power factors of the CRT packet reduction commute with refinement. -/
theorem deningerPrimeStageFactorReduction_transition
    (p : Nat.Primes)
    {s t : DeningerFiniteFrobeniusStage (p : ℕ)} (hst : s ≤ t)
    (q : s.modulus.primeFactors) (u : DeningerPacketUnits p) :
    ZMod.unitsMap
        (pow_dvd_pow (q : ℕ)
          (deningerPrimeStageFactorRefinement_exponent_le p hst q))
        (deningerPrimeStageFactorReduction p t
          (deningerPrimeStageFactorRefinement p hst q) u) =
      deningerPrimeStageFactorReduction p s q u := by
  let qt := deningerPrimeStageFactorRefinement p hst q
  let lₜ := deningerPrimeStageAwayFactor p t qt
  let lₛ := deningerPrimeStageAwayFactor p s q
  let eₜ := deningerFiniteFrobeniusStageExponent t qt
  let eₛ := deningerFiniteFrobeniusStageExponent s q
  have he : eₛ ≤ eₜ :=
    deningerPrimeStageFactorRefinement_exponent_le p hst q
  have hl : lₜ = lₛ := by
    exact deningerPrimeStageFactorRefinement_away p hst q
  have hqₜ :
      ((lₜ.1 : ℕ) ^ eₜ) =
        ((qt : ℕ) ^ eₜ) :=
    deningerPrimeStageFactorModulus_eq p t qt
  have hqₛ :
      ((lₛ.1 : ℕ) ^ eₛ) =
        ((q : ℕ) ^ eₛ) :=
    deningerPrimeStageFactorModulus_eq p s q
  have hlₛ :
      ((lₜ.1 : ℕ) ^ eₛ) =
        ((lₛ.1 : ℕ) ^ eₛ) :=
    congrArg (fun l :
      {l : Nat.Primes // (l : ℕ) ≠ (p : ℕ)} =>
        (l.1 : ℕ) ^ eₛ) hl
  have hring :
      (ZMod.castHom
          (pow_dvd_pow (q : ℕ) he)
          (ZMod ((q : ℕ) ^ eₛ))).comp
          (ZMod.ringEquivCongr hqₜ).toRingHom =
        (ZMod.ringEquivCongr hqₛ).toRingHom.comp
          ((ZMod.ringEquivCongr hlₛ).toRingHom.comp
            (ZMod.castHom
              (pow_dvd_pow (lₜ.1 : ℕ) he)
              (ZMod ((lₜ.1 : ℕ) ^ eₛ)))) := by
    exact Subsingleton.elim _ _
  let xₜ : ZMod ((lₜ.1 : ℕ) ^ eₜ) :=
    ((deningerPacketCoordinateReduction p lₜ eₜ u :
      (ZMod ((lₜ.1 : ℕ) ^ eₜ))ˣ) :
        ZMod ((lₜ.1 : ℕ) ^ eₜ))
  let xₛ : ZMod ((lₛ.1 : ℕ) ^ eₛ) :=
    ((deningerPacketCoordinateReduction p lₛ eₛ u :
      (ZMod ((lₛ.1 : ℕ) ^ eₛ))ˣ) :
        ZMod ((lₛ.1 : ℕ) ^ eₛ))
  apply Units.ext
  change
    ZMod.castHom (pow_dvd_pow (q : ℕ) he)
        (ZMod ((q : ℕ) ^ eₛ))
        (ZMod.ringEquivCongr hqₜ xₜ) =
      ZMod.ringEquivCongr hqₛ xₛ
  have hring_apply := RingHom.congr_fun hring xₜ
  rw [RingHom.comp_apply, RingHom.comp_apply,
    RingHom.comp_apply] at hring_apply
  have hcoord := congrArg Units.val
    (deningerPacketCoordinateReduction_transition p lₜ he u)
  change
    ZMod.castHom (pow_dvd_pow (lₜ.1 : ℕ) he)
        (ZMod ((lₜ.1 : ℕ) ^ eₛ)) xₜ =
      ((deningerPacketCoordinateReduction p lₜ eₛ u :
        (ZMod ((lₜ.1 : ℕ) ^ eₛ))ˣ) :
          ZMod ((lₜ.1 : ℕ) ^ eₛ)) at hcoord
  have hcongr :
      ZMod.ringEquivCongr hlₛ
          (((deningerPacketCoordinateReduction p lₜ eₛ u :
            (ZMod ((lₜ.1 : ℕ) ^ eₛ))ˣ) :
              ZMod ((lₜ.1 : ℕ) ^ eₛ))) =
        xₛ := by
    simpa only [xₛ] using
      deningerPacketCoordinateReduction_congr p lₜ lₛ hl eₛ u
  calc
    _ = ZMod.ringEquivCongr hqₛ
          (ZMod.ringEquivCongr hlₛ
            (ZMod.castHom (pow_dvd_pow (lₜ.1 : ℕ) he)
              (ZMod ((lₜ.1 : ℕ) ^ eₛ)) xₜ)) := hring_apply
    _ = ZMod.ringEquivCongr hqₛ
          (ZMod.ringEquivCongr hlₛ
            (((deningerPacketCoordinateReduction p lₜ eₛ u :
              (ZMod ((lₜ.1 : ℕ) ^ eₛ))ˣ) :
                ZMod ((lₜ.1 : ℕ) ^ eₛ)))) := by
        exact congrArg (ZMod.ringEquivCongr hqₛ)
          (congrArg (ZMod.ringEquivCongr hlₛ) hcoord)
    _ = _ := congrArg (ZMod.ringEquivCongr hqₛ) hcongr

/-- **Canonical CRT naturality.** Literal packet reduction commutes with every canonical
finite-stage unit reduction. -/
theorem deningerPrimeFiniteStageReduction_transition
    (p : Nat.Primes)
    {s t : DeningerFiniteFrobeniusStage (p : ℕ)} (hst : s ≤ t)
    (u : DeningerPacketUnits p) :
    deningerFiniteFrobeniusStageReduction hst
        (deningerPrimeFiniteStageReduction p t u) =
      deningerPrimeFiniteStageReduction p s u := by
  apply (deningerFiniteFrobeniusStageCRTMulEquiv s).injective
  funext q
  rw [deningerFiniteFrobeniusStageCRT_component p s q,
    deningerFiniteFrobeniusStageCRT_component p s q,
    deningerFiniteFrobeniusStageReduction]
  let qt := deningerPrimeStageFactorRefinement p hst q
  have he :
      deningerFiniteFrobeniusStageExponent s q ≤
        deningerFiniteFrobeniusStageExponent t qt :=
    deningerPrimeStageFactorRefinement_exponent_le p hst q
  calc
    ZMod.unitsMap (deningerFiniteStageFactor_dvd p s q)
        (ZMod.unitsMap hst (deningerPrimeFiniteStageReduction p t u)) =
      ZMod.unitsMap
          (pow_dvd_pow (q : ℕ) he)
          (ZMod.unitsMap (deningerFiniteStageFactor_dvd p t qt)
            (deningerPrimeFiniteStageReduction p t u)) := by
        have hleft := congrArg
          (fun f => f (deningerPrimeFiniteStageReduction p t u))
          (ZMod.unitsMap_comp
            (deningerFiniteStageFactor_dvd p s q) hst)
        have hright := congrArg
          (fun f => f (deningerPrimeFiniteStageReduction p t u))
          (ZMod.unitsMap_comp
            (pow_dvd_pow (q : ℕ) he)
            (deningerFiniteStageFactor_dvd p t qt))
        rw [MonoidHom.comp_apply] at hleft hright
        exact hleft.trans hright.symm
    _ = ZMod.unitsMap (pow_dvd_pow (q : ℕ) he)
          (deningerPrimeStageFactorReduction p t qt u) := by
        rw [deningerPrimeFiniteStageReduction_component p t qt u]
    _ = deningerPrimeStageFactorReduction p s q u := by
        exact deningerPrimeStageFactorReduction_transition p hst q u
    _ = ZMod.unitsMap (deningerFiniteStageFactor_dvd p s q)
          (deningerPrimeFiniteStageReduction p s u) := by
        exact (deningerPrimeFiniteStageReduction_component p s q u).symm

/-- The actual packet quotient reductions commute with canonical finite Frobenius quotient
transitions. -/
theorem deningerPrimeFiniteStageQuotientReduction_transition
    (p : Nat.Primes)
    {s t : DeningerFiniteFrobeniusStage (p : ℕ)} (hst : s ≤ t)
    (x : DeningerPacketFrobeniusQuotient p) :
    deningerFiniteFrobeniusStageQuotientMap hst
        (deningerPrimeFiniteStageQuotientReduction p t x) =
      deningerPrimeFiniteStageQuotientReduction p s x := by
  obtain ⟨u, rfl⟩ := QuotientGroup.mk_surjective x
  change
    QuotientGroup.mk
        (deningerFiniteFrobeniusStageReduction hst
          (deningerPrimeFiniteStageReduction p t u)) =
      QuotientGroup.mk (deningerPrimeFiniteStageReduction p s u)
  rw [deningerPrimeFiniteStageReduction_transition p hst u]

/-- The old choice-defined finite quotient factor is extensionally the canonical arithmetic
Frobenius-stage transition. -/
theorem deningerPrimeFiniteStageQuotientFactor_eq_canonical
    (p : Nat.Primes)
    {s t : DeningerFiniteFrobeniusStage (p : ℕ)} (hst : s ≤ t) :
    deningerPrimeFiniteStageQuotientFactor p hst =
      deningerFiniteFrobeniusStageQuotientMap hst := by
  funext q
  obtain ⟨x, rfl⟩ :=
    deningerPrimeFiniteStageQuotientReduction_surjective p t q
  rw [deningerPrimeFiniteStageQuotientFactor_spec,
    deningerPrimeFiniteStageQuotientReduction_transition]

end

end RHTower
