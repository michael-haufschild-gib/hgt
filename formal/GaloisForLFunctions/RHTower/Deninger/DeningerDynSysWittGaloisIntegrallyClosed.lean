/-
Deninger, *Dynamical systems for arithmetic schemes* (arXiv:1807.06400v4), Proposition 1.2(b)
(`t21n`), integrally closed domain case:

`W_rat (A ^ G) = W_rat (A) ^ G`  for `A` an integrally closed domain and `G` an arbitrary group of
ring automorphisms — in series form, in polynomial form, and for the rational Witt ring itself.

The source's argument is followed.  The action of `G` extends to the fraction field `K`, where the
field case gives a **coprime** `G`-invariant normalized presentation `P₁ / Q₁` of the vector.
Bézout for `P₁, Q₁` together with the cross relation `P₁ Q = Q₁ P` shows `P₁ ∣ P` and `Q₁ ∣ Q` in
`K[t]`.  Reversing turns `P` into a *monic* polynomial over `A` and `P₁` into a monic divisor of it
over `K`; since `A` is integrally closed, such a divisor already has coefficients in `A`
(`IsIntegrallyClosed.eq_map_mul_C_of_dvd`).  Reversing back, `P₁` and `Q₁` have coefficients in
`A`, and being `G`-invariant they have coefficients in `A ^ G`.

The reversal lemmas (`deningerReverse_map`, `deningerReverse_monic`,
`deningerCoeff_mem_range_of_reverse`) are stated separately; they are the standard device turning
"constant coefficient one" into "monic".

Together with `deningerWittRing_galoisDescent` (the finite-orbit case) this closes Proposition 1.2
in full.
-/
import Mathlib.RingTheory.Polynomial.GaussLemma
import Mathlib.RingTheory.Localization.FractionRing
import GaloisForLFunctions.RHTower.Deninger.DeningerDynSysWittGaloisField
import GaloisForLFunctions.RHTower.Deninger.DeningerDynSysWittRingDescent

namespace RHTower

open Polynomial

/-- Reversal commutes with an injective coefficient map. -/
theorem deningerReverse_map {R S : Type*} [Semiring R] [Semiring S] (f : R →+* S)
    (hf : Function.Injective f) (p : Polynomial R) :
    (p.map f).reverse = p.reverse.map f := by
  ext n
  simp only [Polynomial.coeff_reverse, Polynomial.coeff_map,
    Polynomial.natDegree_map_eq_of_injective hf]

/-- The reverse of a polynomial with constant coefficient one is monic. -/
theorem deningerReverse_monic {R : Type*} [Semiring R] {p : Polynomial R} (h : p.coeff 0 = 1) :
    p.reverse.Monic := by
  refine Polynomial.monic_of_natDegree_le_of_coeff_eq_one p.natDegree
    (Polynomial.reverse_natDegree_le p) ?_
  rw [Polynomial.coeff_reverse, Polynomial.revAt_le le_rfl, Nat.sub_self]
  exact h

/-- If the reverse of `p` lifts along `f`, so does `p`. -/
theorem deningerCoeff_mem_range_of_reverse {R S : Type*} [Semiring R] [Semiring S] (f : R →+* S)
    {p : Polynomial S} (h : ∀ n, p.reverse.coeff n ∈ Set.range f) (n : ℕ) :
    p.coeff n ∈ Set.range f := by
  have := h (Polynomial.revAt p.natDegree n)
  rwa [Polynomial.coeff_reverse, Polynomial.revAt_invol] at this

/-- **Deninger, Proposition 1.2(b) (`t21n`), integrally closed domain case.**  For a group `G`
acting by ring automorphisms on an integrally closed domain `A`, every `G`-invariant rational Witt
vector over `A` has a normalized presentation with `G`-invariant coefficients, i.e.
`W_rat (A ^ G) = W_rat (A) ^ G`. -/
theorem deningerRationalSeries_galoisDescent_integrallyClosed
    {G A : Type*} [Group G] [CommRing A] [IsDomain A] [IsIntegrallyClosed A]
    [MulSemiringAction G A] (F : PowerSeries A)
    (hF : ∀ (σ : G) (n : ℕ), σ • PowerSeries.coeff n F = PowerSeries.coeff n F)
    (hrat : DeningerIsRationalSeries F) :
    ∃ α β : Polynomial A,
      (∀ (σ : G) (n : ℕ), σ • α.coeff n = α.coeff n) ∧
      (∀ (σ : G) (n : ℕ), σ • β.coeff n = β.coeff n) ∧
      α.coeff 0 = 1 ∧ β.coeff 0 = 1 ∧ (β : PowerSeries A) * F = (α : PowerSeries A) := by
  classical
  obtain ⟨P, Q, hP0, hQ0, hPQ⟩ := hrat
  letI : MulSemiringAction G (FractionRing A) :=
    IsFractionRing.mulSemiringAction G A (FractionRing A)
  haveI : SMulDistribClass G A (FractionRing A) :=
    IsFractionRing.smulDistribClass G A (FractionRing A)
  have hι : Function.Injective (algebraMap A (FractionRing A)) :=
    IsFractionRing.injective A (FractionRing A)
  have hcompat : ∀ (σ : G) (a : A),
      σ • (algebraMap A (FractionRing A) a) = algebraMap A (FractionRing A) (σ • a) := by
    intro σ a
    have h := smul_distrib_smul σ a (1 : FractionRing A)
    simpa [Algebra.smul_def] using h
  have hFK : ∀ (σ : G) (n : ℕ),
      σ • PowerSeries.coeff n (PowerSeries.map (algebraMap A (FractionRing A)) F)
        = PowerSeries.coeff n (PowerSeries.map (algebraMap A (FractionRing A)) F) := by
    intro σ n
    rw [PowerSeries.coeff_map, hcompat, hF]
  have hPQK : ((Q.map (algebraMap A (FractionRing A)) : Polynomial (FractionRing A)) :
        PowerSeries (FractionRing A))
      * PowerSeries.map (algebraMap A (FractionRing A)) F
      = ((P.map (algebraMap A (FractionRing A)) : Polynomial (FractionRing A)) :
        PowerSeries (FractionRing A)) := by
    rw [Polynomial.polynomial_map_coe, Polynomial.polynomial_map_coe, ← map_mul, hPQ]
  have hratK : DeningerIsRationalSeries (PowerSeries.map (algebraMap A (FractionRing A)) F) := by
    refine ⟨P.map (algebraMap A (FractionRing A)), Q.map (algebraMap A (FractionRing A)), ?_, ?_,
      hPQK⟩
    · rw [Polynomial.coeff_map, hP0, map_one]
    · rw [Polynomial.coeff_map, hQ0, map_one]
  obtain ⟨P₁, Q₁, hP₁inv, hQ₁inv, hP₁0, hQ₁0, hPQ₁, hcop⟩ :=
    deningerRationalSeries_galoisDescent_field_coprime
      (PowerSeries.map (algebraMap A (FractionRing A)) F) hFK hratK
  have hcross : P₁ * Q.map (algebraMap A (FractionRing A))
      = Q₁ * P.map (algebraMap A (FractionRing A)) := by
    apply Polynomial.coe_injective (FractionRing A)
    push_cast
    rw [← hPQ₁, ← hPQK]
    ring
  obtain ⟨a, b, hab⟩ := hcop
  have hdvdP : P₁ ∣ P.map (algebraMap A (FractionRing A)) := by
    refine ⟨a * P.map (algebraMap A (FractionRing A))
      + b * Q.map (algebraMap A (FractionRing A)), ?_⟩
    calc P.map (algebraMap A (FractionRing A))
        = (a * P₁ + b * Q₁) * P.map (algebraMap A (FractionRing A)) := by rw [hab, one_mul]
      _ = a * (P₁ * P.map (algebraMap A (FractionRing A)))
          + b * (Q₁ * P.map (algebraMap A (FractionRing A))) := by ring
      _ = a * (P₁ * P.map (algebraMap A (FractionRing A)))
          + b * (P₁ * Q.map (algebraMap A (FractionRing A))) := by rw [hcross]
      _ = P₁ * (a * P.map (algebraMap A (FractionRing A))
          + b * Q.map (algebraMap A (FractionRing A))) := by ring
  have hdvdQ : Q₁ ∣ Q.map (algebraMap A (FractionRing A)) := by
    refine ⟨a * P.map (algebraMap A (FractionRing A))
      + b * Q.map (algebraMap A (FractionRing A)), ?_⟩
    calc Q.map (algebraMap A (FractionRing A))
        = (a * P₁ + b * Q₁) * Q.map (algebraMap A (FractionRing A)) := by rw [hab, one_mul]
      _ = a * (P₁ * Q.map (algebraMap A (FractionRing A)))
          + b * (Q₁ * Q.map (algebraMap A (FractionRing A))) := by ring
      _ = a * (Q₁ * P.map (algebraMap A (FractionRing A)))
          + b * (Q₁ * Q.map (algebraMap A (FractionRing A))) := by rw [← hcross]
      _ = Q₁ * (a * P.map (algebraMap A (FractionRing A))
          + b * Q.map (algebraMap A (FractionRing A))) := by ring
  have key : ∀ (R₁ : Polynomial (FractionRing A)) (R : Polynomial A), R.coeff 0 = 1 →
      R₁.coeff 0 = 1 → R₁ ∣ R.map (algebraMap A (FractionRing A)) →
      ∀ n, R₁.coeff n ∈ Set.range (algebraMap A (FractionRing A)) := by
    intro R₁ R hR0 hR₁0 hdvd n
    have hmonic : (R.reverse).Monic := deningerReverse_monic hR0
    have hrevdvd : R₁.reverse ∣ (R.reverse).map (algebraMap A (FractionRing A)) := by
      obtain ⟨S, hS⟩ := hdvd
      refine ⟨S.reverse, ?_⟩
      rw [← deningerReverse_map _ hι, hS, Polynomial.reverse_mul_of_domain]
    obtain ⟨g', hg'⟩ :=
      IsIntegrallyClosed.eq_map_mul_C_of_dvd (FractionRing A) hmonic hrevdvd
    have hlead : R₁.reverse.leadingCoeff = 1 := deningerReverse_monic hR₁0
    rw [hlead, Polynomial.C_1, mul_one] at hg'
    refine deningerCoeff_mem_range_of_reverse _ (fun m => ?_) n
    rw [← hg', Polynomial.coeff_map]
    exact ⟨g'.coeff m, rfl⟩
  obtain ⟨α, hα⟩ := (Polynomial.mem_lifts _).1
    ((Polynomial.lifts_iff_coeff_lifts _).2 (key P₁ P hP0 hP₁0 hdvdP))
  obtain ⟨β, hβ⟩ := (Polynomial.mem_lifts _).1
    ((Polynomial.lifts_iff_coeff_lifts _).2 (key Q₁ Q hQ0 hQ₁0 hdvdQ))
  have hαcoeff : ∀ n, algebraMap A (FractionRing A) (α.coeff n) = P₁.coeff n := by
    intro n
    rw [← hα, Polynomial.coeff_map]
  have hβcoeff : ∀ n, algebraMap A (FractionRing A) (β.coeff n) = Q₁.coeff n := by
    intro n
    rw [← hβ, Polynomial.coeff_map]
  refine ⟨α, β, ?_, ?_, ?_, ?_, ?_⟩
  · intro σ n
    apply hι
    rw [← hcompat, hαcoeff]
    exact hP₁inv σ n
  · intro σ n
    apply hι
    rw [← hcompat, hβcoeff]
    exact hQ₁inv σ n
  · apply hι
    rw [hαcoeff, hP₁0, map_one]
  · apply hι
    rw [hβcoeff, hQ₁0, map_one]
  · apply PowerSeries.map_injective (algebraMap A (FractionRing A)) hι
    rw [map_mul, ← Polynomial.polynomial_map_coe, ← Polynomial.polynomial_map_coe, hα, hβ, hPQ₁]

/-- **Deninger, Proposition 1.2(b), polynomial form.**  Over an integrally closed domain, a
`G`-invariant normalized fraction `P / Q` is equivalent to one with `G`-invariant numerator and
denominator. -/
theorem deningerPolyGaloisDescent_integrallyClosed
    {G A : Type*} [Group G] [CommRing A] [IsDomain A] [IsIntegrallyClosed A]
    [MulSemiringAction G A] (P Q : Polynomial A) (hP0 : P.coeff 0 = 1) (hQ0 : Q.coeff 0 = 1)
    (hcross : ∀ σ : G, deningerPolyAct σ P * Q = deningerPolyAct σ Q * P) :
    ∃ α β : Polynomial A,
      (∀ (σ : G) (n : ℕ), σ • α.coeff n = α.coeff n) ∧
      (∀ (σ : G) (n : ℕ), σ • β.coeff n = β.coeff n) ∧
      α.coeff 0 = 1 ∧ β.coeff 0 = 1 ∧ α * Q = P * β := by
  classical
  have hunit : ∀ R : Polynomial A, R.coeff 0 = 1 → IsUnit ((R : Polynomial A) : PowerSeries A) := by
    intro R hR
    rw [PowerSeries.isUnit_iff_constantCoeff, ← PowerSeries.coeff_zero_eq_constantCoeff,
      Polynomial.coeff_coe, hR]
    exact isUnit_one
  have hQunit := hunit Q hQ0
  obtain ⟨V, hV⟩ : ∃ V : PowerSeries A, ((Q : Polynomial A) : PowerSeries A) * V = 1 := by
    obtain ⟨u, hu⟩ := hQunit
    exact ⟨((u⁻¹ : (PowerSeries A)ˣ) : PowerSeries A), by
      rw [← hu, ← Units.val_mul, mul_inv_cancel, Units.val_one]⟩
  set F : PowerSeries A := ((P : Polynomial A) : PowerSeries A) * V with hFdef
  have hQF : ((Q : Polynomial A) : PowerSeries A) * F = ((P : Polynomial A) : PowerSeries A) := by
    rw [hFdef]
    calc ((Q : Polynomial A) : PowerSeries A) * (((P : Polynomial A) : PowerSeries A) * V)
        = (((Q : Polynomial A) : PowerSeries A) * V) * ((P : Polynomial A) : PowerSeries A) := by
          ring
      _ = ((P : Polynomial A) : PowerSeries A) := by rw [hV, one_mul]
  have hFinv : ∀ (σ : G) (n : ℕ), σ • PowerSeries.coeff n F = PowerSeries.coeff n F := by
    intro σ
    have hmapF : PowerSeries.map (MulSemiringAction.toRingHom G A σ) F = F := by
      have hσQunit : IsUnit (((deningerPolyAct σ Q : Polynomial A)) : PowerSeries A) := by
        refine hunit _ ?_
        rw [deningerPolyAct_coeff, hQ0, smul_one]
      have hmapped := congrArg (PowerSeries.map (MulSemiringAction.toRingHom G A σ)) hQF
      rw [map_mul] at hmapped
      have hQmap : PowerSeries.map (MulSemiringAction.toRingHom G A σ)
          ((Q : Polynomial A) : PowerSeries A)
          = ((deningerPolyAct σ Q : Polynomial A) : PowerSeries A) := by
        rw [deningerPolyAct, ← Polynomial.polynomial_map_coe]
        rfl
      have hPmap : PowerSeries.map (MulSemiringAction.toRingHom G A σ)
          ((P : Polynomial A) : PowerSeries A)
          = ((deningerPolyAct σ P : Polynomial A) : PowerSeries A) := by
        rw [deningerPolyAct, ← Polynomial.polynomial_map_coe]
        rfl
      rw [hQmap, hPmap] at hmapped
      have hcr : ((deningerPolyAct σ P : Polynomial A) : PowerSeries A)
          * ((Q : Polynomial A) : PowerSeries A)
          = ((deningerPolyAct σ Q : Polynomial A) : PowerSeries A)
            * ((P : Polynomial A) : PowerSeries A) := by
        have := congrArg (fun R : Polynomial A => ((R : Polynomial A) : PowerSeries A)) (hcross σ)
        push_cast at this
        exact this
      have hcancel : ((deningerPolyAct σ Q : Polynomial A) : PowerSeries A)
          * (((Q : Polynomial A) : PowerSeries A)
            * PowerSeries.map (MulSemiringAction.toRingHom G A σ) F)
          = ((deningerPolyAct σ Q : Polynomial A) : PowerSeries A)
            * (((Q : Polynomial A) : PowerSeries A) * F) := by
        calc ((deningerPolyAct σ Q : Polynomial A) : PowerSeries A)
              * (((Q : Polynomial A) : PowerSeries A)
                * PowerSeries.map (MulSemiringAction.toRingHom G A σ) F)
            = (((deningerPolyAct σ Q : Polynomial A) : PowerSeries A)
                * PowerSeries.map (MulSemiringAction.toRingHom G A σ) F)
              * ((Q : Polynomial A) : PowerSeries A) := by ring
          _ = ((deningerPolyAct σ P : Polynomial A) : PowerSeries A)
              * ((Q : Polynomial A) : PowerSeries A) := by rw [hmapped]
          _ = ((deningerPolyAct σ Q : Polynomial A) : PowerSeries A)
              * ((P : Polynomial A) : PowerSeries A) := hcr
          _ = ((deningerPolyAct σ Q : Polynomial A) : PowerSeries A)
              * (((Q : Polynomial A) : PowerSeries A) * F) := by rw [hQF]
      have h1 := hσQunit.mul_left_cancel hcancel
      exact hQunit.mul_left_cancel h1
    intro n
    have := congrArg (PowerSeries.coeff n) hmapF
    rwa [PowerSeries.coeff_map] at this
  obtain ⟨α, β, hα, hβ, hα0, hβ0, hαβ⟩ :=
    deningerRationalSeries_galoisDescent_integrallyClosed F hFinv ⟨P, Q, hP0, hQ0, hQF⟩
  refine ⟨α, β, hα, hβ, hα0, hβ0, ?_⟩
  apply Polynomial.coe_injective A
  push_cast
  calc ((α : Polynomial A) : PowerSeries A) * ((Q : Polynomial A) : PowerSeries A)
      = (((β : Polynomial A) : PowerSeries A) * F) * ((Q : Polynomial A) : PowerSeries A) := by
        rw [hαβ]
    _ = ((β : Polynomial A) : PowerSeries A)
        * (((Q : Polynomial A) : PowerSeries A) * F) := by ring
    _ = ((P : Polynomial A) : PowerSeries A) * ((β : Polynomial A) : PowerSeries A) := by
        rw [hQF]; ring

open scoped DeningerWittRing in
/-- **Deninger, Proposition 1.2(b) (`t21n`), for the rational Witt ring.**  For a group acting by
ring automorphisms on an integrally closed domain, every `G`-invariant rational Witt vector comes
from a rational Witt vector over the fixed subring. -/
theorem deningerWittRing_galoisDescent_integrallyClosed
    {G A : Type*} [Group G] [CommRing A] [IsDomain A] [IsIntegrallyClosed A]
    [MulSemiringAction G A] (w : DeningerCanonicalRationalWittRing A) (hw : ∀ σ : G, σ • w = w) :
    ∃ w₀ : DeningerCanonicalRationalWittRing (FixedPoints.subring A G),
      deningerCanonicalRationalWittMap
        (algebraMap (FixedPoints.subring A G) A) w₀ = w :=
  deningerWittRing_galoisDescent_of_polyDescent
    (fun P Q hP0 hQ0 _ hcross =>
      deningerPolyGaloisDescent_integrallyClosed P Q hP0 hQ0 hcross) w hw

end RHTower
