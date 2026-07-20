import GaloisForLFunctions.HTGeometry.PrimeRadialFusionRankSurfaceLaw

/-!
# Realization of additive order spectra by prime-radial fusion fields

Every additive submonoid of `ℕ` is realized exactly as the order spectrum of a radial formal
profile algebra.  Through the fusion--field correspondence and the rank-surface law, this gives
an inverse theorem: the admissible relative Kolchin-rank surfaces are precisely the cumulative
counting surfaces of additive order submonoids.
-/

namespace GaloisForLFunctions.HTGeometry

open Set
open scoped Differential

noncomputable section

set_option maxHeartbeats 1200000

/-! ## The support algebra of an additive monoid -/

/-- Radial profiles all of whose nonzero coefficients have index in `S`. -/
def primeRadialMonoidProfileAlgebra
    (S : AddSubmonoid Nat) : NonUnitalSubalgebra ℂ PrimeRadialProfile where
  carrier := {u | ∀ n,
    PowerSeries.coeff n (u : PowerSeries ℂ) ≠ 0 → n ∈ S}
  zero_mem' := by
    intro n hn
    exact (hn (by simp)).elim
  add_mem' := by
    intro u v hu hv n hn
    by_contra hnS
    have hun : PowerSeries.coeff n (u : PowerSeries ℂ) = 0 := by
      by_contra h
      exact hnS (hu n h)
    have hvn : PowerSeries.coeff n (v : PowerSeries ℂ) = 0 := by
      by_contra h
      exact hnS (hv n h)
    apply hn
    simp [hun, hvn]
  mul_mem' := by
    intro u v hu hv n hn
    by_contra hnS
    apply hn
    change PowerSeries.coeff n
      ((u : PowerSeries ℂ) * (v : PowerSeries ℂ)) = 0
    rw [PowerSeries.coeff_mul]
    apply Finset.sum_eq_zero
    intro ij hij
    by_cases hi : PowerSeries.coeff ij.1 (u : PowerSeries ℂ) = 0
    · simp [hi]
    by_cases hj : PowerSeries.coeff ij.2 (v : PowerSeries ℂ) = 0
    · simp [hj]
    exfalso
    apply hnS
    have hadd : ij.1 + ij.2 ∈ S := S.add_mem (hu ij.1 hi) (hv ij.2 hj)
    simpa [Finset.mem_antidiagonal.mp hij] using hadd
  smul_mem' := by
    intro a u hu n hn
    by_contra hnS
    have hun : PowerSeries.coeff n (u : PowerSeries ℂ) = 0 := by
      by_contra h
      exact hnS (hu n h)
    apply hn
    simp [hun]

/-- The positive monomial profile `X^n`. -/
def primeRadialMonomialProfile (n : Nat) (hn : 0 < n) : PrimeRadialProfile :=
  ⟨PowerSeries.monomial n 1, by
    change PowerSeries.coeff 0 (PowerSeries.monomial n (1 : ℂ)) = 0
    rw [PowerSeries.coeff_monomial, if_neg (Nat.ne_of_lt hn)]⟩

theorem primeRadialMonomialProfile_mem_monoidAlgebra
    (S : AddSubmonoid Nat) {n : Nat} (hn : 0 < n) (hnS : n ∈ S) :
    primeRadialMonomialProfile n hn ∈ primeRadialMonoidProfileAlgebra S := by
  intro k hk
  by_cases hkn : k = n
  · simpa [hkn] using hnS
  · exfalso
    apply hk
    simp [primeRadialMonomialProfile, PowerSeries.coeff_monomial, hkn]

theorem primeRadialMonomialProfile_ne_zero
    (n : Nat) (hn : 0 < n) : primeRadialMonomialProfile n hn ≠ 0 := by
  intro hzero
  have hcoeff := congrArg
    (fun u : PrimeRadialProfile => PowerSeries.coeff n (u : PowerSeries ℂ)) hzero
  simpa [primeRadialMonomialProfile, PowerSeries.coeff_monomial] using hcoeff

theorem primeRadialMonomialProfile_order
    (n : Nat) (hn : 0 < n) :
    (PowerSeries.order
      (primeRadialMonomialProfile n hn : PowerSeries ℂ)).toNat = n := by
  rw [show (primeRadialMonomialProfile n hn : PowerSeries ℂ) =
    PowerSeries.monomial n 1 by rfl,
    PowerSeries.order_monomial_of_ne_zero n (1 : ℂ) one_ne_zero]
  simp

/-! ## Exact inverse spectrum theorem -/

/-- The realized order spectrum is exactly the positive part of the prescribed additive
submonoid. -/
theorem primeRadialMonoidProfileAlgebra_orderOccurs_iff
    (S : AddSubmonoid Nat) (n : Nat) :
    PrimeRadialOrderOccurs (primeRadialMonoidProfileAlgebra S) n ↔
      n ∈ S ∧ 0 < n := by
  constructor
  · intro hoccurs
    have hnpos := primeRadialOrderOccurs_pos hoccurs
    obtain ⟨u, hu, hord⟩ := hoccurs
    have hu' : (u : PowerSeries ℂ) ≠ 0 := by simpa using hu
    have hcoeff : PowerSeries.coeff
        (PowerSeries.order (u : PowerSeries ℂ)).toNat
        (u : PowerSeries ℂ) ≠ 0 :=
      PowerSeries.coeff_order hu'
    have hmem := u.2 _ hcoeff
    exact ⟨by simpa [hord] using hmem, hnpos⟩
  · rintro ⟨hnS, hnpos⟩
    let u : primeRadialMonoidProfileAlgebra S :=
      ⟨primeRadialMonomialProfile n hnpos,
        primeRadialMonomialProfile_mem_monoidAlgebra S hnpos hnS⟩
    refine ⟨u, ?_, ?_⟩
    · intro hzero
      apply primeRadialMonomialProfile_ne_zero n hnpos
      exact congrArg Subtype.val hzero
    · exact primeRadialMonomialProfile_order n hnpos

/-- The order submonoid recovered from the realizing algebra is the original submonoid. -/
theorem primeRadialOrderSubmonoid_monoidProfileAlgebra
    (S : AddSubmonoid Nat) :
    primeRadialOrderSubmonoid (primeRadialMonoidProfileAlgebra S) = S := by
  ext n
  rw [mem_primeRadialOrderSubmonoid_iff,
    primeRadialMonoidProfileAlgebra_orderOccurs_iff]
  constructor
  · rintro (rfl | ⟨hnS, _⟩)
    · exact S.zero_mem
    · exact hnS
  · intro hnS
    by_cases hn : n = 0
    · exact Or.inl hn
    · exact Or.inr ⟨hnS, Nat.pos_of_ne_zero hn⟩

theorem primeRadialConductorModulus_monoidProfileAlgebra
    (S : AddSubmonoid Nat) :
    primeRadialConductorModulus (primeRadialMonoidProfileAlgebra S) =
      Nat.setGcd (S : Set Nat) := by
  unfold primeRadialConductorModulus
  rw [primeRadialOrderSubmonoid_monoidProfileAlgebra]

/-- The visible-order census of the realizing algebra is exactly the truncated counting function
of the prescribed additive monoid. -/
noncomputable def primeRadialAddSubmonoidCount
    (S : AddSubmonoid Nat) (N : Nat) : Nat := by
  classical
  exact ((Finset.range N).filter fun j => j + 1 ∈ S).card

theorem primeRadialVisibleOrderCount_monoidProfileAlgebra
    (S : AddSubmonoid Nat) (N : Nat) :
    primeRadialVisibleOrderCount
        (primeRadialMonoidProfileAlgebra S).toSubmodule N =
      primeRadialAddSubmonoidCount S N := by
  classical
  unfold primeRadialVisibleOrderCount primeRadialAddSubmonoidCount
  congr 1
  ext j
  simp only [Finset.mem_filter, Finset.mem_range, and_congr_right_iff]
  intro _hj
  rw [primeRadialSubspaceOrderOccurs_toSubmodule_iff,
    primeRadialMonoidProfileAlgebra_orderOccurs_iff]
  simp

/-! ## Completeness of the rank-surface invariant -/

/-- A positive order occurs exactly when the order-zero Kolchin rank gains one unit at that
cutoff.  Thus the rank surface itself recovers the order spectrum. -/
theorem primeRadialOrderOccurs_iff_KolchinRank_jump
    (A : NonUnitalSubalgebra ℂ PrimeRadialProfile) (N : Nat) :
    PrimeRadialOrderOccurs A (N + 1) ↔
      primeRadialKolchinRank A.toSubmodule (N + 1) 0 =
        primeRadialKolchinRank A.toSubmodule N 0 + 1 := by
  constructor
  · intro hoccurs
    have hrec := primeRadialFusionKolchinRank_succ A N 0
    simpa [primeRadialOrderJump,
      primeRadialSubspaceOrderOccurs_toSubmodule_iff, hoccurs] using hrec
  · intro hjump
    by_contra hoccurs
    have hrec := primeRadialFusionKolchinRank_succ A N 0
    have hflat : primeRadialKolchinRank A.toSubmodule (N + 1) 0 =
        primeRadialKolchinRank A.toSubmodule N 0 := by
      simpa [primeRadialOrderJump,
        primeRadialSubspaceOrderOccurs_toSubmodule_iff, hoccurs] using hrec
    omega

/-- **Completeness law.**  Two radial fusion algebras have the same full relative Kolchin-rank
surface exactly when their additive order submonoids agree. -/
theorem primeRadialFusionKolchinRank_surface_eq_iff_orderSubmonoid_eq
    (A B : NonUnitalSubalgebra ℂ PrimeRadialProfile) :
    (∀ N r,
      primeRadialKolchinRank A.toSubmodule N r =
        primeRadialKolchinRank B.toSubmodule N r) ↔
      primeRadialOrderSubmonoid A = primeRadialOrderSubmonoid B := by
  classical
  constructor
  · intro hsurface
    apply AddSubmonoid.ext
    intro n
    rw [mem_primeRadialOrderSubmonoid_iff,
      mem_primeRadialOrderSubmonoid_iff]
    by_cases hn : n = 0
    · simp [hn]
    · have hnpos : 0 < n := Nat.pos_of_ne_zero hn
      let N := n - 1
      have hnN : N + 1 = n := by omega
      rw [← hnN, primeRadialOrderOccurs_iff_KolchinRank_jump,
        primeRadialOrderOccurs_iff_KolchinRank_jump]
      have hnext := hsurface (N + 1) 0
      have hnow := hsurface N 0
      omega
  · intro hmonoid N r
    have hoccurs : ∀ n, PrimeRadialOrderOccurs A n ↔ PrimeRadialOrderOccurs B n := by
      intro n
      have hmem : n ∈ primeRadialOrderSubmonoid A ↔
          n ∈ primeRadialOrderSubmonoid B := by
        rw [hmonoid]
      rw [mem_primeRadialOrderSubmonoid_iff,
        mem_primeRadialOrderSubmonoid_iff] at hmem
      by_cases hn : n = 0
      · subst n
        constructor
        · intro h
          exact ((primeRadialOrderOccurs_pos h).ne' rfl).elim
        · intro h
          exact ((primeRadialOrderOccurs_pos h).ne' rfl).elim
      · simpa [hn] using hmem
    rw [primeRadialFusionKolchinRank_eq_orderCount,
      primeRadialFusionKolchinRank_eq_orderCount]
    congr 1
    unfold primeRadialVisibleOrderCount
    congr 1
    ext j
    simp only [Finset.mem_filter, Finset.mem_range, and_congr_right_iff]
    intro _hj
    rw [primeRadialSubspaceOrderOccurs_toSubmodule_iff,
      primeRadialSubspaceOrderOccurs_toSubmodule_iff, hoccurs]

/-- **Inverse rank-surface realization.**  Every additive submonoid of `ℕ` occurs as the exact
discrete rank spectrum of an embedded fusion-closed prime-radial differential field. -/
theorem primeRadialFusionRankSurface_realizes_addSubmonoid
    (S : AddSubmonoid Nat) :
    PrimeRadialCarrierFusionClosed
        (primeRadialMonoidProfileAlgebra S).toSubmodule ∧
      primeRadialOrderSubmonoid (primeRadialMonoidProfileAlgebra S) = S ∧
      ∀ N r,
        primeRadialKolchinRank
            (primeRadialMonoidProfileAlgebra S).toSubmodule N r =
          (r + 1) * primeRadialAddSubmonoidCount S N := by
  refine ⟨primeRadialFusionField_fusionClosed (primeRadialMonoidProfileAlgebra S),
    primeRadialOrderSubmonoid_monoidProfileAlgebra S, ?_⟩
  intro N r
  rw [primeRadialFusionKolchinRank_eq_orderCount,
    primeRadialVisibleOrderCount_monoidProfileAlgebra]

/-- Classification capstone: radial fusion fields produce additive order spectra, their complete
relative rank surfaces are exactly the cumulative counting surfaces of those spectra, and every
additive spectrum is realized. -/
theorem primeRadialFusionRankSurface_classification :
    (∀ A : NonUnitalSubalgebra ℂ PrimeRadialProfile, ∀ N r,
      primeRadialKolchinRank A.toSubmodule N r =
        (r + 1) * primeRadialVisibleOrderCount A.toSubmodule N) ∧
      (∀ S : AddSubmonoid Nat,
        ∃ A : NonUnitalSubalgebra ℂ PrimeRadialProfile,
          PrimeRadialCarrierFusionClosed A.toSubmodule ∧
            primeRadialOrderSubmonoid A = S ∧
            ∀ N r,
              primeRadialKolchinRank A.toSubmodule N r =
                (r + 1) * primeRadialAddSubmonoidCount S N) := by
  refine ⟨fun A => primeRadialFusionKolchinRank_eq_orderCount A, ?_⟩
  intro S
  exact ⟨primeRadialMonoidProfileAlgebra S,
    primeRadialFusionRankSurface_realizes_addSubmonoid S⟩

/-- **Universal classification master theorem.**  Equality classes of complete prime-radial
fusion rank surfaces are exactly additive submonoids of `ℕ`, and every such submonoid is
realized by an embedded fusion-closed differential field. -/
theorem primeRadialFusionRankSurface_completeClassification :
    (∀ A B : NonUnitalSubalgebra ℂ PrimeRadialProfile,
      (∀ N r,
        primeRadialKolchinRank A.toSubmodule N r =
          primeRadialKolchinRank B.toSubmodule N r) ↔
        primeRadialOrderSubmonoid A = primeRadialOrderSubmonoid B) ∧
      (∀ S : AddSubmonoid Nat,
        ∃ A : NonUnitalSubalgebra ℂ PrimeRadialProfile,
          PrimeRadialCarrierFusionClosed A.toSubmodule ∧
            primeRadialOrderSubmonoid A = S ∧
            ∀ N r,
              primeRadialKolchinRank A.toSubmodule N r =
                (r + 1) * primeRadialAddSubmonoidCount S N) := by
  refine ⟨primeRadialFusionKolchinRank_surface_eq_iff_orderSubmonoid_eq, ?_⟩
  intro S
  exact ⟨primeRadialMonoidProfileAlgebra S,
    primeRadialFusionRankSurface_realizes_addSubmonoid S⟩

end

end GaloisForLFunctions.HTGeometry
