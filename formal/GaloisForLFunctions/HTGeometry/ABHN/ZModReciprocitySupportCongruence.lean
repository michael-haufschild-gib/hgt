import GaloisForLFunctions.HTGeometry.ABHN.ZModTwoReciprocitySupportParity

/-!
# Congruence laws for cyclic reciprocity support

If every active coordinate of a `ℤ/nℤ` profile is the standard generator, its global sum
vanishes exactly when `n` divides the support cardinality. Transporting this across the faithful
cyclic carry coordinate gives a support-congruence refinement of finite ABHN-style reciprocity.
-/

namespace GaloisForLFunctions.HTGeometry.ABHN

universe u

/-- A generator-valued `ℤ/nℤ` profile sums to the cast of its support cardinality. -/
theorem finsuppZMod_natCast_support_card_eq_sum_of_eq_one
    {ι : Type u} [DecidableEq ι] (n : ℕ) (f : ι →₀ ZMod n)
    (hone : ∀ i ∈ f.support, f i = 1) :
    (f.support.card : ZMod n) = f.sum (fun _ x => x) := by
  change (f.support.card : ZMod n) = ∑ i ∈ f.support, f i
  rw [Finset.card_eq_sum_ones, Nat.cast_sum]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [Nat.cast_one, hone i hi]

/-- A generator-valued `ℤ/nℤ` profile has zero sum exactly when `n` divides its support. -/
theorem finsuppZMod_sum_eq_zero_iff_dvd_support_card_of_eq_one
    {ι : Type u} [DecidableEq ι] (n : ℕ) (f : ι →₀ ZMod n)
    (hone : ∀ i ∈ f.support, f i = 1) :
    f.sum (fun _ x => x) = 0 ↔ n ∣ f.support.card := by
  rw [← finsuppZMod_natCast_support_card_eq_sum_of_eq_one n f hone,
    ZMod.natCast_eq_zero_iff]

/-- The support-congruence law transports across any additive equivalence with `ℤ/nℤ`. -/
theorem finsuppAddEquivZMod_sum_eq_zero_iff_dvd_support_card_of_eq_one
    {ι : Type u} [DecidableEq ι]
    {A : Type*} [AddCommGroup A] (n : ℕ) (e : A ≃+ ZMod n) (f : ι →₀ A)
    (hone : ∀ i ∈ f.support, e (f i) = 1) :
    f.sum (fun _ x => e x) = 0 ↔ n ∣ f.support.card := by
  let g : ι →₀ ZMod n := Finsupp.mapRange.addMonoidHom e.toAddMonoidHom f
  have hsum : g.sum (fun _ x => x) = f.sum (fun _ x => e x) := by
    dsimp [g]
    change (Finsupp.mapRange (fun x => e x) e.map_zero f).sum (fun _ x => x) = _
    rw [Finsupp.sum_mapRange_index]
    intro i
    rfl
  have hsupp : g.support = f.support := by
    ext i
    simp [g]
  have honeg : ∀ i ∈ g.support, g i = 1 := by
    intro i hi
    simpa [g, hsupp] using hone i (by simpa [hsupp] using hi)
  rw [← hsum,
    finsuppZMod_sum_eq_zero_iff_dvd_support_card_of_eq_one n g honeg, hsupp]

/-- Literal cyclic carry `H²`, expressed directly in the supplied `ℤ/nℤ` coordinate. -/
noncomputable def cyclicGaloisCarryH2ZModEquiv
    (K L : Type) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L] [IsCyclic Gal(L/K)]
    (n : ℕ) (hn : n ≠ 0)
    (qEquiv : Additive Kˣ ⧸ cyclicGaloisH2BaseNormImage K L ≃+ ZMod n) :
    cyclicGaloisH2 K L ≃+ ZMod n :=
  (cyclicGaloisCarryH2TorsionEquiv K L n hn qEquiv).trans
    (zmodRatModIntAddEquivNTorsion n hn).symm

/-- A generator-valued cyclic carry profile has zero invariant sum exactly when its support
cardinality is divisible by the cyclic order. -/
theorem cyclicGaloisCarryH2Profile_sum_eq_zero_iff_dvd_support_card_of_generator
    {ι : Type u} [DecidableEq ι]
    (K L : Type) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L] [IsCyclic Gal(L/K)]
    (n : ℕ) (hn : n ≠ 0)
    (qEquiv : Additive Kˣ ⧸ cyclicGaloisH2BaseNormImage K L ≃+ ZMod n)
    (f : ι →₀ cyclicGaloisH2 K L)
    (hone : ∀ i ∈ f.support, cyclicGaloisCarryH2ZModEquiv K L n hn qEquiv (f i) = 1) :
    cyclicGaloisCarryH2ProfileInvariantSumAddHom ι K L n hn qEquiv f = 0 ↔
      n ∣ f.support.card := by
  let eT := cyclicGaloisCarryH2TorsionEquiv K L n hn qEquiv
  let d := (zmodRatModIntAddEquivNTorsion n hn).symm
  rw [← finsuppAddEquivZMod_sum_eq_zero_iff_dvd_support_card_of_eq_one
    n (eT.trans d) f hone]
  change f.sum (fun _ x => eT x) = 0 ↔ f.sum (fun _ x => d (eT x)) = 0
  constructor
  · intro h
    have hmap := congrArg d h
    rw [map_zero, map_finsuppSum] at hmap
    exact hmap
  · intro h
    apply d.injective
    rw [map_zero, map_finsuppSum]
    exact h

/-- Product-one reciprocity for a generator-valued cyclic packet is exactly divisibility of its
support cardinality by the cyclic order. -/
theorem cyclicGaloisCarryH2Profile_product_eq_one_iff_dvd_support_card_of_generator
    {ι : Type u} [DecidableEq ι]
    (K L : Type) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L] [IsCyclic Gal(L/K)]
    (n : ℕ) (hn : n ≠ 0)
    (qEquiv : Additive Kˣ ⧸ cyclicGaloisH2BaseNormImage K L ≃+ ZMod n)
    (f : ι →₀ cyclicGaloisH2 K L)
    (hone : ∀ i ∈ f.support, cyclicGaloisCarryH2ZModEquiv K L n hn qEquiv (f i) = 1) :
    f.prod (fun _ z => cyclicGaloisCarryH2TorsionStdAddChar K L n hn qEquiv z) = 1 ↔
      n ∣ f.support.card :=
  (cyclicGaloisCarryH2Profile_product_eq_one_iff_sum_eq_zero
      ι K L n hn qEquiv f).trans
    (cyclicGaloisCarryH2Profile_sum_eq_zero_iff_dvd_support_card_of_generator
      K L n hn qEquiv f hone)

end GaloisForLFunctions.HTGeometry.ABHN
