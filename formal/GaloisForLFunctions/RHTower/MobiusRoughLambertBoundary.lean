import GaloisForLFunctions.RHTower.MobiusPrimeRenewalDefectBoundary

/-!
# Rough-composite Lambert image of the Route E boundary

For a small-prime aperture `P` and an integer prime support `R`, the
zero/one-large-prime coefficient retains exactly those squarefree divisor
supports `D ⊆ R` with at most one label outside `P`.  Lambert dilation
forms the divisor sum of those coefficients.

This file proves its exact finite normal form:

* one small label makes the complete divisor fibre vanish;
* on a rough fibre the image is `1 - |R|`;
* rough prime powers (support cardinality one) vanish;
* genuinely transverse rough support has one fixed negative sign.

This is the finite arithmetic core of

`L B_z = exp(-x) - Σ_{P⁻(n)>z, ω(n)≥2} (ω(n)-1) exp(-nx)`.

No estimate, zero-free hypothesis, or form of RH occurs here.
-/

open scoped BigOperators

namespace RHTower

/-- Alternating divisor mass carried by the small-prime part of one
prime-support fibre. -/
def finiteSmallPrimeDivisorParity
    {α : Type*} [DecidableEq α] (P R : Finset α) : ℤ :=
  ∑ S ∈ (R ∩ P).powerset, (-1 : ℤ) ^ S.card

/-- Grouped zero/one-large-prime divisor image: the zero-large term minus
one identical small-prime parity fibre for every rough support label. -/
def finiteZeroOneLargePrimeDivisorImage
    {α : Type*} [DecidableEq α] (P R : Finset α) : ℤ :=
  finiteSmallPrimeDivisorParity P R -
    ∑ _q ∈ R \ P, finiteSmallPrimeDivisorParity P R

/-- Literal zero/one-large-prime coefficient on a squarefree divisor
support. -/
def finiteZeroOneLargePrimeSupportCoefficient
    {α : Type*} [DecidableEq α] (P D : Finset α) : ℤ :=
  if (D \ P).card ≤ 1 then (-1 : ℤ) ^ D.card else 0

/-- Lambert/divisor image of the literal zero/one support coefficient. -/
def finiteZeroOneLargePrimeSupportDivisorSum
    {α : Type*} [DecidableEq α] (P R : Finset α) : ℤ :=
  ∑ D ∈ R.powerset, finiteZeroOneLargePrimeSupportCoefficient P D

/-- Literal coefficient of the complementary sector with at least two
large support labels. -/
def finiteTwoLargePrimeSupportCoefficient
    {α : Type*} [DecidableEq α] (P D : Finset α) : ℤ :=
  if 2 ≤ (D \ P).card then (-1 : ℤ) ^ D.card else 0

/-- Lambert/divisor image of the complementary two-or-more-large support
coefficient. -/
def finiteTwoLargePrimeSupportDivisorSum
    {α : Type*} [DecidableEq α] (P R : Finset α) : ℤ :=
  ∑ D ∈ R.powerset, finiteTwoLargePrimeSupportCoefficient P D

/-- The zero/one and two-or-more sectors partition the full squarefree
Möbius support coefficient exactly. -/
theorem finiteZeroOne_add_twoLargePrimeSupportCoefficient
    {α : Type*} [DecidableEq α] (P D : Finset α) :
    finiteZeroOneLargePrimeSupportCoefficient P D +
        finiteTwoLargePrimeSupportCoefficient P D =
      (-1 : ℤ) ^ D.card := by
  rw [finiteZeroOneLargePrimeSupportCoefficient,
    finiteTwoLargePrimeSupportCoefficient]
  by_cases hsmall : (D \ P).card ≤ 1
  · have hlarge : ¬2 ≤ (D \ P).card := by omega
    rw [if_pos hsmall, if_neg hlarge, add_zero]
  · have hlarge : 2 ≤ (D \ P).card := by omega
    rw [if_neg hsmall, if_pos hlarge, zero_add]

/-- The full Boolean Möbius divisor fibre is the sum of the two Route E
sector images. -/
theorem sum_powerset_neg_one_pow_card_eq_zeroOne_add_twoLarge
    {α : Type*} [DecidableEq α] (P R : Finset α) :
    (∑ D ∈ R.powerset, (-1 : ℤ) ^ D.card) =
      finiteZeroOneLargePrimeSupportDivisorSum P R +
        finiteTwoLargePrimeSupportDivisorSum P R := by
  rw [finiteZeroOneLargePrimeSupportDivisorSum,
    finiteTwoLargePrimeSupportDivisorSum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro D _hD
  exact (finiteZeroOne_add_twoLargePrimeSupportCoefficient P D).symm

/-- The grouped image factors into rough-support multiplicity times the
small-prime Boolean parity fibre. -/
theorem finiteZeroOneLargePrimeDivisorImage_eq
    {α : Type*} [DecidableEq α] (P R : Finset α) :
    finiteZeroOneLargePrimeDivisorImage P R =
      (1 - ((R \ P).card : ℤ)) * finiteSmallPrimeDivisorParity P R := by
  rw [finiteZeroOneLargePrimeDivisorImage, Finset.sum_const]
  simp only [nsmul_eq_mul]
  ring

/-- Subsets of `R` which also lie in `P` are exactly the subsets of
`R ∩ P`. -/
theorem sum_powerset_if_subset_eq_inter
    {α : Type*} [DecidableEq α] (P R : Finset α) :
    (∑ D ∈ R.powerset,
        if D ⊆ P then (-1 : ℤ) ^ D.card else 0) =
      ∑ D ∈ (R ∩ P).powerset, (-1 : ℤ) ^ D.card := by
  rw [← Finset.sum_filter]
  congr 1
  ext D
  simp only [Finset.mem_filter, Finset.mem_powerset]
  constructor
  · exact fun h q hq => Finset.mem_inter.mpr ⟨h.1 hq, h.2 hq⟩
  · exact fun h =>
      ⟨fun q hq => (Finset.mem_inter.mp (h hq)).1,
        fun q hq => (Finset.mem_inter.mp (h hq)).2⟩

/-- Exact regrouping theorem.  Summing the literal zero/one coefficient
over every squarefree divisor support gives the grouped image. -/
theorem finiteZeroOneLargePrimeSupportDivisorSum_eq
    {α : Type*} [DecidableEq α] (P R : Finset α) :
    finiteZeroOneLargePrimeSupportDivisorSum P R =
      finiteZeroOneLargePrimeDivisorImage P R := by
  induction R using Finset.induction_on with
  | empty =>
      simp [finiteZeroOneLargePrimeSupportDivisorSum,
        finiteZeroOneLargePrimeSupportCoefficient,
        finiteZeroOneLargePrimeDivisorImage,
        finiteSmallPrimeDivisorParity]
  | @insert r R hr ih =>
      rw [finiteZeroOneLargePrimeSupportDivisorSum,
        Finset.sum_powerset_insert hr]
      by_cases hrP : r ∈ P
      · have hcancel :
            ∀ D ∈ R.powerset,
              finiteZeroOneLargePrimeSupportCoefficient P (insert r D) =
                -finiteZeroOneLargePrimeSupportCoefficient P D := by
          intro D hDR
          have hrD : r ∉ D := fun hrD => hr (Finset.mem_powerset.mp hDR hrD)
          have hsdiff : insert r D \ P = D \ P := by
            ext q
            simp only [Finset.mem_sdiff, Finset.mem_insert]
            constructor
            · intro hq
              exact ⟨hq.1.resolve_left (fun hqr => hq.2 (hqr ▸ hrP)), hq.2⟩
            · intro hq
              exact ⟨Or.inr hq.1, hq.2⟩
          simp only [finiteZeroOneLargePrimeSupportCoefficient]
          rw [hsdiff, Finset.card_insert_of_notMem hrD, pow_succ]
          by_cases hle : (D \ P).card ≤ 1
          · rw [if_pos hle]
            simp only [if_pos hle]
            ring
          · rw [if_neg hle]
            simp only [if_neg hle]
            simp
        rw [Finset.sum_congr rfl hcancel]
        have hsumneg :
            (∑ D ∈ R.powerset,
                -finiteZeroOneLargePrimeSupportCoefficient P D) =
              -(∑ D ∈ R.powerset,
                finiteZeroOneLargePrimeSupportCoefficient P D) := by
          simp
        rw [hsumneg, add_neg_cancel]
        rw [finiteZeroOneLargePrimeDivisorImage_eq,
          finiteSmallPrimeDivisorParity]
        have hsmall : ((insert r R) ∩ P).Nonempty := by
          exact ⟨r, by simp [hrP]⟩
        rw [Finset.sum_powerset_neg_one_pow_card_of_nonempty hsmall, mul_zero]
      · have hinsert :
            ∀ D ∈ R.powerset,
              finiteZeroOneLargePrimeSupportCoefficient P (insert r D) =
                -(if D ⊆ P then (-1 : ℤ) ^ D.card else 0) := by
          intro D hDR
          have hrD : r ∉ D := fun hrD => hr (Finset.mem_powerset.mp hDR hrD)
          have hrDP : r ∉ D \ P :=
            fun h => hrD (Finset.mem_sdiff.mp h).1
          have hsdiff : insert r D \ P = insert r (D \ P) := by
            ext q
            simp only [Finset.mem_sdiff, Finset.mem_insert]
            constructor
            · intro hq
              rcases hq.1 with hqr | hqD
              · exact Or.inl hqr
              · exact Or.inr ⟨hqD, hq.2⟩
            · intro hq
              rcases hq with hqr | hq
              · exact ⟨Or.inl hqr, hqr ▸ hrP⟩
              · exact ⟨Or.inr hq.1, hq.2⟩
          simp only [finiteZeroOneLargePrimeSupportCoefficient]
          rw [hsdiff, Finset.card_insert_of_notMem hrDP,
            Finset.card_insert_of_notMem hrD, pow_succ]
          by_cases hsub : D ⊆ P
          · have hempty : D \ P = ∅ := by
              ext q
              simp only [Finset.mem_sdiff, Finset.notMem_empty, iff_false]
              exact fun hq => hq.2 (hsub hq.1)
            rw [if_pos hsub, hempty]
            norm_num
          · have hnonempty : (D \ P).Nonempty := by
              rw [Finset.nonempty_iff_ne_empty]
              intro hempty
              apply hsub
              intro q hqD
              by_contra hqP
              have : q ∈ D \ P := Finset.mem_sdiff.mpr ⟨hqD, hqP⟩
              rw [hempty] at this
              exact Finset.notMem_empty q this
            have htwo : ¬(D \ P).card + 1 ≤ 1 := by
              have hone : 1 ≤ (D \ P).card := Finset.one_le_card.mpr hnonempty
              omega
            rw [if_neg hsub, if_neg htwo]
            simp
        rw [Finset.sum_congr rfl hinsert]
        have hsuminsert :
            (∑ D ∈ R.powerset,
                -(if D ⊆ P then (-1 : ℤ) ^ D.card else 0)) =
              -finiteSmallPrimeDivisorParity P R := by
          rw [Finset.sum_neg_distrib,
            sum_powerset_if_subset_eq_inter,
            finiteSmallPrimeDivisorParity]
        rw [hsuminsert]
        change
          finiteZeroOneLargePrimeSupportDivisorSum P R -
              finiteSmallPrimeDivisorParity P R =
            finiteZeroOneLargePrimeDivisorImage P (insert r R)
        rw [ih, finiteZeroOneLargePrimeDivisorImage_eq,
          finiteZeroOneLargePrimeDivisorImage_eq]
        have hinter : insert r R ∩ P = R ∩ P := by
          ext q
          simp only [Finset.mem_inter, Finset.mem_insert]
          constructor
          · intro hq
            rcases hq.1 with hqr | hqR
            · subst q
              exact False.elim (hrP hq.2)
            · exact ⟨hqR, hq.2⟩
          · intro hq
            exact ⟨Or.inr hq.1, hq.2⟩
        have hsdiff : insert r R \ P = insert r (R \ P) := by
          ext q
          simp only [Finset.mem_sdiff, Finset.mem_insert]
          constructor
          · intro hq
            rcases hq.1 with hqr | hqR
            · exact Or.inl hqr
            · exact Or.inr ⟨hqR, hq.2⟩
          · intro hq
            rcases hq with hqr | hq
            · exact ⟨Or.inl hqr, hqr ▸ hrP⟩
            · exact ⟨Or.inr hq.1, hq.2⟩
        have hrSdiff : r ∉ R \ P := by simp [hr]
        rw [finiteSmallPrimeDivisorParity, finiteSmallPrimeDivisorParity,
          hinter, hsdiff, Finset.card_insert_of_notMem hrSdiff]
        push_cast
        ring

/-- Any small prime in the support makes the complete divisor fibre
cancel. -/
theorem finiteZeroOneLargePrimeDivisorImage_eq_zero_of_small
    {α : Type*} [DecidableEq α] {P R : Finset α}
    (hsmall : (R ∩ P).Nonempty) :
    finiteZeroOneLargePrimeDivisorImage P R = 0 := by
  rw [finiteZeroOneLargePrimeDivisorImage_eq,
    finiteSmallPrimeDivisorParity,
    Finset.sum_powerset_neg_one_pow_card_of_nonempty hsmall,
    mul_zero]

/-- The literal support-divisor sum also vanishes as soon as one small
prime label is present. -/
theorem finiteZeroOneLargePrimeSupportDivisorSum_eq_zero_of_small
    {α : Type*} [DecidableEq α] {P R : Finset α}
    (hsmall : (R ∩ P).Nonempty) :
    finiteZeroOneLargePrimeSupportDivisorSum P R = 0 := by
  rw [finiteZeroOneLargePrimeSupportDivisorSum_eq,
    finiteZeroOneLargePrimeDivisorImage_eq_zero_of_small hsmall]

/-- On a rough support fibre, the exact Lambert image is `1 - |R|`. -/
theorem finiteZeroOneLargePrimeDivisorImage_eq_of_disjoint
    {α : Type*} [DecidableEq α] {P R : Finset α}
    (hdisjoint : Disjoint R P) :
    finiteZeroOneLargePrimeDivisorImage P R = 1 - (R.card : ℤ) := by
  have hinter : R ∩ P = ∅ := by
    ext q
    simp only [Finset.mem_inter, Finset.notMem_empty, iff_false]
    intro hq
    exact (Finset.disjoint_left.mp hdisjoint hq.1) hq.2
  have hsdiff : R \ P = R := by
    ext q
    simp only [Finset.mem_sdiff]
    constructor
    · exact fun h => h.1
    · intro hqR
      exact ⟨hqR, Finset.disjoint_left.mp hdisjoint hqR⟩
  rw [finiteZeroOneLargePrimeDivisorImage_eq, hsdiff,
    finiteSmallPrimeDivisorParity, hinter]
  simp

/-- Literal support-divisor form of the rough-fibre law. -/
theorem finiteZeroOneLargePrimeSupportDivisorSum_eq_of_disjoint
    {α : Type*} [DecidableEq α] {P R : Finset α}
    (hdisjoint : Disjoint R P) :
    finiteZeroOneLargePrimeSupportDivisorSum P R = 1 - (R.card : ℤ) := by
  rw [finiteZeroOneLargePrimeSupportDivisorSum_eq,
    finiteZeroOneLargePrimeDivisorImage_eq_of_disjoint hdisjoint]

/-- Every rough support-cardinality-one fibre, hence every rough prime
power, is annihilated by Lambert dilation. -/
theorem finiteZeroOneLargePrimeSupportDivisorSum_eq_zero_of_disjoint_card_one
    {α : Type*} [DecidableEq α] {P R : Finset α}
    (hdisjoint : Disjoint R P) (hcard : R.card = 1) :
    finiteZeroOneLargePrimeSupportDivisorSum P R = 0 := by
  rw [finiteZeroOneLargePrimeSupportDivisorSum_eq_of_disjoint hdisjoint, hcard]
  norm_num

/-- Every genuinely transverse rough fibre has a fixed negative Lambert
orientation. -/
theorem finiteZeroOneLargePrimeSupportDivisorSum_neg_of_disjoint_two_le
    {α : Type*} [DecidableEq α] {P R : Finset α}
    (hdisjoint : Disjoint R P) (hcard : 2 ≤ R.card) :
    finiteZeroOneLargePrimeSupportDivisorSum P R < 0 := by
  rw [finiteZeroOneLargePrimeSupportDivisorSum_eq_of_disjoint hdisjoint]
  exact sub_neg.mpr (by exact_mod_cast (lt_of_lt_of_le Nat.one_lt_two hcard))

/-- On every nonempty support, the two-or-more-large sector image is the
negative of the zero/one sector image.  This is the exact finite
sector-reassignment identity behind `L R_{≥2,z} = C_z`. -/
theorem finiteTwoLargePrimeSupportDivisorSum_eq_neg_zeroOne_of_nonempty
    {α : Type*} [DecidableEq α] {P R : Finset α}
    (hR : R.Nonempty) :
    finiteTwoLargePrimeSupportDivisorSum P R =
      -finiteZeroOneLargePrimeSupportDivisorSum P R := by
  have hfull :=
    Finset.sum_powerset_neg_one_pow_card_of_nonempty (x := R) hR
  rw [sum_powerset_neg_one_pow_card_eq_zeroOne_add_twoLarge P R] at hfull
  linarith

/-- A small support label also annihilates the complementary remainder
fibre. -/
theorem finiteTwoLargePrimeSupportDivisorSum_eq_zero_of_small
    {α : Type*} [DecidableEq α] {P R : Finset α}
    (hsmall : (R ∩ P).Nonempty) :
    finiteTwoLargePrimeSupportDivisorSum P R = 0 := by
  have hR : R.Nonempty := by
    obtain ⟨q, hq⟩ := hsmall
    exact ⟨q, (Finset.mem_inter.mp hq).1⟩
  rw [finiteTwoLargePrimeSupportDivisorSum_eq_neg_zeroOne_of_nonempty hR,
    finiteZeroOneLargePrimeSupportDivisorSum_eq_zero_of_small hsmall, neg_zero]

/-- A rough prime-power support has no two-or-more-large remainder
image. -/
theorem finiteTwoLargePrimeSupportDivisorSum_eq_zero_of_disjoint_card_one
    {α : Type*} [DecidableEq α] {P R : Finset α}
    (hdisjoint : Disjoint R P) (hcard : R.card = 1) :
    finiteTwoLargePrimeSupportDivisorSum P R = 0 := by
  have hR : R.Nonempty := Finset.card_pos.mp (by omega)
  rw [finiteTwoLargePrimeSupportDivisorSum_eq_neg_zeroOne_of_nonempty hR,
    finiteZeroOneLargePrimeSupportDivisorSum_eq_zero_of_disjoint_card_one
      hdisjoint hcard,
    neg_zero]

/-- Every transverse rough remainder fibre has the positive coefficient
`|R| - 1`; this is exactly the positive rough-composite Lambert tail,
not the hard zero/one source. -/
theorem finiteTwoLargePrimeSupportDivisorSum_eq_card_sub_one_of_disjoint_two_le
    {α : Type*} [DecidableEq α] {P R : Finset α}
    (hdisjoint : Disjoint R P) (hcard : 2 ≤ R.card) :
    finiteTwoLargePrimeSupportDivisorSum P R = (R.card : ℤ) - 1 := by
  have hR : R.Nonempty := Finset.card_pos.mp (by omega)
  rw [finiteTwoLargePrimeSupportDivisorSum_eq_neg_zeroOne_of_nonempty hR,
    finiteZeroOneLargePrimeSupportDivisorSum_eq_of_disjoint hdisjoint]
  ring

/-- Set difference by the canonical small-prime aperture is exactly the
existing Route E large-prime support. -/
theorem primeFactors_sdiff_mobiusFinitePrimeAperture
    (z n : ℕ) :
    n.primeFactors \ mobiusFinitePrimeAperture z =
      mobiusLargePrimeFactors z n := by
  ext p
  simp only [Finset.mem_sdiff, mobiusFinitePrimeAperture,
    Finset.mem_filter, Finset.mem_range, mobiusLargePrimeFactors]
  by_cases hp : p ∈ n.primeFactors
  · have hpPrime : p.Prime := Nat.prime_of_mem_primeFactors hp
    simp only [hp, true_and, hpPrime, and_true]
    omega
  · simp [hp]

/-- Concrete arithmetic specialization: a `z`-rough integer fibre has
Lambert coefficient `1 - ω(n)`. -/
theorem finiteZeroOneLargePrimeSupportDivisorSum_primeFactors_eq_of_rough
    {z n : ℕ}
    (hrough : Disjoint n.primeFactors (mobiusFinitePrimeAperture z)) :
    finiteZeroOneLargePrimeSupportDivisorSum
        (mobiusFinitePrimeAperture z) n.primeFactors =
      1 - (mobiusLargePrimeFactorCount z n : ℤ) := by
  have hsdiff :
      n.primeFactors \ mobiusFinitePrimeAperture z = n.primeFactors := by
    ext p
    simp only [Finset.mem_sdiff]
    constructor
    · exact fun hp => hp.1
    · intro hp
      exact ⟨hp, Finset.disjoint_left.mp hrough hp⟩
  rw [finiteZeroOneLargePrimeSupportDivisorSum_eq_of_disjoint hrough,
    mobiusLargePrimeFactorCount, ← primeFactors_sdiff_mobiusFinitePrimeAperture,
    hsdiff]

end RHTower
