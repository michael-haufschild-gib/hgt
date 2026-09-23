import GaloisForLFunctions.HTGeometry.RelativeLogCharacteristicSourceBridge
import GaloisForLFunctions.HTGeometry.MultipleGammaDifferenceOperatorAlgebra
import GaloisForLFunctions.HTGeometry.OrderTwoStructuralTranslateDecomposition
import GaloisForLFunctions.HTGeometry.PhysicalArcContactVeronese
import GaloisForLFunctions.HTGeometry.VeroneseSourceHeightIncidence

/-!
# Positive physical tangency from a natural resonant source

The augmentation degree of a difference operator is the least total degree of a monomial occurring
in it.  Pulling back along the physical exponential arc multiplies each monomial by the
corresponding power of the arc parameter, so contact order is at least the augmentation degree.

Equality can fail, and it fails for a genuine special-function reason rather than an engineered
one.  When three structural directions satisfy the additive resonance `τ_c = τ_a + τ_b`, the group
identity `T_c = T_a T_b` gives an operator that annihilates every germ:

```text
Q = (1 + x_a)(1 + x_b) - (1 + x_c).
```

Its augmentation degree is one, because its linear part `x_a + x_b - x_c` is nonzero.  Its arc
pullback is `τ_a τ_b λ²`, because the linear part is exactly what the resonance cancels.  So the
physical contact order is two and the tangency excess is one, for the actual multiple elliptic
gamma logarithmic derivative carried by a resonant period frame.

Integral independence of the periods is therefore not a convenience hypothesis in the zero-tangency
theorem: it is what forbids this operator.
-/

open Filter Set Topology Function Complex
open scoped Differential BigOperators

namespace GaloisForLFunctions.VeroneseIdeal

open MvPolynomial

noncomputable section

variable {R σ : Type*} [CommRing R]

/-! ## The augmentation degree -/

/-- The augmentation degree of a difference operator: the least total degree of a monomial
occurring in it. -/
def augDegree (P : MvPolynomial σ R) : ℕ :=
  sInf {n | ∃ d ∈ P.support, (d.sum fun _ e => e) = n}

theorem augDegree_le_of_mem_support {P : MvPolynomial σ R} {d : σ →₀ ℕ} (hd : d ∈ P.support) :
    augDegree P ≤ d.sum fun _ e => e :=
  Nat.sInf_le ⟨d, hd, rfl⟩

theorem sum_eq_zero_iff_eq_zero {d : σ →₀ ℕ} : (d.sum fun _ e => e) = 0 ↔ d = 0 := by
  classical
  constructor
  · intro h
    ext i
    by_cases hi : i ∈ d.support
    · exact absurd (Finset.sum_eq_zero_iff.mp h i hi) (Finsupp.mem_support_iff.mp hi)
    · simpa using Finsupp.notMem_support_iff.mp hi
  · rintro rfl
    simp

/-- The augmentation degree is positive exactly when the constant term vanishes. -/
theorem one_le_augDegree_iff {P : MvPolynomial σ R} (hP : P ≠ 0) :
    1 ≤ augDegree P ↔ MvPolynomial.coeff 0 P = 0 := by
  classical
  have hne : {n | ∃ d ∈ P.support, (d.sum fun _ e => e) = n}.Nonempty := by
    obtain ⟨d, hd⟩ := Finset.nonempty_iff_ne_empty.mpr
      (fun h => hP (MvPolynomial.support_eq_empty.mp h))
    exact ⟨_, d, hd, rfl⟩
  rw [Nat.one_le_iff_ne_zero, Ne, augDegree, Nat.sInf_eq_zero]
  constructor
  · intro h
    by_contra hc
    exact h (Or.inl ⟨0, MvPolynomial.mem_support_iff.mpr hc, by simp⟩)
  · rintro hc (⟨d, hd, hdeg⟩ | hempty)
    · rw [sum_eq_zero_iff_eq_zero.mp hdeg] at hd
      exact MvPolynomial.mem_support_iff.mp hd hc
    · exact absurd hempty hne.ne_empty

/-- The augmentation degree is exactly one when the constant term vanishes and some linear
monomial occurs. -/
theorem augDegree_eq_one {P : MvPolynomial σ R} (hP : P ≠ 0) (h0 : MvPolynomial.coeff 0 P = 0)
    {j : σ} (hj : MvPolynomial.coeff (Finsupp.single j 1) P ≠ 0) :
    augDegree P = 1 := by
  classical
  refine le_antisymm ?_ ((one_le_augDegree_iff hP).mpr h0)
  have hmem : (Finsupp.single j 1 : σ →₀ ℕ) ∈ P.support := MvPolynomial.mem_support_iff.mpr hj
  have hdeg : ((Finsupp.single j (1 : ℕ)).sum fun _ e => e) = 1 :=
    Finsupp.sum_single_index rfl
  exact hdeg ▸ augDegree_le_of_mem_support hmem

/-! ## Contact order is at least the augmentation degree -/

variable {ι : Type*}

/-- **`(14b)`.**  If every monomial of `P` has total degree at least `n`, its arc pullback is
divisible by `λ^n`. -/
theorem pow_dvd_physicalArcPullback_of_le_degree (τ : ι → ℂ) {n : ℕ}
    {P : MvPolynomial ι ℂ} (hP : ∀ d ∈ P.support, n ≤ d.sum fun _ e => e) :
    (Polynomial.X : Polynomial ℂ) ^ n ∣ physicalArcPullback τ P := by
  classical
  rw [P.as_sum, map_sum]
  refine Finset.dvd_sum fun d hd => ?_
  rw [physicalArcPullback_monomial]
  exact Dvd.dvd.mul_left (pow_dvd_pow _ (hP d hd)) _

/-- **Contact order dominates source height.**  The arc pullback of any operator is divisible by
the augmentation-degree power of the arc parameter. -/
theorem pow_augDegree_dvd_physicalArcPullback (τ : ι → ℂ) (P : MvPolynomial ι ℂ) :
    (Polynomial.X : Polynomial ℂ) ^ augDegree P ∣ physicalArcPullback τ P :=
  pow_dvd_physicalArcPullback_of_le_degree τ fun _ hd => augDegree_le_of_mem_support hd

/-! ## The augmentation height of the squarefree annihilator -/

theorem le_augDegree_of_monoWide {r : ℕ} {P : MvPolynomial σ R} (hP : MonoWide r P)
    (hP0 : P ≠ 0) : r ≤ augDegree P := by
  classical
  have hne : {n | ∃ d ∈ P.support, (d.sum fun _ e => e) = n}.Nonempty := by
    obtain ⟨d, hd⟩ := Finset.nonempty_iff_ne_empty.mpr
      (fun h => hP0 (MvPolynomial.support_eq_empty.mp h))
    exact ⟨_, d, hd, rfl⟩
  obtain ⟨d, hd, hdeg⟩ := Nat.sInf_mem hne
  rw [augDegree, ← hdeg]
  calc r ≤ d.support.card := hP d (MvPolynomial.mem_support_iff.mp hd)
    _ ≤ d.sum fun _ e => e := card_support_le_sum d

theorem augDegree_prod_X [DecidableEq σ] [Nontrivial R] (J : Finset σ) :
    augDegree (∏ j ∈ J, (X j : MvPolynomial σ R)) = J.card := by
  classical
  have hdeg : ((∑ j ∈ J, Finsupp.single j (1 : ℕ)).sum fun _ e => e) = J.card := by
    rw [Finsupp.sum, support_sum_single]
    refine (Finset.sum_congr rfl fun i hi => ?_).trans (by rw [Finset.card_eq_sum_ones])
    rw [sum_single_apply, if_pos hi]
  have hsupp : (∏ j ∈ J, (X j : MvPolynomial σ R)).support =
      {∑ j ∈ J, Finsupp.single j 1} := by
    rw [prod_X_eq_monomial, MvPolynomial.support_monomial, if_neg (one_ne_zero (α := R))]
  have hset : {n | ∃ d ∈ (∏ j ∈ J, (X j : MvPolynomial σ R)).support,
      (d.sum fun _ e => e) = n} = {J.card} := by
    ext n
    rw [hsupp]
    constructor
    · rintro ⟨d, hd, rfl⟩
      rw [Finset.mem_singleton.mp hd, hdeg]
      rfl
    · rintro rfl
      exact ⟨_, Finset.mem_singleton_self _, hdeg⟩
  rw [augDegree, hset]
  exact csInf_singleton _

/-- **`h(I_r) = r` in the augmentation reading.**  Every nonzero element of the squarefree
degree-`r` ideal has augmentation degree at least `r`, and a coface generator attains it. -/
theorem isLeast_augDegrees_veroneseIdeal [DecidableEq σ] [Nontrivial R] {r : ℕ} {J : Finset σ}
    (hJ : J.card = r) :
    IsLeast {n | ∃ P ∈ veroneseIdeal R σ r, P ≠ 0 ∧ augDegree P = n} r := by
  refine ⟨⟨∏ j ∈ J, X j, Ideal.subset_span ⟨J, hJ, rfl⟩, prod_X_ne_zero J,
    (augDegree_prod_X J).trans hJ⟩, ?_⟩
  rintro n ⟨P, hP, hP0, rfl⟩
  exact le_augDegree_of_monoWide (monoWide_of_mem_ideal hP) hP0

end

end GaloisForLFunctions.VeroneseIdeal

namespace GaloisForLFunctions

open Bottcher HTGeometry VeroneseIdeal

noncomputable section

attribute [local instance] facePacketMeroDecidableEq

attribute [local instance] ellipticGammaRationalBaseDomain
  ellipticGammaRationalBaseComplexAlgebraMero ellipticGammaRationalBaseComplexDifferential
  ellipticGammaRationalBaseMeroDifferential ellipticGammaRationalBaseMeroCharZero
  ellipticGammaRationalBaseComplexDifferentialAlgebra
  ellipticGammaRationalBaseCoordinateDifferential
  ellipticGammaRationalBaseCoordinateDifferentialAlgebra

attribute [local instance] relativeGaugeDomain relativeGaugeDifferential
  relativeGaugeRatFuncAlgebra relativeGaugeRatFuncDifferential relativeGaugeDifferentialAlgebra
  relativeGaugeCharZeroBase relativeGaugeCharZero relativeGaugeComplexAlgebra
  relativeGaugeComplexAlgebraAnalytic

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-! ## The resonance operator -/

omit [Fintype ι] in
theorem xApply_sub (τ : ι → ℂ) (P Q : MvPolynomial ι ℂ)
    (y : meroField (Set.univ : Set ℂ)) :
    xApply τ (P - Q) y = xApply τ P y - xApply τ Q y := by
  have h := xApply_add τ (P - Q) Q y
  rw [sub_add_cancel] at h
  rw [h]
  abel

/-- The operator expressing the group identity `T_c = T_a T_b` of a resonant direction triple. -/
def resonanceOperator (a b c : ι) : MvPolynomial ι ℂ :=
  (1 + MvPolynomial.X a) * (1 + MvPolynomial.X b) - (1 + MvPolynomial.X c)

omit [Fintype ι] in
/-- **The resonance operator annihilates every germ.**  Its two translation terms are the same
structural translation. -/
theorem xApply_resonanceOperator (τ : ι → ℂ) {a b c : ι} (hres : τ c = τ a + τ b)
    (y : meroField (Set.univ : Set ℂ)) :
    xApply τ (resonanceOperator a b c) y = 0 := by
  rw [resonanceOperator, xApply_sub, xApply_mul, xApply_one_add_X, xApply_one_add_X,
    xApply_one_add_X, addTranslationMeroEquiv_add, hres, sub_self]

/-! ## Its augmentation degree is one -/

omit [Fintype ι] [DecidableEq ι] in
theorem resonanceOperator_eq (a b c : ι) :
    resonanceOperator a b c =
      MvPolynomial.X a + MvPolynomial.X b + MvPolynomial.X a * MvPolynomial.X b -
        MvPolynomial.X c := by
  rw [resonanceOperator]
  ring

omit [Fintype ι] [DecidableEq ι] in
theorem X_mul_X_eq_monomial (a b : ι) :
    (MvPolynomial.X a : MvPolynomial ι ℂ) * MvPolynomial.X b =
      MvPolynomial.monomial (Finsupp.single a 1 + Finsupp.single b 1) 1 := by
  rw [MvPolynomial.X, MvPolynomial.X, MvPolynomial.monomial_mul, one_mul]

omit [Fintype ι] [DecidableEq ι] in
theorem coeff_zero_resonanceOperator (a b c : ι) :
    MvPolynomial.coeff 0 (resonanceOperator a b c) = 0 := by
  classical
  have hX : ∀ j : ι, MvPolynomial.coeff 0 (MvPolynomial.X j : MvPolynomial ι ℂ) = 0 := by
    intro j
    rw [MvPolynomial.coeff_X]
    refine if_neg fun h => ?_
    have := congrArg (fun f : ι →₀ ℕ => f j) h
    simp at this
  have hmul : MvPolynomial.coeff 0
      ((MvPolynomial.X a : MvPolynomial ι ℂ) * MvPolynomial.X b) = 0 := by
    rw [X_mul_X_eq_monomial, MvPolynomial.coeff_monomial]
    refine if_neg fun h => ?_
    have := congrArg (fun f : ι →₀ ℕ => f a) h
    simp [Finsupp.add_apply] at this
  rw [resonanceOperator_eq, MvPolynomial.coeff_sub, MvPolynomial.coeff_add,
    MvPolynomial.coeff_add, hX, hX, hX, hmul]
  ring

omit [Fintype ι] [DecidableEq ι] in
theorem coeff_single_resonanceOperator {a b c : ι} (hab : a ≠ b) (hac : a ≠ c) :
    MvPolynomial.coeff (Finsupp.single a 1) (resonanceOperator a b c) = 1 := by
  classical
  have hXa : MvPolynomial.coeff (Finsupp.single a 1)
      (MvPolynomial.X a : MvPolynomial ι ℂ) = 1 := by
    rw [MvPolynomial.coeff_X, if_pos rfl]
  have hXb : MvPolynomial.coeff (Finsupp.single a 1)
      (MvPolynomial.X b : MvPolynomial ι ℂ) = 0 := by
    rw [MvPolynomial.coeff_X]
    refine if_neg fun h => ?_
    have := congrArg (fun f : ι →₀ ℕ => f a) h
    simp [hab.symm] at this
  have hXc : MvPolynomial.coeff (Finsupp.single a 1)
      (MvPolynomial.X c : MvPolynomial ι ℂ) = 0 := by
    rw [MvPolynomial.coeff_X]
    refine if_neg fun h => ?_
    have := congrArg (fun f : ι →₀ ℕ => f a) h
    simp [hac.symm] at this
  have hmul : MvPolynomial.coeff (Finsupp.single a 1)
      ((MvPolynomial.X a : MvPolynomial ι ℂ) * MvPolynomial.X b) = 0 := by
    rw [X_mul_X_eq_monomial, MvPolynomial.coeff_monomial]
    refine if_neg fun h => ?_
    have := congrArg (fun f : ι →₀ ℕ => f b) h
    simp [Finsupp.add_apply, hab.symm] at this
  rw [resonanceOperator_eq, MvPolynomial.coeff_sub, MvPolynomial.coeff_add,
    MvPolynomial.coeff_add, hXa, hXb, hXc, hmul]
  ring

omit [Fintype ι] [DecidableEq ι] in
theorem resonanceOperator_ne_zero {a b c : ι} (hab : a ≠ b) (hac : a ≠ c) :
    resonanceOperator a b c ≠ 0 := by
  intro h
  have hc := coeff_single_resonanceOperator hab hac
  rw [h] at hc
  simp at hc

omit [Fintype ι] [DecidableEq ι] in
/-- **Source height one.** -/
theorem augDegree_resonanceOperator {a b c : ι} (hab : a ≠ b) (hac : a ≠ c) :
    augDegree (resonanceOperator a b c) = 1 :=
  augDegree_eq_one (resonanceOperator_ne_zero hab hac) (coeff_zero_resonanceOperator a b c)
    (by rw [coeff_single_resonanceOperator hab hac]; exact one_ne_zero)

/-! ## Its physical contact order is two -/

omit [Fintype ι] [DecidableEq ι] in
theorem physicalArcPullback_resonanceOperator (τ : ι → ℂ) {a b c : ι} (hres : τ c = τ a + τ b) :
    physicalArcPullback τ (resonanceOperator a b c) =
      Polynomial.C (τ a * τ b) * Polynomial.X ^ (2 : ℕ) := by
  simp only [resonanceOperator, map_sub, map_mul, map_add, map_one, physicalArcPullback_X, hres]
  ring

omit [Fintype ι] [DecidableEq ι] in
/-- **Contact order exactly two.** -/
theorem physicalArcContact_resonanceOperator (τ : ι → ℂ) {a b c : ι} (hres : τ c = τ a + τ b)
    (ha : τ a ≠ 0) (hb : τ b ≠ 0) :
    (Polynomial.X : Polynomial ℂ) ^ (2 : ℕ) ∣ physicalArcPullback τ (resonanceOperator a b c) ∧
      ¬ (Polynomial.X : Polynomial ℂ) ^ (3 : ℕ) ∣
        physicalArcPullback τ (resonanceOperator a b c) := by
  rw [physicalArcPullback_resonanceOperator τ hres]
  refine ⟨Dvd.intro_left _ rfl, fun hdvd => ?_⟩
  have hcoeff : (Polynomial.C (τ a * τ b) * Polynomial.X ^ (2 : ℕ)).coeff 2 = τ a * τ b := by
    rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, if_pos rfl, mul_one]
  have hzero : (Polynomial.C (τ a * τ b) * Polynomial.X ^ (2 : ℕ)).coeff 2 = 0 :=
    Polynomial.X_pow_dvd_iff.mp hdvd 2 (by omega)
  rw [hcoeff] at hzero
  exact (mul_ne_zero ha hb) hzero

/-! ## The natural source realization -/

/-- **Positive physical tangency in a genuine multiple elliptic gamma.**  For a resonant period
frame the differential-algebraic translation annihilator of the actual logarithmic derivative
contains an operator of augmentation degree one whose physical contact order is exactly two: the
tangency excess `(14c)` is one, realized by the additive period relation rather than by an
engineered constraint. -/
theorem resonantSource_positiveTangency
    (τ : ι → ℂ) (hτ : ∀ i, 0 < (τ i).im) {a b c : ι} (hab : a ≠ b) (hac : a ≠ c)
    (hres : τ c = τ a + τ b) :
    resonanceOperator a b c ∈ daTranslationAnnihilator τ hτ ∧
      resonanceOperator a b c ≠ 0 ∧
      augDegree (resonanceOperator a b c) = 1 ∧
      (Polynomial.X : Polynomial ℂ) ^ (2 : ℕ) ∣ physicalArcPullback τ (resonanceOperator a b c) ∧
      ¬ (Polynomial.X : Polynomial ℂ) ^ (3 : ℕ) ∣
        physicalArcPullback τ (resonanceOperator a b c) := by
  have hane : τ a ≠ 0 := by
    intro h
    have him := hτ a
    rw [h] at him
    simp at him
  have hbne : τ b ≠ 0 := by
    intro h
    have him := hτ b
    rw [h] at him
    simp at him
  refine ⟨?_, resonanceOperator_ne_zero hab hac, augDegree_resonanceOperator hab hac,
    (physicalArcContact_resonanceOperator τ hres hane hbne).1,
    (physicalArcContact_resonanceOperator τ hres hane hbne).2⟩
  show DifferentialAlgebraicOver (RatFunc ℂ) _
  rw [xApply_resonanceOperator τ hres]
  exact differentialAlgebraicOver_zero

/-! ## An explicit resonant frame -/

/-- The order-two resonant period frame `(i, 2i, 3i)`. -/
def resonantFrame : Fin 3 → ℂ := ![Complex.I, 2 * Complex.I, 3 * Complex.I]

theorem resonantFrame_im_pos : ∀ i, 0 < (resonantFrame i).im := by
  intro i
  fin_cases i <;> simp [resonantFrame]

theorem resonantFrame_resonance : resonantFrame 2 = resonantFrame 0 + resonantFrame 1 := by
  simp [resonantFrame]
  ring

/-- **The discriminator is realized by an actual special function.**  The order-two multiple
elliptic gamma logarithmic derivative carried by the frame `(i, 2i, 3i)` has an annihilating
difference operator of source degree one and physical contact order two. -/
theorem resonantFrame_positiveTangency :
    resonanceOperator (0 : Fin 3) 1 2 ∈
        daTranslationAnnihilator resonantFrame resonantFrame_im_pos ∧
      augDegree (resonanceOperator (0 : Fin 3) 1 2) = 1 ∧
      (Polynomial.X : Polynomial ℂ) ^ (2 : ℕ) ∣
        physicalArcPullback resonantFrame (resonanceOperator (0 : Fin 3) 1 2) ∧
      ¬ (Polynomial.X : Polynomial ℂ) ^ (3 : ℕ) ∣
        physicalArcPullback resonantFrame (resonanceOperator (0 : Fin 3) 1 2) := by
  obtain ⟨h1, _, h3, h4, h5⟩ :=
    resonantSource_positiveTangency resonantFrame resonantFrame_im_pos
      (a := 0) (b := 1) (c := 2) (by decide) (by decide) resonantFrame_resonance
  exact ⟨h1, h3, h4, h5⟩

/-! ## Independence is necessary for the annihilator theorem -/

omit [Fintype ι] in
/-- An operator of augmentation degree one cannot lie in a squarefree ideal of degree at least
two. -/
theorem resonanceOperator_not_mem_veroneseIdeal {a b c : ι} (hab : a ≠ b) (hac : a ≠ c)
    {r : ℕ} (hr : 2 ≤ r) : resonanceOperator a b c ∉ veroneseIdeal ℂ ι r := by
  intro hmem
  have hle := le_augDegree_of_monoWide (monoWide_of_mem_ideal hmem)
    (resonanceOperator_ne_zero hab hac)
  rw [augDegree_resonanceOperator hab hac] at hle
  omega

/-- **The zero-tangency theorem needs integral independence.**  For a resonant frame of order at
least two the differential-algebraic translation annihilator strictly contains the squarefree
degree-`r` ideal, and the extra operator has augmentation degree one and physical contact order
two, so the tangency excess of the annihilator is positive. -/
theorem resonantSource_annihilator_strictly_larger
    (τ : ι → ℂ) (hτ : ∀ i, 0 < (τ i).im) {a b c : ι} (hab : a ≠ b) (hac : a ≠ c)
    (hres : τ c = τ a + τ b) {r : ℕ} (hr : 2 ≤ r) (hcard : Fintype.card ι = r + 1) :
    ((veroneseIdeal ℂ ι r : Set (MvPolynomial ι ℂ)) ⊆ daTranslationAnnihilator τ hτ) ∧
      resonanceOperator a b c ∈ daTranslationAnnihilator τ hτ ∧
      resonanceOperator a b c ∉ veroneseIdeal ℂ ι r ∧
      augDegree (resonanceOperator a b c) = 1 ∧
      ¬ (Polynomial.X : Polynomial ℂ) ^ (3 : ℕ) ∣
        physicalArcPullback τ (resonanceOperator a b c) := by
  obtain ⟨hmem, _, hdeg, _, hcontact⟩ :=
    resonantSource_positiveTangency τ hτ hab hac hres
  refine ⟨fun P hP => ?_, hmem, resonanceOperator_not_mem_veroneseIdeal hab hac hr, hdeg,
    hcontact⟩
  exact differentialAlgebraicOver_xApply_of_mem_veroneseIdeal τ hτ r
    (card_le_one_compl_of_card_le r hcard) hP

end

end GaloisForLFunctions
