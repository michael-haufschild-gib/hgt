import GaloisForLFunctions.HTGeometry.PrimeValuationVeroneseMaster

namespace GaloisForLFunctions.HTGeometry

open MvPolynomial ArithmeticFunction
open scoped Differential

noncomputable section

universe u

set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 80000

local instance complexFinitePrimeRationalAmbientScalarTowerRecurring :
    IsScalarTower ℂ finitePrimeRationalCoefficientField
      arithmeticFunctionRationalCoordinateField :=
  .of_algebraMap_eq fun z => by
    change algebraMap ℂ arithmeticFunctionRationalCoordinateField z =
      finitePrimeRationalCoefficientFieldToFormalRatFunc
        (algebraMap ℂ finitePrimeRationalCoefficientField z)
    rw [IsScalarTower.algebraMap_apply ℂ finitePrimeCoefficientField
      finitePrimeRationalCoefficientField]
    rw [finitePrimeRationalCoefficientFieldToFormalRatFunc_algebraMap]
    rw [← IsScalarTower.algebraMap_apply ℂ finitePrimeCoefficientField
      arithmeticFunctionFractionField]
    rw [IsScalarTower.algebraMap_apply ℂ arithmeticFunctionFractionField
      arithmeticFunctionRationalCoordinateField]

/-- All but finitely many coordinates belong to an infinite value fibre. -/
def CofinitelyRecurring {P V : Type*} (x : P → V) : Prop :=
  {p | x p ∉ recurringValueSet x}.Finite

/-- Cofinal recurrence is exactly the hypothesis needed to replace finite range in the
observable tail kernel. -/
theorem cofinitelyRecurring_observable_support_finite_iff
    {P V : Type*} (x : P → V) (hrec : CofinitelyRecurring x) (f : V → ℂ) :
    {p | f (x p) ≠ 0}.Finite ↔ ∀ v ∈ recurringValueSet x, f v = 0 := by
  constructor
  · intro hsupp v hv
    by_contra hfv
    have hsub : {p | x p = v} ⊆ {p | f (x p) ≠ 0} := by
      intro p hp
      change x p = v at hp
      change f (x p) ≠ 0
      simpa [hp] using hfv
    exact (hv.mono hsub) hsupp
  · intro hvanish
    apply hrec.subset
    intro p hp
    change f (x p) ≠ 0 at hp
    change x p ∉ recurringValueSet x
    intro hx
    exact hp (hvanish (x p) hx)

/-- Homogeneous tail relations for a cofinally recurrent source are exactly the homogeneous
polynomials vanishing on the recurrent locus. -/
theorem homogeneousTailRelationSubmodule_eq_recurringVanishing_of_cofinitelyRecurring
    {P σ : Type*} (x : P → σ → ℂ) (hrec : CofinitelyRecurring x) (m : ℕ) :
    homogeneousTailRelationSubmodule x m =
      homogeneousRecurringVanishingSubmodule x m := by
  ext Q
  exact cofinitelyRecurring_observable_support_finite_iff x hrec
    (fun v => eval v Q.1)

/-- The cofinally recurrent valuation-tail quotient is canonically the recurrent homogeneous
coordinate image. -/
noncomputable def homogeneousTailQuotientEquivRecurringRange_of_cofinitelyRecurring
    {P σ : Type*} (x : P → σ → ℂ) (hrec : CofinitelyRecurring x) (m : ℕ) :
    (homogeneousSubmodule σ ℂ m ⧸ homogeneousTailRelationSubmodule x m) ≃ₗ[ℂ]
      LinearMap.range (homogeneousRecurringEvaluation x m) := by
  rw [homogeneousTailRelationSubmodule_eq_recurringVanishing_of_cofinitelyRecurring x hrec m,
    homogeneousRecurringVanishingSubmodule_eq_ker]
  exact (homogeneousRecurringEvaluation x m).quotKerEquivRange

/-- A recurrent homogeneous pivot basis automatically has enough infinitely repeated coefficient
patterns to separate every finite shift--jet rectangle. -/
theorem RecurrentHomogeneousValuationPresentation.pivotColumn_recurringPatternsSpan
    {d : ℕ} {σ : Type u} {J R : Fin d → Type u} [∀ r, Fintype (J r)]
    {x : Nat.Primes → σ → ℂ}
    (P : RecurrentHomogeneousValuationPresentation d σ J R x) (r : Fin d) :
    RecurringCoefficientPatternsSpan (P.pivotColumn r) := by
  classical
  intro a hvanish
  have hLI := P.pivotRecurringIndependent r
  rw [Fintype.linearIndependent_iff] at hLI
  have hsum : (∑ i, a i • (fun v : recurringValueSet x =>
      eval v.1 (P.pivot r i).1)) = 0 := by
    funext v
    let b : J r → ℂ := fun j => eval v.1 (P.pivot r j).1
    have hb : {p | coefficientPattern (P.pivotColumn r) p = b}.Infinite := by
      apply v.2.mono
      intro p hp
      change x p = v.1 at hp
      change coefficientPattern (P.pivotColumn r) p = b
      funext j
      simp only [coefficientPattern, RecurrentHomogeneousValuationPresentation.pivotColumn, b]
      rw [hp]
    have hz := hvanish b hb
    simpa only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, b, Pi.zero_apply] using hz
  funext j
  exact hLI a hsum j

/-- Recurrent coordinate expansions fail only on the finite nonrecurrent locus. -/
theorem RecurrentHomogeneousValuationPresentation.residualFinite_of_cofinitelyRecurring
    {d : ℕ} {σ : Type u} {J R : Fin d → Type u} [∀ r, Fintype (J r)]
    {x : Nat.Primes → σ → ℂ}
    (P : RecurrentHomogeneousValuationPresentation d σ J R x)
    (hrec : CofinitelyRecurring x) (r : Fin d) (q : R r) :
    {p | P.dependentColumn r q p -
      ∑ j, P.coefficient r q j * P.pivotColumn r j p ≠ 0}.Finite := by
  apply (cofinitelyRecurring_observable_support_finite_iff x hrec
    (fun v => eval v (P.dependent r q).1 -
      ∑ j, P.coefficient r q j * eval v (P.pivot r j).1)).2
  intro v hv
  rw [P.dependentRecurringExpansion r q ⟨v, hv⟩]
  ring

/-- Recurring coefficient patterns, rather than finite coefficient range, suffice for every
finite shifted logarithmic jet rectangle in a prime-power valuation layer. -/
theorem primePowerCoefficientShiftedRotatedJet_tailIndependent_of_recurringPatternsSpan
    {J A : Type*} [Fintype J] [Fintype A]
    (e : ℕ) (c : J → Nat.Primes → ℂ) (alpha : A → ℂ)
    (hdistinct : Function.Injective (fun a ↦ (alpha a).re))
    (hspan : RecurringCoefficientPatternsSpan c) (m : ℕ) :
    TailCoefficientIndependent
      (fun jak : J × (A × Fin (m + 1)) ↦ fun p ↦
        c jak.1 p * primeShiftFactor (alpha jak.2.1) p *
          ((((e + 1 : ℕ) : ℂ) * rotatedPrimeLogClock p) ^
            (jak.2.2 : ℕ))) := by
  classical
  let raw : J × (A × Fin (m + 1)) → Nat.Primes → ℂ := fun jak p ↦
    c jak.1 p * primeShiftFactor (alpha jak.2.1) p *
      primeLogClock p ^ (jak.2.2 : ℕ)
  let u : J × (A × Fin (m + 1)) → ℂ := fun jak ↦
    ((((e + 1 : ℕ) : ℂ) * Complex.I) ^ (jak.2.2 : ℕ))
  have hu : ∀ jak, u jak ≠ 0 := by
    intro jak
    apply pow_ne_zero
    exact mul_ne_zero (by exact_mod_cast Nat.succ_ne_zero e) Complex.I_ne_zero
  have hscale :
      TailCoefficientIndependent (fun jak p ↦ u jak * raw jak p) ↔
        TailCoefficientIndependent raw :=
    tailCoefficientIndependent_scale_columns_iff raw u hu
  have hraw : TailCoefficientIndependent raw := by
    simpa only [raw, coefficientShiftJet] using!
      coefficientShiftJet_tailIndependent_of_recurringPatternsSpan c
        (fun a p ↦ primeShiftFactor (alpha a) p) primeLogClock hspan m
        (primeFactorClockFiberIndependent alpha hdistinct m)
  apply hscale.mpr at hraw
  convert hraw using 1
  funext jak p
  simp only [u, raw, rotatedPrimeLogClock, mul_pow]
  ring

/-- The recurring-pattern hypothesis supplies algebraic independence of every finite shifted-jet
rectangle across a nonuniform finite valuation window. -/
theorem primePowerCoefficientShiftedJets_algebraicIndependent_of_recurringPatternsSpan
    {d : ℕ} (J B : Fin d → Type u)
    [∀ r, Fintype (J r)] [∀ r, DecidableEq (J r)]
    [∀ r, Fintype (B r)] [∀ r, DecidableEq (B r)]
    (c : ∀ r, J r → Nat.Primes → ℂ) (alpha : ∀ r, B r → ℂ)
    (hdistinct : ∀ r, Function.Injective (fun b ↦ (alpha r b).re))
    (hspan : ∀ r, RecurringCoefficientPatternsSpan (c r))
    (m : Fin d → ℕ) :
    AlgebraicIndependent finitePrimeRationalCoefficientField
      (fun x : Σ r, J r × (B r × Fin (m r + 1)) ↦
        algebraMap arithmeticFunctionFractionField
          arithmeticFunctionRationalCoordinateField
          (algebraMap (ArithmeticFunction ℂ) arithmeticFunctionFractionField
            (primePowerCoefficientShiftedRotatedJet
              x.1 (c x.1 x.2.1) (alpha x.1 x.2.2.1) x.2.2.2))) := by
  let A : Fin d → Type u := fun r ↦ J r × (B r × Fin (m r + 1))
  letI (r : Fin d) : Fintype (A r) := inferInstance
  letI (r : Fin d) : DecidableEq (A r) := inferInstance
  let a : ∀ r, A r → Nat.Primes → ℂ := fun r x p ↦
    c r x.1 p * primeShiftFactor (alpha r x.2.1) p *
      ((((r.1 + 1 : ℕ) : ℂ) * rotatedPrimeLogClock p) ^ (x.2.2 : ℕ))
  have hatail : ∀ r, TailCoefficientIndependent (a r) := by
    intro r
    exact primePowerCoefficientShiftedRotatedJet_tailIndependent_of_recurringPatternsSpan
      r (c r) (alpha r) (hdistinct r) (hspan r) (m r)
  have hraw := algebraicIndependent_primePowerSigmaTower_over_finitePrimeCoefficientField
    d A a hatail
  apply algebraicIndependent_constants_over_finitePrimeRationalCoefficientField at hraw
  simpa only [A, a, primePowerSigmaExponent, primePowerSigmaCoefficient,
    primePowerCoefficientShiftedRotatedJet] using hraw

/-- Recurring-pattern spanning in each valuation layer forces differential independence of the
complete finite shift palette, with no finite-range hypothesis. -/
theorem primePowerCoefficientShiftPalettes_differentialIndependent_of_recurringPatternsSpan
    {d : ℕ} (J B : Fin d → Type u)
    [∀ r, Fintype (J r)] [∀ r, DecidableEq (J r)]
    [∀ r, Fintype (B r)] [∀ r, DecidableEq (B r)]
    [Nonempty (Σ r, J r × B r)]
    (c : ∀ r, J r → Nat.Primes → ℂ) (alpha : ∀ r, B r → ℂ)
    (hdistinct : ∀ r, Function.Injective (fun b ↦ (alpha r b).re))
    (hspan : ∀ r, RecurringCoefficientPatternsSpan (c r)) :
    GaloisForLFunctions.DifferentialIndependent finitePrimeRationalCoefficientField
      (fun x : Σ r, J r × B r ↦
        primePowerCoefficientShiftCarrier x.1 (c x.1 x.2.1) (alpha x.1 x.2.2)) := by
  unfold GaloisForLFunctions.DifferentialIndependent
  simp_rw [differentialJet_primePowerCoefficientShiftCarrier]
  let y : (Σ r, J r × B r) → ℕ → arithmeticFunctionRationalCoordinateField :=
    fun rb k ↦
      algebraMap arithmeticFunctionFractionField arithmeticFunctionRationalCoordinateField
        (algebraMap (ArithmeticFunction ℂ) arithmeticFunctionFractionField
          (primePowerCoefficientShiftedRotatedJet
            rb.1 (c rb.1 rb.2.1) (alpha rb.1 rb.2.2) k))
  apply algebraicIndependent_prod_nat_of_fin y
  intro m
  let f : ((Σ r, J r × B r) × Fin (m + 1)) →
      (Σ r, J r × (B r × Fin (m + 1))) := fun rbk ↦
    ⟨rbk.1.1, (rbk.1.2.1, (rbk.1.2.2, rbk.2))⟩
  have hf : Function.Injective f := by
    rintro ⟨⟨r, j, b⟩, k⟩ ⟨⟨r', j', b'⟩, k'⟩ h
    cases h
    rfl
  have hrect :=
    primePowerCoefficientShiftedJets_algebraicIndependent_of_recurringPatternsSpan
      J B c alpha hdistinct hspan (fun _ ↦ m)
  have hsub := hrect.comp f hf
  simpa only [Function.comp_apply, f, y] using! hsub

/-- A valuation-pivot presentation controlled by infinitely recurring coefficient patterns rather
than by finite coefficient range. -/
structure PrimeValuationRecurringPivotPresentation
    (d : ℕ) (J R : Fin d → Type u) [∀ r, Fintype (J r)] where
  pivot : ∀ r, J r → Nat.Primes → ℂ
  dependent : ∀ r, R r → Nat.Primes → ℂ
  coefficient : ∀ r, R r → J r → ℂ
  pivotShiftJetTailIndependent : ∀ r (A : Type u) [Fintype A]
    (alpha : A → ℂ), Function.Injective (fun a ↦ (alpha a).re) → ∀ m,
      TailCoefficientIndependent
        (fun jak : J r × (A × Fin (m + 1)) ↦ fun p ↦
          pivot r jak.1 p * primeShiftFactor (alpha jak.2.1) p *
            ((((r.1 + 1 : ℕ) : ℂ) * rotatedPrimeLogClock p) ^
              (jak.2.2 : ℕ)))
  residualFinite : ∀ r q,
    {p | dependent r q p - ∑ j, coefficient r q j * pivot r j p ≠ 0}.Finite

def PrimeValuationRecurringPivotPresentation.pivotPalette
    {d : ℕ} {J R A : Fin d → Type u} [∀ r, Fintype (J r)]
    (P : PrimeValuationRecurringPivotPresentation d J R) (α : ∀ r, A r → ℂ)
    (x : Σ r, J r × A r) : arithmeticFunctionRationalCoordinateField :=
  primePowerCoefficientShiftCarrier x.1 (P.pivot x.1 x.2.1) (α x.1 x.2.2)

def PrimeValuationRecurringPivotPresentation.dependentPalette
    {d : ℕ} {J R A : Fin d → Type u} [∀ r, Fintype (J r)]
    (P : PrimeValuationRecurringPivotPresentation d J R) (α : ∀ r, A r → ℂ)
    (x : Σ r, R r × A r) : arithmeticFunctionRationalCoordinateField :=
  primePowerCoefficientShiftCarrier x.1 (P.dependent x.1 x.2.1) (α x.1 x.2.2)

theorem exists_primeValuationRecurringPivotBaseCorrection
    {d : ℕ} {J R : Fin d → Type u} [∀ r, Fintype (J r)]
    (P : PrimeValuationRecurringPivotPresentation d J R)
    (r : Fin d) (q : R r) (a : ℂ) (n : ℕ) :
    ∃ h : finitePrimeRationalCoefficientField,
      GaloisForLFunctions.differentialJet n
          (primePowerCoefficientShiftCarrier r (P.dependent r q) a) =
        algebraMap finitePrimeRationalCoefficientField
            arithmeticFunctionRationalCoordinateField h +
          ∑ j, algebraMap ℂ arithmeticFunctionRationalCoordinateField
              (P.coefficient r q j) *
            GaloisForLFunctions.differentialJet n
              (primePowerCoefficientShiftCarrier r (P.pivot r j) a) := by
  classical
  let combo : Nat.Primes → ℂ := fun p ↦
    ∑ j, P.coefficient r q j * P.pivot r j p
  have hsupport : {p | P.dependent r q p - 1 * combo p ≠ 0}.Finite := by
    simpa [combo] using P.residualFinite r q
  obtain ⟨h, hh⟩ := primePowerCoefficientShiftCarrier_residual_jet_mem_base
    r (P.dependent r q) combo 1 hsupport a n
  refine ⟨h, ?_⟩
  have hcombo := differentialJet_primePowerCoefficientShiftCarrier_linearCombination
    r (P.pivot r) (P.coefficient r q) a n
  change GaloisForLFunctions.differentialJet n
      (primePowerCoefficientShiftCarrier r (P.dependent r q) a) = _
  change GaloisForLFunctions.differentialJet n
      (primePowerCoefficientShiftCarrier r (P.dependent r q) a) -
        algebraMap ℂ arithmeticFunctionRationalCoordinateField 1 *
          GaloisForLFunctions.differentialJet n
            (primePowerCoefficientShiftCarrier r combo a) = _ at hh
  rw [map_one, one_mul, hcombo] at hh
  rw [← hh]
  ring

def PrimeValuationRecurringPivotPresentation.baseCorrection
    {d : ℕ} {J R A : Fin d → Type u} [∀ r, Fintype (J r)]
    (P : PrimeValuationRecurringPivotPresentation d J R) (α : ∀ r, A r → ℂ)
    (x : Σ r, R r × A r) (n : ℕ) : finitePrimeRationalCoefficientField :=
  Classical.choose
    (exists_primeValuationRecurringPivotBaseCorrection
      P x.1 x.2.1 (α x.1 x.2.2) n)

theorem PrimeValuationRecurringPivotPresentation.baseCorrection_spec
    {d : ℕ} {J R A : Fin d → Type u} [∀ r, Fintype (J r)]
    (P : PrimeValuationRecurringPivotPresentation d J R) (α : ∀ r, A r → ℂ)
    (x : Σ r, R r × A r) (n : ℕ) :
    GaloisForLFunctions.differentialJet n (P.dependentPalette α x) =
      algebraMap finitePrimeRationalCoefficientField
          arithmeticFunctionRationalCoordinateField (P.baseCorrection α x n) +
        ∑ j, algebraMap ℂ arithmeticFunctionRationalCoordinateField
            (P.coefficient x.1 x.2.1 j) *
          GaloisForLFunctions.differentialJet n
            (primePowerCoefficientShiftCarrier x.1 (P.pivot x.1 j) (α x.1 x.2.2)) := by
  exact Classical.choose_spec
    (exists_primeValuationRecurringPivotBaseCorrection
      P x.1 x.2.1 (α x.1 x.2.2) n)

def PrimeValuationRecurringPivotPresentation.paletteMatrix
    {d : ℕ} {J R A : Fin d → Type u}
    [∀ r, Fintype (J r)] [∀ r, DecidableEq (A r)]
    (P : PrimeValuationRecurringPivotPresentation d J R) :
    (Σ r, R r × A r) → (Σ r, J r × A r) →
      finitePrimeRationalCoefficientField
  | ⟨r, q, a⟩, ⟨s, j, b⟩ =>
      if hrs : r = s then by
        subst s
        exact if a = b then
          algebraMap ℂ finitePrimeRationalCoefficientField (P.coefficient r q j)
        else 0
      else 0

theorem PrimeValuationRecurringPivotPresentation.palette_affineJet
    {d : ℕ} {J R A : Fin d → Type u}
    [∀ r, Fintype (J r)] [∀ r, Fintype (A r)] [∀ r, DecidableEq (A r)]
    (P : PrimeValuationRecurringPivotPresentation d J R) (α : ∀ r, A r → ℂ)
    (x : Σ r, R r × A r) (n : ℕ) :
    GaloisForLFunctions.differentialJet n (P.dependentPalette α x) =
      algebraMap finitePrimeRationalCoefficientField
          arithmeticFunctionRationalCoordinateField (P.baseCorrection α x n) +
        ∑ y, algebraMap finitePrimeRationalCoefficientField
            arithmeticFunctionRationalCoordinateField (P.paletteMatrix x y) *
          GaloisForLFunctions.differentialJet n (P.pivotPalette α y) := by
  classical
  rcases x with ⟨r, q, a⟩
  rw [P.baseCorrection_spec α ⟨r, (q, a)⟩ n]
  congr 1
  rw [Fintype.sum_sigma]
  rw [Finset.sum_eq_single r]
  · rw [Fintype.sum_prod_type]
    apply Finset.sum_congr rfl
    intro j hj
    rw [Finset.sum_eq_single a]
    · simp [PrimeValuationRecurringPivotPresentation.paletteMatrix,
        PrimeValuationRecurringPivotPresentation.pivotPalette,
        IsScalarTower.algebraMap_apply ℂ finitePrimeRationalCoefficientField
          arithmeticFunctionRationalCoordinateField]
    · intro b hb hba
      simp [PrimeValuationRecurringPivotPresentation.paletteMatrix, hba.symm]
    · simp
  · intro s hs hsr
    apply Finset.sum_eq_zero
    intro y hy
    rcases y with ⟨j, b⟩
    simp [PrimeValuationRecurringPivotPresentation.paletteMatrix, hsr.symm]
  · simp

theorem PrimeValuationRecurringPivotPresentation.pivotPalette_differentialIndependent
    {d : ℕ} {J R A : Fin d → Type u}
    [∀ r, Fintype (J r)] [∀ r, DecidableEq (J r)]
    [∀ r, Fintype (A r)] [∀ r, DecidableEq (A r)]
    [Nonempty (Σ r, J r × A r)]
    (P : PrimeValuationRecurringPivotPresentation d J R) (α : ∀ r, A r → ℂ)
    (hdistinct : ∀ r, Function.Injective (fun a ↦ (α r a).re)) :
    GaloisForLFunctions.DifferentialIndependent finitePrimeRationalCoefficientField
      (P.pivotPalette α) := by
  unfold PrimeValuationRecurringPivotPresentation.pivotPalette
  unfold GaloisForLFunctions.DifferentialIndependent
  simp_rw [differentialJet_primePowerCoefficientShiftCarrier]
  let y : (Σ r, J r × A r) → ℕ → arithmeticFunctionRationalCoordinateField :=
    fun rb k ↦
      algebraMap arithmeticFunctionFractionField arithmeticFunctionRationalCoordinateField
        (algebraMap (ArithmeticFunction ℂ) arithmeticFunctionFractionField
          (primePowerCoefficientShiftedRotatedJet
            rb.1 (P.pivot rb.1 rb.2.1) (α rb.1 rb.2.2) k))
  apply algebraicIndependent_prod_nat_of_fin y
  intro m
  let B : Fin d → Type u := fun r ↦ J r × (A r × Fin (m + 1))
  letI (r : Fin d) : Fintype (B r) := inferInstance
  letI (r : Fin d) : DecidableEq (B r) := inferInstance
  let a : ∀ r, B r → Nat.Primes → ℂ := fun r x p ↦
    P.pivot r x.1 p * primeShiftFactor (α r x.2.1) p *
      ((((r.1 + 1 : ℕ) : ℂ) * rotatedPrimeLogClock p) ^ (x.2.2 : ℕ))
  have hatail : ∀ r, TailCoefficientIndependent (a r) := by
    intro r
    exact P.pivotShiftJetTailIndependent r (A r) (α r) (hdistinct r) m
  have hraw := algebraicIndependent_primePowerSigmaTower_over_finitePrimeCoefficientField
    d B a hatail
  apply algebraicIndependent_constants_over_finitePrimeRationalCoefficientField at hraw
  let f : ((Σ r, J r × A r) × Fin (m + 1)) →
      (Σ r, J r × (A r × Fin (m + 1))) := fun rbk ↦
    ⟨rbk.1.1, (rbk.1.2.1, (rbk.1.2.2, rbk.2))⟩
  have hf : Function.Injective f := by
    rintro ⟨⟨r, j, b⟩, k⟩ ⟨⟨r', j', b'⟩, k'⟩ h
    cases h
    rfl
  have hsub := hraw.comp f hf
  simpa only [Function.comp_apply, B, a, f, y, primePowerSigmaExponent,
    primePowerSigmaCoefficient, primePowerCoefficientShiftedRotatedJet] using! hsub

theorem PrimeValuationRecurringPivotPresentation.complete_relationIdeal
    {d : ℕ} {J R A : Fin d → Type u}
    [∀ r, Fintype (J r)] [∀ r, DecidableEq (J r)]
    [∀ r, Fintype (R r)] [∀ r, DecidableEq (R r)]
    [∀ r, Fintype (A r)] [∀ r, DecidableEq (A r)]
    [Nonempty (Σ r, J r × A r)]
    (P : PrimeValuationRecurringPivotPresentation d J R) (α : ∀ r, A r → ℂ)
    (hdistinct : ∀ r, Function.Injective (fun a ↦ (α r a).re)) :
    GaloisForLFunctions.differentialRelationIdeal
        (C := finitePrimeRationalCoefficientField)
        (Sum.elim (P.pivotPalette α) (P.dependentPalette α)) =
      differentialPivotRelationIdeal P.paletteMatrix (P.baseCorrection α) := by
  apply differentialRelationIdeal_sumElim_eq_pivot
    (P.pivotPalette α) (P.dependentPalette α)
    P.paletteMatrix (P.baseCorrection α)
  · exact P.pivotPalette_differentialIndependent α hdistinct
  · exact P.palette_affineJet α

theorem PrimeValuationRecurringPivotPresentation.differentialBasis
    {d : ℕ} {J R A : Fin d → Type u}
    [∀ r, Fintype (J r)] [∀ r, DecidableEq (J r)]
    [∀ r, Fintype (R r)] [∀ r, DecidableEq (R r)]
    [∀ r, Fintype (A r)] [∀ r, DecidableEq (A r)]
    [Nonempty (Σ r, J r × A r)]
    (P : PrimeValuationRecurringPivotPresentation d J R) (α : ∀ r, A r → ℂ)
    (hdistinct : ∀ r, Function.Injective (fun a ↦ (α r a).re)) :
    GaloisForLFunctions.DifferentialIndependent finitePrimeRationalCoefficientField
        (P.pivotPalette α) ∧
      GaloisForLFunctions.differentialAdjoin finitePrimeRationalCoefficientField
          (Set.range (Sum.elim (P.pivotPalette α) (P.dependentPalette α))) =
        GaloisForLFunctions.differentialAdjoin finitePrimeRationalCoefficientField
          (Set.range (P.pivotPalette α)) := by
  constructor
  · exact P.pivotPalette_differentialIndependent α hdistinct
  · exact differentialAdjoin_sumElim_eq_left_of_affineJets
      (P.pivotPalette α) (P.dependentPalette α)
      P.paletteMatrix (P.baseCorrection α) (P.palette_affineJet α)

/-- A recurrent homogeneous coordinate presentation over a cofinally recurrent prime source
canonically supplies the recurring-pattern pivot data used by the complete relation theorem. -/
def RecurrentHomogeneousValuationPresentation.toRecurringPivotPresentation
    {d : ℕ} {σ : Type u} {J R : Fin d → Type u} [∀ r, Fintype (J r)]
    {x : Nat.Primes → σ → ℂ}
    (P : RecurrentHomogeneousValuationPresentation d σ J R x)
    (hrec : CofinitelyRecurring x) :
    PrimeValuationRecurringPivotPresentation d J R where
  pivot := P.pivotColumn
  dependent := P.dependentColumn
  coefficient := P.coefficient
  pivotShiftJetTailIndependent r _ _ alpha hdistinct m :=
    primePowerCoefficientShiftedRotatedJet_tailIndependent_of_recurringPatternsSpan
      r (P.pivotColumn r) alpha hdistinct (P.pivotColumn_recurringPatternsSpan r) m
  residualFinite := P.residualFinite_of_cofinitelyRecurring hrec

/-- The valuation-tail Hilbert number of a cofinally recurrent source is its recurrent
homogeneous coordinate rank in every degree. -/
theorem valuationTailHilbertFunction_eq_recurrent_of_cofinitelyRecurring
    {P σ : Type*} [Fintype σ]
    (x : P → σ → ℂ) (hrec : CofinitelyRecurring x) (m : ℕ) :
    valuationTailHilbertFunction x m = recurrentHomogeneousHilbertFunction x m := by
  exact (homogeneousTailQuotientEquivRecurringRange_of_cofinitelyRecurring
    x hrec m).finrank_eq

/-- **Cofinal recurrent complete relation theorem.** In every finite valuation window, the
prolonged homogeneous coordinate reductions generate the full differential relation ideal, even
when the recurrent profile geometry is infinite. -/
theorem fullRecurrentHilbert_complete_relationIdeal_of_cofinitelyRecurring
    {d : ℕ} {σ : Type u} [Fintype σ]
    {A : Fin d → Type u}
    [∀ r, Fintype (A r)] [∀ r, DecidableEq (A r)]
    (x : Nat.Primes → σ → ℂ)
    [Nonempty (Σ r : Fin d, fullRecurrentHilbertIndex x (r + 1) × A r)]
    (hrec : CofinitelyRecurring x)
    (α : ∀ r, A r → ℂ)
    (hdistinct : ∀ r, Function.Injective (fun a ↦ (α r a).re)) :
    let P := fullRecurrentHilbertValuationPresentation (d := d) x
    let T := P.toRecurringPivotPresentation hrec
    GaloisForLFunctions.differentialRelationIdeal
        (C := finitePrimeRationalCoefficientField)
        (Sum.elim (T.pivotPalette α) (T.dependentPalette α)) =
      differentialPivotRelationIdeal T.paletteMatrix (T.baseCorrection α) := by
  dsimp only
  exact (fullRecurrentHilbertValuationPresentation (d := d) x
    |>.toRecurringPivotPresentation hrec).complete_relationIdeal α hdistinct

/-- **Cofinal recurrent valuation--Hilbert basis law.** The full homogeneous-coordinate pivots are
a differential transcendence basis of the selected monomial carrier field, and their exact size
is the shift-weighted Hilbert-rank sum. -/
theorem fullRecurrentHilbert_differentialBasis_and_rank_of_cofinitelyRecurring
    {d : ℕ} {σ : Type u} [Fintype σ]
    {A : Fin d → Type u}
    [∀ r, Fintype (A r)] [∀ r, DecidableEq (A r)]
    (x : Nat.Primes → σ → ℂ)
    [Nonempty (Σ r : Fin d, fullRecurrentHilbertIndex x (r + 1) × A r)]
    (hrec : CofinitelyRecurring x)
    (α : ∀ r, A r → ℂ)
    (hdistinct : ∀ r, Function.Injective (fun a ↦ (α r a).re)) :
    let P := fullRecurrentHilbertValuationPresentation (d := d) x
    let T := P.toRecurringPivotPresentation hrec
    GaloisForLFunctions.DifferentialIndependent finitePrimeRationalCoefficientField
        (T.pivotPalette α) ∧
      GaloisForLFunctions.differentialAdjoin finitePrimeRationalCoefficientField
          (Set.range (Sum.elim (T.pivotPalette α) (T.dependentPalette α))) =
        GaloisForLFunctions.differentialAdjoin finitePrimeRationalCoefficientField
          (Set.range (T.pivotPalette α)) ∧
      Fintype.card (Σ r : Fin d, fullRecurrentHilbertIndex x (r + 1) × A r) =
        ∑ r : Fin d,
          recurrentHomogeneousHilbertFunction x (r + 1) * Fintype.card (A r) := by
  dsimp only
  let T := (fullRecurrentHilbertValuationPresentation (d := d) x
    |>.toRecurringPivotPresentation hrec)
  obtain ⟨hind, hadjoin⟩ := T.differentialBasis α hdistinct
  exact ⟨hind, hadjoin, fullRecurrentHilbert_pivotPalette_card x⟩

end

end GaloisForLFunctions.HTGeometry
