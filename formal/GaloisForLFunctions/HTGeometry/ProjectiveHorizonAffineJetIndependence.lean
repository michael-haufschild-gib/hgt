import GaloisForLFunctions.HTGeometry.ProjectiveHorizonChartTranslation
import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.RingTheory.AlgebraicIndependent.Basic

/-!
# Algebraic independence of the affine chart jets

The jets of the affine coordinates of the chart at `i` are rational in the homogeneous jets, with
denominator a power of `X_(i,0)`:

`x_k^(l) = N_(k,l) / X_(i,0)^(l+1)`,   `N_(k,l+1) = (D N_(k,l)) X_(i,0) - (l+1) N_(k,l) X_(i,1)`.

The differential specialization `X_(i,0) ↦ 1`, `X_(i,l+1) ↦ 0`, which fixes every other jet
variable, commutes with the jet shift and therefore sends `N_(k,l)` to `X_(k,l)`.  Because it
inverts the chart substitution after inverting `X_(i,0)`, the affine chart jets are algebraically
independent: differential genericity of the projective source is a theorem about the universal
model rather than an assumption.
-/

namespace GaloisForLFunctions.HTGeometry

open Matrix

noncomputable section

variable {n : Type*} [Fintype n] [DecidableEq n] {K : Type*} [Field K]

/-! ## Numerators of the affine jets -/

/-- Numerator of the `l`-th affine chart jet over the denominator `X_(i,0)^(l+1)`. -/
def affineNumer (i k : n) : ℕ → MvPolynomial (n × ℕ) K
  | 0 => MvPolynomial.X (k, 0)
  | l + 1 =>
      differentialPolynomialDerivation n K (affineNumer i k l) * MvPolynomial.X (i, 0) -
        (l + 1) • (affineNumer i k l * MvPolynomial.X (i, 1))

omit [Fintype n] [DecidableEq n] in
@[simp]
theorem affineNumer_zero (i k : n) :
    affineNumer (K := K) i k 0 = MvPolynomial.X (k, 0) := rfl

omit [Fintype n] [DecidableEq n] in
theorem affineNumer_succ (i k : n) (l : ℕ) :
    affineNumer (K := K) i k (l + 1) =
      differentialPolynomialDerivation n K (affineNumer i k l) * MvPolynomial.X (i, 0) -
        (l + 1) • (affineNumer i k l * MvPolynomial.X (i, 1)) := rfl

/-- The affine chart jets are the numerators over powers of the chart denominator. -/
theorem affineJet_eq_div (i k : n) (l : ℕ) :
    affineJet (K := K) i k l =
      algebraMap (MvPolynomial (n × ℕ) K) (HomogeneousJetField n K) (affineNumer i k l) /
        freeCoordinate K (n × ℕ) (i, 0) ^ (l + 1) := by
  have hi : freeCoordinate K (n × ℕ) (i, 0) ≠ (0 : HomogeneousJetField n K) :=
    freeCoordinate_ne_zero i 0
  induction l with
  | zero =>
      rw [affineJet_zero, affineCoord, affineNumer_zero, pow_one]
      rfl
  | succ l ih =>
      set x : HomogeneousJetField n K := freeCoordinate K (n × ℕ) (i, 0) with hxdef
      set x1 : HomogeneousJetField n K := freeCoordinate K (n × ℕ) (i, 1) with hx1def
      set A : HomogeneousJetField n K :=
        algebraMap (MvPolynomial (n × ℕ) K) (HomogeneousJetField n K)
          (affineNumer i k l) with hAdef
      set A' : HomogeneousJetField n K :=
        algebraMap (MvPolynomial (n × ℕ) K) (HomogeneousJetField n K)
          (differentialPolynomialDerivation n K (affineNumer i k l)) with hA'def
      have hD : homogeneousJetShift n K (x ^ (l + 1)) =
          ((l : ℕ) + 1) • (x ^ l * x1) := by
        rw [hxdef, hx1def, Derivation.leibniz_pow, homogeneousJetShift_freeCoordinate]
        simp [smul_eq_mul, mul_comm]
      have hcancel : (x ^ (l + 1))⁻¹ ^ 2 * x ^ l * x ^ (l + 2) = 1 := by
        rw [inv_pow, ← pow_mul, mul_assoc, ← pow_add,
          mul_comm ((x ^ ((l + 1) * 2))⁻¹) (x ^ (l + (l + 2))),
          show l + (l + 2) = (l + 1) * 2 by ring]
        exact mul_inv_cancel₀ (pow_ne_zero _ hi)
      rw [affineJet_succ, ih, affineNumer_succ, Derivation.leibniz_div, hD,
        homogeneousJetShift_algebraMap, map_sub, map_mul, map_nsmul, map_mul,
        ← hAdef, ← hA'def]
      show (x ^ (l + 1))⁻¹ ^ 2 • (x ^ (l + 1) • A' - A • (((l : ℕ) + 1) • (x ^ l * x1))) =
        (A' * x - ((l : ℕ) + 1) • (A * x1)) / x ^ (l + 1 + 1)
      simp only [smul_eq_mul, nsmul_eq_mul, Nat.cast_add, Nat.cast_one]
      rw [eq_div_iff (pow_ne_zero (l + 1 + 1) hi)]
      have hfac : x ^ (l + 1) * A' - A * (((l : HomogeneousJetField n K) + 1) * (x ^ l * x1)) =
          x ^ l * (A' * x - ((l : HomogeneousJetField n K) + 1) * (A * x1)) := by ring
      calc (x ^ (l + 1))⁻¹ ^ 2 * (x ^ (l + 1) * A' - A * (((l : HomogeneousJetField n K) + 1) * (x ^ l * x1))) *
            x ^ (l + 1 + 1)
          = ((x ^ (l + 1))⁻¹ ^ 2 * x ^ l * x ^ (l + 2)) *
              (A' * x - ((l : HomogeneousJetField n K) + 1) * (A * x1)) := by
            rw [hfac]; ring
        _ = A' * x - ((l : HomogeneousJetField n K) + 1) * (A * x1) := by rw [hcancel, one_mul]

/-! ## The chart specialization -/

/-- The differential specialization `X_(i,0) ↦ 1`, `X_(i,l+1) ↦ 0`, fixing every other jet
variable. -/
def chartSpec (i : n) : MvPolynomial (n × ℕ) K →ₐ[K] MvPolynomial (n × ℕ) K :=
  MvPolynomial.aeval fun p : n × ℕ =>
    if p.1 = i then (if p.2 = 0 then 1 else 0) else MvPolynomial.X p

omit [Fintype n] in
@[simp]
theorem chartSpec_X_of_ne {i k : n} (hk : k ≠ i) (l : ℕ) :
    chartSpec (K := K) i (MvPolynomial.X (k, l)) = MvPolynomial.X (k, l) := by
  simp [chartSpec, hk]

omit [Fintype n] in
@[simp]
theorem chartSpec_X_self_zero (i : n) :
    chartSpec (K := K) i (MvPolynomial.X (i, 0)) = 1 := by
  simp [chartSpec]

omit [Fintype n] in
@[simp]
theorem chartSpec_X_self_succ (i : n) (l : ℕ) :
    chartSpec (K := K) i (MvPolynomial.X (i, l + 1)) = 0 := by
  simp [chartSpec]

omit [Fintype n] in
/-- The specialization commutes with the total-derivative jet shift. -/
theorem chartSpec_deriv (i : n) (p : MvPolynomial (n × ℕ) K) :
    chartSpec i (differentialPolynomialDerivation n K p) =
      differentialPolynomialDerivation n K (chartSpec i p) := by
  have hX : ∀ (k : n) (l : ℕ),
      chartSpec (K := K) i (differentialPolynomialDerivation n K (MvPolynomial.X (k, l))) =
        differentialPolynomialDerivation n K (chartSpec i (MvPolynomial.X (k, l))) := by
    intro k l
    rw [differentialPolynomialDerivation_X]
    rcases eq_or_ne k i with rfl | hk
    · cases l with
      | zero =>
          rw [chartSpec_X_self_succ, chartSpec_X_self_zero, Derivation.map_one_eq_zero]
      | succ l => rw [chartSpec_X_self_succ, chartSpec_X_self_succ, map_zero]
    · rw [chartSpec_X_of_ne hk, chartSpec_X_of_ne hk, differentialPolynomialDerivation_X]
  induction p using MvPolynomial.induction_on with
  | C a =>
      have hCa : differentialPolynomialDerivation n K (MvPolynomial.C a) = 0 := by
        rw [← MvPolynomial.algebraMap_eq]
        exact Derivation.map_algebraMap _ a
      have hspec : chartSpec (K := K) i (MvPolynomial.C a) = MvPolynomial.C a := by
        rw [← MvPolynomial.algebraMap_eq]
        exact (chartSpec i).commutes a
      rw [hCa, map_zero, hspec, hCa]
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p j hp =>
      obtain ⟨k, l⟩ := j
      have hL : chartSpec (K := K) i (differentialPolynomialDerivation n K
            (p * MvPolynomial.X (k, l))) =
          chartSpec i p *
              chartSpec i (differentialPolynomialDerivation n K (MvPolynomial.X (k, l))) +
            chartSpec i (MvPolynomial.X (k, l)) *
              chartSpec i (differentialPolynomialDerivation n K p) := by
        rw [Derivation.leibniz]
        simp [smul_eq_mul]
      have hR : differentialPolynomialDerivation n K
            (chartSpec (K := K) i (p * MvPolynomial.X (k, l))) =
          chartSpec i p *
              differentialPolynomialDerivation n K (chartSpec i (MvPolynomial.X (k, l))) +
            chartSpec i (MvPolynomial.X (k, l)) *
              differentialPolynomialDerivation n K (chartSpec i p) := by
        rw [map_mul, Derivation.leibniz]
        simp [smul_eq_mul]
      rw [hL, hR, hp, hX]

omit [Fintype n] in
/-- The specialization inverts the chart substitution on numerators. -/
theorem chartSpec_affineNumer {i k : n} (hk : k ≠ i) (l : ℕ) :
    chartSpec (K := K) i (affineNumer i k l) = MvPolynomial.X (k, l) := by
  induction l with
  | zero => rw [affineNumer_zero, chartSpec_X_of_ne hk]
  | succ l ih =>
      rw [affineNumer_succ, map_sub, map_mul, map_nsmul, map_mul, chartSpec_X_self_zero,
        chartSpec_X_self_succ, chartSpec_deriv, ih, mul_one, mul_zero, smul_zero, sub_zero,
        differentialPolynomialDerivation_X]

/-! ## The chart localization -/

/-- The chart denominator, inverted to reach the affine chart. -/
abbrev chartDenom (i : n) (K : Type*) [Field K] : MvPolynomial (n × ℕ) K :=
  MvPolynomial.X (i, 0)

omit [Fintype n] [DecidableEq n] in
theorem chartDenom_ne_zero (i : n) : chartDenom i K ≠ 0 :=
  MvPolynomial.X_ne_zero _

/-- The homogeneous jet polynomial ring with the chart denominator inverted. -/
abbrev ChartLoc (i : n) (K : Type*) [Field K] := Localization.Away (chartDenom i K)

omit [Fintype n] [DecidableEq n] in
theorem isUnit_toField_powers (i : n) :
    ∀ y : Submonoid.powers (chartDenom i K),
      IsUnit (algebraMap (MvPolynomial (n × ℕ) K) (HomogeneousJetField n K)
        (y : MvPolynomial (n × ℕ) K)) := by
  rintro ⟨_, m, rfl⟩
  rw [map_pow]
  exact ((freeCoordinate_ne_zero (K := K) i 0).isUnit).pow m

omit [Fintype n] in
theorem isUnit_spec_powers (i : n) :
    ∀ y : Submonoid.powers (chartDenom i K),
      IsUnit (chartSpec (K := K) i (y : MvPolynomial (n × ℕ) K)) := by
  rintro ⟨_, m, rfl⟩
  rw [map_pow, chartDenom, chartSpec_X_self_zero, one_pow]
  exact isUnit_one

/-- The chart localization inside the homogeneous jet field. -/
def chartLocToField (i : n) : ChartLoc i K →ₐ[K] HomogeneousJetField n K :=
  { IsLocalization.lift (isUnit_toField_powers i) with
    commutes' := fun c => by
      show IsLocalization.lift (isUnit_toField_powers i) (algebraMap K (ChartLoc i K) c) = _
      rw [IsScalarTower.algebraMap_apply K (MvPolynomial (n × ℕ) K) (ChartLoc i K),
        IsLocalization.lift_eq]
      exact (IsScalarTower.algebraMap_apply K (MvPolynomial (n × ℕ) K)
        (HomogeneousJetField n K) c).symm }

/-- The chart specialization extended to the chart localization. -/
def chartLocSpec (i : n) : ChartLoc i K →ₐ[K] MvPolynomial (n × ℕ) K :=
  { IsLocalization.lift (isUnit_spec_powers i) with
    commutes' := fun c => by
      show IsLocalization.lift (isUnit_spec_powers i) (algebraMap K (ChartLoc i K) c) = _
      rw [IsScalarTower.algebraMap_apply K (MvPolynomial (n × ℕ) K) (ChartLoc i K),
        IsLocalization.lift_eq]
      exact (chartSpec i).commutes c }

theorem chartLocToField_algebraMap (i : n) (p : MvPolynomial (n × ℕ) K) :
    chartLocToField i (algebraMap (MvPolynomial (n × ℕ) K) (ChartLoc i K) p) =
      algebraMap (MvPolynomial (n × ℕ) K) (HomogeneousJetField n K) p :=
  IsLocalization.lift_eq (isUnit_toField_powers i) p

theorem chartLocSpec_algebraMap (i : n) (p : MvPolynomial (n × ℕ) K) :
    chartLocSpec i (algebraMap (MvPolynomial (n × ℕ) K) (ChartLoc i K) p) = chartSpec i p :=
  IsLocalization.lift_eq (isUnit_spec_powers i) p

theorem chartLocToField_invSelf (i : n) :
    chartLocToField i (IsLocalization.Away.invSelf (S := ChartLoc i K) (chartDenom i K)) =
      (freeCoordinate K (n × ℕ) (i, 0))⁻¹ := by
  have hmul := IsLocalization.Away.mul_invSelf (S := ChartLoc i K) (chartDenom i K)
  have hkey := congrArg (chartLocToField (K := K) i) hmul
  rw [map_mul, chartLocToField_algebraMap, map_one] at hkey
  exact eq_inv_of_mul_eq_one_right hkey

theorem chartLocSpec_invSelf (i : n) :
    chartLocSpec i (IsLocalization.Away.invSelf (S := ChartLoc i K) (chartDenom i K)) = 1 := by
  have hmul := IsLocalization.Away.mul_invSelf (S := ChartLoc i K) (chartDenom i K)
  have := congrArg (chartLocSpec (K := K) i) hmul
  rw [map_mul, chartLocSpec_algebraMap, map_one, chartSpec_X_self_zero, one_mul] at this
  exact this

/-- The affine chart jet, realised inside the chart localization. -/
def chartJetLoc (i k : n) (l : ℕ) : ChartLoc i K :=
  algebraMap (MvPolynomial (n × ℕ) K) (ChartLoc i K) (affineNumer i k l) *
    (IsLocalization.Away.invSelf (S := ChartLoc i K) (chartDenom i K)) ^ (l + 1)

theorem chartLocToField_chartJetLoc (i k : n) (l : ℕ) :
    chartLocToField i (chartJetLoc (K := K) i k l) = affineJet i k l := by
  rw [chartJetLoc, map_mul, map_pow, chartLocToField_algebraMap, chartLocToField_invSelf,
    affineJet_eq_div, div_eq_mul_inv, inv_pow]

theorem chartLocSpec_chartJetLoc {i k : n} (hk : k ≠ i) (l : ℕ) :
    chartLocSpec i (chartJetLoc (K := K) i k l) = MvPolynomial.X (k, l) := by
  rw [chartJetLoc, map_mul, map_pow, chartLocSpec_algebraMap, chartLocSpec_invSelf, one_pow,
    mul_one, chartSpec_affineNumer hk]

theorem chartLocToField_injective (i : n) :
    Function.Injective (chartLocToField (K := K) i) := by
  have hmem : Submonoid.powers (chartDenom i K) ≤
      nonZeroDivisors (MvPolynomial (n × ℕ) K) := by
    rw [Submonoid.powers_le]
    exact mem_nonZeroDivisors_of_ne_zero (chartDenom_ne_zero i)
  have hloc : Function.Injective
      (algebraMap (MvPolynomial (n × ℕ) K) (ChartLoc i K)) :=
    IsLocalization.injective (ChartLoc i K) hmem
  have hfrac : Function.Injective
      (algebraMap (MvPolynomial (n × ℕ) K) (HomogeneousJetField n K)) :=
    IsFractionRing.injective (MvPolynomial (n × ℕ) K) (HomogeneousJetField n K)
  show Function.Injective (IsLocalization.lift (isUnit_toField_powers (K := K) i))
  rw [IsLocalization.lift_injective_iff]
  intro x y
  exact ⟨fun h => congrArg _ (hloc h), fun h => congrArg _ (hfrac h)⟩

/-! ## Independence -/

/-- **Algebraic independence of the affine chart jets.**  All jets of all affine coordinates of one
chart are algebraically independent over the constants, so the projective jet field of a chart is a
free jet field.  This is differential genericity, proved for the universal model. -/
theorem algebraicIndependent_affineJet (i : n) :
    AlgebraicIndependent K
      (fun p : {k : n // k ≠ i} × ℕ => affineJet (K := K) i p.1.1 p.2) := by
  have hinj : Function.Injective (fun p : {k : n // k ≠ i} × ℕ => ((p.1.1, p.2) : n × ℕ)) := by
    rintro ⟨⟨a, ha⟩, l⟩ ⟨⟨b, hb⟩, m⟩ h
    simp only [Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    rfl
  have hX : AlgebraicIndependent K
      (fun p : {k : n // k ≠ i} × ℕ =>
        (MvPolynomial.X (p.1.1, p.2) : MvPolynomial (n × ℕ) K)) :=
    (MvPolynomial.algebraicIndependent_X (n × ℕ) K).comp _ hinj
  have hcomp : (fun p : {k : n // k ≠ i} × ℕ =>
      chartLocSpec (K := K) i (chartJetLoc i p.1.1 p.2)) =
      fun p : {k : n // k ≠ i} × ℕ =>
        (MvPolynomial.X (p.1.1, p.2) : MvPolynomial (n × ℕ) K) := by
    funext p
    exact chartLocSpec_chartJetLoc p.1.2 p.2
  have hloc : AlgebraicIndependent K
      (fun p : {k : n // k ≠ i} × ℕ => chartJetLoc (K := K) i p.1.1 p.2) := by
    refine AlgebraicIndependent.of_comp (chartLocSpec (K := K) i) ?_
    rw [Function.comp_def, hcomp]
    exact hX
  have hmap := hloc.map (f := chartLocToField (K := K) i)
    ((chartLocToField_injective i).injOn)
  have hfun : (fun p : {k : n // k ≠ i} × ℕ =>
      chartLocToField (K := K) i (chartJetLoc i p.1.1 p.2)) =
      fun p : {k : n // k ≠ i} × ℕ => affineJet (K := K) i p.1.1 p.2 := by
    funext p
    exact chartLocToField_chartJetLoc i p.1.1 p.2
  rw [Function.comp_def, hfun] at hmap
  exact hmap

end

end GaloisForLFunctions.HTGeometry
