import GaloisForLFunctions.RHTower.FieldOneFiniteStageSoninSigma
import GaloisForLFunctions.RHTower.FieldOnePositiveUnitsHaarNormalization
import GaloisForLFunctions.RHTower.CCMArchimedeanGeometricScaledKernel

/-!
# Literal finite-stage CCM theta equation

This file rewrites the finite Boolean support of the literal semilocal Sonin
vector as the Euler product in Connes--Consani--Moscovici equation (4.23).
The signed/full-lattice normalization remains explicit throughout.
-/

namespace GaloisForLFunctions.RHTower

noncomputable section

open MeasureTheory Set TopologicalSpace IsDedekindDomain
open _root_.RHTower
open scoped BigOperators NNReal

/-! ## Boolean cube as subsets of finite places -/

/-- Exponent vector associated to a subset of the selected finite places. -/
def fieldOneSoninExponentOfSubset
    {S : Finset (HeightOneSpectrum ℤ)} (A : Finset ↥S) (v : ↥S) : ℤ := by
  classical
  exact if v ∈ A then -1 else 0

@[simp] theorem fieldOneSoninExponentOfSubset_eq_negOne_iff
    {S : Finset (HeightOneSpectrum ℤ)} (A : Finset ↥S) (v : ↥S) :
    fieldOneSoninExponentOfSubset A v = -1 ↔ v ∈ A := by
  classical
  simp [fieldOneSoninExponentOfSubset]

theorem fieldOneSoninExponentOfSubset_injective
    (S : Finset (HeightOneSpectrum ℤ)) :
    Function.Injective
      (fieldOneSoninExponentOfSubset (S := S)) := by
  intro A B h
  ext v
  rw [← fieldOneSoninExponentOfSubset_eq_negOne_iff A v,
    ← fieldOneSoninExponentOfSubset_eq_negOne_iff B v,
    congrFun h v]

/-- The Boolean exponent cube is canonically the powerset of the finite
place set. -/
theorem fieldOneFiniteStageSoninExponentCube_eq_powerset_image
    (S : Finset (HeightOneSpectrum ℤ)) :
    fieldOneFiniteStageSoninExponentCube S =
      (Finset.univ.powerset : Finset (Finset ↥S)).image
        (fieldOneSoninExponentOfSubset (S := S)) := by
  classical
  ext n
  rw [fieldOneFiniteStageSoninExponent_mem_cube_iff, Finset.mem_image]
  constructor
  · intro hn
    let A : Finset ↥S := Finset.univ.filter (fun v => n v = -1)
    refine ⟨A, Finset.mem_powerset.2 (Finset.subset_univ A), ?_⟩
    funext v
    rcases hn v with hv | hv
    · simp [A, fieldOneSoninExponentOfSubset, hv]
    · simp [A, fieldOneSoninExponentOfSubset, hv]
  · rintro ⟨A, hA, rfl⟩ v
    by_cases hv : v ∈ A
    · exact Or.inr (by simp [fieldOneSoninExponentOfSubset, hv])
    · exact Or.inl (by simp [fieldOneSoninExponentOfSubset, hv])

/-- Rational dilation scale attached to a subset of finite places. -/
def fieldOneFiniteStageSoninSubsetRationalScale
    {S : Finset (HeightOneSpectrum ℤ)} (A : Finset ↥S) : ℚˣ :=
  ∏ v ∈ A, (fieldOneRationalPrimeUnit v.1)⁻¹

/-- Complex Euler coefficient attached to a subset of finite places. -/
def fieldOneFiniteStageSoninSubsetCoefficient
    {S : Finset (HeightOneSpectrum ℤ)} (A : Finset ↥S) : ℂ :=
  ∏ v ∈ A, -((Rat.HeightOneSpectrum.primesEquiv v.1 : ℂ)⁻¹)

theorem fieldOneSUnitProduct_soninExponentOfSubset
    (S : Finset (HeightOneSpectrum ℤ)) (A : Finset ↥S) :
    fieldOneSUnitProduct S (fieldOneSoninExponentOfSubset A) =
      fieldOneFiniteStageSoninSubsetRationalScale A := by
  classical
  unfold fieldOneSUnitProduct
  unfold fieldOneFiniteStageSoninSubsetRationalScale
  calc
    (∏ v : ↥S, fieldOneRationalPrimeUnit v.1 ^
        fieldOneSoninExponentOfSubset A v) =
        ∏ v ∈ A, fieldOneRationalPrimeUnit v.1 ^
          fieldOneSoninExponentOfSubset A v := by
      symm
      apply Finset.prod_subset (Finset.subset_univ A)
      intro v hvuniv hvA
      simp [fieldOneSoninExponentOfSubset, hvA]
    _ = ∏ v ∈ A, (fieldOneRationalPrimeUnit v.1)⁻¹ := by
      apply Finset.prod_congr rfl
      intro v hvA
      simp [fieldOneSoninExponentOfSubset, hvA]

theorem fieldOneFiniteStageSoninExponentCoefficient_subset
    (S : Finset (HeightOneSpectrum ℤ)) (A : Finset ↥S) :
    fieldOneFiniteStageSoninExponentCoefficient S
        (fieldOneSoninExponentOfSubset A) =
      fieldOneFiniteStageSoninSubsetCoefficient A := by
  classical
  unfold fieldOneFiniteStageSoninExponentCoefficient
  unfold fieldOneFiniteStageSoninSubsetCoefficient
  calc
    (∏ v : ↥S, if fieldOneSoninExponentOfSubset A v = 0 then 1
      else if fieldOneSoninExponentOfSubset A v = -1 then
        -((Rat.HeightOneSpectrum.primesEquiv v.1 : ℂ)⁻¹) else 0) =
        ∏ v ∈ A, (if fieldOneSoninExponentOfSubset A v = 0 then 1
          else if fieldOneSoninExponentOfSubset A v = -1 then
            -((Rat.HeightOneSpectrum.primesEquiv v.1 : ℂ)⁻¹) else 0) := by
      symm
      apply Finset.prod_subset (Finset.subset_univ A)
      intro v hvuniv hvA
      simp [fieldOneSoninExponentOfSubset, hvA]
    _ = ∏ v ∈ A,
        -((Rat.HeightOneSpectrum.primesEquiv v.1 : ℂ)⁻¹) := by
      apply Finset.prod_congr rfl
      intro v hvA
      simp [fieldOneSoninExponentOfSubset, hvA]

/-- Fully expanded finite Euler product value. -/
def fieldOneFiniteStageThetaSubsetEulerValue
    (S : Finset (HeightOneSpectrum ℤ))
    (f : SchwartzMap ℝ ℂ) (x : ℝ) : ℂ :=
  ∑ A ∈ (Finset.univ.powerset : Finset (Finset ↥S)),
    f (x *
        (((fieldOneFiniteStageSoninSubsetRationalScale A : ℚˣ) : ℚ) : ℝ)) *
      fieldOneFiniteStageSoninSubsetCoefficient A

/-- The orbit-selected Boolean cube is exactly the subset expansion of the
finite Euler product. -/
theorem fieldOneFiniteStageThetaPositiveEulerValue_eq_subset
    (S : Finset (HeightOneSpectrum ℤ))
    (f : SchwartzMap ℝ ℂ) (x : ℝ) :
    fieldOneFiniteStageThetaPositiveEulerValue S f x =
      fieldOneFiniteStageThetaSubsetEulerValue S f x := by
  classical
  unfold fieldOneFiniteStageThetaPositiveEulerValue
  unfold fieldOneFiniteStageThetaSubsetEulerValue
  rw [fieldOneFiniteStageSoninExponentCube_eq_powerset_image,
    Finset.sum_image]
  · apply Finset.sum_congr rfl
    intro A hA
    rw [fieldOneSUnitProduct_soninExponentOfSubset,
      fieldOneFiniteStageSoninExponentCoefficient_subset]
  · intro A hA B hB h
    exact fieldOneSoninExponentOfSubset_injective S h

/-! ## Literal Euler operator on the dense even-Schwartz source -/

/-- One local CCM Euler factor on Schwartz space, normalized so that its
`L²` image is exactly `1 - p⁻¹ᐟ² Uₚ⁻¹`. -/
def fieldOneFiniteStageThetaSchwartzTerm
    (S : Finset (HeightOneSpectrum ℤ)) (v : ↥S)
    (g : SchwartzMap ℝ ℂ) : SchwartzMap ℝ ℂ :=
  g - ((Real.sqrt (fieldOneFinitePlacePrime v.1 : ℝ) : ℂ)⁻¹) •
    RHTower.ccmNormalizedSchwartzDilation
      (fieldOneFinitePlacePrime v.1 : ℝ)⁻¹
      (inv_pos.mpr (zero_lt_one.trans
        (fieldOneFinitePlacePrime_real_gt_one v.1))) g

/-- The Schwartz local factor is literally the bounded CCM Euler factor on
the dense even-Schwartz source. -/
theorem fieldOneFiniteStageThetaSchwartzTerm_source
    (S : Finset (HeightOneSpectrum ℤ)) (v : ↥S)
    (g : SchwartzMap ℝ ℂ) :
    RHTower.ccmEvenSchwartzSource
        (fieldOneFiniteStageThetaSchwartzTerm S v g) =
      fieldOneFiniteStageThetaEulerTerm S v
        (RHTower.ccmEvenSchwartzSource g) := by
  change RHTower.ccmEvenSchwartzSourceCLM
    (fieldOneFiniteStageThetaSchwartzTerm S v g) = _
  rw [fieldOneFiniteStageThetaSchwartzTerm, map_sub, map_smul,
    RHTower.ccmEvenSchwartzSourceCLM_apply,
    RHTower.ccmEvenSchwartzSourceCLM_apply,
    RHTower.ccmEvenSchwartzSource_normalizedDilation]
  rfl

/-- Pointwise form of one local factor: `g(x) - p⁻¹g(x/p)`. -/
theorem fieldOneFiniteStageThetaSchwartzTerm_apply
    (S : Finset (HeightOneSpectrum ℤ)) (v : ↥S)
    (g : SchwartzMap ℝ ℂ) (x : ℝ) :
    fieldOneFiniteStageThetaSchwartzTerm S v g x =
      g x - ((fieldOneFinitePlacePrime v.1 : ℝ) : ℂ)⁻¹ *
        g ((fieldOneFinitePlacePrime v.1 : ℝ)⁻¹ * x) := by
  let p : ℝ := fieldOneFinitePlacePrime v.1
  have hp : 0 < p := zero_lt_one.trans
    (fieldOneFinitePlacePrime_real_gt_one v.1)
  have hsqrt : Real.sqrt p * Real.sqrt p = p :=
    Real.mul_self_sqrt hp.le
  change g x - (Real.sqrt p : ℂ)⁻¹ *
      ((Real.sqrt p⁻¹ : ℂ) * g (p⁻¹ * x)) =
    g x - (p : ℂ)⁻¹ * g (p⁻¹ * x)
  have hsqrt_inv : Real.sqrt p⁻¹ = (Real.sqrt p)⁻¹ := by
    rw [Real.sqrt_inv]
  rw [hsqrt_inv]
  congr 1
  rw [← mul_assoc]
  congr 1
  norm_cast
  rw [← mul_inv, hsqrt]

/-- Ordered iteration of local Schwartz Euler factors.  The order is the
same order used by the literal bounded-operator product. -/
def fieldOneFiniteStageThetaSchwartzIterate
    (S : Finset (HeightOneSpectrum ℤ)) :
    List ↥S → SchwartzMap ℝ ℂ → SchwartzMap ℝ ℂ
  | [], g => g
  | v :: L, g => fieldOneFiniteStageThetaSchwartzTerm S v
      (fieldOneFiniteStageThetaSchwartzIterate S L g)

/-- Every ordered finite Schwartz iteration intertwines with the matching
ordered product of bounded CCM Euler factors. -/
theorem fieldOneFiniteStageThetaSchwartzIterate_source
    (S : Finset (HeightOneSpectrum ℤ)) (L : List ↥S)
    (g : SchwartzMap ℝ ℂ) :
    RHTower.ccmEvenSchwartzSource
        (fieldOneFiniteStageThetaSchwartzIterate S L g) =
      (L.map (fieldOneFiniteStageThetaEulerTerm S)).prod
        (RHTower.ccmEvenSchwartzSource g) := by
  induction L with
  | nil => rfl
  | cons v L ih =>
      rw [fieldOneFiniteStageThetaSchwartzIterate,
        fieldOneFiniteStageThetaSchwartzTerm_source, ih]
      rfl

/-- The concrete finite Euler operator is the closure of the literal
finite Schwartz iteration on the dense source. -/
theorem fieldOneFiniteStageThetaEulerOperator_source
    (S : Finset (HeightOneSpectrum ℤ)) (g : SchwartzMap ℝ ℂ) :
    fieldOneFiniteStageThetaEulerOperator S
        (RHTower.ccmEvenSchwartzSource g) =
      RHTower.ccmEvenSchwartzSource
        (fieldOneFiniteStageThetaSchwartzIterate S S.attach.toList g) := by
  rw [fieldOneFiniteStageThetaSchwartzIterate_source]
  rfl

/-! ## Exact arithmetic of subset insertion -/

theorem fieldOneFiniteStageSoninSubsetRationalScale_cons
    {S : Finset (HeightOneSpectrum ℤ)} (v : ↥S) (A : Finset ↥S)
    (hv : v ∉ A) :
    fieldOneFiniteStageSoninSubsetRationalScale (A.cons v hv) =
      (fieldOneRationalPrimeUnit v.1)⁻¹ *
        fieldOneFiniteStageSoninSubsetRationalScale A := by
  simpa [fieldOneFiniteStageSoninSubsetRationalScale, mul_comm]

theorem fieldOneFiniteStageSoninSubsetCoefficient_cons
    {S : Finset (HeightOneSpectrum ℤ)} (v : ↥S) (A : Finset ↥S)
    (hv : v ∉ A) :
    fieldOneFiniteStageSoninSubsetCoefficient (A.cons v hv) =
      -((Rat.HeightOneSpectrum.primesEquiv v.1 : ℂ)⁻¹) *
        fieldOneFiniteStageSoninSubsetCoefficient A := by
  simp [fieldOneFiniteStageSoninSubsetCoefficient]

theorem fieldOneFinitePlacePrime_real_eq_rationalPrimeUnit
    {S : Finset (HeightOneSpectrum ℤ)} (v : ↥S) :
    (fieldOneFinitePlacePrime v.1 : ℝ) =
      (((fieldOneRationalPrimeUnit v.1 : ℚˣ) : ℚ) : ℝ) := by
  rfl

theorem fieldOneFinitePlacePrime_complex_eq_primesEquiv
    {S : Finset (HeightOneSpectrum ℤ)} (v : ↥S) :
    ((fieldOneFinitePlacePrime v.1 : ℝ) : ℂ) =
      (Rat.HeightOneSpectrum.primesEquiv v.1 : ℂ) := by
  rfl

/-- One summand of the literal subset Euler expansion. -/
def fieldOneFiniteStageThetaSubsetEulerTerm
    {S : Finset (HeightOneSpectrum ℤ)} (A : Finset ↥S)
    (g : SchwartzMap ℝ ℂ) (x : ℝ) : ℂ :=
  g (x * (((fieldOneFiniteStageSoninSubsetRationalScale A : ℚˣ) : ℚ) : ℝ)) *
    fieldOneFiniteStageSoninSubsetCoefficient A

/-- Inserting a new finite place into a subset multiplies its term by
`-p⁻¹` and evaluates the old term at `x/p`. -/
theorem fieldOneFiniteStageThetaSubsetEulerTerm_cons
    {S : Finset (HeightOneSpectrum ℤ)} (v : ↥S) (A : Finset ↥S)
    (hv : v ∉ A) (g : SchwartzMap ℝ ℂ) (x : ℝ) :
    fieldOneFiniteStageThetaSubsetEulerTerm (A.cons v hv) g x =
      -((fieldOneFinitePlacePrime v.1 : ℝ) : ℂ)⁻¹ *
        fieldOneFiniteStageThetaSubsetEulerTerm A g
          ((fieldOneFinitePlacePrime v.1 : ℝ)⁻¹ * x) := by
  rw [fieldOneFiniteStageThetaSubsetEulerTerm,
    fieldOneFiniteStageThetaSubsetEulerTerm,
    fieldOneFiniteStageSoninSubsetRationalScale_cons v A hv,
    fieldOneFiniteStageSoninSubsetCoefficient_cons v A hv]
  rw [← fieldOneFinitePlacePrime_complex_eq_primesEquiv v]
  have harg :
      x * (((((fieldOneRationalPrimeUnit v.1)⁻¹ *
          fieldOneFiniteStageSoninSubsetRationalScale A : ℚˣ) : ℚ) : ℝ)) =
        (fieldOneFinitePlacePrime v.1 : ℝ)⁻¹ * x *
          (((fieldOneFiniteStageSoninSubsetRationalScale A : ℚˣ) : ℚ) : ℝ) := by
    rw [Units.val_mul, Units.val_inv_eq_inv_val,
      Rat.cast_mul, Rat.cast_inv]
    rw [← fieldOneFinitePlacePrime_real_eq_rationalPrimeUnit v]
    ring
  rw [harg]
  ring

end

end GaloisForLFunctions.RHTower
