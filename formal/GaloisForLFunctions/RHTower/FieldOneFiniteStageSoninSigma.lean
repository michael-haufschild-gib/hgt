import GaloisForLFunctions.RHTower.FieldOnePadicSoninSigma
import GaloisForLFunctions.RHTower.FieldOnePadicSoninL2
import GaloisForLFunctions.RHTower.FieldOnePadicProductBruhatFourierSelfMap
import GaloisForLFunctions.RHTower.FieldOneFiniteStageFiniteFourierSelfMap
import GaloisForLFunctions.RHTower.FieldOneFiniteStageClassFourier
import GaloisForLFunctions.RHTower.FieldOneFiniteStageSUnitCoordinates
import Mathlib.MeasureTheory.Integral.Pi

/-!
# The finite-stage CCM Sonin vector

For a finite set `S` of rational places, this file constructs the literal
finite tensor product

`σ_S(x) = ∏_{v∈S} σ_{p_v}(x_v)`

as a compactly supported locally constant function.  Compact support is
proved in the full dependent product, including the empty stage.  Finite
Fubini and the exact local Fourier identity then prove `F_S σ_S = σ_S`.
No factorization, nonvanishing, or spectral hypothesis is assumed.
-/

namespace GaloisForLFunctions.RHTower

noncomputable section

open MeasureTheory Set TopologicalSpace IsDedekindDomain
open _root_.RHTower
open scoped BigOperators TensorProduct FourierTransform NNReal

variable {ι : Type*} [Fintype ι]
variable (p : ι → ℕ) [∀ i, Fact (p i).Prime]

/-- Exact two-shell value of `σ_p` in valuation--unit coordinates. -/
@[simp] theorem fieldOnePadicSoninSigma_apply_forward
    (q : ℕ) [Fact q.Prime] (k : ℤ) (u : ℤ_[q]ˣ) :
    (fieldOnePadicSoninSigma q).1
        ((fieldOnePadicValuationUnitForward q
          (Multiplicative.ofAdd k, u) : ℚ_[q]ˣ) : ℚ_[q]) =
      if k = 0 then 1 else if k = -1 then -(q : ℂ)⁻¹ else 0 := by
  simp only [fieldOnePadicSoninSigma, fieldOnePadicSoninShell]
  change ((fieldOnePadicSoninShell q 0).1 _ -
      (q : ℂ)⁻¹ * (fieldOnePadicSoninShell q 1).1 _) = _
  rw [fieldOnePadicSoninShell_apply_forward,
    fieldOnePadicSoninShell_apply_forward]
  by_cases hk0 : k = 0
  · simp [hk0]
  · by_cases hk1 : k = -1
    · simp [hk1]
    · simp [hk0, hk1]

/-- Coordinate-free value classification on nonzero p-adic elements, with
nonzeroness encoded by the unit type. -/
theorem fieldOnePadicSoninSigma_apply_unit
    (q : ℕ) [Fact q.Prime] (x : ℚ_[q]ˣ) :
    (fieldOnePadicSoninSigma q).1 (x : ℚ_[q]) =
      if Padic.valuation (x : ℚ_[q]) = 0 then 1
      else if Padic.valuation (x : ℚ_[q]) = -1 then -(q : ℂ)⁻¹ else 0 := by
  let z := (fieldOnePadicValuationUnitContinuousMulEquiv q).symm x
  let k : ℤ := z.1.toAdd
  let u : ℤ_[q]ˣ := z.2
  have hz : z = (Multiplicative.ofAdd k, u) := by
    apply Prod.ext
    · exact Multiplicative.toAdd.injective (by rfl)
    · rfl
  have hx : fieldOnePadicValuationUnitForward q
      (Multiplicative.ofAdd k, u) = x := by
    change (fieldOnePadicValuationUnitContinuousMulEquiv q)
      (Multiplicative.ofAdd k, u) = x
    rw [← hz]
    exact (fieldOnePadicValuationUnitContinuousMulEquiv q).apply_symm_apply x
  rw [← hx, fieldOnePadicSoninSigma_apply_forward,
    fieldOnePadic_valuation_forward]
  rfl

/-- Prime exponent of an `S`-unit is exactly its valuation in the canonical
local p-adic model. -/
theorem fieldOneSUnit_localPadic_valuation
    (S : Finset (HeightOneSpectrum ℤ))
    (q : fieldOneSUnitSubgroup S) (v : ↑S) :
    Padic.valuation
        (fieldOneLocalPadicContinuousAddEquiv v.1
          (algebraMap ℚ (v.1.adicCompletion ℚ) (q.1 : ℚ))) =
      fieldOneSUnitExponent S q v := by
  let P : Nat.Primes := Rat.HeightOneSpectrum.primesEquiv v.1
  let e := Rat.HeightOneSpectrum.adicCompletion.padicEquiv v.1
  have he : e (algebraMap ℚ (v.1.adicCompletion ℚ) (q.1 : ℚ)) =
      ((q.1 : ℚ) : ℚ_[P.1]) := e.commutes (q.1 : ℚ)
  change Padic.valuation
      (e (algebraMap ℚ (v.1.adicCompletion ℚ) (q.1 : ℚ))) = _
  rw [he, Padic.valuation_ratCast]
  unfold fieldOneSUnitExponent
  rw [deningerRatExp_apply_of_prime P.2]

/-- A norm-one local unit has valuation zero after canonical p-adic
transport.  The norm-one condition is encoded in its type. -/
theorem fieldOneAdicNormOneUnit_padic_valuation
    (v : HeightOneSpectrum ℤ) (a : FieldOneAdicNormOneUnits v) :
    Padic.valuation
        (fieldOneLocalPadicContinuousAddEquiv v (a.1 : v.adicCompletion ℚ)) = 0 := by
  let P : Nat.Primes := Rat.HeightOneSpectrum.primesEquiv v
  let e := Rat.HeightOneSpectrum.adicCompletion.padicEquiv v
  let z : ℚ_[P.1] := e (a.1 : v.adicCompletion ℚ)
  have hz0 : z ≠ 0 := by
    dsimp [z]
    exact (map_ne_zero e).mpr (Units.ne_zero a.1)
  have hzle : ‖z‖ ≤ 1 := by
    exact (fieldOneAdic_padicEquiv_norm_le_one_iff v _).2 a.2.le
  have hzinvle : ‖z⁻¹‖ ≤ 1 := by
    have hlocalInv : ‖((a.1⁻¹ : (v.adicCompletion ℚ)ˣ) :
        v.adicCompletion ℚ)‖ ≤ 1 := by
      rw [Units.val_inv_eq_inv_val, norm_inv, a.2]
      simp
    have hmapInv : e (((a.1⁻¹ : (v.adicCompletion ℚ)ˣ) :
        v.adicCompletion ℚ)) = z⁻¹ := by
      simp [z]
    rw [← hmapInv]
    exact (fieldOneAdic_padicEquiv_norm_le_one_iff v _).2 hlocalInv
  have honele : 1 ≤ ‖z‖ := by
    have hnorm0 : ‖z‖ ≠ 0 := norm_ne_zero_iff.mpr hz0
    calc
      1 = ‖z‖ * ‖z‖⁻¹ := (mul_inv_cancel₀ hnorm0).symm
      _ = ‖z‖ * ‖z⁻¹‖ := by rw [norm_inv]
      _ ≤ ‖z‖ * 1 := mul_le_mul_of_nonneg_left hzinvle (norm_nonneg z)
      _ = ‖z‖ := mul_one _
  have hznorm : ‖z‖ = 1 := le_antisymm hzle honele
  have hpow : (P.1 : ℝ) ^ (-z.valuation) = 1 := by
    rw [← Padic.norm_eq_zpow_neg_valuation hz0, hznorm]
  have hvalneg : -z.valuation = 0 :=
    (zpow_eq_one_iff_right₀ (by positivity)
      (by exact_mod_cast P.2.one_lt.ne')).1 hpow
  have hval : z.valuation = 0 := neg_eq_zero.mp hvalneg
  exact hval

theorem fieldOneFiniteStageAngularLocalPadic_valuation
    (S : Finset (HeightOneSpectrum ℤ))
    (k : FieldOneFiniteStageModuleOneClass S) (v : ↑S) :
    Padic.valuation
        (fieldOneLocalPadicContinuousAddEquiv v.1
          (fieldOneFiniteStageAngularFiniteEmbedding S k v)) = 0 := by
  exact fieldOneAdicNormOneUnit_padic_valuation v.1
    (fieldOneFiniteStageAngularTorusRepresentative S k v)

/-- Literal product of local CCM vectors `σ_p` on a finite p-adic product. -/
def fieldOnePadicProductSoninSigma :
    compactlySupportedLocallyConstant (FieldOnePadicProduct p) := by
  let g : FieldOnePadicProduct p → ℂ := fun x =>
    ∏ i, (fieldOnePadicSoninSigma (p i)).1 (x i)
  let glc : LocallyConstant (FieldOnePadicProduct p) ℂ :=
    ⟨g, by
      dsimp only [g]
      have hprod :
          ((∏ i : ι, (fun x : FieldOnePadicProduct p =>
              (fieldOnePadicSoninSigma (p i)).1 (x i))) :
              FieldOnePadicProduct p → ℂ) =
            (fun x => ∏ i, (fieldOnePadicSoninSigma (p i)).1 (x i)) := by
        funext x
        simp
      rw [← hprod]
      apply Finset.prod_induction (s := Finset.univ)
        (fun i : ι => fun x : FieldOnePadicProduct p =>
          (fieldOnePadicSoninSigma (p i)).1 (x i))
        IsLocallyConstant
      · intro a b ha hb
        exact ha.mul hb
      · simp [IsLocallyConstant.iff_eventually_eq]
      · intro i hi
        exact (fieldOnePadicSoninSigma (p i)).1.isLocallyConstant.comp_continuous
          (continuous_apply i)⟩
  refine ⟨glc, ?_⟩
  apply HasCompactSupport.of_support_subset_isCompact
    (isCompact_univ_pi fun i => (fieldOnePadicSoninSigma (p i)).2)
  intro x hx
  rw [Set.mem_pi]
  intro i hi
  by_contra hxi
  apply hx
  change ∏ j, (fieldOnePadicSoninSigma (p j)).1 (x j) = 0
  exact Finset.prod_eq_zero (Finset.mem_univ i)
    (image_eq_zero_of_notMem_tsupport hxi)

@[simp] theorem fieldOnePadicProductSoninSigma_apply
    (x : FieldOnePadicProduct p) :
    (fieldOnePadicProductSoninSigma p).1 x =
      ∏ i, (fieldOnePadicSoninSigma (p i)).1 (x i) := rfl

theorem fieldOnePadicBruhatFourier_soninSigma_pointwise
    (q : ℕ) [Fact q.Prime] (y : ℚ_[q]) :
    fieldOnePadicBruhatFourier q (fieldOnePadicSoninSigma q) y =
      (fieldOnePadicSoninSigma q).1 y := by
  have h := congrArg
    (fun f : compactlySupportedLocallyConstant ℚ_[q] => f.1 y)
    (fieldOnePadicBruhatFourier_soninSigma q)
  exact h

/-- Exact finite-product Fourier fixed-point identity, proved from finite
Fubini and the local identities. -/
theorem fieldOnePadicProductBruhatFourier_soninSigma
    (y : FieldOnePadicProduct p) :
    fieldOnePadicProductBruhatFourier p
        (fieldOnePadicProductSoninSigma p) y =
      (fieldOnePadicProductSoninSigma p).1 y := by
  rw [fieldOnePadicProductBruhatFourier]
  change (∫ x, (∏ i, fieldOnePadicStandardAddChar (p i) (-(x i * y i))) *
      (∏ i, (fieldOnePadicSoninSigma (p i)).1 (x i))
      ∂(Measure.pi fun i => fieldOnePadicUnitBallNormalizedHaar (p i))) = _
  change _ = ∏ i, (fieldOnePadicSoninSigma (p i)).1 (y i)
  have hintegrand :
      (fun x : FieldOnePadicProduct p =>
        (∏ i, fieldOnePadicStandardAddChar (p i) (-(x i * y i))) *
          ∏ i, (fieldOnePadicSoninSigma (p i)).1 (x i)) =
      (fun x : FieldOnePadicProduct p =>
        ∏ i, fieldOnePadicStandardAddChar (p i) (-(x i * y i)) *
          (fieldOnePadicSoninSigma (p i)).1 (x i)) := by
    funext x
    exact Finset.prod_mul_distrib.symm
  rw [hintegrand]
  calc
    (∫ x : (i : ι) → ℚ_[p i],
        ∏ i, fieldOnePadicStandardAddChar (p i) (-(x i * y i)) *
          (fieldOnePadicSoninSigma (p i)).1 (x i)
        ∂(Measure.pi fun i => fieldOnePadicUnitBallNormalizedHaar (p i))) =
        ∏ i, ∫ x : ℚ_[p i],
          fieldOnePadicStandardAddChar (p i) (-(x * y i)) *
            (fieldOnePadicSoninSigma (p i)).1 x
          ∂fieldOnePadicUnitBallNormalizedHaar (p i) :=
      integral_fintype_prod_eq_prod
        (fun i x => fieldOnePadicStandardAddChar (p i) (-(x * y i)) *
          (fieldOnePadicSoninSigma (p i)).1 x)
    _ = ∏ i, (fieldOnePadicSoninSigma (p i)).1 (y i) := by
      apply Finset.prod_congr rfl
      intro i hi
      exact fieldOnePadicBruhatFourier_soninSigma_pointwise (p i) (y i)

theorem fieldOnePadicProductBruhatFourierLinear_soninSigma [DecidableEq ι] :
    fieldOnePadicProductBruhatFourierLinear p
        (fieldOnePadicProductSoninSigma p) =
      fieldOnePadicProductSoninSigma p := by
  apply Subtype.ext
  apply LocallyConstant.ext
  intro y
  exact fieldOnePadicProductBruhatFourier_soninSigma p y

/-- Literal finite-stage vector `σ_S`, transported only across the canonical
local-completion equivalences. -/
def fieldOneFiniteStageSoninSigma
    (S : Finset (HeightOneSpectrum ℤ)) :
    FieldOneFiniteStageFiniteBruhatSchwartz S := by
  let e := fieldOneFiniteStagePadicProductAddEquiv S
  let sigma := fieldOnePadicProductSoninSigma
    (fun v : ↑S => Rat.HeightOneSpectrum.primesEquiv v.1)
  let sigma' : LocallyConstant (FieldOneFiniteStageFinitePart S) ℂ :=
    LocallyConstant.comap ⟨fun x => e x, e.continuous⟩ sigma.1
  refine ⟨sigma', ?_⟩
  exact sigma.2.comp_homeomorph e.toHomeomorph

@[simp] theorem fieldOneFiniteStageSoninSigma_apply
    (S : Finset (HeightOneSpectrum ℤ))
    (x : FieldOneFiniteStageFinitePart S) :
    (fieldOneFiniteStageSoninSigma S).1 x =
      ∏ v : ↑S, (fieldOnePadicSoninSigma
        (Rat.HeightOneSpectrum.primesEquiv v.1)).1
          (fieldOneLocalPadicContinuousAddEquiv v.1 (x v)) := rfl

/-- Coefficient selected by `σ_S` on an `S`-unit orbit.  It is zero unless
every prime exponent is `0` or `-1`. -/
def fieldOneFiniteStageSoninSigmaOrbitCoefficient
    (S : Finset (HeightOneSpectrum ℤ))
    (q : fieldOneSUnitSubgroup S) : ℂ :=
  ∏ v : ↑S,
    if fieldOneSUnitExponent S q v = 0 then 1
    else if fieldOneSUnitExponent S q v = -1 then
      -((Rat.HeightOneSpectrum.primesEquiv v.1 : ℂ)⁻¹)
    else 0

/-- Exact evaluation on every rational `S`-unit translate of every angular
representative.  This is the orbit-classification core of equation (57). -/
theorem fieldOneFiniteStageSoninSigma_sunitAngular
    (S : Finset (HeightOneSpectrum ℤ))
    (q : fieldOneSUnitSubgroup S)
    (k : FieldOneFiniteStageModuleOneClass S) :
    (fieldOneFiniteStageSoninSigma S).1
        (fun v =>
          algebraMap ℚ (v.1.adicCompletion ℚ) (q.1 : ℚ) *
            fieldOneFiniteStageAngularFiniteEmbedding S k v) =
      fieldOneFiniteStageSoninSigmaOrbitCoefficient S q := by
  rw [fieldOneFiniteStageSoninSigma_apply,
    fieldOneFiniteStageSoninSigmaOrbitCoefficient]
  apply Finset.prod_congr rfl
  intro v hv
  let P : Nat.Primes := Rat.HeightOneSpectrum.primesEquiv v.1
  let e := Rat.HeightOneSpectrum.adicCompletion.padicEquiv v.1
  let a : v.1.adicCompletion ℚ :=
    algebraMap ℚ (v.1.adicCompletion ℚ) (q.1 : ℚ) *
      fieldOneFiniteStageAngularFiniteEmbedding S k v
  have ha0 : a ≠ 0 := by
    apply mul_ne_zero
    · exact (map_ne_zero (algebraMap ℚ (v.1.adicCompletion ℚ))).2
        (Units.ne_zero q.1)
    · exact Units.ne_zero
        (fieldOneFiniteStageAngularTorusRepresentative S k v).1
  have hea0 : e a ≠ 0 := (map_ne_zero e).2 ha0
  let au : ℚ_[P.1]ˣ := Units.mk0 (e a) hea0
  change (fieldOnePadicSoninSigma P.1).1 (e a) = _
  change (fieldOnePadicSoninSigma P.1).1 (au : ℚ_[P.1]) = _
  rw [fieldOnePadicSoninSigma_apply_unit]
  have hval : Padic.valuation (au : ℚ_[P.1]) =
      fieldOneSUnitExponent S q v := by
    have hqval := fieldOneSUnit_localPadic_valuation S q v
    change Padic.valuation
        (e (algebraMap ℚ (v.1.adicCompletion ℚ) (q.1 : ℚ))) =
      fieldOneSUnitExponent S q v at hqval
    have hkval := fieldOneFiniteStageAngularLocalPadic_valuation S k v
    change Padic.valuation
        (e (fieldOneFiniteStageAngularFiniteEmbedding S k v)) = 0 at hkval
    change Padic.valuation (e a) = fieldOneSUnitExponent S q v
    change Padic.valuation
        (e (algebraMap ℚ (v.1.adicCompletion ℚ) (q.1 : ℚ) *
          fieldOneFiniteStageAngularFiniteEmbedding S k v)) = _
    rw [map_mul, Padic.valuation_mul]
    · rw [hqval, hkval, add_zero]
    · exact (map_ne_zero e).2
        ((map_ne_zero (algebraMap ℚ (v.1.adicCompletion ℚ))).2
          (Units.ne_zero q.1))
    · exact (map_ne_zero e).2 (Units.ne_zero
        (fieldOneFiniteStageAngularTorusRepresentative S k v).1)
  rw [hval]

theorem fieldOneFiniteStageFiniteBruhatToPadicProduct_soninSigma
    (S : Finset (HeightOneSpectrum ℤ)) :
    fieldOneFiniteStageFiniteBruhatToPadicProduct S
        (fieldOneFiniteStageSoninSigma S) =
      fieldOnePadicProductSoninSigma
        (fun v : ↑S => Rat.HeightOneSpectrum.primesEquiv v.1) := by
  classical
  apply Subtype.ext
  apply LocallyConstant.ext
  intro y
  simp [fieldOneFiniteStageSoninSigma,
    fieldOneFiniteStageFiniteBruhatToPadicProduct_apply]

/-- Exact finite-place identity `F_S σ_S = σ_S` in the source finite-stage
Bruhat space. -/
theorem fieldOneFiniteStageFiniteBruhatFourier_soninSigma
    (S : Finset (HeightOneSpectrum ℤ)) :
    fieldOneFiniteStageFiniteBruhatFourierLinear S
        (fieldOneFiniteStageSoninSigma S) =
      fieldOneFiniteStageSoninSigma S := by
  classical
  apply Subtype.ext
  apply LocallyConstant.ext
  intro y
  change (fieldOneFiniteStageFiniteBruhatFourierBruhat S
    (fieldOneFiniteStageSoninSigma S)).1 y = _
  rw [fieldOneFiniteStageFiniteBruhatFourierBruhat_apply,
    fieldOneFiniteStageFiniteBruhatFourier_eq_padic]
  rw [fieldOneFiniteStageFiniteBruhatToPadicProduct_soninSigma]
  rw [fieldOnePadicProductBruhatFourier_soninSigma]
  rfl

@[simp] theorem fieldOneFiniteStageFiniteBruhatFourierBruhat_soninSigma
    (S : Finset (HeightOneSpectrum ℤ)) :
    fieldOneFiniteStageFiniteBruhatFourierBruhat S
        (fieldOneFiniteStageSoninSigma S) =
      fieldOneFiniteStageSoninSigma S := by
  change fieldOneFiniteStageFiniteBruhatFourierLinear S
      (fieldOneFiniteStageSoninSigma S) = _
  exact fieldOneFiniteStageFiniteBruhatFourier_soninSigma S

/-! ## Literal semilocal theta core -/

/-- The CCM test-core map `f ↦ f ⊗ σ_S`, before periodization and
half-density completion. -/
def fieldOneFiniteStageThetaBruhatCoreLinearMap
    (S : Finset (HeightOneSpectrum ℤ)) :
    SchwartzMap ℝ ℂ →ₗ[ℂ] FieldOneFiniteStageBruhatSchwartz S where
  toFun f := f ⊗ₜ[ℂ] fieldOneFiniteStageSoninSigma S
  map_add' f g := TensorProduct.add_tmul f g
    (fieldOneFiniteStageSoninSigma S)
  map_smul' c f := (TensorProduct.smul_tmul' c f
    (fieldOneFiniteStageSoninSigma S)).symm

@[simp] theorem fieldOneFiniteStageThetaBruhatCoreLinearMap_apply
    (S : Finset (HeightOneSpectrum ℤ)) (f : SchwartzMap ℝ ℂ) :
    fieldOneFiniteStageThetaBruhatCoreLinearMap S f =
      f ⊗ₜ[ℂ] fieldOneFiniteStageSoninSigma S := rfl

/-- Exact Fourier covariance of the literal `σ_S ⊗ f` core. -/
theorem fieldOneFiniteStageBruhatFourier_thetaCore
    (S : Finset (HeightOneSpectrum ℤ)) (f : SchwartzMap ℝ ℂ) :
    fieldOneFiniteStageBruhatFourierLinearEquiv S
        (fieldOneFiniteStageThetaBruhatCoreLinearMap S f) =
      fieldOneFiniteStageThetaBruhatCoreLinearMap S (𝓕⁻ f) := by
  rw [fieldOneFiniteStageThetaBruhatCoreLinearMap_apply,
    fieldOneFiniteStageBruhatFourierLinearEquiv_tmul,
    fieldOneFiniteStageFiniteBruhatFourierBruhat_soninSigma,
    fieldOneFiniteStageThetaBruhatCoreLinearMap_apply]

/-- Literal class-space realization of `σ_S ⊗ f`: periodization followed by
the source half-density map. -/
def fieldOneFiniteStageThetaClassBruhatCoreLinearMap
    (S : Finset (HeightOneSpectrum ℤ)) :
    SchwartzMap ℝ ℂ →ₗ[ℂ] FieldOneFiniteStageClassL2 S :=
  (fieldOneFiniteStageClassBruhatHalfDensityLinearMap S).comp
    (fieldOneFiniteStageThetaBruhatCoreLinearMap S)

@[simp] theorem fieldOneFiniteStageThetaClassBruhatCoreLinearMap_apply
    (S : Finset (HeightOneSpectrum ℤ)) (f : SchwartzMap ℝ ℂ) :
    fieldOneFiniteStageThetaClassBruhatCoreLinearMap S f =
      fieldOneFiniteStageClassBruhatHalfDensityLinearMap S
        (f ⊗ₜ[ℂ] fieldOneFiniteStageSoninSigma S) := rfl

/-- Exact Fourier covariance on literal `L²(X_S)`, proved on the independent
Bruhat core rather than imposed through a transported support definition. -/
theorem fieldOneFiniteStageClassFourier_thetaClassCore
    (S : Finset (HeightOneSpectrum ℤ)) (f : SchwartzMap ℝ ℂ) :
    fieldOneFiniteStageClassFourierUnitary S
        (fieldOneFiniteStageThetaClassBruhatCoreLinearMap S f) =
      fieldOneFiniteStageThetaClassBruhatCoreLinearMap S (𝓕⁻ f) := by
  rw [fieldOneFiniteStageThetaClassBruhatCoreLinearMap_apply,
    fieldOneFiniteStageClassFourierUnitary_classBruhat,
    fieldOneFiniteStageBruhatFourierLinearEquiv_tmul,
    fieldOneFiniteStageFiniteBruhatFourierBruhat_soninSigma,
    fieldOneFiniteStageThetaClassBruhatCoreLinearMap_apply]

/-! ## Radiality and literal invariant landing -/

theorem fieldOneFiniteStageThetaBruhatCore_orbit_independentAngular
    (S : Finset (HeightOneSpectrum ℤ)) (f : SchwartzMap ℝ ℂ)
    (k l : FieldOneFiniteStageModuleOneClass S) (t : ℝ)
    (q : fieldOneSUnitSubgroup S) :
    fieldOneFiniteStageBruhatOrbit S
        (fieldOneFiniteStageThetaBruhatCoreLinearMap S f)
        (fieldOneFiniteStageBruhatLogRayIdele S
          (fun v => (fieldOneFiniteStageAngularTorusRepresentative S k v).1) t) q =
      fieldOneFiniteStageBruhatOrbit S
        (fieldOneFiniteStageThetaBruhatCoreLinearMap S f)
        (fieldOneFiniteStageBruhatLogRayIdele S
          (fun v => (fieldOneFiniteStageAngularTorusRepresentative S l v).1) t) q := by
  rw [fieldOneFiniteStageThetaBruhatCoreLinearMap_apply,
    fieldOneFiniteStageBruhatOrbit_tmul,
    fieldOneFiniteStageBruhatOrbit_tmul]
  unfold fieldOneFiniteStageBruhatPureTensorOrbit
  change f (Real.exp t * (((q.1 : ℚ) : ℚ) : ℝ)) *
      (fieldOneFiniteStageSoninSigma S).1
        (fun v => algebraMap ℚ (v.1.adicCompletion ℚ) (q.1 : ℚ) *
          fieldOneFiniteStageAngularFiniteEmbedding S k v) =
    f (Real.exp t * (((q.1 : ℚ) : ℚ) : ℝ)) *
      (fieldOneFiniteStageSoninSigma S).1
        (fun v => algebraMap ℚ (v.1.adicCompletion ℚ) (q.1 : ℚ) *
          fieldOneFiniteStageAngularFiniteEmbedding S l v)
  rw [fieldOneFiniteStageSoninSigma_sunitAngular,
    fieldOneFiniteStageSoninSigma_sunitAngular]

theorem fieldOneFiniteStageThetaBruhatCore_logPeriodization_independentAngular
    (S : Finset (HeightOneSpectrum ℤ)) (f : SchwartzMap ℝ ℂ)
    (k l : FieldOneFiniteStageModuleOneClass S) (t : ℝ) :
    fieldOneFiniteStageBruhatLogPeriodization S
        (fieldOneFiniteStageThetaBruhatCoreLinearMap S f) (k, t) =
      fieldOneFiniteStageBruhatLogPeriodization S
        (fieldOneFiniteStageThetaBruhatCoreLinearMap S f) (l, t) := by
  rw [fieldOneFiniteStageBruhatLogPeriodization,
    fieldOneFiniteStageBruhatLogPeriodization,
    fieldOneFiniteStageBruhatPeriodization,
    fieldOneFiniteStageBruhatPeriodization]
  apply tsum_congr
  intro q
  exact fieldOneFiniteStageThetaBruhatCore_orbit_independentAngular
    S f k l t q

theorem fieldOneFiniteStageThetaBruhatCore_logHalfDensity_independentAngular
    (S : Finset (HeightOneSpectrum ℤ)) (f : SchwartzMap ℝ ℂ)
    (k l : FieldOneFiniteStageModuleOneClass S) (t : ℝ) :
    fieldOneFiniteStageBruhatLogHalfDensity S
        (fieldOneFiniteStageThetaBruhatCoreLinearMap S f) (k, t) =
      fieldOneFiniteStageBruhatLogHalfDensity S
        (fieldOneFiniteStageThetaBruhatCoreLinearMap S f) (l, t) := by
  unfold fieldOneFiniteStageBruhatLogHalfDensity
  rw [fieldOneFiniteStageThetaBruhatCore_logPeriodization_independentAngular]

theorem fieldOneFiniteStageThetaBruhatCore_splitHalfDensity_independentAngular
    (S : Finset (HeightOneSpectrum ℤ)) (f : SchwartzMap ℝ ℂ)
    (k l : FieldOneFiniteStageModuleOneClass S) (u : ℝ≥0ˣ) :
    fieldOneFiniteStageBruhatSplitHalfDensity S
        (fieldOneFiniteStageThetaBruhatCoreLinearMap S f) (k, u) =
      fieldOneFiniteStageBruhatSplitHalfDensity S
        (fieldOneFiniteStageThetaBruhatCoreLinearMap S f) (l, u) := by
  exact fieldOneFiniteStageThetaBruhatCore_logHalfDensity_independentAngular
    S f k l (fieldOnePositiveUnitsExpHomeomorph.symm u)

/-- The literal theta Bruhat half-density is fixed by the actual module-one
regular representation on the split product `L²` space. -/
theorem fieldOneFiniteStageThetaBruhatHalfDensity_mem_productInvariants
    (S : Finset (HeightOneSpectrum ℤ)) (f : SchwartzMap ℝ ℂ) :
    fieldOneFiniteStageBruhatHalfDensityLinearMap S
        (fieldOneFiniteStageThetaBruhatCoreLinearMap S f) ∈
      fieldOneFiniteStageProductModuleOneInvariantSubmodule S := by
  intro k
  let h := fieldOneFiniteStageBruhatHalfDensityLinearMap S
    (fieldOneFiniteStageThetaBruhatCoreLinearMap S f)
  change fieldOneFiniteStageProductModuleOneLeftRegular S k h = h
  change Lp.compMeasurePreserving ((k⁻¹, 1) * ·)
      (measurePreserving_mul_left
        (fieldOneFiniteStageSplitProductHaarMeasure S) (k⁻¹, 1)) h = h
  apply Lp.ext
  let mp := measurePreserving_mul_left
    (fieldOneFiniteStageSplitProductHaarMeasure S) (k⁻¹, 1)
  have hleft := Lp.coeFn_compMeasurePreserving h mp
  have hae := fieldOneFiniteStageBruhatHalfDensityL2_ae S
    (fieldOneFiniteStageThetaBruhatCoreLinearMap S f)
  have haecomp := mp.quasiMeasurePreserving.ae_eq_comp hae
  filter_upwards [hleft, haecomp, hae] with x hleftx hcompx hx
  rw [hleftx]
  change (fieldOneFiniteStageBruhatHalfDensityL2 S
      (fieldOneFiniteStageThetaBruhatCoreLinearMap S f))
        ((k⁻¹, 1) * x) =
    (fieldOneFiniteStageBruhatHalfDensityL2 S
      (fieldOneFiniteStageThetaBruhatCoreLinearMap S f)) x
  have hcompx' :
      (fieldOneFiniteStageBruhatHalfDensityL2 S
        (fieldOneFiniteStageThetaBruhatCoreLinearMap S f)) ((k⁻¹, 1) * x) =
        fieldOneFiniteStageBruhatSplitHalfDensity S
          (fieldOneFiniteStageThetaBruhatCoreLinearMap S f) ((k⁻¹, 1) * x) := by
    simpa only [Function.comp_apply] using hcompx
  rw [hcompx', hx]
  have hmul : (k⁻¹, (1 : ℝ≥0ˣ)) * x = (k⁻¹ * x.1, x.2) := by
    apply Prod.ext <;> simp
  rw [hmul]
  exact fieldOneFiniteStageThetaBruhatCore_splitHalfDensity_independentAngular
    S f (k⁻¹ * x.1) x.1 x.2

/-- The literal class-space vector `E(σ_S ⊗ f)` lies in the actual
`K_S`-fixed subspace of `L²(X_S)`. -/
theorem fieldOneFiniteStageThetaClassBruhatCore_mem_invariants
    (S : Finset (HeightOneSpectrum ℤ)) (f : SchwartzMap ℝ ℂ) :
    fieldOneFiniteStageThetaClassBruhatCoreLinearMap S f ∈
      fieldOneFiniteStageClassModuleOneInvariantSubmodule S := by
  intro k
  apply (fieldOneFiniteStageClassToSplitProductL2Unitary S).injective
  change fieldOneFiniteStageSplitL2Unitary S
      (fieldOneFiniteStageClassToSplitClassL2Unitary S
        (fieldOneFiniteStageClassModuleOneLeftRegular S k
          (fieldOneFiniteStageThetaClassBruhatCoreLinearMap S f))) = _
  rw [fieldOneFiniteStageClassToSplitClassL2Unitary_intertwines_moduleOne,
    fieldOneFiniteStageSplitL2Unitary_intertwines_moduleOne]
  have hinv := fieldOneFiniteStageThetaBruhatHalfDensity_mem_productInvariants S f
  have hcore :
      fieldOneFiniteStageClassToSplitProductL2Unitary S
          (fieldOneFiniteStageThetaClassBruhatCoreLinearMap S f) =
        fieldOneFiniteStageBruhatHalfDensityLinearMap S
          (fieldOneFiniteStageThetaBruhatCoreLinearMap S f) := by
    rw [fieldOneFiniteStageThetaClassBruhatCoreLinearMap_apply,
      fieldOneFiniteStageClassToSplitProductL2Unitary_classBruhat,
      fieldOneFiniteStageThetaBruhatCoreLinearMap_apply]
  change fieldOneFiniteStageProductModuleOneLeftRegular S k
      (fieldOneFiniteStageClassToSplitProductL2Unitary S
        (fieldOneFiniteStageThetaClassBruhatCoreLinearMap S f)) =
    fieldOneFiniteStageClassToSplitProductL2Unitary S
      (fieldOneFiniteStageThetaClassBruhatCoreLinearMap S f)
  rw [hcore, hinv k]

/-- Literal CCM theta on the Schwartz--Bruhat core, now valued in the actual
fixed subspace rather than an abstractly transported copy. -/
def fieldOneFiniteStageThetaInvariantBruhatCoreLinearMap
    (S : Finset (HeightOneSpectrum ℤ)) :
    SchwartzMap ℝ ℂ →ₗ[ℂ]
      fieldOneFiniteStageClassModuleOneInvariantSubmodule S where
  toFun f := ⟨fieldOneFiniteStageThetaClassBruhatCoreLinearMap S f,
    fieldOneFiniteStageThetaClassBruhatCore_mem_invariants S f⟩
  map_add' f g := by
    apply Subtype.ext
    exact map_add (fieldOneFiniteStageThetaClassBruhatCoreLinearMap S) f g
  map_smul' c f := by
    apply Subtype.ext
    exact map_smul (fieldOneFiniteStageThetaClassBruhatCoreLinearMap S) c f

end

end GaloisForLFunctions.RHTower
