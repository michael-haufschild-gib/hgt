import GaloisForLFunctions.HTGeometry.MatrixFactorizationCategory
import GaloisForLFunctions.HTGeometry.ParachainConnesComparisonLaw
import Mathlib.Algebra.Category.ModuleCat.ProjectiveDimension
import Mathlib.Algebra.DualNumber
import Mathlib.Algebra.Module.Projective
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.InnerProductSpace.LinearMap
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.LinearAlgebra.Quotient.Basic
import Mathlib.RingTheory.Nilpotent.Basic
import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.RingTheory.PowerSeries.NoZeroDivisors
import Mathlib.RingTheory.DualNumber
import Mathlib.RingTheory.RegularLocalRing.Defs

/-!
# Polarized exactness horizon and relative Connes phase law

Exact local and Hilbert-space infrastructure for the Stage-2 card
`polarized-exactness-horizon-and-relative-connes-phase-law.md`.

This file presently proves the sign involution and its conormal action, the exact phase fibre and
real differential kernel of positive rank-one observation, the general power-series `mu_m` phase
automorphism, and the reflected positive-energy identity.  Matrix-factorization classification and
the relative connecting class are developed below in the same module.
-/

open scoped InnerProductSpace DualNumber

set_option maxRecDepth 4000

namespace GaloisForLFunctions.HTGeometry

open TrivSqZeroExt

/-! ## Doubled local horizon and its sign action -/

variable {K : Type*} [Field K]

/-- Algebra endomorphism of the dual-number doubled horizon induced by `a ↦ -a`. -/
noncomputable def dualNumberSignHom : DualNumber K →ₐ[K] DualNumber K :=
  TrivSqZeroExt.map (-LinearMap.id)

@[simp] lemma dualNumberSignHom_eps :
    dualNumberSignHom (K := K) DualNumber.eps = -DualNumber.eps := by
  change TrivSqZeroExt.map (-LinearMap.id) (TrivSqZeroExt.inr 1) =
    -TrivSqZeroExt.inr 1
  simp only [TrivSqZeroExt.map_inr, LinearMap.neg_apply, LinearMap.id_apply,
    TrivSqZeroExt.inr_neg]

@[simp] lemma dualNumberSignHom_involutive (x : DualNumber K) :
    dualNumberSignHom (dualNumberSignHom x) = x := by
  apply TrivSqZeroExt.ext
  · simp only [dualNumberSignHom, TrivSqZeroExt.fst_map]
  · simp only [dualNumberSignHom, TrivSqZeroExt.snd_map, LinearMap.neg_apply,
      LinearMap.id_apply, neg_neg]

/-- The sign map on the doubled horizon is an involutive algebra equivalence. -/
noncomputable def dualNumberSign : DualNumber K ≃ₐ[K] DualNumber K where
  __ := AlgEquiv.ofBijective dualNumberSignHom ⟨
    fun _ _ h ↦ by
      have h' := congrArg dualNumberSignHom h
      simpa only [dualNumberSignHom_involutive] using h',
    fun y ↦ ⟨dualNumberSignHom y, dualNumberSignHom_involutive y⟩⟩

@[simp] lemma dualNumberSign_apply (x : DualNumber K) :
    dualNumberSign (K := K) x = dualNumberSignHom x := rfl

/-- The sign involution acts by weight `-1` on the conormal generator. -/
@[simp] theorem dualNumberSign_eps :
    dualNumberSign (K := K) DualNumber.eps = -DualNumber.eps :=
  dualNumberSignHom_eps

/-- The conormal generator survives in the doubled horizon. -/
theorem dualNumber_eps_ne_zero : (DualNumber.eps : DualNumber K) ≠ 0 := by
  intro h
  have hsnd := congrArg TrivSqZeroExt.snd h
  exact one_ne_zero <| by
    simpa only [DualNumber.snd_eps, TrivSqZeroExt.snd_zero] using hsnd

/-- The doubled horizon is nonreduced, hence singular in the local Artinian field case. -/
theorem dualNumber_not_reduced : ¬ IsReduced (DualNumber K) := by
  intro hred
  have hz : (DualNumber.eps : DualNumber K) = 0 :=
    hred.eq_zero DualNumber.eps ⟨2, DualNumber.eps_pow_two⟩
  exact dualNumber_eps_ne_zero hz

/-- In characteristic different from two, no nonzero conormal vector is natural under the sign
involution. -/
theorem dualNumber_conormal_fixed_eq_zero
    (htwo : (2 : K) ≠ 0) (x : DualNumber K)
    (hx : ∃ c : K, x = c • DualNumber.eps)
    (hfix : dualNumberSign x = x) :
    x = 0 := by
  rcases hx with ⟨c, rfl⟩
  have hsnd := congrArg TrivSqZeroExt.snd hfix
  simp only [map_smul, dualNumberSign_eps, TrivSqZeroExt.snd_neg,
    TrivSqZeroExt.snd_smul, DualNumber.snd_eps, smul_eq_mul, mul_one] at hsnd
  have hneg : -c = c := by simpa using hsnd
  have hc2 : (2 : K) * c = 0 := calc
    (2 : K) * c = c + c := by ring
    _ = c + (-c) := congrArg (c + ·) hneg.symm
    _ = 0 := add_neg_cancel c
  have hc : c = 0 := (mul_eq_zero.mp hc2).resolve_left htwo
  simp [hc]

/-! ## Residue singularity and periodic resolution -/

section Residue

variable {K : Type*} [Field K]

local instance dualNumberResidueModule : Module (DualNumber K) K :=
  Module.compHom K (TrivSqZeroExt.fstHom K K K).toRingHom

/-- Residue quotient from the doubled horizon to its residue field. -/
noncomputable def dualNumberResidue : DualNumber K →ₗ[DualNumber K] K where
  toFun := TrivSqZeroExt.fst
  map_add' := TrivSqZeroExt.fst_add
  map_smul' x y := by
    change (x * y).fst = x.fst * y.fst
    exact TrivSqZeroExt.fst_mul x y

@[simp] theorem dualNumberResidue_apply (x : DualNumber K) :
    dualNumberResidue x = x.fst := rfl

theorem dualNumberResidue_surjective : Function.Surjective (dualNumberResidue (K := K)) := by
  intro y
  exact ⟨TrivSqZeroExt.inl y, by simp⟩

/-- Inclusion of the residue field as the square-zero socle. -/
noncomputable def dualNumberSocleInclusion : K →ₗ[DualNumber K] DualNumber K where
  toFun := TrivSqZeroExt.inr
  map_add' x y := by apply TrivSqZeroExt.ext <;> simp
  map_smul' x y := by
    change TrivSqZeroExt.inr (x.fst * y) = x * TrivSqZeroExt.inr y
    apply TrivSqZeroExt.ext <;> simp [mul_comm]

@[simp] theorem dualNumberSocleInclusion_apply (x : K) :
    dualNumberSocleInclusion x = TrivSqZeroExt.inr x := rfl

theorem dualNumberSocleInclusion_injective :
    Function.Injective (dualNumberSocleInclusion (K := K)) := by
  intro x y h
  have hsnd := congrArg TrivSqZeroExt.snd h
  change x = y at hsnd
  exact hsnd

theorem dualNumberSocle_range_eq_residue_ker :
    LinearMap.range (dualNumberSocleInclusion (K := K)) =
      LinearMap.ker (dualNumberResidue (K := K)) := by
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    simp
  · intro hx
    have hfst : x.fst = 0 := by simpa using hx
    refine ⟨x.snd, ?_⟩
    apply TrivSqZeroExt.ext
    · simp [hfst]
    · simp

/-- Exact self-syzygy sequence `0 → K → K[ε] → K → 0`. -/
noncomputable def dualNumberResidueShortComplex :
    CategoryTheory.ShortComplex (ModuleCat (DualNumber K)) :=
  CategoryTheory.ShortComplex.moduleCatMk
    (dualNumberSocleInclusion (K := K)) (dualNumberResidue (K := K)) (by
    ext x
    simp)

theorem dualNumberResidueShortComplex_shortExact :
    (dualNumberResidueShortComplex (K := K)).ShortExact where
  exact := (CategoryTheory.ShortComplex.moduleCat_exact_iff_range_eq_ker _).mpr
    (dualNumberSocle_range_eq_residue_ker (K := K))
  mono_f := (ModuleCat.mono_iff_injective _).mpr
    (dualNumberSocleInclusion_injective (K := K))
  epi_g := (ModuleCat.epi_iff_surjective _).mpr
    (dualNumberResidue_surjective (K := K))

/-- Multiplication by the nilpotent conormal generator. -/
noncomputable def dualNumberEpsMul :
    DualNumber K →ₗ[DualNumber K] DualNumber K :=
  LinearMap.mulLeft (DualNumber K) DualNumber.eps

@[simp] theorem dualNumberEpsMul_apply (x : DualNumber K) :
    dualNumberEpsMul x = DualNumber.eps * x := rfl

/-- Adjacent arrows in the periodic resolution compose to zero. -/
theorem dualNumberEpsMul_sq (x : DualNumber K) :
    dualNumberEpsMul (dualNumberEpsMul x) = 0 := by
  simp [dualNumberEpsMul, ← mul_assoc, DualNumber.eps_mul_eps]

/-- Exactness at every free term of the periodic residue resolution. -/
theorem dualNumberEpsMul_range_eq_ker :
    LinearMap.range (dualNumberEpsMul (K := K)) =
      LinearMap.ker (dualNumberEpsMul (K := K)) := by
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    exact dualNumberEpsMul_sq y
  · intro hx
    have hfst : x.fst = 0 := by
      have h := congrArg TrivSqZeroExt.snd hx
      simp only [dualNumberEpsMul_apply, TrivSqZeroExt.snd_mul,
        DualNumber.fst_eps, DualNumber.snd_eps, zero_smul,
        op_smul_eq_smul, zero_add, TrivSqZeroExt.snd_zero] at h
      simpa using h
    refine ⟨TrivSqZeroExt.inl x.snd, ?_⟩
    apply TrivSqZeroExt.ext
    · simp [hfst]
    · simp

/-- The periodic free differential factors through the residue and its recurring first syzygy. -/
theorem dualNumberEpsMul_eq_socle_comp_residue :
    dualNumberEpsMul (K := K) =
      (dualNumberSocleInclusion (K := K)).comp dualNumberResidue := by
  apply LinearMap.ext
  intro x
  apply TrivSqZeroExt.ext <;> simp [dualNumberEpsMul]

/-- The residue field of the doubled horizon is not projective over the doubled horizon. -/
theorem dualNumberResidue_not_projective :
    ¬ Module.Projective (DualNumber K) K := by
  intro hprojective
  letI : Module.Projective (DualNumber K) K := hprojective
  obtain ⟨s, hs⟩ := (dualNumberResidue (K := K)).exists_rightInverse_of_surjective
    (LinearMap.range_eq_top.mpr dualNumberResidue_surjective)
  have hs_one : (s 1).fst = 1 := by
    have h := LinearMap.congr_fun hs 1
    simpa using h
  have heps_one : (DualNumber.eps : DualNumber K) • (1 : K) = 0 := by
    change (DualNumber.eps : DualNumber K).fst * (1 : K) = 0
    simp
  have hlinear := s.map_smul (DualNumber.eps : DualNumber K) (1 : K)
  rw [heps_one, map_zero] at hlinear
  have heps_mul : (DualNumber.eps : DualNumber K) * s 1 =
      (s 1).fst • DualNumber.eps := by
    apply TrivSqZeroExt.ext <;> simp
  change (0 : DualNumber K) = (DualNumber.eps : DualNumber K) * s 1 at hlinear
  rw [heps_mul] at hlinear
  have hsnd := congrArg TrivSqZeroExt.snd hlinear
  simp only [TrivSqZeroExt.snd_zero, TrivSqZeroExt.snd_smul,
    DualNumber.snd_eps, smul_eq_mul, mul_one] at hsnd
  exact one_ne_zero (hs_one ▸ hsnd.symm)

/-- The recurring residue syzygy forces infinite projective dimension. -/
theorem dualNumberResidue_projectiveDimension_eq_top :
    CategoryTheory.projectiveDimension
      (ModuleCat.of (DualNumber K) K) = ⊤ := by
  by_contra htop
  obtain ⟨n, hn⟩ := (CategoryTheory.projectiveDimension_ne_top_iff
    (ModuleCat.of (DualNumber K) K)).mp htop
  let S := dualNumberResidueShortComplex (K := K)
  have hS : S.ShortExact := dualNumberResidueShortComplex_shortExact (K := K)
  have descend : ∀ n : ℕ,
      CategoryTheory.HasProjectiveDimensionLE
          (ModuleCat.of (DualNumber K) K) n →
        CategoryTheory.HasProjectiveDimensionLE
          (ModuleCat.of (DualNumber K) K) 0 := by
    intro m hm
    induction m with
    | zero => exact hm
    | succ m ih =>
        have hm' : CategoryTheory.HasProjectiveDimensionLT S.X₃ (m + 2) := by
          change CategoryTheory.HasProjectiveDimensionLT
            (ModuleCat.of (DualNumber K) K) (m + 2)
          simpa [CategoryTheory.HasProjectiveDimensionLE,
            Nat.succ_eq_add_one, Nat.add_assoc] using hm
        have hprojective : CategoryTheory.Projective S.X₂ := by
          dsimp [S, dualNumberResidueShortComplex,
            CategoryTheory.ShortComplex.moduleCatMk]
          infer_instance
        have hprev : CategoryTheory.HasProjectiveDimensionLT S.X₁ (m + 1) :=
          (hS.hasProjectiveDimensionLT_X₃_iff m hprojective).mp hm'
        apply ih
        change CategoryTheory.HasProjectiveDimensionLT
          (ModuleCat.of (DualNumber K) K) (m + 1)
        change CategoryTheory.HasProjectiveDimensionLT
          (ModuleCat.of (DualNumber K) K) (m + 1) at hprev
        exact hprev
  have hzero := descend n hn
  have hcat : CategoryTheory.Projective (ModuleCat.of (DualNumber K) K) :=
    (CategoryTheory.projective_iff_hasProjectiveDimensionLE_zero _).mpr hzero
  have hmodule : Module.Projective (DualNumber K) K :=
    (IsProjective.iff_projective K).mpr hcat
  exact dualNumberResidue_not_projective hmodule

/-- Every prime of the doubled horizon is maximal. -/
theorem dualNumber_krullDimLE_zero : Ring.KrullDimLE 0 (DualNumber K) := by
  apply Ring.KrullDimLE.mk₀
  intro I hI
  rcases DualNumber.ideal_trichotomy I with rfl | rfl | rfl
  · exfalso
    have hprod : (DualNumber.eps : DualNumber K) * DualNumber.eps ∈
        (⊥ : Ideal (DualNumber K)) := by
      rw [DualNumber.eps_mul_eps]
      exact Ideal.zero_mem _
    rcases hI.mem_or_mem hprod with hmem | hmem
    · exact dualNumber_eps_ne_zero (by simpa using hmem)
    · exact dualNumber_eps_ne_zero (by simpa using hmem)
  · exact DualNumber.isMaximal_span_singleton_eps
  · exact False.elim (hI.ne_top rfl)

/-- The doubled horizon has Krull dimension zero. -/
theorem dualNumber_krullDim_eq_zero : ringKrullDim (DualNumber K) = 0 :=
  ringKrullDimZero_iff_ringKrullDim_eq_zero.mp dualNumber_krullDimLE_zero

/-- Its nonzero maximal ideal needs exactly one generator. -/
theorem dualNumber_spanFinrank_maximalIdeal_eq_one :
    (IsLocalRing.maximalIdeal (DualNumber K)).spanFinrank = 1 := by
  rw [DualNumber.maximalIdeal_eq_span_singleton_eps]
  exact Submodule.spanFinrank_singleton dualNumber_eps_ne_zero

/-- The doubled horizon is not a regular local ring. -/
theorem dualNumber_not_regularLocalRing :
    ¬ IsRegularLocalRing (DualNumber K) := by
  intro hregular
  have h := hregular.spanFinrank_maximalIdeal
  rw [dualNumber_spanFinrank_maximalIdeal_eq_one,
    dualNumber_krullDim_eq_zero] at h
  exact one_ne_zero h

/-- Therefore the doubled horizon is not a regular ring. -/
theorem dualNumber_not_regularRing : ¬ IsRegularRing (DualNumber K) := by
  intro hregular
  letI : IsRegularRing (DualNumber K) := hregular
  exact dualNumber_not_regularLocalRing (K := K)
    (IsRegularLocalRing.of_isRegularRing_of_isLocalRing (DualNumber K))

end Residue

/-! ## Reduced horizon and completed doubled-energy ideal -/

section ReducedAndEnergy

open PowerSeries

variable {F : Type*} [Field F]

/-- The reduced horizon is a regular ring. -/
theorem reducedHorizon_isRegularRing : IsRegularRing F := by infer_instance

/-- Every module over the reduced field horizon is projective. -/
theorem reducedHorizon_everyModule_projective
    {M : Type*} [AddCommGroup M] [Module F M] : Module.Projective F M := by
  infer_instance

/-- Completed local parameter `q=1+X`. -/
noncomputable def completedHorizonParameter : F⟦X⟧ := 1 + PowerSeries.X

theorem completedHorizonParameter_isUnit :
    IsUnit (completedHorizonParameter (F := F)) := by
  rw [PowerSeries.isUnit_iff_constantCoeff]
  simp [completedHorizonParameter]

/-- Reflected positive energy at the completed identity horizon. -/
noncomputable def completedPositiveStokesEnergy : F⟦X⟧ :=
  completedHorizonParameter + completedHorizonParameter⁻¹ - 2

/-- Exact completed energy factorization `E(1+X)=X²/(1+X)`. -/
theorem completedPositiveStokesEnergy_eq :
    completedPositiveStokesEnergy (F := F) =
      PowerSeries.X ^ 2 * (completedHorizonParameter (F := F))⁻¹ := by
  let q : F⟦X⟧ := completedHorizonParameter
  have hq : q * q⁻¹ = 1 := PowerSeries.mul_inv_cancel q (by
    simp [q, completedHorizonParameter])
  have hqsub : q - 1 = PowerSeries.X := by simp [q, completedHorizonParameter]
  change q + q⁻¹ - 2 = PowerSeries.X ^ 2 * q⁻¹
  rw [← hqsub]
  calc
    q + q⁻¹ - 2 = q - 2 + q⁻¹ := by ring
    _ = (q * q⁻¹) * q - 2 * (q * q⁻¹) + q⁻¹ := by rw [hq]; ring
    _ = (q - 1) ^ 2 * q⁻¹ := by ring

/-- The energy generates exactly the doubled ideal `(X²)`. -/
theorem completedPositiveStokesEnergy_span_eq_square :
    Ideal.span ({completedPositiveStokesEnergy (F := F)} : Set F⟦X⟧) =
      Ideal.span ({PowerSeries.X ^ 2} : Set F⟦X⟧) := by
  rw [completedPositiveStokesEnergy_eq, Ideal.span_singleton_eq_span_singleton]
  apply associated_mul_unit_left
  rw [PowerSeries.isUnit_iff_constantCoeff]
  simp [completedHorizonParameter]

end ReducedAndEnergy

/-! ## Positive rank-one observation loses exactly phase -/

section Quantum

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]

/-- Positive rank-one observer `|ψ⟩⟨ψ|`. -/
noncomputable def positiveRankOne (psi : V) : V →L[ℂ] V :=
  InnerProductSpace.rankOne ℂ psi psi

/-- A unit complex phase is invisible to positive rank-one observation. -/
theorem positiveRankOne_phase (psi : V) (theta : ℝ) :
    positiveRankOne (Complex.exp ((theta : ℂ) * Complex.I) • psi) =
      positiveRankOne psi := by
  apply ContinuousLinearMap.ext
  intro x
  simp [positiveRankOne, InnerProductSpace.rankOne_apply, smul_smul,
    ← Complex.exp_conj, ← Complex.exp_add]

/-- Two nonzero vectors have the same positive rank-one observer exactly when they differ by a
real phase. -/
theorem positiveRankOne_eq_iff_phase {phi psi : V} (hphi : phi ≠ 0) (hpsi : psi ≠ 0) :
    positiveRankOne phi = positiveRankOne psi ↔
      ∃ theta : ℝ, phi = Complex.exp ((theta : ℂ) * Complex.I) • psi := by
  constructor
  · intro h
    obtain ⟨alpha, beta, halpha, hbeta, hrel, _⟩ :=
      InnerProductSpace.exists_of_rankOne_eq_rankOne hphi hphi h
    have hnormsq := congrArg norm h
    simp only [positiveRankOne, InnerProductSpace.norm_rankOne] at hnormsq
    have hnorm : ‖phi‖ = ‖psi‖ := by nlinarith [norm_nonneg phi, norm_nonneg psi]
    have hpsiNorm : ‖psi‖ ≠ 0 := norm_ne_zero_iff.mpr hpsi
    have halphaNorm : ‖alpha‖ = 1 := by
      rw [hrel, norm_smul] at hnorm
      apply (mul_right_cancel₀ hpsiNorm)
      simpa using hnorm
    refine ⟨alpha.arg, ?_⟩
    rw [hrel]
    congr 1
    symm
    simpa [halphaNorm] using Complex.norm_mul_exp_arg_mul_I alpha
  · rintro ⟨theta, rfl⟩
    exact positiveRankOne_phase psi theta

/-- Real differential of `ψ ↦ |ψ⟩⟨ψ|` applied to a tangent vector. -/
noncomputable def positiveRankOneDifferential (psi v : V) : V →L[ℂ] V :=
  InnerProductSpace.rankOne ℂ v psi + InnerProductSpace.rankOne ℂ psi v

/-- Every infinitesimal phase direction lies in the differential kernel. -/
theorem positiveRankOneDifferential_imaginary (psi : V) (r : ℝ) :
    positiveRankOneDifferential psi (((r : ℂ) * Complex.I) • psi) = 0 := by
  apply ContinuousLinearMap.ext
  intro x
  simp [positiveRankOneDifferential]

/-- Exact real differential kernel: `ker(dπ_ψ) = ℝ iψ`. -/
theorem positiveRankOneDifferential_eq_zero_iff {psi v : V} (hpsi : psi ≠ 0) :
    positiveRankOneDifferential psi v = 0 ↔
      ∃ r : ℝ, v = ((r : ℂ) * Complex.I) • psi := by
  constructor
  · intro hzero
    have happ := congrArg (fun T : V →L[ℂ] V ↦ T psi) hzero
    simp only [positiveRankOneDifferential, add_apply, zero_apply,
      InnerProductSpace.rankOne_apply] at happ
    have hinner : inner ℂ psi psi ≠ 0 := by
      exact inner_self_ne_zero.mpr hpsi
    let alpha : ℂ := -(inner ℂ v psi / inner ℂ psi psi)
    have hv : v = alpha • psi := by
      have hscaled : inner ℂ psi psi • v = -(inner ℂ v psi • psi) :=
        eq_neg_of_add_eq_zero_left happ
      calc
        v = (inner ℂ psi psi)⁻¹ • (inner ℂ psi psi • v) := by
          rw [smul_smul, inv_mul_cancel₀ hinner, one_smul]
        _ = (inner ℂ psi psi)⁻¹ • (-(inner ℂ v psi • psi)) := by rw [hscaled]
        _ = alpha • psi := by
          simp only [alpha, smul_neg, smul_smul, neg_smul]
          congr 1
          field_simp
    have hscaled : (alpha + star alpha) • positiveRankOne psi = 0 := by
      apply ContinuousLinearMap.ext
      intro x
      have hx := congrArg (fun T : V →L[ℂ] V ↦ T x) hzero
      rw [hv] at hx
      simpa [positiveRankOneDifferential, positiveRankOne,
        InnerProductSpace.rankOne_apply, inner_smul_left, smul_smul, add_smul] using hx
    have hoperator : positiveRankOne psi ≠ 0 := by
      exact InnerProductSpace.rankOne_ne_zero hpsi hpsi
    have halpha : alpha + star alpha = 0 :=
      (smul_eq_zero.mp hscaled).resolve_right hoperator
    have hare : alpha.re = 0 := by
      have := congrArg Complex.re halpha
      simpa [Complex.add_re, Complex.star_def] using this
    refine ⟨alpha.im, ?_⟩
    rw [hv]
    congr 1
    apply Complex.ext
    · simp [hare]
    · simp
  · rintro ⟨r, rfl⟩
    exact positiveRankOneDifferential_imaginary psi r

/-- Executed phase distance between two parameter times. -/
def executedPhaseLength (theta : ℝ → ℝ) (s t : ℝ) : ℝ :=
  |theta t - theta s|

/-- Every point on a phase orbit has the same positive observer. -/
theorem phaseOrbit_observer_constant (psi : V) (theta : ℝ → ℝ) (t : ℝ) :
    positiveRankOne (Complex.exp (((theta t : ℝ) : ℂ) * Complex.I) • psi) =
      positiveRankOne psi :=
  positiveRankOne_phase psi (theta t)

/-- A nonconstant phase path has a pair of times with positive executed phase length. -/
theorem exists_executedPhaseLength_pos_of_nonconstant (theta : ℝ → ℝ)
    (h : ¬ ∀ s t, theta s = theta t) :
    ∃ s t, 0 < executedPhaseLength theta s t := by
  push Not at h
  obtain ⟨s, t, hst⟩ := h
  refine ⟨s, t, abs_pos.mpr ?_⟩
  exact sub_ne_zero.mpr hst.symm

end Quantum

/-! ## General power/phase uncertainty -/

section PowerPhase

open PowerSeries

variable {F : Type*} [Field F]

/-- Power-series coordinate change `X ↦ ζX`, with inverse `X ↦ ζ⁻¹X`. -/
noncomputable def powerSeriesPhaseEquiv (zeta : Fˣ) : F⟦X⟧ ≃+* F⟦X⟧ where
  toFun := PowerSeries.rescale (zeta : F)
  invFun := PowerSeries.rescale (↑zeta⁻¹ : F)
  left_inv f := by
    rw [PowerSeries.rescale_rescale]
    simp [PowerSeries.rescale_one]
  right_inv f := by
    rw [PowerSeries.rescale_rescale]
    simp [PowerSeries.rescale_one]
  map_add' := map_add (PowerSeries.rescale (zeta : F))
  map_mul' := map_mul (PowerSeries.rescale (zeta : F))

/-- The conormal coordinate has phase weight one. -/
@[simp] theorem powerSeriesPhaseEquiv_X (zeta : Fˣ) :
    powerSeriesPhaseEquiv zeta (PowerSeries.X : F⟦X⟧) =
      PowerSeries.C (zeta : F) * PowerSeries.X :=
  PowerSeries.rescale_X (zeta : F)

/-- An `m`-th root phase fixes the `m`-th-power horizon equation exactly. -/
theorem powerSeriesPhaseEquiv_X_pow (zeta : Fˣ) (m : ℕ)
    (hzeta : (zeta : F) ^ m = 1) :
    powerSeriesPhaseEquiv zeta ((PowerSeries.X : F⟦X⟧) ^ m) = PowerSeries.X ^ m := by
  rw [map_pow, powerSeriesPhaseEquiv_X, mul_pow, ← map_pow, hzeta, map_one, one_mul]

/-- A nontrivial phase fixes no nonzero vector in its weight-one line. -/
theorem phase_fixed_vector_eq_zero (zeta x : F) (hzeta : zeta ≠ 1)
    (hfix : zeta * x = x) : x = 0 := by
  have hprod : (zeta - 1) * x = 0 := by
    calc
      (zeta - 1) * x = zeta * x - x := by ring
      _ = 0 := sub_eq_zero.mpr hfix
  exact (mul_eq_zero.mp hprod).resolve_left (sub_ne_zero.mpr hzeta)

end PowerPhase

/-! ## Finite free matrix factorizations of the unsquared horizon -/

section MatrixFactorizationHorizon

open Module PowerSeries

variable {k : Type*} [Field k]

/-- First differential of a matrix factorization as a linear endomorphism of its standard finite
free module. -/
noncomputable def mfD0 {w : k⟦X⟧} (P : MatrixFactorization k⟦X⟧ w) :
    (Fin P.rank → k⟦X⟧) →ₗ[k⟦X⟧] (Fin P.rank → k⟦X⟧) :=
  Matrix.toLin' P.d₀

/-- Second differential of a matrix factorization as a linear endomorphism. -/
noncomputable def mfD1 {w : k⟦X⟧} (P : MatrixFactorization k⟦X⟧ w) :
    (Fin P.rank → k⟦X⟧) →ₗ[k⟦X⟧] (Fin P.rank → k⟦X⟧) :=
  Matrix.toLin' P.d₁

theorem mfD1_mfD0 (P : MatrixFactorization k⟦X⟧ (PowerSeries.X : k⟦X⟧))
    (v : Fin P.rank → k⟦X⟧) :
    mfD1 (k := k) P (mfD0 (k := k) P v) = (PowerSeries.X : k⟦X⟧) • v := by
  change Matrix.toLin' P.d₁ (Matrix.toLin' P.d₀ v) = (PowerSeries.X : k⟦X⟧) • v
  rw [← Matrix.toLin'_mul_apply, P.d₁_mul_d₀]
  simp

theorem mfD0_mfD1 (P : MatrixFactorization k⟦X⟧ (PowerSeries.X : k⟦X⟧))
    (v : Fin P.rank → k⟦X⟧) :
    mfD0 (k := k) P (mfD1 (k := k) P v) = (PowerSeries.X : k⟦X⟧) • v := by
  change Matrix.toLin' P.d₀ (Matrix.toLin' P.d₁ v) = (PowerSeries.X : k⟦X⟧) • v
  rw [← Matrix.toLin'_mul_apply, P.d₀_mul_d₁]
  simp

/-- Multiplication to `X id` by the complementary differential makes the first differential
injective over the power-series domain. -/
theorem mfD0_injective (P : MatrixFactorization k⟦X⟧ (PowerSeries.X : k⟦X⟧)) :
    Function.Injective (mfD0 (k := k) P) := by
  intro v w hvw
  have hcomp := congrArg (mfD1 (k := k) P) hvw
  rw [mfD1_mfD0 (k := k), mfD1_mfD0 (k := k)] at hcomp
  apply funext
  intro j
  apply mul_left_cancel₀ PowerSeries.X_ne_zero
  simpa only [Pi.smul_apply, smul_eq_mul] using congrFun hcomp j

/-- **Smith classification of every finite free factorization of `X`.**  There are bases in which
both differentials are diagonal, with rank-one block coefficients `aᵢ,cᵢ` satisfying
`aᵢcᵢ=X`; irreducibility of `X` forces one coefficient in each block to be a unit.  Thus these
are exactly direct sums of contractible rank-one blocks, before absorbing units into the bases. -/
theorem finite_free_X_factorization_smith_classification
    (P : MatrixFactorization k⟦X⟧ (PowerSeries.X : k⟦X⟧)) :
    ∃ (b₀ b₁ : Basis (Fin P.rank) k⟦X⟧ (Fin P.rank → k⟦X⟧))
      (a c : Fin P.rank → k⟦X⟧),
      (∀ i, mfD0 (k := k) P (b₀ i) = a i • b₁ i) ∧
      (∀ i, mfD1 (k := k) P (b₁ i) = c i • b₀ i) ∧
      (∀ i, a i * c i = (PowerSeries.X : k⟦X⟧)) ∧
      (∀ i, IsUnit (a i) ∨ IsUnit (c i)) := by
  let φ := mfD0 (k := k) P
  let ψ := mfD1 (k := k) P
  let N := LinearMap.range φ
  have hφ : Function.Injective φ := mfD0_injective P
  have hrank : Module.finrank k⟦X⟧ N =
      Module.finrank k⟦X⟧ (Fin P.rank → k⟦X⟧) :=
    LinearMap.finrank_range_of_inj hφ
  obtain ⟨b₁, a, bN, hdiag⟩ :=
    N.exists_smith_normal_form_of_rank_eq
      (Pi.basisFun k⟦X⟧ (Fin P.rank)) hrank
  let eφ : (Fin P.rank → k⟦X⟧) ≃ₗ[k⟦X⟧] N :=
    LinearEquiv.ofInjective φ hφ
  let b₀ : Basis (Fin P.rank) k⟦X⟧ (Fin P.rank → k⟦X⟧) :=
    bN.map eφ.symm
  have hφb₀ (i : Fin P.rank) : φ (b₀ i) = (bN i : Fin P.rank → k⟦X⟧) := by
    change φ (eφ.symm (bN i)) = (bN i : Fin P.rank → k⟦X⟧)
    have h := congrArg Subtype.val (eφ.apply_symm_apply (bN i))
    exact h
  have hphi (i : Fin P.rank) : φ (b₀ i) = a i • b₁ i := by
    rw [hφb₀]
    exact hdiag i
  have ha (i : Fin P.rank) : a i ≠ 0 := by
    intro hai
    apply bN.ne_zero i
    apply Subtype.ext
    simpa [hai] using hdiag i
  have hvector (i : Fin P.rank) : a i • ψ (b₁ i) =
      (PowerSeries.X : k⟦X⟧) • b₀ i := by
    calc
      a i • ψ (b₁ i) = ψ (a i • b₁ i) := by simp
      _ = ψ (φ (b₀ i)) := by rw [hphi]
      _ = (PowerSeries.X : k⟦X⟧) • b₀ i := mfD1_mfD0 (k := k) P (b₀ i)
  let c : Fin P.rank → k⟦X⟧ := fun i ↦ b₀.repr (ψ (b₁ i)) i
  have hprod (i : Fin P.rank) : a i * c i = (PowerSeries.X : k⟦X⟧) := by
    have hcoord := congrArg (fun v ↦ b₀.repr v i) (hvector i)
    simpa [c] using hcoord
  have hpsi (i : Fin P.rank) : ψ (b₁ i) = c i • b₀ i := by
    apply b₀.repr.injective
    ext j
    by_cases hji : j = i
    · subst j
      simp [c]
    · have hcoord := congrArg (fun v ↦ b₀.repr v j) (hvector i)
      have hz : b₀.repr (ψ (b₁ i)) j = 0 := by
        apply (mul_left_cancel₀ (ha i))
        simpa [hji] using hcoord
      simp [c, hji, hz]
  refine ⟨b₀, b₁, a, c, hphi, hpsi, hprod, ?_⟩
  intro i
  exact PowerSeries.X_irreducible.isUnit_or_isUnit (hprod i).symm

/-- Literal odd null-homotopy equations for a two-periodic finite free matrix factorization. -/
def IsLinearlyContractible {w : k⟦X⟧}
    (P : MatrixFactorization k⟦X⟧ w) : Prop :=
  ∃ h₀ h₁ : (Fin P.rank → k⟦X⟧) →ₗ[k⟦X⟧] (Fin P.rank → k⟦X⟧),
    (mfD1 (k := k) P).comp h₀ + h₁.comp (mfD0 (k := k) P) = LinearMap.id ∧
    (mfD0 (k := k) P).comp h₁ + h₀.comp (mfD1 (k := k) P) = LinearMap.id

/-- Every finite free matrix factorization of the unsquared uniformizer `X` is contractible.  The
proof constructs the two odd homotopies blockwise from the Smith classification and verifies both
global contraction identities. -/
theorem finite_free_X_factorization_contractible
    (P : MatrixFactorization k⟦X⟧ (PowerSeries.X : k⟦X⟧)) :
    IsLinearlyContractible P := by
  obtain ⟨b₀, b₁, a, c, hphi, hpsi, hprod, hunit⟩ :=
    finite_free_X_factorization_smith_classification P
  classical
  let u : Fin P.rank → k⟦X⟧ := fun i ↦
    if IsUnit (a i) then 0 else (c i)⁻¹
  let v : Fin P.rank → k⟦X⟧ := fun i ↦
    if IsUnit (a i) then (a i)⁻¹ else 0
  have huv (i : Fin P.rank) : c i * u i + v i * a i = 1 := by
    by_cases ha : IsUnit (a i)
    · have hcc : PowerSeries.constantCoeff (a i) ≠ 0 :=
        (PowerSeries.isUnit_iff_constantCoeff.mp ha).ne_zero
      simp [u, v, ha, PowerSeries.inv_mul_cancel _ hcc]
    · have hc : IsUnit (c i) := (hunit i).resolve_left ha
      have hcc : PowerSeries.constantCoeff (c i) ≠ 0 :=
        (PowerSeries.isUnit_iff_constantCoeff.mp hc).ne_zero
      simp [u, v, ha, PowerSeries.mul_inv_cancel _ hcc]
  let h₀ : (Fin P.rank → k⟦X⟧) →ₗ[k⟦X⟧] (Fin P.rank → k⟦X⟧) :=
    b₀.constr k⟦X⟧ (fun i ↦ u i • b₁ i)
  let h₁ : (Fin P.rank → k⟦X⟧) →ₗ[k⟦X⟧] (Fin P.rank → k⟦X⟧) :=
    b₁.constr k⟦X⟧ (fun i ↦ v i • b₀ i)
  refine ⟨h₀, h₁, ?_, ?_⟩
  · apply b₀.ext
    intro i
    simp only [LinearMap.add_apply, LinearMap.comp_apply, LinearMap.id_apply]
    rw [show h₀ (b₀ i) = u i • b₁ i by simp [h₀], map_smul, hpsi,
      hphi, map_smul, show h₁ (b₁ i) = v i • b₀ i by simp [h₁]]
    rw [smul_smul, smul_smul, ← add_smul, mul_comm (u i), mul_comm (a i), huv, one_smul]
  · apply b₁.ext
    intro i
    simp only [LinearMap.add_apply, LinearMap.comp_apply, LinearMap.id_apply]
    rw [show h₁ (b₁ i) = v i • b₀ i by simp [h₁], map_smul, hphi,
      hpsi, map_smul, show h₀ (b₀ i) = u i • b₁ i by simp [h₀]]
    rw [smul_smul, smul_smul, ← add_smul,
      show v i * a i + c i * u i = c i * u i + v i * a i by ring, huv, one_smul]

/-- Rank-one factorization `(X,X)` of the doubled potential `X²`. -/
noncomputable def squareUniformizerFactorization :
    MatrixFactorization k⟦X⟧ ((PowerSeries.X : k⟦X⟧) ^ 2) where
  rank := 1
  d₀ := (PowerSeries.X : k⟦X⟧) • (1 : Matrix (Fin 1) (Fin 1) k⟦X⟧)
  d₁ := (PowerSeries.X : k⟦X⟧) • (1 : Matrix (Fin 1) (Fin 1) k⟦X⟧)
  d₀_mul_d₁ := by
    ext i j
    fin_cases i
    fin_cases j
    simp [pow_two]
  d₁_mul_d₀ := by
    ext i j
    fin_cases i
    fin_cases j
    simp [pow_two]

@[simp] theorem squareUniformizerFactorization_D0
    (v : Fin 1 → k⟦X⟧) :
    mfD0 (k := k) squareUniformizerFactorization v = (PowerSeries.X : k⟦X⟧) • v := by
  funext i
  fin_cases i
  change Matrix.mulVec
      ((PowerSeries.X : k⟦X⟧) • (1 : Matrix (Fin 1) (Fin 1) k⟦X⟧)) v 0 =
    PowerSeries.X * v 0
  rw [Matrix.smul_mulVec, Matrix.one_mulVec]
  rfl

@[simp] theorem squareUniformizerFactorization_D1
    (v : Fin 1 → k⟦X⟧) :
    mfD1 (k := k) squareUniformizerFactorization v = (PowerSeries.X : k⟦X⟧) • v := by
  funext i
  fin_cases i
  change Matrix.mulVec
      ((PowerSeries.X : k⟦X⟧) • (1 : Matrix (Fin 1) (Fin 1) k⟦X⟧)) v 0 =
    PowerSeries.X * v 0
  rw [Matrix.smul_mulVec, Matrix.one_mulVec]
  rfl

/-- The doubled factorization `(X,X)` is noncontractible: either contraction equation would put
`1` in the ideal `(X)`, contradicted by constant coefficient. -/
theorem squareUniformizerFactorization_noncontractible :
    ¬ IsLinearlyContractible (squareUniformizerFactorization (k := k)) := by
  unfold IsLinearlyContractible
  change ¬ ∃ h₀ h₁ : (Fin 1 → k⟦X⟧) →ₗ[k⟦X⟧] (Fin 1 → k⟦X⟧),
    (Matrix.toLin' ((PowerSeries.X : k⟦X⟧) •
        (1 : Matrix (Fin 1) (Fin 1) k⟦X⟧))).comp h₀ +
        h₁.comp (Matrix.toLin' ((PowerSeries.X : k⟦X⟧) •
          (1 : Matrix (Fin 1) (Fin 1) k⟦X⟧))) = LinearMap.id ∧
      (Matrix.toLin' ((PowerSeries.X : k⟦X⟧) •
        (1 : Matrix (Fin 1) (Fin 1) k⟦X⟧))).comp h₁ +
        h₀.comp (Matrix.toLin' ((PowerSeries.X : k⟦X⟧) •
          (1 : Matrix (Fin 1) (Fin 1) k⟦X⟧))) = LinearMap.id
  rintro ⟨h₀, h₁, hfirst, _⟩
  let e : Fin 1 → k⟦X⟧ := fun _ ↦ 1
  have happ := LinearMap.congr_fun hfirst e
  simp only [LinearMap.add_apply, LinearMap.comp_apply, LinearMap.id_apply] at happ
  rw [show Matrix.toLin' ((PowerSeries.X : k⟦X⟧) •
      (1 : Matrix (Fin 1) (Fin 1) k⟦X⟧)) (h₀ e) =
      PowerSeries.X • h₀ e by exact squareUniformizerFactorization_D1 (h₀ e),
    show Matrix.toLin' ((PowerSeries.X : k⟦X⟧) •
      (1 : Matrix (Fin 1) (Fin 1) k⟦X⟧)) e =
      PowerSeries.X • e by exact squareUniformizerFactorization_D0 e] at happ
  rw [map_smul] at happ
  have hcoord := congrFun happ 0
  have hconstant := congrArg PowerSeries.constantCoeff hcoord
  simp [e] at hconstant

end MatrixFactorizationHorizon

/-! ## Relative Connes-lift obstruction -/

section RelativeConnes

variable {M : Type*} [AddCommGroup M]

/-- A cochain complex, a source-realizable subcomplex, and the Connes comparison/defect pair
`dH = -E`.  The differential and source inclusion are literal data; all cohomology groups below
are constructed as cycle/boundary quotients. -/
structure RelativeConnesDatum (M : Type*) [AddCommGroup M] where
  d : M →ₗ[ℤ] M
  d_sq : ∀ x, d (d x) = 0
  source : Submodule ℤ M
  source_stable : ∀ x, x ∈ source → d x ∈ source
  H : M
  E : M
  E_source : E ∈ source
  differential_H : d H = -E

namespace RelativeConnesDatum

/-- Differential induced on the quotient by source-realizable cochains. -/
noncomputable def quotientDifferential (D : RelativeConnesDatum M) :
    (M ⧸ D.source) →ₗ[ℤ] (M ⧸ D.source) :=
  D.source.mapQ D.source D.d (by
    intro x hx
    exact D.source_stable x hx)

@[simp] theorem quotientDifferential_mk (D : RelativeConnesDatum M) (x : M) :
    D.quotientDifferential (D.source.mkQ x) = D.source.mkQ (D.d x) := by
  exact Submodule.mapQ_apply D.source D.source D.d x

theorem quotientDifferential_sq (D : RelativeConnesDatum M) (x : M ⧸ D.source) :
    D.quotientDifferential (D.quotientDifferential x) = 0 := by
  obtain ⟨x, rfl⟩ := D.source.mkQ_surjective x
  rw [D.quotientDifferential_mk, D.quotientDifferential_mk, D.d_sq, map_zero]

/-- Quotient cycles. -/
noncomputable def quotientCycles (D : RelativeConnesDatum M) :
    Submodule ℤ (M ⧸ D.source) :=
  LinearMap.ker D.quotientDifferential

/-- Quotient coboundary map with codomain restricted to cycles. -/
noncomputable def quotientBoundaryMap (D : RelativeConnesDatum M) :
    (M ⧸ D.source) →ₗ[ℤ] D.quotientCycles where
  toFun x := ⟨D.quotientDifferential x, D.quotientDifferential_sq x⟩
  map_add' x y := by ext; simp
  map_smul' n x := by ext; simp

/-- Quotient coboundaries. -/
noncomputable def quotientBoundaries (D : RelativeConnesDatum M) :
    Submodule ℤ D.quotientCycles :=
  LinearMap.range D.quotientBoundaryMap

/-- Cohomology of the quotient complex `M/A_src`. -/
abbrev QuotientCohomology (D : RelativeConnesDatum M) :=
  D.quotientCycles ⧸ D.quotientBoundaries

theorem quotient_H_closed (D : RelativeConnesDatum M) :
    D.quotientDifferential (D.source.mkQ D.H) = 0 := by
  rw [D.quotientDifferential_mk, D.differential_H, map_neg]
  apply (Submodule.Quotient.mk_eq_zero D.source).2
  exact D.source.neg_mem D.E_source

/-- Quotient cycle represented by the Connes comparison `H`. -/
noncomputable def quotientHCycle (D : RelativeConnesDatum M) : D.quotientCycles :=
  ⟨D.source.mkQ D.H, D.quotient_H_closed⟩

/-- Relative Connes class `[̅H] ∈ H(M/A_src)`. -/
noncomputable def relativeConnesClass (D : RelativeConnesDatum M) :
    D.QuotientCohomology :=
  QuotientAddGroup.mk (s := D.quotientBoundaries.toAddSubgroup) D.quotientHCycle

/-- Differential restricted to source-realizable cochains. -/
noncomputable def sourceDifferential (D : RelativeConnesDatum M) :
    D.source →ₗ[ℤ] D.source where
  toFun x := ⟨D.d x, D.source_stable x x.2⟩
  map_add' x y := by ext; simp
  map_smul' n x := by ext; simp

@[simp] theorem sourceDifferential_apply_coe (D : RelativeConnesDatum M)
    (x : D.source) : (D.sourceDifferential x : M) = D.d x := rfl

theorem sourceDifferential_sq (D : RelativeConnesDatum M) (x : D.source) :
    D.sourceDifferential (D.sourceDifferential x) = 0 := by
  apply Subtype.ext
  exact D.d_sq x

/-- Source cycles. -/
noncomputable def sourceCycles (D : RelativeConnesDatum M) :
    Submodule ℤ D.source :=
  LinearMap.ker D.sourceDifferential

/-- Source coboundary map with codomain restricted to cycles. -/
noncomputable def sourceBoundaryMap (D : RelativeConnesDatum M) :
    D.source →ₗ[ℤ] D.sourceCycles where
  toFun x := ⟨D.sourceDifferential x, D.sourceDifferential_sq x⟩
  map_add' x y := by ext; simp
  map_smul' n x := by ext; simp

/-- Source coboundaries. -/
noncomputable def sourceBoundaries (D : RelativeConnesDatum M) :
    Submodule ℤ D.sourceCycles :=
  LinearMap.range D.sourceBoundaryMap

/-- Cohomology of the source-realizable subcomplex. -/
abbrev SourceCohomology (D : RelativeConnesDatum M) :=
  D.sourceCycles ⧸ D.sourceBoundaries

theorem source_E_closed (D : RelativeConnesDatum M) : D.d D.E = 0 := by
  have h := D.d_sq D.H
  rw [D.differential_H, map_neg] at h
  exact neg_eq_zero.mp h

/-- Source cycle represented by the monodromy defect `E`. -/
noncomputable def sourceDefectCycle (D : RelativeConnesDatum M) : D.sourceCycles :=
  ⟨⟨D.E, D.E_source⟩, by
    apply Subtype.ext
    exact D.source_E_closed⟩

/-- Source cohomology class `[E]`. -/
noncomputable def sourceDefectClass (D : RelativeConnesDatum M) : D.SourceCohomology :=
  QuotientAddGroup.mk (s := D.sourceBoundaries.toAddSubgroup) D.sourceDefectCycle

/-- The connecting representative is the source cochain `dH`. -/
noncomputable def connectingCycle (D : RelativeConnesDatum M) : D.sourceCycles :=
  ⟨⟨D.d D.H, by
      rw [D.differential_H]
      exact D.source.neg_mem D.E_source⟩,
    by
      apply Subtype.ext
      exact D.d_sq D.H⟩

/-- Connecting class represented by `dH`. -/
noncomputable def connectingClass (D : RelativeConnesDatum M) : D.SourceCohomology :=
  QuotientAddGroup.mk (s := D.sourceBoundaries.toAddSubgroup) D.connectingCycle

/-- Exact connecting-morphism law `∂[̅H] = -[E]`. -/
theorem connectingClass_eq_neg_sourceDefectClass (D : RelativeConnesDatum M) :
    D.connectingClass = -D.sourceDefectClass := by
  unfold connectingClass sourceDefectClass
  change QuotientAddGroup.mk (s := D.sourceBoundaries.toAddSubgroup) D.connectingCycle =
    -QuotientAddGroup.mk (s := D.sourceBoundaries.toAddSubgroup) D.sourceDefectCycle
  rw [← QuotientAddGroup.mk_neg]
  apply congrArg (QuotientAddGroup.mk (s := D.sourceBoundaries.toAddSubgroup))
  apply Subtype.ext
  apply Subtype.ext
  exact D.differential_H

/-- If the relative Connes class vanishes, the monodromy defect is a boundary produced inside the
source-realizable subcomplex. -/
theorem sourceDefectClass_eq_zero_of_relativeConnesClass_eq_zero
    (D : RelativeConnesDatum M) (hclass : D.relativeConnesClass = 0) :
    D.sourceDefectClass = 0 := by
  unfold relativeConnesClass at hclass
  have hmem := (QuotientAddGroup.eq_zero_iff _).1 hclass
  rcases hmem with ⟨q, hq⟩
  obtain ⟨K, rfl⟩ := D.source.mkQ_surjective q
  have hquot : D.source.mkQ (D.d K) = D.source.mkQ D.H := by
    have hq' := congrArg Subtype.val hq
    change D.quotientDifferential (D.source.mkQ K) = D.source.mkQ D.H at hq'
    rw [D.quotientDifferential_mk] at hq'
    exact hq'
  have hsource : D.H - D.d K ∈ D.source := by
    apply (Submodule.Quotient.mk_eq_zero D.source).mp
    change D.source.mkQ (D.H - D.d K) = 0
    rw [map_sub, hquot, sub_self]
  let A : D.source := ⟨D.H - D.d K, hsource⟩
  unfold sourceDefectClass
  apply (QuotientAddGroup.eq_zero_iff _).2
  refine ⟨-A, ?_⟩
  apply Subtype.ext
  apply Subtype.ext
  change D.d (-((A : D.source) : M)) = D.E
  simp only [map_neg, A]
  rw [map_sub, D.d_sq, sub_zero, D.differential_H, neg_neg]

end RelativeConnesDatum

end RelativeConnes

/-! ## Reflected positive energy -/

section Energy

variable {F : Type*} [Field F]

/-- Reflected Stokes energy `q + q⁻¹ - 2`. -/
def positiveStokesEnergy (q : F) : F := q + q⁻¹ - 2

/-- Exact doubled-amplitude identity `E(q) = (q-1)²/q`. -/
theorem positiveStokesEnergy_eq_square_div (q : F) (hq : q ≠ 0) :
    positiveStokesEnergy q = (q - 1) ^ 2 / q := by
  unfold positiveStokesEnergy
  field_simp [hq]
  ring

/-- Reflection `q ↦ q⁻¹` acts by `a ↦ -a` modulo `a²` at `q=1+a`. -/
theorem dualNumber_reflection_linearization :
    ((1 + DualNumber.eps : DualNumber F)⁻¹ - 1) = -DualNumber.eps := by
  apply TrivSqZeroExt.ext
  · simp only [TrivSqZeroExt.fst_sub, TrivSqZeroExt.fst_inv,
      TrivSqZeroExt.fst_add, TrivSqZeroExt.fst_one, DualNumber.fst_eps,
      inv_one, add_zero, sub_self, TrivSqZeroExt.fst_neg, neg_zero]
  · simp only [TrivSqZeroExt.snd_sub, TrivSqZeroExt.snd_inv,
      TrivSqZeroExt.fst_add, TrivSqZeroExt.fst_one, DualNumber.fst_eps,
      TrivSqZeroExt.snd_add, TrivSqZeroExt.snd_one, DualNumber.snd_eps,
      inv_one, add_zero, zero_add, op_smul_eq_smul, one_smul, sub_zero,
      TrivSqZeroExt.snd_neg]

end Energy

end GaloisForLFunctions.HTGeometry
