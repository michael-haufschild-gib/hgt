import GaloisForLFunctions.HTGeometry.MultipleEllipticGammaFaceHierarchy
import GaloisForLFunctions.HTGeometry.MultipleEllipticGammaHypertranscendence
import GaloisForLFunctions.HTGeometry.EllipticGammaTranslationAnomalyRationalBase
import GaloisForLFunctions.HTGeometry.TranslationStableDifferentialAlgebraicity
import GaloisForLFunctions.HTGeometry.FiniteDifferentialCircuitBoundary

/-!
# The generic multiple-elliptic-gamma translation spectrum

For a family of periods `τ : ι → ℂ` whose augmentation `1, τ_0, …, τ_r` is `ℚ`-linearly
independent, the integer period groups obtained by deleting one coordinate intersect in `ℤ`:

```text
⋂_q ( ℤ + ∑_{k ≠ q} ℤ τ_k ) = ℤ .
```

This is the arithmetic heart of the generic spectrum collapse: at order two the three rank-three
order-one spectra obtained by deleting one parameter intersect only in the integers, and the same
computation propagates through every higher order.

The analytic half is supplied by the corpus: the all-order coface equation
`multipleEllipticGammaLogDerivFaceMero_addTranslation_sub` turns a translation defect of the face
coordinate into the face coordinate of the enlarged face, and differential algebraicity is stable
under translation and subtraction.
-/

open Filter Set Topology Function Complex
open scoped Differential

namespace GaloisForLFunctions

open Bottcher HTGeometry

noncomputable section

attribute [local instance] relativeGaugeDomain relativeGaugeDifferential
  relativeGaugeRatFuncAlgebra relativeGaugeRatFuncDifferential relativeGaugeDifferentialAlgebra
  relativeGaugeCharZeroBase relativeGaugeCharZero relativeGaugeComplexAlgebra
  relativeGaugeComplexAlgebraAnalytic

attribute [local instance] meromorphicEllipticCompositumComplexAlgebraMero

/-! ## The deleted-coordinate period intersection -/

/-- The augmented period family `1, τ_0, …, τ_r`. -/
def augmentedPeriods {ι : Type*} (τ : ι → ℂ) : Option ι → ℂ
  | none => 1
  | some i => τ i

@[simp] theorem augmentedPeriods_none {ι : Type*} (τ : ι → ℂ) :
    augmentedPeriods τ none = 1 := rfl

@[simp] theorem augmentedPeriods_some {ι : Type*} (τ : ι → ℂ) (i : ι) :
    augmentedPeriods τ (some i) = τ i := rfl

/-- Membership in the integer period group obtained by deleting the coordinate `q`. -/
def MemDeletedPeriodGroup {ι : Type*} [Fintype ι] (τ : ι → ℂ) (q : ι) (h : ℂ) : Prop :=
  ∃ (a : ℤ) (b : ι → ℤ), b q = 0 ∧ h = (a : ℂ) + ∑ k, (b k : ℂ) * τ k

/-- **The deleted-coordinate period groups intersect in the integers.** -/
theorem exists_int_of_forall_memDeletedPeriodGroup {ι : Type*} [Fintype ι] [DecidableEq ι]
    (τ : ι → ℂ) (hind : LinearIndependent ℚ (augmentedPeriods τ))
    {q₀ : ι} {h : ℂ} (hmem : ∀ q, MemDeletedPeriodGroup τ q h) :
    ∃ n : ℤ, h = (n : ℂ) := by
  obtain ⟨a, b, hbq, hh⟩ := hmem q₀
  have hcoeff : ∀ j : ι, b j = 0 := by
    intro j
    by_cases hjq : j = q₀
    · rw [hjq]; exact hbq
    · obtain ⟨a2, b2, hb2j, hh2⟩ := hmem j
      have hthis := hh.symm.trans hh2
      have hrel : ((a : ℂ) - (a2 : ℂ)) + ∑ k, ((b k : ℂ) - (b2 k : ℂ)) * τ k = 0 := by
        have hsplit : ∑ k, ((b k : ℂ) - (b2 k : ℂ)) * τ k
            = (∑ k, (b k : ℂ) * τ k) - ∑ k, (b2 k : ℂ) * τ k := by
          rw [← Finset.sum_sub_distrib]
          exact Finset.sum_congr rfl fun k _ => by ring
        rw [hsplit]
        linear_combination hthis
      set g : Option ι → ℚ := fun i =>
        Option.rec ((a : ℚ) - (a2 : ℚ)) (fun k => ((b k : ℚ) - (b2 k : ℚ))) i with hg
      have hgsum : ∑ i : Option ι, g i • augmentedPeriods τ i = 0 := by
        rw [Fintype.sum_option]
        simp only [hg, augmentedPeriods_none, augmentedPeriods_some]
        simp only [Rat.smul_def]
        push_cast
        linear_combination hrel
      have hall := (Fintype.linearIndependent_iff.mp hind) g hgsum
      have hj := hall (some j)
      simp only [hg] at hj
      have hbjQ : (b j : ℚ) = (b2 j : ℚ) := by linarith [hj]
      have hbj : b j = b2 j := by exact_mod_cast hbjQ
      rw [hbj, hb2j]
  refine ⟨a, ?_⟩
  rw [hh]
  simp only [hcoeff, Int.cast_zero, zero_mul, Finset.sum_const_zero, add_zero]

/-! ## Translation defects on the meromorphic field -/

/-- The translation defect `Δ_h x = x(· + h) − x`. -/
def meroTranslationDefect (h : ℂ) (x : meroField (Set.univ : Set ℂ)) :
    meroField (Set.univ : Set ℂ) :=
  addTranslationMeroEquiv h x - x

theorem meroTranslationDefect_comm (a b : ℂ) (x : meroField (Set.univ : Set ℂ)) :
    meroTranslationDefect a (meroTranslationDefect b x)
      = meroTranslationDefect b (meroTranslationDefect a x) := by
  simp only [meroTranslationDefect, map_sub, addTranslationMeroEquiv_add]
  rw [add_comm a b]
  ring

theorem differentialAlgebraicOver_meroTranslationDefect (a : ℂ)
    {x : meroField (Set.univ : Set ℂ)}
    (hx : DifferentialAlgebraicOver (RatFunc ℂ) x) :
    DifferentialAlgebraicOver (RatFunc ℂ) (meroTranslationDefect a x) :=
  differentialAlgebraicOver_sub
    (HTGeometry.differentialAlgebraicOver_addTranslationMeroEquiv a hx) hx

/-- Descending one structural direction through a translation defect deletes that parameter. -/
theorem meroTranslationDefect_face {ι : Type} [Fintype ι] [DecidableEq ι]
    (τ : ι → ℂ) (hτ : ∀ i, 0 < (τ i).im)
    (J : Finset ι) {q : ι} (hq : q ∉ J) (h : ℂ) :
    meroTranslationDefect (τ q)
        (meroTranslationDefect h (multipleEllipticGammaLogDerivFaceMero τ hτ J))
      = meroTranslationDefect h (multipleEllipticGammaLogDerivFaceMero τ hτ (insert q J)) := by
  rw [meroTranslationDefect_comm]
  congr 1
  exact multipleEllipticGammaLogDerivFaceMero_addTranslation_sub τ hτ J q hq

theorem meroTranslationDefect_addTranslation (c h : ℂ) (y : meroField (Set.univ : Set ℂ)) :
    meroTranslationDefect h (addTranslationMeroEquiv c y)
      = addTranslationMeroEquiv c (meroTranslationDefect h y) := by
  simp only [meroTranslationDefect, map_sub, addTranslationMeroEquiv_add]
  rw [add_comm h c]

theorem differentialAlgebraicOver_addTranslation_iff (c : ℂ)
    {x : meroField (Set.univ : Set ℂ)} :
    DifferentialAlgebraicOver (RatFunc ℂ) (addTranslationMeroEquiv c x)
      ↔ DifferentialAlgebraicOver (RatFunc ℂ) x := by
  constructor
  · intro hx
    have h := HTGeometry.differentialAlgebraicOver_addTranslationMeroEquiv (-c) hx
    rwa [addTranslationMeroEquiv_add, neg_add_cancel, addTranslationMeroEquiv_zero_apply] at h
  · exact HTGeometry.differentialAlgebraicOver_addTranslationMeroEquiv c

/-! ## The order-one bridge -/

/-- **Order-one bridge.**  A differentially algebraic translation defect of the two-parameter
multiple elliptic gamma logarithmic derivative forces the shift into the rank-three period
group. -/
theorem exists_int_of_da_defect_fin_two
    (σ τ' : ℂ) (hσ : 0 < σ.im) (hτ' : 0 < τ'.im)
    (hind : LinearIndependent ℚ (ellipticGammaSourcePeriods σ τ'))
    (hpos : ∀ i, 0 < ((![σ, τ'] : Fin 2 → ℂ) i).im) {h : ℂ}
    (hDA : DifferentialAlgebraicOver (RatFunc ℂ)
      (meroTranslationDefect h (multipleEllipticGammaLogDerivMero ![σ, τ'] hpos))) :
    ∃ a b n : ℤ, h = (a : ℂ) + (b : ℂ) * τ' + (n : ℂ) * σ := by
  have hval : multipleEllipticGammaLogDerivMero ![σ, τ'] hpos
      = addTranslationMeroEquiv (-(1 + τ') / 2) (ellipticGammaLogDerivMero σ τ' hσ hτ') :=
    multipleEllipticGammaLogDerivMero_fin_two σ τ' hσ hτ'
  rw [hval, meroTranslationDefect_addTranslation,
    differentialAlgebraicOver_addTranslation_iff] at hDA
  have hdef : meroTranslationDefect h (ellipticGammaLogDerivMero σ τ' hσ hτ')
      = ellipticGammaExternalLogDerivDefectMero h σ τ' hσ hτ' := rfl
  rw [hdef] at hDA
  exact (differentialAlgebraicOver_ellipticGammaExternalLogDerivDefectMero_iff_resonant
    h σ τ' hσ hτ' hind).mp (differentialAlgebraicOver_compositum_of_ratFunc hDA)


theorem linearIndependent_ellipticGammaSourcePeriods_of_augmented {ι : Type*} (τ : ι → ℂ)
    (hind : LinearIndependent ℚ (augmentedPeriods τ)) {j k : ι} (hjk : j ≠ k) :
    LinearIndependent ℚ (ellipticGammaSourcePeriods (τ j) (τ k)) := by
  have hf : Function.Injective (fun i : Fin 3 => (![none, some j, some k] : Fin 3 → Option ι) i) := by
    intro a b hab
    fin_cases a <;> fin_cases b <;> simp_all
  have hcomp : (augmentedPeriods τ) ∘ (fun i : Fin 3 => (![none, some j, some k] : Fin 3 → Option ι) i)
      = ellipticGammaSourcePeriods (τ j) (τ k) := by
    funext i
    fin_cases i <;> rfl
  have := hind.comp _ hf
  rwa [hcomp] at this

/-! ## The order-two spectrum collapse -/

/-- **Order-two collapse.**  With three `ℚ`-independent structural periods, a differentially
algebraic translation defect of the multiple elliptic gamma logarithmic derivative forces the shift
to be an integer. -/
theorem exists_int_of_da_faceDefect_card_three {ι : Type} [Fintype ι] [DecidableEq ι]
    (τ : ι → ℂ) (hτ : ∀ i, 0 < (τ i).im)
    (hind : LinearIndependent ℚ (augmentedPeriods τ)) (hcard : Fintype.card ι = 3)
    {h : ℂ}
    (hDA : DifferentialAlgebraicOver (RatFunc ℂ)
      (meroTranslationDefect h (multipleEllipticGammaLogDerivFaceMero τ hτ ∅))) :
    ∃ n : ℤ, h = (n : ℂ) := by
  have hne : Nonempty ι := Fintype.card_pos_iff.mp (by omega)
  obtain ⟨q₀⟩ := hne
  refine exists_int_of_forall_memDeletedPeriodGroup (q₀ := q₀) τ hind ?_
  intro q
  -- the face `{q}` leaves two parameters
  have hDAface : DifferentialAlgebraicOver (RatFunc ℂ)
      (meroTranslationDefect h (multipleEllipticGammaLogDerivFaceMero τ hτ {q})) := by
    have hstep := meroTranslationDefect_face τ hτ ∅ (q := q) (by simp) h
    rw [show insert q (∅ : Finset ι) = ({q} : Finset ι) by simp] at hstep
    rw [← hstep]
    exact differentialAlgebraicOver_meroTranslationDefect (τ q) hDA
  -- identify the surviving two-element parameter family
  have hsub : Fintype.card {i : ι // i ∉ ({q} : Finset ι)} = 2 := by
    have hcompl : Fintype.card {i : ι // i ∈ ({q} : Finset ι)} = 1 := by
      simp
    have := Fintype.card_subtype_compl (fun i : ι => i ∈ ({q} : Finset ι))
    omega
  obtain ⟨e⟩ : Nonempty ({i : ι // i ∉ ({q} : Finset ι)} ≃ Fin 2) :=
    ⟨Fintype.equivFinOfCardEq hsub⟩
  set j : ι := (e.symm 0 : ι) with hj
  set k : ι := (e.symm 1 : ι) with hk
  have hjq : j ≠ q := by
    have := (e.symm 0).2
    simpa [hj] using this
  have hkq : k ≠ q := by
    have := (e.symm 1).2
    simpa [hk] using this
  have hjk : j ≠ k := by
    intro hcon
    have : e.symm 0 = e.symm 1 := Subtype.ext hcon
    have := e.symm.injective this
    exact absurd this (by decide)
  have hjpos : 0 < (τ j).im := hτ j
  have hkpos : 0 < (τ k).im := hτ k
  -- rewrite the face coordinate as the two-parameter object
  have hreindex : multipleEllipticGammaLogDerivFaceMero τ hτ {q}
      = multipleEllipticGammaLogDerivMero ![τ j, τ k]
        (by
          intro i
          fin_cases i
          · exact hjpos
          · exact hkpos) := by
    have hface : multipleEllipticGammaLogDerivFaceMero τ hτ {q}
        = multipleEllipticGammaLogDerivMero
            (multipleEllipticGammaFaceParameters τ {q}) (fun i => hτ i) := rfl
    rw [hface]
    have hre := multipleEllipticGammaLogDerivMero_reindex e.symm
      (multipleEllipticGammaFaceParameters τ ({q} : Finset ι)) (fun i => hτ i)
    rw [← hre]
    congr 1
    funext i
    fin_cases i <;> rfl
  rw [hreindex] at hDAface
  obtain ⟨a, b, n, hval⟩ := exists_int_of_da_defect_fin_two (τ j) (τ k) hjpos hkpos
    (linearIndependent_ellipticGammaSourcePeriods_of_augmented τ hind hjk) _ hDAface
  -- package as a deleted period group membership
  classical
  refine ⟨a, Function.update (Function.update (fun _ : ι => (0 : ℤ)) j n) k b, ?_, ?_⟩
  · rw [Function.update_of_ne (Ne.symm hkq), Function.update_of_ne (Ne.symm hjq)]
  · rw [hval]
    have hsum : ∑ i : ι,
        ((Function.update (Function.update (fun _ : ι => (0 : ℤ)) j n) k b i : ℤ) : ℂ) * τ i
        = (n : ℂ) * τ j + (b : ℂ) * τ k := by
      rw [Finset.sum_eq_add_of_mem j k (Finset.mem_univ j) (Finset.mem_univ k) hjk ?_]
      · rw [Function.update_of_ne hjk, Function.update_self, Function.update_self]
      · intro c _ hc
        rw [Function.update_of_ne hc.2, Function.update_of_ne hc.1]
        simp
    rw [hsum]
    ring

end

end GaloisForLFunctions
