import GaloisForLFunctions.HTGeometry.MultipleEllipticGammaFaceHierarchy
import GaloisForLFunctions.HTGeometry.FacePacketDisplacementFreeness
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


/-! ## Faces: restriction of the period independence and the surviving cardinality -/

theorem linearIndependent_augmentedPeriods_face {ι : Type} [Fintype ι] [DecidableEq ι]
    (τ : ι → ℂ) (hind : LinearIndependent ℚ (augmentedPeriods τ)) (J : Finset ι) :
    LinearIndependent ℚ (augmentedPeriods (multipleEllipticGammaFaceParameters τ J)) := by
  have hf : Function.Injective (Option.map (Subtype.val : {i : ι // i ∉ J} → ι)) :=
    Option.map_injective Subtype.val_injective
  have hcomp : (augmentedPeriods τ) ∘ (Option.map (Subtype.val : {i : ι // i ∉ J} → ι))
      = augmentedPeriods (multipleEllipticGammaFaceParameters τ J) := by
    funext i
    cases i with
    | none => rfl
    | some x => rfl
  have hres := hind.comp _ hf
  rwa [hcomp] at hres

theorem card_not_mem_eq {ι : Type} [Fintype ι] [DecidableEq ι] (J : Finset ι) :
    Fintype.card {i : ι // i ∉ J} = Fintype.card ι - J.card := by
  have h1 : Fintype.card {i : ι // i ∈ J} = J.card := by simp
  have h2 := Fintype.card_subtype_compl (fun i : ι => i ∈ J)
  omega

theorem card_not_mem_insert {ι : Type} [Fintype ι] [DecidableEq ι] (J : Finset ι) {q : ι}
    (hq : q ∉ J) :
    Fintype.card {i : ι // i ∉ insert q J} + 1 = Fintype.card {i : ι // i ∉ J} := by
  have hJ : J.card ≤ Fintype.card ι := Finset.card_le_univ J
  have hins : (insert q J).card = J.card + 1 := Finset.card_insert_of_notMem hq
  have hle : (insert q J).card ≤ Fintype.card ι := Finset.card_le_univ _
  rw [card_not_mem_eq, card_not_mem_eq, hins] at *
  omega

/-! ## The order-two spectrum collapse -/

/-- **Order-two collapse on a face.**  If exactly three structural periods survive a face and the
augmented period family is `ℚ`-independent, then a differentially algebraic translation defect of
the face coordinate forces the shift to be an integer. -/
theorem exists_int_of_da_faceDefect_card_three {ι : Type} [Fintype ι] [DecidableEq ι]
    (τ : ι → ℂ) (hτ : ∀ i, 0 < (τ i).im)
    (hind : LinearIndependent ℚ (augmentedPeriods τ)) (J : Finset ι)
    (hcard : Fintype.card {i : ι // i ∉ J} = 3) {h : ℂ}
    (hDA : DifferentialAlgebraicOver (RatFunc ℂ)
      (meroTranslationDefect h (multipleEllipticGammaLogDerivFaceMero τ hτ J))) :
    ∃ n : ℤ, h = (n : ℂ) := by
  classical
  have hne : Nonempty {i : ι // i ∉ J} := Fintype.card_pos_iff.mp (by omega)
  obtain ⟨q₀⟩ := hne
  refine exists_int_of_forall_memDeletedPeriodGroup (q₀ := q₀)
    (multipleEllipticGammaFaceParameters τ J)
    (linearIndependent_augmentedPeriods_face τ hind J) ?_
  intro q
  have hDAface : DifferentialAlgebraicOver (RatFunc ℂ)
      (meroTranslationDefect h
        (multipleEllipticGammaLogDerivFaceMero τ hτ (insert (q : ι) J))) := by
    rw [← meroTranslationDefect_face τ hτ J q.2 h]
    exact differentialAlgebraicOver_meroTranslationDefect (τ (q : ι)) hDA
  have hsub : Fintype.card {i : ι // i ∉ insert (q : ι) J} = 2 := by
    have hstep := card_not_mem_insert J q.2
    omega
  obtain ⟨e⟩ : Nonempty ({i : ι // i ∉ insert (q : ι) J} ≃ Fin 2) :=
    ⟨Fintype.equivFinOfCardEq hsub⟩
  set j : ι := (e.symm 0 : ι) with hjdef
  set k : ι := (e.symm 1 : ι) with hkdef
  have hjmem : j ∉ insert (q : ι) J := (e.symm 0).2
  have hkmem : k ∉ insert (q : ι) J := (e.symm 1).2
  have hjJ : j ∉ J := fun hc => hjmem (Finset.mem_insert_of_mem hc)
  have hkJ : k ∉ J := fun hc => hkmem (Finset.mem_insert_of_mem hc)
  have hjq : j ≠ (q : ι) := fun hc => hjmem (by rw [hc]; exact Finset.mem_insert_self _ _)
  have hkq : k ≠ (q : ι) := fun hc => hkmem (by rw [hc]; exact Finset.mem_insert_self _ _)
  have hjk : j ≠ k := by
    intro hcon
    have hsub2 : e.symm 0 = e.symm 1 := Subtype.ext hcon
    have := e.symm.injective hsub2
    exact absurd this (by decide)
  have hjpos : 0 < (τ j).im := hτ j
  have hkpos : 0 < (τ k).im := hτ k
  have hreindex : multipleEllipticGammaLogDerivFaceMero τ hτ (insert (q : ι) J)
      = multipleEllipticGammaLogDerivMero ![τ j, τ k]
        (by
          intro i
          fin_cases i
          · exact hjpos
          · exact hkpos) := by
    have hface : multipleEllipticGammaLogDerivFaceMero τ hτ (insert (q : ι) J)
        = multipleEllipticGammaLogDerivMero
            (multipleEllipticGammaFaceParameters τ (insert (q : ι) J)) (fun i => hτ i) := rfl
    rw [hface]
    have hre := multipleEllipticGammaLogDerivMero_reindex e.symm
      (multipleEllipticGammaFaceParameters τ (insert (q : ι) J)) (fun i => hτ i)
    rw [← hre]
    congr 1
    funext i
    fin_cases i <;> rfl
  rw [hreindex] at hDAface
  obtain ⟨a, b, n, hval⟩ := exists_int_of_da_defect_fin_two (τ j) (τ k) hjpos hkpos
    (linearIndependent_ellipticGammaSourcePeriods_of_augmented τ hind hjk) _ hDAface
  set jκ : {i : ι // i ∉ J} := ⟨j, hjJ⟩ with hjκ
  set kκ : {i : ι // i ∉ J} := ⟨k, hkJ⟩ with hkκ
  have hjκq : jκ ≠ q := fun hc => hjq (congrArg Subtype.val hc)
  have hkκq : kκ ≠ q := fun hc => hkq (congrArg Subtype.val hc)
  have hjκk : jκ ≠ kκ := by
    simp only [hjκ, hkκ, ne_eq, Subtype.mk.injEq]
    exact hjk
  refine ⟨a, Function.update (Function.update (fun _ : {i : ι // i ∉ J} => (0 : ℤ)) jκ n) kκ b,
    ?_, ?_⟩
  · rw [Function.update_of_ne (Ne.symm hkκq), Function.update_of_ne (Ne.symm hjκq)]
  · rw [hval]
    have hsum : ∑ i : {i : ι // i ∉ J},
        ((Function.update (Function.update (fun _ : {i : ι // i ∉ J} => (0 : ℤ)) jκ n) kκ b i :
            ℤ) : ℂ) * multipleEllipticGammaFaceParameters τ J i
        = (n : ℂ) * τ j + (b : ℂ) * τ k := by
      rw [Finset.sum_eq_add_of_mem jκ kκ (Finset.mem_univ jκ) (Finset.mem_univ kκ) hjκk ?_]
      · rw [Function.update_of_ne hjκk, Function.update_self, Function.update_self]
        rfl
      · intro c _ hc
        rw [Function.update_of_ne hc.2, Function.update_of_ne hc.1]
        simp
    rw [hsum]
    ring

/-! ## The generic all-order spectrum -/

/-- **The generic multiple-elliptic-gamma translation spectrum, upper half.**  Whenever at least
three structural periods survive the face, a differentially algebraic translation defect forces
the shift to be an integer. -/
theorem exists_int_of_da_faceDefect {ι : Type} [Fintype ι] [DecidableEq ι]
    (τ : ι → ℂ) (hτ : ∀ i, 0 < (τ i).im)
    (hind : LinearIndependent ℚ (augmentedPeriods τ)) :
    ∀ (m : ℕ), 3 ≤ m → ∀ (J : Finset ι), Fintype.card {i : ι // i ∉ J} = m →
      ∀ {h : ℂ}, DifferentialAlgebraicOver (RatFunc ℂ)
        (meroTranslationDefect h (multipleEllipticGammaLogDerivFaceMero τ hτ J)) →
      ∃ n : ℤ, h = (n : ℂ) := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro hm J hJ h hDA
    rcases eq_or_lt_of_le hm with hm3 | hm4
    · exact exists_int_of_da_faceDefect_card_three τ hτ hind J (by omega) hDA
    · have hne : Nonempty {i : ι // i ∉ J} := Fintype.card_pos_iff.mp (by omega)
      obtain ⟨q⟩ := hne
      have hDAface : DifferentialAlgebraicOver (RatFunc ℂ)
          (meroTranslationDefect h
            (multipleEllipticGammaLogDerivFaceMero τ hτ (insert (q : ι) J))) := by
        rw [← meroTranslationDefect_face τ hτ J q.2 h]
        exact differentialAlgebraicOver_meroTranslationDefect (τ (q : ι)) hDA
      have hcard := card_not_mem_insert J q.2
      exact ih (m - 1) (by omega) (by omega) (insert (q : ι) J) (by omega) hDAface

/-- **Integer shifts are in the spectrum.**  Every integer translation fixes the face
coordinate, so its defect vanishes and is trivially differentially algebraic. -/
theorem differentialAlgebraicOver_meroTranslationDefect_intCast {ι : Type} [Fintype ι]
    [DecidableEq ι] (τ : ι → ℂ) (hτ : ∀ i, 0 < (τ i).im) (J : Finset ι) (n : ℤ) :
    DifferentialAlgebraicOver (RatFunc ℂ)
      (meroTranslationDefect (n : ℂ) (multipleEllipticGammaLogDerivFaceMero τ hτ J)) := by
  have hfix := addTranslationMeroEquiv_intCast_multipleEllipticGammaLogDerivFaceMero τ hτ J n
  have hzero : meroTranslationDefect (n : ℂ) (multipleEllipticGammaLogDerivFaceMero τ hτ J)
      = 0 := by
    rw [meroTranslationDefect, hfix, sub_self]
  rw [hzero]
  have h0 : (0 : meroField (Set.univ : Set ℂ)) = algebraMap (RatFunc ℂ) _ 0 := by simp
  rw [h0]
  exact HTGeometry.differentialAlgebraicOver_algebraMap _

/-- **The exact generic spectrum.**  With at least three surviving `ℚ`-independent structural
periods, the differentially algebraic translation spectrum of the multiple elliptic gamma
logarithmic derivative is exactly `ℤ`. -/
theorem da_meroTranslationDefect_iff_int {ι : Type} [Fintype ι] [DecidableEq ι]
    (τ : ι → ℂ) (hτ : ∀ i, 0 < (τ i).im)
    (hind : LinearIndependent ℚ (augmentedPeriods τ)) (J : Finset ι)
    (hcard : 3 ≤ Fintype.card {i : ι // i ∉ J}) (h : ℂ) :
    DifferentialAlgebraicOver (RatFunc ℂ)
        (meroTranslationDefect h (multipleEllipticGammaLogDerivFaceMero τ hτ J))
      ↔ ∃ n : ℤ, h = (n : ℂ) := by
  constructor
  · intro hDA
    exact exists_int_of_da_faceDefect τ hτ hind (Fintype.card {i : ι // i ∉ J}) hcard J rfl hDA
  · rintro ⟨n, rfl⟩
    exact differentialAlgebraicOver_meroTranslationDefect_intCast τ hτ J n

/-- The empty face is the full hierarchy coordinate. -/
theorem multipleEllipticGammaLogDerivFaceMero_empty {ι : Type} [Fintype ι] [DecidableEq ι]
    (τ : ι → ℂ) (hτ : ∀ i, 0 < (τ i).im) :
    multipleEllipticGammaLogDerivFaceMero τ hτ ∅ = multipleEllipticGammaLogDerivMero τ hτ := by
  let e : {i : ι // i ∉ (∅ : Finset ι)} ≃ ι :=
    { toFun := fun i => i.1
      invFun := fun i => ⟨i, by simp⟩
      left_inv := fun i => rfl
      right_inv := fun i => rfl }
  have hre := multipleEllipticGammaLogDerivMero_reindex e τ hτ
  rw [← hre]
  unfold multipleEllipticGammaLogDerivFaceMero
  congr 1
  funext k

/-- **The exact generic spectrum of the multiple elliptic gamma logarithmic derivative.**
For at least three `ℚ`-independent structural periods,

```text
Spec_DA(Ψ_r) = { h : Δ_h Ψ_r is differentially algebraic over ℂ(z) } = ℤ .
```
-/
theorem da_meroTranslationDefect_multipleEllipticGamma_iff_int {ι : Type} [Fintype ι]
    [DecidableEq ι] (τ : ι → ℂ) (hτ : ∀ i, 0 < (τ i).im)
    (hind : LinearIndependent ℚ (augmentedPeriods τ)) (hcard : 3 ≤ Fintype.card ι) (h : ℂ) :
    DifferentialAlgebraicOver (RatFunc ℂ)
        (meroTranslationDefect h (multipleEllipticGammaLogDerivMero τ hτ))
      ↔ ∃ n : ℤ, h = (n : ℂ) := by
  have hface : Fintype.card {i : ι // i ∉ (∅ : Finset ι)} = Fintype.card ι := by
    rw [card_not_mem_eq]
    simp
  have := da_meroTranslationDefect_iff_int τ hτ hind ∅ (by omega) h
  rwa [multipleEllipticGammaLogDerivFaceMero_empty] at this

/-- **Every nonintegral translation defect is hypertranscendental.** -/
theorem hypertranscendentalOver_meroTranslationDefect_of_not_int {ι : Type} [Fintype ι]
    [DecidableEq ι] (τ : ι → ℂ) (hτ : ∀ i, 0 < (τ i).im)
    (hind : LinearIndependent ℚ (augmentedPeriods τ)) (hcard : 3 ≤ Fintype.card ι) {h : ℂ}
    (hnot : ¬ ∃ n : ℤ, h = (n : ℂ)) :
    HypertranscendentalOver (RatFunc ℂ)
      (meroTranslationDefect h (multipleEllipticGammaLogDerivMero τ hτ)) := by
  intro hDA
  exact hnot ((da_meroTranslationDefect_multipleEllipticGamma_iff_int τ hτ hind hcard h).mp hDA)

/-- **The logarithmic derivative is hypertranscendental.**  Its translation spectrum is a proper
subgroup of `ℂ`, so it cannot itself be differentially algebraic. -/
theorem hypertranscendentalOver_multipleEllipticGammaLogDerivMero_of_card {ι : Type} [Fintype ι]
    [DecidableEq ι] (τ : ι → ℂ) (hτ : ∀ i, 0 < (τ i).im)
    (hind : LinearIndependent ℚ (augmentedPeriods τ)) (hcard : 3 ≤ Fintype.card ι) :
    HypertranscendentalOver (RatFunc ℂ) (multipleEllipticGammaLogDerivMero τ hτ) := by
  intro hDA
  have hne : Nonempty ι := Fintype.card_pos_iff.mp (by omega)
  obtain ⟨i₀⟩ := hne
  have hnot : ¬ ∃ n : ℤ, τ i₀ = (n : ℂ) := by
    rintro ⟨n, hn⟩
    have hzero : (τ i₀).im = 0 := by rw [hn]; simp
    have := hτ i₀
    rw [hzero] at this
    exact lt_irrefl 0 this
  exact hypertranscendentalOver_meroTranslationDefect_of_not_int τ hτ hind hcard hnot
    (differentialAlgebraicOver_meroTranslationDefect (τ i₀) hDA)

end

end GaloisForLFunctions
