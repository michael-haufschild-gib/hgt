import GaloisForLFunctions.HTGeometry.MultipleGammaDifferenceOperatorAnnihilator

/-!
# Nonnegative exponent coordinates on a face packet

A difference monomial in the directions deleted by a face moves the face coordinate only by
nonnegative integer combinations of those periods.  Coefficient functions on such exponent vectors
therefore describe every iterated difference: a difference in an already deleted direction is the
shift `n ↦ n + e_j` minus the identity, and a difference in a surviving direction deletes that
direction and keeps the coefficients unchanged.

The labelling is faithful — integral independence of the periods separates exponent vectors and
face-packet faithfulness separates their translates — so a nonzero coefficient function carried by
a face retaining two periods synthesizes a hypertranscendental germ.
-/

open Filter Set Topology Function Complex
open scoped Differential BigOperators

namespace GaloisForLFunctions

open Bottcher HTGeometry

noncomputable section

attribute [local instance] facePacketMeroDecidableEq

attribute [local instance] ellipticGammaRationalBaseDomain
  ellipticGammaRationalBaseComplexAlgebraMero ellipticGammaRationalBaseComplexDifferential
  ellipticGammaRationalBaseMeroDifferential ellipticGammaRationalBaseMeroCharZero
  ellipticGammaRationalBaseComplexDifferentialAlgebra
  ellipticGammaRationalBaseCoordinateDifferential
  ellipticGammaRationalBaseCoordinateDifferentialAlgebra

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-! ## Exponent vectors and their shifts -/

/-- The shift attached to a nonnegative exponent vector. -/
def natShift (τ : ι → ℂ) (n : ι →₀ ℕ) : ℂ := ∑ j, (n j : ℂ) * τ j

theorem natShift_add_single (τ : ι → ℂ) (n : ι →₀ ℕ) (j : ι) :
    natShift τ (n + Finsupp.single j 1) = natShift τ n + τ j := by
  classical
  simp only [natShift, Finsupp.add_apply, Finsupp.single_apply]
  have hterm : ∀ x : ι, ((n x + (if j = x then 1 else 0) : ℕ) : ℂ) * τ x =
      (n x : ℂ) * τ x + (if j = x then τ x else 0) := by
    intro x
    split_ifs <;> push_cast <;> ring
  rw [Finset.sum_congr rfl fun x _ => hterm x, Finset.sum_add_distrib]
  congr 1
  simp

omit [DecidableEq ι] in
theorem natShift_mem_faceShiftLattice (τ : ι → ℂ) {S : Finset ι} {n : ι →₀ ℕ}
    (hn : n.support ⊆ S) : natShift τ n ∈ faceShiftLattice τ S := by
  refine ⟨fun i => (n i : ℤ), fun i hi => ?_, ?_⟩
  · have hni : i ∉ n.support := fun h => hi (hn h)
    simp [Finsupp.notMem_support_iff.mp hni]
  · simp [natShift]

omit [DecidableEq ι] in
/-- Integral independence of the periods makes the exponent labelling faithful. -/
theorem natShift_injective (τ : ι → ℂ) (hQ : PeriodsIntegrallyIndependent τ)
    {n m : ι →₀ ℕ} (h : natShift τ n = natShift τ m) : n = m := by
  have hzero : (0 : ℂ) + ∑ i, ((n i : ℤ) - (m i : ℤ) : ℤ) * τ i = 0 := by
    have hsplit : ∑ i, (((n i : ℤ) - (m i : ℤ) : ℤ) : ℂ) * τ i =
        natShift τ n - natShift τ m := by
      rw [natShift, natShift, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun i _ => by push_cast; ring
    rw [zero_add]
    push_cast
    push_cast at hsplit
    rw [hsplit, h, sub_self]
  obtain ⟨-, hcoeff⟩ := hQ 0 (fun i => (n i : ℤ) - (m i : ℤ)) (by exact_mod_cast hzero)
  ext i
  have := hcoeff i
  omega

/-! ## Synthesis from exponent coefficients -/

/-- The face coordinate translated by an exponent vector. -/
def faceTranslate (τ : ι → ℂ) (hτ : ∀ i, 0 < (τ i).im) (S : Finset ι) (n : ι →₀ ℕ) :
    meroField (Set.univ : Set ℂ) :=
  addTranslationMeroEquiv (natShift τ n) (multipleEllipticGammaLogDerivFaceMero τ hτ S)

/-- Synthesis of a finitely supported exponent coefficient function. -/
def natSynth (τ : ι → ℂ) (hτ : ∀ i, 0 < (τ i).im) (S : Finset ι)
    (c : (ι →₀ ℕ) →₀ ℂ) : meroField (Set.univ : Set ℂ) :=
  Finsupp.linearCombination ℂ (faceTranslate τ hτ S) c

theorem natSynth_eq_sum (τ : ι → ℂ) (hτ : ∀ i, 0 < (τ i).im) (S : Finset ι)
    (c : (ι →₀ ℕ) →₀ ℂ) :
    natSynth τ hτ S c =
      ∑ n ∈ c.support,
        algebraMap ℂ (meroField (Set.univ : Set ℂ)) (c n) * faceTranslate τ hτ S n := by
  rw [natSynth, Finsupp.linearCombination_apply, Finsupp.sum]
  exact Finset.sum_congr rfl fun n _ => Algebra.smul_def _ _

theorem natSynth_sub (τ : ι → ℂ) (hτ : ∀ i, 0 < (τ i).im) (S : Finset ι)
    (a b : (ι →₀ ℕ) →₀ ℂ) :
    natSynth τ hτ S (a - b) = natSynth τ hτ S a - natSynth τ hτ S b := by
  rw [natSynth, natSynth, natSynth, map_sub]

theorem natSynth_single_zero (τ : ι → ℂ) (hτ : ∀ i, 0 < (τ i).im) (S : Finset ι) :
    natSynth τ hτ S (Finsupp.single 0 1) =
      multipleEllipticGammaLogDerivFaceMero τ hτ S := by
  rw [natSynth, Finsupp.linearCombination_single, one_smul, faceTranslate]
  have hzero : natShift τ (0 : ι →₀ ℕ) = 0 := by simp [natShift]
  rw [hzero, addTranslationMeroEquiv_zero_apply]

/-! ## Faithfulness and hypertranscendence -/

/-- A coefficient function is *carried by* a face when every occurring exponent is supported on the
deleted directions. -/
def CarriedBy (S : Finset ι) (c : (ι →₀ ℕ) →₀ ℂ) : Prop :=
  ∀ n ∈ c.support, (n : ι →₀ ℕ).support ⊆ S

/-- **A nonzero coefficient function carried by a face retaining two periods synthesizes a
hypertranscendental germ.** -/
theorem hypertranscendentalOver_natSynth (τ : ι → ℂ) (hτ : ∀ i, 0 < (τ i).im)
    (hQ : PeriodsIntegrallyIndependent τ) (hι : 2 ≤ Fintype.card ι)
    (S : Finset ι) (hS : 2 ≤ (Sᶜ).card)
    {c : (ι →₀ ℕ) →₀ ℂ} (hcarry : CarriedBy S c) (hc : c ≠ 0) :
    HypertranscendentalOver ℂ (natSynth τ hτ S c) := by
  classical
  have hmem : ∀ k : (c.support : Finset (ι →₀ ℕ)),
      faceTranslate τ hτ S (k : ι →₀ ℕ) ∈
        facePacketUnion τ hτ {L : Finset ι | 2 ≤ (Lᶜ).card} := by
    intro k
    exact Set.mem_iUnion₂.mpr ⟨S, hS,
      ⟨natShift τ (k : ι →₀ ℕ),
        natShift_mem_faceShiftLattice τ (hcarry (k : ι →₀ ℕ) k.2), rfl⟩⟩
  have hinj : Function.Injective
      (fun k : (c.support : Finset (ι →₀ ℕ)) => faceTranslate τ hτ S (k : ι →₀ ℕ)) := by
    intro a b hab
    have hshift := faceShiftLattice_translate_injective τ hτ hQ S hS
      (natShift_mem_faceShiftLattice τ (hcarry (a : ι →₀ ℕ) a.2))
      (natShift_mem_faceShiftLattice τ (hcarry (b : ι →₀ ℕ) b.2)) hab
    exact Subtype.ext (natShift_injective τ hQ hshift)
  have hindep : DifferentialIndependent ℂ
      (fun k : (c.support : Finset (ι →₀ ℕ)) => faceTranslate τ hτ S (k : ι →₀ ℕ)) :=
    multipleEllipticGammaSelectedFaces_differentialIndependent τ hτ hQ hι _ hmem hinj
  have hcne : (fun k : (c.support : Finset (ι →₀ ℕ)) => c (k : ι →₀ ℕ)) ≠ 0 := by
    obtain ⟨n₀, hn₀⟩ := Finsupp.support_nonempty_iff.mpr hc
    intro hzero
    exact (Finsupp.mem_support_iff.mp hn₀) (congrFun hzero ⟨n₀, hn₀⟩)
  have hsum := hypertranscendentalOver_linearCombination_of_ne_zero
    (C := ℂ) (K := meroField (Set.univ : Set ℂ))
    meroField_deriv_algebraMap_complex_rationalBase _ hcne _ hindep
  have hval : ∑ k : (c.support : Finset (ι →₀ ℕ)),
        algebraMap ℂ (meroField (Set.univ : Set ℂ)) (c (k : ι →₀ ℕ)) *
          faceTranslate τ hτ S (k : ι →₀ ℕ) = natSynth τ hτ S c := by
    rw [natSynth_eq_sum, ← Finset.sum_coe_sort c.support]
  rwa [hval] at hsum

/-! ## The two structural steps -/

/-- Exponent increment in one direction. -/
def monomialExpShift (j : ι) (n : ι →₀ ℕ) : ι →₀ ℕ := n + Finsupp.single j 1

omit [Fintype ι] [DecidableEq ι] in
theorem monomialExpShift_injective (j : ι) : Function.Injective (monomialExpShift (ι := ι) j) :=
  fun _ _ hab => add_right_cancel hab

theorem faceTranslate_monomialExpShift (τ : ι → ℂ) (hτ : ∀ i, 0 < (τ i).im) (S : Finset ι)
    (j : ι) (n : ι →₀ ℕ) :
    faceTranslate τ hτ S (monomialExpShift j n) =
      addTranslationMeroEquiv (τ j) (faceTranslate τ hτ S n) := by
  rw [faceTranslate, faceTranslate, addTranslationMeroEquiv_add, monomialExpShift,
    natShift_add_single, add_comm]

/-- **Face-preserving step.**  A difference in an already deleted direction is the exponent shift
minus the identity on coefficients. -/
theorem meroShiftDiff_natSynth (τ : ι → ℂ) (hτ : ∀ i, 0 < (τ i).im) (S : Finset ι)
    (j : ι) (c : (ι →₀ ℕ) →₀ ℂ) :
    meroShiftDiff (τ j) (natSynth τ hτ S c) =
      natSynth τ hτ S (Finsupp.mapDomain (monomialExpShift j) c - c) := by
  classical
  have hsupp : (Finsupp.mapDomain (monomialExpShift j) c).support = c.support.image (monomialExpShift j) :=
    Finsupp.mapDomain_support_of_injective (monomialExpShift_injective j) c
  have htrans : addTranslationMeroEquiv (τ j) (natSynth τ hτ S c) =
      natSynth τ hτ S (Finsupp.mapDomain (monomialExpShift j) c) := by
    rw [natSynth_eq_sum, natSynth_eq_sum, hsupp, map_sum,
      Finset.sum_image fun a _ b _ h => monomialExpShift_injective j h]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [map_mul, addTranslationMeroEquiv_algebraMap_complex,
      Finsupp.mapDomain_apply (monomialExpShift_injective j), faceTranslate_monomialExpShift]
  rw [meroShiftDiff, natSynth_sub, htrans]

/-- **Face-growing step.**  A difference in a surviving direction deletes that direction and leaves
the coefficients unchanged. -/
theorem meroShiftDiff_natSynth_notMem (τ : ι → ℂ) (hτ : ∀ i, 0 < (τ i).im) (S : Finset ι)
    {j : ι} (hj : j ∉ S) (c : (ι →₀ ℕ) →₀ ℂ) :
    meroShiftDiff (τ j) (natSynth τ hτ S c) = natSynth τ hτ (insert j S) c := by
  classical
  rw [meroShiftDiff, natSynth_eq_sum, natSynth_eq_sum, map_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [map_mul, addTranslationMeroEquiv_algebraMap_complex, ← mul_sub]
  congr 1
  exact facePacket_coface τ hτ S hj (natShift τ n)

/-! ## Carriers propagate through both steps -/

omit [Fintype ι] [DecidableEq ι] in
theorem carriedBy_mono {S T : Finset ι} (hST : S ⊆ T) {c : (ι →₀ ℕ) →₀ ℂ}
    (hc : CarriedBy S c) : CarriedBy T c := fun n hn => (hc n hn).trans hST

omit [Fintype ι] in
theorem carriedBy_mapDomain_monomialExpShift {S : Finset ι} {j : ι} (hj : j ∈ S)
    {c : (ι →₀ ℕ) →₀ ℂ} (hc : CarriedBy S c) :
    CarriedBy S (Finsupp.mapDomain (monomialExpShift j) c - c) := by
  classical
  intro n hn
  rcases Finset.mem_union.mp (Finsupp.support_sub hn) with h | h
  · rw [Finsupp.mapDomain_support_of_injective (monomialExpShift_injective j)] at h
    obtain ⟨m, hm, rfl⟩ := Finset.mem_image.mp h
    intro i hi
    rcases Finset.mem_union.mp (Finsupp.support_add hi) with h' | h'
    · exact hc m hm h'
    · have := Finsupp.support_single_subset h'
      rw [Finset.mem_singleton] at this
      exact this ▸ hj
  · exact hc n h

omit [Fintype ι] in
/-- The zero-exponent coefficient is carried by every face. -/
theorem carriedBy_single_zero (S : Finset ι) :
    CarriedBy S (Finsupp.single (0 : ι →₀ ℕ) (1 : ℂ)) := by
  classical
  intro n hn
  have : n = 0 := by
    by_contra hne
    simp [Finsupp.support_single, hne] at hn
  simp [this]

/-! ## The coefficient of an iterated difference along a list -/

/-- The coefficient function produced by an iterated difference along a list of directions. -/
def listCoeff : List ι → ((ι →₀ ℕ) →₀ ℂ)
  | [] => Finsupp.single 0 1
  | j :: l =>
      if j ∈ l.toFinset then Finsupp.mapDomain (monomialExpShift j) (listCoeff l) - listCoeff l
      else listCoeff l

/-- The accumulated top exponent of an iterated difference along a list. -/
def listTop : List ι → (ι →₀ ℕ)
  | [] => 0
  | j :: l => if j ∈ l.toFinset then monomialExpShift j (listTop l) else listTop l

theorem listShiftDiff_eq_natSynth (τ : ι → ℂ) (hτ : ∀ i, 0 < (τ i).im) :
    ∀ l : List ι,
      listShiftDiff τ l (multipleEllipticGammaLogDerivMero τ hτ) =
        natSynth τ hτ l.toFinset (listCoeff l) := by
  classical
  intro l
  induction l with
  | nil =>
      rw [listShiftDiff_nil, List.toFinset_nil, listCoeff, natSynth_single_zero,
        multipleEllipticGammaLogDerivFaceMero_empty]
  | cons j l ih =>
      rw [listShiftDiff_cons, ih, List.toFinset_cons, listCoeff]
      by_cases hj : j ∈ l.toFinset
      · rw [if_pos hj, Finset.insert_eq_self.mpr hj, meroShiftDiff_natSynth]
      · rw [if_neg hj, meroShiftDiff_natSynth_notMem τ hτ l.toFinset hj]

omit [Fintype ι] in
theorem carriedBy_listCoeff : ∀ l : List ι, CarriedBy l.toFinset (listCoeff l) := by
  classical
  intro l
  induction l with
  | nil => rw [List.toFinset_nil, listCoeff]; exact carriedBy_single_zero ∅
  | cons j l ih =>
      rw [List.toFinset_cons, listCoeff]
      by_cases hj : j ∈ l.toFinset
      · rw [if_pos hj, Finset.insert_eq_self.mpr hj]
        exact carriedBy_mapDomain_monomialExpShift hj ih
      · rw [if_neg hj]
        exact carriedBy_mono (Finset.subset_insert j l.toFinset) ih

omit [Fintype ι] in
theorem listCoeff_support_le :
    ∀ (l : List ι) {n : ι →₀ ℕ}, n ∈ (listCoeff l).support → n ≤ listTop l := by
  classical
  intro l
  induction l with
  | nil =>
      intro n hn
      have hn0 : n = 0 := by
        by_contra hne
        simp [listCoeff, Finsupp.support_single, hne] at hn
      rw [hn0, listTop]
  | cons j l ih =>
      intro n hn
      rw [listCoeff] at hn
      rw [listTop]
      by_cases hj : j ∈ l.toFinset
      · rw [if_pos hj] at hn ⊢
        rcases Finset.mem_union.mp (Finsupp.support_sub hn) with h | h
        · rw [Finsupp.mapDomain_support_of_injective (monomialExpShift_injective j)] at h
          obtain ⟨m, hm, rfl⟩ := Finset.mem_image.mp h
          refine Finsupp.le_def.mpr fun i => ?_
          have hmi := Finsupp.le_def.mp (ih hm) i
          simp only [monomialExpShift, Finsupp.add_apply]
          omega
        · refine Finsupp.le_def.mpr fun i => ?_
          have hni := Finsupp.le_def.mp (ih h) i
          simp only [monomialExpShift, Finsupp.add_apply]
          omega
      · rw [if_neg hj] at hn ⊢
        exact ih hn

omit [Fintype ι] in
theorem listCoeff_top : ∀ l : List ι, listCoeff l (listTop l) = 1 := by
  classical
  intro l
  induction l with
  | nil => simp [listCoeff, listTop]
  | cons j l ih =>
      rw [listCoeff, listTop]
      by_cases hj : j ∈ l.toFinset
      · rw [if_pos hj, if_pos hj]
        have hnotmem : monomialExpShift j (listTop l) ∉ (listCoeff l).support := by
          intro hmem
          have hjle := Finsupp.le_def.mp (listCoeff_support_le l hmem) j
          simp only [monomialExpShift, Finsupp.add_apply, Finsupp.single_eq_same] at hjle
          omega
        rw [Finsupp.sub_apply, Finsupp.mapDomain_apply (monomialExpShift_injective j),
          Finsupp.notMem_support_iff.mp hnotmem, ih, sub_zero]
      · rw [if_neg hj, if_neg hj]
        exact ih

/-! ## Independence of iterated differences with distinct tops -/

omit [DecidableEq ι] in
theorem natExp_eq_of_le_of_degree_le {a b : ι →₀ ℕ}
    (hle : a ≤ b) (hdeg : ∑ i, b i ≤ ∑ i, a i) : a = b := by
  have hsum : ∑ i, a i = ∑ i, b i :=
    le_antisymm (Finset.sum_le_sum fun i _ => Finsupp.le_def.mp hle i) hdeg
  exact Finsupp.ext fun i =>
    (Finset.sum_eq_sum_iff_of_le (fun i _ => Finsupp.le_def.mp hle i)).mp hsum i
      (Finset.mem_univ i)

/-- **Distinct tops give independent iterated differences.**  A combination whose maximal-degree
term carries a nonzero scalar has a nonzero coefficient function. -/
theorem listCoeff_combination_ne_zero {κ : Type} [Fintype κ] [DecidableEq κ]
    (l : κ → List ι) (a : κ → ℂ)
    (htop : Function.Injective fun k => listTop (l k))
    {k₀ : κ} (hk₀ : a k₀ ≠ 0)
    (hmax : ∀ k, a k ≠ 0 → ∑ i, (listTop (l k)) i ≤ ∑ i, (listTop (l k₀)) i) :
    ∑ k, a k • listCoeff (l k) ≠ 0 := by
  classical
  intro hzero
  have hval := congrArg (fun c : (ι →₀ ℕ) →₀ ℂ => c (listTop (l k₀))) hzero
  simp only [Finsupp.coe_finsetSum, Finset.sum_apply, Finsupp.coe_smul, Pi.smul_apply,
    smul_eq_mul, Finsupp.coe_zero, Pi.zero_apply] at hval
  have hterm : ∀ k ∈ Finset.univ, k ≠ k₀ →
      a k * listCoeff (l k) (listTop (l k₀)) = 0 := by
    intro k _ hk
    by_cases hak : a k = 0
    · simp [hak]
    by_cases hsupp : listTop (l k₀) ∈ (listCoeff (l k)).support
    · exact absurd (htop (natExp_eq_of_le_of_degree_le
        (listCoeff_support_le (l k) hsupp) (hmax k hak)).symm) hk
    · simp [Finsupp.notMem_support_iff.mp hsupp]
  rw [Finset.sum_eq_single k₀ hterm (fun h => absurd (Finset.mem_univ k₀) h),
    listCoeff_top] at hval
  exact hk₀ (by simpa using hval)

/-! ## The top of a multidegree list -/

omit [Fintype ι] in
theorem count_flatMap (a : ι) (L : List ι) (f : ι → List ι) :
    (L.flatMap f).count a = (L.map fun x => (f x).count a).sum := by
  induction L with
  | nil => simp
  | cons b L ih => rw [List.flatMap_cons, List.count_append, ih, List.map_cons, List.sum_cons]

omit [Fintype ι] in
theorem count_multiDegreeList (d : ι →₀ ℕ) (a : ι) : (multiDegreeList d).count a = d a := by
  classical
  rw [multiDegreeList, count_flatMap]
  rw [Finset.sum_map_toList d.support (fun x => (List.replicate (d x) x).count a)]
  have hterm : ∀ x ∈ d.support, (List.replicate (d x) x).count a = if x = a then d x else 0 := by
    intro x _
    simp [List.count_replicate]
  rw [Finset.sum_congr rfl hterm, Finset.sum_ite_eq' d.support a]
  by_cases ha : a ∈ d.support
  · rw [if_pos ha]
  · rw [if_neg ha, Finsupp.notMem_support_iff.mp ha]

omit [Fintype ι] in
theorem listTop_apply : ∀ (l : List ι) (i : ι), listTop l i = l.count i - 1 := by
  classical
  intro l
  induction l with
  | nil => simp [listTop]
  | cons j l ih =>
      intro i
      rw [listTop]
      by_cases hj : j ∈ l.toFinset
      · rw [if_pos hj]
        by_cases hij : i = j
        · subst hij
          have hcount : 1 ≤ l.count i := by
            have := List.mem_toFinset.mp hj
            exact List.one_le_count_iff.mpr this
          have hval : (monomialExpShift i (listTop l)) i = listTop l i + 1 := by
            simp [monomialExpShift, Finsupp.add_apply]
          rw [hval, ih i, List.count_cons_self]
          omega
        · have hval : (monomialExpShift j (listTop l)) i = listTop l i := by
            simp [monomialExpShift, Finsupp.add_apply, Ne.symm hij]
          rw [hval, ih i, List.count_cons_of_ne (Ne.symm hij)]
      · rw [if_neg hj]
        by_cases hij : i = j
        · subst hij
          have hcount : l.count i = 0 := by
            rw [List.count_eq_zero]
            exact fun h => hj (List.mem_toFinset.mpr h)
          rw [ih i, hcount, List.count_cons_self, hcount]
        · rw [ih i, List.count_cons_of_ne (Ne.symm hij)]

omit [Fintype ι] in
theorem listTop_multiDegreeList_apply (d : ι →₀ ℕ) (i : ι) :
    listTop (multiDegreeList d) i = d i - 1 := by
  rw [listTop_apply, count_multiDegreeList]

theorem sum_listTop_multiDegreeList (d : ι →₀ ℕ) :
    (∑ i, listTop (multiDegreeList d) i) + d.support.card = ∑ i, d i := by
  classical
  have hpt : ∀ i, listTop (multiDegreeList d) i = d i - 1 :=
    listTop_multiDegreeList_apply d
  rw [Finset.sum_congr rfl fun i _ => hpt i]
  have hoff : ∀ i ∈ (Finset.univ : Finset ι), i ∉ d.support → d i - 1 = 0 := by
    intro i _ hi
    simp [Finsupp.notMem_support_iff.mp hi]
  have hoff' : ∀ i ∈ (Finset.univ : Finset ι), i ∉ d.support → d i = 0 := by
    intro i _ hi
    exact Finsupp.notMem_support_iff.mp hi
  rw [← Finset.sum_subset (Finset.subset_univ d.support) hoff,
    ← Finset.sum_subset (Finset.subset_univ d.support) hoff',
    Finset.card_eq_sum_ones, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i hi => ?_
  have hd1 : 1 ≤ d i := Nat.one_le_iff_ne_zero.mpr (Finsupp.mem_support_iff.mp hi)
  omega

/-! ## Independence of monomials with a common support -/

/-- **A nonzero combination of difference monomials with a common deep support is
hypertranscendental.** -/
theorem hypertranscendentalOver_sum_xMonomialApply_of_common_support
    (τ : ι → ℂ) (hτ : ∀ i, 0 < (τ i).im)
    (hQ : PeriodsIntegrallyIndependent τ) (hι : 2 ≤ Fintype.card ι)
    (S : Finset ι) (hS : 2 ≤ (Sᶜ).card)
    {κ : Type} [Fintype κ] [DecidableEq κ]
    (d : κ → (ι →₀ ℕ)) (hd : ∀ k, (d k).support = S) (hdinj : Function.Injective d)
    (a : κ → ℂ) {k₀ : κ} (hk₀ : a k₀ ≠ 0)
    (hmax : ∀ k, a k ≠ 0 → ∑ i, (d k) i ≤ ∑ i, (d k₀) i) :
    HypertranscendentalOver ℂ
      (∑ k, algebraMap ℂ (meroField (Set.univ : Set ℂ)) (a k) *
        xMonomialApply τ (d k) (multipleEllipticGammaLogDerivMero τ hτ)) := by
  classical
  have hface : ∀ k, (multiDegreeList (d k)).toFinset = S := fun k => by
    rw [multiDegreeList_toFinset, hd k]
  have hval : ∀ k, xMonomialApply τ (d k) (multipleEllipticGammaLogDerivMero τ hτ) =
      natSynth τ hτ S (listCoeff (multiDegreeList (d k))) := by
    intro k
    rw [xMonomialApply, listShiftDiff_eq_natSynth τ hτ, hface k]
  have hsum : ∑ k, algebraMap ℂ (meroField (Set.univ : Set ℂ)) (a k) *
      xMonomialApply τ (d k) (multipleEllipticGammaLogDerivMero τ hτ) =
      natSynth τ hτ S (∑ k, a k • listCoeff (multiDegreeList (d k))) := by
    rw [natSynth, map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [map_smul, hval k, natSynth, Algebra.smul_def]
  -- distinct tops
  have htopinj : Function.Injective fun k => listTop (multiDegreeList (d k)) := by
    intro k k' hkk'
    refine hdinj (Finsupp.ext fun i => ?_)
    have hi := congrArg (fun n : ι →₀ ℕ => n i) hkk'
    simp only [listTop_multiDegreeList_apply] at hi
    by_cases hiS : i ∈ S
    · have h1 : 1 ≤ (d k) i := Nat.one_le_iff_ne_zero.mpr
        (Finsupp.mem_support_iff.mp (by rw [hd k]; exact hiS))
      have h2 : 1 ≤ (d k') i := Nat.one_le_iff_ne_zero.mpr
        (Finsupp.mem_support_iff.mp (by rw [hd k']; exact hiS))
      omega
    · have h1 : (d k) i = 0 := Finsupp.notMem_support_iff.mp (by rw [hd k]; exact hiS)
      have h2 : (d k') i = 0 := Finsupp.notMem_support_iff.mp (by rw [hd k']; exact hiS)
      rw [h1, h2]
  have hmaxtop : ∀ k, a k ≠ 0 →
      ∑ i, listTop (multiDegreeList (d k)) i ≤
        ∑ i, listTop (multiDegreeList (d k₀)) i := by
    intro k hak
    have h1 := sum_listTop_multiDegreeList (d k)
    have h2 := sum_listTop_multiDegreeList (d k₀)
    rw [hd k] at h1
    rw [hd k₀] at h2
    have := hmax k hak
    omega
  have hne : (∑ k, a k • listCoeff (multiDegreeList (d k))) ≠ 0 :=
    listCoeff_combination_ne_zero (fun k => multiDegreeList (d k)) a htopinj hk₀ hmaxtop
  have hcarry : CarriedBy S (∑ k, a k • listCoeff (multiDegreeList (d k))) := by
    intro n hn
    have hsub := Finsupp.support_finsetSum (s := (Finset.univ : Finset κ))
      (f := fun k => a k • listCoeff (multiDegreeList (d k))) hn
    obtain ⟨k, -, hk⟩ := Finset.mem_biUnion.mp hsub
    have hk' : n ∈ (listCoeff (multiDegreeList (d k))).support := Finsupp.support_smul hk
    have hcar := carriedBy_listCoeff (multiDegreeList (d k)) n hk'
    rwa [hface k] at hcar
  rw [hsum]
  exact hypertranscendentalOver_natSynth τ hτ hQ hι S hS hcarry hne

end

end GaloisForLFunctions
