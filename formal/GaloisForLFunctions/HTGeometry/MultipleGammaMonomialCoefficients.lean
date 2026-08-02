import GaloisForLFunctions.HTGeometry.MultipleGammaDifferenceOperatorAnnihilator

/-!
# Nonnegative exponent coordinates on a face packet

A difference monomial in the directions deleted by a face moves the face coordinate only by
nonnegative integer combinations of those periods.  Indexing the packet by such exponent vectors
turns the structural difference in a deleted direction into the shift `n ↦ n + e_j` minus the
identity on finitely supported coefficient functions.

The indexing is faithful: integral independence of the periods makes distinct exponent vectors give
distinct shifts, and face-packet faithfulness makes distinct shifts give distinct germs.  Hence a
nonzero coefficient function synthesizes a hypertranscendental germ.
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

/-! ## Exponent vectors supported on a face -/

/-- Nonnegative exponent vectors supported on the deleted directions of a face. -/
def NatExp (S : Finset ι) : Type := {n : ι →₀ ℕ // n.support ⊆ S}

instance (S : Finset ι) : DecidableEq (NatExp S) := fun a b =>
  decidable_of_iff (a.1 = b.1) Subtype.ext_iff.symm

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
  · have : i ∉ n.support := fun h => hi (hn h)
    simp [Finsupp.notMem_support_iff.mp this]
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

/-! ## The packet in exponent coordinates -/

/-- The face coordinate translated by an exponent vector. -/
def natPacket (τ : ι → ℂ) (hτ : ∀ i, 0 < (τ i).im) (S : Finset ι) (n : NatExp S) :
    meroField (Set.univ : Set ℂ) :=
  addTranslationMeroEquiv (natShift τ n.1) (multipleEllipticGammaLogDerivFaceMero τ hτ S)

theorem natPacket_mem (τ : ι → ℂ) (hτ : ∀ i, 0 < (τ i).im) (S : Finset ι)
    (hS : 2 ≤ (Sᶜ).card) (n : NatExp S) :
    natPacket τ hτ S n ∈ facePacketUnion τ hτ {L : Finset ι | 2 ≤ (Lᶜ).card} :=
  Set.mem_iUnion₂.mpr ⟨S, hS, ⟨natShift τ n.1, natShift_mem_faceShiftLattice τ n.2, rfl⟩⟩

theorem natPacket_injective (τ : ι → ℂ) (hτ : ∀ i, 0 < (τ i).im)
    (hQ : PeriodsIntegrallyIndependent τ) (S : Finset ι) (hS : 2 ≤ (Sᶜ).card) :
    Function.Injective (natPacket τ hτ S) := by
  intro n m hnm
  have hshift := faceShiftLattice_translate_injective τ hτ hQ S hS
    (natShift_mem_faceShiftLattice τ n.2) (natShift_mem_faceShiftLattice τ m.2) hnm
  exact Subtype.ext (natShift_injective τ hQ hshift)

theorem natPacket_differentialIndependent (τ : ι → ℂ) (hτ : ∀ i, 0 < (τ i).im)
    (hQ : PeriodsIntegrallyIndependent τ) (hι : 2 ≤ Fintype.card ι)
    (S : Finset ι) (hS : 2 ≤ (Sᶜ).card) :
    DifferentialIndependent ℂ (natPacket τ hτ S) :=
  multipleEllipticGammaSelectedFaces_differentialIndependent τ hτ hQ hι _
    (natPacket_mem τ hτ S hS) (natPacket_injective τ hτ hQ S hS)

/-! ## Synthesis from exponent coefficients -/

/-- Synthesis of a finitely supported exponent coefficient function. -/
def natSynth (τ : ι → ℂ) (hτ : ∀ i, 0 < (τ i).im) (S : Finset ι)
    (c : NatExp S →₀ ℂ) : meroField (Set.univ : Set ℂ) :=
  Finsupp.linearCombination ℂ (natPacket τ hτ S) c

theorem natSynth_eq_sum (τ : ι → ℂ) (hτ : ∀ i, 0 < (τ i).im) (S : Finset ι)
    (c : NatExp S →₀ ℂ) :
    natSynth τ hτ S c =
      ∑ n ∈ c.support,
        algebraMap ℂ (meroField (Set.univ : Set ℂ)) (c n) * natPacket τ hτ S n := by
  rw [natSynth, Finsupp.linearCombination_apply, Finsupp.sum]
  exact Finset.sum_congr rfl fun n _ => Algebra.smul_def _ _

theorem natSynth_sub (τ : ι → ℂ) (hτ : ∀ i, 0 < (τ i).im) (S : Finset ι)
    (a b : NatExp S →₀ ℂ) :
    natSynth τ hτ S (a - b) = natSynth τ hτ S a - natSynth τ hτ S b := by
  rw [natSynth, natSynth, natSynth, map_sub]

/-- **A nonzero exponent coefficient function synthesizes a hypertranscendental germ.** -/
theorem hypertranscendentalOver_natSynth (τ : ι → ℂ) (hτ : ∀ i, 0 < (τ i).im)
    (hQ : PeriodsIntegrallyIndependent τ) (hι : 2 ≤ Fintype.card ι)
    (S : Finset ι) (hS : 2 ≤ (Sᶜ).card) {c : NatExp S →₀ ℂ} (hc : c ≠ 0) :
    HypertranscendentalOver ℂ (natSynth τ hτ S c) := by
  classical
  have hindep : DifferentialIndependent ℂ
      (fun k : (c.support : Finset (NatExp S)) => natPacket τ hτ S (k : NatExp S)) :=
    (natPacket_differentialIndependent τ hτ hQ hι S hS).comp
      (fun k : (c.support : Finset (NatExp S)) => (k : NatExp S))
      (fun a b hab => Subtype.ext hab)
  have hcne : (fun k : (c.support : Finset (NatExp S)) => c (k : NatExp S)) ≠ 0 := by
    obtain ⟨n₀, hn₀⟩ := Finsupp.support_nonempty_iff.mpr hc
    intro hzero
    exact (Finsupp.mem_support_iff.mp hn₀) (congrFun hzero ⟨n₀, hn₀⟩)
  have hsum := hypertranscendentalOver_linearCombination_of_ne_zero
    (C := ℂ) (K := meroField (Set.univ : Set ℂ))
    meroField_deriv_algebraMap_complex_rationalBase _ hcne _ hindep
  have hval : ∑ k : (c.support : Finset (NatExp S)),
        algebraMap ℂ (meroField (Set.univ : Set ℂ)) (c (k : NatExp S)) *
          natPacket τ hτ S (k : NatExp S) = natSynth τ hτ S c := by
    rw [natSynth_eq_sum, ← Finset.sum_coe_sort c.support]
  rwa [hval] at hsum

theorem natSynth_ne_zero (τ : ι → ℂ) (hτ : ∀ i, 0 < (τ i).im)
    (hQ : PeriodsIntegrallyIndependent τ) (hι : 2 ≤ Fintype.card ι)
    (S : Finset ι) (hS : 2 ≤ (Sᶜ).card) {c : NatExp S →₀ ℂ} (hc : c ≠ 0) :
    natSynth τ hτ S c ≠ 0 := by
  intro hzero
  refine hypertranscendentalOver_natSynth τ hτ hQ hι S hS hc ?_
  rw [hzero]
  exact differentialAlgebraicOver_zero

/-! ## The shift operator in exponent coordinates -/

/-- Increment an exponent vector in a deleted direction. -/
def natExpShift (S : Finset ι) {j : ι} (hj : j ∈ S) (n : NatExp S) : NatExp S :=
  ⟨n.1 + Finsupp.single j 1, by
    intro i hi
    rcases Finset.mem_union.mp (Finsupp.support_add hi) with h | h
    · exact n.2 h
    · have hji : i = j := by
        have := Finsupp.support_single_subset h
        simpa using this
      exact hji ▸ hj⟩

omit [Fintype ι] in
theorem natExpShift_injective (S : Finset ι) {j : ι} (hj : j ∈ S) :
    Function.Injective (natExpShift S hj) := by
  intro a b hab
  have h := congrArg Subtype.val hab
  exact Subtype.ext (add_right_cancel h)

theorem natPacket_natExpShift (τ : ι → ℂ) (hτ : ∀ i, 0 < (τ i).im) (S : Finset ι)
    {j : ι} (hj : j ∈ S) (n : NatExp S) :
    natPacket τ hτ S (natExpShift S hj n) =
      addTranslationMeroEquiv (τ j) (natPacket τ hτ S n) := by
  have hshift : natShift τ (natExpShift S hj n).1 = τ j + natShift τ n.1 := by
    show natShift τ (n.1 + Finsupp.single j 1) = τ j + natShift τ n.1
    rw [natShift_add_single, add_comm]
  rw [natPacket, natPacket, addTranslationMeroEquiv_add, hshift]

theorem natSynth_translate (τ : ι → ℂ) (hτ : ∀ i, 0 < (τ i).im) (S : Finset ι)
    {j : ι} (hj : j ∈ S) (c : NatExp S →₀ ℂ) :
    addTranslationMeroEquiv (τ j) (natSynth τ hτ S c) =
      natSynth τ hτ S (Finsupp.mapDomain (natExpShift S hj) c) := by
  classical
  have hsupp : (Finsupp.mapDomain (natExpShift S hj) c).support =
      c.support.image (natExpShift S hj) :=
    Finsupp.mapDomain_support_of_injective (natExpShift_injective S hj) c
  rw [natSynth_eq_sum, natSynth_eq_sum, hsupp, map_sum,
    Finset.sum_image fun a _ b _ h => natExpShift_injective S hj h]
  refine Finset.sum_congr rfl fun n hn => ?_
  rw [map_mul, addTranslationMeroEquiv_algebraMap_complex,
    Finsupp.mapDomain_apply (natExpShift_injective S hj), natPacket_natExpShift]

/-! ## Iterated differences in exponent coordinates -/

/-- The coefficient action of an iterated difference along deleted directions. -/
def natShiftDiffCoeff (S : Finset ι) :
    List {j : ι // j ∈ S} → (NatExp S →₀ ℂ) → (NatExp S →₀ ℂ)
  | [], c => c
  | j :: l, c =>
      Finsupp.mapDomain (natExpShift S j.2) (natShiftDiffCoeff S l c) - natShiftDiffCoeff S l c

theorem listShiftDiff_natSynth (τ : ι → ℂ) (hτ : ∀ i, 0 < (τ i).im) (S : Finset ι)
    (l : List {j : ι // j ∈ S}) (c : NatExp S →₀ ℂ) :
    listShiftDiff τ (l.map Subtype.val) (natSynth τ hτ S c) =
      natSynth τ hτ S (natShiftDiffCoeff S l c) := by
  induction l with
  | nil => rfl
  | cons j l ih =>
      rw [List.map_cons, listShiftDiff_cons, ih, meroShiftDiff, natShiftDiffCoeff,
        natSynth_sub, natSynth_translate τ hτ S j.2]

/-! ## Box and top invariants of an iterated difference -/

/-- The zero exponent vector. -/
def natExpZero (S : Finset ι) : NatExp S := ⟨0, by simp⟩

/-- The accumulated exponent reached by an iterated difference. -/
def natExpTop (S : Finset ι) : List {j : ι // j ∈ S} → NatExp S
  | [] => natExpZero S
  | j :: l => natExpShift S j.2 (natExpTop S l)

/-- The coefficient function of an iterated difference applied to the face coordinate. -/
def natMonomialCoeff (S : Finset ι) (l : List {j : ι // j ∈ S}) : NatExp S →₀ ℂ :=
  natShiftDiffCoeff S l (Finsupp.single (natExpZero S) 1)

omit [Fintype ι] in
theorem natMonomialCoeff_support_le (S : Finset ι) :
    ∀ (l : List {j : ι // j ∈ S}) {n : NatExp S},
      n ∈ (natMonomialCoeff S l).support → n.1 ≤ (natExpTop S l).1 := by
  classical
  intro l
  induction l with
  | nil =>
      intro n hn
      rw [natMonomialCoeff, natShiftDiffCoeff] at hn
      have hn0 : n = natExpZero S := by
        by_contra hne
        simp [Finsupp.support_single, hne] at hn
      rw [hn0]
      exact le_refl _
  | cons j l ih =>
      intro n hn
      have hn' : n ∈ (Finsupp.mapDomain (natExpShift S j.2) (natMonomialCoeff S l)
          - natMonomialCoeff S l).support := hn
      rcases Finset.mem_union.mp (Finsupp.support_sub hn') with h | h
      · rw [Finsupp.mapDomain_support_of_injective (natExpShift_injective S j.2)] at h
        obtain ⟨m, hm, rfl⟩ := Finset.mem_image.mp h
        have hmle := Finsupp.le_def.mp (ih hm)
        refine Finsupp.le_def.mpr fun i => ?_
        have hmi := hmle i
        simp only [natExpShift, natExpTop, Finsupp.add_apply]
        omega
      · have hnle := Finsupp.le_def.mp (ih h)
        refine Finsupp.le_def.mpr fun i => ?_
        have hni := hnle i
        simp only [natExpShift, natExpTop, Finsupp.add_apply]
        omega

omit [Fintype ι] in
theorem natMonomialCoeff_top (S : Finset ι) :
    ∀ l : List {j : ι // j ∈ S}, natMonomialCoeff S l (natExpTop S l) = 1 := by
  classical
  intro l
  induction l with
  | nil => simp [natMonomialCoeff, natShiftDiffCoeff, natExpTop]
  | cons j l ih =>
      have hnotmem : natExpShift S j.2 (natExpTop S l) ∉ (natMonomialCoeff S l).support := by
        intro hmem
        have hj := Finsupp.le_def.mp (natMonomialCoeff_support_le S l hmem) j.1
        simp only [natExpShift, Finsupp.add_apply, Finsupp.single_eq_same] at hj
        omega
      have hstep : natMonomialCoeff S (j :: l) (natExpTop S (j :: l)) =
          natMonomialCoeff S l (natExpTop S l) -
            natMonomialCoeff S l (natExpShift S j.2 (natExpTop S l)) := by
        show (Finsupp.mapDomain (natExpShift S j.2) (natMonomialCoeff S l)
            - natMonomialCoeff S l) (natExpShift S j.2 (natExpTop S l)) = _
        rw [Finsupp.sub_apply, Finsupp.mapDomain_apply (natExpShift_injective S j.2)]
      rw [hstep, Finsupp.notMem_support_iff.mp hnotmem, ih, sub_zero]

/-! ## Independence of monomial coefficients with distinct tops -/

omit [DecidableEq ι] in
theorem natExp_eq_of_le_of_degree_le {S : Finset ι} {a b : NatExp S}
    (hle : a.1 ≤ b.1) (hdeg : ∑ i, b.1 i ≤ ∑ i, a.1 i) : a = b := by
  have hsum : ∑ i, a.1 i = ∑ i, b.1 i :=
    le_antisymm (Finset.sum_le_sum fun i _ => hle i) hdeg
  exact Subtype.ext (Finsupp.ext fun i =>
    (Finset.sum_eq_sum_iff_of_le (fun i _ => hle i)).mp hsum i (Finset.mem_univ i))

/-- **Distinct tops give independent monomial coefficients.**  A combination whose top-degree term
survives cannot vanish. -/
theorem natMonomialCoeff_combination_ne_zero {S : Finset ι} {κ : Type} [Fintype κ] [DecidableEq κ]
    (l : κ → List {j : ι // j ∈ S}) (a : κ → ℂ)
    (htop : Function.Injective fun k => natExpTop S (l k))
    {k₀ : κ} (hk₀ : a k₀ ≠ 0)
    (hmax : ∀ k, a k ≠ 0 → ∑ i, (natExpTop S (l k)).1 i ≤ ∑ i, (natExpTop S (l k₀)).1 i) :
    ∑ k, a k • natMonomialCoeff S (l k) ≠ 0 := by
  classical
  intro hzero
  have hval := congrArg (fun c : NatExp S →₀ ℂ => c (natExpTop S (l k₀))) hzero
  simp only [Finsupp.coe_finsetSum, Finset.sum_apply, Finsupp.coe_smul, Pi.smul_apply,
    smul_eq_mul, Finsupp.coe_zero, Pi.zero_apply] at hval
  have hterm : ∀ k ∈ Finset.univ, k ≠ k₀ →
      a k * natMonomialCoeff S (l k) (natExpTop S (l k₀)) = 0 := by
    intro k _ hk
    by_cases hak : a k = 0
    · simp [hak]
    by_cases hsupp : natExpTop S (l k₀) ∈ (natMonomialCoeff S (l k)).support
    · exfalso
      have hle := natMonomialCoeff_support_le S (l k) hsupp
      have heq := natExp_eq_of_le_of_degree_le hle (hmax k hak)
      exact hk (htop heq.symm)
    · simp [Finsupp.notMem_support_iff.mp hsupp]
  rw [Finset.sum_eq_single k₀ hterm (fun h => absurd (Finset.mem_univ k₀) h)] at hval
  rw [natMonomialCoeff_top] at hval
  exact hk₀ (by simpa using hval)

end

end GaloisForLFunctions
