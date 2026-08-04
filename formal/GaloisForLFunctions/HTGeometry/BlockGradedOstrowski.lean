import GaloisForLFunctions.HTGeometry.BlockOstrowskiFiber
import GaloisForLFunctions.HTGeometry.BlockFrequencyProfile

/-!
# Grading a several-carrier relation by its multi-degree

A relation among the jets of an `n`-element palette is graded by the multi-degree: how many factors
of each carrier a monomial carries.  Each grade has its own slot set and its own canonical
slot-to-block assignment, so the grades cannot be merged into one family — they are summed over a
finite index of bounded multi-degrees.

This file assembles the graded expansion: the whole relation is one exponential series over the
disjoint union of the grades, exactly as in the single-carrier case, and each grade's summability is
the fixed-grade statement.
-/

open Filter Topology

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {ι : Type*} [DecidableEq ι] {n N : ℕ}

/-- The number of slots of a multi-degree. -/
def gradeSlots (d : Fin n → Fin (N + 1)) : ℕ := ∑ k, (d k : ℕ)

/-- The canonical slot-to-block assignment of a multi-degree. -/
def gradeBlk (d : Fin n → Fin (N + 1)) : Fin (gradeSlots d) → Fin n :=
  profileBlk fun k => (d k : ℕ)

/-- The amplitude family of the slot `j` in the grade `d`: the amplitudes restricted to that slot's
own block. -/
def gradeAmp (a : ι → ℂ) (bidx : ι → Fin n) (d : Fin n → Fin (N + 1))
    (j : Fin (gradeSlots d)) : ι → ℂ :=
  fun y => if bidx y = gradeBlk d j then a y else 0

variable {a : ι → ℂ} {omega : ι → ℝ} {bidx : ι → Fin n}

omit [DecidableEq ι] in
theorem summable_norm_blockGraded
    (hb : ∀ (d : Fin n → Fin (N + 1)) (j : Fin (gradeSlots d)),
      ExpSeriesNormallySummable (gradeAmp a bidx d j) omega)
    (K : ∀ d : Fin n → Fin (N + 1), Finset (Fin (gradeSlots d) → ℕ))
    (c : ∀ d : Fin n → Fin (N + 1), (Fin (gradeSlots d) → ℕ) → ℂ)
    (d : Fin n → Fin (N + 1)) :
    Summable fun p : Σ _ : {s // s ∈ K d}, Fin (gradeSlots d) → ι =>
      ‖blockMonomialAmplitude (gradeAmp a bidx d) omega (c d p.1.1) p.1.1 p.2‖ :=
  summable_norm_sigma (J := fun _ : {s // s ∈ K d} => (Fin (gradeSlots d) → ι))
    (b := fun s p => blockMonomialAmplitude (gradeAmp a bidx d) omega (c d s.1) s.1 p)
    fun s => summable_norm_blockMonomialAmplitude (hb d) (c d s.1) s.1

omit [DecidableEq ι] in
/-- **A graded several-carrier relation is one exponential series.** -/
theorem blockGradedCombination_eq_expSeriesCarrier
    (hb : ∀ (d : Fin n → Fin (N + 1)) (j : Fin (gradeSlots d)),
      ExpSeriesNormallySummable (gradeAmp a bidx d j) omega)
    (K : ∀ d : Fin n → Fin (N + 1), Finset (Fin (gradeSlots d) → ℕ))
    (c : ∀ d : Fin n → Fin (N + 1), (Fin (gradeSlots d) → ℕ) → ℂ) (t : ℝ) :
    ∑ d : Fin n → Fin (N + 1), ∑ s ∈ K d, c d s *
        ∏ j, iteratedDeriv (s j) (cexpSeriesCarrier (gradeAmp a bidx d j) omega) (t : ℂ)
      = expSeriesCarrier
        (fun q : Σ d : Fin n → Fin (N + 1), Σ _ : {s // s ∈ K d}, Fin (gradeSlots d) → ι =>
          blockMonomialAmplitude (gradeAmp a bidx q.1) omega (c q.1 q.2.1.1) q.2.1.1 q.2.2)
        (fun q : Σ d : Fin n → Fin (N + 1), Σ _ : {s // s ∈ K d}, Fin (gradeSlots d) → ι =>
          tupleFrequency omega q.2.2) t := by
  rw [← sum_expSeriesCarrier
    (J := fun d : Fin n → Fin (N + 1) => Σ _ : {s // s ∈ K d}, Fin (gradeSlots d) → ι)
    (fun d p => blockMonomialAmplitude (gradeAmp a bidx d) omega (c d p.1.1) p.1.1 p.2)
    (fun _ p => tupleFrequency omega p.2) (summable_norm_blockGraded hb K c) t]
  refine Finset.sum_congr rfl fun d _ => ?_
  exact blockMonomialCombination_eq_expSeriesCarrier (hb d) (c d) t

omit [DecidableEq ι] in
/-- **A vanishing graded relation is a vanishing exponential series.** -/
theorem blockGraded_expSeriesCarrier_eq_zero
    (hb : ∀ (d : Fin n → Fin (N + 1)) (j : Fin (gradeSlots d)),
      ExpSeriesNormallySummable (gradeAmp a bidx d j) omega)
    (K : ∀ d : Fin n → Fin (N + 1), Finset (Fin (gradeSlots d) → ℕ))
    (c : ∀ d : Fin n → Fin (N + 1), (Fin (gradeSlots d) → ℕ) → ℂ)
    (hzero : ∀ t : ℝ, ∑ d : Fin n → Fin (N + 1), ∑ s ∈ K d, c d s *
      ∏ j, iteratedDeriv (s j) (cexpSeriesCarrier (gradeAmp a bidx d j) omega) (t : ℂ) = 0)
    (t : ℝ) :
    expSeriesCarrier
      (fun q : Σ d : Fin n → Fin (N + 1), Σ _ : {s // s ∈ K d}, Fin (gradeSlots d) → ι =>
        blockMonomialAmplitude (gradeAmp a bidx q.1) omega (c q.1 q.2.1.1) q.2.1.1 q.2.2)
      (fun q : Σ d : Fin n → Fin (N + 1), Σ _ : {s // s ∈ K d}, Fin (gradeSlots d) → ι =>
        tupleFrequency omega q.2.2) t = 0 := by
  rw [← blockGradedCombination_eq_expSeriesCarrier hb K c t]
  exact hzero t

/-- **Ostrowski for a graded several-carrier relation.**  Grades of different multi-degree sit at
disjoint frequencies, so each grade is tested on its own and the fixed-grade theorem applies. -/
theorem eq_zero_of_gradedBlockMonomialCombination_vanishing
    (hom : RationallyIndependentSequence omega)
    (hb : ∀ (d : Fin n → Fin (N + 1)) (j : Fin (gradeSlots d)),
      ExpSeriesNormallySummable (gradeAmp a bidx d j) omega)
    (hinf : ∀ k : Fin n, {y : ι | bidx y = k ∧ a y ≠ 0}.Infinite)
    (K : ∀ d : Fin n → Fin (N + 1), Finset (Fin (gradeSlots d) → ℕ))
    (hdistinct : ∀ d : Fin n → Fin (N + 1), ∀ s ∈ K d, ∀ s' ∈ K d,
      (∀ k, slotCount (gradeBlk d) s k = slotCount (gradeBlk d) s' k) → s = s')
    (c : ∀ d : Fin n → Fin (N + 1), (Fin (gradeSlots d) → ℕ) → ℂ)
    (hzero : ∀ t : ℝ, ∑ d : Fin n → Fin (N + 1), ∑ s ∈ K d, c d s *
      ∏ j, iteratedDeriv (s j) (cexpSeriesCarrier (gradeAmp a bidx d j) omega) (t : ℂ) = 0) :
    ∀ d : Fin n → Fin (N + 1), ∀ s ∈ K d, c d s = 0 := by
  classical
  have hsumTotal : Summable fun q : Σ d : Fin n → Fin (N + 1),
      Σ _ : {s // s ∈ K d}, Fin (gradeSlots d) → ι =>
      ‖blockMonomialAmplitude (gradeAmp a bidx q.1) omega (c q.1 q.2.1.1) q.2.1.1 q.2.2‖ :=
    summable_norm_sigma
      (J := fun d : Fin n → Fin (N + 1) => Σ _ : {s // s ∈ K d}, Fin (gradeSlots d) → ι)
      (b := fun d p => blockMonomialAmplitude (gradeAmp a bidx d) omega (c d p.1.1) p.1.1 p.2)
      (summable_norm_blockGraded hb K c)
  intro d
  refine eq_zero_of_blockFiberAmplitudes_vanishing hom (hb d) hinf (hdistinct d) (c d) ?_
  intro i hiinj hane hib
  have hfibTotal := fiberAmplitude_eq_zero_of_expSeriesCarrier_eq_zero _ _ hsumTotal
    (blockGraded_expSeriesCarrier_eq_zero hb K c hzero) (tupleFrequency omega i)
  rw [fiberAmplitude_sigma
    (J := fun d : Fin n → Fin (N + 1) => Σ _ : {s // s ∈ K d}, Fin (gradeSlots d) → ι)
    (fun d p => blockMonomialAmplitude (gradeAmp a bidx d) omega (c d p.1.1) p.1.1 p.2)
    (fun _ p => tupleFrequency omega p.2) (summable_norm_blockGraded hb K c)] at hfibTotal
  rw [Finset.sum_eq_single d] at hfibTotal
  · exact hfibTotal
  · intro d' _ hd'
    have hk : ∃ k : Fin n, (d' k : ℕ) ≠ (d k : ℕ) := by
      by_contra hcon
      push Not at hcon
      exact hd' (funext fun k => Fin.ext (hcon k))
    obtain ⟨k, hkne⟩ := hk
    refine fiberAmplitude_blockGrade_eq_zero_of_profile_ne hom a bidx (gradeBlk d')
      (fun s : {s // s ∈ K d'} => c d' s.1) (fun s : {s // s ∈ K d'} => s.1) (k := k) ?_
    have hd'k : (Finset.univ.filter fun j : Fin (gradeSlots d') => gradeBlk d' j = k).card
        = (d' k : ℕ) := card_profileBlk _ k
    have hdk : (Finset.univ.filter fun j : Fin (gradeSlots d) => bidx (i j) = k).card
        = (d k : ℕ) := by
      rw [Finset.filter_congr fun j _ => by rw [hib j]]
      exact card_profileBlk _ k
    rw [hd'k, hdk]
    exact hkne
  · intro hd
    exact absurd (Finset.mem_univ d) hd

end

end GaloisForLFunctions.HTGeometry
