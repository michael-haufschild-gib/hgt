import GaloisForLFunctions.HTGeometry.ChamberLawPickWitness
import GaloisForLFunctions.RHTower.CCMPolarPrimeStieltjesAutocorrelation
import Mathlib.NumberTheory.PrimeCounting

/-!
# Raw critical-Mellin Stieltjes chambers

The positive polar continuum is paired with the actual negative von Mangoldt atoms.  Boundary
localization shows that every finite packet of active prime-power atoms contributes its full packet
dimension to the negative Pick index.  Enumerating all active atoms at an aperture then gives the
raw finite-aperture chamber, whose index is cofinally unbounded.
-/

open scoped BigOperators ComplexConjugate Classical ComplexOrder ENNReal
open MeasureTheory Set Finset Filter Topology ArithmeticFunction

noncomputable section

namespace RHTower

open GaloisForLFunctions.HTGeometry Matrix

/-- The positive polar part of the critical-Mellin Stieltjes source on `(0,2A]`. -/
def criticalMellinPolarMeasure (A : ℝ) : Measure ℝ :=
  (volume.restrict (Ioc 0 (2 * A))).withDensity
    (fun h => ENNReal.ofReal (2 * Real.cosh (h / 2)))

theorem criticalMellinPolarDensity_integrable (A : ℝ) :
    Integrable (fun h : ℝ => 2 * Real.cosh (h / 2))
      (volume.restrict (Ioc 0 (2 * A))) := by
  have hcont : Continuous (fun h : ℝ => 2 * Real.cosh (h / 2)) := by
    fun_prop
  exact hcont.integrableOn_Ioc

/-- The polar measure is finite at every finite aperture. -/
theorem criticalMellinPolarMeasure_isFinite (A : ℝ) :
    IsFiniteMeasure (criticalMellinPolarMeasure A) := by
  rw [criticalMellinPolarMeasure]
  exact isFiniteMeasure_withDensity_ofReal
    (criticalMellinPolarDensity_integrable A).hasFiniteIntegral

/-- The finite polar measure integrates the chamber dominant at every real node. -/
theorem integrable_atomDominant_criticalMellinPolarMeasure
    (A a : ℝ) {R : ℝ} (hR : 0 < R) :
    Integrable (atomDominant a R) (criticalMellinPolarMeasure A) := by
  letI : IsFiniteMeasure (criticalMellinPolarMeasure A) :=
    criticalMellinPolarMeasure_isFinite A
  have hmeas : Measurable (atomDominant a R) := by
    have hopen : IsOpen {s : ℝ | |s - a| < R} := by
      exact isOpen_lt (continuous_abs.comp (continuous_id.sub continuous_const)) continuous_const
    have htail : Measurable (fun s : ℝ => tailComparison a R / (1 + s ^ 2)) := by
      fun_prop
    rw [show atomDominant a R = fun t =>
        Set.indicator {s : ℝ | |s - a| < R} (fun _ => (1 : ℝ)) t +
          Set.indicator {s : ℝ | ¬ |s - a| < R}
            (fun s => tailComparison a R / (1 + s ^ 2)) t by
      funext t
      exact atomDominant_eq_indicator a R t]
    exact (measurable_const.indicator hopen.measurableSet).add
      (htail.indicator hopen.measurableSet.compl)
  refine Integrable.of_bound hmeas.aestronglyMeasurable
    (max 1 (tailComparison a R)) (ae_of_all _ fun t => ?_)
  rw [atomDominant]
  split_ifs
  · simp
  · have hC : 0 ≤ tailComparison a R := (tailComparison_pos (a := a) hR).le
    have hden : 1 ≤ 1 + t ^ 2 := by nlinarith [sq_nonneg t]
    have hden0 : 0 ≤ 1 + t ^ 2 := by linarith
    rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg hC hden0)]
    exact (div_le_self hC hden).trans (le_max_right _ _)

/-- The polar continuum has no atoms, including at every prime logarithm. -/
theorem criticalMellinPolarMeasure_singleton (A a : ℝ) :
    criticalMellinPolarMeasure A {a} = 0 := by
  unfold criticalMellinPolarMeasure
  exact measure_singleton a

/-- Every nonzero von Mangoldt atom has strictly positive critical-Mellin weight. -/
theorem criticalMellinAtomWeight_pos {k : ℕ} (hk : IsPrimePow k) :
    0 < criticalMellinAtomWeight k := by
  rw [criticalMellinAtomWeight]
  have hkpos : (0 : ℝ) < k := by exact_mod_cast hk.pos
  exact mul_pos (Real.rpow_pos_of_pos hkpos _)
    (ArithmeticFunction.vonMangoldt_pos_iff.mpr hk)

/-- The selected actual source nodes. -/
def criticalMellinSelectedNodes {d : ℕ} (k : Fin d → ℕ) : Fin d → ℝ :=
  fun j => Real.log (k j)

/-- The selected actual negative source coefficients. -/
def criticalMellinSelectedCoefficients {d : ℕ} (k : Fin d → ℕ) : Fin d → ℝ :=
  fun j => -criticalMellinAtomWeight (k j)

/-- The scaled Pick Gram of the positive polar continuum and a selected packet of actual negative
von Mangoldt atoms. -/
def criticalMellinSelectedStieltjesGram {d : ℕ} (A : ℝ) (k : Fin d → ℕ) (y : ℝ) :
    Matrix (Fin d) (Fin d) ℂ :=
  totalGram (criticalMellinPolarMeasure A) (criticalMellinSelectedNodes k)
    (criticalMellinSelectedCoefficients k) y

theorem criticalMellinSelectedNodes_injective {d : ℕ} {k : Fin d → ℕ}
    (hk : ∀ j, IsPrimePow (k j)) (hkinj : Function.Injective k) :
    Function.Injective (criticalMellinSelectedNodes k) := by
  intro i j hij
  apply hkinj
  have hcast : (k i : ℝ) = (k j : ℝ) := Real.strictMonoOn_log.injOn
    (by simpa only [Set.mem_Ioi] using (show (0 : ℝ) < k i by exact_mod_cast (hk i).pos))
    (by simpa only [Set.mem_Ioi] using (show (0 : ℝ) < k j by exact_mod_cast (hk j).pos)) hij
  exact_mod_cast hcast

/-- Every finite prime-power packet has a common strictly positive weight margin. -/
theorem exists_criticalMellinSelectedWeightMargin {d : ℕ} (k : Fin d → ℕ)
    (hk : ∀ j, IsPrimePow (k j)) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ j, criticalMellinSelectedCoefficients k j ≤ -δ := by
  classical
  cases isEmpty_or_nonempty (Fin d) with
  | inl hempty =>
      refine ⟨1, one_pos, fun j => ?_⟩
      exact isEmptyElim j
  | inr hnonempty =>
      let weights : Finset ℝ :=
        Finset.univ.image fun j : Fin d => criticalMellinAtomWeight (k j)
      have hweights : weights.Nonempty := by
        obtain ⟨j⟩ := hnonempty
        exact ⟨criticalMellinAtomWeight (k j),
          Finset.mem_image.mpr ⟨j, Finset.mem_univ _, rfl⟩⟩
      let δ : ℝ := weights.min' hweights
      have hδ : 0 < δ := by
        have hmem : δ ∈ weights := Finset.min'_mem weights hweights
        obtain ⟨j, -, hj⟩ := Finset.mem_image.mp hmem
        rw [← hj]
        exact criticalMellinAtomWeight_pos (hk j)
      refine ⟨δ, hδ, fun j => ?_⟩
      have hmin : δ ≤ criticalMellinAtomWeight (k j) :=
        Finset.min'_le weights _
          (Finset.mem_image.mpr ⟨j, Finset.mem_univ _, rfl⟩)
      dsimp [criticalMellinSelectedCoefficients]
      linarith

/-- **Raw selected-source chamber law.**  If the selected prime-power atoms are active at aperture
`A`, their actual scaled Stieltjes Pick Gram is negative definite at every sufficiently small
nonzero height.  Its chamber grade is exactly the packet size. -/
theorem criticalMellinSelectedStieltjes_chamber {d : ℕ} {A : ℝ} {k : Fin d → ℕ}
    (hk : ∀ j, IsPrimePow (k j)) (hkinj : Function.Injective k)
    (hactive : ∀ j, Real.log (k j) ≤ 2 * A) :
    (∀ᶠ y : ℝ in 𝓝[≠] 0, ∀ x : Fin d → ℂ, x ≠ 0 →
      (star x ⬝ᵥ (criticalMellinSelectedStieltjesGram A k y).mulVec x).re < 0) ∧
      (∀ j, criticalMellinSelectedNodes k j ∈ Ioc 0 (2 * A)) ∧
      hammingDist (signPattern (criticalMellinSelectedCoefficients k))
        (positiveChamber d) = d := by
  obtain ⟨δ, hδ, hc⟩ := exists_criticalMellinSelectedWeightMargin k hk
  have hchamber := chamberLaw_all_negative
    (criticalMellinPolarMeasure A) (criticalMellinSelectedNodes k)
    (criticalMellinSelectedCoefficients k)
    (criticalMellinSelectedNodes_injective hk hkinj) hδ hc 1 one_pos
    (fun j => integrable_atomDominant_criticalMellinPolarMeasure A _ one_pos)
    (fun j => criticalMellinPolarMeasure_singleton A _)
  refine ⟨?_, ?_, hchamber.2⟩
  · simpa [criticalMellinSelectedStieltjesGram] using hchamber.1
  · intro j
    exact ⟨Real.log_pos (by exact_mod_cast (hk j).one_lt), hactive j⟩

/-- The nonzero critical-Mellin atoms active at aperture `A`. -/
def activeCriticalMellinAtoms (A : ℝ) : Finset ℕ :=
  (Finset.Icc 2 ⌊Real.exp (2 * A)⌋₊).filter IsPrimePow

/-- A duplicate-free enumeration of all active nonzero critical-Mellin atoms. -/
def activeCriticalMellinAtom (A : ℝ) : Fin (activeCriticalMellinAtoms A).card → ℕ :=
  fun j => ((activeCriticalMellinAtoms A).equivFinOfCardEq rfl).symm j

theorem activeCriticalMellinAtom_injective (A : ℝ) :
    Function.Injective (activeCriticalMellinAtom A) := by
  exact Subtype.val_injective.comp
    ((activeCriticalMellinAtoms A).equivFinOfCardEq rfl).symm.injective

theorem activeCriticalMellinAtom_isPrimePow (A : ℝ)
    (j : Fin (activeCriticalMellinAtoms A).card) :
    IsPrimePow (activeCriticalMellinAtom A j) := by
  exact (Finset.mem_filter.mp
    (((activeCriticalMellinAtoms A).equivFinOfCardEq rfl).symm j).property).2

theorem activeCriticalMellinAtom_log_le (A : ℝ)
    (j : Fin (activeCriticalMellinAtoms A).card) :
    Real.log (activeCriticalMellinAtom A j) ≤ 2 * A := by
  have hmem := (Finset.mem_filter.mp
    (((activeCriticalMellinAtoms A).equivFinOfCardEq rfl).symm j).property).1
  have hk := (Finset.mem_Icc.mp hmem).2
  have hkpos : (0 : ℝ) < activeCriticalMellinAtom A j := by
    exact_mod_cast (activeCriticalMellinAtom_isPrimePow A j).pos
  exact (Real.log_le_iff_le_exp hkpos).mpr
    ((Nat.le_floor_iff (Real.exp_pos (2 * A)).le).mp hk)

/-- The full raw finite-aperture chamber has one negative direction per active nonzero atom. -/
theorem activeCriticalMellinStieltjes_chamber (A : ℝ) :
    (∀ᶠ y : ℝ in 𝓝[≠] 0,
      ∀ x : Fin (activeCriticalMellinAtoms A).card → ℂ, x ≠ 0 →
        (star x ⬝ᵥ
          (criticalMellinSelectedStieltjesGram A (activeCriticalMellinAtom A) y).mulVec x).re < 0) ∧
      hammingDist
        (signPattern (criticalMellinSelectedCoefficients (activeCriticalMellinAtom A)))
        (positiveChamber (activeCriticalMellinAtoms A).card)
        = (activeCriticalMellinAtoms A).card := by
  have h := criticalMellinSelectedStieltjes_chamber
    (fun j => activeCriticalMellinAtom_isPrimePow A j)
    (activeCriticalMellinAtom_injective A)
    (fun j => activeCriticalMellinAtom_log_le A j)
  exact ⟨h.1, h.2.2⟩

/-- The raw source chamber grades are cofinally unbounded: the first `d` primes are all active at
the aperture whose doubled width is the `d`-th prime. -/
theorem activeCriticalMellinAtoms_card_ge (d : ℕ) :
    d ≤ (activeCriticalMellinAtoms ((Nat.nth Nat.Prime d : ℝ) / 2)).card := by
  let A : ℝ := (Nat.nth Nat.Prime d : ℝ) / 2
  let f : Fin d → ↥(activeCriticalMellinAtoms A) := fun j =>
    ⟨Nat.nth Nat.Prime j, by
      rw [activeCriticalMellinAtoms, Finset.mem_filter, Finset.mem_Icc]
      have hjprime : Nat.Prime (Nat.nth Nat.Prime j) := Nat.prime_nth_prime j
      have hdprime : Nat.Prime (Nat.nth Nat.Prime d) := Nat.prime_nth_prime d
      have hjd : Nat.nth Nat.Prime j ≤ Nat.nth Nat.Prime d :=
        (Nat.nth_strictMono Nat.infinite_setOf_prime).monotone (Nat.le_of_lt j.isLt)
      have hreal : (Nat.nth Nat.Prime j : ℝ) ≤ Real.exp (2 * A) := by
        calc
          (Nat.nth Nat.Prime j : ℝ) ≤ (Nat.nth Nat.Prime d : ℝ) := by exact_mod_cast hjd
          _ ≤ (Nat.nth Nat.Prime d : ℝ) + 1 := by linarith
          _ ≤ Real.exp (Nat.nth Nat.Prime d : ℝ) := Real.add_one_le_exp _
          _ = Real.exp (2 * A) := by congr 1; dsimp [A]; ring
      exact ⟨⟨hjprime.two_le,
        (Nat.le_floor_iff (Real.exp_pos (2 * A)).le).mpr hreal⟩,
        hjprime.isPrimePow⟩⟩
  have hfinj : Function.Injective f := by
    intro i j hij
    exact Fin.ext ((Nat.nth_injective Nat.infinite_setOf_prime)
      (congrArg Subtype.val hij))
  simpa [A] using Fintype.card_le_of_injective f hfinj

/-- **Cofinal raw-index inflation.**  For every finite target dimension there is an actual aperture
whose complete nonzero critical-Mellin atom chamber is negative definite near the boundary and has
grade at least that dimension. -/
theorem exists_activeCriticalMellinStieltjes_chamber_grade_ge (d : ℕ) :
    ∃ A : ℝ,
      d ≤ (activeCriticalMellinAtoms A).card ∧
      (∀ᶠ y : ℝ in 𝓝[≠] 0,
        ∀ x : Fin (activeCriticalMellinAtoms A).card → ℂ, x ≠ 0 →
          (star x ⬝ᵥ
            (criticalMellinSelectedStieltjesGram A (activeCriticalMellinAtom A) y).mulVec x).re < 0) := by
  refine ⟨(Nat.nth Nat.Prime d : ℝ) / 2, activeCriticalMellinAtoms_card_ge d, ?_⟩
  exact (activeCriticalMellinStieltjes_chamber _).1

end RHTower
