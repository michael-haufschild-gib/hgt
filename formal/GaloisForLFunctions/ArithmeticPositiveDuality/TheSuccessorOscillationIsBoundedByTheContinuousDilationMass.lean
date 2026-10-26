import GaloisForLFunctions.ArithmeticPositiveDuality.TheSuccessorSeesOnlyTheContinuousDilationSpectrum

/-!
# The successor oscillation is bounded by the continuous dilation mass

Let `φ` be positive definite on `Aff(ℚ)` with archimedean dilation part
`φ(x ↦ ux) = ∫ u^{ix} dν(x)` for `u > 0`, `ν` a finite measure on `ℝ`.

**Theorem** (`norm_successor_sub_le_nonatomic`). For `b, b' ≠ 0`,
`|φ(x ↦ x + b) − φ(x ↦ x + b')| ≤ 2 ν{x : ν{x} = 0}`,
twice the mass of the continuous part of `ν`.

**Corollary** (`successor_blind_of_atomic`). If `ν` is purely atomic, the successor is blind:
`φ(x ↦ x + b)` is constant on `b ≠ 0`.

The bound is the limit of the finite-atom bound `2(ν(ℝ) − ν(F))` (`norm_successor_sub_le`)
along finite sets `F` exhausting the countable set of atoms of `ν`. Together with
`successor_sees_autocorrelation` it says that the successor reads exactly the continuous part of
the archimedean dilation spectrum: atoms never move it, absolutely continuous mass can.
-/

open Complex MeasureTheory Filter Topology Finset
open scoped InnerProductSpace ComplexConjugate

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality

variable {φ : AffineGroupQ → ℂ} (hφ : IsPosDefOnGroup φ) {ν : Measure ℝ} [IsFiniteMeasure ν]
  (hν : ∀ u : ℚˣ, 0 < (u : ℚ) → φ (dilation u) = ∫ x, archChar x u ∂ν)
include hφ hν

/-- The finite-atom bound along a finite set `F`: `|Δ| ≤ 2(ν(ℝ) − ν(F))`. -/
theorem norm_successor_sub_le_finset (F : Finset ℝ) {b b' : ℚ} (hb : b ≠ 0) (hb' : b' ≠ 0) :
    ‖φ (translation b) - φ (translation b')‖ ≤ 2 * (ν.real Set.univ - ν.real (F : Set ℝ)) := by
  have h := norm_successor_sub_le hφ hν (γ := fun k => ((F.equivFin.symm k : F) : ℝ))
    (fun j k hjk => F.equivFin.symm.injective (Subtype.ext hjk)) hb hb'
  have hsum : ∑ k, ν.real {((F.equivFin.symm k : F) : ℝ)} = ν.real (F : Set ℝ) := by
    rw [F.equivFin.symm.sum_comp (fun x : F => ν.real {(x : ℝ)}),
      F.sum_coe_sort (fun x => ν.real {x}), sum_measureReal_singleton]
  rwa [hsum] at h

/-- **The successor oscillates by at most twice the continuous dilation mass.** -/
theorem norm_successor_sub_le_nonatomic {b b' : ℚ} (hb : b ≠ 0) (hb' : b' ≠ 0) :
    ‖φ (translation b) - φ (translation b')‖ ≤ 2 * ν.real {x | ν {x} = 0} := by
  set A : Set ℝ := {x | 0 < ν {x}}
  have hA : A.Countable := Measure.countable_meas_pos_of_disjoint_iUnion
    (As := fun x : ℝ => ({x} : Set ℝ)) (fun x => measurableSet_singleton x)
    (fun x y hxy => Set.disjoint_singleton.mpr hxy)
  obtain ⟨e, he⟩ := Set.countable_iff_exists_injective.mp hA
  -- finite sets exhausting the atoms
  set F : ℕ → Set ℝ := fun n => Subtype.val '' {a : A | e a < n}
  have hF : ∀ n, (F n).Finite := fun n =>
    ((Set.finite_lt_nat n).preimage he.injOn).image _
  have hmono : Monotone F := fun m n hmn => Set.image_mono fun a (ha : e a < m) =>
    (lt_of_lt_of_le ha hmn : e a < n)
  have hunion : ⋃ n, F n = A := by
    ext x
    simp only [Set.mem_iUnion, F, Set.mem_image, Set.mem_setOf_eq]
    constructor
    · rintro ⟨n, a, -, rfl⟩; exact a.2
    · intro hx; exact ⟨e ⟨x, hx⟩ + 1, ⟨x, hx⟩, Nat.lt_succ_self _, rfl⟩
  have hlim : Tendsto (fun n => ν.real (F n)) atTop (𝓝 (ν.real A)) := by
    have h := tendsto_measure_iUnion_atTop (μ := ν) hmono
    rw [hunion] at h
    exact (ENNReal.tendsto_toReal (measure_ne_top ν A)).comp h
  have hbound : ∀ n, ‖φ (translation b) - φ (translation b')‖ ≤
      2 * (ν.real Set.univ - ν.real (F n)) := fun n => by
    have h := norm_successor_sub_le_finset hφ hν (hF n).toFinset hb hb'
    rwa [Set.Finite.coe_toFinset] at h
  have hle : ‖φ (translation b) - φ (translation b')‖ ≤ 2 * (ν.real Set.univ - ν.real A) :=
    ge_of_tendsto ((hlim.const_sub _).const_mul 2) (Eventually.of_forall hbound)
  have hcompl : {x : ℝ | ν {x} = 0} = Aᶜ := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_compl_iff, A, not_lt, nonpos_iff_eq_zero]
  rw [hcompl, measureReal_compl hA.measurableSet]
  exact hle

/-- **Purely atomic archimedean dilation spectra blind the successor.** -/
theorem successor_blind_of_atomic (hat : ν {x | ν {x} = 0} = 0) :
    ∃ α : ℂ, ∀ b : ℚ, b ≠ 0 → φ (translation b) = α := by
  refine ⟨φ (translation 1), fun b hb => ?_⟩
  have h := norm_successor_sub_le_nonatomic hφ hν hb one_ne_zero
  rw [measureReal_def, hat, ENNReal.toReal_zero, mul_zero] at h
  exact sub_eq_zero.mp (norm_le_zero_iff.mp h)

end GaloisForLFunctions.ArithmeticPositiveDuality
