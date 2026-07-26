import GaloisForLFunctions.HTGeometry.Hypertranscendence
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# The fundamental parallelogram of two independent steps

Two `ℝ`-independent complex numbers form an `ℝ`-basis of `ℂ`, so every point differs from a point of
the compact parallelogram they span by an integer combination of the two steps, with coefficients
bounded by a fixed multiple of the norm.

* `stepBasis` — the two steps as an `ℝ`-basis of `ℂ`, with bounded coordinate functionals
  (`exists_bound_stepBasis_repr`);
* `fundamentalParallelogram` and `isCompact_fundamentalParallelogram`;
* **`exists_bounded_intCombination`** — the covering, with the coefficient bound.

Two uses: the exponential-type bound for a quasi-periodic function, which pays one multiplier per
lattice step, and the finiteness of the poles of a lattice-periodic meromorphic function, which
happens on a compact set.
-/

namespace GaloisForLFunctions.HTGeometry

/-! ### The two steps as a real basis -/

/-- Two `ℝ`-independent complex numbers form an `ℝ`-basis of `ℂ`. -/
noncomputable def stepBasis {w₁ w₂ : ℂ} (hindep : LinearIndependent ℝ ![w₁, w₂]) :
    Module.Basis (Fin 2) ℝ ℂ :=
  basisOfLinearIndependentOfCardEqFinrank hindep (by simp [Complex.finrank_real_complex])

theorem stepBasis_apply {w₁ w₂ : ℂ} (hindep : LinearIndependent ℝ ![w₁, w₂]) (i : Fin 2) :
    stepBasis hindep i = ![w₁, w₂] i := by
  rw [stepBasis, coe_basisOfLinearIndependentOfCardEqFinrank]

/-- The coordinate functionals of a basis of `ℂ` over `ℝ` are bounded by the norm. -/
theorem exists_bound_stepBasis_repr {w₁ w₂ : ℂ} (hindep : LinearIndependent ℝ ![w₁, w₂])
    (i : Fin 2) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z : ℂ, |(stepBasis hindep).repr z i| ≤ C * ‖z‖ := by
  let L : ℂ →ₗ[ℝ] ℝ :=
    { toFun := fun z => (stepBasis hindep).repr z i
      map_add' := by intro x y; simp
      map_smul' := by
        intro c x
        simp only [map_smul, Finsupp.smul_apply, smul_eq_mul]
        rfl }
  let Lc : ℂ →L[ℝ] ℝ := ⟨L, LinearMap.continuous_of_finiteDimensional L⟩
  refine ⟨‖Lc‖, norm_nonneg _, fun z => ?_⟩
  have hle := Lc.le_opNorm z
  simpa [Lc, L, Real.norm_eq_abs] using hle

/-! ### The parallelogram -/

/-- The closed parallelogram spanned by two steps. -/
def fundamentalParallelogram (w₁ w₂ : ℂ) : Set ℂ :=
  (fun p : ℝ × ℝ => p.1 • w₁ + p.2 • w₂) '' (Set.Icc 0 1 ×ˢ Set.Icc 0 1)

theorem isCompact_fundamentalParallelogram (w₁ w₂ : ℂ) :
    IsCompact (fundamentalParallelogram w₁ w₂) := by
  refine ((isCompact_Icc (a := (0 : ℝ)) (b := 1)).prod
    (isCompact_Icc (a := (0 : ℝ)) (b := 1))).image ?_
  fun_prop

theorem zero_mem_fundamentalParallelogram (w₁ w₂ : ℂ) :
    (0 : ℂ) ∈ fundamentalParallelogram w₁ w₂ :=
  ⟨(0, 0), by constructor <;> simp, by simp⟩

/-! ### The covering -/

/-- **Every point is a bounded integer translate of a point of the parallelogram.** -/
theorem exists_bounded_intCombination {w₁ w₂ : ℂ} (hindep : LinearIndependent ℝ ![w₁, w₂]) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z : ℂ, ∃ m n : ℤ,
      z - (m • w₁ + n • w₂) ∈ fundamentalParallelogram w₁ w₂ ∧
      ((m.natAbs : ℝ) ≤ C * ‖z‖ + 1) ∧ ((n.natAbs : ℝ) ≤ C * ‖z‖ + 1) := by
  obtain ⟨C₁, hC₁0, hC₁⟩ := exists_bound_stepBasis_repr hindep 0
  obtain ⟨C₂, hC₂0, hC₂⟩ := exists_bound_stepBasis_repr hindep 1
  refine ⟨max C₁ C₂, le_trans hC₁0 (le_max_left _ _), fun z => ?_⟩
  obtain ⟨s, hs⟩ : ∃ s : ℝ, s = (stepBasis hindep).repr z 0 := ⟨_, rfl⟩
  obtain ⟨t, ht⟩ : ∃ t : ℝ, t = (stepBasis hindep).repr z 1 := ⟨_, rfl⟩
  have hzsum : z = s • w₁ + t • w₂ := by
    have hrep := (stepBasis hindep).sum_repr z
    rw [Fin.sum_univ_two, stepBasis_apply hindep 0, stepBasis_apply hindep 1] at hrep
    rw [hs, ht]
    simpa using hrep.symm
  have hcast : ∀ k : ℤ, ((k.natAbs : ℝ)) = |(k : ℝ)| := by
    intro k
    rw [← Int.cast_natCast, Int.natCast_natAbs, Int.cast_abs]
  have hfloor : ∀ (r C : ℝ), |r| ≤ C * ‖z‖ → ((⌊r⌋ : ℤ).natAbs : ℝ) ≤ C * ‖z‖ + 1 := by
    intro r C hr
    rw [hcast]
    have h1 : ((⌊r⌋ : ℤ) : ℝ) ≤ r := Int.floor_le r
    have h2 : r - 1 < ((⌊r⌋ : ℤ) : ℝ) := by
      have := Int.lt_floor_add_one r
      linarith
    have h3 : -|r| ≤ r := neg_abs_le r
    have h4 : r ≤ |r| := le_abs_self r
    rw [abs_le]
    constructor <;> linarith
  have hmono : ∀ (r C : ℝ), 0 ≤ C → C ≤ max C₁ C₂ → |r| ≤ C * ‖z‖ →
      ((⌊r⌋ : ℤ).natAbs : ℝ) ≤ max C₁ C₂ * ‖z‖ + 1 := by
    intro r C _ hCle hr
    refine le_trans (hfloor r C hr) ?_
    have : C * ‖z‖ ≤ max C₁ C₂ * ‖z‖ :=
      mul_le_mul_of_nonneg_right hCle (norm_nonneg _)
    linarith
  refine ⟨⌊s⌋, ⌊t⌋, ?_, ?_, ?_⟩
  · have hu : z - ((⌊s⌋ : ℤ) • w₁ + (⌊t⌋ : ℤ) • w₂)
        = (s - (⌊s⌋ : ℝ)) • w₁ + (t - (⌊t⌋ : ℝ)) • w₂ := by
      rw [hzsum]
      simp only [sub_smul, zsmul_eq_mul, Complex.real_smul, Complex.ofReal_intCast]
      ring
    refine ⟨(s - (⌊s⌋ : ℝ), t - (⌊t⌋ : ℝ)), ⟨⟨?_, ?_⟩, ?_, ?_⟩, hu.symm⟩
    · change 0 ≤ Int.fract s
      exact Int.fract_nonneg s
    · change Int.fract s ≤ 1
      exact (Int.fract_lt_one s).le
    · change 0 ≤ Int.fract t
      exact Int.fract_nonneg t
    · change Int.fract t ≤ 1
      exact (Int.fract_lt_one t).le
  · refine hmono s C₁ hC₁0 (le_max_left _ _) ?_
    rw [hs]
    exact hC₁ z
  · refine hmono t C₂ hC₂0 (le_max_right _ _) ?_
    rw [ht]
    exact hC₂ z

end GaloisForLFunctions.HTGeometry
