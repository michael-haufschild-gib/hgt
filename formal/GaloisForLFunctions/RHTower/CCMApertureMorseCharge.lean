import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Order.ConditionallyCompleteLattice.Basic

/-!
# The aperture Morse charge is monotone, and its vanishing is form positivity

The negative Morse charge of a quadratic form on a trial domain is the largest dimension of a
subspace on which the form is negative definite.  Three facts are proved.

* `HasNegDefSubspaceOfDim.mono` and `morseCharge_mono` — the charge is **monotone** under enlargement
  of the trial domain.  In the aperture representation the enlargement is literal inclusion of
  submodules, so zero extension is not an extra construction and no isometry has to be built.
* `negDefDims_eq_zero_iff_nonneg` and `morseCharge_eq_zero_of_nonneg` — the charge vanishes exactly
  when the form is nonnegative on the domain.  One direction is immediate; the other produces an explicit one-dimensional negative
  subspace from a single negative vector, which is where homogeneity of the form is used.
* `exists_crossing_of_pos_of_neg` — the first-crossing step: a continuous aperture-indexed bottom
  eigenvalue that is positive at a small aperture and negative at a larger one must vanish somewhere
  in between, which is the zero mode the conservation law excludes.

Everything is stated for an arbitrary real quadratic form on submodules of an arbitrary real vector
space, so the aperture filtration enters only through the inclusion `D a ≤ D b`.
-/

noncomputable section

namespace GaloisForLFunctions.RHTower

open Set

/-! ## The Morse charge -/

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

/-- The trial domain carries a negative-definite subspace of dimension `n`. -/
def HasNegDefSubspaceOfDim (Q : V → ℝ) (D : Submodule ℝ V) (n : ℕ) : Prop :=
  ∃ W : Submodule ℝ V, W ≤ D ∧ Module.finrank ℝ W = n ∧ ∀ v ∈ W, v ≠ 0 → Q v < 0

/-- **Monotonicity of the achievable negative dimensions.**  Every negative-definite subspace of a
smaller trial domain is one of the larger domain, of the same dimension. -/
theorem HasNegDefSubspaceOfDim.mono {Q : V → ℝ} {D D' : Submodule ℝ V} (hDD : D ≤ D') {n : ℕ}
    (h : HasNegDefSubspaceOfDim Q D n) : HasNegDefSubspaceOfDim Q D' n := by
  obtain ⟨W, hWD, hdim, hneg⟩ := h
  exact ⟨W, le_trans hWD hDD, hdim, hneg⟩

/-- The Morse charge: the largest dimension of a negative-definite subspace. -/
def morseCharge (Q : V → ℝ) (D : Submodule ℝ V) : ℕ :=
  sSup {n : ℕ | HasNegDefSubspaceOfDim Q D n}

theorem zero_mem_negDefDims (Q : V → ℝ) (D : Submodule ℝ V) :
    (0 : ℕ) ∈ {n : ℕ | HasNegDefSubspaceOfDim Q D n} := by
  refine ⟨⊥, bot_le, ?_, ?_⟩
  · simp
  · intro v hv hne
    rw [Submodule.mem_bot] at hv
    exact absurd hv hne

/-- **Equation (3).**  The Morse charge is monotone in the trial domain. -/
theorem morseCharge_mono {Q : V → ℝ} {D D' : Submodule ℝ V} (hDD : D ≤ D')
    (hbdd : BddAbove {n : ℕ | HasNegDefSubspaceOfDim Q D' n}) :
    morseCharge Q D ≤ morseCharge Q D' :=
  csSup_le_csSup hbdd ⟨0, zero_mem_negDefDims Q D⟩
    fun _ hn => HasNegDefSubspaceOfDim.mono hDD hn

/-! ## Vanishing of the charge is positivity -/

/-- A single negative vector produces a one-dimensional negative-definite subspace. -/
theorem hasNegDefSubspaceOfDim_one {Q : V → ℝ} {D : Submodule ℝ V}
    (hhom : ∀ (c : ℝ) (v : V), Q (c • v) = c ^ (2 : ℕ) * Q v)
    {v : V} (hv : v ∈ D) (hvne : v ≠ 0) (hQ : Q v < 0) :
    HasNegDefSubspaceOfDim Q D 1 := by
  refine ⟨Submodule.span ℝ {v}, ?_, finrank_span_singleton hvne, ?_⟩
  · rw [Submodule.span_le, Set.singleton_subset_iff]
    exact hv
  · intro w hw hwne
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hw
    have hc : c ≠ 0 := by
      intro hc0
      rw [hc0, zero_smul] at hwne
      exact hwne rfl
    rw [hhom]
    have : 0 < c ^ (2 : ℕ) := by positivity
    exact mul_neg_of_pos_of_neg this hQ

/-- **Equations (ii) ↔ (iii).**  The Morse charge vanishes exactly when the form is nonnegative on
the trial domain. -/
theorem negDefDims_eq_zero_iff_nonneg {Q : V → ℝ} {D : Submodule ℝ V}
    (hhom : ∀ (c : ℝ) (v : V), Q (c • v) = c ^ (2 : ℕ) * Q v) :
    (∀ n, HasNegDefSubspaceOfDim Q D n → n = 0) ↔ ∀ v ∈ D, 0 ≤ Q v := by
  constructor
  · intro h v hv
    by_contra hneg
    rw [not_le] at hneg
    have hvne : v ≠ 0 := by
      intro hv0
      rw [hv0] at hneg
      have : Q (0 : V) = 0 := by
        have := hhom 0 (0 : V)
        rw [zero_smul] at this
        simpa using this
      rw [this] at hneg
      exact absurd hneg (lt_irrefl 0)
    exact absurd (h 1 (hasNegDefSubspaceOfDim_one hhom hv hvne hneg)) one_ne_zero
  · rintro hpos n ⟨W, hWD, hdim, hneg⟩
    by_contra hn
    have hne : W ≠ ⊥ := by
      intro hW
      rw [hW] at hdim
      simp at hdim
      exact hn hdim.symm
    obtain ⟨v, hvW, hvne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
    have h1 := hneg v hvW hvne
    have h2 := hpos v (hWD hvW)
    linarith

/-- **The small-aperture anchor.**  A nonnegative form has vanishing charge. -/
theorem morseCharge_eq_zero_of_nonneg {Q : V → ℝ} {D : Submodule ℝ V}
    (hhom : ∀ (c : ℝ) (v : V), Q (c • v) = c ^ (2 : ℕ) * Q v) (hpos : ∀ v ∈ D, 0 ≤ Q v) :
    morseCharge Q D = 0 := by
  have hzero := (negDefDims_eq_zero_iff_nonneg hhom).mpr hpos
  have hset : {n : ℕ | HasNegDefSubspaceOfDim Q D n} = {0} := by
    apply Set.eq_singleton_iff_unique_mem.mpr
    exact ⟨zero_mem_negDefDims Q D, fun n hn => hzero n hn⟩
  rw [morseCharge, hset, csSup_singleton]

/-! ## The first crossing -/

/-- **Equation (9).**  A continuous aperture-indexed bottom eigenvalue that is positive at a small
aperture and negative at a larger one vanishes somewhere in between: the first zero mode. -/
theorem exists_crossing_of_pos_of_neg {f : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hcont : ContinuousOn f (Icc a b)) (hpos : 0 < f a) (hneg : f b < 0) :
    ∃ c ∈ Ioo a b, f c = 0 := by
  have h := intermediate_value_Ioo' hab hcont
  have hmem : (0 : ℝ) ∈ Ioo (f b) (f a) := ⟨hneg, hpos⟩
  obtain ⟨c, hc, hc0⟩ := h hmem
  exact ⟨c, hc, hc0⟩

end GaloisForLFunctions.RHTower

end
