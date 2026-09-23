import GaloisForLFunctions.RHTower.SuzukiDonoghueHerglotzTransform
import Mathlib.Analysis.InnerProductSpace.Orthonormal

/-!
# Movable-anchor Donoghue weights and Clark source coherence

For a collapsing deficiency base `±ic`, the normalized Donoghue kernel is

`K_c(t,z) = (tz+c²)/(c(t-z))`.

This module proves the exact movable-anchor kernel decomposition, its normalization at `ic`, and
the Nevanlinna-weight/phase-speed law.  It then identifies the finite Clark probability weights
with squared source coherences and applies Bessel's inequality.  Thus a family of `N` orthonormal
extension modes carries total source coherence at most one, so at least one mode has coherence at
most `1/N`.

This is the dependency-closed positive survivor of the real-axis overcrowding obstruction.  It is
unconditional and contains no RH assumption, spectral fitting, numerical computation, or new
axiom.
-/

open Complex Finset

namespace GaloisForLFunctions.RHTower

noncomputable section

/-! ## Exact movable-anchor Donoghue kernel -/

/-- Donoghue kernel normalized at the movable upper-half-plane anchor `ic`. -/
def suzukiMovableDonoghueKernel (c t : ℝ) (z : ℂ) : ℂ :=
  ((t : ℂ) * z + (c : ℂ) ^ (2 : ℕ)) /
    ((c : ℂ) * ((t : ℂ) - z))

/-- The movable Donoghue kernel is exactly normalized to `i` at `z = ic`. -/
@[simp] theorem suzukiMovableDonoghueKernel_anchor
    {c : ℝ} (hc : c ≠ 0) (t : ℝ) :
    suzukiMovableDonoghueKernel c t ((c : ℂ) * I) = I := by
  rw [suzukiMovableDonoghueKernel]
  have hden : (c : ℂ) * ((t : ℂ) - (c : ℂ) * I) ≠ 0 := by
    refine mul_ne_zero (ofReal_ne_zero.mpr hc) ?_
    intro h
    have him := congrArg im h
    simp [hc] at him
  apply (div_eq_iff hden).2
  ring_nf
  simp

/-- Exact Nevanlinna decomposition of the movable kernel. -/
theorem suzukiMovableDonoghueKernel_eq_nevanlinna
    {c : ℝ} (hc : c ≠ 0) {t : ℝ} {z : ℂ}
    (htz : (t : ℂ) - z ≠ 0) :
    suzukiMovableDonoghueKernel c t z =
      (((t : ℂ) ^ (2 : ℕ) + (c : ℂ) ^ (2 : ℕ)) /
          ((c : ℂ) * ((t : ℂ) - z))) - (t : ℂ) / c := by
  rw [suzukiMovableDonoghueKernel]
  field_simp [ofReal_ne_zero.mpr hc, htz]
  ring

/-- Nevanlinna mass contributed by a Clark atom of probability `p` at the real point `x`. -/
def suzukiMovableNevanlinnaWeight (c x p : ℝ) : ℝ :=
  (x ^ (2 : ℕ) + c ^ (2 : ℕ)) * p / c

theorem suzukiMovableNevanlinnaWeight_pos
    {c x p : ℝ} (hc : 0 < c) (hp : 0 < p) :
    0 < suzukiMovableNevanlinnaWeight c x p := by
  rw [suzukiMovableNevanlinnaWeight]
  positivity

/-- A probability atom times the movable kernel has Nevanlinna pole weight
`(x²+c²)p/c`, with the remaining term affine and pole-free. -/
theorem mul_suzukiMovableDonoghueKernel_eq_weightedPole
    {c : ℝ} (hc : c ≠ 0) {x p : ℝ} {z : ℂ}
    (hxz : (x : ℂ) - z ≠ 0) :
    (p : ℂ) * suzukiMovableDonoghueKernel c x z =
      (suzukiMovableNevanlinnaWeight c x p : ℂ) /
          ((x : ℂ) - z) - (p * x / c : ℝ) := by
  rw [suzukiMovableDonoghueKernel_eq_nevanlinna hc hxz,
    suzukiMovableNevanlinnaWeight]
  push_cast
  field_simp [ofReal_ne_zero.mpr hc, hxz]

/-- Clark boundary phase speed is the reciprocal of half the Nevanlinna atom mass. -/
def suzukiMovableClarkPhaseSpeed (c x p : ℝ) : ℝ :=
  2 / suzukiMovableNevanlinnaWeight c x p

/-- Exact movable-anchor phase-speed law, equation `(60)` of the paper card. -/
theorem suzukiMovableClarkPhaseSpeed_eq
    {c x p : ℝ} (hc : c ≠ 0) (hp : p ≠ 0) :
    suzukiMovableClarkPhaseSpeed c x p =
      2 * c / ((x ^ (2 : ℕ) + c ^ (2 : ℕ)) * p) := by
  rw [suzukiMovableClarkPhaseSpeed, suzukiMovableNevanlinnaWeight]
  have hs : x ^ (2 : ℕ) + c ^ (2 : ℕ) ≠ 0 := by positivity
  field_simp [hc, hp, hs]

/-! ## Source coherence and exact fragmentation -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- Squared cosine of the Hilbert-space angle between two nonzero source vectors.  The zero-vector
convention is harmless and keeps the expression total. -/
def suzukiSourceCoherence (anchor mode : E) : ℝ :=
  ‖inner ℂ anchor mode‖ ^ (2 : ℕ) / (‖anchor‖ ^ (2 : ℕ) * ‖mode‖ ^ (2 : ℕ))

theorem suzukiSourceCoherence_nonneg (anchor mode : E) :
    0 ≤ suzukiSourceCoherence anchor mode := by
  rw [suzukiSourceCoherence]
  positivity

/-- For normalized source and mode vectors, source coherence is exactly the squared spectral
overlap that appears as the Clark probability atom. -/
theorem suzukiSourceCoherence_of_norm_eq_one
    {anchor mode : E} (hanchor : ‖anchor‖ = 1) (hmode : ‖mode‖ = 1) :
    suzukiSourceCoherence anchor mode = ‖inner ℂ anchor mode‖ ^ (2 : ℕ) := by
  simp [suzukiSourceCoherence, hanchor, hmode]

theorem suzukiSourceCoherence_le_one (anchor mode : E) :
    suzukiSourceCoherence anchor mode ≤ 1 := by
  by_cases ha : anchor = 0
  · simp [suzukiSourceCoherence, ha]
  by_cases hm : mode = 0
  · simp [suzukiSourceCoherence, hm]
  have ha_pos : 0 < ‖anchor‖ := norm_pos_iff.mpr ha
  have hm_pos : 0 < ‖mode‖ := norm_pos_iff.mpr hm
  have hcs := norm_inner_le_norm (𝕜 := ℂ) anchor mode
  have hinner_nonneg : 0 ≤ ‖inner ℂ anchor mode‖ := norm_nonneg _
  have hproduct_nonneg : 0 ≤ ‖anchor‖ * ‖mode‖ := mul_nonneg (norm_nonneg _) (norm_nonneg _)
  have hfactor := mul_nonneg (sub_nonneg.mpr hcs)
    (add_nonneg hproduct_nonneg hinner_nonneg)
  rw [suzukiSourceCoherence, div_le_one]
  · nlinarith
  · positivity

/-- **Clark coherence budget.**  Every finite orthonormal family receives total normalized
source probability at most one. -/
theorem sum_suzukiSourceCoherence_le_one
    {ι : Type*} [Fintype ι] {anchor : E} {mode : ι → E}
    (hanchor : ‖anchor‖ = 1) (hmode : Orthonormal ℂ mode) :
    ∑ i, suzukiSourceCoherence anchor (mode i) ≤ 1 := by
  have hb := hmode.sum_inner_products_le anchor (s := Finset.univ)
  simpa [suzukiSourceCoherence, hanchor, hmode.norm_eq_one,
    norm_inner_symm] using hb

/-- **Exact fragmentation consequence.**  Among `N` orthonormal Clark modes, one has source
coherence at most `1/N`. -/
theorem exists_suzukiSourceCoherence_le_card_inv
    {ι : Type*} [Fintype ι] [Nonempty ι]
    {anchor : E} {mode : ι → E}
    (hanchor : ‖anchor‖ = 1) (hmode : Orthonormal ℂ mode) :
    ∃ i, suzukiSourceCoherence anchor (mode i) ≤
      1 / (Fintype.card ι : ℝ) := by
  have hsum := sum_suzukiSourceCoherence_le_one hanchor hmode
  have hcard : (Fintype.card ι : ℝ) ≠ 0 := by
    exact_mod_cast (Fintype.card_pos.ne' : Fintype.card ι ≠ 0)
  have hconst :
      ∑ _i : ι, (1 / (Fintype.card ι : ℝ)) = 1 := by
    simp [hcard]
  have hle :
      ∑ i : ι, suzukiSourceCoherence anchor (mode i) ≤
        ∑ _i : ι, (1 / (Fintype.card ι : ℝ)) := by
    simpa [hconst] using hsum
  obtain ⟨i, -, hi⟩ :=
    Finset.exists_le_of_sum_le Finset.univ_nonempty hle
  exact ⟨i, hi⟩

/-- Conversely, a uniform positive coherence floor bounds the number of orthonormal Clark modes. -/
theorem card_mul_le_one_of_suzukiSourceCoherence_floor
    {ι : Type*} [Fintype ι] {anchor : E} {mode : ι → E} {epsilon : ℝ}
    (hanchor : ‖anchor‖ = 1) (hmode : Orthonormal ℂ mode)
    (hfloor : ∀ i, epsilon ≤ suzukiSourceCoherence anchor (mode i)) :
    (Fintype.card ι : ℝ) * epsilon ≤ 1 := by
  calc
    (Fintype.card ι : ℝ) * epsilon = ∑ _i : ι, epsilon := by simp
    _ ≤ ∑ i : ι, suzukiSourceCoherence anchor (mode i) :=
      Finset.sum_le_sum fun i _ => hfloor i
    _ ≤ 1 := sum_suzukiSourceCoherence_le_one hanchor hmode

end

end GaloisForLFunctions.RHTower
