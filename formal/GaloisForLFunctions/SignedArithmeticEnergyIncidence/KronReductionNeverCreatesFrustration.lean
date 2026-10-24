import GaloisForLFunctions.SignedArithmeticEnergyIncidence.PositivityIsDecidedOnTheFrustrationTerminals

/-!
# Kron reduction never creates frustration

Let every anti-aligned overlap of a signed incidence form have both ends in the terminal set `T`,
and let the form be coercive on profiles vanishing on `T`.

* **Harmonic extensions are nonnegative** (`HarmonicFrame.h_nonneg`).  The extension `h_τ` has
  boundary values `1_τ ≥ 0`; `|h_τ|` has the same ones, and passing to absolute values does not
  raise the energy of a form whose overlaps are aligned or join two nonnegative values
  (`incidenceEnergy_abs_le_of_aligned_off`).  Since `h_τ` is harmonic off `T`,
  `E(|h_τ| − h_τ) = E(|h_τ|) − E(h_τ) ≤ 0`, and coercivity forces `|h_τ| = h_τ`.
* **The reduction lowers every terminal charge** (`HarmonicFrame.reduced_eq_sub_conductance`):
  `R_στ = c_στ − β_στ` with the effective conductance `β_στ = −Σ_{i ∉ T} c_σi h_τ(i) ≥ 0`
  (`HarmonicFrame.conductance_nonneg`).  So an aligned terminal pair stays aligned and every
  anti-aligned pair of `R` is an anti-aligned overlap of `c` (`HarmonicFrame.pos_of_reduced_pos`):
  Kron reduction never creates frustration.
* **Healing** (`nonneg_iff_payable_of_healed`): if every terminal pair carries a charge at most
  its effective conductance, the reduced form is aligned, and the form is nonnegative iff its
  interior and its reduced form are locally payable.  The healing test is pairwise, whatever the
  number of terminals; for one pair it is the aligned side `t ≤ β` of the two-terminal law
  `(t − β)² ≤ αγ` (`nonneg_iff_two_terminal`).
-/

open Finset

namespace GaloisForLFunctions.SignedArithmeticEnergyIncidence

noncomputable section
set_option autoImplicit false

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {c : ι → ι → ℝ} {T : Finset ι}

omit [DecidableEq ι] in
/-- **Absolute values do not raise the energy** when every overlap off `T × T` is aligned and the
profile is nonnegative on `T`. -/
theorem incidenceEnergy_abs_le_of_aligned_off
    (hT : ∀ i j, i ≠ j → ¬(i ∈ T ∧ j ∈ T) → c i j ≤ 0) {g : ι → ℝ} (hg : ∀ τ ∈ T, 0 ≤ g τ) :
    incidenceEnergy c (fun i => |g i|) ≤ incidenceEnergy c g := by
  unfold incidenceEnergy
  refine sum_le_sum fun i _ => sum_le_sum fun j _ => ?_
  show c i j * |g i| * |g j| ≤ c i j * g i * g j
  by_cases hij : i = j
  · subst hij
    rw [mul_assoc, mul_assoc, abs_mul_abs_self]
  · by_cases hin : i ∈ T ∧ j ∈ T
    · rw [abs_of_nonneg (hg i hin.1), abs_of_nonneg (hg j hin.2)]
    · have hc := hT i j hij hin
      have h1 : g i * g j ≤ |g i| * |g j| := by rw [← abs_mul]; exact le_abs_self _
      nlinarith

/-- **Harmonic extensions through an aligned interior are nonnegative.** -/
theorem HarmonicFrame.h_nonneg (hc : IsSymmetricCoupling c)
    (hT : ∀ i j, i ≠ j → ¬(i ∈ T ∧ j ∈ T) → c i j ≤ 0) {δ : ℝ} (hδ : 0 < δ)
    (hcoer : ∀ g : ι → ℝ, (∀ τ ∈ T, g τ = 0) → δ * ∑ i, g i ^ 2 ≤ incidenceEnergy c g)
    (H : HarmonicFrame c T) {τ : ι} (hτ : τ ∈ T) (i : ι) : 0 ≤ H.h τ i := by
  have hbd : ∀ σ ∈ T, 0 ≤ H.h τ σ := fun σ hσ => by
    rw [H.boundary τ hτ σ hσ]; split_ifs <;> norm_num
  have hsub : incidenceEnergy c (fun i => |H.h τ i| - H.h τ i) =
      incidenceEnergy c (fun i => |H.h τ i|) -
        2 * ∑ i, |H.h τ i| * couplingAction c (H.h τ) i + incidenceEnergy c (H.h τ) :=
    incidenceEnergy_sub hc _ (H.h τ)
  have hcross : ∑ i, |H.h τ i| * couplingAction c (H.h τ) i = incidenceEnergy c (H.h τ) := by
    rw [incidenceEnergy_eq_sum_mul_couplingAction]
    refine sum_congr rfl fun i _ => ?_
    by_cases hi : i ∈ T
    · rw [abs_of_nonneg (hbd i hi)]
    · rw [H.harmonic τ hτ i hi, mul_zero, mul_zero]
  have habs := incidenceEnergy_abs_le_of_aligned_off hT hbd
  have hco := hcoer (fun i => |H.h τ i| - H.h τ i) fun σ hσ => by
    rw [abs_of_nonneg (hbd σ hσ), sub_self]
  rw [hsub, hcross] at hco
  have h0 : 0 ≤ ∑ i, (|H.h τ i| - H.h τ i) ^ 2 := sum_nonneg fun i _ => sq_nonneg _
  have hsq : ∑ i, (|H.h τ i| - H.h τ i) ^ 2 = 0 := by nlinarith
  have hi := (sum_eq_zero_iff_of_nonneg fun i _ => sq_nonneg (|H.h τ i| - H.h τ i)).mp hsq i
    (mem_univ i)
  have h1 := (pow_eq_zero_iff two_ne_zero).mp hi
  linarith [abs_nonneg (H.h τ i)]

/-- The effective conductance `β_στ = −Σ_{i ∉ T} c_σi h_τ(i)` of the interior. -/
def HarmonicFrame.conductance (H : HarmonicFrame c T) (σ τ : ι) : ℝ :=
  -∑ i ∈ univ.filter (· ∉ T), c σ i * H.h τ i

/-- **The reduced charge is the charge minus the effective conductance**: `R_στ = c_στ − β_στ`. -/
theorem HarmonicFrame.reduced_eq_sub_conductance (H : HarmonicFrame c T) {σ τ : ι} (hσ : σ ∈ T)
    (hτ : τ ∈ T) : H.reduced σ τ = c σ τ - H.conductance σ τ := by
  unfold HarmonicFrame.reduced HarmonicFrame.conductance couplingAction
  rw [if_pos ⟨hσ, hτ⟩, ← sum_filter_add_sum_filter_not univ (· ∈ T), sub_neg_eq_add]
  congr 1
  rw [sum_congr rfl fun i hi => by rw [H.boundary τ hτ i (mem_filter.mp hi).2]]
  simp only [mul_ite, mul_one, mul_zero]
  rw [sum_ite_eq' (univ.filter (· ∈ T)) τ (fun i => c σ i), if_pos (mem_filter.mpr ⟨mem_univ τ, hτ⟩)]

/-- **The effective conductance of an aligned interior is nonnegative.** -/
theorem HarmonicFrame.conductance_nonneg (hc : IsSymmetricCoupling c)
    (hT : ∀ i j, i ≠ j → ¬(i ∈ T ∧ j ∈ T) → c i j ≤ 0) {δ : ℝ} (hδ : 0 < δ)
    (hcoer : ∀ g : ι → ℝ, (∀ τ ∈ T, g τ = 0) → δ * ∑ i, g i ^ 2 ≤ incidenceEnergy c g)
    (H : HarmonicFrame c T) {σ τ : ι} (hσ : σ ∈ T) (hτ : τ ∈ T) : 0 ≤ H.conductance σ τ := by
  unfold HarmonicFrame.conductance
  rw [neg_nonneg]
  refine sum_nonpos fun i hi => ?_
  have hiT := (mem_filter.mp hi).2
  have hσi : σ ≠ i := fun h => hiT (h ▸ hσ)
  have h1 := hT σ i hσi fun h => hiT h.2
  have h2 := H.h_nonneg hc hT hδ hcoer hτ i
  nlinarith

/-- **Kron reduction never creates frustration**: every positive reduced charge comes from a
positive charge, `0 < R_στ → 0 < c_στ`. -/
theorem HarmonicFrame.pos_of_reduced_pos (hc : IsSymmetricCoupling c)
    (hT : ∀ i j, i ≠ j → ¬(i ∈ T ∧ j ∈ T) → c i j ≤ 0) {δ : ℝ} (hδ : 0 < δ)
    (hcoer : ∀ g : ι → ℝ, (∀ τ ∈ T, g τ = 0) → δ * ∑ i, g i ^ 2 ≤ incidenceEnergy c g)
    (H : HarmonicFrame c T) {σ τ : ι} (hσ : σ ∈ T) (hτ : τ ∈ T) (hR : 0 < H.reduced σ τ) :
    0 < c σ τ := by
  rw [H.reduced_eq_sub_conductance hσ hτ] at hR
  linarith [H.conductance_nonneg hc hT hδ hcoer hσ hτ]

/-- **Healing**: if every pair of terminals carries a charge at most its effective conductance,
the form is nonnegative iff its interior and its reduced form are locally payable. -/
theorem nonneg_iff_payable_of_healed (hc : IsSymmetricCoupling c)
    (hT : ∀ i j, i ≠ j → 0 < c i j → i ∈ T ∧ j ∈ T) (H : HarmonicFrame c T)
    (hheal : ∀ σ ∈ T, ∀ τ ∈ T, σ ≠ τ → c σ τ ≤ H.conductance σ τ) :
    (∀ f, 0 ≤ incidenceEnergy c f) ↔
      LocallyPayable (interiorCoupling c T) ∧ LocallyPayable H.reduced := by
  have halign : HasNonpositiveOverlaps H.reduced := by
    intro σ τ hστ
    by_cases h : σ ∈ T ∧ τ ∈ T
    · rw [H.reduced_eq_sub_conductance h.1 h.2]
      linarith [hheal σ h.1 τ h.2 hστ]
    · simp only [HarmonicFrame.reduced, if_neg h, le_refl]
  rw [nonneg_iff_interior_payable_and_reduced hc hT H,
    nonneg_iff_locallyPayable_of_isBalanced (H.reduced_symm hc) (isBalanced_of_aligned halign)]

end

end GaloisForLFunctions.SignedArithmeticEnergyIncidence
