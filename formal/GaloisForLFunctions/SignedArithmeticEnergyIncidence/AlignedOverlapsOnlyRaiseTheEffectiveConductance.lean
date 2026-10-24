import GaloisForLFunctions.SignedArithmeticEnergyIncidence.KronReductionNeverCreatesFrustration

/-!
# Aligned overlaps only raise the effective conductance

Two monotonicity laws for the Kron reduction of a signed incidence form through an aligned
interior, coercive on profiles vanishing on the terminal set `T`.

* **Discrete minimum principle** (`nonneg_of_action_nonneg`): a profile vanishing on `T` whose
  coupling action is nonnegative off `T` is nonnegative.  With `ψ = ψ⁺ − ψ⁻`, the pairing
  `⟨ψ⁻, Cψ⟩ ≥ 0` while `⟨ψ⁻, Cψ⁺⟩ ≤ 0` (disjoint supports, aligned overlaps), so
  `E(ψ⁻) ≤ 0` and coercivity forces `ψ⁻ = 0`.
* **Rayleigh monotonicity** (`HarmonicFrame.h_mono`, `HarmonicFrame.conductance_mono`): if `c'`
  has the same budgets as `c` and every overlap off `T × T` at least as aligned, `c'_ij ≤ c_ij ≤ 0`,
  then the harmonic extensions grow, `h_τ ≤ h'_τ`, and so do all effective conductances,
  `β_στ ≤ β'_στ`.  The difference `h'_τ − h_τ` vanishes on `T` and has action
  `−Σ_j (c'_ij − c_ij) h_τ(j) ≥ 0` off `T`.
* **Healing is monotone** (`healed_mono`): strengthening aligned overlaps keeps every healed
  terminal pair healed, so positivity stays local payment (`nonneg_iff_payable_of_healed`).
  Adding interior points with aligned overlaps is the case of points that start decoupled.
-/

open Finset

namespace GaloisForLFunctions.SignedArithmeticEnergyIncidence

noncomputable section
set_option autoImplicit false

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {c : ι → ι → ℝ} {T : Finset ι}

/-- **Discrete minimum principle**: through an aligned interior coercive on profiles vanishing
on `T`, a profile vanishing on `T` with nonnegative action off `T` is nonnegative. -/
theorem nonneg_of_action_nonneg
    (hT : ∀ i j, i ≠ j → ¬(i ∈ T ∧ j ∈ T) → c i j ≤ 0) {δ : ℝ} (hδ : 0 < δ)
    (hcoer : ∀ g : ι → ℝ, (∀ τ ∈ T, g τ = 0) → δ * ∑ i, g i ^ 2 ≤ incidenceEnergy c g)
    {ψ : ι → ℝ} (hψT : ∀ τ ∈ T, ψ τ = 0) (hact : ∀ i ∉ T, 0 ≤ couplingAction c ψ i) (i : ι) :
    0 ≤ ψ i := by
  set m : ι → ℝ := fun j => max (-ψ j) 0 with hm
  set p : ι → ℝ := fun j => max (ψ j) 0 with hp
  have hm0 : ∀ j, 0 ≤ m j := fun j => le_max_right _ _
  have hdec : ∀ j, ψ j = p j - m j := fun j => by
    simp only [hp, hm]; rcases le_total 0 (ψ j) with h | h
    · rw [max_eq_left h, max_eq_right (by linarith)]; ring
    · rw [max_eq_right h, max_eq_left (by linarith)]; ring
  have hdisj : ∀ j, p j * m j = 0 := fun j => by
    simp only [hp, hm]; rcases le_total 0 (ψ j) with h | h
    · rw [max_eq_right (by linarith : -ψ j ≤ 0), mul_zero]
    · rw [max_eq_right h, zero_mul]
  have hmT : ∀ τ ∈ T, m τ = 0 := fun τ hτ => by simp only [hm, hψT τ hτ, neg_zero, max_self]
  -- `⟨ψ⁻, Cψ⟩ ≥ 0`
  have h1 : 0 ≤ ∑ i, m i * couplingAction c ψ i := sum_nonneg fun i _ => by
    by_cases hi : i ∈ T
    · rw [hmT i hi, zero_mul]
    · exact mul_nonneg (hm0 i) (hact i hi)
  -- `⟨ψ⁻, Cψ⟩ = ⟨ψ⁻, Cψ⁺⟩ − E(ψ⁻)` and `⟨ψ⁻, Cψ⁺⟩ ≤ 0`
  have hsplit : ∑ i, m i * couplingAction c ψ i =
      ∑ i, ∑ j, c i j * m i * p j - incidenceEnergy c m := by
    unfold couplingAction incidenceEnergy
    rw [← sum_sub_distrib]
    refine sum_congr rfl fun i _ => ?_
    rw [mul_sum, ← sum_sub_distrib]
    exact sum_congr rfl fun j _ => by rw [hdec j]; ring
  have h2 : ∑ i, ∑ j, c i j * m i * p j ≤ 0 := sum_nonpos fun i _ => sum_nonpos fun j _ => by
    by_cases hij : i = j
    · subst hij
      rw [mul_assoc, mul_comm (m i), hdisj i, mul_zero]
    · by_cases hin : i ∈ T ∧ j ∈ T
      · rw [hmT i hin.1, mul_zero, zero_mul]
      · have := hT i j hij hin
        have hpj : 0 ≤ p j := le_max_right _ _
        nlinarith [mul_nonneg (hm0 i) hpj]
  have hE := hcoer m hmT
  have hsq : ∑ j, m j ^ 2 = 0 := by
    have h0 : 0 ≤ ∑ j, m j ^ 2 := sum_nonneg fun j _ => sq_nonneg _
    nlinarith
  have hmi := (sum_eq_zero_iff_of_nonneg fun j _ => sq_nonneg (m j)).mp hsq i (mem_univ i)
  have hmi' : m i = 0 := (pow_eq_zero_iff two_ne_zero).mp hmi
  have : max (-ψ i) 0 = 0 := hmi'
  have := le_max_left (-ψ i) 0
  linarith

variable {c' : ι → ι → ℝ}

/-- **Rayleigh monotonicity of the harmonic extensions**: with equal budgets and every overlap
off `T × T` at least as aligned, `h_τ ≤ h'_τ`. -/
theorem HarmonicFrame.h_mono (hc : IsSymmetricCoupling c)
    (hT : ∀ i j, i ≠ j → ¬(i ∈ T ∧ j ∈ T) → c i j ≤ 0)
    (hle : ∀ i j, i ≠ j → ¬(i ∈ T ∧ j ∈ T) → c' i j ≤ c i j) (hdiag : ∀ i, c' i i = c i i)
    {δ : ℝ} (hδ : 0 < δ)
    (hcoer : ∀ g : ι → ℝ, (∀ τ ∈ T, g τ = 0) → δ * ∑ i, g i ^ 2 ≤ incidenceEnergy c g)
    (hcoer' : ∀ g : ι → ℝ, (∀ τ ∈ T, g τ = 0) → δ * ∑ i, g i ^ 2 ≤ incidenceEnergy c' g)
    (H : HarmonicFrame c T) (H' : HarmonicFrame c' T) {τ : ι} (hτ : τ ∈ T) (i : ι) :
    H.h τ i ≤ H'.h τ i := by
  have hT' : ∀ i j, i ≠ j → ¬(i ∈ T ∧ j ∈ T) → c' i j ≤ 0 := fun i j hij hin =>
    (hle i j hij hin).trans (hT i j hij hin)
  have hh0 := H.h_nonneg hc hT hδ hcoer hτ
  set φ : ι → ℝ := fun j => H'.h τ j - H.h τ j
  have hφT : ∀ σ ∈ T, φ σ = 0 := fun σ hσ => by
    simp only [φ, H'.boundary τ hτ σ hσ, H.boundary τ hτ σ hσ, sub_self]
  have hact : ∀ k ∉ T, 0 ≤ couplingAction c' φ k := by
    intro k hk
    have e1 : couplingAction c' φ k = couplingAction c' (H'.h τ) k - couplingAction c' (H.h τ) k := by
      unfold couplingAction; rw [← sum_sub_distrib]; exact sum_congr rfl fun j _ => by ring
    have e2 : couplingAction c' (H.h τ) k =
        couplingAction c (H.h τ) k + ∑ j, (c' k j - c k j) * H.h τ j := by
      unfold couplingAction; rw [← sum_add_distrib]; exact sum_congr rfl fun j _ => by ring
    rw [e1, e2, H'.harmonic τ hτ k hk, H.harmonic τ hτ k hk, zero_sub, zero_add, neg_nonneg]
    refine sum_nonpos fun j _ => ?_
    by_cases hkj : k = j
    · subst hkj; rw [hdiag k, sub_self, zero_mul]
    · exact mul_nonpos_of_nonpos_of_nonneg (by linarith [hle k j hkj fun h => hk h.1]) (hh0 j)
  have := nonneg_of_action_nonneg hT' hδ hcoer' hφT hact i
  simp only [φ] at this
  linarith

/-- **Rayleigh monotonicity of the effective conductance**: `β_στ ≤ β'_στ`. -/
theorem HarmonicFrame.conductance_mono (hc : IsSymmetricCoupling c)
    (hT : ∀ i j, i ≠ j → ¬(i ∈ T ∧ j ∈ T) → c i j ≤ 0)
    (hle : ∀ i j, i ≠ j → ¬(i ∈ T ∧ j ∈ T) → c' i j ≤ c i j) (hdiag : ∀ i, c' i i = c i i)
    {δ : ℝ} (hδ : 0 < δ)
    (hcoer : ∀ g : ι → ℝ, (∀ τ ∈ T, g τ = 0) → δ * ∑ i, g i ^ 2 ≤ incidenceEnergy c g)
    (hcoer' : ∀ g : ι → ℝ, (∀ τ ∈ T, g τ = 0) → δ * ∑ i, g i ^ 2 ≤ incidenceEnergy c' g)
    (H : HarmonicFrame c T) (H' : HarmonicFrame c' T) {σ τ : ι} (hσ : σ ∈ T) (hτ : τ ∈ T) :
    H.conductance σ τ ≤ H'.conductance σ τ := by
  unfold HarmonicFrame.conductance
  rw [neg_le_neg_iff]
  refine sum_le_sum fun i hi => ?_
  have hiT := (mem_filter.mp hi).2
  have hσi : σ ≠ i := fun h => hiT (h ▸ hσ)
  have hn : ¬(σ ∈ T ∧ i ∈ T) := fun h => hiT h.2
  have h1 := hle σ i hσi hn
  have h2 := hT σ i hσi hn
  have h3 := H.h_nonneg hc hT hδ hcoer hτ i
  have h4 := H.h_mono hc hT hle hdiag hδ hcoer hcoer' H' hτ i
  nlinarith

/-- **Healing is monotone**: strengthening aligned overlaps keeps every healed pair healed. -/
theorem healed_mono (hc : IsSymmetricCoupling c)
    (hT : ∀ i j, i ≠ j → ¬(i ∈ T ∧ j ∈ T) → c i j ≤ 0)
    (hle : ∀ i j, i ≠ j → ¬(i ∈ T ∧ j ∈ T) → c' i j ≤ c i j) (hdiag : ∀ i, c' i i = c i i)
    {δ : ℝ} (hδ : 0 < δ)
    (hcoer : ∀ g : ι → ℝ, (∀ τ ∈ T, g τ = 0) → δ * ∑ i, g i ^ 2 ≤ incidenceEnergy c g)
    (hcoer' : ∀ g : ι → ℝ, (∀ τ ∈ T, g τ = 0) → δ * ∑ i, g i ^ 2 ≤ incidenceEnergy c' g)
    (H : HarmonicFrame c T) (H' : HarmonicFrame c' T)
    (hTT : ∀ σ ∈ T, ∀ τ ∈ T, c' σ τ ≤ c σ τ)
    (hheal : ∀ σ ∈ T, ∀ τ ∈ T, σ ≠ τ → c σ τ ≤ H.conductance σ τ) :
    ∀ σ ∈ T, ∀ τ ∈ T, σ ≠ τ → c' σ τ ≤ H'.conductance σ τ := fun σ hσ τ hτ hστ =>
  (hTT σ hσ τ hτ).trans ((hheal σ hσ τ hτ hστ).trans
    (H.conductance_mono hc hT hle hdiag hδ hcoer hcoer' H' hσ hτ))

end

end GaloisForLFunctions.SignedArithmeticEnergyIncidence
