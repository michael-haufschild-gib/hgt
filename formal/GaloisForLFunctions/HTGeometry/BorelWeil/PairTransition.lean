import GaloisForLFunctions.HTGeometry.BorelWeil.SimpleReflectionMinors

/-!
# The transition function of a `ℙ¹` fibre

The two cells of a coset pair `{σ, σ s_i}` trivialize `L_λ` by `cellTriv σ λ` and
`cellTriv (σ s_i) λ`, and the quotient of the two trivializations is, up to sign, the `d`-th power
of the ratio of the two exceptional minors, where `d = λ_i − λ_{i+1}` is the pairing of the weight
with the coroot.  That is the transition function of `O(d)` on the fibre `ℙ¹`.

## Main definitions

* `fibreCoord` — the ratio of the two exceptional minors.

## Main results

* `cellTriv_div_cellTriv_swapNext` — the transition function is `± fibreCoord ^ d`.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace GaloisForLFunctions.HTGeometry.BorelWeil

open Matrix MvPolynomial

variable {N : ℕ} {k : Type*} [Field k] [Infinite k]

theorem minorUnit_mul_swapNext_of_le (σ : Equiv.Perm (Fin N)) {i : Fin N} (hi : (i : ℕ) + 1 < N)
    {j : ℕ} (hj : j ≤ (i : ℕ)) (hjN : j ≤ N) :
    minorUnit (k := k) (σ * swapNext i hi) j hjN = minorUnit σ j hjN := by
  refine Units.ext ?_
  rw [coe_minorUnit, coe_minorUnit, minorPolyAt_mul_swapNext_of_le σ hi hj]

theorem minorUnit_mul_swapNext_of_gt (σ : Equiv.Perm (Fin N)) {i : Fin N} (hi : (i : ℕ) + 1 < N)
    {j : ℕ} (hj : (i : ℕ) + 1 < j) (hjN : j ≤ N) :
    minorUnit (k := k) (σ * swapNext i hi) j hjN = - minorUnit σ j hjN := by
  refine Units.ext ?_
  rw [coe_minorUnit, Units.val_neg, coe_minorUnit, minorPolyAt_mul_swapNext_of_gt σ hi hj, map_neg]

theorem minorUnit_congr (σ : Equiv.Perm (Fin N)) {j j' : ℕ} (h : j = j') (hj : j ≤ N)
    (hj' : j' ≤ N) : minorUnit (k := k) σ j hj = minorUnit σ j' hj' := by
  subst h
  rfl

theorem div_div_div_cancel_right_units (a b c : (FlagLoc N k)ˣ) : a / c / (b / c) = a / b := by
  rw [div_div_div_comm, div_self', div_one]

/-- The `ℙ¹`-coordinate of the fibre through the cells `σ` and `σ s_i`. -/
noncomputable def fibreCoord (σ : Equiv.Perm (Fin N)) {i : Fin N} (hi : (i : ℕ) + 1 < N) :
    (FlagLoc N k)ˣ :=
  minorUnit σ ((i : ℕ) + 1) (le_of_lt hi)
    / minorUnit (σ * swapNext i hi) ((i : ℕ) + 1) (le_of_lt hi)

theorem diagRatio_div_of_lt (σ : Equiv.Perm (Fin N)) {i : Fin N} (hi : (i : ℕ) + 1 < N)
    {l : Fin N} (hl : (l : ℕ) < (i : ℕ)) :
    diagRatio (k := k) σ l / diagRatio (σ * swapNext i hi) l = 1 := by
  rw [diagRatio, diagRatio, minorUnit_mul_swapNext_of_le σ hi (by omega) l.isLt,
    minorUnit_mul_swapNext_of_le σ hi (by omega) (le_of_lt l.isLt), div_self']

theorem diagRatio_div_of_gt (σ : Equiv.Perm (Fin N)) {i : Fin N} (hi : (i : ℕ) + 1 < N)
    {l : Fin N} (hl : (i : ℕ) + 1 < (l : ℕ)) :
    diagRatio (k := k) σ l / diagRatio (σ * swapNext i hi) l = 1 := by
  rw [diagRatio, diagRatio, minorUnit_mul_swapNext_of_gt σ hi (by omega) l.isLt,
    minorUnit_mul_swapNext_of_gt σ hi (by omega) (le_of_lt l.isLt), neg_div_neg_eq, div_self']

theorem diagRatio_div_self (σ : Equiv.Perm (Fin N)) {i : Fin N} (hi : (i : ℕ) + 1 < N) :
    diagRatio (k := k) σ i / diagRatio (σ * swapNext i hi) i = fibreCoord σ hi := by
  rw [diagRatio, diagRatio, minorUnit_mul_swapNext_of_le σ hi (le_refl _) (le_of_lt i.isLt),
    fibreCoord, div_div_div_cancel_right_units]

theorem diagRatio_div_succ (σ : Equiv.Perm (Fin N)) {i : Fin N} (hi : (i : ℕ) + 1 < N)
    {l : Fin N} (hl : (l : ℕ) = (i : ℕ) + 1) :
    diagRatio (k := k) σ l / diagRatio (σ * swapNext i hi) l = -(fibreCoord σ hi)⁻¹ := by
  rw [diagRatio, diagRatio, minorUnit_mul_swapNext_of_gt σ hi (by omega) l.isLt,
    minorUnit_congr (k := k) (σ * swapNext i hi) hl (le_of_lt l.isLt) (le_of_lt hi),
    minorUnit_congr (k := k) σ hl (le_of_lt l.isLt) (le_of_lt hi), fibreCoord]
  rw [inv_div, div_div_div_comm, div_neg, neg_div, div_self', one_div, inv_div]

end GaloisForLFunctions.HTGeometry.BorelWeil

namespace GaloisForLFunctions.HTGeometry.BorelWeil

open Matrix MvPolynomial

variable {N : ℕ} {k : Type*} [Field k] [Infinite k]

/-- **The transition function of the fibre.**  The two cell trivializations of `L_λ` differ by the
`d`-th power of the fibre coordinate, where `d = λ_i − λ_{i+1}`, up to a sign. -/
theorem cellTriv_div_cellTriv_swapNext (σ : Equiv.Perm (Fin N)) {i : Fin N} (hi : (i : ℕ) + 1 < N)
    (lam : Fin N → ℤ) :
    cellTriv (k := k) σ lam / cellTriv (σ * swapNext i hi) lam
      = (fibreCoord σ hi) ^ (lam i - lam ⟨(i : ℕ) + 1, hi⟩)
        * (-1 : (FlagLoc N k)ˣ) ^ (lam ⟨(i : ℕ) + 1, hi⟩) := by
  classical
  have hne : i ≠ (⟨(i : ℕ) + 1, hi⟩ : Fin N) := by
    intro hc
    have h := congrArg (Fin.val) hc
    simp at h
  have hstep : cellTriv (k := k) σ lam / cellTriv (σ * swapNext i hi) lam
      = ∏ l : Fin N, (diagRatio σ l / diagRatio (σ * swapNext i hi) l) ^ (lam l) := by
    rw [cellTriv, cellTriv, ← Finset.prod_div_distrib]
    exact Finset.prod_congr rfl fun l _ => (div_zpow _ _ _).symm
  have hsub : ({i, (⟨(i : ℕ) + 1, hi⟩ : Fin N)} : Finset (Fin N)) ⊆ Finset.univ :=
    Finset.subset_univ _
  have hout : ∀ l ∈ Finset.univ, l ∉ ({i, (⟨(i : ℕ) + 1, hi⟩ : Fin N)} : Finset (Fin N)) →
      (diagRatio (k := k) σ l / diagRatio (σ * swapNext i hi) l) ^ (lam l) = 1 := by
    intro l _ hl
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hl
    rcases lt_trichotomy (l : ℕ) (i : ℕ) with h | h | h
    · rw [diagRatio_div_of_lt σ hi h, one_zpow]
    · exact absurd (Fin.ext h) hl.1
    · have h2 : (i : ℕ) + 1 < (l : ℕ) := by
        rcases Nat.lt_or_ge ((i : ℕ) + 1) (l : ℕ) with h3 | h3
        · exact h3
        · refine absurd (Fin.ext ?_) hl.2
          show (l : ℕ) = (i : ℕ) + 1
          omega
      rw [diagRatio_div_of_gt σ hi h2, one_zpow]
  rw [hstep, ← Finset.prod_subset hsub hout, Finset.prod_pair hne, diagRatio_div_self,
    diagRatio_div_succ σ hi rfl, neg_eq_neg_one_mul, mul_zpow, inv_zpow, ← zpow_neg,
    mul_comm ((-1 : (FlagLoc N k)ˣ) ^ (lam (⟨(i : ℕ) + 1, hi⟩ : Fin N)))
      (fibreCoord σ hi ^ (-lam (⟨(i : ℕ) + 1, hi⟩ : Fin N))), ← mul_assoc, ← zpow_add,
    ← sub_eq_add_neg]

end GaloisForLFunctions.HTGeometry.BorelWeil
