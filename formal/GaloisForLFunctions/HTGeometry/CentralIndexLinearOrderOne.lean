import GaloisForLFunctions.HTGeometry.CentralIndexGrowthWall

/-!
# A linearly bounded central index means order at most one

The lower growth law `ν(r)·log(s/r) ≤ log μ(s) − log μ(r)` costs `ν(2r)·log 2` per doubling of the
radius.  If `ν(r) ≤ C r` beyond some `r₀`, that cost is `C r log 2`, and the dyadic sum telescopes:
`log μ(r) ≤ log μ(r₀) + 4 C (log 2) r`.

This is the growth half of the statement that an entire solution of an autonomous first-order
algebraic differential equation has order at most one.  The other half — that the equation forces
`ν(r) = O(r)` — is read off at a Wiman–Valiron point, where the relation becomes a polynomial
identity in `ν/r` whose balancing pins that ratio to a power of the maximum modulus.
-/

namespace GaloisForLFunctions.HTGeometry

variable {a : ℕ → ℂ}

/-- **A linearly bounded central index gives order at most one.**  If `ν(r) ≤ C r` beyond `r₀`, then
`log μ(r) ≤ log μ(r₀) + 4 C (log 2) r`: doubling the radius costs `ν(r) log 2 ≤ C r log 2`, and the
dyadic sum telescopes. -/
theorem log_maxTerm_le_linear_of_centralIndex_le_linear (ha : EntireCoeffs a) {n₀ : ℕ}
    (hn₀ : a n₀ ≠ 0) {C r₀ : ℝ} (hC : 0 ≤ C) (hr₀ : 1 ≤ r₀)
    (hbd : ∀ r : ℝ, r₀ ≤ r → (centralIndex a r : ℝ) ≤ C * r) :
    ∀ r : ℝ, r₀ ≤ r → Real.log (maxTerm a r)
      ≤ Real.log (maxTerm a r₀) + 4 * C * Real.log 2 * r := by
  have hr₀0 : (0 : ℝ) < r₀ := by linarith
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  -- one doubling step
  have hstep : ∀ s r : ℝ, r₀ ≤ s → s ≤ r → r ≤ 2 * s →
      Real.log (maxTerm a r) ≤ Real.log (maxTerm a s) + C * r * Real.log 2 := by
    intro s r hs hsr hr2s
    have hs0 : (0 : ℝ) < s := by linarith
    have hgrow := log_maxTerm_sub_le_centralIndex_mul_log ha hs0 hsr hn₀
    have hnu : (centralIndex a r : ℝ) ≤ C * r := hbd r (le_trans hs hsr)
    have hratio : Real.log (r / s) ≤ Real.log 2 := by
      have hrpos : (0 : ℝ) < r := by linarith
      refine Real.log_le_log (by positivity) ?_
      rw [div_le_iff₀ hs0]
      linarith
    have hnu0 : (0 : ℝ) ≤ (centralIndex a r : ℝ) := Nat.cast_nonneg _
    have hlogr : (0 : ℝ) ≤ Real.log (r / s) := by
      refine Real.log_nonneg ?_
      rw [le_div_iff₀ hs0]
      linarith
    nlinarith [hgrow, hnu, hratio, hnu0, hlogr]
  -- dyadic induction
  have hind : ∀ k : ℕ, ∀ r : ℝ, r₀ ≤ r → r ≤ 2 ^ k * r₀ →
      Real.log (maxTerm a r) ≤ Real.log (maxTerm a r₀) + 4 * C * Real.log 2 * r := by
    intro k
    induction k with
    | zero =>
        intro r hr hle
        simp only [pow_zero, one_mul] at hle
        have : r = r₀ := le_antisymm hle hr
        subst this
        have hnn : (0 : ℝ) ≤ 4 * C * Real.log 2 * r :=
          mul_nonneg (by positivity) (by linarith)
        linarith
    | succ k ih =>
        intro r hr hle
        rcases le_or_gt r (2 * r₀) with hsmall | hbig
        · have h := hstep r₀ r le_rfl hr hsmall
          have hpos : (0 : ℝ) ≤ 3 * C * Real.log 2 * r :=
            mul_nonneg (by positivity) (by linarith)
          nlinarith [h, hpos]
        · have hs : r₀ ≤ r / 2 := by linarith
          have hsle : r / 2 ≤ 2 ^ k * r₀ := by
            have h2 : (2 : ℝ) ^ (k + 1) * r₀ = 2 * (2 ^ k * r₀) := by ring
            rw [h2] at hle
            linarith
          have hih := ih (r / 2) hs hsle
          have h := hstep (r / 2) r hs (by linarith) (by linarith)
          have hCr : (0 : ℝ) ≤ C * Real.log 2 * r :=
            mul_nonneg (by positivity) (by linarith)
          nlinarith [hih, h, hCr]
  intro r hr
  obtain ⟨k, hk⟩ : ∃ k : ℕ, r ≤ 2 ^ k * r₀ := by
    obtain ⟨k, hk⟩ := pow_unbounded_of_one_lt (r / r₀) (by norm_num : (1:ℝ) < 2)
    refine ⟨k, ?_⟩
    rw [div_lt_iff₀ hr₀0] at hk
    linarith
  exact hind k r hr hk

end GaloisForLFunctions.HTGeometry
