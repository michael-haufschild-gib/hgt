import GaloisForLFunctions.HTGeometry.LongRangeNonHermitianSpectra
import GaloisForLFunctions.HTGeometry.FeedForwardFisherRetention

/-!
# Non-Bloch annular convergence and Fisher coverage

Equation (3) of Gu--Fu--Hu--Wang, arXiv:2608.28577, for non-unit Bloch
moduli. The exterior tail has no summable nonzero-coupling version, despite
vanishing at zero coupling at each finite truncation. Combining the
corpus squeeze with Bai--Li--Kou retention gives a finite-length coverage floor.
These are exact analytic statements, not an assertion of spectral reconstruction.
-/

open Filter Topology
open scoped BigOperators

noncomputable section

namespace GaloisForLFunctions.HTGeometry

/-- A non-Bloch factor with unrestricted logarithmic modulus and phase. -/
def longRangeBlochFactor (mu theta : ℝ) : ℂ :=
  (Real.exp mu : ℂ) * unitBlochFactor theta

theorem norm_longRangeBlochFactor (mu theta : ℝ) :
    ‖longRangeBlochFactor mu theta‖ = Real.exp mu := by
  simp [longRangeBlochFactor]

/-- Damping lies strictly beyond the mode's logarithmic modulus, with arbitrary positive margin. -/
def longRangeInteriorRatio (mu a : ℝ) : ℝ := Real.exp (-(|mu| + Real.exp a))

theorem longRangeInterior_norm_forward (mu a theta : ℝ) :
    ‖(longRangeInteriorRatio mu a : ℂ) * longRangeBlochFactor mu theta‖ < 1 := by
  rw [norm_mul, norm_longRangeBlochFactor, Complex.norm_real,
    longRangeInteriorRatio, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _),
    ← Real.exp_add, Real.exp_lt_one_iff]
  linarith [le_abs_self mu, Real.exp_pos a]

theorem longRangeInterior_norm_backward (mu a theta : ℝ) :
    ‖(longRangeInteriorRatio mu a : ℂ) * (longRangeBlochFactor mu theta)⁻¹‖ < 1 := by
  rw [norm_mul, norm_inv, norm_longRangeBlochFactor, Complex.norm_real,
    longRangeInteriorRatio, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), ← Real.exp_neg,
    ← Real.exp_add, Real.exp_lt_one_iff]
  linarith [neg_le_abs mu, Real.exp_pos a]

/-- Both oriented exponentially decaying tails at a genuinely non-Bloch mode. -/
def longRangeAnnularTerm (mu a theta : ℝ) (n : ℕ) : ℂ :=
  ((longRangeInteriorRatio mu a : ℂ) * longRangeBlochFactor mu theta) ^ (n + 1) +
    ((longRangeInteriorRatio mu a : ℂ) * (longRangeBlochFactor mu theta)⁻¹) ^ (n + 1)

def longRangeAnnularClosedForm (mu a theta : ℝ) : ℂ :=
  let q : ℂ := longRangeInteriorRatio mu a
  let z := longRangeBlochFactor mu theta
  q * z * (1 - q * z)⁻¹ + q * z⁻¹ * (1 - q * z⁻¹)⁻¹

/-- Equation (3) on the entire parametrized open annulus, beyond the unit-circle specialization. -/
theorem hasSum_longRangeAnnularTerm (mu a theta : ℝ) :
    HasSum (longRangeAnnularTerm mu a theta) (longRangeAnnularClosedForm mu a theta) := by
  have hf := (hasSum_geometric_of_norm_lt_one
    (longRangeInterior_norm_forward mu a theta)).mul_left
      ((longRangeInteriorRatio mu a : ℂ) * longRangeBlochFactor mu theta)
  have hb := (hasSum_geometric_of_norm_lt_one
    (longRangeInterior_norm_backward mu a theta)).mul_left
      ((longRangeInteriorRatio mu a : ℂ) * (longRangeBlochFactor mu theta)⁻¹)
  unfold longRangeAnnularTerm longRangeAnnularClosedForm
  simpa only [pow_succ'] using hf.add hb

/-- At a fixed interior mode the long-range correction vanishes with its coupling. -/
theorem longRangeAnnularCorrection_tendsto_zero (mu a theta : ℝ) :
    Tendsto (fun g : ℂ => g * ∑' n, longRangeAnnularTerm mu a theta n)
      (𝓝 0) (𝓝 0) := by
  simpa using (tendsto_id.mul (tendsto_const_nhds :
    Tendsto (fun _ : ℂ => ∑' n, longRangeAnnularTerm mu a theta n) (𝓝 0) _))

/-- Zero-phase tail outside the convergence annulus; its growing component is explicit. -/
def longRangeExteriorTerm (alpha a : ℝ) (n : ℕ) : ℝ :=
  Real.exp (Real.exp a) ^ (n + 1) +
    Real.exp (-2 * |alpha| - Real.exp a) ^ (n + 1)

/-- The exterior sequence is the original exponentially weighted Bloch tail, without approximation. -/
theorem longRangeExteriorTerm_eq_hopping (alpha a : ℝ) (n : ℕ) :
    longRangeExteriorTerm alpha a n =
      Real.exp (-|alpha|) ^ (n + 1) *
        (Real.exp (|alpha| + Real.exp a) ^ (n + 1) +
          Real.exp (-(|alpha| + Real.exp a)) ^ (n + 1)) := by
  unfold longRangeExteriorTerm
  rw [mul_add, ← mul_pow, ← mul_pow, ← Real.exp_add, ← Real.exp_add]
  rw [show -|alpha| + (|alpha| + Real.exp a) = Real.exp a by ring,
    show -|alpha| + -(|alpha| + Real.exp a) = -2 * |alpha| - Real.exp a by ring]

theorem one_le_longRangeExteriorTerm (alpha a : ℝ) (n : ℕ) :
    1 ≤ longRangeExteriorTerm alpha a n := by
  have h : 1 ≤ Real.exp (Real.exp a) := by
    rw [Real.one_le_exp_iff]
    exact (Real.exp_pos a).le
  exact (one_le_pow₀ h).trans (le_add_of_nonneg_right (by positivity))

/-- An arbitrarily small nonzero coupling cannot repair an exterior mode's divergent tail. -/
theorem summable_longRangeExterior_iff (alpha a g : ℝ) :
    Summable (fun n => g * longRangeExteriorTerm alpha a n) ↔ g = 0 := by
  constructor
  · intro hs
    by_contra hg
    have h : Summable (longRangeExteriorTerm alpha a) := by
      simpa only [← mul_assoc, inv_mul_cancel₀ hg, one_mul] using hs.mul_left g⁻¹
    have hbad : (1 : ℝ) ≤ 0 := ge_of_tendsto h.tendsto_atTop_zero
      (Eventually.of_forall (one_le_longRangeExteriorTerm alpha a))
    exact (not_le_of_gt zero_lt_one) hbad
  · rintro rfl
    simp

/-- Every finite truncation still vanishes as coupling tends to zero. -/
theorem longRangeExterior_finite_coupling_limit (alpha a : ℝ) (N : ℕ) :
    Tendsto (fun g : ℝ => ∑ n ∈ Finset.range N, g * longRangeExteriorTerm alpha a n)
      (𝓝 0) (𝓝 0) := by
  simp only [← Finset.mul_sum]
  simpa using (tendsto_id.mul (tendsto_const_nhds :
    Tendsto (fun _ : ℝ => ∑ n ∈ Finset.range N, longRangeExteriorTerm alpha a n) (𝓝 0) _))

/-- The long-range cap limits every finite feed-forward preparation energy. -/
theorem squeezed_feedForwardBuildup_le (alpha mu : ℝ) (n : ℕ) :
    feedForwardBuildup (Real.exp (squeezedLogModulus alpha mu)) n ≤
      (n + 1 : ℝ) * Real.exp (2 * |alpha| * n) := by
  have hupper := (squeezedLogModulus alpha mu).property.2
  have hlower := (squeezedLogModulus alpha mu).property.1
  calc
    _ ≤ ∑ _i : Fin (n + 1), Real.exp (2 * |alpha| * n) := by
      apply Finset.sum_le_sum
      intro i _
      rw [← Real.exp_nat_mul, ← Real.exp_nat_mul, Real.exp_le_exp]
      norm_num only [Nat.cast_ofNat]
      have hi : (i.val : ℝ) ≤ n := by exact_mod_cast Nat.le_of_lt_succ i.isLt
      have hi0 : (0 : ℝ) ≤ i.val := by positivity
      nlinarith [mul_nonneg hi0 (sub_nonneg.mpr hupper),
        mul_nonneg (abs_nonneg alpha) (sub_nonneg.mpr hi)]
    _ = _ := by simp

/-- A concrete link between the two non-Hermitian papers: squeezing gives an explicit
floor on upstream Fisher retention at each finite interval length. -/
theorem squeezed_feedForwardRetention_floor (alpha mu : ℝ) (n : ℕ) :
    1 / ((n + 1 : ℝ) * Real.exp (2 * |alpha| * n)) ≤
      feedForwardRetention (Real.exp (squeezedLogModulus alpha mu)) n 0 := by
  simp only [feedForwardRetention, Fin.val_zero, pow_zero]
  exact div_le_div_of_nonneg_left zero_le_one (feedForwardBuildup_pos _ _)
    (squeezed_feedForwardBuildup_le alpha mu n)

end GaloisForLFunctions.HTGeometry
