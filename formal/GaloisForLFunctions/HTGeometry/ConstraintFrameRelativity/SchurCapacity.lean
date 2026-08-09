import GaloisForLFunctions.HTGeometry.ConstraintFrameRelativity.BernoulliBooleanGibbs

/-!
# The parity--energy Schur capacity of a finite weighted clock

For a finite family of positive weights `w` and a clock vector `lam`, the covariance Gram of the
pair `(1, lam)` is `!![A, B; B, C]` with `A = ∑ w`, `B = ∑ w · lam`, `C = ∑ w · lam²`.  The
*Schur capacity* is `π² (A - B²/C)`, the minimal variance of `π N - t E` over `t`.

The exact contents are:

* `quadratic_expand` — the variance of `c - t · lam` against `w`;
* `schurCapacity_le_quadratic`, `quadratic_eq_schurCapacity` — the variational characterisation
  and its unique minimiser `t = π B / C`;
* `capA_mul_capC_sub_capB_sq` — the two-row Cauchy--Binet identity
  `A C - B² = ½ ∑_{p,r} w_p w_r (lam_p - lam_r)²`;
* `schurCapacity_pos` — strict positivity as soon as two clocks differ;
* `schurCapacity_le_pi_sq_mul_capA` — the crude upper bound `π² A`.
-/

namespace HTGeometry.ConstraintFrameRelativity

open Finset

variable {ι : Type*} [Fintype ι]

/-! ## The covariance Gram entries -/

/-- Total weight `A = ∑ w`. -/
def capA (w : ι → ℝ) : ℝ := ∑ p, w p

/-- Mixed moment `B = ∑ w · lam`. -/
def capB (w lam : ι → ℝ) : ℝ := ∑ p, w p * lam p

/-- Energy moment `C = ∑ w · lam²`. -/
def capC (w lam : ι → ℝ) : ℝ := ∑ p, w p * lam p ^ 2

/-- The parity--energy Schur capacity `π² (A - B²/C)`. -/
noncomputable def schurCapacity (w lam : ι → ℝ) : ℝ :=
  Real.pi ^ 2 * (capA w - capB w lam ^ 2 / capC w lam)

theorem capA_nonneg {w : ι → ℝ} (hw : ∀ p, 0 ≤ w p) : 0 ≤ capA w :=
  Finset.sum_nonneg fun p _ => hw p

theorem capC_nonneg {w : ι → ℝ} (hw : ∀ p, 0 ≤ w p) (lam : ι → ℝ) : 0 ≤ capC w lam :=
  Finset.sum_nonneg fun p _ => mul_nonneg (hw p) (sq_nonneg _)

/-- The weighted variance of the affine clock observable `c - t · lam`. -/
theorem quadratic_expand (w lam : ι → ℝ) (c t : ℝ) :
    ∑ p, w p * (c - t * lam p) ^ 2
      = c ^ 2 * capA w - 2 * c * t * capB w lam + t ^ 2 * capC w lam := by
  simp only [capA, capB, capC, Finset.mul_sum, ← Finset.sum_sub_distrib,
    ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun p _ => by ring

/-! ## The variational characterisation -/

theorem schurCapacity_le_quadratic {w lam : ι → ℝ} (hC : 0 < capC w lam) (t : ℝ) :
    schurCapacity w lam
      ≤ Real.pi ^ 2 * capA w - 2 * Real.pi * t * capB w lam + t ^ 2 * capC w lam := by
  have hkey : Real.pi ^ 2 * capA w - 2 * Real.pi * t * capB w lam + t ^ 2 * capC w lam
      - schurCapacity w lam = capC w lam * (t - Real.pi * capB w lam / capC w lam) ^ 2 := by
    simp only [schurCapacity]
    field_simp
    ring
  nlinarith [mul_nonneg hC.le (sq_nonneg (t - Real.pi * capB w lam / capC w lam))]

theorem quadratic_eq_schurCapacity {w lam : ι → ℝ} (hC : 0 < capC w lam) :
    Real.pi ^ 2 * capA w - 2 * Real.pi * (Real.pi * capB w lam / capC w lam) * capB w lam
        + (Real.pi * capB w lam / capC w lam) ^ 2 * capC w lam
      = schurCapacity w lam := by
  simp only [schurCapacity]
  field_simp
  ring

/-- The Schur capacity is the least weighted variance of `π · 1 - t · lam`. -/
theorem isLeast_schurCapacity {w lam : ι → ℝ} (hC : 0 < capC w lam) :
    IsLeast {v : ℝ | ∃ t : ℝ, ∑ p, w p * (Real.pi - t * lam p) ^ 2 = v}
      (schurCapacity w lam) := by
  constructor
  · refine ⟨Real.pi * capB w lam / capC w lam, ?_⟩
    rw [quadratic_expand]
    exact quadratic_eq_schurCapacity hC
  · rintro v ⟨t, rfl⟩
    rw [quadratic_expand]
    exact schurCapacity_le_quadratic hC t

/-! ## Two-row Cauchy--Binet -/

/-- **Two-row Cauchy--Binet.**  The Gram determinant is the weighted clock-gap energy. -/
theorem capA_mul_capC_sub_capB_sq (w lam : ι → ℝ) :
    capA w * capC w lam - capB w lam ^ 2
      = (∑ p, ∑ r, w p * w r * (lam p - lam r) ^ 2) / 2 := by
  have key : ∀ p : ι, ∑ r, w p * w r * (lam p - lam r) ^ 2
      = w p * lam p ^ 2 * capA w - 2 * (w p * lam p) * capB w lam + w p * capC w lam := by
    intro p
    simp only [capA, capB, capC, Finset.mul_sum, ← Finset.sum_sub_distrib,
      ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun r _ => by ring
  rw [Finset.sum_congr rfl fun p _ => key p]
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.sum_mul, ← Finset.sum_mul,
    ← Finset.sum_mul]
  simp only [capA, capB, capC]
  have h2 : ∑ p, 2 * (w p * lam p) = 2 * ∑ p, w p * lam p := by
    rw [Finset.mul_sum]
  rw [h2]
  ring

/-! ## Positivity -/

theorem capC_pos {w lam : ι → ℝ} (hw : ∀ p, 0 < w p) {p₀ : ι} (hlam : lam p₀ ≠ 0) :
    0 < capC w lam := by
  refine Finset.sum_pos' (fun p _ => mul_nonneg (hw p).le (sq_nonneg _)) ⟨p₀, mem_univ p₀, ?_⟩
  exact mul_pos (hw p₀) (by positivity)

theorem capA_mul_capC_sub_capB_sq_pos {w lam : ι → ℝ} (hw : ∀ p, 0 < w p) {p₀ r₀ : ι}
    (hne : lam p₀ ≠ lam r₀) : 0 < capA w * capC w lam - capB w lam ^ 2 := by
  rw [capA_mul_capC_sub_capB_sq]
  have hnn : ∀ p ∈ (univ : Finset ι), (0 : ℝ) ≤ ∑ r, w p * w r * (lam p - lam r) ^ 2 := by
    intro p _
    exact Finset.sum_nonneg fun r _ =>
      mul_nonneg (mul_nonneg (hw p).le (hw r).le) (sq_nonneg _)
  have hpos : (0 : ℝ) < ∑ r, w p₀ * w r * (lam p₀ - lam r) ^ 2 := by
    refine Finset.sum_pos' (fun r _ => mul_nonneg (mul_nonneg (hw p₀).le (hw r).le) (sq_nonneg _))
      ⟨r₀, mem_univ r₀, ?_⟩
    exact mul_pos (mul_pos (hw p₀) (hw r₀)) (by positivity)
  have := Finset.sum_pos' hnn ⟨p₀, mem_univ p₀, hpos⟩
  linarith

/-- The Schur capacity as an explicit ratio. -/
theorem schurCapacity_eq_ratio {w lam : ι → ℝ} (hC : 0 < capC w lam) :
    schurCapacity w lam
      = Real.pi ^ 2 * ((capA w * capC w lam - capB w lam ^ 2) / capC w lam) := by
  rw [schurCapacity]
  field_simp

/-- **Strict positivity of the capacity.**  Two distinct clocks and positive weights suffice. -/
theorem schurCapacity_pos {w lam : ι → ℝ} (hw : ∀ p, 0 < w p) {p₀ r₀ : ι}
    (hne : lam p₀ ≠ lam r₀) : 0 < schurCapacity w lam := by
  have hlam : lam p₀ ≠ 0 ∨ lam r₀ ≠ 0 := by
    by_contra h
    rw [not_or, not_not, not_not] at h
    exact hne (by rw [h.1, h.2])
  have hC : 0 < capC w lam := by
    rcases hlam with h | h
    · exact capC_pos hw h
    · exact capC_pos hw h
  rw [schurCapacity_eq_ratio hC]
  have hnum := capA_mul_capC_sub_capB_sq_pos hw hne
  have : 0 < (capA w * capC w lam - capB w lam ^ 2) / capC w lam := div_pos hnum hC
  positivity

/-- The crude upper bound `π² A`. -/
theorem schurCapacity_le_pi_sq_mul_capA {w lam : ι → ℝ} (hC : 0 < capC w lam) :
    schurCapacity w lam ≤ Real.pi ^ 2 * capA w := by
  rw [schurCapacity]
  have h : 0 ≤ capB w lam ^ 2 / capC w lam := div_nonneg (sq_nonneg _) hC.le
  nlinarith [Real.pi_pos, sq_nonneg Real.pi]

/-! ## The Boolean gas realisation -/

variable [DecidableEq ι]

/-- The Boolean-gas parity statistic `N(S) = |S|`. -/
theorem bernoulliCov_parity_energy (q lam : ι → ℝ) (c t : ℝ) :
    bernoulliCov q (linearStat fun _ => c) (linearStat fun p => t * lam p)
      = ∑ p, c * (t * lam p) * (q p * (1 - q p)) :=
  bernoulliCov_linearStat q _ _

/-- **The Boolean-gas variance of `c · N - t · E`.**  Its minimum over `t` at `c = π` is the
Schur capacity of the Bernoulli variance vector. -/
theorem bernoulliCov_affine_clock (q lam : ι → ℝ) (c t : ℝ) :
    bernoulliCov q (linearStat fun p => c - t * lam p) (linearStat fun p => c - t * lam p)
      = ∑ p, (q p * (1 - q p)) * (c - t * lam p) ^ 2 := by
  rw [bernoulliCov_linearStat]
  exact Finset.sum_congr rfl fun p _ => by ring

end HTGeometry.ConstraintFrameRelativity
