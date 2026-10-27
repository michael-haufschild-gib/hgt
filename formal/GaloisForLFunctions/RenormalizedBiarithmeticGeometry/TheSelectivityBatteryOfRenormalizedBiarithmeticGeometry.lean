import GaloisForLFunctions.RenormalizedBiarithmeticGeometry.TheDyadicAmplificationOfTheHeckeDefect
import GaloisForLFunctions.RenormalizedBiarithmeticGeometry.TheCellHolonomyDefectCountsChargedCells
import GaloisForLFunctions.RenormalizedBiarithmeticGeometry.TheGaugeChargeOfACoupling

/-!
# The selectivity battery of Renormalized Biarithmetic Geometry

A law of the field is either *soft* — true on every configuration of the relevant shape, hence
blind to which source produced it — or *selective*. The battery records which RBG invariants are
which.

* **Dyadic amplification is soft** (`configDefect_sq_le`, `config_dyadic_ge`). For every finite
  family of nonnegative weights `w_i` and depths `δ_i` — the zeros of `ζ`, of the golden datum, of
  any fake — `E(L) = Σ w_i (2cosh(2δ_i L) − 2)` satisfies two-scale rigidity and dyadic
  amplification with loss `D = Σ w_i`. Its content for `ζ` is the transfer of a source-side bound,
  never the bound itself.
* **Cells reject the Liouville twin** (`liouville_not_cell_covariant`,
  `two_le_hsDefect_liouville`). The dyadic cell dilation is not covariant at the Liouville gauge,
  and its covariance defect is at least `2` for every scalar once the horizon reaches `2`.
* **The Euler point passes** (`euler_cell_covariant`).
* **Square-class criteria accept the Liouville twin** (`squareClass_liouville_iff`). Any positivity
  criterion built from square-class couplings holds for a source `F` iff it holds for `λF`.
-/

noncomputable section

open Finset

namespace GaloisForLFunctions.RenormalizedBiarithmeticGeometry

open ConjugateDiagonalGeometry BiarithmeticGaugeGeometry

/-! ### Soft laws: every positive configuration amplifies -/

section Soft

variable {ι : Type*} (s : Finset ι) (w δ : ι → ℝ)

/-- The mass `D = Σ w_i` of a configuration. -/
def configMass : ℝ := ∑ i ∈ s, w i

/-- The Hecke defect `E(L) = Σ w_i (2cosh(2δ_i L) − 2)` of a configuration. -/
def configDefect (L : ℝ) : ℝ := ∑ i ∈ s, w i * depthKernel L (δ i)

/-- Weighted Cauchy–Schwarz: `(Σ w k)² ≤ (Σ w)(Σ w k²)` for `w ≥ 0`. -/
theorem sq_sum_le_mul_sum (hw : ∀ i ∈ s, 0 ≤ w i) (k : ι → ℝ) :
    (∑ i ∈ s, w i * k i) ^ 2 ≤ (∑ i ∈ s, w i) * ∑ i ∈ s, w i * k i ^ 2 := by
  have h : 0 ≤ ∑ i ∈ s, ∑ j ∈ s, w i * w j * (k i - k j) ^ 2 :=
    sum_nonneg fun i hi => sum_nonneg fun j hj =>
      mul_nonneg (mul_nonneg (hw i hi) (hw j hj)) (sq_nonneg _)
  have hexp : ∑ i ∈ s, ∑ j ∈ s, w i * w j * (k i - k j) ^ 2 =
      2 * ((∑ i ∈ s, w i) * ∑ i ∈ s, w i * k i ^ 2) - 2 * (∑ i ∈ s, w i * k i) ^ 2 := by
    have e : ∀ i j, w i * w j * (k i - k j) ^ 2 =
        w j * (w i * k i ^ 2) + w i * (w j * k j ^ 2) -
          ((w i * k i) * (w j * k j) + (w i * k i) * (w j * k j)) := fun i j => by ring
    have A : ∑ i ∈ s, ∑ j ∈ s, w j * (w i * k i ^ 2) =
        (∑ i ∈ s, w i * k i ^ 2) * ∑ j ∈ s, w j := by
      rw [sum_mul_sum]; exact sum_congr rfl fun i _ => sum_congr rfl fun j _ => by ring
    have B : ∑ i ∈ s, ∑ j ∈ s, w i * (w j * k j ^ 2) =
        (∑ i ∈ s, w i) * ∑ j ∈ s, w j * k j ^ 2 := by
      rw [sum_mul_sum]
    have C : ∑ i ∈ s, ∑ j ∈ s, (w i * k i) * (w j * k j) = (∑ i ∈ s, w i * k i) ^ 2 := by
      rw [sq, sum_mul_sum]
    simp only [e, sum_sub_distrib, sum_add_distrib]
    rw [A, B, C]
    ring
  linarith

/-- **Two-scale rigidity is soft.** -/
theorem configDefect_sq_le (hw : ∀ i ∈ s, 0 ≤ w i) (L : ℝ) :
    configDefect s w δ L ^ 2 ≤
      configMass s w * (configDefect s w δ (2 * L) - 4 * configDefect s w δ L) := by
  have h := sq_sum_le_mul_sum s w hw (fun i => depthKernel L (δ i))
  have hdouble : configDefect s w δ (2 * L) - 4 * configDefect s w δ L =
      ∑ i ∈ s, w i * depthKernel L (δ i) ^ 2 := by
    simp only [configDefect, depthKernel_double]
    rw [mul_sum, ← sum_sub_distrib]
    exact sum_congr rfl fun i _ => by ring
  rw [hdouble]
  exact h

theorem configDefect_nonneg (hw : ∀ i ∈ s, 0 ≤ w i) (L : ℝ) : 0 ≤ configDefect s w δ L :=
  sum_nonneg fun i hi => mul_nonneg (hw i hi) (depthKernel_nonneg _ _)

/-- **Dyadic amplification is soft**: it holds on every finite positive depth configuration. -/
theorem config_dyadic_ge (hw : ∀ i ∈ s, 0 ≤ w i) (L θ : ℝ)
    (h : configMass s w * (2 * Real.cosh θ - 2) ≤ configDefect s w δ L) (k : ℕ) :
    configMass s w * (2 * Real.cosh (2 ^ k * θ) - 2) ≤ configDefect s w δ (2 ^ k * L) := by
  have hD0 : 0 ≤ configMass s w := sum_nonneg hw
  rcases hD0.lt_or_eq with hD | hD
  · -- One doubling step, then iterate.
    have hstep : ∀ L', amplify (configMass s w) (configDefect s w δ L') ≤
        configDefect s w δ (2 * L') := by
      intro L'
      have h2 := configDefect_sq_le s w δ hw L'
      rw [amplify]
      have : configDefect s w δ L' ^ 2 / configMass s w ≤
          configDefect s w δ (2 * L') - 4 * configDefect s w δ L' := by
        rw [div_le_iff₀ hD]; linarith
      linarith
    have hiter : ∀ k : ℕ, (amplify (configMass s w))^[k] (configDefect s w δ L) ≤
        configDefect s w δ (2 ^ k * L) := by
      intro k
      induction k with
      | zero => simp
      | succ k ih =>
        rw [Function.iterate_succ_apply', pow_succ, mul_comm ((2 : ℝ) ^ k) 2, mul_assoc]
        exact (amplify_le_amplify hD (iterate_amplify_nonneg hD k (configDefect_nonneg s w δ hw L))
          ih).trans (hstep _)
    rw [← iterate_amplify_cosh hD]
    exact (iterate_amplify_le hD k (mul_nonneg hD.le (two_mul_cosh_sub_two_nonneg θ)) h).trans
      (hiter k)
  · rw [← hD, zero_mul]
    exact configDefect_nonneg s w δ hw _

end Soft

/-! ### Selective laws: cells see the Liouville twin -/

theorem liouvilleGauge_ne_euler : PrimeGauge.liouvilleGauge ≠ PrimeGauge.eulerGauge := by
  intro h
  have h2 := congrArg (fun ω : PrimeGauge => ω.val 2) h
  simp [PrimeGauge.liouvilleGauge, PrimeGauge.eulerGauge, Nat.prime_two] at h2
  norm_num at h2

/-- **Cells reject the Liouville twin.** -/
theorem liouville_not_cell_covariant :
    ¬ ∃ c : ℂ, ∀ q : ℕ → ℂ, q 0 = 0 →
      gaugeTwist PrimeGauge.liouvilleGauge (cellDilate 2 q) =
        c • cellDilate 2 (gaugeTwist PrimeGauge.liouvilleGauge q) := by
  rw [cellDilate_two_covariant_iff]
  exact liouvilleGauge_ne_euler

/-- The Liouville covariance defect is at least `2` for every scalar once `X ≥ 2`. -/
theorem two_le_hsDefect_liouville {X : ℕ} (hX : 2 ≤ X) (c : ℝ) :
    2 ≤ hsDefect PrimeGauge.liouvilleGauge X c := by
  have h := (hsDefect_liouville_sandwich X).1 c
  have h1 : (1 : ℝ) ≤ (liouvilleAgreements X).card := by
    exact_mod_cast one_le_liouvilleAgreements hX
  linarith

/-- **The Euler point passes.** -/
theorem euler_cell_covariant :
    ∃ c : ℂ, ∀ q : ℕ → ℂ, q 0 = 0 →
      gaugeTwist PrimeGauge.eulerGauge (cellDilate 2 q) =
        c • cellDilate 2 (gaugeTwist PrimeGauge.eulerGauge q) :=
  (cellDilate_two_covariant_iff _).mpr rfl

/-- **Square-class criteria accept the Liouville twin.** -/
theorem squareClass_liouville_iff {T S : Finset ℕ} (hT : ∀ a ∈ T, a ≠ 0) (hS : ∀ n ∈ S, n ≠ 0)
    {c : ℕ → ℕ → ℕ → ℂ}
    (hsq : ∀ a ∈ T, ∀ b ∈ T, ∀ n ∈ S, c n a b ≠ 0 → IsSquare (n * a * b)) (F : ℕ → ℂ) :
    (∀ x : ℕ → ℝ, 0 ≤ (sourceForm T S c F x).re) ↔
      ∀ x : ℕ → ℝ, 0 ≤ (sourceForm T S c (gaugeTwist PrimeGauge.liouvilleGauge F) x).re :=
  sourceForm_nonneg_twist_iff hT hS hsq (fun hp => isRealSignGauge_liouville hp) F

end GaloisForLFunctions.RenormalizedBiarithmeticGeometry
