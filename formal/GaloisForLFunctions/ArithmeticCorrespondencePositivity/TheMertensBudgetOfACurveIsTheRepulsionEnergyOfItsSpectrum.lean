import GaloisForLFunctions.ArithmeticCorrespondencePositivity.TheCurvePrimeErrorBudgetCountsItsSpectrum
import Mathlib.LinearAlgebra.Lagrange
import Mathlib.RingTheory.PowerSeries.Inverse

/-!
# The Mertens budget of a curve is the repulsion energy of its spectrum

The `𝔽_q` calibration of P45 in every genus. For normalized Frobenius eigenvalues `β_i`, the
Mertens row of the `H¹` part is the coefficient sequence of
`1/P(u) = Π_i (1 − β_i u)⁻¹` (`spectralMertensRow`).

* **Partial fractions** (`spectralMertensRow_eq`). For a simple spectrum,
  `h_m = Σ_i A_i β_i^m` with the Lagrange weights `A_i = Π_{j ≠ i} β_i/(β_i − β_j)`
  (`Lagrange.sum_basis` at the nodes `β_i⁻¹`).
* **The slope is the repulsion energy** (`tendsto_spectralMertens_energy_div`). For a pure simple
  spectrum, `(1/M) Σ_{m ≤ M} |h_m|² → Σ_i ‖A_i‖² = Σ_i Π_{j ≠ i} |β_i − β_j|⁻²`: the diagonal terms
  survive and the cross terms `(β_i β̄_j)^m` average out.

So the Mertens budget of a pure curve with simple spectrum is the repulsion energy of its
eigenvalues on the unit circle, finite exactly as long as no two eigenvalues collide; in genus one
it is `2/|β − β̄|² = 2q/(4q − a²)` (P47). Over `ℤ` the corresponding slope `Σ_ρ |ρ ζ′(ρ)|⁻²` (P45)
has the same shape: `|ζ′(ρ)|` is the product of the distances from `ρ` to the other zeros.
-/

open Complex Finset Filter Topology

noncomputable section

namespace GaloisForLFunctions.ArithmeticCorrespondencePositivity

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The Mertens row of a spectrum: the coefficients of `Π_i (1 − β_i u)⁻¹`. -/
def spectralMertensRow (β : ι → ℂ) (m : ℕ) : ℂ :=
  PowerSeries.coeff m (∏ i, PowerSeries.mk fun k => β i ^ k)

/-- The geometric series inverts `1 − b u`. -/
theorem geom_mul_one_sub (b : ℂ) :
    (PowerSeries.mk fun k => b ^ k) * (1 - PowerSeries.C b * PowerSeries.X) = 1 := by
  ext n
  rcases n with _ | n
  · simp
  · rw [mul_sub, mul_one, map_sub, show (PowerSeries.mk fun k => b ^ k) *
      (PowerSeries.C b * PowerSeries.X) =
      PowerSeries.C b * ((PowerSeries.mk fun k => b ^ k) * PowerSeries.X) by ring,
      PowerSeries.coeff_C_mul, PowerSeries.coeff_succ_mul_X]
    simp [pow_succ]
    ring

/-- The Lagrange weight `A_i = Π_{j ≠ i} β_i/(β_i − β_j)`. -/
def repulsionWeight (β : ι → ℂ) (i : ι) : ℂ := ∏ j ∈ univ.erase i, β i / (β i - β j)

/-- `C(β_i/(β_i − β_j)) (1 − β_j X)` is the Lagrange divisor at the nodes `β_i⁻¹, β_j⁻¹`. -/
theorem C_mul_one_sub_eq_basisDivisor {a b : ℂ} (ha : a ≠ 0) (hb : b ≠ 0) (hab : a ≠ b) :
    Polynomial.C (a / (a - b)) * (1 - Polynomial.C b * Polynomial.X) =
      Lagrange.basisDivisor a⁻¹ b⁻¹ := by
  have hsub : a - b ≠ 0 := sub_ne_zero.mpr hab
  have hc : (a⁻¹ - b⁻¹)⁻¹ = -(a / (a - b) * b) := by
    field_simp
    ring
  have hcb : -(a / (a - b) * b) * b⁻¹ = -(a / (a - b)) := by
    field_simp
  rw [Lagrange.basisDivisor, hc, mul_sub, mul_sub, mul_one, ← mul_assoc, ← map_mul,
    ← map_mul, hcb, map_neg, map_neg]
  ring

/-- **Lagrange.** For a simple spectrum of nonzero eigenvalues,
`Σ_i A_i Π_{j ≠ i} (1 − β_j u) = 1`. -/
theorem sum_repulsionWeight_mul_prod [Nonempty ι] {β : ι → ℂ} (hinj : Function.Injective β)
    (h0 : ∀ i, β i ≠ 0) :
    ∑ i, Polynomial.C (repulsionWeight β i) *
      ∏ j ∈ univ.erase i, (1 - Polynomial.C (β j) * Polynomial.X) = 1 := by
  have hv : Set.InjOn (fun i => (β i)⁻¹) (univ : Finset ι) := fun i _ j _ h =>
    hinj (inv_injective h)
  refine Eq.trans (sum_congr rfl fun i _ => ?_) (Lagrange.sum_basis hv univ_nonempty)
  rw [Lagrange.basis, repulsionWeight, map_prod, ← prod_mul_distrib]
  refine prod_congr rfl fun j hj => ?_
  exact C_mul_one_sub_eq_basisDivisor (h0 i) (h0 j) (hinj.ne (ne_of_mem_erase hj).symm)

/-- **Partial fractions.** For a simple spectrum of nonzero eigenvalues,
`Π_i (1 − β_i u)⁻¹ = Σ_i A_i (1 − β_i u)⁻¹`. -/
theorem prod_geom_eq_sum [Nonempty ι] {β : ι → ℂ} (hinj : Function.Injective β)
    (h0 : ∀ i, β i ≠ 0) :
    (∏ i, PowerSeries.mk fun k => β i ^ k) =
      ∑ i, PowerSeries.C (repulsionWeight β i) * PowerSeries.mk fun k => β i ^ k := by
  have hQ : (∏ i, (1 - PowerSeries.C (β i) * PowerSeries.X : PowerSeries ℂ)) ≠ 0 := by
    intro h
    have := congrArg PowerSeries.constantCoeff h
    simp at this
  apply mul_right_cancel₀ hQ
  rw [← prod_mul_distrib]
  simp_rw [geom_mul_one_sub]
  rw [prod_const_one, sum_mul]
  have hpoly := congrArg (Polynomial.coeToPowerSeries.ringHom (R := ℂ))
    (sum_repulsionWeight_mul_prod hinj h0)
  simp only [map_sum, map_mul, map_prod, map_sub, map_one,
    Polynomial.coeToPowerSeries.ringHom_apply, Polynomial.coe_C, Polynomial.coe_X] at hpoly
  refine hpoly.symm.trans (sum_congr rfl fun i _ => ?_)
  rw [← mul_prod_erase univ (fun j => (1 - PowerSeries.C (β j) * PowerSeries.X : PowerSeries ℂ))
    (mem_univ i), ← mul_assoc, mul_assoc (PowerSeries.C _), geom_mul_one_sub, mul_one]

/-- `h_m = Σ_i A_i β_i^m`. -/
theorem spectralMertensRow_eq [Nonempty ι] {β : ι → ℂ} (hinj : Function.Injective β)
    (h0 : ∀ i, β i ≠ 0) (m : ℕ) :
    spectralMertensRow β m = ∑ i, repulsionWeight β i * β i ^ m := by
  rw [spectralMertensRow, prod_geom_eq_sum hinj h0, map_sum]
  simp only [PowerSeries.coeff_C_mul, PowerSeries.coeff_mk]

/-! ### The slope -/

/-- For unimodular eigenvalues `‖A_i‖² = Π_{j ≠ i} |β_i − β_j|⁻²`. -/
theorem norm_repulsionWeight_sq {β : ι → ℂ} (hu : ∀ i, ‖β i‖ = 1) (i : ι) :
    ‖repulsionWeight β i‖ ^ 2 = ∏ j ∈ univ.erase i, 1 / ‖β i - β j‖ ^ 2 := by
  rw [repulsionWeight, norm_prod, ← prod_pow]
  refine prod_congr rfl fun j _ => ?_
  rw [norm_div, hu, div_pow, one_pow]

/-- **A Mertens budget.** For a pure simple spectrum, `Σ_{m ≤ M} |h_m|² ≤ (Σ_i ‖A_i‖)² M`. -/
theorem spectralMertens_energy_le [Nonempty ι] {β : ι → ℂ} (hinj : Function.Injective β)
    (hu : ∀ i, ‖β i‖ = 1) (M : ℕ) :
    ∑ m ∈ Icc 1 M, ‖spectralMertensRow β m‖ ^ 2 ≤ (∑ i, ‖repulsionWeight β i‖) ^ 2 * M := by
  have h0 : ∀ i, β i ≠ 0 := fun i h => by
    have := hu i; rw [h, norm_zero] at this; norm_num at this
  have hb : ∀ m, ‖spectralMertensRow β m‖ ≤ ∑ i, ‖repulsionWeight β i‖ := fun m => by
    rw [spectralMertensRow_eq hinj h0]
    refine (norm_sum_le _ _).trans (sum_le_sum fun i _ => ?_)
    rw [norm_mul, norm_pow, hu, one_pow, mul_one]
  calc ∑ m ∈ Icc 1 M, ‖spectralMertensRow β m‖ ^ 2
      ≤ ∑ _m ∈ Icc 1 M, (∑ i, ‖repulsionWeight β i‖) ^ 2 :=
        sum_le_sum fun m _ => pow_le_pow_left₀ (norm_nonneg _) (hb m) 2
    _ = (∑ i, ‖repulsionWeight β i‖) ^ 2 * M := by
        rw [sum_const, Nat.card_Icc, Nat.add_sub_cancel, nsmul_eq_mul, mul_comm]

/-- `‖h_m‖² = Σ_{i,j} A_i Ā_j (β_i β̄_j)^m`. -/
theorem ofReal_norm_spectralMertensRow_sq [Nonempty ι] {β : ι → ℂ}
    (hinj : Function.Injective β) (h0 : ∀ i, β i ≠ 0) (m : ℕ) :
    ((‖spectralMertensRow β m‖ ^ 2 : ℝ) : ℂ) = ∑ p ∈ (univ ×ˢ univ : Finset (ι × ι)),
      repulsionWeight β p.1 * starRingEnd ℂ (repulsionWeight β p.2) *
        (β p.1 * starRingEnd ℂ (β p.2)) ^ m := by
  rw [Complex.ofReal_pow, ← Complex.mul_conj', spectralMertensRow_eq hinj h0, map_sum,
    sum_mul_sum, ← sum_product']
  refine sum_congr rfl fun p _ => ?_
  rw [map_mul, map_pow, mul_pow]
  ring

/-- **The slope is the repulsion energy.** For a pure simple spectrum,
`(1/M) Σ_{m ≤ M} |h_m|² → Σ_i Π_{j ≠ i} |β_i − β_j|⁻²`. -/
theorem tendsto_spectralMertens_energy_div [Nonempty ι] {β : ι → ℂ}
    (hinj : Function.Injective β) (hu : ∀ i, ‖β i‖ = 1) :
    Tendsto (fun M : ℕ => (∑ m ∈ Icc 1 M, ‖spectralMertensRow β m‖ ^ 2) / M) atTop
      (𝓝 (∑ i, ∏ j ∈ univ.erase i, 1 / ‖β i - β j‖ ^ 2)) := by
  have h0 : ∀ i, β i ≠ 0 := fun i h => by
    have := hu i; rw [h, norm_zero] at this; norm_num at this
  have hpair : ∀ p ∈ (univ ×ˢ univ : Finset (ι × ι)),
      Tendsto (fun M : ℕ => repulsionWeight β p.1 * starRingEnd ℂ (repulsionWeight β p.2) *
        ((∑ m ∈ Icc 1 M, (β p.1 * starRingEnd ℂ (β p.2)) ^ m) / M)) atTop
        (𝓝 (if p.1 = p.2 then ((‖repulsionWeight β p.1‖ ^ 2 : ℝ) : ℂ) else 0)) := by
    intro p _
    have hz : ‖β p.1 * starRingEnd ℂ (β p.2)‖ = 1 := by
      rw [norm_mul, Complex.norm_conj, hu, hu, one_mul]
    by_cases heq : p.1 = p.2
    · rw [if_pos heq]
      have h1 : β p.1 * starRingEnd ℂ (β p.2) = 1 := by
        rw [← heq, Complex.mul_conj', hu]; simp
      have hA : repulsionWeight β p.1 * starRingEnd ℂ (repulsionWeight β p.2) =
          ((‖repulsionWeight β p.1‖ ^ 2 : ℝ) : ℂ) := by
        rw [← heq, Complex.mul_conj', Complex.ofReal_pow]
      simp only [h1, one_pow, sum_const, Nat.card_Icc, Nat.add_sub_cancel, nsmul_eq_mul, mul_one,
        hA]
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [eventually_ne_atTop 0] with M hM
      rw [div_self (Nat.cast_ne_zero.mpr hM), mul_one]
    · rw [if_neg heq]
      have hne : β p.1 * starRingEnd ℂ (β p.2) ≠ 1 := fun h1 => heq <| hinj <| by
        have hconj : starRingEnd ℂ (β p.2) = (β p.2)⁻¹ := by
          rw [Complex.inv_def, Complex.normSq_eq_norm_sq, hu, one_pow, inv_one,
            Complex.ofReal_one, mul_one]
        rw [hconj, mul_inv_eq_one₀ (h0 p.2)] at h1
        exact h1
      simpa using (tendsto_sum_pow_div_zero hz hne).const_mul
        (repulsionWeight β p.1 * starRingEnd ℂ (repulsionWeight β p.2))
  have hsum := tendsto_finsetSum _ hpair
  have hval : (∑ p ∈ (univ ×ˢ univ : Finset (ι × ι)),
      (if p.1 = p.2 then ((‖repulsionWeight β p.1‖ ^ 2 : ℝ) : ℂ) else 0)) =
      ((∑ i, ∏ j ∈ univ.erase i, 1 / ‖β i - β j‖ ^ 2 : ℝ) : ℂ) := by
    rw [sum_product]
    simp only [sum_ite_eq, mem_univ, if_true]
    push_cast
    refine sum_congr rfl fun i _ => ?_
    rw [← Complex.ofReal_pow, norm_repulsionWeight_sq hu]
    push_cast
    rfl
  rw [hval] at hsum
  have hident : ∀ M : ℕ, (∑ p ∈ (univ ×ˢ univ : Finset (ι × ι)),
      repulsionWeight β p.1 * starRingEnd ℂ (repulsionWeight β p.2) *
        ((∑ m ∈ Icc 1 M, (β p.1 * starRingEnd ℂ (β p.2)) ^ m) / M)) =
      (((∑ m ∈ Icc 1 M, ‖spectralMertensRow β m‖ ^ 2) / M : ℝ) : ℂ) := by
    intro M
    push_cast
    simp_rw [mul_div_assoc', mul_sum]
    rw [← sum_div, sum_comm]
    congr 1
    refine sum_congr rfl fun m _ => ?_
    rw [← Complex.ofReal_pow, ofReal_norm_spectralMertensRow_sq hinj h0]
  have hre := (Complex.continuous_re.tendsto _).comp hsum
  simp only [Function.comp_def, hident, Complex.ofReal_re] at hre
  exact hre

/-- **The Mertens budget of a pure curve with simple spectrum is the repulsion energy of its
Frobenius eigenvalues.** -/
theorem tendsto_curveMertens_energy_div (D : ArithmeticCastelnuovoSeveri.CurveDatum ι)
    [Nonempty ι] (hinj : Function.Injective D.β) (hu : ∀ i, ‖D.β i‖ = 1) :
    Tendsto (fun M : ℕ => (∑ m ∈ Icc 1 M, ‖spectralMertensRow D.β m‖ ^ 2) / M) atTop
      (𝓝 (∑ i, ∏ j ∈ univ.erase i, 1 / ‖D.β i - D.β j‖ ^ 2)) :=
  tendsto_spectralMertens_energy_div hinj hu

end GaloisForLFunctions.ArithmeticCorrespondencePositivity
