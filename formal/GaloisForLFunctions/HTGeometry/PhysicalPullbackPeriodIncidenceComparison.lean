import GaloisForLFunctions.HTGeometry.PeriodIncidenceMultiplier
import GaloisForLFunctions.HTGeometry.PhysicalArcContactVeronese

/-!
# Comparing the physical arc filtration with the powered period-incidence filtration

Evaluating an arc-coordinate polynomial at the regularized period symbol sends `λ` to `w`, hence
`λ^k` to `w^k`.  The evaluation is bounded because the symbol has norm at most one, so it lands in
the bounded period-incidence space.

The comparison is filtration preserving: a polynomial divisible by `λ^k` evaluates into the range
of multiplication by `w^k`.  Applied to the physical arc pullback of the squarefree annihilator,
whose contact order is exactly `r`, the whole ideal lands in the order-`r` powered incidence scale.
-/

open Filter
open scoped BigOperators Topology ENNReal

namespace GaloisForLFunctions

noncomputable section

variable {L : Submodule ℤ ℂ}

/-! ## Bounded evaluation at the period symbol -/

theorem norm_eval_le_sum_norm_coeff {z : ℂ} (hz : ‖z‖ ≤ 1) (P : Polynomial ℂ) :
    ‖Polynomial.eval z P‖ ≤ ∑ i ∈ P.support, ‖P.coeff i‖ := by
  classical
  rw [Polynomial.eval_eq_sum, Polynomial.sum]
  refine le_trans (norm_sum_le _ _) (Finset.sum_le_sum fun i _ => ?_)
  rw [norm_mul, norm_pow]
  have hpow : ‖z‖ ^ i ≤ 1 := pow_le_one₀ (norm_nonneg _) hz
  calc ‖P.coeff i‖ * ‖z‖ ^ i ≤ ‖P.coeff i‖ * 1 :=
        mul_le_mul_of_nonneg_left hpow (norm_nonneg _)
    _ = ‖P.coeff i‖ := mul_one _

/-- Evaluate an arc-coordinate polynomial at the regularized period symbol. -/
def arcEvalVector (L : Submodule ℤ ℂ) (P : Polynomial ℂ) :
    lp (fun _ : NonzeroPeriod L ↦ ℂ) ∞ :=
  ⟨fun q => Polynomial.eval (regularizedPeriodWeight q.1.1) P,
    memℓp_infty ⟨∑ i ∈ P.support, ‖P.coeff i‖, by
      rintro _ ⟨q, rfl⟩
      exact norm_eval_le_sum_norm_coeff (norm_regularizedPeriodWeight_le_one q.1.1) P⟩⟩

@[simp] theorem arcEvalVector_apply (L : Submodule ℤ ℂ) (P : Polynomial ℂ)
    (q : NonzeroPeriod L) :
    arcEvalVector L P q = Polynomial.eval (regularizedPeriodWeight q.1.1) P := rfl

/-! ## The comparison sends `λ^k` to `w^k` -/

/-- **`λ^k ↦ w^k`.** -/
theorem arcEvalVector_X_pow (L : Submodule ℤ ℂ) (k : ℕ) :
    arcEvalVector L (Polynomial.X ^ k) = poweredPeriodWeightVector L k := by
  ext q
  rw [arcEvalVector_apply, poweredPeriodWeightVector_apply, Polynomial.eval_pow,
    Polynomial.eval_X]

/-! ## Filtration preservation -/

/-- **The comparison is filtration preserving.**  A polynomial divisible by `λ^k` evaluates into
the range of multiplication by the order-`k` period symbol. -/
theorem arcEvalVector_mem_range_of_X_pow_dvd (L : Submodule ℤ ℂ) (k : ℕ)
    {P : Polynomial ℂ} (hdvd : (Polynomial.X : Polynomial ℂ) ^ k ∣ P) :
    arcEvalVector L P ∈ Set.range (poweredPeriodIncidenceMultiplier L k) := by
  obtain ⟨Q, rfl⟩ := hdvd
  refine ⟨arcEvalVector L Q, ?_⟩
  ext q
  rw [poweredPeriodIncidenceMultiplier_apply, arcEvalVector_apply, arcEvalVector_apply,
    Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_X]

/-! ## The squarefree annihilator lands in the order-`r` scale -/

/-- **Filtration-preserving comparison for the squarefree hierarchy.**  The physical arc pullback
of every element of the squarefree degree-`r` annihilator evaluates into the range of the order-`r`
powered period-incidence multiplier. -/
theorem veroneseIdeal_arcEval_mem_poweredRange
    {ι : Type*} [DecidableEq ι] (L : Submodule ℤ ℂ) (τ : ι → ℂ) {r : ℕ}
    {P : MvPolynomial ι ℂ} (hP : P ∈ VeroneseIdeal.veroneseIdeal ℂ ι r) :
    arcEvalVector L (VeroneseIdeal.physicalArcPullback τ P) ∈
      Set.range (poweredPeriodIncidenceMultiplier L r) :=
  arcEvalVector_mem_range_of_X_pow_dvd L r
    (VeroneseIdeal.pow_dvd_physicalArcPullback_of_mem_veroneseIdeal τ hP)

/-- The comparison of the two filtrations at a coface generator is exactly the order-`r` symbol,
up to the nonzero constant given by the period product. -/
theorem arcEval_physicalArcPullback_prod_X
    {ι : Type*} [DecidableEq ι] (L : Submodule ℤ ℂ) (τ : ι → ℂ) (S : Finset ι) :
    arcEvalVector L (VeroneseIdeal.physicalArcPullback τ (∏ j ∈ S, MvPolynomial.X j)) =
      (∏ j ∈ S, τ j) • poweredPeriodWeightVector L S.card := by
  rw [VeroneseIdeal.physicalArcPullback_prod_X]
  ext q
  rw [arcEvalVector_apply, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow,
    Polynomial.eval_X]
  change _ = (∏ j ∈ S, τ j) • (regularizedPeriodWeight q.1.1 ^ S.card)
  rw [smul_eq_mul]

/-! ## The arc-contact Rees filtration -/

/-- Operators whose physical arc pullback has contact order at least `k`. -/
def arcContactFiltration {ι : Type*} [DecidableEq ι] (τ : ι → ℂ) (k : ℕ) :
    Ideal (MvPolynomial ι ℂ) :=
  Ideal.comap (VeroneseIdeal.physicalArcPullback τ).toRingHom
    (Ideal.span {(Polynomial.X : Polynomial ℂ) ^ k})

theorem mem_arcContactFiltration_iff {ι : Type*} [DecidableEq ι] (τ : ι → ℂ) (k : ℕ)
    (P : MvPolynomial ι ℂ) :
    P ∈ arcContactFiltration τ k ↔
      (Polynomial.X : Polynomial ℂ) ^ k ∣ VeroneseIdeal.physicalArcPullback τ P := by
  rw [arcContactFiltration, Ideal.mem_comap, Ideal.mem_span_singleton]
  rfl

/-- The filtration is descending. -/
theorem arcContactFiltration_antitone {ι : Type*} [DecidableEq ι] (τ : ι → ℂ)
    {k l : ℕ} (hkl : k ≤ l) :
    arcContactFiltration τ l ≤ arcContactFiltration τ k := by
  intro P hP
  rw [mem_arcContactFiltration_iff] at hP ⊢
  exact dvd_trans (pow_dvd_pow _ hkl) hP

/-- **Rees property.**  Contact orders add under multiplication. -/
theorem arcContactFiltration_mul_le {ι : Type*} [DecidableEq ι] (τ : ι → ℂ) (k l : ℕ) :
    arcContactFiltration τ k * arcContactFiltration τ l ≤ arcContactFiltration τ (k + l) := by
  refine Ideal.mul_le.mpr fun P hP Q hQ => ?_
  rw [mem_arcContactFiltration_iff] at hP hQ ⊢
  rw [map_mul, pow_add]
  exact mul_dvd_mul hP hQ

theorem arcContactFiltration_zero {ι : Type*} [DecidableEq ι] (τ : ι → ℂ) :
    arcContactFiltration τ 0 = ⊤ := by
  refine Ideal.eq_top_iff_one _ |>.mpr ?_
  rw [mem_arcContactFiltration_iff]
  simp

/-- **The squarefree annihilator sits at level `r` of the Rees filtration.** -/
theorem veroneseIdeal_le_arcContactFiltration {ι : Type*} [DecidableEq ι] (τ : ι → ℂ) (r : ℕ) :
    VeroneseIdeal.veroneseIdeal ℂ ι r ≤ arcContactFiltration τ r := by
  intro P hP
  rw [mem_arcContactFiltration_iff]
  exact VeroneseIdeal.pow_dvd_physicalArcPullback_of_mem_veroneseIdeal τ hP

/-- **And no higher.**  With no vanishing period a coface generator already leaves level `r + 1`. -/
theorem veroneseIdeal_not_le_arcContactFiltration_succ {ι : Type*} [DecidableEq ι]
    (τ : ι → ℂ) (hτ : ∀ j, τ j ≠ 0) {r : ℕ} {S : Finset ι} (hS : S.card = r) :
    ¬ VeroneseIdeal.veroneseIdeal ℂ ι r ≤ arcContactFiltration τ (r + 1) := by
  intro hle
  have hmem : (∏ j ∈ S, MvPolynomial.X j) ∈ VeroneseIdeal.veroneseIdeal ℂ ι r :=
    Ideal.subset_span ⟨S, hS, rfl⟩
  have := (mem_arcContactFiltration_iff τ (r + 1) _).mp (hle hmem)
  exact (VeroneseIdeal.physicalArcPullback_generator_ne_zero τ hτ hS).2 this

/-- **Source-natural comparison of the two filtrations.**  Level `k` of the arc-contact Rees
filtration evaluates into the range of the order-`k` powered period-incidence multiplier. -/
theorem arcContactFiltration_arcEval_mem_poweredRange
    {ι : Type*} [DecidableEq ι] (L : Submodule ℤ ℂ) (τ : ι → ℂ) (k : ℕ)
    {P : MvPolynomial ι ℂ} (hP : P ∈ arcContactFiltration τ k) :
    arcEvalVector L (VeroneseIdeal.physicalArcPullback τ P) ∈
      Set.range (poweredPeriodIncidenceMultiplier L k) :=
  arcEvalVector_mem_range_of_X_pow_dvd L k ((mem_arcContactFiltration_iff τ k P).mp hP)

end

end GaloisForLFunctions
