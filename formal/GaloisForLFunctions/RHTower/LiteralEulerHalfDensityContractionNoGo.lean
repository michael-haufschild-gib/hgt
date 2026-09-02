import GaloisForLFunctions.HTGeometry.LpBoundedMultiplier
import GaloisForLFunctions.HTGeometry.PrimeEulerProductAperture
import GaloisForLFunctions.HTGeometry.PrimeTorusKroneckerDensity
import GaloisForLFunctions.HTGeometry.QuasiAbelianComplementWeightTransfer
import GaloisForLFunctions.RHTower.Sieve.MoebiusSmoothLimit
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.Analysis.Normed.Operator.BanachSteinhaus

/-!
# Literal Euler half-density contraction no-go

On the additive Fourier carrier, the literal cutoff Euler formation operator has multiplier

`∏_{p ≤ N} (1 - p⁻¹ᐟ² exp(i t log p))`.

Kronecker density of the prime-log flow makes all factors approach their maximizing phase `-1`
simultaneously.  Its exact operator norm is therefore `∏_{p ≤ N} (1 + p⁻¹ᐟ²)`.  These norms diverge,
so literal Euler formation is neither contractive nor strongly convergent to a bounded completion.
Any viable admissibility law must be a relative cancellation law, not raw operator contractivity.
-/

noncomputable section

open MeasureTheory Set Metric Filter Topology
open scoped ENNReal BigOperators

namespace GaloisForLFunctions.RHTower

open GaloisForLFunctions

/-- A continuous multiplier symbol is pointwise bounded by the norm of its `L²(ℝ)` multiplication
operator.  The proof localizes a unit vector on a finite positive-measure interval. -/
theorem continuous_symbol_le_multiplier_norm
    {φ : ℝ → ℂ} (hφ : Continuous φ) {C : ℝ} (hC0 : 0 ≤ C)
    (hC : ∀ x, ‖φ x‖ ≤ C) (x₀ : ℝ) :
    ‖φ x₀‖ ≤ ‖MeasureTheory.lpBoundedMulCLM (p := 2) (μ := (volume : Measure ℝ))
      hφ.measurable hC0 hC‖ := by
  let T := MeasureTheory.lpBoundedMulCLM (p := 2) (μ := (volume : Measure ℝ))
    hφ.measurable hC0 hC
  by_contra hnot
  have hop : ‖T‖ < ‖φ x₀‖ := lt_of_not_ge hnot
  let c : ℝ := (‖T‖ + ‖φ x₀‖) / 2
  have hcT : ‖T‖ < c := by dsimp [c]; linarith
  have hcv : c < ‖φ x₀‖ := by dsimp [c]; linarith
  have hc0 : 0 < c := lt_of_le_of_lt (norm_nonneg T) hcT
  have hev : ∀ᶠ x in 𝓝 x₀, c < ‖φ x‖ :=
    hφ.norm.continuousAt.eventually (isOpen_Ioi.mem_nhds hcv)
  rw [Metric.eventually_nhds_iff] at hev
  obtain ⟨δ, hδ, hball⟩ := hev
  let S : Set ℝ := Ioo (x₀ - δ / 2) (x₀ + δ / 2)
  have hSball : S ⊆ ball x₀ δ := by
    intro x hx
    rw [mem_ball, Real.dist_eq, abs_lt]
    constructor <;> linarith [hx.1, hx.2]
  have hSm : MeasurableSet S := measurableSet_Ioo
  have hSfin : volume S ≠ ∞ := by simp [S, Real.volume_Ioo]
  have hS0 : volume S ≠ 0 := by simpa [S, Real.volume_Ioo] using hδ
  let f : Lp ℂ 2 (volume : Measure ℝ) := indicatorConstLp 2 hSm hSfin (1 : ℂ)
  let g : Lp ℂ 2 (volume : Measure ℝ) := indicatorConstLp 2 hSm hSfin (c : ℂ)
  have hfnorm : ‖f‖ = (volume.real S) ^ (1 / (2 : ℝ≥0∞).toReal) := by
    rw [show f = indicatorConstLp 2 hSm hSfin (1 : ℂ) from rfl,
      norm_indicatorConstLp (by norm_num) (by norm_num)]
    simp
  have hgnorm : ‖g‖ = c * ‖f‖ := by
    rw [show g = indicatorConstLp 2 hSm hSfin (c : ℂ) from rfl,
      norm_indicatorConstLp (by norm_num) (by norm_num), hfnorm]
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hc0]
  have hfpos : 0 < ‖f‖ := by
    rw [hfnorm]
    exact Real.rpow_pos_of_pos (ENNReal.toReal_pos hS0 hSfin) _
  have hlower : ‖g‖ ≤ ‖T f‖ := by
    refine Lp.norm_le_norm_of_ae_le ?_
    filter_upwards [indicatorConstLp_coeFn (p := 2) (μ := (volume : Measure ℝ))
        (hs := hSm) (hμs := hSfin) (c := (1 : ℂ)),
      indicatorConstLp_coeFn (p := 2) (μ := (volume : Measure ℝ))
        (hs := hSm) (hμs := hSfin) (c := (c : ℂ)),
      MeasureTheory.lpBoundedMulCLM_coeFn (p := 2) (μ := (volume : Measure ℝ))
        hφ.measurable hC0 hC f] with x hfx hgx hTx
    rw [show (g : ℝ → ℂ) x = S.indicator (fun _ => (c : ℂ)) x from hgx,
      show (T f : Lp ℂ 2 (volume : Measure ℝ)) x = φ x * (f : ℝ → ℂ) x from hTx,
      show (f : ℝ → ℂ) x = S.indicator (fun _ => (1 : ℂ)) x from hfx]
    by_cases hx : x ∈ S
    · rw [Set.indicator_of_mem hx, Set.indicator_of_mem hx, mul_one,
        Complex.norm_real, Real.norm_eq_abs, abs_of_pos hc0]
      exact le_of_lt (hball (hSball hx))
    · simp [Set.indicator_of_notMem hx]
  have hupper : ‖T f‖ ≤ ‖T‖ * ‖f‖ := T.le_opNorm f
  rw [hgnorm] at hlower
  nlinarith

/-- Half-density weight attached to a prime. -/
def literalEulerHalfDensityWeight (p : Nat.Primes) : ℝ :=
  (Real.sqrt (((p : Nat.Primes) : ℕ) : ℝ))⁻¹

theorem literalEulerHalfDensityWeight_pos (p : Nat.Primes) :
    0 < literalEulerHalfDensityWeight p := by
  unfold literalEulerHalfDensityWeight
  have hp : (0 : ℝ) < (((p : Nat.Primes) : ℕ) : ℝ) := by exact_mod_cast p.2.pos
  exact inv_pos.mpr (Real.sqrt_pos.2 hp)

theorem literalEulerHalfDensityWeight_le_one (p : Nat.Primes) :
    literalEulerHalfDensityWeight p ≤ 1 := by
  unfold literalEulerHalfDensityWeight
  have hp1 : (1 : ℝ) ≤ (((p : Nat.Primes) : ℕ) : ℝ) := by
    exact_mod_cast (p.2.two_le.trans' (by omega : 1 ≤ 2))
  have hp : (0 : ℝ) < (((p : Nat.Primes) : ℕ) : ℝ) := by exact_mod_cast p.2.pos
  exact (inv_le_one₀ (Real.sqrt_pos.2 hp)).2 (Real.one_le_sqrt.mpr hp1)

/-- Fourier multiplier of literal Euler formation through aperture `N`. -/
def literalEulerHalfDensitySymbol (N : ℕ) (t : ℝ) : ℂ :=
  ∏ p : primesLE N,
    (1 - (literalEulerHalfDensityWeight (p : Nat.Primes) : ℂ) *
      expChar (Real.log (((p : Nat.Primes) : ℕ) : ℝ)) t)

/-- Candidate exact operator-norm budget. -/
def literalEulerHalfDensityBudget (N : ℕ) : ℝ :=
  ∏ p : primesLE N, (1 + literalEulerHalfDensityWeight (p : Nat.Primes))

theorem literalEulerHalfDensitySymbol_continuous (N : ℕ) :
    Continuous (literalEulerHalfDensitySymbol N) := by
  unfold literalEulerHalfDensitySymbol
  apply continuous_finsetProd
  intro p _
  exact continuous_const.sub (continuous_const.mul (continuous_expChar _))

theorem literalEulerHalfDensityBudget_nonneg (N : ℕ) :
    0 ≤ literalEulerHalfDensityBudget N := by
  unfold literalEulerHalfDensityBudget
  exact Finset.prod_nonneg fun p _ => by
    linarith [literalEulerHalfDensityWeight_pos (p : Nat.Primes)]

theorem norm_literalEulerHalfDensitySymbol_le (N : ℕ) (t : ℝ) :
    ‖literalEulerHalfDensitySymbol N t‖ ≤ literalEulerHalfDensityBudget N := by
  rw [literalEulerHalfDensitySymbol, literalEulerHalfDensityBudget, norm_prod]
  exact Finset.prod_le_prod (fun _ _ => norm_nonneg _) (fun p _ => by
    calc
      ‖1 - (literalEulerHalfDensityWeight (p : Nat.Primes) : ℂ) *
          expChar (Real.log (((p : Nat.Primes) : ℕ) : ℝ)) t‖
          ≤ ‖(1 : ℂ)‖ + ‖(literalEulerHalfDensityWeight (p : Nat.Primes) : ℂ) *
              expChar (Real.log (((p : Nat.Primes) : ℕ) : ℝ)) t‖ := norm_sub_le _ _
      _ = 1 + literalEulerHalfDensityWeight (p : Nat.Primes) := by
        rw [norm_one, norm_mul, norm_expChar, mul_one, Complex.norm_real,
          Real.norm_eq_abs, abs_of_pos (literalEulerHalfDensityWeight_pos _)])

theorem literalEulerHalfDensity_target_eq_budget (N : ℕ) :
    (∏ p : primesLE N,
      (1 - (literalEulerHalfDensityWeight (p : Nat.Primes) : ℂ) * (-1))) =
      (literalEulerHalfDensityBudget N : ℂ) := by
  rw [literalEulerHalfDensityBudget, Complex.ofReal_prod]
  apply Finset.prod_congr rfl
  intro p _
  push_cast
  ring

/-- Prime-log Kronecker density approaches the norm budget arbitrarily closely. -/
theorem exists_norm_literalEulerHalfDensitySymbol_gt (N : ℕ) {c : ℝ}
    (hc : c < literalEulerHalfDensityBudget N) :
    ∃ t : ℝ, c < ‖literalEulerHalfDensitySymbol N t‖ := by
  let A : ℝ := ((primesLE N).card : ℝ) * 2 ^ (primesLE N).card
  let δ : ℝ := (literalEulerHalfDensityBudget N - c) / (A + 1)
  have hA0 : 0 ≤ A := by dsimp [A]; positivity
  have hden : 0 < A + 1 := by linarith
  have hδ : 0 < δ := div_pos (sub_pos.mpr hc) hden
  obtain ⟨t, ht⟩ := primeTorus_kronecker_dense N (fun _ => Real.pi) hδ
  have ht' : ∀ p : primesLE N,
      ‖expChar (Real.log (((p : Nat.Primes) : ℕ) : ℝ)) t - (-1 : ℂ)‖ < δ := by
    intro p
    simpa [Complex.exp_pi_mul_I] using ht p
  have hprod := norm_prod_sub_prod_le
    (fun p : primesLE N =>
      1 - (literalEulerHalfDensityWeight (p : Nat.Primes) : ℂ) *
        expChar (Real.log (((p : Nat.Primes) : ℕ) : ℝ)) t)
    (fun p : primesLE N =>
      1 - (literalEulerHalfDensityWeight (p : Nat.Primes) : ℂ) * (-1))
    (C := 2) (δ := δ) (by norm_num) hδ.le (Finset.univ)
  have hactual : ∀ p ∈ (Finset.univ : Finset (primesLE N)),
      ‖1 - (literalEulerHalfDensityWeight (p : Nat.Primes) : ℂ) *
        expChar (Real.log (((p : Nat.Primes) : ℕ) : ℝ)) t‖ ≤ 2 := by
    intro p _
    calc
      ‖1 - (literalEulerHalfDensityWeight (p : Nat.Primes) : ℂ) *
          expChar (Real.log (((p : Nat.Primes) : ℕ) : ℝ)) t‖
          ≤ 1 + literalEulerHalfDensityWeight (p : Nat.Primes) := by
            simpa [Complex.norm_real, Real.norm_eq_abs,
              abs_of_pos (literalEulerHalfDensityWeight_pos _)] using
              (norm_sub_le (1 : ℂ)
                ((literalEulerHalfDensityWeight (p : Nat.Primes) : ℂ) *
                  expChar (Real.log (((p : Nat.Primes) : ℕ) : ℝ)) t))
      _ ≤ 2 := by linarith [literalEulerHalfDensityWeight_le_one (p : Nat.Primes)]
  have htarget : ∀ p ∈ (Finset.univ : Finset (primesLE N)),
      ‖1 - (literalEulerHalfDensityWeight (p : Nat.Primes) : ℂ) * (-1)‖ ≤ 2 := by
    intro p _
    rw [show (1 : ℂ) - (literalEulerHalfDensityWeight (p : Nat.Primes) : ℂ) * (-1) =
      (1 + literalEulerHalfDensityWeight (p : Nat.Primes) : ℝ) by push_cast; ring,
      Complex.norm_real, Real.norm_eq_abs, abs_of_pos]
    · linarith [literalEulerHalfDensityWeight_le_one (p : Nat.Primes)]
    · linarith [literalEulerHalfDensityWeight_pos (p : Nat.Primes)]
  have hdiff : ∀ p ∈ (Finset.univ : Finset (primesLE N)),
      ‖(1 - (literalEulerHalfDensityWeight (p : Nat.Primes) : ℂ) *
          expChar (Real.log (((p : Nat.Primes) : ℕ) : ℝ)) t) -
        (1 - (literalEulerHalfDensityWeight (p : Nat.Primes) : ℂ) * (-1))‖ ≤ δ := by
    intro p _
    have heq :
        (1 - (literalEulerHalfDensityWeight (p : Nat.Primes) : ℂ) *
            expChar (Real.log (((p : Nat.Primes) : ℕ) : ℝ)) t) -
          (1 - (literalEulerHalfDensityWeight (p : Nat.Primes) : ℂ) * (-1)) =
        -(literalEulerHalfDensityWeight (p : Nat.Primes) : ℂ) *
          (expChar (Real.log (((p : Nat.Primes) : ℕ) : ℝ)) t - (-1)) := by ring
    rw [heq, norm_mul, norm_neg, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (literalEulerHalfDensityWeight_pos _)]
    exact (calc
      literalEulerHalfDensityWeight (p : Nat.Primes) *
          ‖expChar (Real.log (((p : Nat.Primes) : ℕ) : ℝ)) t - -1‖
          ≤ 1 * ‖expChar (Real.log (((p : Nat.Primes) : ℕ) : ℝ)) t - -1‖ :=
            mul_le_mul_of_nonneg_right (literalEulerHalfDensityWeight_le_one _) (norm_nonneg _)
      _ < 1 * δ := mul_lt_mul_of_pos_left (ht' p) zero_lt_one
      _ = δ := one_mul _).le
  have hclose := hprod hactual htarget hdiff
  simp only [Finset.card_univ, Fintype.card_coe] at hclose
  have hclose' :
      ‖literalEulerHalfDensitySymbol N t - (literalEulerHalfDensityBudget N : ℂ)‖ ≤ A * δ := by
    rw [literalEulerHalfDensitySymbol, ← literalEulerHalfDensity_target_eq_budget]
    simpa [A] using hclose
  have hδeq : (A + 1) * δ = literalEulerHalfDensityBudget N - c := by
    change (A + 1) * ((literalEulerHalfDensityBudget N - c) / (A + 1)) = _
    exact mul_div_cancel₀ _ hden.ne'
  have herror : A * δ < literalEulerHalfDensityBudget N - c := by
    nlinarith [hδeq, hδ]
  refine ⟨t, ?_⟩
  have htriangle : literalEulerHalfDensityBudget N ≤
      ‖literalEulerHalfDensitySymbol N t - (literalEulerHalfDensityBudget N : ℂ)‖ +
        ‖literalEulerHalfDensitySymbol N t‖ := by
    have h := norm_add_le
      ((literalEulerHalfDensityBudget N : ℂ) - literalEulerHalfDensitySymbol N t)
      (literalEulerHalfDensitySymbol N t)
    rw [sub_add_cancel, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (literalEulerHalfDensityBudget_nonneg N), norm_sub_rev] at h
    exact h
  nlinarith [hclose', herror]

/-- Literal finite Euler formation as an `L²(ℝ)` Fourier multiplier. -/
def literalEulerHalfDensityOperator (N : ℕ) :
    Lp ℂ 2 (volume : Measure ℝ) →L[ℂ] Lp ℂ 2 (volume : Measure ℝ) :=
  MeasureTheory.lpBoundedMulCLM
    (literalEulerHalfDensitySymbol_continuous N).measurable
    (literalEulerHalfDensityBudget_nonneg N)
    (norm_literalEulerHalfDensitySymbol_le N)

/-- **Exact finite-cutoff norm law.** -/
theorem norm_literalEulerHalfDensityOperator (N : ℕ) :
    ‖literalEulerHalfDensityOperator N‖ = literalEulerHalfDensityBudget N := by
  apply le_antisymm
  · exact MeasureTheory.norm_lpBoundedMulCLM_le
      (literalEulerHalfDensitySymbol_continuous N).measurable
      (literalEulerHalfDensityBudget_nonneg N)
      (norm_literalEulerHalfDensitySymbol_le N)
  · apply le_of_forall_lt
    intro c hc
    obtain ⟨t, ht⟩ := exists_norm_literalEulerHalfDensitySymbol_gt N hc
    exact ht.trans_le (continuous_symbol_le_multiplier_norm
      (literalEulerHalfDensitySymbol_continuous N)
      (literalEulerHalfDensityBudget_nonneg N)
      (norm_literalEulerHalfDensitySymbol_le N) t)

theorem literalEulerHalfDensityBudget_eq_primesBelow (N : ℕ) :
    literalEulerHalfDensityBudget N =
      ∏ p ∈ Nat.primesBelow (N + 1), (1 + (Real.sqrt (p : ℝ))⁻¹) := by
  rw [literalEulerHalfDensityBudget]
  calc
    (∏ p : primesLE N, (1 + literalEulerHalfDensityWeight (p : Nat.Primes))) =
        ∏ p ∈ primesLE N, (1 + literalEulerHalfDensityWeight p) :=
      (Finset.prod_subtype (primesLE N) (fun _ => Iff.rfl)
        (fun p : Nat.Primes => 1 + literalEulerHalfDensityWeight p)).symm
    _ = ∏ p ∈ Nat.primesBelow (N + 1), (1 + (Real.sqrt (p : ℝ))⁻¹) := by
      rw [primesLE, Finset.prod_map]
      change
        (∏ p ∈ (Nat.primesBelow (N + 1)).attach,
          (1 + (Real.sqrt (((p : {p // p ∈ Nat.primesBelow (N + 1)}) : ℕ) : ℝ))⁻¹)) =
          ∏ p ∈ Nat.primesBelow (N + 1), (1 + (Real.sqrt (p : ℝ))⁻¹)
      exact Finset.prod_attach (Nat.primesBelow (N + 1))
        (fun p : ℕ => 1 + (Real.sqrt (p : ℝ))⁻¹)

theorem primeReciprocal_le_halfDensityWeight {p : ℕ} (hp : p.Prime) :
    1 / (p : ℝ) ≤ (Real.sqrt (p : ℝ))⁻¹ := by
  have hp0 : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp.pos
  have hp1 : (1 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp.one_le
  have hs0 : 0 < Real.sqrt (p : ℝ) := Real.sqrt_pos.2 hp0
  have hsle : Real.sqrt (p : ℝ) ≤ (p : ℝ) :=
    Real.sqrt_le_self_iff.mpr (Or.inr hp1)
  simpa [one_div] using (inv_le_inv₀ hp0 hs0).2 hsle

/-- The exact norm budget dominates the divergent prime harmonic sum. -/
theorem one_add_primeReciprocalSum_le_literalEulerHalfDensityBudget (N : ℕ) :
    1 + ∑ p ∈ Nat.primesBelow (N + 1), 1 / (p : ℝ) ≤
      literalEulerHalfDensityBudget N := by
  rw [literalEulerHalfDensityBudget_eq_primesBelow]
  calc
    1 + ∑ p ∈ Nat.primesBelow (N + 1), 1 / (p : ℝ) ≤
        1 + ∑ p ∈ Nat.primesBelow (N + 1), (Real.sqrt (p : ℝ))⁻¹ := by
      gcongr with p hp
      exact primeReciprocal_le_halfDensityWeight (Nat.prime_of_mem_primesBelow hp)
    _ ≤ ∏ p ∈ Nat.primesBelow (N + 1), (1 + (Real.sqrt (p : ℝ))⁻¹) :=
      GaloisForLFunctions.HTGeometry.one_add_sum_le_prod_one_add
        (Nat.primesBelow (N + 1)) (fun p => (Real.sqrt (p : ℝ))⁻¹) (fun p => by positivity)

theorem tendsto_literalEulerHalfDensityBudget_atTop :
    Tendsto literalEulerHalfDensityBudget atTop atTop := by
  rw [Filter.tendsto_atTop]
  intro b
  have hshift : Tendsto (fun N : ℕ => N + 1) atTop atTop :=
    Filter.tendsto_add_atTop_nat 1
  have hsum := RHTower.Sieve.tendsto_sum_primesBelow_inv_atTop.comp hshift
  have hev := hsum.eventually (eventually_ge_atTop b)
  filter_upwards [hev] with N hN
  exact hN.trans ((le_add_of_nonneg_left zero_le_one).trans
    (one_add_primeReciprocalSum_le_literalEulerHalfDensityBudget N))

/-- Literal finite Euler formation norms diverge. -/
theorem tendsto_norm_literalEulerHalfDensityOperator_atTop :
    Tendsto (fun N => ‖literalEulerHalfDensityOperator N‖) atTop atTop := by
  simpa only [norm_literalEulerHalfDensityOperator] using
    tendsto_literalEulerHalfDensityBudget_atTop

theorem literalEulerHalfDensityOperator_not_uniformly_bounded :
    ¬ ∃ C : ℝ, ∀ N : ℕ, ‖literalEulerHalfDensityOperator N‖ ≤ C := by
  rintro ⟨C, hC⟩
  have hev := tendsto_norm_literalEulerHalfDensityOperator_atTop.eventually
    (eventually_gt_atTop C)
  obtain ⟨N, hN⟩ := hev.exists
  exact (not_lt_of_ge (hC N)) hN

/-- **Completion no-go.**  Literal Euler cutoff formation has no strong limit which is a bounded
operator on the additive Fourier half-density carrier. -/
theorem literalEulerHalfDensityOperator_no_strong_bounded_completion :
    ¬ ∃ T : Lp ℂ 2 (volume : Measure ℝ) →L[ℂ] Lp ℂ 2 (volume : Measure ℝ),
      ∀ f, Tendsto (fun N => literalEulerHalfDensityOperator N f) atTop (𝓝 (T f)) := by
  rintro ⟨T, hT⟩
  have hpoint : ∀ f : Lp ℂ 2 (volume : Measure ℝ),
      ∃ C : ℝ, ∀ N, ‖literalEulerHalfDensityOperator N f‖ ≤ C := by
    intro f
    obtain ⟨C, hC⟩ := (hT f).norm.bddAbove_range
    exact ⟨C, fun N => hC ⟨N, rfl⟩⟩
  obtain ⟨C, hC⟩ := banach_steinhaus hpoint
  exact literalEulerHalfDensityOperator_not_uniformly_bounded ⟨C, hC⟩

/-- **Weak completion no-go.**  Literal Euler cutoff formation has no weak-operator limit which is
a bounded operator on the additive Fourier half-density carrier. -/
theorem literalEulerHalfDensityOperator_no_weak_bounded_completion :
    ¬ ∃ T : Lp ℂ 2 (volume : Measure ℝ) →L[ℂ] Lp ℂ 2 (volume : Measure ℝ),
      ∀ f g, Tendsto (fun N => inner ℂ (literalEulerHalfDensityOperator N f) g) atTop
        (𝓝 (inner ℂ (T f) g)) := by
  rintro ⟨T, hT⟩
  have hpoint : ∀ f : Lp ℂ 2 (volume : Measure ℝ),
      ∃ C : ℝ, ∀ N, ‖literalEulerHalfDensityOperator N f‖ ≤ C := by
    intro f
    have hfunctional : ∀ g : Lp ℂ 2 (volume : Measure ℝ),
        ∃ C : ℝ, ∀ N,
          ‖innerSL ℂ (literalEulerHalfDensityOperator N f) g‖ ≤ C := by
      intro g
      obtain ⟨C, hC⟩ := (hT f g).norm.bddAbove_range
      exact ⟨C, fun N => by simpa [innerSL_apply_apply] using hC ⟨N, rfl⟩⟩
    obtain ⟨C, hC⟩ := banach_steinhaus hfunctional
    exact ⟨C, fun N => by simpa [innerSL_apply_norm] using hC N⟩
  obtain ⟨C, hC⟩ := banach_steinhaus hpoint
  exact literalEulerHalfDensityOperator_not_uniformly_bounded ⟨C, hC⟩

end GaloisForLFunctions.RHTower
