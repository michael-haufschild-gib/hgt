import GaloisForLFunctions.RHTower.LiteralEulerHalfDensityContractionNoGo

/-!
# Literal Euler half-density norm law on arbitrary finite prime sets

`LiteralEulerHalfDensityContractionNoGo` computes the exact operator norm of the literal cutoff
Euler formation multiplier for the initial prime segments `p ≤ N`.  This module proves the law for
an *arbitrary* finite set `S` of primes:

`‖E_S‖ = ∏_{p ∈ S} (1 + p^{-1/2})`,

so `E_S` is never a contraction when `S` is nonempty, and along *every* increasing exhaustion of
the primes the norms diverge and no strong or weak bounded completion exists.
-/

noncomputable section

open MeasureTheory Set Metric Filter Topology
open scoped ENNReal BigOperators

namespace GaloisForLFunctions.RHTower

open GaloisForLFunctions

/-- Fourier multiplier of literal Euler formation over a finite prime set `S`. -/
def literalEulerHalfDensitySymbolOn (S : Finset Nat.Primes) (t : ℝ) : ℂ :=
  ∏ p ∈ S, (1 - (literalEulerHalfDensityWeight p : ℂ) *
    expChar (Real.log ((p : ℕ) : ℝ)) t)

/-- Exact norm budget over a finite prime set `S`. -/
def literalEulerHalfDensityBudgetOn (S : Finset Nat.Primes) : ℝ :=
  ∏ p ∈ S, (1 + literalEulerHalfDensityWeight p)

theorem literalEulerHalfDensitySymbolOn_continuous (S : Finset Nat.Primes) :
    Continuous (literalEulerHalfDensitySymbolOn S) := by
  unfold literalEulerHalfDensitySymbolOn
  apply continuous_finsetProd
  intro p _
  exact continuous_const.sub (continuous_const.mul (continuous_expChar _))

theorem one_le_literalEulerHalfDensityBudgetOn (S : Finset Nat.Primes) :
    1 ≤ literalEulerHalfDensityBudgetOn S := by
  unfold literalEulerHalfDensityBudgetOn
  exact Finset.one_le_prod fun p _ => by
    linarith [literalEulerHalfDensityWeight_pos p]

theorem literalEulerHalfDensityBudgetOn_nonneg (S : Finset Nat.Primes) :
    0 ≤ literalEulerHalfDensityBudgetOn S :=
  zero_le_one.trans (one_le_literalEulerHalfDensityBudgetOn S)

/-- Enlarging the prime set can only enlarge the budget: every factor is at least one. -/
theorem literalEulerHalfDensityBudgetOn_mono {S T : Finset Nat.Primes} (hST : S ⊆ T) :
    literalEulerHalfDensityBudgetOn S ≤ literalEulerHalfDensityBudgetOn T := by
  unfold literalEulerHalfDensityBudgetOn
  rw [← Finset.prod_sdiff hST]
  have h1 : 1 ≤ ∏ p ∈ T \ S, (1 + literalEulerHalfDensityWeight p) :=
    Finset.one_le_prod fun p _ => by linarith [literalEulerHalfDensityWeight_pos p]
  have h0 : 0 ≤ ∏ p ∈ S, (1 + literalEulerHalfDensityWeight p) :=
    Finset.prod_nonneg fun p _ => by linarith [literalEulerHalfDensityWeight_pos p]
  nlinarith

/-- On a nonempty prime set the budget is strictly larger than one. -/
theorem one_lt_literalEulerHalfDensityBudgetOn {S : Finset Nat.Primes} (hS : S.Nonempty) :
    1 < literalEulerHalfDensityBudgetOn S := by
  obtain ⟨q, hq⟩ := hS
  have hsingle : literalEulerHalfDensityBudgetOn {q} ≤ literalEulerHalfDensityBudgetOn S :=
    literalEulerHalfDensityBudgetOn_mono (Finset.singleton_subset_iff.mpr hq)
  have hq1 : 1 < literalEulerHalfDensityBudgetOn {q} := by
    rw [literalEulerHalfDensityBudgetOn, Finset.prod_singleton]
    linarith [literalEulerHalfDensityWeight_pos q]
  exact hq1.trans_le hsingle

theorem norm_literalEulerHalfDensitySymbolOn_le (S : Finset Nat.Primes) (t : ℝ) :
    ‖literalEulerHalfDensitySymbolOn S t‖ ≤ literalEulerHalfDensityBudgetOn S := by
  rw [literalEulerHalfDensitySymbolOn, literalEulerHalfDensityBudgetOn, norm_prod]
  exact Finset.prod_le_prod (fun _ _ => norm_nonneg _) (fun p _ => by
    calc
      ‖1 - (literalEulerHalfDensityWeight p : ℂ) * expChar (Real.log ((p : ℕ) : ℝ)) t‖
          ≤ ‖(1 : ℂ)‖ + ‖(literalEulerHalfDensityWeight p : ℂ) *
              expChar (Real.log ((p : ℕ) : ℝ)) t‖ := norm_sub_le _ _
      _ = 1 + literalEulerHalfDensityWeight p := by
        rw [norm_one, norm_mul, norm_expChar, mul_one, Complex.norm_real,
          Real.norm_eq_abs, abs_of_pos (literalEulerHalfDensityWeight_pos _)])

/-- Every finite prime set lies in some initial aperture `primesLE N`. -/
theorem exists_subset_primesLE (S : Finset Nat.Primes) : ∃ N, S ⊆ primesLE N :=
  ⟨S.sup (fun p => (p : ℕ)), fun p hp => by
    rw [mem_primesLE]
    exact Finset.le_sup (f := fun p : Nat.Primes => (p : ℕ)) hp⟩

/-- Prime-log Kronecker density approaches the budget of an arbitrary finite prime set. -/
theorem exists_norm_literalEulerHalfDensitySymbolOn_gt (S : Finset Nat.Primes) {c : ℝ}
    (hc : c < literalEulerHalfDensityBudgetOn S) :
    ∃ t : ℝ, c < ‖literalEulerHalfDensitySymbolOn S t‖ := by
  obtain ⟨N, hSN⟩ := exists_subset_primesLE S
  let A : ℝ := (S.card : ℝ) * 2 ^ S.card
  let δ : ℝ := (literalEulerHalfDensityBudgetOn S - c) / (A + 1)
  have hA0 : 0 ≤ A := by dsimp [A]; positivity
  have hden : 0 < A + 1 := by linarith
  have hδ : 0 < δ := div_pos (sub_pos.mpr hc) hden
  obtain ⟨t, ht⟩ := primeTorus_kronecker_dense N (fun _ => Real.pi) hδ
  have ht' : ∀ p ∈ S,
      ‖expChar (Real.log ((p : ℕ) : ℝ)) t - (-1 : ℂ)‖ < δ := by
    intro p hp
    simpa [Complex.exp_pi_mul_I] using ht ⟨p, hSN hp⟩
  have hw1 : ∀ p : Nat.Primes, 1 + literalEulerHalfDensityWeight p ≤ 2 := fun p => by
    linarith [literalEulerHalfDensityWeight_le_one p]
  have hactual : ∀ p ∈ S,
      ‖1 - (literalEulerHalfDensityWeight p : ℂ) * expChar (Real.log ((p : ℕ) : ℝ)) t‖ ≤ 2 := by
    intro p _
    calc
      ‖1 - (literalEulerHalfDensityWeight p : ℂ) * expChar (Real.log ((p : ℕ) : ℝ)) t‖
          ≤ 1 + literalEulerHalfDensityWeight p := by
            simpa [Complex.norm_real, Real.norm_eq_abs,
              abs_of_pos (literalEulerHalfDensityWeight_pos _)] using
              (norm_sub_le (1 : ℂ)
                ((literalEulerHalfDensityWeight p : ℂ) * expChar (Real.log ((p : ℕ) : ℝ)) t))
      _ ≤ 2 := hw1 p
  have htarget : ∀ p ∈ S,
      ‖1 - (literalEulerHalfDensityWeight p : ℂ) * (-1)‖ ≤ 2 := by
    intro p _
    rw [show (1 : ℂ) - (literalEulerHalfDensityWeight p : ℂ) * (-1) =
      (1 + literalEulerHalfDensityWeight p : ℝ) by push_cast; ring,
      Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (by linarith [literalEulerHalfDensityWeight_pos p])]
    exact hw1 p
  have hdiff : ∀ p ∈ S,
      ‖(1 - (literalEulerHalfDensityWeight p : ℂ) * expChar (Real.log ((p : ℕ) : ℝ)) t) -
        (1 - (literalEulerHalfDensityWeight p : ℂ) * (-1))‖ ≤ δ := by
    intro p hp
    have heq :
        (1 - (literalEulerHalfDensityWeight p : ℂ) * expChar (Real.log ((p : ℕ) : ℝ)) t) -
          (1 - (literalEulerHalfDensityWeight p : ℂ) * (-1)) =
        -(literalEulerHalfDensityWeight p : ℂ) *
          (expChar (Real.log ((p : ℕ) : ℝ)) t - (-1)) := by ring
    rw [heq, norm_mul, norm_neg, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (literalEulerHalfDensityWeight_pos _)]
    exact (calc
      literalEulerHalfDensityWeight p * ‖expChar (Real.log ((p : ℕ) : ℝ)) t - -1‖
          ≤ 1 * ‖expChar (Real.log ((p : ℕ) : ℝ)) t - -1‖ :=
            mul_le_mul_of_nonneg_right (literalEulerHalfDensityWeight_le_one _) (norm_nonneg _)
      _ < 1 * δ := mul_lt_mul_of_pos_left (ht' p hp) zero_lt_one
      _ = δ := one_mul _).le
  have hclose := norm_prod_sub_prod_le
    (fun p : Nat.Primes =>
      1 - (literalEulerHalfDensityWeight p : ℂ) * expChar (Real.log ((p : ℕ) : ℝ)) t)
    (fun p : Nat.Primes => 1 - (literalEulerHalfDensityWeight p : ℂ) * (-1))
    (C := 2) (δ := δ) (by norm_num) hδ.le S hactual htarget hdiff
  have htargetProd :
      (∏ p ∈ S, (1 - (literalEulerHalfDensityWeight p : ℂ) * (-1))) =
        (literalEulerHalfDensityBudgetOn S : ℂ) := by
    rw [literalEulerHalfDensityBudgetOn, Complex.ofReal_prod]
    exact Finset.prod_congr rfl fun p _ => by push_cast; ring
  have hclose' :
      ‖literalEulerHalfDensitySymbolOn S t - (literalEulerHalfDensityBudgetOn S : ℂ)‖ ≤
        A * δ := by
    rw [literalEulerHalfDensitySymbolOn, ← htargetProd]
    simpa [A] using hclose
  have hδeq : (A + 1) * δ = literalEulerHalfDensityBudgetOn S - c := by
    change (A + 1) * ((literalEulerHalfDensityBudgetOn S - c) / (A + 1)) = _
    exact mul_div_cancel₀ _ hden.ne'
  have herror : A * δ < literalEulerHalfDensityBudgetOn S - c := by
    nlinarith [hδeq, hδ]
  refine ⟨t, ?_⟩
  have htriangle : literalEulerHalfDensityBudgetOn S ≤
      ‖literalEulerHalfDensitySymbolOn S t - (literalEulerHalfDensityBudgetOn S : ℂ)‖ +
        ‖literalEulerHalfDensitySymbolOn S t‖ := by
    have h := norm_add_le
      ((literalEulerHalfDensityBudgetOn S : ℂ) - literalEulerHalfDensitySymbolOn S t)
      (literalEulerHalfDensitySymbolOn S t)
    rw [sub_add_cancel, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (literalEulerHalfDensityBudgetOn_nonneg S), norm_sub_rev] at h
    exact h
  nlinarith [hclose', herror]

/-- Literal Euler formation over a finite prime set as an `L²(ℝ)` Fourier multiplier. -/
def literalEulerHalfDensityOperatorOn (S : Finset Nat.Primes) :
    Lp ℂ 2 (volume : Measure ℝ) →L[ℂ] Lp ℂ 2 (volume : Measure ℝ) :=
  MeasureTheory.lpBoundedMulCLM
    (literalEulerHalfDensitySymbolOn_continuous S).measurable
    (literalEulerHalfDensityBudgetOn_nonneg S)
    (norm_literalEulerHalfDensitySymbolOn_le S)

/-- **Exact finite-set norm law:** `‖E_S‖ = ∏_{p ∈ S} (1 + p^{-1/2})`. -/
theorem norm_literalEulerHalfDensityOperatorOn (S : Finset Nat.Primes) :
    ‖literalEulerHalfDensityOperatorOn S‖ = literalEulerHalfDensityBudgetOn S := by
  apply le_antisymm
  · exact MeasureTheory.norm_lpBoundedMulCLM_le
      (literalEulerHalfDensitySymbolOn_continuous S).measurable
      (literalEulerHalfDensityBudgetOn_nonneg S)
      (norm_literalEulerHalfDensitySymbolOn_le S)
  · apply le_of_forall_lt
    intro c hc
    obtain ⟨t, ht⟩ := exists_norm_literalEulerHalfDensitySymbolOn_gt S hc
    exact ht.trans_le (continuous_symbol_le_multiplier_norm
      (literalEulerHalfDensitySymbolOn_continuous S)
      (literalEulerHalfDensityBudgetOn_nonneg S)
      (norm_literalEulerHalfDensitySymbolOn_le S) t)

/-- The budget written with the arithmetic half-density weights `p^{-1/2}`. -/
theorem literalEulerHalfDensityBudgetOn_eq (S : Finset Nat.Primes) :
    literalEulerHalfDensityBudgetOn S =
      ∏ p ∈ S, (1 + Real.rpow ((p : ℕ) : ℝ) (-(1 / 2 : ℝ))) := by
  unfold literalEulerHalfDensityBudgetOn literalEulerHalfDensityWeight
  refine Finset.prod_congr rfl fun p _ => ?_
  have hp : (0 : ℝ) ≤ ((p : ℕ) : ℝ) := Nat.cast_nonneg _
  rw [Real.sqrt_eq_rpow, ← Real.rpow_neg hp]
  rfl

/-- **Non-contraction:** for every nonempty finite prime set the literal Euler operator has norm
strictly larger than one. -/
theorem one_lt_norm_literalEulerHalfDensityOperatorOn {S : Finset Nat.Primes}
    (hS : S.Nonempty) :
    1 < ‖literalEulerHalfDensityOperatorOn S‖ := by
  rw [norm_literalEulerHalfDensityOperatorOn]
  exact one_lt_literalEulerHalfDensityBudgetOn hS

/-- The initial-segment operator of `LiteralEulerHalfDensityContractionNoGo` is the finite-set
operator on `primesLE N`. -/
theorem literalEulerHalfDensityBudgetOn_primesLE (N : ℕ) :
    literalEulerHalfDensityBudgetOn (primesLE N) = literalEulerHalfDensityBudget N := by
  unfold literalEulerHalfDensityBudgetOn literalEulerHalfDensityBudget
  exact (Finset.prod_coe_sort (primesLE N) (fun p => 1 + literalEulerHalfDensityWeight p)).symm

/-- An increasing exhaustion of the primes by finite sets. -/
structure PrimeExhaustion (S : ℕ → Finset Nat.Primes) : Prop where
  mono : Monotone S
  exhaust : ∀ p : Nat.Primes, ∃ k, p ∈ S k

/-- Along any increasing exhaustion, each initial aperture is eventually contained in the stage. -/
theorem PrimeExhaustion.eventually_primesLE_subset {S : ℕ → Finset Nat.Primes}
    (hS : PrimeExhaustion S) (N : ℕ) : ∀ᶠ k in atTop, primesLE N ⊆ S k := by
  classical
  have hfin : ∀ T : Finset Nat.Primes, ∃ k, T ⊆ S k := by
    intro T
    induction T using Finset.induction_on with
    | empty => exact ⟨0, Finset.empty_subset _⟩
    | insert q T _ ih =>
        obtain ⟨k, hk⟩ := ih
        obtain ⟨l, hl⟩ := hS.exhaust q
        refine ⟨max k l, Finset.insert_subset ?_ ?_⟩
        · exact hS.mono (le_max_right k l) hl
        · exact hk.trans (hS.mono (le_max_left k l))
  obtain ⟨k, hk⟩ := hfin (primesLE N)
  filter_upwards [eventually_ge_atTop k] with m hm
  exact hk.trans (hS.mono hm)

/-- **Divergence along every exhaustion.** -/
theorem PrimeExhaustion.tendsto_norm_literalEulerHalfDensityOperatorOn
    {S : ℕ → Finset Nat.Primes} (hS : PrimeExhaustion S) :
    Tendsto (fun k => ‖literalEulerHalfDensityOperatorOn (S k)‖) atTop atTop := by
  simp only [norm_literalEulerHalfDensityOperatorOn]
  rw [Filter.tendsto_atTop]
  intro b
  obtain ⟨N, hN⟩ := (tendsto_literalEulerHalfDensityBudget_atTop.eventually
    (eventually_ge_atTop b)).exists
  filter_upwards [hS.eventually_primesLE_subset N] with k hk
  calc
    b ≤ literalEulerHalfDensityBudget N := hN
    _ = literalEulerHalfDensityBudgetOn (primesLE N) :=
      (literalEulerHalfDensityBudgetOn_primesLE N).symm
    _ ≤ literalEulerHalfDensityBudgetOn (S k) := literalEulerHalfDensityBudgetOn_mono hk

theorem PrimeExhaustion.not_uniformly_bounded {S : ℕ → Finset Nat.Primes}
    (hS : PrimeExhaustion S) :
    ¬ ∃ C : ℝ, ∀ k : ℕ, ‖literalEulerHalfDensityOperatorOn (S k)‖ ≤ C := by
  rintro ⟨C, hC⟩
  obtain ⟨k, hk⟩ :=
    (hS.tendsto_norm_literalEulerHalfDensityOperatorOn.eventually (eventually_gt_atTop C)).exists
  exact (not_lt_of_ge (hC k)) hk

/-- **Strong completion no-go along every exhaustion.** -/
theorem PrimeExhaustion.no_strong_bounded_completion {S : ℕ → Finset Nat.Primes}
    (hS : PrimeExhaustion S) :
    ¬ ∃ T : Lp ℂ 2 (volume : Measure ℝ) →L[ℂ] Lp ℂ 2 (volume : Measure ℝ),
      ∀ f, Tendsto (fun k => literalEulerHalfDensityOperatorOn (S k) f) atTop (𝓝 (T f)) := by
  rintro ⟨T, hT⟩
  have hpoint : ∀ f : Lp ℂ 2 (volume : Measure ℝ),
      ∃ C : ℝ, ∀ k, ‖literalEulerHalfDensityOperatorOn (S k) f‖ ≤ C := by
    intro f
    obtain ⟨C, hC⟩ := (hT f).norm.bddAbove_range
    exact ⟨C, fun k => hC ⟨k, rfl⟩⟩
  obtain ⟨C, hC⟩ := banach_steinhaus hpoint
  exact hS.not_uniformly_bounded ⟨C, hC⟩

/-- **Weak completion no-go along every exhaustion.** -/
theorem PrimeExhaustion.no_weak_bounded_completion {S : ℕ → Finset Nat.Primes}
    (hS : PrimeExhaustion S) :
    ¬ ∃ T : Lp ℂ 2 (volume : Measure ℝ) →L[ℂ] Lp ℂ 2 (volume : Measure ℝ),
      ∀ f g, Tendsto (fun k => inner ℂ (literalEulerHalfDensityOperatorOn (S k) f) g) atTop
        (𝓝 (inner ℂ (T f) g)) := by
  rintro ⟨T, hT⟩
  have hpoint : ∀ f : Lp ℂ 2 (volume : Measure ℝ),
      ∃ C : ℝ, ∀ k, ‖literalEulerHalfDensityOperatorOn (S k) f‖ ≤ C := by
    intro f
    have hfunctional : ∀ g : Lp ℂ 2 (volume : Measure ℝ),
        ∃ C : ℝ, ∀ k,
          ‖innerSL ℂ (literalEulerHalfDensityOperatorOn (S k) f) g‖ ≤ C := by
      intro g
      obtain ⟨C, hC⟩ := (hT f g).norm.bddAbove_range
      exact ⟨C, fun k => by simpa [innerSL_apply_apply] using hC ⟨k, rfl⟩⟩
    obtain ⟨C, hC⟩ := banach_steinhaus hfunctional
    exact ⟨C, fun k => by simpa [innerSL_apply_norm] using hC k⟩
  obtain ⟨C, hC⟩ := banach_steinhaus hpoint
  exact hS.not_uniformly_bounded ⟨C, hC⟩

end GaloisForLFunctions.RHTower
