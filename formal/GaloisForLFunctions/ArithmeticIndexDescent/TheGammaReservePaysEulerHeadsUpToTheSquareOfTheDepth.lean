import GaloisForLFunctions.ArithmeticIndexDescent.FiniteEulerMixedFormsHaveUniformFiniteIndex
import GaloisForLFunctions.RHTower.PrimeMassLowerBound
import Mathlib.NumberTheory.SumPrimeReciprocals

/-!
# The Gamma reserve pays Euler heads up to the square of the depth

Gamma minus the complete mixed Euler source of a finite prime set `P` has finite negative index
because a detail cutoff at depth `A` pays the source tail at the rate
`cost(P)/cellGammaWeight(A)`, with `cost(P) = Σ_{p∈P} 4 log p/(√p − 1)` and
`log A ≤ cellGammaWeight A ≤ log A + 1`. This file makes the dependence on `P` explicit.

* **Depth law** (`finiteEulerGamma_negative_dimension_le`): if `cost(P) ≤ log A`, every negative
  subspace has dimension at most `A`; in particular at most `⌈exp cost(P)⌉`
  (`finiteEulerGamma_negative_dimension_le_exp`).
* **Square-root cost of a head** (`finiteEulerMixedGammaCost_eulerHead_le`): the head of all
  primes `p ≤ Y` costs at most `32 √Y log Y`. So depth `A` pays the heads with `32 √Y log Y ≤ log A`:
  the reach of the Gamma reserve is `Y ≈ (log A)²` up to logarithms, and the head `p ≤ (log N)^a`
  has negative index at most `exp(C (log N)^{a/2} log log N)`.
* **No depth pays the whole layer** (`not_summable_primeEulerMixedWeightTotal`,
  `exists_eulerHead_cost_gt`): the Euler costs of the primes are not summable, so for every depth
  some finite head exceeds the Gamma capacity of that depth. A uniform finite index for the whole
  first prime layer cannot come from coefficient-wise Gamma payment: the tail beyond the reach
  must be paid by cancellation among the primes, i.e. by the square-root count itself.
-/

noncomputable section

open MeasureTheory Finset Filter
open RHTower

namespace GaloisForLFunctions.ArithmeticIndexDescent

open ArithmeticCastelnuovoSeveri.LogCells BiarithmeticGaugeGeometry HTGeometry

/-! ### The depth law -/

/-- **Payment at depth `A`.** A finite Euler head of cost at most `δ log A` is paid by the Gamma
energy with constant `δ` once the details below `A` vanish. -/
theorem abs_finiteEulerMixed_tail_le_of_cost (P : Finset Nat.Primes) {A : ℕ} (hA : 1 ≤ A) {δ : ℝ}
    (hδ : 0 ≤ δ) (hcost : finiteEulerMixedGammaCost P ≤ δ * Real.log A) (d q : ℕ → ℝ) (X : ℕ) :
    |finiteEulerMixedSource P (fun a => if A ≤ a then d a else 0) q X| ≤
      δ * levyEnergy (completePairProfile q d X) := by
  have hE := levyEnergy_nonneg_bv (completePairProfile_bv q d X) (completePairProfile_compact q d X)
  have hw := cellGammaWeight_pos hA
  have hcoef : finiteEulerMixedGammaCost P / cellGammaWeight A ≤ δ := by
    rw [div_le_iff₀ hw]
    exact hcost.trans (mul_le_mul_of_nonneg_left (log_le_cellGammaWeight hA) hδ)
  calc _ ≤ _ := abs_finiteEulerMixed_tail_le_gamma P d q hA X
    _ = (finiteEulerMixedGammaCost P / cellGammaWeight A) * levyEnergy (completePairProfile q d X) := by
        ring
    _ ≤ _ := mul_le_mul_of_nonneg_right hcoef hE

private def headReadout {n : ℕ} (d : Fin n → ℕ → ℝ) (A : ℕ) : (Fin n → ℝ) →ₗ[ℝ] (Fin A → ℝ) where
  toFun x a := ∑ i, x i * d i a
  map_add' x y := by
    funext a
    simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib]
  map_smul' c x := by
    funext a
    simp only [Pi.smul_apply, smul_eq_mul, mul_assoc, Finset.mul_sum]
    rfl

/-- **The depth law.** If `cost(P) ≤ log A`, every negative subspace of Gamma minus the complete
mixed Euler source of `P` has dimension at most `A`, at every horizon. -/
theorem finiteEulerGamma_negative_dimension_le (P : Finset Nat.Primes) {A : ℕ} (hA : 1 ≤ A)
    (hcost : finiteEulerMixedGammaCost P ≤ Real.log A) {n : ℕ} (q d : Fin n → ℕ → ℝ) (X : ℕ)
    (W : Submodule ℝ (Fin n → ℝ))
    (hW : ∀ x ∈ W, x ≠ 0 → finiteEulerGammaProfileForm P q d X x < 0) :
    Module.finrank ℝ W ≤ A := by
  let T := headReadout d A
  have hnonneg (x : Fin n → ℝ) (hx : T x = 0) : 0 ≤ finiteEulerGammaProfileForm P q d X x := by
    have hz (a : ℕ) (ha : a < A) : (∑ i, x i * d i a) = 0 := congrFun hx (⟨a, ha⟩ : Fin A)
    have htail : (fun a => if A ≤ a then ∑ i, x i * d i a else 0) =
        (fun a => ∑ i, x i * d i a) := by
      funext a
      by_cases ha : A ≤ a
      · exact if_pos ha
      · rw [if_neg ha, hz a (by omega)]
    have hp := abs_finiteEulerMixed_tail_le_of_cost P hA zero_le_one (by rw [one_mul]; exact hcost)
      (fun a => ∑ i, x i * d i a) (fun a => ∑ i, x i * q i a) X
    rw [htail, one_mul] at hp
    exact sub_nonneg.mpr ((le_abs_self _).trans hp)
  have hker : LinearMap.ker (T.domRestrict W) = ⊥ := by
    rw [Submodule.eq_bot_iff]
    intro x hx
    rw [LinearMap.mem_ker, LinearMap.domRestrict_apply] at hx
    by_contra hx0
    have hv : (x : Fin n → ℝ) ≠ 0 := fun h0 => hx0 (Subtype.ext h0)
    exact (not_lt_of_ge (hnonneg x hx)) (hW x x.property hv)
  have hd := LinearMap.finrank_le_finrank_of_injective (LinearMap.ker_eq_bot.mp hker)
  simpa only [Module.finrank_fintype_fun_eq_card, Fintype.card_fin] using hd

/-- Explicit form of the depth law: the negative index is at most `⌈exp cost(P)⌉`. -/
theorem finiteEulerGamma_negative_dimension_le_exp (P : Finset Nat.Primes) {n : ℕ}
    (q d : Fin n → ℕ → ℝ) (X : ℕ) (W : Submodule ℝ (Fin n → ℝ))
    (hW : ∀ x ∈ W, x ≠ 0 → finiteEulerGammaProfileForm P q d X x < 0) :
    Module.finrank ℝ W ≤ ⌈Real.exp (finiteEulerMixedGammaCost P)⌉₊ := by
  set A := ⌈Real.exp (finiteEulerMixedGammaCost P)⌉₊
  have hA0 : (0 : ℝ) < A := (Real.exp_pos _).trans_le (Nat.le_ceil _)
  have hA : 1 ≤ A := Nat.one_le_iff_ne_zero.mpr (Nat.cast_ne_zero.mp hA0.ne')
  have hcost : finiteEulerMixedGammaCost P ≤ Real.log A := by
    rw [Real.le_log_iff_exp_le hA0]
    exact Nat.le_ceil _
  exact finiteEulerGamma_negative_dimension_le P hA hcost q d X W hW

/-! ### The cost of a head -/

/-- The Euler head: all primes up to `Y`. -/
def eulerHead (Y : ℕ) : Finset Nat.Primes :=
  (Finset.range (Y + 1)).subtype Nat.Prime

theorem mem_eulerHead {Y : ℕ} {p : Nat.Primes} : p ∈ eulerHead Y ↔ (p : ℕ) ≤ Y := by
  change (⟨(p : ℕ), p.property⟩ : Subtype Nat.Prime) ∈ (Finset.range (Y + 1)).subtype Nat.Prime ↔ _
  rw [Finset.mem_subtype, Finset.mem_range]
  omega

/-- Each prime's Euler cost is at most `16 log p/√p`. -/
theorem two_mul_primeEulerMixedWeightTotal_le (p : Nat.Primes) :
    2 * primeEulerMixedWeightTotal p ≤ 16 * Real.log (p : ℝ) / Real.sqrt (p : ℝ) := by
  have hp2 : (2 : ℝ) ≤ (p : ℕ) := by exact_mod_cast p.property.two_le
  have hs : (4 / 3 : ℝ) ≤ Real.sqrt (p : ℝ) := by
    rw [Real.le_sqrt (by norm_num) (by linarith)]; nlinarith
  have hs0 : 0 < Real.sqrt (p : ℝ) := by linarith
  have hlog : 0 ≤ Real.log (p : ℝ) := Real.log_nonneg (by linarith)
  have hden : Real.sqrt (p : ℝ) / 4 ≤ Real.sqrt (p : ℝ) - 1 := by linarith
  unfold primeEulerMixedWeightTotal
  rw [mul_div_assoc', div_le_div_iff₀ (by linarith) hs0]
  nlinarith [mul_le_mul_of_nonneg_left hden hlog]

/-- **The square-root cost of a head.** The primes up to `Y` cost at most `32 √Y log Y`. -/
theorem finiteEulerMixedGammaCost_eulerHead_le (Y : ℕ) :
    finiteEulerMixedGammaCost (eulerHead Y) ≤ 32 * Real.sqrt Y * Real.log Y := by
  rcases Nat.eq_zero_or_pos Y with rfl | hY
  · have : eulerHead 0 = ∅ := by
      ext p; simp only [mem_eulerHead, Finset.notMem_empty, iff_false, Nat.le_zero]
      exact p.property.ne_zero
    simp [this, finiteEulerMixedGammaCost]
  have hlogY : 0 ≤ Real.log (Y : ℝ) := Real.log_natCast_nonneg Y
  have hterm : ∀ p ∈ eulerHead Y, 2 * primeEulerMixedWeightTotal p ≤
      16 * Real.log Y * (1 / Real.sqrt (p : ℕ)) := by
    intro p hp
    refine (two_mul_primeEulerMixedWeightTotal_le p).trans ?_
    have hpY : ((p : ℕ) : ℝ) ≤ Y := by exact_mod_cast (mem_eulerHead.mp hp)
    have hp0 : (0 : ℝ) < (p : ℕ) := by exact_mod_cast p.property.pos
    have hl : Real.log ((p : ℕ) : ℝ) ≤ Real.log Y := Real.log_le_log hp0 hpY
    rw [mul_one_div, div_le_div_iff_of_pos_right (Real.sqrt_pos.mpr hp0)]
    linarith
  have hsum : ∑ p ∈ eulerHead Y, (1 / Real.sqrt ((p : ℕ) : ℝ)) ≤
      ∑ n ∈ Finset.Icc 1 Y, (1 : ℝ) / Real.sqrt n := by
    rw [← Finset.sum_image (f := fun n : ℕ => (1 : ℝ) / Real.sqrt n)
      (g := fun p : Nat.Primes => (p : ℕ)) (fun a _ b _ h => Subtype.ext h)]
    refine Finset.sum_le_sum_of_subset_of_nonneg (fun n hn => ?_) fun n _ _ => by positivity
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hn
    exact Finset.mem_Icc.mpr ⟨p.property.one_lt.le, mem_eulerHead.mp hp⟩
  calc finiteEulerMixedGammaCost (eulerHead Y)
      ≤ ∑ p ∈ eulerHead Y, 16 * Real.log Y * (1 / Real.sqrt (p : ℕ)) := sum_le_sum hterm
    _ = 16 * Real.log Y * ∑ p ∈ eulerHead Y, (1 / Real.sqrt ((p : ℕ) : ℝ)) := by rw [mul_sum]
    _ ≤ 16 * Real.log Y * (2 * Real.sqrt Y) :=
        mul_le_mul_of_nonneg_left (hsum.trans (RHTower.sum_one_div_sqrt_le Y)) (by positivity)
    _ = _ := by ring

/-- **Reach of the Gamma reserve.** Depth `A` pays the head of the primes up to `Y` as soon as
`32 √Y log Y ≤ log A`, with negative index at most `A`. -/
theorem eulerHead_negative_dimension_le {Y A : ℕ} (hA : 1 ≤ A)
    (hreach : 32 * Real.sqrt Y * Real.log Y ≤ Real.log A) {n : ℕ} (q d : Fin n → ℕ → ℝ) (X : ℕ)
    (W : Submodule ℝ (Fin n → ℝ))
    (hW : ∀ x ∈ W, x ≠ 0 → finiteEulerGammaProfileForm (eulerHead Y) q d X x < 0) :
    Module.finrank ℝ W ≤ A :=
  finiteEulerGamma_negative_dimension_le (eulerHead Y) hA
    ((finiteEulerMixedGammaCost_eulerHead_le Y).trans hreach) q d X W hW

/-! ### No finite depth pays the whole first layer -/

/-- **The Euler costs of the primes are not summable.** Each is at least `1/p`. -/
theorem not_summable_primeEulerMixedWeightTotal :
    ¬ Summable fun p : Nat.Primes => primeEulerMixedWeightTotal p := by
  intro hs
  apply Nat.Primes.not_summable_one_div
  refine hs.of_nonneg_of_le (fun p => by positivity) fun p => ?_
  have hp2 : (2 : ℝ) ≤ (p : ℕ) := by exact_mod_cast p.property.two_le
  have hs1 : 1 < Real.sqrt (p : ℝ) := by
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]; exact Real.sqrt_lt_sqrt zero_le_one (by linarith)
  have hsp : Real.sqrt (p : ℝ) - 1 ≤ (p : ℝ) := by
    have := Real.sq_sqrt (show (0 : ℝ) ≤ (p : ℕ) by linarith)
    nlinarith
  have hlog : (1 / 2 : ℝ) ≤ Real.log (p : ℝ) := by
    have := Real.log_two_gt_d9
    have := Real.log_le_log (by norm_num) hp2
    linarith
  unfold primeEulerMixedWeightTotal
  rw [div_le_div_iff₀ (by linarith) (by linarith)]
  nlinarith

/-- **No depth pays every head.** For every depth `A ≥ 1` some Euler head costs more than the Gamma
capacity `cellGammaWeight A`, so coefficient-wise Gamma payment of the whole first prime layer fails
at every finite depth. -/
theorem exists_eulerHead_cost_gt (A : ℕ) :
    ∃ Y : ℕ, cellGammaWeight A < finiteEulerMixedGammaCost (eulerHead Y) := by
  by_contra h
  push Not at h
  apply not_summable_primeEulerMixedWeightTotal
  refine summable_of_sum_le (c := cellGammaWeight A / 2)
    (fun p => primeEulerMixedWeightTotal_nonneg p) fun s => ?_
  set Y := s.sup (fun p : Nat.Primes => (p : ℕ))
  have hsub : s ⊆ eulerHead Y := fun p hp =>
    mem_eulerHead.mpr (Finset.le_sup (f := fun p : Nat.Primes => (p : ℕ)) hp)
  have h1 : ∑ p ∈ s, primeEulerMixedWeightTotal p ≤
      ∑ p ∈ eulerHead Y, primeEulerMixedWeightTotal p :=
    sum_le_sum_of_subset_of_nonneg hsub fun p _ _ => primeEulerMixedWeightTotal_nonneg p
  have h2 : finiteEulerMixedGammaCost (eulerHead Y) =
      2 * ∑ p ∈ eulerHead Y, primeEulerMixedWeightTotal p := by
    rw [finiteEulerMixedGammaCost, mul_sum]
  have := h Y
  linarith

end GaloisForLFunctions.ArithmeticIndexDescent
