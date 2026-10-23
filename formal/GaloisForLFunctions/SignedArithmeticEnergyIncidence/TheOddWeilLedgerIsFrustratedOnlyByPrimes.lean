import GaloisForLFunctions.SignedArithmeticEnergyIncidence.OddFoldingIsTheSourceOfFrustration
import GaloisForLFunctions.RHTower.ArchimedeanWeilKernelSign

/-!
# The odd Weil ledger is frustrated only by primes

In the autocorrelation variable the archimedean and polar parts of the Weil functional combine
into the weight `K(u) = 2e^{−u/2}/(1 − e^{−2u}) − 4 cosh(u/2)`
(`RHTower.ArchimedeanKernel.weilKernel`), and the primes contribute the atoms `Λ(n) n^{−1/2}` at
`u = log n` (`primeKernel`).  Sample the ledger with translation kernel
`w = α K(|u|) + β · prime(u)`, `α, β ≥ 0` (`weilLedgerKernel`), at mirror points `±p_x`, `p_x > 0`.

`K` changes sign once, so the unfolded ledger already has anti-aligned overlaps.  But `K` is
nonincreasing on `(0, ∞)` (`weilKernel_antitone`): its decreasing archimedean part and its
increasing polar part push the same way.  Odd folding of a nonincreasing kernel is aligned
(`OddFoldingIsTheSourceOfFrustration`), so

* **an anti-aligned odd overlap needs a prime sum** (`oddFold_pos_imp_primeSum`): if the folded
  overlap of `x, y` is positive then `e^{p_x + p_y}` is a prime power;
* **every frustrated cycle passes through a prime sum** (`frustrated_walk_has_primeSum`): a closed
  walk of the odd Weil ledger with holonomy `≠ 1` has two consecutive points whose positions sum to
  the logarithm of a prime power;
* **sampling free of prime sums is lossless** (`oddWeilLedger_lossless_of_no_primeSum`): if no two
  sample positions sum to a prime-power logarithm, positivity of the odd Weil ledger is local
  payment of its fold.

The prime triangle `log 2, log 3, log 5` of `OddFoldingIsTheSourceOfFrustration` shows that the
primes do frustrate it.
-/

open Finset ArithmeticFunction

namespace GaloisForLFunctions.SignedArithmeticEnergyIncidence

noncomputable section
set_option autoImplicit false

/-- **The archimedean–polar Weil weight is nonincreasing on `(0, ∞)`.** -/
theorem weilKernel_antitone {u u' : ℝ} (hu : 0 < u) (huu : u ≤ u') :
    RHTower.ArchimedeanKernel.weilKernel u' ≤ RHTower.ArchimedeanKernel.weilKernel u := by
  unfold RHTower.ArchimedeanKernel.weilKernel
  have d1 := RHTower.ArchimedeanKernel.one_sub_exp_neg_two_mul_pos hu
  have d2 : 1 - Real.exp (-2 * u) ≤ 1 - Real.exp (-2 * u') := by
    have := Real.exp_le_exp.2 (by linarith : -2 * u' ≤ -2 * u); linarith
  have n1 : Real.exp (-u' / 2) ≤ Real.exp (-u / 2) := Real.exp_le_exp.2 (by linarith)
  have hfrac : 2 * Real.exp (-u' / 2) / (1 - Real.exp (-2 * u')) ≤
      2 * Real.exp (-u / 2) / (1 - Real.exp (-2 * u)) :=
    div_le_div₀ (by positivity) (by linarith) d1 d2
  have hcosh : Real.cosh (u / 2) ≤ Real.cosh (u' / 2) := by
    rw [Real.cosh_le_cosh, abs_of_pos (by linarith), abs_of_pos (by linarith)]
    linarith
  linarith

/-- The sampled Weil translation kernel: archimedean–polar weight `α K(|u|)` plus prime atoms
`β Λ(n) n^{−1/2}` at `|u| = log n`. -/
def weilLedgerKernel (α β : ℝ) (u : ℝ) : ℝ :=
  α * RHTower.ArchimedeanKernel.weilKernel |u| + β * primeKernel u

theorem weilLedgerKernel_neg (α β u : ℝ) : weilLedgerKernel α β (-u) = weilLedgerKernel α β u := by
  simp only [weilLedgerKernel, abs_neg, primeKernel_neg]

/-- A positive prime kernel sits at the logarithm of a prime power. -/
theorem exists_of_primeKernel_pos {u : ℝ} (h : 0 < primeKernel u) :
    ∃ n : ℕ, Real.exp |u| = n ∧ 0 < Λ n := by
  by_contra hno
  push Not at hno
  have : primeKernel u = 0 := by
    unfold primeKernel
    refine (tsum_congr fun n => ?_).trans tsum_zero
    split_ifs with hn
    · rw [le_antisymm (hno n hn) vonMangoldt_nonneg, zero_div]
    · rfl
  linarith

section Ledger

variable {ι : Type*} [DecidableEq ι]

/-- **An anti-aligned odd overlap needs a prime sum.** -/
theorem oddFold_pos_imp_primeSum {p : ι → ℝ} (hp : ∀ x, 0 < p x) (hinj : Function.Injective p)
    {α β : ℝ} (hα : 0 ≤ α) (hβ : 0 ≤ β) {b : ι → ℝ} {x y : ι} (hxy : x ≠ y)
    (h : 0 < oddFold p (weilLedgerKernel α β) b x y) :
    ∃ n : ℕ, Real.exp (p x + p y) = n ∧ 0 < Λ n := by
  rw [oddFold_offDiag hxy] at h
  unfold weilLedgerKernel at h
  have hx := hp x
  have hy := hp y
  have hd : 0 < |p x - p y| := abs_pos.2 (sub_ne_zero.2 fun e => hxy (hinj e))
  have hs : |p x + p y| = p x + p y := abs_of_pos (by linarith)
  have hds : |p x - p y| ≤ |p x + p y| := by
    rw [hs]; exact abs_le.2 ⟨by linarith, by linarith⟩
  -- the archimedean–polar part folds to an aligned overlap
  have hK := weilKernel_antitone hd hds
  have hKα := mul_le_mul_of_nonneg_left hK hα
  have hprime : primeKernel (p x - p y) < primeKernel (p x + p y) := by
    by_contra hle
    push Not at hle
    nlinarith [mul_le_mul_of_nonneg_left hle hβ]
  obtain ⟨n, hn, hΛ⟩ := exists_of_primeKernel_pos
    (lt_of_le_of_lt (primeKernel_nonneg _) hprime)
  exact ⟨n, by rw [← hs]; exact hn, hΛ⟩

omit [DecidableEq ι] in
/-- A closed walk whose edges are all aligned has holonomy `+1`. -/
theorem walkHolonomy_eq_one_of_edges {c : ι → ι → ℝ} {u : ι} {l : List ι}
    (hl : IsWalkFrom c u l)
    (hz : ∀ i < l.length, c (walkVertex u l i) (walkVertex u l (i + 1)) ≤ 0) :
    walkHolonomy c u l = 1 := by
  rw [walkHolonomy_eq_prod]
  refine prod_eq_one fun i hi => ?_
  have hi' := mem_range.1 hi
  have hne := (isWalkFrom_vertex u l hl i hi').2
  have hneg := lt_of_le_of_ne (hz i hi') hne
  rw [edgeSign, if_neg hne, abs_of_neg hneg, div_neg, neg_neg, div_self hne]

/-- **Every frustrated cycle of the odd Weil ledger passes through a prime sum.** -/
theorem frustrated_walk_has_primeSum {p : ι → ℝ} (hp : ∀ x, 0 < p x)
    (hinj : Function.Injective p) {α β : ℝ} (hα : 0 ≤ α) (hβ : 0 ≤ β) {b : ι → ℝ} {u : ι}
    {l : List ι} (hl : IsWalkFrom (oddFold p (weilLedgerKernel α β) b) u l)
    (hhol : walkHolonomy (oddFold p (weilLedgerKernel α β) b) u l ≠ 1) :
    ∃ i < l.length, ∃ n : ℕ,
      Real.exp (p (walkVertex u l i) + p (walkVertex u l (i + 1))) = n ∧ 0 < Λ n := by
  by_contra hno
  push Not at hno
  refine hhol (walkHolonomy_eq_one_of_edges hl fun i hi => ?_)
  by_contra hpos
  push Not at hpos
  obtain ⟨n, hn, hΛ⟩ := oddFold_pos_imp_primeSum hp hinj hα hβ
    (isWalkFrom_vertex u l hl i hi).1 hpos
  exact absurd hΛ (not_lt.2 (hno i hi n hn))

/-- **Sampling free of prime sums is lossless**: if no two sample positions sum to the logarithm
of a prime power, positivity of the odd Weil ledger is local payment of its fold. -/
theorem oddWeilLedger_lossless_of_no_primeSum [Fintype ι] {p : ι → ℝ} (hp : ∀ x, 0 < p x)
    (hinj : Function.Injective p) {α β : ℝ} (hα : 0 ≤ α) (hβ : 0 ≤ β) {b : ι → ℝ}
    (hns : ∀ x y, x ≠ y → ∀ n : ℕ, Real.exp (p x + p y) = n → Λ n = 0) :
    (∀ f : ι → ℝ, 0 ≤ incidenceEnergy (mirrorCoupling p (weilLedgerKernel α β) b)
        (fun X => sideSign X.1 * f X.2)) ↔
      LocallyPayable (oddFold p (weilLedgerKernel α β) b) := by
  have hal : HasNonpositiveOverlaps (oddFold p (weilLedgerKernel α β) b) := by
    intro x y hxy
    by_contra hpos
    push Not at hpos
    obtain ⟨n, hn, hΛ⟩ := oddFold_pos_imp_primeSum hp hinj hα hβ hxy hpos
    rw [hns x y hxy n hn] at hΛ
    exact lt_irrefl 0 hΛ
  rw [← nonneg_iff_locallyPayable_of_isBalanced (oddFold_isSymmetric (weilLedgerKernel_neg α β))
    (isBalanced_of_aligned hal)]
  simp only [incidenceEnergy_mirror_odd (weilLedgerKernel_neg α β)]
  exact forall_congr' fun f => by constructor <;> intro h <;> linarith

end Ledger

end

end GaloisForLFunctions.SignedArithmeticEnergyIncidence
