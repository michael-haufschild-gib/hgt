import GaloisForLFunctions.RHTower.Sieve.NoncoprimeDensity
import GaloisForLFunctions.RHTower.Sieve.MRInterface

/-!
# The coprime sign classes keep a positive density

Deleting the noncoprime pairs from a sign class costs at most `B(x,h)`, so `(7)` and `(12)` give

    R_ε(x,h) / (h√x log 2)  ≥  D²/2 - D²A - ε   eventually,

and `A < 1/2` makes the right-hand side positive.  That is the card's `(3)`.
-/

namespace RHTower.Sieve

open Finset Filter Topology
open scoped ArithmeticFunction.Moebius

/-- The coprime pairs of a given product sign. -/
noncomputable def coprimeSignClass (x h : ℝ) (s : ℤ) : Finset (ℕ × ℕ) :=
  (balancedPairs x h).filter (fun q => μ q.1 * μ q.2 = s ∧ Nat.Coprime q.1 q.2)

/-- The size of a coprime sign class. -/
noncomputable def coprimeSignClassCount (x h : ℝ) (s : ℤ) : ℝ :=
  ((coprimeSignClass x h s).card : ℝ)

/-- A pair of product sign `±1` has squarefree weight one. -/
theorem weight_eq_one_of_sign {a b : ℕ} {s : ℤ} (hs : s = 1 ∨ s = -1)
    (hab : μ a * μ b = s) :
    ((μ a : ℤ) : ℝ) ^ (2 : ℕ) * ((μ b : ℤ) : ℝ) ^ (2 : ℕ) = 1 := by
  have hsq : ((μ a : ℤ) : ℝ) ^ (2 : ℕ) * ((μ b : ℤ) : ℝ) ^ (2 : ℕ) = ((μ a * μ b : ℤ) : ℝ) ^ (2 : ℕ) := by
    push_cast; ring
  rw [hsq, hab]
  rcases hs with rfl | rfl <;> norm_num

/-- **Deleting the noncoprime pairs costs at most `B`.** -/
theorem signClassCount_sub_le {x h : ℝ} {s : ℤ} (hs : s = 1 ∨ s = -1) :
    signClassCount x h s - noncoprimePairCount x h ≤ coprimeSignClassCount x h s := by
  classical
  set w : ℕ × ℕ → ℝ := fun q => ((μ q.1 : ℤ) : ℝ) ^ (2 : ℕ) * ((μ q.2 : ℤ) : ℝ) ^ (2 : ℕ) with hw
  have hw0 : ∀ q, 0 ≤ w q := by
    intro q; rw [hw]; positivity
  -- the sign class splits into the coprime part and the rest
  have hsplit := Finset.card_filter_add_card_filter_not
    (s := signClass x h s) (p := fun q => Nat.Coprime q.1 q.2)
  have hcop : (signClass x h s).filter (fun q => Nat.Coprime q.1 q.2) = coprimeSignClass x h s := by
    rw [signClass, coprimeSignClass, Finset.filter_filter]
  have hbad : (signClass x h s).filter (fun q => ¬ Nat.Coprime q.1 q.2)
      ⊆ (balancedPairs x h).filter (fun q => ¬ Nat.Coprime q.1 q.2) := by
    intro q hq
    rw [Finset.mem_filter, signClass, Finset.mem_filter] at hq
    exact Finset.mem_filter.2 ⟨hq.1.1, hq.2⟩
  have hbadcount : (((signClass x h s).filter (fun q => ¬ Nat.Coprime q.1 q.2)).card : ℝ)
      ≤ noncoprimePairCount x h := by
    have hone : ∀ q ∈ (signClass x h s).filter (fun q => ¬ Nat.Coprime q.1 q.2), w q = 1 := by
      intro q hq
      rw [Finset.mem_filter, signClass, Finset.mem_filter] at hq
      exact weight_eq_one_of_sign hs hq.1.2
    calc (((signClass x h s).filter (fun q => ¬ Nat.Coprime q.1 q.2)).card : ℝ)
        = ∑ q ∈ (signClass x h s).filter (fun q => ¬ Nat.Coprime q.1 q.2), (1 : ℝ) := by
          rw [Finset.sum_const, nsmul_eq_mul, mul_one]
      _ = ∑ q ∈ (signClass x h s).filter (fun q => ¬ Nat.Coprime q.1 q.2), w q :=
          (Finset.sum_congr rfl hone).symm
      _ ≤ ∑ q ∈ (balancedPairs x h).filter (fun q => ¬ Nat.Coprime q.1 q.2), w q :=
          Finset.sum_le_sum_of_subset_of_nonneg hbad (fun q _ _ => hw0 q)
      _ = noncoprimePairCount x h := rfl
  rw [hcop] at hsplit
  have hcast : signClassCount x h s
      = coprimeSignClassCount x h s
        + (((signClass x h s).filter (fun q => ¬ Nat.Coprime q.1 q.2)).card : ℝ) := by
    rw [signClassCount, coprimeSignClassCount, ← hsplit]
    push_cast
    ring
  rw [hcast]
  linarith

/-- The squarefree density is positive. -/
theorem squarefreeDensity_pos : 0 < squarefreeDensity := by
  rw [squarefreeDensity_eq]
  have := Real.pi_pos
  positivity

/-- **Card equation (3).**  Both coprime sign classes keep a positive density. -/
theorem eventually_coprimeSignClass_ge {hh : ℝ → ℝ} {s : ℤ} (hs : s = 1 ∨ s = -1)
    (hgrow : Tendsto (fun x => hh x / Real.log (Real.log (3 * x))) atTop atTop)
    (hMRsign : Tendsto (fun x => signClassCount x (hh x) s
        / (hh x * Real.sqrt x * Real.log 2)) atTop (𝓝 (squarefreeDensity ^ (2 : ℕ) / 2)))
    (hMR : ∀ p : ℕ, p.Prime → MRBilinearAt (coprimeSquarefreeWeight p)
      (fun x => x / (p : ℝ) ^ (2 : ℕ)) (fun x => hh x / (p : ℝ)))
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ x in atTop,
      squarefreeDensity ^ (2 : ℕ) / 2 - squarefreeDensity ^ (2 : ℕ) * RHTower.coprimeSharedPrimeDensity - ε
        ≤ coprimeSignClassCount x (hh x) s / (hh x * Real.sqrt x * Real.log 2) := by
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hhtop : Tendsto hh atTop atTop := tendsto_of_growth hgrow
  have hsignev := hMRsign.eventually (eventually_gt_nhds
    (by linarith : squarefreeDensity ^ (2 : ℕ) / 2 - ε / 2 < squarefreeDensity ^ (2 : ℕ) / 2))
  have hbadev := eventually_noncoprime_le hgrow hMR (ε := ε / 2) (by linarith)
  filter_upwards [eventually_gt_atTop (0 : ℝ), hhtop.eventually_gt_atTop (0 : ℝ),
    hsignev, hbadev] with x hx0 hhx hsx hbx
  have hs0 : (0 : ℝ) < Real.sqrt x := Real.sqrt_pos.2 hx0
  have hden : (0 : ℝ) < hh x * Real.sqrt x * Real.log 2 := by positivity
  have hdel := signClassCount_sub_le (x := x) (h := hh x) hs
  have hdiv : (signClassCount x (hh x) s - noncoprimePairCount x (hh x))
      / (hh x * Real.sqrt x * Real.log 2)
      ≤ coprimeSignClassCount x (hh x) s / (hh x * Real.sqrt x * Real.log 2) := by
    gcongr
  rw [sub_div] at hdiv
  linarith

/-- **The margin is strictly positive.** -/
theorem coprime_margin_pos :
    0 < squarefreeDensity ^ (2 : ℕ) / 2
      - squarefreeDensity ^ (2 : ℕ) * RHTower.coprimeSharedPrimeDensity := by
  have hD := squarefreeDensity_pos
  have hA := RHTower.coprimeSharedPrimeDensity_lt_half
  have hsq : 0 < squarefreeDensity ^ (2 : ℕ) := by positivity
  have hfac : 0 < 1 / 2 - RHTower.coprimeSharedPrimeDensity := by linarith
  have hrw : squarefreeDensity ^ (2 : ℕ) / 2
      - squarefreeDensity ^ (2 : ℕ) * RHTower.coprimeSharedPrimeDensity
      = squarefreeDensity ^ (2 : ℕ) * (1 / 2 - RHTower.coprimeSharedPrimeDensity) := by ring
  rw [hrw]
  exact mul_pos hsq hfac

end RHTower.Sieve
