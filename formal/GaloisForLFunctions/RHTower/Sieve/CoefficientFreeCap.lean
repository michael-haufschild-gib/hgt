import GaloisForLFunctions.RHTower.Sieve.CesaroDyadicTrivialCap
import GaloisForLFunctions.RHTower.DeciderBarrier

/-!
# Coefficient-free bounds cannot beat the constant sequence

Three architectures in this folder are capped at the trivial size, and by one argument rather than three:
the modulus-first vertical integral, any coefficient-free majorisation of the GHS sieve mean squares, and
the unconditional mean-square Cesàro chain.  In each case the bound's right-hand side does not mention the
coefficient sequence — either because it was majorised through `‖a_n‖ ≤ A log n`, or because it is built
from `‖a_n‖` alone — and the bound holds for *every* bounded completely multiplicative sequence.  Then
instantiating at the constant sequence `1`, whose functional value is the trivial size, bounds the
right-hand side from below.

The two laws below make that test mechanical.  To kill a route of this shape it suffices to exhibit
(i) its bound as a `∀ g` statement with a sequence-free right-hand side, and (ii) a lower bound for the
functional at the constant sequence.  Nothing about the analytic estimate enters, so no sharpening of it
can evade the conclusion.

The second law is the sharper form: a right-hand side depending on the sequence only through the moduli
cannot separate *any* unimodular completely multiplicative sequence from the constant one.  That is the
relevant comparison for the Liouville function, whose moduli are identically `1`.
-/

noncomputable section
namespace RHTower.Sieve

/-- **A coefficient-free bound is at least its value at the constant sequence.**  If `B` majorises `Φ g`
for every bounded completely multiplicative `g`, and `Φ` at the constant sequence is at least `L`, then
`L ≤ B`. -/
theorem le_of_coefficientFree_bound {Φ : (ℕ → ℂ) → ℝ} {B L : ℝ}
    (hB : ∀ g : ℕ → ℂ, g 1 = 1 → (∀ a b : ℕ, g (a * b) = g a * g b) → (∀ n : ℕ, ‖g n‖ ≤ 1) →
      Φ g ≤ B)
    (hL : L ≤ Φ (fun _ => (1 : ℂ))) : L ≤ B :=
  le_trans hL (hB (fun _ => (1 : ℂ)) rfl (fun a b => by norm_num) (fun n => by norm_num))

/-- **A modulus-only bound cannot separate a unimodular sequence from the constant one.**  If the
right-hand side is a function of the moduli alone, its value at any unimodular `f` equals its value at
the constant sequence, which is at least the trivial size. -/
theorem le_of_modulusOnly_bound {Φ : (ℕ → ℂ) → ℝ} {B : (ℕ → ℝ) → ℝ} {L : ℝ}
    (hB : ∀ g : ℕ → ℂ, g 1 = 1 → (∀ a b : ℕ, g (a * b) = g a * g b) → (∀ n : ℕ, ‖g n‖ ≤ 1) →
      Φ g ≤ B (fun n => ‖g n‖))
    (hL : L ≤ Φ (fun _ => (1 : ℂ))) {f : ℕ → ℂ} (hf : ∀ n : ℕ, ‖f n‖ = 1) :
    L ≤ B (fun n => ‖f n‖) := by
  have hmod : (fun n : ℕ => ‖f n‖) = (fun n : ℕ => ‖(1 : ℂ)‖) := by
    funext n
    rw [hf n, norm_one]
  rw [hmod]
  exact le_trans hL
    (hB (fun _ => (1 : ℂ)) rfl (fun a b => by norm_num) (fun n => by norm_num))

/-- **The unconditional Cesàro chain through the law.**  The instance that recovers
`trivial_le_cesaro_dyadic_bound` from the general test. -/
theorem trivial_le_cesaro_dyadic_bound_of_law {N : ℕ} (hN : 1 ≤ N) {σ T : ℝ} (hσ1 : 1 ≤ σ)
    (hσ2 : σ ≤ 2) (hT : 1 ≤ T) :
    ((N / 2 : ℕ) : ℝ) * Real.log 2
      ≤ (∑ n ∈ Finset.Icc 1 N, cesaroError σ T ((N : ℝ) / n))
        + (1 / (2 * Real.pi))
          * (8 * (N : ℝ) ^ σ * Real.sqrt (5 * Real.pi * Real.exp 1 * (1 + Real.log N))
            + 12 * (N : ℝ) ^ σ * Real.sqrt (5 * Real.pi)) := by
  refine le_of_coefficientFree_bound
    (Φ := fun g => ‖∑ n ∈ Finset.Icc 1 N,
      truncSeq g N n * ((Real.log ((N : ℝ) / n) : ℝ) : ℂ)‖) ?_ ?_
  · intro g _ _ hgbdd
    exact norm_sum_Icc_mul_log_div_le_cesaro_dyadic hgbdd hN hσ1 hσ2 hT (le_refl ((N : ℝ)))
  · have hcoeff : ∀ n ∈ Finset.Icc 1 N,
        truncSeq (fun _ => (1 : ℂ)) N n * ((Real.log ((N : ℝ) / n) : ℝ) : ℂ)
          = ((Real.log ((N : ℝ) / n) : ℝ) : ℂ) := by
      intro n hn
      rw [truncSeq, if_pos hn, one_mul]
    rw [Finset.sum_congr rfl hcoeff, ← Complex.ofReal_sum, Complex.norm_real, Real.norm_eq_abs]
    have hnn : (0 : ℝ) ≤ ∑ n ∈ Finset.Icc 1 N, Real.log ((N : ℝ) / n) := by
      refine Finset.sum_nonneg fun n hn => ?_
      rw [Finset.mem_Icc] at hn
      have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn.1
      have hnN : (n : ℝ) ≤ (N : ℝ) := by exact_mod_cast hn.2
      refine Real.log_nonneg ?_
      rw [le_div_iff₀ (by linarith : (0 : ℝ) < (n : ℝ))]
      linarith
    rw [abs_of_nonneg hnn]
    exact sum_Icc_log_div_ge

/-- **The caps are instances of the quantitative barrier.**  `DeciderBarrier.le_bound_of_invariant_collision`
is the abstract form: a majorant factoring through an invariant is at least the majorised quantity at both
members of a collided pair.  Here the invariant is the sequence of moduli, the collided pair is a
unimodular completely multiplicative sequence and the constant one, and the conclusion is that the bound
majorises both — so it cannot certify a gap.  Restating the modulus-only cap through the barrier shows the
two families of no-go in this corpus, for verdicts and for bounds, are one shape. -/
theorem max_le_of_modulusOnly_bound {Φ : (ℕ → ℂ) → ℝ} {B : (ℕ → ℝ) → ℝ}
    (hB : ∀ g : ℕ → ℂ, Φ g ≤ B (fun n => ‖g n‖)) {f : ℕ → ℂ} (hf : ∀ n : ℕ, ‖f n‖ = 1) :
    max (Φ f) (Φ (fun _ => (1 : ℂ))) ≤ B (fun n => ‖f n‖) := by
  have hcoll : (fun n : ℕ => ‖f n‖) = (fun n : ℕ => ‖(1 : ℂ)‖) := by
    funext n
    rw [hf n, norm_one]
  exact RHTower.le_bound_of_invariant_collision (fun g : ℕ → ℂ => fun n => ‖g n‖) B Φ hB hcoll

end RHTower.Sieve
end
