import GaloisForLFunctions.RHTower.JointAncestryTypicalCapLocal
import GaloisForLFunctions.RHTower.JointAncestryTypicalCapCount
import GaloisForLFunctions.RHTower.JointAncestryTypicalCapWindow
import GaloisForLFunctions.RHTower.CosineAvoidanceFiniteFrequencies

/-!
# Arithmetic of the typical-cap receiver: the aggregate at `r = 1` and its coefficients

At `r = 1` every Bernoulli factor is `2 g_p(k_p)` with
`g_p(x) = 1 + ½(ω^x A_p + ω^{−x} B_p)`, where `A_p = p^{−σ} p^{½−ρ}` and `B_p = p^{−σ} p^{ρ−½}`,
so `jasPhaseAggregate σ 1 N P k = 2^{|P|} Σ_ρ w_ρ ∏_p g_p(k_p)` (`jasPhaseAggregate_one_eq`).
This file records the norms `|A_p| = p^{−σ−(Re ρ−½)}`, `|B_p| = p^{−σ+(Re ρ−½)}`, the product
`A_p B_p = p^{−2σ}`, and the coherence bound `|p^z − X^z| ≤ 2 X^{Re z}|z| log C` for
`X < p ≤ CX`.
-/

open Complex Finset
open scoped ComplexConjugate

namespace RHTower

noncomputable section

/-- `A_p = p^{−(ρ + σ − ½)}`. -/
def typCapA (σ : ℝ) (q : XiZeroCopy) (p : Nat.Primes) : ℂ :=
  jasHoloA ((q.1 : ℂ) + (σ - 1 / 2 : ℝ)) p

/-- `B_p = p^{−(½ − ρ + σ)}`. -/
def typCapB (σ : ℝ) (q : XiZeroCopy) (p : Nat.Primes) : ℂ :=
  jasHoloB ((q.1 : ℂ) - (σ - 1 / 2 : ℝ)) p

/-- **The aggregate at `r = 1`.** -/
theorem jasPhaseAggregate_one_eq (σ : ℝ) (N : ℕ) (P : Finset Nat.Primes) (k : ↥P → Fin N) :
    jasPhaseAggregate σ 1 N P k = (2 : ℂ) ^ P.card *
      ∑' q : XiZeroCopy, lagWeight q *
        ∏ p : ↥P, phaseFactor N (1 / 2) (typCapA σ q p) (typCapB σ q p) (k p) := by
  unfold jasPhaseAggregate
  rw [← tsum_mul_left]
  refine tsum_congr fun q => ?_
  have hfac : ∀ p : ↥P, jasBernoulliFactor (jasHoloA ((q.1 : ℂ) + (σ - 1 / 2 : ℝ)) p)
      (jasHoloB ((q.1 : ℂ) - (σ - 1 / 2 : ℝ)) p) (((1 : ℝ) : ℂ) * unitRoot N ^ ((k p : Fin N) : ℕ)) =
      2 * phaseFactor N (1 / 2) (typCapA σ q p) (typCapB σ q p) (k p) := by
    intro p
    rw [jasBernoulliFactor_phase _ _ (zero_le_one) (k p)]
    unfold typCapA typCapB
    norm_num
  rw [Finset.prod_congr rfl fun p _ => hfac p, Finset.prod_mul_distrib, Finset.prod_const,
    Finset.card_univ, Fintype.card_coe, lagWeight]
  ring

theorem norm_capA (σ : ℝ) (q : XiZeroCopy) (p : Nat.Primes) :
    ‖typCapA σ q p‖ = Real.exp (-(σ + ((q.1 : ℂ).re - 1 / 2)) * Real.log p) := by
  unfold typCapA; rw [norm_jasHoloA, Complex.add_re, Complex.ofReal_re]; ring_nf

theorem norm_capB (σ : ℝ) (q : XiZeroCopy) (p : Nat.Primes) :
    ‖typCapB σ q p‖ = Real.exp (-(σ - ((q.1 : ℂ).re - 1 / 2)) * Real.log p) := by
  unfold typCapB; rw [norm_jasHoloB, Complex.sub_re, Complex.ofReal_re]; ring_nf

theorem capA_mul_capB (σ : ℝ) (q : XiZeroCopy) (p : Nat.Primes) :
    typCapA σ q p * typCapB σ q p = Complex.exp (-(2 * σ) * Real.log p) := by
  unfold typCapA typCapB jasHoloA jasHoloB
  rw [← Complex.exp_add]; congr 1; push_cast; ring

theorem capB_eq (σ : ℝ) (q : XiZeroCopy) (p : Nat.Primes) :
    typCapB σ q p = Complex.exp (-σ * Real.log p) *
      Complex.exp (((q.1 : ℂ) - 1 / 2) * Real.log p) := by
  unfold typCapB jasHoloB
  rw [← Complex.exp_add]; congr 1; push_cast; ring

theorem capA_eq (σ : ℝ) (q : XiZeroCopy) (p : Nat.Primes) :
    typCapA σ q p = Complex.exp (-σ * Real.log p) *
      Complex.exp ((1 / 2 - (q.1 : ℂ)) * Real.log p) := by
  unfold typCapA jasHoloA
  rw [← Complex.exp_add]; congr 1; push_cast; ring

/-- Both coefficients are at most `p^{Θ−σ}` when `|Re ρ − ½| ≤ Θ`. -/
theorem norm_capA_le {σ Θ : ℝ} {q : XiZeroCopy} (hq : |(q.1 : ℂ).re - 1 / 2| ≤ Θ)
    (p : Nat.Primes) : ‖typCapA σ q p‖ ≤ Real.exp ((Θ - σ) * Real.log p) := by
  rw [norm_capA]
  have hL := (Real.log_pos (by exact_mod_cast p.2.one_lt : (1 : ℝ) < p)).le
  refine Real.exp_le_exp.mpr ?_
  have := (abs_le.mp hq).1
  nlinarith

theorem norm_capB_le {σ Θ : ℝ} {q : XiZeroCopy} (hq : |(q.1 : ℂ).re - 1 / 2| ≤ Θ)
    (p : Nat.Primes) : ‖typCapB σ q p‖ ≤ Real.exp ((Θ - σ) * Real.log p) := by
  rw [norm_capB]
  have hL := (Real.log_pos (by exact_mod_cast p.2.one_lt : (1 : ℝ) < p)).le
  refine Real.exp_le_exp.mpr ?_
  have := (abs_le.mp hq).2
  nlinarith

/-- **Coherence.**  `|p^z − X^z| ≤ 2 X^{Re z} |z| log C` for `X < p ≤ CX` and `|z| log C ≤ 1`. -/
theorem norm_cexp_log_sub_le {p X C : ℝ} {z : ℂ} (hX : 0 < X) (hpX : X < p) (hpC : p ≤ C * X)
    (hz : ‖z‖ * Real.log C ≤ 1) :
    ‖Complex.exp (z * Real.log p) - Complex.exp (z * Real.log X)‖ ≤
      2 * Real.exp (z.re * Real.log X) * (‖z‖ * Real.log C) := by
  have hp0 : 0 < p := hX.trans hpX
  have hlog : Real.log p - Real.log X ≤ Real.log C := by
    rw [← Real.log_div hp0.ne' hX.ne']
    have hC : 0 < C := by
      by_contra h; push Not at h; nlinarith
    exact Real.log_le_log (div_pos hp0 hX) (by rw [div_le_iff₀ hX]; linarith)
  have hlog0 : 0 ≤ Real.log p - Real.log X := by
    have := Real.log_le_log hX hpX.le; linarith
  have hd : ‖z * Real.log p - z * Real.log X‖ = ‖z‖ * (Real.log p - Real.log X) := by
    rw [← mul_sub, norm_mul, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg hlog0]
  have hd1 : ‖z * Real.log p - z * Real.log X‖ ≤ ‖z‖ * Real.log C := by
    rw [hd]; exact mul_le_mul_of_nonneg_left hlog (norm_nonneg _)
  refine (norm_cexp_sub_cexp_le_two_mul (hd1.trans hz)).trans ?_
  have hre : (z * Real.log X).re = z.re * Real.log X := by simp
  rw [hre]
  have := Real.exp_pos (z.re * Real.log X)
  nlinarith

end

end RHTower
