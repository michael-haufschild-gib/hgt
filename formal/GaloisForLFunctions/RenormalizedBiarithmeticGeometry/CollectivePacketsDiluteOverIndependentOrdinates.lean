import GaloisForLFunctions.HTGeometry.KroneckerWeylDensity
import GaloisForLFunctions.MultiplicativePositivityGeometry.ExactFejerBarrier

/-!
# Collective packets dilute over independent ordinates

A *positive packet* on a family of ordinates `ω_j` is a nonnegative almost-periodic polynomial
`P(t) = a_0 + Σ_j a_j cos(ω_j t) ≥ 0`: the constant `a_0` is the pole share it pays, the `a_j` are
what it buys at the ordinates. Coupling many ordinates in one packet is the collective
amortization proposed for clouds of off-line companions. Whether it amortizes depends only on the
arithmetic of the cloud.

* **Kronecker dilution** (`sum_abs_le_of_packet_nonneg`). If the ordinates are linearly independent
  over `ℚ`, then `Σ_j |a_j| ≤ a_0`: the whole cloud buys at most the pole share, so each of `K`
  ordinates gets `a_0/K` on average. The bound is sharp (`packet_nonneg_of_sum_abs_le`). Proof:
  Kronecker's theorem puts every `cos(ω_j t)` near `−sign(a_j)` at one time `t`.
* **Peak-to-mean** (`packet_peak_le_two_mul`): an independent packet never exceeds twice its pole
  share at `t = 0`.
* **Harmonic concentration** (`exists_harmonic_packet`). On the harmonic ordinates
  `γ, 2γ, …, Mγ` the Fejér packet `|Σ_{j ≤ M} e^{ijγt}|²` has pole share `M + 1` and buys
  `M(M + 1)`: `M` times the pole share.

So collective amortization exists only through arithmetic relations among the ordinates. A cloud
of companions with independent ordinates is worse than a single ordinate (MPG
`multiFrequency_purchase_le_two`); only commensurable clouds can be amortized.
-/

noncomputable section

open Finset

namespace GaloisForLFunctions.RenormalizedBiarithmeticGeometry

/-- `|cos x − cos y|` is bounded by the distance of the unit characters. -/
theorem abs_cos_sub_cos_le (x y : ℝ) :
    |Real.cos x - Real.cos y| ≤
      ‖Complex.exp ((x : ℝ) * Complex.I) - Complex.exp ((y : ℝ) * Complex.I)‖ := by
  have h := Complex.abs_re_le_norm
    (Complex.exp ((x : ℝ) * Complex.I) - Complex.exp ((y : ℝ) * Complex.I))
  rwa [Complex.sub_re, Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_re] at h

/-- **Kronecker dilution.** A nonnegative packet on `ℚ`-independent ordinates buys in total at
most its pole share: `Σ_j |a_j| ≤ a_0`. -/
theorem sum_abs_le_of_packet_nonneg {ι : Type*} [Fintype ι] [DecidableEq ι] {ω : ι → ℝ}
    (hind : LinearIndependent ℚ ω) (a₀ : ℝ) (a : ι → ℝ)
    (hP : ∀ t : ℝ, 0 ≤ a₀ + ∑ j, a j * Real.cos (ω j * t)) : ∑ j, |a j| ≤ a₀ := by
  set S := ∑ j, |a j|
  -- Target phases: `cos θ_j = −sign(a_j)`.
  set θ : ι → ℝ := fun j => if 0 ≤ a j then Real.pi else 0
  have hθ : ∀ j, a j * Real.cos (θ j) = -|a j| := fun j => by
    simp only [θ]
    split_ifs with h
    · rw [Real.cos_pi, abs_of_nonneg h]; ring
    · rw [Real.cos_zero, abs_of_neg (not_le.mp h)]; ring
  -- For every `ε > 0`, `0 ≤ a₀ − (1 − ε) S`.
  have hε : ∀ ε : ℝ, 0 < ε → (1 - ε) * S ≤ a₀ := by
    intro ε hεpos
    obtain ⟨t, ht⟩ := kronecker_approx hind θ hεpos
    have hj : ∀ j, a j * Real.cos (ω j * t) ≤ -|a j| + |a j| * ε := by
      intro j
      have hcos : |Real.cos (ω j * t) - Real.cos (θ j)| ≤ ε := by
        refine (abs_cos_sub_cos_le _ _).trans ?_
        have := (ht j).le
        simpa [expChar] using this
      have h1 : a j * Real.cos (ω j * t) - a j * Real.cos (θ j) ≤ |a j| * ε := by
        rw [← mul_sub]
        calc a j * (Real.cos (ω j * t) - Real.cos (θ j))
            ≤ |a j * (Real.cos (ω j * t) - Real.cos (θ j))| := le_abs_self _
          _ = |a j| * |Real.cos (ω j * t) - Real.cos (θ j)| := abs_mul _ _
          _ ≤ |a j| * ε := mul_le_mul_of_nonneg_left hcos (abs_nonneg _)
      linarith [hθ j]
    have hsum : ∑ j, a j * Real.cos (ω j * t) ≤ ∑ j, (-|a j| + |a j| * ε) := sum_le_sum fun j _ => hj j
    rw [sum_add_distrib, sum_neg_distrib, ← sum_mul] at hsum
    have := hP t
    linarith
  have hS0 : 0 ≤ S := sum_nonneg fun j _ => abs_nonneg (a j)
  by_contra hlt
  rw [not_le] at hlt
  rcases hS0.lt_or_eq with hSpos | hSzero
  · have h := hε ((S - a₀) / (2 * S)) (div_pos (by linarith) (by positivity))
    have heq : (1 - (S - a₀) / (2 * S)) * S = (S + a₀) / 2 := by field_simp; ring
    rw [heq] at h
    linarith
  · have h := hε 1 one_pos
    rw [← hSzero] at hlt
    linarith

/-- The bound is attained: any packet with `Σ_j |a_j| ≤ a_0` is nonnegative. -/
theorem packet_nonneg_of_sum_abs_le {ι : Type*} [Fintype ι] (ω : ι → ℝ) (a₀ : ℝ) (a : ι → ℝ)
    (h : ∑ j, |a j| ≤ a₀) (t : ℝ) : 0 ≤ a₀ + ∑ j, a j * Real.cos (ω j * t) := by
  have hj : ∀ j, -|a j| ≤ a j * Real.cos (ω j * t) := fun j => by
    have h1 : |a j * Real.cos (ω j * t)| ≤ |a j| := by
      rw [abs_mul]; exact mul_le_of_le_one_right (abs_nonneg _) (Real.abs_cos_le_one _)
    linarith [neg_abs_le (a j * Real.cos (ω j * t))]
  have := sum_le_sum fun j (_ : j ∈ univ) => hj j
  rw [sum_neg_distrib] at this
  linarith

/-- **Peak-to-mean.** A nonnegative packet on independent ordinates is at most twice its pole share
at `t = 0`. -/
theorem packet_peak_le_two_mul {ι : Type*} [Fintype ι] [DecidableEq ι] {ω : ι → ℝ}
    (hind : LinearIndependent ℚ ω) (a₀ : ℝ) (a : ι → ℝ)
    (hP : ∀ t : ℝ, 0 ≤ a₀ + ∑ j, a j * Real.cos (ω j * t)) :
    a₀ + ∑ j, a j ≤ 2 * a₀ := by
  have h := sum_abs_le_of_packet_nonneg hind a₀ a hP
  have := sum_le_sum fun j (_ : j ∈ univ) => le_abs_self (a j)
  linarith

/-- **Harmonic concentration.** On the harmonic ordinates `γ, …, Mγ` the Fejér packet has pole
share `M + 1`, is nonnegative, and buys `M(M + 1)` in total. -/
theorem exists_harmonic_packet (M : ℕ) :
    ∃ a : ℕ → ℝ, a 0 = M + 1 ∧
      (∀ θ : ℝ, 0 ≤ ∑ k ∈ range (M + 1), a k * Real.cos (k * θ)) ∧
      ∑ k ∈ range (M + 1), a k = (M + 1) ^ 2 := by
  set a := ArithmeticCastelnuovoSeveri.fejerAutoCoeff M (fun _ => 1)
  refine ⟨a, ?_, fun θ => ?_, ?_⟩
  · simp only [a]
    rw [MultiplicativePositivityGeometry.fejerAutoCoeff_zero_eq]
    simp
  · exact ArithmeticCastelnuovoSeveri.cosinePolynomial_fejerAutoCoeff_nonneg M _ θ
  · have h := ArithmeticCastelnuovoSeveri.cosinePolynomial_fejerAutoCoeff M (fun _ => 1) 0
    simp [HTGeometry.cosinePolynomial] at h
    linarith

/-- **Dilution versus concentration.** Over independent ordinates the total purchase is at most the
pole share; over `M` harmonic ordinates it can be `M` times the pole share. -/
theorem harmonic_purchase_eq (M : ℕ) :
    ∃ a : ℕ → ℝ, (∀ θ : ℝ, 0 ≤ ∑ k ∈ range (M + 1), a k * Real.cos (k * θ)) ∧
      ∑ k ∈ (range (M + 1)).erase 0, a k = M * a 0 := by
  obtain ⟨a, h0, hnn, hsum⟩ := exists_harmonic_packet M
  refine ⟨a, hnn, ?_⟩
  have := sum_erase_add (range (M + 1)) a (mem_range.mpr (Nat.succ_pos M))
  rw [h0]
  rw [hsum, h0] at this
  linarith

end GaloisForLFunctions.RenormalizedBiarithmeticGeometry
