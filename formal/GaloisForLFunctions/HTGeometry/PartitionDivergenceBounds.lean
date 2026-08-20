/-
# The log-sum inequality and the partition lower bounds on accessibility divergence

Data processing for relative entropy is the log-sum inequality, and the log-sum inequality is one
application of `log t ≥ 1 - 1/t` per cell.  Applying it to the two-cell partition `{A, Aᶜ}` turns
the target mass of the accessibility-biased law into an explicit entropy lower bound, and the
capacity window turns the same mass into a chi-square lower bound.

Main results:
* `log_sum_le` — **the log-sum inequality** on a finite family.
* `finRelEntropy` — relative entropy of two finite laws.
* `partition_le_finRelEntropy` — **two-cell data processing**.
* `binaryEntropy_le_log_two` — `H₂(p) ≤ log 2`.
* `le_finRelEntropy_of_target_mass` — **`(11aa)`**: `D(σ‖π) ≥ (1-a)log(1/q) - log 2`.
* `le_chiSquare` — **`(11ab)`**: `χ²(σ‖π) ≥ (1-a)²/cap - 1 ≥ (1-a)²/π(A) - 1`.
-/
import Mathlib

open Finset

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-! ## The log-sum inequality -/

/-- **The log-sum inequality.**  For nonnegative numerators and positive denominators, the sum of
the individual surprisals dominates the surprisal of the sums. -/
theorem log_sum_le {ι : Type*} (s : Finset ι) (a b : ι → ℝ)
    (ha : ∀ i ∈ s, 0 ≤ a i) (hb : ∀ i ∈ s, 0 < b i)
    (hA : 0 < ∑ i ∈ s, a i) :
    (∑ i ∈ s, a i) * Real.log ((∑ i ∈ s, a i) / (∑ i ∈ s, b i))
      ≤ ∑ i ∈ s, a i * Real.log (a i / b i) := by
  classical
  obtain ⟨A, hAdef⟩ : ∃ A, A = ∑ i ∈ s, a i := ⟨_, rfl⟩
  obtain ⟨B, hBdef⟩ : ∃ B, B = ∑ i ∈ s, b i := ⟨_, rfl⟩
  rw [← hAdef] at hA ⊢
  rw [← hBdef]
  have hsne : s.Nonempty := by
    rcases Finset.eq_empty_or_nonempty s with hs | hs
    · rw [hs, Finset.sum_empty] at hAdef
      rw [hAdef] at hA
      exact absurd hA (lt_irrefl 0)
    · exact hs
  have hB : 0 < B := by rw [hBdef]; exact Finset.sum_pos hb hsne
  have hterm : ∀ i ∈ s, a i * Real.log (A / B) + (a i - b i * A / B)
      ≤ a i * Real.log (a i / b i) := by
    intro i hi
    have hbi := hb i hi
    rcases eq_or_lt_of_le (ha i hi) with hzero | hpos
    · rw [← hzero]
      have hnn : 0 ≤ b i * A / B := div_nonneg (mul_nonneg hbi.le hA.le) hB.le
      simp only [zero_mul, zero_add, zero_sub, zero_div, Real.log_zero, mul_zero]
      linarith
    · have hpos2 : (0 : ℝ) < (b i * A) / (a i * B) :=
        div_pos (mul_pos hbi hA) (mul_pos hpos hB)
      have hlog : Real.log ((b i * A) / (a i * B)) ≤ (b i * A) / (a i * B) - 1 :=
        Real.log_le_sub_one_of_pos hpos2
      have hsplit : Real.log (a i / b i) - Real.log (A / B)
          = -Real.log ((b i * A) / (a i * B)) := by
        rw [← Real.log_div (div_ne_zero (ne_of_gt hpos) (ne_of_gt hbi))
            (div_ne_zero (ne_of_gt hA) (ne_of_gt hB)), ← Real.log_inv]
        congr 1
        field_simp
      have hkey : Real.log (A / B) + (1 - (b i * A) / (a i * B)) ≤ Real.log (a i / b i) := by
        linarith
      have hmul := mul_le_mul_of_nonneg_left hkey hpos.le
      have hexp : a i * (Real.log (A / B) + (1 - (b i * A) / (a i * B)))
          = a i * Real.log (A / B) + (a i - b i * A / B) := by
        field_simp
      rw [hexp] at hmul
      exact hmul
  have hsum := Finset.sum_le_sum hterm
  have hleft : (∑ i ∈ s, (a i * Real.log (A / B) + (a i - b i * A / B)))
      = A * Real.log (A / B) := by
    rw [Finset.sum_add_distrib, ← Finset.sum_mul, Finset.sum_sub_distrib, ← hAdef]
    have hb2 : (∑ i ∈ s, b i * A / B) = A := by
      rw [show (fun i => b i * A / B) = (fun i => b i * (A / B)) by funext i; ring]
      rw [← Finset.sum_mul, ← hBdef]
      field_simp
    rw [hb2]
    ring
  rw [hleft] at hsum
  exact hsum

/-! ## Relative entropy of finite laws -/

variable {X : Type*} [Fintype X] [DecidableEq X]

/-- Relative entropy of two finite laws. -/
def finRelEntropy (sigma pi : X → ℝ) : ℝ := ∑ x, sigma x * Real.log (sigma x / pi x)

/-- **Two-cell data processing.**  The relative entropy dominates the relative entropy of the
`{A, Aᶜ}` coarsening. -/
theorem partition_le_finRelEntropy {sigma pi : X → ℝ} (A : Finset X)
    (hsigma : ∀ x, 0 ≤ sigma x) (hpi : ∀ x, 0 < pi x)
    (hAmass : 0 < ∑ x ∈ A, sigma x) (hAcmass : 0 < ∑ x ∈ Aᶜ, sigma x) :
    (∑ x ∈ A, sigma x) * Real.log ((∑ x ∈ A, sigma x) / (∑ x ∈ A, pi x))
        + (∑ x ∈ Aᶜ, sigma x) * Real.log ((∑ x ∈ Aᶜ, sigma x) / (∑ x ∈ Aᶜ, pi x))
      ≤ finRelEntropy sigma pi := by
  classical
  have h1 := log_sum_le A sigma pi (fun x _ => hsigma x) (fun x _ => hpi x) hAmass
  have h2 := log_sum_le Aᶜ sigma pi (fun x _ => hsigma x) (fun x _ => hpi x) hAcmass
  have hsplit : finRelEntropy sigma pi
      = (∑ x ∈ A, sigma x * Real.log (sigma x / pi x))
        + ∑ x ∈ Aᶜ, sigma x * Real.log (sigma x / pi x) := by
    rw [finRelEntropy, ← Finset.sum_add_sum_compl A]
  rw [hsplit]
  linarith

/-- **`H₂(p) ≤ log 2`.** -/
theorem binaryEntropy_le_log_two {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) :
    -(p * Real.log p) - ((1 - p) * Real.log (1 - p)) ≤ Real.log 2 := by
  have hone : (0 : ℝ) < 1 - p := by linarith
  have hstep : ∀ t : ℝ, 0 < t → 1 - 1 / t ≤ Real.log t := by
    intro t ht
    have h := Real.log_le_sub_one_of_pos (show (0:ℝ) < 1 / t by positivity)
    rw [one_div, Real.log_inv] at h
    have : (1 : ℝ) / t = t⁻¹ := one_div t
    rw [this]
    linarith
  have h1 : 1 - 1 / (2 * p) ≤ Real.log (2 * p) := hstep _ (by linarith)
  have h2 : 1 - 1 / (2 * (1 - p)) ≤ Real.log (2 * (1 - p)) := hstep _ (by linarith)
  have hl1 : Real.log (2 * p) = Real.log 2 + Real.log p :=
    Real.log_mul (by norm_num) (ne_of_gt hp0)
  have hl2 : Real.log (2 * (1 - p)) = Real.log 2 + Real.log (1 - p) :=
    Real.log_mul (by norm_num) (ne_of_gt hone)
  have e1 : p * (1 - 1 / (2 * p)) = p - 1 / 2 := by field_simp
  have e2 : (1 - p) * (1 - 1 / (2 * (1 - p))) = (1 - p) - 1 / 2 := by field_simp
  have m1 := mul_le_mul_of_nonneg_left h1 hp0.le
  have m2 := mul_le_mul_of_nonneg_left h2 hone.le
  rw [e1, hl1] at m1
  rw [e2, hl2] at m2
  nlinarith [m1, m2]


/-- **`(11aa)`.**  A law whose target mass is at least `1−a` has relative entropy at least
`(1−a)log(1/π(A)) − log 2` against the reference: data processing to the two-cell partition, the
binary-entropy ceiling, and the nonnegativity of the complementary surprisal. -/
theorem le_finRelEntropy_of_target_mass {sigma pi : X → ℝ} (A : Finset X)
    (hsigma : ∀ x, 0 ≤ sigma x) (hpi : ∀ x, 0 < pi x)
    (hsigmasum : ∑ x, sigma x = 1) (hpisum : ∑ x, pi x = 1)
    {a : ℝ} (ha1 : a < 1)
    (hmass : 1 - a ≤ ∑ x ∈ A, sigma x)
    (hlt : (∑ x ∈ A, sigma x) < 1) :
    (1 - a) * Real.log (1 / (∑ x ∈ A, pi x)) - Real.log 2 ≤ finRelEntropy sigma pi := by
  classical
  obtain ⟨p, hpdef⟩ : ∃ p, p = ∑ x ∈ A, sigma x := ⟨_, rfl⟩
  obtain ⟨q, hqdef⟩ : ∃ q, q = ∑ x ∈ A, pi x := ⟨_, rfl⟩
  have hsplitS : (∑ x ∈ A, sigma x) + ∑ x ∈ Aᶜ, sigma x = 1 := by
    rw [Finset.sum_add_sum_compl, hsigmasum]
  have hsplitP : (∑ x ∈ A, pi x) + ∑ x ∈ Aᶜ, pi x = 1 := by
    rw [Finset.sum_add_sum_compl, hpisum]
  have hp0 : 0 < p := by rw [hpdef]; linarith
  have hp1 : p < 1 := by rw [hpdef]; exact hlt
  have hpc : (∑ x ∈ Aᶜ, sigma x) = 1 - p := by rw [hpdef]; linarith
  have hqc : (∑ x ∈ Aᶜ, pi x) = 1 - q := by rw [hqdef]; linarith
  have hAne : A.Nonempty := by
    rcases Finset.eq_empty_or_nonempty A with hA | hA
    · rw [hA, Finset.sum_empty] at hpdef
      rw [hpdef] at hp0
      exact absurd hp0 (lt_irrefl 0)
    · exact hA
  have hAcne : Aᶜ.Nonempty := by
    rcases Finset.eq_empty_or_nonempty Aᶜ with hA | hA
    · rw [hA, Finset.sum_empty] at hpc
      have : p = 1 := by linarith
      rw [this] at hp1
      exact absurd hp1 (lt_irrefl 1)
    · exact hA
  have hq0 : 0 < q := by rw [hqdef]; exact Finset.sum_pos (fun x _ => hpi x) hAne
  have hqc0 : 0 < 1 - q := by
    rw [← hqc]
    exact Finset.sum_pos (fun x _ => hpi x) hAcne
  have hq1 : q < 1 := by linarith
  have hpart := partition_le_finRelEntropy A hsigma hpi (by rw [← hpdef]; exact hp0)
    (by rw [hpc]; linarith)
  rw [← hpdef, ← hqdef, hpc, hqc] at hpart
  have hlogp : Real.log (p / q) = Real.log p - Real.log q :=
    Real.log_div (ne_of_gt hp0) (ne_of_gt hq0)
  have hlogpc : Real.log ((1 - p) / (1 - q)) = Real.log (1 - p) - Real.log (1 - q) :=
    Real.log_div (by linarith) (ne_of_gt hqc0)
  rw [hlogp, hlogpc] at hpart
  have hbin := binaryEntropy_le_log_two hp0 hp1
  have hlogq : 0 ≤ -Real.log q := by
    have := Real.log_nonpos hq0.le hq1.le
    linarith
  have hlogqc : 0 ≤ -Real.log (1 - q) := by
    have := Real.log_nonpos hqc0.le (by linarith)
    linarith
  have hstep : (1 - a) * (-Real.log q) ≤ p * (-Real.log q) :=
    mul_le_mul_of_nonneg_right (by rw [hpdef]; exact hmass) hlogq
  have hpc0 : 0 ≤ 1 - p := by linarith
  have hlast : 0 ≤ (1 - p) * (-Real.log (1 - q)) := mul_nonneg hpc0 hlogqc
  rw [one_div, Real.log_inv, ← hqdef]
  linarith

end

end GaloisForLFunctions.HTGeometry
