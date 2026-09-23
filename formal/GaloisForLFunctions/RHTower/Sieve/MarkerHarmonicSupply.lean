import GaloisForLFunctions.RHTower.Sieve.MarkerLossDevice

/-!
# The harmonic mass of the surviving markers

The Hall criterion in its sum form needs `∑_{p ∈ P} #(C p)`, hence the harmonic mass `∑_{p ∈ P} 1/p`
of the *surviving* markers.  Discarding a set of markers all of which exceed `M₀` costs at most
their number divided by `M₀`, and their number is what the device of `Sieve/MarkerLossDevice`
bounds.
-/

namespace RHTower.Sieve

open Finset

/-- Discarding markers above `M₀` costs at most their number over `M₀`. -/
theorem sum_inv_sdiff_le {M₀ : ℕ} (hM₀ : 0 < M₀) {M P : Finset ℕ} (hPM : P ⊆ M)
    (hlarge : ∀ p ∈ M, M₀ < p) :
    ∑ p ∈ M, (1 : ℝ) / (p : ℝ) - (((M \ P).card : ℕ) : ℝ) / (M₀ : ℝ)
      ≤ ∑ p ∈ P, (1 : ℝ) / (p : ℝ) := by
  classical
  have hM₀R : (0 : ℝ) < (M₀ : ℝ) := by exact_mod_cast hM₀
  have hsplit : ∑ p ∈ M, (1 : ℝ) / (p : ℝ)
      = ∑ p ∈ P, (1 : ℝ) / (p : ℝ) + ∑ p ∈ M \ P, (1 : ℝ) / (p : ℝ) := by
    rw [← Finset.sum_sdiff hPM]
    ring
  have hbound : ∑ p ∈ M \ P, (1 : ℝ) / (p : ℝ) ≤ (((M \ P).card : ℕ) : ℝ) / (M₀ : ℝ) := by
    have hterm : ∀ p ∈ M \ P, (1 : ℝ) / (p : ℝ) ≤ 1 / (M₀ : ℝ) := by
      intro p hp
      have hpM : M₀ < p := hlarge p (Finset.mem_sdiff.1 hp).1
      have hpR : (M₀ : ℝ) ≤ (p : ℝ) := by exact_mod_cast hpM.le
      exact one_div_le_one_div_of_le hM₀R hpR
    have := Finset.sum_le_sum hterm
    rw [Finset.sum_const, nsmul_eq_mul] at this
    calc ∑ p ∈ M \ P, (1 : ℝ) / (p : ℝ) ≤ ((M \ P).card : ℝ) * (1 / (M₀ : ℝ)) := this
      _ = (((M \ P).card : ℕ) : ℝ) / (M₀ : ℝ) := by rw [mul_one_div]
  linarith

/-- **The harmonic mass of the surviving markers.** -/
theorem sum_inv_good_markers_ge {X M₀ K : ℕ} {S : Finset ℕ} {M : Finset ℕ} {Pi b : ℝ}
    (hM₀ : 0 < M₀) (hlarge : ∀ p ∈ M, M₀ < p)
    (hsep : ∀ p ∈ M, ∀ q ∈ M, p < q → X / q = X / p → q ≤ p + K)
    (hpair : ∑ d ∈ Finset.Icc 1 K,
        (((M.filter (fun p => p + d ∈ M)).card : ℕ) : ℝ) ≤ Pi)
    (hb : (S.card : ℝ) * ((M.card : ℝ) + 2 * Pi) ≤ b ^ (2 : ℕ)) (hb0 : 0 ≤ b) :
    ∑ p ∈ M, (1 : ℝ) / (p : ℝ) - b / (M₀ : ℝ)
      ≤ ∑ p ∈ M.filter (fun p => X / p ∉ S), (1 : ℝ) / (p : ℝ) := by
  classical
  set P : Finset ℕ := M.filter (fun p => X / p ∉ S) with hP
  have hPM : P ⊆ M := Finset.filter_subset _ _
  have hsdiff : M \ P = M.filter (fun p => X / p ∈ S) := by
    ext p
    rw [Finset.mem_sdiff, hP, Finset.mem_filter, Finset.mem_filter]
    constructor
    · rintro ⟨hpM, hnot⟩
      refine ⟨hpM, ?_⟩
      by_contra hcon
      exact hnot ⟨hpM, hcon⟩
    · rintro ⟨hpM, hpS⟩
      exact ⟨hpM, fun hc => hc.2 hpS⟩
  have hdev := sq_card_markers_start_mem_le (X := X) (M := M) (S := S) (K := K) hsep hpair
  have hcardle : (((M \ P).card : ℕ) : ℝ) ≤ b := by
    rw [hsdiff]
    have hsq : (((M.filter (fun p => X / p ∈ S)).card : ℕ) : ℝ) ^ (2 : ℕ) ≤ b ^ (2 : ℕ) :=
      le_trans hdev hb
    have h0 : (0 : ℝ) ≤ (((M.filter (fun p => X / p ∈ S)).card : ℕ) : ℝ) := Nat.cast_nonneg _
    nlinarith [hsq, h0, hb0]
  have hM₀R : (0 : ℝ) < (M₀ : ℝ) := by exact_mod_cast hM₀
  have hmono : (((M \ P).card : ℕ) : ℝ) / (M₀ : ℝ) ≤ b / (M₀ : ℝ) :=
    div_le_div_of_nonneg_right hcardle hM₀R.le
  linarith [sum_inv_sdiff_le hM₀ hPM hlarge]

end RHTower.Sieve
