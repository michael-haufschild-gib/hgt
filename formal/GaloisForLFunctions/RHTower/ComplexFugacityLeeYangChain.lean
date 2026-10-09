import GaloisForLFunctions.RHTower.RiemannSiegelLeeYangChain

/-!
# Lee–Yang chains with complex wall fugacities

The chain of `RiemannSiegelLeeYangChain` has wall fugacities `c k ∈ [0, 1]`, i.e. ferromagnetic
couplings, and positive weight on every spin configuration.  Real-rootedness does not need that
positivity.  Replace the transfer step by the Szegő-type step

  `(A, B) ↦ (A + α B, u (conj α · A + B))`

with complex fugacities `α k` in the closed unit disc.

* The cross terms of `‖A + αB‖²` and `‖conj α · A + B‖²` coincide, so
  `‖conj α · A + B‖² − ‖A + α B‖² = (‖α‖² − 1)(‖A‖² − ‖B‖²)` (`normSq_conj_mul_add_sub`).  Hence
  `‖B_k‖ < ‖A_k‖` propagates whenever every field lies in the open unit disc
  (`cChainPair_inside`).
* Global spin flip exchanges `A` and `B` and conjugates the fugacities
  (`cChainZ_reciprocal`).
* For exponential fields `u_k = e^{−i λ_k z}` with `λ_k > 0`, every zero of `z ↦ Z` is real, for
  every sequence of complex fugacities with `‖α k‖ ≤ 1` (`cChainZ_ne_zero_of_im_ne_zero`).
  Fugacities of either sign, e.g. `α_k = μ(k+2)(k+2)^{−1/2}`, are allowed.  For real fugacities
  in `[0, 1]` the chain is the ferromagnetic chain (`cChainPair_ofReal`).
-/

open Complex Finset

namespace RHTower.LeeYangChain

noncomputable section

/-- Chain weights `(A_k, B_k)` with complex wall fugacities `α k`. -/
def cChainPair (α : ℕ → ℂ) (u : ℕ → ℂ) : ℕ → ℂ × ℂ
  | 0 => (1, u 0)
  | k + 1 =>
      ((cChainPair α u k).1 + α k * (cChainPair α u k).2,
        u (k + 1) * ((starRingEnd ℂ) (α k) * (cChainPair α u k).1 + (cChainPair α u k).2))

/-- The chain partition function with complex wall fugacities. -/
def cChainZ (α : ℕ → ℂ) (u : ℕ → ℂ) (N : ℕ) : ℂ := (cChainPair α u N).1 + (cChainPair α u N).2

/-- Real fugacities give the ferromagnetic chain. -/
theorem cChainPair_ofReal (c : ℕ → ℝ) (u : ℕ → ℂ) (k : ℕ) :
    cChainPair (fun i => (c i : ℂ)) u k = chainPair c u k := by
  induction k with
  | zero => rfl
  | succ k ih => simp only [cChainPair, chainPair, ih, Complex.conj_ofReal]

theorem normSq_conj_mul_add_sub (α A B : ℂ) :
    Complex.normSq ((starRingEnd ℂ) α * A + B) - Complex.normSq (A + α * B) =
      (Complex.normSq α - 1) * (Complex.normSq A - Complex.normSq B) := by
  simp only [Complex.normSq_add, Complex.normSq_conj, map_mul]
  have h : ((starRingEnd ℂ) α * A * (starRingEnd ℂ) B).re =
      (A * ((starRingEnd ℂ) α * (starRingEnd ℂ) B)).re := by
    ring_nf
  rw [h]
  ring

theorem cChainPair_inside {α : ℕ → ℂ} {u : ℕ → ℂ} (hα : ∀ k, ‖α k‖ ≤ 1)
    (hu : ∀ k, ‖u k‖ < 1) (k : ℕ) :
    (cChainPair α u k).1 ≠ 0 ∧ ‖(cChainPair α u k).2‖ < ‖(cChainPair α u k).1‖ := by
  induction k with
  | zero => simpa [cChainPair] using hu 0
  | succ k ih =>
    obtain ⟨hA, hB⟩ := ih
    obtain ⟨A, hAdef⟩ : ∃ A, A = (cChainPair α u k).1 := ⟨_, rfl⟩
    obtain ⟨B, hBdef⟩ : ∃ B, B = (cChainPair α u k).2 := ⟨_, rfl⟩
    rw [← hAdef] at hA hB
    rw [← hBdef] at hB
    simp only [cChainPair, ← hAdef, ← hBdef]
    have hαB : ‖α k * B‖ < ‖A‖ := by
      rw [norm_mul]
      calc ‖α k‖ * ‖B‖ ≤ 1 * ‖B‖ := mul_le_mul_of_nonneg_right (hα k) (norm_nonneg _)
        _ < ‖A‖ := by rw [one_mul]; exact hB
    have hA' : A + α k * B ≠ 0 := by
      intro h
      have : A = -(α k * B) := by linear_combination h
      rw [this, norm_neg] at hαB
      exact lt_irrefl _ hαB
    have hsq : Complex.normSq ((starRingEnd ℂ) (α k) * A + B) ≤ Complex.normSq (A + α k * B) := by
      have h := normSq_conj_mul_add_sub (α k) A B
      have hAB : Complex.normSq B < Complex.normSq A := by
        rw [← Complex.sq_norm, ← Complex.sq_norm]
        exact pow_lt_pow_left₀ hB (norm_nonneg _) two_ne_zero
      have hα2 : Complex.normSq (α k) - 1 ≤ 0 := by
        rw [← Complex.sq_norm]
        nlinarith [hα k, norm_nonneg (α k)]
      nlinarith
    have hnorm : ‖(starRingEnd ℂ) (α k) * A + B‖ ≤ ‖A + α k * B‖ := by
      rw [← Complex.sq_norm, ← Complex.sq_norm] at hsq
      exact (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).mp hsq
    refine ⟨hA', ?_⟩
    rw [norm_mul]
    calc ‖u (k + 1)‖ * ‖(starRingEnd ℂ) (α k) * A + B‖ ≤ ‖u (k + 1)‖ * ‖A + α k * B‖ :=
          mul_le_mul_of_nonneg_left hnorm (norm_nonneg _)
      _ < 1 * ‖A + α k * B‖ :=
          mul_lt_mul_of_pos_right (hu (k + 1)) (norm_pos_iff.mpr hA')
      _ = ‖A + α k * B‖ := one_mul _

/-- **Lee–Yang for complex fugacities.**  Fields inside the unit disc and fugacities in the closed
unit disc make the partition function nonzero. -/
theorem cChainZ_ne_zero_of_norm_lt_one {α : ℕ → ℂ} {u : ℕ → ℂ} (hα : ∀ k, ‖α k‖ ≤ 1)
    (hu : ∀ k, ‖u k‖ < 1) (N : ℕ) : cChainZ α u N ≠ 0 := by
  obtain ⟨hA, hB⟩ := cChainPair_inside hα hu N
  intro h
  rw [cChainZ] at h
  have : (cChainPair α u N).2 = -(cChainPair α u N).1 := by linear_combination h
  rw [this, norm_neg] at hB
  exact lt_irrefl _ hB

/-- Global spin flip exchanges the two weights and conjugates the fugacities. -/
theorem cChainPair_reciprocal (α : ℕ → ℂ) {u : ℕ → ℂ} (hu : ∀ k, u k ≠ 0) (k : ℕ) :
    (cChainPair α u k).1 =
        (∏ i ∈ range (k + 1), u i) *
          (cChainPair (fun i => (starRingEnd ℂ) (α i)) (fun i => (u i)⁻¹) k).2 ∧
      (cChainPair α u k).2 =
        (∏ i ∈ range (k + 1), u i) *
          (cChainPair (fun i => (starRingEnd ℂ) (α i)) (fun i => (u i)⁻¹) k).1 := by
  induction k with
  | zero =>
    simp only [cChainPair, zero_add, range_one, prod_singleton]
    exact ⟨(mul_inv_cancel₀ (hu 0)).symm, (mul_one _).symm⟩
  | succ k ih =>
    obtain ⟨h1, h2⟩ := ih
    simp only [cChainPair, Complex.conj_conj]
    rw [prod_range_succ, h1, h2]
    have hk := hu (k + 1)
    constructor
    · field_simp
      ring
    · ring

theorem cChainZ_reciprocal (α : ℕ → ℂ) {u : ℕ → ℂ} (hu : ∀ k, u k ≠ 0) (N : ℕ) :
    cChainZ α u N = (∏ i ∈ range (N + 1), u i) *
      cChainZ (fun i => (starRingEnd ℂ) (α i)) (fun i => (u i)⁻¹) N := by
  obtain ⟨h1, h2⟩ := cChainPair_reciprocal α hu N
  rw [cChainZ, cChainZ, h1, h2]
  ring

/-- **Real zeros without positivity.**  With exponential fields of positive frequencies, every zero
of the chain partition function is real, for every sequence of complex wall fugacities in the
closed unit disc. -/
theorem cChainZ_ne_zero_of_im_ne_zero {α : ℕ → ℂ} {freqs : ℕ → ℝ} (hα : ∀ k, ‖α k‖ ≤ 1)
    (hfreq : ∀ k, 0 < freqs k) (N : ℕ) {z : ℂ} (hz : z.im ≠ 0) :
    cChainZ α (chainExpField freqs z) N ≠ 0 := by
  rcases lt_or_gt_of_ne hz with hneg | hpos
  · refine cChainZ_ne_zero_of_norm_lt_one hα (fun k => ?_) N
    rw [norm_chainExpField, Real.exp_lt_one_iff]
    exact mul_neg_of_pos_of_neg (hfreq k) hneg
  · have hne : ∀ k, chainExpField freqs z k ≠ 0 := fun k => Complex.exp_ne_zero _
    rw [cChainZ_reciprocal α hne N]
    refine mul_ne_zero (prod_ne_zero_iff.mpr fun k _ => hne k)
      (cChainZ_ne_zero_of_norm_lt_one (fun k => by rw [Complex.norm_conj]; exact hα k)
        (fun k => ?_) N)
    rw [norm_inv, norm_chainExpField, inv_lt_one₀ (Real.exp_pos _), Real.one_lt_exp_iff]
    exact mul_pos (hfreq k) hpos

end

end RHTower.LeeYangChain
