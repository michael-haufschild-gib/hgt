import GaloisForLFunctions.RHTower.Sieve.HalaszPrimeSavingBound

/-!
# The prime-saving master bound is at least the trivial bound

Majorising both sieve mean squares by their dyadic Chebyshev caps removes every trace of the
coefficient sequence from the right-hand side: `sieveBoundPrime A σ z Y` sees only the majorant
`‖a_n‖ ≤ A log n`, and the kernel constant of the Perron assembly depends only on `N`, `H`, `σ`.  So
one constant serves every sequence, and the bound reads

`‖∑_{n ≤ N} f(n)‖·log N ≤ ghsPrimeMasterBound N H σ z Y C`   for all bounded completely multiplicative `f`.

Instantiating at the constant sequence `1`, whose left side is exactly `N log N`, therefore forces

`N·log N ≤ ghsPrimeMasterBound N H σ z Y C`,

so the bound can never assert anything beyond `‖∑_{n ≤ N} f(n)‖ ≤ N`.  The obstruction is not the size
of any one estimate: it is that the analytic side of this architecture is blind to the coefficients
apart from their moduli, and the moduli of `μ` and of `1` agree on the squarefree integers.  Sharpening
the caps cannot help; what must change is the step that discards the signs.
-/

noncomputable section
namespace RHTower.Sieve
open Complex Finset

/-- The right-hand side of the prime-saving master bound.  It does not mention the coefficient
sequence. -/
def ghsPrimeMasterBound (N : ℕ) (H σ : ℝ) (z Y : ℕ) (C : ℝ) : ℝ :=
  ((9 + RHTower.Mertens.mertensTail) * (N : ℝ) + (N : ℝ) * Real.log 4
      + (9 + RHTower.Mertens.mertensTail)
          * ((N : ℝ)
              * (((Real.log 3 + 2 * ((Real.log 4 + 4) + (8 + RHTower.Mertens.mertensTail)))
                    / Real.log 2)
                  * (1 + Real.log ((Nat.log 2 N : ℕ) : ℝ)))))
    + (H + 1) * ((Real.log ((⌊(N : ℝ) + H⌋₊ : ℕ) : ℝ)) ^ 4 / (Real.log 2) ^ 3)
    + (1 / (2 * Real.pi))
        * (((1 + 1 / (σ - 1)) * Real.exp (7 / 2)) * C
            * (Real.sqrt (25 * Real.pi ^ 2 * sieveBoundPrime (1 / Real.log 2) σ z Y)
                * Real.sqrt (25 * Real.pi ^ 2 * sieveBoundPrime 1 σ z Y)))

/-- **The prime-saving master bound with the kernel constant as a parameter.** -/
theorem norm_sum_Icc_mul_log_le_ghsPrimeMasterBound {f : ℕ → ℂ} (hf1 : f 1 = 1)
    (hfmul : ∀ a b : ℕ, f (a * b) = f a * f b) (hbdd : ∀ n : ℕ, ‖f n‖ ≤ 1)
    (N : ℕ) (hN : 2 ≤ N) {H : ℝ} (hH : 0 < H) {σ : ℝ} (hσ : 1 < σ)
    (z Y : ℕ) (hY : 1 ≤ Y) (hYz : Y ≤ z) (hz : 2 ≤ z) (hlogY : 0 < Real.log Y)
    {C : ℝ} (hC0 : 0 ≤ C)
    (hCb : ∀ y : ℝ, ‖mellin (fun x : ℝ =>
        ((GaloisForLFunctions.HTGeometry.smoothWeight ((N : ℕ) : ℝ) H x : ℝ) : ℂ))
          ((σ : ℂ) + (y : ℝ) * Complex.I)‖ ≤ C * (1 + y ^ 2)⁻¹) :
    ‖∑ n ∈ Finset.Icc 1 N, f n‖ * Real.log (N : ℝ)
      ≤ ghsPrimeMasterBound N H σ z Y C := by
  have hmain := norm_sum_Icc_mul_log_le_of_kernelBound hf1 hfmul hbdd N hN hH hσ z Y hY hYz hz
    hlogY hC0 hCb
  have hout := sieveMeanSquare_le_sieveBoundPrime (norm_ghsOuter_le hbdd N)
    (fun n hn => ghsOuter_support hn) N hσ z Y hz hlogY
  have hin := sieveMeanSquare_le_sieveBoundPrime (A := 1)
    (by simpa using norm_ghsInner_le hbdd N) (fun n hn => ghsInner_support hn) N hσ z Y hz hlogY
  have hsq : Real.sqrt (25 * Real.pi ^ 2 * sieveMeanSquare (ghsOuter f N) (Finset.Icc 1 N) σ z Y)
        * Real.sqrt (25 * Real.pi ^ 2 * sieveMeanSquare (ghsInner f N) (Finset.Icc 1 N) σ z Y)
      ≤ Real.sqrt (25 * Real.pi ^ 2 * sieveBoundPrime (1 / Real.log 2) σ z Y)
        * Real.sqrt (25 * Real.pi ^ 2 * sieveBoundPrime 1 σ z Y) := by
    refine mul_le_mul (Real.sqrt_le_sqrt (by nlinarith [hout, sq_nonneg Real.pi, Real.pi_pos]))
      (Real.sqrt_le_sqrt (by nlinarith [hin, sq_nonneg Real.pi, Real.pi_pos]))
      (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  have hmul0 : (0 : ℝ) ≤ (1 / (2 * Real.pi)) * (((1 + 1 / (σ - 1)) * Real.exp (7 / 2)) * C) := by
    have h1 : 0 < σ - 1 := by linarith
    have hfac : (0 : ℝ) ≤ (1 + 1 / (σ - 1)) * Real.exp (7 / 2) := by positivity
    have hpi : (0 : ℝ) < 1 / (2 * Real.pi) := by positivity
    exact mul_nonneg hpi.le (mul_nonneg hfac hC0)
  rw [ghsPrimeMasterBound]
  nlinarith [mul_le_mul_of_nonneg_left hsq hmul0]

/-- **One constant for every sequence.**  The kernel constant depends only on `N`, `H`, `σ`, so the
quantifiers can be exchanged. -/
theorem exists_norm_sum_Icc_mul_log_le_ghsPrimeMasterBound_uniform
    (N : ℕ) (hN : 2 ≤ N) {H : ℝ} (hH : 0 < H) {σ : ℝ} (hσ : 1 < σ)
    (z Y : ℕ) (hY : 1 ≤ Y) (hYz : Y ≤ z) (hz : 2 ≤ z) (hlogY : 0 < Real.log Y) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ g : ℕ → ℂ, g 1 = 1 → (∀ a b : ℕ, g (a * b) = g a * g b) →
      (∀ n : ℕ, ‖g n‖ ≤ 1) →
      ‖∑ n ∈ Finset.Icc 1 N, g n‖ * Real.log (N : ℝ)
        ≤ ghsPrimeMasterBound N H σ z Y C := by
  have hNR : (2 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  obtain ⟨C, hC0, hCb⟩ := GaloisForLFunctions.HTGeometry.exists_bound_mellin_smoothWeight_line
    (show (0 : ℝ) < ((N : ℕ) : ℝ) by linarith) hH (show (0 : ℝ) < σ by linarith)
  refine ⟨C, hC0, fun g hg1 hgmul hgbdd => ?_⟩
  exact norm_sum_Icc_mul_log_le_ghsPrimeMasterBound hg1 hgmul hgbdd N hN hH hσ z Y hY hYz hz
    hlogY hC0 hCb

/-- **The bound is at least the trivial bound.**  Instantiating the uniform form at the constant
sequence `1`, whose partial sum is `N`. -/
theorem trivial_le_ghsPrimeMasterBound (N : ℕ) (hN : 2 ≤ N) {H : ℝ} (hH : 0 < H) {σ : ℝ}
    (hσ : 1 < σ) (z Y : ℕ) (hY : 1 ≤ Y) (hYz : Y ≤ z) (hz : 2 ≤ z) (hlogY : 0 < Real.log Y) :
    ∃ C : ℝ, 0 ≤ C ∧ (N : ℝ) * Real.log (N : ℝ) ≤ ghsPrimeMasterBound N H σ z Y C
      ∧ ∀ g : ℕ → ℂ, g 1 = 1 → (∀ a b : ℕ, g (a * b) = g a * g b) → (∀ n : ℕ, ‖g n‖ ≤ 1) →
        ‖∑ n ∈ Finset.Icc 1 N, g n‖ * Real.log (N : ℝ)
          ≤ ghsPrimeMasterBound N H σ z Y C := by
  obtain ⟨C, hC0, huniform⟩ :=
    exists_norm_sum_Icc_mul_log_le_ghsPrimeMasterBound_uniform N hN hH hσ z Y hY hYz hz hlogY
  refine ⟨C, hC0, ?_, huniform⟩
  have hone := huniform (fun _ => (1 : ℂ)) rfl (fun a b => by norm_num) (fun n => by norm_num)
  have hsum : ∑ _n ∈ Finset.Icc 1 N, (1 : ℂ) = ((N : ℕ) : ℂ) := by
    rw [Finset.sum_const, Nat.card_Icc, nsmul_eq_mul, mul_one]
    norm_num
  rw [hsum] at hone
  have hnorm : ‖((N : ℕ) : ℂ)‖ = (N : ℝ) := by
    rw [Complex.norm_natCast]
  rwa [hnorm] at hone

end RHTower.Sieve
end
