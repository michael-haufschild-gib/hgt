import GaloisForLFunctions.RHTower.Sieve.HalaszPrimeSavingBound

/-!
# Any coefficient-free majorisation caps the GHS master bound at the trivial bound

The master bound's analytic term is a product of square roots of the two sieve mean squares of the GHS
pieces.  Majorising both by quantities that do not mention the coefficient sequence — which is what
`sieveBound` and `sieveBoundPrime` do, since they see only `‖a_n‖ ≤ A log n` — leaves a right-hand side
independent of the sequence, and the kernel constant of the Perron assembly depends only on `N`, `H`,
`σ`.  So one constant serves every sequence:

`‖∑_{n ≤ N} f(n)‖·log N ≤ ghsMasterBound N H σ Bout Bin C`   for all bounded completely multiplicative `f`.

Instantiating at the constant sequence `1`, whose partial sum over `[1,N]` is exactly `N`, gives

`N·log N ≤ ghsMasterBound N H σ Bout Bin C`,

so the bound can never assert anything beyond `‖∑_{n ≤ N} f(n)‖ ≤ N` — whatever the majorants are.  The
obstruction is therefore not the size of `sieveBound` or of `sieveBoundPrime`, and no sharpening of
either can remove it: the analytic side is blind to the coefficients apart from their moduli, and the
moduli of `μ` and of `1` agree on the squarefree integers.  What must change is the step that discards
the signs.
-/

noncomputable section
namespace RHTower.Sieve
open Complex Finset

/-- The right-hand side of the GHS master bound after majorising both sieve mean squares.  It does not
mention the coefficient sequence. -/
def ghsMasterBound (N : ℕ) (H σ Bout Bin C : ℝ) : ℝ :=
  ((9 + RHTower.Mertens.mertensTail) * (N : ℝ) + (N : ℝ) * Real.log 4
      + (9 + RHTower.Mertens.mertensTail)
          * ((N : ℝ)
              * (((Real.log 3 + 2 * ((Real.log 4 + 4) + (8 + RHTower.Mertens.mertensTail)))
                    / Real.log 2)
                  * (1 + Real.log ((Nat.log 2 N : ℕ) : ℝ)))))
    + (H + 1) * ((Real.log ((⌊(N : ℝ) + H⌋₊ : ℕ) : ℝ)) ^ (4 : ℕ) / (Real.log 2) ^ (3 : ℕ))
    + (1 / (2 * Real.pi))
        * (((1 + 1 / (σ - 1)) * Real.exp (7 / 2)) * C
            * (Real.sqrt (25 * Real.pi ^ (2 : ℕ) * Bout) * Real.sqrt (25 * Real.pi ^ (2 : ℕ) * Bin)))

/-- **The master bound with the kernel constant and both majorants as parameters.** -/
theorem norm_sum_Icc_mul_log_le_ghsMasterBound {f : ℕ → ℂ} (hf1 : f 1 = 1)
    (hfmul : ∀ a b : ℕ, f (a * b) = f a * f b) (hbdd : ∀ n : ℕ, ‖f n‖ ≤ 1)
    (N : ℕ) (hN : 2 ≤ N) {H : ℝ} (hH : 0 < H) {σ : ℝ} (hσ : 1 < σ)
    (z Y : ℕ) (hY : 1 ≤ Y) (hYz : Y ≤ z) (hz : 2 ≤ z) (hlogY : 0 < Real.log Y)
    {C : ℝ} (hC0 : 0 ≤ C)
    (hCb : ∀ y : ℝ, ‖mellin (fun x : ℝ =>
        ((GaloisForLFunctions.HTGeometry.smoothWeight ((N : ℕ) : ℝ) H x : ℝ) : ℂ))
          ((σ : ℂ) + (y : ℝ) * Complex.I)‖ ≤ C * (1 + y ^ (2 : ℕ))⁻¹)
    {Bout Bin : ℝ}
    (hout : sieveMeanSquare (ghsOuter f N) (Finset.Icc 1 N) σ z Y ≤ Bout)
    (hin : sieveMeanSquare (ghsInner f N) (Finset.Icc 1 N) σ z Y ≤ Bin) :
    ‖∑ n ∈ Finset.Icc 1 N, f n‖ * Real.log (N : ℝ) ≤ ghsMasterBound N H σ Bout Bin C := by
  have hmain := norm_sum_Icc_mul_log_le_of_kernelBound hf1 hfmul hbdd N hN hH hσ z Y hY hYz hz
    hlogY hC0 hCb
  have hsq : Real.sqrt (25 * Real.pi ^ (2 : ℕ) * sieveMeanSquare (ghsOuter f N) (Finset.Icc 1 N) σ z Y)
        * Real.sqrt (25 * Real.pi ^ (2 : ℕ) * sieveMeanSquare (ghsInner f N) (Finset.Icc 1 N) σ z Y)
      ≤ Real.sqrt (25 * Real.pi ^ (2 : ℕ) * Bout) * Real.sqrt (25 * Real.pi ^ (2 : ℕ) * Bin) := by
    refine mul_le_mul (Real.sqrt_le_sqrt (by nlinarith [hout, sq_nonneg Real.pi, Real.pi_pos]))
      (Real.sqrt_le_sqrt (by nlinarith [hin, sq_nonneg Real.pi, Real.pi_pos]))
      (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  have hmul0 : (0 : ℝ) ≤ (1 / (2 * Real.pi)) * (((1 + 1 / (σ - 1)) * Real.exp (7 / 2)) * C) := by
    have h1 : 0 < σ - 1 := by linarith
    have hfac : (0 : ℝ) ≤ (1 + 1 / (σ - 1)) * Real.exp (7 / 2) := by positivity
    have hpi : (0 : ℝ) < 1 / (2 * Real.pi) := by positivity
    exact mul_nonneg hpi.le (mul_nonneg hfac hC0)
  rw [ghsMasterBound]
  nlinarith [mul_le_mul_of_nonneg_left hsq hmul0]

/-- **One constant for every sequence.**  The kernel constant depends only on `N`, `H`, `σ`, so with
coefficient-free majorants the quantifiers exchange. -/
theorem exists_norm_sum_Icc_mul_log_le_ghsMasterBound_uniform
    (N : ℕ) (hN : 2 ≤ N) {H : ℝ} (hH : 0 < H) {σ : ℝ} (hσ : 1 < σ)
    (z Y : ℕ) (hY : 1 ≤ Y) (hYz : Y ≤ z) (hz : 2 ≤ z) (hlogY : 0 < Real.log Y) {Bout Bin : ℝ}
    (hout : ∀ g : ℕ → ℂ, g 1 = 1 → (∀ a b : ℕ, g (a * b) = g a * g b) → (∀ n : ℕ, ‖g n‖ ≤ 1) →
      sieveMeanSquare (ghsOuter g N) (Finset.Icc 1 N) σ z Y ≤ Bout)
    (hin : ∀ g : ℕ → ℂ, g 1 = 1 → (∀ a b : ℕ, g (a * b) = g a * g b) → (∀ n : ℕ, ‖g n‖ ≤ 1) →
      sieveMeanSquare (ghsInner g N) (Finset.Icc 1 N) σ z Y ≤ Bin) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ g : ℕ → ℂ, g 1 = 1 → (∀ a b : ℕ, g (a * b) = g a * g b) →
      (∀ n : ℕ, ‖g n‖ ≤ 1) →
      ‖∑ n ∈ Finset.Icc 1 N, g n‖ * Real.log (N : ℝ) ≤ ghsMasterBound N H σ Bout Bin C := by
  have hNR : (2 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  obtain ⟨C, hC0, hCb⟩ := GaloisForLFunctions.HTGeometry.exists_bound_mellin_smoothWeight_line
    (show (0 : ℝ) < ((N : ℕ) : ℝ) by linarith) hH (show (0 : ℝ) < σ by linarith)
  refine ⟨C, hC0, fun g hg1 hgmul hgbdd => ?_⟩
  exact norm_sum_Icc_mul_log_le_ghsMasterBound hg1 hgmul hgbdd N hN hH hσ z Y hY hYz hz hlogY
    hC0 hCb (hout g hg1 hgmul hgbdd) (hin g hg1 hgmul hgbdd)

/-- **Any coefficient-free majorisation caps the bound at the trivial bound.**  Instantiating the
uniform form at the constant sequence `1`, whose partial sum over `[1,N]` is `N`. -/
theorem trivial_le_ghsMasterBound (N : ℕ) (hN : 2 ≤ N) {H : ℝ} (hH : 0 < H) {σ : ℝ} (hσ : 1 < σ)
    (z Y : ℕ) (hY : 1 ≤ Y) (hYz : Y ≤ z) (hz : 2 ≤ z) (hlogY : 0 < Real.log Y) {Bout Bin : ℝ}
    (hout : ∀ g : ℕ → ℂ, g 1 = 1 → (∀ a b : ℕ, g (a * b) = g a * g b) → (∀ n : ℕ, ‖g n‖ ≤ 1) →
      sieveMeanSquare (ghsOuter g N) (Finset.Icc 1 N) σ z Y ≤ Bout)
    (hin : ∀ g : ℕ → ℂ, g 1 = 1 → (∀ a b : ℕ, g (a * b) = g a * g b) → (∀ n : ℕ, ‖g n‖ ≤ 1) →
      sieveMeanSquare (ghsInner g N) (Finset.Icc 1 N) σ z Y ≤ Bin) :
    ∃ C : ℝ, 0 ≤ C ∧ (N : ℝ) * Real.log (N : ℝ) ≤ ghsMasterBound N H σ Bout Bin C
      ∧ ∀ g : ℕ → ℂ, g 1 = 1 → (∀ a b : ℕ, g (a * b) = g a * g b) → (∀ n : ℕ, ‖g n‖ ≤ 1) →
        ‖∑ n ∈ Finset.Icc 1 N, g n‖ * Real.log (N : ℝ) ≤ ghsMasterBound N H σ Bout Bin C := by
  obtain ⟨C, hC0, huniform⟩ := exists_norm_sum_Icc_mul_log_le_ghsMasterBound_uniform N hN hH hσ
    z Y hY hYz hz hlogY hout hin
  refine ⟨C, hC0, ?_, huniform⟩
  have hone := huniform (fun _ => (1 : ℂ)) rfl (fun a b => by norm_num) (fun n => by norm_num)
  have hsum : ∑ _n ∈ Finset.Icc 1 N, (1 : ℂ) = ((N : ℕ) : ℂ) := by
    rw [Finset.sum_const, Nat.card_Icc, nsmul_eq_mul, mul_one]
    norm_num
  rw [hsum, Complex.norm_natCast] at hone
  exact hone

/-- The prime-cap majorants are coefficient-free, so the bound with the prime saving is capped. -/
theorem trivial_le_ghsMasterBound_sieveBoundPrime (N : ℕ) (hN : 2 ≤ N) {H : ℝ} (hH : 0 < H)
    {σ : ℝ} (hσ : 1 < σ) (z Y : ℕ) (hY : 1 ≤ Y) (hYz : Y ≤ z) (hz : 2 ≤ z)
    (hlogY : 0 < Real.log Y) :
    ∃ C : ℝ, 0 ≤ C ∧ (N : ℝ) * Real.log (N : ℝ)
        ≤ ghsMasterBound N H σ (sieveBoundPrime (1 / Real.log 2) σ z Y)
            (sieveBoundPrime 1 σ z Y) C
      ∧ ∀ g : ℕ → ℂ, g 1 = 1 → (∀ a b : ℕ, g (a * b) = g a * g b) → (∀ n : ℕ, ‖g n‖ ≤ 1) →
        ‖∑ n ∈ Finset.Icc 1 N, g n‖ * Real.log (N : ℝ)
          ≤ ghsMasterBound N H σ (sieveBoundPrime (1 / Real.log 2) σ z Y)
              (sieveBoundPrime 1 σ z Y) C :=
  trivial_le_ghsMasterBound N hN hH hσ z Y hY hYz hz hlogY
    (fun g _ _ hgbdd => sieveMeanSquare_le_sieveBoundPrime (norm_ghsOuter_le hgbdd N)
      (fun n hn => ghsOuter_support hn) N hσ z Y hz hlogY)
    (fun g _ _ hgbdd => sieveMeanSquare_le_sieveBoundPrime (A := 1)
      (by simpa using norm_ghsInner_le hgbdd N) (fun n hn => ghsInner_support hn) N hσ z Y hz hlogY)

/-- The integer-cap majorants are coefficient-free too, so the bound without the prime saving is
capped as well. -/
theorem trivial_le_ghsMasterBound_sieveBound (N : ℕ) (hN : 2 ≤ N) {H : ℝ} (hH : 0 < H)
    {σ : ℝ} (hσ : 1 < σ) (z Y : ℕ) (hY : 1 ≤ Y) (hYz : Y ≤ z) (hz : 2 ≤ z)
    (hlogY : 0 < Real.log Y) :
    ∃ C : ℝ, 0 ≤ C ∧ (N : ℝ) * Real.log (N : ℝ)
        ≤ ghsMasterBound N H σ (sieveBound (1 / Real.log 2) σ z Y) (sieveBound 1 σ z Y) C
      ∧ ∀ g : ℕ → ℂ, g 1 = 1 → (∀ a b : ℕ, g (a * b) = g a * g b) → (∀ n : ℕ, ‖g n‖ ≤ 1) →
        ‖∑ n ∈ Finset.Icc 1 N, g n‖ * Real.log (N : ℝ)
          ≤ ghsMasterBound N H σ (sieveBound (1 / Real.log 2) σ z Y) (sieveBound 1 σ z Y) C :=
  trivial_le_ghsMasterBound N hN hH hσ z Y hY hYz hz hlogY
    (fun g _ _ hgbdd => sieveMeanSquare_le_sieveBound (norm_ghsOuter_le hgbdd N) N hσ z Y hz hlogY)
    (fun g _ _ hgbdd => sieveMeanSquare_le_sieveBound (A := 1)
      (by simpa using norm_ghsInner_le hgbdd N) N hσ z Y hz hlogY)

end RHTower.Sieve
end
