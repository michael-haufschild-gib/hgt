import GaloisForLFunctions.RHTower.RouteEMovingTerminalKernelResonance

/-!
# Terminal-leg and multilinear antiscale resonance

Physical antiscale resonance suppresses more than terminal-by-terminal quadratic kernels.
Any absolutely summable cross-prime kernel whose every nonzero entry has at least one terminal
leg loses one full power of terminal log-width.  More generally, a signed finite-arity monomial
with one selected terminal leg loses one power, while an all-terminal monomial loses one power
per leg.  No positivity, Hermitian symmetry, or sign condition on coefficients is used.
-/

open scoped BigOperators

namespace RHTower.Sieve

noncomputable section

/-- A quadratic kernel entry with at least one terminal coordinate is inverse-linearly suppressed
at physical antiscale resonance.  The other coordinate may lie at any prime scale. -/
theorem norm_routeEStaticAbsoluteKernelTerm_terminalLeg_pi_div_log_le
    {Y eta : ℝ} (hY : 1 < Y) (heta : 0 ≤ eta)
    (K : Nat.Primes × Nat.Primes → ℂ)
    (hsupport : ∀ q, K q ≠ 0 →
      routeETerminalLogBand Y eta q.1 ∨ routeETerminalLogBand Y eta q.2)
    (q : Nat.Primes × Nat.Primes) :
    ‖routeEStaticAbsoluteKernelTerm K q (Real.pi / Real.log Y)‖ ≤
      2 * (Real.pi * eta) * ‖K q‖ := by
  by_cases hq : K q = 0
  · simp [routeEStaticAbsoluteKernelTerm, hq]
  · have hpiEta : 0 ≤ Real.pi * eta := mul_nonneg Real.pi_pos.le heta
    have hseams :
        ‖routeEAntiscaleSeam q.1 (Real.pi / Real.log Y)‖ *
            ‖routeEAntiscaleSeam q.2 (Real.pi / Real.log Y)‖ ≤
          2 * (Real.pi * eta) := by
      rcases hsupport q hq with hterminal | hterminal
      · have hsmall := norm_routeEAntiscaleSeam_pi_div_log_le hY hterminal
        have hother := norm_routeEAntiscaleSeam_le_two q.2 (Real.pi / Real.log Y)
        calc
          ‖routeEAntiscaleSeam q.1 (Real.pi / Real.log Y)‖ *
              ‖routeEAntiscaleSeam q.2 (Real.pi / Real.log Y)‖ ≤
              (Real.pi * eta) * 2 :=
            mul_le_mul hsmall hother (norm_nonneg _) hpiEta
          _ = 2 * (Real.pi * eta) := by ring
      · have hother := norm_routeEAntiscaleSeam_le_two q.1 (Real.pi / Real.log Y)
        have hsmall := norm_routeEAntiscaleSeam_pi_div_log_le hY hterminal
        exact mul_le_mul hother hsmall (norm_nonneg _) (by norm_num)
    rw [routeEStaticAbsoluteKernelTerm, norm_mul, norm_mul, RCLike.norm_conj]
    calc
      ‖K q‖ * ‖routeEAntiscaleSeam q.1 (Real.pi / Real.log Y)‖ *
          ‖routeEAntiscaleSeam q.2 (Real.pi / Real.log Y)‖ =
          ‖K q‖ *
            (‖routeEAntiscaleSeam q.1 (Real.pi / Real.log Y)‖ *
              ‖routeEAntiscaleSeam q.2 (Real.pi / Real.log Y)‖) := by ring
      _ ≤ ‖K q‖ * (2 * (Real.pi * eta)) :=
        mul_le_mul_of_nonneg_left hseams (norm_nonneg _)
      _ = 2 * (Real.pi * eta) * ‖K q‖ := by ring

/-- **One-terminal-leg quadratic resonance.**  A complete entrywise absolutely summable
cross-prime kernel is inverse-linearly small if every nonzero entry touches the terminal band. -/
theorem norm_tsum_routeEStaticAbsoluteKernelTerm_terminalLeg_pi_div_log_le
    {Y eta : ℝ} (hY : 1 < Y) (heta : 0 ≤ eta)
    {K : Nat.Primes × Nat.Primes → ℂ}
    (hK : Summable (fun q : Nat.Primes × Nat.Primes => ‖K q‖))
    (hsupport : ∀ q, K q ≠ 0 →
      routeETerminalLogBand Y eta q.1 ∨ routeETerminalLogBand Y eta q.2) :
    ‖∑' q : Nat.Primes × Nat.Primes,
        routeEStaticAbsoluteKernelTerm K q (Real.pi / Real.log Y)‖ ≤
      2 * (Real.pi * eta) *
        ∑' q : Nat.Primes × Nat.Primes, ‖K q‖ := by
  have hsummable :=
    summable_routeEStaticAbsoluteKernelTerm hK (Real.pi / Real.log Y)
  calc
    ‖∑' q : Nat.Primes × Nat.Primes,
        routeEStaticAbsoluteKernelTerm K q (Real.pi / Real.log Y)‖
        ≤ ∑' q : Nat.Primes × Nat.Primes,
            ‖routeEStaticAbsoluteKernelTerm K q (Real.pi / Real.log Y)‖ :=
          norm_tsum_le_tsum_norm hsummable.norm
    _ ≤ ∑' q : Nat.Primes × Nat.Primes,
          2 * (Real.pi * eta) * ‖K q‖ := by
        refine Summable.tsum_le_tsum (fun q => ?_) hsummable.norm
          (hK.mul_left (2 * (Real.pi * eta)))
        exact norm_routeEStaticAbsoluteKernelTerm_terminalLeg_pi_div_log_le
          hY heta K hsupport q
    _ = 2 * (Real.pi * eta) *
          ∑' q : Nat.Primes × Nat.Primes, ‖K q‖ := tsum_mul_left

/-- One coefficient of an arbitrary finite-arity signed antiscale monomial. -/
def routeEMultilinearAntiscaleTerm
    {ι τ : Type*} [Fintype ι] (K : τ → ℂ)
    (prime : τ → ι → Nat.Primes) (q : τ) (t : ℝ) : ℂ :=
  K q * ∏ j : ι, routeEAntiscaleSeam (prime q j) t

/-- One selected terminal leg gives inverse-linear suppression; every unselected leg is controlled
only by the sharp unit-circle ceiling two. -/
theorem norm_routeEMultilinearAntiscaleTerm_selectedTerminal_pi_div_log_le
    {ι τ : Type*} [Fintype ι] [DecidableEq ι]
    {Y eta : ℝ} (hY : 1 < Y) (heta : 0 ≤ eta)
    (K : τ → ℂ) (prime : τ → ι → Nat.Primes) (leg : τ → ι)
    (hsupport : ∀ q, K q ≠ 0 → routeETerminalLogBand Y eta (prime q (leg q)))
    (q : τ) :
    ‖routeEMultilinearAntiscaleTerm K prime q (Real.pi / Real.log Y)‖ ≤
      (Real.pi * eta) * 2 ^ Fintype.card ι * ‖K q‖ := by
  by_cases hq : K q = 0
  · simp [routeEMultilinearAntiscaleTerm, hq]
  · have hterminal :=
      norm_routeEAntiscaleSeam_pi_div_log_le hY (hsupport q hq)
    have herased :
        ∏ j ∈ (Finset.univ.erase (leg q)),
            ‖routeEAntiscaleSeam (prime q j) (Real.pi / Real.log Y)‖ ≤
          (2 : ℝ) ^ Fintype.card ι := by
      calc
        ∏ j ∈ (Finset.univ.erase (leg q)),
              ‖routeEAntiscaleSeam (prime q j) (Real.pi / Real.log Y)‖ ≤
            ∏ _j ∈ (Finset.univ.erase (leg q)), (2 : ℝ) := by
          exact Finset.prod_le_prod (fun j _ => norm_nonneg _)
            (fun j _ => norm_routeEAntiscaleSeam_le_two (prime q j)
              (Real.pi / Real.log Y))
        _ = (2 : ℝ) ^ (Finset.univ.erase (leg q)).card := by simp
        _ ≤ (2 : ℝ) ^ Fintype.card ι := by
          exact pow_le_pow_right₀ (by norm_num)
            (Finset.card_le_card (Finset.erase_subset _ _))
    have hprodEq :
        ∏ j : ι, ‖routeEAntiscaleSeam (prime q j) (Real.pi / Real.log Y)‖ =
          ‖routeEAntiscaleSeam (prime q (leg q)) (Real.pi / Real.log Y)‖ *
            ∏ j ∈ (Finset.univ.erase (leg q)),
              ‖routeEAntiscaleSeam (prime q j) (Real.pi / Real.log Y)‖ := by
      exact (Finset.mul_prod_erase Finset.univ
        (fun j => ‖routeEAntiscaleSeam (prime q j) (Real.pi / Real.log Y)‖)
        (Finset.mem_univ (leg q))).symm
    rw [routeEMultilinearAntiscaleTerm, norm_mul, norm_prod, hprodEq]
    have hpiEta : 0 ≤ Real.pi * eta := mul_nonneg Real.pi_pos.le heta
    have hlegs :
        ‖routeEAntiscaleSeam (prime q (leg q)) (Real.pi / Real.log Y)‖ *
            ∏ j ∈ (Finset.univ.erase (leg q)),
              ‖routeEAntiscaleSeam (prime q j) (Real.pi / Real.log Y)‖ ≤
          (Real.pi * eta) * 2 ^ Fintype.card ι :=
      mul_le_mul hterminal herased (by positivity) hpiEta
    calc
      ‖K q‖ *
          (‖routeEAntiscaleSeam (prime q (leg q)) (Real.pi / Real.log Y)‖ *
            ∏ j ∈ (Finset.univ.erase (leg q)),
              ‖routeEAntiscaleSeam (prime q j) (Real.pi / Real.log Y)‖) ≤
          ‖K q‖ *
            ((Real.pi * eta) * 2 ^ Fintype.card ι) :=
        mul_le_mul_of_nonneg_left hlegs (norm_nonneg _)
      _ = (Real.pi * eta) * 2 ^ Fintype.card ι * ‖K q‖ := by ring

/-- Complete arbitrary-arity selected-terminal resonance for entrywise absolutely summable signed
coefficients. -/
theorem norm_tsum_routeEMultilinearAntiscaleTerm_selectedTerminal_pi_div_log_le
    {ι τ : Type*} [Fintype ι] [DecidableEq ι]
    {Y eta : ℝ} (hY : 1 < Y) (heta : 0 ≤ eta)
    {K : τ → ℂ} (prime : τ → ι → Nat.Primes) (leg : τ → ι)
    (hK : Summable (fun q : τ => ‖K q‖))
    (hsupport : ∀ q, K q ≠ 0 → routeETerminalLogBand Y eta (prime q (leg q))) :
    ‖∑' q : τ,
        routeEMultilinearAntiscaleTerm K prime q (Real.pi / Real.log Y)‖ ≤
      (Real.pi * eta) * 2 ^ Fintype.card ι * ∑' q : τ, ‖K q‖ := by
  let C : ℝ := (Real.pi * eta) * 2 ^ Fintype.card ι
  have hterm : ∀ q : τ,
      ‖routeEMultilinearAntiscaleTerm K prime q (Real.pi / Real.log Y)‖ ≤
        C * ‖K q‖ := fun q =>
    norm_routeEMultilinearAntiscaleTerm_selectedTerminal_pi_div_log_le
      hY heta K prime leg hsupport q
  have hsummable : Summable (fun q : τ =>
      routeEMultilinearAntiscaleTerm K prime q (Real.pi / Real.log Y)) :=
    Summable.of_norm_bounded (hK.mul_left C) hterm
  calc
    ‖∑' q : τ,
        routeEMultilinearAntiscaleTerm K prime q (Real.pi / Real.log Y)‖
        ≤ ∑' q : τ,
            ‖routeEMultilinearAntiscaleTerm K prime q
              (Real.pi / Real.log Y)‖ := norm_tsum_le_tsum_norm hsummable.norm
    _ ≤ ∑' q : τ, C * ‖K q‖ := by
      exact Summable.tsum_le_tsum hterm hsummable.norm (hK.mul_left C)
    _ = C * ∑' q : τ, ‖K q‖ := tsum_mul_left

/-- Product form of the full terminal resonance: every terminal leg contributes one power of
`pi * eta`. -/
theorem norm_prod_routeEAntiscaleSeam_pi_div_log_le_pow
    {ι : Type*} [Fintype ι] {Y eta : ℝ} (hY : 1 < Y)
    (prime : ι → Nat.Primes)
    (hsupport : ∀ j, routeETerminalLogBand Y eta (prime j)) :
    ‖∏ j : ι, routeEAntiscaleSeam (prime j) (Real.pi / Real.log Y)‖ ≤
      (Real.pi * eta) ^ Fintype.card ι := by
  rw [norm_prod]
  calc
    ∏ j : ι, ‖routeEAntiscaleSeam (prime j) (Real.pi / Real.log Y)‖ ≤
        ∏ _j : ι, Real.pi * eta := by
      exact Finset.prod_le_prod (fun j _ => norm_nonneg _)
        (fun j _ => norm_routeEAntiscaleSeam_pi_div_log_le hY (hsupport j))
    _ = (Real.pi * eta) ^ Fintype.card ι := by simp

/-- An all-terminal arbitrary-arity monomial has inverse-degree suppression at physical
resonance. -/
theorem norm_routeEMultilinearAntiscaleTerm_allTerminal_pi_div_log_le
    {ι τ : Type*} [Fintype ι]
    {Y eta : ℝ} (hY : 1 < Y)
    (K : τ → ℂ) (prime : τ → ι → Nat.Primes)
    (hsupport : ∀ q, K q ≠ 0 → ∀ j,
      routeETerminalLogBand Y eta (prime q j))
    (q : τ) :
    ‖routeEMultilinearAntiscaleTerm K prime q (Real.pi / Real.log Y)‖ ≤
      (Real.pi * eta) ^ Fintype.card ι * ‖K q‖ := by
  by_cases hq : K q = 0
  · simp [routeEMultilinearAntiscaleTerm, hq]
  · have hproduct := norm_prod_routeEAntiscaleSeam_pi_div_log_le_pow
      hY (prime q) (hsupport q hq)
    rw [routeEMultilinearAntiscaleTerm, norm_mul]
    calc
      ‖K q‖ * ‖∏ j : ι,
          routeEAntiscaleSeam (prime q j) (Real.pi / Real.log Y)‖ ≤
          ‖K q‖ * (Real.pi * eta) ^ Fintype.card ι :=
        mul_le_mul_of_nonneg_left hproduct (norm_nonneg _)
      _ = (Real.pi * eta) ^ Fintype.card ι * ‖K q‖ := by ring

/-- Complete all-terminal arbitrary-arity resonance for entrywise absolutely summable signed
coefficients. -/
theorem norm_tsum_routeEMultilinearAntiscaleTerm_allTerminal_pi_div_log_le
    {ι τ : Type*} [Fintype ι]
    {Y eta : ℝ} (hY : 1 < Y) (heta : 0 ≤ eta)
    {K : τ → ℂ} (prime : τ → ι → Nat.Primes)
    (hK : Summable (fun q : τ => ‖K q‖))
    (hsupport : ∀ q, K q ≠ 0 → ∀ j,
      routeETerminalLogBand Y eta (prime q j)) :
    ‖∑' q : τ,
        routeEMultilinearAntiscaleTerm K prime q (Real.pi / Real.log Y)‖ ≤
      (Real.pi * eta) ^ Fintype.card ι * ∑' q : τ, ‖K q‖ := by
  let C : ℝ := (Real.pi * eta) ^ Fintype.card ι
  have hC : 0 ≤ C := pow_nonneg (mul_nonneg Real.pi_pos.le heta) _
  have hterm : ∀ q : τ,
      ‖routeEMultilinearAntiscaleTerm K prime q (Real.pi / Real.log Y)‖ ≤
        C * ‖K q‖ := fun q =>
    norm_routeEMultilinearAntiscaleTerm_allTerminal_pi_div_log_le
      hY K prime hsupport q
  have hsummable : Summable (fun q : τ =>
      routeEMultilinearAntiscaleTerm K prime q (Real.pi / Real.log Y)) :=
    Summable.of_norm_bounded (hK.mul_left C) hterm
  calc
    ‖∑' q : τ,
        routeEMultilinearAntiscaleTerm K prime q (Real.pi / Real.log Y)‖
        ≤ ∑' q : τ,
            ‖routeEMultilinearAntiscaleTerm K prime q
              (Real.pi / Real.log Y)‖ := norm_tsum_le_tsum_norm hsummable.norm
    _ ≤ ∑' q : τ, C * ‖K q‖ := by
      exact Summable.tsum_le_tsum hterm hsummable.norm (hK.mul_left C)
    _ = C * ∑' q : τ, ‖K q‖ := tsum_mul_left

end

end RHTower.Sieve
