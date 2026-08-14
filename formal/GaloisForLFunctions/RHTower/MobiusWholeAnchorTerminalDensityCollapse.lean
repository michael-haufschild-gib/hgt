import GaloisForLFunctions.RHTower.MobiusWholeAnchorGlobalTerminalCapacity

/-!
# Density collapse and column load of the full-allocation whole-anchor terminal universe

The global capacity bound for the whole-anchor terminal universe is combined here with the finite
row-stochastic conservation law.  Three consequences are proved.

* Along any band schedule whose capacity weight `(log log b + K) · log Z / log b` tends to zero,
  the physical terminal universe has vanishing density in the window.
* Any upper bound for the terminal universe converts the conservation law into a lower bound for
  the heaviest column of a row-stochastic kernel into the terminal universe, so bounded column
  load forces the terminal density to be comparable to the source density.
* In the band regime `exp √(log log b) ≤ log W` and `log Z · (log log b)² ≤ log b` the terminal
  universe is exponentially sparse, `#𝒯 ≤ C · b · exp(-√(log log b))`, and a source universe of
  linear size therefore carries a column of size at least `exp(√(log log b))/C` times its density.
-/

open Finset Filter
open scoped BigOperators Classical Topology

namespace RHTower

open Sieve

noncomputable section

universe u

/-- Past `16` the iterated logarithm is at least one, since `e^e < 16`. -/
theorem one_le_logLog_of_sixteen_le {N : ℕ} (hN : 16 ≤ N) : 1 ≤ logLog N := by
  have hNR : (16 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have h2 : (0.6931471803 : ℝ) < Real.log 2 := Real.log_two_gt_d9
  have h16 : Real.log 16 = 4 * Real.log 2 := by
    rw [show (16 : ℝ) = 2 ^ (4 : ℕ) by norm_num, Real.log_pow]
    push_cast
    ring
  have hmono : Real.log 16 ≤ Real.log N := Real.log_le_log (by norm_num) hNR
  have he : Real.exp 1 < 2.7182818286 := Real.exp_one_lt_d9
  have hexp : Real.exp 1 ≤ Real.log N := by
    rw [h16] at hmono
    nlinarith [hmono, h2, he]
  unfold logLog
  calc (1 : ℝ) = Real.log (Real.exp 1) := by rw [Real.log_exp]
    _ ≤ Real.log (Real.log N) := Real.log_le_log (Real.exp_pos 1) hexp

/-- **Terminal density collapse.**  If the capacity weight
`θ = (log log b + K) · log Z / log b` of an admissible band schedule tends to zero, then the full
physical terminal universe — every reservoir subset of bounded product times every squarefree
three-prime token — has vanishing density in its window. -/
theorem tendsto_wholeAnchorTerminalUniverse_density_zero {A : ℝ} (hA : 0 < A)
    (a b T W Z : ℕ → ℕ) (hT : ∀ n, 1 ≤ T n) (hsq : ∀ n, T n * T n ≤ b n)
    (hbig : ∀ n, 16 ≤ b n) (hW : ∀ n, 2 ≤ W n) (hWZ : ∀ n, W n ≤ Z n)
    (hfloor : ∀ n, A * (logLog (b n) + mertensUpperConst) ≤ Real.log (W n))
    (hθ : Tendsto
      (fun n => (logLog (b n) + mertensUpperConst) * Real.log (Z n) / Real.log (b n))
      atTop (𝓝 0)) :
    Tendsto
      (fun n => ((wholeAnchorTerminalUniverse (a n) (b n) (T n) (W n) (Z n)).card : ℝ) / (b n : ℝ))
      atTop (𝓝 0) := by
  obtain ⟨C, hC, hbound⟩ := exists_wholeAnchorTerminalUniverse_card_le_theta hA
  have hlim : Tendsto (fun n => C *
      ((logLog (b n) + mertensUpperConst) * Real.log (Z n) / Real.log (b n))) atTop (𝓝 0) := by
    simpa using hθ.const_mul C
  refine squeeze_zero (fun n => ?_) (fun n => ?_) hlim
  · positivity
  · have hbR : (16 : ℝ) ≤ (b n : ℝ) := by exact_mod_cast hbig n
    have hbpos : (0 : ℝ) < (b n : ℝ) := by linarith
    have h := hbound (a n) (b n) (T n) (W n) (Z n) (hT n) (hsq n) (hbig n) (hW n) (hWZ n)
      (hfloor n)
    rw [div_le_iff₀ hbpos]
    calc ((wholeAnchorTerminalUniverse (a n) (b n) (T n) (W n) (Z n)).card : ℝ) ≤
        C * ((b n : ℝ) * (logLog (b n) + mertensUpperConst) * Real.log (Z n) /
          Real.log (b n)) := h
      _ = C * ((logLog (b n) + mertensUpperConst) * Real.log (Z n) / Real.log (b n)) *
          (b n : ℝ) := by ring

/-- **Capacity–column composition.**  Any upper bound for the physical terminal universe turns the
finite row-stochastic conservation law into a lower bound for the heaviest column: a kernel from a
source universe into the terminal universe has a terminal carrying at least the source count
divided by that bound. -/
theorem exists_column_ge_of_card_le {a b T W Z : ℕ} {M : ℝ}
    (hM : ((wholeAnchorTerminalUniverse a b T W Z).card : ℝ) ≤ M)
    (hne : (wholeAnchorTerminalUniverse a b T W Z).Nonempty)
    {Anchor : Type u} [Fintype Anchor]
    (P : FiniteRowStochasticKernel Anchor ↥(wholeAnchorTerminalUniverse a b T W Z)) :
    ∃ q : ↥(wholeAnchorTerminalUniverse a b T W Z),
      (Fintype.card Anchor : ℝ) / M ≤ ∑ n : Anchor, P.weight n q := by
  haveI : Nonempty ↥(wholeAnchorTerminalUniverse a b T W Z) := hne.to_subtype
  obtain ⟨q, hq⟩ := P.exists_average_le_column
  refine ⟨q, le_trans ?_ hq⟩
  have hcardpos : (0 : ℝ) < (Fintype.card ↥(wholeAnchorTerminalUniverse a b T W Z) : ℝ) := by
    exact_mod_cast Fintype.card_pos
  have hle : (Fintype.card ↥(wholeAnchorTerminalUniverse a b T W Z) : ℝ) ≤ M := by
    rwa [Fintype.card_coe]
  exact div_le_div_of_nonneg_left (by positivity) hcardpos hle

/-- **Bounded column load forces comparable density.**  Under the band floor
`A · (log log b + K) ≤ log W`, every row-stochastic kernel from a source universe into the physical
terminal universe has a column of size at least the source count divided by the sublinear capacity
`C · b · (log log b + K) · log Z / log b`. -/
theorem exists_column_ge_theta {A : ℝ} (hA : 0 < A) :
    ∃ C : ℝ, 0 < C ∧ ∀ a b T W Z : ℕ, 1 ≤ T → T * T ≤ b → 16 ≤ b → 2 ≤ W → W ≤ Z →
      A * (logLog b + mertensUpperConst) ≤ Real.log W →
      (wholeAnchorTerminalUniverse a b T W Z).Nonempty →
      ∀ (Anchor : Type u) [Fintype Anchor]
        (P : FiniteRowStochasticKernel Anchor ↥(wholeAnchorTerminalUniverse a b T W Z)),
        ∃ q : ↥(wholeAnchorTerminalUniverse a b T W Z),
          (Fintype.card Anchor : ℝ) /
              (C * ((b : ℝ) * (logLog b + mertensUpperConst) * Real.log Z / Real.log b)) ≤
            ∑ n : Anchor, P.weight n q := by
  obtain ⟨C, hC, hbound⟩ := exists_wholeAnchorTerminalUniverse_card_le_theta hA
  refine ⟨C, hC, fun a b T W Z hT hsq hbig hW hWZ hfloor hne Anchor _ P => ?_⟩
  exact exists_column_ge_of_card_le (hbound a b T W Z hT hsq hbig hW hWZ hfloor) hne P

/-- **Proposed-band capacity.**  In the band regime `exp √(log log b) ≤ log W` and
`log Z · (log log b)² ≤ log b` the physical terminal universe is exponentially sparse:
`#𝒯 ≤ C · b · exp(-√(log log b))`. -/
theorem exists_wholeAnchorTerminalUniverse_card_le_proposedBand :
    ∃ C : ℝ, 0 < C ∧ ∀ a b T W Z : ℕ, 1 ≤ T → T * T ≤ b → 16 ≤ b → 2 ≤ W → W ≤ Z →
      Real.exp (Real.sqrt (logLog b)) ≤ Real.log W →
      Real.log Z * (logLog b) ^ 2 ≤ Real.log b →
      ((wholeAnchorTerminalUniverse a b T W Z).card : ℝ) ≤
        C * (b : ℝ) * Real.exp (-Real.sqrt (logLog b)) := by
  obtain ⟨C₁, hC₁, h₁⟩ := exists_wholeAnchorTerminalUniverse_card_le
  refine ⟨C₁ * mertensBandProductConst * (1 + |mertensUpperConst|) ^ 2,
    mul_pos (mul_pos hC₁ mertensBandProductConst_pos) (by positivity),
    fun a b T W Z hT hsq hbig hW hWZ hWfloor hZceil => ?_⟩
  have hbR : (16 : ℝ) ≤ (b : ℝ) := by exact_mod_cast hbig
  have hlogb : (0 : ℝ) < Real.log b := Real.log_pos (by linarith)
  have hL1 : (1 : ℝ) ≤ logLog b := one_le_logLog_of_sixteen_le hbig
  have hLK : (1 / 2 : ℝ) ≤ logLog b + mertensUpperConst :=
    half_le_logLog_add_mertensUpperConst (by omega)
  have hlogW : (0 : ℝ) < Real.log W := Real.log_pos (by exact_mod_cast hW)
  have hlogZ : (0 : ℝ) < Real.log Z :=
    Real.log_pos (by exact_mod_cast lt_of_lt_of_le (by omega : (1 : ℕ) < 2) (le_trans hW hWZ))
  have hexppos : (0 : ℝ) < Real.exp (Real.sqrt (logLog b)) := Real.exp_pos _
  -- the reservoir Euler product in the proposed band
  have hprod := bandPrimes_eulerProduct_le hW hWZ
  have hZle : Real.log Z ≤ Real.log b / (logLog b) ^ 2 := by
    rw [le_div_iff₀ (by nlinarith)]
    exact hZceil
  have hratio : Real.log Z / Real.log W ≤
      (Real.log b / (logLog b) ^ 2) * Real.exp (-Real.sqrt (logLog b)) := by
    have hstep1 : Real.log Z / Real.log W ≤ Real.log Z / Real.exp (Real.sqrt (logLog b)) :=
      div_le_div_of_nonneg_left hlogZ.le hexppos hWfloor
    have hstep2 : Real.log Z / Real.exp (Real.sqrt (logLog b)) ≤
        (Real.log b / (logLog b) ^ 2) / Real.exp (Real.sqrt (logLog b)) := by
      gcongr
    have hstep3 : (Real.log b / (logLog b) ^ 2) / Real.exp (Real.sqrt (logLog b)) =
        (Real.log b / (logLog b) ^ 2) * Real.exp (-Real.sqrt (logLog b)) := by
      rw [Real.exp_neg, div_eq_mul_inv]
    linarith [hstep1, hstep2, hstep3.le, hstep3.ge]
  -- the two-sided comparison of the Mertens shift with the iterated logarithm
  have hLKle : logLog b + mertensUpperConst ≤ (1 + |mertensUpperConst|) * logLog b := by
    have habs : mertensUpperConst ≤ |mertensUpperConst| := le_abs_self _
    nlinarith [abs_nonneg mertensUpperConst]
  have hsqle : (logLog b + mertensUpperConst) ^ 2 ≤
      (1 + |mertensUpperConst|) ^ 2 * (logLog b) ^ 2 := by
    have h0 : (0 : ℝ) ≤ logLog b + mertensUpperConst := by linarith
    calc (logLog b + mertensUpperConst) ^ 2 ≤ ((1 + |mertensUpperConst|) * logLog b) ^ 2 :=
          pow_le_pow_left₀ h0 hLKle 2
      _ = (1 + |mertensUpperConst|) ^ 2 * (logLog b) ^ 2 := by ring
  have hquot : (logLog b + mertensUpperConst) ^ 2 / (logLog b) ^ 2 ≤
      (1 + |mertensUpperConst|) ^ 2 := by
    rw [div_le_iff₀ (by nlinarith)]
    exact hsqle
  -- assemble
  have hfrontpos : (0 : ℝ) ≤ C₁ * ((b : ℝ) * (logLog b + mertensUpperConst) ^ 2 / Real.log b) := by
    apply mul_nonneg hC₁.le
    apply div_nonneg _ hlogb.le
    apply mul_nonneg (by positivity)
    positivity
  have hchain : ((wholeAnchorTerminalUniverse a b T W Z).card : ℝ) ≤
      C₁ * ((b : ℝ) * (logLog b + mertensUpperConst) ^ 2 / Real.log b) *
        (mertensBandProductConst *
          ((Real.log b / (logLog b) ^ 2) * Real.exp (-Real.sqrt (logLog b)))) := by
    refine le_trans (h₁ a b T W Z hT hsq hbig) ?_
    apply mul_le_mul_of_nonneg_left _ hfrontpos
    refine le_trans hprod ?_
    exact mul_le_mul_of_nonneg_left hratio mertensBandProductConst_pos.le
  have hEpos : (0 : ℝ) < Real.exp (-Real.sqrt (logLog b)) := Real.exp_pos _
  have hL2pos : (0 : ℝ) < (logLog b) ^ 2 := by nlinarith
  have hrewrite : C₁ * ((b : ℝ) * (logLog b + mertensUpperConst) ^ 2 / Real.log b) *
      (mertensBandProductConst *
        ((Real.log b / (logLog b) ^ 2) * Real.exp (-Real.sqrt (logLog b)))) =
      C₁ * mertensBandProductConst * (b : ℝ) * Real.exp (-Real.sqrt (logLog b)) *
        ((logLog b + mertensUpperConst) ^ 2 / (logLog b) ^ 2) := by
    field_simp
  have hbase : (0 : ℝ) ≤ C₁ * mertensBandProductConst * (b : ℝ) *
      Real.exp (-Real.sqrt (logLog b)) := by
    apply mul_nonneg _ hEpos.le
    apply mul_nonneg _ (Nat.cast_nonneg b)
    exact mul_nonneg hC₁.le mertensBandProductConst_pos.le
  calc ((wholeAnchorTerminalUniverse a b T W Z).card : ℝ) ≤
      C₁ * ((b : ℝ) * (logLog b + mertensUpperConst) ^ 2 / Real.log b) *
        (mertensBandProductConst *
          ((Real.log b / (logLog b) ^ 2) * Real.exp (-Real.sqrt (logLog b)))) := hchain
    _ = C₁ * mertensBandProductConst * (b : ℝ) * Real.exp (-Real.sqrt (logLog b)) *
        ((logLog b + mertensUpperConst) ^ 2 / (logLog b) ^ 2) := hrewrite
    _ ≤ C₁ * mertensBandProductConst * (b : ℝ) * Real.exp (-Real.sqrt (logLog b)) *
        (1 + |mertensUpperConst|) ^ 2 := mul_le_mul_of_nonneg_left hquot hbase
    _ = C₁ * mertensBandProductConst * (1 + |mertensUpperConst|) ^ 2 * (b : ℝ) *
        Real.exp (-Real.sqrt (logLog b)) := by ring

/-- **Proposed-band column load.**  In the same band regime a row-stochastic kernel from a source
universe into the physical terminal universe carries a column at least
`exp(√(log log b))/C` times the source density: full-band whole-anchor allocation cannot be a
bounded-load relation for a source universe of linear size. -/
theorem exists_column_ge_proposedBand :
    ∃ C : ℝ, 0 < C ∧ ∀ a b T W Z : ℕ, 1 ≤ T → T * T ≤ b → 16 ≤ b → 2 ≤ W → W ≤ Z →
      Real.exp (Real.sqrt (logLog b)) ≤ Real.log W →
      Real.log Z * (logLog b) ^ 2 ≤ Real.log b →
      (wholeAnchorTerminalUniverse a b T W Z).Nonempty →
      ∀ (Anchor : Type u) [Fintype Anchor]
        (P : FiniteRowStochasticKernel Anchor ↥(wholeAnchorTerminalUniverse a b T W Z)),
        ∃ q : ↥(wholeAnchorTerminalUniverse a b T W Z),
          (Fintype.card Anchor : ℝ) / (b : ℝ) *
              (Real.exp (Real.sqrt (logLog b)) / C) ≤ ∑ n : Anchor, P.weight n q := by
  obtain ⟨C, hC, hbound⟩ := exists_wholeAnchorTerminalUniverse_card_le_proposedBand
  refine ⟨C, hC, fun a b T W Z hT hsq hbig hW hWZ hWfloor hZceil hne Anchor _ P => ?_⟩
  obtain ⟨q, hq⟩ :=
    exists_column_ge_of_card_le (hbound a b T W Z hT hsq hbig hW hWZ hWfloor hZceil) hne P
  refine ⟨q, le_trans (le_of_eq ?_) hq⟩
  have hbR : (16 : ℝ) ≤ (b : ℝ) := by exact_mod_cast hbig
  have hbne : ((b : ℝ)) ≠ 0 := ne_of_gt (by linarith)
  have hCne : C ≠ 0 := ne_of_gt hC
  have hexpne : Real.exp (Real.sqrt (logLog b)) ≠ 0 := ne_of_gt (Real.exp_pos _)
  rw [Real.exp_neg]
  field_simp

end

end RHTower
