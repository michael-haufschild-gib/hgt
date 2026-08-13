import GaloisForLFunctions.RHTower.MobiusWholeAnchorCapacityDisplacement
import GaloisForLFunctions.RHTower.Sieve.AlmostPrimeGlobalCount

/-!
# Global terminal capacity of the full-allocation whole-anchor relation

The full physical terminal universe of the whole-anchor Route E relation — every window integer
of the form `t_R · m` with `R` a reservoir subset of the prime band `(W, Z]` of bounded product
and `m` a squarefree three-prime token — is counted by granting every subset and every cofactor:
the count splits through the reservoir label, each label contributes a global order-three
Hardy--Ramanujan window count, and the label sum is the reservoir Euler product, which the sharp
Mertens second theorem bounds by `log Z / log W`.  Together with the finite row-stochastic
conservation law this closes the full-allocation no-go: bounded column load forces physical
terminal density comparable to source density.
-/

open Finset
open scoped BigOperators Classical

namespace RHTower

open Sieve

noncomputable section

/-- The reservoir prime band `(W, Z]`. -/
def wholeAnchorBandPrimes (W Z : ℕ) : Finset ℕ :=
  (Finset.Ioc W Z).filter Nat.Prime

/-- Full physical terminal universe: all window integers `t_R · m` over reservoir subsets `R`
of band product at most `T` and squarefree three-prime tokens `m`. -/
def wholeAnchorTerminalUniverse (a b T W Z : ℕ) : Finset ℕ :=
  (Finset.Icc a b).filter fun q =>
    ∃ R ∈ (wholeAnchorBandPrimes W Z).powerset, (∏ p ∈ R, p) ≤ T ∧
      ∃ m : ℕ, Squarefree m ∧ m.primeFactors.card = 3 ∧ q = (∏ p ∈ R, p) * m

/-- Small-argument vanishing of the order-three count. -/
theorem squarefreeOmegaCount_three_eq_zero_of_le_one {M : ℕ} (hM : M ≤ 1) :
    squarefreeOmegaCount 3 M = 0 := by
  unfold squarefreeOmegaCount
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro m hm
  rw [Finset.mem_Icc] at hm
  have hm1 : m = 1 := by omega
  rintro ⟨-, hcard⟩
  rw [hm1] at hcard
  simp at hcard

/-- The window integers with a fixed reservoir label inject into the order-three count of the
divided window. -/
theorem card_window_fixed_label_le (a b t : ℕ) (ht : 1 ≤ t) :
    (((Finset.Icc a b).filter fun q =>
        ∃ m : ℕ, Squarefree m ∧ m.primeFactors.card = 3 ∧ q = t * m).card : ℕ) ≤
      squarefreeOmegaCount 3 (b / t) := by
  classical
  unfold squarefreeOmegaCount
  apply Finset.card_le_card_of_injOn (fun q => q / t)
  · intro q hq
    simp only [Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_Icc] at hq
    obtain ⟨⟨haq, hqb⟩, m, hmsf, hmcard, hqm⟩ := hq
    simp only [Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_Icc]
    have hqt : q / t = m := by
      rw [hqm, Nat.mul_div_cancel_left m (by omega)]
    rw [hqt]
    have hm1 : 1 ≤ m := by
      rcases Nat.eq_zero_or_pos m with rfl | h
      · exfalso
        simp at hmcard
      · exact h
    refine ⟨⟨hm1, ?_⟩, hmsf, hmcard⟩
    calc m = t * m / t := by rw [Nat.mul_div_cancel_left m (by omega)]
      _ ≤ b / t := by
          apply Nat.div_le_div_right
          rw [← hqm]
          exact hqb
  · intro q hq r hr hqr
    simp only [Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_Icc] at hq hr
    obtain ⟨-, mq, -, -, hq2⟩ := hq
    obtain ⟨-, mr, -, -, hr2⟩ := hr
    have hqr' : q / t = r / t := hqr
    have hq3 : q = t * (q / t) := by
      conv_lhs => rw [hq2]
      rw [hq2, Nat.mul_div_cancel_left mq (by omega)]
    have hr3 : r = t * (r / t) := by
      conv_lhs => rw [hr2]
      rw [hr2, Nat.mul_div_cancel_left mr (by omega)]
    calc q = t * (q / t) := hq3
      _ = t * (r / t) := by rw [hqr']
      _ = r := hr3.symm

/-- The terminal universe splits through the reservoir label. -/
theorem wholeAnchorTerminalUniverse_card_le_sum (a b T W Z : ℕ) :
    (wholeAnchorTerminalUniverse a b T W Z).card ≤
      ∑ R ∈ ((wholeAnchorBandPrimes W Z).powerset).filter
          (fun R => (∏ p ∈ R, p) ≤ T),
        squarefreeOmegaCount 3 (b / (∏ p ∈ R, p)) := by
  classical
  have hsplit : wholeAnchorTerminalUniverse a b T W Z ⊆
      (((wholeAnchorBandPrimes W Z).powerset).filter
          (fun R => (∏ p ∈ R, p) ≤ T)).biUnion fun R =>
        (Finset.Icc a b).filter fun q =>
          ∃ m : ℕ, Squarefree m ∧ m.primeFactors.card = 3 ∧ q = (∏ p ∈ R, p) * m := by
    intro q hq
    rw [wholeAnchorTerminalUniverse, Finset.mem_filter] at hq
    obtain ⟨hqIcc, R, hR, hRT, m, hmsf, hmcard, hqm⟩ := hq
    rw [Finset.mem_biUnion]
    refine ⟨R, ?_, ?_⟩
    · rw [Finset.mem_filter]
      exact ⟨hR, hRT⟩
    · rw [Finset.mem_filter]
      exact ⟨hqIcc, m, hmsf, hmcard, hqm⟩
  calc (wholeAnchorTerminalUniverse a b T W Z).card ≤
      ((((wholeAnchorBandPrimes W Z).powerset).filter
          (fun R => (∏ p ∈ R, p) ≤ T)).biUnion fun R =>
        (Finset.Icc a b).filter fun q =>
          ∃ m : ℕ, Squarefree m ∧ m.primeFactors.card = 3 ∧
            q = (∏ p ∈ R, p) * m).card :=
        Finset.card_le_card hsplit
    _ ≤ ∑ R ∈ ((wholeAnchorBandPrimes W Z).powerset).filter
          (fun R => (∏ p ∈ R, p) ≤ T),
        ((Finset.Icc a b).filter fun q =>
          ∃ m : ℕ, Squarefree m ∧ m.primeFactors.card = 3 ∧
            q = (∏ p ∈ R, p) * m).card := Finset.card_biUnion_le
    _ ≤ ∑ R ∈ ((wholeAnchorBandPrimes W Z).powerset).filter
          (fun R => (∏ p ∈ R, p) ≤ T),
        squarefreeOmegaCount 3 (b / (∏ p ∈ R, p)) := by
        refine Finset.sum_le_sum fun R hR => ?_
        have hpos : 1 ≤ ∏ p ∈ R, p := by
          apply Finset.one_le_prod'
          intro p hp
          rw [Finset.mem_filter, Finset.mem_powerset] at hR
          have hpband := hR.1 hp
          rw [wholeAnchorBandPrimes, Finset.mem_filter] at hpband
          exact hpband.2.one_lt.le
        exact card_window_fixed_label_le a b _ hpos

/-- Logarithmic stability of the bounded-label division: with `t² ≤ b` past the threshold, the
divided window keeps a quarter of `log b`. -/
theorem log_natDiv_ge_of_sq_le {b t : ℕ} (ht : 1 ≤ t) (hsq : t * t ≤ b) (hbig : 16 ≤ b) :
    (1 / 4 : ℝ) * Real.log b ≤ Real.log ((b / t : ℕ) : ℝ) := by
  have hbR : (16 : ℝ) ≤ (b : ℝ) := by exact_mod_cast hbig
  have hlogb : 0 < Real.log b := Real.log_pos (by linarith)
  have htR : (1 : ℝ) ≤ (t : ℝ) := by exact_mod_cast ht
  -- `log t ≤ log b / 2`
  have hlogt : Real.log t ≤ Real.log b / 2 := by
    rw [le_div_iff₀ (by norm_num : (0:ℝ) < 2)]
    have hsqR : (t : ℝ) * t ≤ (b : ℝ) := by exact_mod_cast hsq
    have := Real.log_le_log (by positivity : (0:ℝ) < (t:ℝ) * t) hsqR
    rw [Real.log_mul (by positivity) (by positivity)] at this
    linarith
  -- the divided window dominates `b / (2t)`
  have h2t : (2 : ℝ) ≤ (b : ℝ) / t := by
    rw [le_div_iff₀ (by positivity : (0:ℝ) < (t:ℝ))]
    have h2tb : 2 * t ≤ b := by
      rcases Nat.lt_or_ge t 2 with h1 | h2
      · have : t = 1 := by omega
        omega
      · calc 2 * t ≤ t * t := Nat.mul_le_mul_right t h2
          _ ≤ b := hsq
    exact_mod_cast h2tb
  have hdivge : (b : ℝ) / (2 * t) ≤ ((b / t : ℕ) : ℝ) := by
    have hone := cast_natDiv_ge_sub_one b t (by omega)
    have hhalf : (b : ℝ) / (2 * t) = ((b : ℝ) / t) / 2 := by
      rw [div_div]
      ring_nf
    rw [hhalf]
    linarith
  have hdivpos : (0 : ℝ) < (b : ℝ) / (2 * t) := by positivity
  have hlogdiv := Real.log_le_log hdivpos hdivge
  have hlogsplit : Real.log ((b : ℝ) / (2 * t)) =
      Real.log b - Real.log 2 - Real.log t := by
    rw [Real.log_div (by positivity) (by positivity), Real.log_mul (by norm_num)
      (by positivity : ((t:ℝ)) ≠ 0)]
    ring
  have hlog2 : Real.log 2 ≤ Real.log b / 4 := by
    rw [le_div_iff₀ (by norm_num : (0:ℝ) < 4)]
    have h16 : ((2 : ℝ)) ^ (4 : ℕ) ≤ (b : ℝ) := by
      norm_num
      linarith
    have := Real.log_le_log (by positivity) h16
    rw [Real.log_pow] at this
    push_cast at this
    linarith
  calc (1 / 4 : ℝ) * Real.log b =
      Real.log b - Real.log b / 4 - Real.log b / 2 := by ring
    _ ≤ Real.log b - Real.log 2 - Real.log t := by linarith
    _ = Real.log ((b : ℝ) / (2 * t)) := hlogsplit.symm
    _ ≤ Real.log ((b / t : ℕ) : ℝ) := hlogdiv

/-- Sharp Mertens lower bound. -/
theorem logLog_sub_le_mertensS {N : ℕ} (hN : 2 ≤ N) :
    logLog N + meisselMertensConst -
        (2 * mertensFirstConst + 1 / 2) / Real.log 2 ≤ mertensS N := by
  have h := abs_mertensS_sub_logLog_sub_const_le hN
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hlogN : Real.log 2 ≤ Real.log N := by
    apply Real.log_le_log (by norm_num)
    exact_mod_cast hN
  have hnum : (0 : ℝ) ≤ 2 * mertensFirstConst + 1 / 2 := by
    have hpos : (0 : ℝ) < mertensFirstConst :=
      lt_of_lt_of_le (Real.log_pos (by norm_num : (1 : ℝ) < 4)) (le_max_left _ _)
    linarith
  have hquot : (2 * mertensFirstConst + 1 / 2) / Real.log N ≤
      (2 * mertensFirstConst + 1 / 2) / Real.log 2 :=
    div_le_div_of_nonneg_left hnum hlog2 hlogN
  have habs := (abs_le.mp h).1
  linarith

/-- The reservoir band reciprocal sum is the Mertens increment. -/
theorem sum_one_div_bandPrimes {W Z : ℕ} (hWZ : W ≤ Z) :
    ∑ p ∈ wholeAnchorBandPrimes W Z, 1 / (p : ℝ) = mertensS Z - mertensS W := by
  have hsub : Nat.primesLE W ⊆ Nat.primesLE Z := by
    intro p hp
    rw [Nat.mem_primesLE] at hp ⊢
    exact ⟨le_trans hp.1 hWZ, hp.2⟩
  have hband : wholeAnchorBandPrimes W Z = Nat.primesLE Z \ Nat.primesLE W := by
    ext p
    rw [wholeAnchorBandPrimes, Finset.mem_filter, Finset.mem_Ioc, Finset.mem_sdiff,
      Nat.mem_primesLE, Nat.mem_primesLE]
    constructor
    · rintro ⟨⟨hWp, hpZ⟩, hp⟩
      exact ⟨⟨hpZ, hp⟩, fun hcon => by omega⟩
    · rintro ⟨⟨hpZ, hp⟩, hnot⟩
      refine ⟨⟨?_, hpZ⟩, hp⟩
      by_contra hcon
      exact hnot ⟨by omega, hp⟩
  rw [hband, Finset.sum_sdiff_eq_sub hsub, mertensS, mertensS]

/-- Constant of the Mertens band Euler product. -/
noncomputable def mertensBandProductConst : ℝ :=
  Real.exp (2 * ((2 * mertensFirstConst + 1 / 2) / Real.log 2))

theorem mertensBandProductConst_pos : 0 < mertensBandProductConst := Real.exp_pos _

/-- **Mertens band product bound**: `∏_{W<p≤Z} (1 + 1/p) ≤ K · log Z / log W`. -/
theorem bandPrimes_eulerProduct_le {W Z : ℕ} (hW : 2 ≤ W) (hWZ : W ≤ Z) :
    ∏ p ∈ wholeAnchorBandPrimes W Z, (1 + 1 / (p : ℝ)) ≤
      mertensBandProductConst * (Real.log Z / Real.log W) := by
  have hZ2 : 2 ≤ Z := le_trans hW hWZ
  have hlogW : (0 : ℝ) < Real.log W := Real.log_pos (by exact_mod_cast hW)
  have hlogZ : (0 : ℝ) < Real.log Z := Real.log_pos (by exact_mod_cast hZ2)
  have hexp : ∏ p ∈ wholeAnchorBandPrimes W Z, (1 + 1 / (p : ℝ)) ≤
      Real.exp (∑ p ∈ wholeAnchorBandPrimes W Z, 1 / (p : ℝ)) := by
    rw [Real.exp_sum]
    apply Finset.prod_le_prod
    · intro p hp
      have : (0 : ℝ) ≤ 1 / (p : ℝ) := by positivity
      linarith
    · intro p hp
      calc 1 + 1 / (p : ℝ) = 1 / (p : ℝ) + 1 := by ring
        _ ≤ Real.exp (1 / (p : ℝ)) := Real.add_one_le_exp _
  rw [sum_one_div_bandPrimes hWZ] at hexp
  set E : ℝ := (2 * mertensFirstConst + 1 / 2) / Real.log 2 with hE
  have hupper := mertensS_le_logLog_add hZ2
  have hlower := logLog_sub_le_mertensS hW
  have hEnonneg : (0 : ℝ) ≤ E := by
    rw [hE]
    have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
    have hpos : (0 : ℝ) < mertensFirstConst :=
      lt_of_lt_of_le (Real.log_pos (by norm_num : (1 : ℝ) < 4)) (le_max_left _ _)
    positivity
  have hdiff : mertensS Z - mertensS W ≤ logLog Z - logLog W + 2 * E := by
    have hupper' : mertensS Z ≤ logLog Z + mertensUpperConst := hupper
    rw [mertensUpperConst] at hupper'
    linarith
  calc ∏ p ∈ wholeAnchorBandPrimes W Z, (1 + 1 / (p : ℝ)) ≤
      Real.exp (mertensS Z - mertensS W) := hexp
    _ ≤ Real.exp (logLog Z - logLog W + 2 * E) := Real.exp_le_exp.mpr hdiff
    _ = Real.exp (2 * E) * (Real.exp (logLog Z) / Real.exp (logLog W)) := by
        rw [← Real.exp_sub, ← Real.exp_add]
        ring_nf
    _ = mertensBandProductConst * (Real.log Z / Real.log W) := by
        rw [mertensBandProductConst, ← hE]
        congr 1
        unfold logLog
        rw [Real.exp_log hlogZ, Real.exp_log hlogW]

/-- **Global terminal capacity, Euler-product form.**  Granting every reservoir subset of
bounded product and every squarefree three-prime cofactor, the terminal universe obeys the
Hardy--Ramanujan window bound times the full reservoir Euler product. -/
theorem exists_wholeAnchorTerminalUniverse_card_le :
    ∃ C : ℝ, 0 < C ∧ ∀ a b T W Z : ℕ, 1 ≤ T → T * T ≤ b → 16 ≤ b →
      ((wholeAnchorTerminalUniverse a b T W Z).card : ℝ) ≤
        C * ((b : ℝ) * (logLog b + mertensUpperConst) ^ 2 / Real.log b) *
          ∏ p ∈ wholeAnchorBandPrimes W Z, (1 + 1 / (p : ℝ)) := by
  obtain ⟨C₃, hC₃, h₃⟩ := exists_squarefreeOmegaCount_three_bound
  refine ⟨4 * C₃, by positivity, fun a b T W Z hT hsq hbig => ?_⟩
  have hbR : (16 : ℝ) ≤ (b : ℝ) := by exact_mod_cast hbig
  have hlogb : (0 : ℝ) < Real.log b := Real.log_pos (by linarith)
  have hLK : (1 / 2 : ℝ) ≤ logLog b + mertensUpperConst :=
    half_le_logLog_add_mertensUpperConst (by omega)
  -- the per-label bound
  have hlabel : ∀ R ∈ ((wholeAnchorBandPrimes W Z).powerset).filter
      (fun R => (∏ p ∈ R, p) ≤ T),
      (squarefreeOmegaCount 3 (b / (∏ p ∈ R, p)) : ℝ) ≤
        4 * C₃ * ((b : ℝ) * (logLog b + mertensUpperConst) ^ 2 / Real.log b) *
          ∏ p ∈ R, (1 / (p : ℝ)) := by
    intro R hR
    rw [Finset.mem_filter, Finset.mem_powerset] at hR
    obtain ⟨hRsub, hRT⟩ := hR
    set t : ℕ := ∏ p ∈ R, p with ht
    have htpos : 1 ≤ t := by
      rw [ht]
      apply Finset.one_le_prod'
      intro p hp
      have hpband := hRsub hp
      rw [wholeAnchorBandPrimes, Finset.mem_filter] at hpband
      exact hpband.2.one_lt.le
    have htsq : t * t ≤ b := le_trans (Nat.mul_le_mul hRT hRT) hsq
    have hprodinv : ∏ p ∈ R, (1 / (p : ℝ)) = 1 / (t : ℝ) := by
      rw [ht]
      push_cast
      rw [one_div, ← Finset.prod_inv_distrib]
      exact Finset.prod_congr rfl fun p _ => one_div _
    rcases Nat.lt_or_ge (b / t) 2 with hdivsmall | hdiv2
    · -- degenerate label: the divided window is empty of three-prime tokens
      have hzero : squarefreeOmegaCount 3 (b / t) = 0 :=
        squarefreeOmegaCount_three_eq_zero_of_le_one (by omega)
      rw [hzero]
      have hrhs : (0 : ℝ) ≤ 4 * C₃ *
          ((b : ℝ) * (logLog b + mertensUpperConst) ^ 2 / Real.log b) *
          ∏ p ∈ R, (1 / (p : ℝ)) := by
        apply mul_nonneg
        apply mul_nonneg (by positivity)
        · apply div_nonneg _ hlogb.le
          apply mul_nonneg (by positivity)
          positivity
        · apply Finset.prod_nonneg
          intro p hp
          positivity
      exact_mod_cast hrhs
    · -- the Hardy--Ramanujan regime
      have hb₃ := h₃ (b / t) hdiv2
      have hcast : ((b / t : ℕ) : ℝ) ≤ (b : ℝ) / t := Nat.cast_div_le
      have hloglow := log_natDiv_ge_of_sq_le htpos htsq hbig
      have hlogdivpos : (0 : ℝ) < Real.log ((b / t : ℕ) : ℝ) := by
        apply Real.log_pos
        have : (2 : ℝ) ≤ ((b / t : ℕ) : ℝ) := by exact_mod_cast hdiv2
        linarith
      have hLmono : logLog (b / t) + mertensUpperConst ≤ logLog b + mertensUpperConst := by
        have := logLog_natDiv_le (N := b) (p := t) hdiv2
        linarith
      have hLdivpos : (0 : ℝ) ≤ logLog (b / t) + mertensUpperConst := by
        have := half_le_logLog_add_mertensUpperConst hdiv2
        linarith
      have hpowmono : (logLog (b / t) + mertensUpperConst) ^ 2 ≤
          (logLog b + mertensUpperConst) ^ 2 :=
        pow_le_pow_left₀ hLdivpos hLmono 2
      calc (squarefreeOmegaCount 3 (b / t) : ℝ) ≤
          C₃ * (((b / t : ℕ) : ℝ) * (logLog (b / t) + mertensUpperConst) ^ 2 /
            Real.log ((b / t : ℕ) : ℝ)) := hb₃
        _ ≤ C₃ * (((b : ℝ) / t) * (logLog b + mertensUpperConst) ^ 2 /
            ((1 / 4 : ℝ) * Real.log b)) := by
            apply mul_le_mul_of_nonneg_left _ hC₃.le
            calc ((b / t : ℕ) : ℝ) * (logLog (b / t) + mertensUpperConst) ^ 2 /
                Real.log ((b / t : ℕ) : ℝ) ≤
                ((b / t : ℕ) : ℝ) * (logLog (b / t) + mertensUpperConst) ^ 2 /
                  ((1 / 4 : ℝ) * Real.log b) :=
                  div_le_div_of_nonneg_left (by positivity) (by positivity) hloglow
              _ ≤ ((b : ℝ) / t) * (logLog b + mertensUpperConst) ^ 2 /
                  ((1 / 4 : ℝ) * Real.log b) := by
                  gcongr
        _ = 4 * C₃ * ((b : ℝ) * (logLog b + mertensUpperConst) ^ 2 / Real.log b) *
            (1 / (t : ℝ)) := by
            have htne : ((t : ℝ)) ≠ 0 := by positivity
            field_simp
        _ = 4 * C₃ * ((b : ℝ) * (logLog b + mertensUpperConst) ^ 2 / Real.log b) *
            ∏ p ∈ R, (1 / (p : ℝ)) := by rw [hprodinv]
  -- assemble through the label sum and the full Euler product
  have hcount := wholeAnchorTerminalUniverse_card_le_sum a b T W Z
  have hcountR : ((wholeAnchorTerminalUniverse a b T W Z).card : ℝ) ≤
      ∑ R ∈ ((wholeAnchorBandPrimes W Z).powerset).filter
          (fun R => (∏ p ∈ R, p) ≤ T),
        (squarefreeOmegaCount 3 (b / (∏ p ∈ R, p)) : ℝ) := by
    exact_mod_cast hcount
  have hfront : (0 : ℝ) ≤ 4 * C₃ *
      ((b : ℝ) * (logLog b + mertensUpperConst) ^ 2 / Real.log b) := by positivity
  calc ((wholeAnchorTerminalUniverse a b T W Z).card : ℝ) ≤
      ∑ R ∈ ((wholeAnchorBandPrimes W Z).powerset).filter
          (fun R => (∏ p ∈ R, p) ≤ T),
        (squarefreeOmegaCount 3 (b / (∏ p ∈ R, p)) : ℝ) := hcountR
    _ ≤ ∑ R ∈ ((wholeAnchorBandPrimes W Z).powerset).filter
          (fun R => (∏ p ∈ R, p) ≤ T),
        4 * C₃ * ((b : ℝ) * (logLog b + mertensUpperConst) ^ 2 / Real.log b) *
          ∏ p ∈ R, (1 / (p : ℝ)) := Finset.sum_le_sum hlabel
    _ = 4 * C₃ * ((b : ℝ) * (logLog b + mertensUpperConst) ^ 2 / Real.log b) *
        ∑ R ∈ ((wholeAnchorBandPrimes W Z).powerset).filter
          (fun R => (∏ p ∈ R, p) ≤ T),
          ∏ p ∈ R, (1 / (p : ℝ)) := by rw [Finset.mul_sum]
    _ ≤ 4 * C₃ * ((b : ℝ) * (logLog b + mertensUpperConst) ^ 2 / Real.log b) *
        ∑ R ∈ (wholeAnchorBandPrimes W Z).powerset,
          ∏ p ∈ R, (1 / (p : ℝ)) := by
        apply mul_le_mul_of_nonneg_left _ hfront
        apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        intro R _ _
        apply Finset.prod_nonneg
        intro p _
        positivity
    _ = 4 * C₃ * ((b : ℝ) * (logLog b + mertensUpperConst) ^ 2 / Real.log b) *
        ∏ p ∈ wholeAnchorBandPrimes W Z, (1 + 1 / (p : ℝ)) := by
        rw [wholeAnchor_fullReservoirMass_eq_eulerProduct]

/-- **Global terminal capacity, `θ` form.**  Under the band floor `A·L ≤ log W` the terminal
universe is sublinear with the exact `θ_X = L · log Z / log X` weight of the whole-anchor
relation: bounded column load forces terminal density comparable to source density. -/
theorem exists_wholeAnchorTerminalUniverse_card_le_theta {A : ℝ} (hA : 0 < A) :
    ∃ C : ℝ, 0 < C ∧ ∀ a b T W Z : ℕ, 1 ≤ T → T * T ≤ b → 16 ≤ b → 2 ≤ W → W ≤ Z →
      A * (logLog b + mertensUpperConst) ≤ Real.log W →
      ((wholeAnchorTerminalUniverse a b T W Z).card : ℝ) ≤
        C * ((b : ℝ) * (logLog b + mertensUpperConst) * Real.log Z / Real.log b) := by
  obtain ⟨C₁, hC₁, h₁⟩ := exists_wholeAnchorTerminalUniverse_card_le
  refine ⟨C₁ * mertensBandProductConst / A, by
    have := mertensBandProductConst_pos
    positivity, fun a b T W Z hT hsq hbig hW hWZ hfloor => ?_⟩
  have hbR : (16 : ℝ) ≤ (b : ℝ) := by exact_mod_cast hbig
  have hlogb : (0 : ℝ) < Real.log b := Real.log_pos (by linarith)
  have hLK : (1 / 2 : ℝ) ≤ logLog b + mertensUpperConst :=
    half_le_logLog_add_mertensUpperConst (by omega)
  have hlogW : (0 : ℝ) < Real.log W := Real.log_pos (by exact_mod_cast hW)
  have hlogZ : (0 : ℝ) < Real.log Z :=
    Real.log_pos (by exact_mod_cast lt_of_lt_of_le (by omega : (1:ℕ) < 2) (le_trans hW hWZ))
  have hbound := h₁ a b T W Z hT hsq hbig
  have hprod := bandPrimes_eulerProduct_le hW hWZ
  have hratio : Real.log Z / Real.log W ≤
      Real.log Z / (A * (logLog b + mertensUpperConst)) :=
    div_le_div_of_nonneg_left hlogZ.le (by positivity) hfloor
  calc ((wholeAnchorTerminalUniverse a b T W Z).card : ℝ) ≤
      C₁ * ((b : ℝ) * (logLog b + mertensUpperConst) ^ 2 / Real.log b) *
        ∏ p ∈ wholeAnchorBandPrimes W Z, (1 + 1 / (p : ℝ)) := hbound
    _ ≤ C₁ * ((b : ℝ) * (logLog b + mertensUpperConst) ^ 2 / Real.log b) *
        (mertensBandProductConst * (Real.log Z / Real.log W)) := by
        apply mul_le_mul_of_nonneg_left hprod
        positivity
    _ ≤ C₁ * ((b : ℝ) * (logLog b + mertensUpperConst) ^ 2 / Real.log b) *
        (mertensBandProductConst *
          (Real.log Z / (A * (logLog b + mertensUpperConst)))) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        apply mul_le_mul_of_nonneg_left hratio mertensBandProductConst_pos.le
    _ = C₁ * mertensBandProductConst / A *
        ((b : ℝ) * (logLog b + mertensUpperConst) * Real.log Z / Real.log b) := by
        have hLKne : (logLog b + mertensUpperConst) ≠ 0 := by linarith
        field_simp

end

end RHTower
