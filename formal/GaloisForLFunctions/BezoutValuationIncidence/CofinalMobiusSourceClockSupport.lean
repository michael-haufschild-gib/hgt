import GaloisForLFunctions.BezoutValuationIncidence.FermiCellJumpReciprocityAndPronicTailBridge
import GaloisForLFunctions.BezoutValuationIncidence.QuotientDualOctaveReciprocityAndValuationSwitching
import GaloisForLFunctions.BezoutValuationIncidence.TranslatedWindowStrideAnnihilationAndLcmReturnObservability
import Mathlib.Data.Nat.Prime.Infinite

/-!
# Exact cofinal Möbius source visibility clocks

On the literal horizon `(B+2)N`, a nonzero source has visibility clock below
`B+2`. Every positive clock below that ratio realizes either unit sign at
arbitrarily large cutoffs. The exact clock fibre is parametrized by squarefree
multiples of the clock's radical.

The proof uses the existing full radical, first-octave reciprocity, and
unbounded primes. These support the full source/clock law; no frequency
conclusion is asserted here.
-/

open Finset ArithmeticFunction
open RHTower RHTower.Sieve
open scoped BigOperators ArithmeticFunction.Moebius

namespace GaloisForLFunctions.BezoutValuationIncidence

set_option autoImplicit false

private theorem full_radical_pos (n : ℕ) : 0 < primeRadical n :=
  Finset.prod_pos fun _ hp => (Nat.mem_primeFactors.mp hp).1.pos

private theorem full_radical_dvd (n : ℕ) : primeRadical n ∣ n :=
  Nat.prod_primeFactors_dvd n

private theorem full_radical_clock (n : ℕ) :
    lagVisibilityClock n * primeRadical n = n :=
  Nat.div_mul_cancel (Nat.prod_primeFactors_dvd n)

private theorem squarefree_dvd_full_radical {n d : ℕ} (hn : n ≠ 0)
    (hd : Squarefree d) : d ∣ primeRadical n ↔ d ∣ n := by
  rw [← Nat.prod_primeFactors_of_squarefree hd,
    Nat.prod_primeFactors_dvd_iff (full_radical_pos n).ne',
    Nat.prod_primeFactors_dvd_iff hn]
  simp only [primeRadical, Nat.primeFactors_prod_primeFactors]

private theorem source_full_radical (N : ℕ) {n : ℕ} (hn : n ≠ 0) :
    sieveSeq N moebiusReal (primeRadical n) = sieveSeq N moebiusReal n := by
  unfold sieveSeq
  rw [Finset.sum_filter, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro d _
  by_cases hd : Squarefree d
  · simp only [squarefree_dvd_full_radical hn hd]
  · simp only [moebiusReal, ArithmeticFunction.moebius_eq_zero_of_not_squarefree hd,
      Int.cast_zero, ite_self]

private theorem full_radical_gt_one {n : ℕ} (hn : 1 < n) : 1 < primeRadical n := by
  obtain ⟨p, hp⟩ := Nat.nonempty_primeFactors.mpr hn
  have hpP := (Nat.mem_primeFactors.mp hp).1
  have hpr : p ∣ primeRadical n :=
    (squarefree_dvd_full_radical (by omega) hpP.squarefree).mpr
      (Nat.mem_primeFactors.mp hp).2.1
  exact hpP.one_lt.trans_le (Nat.le_of_dvd (full_radical_pos n) hpr)

private theorem source_zero_or_clock_lt {A N n : ℕ} (hA : 2 ≤ A)
    (hn : 1 ≤ n) (hhi : n ≤ A * N) :
    sieveSeq N moebiusReal n = 0 ∨ lagVisibilityClock n < A := by
  by_cases hn1 : n = 1
  · right
    subst n
    simpa [lagVisibilityClock] using (show 1 < A by omega)
  · by_cases hR : primeRadical n ≤ N
    · left
      rw [← source_full_radical N (by omega),
        sieveSeq_moebiusReal_eq_ite_of_le (by exact full_radical_pos n) hR,
        if_neg (by have := full_radical_gt_one (by omega : 1 < n); omega)]
    · right
      have hc : 1 ≤ lagVisibilityClock n := by
        have hmul := full_radical_clock n
        nlinarith
      have hmul := full_radical_clock n
      nlinarith

private theorem full_radical_mul_state {w R : ℕ} (hw : w ≠ 0)
    (hR : Squarefree R) (hd : primeRadical w ∣ R) :
    primeRadical (w * R) = R := by
  have hsub : w.primeFactors ⊆ R.primeFactors :=
    (Nat.prod_primeFactors_dvd_iff hR.ne_zero).mp hd
  unfold primeRadical
  rw [Nat.primeFactors_mul hw hR.ne_zero, Finset.union_eq_right.mpr hsub,
    Nat.prod_primeFactors_of_squarefree hR]

private theorem clock_mul_state {w R : ℕ} (hw : w ≠ 0)
    (hR : Squarefree R) (hd : primeRadical w ∣ R) :
    lagVisibilityClock (w * R) = w := by
  change (w * R) / primeRadical (w * R) = w
  rw [full_radical_mul_state hw hR hd, Nat.mul_div_cancel w hR.ne_zero.bot_lt]

private theorem large_squarefree_sign_flip (d T : ℕ) (hd : Squarefree d) :
    ∃ R : ℕ, T ≤ R ∧ Squarefree R ∧ d ∣ R ∧
      moebiusReal R = -moebiusReal d := by
  obtain ⟨p, hpT, hp⟩ := Nat.exists_infinite_primes (T + d + 2)
  have hdp : Nat.Coprime d p := (hp.coprime_iff_not_dvd.mpr (by
    intro hpd
    have := Nat.le_of_dvd hd.ne_zero.bot_lt hpd
    omega)).symm
  refine ⟨d * p, by nlinarith [hd.ne_zero.bot_lt],
    Nat.squarefree_mul_iff.mpr ⟨hdp, hd, hp.squarefree⟩, dvd_mul_right d p, ?_⟩
  have hm := ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime hdp
  rw [ArithmeticFunction.moebius_apply_prime hp, mul_neg_one] at hm
  unfold moebiusReal
  exact_mod_cast hm

private theorem large_squarefree_signs (d T : ℕ) (hd : Squarefree d) :
    (∃ R : ℕ, T ≤ R ∧ Squarefree R ∧ d ∣ R ∧ moebiusReal R = 1) ∧
    (∃ R : ℕ, T ≤ R ∧ Squarefree R ∧ d ∣ R ∧ moebiusReal R = -1) := by
  have hm := large_squarefree_sign_flip d T hd
  have hp : ∃ R : ℕ, T ≤ R ∧ Squarefree R ∧ d ∣ R ∧
      moebiusReal R = moebiusReal d := by
    obtain ⟨R, _, hR, hdR, hμR⟩ := hm
    obtain ⟨S, hST, hS, hRS, hμS⟩ := large_squarefree_sign_flip R T hR
    refine ⟨S, hST, hS, hdR.trans hRS, ?_⟩
    rw [hμS, hμR, neg_neg]
  rcases ArithmeticFunction.moebius_eq_or d with hzero | hpos | hneg
  · exact ((ArithmeticFunction.moebius_ne_zero_iff_squarefree.mpr hd) hzero).elim
  · have hpos' : moebiusReal d = 1 := by
      simpa [moebiusReal] using congrArg (Int.cast : ℤ → ℝ) hpos
    exact ⟨by simpa [hpos'] using hp, by simpa [hpos'] using hm⟩
  · have hneg' : moebiusReal d = -1 := by
      simpa [moebiusReal] using congrArg (Int.cast : ℤ → ℝ) hneg
    exact ⟨by simpa [hneg'] using hm, by simpa [hneg'] using hp⟩

private theorem clock_unit_attainment {A w : ℕ} (hw : 1 ≤ w) (hwA : w < A)
    (positive : Bool) (T : ℕ) :
    ∃ N n : ℕ, T ≤ N ∧ 1 ≤ N ∧ 1 ≤ n ∧ n ≤ A * N ∧
      lagVisibilityClock n = w ∧
      sieveSeq N moebiusReal n = (if positive then 1 else -1) := by
  have hex : ∃ R : ℕ, T + A + 2 ≤ R ∧ Squarefree R ∧ primeRadical w ∣ R ∧
      moebiusReal R = -(if positive then (1 : ℝ) else -1) := by
    have hs := large_squarefree_signs (primeRadical w) (T + A + 2)
      (squarefree_primeRadical w (by omega))
    cases positive
    · simpa using hs.1
    · simpa using hs.2
  obtain ⟨R, hRT, hR, hdR, hμR⟩ := hex
  have hRad := full_radical_mul_state (by omega : w ≠ 0) hR hdR
  have hR2 : 2 ≤ R := by omega
  have hpred : R - 1 + 1 = R := Nat.sub_add_cancel (by omega)
  have hprod : w * R + R ≤ A * R := by nlinarith
  refine ⟨R - 1, w * R, by omega, by omega, by nlinarith,
    by nlinarith, clock_mul_state (by omega) hR hdR, ?_⟩
  rw [← source_full_radical (R - 1) (Nat.mul_ne_zero (by omega) hR.ne_zero),
    hRad, sieveSeq_moebiusReal_first_octave (by omega) (by omega), hμR, neg_neg]

/-- The Möbius source at a positive sample depends only on its full radical. -/
theorem moebius_source_full_radical (N : ℕ) (n : ℕ+) :
    sieveSeq N moebiusReal (primeRadical n) = sieveSeq N moebiusReal n :=
  source_full_radical N n.property.ne'

/-- Exact squarefree parametrization of a visibility-clock fibre. -/
theorem moebius_visibilityClock_fibre (w R : ℕ+) :
    lagVisibilityClock ((w : ℕ) * R) = w ↔
      Squarefree (R : ℕ) ∧ primeRadical w ∣ (R : ℕ) := by
  constructor
  · intro hc
    have hmul := full_radical_clock ((w : ℕ) * R)
    rw [hc] at hmul
    have hRad : primeRadical ((w : ℕ) * R) = R :=
      Nat.eq_of_mul_eq_mul_left w.property hmul
    refine ⟨?_, ?_⟩
    · rw [← hRad]
      exact squarefree_primeRadical _ (Nat.mul_ne_zero w.property.ne' R.property.ne')
    · rw [← hRad]
      exact (squarefree_dvd_full_radical
        (Nat.mul_ne_zero w.property.ne' R.property.ne')
        (squarefree_primeRadical w w.property.ne')).mpr
        ((full_radical_dvd w).trans (dvd_mul_right (w : ℕ) (R : ℕ)))
  · rintro ⟨hR, hdR⟩
    exact clock_mul_state w.property.ne' hR hdR

/-- A nonzero literal source must have visibility clock below the horizon ratio. -/
theorem moebius_linear_horizon_zero_or_clock_lt (B : ℕ) (N : ℕ+)
    (k : Fin ((B + 2) * (N : ℕ))) :
    sieveSeq N moebiusReal (k.val + 1) = 0 ∨ lagVisibilityClock (k.val + 1) < B + 2 :=
  source_zero_or_clock_lt (by omega) (by omega) (Nat.succ_le_of_lt k.isLt)

/-- Every clock below the ratio realizes either unit sign at arbitrarily large cutoffs. -/
theorem moebius_visibilityClock_iff_cofinal_unit_source (B : ℕ) (w : ℕ+)
    (positive : Bool) :
    (w : ℕ) < B + 2 ↔ ∀ T : ℕ, ∃ N : ℕ+, T ≤ (N : ℕ) ∧
      ∃ k : Fin ((B + 2) * (N : ℕ)), lagVisibilityClock (k.val + 1) = w ∧
        sieveSeq N moebiusReal (k.val + 1) = (if positive then 1 else -1) := by
  constructor
  · intro hw T
    obtain ⟨N, n, hTN, hN, hn, hhi, hc, hs⟩ := clock_unit_attainment w.property hw positive T
    refine ⟨⟨N, hN⟩, hTN, ⟨n - 1, by dsimp; omega⟩, ?_⟩
    change lagVisibilityClock (n - 1 + 1) = w ∧
      sieveSeq N moebiusReal (n - 1 + 1) = (if positive then 1 else -1)
    rw [Nat.sub_add_cancel hn]
    constructor
    · exact hc
    · cases positive <;> simpa using hs
  · intro h
    obtain ⟨N, _, k, hc, hs⟩ := h 0
    rcases moebius_linear_horizon_zero_or_clock_lt B N k with hz | hlt
    · rw [hz] at hs
      cases positive <;> norm_num at hs
    · simpa only [hc] using hlt

end GaloisForLFunctions.BezoutValuationIncidence
