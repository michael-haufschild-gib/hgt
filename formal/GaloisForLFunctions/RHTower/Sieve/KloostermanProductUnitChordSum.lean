import GaloisForLFunctions.RHTower.Sieve.KloostermanCoprimeCrossPhaseFrequency
import GaloisForLFunctions.RHTower.Sieve.CircleSeparation
import GaloisForLFunctions.RHTower.Sieve.FiniteReciprocalBound

/-!
# Harmonic bound for the product-unit chord sum

The reciprocal chord at a nonzero frequency `j mod N` is controlled by the two endpoint
reciprocals `1/j + 1/(N-j)`.  Unit representatives are injective in each endpoint coordinate, so
both sums embed into the ordinary harmonic sum through `N`.  This proves the collective bound

`sum_{z in (ZMod N)ˣ} 2 / ||1 - e_N(z)|| ≤ N * (1 + log N)`.

Combined with coprime CRT compression, the literal unequal-modulus terminal Kloosterman block has
the length-independent bound `q*r*(1+log(q*r))`.  No spectral estimate or unproved analytic input
is used.
-/

open scoped BigOperators ComplexConjugate
open Complex Finset

namespace RHTower.Sieve

noncomputable section

/-- Standard additive character written at the canonical representative divided by the modulus. -/
theorem stdAddChar_eq_exp_val
    (N : ℕ) [NeZero N] (z : ZMod N) :
    ZMod.stdAddChar z =
      Complex.exp (((2 * Real.pi * ((z.val : ℝ) / N) : ℝ) : ℂ) * Complex.I) := by
  rw [ZMod.stdAddChar_apply, ZMod.toCircle_apply]
  congr 1
  push_cast
  have hNC : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne N)
  field_simp [hNC]

private theorem exp_two_pi_sub_one (a : ℝ) :
    Complex.exp (((2 * Real.pi * (a - 1) : ℝ) : ℂ) * Complex.I) =
      Complex.exp (((2 * Real.pi * a : ℝ) : ℂ) * Complex.I) := by
  have hsplit : ((2 * Real.pi * (a - 1) : ℝ) : ℂ) * Complex.I =
      ((2 * Real.pi * a : ℝ) : ℂ) * Complex.I +
        ((-1 : ℤ) : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) := by
    push_cast
    ring
  rw [hsplit, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]

/-- A nonzero cyclic frequency has chord at least four times its distance from either endpoint of
the canonical residue interval. -/
theorem four_mul_cyclicDistance_le_norm_one_sub_stdAddChar
    (N : ℕ) [NeZero N] (hN : 1 < N) (z : (ZMod N)ˣ) :
    4 * min ((z : ZMod N).val : ℝ) (N - (z : ZMod N).val : ℕ) / N ≤
      ‖1 - ZMod.stdAddChar (z : ZMod N)‖ := by
  letI : Nontrivial (ZMod N) := ZMod.nontrivial_iff.mpr hN.ne'
  have hjpos : 0 < (z : ZMod N).val := by
    exact Nat.pos_of_ne_zero ((ZMod.val_ne_zero _).mpr (Units.ne_zero z))
  have hjlt : (z : ZMod N).val < N := ZMod.val_lt _
  have hNC : (0 : ℝ) < N := by exact_mod_cast (lt_trans Nat.zero_lt_one hN)
  rw [stdAddChar_eq_exp_val]
  rw [norm_sub_rev]
  by_cases hhalf : 2 * (z : ZMod N).val ≤ N
  · have hmin : min ((z : ZMod N).val : ℝ) (N - (z : ZMod N).val : ℕ) =
        ((z : ZMod N).val : ℝ) := by
      rw [min_eq_left]
      exact_mod_cast (by omega : (z : ZMod N).val ≤ N - (z : ZMod N).val)
    rw [hmin]
    have hbeta : |((z : ZMod N).val : ℝ) / N| ≤ 1 / 2 := by
      rw [abs_of_nonneg (div_nonneg (Nat.cast_nonneg _) hNC.le)]
      apply (div_le_iff₀ hNC).mpr
      have hhalfR : (2 : ℝ) * ((z : ZMod N).val : ℝ) ≤ (N : ℝ) := by
        exact_mod_cast hhalf
      nlinarith
    have h := four_mul_abs_le_norm_exp_two_pi hbeta
    rw [abs_of_nonneg (div_nonneg (Nat.cast_nonneg _) hNC.le)] at h
    convert h using 1
    all_goals ring
  · have hmin : min ((z : ZMod N).val : ℝ) (N - (z : ZMod N).val : ℕ) =
        ((N - (z : ZMod N).val : ℕ) : ℝ) := by
      rw [min_eq_right]
      exact_mod_cast (by omega : N - (z : ZMod N).val ≤ (z : ZMod N).val)
    rw [hmin]
    let beta : ℝ := ((z : ZMod N).val : ℝ) / N - 1
    have hbetaNeg : beta ≤ 0 := by
      dsimp [beta]
      have hjltR : (((z : ZMod N).val : ℕ) : ℝ) < (N : ℝ) := by
        exact_mod_cast hjlt
      have := (div_lt_one hNC).mpr hjltR
      linarith
    have hbetaAbs : |beta| = ((N - (z : ZMod N).val : ℕ) : ℝ) / N := by
      rw [abs_of_nonpos hbetaNeg]
      dsimp [beta]
      rw [Nat.cast_sub (Nat.le_of_lt hjlt)]
      field_simp
      ring
    have hbetaHalf : |beta| ≤ 1 / 2 := by
      rw [hbetaAbs]
      apply (div_le_iff₀ hNC).mpr
      have hlarge : N < 2 * (z : ZMod N).val := Nat.lt_of_not_ge hhalf
      have hdist : 2 * (N - (z : ZMod N).val) ≤ N := by omega
      have hdistR : (2 : ℝ) * ((N - (z : ZMod N).val : ℕ) : ℝ) ≤
          (N : ℝ) := by exact_mod_cast hdist
      nlinarith
    have h := four_mul_abs_le_norm_exp_two_pi hbetaHalf
    rw [hbetaAbs] at h
    have hexp := exp_two_pi_sub_one (((z : ZMod N).val : ℝ) / N)
    dsimp [beta] at h
    rw [hexp] at h
    convert h using 1
    all_goals ring

/-- Pointwise reciprocal-chord bound by the two endpoint reciprocals of the canonical residue. -/
theorem two_div_norm_one_sub_stdAddChar_le_twoSidedReciprocals
    (N : ℕ) [NeZero N] (hN : 1 < N) (z : (ZMod N)ˣ) :
    2 / ‖1 - ZMod.stdAddChar (z : ZMod N)‖ ≤
      (N : ℝ) / 2 *
        (1 / (((z : ZMod N).val : ℕ) : ℝ) +
          1 / ((N - (z : ZMod N).val : ℕ) : ℝ)) := by
  letI : Nontrivial (ZMod N) := ZMod.nontrivial_iff.mpr hN.ne'
  let j := (z : ZMod N).val
  let k := N - j
  let d : ℝ := min (j : ℝ) (k : ℝ)
  have hjpos : 0 < j := by
    exact Nat.pos_of_ne_zero ((ZMod.val_ne_zero _).mpr (Units.ne_zero z))
  have hjlt : j < N := ZMod.val_lt _
  have hkpos : 0 < k := by omega
  have hjR : (0 : ℝ) < j := by exact_mod_cast hjpos
  have hkR : (0 : ℝ) < k := by exact_mod_cast hkpos
  have hdpos : 0 < d := lt_min hjR hkR
  have hNR : (0 : ℝ) < N := by exact_mod_cast (lt_trans Nat.zero_lt_one hN)
  have hlower : 4 * d / (N : ℝ) ≤
      ‖1 - ZMod.stdAddChar (z : ZMod N)‖ := by
    simpa [j, k, d] using
      four_mul_cyclicDistance_le_norm_one_sub_stdAddChar N hN z
  have hbasepos : 0 < 4 * d / (N : ℝ) := div_pos (by positivity) hNR
  have hchordpos : 0 < ‖1 - ZMod.stdAddChar (z : ZMod N)‖ :=
    hbasepos.trans_le hlower
  have hrecip : 2 / ‖1 - ZMod.stdAddChar (z : ZMod N)‖ ≤
      2 / (4 * d / (N : ℝ)) := by
    apply (div_le_div_iff₀ hchordpos hbasepos).mpr
    nlinarith
  have hminInv : 1 / d ≤ 1 / (j : ℝ) + 1 / (k : ℝ) := by
    rcases le_total (j : ℝ) (k : ℝ) with hjk | hkj
    · rw [show d = (j : ℝ) by simp [d, hjk]]
      exact le_add_of_nonneg_right (by positivity)
    · rw [show d = (k : ℝ) by simp [d, hkj]]
      exact le_add_of_nonneg_left (by positivity)
  calc
    2 / ‖1 - ZMod.stdAddChar (z : ZMod N)‖ ≤
        2 / (4 * d / (N : ℝ)) := hrecip
    _ = (N : ℝ) / 2 * (1 / d) := by field_simp; ring
    _ ≤ (N : ℝ) / 2 * (1 / (j : ℝ) + 1 / (k : ℝ)) := by
      exact mul_le_mul_of_nonneg_left hminInv (by positivity)
    _ = _ := by rfl

private def zmodUnitVals (N : ℕ) [NeZero N] : Finset ℕ :=
  Finset.univ.image (fun z : (ZMod N)ˣ => (z : ZMod N).val)

private def zmodUnitComplementVals (N : ℕ) [NeZero N] : Finset ℕ :=
  Finset.univ.image (fun z : (ZMod N)ˣ => N - (z : ZMod N).val)

/-- Harmonic bound for canonical representatives of unit residues. -/
theorem sum_zmodUnits_inv_val_le_one_add_log
    (N : ℕ) [NeZero N] (hN : 1 < N) :
    (∑ z : (ZMod N)ˣ, 1 / (((z : ZMod N).val : ℕ) : ℝ)) ≤
      1 + Real.log N := by
  classical
  letI : Nontrivial (ZMod N) := ZMod.nontrivial_iff.mpr hN.ne'
  let f : (ZMod N)ˣ → ℕ := fun z => (z : ZMod N).val
  have hfinj : Function.Injective f := by
    intro z w h
    apply Units.ext
    apply ZMod.val_injective N
    exact h
  have hsum : (∑ n ∈ zmodUnitVals N, 1 / (n : ℝ)) =
      ∑ z : (ZMod N)ˣ, 1 / (f z : ℝ) := by
    exact Finset.sum_image (fun _ _ _ _ h => hfinj h)
  rw [← hsum]
  apply sum_inv_finset_bounded_le_one_add_log
  · intro n hn
    rcases Finset.mem_image.mp hn with ⟨z, hz, rfl⟩
    exact Nat.one_le_iff_ne_zero.mpr
      ((ZMod.val_ne_zero _).mpr (Units.ne_zero z))
  · intro n hn
    rcases Finset.mem_image.mp hn with ⟨z, hz, rfl⟩
    exact Nat.le_of_lt (ZMod.val_lt _)

/-- Harmonic bound for complementary representatives `N - val z` of unit residues. -/
theorem sum_zmodUnits_inv_complementVal_le_one_add_log
    (N : ℕ) [NeZero N] (hN : 1 < N) :
    (∑ z : (ZMod N)ˣ, 1 / ((N - (z : ZMod N).val : ℕ) : ℝ)) ≤
      1 + Real.log N := by
  classical
  letI : Nontrivial (ZMod N) := ZMod.nontrivial_iff.mpr hN.ne'
  let f : (ZMod N)ˣ → ℕ := fun z => N - (z : ZMod N).val
  have hfinj : Function.Injective f := by
    intro z w h
    apply Units.ext
    apply ZMod.val_injective N
    have hz := ZMod.val_lt (z : ZMod N)
    have hw := ZMod.val_lt (w : ZMod N)
    dsimp [f] at h
    omega
  have hsum : (∑ n ∈ zmodUnitComplementVals N, 1 / (n : ℝ)) =
      ∑ z : (ZMod N)ˣ, 1 / (f z : ℝ) := by
    exact Finset.sum_image (fun _ _ _ _ h => hfinj h)
  rw [← hsum]
  apply sum_inv_finset_bounded_le_one_add_log
  · intro n hn
    rcases Finset.mem_image.mp hn with ⟨z, hz, rfl⟩
    have := ZMod.val_lt (z : ZMod N)
    omega
  · intro n hn
    rcases Finset.mem_image.mp hn with ⟨z, hz, rfl⟩
    omega

/-- Collective reciprocal-chord budget for every unit frequency at one modulus. -/
theorem sum_zmodUnits_reciprocalChord_le
    (N : ℕ) [NeZero N] (hN : 1 < N) :
    (∑ z : (ZMod N)ˣ, 2 / ‖1 - ZMod.stdAddChar (z : ZMod N)‖) ≤
      (N : ℝ) * (1 + Real.log N) := by
  have hpoint := fun z : (ZMod N)ˣ =>
    two_div_norm_one_sub_stdAddChar_le_twoSidedReciprocals N hN z
  calc
    (∑ z : (ZMod N)ˣ, 2 / ‖1 - ZMod.stdAddChar (z : ZMod N)‖) ≤
        ∑ z : (ZMod N)ˣ, (N : ℝ) / 2 *
          (1 / (((z : ZMod N).val : ℕ) : ℝ) +
            1 / ((N - (z : ZMod N).val : ℕ) : ℝ)) := by
      exact Finset.sum_le_sum fun z hz => hpoint z
    _ = (N : ℝ) / 2 *
        ((∑ z : (ZMod N)ˣ, 1 / (((z : ZMod N).val : ℕ) : ℝ)) +
          ∑ z : (ZMod N)ˣ,
            1 / ((N - (z : ZMod N).val : ℕ) : ℝ)) := by
      rw [mul_add, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro z hz
      ring
    _ ≤ (N : ℝ) / 2 *
        ((1 + Real.log N) + (1 + Real.log N)) := by
      gcongr
      · exact sum_zmodUnits_inv_val_le_one_add_log N hN
      · exact sum_zmodUnits_inv_complementVal_le_one_add_log N hN
    _ = (N : ℝ) * (1 + Real.log N) := by ring

/-- Coprime terminal block bound after CRT compression and collective harmonic summation. -/
theorem norm_kloostermanNaturalCrossIntervalTerminalBlock_le_coprimeHarmonic
    (M q r : ℕ) [NeZero q] [NeZero r] [NeZero (q * r)]
    (hprod : 1 < q * r) (hcop : Nat.Coprime q r) (hqr : q ≠ r)
    (n : ZMod q) (k : ZMod r) :
    ‖kloostermanNaturalCrossIntervalTerminalBlock M q r n k‖ ≤
      (q * r : ℝ) * (1 + Real.log (q * r)) := by
  apply (norm_kloostermanNaturalCrossIntervalTerminalBlock_le_productUnitChords
    M q r hcop hqr n k).trans
  simpa only [Nat.cast_mul] using sum_zmodUnits_reciprocalChord_le (q * r) hprod

/-- Stored-index coprime cross-modulus correlation has the same product-period harmonic bound. -/
theorem norm_kloostermanCrossModulusCorrelation_Icc_le_coprimeHarmonic
    (M q r : ℕ) (hqr : q ≠ r)
    (hcop : Nat.Coprime (q + 1) (r + 1)) (n k : ℤ) :
    ‖kloostermanCrossModulusCorrelation (Finset.Icc 1 M) q r n k‖ ≤
      (((q + 1) * (r + 1) : ℕ) : ℝ) *
        (1 + Real.log ((q + 1) * (r + 1))) := by
  have hprod : 1 < (q + 1) * (r + 1) := by
    by_cases hq0 : q = 0
    · subst q
      have hrpos : 0 < r := Nat.pos_of_ne_zero (by omega)
      simp
      omega
    · have hq2 : 2 ≤ q + 1 := by omega
      have hr1 : 1 ≤ r + 1 := by omega
      have htwo : 2 ≤ (q + 1) * (r + 1) := by
        simpa using Nat.mul_le_mul hq2 hr1
      omega
  rw [kloostermanCrossModulusCorrelation_Icc_eq_terminalBlock_of_ne
    M q r hqr n k]
  simpa only [Nat.cast_mul, Nat.cast_add, Nat.cast_one] using
    norm_kloostermanNaturalCrossIntervalTerminalBlock_le_coprimeHarmonic
      M (q + 1) (r + 1) hprod hcop (Nat.succ_ne_succ_iff.mpr hqr)
        (Int.cast n) (Int.cast k)

end

end RHTower.Sieve
