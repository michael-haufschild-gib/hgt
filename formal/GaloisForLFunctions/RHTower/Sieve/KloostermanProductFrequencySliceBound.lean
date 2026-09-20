import GaloisForLFunctions.RHTower.Sieve.KloostermanProductUnitChordSum

/-!
# Product-period harmonic bounds without coprimality

For arbitrary positive unequal moduli \`q\` and \`r\`, the cross phase attached to unit
frequencies \`x\` and \`y\` is the standard additive character of
\`q * val(y) - r * val(x)\` modulo \`q*r\`.  Each one-coordinate slice of this frequency map is
injective, and unequal moduli force every frequency in the slice to be nonzero.

A general harmonic lemma bounds reciprocal chords along any injective family of nonzero cyclic
frequencies.  Applying it in either coordinate yields a shared-gcd-safe terminal correlation bound
with the smaller of the two totient multiplicities.  No coprimality, spectral estimate, or unproved
analytic input is used.
-/

open scoped BigOperators ComplexConjugate
open Complex Finset

namespace RHTower.Sieve

noncomputable section

/-- Product-period residue whose additive character is one unequal-modulus cross phase. -/
def kloostermanProductCrossPhaseFrequency
    (q r : ℕ) [NeZero q] [NeZero r]
    (x : (ZMod q)ˣ) (y : (ZMod r)ˣ) : ZMod (q * r) :=
  (((q : ℤ) * ((y : ZMod r).val : ℤ) -
    (r : ℤ) * ((x : ZMod q).val : ℤ) : ℤ) : ZMod (q * r))

/-- The product-period frequency carries exactly the original cross-phase ratio. -/
theorem kloostermanProductCrossPhaseFrequency_phase
    (q r : ℕ) [NeZero q] [NeZero r]
    (x : (ZMod q)ˣ) (y : (ZMod r)ˣ) :
    ZMod.stdAddChar (kloostermanProductCrossPhaseFrequency q r x y) =
      kloostermanCrossPhaseRatio q r x y := by
  letI : NeZero (q * r) := ⟨Nat.mul_ne_zero (NeZero.ne q) (NeZero.ne r)⟩
  unfold kloostermanProductCrossPhaseFrequency kloostermanCrossPhaseRatio
  rw [ZMod.stdAddChar_coe]
  rw [stdAddChar_eq_exp_val, stdAddChar_eq_exp_val]
  rw [← starRingEnd_apply, ← Complex.exp_conj]
  simp only [map_mul, Complex.conj_ofReal, Complex.conj_I]
  rw [← Complex.exp_add]
  congr 1
  push_cast
  have hqC : (q : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne q)
  have hrC : (r : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne r)
  field_simp [hqC, hrC]
  ring

/-- With the first unit fixed, product-period cross frequencies are injective in the second. -/
theorem kloostermanProductCrossPhaseFrequency_right_injective
    (q r : ℕ) [NeZero q] [NeZero r]
    (x : (ZMod q)ˣ) :
    Function.Injective (fun y : (ZMod r)ˣ => kloostermanProductCrossPhaseFrequency q r x y) := by
  intro y y' h
  have hphase := congrArg ZMod.stdAddChar h
  rw [kloostermanProductCrossPhaseFrequency_phase, kloostermanProductCrossPhaseFrequency_phase] at hphase
  unfold kloostermanCrossPhaseRatio at hphase
  have hxne : star (ZMod.stdAddChar (x : ZMod q)) ≠ 0 := by
    intro hs
    have hs' := congrArg star hs
    have hx0 : ZMod.stdAddChar (x : ZMod q) ≠ 0 :=
      norm_ne_zero_iff.mp (by simp)
    exact hx0 (by simpa using hs')
  have hychar : ZMod.stdAddChar (y : ZMod r) = ZMod.stdAddChar (y' : ZMod r) := by
    exact mul_left_cancel₀ hxne hphase
  have hdiff : ZMod.stdAddChar ((y : ZMod r) - (y' : ZMod r)) = 1 := by
    rw [AddChar.map_sub_eq_div, hychar]
    exact div_self (norm_ne_zero_iff.mp (by simp))
  have hy : (y : ZMod r) = (y' : ZMod r) := by
    have := (stdAddChar_eq_one_iff r _).mp hdiff
    exact sub_eq_zero.mp this
  exact Units.ext hy

/-- With the second unit fixed, product-period cross frequencies are injective in the first. -/
theorem kloostermanProductCrossPhaseFrequency_left_injective
    (q r : ℕ) [NeZero q] [NeZero r]
    (y : (ZMod r)ˣ) :
    Function.Injective (fun x : (ZMod q)ˣ => kloostermanProductCrossPhaseFrequency q r x y) := by
  intro x x' h
  have hphase := congrArg ZMod.stdAddChar h
  rw [kloostermanProductCrossPhaseFrequency_phase, kloostermanProductCrossPhaseFrequency_phase] at hphase
  unfold kloostermanCrossPhaseRatio at hphase
  have hyne : ZMod.stdAddChar (y : ZMod r) ≠ 0 :=
    norm_ne_zero_iff.mp (by simp)
  have hxchar : star (ZMod.stdAddChar (x : ZMod q)) =
      star (ZMod.stdAddChar (x' : ZMod q)) := by
    exact mul_right_cancel₀ hyne hphase
  have hxchar' : ZMod.stdAddChar (x : ZMod q) =
      ZMod.stdAddChar (x' : ZMod q) := by
    exact (starRingEnd ℂ).injective hxchar
  have hdiff : ZMod.stdAddChar ((x : ZMod q) - (x' : ZMod q)) = 1 := by
    rw [AddChar.map_sub_eq_div, hxchar']
    exact div_self (norm_ne_zero_iff.mp (by simp))
  have hx : (x : ZMod q) = (x' : ZMod q) := by
    have := (stdAddChar_eq_one_iff q _).mp hdiff
    exact sub_eq_zero.mp this
  exact Units.ext hx

/-- Unequal moduli force every product-period cross frequency to be nonzero. -/
theorem kloostermanProductCrossPhaseFrequency_ne_zero
    (q r : ℕ) [NeZero q] [NeZero r] (hqr : q ≠ r)
    (x : (ZMod q)ˣ) (y : (ZMod r)ˣ) :
    kloostermanProductCrossPhaseFrequency q r x y ≠ 0 := by
  letI : NeZero (q * r) := ⟨Nat.mul_ne_zero (NeZero.ne q) (NeZero.ne r)⟩
  intro hzero
  have hchar : ZMod.stdAddChar (kloostermanProductCrossPhaseFrequency q r x y) = 1 := by rw [hzero]; simp
  rw [kloostermanProductCrossPhaseFrequency_phase] at hchar
  exact kloostermanCrossPhaseRatio_ne_one_of_ne q r hqr x y hchar

private theorem exp_two_pi_sub_one_productFrequency (a : ℝ) :
    Complex.exp (((2 * Real.pi * (a - 1) : ℝ) : ℂ) * Complex.I) =
      Complex.exp (((2 * Real.pi * a : ℝ) : ℂ) * Complex.I) := by
  have hsplit : ((2 * Real.pi * (a - 1) : ℝ) : ℂ) * Complex.I =
      ((2 * Real.pi * a : ℝ) : ℂ) * Complex.I +
        ((-1 : ℤ) : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) := by
    push_cast
    ring
  rw [hsplit, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]

/-- Chord separation for an arbitrary nonzero cyclic frequency, without a unit assumption. -/
theorem four_mul_cyclicDistance_le_norm_one_sub_stdAddChar_of_ne_zero
    (N : ℕ) [NeZero N] (hN : 1 < N) (z : ZMod N) (hz : z ≠ 0) :
    4 * min (z.val : ℝ) (N - z.val : ℕ) / N ≤
      ‖1 - ZMod.stdAddChar z‖ := by
  letI : Nontrivial (ZMod N) := ZMod.nontrivial_iff.mpr hN.ne'
  have hjpos : 0 < z.val := by
    exact Nat.pos_of_ne_zero ((ZMod.val_ne_zero _).mpr hz)
  have hjlt : z.val < N := ZMod.val_lt _
  have hNC : (0 : ℝ) < N := by exact_mod_cast (lt_trans Nat.zero_lt_one hN)
  rw [stdAddChar_eq_exp_val]
  rw [norm_sub_rev]
  by_cases hhalf : 2 * z.val ≤ N
  · have hmin : min (z.val : ℝ) (N - z.val : ℕ) = (z.val : ℝ) := by
      rw [min_eq_left]
      exact_mod_cast (by omega : z.val ≤ N - z.val)
    rw [hmin]
    have hbeta : |(z.val : ℝ) / N| ≤ 1 / 2 := by
      rw [abs_of_nonneg (div_nonneg (Nat.cast_nonneg _) hNC.le)]
      apply (div_le_iff₀ hNC).mpr
      have hhalfR : (2 : ℝ) * (z.val : ℝ) ≤ (N : ℝ) := by exact_mod_cast hhalf
      nlinarith
    have h := four_mul_abs_le_norm_exp_two_pi hbeta
    rw [abs_of_nonneg (div_nonneg (Nat.cast_nonneg _) hNC.le)] at h
    convert h using 1
    all_goals ring
  · have hmin : min (z.val : ℝ) (N - z.val : ℕ) =
        ((N - z.val : ℕ) : ℝ) := by
      rw [min_eq_right]
      exact_mod_cast (by omega : N - z.val ≤ z.val)
    rw [hmin]
    let beta : ℝ := (z.val : ℝ) / N - 1
    have hbetaNeg : beta ≤ 0 := by
      dsimp [beta]
      have hjltR : (z.val : ℝ) < (N : ℝ) := by exact_mod_cast hjlt
      have := (div_lt_one hNC).mpr hjltR
      linarith
    have hbetaAbs : |beta| = ((N - z.val : ℕ) : ℝ) / N := by
      rw [abs_of_nonpos hbetaNeg]
      dsimp [beta]
      rw [Nat.cast_sub (Nat.le_of_lt hjlt)]
      field_simp
      ring
    have hbetaHalf : |beta| ≤ 1 / 2 := by
      rw [hbetaAbs]
      apply (div_le_iff₀ hNC).mpr
      have hlarge : N < 2 * z.val := Nat.lt_of_not_ge hhalf
      have hdist : 2 * (N - z.val) ≤ N := by omega
      have hdistR : (2 : ℝ) * ((N - z.val : ℕ) : ℝ) ≤ (N : ℝ) := by
        exact_mod_cast hdist
      nlinarith
    have h := four_mul_abs_le_norm_exp_two_pi hbetaHalf
    rw [hbetaAbs] at h
    have hexp := exp_two_pi_sub_one_productFrequency ((z.val : ℝ) / N)
    dsimp [beta] at h
    rw [hexp] at h
    convert h using 1
    all_goals ring

/-- Reciprocal-chord bound for an arbitrary nonzero cyclic frequency. -/
theorem two_div_norm_one_sub_stdAddChar_le_twoSidedReciprocals_of_ne_zero
    (N : ℕ) [NeZero N] (hN : 1 < N) (z : ZMod N) (hz : z ≠ 0) :
    2 / ‖1 - ZMod.stdAddChar z‖ ≤
      (N : ℝ) / 2 *
        (1 / ((z.val : ℕ) : ℝ) +
          1 / ((N - z.val : ℕ) : ℝ)) := by
  letI : Nontrivial (ZMod N) := ZMod.nontrivial_iff.mpr hN.ne'
  let j := z.val
  let k := N - j
  let d : ℝ := min (j : ℝ) (k : ℝ)
  have hjpos : 0 < j := by
    exact Nat.pos_of_ne_zero ((ZMod.val_ne_zero _).mpr hz)
  have hjlt : j < N := ZMod.val_lt _
  have hkpos : 0 < k := by omega
  have hjR : (0 : ℝ) < j := by exact_mod_cast hjpos
  have hkR : (0 : ℝ) < k := by exact_mod_cast hkpos
  have hdpos : 0 < d := lt_min hjR hkR
  have hNR : (0 : ℝ) < N := by exact_mod_cast (lt_trans Nat.zero_lt_one hN)
  have hlower : 4 * d / (N : ℝ) ≤ ‖1 - ZMod.stdAddChar z‖ := by
    simpa [j, k, d] using four_mul_cyclicDistance_le_norm_one_sub_stdAddChar_of_ne_zero N hN z hz
  have hbasepos : 0 < 4 * d / (N : ℝ) := div_pos (by positivity) hNR
  have hchordpos : 0 < ‖1 - ZMod.stdAddChar z‖ := hbasepos.trans_le hlower
  have hrecip : 2 / ‖1 - ZMod.stdAddChar z‖ ≤ 2 / (4 * d / (N : ℝ)) := by
    apply (div_le_div_iff₀ hchordpos hbasepos).mpr
    nlinarith
  have hminInv : 1 / d ≤ 1 / (j : ℝ) + 1 / (k : ℝ) := by
    rcases le_total (j : ℝ) (k : ℝ) with hjk | hkj
    · rw [show d = (j : ℝ) by simp [d, hjk]]
      exact le_add_of_nonneg_right (by positivity)
    · rw [show d = (k : ℝ) by simp [d, hkj]]
      exact le_add_of_nonneg_left (by positivity)
  calc
    2 / ‖1 - ZMod.stdAddChar z‖ ≤ 2 / (4 * d / (N : ℝ)) := hrecip
    _ = (N : ℝ) / 2 * (1 / d) := by field_simp; ring
    _ ≤ (N : ℝ) / 2 * (1 / (j : ℝ) + 1 / (k : ℝ)) := by
      exact mul_le_mul_of_nonneg_left hminInv (by positivity)
    _ = _ := by rfl

private def zmodFrequencyVals
    (N : ℕ) [NeZero N] {ι : Type*} [Fintype ι]
    (f : ι → ZMod N) : Finset ℕ :=
  Finset.univ.image (fun i => (f i).val)

private def zmodFrequencyComplementVals
    (N : ℕ) [NeZero N] {ι : Type*} [Fintype ι]
    (f : ι → ZMod N) : Finset ℕ :=
  Finset.univ.image (fun i => N - (f i).val)

/-- Harmonic bound for representatives of an injective nonzero cyclic-frequency family. -/
theorem sum_injective_zmodFrequency_inv_val_le_one_add_log
    (N : ℕ) [NeZero N] (_hN : 1 < N)
    {ι : Type*} [Fintype ι] (f : ι → ZMod N)
    (hinj : Function.Injective f) (hne : ∀ i, f i ≠ 0) :
    (∑ i, 1 / (((f i).val : ℕ) : ℝ)) ≤ 1 + Real.log N := by
  classical
  letI : Nontrivial (ZMod N) := ZMod.nontrivial_iff.mpr _hN.ne'
  let g : ι → ℕ := fun i => (f i).val
  have hginj : Function.Injective g := by
    intro i j h
    apply hinj
    apply ZMod.val_injective N
    exact h
  have hsum : (∑ n ∈ zmodFrequencyVals N f, 1 / (n : ℝ)) =
      ∑ i, 1 / (g i : ℝ) := by
    exact Finset.sum_image (fun _ _ _ _ h => hginj h)
  rw [← hsum]
  apply sum_inv_finset_bounded_le_one_add_log
  · intro n hn
    rcases Finset.mem_image.mp hn with ⟨i, hi, rfl⟩
    exact Nat.one_le_iff_ne_zero.mpr ((ZMod.val_ne_zero _).mpr (hne i))
  · intro n hn
    rcases Finset.mem_image.mp hn with ⟨i, hi, rfl⟩
    exact Nat.le_of_lt (ZMod.val_lt _)

/-- Harmonic bound for complementary representatives of an injective cyclic-frequency family. -/
theorem sum_injective_zmodFrequency_inv_complementVal_le_one_add_log
    (N : ℕ) [NeZero N] (hN : 1 < N)
    {ι : Type*} [Fintype ι] (f : ι → ZMod N)
    (hinj : Function.Injective f) :
    (∑ i, 1 / ((N - (f i).val : ℕ) : ℝ)) ≤ 1 + Real.log N := by
  classical
  letI : Nontrivial (ZMod N) := ZMod.nontrivial_iff.mpr hN.ne'
  let g : ι → ℕ := fun i => N - (f i).val
  have hginj : Function.Injective g := by
    intro i j h
    apply hinj
    apply ZMod.val_injective N
    have hi := ZMod.val_lt (f i)
    have hj := ZMod.val_lt (f j)
    dsimp [g] at h
    omega
  have hsum : (∑ n ∈ zmodFrequencyComplementVals N f, 1 / (n : ℝ)) =
      ∑ i, 1 / (g i : ℝ) := by
    exact Finset.sum_image (fun _ _ _ _ h => hginj h)
  rw [← hsum]
  apply sum_inv_finset_bounded_le_one_add_log
  · intro n hn
    rcases Finset.mem_image.mp hn with ⟨i, hi, rfl⟩
    have := ZMod.val_lt (f i)
    omega
  · intro n hn
    rcases Finset.mem_image.mp hn with ⟨i, hi, rfl⟩
    omega

/-- Reciprocal-chord budget for any injective family of nonzero cyclic frequencies. -/
theorem sum_injective_nonzero_zmodFrequency_reciprocalChord_le
    (N : ℕ) [NeZero N] (hN : 1 < N)
    {ι : Type*} [Fintype ι] (f : ι → ZMod N)
    (hinj : Function.Injective f) (hne : ∀ i, f i ≠ 0) :
    (∑ i, 2 / ‖1 - ZMod.stdAddChar (f i)‖) ≤
      (N : ℝ) * (1 + Real.log N) := by
  calc
    (∑ i, 2 / ‖1 - ZMod.stdAddChar (f i)‖) ≤
        ∑ i, (N : ℝ) / 2 *
          (1 / (((f i).val : ℕ) : ℝ) +
            1 / ((N - (f i).val : ℕ) : ℝ)) := by
      exact Finset.sum_le_sum fun i hi => two_div_norm_one_sub_stdAddChar_le_twoSidedReciprocals_of_ne_zero N hN (f i) (hne i)
    _ = (N : ℝ) / 2 *
        ((∑ i, 1 / (((f i).val : ℕ) : ℝ)) +
          ∑ i, 1 / ((N - (f i).val : ℕ) : ℝ)) := by
      rw [mul_add, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i hi
      ring
    _ ≤ (N : ℝ) / 2 * ((1 + Real.log N) + (1 + Real.log N)) := by
      gcongr
      · exact sum_injective_zmodFrequency_inv_val_le_one_add_log N hN f hinj hne
      · exact sum_injective_zmodFrequency_inv_complementVal_le_one_add_log N hN f hinj
    _ = (N : ℝ) * (1 + Real.log N) := by ring

/-- One fixed-first-coordinate slice has one product-period harmonic budget. -/
theorem sum_kloostermanCrossPhaseRatio_reciprocalChord_le_productHarmonic_rightSlice
    (q r : ℕ) [NeZero q] [NeZero r] (hqr : q ≠ r)
    (x : (ZMod q)ˣ) :
    (∑ y : (ZMod r)ˣ, 2 / ‖1 - kloostermanCrossPhaseRatio q r x y‖) ≤
      (q * r : ℝ) * (1 + Real.log (q * r)) := by
  letI : NeZero (q * r) := ⟨Nat.mul_ne_zero (NeZero.ne q) (NeZero.ne r)⟩
  have hprod : 1 < q * r := by
    by_cases hq : q = 1
    · subst q
      have hrpos := Nat.pos_of_ne_zero (NeZero.ne r)
      have hr2 : 2 ≤ r := by omega
      simpa using (Nat.lt_of_succ_le hr2)
    · have hqpos := Nat.pos_of_ne_zero (NeZero.ne q)
      have hrpos := Nat.pos_of_ne_zero (NeZero.ne r)
      have hq2 : 2 ≤ q := by omega
      have hr1 : 1 ≤ r := hrpos
      exact lt_of_lt_of_le Nat.one_lt_two (Nat.mul_le_mul hq2 hr1)
  have h := sum_injective_nonzero_zmodFrequency_reciprocalChord_le (q * r) hprod
    (fun y : (ZMod r)ˣ => kloostermanProductCrossPhaseFrequency q r x y)
    (kloostermanProductCrossPhaseFrequency_right_injective q r x)
    (fun y => kloostermanProductCrossPhaseFrequency_ne_zero q r hqr x y)
  simpa only [kloostermanProductCrossPhaseFrequency_phase, Nat.cast_mul] using h

/-- Summing right slices costs exactly the first modulus totient. -/
theorem sum_kloostermanCrossPhaseRatio_reciprocalChord_le_productHarmonic_right
    (q r : ℕ) [NeZero q] [NeZero r] (hqr : q ≠ r) :
    (∑ x : (ZMod q)ˣ, ∑ y : (ZMod r)ˣ,
      2 / ‖1 - kloostermanCrossPhaseRatio q r x y‖) ≤
      (Nat.totient q : ℝ) *
        ((q * r : ℝ) * (1 + Real.log (q * r))) := by
  calc
    (∑ x : (ZMod q)ˣ, ∑ y : (ZMod r)ˣ,
        2 / ‖1 - kloostermanCrossPhaseRatio q r x y‖) ≤
        ∑ _x : (ZMod q)ˣ,
          ((q * r : ℝ) * (1 + Real.log (q * r))) := by
      exact Finset.sum_le_sum fun x hx => sum_kloostermanCrossPhaseRatio_reciprocalChord_le_productHarmonic_rightSlice q r hqr x
    _ = (Nat.totient q : ℝ) *
        ((q * r : ℝ) * (1 + Real.log (q * r))) := by
      rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ,
        ZMod.card_units_eq_totient]

/-- One fixed-second-coordinate slice has one product-period harmonic budget. -/
theorem sum_kloostermanCrossPhaseRatio_reciprocalChord_le_productHarmonic_leftSlice
    (q r : ℕ) [NeZero q] [NeZero r] (hqr : q ≠ r)
    (y : (ZMod r)ˣ) :
    (∑ x : (ZMod q)ˣ, 2 / ‖1 - kloostermanCrossPhaseRatio q r x y‖) ≤
      (q * r : ℝ) * (1 + Real.log (q * r)) := by
  letI : NeZero (q * r) := ⟨Nat.mul_ne_zero (NeZero.ne q) (NeZero.ne r)⟩
  have hprod : 1 < q * r := by
    by_cases hq : q = 1
    · subst q
      have hrpos := Nat.pos_of_ne_zero (NeZero.ne r)
      have hr2 : 2 ≤ r := by omega
      simpa using (Nat.lt_of_succ_le hr2)
    · have hqpos := Nat.pos_of_ne_zero (NeZero.ne q)
      have hrpos := Nat.pos_of_ne_zero (NeZero.ne r)
      have hq2 : 2 ≤ q := by omega
      have hr1 : 1 ≤ r := hrpos
      exact lt_of_lt_of_le Nat.one_lt_two (Nat.mul_le_mul hq2 hr1)
  have h := sum_injective_nonzero_zmodFrequency_reciprocalChord_le (q * r) hprod
    (fun x : (ZMod q)ˣ => kloostermanProductCrossPhaseFrequency q r x y)
    (kloostermanProductCrossPhaseFrequency_left_injective q r y)
    (fun x => kloostermanProductCrossPhaseFrequency_ne_zero q r hqr x y)
  simpa only [kloostermanProductCrossPhaseFrequency_phase, Nat.cast_mul] using h

/-- Summing left slices costs exactly the second modulus totient. -/
theorem sum_kloostermanCrossPhaseRatio_reciprocalChord_le_productHarmonic_left
    (q r : ℕ) [NeZero q] [NeZero r] (hqr : q ≠ r) :
    (∑ x : (ZMod q)ˣ, ∑ y : (ZMod r)ˣ,
      2 / ‖1 - kloostermanCrossPhaseRatio q r x y‖) ≤
      (Nat.totient r : ℝ) *
        ((q * r : ℝ) * (1 + Real.log (q * r))) := by
  rw [Finset.sum_comm]
  calc
    (∑ y : (ZMod r)ˣ, ∑ x : (ZMod q)ˣ,
        2 / ‖1 - kloostermanCrossPhaseRatio q r x y‖) ≤
        ∑ _y : (ZMod r)ˣ,
          ((q * r : ℝ) * (1 + Real.log (q * r))) := by
      exact Finset.sum_le_sum fun y hy => sum_kloostermanCrossPhaseRatio_reciprocalChord_le_productHarmonic_leftSlice q r hqr y
    _ = (Nat.totient r : ℝ) *
        ((q * r : ℝ) * (1 + Real.log (q * r))) := by
      rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ,
        ZMod.card_units_eq_totient]

/-- Shared-gcd-safe double chord budget using the better slicing direction. -/
theorem sum_kloostermanCrossPhaseRatio_reciprocalChord_le_productHarmonic_min
    (q r : ℕ) [NeZero q] [NeZero r] (hqr : q ≠ r) :
    (∑ x : (ZMod q)ˣ, ∑ y : (ZMod r)ˣ,
      2 / ‖1 - kloostermanCrossPhaseRatio q r x y‖) ≤
      min
        ((Nat.totient q : ℝ) *
          ((q * r : ℝ) * (1 + Real.log (q * r))))
        ((Nat.totient r : ℝ) *
          ((q * r : ℝ) * (1 + Real.log (q * r)))) := by
  exact le_min (sum_kloostermanCrossPhaseRatio_reciprocalChord_le_productHarmonic_right q r hqr) (sum_kloostermanCrossPhaseRatio_reciprocalChord_le_productHarmonic_left q r hqr)

/-- Unequal-modulus terminal block bound requiring no coprimality. -/
theorem norm_kloostermanNaturalCrossIntervalTerminalBlock_le_productHarmonic
    (M q r : ℕ) [NeZero q] [NeZero r] (hqr : q ≠ r)
    (n : ZMod q) (k : ZMod r) :
    ‖kloostermanNaturalCrossIntervalTerminalBlock M q r n k‖ ≤
      min
        ((Nat.totient q : ℝ) *
          ((q * r : ℝ) * (1 + Real.log (q * r))))
        ((Nat.totient r : ℝ) *
          ((q * r : ℝ) * (1 + Real.log (q * r)))) := by
  exact (norm_kloostermanNaturalCrossIntervalTerminalBlock_le_geometric
    M q r hqr n k).trans (sum_kloostermanCrossPhaseRatio_reciprocalChord_le_productHarmonic_min q r hqr)

/-- Stored-index unequal-modulus correlation bound requiring no coprimality. -/
theorem norm_kloostermanCrossModulusCorrelation_Icc_le_productHarmonic
    (M q r : ℕ) (hqr : q ≠ r) (n k : ℤ) :
    ‖kloostermanCrossModulusCorrelation (Finset.Icc 1 M) q r n k‖ ≤
      min
        ((Nat.totient (q + 1) : ℝ) *
          ((((q + 1) * (r + 1) : ℕ) : ℝ) *
            (1 + Real.log ((q + 1) * (r + 1)))))
        ((Nat.totient (r + 1) : ℝ) *
          ((((q + 1) * (r + 1) : ℕ) : ℝ) *
            (1 + Real.log ((q + 1) * (r + 1))))) := by
  rw [kloostermanCrossModulusCorrelation_Icc_eq_terminalBlock_of_ne
    M q r hqr n k]
  simpa only [Nat.cast_mul, Nat.cast_add, Nat.cast_one] using
    norm_kloostermanNaturalCrossIntervalTerminalBlock_le_productHarmonic M (q + 1) (r + 1)
      (Nat.succ_ne_succ_iff.mpr hqr) (Int.cast n) (Int.cast k)

end

end RHTower.Sieve
