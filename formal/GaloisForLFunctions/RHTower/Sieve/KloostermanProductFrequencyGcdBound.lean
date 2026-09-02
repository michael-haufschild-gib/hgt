import GaloisForLFunctions.RHTower.Sieve.KloostermanProductHarmonicQuadratic

/-!
# GCD multiplicity bounds for product-period Kloosterman frequencies

For arbitrary positive moduli, equality of two product-period cross frequencies forces their
first unit representatives to agree modulo the first modulus divided by the shared gcd.  Recording
the remaining quotient embeds every frequency fibre into `Fin (gcd q r)`, so every fibre has
cardinality at most `gcd q r`.

Grouping reciprocal chords by frequency therefore replaces the earlier one-coordinate totient loss
by an exact shared-gcd multiplicity.  The bound is propagated through terminal correlations,
distinct-modulus Gram entries, full source quadratics, and erased off-diagonal quadratics.  All
results are unconditional absolute-value estimates; they do not supply signed spectral saving.
-/

open scoped BigOperators ComplexConjugate
open Complex Finset

namespace RHTower.Sieve

noncomputable section

/-- Equal cross frequencies force first representatives to agree modulo `q / gcd(q,r)`. -/
theorem kloostermanProductCrossPhaseFrequency_eq_imp_x_modEq_reduced
    (q r : ℕ) [NeZero q] [NeZero r]
    (x x' : (ZMod q)ˣ) (y y' : (ZMod r)ˣ)
    (hfreq : kloostermanProductCrossPhaseFrequency q r x y =
      kloostermanProductCrossPhaseFrequency q r x' y') :
    (x : ZMod q).val ≡ (x' : ZMod q).val [MOD q / q.gcd r] := by
  let d := q.gcd r
  let q0 := q / d
  let r0 := r / d
  have hdpos : 0 < d := Nat.gcd_pos_of_pos_left r (Nat.pos_of_ne_zero (NeZero.ne q))
  have hqfac : d * q0 = q := by
    dsimp [q0, d]
    exact Nat.mul_div_cancel' (Nat.gcd_dvd_left q r)
  have hrfac : d * r0 = r := by
    dsimp [r0, d]
    exact Nat.mul_div_cancel' (Nat.gcd_dvd_right q r)
  have hprod : ((q * r : ℕ) : ℤ) ∣
      ((q : ℤ) * (y' : ZMod r).val - (r : ℤ) * (x' : ZMod q).val) -
        ((q : ℤ) * (y : ZMod r).val - (r : ℤ) * (x : ZMod q).val) := by
    exact (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ (q * r)).mp hfreq
  rcases hprod with ⟨j, hj⟩
  have hdiv : (q : ℤ) ∣
      (r * (x' : ZMod q).val : ℕ) - (r * (x : ZMod q).val : ℕ) := by
    refine ⟨((y' : ZMod r).val : ℤ) - (y : ZMod r).val - (r : ℤ) * j, ?_⟩
    calc
      _ = (q : ℤ) * ((y' : ZMod r).val - (y : ZMod r).val) -
          (((q : ℤ) * (y' : ZMod r).val - (r : ℤ) * (x' : ZMod q).val) -
            ((q : ℤ) * (y : ZMod r).val - (r : ℤ) * (x : ZMod q).val)) := by
        push_cast
        ring
      _ = (q : ℤ) * ((y' : ZMod r).val - (y : ZMod r).val) -
          ((q * r : ℕ) : ℤ) * j := by rw [hj]
      _ = (q : ℤ) *
          (((y' : ZMod r).val : ℤ) - (y : ZMod r).val - (r : ℤ) * j) := by
        push_cast
        ring
  rcases hdiv with ⟨k, hk⟩
  have hdZ : (d : ℤ) ≠ 0 := by exact_mod_cast hdpos.ne'
  have hqfacZ : (d : ℤ) * (q0 : ℤ) = (q : ℤ) := by exact_mod_cast hqfac
  have hrfacZ : (d : ℤ) * (r0 : ℤ) = (r : ℤ) := by exact_mod_cast hrfac
  have hfactor :
      (d : ℤ) * ((r0 : ℤ) * (x' : ZMod q).val -
        (r0 : ℤ) * (x : ZMod q).val) =
      (d : ℤ) * ((q0 : ℤ) * k) := by
    calc
      _ = (r : ℤ) * (x' : ZMod q).val -
          (r : ℤ) * (x : ZMod q).val := by rw [← hrfacZ]; ring
      _ = (q : ℤ) * k := by simpa only [Nat.cast_mul, Nat.cast_ofNat] using hk
      _ = _ := by rw [← hqfacZ]; ring
  have hkred :
      (r0 * (x' : ZMod q).val : ℕ) - (r0 * (x : ZMod q).val : ℕ) =
        (q0 : ℤ) * k := by
    push_cast
    exact mul_left_cancel₀ hdZ hfactor
  have hred : r0 * (x : ZMod q).val ≡ r0 * (x' : ZMod q).val [MOD q0] := by
    apply Nat.modEq_iff_dvd.mpr
    exact ⟨k, hkred⟩
  have hcop : q0.Coprime r0 := by
    simpa [q0, r0, d] using Nat.coprime_div_gcd_div_gcd hdpos
  exact Nat.ModEq.cancel_left_of_coprime hcop.gcd_eq_one hred

/-- Quotient label left after reducing the first representative modulo `q / gcd(q,r)`. -/
def kloostermanProductGcdSliceLabel
    (q r : ℕ) [NeZero q] [NeZero r]
    (p : (ZMod q)ˣ × (ZMod r)ˣ) : Fin (q.gcd r) := by
  have hdpos : 0 < q.gcd r :=
    Nat.gcd_pos_of_pos_left r (Nat.pos_of_ne_zero (NeZero.ne q))
  have hq0pos : 0 < q / q.gcd r :=
    Nat.div_pos (Nat.gcd_le_left r (Nat.pos_of_ne_zero (NeZero.ne q))) hdpos
  refine ⟨(p.1 : ZMod q).val / (q / q.gcd r), ?_⟩
  rw [Nat.div_lt_iff_lt_mul hq0pos]
  have hqfac : q.gcd r * (q / q.gcd r) = q :=
    Nat.mul_div_cancel' (Nat.gcd_dvd_left q r)
  simpa [hqfac] using ZMod.val_lt (p.1 : ZMod q)

/-- Product-period cross frequency is injective on each fixed gcd-slice label. -/
theorem kloostermanProductCrossPhaseFrequency_injective_on_gcdSlice
    (q r : ℕ) [NeZero q] [NeZero r]
    (p p' : (ZMod q)ˣ × (ZMod r)ˣ)
    (hslice : kloostermanProductGcdSliceLabel q r p =
      kloostermanProductGcdSliceLabel q r p')
    (hfreq : kloostermanProductCrossPhaseFrequency q r p.1 p.2 =
      kloostermanProductCrossPhaseFrequency q r p'.1 p'.2) :
    p = p' := by
  have hmod := kloostermanProductCrossPhaseFrequency_eq_imp_x_modEq_reduced
    q r p.1 p'.1 p.2 p'.2 hfreq
  have hrem : (p.1 : ZMod q).val % (q / q.gcd r) =
      (p'.1 : ZMod q).val % (q / q.gcd r) := hmod
  have hquot : (p.1 : ZMod q).val / (q / q.gcd r) =
      (p'.1 : ZMod q).val / (q / q.gcd r) := by
    exact congrArg Fin.val hslice
  have hxval : (p.1 : ZMod q).val = (p'.1 : ZMod q).val := by
    rw [← Nat.mod_add_div (p.1 : ZMod q).val (q / q.gcd r),
      ← Nat.mod_add_div (p'.1 : ZMod q).val (q / q.gcd r)]
    rw [hrem, hquot]
  have hx : p.1 = p'.1 := by
    apply Units.ext
    exact ZMod.val_injective q hxval
  have hy : p.2 = p'.2 := by
    apply kloostermanProductCrossPhaseFrequency_right_injective q r p.1
    simpa only [hx] using hfreq
  exact Prod.ext hx hy

/-- Fibre of the two-coordinate cross-frequency map over one product-period residue. -/
def kloostermanProductCrossPhaseFrequencyFibre
    (q r : ℕ) [NeZero q] [NeZero r] (z : ZMod (q * r)) :=
  {p : (ZMod q)ˣ × (ZMod r)ˣ //
    kloostermanProductCrossPhaseFrequency q r p.1 p.2 = z}

noncomputable instance kloostermanProductCrossPhaseFrequencyFibreFintype
    (q r : ℕ) [NeZero q] [NeZero r] (z : ZMod (q * r)) :
    Fintype (kloostermanProductCrossPhaseFrequencyFibre q r z) := by
  classical
  unfold kloostermanProductCrossPhaseFrequencyFibre
  infer_instance

/-- Every two-coordinate cross-frequency fibre has at most `gcd(q,r)` elements. -/
theorem card_kloostermanProductCrossPhaseFrequencyFibre_le_gcd
    (q r : ℕ) [NeZero q] [NeZero r] (z : ZMod (q * r)) :
    Fintype.card (kloostermanProductCrossPhaseFrequencyFibre q r z) ≤ q.gcd r := by
  let label : kloostermanProductCrossPhaseFrequencyFibre q r z → Fin (q.gcd r) :=
    fun p => kloostermanProductGcdSliceLabel q r p.1
  have hinj : Function.Injective label := by
    intro p p' hlabel
    apply Subtype.ext
    apply kloostermanProductCrossPhaseFrequency_injective_on_gcdSlice q r p.1 p'.1 hlabel
    exact p.2.trans p'.2.symm
  simpa [label] using Fintype.card_le_of_injective label hinj

/-- Full unequal-modulus chord sum with exact shared-gcd frequency multiplicity. -/
theorem sum_kloostermanCrossPhaseRatio_reciprocalChord_le_productHarmonic_gcd
    (q r : ℕ) [NeZero q] [NeZero r] (hqr : q ≠ r) :
    (∑ x : (ZMod q)ˣ, ∑ y : (ZMod r)ˣ,
      2 / ‖1 - kloostermanCrossPhaseRatio q r x y‖) ≤
      (q.gcd r : ℝ) * ((q * r : ℝ) * (1 + Real.log (q * r))) := by
  classical
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
  let f : (ZMod q)ˣ × (ZMod r)ˣ → {z : ZMod (q * r) // z ≠ 0} := fun p =>
    ⟨kloostermanProductCrossPhaseFrequency q r p.1 p.2,
      kloostermanProductCrossPhaseFrequency_ne_zero q r hqr p.1 p.2⟩
  have hfibreCard (z : {z : ZMod (q * r) // z ≠ 0}) :
      Fintype.card {p : (ZMod q)ˣ × (ZMod r)ˣ // f p = z} ≤ q.gcd r := by
    let label : {p : (ZMod q)ˣ × (ZMod r)ˣ // f p = z} → Fin (q.gcd r) :=
      fun p => kloostermanProductGcdSliceLabel q r p.1
    have hinj : Function.Injective label := by
      intro p p' hlabel
      apply Subtype.ext
      apply kloostermanProductCrossPhaseFrequency_injective_on_gcdSlice
        q r p.1 p'.1 hlabel
      exact congrArg Subtype.val (p.2.trans p'.2.symm)
    simpa [label] using Fintype.card_le_of_injective label hinj
  calc
    (∑ x : (ZMod q)ˣ, ∑ y : (ZMod r)ˣ,
        2 / ‖1 - kloostermanCrossPhaseRatio q r x y‖) =
        ∑ p : (ZMod q)ˣ × (ZMod r)ˣ,
          2 / ‖1 - ZMod.stdAddChar (f p).1‖ := by
      rw [Fintype.sum_prod_type]
      apply Finset.sum_congr rfl
      intro p hp
      apply Finset.sum_congr rfl
      intro y hy
      rw [show (f (p, y)).1 = kloostermanProductCrossPhaseFrequency q r p y by rfl,
        kloostermanProductCrossPhaseFrequency_phase]
    _ = ∑ z : {z : ZMod (q * r) // z ≠ 0},
          ∑ p : {p : (ZMod q)ˣ × (ZMod r)ˣ // f p = z},
            2 / ‖1 - ZMod.stdAddChar (f p.1).1‖ := by
      exact (Fintype.sum_fiberwise f
        (fun p => 2 / ‖1 - ZMod.stdAddChar (f p).1‖)).symm
    _ ≤ ∑ z : {z : ZMod (q * r) // z ≠ 0},
          (q.gcd r : ℝ) * (2 / ‖1 - ZMod.stdAddChar z.1‖) := by
      apply Finset.sum_le_sum
      intro z hz
      calc
        (∑ p : {p : (ZMod q)ˣ × (ZMod r)ˣ // f p = z},
            2 / ‖1 - ZMod.stdAddChar (f p.1).1‖) =
            ∑ _p : {p : (ZMod q)ˣ × (ZMod r)ˣ // f p = z},
              2 / ‖1 - ZMod.stdAddChar z.1‖ := by
          apply Finset.sum_congr rfl
          intro p hp
          rw [show (f p.1).1 = z.1 by exact congrArg Subtype.val p.2]
        _ = (Fintype.card {p : (ZMod q)ˣ × (ZMod r)ˣ // f p = z} : ℝ) *
              (2 / ‖1 - ZMod.stdAddChar z.1‖) := by simp
        _ ≤ (q.gcd r : ℝ) * (2 / ‖1 - ZMod.stdAddChar z.1‖) := by
          apply mul_le_mul_of_nonneg_right
          · exact_mod_cast hfibreCard z
          · exact div_nonneg (by positivity) (norm_nonneg _)
    _ = (q.gcd r : ℝ) *
          (∑ z : {z : ZMod (q * r) // z ≠ 0},
            2 / ‖1 - ZMod.stdAddChar z.1‖) := by
      rw [Finset.mul_sum]
    _ ≤ (q.gcd r : ℝ) * ((q * r : ℝ) * (1 + Real.log (q * r))) := by
      apply mul_le_mul_of_nonneg_left
      · simpa only [Nat.cast_mul] using
          (sum_injective_nonzero_zmodFrequency_reciprocalChord_le
            (q * r) hprod (fun z : {z : ZMod (q * r) // z ≠ 0} => z.1)
            Subtype.val_injective (fun z => z.2))
      · exact Nat.cast_nonneg _

/-- Terminal unequal-modulus block bounded by the shared-gcd product-harmonic budget. -/
theorem norm_kloostermanNaturalCrossIntervalTerminalBlock_le_productHarmonic_gcd
    (M q r : ℕ) [NeZero q] [NeZero r] (hqr : q ≠ r)
    (n : ZMod q) (k : ZMod r) :
    ‖kloostermanNaturalCrossIntervalTerminalBlock M q r n k‖ ≤
      (q.gcd r : ℝ) * ((q * r : ℝ) * (1 + Real.log (q * r))) := by
  exact (norm_kloostermanNaturalCrossIntervalTerminalBlock_le_geometric
    M q r hqr n k).trans
      (sum_kloostermanCrossPhaseRatio_reciprocalChord_le_productHarmonic_gcd q r hqr)

/-- Stored interval correlation inherits the shared-gcd product-harmonic budget. -/
theorem norm_kloostermanCrossModulusCorrelation_Icc_le_productHarmonic_gcd
    (M q r : ℕ) (hqr : q ≠ r) (n k : ℤ) :
    ‖kloostermanCrossModulusCorrelation (Finset.Icc 1 M) q r n k‖ ≤
      ((q + 1).gcd (r + 1) : ℝ) *
        ((((q + 1) * (r + 1) : ℕ) : ℝ) *
          (1 + Real.log ((q + 1) * (r + 1)))) := by
  rw [kloostermanCrossModulusCorrelation_Icc_eq_terminalBlock_of_ne
    M q r hqr n k]
  simpa only [Nat.cast_mul, Nat.cast_add, Nat.cast_one] using
    norm_kloostermanNaturalCrossIntervalTerminalBlock_le_productHarmonic_gcd
      M (q + 1) (r + 1) (Nat.succ_ne_succ_iff.mpr hqr) (Int.cast n) (Int.cast k)

/-- Shifted modulus-pair budget using exact shared-gcd frequency multiplicity. -/
def kloostermanProductGcdHarmonicPairBudget (q r : ℕ) : ℝ :=
  ((q + 1).gcd (r + 1) : ℝ) *
    ((((q + 1) * (r + 1) : ℕ) : ℝ) *
      (1 + Real.log ((q + 1) * (r + 1))))

/-- Weighted distinct-modulus sum of the shared-gcd pair budgets. -/
def kloostermanDistinctModulusProductGcdHarmonicBudget
    (Q : Finset ℕ) (w : ℕ → ℂ) : ℝ :=
  ∑ q ∈ Q, ‖w q‖ * ∑ r ∈ Q.erase q, ‖w r‖ * kloostermanProductGcdHarmonicPairBudget q r

/-- Shared-gcd pair budget is nonnegative. -/
theorem kloostermanProductGcdHarmonicPairBudget_nonneg (q r : ℕ) :
    0 ≤ kloostermanProductGcdHarmonicPairBudget q r := by
  have hNnat : 1 ≤ (q + 1) * (r + 1) :=
    Nat.one_le_iff_ne_zero.mpr
      (Nat.mul_ne_zero (Nat.succ_ne_zero q) (Nat.succ_ne_zero r))
  have hN : (1 : ℝ) ≤ (((q + 1) * (r + 1) : ℕ) : ℝ) := by exact_mod_cast hNnat
  have hlog : 0 ≤ Real.log (((q + 1) * (r + 1) : ℕ) : ℝ) := Real.log_nonneg hN
  have hfactor : 0 ≤ 1 + Real.log (((q + 1) * (r + 1) : ℕ) : ℝ) := by
    linarith
  have hfactor' : 0 ≤ 1 + Real.log (((q : ℝ) + 1) * ((r : ℝ) + 1)) := by
    simpa only [Nat.cast_mul, Nat.cast_add, Nat.cast_one] using hfactor
  unfold kloostermanProductGcdHarmonicPairBudget
  exact mul_nonneg (Nat.cast_nonneg _)
    (mul_nonneg (Nat.cast_nonneg _) hfactor')

/-- Weighted distinct-modulus shared-gcd budget is nonnegative. -/
theorem kloostermanDistinctModulusProductGcdHarmonicBudget_nonneg
    (Q : Finset ℕ) (w : ℕ → ℂ) :
    0 ≤ kloostermanDistinctModulusProductGcdHarmonicBudget Q w := by
  unfold kloostermanDistinctModulusProductGcdHarmonicBudget
  apply Finset.sum_nonneg
  intro q hq
  apply mul_nonneg (norm_nonneg _)
  apply Finset.sum_nonneg
  intro r hr
  exact mul_nonneg (norm_nonneg _)
    (kloostermanProductGcdHarmonicPairBudget_nonneg q r)

/-- Every terminal distinct-modulus Gram entry obeys the shared-gcd budget. -/
theorem norm_kloostermanDistinctModulusTerminalGram_le_productHarmonic_gcd
    (M : ℕ) (Q : Finset ℕ) (w : ℕ → ℂ) (n k : ℕ) :
    ‖kloostermanDistinctModulusTerminalGram M Q w n k‖ ≤
      kloostermanDistinctModulusProductGcdHarmonicBudget Q w := by
  calc
    ‖kloostermanDistinctModulusTerminalGram M Q w n k‖ ≤
        ∑ q ∈ Q, ‖star (w q) *
          ∑ r ∈ Q.erase q, w r *
            kloostermanNaturalCrossIntervalTerminalBlock M (q + 1) (r + 1)
              (Int.cast (n : ℤ)) (Int.cast (k : ℤ))‖ := by
      unfold kloostermanDistinctModulusTerminalGram
      exact norm_sum_le _ _
    _ = ∑ q ∈ Q, ‖w q‖ * ‖∑ r ∈ Q.erase q, w r *
          kloostermanNaturalCrossIntervalTerminalBlock M (q + 1) (r + 1)
            (Int.cast (n : ℤ)) (Int.cast (k : ℤ))‖ := by
      apply Finset.sum_congr rfl
      intro q hq
      rw [norm_mul, norm_star]
    _ ≤ ∑ q ∈ Q, ‖w q‖ * ∑ r ∈ Q.erase q,
          ‖w r * kloostermanNaturalCrossIntervalTerminalBlock M (q + 1) (r + 1)
            (Int.cast (n : ℤ)) (Int.cast (k : ℤ))‖ := by
      apply Finset.sum_le_sum
      intro q hq
      gcongr
      exact norm_sum_le _ _
    _ = ∑ q ∈ Q, ‖w q‖ * ∑ r ∈ Q.erase q,
          ‖w r‖ * ‖kloostermanNaturalCrossIntervalTerminalBlock M (q + 1) (r + 1)
            (Int.cast (n : ℤ)) (Int.cast (k : ℤ))‖ := by
      apply Finset.sum_congr rfl
      intro q hq
      congr 1
      apply Finset.sum_congr rfl
      intro r hr
      rw [norm_mul]
    _ ≤ ∑ q ∈ Q, ‖w q‖ * ∑ r ∈ Q.erase q,
          ‖w r‖ * kloostermanProductGcdHarmonicPairBudget q r := by
      apply Finset.sum_le_sum
      intro q hq
      gcongr with r hr
      have hrq : r ≠ q := (Finset.mem_erase.mp hr).1
      simpa [kloostermanProductGcdHarmonicPairBudget,
        Nat.cast_mul, Nat.cast_add, Nat.cast_one] using
        norm_kloostermanNaturalCrossIntervalTerminalBlock_le_productHarmonic_gcd
          M (q + 1) (r + 1) (Ne.symm (Nat.succ_ne_succ_iff.mpr hrq))
            (Int.cast (n : ℤ)) (Int.cast (k : ℤ))
    _ = kloostermanDistinctModulusProductGcdHarmonicBudget Q w := rfl

/-- Stored distinct-modulus Gram entries inherit the shared-gcd budget. -/
theorem norm_kloostermanDistinctModulusGram_Icc_le_productHarmonic_gcd
    (M : ℕ) (Q : Finset ℕ) (w : ℕ → ℂ) (n k : ℕ) :
    ‖kloostermanDistinctModulusGram Q w (Finset.Icc 1 M) n k‖ ≤
      kloostermanDistinctModulusProductGcdHarmonicBudget Q w := by
  rw [kloostermanDistinctModulusGram_Icc_eq_terminalGram]
  exact norm_kloostermanDistinctModulusTerminalGram_le_productHarmonic_gcd M Q w n k

/-- Full source quadratic bounded by squared source `ℓ¹` mass and the shared-gcd budget. -/
theorem norm_kloostermanDistinctModulusTerminalGramQuadratic_le_productHarmonic_gcd
    (M : ℕ) (Q : Finset ℕ) (w : ℕ → ℂ)
    (B : Finset ℕ) (b : ℕ → ℂ) :
    ‖kloostermanDistinctModulusTerminalGramQuadratic M Q w B b‖ ≤
      (∑ n ∈ B, ‖b n‖) ^ 2 *
        kloostermanDistinctModulusProductGcdHarmonicBudget Q w := by
  calc
    ‖kloostermanDistinctModulusTerminalGramQuadratic M Q w B b‖ ≤
        ∑ n ∈ B, ‖star (b n) * ∑ k ∈ B, b k *
          kloostermanDistinctModulusTerminalGram M Q w n k‖ := by
      unfold kloostermanDistinctModulusTerminalGramQuadratic
      exact norm_sum_le _ _
    _ = ∑ n ∈ B, ‖b n‖ * ‖∑ k ∈ B, b k *
          kloostermanDistinctModulusTerminalGram M Q w n k‖ := by
      apply Finset.sum_congr rfl
      intro n hn
      rw [norm_mul, norm_star]
    _ ≤ ∑ n ∈ B, ‖b n‖ * ∑ k ∈ B,
          ‖b k * kloostermanDistinctModulusTerminalGram M Q w n k‖ := by
      apply Finset.sum_le_sum
      intro n hn
      gcongr
      exact norm_sum_le _ _
    _ = ∑ n ∈ B, ‖b n‖ * ∑ k ∈ B,
          ‖b k‖ * ‖kloostermanDistinctModulusTerminalGram M Q w n k‖ := by
      apply Finset.sum_congr rfl
      intro n hn
      congr 1
      apply Finset.sum_congr rfl
      intro k hk
      rw [norm_mul]
    _ ≤ ∑ n ∈ B, ‖b n‖ * ∑ k ∈ B,
          ‖b k‖ * kloostermanDistinctModulusProductGcdHarmonicBudget Q w := by
      apply Finset.sum_le_sum
      intro n hn
      gcongr with k hk
      exact norm_kloostermanDistinctModulusTerminalGram_le_productHarmonic_gcd
        M Q w n k
    _ = (∑ n ∈ B, ‖b n‖) ^ 2 *
        kloostermanDistinctModulusProductGcdHarmonicBudget Q w := by
      rw [← Finset.sum_mul, ← Finset.sum_mul]
      ring

/-- Erased source off-diagonal obeys the same shared-gcd quadratic budget. -/
theorem norm_kloostermanDistinctModulusTerminalGramOffDiagonal_le_productHarmonic_gcd
    (M : ℕ) (Q : Finset ℕ) (w : ℕ → ℂ)
    (B : Finset ℕ) (b : ℕ → ℂ) :
    ‖kloostermanDistinctModulusTerminalGramOffDiagonal M Q w B b‖ ≤
      (∑ n ∈ B, ‖b n‖) ^ 2 *
        kloostermanDistinctModulusProductGcdHarmonicBudget Q w := by
  calc
    ‖kloostermanDistinctModulusTerminalGramOffDiagonal M Q w B b‖ ≤
        ∑ n ∈ B, ‖star (b n) * ∑ k ∈ B.erase n, b k *
          kloostermanDistinctModulusTerminalGram M Q w n k‖ := by
      unfold kloostermanDistinctModulusTerminalGramOffDiagonal
      exact norm_sum_le _ _
    _ = ∑ n ∈ B, ‖b n‖ * ‖∑ k ∈ B.erase n, b k *
          kloostermanDistinctModulusTerminalGram M Q w n k‖ := by
      apply Finset.sum_congr rfl
      intro n hn
      rw [norm_mul, norm_star]
    _ ≤ ∑ n ∈ B, ‖b n‖ * ∑ k ∈ B.erase n,
          ‖b k * kloostermanDistinctModulusTerminalGram M Q w n k‖ := by
      apply Finset.sum_le_sum
      intro n hn
      gcongr
      exact norm_sum_le _ _
    _ = ∑ n ∈ B, ‖b n‖ * ∑ k ∈ B.erase n,
          ‖b k‖ * ‖kloostermanDistinctModulusTerminalGram M Q w n k‖ := by
      apply Finset.sum_congr rfl
      intro n hn
      congr 1
      apply Finset.sum_congr rfl
      intro k hk
      rw [norm_mul]
    _ ≤ ∑ n ∈ B, ‖b n‖ * ∑ k ∈ B,
          ‖b k‖ * kloostermanDistinctModulusProductGcdHarmonicBudget Q w := by
      apply Finset.sum_le_sum
      intro n hn
      gcongr
      calc
        (∑ k ∈ B.erase n,
            ‖b k‖ * ‖kloostermanDistinctModulusTerminalGram M Q w n k‖) ≤
            ∑ k ∈ B.erase n,
              ‖b k‖ * kloostermanDistinctModulusProductGcdHarmonicBudget Q w := by
          gcongr with k hk
          exact norm_kloostermanDistinctModulusTerminalGram_le_productHarmonic_gcd
            M Q w n k
        _ ≤ ∑ k ∈ B,
            ‖b k‖ * kloostermanDistinctModulusProductGcdHarmonicBudget Q w := by
          rw [← Finset.sum_erase_add _ _ hn]
          exact le_add_of_nonneg_right
            (mul_nonneg (norm_nonneg _)
              (kloostermanDistinctModulusProductGcdHarmonicBudget_nonneg Q w))
    _ = (∑ n ∈ B, ‖b n‖) ^ 2 *
        kloostermanDistinctModulusProductGcdHarmonicBudget Q w := by
      rw [← Finset.sum_mul, ← Finset.sum_mul]
      ring

end

end RHTower.Sieve
