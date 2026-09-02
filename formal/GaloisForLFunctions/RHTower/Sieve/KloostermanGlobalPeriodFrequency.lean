import GaloisForLFunctions.RHTower.Sieve.KloostermanTerminalOrbitParsevalSchur

/-!
# One common period for all terminal Kloosterman phases

For a finite stored modulus family `Q`, the least common multiple of all moduli
`q + 1` is a positive common period.  Every off-diagonal cross phase embeds as a nonzero
frequency in this single cyclic group, and its pairwise lcm-terminal orbit is
exactly the orbit at that global frequency.

This is the lossless finite-frequency carrier needed to postpone absolute
values until after the signed modulus sum.  No spectral estimate is assumed.
-/

open scoped BigOperators ComplexConjugate
open Complex Finset

namespace RHTower.Sieve

noncomputable section

/-- Common positive period containing every stored Kloosterman modulus. -/
def kloostermanGlobalPeriod (Q : Finset ℕ) : ℕ :=
  Q.lcm (fun q => q + 1)

theorem kloostermanGlobalPeriod_pos (Q : Finset ℕ) :
    0 < kloostermanGlobalPeriod Q := by
  unfold kloostermanGlobalPeriod
  classical
  induction Q using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
      rw [Finset.lcm_insert]
      exact Nat.lcm_pos (Nat.succ_pos a) ih

instance kloostermanGlobalPeriodNeZero (Q : Finset ℕ) :
    NeZero (kloostermanGlobalPeriod Q) :=
  ⟨(kloostermanGlobalPeriod_pos Q).ne'⟩

/-- The standard additive character separates every frequency in a positive cyclic group. -/
theorem stdAddChar_injective
    (P : ℕ) [NeZero P] :
    Function.Injective (fun z : ZMod P => ZMod.stdAddChar z) := by
  intro z w h
  change ZMod.stdAddChar z = ZMod.stdAddChar w at h
  have hw : ZMod.stdAddChar w ≠ (0 : ℂ) :=
    norm_ne_zero_iff.mp (by simp)
  have hchar : ZMod.stdAddChar (z - w) = (1 : ℂ) := by
    rw [AddChar.map_sub_eq_div, h]
    exact div_self hw
  exact sub_eq_zero.mp ((stdAddChar_eq_one_iff P (z - w)).mp hchar)

/-- Every stored modulus divides the common least-common-multiple period. -/
theorem succ_dvd_kloostermanGlobalPeriod
    (Q : Finset ℕ) {q : ℕ} (hq : q ∈ Q) :
    q + 1 ∣ kloostermanGlobalPeriod Q := by
  unfold kloostermanGlobalPeriod
  exact Finset.dvd_lcm hq

/-- Every pairwise least common multiple divides the family least common multiple. -/
theorem lcm_succ_dvd_kloostermanGlobalPeriod
    (Q : Finset ℕ) {q r : ℕ} (hq : q ∈ Q) (hr : r ∈ Q) :
    Nat.lcm (q + 1) (r + 1) ∣ kloostermanGlobalPeriod Q := by
  exact Nat.lcm_dvd
    (succ_dvd_kloostermanGlobalPeriod Q hq)
    (succ_dvd_kloostermanGlobalPeriod Q hr)

/-- Cross phase embedded in the least common multiple of the whole modulus family. -/
def kloostermanGlobalCrossPhaseFrequency
    (Q : Finset ℕ) (q r : ℕ)
    (x : (ZMod (q + 1))ˣ) (y : (ZMod (r + 1))ˣ) :
    ZMod (kloostermanGlobalPeriod Q) :=
  ((((kloostermanGlobalPeriod Q / (r + 1) : ℕ) : ℤ) *
      ((y : ZMod (r + 1)).val : ℤ) -
    ((kloostermanGlobalPeriod Q / (q + 1) : ℕ) : ℤ) *
      ((x : ZMod (q + 1)).val : ℤ) : ℤ) :
        ZMod (kloostermanGlobalPeriod Q))

/-- The global-period frequency carries the original cross phase. -/
theorem kloostermanGlobalCrossPhaseFrequency_phase
    (Q : Finset ℕ) (q r : ℕ) (hq : q ∈ Q) (hr : r ∈ Q)
    (x : (ZMod (q + 1))ˣ) (y : (ZMod (r + 1))ˣ) :
    ZMod.stdAddChar (kloostermanGlobalCrossPhaseFrequency Q q r x y) =
      kloostermanCrossPhaseRatio (q + 1) (r + 1) x y := by
  unfold kloostermanGlobalCrossPhaseFrequency kloostermanCrossPhaseRatio
  rw [ZMod.stdAddChar_coe]
  rw [stdAddChar_eq_exp_val, stdAddChar_eq_exp_val]
  rw [← starRingEnd_apply, ← Complex.exp_conj]
  simp only [map_mul, Complex.conj_ofReal, Complex.conj_I]
  rw [← Complex.exp_add]
  congr 1
  have hqdiv : (q + 1) * (kloostermanGlobalPeriod Q / (q + 1)) =
      kloostermanGlobalPeriod Q :=
    Nat.mul_div_cancel' (succ_dvd_kloostermanGlobalPeriod Q hq)
  have hrdiv : (r + 1) * (kloostermanGlobalPeriod Q / (r + 1)) =
      kloostermanGlobalPeriod Q :=
    Nat.mul_div_cancel' (succ_dvd_kloostermanGlobalPeriod Q hr)
  simp only [Int.cast_sub, Int.cast_mul, Int.cast_natCast,
    Complex.ofReal_mul, Complex.ofReal_div, Complex.ofReal_natCast]
  have hqC : ((q + 1 : ℕ) : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.succ_ne_zero q)
  have hrC : ((r + 1 : ℕ) : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.succ_ne_zero r)
  have hPC : ((kloostermanGlobalPeriod Q : ℕ) : ℂ) ≠ 0 := by
    exact Nat.cast_ne_zero.mpr (NeZero.ne (kloostermanGlobalPeriod Q))
  have hqdivC :
      (((kloostermanGlobalPeriod Q / (q + 1) : ℕ) : ℂ) * (q + 1 : ℂ)) =
        (kloostermanGlobalPeriod Q : ℂ) := by
    exact_mod_cast (by simpa [Nat.mul_comm] using hqdiv)
  have hrdivC :
      (((kloostermanGlobalPeriod Q / (r + 1) : ℕ) : ℂ) * (r + 1 : ℂ)) =
        (kloostermanGlobalPeriod Q : ℂ) := by
    exact_mod_cast (by simpa [Nat.mul_comm] using hrdiv)
  field_simp [hqC, hrC, hPC]
  calc
    _ = 2 *
        (((y : ZMod (r + 1)).val : ℂ) * (q + 1 : ℂ) *
            (((kloostermanGlobalPeriod Q / (r + 1) : ℕ) : ℂ) *
              (r + 1 : ℂ)) -
          ((x : ZMod (q + 1)).val : ℂ) * (r + 1 : ℂ) *
            (((kloostermanGlobalPeriod Q / (q + 1) : ℕ) : ℂ) *
              (q + 1 : ℂ))) := by
      push_cast
      ring
    _ = _ := by rw [hqdivC, hrdivC]; norm_num; ring

/-- Two stored cross-phase tuples collide in the common frequency space exactly when their
original complex phase ratios agree. -/
theorem kloostermanGlobalCrossPhaseFrequency_eq_iff
    (Q : Finset ℕ) (q r q' r' : ℕ)
    (hq : q ∈ Q) (hr : r ∈ Q) (hq' : q' ∈ Q) (hr' : r' ∈ Q)
    (x : (ZMod (q + 1))ˣ) (y : (ZMod (r + 1))ˣ)
    (x' : (ZMod (q' + 1))ˣ) (y' : (ZMod (r' + 1))ˣ) :
    kloostermanGlobalCrossPhaseFrequency Q q r x y =
        kloostermanGlobalCrossPhaseFrequency Q q' r' x' y' ↔
      kloostermanCrossPhaseRatio (q + 1) (r + 1) x y =
        kloostermanCrossPhaseRatio (q' + 1) (r' + 1) x' y' := by
  constructor
  · intro h
    have hchar := congrArg
      (fun z : ZMod (kloostermanGlobalPeriod Q) =>
        (ZMod.stdAddChar z : ℂ)) h
    rw [kloostermanGlobalCrossPhaseFrequency_phase Q q r hq hr x y,
      kloostermanGlobalCrossPhaseFrequency_phase Q q' r' hq' hr' x' y'] at hchar
    exact hchar
  · intro h
    apply stdAddChar_injective (kloostermanGlobalPeriod Q)
    change ZMod.stdAddChar (kloostermanGlobalCrossPhaseFrequency Q q r x y) =
      ZMod.stdAddChar (kloostermanGlobalCrossPhaseFrequency Q q' r' x' y')
    rw [kloostermanGlobalCrossPhaseFrequency_phase Q q r hq hr x y,
      kloostermanGlobalCrossPhaseFrequency_phase Q q' r' hq' hr' x' y']
    exact h

/-- Unequal stored moduli give a nonzero common-period frequency. -/
theorem kloostermanGlobalCrossPhaseFrequency_ne_zero
    (Q : Finset ℕ) (q r : ℕ) (hq : q ∈ Q) (hr : r ∈ Q)
    (hqr : q ≠ r)
    (x : (ZMod (q + 1))ˣ) (y : (ZMod (r + 1))ˣ) :
    kloostermanGlobalCrossPhaseFrequency Q q r x y ≠ 0 := by
  intro hzero
  have hphase := kloostermanGlobalCrossPhaseFrequency_phase Q q r hq hr x y
  rw [hzero] at hphase
  have hone : kloostermanCrossPhaseRatio (q + 1) (r + 1) x y = 1 := by
    simpa using hphase.symm
  exact (kloostermanCrossPhaseRatio_ne_one_of_ne
    (q + 1) (r + 1) (Nat.succ_ne_succ_iff.mpr hqr) x y) hone

private theorem sum_range_eq_nsmul_add_mod_of_add_periodic_global
    {A : Type*} [AddCommMonoid A] (f : ℕ → A) (M P : ℕ)
    (hperiodic : ∀ a j : ℕ, f (a + P * j) = f a) :
    (∑ m ∈ Finset.range M, f m) =
      (M / P) • (∑ a ∈ Finset.range P, f a) +
        ∑ a ∈ Finset.range (M % P), f a := by
  conv_lhs => rw [← Nat.div_add_mod M P]
  rw [Finset.sum_range_add]
  have hblocks :
      (∑ m ∈ Finset.range ((M / P) * P), f m) =
        (M / P) • ∑ a ∈ Finset.range P, f a := by
    rw [← Fin.sum_univ_eq_sum_range]
    let e : Fin (M / P) × Fin P ≃ Fin ((M / P) * P) := finProdFinEquiv
    calc
      (∑ m : Fin ((M / P) * P), f m.val) =
          ∑ p : Fin (M / P) × Fin P,
            f (p.2.val + P * p.1.val) := by
        rw [show (∑ m : Fin ((M / P) * P), f m.val) =
            ∑ p : Fin (M / P) × Fin P, f (e p).val from
          (e.sum_comp (fun m : Fin ((M / P) * P) => f m.val)).symm]
        apply Fintype.sum_congr
        intro p
        simp [e, finProdFinEquiv]
      _ = ∑ _j : Fin (M / P), ∑ a : Fin P, f a.val := by
        rw [Fintype.sum_prod_type]
        apply Fintype.sum_congr
        intro j
        apply Fintype.sum_congr
        intro a
        exact hperiodic a.val j.val
      _ = (M / P) • ∑ a ∈ Finset.range P, f a := by
        rw [← Fin.sum_univ_eq_sum_range]
        simp
  have hblocks' :
      (∑ m ∈ Finset.range (P * (M / P)), f m) =
        (M / P) • ∑ a ∈ Finset.range P, f a := by
    simpa [Nat.mul_comm] using hblocks
  rw [hblocks']
  apply congrArg (fun z => (M / P) • (∑ a ∈ Finset.range P, f a) + z)
  apply Finset.sum_congr rfl
  intro a ha
  rw [Nat.add_comm (P * (M / P)) a]
  exact hperiodic a (M / P)

/-- A nontrivial finite-order phase orbit depends only on length modulo its period. -/
theorem sum_range_pow_succ_eq_sum_mod
    (ζ : ℂ) (M P : ℕ) (hpow : ζ ^ P = 1) (hne : ζ ≠ 1) :
    (∑ i ∈ Finset.range M, ζ ^ (i + 1)) =
      ∑ i ∈ Finset.range (M % P), ζ ^ (i + 1) := by
  let f : ℕ → ℂ := fun i => ζ ^ (i + 1)
  have hperiodic : ∀ a j : ℕ, f (a + P * j) = f a := by
    intro a j
    unfold f
    rw [show a + P * j + 1 = (a + 1) + P * j by omega,
      pow_add, pow_mul, hpow, one_pow, mul_one]
  have hdecomp := sum_range_eq_nsmul_add_mod_of_add_periodic_global
    f M P hperiodic
  have hcomplete : (∑ a ∈ Finset.range P, f a) = 0 := by
    unfold f
    calc
      (∑ a ∈ Finset.range P, ζ ^ (a + 1)) =
          ζ * ∑ a ∈ Finset.range P, ζ ^ a := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro a ha
        rw [pow_succ']
      _ = 0 := by rw [sum_range_pow_eq_zero hpow hne, mul_zero]
  rw [hcomplete, nsmul_zero, zero_add] at hdecomp
  exact hdecomp

/-- Common-period geometric orbit at one global frequency. -/
def kloostermanGlobalTerminalOrbit
    (M : ℕ) (Q : Finset ℕ) (z : ZMod (kloostermanGlobalPeriod Q)) : ℂ :=
  ∑ i ∈ Finset.range (M % kloostermanGlobalPeriod Q),
    (ZMod.stdAddChar z) ^ (i + 1)

private theorem stdAddChar_pow_modulus_eq_one
    (P : ℕ) [NeZero P] (z : ZMod P) :
    (ZMod.stdAddChar z) ^ P = 1 := by
  rw [← stdAddChar_nsmul_eq_pow]
  simp

/-- Every unequal-modulus terminal orbit is exactly its common-period embedded orbit. -/
theorem kloostermanTerminalOrbit_eq_globalTerminalOrbit
    (M : ℕ) (Q : Finset ℕ) (q r : ℕ)
    (hq : q ∈ Q) (hr : r ∈ Q) (hqr : q ≠ r)
    (x : (ZMod (q + 1))ˣ) (y : (ZMod (r + 1))ˣ) :
    kloostermanTerminalOrbit M (q + 1) (r + 1) x y =
      kloostermanGlobalTerminalOrbit M Q
        (kloostermanGlobalCrossPhaseFrequency Q q r x y) := by
  let ζ : ℂ := kloostermanCrossPhaseRatio (q + 1) (r + 1) x y
  have hζne : ζ ≠ 1 :=
    kloostermanCrossPhaseRatio_ne_one_of_ne
      (q + 1) (r + 1) (Nat.succ_ne_succ_iff.mpr hqr) x y
  letI : NeZero (Nat.lcm (q + 1) (r + 1)) :=
    ⟨(Nat.lcm_pos (Nat.succ_pos q) (Nat.succ_pos r)).ne'⟩
  have hζlcm : ζ ^ Nat.lcm (q + 1) (r + 1) = 1 := by
    rw [show ζ = ZMod.stdAddChar
        (kloostermanLcmCrossPhaseFrequency (q + 1) (r + 1) x y) by
      exact (kloostermanLcmCrossPhaseFrequency_phase
        (q + 1) (r + 1) x y).symm]
    exact stdAddChar_pow_modulus_eq_one _ _
  have hlocal := sum_range_pow_succ_eq_sum_mod ζ M
    (Nat.lcm (q + 1) (r + 1)) hζlcm hζne
  have hglobalPhase :
      ZMod.stdAddChar (kloostermanGlobalCrossPhaseFrequency Q q r x y) = ζ :=
    kloostermanGlobalCrossPhaseFrequency_phase Q q r hq hr x y
  have hglobalNe :
      ZMod.stdAddChar (kloostermanGlobalCrossPhaseFrequency Q q r x y) ≠ 1 := by
    rw [hglobalPhase]
    exact hζne
  have hglobal := sum_range_pow_succ_eq_sum_mod
    (ZMod.stdAddChar (kloostermanGlobalCrossPhaseFrequency Q q r x y)) M
      (kloostermanGlobalPeriod Q)
      (stdAddChar_pow_modulus_eq_one _ _) hglobalNe
  unfold kloostermanTerminalOrbit kloostermanGlobalTerminalOrbit
  calc
    (∑ i ∈ Finset.range (M % Nat.lcm (q + 1) (r + 1)), ζ ^ (i + 1)) =
        ∑ i ∈ Finset.range M, ζ ^ (i + 1) := hlocal.symm
    _ = ∑ i ∈ Finset.range (M % kloostermanGlobalPeriod Q),
        (ZMod.stdAddChar
          (kloostermanGlobalCrossPhaseFrequency Q q r x y)) ^ (i + 1) := by
      simpa only [hglobalPhase] using hglobal

end

end RHTower.Sieve
