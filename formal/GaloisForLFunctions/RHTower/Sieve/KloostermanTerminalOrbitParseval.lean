import GaloisForLFunctions.RHTower.Sieve.KloostermanProductFrequencyGcdBound
import GaloisForLFunctions.RHTower.Sieve.FiniteAdditiveLargeSieve
import GaloisForLFunctions.RHTower.Sieve.KloostermanTerminalSourceFourier
import GaloisForLFunctions.RHTower.Sieve.KloostermanTerminalOrbitEnergy
import GaloisForLFunctions.RHTower.Sieve.KloostermanSourceResidueMultiplicity

/-!
# Exact lcm-period Parseval energy for terminal Kloosterman orbits

This module encodes each cross phase at its exact `lcm q r` period.  A frequency
fibre has cardinality at most `gcd q r`, while finite Parseval contributes
`lcm q r`; the identity `gcd q r * lcm q r = q * r` therefore removes both the
harmonic logarithm and the shared-gcd overcount from the terminal-orbit energy.

The resulting bound is propagated through source residues, weighted Gram pairs,
and literal interval receivers.  It is unconditional finite Fourier
cancellation, but does not supply the signed modulus-average Kuznetsov saving
still needed by the Route E cards.
-/

open scoped BigOperators ComplexConjugate
open Complex Finset

namespace RHTower.Sieve

noncomputable section

/-- Exact Parseval energy of a consecutive additive-character orbit. -/
theorem sum_normSq_stdAddChar_pow_range_eq
    (N L : ℕ) [NeZero N] (hL : L ≤ N) :
    (∑ z : ZMod N,
      ‖∑ i ∈ Finset.range L, (ZMod.stdAddChar z) ^ (i + 1)‖ ^ 2) =
      (N : ℝ) * L := by
  let f : Fin L → ZMod N := fun i => (i.val : ZMod N)
  have hf : Function.Injective f := by
    intro i j hij
    apply Fin.ext
    have hiN : i.val < N := lt_of_lt_of_le i.isLt hL
    have hjN : j.val < N := lt_of_lt_of_le j.isLt hL
    have hval := congrArg ZMod.val hij
    simpa [f, ZMod.val_natCast, Nat.mod_eq_of_lt hiN,
      Nat.mod_eq_of_lt hjN] using hval
  have hparseval :=
    sum_normSq_weighted_stdAddChar_mul_of_injective
      N f hf (fun _ : Fin L => (1 : ℂ))
  have hinner (z : ZMod N) :
      (∑ i : Fin L, (1 : ℂ) * ZMod.stdAddChar (z * f i)) =
        ∑ i : Fin L, (ZMod.stdAddChar z) ^ i.val := by
    apply Finset.sum_congr rfl
    intro i hi
    rw [one_mul, ← stdAddChar_nsmul_eq_pow N i.val z]
    congr 1
    simp [f, nsmul_eq_mul, mul_comm]
  have hunshifted :
      (∑ z : ZMod N,
        Complex.normSq (∑ i : Fin L, (ZMod.stdAddChar z) ^ i.val)) =
        (N : ℝ) * L := by
    calc
      _ = ∑ z : ZMod N,
          Complex.normSq
            (∑ i : Fin L, (1 : ℂ) * ZMod.stdAddChar (z * f i)) := by
        apply Finset.sum_congr rfl
        intro z hz
        rw [hinner]
      _ = (N : ℝ) * ∑ _i : Fin L, Complex.normSq (1 : ℂ) := hparseval
      _ = (N : ℝ) * L := by simp
  calc
    (∑ z : ZMod N,
      ‖∑ i ∈ Finset.range L, (ZMod.stdAddChar z) ^ (i + 1)‖ ^ 2) =
        ∑ z : ZMod N,
          Complex.normSq (∑ i : Fin L, (ZMod.stdAddChar z) ^ i.val) := by
      apply Finset.sum_congr rfl
      intro z hz
      have hfactor :
          (∑ i ∈ Finset.range L, (ZMod.stdAddChar z) ^ (i + 1)) =
            ZMod.stdAddChar z *
              ∑ i ∈ Finset.range L, (ZMod.stdAddChar z) ^ i := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i hi
        rw [pow_succ']
      rw [hfactor, ← Complex.normSq_eq_norm_sq, Complex.normSq_mul]
      have hchar : Complex.normSq (ZMod.stdAddChar z) = 1 := by
        rw [Complex.normSq_eq_norm_sq]
        simp
      rw [hchar, one_mul]
      rw [Fin.sum_univ_eq_sum_range]
    _ = (N : ℝ) * L := hunshifted

local instance kloostermanLcmNeZero
    (q r : ℕ) [NeZero q] [NeZero r] : NeZero (Nat.lcm q r) :=
  ⟨(Nat.lcm_pos (Nat.pos_of_ne_zero (NeZero.ne q))
    (Nat.pos_of_ne_zero (NeZero.ne r))).ne'⟩

/-- Cross phase represented on its exact least-common-multiple period. -/
def kloostermanLcmCrossPhaseFrequency
    (q r : ℕ) [NeZero q] [NeZero r]
    (x : (ZMod q)ˣ) (y : (ZMod r)ˣ) : ZMod (Nat.lcm q r) :=
  ((((Nat.lcm q r / r : ℕ) : ℤ) * ((y : ZMod r).val : ℤ) -
    ((Nat.lcm q r / q : ℕ) : ℤ) * ((x : ZMod q).val : ℤ) : ℤ) :
      ZMod (Nat.lcm q r))

/-- Exact-period frequency carries the original cross-phase ratio. -/
theorem kloostermanLcmCrossPhaseFrequency_phase
    (q r : ℕ) [NeZero q] [NeZero r]
    (x : (ZMod q)ˣ) (y : (ZMod r)ˣ) :
    ZMod.stdAddChar (kloostermanLcmCrossPhaseFrequency q r x y) =
      kloostermanCrossPhaseRatio q r x y := by
  unfold kloostermanLcmCrossPhaseFrequency kloostermanCrossPhaseRatio
  rw [ZMod.stdAddChar_coe]
  rw [stdAddChar_eq_exp_val, stdAddChar_eq_exp_val]
  rw [← starRingEnd_apply, ← Complex.exp_conj]
  simp only [map_mul, Complex.conj_ofReal, Complex.conj_I]
  rw [← Complex.exp_add]
  congr 1
  have hqdiv : q * (Nat.lcm q r / q) = Nat.lcm q r :=
    Nat.mul_div_cancel' (Nat.dvd_lcm_left q r)
  have hrdiv : r * (Nat.lcm q r / r) = Nat.lcm q r :=
    Nat.mul_div_cancel' (Nat.dvd_lcm_right q r)
  simp only [Int.cast_sub, Int.cast_mul, Int.cast_natCast,
    Complex.ofReal_mul, Complex.ofReal_div, Complex.ofReal_natCast]
  have hqC : (q : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne q)
  have hrC : (r : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne r)
  have hNC : ((Nat.lcm q r : ℕ) : ℂ) ≠ 0 := by
    exact Nat.cast_ne_zero.mpr (NeZero.ne (Nat.lcm q r))
  have hqdivC : (((Nat.lcm q r / q : ℕ) : ℂ) * (q : ℂ)) =
      (Nat.lcm q r : ℂ) := by
    exact_mod_cast (by simpa [Nat.mul_comm] using hqdiv)
  have hrdivC : (((Nat.lcm q r / r : ℕ) : ℂ) * (r : ℂ)) =
      (Nat.lcm q r : ℂ) := by
    exact_mod_cast (by simpa [Nat.mul_comm] using hrdiv)
  field_simp [hqC, hrC, hNC]
  calc
    _ = 2 *
        (((y : ZMod r).val : ℂ) * (q : ℂ) *
            (((Nat.lcm q r / r : ℕ) : ℂ) * (r : ℂ)) -
          ((x : ZMod q).val : ℂ) * (r : ℂ) *
            (((Nat.lcm q r / q : ℕ) : ℂ) * (q : ℂ))) := by ring
    _ = _ := by rw [hqdivC, hrdivC]; norm_num; ring

/-- Exact-period cross-frequency fibre. -/
def kloostermanLcmCrossPhaseFrequencyFibre
    (q r : ℕ) [NeZero q] [NeZero r] (z : ZMod (Nat.lcm q r)) :=
  {p : (ZMod q)ˣ × (ZMod r)ˣ //
    kloostermanLcmCrossPhaseFrequency q r p.1 p.2 = z}

noncomputable instance kloostermanLcmCrossPhaseFrequencyFibreFintype
    (q r : ℕ) [NeZero q] [NeZero r] (z : ZMod (Nat.lcm q r)) :
    Fintype (kloostermanLcmCrossPhaseFrequencyFibre q r z) := by
  classical
  unfold kloostermanLcmCrossPhaseFrequencyFibre
  infer_instance

/-- Every exact-period cross-frequency fibre has at most the shared gcd many elements. -/
theorem card_kloostermanLcmCrossPhaseFrequencyFibre_le_gcd
    (q r : ℕ) [NeZero q] [NeZero r] (z : ZMod (Nat.lcm q r)) :
    Fintype.card (kloostermanLcmCrossPhaseFrequencyFibre q r z) ≤ q.gcd r := by
  classical
  letI : NeZero (q * r) :=
    ⟨Nat.mul_ne_zero (NeZero.ne q) (NeZero.ne r)⟩
  let label : kloostermanLcmCrossPhaseFrequencyFibre q r z → Fin (q.gcd r) :=
    fun p => kloostermanProductGcdSliceLabel q r p.1
  have hinj : Function.Injective label := by
    intro p p' hlabel
    apply Subtype.ext
    apply kloostermanProductCrossPhaseFrequency_injective_on_gcdSlice
      q r p.1 p'.1 hlabel
    have hred : kloostermanLcmCrossPhaseFrequency q r p.1.1 p.1.2 =
        kloostermanLcmCrossPhaseFrequency q r p'.1.1 p'.1.2 :=
      p.2.trans p'.2.symm
    have hratio : kloostermanCrossPhaseRatio q r p.1.1 p.1.2 =
        kloostermanCrossPhaseRatio q r p'.1.1 p'.1.2 := by
      rw [← kloostermanLcmCrossPhaseFrequency_phase,
        ← kloostermanLcmCrossPhaseFrequency_phase]
      exact congrArg ZMod.stdAddChar hred
    have hchar :
        ZMod.stdAddChar
            (kloostermanProductCrossPhaseFrequency q r p.1.1 p.1.2) =
          ZMod.stdAddChar
            (kloostermanProductCrossPhaseFrequency q r p'.1.1 p'.1.2) := by
      rw [kloostermanProductCrossPhaseFrequency_phase,
        kloostermanProductCrossPhaseFrequency_phase]
      exact hratio
    have hdiff : ZMod.stdAddChar
        (kloostermanProductCrossPhaseFrequency q r p.1.1 p.1.2 -
          kloostermanProductCrossPhaseFrequency q r p'.1.1 p'.1.2) = 1 := by
      rw [AddChar.map_sub_eq_div, hchar]
      exact div_self (norm_ne_zero_iff.mp (by simp))
    exact sub_eq_zero.mp ((stdAddChar_eq_one_iff (q * r) _).mp hdiff)
  simpa [label] using Fintype.card_le_of_injective label hinj

/-- Exact-period fibre multiplicity plus Parseval removes both the harmonic logarithm and the
spurious shared-gcd factor from total squared terminal-orbit energy. -/
theorem sum_kloostermanTerminalOrbit_sq_le_lcmParseval
    (M q r : ℕ) [NeZero q] [NeZero r] :
    (∑ x : (ZMod q)ˣ, ∑ y : (ZMod r)ˣ,
      ‖kloostermanTerminalOrbit M q r x y‖ ^ 2) ≤
      (((q * r : ℕ) : ℝ) * (M % Nat.lcm q r : ℕ)) := by
  classical
  let L : ℕ := M % Nat.lcm q r
  let f : (ZMod q)ˣ × (ZMod r)ˣ → ZMod (Nat.lcm q r) := fun p =>
    kloostermanLcmCrossPhaseFrequency q r p.1 p.2
  have hlcm0 : 0 < Nat.lcm q r :=
    Nat.lcm_pos (Nat.pos_of_ne_zero (NeZero.ne q))
      (Nat.pos_of_ne_zero (NeZero.ne r))
  have hLN : L ≤ Nat.lcm q r := (Nat.mod_lt M hlcm0).le
  have hfibre (z : ZMod (Nat.lcm q r)) :
      Fintype.card {p : (ZMod q)ˣ × (ZMod r)ˣ // f p = z} ≤ q.gcd r := by
    let e : {p : (ZMod q)ˣ × (ZMod r)ˣ // f p = z} →
        kloostermanLcmCrossPhaseFrequencyFibre q r z := fun p =>
      ⟨p.1, p.2⟩
    have he : Function.Injective e := by
      intro p p' h
      exact Subtype.ext (congrArg Subtype.val h)
    exact le_trans (Fintype.card_le_of_injective e he)
      (card_kloostermanLcmCrossPhaseFrequencyFibre_le_gcd q r z)
  have horbit (p : (ZMod q)ˣ × (ZMod r)ˣ) :
      ‖kloostermanTerminalOrbit M q r p.1 p.2‖ ^ 2 =
        ‖∑ i ∈ Finset.range L,
          (ZMod.stdAddChar (f p)) ^ (i + 1)‖ ^ 2 := by
    unfold kloostermanTerminalOrbit
    change ‖∑ i ∈ Finset.range L,
      (kloostermanCrossPhaseRatio q r p.1 p.2) ^ (i + 1)‖ ^ 2 = _
    rw [kloostermanLcmCrossPhaseFrequency_phase]
  calc
    (∑ x : (ZMod q)ˣ, ∑ y : (ZMod r)ˣ,
      ‖kloostermanTerminalOrbit M q r x y‖ ^ 2) =
        ∑ p : (ZMod q)ˣ × (ZMod r)ˣ,
          ‖∑ i ∈ Finset.range L,
            (ZMod.stdAddChar (f p)) ^ (i + 1)‖ ^ 2 := by
      rw [Fintype.sum_prod_type]
      apply Finset.sum_congr rfl
      intro x hx
      apply Finset.sum_congr rfl
      intro y hy
      exact horbit (x, y)
    _ = ∑ z : ZMod (Nat.lcm q r),
        ∑ p : {p : (ZMod q)ˣ × (ZMod r)ˣ // f p = z},
          ‖∑ i ∈ Finset.range L,
            (ZMod.stdAddChar (f p.1)) ^ (i + 1)‖ ^ 2 := by
      exact (Fintype.sum_fiberwise f (fun p =>
        ‖∑ i ∈ Finset.range L,
          (ZMod.stdAddChar (f p)) ^ (i + 1)‖ ^ 2)).symm
    _ ≤ ∑ z : ZMod (Nat.lcm q r),
        (q.gcd r : ℝ) *
          ‖∑ i ∈ Finset.range L,
            (ZMod.stdAddChar z) ^ (i + 1)‖ ^ 2 := by
      apply Finset.sum_le_sum
      intro z hz
      calc
        (∑ p : {p : (ZMod q)ˣ × (ZMod r)ˣ // f p = z},
          ‖∑ i ∈ Finset.range L,
            (ZMod.stdAddChar (f p.1)) ^ (i + 1)‖ ^ 2) =
            (Fintype.card {p : (ZMod q)ˣ × (ZMod r)ˣ // f p = z} : ℝ) *
              ‖∑ i ∈ Finset.range L,
                (ZMod.stdAddChar z) ^ (i + 1)‖ ^ 2 := by
          simp_rw [show ∀ p : {p : (ZMod q)ˣ × (ZMod r)ˣ // f p = z},
            f p.1 = z from fun p => p.2]
          simp
        _ ≤ (q.gcd r : ℝ) *
              ‖∑ i ∈ Finset.range L,
                (ZMod.stdAddChar z) ^ (i + 1)‖ ^ 2 := by
          apply mul_le_mul_of_nonneg_right
          · exact_mod_cast hfibre z
          · positivity
    _ = (q.gcd r : ℝ) *
        (∑ z : ZMod (Nat.lcm q r),
          ‖∑ i ∈ Finset.range L,
            (ZMod.stdAddChar z) ^ (i + 1)‖ ^ 2) := by
      rw [Finset.mul_sum]
    _ = (q.gcd r : ℝ) * (((Nat.lcm q r : ℕ) : ℝ) * L) := by
      rw [sum_normSq_stdAddChar_pow_range_eq (Nat.lcm q r) L hLN]
    _ = (((q * r : ℕ) : ℝ) * (M % Nat.lcm q r : ℕ)) := by
      have hgl : (q.gcd r : ℝ) * (Nat.lcm q r : ℝ) = (q * r : ℝ) := by
        exact_mod_cast Nat.gcd_mul_lcm q r
      rw [← mul_assoc, hgl]
      simp [L]

/-- Exact stored-modulus Parseval budget for one terminal orbit kernel. -/
def kloostermanTerminalOrbitLcmParsevalBudget (M q r : ℕ) : ℝ :=
  ((((q + 1) * (r + 1) : ℕ) : ℝ) *
    (M % Nat.lcm (q + 1) (r + 1) : ℕ))

/-- Stored terminal-orbit energy has product-times-residual-length scale, with no harmonic or gcd
loss. -/
theorem sum_kloostermanTerminalOrbit_succ_sq_le_lcmParsevalBudget
    (M q r : ℕ) :
    (∑ x : (ZMod (q + 1))ˣ, ∑ y : (ZMod (r + 1))ˣ,
      ‖kloostermanTerminalOrbit M (q + 1) (r + 1) x y‖ ^ 2) ≤
      kloostermanTerminalOrbitLcmParsevalBudget M q r := by
  simpa [kloostermanTerminalOrbitLcmParsevalBudget] using
    (sum_kloostermanTerminalOrbit_sq_le_lcmParseval M (q + 1) (r + 1))

/-- One stored terminal source quadratic inherits the exact-period Parseval orbit budget. -/
theorem norm_sourceQuadratic_terminalBlock_succ_sq_le_residue_lcmParseval
    (M q r : ℕ) (B : Finset ℕ) (b : ℕ → ℂ) :
    ‖∑ n ∈ B, star (b n) * ∑ k ∈ B, b k *
      kloostermanNaturalCrossIntervalTerminalBlock M (q + 1) (r + 1)
        (n : ZMod (q + 1)) (k : ZMod (r + 1))‖ ^ 2 ≤
      kloostermanSourceResidueEnergy q B b *
        kloostermanSourceResidueEnergy r B b *
          kloostermanTerminalOrbitLcmParsevalBudget M q r := by
  have hsource : 0 ≤
      kloostermanSourceResidueEnergy q B b *
        kloostermanSourceResidueEnergy r B b := by
    unfold kloostermanSourceResidueEnergy
    exact mul_nonneg
      (mul_nonneg (by positivity)
        (Finset.sum_nonneg fun z hz => Complex.normSq_nonneg _))
      (mul_nonneg (by positivity)
        (Finset.sum_nonneg fun z hz => Complex.normSq_nonneg _))
  calc
    _ ≤ (((q + 1 : ℕ) : ℝ) * ∑ z : ZMod (q + 1),
          Complex.normSq (kloostermanSourceResidue (q + 1) B b z)) *
        (((r + 1 : ℕ) : ℝ) * ∑ z : ZMod (r + 1),
          Complex.normSq (kloostermanSourceResidue (r + 1) B b z)) *
          ∑ x : (ZMod (q + 1))ˣ, ∑ y : (ZMod (r + 1))ˣ,
            ‖kloostermanTerminalOrbit M (q + 1) (r + 1) x y‖ ^ 2 :=
      norm_sourceQuadratic_terminalBlock_sq_le_residue_hilbertSchmidt
        M (q + 1) (r + 1) B b
    _ ≤ kloostermanSourceResidueEnergy q B b *
        kloostermanSourceResidueEnergy r B b *
          kloostermanTerminalOrbitLcmParsevalBudget M q r := by
      change kloostermanSourceResidueEnergy q B b *
          kloostermanSourceResidueEnergy r B b * _ ≤ _
      exact mul_le_mul_of_nonneg_left
        (sum_kloostermanTerminalOrbit_succ_sq_le_lcmParsevalBudget M q r)
        hsource

/-- Aggregate erased-modulus terminal source-quadratic energy with exact-period Parseval on every
modulus pair. -/
theorem sum_norm_sourceQuadratic_terminalBlock_succ_sq_le_residue_lcmParseval
    (M : ℕ) (Q B : Finset ℕ) (b : ℕ → ℂ) :
    (∑ q ∈ Q, ∑ r ∈ Q.erase q,
      ‖∑ n ∈ B, star (b n) * ∑ k ∈ B, b k *
        kloostermanNaturalCrossIntervalTerminalBlock M (q + 1) (r + 1)
          (n : ZMod (q + 1)) (k : ZMod (r + 1))‖ ^ 2) ≤
      ∑ q ∈ Q, ∑ r ∈ Q.erase q,
        kloostermanSourceResidueEnergy q B b *
          kloostermanSourceResidueEnergy r B b *
            kloostermanTerminalOrbitLcmParsevalBudget M q r := by
  classical
  apply Finset.sum_le_sum
  intro q hq
  apply Finset.sum_le_sum
  intro r hr
  exact norm_sourceQuadratic_terminalBlock_succ_sq_le_residue_lcmParseval
    M q r B b

private theorem norm_dependent_sum_mul_sq_le_sq_mul_sq_lcmParseval
    {α β : Type*} [DecidableEq α] [DecidableEq β]
    (A : Finset α) (D : α → Finset β)
    (a s : α → β → ℂ) :
    ‖∑ i ∈ A, ∑ j ∈ D i, a i j * s i j‖ ^ 2 ≤
      (∑ i ∈ A, ∑ j ∈ D i, ‖a i j‖ ^ 2) *
        ∑ i ∈ A, ∑ j ∈ D i, ‖s i j‖ ^ 2 := by
  have htri :
      ‖∑ i ∈ A, ∑ j ∈ D i, a i j * s i j‖ ≤
        ∑ i ∈ A, ∑ j ∈ D i, ‖a i j‖ * ‖s i j‖ := by
    refine (norm_sum_le _ _).trans ?_
    apply Finset.sum_le_sum
    intro i hi
    refine (norm_sum_le _ _).trans ?_
    apply Finset.sum_le_sum
    intro j hj
    rw [norm_mul]
  have hsum0 : 0 ≤ ∑ i ∈ A, ∑ j ∈ D i, ‖a i j‖ * ‖s i j‖ := by
    positivity
  calc
    ‖∑ i ∈ A, ∑ j ∈ D i, a i j * s i j‖ ^ 2 ≤
        (∑ i ∈ A, ∑ j ∈ D i, ‖a i j‖ * ‖s i j‖) ^ 2 := by
      nlinarith [norm_nonneg (∑ i ∈ A, ∑ j ∈ D i, a i j * s i j)]
    _ ≤ (∑ i ∈ A, ∑ j ∈ D i, ‖a i j‖ ^ 2) *
        ∑ i ∈ A, ∑ j ∈ D i, ‖s i j‖ ^ 2 := by
      rw [Finset.sum_sigma' A D (fun i j => ‖a i j‖ * ‖s i j‖)]
      rw [Finset.sum_sigma' A D (fun i j => ‖a i j‖ ^ 2)]
      rw [Finset.sum_sigma' A D (fun i j => ‖s i j‖ ^ 2)]
      exact Finset.sum_mul_sq_le_sq_mul_sq (A.sigma D)
        (fun p => ‖a p.1 p.2‖) (fun p => ‖s p.1 p.2‖)

/-- Full weighted terminal Gram quadratic with exact-period Parseval in every modulus-pair orbit
kernel. -/
theorem norm_kloostermanDistinctModulusTerminalGramQuadratic_sq_le_weightPair_residue_lcmParseval
    (M : ℕ) (Q : Finset ℕ) (w : ℕ → ℂ)
    (B : Finset ℕ) (b : ℕ → ℂ) :
    ‖kloostermanDistinctModulusTerminalGramQuadratic M Q w B b‖ ^ 2 ≤
      kloostermanDistinctModulusWeightPairEnergy Q w *
        ∑ q ∈ Q, ∑ r ∈ Q.erase q,
          kloostermanSourceResidueEnergy q B b *
            kloostermanSourceResidueEnergy r B b *
              kloostermanTerminalOrbitLcmParsevalBudget M q r := by
  classical
  rw [kloostermanDistinctModulusTerminalGramQuadratic_eq_sourceFourierOrbits]
  simp_rw [← sourceQuadratic_terminalBlock_eq_fourierOrbits]
  calc
    ‖∑ q ∈ Q, ∑ r ∈ Q.erase q,
        star (w q) * w r *
          (∑ n ∈ B, star (b n) * ∑ k ∈ B, b k *
            kloostermanNaturalCrossIntervalTerminalBlock M (q + 1) (r + 1)
              (n : ZMod (q + 1)) (k : ZMod (r + 1)))‖ ^ 2 ≤
        (∑ q ∈ Q, ∑ r ∈ Q.erase q, ‖star (w q) * w r‖ ^ 2) *
          ∑ q ∈ Q, ∑ r ∈ Q.erase q,
            ‖∑ n ∈ B, star (b n) * ∑ k ∈ B, b k *
              kloostermanNaturalCrossIntervalTerminalBlock M (q + 1) (r + 1)
                (n : ZMod (q + 1)) (k : ZMod (r + 1))‖ ^ 2 :=
      norm_dependent_sum_mul_sq_le_sq_mul_sq_lcmParseval Q (fun q => Q.erase q)
        (fun q r => star (w q) * w r)
        (fun q r => ∑ n ∈ B, star (b n) * ∑ k ∈ B, b k *
          kloostermanNaturalCrossIntervalTerminalBlock M (q + 1) (r + 1)
            (n : ZMod (q + 1)) (k : ZMod (r + 1)))
    _ ≤ kloostermanDistinctModulusWeightPairEnergy Q w *
        ∑ q ∈ Q, ∑ r ∈ Q.erase q,
          kloostermanSourceResidueEnergy q B b *
            kloostermanSourceResidueEnergy r B b *
              kloostermanTerminalOrbitLcmParsevalBudget M q r := by
      unfold kloostermanDistinctModulusWeightPairEnergy
      simp_rw [norm_mul, norm_star, mul_pow]
      exact mul_le_mul_of_nonneg_left
        (sum_norm_sourceQuadratic_terminalBlock_succ_sq_le_residue_lcmParseval
          M Q B b)
        (Finset.sum_nonneg fun q hq => Finset.sum_nonneg fun r hr => by positivity)

/-- Literal source interval version of the full exact-period Parseval receiver. -/
theorem norm_kloostermanDistinctModulusTerminalGramQuadratic_Icc_sq_le_interval_lcmParseval
    (M N : ℕ) (Q : Finset ℕ) (w b : ℕ → ℂ) :
    ‖kloostermanDistinctModulusTerminalGramQuadratic
        M Q w (Finset.Icc 1 N) b‖ ^ 2 ≤
      kloostermanDistinctModulusWeightPairEnergy Q w *
        ∑ q ∈ Q, ∑ r ∈ Q.erase q,
          kloostermanIntervalSourceEnergyBudget q N b *
            kloostermanIntervalSourceEnergyBudget r N b *
              kloostermanTerminalOrbitLcmParsevalBudget M q r := by
  calc
    _ ≤ kloostermanDistinctModulusWeightPairEnergy Q w *
        ∑ q ∈ Q, ∑ r ∈ Q.erase q,
          kloostermanSourceResidueEnergy q (Finset.Icc 1 N) b *
            kloostermanSourceResidueEnergy r (Finset.Icc 1 N) b *
              kloostermanTerminalOrbitLcmParsevalBudget M q r :=
      norm_kloostermanDistinctModulusTerminalGramQuadratic_sq_le_weightPair_residue_lcmParseval
        M Q w (Finset.Icc 1 N) b
    _ ≤ kloostermanDistinctModulusWeightPairEnergy Q w *
        ∑ q ∈ Q, ∑ r ∈ Q.erase q,
          kloostermanIntervalSourceEnergyBudget q N b *
            kloostermanIntervalSourceEnergyBudget r N b *
              kloostermanTerminalOrbitLcmParsevalBudget M q r := by
      apply mul_le_mul_of_nonneg_left
      · apply Finset.sum_le_sum
        intro q hq
        apply Finset.sum_le_sum
        intro r hr
        have hP : 0 ≤ kloostermanTerminalOrbitLcmParsevalBudget M q r := by
          unfold kloostermanTerminalOrbitLcmParsevalBudget
          positivity
        have hSr : 0 ≤ kloostermanSourceResidueEnergy r (Finset.Icc 1 N) b := by
          unfold kloostermanSourceResidueEnergy
          exact mul_nonneg (by positivity)
            (Finset.sum_nonneg fun z hz => Complex.normSq_nonneg _)
        have hBq : 0 ≤ kloostermanIntervalSourceEnergyBudget q N b := by
          unfold kloostermanIntervalSourceEnergyBudget
          exact mul_nonneg (by positivity) <| mul_nonneg (by positivity)
            (Finset.sum_nonneg fun n hn => Complex.normSq_nonneg _)
        calc
          kloostermanSourceResidueEnergy q (Finset.Icc 1 N) b *
              kloostermanSourceResidueEnergy r (Finset.Icc 1 N) b *
                kloostermanTerminalOrbitLcmParsevalBudget M q r ≤
              kloostermanIntervalSourceEnergyBudget q N b *
                kloostermanSourceResidueEnergy r (Finset.Icc 1 N) b *
                  kloostermanTerminalOrbitLcmParsevalBudget M q r := by
            apply mul_le_mul_of_nonneg_right _ hP
            exact mul_le_mul_of_nonneg_right
              (kloostermanSourceResidueEnergy_Icc_le_intervalBudget q N b) hSr
          _ ≤ kloostermanIntervalSourceEnergyBudget q N b *
                kloostermanIntervalSourceEnergyBudget r N b *
                  kloostermanTerminalOrbitLcmParsevalBudget M q r := by
            apply mul_le_mul_of_nonneg_right _ hP
            exact mul_le_mul_of_nonneg_left
              (kloostermanSourceResidueEnergy_Icc_le_intervalBudget r N b) hBq
      · unfold kloostermanDistinctModulusWeightPairEnergy
        positivity

end

end RHTower.Sieve
