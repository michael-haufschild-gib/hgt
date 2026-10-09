import GaloisForLFunctions.RHTower.MobiusSquareResidueFourier
import GaloisForLFunctions.RHTower.SquareResidueGcdHarmonic

/-!
The centered logarithmic Mobius action on quadratic-residue prefixes fits
the critical quadratic budget for all moduli up to the sampling cutoff.
Pairing reciprocal character chords reduces the Fourier bound to a gcd
harmonic row. Its aggregate costs at most `sqrt D * (1 + log D)^2`.
For `D <= N`, the full centered action, including complete periods, is at
most `4 * N * sqrt D * (1 + log D)^4`, hence at most `16384 * N * D`.
The explicit mean is retained in a separate exact identity.
-/

set_option autoImplicit false
open scoped BigOperators
open Finset Complex

namespace RHTower
variable {q : ℕ} [NeZero q]

theorem squareResidue_double_gcd_le (k : ℕ) :
    Nat.gcd q (2 * (k : ZMod q)).val ≤ 2 * Nat.gcd q k := by
  have he : 2 * (k : ZMod q) = ((2 * k : ℕ) : ZMod q) := by
    simp only [Nat.cast_mul, Nat.cast_ofNat]
  have hv : Nat.gcd q (2 * (k : ZMod q)).val = Nat.gcd q (2 * k) := by
    calc
      _ = Nat.gcd q ((2 * k) % q) := by rw [he, ZMod.val_natCast]
      _ = Nat.gcd ((2 * k) % q) q := Nat.gcd_comm _ _
      _ = _ := (Nat.gcd_rec q (2 * k)).symm
  rw [hv]
  have hd : Nat.gcd q (2 * k) ∣ Nat.gcd q 2 * Nat.gcd q k := by
    simpa only [Nat.gcd_comm] using Nat.gcd_mul_left_dvd_mul_gcd q 2 k
  have hd' := hd.trans (Nat.mul_dvd_mul_right (Nat.gcd_dvd_right q 2) (Nat.gcd q k))
  apply Nat.le_of_dvd _ hd'
  have := Nat.gcd_pos_of_pos_left k (NeZero.pos q)
  omega

theorem squareResidue_gauss_gcd_sqrt_le (k : ℕ) :
    Real.sqrt ((q : ℝ) * Nat.gcd q (2 * (k : ZMod q)).val) ≤
      2 * (q : ℝ) * Real.sqrt ((Nat.gcd q k : ℝ) / q) := by
  have hq : (0 : ℝ) < q := Nat.cast_pos.mpr (NeZero.pos q)
  have hg : (Nat.gcd q (2 * (k : ZMod q)).val : ℝ) ≤ 2 * Nat.gcd q k := by
    exact_mod_cast squareResidue_double_gcd_le (q := q) k
  have hr : (2 * (q : ℝ) * Real.sqrt ((Nat.gcd q k : ℝ) / q)) ^ 2 =
      4 * (q : ℝ) * Nat.gcd q k := by
    rw [mul_pow, Real.sq_sqrt (by positivity)]
    field_simp [ne_of_gt hq]
    ring
  have hm := mul_le_mul_of_nonneg_left hg hq.le
  have hnn := mul_nonneg hq.le (Nat.cast_nonneg (Nat.gcd q k) : (0 : ℝ) ≤ _)
  have hh : (q : ℝ) * Nat.gcd q (2 * (k : ZMod q)).val ≤
      (2 * (q : ℝ) * Real.sqrt ((Nat.gcd q k : ℝ) / q)) ^ 2 := by
    rw [hr]
    nlinarith
  calc
    _ ≤ Real.sqrt ((2 * (q : ℝ) * Real.sqrt ((Nat.gcd q k : ℝ) / q)) ^ 2) :=
      Real.sqrt_le_sqrt hh
    _ = _ := by rw [Real.sqrt_sq_eq_abs, abs_of_nonneg (by positivity)]

private theorem squareResidue_neg_chord (a : ZMod q) :
    ‖1 - ZMod.stdAddChar (-a)‖ = ‖ZMod.stdAddChar a - 1‖ := by
  rw [AddChar.map_neg_eq_conj]
  have he : (1 : ℂ) - (starRingEnd ℂ) (ZMod.stdAddChar a) =
      (starRingEnd ℂ) (1 - ZMod.stdAddChar a) := by rw [map_sub, map_one]
  rw [he, Complex.norm_conj, norm_sub_rev]

private theorem squareResidue_nat_chord_le {k : ℕ} (hk : 0 < k) (hkq : k < q) :
    1 / ‖1 - ZMod.stdAddChar (-(k : ZMod q))‖ ≤
      (q : ℝ) / 4 * (1 / (k : ℝ) + 1 / ((q - k : ℕ) : ℝ)) := by
  have hc : ZMod.stdAddChar (k : ZMod q) =
      Complex.exp (2 * Real.pi * Complex.I * (k : ℂ) / q) := by
    simpa only [Int.cast_natCast] using ZMod.stdAddChar_coe (N := q) (k : ℤ)
  have h := GaloisForLFunctions.RHTower.RootOfUnityCompletion.two_div_norm_exp_sub_one_le hk hkq
  rw [← hc, ← squareResidue_neg_chord] at h
  have hh := mul_le_mul_of_nonneg_left h (by norm_num : (0 : ℝ) ≤ 1 / 2)
  calc
    _ = (1 / 2 : ℝ) * (2 / ‖1 - ZMod.stdAddChar (-(k : ZMod q))‖) := by ring
    _ ≤ _ := hh
    _ = _ := by ring

theorem squareResidue_gcd_chord_sum_le :
    (∑ a ∈ (univ : Finset (ZMod q)).erase 0,
      Real.sqrt ((q : ℝ) * Nat.gcd q (2 * a).val) / ‖1 - ZMod.stdAddChar (-a)‖) ≤
      (q : ℝ) ^ 2 * ∑ k ∈ Ioc 0 q, Real.sqrt ((Nat.gcd q k : ℝ) / q) / k := by
  let r : ℕ → ℝ := fun k => Real.sqrt ((Nat.gcd q k : ℝ) / q)
  have hre : (∑ a ∈ (univ : Finset (ZMod q)).erase 0,
        Real.sqrt ((q : ℝ) * Nat.gcd q (2 * a).val) / ‖1 - ZMod.stdAddChar (-a)‖) =
      ∑ k ∈ Ioo 0 q, Real.sqrt ((q : ℝ) * Nat.gcd q (2 * (k : ZMod q)).val) /
        ‖1 - ZMod.stdAddChar (-(k : ZMod q))‖ := by
    apply Finset.sum_bij (fun a _ => a.val)
    · intro a ha
      refine mem_Ioo.mpr ⟨Nat.pos_of_ne_zero ?_, ZMod.val_lt a⟩
      intro hv
      exact (mem_erase.mp ha).1 ((ZMod.val_eq_zero a).mp hv)
    · intro a _ b _ h
      have hc := congrArg (fun n : ℕ => (n : ZMod q)) h
      simpa only [ZMod.natCast_zmod_val] using hc
    · intro k hk
      have hv : (k : ZMod q).val = k := by
        rw [ZMod.val_natCast, Nat.mod_eq_of_lt (mem_Ioo.mp hk).2]
      refine ⟨(k : ZMod q), mem_erase.mpr ⟨?_, mem_univ _⟩, hv⟩
      intro hz
      have hk0 : k = 0 := by simpa only [hz, ZMod.val_zero] using hv.symm
      exact (Nat.ne_of_gt (mem_Ioo.mp hk).1) hk0
    · intro a _
      rw [ZMod.natCast_zmod_val]
  have href : (∑ k ∈ Ioo 0 q, r k / ((q - k : ℕ) : ℝ)) =
      ∑ k ∈ Ioo 0 q, r k / k := by
    apply Finset.sum_bij (fun k _ => q - k)
    · intro k hk
      have := mem_Ioo.mp hk
      apply mem_Ioo.mpr
      omega
    · intro k hk l hl h
      have := mem_Ioo.mp hk
      have := mem_Ioo.mp hl
      omega
    · intro k hk
      have := mem_Ioo.mp hk
      refine ⟨q - k, mem_Ioo.mpr ?_, ?_⟩ <;> omega
    · intro k hk
      dsimp [r]
      rw [Nat.gcd_self_sub_right (mem_Ioo.mp hk).2.le]
  rw [hre]
  calc
    _ ≤ ∑ k ∈ Ioo 0 q, (q : ℝ) ^ 2 / 2 * (r k / k + r k / ((q - k : ℕ) : ℝ)) := by
      apply sum_le_sum
      intro k hk
      have hk' := mem_Ioo.mp hk
      calc
        _ = Real.sqrt ((q : ℝ) * Nat.gcd q (2 * (k : ZMod q)).val) *
            (1 / ‖1 - ZMod.stdAddChar (-(k : ZMod q))‖) := by ring
        _ ≤ (2 * (q : ℝ) * r k) *
            ((q : ℝ) / 4 * (1 / (k : ℝ) + 1 / ((q - k : ℕ) : ℝ))) := by
          exact mul_le_mul (squareResidue_gauss_gcd_sqrt_le k)
            (squareResidue_nat_chord_le hk'.1 hk'.2) (by positivity) (by dsimp [r]; positivity)
        _ = _ := by ring
    _ = (q : ℝ) ^ 2 / 2 *
        ((∑ k ∈ Ioo 0 q, r k / k) + ∑ k ∈ Ioo 0 q, r k / ((q - k : ℕ) : ℝ)) := by
      rw [mul_add, mul_sum, mul_sum, ← sum_add_distrib]
      apply sum_congr rfl
      intro k _
      ring
    _ = (q : ℝ) ^ 2 * ∑ k ∈ Ioo 0 q, r k / k := by rw [href]; ring
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_left _ (sq_nonneg (q : ℝ))
      apply sum_le_sum_of_subset_of_nonneg
      · intro k hk
        exact mem_Ioc.mpr ⟨(mem_Ioo.mp hk).1, (mem_Ioo.mp hk).2.le⟩
      · intro k _ _
        dsimp [r]
        positivity

theorem abs_quadraticResiduePrefix_centered_le_gcd (N : ℕ) :
    |quadraticResiduePrefix N q - (N : ℝ) * ((q : ℝ) - 1) / 2| ≤
      ((N / q : ℕ) + 1 : ℝ) * (q : ℝ) ^ 2 * (2 + Real.log q) *
        ∑ k ∈ Ioc 0 q, Real.sqrt ((Nat.gcd q k : ℝ) / q) / k := by
  have hlog := Real.log_natCast_nonneg q
  calc
    _ ≤ ((N / q : ℕ) + 1 : ℝ) * (2 + Real.log q) *
        ∑ a ∈ (univ : Finset (ZMod q)).erase 0,
          Real.sqrt ((q : ℝ) * Nat.gcd q (2 * a).val) / ‖1 - ZMod.stdAddChar (-a)‖ :=
      abs_quadraticResiduePrefix_centered_le_periods N
    _ ≤ ((N / q : ℕ) + 1 : ℝ) * (2 + Real.log q) *
        ((q : ℝ) ^ 2 * ∑ k ∈ Ioc 0 q, Real.sqrt ((Nat.gcd q k : ℝ) / q) / k) :=
      mul_le_mul_of_nonneg_left squareResidue_gcd_chord_sum_le (by positivity)
    _ = _ := by ring

end RHTower

namespace RHTower

noncomputable def logMobiusCenteredQuadraticResidueAction (N D : ℕ) : ℝ :=
  ∑ d ∈ Icc 1 D, (((ArithmeticFunction.moebius d : ℤ) : ℝ) * Real.log d / d) *
    (quadraticResiduePrefix N d - (N : ℝ) * ((d : ℝ) - 1) / 2)

theorem logMobiusQuadraticResidueAction_eq_mean_add_centered (N D : ℕ) :
    (∑ d ∈ Icc 1 D, (((ArithmeticFunction.moebius d : ℤ) : ℝ) * Real.log d / d) *
      quadraticResiduePrefix N d) =
      (N : ℝ) / 2 * ∑ d ∈ Icc 1 D,
        (((ArithmeticFunction.moebius d : ℤ) : ℝ) * Real.log d) * (1 - 1 / (d : ℝ)) +
      logMobiusCenteredQuadraticResidueAction N D := by
  rw [logMobiusCenteredQuadraticResidueAction, mul_sum, ← sum_add_distrib]
  apply sum_congr rfl
  intro d hd
  have hdR : (0 : ℝ) < d := by exact_mod_cast (mem_Icc.mp hd).1
  field_simp [ne_of_gt hdR]
  ring

theorem abs_logMobiusCenteredQuadraticResidueAction_le_all (N D : ℕ) :
    |logMobiusCenteredQuadraticResidueAction N D| ≤
      2 * ((N : ℝ) + D) * Real.sqrt D * (1 + Real.log D) ^ 4 := by
  let R : ℕ → ℝ := fun d => ∑ k ∈ Ioc 0 d, Real.sqrt ((Nat.gcd d k : ℝ) / d) / k
  let T : ℕ → ℝ := fun d => ∑ k ∈ Ioc 0 D, Real.sqrt ((Nat.gcd d k : ℝ) / d) / k
  let C := ((N : ℝ) + D) * Real.log D * (2 + Real.log D)
  have hlogD := Real.log_natCast_nonneg D
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hRT {d : ℕ} (hd : d ≤ D) : R d ≤ T d := by
    apply sum_le_sum_of_subset_of_nonneg
    · intro k hk
      exact mem_Ioc.mpr ⟨(mem_Ioc.mp hk).1, (mem_Ioc.mp hk).2.trans hd⟩
    · intro k _ _
      positivity
  have hterm (d : ℕ) (hd : d ∈ Icc 1 D) :
      |(((ArithmeticFunction.moebius d : ℤ) : ℝ) * Real.log d / d) *
          (quadraticResiduePrefix N d - (N : ℝ) * ((d : ℝ) - 1) / 2)| ≤ C * T d := by
    have hd' := mem_Icc.mp hd
    have hd0 : 0 < d := by omega
    letI : NeZero d := ⟨Nat.ne_of_gt hd0⟩
    have hdR : (0 : ℝ) < d := by exact_mod_cast hd0
    have hlogd := Real.log_natCast_nonneg d
    have hlog : Real.log d ≤ Real.log D := Real.log_le_log hdR (by exact_mod_cast hd'.2)
    have hmu : |((ArithmeticFunction.moebius d : ℤ) : ℝ)| ≤ 1 := by
      exact_mod_cast ArithmeticFunction.abs_moebius_le_one (n := d)
    have hQ : ((N / d : ℕ) + 1 : ℝ) * (d : ℝ) ≤ (N : ℝ) + D := by
      have hn : (N / d + 1) * d ≤ N + D := by
        rw [Nat.add_mul, one_mul]
        have := Nat.div_mul_le_self N d
        omega
      exact_mod_cast hn
    have hlogs : Real.log d * (2 + Real.log d) ≤ Real.log D * (2 + Real.log D) :=
      mul_le_mul hlog (by linarith) (by positivity) hlogD
    have hR : 0 ≤ R d := sum_nonneg fun _ _ => by positivity
    have hE := abs_quadraticResiduePrefix_centered_le_gcd (q := d) N
    rw [abs_mul, abs_div, abs_mul, abs_of_nonneg hlogd, abs_of_pos hdR]
    calc
      _ ≤ (1 * Real.log d / d) *
          (((N / d : ℕ) + 1 : ℝ) * (d : ℝ) ^ 2 * (2 + Real.log d) * R d) := by
        apply mul_le_mul
        · exact div_le_div_of_nonneg_right
            (mul_le_mul_of_nonneg_right hmu hlogd) hdR.le
        · exact hE
        · exact abs_nonneg _
        · positivity
      _ = (((N / d : ℕ) + 1 : ℝ) * d) * (Real.log d * (2 + Real.log d)) * R d := by
        field_simp [ne_of_gt hdR]
      _ ≤ ((N : ℝ) + D) * (Real.log D * (2 + Real.log D)) * T d := by
        apply mul_le_mul
        · exact mul_le_mul hQ hlogs (by positivity) (by positivity)
        · exact hRT hd'.2
        · exact hR
        · positivity
      _ = _ := by dsimp [C]; ring
  calc
    _ ≤ ∑ d ∈ Icc 1 D,
        |(((ArithmeticFunction.moebius d : ℤ) : ℝ) * Real.log d / d) *
          (quadraticResiduePrefix N d - (N : ℝ) * ((d : ℝ) - 1) / 2)| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ d ∈ Icc 1 D, C * T d := sum_le_sum hterm
    _ = C * ∑ d ∈ Ioc 0 D, T d := by
      have he : Icc 1 D = Ioc 0 D := by ext d; simp only [mem_Icc, mem_Ioc]; omega
      rw [← mul_sum, he]
    _ ≤ C * (Real.sqrt D * (1 + Real.log D) ^ 2) :=
      mul_le_mul_of_nonneg_left (squareResidue_gcd_harmonic_le D) hC
    _ ≤ _ := by
      have hx : Real.log D * (2 + Real.log D) ≤ 2 * (1 + Real.log D) ^ 2 := by nlinarith
      have hm := mul_le_mul_of_nonneg_left hx
        (show 0 ≤ ((N : ℝ) + D) * Real.sqrt D * (1 + Real.log D) ^ 2 by positivity)
      calc
        _ = (((N : ℝ) + D) * Real.sqrt D * (1 + Real.log D) ^ 2) *
            (Real.log D * (2 + Real.log D)) := by dsimp [C]; ring
        _ ≤ _ := hm
        _ = _ := by ring

theorem abs_logMobiusCenteredQuadraticResidueAction_le {N D : ℕ} (hDN : D ≤ N) :
    |logMobiusCenteredQuadraticResidueAction N D| ≤
      4 * (N : ℝ) * Real.sqrt D * (1 + Real.log D) ^ 4 := by
  have hDN' : (D : ℝ) ≤ N := by exact_mod_cast hDN
  calc
    _ ≤ 2 * ((N : ℝ) + D) * Real.sqrt D * (1 + Real.log D) ^ 4 :=
      abs_logMobiusCenteredQuadraticResidueAction_le_all N D
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      apply mul_le_mul_of_nonneg_right _ (Real.sqrt_nonneg _)
      linarith

private theorem squareResidue_log_fourth_le_rpow {x ε : ℝ} (hx : 1 ≤ x) (hε : 0 < ε) :
    (1 + Real.log x) ^ 4 ≤ (1 + 4 / ε) ^ 4 * x ^ ε := by
  have hx0 : 0 ≤ x := by linarith
  have he4 : 0 < ε / 4 := by positivity
  have hp : 1 ≤ x ^ (ε / 4) := Real.one_le_rpow hx he4.le
  have hl := Real.log_le_rpow_div hx0 he4
  have hlin : 1 + Real.log x ≤ (1 + 4 / ε) * x ^ (ε / 4) := by
    calc
      _ ≤ x ^ (ε / 4) + x ^ (ε / 4) / (ε / 4) := add_le_add hp hl
      _ = _ := by field_simp [ne_of_gt hε]
  have hpow : (x ^ (ε / 4)) ^ (4 : ℕ) = x ^ ε := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hx0]
    congr 1
    ring
  calc
    _ ≤ ((1 + 4 / ε) * x ^ (ε / 4)) ^ 4 :=
      pow_le_pow_left₀ (by linarith [Real.log_nonneg hx]) hlin 4
    _ = _ := by rw [mul_pow, hpow]

/-- Uniform centered action bound for every cutoff, with an arbitrarily small power loss. -/
theorem abs_logMobiusCenteredQuadraticResidueAction_le_rpow
    {ε : ℝ} (hε : 0 < ε) (N : ℕ) {D : ℕ} (hD : 1 ≤ D) :
    |logMobiusCenteredQuadraticResidueAction N D| ≤
      2 * (1 + 4 / ε) ^ 4 * ((N : ℝ) + D) * (D : ℝ) ^ (1 / 2 + ε) := by
  have hD1 : (1 : ℝ) ≤ D := by exact_mod_cast hD
  have hDpos : (0 : ℝ) < D := by linarith
  calc
    _ ≤ 2 * ((N : ℝ) + D) * Real.sqrt D * (1 + Real.log D) ^ 4 :=
      abs_logMobiusCenteredQuadraticResidueAction_le_all N D
    _ ≤ 2 * ((N : ℝ) + D) * Real.sqrt D *
        ((1 + 4 / ε) ^ 4 * (D : ℝ) ^ ε) :=
      mul_le_mul_of_nonneg_left (squareResidue_log_fourth_le_rpow hD1 hε) (by positivity)
    _ = _ := by
      rw [Real.sqrt_eq_rpow, Real.rpow_add hDpos]
      ring

/-- The centered source remains quadratic for superlinear cutoffs below the 4/3 exponent. -/
theorem abs_logMobiusCenteredQuadraticResidueAction_le_superlinear_aperture
    {ε : ℝ} (hε : 0 < ε) {N D : ℕ} (hD : 1 ≤ D) (hND : N ≤ D)
    (hcritical : (D : ℝ) ^ (3 / 2 + ε) ≤ (N : ℝ) ^ 2) :
    |logMobiusCenteredQuadraticResidueAction N D| ≤
      4 * (1 + 4 / ε) ^ 4 * (N : ℝ) ^ 2 := by
  have hND' : (N : ℝ) ≤ D := by exact_mod_cast hND
  have hDpos : (0 : ℝ) < D := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hD)
  have hpower : (D : ℝ) * (D : ℝ) ^ (1 / 2 + ε) =
      (D : ℝ) ^ (3 / 2 + ε) := by
    have hp := Real.rpow_add hDpos 1 ((1 / 2 : ℝ) + ε)
    rw [Real.rpow_one] at hp
    calc
      _ = (D : ℝ) ^ (1 + (1 / 2 + ε)) := hp.symm
      _ = _ := by congr 1; ring
  calc
    _ ≤ 2 * (1 + 4 / ε) ^ 4 * ((N : ℝ) + D) * (D : ℝ) ^ (1 / 2 + ε) :=
      abs_logMobiusCenteredQuadraticResidueAction_le_rpow hε N hD
    _ ≤ 4 * (1 + 4 / ε) ^ 4 * D * (D : ℝ) ^ (1 / 2 + ε) := by
      apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg (Nat.cast_nonneg D) _)
      have hm := mul_le_mul_of_nonneg_left hND'
        (show 0 ≤ 2 * (1 + 4 / ε) ^ 4 by positivity)
      nlinarith only [hm]
    _ = 4 * (1 + 4 / ε) ^ 4 * ((D : ℝ) * (D : ℝ) ^ (1 / 2 + ε)) := by ring
    _ = 4 * (1 + 4 / ε) ^ 4 * (D : ℝ) ^ (3 / 2 + ε) := by rw [hpower]
    _ ≤ _ := mul_le_mul_of_nonneg_left hcritical (by positivity)

private theorem squareResidue_log_fourth_le_sqrt {x : ℝ} (hx : 1 ≤ x) :
    (1 + Real.log x) ^ 4 ≤ 4096 * Real.sqrt x := by
  let u := Real.sqrt (Real.sqrt (Real.sqrt x))
  have hx0 : 0 ≤ x := by linarith
  have hxpos : 0 < x := by linarith
  have hu : 0 < u := by dsimp [u]; positivity
  have hlog1 := Real.log_sqrt hx0
  have hlog2 := Real.log_sqrt (Real.sqrt_nonneg x)
  have hlog3 := Real.log_sqrt (Real.sqrt_nonneg (Real.sqrt x))
  have hl := Real.log_le_sub_one_of_pos hu
  have hlin : 1 + Real.log x ≤ 8 * u := by
    dsimp [u] at hl ⊢
    linarith
  have hupow : u ^ 4 = Real.sqrt x := by
    calc
      _ = (u ^ 2) ^ 2 := by ring
      _ = (Real.sqrt (Real.sqrt x)) ^ 2 := by
        dsimp [u]
        rw [Real.sq_sqrt (Real.sqrt_nonneg (Real.sqrt x))]
      _ = _ := Real.sq_sqrt (Real.sqrt_nonneg x)
  have hlog := Real.log_nonneg hx
  calc
    _ ≤ (8 * u) ^ 4 := pow_le_pow_left₀ (by linarith) hlin 4
    _ = _ := by rw [mul_pow, hupow]; norm_num

theorem abs_logMobiusCenteredQuadraticResidueAction_le_mul {N D : ℕ} (hDN : D ≤ N) :
    |logMobiusCenteredQuadraticResidueAction N D| ≤ 16384 * (N : ℝ) * D := by
  by_cases hD : D = 0
  · subst D
    simp [logMobiusCenteredQuadraticResidueAction]
  have hD1 : (1 : ℝ) ≤ D := by exact_mod_cast (Nat.one_le_iff_ne_zero.mpr hD)
  calc
    _ ≤ 4 * (N : ℝ) * Real.sqrt D * (1 + Real.log D) ^ 4 :=
      abs_logMobiusCenteredQuadraticResidueAction_le hDN
    _ ≤ 4 * (N : ℝ) * Real.sqrt D * (4096 * Real.sqrt D) :=
      mul_le_mul_of_nonneg_left (squareResidue_log_fourth_le_sqrt hD1) (by positivity)
    _ = 16384 * (N : ℝ) * (Real.sqrt D) ^ 2 := by ring
    _ = _ := by rw [Real.sq_sqrt (Nat.cast_nonneg D)]

theorem abs_logMobiusCenteredQuadraticResidueAction_self_le (N : ℕ) :
    |logMobiusCenteredQuadraticResidueAction N N| ≤ 16384 * (N : ℝ) ^ 2 := by
  simpa only [pow_two, mul_assoc] using
    abs_logMobiusCenteredQuadraticResidueAction_le_mul (N := N) (D := N) le_rfl

end RHTower
