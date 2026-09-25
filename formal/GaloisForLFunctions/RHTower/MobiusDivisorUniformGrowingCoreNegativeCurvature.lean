import GaloisForLFunctions.RHTower.MobiusDivisorPositivePrimeSupply
import GaloisForLFunctions.RHTower.MobiusDivisorSmallCoreInteractions
import GaloisForLFunctions.RHTower.MobiusDivisorLatePrimeFibres

/-!
# Uniform negative mixed curvature across growing prime cores

A positive small-core p-fibre and a negative late-q dilation produce a
macroscopic negative mixed energy difference. The bound survives any
processed prime core containing the primes below eight, provided p and q
remain unprocessed. This controls a second difference, not absolute energy.
-/

open Finset Set
namespace RHTower

private theorem uniform_mixed_eq_late_product
    (M : ℕ) (P : Finset ℕ) {p q : ℕ}
    (hq : q.Prime) (hqM : q < M) (hMq : M ≤ 2 * q)
    (hqP : q ∉ P) (hpq : p ≠ q) :
    mobiusDivisorSelectionEnergy M (insert q (insert p P)) -
      mobiusDivisorSelectionEnergy M (insert p P) -
      mobiusDivisorSelectionEnergy M (insert q P) +
        mobiusDivisorSelectionEnergy M P =
      2 * mobiusDivisorSelectionFibre M P {p} *
        mobiusDivisorDilationChannel M q := by
  have hqPp : q ∉ insert p P := by simp [hqP, hpq.symm]
  have h₁ := mobiusDivisorSelectionEnergy_insert_late_prime
    hq hqM hMq (insert p P) hqPp
  have h₀ := mobiusDivisorSelectionEnergy_insert_late_prime
    hq hqM hMq P hqP
  have hh : mobiusDivisorSelectionFibre M (insert p P) ∅ =
      mobiusDivisorSelectionFibre M P ∅ +
        mobiusDivisorSelectionFibre M P {p} := by
    rw [mobiusDivisorSelectionFibre_insert]
    simp
  calc
    _ = (mobiusDivisorSelectionEnergy M (insert q (insert p P)) -
          mobiusDivisorSelectionEnergy M (insert p P)) -
        (mobiusDivisorSelectionEnergy M (insert q P) -
          mobiusDivisorSelectionEnergy M P) := by ring
    _ = 2 * mobiusDivisorSelectionFibre M (insert p P) ∅ *
          mobiusDivisorDilationChannel M q -
        2 * mobiusDivisorSelectionFibre M P ∅ *
          mobiusDivisorDilationChannel M q := by rw [h₁, h₀]
    _ = _ := by rw [hh]; ring

private theorem uniform_first_defect_pos : 0 < primeFreeDivisorDefect 1 := by
  norm_num [primeFreeDivisorDefect]
  linarith [Real.one_half_lt_eulerMascheroniConstant]

private theorem uniform_late_dilation_margin
    {M q : ℕ} (hq : q.Prime) (hqband :
      (M : ℝ) / q ∈ Ioo (4 / 3 : ℝ) (3 / 2)) :
    mobiusDivisorDilationChannel M q ≤
      -(primeFreeDivisorDefect 1 / 8) * Real.sqrt M := by
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq.pos
  have hqM : q < M := by
    have h : (1 : ℝ) < (M : ℝ) / q := by linarith [hqband.1]
    exact_mod_cast (one_lt_div hq0).mp h
  have hM2q : M ≤ 2 * q := by
    have h : (M : ℝ) < 2 * q := by
      have h' := (div_lt_iff₀ hq0).mp hqband.2
      linarith
    exact_mod_cast h.le
  have hq3M : 4 * q < 3 * M := by
    have h := (lt_div_iff₀ hq0).mp hqband.1
    exact_mod_cast (by nlinarith : 4 * (q : ℝ) < 3 * M)
  have hroot : Real.sqrt (q : ℝ) ≤ (7 / 8) * Real.sqrt M := by
    apply Real.sqrt_le_iff.mpr
    constructor
    · positivity
    · rw [mul_pow, Real.sq_sqrt (Nat.cast_nonneg M)]
      have hqr : 4 * (q : ℝ) < 3 * M := by exact_mod_cast hq3M
      nlinarith
  have hgap : Real.sqrt (M : ℝ) / 8 ≤
      Real.sqrt M - Real.sqrt q := by linarith
  have hpos := uniform_first_defect_pos
  have hfirst := divisorUnsignedDilationChannel_eq_first_block
    hq.one_le hqM hM2q
  rw [mobiusDivisorDilationChannel_eq_moebius_unsigned,
    ArithmeticFunction.moebius_apply_prime hq, hfirst]
  push_cast
  nlinarith [mul_le_mul_of_nonneg_right hgap hpos.le]

private theorem uniform_small_core_filter
    (P : Finset ℕ) (hP : ∀ r ∈ P, r.Prime)
    (hcore : mobiusDivisorSelectionPrimes 8 ⊆ P) :
    P.filter (fun r => r < 8) = mobiusDivisorSelectionPrimes 8 := by
  ext r
  constructor
  · intro hr
    exact mem_filter.mpr ⟨mem_range.mpr (mem_filter.mp hr).2,
      hP r (mem_filter.mp hr).1⟩
  · intro hr
    exact mem_filter.mpr ⟨hcore hr, mem_range.mp (mem_filter.mp hr).1⟩

theorem exists_uniform_growingCore_negative_mixed_window :
    ∃ b : ℕ, 8 ≤ b ∧ ∃ κ : ℝ, 0 < κ ∧
      ∀ N : ℕ, 1 ≤ N →
      let M := 7 * (b + 1) * N
      ∀ P : Finset ℕ, (∀ r ∈ P, r.Prime) →
        mobiusDivisorSelectionPrimes 8 ⊆ P →
        ∀ p q : ℕ,
          p ∈ GaloisForLFunctions.HTGeometry.primesInIoc
            (b * N) ((b + 1) * N) → p ∉ P →
          q.Prime →
          (M : ℝ) / q ∈ Ioo (4 / 3 : ℝ) (3 / 2) → q ∉ P →
          mobiusDivisorSelectionEnergy M (insert q (insert p P)) -
            mobiusDivisorSelectionEnergy M (insert p P) -
            mobiusDivisorSelectionEnergy M (insert q P) +
              mobiusDivisorSelectionEnergy M P ≤
            -κ * (M : ℝ) := by
  obtain ⟨b, hb, c, hc, hpositive⟩ := exists_mobiusDivisorPositivePrimeWindow
  let C : ℕ := 7 * (b + 1)
  let d : ℝ := primeFreeDivisorDefect 1 / 8
  let κ : ℝ := c * d / C
  have hC : 1 ≤ C := by dsimp [C]; omega
  have hd : 0 < d := by
    dsimp [d]
    exact div_pos uniform_first_defect_pos (by norm_num)
  have hκ : 0 < κ := by dsimp [κ]; positivity
  refine ⟨b, hb, κ, hκ, fun N hN => ?_⟩
  dsimp only
  intro P hP hcore p q hp hpP hq hqband hqP
  let M : ℕ := C * N
  have hM : M = 7 * (b + 1) * N := by dsimp [M, C]
  have hMq := uniform_late_dilation_margin hq (by simpa only [← hM] using hqband)
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq.pos
  have hqM : q < M := by
    have h : (1 : ℝ) < (M : ℝ) / q := by
      rw [hM]
      linarith [hqband.1]
    exact_mod_cast (one_lt_div hq0).mp h
  have hM2q : M ≤ 2 * q := by
    have h : (M : ℝ) < 2 * q := by
      have h' := (div_lt_iff₀ hq0).mp hqband.2
      rw [hM]
      linarith
    exact_mod_cast h.le
  obtain ⟨hpp, hlo, hhi⟩ := GaloisForLFunctions.HTGeometry.mem_primesInIoc hp
  have hfactor : 7 * (b + 1) ≤ 8 * b := by omega
  have hM8p : M < 8 * p := by
    calc
      M = (7 * (b + 1)) * N := rfl
      _ ≤ (8 * b) * N := Nat.mul_le_mul_right N hfactor
      _ = 8 * (b * N) := by ring
      _ < 8 * p := Nat.mul_lt_mul_of_pos_left hlo (by norm_num)
  have hpN : M / p + 1 ≤ 8 := by
    have h := (Nat.div_lt_iff_lt_mul hpp.pos).mpr hM8p
    omega
  have hcoreeq := uniform_small_core_filter P hP hcore
  have hF := mobiusDivisorSelectionFibre_partner_filter_cutoff
    M 8 P ∅ hpp hpP (by simp) hpN
  rw [hcoreeq] at hF
  have hFpos : c * Real.sqrt N ≤ mobiusDivisorSelectionFibre M P {p} := by
    change c * Real.sqrt N ≤ mobiusDivisorSelectionFibre M P (insert p ∅)
    rw [hF, hM]
    simpa using hpositive N p hp
  have hpM7 : 7 * p ≤ M := by
    calc
      7 * p ≤ 7 * ((b + 1) * N) := Nat.mul_le_mul_left 7 hhi
      _ = M := by dsimp [M, C]; ring
  have hpq : p ≠ q := by
    intro he
    subst q
    omega
  have hcurv := uniform_mixed_eq_late_product M P hq hqM hM2q hqP hpq
  have hMgeN : N ≤ M := by dsimp [M]; nlinarith [hC]
  have hsqrt : Real.sqrt (N : ℝ) ≤ Real.sqrt M :=
    Real.sqrt_le_sqrt (by exact_mod_cast hMgeN)
  have hrootN : 0 ≤ Real.sqrt (N : ℝ) := Real.sqrt_nonneg _
  have hrootM : 0 ≤ Real.sqrt (M : ℝ) := Real.sqrt_nonneg _
  have hNr : (N : ℝ) = Real.sqrt N * Real.sqrt N := by
    rw [← pow_two, Real.sq_sqrt (Nat.cast_nonneg N)]
  have hCN : (M : ℝ) = (C : ℝ) * N := by dsimp [M]; push_cast; ring
  have hDM : mobiusDivisorDilationChannel M q ≤ -d * Real.sqrt M := hMq
  have hFnonneg : 0 ≤ c * Real.sqrt N := by positivity
  have hDnonpos : mobiusDivisorDilationChannel M q ≤ 0 := by
    have : 0 ≤ d * Real.sqrt M := by positivity
    linarith
  have hscale : (N : ℝ) ≤ Real.sqrt N * Real.sqrt M := by
    calc
      (N : ℝ) = Real.sqrt N * Real.sqrt N := hNr
      _ ≤ Real.sqrt N * Real.sqrt M :=
        mul_le_mul_of_nonneg_left hsqrt hrootN
  change mobiusDivisorSelectionEnergy M (insert q (insert p P)) -
      mobiusDivisorSelectionEnergy M (insert p P) -
      mobiusDivisorSelectionEnergy M (insert q P) +
        mobiusDivisorSelectionEnergy M P ≤ -κ * (M : ℝ)
  rw [hcurv]
  dsimp [κ]
  have hCpos : (0 : ℝ) < C := by exact_mod_cast hC
  have hkey : (c * d / (C : ℝ)) * (M : ℝ) = c * d * N := by
    rw [hCN]
    field_simp
  have hFle : mobiusDivisorSelectionFibre M P {p} *
      mobiusDivisorDilationChannel M q ≤
      (c * Real.sqrt N) * mobiusDivisorDilationChannel M q :=
    mul_le_mul_of_nonpos_right hFpos hDnonpos
  have hDle : (c * Real.sqrt N) * mobiusDivisorDilationChannel M q ≤
      (c * Real.sqrt N) * (-d * Real.sqrt M) :=
    mul_le_mul_of_nonneg_left hDM hFnonneg
  have hAB : c * d * (N : ℝ) ≤
      c * d * (Real.sqrt N * Real.sqrt M) :=
    mul_le_mul_of_nonneg_left hscale (mul_nonneg hc.le hd.le)
  have hproduct : mobiusDivisorSelectionFibre M P {p} *
      mobiusDivisorDilationChannel M q ≤ -(c * d * N) := by
    calc
      _ ≤ (c * Real.sqrt N) * mobiusDivisorDilationChannel M q := hFle
      _ ≤ (c * Real.sqrt N) * (-d * Real.sqrt M) := hDle
      _ = -(c * d * (Real.sqrt N * Real.sqrt M)) := by ring
      _ ≤ -(c * d * N) := neg_le_neg hAB
  have hproduct_nonpos : mobiusDivisorSelectionFibre M P {p} *
      mobiusDivisorDilationChannel M q ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos (le_trans hFnonneg hFpos) hDnonpos
  calc
    2 * mobiusDivisorSelectionFibre M P {p} *
        mobiusDivisorDilationChannel M q =
        mobiusDivisorSelectionFibre M P {p} *
          mobiusDivisorDilationChannel M q +
        mobiusDivisorSelectionFibre M P {p} *
          mobiusDivisorDilationChannel M q := by ring
    _ ≤ -(c * d * N) + 0 := add_le_add hproduct hproduct_nonpos
    _ = -(c * d * N) := by ring
    _ = -(c * d / (C : ℝ)) * (M : ℝ) := by
      calc
        -(c * d * N) = -((c * d / (C : ℝ)) * M) :=
          congrArg Neg.neg hkey.symm
        _ = _ := by ring

end RHTower
