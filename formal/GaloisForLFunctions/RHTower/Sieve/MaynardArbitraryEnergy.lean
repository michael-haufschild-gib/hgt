import GaloisForLFunctions.RHTower.Sieve.MaynardUniformEnergy
import GaloisForLFunctions.RHTower.Sieve.MaynardEnergyEnvelope

/-!
# Arbitrarily small uniform energy loss

The fixed `41/40` envelope is too coarse in Maynard's ultra-near-one amplitude band.  This file
keeps the divisor and convolution losses variable and proves one uniform `Y^(1+rho)` envelope for
every prescribed `rho > 0`.
-/

noncomputable section

namespace RHTower.Sieve

open Finset ArithmeticFunction

def maynardVariableEta (rho : ℝ) : ℝ := rho / 1000
def maynardVariableXi (rho : ℝ) : ℝ := rho / 2

private theorem maynardVariableEta_pos {rho : ℝ} (hrho : 0 < rho) :
    0 < maynardVariableEta rho := by
  simp [maynardVariableEta, hrho]

private theorem maynardVariableXi_pos {rho : ℝ} (hrho : 0 < rho) :
    0 < maynardVariableXi rho := by
  simp [maynardVariableXi, hrho]

private theorem exists_maynardVariableDivisorConstant {rho : ℝ} (hrho : 0 < rho) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 0 < n →
      (n.divisors.card : ℝ) ≤ C * (n : ℝ) ^ maynardVariableEta rho := by
  exact RHTower.card_divisors_le_const_mul_rpow (maynardVariableEta_pos hrho)

def maynardVariableDivisorConstant (rho : ℝ) : ℝ :=
  if hrho : 0 < rho then Classical.choose (exists_maynardVariableDivisorConstant hrho) else 1

theorem maynardVariableDivisorConstant_pos (rho : ℝ) :
    0 < maynardVariableDivisorConstant rho := by
  by_cases hrho : 0 < rho
  · rw [maynardVariableDivisorConstant, dif_pos hrho]
    exact (Classical.choose_spec (exists_maynardVariableDivisorConstant hrho)).1
  · simp [maynardVariableDivisorConstant, hrho]

theorem card_divisors_le_maynardVariableDivisorConstant
    {rho : ℝ} (hrho : 0 < rho) (n : ℕ) (hn : 0 < n) :
    (n.divisors.card : ℝ) ≤
      maynardVariableDivisorConstant rho * (n : ℝ) ^ maynardVariableEta rho := by
  rw [maynardVariableDivisorConstant, dif_pos hrho]
  exact (Classical.choose_spec (exists_maynardVariableDivisorConstant hrho)).2 n hn

def maynardVariableGroupedConstant (rho : ℝ) : ℝ :=
  maynardVariableDivisorConstant rho * (1 + (maynardVariableEta rho)⁻¹)

theorem maynardVariableGroupedConstant_pos {rho : ℝ} (hrho : 0 < rho) :
    0 < maynardVariableGroupedConstant rho := by
  have heta := maynardVariableEta_pos hrho
  exact mul_pos (maynardVariableDivisorConstant_pos rho)
    (by have : 0 < (maynardVariableEta rho)⁻¹ := inv_pos.mpr heta; linarith)

theorem one_add_log_le_maynardVariable_power
    {rho M : ℝ} (hrho : 0 < rho) (hM : 1 ≤ M) :
    1 + Real.log M ≤
      (1 + (maynardVariableEta rho)⁻¹) * M ^ maynardVariableEta rho := by
  have heta := maynardVariableEta_pos hrho
  have hM0 : 0 ≤ M := le_trans (by norm_num) hM
  have hpow1 : 1 ≤ M ^ maynardVariableEta rho := Real.one_le_rpow hM heta.le
  have hlog := Real.log_le_rpow_div hM0 heta
  calc
    1 + Real.log M ≤ 1 + M ^ maynardVariableEta rho / maynardVariableEta rho :=
      by linarith
    _ ≤ M ^ maynardVariableEta rho +
        M ^ maynardVariableEta rho / maynardVariableEta rho := by linarith
    _ = (1 + (maynardVariableEta rho)⁻¹) *
        M ^ maynardVariableEta rho := by
      rw [div_eq_mul_inv]
      ring

/-- Base grouped-factor energy with a variable loss, uniform in factor type and box. -/
theorem sum_normSq_heathBrownGroupedCoeffVector_le_variable
    {ι : Type*} [Fintype ι] {rho : ℝ} (hrho : 0 < rho)
    (L X : ℕ) (kind : ι → HeathBrownFactorKind) (q : ι → ℕ) :
    ∑ j : Fin (groupedDyadicUpper q),
        ‖groupedDyadicCoeffVector
          (fun i => heathBrownFactorBase L X (kind i)) q j‖ ^ 2
      ≤ (groupedDyadicUpper q : ℝ) *
        (((maynardVariableGroupedConstant rho) *
          (groupedDyadicUpper q : ℝ) ^ (2 * maynardVariableEta rho)) ^
            Fintype.card ι) ^ 2 := by
  let M := groupedDyadicUpper q
  have hM1 : 1 ≤ M := one_le_groupedDyadicUpper q
  have hM1r : (1 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM1
  have hterm : ∀ j : Fin M,
      ‖groupedDyadicCoeffVector
        (fun i => heathBrownFactorBase L X (kind i)) q j‖ ^ 2 ≤
        (((maynardVariableGroupedConstant rho) *
          (M : ℝ) ^ (2 * maynardVariableEta rho)) ^ Fintype.card ι) ^ 2 := by
    intro j
    have hnpos : 0 < (j : ℕ) + 1 := by omega
    have hd := card_divisors_le_maynardVariableDivisorConstant hrho
      ((j : ℕ) + 1) hnpos
    have hjcast : ((((j : ℕ) + 1 : ℕ) : ℝ)) ≤ (M : ℝ) := by
      exact_mod_cast j.isLt
    have heta := maynardVariableEta_pos hrho
    have hmono : ((((j : ℕ) + 1 : ℕ) : ℝ) ^ maynardVariableEta rho) ≤
        (M : ℝ) ^ maynardVariableEta rho :=
      Real.rpow_le_rpow (by positivity) hjcast heta.le
    have hdM : (((((j : ℕ) + 1).divisors.card : ℕ) : ℝ)) ≤
        maynardVariableDivisorConstant rho *
          (M : ℝ) ^ maynardVariableEta rho :=
      hd.trans (mul_le_mul_of_nonneg_left hmono
        (maynardVariableDivisorConstant_pos rho).le)
    let W : ℝ := 1 + Real.log (M : ℝ)
    have hW0 : 0 ≤ W := by
      dsimp [W]
      have := Real.log_nonneg hM1r
      linarith
    have hfactor : ∀ i n,
        ‖arithmeticDyadicBlock
          (heathBrownFactorBase L X (kind i)) (q i) n‖ ≤ W := by
      exact norm_heathBrownGroupedFactorBlock_le L X kind q
    have hnorm := norm_groupedDyadicProduct_le_divisors_mul_pow
      (fun i => heathBrownFactorBase L X (kind i)) q hW0 hfactor ((j : ℕ) + 1)
    have hnorm' : ‖groupedDyadicCoeffVector
          (fun i => heathBrownFactorBase L X (kind i)) q j‖ ≤
        (((((j : ℕ) + 1).divisors.card : ℕ) : ℝ) * W) ^ Fintype.card ι := by
      simpa [groupedDyadicCoeffVector, complexCoeff_apply] using hnorm
    have hlog := one_add_log_le_maynardVariable_power hrho hM1r
    have hbase : (((((j : ℕ) + 1).divisors.card : ℕ) : ℝ) * W) ≤
        maynardVariableGroupedConstant rho *
          (M : ℝ) ^ (2 * maynardVariableEta rho) := by
      have hm := mul_le_mul hdM hlog hW0
        (mul_nonneg (maynardVariableDivisorConstant_pos rho).le
          (Real.rpow_nonneg (by positivity) _))
      calc
        (((((j : ℕ) + 1).divisors.card : ℕ) : ℝ) * W)
            ≤ (maynardVariableDivisorConstant rho *
                (M : ℝ) ^ maynardVariableEta rho) *
              ((1 + (maynardVariableEta rho)⁻¹) *
                (M : ℝ) ^ maynardVariableEta rho) := hm
        _ = maynardVariableGroupedConstant rho *
              (M : ℝ) ^ (2 * maynardVariableEta rho) := by
          rw [show 2 * maynardVariableEta rho =
            maynardVariableEta rho + maynardVariableEta rho by ring,
            Real.rpow_add (by positivity)]
          simp [maynardVariableGroupedConstant]
          ring
    have hvec := hnorm'.trans
      (pow_le_pow_left₀ (by positivity) hbase (Fintype.card ι))
    exact pow_le_pow_left₀ (norm_nonneg _) hvec 2
  calc
    ∑ j : Fin (groupedDyadicUpper q),
        ‖groupedDyadicCoeffVector
          (fun i => heathBrownFactorBase L X (kind i)) q j‖ ^ 2
      ≤ ∑ _j : Fin M,
          (((maynardVariableGroupedConstant rho) *
            (M : ℝ) ^ (2 * maynardVariableEta rho)) ^ Fintype.card ι) ^ 2 :=
        Finset.sum_le_sum fun j _ => hterm j
    _ = (M : ℝ) *
          (((maynardVariableGroupedConstant rho) *
            (M : ℝ) ^ (2 * maynardVariableEta rho)) ^ Fintype.card ι) ^ 2 := by
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    _ = _ := rfl

private theorem exists_maynardVariableRaiseConstant
    (rho : ℝ) (ell : ℕ) (hrho : 0 < rho) (hell : 0 < ell) :
    ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ), 1 ≤ N → ∀ a : Fin N → ℂ,
      ∑ j : Fin (N ^ ell), ‖convPow N ell a j‖ ^ 2 ≤
        C * ((N ^ ell : ℕ) : ℝ) ^ maynardVariableXi rho *
          (∑ n : Fin N, ‖a n‖ ^ 2) ^ ell := by
  exact exists_sum_normSq_convPow_le_rpow ell hell (maynardVariableXi_pos hrho)

def maynardVariableRaiseConstant (rho : ℝ) (ell : ℕ) : ℝ :=
  if h : 0 < rho ∧ 0 < ell then
    Classical.choose (exists_maynardVariableRaiseConstant rho ell h.1 h.2)
  else 1

theorem maynardVariableRaiseConstant_pos (rho : ℝ) (ell : ℕ) :
    0 < maynardVariableRaiseConstant rho ell := by
  by_cases h : 0 < rho ∧ 0 < ell
  · rw [maynardVariableRaiseConstant, dif_pos h]
    exact (Classical.choose_spec
      (exists_maynardVariableRaiseConstant rho ell h.1 h.2)).1
  · simp [maynardVariableRaiseConstant, h]

theorem sum_normSq_convPow_le_maynardVariableRaiseConstant
    {rho : ℝ} (hrho : 0 < rho) (ell : ℕ) (hell : 0 < ell)
    (N : ℕ) (hN : 1 ≤ N) (a : Fin N → ℂ) :
    ∑ j : Fin (N ^ ell), ‖convPow N ell a j‖ ^ 2 ≤
      maynardVariableRaiseConstant rho ell *
        ((N ^ ell : ℕ) : ℝ) ^ maynardVariableXi rho *
        (∑ n : Fin N, ‖a n‖ ^ 2) ^ ell := by
  rw [maynardVariableRaiseConstant, dif_pos ⟨hrho, hell⟩]
  exact (Classical.choose_spec
    (exists_maynardVariableRaiseConstant rho ell hrho hell)).2 N hN a

def maynardVariableUniformRaiseConstant (rho : ℝ) : ℝ :=
  ∑ ell ∈ Finset.range 52, maynardVariableRaiseConstant rho ell

theorem maynardVariableRaiseConstant_le_uniform
    (rho : ℝ) {ell : ℕ} (hell51 : ell ≤ 51) :
    maynardVariableRaiseConstant rho ell ≤ maynardVariableUniformRaiseConstant rho := by
  dsimp [maynardVariableUniformRaiseConstant]
  exact Finset.single_le_sum
    (fun j hj => (maynardVariableRaiseConstant_pos rho j).le)
    (by simp; omega)

theorem maynardVariableUniformRaiseConstant_pos (rho : ℝ) :
    0 < maynardVariableUniformRaiseConstant rho := by
  exact (maynardVariableRaiseConstant_pos rho 1).trans_le
    (maynardVariableRaiseConstant_le_uniform rho (by norm_num))

theorem sum_normSq_convPow_heathBrownGrouped_le_variable_raw
    {ι : Type*} [Fintype ι] {rho : ℝ} (hrho : 0 < rho)
    (ell : ℕ) (hell : 0 < ell) (hell51 : ell ≤ 51)
    (L X : ℕ) (kind : ι → HeathBrownFactorKind) (q : ι → ℕ) :
    ∑ j : Fin ((groupedDyadicUpper q) ^ ell),
      ‖convPow (groupedDyadicUpper q) ell
        (groupedDyadicCoeffVector
          (fun i => heathBrownFactorBase L X (kind i)) q) j‖ ^ 2 ≤
      maynardVariableUniformRaiseConstant rho *
        (((groupedDyadicUpper q) ^ ell : ℕ) : ℝ) ^ maynardVariableXi rho *
        (((groupedDyadicUpper q : ℝ) *
          ((maynardVariableGroupedConstant rho *
            (groupedDyadicUpper q : ℝ) ^ (2 * maynardVariableEta rho)) ^
              Fintype.card ι) ^ 2) ^ ell) := by
  have hraw := sum_normSq_convPow_le_maynardVariableRaiseConstant hrho
    ell hell (groupedDyadicUpper q) (one_le_groupedDyadicUpper q)
      (groupedDyadicCoeffVector
        (fun i => heathBrownFactorBase L X (kind i)) q)
  have hbase := sum_normSq_heathBrownGroupedCoeffVector_le_variable
    hrho L X kind q
  have hsum0 : 0 ≤ ∑ n : Fin (groupedDyadicUpper q),
      ‖groupedDyadicCoeffVector
        (fun i => heathBrownFactorBase L X (kind i)) q n‖ ^ 2 :=
    Finset.sum_nonneg fun j _ => sq_nonneg _
  have hbasePow := pow_le_pow_left₀ hsum0 hbase ell
  let Zpow : ℝ :=
    (((groupedDyadicUpper q) ^ ell : ℕ) : ℝ) ^ maynardVariableXi rho
  have hZpow0 : 0 ≤ Zpow := Real.rpow_nonneg (Nat.cast_nonneg _) _
  have hreplaceBase :
      (maynardVariableRaiseConstant rho ell * Zpow) *
          (∑ n : Fin (groupedDyadicUpper q),
            ‖groupedDyadicCoeffVector
              (fun i => heathBrownFactorBase L X (kind i)) q n‖ ^ 2) ^ ell ≤
        (maynardVariableRaiseConstant rho ell * Zpow) *
          ((groupedDyadicUpper q : ℝ) *
            ((maynardVariableGroupedConstant rho *
              (groupedDyadicUpper q : ℝ) ^ (2 * maynardVariableEta rho)) ^
                Fintype.card ι) ^ 2) ^ ell :=
    mul_le_mul_of_nonneg_left hbasePow
      (mul_nonneg (maynardVariableRaiseConstant_pos rho ell).le hZpow0)
  have hCrZ : maynardVariableRaiseConstant rho ell * Zpow ≤
      maynardVariableUniformRaiseConstant rho * Zpow :=
    mul_le_mul_of_nonneg_right
      (maynardVariableRaiseConstant_le_uniform rho hell51) hZpow0
  have hbaseRight0 : 0 ≤ (groupedDyadicUpper q : ℝ) *
      ((maynardVariableGroupedConstant rho *
        (groupedDyadicUpper q : ℝ) ^ (2 * maynardVariableEta rho)) ^
          Fintype.card ι) ^ 2 := by positivity
  have hreplaceConstant := mul_le_mul_of_nonneg_right hCrZ
    (pow_nonneg hbaseRight0 ell)
  simpa [Zpow, mul_assoc] using hraw.trans (hreplaceBase.trans hreplaceConstant)

private theorem variable_rpow_natPow_comm {x a : ℝ} (hx : 0 < x) (n : ℕ) :
    (x ^ a) ^ n = (x ^ n) ^ a := by
  calc
    (x ^ a) ^ n = (x ^ a) ^ (n : ℝ) := by rw [Real.rpow_natCast]
    _ = x ^ (a * (n : ℝ)) := (Real.rpow_mul hx.le _ _).symm
    _ = x ^ ((n : ℝ) * a) := by ring
    _ = (x ^ (n : ℝ)) ^ a := Real.rpow_mul hx.le _ _
    _ = (x ^ n) ^ a := by rw [Real.rpow_natCast]

private theorem variable_natPow_rpow_flat {x a : ℝ} (hx : 0 < x) (n : ℕ) :
    (x ^ n) ^ a = x ^ (a * (n : ℝ)) := by
  calc
    (x ^ n) ^ a = (x ^ (n : ℝ)) ^ a := by rw [Real.rpow_natCast]
    _ = x ^ ((n : ℝ) * a) := (Real.rpow_mul hx.le _ _).symm
    _ = x ^ (a * (n : ℝ)) := by ring

private theorem maynardVariableEnergy_algebra
    {M P rho : ℝ} (hM : 0 < M) (w ell : ℕ) :
    (M ^ ell) ^ maynardVariableXi rho *
        (M * ((P * M ^ (2 * maynardVariableEta rho)) ^ w) ^ 2) ^ ell =
      P ^ (2 * w * ell) *
        (M ^ ell) ^ (maynardVariableXi rho + 1 +
          4 * maynardVariableEta rho * w) := by
  let n : ℕ := 2 * w * ell
  have hn : w * (2 * ell) = n := by
    simp [n, mul_left_comm, mul_comm]
  have hcore :
      (M * ((P * M ^ (2 * maynardVariableEta rho)) ^ w) ^ 2) ^ ell =
        M ^ ell *
          (P ^ n * M ^ ((2 * maynardVariableEta rho) * n)) := by
    rw [mul_pow, ← pow_mul]
    rw [← pow_mul]
    rw [hn, mul_pow]
    rw [variable_rpow_natPow_comm hM]
    rw [variable_natPow_rpow_flat hM]
  rw [hcore]
  have hMterm : M ^ ((2 * maynardVariableEta rho) * n) =
      (M ^ ell) ^ (4 * maynardVariableEta rho * w) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hM.le]
    dsimp [n]
    congr 1
    push_cast
    ring
  rw [hMterm]
  have hMell : 0 < M ^ ell := pow_pos hM ell
  have hcombine : (M ^ ell) ^ maynardVariableXi rho * (M ^ ell) *
      (M ^ ell) ^ (4 * maynardVariableEta rho * w) =
        (M ^ ell) ^ (maynardVariableXi rho + 1 +
          4 * maynardVariableEta rho * w) := by
    calc
      (M ^ ell) ^ maynardVariableXi rho * (M ^ ell) *
          (M ^ ell) ^ (4 * maynardVariableEta rho * w) =
        ((M ^ ell) ^ maynardVariableXi rho * (M ^ ell) ^ (1 : ℝ)) *
          (M ^ ell) ^ (4 * maynardVariableEta rho * w) := by simp
      _ = (M ^ ell) ^ (maynardVariableXi rho + 1) *
          (M ^ ell) ^ (4 * maynardVariableEta rho * w) := by
            congr 1
            exact (Real.rpow_add hMell _ _).symm
      _ = (M ^ ell) ^ (maynardVariableXi rho + 1 +
          4 * maynardVariableEta rho * w) :=
            (Real.rpow_add hMell _ _).symm
  calc
    (M ^ ell) ^ maynardVariableXi rho *
        (M ^ ell * (P ^ n *
          (M ^ ell) ^ (4 * maynardVariableEta rho * w))) =
      P ^ n * (((M ^ ell) ^ maynardVariableXi rho * (M ^ ell)) *
        (M ^ ell) ^ (4 * maynardVariableEta rho * w)) := by ring
    _ = P ^ n * (M ^ ell) ^ (maynardVariableXi rho + 1 +
        4 * maynardVariableEta rho * w) := by rw [hcombine]
    _ = P ^ (2 * w * ell) *
        (M ^ ell) ^ (maynardVariableXi rho + 1 +
          4 * maynardVariableEta rho * w) := rfl

def maynardVariablePositiveGroupedConstant (rho : ℝ) : ℝ :=
  max 1 (maynardVariableGroupedConstant rho)

theorem one_le_maynardVariablePositiveGroupedConstant (rho : ℝ) :
    1 ≤ maynardVariablePositiveGroupedConstant rho := le_max_left _ _

theorem maynardVariableGroupedConstant_le_positive (rho : ℝ) :
    maynardVariableGroupedConstant rho ≤ maynardVariablePositiveGroupedConstant rho :=
  le_max_right _ _

def maynardVariableUniformEnergyConstant (rho : ℝ) : ℝ :=
  maynardVariableUniformRaiseConstant rho *
    maynardVariablePositiveGroupedConstant rho ^ 12240 *
    maynardRaisedWidthConstant ^ (1 + rho)

theorem maynardVariableUniformEnergyConstant_pos (rho : ℝ) :
    0 < maynardVariableUniformEnergyConstant rho := by
  dsimp [maynardVariableUniformEnergyConstant]
  exact mul_pos
    (mul_pos (maynardVariableUniformRaiseConstant_pos rho)
      (pow_pos (lt_of_lt_of_le zero_lt_one
        (one_le_maynardVariablePositiveGroupedConstant rho)) _))
    (Real.rpow_pos_of_pos
      (lt_of_lt_of_le zero_lt_one maynardRaisedWidthConstant_one_le) _)

/-- **Arbitrarily small uniform energy loss.**  Every selected group of at most `120` literal
Heath--Brown factors, raised at most `51` times, has coefficient energy `O_rho(Y^(1+rho))`.
The constant is independent of cutoffs, factor kinds, dyadic exponents, and selection labels. -/
theorem sum_normSq_convPow_heathBrownGrouped_le_arbitrary_subcritical
    {ι : Type*} [Fintype ι] {rho : ℝ} (hrho : 0 < rho)
    (hw : Fintype.card ι ≤ 120)
    (ell : ℕ) (hell : 0 < ell) (hell51 : ell ≤ 51)
    (L X : ℕ) (kind : ι → HeathBrownFactorKind) (q : ι → ℕ) :
    ∑ j : Fin ((groupedDyadicUpper q) ^ ell),
      ‖convPow (groupedDyadicUpper q) ell
        (groupedDyadicCoeffVector
          (fun i => heathBrownFactorBase L X (kind i)) q) j‖ ^ 2 ≤
      maynardVariableUniformEnergyConstant rho *
        (((groupedDyadicLower q) ^ ell : ℕ) : ℝ) ^ (1 + rho) := by
  let w : ℕ := Fintype.card ι
  let A : ℕ := groupedDyadicLower q
  let Mnat : ℕ := groupedDyadicUpper q
  let M : ℝ := (Mnat : ℝ)
  let Y : ℝ := ((A ^ ell : ℕ) : ℝ)
  let Z : ℝ := ((Mnat ^ ell : ℕ) : ℝ)
  let P : ℝ := maynardVariableGroupedConstant rho
  let Pplus : ℝ := maynardVariablePositiveGroupedConstant rho
  let p : ℝ := 1 + rho
  have hMnat1 : 1 ≤ Mnat := one_le_groupedDyadicUpper q
  have hM1 : 1 ≤ M := by
    dsimp [M]
    exact_mod_cast hMnat1
  have hM0 : 0 < M := lt_of_lt_of_le zero_lt_one hM1
  have hA1 : 1 ≤ A := one_le_groupedDyadicLower q
  have hY1 : 1 ≤ Y := by
    dsimp [Y]
    exact_mod_cast one_le_pow₀ hA1
  have hZ1 : 1 ≤ Z := by
    dsimp [Z]
    exact_mod_cast one_le_pow₀ hMnat1
  have hp : 0 < p := by dsimp [p]; linarith
  have hn : 2 * w * ell ≤ 12240 := by
    calc
      2 * w * ell ≤ 2 * 120 * 51 := Nat.mul_le_mul
        (Nat.mul_le_mul_left 2 hw) hell51
      _ = 12240 := by norm_num
  have hPpos : 0 < P := by
    dsimp [P]
    exact maynardVariableGroupedConstant_pos hrho
  have hPplus1 : 1 ≤ Pplus := by
    dsimp [Pplus]
    exact one_le_maynardVariablePositiveGroupedConstant rho
  have hPpower : P ^ (2 * w * ell) ≤ Pplus ^ 12240 := by
    calc
      P ^ (2 * w * ell) ≤ Pplus ^ (2 * w * ell) :=
        pow_le_pow_left₀ hPpos.le
          (maynardVariableGroupedConstant_le_positive rho) _
      _ ≤ Pplus ^ 12240 := pow_le_pow_right₀ hPplus1 hn
  have hwreal : (w : ℝ) ≤ 120 := by exact_mod_cast hw
  have hexponent : maynardVariableXi rho + 1 +
      4 * maynardVariableEta rho * w ≤ p := by
    dsimp [maynardVariableXi, maynardVariableEta, p]
    nlinarith
  have hZpower : Z ^ (maynardVariableXi rho + 1 +
      4 * maynardVariableEta rho * w) ≤ Z ^ p :=
    Real.rpow_le_rpow_of_exponent_le hZ1 hexponent
  have hwidthNat : Mnat ^ ell ≤ 2 ^ 6120 * A ^ ell := by
    have hfactor : Mnat = A * 2 ^ w := by
      dsimp [Mnat, A, w]
      exact groupedDyadicUpper_eq_lower_mul_twoPow q
    rw [hfactor, mul_pow, ← pow_mul]
    have hwe : w * ell ≤ 6120 := by
      calc
        w * ell ≤ 120 * 51 := Nat.mul_le_mul hw hell51
        _ = 6120 := by norm_num
    simpa [mul_comm] using Nat.mul_le_mul_right (A ^ ell)
      (Nat.pow_le_pow_right (by norm_num : 0 < 2) hwe)
  have hZwidth : Z ≤ maynardRaisedWidthConstant * Y := by
    have hcast := (Nat.cast_le (α := ℝ)).mpr hwidthNat
    change ((Mnat ^ ell : ℕ) : ℝ) ≤
      ((2 ^ 6120 : ℕ) : ℝ) * ((A ^ ell : ℕ) : ℝ)
    simpa only [Nat.cast_mul] using hcast
  have hwidthPower : Z ^ p ≤
      maynardRaisedWidthConstant ^ p * Y ^ p := by
    calc
      Z ^ p ≤ (maynardRaisedWidthConstant * Y) ^ p :=
        Real.rpow_le_rpow (by linarith) hZwidth hp.le
      _ = maynardRaisedWidthConstant ^ p * Y ^ p :=
        Real.mul_rpow
          (by linarith [maynardRaisedWidthConstant_one_le]) (by linarith)
  have hraw := sum_normSq_convPow_heathBrownGrouped_le_variable_raw
    hrho ell hell hell51 L X kind q
  have hnormalize :
      Z ^ maynardVariableXi rho *
          (M * ((P * M ^ (2 * maynardVariableEta rho)) ^ w) ^ 2) ^ ell =
        P ^ (2 * w * ell) *
          Z ^ (maynardVariableXi rho + 1 +
            4 * maynardVariableEta rho * w) := by
    have halg := maynardVariableEnergy_algebra (rho := rho) hM0 w ell (P := P)
    have hZ : Z = M ^ ell := by
      dsimp [Z, M, Mnat]
      rw [Nat.cast_pow]
    simpa [hZ] using halg
  have hraw' :
      ∑ j : Fin ((groupedDyadicUpper q) ^ ell),
        ‖convPow (groupedDyadicUpper q) ell
          (groupedDyadicCoeffVector
            (fun i => heathBrownFactorBase L X (kind i)) q) j‖ ^ 2 ≤
        maynardVariableUniformRaiseConstant rho *
          (P ^ (2 * w * ell) *
            Z ^ (maynardVariableXi rho + 1 +
              4 * maynardVariableEta rho * w)) := by
    rw [← hnormalize]
    simpa [Z, M, Mnat, P, w, mul_assoc] using hraw
  have hCu0 : 0 ≤ maynardVariableUniformRaiseConstant rho :=
    (maynardVariableUniformRaiseConstant_pos rho).le
  have hPplusPow0 : 0 ≤ Pplus ^ 12240 := pow_nonneg (by linarith) _
  have hZexp0 : 0 ≤ Z ^ (maynardVariableXi rho + 1 +
      4 * maynardVariableEta rho * w) :=
    Real.rpow_nonneg (by linarith) _
  have hWpow0 : 0 ≤ maynardRaisedWidthConstant ^ p :=
    Real.rpow_nonneg (by linarith [maynardRaisedWidthConstant_one_le]) _
  calc
    ∑ j : Fin ((groupedDyadicUpper q) ^ ell),
        ‖convPow (groupedDyadicUpper q) ell
          (groupedDyadicCoeffVector
            (fun i => heathBrownFactorBase L X (kind i)) q) j‖ ^ 2
      ≤ maynardVariableUniformRaiseConstant rho *
          (P ^ (2 * w * ell) *
            Z ^ (maynardVariableXi rho + 1 +
              4 * maynardVariableEta rho * w)) := hraw'
    _ ≤ maynardVariableUniformRaiseConstant rho *
          (Pplus ^ 12240 * Z ^ p) := by
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul hPpower hZpower hZexp0 hPplusPow0) hCu0
    _ ≤ maynardVariableUniformRaiseConstant rho *
          (Pplus ^ 12240 *
            (maynardRaisedWidthConstant ^ p * Y ^ p)) := by
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hwidthPower hPplusPow0) hCu0
    _ = maynardVariableUniformEnergyConstant rho * Y ^ p := by
      change maynardVariableUniformRaiseConstant rho *
          (maynardVariablePositiveGroupedConstant rho ^ 12240 *
            (maynardRaisedWidthConstant ^ (1 + rho) * Y ^ (1 + rho))) =
        (maynardVariableUniformRaiseConstant rho *
          maynardVariablePositiveGroupedConstant rho ^ 12240 *
            maynardRaisedWidthConstant ^ (1 + rho)) * Y ^ (1 + rho)
      ring
    _ = _ := rfl

end RHTower.Sieve

