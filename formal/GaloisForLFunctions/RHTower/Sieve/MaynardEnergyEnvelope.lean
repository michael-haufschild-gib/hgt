import GaloisForLFunctions.RHTower.Sieve.MaynardUniformEnergy
import GaloisForLFunctions.RHTower.Sieve.MaynardEnergyScalar

set_option maxRecDepth 10000

noncomputable section
namespace RHTower.Sieve

open Finset ArithmeticFunction

def maynardEnergyEta : ℝ := 1 / 100000
def maynardEnergyRho : ℝ := 1 / 100000

private theorem exists_maynardEnergyBaseConstant :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 0 < n →
      (n.divisors.card : ℝ) ≤ C * (n : ℝ) ^ maynardEnergyEta := by
  exact RHTower.card_divisors_le_const_mul_rpow
    (by simp [maynardEnergyEta])

def maynardEnergyBaseConstant : ℝ :=
  Classical.choose exists_maynardEnergyBaseConstant

theorem maynardEnergyBaseConstant_pos : 0 < maynardEnergyBaseConstant :=
  (Classical.choose_spec exists_maynardEnergyBaseConstant).1

theorem card_divisors_le_maynardEnergyBaseConstant
    (n : ℕ) (hn : 0 < n) :
    (n.divisors.card : ℝ) ≤
      maynardEnergyBaseConstant * (n : ℝ) ^ maynardEnergyEta :=
  (Classical.choose_spec exists_maynardEnergyBaseConstant).2 n hn

theorem sum_normSq_heathBrownGroupedCoeffVector_le_maynardBase
    {ι : Type*} [Fintype ι]
    (L X : ℕ) (kind : ι → HeathBrownFactorKind) (q : ι → ℕ) :
    ∑ j : Fin (groupedDyadicUpper q),
        ‖groupedDyadicCoeffVector
          (fun i => heathBrownFactorBase L X (kind i)) q j‖ ^ 2
      ≤ (groupedDyadicUpper q : ℝ) *
        ((maynardEnergyBaseConstant *
          (groupedDyadicUpper q : ℝ) ^ maynardEnergyEta *
          (1 + Real.log (groupedDyadicUpper q : ℝ))) ^ Fintype.card ι) ^ 2 := by
  let M := groupedDyadicUpper q
  have hM1 : 1 ≤ M := one_le_groupedDyadicUpper q
  have hlog0 : 0 ≤ Real.log (M : ℝ) := Real.log_nonneg (by exact_mod_cast hM1)
  have hterm : ∀ j : Fin M,
      ‖groupedDyadicCoeffVector
        (fun i => heathBrownFactorBase L X (kind i)) q j‖ ^ 2 ≤
        ((maynardEnergyBaseConstant * (M : ℝ) ^ maynardEnergyEta *
          (1 + Real.log (M : ℝ))) ^ Fintype.card ι) ^ 2 := by
    intro j
    have hnpos : 0 < (j : ℕ) + 1 := by omega
    have hd := card_divisors_le_maynardEnergyBaseConstant ((j : ℕ) + 1) hnpos
    have hjcast : ((((j : ℕ) + 1 : ℕ) : ℝ)) ≤ (M : ℝ) := by
      exact_mod_cast j.isLt
    have hmono : ((((j : ℕ) + 1 : ℕ) : ℝ) ^ maynardEnergyEta) ≤
        (M : ℝ) ^ maynardEnergyEta :=
      Real.rpow_le_rpow (by positivity) hjcast (by simp [maynardEnergyEta])
    have hdM : (((((j : ℕ) + 1).divisors.card : ℕ) : ℝ)) ≤
        maynardEnergyBaseConstant * (M : ℝ) ^ maynardEnergyEta :=
      hd.trans (mul_le_mul_of_nonneg_left hmono maynardEnergyBaseConstant_pos.le)
    have hfactor := norm_heathBrownGroupedFactorBlock_le L X kind q
    have hnorm := norm_groupedDyadicProduct_le_divisors_mul_pow
      (fun i => heathBrownFactorBase L X (kind i)) q (by linarith) hfactor
        ((j : ℕ) + 1)
    have hbase : (((((j : ℕ) + 1).divisors.card : ℕ) : ℝ)) *
          (1 + Real.log (M : ℝ)) ≤
        (maynardEnergyBaseConstant * (M : ℝ) ^ maynardEnergyEta) *
          (1 + Real.log (M : ℝ)) :=
      mul_le_mul_of_nonneg_right hdM (by linarith)
    have hnorm' : ‖groupedDyadicCoeffVector
        (fun i => heathBrownFactorBase L X (kind i)) q j‖ ≤
        (((((j : ℕ) + 1).divisors.card : ℕ) : ℝ) *
          (1 + Real.log (M : ℝ))) ^ Fintype.card ι := by
      simpa [groupedDyadicCoeffVector, complexCoeff_apply] using hnorm
    have hvec := hnorm'.trans
      (pow_le_pow_left₀ (by positivity) hbase (Fintype.card ι))
    exact pow_le_pow_left₀ (norm_nonneg _) (by simpa [mul_assoc] using hvec) 2
  calc
    ∑ j : Fin (groupedDyadicUpper q),
        ‖groupedDyadicCoeffVector
          (fun i => heathBrownFactorBase L X (kind i)) q j‖ ^ 2
        ≤ ∑ _j : Fin M,
            ((maynardEnergyBaseConstant * (M : ℝ) ^ maynardEnergyEta *
              (1 + Real.log (M : ℝ))) ^ Fintype.card ι) ^ 2 :=
          Finset.sum_le_sum fun j _ => hterm j
    _ = (M : ℝ) *
        ((maynardEnergyBaseConstant * (M : ℝ) ^ maynardEnergyEta *
          (1 + Real.log (M : ℝ))) ^ Fintype.card ι) ^ 2 := by
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    _ = _ := rfl

theorem one_add_log_le_maynardEnergy_power
    {M : ℝ} (hM : 1 ≤ M) :
    1 + Real.log M ≤ 100001 * M ^ maynardEnergyEta := by
  have hM0 : 0 < M := lt_of_lt_of_le zero_lt_one hM
  have hpow1 : 1 ≤ M ^ maynardEnergyEta :=
    Real.one_le_rpow hM (by simp [maynardEnergyEta])
  dsimp [maynardEnergyEta] at hpow1
  have hlog := Real.log_le_sub_one_of_pos
    (Real.rpow_pos_of_pos hM0 maynardEnergyEta)
  rw [Real.log_rpow hM0] at hlog
  have hscaled := mul_le_mul_of_nonneg_left hlog (by norm_num : (0 : ℝ) ≤ 100000)
  dsimp [maynardEnergyEta] at hscaled ⊢
  have hscaled' : Real.log M ≤ 100000 * (M ^ (1 / 100000 : ℝ) - 1) := by
    calc
      Real.log M = 100000 * (1 / 100000 * Real.log M) := by ring
      _ ≤ 100000 * (M ^ (1 / 100000 : ℝ) - 1) := hscaled
  nlinarith [hscaled', hpow1]

def maynardEnergyGroupedConstant : ℝ :=
  100001 * maynardEnergyBaseConstant

theorem maynardEnergyGroupedConstant_pos :
    0 < maynardEnergyGroupedConstant := by
  dsimp [maynardEnergyGroupedConstant]
  exact mul_pos (by norm_num) maynardEnergyBaseConstant_pos

theorem sum_normSq_heathBrownGroupedCoeffVector_le_maynardPower
    {ι : Type*} [Fintype ι]
    (L X : ℕ) (kind : ι → HeathBrownFactorKind) (q : ι → ℕ) :
    ∑ j : Fin (groupedDyadicUpper q),
        ‖groupedDyadicCoeffVector
          (fun i => heathBrownFactorBase L X (kind i)) q j‖ ^ 2
      ≤ (groupedDyadicUpper q : ℝ) *
        ((maynardEnergyGroupedConstant *
          (groupedDyadicUpper q : ℝ) ^ (1 / 50000 : ℝ)) ^
            Fintype.card ι) ^ 2 := by
  let M : ℝ := (groupedDyadicUpper q : ℝ)
  have hM1 : 1 ≤ M := by
    dsimp [M]
    exact_mod_cast one_le_groupedDyadicUpper q
  have hlog := one_add_log_le_maynardEnergy_power hM1
  have hfactor : maynardEnergyBaseConstant * M ^ maynardEnergyEta *
      (1 + Real.log M) ≤
        maynardEnergyGroupedConstant * M ^ (1 / 50000 : ℝ) := by
    calc
      maynardEnergyBaseConstant * M ^ maynardEnergyEta * (1 + Real.log M)
          ≤ maynardEnergyBaseConstant * M ^ maynardEnergyEta *
              (100001 * M ^ maynardEnergyEta) := by
            exact mul_le_mul_of_nonneg_left hlog
              (mul_nonneg maynardEnergyBaseConstant_pos.le
                (Real.rpow_nonneg (by linarith) _))
      _ = maynardEnergyGroupedConstant * M ^ (1 / 50000 : ℝ) := by
            rw [show (1 / 50000 : ℝ) = maynardEnergyEta + maynardEnergyEta by
              norm_num [maynardEnergyEta]]
            rw [Real.rpow_add (lt_of_lt_of_le zero_lt_one hM1)]
            simp [maynardEnergyGroupedConstant]
            ring
  have hleft0 : 0 ≤ maynardEnergyBaseConstant * M ^ maynardEnergyEta *
      (1 + Real.log M) := by
    have hlog0 : 0 ≤ Real.log M := Real.log_nonneg hM1
    exact mul_nonneg
      (mul_nonneg maynardEnergyBaseConstant_pos.le
        (Real.rpow_nonneg (by linarith) _)) (by linarith)
  have hpow := pow_le_pow_left₀ hleft0 hfactor (Fintype.card ι)
  have hsq := pow_le_pow_left₀ (pow_nonneg hleft0 _) hpow 2
  exact (sum_normSq_heathBrownGroupedCoeffVector_le_maynardBase L X kind q).trans
    (mul_le_mul_of_nonneg_left (by simpa [M, mul_assoc] using hsq)
      (by positivity))

private theorem exists_maynardRaiseConstant (ell : ℕ) (hell : 0 < ell) :
    ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ), 1 ≤ N → ∀ a : Fin N → ℂ,
      ∑ j : Fin (N ^ ell), ‖convPow N ell a j‖ ^ 2 ≤
        C * ((N ^ ell : ℕ) : ℝ) ^ maynardEnergyRho *
          (∑ n : Fin N, ‖a n‖ ^ 2) ^ ell := by
  exact exists_sum_normSq_convPow_le_rpow ell hell
    (by simp [maynardEnergyRho])

def maynardRaiseConstant (ell : ℕ) : ℝ :=
  if hell : 0 < ell then Classical.choose (exists_maynardRaiseConstant ell hell) else 1

theorem maynardRaiseConstant_pos (ell : ℕ) : 0 < maynardRaiseConstant ell := by
  by_cases hell : 0 < ell
  · rw [maynardRaiseConstant, dif_pos hell]
    exact (Classical.choose_spec (exists_maynardRaiseConstant ell hell)).1
  · simp [maynardRaiseConstant, hell]

theorem sum_normSq_convPow_le_maynardRaiseConstant
    (ell : ℕ) (hell : 0 < ell) (N : ℕ) (hN : 1 ≤ N) (a : Fin N → ℂ) :
    ∑ j : Fin (N ^ ell), ‖convPow N ell a j‖ ^ 2 ≤
      maynardRaiseConstant ell * ((N ^ ell : ℕ) : ℝ) ^ maynardEnergyRho *
        (∑ n : Fin N, ‖a n‖ ^ 2) ^ ell := by
  rw [maynardRaiseConstant, dif_pos hell]
  exact (Classical.choose_spec (exists_maynardRaiseConstant ell hell)).2 N hN a

def maynardUniformRaiseConstant : ℝ :=
  ∑ ell ∈ Finset.range 52, maynardRaiseConstant ell

theorem maynardRaiseConstant_le_uniform
    {ell : ℕ} (hell51 : ell ≤ 51) :
    maynardRaiseConstant ell ≤ maynardUniformRaiseConstant := by
  dsimp [maynardUniformRaiseConstant]
  exact Finset.single_le_sum
    (fun j hj => (maynardRaiseConstant_pos j).le)
    (by simp; omega)

theorem maynardUniformRaiseConstant_pos : 0 < maynardUniformRaiseConstant := by
  have hle : maynardRaiseConstant 1 ≤ maynardUniformRaiseConstant :=
    maynardRaiseConstant_le_uniform (by norm_num)
  exact (maynardRaiseConstant_pos 1).trans_le hle

theorem sum_normSq_convPow_heathBrownGrouped_le_maynardUniform
    {ι : Type*} [Fintype ι] (ell : ℕ) (hell : 0 < ell) (hell51 : ell ≤ 51)
    (L X : ℕ) (kind : ι → HeathBrownFactorKind) (q : ι → ℕ) :
    ∑ j : Fin ((groupedDyadicUpper q) ^ ell),
      ‖convPow (groupedDyadicUpper q) ell
        (groupedDyadicCoeffVector
          (fun i => heathBrownFactorBase L X (kind i)) q) j‖ ^ 2 ≤
      maynardUniformRaiseConstant *
        (((groupedDyadicUpper q) ^ ell : ℕ) : ℝ) ^ maynardEnergyRho *
        (((groupedDyadicUpper q : ℝ) *
          ((maynardEnergyGroupedConstant *
            (groupedDyadicUpper q : ℝ) ^ (1 / 50000 : ℝ)) ^
              Fintype.card ι) ^ 2) ^ ell) := by
  have hraw := sum_normSq_convPow_le_maynardRaiseConstant ell hell
    (groupedDyadicUpper q) (one_le_groupedDyadicUpper q)
      (groupedDyadicCoeffVector
        (fun i => heathBrownFactorBase L X (kind i)) q)
  have hbase := sum_normSq_heathBrownGroupedCoeffVector_le_maynardPower
    L X kind q
  have hsum0 : 0 ≤ ∑ n : Fin (groupedDyadicUpper q),
      ‖groupedDyadicCoeffVector
        (fun i => heathBrownFactorBase L X (kind i)) q n‖ ^ 2 :=
    Finset.sum_nonneg fun j _ => sq_nonneg _
  have hbasePow := pow_le_pow_left₀ hsum0 hbase ell
  let Zpow : ℝ :=
    (((groupedDyadicUpper q) ^ ell : ℕ) : ℝ) ^ maynardEnergyRho
  have hZpow0 : 0 ≤ Zpow := Real.rpow_nonneg (Nat.cast_nonneg _) _
  have hreplaceBase :
      (maynardRaiseConstant ell * Zpow) *
          (∑ n : Fin (groupedDyadicUpper q),
            ‖groupedDyadicCoeffVector
              (fun i => heathBrownFactorBase L X (kind i)) q n‖ ^ 2) ^ ell ≤
        (maynardRaiseConstant ell * Zpow) *
          ((groupedDyadicUpper q : ℝ) *
            ((maynardEnergyGroupedConstant *
              (groupedDyadicUpper q : ℝ) ^ (1 / 50000 : ℝ)) ^
                Fintype.card ι) ^ 2) ^ ell :=
    mul_le_mul_of_nonneg_left hbasePow
      (mul_nonneg (maynardRaiseConstant_pos ell).le hZpow0)
  have hCrZ : maynardRaiseConstant ell * Zpow ≤
      maynardUniformRaiseConstant * Zpow := mul_le_mul_of_nonneg_right
    (maynardRaiseConstant_le_uniform hell51)
    hZpow0
  have hbaseRight0 : 0 ≤ (groupedDyadicUpper q : ℝ) *
      ((maynardEnergyGroupedConstant *
        (groupedDyadicUpper q : ℝ) ^ (1 / 50000 : ℝ)) ^
          Fintype.card ι) ^ 2 := by positivity
  have hreplaceConstant := mul_le_mul_of_nonneg_right hCrZ
    (pow_nonneg hbaseRight0 ell)
  simpa [Zpow] using hraw.trans (hreplaceBase.trans hreplaceConstant)

private theorem rpow_natPow_comm {x a : ℝ} (hx : 0 < x) (n : ℕ) :
    (x ^ a) ^ n = (x ^ n) ^ a := by
  calc
    (x ^ a) ^ n = (x ^ a) ^ (n : ℝ) := by rw [Real.rpow_natCast]
    _ = x ^ (a * (n : ℝ)) := (Real.rpow_mul hx.le _ _).symm
    _ = x ^ ((n : ℝ) * a) := by ring
    _ = (x ^ (n : ℝ)) ^ a := Real.rpow_mul hx.le _ _
    _ = (x ^ n) ^ a := by rw [Real.rpow_natCast]

private theorem natPow_rpow_flat {x a : ℝ} (hx : 0 < x) (n : ℕ) :
    (x ^ n) ^ a = x ^ (a * (n : ℝ)) := by
  calc
    (x ^ n) ^ a = (x ^ (n : ℝ)) ^ a := by rw [Real.rpow_natCast]
    _ = x ^ ((n : ℝ) * a) := (Real.rpow_mul hx.le _ _).symm
    _ = x ^ (a * (n : ℝ)) := by ring

private theorem maynardEnergy_algebra
    {M P : ℝ} (hM : 0 < M) (w ell : ℕ) :
    (M ^ ell) ^ maynardEnergyRho *
        (M * ((P * M ^ (1 / 50000 : ℝ)) ^ w) ^ 2) ^ ell =
      P ^ (2 * w * ell) *
        (M ^ ell) ^ (maynardEnergyRho + 1 + (2 / 50000 : ℝ) * w) := by
  let n : ℕ := 2 * w * ell
  have hn : w * (2 * ell) = n := by
    simp [n, mul_left_comm, mul_comm]
  have hcore :
      (M * ((P * M ^ (1 / 50000 : ℝ)) ^ w) ^ 2) ^ ell =
        M ^ ell * (P ^ n * M ^ ((1 / 50000 : ℝ) * n)) := by
    rw [mul_pow, ← pow_mul]
    rw [← pow_mul]
    rw [hn, mul_pow]
    rw [rpow_natPow_comm hM]
    rw [natPow_rpow_flat hM]
  rw [hcore]
  have hMterm : M ^ ((1 / 50000 : ℝ) * n) =
      (M ^ ell) ^ ((2 / 50000 : ℝ) * w) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hM.le]
    dsimp [n]
    congr 1
    push_cast
    ring
  rw [hMterm]
  have hMell : 0 < M ^ ell := pow_pos hM ell
  have hcombine : (M ^ ell) ^ maynardEnergyRho * (M ^ ell) *
      (M ^ ell) ^ ((2 / 50000 : ℝ) * w) =
        (M ^ ell) ^ (maynardEnergyRho + 1 + (2 / 50000 : ℝ) * w) := by
    calc
      (M ^ ell) ^ maynardEnergyRho * (M ^ ell) *
          (M ^ ell) ^ ((2 / 50000 : ℝ) * w) =
        ((M ^ ell) ^ maynardEnergyRho * (M ^ ell) ^ (1 : ℝ)) *
          (M ^ ell) ^ ((2 / 50000 : ℝ) * w) := by simp
      _ = (M ^ ell) ^ (maynardEnergyRho + 1) *
          (M ^ ell) ^ ((2 / 50000 : ℝ) * w) := by
            congr 1
            exact (Real.rpow_add hMell _ _).symm
      _ = (M ^ ell) ^
          (maynardEnergyRho + 1 + (2 / 50000 : ℝ) * w) := by
            exact (Real.rpow_add hMell _ _).symm
  calc
    (M ^ ell) ^ maynardEnergyRho *
        (M ^ ell * (P ^ n * (M ^ ell) ^ ((2 / 50000 : ℝ) * w))) =
      P ^ n * (((M ^ ell) ^ maynardEnergyRho * (M ^ ell)) *
        (M ^ ell) ^ ((2 / 50000 : ℝ) * w)) := by ring
    _ = P ^ n * (M ^ ell) ^
        (maynardEnergyRho + 1 + (2 / 50000 : ℝ) * w) := by
      rw [hcombine]
    _ = P ^ (2 * w * ell) * (M ^ ell) ^
        (maynardEnergyRho + 1 + (2 / 50000 : ℝ) * w) := by
      rfl

def maynardEnergyPositiveGroupedConstant : ℝ :=
  max 1 maynardEnergyGroupedConstant

theorem one_le_maynardEnergyPositiveGroupedConstant :
    1 ≤ maynardEnergyPositiveGroupedConstant := le_max_left _ _

theorem maynardEnergyGroupedConstant_le_positive :
    maynardEnergyGroupedConstant ≤ maynardEnergyPositiveGroupedConstant :=
  le_max_right _ _

def maynardUniformEnergyConstant : ℝ :=
  maynardUniformRaiseConstant * maynardEnergyPositiveGroupedConstant ^ 12240 *
    maynardRaisedWidthConstant ^ (101 / 100 : ℝ)

theorem maynardUniformEnergyConstant_pos :
    0 < maynardUniformEnergyConstant := by
  dsimp [maynardUniformEnergyConstant]
  exact mul_pos
    (mul_pos maynardUniformRaiseConstant_pos
      (pow_pos (lt_of_lt_of_le zero_lt_one
        one_le_maynardEnergyPositiveGroupedConstant) _))
    (Real.rpow_pos_of_pos
      (lt_of_lt_of_le zero_lt_one maynardRaisedWidthConstant_one_le) _)

/-- **Uniform subcritical energy theorem.**  Every literal selected group of at most `120`
factors, raised at most `51` times, has energy `O(Y^(41/40))` with one global constant. -/
theorem sum_normSq_convPow_heathBrownGrouped_le_subcritical
    {ι : Type*} [Fintype ι] (hw : Fintype.card ι ≤ 120)
    (ell : ℕ) (hell : 0 < ell) (hell51 : ell ≤ 51)
    (L X : ℕ) (kind : ι → HeathBrownFactorKind) (q : ι → ℕ) :
    ∑ j : Fin ((groupedDyadicUpper q) ^ ell),
      ‖convPow (groupedDyadicUpper q) ell
        (groupedDyadicCoeffVector
          (fun i => heathBrownFactorBase L X (kind i)) q) j‖ ^ 2 ≤
      maynardUniformEnergyConstant *
        (((groupedDyadicLower q) ^ ell : ℕ) : ℝ) ^ (41 / 40 : ℝ) := by
  let w : ℕ := Fintype.card ι
  let A : ℕ := groupedDyadicLower q
  let Mnat : ℕ := groupedDyadicUpper q
  let M : ℝ := (Mnat : ℝ)
  let Y : ℝ := ((A ^ ell : ℕ) : ℝ)
  let Z : ℝ := ((Mnat ^ ell : ℕ) : ℝ)
  let P : ℝ := maynardEnergyGroupedConstant
  let Pplus : ℝ := maynardEnergyPositiveGroupedConstant
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
  have hn : 2 * w * ell ≤ 12240 := by
    calc
      2 * w * ell ≤ 2 * 120 * 51 := Nat.mul_le_mul
        (Nat.mul_le_mul_left 2 hw) hell51
      _ = 12240 := by norm_num
  have hPpos : 0 < P := maynardEnergyGroupedConstant_pos
  have hPplus1 : 1 ≤ Pplus := one_le_maynardEnergyPositiveGroupedConstant
  have hPpower : P ^ (2 * w * ell) ≤ Pplus ^ 12240 := by
    calc
      P ^ (2 * w * ell) ≤ Pplus ^ (2 * w * ell) :=
        pow_le_pow_left₀ hPpos.le maynardEnergyGroupedConstant_le_positive _
      _ ≤ Pplus ^ 12240 := pow_le_pow_right₀ hPplus1 hn
  have hexponent : maynardEnergyRho + 1 + (2 / 50000 : ℝ) * w ≤
      101 / 100 := by
    have hwreal : (w : ℝ) ≤ 120 := by exact_mod_cast hw
    dsimp [maynardEnergyRho]
    nlinarith
  have hZpower : Z ^ (maynardEnergyRho + 1 + (2 / 50000 : ℝ) * w) ≤
      Z ^ (101 / 100 : ℝ) :=
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
  have hwidthPower : Z ^ (101 / 100 : ℝ) ≤
      maynardRaisedWidthConstant ^ (101 / 100 : ℝ) *
        Y ^ (101 / 100 : ℝ) := by
    calc
      Z ^ (101 / 100 : ℝ) ≤
          (maynardRaisedWidthConstant * Y) ^ (101 / 100 : ℝ) :=
        Real.rpow_le_rpow (by linarith) hZwidth (by norm_num)
      _ = maynardRaisedWidthConstant ^ (101 / 100 : ℝ) *
          Y ^ (101 / 100 : ℝ) :=
        Real.mul_rpow
          (by linarith [maynardRaisedWidthConstant_one_le]) (by linarith)
  have hYpower : Y ^ (101 / 100 : ℝ) ≤ Y ^ (41 / 40 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hY1 (by norm_num)
  have hraw := sum_normSq_convPow_heathBrownGrouped_le_maynardUniform
    ell hell hell51 L X kind q
  have hnormalize :
      Z ^ maynardEnergyRho *
          (M * ((P * M ^ (1 / 50000 : ℝ)) ^ w) ^ 2) ^ ell =
        P ^ (2 * w * ell) *
          Z ^ (maynardEnergyRho + 1 + (2 / 50000 : ℝ) * w) := by
    have halg := maynardEnergy_algebra hM0 w ell (P := P)
    have hZ : Z = M ^ ell := by
      dsimp [Z, M, Mnat]
      rw [Nat.cast_pow]
    simpa [hZ] using halg
  have hraw' :
      ∑ j : Fin ((groupedDyadicUpper q) ^ ell),
        ‖convPow (groupedDyadicUpper q) ell
          (groupedDyadicCoeffVector
            (fun i => heathBrownFactorBase L X (kind i)) q) j‖ ^ 2 ≤
        maynardUniformRaiseConstant *
          (P ^ (2 * w * ell) *
            Z ^ (maynardEnergyRho + 1 + (2 / 50000 : ℝ) * w)) := by
    rw [← hnormalize]
    simpa [Z, M, Mnat, P, w, mul_assoc] using hraw
  have hCu0 : 0 ≤ maynardUniformRaiseConstant :=
    maynardUniformRaiseConstant_pos.le
  have hPplusPow0 : 0 ≤ Pplus ^ 12240 := pow_nonneg (by linarith) _
  have hZexp0 :
      0 ≤ Z ^ (maynardEnergyRho + 1 + (2 / 50000 : ℝ) * w) :=
    Real.rpow_nonneg (by linarith) _
  have hWpow0 : 0 ≤ maynardRaisedWidthConstant ^ (101 / 100 : ℝ) :=
    Real.rpow_nonneg (by linarith [maynardRaisedWidthConstant_one_le]) _
  calc
    ∑ j : Fin ((groupedDyadicUpper q) ^ ell),
        ‖convPow (groupedDyadicUpper q) ell
          (groupedDyadicCoeffVector
            (fun i => heathBrownFactorBase L X (kind i)) q) j‖ ^ 2
        ≤ maynardUniformRaiseConstant *
            (P ^ (2 * w * ell) *
              Z ^ (maynardEnergyRho + 1 + (2 / 50000 : ℝ) * w)) := hraw'
    _ ≤ maynardUniformRaiseConstant *
          (Pplus ^ 12240 * Z ^ (101 / 100 : ℝ)) := by
        exact mul_le_mul_of_nonneg_left
          (mul_le_mul hPpower hZpower hZexp0 hPplusPow0) hCu0
    _ ≤ maynardUniformRaiseConstant *
          (Pplus ^ 12240 *
            (maynardRaisedWidthConstant ^ (101 / 100 : ℝ) *
              Y ^ (101 / 100 : ℝ))) := by
        exact mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left hwidthPower hPplusPow0) hCu0
    _ ≤ maynardUniformRaiseConstant *
          (Pplus ^ 12240 *
            (maynardRaisedWidthConstant ^ (101 / 100 : ℝ) *
              Y ^ (41 / 40 : ℝ))) := by
        exact mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left hYpower hWpow0) hPplusPow0) hCu0
    _ = maynardUniformEnergyConstant * Y ^ (41 / 40 : ℝ) := by
        change maynardUniformRaiseConstant *
            (maynardEnergyPositiveGroupedConstant ^ 12240 *
              (maynardRaisedWidthConstant ^ (101 / 100 : ℝ) *
                Y ^ (41 / 40 : ℝ))) =
          (maynardUniformRaiseConstant *
              maynardEnergyPositiveGroupedConstant ^ 12240 *
                maynardRaisedWidthConstant ^ (101 / 100 : ℝ)) *
            Y ^ (41 / 40 : ℝ)
        ring
    _ = _ := rfl

end RHTower.Sieve
