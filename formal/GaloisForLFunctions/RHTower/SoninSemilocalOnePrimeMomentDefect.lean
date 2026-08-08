import GaloisForLFunctions.RHTower.SoninSemilocalGradingDeformation
import GaloisForLFunctions.RHTower.SoninSemilocalGradingBounds
import GaloisForLFunctions.RHTower.TraceNorm
import Mathlib.NumberTheory.SumPrimeReciprocals

noncomputable section

open Complex Filter MeasureTheory Polynomial Real Set
open scoped BigOperators InnerProductSpace

namespace RHTower

/-- Loss of the normalized second moment caused by one Euler prime. -/
def semilocalOnePrimeMomentDefect (p : ℕ) : ℝ :=
  1 / 2 - semilocalFinitePrimeNormalizedSecondMoment
    (semilocalOnePrimeFamily p)

/-- Positive summand in the one-prime second-moment defect numerator, indexed from one. -/
def semilocalOnePrimeMomentDefectTerm (p m : ℕ) : ℝ :=
  semilocalPrimePoissonRatio p ^ (m + 1) *
    semilocalArchimedeanCharacteristic
      (((m + 1 : ℕ) : ℝ) * Real.log p) *
    Real.tanh (((m + 1 : ℕ) : ℝ) * Real.log p) ^ 2

def semilocalOnePrimeMomentDefectNumerator (p : ℕ) : ℝ :=
  ∑' m : ℕ, semilocalOnePrimeMomentDefectTerm p m

/-- One-prime normalizing-mass summand on the bilateral integer lattice. -/
def semilocalOnePrimeMassTerm (p : ℕ) (m : ℤ) : ℝ :=
  semilocalPrimePoissonRatio p ^ m.natAbs *
    semilocalArchimedeanCharacteristic ((m : ℝ) * Real.log p)

def semilocalOnePrimePositiveMassSeries (p : ℕ) : ℝ :=
  ∑' m : ℕ, semilocalOnePrimeMassTerm p ((m : ℤ) + 1)

theorem semilocalArchimedeanCharacteristic_neg (t : ℝ) :
    semilocalArchimedeanCharacteristic (-t) =
      semilocalArchimedeanCharacteristic t := by
  simp [semilocalArchimedeanCharacteristic]

theorem semilocalOnePrimeMassTerm_even (p : ℕ) :
    Function.Even (semilocalOnePrimeMassTerm p) := by
  intro m
  unfold semilocalOnePrimeMassTerm
  rw [Int.natAbs_neg]
  push_cast
  rw [neg_mul, semilocalArchimedeanCharacteristic_neg]

theorem summable_semilocalOnePrimeMassTerm
    {p : ℕ} (hp : p.Prime) :
    Summable (semilocalOnePrimeMassTerm p) := by
  have hfull := summable_semilocalFinitePrimePoissonMassTerm
    (semilocalOnePrimeFamily p) (fun _ => hp)
  have hcomp := hfull.comp_injective
    (Equiv.funUnique (Fin 1) ℤ).symm.injective
  simpa [semilocalOnePrimeMassTerm, semilocalOnePrimePoissonWeight,
    semilocalOnePrimeLogFrequency, Equiv.funUnique_symm_apply] using! hcomp

theorem semilocalFinitePrimePoissonMass_onePrime
    {p : ℕ} (hp : p.Prime) :
    semilocalFinitePrimePoissonMass (semilocalOnePrimeFamily p) =
      1 + 2 * semilocalOnePrimePositiveMassSeries p := by
  unfold semilocalFinitePrimePoissonMass
  rw [← (Equiv.funUnique (Fin 1) ℤ).symm.tsum_eq]
  rw [show (fun m : ℤ =>
      semilocalFinitePrimePoissonWeight (semilocalOnePrimeFamily p)
          ((Equiv.funUnique (Fin 1) ℤ).symm m) *
        semilocalArchimedeanCharacteristic
          (semilocalFinitePrimeLogFrequency (semilocalOnePrimeFamily p)
            ((Equiv.funUnique (Fin 1) ℤ).symm m))) =
      semilocalOnePrimeMassTerm p by
    funext m
    simp [semilocalOnePrimeMassTerm, semilocalOnePrimePoissonWeight,
      semilocalOnePrimeLogFrequency, Equiv.funUnique_symm_apply]]
  rw [tsum_int_eq_zero_add_two_mul_tsum_pnat
    (semilocalOnePrimeMassTerm_even p)
    (summable_semilocalOnePrimeMassTerm hp)]
  have hzero : semilocalOnePrimeMassTerm p 0 = 1 := by
    simp [semilocalOnePrimeMassTerm, semilocalArchimedeanCharacteristic]
  rw [hzero]
  rw [show (∑' n : ℕ+, semilocalOnePrimeMassTerm p (n : ℕ)) =
      ∑' n : ℕ, semilocalOnePrimeMassTerm p (n + 1) by
    exact tsum_pnat_eq_tsum_succ
      (M := ℝ) (f := fun n : ℕ => semilocalOnePrimeMassTerm p n)]
  simp [semilocalOnePrimePositiveMassSeries]

theorem semilocalArchimedeanJacobiNormalization_two :
    semilocalArchimedeanJacobiNormalization 2 =
      Real.sqrt (3 / 2) / 2 := by
  have hpos : 0 ≤ semilocalArchimedeanJacobiNormalization 2 :=
    (semilocalArchimedeanJacobiNormalization_pos 2).le
  have hrhs : 0 ≤ Real.sqrt (3 / 2) / 2 := by positivity
  have hsq := semilocalArchimedeanJacobiNormalization_sq 2
  have hsqrt : Real.sqrt (3 / 2) ^ 2 = 3 / 2 := by
    rw [Real.sq_sqrt]
    norm_num
  norm_num at hsq
  nlinarith

theorem semilocalOnePrimeEvenJacobiMagnitudeTerm_one
    (p m : ℕ) :
    semilocalOnePrimeEvenJacobiMagnitudeTerm 1 p m =
      (Real.sqrt (3 / 2) / 2) *
        semilocalOnePrimeMomentDefectTerm p m := by
  unfold semilocalOnePrimeEvenJacobiMagnitudeTerm
    semilocalOnePrimeMomentDefectTerm
  rw [semilocalArchimedeanJacobiNormalization_two]
  ring

theorem semilocalOnePrimeEvenJacobiMagnitudeSeries_one
    (p : ℕ) :
    semilocalOnePrimeEvenJacobiMagnitudeSeries 1 p =
      (Real.sqrt (3 / 2) / 2) *
        semilocalOnePrimeMomentDefectNumerator p := by
  unfold semilocalOnePrimeEvenJacobiMagnitudeSeries
    semilocalOnePrimeMomentDefectNumerator
  rw [← tsum_mul_left]
  exact tsum_congr (semilocalOnePrimeEvenJacobiMagnitudeTerm_one p)

theorem semilocalOnePrimeMomentDefect_eq_series
    {p : ℕ} (hp : p.Prime) :
    semilocalOnePrimeMomentDefect p =
      (3 / 2) * semilocalOnePrimeMomentDefectNumerator p /
        (1 + 2 * semilocalOnePrimePositiveMassSeries p) := by
  have hinj : Function.Injective (semilocalOnePrimeFamily p) := by
    intro i j _
    exact Subsingleton.elim i j
  have hres :=
    (semilocalFinitePrimeActualGradingGroundDefect_one_eq_explicitResidue
      (semilocalOnePrimeFamily p) hinj (fun _ => hp)).1
  have hmom := semilocalFinitePrimeActualEvenJacobiMoment_eq_seriesMoment
    (k := 1) (by norm_num) (semilocalOnePrimeFamily p) (fun _ => hp)
  rw [semilocalFinitePrimeActualGradingGroundDefect, hmom,
    semilocalFinitePrimeEvenJacobiMoment,
    semilocalOnePrimeEvenJacobiNumerator_eq_two_mul_positiveSeries
      (by norm_num) hp,
    semilocalOnePrimePositiveEvenJacobiSeries_eq_signed_magnitudeSeries,
    semilocalOnePrimeEvenJacobiMagnitudeSeries_one,
    semilocalFinitePrimePoissonMass_onePrime hp] at hres
  have hsqrt : Real.sqrt (3 / 2) ≠ 0 := by positivity
  have hmass : 1 + 2 * semilocalOnePrimePositiveMassSeries p ≠ 0 := by
    rw [← semilocalFinitePrimePoissonMass_onePrime hp]
    exact (semilocalFinitePrimePoissonMass_pos
      (semilocalOnePrimeFamily p) (fun _ => hp)).ne'
  unfold semilocalOnePrimeMomentDefect
  norm_num at hres
  field_simp [hsqrt, hmass] at hres ⊢
  have hsqrtTwo : Real.sqrt 2 ^ 2 = 2 := by norm_num
  have hsqrtThree : Real.sqrt 3 ^ 2 = 3 := by norm_num
  rw [hsqrtTwo, hsqrtThree] at hres
  linarith

theorem semilocalOnePrimeMomentDefect_pos
    {p : ℕ} (hp : p.Prime) :
    0 < semilocalOnePrimeMomentDefect p := by
  unfold semilocalOnePrimeMomentDefect
  exact sub_pos.mpr (semilocalFinitePrimeNormalizedSecondMoment_lt_half
    (semilocalOnePrimeFamily p)
    (fun i j _ => (Fin.eq_zero i).trans (Fin.eq_zero j).symm) (fun _ => hp))

/-- Positive mixed-packet numerator retained when a finite Euler product is normalized globally. -/
def semilocalFinitePrimeJointMomentDefectNumerator
    {n : ℕ} (p : Fin (n + 1) → ℕ) : ℝ :=
  ∑' m : SemilocalNonzeroPrimePacket n,
    semilocalFinitePrimePoissonWeight p m.1 *
      semilocalArchimedeanCharacteristic
        (semilocalFinitePrimeLogFrequency p m.1) *
      Real.tanh (semilocalFinitePrimeLogFrequency p m.1) ^ 2

theorem summable_semilocalFinitePrimeJointMomentDefectTerm
    {n : ℕ} (p : Fin (n + 1) → ℕ) (hprime : ∀ i, (p i).Prime) :
    Summable fun m : SemilocalNonzeroPrimePacket n =>
      semilocalFinitePrimePoissonWeight p m.1 *
        semilocalArchimedeanCharacteristic
          (semilocalFinitePrimeLogFrequency p m.1) *
        Real.tanh (semilocalFinitePrimeLogFrequency p m.1) ^ 2 := by
  have hw := summable_semilocalNonzeroPrimePoissonWeight p hprime
  refine hw.of_norm_bounded ?_
  intro m
  rw [Real.norm_eq_abs, abs_mul, abs_mul,
    abs_of_pos (semilocalFinitePrimePoissonWeight_pos p hprime m.1),
    abs_of_pos (semilocalArchimedeanCharacteristic_pos _), abs_pow]
  have hchar0 : 0 ≤ semilocalArchimedeanCharacteristic
      (semilocalFinitePrimeLogFrequency p m.1) :=
    (semilocalArchimedeanCharacteristic_pos _).le
  have hchar1 : semilocalArchimedeanCharacteristic
      (semilocalFinitePrimeLogFrequency p m.1) ≤ 1 :=
    semilocalArchimedeanCharacteristic_le_one _
  have htanh0 : 0 ≤ |Real.tanh
      (semilocalFinitePrimeLogFrequency p m.1)| ^ 2 := sq_nonneg _
  have htanh1 : |Real.tanh
      (semilocalFinitePrimeLogFrequency p m.1)| ^ 2 ≤ 1 :=
    pow_le_one₀ (abs_nonneg _) (Real.abs_tanh_lt_one _).le
  have hw0 := (semilocalFinitePrimePoissonWeight_pos p hprime m.1).le
  calc
    semilocalFinitePrimePoissonWeight p m.1 *
          semilocalArchimedeanCharacteristic
            (semilocalFinitePrimeLogFrequency p m.1) *
          |Real.tanh (semilocalFinitePrimeLogFrequency p m.1)| ^ 2 ≤
        semilocalFinitePrimePoissonWeight p m.1 * 1 * 1 := by
      calc
        semilocalFinitePrimePoissonWeight p m.1 *
              semilocalArchimedeanCharacteristic
                (semilocalFinitePrimeLogFrequency p m.1) *
              |Real.tanh (semilocalFinitePrimeLogFrequency p m.1)| ^ 2 ≤
            semilocalFinitePrimePoissonWeight p m.1 * 1 *
              |Real.tanh (semilocalFinitePrimeLogFrequency p m.1)| ^ 2 :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hchar1 hw0) htanh0
        _ ≤ semilocalFinitePrimePoissonWeight p m.1 * 1 * 1 :=
          mul_le_mul_of_nonneg_left htanh1 (mul_nonneg hw0 (by norm_num))
    _ = semilocalFinitePrimePoissonWeight p m.1 := by ring

theorem semilocalFinitePrimeJointMomentDefectNumerator_pos
    {n : ℕ} (p : Fin (n + 1) → ℕ) (hp : Function.Injective p)
    (hprime : ∀ i, (p i).Prime) :
    0 < semilocalFinitePrimeJointMomentDefectNumerator p := by
  let m₀ := semilocalUnitPrimePacket n
  have hterm (m : SemilocalNonzeroPrimePacket n) :
      0 < semilocalFinitePrimePoissonWeight p m.1 *
        semilocalArchimedeanCharacteristic
          (semilocalFinitePrimeLogFrequency p m.1) *
        Real.tanh (semilocalFinitePrimeLogFrequency p m.1) ^ 2 := by
    have hfreq := semilocalNonzeroPrimeLogFrequency_ne_zero p hp hprime m
    have htanh : Real.tanh (semilocalFinitePrimeLogFrequency p m.1) ≠ 0 := by
      rw [Real.tanh_eq_sinh_div_cosh]
      exact div_ne_zero
        (by simpa using Real.sinh_strictMono.injective.ne hfreq)
        (Real.cosh_pos _).ne'
    exact mul_pos
      (mul_pos (semilocalFinitePrimePoissonWeight_pos p hprime m.1)
        (semilocalArchimedeanCharacteristic_pos _))
      (sq_pos_of_ne_zero htanh)
  have hs := summable_semilocalFinitePrimeJointMomentDefectTerm p hprime
  exact (hterm m₀).trans_le (by
    unfold semilocalFinitePrimeJointMomentDefectNumerator
    exact hs.le_tsum m₀ (fun m _ => (hterm m).le))

theorem semilocalFinitePrimeEvenJacobiNumerator_one_eq_jointDefect
    {n : ℕ} (p : Fin (n + 1) → ℕ) :
    semilocalFinitePrimeEvenJacobiNumerator 1 p =
      -(Real.sqrt (3 / 2) / 2) *
        semilocalFinitePrimeJointMomentDefectNumerator p := by
  unfold semilocalFinitePrimeEvenJacobiNumerator
    semilocalFinitePrimeJointMomentDefectNumerator
  rw [← tsum_mul_left]
  apply tsum_congr
  intro m
  unfold semilocalArchimedeanEvenJacobiKernel
  rw [semilocalArchimedeanJacobiNormalization_two]
  norm_num
  ring

theorem semilocalFinitePrimeMomentDefect_eq_jointSeries
    {n : ℕ} (p : Fin (n + 1) → ℕ) (hp : Function.Injective p)
    (hprime : ∀ i, (p i).Prime) :
    1 / 2 - semilocalFinitePrimeNormalizedSecondMoment p =
      (3 / 4) * semilocalFinitePrimeJointMomentDefectNumerator p /
        semilocalFinitePrimePoissonMass p := by
  have hres :=
    (semilocalFinitePrimeActualGradingGroundDefect_one_eq_explicitResidue
      p hp hprime).1
  have hmom := semilocalFinitePrimeActualEvenJacobiMoment_eq_seriesMoment
    (k := 1) (by norm_num) p hprime
  rw [semilocalFinitePrimeActualGradingGroundDefect, hmom,
    semilocalFinitePrimeEvenJacobiMoment,
    semilocalFinitePrimeEvenJacobiNumerator_one_eq_jointDefect] at hres
  have hsqrt : Real.sqrt (3 / 2) ≠ 0 := by positivity
  have hmass := (semilocalFinitePrimePoissonMass_pos p hprime).ne'
  norm_num at hres
  field_simp [hsqrt, hmass] at hres ⊢
  have hsqrtTwo : Real.sqrt 2 ^ 2 = 2 := by norm_num
  have hsqrtThree : Real.sqrt 3 ^ 2 = 3 := by norm_num
  rw [hsqrtTwo, hsqrtThree] at hres
  linarith

theorem semilocalFinitePrimeMomentDefect_eq_jointSeries_pos
    {n : ℕ} (p : Fin (n + 1) → ℕ) (hp : Function.Injective p)
    (hprime : ∀ i, (p i).Prime) :
    1 / 2 - semilocalFinitePrimeNormalizedSecondMoment p =
        (3 / 4) * semilocalFinitePrimeJointMomentDefectNumerator p /
          semilocalFinitePrimePoissonMass p ∧
      0 < 1 / 2 - semilocalFinitePrimeNormalizedSecondMoment p := by
  exact ⟨semilocalFinitePrimeMomentDefect_eq_jointSeries p hp hprime,
    sub_pos.mpr (semilocalFinitePrimeNormalizedSecondMoment_lt_half p hp hprime)⟩

/-- A negative unit-vector coefficient forces at least the same trace-norm mass in any correction
to a positive innovation. -/
theorem two_mul_semilocalOnePrimeMomentDefect_le_traceNorm
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    {p : ℕ} (hp : p.Prime) {e : H} (he : ‖e‖ = 1)
    {Δ I R : H →L[ℂ] H}
    (hquad : (inner ℂ e (Δ e)).re = -2 * semilocalOnePrimeMomentDefect p)
    (hsplit : Δ = I + R) (hI : I.IsPositive)
    (hR : MemSchattenClass 1 R) :
    2 * semilocalOnePrimeMomentDefect p ≤ traceNorm H R := by
  have hIquad : 0 ≤ (inner ℂ e (I e)).re := hI.re_inner_nonneg_right e
  have hRquad : (inner ℂ e (R e)).re ≤
      -2 * semilocalOnePrimeMomentDefect p := by
    rw [hsplit, add_apply, inner_add_right, Complex.add_re] at hquad
    linarith
  have hRnonpos : (inner ℂ e (R e)).re ≤ 0 :=
    hRquad.trans (by linarith [semilocalOnePrimeMomentDefect_pos hp])
  calc
    2 * semilocalOnePrimeMomentDefect p ≤
        |(inner ℂ e (R e)).re| := by
      rw [abs_of_nonpos hRnonpos]
      linarith
    _ ≤ ‖inner ℂ e (R e)‖ := Complex.abs_re_le_norm _
    _ ≤ ‖e‖ * ‖R e‖ := norm_inner_le_norm _ _
    _ = ‖R e‖ := by rw [he, one_mul]
    _ ≤ ‖R‖ * ‖e‖ := R.le_opNorm e
    _ = ‖R‖ := by rw [he, mul_one]
    _ ≤ traceNorm H R := by
      apply norm_le_traceNorm
      unfold MemSchattenClass at hR
      exact hR.congr fun n => Real.rpow_one (approxNumber R n)

theorem tsum_two_mul_prime_inv_pow_add_eq
    {p M : ℕ} (hp : 1 < p) :
    (∑' j : ℕ, 2 * ((p : ℝ) ^ (M + j + 1))⁻¹) =
      2 * ((p : ℝ) ^ M)⁻¹ *
        ((p : ℝ)⁻¹ * (1 - (p : ℝ)⁻¹)⁻¹) := by
  let q : ℝ := (p : ℝ)⁻¹
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.trans' Nat.zero_lt_one
  have hq0 : 0 ≤ q := by dsimp [q]; positivity
  have hq1 : q < 1 := by
    dsimp [q]
    exact inv_lt_one_of_one_lt₀ (by exact_mod_cast hp)
  have hs : Summable (fun j : ℕ => q ^ j) :=
    summable_geometric_of_norm_lt_one (by simpa [abs_of_nonneg hq0] using hq1)
  calc
    (∑' j : ℕ, 2 * ((p : ℝ) ^ (M + j + 1))⁻¹) =
        2 * ((p : ℝ) ^ M)⁻¹ * (∑' j : ℕ, q ^ (j + 1)) := by
      rw [← tsum_mul_left]
      apply tsum_congr
      intro j
      dsimp [q]
      rw [inv_pow]
      ring_nf
    _ = 2 * ((p : ℝ) ^ M)⁻¹ *
          (q * (1 - q)⁻¹) := by
      rw [show (∑' j : ℕ, q ^ (j + 1)) = q * (∑' j : ℕ, q ^ j) by
        rw [← hs.tsum_mul_left]
        apply tsum_congr
        intro j
        rw [pow_succ']]
      rw [tsum_geometric_of_lt_one hq0 hq1]
    _ = _ := rfl

theorem tsum_two_mul_prime_inv_pow_add_le_four
    {p M : ℕ} (hp : p.Prime) :
    (∑' j : ℕ, 2 * ((p : ℝ) ^ (M + j + 1))⁻¹) ≤
      4 * ((p : ℝ) ^ (M + 1))⁻¹ := by
  rw [tsum_two_mul_prime_inv_pow_add_eq hp.one_lt]
  let q : ℝ := (p : ℝ)⁻¹
  have hpR : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hq0 : 0 ≤ q := by dsimp [q]; positivity
  have hqhalf : q ≤ 1 / 2 := by
    dsimp [q]
    simpa [one_div] using
      (inv_le_inv₀ hp0 (by norm_num : (0 : ℝ) < 2)).2 hpR
  have hden : 0 < 1 - q := sub_pos.mpr (hqhalf.trans_lt (by norm_num))
  have hinv : (1 - q)⁻¹ ≤ 2 := by
    rw [inv_eq_one_div, div_le_iff₀ hden]
    linarith
  have hratio : q * (1 - q)⁻¹ ≤ 2 * q :=
    by simpa [mul_comm] using mul_le_mul_of_nonneg_left hinv hq0
  have hpow0 : 0 ≤ ((p : ℝ) ^ M)⁻¹ := by positivity
  calc
    2 * ((p : ℝ) ^ M)⁻¹ * (q * (1 - q)⁻¹) ≤
        2 * ((p : ℝ) ^ M)⁻¹ * (2 * q) :=
      mul_le_mul_of_nonneg_left hratio (mul_nonneg (by norm_num) hpow0)
    _ = 4 * ((p : ℝ) ^ (M + 1))⁻¹ := by
      dsimp [q]
      rw [pow_succ, mul_inv]
      ring

theorem semilocalOnePrimeMomentDefectTerm_pos
    {p : ℕ} (hp : p.Prime) (m : ℕ) :
    0 < semilocalOnePrimeMomentDefectTerm p m := by
  unfold semilocalOnePrimeMomentDefectTerm
  have hfreq : (((m + 1 : ℕ) : ℝ) * Real.log p) ≠ 0 := by
    exact mul_ne_zero (by positivity)
      (Real.log_pos (by exact_mod_cast hp.one_lt)).ne'
  have htanh : Real.tanh (((m + 1 : ℕ) : ℝ) * Real.log p) ≠ 0 := by
    rw [Real.tanh_eq_sinh_div_cosh]
    exact div_ne_zero
      (by simpa using Real.sinh_strictMono.injective.ne hfreq)
      (Real.cosh_pos _).ne'
  exact mul_pos
    (mul_pos (pow_pos (semilocalPrimePoissonRatio_pos hp) _)
      (semilocalArchimedeanCharacteristic_pos _))
    (sq_pos_of_ne_zero htanh)

theorem summable_semilocalOnePrimeMomentDefectTerm
    {p : ℕ} (hp : p.Prime) :
    Summable (semilocalOnePrimeMomentDefectTerm p) := by
  have hs := summable_semilocalOnePrimeEvenJacobiMagnitudeTerm (k := 1) hp
  have hc : Real.sqrt (3 / 2) / 2 ≠ 0 := by positivity
  have hscaled := hs.mul_left (Real.sqrt (3 / 2) / 2)⁻¹
  apply hscaled.congr
  intro m
  rw [semilocalOnePrimeEvenJacobiMagnitudeTerm_one]
  field_simp [hc]

theorem semilocalOnePrimeMomentDefectNumerator_split
    {p : ℕ} (hp : p.Prime) :
    semilocalOnePrimeMomentDefectNumerator p =
      semilocalOnePrimeMomentDefectTerm p 0 +
        ∑' j : ℕ, semilocalOnePrimeMomentDefectTerm p (j + 1) := by
  unfold semilocalOnePrimeMomentDefectNumerator
  simpa using
    (summable_semilocalOnePrimeMomentDefectTerm hp).sum_add_tsum_nat_add 1 |>.symm

theorem semilocalOnePrimeMomentDefectTerm_le_tail
    {p : ℕ} (hp : p.Prime) (m : ℕ) :
    semilocalOnePrimeMomentDefectTerm p m ≤
      2 * ((p : ℝ) ^ (m + 1))⁻¹ := by
  exact semilocalOnePrimeRawMagnitude_le_tail (k := 1) hp

theorem semilocalOnePrimeMomentDefectTail_le
    {p : ℕ} (hp : p.Prime) :
    (∑' j : ℕ, semilocalOnePrimeMomentDefectTerm p (j + 1)) ≤
      4 * ((p : ℝ) ^ 2)⁻¹ := by
  have hleft : Summable fun j : ℕ =>
      semilocalOnePrimeMomentDefectTerm p (j + 1) :=
    (summable_nat_add_iff 1).2 (summable_semilocalOnePrimeMomentDefectTerm hp)
  have hright := summable_two_mul_prime_inv_pow_add (M := 1) hp.one_lt
  calc
    (∑' j : ℕ, semilocalOnePrimeMomentDefectTerm p (j + 1)) ≤
        ∑' j : ℕ, 2 * ((p : ℝ) ^ (1 + j + 1))⁻¹ := by
      exact Summable.tsum_le_tsum (fun j => by
        simpa [add_assoc, add_comm, add_left_comm] using
          semilocalOnePrimeMomentDefectTerm_le_tail hp (j + 1))
        hleft hright
    _ ≤ 4 * ((p : ℝ) ^ (1 + 1))⁻¹ :=
      tsum_two_mul_prime_inv_pow_add_le_four hp
    _ = 4 * ((p : ℝ) ^ 2)⁻¹ := by norm_num

def semilocalOnePrimeMomentMainTerm (p : ℕ) : ℝ :=
  Real.sqrt 2 / (p : ℝ)

def semilocalOnePrimePoissonCharacteristicFirst (p : ℕ) : ℝ :=
  semilocalPrimePoissonRatio p *
    semilocalArchimedeanCharacteristic (Real.log p)

theorem semilocalOnePrimePoissonCharacteristicFirst_sq
    {p : ℕ} (hp : p.Prime) :
    semilocalOnePrimePoissonCharacteristicFirst p ^ 2 =
      2 / ((p : ℝ) ^ 2 + 1) := by
  simpa [semilocalOnePrimePoissonCharacteristicFirst] using
    semilocalPrimePoissonCharacteristicProduct_sq hp 1

theorem semilocalOnePrimePoissonCharacteristicFirst_nonneg
    {p : ℕ} (hp : p.Prime) :
    0 ≤ semilocalOnePrimePoissonCharacteristicFirst p := by
  exact mul_nonneg (semilocalPrimePoissonRatio_pos hp).le
    (semilocalArchimedeanCharacteristic_pos _).le

theorem semilocalOnePrimePoissonCharacteristicFirst_le_main
    {p : ℕ} (hp : p.Prime) :
    semilocalOnePrimePoissonCharacteristicFirst p ≤
      semilocalOnePrimeMomentMainTerm p := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hb0 := semilocalOnePrimePoissonCharacteristicFirst_nonneg hp
  have ha0 : 0 ≤ semilocalOnePrimeMomentMainTerm p := by
    unfold semilocalOnePrimeMomentMainTerm
    positivity
  apply (sq_le_sq₀ hb0 ha0).mp
  rw [semilocalOnePrimePoissonCharacteristicFirst_sq hp]
  unfold semilocalOnePrimeMomentMainTerm
  rw [div_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  have hden : 0 < (p : ℝ) ^ 2 + 1 := by positivity
  rw [div_le_div_iff₀ hden (sq_pos_of_pos hp0)]
  nlinarith

theorem main_sub_inv_sq_le_semilocalOnePrimePoissonCharacteristicFirst
    {p : ℕ} (hp : p.Prime) :
    semilocalOnePrimeMomentMainTerm p - ((p : ℝ) ^ 2)⁻¹ ≤
      semilocalOnePrimePoissonCharacteristicFirst p := by
  let x : ℝ := p
  let a : ℝ := semilocalOnePrimeMomentMainTerm p
  let b : ℝ := semilocalOnePrimePoissonCharacteristicFirst p
  have hx : 2 ≤ x := by
    dsimp [x]
    exact_mod_cast hp.two_le
  have hx0 : 0 < x := by linarith
  have hsqrt1 : 1 ≤ Real.sqrt 2 := by
    nlinarith [Real.sq_sqrt (show 0 ≤ (2 : ℝ) by norm_num), Real.sqrt_nonneg 2]
  have ha : a = Real.sqrt 2 / x := rfl
  have hb0 : 0 ≤ b := semilocalOnePrimePoissonCharacteristicFirst_nonneg hp
  have hleft0 : 0 ≤ a - (x ^ 2)⁻¹ := by
    rw [ha]
    have hxinv : (x ^ 2)⁻¹ ≤ x⁻¹ := by
      rw [inv_le_inv₀ (by positivity : 0 < x ^ 2) hx0]
      nlinarith [sq_nonneg (x - 1)]
    have hsqrt : x⁻¹ ≤ Real.sqrt 2 / x := by
      rw [div_eq_mul_inv]
      simpa only [one_mul] using
        mul_le_mul_of_nonneg_right hsqrt1 (inv_nonneg.mpr hx0.le)
    linarith
  apply (sq_le_sq₀ hleft0 hb0).mp
  have hb2 := semilocalOnePrimePoissonCharacteristicFirst_sq hp
  change b ^ 2 = 2 / (x ^ 2 + 1) at hb2
  change (a - (x ^ 2)⁻¹) ^ 2 ≤ b ^ 2
  rw [hb2, ha]
  have hden : 0 < x ^ 2 + 1 := by positivity
  have hx4 : 0 < x ^ 4 := by positivity
  rw [show (Real.sqrt 2 / x - (x ^ 2)⁻¹) =
      (Real.sqrt 2 * x - 1) / x ^ 2 by field_simp]
  rw [div_pow, show (x ^ 2) ^ 2 = x ^ 4 by ring]
  rw [div_le_div_iff₀ hx4 hden]
  have hsqrt2 : Real.sqrt 2 ^ 2 = 2 := by norm_num
  have hcube0 : 0 ≤ x ^ 3 := by positivity
  have hscube : x ^ 3 ≤ Real.sqrt 2 * x ^ 3 :=
    by simpa only [one_mul] using mul_le_mul_of_nonneg_right hsqrt1 hcube0
  nlinarith [sq_nonneg (x - 2), sq_nonneg x]

theorem one_sub_tanh_log_prime_sq_le_four_div_sq
    {p : ℕ} (hp : p.Prime) :
    1 - Real.tanh (Real.log p) ^ 2 ≤ 4 / (p : ℝ) ^ 2 := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have ht := tanh_nat_mul_log_prime hp 1
  norm_num at ht
  rw [ht]
  have hden : 0 < (p : ℝ) ^ 2 + 1 := by positivity
  rw [show 1 - (((p : ℝ) ^ 2 - 1) / ((p : ℝ) ^ 2 + 1)) ^ 2 =
      4 * (p : ℝ) ^ 2 / (((p : ℝ) ^ 2 + 1) ^ 2) by
    field_simp
    ring]
  rw [div_le_div_iff₀ (sq_pos_of_pos hden) (sq_pos_of_pos hp0)]
  nlinarith [sq_nonneg (p : ℝ)]

theorem semilocalOnePrimeMomentDefectTerm_zero_eq
    (p : ℕ) :
    semilocalOnePrimeMomentDefectTerm p 0 =
      semilocalOnePrimePoissonCharacteristicFirst p *
        Real.tanh (Real.log p) ^ 2 := by
  simp [semilocalOnePrimeMomentDefectTerm,
    semilocalOnePrimePoissonCharacteristicFirst]

theorem semilocalOnePrimeMomentDefectTerm_zero_le_main
    {p : ℕ} (hp : p.Prime) :
    semilocalOnePrimeMomentDefectTerm p 0 ≤
      semilocalOnePrimeMomentMainTerm p := by
  rw [semilocalOnePrimeMomentDefectTerm_zero_eq]
  have hb0 := semilocalOnePrimePoissonCharacteristicFirst_nonneg hp
  have ht0 : 0 ≤ Real.tanh (Real.log p) ^ 2 := sq_nonneg _
  have ht1 : Real.tanh (Real.log p) ^ 2 ≤ 1 := by
    exact (Real.tanh_sq_lt_one (Real.log p)).le
  exact (mul_le_of_le_one_right hb0 ht1).trans
    (semilocalOnePrimePoissonCharacteristicFirst_le_main hp)

theorem main_sub_semilocalOnePrimeMomentDefectTerm_zero_le
    {p : ℕ} (hp : p.Prime) :
    semilocalOnePrimeMomentMainTerm p -
        semilocalOnePrimeMomentDefectTerm p 0 ≤
      5 * ((p : ℝ) ^ 2)⁻¹ := by
  let x : ℝ := p
  let a := semilocalOnePrimeMomentMainTerm p
  let b := semilocalOnePrimePoissonCharacteristicFirst p
  let t := Real.tanh (Real.log p)
  have hx : 2 ≤ x := by
    dsimp [x]
    exact_mod_cast hp.two_le
  have hx0 : 0 < x := by linarith
  have hab : a - (x ^ 2)⁻¹ ≤ b :=
    main_sub_inv_sq_le_semilocalOnePrimePoissonCharacteristicFirst hp
  have hba : b ≤ a := semilocalOnePrimePoissonCharacteristicFirst_le_main hp
  have ha2 : a ≤ 2 / x := by
    have hsqrt2sq := Real.sq_sqrt (show 0 ≤ (2 : ℝ) by norm_num)
    have hsqrt2nonneg := Real.sqrt_nonneg 2
    have hsqrt2 : Real.sqrt 2 ≤ 2 := by nlinarith
    simpa [a, x, semilocalOnePrimeMomentMainTerm] using
      div_le_div_of_nonneg_right hsqrt2 hx0.le
  have ht : 1 - t ^ 2 ≤ 4 / x ^ 2 :=
    by simpa [t, x] using one_sub_tanh_log_prime_sq_le_four_div_sq hp
  have ht0 : 0 ≤ 1 - t ^ 2 := by
    dsimp [t]
    exact sub_nonneg.mpr (Real.tanh_sq_lt_one (Real.log p)).le
  have hb0 : 0 ≤ b := semilocalOnePrimePoissonCharacteristicFirst_nonneg hp
  have hprod : b * (1 - t ^ 2) ≤ 8 / x ^ 3 := by
    calc
      b * (1 - t ^ 2) ≤ (2 / x) * (1 - t ^ 2) :=
        mul_le_mul_of_nonneg_right (hba.trans ha2) ht0
      _ ≤ (2 / x) * (4 / x ^ 2) :=
        mul_le_mul_of_nonneg_left ht (by positivity)
      _ = 8 / x ^ 3 := by field_simp; ring
  have hcube : 8 / x ^ 3 ≤ 4 / x ^ 2 := by
    rw [div_le_div_iff₀ (by positivity : 0 < x ^ 3)
      (by positivity : 0 < x ^ 2)]
    nlinarith
  rw [semilocalOnePrimeMomentDefectTerm_zero_eq]
  change a - b * t ^ 2 ≤ _
  calc
    a - b * t ^ 2 = (a - b) + b * (1 - t ^ 2) := by ring
    _ ≤ (x ^ 2)⁻¹ + 4 / x ^ 2 :=
      add_le_add (by linarith) (hprod.trans hcube)
    _ = 5 * (x ^ 2)⁻¹ := by field_simp; ring

theorem abs_semilocalOnePrimeMomentDefectNumerator_sub_main_le
    {p : ℕ} (hp : p.Prime) :
    |semilocalOnePrimeMomentDefectNumerator p -
        semilocalOnePrimeMomentMainTerm p| ≤
      5 * ((p : ℝ) ^ 2)⁻¹ := by
  let a := semilocalOnePrimeMomentMainTerm p
  let u := semilocalOnePrimeMomentDefectTerm p 0
  let v := ∑' j : ℕ, semilocalOnePrimeMomentDefectTerm p (j + 1)
  have hsplit := semilocalOnePrimeMomentDefectNumerator_split hp
  change semilocalOnePrimeMomentDefectNumerator p = u + v at hsplit
  have hu : u ≤ a := semilocalOnePrimeMomentDefectTerm_zero_le_main hp
  have hau : a - u ≤ 5 * ((p : ℝ) ^ 2)⁻¹ :=
    main_sub_semilocalOnePrimeMomentDefectTerm_zero_le hp
  have hv0 : 0 ≤ v := by
    exact tsum_nonneg fun j => (semilocalOnePrimeMomentDefectTerm_pos hp (j + 1)).le
  have hv : v ≤ 4 * ((p : ℝ) ^ 2)⁻¹ :=
    semilocalOnePrimeMomentDefectTail_le hp
  have hinv0 : 0 ≤ ((p : ℝ) ^ 2)⁻¹ := by positivity
  rw [hsplit]
  apply abs_le.mpr
  constructor
  · linarith
  · nlinarith

theorem semilocalOnePrimePositiveMassSeries_nonneg
    {p : ℕ} (hp : p.Prime) :
    0 ≤ semilocalOnePrimePositiveMassSeries p := by
  unfold semilocalOnePrimePositiveMassSeries
  exact tsum_nonneg fun m => mul_nonneg
    (pow_nonneg (semilocalPrimePoissonRatio_pos hp).le _)
    (semilocalArchimedeanCharacteristic_pos _).le

theorem semilocalOnePrimePositiveMassSeries_le
    {p : ℕ} (hp : p.Prime) :
    semilocalOnePrimePositiveMassSeries p ≤ 4 * (p : ℝ)⁻¹ := by
  have hleft : Summable fun m : ℕ =>
      semilocalOnePrimeMassTerm p ((m : ℤ) + 1) := by
    exact (summable_semilocalOnePrimeMassTerm hp).comp_injective
      (show Function.Injective (fun m : ℕ => (m : ℤ) + 1) by
        intro m n h
        exact_mod_cast add_right_cancel h)
  have hright := summable_two_mul_prime_inv_pow_add (M := 0) hp.one_lt
  unfold semilocalOnePrimePositiveMassSeries
  calc
    (∑' m : ℕ, semilocalOnePrimeMassTerm p ((m : ℤ) + 1)) ≤
        ∑' m : ℕ, 2 * ((p : ℝ) ^ (0 + m + 1))⁻¹ := by
      exact Summable.tsum_le_tsum (fun m => by
        unfold semilocalOnePrimeMassTerm
        have habs : ((m : ℤ) + 1).natAbs = m + 1 := by omega
        rw [habs]
        push_cast
        simpa using semilocalPrimePoissonCharacteristicProduct_upper hp (m + 1))
        hleft hright
    _ ≤ 4 * ((p : ℝ) ^ (0 + 1))⁻¹ :=
      tsum_two_mul_prime_inv_pow_add_le_four hp
    _ = 4 * (p : ℝ)⁻¹ := by norm_num

theorem abs_semilocalOnePrimeMomentDefect_sub_asymptoticMain_le
    {p : ℕ} (hp : p.Prime) :
    |semilocalOnePrimeMomentDefect p -
        3 * Real.sqrt 2 / (2 * p)| ≤
      42 * ((p : ℝ) ^ 2)⁻¹ := by
  let x : ℝ := p
  let a := semilocalOnePrimeMomentMainTerm p
  let N := semilocalOnePrimeMomentDefectNumerator p
  let S := semilocalOnePrimePositiveMassSeries p
  let D := 1 + 2 * S
  have hx : 2 ≤ x := by
    dsimp [x]
    exact_mod_cast hp.two_le
  have hx0 : 0 < x := by linarith
  have hN : |N - a| ≤ 5 * (x ^ 2)⁻¹ := by
    simpa [N, a, x] using abs_semilocalOnePrimeMomentDefectNumerator_sub_main_le hp
  have hS0 : 0 ≤ S := semilocalOnePrimePositiveMassSeries_nonneg hp
  have hS : S ≤ 4 * x⁻¹ := by
    simpa [S, x] using semilocalOnePrimePositiveMassSeries_le hp
  have hD1 : 1 ≤ D := by dsimp [D]; linarith
  have hD0 : 0 < D := zero_lt_one.trans_le hD1
  have hDm1 : D - 1 ≤ 8 * x⁻¹ := by dsimp [D]; linarith
  have hDm10 : 0 ≤ D - 1 := by linarith
  have ha0 : 0 ≤ a := by
    dsimp [a, semilocalOnePrimeMomentMainTerm]
    positivity
  have ha2 : a ≤ 2 * x⁻¹ := by
    have hsqrt2sq := Real.sq_sqrt (show 0 ≤ (2 : ℝ) by norm_num)
    have hsqrt2nonneg := Real.sqrt_nonneg 2
    have hsqrt2 : Real.sqrt 2 ≤ 2 := by nlinarith
    dsimp [a, semilocalOnePrimeMomentMainTerm, x]
    rw [div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_right hsqrt2 (inv_nonneg.mpr hx0.le)
  have had : a * (D - 1) ≤ 16 * (x ^ 2)⁻¹ := by
    calc
      a * (D - 1) ≤ (2 * x⁻¹) * (8 * x⁻¹) :=
        le_trans (mul_le_mul_of_nonneg_right ha2 hDm10)
          (mul_le_mul_of_nonneg_left hDm1 (by positivity))
      _ = 16 * (x ^ 2)⁻¹ := by
        rw [show (x ^ 2)⁻¹ = x⁻¹ ^ 2 by rw [inv_pow]]
        ring
  have hquot : |N / D - a| ≤ 21 * (x ^ 2)⁻¹ := by
    have hre : N / D - a = ((N - a) - a * (D - 1)) / D := by
      field_simp [hD0.ne']
      ring
    rw [hre, abs_div, abs_of_pos hD0]
    have hnum : |(N - a) - a * (D - 1)| ≤
        |N - a| + a * (D - 1) := by
      calc
        |(N - a) - a * (D - 1)| ≤ |N - a| + |a * (D - 1)| :=
          abs_sub _ _
        _ = |N - a| + a * (D - 1) := by
          rw [abs_of_nonneg (mul_nonneg ha0 hDm10)]
    have hnum' : |(N - a) - a * (D - 1)| ≤ 21 * (x ^ 2)⁻¹ :=
      hnum.trans (by linarith)
    exact (div_le_self (abs_nonneg _) hD1).trans hnum'
  rw [semilocalOnePrimeMomentDefect_eq_series hp]
  change |(3 / 2) * N / D - 3 * Real.sqrt 2 / (2 * p)| ≤ _
  have hmain : 3 * Real.sqrt 2 / (2 * (p : ℝ)) = (3 / 2) * a := by
    dsimp [a, semilocalOnePrimeMomentMainTerm]
    field_simp
  rw [hmain, show (3 / 2) * N / D = (3 / 2) * (N / D) by ring,
    ← mul_sub, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 3 / 2)]
  calc
    3 / 2 * |N / D - a| ≤ 3 / 2 * (21 * (x ^ 2)⁻¹) :=
      mul_le_mul_of_nonneg_left hquot (by norm_num)
    _ ≤ 42 * (x ^ 2)⁻¹ := by
      have hinv : 0 ≤ (x ^ 2)⁻¹ := inv_nonneg.mpr (sq_nonneg x)
      nlinarith

open Asymptotics in
theorem semilocalOnePrimeMomentDefect_asymptotic :
    (fun p : Nat.Primes =>
      semilocalOnePrimeMomentDefect p -
        3 * Real.sqrt 2 / (2 * (p : ℝ))) =O[cofinite]
      (fun p : Nat.Primes => ((p : ℝ) ^ 2)⁻¹) := by
  apply IsBigO.of_bound 42
  filter_upwards with p
  rw [Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_nonneg (inv_nonneg.mpr (sq_nonneg (p : ℝ)))]
  exact abs_semilocalOnePrimeMomentDefect_sub_asymptoticMain_le p.property

theorem one_div_prime_le_semilocalOnePrimeMomentDefect_of_large
    (p : Nat.Primes) (hp : 84 ≤ (p : ℕ)) :
    (1 : ℝ) / (p : ℝ) ≤ semilocalOnePrimeMomentDefect p := by
  let x : ℝ := (p : ℕ)
  have herror := abs_semilocalOnePrimeMomentDefect_sub_asymptoticMain_le p.property
  have hpR : (84 : ℝ) ≤ x := by
    dsimp [x]
    exact_mod_cast hp
  have hp0 : (0 : ℝ) < x := by linarith
  have hsqrt1 : 1 ≤ Real.sqrt 2 := by
    nlinarith [Real.sq_sqrt (show 0 ≤ (2 : ℝ) by norm_num), Real.sqrt_nonneg 2]
  have hmain : (3 / 2 : ℝ) / x ≤ 3 * Real.sqrt 2 / (2 * x) := by
    have heq : 3 * Real.sqrt 2 / (2 * x) =
        ((3 / 2) * Real.sqrt 2) / x := by field_simp
    rw [heq, div_le_div_iff_of_pos_right hp0]
    nlinarith
  have herr : 42 * (x ^ 2)⁻¹ ≤ (1 / 2 : ℝ) / x := by
    rw [show (x ^ 2)⁻¹ = x⁻¹ ^ 2 by rw [inv_pow]]
    field_simp
    nlinarith
  have herror' : |semilocalOnePrimeMomentDefect p -
      3 * Real.sqrt 2 / (2 * x)| ≤ 42 * (x ^ 2)⁻¹ := by
    simpa [x] using herror
  have hlower : 3 * Real.sqrt 2 / (2 * x) -
      42 * (x ^ 2)⁻¹ ≤ semilocalOnePrimeMomentDefect p := by
    have habs := (abs_le.mp herror').1
    linarith
  change (1 : ℝ) / x ≤ semilocalOnePrimeMomentDefect p
  calc
    (1 : ℝ) / x = (3 / 2 : ℝ) / x - (1 / 2 : ℝ) / x := by
      field_simp
      norm_num
    _ ≤ 3 * Real.sqrt 2 / (2 * x) - 42 * (x ^ 2)⁻¹ :=
      sub_le_sub hmain herr
    _ ≤ semilocalOnePrimeMomentDefect p := hlower

theorem not_summable_semilocalOnePrimeMomentDefect :
    ¬ Summable (fun p : Nat.Primes => semilocalOnePrimeMomentDefect p) := by
  intro hsum
  have hfinite : {p : Nat.Primes | (p : ℕ) < 84}.Finite :=
    (Set.finite_Iio 84).preimage Subtype.val_injective.injOn
  have hevent : ∀ᶠ p : Nat.Primes in cofinite,
      ‖(1 / p : ℝ)‖ ≤ semilocalOnePrimeMomentDefect p := by
    filter_upwards [hfinite.compl_mem_cofinite] with p hp
    rw [Set.mem_compl_iff, Set.mem_setOf_eq, not_lt] at hp
    rw [Real.norm_eq_abs, abs_of_pos (by positivity : (0 : ℝ) < 1 / p)]
    exact one_div_prime_le_semilocalOnePrimeMomentDefect_of_large p hp
  have hprimeHarmonic : Summable (fun p : Nat.Primes => (1 / p : ℝ)) :=
    hsum.of_norm_bounded_eventually hevent
  exact Nat.Primes.not_summable_one_div hprimeHarmonic

/-- Independent one-prime positive innovations cannot have a summable family of trace-class
corrections.  This is the family-level form of the channelwise trace-class obstruction. -/
theorem not_summable_traceNorm_semilocalOnePrimeCorrection
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (e : H) (he : ‖e‖ = 1)
    (Δ I R : Nat.Primes → H →L[ℂ] H)
    (hquad : ∀ p, (inner ℂ e (Δ p e)).re =
      -2 * semilocalOnePrimeMomentDefect p)
    (hsplit : ∀ p, Δ p = I p + R p)
    (hI : ∀ p, (I p).IsPositive)
    (hR : ∀ p, MemSchattenClass 1 (R p)) :
    ¬ Summable (fun p : Nat.Primes => traceNorm H (R p)) := by
  intro htrace
  apply not_summable_semilocalOnePrimeMomentDefect
  apply htrace.of_norm_bounded
  intro p
  rw [Real.norm_eq_abs, abs_of_pos (semilocalOnePrimeMomentDefect_pos p.property)]
  have hbound := two_mul_semilocalOnePrimeMomentDefect_le_traceNorm
    p.property he (hquad p) (hsplit p) (hI p) (hR p)
  have hpos := semilocalOnePrimeMomentDefect_pos p.property
  linarith

end RHTower
