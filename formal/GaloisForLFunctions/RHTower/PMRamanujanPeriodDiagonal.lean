import GaloisForLFunctions.RHTower.PMPowerDampedMobiusRamanujanMoment
import GaloisForLFunctions.RHTower.EulerDeletionMobiusPeriodCovariance
import GaloisForLFunctions.RHTower.Sieve.GcdPowerDiagonalization

/-!
# Exact complete-period diagonalization of Ramanujan primitives

Finite multiples inversion turns the signed residue gcd-square form into a
diagonal form in the original Ramanujan coefficients. The density drift and
signed totient mean are explicit, including for actual denominator bands.

These are complete-period identities. The reciprocal anchored energy retains
nonuniform residue weights; no upper bound for that energy is asserted here.
-/

open Finset ArithmeticFunction
open scoped BigOperators
noncomputable section
namespace RHTower

/-- The exact finite real cofactor of a Ramanujan coefficient sequence. -/
def pmRamanujanResidueCoeff (a : ℕ → ℝ) (Q d : ℕ) : ℝ :=
  (d : ℝ) * ∑ m ∈ Icc 1 (Q/d), (moebius m : ℝ) * a (d*m)

private theorem residueCoeff_div (a : ℕ → ℝ) (Q : ℕ) {d : ℕ} (hd : 0 < d) :
    pmRamanujanResidueCoeff a Q d / d =
      ∑ m ∈ Icc 1 (Q/d), (moebius m : ℝ) * a (d*m) := by
  have hd0 : (d : ℝ) ≠ 0 := by exact_mod_cast hd.ne'
  simp [pmRamanujanResidueCoeff, hd0]

/-- Finite multiples inversion retains the whole natural product cutoff. -/
theorem pmRamanujanResidueCoeff_multiples (a : ℕ → ℝ) {Q e : ℕ}
    (he : 0 < e) (heQ : e ≤ Q) :
    (∑ d ∈ (Icc 1 Q).filter (fun d => e ∣ d), pmRamanujanResidueCoeff a Q d / d) = a e := by
  rw [sum_Icc_filter_dvd_reindex e Q he]
  have heq (r : ℕ) (hr : r ∈ Icc 1 (Q/e)) :
      pmRamanujanResidueCoeff a Q (e*r) / ((e*r : ℕ) : ℝ) =
        ∑ m ∈ Icc 1 ((Q/e)/r), (moebius m : ℝ) * a (e*(r*m)) := by
    rw [residueCoeff_div a Q (Nat.mul_pos he (Finset.mem_Icc.mp hr).1),
      Nat.div_div_eq_div_mul]
    simp only [Nat.mul_assoc]
  rw [Finset.sum_congr rfl heq,
    ← Sieve.sum_Icc_divisorsAntidiagonal_swap
      (fun r m => (moebius m : ℝ) * a (e*(r*m))) (Q/e)]
  have ht (n : ℕ) (hn : n ∈ Icc 1 (Q/e)) :
      (∑ x ∈ n.divisorsAntidiagonal, (moebius x.2 : ℝ) * a (e*(x.1*x.2))) =
        (if n = 1 then 1 else 0) * a (e*n) := by
    have hm := congrArg Complex.re (pm_mobius_antidiagonal_sum n)
    simp only [Complex.re_sum, Complex.intCast_re] at hm
    have hm' : (∑ x ∈ n.divisorsAntidiagonal, (moebius x.2 : ℝ)) =
        if n = 1 then 1 else 0 := by
      split_ifs at hm ⊢ <;> simpa using hm
    calc
      _ = (∑ x ∈ n.divisorsAntidiagonal, (moebius x.2 : ℝ)) * a (e*n) := by
        rw [Finset.sum_mul]
        exact Finset.sum_congr rfl (fun x hx => by rw [(Nat.mem_divisorsAntidiagonal.mp hx).1])
      _ = _ := by rw [hm']
  rw [Finset.sum_congr rfl ht]
  have h1 : 1 ≤ Q/e := (Nat.le_div_iff_mul_le he).mpr (by simpa using heQ)
  simp [h1]

private theorem divisors_Icc (Q : ℕ) : (Icc 1 Q).biUnion Nat.divisors = Icc 1 Q := by
  ext d
  constructor
  · intro h
    obtain ⟨n, hn, hd⟩ := mem_biUnion.mp h
    exact mem_Icc.mpr ⟨Nat.pos_of_mem_divisors hd,
      (Nat.le_of_dvd (mem_Icc.mp hn).1 (Nat.dvd_of_mem_divisors hd)).trans (mem_Icc.mp hn).2⟩
  · intro hd
    exact mem_biUnion.mpr ⟨d, hd, Nat.mem_divisors.mpr ⟨dvd_refl _, (by have := (mem_Icc.mp hd).1; omega : d ≠ 0)⟩⟩

/-- The whole signed gcd-square form diagonalizes in the original Ramanujan coefficients. -/
theorem pmRamanujanResidueCoeff_gcd_diagonal (a : ℕ → ℝ) (Q : ℕ) :
    (∑ d ∈ Icc 1 Q, ∑ e ∈ Icc 1 Q,
      pmRamanujanResidueCoeff a Q d * pmRamanujanResidueCoeff a Q e *
        (Nat.gcd d e : ℝ)^2 / ((d : ℝ)*e)) =
      ∑ q ∈ Icc 1 Q, Sieve.gcdPowKernel 2 q * a q^2 := by
  have h := Sieve.sum_gcd_rpow_div_eq_kernel_diagonal (Icc 1 Q)
    (fun d hd => (mem_Icc.mp hd).1) (pmRamanujanResidueCoeff a Q) 2
  rw [divisors_Icc, Finset.sum_product] at h
  simp only [Real.rpow_two] at h
  rw [h]
  exact sum_congr rfl fun q hq => by
    rw [pmRamanujanResidueCoeff_multiples a (mem_Icc.mp hq).1 (mem_Icc.mp hq).2]

/-- Exact complete-period covariance, with the scalar density subtracted explicitly. -/
theorem pmRamanujanResidueCoeff_periodCovariance (a : ℕ → ℝ) {Q : ℕ} (hQ : 1 ≤ Q) :
    DeletionPeriodCovariance.periodCovariance (Icc 1 Q) (pmRamanujanResidueCoeff a Q) =
      ((∑ q ∈ Icc 1 Q, Sieve.gcdPowKernel 2 q * a q^2) - a 1^2) / 12 := by
  have hd := pmRamanujanResidueCoeff_gcd_diagonal a Q
  have hm := pmRamanujanResidueCoeff_multiples a (e := 1) (by omega) hQ
  simp only [one_dvd, filter_true] at hm
  have hc : (∑ d ∈ Icc 1 Q, ∑ e ∈ Icc 1 Q,
      pmRamanujanResidueCoeff a Q d * pmRamanujanResidueCoeff a Q e / ((d : ℝ)*e)) = a 1^2 := by
    rw [← hm, pow_two, sum_mul_sum]
    apply sum_congr rfl
    intro d hd
    apply sum_congr rfl
    intro e he
    ring
  unfold DeletionPeriodCovariance.periodCovariance
  have ht (d e : ℕ) :
      pmRamanujanResidueCoeff a Q d * pmRamanujanResidueCoeff a Q e *
        ((Nat.gcd d e : ℝ)^2-1) / ((d : ℝ)*e) =
      pmRamanujanResidueCoeff a Q d * pmRamanujanResidueCoeff a Q e *
        (Nat.gcd d e : ℝ)^2 / ((d : ℝ)*e) -
      pmRamanujanResidueCoeff a Q d * pmRamanujanResidueCoeff a Q e / ((d : ℝ)*e) := by ring
  simp_rw [ht, sum_sub_distrib]
  rw [hd, hc]
  ring


private theorem primitive_weighted_floor (a : ℕ → ℝ) (Q N : ℕ) :
    (∑ q ∈ Icc 1 Q, a q * (pmRamanujanPrimitive q N).re) =
      ∑ d ∈ Icc 1 Q, pmRamanujanResidueCoeff a Q d * (N/d : ℕ) := by
  simp only [pmRamanujanPrimitive_eq_floor, Complex.re_sum]
  have he (q : ℕ) (hq : q ∈ Icc 1 Q) :
      a q * ∑ x ∈ q.divisorsAntidiagonal,
        ((x.1 : ℂ) * (moebius x.2 : ℂ) * (N/x.1 : ℕ)).re =
      ∑ x ∈ q.divisorsAntidiagonal,
        (x.1 : ℝ) * (moebius x.2 : ℝ) * a (x.1*x.2) * (N/x.1 : ℕ) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro x hx
    rw [(Nat.mem_divisorsAntidiagonal.mp hx).1]
    simp only [Complex.mul_re, Complex.natCast_re, Complex.intCast_re,
      Complex.natCast_im, Complex.intCast_im, mul_zero, zero_mul, sub_zero,
      Complex.mul_im, add_zero]
    ring
  rw [sum_congr rfl he, Sieve.sum_Icc_divisorsAntidiagonal_swap
    (fun d m => (d : ℝ) * (moebius m : ℝ) * a (d*m) * (N/d : ℕ)) Q]
  apply sum_congr rfl
  intro d hd
  rw [pmRamanujanResidueCoeff, mul_sum, sum_mul]
  apply sum_congr rfl
  intro m hm
  ring

/-- The drift-removed finite primitive is the literal negative residue combination. -/
theorem pmRamanujan_sum_primitive_eq_residue (a : ℕ → ℝ) {Q : ℕ}
    (hQ : 1 ≤ Q) (N : ℕ) :
    (∑ q ∈ Icc 1 Q, a q * (pmRamanujanPrimitive q N).re) - a 1 * N =
      -DeletionPeriodCovariance.residueCombination (Icc 1 Q)
        (pmRamanujanResidueCoeff a Q) N := by
  have hm := pmRamanujanResidueCoeff_multiples a (e := 1) (by omega) hQ
  simp only [one_dvd, filter_true] at hm
  rw [primitive_weighted_floor, ← hm, sum_mul,
    DeletionPeriodCovariance.residueCombination, ← sum_sub_distrib, ← sum_neg_distrib]
  apply sum_congr rfl
  intro d hd
  have hd0 : (d : ℝ) ≠ 0 := by exact_mod_cast (by have := (mem_Icc.mp hd).1; omega : d ≠ 0)
  have hn : ((N%d : ℕ) : ℝ) + (d : ℝ)*(N/d : ℕ) = N := by
    exact_mod_cast Nat.mod_add_div N d
  field_simp
  linear_combination pmRamanujanResidueCoeff a Q d * hn

private theorem residueCoeff_sum (a : ℕ → ℝ) (Q : ℕ) :
    (∑ d ∈ Icc 1 Q, pmRamanujanResidueCoeff a Q d) =
      ∑ q ∈ Icc 1 Q, a q * q.totient := by
  simp only [pmRamanujanResidueCoeff, mul_sum]
  rw [← Sieve.sum_Icc_divisorsAntidiagonal_swap]
  apply sum_congr rfl
  intro q hq
  have hphi := congrArg Complex.re (pm_totient_antidiagonal (mem_Icc.mp hq).1)
  simp only [Complex.re_sum, Complex.mul_re, Complex.natCast_re, Complex.intCast_re,
    Complex.natCast_im, Complex.intCast_im, mul_zero, sub_zero] at hphi
  rw [← hphi, mul_sum]
  apply sum_congr rfl
  intro x hx
  rw [(Nat.mem_divisorsAntidiagonal.mp hx).1]
  ring

/-- The complete-period mean retains the signed totient term. -/
theorem pmRamanujanResidueCoeff_periodMean (a : ℕ → ℝ) {Q : ℕ} (hQ : 1 ≤ Q) :
    DeletionPeriodCovariance.periodMean (Icc 1 Q) (pmRamanujanResidueCoeff a Q) =
      ((∑ q ∈ Icc 1 Q, a q * q.totient) - a 1) / 2 := by
  have hm := pmRamanujanResidueCoeff_multiples a (e := 1) (by omega) hQ
  simp only [one_dvd, filter_true] at hm
  rw [← residueCoeff_sum, ← hm, DeletionPeriodCovariance.periodMean,
    ← sum_sub_distrib, sum_div]
  apply sum_congr rfl
  intro d hd
  have hd0 : (d : ℝ) ≠ 0 := by exact_mod_cast (by have := (mem_Icc.mp hd).1; omega : d ≠ 0)
  field_simp

/-- Exact common-period second moment. The density drift and the totient mean are explicit. -/
theorem pmRamanujan_complete_period_square (a : ℕ → ℝ) {Q P : ℕ}
    (hQ : 1 ≤ Q) (hP : ∀ d ∈ Icc 1 Q, d ∣ P) :
    (∑ N ∈ range P,
      ((∑ q ∈ Icc 1 Q, a q * (pmRamanujanPrimitive q N).re) - a 1 * N)^2) =
      (P : ℝ) *
        ((((∑ q ∈ Icc 1 Q, a q * q.totient) - a 1) / 2)^2 +
          ((∑ q ∈ Icc 1 Q, Sieve.gcdPowKernel 2 q * a q^2) - a 1^2) / 12) := by
  simp_rw [pmRamanujan_sum_primitive_eq_residue a hQ, neg_sq]
  rw [DeletionPeriodCovariance.sum_residueCombination_sq _
    (fun d hd => (mem_Icc.mp hd).1) hP,
    pmRamanujanResidueCoeff_periodMean a hQ, pmRamanujanResidueCoeff_periodCovariance a hQ]

/-- Period centering diagonalizes the complete signed quadratic exactly. -/
theorem pmRamanujan_complete_period_centered_square (a : ℕ → ℝ) {Q P : ℕ}
    (hQ : 1 ≤ Q) (hP : ∀ d ∈ Icc 1 Q, d ∣ P) :
    (∑ N ∈ range P,
      ((∑ q ∈ Icc 1 Q, a q * (pmRamanujanPrimitive q N).re) - a 1 * N +
        ((∑ q ∈ Icc 1 Q, a q * q.totient) - a 1) / 2)^2) =
      (P : ℝ) * ((∑ q ∈ Icc 1 Q, Sieve.gcdPowKernel 2 q * a q^2) - a 1^2) / 12 := by
  simp_rw [pmRamanujan_sum_primitive_eq_residue a hQ]
  have h := DeletionPeriodCovariance.sum_residueCombination_centered_sq
    (pmRamanujanResidueCoeff a Q) (fun d hd => (mem_Icc.mp hd).1) hP
  rw [pmRamanujanResidueCoeff_periodMean a hQ,
    pmRamanujanResidueCoeff_periodCovariance a hQ] at h
  calc
    _ = ∑ N ∈ range P,
        (DeletionPeriodCovariance.residueCombination (Icc 1 Q)
          (pmRamanujanResidueCoeff a Q) N -
          ((∑ q ∈ Icc 1 Q, a q * q.totient) - a 1) / 2)^2 := by
      apply sum_congr rfl
      intro N hN
      ring
    _ = _ := h.trans (by ring)

/-- The literal natural-denominator band, with all actual signs retained. -/
def pmRamanujanDenominatorBand (ε : ℝ) (X Y N : ℕ) : ℂ :=
  ∑ q ∈ Ioc X Y, pmPowerDampedRamanujanWeight ε q * pmRamanujanPrimitive q N

private theorem band_Icc_filter {X Y : ℕ} (hX : 1 ≤ X) :
    (Icc 1 Y).filter (fun q => X < q) = Ioc X Y := by
  ext q
  simp only [mem_filter, mem_Icc, mem_Ioc]
  omega

private theorem band_re {ε : ℝ} (hε : 0 < ε) (X Y N : ℕ) :
    (pmRamanujanDenominatorBand ε X Y N).re =
      ∑ q ∈ Ioc X Y, (pmPowerDampedRamanujanWeight ε q).re * (pmRamanujanPrimitive q N).re := by
  simp [pmRamanujanDenominatorBand, Complex.mul_re, pmPowerDampedRamanujanWeight_im hε]

private theorem band_im {ε : ℝ} (hε : 0 < ε) (X Y N : ℕ) :
    (pmRamanujanDenominatorBand ε X Y N).im = 0 := by
  simp [pmRamanujanDenominatorBand, Complex.mul_im,
    pmPowerDampedRamanujanWeight_im hε, pmRamanujanPrimitive_im]

/-- Exact complete-period band energy, retaining its signed totient mean. -/
theorem pmRamanujanDenominatorBand_period_square {ε : ℝ} (hε : 0 < ε)
    {X Y P : ℕ} (hX : 1 ≤ X) (hY : 1 ≤ Y) (hP : ∀ d ∈ Icc 1 Y, d ∣ P) :
    (∑ N ∈ range P, ‖pmRamanujanDenominatorBand ε X Y N‖^2) =
      (P : ℝ) *
        (((∑ q ∈ Ioc X Y, (pmPowerDampedRamanujanWeight ε q).re * q.totient) / 2)^2 +
          (∑ q ∈ Ioc X Y, Sieve.gcdPowKernel 2 q * ‖pmPowerDampedRamanujanWeight ε q‖^2) / 12) := by
  let a : ℕ → ℝ := fun q => if X < q then (pmPowerDampedRamanujanWeight ε q).re else 0
  have ha1 : a 1 = 0 := by simp [a, not_lt.mpr hX]
  have h := pmRamanujan_complete_period_square a hY hP
  rw [ha1] at h
  simp only [zero_mul, sub_zero, zero_pow (by omega : (2:ℕ) ≠ 0)] at h
  have hb (N : ℕ) : (∑ q ∈ Icc 1 Y, a q * (pmRamanujanPrimitive q N).re) =
      (pmRamanujanDenominatorBand ε X Y N).re := by
    rw [band_re hε]
    rw [← band_Icc_filter hX, sum_filter]
    apply sum_congr rfl
    intro q hq
    simp only [a]
    split_ifs <;> simp
  have hm : (∑ q ∈ Icc 1 Y, a q * q.totient) =
      ∑ q ∈ Ioc X Y, (pmPowerDampedRamanujanWeight ε q).re * q.totient := by
    rw [← band_Icc_filter hX, sum_filter]
    apply sum_congr rfl
    intro q hq
    simp only [a]
    split_ifs <;> simp
  have hd : (∑ q ∈ Icc 1 Y, Sieve.gcdPowKernel 2 q * a q^2) =
      ∑ q ∈ Ioc X Y, Sieve.gcdPowKernel 2 q * ‖pmPowerDampedRamanujanWeight ε q‖^2 := by
    rw [← band_Icc_filter hX, sum_filter]
    apply sum_congr rfl
    intro q hq
    simp only [a]
    split_ifs
    · rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply, pmPowerDampedRamanujanWeight_im hε]
      ring
    · simp
  simp_rw [hb] at h
  rw [hm, hd] at h
  convert h using 1
  apply sum_congr rfl
  intro N hN
  rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply, band_im hε]
  ring

end RHTower
