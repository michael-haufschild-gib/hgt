import GaloisForLFunctions.RHTower.EulerDeletionInfiniteDecomposition
import Mathlib.NumberTheory.TsumDivisorsAntidiagonal
import Mathlib.NumberTheory.ArithmeticFunction.Moebius

/-!
# Arithmetic reconstruction from the mixed Euler-deletion remainder

Dividing the retained remainder by its modulus gives a sum over positive multiples
of the weighted ordinary power-sum error. An absolutely convergent product-index
regrouping inverts that sum by the divisor identity for the Möbius function.

At a zeta zero with positive real part, the reconstructed unit error has norm
strictly greater than one half. Thus neither the entire remainder family nor its
Möbius-weighted sum vanishes. This identity alone does not locate any zero.
-/

noncomputable section
open scoped BigOperators ArithmeticFunction.Moebius
open Filter Topology
namespace RHTower.DeletionMixedRefinement

private theorem norm_moebius_complex_le (n : ℕ) : ‖(μ n : ℂ)‖ ≤ 1 := by
  rw [Complex.norm_intCast]
  exact_mod_cast (ArithmeticFunction.abs_moebius_le_one (n := n))

private theorem sum_moebius_divisors (n : ℕ) :
    ∑ d ∈ n.divisors, (μ d : ℂ) = if n = 1 then 1 else 0 := by
  have h := congrArg (fun f : ArithmeticFunction ℂ => f n)
    (ArithmeticFunction.coe_moebius_mul_coe_zeta (R := ℂ))
  simpa only [ArithmeticFunction.coe_mul_zeta_apply, ArithmeticFunction.intCoe_apply, ArithmeticFunction.one_apply] using h

/-- Absolutely admitted inversion of the sum over positive multiples. -/
theorem moebius_multiples_inversion (f : ℕ → ℂ)
    (hf : Summable (fun x : ℕ+ × ℕ+ => ‖f ((x.1 : ℕ) * x.2)‖)) :
    (∑' p : ℕ+, (μ (p : ℕ) : ℂ) * ∑' n : ℕ+, f ((p : ℕ) * n)) = f 1 := by
  have hw : Summable (fun x : ℕ+ × ℕ+ =>
      (μ (x.1 : ℕ) : ℂ) * f ((x.1 : ℕ) * x.2)) := by
    apply hf.of_norm_bounded
    intro x
    rw [norm_mul]
    exact mul_le_of_le_one_left (norm_nonneg _) (norm_moebius_complex_le _)
  have hs := sigmaAntidiagonalEquivProd.summable_iff.mpr hw
  calc
    _ = ∑' x : ℕ+ × ℕ+, (μ (x.1 : ℕ) : ℂ) * f ((x.1 : ℕ) * x.2) := by
      rw [hw.tsum_prod]
      exact tsum_congr fun p => tsum_mul_left.symm
    _ = ∑' n : ℕ+, ∑' x : (n : ℕ).divisorsAntidiagonal,
        (μ x.val.1 : ℂ) * f (x.val.1 * x.val.2) := by
      rw [← sigmaAntidiagonalEquivProd.tsum_eq]
      simpa only [Function.comp_apply, sigmaAntidiagonalEquivProd, Equiv.coe_fn_mk,
        divisorsAntidiagonalFactors, PNat.mk_coe] using hs.tsum_sigma
    _ = ∑' n : ℕ+, if (n : ℕ) = 1 then f 1 else 0 := by
      apply tsum_congr
      intro n
      rw [tsum_fintype, Finset.univ_eq_attach,
        Finset.sum_attach _ (fun x : ℕ × ℕ => (μ x.1 : ℂ) * f (x.1 * x.2))]
      have he : (∑ x ∈ (n : ℕ).divisorsAntidiagonal,
          (μ x.1 : ℂ) * f (x.1 * x.2)) =
          (∑ d ∈ (n : ℕ).divisors, (μ d : ℂ)) * f n := by
        calc
          _ = ∑ x ∈ (n : ℕ).divisorsAntidiagonal, (μ x.1 : ℂ) * f n := by
            apply Finset.sum_congr rfl
            intro x hx
            rw [(Nat.mem_divisorsAntidiagonal.1 hx).1]
          _ = _ := by rw [Nat.sum_divisorsAntidiagonal (fun a _ => (μ a : ℂ) * f n), Finset.sum_mul]
      rw [he, sum_moebius_divisors]
      split_ifs with h
      · simp [h]
      · simp
    _ = f 1 := by
      rw [tsum_eq_single (1 : ℕ+)]
      · simp
      · intro n hn
        have hn' : (n : ℕ) ≠ 1 := by intro h; apply hn; exact Subtype.ext h
        simp [hn']

/-- The ordinary error with its original Dirichlet weight retained. -/
def weightedPowerRemainder (s : ℂ) (n : ℕ) : ℂ :=
  kernel s n * star (powerSumRemainder s n)

/-- The weighted arithmetic remainder has a summable power majorant. -/
theorem norm_weightedPowerRemainder_le {s : ℂ} (hs : 0 < s.re) (hs1 : s ≠ 1)
    {n : ℕ} (hn : 0 < n) :
    ‖weightedPowerRemainder s n‖ ≤
      (‖s * (s + 1)‖ / (s.re + 1)) * (n : ℝ) ^ (-2 * s.re - 1) := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  rw [weightedPowerRemainder, norm_mul, norm_star, kernel, Complex.norm_natCast_cpow_of_pos hn]
  calc
    _ ≤ (n : ℝ) ^ (-s).re *
        ((‖s * (s + 1)‖ / (s.re + 1)) * (n : ℝ) ^ (-s.re - 1)) :=
      mul_le_mul_of_nonneg_left (norm_powerSumRemainder_le (by linarith) hs1 (by omega))
        (Real.rpow_nonneg hn'.le _)
    _ = _ := by
      simp only [Complex.neg_re]
      rw [mul_left_comm, ← Real.rpow_add hn']
      congr 2
      ring

/-- Positive-index majorant for every product-index regrouping. -/
theorem summable_norm_weightedPowerRemainder_pair {s : ℂ} (hs : 0 < s.re) (hs1 : s ≠ 1)
    {m : ℕ} (hm : 0 < m) :
    Summable (fun x : ℕ+ × ℕ+ => ‖weightedPowerRemainder s (m * ((x.1 : ℕ) * x.2))‖) := by
  let a : ℝ := -2 * s.re - 1
  let C : ℝ := ‖s * (s + 1)‖ / (s.re + 1)
  have ha : Summable (fun n : ℕ+ => (n : ℝ) ^ a) :=
    (Real.summable_nat_rpow.2 (by dsimp [a]; linarith)).subtype _
  have hmaj := (ha.mul_of_nonneg ha (fun _ => Real.rpow_nonneg (by positivity) _)
    (fun _ => Real.rpow_nonneg (by positivity) _)).mul_left (C * (m : ℝ) ^ a)
  apply Summable.of_nonneg_of_le (fun _ => norm_nonneg _) ?_ hmaj
  intro x
  refine (norm_weightedPowerRemainder_le hs hs1 (Nat.mul_pos hm (Nat.mul_pos x.1.pos x.2.pos))).trans_eq ?_
  simp only [Nat.cast_mul]
  change C * ((m : ℝ) * ((x.1 : ℝ) * (x.2 : ℝ))) ^ a = _
  rw [Real.mul_rpow (by positivity) (by positivity), Real.mul_rpow (by positivity) (by positivity)]
  ring

/-- Division by the modulus turns the retained remainder into a sum over multiples. -/
theorem infiniteRemainder_div_eq_multiples (s : ℂ) {m : ℕ} (hm : 0 < m) :
    infiniteRemainder s m / (m : ℂ) =
      ∑' n : ℕ+, weightedPowerRemainder s (m * (n : ℕ)) := by
  rw [tsum_pnat_eq_tsum_succ (f := fun n => weightedPowerRemainder s (m * n))]
  simp only [weightedPowerRemainder, kernel_mul, mul_assoc, tsum_mul_left]
  rw [infiniteRemainder, amplitude]
  have hm' : (m : ℂ) ≠ 0 := by exact_mod_cast hm.ne'
  field_simp

/-- The entire modulus family recovers each ordinary remainder by absolute Möbius inversion. -/
theorem infiniteRemainder_moebius_inversion {s : ℂ} (hs : 0 < s.re) (hs1 : s ≠ 1)
    {m : ℕ} (hm : 0 < m) :
    (∑' p : ℕ+, (μ (p : ℕ) : ℂ) *
      (infiniteRemainder s (m * (p : ℕ)) / ((m * (p : ℕ) : ℕ) : ℂ))) =
      weightedPowerRemainder s m := by
  have h := moebius_multiples_inversion (fun n => weightedPowerRemainder s (m * n))
    (summable_norm_weightedPowerRemainder_pair hs hs1 hm)
  calc
    _ = ∑' p : ℕ+, (μ (p : ℕ) : ℂ) * ∑' n : ℕ+,
        weightedPowerRemainder s (m * ((p : ℕ) * n)) := by
      apply tsum_congr
      intro p
      rw [infiniteRemainder_div_eq_multiples s (Nat.mul_pos hm p.pos)]
      simp only [Nat.mul_assoc]
    _ = _ := by simpa only [Nat.mul_one] using h

/-- Absolute convergence of the modulus-normalized remainder family. -/
theorem summable_norm_infiniteRemainder_div {s : ℂ} (hs : 0 < s.re) (hs1 : s ≠ 1)
    {m : ℕ} (hm : 0 < m) :
    Summable (fun p : ℕ+ => ‖infiniteRemainder s (m * (p : ℕ)) /
      ((m * (p : ℕ) : ℕ) : ℂ)‖) := by
  have hh := summable_norm_weightedPowerRemainder_pair hs hs1 hm
  apply Summable.of_nonneg_of_le (fun _ => norm_nonneg _) ?_ hh.prod
  intro p
  rw [infiniteRemainder_div_eq_multiples s (Nat.mul_pos hm p.pos)]
  simpa only [Nat.mul_assoc] using norm_tsum_le_tsum_norm (hh.prod_factor p)

/-- The absolute convergence needed for the signed arithmetic reconstruction is proved. -/
theorem summable_norm_moebius_infiniteRemainder {s : ℂ} (hs : 0 < s.re) (hs1 : s ≠ 1)
    {m : ℕ} (hm : 0 < m) :
    Summable (fun p : ℕ+ => ‖(μ (p : ℕ) : ℂ) *
      (infiniteRemainder s (m * (p : ℕ)) / ((m * (p : ℕ) : ℕ) : ℂ))‖) := by
  apply Summable.of_nonneg_of_le (fun _ => norm_nonneg _) ?_
    (summable_norm_infiniteRemainder_div hs hs1 hm)
  intro p
  rw [norm_mul]
  exact mul_le_of_le_one_left (norm_nonneg _) (norm_moebius_complex_le _)

/-- Arithmetic reconstruction at unit cutoff, with the zeta term retained. -/
theorem moebius_infiniteRemainder_eq {s : ℂ} (hs : 0 < s.re) (hs1 : s ≠ 1) :
    (∑' p : ℕ+, (μ (p : ℕ) : ℂ) * (infiniteRemainder s p / (p : ℂ))) =
      (1 / 2 : ℂ) - star (riemannZeta s) - 1 / (1 - star s) := by
  have h := infiniteRemainder_moebius_inversion hs hs1 (m := 1) (by omega)
  simp only [Nat.one_mul] at h
  rw [h, weightedPowerRemainder, powerSumRemainder]
  simp only [kernel, Nat.cast_one, Complex.one_cpow, one_mul, rawPrefix,
    Finset.sum_range_one, zero_add, star_sub, star_div₀, star_one, star_ofNat]
  ring

/-- The exact reconstructed remainder at a zero is a nonzero boundary value. -/
theorem moebius_infiniteRemainder_at_zero {s : ℂ} (hs : 0 < s.re) (hs1 : s ≠ 1)
    (hz : riemannZeta s = 0) :
    (∑' p : ℕ+, (μ (p : ℕ) : ℂ) * (infiniteRemainder s p / (p : ℂ))) =
      (1 / 2 : ℂ) - 1 / (1 - star s) := by
  rw [moebius_infiniteRemainder_eq hs hs1, hz, star_zero, sub_zero]

private theorem half_lt_norm_boundary {s : ℂ} (hs : 0 < s.re) (hs1 : s ≠ 1) :
    (1 / 2 : ℝ) < ‖(1 / 2 : ℂ) - 1 / (1 - star s)‖ := by
  have hden : 1 - star s ≠ 0 := by
    intro h
    apply hs1
    have h' := congrArg star (sub_eq_zero.1 h)
    simpa using h'.symm
  have he : (1 / 2 : ℂ) - 1 / (1 - star s) = -(1 + star s) / (2 * (1 - star s)) := by
    field_simp
    ring
  have hn : ‖1 - star s‖ < ‖1 + star s‖ := by
    have hm := norm_nonneg (1 - star s)
    have hp := norm_nonneg (1 + star s)
    have he1 := Complex.sq_norm (1 - star s)
    have he2 := Complex.sq_norm (1 + star s)
    simp only [Complex.normSq_apply, Complex.add_re, Complex.sub_re, Complex.one_re,
      Complex.add_im, Complex.sub_im, Complex.one_im, Complex.star_def, Complex.conj_re,
      Complex.conj_im] at he1 he2
    simp only [Complex.star_def] at hm hp ⊢
    nlinarith
  rw [he, norm_div, norm_neg, norm_mul]
  norm_num only [Complex.norm_ofNat]
  apply (lt_div_iff₀ (mul_pos (by norm_num) (norm_pos_iff.2 hden))).2
  nlinarith

/-- Every positive-half-plane zeta zero forces nonzero Möbius-weighted remainder mass. -/
theorem norm_moebius_infiniteRemainder_gt_half_at_zero {s : ℂ}
    (hs : 0 < s.re) (hs1 : s ≠ 1) (hz : riemannZeta s = 0) :
    (1 / 2 : ℝ) < ‖∑' p : ℕ+, (μ (p : ℕ) : ℂ) * (infiniteRemainder s p / (p : ℂ))‖ := by
  rw [moebius_infiniteRemainder_at_zero hs hs1 hz]
  exact half_lt_norm_boundary hs hs1

/-- The entire remainder family cannot vanish at any positive-half-plane zeta zero. -/
theorem exists_infiniteRemainder_ne_zero_at_zero {s : ℂ}
    (hs : 0 < s.re) (hs1 : s ≠ 1) (hz : riemannZeta s = 0) :
    ∃ p : ℕ+, infiniteRemainder s p ≠ 0 := by
  by_contra h
  push Not at h
  have hnorm := norm_moebius_infiniteRemainder_gt_half_at_zero hs hs1 hz
  simp only [h, zero_div, mul_zero, tsum_zero, norm_zero] at hnorm
  norm_num at hnorm

/-- A zeta zero requires strictly more than one half unit of weighted absolute remainder mass. -/
theorem remainder_mass_gt_half_at_zero {s : ℂ}
    (hs : 0 < s.re) (hs1 : s ≠ 1) (hz : riemannZeta s = 0) :
    (1 / 2 : ℝ) < ∑' p : ℕ+, ‖infiniteRemainder s p / (p : ℂ)‖ := by
  apply (norm_moebius_infiniteRemainder_gt_half_at_zero hs hs1 hz).trans_le
  refine (norm_tsum_le_tsum_norm (by simpa only [Nat.one_mul] using
    summable_norm_moebius_infiniteRemainder hs hs1 (m := 1) (by omega))).trans ?_
  apply Summable.tsum_le_tsum ?_
    (by simpa only [Nat.one_mul] using summable_norm_moebius_infiniteRemainder hs hs1 (m := 1) (by omega))
    (by simpa only [Nat.one_mul] using summable_norm_infiniteRemainder_div hs hs1 (m := 1) (by omega))
  intro p
  rw [norm_mul]
  exact mul_le_of_le_one_left (norm_nonneg _) (norm_moebius_complex_le _)


end RHTower.DeletionMixedRefinement
