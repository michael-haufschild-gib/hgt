import GaloisForLFunctions.ExceptionalLayerTheory.GaussianFilteredCentredVaughanError
import GaloisForLFunctions.RHTower.LogVonMangoldtGaussianSums
import GaloisForLFunctions.RHTower.Sieve.TypeIILongSupport

/-!
# Localization to short Vaughan cofactors

The complementary cofactor convolution is supported beyond the product
of its cutoffs. Gaussian decay makes that tail smaller than any prescribed
power beyond a superlinear product horizon.
-/

open Complex Finset Filter Topology RHTower RHTower.Sieve ArithmeticFunction Metric
noncomputable section
namespace GaloisForLFunctions.ExceptionalLayerTheory

/-- The actual type-II coefficient restricted to cofactors above `W`. -/
def gaussianVaughanCofactorTailCoeff (U V W : ℕ) : ArithmeticFunction ℝ :=
  typeIILong U * (typeIIShort V - truncAF (typeIIShort V) W)

/-- Both factors must exceed their cutoffs before a tail term survives. -/
theorem gaussianVaughanCofactorTailCoeff_eq_zero {U V W n : ℕ}
    (hn : n ≤ U * W) : gaussianVaughanCofactorTailCoeff U V W n = 0 := by
  unfold gaussianVaughanCofactorTailCoeff
  rw [ArithmeticFunction.mul_apply]
  apply sum_eq_zero
  intro p hp
  obtain ⟨hprod, _⟩ := Nat.mem_divisorsAntidiagonal.mp hp
  by_cases hd : p.1 ≤ U
  · rw [typeIILong_eq_zero_of_le hd, zero_mul]
  · have hm : p.2 ≤ W := by
      by_contra h
      have hU : U < p.1 := by omega
      have hW : W < p.2 := by omega
      nlinarith only [hU, hW, hprod, hn]
    change typeIILong U p.1 * (typeIIShort V p.2 - truncAF (typeIIShort V) W p.2) = 0
    rw [truncAF_apply, if_pos hm, sub_self, mul_zero]

/-- The restricted convolution keeps the same elementary coefficient bound. -/
theorem norm_gaussianVaughanCofactorTailCoeff_le (U V W n : ℕ) :
    ‖(((gaussianVaughanCofactorTailCoeff U V W) n : ℝ) : ℂ)‖ ≤ 2 * (n : ℝ) ^ 2 := by
  unfold gaussianVaughanCofactorTailCoeff
  rw [coe_mul_apply]
  calc
    _ ≤ ∑ p ∈ n.divisorsAntidiagonal,
        ‖((typeIILong U p.1 : ℝ) : ℂ) * (((typeIIShort V - truncAF (typeIIShort V) W) p.2 : ℝ) : ℂ)‖ := norm_sum_le _ _
    _ ≤ ∑ p ∈ n.divisorsAntidiagonal, 2 * (n : ℝ) := by
      apply sum_le_sum
      intro p hp
      have hp' := Nat.mem_divisorsAntidiagonal.mp hp
      have hp1 : 1 ≤ p.1 := by
        by_contra h
        have hz : p.1 = 0 := by omega
        rw [hz, zero_mul] at hp'
        exact hp'.2 hp'.1.symm
      have hp2 : 1 ≤ p.2 := by
        by_contra h
        have hz : p.2 = 0 := by omega
        rw [hz, mul_zero] at hp'
        exact hp'.2 hp'.1.symm
      have hlong : |typeIILong U p.1| ≤ (p.1 : ℝ) := by
        have hlog := Real.log_le_sub_one_of_pos (by exact_mod_cast hp1 : (0 : ℝ) < p.1)
        exact ((abs_vonMangoldt_sub_truncAF_le U p.1).trans ArithmeticFunction.vonMangoldt_le_log).trans
          (by linarith only [hlog])
      have hshort : |(typeIIShort V - truncAF (typeIIShort V) W) p.2| ≤ 2 * (p.2 : ℝ) := by
        change |typeIIShort V p.2 - truncAF (typeIIShort V) W p.2| ≤ _
        rw [truncAF_apply]
        split_ifs with hm
        · simp only [sub_self, abs_zero]
          positivity
        rw [sub_zero]
        have hh := abs_one_sub_zeta_mul_moebius_le V p.2
        change |typeIIShort V p.2| ≤ 1 + (p.2.divisors.card : ℝ) at hh
        have hcard : (p.2.divisors.card : ℝ) ≤ (p.2 : ℝ) := by exact_mod_cast Nat.card_divisors_le_self p.2
        have hp2' : (1 : ℝ) ≤ p.2 := by exact_mod_cast hp2
        linarith only [hh, hcard, hp2']
      rw [norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs]
      refine (mul_le_mul hlong hshort (abs_nonneg _) (by positivity)).trans_eq ?_
      have hprod : (p.1 : ℝ) * p.2 = n := by exact_mod_cast hp'.1
      nlinarith only [hprod]
    _ = (n.divisors.card : ℝ) * (2 * n) := by simp [card_divisorsAntidiagonal]
    _ ≤ (n : ℝ) * (2 * n) := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      exact_mod_cast Nat.card_divisors_le_self n
    _ = _ := by ring


private theorem tsum_exp_neg_div_sq_le {X : ℝ} (hX : 1 ≤ X) :
    ∑' n : ℕ, Real.exp (-((n : ℝ) / X) ^ 2) ≤ 49 * X := by
  apply Real.tsum_le_of_sum_range_le (fun n => (Real.exp_pos _).le)
  intro N
  rcases N with _ | N
  · simp only [range_zero, sum_empty]
    positivity
  · have hset : range (N + 1) = insert 0 (Icc 1 N) := by
      ext n
      simp only [mem_range, mem_insert, mem_Icc]
      omega
    rw [hset, sum_insert (by simp)]
    simp only [Nat.cast_zero, zero_div, zero_pow (by norm_num : 2 ≠ 0), neg_zero, Real.exp_zero]
    have hb := RHTower.GaussZeroSum.sum_exp_neg_sq_le (zero_lt_one.trans_le hX) N
    linarith only [hb, hX]

private theorem pow_mul_exp_neg_le_factorial {x : ℝ} (hx : 0 ≤ x) (r : ℕ) :
    x ^ r * Real.exp (-x) ≤ (r.factorial : ℝ) := by
  have hf : (0 : ℝ) < r.factorial := by exact_mod_cast Nat.factorial_pos r
  have hh := (div_le_iff₀ hf).mp (Real.pow_div_factorial_le_exp x hx r)
  calc
    _ ≤ (Real.exp x * r.factorial) * Real.exp (-x) :=
      mul_le_mul_of_nonneg_right hh (Real.exp_pos _).le
    _ = _ := by rw [mul_right_comm, ← Real.exp_add, add_neg_cancel, Real.exp_zero, one_mul]

/-- Every even Gaussian lattice moment has its physical-scale bound. -/
theorem tsum_pow_mul_exp_gaussian_le {α X : ℝ} (hα : 0 < α) (hX : 1 ≤ X)
    (hscale : α * X ^ 2 = 2) (r : ℕ) :
    ∑' n : ℕ, (n : ℝ) ^ (2 * r) * Real.exp (-α * (n : ℝ) ^ 2) ≤
      49 * (r.factorial : ℝ) * X ^ (2 * r + 1) := by
  have hX0 := zero_lt_one.trans_le hX
  have hαeq : α = 2 / X ^ 2 := (eq_div_iff (pow_ne_zero 2 hX0.ne')).mpr hscale
  have hpt (n : ℕ) : (n : ℝ) ^ (2 * r) * Real.exp (-α * (n : ℝ) ^ 2) ≤
      ((r.factorial : ℝ) * X ^ (2 * r)) * Real.exp (-((n : ℝ) / X) ^ 2) := by
    have hp : (n : ℝ) ^ (2 * r) = X ^ (2 * r) * (((n : ℝ) / X) ^ 2) ^ r := by
      rw [← pow_mul, div_pow]
      field_simp
    have he : -α * (n : ℝ) ^ 2 = -((n : ℝ) / X) ^ 2 + -((n : ℝ) / X) ^ 2 := by
      rw [hαeq]
      field_simp
      ring
    rw [hp, he, Real.exp_add]
    calc
      _ = X ^ (2 * r) * ((((n : ℝ) / X) ^ 2) ^ r * Real.exp (-((n : ℝ) / X) ^ 2)) *
          Real.exp (-((n : ℝ) / X) ^ 2) := by ring
      _ ≤ X ^ (2 * r) * (r.factorial : ℝ) * Real.exp (-((n : ℝ) / X) ^ 2) := by
        gcongr
        exact pow_mul_exp_neg_le_factorial (sq_nonneg _) r
      _ = _ := by ring
  have hs := RHTower.summable_pow_mul_exp_neg_nat_sq (2 * r) hα
  have hg : Summable (fun n : ℕ => Real.exp (-((n : ℝ) / X) ^ 2)) := by
    have hh := RHTower.summable_pow_mul_exp_neg_nat_sq 0 (by positivity : 0 < 1 / X ^ 2)
    apply hh.congr
    intro n
    simp only [pow_zero, one_mul]
    congr 1
    field_simp
  calc
    _ ≤ ∑' n : ℕ, ((r.factorial : ℝ) * X ^ (2 * r)) * Real.exp (-((n : ℝ) / X) ^ 2) :=
      hs.tsum_le_tsum hpt (hg.mul_left _)
    _ = ((r.factorial : ℝ) * X ^ (2 * r)) * ∑' n : ℕ, Real.exp (-((n : ℝ) / X) ^ 2) := by rw [tsum_mul_left]
    _ ≤ ((r.factorial : ℝ) * X ^ (2 * r)) * (49 * X) :=
      mul_le_mul_of_nonneg_left (tsum_exp_neg_div_sq_le hX) (by positivity)
    _ = _ := by rw [pow_succ]; ring

/-- The complete first moment contributed by cofactors greater than `W`. -/
def gaussianVaughanCofactorTail (σ t : ℝ) (U V W : ℕ) (ε : ℂ) : ℂ :=
  ∑' n : ℕ, (gaussianVaughanCofactorTailCoeff U V W n : ℂ) *
    gaussianPrimeMomentWeight σ ε.re (-ε.im) t n

private theorem norm_cofactor_tail_term_le {σ α ξ t : ℝ}
    (hσ : 0 ≤ σ) (hα : 0 ≤ α) (hαξ : α ≤ ξ) (ht : 0 < t)
    (hξ : ξ ≤ 2 * α * t) (U V W n : ℕ) :
    ‖(gaussianVaughanCofactorTailCoeff U V W n : ℂ) * gaussianPrimeMomentWeight σ α ξ t n‖ ≤
      8 * α * (n : ℝ) ^ 4 * Real.exp (-α * (n : ℝ) ^ 2) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [gaussianVaughanCofactorTailCoeff]
  have hp : (n : ℝ) ^ (2 - σ) ≤ (n : ℝ) ^ 2 := by
    simpa only [Real.rpow_two] using Real.rpow_le_rpow_of_exponent_le
      (by exact_mod_cast hn : (1 : ℝ) ≤ n) (by linarith only [hσ] : 2 - σ ≤ 2)
  rw [norm_mul]
  calc
    _ ≤ (2 * (n : ℝ) ^ 2) * (4 * α * (n : ℝ) ^ (2 - σ) * Real.exp (-α * (n : ℝ) ^ 2)) :=
      mul_le_mul (norm_gaussianVaughanCofactorTailCoeff_le U V W n)
        (norm_gaussianPrimeMomentWeight_le σ hα hαξ ht hξ hn) (norm_nonneg _) (by positivity)
    _ ≤ (2 * (n : ℝ) ^ 2) * (4 * α * (n : ℝ) ^ 2 * Real.exp (-α * (n : ℝ) ^ 2)) := by gcongr
    _ = _ := by ring

/-- Arbitrary Gaussian moments make the actual long-cofactor tail small;
no cancellation or zero-location input enters this estimate. -/
theorem norm_gaussianVaughanCofactorTail_le {σ α ξ t X : ℝ}
    (hσ : 0 ≤ σ) (hα : 0 < α) (hαξ : α ≤ ξ) (ht : 0 < t)
    (hξ : ξ ≤ 2 * α * t) (hX : 1 ≤ X) (hscale : α * X ^ 2 = 2)
    {U W : ℕ} (hU : 1 ≤ U) (hW : 1 ≤ W) (V k : ℕ) :
    ‖gaussianVaughanCofactorTail σ t U V W ((α : ℂ) - ξ * I)‖ ≤
      784 * ((k + 2).factorial : ℝ) * X ^ (3 + 2 * k) / ((U * W : ℕ) : ℝ) ^ (2 * k) := by
  let B : ℝ := ((U * W : ℕ) : ℝ)
  have hB : 0 < B := by dsimp only [B]; exact_mod_cast Nat.mul_pos hU hW
  let f := fun n : ℕ => (gaussianVaughanCofactorTailCoeff U V W n : ℂ) * gaussianPrimeMomentWeight σ α ξ t n
  have hs : Summable (fun n : ℕ => ‖f n‖) :=
    ((RHTower.summable_pow_mul_exp_neg_nat_sq 4 hα).mul_left (8 * α)).of_nonneg_of_le
      (fun n => norm_nonneg _) (fun n => by
        simpa only [f, mul_assoc] using norm_cofactor_tail_term_le hσ hα.le hαξ ht hξ U V W n)
  have hpt (n : ℕ) : ‖f n‖ ≤ (8 * α / B ^ (2 * k)) *
      ((n : ℝ) ^ (2 * (k + 2)) * Real.exp (-α * (n : ℝ) ^ 2)) := by
    by_cases hn : n ≤ U * W
    · dsimp only [f]
      rw [gaussianVaughanCofactorTailCoeff_eq_zero hn, Complex.ofReal_zero, zero_mul, norm_zero]
      positivity
    · have hBn : B ≤ (n : ℝ) := by dsimp only [B]; exact_mod_cast (show U * W ≤ n by omega)
      have hn0 : 0 < (n : ℝ) := hB.trans_le hBn
      have hp := pow_le_pow_left₀ hB.le hBn (2 * k)
      have hbound := norm_cofactor_tail_term_le hσ hα.le hαξ ht hξ U V W n
      apply hbound.trans
      calc
        _ ≤ (8 * α * ((n : ℝ) ^ (2 * (k + 2)) * Real.exp (-α * (n : ℝ) ^ 2))) / B ^ (2 * k) := by
          apply (le_div_iff₀ (pow_pos hB (2 * k))).mpr
          have H := mul_le_mul_of_nonneg_left hp
            (show 0 ≤ 8 * α * (n : ℝ) ^ 4 * Real.exp (-α * (n : ℝ) ^ 2) by positivity)
          rw [show 2 * (k + 2) = 4 + 2 * k by omega, pow_add]
          convert H using 1
          ring
        _ = _ := by ring
  have hm := tsum_pow_mul_exp_gaussian_le hα hX hscale (k + 2)
  have hsum : ‖∑' n : ℕ, f n‖ ≤
      (8 * α / B ^ (2 * k)) * (49 * ((k + 2).factorial : ℝ) * X ^ (2 * (k + 2) + 1)) := by
    calc
      _ ≤ ∑' n : ℕ, ‖f n‖ := norm_tsum_le_tsum_norm hs
      _ ≤ ∑' n : ℕ, (8 * α / B ^ (2 * k)) *
          ((n : ℝ) ^ (2 * (k + 2)) * Real.exp (-α * (n : ℝ) ^ 2)) :=
        hs.tsum_le_tsum hpt ((RHTower.summable_pow_mul_exp_neg_nat_sq (2 * (k + 2)) hα).mul_left _)
      _ = (8 * α / B ^ (2 * k)) *
          ∑' n : ℕ, (n : ℝ) ^ (2 * (k + 2)) * Real.exp (-α * (n : ℝ) ^ 2) := by rw [tsum_mul_left]
      _ ≤ _ := mul_le_mul_of_nonneg_left hm (by positivity)
  have he : gaussianVaughanCofactorTail σ t U V W ((α : ℂ) - ξ * I) = ∑' n : ℕ, f n := by
    simp only [gaussianVaughanCofactorTail, f, Complex.sub_re, Complex.ofReal_re,
      Complex.mul_re, Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero,
      sub_zero, Complex.sub_im, Complex.mul_im, mul_one, add_zero, neg_neg, zero_sub]
  rw [he]
  apply hsum.trans_eq
  rw [show 2 * (k + 2) + 1 = (3 + 2 * k) + 2 by omega, pow_add]
  calc
    _ = (392 * ((k + 2).factorial : ℝ) * X ^ (3 + 2 * k) / B ^ (2 * k)) * (α * X ^ 2) := by ring
    _ = _ := by rw [hscale]; dsimp only [B]; ring

private theorem differentiableAt_cofactorDampingSeries
    (a : ℕ → ℂ) {C : ℝ} (hC : 0 ≤ C) (k : ℕ)
    (ha : ∀ n : ℕ, ‖a n‖ ≤ C * (n : ℝ) ^ k) {ε : ℂ} (hε : 0 < ε.re) :
    DifferentiableAt ℂ (fun z : ℂ => ∑' n : ℕ, a n * Complex.exp (-(z * (n : ℂ) ^ 2))) ε := by
  let U : Set ℂ := {z | ε.re / 2 < z.re}
  have hU : IsOpen U := isOpen_lt continuous_const Complex.continuous_re
  have hεU : ε ∈ U := by dsimp only [U, Set.mem_setOf_eq]; linarith only [hε]
  have hs := (RHTower.summable_pow_mul_exp_neg_nat_sq k (by positivity : 0 < ε.re / 2)).mul_left C
  have hf (n : ℕ) : DifferentiableOn ℂ
      (fun z : ℂ => a n * Complex.exp (-(z * (n : ℂ) ^ 2))) U := by fun_prop
  have hb (n : ℕ) (z : ℂ) (hz : z ∈ U) :
      ‖a n * Complex.exp (-(z * (n : ℂ) ^ 2))‖ ≤
        C * ((n : ℝ) ^ k * Real.exp (-(ε.re / 2) * (n : ℝ) ^ 2)) := by
    have hr : (-(z * (n : ℂ) ^ 2)).re = -z.re * (n : ℝ) ^ 2 := by
      simp only [Complex.neg_re, Complex.mul_re, pow_two, Complex.mul_im,
        Complex.natCast_re, Complex.natCast_im, mul_zero, zero_mul, sub_zero, add_zero]
      ring
    rw [norm_mul, Complex.norm_exp, hr]
    have he : Real.exp (-z.re * (n : ℝ) ^ 2) ≤ Real.exp (-(ε.re / 2) * (n : ℝ) ^ 2) := by
      apply Real.exp_le_exp.mpr
      have hh := mul_le_mul_of_nonneg_right (le_of_lt hz) (sq_nonneg (n : ℝ))
      linarith only [hh]
    calc
      _ ≤ (C * (n : ℝ) ^ k) * Real.exp (-(ε.re / 2) * (n : ℝ) ^ 2) :=
        mul_le_mul (ha n) he (Real.exp_pos _).le (by positivity)
      _ = _ := by ring
  exact (Complex.differentiableOn_tsum_of_summable_norm hs hf hU hb).differentiableAt (hU.mem_nhds hεU)


/-- Normal convergence makes the actual cofactor tail holomorphic in damping. -/
theorem differentiableAt_gaussianVaughanCofactorTail {σ : ℝ} (hσ : 0 ≤ σ)
    (t : ℝ) (U V W : ℕ) {ε : ℂ} (hε : 0 < ε.re) :
    DifferentiableAt ℂ (gaussianVaughanCofactorTail σ t U V W) ε := by
  let c := gaussianVaughanCofactorTailCoeff U V W
  have hreconstruct (z : ℂ) : (z.re : ℂ) - (-z.im : ℝ) * I = z := by
    apply Complex.ext <;> simp
  change DifferentiableAt ℂ (fun z : ℂ => ∑' n : ℕ, (c n : ℂ) *
    gaussianPrimeMomentWeight σ z.re (-z.im) t n) ε
  let a (n : ℕ) := (c n : ℂ) * (n : ℂ) ^ (2 - ((σ : ℂ) + t * I))
  have ha (n : ℕ) : ‖a n‖ ≤ (2 : ℝ) * (n : ℝ) ^ 4 := by
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp [a]
    have hnR : (0 : ℝ) < n := by exact_mod_cast hn
    have hp : (n : ℝ) ^ (2 - σ) ≤ (n : ℝ) ^ 2 := by
      simpa only [Real.rpow_two] using Real.rpow_le_rpow_of_exponent_le
        (by exact_mod_cast hn : (1 : ℝ) ≤ n) (by linarith only [hσ] : 2 - σ ≤ 2)
    have hre : (2 - ((σ : ℂ) + t * I)).re = 2 - σ := by simp
    dsimp only [a]
    rw [norm_mul]
    have he : ‖(n : ℂ) ^ (2 - ((σ : ℂ) + t * I))‖ = (n : ℝ) ^ (2 - σ) := by
      simpa only [Complex.ofReal_natCast, hre] using
        (Complex.norm_cpow_eq_rpow_re_of_pos hnR (2 - ((σ : ℂ) + t * I)))
    rw [he]
    calc
      _ ≤ ((2 : ℝ) * (n : ℝ) ^ 2) * (n : ℝ) ^ 2 :=
        mul_le_mul (norm_gaussianVaughanCofactorTailCoeff_le U V W n) hp (Real.rpow_nonneg hnR.le _) (by positivity)
      _ = _ := by ring
  have he (z : ℂ) : (∑' n : ℕ, (c n : ℂ) *
      gaussianPrimeMomentWeight σ z.re (-z.im) t n) =
      (z / (t : ℂ)) * ∑' n : ℕ, a n * Complex.exp (-(z * (n : ℂ) ^ 2)) := by
    rw [← tsum_mul_left]
    apply tsum_congr
    intro n
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp [a]
    rw [gaussianPrimeMomentWeight_eq_mellin σ z.re (-z.im) t hn,
      hreconstruct, gaussianMellinWeight]
    simp only [Complex.ofReal_natCast]
    dsimp only [a]
    ring
  simp_rw [he]
  exact (differentiableAt_id.div_const (t : ℂ)).mul
    (differentiableAt_cofactorDampingSeries a (by norm_num : (0 : ℝ) ≤ 2) 4 ha hε)

/-- The centred type-II current retaining only cofactors at most `W`. -/
def gaussianCentredVaughanCofactorCurrent (σ α ξ t : ℝ) (U V W : ℕ) : ℂ :=
  (∑' n : ℕ, (((typeIILong U * truncAF (typeIIShort V) W) n : ℝ) : ℂ) *
    gaussianPrimeMomentWeight σ α ξ t n) +
  (∑ b ∈ Icc 1 V, ((truncAF (moebius : ArithmeticFunction ℝ) V b : ℝ) : ℂ) / (b : ℂ)) *
    gaussianFirstMomentLogPole ((σ : ℂ) + t * I) ((α : ℂ) - ξ * I) t -
  (1 + (∑ b ∈ Icc 1 (U * V),
      (((truncAF vonMangoldt U * truncAF (moebius : ArithmeticFunction ℝ) V) b : ℝ) : ℂ) / (b : ℂ)) +
    ∑ b ∈ Icc 1 V, ((truncAF (moebius : ArithmeticFunction ℝ) V b : ℝ) : ℂ) *
      (Real.log (b : ℝ) : ℂ) / (b : ℂ)) *
    gaussianFirstMomentPole ((σ : ℂ) + t * I) ((α : ℂ) - ξ * I) t


/-- Truncating cofactors changes the centred current by exactly the actual
complementary convolution; both continuum terms remain intact. -/
theorem gaussianCentredVaughan_sub_cofactorCurrent_eq {σ α ξ t : ℝ}
    (hσ : 0 ≤ σ) (hα : 0 < α) (hαξ : α ≤ ξ) (ht : 0 < t)
    (hξ : ξ ≤ 2 * α * t) (U V W : ℕ) :
    gaussianCentredVaughanCurrent σ α ξ t U V -
      gaussianCentredVaughanCofactorCurrent σ α ξ t U V W =
        gaussianVaughanCofactorTail σ t U V W ((α : ℂ) - ξ * I) := by
  let f := fun n : ℕ => (((typeIILong U * typeIIShort V) n : ℝ) : ℂ) *
    gaussianPrimeMomentWeight σ α ξ t n
  let g := fun n : ℕ => (gaussianVaughanCofactorTailCoeff U V W n : ℂ) *
    gaussianPrimeMomentWeight σ α ξ t n
  have hf : Summable f := by
    have hh := (summable_gaussianVaughan_moment_typeII hσ hα ξ t U V).mul_left
      (((α : ℂ) - ξ * I) / t)
    apply hh.congr
    intro n
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp [f]
    · dsimp only [f]
      rw [gaussianPrimeMomentWeight_eq_shift σ α ξ t hn]
      ring
  have hg : Summable g := by
    apply ((RHTower.summable_pow_mul_exp_neg_nat_sq 4 hα).mul_left (8 * α)).of_norm_bounded
    intro n
    simpa only [g, mul_assoc] using norm_cofactor_tail_term_le hσ hα.le hαξ ht hξ U V W n
  have hsplit : typeIILong U * typeIIShort V - gaussianVaughanCofactorTailCoeff U V W =
      typeIILong U * truncAF (typeIIShort V) W := by
    unfold gaussianVaughanCofactorTailCoeff
    rw [mul_sub]
    abel
  have hs : (∑' n : ℕ, (((typeIILong U * truncAF (typeIIShort V) W) n : ℝ) : ℂ) *
      gaussianPrimeMomentWeight σ α ξ t n) = (∑' n : ℕ, f n) - ∑' n : ℕ, g n := by
    rw [← hf.tsum_sub hg]
    apply tsum_congr
    intro n
    have hc := congrArg (fun a : ArithmeticFunction ℝ => a n) hsplit
    change (typeIILong U * typeIIShort V) n - gaussianVaughanCofactorTailCoeff U V W n =
      (typeIILong U * truncAF (typeIIShort V) W) n at hc
    rw [← hc]
    dsimp only [f, g]
    push_cast
    ring
  unfold gaussianCentredVaughanCurrent gaussianCentredVaughanCofactorCurrent
  rw [hs]
  have he : gaussianVaughanCofactorTail σ t U V W ((α : ℂ) - ξ * I) = ∑' n : ℕ, g n := by
    simp only [gaussianVaughanCofactorTail, g, Complex.sub_re, Complex.ofReal_re,
      Complex.mul_re, Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero,
      sub_zero, Complex.sub_im, Complex.mul_im, mul_one, add_zero, neg_neg, zero_sub]
  rw [he]
  dsimp only [f]
  ring

#print axioms gaussianCentredVaughan_sub_cofactorCurrent_eq
#print axioms differentiableAt_gaussianVaughanCofactorTail
#print axioms tsum_pow_mul_exp_gaussian_le
#print axioms norm_gaussianVaughanCofactorTail_le
#print axioms gaussianVaughanCofactorTailCoeff_eq_zero
#print axioms norm_gaussianVaughanCofactorTailCoeff_le

end GaloisForLFunctions.ExceptionalLayerTheory
