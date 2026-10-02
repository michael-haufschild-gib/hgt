import GaloisForLFunctions.RHTower.PMPowerDampedMobiusRamanujanMoment
import Mathlib.Data.Finset.NatDivisors

/-!
# Exact prime-paired Ramanujan energy and its signed covariance limit

The primitive prime recursion preserves all four Gram terms. Floor dilation
scales the reciprocal energy exactly; periodic centering and finite Abel
summation identify the mixed dilation limit. For every fixed non-prime-power
channel, the paired primitive covariance is eventually negative. Actual
Möbius-aligned weights make its cross energy positive when the channel is
squarefree. No uniform natural-cutoff energy budget is asserted.
-/

open MeasureTheory Set Filter Topology Complex ArithmeticFunction
open scoped BigOperators
noncomputable section
namespace RHTower

private theorem pm_sum_divisors_prime_mul (F : ℕ → ℂ) {p q : ℕ}
    (hp : p.Prime) (hpq : ¬ p ∣ q) :
    (∑ d ∈ (p*q).divisors, F d) = ∑ d ∈ q.divisors, (F d + F (p*d)) := by
  classical
  rw [(hp.coprime_iff_not_dvd.mpr hpq).divisors_mul]
  simp only [Finset.sum_map, Function.Embedding.coeFn_mk]
  trans ∑ x ∈ p.divisors ×ˢ q.divisors, F (x.1*x.2)
  · exact Finset.sum_attach (p.divisors ×ˢ q.divisors) (fun x : ℕ × ℕ => F (x.1*x.2))
  rw [Finset.sum_product, hp.divisors]
  rw [Finset.sum_pair hp.ne_one.symm]
  simp only [one_mul, Finset.sum_add_distrib]

theorem pmRamanujanPrimitive_prime_mul {p q : ℕ} (hp : p.Prime)
    (hpq : ¬ p ∣ q) (N : ℕ) :
    pmRamanujanPrimitive (p*q) N =
      (p : ℂ)*pmRamanujanPrimitive q (N/p)-pmRamanujanPrimitive q N := by
  have hf (q N : ℕ) : pmRamanujanPrimitive q N =
      ∑ d ∈ q.divisors, (d : ℂ)*(moebius (q/d) : ℂ)*((N/d : ℕ) : ℂ) := by
    rw [pmRamanujanPrimitive_eq_floor,
      Nat.sum_divisorsAntidiagonal (fun a b => (a : ℂ)*(moebius b : ℂ)*((N/a : ℕ) : ℂ))]
  simp_rw [hf]
  rw [pm_sum_divisors_prime_mul _ hp hpq]
  simp only [Finset.mul_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro d hd
  have hdq : d ∣ q := Nat.dvd_of_mem_divisors hd
  have hpqd : ¬ p ∣ q/d := fun h => hpq (h.trans (Nat.div_dvd_of_dvd hdq))
  have hm : (moebius (p*(q/d)) : ℂ) = -(moebius (q/d) : ℂ) := by
    have hmR : (moebius (p*(q/d)) : ℝ) = -(moebius (q/d) : ℝ) := by
      simpa [hpqd] using (Sieve.moebius_prime_mul (e := q/d) hp)
    exact_mod_cast hmR
  rw [Nat.mul_div_assoc p hdq, hm,
    Nat.mul_div_mul_left q d hp.pos, Nat.div_div_eq_div_mul]
  push_cast
  ring

private theorem pm_bounded_reciprocal_summable (f : ℕ → ℝ) {B : ℝ}
    (hB : ∀ N, ‖f N‖ ≤ B) :
    Summable (fun N : ℕ => f N/((N : ℝ)*((N : ℝ)+1))) := by
  apply (summable_nat_add_iff 1).mp
  have hs := (GaloisForLFunctions.hasSum_one_div_shift_mul_succ
    (by norm_num : (0 : ℝ)<1)).summable
  apply Summable.of_norm_bounded (hs.mul_left B)
  intro N
  simp only [norm_div, Real.norm_eq_abs, Nat.cast_add, Nat.cast_one]
  rw [abs_of_nonneg (by positivity : 0 ≤ ((N : ℝ)+1)*((N : ℝ)+1+1))]
  calc
    _ ≤ B/(((N : ℝ)+1)*((N : ℝ)+1+1)) :=
      div_le_div_of_nonneg_right (hB _) (by positivity)
    _ = _ := by ring

private theorem pm_floor_weight_block {p k : ℕ} (hp : 0 < p) (hk : 0 < k) :
    (∑ r : Fin p, 1 / ((((k*p : ℕ) : ℝ)+r)*(((k*p : ℕ) : ℝ)+r+1))) =
      (1/((k : ℝ)*((k : ℝ)+1)))/(p : ℝ) := by
  trans ∑ r ∈ Finset.range p,
    1 / ((((k*p : ℕ) : ℝ)+r)*(((k*p : ℕ) : ℝ)+r+1))
  · exact Fin.sum_univ_eq_sum_range
      (fun r : ℕ => 1 / ((((k*p : ℕ) : ℝ)+r)*(((k*p : ℕ) : ℝ)+r+1))) p
  have hkp : (0 : ℝ) < (k*p : ℕ) := by exact_mod_cast Nat.mul_pos hk hp
  have ht (r : ℕ) :
      1/((((k*p : ℕ) : ℝ)+r)*(((k*p : ℕ) : ℝ)+r+1)) =
        1/(((k*p : ℕ) : ℝ)+r)-1/(((k*p : ℕ) : ℝ)+(r+1 : ℕ)) := by
    have h1 : (0 : ℝ) < ((k*p : ℕ) : ℝ)+r := by positivity
    have h2 : (0 : ℝ) < ((k*p : ℕ) : ℝ)+r+1 := by positivity
    push_cast
    field_simp
    ring
  rw [Finset.sum_congr rfl (fun r _ => ht r), Finset.sum_range_sub']
  have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast hp.ne'
  have hk0 : (k : ℝ) ≠ 0 := by exact_mod_cast hk.ne'
  have hk1 : (k : ℝ)+1 ≠ 0 := by positivity
  have hkp0 : (k : ℝ)*(p : ℝ)+(p : ℝ) ≠ 0 := by positivity
  push_cast
  field_simp
  ring

theorem pm_tsum_floor_dilation (f : ℕ → ℝ) {B : ℝ} (hB : ∀ N, ‖f N‖ ≤ B)
    (hf0 : f 0 = 0) {p : ℕ} (hp : 0 < p) :
    (∑' N : ℕ, f (N/p)/((N : ℝ)*((N : ℝ)+1))) =
      (∑' N : ℕ, f N/((N : ℝ)*((N : ℝ)+1)))/(p : ℝ) := by
  letI : NeZero p := ⟨hp.ne'⟩
  let F : ℕ → ℝ := fun N => f (N/p)/((N : ℝ)*((N : ℝ)+1))
  have hF : Summable F := pm_bounded_reciprocal_summable _ (fun N => hB (N/p))
  let e := (Nat.divModEquiv p).symm
  have hE : Summable (F ∘ e) := e.summable_iff.mpr hF
  have hd (x : ℕ × Fin p) : (x.1*p+x.2)/p = x.1 :=
    congrArg Prod.fst ((Nat.divModEquiv p).apply_symm_apply x)
  have hdiv (k : ℕ) (r : Fin p) : (k*p+r.val)/p = k := hd (k,r)
  change (∑' N, F N) = _
  rw [← e.tsum_eq F]
  trans ∑' k : ℕ, ∑' r : Fin p, F (e (k,r))
  · exact hE.tsum_prod
  have hblock (k : ℕ) : (∑' r : Fin p, F (e (k,r))) =
      (f k/((k : ℝ)*((k : ℝ)+1)))/(p : ℝ) := by
    rw [tsum_fintype]
    simp only [F, e, Nat.divModEquiv_symm_apply, hdiv]
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · simp [hf0]
    · simp only [Nat.cast_add]
      calc
        _ = f k * ∑ r : Fin p,
            1/((((k*p : ℕ) : ℝ)+r)*(((k*p : ℕ) : ℝ)+r+1)) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro r hr
          ring
        _ = _ := by rw [pm_floor_weight_block hp hk]; ring
  rw [tsum_congr hblock, tsum_div_const]

theorem pmRamanujanPrimitiveGram_prime_pair {p q r : ℕ} (hp : p.Prime)
    (hq : 1 < q) (hr : 1 < r) (hpq : ¬ p ∣ q) (hpr : ¬ p ∣ r) :
    pmRamanujanPrimitiveGram (p*q) (p*r) +
      pmRamanujanPrimitiveGram (p*q) r + pmRamanujanPrimitiveGram q (p*r) =
        ((p : ℝ)-1)*pmRamanujanPrimitiveGram q r := by
  have hpq1 : 1 < p*q := lt_of_lt_of_le hq (Nat.le_mul_of_pos_left q hp.pos)
  have hpr1 : 1 < p*r := lt_of_lt_of_le hr (Nat.le_mul_of_pos_left r hp.pos)
  let f : ℕ → ℝ := fun N =>
    (pmRamanujanPrimitive q N).re*(pmRamanujanPrimitive r N).re
  have hB (N : ℕ) : ‖f N‖ ≤ pmRamanujanPrimitiveBound q*pmRamanujanPrimitiveBound r := by
    dsimp only [f]
    rw [norm_mul]
    apply mul_le_mul
    · exact (Complex.abs_re_le_norm _).trans (norm_pmRamanujanPrimitive_le hq N)
    · exact (Complex.abs_re_le_norm _).trans (norm_pmRamanujanPrimitive_le hr N)
    · exact norm_nonneg _
    · exact Finset.sum_nonneg (fun _ _ => norm_nonneg _)
  have hf0 : f 0 = 0 := by simp [f, pmRamanujanPrimitive]
  have hd := pm_tsum_floor_dilation f hB hf0 hp.pos
  have ht (N : ℕ) :
      pmRamanujanPrimitiveGramTerm (p*q) (p*r) N +
        pmRamanujanPrimitiveGramTerm (p*q) r N +
        pmRamanujanPrimitiveGramTerm q (p*r) N +
        pmRamanujanPrimitiveGramTerm q r N =
          (p : ℝ)^2*(f (N/p)/((N : ℝ)*((N : ℝ)+1))) := by
    simp only [pmRamanujanPrimitiveGramTerm, pmRamanujanPrimitive_prime_mul hp hpq,
      pmRamanujanPrimitive_prime_mul hp hpr, Complex.sub_re, Complex.mul_re,
      Complex.natCast_re, Complex.natCast_im, zero_mul, sub_zero, f]
    ring
  have hsum := congrArg (fun F : ℕ → ℝ => ∑' N, F N) (funext ht)
  rw [((summable_pmRamanujanPrimitiveGramTerm hpq1 hpr1).add
      (summable_pmRamanujanPrimitiveGramTerm hpq1 hr) |>.add
      (summable_pmRamanujanPrimitiveGramTerm hq hpr1)).tsum_add
        (summable_pmRamanujanPrimitiveGramTerm hq hr),
    ((summable_pmRamanujanPrimitiveGramTerm hpq1 hpr1).add
      (summable_pmRamanujanPrimitiveGramTerm hpq1 hr)).tsum_add
        (summable_pmRamanujanPrimitiveGramTerm hq hpr1),
    (summable_pmRamanujanPrimitiveGramTerm hpq1 hpr1).tsum_add
      (summable_pmRamanujanPrimitiveGramTerm hpq1 hr), tsum_mul_left, hd] at hsum
  change pmRamanujanPrimitiveGram (p*q) (p*r) +
    pmRamanujanPrimitiveGram (p*q) r + pmRamanujanPrimitiveGram q (p*r) +
    pmRamanujanPrimitiveGram q r =
      (p : ℝ)^2*(pmRamanujanPrimitiveGram q r/(p : ℝ)) at hsum
  have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast hp.ne_zero
  have he : (p : ℝ)^2*(pmRamanujanPrimitiveGram q r/(p : ℝ)) =
      (p : ℝ)*pmRamanujanPrimitiveGram q r := by field_simp
  rw [he] at hsum
  linarith

theorem pmRamanujanPrimitiveGram_prime_pair_damped {p q r : ℕ} (hp : p.Prime)
    (hq : 1 < q) (hr : 1 < r) (hpq : ¬ p ∣ q) (hpr : ¬ p ∣ r)
    {b : ℝ} (hb : b ≠ 0) :
    pmRamanujanPrimitiveGram q r -
      (pmRamanujanPrimitiveGram (p*q) r+pmRamanujanPrimitiveGram q (p*r))/b +
        pmRamanujanPrimitiveGram (p*q) (p*r)/b^2 =
      (1-((p : ℝ)-1)/b)*pmRamanujanPrimitiveGram q r +
        ((b+1)/b^2)*pmRamanujanPrimitiveGram (p*q) (p*r) := by
  have h := pmRamanujanPrimitiveGram_prime_pair hp hq hr hpq hpr
  field_simp
  linear_combination -b*h

private theorem pm_tsum_nat_blocks (F : ℕ → ℝ) (hF : Summable F)
    {p : ℕ} (hp : 0 < p) :
    (∑' N : ℕ, F N) = ∑' k : ℕ, ∑ r : Fin p, F (k*p+r) := by
  letI : NeZero p := ⟨hp.ne'⟩
  let e := (Nat.divModEquiv p).symm
  have hE : Summable (F ∘ e) := e.summable_iff.mpr hF
  rw [← e.tsum_eq F]
  trans ∑' k : ℕ, ∑' r : Fin p, F (e (k,r))
  · exact hE.tsum_prod
  simp only [tsum_fintype, e, Nat.divModEquiv_symm_apply]

private theorem pm_abs_sum_mul_antitone_le (a w : ℕ → ℝ) (L : ℕ) {B : ℝ}
    (hB : 0 ≤ B) (hw : ∀ k, 0 ≤ w k) (hanti : Antitone w)
    (hprefix : ∀ K ≤ L, |∑ i ∈ Finset.range K, a i| ≤ B) :
    |∑ i ∈ Finset.range L, w i*a i| ≤ B*w 0 := by
  by_cases hL : L = 0
  · subst L
    simpa using mul_nonneg hB (hw 0)
  let P (K : ℕ) := ∑ i ∈ Finset.range K, a i
  have he : (∑ i ∈ Finset.range L, w i*a i) =
      w (L-1)*P L + ∑ i ∈ Finset.range (L-1), (w i-w (i+1))*P (i+1) := by
    have h := Finset.sum_range_by_parts w a L
    simp only [smul_eq_mul] at h
    rw [h]
    simp only [sub_mul, Finset.sum_sub_distrib, P]
    ring
  rw [he]
  calc
    _ ≤ |w (L-1)*P L| + ∑ i ∈ Finset.range (L-1), |(w i-w (i+1))*P (i+1)| :=
      (abs_add_le _ _).trans (add_le_add le_rfl (Finset.abs_sum_le_sum_abs _ _))
    _ ≤ w (L-1)*B + ∑ i ∈ Finset.range (L-1), (w i-w (i+1))*B := by
      apply add_le_add
      · rw [abs_mul, abs_of_nonneg (hw _)]
        exact mul_le_mul_of_nonneg_left (hprefix L le_rfl) (hw _)
      · apply Finset.sum_le_sum
        intro i hi
        have hd : 0 ≤ w i-w (i+1) := sub_nonneg.mpr (hanti (by omega))
        rw [abs_mul, abs_of_nonneg hd]
        exact mul_le_mul_of_nonneg_left
          (hprefix (i+1) (by simp only [Finset.mem_range] at hi; omega)) hd
    _ = _ := by rw [← Finset.sum_mul, Finset.sum_range_sub']; ring

private theorem pm_centered_reciprocal_block_le (g : ℕ → ℝ) {B m : ℝ}
    (hB : ∀ K, |∑ i ∈ Finset.range K, (g i-m)| ≤ B)
    {p k : ℕ} (hp : 0 < p) (hk : 0 < k) :
    |∑ r : Fin p, (g (k*p+r)-m)/
      ((((k*p+r : ℕ) : ℝ))*(((k*p+r : ℕ) : ℝ)+1))| ≤
        2*B/(((k*p : ℕ) : ℝ)*(((k*p : ℕ) : ℝ)+1)) := by
  have hB0 : 0 ≤ B := by simpa using hB 0
  let a : ℕ → ℝ := fun i => g (k*p+i)-m
  let w : ℕ → ℝ := fun i => 1/(((k*p+i : ℕ) : ℝ)*(((k*p+i : ℕ) : ℝ)+1))
  have hprefix (K : ℕ) : |∑ i ∈ Finset.range K, a i| ≤ 2*B := by
    have he := Finset.sum_range_add (fun i => g i-m) (k*p) K
    have he' : (∑ i ∈ Finset.range K, a i) =
        (∑ i ∈ Finset.range (k*p+K), (g i-m))-
          ∑ i ∈ Finset.range (k*p), (g i-m) := by
      dsimp only [a]
      linarith [he]
    rw [he']
    exact (abs_sub _ _).trans (by linarith [hB (k*p+K), hB (k*p)])
  have hkp : 0 < k*p := Nat.mul_pos hk hp
  have hw (i : ℕ) : 0 ≤ w i := by dsimp [w]; positivity
  have hanti : Antitone w := by
    intro i j hij
    dsimp [w]
    apply one_div_le_one_div_of_le (by positivity)
    gcongr
  have hh := pm_abs_sum_mul_antitone_le a w p (by positivity) hw hanti
    (fun K _ => hprefix K)
  have he : (∑ r : Fin p, (g (k*p+r)-m)/
      (((k*p+r : ℕ) : ℝ)*(((k*p+r : ℕ) : ℝ)+1))) =
        ∑ i ∈ Finset.range p, w i*a i := by
    trans ∑ r : Fin p, w r*a r
    · apply Finset.sum_congr rfl
      intro r hr
      dsimp [w,a]
      ring
    · exact Fin.sum_univ_eq_sum_range (fun i => w i*a i) p
  rw [he]
  simpa only [w, add_zero, mul_one_div] using hh

private theorem pm_floor_dilation_centered_covariance_le (f g : ℕ → ℝ)
    {A C B m : ℝ} (hA : ∀ N, ‖f N‖ ≤ A) (hC : ∀ N, ‖g N‖ ≤ C)
    (hf0 : f 0 = 0) (hB : ∀ K, |∑ i ∈ Finset.range K, (g i-m)| ≤ B)
    {p : ℕ} (hp : 0 < p) :
    ‖(p : ℝ)*(∑' N : ℕ, f (N/p)*(g N-m)/((N : ℝ)*((N : ℝ)+1)))‖ ≤
      (A*(2*B)*(∑' k : ℕ, 1/(k : ℝ)^2))/(p : ℝ) := by
  have hA0 : 0 ≤ A := (norm_nonneg _).trans (hA 0)
  have hB0 : 0 ≤ B := by simpa using hB 0
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp
  let block (k : ℕ) : ℝ := ∑ r : Fin p,
    (g (k*p+r)-m)/(((k*p+r : ℕ) : ℝ)*(((k*p+r : ℕ) : ℝ)+1))
  let H (k : ℕ) : ℝ := f k*block k
  let major (k : ℕ) : ℝ := (A*(2*B)/(p : ℝ)^2)*(1/(k : ℝ)^2)
  have hmajor : Summable major :=
    (Real.summable_one_div_nat_pow.mpr (by norm_num : 1 < 2)).mul_left _
  have hpoint (k : ℕ) : ‖H k‖ ≤ major k := by
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · simp [H, hf0, major]
    have hkR : (0 : ℝ) < k := by exact_mod_cast hk
    have hkp : (0 : ℝ) < (k*p : ℕ) := by exact_mod_cast Nat.mul_pos hk hp
    have hblock := pm_centered_reciprocal_block_le g hB hp hk
    change ‖f k*block k‖ ≤ _
    rw [norm_mul]
    calc
      _ ≤ A*(2*B/(((k*p : ℕ) : ℝ)*(((k*p : ℕ) : ℝ)+1))) :=
        mul_le_mul (hA k) hblock (abs_nonneg _) hA0
      _ = A*(2*B)/(((k*p : ℕ) : ℝ)*(((k*p : ℕ) : ℝ)+1)) := by ring
      _ ≤ A*(2*B)/((k*p : ℕ) : ℝ)^2 := by
        apply div_le_div_of_nonneg_left (by positivity) (by positivity)
        nlinarith
      _ = major k := by dsimp [major]; push_cast; field_simp
  have hH : Summable H := Summable.of_norm_bounded hmajor hpoint
  have hsource : Summable (fun N : ℕ =>
      f (N/p)*(g N-m)/((N : ℝ)*((N : ℝ)+1))) := by
    apply pm_bounded_reciprocal_summable (B := A*(C+‖m‖))
    intro N
    rw [norm_mul]
    exact mul_le_mul (hA _) ((norm_sub_le _ _).trans (by linarith [hC N]))
      (norm_nonneg _) hA0
  have hrep : (∑' N : ℕ, f (N/p)*(g N-m)/((N : ℝ)*((N : ℝ)+1))) = ∑' k, H k := by
    rw [pm_tsum_nat_blocks _ hsource hp]
    apply tsum_congr
    intro k
    dsimp only [H, block]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro r hr
    letI : NeZero p := ⟨hp.ne'⟩
    have hd : (k*p+r.val)/p = k :=
      congrArg Prod.fst ((Nat.divModEquiv p).apply_symm_apply (k,r))
    rw [hd]
    ring
  rw [hrep, norm_mul, Real.norm_eq_abs, abs_of_pos hpR]
  calc
    _ ≤ (p : ℝ)*(∑' k, ‖H k‖) :=
      mul_le_mul_of_nonneg_left (norm_tsum_le_tsum_norm hH.norm) hpR.le
    _ ≤ (p : ℝ)*(∑' k, major k) :=
      mul_le_mul_of_nonneg_left (Summable.tsum_le_tsum hpoint hH.norm hmajor) hpR.le
    _ = _ := by
      simp only [major, tsum_mul_left]
      field_simp

theorem tendsto_pm_floor_dilation_covariance (f g : ℕ → ℝ)
    {A C B m : ℝ} (hA : ∀ N, ‖f N‖ ≤ A) (hC : ∀ N, ‖g N‖ ≤ C)
    (hf0 : f 0 = 0) (hB : ∀ K, |∑ i ∈ Finset.range K, (g i-m)| ≤ B) :
    Tendsto (fun p : ℕ => (p : ℝ)*
      ∑' N : ℕ, f (N/p)*g N/((N : ℝ)*((N : ℝ)+1))) atTop
        (𝓝 (m*∑' N : ℕ, f N/((N : ℝ)*((N : ℝ)+1)))) := by
  have hA0 : 0 ≤ A := (norm_nonneg _).trans (hA 0)
  have hzero : Tendsto (fun p : ℕ => (p : ℝ)*
      ∑' N : ℕ, f (N/p)*(g N-m)/((N : ℝ)*((N : ℝ)+1))) atTop (𝓝 0) := by
    apply squeeze_zero_norm' _
      (show Tendsto (fun p : ℕ =>
        (A*(2*B)*(∑' k : ℕ, 1/(k : ℝ)^2))/(p : ℝ)) atTop (𝓝 0) from
          tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop)
    filter_upwards [eventually_ge_atTop 1] with p hp
    exact pm_floor_dilation_centered_covariance_le f g hA hC hf0 hB (by omega)
  have hdiff : Tendsto (fun p : ℕ =>
      (p : ℝ)*(∑' N : ℕ, f (N/p)*g N/((N : ℝ)*((N : ℝ)+1))) -
        m*(∑' N : ℕ, f N/((N : ℝ)*((N : ℝ)+1)))) atTop (𝓝 0) := by
    apply hzero.congr'
    filter_upwards [eventually_ge_atTop 1] with p hp
    have hp' : 0 < p := by omega
    have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast hp'.ne'
    have hfg : Summable (fun N : ℕ => f (N/p)*g N/((N : ℝ)*((N : ℝ)+1))) := by
      apply pm_bounded_reciprocal_summable (B := A*C)
      intro N
      rw [norm_mul]
      exact mul_le_mul (hA _) (hC _) (norm_nonneg _) hA0
    have hff := pm_bounded_reciprocal_summable (fun N => f (N/p)) (fun N => hA (N/p))
    have he (N : ℕ) : f (N/p)*(g N-m)/((N : ℝ)*((N : ℝ)+1)) =
        f (N/p)*g N/((N : ℝ)*((N : ℝ)+1))-
          m*(f (N/p)/((N : ℝ)*((N : ℝ)+1))) := by ring
    rw [tsum_congr he, hfg.tsum_sub (hff.mul_left m), tsum_mul_left,
      pm_tsum_floor_dilation f hA hf0 hp']
    field_simp
  have h := hdiff.add_const (m*∑' N : ℕ, f N/((N : ℝ)*((N : ℝ)+1)))
  simpa only [sub_add_cancel, zero_add] using h

theorem pmRamanujanPrimitive_centered_prefix_bound {q : ℕ} (hq : 1 < q) :
    ∃ B : ℝ, ∀ K : ℕ,
      |∑ i ∈ Finset.range K, ((pmRamanujanPrimitive q i).re+(q.totient : ℝ)/2)| ≤ B := by
  let f : ℕ → ℂ := fun N => pmRamanujanPrimitive q N+(q.totient : ℂ)/2
  have hper : Function.Periodic f q := by
    intro N
    dsimp only [f]
    rw [pmRamanujanPrimitive_periodic hq]
  have hz : ∑ N ∈ Finset.range q, f N = 0 := by
    dsimp only [f]
    rw [Finset.sum_add_distrib, pmRamanujanPrimitive_range_sum q q,
      pmRamanujanPrimitive_period_mean hq, pmRamanujanPrimitive_period_sum hq]
    simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    ring
  obtain ⟨B,hB⟩ := DeletionChronologicalLimit.periodic_zero_sum_prefix_bound
    (by omega : 0 < q) hper hz
  refine ⟨B,fun K => ?_⟩
  have h := (Complex.abs_re_le_norm (∑ i ∈ Finset.range K, f i)).trans (hB K)
  simpa [f, Complex.div_re] using h

theorem pmRamanujanPrimitiveGram_pos {q : ℕ} (hq : 1 < q) :
    0 < pmRamanujanPrimitiveGram q q := by
  have hqR : (0 : ℝ) < q := by exact_mod_cast (by omega : 0 < q)
  have hphi : (0 : ℝ) < q.totient := by
    exact_mod_cast (Nat.totient_pos.mpr (by omega : 0 < q))
  have hs : (∑ N ∈ Finset.Icc 1 q, (pmRamanujanPrimitive q N).re) =
      -(q : ℝ)*(q.totient : ℝ)/2 := by
    have h := congrArg Complex.re (pmRamanujanPrimitive_period_mean hq)
    simpa [Complex.mul_re, Complex.div_re] using h
  have hsne : (∑ N ∈ Finset.Icc 1 q, (pmRamanujanPrimitive q N).re) ≠ 0 := by
    rw [hs]
    have : (0 : ℝ) < (q : ℝ)*(q.totient : ℝ)/2 := by positivity
    linarith
  obtain ⟨N,hN,hne⟩ := Finset.exists_ne_zero_of_sum_ne_zero hsne
  apply (summable_pmRamanujanPrimitiveGramTerm hq hq).tsum_pos (i := N)
  · intro n
    dsimp only [pmRamanujanPrimitiveGramTerm]
    exact div_nonneg (mul_self_nonneg _) (by positivity)
  · dsimp only [pmRamanujanPrimitiveGramTerm]
    have hN0 : (0 : ℝ) < N := by
      exact_mod_cast (by have := (Finset.mem_Icc.mp hN).1; omega : 0 < N)
    exact div_pos (mul_self_pos.mpr hne) (by positivity)

theorem tendsto_pmRamanujanPrimitiveGram_prime_mul {q r : ℕ} (hq : 1 < q)
    (hr : 1 < r) :
    Tendsto (fun p : {p : ℕ // p.Prime} =>
      pmRamanujanPrimitiveGram ((p : ℕ)*q) r) atTop
        (𝓝 ((r.totient : ℝ)*vonMangoldt q/2-pmRamanujanPrimitiveGram q r)) := by
  let f : ℕ → ℝ := fun N => (pmRamanujanPrimitive q N).re
  let g : ℕ → ℝ := fun N => (pmRamanujanPrimitive r N).re
  have hF (N : ℕ) : ‖f N‖ ≤ pmRamanujanPrimitiveBound q :=
    (Complex.abs_re_le_norm _).trans (norm_pmRamanujanPrimitive_le hq N)
  have hG (N : ℕ) : ‖g N‖ ≤ pmRamanujanPrimitiveBound r :=
    (Complex.abs_re_le_norm _).trans (norm_pmRamanujanPrimitive_le hr N)
  obtain ⟨B,hB⟩ := pmRamanujanPrimitive_centered_prefix_bound hr
  have hB' (K : ℕ) : |∑ i ∈ Finset.range K, (g i-(-(r.totient : ℝ)/2))| ≤ B := by
    simpa only [g, neg_div, sub_neg_eq_add] using hB K
  have hf0 : f 0 = 0 := by simp [f,pmRamanujanPrimitive]
  have hlim := tendsto_pm_floor_dilation_covariance f g hF hG hf0 hB'
  have hmoment : (∑' N : ℕ, f N/((N : ℝ)*((N : ℝ)+1))) = -vonMangoldt q :=
    (hasSum_pmRamanujanPrimitive_reciprocal hq).tsum_eq
  rw [hmoment] at hlim
  have hcoe : Tendsto (fun p : {p : ℕ // p.Prime} => (p : ℕ)) atTop atTop := by
    apply tendsto_atTop.2
    intro N
    obtain ⟨p,hNp,hp⟩ := Nat.exists_infinite_primes N
    letI : Nonempty {p : ℕ // p.Prime} := ⟨⟨p,hp⟩⟩
    exact eventually_atTop.2 ⟨⟨p,hp⟩,fun s hs => hNp.trans hs⟩
  have h := (hlim.comp hcoe).sub_const (pmRamanujanPrimitiveGram q r)
  have hv : -(r.totient : ℝ)/2 * -vonMangoldt q =
      (r.totient : ℝ)*vonMangoldt q/2 := by ring
  rw [hv] at h
  apply h.congr'
  filter_upwards [hcoe.eventually (eventually_gt_atTop q)] with p hpq
  have hpnq : ¬ (p : ℕ) ∣ q := by
    intro hd
    have := Nat.le_of_dvd (by omega : 0 < q) hd
    omega
  have hterm (N : ℕ) : pmRamanujanPrimitiveGramTerm ((p : ℕ)*q) r N =
      ((p : ℕ) : ℝ)*(f (N/(p : ℕ))*g N/((N : ℝ)*((N : ℝ)+1)))-
        pmRamanujanPrimitiveGramTerm q r N := by
    simp only [pmRamanujanPrimitiveGramTerm, pmRamanujanPrimitive_prime_mul p.property hpnq,
      Complex.sub_re, Complex.mul_re, Complex.natCast_re, Complex.natCast_im,
      zero_mul, sub_zero, f,g]
    ring
  have hsum : Summable (fun N : ℕ =>
      f (N/(p : ℕ))*g N/((N : ℝ)*((N : ℝ)+1))) := by
    apply pm_bounded_reciprocal_summable (B := pmRamanujanPrimitiveBound q*pmRamanujanPrimitiveBound r)
    intro N
    rw [norm_mul]
    exact mul_le_mul (hF _) (hG _) (norm_nonneg _)
      (Finset.sum_nonneg (fun _ _ => norm_nonneg _))
  change _ = ∑' N : ℕ, pmRamanujanPrimitiveGramTerm ((p : ℕ)*q) r N
  rw [tsum_congr hterm, (hsum.mul_left _).tsum_sub
    (summable_pmRamanujanPrimitiveGramTerm hq hr), tsum_mul_left]
  rfl

theorem eventually_pmRamanujanPrimitiveGram_prime_mul_self_neg {q : ℕ}
    (hq : 1 < q) (hqp : ¬ IsPrimePow q) :
    ∀ᶠ p : {p : ℕ // p.Prime} in atTop,
      pmRamanujanPrimitiveGram ((p : ℕ)*q) q < 0 := by
  have h := tendsto_pmRamanujanPrimitiveGram_prime_mul hq hq
  rw [vonMangoldt_eq_zero_iff.mpr hqp, mul_zero, zero_div, zero_sub] at h
  exact h.eventually (gt_mem_nhds (by linarith [pmRamanujanPrimitiveGram_pos hq]))

theorem eventually_pmPowerDampedRamanujan_prime_pair_cross_pos {ε : ℝ}
    (hε : 0 < ε) {q : ℕ} (hq : 1 < q) (hsq : Squarefree q) (hqp : ¬ IsPrimePow q) :
    ∀ᶠ p : {p : ℕ // p.Prime} in atTop,
      0 < (pmPowerDampedRamanujanWeight ε q).re *
        (pmPowerDampedRamanujanWeight ε ((p : ℕ)*q)).re *
          pmRamanujanPrimitiveGram ((p : ℕ)*q) q := by
  have haq : (pmPowerDampedRamanujanWeight ε q).re ≠ 0 := by
    rw [pmPowerDampedRamanujanWeight_eq_ofReal hε, Complex.ofReal_re]
    have hmu : (moebius q : ℝ) ≠ 0 := by
      exact_mod_cast (ArithmeticFunction.moebius_ne_zero_iff_squarefree.mpr hsq)
    exact div_ne_zero (mul_ne_zero (pmPowerDampedDivisorDensity_re_pos hε).ne' hmu)
      (pmPowerDampedRamanujanDenominator_pos hε q).ne'
  have hnd : ∀ᶠ p : {p : ℕ // p.Prime} in atTop, ¬ (p : ℕ) ∣ q := by
    obtain ⟨P,hP,hPrime⟩ := Nat.exists_infinite_primes (q+1)
    letI : Nonempty {p : ℕ // p.Prime} := ⟨⟨P,hPrime⟩⟩
    apply eventually_atTop.2
    refine ⟨⟨P,hPrime⟩,fun p hpp => ?_⟩
    change P ≤ (p : ℕ) at hpp
    exact Nat.not_dvd_of_pos_of_lt (by omega) (by omega)
  filter_upwards [eventually_pmRamanujanPrimitiveGram_prime_mul_self_neg hq hqp,hnd]
    with p hneg hpq
  have hb : 0 < ((p : ℕ) : ℝ)^(1+ε)-1 := by
    apply sub_pos.mpr
    exact Real.one_lt_rpow (by exact_mod_cast p.property.one_lt) (by linarith)
  have he : (pmPowerDampedRamanujanWeight ε ((p : ℕ)*q)).re =
      -(pmPowerDampedRamanujanWeight ε q).re / (((p : ℕ) : ℝ)^(1+ε)-1) := by
    have h := congrArg Complex.re (pmPowerDampedRamanujanWeight_prime_mul hε p.property hpq)
    simpa only [Complex.div_ofReal_re, Complex.neg_re] using h
  have ha : (pmPowerDampedRamanujanWeight ε q).re *
      (pmPowerDampedRamanujanWeight ε ((p : ℕ)*q)).re < 0 := by
    rw [he]
    have he' : (pmPowerDampedRamanujanWeight ε q).re *
        (-(pmPowerDampedRamanujanWeight ε q).re / (((p : ℕ) : ℝ)^(1+ε)-1)) =
      -((pmPowerDampedRamanujanWeight ε q).re*(pmPowerDampedRamanujanWeight ε q).re/
        (((p : ℕ) : ℝ)^(1+ε)-1)) := by ring
    rw [he']
    have := div_pos (mul_self_pos.mpr haq) hb
    linarith
  exact mul_pos_of_neg_of_neg ha hneg

end RHTower
