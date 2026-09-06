import GaloisForLFunctions.RHTower.EulerDeletionModulusFirstCoefficient
import Mathlib.Data.Nat.Prime.Infinite

/-!
# Global classes of the actual arithmetic minimum profiles

The literal remainder has a nonzero leading coefficient before a zeta zero is
selected. Products of two distinct primes supply cofinally many positive Möbius
values. Thus every power profile below the exact decay exponent attains a negative
minimum, while every profile above it is unbounded below. At critical-line zeros,
the strict arithmetic undershoot also forces minimum attainment at the boundary.

Consequently the two global labels have prescribed finite/nonattained patterns
in either open half-strip, including at nonzeros. At a strip zero both labels are
positive exactly on the critical line. These facts do not exclude off-line zeros.
-/

noncomputable section
open scoped BigOperators ArithmeticFunction.Moebius
open Filter Topology
namespace RHTower.DeletionMixedRefinement

/-- The positive size of the leading signed profile coefficient. -/
def minimumTailCoefficient (s:ℂ) : ℝ :=
  (∑' n:ℕ+, (n:ℝ)^(-2*s.re-1))/12*((star s+1)⁻¹).re

private def profileTail (s:ℂ) (p:ℕ) : ℝ :=
  (infiniteRemainder s p/minimumNormalization s).re*(p:ℝ)^(2*s.re)

private theorem inverse_successor_re_pos {s:ℂ} (hs:0 < s.re) : 0 < ((star s+1)⁻¹).re := by
  rw [Complex.inv_re]
  apply div_pos
  · simp; linarith
  · rw [Complex.normSq_apply]
    have he : (star s+1).re = s.re+1 := by simp
    rw [he]
    nlinarith [sq_nonneg (star s+1).im]

/-- The leading profile coefficient is strictly positive throughout the positive half-plane. -/
theorem minimumTailCoefficient_pos {s:ℂ} (hs:0 < s.re) : 0  <  minimumTailCoefficient s := by
  have hsum : Summable (fun n:ℕ+ => (n:ℝ)^(-2*s.re-1)) :=
    (Real.summable_nat_rpow.mpr (by linarith)).subtype _
  have hS : 0 < (∑' n:ℕ+, (n:ℝ)^(-2*s.re-1)) := by
    have h := hsum.le_tsum (1:ℕ+) (fun _ _ => Real.rpow_nonneg (by positivity) _)
    norm_num only [PNat.val_ofNat, Nat.cast_one, Real.one_rpow] at h
    linarith
  exact mul_pos (div_pos hS (by norm_num)) (inverse_successor_re_pos hs)

private theorem tendsto_profileTail {s:ℂ} (hs:0 < s.re) (hs1:s≠1) :
    Tendsto (profileTail s) atTop (𝓝 (-minimumTailCoefficient s)) := by
  have hu : star s ≠ 0 := by intro h; have := congrArg Complex.re h; simp at this; linarith
  have hv : star s+1 ≠ 0 := by intro h; have := congrArg Complex.re h; simp at this; linarith
  have ht := Complex.continuous_re.continuousAt.tendsto.comp
    ((tendsto_infiniteRemainder_scaled hs hs1).div_const (minimumNormalization s))
  have he : ((-star s/12)*(↑(∑' n:ℕ+, (n:ℝ)^(-2*s.re-1)):ℂ))/minimumNormalization s =
      -(↑((∑' n:ℕ+, (n:ℝ)^(-2*s.re-1))/12):ℂ)*(star s+1)⁻¹ := by
    have hgeneral (u C:ℂ) (hu:u≠0) (hv:u+1≠0) :
        (-u/12*C)/(u*(u+1)) = -(C/12)*(u+1)⁻¹ := by
      field_simp
    simpa only [minimumNormalization, Complex.ofReal_div, Complex.ofReal_ofNat] using
      hgeneral (star s) (↑(∑' n:ℕ+, (n:ℝ)^(-2*s.re-1))) hu hv
  rw [he] at ht
  have hreal : (-(↑((∑' n:ℕ+, (n:ℝ)^(-2*s.re-1))/12):ℂ)*(star s+1)⁻¹).re =
      -minimumTailCoefficient s := by
    rw [neg_mul, Complex.neg_re, Complex.re_ofReal_mul]
    rfl
  rw [hreal] at ht
  apply ht.congr
  intro p
  dsimp [profileTail]
  have hmul : infiniteRemainder s p*(((p:ℝ)^(2*s.re):ℝ):ℂ)/minimumNormalization s =
      (infiniteRemainder s p/minimumNormalization s)*(((p:ℝ)^(2*s.re):ℝ):ℂ) := by ring
  rw [hmul]
  simp

private theorem minimumProfile_eq_tail (s:ℂ) (a:ℝ) {p:ℕ} (hp:0 < p) :
    minimumProfile s a p = (μ p:ℝ)*(p:ℝ)^(a-2*s.re)*profileTail s p := by
  have hpp : (0:ℝ) < p := by exact_mod_cast hp
  have he : minimumBalanceTerm s p =
      (μ p:ℂ)*(infiniteRemainder s p/minimumNormalization s)/(p:ℂ) := by
    dsimp [minimumBalanceTerm]
    ring
  have hmu : (μ p:ℂ) = ((μ p:ℝ):ℂ) := by simp
  rw [minimumProfile, he, hmu, Complex.div_natCast_re, Complex.re_ofReal_mul]
  dsimp [profileTail]
  have hpow : (p:ℝ)^(a+1)/(p:ℝ) = (p:ℝ)^(a-2*s.re)*(p:ℝ)^(2*s.re) := by
    rw [← Real.rpow_add hpp, show a-2*s.re+2*s.re = a by ring,
      Real.rpow_add hpp, Real.rpow_one]
    field_simp
  linear_combination (μ p:ℝ)*(infiniteRemainder s p/minimumNormalization s).re*hpow

private theorem exists_moebius_one_ge (N:ℕ) : ∃ p:ℕ, N≤p ∧ 0 < p ∧ μ p=1 := by
  obtain ⟨q,hq,hprime⟩ := Nat.exists_infinite_primes (max N 3)
  have hc : Nat.Coprime 2 q := (Nat.coprime_primes Nat.prime_two hprime).mpr (by omega)
  refine ⟨2*q, by omega, by omega, ?_⟩
  rw [ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime hc,
    ArithmeticFunction.moebius_apply_prime Nat.prime_two,
    ArithmeticFunction.moebius_apply_prime hprime]
  ring

private def positiveMoebiusSequence (N:ℕ) : ℕ := (exists_moebius_one_ge N).choose

private theorem positiveMoebiusSequence_spec (N:ℕ) :
    N≤positiveMoebiusSequence N ∧ 0 < positiveMoebiusSequence N ∧ μ (positiveMoebiusSequence N)=1 :=
  (exists_moebius_one_ge N).choose_spec

private theorem positiveMoebiusSequence_tendsto : Tendsto positiveMoebiusSequence atTop atTop :=
  tendsto_atTop_mono (fun N => (positiveMoebiusSequence_spec N).1) tendsto_id

/-- Every positive-half-plane parameter has negative profile entries, without a zero assumption. -/
theorem exists_minimumProfile_neg {s:ℂ} (hs:0 < s.re) (hs1:s≠1) (a:ℝ) :
    ∃ p:ℕ, 0 < p ∧ minimumProfile s a p < 0 := by
  have ht := (tendsto_profileTail hs hs1).comp positiveMoebiusSequence_tendsto
  have hn := (tendsto_order.mp ht).2 0 (neg_neg_of_pos (minimumTailCoefficient_pos hs))
  obtain ⟨N,hN⟩ := eventually_atTop.mp hn
  let p := positiveMoebiusSequence N
  have hp := (positiveMoebiusSequence_spec N).2
  refine ⟨p,hp.1, ?_⟩
  rw [minimumProfile_eq_tail s a hp.1, hp.2, Int.cast_one, one_mul]
  exact mul_neg_of_pos_of_neg (Real.rpow_pos_of_pos (by exact_mod_cast hp.1) _) (hN N le_rfl)

/-- Every profile below its exact decay exponent attains a negative global minimum. -/
theorem exists_minimumProfile_minimum_of_lt {s:ℂ} (hs:0 < s.re) (hs1:s≠1)
    {a:ℝ} (ha:a < 2*s.re) : ∃ p, HasNegativeMinimum (minimumProfile s a) p :=
  exists_negativeMinimum_of_tendsto_zero (tendsto_minimumProfile hs hs1 ha)
    (exists_minimumProfile_neg hs hs1 a)

/-- Above the exact decay exponent, the actual profile is unbounded below along squarefree moduli. -/
theorem minimumProfile_unbounded_below {s:ℂ} (hs:0 < s.re) (hs1:s≠1)
    {a:ℝ} (ha:2*s.re < a) (b:ℝ) : ∃ p:ℕ, 0 < p ∧ minimumProfile s a p < b := by
  have hpow := (tendsto_rpow_atTop (by linarith : 0 < a-2*s.re)).comp
    ((tendsto_natCast_atTop_atTop (R:=ℝ)).comp positiveMoebiusSequence_tendsto)
  have ht := hpow.atTop_mul_neg (neg_neg_of_pos (minimumTailCoefficient_pos hs))
    ((tendsto_profileTail hs hs1).comp positiveMoebiusSequence_tendsto)
  have he : (fun N:ℕ => minimumProfile s a (positiveMoebiusSequence N)) =
      (fun N:ℕ => (positiveMoebiusSequence N:ℝ)^(a-2*s.re)*profileTail s (positiveMoebiusSequence N)) := by
    funext N
    rw [minimumProfile_eq_tail s a (positiveMoebiusSequence_spec N).2.1,
      (positiveMoebiusSequence_spec N).2.2, Int.cast_one, one_mul]
  simp only [Function.comp_apply] at ht
  rw [← he] at ht
  obtain ⟨N,hN⟩ := eventually_atTop.mp (ht.eventually (eventually_lt_atBot b))
  exact ⟨positiveMoebiusSequence N, (positiveMoebiusSequence_spec N).2.1, hN N le_rfl⟩

/-- No negative global minimum can be attained above the exact decay exponent. -/
theorem not_minimumProfile_minimum_of_gt {s:ℂ} (hs:0 < s.re) (hs1:s≠1)
    {a:ℝ} (ha:2*s.re < a) : ¬∃ p, HasNegativeMinimum (minimumProfile s a) p := by
  rintro ⟨p,hp⟩
  obtain ⟨q,hq,hlt⟩ := minimumProfile_unbounded_below hs hs1 ha (minimumProfile s a p)
  exact (not_lt_of_ge (hp.2.2 q hq)) hlt

private theorem tailCoefficient_on_line {s:ℂ} (hs:s.re=1/2) :
    minimumTailCoefficient s = reciprocalSquareMass/(8*(s.im^2+9/4)) := by
  have hS : (∑' n:ℕ+, (n:ℝ)^(-2*s.re-1)) = reciprocalSquareMass := by
    apply tsum_congr
    intro n
    rw [hs, show -2*(1/2:ℝ)-1 = -2 by norm_num, Real.rpow_neg (by positivity),
      Real.rpow_two, one_div]
  rw [minimumTailCoefficient, hS, Complex.inv_re, Complex.normSq_apply]
  simp only [Complex.add_re, Complex.add_im, Complex.star_def, Complex.conj_re,
    Complex.conj_im, Complex.one_re, Complex.one_im, hs]
  field_simp
  ring

private theorem negative_minimum_of_eventually_above {f:ℕ→ℝ} {p:ℕ}
    (hp:0 < p) (hfp:f p < 0) (ht:∀ᶠ q:ℕ in atTop, f p < f q) :
    ∃ q, HasNegativeMinimum f q := by
  obtain ⟨N,hN⟩ := eventually_atTop.mp ht
  let K := max N p
  have hm : p ∈ Finset.Icc 1 K := by simp only [Finset.mem_Icc]; dsimp [K]; omega
  obtain ⟨q,hq,hmin⟩ := Finset.exists_min_image (Finset.Icc 1 K) f ⟨p,hm⟩
  refine ⟨q,(Finset.mem_Icc.mp hq).1,(hmin p hm).trans_lt hfp,?_⟩
  intro r hr
  by_cases hrK:r≤K
  · exact hmin r (Finset.mem_Icc.mpr ⟨hr,hrK⟩)
  · have hrN:N≤r := by dsimp [K] at hrK; omega
    exact (hmin p hm).trans (hN r hrN).le

/-- At every critical-line zero the first arithmetic profile attains a negative global minimum. -/
theorem rightMinimum_attained_on_line {s:ℂ} (hs:s.re=1/2) (hz:riemannZeta s=0) :
    ∃ p, HasNegativeMinimum (rightMinimumProfile s) p := by
  have hs0:0 < s.re := by linarith
  have hs1:s≠1 := by intro h; rw [h] at hs; norm_num at hs
  obtain ⟨p,hp,hlt⟩ := exists_rightMinimumProfile_below_critical_boundary hs hz
  rw [neg_div, ← tailCoefficient_on_line hs] at hlt
  have hc := minimumTailCoefficient_pos hs0
  apply negative_minimum_of_eventually_above hp (hlt.trans (neg_neg_of_pos hc))
  have ht := (tendsto_profileTail hs0 hs1).abs.neg
  simp only [abs_neg, abs_of_pos hc] at ht
  have hb := (tendsto_order.mp ht).1 (rightMinimumProfile s p) hlt
  filter_upwards [hb, eventually_ge_atTop 1] with q hq hq1
  refine hq.trans_le ?_
  rw [rightMinimumProfile, minimumProfile_eq_tail s 1 (by omega), hs,
    show (1:ℝ)-2*(1/2)=0 by norm_num, Real.rpow_zero, mul_one]
  have hm : |(μ q:ℝ)|≤1 := by exact_mod_cast (ArithmeticFunction.abs_moebius_le_one (n:=q))
  have hh : |(μ q:ℝ)*profileTail s q|≤|profileTail s q| := by
    rw [abs_mul]
    exact mul_le_of_le_one_left (abs_nonneg _) hm
  exact (neg_le_neg hh).trans (neg_abs_le _)

private theorem class_pos_of_minimum {f:ℕ→ℝ} {p:ℕ}
    (hc:NegativeMinimumClass f p) (he:∃q,HasNegativeMinimum f q) : 0 < p := by
  by_contra h
  have hp:p=0 := by omega
  rw [hp, NegativeMinimumClass, if_pos rfl] at hc
  exact hc he

private theorem class_zero_of_no_minimum {f:ℕ→ℝ} {p:ℕ}
    (hc:NegativeMinimumClass f p) (he:¬∃q,HasNegativeMinimum f q) : p=0 := by
  by_contra hp
  rw [NegativeMinimumClass, if_neg hp] at hc
  exact he ⟨p,hc.1⟩

/-- Every strict-right parameter has a finite first label and a zero second label, even at nonzeros. -/
theorem arithmeticMinimumClass_strict_right {s:ℂ} (hs:(1/2:ℝ) < s.re) (hs1:s≠1)
    {ij:ℕ×ℕ} (hc:ArithmeticMinimumClass s ij) : 0 < ij.1 ∧ ij.2=0 := by
  have hs0:0 < s.re := by linarith
  exact ⟨class_pos_of_minimum hc.1 (exists_minimumProfile_minimum_of_lt hs0 hs1 (by linarith)),
    class_zero_of_no_minimum hc.2 (not_minimumProfile_minimum_of_gt hs0 hs1 (by linarith))⟩

/-- Every strict-left positive parameter has a zero first label and a finite second label. -/
theorem arithmeticMinimumClass_strict_left {s:ℂ} (hs:0 < s.re) (hs':s.re < (1/2:ℝ))
    {ij:ℕ×ℕ} (hc:ArithmeticMinimumClass s ij) : ij.1=0 ∧ 0 < ij.2 := by
  have hs1:s≠1 := by intro h; rw [h] at hs'; norm_num at hs'
  exact ⟨class_zero_of_no_minimum hc.1 (not_minimumProfile_minimum_of_gt hs hs1 (by linarith)),
    class_pos_of_minimum hc.2 (exists_minimumProfile_minimum_of_lt hs hs1 (by linarith))⟩

/-- Critical-line zeros have equal, strictly positive least-minimum labels. -/
theorem arithmeticMinimumClass_on_line {s:ℂ} (hs:s.re=1/2) (hz:riemannZeta s=0)
    {ij:ℕ×ℕ} (hc:ArithmeticMinimumClass s ij) : 0 < ij.1 ∧ ij.1=ij.2 :=
  ⟨class_pos_of_minimum hc.1 (rightMinimum_attained_on_line hs hz),
    arithmeticMinimumClass_labels_eq_on_line hs hc⟩

/-- The class with neither minimum attained contains no nontrivial zero in the open strip. -/
theorem not_arithmeticMinimumClass_zero_zero_at_zero {s:ℂ}
    (hs:0 < s.re) (hs':s.re < 1) (hz:riemannZeta s=0) : ¬ArithmeticMinimumClass s (0,0) := by
  intro hc
  have hline := re_eq_half_of_arithmeticMinimumClass_zero_zero hs hs' hz hc
  have hpos := (arithmeticMinimumClass_on_line hline hz hc).1
  exact (Nat.lt_irrefl 0) hpos

/-- At a strip zero, two attained negative minima characterize the critical line exactly. -/
theorem arithmeticMinimumClass_both_positive_iff {s:ℂ}
    (hs:0 < s.re) (hs':s.re < 1) (hz:riemannZeta s=0)
    {ij:ℕ×ℕ} (hc:ArithmeticMinimumClass s ij) :
    (0 < ij.1 ∧ 0 < ij.2) ↔ s.re=1/2 := by
  constructor
  · intro hp
    rcases lt_trichotomy s.re (1/2) with hl | he | hr
    · have h := (arithmeticMinimumClass_strict_left hs hl hc).1
      omega
    · exact he
    · have hs1:s≠1 := by intro h; rw [h] at hs'; norm_num at hs'
      have h := (arithmeticMinimumClass_strict_right hr hs1 hc).2
      omega
  · intro hline
    obtain ⟨hp,he⟩ := arithmeticMinimumClass_on_line hline hz hc
    exact ⟨hp,he ▸ hp⟩

end RHTower.DeletionMixedRefinement
