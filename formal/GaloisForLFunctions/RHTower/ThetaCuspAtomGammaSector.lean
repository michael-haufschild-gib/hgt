import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

open scoped BigOperators Topology
open Filter

/-!
# A sector law for the first theta atom's Gamma pair

The Gamma expression associated on paper with the first theta source atom is
strictly in the right half-plane throughout the open spectral strip. The proof
uses Euler's finite Gamma products. Their denominator angles telescope to a
bound strictly below pi/2; a closed sector estimate survives the Gamma limit.

This leaf proves the special-function inequality. It does not identify an
integral transform, extend a Weil identity to a noncompact test, or prove the
sign of a mixed theta-source packet.
-/

namespace RHTower


private noncomputable def q (b c a : ℝ) : ℂ :=
  ((a-c : ℝ) + (b:ℂ)*Complex.I) * ((a+c : ℝ) - (b:ℂ)*Complex.I)
private noncomputable def f (b t : ℝ) : ℝ := Real.arctan (b/t)
private noncomputable def d (b c a : ℝ) : ℝ := f b (a-c) - f b (a+c)

private lemma arg_eq_arctan {z : ℂ} (hz : 0 < z.re) :
    z.arg = Real.arctan (z.im/z.re) := by
  rw [← Complex.tan_arg]
  exact (Real.arctan_tan
    (Complex.neg_pi_div_two_lt_arg_iff.mpr (Or.inl hz))
    (Complex.arg_lt_pi_div_two_iff.mpr (Or.inl hz))).symm

private lemma f_nonneg {b t : ℝ} (hb : 0 ≤ b) (ht : 0 < t) : 0 ≤ f b t :=
  Real.arctan_nonneg.mpr (div_nonneg hb ht.le)

private lemma f_antitone {b s t : ℝ} (hb : 0 ≤ b) (hs : 0 < s) (hst : s ≤ t) :
    f b t ≤ f b s :=
  Real.arctan_le_arctan_iff.mpr (div_le_div_of_nonneg_left hb hs hst)

private lemma d_bounds {b c a : ℝ} (hb : 0 ≤ b) (hc : 0 ≤ c) (ha : c < a) :
    0 ≤ d b c a ∧ d b c a ≤ f b (a-c) := by
  constructor
  · exact sub_nonneg.mpr (f_antitone hb (by linarith) (by linarith))
  · exact sub_le_self _ (f_nonneg hb (by linarith))

private lemma q_arg {b c a : ℝ} (hb : 0 ≤ b) (hc : 0 ≤ c) (ha : c < a) :
    (q b c a).arg = d b c a := by
  have hp : 0 < a-c := sub_pos.mpr ha
  have hm : 0 < a+c := by linarith
  have h₁ : 0 < (((a-c:ℝ):ℂ)+(b:ℂ)*Complex.I).re := by simpa using hp
  have h₂ : 0 < (((a+c:ℝ):ℂ)-(b:ℂ)*Complex.I).re := by simpa using hm
  have hn₁ : (((a-c:ℝ):ℂ)+(b:ℂ)*Complex.I) ≠ 0 := by
    intro h; rw [h] at h₁; exact (lt_irrefl 0) h₁
  have hn₂ : (((a+c:ℝ):ℂ)-(b:ℂ)*Complex.I) ≠ 0 := by
    intro h; rw [h] at h₂; exact (lt_irrefl 0) h₂
  have he₁ : ((((a-c:ℝ):ℂ)+(b:ℂ)*Complex.I)).arg = f b (a-c) := by
    rw [arg_eq_arctan h₁]; simp [f]
  have he₂ : ((((a+c:ℝ):ℂ)-(b:ℂ)*Complex.I)).arg = -f b (a+c) := by
    rw [arg_eq_arctan h₂]; simp [f, neg_div]
  have hd := d_bounds hb hc ha
  have hlt := Real.arctan_lt_pi_div_two (b/(a-c))
  unfold q
  rw [Complex.arg_mul hn₁ hn₂, he₁, he₂]
  · rfl
  · rw [he₁, he₂]
    change d b c a ∈ Set.Ioc (-Real.pi) Real.pi
    constructor <;> dsimp [f] at * <;> linarith [Real.pi_pos]

private lemma q_ne_zero {b c a : ℝ} (hc : 0 ≤ c) (ha : c < a) : q b c a ≠ 0 := by
  apply mul_ne_zero
  · intro h
    have h' := congrArg Complex.re h
    simp at h'
    linarith
  · intro h
    have h' := congrArg Complex.re h
    simp at h'
    linarith

private noncomputable def a (n : ℕ) : ℝ := 2*n+1/2
private noncomputable def S (b c : ℝ) (N : ℕ) : ℝ :=
  ∑ n ∈ Finset.range N, d b c (a (n+1))
private noncomputable def P (b c : ℝ) (N : ℕ) : ℂ :=
  ∏ n ∈ Finset.range N, q b c (a (n+1))

private lemma a_pos {c : ℝ} (hc : c < 1/2) (n : ℕ) : c < a n := by
  dsimp [a]
  linarith [Nat.cast_nonneg (α := ℝ) n]

private lemma S_bounds {b c : ℝ} (hb : 0 ≤ b) (hc : 0 ≤ c) (hc' : c < 1/2) (N : ℕ) :
    0 ≤ S b c N ∧ S b c N ≤ f b (a 1-c) - f b (a (N+1)-c) := by
  induction N with
  | zero => simp [S]
  | succ N ih =>
    have had := a_pos hc' (N+1)
    have hd := d_bounds hb hc had
    have hg : a (N+1)+c ≤ a (N+1+1)-c := by
      simp [a]; linarith
    have hf := f_antitone hb (by linarith : 0 < a (N+1)+c) hg
    have he : S b c (N+1) = S b c N + d b c (a (N+1)) := by
      simp [S, Finset.sum_range_succ]
    rw [he]
    dsimp [d] at *
    constructor <;> linarith

private lemma S_lt {b c : ℝ} (hb : 0 ≤ b) (hc : 0 ≤ c) (hc' : c < 1/2) (N : ℕ) :
    S b c N < Real.pi/2 := by
  have hs := (S_bounds hb hc hc' N).2
  have hpos := f_nonneg hb (sub_pos.mpr (a_pos hc' (N+1)))
  have hlt := Real.arctan_lt_pi_div_two (b/(a 1-c))
  change f b (a 1-c) < Real.pi/2 at hlt
  linarith

private lemma P_ne_zero {b c : ℝ} (hc : 0 ≤ c) (hc' : c < 1/2) (N : ℕ) :
    P b c N ≠ 0 := by
  exact Finset.prod_ne_zero_iff.mpr (fun n _ => q_ne_zero hc (a_pos hc' (n+1)))

private lemma P_arg {b c : ℝ} (hb : 0 ≤ b) (hc : 0 ≤ c) (hc' : c < 1/2) (N : ℕ) :
    (P b c N).arg = S b c N := by
  induction N with
  | zero => simp [P, S]
  | succ N ih =>
    have he : P b c (N+1) = P b c N * q b c (a (N+1)) := by
      simp [P, Finset.prod_range_succ]
    have hs : S b c (N+1) = S b c N + d b c (a (N+1)) := by
      simp [S, Finset.sum_range_succ]
    rw [he, hs, Complex.arg_mul (P_ne_zero hc hc' N)
      (q_ne_zero hc (a_pos hc' (N+1))), ih, q_arg hb hc (a_pos hc' (N+1))]
    rw [ih, q_arg hb hc (a_pos hc' (N+1)), ← hs]
    constructor
    · linarith [(S_bounds hb hc hc' (N+1)).1, Real.pi_pos]
    · linarith [S_lt hb hc hc' (N+1), Real.pi_pos]

private noncomputable def R (b c : ℝ) (N : ℕ) : ℂ := q b c (a 0) / P b c N

private lemma R_arg_bounds {b c : ℝ} (hb : 0 ≤ b) (hc : 0 ≤ c) (hc' : c < 1/2) (N : ℕ) :
    |(R b c N).arg| ≤ f b (a 0-c) := by
  have hs := S_bounds hb hc hc' N
  have hd := d_bounds hb hc (a_pos hc' 0)
  have hn := f_nonneg hb (sub_pos.mpr (a_pos hc' (N+1)))
  have hf : f b (a 1-c) ≤ f b (a 0-c) :=
    f_antitone hb (sub_pos.mpr (a_pos hc' 0)) (by norm_num [a])
  have hlt : f b (a 0-c) < Real.pi/2 := Real.arctan_lt_pi_div_two _
  have hr : -f b (a 0-c) ≤ d b c (a 0) - S b c N ∧
      d b c (a 0) - S b c N ≤ f b (a 0-c) := by constructor <;> linarith
  have hm : d b c (a 0) - S b c N ∈ Set.Ioc (-Real.pi) Real.pi := by
    constructor <;> linarith [Real.pi_pos]
  have he : (R b c N).arg = d b c (a 0) - S b c N := by
    have he' : ((R b c N).arg : Real.Angle) =
        ((d b c (a 0) - S b c N : ℝ) : Real.Angle) := by
      rw [R, Complex.arg_div_coe_angle (q_ne_zero hc (a_pos hc' 0)) (P_ne_zero hc hc' N),
        q_arg hb hc (a_pos hc' 0), P_arg hb hc hc' N, Real.Angle.coe_sub]
    have h := congrArg Real.Angle.toReal he'
    rw [Complex.arg_coe_angle_toReal_eq_arg,
      Real.Angle.toReal_coe_eq_self_iff_mem_Ioc.mpr hm] at h
    exact h
  rw [he, abs_le]
  exact hr

private lemma sector_estimate {z : ℂ} {M : ℝ} (hM : M < Real.pi/2) (hz : |z.arg| ≤ M) :
    ‖z‖ * Real.cos M ≤ z.re := by
  rw [← Complex.norm_mul_cos_arg z]
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
  rw [← Real.cos_abs z.arg]
  exact Real.cos_le_cos_of_nonneg_of_le_pi (abs_nonneg _) (by linarith [Real.pi_pos]) hz

private noncomputable def sp (b c : ℝ) : ℂ := ((1/4-c/2:ℝ):ℂ) + ((b/2:ℝ):ℂ)*Complex.I
private noncomputable def sm (b c : ℝ) : ℂ := ((1/4+c/2:ℝ):ℂ) - ((b/2:ℝ):ℂ)*Complex.I

private lemma q_eq (b c : ℝ) (n : ℕ) :
    q b c (a n) = 4*((sp b c+n)*(sm b c+n)) := by
  simp only [q, a, sp, sm]
  push_cast
  ring

private lemma q_product (b c : ℝ) (N : ℕ) :
    q b c (a 0) * P b c N =
      (4:ℂ)^(N+1)*(∏ n ∈ Finset.range (N+1), (sp b c+n)) *
        (∏ n ∈ Finset.range (N+1), (sm b c+n)) := by
  have h : q b c (a 0) * P b c N = ∏ n ∈ Finset.range (N+1), q b c (a n) := by
    rw [Finset.prod_range_succ']
    exact mul_comm _ _
  rw [h]
  simp only [q_eq, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_range]
  ring

private noncomputable def H (b c : ℝ) (N : ℕ) : ℂ :=
  q b c (a 0)^2 * Complex.GammaSeq (sp b c) N * Complex.GammaSeq (sm b c) N

private lemma H_eq {b c : ℝ} (hc : 0 ≤ c) (hc' : c < 1/2) {N : ℕ} (hN : N ≠ 0) :
    H b c N = (((N:ℝ)^(1/2:ℝ) * (N.factorial:ℝ)^2 * 4^(N+1):ℝ):ℂ) * R b c N := by
  have hn : (N:ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hN
  have hs : sp b c + sm b c = (1/2:ℂ) := by unfold sp sm; push_cast; ring
  have hp := q_product b c N
  have hq := q_ne_zero (b := b) hc (a_pos hc' 0)
  have hP := P_ne_zero (b := b) hc hc' N
  have hd : (∏ n ∈ Finset.range (N+1), (sp b c+n)) *
      (∏ n ∈ Finset.range (N+1), (sm b c+n)) ≠ 0 := by
    intro h
    have hz : q b c (a 0) * P b c N = 0 := by rw [hp, mul_assoc, h, mul_zero]
    exact (mul_ne_zero hq hP) hz
  have hnum : (N:ℂ)^(sp b c) * (N:ℂ)^(sm b c) =
      (((N:ℝ)^(1/2:ℝ):ℝ):ℂ) := by
    rw [← Complex.cpow_add _ _ hn, hs, Complex.ofReal_cpow (by positivity)]
    push_cast
    rfl
  unfold H Complex.GammaSeq R
  push_cast
  rw [show q b c (a 0)^2 *
      ((N:ℂ)^(sp b c) * (N.factorial:ℂ) / (∏ n ∈ Finset.range (N+1), (sp b c+n))) *
      ((N:ℂ)^(sm b c) * (N.factorial:ℂ) / (∏ n ∈ Finset.range (N+1), (sm b c+n))) =
      q b c (a 0)^2 * ((N:ℂ)^(sp b c)*(N:ℂ)^(sm b c)) * (N.factorial:ℂ)^2 /
        ((∏ n ∈ Finset.range (N+1), (sp b c+n)) *
         (∏ n ∈ Finset.range (N+1), (sm b c+n))) by ring]
  rw [hnum]
  field_simp [(mul_ne_zero_iff.mp hd).1, (mul_ne_zero_iff.mp hd).2, hP]
  linear_combination (((N:ℝ)^(1/2:ℝ):ℝ):ℂ) * (N.factorial:ℂ)^2 * hp



private lemma H_tendsto (b c : ℝ) :
    Tendsto (H b c) atTop
      (𝓝 (q b c (a 0)^2 * Complex.Gamma (sp b c) * Complex.Gamma (sm b c))) :=
  (tendsto_const_nhds.mul (Complex.GammaSeq_tendsto_Gamma _)).mul
    (Complex.GammaSeq_tendsto_Gamma _)

private lemma gamma_sector_quadrant {b c : ℝ} (hb : 0 ≤ b) (hc : 0 ≤ c) (hc' : c < 1/2) :
    0 < (q b c (a 0)^2 * Complex.Gamma (sp b c) * Complex.Gamma (sm b c)).re := by
  let M := f b (a 0-c)
  have hM : M < Real.pi/2 := Real.arctan_lt_pi_div_two _
  have hcos : 0 < Real.cos M := Real.cos_arctan_pos _
  have hest : ∀ᶠ N in atTop, ‖H b c N‖ * Real.cos M ≤ (H b c N).re := by
    filter_upwards [eventually_ne_atTop 0] with N hN
    have hcoef : 0 < (N:ℝ)^(1/2:ℝ) * (N.factorial:ℝ)^2 * 4^(N+1) := by
      have hn : 0 < (N:ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hN)
      have hn' : 0 < (N.factorial:ℝ) := Nat.cast_pos.mpr (Nat.factorial_pos N)
      positivity
    apply sector_estimate hM
    rw [H_eq hc hc' hN, Complex.arg_real_mul _ hcoef]
    exact R_arg_bounds hb hc hc' N
  have hlim := H_tendsto b c
  have hle := le_of_tendsto_of_tendsto (hlim.norm.mul_const (Real.cos M))
    (Complex.continuous_re.tendsto _ |>.comp hlim) hest
  have hsp : 0 < (sp b c).re := by simp [sp]; linarith
  have hsm : 0 < (sm b c).re := by simp [sm]; linarith
  have hne := mul_ne_zero
    (mul_ne_zero (pow_ne_zero 2 (q_ne_zero (b := b) hc (a_pos hc' 0)))
      (Complex.Gamma_ne_zero_of_re_pos hsp)) (Complex.Gamma_ne_zero_of_re_pos hsm)
  exact lt_of_lt_of_le (mul_pos (norm_pos_iff.mpr hne) hcos) hle

private noncomputable def F (z : ℂ) : ℂ :=
  (z^2+1/4)^2 * Complex.Gamma (1/4+Complex.I*z/2) * Complex.Gamma (1/4-Complex.I*z/2)

private lemma F_quadrant {z : ℂ} (hb : 0 ≤ z.re) (hc : 0 ≤ z.im) (hc' : z.im < 1/2) :
    0 < (F z).re := by
  have hq : q z.re z.im (a 0) = z^2+1/4 := by
    apply Complex.ext <;> simp [q, a, pow_two, Complex.mul_re, Complex.mul_im] <;> ring
  have hsp : sp z.re z.im = 1/4+Complex.I*z/2 := by
    apply Complex.ext <;> simp [sp, Complex.mul_re, Complex.mul_im]; ring
  have hsm : sm z.re z.im = 1/4-Complex.I*z/2 := by
    apply Complex.ext <;> simp [sm, Complex.mul_re, Complex.mul_im]; ring
  simpa only [F, hq, hsp, hsm] using gamma_sector_quadrant hb hc hc'

private lemma F_neg (z : ℂ) : F (-z) = F z := by
  simp only [F, neg_sq, mul_neg, neg_div, ← sub_eq_add_neg, sub_neg_eq_add]
  ring

private lemma F_conj (z : ℂ) : F (starRingEnd ℂ z) = starRingEnd ℂ (F z) := by
  have hsp : (1/4+Complex.I*(starRingEnd ℂ z)/2:ℂ) =
      starRingEnd ℂ (1/4-Complex.I*z/2) := by
    simp only [map_sub, map_div₀, map_mul, map_one, map_ofNat, Complex.conj_I]
    ring
  have hsm : (1/4-Complex.I*(starRingEnd ℂ z)/2:ℂ) =
      starRingEnd ℂ (1/4+Complex.I*z/2) := by
    simp only [map_add, map_div₀, map_mul, map_one, map_ofNat, Complex.conj_I]
    ring
  rw [F, hsp, hsm, Complex.Gamma_conj, Complex.Gamma_conj]
  simp only [F, map_mul, map_pow, map_add, map_div₀, map_one, map_ofNat]
  ring

/-- Exact Gamma-pair positivity throughout the open spectral strip. -/
private theorem gamma_pair_re_pos {z : ℂ} (hz : |z.im| < 1/2) : 0 < (F z).re := by
  obtain ⟨hlo, hhi⟩ := abs_lt.mp hz
  by_cases hb : 0 ≤ z.re
  · by_cases hc : 0 ≤ z.im
    · exact F_quadrant hb hc hhi
    · have h := F_quadrant (z := starRingEnd ℂ z) (by simpa using hb)
        (by simp; linarith) (by simp; linarith)
      simpa [F_conj] using h
  · by_cases hc : 0 ≤ z.im
    · have h := F_quadrant (z := -(starRingEnd ℂ z))
        (by simp; linarith) (by simpa using hc) (by simpa using hhi)
      simpa [F_neg, F_conj] using h
    · have h := F_quadrant (z := -z) (by simp; linarith)
        (by simp; linarith) (by simp; linarith)
      simpa [F_neg] using h


/-- Gamma pair associated with the first theta atom, with its real normalization. -/
noncomputable def thetaCuspAtomGammaPair (z : ℂ) : ℂ :=
  ((z^2+1/4)^2 * Complex.Gamma (1/4+Complex.I*z/2) *
    Complex.Gamma (1/4-Complex.I*z/2)) / ((4 * Real.sqrt Real.pi : ℝ) : ℂ)

/-- The polynomial-corrected Gamma product has positive real part in the open strip. -/
theorem thetaCuspAtomGammaCore_re_pos {z : ℂ} (hz : |z.im| < 1/2) :
    0 < ((z^2+1/4)^2 * Complex.Gamma (1/4+Complex.I*z/2) *
      Complex.Gamma (1/4-Complex.I*z/2)).re :=
  gamma_pair_re_pos hz

/-- Strict sector law; no hypothesis about zeta zeros is used. -/
theorem thetaCuspAtomGammaPair_re_pos {z : ℂ} (hz : |z.im| < 1/2) :
    0 < (thetaCuspAtomGammaPair z).re := by
  change 0 < (F z / ((4 * Real.sqrt Real.pi : ℝ) : ℂ)).re
  rw [Complex.div_ofReal_re]
  exact div_pos (gamma_pair_re_pos hz)
    (mul_pos (by norm_num) (Real.sqrt_pos_of_pos Real.pi_pos))

end RHTower
