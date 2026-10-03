import GaloisForLFunctions.RHTower.DirichletAbel
import GaloisForLFunctions.RHTower.DirichletUniformAbel
import GaloisForLFunctions.RHTower.DirichletLSeriesBridge
import GaloisForLFunctions.RHTower.ZetaVerticalGrowth
import GaloisForLFunctions.RHTower.ZetaThreeFourOne
import Mathlib.NumberTheory.LSeries.Nonvanishing

/-!
# Actual Dirichlet L-functions in a logarithmically shrinking strip

Finite-period cancellation supplies an unconditional truncation remainder for each
nonprincipal character throughout Re(s)>0. Its ordered Dirichlet sums are identified
with the actual analytic continuation, without claiming absolute convergence there.
Truncating at the height gives logarithmic growth across the one-line. The principal
character is included through its exact finite Euler product, with a common explicit
constant for every character of the fixed modulus. This is the analytic input for
BAG rational-phase prime estimates; no prime-distribution rate is assumed.
-/

noncomputable section
open Filter Topology Finset Complex
open GaloisForLFunctions.RHTower
namespace RHTower
variable {Q : ℕ} [NeZero Q]

private theorem character_period_sum {χ : DirichletCharacter ℂ Q} (hχ : χ ≠ 1) :
    (∑ j ∈ range Q, χ (j + 1)) = 0 := by
  have hfin (r : Fin Q) : ZMod.finEquiv Q r = (r.val : ZMod Q) := by
    cases Q with
    | zero => exact (NeZero.ne 0 rfl).elim
    | succ q =>
      apply ZMod.val_injective
      change r.val = r.val % (q + 1)
      rw [Nat.mod_eq_of_lt r.isLt]
  have heq : (∑ r : ZMod Q, χ (r + 1)) = ∑ j ∈ range Q, χ (j + 1) := by
    calc
      (∑ r : ZMod Q, χ (r + 1)) = ∑ r : Fin Q, χ (ZMod.finEquiv Q r + 1) :=
        ((ZMod.finEquiv Q).sum_comp _).symm
      _ = ∑ r : Fin Q, χ ((r.val : ZMod Q) + 1) := by simp_rw [hfin]
      _ = _ := Fin.sum_univ_eq_sum_range (fun j : ℕ => χ (j + 1)) Q
  rw [← heq]
  calc
    (∑ r : ZMod Q, χ (r + 1)) = ∑ r : ZMod Q, χ r :=
      Equiv.sum_comp (Equiv.addRight (1 : ZMod Q)) χ
    _ = 0 := χ.sum_eq_zero_of_ne_one hχ

private theorem character_partial_bound {χ : DirichletCharacter ℂ Q} (hχ : χ ≠ 1)
    (n : ℕ) : ‖∑ j ∈ range n, χ (j + 1)‖ ≤ (Q : ℝ) := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases hn : n < Q
    · calc
        ‖∑ j ∈ range n, χ (j + 1)‖ ≤ ∑ j ∈ range n, ‖χ (j + 1)‖ := norm_sum_le _ _
        _ ≤ ∑ _j ∈ range n, (1 : ℝ) := sum_le_sum fun j _ => χ.norm_le_one _
        _ = n := by simp
        _ ≤ Q := by exact_mod_cast hn.le
    · have hQ : 0 < Q := NeZero.pos Q
      have hQn : Q ≤ n := Nat.le_of_not_gt hn
      have hsplit : (∑ j ∈ range n, χ (j + 1)) = ∑ j ∈ range (n - Q), χ (j + 1) := by
        conv_lhs => rw [← Nat.add_sub_of_le hQn, sum_range_add]
        rw [character_period_sum hχ, zero_add]
        apply sum_congr rfl
        intro j _
        simp
      rw [hsplit]
      exact ih (n - Q) (by omega)

private theorem character_abel_eq_of_one_lt {χ : DirichletCharacter ℂ Q} (hχ : χ ≠ 1)
    {s : ℂ} (hs : 1 < s.re) :
    abelDirichlet (fun j => χ (j + 1)) s = DirichletCharacter.LFunction χ s := by
  have hsum : HasSum (LSeries.term (fun n => χ n) s) (DirichletCharacter.LFunction χ s) := by
    rw [χ.LFunction_eq_LSeries hs]
    exact (χ.LSeriesSummable_of_one_lt_re hs).hasSum
  have hshift : HasSum (fun j : ℕ => LSeries.term (fun n => χ n) s (j + 1))
      (DirichletCharacter.LFunction χ s) := by
    apply (hasSum_nat_add_iff 1).mpr
    simpa only [sum_range_one, LSeries.term_zero, add_zero] using hsum
  have hlim := hshift.tendsto_sum_nat
  have hlim' : Tendsto (fun n : ℕ => ∑ j ∈ range n,
      (((j : ℝ) + 1 : ℝ) : ℂ) ^ (-s) * χ (j + 1)) atTop
      (𝓝 (DirichletCharacter.LFunction χ s)) := by
    apply hlim.congr
    intro n
    apply sum_congr rfl
    intro j _
    rw [term_succ_eq]
    push_cast
    ring
  exact tendsto_nhds_unique
    (tendsto_abelDirichlet (character_partial_bound hχ) (by linarith)) hlim'

private theorem character_abel_eq {χ : DirichletCharacter ℂ Q} (hχ : χ ≠ 1)
    {s : ℂ} (hs : 0 < s.re) :
    abelDirichlet (fun j => χ (j + 1)) s = DirichletCharacter.LFunction χ s := by
  let F : ℂ → ℂ := fun z => abelDirichlet (fun j => χ (j + 1)) z -
    DirichletCharacter.LFunction χ z
  have hdiff : DifferentiableOn ℂ F {z : ℂ | 0 < z.re} := by
    intro z hz
    exact ((differentiableAt_abelDirichlet (character_partial_bound hχ) hz).sub
      (DirichletCharacter.differentiable_LFunction hχ z)).differentiableWithinAt
  have hev : F =ᶠ[𝓝 (2 : ℂ)] 0 := by
    have hn : {z : ℂ | 1 < z.re} ∈ 𝓝 (2 : ℂ) :=
      (isOpen_lt continuous_const Complex.continuous_re).mem_nhds (by norm_num)
    filter_upwards [hn] with z hz
    simp only [F, character_abel_eq_of_one_lt hχ hz, sub_self, Pi.zero_apply]
  have hz := (hdiff.analyticOnNhd isOpen_reGT_zero).eqOn_zero_of_preconnected_of_eventuallyEq_zero
    isPreconnected_reGT_zero (show (2 : ℂ) ∈ {z : ℂ | 0 < z.re} by norm_num) hev hs
  exact sub_eq_zero.mp hz

private theorem tendsto_character_partial {χ : DirichletCharacter ℂ Q} (hχ : χ ≠ 1)
    {s : ℂ} (hs : 0 < s.re) :
    Tendsto (fun n => dirichletPartialSum (fun j => χ (j + 1)) n s) atTop
      (𝓝 (DirichletCharacter.LFunction χ s)) := by
  have h := tendsto_abelDirichlet (character_partial_bound hχ) hs
  rw [character_abel_eq hχ hs] at h
  apply h.congr
  intro n
  exact sum_congr rfl fun j _ => mul_comm _ _

/-- Actual character truncation, valid throughout the open right half-plane. -/
theorem norm_LFunction_sub_character_partial_le {χ : DirichletCharacter ℂ Q}
    (hχ : χ ≠ 1) {s : ℂ} (hs : 0 < s.re) (M : ℕ) :
    ‖DirichletCharacter.LFunction χ s - dirichletPartialSum (fun j => χ (j + 1)) M s‖ ≤
      2 * Q * (1 + ‖s‖ / s.re) * ((M : ℝ) + 1) ^ (-s.re) := by
  apply le_of_tendsto (((tendsto_character_partial hχ hs).sub tendsto_const_nhds).norm)
  filter_upwards [eventually_ge_atTop M] with n hn
  exact norm_dirichletPartialSum_sub_le (character_partial_bound hχ) hs hn

/-- The actual nonprincipal character L-function has logarithmic growth on a shrinking
neighborhood of the one-line; the modulus cost is explicit. -/
theorem norm_LFunction_le_log_of_ne_one {χ : DirichletCharacter ℂ Q} (hχ : χ ≠ 1)
    {σ t : ℝ} (ht : 8 ≤ |t|) (hσ : 1 - 1 / Real.log |t| ≤ σ) (hσ2 : σ ≤ 2) :
    ‖DirichletCharacter.LFunction χ (σ + t * I)‖ ≤
      (2 + 6 * (Q : ℝ)) * Real.exp 1 * Real.log |t| := by
  have ht0 : 0 < |t| := by linarith
  have ht1 : 1 ≤ |t| := by linarith
  have hL2 : 2 < Real.log |t| := by
    have h := Real.log_lt_log (Real.exp_pos 2)
      (lt_of_lt_of_le exp_two_lt_eight ht)
    rwa [Real.log_exp] at h
  have hσhalf : 1 / 2 ≤ σ := by
    have h := div_le_div_of_nonneg_left (by norm_num : (0 : ℝ) ≤ 1)
      (by norm_num : (0 : ℝ) < 2) hL2.le
    linarith
  have hre : (σ + t * I : ℂ).re = σ := by simp
  have hs0 : 0 < (σ + t * I : ℂ).re := by rw [hre]; linarith
  let M := ⌊|t|⌋₊
  have hM1 : 1 ≤ M := Nat.le_floor (by exact_mod_cast ht1)
  have hM0 : (0 : ℝ) < M := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hM1)
  have hMt : (M : ℝ) ≤ |t| := Nat.floor_le ht0.le
  have htM : |t| ≤ (M : ℝ) + 1 := (Nat.lt_floor_add_one |t|).le
  have hp : ∀ x : ℝ, 1 ≤ x → x ≤ |t| → x ^ (1 - σ) ≤ Real.exp 1 := by
    intro x hx hxt
    rcases le_or_gt (1 - σ) 0 with hneg | hpos
    · exact (Real.rpow_le_one_of_one_le_of_nonpos hx hneg).trans
        (by linarith [Real.add_one_le_exp (1 : ℝ)])
    · calc
        x ^ (1 - σ) ≤ |t| ^ (1 - σ) := Real.rpow_le_rpow (by linarith) hxt hpos.le
        _ ≤ |t| ^ (1 / Real.log |t|) :=
          Real.rpow_le_rpow_of_exponent_le ht1 (by linarith)
        _ = Real.exp 1 := by
          rw [Real.rpow_def_of_pos ht0, mul_one_div, div_self (by linarith)]
  have hpneg : ∀ x : ℝ, 1 ≤ x → x ≤ |t| → x ^ (-σ) ≤ Real.exp 1 / x := by
    intro x hx hxt
    have hx0 : 0 < x := by linarith
    calc
      x ^ (-σ) = x ^ (1 - σ) * x ^ (-1 : ℝ) := by
        rw [← Real.rpow_add hx0]; congr 1; ring
      _ ≤ Real.exp 1 * x ^ (-1 : ℝ) :=
        mul_le_mul_of_nonneg_right (hp x hx hxt) (Real.rpow_nonneg hx0.le _)
      _ = Real.exp 1 / x := by rw [Real.rpow_neg_one, div_eq_mul_inv]
  have hhead : ‖dirichletPartialSum (fun j => χ (j + 1)) M (σ + t * I)‖ ≤
      Real.exp 1 * (Real.log (M : ℝ) + 2) := by
    have hid := dirichletPartialSum_eq_sum_term (fun n : ℕ => χ n) M (σ + t * I)
    simp only [Nat.cast_add, Nat.cast_one] at hid
    rw [hid]
    calc
      ‖∑ n ∈ Icc 1 M, LSeries.term (fun n => χ n) (σ + t * I) n‖ ≤
          ∑ n ∈ Icc 1 M, ‖LSeries.term (fun n => χ n) (σ + t * I) n‖ := norm_sum_le _ _
      _ ≤ ∑ n ∈ Icc 1 M, Real.exp 1 / (n : ℝ) := by
        apply sum_le_sum
        intro n hn
        obtain ⟨hn1, hnM⟩ := mem_Icc.mp hn
        have hn0 : 0 < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
        have hnc : (1 : ℝ) ≤ n := by exact_mod_cast hn1
        have hnt : (n : ℝ) ≤ |t| := (Nat.cast_le.mpr hnM).trans hMt
        rw [LSeries.term_of_ne_zero (by omega : n ≠ 0), div_eq_mul_inv,
          ← Complex.cpow_neg, norm_mul]
        have hncast : (n : ℂ) = ((n : ℝ) : ℂ) := by simp
        rw [hncast, Complex.norm_cpow_eq_rpow_re_of_pos hn0, Complex.neg_re, hre]
        calc
          ‖χ (n : ZMod Q)‖ * (n : ℝ) ^ (-σ) ≤ (n : ℝ) ^ (-σ) :=
            mul_le_of_le_one_left (Real.rpow_nonneg hn0.le _) (χ.norm_le_one _)
          _ ≤ Real.exp 1 / n := hpneg n hnc hnt
      _ = Real.exp 1 * ∑ n ∈ Icc 1 M, 1 / (n : ℝ) := by rw [mul_sum]; congr 1; ext; ring
      _ ≤ Real.exp 1 * (Real.log (M : ℝ) + 2) :=
        mul_le_mul_of_nonneg_left (sum_inv_le M hM1) (Real.exp_pos 1).le
  have htailpow : ((M : ℝ) + 1) ^ (-σ) ≤ Real.exp 1 / |t| := by
    exact (Real.rpow_le_rpow_of_nonpos ht0 htM (by linarith)).trans
      (hpneg |t| ht1 le_rfl)
  have hnorm : ‖(σ + t * I : ℂ)‖ ≤ 2 + |t| := by
    have h := Complex.norm_le_abs_re_add_abs_im (σ + t * I : ℂ)
    simp only [add_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im,
      sub_self, add_zero, add_im, mul_im, mul_one, zero_add] at h
    rw [abs_of_nonneg (by linarith : 0 ≤ σ)] at h
    linarith
  have hcoef : 1 + ‖(σ + t * I : ℂ)‖ / σ ≤ 3 * |t| := by
    have hdiv : ‖(σ + t * I : ℂ)‖ / σ ≤ 2 * (2 + |t|) := by
      apply (div_le_iff₀ (by linarith : 0 < σ)).mpr
      have hmul := mul_le_mul_of_nonneg_left hσhalf (by positivity : 0 ≤ 2 * (2 + |t|))
      nlinarith
    linarith
  have htail : ‖DirichletCharacter.LFunction χ (σ + t * I) -
      dirichletPartialSum (fun j => χ (j + 1)) M (σ + t * I)‖ ≤
        6 * (Q : ℝ) * Real.exp 1 := by
    refine (norm_LFunction_sub_character_partial_le hχ hs0 M).trans ?_
    rw [hre]
    calc
      2 * Q * (1 + ‖(σ + t * I : ℂ)‖ / σ) * ((M : ℝ) + 1) ^ (-σ) ≤
          (2 * Q * (3 * |t|)) * (Real.exp 1 / |t|) :=
        mul_le_mul (mul_le_mul_of_nonneg_left hcoef (by positivity)) htailpow
          (Real.rpow_nonneg (by positivity) _) (by positivity)
      _ = 6 * (Q : ℝ) * Real.exp 1 := by field_simp; ring
  have hlog : Real.log (M : ℝ) ≤ Real.log |t| := Real.log_le_log hM0 hMt
  have htri := norm_le_norm_add_norm_sub'
    (DirichletCharacter.LFunction χ (σ + t * I))
    (dirichletPartialSum (fun j => χ (j + 1)) M (σ + t * I))
  have hQ0 : (0 : ℝ) ≤ Q := Nat.cast_nonneg _
  have hE := Real.exp_pos (1 : ℝ)
  nlinarith [mul_nonneg (by positivity : (0 : ℝ) ≤ 6 * Q * Real.exp 1)
    (show 0 ≤ Real.log |t| - 1 by linarith)]

omit [NeZero Q] in
private theorem norm_character_euler_product_le {s : ℂ} (hs : 0 ≤ s.re) :
    ‖∏ p ∈ Q.primeFactors, (1 - (p : ℂ) ^ (-s))‖ ≤ (2 : ℝ) ^ Q.primeFactors.card := by
  rw [norm_prod]
  calc
    (∏ p ∈ Q.primeFactors, ‖1 - (p : ℂ) ^ (-s)‖) ≤ ∏ _p ∈ Q.primeFactors, (2 : ℝ) := by
      apply prod_le_prod (fun p _ => norm_nonneg _)
      intro p hp
      have hpprime := Nat.prime_of_mem_primeFactors hp
      have hpow : ‖(p : ℂ) ^ (-s)‖ ≤ 1 := by
        change ‖((p : ℝ) : ℂ) ^ (-s)‖ ≤ 1
        rw [Complex.norm_cpow_eq_rpow_re_of_pos (by exact_mod_cast hpprime.pos), neg_re]
        exact Real.rpow_le_one_of_one_le_of_nonpos (by exact_mod_cast hpprime.one_le) (by linarith)
      have h := norm_sub_le (1 : ℂ) ((p : ℂ) ^ (-s))
      rw [norm_one] at h
      linarith
    _ = _ := by simp

/-- A fixed-modulus constant controlling the actual principal and nonprincipal functions. -/
def characterLogStripConstant (Q : ℕ) : ℝ :=
  (2 + 6 * (Q : ℝ)) * Real.exp 1 + 17 * (2 : ℝ) ^ Q.primeFactors.card

theorem one_le_characterLogStripConstant (Q : ℕ) : 1 ≤ characterLogStripConstant Q := by
  have hpow : (1 : ℝ) ≤ 2 ^ Q.primeFactors.card := one_le_pow₀ (by norm_num)
  have hpos : 0 ≤ (2 + 6 * (Q : ℝ)) * Real.exp 1 := by positivity
  unfold characterLogStripConstant
  linarith

/-- Logarithmic growth holds for every actual character, including principal and imprimitive
characters, on the same shrinking strip. -/
theorem norm_LFunction_le_log (χ : DirichletCharacter ℂ Q)
    {σ t : ℝ} (ht : 8 ≤ |t|) (hσ : 1 - 1 / Real.log |t| ≤ σ) (hσ2 : σ ≤ 2) :
    ‖DirichletCharacter.LFunction χ (σ + t * I)‖ ≤
      characterLogStripConstant Q * Real.log |t| := by
  have hL0 : 0 ≤ Real.log |t| := Real.log_nonneg (by linarith)
  by_cases hχ : χ = 1
  · subst χ
    have hsne : (σ + t * I : ℂ) ≠ 1 := by
      intro heq
      have him := congrArg Complex.im heq
      simp at him
      simp [him] at ht
      linarith
    have hL1 : 1 ≤ Real.log |t| := by
      have h := Real.log_lt_log (Real.exp_pos 2)
        (lt_of_lt_of_le exp_two_lt_eight ht)
      rw [Real.log_exp] at h
      linarith
    have hσ0 : 0 ≤ σ := by
      have h := div_le_one_of_le₀ hL1 (by linarith : 0 ≤ Real.log |t|)
      linarith
    change ‖DirichletCharacter.LFunctionTrivChar Q (σ + t * I)‖ ≤ _
    rw [DirichletCharacter.LFunctionTrivChar_eq_mul_riemannZeta hsne, norm_mul]
    calc
      _ ≤ (2 : ℝ) ^ Q.primeFactors.card * (14 * Real.log |t|) :=
        mul_le_mul (norm_character_euler_product_le (by simpa using hσ0))
          (abs_riemannZeta_le_log ht hσ hσ2) (norm_nonneg _) (by positivity)
      _ ≤ characterLogStripConstant Q * Real.log |t| := by
        unfold characterLogStripConstant
        have hpos : 0 ≤ (2 + 6 * (Q : ℝ)) * Real.exp 1 := by positivity
        have hpow : 0 ≤ (2 : ℝ) ^ Q.primeFactors.card := by positivity
        nlinarith
  · refine (norm_LFunction_le_log_of_ne_one hχ ht hσ hσ2).trans ?_
    apply mul_le_mul_of_nonneg_right _ hL0
    unfold characterLogStripConstant
    exact le_add_of_nonneg_right (by positivity)

/-- The actual principal character has the required pole bound on the real axis. -/
theorem norm_LFunctionTrivChar_one_add_le {x : ℝ} (hx : 0 < x) (hx1 : x ≤ 1) :
    ‖DirichletCharacter.LFunctionTrivChar Q (1 + x)‖ ≤ characterLogStripConstant Q / x := by
  have hsne : (1 + (x : ℂ)) ≠ 1 := by
    intro heq
    have hre := congrArg Complex.re heq
    simp at hre
    linarith
  rw [DirichletCharacter.LFunctionTrivChar_eq_mul_riemannZeta hsne, norm_mul]
  have hpole : ‖riemannZeta (1 + (x : ℂ))‖ ≤ 3 / x := by
    refine (abs_riemannZeta_one_add_le hx).trans ?_
    apply (le_div_iff₀ hx).mpr
    have hinv : 1 / x * x = (1 : ℝ) := div_mul_cancel₀ 1 hx.ne'
    nlinarith
  calc
    _ ≤ (2 : ℝ) ^ Q.primeFactors.card * (3 / x) :=
      mul_le_mul (norm_character_euler_product_le (by simp; linarith)) hpole
        (norm_nonneg _) (by positivity)
    _ ≤ characterLogStripConstant Q / x := by
      rw [← mul_div_assoc]
      apply div_le_div_of_nonneg_right _ hx.le
      unfold characterLogStripConstant
      have hpos : 0 ≤ (2 + 6 * (Q : ℝ)) * Real.exp 1 := by positivity
      have hpow : 0 ≤ (2 : ℝ) ^ Q.primeFactors.card := by positivity
      linarith

end RHTower
