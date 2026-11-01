import GaloisForLFunctions.RenormalizedIntersectionTheory.GaussMayerCountableWordTraces
import GaloisForLFunctions.HTGeometry.TrigammaLeadingAsymptotic

/-! The bottom rows of actual Gauss matrices carry an exact probability law.
Its successor telescope controls all word lengths and their denominator sums. -/

open Filter Topology
open GaloisForLFunctions
open GaloisForLFunctions.RenormalizedIntersectionTheory.MayerWords
set_option autoImplicit false
noncomputable section
namespace GaloisForLFunctions.RenormalizedIntersectionTheory.MayerWordProbability

/-- The exact probability attached to the actual denominator row. -/
def probability (k : ℕ) (a : Word k) : ℝ :=
  1 / ((wordMatrix k a 1 1 : ℝ) * (wordMatrix k a 1 0 + wordMatrix k a 1 1))

private theorem probability_nonneg (k : ℕ) (a : Word k) : 0 ≤ probability k a := by
  unfold probability
  positivity

private theorem denominator_pos (k : ℕ) (a : Word k) : (0 : ℝ) < wordMatrix k a 1 1 := by
  exact_mod_cast (wordMatrix_denominator_row k a).2

/-- One successor digit preserves the bottom-row probability exactly. -/
theorem hasSum_successor {c d : ℝ} (hc : 0 ≤ c) (hd : 0 < d) :
    HasSum (fun n : ℕ => 1 / ((c+d*(n+1))*(c+d*(n+2)))) (1/(d*(c+d))) := by
  have hcd : 0 < c+d := add_pos_of_nonneg_of_pos hc hd
  have hx : 0 < (c+d)/d := div_pos hcd hd
  have h := (hasSum_one_div_shift_mul_succ hx).mul_left (d^2)⁻¹
  have he (n : ℕ) : (d^2)⁻¹ * (1 / (((c+d)/d+n)*((c+d)/d+n+1))) =
      1 / ((c+d*(n+1))*(c+d*(n+2))) := by
    have h1 : 0 < c+d*((n : ℝ)+1) := by positivity
    have h2 : 0 < c+d*((n : ℝ)+2) := by positivity
    field_simp
    ring
  have hv : (d^2)⁻¹ * (1/((c+d)/d)) = 1/(d*(c+d)) := by
    field_simp
  simpa only [he,hv] using h

private theorem hasSum_probability_cons (k : ℕ) (a : Word k) :
    HasSum (fun n : ℕ => probability (k+1) (Fin.cons n a)) (probability k a) := by
  have h := hasSum_successor (c := (wordMatrix k a 1 0 : ℝ))
    (Nat.cast_nonneg _) (denominator_pos k a)
  convert h using 1
  · funext n
    simp only [probability, wordMatrix_col_zero, wordMatrix_col_one,
      Fin.tail_cons, Fin.cons_zero, Nat.cast_add, Nat.cast_mul, Nat.cast_one]
    ring
  · rfl

/-- Summing over the entire countable Gauss alphabet gives mass one at every length. -/
theorem hasSum_probability (k : ℕ) : HasSum (probability k) 1 := by
  induction k with
  | zero => simpa [probability, wordMatrix] using hasSum_fintype (probability 0)
  | succ k ih =>
      let e : Word (k+1) ≃ (Σ _ : Word k, ℕ) :=
        { toFun := fun a => ⟨Fin.tail a,a 0⟩
          invFun := fun p => Fin.cons p.2 p.1
          left_inv := fun a => by simp
          right_inv := fun p => by cases p; simp }
      let f : (Σ _ : Word k, ℕ) → ℝ := fun p => probability (k+1) (Fin.cons p.2 p.1)
      have hf (a : Word k) : HasSum (fun n => f ⟨a,n⟩) (probability k a) :=
        hasSum_probability_cons k a
      have hs : Summable f := (summable_sigma_of_nonneg (fun p => probability_nonneg _ _)).mpr
        ⟨fun a => (hf a).summable, ih.summable.congr (fun a => (hf a).tsum_eq.symm)⟩
      have hv : (∑' p, f p) = 1 := by
        rw [hs.tsum_sigma' (fun a => (hf a).summable)]
        simpa only [(hf _).tsum_eq] using ih.tsum_eq
      have h := e.hasSum_iff.mpr (hv ▸ hs.hasSum)
      simpa [Function.comp_def, e, f] using h

/-- The denominator inverse squares have a bound independent of word length. -/
theorem tsum_denominator_inv_sq_le (k : ℕ) :
    Summable (fun a : Word k => (wordMatrix k a 1 1 : ℝ)⁻¹^2) ∧
      (∑' a : Word k, (wordMatrix k a 1 1 : ℝ)⁻¹^2) ≤ 2 := by
  have hb (a : Word k) : (wordMatrix k a 1 1 : ℝ)⁻¹^2 ≤ 2*probability k a := by
    have hd := denominator_pos k a
    have hc : (0 : ℝ) ≤ wordMatrix k a 1 0 := Nat.cast_nonneg _
    have hcd : (wordMatrix k a 1 0 : ℝ) ≤ wordMatrix k a 1 1 :=
      by exact_mod_cast (wordMatrix_denominator_row k a).1
    have hsum : (0 : ℝ) < wordMatrix k a 1 0 + wordMatrix k a 1 1 :=
      add_pos_of_nonneg_of_pos hc hd
    rw [probability, mul_one_div]
    apply (le_div_iff₀ (mul_pos hd hsum)).mpr
    field_simp
    nlinarith only [hcd,hd]
  have hs := (hasSum_probability k).summable.mul_left (2 : ℝ)
  have hf : Summable (fun a : Word k => (wordMatrix k a 1 1 : ℝ)⁻¹^2) :=
    hs.of_nonneg_of_le (fun _ => sq_nonneg _) hb
  refine ⟨hf, ?_⟩
  calc
    _ ≤ ∑' a : Word k, 2*probability k a := hf.tsum_le_tsum hb hs
    _ = 2 := by rw [tsum_mul_left, (hasSum_probability k).tsum_eq, mul_one]

/-- Every consecutive digit pair multiplies the denominator by at least two. -/
theorem even_denominator_growth (n : ℕ) (a : Word (2*n)) :
    2^n ≤ wordMatrix (2*n) a 1 1 := by
  induction n with
  | zero => norm_num [wordMatrix, Matrix.one_apply]
  | succ n ih =>
      have h0 := ih (Fin.tail (Fin.tail a))
      have h1 : wordMatrix (2*n) (Fin.tail (Fin.tail a)) 1 1 ≤
          wordMatrix (2*n) (Fin.tail (Fin.tail a)) 1 1 * (Fin.tail a 0+1) :=
        Nat.le_mul_of_pos_right _ (Nat.succ_pos _)
      have h2 : wordMatrix (2*n+1) (Fin.tail a) 1 1 ≤
          wordMatrix (2*n+1) (Fin.tail a) 1 1 * (a 0+1) :=
        Nat.le_mul_of_pos_right _ (Nat.succ_pos _)
      rw [wordMatrix_col_one] at h2
      change 2^(n+1) ≤ wordMatrix (2*n+2) a 1 1
      rw [pow_succ,wordMatrix_col_one,wordMatrix_col_zero,wordMatrix_col_one]
      omega

/-- The expanding eigenvalue dominates the actual bottom-right denominator. -/
theorem denominator_le_wordMultiplier (k : ℕ) (a : Word (k+1)) :
    (wordMatrix (k+1) a 1 1 : ℝ) ≤ wordMultiplier k a := by
  have h := mul_nonneg (Nat.cast_nonneg (wordMatrix (k+1) a 1 0))
    (fixedPoint_real_interval k a).1.le
  unfold wordMultiplier
  linarith only [h]

/-- The source decay rate beyond exponent two. -/
def decayRate (w : ℂ) : ℝ := Real.exp (-(w.re-2)*Real.log 2)

theorem decayRate_bounds {w : ℂ} (hw : 2 < w.re) : 0 < decayRate w ∧ decayRate w < 1 := by
  refine ⟨Real.exp_pos _, Real.exp_lt_one_iff.mpr ?_⟩
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  exact mul_neg_of_neg_of_pos (neg_neg_of_pos (sub_pos.mpr hw)) hlog

/-- Every even word has a uniformly bounded fixed-point trace denominator. -/
theorem norm_even_wordTrace_le {w : ℂ} (n : ℕ) (a : Word (2*n+2)) :
    ‖wordTrace w (2*n+1) a‖ ≤ (4/3 : ℝ) * wordMultiplier (2*n+1) a ^ (-w.re) := by
  let l := wordMultiplier (2*n+1) a
  have hd : 2 ≤ wordMatrix (2*n+2) a 1 1 := by
    have h := even_denominator_growth (n+1) a
    have hp : (2 : ℕ) ≤ 2^(n+1) := by
      rw [pow_succ]
      have hpos : 0 < (2 : ℕ)^n := pow_pos (by omega) _
      omega
    exact hp.trans h
  have hl : (2 : ℝ) ≤ l :=
    (by exact_mod_cast hd : (2 : ℝ) ≤ wordMatrix (2*n+2) a 1 1).trans
      (denominator_le_wordMultiplier (2*n+1) a)
  have hl0 : 0 < l := lt_of_lt_of_le (by norm_num) hl
  have hs : 0 < l^2 := sq_pos_of_pos hl0
  have hi : 1/l^2 ≤ (1/4 : ℝ) := by
    apply (div_le_div_iff₀ hs (by norm_num)).mpr
    nlinarith only [sq_nonneg (l-2),hl]
  have he : (3/4 : ℝ) ≤ 1-1/l^2 := by linarith only [hi]
  have hpos : 0 < 1-1/l^2 := lt_of_lt_of_le (by norm_num) he
  have hC : (1 - (-1 : ℂ)^(2*n+1+1)/(l : ℂ)^2) = ((1-1/l^2 : ℝ) : ℂ) := by
    push_cast
    simp only [show 2*n+1+1 = 2*n+2 by omega, pow_add, pow_mul]
    norm_num
  rw [wordTrace_eq_multiplier]
  change ‖(l : ℂ)^(-w)/(1-(-1 : ℂ)^(2*n+1+1)/(l : ℂ)^2)‖ ≤ _
  rw [norm_div, Complex.norm_cpow_eq_rpow_re_of_pos hl0, Complex.neg_re,
    hC, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hpos]
  calc
    _ ≤ l^(-w.re)/(3/4 : ℝ) :=
      div_le_div_of_nonneg_left (Real.rpow_nonneg hl0.le _) (by norm_num) he
    _ = _ := by ring

/-- The extra real exponent gives uniform geometric decay with pair length. -/
theorem multiplier_decay_le {w : ℂ} (hw : 2 < w.re) (n : ℕ) (a : Word (2*n+2)) :
    wordMultiplier (2*n+1) a ^ (-w.re) ≤ decayRate w^(n+1) *
      (wordMatrix (2*n+2) a 1 1 : ℝ)⁻¹^2 := by
  let d : ℝ := wordMatrix (2*n+2) a 1 1
  let l := wordMultiplier (2*n+1) a
  have hd : 0 < d := denominator_pos _ a
  have hdl : d ≤ l := denominator_le_wordMultiplier _ a
  have hl : 0 < l := hd.trans_le hdl
  have hpow : (2 : ℝ)^(n+1) ≤ d := by
    dsimp only [d]
    exact_mod_cast even_denominator_growth (n+1) a
  have hlog : ((n+1 : ℕ) : ℝ)*Real.log 2 ≤ Real.log d := by
    simpa only [Real.log_pow] using Real.log_le_log (pow_pos (by norm_num) _) hpow
  have hlogl : Real.log d ≤ Real.log l := Real.log_le_log hd hdl
  have h1 := mul_le_mul_of_nonneg_left hlogl (show 0 ≤ w.re by linarith only [hw])
  have h2 := mul_le_mul_of_nonneg_left hlog (sub_pos.mpr hw).le
  have he : d⁻¹^2 = Real.exp (-2*Real.log d) := by
    calc
      d⁻¹^2 = (Real.exp (Real.log d))⁻¹^2 := by rw [Real.exp_log hd]
      _ = _ := by rw [← Real.exp_neg, ← Real.exp_nat_mul]; congr 1; ring
  change l^(-w.re) ≤ decayRate w^(n+1)*d⁻¹^2
  rw [Real.rpow_def_of_pos hl, decayRate, ← Real.exp_nat_mul, he, ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  nlinarith only [h1,h2]

/-- All even-word fixed-point traces have a geometric absolute mass bound on
`Re w>2`; the bound is uniform across the countable Gauss alphabet. -/
theorem tsum_norm_even_wordTrace_le {w : ℂ} (hw : 2 < w.re) (n : ℕ) :
    (∑' a : Word (2*n+2), ‖wordTrace w (2*n+1) a‖) ≤
      (8/3 : ℝ)*decayRate w^(n+1) := by
  have hc : 0 ≤ (4/3 : ℝ)*decayRate w^(n+1) :=
    mul_nonneg (by norm_num) (pow_nonneg (decayRate_bounds hw).1.le _)
  have hb (a : Word (2*n+2)) : ‖wordTrace w (2*n+1) a‖ ≤
      ((4/3 : ℝ)*decayRate w^(n+1)) * (wordMatrix (2*n+2) a 1 1 : ℝ)⁻¹^2 := by
    calc
      _ ≤ (4/3 : ℝ)*wordMultiplier (2*n+1) a ^ (-w.re) := norm_even_wordTrace_le n a
      _ ≤ (4/3 : ℝ)*(decayRate w^(n+1) * (wordMatrix (2*n+2) a 1 1 : ℝ)⁻¹^2) :=
        mul_le_mul_of_nonneg_left (multiplier_decay_le hw n a) (by norm_num)
      _ = _ := by ring
  have hd := tsum_denominator_inv_sq_le (2*n+2)
  have ht := (summable_wordTrace (show 1 < w.re by linarith only [hw]) (2*n+1)).norm
  calc
    _ ≤ ∑' a : Word (2*n+2), ((4/3 : ℝ)*decayRate w^(n+1)) *
        (wordMatrix (2*n+2) a 1 1 : ℝ)⁻¹^2 := ht.tsum_le_tsum hb (hd.1.mul_left _)
    _ = ((4/3 : ℝ)*decayRate w^(n+1))*
        ∑' a : Word (2*n+2), (wordMatrix (2*n+2) a 1 1 : ℝ)⁻¹^2 := tsum_mul_left
    _ ≤ ((4/3 : ℝ)*decayRate w^(n+1))*2 := mul_le_mul_of_nonneg_left hd.2 hc
    _ = _ := by ring

#print axioms hasSum_successor
#print axioms hasSum_probability
#print axioms tsum_denominator_inv_sq_le
#print axioms even_denominator_growth
#print axioms denominator_le_wordMultiplier
#print axioms decayRate_bounds
#print axioms norm_even_wordTrace_le
#print axioms multiplier_decay_le
#print axioms tsum_norm_even_wordTrace_le
end GaloisForLFunctions.RenormalizedIntersectionTheory.MayerWordProbability
