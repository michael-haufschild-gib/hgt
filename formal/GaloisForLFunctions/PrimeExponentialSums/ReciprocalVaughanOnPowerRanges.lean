import GaloisForLFunctions.RHTower.Sieve.KubalalikaFibreCondition
import GaloisForLFunctions.RHTower.Sieve.KubalalikaLargeScale
import Mathlib.Analysis.Calculus.Deriv.Slope

/-!
# Reciprocal Vaughan sums on power ranges

The logarithmic phase tends to the reciprocal phase while the product
of frequency and shift stays fixed. This preserves all five terms of the
mixed Vaughan bound on every sharp subinterval.
-/

noncomputable section
open Filter Finset ArithmeticFunction RHTower RHTower.Sieve Topology
namespace GaloisForLFunctions.PrimeExponentialSums

private theorem tendsto_logarithmic_phase (S : ℝ) (n : ℕ) :
    Tendsto (fun r : ℝ => ndPhaseExp (S/r) r n) (𝓝[>] 0) (𝓝 (Complex.exp (((S/(n:ℝ):ℝ):ℂ)*Complex.I))) := by
  have hd : HasDerivAt (fun r : ℝ => Real.log (1+r/(n : ℝ))) (1/(n : ℝ)) 0 := by
    simpa using (((hasDerivAt_const (0 : ℝ) (1 : ℝ)).add
      ((hasDerivAt_id (0 : ℝ)).div_const (n : ℝ))).log (by simp))
  have hsl : Tendsto (fun r : ℝ => r⁻¹ * Real.log (1+r/n)) (𝓝[>] 0) (𝓝 (1/(n : ℝ))) := by
    simpa only [zero_add,zero_div,add_zero,Real.log_one,sub_zero,smul_eq_mul] using hd.tendsto_slope_zero_right
  have hc (t : ℝ) : 2*Real.pi*(t/(2*Real.pi)) = t := by field_simp
  have hp (r : ℝ) : 2*Real.pi*nearDiagonalPhase (S/r) r n = S*(r⁻¹*Real.log (1+r/n)) := by
    unfold nearDiagonalPhase
    rw [← mul_assoc, hc]
    ring
  simp only [ndPhaseExp,RHTower.Sieve.phaseExp,hp]
  have h := (Complex.continuous_ofReal.continuousAt.tendsto.comp ((tendsto_const_nhds (x := S)).mul hsl)).mul
    (tendsto_const_nhds (x := Complex.I))
  simpa only [Function.comp_def, mul_one_div] using Complex.continuous_exp.continuousAt.tendsto.comp h

/-- Preserve the full Vaughan estimate when the logarithmic phase tends to
a reciprocal phase, with no error depending on the block length. -/
theorem reciprocal_vaughan_envelope :
    ∃ D : ℝ, 0 < D ∧ ∀ {S : ℝ} {A B U V : ℕ},
      0 < S → 1 ≤ A → A ≤ B → B ≤ 2*A → 1 ≤ U → 1 ≤ V → U < A →
      U*V ≤ A → S*((U*V : ℕ) : ℝ)^3 ≤ 72*Real.pi*(A : ℝ)^4 →
      (10 : ℝ)^27 * A ≤ S →
      ‖∑ n ∈ Ico A B, (vonMangoldt n : ℂ)*Complex.exp (((S/(n:ℝ):ℝ):ℂ)*Complex.I)‖ ≤
        kubalalikaBlockPower D S 1 A B U V := by
  obtain ⟨D,hD,h⟩ := exists_norm_sum_vonMangoldt_ndPhaseExp_le_kubalalika_power'
  refine ⟨D,hD,?_⟩
  intro S A B U V hS hA hAB hB hU hV hu huv hcur hbig
  have ht := tendsto_finsetSum (Ico A B) fun n _ =>
    (tendsto_const_nhds (x := (vonMangoldt n : ℂ))).mul (tendsto_logarithmic_phase S n)
  apply le_of_tendsto ht.norm
  have ha : (0 : ℝ) < A := by exact_mod_cast hA
  have hA0 : 0 < (A : ℝ)/8 := by positivity
  have hsmall : ∀ᶠ r : ℝ in 𝓝[>] 0, r < (A : ℝ)/8 :=
    mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds hA0)
  filter_upwards [self_mem_nhdsWithin,hsmall] with r hr hsmall
  change 0 < r at hr
  have he : S/r*r = S := div_mul_cancel₀ _ hr.ne'
  have hh := h (T := S/r) (r := r) (div_pos hS hr) hr hA hAB hB hU hV hu huv
    (by linarith only [hsmall]) (by simpa only [he] using hcur) (by simpa only [he] using hbig)
  simpa only [kubalalikaBlockPower, he, mul_one] using hh

#print axioms reciprocal_vaughan_envelope

/-- The five exponents in the mixed Vaughan estimate when the block,
frequency and factor cutoffs are bounded by powers of a common scale. -/
def reciprocalVaughanExponent (a lo hi u v upperUV : ℝ) : ℝ :=
  max (a/3+hi/6+upperUV/2) (max (3*a/2-lo/2)
    (max (a-v/2) (max (hi/4+3*a/4-u/2) (a-u/2))))

/-- Power accounting for the complete mixed Vaughan bound, at a sharp
terminal B. The lower frequency is used by the inverse-frequency term. -/
theorem reciprocal_vaughan_power_account {D x S a lo hi u v upperUV : ℝ}
    {A B U V : ℕ} (hD : 0 ≤ D) (hx : 1 ≤ x) (hAB : A ≤ B) (hB : (B:ℝ) ≤ x^a)
    (hlo : x^lo ≤ S) (hhi : S ≤ x^hi) (hU : x^u ≤ U) (hV : x^v ≤ V)
    (hUV : ((U*V:ℕ):ℝ) ≤ x^upperUV) :
    kubalalikaBlockPower D S 1 A B U V ≤
      5*D*(1+Real.log B)^4*x^(reciprocalVaughanExponent a lo hi u v upperUV) := by
  let P (z : ℝ) := x^z
  have hx0 : 0 < x := zero_lt_one.trans_le hx
  have pos (z : ℝ) : 0 < P z := Real.rpow_pos_of_pos hx0 _
  have mono {z w : ℝ} (h : z ≤ w) : P z ≤ P w := Real.rpow_le_rpow_of_exponent_le hx h
  have mult (z w : ℝ) : P z*P w=P (z+w) := (Real.rpow_add hx0 _ _).symm
  have up {y z e : ℝ} (hy : 0 ≤ y) (h : y ≤ P z) (he : 0 ≤ e) : y^e ≤ P (z*e) := by
    calc y^e ≤ (P z)^e := Real.rpow_le_rpow hy h he
         _ = _ := (Real.rpow_mul hx0.le _ _).symm
  have down {y z e : ℝ} (h : P z ≤ y) (he : e ≤ 0) : y^e ≤ P (z*e) := by
    calc y^e ≤ (P z)^e := Real.rpow_le_rpow_of_nonpos (pos z) h he
         _ = _ := (Real.rpow_mul hx0.le _ _).symm
  let t := reciprocalVaughanExponent a lo hi u v upperUV
  have ht : a/3+hi/6+upperUV/2 ≤ t ∧ 3*a/2-lo/2 ≤ t ∧ a-v/2 ≤ t ∧ hi/4+3*a/4-u/2 ≤ t ∧ a-u/2 ≤ t := by
    dsimp only [t,reciprocalVaughanExponent]
    exact ⟨le_max_left _ _,(le_max_left _ _).trans (le_max_right _ _),
      ((le_max_left _ _).trans (le_max_right _ _)).trans (le_max_right _ _),
      (((le_max_left _ _).trans (le_max_right _ _)).trans (le_max_right _ _)).trans (le_max_right _ _),
      (((le_max_right _ _).trans (le_max_right _ _)).trans (le_max_right _ _)).trans (le_max_right _ _)⟩
  have hS : 0 < S := (pos _).trans_le hlo
  have huV : (0:ℝ) < U := (pos _).trans_le hU
  have hvV : (0:ℝ) < V := (pos _).trans_le hV
  have t1 : (A:ℝ)^(1/3:ℝ)*S^(1/6:ℝ)*Real.sqrt (U*V:ℕ) ≤ P t := by
    rw [Real.sqrt_eq_rpow]
    calc _ ≤ P (a*(1/3))*P (hi*(1/6))*P (upperUV*(1/2)) := by
               apply mul_le_mul
               · exact mul_le_mul (up (Nat.cast_nonneg _) ((Nat.cast_le.mpr hAB).trans hB) (by norm_num))
                   (up hS.le hhi (by norm_num)) (by positivity) (pos _).le
               · exact up (by positivity) hUV (by norm_num)
               · positivity
               · exact mul_nonneg (pos _).le (pos _).le
         _ ≤ _ := by rw [mult,mult]; apply mono; linarith only [ht.1]
  have t2 : (B:ℝ)^(3/2:ℝ)*S^(-(1/2):ℝ) ≤ P t := by
    calc _ ≤ P (a*(3/2))*P (lo*(-(1/2))) := mul_le_mul (up (Nat.cast_nonneg _) hB (by norm_num))
             (down hlo (by norm_num)) (by positivity) (pos _).le
         _ ≤ _ := by rw [mult]; apply mono; linarith only [ht.2.1]
  have t3 : (B:ℝ)*(V:ℝ)^(-(1/2):ℝ) ≤ P t := by
    calc _ ≤ P a*P (v*(-(1/2))) := mul_le_mul hB (down hV (by norm_num)) (by positivity) (pos _).le
         _ ≤ _ := by rw [mult]; apply mono; linarith only [ht.2.2.1]
  have t4 : S^(1/4:ℝ)*(B:ℝ)^(3/4:ℝ)*(U:ℝ)^(-(1/2):ℝ) ≤ P t := by
    calc _ ≤ P (hi*(1/4))*P (a*(3/4))*P (u*(-(1/2))) := by
               apply mul_le_mul
               · exact mul_le_mul (up hS.le hhi (by norm_num)) (up (Nat.cast_nonneg _) hB (by norm_num))
                   (by positivity) (pos _).le
               · exact down hU (by norm_num)
               · positivity
               · exact mul_nonneg (pos _).le (pos _).le
         _ ≤ _ := by rw [mult,mult]; apply mono; linarith only [ht.2.2.2.1]
  have t5 : (B:ℝ)*(U:ℝ)^(-(1/2):ℝ) ≤ P t := by
    calc _ ≤ P a*P (u*(-(1/2))) := mul_le_mul hB (down hU (by norm_num)) (by positivity) (pos _).le
         _ ≤ _ := by rw [mult]; apply mono; linarith only [ht.2.2.2.2]
  simp only [kubalalikaBlockPower,mul_one]
  calc _ ≤ D*(1+Real.log B)^4*(5*P t) := by
          apply mul_le_mul_of_nonneg_left _ (mul_nonneg hD (by positivity))
          push_cast at t1
          linarith only [t1,t2,t3,t4,t5]
       _ = _ := by change _ = 5*D*(1+Real.log B)^4*P t; ring

#print axioms reciprocal_vaughan_power_account

/-- Prime scale paid by the mixed Vaughan bound and finite sawtooth
smoothing at target exponent t. -/
def reflectedPrimeShellExponent (t : ℝ) := min ((46*t-5)/35) ((2*t+1)/3)

/-- The two factor lengths fit below the lower block and meet the strict
curvature condition. All five terms then have exponent at most t. -/
theorem reflected_prime_shell_exponents {t : ℝ} (hhalf : 1/2 ≤ t) (hone : t < 1) :
    let a := reflectedPrimeShellExponent t
    let b := 2*(a-t)
    let u := 1/2+5*a/2-3*t
    let v := 2*(a-t)
    t < a ∧ a < 1 ∧ 0 < u ∧ 0 < v ∧ u+v < t ∧
      1+b+3*(u+v) < 4*t ∧ reciprocalVaughanExponent a 1 (1+b) u v (u+v) ≤ t := by
  dsimp only [reflectedPrimeShellExponent,reciprocalVaughanExponent]
  rcases le_total ((46*t-5)/35) ((2*t+1)/3) with h | h
  · simp only [min_eq_left h,max_le_iff]
    repeat' apply And.intro
    all_goals linarith only [hhalf,hone,h]
  · simp only [min_eq_right h,max_le_iff]
    repeat' apply And.intro
    all_goals linarith only [hhalf,hone,h]

theorem reflected_prime_shell_at_half : reflectedPrimeShellExponent (1/2)=18/35 := by
  norm_num [reflectedPrimeShellExponent]

theorem reflected_prime_shell_at_five_sixths : reflectedPrimeShellExponent (5/6)=8/9 := by
  norm_num [reflectedPrimeShellExponent]

#print axioms reflected_prime_shell_exponents

end GaloisForLFunctions.PrimeExponentialSums
