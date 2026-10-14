import GaloisForLFunctions.RHTower.TwistedArcMomentN1Reduction

/-!
# Second derivatives of the twisted arc vectors and Fourier decay of the witness

The twisted point vector `τ_c` and its derivative are finite sums of monomials `α x^i Q_c(x)^{−1/2−j}`
with `i + 1 ≤ 2j` (`TwistedArcGenerator`).  Differentiating a monomial gives

`α (i x^{i−1} Q^{−1/2−j} − (j + ½)(2x − 2c) x^i Q^{−3/2−j})`   (`monoDeriv`),

a sum of monomials of the same type, so every such monomial is `O(1/(1+x²))` uniformly in
`|c| ≤ ½` (`abs_monoDeriv_le`).  Hence:

* `g_u'' = O(1/(1+x²))` uniformly on the arc (`abs_twArcDeriv2_le`);
* the weighted witness `h = ∫ g(u) g_u dν(u)` is twice differentiable with `h'' = O(1/(1+x²))`
  (`hasDerivAt_twWitnessWDeriv`, `abs_twWitnessWDeriv2_le`);
* its Fourier transform satisfies `|𝓕h(ξ)| ≤ K/(1 + ξ²)` and is integrable
  (`integrable_fourier_twWitnessW`), because `𝓕(h'') = (2πiξ)² 𝓕h`.
-/

open MeasureTheory Set Filter Topology
open scoped FourierTransform

namespace RHTower

noncomputable section

/-! ### Monomials -/

/-- The derivative of the monomial `α x^i Q_c(x)^{−1/2−j}`. -/
def monoDeriv (α : ℝ) (i j : ℕ) (c x : ℝ) : ℝ :=
  α * ((i : ℝ) * x ^ (i - 1) * arcQuadTerm c j x -
    ((j : ℝ) + 1 / 2) * (2 * x - 2 * c) * x ^ i * arcQuadTerm c (j + 1) x)

theorem hasDerivAt_mono {c : ℝ} (hc : |c| < 1) (α : ℝ) (i j : ℕ) (x : ℝ) :
    HasDerivAt (fun x => α * x ^ i * arcQuadTerm c j x) (monoDeriv α i j c x) x := by
  have h := (((hasDerivAt_pow i x).const_mul α).mul (hasDerivAt_arcQuadTerm hc j x))
  refine h.congr_deriv ?_
  unfold monoDeriv
  ring

theorem continuous_monoDeriv {c : ℝ} (hc : |c| < 1) (α : ℝ) (i j : ℕ) :
    Continuous (monoDeriv α i j c) := by
  have h1 := continuous_arcQuadTerm hc j
  have h2 := continuous_arcQuadTerm hc (j + 1)
  unfold monoDeriv
  fun_prop

/-- `|α x^i Q^{−1/2−j}|`-type bound for the derivative of a monomial with `i + 1 ≤ 2j`. -/
theorem abs_monoDeriv_le {c : ℝ} (hc : |c| ≤ 1 / 2) {α : ℝ} (hα : |α| ≤ 945) {i j : ℕ}
    (hi : i ≤ 5) (hj : j ≤ 5) (hij : i + 1 ≤ 2 * j) (x : ℝ) :
    |monoDeriv α i j c x| ≤ 2298240 * (1 + x ^ 2)⁻¹ := by
  have hc1 : |c| < 1 := by linarith
  have hp : 0 < (1 + x ^ 2)⁻¹ := by positivity
  have hT1 := arcQuadTerm_pos hc1 (j + 1) x
  -- the three monomials
  have m2 : |x| ^ (i + 1) * arcQuadTerm c (j + 1) x ≤ 2 ^ (j + 2) * (1 + x ^ 2)⁻¹ :=
    pow_abs_mul_arcQuadTerm_le hc (by omega) x
  have m3 : |x| ^ i * arcQuadTerm c (j + 1) x ≤ 2 ^ (j + 2) * (1 + x ^ 2)⁻¹ :=
    pow_abs_mul_arcQuadTerm_le hc (by omega) x
  have m1 : |(i : ℝ) * x ^ (i - 1) * arcQuadTerm c j x| ≤ 5 * (2 ^ (j + 1) * (1 + x ^ 2)⁻¹) := by
    rcases Nat.eq_zero_or_pos i with rfl | hi0
    · simp only [CharP.cast_eq_zero, zero_mul, abs_zero]; positivity
    · rw [abs_mul, abs_mul, abs_pow, abs_of_pos (arcQuadTerm_pos hc1 j x), Nat.abs_cast,
        mul_assoc]
      have hb := pow_abs_mul_arcQuadTerm_le hc (i := i - 1) (j := j) (by omega) x
      have hi5 : (i : ℝ) ≤ 5 := by exact_mod_cast hi
      exact mul_le_mul hi5 hb
        (mul_nonneg (pow_nonneg (abs_nonneg x) _) (arcQuadTerm_pos hc1 j x).le) (by norm_num)
  have hpow2 : (2 : ℝ) ^ (j + 1) ≤ 64 := by
    calc (2 : ℝ) ^ (j + 1) ≤ 2 ^ 6 := pow_le_pow_right₀ (by norm_num) (by omega)
      _ = 64 := by norm_num
  have hpow3 : (2 : ℝ) ^ (j + 2) ≤ 128 := by
    calc (2 : ℝ) ^ (j + 2) ≤ 2 ^ 7 := pow_le_pow_right₀ (by norm_num) (by omega)
      _ = 128 := by norm_num
  have hjr : (j : ℝ) + 1 / 2 ≤ 11 / 2 := by
    have : (j : ℝ) ≤ 5 := by exact_mod_cast hj
    linarith
  have hsecond : |((j : ℝ) + 1 / 2) * (2 * x - 2 * c) * x ^ i * arcQuadTerm c (j + 1) x| ≤
      11 / 2 * (3 * (128 * (1 + x ^ 2)⁻¹)) := by
    have e : |((j : ℝ) + 1 / 2) * (2 * x - 2 * c) * x ^ i * arcQuadTerm c (j + 1) x| =
        ((j : ℝ) + 1 / 2) * (|2 * x - 2 * c| * (|x| ^ i * arcQuadTerm c (j + 1) x)) := by
      rw [abs_mul, abs_mul, abs_mul, abs_pow, abs_of_pos hT1, abs_of_pos (by positivity)]
      ring
    rw [e]
    have h2x : |2 * x - 2 * c| * (|x| ^ i * arcQuadTerm c (j + 1) x) ≤
        2 * (|x| ^ (i + 1) * arcQuadTerm c (j + 1) x) + (|x| ^ i * arcQuadTerm c (j + 1) x) := by
      have hT := mul_nonneg (pow_nonneg (abs_nonneg x) i) hT1.le
      have habs : |2 * x - 2 * c| ≤ 2 * |x| + 1 := by
        calc |2 * x - 2 * c| ≤ |2 * x| + |2 * c| := abs_sub _ _
          _ ≤ 2 * |x| + 1 := by rw [abs_mul, abs_mul]; norm_num; linarith
      calc |2 * x - 2 * c| * (|x| ^ i * arcQuadTerm c (j + 1) x) ≤
          (2 * |x| + 1) * (|x| ^ i * arcQuadTerm c (j + 1) x) := mul_le_mul_of_nonneg_right habs hT
        _ = _ := by rw [pow_succ]; ring
    have hb : |2 * x - 2 * c| * (|x| ^ i * arcQuadTerm c (j + 1) x) ≤ 3 * (128 * (1 + x ^ 2)⁻¹) := by
      refine h2x.trans ?_
      have := mul_le_mul_of_nonneg_right hpow3 hp.le
      nlinarith
    calc ((j : ℝ) + 1 / 2) * (|2 * x - 2 * c| * (|x| ^ i * arcQuadTerm c (j + 1) x)) ≤
        11 / 2 * (3 * (128 * (1 + x ^ 2)⁻¹)) :=
          mul_le_mul hjr hb (by positivity) (by norm_num)
      _ = _ := rfl
  unfold monoDeriv
  rw [abs_mul]
  calc |α| * |(i : ℝ) * x ^ (i - 1) * arcQuadTerm c j x -
        ((j : ℝ) + 1 / 2) * (2 * x - 2 * c) * x ^ i * arcQuadTerm c (j + 1) x| ≤
      945 * (5 * (64 * (1 + x ^ 2)⁻¹) + 11 / 2 * (3 * (128 * (1 + x ^ 2)⁻¹))) := by
        refine mul_le_mul hα ((abs_sub _ _).trans (add_le_add (m1.trans ?_) hsecond))
          (abs_nonneg _) (by norm_num)
        have := mul_le_mul_of_nonneg_right hpow2 hp.le
        nlinarith
    _ = 2298240 * (1 + x ^ 2)⁻¹ := by ring

/-! ### The second derivative of the twisted point vector -/

/-- The derivative of `τ_c′`. -/
def twPointDeriv2 (c x : ℝ) : ℝ :=
  monoDeriv (4 * c) 0 1 c x + monoDeriv (-(12 * c)) 2 2 c x + monoDeriv (12 * c ^ 2) 1 2 c x +
    monoDeriv (84 * c ^ 2 - 36) 1 2 c x + monoDeriv (-(210 * c ^ 2 - 90)) 3 3 c x +
    monoDeriv (210 * c ^ 3 - 90 * c) 2 3 c x + monoDeriv (360 * c * (c ^ 2 - 1)) 2 3 c x +
    monoDeriv (-(840 * c * (c ^ 2 - 1))) 4 4 c x + monoDeriv (840 * c ^ 2 * (c ^ 2 - 1)) 3 4 c x +
    monoDeriv (420 * (1 - c ^ 2) ^ 2) 3 4 c x + monoDeriv (-(945 * (1 - c ^ 2) ^ 2)) 5 5 c x +
    monoDeriv (945 * c * (1 - c ^ 2) ^ 2) 4 5 c x

theorem hasDerivAt_twPointDeriv {c : ℝ} (hc : |c| < 1) (x : ℝ) :
    HasDerivAt (twPointDeriv c) (twPointDeriv2 c x) x := by
  have h := ((((((((((((hasDerivAt_mono hc (4 * c) 0 1 x).add
    (hasDerivAt_mono hc (-(12 * c)) 2 2 x)).add (hasDerivAt_mono hc (12 * c ^ 2) 1 2 x)).add
    (hasDerivAt_mono hc (84 * c ^ 2 - 36) 1 2 x)).add
    (hasDerivAt_mono hc (-(210 * c ^ 2 - 90)) 3 3 x)).add
    (hasDerivAt_mono hc (210 * c ^ 3 - 90 * c) 2 3 x)).add
    (hasDerivAt_mono hc (360 * c * (c ^ 2 - 1)) 2 3 x)).add
    (hasDerivAt_mono hc (-(840 * c * (c ^ 2 - 1))) 4 4 x)).add
    (hasDerivAt_mono hc (840 * c ^ 2 * (c ^ 2 - 1)) 3 4 x)).add
    (hasDerivAt_mono hc (420 * (1 - c ^ 2) ^ 2) 3 4 x)).add
    (hasDerivAt_mono hc (-(945 * (1 - c ^ 2) ^ 2)) 5 5 x)).add
    (hasDerivAt_mono hc (945 * c * (1 - c ^ 2) ^ 2) 4 5 x))
  have e : twPointDeriv c = fun x =>
      4 * c * x ^ 0 * arcQuadTerm c 1 x + -(12 * c) * x ^ 2 * arcQuadTerm c 2 x +
        12 * c ^ 2 * x ^ 1 * arcQuadTerm c 2 x + (84 * c ^ 2 - 36) * x ^ 1 * arcQuadTerm c 2 x +
        -(210 * c ^ 2 - 90) * x ^ 3 * arcQuadTerm c 3 x +
        (210 * c ^ 3 - 90 * c) * x ^ 2 * arcQuadTerm c 3 x +
        360 * c * (c ^ 2 - 1) * x ^ 2 * arcQuadTerm c 3 x +
        -(840 * c * (c ^ 2 - 1)) * x ^ 4 * arcQuadTerm c 4 x +
        840 * c ^ 2 * (c ^ 2 - 1) * x ^ 3 * arcQuadTerm c 4 x +
        420 * (1 - c ^ 2) ^ 2 * x ^ 3 * arcQuadTerm c 4 x +
        -(945 * (1 - c ^ 2) ^ 2) * x ^ 5 * arcQuadTerm c 5 x +
        945 * c * (1 - c ^ 2) ^ 2 * x ^ 4 * arcQuadTerm c 5 x := by
    funext y
    unfold twPointDeriv
    ring
  rw [e]
  exact h

theorem continuous_twPointDeriv2 {c : ℝ} (hc : |c| < 1) : Continuous (twPointDeriv2 c) := by
  unfold twPointDeriv2
  have := continuous_monoDeriv hc
  fun_prop

/-- `|τ_c″(x)| ≤ 3·10⁷/(1 + x²)` for `|c| ≤ ½`. -/
theorem abs_twPointDeriv2_le {c : ℝ} (hc : |c| ≤ 1 / 2) (x : ℝ) :
    |twPointDeriv2 c x| ≤ 30000000 * (1 + x ^ 2)⁻¹ := by
  have h0 := abs_nonneg c
  have hsq : c ^ 2 ≤ 1 / 4 := by nlinarith [sq_abs c]
  have hsq0 : 0 ≤ c ^ 2 := sq_nonneg c
  have hp : 0 < (1 + x ^ 2)⁻¹ := by positivity
  have k1 : |4 * c| ≤ 945 := by rw [abs_mul]; norm_num; linarith
  have k2 : |-(12 * c)| ≤ 945 := by rw [abs_neg, abs_mul]; norm_num; linarith
  have k3 : |12 * c ^ 2| ≤ 945 := by rw [abs_of_nonneg (by positivity)]; linarith
  have k4 : |84 * c ^ 2 - 36| ≤ 945 := by rw [abs_le]; constructor <;> nlinarith
  have k5 : |-(210 * c ^ 2 - 90)| ≤ 945 := by rw [abs_neg, abs_le]; constructor <;> nlinarith
  have k6 : |210 * c ^ 3 - 90 * c| ≤ 945 := by
    have : 210 * c ^ 3 - 90 * c = c * (210 * c ^ 2 - 90) := by ring
    rw [this, abs_mul]
    have : |210 * c ^ 2 - 90| ≤ 90 := by rw [abs_le]; constructor <;> nlinarith
    nlinarith
  have k7 : |360 * c * (c ^ 2 - 1)| ≤ 945 := by
    rw [abs_mul, abs_mul, abs_of_nonpos (by linarith : c ^ 2 - 1 ≤ 0)]; norm_num; nlinarith
  have k8 : |-(840 * c * (c ^ 2 - 1))| ≤ 945 := by
    rw [abs_neg, abs_mul, abs_mul, abs_of_nonpos (by linarith : c ^ 2 - 1 ≤ 0)]; norm_num
    nlinarith
  have k9 : |840 * c ^ 2 * (c ^ 2 - 1)| ≤ 945 := by
    rw [abs_mul, abs_of_nonpos (by linarith : c ^ 2 - 1 ≤ 0), abs_of_nonneg (by positivity)]
    nlinarith
  have k10 : |420 * (1 - c ^ 2) ^ 2| ≤ 945 := by
    rw [abs_of_nonneg (by positivity)]; nlinarith [sq_nonneg (1 - c ^ 2)]
  have k11 : |-(945 * (1 - c ^ 2) ^ 2)| ≤ 945 := by
    rw [abs_neg, abs_of_nonneg (by positivity)]; nlinarith [sq_nonneg (1 - c ^ 2)]
  have k12 : |945 * c * (1 - c ^ 2) ^ 2| ≤ 945 := by
    rw [abs_mul, abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (1 - c ^ 2) ^ 2)]
    norm_num
    have : (1 - c ^ 2) ^ 2 ≤ 1 := by nlinarith
    nlinarith
  have b1 := abs_monoDeriv_le hc k1 (i := 0) (j := 1) (by norm_num) (by norm_num) (by norm_num) x
  have b2 := abs_monoDeriv_le hc k2 (i := 2) (j := 2) (by norm_num) (by norm_num) (by norm_num) x
  have b3 := abs_monoDeriv_le hc k3 (i := 1) (j := 2) (by norm_num) (by norm_num) (by norm_num) x
  have b4 := abs_monoDeriv_le hc k4 (i := 1) (j := 2) (by norm_num) (by norm_num) (by norm_num) x
  have b5 := abs_monoDeriv_le hc k5 (i := 3) (j := 3) (by norm_num) (by norm_num) (by norm_num) x
  have b6 := abs_monoDeriv_le hc k6 (i := 2) (j := 3) (by norm_num) (by norm_num) (by norm_num) x
  have b7 := abs_monoDeriv_le hc k7 (i := 2) (j := 3) (by norm_num) (by norm_num) (by norm_num) x
  have b8 := abs_monoDeriv_le hc k8 (i := 4) (j := 4) (by norm_num) (by norm_num) (by norm_num) x
  have b9 := abs_monoDeriv_le hc k9 (i := 3) (j := 4) (by norm_num) (by norm_num) (by norm_num) x
  have b10 := abs_monoDeriv_le hc k10 (i := 3) (j := 4) (by norm_num) (by norm_num) (by norm_num) x
  have b11 := abs_monoDeriv_le hc k11 (i := 5) (j := 5) (by norm_num) (by norm_num) (by norm_num) x
  have b12 := abs_monoDeriv_le hc k12 (i := 4) (j := 5) (by norm_num) (by norm_num) (by norm_num) x
  unfold twPointDeriv2
  set t1 := monoDeriv (4 * c) 0 1 c x
  set t2 := monoDeriv (-(12 * c)) 2 2 c x
  set t3 := monoDeriv (12 * c ^ 2) 1 2 c x
  set t4 := monoDeriv (84 * c ^ 2 - 36) 1 2 c x
  set t5 := monoDeriv (-(210 * c ^ 2 - 90)) 3 3 c x
  set t6 := monoDeriv (210 * c ^ 3 - 90 * c) 2 3 c x
  set t7 := monoDeriv (360 * c * (c ^ 2 - 1)) 2 3 c x
  set t8 := monoDeriv (-(840 * c * (c ^ 2 - 1))) 4 4 c x
  set t9 := monoDeriv (840 * c ^ 2 * (c ^ 2 - 1)) 3 4 c x
  set t10 := monoDeriv (420 * (1 - c ^ 2) ^ 2) 3 4 c x
  set t11 := monoDeriv (-(945 * (1 - c ^ 2) ^ 2)) 5 5 c x
  set t12 := monoDeriv (945 * c * (1 - c ^ 2) ^ 2) 4 5 c x
  have a2 := abs_add_le t1 t2
  have a3 := abs_add_le (t1 + t2) t3
  have a4 := abs_add_le (t1 + t2 + t3) t4
  have a5 := abs_add_le (t1 + t2 + t3 + t4) t5
  have a6 := abs_add_le (t1 + t2 + t3 + t4 + t5) t6
  have a7 := abs_add_le (t1 + t2 + t3 + t4 + t5 + t6) t7
  have a8 := abs_add_le (t1 + t2 + t3 + t4 + t5 + t6 + t7) t8
  have a9 := abs_add_le (t1 + t2 + t3 + t4 + t5 + t6 + t7 + t8) t9
  have a10 := abs_add_le (t1 + t2 + t3 + t4 + t5 + t6 + t7 + t8 + t9) t10
  have a11 := abs_add_le (t1 + t2 + t3 + t4 + t5 + t6 + t7 + t8 + t9 + t10) t11
  have a12 := abs_add_le (t1 + t2 + t3 + t4 + t5 + t6 + t7 + t8 + t9 + t10 + t11) t12
  nlinarith

/-! ### The arc vectors -/

/-- `g_u″`. -/
def twArcDeriv2 (u : ArcParam) (x : ℝ) : ℝ :=
  Real.sqrt (modularArcHeight u) * (twPointDeriv2 u x + twPointDeriv2 (-u) x)

theorem hasDerivAt_twArcDeriv (u : ArcParam) (x : ℝ) :
    HasDerivAt (twArcDeriv u) (twArcDeriv2 u x) x := by
  have hu := abs_arcParam_lt u
  have hu' : |-(u : ℝ)| < 1 := by rwa [abs_neg]
  exact ((hasDerivAt_twPointDeriv hu x).add (hasDerivAt_twPointDeriv hu' x)).const_mul _

theorem abs_twArcDeriv2_le (u : ArcParam) (x : ℝ) :
    |twArcDeriv2 u x| ≤ 60000000 * (1 + x ^ 2)⁻¹ := by
  have h1 := abs_twPointDeriv2_le (abs_arcParam_le u) x
  have h2 := abs_twPointDeriv2_le (abs_neg_arcParam_le u) x
  have hs := sqrt_modularArcHeight_le_one u
  have hs0 := Real.sqrt_nonneg (modularArcHeight u)
  unfold twArcDeriv2
  rw [abs_mul, abs_of_nonneg hs0]
  calc Real.sqrt (modularArcHeight u) * |twPointDeriv2 u x + twPointDeriv2 (-u) x|
      ≤ 1 * (30000000 * (1 + x ^ 2)⁻¹ + 30000000 * (1 + x ^ 2)⁻¹) :=
        mul_le_mul hs ((abs_add_le _ _).trans (add_le_add h1 h2)) (abs_nonneg _) zero_le_one
    _ = _ := by ring

theorem continuous_twArcDeriv2_param :
    Continuous fun p : ℝ × ArcParam => twArcDeriv2 p.2 p.1 := by
  have h1 := continuous_arcQuadTerm_param 1
  have h2 := continuous_arcQuadTerm_param 2
  have h3 := continuous_arcQuadTerm_param 3
  have h4 := continuous_arcQuadTerm_param 4
  have h5 := continuous_arcQuadTerm_param 5
  have h6 := continuous_arcQuadTerm_param 6
  have g1 := continuous_arcQuadTerm_param_neg 1
  have g2 := continuous_arcQuadTerm_param_neg 2
  have g3 := continuous_arcQuadTerm_param_neg 3
  have g4 := continuous_arcQuadTerm_param_neg 4
  have g5 := continuous_arcQuadTerm_param_neg 5
  have g6 := continuous_arcQuadTerm_param_neg 6
  have hy : Continuous fun p : ℝ × ArcParam => Real.sqrt (modularArcHeight p.2) := by
    unfold modularArcHeight; fun_prop
  unfold twArcDeriv2 twPointDeriv2 monoDeriv
  simp only [Nat.cast_ofNat, Nat.cast_one, Nat.cast_zero, Nat.reduceAdd]
  fun_prop

theorem continuous_twArcDeriv2_at (x : ℝ) : Continuous fun u : ArcParam => twArcDeriv2 u x :=
  continuous_twArcDeriv2_param.comp (continuous_const.prodMk continuous_id)

theorem continuous_twArcDeriv2 (u : ArcParam) : Continuous (twArcDeriv2 u) :=
  continuous_twArcDeriv2_param.comp (continuous_id.prodMk continuous_const)

/-! ### The witness -/

section Weighted

variable {ν : Measure ArcParam} [IsFiniteMeasure ν] {g : ArcParam → ℝ} {B : ℝ}

/-- The second derivative `∫ g(u) g_u″ dν(u)` of the weighted witness. -/
def twWitnessWDeriv2 (ν : Measure ArcParam) (g : ArcParam → ℝ) (x : ℝ) : ℝ :=
  ∫ u, g u * twArcDeriv2 u x ∂ν

theorem hasDerivAt_twWitnessWDeriv (hg : Measurable g) (hgB : ∀ u, |g u| ≤ B) (x : ℝ) :
    HasDerivAt (twWitnessWDeriv ν g) (twWitnessWDeriv2 ν g x) x := by
  have hB0 : 0 ≤ B := (abs_nonneg _).trans (hgB arcZeroPt)
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := ν)
    (F := fun (x : ℝ) (u : ArcParam) => g u * twArcDeriv u x)
    (F' := fun x u => g u * twArcDeriv2 u x) (x₀ := x) (bound := fun _ => B * 60000000)
    (s := univ) Filter.univ_mem
    (Eventually.of_forall fun x' =>
      (hg.mul (continuous_twArcDeriv_at x').measurable).aestronglyMeasurable)
    (integrable_g_mul_of_bound hg hgB (continuous_twArcDeriv_at x)
      (C := 260000) fun u => (abs_twArcDeriv_le u x).trans (by
        have : (1 + x ^ 2)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by nlinarith [sq_nonneg x])
        nlinarith))
    (hg.mul (continuous_twArcDeriv2_at x).measurable).aestronglyMeasurable
    (Eventually.of_forall fun u x' _ => by
      rw [Real.norm_eq_abs, abs_mul]
      refine mul_le_mul (hgB u) ((abs_twArcDeriv2_le u x').trans ?_) (abs_nonneg _) hB0
      have : (1 + x' ^ 2)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by nlinarith [sq_nonneg x'])
      nlinarith)
    (integrable_const _)
    (Eventually.of_forall fun u x' _ => (hasDerivAt_twArcDeriv u x').const_mul (g u))
  exact key.2

theorem abs_twWitnessWDeriv2_le (hgB : ∀ u, |g u| ≤ B) (x : ℝ) :
    |twWitnessWDeriv2 ν g x| ≤ B * ν.real univ * 60000000 * (1 + x ^ 2)⁻¹ := by
  have hB0 : 0 ≤ B := (abs_nonneg _).trans (hgB arcZeroPt)
  have h := norm_integral_le_of_norm_le_const (μ := ν)
    (f := fun u => g u * twArcDeriv2 u x) (C := B * (60000000 * (1 + x ^ 2)⁻¹))
    (Eventually.of_forall fun u => by
      rw [Real.norm_eq_abs, abs_mul]
      exact mul_le_mul (hgB u) (abs_twArcDeriv2_le u x) (abs_nonneg _) hB0)
  rw [Real.norm_eq_abs] at h
  unfold twWitnessWDeriv2
  calc _ ≤ B * (60000000 * (1 + x ^ 2)⁻¹) * ν.real univ := h
    _ = _ := by ring

theorem continuous_twWitnessWDeriv2 (hg : Measurable g) (hgB : ∀ u, |g u| ≤ B) :
    Continuous (twWitnessWDeriv2 ν g) := by
  have hB0 : 0 ≤ B := (abs_nonneg _).trans (hgB arcZeroPt)
  unfold twWitnessWDeriv2
  refine continuous_of_dominated (bound := fun _ => B * 60000000) (fun x => ?_)
    (fun x => Eventually.of_forall fun u => ?_) (integrable_const _)
    (Eventually.of_forall fun u => ?_)
  · exact (hg.mul (continuous_twArcDeriv2_at x).measurable).aestronglyMeasurable
  · rw [Real.norm_eq_abs, abs_mul]
    refine mul_le_mul (hgB u) ((abs_twArcDeriv2_le u x).trans ?_) (abs_nonneg _) hB0
    have : (1 + x ^ 2)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by nlinarith [sq_nonneg x])
    nlinarith
  · exact continuous_const.mul (continuous_twArcDeriv2 u)

/-! ### Fourier decay -/

theorem norm_fourier_le_integral_norm_twArc (f : ℝ → ℂ) (ξ : ℝ) : ‖𝓕 f ξ‖ ≤ ∫ x, ‖f x‖ :=
  VectorFourier.norm_fourierIntegral_le_integral_norm _ _ _ _ _

theorem integrable_of_abs_le_mul_inv_one_add_sq {f : ℝ → ℝ} (hf : Continuous f) {C : ℝ}
    (hC : ∀ x, |f x| ≤ C * (1 + x ^ 2)⁻¹) : Integrable f :=
  (integrable_inv_one_add_sq.const_mul C).mono' hf.aestronglyMeasurable
    (Eventually.of_forall fun x => by rw [Real.norm_eq_abs]; exact hC x)

/-- **Quadratic Fourier decay of the weighted witness**:
`(1 + ξ²) |𝓕h(ξ)| ≤ ∫|h| + ∫|h″|/(4π²)`. -/
theorem norm_fourier_twWitnessW_le (hg : Measurable g) (hgB : ∀ u, |g u| ≤ B) (ξ : ℝ) :
    ‖𝓕 (fun x => (twWitnessW ν g x : ℂ)) ξ‖ ≤
      ((∫ x, |twWitnessW ν g x|) + (∫ x, |twWitnessWDeriv2 ν g x|) / (4 * Real.pi ^ 2)) *
        (1 + ξ ^ 2)⁻¹ := by
  set F : ℝ → ℂ := fun x => (twWitnessW ν g x : ℂ) with hF
  set F1 : ℝ → ℂ := fun x => (twWitnessWDeriv ν g x : ℂ) with hF1
  set F2 : ℝ → ℂ := fun x => (twWitnessWDeriv2 ν g x : ℂ) with hF2
  have hd0 : ∀ x, HasDerivAt F (F1 x) x := fun x =>
    (hasDerivAt_twWitnessW hg hgB x).ofReal_comp
  have hd1 : ∀ x, HasDerivAt F1 (F2 x) x := fun x =>
    (hasDerivAt_twWitnessWDeriv hg hgB x).ofReal_comp
  have hderiv0 : deriv F = F1 := funext fun x => (hd0 x).deriv
  have hderiv1 : deriv F1 = F2 := funext fun x => (hd1 x).deriv
  have hc0 := continuous_twWitnessW (ν := ν) hg hgB
  have hc1 := continuous_twWitnessWDeriv (ν := ν) hg hgB
  have hc2 := continuous_twWitnessWDeriv2 (ν := ν) hg hgB
  have hi0 : Integrable (twWitnessW ν g) :=
    integrable_of_abs_le_mul_inv_one_add_sq hc0 (abs_twWitnessW_le hgB)
  have hi1 : Integrable (twWitnessWDeriv ν g) :=
    integrable_of_abs_le_mul_inv_one_add_sq hc1 (abs_twWitnessWDeriv_le hgB)
  have hi2 : Integrable (twWitnessWDeriv2 ν g) :=
    integrable_of_abs_le_mul_inv_one_add_sq hc2 (abs_twWitnessWDeriv2_le hgB)
  have hI0 : Integrable F := hi0.ofReal
  have hI1 : Integrable F1 := hi1.ofReal
  have hI2 : Integrable F2 := hi2.ofReal
  have hD0 : Differentiable ℝ F := fun x => (hd0 x).differentiableAt
  have hD1 : Differentiable ℝ F1 := fun x => (hd1 x).differentiableAt
  have e1 := Real.fourier_deriv hI0 hD0 (by rw [hderiv0]; exact hI1)
  have e2 := Real.fourier_deriv hI1 hD1 (by rw [hderiv1]; exact hI2)
  rw [hderiv0] at e1
  rw [hderiv1] at e2
  have hrel : 𝓕 F2 ξ = (2 * (Real.pi : ℂ) * Complex.I * ξ) ^ 2 * 𝓕 F ξ := by
    rw [congrFun e2 ξ, congrFun e1 ξ, smul_eq_mul, smul_eq_mul]; ring
  have hb0 : ‖𝓕 F ξ‖ ≤ ∫ x, |twWitnessW ν g x| := by
    refine (norm_fourier_le_integral_norm_twArc F ξ).trans (le_of_eq ?_)
    congr 1; funext x; simp [hF]
  have hb2 : ‖𝓕 F2 ξ‖ ≤ ∫ x, |twWitnessWDeriv2 ν g x| := by
    refine (norm_fourier_le_integral_norm_twArc F2 ξ).trans (le_of_eq ?_)
    congr 1; funext x; simp [hF2]
  have hnorm2 : ‖𝓕 F2 ξ‖ = 4 * Real.pi ^ 2 * ξ ^ 2 * ‖𝓕 F ξ‖ := by
    rw [hrel, norm_mul, norm_pow]
    have : ‖2 * (Real.pi : ℂ) * Complex.I * ξ‖ = 2 * Real.pi * |ξ| := by
      rw [norm_mul, norm_mul, norm_mul, Complex.norm_I, Complex.norm_real, Complex.norm_ofNat,
        Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos Real.pi_pos]
      ring
    rw [this, mul_pow, mul_pow, sq_abs]
    ring
  have hpi : 0 < 4 * Real.pi ^ 2 := by positivity
  have hξ : 0 < 1 + ξ ^ 2 := by positivity
  rw [le_mul_inv_iff₀ hξ]
  have h2 : ξ ^ 2 * ‖𝓕 F ξ‖ ≤ (∫ x, |twWitnessWDeriv2 ν g x|) / (4 * Real.pi ^ 2) := by
    rw [le_div_iff₀ hpi]
    nlinarith [hnorm2, hb2]
  nlinarith [hb0, h2, norm_nonneg (𝓕 F ξ)]

/-- **The Fourier transform of the weighted witness is integrable.** -/
theorem integrable_fourier_twWitnessW (hg : Measurable g) (hgB : ∀ u, |g u| ≤ B) :
    Integrable (𝓕 (fun x => (twWitnessW ν g x : ℂ))) := by
  have hc0 := continuous_twWitnessW (ν := ν) hg hgB
  have hi0 : Integrable fun x => (twWitnessW ν g x : ℂ) :=
    (integrable_of_abs_le_mul_inv_one_add_sq hc0 (abs_twWitnessW_le hgB)).ofReal
  have hcont : Continuous (𝓕 (fun x => (twWitnessW ν g x : ℂ))) :=
    VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar
      (innerSL ℝ).continuous₂ hi0
  exact (integrable_inv_one_add_sq.const_mul ((∫ x, |twWitnessW ν g x|) +
    (∫ x, |twWitnessWDeriv2 ν g x|) / (4 * Real.pi ^ 2))).mono' hcont.aestronglyMeasurable
    (Eventually.of_forall fun ξ => norm_fourier_twWitnessW_le hg hgB ξ)

end Weighted

end

end RHTower
