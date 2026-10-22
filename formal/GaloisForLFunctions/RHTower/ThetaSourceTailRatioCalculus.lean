import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspDerivativeTailPositivity

/-!
# Tail ratio calculus for the literal theta source

On the positive tail, with first-atom scale `q = π e^{2x}`, a function is *negligible* if
`q^s f → 0` for every `s` and *moderate* if `|f| ≤ C q^d` eventually. Negligible functions form an
ideal over the moderate ones, giving a closeness calculus stable under sums, products, squares and
quotients by eventually large denominators.

Every source ratio `σ_j = k^{(j)}/k` is negligibly close to the first-atom ratio
`π_j = P_j(e^x)/P_0(e^x)`. The source recursion `P_{n+1} = P_n/2 + yP_n' - 2πy²P_n` turns the
model quantities into logarithmic derivatives of `P(e^x)`, whose limits are read off from degrees.
Consequences for `r = 4m`: `σ_{r+1}/σ_r - σ_1 → 2r`, the logarithmic curvature of `σ_r` tends to
zero, and `(log k)'' + 4π e^{2x} → 0`.
-/
open Filter Topology Polynomial

namespace RHTower

noncomputable section

/-! ## Negligible and moderate functions on the positive tail -/

/-- `f` is negligible on the positive tail: `q^s f → 0` for every `s`, where
`q(x) = π e^{2x}` is the first-atom scale. -/
def ThetaTailNegligible (f : ℝ → ℝ) : Prop :=
  ∀ s : ℕ, Tendsto (fun x => thetaCuspSingleAtomReflectionScale 1 x ^ s * f x) atTop (𝓝 0)

/-- `f` is moderate on the positive tail: `|f| ≤ C q^d` eventually. -/
def ThetaTailModerate (f : ℝ → ℝ) : Prop :=
  ∃ C : ℝ, ∃ d : ℕ, ∀ᶠ x in atTop, |f x| ≤ C * thetaCuspSingleAtomReflectionScale 1 x ^ d

theorem thetaTailScale_pos (x : ℝ) : 0 < thetaCuspSingleAtomReflectionScale 1 x := by
  unfold thetaCuspSingleAtomReflectionScale
  positivity

theorem thetaTailScale_eq (x : ℝ) :
    thetaCuspSingleAtomReflectionScale 1 x = Real.pi * Real.exp x ^ 2 := by
  unfold thetaCuspSingleAtomReflectionScale
  rw [← Real.exp_nat_mul]
  push_cast
  ring_nf

theorem eventually_one_le_thetaTailScale :
    ∀ᶠ x in atTop, 1 ≤ thetaCuspSingleAtomReflectionScale 1 x := by
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with x hx
  have := three_lt_thetaCuspSingleAtomReflectionScale (n := 1) (by norm_num) hx
  linarith

theorem tendsto_thetaTailScale :
    Tendsto (thetaCuspSingleAtomReflectionScale 1) atTop atTop := by
  have h : Tendsto (fun x : ℝ => Real.pi * Real.exp (2 * x)) atTop atTop :=
    (Real.tendsto_exp_atTop.comp (tendsto_id.const_mul_atTop two_pos)).const_mul_atTop
      Real.pi_pos
  refine h.congr fun x => ?_
  unfold thetaCuspSingleAtomReflectionScale
  simp

namespace ThetaTailNegligible

variable {f g : ℝ → ℝ}

theorem tendsto (hf : ThetaTailNegligible f) : Tendsto f atTop (𝓝 0) := by
  simpa using hf 0

theorem zero : ThetaTailNegligible (fun _ => 0) := fun s => by simp

theorem add (hf : ThetaTailNegligible f) (hg : ThetaTailNegligible g) :
    ThetaTailNegligible (fun x => f x + g x) := fun s => by
  simpa [mul_add] using (hf s).add (hg s)

theorem neg (hf : ThetaTailNegligible f) : ThetaTailNegligible (fun x => -f x) := fun s => by
  simpa using (hf s).neg

theorem sub (hf : ThetaTailNegligible f) (hg : ThetaTailNegligible g) :
    ThetaTailNegligible (fun x => f x - g x) := by
  simpa [sub_eq_add_neg] using hf.add hg.neg

theorem const_mul (hf : ThetaTailNegligible f) (c : ℝ) :
    ThetaTailNegligible (fun x => c * f x) := fun s => by
  simpa [mul_left_comm] using (hf s).const_mul c

theorem congr' (hf : ThetaTailNegligible f) (h : f =ᶠ[atTop] g) : ThetaTailNegligible g :=
  fun s => (hf s).congr' (h.mono fun x hx => by rw [hx])

end ThetaTailNegligible

namespace ThetaTailModerate

variable {f g : ℝ → ℝ}

theorem const (c : ℝ) : ThetaTailModerate (fun _ => c) :=
  ⟨|c|, 0, Eventually.of_forall fun x => by simp⟩

theorem scale_pow (d : ℕ) :
    ThetaTailModerate (fun x => thetaCuspSingleAtomReflectionScale 1 x ^ d) :=
  ⟨1, d, Eventually.of_forall fun x => by
    rw [one_mul, abs_of_nonneg (pow_nonneg (thetaTailScale_pos x).le d)]⟩

theorem add (hf : ThetaTailModerate f) (hg : ThetaTailModerate g) :
    ThetaTailModerate (fun x => f x + g x) := by
  obtain ⟨C₁, d₁, h₁⟩ := hf
  obtain ⟨C₂, d₂, h₂⟩ := hg
  refine ⟨|C₁| + |C₂|, d₁ + d₂, ?_⟩
  filter_upwards [h₁, h₂, eventually_one_le_thetaTailScale] with x hx₁ hx₂ hq
  set q := thetaCuspSingleAtomReflectionScale 1 x
  have hq₁ : q ^ d₁ ≤ q ^ (d₁ + d₂) := pow_le_pow_right₀ hq (by omega)
  have hq₂ : q ^ d₂ ≤ q ^ (d₁ + d₂) := pow_le_pow_right₀ hq (by omega)
  have hp : 0 ≤ q ^ d₁ := pow_nonneg (by linarith) _
  have hp' : 0 ≤ q ^ d₂ := pow_nonneg (by linarith) _
  calc |f x + g x| ≤ |f x| + |g x| := abs_add_le _ _
    _ ≤ |C₁| * q ^ d₁ + |C₂| * q ^ d₂ := by
        gcongr
        · exact hx₁.trans (mul_le_mul_of_nonneg_right (le_abs_self _) hp)
        · exact hx₂.trans (mul_le_mul_of_nonneg_right (le_abs_self _) hp')
    _ ≤ |C₁| * q ^ (d₁ + d₂) + |C₂| * q ^ (d₁ + d₂) := by gcongr
    _ = (|C₁| + |C₂|) * q ^ (d₁ + d₂) := by ring

theorem mul (hf : ThetaTailModerate f) (hg : ThetaTailModerate g) :
    ThetaTailModerate (fun x => f x * g x) := by
  obtain ⟨C₁, d₁, h₁⟩ := hf
  obtain ⟨C₂, d₂, h₂⟩ := hg
  refine ⟨|C₁| * |C₂|, d₁ + d₂, ?_⟩
  filter_upwards [h₁, h₂] with x hx₁ hx₂
  have hp : 0 ≤ thetaCuspSingleAtomReflectionScale 1 x ^ d₁ :=
    pow_nonneg (thetaTailScale_pos x).le _
  have hp' : 0 ≤ thetaCuspSingleAtomReflectionScale 1 x ^ d₂ :=
    pow_nonneg (thetaTailScale_pos x).le _
  rw [abs_mul, pow_add]
  calc |f x| * |g x| ≤ (|C₁| * thetaCuspSingleAtomReflectionScale 1 x ^ d₁) *
        (|C₂| * thetaCuspSingleAtomReflectionScale 1 x ^ d₂) := by
        gcongr
        · exact hx₁.trans (mul_le_mul_of_nonneg_right (le_abs_self _) hp)
        · exact hx₂.trans (mul_le_mul_of_nonneg_right (le_abs_self _) hp')
    _ = _ := by ring

theorem neg (hf : ThetaTailModerate f) : ThetaTailModerate (fun x => -f x) := by
  obtain ⟨C, d, h⟩ := hf
  exact ⟨C, d, h.mono fun x hx => by rwa [abs_neg]⟩

theorem sub (hf : ThetaTailModerate f) (hg : ThetaTailModerate g) :
    ThetaTailModerate (fun x => f x - g x) := by
  simpa [sub_eq_add_neg] using hf.add hg.neg

theorem congr' (hf : ThetaTailModerate f) (h : f =ᶠ[atTop] g) : ThetaTailModerate g := by
  obtain ⟨C, d, hC⟩ := hf
  exact ⟨C, d, (hC.and h).mono fun x hx => by rw [← hx.2]; exact hx.1⟩

theorem of_tendsto {a : ℝ} (hf : Tendsto f atTop (𝓝 a)) : ThetaTailModerate f := by
  refine ⟨|a| + 1, 0, ?_⟩
  have h := hf.abs.eventually_lt_const (show |a| < |a| + 1 by linarith)
  filter_upwards [h] with x hx
  rw [pow_zero, mul_one]
  exact hx.le

theorem inv_of_ge {c : ℝ} (hc : 0 < c) (hf : ∀ᶠ x in atTop, c ≤ f x) :
    ThetaTailModerate (fun x => (f x)⁻¹) := by
  refine ⟨c⁻¹, 0, ?_⟩
  filter_upwards [hf] with x hx
  rw [pow_zero, mul_one, abs_inv, abs_of_pos (hc.trans_le hx)]
  exact inv_anti₀ hc hx

end ThetaTailModerate

theorem ThetaTailNegligible.mul_moderate {f g : ℝ → ℝ} (hf : ThetaTailNegligible f)
    (hg : ThetaTailModerate g) : ThetaTailNegligible (fun x => f x * g x) := fun s => by
  obtain ⟨C, d, hC⟩ := hg
  have h := ((hf (s + d)).abs.const_mul |C|)
  rw [abs_zero, mul_zero] at h
  refine squeeze_zero_norm' ?_ h
  filter_upwards [hC] with x hx
  set q := thetaCuspSingleAtomReflectionScale 1 x
  have hq : 0 ≤ q := (thetaTailScale_pos x).le
  rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_pow, abs_of_nonneg hq, abs_mul, abs_pow,
    abs_of_nonneg hq, pow_add]
  have hg' : |g x| ≤ |C| * q ^ d :=
    hx.trans (mul_le_mul_of_nonneg_right (le_abs_self _) (pow_nonneg hq _))
  calc q ^ s * (|f x| * |g x|) ≤ q ^ s * (|f x| * (|C| * q ^ d)) := by gcongr
    _ = |C| * (q ^ s * q ^ d * |f x|) := by ring

theorem ThetaTailNegligible.moderate {f : ℝ → ℝ} (hf : ThetaTailNegligible f) :
    ThetaTailModerate f :=
  ThetaTailModerate.of_tendsto hf.tendsto

/-! ## Closeness modulo negligible functions -/

/-- `f` and `g` agree on the positive tail up to a negligible function. -/
def ThetaTailClose (f g : ℝ → ℝ) : Prop := ThetaTailNegligible (fun x => f x - g x)

namespace ThetaTailClose

variable {a b c d : ℝ → ℝ}

theorem refl (a : ℝ → ℝ) : ThetaTailClose a a := by
  simpa [ThetaTailClose] using ThetaTailNegligible.zero

theorem moderate (h : ThetaTailClose a b) (hb : ThetaTailModerate b) : ThetaTailModerate a :=
  ((ThetaTailNegligible.moderate h).add hb).congr' (Eventually.of_forall fun x => by ring)

theorem add (h₁ : ThetaTailClose a b) (h₂ : ThetaTailClose c d) :
    ThetaTailClose (fun x => a x + c x) (fun x => b x + d x) :=
  (ThetaTailNegligible.add h₁ h₂).congr' (Eventually.of_forall fun x => by ring)

theorem sub (h₁ : ThetaTailClose a b) (h₂ : ThetaTailClose c d) :
    ThetaTailClose (fun x => a x - c x) (fun x => b x - d x) :=
  (ThetaTailNegligible.sub h₁ h₂).congr' (Eventually.of_forall fun x => by ring)

theorem mul (h₁ : ThetaTailClose a b) (hb : ThetaTailModerate b) (h₂ : ThetaTailClose c d)
    (hd : ThetaTailModerate d) : ThetaTailClose (fun x => a x * c x) (fun x => b x * d x) := by
  have hc := h₂.moderate hd
  exact ((ThetaTailNegligible.mul_moderate h₁ hc).add
    (ThetaTailNegligible.mul_moderate h₂ hb)).congr' (Eventually.of_forall fun x => by ring)

theorem div (h₁ : ThetaTailClose a b) (hb : ThetaTailModerate b) (h₂ : ThetaTailClose c d)
    (hc : ThetaTailModerate (fun x => (c x)⁻¹)) (hd : ThetaTailModerate (fun x => (d x)⁻¹))
    (hc0 : ∀ᶠ x in atTop, c x ≠ 0) (hd0 : ∀ᶠ x in atTop, d x ≠ 0) :
    ThetaTailClose (fun x => a x / c x) (fun x => b x / d x) := by
  have hN := (ThetaTailNegligible.mul_moderate h₁ hc).sub
    (ThetaTailNegligible.mul_moderate (ThetaTailNegligible.mul_moderate h₂ (hb.mul hc)) hd)
  refine hN.congr' ?_
  filter_upwards [hc0, hd0] with x hcx hdx
  field_simp
  ring

theorem pow_two (h : ThetaTailClose a b) (hb : ThetaTailModerate b) :
    ThetaTailClose (fun x => a x ^ 2) (fun x => b x ^ 2) := by
  simpa [sq] using h.mul hb h hb

end ThetaTailClose

/-! ## Polynomial logarithmic derivatives -/

theorem tendsto_eval_div_eval_of_natDegree_le (P Q : ℝ[X]) (hP : 0 < P.degree)
    (hQ : Q.natDegree ≤ P.natDegree) :
    Tendsto (fun y => eval y Q / eval y P) atTop
      (𝓝 (Q.coeff P.natDegree / P.leadingCoeff)) := by
  have hP0 : P ≠ 0 := ne_zero_of_degree_gt hP
  have hlc : P.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.2 hP0
  set c := Q.coeff P.natDegree / P.leadingCoeff
  set R := Q - C c * P
  have hR : R.degree < P.degree := by
    rw [degree_eq_natDegree hP0, degree_lt_iff_coeff_zero]
    intro k hk
    simp only [R, coeff_sub, coeff_C_mul]
    rcases hk.lt_or_eq with hk | hk
    · rw [coeff_eq_zero_of_natDegree_lt (hQ.trans_lt hk), coeff_eq_zero_of_natDegree_lt hk]
      ring
    · subst hk
      simp only [c, coeff_natDegree]
      field_simp
      ring
  have hlim := (Polynomial.div_tendsto_atTop_zero_of_degree_lt R P hR).const_add c
  rw [add_zero] at hlim
  refine hlim.congr' ?_
  filter_upwards [Polynomial.eventually_atTop_not_isRoot P hP0] with y hy
  have hy' : eval y P ≠ 0 := hy
  simp only [R, eval_sub, eval_mul, eval_C]
  field_simp
  ring

theorem coeff_X_mul_derivative_natDegree (P : ℝ[X]) (hP : 0 < P.natDegree) :
    (X * derivative P).coeff P.natDegree = P.natDegree * P.leadingCoeff := by
  obtain ⟨n, hn⟩ : ∃ n, P.natDegree = n + 1 := ⟨P.natDegree - 1, by omega⟩
  rw [hn, coeff_X_mul, coeff_derivative, leadingCoeff, hn]
  push_cast
  ring

theorem coeff_X_sq_mul_derivative_derivative_natDegree (P : ℝ[X]) :
    (X ^ 2 * derivative (derivative P)).coeff P.natDegree =
      P.natDegree * (P.natDegree - 1) * P.leadingCoeff := by
  rw [coeff_X_pow_mul', leadingCoeff]
  split_ifs with h
  · obtain ⟨n, hn⟩ : ∃ n, P.natDegree = n + 2 := ⟨P.natDegree - 2, by omega⟩
    rw [hn, show n + 2 - 2 = n by omega, coeff_derivative, coeff_derivative]
    push_cast
    ring
  · have : P.natDegree = 0 ∨ P.natDegree = 1 := by omega
    rcases this with h0 | h1 <;> simp [*]

theorem natDegree_X_mul_derivative_le (P : ℝ[X]) (hP : 0 < P.natDegree) :
    (X * derivative P).natDegree ≤ P.natDegree :=
  (natDegree_mul_le).trans (by
    have := natDegree_derivative_le P
    rw [natDegree_X]
    omega)

theorem natDegree_X_sq_mul_derivative_derivative_le (P : ℝ[X]) (hP : 2 ≤ P.natDegree) :
    (X ^ 2 * derivative (derivative P)).natDegree ≤ P.natDegree :=
  (natDegree_mul_le).trans (by
    have h1 := natDegree_derivative_le P
    have h2 := natDegree_derivative_le (derivative P)
    rw [natDegree_X_pow]
    omega)

/-- `(log P(e^x))' = e^x P'(e^x) / P(e^x)`. -/
def polyLogSlope (P : ℝ[X]) (x : ℝ) : ℝ :=
  eval (Real.exp x) (X * derivative P) / eval (Real.exp x) P

/-- `(log P(e^x))''`. -/
def polyLogCurvature (P : ℝ[X]) (x : ℝ) : ℝ :=
  polyLogSlope P x + eval (Real.exp x) (X ^ 2 * derivative (derivative P)) / eval (Real.exp x) P -
    polyLogSlope P x ^ 2

theorem tendsto_polyLogSlope (P : ℝ[X]) (hP : 0 < P.natDegree) :
    Tendsto (polyLogSlope P) atTop (𝓝 P.natDegree) := by
  have hdeg : 0 < P.degree := by
    rw [degree_eq_natDegree (ne_zero_of_natDegree_gt hP)]; exact_mod_cast hP
  have h := tendsto_eval_div_eval_of_natDegree_le P (X * derivative P) hdeg
    (natDegree_X_mul_derivative_le P hP)
  have hlc : P.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.2 (ne_zero_of_natDegree_gt hP)
  rw [coeff_X_mul_derivative_natDegree P hP, mul_div_assoc, div_self hlc, mul_one] at h
  exact h.comp Real.tendsto_exp_atTop

theorem tendsto_polyLogCurvature (P : ℝ[X]) (hP : 2 ≤ P.natDegree) :
    Tendsto (polyLogCurvature P) atTop (𝓝 0) := by
  have hP1 : 0 < P.natDegree := by omega
  have hdeg : 0 < P.degree := by
    rw [degree_eq_natDegree (ne_zero_of_natDegree_gt hP1)]; exact_mod_cast hP1
  have hlc : P.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.2 (ne_zero_of_natDegree_gt hP1)
  have h2 := tendsto_eval_div_eval_of_natDegree_le P (X ^ 2 * derivative (derivative P)) hdeg
    (natDegree_X_sq_mul_derivative_derivative_le P hP)
  rw [coeff_X_sq_mul_derivative_derivative_natDegree, mul_div_assoc, div_self hlc,
    mul_one] at h2
  have h1 := tendsto_polyLogSlope P hP1
  have h := (h1.add (h2.comp Real.tendsto_exp_atTop)).sub (h1.pow 2)
  have hval : (P.natDegree : ℝ) + P.natDegree * (P.natDegree - 1) - (P.natDegree : ℝ) ^ 2 = 0 := by
    ring
  rw [hval] at h
  exact h

/-- The source recursion evaluated: `P_{n+1}(y) = P_n(y)/2 + y P_n'(y) - 2π y² P_n(y)`. -/
theorem eval_thetaCuspLogDerivativeStep (P : ℝ[X]) (y : ℝ) :
    eval y (thetaCuspLogDerivativeStep P) =
      eval y P / 2 + eval y (X * derivative P) - 2 * Real.pi * y ^ 2 * eval y P := by
  simp only [thetaCuspLogDerivativeStep, eval_add, eval_sub, eval_mul, eval_C, eval_X, eval_pow]
  ring

/-- The logarithmic curvature identity of one source step:
`S²P · P - (SP)² = y P P' + y² P P'' - y² P'² - 4π y² P²`. -/
theorem eval_thetaCuspLogDerivativeStep_curvature (P : ℝ[X]) (y : ℝ) :
    eval y (thetaCuspLogDerivativeStep (thetaCuspLogDerivativeStep P)) * eval y P -
        eval y (thetaCuspLogDerivativeStep P) ^ 2 =
      eval y (X * derivative P) * eval y P +
        eval y (X ^ 2 * derivative (derivative P)) * eval y P -
          eval y (X * derivative P) ^ 2 - 4 * Real.pi * y ^ 2 * eval y P ^ 2 := by
  simp only [thetaCuspLogDerivativeStep, derivative_add, derivative_sub, derivative_mul,
    derivative_C, derivative_X, derivative_X_pow, eval_add, eval_sub, eval_mul, eval_C, eval_X,
    eval_pow, zero_mul, zero_add, one_mul]
  push_cast
  ring


theorem ThetaTailClose.tendsto {a b : ℝ → ℝ} {L : ℝ} (h : ThetaTailClose a b)
    (hb : Tendsto b atTop (𝓝 L)) : Tendsto a atTop (𝓝 L) := by
  have := (ThetaTailNegligible.tendsto h).add hb
  rw [zero_add] at this
  exact this.congr fun x => sub_add_cancel _ _

theorem ThetaTailClose.congr_right {a b c : ℝ → ℝ} (h : ThetaTailClose a b) (hbc : b =ᶠ[atTop] c) :
    ThetaTailClose a c :=
  ThetaTailNegligible.congr' h (hbc.mono fun x hx => by simp only; rw [hx])

/-! ## Source and first-atom derivative ratios -/

/-- The source derivative ratio `σ_j = k^{(j)}/k`. -/
def thetaSourceRatio (j : ℕ) (x : ℝ) : ℝ :=
  iteratedDeriv j thetaCuspFullSource x / thetaCuspFullSource x

/-- The first-atom derivative ratio `π_j = P_j(e^x)/P_0(e^x)`. -/
def thetaAtomRatio (j : ℕ) (x : ℝ) : ℝ :=
  eval (Real.exp x) (thetaCuspLogDerivativePolynomial j) /
    eval (Real.exp x) thetaCuspSeedPolynomial

theorem natDegree_thetaCuspLogDerivativePolynomial (j : ℕ) :
    (thetaCuspLogDerivativePolynomial j).natDegree = 4 + 2 * j :=
  natDegree_eq_of_degree_eq_some (thetaCuspLogDerivativePolynomial_degree_leading j).1

theorem firstAtom_derivative_ratio_eq (j : ℕ) (x : ℝ) :
    iteratedDeriv j (fun y : ℝ => thetaCuspSourceTerm y 1) x / thetaCuspSourceTerm x 1 =
      thetaAtomRatio j x := by
  rw [iteratedDeriv_thetaCuspSourceTerm_eq_polynomialAtom,
    show thetaCuspSourceTerm x 1 = thetaCuspPolynomialAtom thetaCuspSeedPolynomial 1 x from
      congrFun (thetaCuspSourceTerm_eq_polynomialAtom 1) x]
  unfold thetaCuspPolynomialAtom thetaAtomRatio
  simp only [Nat.cast_one, one_mul]
  rw [mul_div_mul_right _ _ (Real.exp_pos _).ne', mul_div_mul_left _ _ (Real.exp_pos _).ne']

theorem eval_thetaCuspSeedPolynomial_pos {x : ℝ} (hx : 0 < x) :
    0 < eval (Real.exp x) thetaCuspSeedPolynomial := by
  have hq := three_lt_thetaCuspSingleAtomReflectionScale (n := 1) (by norm_num) hx.le
  rw [thetaTailScale_eq] at hq
  have hid : eval (Real.exp x) thetaCuspSeedPolynomial =
      (2 * Real.pi * Real.exp x ^ 2) * (2 * Real.pi * Real.exp x ^ 2 - 3) := by
    simp only [thetaCuspSeedPolynomial, eval_sub, eval_mul, eval_C, eval_pow, eval_X]
    ring
  rw [hid]
  have h1 : 0 < 2 * Real.pi * Real.exp x ^ 2 := by positivity
  exact mul_pos h1 (by linarith)

theorem thetaAtomRatio_moderate (j : ℕ) : ThetaTailModerate (thetaAtomRatio j) := by
  refine ⟨thetaCuspCoeffMass (thetaCuspLogDerivativePolynomial j),
    (thetaCuspLogDerivativePolynomial j).natDegree, ?_⟩
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
  rw [← firstAtom_derivative_ratio_eq]
  exact abs_firstAtom_derivative_ratio_le j hx

theorem thetaSourceError_negligible (j : ℕ) :
    ThetaTailNegligible (fun x => (iteratedDeriv j thetaCuspFullSource x -
      iteratedDeriv j (fun y : ℝ => thetaCuspSourceTerm y 1) x) / thetaCuspSourceTerm x 1) :=
  fun s => thetaCuspFullSource_derivative_relative_error_scaled_tendsto_zero s j

/-- **Ratio approximation.** Every source derivative ratio `k^{(j)}/k` agrees with the first-atom
ratio `P_j(e^x)/P_0(e^x)` up to a negligible error. -/
theorem thetaSourceRatio_close (j : ℕ) :
    ThetaTailClose (thetaSourceRatio j) (thetaAtomRatio j) := by
  set e : ℕ → ℝ → ℝ := fun i x => (iteratedDeriv i thetaCuspFullSource x -
      iteratedDeriv i (fun y : ℝ => thetaCuspSourceTerm y 1) x) / thetaCuspSourceTerm x 1
  have he : ∀ i, ThetaTailNegligible (e i) := thetaSourceError_negligible
  have h0 : ∀ᶠ x in atTop, 1 / 2 ≤ 1 + e 0 x := by
    filter_upwards [(he 0).tendsto.eventually_const_lt (show (-(1 / 2) : ℝ) < 0 by norm_num)]
      with x hx
    linarith
  have hinv := ThetaTailModerate.inv_of_ge (by norm_num : (0 : ℝ) < 1 / 2) h0
  have hN := ((he j).sub ((he 0).mul_moderate (thetaAtomRatio_moderate j))).mul_moderate hinv
  refine hN.congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
  have hf : 0 < thetaCuspSourceTerm x 1 := thetaCuspSourceTerm_pos_of_pos_of_nat_pos hx one_pos
  have hk : 0 < thetaCuspFullSource x := thetaCuspFullSource_pos_all x
  have h1 : 1 + e 0 x = thetaCuspFullSource x / thetaCuspSourceTerm x 1 := by
    simp only [e, iteratedDeriv_zero]
    field_simp
    ring
  have hπ := firstAtom_derivative_ratio_eq j x
  simp only [thetaSourceRatio]
  rw [h1, inv_div, ← hπ]
  simp only [e, iteratedDeriv_zero]
  field_simp
  ring

theorem thetaSourceRatio_moderate (j : ℕ) : ThetaTailModerate (thetaSourceRatio j) :=
  (thetaSourceRatio_close j).moderate (thetaAtomRatio_moderate j)

theorem eventually_one_le_thetaAtomRatio (m : ℕ) (hm : 0 < m) :
    ∀ᶠ x in atTop, 1 ≤ thetaAtomRatio (4 * m) x :=
  (thetaCuspLogDerivativePolynomial_four_mul_ratio_tendsto_atTop m hm).eventually_ge_atTop 1

theorem eventually_half_le_thetaSourceRatio (m : ℕ) (hm : 0 < m) :
    ∀ᶠ x in atTop, 1 / 2 ≤ thetaSourceRatio (4 * m) x := by
  filter_upwards [eventually_one_le_thetaAtomRatio m hm,
    (ThetaTailNegligible.tendsto (thetaSourceRatio_close (4 * m))).eventually_const_lt
      (show (-(1 / 2) : ℝ) < 0 by norm_num)] with x h1 h2
  linarith

/-! ## The first-atom model of the logarithmic tail quantities -/

theorem thetaAtomRatio_succ_div (j : ℕ) {x : ℝ} (hx : 0 < x)
    (hj : eval (Real.exp x) (thetaCuspLogDerivativePolynomial j) ≠ 0) :
    thetaAtomRatio (j + 1) x / thetaAtomRatio j x =
      1 / 2 + polyLogSlope (thetaCuspLogDerivativePolynomial j) x -
        2 * thetaCuspSingleAtomReflectionScale 1 x := by
  have h0 := (eval_thetaCuspSeedPolynomial_pos hx).ne'
  unfold thetaAtomRatio polyLogSlope
  rw [thetaTailScale_eq]
  change eval _ (thetaCuspLogDerivativeStep (thetaCuspLogDerivativePolynomial j)) / _ / (_ / _) = _
  rw [eval_thetaCuspLogDerivativeStep]
  field_simp

theorem thetaAtomRatio_curvature (j : ℕ) {x : ℝ} (hx : 0 < x)
    (hj : eval (Real.exp x) (thetaCuspLogDerivativePolynomial j) ≠ 0) :
    thetaAtomRatio (j + 2) x / thetaAtomRatio j x -
        (thetaAtomRatio (j + 1) x / thetaAtomRatio j x) ^ 2 =
      polyLogCurvature (thetaCuspLogDerivativePolynomial j) x -
        4 * thetaCuspSingleAtomReflectionScale 1 x := by
  have h0 := (eval_thetaCuspSeedPolynomial_pos hx).ne'
  set P := thetaCuspLogDerivativePolynomial j
  have e1 : thetaAtomRatio (j + 2) x / thetaAtomRatio j x -
      (thetaAtomRatio (j + 1) x / thetaAtomRatio j x) ^ 2 =
      (eval (Real.exp x) (thetaCuspLogDerivativeStep (thetaCuspLogDerivativeStep P)) *
          eval (Real.exp x) P - eval (Real.exp x) (thetaCuspLogDerivativeStep P) ^ 2) /
        eval (Real.exp x) P ^ 2 := by
    change eval (Real.exp x) (thetaCuspLogDerivativeStep (thetaCuspLogDerivativeStep P)) /
      eval (Real.exp x) _ / (eval (Real.exp x) P / eval (Real.exp x) _) -
        (eval (Real.exp x) (thetaCuspLogDerivativeStep P) / eval (Real.exp x) _ /
          (eval (Real.exp x) P / eval (Real.exp x) _)) ^ 2 = _
    field_simp
  rw [e1, eval_thetaCuspLogDerivativeStep_curvature]
  unfold polyLogCurvature polyLogSlope
  rw [thetaTailScale_eq]
  field_simp

theorem thetaAtomRatio_zero {x : ℝ} (hx : 0 < x) : thetaAtomRatio 0 x = 1 :=
  div_self (eval_thetaCuspSeedPolynomial_pos hx).ne'

section FourthMultiple

variable (m : ℕ) (hm : 0 < m)
include hm

theorem eventually_thetaAtomRatio_ne_zero : ∀ᶠ x in atTop, thetaAtomRatio (4 * m) x ≠ 0 :=
  (eventually_one_le_thetaAtomRatio m hm).mono fun x hx => by positivity

theorem eventually_thetaSourceRatio_ne_zero : ∀ᶠ x in atTop, thetaSourceRatio (4 * m) x ≠ 0 :=
  (eventually_half_le_thetaSourceRatio m hm).mono fun x hx => by positivity

theorem thetaAtomRatio_inv_moderate :
    ThetaTailModerate (fun x => (thetaAtomRatio (4 * m) x)⁻¹) :=
  ThetaTailModerate.inv_of_ge one_pos (eventually_one_le_thetaAtomRatio m hm)

theorem thetaSourceRatio_inv_moderate :
    ThetaTailModerate (fun x => (thetaSourceRatio (4 * m) x)⁻¹) :=
  ThetaTailModerate.inv_of_ge (by norm_num) (eventually_half_le_thetaSourceRatio m hm)

theorem thetaAtomRatio_div_moderate (i : ℕ) :
    ThetaTailModerate (fun x => thetaAtomRatio i x / thetaAtomRatio (4 * m) x) :=
  ((thetaAtomRatio_moderate i).mul (thetaAtomRatio_inv_moderate m hm)).congr'
    (Eventually.of_forall fun _ => (div_eq_mul_inv _ _).symm)

theorem thetaSourceRatio_div_close (i : ℕ) :
    ThetaTailClose (fun x => thetaSourceRatio i x / thetaSourceRatio (4 * m) x)
      (fun x => thetaAtomRatio i x / thetaAtomRatio (4 * m) x) :=
  (thetaSourceRatio_close i).div (thetaAtomRatio_moderate i) (thetaSourceRatio_close (4 * m))
    (thetaSourceRatio_inv_moderate m hm) (thetaAtomRatio_inv_moderate m hm)
    (eventually_thetaSourceRatio_ne_zero m hm) (eventually_thetaAtomRatio_ne_zero m hm)

theorem eventually_eval_thetaCuspLogDerivativePolynomial_ne_zero :
    ∀ᶠ x in atTop, eval (Real.exp x) (thetaCuspLogDerivativePolynomial (4 * m)) ≠ 0 := by
  filter_upwards [eventually_thetaAtomRatio_ne_zero m hm] with x hx h
  exact hx (by rw [thetaAtomRatio, h, zero_div])

/-- The logarithmic slope of `a = k^{(4m)}/k` tends to `2·4m`. -/
theorem tendsto_thetaSourceRatio_logSlope :
    Tendsto (fun x => thetaSourceRatio (4 * m + 1) x / thetaSourceRatio (4 * m) x -
      thetaSourceRatio 1 x) atTop (𝓝 (2 * (4 * m : ℕ))) := by
  have hc : ThetaTailClose (fun x => thetaSourceRatio (4 * m + 1) x / thetaSourceRatio (4 * m) x -
      thetaSourceRatio 1 x) (fun x => polyLogSlope (thetaCuspLogDerivativePolynomial (4 * m)) x -
        polyLogSlope thetaCuspSeedPolynomial x) := by
    refine ((thetaSourceRatio_div_close m hm (4 * m + 1)).sub
      (thetaSourceRatio_close 1)).congr_right ?_
    filter_upwards [eventually_gt_atTop (0 : ℝ),
      eventually_eval_thetaCuspLogDerivativePolynomial_ne_zero m hm] with x hx hP
    have h1 := thetaAtomRatio_succ_div (4 * m) hx hP
    have h0 := thetaAtomRatio_succ_div 0 hx (eval_thetaCuspSeedPolynomial_pos hx).ne'
    rw [thetaAtomRatio_zero hx, div_one,
      show thetaCuspLogDerivativePolynomial 0 = thetaCuspSeedPolynomial from rfl] at h0
    rw [h1, h0]
    ring
  refine hc.tendsto ?_
  have h1 := tendsto_polyLogSlope (thetaCuspLogDerivativePolynomial (4 * m))
    (by rw [natDegree_thetaCuspLogDerivativePolynomial]; omega)
  have h0 := tendsto_polyLogSlope thetaCuspSeedPolynomial
    (by rw [show thetaCuspSeedPolynomial = thetaCuspLogDerivativePolynomial 0 from rfl,
      natDegree_thetaCuspLogDerivativePolynomial]; omega)
  rw [natDegree_thetaCuspLogDerivativePolynomial] at h1
  rw [show thetaCuspSeedPolynomial = thetaCuspLogDerivativePolynomial 0 from rfl,
    natDegree_thetaCuspLogDerivativePolynomial] at h0
  have h := h1.sub h0
  have hval : ((4 + 2 * (4 * m) : ℕ) : ℝ) - ((4 + 2 * 0 : ℕ) : ℝ) = 2 * ((4 * m : ℕ) : ℝ) := by
    push_cast; ring
  rw [hval] at h
  exact h

/-- The logarithmic curvature of `a = k^{(4m)}/k` tends to zero. -/
theorem tendsto_thetaSourceRatio_logCurvature :
    Tendsto (fun x => (thetaSourceRatio (4 * m + 2) x / thetaSourceRatio (4 * m) x -
      (thetaSourceRatio (4 * m + 1) x / thetaSourceRatio (4 * m) x) ^ 2) -
        (thetaSourceRatio 2 x - thetaSourceRatio 1 x ^ 2)) atTop (𝓝 0) := by
  have hc : ThetaTailClose (fun x => (thetaSourceRatio (4 * m + 2) x / thetaSourceRatio (4 * m) x -
      (thetaSourceRatio (4 * m + 1) x / thetaSourceRatio (4 * m) x) ^ 2) -
        (thetaSourceRatio 2 x - thetaSourceRatio 1 x ^ 2))
      (fun x => polyLogCurvature (thetaCuspLogDerivativePolynomial (4 * m)) x -
        polyLogCurvature thetaCuspSeedPolynomial x) := by
    refine (((thetaSourceRatio_div_close m hm (4 * m + 2)).sub
      ((thetaSourceRatio_div_close m hm (4 * m + 1)).pow_two
        (thetaAtomRatio_div_moderate m hm _))).sub
      ((thetaSourceRatio_close 2).sub ((thetaSourceRatio_close 1).pow_two
        (thetaAtomRatio_moderate 1)))).congr_right ?_
    filter_upwards [eventually_gt_atTop (0 : ℝ),
      eventually_eval_thetaCuspLogDerivativePolynomial_ne_zero m hm] with x hx hP
    have h1 := thetaAtomRatio_curvature (4 * m) hx hP
    have h0 := thetaAtomRatio_curvature 0 hx (eval_thetaCuspSeedPolynomial_pos hx).ne'
    rw [thetaAtomRatio_zero hx, div_one, div_one,
      show thetaCuspLogDerivativePolynomial 0 = thetaCuspSeedPolynomial from rfl] at h0
    rw [h1, h0]
    ring
  refine hc.tendsto ?_
  have h1 := tendsto_polyLogCurvature (thetaCuspLogDerivativePolynomial (4 * m))
    (by rw [natDegree_thetaCuspLogDerivativePolynomial]; omega)
  have h0 := tendsto_polyLogCurvature thetaCuspSeedPolynomial
    (by rw [show thetaCuspSeedPolynomial = thetaCuspLogDerivativePolynomial 0 from rfl,
      natDegree_thetaCuspLogDerivativePolynomial]; omega)
  simpa using h1.sub h0

end FourthMultiple

/-- **Source curvature.** `(log k)'' = k''/k - (k'/k)² = -4π e^{2x} + o(1)`. -/
theorem tendsto_thetaSourceRatio_curvature_add_scale :
    Tendsto (fun x => thetaSourceRatio 2 x - thetaSourceRatio 1 x ^ 2 +
      4 * thetaCuspSingleAtomReflectionScale 1 x) atTop (𝓝 0) := by
  have hc : ThetaTailClose (fun x => thetaSourceRatio 2 x - thetaSourceRatio 1 x ^ 2 +
      4 * thetaCuspSingleAtomReflectionScale 1 x)
      (polyLogCurvature thetaCuspSeedPolynomial) := by
    refine (((thetaSourceRatio_close 2).sub ((thetaSourceRatio_close 1).pow_two
      (thetaAtomRatio_moderate 1))).add
        (ThetaTailClose.refl (fun x => 4 * thetaCuspSingleAtomReflectionScale 1 x))).congr_right ?_
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
    have h0 := thetaAtomRatio_curvature 0 hx (eval_thetaCuspSeedPolynomial_pos hx).ne'
    rw [thetaAtomRatio_zero hx, div_one, div_one,
      show thetaCuspLogDerivativePolynomial 0 = thetaCuspSeedPolynomial from rfl] at h0
    rw [h0]
    ring
  exact hc.tendsto (tendsto_polyLogCurvature thetaCuspSeedPolynomial
    (by rw [show thetaCuspSeedPolynomial = thetaCuspLogDerivativePolynomial 0 from rfl,
      natDegree_thetaCuspLogDerivativePolynomial]; omega))

end

end RHTower
