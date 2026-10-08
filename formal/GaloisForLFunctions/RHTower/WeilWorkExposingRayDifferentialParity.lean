import GaloisForLFunctions.RHTower.WeilWorkExposingRayUniformPolarTail

/-!
# Alternating tails of the polar Riemann derivative family

The actual source `F_k = D^(k+2)Φ - D^kΦ/4` has both half-poles and every
literal Weil zero evaluation equal to zero. Its complete signed autocorrelation
has tail sign `(-1)^k`, with the explicit lower envelope
`exp (-(2*π*exp 2*exp y))` after an order-dependent threshold.

The proof uses the full theta series, its exact leading cusp polynomial, and an
integrable bound for every adverse contribution. Odd orders therefore supply
negative tails outside the previous even-source class. These untruncated source
identities do not prove compact admissibility, opposite exposing-ray matching,
or the universal WP02 energy lower bound.

Paper proof: `docs/reports/weil-work/results/02-exposing-ray/DIFFERENTIAL-PARITY-PROOF.md`.
-/

open Real Polynomial MeasureTheory Set Filter Topology
open scoped ComplexConjugate
noncomputable section
namespace RHTower.ExposingRayDifferential

/-- The actual polar radical derivative `D^k(D²-1/4)Φ`, with real values. -/
def source (k : ℕ) (x : ℝ) : ℝ :=
  (riemannKernelDeriv (k+2) x).re - (riemannKernelDeriv k x).re / 4

private def sourcePoly (k : ℕ) : ℝ[X] :=
  C ((-1:ℝ)^k) * (riemannKernelPoly (k+2) - C (1/4) * riemannKernelPoly k)

private theorem sign_sq (k : ℕ) : ((-1:ℝ)^k)^2 = 1 := by
  rw [← pow_mul, Nat.mul_comm, pow_mul]
  norm_num

private theorem sourcePoly_top (k : ℕ) :
    (sourcePoly k).coeff (k+4) = 4*π^2*(2*π)^(k+2) := by
  have hz : (riemannKernelPoly k).coeff (k+4) = 0 :=
    coeff_eq_zero_of_natDegree_lt ((natDegree_riemannKernelPoly_le k).trans_lt (by omega))
  simp only [sourcePoly, coeff_C_mul, coeff_sub, hz, mul_zero, sub_zero]
  rw [show k+4 = (k+2)+2 by omega, coeff_riemannKernelPoly_top]
  have hn : (-(2*π))^(k+2) = (-1:ℝ)^k*(2*π)^(k+2) := by
    rw [neg_pow, pow_add (-1:ℝ)]
    norm_num
  rw [hn]
  calc _ = ((-1:ℝ)^k)^2*(4*π^2*(2*π)^(k+2)) := by ring
    _ = _ := by rw [sign_sq,one_mul]


private theorem sourcePoly_degree (k : ℕ) : (sourcePoly k).natDegree = k+4 := by
  apply le_antisymm
  · apply (natDegree_C_mul_le _ _).trans
    apply (natDegree_sub_le _ _).trans
    apply max_le
    · exact (natDegree_riemannKernelPoly_le (k+2)).trans (by omega)
    · exact (natDegree_C_mul_le _ _).trans ((natDegree_riemannKernelPoly_le k).trans (by omega))
  · apply le_natDegree_of_ne_zero
    rw [sourcePoly_top]
    positivity

private theorem sourcePoly_eq (k : ℕ) (x : ℝ) :
    cuspSeries (sourcePoly k) x = (-1:ℝ)^k * source k x := by
  simp only [sourcePoly, cuspSeries_smul, cuspSeries_sub, source,
    riemannKernelDeriv, Complex.ofReal_re, riemannKernelPoly]
  ring

theorem source_parity (k : ℕ) (x : ℝ) : source k (-x) = (-1:ℝ)^k * source k x := by
  have h (j : ℕ) : (riemannKernelDeriv j (-x)).re =
      (-1:ℝ)^j * (riemannKernelDeriv j x).re := by
    rw [riemannKernelDeriv_neg]
    have hc : (-1:ℂ)^j = (((-1:ℝ)^j : ℝ):ℂ) := by push_cast; rfl
    rw [hc, Complex.re_ofReal_mul]
  simp only [source, h, pow_add, neg_one_sq, mul_one]
  ring

private theorem signed_cont (k : ℕ) : Continuous (fun x => (-1:ℝ)^k * source k x) := by
  have he : cuspSeries (sourcePoly k) = fun x => (-1:ℝ)^k*source k x := funext (sourcePoly_eq k)
  rw [← he]
  exact continuous_cuspSeries (sourcePoly k)

private theorem source_abs (k : ℕ) (x : ℝ) : |source k (|x|)| = |source k x| := by
  rcases le_total 0 x with hx | hx
  · rw [abs_of_nonneg hx]
  · rw [abs_of_nonpos hx, source_parity, abs_mul, abs_pow]
    norm_num

/-- Positive right-cusp envelope for every signed polar derivative. -/
theorem source_lower (k : ℕ) :
    ∃ R : ℝ, 0 ≤ R ∧ ∀ x : ℝ, R ≤ x →
      exp (-(π*exp (2*x))) ≤ (-1:ℝ)^k * source k x := by
  have hpoly : Tendsto (fun v : ℝ => (sourcePoly k).eval v) atTop atTop :=
    (sourcePoly k).tendsto_atTop_of_leadingCoeff_nonneg
      (natDegree_pos_iff_degree_pos.mp (by rw [sourcePoly_degree]; omega))
      (by rw [Polynomial.leadingCoeff, sourcePoly_degree, sourcePoly_top]; positivity)
  obtain ⟨V,hV⟩ := eventually_atTop.mp (hpoly.eventually_ge_atTop 1)
  obtain ⟨R,hR⟩ := eventually_atTop.mp
    ((Real.tendsto_exp_atTop.comp (tendsto_id.const_mul_atTop (by norm_num : (0:ℝ)<2))).eventually_ge_atTop V)
  refine ⟨max R 0, le_max_right _ _, fun x hx => ?_⟩
  have hx0 : 0 ≤ x := (le_max_right _ _).trans hx
  have hVx : V ≤ exp (2*x) := hR _ ((le_max_left _ _).trans hx)
  have hall (n : ℕ) : 1 ≤ (sourcePoly k).eval (((n+1:ℕ):ℝ)^2*exp (2*x)) := by
    apply hV
    have hn : (1:ℝ) ≤ ((n+1:ℕ):ℝ) := by exact_mod_cast Nat.succ_le_succ (Nat.zero_le n)
    have hn2 := one_le_pow₀ (n:=2) hn
    exact hVx.trans (by nlinarith [exp_pos (2*x)])
  have hterm (n : ℕ) : 0 ≤ cuspTerm (sourcePoly k) (n+1) x := by
    unfold cuspTerm
    exact mul_nonneg (mul_nonneg (exp_pos _).le (le_trans (by norm_num) (hall n))) (exp_pos _).le
  have hsum := (summable_cuspTerm (sourcePoly k) x).le_tsum 0 (fun n _ => hterm n)
  have hfirst : exp (-(π*exp (2*x))) ≤ cuspTerm (sourcePoly k) 1 x := by
    unfold cuspTerm
    simp only [Nat.cast_one, one_pow, one_mul]
    have hP := hall 0
    simp only [Nat.zero_add, Nat.cast_one, one_pow, one_mul] at hP
    have hE : 1 ≤ exp (x/2) := Real.one_le_exp (by positivity)
    rw [neg_mul]
    exact le_mul_of_one_le_left (exp_pos _).le (one_le_mul_of_one_le_of_one_le hE hP)
  rw [← sourcePoly_eq]
  exact hfirst.trans hsum

private theorem cusp_upper (P : ℝ[X]) {a : ℝ} (_ha : 0 < a) (haπ : a < π) :
    ∃ B : ℝ, 0 < B ∧ ∀ x : ℝ, 0 ≤ x →
      |cuspSeries P x| ≤ B*exp (-(a*exp (2*x)))*exp (-x) := by
  let d := π-a
  let m := P.natDegree+1
  let B := (cuspDecayConst P+1) * ((m.factorial:ℝ)/d^m)
  have hd : 0 < d := by dsimp [d]; linarith
  have hC := cuspDecayConst_nonneg P
  have hf : (0:ℝ) < (m.factorial:ℝ) := by exact_mod_cast Nat.factorial_pos m
  refine ⟨B, by dsimp [B]; positivity, fun x hx => ?_⟩
  let V := exp (2*x)
  have hV : 0 < V := exp_pos _
  have hpower : exp (x/2)*exp (2*P.natDegree*x) ≤ V^m*exp (-x) := by
    dsimp [V]
    rw [← exp_nat_mul, ← exp_add, ← exp_add]
    apply exp_le_exp.mpr
    dsimp [m]
    push_cast
    nlinarith
  have ht := Real.pow_div_factorial_le_exp (x:=d*V) (by positivity) m
  have hpay : V^m*exp (-(d*V)) ≤ (m.factorial:ℝ)/d^m := by
    have heq : exp (d*V)*exp (-(d*V)) = 1 := by rw [← exp_add]; simp
    have ht' := (div_le_iff₀ hf).mp ht
    rw [mul_pow] at ht'
    have hh := mul_le_mul_of_nonneg_right ht' (exp_pos (-(d*V))).le
    rw [le_div_iff₀ (by positivity)]
    nlinarith [heq]
  have heq : exp (-(π*V)) = exp (-(d*V))*exp (-(a*V)) := by
    rw [← exp_add]; congr 1; dsimp [d]; ring
  calc |cuspSeries P x| ≤ (cuspDecayConst P+1) *
        (exp (x/2)*exp (2*P.natDegree*x))*exp (-(π*V)) := by
        apply (abs_cuspSeries_le P hx).trans
        dsimp [V]
        simp only [neg_mul, mul_assoc]
        gcongr
        linarith
    _ ≤ (cuspDecayConst P+1)*(V^m*exp (-x))*exp (-(π*V)) := by gcongr
    _ = (cuspDecayConst P+1)*(V^m*exp (-(d*V)))*exp (-(a*V))*exp (-x) := by rw [heq]; ring
    _ ≤ (cuspDecayConst P+1)*((m.factorial:ℝ)/d^m)*exp (-(a*V))*exp (-x) := by gcongr
    _ = _ := rfl

/-- Every actual Riemann derivative has every subcritical full-theta norm envelope. -/
theorem kernel_derivative_upper_subcritical (k : ℕ) {a : ℝ} (ha : 0 < a) (haπ : a < π) :
    ∃ B : ℝ, 0 < B ∧ ∀ x : ℝ,
      ‖riemannKernelDeriv k x‖ ≤ B*exp (-(a*exp (2*|x|)))*exp (-|x|) := by
  obtain ⟨B,hB,h⟩ := cusp_upper (riemannKernelPoly k) ha haπ
  refine ⟨B,hB,fun x => ?_⟩
  have habs : ‖riemannKernelDeriv k |x|‖ = ‖riemannKernelDeriv k x‖ := by
    rcases le_total 0 x with hx | hx
    · rw [abs_of_nonneg hx]
    · rw [abs_of_nonpos hx,norm_riemannKernelDeriv_neg]
  have hb : ‖riemannKernelDeriv k |x|‖ ≤
      B*exp (-(a*exp (2*|x|)))*exp (-|x|) := by
    simpa only [riemannKernelDeriv,riemannKernelPoly,Complex.norm_real,Real.norm_eq_abs]
      using h |x| (abs_nonneg x)
  rwa [habs] at hb

/-- Every subcritical theta exponent bounds every fixed polar derivative. -/
theorem source_upper_subcritical (k : ℕ) {a : ℝ} (ha : 0 < a) (haπ : a < π) :
    ∃ B : ℝ, 0 < B ∧ ∀ x : ℝ,
      |source k x| ≤ B*exp (-(a*exp (2*|x|)))*exp (-|x|) := by
  obtain ⟨B,hB,h⟩ := cusp_upper (sourcePoly k) ha haπ
  refine ⟨B,hB,fun x => ?_⟩
  have hb := h |x| (abs_nonneg x)
  rw [sourcePoly_eq, abs_mul, abs_pow, source_abs] at hb
  simpa only [abs_neg, abs_one, one_pow, one_mul] using hb

/-- Global full-theta envelope for every polar derivative. -/
theorem source_upper (k : ℕ) :
    ∃ B : ℝ, 0 < B ∧ ∀ x : ℝ,
      |(-1:ℝ)^k*source k x| ≤ B*exp (-((π/2)*exp (2*|x|)))*exp (-|x|) := by
  obtain ⟨B,hB,h⟩ := source_upper_subcritical k (a:=π/2) (by positivity)
    (by linarith [Real.pi_pos])
  refine ⟨B,hB,fun x => ?_⟩
  simpa only [abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul] using h x

private theorem convolution_integrable {f : ℝ → ℝ} {a B : ℝ} (ha : 0 < a) (hB : 0 < B)
    (hf : Continuous f)
    (hu : ∀ x, |f x| ≤ B*exp (-(a*exp (2*|x|)))*exp (-|x|)) (y : ℝ) :
    Integrable (fun t => f t*f (y-t)) := by
  apply Integrable.mono' (integrable_exp_neg_abs.const_mul (B^2))
    (hf.mul (hf.comp (continuous_const.sub continuous_id))).aestronglyMeasurable
  apply Eventually.of_forall
  intro t
  simp only [Pi.mul_apply, Function.comp_apply, Pi.sub_apply, id_eq]
  rw [Real.norm_eq_abs, abs_mul]
  have hb (x : ℝ) : |f x| ≤ B*exp (-|x|) := by
    have he : exp (-(a*exp (2*|x|))) ≤ 1 := exp_le_one_iff.mpr (neg_nonpos.mpr (by positivity))
    exact (hu x).trans (by
      calc _ ≤ B*1*exp (-|x|) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left he hB.le) (exp_pos _).le
        _ = _ := by ring)
  have hs : exp (-|y-t|) ≤ 1 := exp_le_one_iff.mpr (by linarith [abs_nonneg (y-t)])
  calc _ ≤ (B*exp (-|t|))*(B*exp (-|y-t|)) := mul_le_mul (hb t) (hb (y-t)) (abs_nonneg _) (by positivity)
    _ ≤ (B*exp (-|t|))*(B*1) := by gcongr
    _ = _ := by ring

private theorem convolution_negative_bound {f : ℝ → ℝ} {a b B R : ℝ}
    (ha : 0 < a) (hB : 0 < B)
    (hu : ∀ x, |f x| ≤ B*exp (-(a*exp (2*|x|)))*exp (-|x|))
    (hl : ∀ x, R ≤ x → exp (-(b*exp (2*x))) ≤ f x) (t y : ℝ) :
    -(B^2*exp (-(a*exp (2*(y-R))))*exp (-|t|)) ≤ f t*f (y-t) := by
  by_cases hp : 0 ≤ f t*f (y-t)
  · exact le_trans (neg_nonpos.mpr (by positivity)) hp
  have hclose : t<R ∨ y-t<R := by
    by_contra hc
    push Not at hc
    exact hp (mul_nonneg ((exp_pos _).le.trans (hl t hc.1))
      ((exp_pos _).le.trans (hl (y-t) hc.2)))
  have hex : exp (2*(y-R)) ≤ exp (2*|t|)+exp (2*|y-t|) := by
    rcases hclose with hc | hc
    · have he := exp_le_exp.mpr (show 2*(y-R) ≤ 2*|y-t| by linarith [le_abs_self (y-t)])
      linarith [exp_pos (2*|t|)]
    · have he := exp_le_exp.mpr (show 2*(y-R) ≤ 2*|t| by linarith [le_abs_self t])
      linarith [exp_pos (2*|y-t|)]
  have hexp : exp (-(a*exp (2*|t|)))*exp (-(a*exp (2*|y-t|))) ≤
      exp (-(a*exp (2*(y-R)))) := by
    rw [← exp_add]
    apply exp_le_exp.mpr
    nlinarith [ha]
  have hs : exp (-|y-t|) ≤ 1 := exp_le_one_iff.mpr (by linarith [abs_nonneg (y-t)])
  have habs : |f t*f (y-t)| ≤ B^2*exp (-(a*exp (2*(y-R))))*exp (-|t|) := by
    rw [abs_mul]
    calc _ ≤ (B*exp (-(a*exp (2*|t|)))*exp (-|t|))*
          (B*exp (-(a*exp (2*|y-t|)))*exp (-|y-t|)) :=
        mul_le_mul (hu t) (hu (y-t)) (abs_nonneg _) (by positivity)
      _ = B^2*(exp (-(a*exp (2*|t|)))*exp (-(a*exp (2*|y-t|))))*
          exp (-|t|)*exp (-|y-t|) := by ring
      _ ≤ B^2*exp (-(a*exp (2*(y-R))))*exp (-|t|)*1 := by gcongr
      _ = _ := by ring
  exact (abs_le.mp habs).1

private theorem convolution_lower (a b B R : ℝ)
    (ha : 0<a) (hb : 0<b) (hB : 0<B) :
    ∃ Y : ℝ, ∀ f : ℝ → ℝ, Continuous f →
      (∀ x, |f x| ≤ B*exp (-(a*exp (2*|x|)))*exp (-|x|)) →
      (∀ x, R ≤ x → exp (-(b*exp (2*x))) ≤ f x) →
      ∀ y : ℝ, Y ≤ y → exp (-(2*b*exp 2*exp y)) ≤ ∫ t : ℝ, f t*f (y-t) := by
  obtain ⟨Y,hY⟩ := eventually_atTop.mp (ExposingRaySmallShift.error_absorbed a b B R ha)
  refine ⟨max Y (2*(R+1)),fun f hf hu hl y hy => ?_⟩
  have hyR : 2*(R+1) ≤ y := (le_max_right _ _).trans hy
  let L := exp (-(2*b*exp 2*exp y))
  let E := B^2*exp (-(a*exp (2*(y-R))))
  have hmid : ∀ t ∈ Ioc (y/2-1) (y/2+1), L ≤ f t*f (y-t) := by
    intro t ht
    have htR : R ≤ t := by linarith [ht.1]
    have hytR : R ≤ y-t := by linarith [ht.2]
    have h1 := exp_le_exp.mpr (show 2*t ≤ y+2 by linarith [ht.2])
    have h2 := exp_le_exp.mpr (show 2*(y-t) ≤ y+2 by linarith [ht.1])
    rw [exp_add] at h1 h2
    have hex : L ≤ exp (-(b*exp (2*t)))*exp (-(b*exp (2*(y-t)))) := by
      rw [← exp_add]
      apply exp_le_exp.mpr
      nlinarith [hb]
    exact hex.trans (mul_le_mul (hl t htR) (hl (y-t) hytR) (exp_pos _).le
      ((exp_pos _).le.trans (hl t htR)))
  have hnonneg : ∀ t, 0 ≤ f t*f (y-t)+E*exp (-|t|) := by
    intro t
    have := convolution_negative_bound ha hB hu hl t y
    dsimp [E]
    linarith
  have hi := (convolution_integrable ha hB hf hu y).add (integrable_exp_neg_abs.const_mul E)
  have hm := setIntegral_mono_on (integrableOn_const (by simp)) hi.integrableOn measurableSet_Ioc
    (fun t ht => (hmid t ht).trans (le_add_of_nonneg_right (by dsimp [E]; positivity)))
  have hc : (∫ t in Ioc (y/2-1) (y/2+1), L) = 2*L := by
    rw [setIntegral_const, Measure.real, Real.volume_Ioc, ENNReal.toReal_ofReal (by linarith)]
    simp only [smul_eq_mul]
    ring
  rw [hc] at hm
  have hg := hm.trans (setIntegral_le_integral hi (Eventually.of_forall hnonneg))
  simp only [Pi.add_apply] at hg
  rw [integral_add (convolution_integrable ha hB hf hu y) (integrable_exp_neg_abs.const_mul E),
    integral_const_mul,integral_exp_neg_abs] at hg
  have herr := hY y ((le_max_left _ _).trans hy)
  change L ≤ _
  change 2*L ≤ (∫ t : ℝ, f t*f (y-t))+E*2 at hg
  dsimp [E,L] at hg ⊢
  linarith

/-- The literal autocorrelation, including its entire signed integral. -/
def autocorr (k : ℕ) (y : ℝ) : ℝ := ∫ t : ℝ, source k t*source k (t-y)

/-- Absolute integrability of every literal differential autocorrelation. -/
theorem autocorr_integrable (k : ℕ) (y : ℝ) :
    Integrable (fun t => source k t*source k (t-y)) := by
  obtain ⟨B,hB,hu⟩ := source_upper k
  have hi := ExposingRaySmallShift.general_corr_integrable
    (by positivity : (0:ℝ)<π/2) hB (signed_cont k) hu y
  convert hi using 1
  funext t
  calc source k t*source k (t-y) =
      ((-1:ℝ)^k)^2*(source k t*source k (t-y)) := by rw [sign_sq,one_mul]
    _ = _ := by ring

/-- All derivative orders have an explicit nonzero tail, with alternating sign. -/
theorem autocorr_parity_lower (k : ℕ) :
    ∃ Y : ℝ, ∀ y : ℝ, Y ≤ y →
      exp (-(2*π*exp 2*exp y)) ≤ (-1:ℝ)^k*autocorr k y := by
  obtain ⟨B,hB,hu⟩ := source_upper k
  obtain ⟨R,_hR,hl⟩ := source_lower k
  obtain ⟨Y,hY⟩ := convolution_lower (π/2) π B R (by positivity) pi_pos hB
  refine ⟨Y,fun y hy => ?_⟩
  have h := hY _ (signed_cont k) hu hl y hy
  have he : (∫ t : ℝ, ((-1:ℝ)^k*source k t)*((-1:ℝ)^k*source k (y-t))) =
      (-1:ℝ)^k*autocorr k y := by
    rw [autocorr,← integral_const_mul]
    apply integral_congr_ae
    apply Eventually.of_forall
    intro t
    have hs := sign_sq k
    have hp : source k (y-t) = (-1:ℝ)^k*source k (t-y) := by
      rw [show y-t = -(t-y) by ring,source_parity]
    dsimp only
    rw [hp]
    calc _ = ((-1:ℝ)^k)^2*((-1:ℝ)^k*(source k t*source k (t-y))) := by ring
      _ = _ := by rw [hs,one_mul]
  rwa [he] at h

/-- Strict positive tails for every even-order polar differential source. -/
theorem even_autocorr_eventually_pos (k : ℕ) :
    ∀ᶠ y : ℝ in atTop, 0 < autocorr (2*k) y := by
  obtain ⟨Y,hY⟩ := autocorr_parity_lower (2*k)
  refine eventually_atTop.mpr ⟨Y,fun y hy => ?_⟩
  have h := (exp_pos _).trans_le (hY y hy)
  simpa [pow_mul] using h

/-- Strict negative tails for every odd-order polar differential source. -/
theorem odd_autocorr_eventually_neg (k : ℕ) :
    ∀ᶠ y : ℝ in atTop, autocorr (2*k+1) y < 0 := by
  obtain ⟨Y,hY⟩ := autocorr_parity_lower (2*k+1)
  refine eventually_atTop.mpr ⟨Y,fun y hy => ?_⟩
  have h := (exp_pos _).trans_le (hY y hy)
  simpa [pow_add,pow_mul] using h


private theorem source_complex (k : ℕ) (x : ℝ) :
    (source k x : ℂ) = riemannKernelDeriv (k+2) x - riemannKernelDeriv k x / 4 := by
  simp only [source,riemannKernelDeriv,Complex.ofReal_re]
  push_cast
  rfl

/-- Fourier multiplier of the literal polar radical derivative, at every complex frequency. -/
theorem source_fourier (k : ℕ) (z : ℂ) :
    Zeta23.paperFT (fun x => (source k x : ℂ)) z =
      (-(Complex.I*z))^k*((-(Complex.I*z))^2-1/4)*
        riemannPhiTransform (1/2+Complex.I*z) := by
  have he : (fun x : ℝ => (source k x : ℂ)*Complex.exp (Complex.I*z*x)) =
      fun x => riemannKernelDeriv (k+2) x*Complex.exp (Complex.I*z*x) -
        (riemannKernelDeriv k x*Complex.exp (Complex.I*z*x))/4 := by
    funext x
    rw [source_complex]
    ring
  unfold Zeta23.paperFT
  rw [he,integral_sub ((superExpDecay_riemannKernelDeriv (k+2)).integrable_mul_cexp z)
    (((superExpDecay_riemannKernelDeriv k).integrable_mul_cexp z).div_const 4),integral_div]
  change Zeta23.paperFT (riemannKernelDeriv (k+2)) z -
    Zeta23.paperFT (riemannKernelDeriv k) z / 4 = _
  rw [paperFT_riemannKernelDeriv,paperFT_riemannKernelDeriv,pow_add]
  ring

/-- Both actual half-poles vanish, without a source hypothesis. -/
theorem source_half_poles (k : ℕ) :
    Zeta23.paperFT (fun x => (source k x : ℂ)) (Complex.I/2) = 0 ∧
      Zeta23.paperFT (fun x => (source k x : ℂ)) (-(Complex.I/2)) = 0 := by
  have hi : Complex.I*Complex.I = -1 := by simpa only [pow_two] using Complex.I_sq
  have hp : -(Complex.I*(Complex.I/2)) = (1/2:ℂ) := by
    rw [mul_div,hi]
    ring
  have hm : -(Complex.I*(-(Complex.I/2))) = -(1/2:ℂ) := by
    rw [mul_neg,mul_div,hi]
    ring
  constructor
  · rw [source_fourier,hp]
    norm_num
  · rw [source_fourier,hm]
    norm_num

/-- The full derivative family remains in the literal Riemann radical. -/
theorem source_zero_evaluations (k : ℕ) (ρ : Zeta23.zetaZeroConfig.carrier) :
    Zeta23.paperFT (fun x => (source k x : ℂ)) (Zeta23.gammaOf ρ) = 0 ∧
      Zeta23.paperFT (fun x => (source k x : ℂ))
        ((starRingEnd ℂ) (Zeta23.gammaOf ρ)) = 0 := by
  have hz := paperFT_riemannKernelDeriv_at_zero 0 ρ.property
  simp only [paperFT_riemannKernelDeriv,pow_zero,one_mul] at hz
  constructor
  · rw [source_fourier,hz.1,mul_zero]
  · rw [source_fourier,hz.2,mul_zero]

end RHTower.ExposingRayDifferential
