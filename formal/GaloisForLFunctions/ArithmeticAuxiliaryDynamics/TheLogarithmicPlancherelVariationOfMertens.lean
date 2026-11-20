import GaloisForLFunctions.RHTower.MobiusMertensAbscissaLittlewood
import GaloisForLFunctions.HTGeometry.MellinLinePlancherel
import GaloisForLFunctions.ArithmeticAuxiliaryDynamics.TheOneFifthRateUnderTheRiemannHypothesis

/-!
# Logarithmic Plancherel variation and dyadic Haar chaining for smoothed Mertens sums

Right of a zero-free abscissa `Θ ∈ [1/2, 1)`, the smoothed Mertens sum
`smoothMertens θ X = ∑' n, μ(n) smoothWeight X (θ X) n` differs from `M(⌊X⌋₊)` by at most
`θ X + 1`, while its multiplicative increments `S_θ(e^{u+λ}) - S_θ(e^u)` are inverse Mellin
transforms on `Re s = Θ + ε` of `(e^{λ s} - 1) invZeta(s) W_θ(s)`. Mellin–Plancherel bounds the
weighted `L²` increment energy uniformly in the smoothing width `θ ∈ (0, 1]`.

Combined with dyadic interval decomposition on `[0, 2^N)` and a greedy tube-exit anchor, this
controls the `ℓ¹` jump variation of piecewise-constant integer approximations to `S_θ` on every
dyadic octave.
-/

open Complex MeasureTheory Filter Finset Topology
open scoped FourierTransform
open GaloisForLFunctions.HTGeometry

noncomputable section

namespace GaloisForLFunctions.ArithmeticAuxiliaryDynamics

/-! ### Part 1: Smoothed Mertens sums and Mellin–Plancherel `L²` variation -/

/-- The smoothed Mertens sum with relative transition width `θ`. -/
def smoothMertens (θ X : ℝ) : ℝ :=
  ∑' n : ℕ, (ArithmeticFunction.moebius n : ℝ) * smoothWeight X (θ * X) (n : ℝ)

theorem smoothMertens_eq_sum_range {θ X : ℝ} (hθ : 0 < θ) (hX : 0 < X) (m : ℕ)
    (hm : X + θ * X ≤ (m : ℝ)) :
    smoothMertens θ X =
      ∑ n ∈ range m, (ArithmeticFunction.moebius n : ℝ) * smoothWeight X (θ * X) (n : ℝ) := by
  have hH : 0 < θ * X := mul_pos hθ hX
  refine tsum_eq_sum fun n hn => ?_
  have hnm : m ≤ n := not_lt.mp (mt Finset.mem_range.mpr hn)
  have hnR : (m : ℝ) ≤ (n : ℝ) := by exact_mod_cast hnm
  rw [smoothWeight_eq_zero hH (by linarith), mul_zero]

theorem ofReal_smoothMertens {θ X : ℝ} (hθ : 0 < θ) (hX : 0 < X) :
    ((smoothMertens θ X : ℝ) : ℂ) =
      ∑' n : ℕ, (ArithmeticFunction.moebius n : ℂ) *
        ((smoothWeight X (θ * X) (n : ℝ) : ℝ) : ℂ) := by
  have hH : 0 < θ * X := mul_pos hθ hX
  set m : ℕ := ⌊X + θ * X⌋₊ + 1
  have hm : X + θ * X ≤ (m : ℝ) := by
    have := Nat.lt_floor_add_one (X + θ * X)
    push_cast [m]
    linarith
  rw [smoothMertens_eq_sum_range hθ hX m hm,
    tsum_mul_smoothWeight_eq_sum_range_real hH m hm]
  push_cast
  rfl

/-- `smoothMertens θ X` differs from `mertens ⌊X⌋₊` by at most `θ X + 1`. -/
theorem abs_smoothMertens_sub_mertens_le {θ X : ℝ} (hθ : 0 < θ) (hX : 0 < X) :
    |smoothMertens θ X - mertens ⌊X⌋₊| ≤ θ * X + 1 := by
  have hH : 0 < θ * X := mul_pos hθ hX
  have hcmp := RHTower.Sieve.norm_tsum_smoothWeight_sub_sum_le hX hH
  rw [← ofReal_smoothMertens hθ hX] at hcmp
  have hsum : (∑ n ∈ range (⌊X⌋₊ + 1), (ArithmeticFunction.moebius n : ℂ)) =
      ((mertens ⌊X⌋₊ : ℝ) : ℂ) := by
    rw [mertens]
    have hset : range (⌊X⌋₊ + 1) = insert 0 (Ioc 0 ⌊X⌋₊) := by
      ext n
      simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Ioc]
      omega
    rw [hset, sum_insert (by simp)]
    simp only [ArithmeticFunction.map_zero, Int.cast_zero, zero_add]
    push_cast
    rfl
  rw [hsum, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs] at hcmp
  exact hcmp

/-- On any compact interval inside `(0, ∞)`, `smoothMertens θ` is continuous. -/
theorem continuousOn_smoothMertens {θ A B : ℝ} (hθ : 0 < θ) (hA : 0 < A) :
    ContinuousOn (smoothMertens θ) (Set.Icc A B) := by
  rcases lt_or_ge B A with hBA | hAB
  · rw [Set.Icc_eq_empty (not_le.mpr hBA)]
    exact continuousOn_empty _
  have hB : 0 < B := lt_of_lt_of_le hA hAB
  set m : ℕ := ⌊B + θ * B⌋₊ + 1
  have heq : Set.EqOn (smoothMertens θ)
      (fun X => ∑ n ∈ range m, (ArithmeticFunction.moebius n : ℝ) *
        smoothWeight X (θ * X) (n : ℝ)) (Set.Icc A B) := by
    intro X hX
    have hXpos : 0 < X := lt_of_lt_of_le hA hX.1
    have hm : X + θ * X ≤ (m : ℝ) := by
      have hle : X + θ * X ≤ B + θ * B := by nlinarith [hX.2]
      have hfl := Nat.lt_floor_add_one (B + θ * B)
      push_cast [m]
      linarith
    exact smoothMertens_eq_sum_range hθ hXpos m hm
  refine ContinuousOn.congr ?_ heq
  refine continuousOn_finsetSum _ fun n _ => ContinuousOn.mul continuousOn_const ?_
  intro X hX
  have hXpos : 0 < X := lt_of_lt_of_le hA hX.1
  have hHne : θ * X ≠ 0 := (mul_pos hθ hXpos).ne'
  unfold smoothWeight
  refine ContinuousAt.continuousWithinAt (ContinuousAt.sub continuousAt_const ?_)
  refine Real.smoothTransition.continuous.continuousAt.comp ?_
  exact ContinuousAt.mul ((continuousAt_const.mul continuousAt_id).inv₀ hHne)
    (continuousAt_const.add continuousAt_id.neg)

private lemma mellin_smoothWeight_scale {θ X : ℝ} (hX : 0 < X) (s : ℂ) :
    mellin (fun x : ℝ => ((smoothWeight X (θ * X) x : ℝ) : ℂ)) s =
      (X : ℂ) ^ s * mellin (fun x : ℝ => ((smoothWeight 1 θ x : ℝ) : ℂ)) s := by
  let f : ℝ → ℂ := fun x => ((smoothWeight 1 θ x : ℝ) : ℂ)
  have hfun : (fun x : ℝ => ((smoothWeight X (θ * X) x : ℝ) : ℂ)) =
      fun x : ℝ => f (X⁻¹ * x) := by
    funext x
    simp only [f, smoothWeight]
    congr 2
    field_simp [hX.ne']
  rw [hfun, mellin_comp_mul_left f s (inv_pos.mpr hX)]
  change (((X⁻¹ : ℝ) : ℂ) ^ (-s)) * mellin f s = (X : ℂ) ^ s * mellin f s
  have harg : (X : ℂ).arg ≠ Real.pi := by
    rw [Complex.arg_ofReal_of_nonneg hX.le]
    exact Real.pi_pos.ne
  rw [Complex.ofReal_inv, Complex.inv_cpow _ _ harg, ← Complex.cpow_neg]
  congr 2
  ring

private lemma ofReal_exp_cpow (x : ℝ) (s : ℂ) :
    ((Real.exp x : ℝ) : ℂ) ^ s = Complex.exp ((x : ℂ) * s) := by
  rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr (Real.exp_pos x).ne'),
    ← Complex.ofReal_log (Real.exp_pos x).le, Real.log_exp]

private lemma norm_exp_sub_one_le_of_re_nonneg {w : ℂ} (hw : 0 ≤ w.re) :
    ‖Complex.exp w - 1‖ ≤ Real.exp w.re * ‖w‖ := by
  have hderiv : ∀ t ∈ Set.uIcc (0 : ℝ) 1,
      HasDerivAt (fun t : ℝ => Complex.exp ((t : ℂ) * w))
        (Complex.exp ((t : ℂ) * w) * w) t := by
    intro t _
    have h1 : HasDerivAt (fun t : ℝ => (t : ℂ) * w) w t := by
      simpa using (Complex.ofRealCLM.hasDerivAt (x := t)).mul_const w
    exact h1.cexp
  have hint : IntervalIntegrable (fun t : ℝ => Complex.exp ((t : ℂ) * w) * w) volume 0 1 := by
    refine Continuous.intervalIntegrable ?_ 0 1
    fun_prop
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint
  simp only [Complex.ofReal_one, one_mul, Complex.ofReal_zero, zero_mul, Complex.exp_zero] at hftc
  rw [← hftc]
  have hbd := intervalIntegral.norm_integral_le_of_norm_le_const
    (C := Real.exp w.re * ‖w‖) (f := fun t : ℝ => Complex.exp ((t : ℂ) * w) * w)
    (a := 0) (b := 1) fun t ht => by
      rw [Set.uIoc_of_le zero_le_one] at ht
      rw [norm_mul, Complex.norm_exp]
      have hre : ((t : ℂ) * w).re = t * w.re := by simp
      rw [hre]
      refine mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr ?_) (norm_nonneg w)
      exact mul_le_of_le_one_left hw ht.2
  simpa using hbd

/-- Right of a zero-free frontier `Θ ∈ [1/2, 1)`, smoothed Mertens increments satisfy an `L²`
logarithmic Plancherel bound uniform in `θ ∈ (0, 1]` and `λ ∈ (0, 1]`. -/
theorem exists_integral_smoothMertens_log_diff_sq_le {Θ ε : ℝ}
    (hΘ : 1 / 2 ≤ Θ) (hΘ1 : Θ < 1)
    (hzf : ∀ z : ℂ, Θ < z.re → riemannZeta z ≠ 0)
    (hε0 : 0 < ε) (hε4 : ε ≤ 1 / 4) :
    ∃ C : ℝ, 0 < C ∧ ∀ θ lam : ℝ, 0 < θ → θ ≤ 1 → 0 < lam → lam ≤ 1 →
      Integrable (fun u : ℝ => Real.exp (-(2 * (Θ + ε)) * u) *
        (smoothMertens θ (Real.exp (u + lam)) - smoothMertens θ (Real.exp u)) ^ 2) ∧
      (∫ u : ℝ, Real.exp (-(2 * (Θ + ε)) * u) *
        (smoothMertens θ (Real.exp (u + lam)) - smoothMertens θ (Real.exp u)) ^ 2) ≤
        C * lam ^ (1 - 2 * ε) := by
  set σ : ℝ := Θ + ε
  have hσpos : 0 < σ := by dsimp [σ]; linarith
  have hσ2 : σ ≤ 2 := by dsimp [σ]; linarith
  have hε1 : ε < 1 := by linarith
  have h12ε : 0 < 1 - 2 * ε := by linarith
  obtain ⟨Kb, hKb, hFdiff, hFbd⟩ :=
    RHTower.exists_invZeta_shift_data_of_zeroFree hΘ hΘ1.le hzf hε0 hε1 hε0 (2 : ℝ)
  obtain ⟨A₀, hA₀, hW₀⟩ := exists_bound_mellin_smoothWeight_uniform_support 0
  set B : ℝ := 12 * (Real.exp 2 + 1) * (A₀ + 1) * (Kb + 1)
  have hBpos : 0 < B := by dsimp [B]; positivity
  set Cout : ℝ := 4 * B ^ 2 / (1 - 2 * ε) + 1
  refine ⟨Cout, by dsimp [Cout]; positivity, fun θ lam hθ0 hθ1 hlam0 hlam1 => ?_⟩
  let W : ℂ → ℂ := mellin (fun x : ℝ => ((smoothWeight 1 θ x : ℝ) : ℂ))
  let F : ℂ → ℂ := fun s => (Complex.exp ((lam : ℂ) * s) - 1) * RHTower.Sieve.invZeta s
  let Ψ : ℂ → ℂ := fun s => F s * W s
  have hFstrip_diff : DifferentiableOn ℂ F (HTGeometry.verticalStrip σ 2) := by
    refine DifferentiableOn.mul ?_ hFdiff
    intro s _
    exact (((differentiableAt_id.const_mul (lam : ℂ)).cexp).sub
      (differentiableAt_const 1)).differentiableWithinAt
  have hFstrip_bd : ∀ s ∈ HTGeometry.verticalStrip σ 2,
      ‖F s‖ ≤ ((Real.exp 2 + 1) * Kb) * (2 + |s.im|) ^ ε := by
    intro s hs
    have hs_hi : s.re ≤ 2 := hs.2
    have hexp_le : ‖Complex.exp ((lam : ℂ) * s) - 1‖ ≤ Real.exp 2 + 1 := by
      refine (norm_sub_le _ _).trans ?_
      rw [Complex.norm_exp, norm_one]
      have hre : ((lam : ℂ) * s).re = lam * s.re := by simp
      rw [hre]
      have : lam * s.re ≤ 2 := by nlinarith [hs_hi]
      linarith [Real.exp_le_exp.mpr this]
    rw [norm_mul]
    calc ‖Complex.exp ((lam : ℂ) * s) - 1‖ * ‖RHTower.Sieve.invZeta s‖
        ≤ (Real.exp 2 + 1) * (Kb * (2 + |s.im|) ^ ε) :=
          mul_le_mul hexp_le (hFbd s hs) (norm_nonneg _) (by positivity)
      _ = ((Real.exp 2 + 1) * Kb) * (2 + |s.im|) ^ ε := by ring
  have hintΨ : Integrable (fun t : ℝ => Ψ ((σ : ℂ) + (t : ℝ) * I)) :=
    integrable_mul_mellin_smoothWeight_line one_pos hθ0 hσpos hFstrip_diff.continuousOn
      (by positivity) hε0.le hFstrip_bd le_rfl hσ2
  have hWnorm : ∀ t : ℝ,
      ‖((σ : ℂ) + (t : ℝ) * I)‖ * ‖W ((σ : ℂ) + (t : ℝ) * I)‖ ≤ 4 * (A₀ + 1) := by
    intro t
    have hre : (((σ : ℂ) + (t : ℝ) * I)).re = σ := by simp
    have hz := hW₀ 1 θ one_pos hθ0 ((σ : ℂ) + (t : ℝ) * I) (by rw [hre]; exact hσpos)
    simp only [Finset.range_zero, Finset.prod_empty, mul_one, Nat.cast_zero, add_zero,
      zero_add, pow_one, hre] at hz
    have h1θ : (1 + θ) ^ σ ≤ 4 := by
      calc (1 + θ) ^ σ ≤ (2 : ℝ) ^ σ := Real.rpow_le_rpow (by positivity) (by linarith) hσpos.le
        _ ≤ (2 : ℝ) ^ (2 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) hσ2
        _ = 4 := by norm_num
    calc ‖((σ : ℂ) + (t : ℝ) * I)‖ * ‖W ((σ : ℂ) + (t : ℝ) * I)‖
        ≤ A₀ / θ * (1 + θ) ^ σ * θ := hz
      _ = A₀ * (1 + θ) ^ σ := by field_simp [hθ0.ne']
      _ ≤ (A₀ + 1) * 4 := mul_le_mul (by linarith) h1θ (by positivity) (by positivity)
      _ = 4 * (A₀ + 1) := by ring
  have hΨ_global : ∀ t : ℝ, ‖Ψ ((σ : ℂ) + (t : ℝ) * I)‖ ≤ 2 * B := by
    intro t
    set s : ℂ := (σ : ℂ) + (t : ℝ) * I
    have hs_mem : s ∈ HTGeometry.verticalStrip σ 2 := line_mem_verticalStrip le_rfl hσ2 t
    have hre_le : σ ≤ ‖s‖ := by
      have := Complex.abs_re_le_norm s
      have hsre : s.re = σ := by simp [s]
      rwa [hsre, abs_of_pos hσpos] at this
    have him_le : |t| ≤ ‖s‖ := by
      have := Complex.abs_im_le_norm s
      have hsim : s.im = t := by simp [s]
      rwa [hsim] at this
    have h2t : (2 + |t|) ^ ε ≤ 6 * ‖s‖ := by
      calc (2 + |t|) ^ ε ≤ (2 + |t|) ^ (1 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le (by linarith [abs_nonneg t]) hε1.le
        _ = 2 + |t| := Real.rpow_one _
        _ ≤ 6 * ‖s‖ := by dsimp [σ] at hre_le; linarith
    have hFs := hFstrip_bd s hs_mem
    have hsim : s.im = t := by simp [s]
    rw [hsim] at hFs
    change ‖F s * W s‖ ≤ 2 * B
    rw [norm_mul]
    calc ‖F s‖ * ‖W s‖
        ≤ (((Real.exp 2 + 1) * Kb) * (2 + |t|) ^ ε) * ‖W s‖ :=
          mul_le_mul_of_nonneg_right hFs (norm_nonneg _)
      _ ≤ (((Real.exp 2 + 1) * Kb) * (6 * ‖s‖)) * ‖W s‖ := by
          gcongr
      _ = 6 * (Real.exp 2 + 1) * Kb * (‖s‖ * ‖W s‖) := by ring
      _ ≤ 6 * (Real.exp 2 + 1) * (Kb + 1) * (4 * (A₀ + 1)) := by
          refine mul_le_mul ?_ (hWnorm t) (by positivity) (by positivity)
          nlinarith [Real.exp_pos 2]
      _ = 2 * B := by dsimp [B]; ring
  have hL2Ψ : MemLp (fun t : ℝ => Ψ ((σ : ℂ) + (t : ℝ) * I)) 2 := by
    rw [memLp_two_iff_integrable_sq_norm hintΨ.aestronglyMeasurable]
    refine Integrable.mono' (hintΨ.norm.const_mul (2 * B))
      (hintΨ.aestronglyMeasurable.norm.pow 2) ?_
    filter_upwards with t
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), sq]
    exact mul_le_mul_of_nonneg_right (hΨ_global t) (norm_nonneg _)
  have hshift_pt : ∀ x : ℝ,
      ((smoothMertens θ (Real.exp x) : ℝ) : ℂ) =
        (1 / (2 * Real.pi) : ℝ) • ∫ t : ℝ,
          Complex.exp ((x : ℂ) * ((σ : ℂ) + (t : ℝ) * I)) *
            (RHTower.Sieve.invZeta ((σ : ℂ) + (t : ℝ) * I) * W ((σ : ℂ) + (t : ℝ) * I)) := by
    intro x
    have hx : 0 < Real.exp x := Real.exp_pos x
    have hH : 0 < θ * Real.exp x := mul_pos hθ0 hx
    have hp := RHTower.mobius_perron_shift_of_zeroFree hΘ hΘ1.le hzf hε0 hε1 hε0 hx hH
    rw [← ofReal_smoothMertens hθ0 hx] at hp
    have hpi : (2 * Real.pi : ℝ) ≠ 0 := by positivity
    have hp' : ((smoothMertens θ (Real.exp x) : ℝ) : ℂ) =
        (1 / (2 * Real.pi) : ℝ) • ∫ t : ℝ,
          RHTower.Sieve.invZeta ((σ : ℂ) + (t : ℝ) * I) *
            mellin (fun v : ℝ => ((smoothWeight (Real.exp x) (θ * Real.exp x) v : ℝ) : ℂ))
              ((σ : ℂ) + (t : ℝ) * I) := by
      rw [← hp, smul_smul]
      field_simp [hpi]
      simp
    rw [hp']
    congr 1
    refine integral_congr_ae (Eventually.of_forall fun t => ?_)
    dsimp only
    rw [mellin_smoothWeight_scale hx, ofReal_exp_cpow]
    ring
  have hint_pt : ∀ x : ℝ, Integrable (fun t : ℝ =>
      Complex.exp ((x : ℂ) * ((σ : ℂ) + (t : ℝ) * I)) *
        (RHTower.Sieve.invZeta ((σ : ℂ) + (t : ℝ) * I) * W ((σ : ℂ) + (t : ℝ) * I))) := by
    intro x
    have hx : 0 < Real.exp x := Real.exp_pos x
    have hH : 0 < θ * Real.exp x := mul_pos hθ0 hx
    have hi := integrable_mul_mellin_smoothWeight_line hx hH hσpos hFdiff.continuousOn
      hKb hε0.le hFbd le_rfl hσ2
    refine hi.congr (Eventually.of_forall fun t => ?_)
    dsimp only
    rw [mellin_smoothWeight_scale hx, ofReal_exp_cpow]
    ring
  have hdiff_eq : ∀ u : ℝ,
      ((smoothMertens θ (Real.exp (u + lam)) - smoothMertens θ (Real.exp u) : ℝ) : ℂ) =
        mellinInv σ Ψ (Real.exp (-u)) := by
    intro u
    rw [Complex.ofReal_sub, hshift_pt (u + lam), hshift_pt u, ← smul_sub,
      ← integral_sub (hint_pt (u + lam)) (hint_pt u), mellinInv]
    congr 1
    refine integral_congr_ae (Eventually.of_forall fun t => ?_)
    dsimp only [Ψ, F]
    rw [ofReal_exp_cpow (-u), smul_eq_mul]
    have hexp1 : Complex.exp (((u + lam : ℝ) : ℂ) * ((σ : ℂ) + (t : ℝ) * I)) =
        Complex.exp ((lam : ℂ) * ((σ : ℂ) + (t : ℝ) * I)) *
          Complex.exp ((u : ℂ) * ((σ : ℂ) + (t : ℝ) * I)) := by
      rw [← Complex.exp_add]
      congr 1
      push_cast
      ring
    have hexp2 : Complex.exp (((-u : ℝ) : ℂ) * -((σ : ℂ) + (t : ℝ) * I)) =
        Complex.exp ((u : ℂ) * ((σ : ℂ) + (t : ℝ) * I)) := by
      congr 1
      push_cast
      ring
    rw [hexp1, hexp2]
    ring
  have hpt_sq : ∀ u : ℝ,
      Real.exp (-(2 * σ) * u) *
        (smoothMertens θ (Real.exp (u + lam)) - smoothMertens θ (Real.exp u)) ^ 2 =
        ‖mellinInv σ Ψ (Real.exp (-u))‖ ^ 2 * Real.exp (-(2 * σ) * u) := by
    intro u
    have hnorm := congrArg norm (hdiff_eq u)
    rw [Complex.norm_real, Real.norm_eq_abs] at hnorm
    rw [← sq_abs, hnorm, mul_comm]
  set φ : ℝ → ℂ := fun y => Ψ ((σ : ℂ) + 2 * Real.pi * y * I)
  have h2π : (0 : ℝ) < 2 * Real.pi := by positivity
  have hφeq : φ = fun y : ℝ => (fun t : ℝ => Ψ ((σ : ℂ) + t * I)) (2 * Real.pi * y) := by
    funext y; simp only [φ]; push_cast; ring_nf
  have hφint : Integrable φ := by
    rw [hφeq]; exact hintΨ.comp_mul_left' h2π.ne'
  have hφL2 : MemLp φ 2 := by
    rw [memLp_two_iff_integrable_sq_norm hφint.aestronglyMeasurable]
    have h := (memLp_two_iff_integrable_sq_norm hintΨ.aestronglyMeasurable).mp hL2Ψ
    rw [hφeq]
    exact h.comp_mul_left' h2π.ne'
  have hfour_pt : ∀ u : ℝ,
      ‖mellinInv σ Ψ (Real.exp (-u))‖ ^ 2 * Real.exp (-(2 * σ) * u) = ‖𝓕⁻ φ u‖ ^ 2 := by
    intro u
    have hx : 0 < Real.exp (-u) := Real.exp_pos (-u)
    rw [mellinInv_eq_fourierInv σ Ψ hx, Real.log_exp, neg_neg, norm_smul,
      Complex.norm_cpow_eq_rpow_re_of_pos hx]
    simp only [neg_re, ofReal_re]
    rw [mul_pow, ← Real.rpow_natCast, ← Real.rpow_mul hx.le, Real.rpow_def_of_pos hx,
      Real.log_exp]
    have hexp_cancel : Real.exp ((-u) * (-σ * ((2 : ℕ) : ℝ))) * Real.exp (-(2 * σ) * u) = 1 := by
      rw [← Real.exp_add]
      have : (-u) * (-σ * ((2 : ℕ) : ℝ)) + -(2 * σ) * u = 0 := by push_cast; ring
      rw [this, Real.exp_zero]
    calc Real.exp ((-u) * (-σ * ((2 : ℕ) : ℝ))) * ‖𝓕⁻ φ u‖ ^ 2 * Real.exp (-(2 * σ) * u)
        = ‖𝓕⁻ φ u‖ ^ 2 * (Real.exp ((-u) * (-σ * ((2 : ℕ) : ℝ))) * Real.exp (-(2 * σ) * u)) := by
          ring
      _ = ‖𝓕⁻ φ u‖ ^ 2 := by rw [hexp_cancel, mul_one]
  have hint_u : Integrable (fun u : ℝ => Real.exp (-(2 * σ) * u) *
      (smoothMertens θ (Real.exp (u + lam)) - smoothMertens θ (Real.exp u)) ^ 2) := by
    have heq : (fun u : ℝ => Real.exp (-(2 * σ) * u) *
        (smoothMertens θ (Real.exp (u + lam)) - smoothMertens θ (Real.exp u)) ^ 2) =
        fun u : ℝ => ‖𝓕 φ (-u)‖ ^ 2 := by
      funext u
      rw [hpt_sq u, hfour_pt u, Real.fourierInv_eq_fourier_neg]
    rw [heq]
    set uLp : Lp ℂ 2 (volume : Measure ℝ) := hφL2.toLp φ
    have hcoe : (uLp : ℝ → ℂ) =ᵐ[volume] φ := hφL2.coeFn_toLp
    have hFae : ((𝓕 uLp : Lp ℂ 2 (volume : Measure ℝ)) : ℝ → ℂ) =ᵐ[volume] 𝓕 φ :=
      (coeFn_fourierTransform_eq_fourierIntegral uLp (hφint.congr hcoe.symm)).trans
        (Eventually.of_forall fun ξ => Real.fourier_congr_ae hcoe ξ)
    have hsq_int : Integrable (fun ξ : ℝ => ‖𝓕 φ ξ‖ ^ 2) := by
      have hbase := (Lp.memLp (𝓕 uLp : Lp ℂ 2 (volume : Measure ℝ))).integrable_norm_pow
        (by norm_num : (2 : ℕ) ≠ 0)
      refine hbase.congr ?_
      filter_upwards [hFae] with ξ hξ
      simp [hξ]
    exact hsq_int.comp_neg
  refine ⟨hint_u, ?_⟩
  have hpl := integral_norm_sq_mellinInv hintΨ hL2Ψ
  have hsub := integral_Ioi_comp_neg_log_div
    (fun u : ℝ => Real.exp (-(2 * σ) * u) *
      (smoothMertens θ (Real.exp (u + lam)) - smoothMertens θ (Real.exp u)) ^ 2)
  have hsub_eq : (∫ x in Set.Ioi (0 : ℝ),
      (Real.exp (-(2 * σ) * (-Real.log x)) *
        (smoothMertens θ (Real.exp (-Real.log x + lam)) -
          smoothMertens θ (Real.exp (-Real.log x))) ^ 2) * x⁻¹) =
      ∫ x in Set.Ioi (0 : ℝ), ‖mellinInv σ Ψ x‖ ^ 2 * x ^ (2 * σ - 1) := by
    refine setIntegral_congr_fun measurableSet_Ioi fun x hx => ?_
    have hx0 : 0 < x := hx
    rw [hpt_sq (-Real.log x), neg_neg, Real.exp_log hx0]
    have hexp_pow : Real.exp (-(2 * σ) * (-Real.log x)) * x⁻¹ = x ^ (2 * σ - 1) := by
      rw [show -(2 * σ) * (-Real.log x) = Real.log x * (2 * σ) by ring,
        ← Real.rpow_def_of_pos hx0, ← Real.rpow_neg_one x, ← Real.rpow_add hx0, ← sub_eq_add_neg]
    calc ‖mellinInv σ Ψ x‖ ^ 2 * Real.exp (-(2 * σ) * (-Real.log x)) * x⁻¹
        = ‖mellinInv σ Ψ x‖ ^ 2 * (Real.exp (-(2 * σ) * (-Real.log x)) * x⁻¹) := by ring
      _ = ‖mellinInv σ Ψ x‖ ^ 2 * x ^ (2 * σ - 1) := by rw [hexp_pow]
  rw [← hsub, hsub_eq, hpl]
  set R : ℝ := lam⁻¹
  have hRpos : 0 < R := inv_pos.mpr hlam0
  have hR1 : 1 ≤ R := (one_le_inv₀ hlam0).mpr hlam1
  let g : ℝ → ℝ := fun t => ‖Ψ ((σ : ℂ) + (t : ℝ) * I)‖ ^ 2
  have hgint : Integrable g :=
    (memLp_two_iff_integrable_sq_norm hintΨ.aestronglyMeasurable).mp hL2Ψ
  have htail_meas : MeasurableSet {t : ℝ | R ≤ |t|} := measurableSet_centralTail R
  have hsplit := integral_add_compl htail_meas hgint
  have hcompl : {t : ℝ | R ≤ |t|}ᶜ = Set.Ioo (-R) R := by
    ext t; simp only [Set.mem_compl_iff, Set.mem_setOf_eq, Set.mem_Ioo, not_le, abs_lt]
  rw [hcompl] at hsplit
  have hcenter_bd : ∀ t ∈ Set.Ioo (-R) R, g t ≤ B ^ 2 * lam ^ (2 - 2 * ε) := by
    intro t ht
    have htabs : |t| < R := abs_lt.mpr ht
    set s : ℂ := (σ : ℂ) + (t : ℝ) * I
    have hs_mem : s ∈ HTGeometry.verticalStrip σ 2 := line_mem_verticalStrip le_rfl hσ2 t
    have hw_re : 0 ≤ ((lam : ℂ) * s).re := by
      have : ((lam : ℂ) * s).re = lam * σ := by simp [s]
      rw [this]; positivity
    have hexp_lip : ‖Complex.exp ((lam : ℂ) * s) - 1‖ ≤ (Real.exp 2 + 1) * lam * ‖s‖ := by
      have h1 := norm_exp_sub_one_le_of_re_nonneg hw_re
      have hre : ((lam : ℂ) * s).re = lam * σ := by simp [s]
      rw [hre, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hlam0] at h1
      have hexp2 : Real.exp (lam * σ) ≤ Real.exp 2 + 1 := by
        have : lam * σ ≤ 2 := by nlinarith
        linarith [Real.exp_le_exp.mpr this]
      calc ‖Complex.exp ((lam : ℂ) * s) - 1‖ ≤ Real.exp (lam * σ) * (lam * ‖s‖) := h1
        _ ≤ (Real.exp 2 + 1) * (lam * ‖s‖) := mul_le_mul_of_nonneg_right hexp2 (by positivity)
        _ = (Real.exp 2 + 1) * lam * ‖s‖ := by ring
    have hinvZ := hFbd s hs_mem
    have hsim : s.im = t := by simp [s]
    rw [hsim] at hinvZ
    have h2t : (2 + |t|) ^ ε ≤ 3 * R ^ ε := by
      have hbase : 2 + |t| ≤ 3 * R := by linarith
      calc (2 + |t|) ^ ε ≤ (3 * R) ^ ε := Real.rpow_le_rpow (by positivity) hbase hε0.le
        _ = 3 ^ ε * R ^ ε := Real.mul_rpow (by norm_num) hRpos.le
        _ ≤ 3 ^ (1 : ℝ) * R ^ ε :=
          mul_le_mul_of_nonneg_right (Real.rpow_le_rpow_of_exponent_le (by norm_num) hε1.le)
            (by positivity)
        _ = 3 * R ^ ε := by rw [Real.rpow_one]
    have hlamR : lam * R ^ ε = lam ^ (1 - ε) := by
      rw [show R = lam ^ (-1 : ℝ) by rw [Real.rpow_neg_one], ← Real.rpow_mul hlam0.le]
      nth_rw 1 [← Real.rpow_one lam]
      rw [← Real.rpow_add hlam0]
      congr 1; ring
    have hΨ_pt : ‖Ψ s‖ ≤ B * lam ^ (1 - ε) := by
      change ‖(Complex.exp ((lam : ℂ) * s) - 1) * RHTower.Sieve.invZeta s * W s‖ ≤ _
      rw [norm_mul, norm_mul]
      calc ‖Complex.exp ((lam : ℂ) * s) - 1‖ * ‖RHTower.Sieve.invZeta s‖ * ‖W s‖
          ≤ ((Real.exp 2 + 1) * lam * ‖s‖) * (Kb * (2 + |t|) ^ ε) * ‖W s‖ := by
            refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
            exact mul_le_mul hexp_lip hinvZ (norm_nonneg _) (by positivity)
        _ ≤ ((Real.exp 2 + 1) * lam * ‖s‖) * ((Kb + 1) * (3 * R ^ ε)) * ‖W s‖ := by
            gcongr
            linarith
        _ = 3 * (Real.exp 2 + 1) * (Kb + 1) * (lam * R ^ ε) * (‖s‖ * ‖W s‖) := by ring
        _ ≤ 3 * (Real.exp 2 + 1) * (Kb + 1) * lam ^ (1 - ε) * (4 * (A₀ + 1)) := by
            rw [hlamR]
            exact mul_le_mul_of_nonneg_left (hWnorm t) (by positivity)
        _ = B * lam ^ (1 - ε) := by dsimp [B]; ring
    have hsq := pow_le_pow_left₀ (norm_nonneg _) hΨ_pt 2
    refine hsq.trans_eq ?_
    rw [mul_pow, ← Real.rpow_natCast (lam ^ (1 - ε)) 2, ← Real.rpow_mul hlam0.le]
    congr 2; push_cast; ring
  have hcenter_int : ∫ t in Set.Ioo (-R) R, g t ≤ 2 * B ^ 2 * lam ^ (1 - 2 * ε) := by
    have hnorm := norm_setIntegral_le_of_norm_le_const (μ := volume) (f := g)
      (s := Set.Ioo (-R) R) measure_Ioo_lt_top fun t ht => by
        rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
        exact hcenter_bd t ht
    have hvol : volume.real (Set.Ioo (-R) R) = 2 * R := by
      rw [Measure.real, Real.volume_Ioo, ENNReal.toReal_ofReal (by linarith)]
      ring
    rw [hvol] at hnorm
    have hle : ∫ t in Set.Ioo (-R) R, g t ≤ (B ^ 2 * lam ^ (2 - 2 * ε)) * (2 * R) :=
      (le_abs_self _).trans (by simpa [Real.norm_eq_abs] using hnorm)
    refine hle.trans_eq ?_
    have hRlam : lam ^ (2 - 2 * ε) * R = lam ^ (1 - 2 * ε) := by
      rw [show R = lam ^ (-1 : ℝ) by rw [Real.rpow_neg_one], ← Real.rpow_add hlam0]
      congr 1; ring
    calc B ^ 2 * lam ^ (2 - 2 * ε) * (2 * R)
        = 2 * B ^ 2 * (lam ^ (2 - 2 * ε) * R) := by ring
      _ = 2 * B ^ 2 * lam ^ (1 - 2 * ε) := by rw [hRlam]
  have htail_bd : ∀ t : ℝ, R ≤ |t| → g t ≤ B ^ 2 * |t| ^ (-(2 - 2 * ε)) := by
    intro t ht
    have ht1 : 1 ≤ |t| := hR1.trans ht
    have ht0 : 0 < |t| := zero_lt_one.trans_le ht1
    set s : ℂ := (σ : ℂ) + (t : ℝ) * I
    have hs_mem : s ∈ HTGeometry.verticalStrip σ 2 := line_mem_verticalStrip le_rfl hσ2 t
    have hFs := hFstrip_bd s hs_mem
    have hsim : s.im = t := by simp [s]
    rw [hsim] at hFs
    have him_le : |t| ≤ ‖s‖ := by
      have := Complex.abs_im_le_norm s
      rwa [hsim] at this
    have hWt : ‖W s‖ ≤ 4 * (A₀ + 1) * |t|⁻¹ := by
      rw [le_mul_inv_iff₀ ht0]
      calc ‖W s‖ * |t| ≤ ‖W s‖ * ‖s‖ := mul_le_mul_of_nonneg_left him_le (norm_nonneg _)
        _ = ‖s‖ * ‖W s‖ := mul_comm _ _
        _ ≤ 4 * (A₀ + 1) := hWnorm t
    have h2t : (2 + |t|) ^ ε ≤ 3 * |t| ^ ε := by
      have hbase : 2 + |t| ≤ 3 * |t| := by linarith
      calc (2 + |t|) ^ ε ≤ (3 * |t|) ^ ε := Real.rpow_le_rpow (by positivity) hbase hε0.le
        _ = 3 ^ ε * |t| ^ ε := Real.mul_rpow (by norm_num) ht0.le
        _ ≤ 3 ^ (1 : ℝ) * |t| ^ ε :=
          mul_le_mul_of_nonneg_right (Real.rpow_le_rpow_of_exponent_le (by norm_num) hε1.le)
            (by positivity)
        _ = 3 * |t| ^ ε := by rw [Real.rpow_one]
    have hΨ_pt : ‖Ψ s‖ ≤ B * |t| ^ (-(1 - ε)) := by
      change ‖F s * W s‖ ≤ _
      rw [norm_mul]
      have htpow : |t| ^ ε * |t|⁻¹ = |t| ^ (-(1 - ε)) := by
        rw [← Real.rpow_neg_one |t|, ← Real.rpow_add ht0]
        congr 1; ring
      calc ‖F s‖ * ‖W s‖
          ≤ (((Real.exp 2 + 1) * Kb) * (2 + |t|) ^ ε) * (4 * (A₀ + 1) * |t|⁻¹) :=
            mul_le_mul hFs hWt (norm_nonneg _) (by positivity)
        _ ≤ (((Real.exp 2 + 1) * (Kb + 1)) * (3 * |t| ^ ε)) * (4 * (A₀ + 1) * |t|⁻¹) := by
            gcongr; linarith
        _ = B * (|t| ^ ε * |t|⁻¹) := by dsimp [B]; ring
        _ = B * |t| ^ (-(1 - ε)) := by rw [htpow]
    have hsq := pow_le_pow_left₀ (norm_nonneg _) hΨ_pt 2
    refine hsq.trans_eq ?_
    rw [mul_pow, ← Real.rpow_natCast (|t| ^ (-(1 - ε))) 2, ← Real.rpow_mul ht0.le]
    congr 2; push_cast; ring
  have htail_int : ∫ t in {t : ℝ | R ≤ |t|}, g t ≤
      (2 * B ^ 2 / (1 - 2 * ε)) * lam ^ (1 - 2 * ε) := by
    have hp : 1 < 2 - 2 * ε := by linarith
    have ht := setIntegral_le_of_le_powerTail (f := g) (K := B ^ 2) (t := R) (p := 2 - 2 * ε)
      (fun _ => sq_nonneg _) hRpos hp htail_bd
    refine ht.trans_eq ?_
    have hRpow : R ^ (1 - (2 - 2 * ε)) = lam ^ (1 - 2 * ε) := by
      rw [show R = lam ^ (-1 : ℝ) by rw [Real.rpow_neg_one], ← Real.rpow_mul hlam0.le]
      congr 1; ring
    rw [hRpow]
    have : 2 - 2 * ε - 1 = 1 - 2 * ε := by ring
    rw [this]
    ring
  have htot : ∫ t : ℝ, g t ≤ (4 * B ^ 2 / (1 - 2 * ε)) * lam ^ (1 - 2 * ε) := by
    rw [← hsplit]
    have hc_le : 2 * B ^ 2 ≤ 2 * B ^ 2 / (1 - 2 * ε) := by
      rw [le_div_iff₀ h12ε]
      nlinarith
    calc (∫ t in {t : ℝ | R ≤ |t|}, g t) + ∫ t in Set.Ioo (-R) R, g t
        ≤ (2 * B ^ 2 / (1 - 2 * ε)) * lam ^ (1 - 2 * ε) + 2 * B ^ 2 * lam ^ (1 - 2 * ε) :=
          add_le_add htail_int hcenter_int
      _ ≤ (2 * B ^ 2 / (1 - 2 * ε)) * lam ^ (1 - 2 * ε) +
          (2 * B ^ 2 / (1 - 2 * ε)) * lam ^ (1 - 2 * ε) := by
          gcongr
      _ = (4 * B ^ 2 / (1 - 2 * ε)) * lam ^ (1 - 2 * ε) := by ring
  have h2π1 : (1 / (2 * Real.pi)) ≤ 1 := by
    rw [div_le_one h2π]
    linarith [Real.pi_gt_three]
  calc (1 / (2 * Real.pi)) * ∫ t : ℝ, g t
      ≤ 1 * ((4 * B ^ 2 / (1 - 2 * ε)) * lam ^ (1 - 2 * ε)) :=
        mul_le_mul h2π1 htot (integral_nonneg fun _ => sq_nonneg _) zero_le_one
    _ ≤ Cout * lam ^ (1 - 2 * ε) := by
        rw [one_mul]
        refine mul_le_mul_of_nonneg_right ?_ (by positivity)
        dsimp [Cout]; linarith

/-! ### Part 2: Dyadic interval decomposition, Haar energy, and greedy tube-exit anchor -/

/-- Dyadic subintervals `[q 2^m, (q + 1) 2^m)` of `[0, 2^N)`, encoded by `(m, q)`. -/
def dyadicSet (N : ℕ) : Finset (ℕ × ℕ) :=
  ((range (N + 1)) ×ˢ (range (2 ^ N))).filter fun p => p.2 < 2 ^ (N - p.1)

theorem mem_dyadicSet {N m q : ℕ} :
    (m, q) ∈ dyadicSet N ↔ m ≤ N ∧ q < 2 ^ (N - m) := by
  simp only [dyadicSet, Finset.mem_filter, Finset.mem_product, Finset.mem_range]
  constructor
  · rintro ⟨⟨hm, _⟩, hq⟩
    exact ⟨by omega, hq⟩
  · rintro ⟨hm, hq⟩
    refine ⟨⟨by omega, hq.trans_le (Nat.pow_le_pow_right (by norm_num) (by omega))⟩, hq⟩

/-- Discrete dyadic Haar energy of `g` on `[0, 2^N]`. -/
def dyadicEnergy (N : ℕ) (g : ℕ → ℝ) : ℝ :=
  ∑ p ∈ dyadicSet N, (g ((p.2 + 1) * 2 ^ p.1) - g (p.2 * 2 ^ p.1)) ^ 2

theorem dyadicEnergy_nonneg (N : ℕ) (g : ℕ → ℝ) : 0 ≤ dyadicEnergy N g :=
  sum_nonneg fun _ _ => sq_nonneg _

private def shiftDyadic (N : ℕ) : ℕ × ℕ ↪ ℕ × ℕ :=
  ⟨fun p => (p.1, p.2 + 2 ^ (N - p.1)), fun a b h => by
    rcases a with ⟨m₁, q₁⟩
    rcases b with ⟨m₂, q₂⟩
    simp only [Prod.mk.injEq] at h
    rcases h with ⟨rfl, hq⟩
    exact Prod.ext rfl (Nat.add_right_cancel hq)⟩

private lemma map_shiftDyadic_subset {N : ℕ} {D : Finset (ℕ × ℕ)} (hD : D ⊆ dyadicSet N) :
    D.map (shiftDyadic N) ⊆ dyadicSet (N + 1) := by
  intro p hp
  rcases mem_map.mp hp with ⟨⟨m, q⟩, hmq, rfl⟩
  obtain ⟨hm, hq⟩ := mem_dyadicSet.mp (hD hmq)
  simp only [shiftDyadic, Function.Embedding.coeFn_mk, mem_dyadicSet]
  refine ⟨by omega, ?_⟩
  have hsub : N + 1 - m = (N - m) + 1 := by omega
  rw [hsub, pow_succ]
  omega

private lemma lift_dyadicSet_subset (N : ℕ) : dyadicSet N ⊆ dyadicSet (N + 1) := by
  intro ⟨m, q⟩ hp
  obtain ⟨hm, hq⟩ := mem_dyadicSet.mp hp
  exact mem_dyadicSet.mpr ⟨by omega,
    hq.trans_le (Nat.pow_le_pow_right (by norm_num) (by omega))⟩

private lemma exists_dyadic_prefix :
    ∀ (N : ℕ) (g : ℕ → ℝ) {b : ℕ}, b ≤ 2 ^ N →
      ∃ D ⊆ dyadicSet N, D.card ≤ N + 1 ∧
        (∀ p ∈ D, (p.2 + 1) * 2 ^ p.1 ≤ b) ∧
        g b - g 0 = ∑ p ∈ D, (g ((p.2 + 1) * 2 ^ p.1) - g (p.2 * 2 ^ p.1))
  | 0, g, b, hb => by
    rcases (by omega : b = 0 ∨ b = 1) with rfl | rfl
    · exact ⟨∅, empty_subset _, by simp, by simp, by simp⟩
    · refine ⟨{(0, 0)}, ?_, by simp, ?_, ?_⟩
      · intro p hp
        rw [mem_singleton.mp hp]
        exact mem_dyadicSet.mpr ⟨le_rfl, by norm_num⟩
      · intro p hp
        rw [mem_singleton.mp hp]; norm_num
      · simp
  | N + 1, g, b, hb => by
    rcases le_or_gt b (2 ^ N) with hle | hgt
    · obtain ⟨D, hD, hcard, hdom, hsum⟩ := exists_dyadic_prefix N g hle
      exact ⟨D, hD.trans (lift_dyadicSet_subset N), by omega, hdom, hsum⟩
    · have hb' : b - 2 ^ N ≤ 2 ^ N := by rw [pow_succ] at hb; omega
      obtain ⟨D', hD', hcard', hdom', hsum'⟩ :=
        exists_dyadic_prefix N (fun k => g (2 ^ N + k)) hb'
      set Ds := D'.map (shiftDyadic N)
      have hnotMem : (N, 0) ∉ Ds := by
        intro hmem
        rcases mem_map.mp hmem with ⟨⟨m, q⟩, _, heq⟩
        simp only [shiftDyadic, Function.Embedding.coeFn_mk, Prod.mk.injEq] at heq
        rcases heq with ⟨rfl, hq0⟩
        simp at hq0
      refine ⟨insert (N, 0) Ds, ?_, ?_, ?_, ?_⟩
      · refine insert_subset ?_ (map_shiftDyadic_subset hD')
        exact mem_dyadicSet.mpr ⟨by omega, by simp⟩
      · rw [card_insert_of_notMem hnotMem, card_map]
        omega
      · intro p hp
        rcases mem_insert.mp hp with rfl | hp'
        · simp only [zero_add, one_mul]
          exact hgt.le
        · rcases mem_map.mp hp' with ⟨⟨m, q⟩, hmq, rfl⟩
          obtain ⟨hm, _⟩ := mem_dyadicSet.mp (hD' hmq)
          have hd : (q + 1) * 2 ^ m ≤ b - 2 ^ N := hdom' (m, q) hmq
          simp only [shiftDyadic, Function.Embedding.coeFn_mk]
          have hpow : 2 ^ (N - m) * 2 ^ m = 2 ^ N := by
            rw [← pow_add, Nat.sub_add_cancel hm]
          have hcalc : (q + 2 ^ (N - m) + 1) * 2 ^ m = 2 ^ N + (q + 1) * 2 ^ m := by
            calc (q + 2 ^ (N - m) + 1) * 2 ^ m = 2 ^ (N - m) * 2 ^ m + (q + 1) * 2 ^ m := by ring
              _ = 2 ^ N + (q + 1) * 2 ^ m := by rw [hpow]
          rw [hcalc]
          omega
      · rw [sum_insert hnotMem, sum_map]
        have hsum_eq : ∑ x ∈ D',
            (g (((shiftDyadic N x).2 + 1) * 2 ^ (shiftDyadic N x).1) -
              g ((shiftDyadic N x).2 * 2 ^ (shiftDyadic N x).1)) =
            ∑ x ∈ D', (g (2 ^ N + (x.2 + 1) * 2 ^ x.1) - g (2 ^ N + x.2 * 2 ^ x.1)) := by
          refine sum_congr rfl fun ⟨m, q⟩ hmq => ?_
          obtain ⟨hm, _⟩ := mem_dyadicSet.mp (hD' hmq)
          simp only [shiftDyadic, Function.Embedding.coeFn_mk]
          have hpow : 2 ^ (N - m) * 2 ^ m = 2 ^ N := by
            rw [← pow_add, Nat.sub_add_cancel hm]
          have h1 : (q + 2 ^ (N - m) + 1) * 2 ^ m = 2 ^ N + (q + 1) * 2 ^ m := by
            calc (q + 2 ^ (N - m) + 1) * 2 ^ m = 2 ^ (N - m) * 2 ^ m + (q + 1) * 2 ^ m := by ring
              _ = 2 ^ N + (q + 1) * 2 ^ m := by rw [hpow]
          have h2 : (q + 2 ^ (N - m)) * 2 ^ m = 2 ^ N + q * 2 ^ m := by
            calc (q + 2 ^ (N - m)) * 2 ^ m = 2 ^ (N - m) * 2 ^ m + q * 2 ^ m := by ring
              _ = 2 ^ N + q * 2 ^ m := by rw [hpow]
          rw [h1, h2]
        rw [hsum_eq, ← hsum']
        simp only [Nat.add_sub_of_le hgt.le, add_zero, zero_add, one_mul, zero_mul]
        ring

private lemma exists_dyadic_suffix :
    ∀ (N : ℕ) (g : ℕ → ℝ) {a : ℕ}, a ≤ 2 ^ N →
      ∃ D ⊆ dyadicSet N, D.card ≤ N + 1 ∧
        (∀ p ∈ D, a ≤ p.2 * 2 ^ p.1) ∧
        g (2 ^ N) - g a = ∑ p ∈ D, (g ((p.2 + 1) * 2 ^ p.1) - g (p.2 * 2 ^ p.1))
  | 0, g, a, ha => by
    rcases (by omega : a = 0 ∨ a = 1) with rfl | rfl
    · refine ⟨{(0, 0)}, ?_, by simp, by simp, by simp⟩
      intro p hp; rw [mem_singleton.mp hp]; exact mem_dyadicSet.mpr ⟨le_rfl, by norm_num⟩
    · exact ⟨∅, empty_subset _, by simp, by simp, by simp⟩
  | N + 1, g, a, ha => by
    rcases le_or_gt (2 ^ N) a with hge | hlt
    · have ha' : a - 2 ^ N ≤ 2 ^ N := by rw [pow_succ] at ha; omega
      obtain ⟨D', hD', hcard', hdom', hsum'⟩ :=
        exists_dyadic_suffix N (fun k => g (2 ^ N + k)) ha'
      refine ⟨D'.map (shiftDyadic N), map_shiftDyadic_subset hD', ?_, ?_, ?_⟩
      · rw [card_map]; omega
      · intro p hp
        rcases mem_map.mp hp with ⟨⟨m, q⟩, hmq, rfl⟩
        obtain ⟨hm, _⟩ := mem_dyadicSet.mp (hD' hmq)
        have hd : a - 2 ^ N ≤ q * 2 ^ m := hdom' (m, q) hmq
        simp only [shiftDyadic, Function.Embedding.coeFn_mk]
        have hpow : 2 ^ (N - m) * 2 ^ m = 2 ^ N := by
          rw [← pow_add, Nat.sub_add_cancel hm]
        have hcalc : (q + 2 ^ (N - m)) * 2 ^ m = 2 ^ N + q * 2 ^ m := by
          calc (q + 2 ^ (N - m)) * 2 ^ m = 2 ^ (N - m) * 2 ^ m + q * 2 ^ m := by ring
            _ = 2 ^ N + q * 2 ^ m := by rw [hpow]
        rw [hcalc]
        omega
      · rw [sum_map]
        have hsum_eq : ∑ x ∈ D',
            (g (((shiftDyadic N x).2 + 1) * 2 ^ (shiftDyadic N x).1) -
              g ((shiftDyadic N x).2 * 2 ^ (shiftDyadic N x).1)) =
            ∑ x ∈ D', (g (2 ^ N + (x.2 + 1) * 2 ^ x.1) - g (2 ^ N + x.2 * 2 ^ x.1)) := by
          refine sum_congr rfl fun ⟨m, q⟩ hmq => ?_
          obtain ⟨hm, _⟩ := mem_dyadicSet.mp (hD' hmq)
          simp only [shiftDyadic, Function.Embedding.coeFn_mk]
          have hpow : 2 ^ (N - m) * 2 ^ m = 2 ^ N := by
            rw [← pow_add, Nat.sub_add_cancel hm]
          have h1 : (q + 2 ^ (N - m) + 1) * 2 ^ m = 2 ^ N + (q + 1) * 2 ^ m := by
            calc (q + 2 ^ (N - m) + 1) * 2 ^ m = 2 ^ (N - m) * 2 ^ m + (q + 1) * 2 ^ m := by ring
              _ = 2 ^ N + (q + 1) * 2 ^ m := by rw [hpow]
          have h2 : (q + 2 ^ (N - m)) * 2 ^ m = 2 ^ N + q * 2 ^ m := by
            calc (q + 2 ^ (N - m)) * 2 ^ m = 2 ^ (N - m) * 2 ^ m + q * 2 ^ m := by ring
              _ = 2 ^ N + q * 2 ^ m := by rw [hpow]
          rw [h1, h2]
        rw [hsum_eq, ← hsum', Nat.add_sub_of_le hge]
        have htwo : 2 ^ (N + 1) = 2 ^ N + 2 ^ N := by rw [pow_succ]; ring
        rw [htwo]
    · obtain ⟨D', hD', hcard', hdom', hsum'⟩ := exists_dyadic_suffix N g hlt.le
      have hnotMem : (N, 1) ∉ D' := by
        intro hmem
        obtain ⟨_, hq⟩ := mem_dyadicSet.mp (hD' hmem)
        have : N - N = 0 := Nat.sub_self N
        rw [this, pow_zero] at hq
        omega
      refine ⟨insert (N, 1) D', ?_, ?_, ?_, ?_⟩
      · refine insert_subset ?_ (hD'.trans (lift_dyadicSet_subset N))
        exact mem_dyadicSet.mpr ⟨by omega, by norm_num⟩
      · rw [card_insert_of_notMem hnotMem]; omega
      · intro p hp
        rcases mem_insert.mp hp with rfl | hp'
        · simp only [one_mul]; exact hlt.le
        · exact hdom' p hp'
      · rw [sum_insert hnotMem, ← hsum']
        have htwo : (1 + 1) * 2 ^ N = 2 ^ (N + 1) := by rw [pow_succ]; ring
        simp only [one_mul, htwo]
        ring

/-- Every discrete interval `[a, b) ⊆ [0, 2^N)` decomposes into at most `2 (N + 1)` dyadic
subintervals contained in `[a, b)`. -/
theorem exists_dyadic_interval :
    ∀ (N : ℕ) (g : ℕ → ℝ) {a b : ℕ}, a ≤ b → b ≤ 2 ^ N →
      ∃ D ⊆ dyadicSet N, D.card ≤ 2 * (N + 1) ∧
        (∀ p ∈ D, a ≤ p.2 * 2 ^ p.1 ∧ (p.2 + 1) * 2 ^ p.1 ≤ b) ∧
        g b - g a = ∑ p ∈ D, (g ((p.2 + 1) * 2 ^ p.1) - g (p.2 * 2 ^ p.1))
  | 0, g, a, b, hab, hb => by
    rcases (by omega : a = b ∨ (a = 0 ∧ b = 1)) with rfl | ⟨rfl, rfl⟩
    · exact ⟨∅, empty_subset _, by simp, by simp, by simp⟩
    · refine ⟨{(0, 0)}, ?_, by simp, ?_, by simp⟩
      · intro p hp; rw [mem_singleton.mp hp]; exact mem_dyadicSet.mpr ⟨le_rfl, by norm_num⟩
      · intro p hp; rw [mem_singleton.mp hp]; norm_num
  | N + 1, g, a, b, hab, hb => by
    rcases le_or_gt b (2 ^ N) with hble | hbgt
    · obtain ⟨D, hD, hcard, hdom, hsum⟩ := exists_dyadic_interval N g hab hble
      exact ⟨D, hD.trans (lift_dyadicSet_subset N), by omega, hdom, hsum⟩
    rcases le_or_gt (2 ^ N) a with hage | halt
    · have hab' : a - 2 ^ N ≤ b - 2 ^ N := by omega
      have hb' : b - 2 ^ N ≤ 2 ^ N := by rw [pow_succ] at hb; omega
      obtain ⟨D', hD', hcard', hdom', hsum'⟩ :=
        exists_dyadic_interval N (fun k => g (2 ^ N + k)) hab' hb'
      refine ⟨D'.map (shiftDyadic N), map_shiftDyadic_subset hD', ?_, ?_, ?_⟩
      · rw [card_map]; omega
      · intro p hp
        rcases mem_map.mp hp with ⟨⟨m, q⟩, hmq, rfl⟩
        obtain ⟨hm, _⟩ := mem_dyadicSet.mp (hD' hmq)
        obtain ⟨hd1, hd2⟩ : a - 2 ^ N ≤ q * 2 ^ m ∧ (q + 1) * 2 ^ m ≤ b - 2 ^ N := hdom' (m, q) hmq
        simp only [shiftDyadic, Function.Embedding.coeFn_mk]
        have hpow : 2 ^ (N - m) * 2 ^ m = 2 ^ N := by
          rw [← pow_add, Nat.sub_add_cancel hm]
        have h1 : (q + 2 ^ (N - m)) * 2 ^ m = 2 ^ N + q * 2 ^ m := by
          calc (q + 2 ^ (N - m)) * 2 ^ m = 2 ^ (N - m) * 2 ^ m + q * 2 ^ m := by ring
            _ = 2 ^ N + q * 2 ^ m := by rw [hpow]
        have h2 : (q + 2 ^ (N - m) + 1) * 2 ^ m = 2 ^ N + (q + 1) * 2 ^ m := by
          calc (q + 2 ^ (N - m) + 1) * 2 ^ m = 2 ^ (N - m) * 2 ^ m + (q + 1) * 2 ^ m := by ring
            _ = 2 ^ N + (q + 1) * 2 ^ m := by rw [hpow]
        rw [h1, h2]
        omega
      · rw [sum_map]
        have hsum_eq : ∑ x ∈ D',
            (g (((shiftDyadic N x).2 + 1) * 2 ^ (shiftDyadic N x).1) -
              g ((shiftDyadic N x).2 * 2 ^ (shiftDyadic N x).1)) =
            ∑ x ∈ D', (g (2 ^ N + (x.2 + 1) * 2 ^ x.1) - g (2 ^ N + x.2 * 2 ^ x.1)) := by
          refine sum_congr rfl fun ⟨m, q⟩ hmq => ?_
          obtain ⟨hm, _⟩ := mem_dyadicSet.mp (hD' hmq)
          simp only [shiftDyadic, Function.Embedding.coeFn_mk]
          have hpow : 2 ^ (N - m) * 2 ^ m = 2 ^ N := by
            rw [← pow_add, Nat.sub_add_cancel hm]
          have h1 : (q + 2 ^ (N - m) + 1) * 2 ^ m = 2 ^ N + (q + 1) * 2 ^ m := by
            calc (q + 2 ^ (N - m) + 1) * 2 ^ m = 2 ^ (N - m) * 2 ^ m + (q + 1) * 2 ^ m := by ring
              _ = 2 ^ N + (q + 1) * 2 ^ m := by rw [hpow]
          have h2 : (q + 2 ^ (N - m)) * 2 ^ m = 2 ^ N + q * 2 ^ m := by
            calc (q + 2 ^ (N - m)) * 2 ^ m = 2 ^ (N - m) * 2 ^ m + q * 2 ^ m := by ring
              _ = 2 ^ N + q * 2 ^ m := by rw [hpow]
          rw [h1, h2]
        rw [hsum_eq, ← hsum', Nat.add_sub_of_le hbgt.le, Nat.add_sub_of_le hage]
    · obtain ⟨D₁, hD₁, hc₁, hdom₁, hsum₁⟩ := exists_dyadic_suffix N g halt.le
      have hb' : b - 2 ^ N ≤ 2 ^ N := by rw [pow_succ] at hb; omega
      obtain ⟨D₂, hD₂, hc₂, hdom₂, hsum₂⟩ :=
        exists_dyadic_prefix N (fun k => g (2 ^ N + k)) hb'
      set D₂s := D₂.map (shiftDyadic N)
      have hdisj : Disjoint D₁ D₂s := by
        rw [Finset.disjoint_left]
        intro ⟨m, q⟩ h₁ h₂
        obtain ⟨hm₁, hq₁⟩ := mem_dyadicSet.mp (hD₁ h₁)
        have hup₁ : (q + 1) * 2 ^ m ≤ 2 ^ N := by
          have : q + 1 ≤ 2 ^ (N - m) := by omega
          calc (q + 1) * 2 ^ m ≤ 2 ^ (N - m) * 2 ^ m := Nat.mul_le_mul_right _ this
            _ = 2 ^ N := by rw [← pow_add, Nat.sub_add_cancel hm₁]
        rcases mem_map.mp h₂ with ⟨⟨m', q'⟩, hmq', heq⟩
        obtain ⟨hm', _⟩ := mem_dyadicSet.mp (hD₂ hmq')
        simp only [shiftDyadic, Function.Embedding.coeFn_mk, Prod.mk.injEq] at heq
        rcases heq with ⟨hm_eq, hq_eq⟩
        subst hm_eq
        have hlo₂ : 2 ^ N ≤ q * 2 ^ m' := by
          rw [← hq_eq]
          calc 2 ^ N = 2 ^ (N - m') * 2 ^ m' := by rw [← pow_add, Nat.sub_add_cancel hm']
            _ ≤ (q' + 2 ^ (N - m')) * 2 ^ m' := Nat.mul_le_mul_right _ (Nat.le_add_left _ _)
        have hpos : 0 < 2 ^ m' := pow_pos (by norm_num) m'
        nlinarith
      refine ⟨D₁ ∪ D₂s, union_subset (hD₁.trans (lift_dyadicSet_subset N))
        (map_shiftDyadic_subset hD₂), ?_, ?_, ?_⟩
      · calc (D₁ ∪ D₂s).card ≤ D₁.card + D₂s.card := card_union_le _ _
          _ = D₁.card + D₂.card := by rw [card_map]
          _ ≤ 2 * (N + 2) := by omega
      · intro p hp
        rcases mem_union.mp hp with hp₁ | hp₂
        · obtain ⟨hm₁, hq₁⟩ := mem_dyadicSet.mp (hD₁ hp₁)
          refine ⟨hdom₁ p hp₁, ?_⟩
          have : p.2 + 1 ≤ 2 ^ (N - p.1) := by omega
          calc (p.2 + 1) * 2 ^ p.1 ≤ 2 ^ (N - p.1) * 2 ^ p.1 := Nat.mul_le_mul_right _ this
            _ = 2 ^ N := by rw [← pow_add, Nat.sub_add_cancel hm₁]
            _ ≤ b := hbgt.le
        · rcases mem_map.mp hp₂ with ⟨⟨m, q⟩, hmq, rfl⟩
          obtain ⟨hm, _⟩ := mem_dyadicSet.mp (hD₂ hmq)
          have hd₂ : (q + 1) * 2 ^ m ≤ b - 2 ^ N := hdom₂ (m, q) hmq
          simp only [shiftDyadic, Function.Embedding.coeFn_mk]
          have hpow : 2 ^ (N - m) * 2 ^ m = 2 ^ N := by
            rw [← pow_add, Nat.sub_add_cancel hm]
          have h1 : (q + 2 ^ (N - m)) * 2 ^ m = 2 ^ N + q * 2 ^ m := by
            calc (q + 2 ^ (N - m)) * 2 ^ m = 2 ^ (N - m) * 2 ^ m + q * 2 ^ m := by ring
              _ = 2 ^ N + q * 2 ^ m := by rw [hpow]
          have h2 : (q + 2 ^ (N - m) + 1) * 2 ^ m = 2 ^ N + (q + 1) * 2 ^ m := by
            calc (q + 2 ^ (N - m) + 1) * 2 ^ m = 2 ^ (N - m) * 2 ^ m + (q + 1) * 2 ^ m := by ring
              _ = 2 ^ N + (q + 1) * 2 ^ m := by rw [hpow]
          rw [h1, h2]
          omega
      · rw [sum_union hdisj, ← hsum₁, sum_map]
        have hsum_eq : ∑ x ∈ D₂,
            (g (((shiftDyadic N x).2 + 1) * 2 ^ (shiftDyadic N x).1) -
              g ((shiftDyadic N x).2 * 2 ^ (shiftDyadic N x).1)) =
            ∑ x ∈ D₂, (g (2 ^ N + (x.2 + 1) * 2 ^ x.1) - g (2 ^ N + x.2 * 2 ^ x.1)) := by
          refine sum_congr rfl fun ⟨m, q⟩ hmq => ?_
          obtain ⟨hm, _⟩ := mem_dyadicSet.mp (hD₂ hmq)
          simp only [shiftDyadic, Function.Embedding.coeFn_mk]
          have hpow : 2 ^ (N - m) * 2 ^ m = 2 ^ N := by
            rw [← pow_add, Nat.sub_add_cancel hm]
          have h1 : (q + 2 ^ (N - m) + 1) * 2 ^ m = 2 ^ N + (q + 1) * 2 ^ m := by
            calc (q + 2 ^ (N - m) + 1) * 2 ^ m = 2 ^ (N - m) * 2 ^ m + (q + 1) * 2 ^ m := by ring
              _ = 2 ^ N + (q + 1) * 2 ^ m := by rw [hpow]
          have h2 : (q + 2 ^ (N - m)) * 2 ^ m = 2 ^ N + q * 2 ^ m := by
            calc (q + 2 ^ (N - m)) * 2 ^ m = 2 ^ (N - m) * 2 ^ m + q * 2 ^ m := by ring
              _ = 2 ^ N + q * 2 ^ m := by rw [hpow]
          rw [h1, h2]
        rw [hsum_eq, ← hsum₂]
        simp only [Nat.add_sub_of_le hbgt.le, add_zero]
        ring

/-- Greedy tube-exit anchor: holds the previous anchor until `g` exits the `Δ`-tube. -/
def greedyAnchor (g : ℕ → ℝ) (Δ : ℝ) : ℕ → ℕ
  | 0 => 0
  | k + 1 =>
      let a := greedyAnchor g Δ k
      if Δ ≤ |g (k + 1) - g a| then k + 1 else a

theorem greedyAnchor_le (g : ℕ → ℝ) (Δ : ℝ) : ∀ k, greedyAnchor g Δ k ≤ k
  | 0 => le_rfl
  | k + 1 => by
      simp only [greedyAnchor]
      split_ifs
      · exact le_rfl
      · exact (greedyAnchor_le g Δ k).trans (Nat.le_succ k)

theorem greedyAnchor_mono (g : ℕ → ℝ) (Δ : ℝ) : Monotone (greedyAnchor g Δ) := by
  refine monotone_nat_of_le_succ fun k => ?_
  simp only [greedyAnchor]
  split_ifs
  · exact (greedyAnchor_le g Δ k).trans (Nat.le_succ k)
  · exact le_rfl

theorem abs_sub_greedyAnchor_lt (g : ℕ → ℝ) {Δ : ℝ} (hΔ : 0 < Δ) :
    ∀ k, |g k - g (greedyAnchor g Δ k)| < Δ
  | 0 => by simp [greedyAnchor, hΔ]
  | k + 1 => by
      simp only [greedyAnchor]
      split_ifs with h
      · simp [hΔ]
      · exact not_le.mp h

/-- Indices `k < 2^N` where `k + 1` triggers a greedy tube exit. -/
def greedyExits (N : ℕ) (g : ℕ → ℝ) (Δ : ℝ) : Finset ℕ :=
  (range (2 ^ N)).filter fun k => Δ ≤ |g (k + 1) - g (greedyAnchor g Δ k)|

/-- The number of greedy tube exits on `[0, 2^N]` is bounded by `2 (N + 1) / Δ²` times the
dyadic Haar energy. -/
theorem card_greedyExits_mul_sq_le (N : ℕ) (g : ℕ → ℝ) {Δ : ℝ} (hΔ : 0 < Δ) :
    ((greedyExits N g Δ).card : ℝ) * Δ ^ 2 ≤ 2 * ((N : ℝ) + 1) * dyadicEnergy N g := by
  classical
  have hex : ∀ k, ∃ D : Finset (ℕ × ℕ), k ∈ greedyExits N g Δ →
      D ⊆ dyadicSet N ∧ D.card ≤ 2 * (N + 1) ∧
      (∀ p ∈ D, greedyAnchor g Δ k ≤ p.2 * 2 ^ p.1 ∧ (p.2 + 1) * 2 ^ p.1 ≤ k + 1) ∧
      g (k + 1) - g (greedyAnchor g Δ k) =
        ∑ p ∈ D, (g ((p.2 + 1) * 2 ^ p.1) - g (p.2 * 2 ^ p.1)) := by
    intro k
    by_cases hk : k ∈ greedyExits N g Δ
    · obtain ⟨hk_lt, _⟩ := mem_filter.mp hk
      rw [Finset.mem_range] at hk_lt
      obtain ⟨D, hD, hcard, hdom, hsum⟩ := exists_dyadic_interval N g
        ((greedyAnchor_le g Δ k).trans (Nat.le_succ k)) (by omega)
      exact ⟨D, fun _ => ⟨hD, hcard, hdom, hsum⟩⟩
    · exact ⟨∅, fun h => absurd h hk⟩
  choose D hD using hex
  have hdisj : (greedyExits N g Δ : Set ℕ).PairwiseDisjoint D := by
    intro k₁ hk₁ k₂ hk₂ hne
    wlog hlt : k₁ < k₂ generalizing k₁ k₂
    · exact (this hk₂ hk₁ hne.symm (by omega)).symm
    change Disjoint (D k₁) (D k₂)
    rw [Finset.disjoint_left]
    intro p hp₁ hp₂
    have hd₁ := (hD k₁ hk₁).2.2.1 p hp₁
    have hd₂ := (hD k₂ hk₂).2.2.1 p hp₂
    have hex₁ : greedyAnchor g Δ (k₁ + 1) = k₁ + 1 := by
      have hc := (mem_filter.mp hk₁).2
      simp [greedyAnchor, hc]
    have hmon : k₁ + 1 ≤ greedyAnchor g Δ k₂ := by
      rw [← hex₁]
      exact greedyAnchor_mono g Δ (by omega)
    have hpos : 0 < 2 ^ p.1 := pow_pos (by norm_num) p.1
    nlinarith
  have hterm : ∀ k ∈ greedyExits N g Δ,
      Δ ^ 2 ≤ 2 * ((N : ℝ) + 1) *
        ∑ p ∈ D k, (g ((p.2 + 1) * 2 ^ p.1) - g (p.2 * 2 ^ p.1)) ^ 2 := by
    intro k hk
    obtain ⟨_, hcard, _, hsum⟩ := hD k hk
    have hexit : Δ ≤ |g (k + 1) - g (greedyAnchor g Δ k)| := (mem_filter.mp hk).2
    have hsq1 : Δ ^ 2 ≤ (g (k + 1) - g (greedyAnchor g Δ k)) ^ 2 := by
      rw [← sq_abs (g (k + 1) - g (greedyAnchor g Δ k))]
      exact pow_le_pow_left₀ hΔ.le hexit 2
    have hcs : (∑ p ∈ D k, (g ((p.2 + 1) * 2 ^ p.1) - g (p.2 * 2 ^ p.1))) ^ 2 ≤
        ((D k).card : ℝ) * ∑ p ∈ D k, (g ((p.2 + 1) * 2 ^ p.1) - g (p.2 * 2 ^ p.1)) ^ 2 :=
      sq_sum_le_card_mul_sum_sq
    have hcardR : ((D k).card : ℝ) ≤ 2 * ((N : ℝ) + 1) := by exact_mod_cast hcard
    calc Δ ^ 2 ≤ (∑ p ∈ D k, (g ((p.2 + 1) * 2 ^ p.1) - g (p.2 * 2 ^ p.1))) ^ 2 := by
          rwa [← hsum]
      _ ≤ ((D k).card : ℝ) * ∑ p ∈ D k, (g ((p.2 + 1) * 2 ^ p.1) - g (p.2 * 2 ^ p.1)) ^ 2 := hcs
      _ ≤ 2 * ((N : ℝ) + 1) * ∑ p ∈ D k, (g ((p.2 + 1) * 2 ^ p.1) - g (p.2 * 2 ^ p.1)) ^ 2 :=
          mul_le_mul_of_nonneg_right hcardR (sum_nonneg fun _ _ => sq_nonneg _)
  have hsum_exits := sum_le_sum hterm
  rw [sum_const, nsmul_eq_mul, ← mul_sum, ← sum_biUnion hdisj] at hsum_exits
  refine hsum_exits.trans (mul_le_mul_of_nonneg_left ?_ (by positivity))
  refine sum_le_sum_of_subset_of_nonneg ?_ fun _ _ _ => sq_nonneg _
  intro p hp
  rcases mem_biUnion.mp hp with ⟨k, hk, hpk⟩
  exact (hD k hk).1 hpk

/-- Integer value of the greedy step approximation at grid index `k`. -/
def greedyApprox (g : ℕ → ℝ) (Δ : ℝ) (k : ℕ) : ℤ :=
  ⌊g (greedyAnchor g Δ k)⌋

/-- Integer jump of the greedy step approximation between `k` and `k + 1`. -/
def greedyJump (g : ℕ → ℝ) (Δ : ℝ) (k : ℕ) : ℤ :=
  greedyApprox g Δ (k + 1) - greedyApprox g Δ k

theorem abs_greedyApprox_sub_le (g : ℕ → ℝ) {Δ : ℝ} (hΔ : 0 < Δ) (k : ℕ) :
    |(greedyApprox g Δ k : ℝ) - g k| ≤ Δ + 1 := by
  have htube := abs_sub_greedyAnchor_lt g hΔ k
  have hfl1 : (greedyApprox g Δ k : ℝ) ≤ g (greedyAnchor g Δ k) := Int.floor_le _
  have hfl2 : g (greedyAnchor g Δ k) < (greedyApprox g Δ k : ℝ) + 1 := Int.lt_floor_add_one _
  rw [abs_lt] at htube
  rw [abs_le]
  constructor <;> linarith

theorem greedyJump_eq_zero_of_notMem {N k : ℕ} {g : ℕ → ℝ} {Δ : ℝ}
    (hkN : k < 2 ^ N) (hk : k ∉ greedyExits N g Δ) :
    greedyJump g Δ k = 0 := by
  have hnot : ¬ Δ ≤ |g (k + 1) - g (greedyAnchor g Δ k)| := fun h =>
    hk (mem_filter.mpr ⟨Finset.mem_range.mpr hkN, h⟩)
  simp [greedyJump, greedyApprox, greedyAnchor, hnot]

theorem abs_greedyJump_le (g : ℕ → ℝ) {Δ S : ℝ} (hΔ : 0 < Δ)
    (hstep : ∀ k, |g (k + 1) - g k| ≤ S) (k : ℕ) :
    |(greedyJump g Δ k : ℝ)| ≤ Δ + S + 1 := by
  by_cases hex : Δ ≤ |g (k + 1) - g (greedyAnchor g Δ k)|
  · have hanch : greedyAnchor g Δ (k + 1) = k + 1 := by simp [greedyAnchor, hex]
    have htube := abs_sub_greedyAnchor_lt g hΔ k
    have hst := hstep k
    have h1 : (greedyApprox g Δ (k + 1) : ℝ) ≤ g (k + 1) := by
      rw [greedyApprox, hanch]; exact Int.floor_le _
    have h2 : g (k + 1) < (greedyApprox g Δ (k + 1) : ℝ) + 1 := by
      rw [greedyApprox, hanch]; exact Int.lt_floor_add_one _
    have h3 : (greedyApprox g Δ k : ℝ) ≤ g (greedyAnchor g Δ k) := Int.floor_le _
    have h4 : g (greedyAnchor g Δ k) < (greedyApprox g Δ k : ℝ) + 1 := Int.lt_floor_add_one _
    rw [greedyJump, Int.cast_sub, abs_le]
    rw [abs_lt] at htube
    rw [abs_le] at hst
    constructor <;> linarith
  · have hanch : greedyAnchor g Δ (k + 1) = greedyAnchor g Δ k := by simp [greedyAnchor, hex]
    have hzero : greedyJump g Δ k = 0 := by simp [greedyJump, greedyApprox, hanch]
    have hS0 : 0 ≤ S := (abs_nonneg _).trans (hstep 0)
    rw [hzero, Int.cast_zero, abs_zero]
    linarith

theorem sum_Ico_greedyJump (g : ℕ → ℝ) (Δ : ℝ) {a b : ℕ} (hab : a ≤ b) :
    ∑ k ∈ Ico a b, greedyJump g Δ k = greedyApprox g Δ b - greedyApprox g Δ a := by
  induction b, hab using Nat.le_induction with
  | base => simp
  | succ b hle ih =>
    rw [Finset.sum_Ico_succ_top hle, ih, greedyJump]
    ring

end GaloisForLFunctions.ArithmeticAuxiliaryDynamics
