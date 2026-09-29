import GaloisForLFunctions.HTGeometry.PrimePoissonFormationFrame

/-!
# Injectivity of the prime Gamma frames

For every degree `k ≥ 1` and aperture `d > 0` the prime frame
`W_d^{(k)} x = ∑_p x_p √μ_d(p) ψ_{log p}^{(k)}` is injective.

If `W x = 0`, pairing with every coherent vector `ψ_s^{(k)}` and exchanging sum and integral shows
that the Laplace transform of `r^{k-1} D(r)` vanishes on the positive axis, where
`D(r) = ∑_p b_p p^{-r}` is an absolutely convergent Dirichlet series with
`b_p = x_p √μ_d(p) √((2 log p)^k/(k-1)!)`.  Laplace injectivity gives `D = 0` almost everywhere on
`(0,∞)`, hence along a sequence `r_n → ∞`, and isolating the least prime with a nonzero coefficient
by `p₀^{r_n} D(r_n) → b_{p₀}` forces every coefficient to vanish.

Together with totality of the prime clocks, the left Gram `B_d^{(k)} = W W*` is positive, of trace
one, injective and with dense range.
-/

open MeasureTheory Set Filter Topology Asymptotics
open scoped ENNReal InnerProductSpace ComplexConjugate

noncomputable section

namespace GaloisForLFunctions.HTGeometry

open _root_.RHTower

/-! ## Moment summability of the formation law -/

theorem transportedPrimeWeight_eq_rpow {d : ℝ} (p : Nat.Primes) :
    routePPrimitiveGammaJuliaStokesTransportedPrimeWeight d p =
      8 * d * Real.log p * (p : ℝ) ^ (-(1 + 2 * d)) := by
  have hp : (0 : ℝ) < p := by exact_mod_cast p.2.pos
  rw [transportedPrimeWeight_eq_scale, routePPrimitiveGammaJuliaStokesApertureScaleSq]
  have h1 : (p : ℝ) ^ (-(1 + 2 * d)) = ((p : ℝ) * (p : ℝ) ^ (2 * d))⁻¹ := by
    rw [Real.rpow_neg hp.le, Real.rpow_add hp, Real.rpow_one]
  have h2 : (p : ℝ) ^ (-2 * d) = ((p : ℝ) ^ (2 * d))⁻¹ := by
    rw [show -2 * d = -(2 * d) by ring, Real.rpow_neg hp.le]
  rw [h1, h2]
  have h3 : (0 : ℝ) < (p : ℝ) ^ (2 * d) := Real.rpow_pos_of_pos hp _
  field_simp
  ring

theorem summable_log_pow_mul_rpow_nat {d : ℝ} (hd : 0 < d) (m : ℕ) :
    Summable fun n : ℕ => Real.log n ^ m * (n : ℝ) ^ (-(1 + 2 * d)) := by
  have hlo := (isLittleO_log_rpow_rpow_atTop (m : ℝ) hd).comp_tendsto
    tendsto_natCast_atTop_atTop
  have hO : (fun n : ℕ => Real.log n ^ m * (n : ℝ) ^ (-(1 + 2 * d))) =O[atTop]
      fun n : ℕ => ((n : ℝ) ^ (1 + d))⁻¹ := by
    have h1 := hlo.isBigO.mul (isBigO_refl (fun n : ℕ => (n : ℝ) ^ (-(1 + 2 * d))) atTop)
    refine h1.congr' ?_ ?_
    · filter_upwards with n
      simp [Function.comp, Real.rpow_natCast]
    · filter_upwards [eventually_gt_atTop 0] with n hn
      have hn' : (0 : ℝ) < n := Nat.cast_pos.mpr hn
      simp only [Function.comp]
      rw [← Real.rpow_add hn', ← Real.rpow_neg hn'.le]
      ring_nf
  exact summable_of_isBigO_nat (Real.summable_nat_rpow_inv.mpr (by linarith)) hO

/-- `∑_p μ_d(p) (log p)^m < ∞`. -/
theorem summable_primeFormationLaw_mul_log_pow {d : ℝ} (hd : 0 < d) (m : ℕ) :
    Summable fun p : Nat.Primes => primeFormationLaw d p * Real.log p ^ m := by
  have hnat := (summable_log_pow_mul_rpow_nat hd (m + 1)).comp_injective
    (Subtype.val_injective : Function.Injective (fun p : Nat.Primes => (p : ℕ)))
  have h := (hnat.mul_left (8 * d)).div_const
    (gammaSewnMobiusApertureStokesOrientedFirstTraceCurrent d)
  refine h.congr fun p => ?_
  simp only [Function.comp, primeFormationLaw, transportedPrimeWeight_eq_rpow]
  ring

/-! ## Dirichlet isolation -/

/-- An absolutely summable Dirichlet series over the primes that vanishes along a sequence
`r_n → ∞` has every coefficient zero. -/
theorem eq_zero_of_primeDirichlet_vanishing {b : Nat.Primes → ℂ} (hb : Summable fun p => ‖b p‖)
    {r : ℕ → ℝ} (hr : Tendsto r atTop atTop)
    (h : ∀ n, ∑' p, b p * (((p : ℝ) ^ (-(r n)) : ℝ) : ℂ) = 0) : b = 0 := by
  by_contra hne
  have hex : ∃ m : ℕ, ∃ hm : m.Prime, b ⟨m, hm⟩ ≠ 0 := by
    by_contra hall
    push Not at hall
    exact hne (funext fun p => hall p.1 p.2)
  classical
  set m₀ := Nat.find hex
  obtain ⟨hm₀, hb₀⟩ := Nat.find_spec hex
  set p₀ : Nat.Primes := ⟨m₀, hm₀⟩
  have hmin : ∀ p : Nat.Primes, (p : ℕ) < m₀ → b p = 0 := by
    intro p hp
    by_contra hbp
    exact Nat.find_min hex hp ⟨p.2, by simpa using hbp⟩
  have hp₀pos : (0 : ℝ) < m₀ := by exact_mod_cast hm₀.pos
  set g : Nat.Primes → ℂ := fun p => if p = p₀ then b p₀ else 0
  have hterm : ∀ p : Nat.Primes, Tendsto (fun n => b p * ((((m₀ : ℝ) / p) ^ (r n) : ℝ) : ℂ)) atTop
      (𝓝 (g p)) := by
    intro p
    by_cases hpp : p = p₀
    · subst hpp
      simp only [g, if_pos rfl]
      have h1 : ∀ n, ((((m₀ : ℝ) / (p₀ : ℕ)) ^ (r n) : ℝ) : ℂ) = 1 := fun n => by
        simp [p₀, div_self hp₀pos.ne']
      simp_rw [h1, mul_one]
      exact tendsto_const_nhds
    · simp only [g, if_neg hpp]
      rcases lt_or_gt_of_ne (show (p : ℕ) ≠ m₀ from fun h => hpp (Subtype.ext h)) with hlt | hgt
      · simp_rw [hmin p hlt, zero_mul]
        exact tendsto_const_nhds
      · have hbase0 : (0 : ℝ) ≤ (m₀ : ℝ) / p := by positivity
        have hbase1 : (m₀ : ℝ) / p < 1 := by
          rw [div_lt_one (by exact_mod_cast p.2.pos)]
          exact_mod_cast hgt
        have ht := (tendsto_rpow_atTop_of_base_lt_one _ (by linarith) hbase1).comp hr
        have := (Complex.continuous_ofReal.tendsto 0).comp ht
        simpa using this.const_mul (b p)
  have hbound : ∀ᶠ n in atTop, ∀ p : Nat.Primes,
      ‖b p * ((((m₀ : ℝ) / p) ^ (r n) : ℝ) : ℂ)‖ ≤ ‖b p‖ := by
    filter_upwards [hr.eventually (eventually_ge_atTop 0)] with n hn p
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
    by_cases hlt : (p : ℕ) < m₀
    · rw [hmin p hlt, norm_zero, zero_mul]
    · have hle : (m₀ : ℝ) / p ≤ 1 := by
        rw [div_le_one (by exact_mod_cast p.2.pos)]
        exact_mod_cast not_lt.1 hlt
      calc ‖b p‖ * ((m₀ : ℝ) / p) ^ (r n) ≤ ‖b p‖ * 1 :=
            mul_le_mul_of_nonneg_left (Real.rpow_le_one (by positivity) hle hn) (norm_nonneg _)
        _ = ‖b p‖ := mul_one _
  have hlim := tendsto_tsum_of_dominated_convergence hb hterm hbound
  have hzero : ∀ n, ∑' p, b p * ((((m₀ : ℝ) / p) ^ (r n) : ℝ) : ℂ) = 0 := by
    intro n
    have hscale : ∀ p : Nat.Primes, b p * ((((m₀ : ℝ) / p) ^ (r n) : ℝ) : ℂ) =
        (((m₀ : ℝ) ^ (r n) : ℝ) : ℂ) * (b p * (((p : ℝ) ^ (-(r n)) : ℝ) : ℂ)) := fun p => by
      have hp : (0 : ℝ) < p := by exact_mod_cast p.2.pos
      rw [Real.div_rpow hp₀pos.le hp.le, Real.rpow_neg hp.le, div_eq_mul_inv]
      push_cast
      ring
    simp_rw [hscale]
    rw [tsum_mul_left, h n, mul_zero]
  simp_rw [hzero] at hlim
  have hg : ∑' p, g p = b p₀ := by
    simp only [g]
    rw [tsum_ite_eq]
  rw [hg] at hlim
  exact hb₀ (tendsto_nhds_unique tendsto_const_nhds hlim).symm

/-! ## Injectivity -/

/-- The profile constant `C_k(t) = √((2t)^k/(k-1)!)`. -/
def gammaCoherentConst (k : ℕ) (t : ℝ) : ℝ := Real.sqrt ((2 * t) ^ k / ((k - 1).factorial : ℝ))

theorem gammaCoherentProfile_eq_const (k : ℕ) (t r : ℝ) :
    gammaCoherentProfile k t r =
      gammaCoherentConst k t * r ^ (((k : ℝ) - 1) / 2) * Real.exp (-(t * r)) := rfl

theorem exp_neg_log_mul (p : Nat.Primes) (r : ℝ) :
    Real.exp (-(Real.log p * r)) = (p : ℝ) ^ (-r) := by
  have hp : (0 : ℝ) < p := by exact_mod_cast p.2.pos
  rw [Real.rpow_def_of_pos hp]
  ring_nf

/-- **Injectivity of the prime Gamma frame.** -/
theorem primeCoherentSynthesis_injective (k : ℕ) [NeZero k] {d : ℝ} (hd : 0 < d) :
    Function.Injective (primeCoherentSynthesis k hd) := by
  refine (injective_iff_map_eq_zero _).2 fun x hx => ?_
  set α : ℝ := ((k : ℝ) - 1) / 2
  set c : Nat.Primes → ℂ := fun p =>
    (x : Nat.Primes → ℂ) p * (Real.sqrt (primeFormationLaw d p) : ℂ)
  set b : Nat.Primes → ℂ := fun p => c p * (gammaCoherentConst k (Real.log p) : ℂ)
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne k)
  -- coefficient summability
  have hC : ∀ p : Nat.Primes, gammaCoherentConst k (Real.log p) ^ 2 =
      2 ^ k / ((k - 1).factorial : ℝ) * Real.log p ^ k := fun p => by
    rw [gammaCoherentConst, Real.sq_sqrt (by have := primeClock_pos p; positivity), mul_pow]
    ring
  have hμC : Summable fun p : Nat.Primes =>
      primeFormationLaw d p * gammaCoherentConst k (Real.log p) ^ 2 := by
    simp_rw [hC]
    exact ((summable_primeFormationLaw_mul_log_pow hd k).mul_left
      (2 ^ k / ((k - 1).factorial : ℝ))).congr fun p => by ring
  have hx2 := HilbertSchmidt.summable_coe_sq x
  have hbsum : Summable fun p => ‖b p‖ := by
    refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun p => ?_)
      ((hx2.add hμC).div_const 2)
    have hμ := (primeFormationLaw_pos hd p).le
    simp only [b, c, norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.sqrt_nonneg _),
      gammaCoherentConst]
    have hs := Real.sq_sqrt hμ
    have hCC := hC p
    rw [gammaCoherentConst] at hCC
    nlinarith [sq_nonneg (‖(x : Nat.Primes → ℂ) p‖ -
      Real.sqrt (primeFormationLaw d p) * Real.sqrt ((2 * Real.log p) ^ k /
        ((k - 1).factorial : ℝ))), norm_nonneg ((x : Nat.Primes → ℂ) p),
      Real.sqrt_nonneg (primeFormationLaw d p),
      Real.sqrt_nonneg ((2 * Real.log p) ^ k / ((k - 1).factorial : ℝ))]
  have hcsum : Summable fun p => ‖c p‖ := by
    refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun p => ?_)
      ((hx2.add (hasSum_primeFormationLaw hd).summable).div_const 2)
    have hμ := (primeFormationLaw_pos hd p).le
    simp only [c, norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.sqrt_nonneg _)]
    have hs := Real.sq_sqrt hμ
    nlinarith [sq_nonneg (‖(x : Nat.Primes → ℂ) p‖ - Real.sqrt (primeFormationLaw d p))]
  -- the Dirichlet series, truncated at the origin
  set D : ℝ → ℂ := fun r => ∑' p, b p * (((p : ℝ) ^ (-(max r 0)) : ℝ) : ℂ)
  have hDterm : ∀ (p : Nat.Primes) (r : ℝ),
      ‖b p * (((p : ℝ) ^ (-(max r 0)) : ℝ) : ℂ)‖ ≤ ‖b p‖ := fun p r => by
    have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast p.2.one_lt.le
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
    exact mul_le_of_le_one_right (norm_nonneg _)
      (Real.rpow_le_one_of_one_le_of_nonpos hp1 (by linarith [le_max_right r 0]))
  have hDcont : Continuous D := by
    refine continuous_tsum (fun p => ?_) hbsum hDterm
    have hp : (0 : ℝ) < p := by exact_mod_cast p.2.pos
    exact continuous_const.mul (Complex.continuous_ofReal.comp
      ((continuous_const.rpow (by fun_prop) fun _ => Or.inl hp.ne')))
  -- pairing with coherent vectors
  have hpair : ∀ {s : ℝ} (hs : 0 < s),
      ∫ r in Ioi (0 : ℝ), ((gammaCoherentConst k s * r ^ ((k : ℝ) - 1) * Real.exp (-(s * r)) : ℝ)
        : ℂ) * D r = 0 := by
    intro s hs
    have h0 : ⟪gammaCoherentVector k hs, primeCoherentSynthesis k hd x⟫_ℂ = 0 := by
      rw [hx, inner_zero_right]
    rw [primeCoherentSynthesis, squareSummableSynthesis_apply] at h0
    have hmap : ⟪gammaCoherentVector k hs,
          ∑' i, (x : Nat.Primes → ℂ) i • primeCoherentFrame k d i⟫_ℂ =
        ∑' i, ⟪gammaCoherentVector k hs,
          (x : Nat.Primes → ℂ) i • primeCoherentFrame k d i⟫_ℂ := by
      have := (innerSL ℂ (gammaCoherentVector k hs)).map_tsum
        (summable_norm_smul_frame (summable_norm_sq_primeCoherentFrame k hd) x).of_norm
      exact this
    rw [hmap] at h0
    simp only [primeCoherentFrame, inner_smul_right, inner_gammaCoherentVector] at h0
    have hswap : ∫ r in Ioi (0 : ℝ), ∑' p : Nat.Primes, c p *
        ((gammaCoherentProfile k s r * gammaCoherentProfile k (Real.log p) r : ℝ) : ℂ) =
        ∑' p : Nat.Primes, ∫ r in Ioi (0 : ℝ), c p *
          ((gammaCoherentProfile k s r * gammaCoherentProfile k (Real.log p) r : ℝ) : ℂ) := by
      refine (integral_tsum_of_summable_integral_norm (ι := Nat.Primes) (F := fun p r =>
        c p * ((gammaCoherentProfile k s r * gammaCoherentProfile k (Real.log p) r : ℝ) : ℂ))
        (fun p => ?_) ?_).symm
      · refine Integrable.const_mul ?_ _
        have h1 := (memLp_gammaCoherentProfile (NeZero.ne k) hs).integrable_mul
          (memLp_gammaCoherentProfile (NeZero.ne k) (primeClock_pos p))
        refine (h1.congr (Eventually.of_forall fun r => ?_))
        simp
      · refine Summable.of_nonneg_of_le (fun _ => integral_nonneg fun _ => norm_nonneg _)
          (fun p => ?_) hcsum
        have hint : ∫ r in Ioi (0 : ℝ), ‖c p *
            ((gammaCoherentProfile k s r * gammaCoherentProfile k (Real.log p) r : ℝ) : ℂ)‖ =
            ‖c p‖ * (2 * Real.sqrt (s * Real.log p) / (s + Real.log p)) ^ k := by
          rw [← integral_gammaCoherentProfile_mul (NeZero.ne k) hs (primeClock_pos p),
            ← integral_const_mul]
          refine setIntegral_congr_fun measurableSet_Ioi fun r hr => ?_
          rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg]
          rw [gammaCoherentProfile_eq_const, gammaCoherentProfile_eq_const, gammaCoherentConst,
            gammaCoherentConst]
          have hr' : (0 : ℝ) < r := hr
          positivity
        rw [hint]
        have hg1 : (2 * Real.sqrt (s * Real.log p) / (s + Real.log p)) ^ k ≤ 1 := by
          have hlp := primeClock_pos p
          refine pow_le_one₀ (by positivity) ?_
          rw [div_le_one (by positivity), Real.sqrt_mul hs.le]
          nlinarith [sq_nonneg (Real.sqrt s - Real.sqrt (Real.log p)), Real.sq_sqrt hs.le,
            Real.sq_sqrt hlp.le]
        exact mul_le_of_le_one_right (norm_nonneg _) hg1
    have hsum_eq : ∑' p : Nat.Primes, ∫ r in Ioi (0 : ℝ), c p *
        ((gammaCoherentProfile k s r * gammaCoherentProfile k (Real.log p) r : ℝ) : ℂ) = 0 := by
      rw [← h0]
      refine tsum_congr fun p => ?_
      rw [integral_const_mul, integral_complex_ofReal,
        integral_gammaCoherentProfile_mul (NeZero.ne k) hs (primeClock_pos p)]
      simp only [c]
      push_cast
      ring
    rw [← hsum_eq, ← hswap]
    refine setIntegral_congr_fun measurableSet_Ioi fun r hr => ?_
    have hr' : (0 : ℝ) < r := hr
    simp only [D, max_eq_left hr'.le]
    rw [← tsum_mul_left]
    refine tsum_congr fun p => ?_
    simp only [b, gammaCoherentProfile_eq_const, exp_neg_log_mul]
    have hrr : r ^ ((k : ℝ) - 1) = r ^ α * r ^ α := by
      rw [← Real.rpow_add hr']
      simp only [α]
      ring_nf
    rw [hrr]
    push_cast
    ring
  -- Laplace uniqueness
  set φ : ℝ → ℂ := fun r => ((r ^ ((k : ℝ) - 1) : ℝ) : ℂ) * D r
  have hDb : ∀ r, 0 ≤ r → ‖D r‖ ≤ (∑' p, ‖b p‖) * (2 : ℝ) ^ (-r) := by
    intro r hr
    refine (norm_tsum_le_tsum_norm ((hbsum.of_nonneg_of_le (fun _ => norm_nonneg _)
      (hDterm · r)))).trans ?_
    rw [← tsum_mul_right]
    refine Summable.tsum_le_tsum (fun p => ?_) (hbsum.of_nonneg_of_le (fun _ => norm_nonneg _)
      (hDterm · r)) (hbsum.mul_right _)
    have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast p.2.two_le
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (by positivity), max_eq_left hr]
    refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
    rw [Real.rpow_neg (by linarith), Real.rpow_neg (by norm_num)]
    exact inv_anti₀ (by positivity) (Real.rpow_le_rpow (by norm_num) hp2 hr)
  have hφL2 : MemLp φ 2 (volume.restrict (Ioi (0 : ℝ))) := by
    have hbase : MemLp (fun r : ℝ => ((r ^ ((k : ℝ) - 1) * Real.exp (-(Real.log 2 * r)) : ℝ) : ℂ))
        2 (volume.restrict (Ioi (0 : ℝ))) := by
      have hsq : MemLp (fun r : ℝ => r ^ ((k : ℝ) - 1) * Real.exp (-(Real.log 2 * r))) 2
          (volume.restrict (Ioi (0 : ℝ))) := by
        rw [memLp_two_iff_integrable_sq (by
          exact (Measurable.mul (by fun_prop) (by fun_prop)).aestronglyMeasurable)]
        have hint := integrableOn_rpow_mul_exp_neg_mul_rpow (s := 2 * ((k : ℝ) - 1)) (p := 1)
          (b := 2 * Real.log 2) (by linarith) le_rfl (by positivity)
        refine IntegrableOn.congr_fun hint (fun r hr => ?_) measurableSet_Ioi
        have hr' : (0 : ℝ) < r := hr
        rw [Real.rpow_one, mul_pow, ← Real.rpow_natCast (r ^ _) 2, ← Real.rpow_mul hr'.le,
          sq, ← Real.exp_add]
        ring_nf
      exact hsq.ofReal
    refine MemLp.of_le (hbase.const_mul ((∑' p, ‖b p‖ : ℝ) : ℂ)) ?_ ?_
    · exact ((Complex.measurable_ofReal.comp (by fun_prop)).mul
        hDcont.measurable).aestronglyMeasurable
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
      have hr' : (0 : ℝ) < r := hr
      simp only [φ, norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.rpow_nonneg hr'.le _),
        Real.norm_of_nonneg (tsum_nonneg fun _ => norm_nonneg _),
        Real.norm_of_nonneg (mul_nonneg (Real.rpow_nonneg hr'.le _) (Real.exp_pos _).le)]
      have h2 : (2 : ℝ) ^ (-r) = Real.exp (-(Real.log 2 * r)) := by
        rw [Real.rpow_def_of_pos (by norm_num)]
        ring_nf
      calc r ^ ((k : ℝ) - 1) * ‖D r‖ ≤ r ^ ((k : ℝ) - 1) * ((∑' p, ‖b p‖) * 2 ^ (-r)) :=
            mul_le_mul_of_nonneg_left (hDb r hr'.le) (by positivity)
        _ = _ := by rw [h2]; ring
  have hlap : ∀ {s : ℝ}, 0 < s → laplaceRay φ s = 0 := by
    intro s hs
    have h := hpair hs
    have hCs : (gammaCoherentConst k s : ℂ) ≠ 0 := by
      rw [gammaCoherentConst]
      have : (0 : ℝ) < ((k - 1).factorial : ℝ) := by exact_mod_cast Nat.factorial_pos _
      exact Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.2 (by positivity)).ne'
    rw [laplaceRay]
    have hcongr : ∫ r in Ioi (0 : ℝ), ((gammaCoherentConst k s * r ^ ((k : ℝ) - 1) *
        Real.exp (-(s * r)) : ℝ) : ℂ) * D r =
        (gammaCoherentConst k s : ℂ) * ∫ r in Ioi (0 : ℝ), φ r * expRay s r := by
      rw [← integral_const_mul]
      refine setIntegral_congr_fun measurableSet_Ioi fun r _ => ?_
      simp only [φ, expRay]
      push_cast
      ring
    rw [hcongr] at h
    exact (mul_eq_zero.1 h).resolve_left hCs
  have hopen : IsOpen {w : ℂ | 0 < w.re} := isOpen_lt continuous_const Complex.continuous_re
  have hana : AnalyticOnNhd ℂ (laplaceRay φ) {w : ℂ | 0 < w.re} :=
    (differentiableOn_laplaceRay hφL2).analyticOnNhd hopen
  have hfreq : ∃ᶠ w in 𝓝[≠] (1 : ℂ), laplaceRay φ w = 0 := by
    have htend : Tendsto (fun n : ℕ => (((1 : ℝ) + ((n : ℝ) + 1)⁻¹ : ℝ) : ℂ)) atTop (𝓝[≠] 1) := by
      refine tendsto_nhdsWithin_iff.2 ⟨?_, Eventually.of_forall fun n => ?_⟩
      · have h0 : Tendsto (fun n : ℕ => (1 : ℝ) + ((n : ℝ) + 1)⁻¹) atTop (𝓝 1) := by
          simpa using (tendsto_const_nhds (x := (1 : ℝ))).add
            (tendsto_inv_atTop_zero.comp (tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds))
        have := (Complex.continuous_ofReal.tendsto 1).comp h0
        rw [Complex.ofReal_one] at this
        exact this
      · simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
        intro h
        have h1 := Complex.ofReal_eq_one.1 h
        have : (0 : ℝ) < ((n : ℝ) + 1)⁻¹ := by positivity
        linarith
    exact htend.frequently (Frequently.of_forall fun n => hlap (by positivity))
  have heq := hana.eqOn_zero_of_preconnected_of_frequently_eq_zero
    (convex_halfSpace_re_gt 0).isPreconnected (by simp : (1 : ℂ) ∈ {w : ℂ | 0 < w.re}) hfreq
  have hφ0 := ae_eq_zero_of_laplaceRay_eq_zero hφL2 fun w hw => heq hw
  have hD0 : ∀ᵐ r ∂(volume.restrict (Ioi (0 : ℝ))), D r = 0 := by
    filter_upwards [hφ0, ae_restrict_mem measurableSet_Ioi] with r hr hrpos
    have hr' : (0 : ℝ) < r := hrpos
    exact (mul_eq_zero.1 hr).resolve_left (Complex.ofReal_ne_zero.mpr (by positivity))
  -- a sequence of zeros going to infinity
  have hseq : ∀ n : ℕ, ∃ r, (n : ℝ) < r ∧ D r = 0 := by
    intro n
    have hsub : Ioo (n : ℝ) (n + 1) ⊆ Ioi 0 := fun r hr => by
      have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
      exact lt_of_le_of_lt this hr.1
    have hae : ∀ᵐ r ∂(volume.restrict (Ioo (n : ℝ) (n + 1))), D r = 0 :=
      ae_restrict_of_ae_restrict_of_subset hsub hD0
    have hpos : volume (Ioo (n : ℝ) (n + 1)) ≠ 0 := by simp
    haveI : (ae (volume.restrict (Ioo (n : ℝ) (n + 1)))).NeBot := by
      rw [ae_neBot, Ne, Measure.restrict_eq_zero]
      exact hpos
    obtain ⟨r, hr, hDr⟩ := ((ae_restrict_mem measurableSet_Ioo).and hae).exists
    exact ⟨r, hr.1, hDr⟩
  choose rseq hrseq using hseq
  have hrtend : Tendsto rseq atTop atTop :=
    tendsto_atTop_mono (fun n => (hrseq n).1.le) tendsto_natCast_atTop_atTop
  have hb0 := eq_zero_of_primeDirichlet_vanishing hbsum hrtend fun n => by
    have h := (hrseq n).2
    have hpos : (0 : ℝ) < rseq n := lt_of_le_of_lt (Nat.cast_nonneg n) (hrseq n).1
    simp only [D, max_eq_left hpos.le] at h
    exact h
  refine lp.ext (funext fun p => ?_)
  have hbp := congrFun hb0 p
  simp only [b, c, Pi.zero_apply] at hbp
  have hC0 : (gammaCoherentConst k (Real.log p) : ℂ) ≠ 0 := by
    rw [gammaCoherentConst]
    have := primeClock_pos p
    have : (0 : ℝ) < ((k - 1).factorial : ℝ) := by exact_mod_cast Nat.factorial_pos _
    exact Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.2 (by positivity)).ne'
  have hμ0 : ((Real.sqrt (primeFormationLaw d p) : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.2 (primeFormationLaw_pos hd p)).ne'
  rw [lp.coeFn_zero, Pi.zero_apply]
  exact (mul_eq_zero.1 ((mul_eq_zero.1 hbp).resolve_right hC0)).resolve_right hμ0

/-- The prime frame vectors `√μ_d(p) ψ_{log p}^{(k)}` span a dense subspace. -/
theorem primeCoherentFrame_total (k : ℕ) [NeZero k] {d : ℝ} (hd : 0 < d) :
    (Submodule.span ℂ (Set.range (primeCoherentFrame k d))).topologicalClosure = ⊤ := by
  refine eq_top_iff.2 ((gammaCoherent_primeClock_total k ∅).symm.le.trans
    (Submodule.topologicalClosure_mono (Submodule.span_le.2 ?_)))
  rintro _ ⟨p, rfl⟩
  have hμ : ((Real.sqrt (primeFormationLaw d p.1) : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.2 (primeFormationLaw_pos hd p.1)).ne'
  have h : gammaCoherentVector k (primeClock_pos p.1) =
      ((Real.sqrt (primeFormationLaw d p.1) : ℝ) : ℂ)⁻¹ • primeCoherentFrame k d p.1 := by
    rw [primeCoherentFrame, smul_smul, inv_mul_cancel₀ hμ, one_smul]
  change gammaCoherentVector k (primeClock_pos p.1) ∈
    Submodule.span ℂ (Set.range (primeCoherentFrame k d))
  rw [h]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨p.1, rfl⟩)

/-- **(PPTI.32)–(PPTI.34), frame part.**  The left Gram `B_d^{(k)} = W_d^{(k)} W_d^{(k)*}` is
positive, Schatten-one of trace one, injective and has dense range. -/
theorem primeFormationLeftGram_properties (k : ℕ) [NeZero k] {d : ℝ} (hd : 0 < d) :
    (primeCoherentSynthesis k hd ∘L
        ContinuousLinearMap.adjoint (primeCoherentSynthesis k hd)).IsPositive ∧
      MemSchattenClass 1 (primeCoherentSynthesis k hd ∘L
        ContinuousLinearMap.adjoint (primeCoherentSynthesis k hd)) ∧
      (primeCoherentSynthesis k hd ∘L
        ContinuousLinearMap.adjoint (primeCoherentSynthesis k hd)).opTrace = 1 ∧
      Function.Injective (primeCoherentSynthesis k hd ∘L
        ContinuousLinearMap.adjoint (primeCoherentSynthesis k hd)) ∧
      DenseRange (primeCoherentSynthesis k hd ∘L
        ContinuousLinearMap.adjoint (primeCoherentSynthesis k hd)) := by
  have hL := leftGram_traceClass (summable_norm_sq_primeCoherentFrame k hd)
  have hD := leftGram_injective_denseRange (summable_norm_sq_primeCoherentFrame k hd)
    (primeCoherentFrame_total k hd)
  rw [tsum_norm_sq_primeCoherentFrame k hd, Complex.ofReal_one] at hL
  exact ⟨hL.1, hL.2.1, hL.2.2, hD.1, hD.2⟩

end GaloisForLFunctions.HTGeometry
