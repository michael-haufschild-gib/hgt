import GaloisForLFunctions.RHTower.ThetaPowerFejerTransfer
import GaloisForLFunctions.RHTower.PerturbationZero
import GaloisForLFunctions.RHTower.LogIndependence

/-!
# Off-line zeros of the theta-power family at transcendental parameters

For `0 < a < 1/2` with `a` transcendental, the completed function `Λ_a` (`thetaPowerXiC a`) of
`F_a = θ₃ h^{a/4}` has a zero `w` with `0 < Im w < 1/2`, i.e. a zero in the open critical strip off the
critical line.

With `α = a/4` and `D(z) = π^z M(z)/Γ(z) = Σ b_n (n+α)^{-z}`, a zero of `D` at `Re z > 1/4` is a zero of `Λ_a`
at `w = i(2z - 1/2)`, `Im w = 2 Re z - 1/2`.  Since `Σ |b_n| (n+α)^{-1/4} = ∞`, some `σ₀ ∈ (1/4, 3/8)` carries
polygon mass `Σ_{n<N} |β_n(σ₀)| ≥ 12B + 12`, and the target construction gives unit phases `u_n` and a
function `f` with an isolated zero at `σ₀`, uniformly approximated by `Σ_{n<N} u_n β_n` along a sequence of
`N → ∞`.  The logarithms `log(n+α)` are linearly independent over `ℚ` (transcendence of `α`), so the Fejér
transfer puts a translate `D(· + it)` within `min_{|z-σ₀|=r} |f| / 3` of `f` on the disc, and sphere
domination moves the zero of `f` to a zero of `D(· + it)` with real part in `(1/4, 1/2)`.
-/

open Complex Real Filter Topology Set Metric

namespace RHTower

noncomputable section

variable {a : ℝ}

/-- For transcendental `a > 0`, the frequencies `-log(n + a/4)` are independent over `ℤ`. -/
theorem thetaPowerLogFreq_independent (ha0 : 0 < a) (htr : Transcendental ℚ a) (M : ℕ)
    (m : Fin M → ℤ) (h : ∑ i, (m i : ℝ) * thetaPowerLogFreq a i = 0) : m = 0 := by
  classical
  have hα : Transcendental ℚ (a / 4) := by
    intro hal
    apply htr
    have h4 : IsAlgebraic ℚ ((4 : ℤ) : ℝ) := isAlgebraic_int 4
    have e : a = ((4 : ℤ) : ℝ) * (a / 4) := by push_cast; ring
    rw [e]
    exact h4.mul hal
  set ε : ℕ → ℤ := fun n => if hn : n < M then m ⟨n, hn⟩ else 0 with hε
  have hrel : ∑ n ∈ Finset.range M, (ε n : ℝ) * Real.log ((n : ℝ) + a / 4) = 0 := by
    rw [← Fin.sum_univ_eq_sum_range (fun n => (ε n : ℝ) * Real.log ((n : ℝ) + a / 4)) M]
    have : ∑ i : Fin M, (ε i : ℝ) * Real.log ((i : ℝ) + a / 4) =
        -∑ i, (m i : ℝ) * thetaPowerLogFreq a i := by
      rw [← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      simp only [hε, dif_pos i.isLt, Fin.eta, thetaPowerLogFreq]
      ring
    rw [this, h, neg_zero]
  have hall := log_shifts_independent (by positivity) hα (Finset.range M) ε hrel
  funext i
  have := hall i (Finset.mem_range.2 i.isLt)
  simpa [hε, dif_pos i.isLt] using this

/-- The circle mass of `β_n` on `|z - σ₀| = R₂` is at most
`2π |b_n|² ((n+α)^{-2(σ₀-R₂)} + (n+α)^{-2(σ₀+R₂)})`. -/
theorem termMass_thetaPower_le (ha0 : 0 < a) {σ₀ R₂ : ℝ} (hR₂ : 0 ≤ R₂) (n : ℕ) :
    termMass (a / 4) (thetaPowerCoeff a) σ₀ R₂ n ≤
      2 * π * (‖thetaPowerCoeff a n‖ ^ 2 *
        (((n : ℝ) + a / 4) ^ (-(2 * (σ₀ - R₂))) + ((n : ℝ) + a / 4) ^ (-(2 * (σ₀ + R₂))))) := by
  have hα0 : 0 < a / 4 := by positivity
  unfold termMass GaloisForLFunctions.HTGeometry.circleMass shiftedTrace
  have hc : Continuous fun θ =>
      ‖shiftedTerm (a / 4) (thetaPowerCoeff a) n (circleMap (σ₀ : ℂ) R₂ θ)‖ ^ 2 :=
    ((differentiable_shiftedTerm hα0 _ n).continuous.comp (continuous_circleMap _ _)).norm.pow 2
  refine (intervalIntegral.integral_mono_on (g := fun _ => ‖thetaPowerCoeff a n‖ ^ 2 *
      (((n : ℝ) + a / 4) ^ (-(2 * (σ₀ - R₂))) + ((n : ℝ) + a / 4) ^ (-(2 * (σ₀ + R₂)))))
    (by positivity) (hc.intervalIntegrable _ _) intervalIntegrable_const fun θ _ => ?_).trans
    (le_of_eq ?_)
  · obtain ⟨h1, h2⟩ := re_mem_of_mem_closedBall (circleMap_mem_closedBall (σ₀ : ℂ) hR₂ θ)
    exact norm_shiftedTerm_sq_le hα0 (thetaPowerCoeff a) n h1 h2
  · rw [intervalIntegral.integral_const, smul_eq_mul, sub_zero]

/-- `|β_n(σ₀)| ≤ C_b α^{-1}` for `1/4 ≤ σ₀ ≤ 5/4`. -/
theorem norm_shiftedTerm_real_le (ha0 : 0 < a) (ha1 : a < 1 / 2) {σ₀ : ℝ} (h1 : 1 / 4 ≤ σ₀)
    (h2 : σ₀ ≤ 5 / 4) (n : ℕ) :
    ‖shiftedTerm (a / 4) (thetaPowerCoeff a) n (σ₀ : ℂ)‖ ≤
      thetaPowerCoeffConstant a * (a / 4) ^ (-1 : ℝ) := by
  have hα0 : 0 < a / 4 := by positivity
  have hpos : 0 < (n : ℝ) + a / 4 := by positivity
  have hCb : 0 ≤ thetaPowerCoeffConstant a :=
    (mul_pos (thetaPowerHeckeConstant_pos ha0 ha1) (Real.exp_pos _)).le
  unfold shiftedTerm
  rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hpos, Complex.neg_re, Complex.ofReal_re]
  calc ‖thetaPowerCoeff a n‖ * ((n : ℝ) + a / 4) ^ (-σ₀)
      ≤ thetaPowerCoeffConstant a * ((n : ℝ) + a / 4) ^ (1 / 4 : ℝ) * ((n : ℝ) + a / 4) ^ (-σ₀) :=
        mul_le_mul_of_nonneg_right (norm_thetaPowerCoeff_le ha0 ha1 n) (by positivity)
    _ = thetaPowerCoeffConstant a * ((n : ℝ) + a / 4) ^ (1 / 4 - σ₀) := by
        rw [mul_assoc, ← Real.rpow_add hpos]; ring_nf
    _ ≤ thetaPowerCoeffConstant a * (a / 4) ^ (1 / 4 - σ₀) := by
        refine mul_le_mul_of_nonneg_left ?_ hCb
        exact Real.rpow_le_rpow_of_nonpos hα0 (by linarith [n.cast_nonneg (α := ℝ)]) (by linarith)
    _ ≤ thetaPowerCoeffConstant a * (a / 4) ^ (-1 : ℝ) := by
        refine mul_le_mul_of_nonneg_left ?_ hCb
        exact Real.rpow_le_rpow_of_exponent_ge hα0 (by linarith) (by linarith)

/-- **Off-line zeros at transcendental parameters, at every height.** For `0 < a < 1/2` transcendental and
every `T₀`, `Λ_a` has a zero `w` with `0 < Im w < 1/2` and `Re w ≤ 2 - 2T₀`. -/
theorem exists_thetaPowerXiC_offline_zero_re_le (ha0 : 0 < a) (ha1 : a < 1 / 2)
    (htr : Transcendental ℚ a) (T₀ : ℝ) :
    ∃ w : ℂ, 0 < w.im ∧ w.im < 1 / 2 ∧ w.re ≤ 2 - 2 * T₀ ∧ thetaPowerXiC a w = 0 := by
  classical
  have hα0 : 0 < a / 4 := by positivity
  -- the polygon point `σ₀`
  obtain ⟨B, hB⟩ : ∃ B : ℝ, B = thetaPowerCoeffConstant a * (a / 4) ^ (-1 : ℝ) + 1 := ⟨_, rfl⟩
  have hB0 : 0 < B := by
    have hCb : 0 ≤ thetaPowerCoeffConstant a :=
      (mul_pos (thetaPowerHeckeConstant_pos ha0 ha1) (Real.exp_pos _)).le
    rw [hB]; positivity
  obtain ⟨σ₀, hσlo, hσhi, N₁, hN₁⟩ :=
    exists_sigma_partial_mass_ge ha0 ha1 (12 * B + 12) (show (0 : ℝ) < 1 / 8 by norm_num)
  obtain ⟨R₂, hR₂⟩ : ∃ R₂ : ℝ, R₂ = (σ₀ - 1 / 4) / 2 := ⟨_, rfl⟩
  obtain ⟨R, hR⟩ : ∃ R : ℝ, R = (σ₀ - 1 / 4) / 4 := ⟨_, rfl⟩
  have hR0 : 0 < R := by rw [hR]; linarith
  have hRR₂ : R < R₂ := by rw [hR, hR₂]; linarith
  have hratio : R₂ / (R₂ - R) = 2 := by
    rw [hR, hR₂, div_eq_iff (by linarith)]; ring
  -- square summability of the circle masses
  have hQ : Summable (termMass (a / 4) (thetaPowerCoeff a) σ₀ R₂) := by
    refine Summable.of_nonneg_of_le (fun n => termMass_nonneg n)
      (fun n => termMass_thetaPower_le ha0 (by linarith) n) ?_
    refine (((summable_thetaPowerCoeff_sq_rpow ha0 ha1 (u := 2 * (σ₀ - R₂)) (by rw [hR₂]; linarith)).add
      (summable_thetaPowerCoeff_sq_rpow ha0 ha1 (u := 2 * (σ₀ + R₂)) (by rw [hR₂]; linarith))).mul_left
        (2 * π)).congr fun n => ?_
    ring
  -- the truncation point `N₀`
  obtain ⟨N₂, hN₂⟩ := eventually_atTop.1
    ((tendsto_tailMass (α := a / 4) (b := thetaPowerCoeff a) (c₀ := σ₀) (R₂ := R₂)).eventually
      (ge_mem_nhds (show (0 : ℝ) < 1 by norm_num)))
  obtain ⟨N₀, hN₀⟩ : ∃ N₀ : ℕ, N₀ = max N₁ N₂ := ⟨_, rfl⟩
  have h₀ : tailMass (a / 4) (thetaPowerCoeff a) σ₀ R₂ N₀ ≤ 1 := hN₂ N₀ (by rw [hN₀]; exact le_max_right _ _)
  have hbound : ∀ n < N₀, ‖shiftedTerm (a / 4) (thetaPowerCoeff a) n (σ₀ : ℂ)‖ ≤ B := fun n _ => by
    rw [hB]
    linarith [norm_shiftedTerm_real_le ha0 ha1 (σ₀ := σ₀) hσlo.le (by linarith) n]
  have hmass : 12 * B + 6 * (R₂ / (R₂ - R)) ≤
      ∑ n ∈ Finset.range N₀, ‖shiftedTerm (a / 4) (thetaPowerCoeff a) n (σ₀ : ℂ)‖ := by
    rw [hratio]
    refine le_trans (by linarith) (hN₁.trans ?_)
    have heq : ∀ n : ℕ, ‖shiftedTerm (a / 4) (thetaPowerCoeff a) n (σ₀ : ℂ)‖ =
        ‖thetaPowerCoeff a n‖ * ((n : ℝ) + a / 4) ^ (-σ₀) := by
      intro n
      have hpos : 0 < (n : ℝ) + a / 4 := by positivity
      unfold shiftedTerm
      rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hpos, Complex.neg_re, Complex.ofReal_re]
    simp_rw [heq]
    exact Finset.sum_le_sum_of_subset_of_nonneg
      (Finset.range_subset_range.2 (by rw [hN₀]; exact le_max_left _ _)) fun n _ _ => by positivity
  -- the target
  obtain ⟨u, f, r, hu, hf, hf0, hr0, hrR, hsph, happ⟩ :=
    exists_shifted_target hα0 (thetaPowerCoeff a) σ₀ hR0 hRR₂ hQ h₀ hB0 hbound hmass
  have happrox : ∀ ε > 0, ∀ N₁' : ℕ, ∃ N ≥ N₁', ∀ z ∈ closedBall (σ₀ : ℂ) R,
      ‖f z - ∑ n ∈ Finset.range N, u n * shiftedTerm (a / 4) (thetaPowerCoeff a) n z‖ ≤ ε := by
    intro ε hε N₁'
    obtain ⟨k₀, hk₀⟩ := exists_pow_lt_of_lt_one (show 0 < ε / 4 by positivity)
      (show (1 / 2 : ℝ) < 1 by norm_num)
    refine ⟨sched (a / 4) (thetaPowerCoeff a) σ₀ R₂ N₀ (max k₀ N₁'), ?_, fun z hz => ?_⟩
    · exact (le_max_right k₀ N₁').trans ((sched_strictMono N₀).id_le _)
    · refine (happ (max k₀ N₁') z hz).trans ?_
      rw [hratio]
      have := pow_le_pow_of_le_one (show (0 : ℝ) ≤ 1 / 2 by norm_num) (show (1 / 2 : ℝ) ≤ 1 by norm_num)
        (le_max_left k₀ N₁')
      linarith
  -- the minimum of `|f|` on the small sphere
  have hsphere_sub : sphere (σ₀ : ℂ) r ⊆ ball (σ₀ : ℂ) R :=
    sphere_subset_closedBall.trans (closedBall_subset_ball hrR)
  obtain ⟨z₀, hz₀, hmin⟩ := (isCompact_sphere (σ₀ : ℂ) r).exists_isMinOn
    (NormedSpace.sphere_nonempty.2 hr0.le) ((hf.continuousOn.mono hsphere_sub).norm)
  have hm0 : 0 < ‖f z₀‖ := norm_pos_iff.2 (hsph z₀ hz₀)
  -- transfer
  have hlo : 1 / 4 < σ₀ - R := by rw [hR]; linarith
  have hhi : σ₀ + R ≤ 1 := by rw [hR]; linarith
  obtain ⟨t, htT, ht⟩ := exists_shift_near_target ha0 ha1 (thetaPowerLogFreq_independent ha0 htr) hr0
    hrR hlo hhi hf hu happrox (show 0 < ‖f z₀‖ / 3 by positivity) T₀
  -- a zero of the translate in the closed disc
  have hzero : ∃ z ∈ closedBall (σ₀ : ℂ) r, thetaPowerDirichlet a (z + t * I) = 0 := by
    by_cases hc : thetaPowerDirichlet a ((σ₀ : ℂ) + t * I) = 0
    · exact ⟨σ₀, mem_closedBall_self hr0.le, hc⟩
    have hDd : Differentiable ℂ fun z : ℂ => thetaPowerDirichlet a (z + t * I) :=
      (differentiable_thetaPowerDirichlet ha0).comp (differentiable_id.add_const _)
    have hfcl : DiffContOnCl ℂ f (ball (σ₀ : ℂ) r) := hf.diffContOnCl_ball (closedBall_subset_ball hrR)
    obtain ⟨z, hz, hsum⟩ := exists_zero_of_sphere_domination
      (g := fun z => thetaPowerDirichlet a (z + t * I) - f z) (h := f) hr0
      (hDd.diffContOnCl.sub hfcl) hfcl hf0 (by simpa [hf0] using hc) (fun z hz => by
        have h1 := ht z (sphere_subset_closedBall hz)
        have h2 := hmin hz
        simp only [mem_setOf_eq] at h2
        linarith)
    exact ⟨z, hz, by simpa using hsum⟩
  obtain ⟨z, hz, hDz⟩ := hzero
  obtain ⟨h1, h2⟩ := re_mem_of_mem_closedBall hz
  have him := abs_im_le_of_mem_closedBall hz
  have hre : (z + t * I).re = z.re := by simp
  have hRle : R ≤ 1 := by rw [hR]; linarith
  refine ⟨I * (2 * (z + t * I) - 1 / 2), ?_, ?_, ?_,
    thetaPowerXiC_eq_zero_of_dirichlet (by rw [hre]; linarith) hDz⟩
  · rw [im_I_mul_two_mul_sub, hre]; linarith
  · rw [im_I_mul_two_mul_sub, hre]; rw [hR] at hrR; linarith
  · have hwre : (I * (2 * (z + t * I) - 1 / 2)).re = -2 * z.im - 2 * t := by simp; ring
    rw [hwre]
    linarith [(abs_le.mp him).1]

/-- **Off-line zeros at transcendental parameters.** For `0 < a < 1/2` transcendental, `Λ_a` has a zero `w`
with `0 < Im w < 1/2`. -/
theorem thetaPowerXiC_offline_zero_of_transcendental (ha0 : 0 < a) (ha1 : a < 1 / 2)
    (htr : Transcendental ℚ a) : ∃ w : ℂ, 0 < w.im ∧ w.im < 1 / 2 ∧ thetaPowerXiC a w = 0 := by
  obtain ⟨w, h1, h2, -, h3⟩ := exists_thetaPowerXiC_offline_zero_re_le ha0 ha1 htr 0
  exact ⟨w, h1, h2, h3⟩

/-- **Infinitely many off-line zeros.** For `0 < a < 1/2` transcendental, `Λ_a` has infinitely many zeros with
`0 < Im w < 1/2`. -/
theorem thetaPowerXiC_offline_zeros_infinite_of_transcendental (ha0 : 0 < a) (ha1 : a < 1 / 2)
    (htr : Transcendental ℚ a) :
    {w : ℂ | 0 < w.im ∧ w.im < 1 / 2 ∧ thetaPowerXiC a w = 0}.Infinite := by
  intro hfin
  obtain ⟨m, hm⟩ := (hfin.image Complex.re).bddBelow
  obtain ⟨w, h1, h2, h3, h4⟩ := exists_thetaPowerXiC_offline_zero_re_le ha0 ha1 htr ((2 - m) / 2 + 1)
  have := hm (Set.mem_image_of_mem Complex.re ⟨h1, h2, h4⟩)
  linarith

end

end RHTower
