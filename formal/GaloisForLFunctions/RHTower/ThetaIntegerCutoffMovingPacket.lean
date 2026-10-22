import GaloisForLFunctions.RHTower.ThetaCriticalBoundaryFluxPotential
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspSeedZeroMean
import GaloisForLFunctions.HTGeometry.ReflectionIntegral

/-!
# The escaping packet of integer theta cutoffs

The integer cutoff `K_N = Σ_{n ≤ N} a_n` has critical moment zero and converges to the completed
source `k` uniformly on compact logarithmic intervals.  In the moving frame `x = y − log N` its
critical density is the dilated Riemann sum

`B_N(y) = e^{(y − log N)/2} K_N(y − log N) = (e^y/N) Σ_{n=1}^N h((n/N) e^y)`

of the theta-cusp seed `h = −2π (t³ e^{−πt²})'`.  A first-order quadrature estimate for Lipschitz
profiles gives `B_N → B_∞(y) = ∫_0^{e^y} h = −2π e^{3y} e^{−π e^{2y}} < 0` uniformly on every
half-line `y ≤ Y`, and `∫ B_∞ = −2π ∫_0^∞ t² e^{−πt²} dt = −1/2`.  Since every `B_N` has total
mass zero, `∫ |B_N − B_∞| ≥ 1/2`: the limit is local only.

The moving flux potential `H_{1..N}(y − log N)` converges in the same way to
`2π ∫_0^{e^y} t² e^{−πt²} dt`, which rises monotonically from `0` at the cusp to `1/2`.
-/

open MeasureTheory Set Filter Topology

namespace RHTower

noncomputable section

/-! ## Dilated Riemann sums -/

/-- Right-endpoint Riemann sums of a `K`-Lipschitz function on `[0, T]` with mesh `h`, `Nh ≤ T`,
have error at most `K N h²`. -/
theorem abs_riemannSum_sub_integral_le {f : ℝ → ℝ} {K : NNReal} {T : ℝ}
    (hf : LipschitzOnWith K f (Icc 0 T)) (hc : ContinuousOn f (Icc 0 T)) (N : ℕ) {h : ℝ}
    (hh : 0 ≤ h) (hNT : N * h ≤ T) :
    |h * ∑ i ∈ Finset.range N, f ((i + 1) * h) - ∫ t in (0 : ℝ)..N * h, f t| ≤ K * N * h ^ 2 := by
  have hcell : ∀ i ∈ Finset.range N, Icc ((i : ℝ) * h) ((i + 1) * h) ⊆ Icc 0 T := by
    intro i hi t ht
    have hi' : (i : ℝ) + 1 ≤ N := by exact_mod_cast Finset.mem_range.1 hi
    exact ⟨le_trans (by positivity) ht.1, ht.2.trans (le_trans (by nlinarith) hNT)⟩
  have hint : ∀ i ∈ Finset.range N,
      IntervalIntegrable f volume ((i : ℝ) * h) ((i + 1 : ℕ) * h) := fun i hi => by
    refine (hc.mono ?_).intervalIntegrable
    rw [uIcc_of_le (by push_cast; nlinarith)]
    push_cast
    exact hcell i hi
  have hsum := intervalIntegral.sum_integral_adjacent_intervals (f := f) (μ := volume)
    (a := fun i : ℕ => (i : ℝ) * h) (n := N) (fun i hi => hint i (Finset.mem_range.2 hi))
  simp only [Nat.cast_zero, zero_mul] at hsum
  rw [← hsum, Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  have hbound : ∀ i ∈ Finset.range N, |h * f ((i + 1) * h) -
      ∫ t in (i : ℝ) * h..((i + 1 : ℕ) : ℝ) * h, f t| ≤ K * h ^ 2 := by
    intro i hi
    have heq : h * f ((i + 1) * h) - ∫ t in (i : ℝ) * h..((i + 1 : ℕ) : ℝ) * h, f t =
        ∫ t in (i : ℝ) * h..((i + 1 : ℕ) : ℝ) * h, (f ((i + 1) * h) - f t) := by
      rw [intervalIntegral.integral_sub intervalIntegrable_const (hint i hi),
        intervalIntegral.integral_const, smul_eq_mul]
      push_cast; ring
    rw [heq]
    have hle := intervalIntegral.norm_integral_le_of_norm_le_const
      (a := (i : ℝ) * h) (b := ((i + 1 : ℕ) : ℝ) * h) (C := K * h)
      (f := fun t => f ((i + 1) * h) - f t) (fun t ht => by
        rw [uIoc_of_le (by push_cast; nlinarith)] at ht
        have ht' : t ∈ Icc ((i : ℝ) * h) ((i + 1) * h) := by
          push_cast at ht; exact ⟨ht.1.le, ht.2⟩
        have hd := hf.dist_le_mul ((i + 1) * h) (hcell i hi ⟨by nlinarith, le_rfl⟩) t
          (hcell i hi ht')
        have habs : |((i : ℝ) + 1) * h - t| = ((i : ℝ) + 1) * h - t :=
          abs_of_nonneg (by linarith [ht'.2])
        rw [Real.dist_eq, Real.dist_eq, habs] at hd
        rw [Real.norm_eq_abs]
        refine hd.trans ?_
        exact mul_le_mul_of_nonneg_left (by linarith [ht'.1]) K.2)
    rw [Real.norm_eq_abs] at hle
    refine hle.trans (le_of_eq ?_)
    rw [show ((i + 1 : ℕ) : ℝ) * h - i * h = h by push_cast; ring, abs_of_nonneg hh]
    ring
  refine (Finset.sum_le_sum hbound).trans (le_of_eq ?_)
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  ring

/-- **Dilated Riemann sums.**  For a `C¹` profile `f`,
`(e^y/N) Σ_{i<N} f((i+1)e^y/N) → ∫_0^{e^y} f` uniformly on every half-line `y ≤ Y`. -/
theorem tendstoUniformlyOn_dilatedRiemannSum {f : ℝ → ℝ} (hf : ContDiff ℝ 1 f) (Y : ℝ) :
    TendstoUniformlyOn (fun (N : ℕ) (y : ℝ) =>
        Real.exp y / N * ∑ i ∈ Finset.range N, f ((i + 1) / N * Real.exp y))
      (fun y => ∫ t in (0 : ℝ)..Real.exp y, f t) atTop (Iic Y) := by
  set T := Real.exp Y
  obtain ⟨K, hK⟩ := (hf.contDiffOn (s := Icc 0 T)).exists_lipschitzOnWith one_ne_zero
    (convex_Icc 0 T) isCompact_Icc
  have hc : ContinuousOn f (Icc 0 T) := hf.continuous.continuousOn
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  have hlim : Tendsto (fun N : ℕ => (K : ℝ) * T ^ 2 / N) atTop (𝓝 0) :=
    tendsto_const_div_atTop_nhds_zero_nat _
  filter_upwards [hlim.eventually (gt_mem_nhds hε), eventually_ge_atTop 1] with N hN hN1 y hy
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN1
  set h := Real.exp y / N
  have hh : 0 ≤ h := div_nonneg (Real.exp_pos y).le hNpos.le
  have hNh : (N : ℝ) * h = Real.exp y := by simp only [h]; field_simp
  have hyT : Real.exp y ≤ T := Real.exp_le_exp.2 hy
  have hmain := abs_riemannSum_sub_integral_le hK hc N hh (by rw [hNh]; exact hyT)
  rw [hNh] at hmain
  have hsum : Real.exp y / N * ∑ i ∈ Finset.range N, f ((i + 1) / N * Real.exp y) =
      h * ∑ i ∈ Finset.range N, f ((i + 1) * h) := by
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [h]; ring_nf
  rw [Real.dist_eq, hsum, abs_sub_comm]
  refine lt_of_le_of_lt (hmain.trans ?_) hN
  have hKT : (K : ℝ) * N * h ^ 2 = K * Real.exp y ^ 2 / N := by
    simp only [h]; field_simp
  rw [hKT]
  have hy2 : Real.exp y ^ 2 ≤ T ^ 2 := pow_le_pow_left₀ (Real.exp_pos y).le hyT 2
  gcongr

/-! ## Integer cutoffs -/

theorem sum_Icc_one_eq_sum_range_succ {M : Type*} [AddCommMonoid M] (f : ℕ → M) (N : ℕ) :
    ∑ n ∈ Finset.Icc 1 N, f n = ∑ i ∈ Finset.range N, f (i + 1) := by
  rw [Finset.range_eq_Ico, Finset.sum_Ico_add' f 0 N 1]
  rfl

theorem integerCutoffThetaSource_eq_sum_range (N : ℕ) (x : ℝ) :
    integerCutoffThetaSource N x = ∑ i ∈ Finset.range N, thetaCuspSourceTerm x (i + 1) := by
  rw [integerCutoffThetaSource, sum_Icc_one_eq_sum_range_succ]

theorem integerCutoffThetaSource_eq_indexThetaSource (N : ℕ) :
    integerCutoffThetaSource N = indexThetaSource (Finset.Icc 1 N : Set ℕ) := by
  funext x
  rw [integerCutoffThetaSource, indexThetaSource]
  exact (Finset.tsum_subtype (Finset.Icc 1 N) (fun n => thetaCuspSourceTerm x n)).symm

/-- Every integer cutoff has absolutely defined critical moment zero. -/
theorem integral_exp_half_mul_integerCutoffThetaSource (N : ℕ) :
    Integrable (fun x : ℝ => Real.exp ((1 / 2 : ℝ) * x) * integerCutoffThetaSource N x) ∧
    (∫ x : ℝ, Real.exp ((1 / 2 : ℝ) * x) * integerCutoffThetaSource N x) = 0 := by
  rw [integerCutoffThetaSource_eq_indexThetaSource]
  exact integral_exp_half_mul_indexThetaSource
    ((Finset.Icc 1 N).summable (fun n : ℕ => ((n : ℕ) : ℝ)⁻¹))

/-- The physical packet: `K_N → k` uniformly on every compact logarithmic interval. -/
theorem tendstoUniformlyOn_integerCutoffThetaSource (R : ℝ) :
    TendstoUniformlyOn integerCutoffThetaSource thetaCuspFullSource atTop (Icc (-R) R) := by
  have h := tendstoUniformlyOn_tsum_nat (f := fun n x => thetaCuspSourceTerm x n)
    (summable_thetaCuspSourceMajorant R) (s := Icc (-R) R)
    (fun n x hx => abs_thetaCuspSourceTerm_le_majorant hx n)
  rw [Metric.tendstoUniformlyOn_iff] at h ⊢
  intro ε hε
  filter_upwards [(tendsto_add_atTop_nat 1).eventually (h ε hε)] with N hN x hx
  have heq : integerCutoffThetaSource N x = ∑ n ∈ Finset.range (N + 1), thetaCuspSourceTerm x n := by
    rw [Finset.sum_range_succ', thetaCuspSourceTerm_zero, add_zero,
      integerCutoffThetaSource_eq_sum_range]
  rw [heq]
  exact hN x hx

/-! ## The escaping packet in the moving frame -/

/-- The moving-frame critical density `B_N(y) = e^{(y − log N)/2} K_N(y − log N)`. -/
def movingPacketDensity (N : ℕ) (y : ℝ) : ℝ :=
  Real.exp ((1 / 2 : ℝ) * (y - Real.log N)) * integerCutoffThetaSource N (y - Real.log N)

theorem exp_sub_log_natCast {N : ℕ} (hN : 0 < N) (y : ℝ) :
    Real.exp (y - Real.log N) = Real.exp y / N := by
  rw [Real.exp_sub, Real.exp_log (by exact_mod_cast hN)]

/-- `B_N(y) = (e^y/N) Σ_{n=1}^N h((n/N) e^y)` for the theta-cusp seed `h`. -/
theorem movingPacketDensity_eq {N : ℕ} (hN : 0 < N) (y : ℝ) :
    movingPacketDensity N y =
      Real.exp y / N * ∑ i ∈ Finset.range N, thetaCuspSeed ((i + 1) / N * Real.exp y) := by
  rw [movingPacketDensity, integerCutoffThetaSource_eq_sum_range, Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hsq : Real.exp ((1 / 2 : ℝ) * (y - Real.log N)) * Real.exp ((y - Real.log N) / 2) =
      Real.exp y / N := by
    rw [← Real.exp_add, show (1 / 2 : ℝ) * (y - Real.log N) + (y - Real.log N) / 2 =
      y - Real.log N by ring, exp_sub_log_natCast hN]
  rw [thetaCuspSourceTerm, ← mul_assoc, hsq, exp_sub_log_natCast hN]
  congr 2
  push_cast
  ring

/-- The limit packet `B_∞(y) = −2π e^{3y} e^{−π e^{2y}}`. -/
def movingPacketLimit (y : ℝ) : ℝ :=
  -(2 * Real.pi) * Real.exp (3 * y) * Real.exp (-(Real.pi * Real.exp (2 * y)))

theorem movingPacketLimit_neg (y : ℝ) : movingPacketLimit y < 0 := by
  unfold movingPacketLimit
  have := Real.pi_pos
  have h1 := Real.exp_pos (3 * y)
  have h2 := Real.exp_pos (-(Real.pi * Real.exp (2 * y)))
  have : 0 < 2 * Real.pi * Real.exp (3 * y) * Real.exp (-(Real.pi * Real.exp (2 * y))) := by
    positivity
  linarith

/-- `h(t) = −2π d/dt [t³ e^{−πt²}]`. -/
theorem hasDerivAt_thetaCuspSeed_primitive (t : ℝ) :
    HasDerivAt (fun t : ℝ => -(2 * Real.pi) * (t ^ 3 * Real.exp (-Real.pi * t ^ 2)))
      (thetaCuspSeed t) t := by
  have h := (((hasDerivAt_pow 3 t).mul ((((hasDerivAt_pow 2 t).const_mul (-Real.pi))).exp)).const_mul
    (-(2 * Real.pi)))
  refine h.congr_deriv ?_
  simp only [thetaCuspSeed, Nat.cast_ofNat]
  ring

theorem continuous_thetaCuspSeed : Continuous thetaCuspSeed := by
  unfold thetaCuspSeed; fun_prop

theorem contDiff_thetaCuspSeed : ContDiff ℝ 1 thetaCuspSeed := by
  unfold thetaCuspSeed; fun_prop

theorem integral_thetaCuspSeed_zero_to (T : ℝ) :
    (∫ t in (0 : ℝ)..T, thetaCuspSeed t) = -(2 * Real.pi) * (T ^ 3 * Real.exp (-Real.pi * T ^ 2)) := by
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hasDerivAt_thetaCuspSeed_primitive t)
    (continuous_thetaCuspSeed.intervalIntegrable _ _)]
  simp

/-- `B_∞(y) = ∫_0^{e^y} h(t) dt`. -/
theorem movingPacketLimit_eq_integral (y : ℝ) :
    movingPacketLimit y = ∫ t in (0 : ℝ)..Real.exp y, thetaCuspSeed t := by
  rw [integral_thetaCuspSeed_zero_to, movingPacketLimit]
  have h3 : Real.exp y ^ 3 = Real.exp (3 * y) := by rw [← Real.exp_nat_mul]; norm_num
  have h2 : Real.exp y ^ 2 = Real.exp (2 * y) := by rw [← Real.exp_nat_mul]; norm_num
  rw [h3, h2, show -Real.pi * Real.exp (2 * y) = -(Real.pi * Real.exp (2 * y)) by ring]
  ring

/-- **(10) Moving-frame limit.**  `B_N → B_∞` uniformly on every half-line `y ≤ Y`. -/
theorem tendstoUniformlyOn_movingPacketDensity (Y : ℝ) :
    TendstoUniformlyOn movingPacketDensity movingPacketLimit atTop (Iic Y) := by
  refine ((tendstoUniformlyOn_dilatedRiemannSum contDiff_thetaCuspSeed Y).congr ?_).congr_right
    fun y _ => (movingPacketLimit_eq_integral y).symm
  filter_upwards [eventually_ge_atTop 1] with N hN y _
  exact (movingPacketDensity_eq hN y).symm

theorem movingPacketLimit_eq_exp_mul (y : ℝ) :
    movingPacketLimit y = Real.exp y *
      (-(2 * Real.pi) * (Real.exp y ^ 2 * Real.exp (-Real.pi * Real.exp y ^ 2))) := by
  have h3 : Real.exp (3 * y) = Real.exp y * Real.exp y ^ 2 := by
    rw [← pow_succ', ← Real.exp_nat_mul]; norm_num
  have h2 : Real.exp y ^ 2 = Real.exp (2 * y) := by rw [← Real.exp_nat_mul]; norm_num
  rw [movingPacketLimit, h3, h2, show -Real.pi * Real.exp (2 * y) = -(Real.pi * Real.exp (2 * y)) by
    ring]
  ring

theorem integrable_movingPacketLimit : Integrable movingPacketLimit := by
  have hg : IntegrableOn (fun t : ℝ => -(2 * Real.pi) * (t ^ 2 * Real.exp (-Real.pi * t ^ 2)))
      (Ioi 0) := (integrableOn_pow_mul_exp_neg_pi_sq 2).const_mul _
  have hg' : IntegrableOn
      (fun t : ℝ => ((-(2 * Real.pi) * (t ^ 2 * Real.exp (-Real.pi * t ^ 2)) : ℝ) : ℂ)) (Ioi 0) :=
    hg.ofReal
  have h := (integrableOn_Ioi_iff_comp_exp_complex
    (fun t : ℝ => ((-(2 * Real.pi) * (t ^ 2 * Real.exp (-Real.pi * t ^ 2)) : ℝ) : ℂ))).1 hg'
  refine h.re.congr (ae_of_all _ fun y => ?_)
  simp only [RCLike.re_to_complex]
  rw [← Complex.ofReal_mul, Complex.ofReal_re, movingPacketLimit_eq_exp_mul]

/-- **(11) The escaping packet carries mass `−1/2`.** -/
theorem integral_movingPacketLimit : (∫ y : ℝ, movingPacketLimit y) = -(1 / 2) := by
  have h := GaloisForLFunctions.HTGeometry.integral_Ioi_comp_exp
    (fun t : ℝ => -(2 * Real.pi) * (t ^ 2 * Real.exp (-Real.pi * t ^ 2)))
  rw [integral_const_mul, integral_sq_mul_exp_neg_pi_sq] at h
  have hpi := Real.pi_pos.ne'
  rw [show (∫ y : ℝ, movingPacketLimit y) = ∫ t : ℝ, Real.exp t *
      (-(2 * Real.pi) * (Real.exp t ^ 2 * Real.exp (-Real.pi * Real.exp t ^ 2))) from
    integral_congr_ae (ae_of_all _ movingPacketLimit_eq_exp_mul), ← h]
  field_simp
  ring

/-- Every moving-frame density has total mass zero. -/
theorem integral_movingPacketDensity (N : ℕ) :
    Integrable (movingPacketDensity N) ∧ (∫ y : ℝ, movingPacketDensity N y) = 0 := by
  obtain ⟨hi, h0⟩ := integral_exp_half_mul_integerCutoffThetaSource N
  refine ⟨hi.comp_sub_right (Real.log N), ?_⟩
  rw [← h0]
  exact integral_sub_right_eq_self
    (fun x : ℝ => Real.exp ((1 / 2 : ℝ) * x) * integerCutoffThetaSource N x) (Real.log N)

/-- The moving-frame limit is local only: `∫ |B_N − B_∞| ≥ 1/2` for every `N`. -/
theorem half_le_integral_abs_movingPacketDensity_sub (N : ℕ) :
    1 / 2 ≤ ∫ y : ℝ, |movingPacketDensity N y - movingPacketLimit y| := by
  obtain ⟨hi, h0⟩ := integral_movingPacketDensity N
  have hsub := integral_sub hi integrable_movingPacketLimit
  rw [h0, integral_movingPacketLimit] at hsub
  have hn := norm_integral_le_integral_norm (μ := (volume : Measure ℝ))
    (fun y => movingPacketDensity N y - movingPacketLimit y)
  rw [hsub] at hn
  simp only [Real.norm_eq_abs] at hn
  norm_num at hn
  linarith

theorem not_tendsto_integral_abs_movingPacketDensity_sub :
    ¬ Tendsto (fun N : ℕ => ∫ y : ℝ, |movingPacketDensity N y - movingPacketLimit y|) atTop
      (𝓝 0) := fun h => by
  have := ge_of_tendsto h (Eventually.of_forall half_le_integral_abs_movingPacketDensity_sub)
  norm_num at this

/-! ## The moving flux potential -/

/-- The integer-cutoff flux potential `H_{1..N}`. -/
def integerCutoffFluxPotential (N : ℕ) (x : ℝ) : ℝ :=
  ∑ n ∈ Finset.Icc 1 N, thetaFluxTerm x n

theorem integerCutoffFluxPotential_eq_indexFluxPotential (N : ℕ) :
    integerCutoffFluxPotential N = indexFluxPotential (Finset.Icc 1 N : Set ℕ) := by
  funext x
  rw [integerCutoffFluxPotential, indexFluxPotential]
  exact (Finset.tsum_subtype (Finset.Icc 1 N) (fun n => thetaFluxTerm x n)).symm

/-- The Gaussian mass profile `2π t² e^{−πt²}`. -/
def gaussianMassProfile (t : ℝ) : ℝ := 2 * Real.pi * (t ^ 2 * Real.exp (-Real.pi * t ^ 2))

theorem contDiff_gaussianMassProfile : ContDiff ℝ 1 gaussianMassProfile := by
  unfold gaussianMassProfile; fun_prop

/-- The moving wall profile `2π ∫_0^{e^y} t² e^{−πt²} dt`. -/
def movingFluxLimit (y : ℝ) : ℝ := ∫ t in (0 : ℝ)..Real.exp y, gaussianMassProfile t

theorem integerCutoffFluxPotential_moving_eq {N : ℕ} (hN : 0 < N) (y : ℝ) :
    integerCutoffFluxPotential N (y - Real.log N) =
      Real.exp y / N * ∑ i ∈ Finset.range N, gaussianMassProfile ((i + 1) / N * Real.exp y) := by
  rw [integerCutoffFluxPotential, sum_Icc_one_eq_sum_range_succ, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hNR : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  have h3 : Real.exp (3 * (y - Real.log N)) = (Real.exp y / N) ^ 3 := by
    rw [← exp_sub_log_natCast hN, ← Real.exp_nat_mul]; norm_num
  have h2 : Real.exp (2 * (y - Real.log N)) = (Real.exp y / N) ^ 2 := by
    rw [← exp_sub_log_natCast hN, ← Real.exp_nat_mul]; norm_num
  simp only [thetaFluxTerm, rateFlux, gaussianMassProfile, h3, h2]
  push_cast
  rw [show -(Real.pi * ((i : ℝ) + 1) ^ 2 * (Real.exp y / N) ^ 2) =
    -Real.pi * ((i + 1) / N * Real.exp y) ^ 2 by field_simp]
  field_simp

/-- **Moving flux potential.**  `H_{1..N}(y − log N) → 2π ∫_0^{e^y} t² e^{−πt²} dt` uniformly on
every half-line `y ≤ Y`. -/
theorem tendstoUniformlyOn_integerCutoffFluxPotential_moving (Y : ℝ) :
    TendstoUniformlyOn (fun (N : ℕ) (y : ℝ) => integerCutoffFluxPotential N (y - Real.log N))
      movingFluxLimit atTop (Iic Y) := by
  refine (tendstoUniformlyOn_dilatedRiemannSum contDiff_gaussianMassProfile Y).congr ?_
  filter_upwards [eventually_ge_atTop 1] with N hN y _
  exact (integerCutoffFluxPotential_moving_eq hN y).symm

theorem movingFluxLimit_monotone : Monotone movingFluxLimit := by
  intro a b hab
  have hc : Continuous gaussianMassProfile := contDiff_gaussianMassProfile.continuous
  exact intervalIntegral.integral_mono_interval le_rfl (Real.exp_pos a).le
    (Real.exp_le_exp.2 hab)
    (ae_of_all _ fun t => by unfold gaussianMassProfile; positivity) (hc.intervalIntegrable _ _)

/-- The moving wall rises from `0` at the cusp ... -/
theorem tendsto_movingFluxLimit_atBot : Tendsto movingFluxLimit atBot (𝓝 0) := by
  have hc := intervalIntegral.continuous_primitive (μ := volume)
    (fun a b => contDiff_gaussianMassProfile.continuous.intervalIntegrable a b) 0
  have h := (hc.tendsto 0).comp Real.tendsto_exp_atBot
  show Tendsto (fun y => ∫ t in (0 : ℝ)..Real.exp y, gaussianMassProfile t) atBot (𝓝 0)
  simpa [Function.comp_def] using h

/-- ... to `1/2` at the physical end. -/
theorem tendsto_movingFluxLimit_atTop : Tendsto movingFluxLimit atTop (𝓝 (1 / 2)) := by
  have hg : IntegrableOn gaussianMassProfile (Ioi 0) :=
    (integrableOn_pow_mul_exp_neg_pi_sq 2).const_mul _
  have h := intervalIntegral_tendsto_integral_Ioi 0 hg Real.tendsto_exp_atTop
  have hv : (∫ t in Ioi (0 : ℝ), gaussianMassProfile t) = 1 / 2 := by
    simp only [gaussianMassProfile]
    rw [integral_const_mul, integral_sq_mul_exp_neg_pi_sq]
    field_simp
    norm_num
  rw [hv] at h
  exact h

end

end RHTower
