import GaloisForLFunctions.RenormalizedIntersectionTheory.GaussMayerFredholmDeterminant
import Mathlib.Topology.Algebra.InfiniteSum.TsumUniformlyOn
import Mathlib.Analysis.Complex.SummableUniformlyOn
import Mathlib.Analysis.SpecialFunctions.Exponential

/-!
# Source-parameter holomorphy of the Gauss–Mayer family

Exponentiating bounded logarithmic multiplication realizes each actual Gauss
branch as an entire operator family. Normal convergence of its constant-mode
correction gives operator-norm holomorphy on the right half-plane and the exact
rank-one residue at one. Uniform geometric Cauchy bounds then prove holomorphy
of the actual Fredholm determinant in the source exponent away from this pole.
-/

open Complex Metric Set Filter Topology
open GaloisForLFunctions.HTGeometry
open GaloisForLFunctions.RenormalizedIntersectionTheory.MayerCutoff
open GaloisForLFunctions.RenormalizedIntersectionTheory.MayerNuclear
open GaloisForLFunctions.RenormalizedIntersectionTheory.MayerFredholm

noncomputable section
namespace GaloisForLFunctions.RenormalizedIntersectionTheory.MayerParameter

private theorem digit_slit {n : ℕ} (hn : 1 ≤ n) {z : ℂ} (hz : z ∈ outer) :
    (n : ℂ) + z ∈ Complex.slitPlane := by
  apply Complex.mem_slitPlane_iff.mpr
  apply Or.inl
  have hr := (neg_le_abs (z - 1).re).trans (Complex.abs_re_le_norm (z - 1))
  have hd : ‖z - 1‖ ≤ (3 / 2 : ℝ) := by simpa only [mem_closedBall, dist_eq_norm] using hz
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  simp only [Complex.sub_re, Complex.one_re] at hr
  simp only [Complex.add_re, Complex.natCast_re]
  linarith only [hr, hd, hn']

/-- A holomorphic representative defines an element of the actual disc algebra. -/
def ofHolomorphic (g : ℂ → ℂ) (hc : ContinuousOn g outer)
    (hd : DifferentiableOn ℂ g inner) : DiscSpace :=
  ⟨⟨fun z => g z, hc.restrict⟩, by
    change DifferentiableOn ℂ (holoExtend inner (fun z => g z.1)) inner
    exact hd.congr fun z hz => holoExtend_of_mem _ hz⟩

/-- Multiplication by a fixed holomorphic disc function. -/
def multiply (g : DiscSpace) : DiscSpace →L[ℂ] DiscSpace :=
  LinearMap.mkContinuous
    { toFun := fun f => ⟨g.1 * f.1, by
        change DifferentiableOn ℂ
          (holoExtend inner (fun z => g.1 ⟨z.1, ball_subset_closedBall z.2⟩ *
            f.1 ⟨z.1, ball_subset_closedBall z.2⟩)) inner
        apply ((differentiableOn_plane g).mul (differentiableOn_plane f)).congr
        intro z hz
        rw [holoExtend_of_mem _ hz]
        exact congrArg₂ (· * ·) (plane_eq g ⟨z, ball_subset_closedBall hz⟩).symm
          (plane_eq f ⟨z, ball_subset_closedBall hz⟩).symm⟩
      map_add' := fun f h => by apply Subtype.ext; ext z; exact mul_add _ _ _
      map_smul' := fun c f => by apply Subtype.ext; ext z; exact mul_left_comm _ _ _ }
    ‖g‖ (fun f => norm_mul_le g.1 f.1)

@[simp] theorem multiply_apply (g f : DiscSpace) (z : Disc) :
    (multiply g f).1 z = g.1 z * f.1 z := rfl

/-- The principal logarithm is holomorphic on every translated source disc. -/
def logDisc (n : ℕ) (hn : 1 ≤ n) : DiscSpace :=
  ofHolomorphic (fun z => Complex.log ((n : ℂ) + z))
    (fun z hz => ((Complex.differentiableAt_log (digit_slit hn hz)).comp z
      (differentiableAt_const (n : ℂ) |>.add differentiableAt_id)).continuousAt.continuousWithinAt)
    (fun z hz => ((Complex.differentiableAt_log (digit_slit hn (ball_subset_closedBall hz))).comp z
      (differentiableAt_const (n : ℂ) |>.add differentiableAt_id)).differentiableWithinAt)

/-- Evaluation on the disc is a bounded linear functional. -/
def evaluation (z : Disc) : DiscSpace →L[ℂ] ℂ :=
  (ContinuousMap.evalCLM ℂ z).comp discSubmodule.subtypeL

@[simp] theorem evaluation_apply (z : Disc) (f : DiscSpace) : evaluation z f = f.1 z := rfl

private theorem multiply_pow_apply (c : ℂ) (g f : DiscSpace) (z : Disc) (k : ℕ) :
    (((c • multiply g)^k) f).1 z = (c * g.1 z)^k * f.1 z := by
  induction k with
  | zero => simp only [pow_zero, one_mul]; rfl
  | succ k ih =>
    rw [pow_succ']
    change c * (g.1 z * (((c • multiply g)^k) f).1 z) = _
    rw [ih, pow_succ']
    ring

/-- The operator exponential of multiplication acts by the scalar exponential. -/
theorem exp_multiply_apply (c : ℂ) (g f : DiscSpace) (z : Disc) :
    ((NormedSpace.exp (c • multiply g)) f).1 z =
      Complex.exp (c * g.1 z) * f.1 z := by
  let ev : (DiscSpace →L[ℂ] DiscSpace) →L[ℂ] ℂ :=
    (evaluation z).comp (ContinuousLinearMap.apply ℂ DiscSpace f)
  have hop := ev.hasSum (NormedSpace.exp_series_hasSum_exp' (𝕂 := ℂ) (c • multiply g))
  have hscalar := (NormedSpace.exp_series_hasSum_exp' (𝕂 := ℂ) (c * g.1 z)).mul_right (f.1 z)
  rw [← Complex.exp_eq_exp_ℂ] at hscalar
  have he : (fun k : ℕ => ev ((k.factorial : ℂ)⁻¹ • (c • multiply g)^k)) =
      (fun k : ℕ => ((k.factorial : ℂ)⁻¹ * (c * g.1 z)^k) * f.1 z) := by
    funext k
    change (k.factorial : ℂ)⁻¹ * (((c • multiply g)^k) f).1 z = _
    rw [multiply_pow_apply, mul_assoc]
  rw [he] at hop
  exact hop.unique hscalar

/-- Entire extension of one genuine Gauss branch in its source exponent. -/
def entireBranch (w : ℂ) (n : ℕ) (hn : 1 ≤ n) : DiscSpace →L[ℂ] DiscSpace :=
  NormedSpace.exp ((1 - w) • multiply (logDisc n hn)) * branch 1 (by norm_num) n hn

theorem entireBranch_apply (w : ℂ) (n : ℕ) (hn : 1 ≤ n) (f : DiscSpace) (z : Disc) :
    (entireBranch w n hn f).1 z =
      ((n : ℂ) + z.1)^(-w) * plane f (((n : ℂ) + z.1)⁻¹) := by
  have ha : (n : ℂ) + z.1 ≠ 0 := by
    intro he
    have hs := Complex.mem_slitPlane_iff.mp (digit_slit hn z.2)
    simp only [he, Complex.zero_re, Complex.zero_im, lt_self_iff_false, ne_eq, not_true_eq_false, or_self] at hs
  change ((NormedSpace.exp ((1 - w) • multiply (logDisc n hn)))
    (branch 1 (by norm_num) n hn f)).1 z = _
  rw [exp_multiply_apply, branch_apply]
  change Complex.exp ((1 - w) * Complex.log ((n : ℂ) + z.1)) *
    (((n : ℂ) + z.1)^(-(1 : ℂ)) * plane f (((n : ℂ) + z.1)⁻¹)) = _
  rw [Complex.cpow_def_of_ne_zero ha, Complex.cpow_def_of_ne_zero ha,
    ← mul_assoc, ← Complex.exp_add]
  congr 2
  ring

theorem entireBranch_eq {w : ℂ} (hw : 0 < w.re) (n : ℕ) (hn : 1 ≤ n) :
    entireBranch w n hn = branch w hw n hn := by
  ext f
  apply Subtype.ext
  ext z
  rw [entireBranch_apply, branch_apply]

theorem differentiable_entireBranch (n : ℕ) (hn : 1 ≤ n) :
    Differentiable ℂ (fun w => entireBranch w n hn) := by
  have h := (differentiable_exp_smul_const ℂ (multiply (logDisc n hn))).comp
    ((differentiable_const (1 : ℂ)).sub differentiable_id)
  exact h.mul_const _

/-- Entire branch correction, with no domain-dependent proof argument. -/
def entireRemainder (n : ℕ) (w : ℂ) : DiscSpace →L[ℂ] DiscSpace :=
  entireBranch w (n + 1) (Nat.succ_le_succ (Nat.zero_le _)) -
    ((n + 1 : ℕ) : ℂ)^(-w) • constantProjection

theorem entireRemainder_eq {w : ℂ} (hw : 0 < w.re) (n : ℕ) :
    entireRemainder n w = branchRemainder w hw (n + 1)
      (Nat.succ_le_succ (Nat.zero_le _)) := by
  rw [entireRemainder, entireBranch_eq hw]
  rfl

theorem differentiable_entireRemainder (n : ℕ) :
    Differentiable ℂ (entireRemainder n) := by
  have hn : ((n + 1 : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.succ_ne_zero n)
  have h : Differentiable ℂ (fun w : ℂ => ((n + 1 : ℕ) : ℂ)^(-w)) := by
    simp only [Complex.cpow_def_of_ne_zero hn]
    fun_prop
  exact (differentiable_entireBranch _ _).sub (h.smul_const _)

/-- Operator-norm remainder after removal of the zeta constant mode. -/
def remainder (w : ℂ) : DiscSpace →L[ℂ] DiscSpace := ∑' n, entireRemainder n w

private theorem continuous_remainderBound : Continuous remainderBound := by
  unfold remainderBound powerBound
  fun_prop (disch := norm_num)

/-- The genuine operator corrections converge normally on the right half-plane. -/
theorem remainder_locallyUniform :
    SummableLocallyUniformlyOn entireRemainder {w : ℂ | 0 < w.re} := by
  apply SummableLocallyUniformlyOn_of_locally_bounded
    (isOpen_lt continuous_const Complex.continuous_re)
  intro K hK hKc
  by_cases hKn : K.Nonempty
  · obtain ⟨a, haK, hamin⟩ := hKc.exists_isMinOn hKn Complex.continuous_re.continuousOn
    obtain ⟨C, hC⟩ := hKc.bddAbove_image continuous_remainderBound.continuousOn
    have ha : 0 < a.re := hK haK
    have hb : 0 ≤ remainderBound a := by
      unfold remainderBound
      have hp := (powerBound_pos a).le
      have hq := (powerBound_pos (a + 1)).le
      positivity
    have hC0 : 0 ≤ C := hb.trans (hC ⟨a, haK, rfl⟩)
    have hs : Summable (fun j : ℕ => ((j + 1 : ℕ) : ℝ)^(-a.re - 1)) := by
      rw [show -a.re - 1 = -(a.re + 1) by ring]
      exact (summable_nat_add_iff (f := fun n : ℕ => (n : ℝ)^(-(a.re + 1))) 1).mpr
        (RHTower.Sieve.summable_nat_rpow_neg (by linarith only [ha]))
    refine ⟨fun j : ℕ => C * ((j + 1 : ℕ) : ℝ)^(-a.re - 1), hs.mul_left _, ?_⟩
    intro j w hwK
    have hw : 0 < w.re := hK hwK
    have hRe : a.re ≤ w.re := hamin hwK
    have hn : (1 : ℝ) ≤ (j + 1 : ℕ) := by exact_mod_cast Nat.succ_le_succ (Nat.zero_le j)
    rw [entireRemainder_eq hw]
    refine (norm_branchRemainder_le hw (Nat.succ_le_succ (Nat.zero_le j))).trans ?_
    exact mul_le_mul (hC ⟨w, hwK, rfl⟩)
      (Real.rpow_le_rpow_of_exponent_le hn (by linarith only [hRe]))
      (Real.rpow_nonneg (by positivity) _) hC0
  · refine ⟨fun _ : ℕ => 0, summable_zero, ?_⟩
    intro j w hwK
    exact False.elim (hKn ⟨w, hwK⟩)

/-- The zeta-subtracted actual Mayer family is holomorphic in operator norm. -/
theorem differentiableOn_remainder :
    DifferentiableOn ℂ remainder {w : ℂ | 0 < w.re} := by
  apply SummableLocallyUniformlyOn.differentiableOn
    (isOpen_lt continuous_const Complex.continuous_re) remainder_locallyUniform
  exact fun j w _ => (differentiable_entireRemainder j) w

/-- Proof-independent source family, meromorphic only through its zeta term. -/
def source (w : ℂ) : DiscSpace →L[ℂ] DiscSpace :=
  riemannZeta w • constantProjection + remainder w

theorem source_eq {w : ℂ} (hw : 0 < w.re) : source w = regularized w hw := by
  change riemannZeta w • constantProjection + ∑' n, entireRemainder n w =
    riemannZeta w • constantProjection + ∑' n, branchRemainder w hw (n + 1)
      (Nat.succ_le_succ (Nat.zero_le _))
  congr 1
  exact tsum_congr fun n => entireRemainder_eq hw n

/-- Holomorphic dependence on the actual source exponent away from its scalar pole. -/
theorem differentiableOn_source :
    DifferentiableOn ℂ source {w : ℂ | 0 < w.re ∧ w ≠ 1} := by
  intro w hw
  exact (((differentiableAt_riemannZeta hw.2).smul_const constantProjection).add
    (differentiableOn_remainder.differentiableAt
      ((isOpen_lt continuous_const Complex.continuous_re).mem_nhds hw.1))).differentiableWithinAt

private theorem poleCoordinate_tendsto :
    Tendsto (fun w : ℂ => w - 1) (𝓝[≠] 1) (𝓝 0) := by
  have h : Continuous (fun w : ℂ => w - 1) := continuous_id.sub continuous_const
  simpa only [sub_self] using (h.tendsto 1).mono_left nhdsWithin_le_nhds

/-- The actual source family has exactly the rank-one zeta residue. -/
theorem source_residue :
    Tendsto (fun w : ℂ => (w - 1) • source w) (𝓝[≠] 1) (𝓝 constantProjection) := by
  have hr : ContinuousAt remainder (1 : ℂ) :=
    (differentiableOn_remainder.differentiableAt
      ((isOpen_lt continuous_const Complex.continuous_re).mem_nhds (by norm_num))).continuousAt
  have hz := riemannZeta_residue_one.smul_const constantProjection
  have hzero := poleCoordinate_tendsto.smul (hr.tendsto.mono_left nhdsWithin_le_nhds)
  have hsum := hz.add hzero
  simpa only [source, smul_add, smul_smul, sub_self, zero_smul, one_smul, add_zero] using hsum

/-- The source pole is genuine: its norm-one residue prevents continuous extension. -/
theorem not_continuousAt_source_one : ¬ ContinuousAt source (1 : ℂ) := by
  intro hc
  have hz := poleCoordinate_tendsto.smul (hc.tendsto.mono_left nhdsWithin_le_nhds)
  have hz' : Tendsto (fun w : ℂ => (w - 1) • source w) (𝓝[≠] 1) (𝓝 0) := by
    simpa only [sub_self, zero_smul] using hz
  have he : constantProjection = 0 := tendsto_nhds_unique source_residue hz'
  have hn := norm_constantProjection
  rw [he, norm_zero] at hn
  norm_num at hn

private theorem continuous_localRemainderBound :
    Continuous (fun w : ℂ => localRemainderBound w innerRadius) := by
  unfold localRemainderBound powerBound
  fun_prop (disch := norm_num)

private theorem localRemainderBound_nonneg (w : ℂ) :
    0 ≤ localRemainderBound w innerRadius := by
  have hp := (powerBound_pos w).le
  have hq := (powerBound_pos (w + 1)).le
  unfold localRemainderBound innerRadius
  positivity

/-- The source's geometric Cauchy bounds are uniform on compact parameter sets. -/
theorem constantBound_boundedOn_compact {K : Set ℂ}
    (hK : K ⊆ {w : ℂ | 0 < w.re ∧ w ≠ 1}) (hKc : IsCompact K) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ w ∈ K, constantBound w ≤ C := by
  by_cases hKn : K.Nonempty
  · obtain ⟨a, haK, hamin⟩ := hKc.exists_isMinOn hKn Complex.continuous_re.continuousOn
    have ha : 0 < a.re := (hK haK).1
    have hzcont : ContinuousOn (fun w => ‖riemannZeta w‖) K :=
      fun w hw => ((differentiableAt_riemannZeta (hK hw).2).continuousAt.norm).continuousWithinAt
    obtain ⟨Z, hZ⟩ := hKc.bddAbove_image hzcont
    obtain ⟨B, hB⟩ := hKc.bddAbove_image continuous_localRemainderBound.continuousOn
    have hZ0 : 0 ≤ Z := (norm_nonneg _).trans (hZ ⟨a, haK, rfl⟩)
    have hB0 : 0 ≤ B := (localRemainderBound_nonneg a).trans (hB ⟨a, haK, rfl⟩)
    let d : ℂ → ℕ → ℝ := fun w j => ((j + 1 : ℕ) : ℝ)^(-w.re - 1)
    have hs : Summable (d a) := by
      change Summable (fun j : ℕ => ((j + 1 : ℕ) : ℝ)^(-a.re - 1))
      rw [show -a.re - 1 = -(a.re + 1) by ring]
      exact (summable_nat_add_iff (f := fun n : ℕ => (n : ℝ)^(-(a.re + 1))) 1).mpr
        (RHTower.Sieve.summable_nat_rpow_neg (by linarith only [ha]))
    have hd0 (w : ℂ) (j : ℕ) : 0 ≤ d w j := Real.rpow_nonneg (by positivity) _
    refine ⟨Z + B * ∑' j, d a j, add_nonneg hZ0 (mul_nonneg hB0 (tsum_nonneg (hd0 a))), ?_⟩
    intro w hw
    have hRe : a.re ≤ w.re := hamin hw
    have hle (j : ℕ) : d w j ≤ d a j := by
      have hn : (1 : ℝ) ≤ (j + 1 : ℕ) := by exact_mod_cast Nat.succ_le_succ (Nat.zero_le j)
      exact Real.rpow_le_rpow_of_exponent_le hn (by linarith only [hRe])
    have hsw : Summable (d w) := hs.of_nonneg_of_le (hd0 w) hle
    change ‖riemannZeta w‖ + localRemainderBound w innerRadius * ∑' j, d w j ≤ _
    exact add_le_add (hZ ⟨w, hw, rfl⟩)
      (mul_le_mul (hB ⟨w, hw, rfl⟩) (hsw.tsum_le_tsum hle hs)
        (tsum_nonneg (hd0 w)) hB0)
  · exact ⟨0, le_rfl, fun w hw => False.elim (hKn ⟨w, hw⟩)⟩

/-- Proof-independent actual Cauchy matrix. -/
def sourceMatrix (w : ℂ) (i j : ℕ) : ℂ :=
  functional i (((balanceRadius : ℂ)^j)⁻¹ • source w (monomial j))

theorem sourceMatrix_eq {w : ℂ} (hw : 0 < w.re) : sourceMatrix w = matrix w hw := by
  funext i j
  rw [sourceMatrix, source_eq hw]
  rfl

theorem differentiableOn_sourceMatrix (i j : ℕ) :
    DifferentiableOn ℂ (fun w => sourceMatrix w i j) {w : ℂ | 0 < w.re ∧ w ≠ 1} := by
  have hd := (ContinuousLinearMap.apply ℂ DiscSpace (monomial j)).differentiable.comp_differentiableOn
    differentiableOn_source
  have hd' : DifferentiableOn ℂ
      (fun w => ((balanceRadius : ℂ)^j)⁻¹ • source w (monomial j))
      {w : ℂ | 0 < w.re ∧ w ≠ 1} :=
    hd.const_smul (((balanceRadius : ℂ)^j)⁻¹)
  exact (functional i).differentiable.comp_differentiableOn hd'

/-- The actual source Fredholm determinant as a function of both parameters. -/
def sourceDeterminant (w lam : ℂ) : ℂ := GeomFredholm.fdet (sourceMatrix w) lam

theorem sourceDeterminant_eq {w : ℂ} (hw : 0 < w.re) (lam : ℂ) :
    sourceDeterminant w lam = determinant w hw lam := by
  rw [sourceDeterminant, sourceMatrix_eq hw]
  rfl

/-- Holomorphic dependence of the actual determinant on its source exponent. -/
theorem differentiableOn_sourceDeterminant (lam : ℂ) :
    DifferentiableOn ℂ (fun w => sourceDeterminant w lam) {w : ℂ | 0 < w.re ∧ w ≠ 1} := by
  let U : Set ℂ := {w : ℂ | 0 < w.re ∧ w ≠ 1}
  have hU : IsOpen U := (isOpen_lt continuous_const Complex.continuous_re).inter isClosed_singleton.isOpen_compl
  intro w hw
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.1 hU w hw
  have hhalf : 0 < r / 2 := half_pos hr
  have hclosed : closedBall w (r / 2) ⊆ U :=
    (closedBall_subset_ball (half_lt_self hr)).trans hball
  obtain ⟨C, hC0, hC⟩ := constantBound_boundedOn_compact hclosed (isCompact_closedBall w (r / 2))
  have hdecay : ∀ z ∈ ball w (r / 2), GeomFredholm.GeomDecay (sourceMatrix z) C rate := by
    intro z hz
    have hzC := ball_subset_closedBall hz
    have hzU := hclosed hzC
    rw [sourceMatrix_eq hzU.1]
    have hg := geomDecay_matrix hzU.1
    refine ⟨hC0, rate_bounds.1, rate_bounds.2, fun i j => ?_⟩
    exact (hg.bound i j).trans (by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (hC z hzC) (pow_nonneg rate_bounds.1 i))
        (pow_nonneg rate_bounds.1 j))
  have hd := GeomFredholm.differentiableOn_fdet isOpen_ball hdecay
    (fun i j => (differentiableOn_sourceMatrix i j).mono
      (ball_subset_closedBall.trans hclosed)) lam rate_bounds.1 rate_bounds.2
  exact (hd.differentiableAt (isOpen_ball.mem_nhds (mem_ball_self hhalf))).differentiableWithinAt

end GaloisForLFunctions.RenormalizedIntersectionTheory.MayerParameter

#print axioms GaloisForLFunctions.RenormalizedIntersectionTheory.MayerParameter.exp_multiply_apply
#print axioms GaloisForLFunctions.RenormalizedIntersectionTheory.MayerParameter.differentiableOn_source
#print axioms GaloisForLFunctions.RenormalizedIntersectionTheory.MayerParameter.source_residue
#print axioms GaloisForLFunctions.RenormalizedIntersectionTheory.MayerParameter.differentiableOn_sourceDeterminant

#print axioms GaloisForLFunctions.RenormalizedIntersectionTheory.MayerParameter.entireBranch_eq

#print axioms GaloisForLFunctions.RenormalizedIntersectionTheory.MayerParameter.remainder_locallyUniform

#print axioms GaloisForLFunctions.RenormalizedIntersectionTheory.MayerParameter.differentiableOn_remainder

#print axioms GaloisForLFunctions.RenormalizedIntersectionTheory.MayerParameter.source_eq

#print axioms GaloisForLFunctions.RenormalizedIntersectionTheory.MayerParameter.not_continuousAt_source_one

#print axioms GaloisForLFunctions.RenormalizedIntersectionTheory.MayerParameter.constantBound_boundedOn_compact

#print axioms GaloisForLFunctions.RenormalizedIntersectionTheory.MayerParameter.sourceDeterminant_eq
