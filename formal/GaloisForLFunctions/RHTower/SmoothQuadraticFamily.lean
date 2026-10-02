import GaloisForLFunctions.RHTower.SmoothLogPhaseFresnel
import GaloisForLFunctions.HTGeometry.InterfinityGeometry.ParametricSmoothness

/-!
# Uniform Fresnel remainder for smooth amplitude families

Parametric averaging divides out a vanishing saddle value while preserving joint
smoothness. Compactness then supplies one remainder for the entire parameter
family, including smooth cutoff transitions where analyticity need not hold.
The full Fresnel formula follows with both orientations and the entire support.
-/

noncomputable section
open Complex MeasureTheory Set Filter
open scoped Topology ContDiff
namespace GaloisForLFunctions.RHTower
open GaloisForLFunctions.HTGeometry.Interfinity

private def saddlePartial (B : ℝ × ℝ → ℂ) (p : ℝ × ℝ) : ℂ :=
  fderiv ℝ B p (0, 1)

private theorem contDiff_saddlePartial {B : ℝ × ℝ → ℂ} (hB : ContDiff ℝ ∞ B) :
    ContDiff ℝ ∞ (saddlePartial B) :=
  (contDiff_infty_iff_fderiv.mp hB).2.clm_apply contDiff_const

private theorem hasDerivAt_saddleSlice {B : ℝ × ℝ → ℂ}
    (hB : ContDiff ℝ ∞ B) (p x : ℝ) :
    HasDerivAt (fun y => B (p, y)) (saddlePartial B (p, x)) x := by
  exact ((hB.differentiable (by simp) (p, x)).hasFDerivAt).comp_hasDerivAt x
    ((hasDerivAt_const x p).prodMk (hasDerivAt_id x))

private def smoothSaddleSlope (B : ℝ × ℝ → ℂ) (p : ℝ × ℝ) : ℂ :=
  ∫ t in (0 : ℝ)..1, saddlePartial B (p.1, t * p.2)

private theorem contDiff_smoothSaddleSlope {B : ℝ × ℝ → ℂ}
    (hB : ContDiff ℝ ∞ B) : ContDiff ℝ ∞ (smoothSaddleSlope B) := by
  have hh : ContDiff ℝ ∞ (fun q : (ℝ × ℝ) × ℝ => (q.1.1, q.2 * q.1.2)) :=
    (contDiff_fst.fst).prodMk (contDiff_snd.mul contDiff_fst.snd)
  have hF := (contDiff_saddlePartial hB).comp hh
  rw [contDiff_infty]
  intro n
  exact contDiff_paramAvg n ((contDiff_infty.mp hF) n)

private theorem smoothSaddleSlope_identity {B : ℝ × ℝ → ℂ}
    (hB : ContDiff ℝ ∞ B) (p x : ℝ) :
    B (p, x) - B (p, 0) = (x : ℂ) * smoothSaddleSlope B (p, x) := by
  have hder (t : ℝ) : HasDerivAt (fun u : ℝ => B (p, u * x))
      ((x : ℂ) * saddlePartial B (p, t * x)) t := by
    have hh := (hasDerivAt_saddleSlice hB p (t * x)).scomp t
      ((hasDerivAt_id' t).mul_const x)
    simpa only [Function.comp_apply, mul_one, one_mul, Complex.real_smul] using! hh
  have hc : Continuous (fun t : ℝ => (x : ℂ) * saddlePartial B (p, t * x)) :=
    continuous_const.mul ((contDiff_saddlePartial hB).continuous.comp
      (continuous_const.prodMk (continuous_id.mul_const x)))
  have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t (_ : t ∈ uIcc (0 : ℝ) 1) => hder t) (hc.intervalIntegrable 0 1)
  simpa only [one_mul, zero_mul, intervalIntegral.integral_const_mul,
    smoothSaddleSlope] using hi.symm

/-- Joint smoothness supplies one signed stationary remainder for a complete compact family,
including parameters where the physical cutoff is in its transition region. -/
theorem exists_uniform_quadratic_zero_saddle_remainder
    {B : ℝ × ℝ → ℂ} (hB : ContDiff ℝ ∞ B) {K : Set ℝ} (hK : IsCompact K)
    {R : ℝ} (hR : 0 < R) (h0 : ∀ p ∈ K, B (p, 0) = 0)
    (hs : ∀ p ∈ K, ∀ x : ℝ, R ≤ |x| → B (p, x) = 0) :
    ∃ C : ℝ, 0 < C ∧ ∀ p ∈ K, ∀ lam : ℝ, 0 < lam →
      ‖∫ x : ℝ, B (p, x) * quadPhase lam x‖ ≤ C / (lam * Real.sqrt lam) := by
  let c := smoothSaddleSlope B
  let c' := saddlePartial c
  let c'' := saddlePartial c'
  have hc : ContDiff ℝ ∞ c := contDiff_smoothSaddleSlope hB
  have hc' : ContDiff ℝ ∞ c' := contDiff_saddlePartial hc
  have hc'' : ContDiff ℝ ∞ c'' := contDiff_saddlePartial hc'
  let L := R + 1
  have hL : 0 < L := by dsimp [L]; linarith
  obtain ⟨M, hM⟩ := (hK.prod (isCompact_Icc (a := -L) (b := L))).exists_bound_of_continuousOn
    hc''.continuous.continuousOn
  let M₁ := |M| + 1
  have hM₁ : 0 < M₁ := by dsimp [M₁]; positivity
  refine ⟨1 + 64 * L * M₁, by positivity, ?_⟩
  intro p hp lam hlam
  have hshape (x : ℝ) : B (p, x) = (x : ℂ) * c (p, x) := by
    simpa only [h0 p hp, sub_zero] using smoothSaddleSlope_identity hB p x
  have hcz (x : ℝ) (hx : R ≤ |x|) : c (p, x) = 0 := by
    have hx0 : (x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr
      (fun hh => by simpa [hh] using hR.trans_le hx)
    exact (mul_eq_zero.mp ((hshape x).symm.trans (hs p hp x hx))).resolve_left hx0
  have hc'z (x : ℝ) (hx : R < |x|) : c' (p, x) = 0 := by
    have he : (fun y : ℝ => c (p, y)) =ᶠ[𝓝 x] (fun _ => (0 : ℂ)) := by
      filter_upwards [(isOpen_lt continuous_const continuous_abs).mem_nhds hx] with y hy
      exact hcz y hy.le
    exact (hasDerivAt_saddleSlice hc p x).deriv.symm.trans
      (he.deriv_eq.trans (deriv_const x (0 : ℂ)))
  have hfinite : (∫ x in (-L)..L, (x : ℂ) * c (p, x) * quadPhase lam x) =
      ∫ x : ℝ, B (p, x) * quadPhase lam x := by
    simp_rw [← hshape]
    rw [intervalIntegral.integral_of_le (by linarith : -L ≤ L)]
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro x hx
    have hb : R ≤ |x| := by
      by_contra hh
      have ha := abs_lt.mp (lt_of_not_ge hh)
      apply hx
      dsimp [L]
      constructor <;> linarith
    rw [hs p hp x hb, zero_mul]
  have hV : (∫ x in (-L)..L, ‖c'' (p, x)‖) ≤ 2 * L * M₁ := by
    have hh := intervalIntegral.integral_mono_on (by linarith : -L ≤ L)
      ((hc''.continuous.comp (continuous_const.prodMk continuous_id)).norm.intervalIntegrable
        (-L) L) (intervalIntegrable_const (c := M₁) (μ := volume))
      (fun x hx => (hM (p, x) ⟨hp, hx⟩).trans (by dsimp [M₁]; linarith [le_abs_self M]))
    simpa only [Function.comp_apply, id_eq, intervalIntegral.integral_const, smul_eq_mul, sub_neg_eq_add,
      ← two_mul] using hh
  have hb := norm_integral_quadratic_divided_remainder_le hlam (by linarith : -L ≤ L)
    (c := fun x => c (p, x)) (c' := fun x => c' (p, x)) (c'' := fun x => c'' (p, x))
    (fun x _ => hasDerivAt_saddleSlice hc p x)
    (fun x _ => hasDerivAt_saddleSlice hc' p x)
    (hc''.continuous.comp (continuous_const.prodMk continuous_id)).continuousOn
  have hLp : R < |L| := by rw [abs_of_pos hL]; dsimp [L]; linarith
  have hLn : R < |-L| := by rwa [abs_neg]
  rw [hfinite, hcz L hLp.le, hcz (-L) hLn.le, hc'z L hLp, hc'z (-L) hLn,
    norm_zero, zero_add, zero_div, zero_add] at hb
  apply hb.trans
  apply div_le_div_of_nonneg_right _ (by positivity)
  nlinarith [hV]

private theorem hasCompactSupport_saddleSlice {B : ℝ × ℝ → ℂ} {p R : ℝ}
    (hs : ∀ x : ℝ, R ≤ |x| → B (p, x) = 0) :
    HasCompactSupport (fun x => B (p, x)) := by
  apply HasCompactSupport.intro isCompact_Icc (K := Icc (-R) R)
  intro x hx
  apply hs
  by_contra hh
  have ha := abs_lt.mp (lt_of_not_ge hh)
  exact hx ⟨ha.1.le, ha.2.le⟩

/-- The full Fresnel formula holds uniformly for every member of a smooth compact family.
No analyticity at its moving saddle is required. -/
theorem exists_uniform_quadratic_fresnel_remainder
    {B : ℝ × ℝ → ℂ} (hB : ContDiff ℝ ∞ B) {K : Set ℝ} (hK : IsCompact K)
    {R : ℝ} (hR : 0 < R)
    (hs : ∀ p ∈ K, ∀ x : ℝ, R ≤ |x| → B (p, x) = 0) :
    ∃ C : ℝ, 0 < C ∧ ∀ p ∈ K, ∀ lam : ℝ, 0 < lam →
      ‖(∫ x : ℝ, B (p, x) * quadPhase lam x) -
        B (p, 0) * (Real.sqrt (2 * Real.pi / lam) : ℂ) *
          Complex.exp (((Real.pi / 4 : ℝ) : ℂ) * I)‖ ≤
            C / (lam * Real.sqrt lam) := by
  let eta : ContDiffBump (0 : ℝ) := ⟨1, 2, by norm_num, by norm_num⟩
  let Z : ℝ × ℝ → ℂ := fun q => B q - B (q.1, 0) * (eta q.2 : ℂ)
  have hZ : ContDiff ℝ ∞ Z := hB.sub
    ((hB.comp (contDiff_fst.prodMk contDiff_const)).mul
      (Complex.ofRealCLM.contDiff.comp (eta.contDiff.comp contDiff_snd)))
  have hZ0 (p : ℝ) (_ : p ∈ K) : Z (p, 0) = 0 := by
    simp only [Z, eta.one_of_mem_closedBall (Metric.mem_closedBall_self eta.rIn_pos.le),
      Complex.ofReal_one, mul_one, sub_self]
  have hZs (p : ℝ) (hp : p ∈ K) (x : ℝ) (hx : R + 3 ≤ |x|) : Z (p, x) = 0 := by
    have he : eta x = 0 := eta.zero_of_le_dist
      (by simpa only [Real.dist_eq, sub_zero] using (show (2 : ℝ) ≤ |x| by linarith))
    simp only [Z, hs p hp x (by linarith), he, Complex.ofReal_zero, mul_zero, sub_zero]
  obtain ⟨Cz, hCz, hz⟩ := exists_uniform_quadratic_zero_saddle_remainder hZ hK
    (show 0 < R + 3 by linarith) hZ0 hZs
  obtain ⟨Ce, hCe, he⟩ := exists_smoothCutoff_fresnel_remainder eta
  obtain ⟨M, hM⟩ := hK.exists_bound_of_continuousOn
    (hB.continuous.comp (continuous_id.prodMk continuous_const)).continuousOn
  let M₁ := |M| + 1
  have hM₁ : 0 < M₁ := by dsimp [M₁]; positivity
  refine ⟨Cz + M₁ * Ce, by positivity, ?_⟩
  intro p hp lam hlam
  have hBint : Integrable (fun x : ℝ => B (p, x) * quadPhase lam x) := by
    simpa only [Function.comp_apply, id_eq, Pi.mul_apply] using!
      ((hB.continuous.comp (continuous_const.prodMk continuous_id)).mul
      (continuous_quadPhase lam)).integrable_of_hasCompactSupport
      (hasCompactSupport_saddleSlice (hs p hp)).mul_right
  have heint : Integrable (fun x : ℝ => (eta x : ℂ) * quadPhase lam x) :=
    ((Complex.continuous_ofReal.comp eta.continuous).mul
      (continuous_quadPhase lam)).integrable_of_hasCompactSupport
      (eta.hasCompactSupport.comp_left (g := fun x : ℝ => (x : ℂ)) rfl).mul_right
  have hsplit : (∫ x : ℝ, B (p, x) * quadPhase lam x) -
      B (p, 0) * (Real.sqrt (2 * Real.pi / lam) : ℂ) *
        Complex.exp (((Real.pi / 4 : ℝ) : ℂ) * I) =
      (∫ x : ℝ, Z (p, x) * quadPhase lam x) + B (p, 0) *
        ((∫ x : ℝ, (eta x : ℂ) * quadPhase lam x) -
          (Real.sqrt (2 * Real.pi / lam) : ℂ) *
            Complex.exp (((Real.pi / 4 : ℝ) : ℂ) * I)) := by
    simp only [Z, sub_mul, mul_assoc]
    rw [integral_sub hBint (heint.const_mul _), integral_const_mul]
    ring
  rw [hsplit]
  calc
    _ ≤ ‖∫ x : ℝ, Z (p, x) * quadPhase lam x‖ + ‖B (p, 0)‖ *
        ‖(∫ x : ℝ, (eta x : ℂ) * quadPhase lam x) -
          (Real.sqrt (2 * Real.pi / lam) : ℂ) *
            Complex.exp (((Real.pi / 4 : ℝ) : ℂ) * I)‖ := by
      rw [← norm_mul]
      exact norm_add_le _ _
    _ ≤ Cz / (lam * Real.sqrt lam) + M₁ * (Ce / (lam * Real.sqrt lam)) := by
      apply add_le_add (hz p hp lam hlam)
      exact mul_le_mul ((hM p hp).trans (by dsimp [M₁]; linarith [le_abs_self M]))
        (he lam hlam) (norm_nonneg _) hM₁.le
    _ = _ := by ring

/-- The same uniform family statement retains the conjugate Fresnel orientation. -/
theorem exists_uniform_quadratic_fresnel_negative_remainder
    {B : ℝ × ℝ → ℂ} (hB : ContDiff ℝ ∞ B) {K : Set ℝ} (hK : IsCompact K)
    {R : ℝ} (hR : 0 < R)
    (hs : ∀ p ∈ K, ∀ x : ℝ, R ≤ |x| → B (p, x) = 0) :
    ∃ C : ℝ, 0 < C ∧ ∀ p ∈ K, ∀ lam : ℝ, 0 < lam →
      ‖(∫ x : ℝ, B (p, x) * quadPhase (-lam) x) -
        B (p, 0) * (Real.sqrt (2 * Real.pi / lam) : ℂ) *
          Complex.exp (((-(Real.pi / 4) : ℝ) : ℂ) * I)‖ ≤
            C / (lam * Real.sqrt lam) := by
  let J : ℝ × ℝ → ℂ := fun q => (starRingEnd ℂ) (B q)
  have hJ : ContDiff ℝ ∞ J := Complex.conjCLE.contDiff.comp hB
  have hJs (p : ℝ) (hp : p ∈ K) (x : ℝ) (hx : R ≤ |x|) : J (p, x) = 0 := by
    simp only [J, hs p hp x hx, map_zero]
  obtain ⟨C, hC, hb⟩ := exists_uniform_quadratic_fresnel_remainder hJ hK hR hJs
  refine ⟨C, hC, ?_⟩
  intro p hp lam hlam
  have he (x : ℝ) : B (p, x) * quadPhase (-lam) x =
      (starRingEnd ℂ) (J (p, x) * quadPhase lam x) := by
    simp only [J, quadPhase, map_mul, Complex.conj_conj, ← Complex.exp_conj,
      Complex.conj_ofReal, Complex.conj_I]
    congr 2
    push_cast
    ring
  have hm : B (p, 0) * (Real.sqrt (2 * Real.pi / lam) : ℂ) *
      Complex.exp (((-(Real.pi / 4) : ℝ) : ℂ) * I) =
      (starRingEnd ℂ) (J (p, 0) * (Real.sqrt (2 * Real.pi / lam) : ℂ) *
        Complex.exp (((Real.pi / 4 : ℝ) : ℂ) * I)) := by
    simp only [J, map_mul, Complex.conj_conj, Complex.conj_ofReal,
      ← Complex.exp_conj, Complex.conj_I]
    congr 2
    push_cast
    ring
  simp_rw [he]
  rw [integral_conj, hm, ← map_sub, RCLike.norm_conj]
  exact hb p hp lam hlam

end GaloisForLFunctions.RHTower
