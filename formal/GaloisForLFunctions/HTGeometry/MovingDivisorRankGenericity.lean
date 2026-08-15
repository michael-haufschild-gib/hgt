import GaloisForLFunctions.HTGeometry.MovingDivisorFiniteJetProbe
import GaloisForLFunctions.HTGeometry.MovingCanonicalFullTranslationRankGenericity

/-!
# Rank genericity of a moving divisor

The expanded evaluation family of the carrier of a moving divisor is a submersion in the bounded
parameter, so every compact patch of rank-defect configurations is avoided on a dense open set and
the Baire intersection over all finite differential patterns leaves a dense residual set of
parameters carrying no differential relation.
-/

namespace GaloisForLFunctions.HTGeometry

open Set Topology Filter
open ClassicalAnalyticNevanlinnaCarrierFamily
open scoped ENNReal

noncomputable section
set_option maxHeartbeats 2000000

/-- The reciprocal-square majorant with an arbitrary constant. -/
def natMajorant (M : ℝ) (a : ℕ) : ℝ := M / ((a : ℝ) + 1) ^ 2

theorem summable_natMajorant (M : ℝ) : Summable (natMajorant M) := by
  have hbase : Summable (fun a : ℕ => (1 : ℝ) / (a : ℝ) ^ 2) :=
    Real.summable_one_div_nat_pow.mpr (by norm_num)
  have hshift := (summable_nat_add_iff
    (f := fun a : ℕ => (1 : ℝ) / (a : ℝ) ^ 2) 1).mpr hbase
  have hone : Summable (fun a : ℕ => (1 : ℝ) / ((a : ℝ) + 1) ^ 2) := by
    simpa only [Nat.cast_add, Nat.cast_one] using hshift
  have hmul := hone.mul_left M
  refine hmul.congr fun a => ?_
  rw [natMajorant]
  ring

namespace MovingDivisor

/-- The carrier of a moving divisor as a function of the bounded parameter. -/
def logDerivativeB (Dv : MovingDivisor) (θ : BoundedRealSequence) : ℂ → ℂ :=
  Dv.logDerivative (θ : ℕ → ℝ)

theorem inv_sq_le_majorantB (Dv : MovingDivisor) (θ : BoundedRealSequence) (a : ℕ) :
    1 / ‖(Dv.zeroAt θ a : ℂ)‖ ^ 2 ≤ Dv.majorantConst / ((a : ℝ) + 1) ^ 2 :=
  Dv.inv_sq_le_majorant _ a

def localJetMajorant (Dv : MovingDivisor) (k : ℕ) (z : ℂ) (a : ℕ) : ℝ :=
  let y := z.im / 2
  let R := ‖z‖ + y
  let C := 1 + R / y
  (if k = 0 then R * C else C ^ 2 * y⁻¹ ^ (k - 1)) *
    natMajorant Dv.majorantConst a

theorem summable_localJetMajorant (Dv : MovingDivisor)
    (k : ℕ) {z : ℂ} (_hz : 0 < z.im) :
    Summable (Dv.localJetMajorant k z) := by
  unfold MovingDivisor.localJetMajorant
  exact (summable_natMajorant Dv.majorantConst).mul_left
    (if k = 0 then (‖z‖ + z.im / 2) *
      (1 + (‖z‖ + z.im / 2) / (z.im / 2))
    else (1 + (‖z‖ + z.im / 2) / (z.im / 2)) ^ 2 *
      (z.im / 2)⁻¹ ^ (k - 1))

theorem normalizedJetTerm_norm_le_localMajorant (Dv : MovingDivisor)
    (k a : ℕ) (θ : BoundedRealSequence) {z₀ z : ℂ}
    (hz₀ : 0 < z₀.im) (hz : z ∈ Metric.ball z₀ (z₀.im / 2)) :
    ‖Dv.normalizedJetTerm θ k a z‖ ≤
      Dv.localJetMajorant k z₀ a := by
  let y : ℝ := z₀.im / 2
  let R : ℝ := ‖z₀‖ + y
  let C : ℝ := 1 + R / y
  let A : ℝ := ‖(Dv.zeroAt θ a : ℂ)‖
  let d : ℝ := ‖(Dv.zeroAt θ a : ℂ) - z‖
  have hy : 0 < y := half_pos hz₀
  have hdist : ‖z - z₀‖ < y := by
    simpa only [Metric.mem_ball, dist_eq_norm] using hz
  have himnorm : |(z - z₀).im| ≤ ‖z - z₀‖ :=
    Complex.abs_im_le_norm _
  have hzim : y < z.im := by
    have habs : |z.im - z₀.im| < y := by
      exact lt_of_le_of_lt (by simpa [Complex.sub_im] using himnorm) hdist
    rw [abs_lt] at habs
    dsimp only [y] at habs ⊢
    linarith
  have hzpos : 0 < z.im := hy.trans hzim
  have hApos : 0 < A := norm_pos_iff.mpr
    (Complex.ofReal_ne_zero.mpr (ne_of_gt (Dv.zeroAt_pos θ a)))
  have hdpos : 0 < d := by
    rw [norm_pos_iff]
    intro h
    have him := congrArg Complex.im h
    simp at him
    exact (ne_of_gt hzpos) him
  have hyd : y ≤ d := by
    have hi : z.im ≤ d := by
      have hi' := Complex.abs_im_le_norm
        ((Dv.zeroAt θ a : ℂ) - z)
      have him :
          ((Dv.zeroAt θ a : ℂ) - z).im = -z.im := by simp
      rw [him, abs_neg, abs_of_pos hzpos] at hi'
      exact hi'
    exact hzim.le.trans hi
  have hnormz : ‖z‖ ≤ R := by
    have htri : ‖z‖ ≤ ‖z - z₀‖ + ‖z₀‖ := by
      calc
        ‖z‖ = ‖(z - z₀) + z₀‖ := by
          congr 2
          abel
        _ ≤ ‖z - z₀‖ + ‖z₀‖ := norm_add_le _ _
    dsimp only [R]
    linarith
  have hAz : A ≤ d + ‖z‖ := by
    calc
      A = ‖(Dv.zeroAt θ a : ℂ)‖ := rfl
      _ = ‖((Dv.zeroAt θ a : ℂ) - z) + z‖ := by
        congr 2
        abel
      _ ≤ d + ‖z‖ := norm_add_le _ _
  have hRscale : R ≤ (R / y) * d := by
    rw [div_mul_eq_mul_div, le_div_iff₀ hy]
    exact mul_le_mul_of_nonneg_left hyd (by
      dsimp only [R]
      positivity)
  have hACd : A ≤ C * d := by
    dsimp only [C]
    nlinarith
  have hinvAC : d⁻¹ ≤ C * A⁻¹ := by
    have hdiv : 1 / d ≤ C / A := by
      rw [div_le_div_iff₀ hdpos hApos]
      simpa [mul_comm] using hACd
    simpa [div_eq_mul_inv] using hdiv
  have hinvY : d⁻¹ ≤ y⁻¹ := by
    simpa [one_div] using one_div_le_one_div_of_le hy hyd
  have hAmajor : 1 / A ^ 2 ≤ Dv.majorantConst / ((a : ℝ) + 1) ^ 2 := by
    exact Dv.inv_sq_le_majorantB θ a
  by_cases hk : k = 0
  · subst k
    have hzeroNe : (Dv.zeroAt θ a : ℂ) ≠ 0 :=
      Complex.ofReal_ne_zero.mpr
        (ne_of_gt (Dv.zeroAt_pos θ a))
    have hsep : (Dv.zeroAt θ a : ℂ) - z ≠ 0 := by
      exact norm_ne_zero_iff.mp (ne_of_gt hdpos)
    have heq :
        ((Dv.zeroAt θ a : ℂ) - z)⁻¹ -
            (Dv.zeroAt θ a : ℂ)⁻¹ =
          z / ((Dv.zeroAt θ a : ℂ) *
            ((Dv.zeroAt θ a : ℂ) - z)) := by
      field_simp [hzeroNe, hsep]
      ring
    rw [MovingDivisor.normalizedJetTerm, if_pos rfl,
      MovingDivisor.regularizedTerm, heq, norm_div, norm_mul]
    change ‖z‖ / (A * d) ≤ _
    have hbound : ‖z‖ / (A * d) ≤
        (R * C) * (1 / A ^ 2) := by
      rw [div_eq_mul_inv, mul_inv]
      calc
        ‖z‖ * (A⁻¹ * d⁻¹) ≤ R * (A⁻¹ * (C * A⁻¹)) := by
          gcongr
        _ = (R * C) * (1 / A ^ 2) := by
          field_simp
    exact hbound.trans (mul_le_mul_of_nonneg_left hAmajor (by positivity))
  · obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk
    rw [MovingDivisor.normalizedJetTerm, if_neg (Nat.succ_ne_zero m),
      norm_pow, norm_inv]
    change d⁻¹ ^ (m + 2) ≤ _
    have hbound :
        d⁻¹ ^ (m + 2) ≤
          (C ^ 2 * y⁻¹ ^ m) * (1 / A ^ 2) := by
      rw [pow_add]
      calc
        d⁻¹ ^ m * d⁻¹ ^ 2 ≤
            y⁻¹ ^ m * (C * A⁻¹) ^ 2 :=
          mul_le_mul (pow_le_pow_left₀ (by positivity) hinvY m)
            (pow_le_pow_left₀ (by positivity) hinvAC 2)
            (by positivity) (by positivity)
        _ = (C ^ 2 * y⁻¹ ^ m) * (1 / A ^ 2) := by
          field_simp
    have hconst : 0 ≤ C ^ 2 * y⁻¹ ^ m := by positivity
    exact hbound.trans (mul_le_mul_of_nonneg_left hAmajor hconst)

theorem continuousAt_normalizedJet (Dv : MovingDivisor)
    (k : ℕ) (θ : BoundedRealSequence) {z : ℂ} (hz : 0 < z.im) :
    ContinuousAt
      (fun p : BoundedRealSequence × ℂ =>
        Dv.normalizedJet p.1 k p.2) (θ, z) := by
  let S : Set (BoundedRealSequence × ℂ) :=
    Set.univ ×ˢ Metric.ball z (z.im / 2)
  have hballUpper : Metric.ball z (z.im / 2) ⊆ upperHalfPlane := by
    intro w hw
    have hdist : ‖w - z‖ < z.im / 2 := by
      simpa only [Metric.mem_ball, dist_eq_norm] using hw
    have himnorm : |(w - z).im| ≤ ‖w - z‖ :=
      Complex.abs_im_le_norm _
    have habs : |w.im - z.im| < z.im / 2 := by
      exact lt_of_le_of_lt (by simpa [Complex.sub_im] using himnorm) hdist
    rw [abs_lt] at habs
    change 0 < w.im
    linarith
  have hterm : ∀ a, ContinuousOn
      (fun p : BoundedRealSequence × ℂ =>
        Dv.normalizedJetTerm p.1 k a p.2) S := by
    intro a
    exact (Dv.continuousOn_normalizedJetTerm k a).mono
      (fun p hp => ⟨Set.mem_univ _, hballUpper hp.2⟩)
  have hcontOn : ContinuousOn
      (fun p : BoundedRealSequence × ℂ =>
        ∑' a, Dv.normalizedJetTerm p.1 k a p.2) S :=
    continuousOn_tsum hterm
      (Dv.summable_localJetMajorant k hz)
      (fun a p hp =>
        Dv.normalizedJetTerm_norm_le_localMajorant
          k a p.1 hz hp.2)
  have hSn : S ∈ 𝓝 (θ, z) := by
    apply (isOpen_univ.prod Metric.isOpen_ball).mem_nhds
    exact ⟨Set.mem_univ _, Metric.mem_ball_self (half_pos hz)⟩
  exact hcontOn.continuousAt hSn

abbrev HasCoherentComplexDerivAt
    (f : ℂ → ℂ) (f' x : ℂ) : Prop :=
  @HasDerivAt ℂ inferInstance ℂ
    instCommCStarAlgebraComplex.toCommRing.toAddCommGroup
    (NormedAlgebra.toNormedSpace ℂ).toModule
    inferInstance inferInstance f f' x

theorem normalizedJetTerm_hasDerivAt (Dv : MovingDivisor)
    (θ : BoundedRealSequence) (k a : ℕ) {z : ℂ} (hz : 0 < z.im) :
    HasCoherentComplexDerivAt
      (Dv.normalizedJetTerm θ k a)
      ((k + 1 : ℕ) •
        Dv.normalizedJetTerm θ (k + 1) a z) z := by
  have hsep : (Dv.zeroAt θ a : ℂ) - z ≠ 0 := by
    intro h
    have him := congrArg Complex.im h
    simp at him
    exact (ne_of_gt hz) him
  have hbase : HasCoherentComplexDerivAt
      (fun w : ℂ => ((Dv.zeroAt θ a : ℂ) - w)⁻¹)
      ((((Dv.zeroAt θ a : ℂ) - z)⁻¹) ^ 2) z := by
    have h :=
      ((hasDerivAt_const (x := z)
        (Dv.zeroAt θ a : ℂ)).sub (hasDerivAt_id z)).inv hsep
    convert h using 1
    · funext w
      rfl
    · simp
  by_cases hk : k = 0
  · subst k
    simp only [MovingDivisor.normalizedJetTerm, if_neg one_ne_zero,
      MovingDivisor.regularizedTerm, zero_add, one_nsmul]
    convert hbase.sub (hasDerivAt_const (x := z)
      (Dv.zeroAt θ a : ℂ)⁻¹) using 1
    · funext w
      rfl
    · simp
  · have hfun : Dv.normalizedJetTerm θ k a =
        fun w : ℂ =>
          (((Dv.zeroAt θ a : ℂ) - w)⁻¹) ^ (k + 1) := by
      funext w
      simp [MovingDivisor.normalizedJetTerm, hk]
    have hnext :
        Dv.normalizedJetTerm θ (k + 1) a z =
          (((Dv.zeroAt θ a : ℂ) - z)⁻¹) ^ (k + 2) := by
      simp [MovingDivisor.normalizedJetTerm]
    rw [hfun, hnext]
    have hpow := hbase.pow (k + 1)
    convert hpow using 1
    · funext w
      rfl
    · simp only [nsmul_eq_mul, Nat.add_sub_cancel]
      rw [pow_add]
      ring

theorem normalizedJet_hasDerivAt (Dv : MovingDivisor)
    (θ : BoundedRealSequence) (k : ℕ) {z : ℂ} (hz : 0 < z.im) :
    HasCoherentComplexDerivAt
      (Dv.normalizedJet θ k)
      ((k + 1 : ℕ) • Dv.normalizedJet θ (k + 1) z) z := by
  let r : ℝ := z.im / 2
  let u : ℕ → ℝ := fun a =>
    (k + 1 : ℝ) * Dv.localJetMajorant (k + 1) z a
  have hr : 0 < r := half_pos hz
  have hu : Summable u := by
    exact (Dv.summable_localJetMajorant
      (k + 1) hz).mul_left (k + 1 : ℝ)
  have hupper : Metric.ball z r ⊆ upperHalfPlane := by
    intro w hw
    have hdist : ‖w - z‖ < r := by
      simpa only [Metric.mem_ball, dist_eq_norm] using hw
    have himnorm : |(w - z).im| ≤ ‖w - z‖ :=
      Complex.abs_im_le_norm _
    have habs : |w.im - z.im| < r := by
      exact lt_of_le_of_lt (by simpa [Complex.sub_im] using himnorm) hdist
    rw [abs_lt] at habs
    change 0 < w.im
    dsimp only [r] at habs
    linarith
  have hterm : ∀ a w, w ∈ Metric.ball z r →
      HasCoherentComplexDerivAt
        (Dv.normalizedJetTerm θ k a)
        ((k + 1 : ℕ) •
          Dv.normalizedJetTerm θ (k + 1) a w) w := by
    intro a w hw
    exact Dv.normalizedJetTerm_hasDerivAt
      θ k a (hupper hw)
  have hbound : ∀ a w, w ∈ Metric.ball z r →
      ‖(k + 1 : ℕ) •
        Dv.normalizedJetTerm θ (k + 1) a w‖ ≤ u a := by
    intro a w hw
    rw [RCLike.norm_nsmul (K := ℂ), nsmul_eq_mul]
    simpa only [u, Nat.cast_add, Nat.cast_one] using
      mul_le_mul_of_nonneg_left
        (Dv.normalizedJetTerm_norm_le_localMajorant
          (k + 1) a θ hz (by simpa only [r] using hw))
        (Nat.cast_nonneg (k + 1))
  have hmain := hasDerivAt_tsum_of_isPreconnected hu Metric.isOpen_ball
    (convex_ball z r).isPreconnected hterm hbound
    (Metric.mem_ball_self hr)
    (Dv.summable_normalizedJetTerm θ k hz)
    (Metric.mem_ball_self hr)
  convert hmain using 1
  · rfl
  · simp only [MovingDivisor.normalizedJet, nsmul_eq_mul]
    rw [tsum_mul_left]

theorem iteratedDeriv_logDerivativeB_eq_factorial_mul_normalizedJet (Dv : MovingDivisor)
    (θ : BoundedRealSequence) (k : ℕ) {z : ℂ} (hz : 0 < z.im) :
    iteratedDeriv k (Dv.logDerivativeB θ) z =
      (k.factorial : ℂ) * Dv.normalizedJet θ k z := by
  induction k generalizing z with
  | zero =>
      simp [iteratedDeriv_zero, MovingDivisor.logDerivativeB, MovingDivisor.normalizedJet_zero]
  | succ k ih =>
      rw [iteratedDeriv_succ]
      have heq : iteratedDeriv k (Dv.logDerivativeB θ) =ᶠ[𝓝 z]
          fun w => (k.factorial : ℂ) *
            Dv.normalizedJet θ k w := by
        filter_upwards [isOpen_upperHalfPlane.mem_nhds hz] with w hw
        exact ih hw
      rw [heq.deriv_eq]
      have hderiv :=
        (Dv.normalizedJet_hasDerivAt θ k hz).const_mul
          (k.factorial : ℂ)
      rw [hderiv.deriv]
      rw [Nat.factorial_succ]
      push_cast
      simp only [nsmul_eq_mul]
      rw [Nat.cast_add, Nat.cast_one]
      ring

theorem continuousAt_iteratedDeriv_logDerivativeB_joint (Dv : MovingDivisor)
    (k : ℕ) (θ : BoundedRealSequence) {z : ℂ} (hz : 0 < z.im) :
    ContinuousAt
      (fun p : BoundedRealSequence × ℂ =>
        iteratedDeriv k (Dv.logDerivativeB p.1) p.2)
      (θ, z) := by
  have hcont : ContinuousAt
      (fun p : BoundedRealSequence × ℂ =>
        (k.factorial : ℂ) *
          Dv.normalizedJet p.1 k p.2) (θ, z) :=
    continuousAt_const.mul
      (Dv.continuousAt_normalizedJet k θ hz)
  have hupperN :
      {p : BoundedRealSequence × ℂ | p.2 ∈ upperHalfPlane} ∈
        𝓝 (θ, z) :=
    (isOpen_upperHalfPlane.preimage continuous_snd).mem_nhds hz
  apply hcont.congr_of_eventuallyEq
  filter_upwards [hupperN] with p hp
  exact Dv.iteratedDeriv_logDerivativeB_eq_factorial_mul_normalizedJet
    p.1 k hp

def actualJetFamily (Dv : MovingDivisor)
    {H ι : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    [Fintype ι]
    (nodes : H → ι → ℂ) (n : ι → ℕ)
    (p : BoundedRealSequence × H) :
    (Σ i, Fin (n i)) → ℂ :=
  fun s => iteratedDeriv s.2.1
    (Dv.logDerivativeB p.1) (nodes p.2 s.1)

theorem continuousOn_actualJetFamily (Dv : MovingDivisor)
    {H ι : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    [Fintype ι]
    (nodes : H → ι → ℂ) (hnodes : Continuous nodes)
    (n : ι → ℕ) (U : Set H)
    (hupper : ∀ h ∈ U, ∀ i, 0 < (nodes h i).im) :
    ContinuousOn
      (Dv.actualJetFamily nodes n)
      (Set.univ ×ˢ U) := by
  apply continuousOn_pi'
  intro s p hp
  have hinner : ContinuousAt
      (fun q : BoundedRealSequence × H =>
        (q.1, nodes q.2 s.1)) p :=
    continuousAt_fst.prodMk
      ((continuous_apply s.1).comp
        (hnodes.comp continuous_snd)).continuousAt
  exact (Dv.continuousAt_iteratedDeriv_logDerivativeB_joint
    s.2.1 p.1 (hupper p.2 hp.2 s.1)).comp
      (f := fun q : BoundedRealSequence × H =>
        (q.1, nodes q.2 s.1)) hinner |>.continuousWithinAt

def expandedActualJetFamily (Dv : MovingDivisor)
    {H row ι : Type*}
    [NormedAddCommGroup H] [NormedSpace ℝ H]
    [Fintype row] [Fintype ι]
    (orders : ι → ℕ) (nodes : H → row × ι → ℂ)
    (p : BoundedRealSequence × H) :
    row × Fin (Fintype.card (Σ i, Fin (orders i))) → ℂ :=
  reshapeCombinedJetsFinCLM row ι orders
    (Dv.actualJetFamily nodes
      (fun x : row × ι => orders x.2) p)

theorem continuousOn_expandedActualJetFamily (Dv : MovingDivisor)
    {H row ι : Type*}
    [NormedAddCommGroup H] [NormedSpace ℝ H]
    [Fintype row] [Fintype ι]
    (orders : ι → ℕ) (nodes : H → row × ι → ℂ)
    (hnodes : Continuous nodes) (U : Set H)
    (hupper : ∀ h ∈ U, ∀ x, 0 < (nodes h x).im) :
    ContinuousOn
      (Dv.expandedActualJetFamily orders nodes)
      (Set.univ ×ˢ U) :=
  (reshapeCombinedJetsFinCLM row ι orders).continuous.comp_continuousOn
    (Dv.continuousOn_actualJetFamily
      nodes hnodes (fun x : row × ι => orders x.2) U hupper)

def finiteJointJetFamily (Dv : MovingDivisor)
    {H ι : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    [Fintype ι]
    (nodes : H → ι → ℂ) (n : ι → ℕ) (θ : BoundedRealSequence)
    (p : (Fin (movingCanonicalLocationProbeCard n) → ℝ) × H) :
    (Σ i, Fin (n i)) → ℂ :=
  Dv.finiteActualJetFamily (nodes p.2) n θ p.1

def finiteJointJetSmoothModel (Dv : MovingDivisor)
    {H ι : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    [Fintype ι]
    (nodes : H → ι → ℂ) (n : ι → ℕ) (θ : BoundedRealSequence)
    (p : (Fin (movingCanonicalLocationProbeCard n) → ℝ) × H) :
    (Σ i, Fin (n i)) → ℂ :=
  fun s =>
    iteratedDeriv s.2.1 (Dv.logDerivativeB θ) (nodes p.2 s.1) +
      ∑ a : Fin (movingCanonicalLocationProbeCard n),
        (Dv.differentialJetTerm
            (movingCanonicalFiniteChart
              (movingCanonicalLocationProbeCard n) θ p.1)
            s.2.1 a.1 (nodes p.2 s.1) -
          Dv.differentialJetTerm
            θ s.2.1 a.1 (nodes p.2 s.1))

theorem finiteJointJetFamily_eq_smoothModel (Dv : MovingDivisor)
    {H ι : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    [Fintype ι]
    (nodes : H → ι → ℂ) (n : ι → ℕ) (θ : BoundedRealSequence)
    (p : (Fin (movingCanonicalLocationProbeCard n) → ℝ) × H)
    (hupper : ∀ i, 0 < (nodes p.2 i).im) :
    Dv.finiteJointJetFamily nodes n θ p =
      Dv.finiteJointJetSmoothModel nodes n θ p := by
  funext s
  exact Dv.iteratedDeriv_logDerivative_finiteChart
    (movingCanonicalLocationProbeCard n) θ p.1 s.2.1 (hupper s.1)

theorem contDiffOn_finiteJointJetSmoothModel (Dv : MovingDivisor)
    {H ι : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    [Fintype ι]
    (nodes : H → ι → ℂ) (hnodes : ContDiff ℝ ⊤ nodes)
    (n : ι → ℕ) (θ : BoundedRealSequence)
    (U : Set H) (hupper : ∀ h ∈ U, ∀ i, 0 < (nodes h i).im) :
    ContDiffOn ℝ ⊤
      (Dv.finiteJointJetSmoothModel nodes n θ)
      (Set.univ ×ˢ U) := by
  apply contDiffOn_pi'
  intro s p hp
  have hpU : p.2 ∈ U := hp.2
  have hnode : ContDiff ℝ ⊤
      (fun q :
        (Fin (movingCanonicalLocationProbeCard n) → ℝ) × H =>
        nodes q.2 s.1) :=
    (contDiff_apply ℝ ℂ s.1).comp (hnodes.comp contDiff_snd)
  have hbase : ContDiffAt ℝ ⊤
      (fun q :
        (Fin (movingCanonicalLocationProbeCard n) → ℝ) × H =>
        iteratedDeriv s.2.1 (Dv.logDerivativeB θ)
          (nodes q.2 s.1)) p := by
    exact ((Dv.analyticAt_iteratedDeriv_logDerivative
      θ s.2.1 (hupper p.2 hpU s.1)).restrictScalars.contDiffAt).comp
        p hnode.contDiffAt
  have hterm : ∀ a : Fin (movingCanonicalLocationProbeCard n),
      ContDiffAt ℝ ⊤
        (fun q :
          (Fin (movingCanonicalLocationProbeCard n) → ℝ) × H =>
          Dv.differentialJetTerm
              (movingCanonicalFiniteChart
                (movingCanonicalLocationProbeCard n) θ q.1)
              s.2.1 a.1 (nodes q.2 s.1) -
            Dv.differentialJetTerm
              θ s.2.1 a.1 (nodes q.2 s.1)) p := by
    intro a
    have hzero : ContDiff ℝ ⊤
        (fun q :
          (Fin (movingCanonicalLocationProbeCard n) → ℝ) × H =>
          (Dv.zeroAt (movingCanonicalFiniteChart (movingCanonicalLocationProbeCard n) θ q.1) a.1 : ℂ)) :=
      (Dv.contDiff_zeroAt_finiteChart_ofReal
        (movingCanonicalLocationProbeCard n) θ a).comp contDiff_fst
    have hsepNew :
        (Dv.zeroAt (movingCanonicalFiniteChart (movingCanonicalLocationProbeCard n) θ p.1) a.1 : ℂ) -
            nodes p.2 s.1 ≠ 0 := by
      intro h
      have him := congrArg Complex.im h
      simp at him
      exact (ne_of_gt (hupper p.2 hpU s.1)) him
    have hzeroNew :
        (Dv.zeroAt (movingCanonicalFiniteChart (movingCanonicalLocationProbeCard n) θ p.1) a.1 : ℂ) ≠ 0 :=
      Complex.ofReal_ne_zero.mpr
        (ne_of_gt (Dv.zeroAt_pos (movingCanonicalFiniteChart (movingCanonicalLocationProbeCard n) θ p.1) a.1))
    have hsepOld :
        (Dv.zeroAt θ a.1 : ℂ) - nodes p.2 s.1 ≠ 0 := by
      intro h
      have him := congrArg Complex.im h
      simp at him
      exact (ne_of_gt (hupper p.2 hpU s.1)) him
    have hzeroOld : (Dv.zeroAt θ a.1 : ℂ) ≠ 0 :=
      Complex.ofReal_ne_zero.mpr
        (ne_of_gt (Dv.zeroAt_pos θ a.1))
    unfold MovingDivisor.differentialJetTerm
    by_cases hk : s.2.1 = 0
    · simp only [if_pos hk, MovingDivisor.regularizedTerm]
      have hnewReg :=
        ((hzero.contDiffAt.sub hnode.contDiffAt).inv hsepNew).sub
          (hzero.contDiffAt.inv hzeroNew)
      have holdZero : ContDiffAt ℝ ⊤
          (fun _ :
            (Fin (movingCanonicalLocationProbeCard n) → ℝ) × H =>
            (Dv.zeroAt θ a.1 : ℂ)) p :=
        contDiffAt_const
      have holdReg :=
        ((holdZero.sub hnode.contDiffAt).inv hsepOld).sub
          (holdZero.inv hzeroOld)
      exact hnewReg.sub holdReg
    · simp only [if_neg hk]
      have hnewPow :=
        ((hzero.contDiffAt.sub hnode.contDiffAt).inv hsepNew).pow
          (s.2.1 + 1)
      have holdZero : ContDiffAt ℝ ⊤
          (fun _ :
            (Fin (movingCanonicalLocationProbeCard n) → ℝ) × H =>
            (Dv.zeroAt θ a.1 : ℂ)) p :=
        contDiffAt_const
      have holdPow :=
        ((holdZero.sub hnode.contDiffAt).inv hsepOld).pow
          (s.2.1 + 1)
      exact (contDiffAt_const.mul hnewPow).sub
        (contDiffAt_const.mul holdPow)
  exact (hbase.add
    (ContDiffAt.sum (s := Finset.univ) (fun a _ => hterm a))).contDiffWithinAt

theorem contDiffOn_finiteJointJetFamily (Dv : MovingDivisor)
    {H ι : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    [Fintype ι]
    (nodes : H → ι → ℂ) (hnodes : ContDiff ℝ ⊤ nodes)
    (n : ι → ℕ) (θ : BoundedRealSequence)
    (U : Set H) (hupper : ∀ h ∈ U, ∀ i, 0 < (nodes h i).im) :
    ContDiffOn ℝ ⊤
      (Dv.finiteJointJetFamily nodes n θ)
      (Set.univ ×ˢ U) := by
  apply (Dv.contDiffOn_finiteJointJetSmoothModel
    nodes hnodes n θ U hupper).congr
  intro p hp
  exact Dv.finiteJointJetFamily_eq_smoothModel
    nodes n θ p (hupper p.2 hp.2)

def expandedJetFamily (Dv : MovingDivisor)
    {H row ι : Type*}
    [NormedAddCommGroup H] [NormedSpace ℝ H]
    [Fintype row] [Fintype ι]
    (orders : ι → ℕ) (nodes : H → row × ι → ℂ)
    (θ : BoundedRealSequence)
    (p :
      (Fin (movingCanonicalLocationProbeCard
        (fun x : row × ι => orders x.2)) → ℝ) × H) :
    row × Fin (Fintype.card (Σ i, Fin (orders i))) → ℂ :=
  reshapeCombinedJetsFinCLM row ι orders
    (Dv.finiteJointJetFamily nodes
      (fun x : row × ι => orders x.2) θ p)

theorem contDiffOn_expandedJetFamily (Dv : MovingDivisor)
    {H row ι : Type*}
    [NormedAddCommGroup H] [NormedSpace ℝ H]
    [Fintype row] [Fintype ι]
    (orders : ι → ℕ) (nodes : H → row × ι → ℂ)
    (hnodes : ContDiff ℝ ⊤ nodes)
    (θ : BoundedRealSequence) (U : Set H)
    (hupper : ∀ h ∈ U, ∀ x, 0 < (nodes h x).im) :
    ContDiffOn ℝ ⊤
      (Dv.expandedJetFamily orders nodes θ)
      (Set.univ ×ˢ U) := by
  exact (reshapeCombinedJetsFinCLM row ι orders).contDiff.comp_contDiffOn
    (Dv.contDiffOn_finiteJointJetFamily
      nodes hnodes (fun x : row × ι => orders x.2) θ U hupper)

theorem fderiv_expandedJetFamily_probe_surjective (Dv : MovingDivisor)
    {H row ι : Type*}
    [NormedAddCommGroup H] [NormedSpace ℝ H]
    [Fintype row] [Fintype ι]
    [DecidableEq row] [DecidableEq ι]
    (orders : ι → ℕ) (nodes : H → row × ι → ℂ)
    (θ : BoundedRealSequence)
    (p : Fin (movingCanonicalLocationProbeCard
      (fun x : row × ι => orders x.2)) → ℝ)
    (h : H) (hinj : Function.Injective (nodes h))
    (hupper : ∀ x, 0 < (nodes h x).im) :
    Function.Surjective
      (fderiv ℝ
        (fun v => Dv.expandedJetFamily
          orders nodes θ (v, h)) p) := by
  let nodeOrders : row × ι → ℕ := fun x => orders x.2
  have hactual :=
    Dv.finiteActualJetFamily_hasFDerivAt
      (nodes h) hupper nodeOrders θ p
  have hreshape : HasNormedFDerivAt
      (reshapeCombinedJetsFinCLM row ι orders)
      (reshapeCombinedJetsFinCLM row ι orders)
      (Dv.finiteActualJetFamily (nodes h) nodeOrders θ p) :=
    (reshapeCombinedJetsFinCLM row ι orders).hasFDerivAt
  have hcomp := hreshape.comp p hactual
  have hfun :
      (fun v => Dv.expandedJetFamily
        orders nodes θ (v, h)) =
        (reshapeCombinedJetsFinCLM row ι orders) ∘
          Dv.finiteActualJetFamily (nodes h) nodeOrders θ := by
    funext v
    rfl
  have hderiv :
      fderiv ℝ
        (fun v => Dv.expandedJetFamily
          orders nodes θ (v, h)) p =
        (reshapeCombinedJetsFinCLM row ι orders).comp
          (Dv.finiteParameterJetCLM (nodes h) nodeOrders
            (movingCanonicalFiniteChart
              (movingCanonicalLocationProbeCard nodeOrders) θ p)) := by
    rw [hfun]
    exact hcomp.fderiv
  rw [hderiv]
  exact (reshapeCombinedJetsFinCLM_surjective row ι orders).comp
    (Dv.finiteParameterJetCLM_surjective
      (nodes h) hinj hupper nodeOrders
        (movingCanonicalFiniteChart
          (movingCanonicalLocationProbeCard nodeOrders) θ p))

theorem compact_expandedEvaluation_avoidance_dense (Dv : MovingDivisor)
    {H row κ ι : Type}
    [NormedAddCommGroup H] [NormedSpace ℝ H] [FiniteDimensional ℝ H]
    [Fintype row] [DecidableEq row]
    [Fintype κ] [DecidableEq κ]
    [Fintype ι] [DecidableEq ι]
    (degree : ℕ) (orders : ι → ℕ)
    (z : row → ℂ) (hz : Function.Injective z)
    (exponent :
      κ → (Fin (Fintype.card (Σ i, Fin (orders i))) →₀ ℕ))
    (hexponent : Function.Injective exponent)
    (hrows : Fintype.card (κ × Fin (degree + 1)) + degree <
      Fintype.card row)
    (nodes : H → row × ι → ℂ) (hnodes : ContDiff ℝ ⊤ nodes)
    (U K : Set H) (hU : IsOpen U) (hKU : K ⊆ U)
    (hinj : ∀ h ∈ U, Function.Injective (nodes h))
    (hupper : ∀ h ∈ U, ∀ x, 0 < (nodes h x).im)
    (θ : BoundedRealSequence)
    (hdim : Module.finrank ℝ H <
      2 * (Fintype.card row -
        Fintype.card (κ × Fin (degree + 1)) - degree + 1)) :
    Dense
      (compactConfigurationAvoidance
        (Dv.expandedJetFamily orders nodes θ)
        (expandedDifferentialEvaluationRankDefect degree
          (Fintype.card (Σ i, Fin (orders i))) z exponent)
        K) := by
  apply expandedEvaluation_compactPatchAvoidance_dense
    degree (Fintype.card (Σ i, Fin (orders i)))
      z hz exponent hexponent hrows
      (Dv.expandedJetFamily orders nodes θ)
      U K hU hKU
  · exact Dv.contDiffOn_expandedJetFamily
      orders nodes hnodes θ U hupper
  · intro p h hh
    exact Dv.fderiv_expandedJetFamily_probe_surjective
      orders nodes θ p h (hinj h hh) (hupper h hh)
  · exact hdim

@[simp]
theorem finiteChartB_zero
    (D : ℕ) (θ : BoundedRealSequence) :
    movingCanonicalFiniteChart D θ 0 = θ := by
  ext a
  simp [movingCanonicalFiniteChart]

theorem compact_expandedActualEvaluation_avoidance_dense (Dv : MovingDivisor)
    {H row κ ι : Type}
    [NormedAddCommGroup H] [NormedSpace ℝ H] [FiniteDimensional ℝ H]
    [Fintype row] [DecidableEq row]
    [Fintype κ] [DecidableEq κ]
    [Fintype ι] [DecidableEq ι]
    (degree : ℕ) (orders : ι → ℕ)
    (z : row → ℂ) (hz : Function.Injective z)
    (exponent :
      κ → (Fin (Fintype.card (Σ i, Fin (orders i))) →₀ ℕ))
    (hexponent : Function.Injective exponent)
    (hrows : Fintype.card (κ × Fin (degree + 1)) + degree <
      Fintype.card row)
    (nodes : H → row × ι → ℂ) (hnodes : ContDiff ℝ ⊤ nodes)
    (U K : Set H) (hU : IsOpen U) (hKU : K ⊆ U)
    (hinj : ∀ h ∈ U, Function.Injective (nodes h))
    (hupper : ∀ h ∈ U, ∀ x, 0 < (nodes h x).im)
    (hdim : Module.finrank ℝ H <
      2 * (Fintype.card row -
        Fintype.card (κ × Fin (degree + 1)) - degree + 1)) :
    Dense
      (compactConfigurationAvoidance
        (Dv.expandedActualJetFamily orders nodes)
        (expandedDifferentialEvaluationRankDefect degree
          (Fintype.card (Σ i, Fin (orders i))) z exponent)
        K) := by
  rw [dense_iff_closure_eq]
  apply Set.eq_univ_of_forall
  intro θ
  rw [mem_closure_iff]
  intro V hVopen hθV
  let D := movingCanonicalLocationProbeCard
    (fun x : row × ι => orders x.2)
  let chart : (Fin D → ℝ) → BoundedRealSequence :=
    movingCanonicalFiniteChart D θ
  have hchart : Continuous chart := by
    exact (contDiff_movingCanonicalFiniteChart D θ).continuous
  have hchartZero : chart 0 = θ := by
    exact finiteChartB_zero D θ
  have hpreOpen : IsOpen (chart ⁻¹' V) :=
    hVopen.preimage hchart
  have hpreNonempty : (chart ⁻¹' V).Nonempty := by
    exact ⟨0, by simpa [hchartZero] using hθV⟩
  have hdenseFinite :=
    Dv.compact_expandedEvaluation_avoidance_dense
      degree orders z hz exponent hexponent hrows nodes hnodes
      U K hU hKU hinj hupper θ hdim
  obtain ⟨p, hpgood, hpV⟩ :=
    hdenseFinite.exists_mem_open hpreOpen hpreNonempty
  refine ⟨chart p, hpV, ?_⟩
  intro h hh
  exact hpgood h hh

def expandedPacketValue (Dv : MovingDivisor)
    {row ι : Type} [Fintype row] [DecidableEq row]
    [Fintype ι] [DecidableEq ι]
    (orders : ι → ℕ) (packet : InjectiveProjectiveRowPacket row)
    (θ : BoundedRealSequence) (shift : InjectiveShiftConfiguration ι) :
    row × Fin (Fintype.card (Σ i, Fin (orders i))) → ℂ :=
  reshapeCombinedJetsFinCLM row ι orders
    (Dv.actualJetFamily
      (fun _ : Unit =>
        combinedProjectiveRowShiftPacket packet shift)
      (fun x : row × ι => orders x.2) (θ, ()))

def expandedFullRankWitness (Dv : MovingDivisor)
    {row κ ι : Type}
    [Fintype row] [DecidableEq row]
    [Fintype κ] [Fintype ι] [DecidableEq ι]
    (degree : ℕ) (orders : ι → ℕ)
    (exponent :
      κ → (Fin (Fintype.card (Σ i, Fin (orders i))) →₀ ℕ))
    (θ : BoundedRealSequence)
    (shift : InjectiveShiftConfiguration ι) : Prop :=
  ∃ packet : InjectiveProjectiveRowPacket row,
    Function.Injective (combinedProjectiveRowShiftPacket packet shift) ∧
      (∀ x, 0 < (combinedProjectiveRowShiftPacket packet shift x).im) ∧
      Function.Injective
        (expandedDifferentialEvaluationMatrix degree
          (Fintype.card (Σ i, Fin (orders i))) packet.1 exponent
          (Dv.expandedPacketValue orders packet θ shift)).mulVec

def expandedPatternRelationHolds (Dv : MovingDivisor)
    {row κ ι : Type}
    [Fintype row] [DecidableEq row]
    [Fintype κ] [Fintype ι] [DecidableEq ι]
    (degree : ℕ) (orders : ι → ℕ)
    (exponent :
      κ → (Fin (Fintype.card (Σ i, Fin (orders i))) →₀ ℕ))
    (θ : BoundedRealSequence)
    (shift : InjectiveShiftConfiguration ι)
    (coeff : κ × Fin (degree + 1) → ℂ) : Prop :=
  ∀ packet : InjectiveProjectiveRowPacket row,
    Function.Injective (combinedProjectiveRowShiftPacket packet shift) →
    (∀ x, 0 < (combinedProjectiveRowShiftPacket packet shift x).im) →
    ∀ r, ∑ col, coeff col *
      expandedDifferentialEvaluationMatrix degree
        (Fintype.card (Σ i, Fin (orders i))) packet.1 exponent
        (Dv.expandedPacketValue orders packet θ shift) r col = 0

theorem expandedPatternRelation_coefficients_eq_zero_of_fullRankWitness (Dv : MovingDivisor)
    {row κ ι : Type}
    [Fintype row] [DecidableEq row]
    [Fintype κ] [DecidableEq κ]
    [Fintype ι] [DecidableEq ι]
    (degree : ℕ) (orders : ι → ℕ)
    (exponent :
      κ → (Fin (Fintype.card (Σ i, Fin (orders i))) →₀ ℕ))
    (θ : BoundedRealSequence)
    (shift : InjectiveShiftConfiguration ι)
    (hwitness : Dv.expandedFullRankWitness
      (row := row) (κ := κ) degree orders exponent θ shift)
    (coeff : κ × Fin (degree + 1) → ℂ)
    (hrelation : Dv.expandedPatternRelationHolds
      (row := row) degree orders exponent θ shift coeff) :
    ∀ col, coeff col = 0 := by
  obtain ⟨packet, hinjNodes, hupper, hinjective⟩ := hwitness
  let A := expandedDifferentialEvaluationMatrix degree
    (Fintype.card (Σ i, Fin (orders i))) packet.1 exponent
    (Dv.expandedPacketValue orders packet θ shift)
  have hmul : A.mulVec coeff = 0 := by
    funext r
    simpa [A, Matrix.mulVec, dotProduct, mul_comm] using
      hrelation packet hinjNodes hupper r
  have hcoeff : coeff = 0 := hinjective (by simpa [A] using hmul)
  intro col
  exact congrFun hcoeff col

theorem compact_injectiveShiftPatch_has_dense_completeAtlas (Dv : MovingDivisor)
    {row κ ι : Type}
    [Fintype row] [DecidableEq row]
    [Fintype κ] [DecidableEq κ]
    [Fintype ι] [DecidableEq ι]
    (degree : ℕ) (orders : ι → ℕ)
    (exponent :
      κ → (Fin (Fintype.card (Σ i, Fin (orders i))) →₀ ℕ))
    (hexponent : Function.Injective exponent)
    (hrows : Fintype.card (κ × Fin (degree + 1)) + degree <
      Fintype.card row)
    (Kshift : Set (InjectiveShiftConfiguration ι))
    (hKshift : IsCompact Kshift)
    (hdim : Module.finrank ℝ (ι → ℂ) <
      2 * (Fintype.card row -
        Fintype.card (κ × Fin (degree + 1)) - degree + 1)) :
    ∃ n : ℕ, ∃ packets : Fin n → InjectiveProjectiveRowPacket row,
      ∃ pieces : Fin n → Set (InjectiveShiftConfiguration ι),
        Kshift ⊆ ⋃ j, pieces j ∧
        (∀ j, IsCompact (pieces j)) ∧
        (∀ j, pieces j ⊆
          cauchyUpperGoodCombinedRowPacketSet (packets j)) ∧
        let ambientPiece := fun j =>
          ambientImageOfInjectiveShiftPiece (pieces j)
        let family := fun j =>
          Dv.expandedActualJetFamily orders
            (fun h x => (packets j).1 x.1 + h x.2)
        let good := fun j => compactConfigurationAvoidance (family j)
          (expandedDifferentialEvaluationRankDefect degree
            (Fintype.card (Σ i, Fin (orders i)))
            (packets j).1 exponent)
          (ambientPiece j)
        Dense (⋂ j, good j) ∧ IsOpen (⋂ j, good j) ∧
          ∀ θ ∈ ⋂ j, good j, ∀ shift ∈ Kshift,
            Dv.expandedFullRankWitness
              (row := row) (κ := κ)
              degree orders exponent θ shift := by
  classical
  obtain ⟨n, packets, pieces, hcover, hpiecesCompact, hpiecesChart⟩ :=
    compact_injectiveShiftPatch_finite_cauchyUpperGoodCombinedRowPacket_refinement
      (row := row) hKshift
  let ambientPiece : Fin n → Set (ι → ℂ) := fun j =>
    ambientImageOfInjectiveShiftPiece (pieces j)
  let nodes : Fin n → (ι → ℂ) → (row × ι → ℂ) := fun j h x =>
    (packets j).1 x.1 + h x.2
  let family := fun j =>
    Dv.expandedActualJetFamily orders (nodes j)
  let good := fun j => compactConfigurationAvoidance (family j)
    (expandedDifferentialEvaluationRankDefect degree
      (Fintype.card (Σ i, Fin (orders i))) (packets j).1 exponent)
    (ambientPiece j)
  have hgood : ∀ j, Dense (good j) ∧ IsOpen (good j) := by
    intro j
    let Uj : Set (ι → ℂ) :=
      cauchyUpperGoodCombinedRowPacketAmbientSet (packets j)
    have hUj : IsOpen Uj :=
      cauchyUpperGoodCombinedRowPacketAmbientSet_isOpen (packets j)
    have hKj : IsCompact (ambientPiece j) :=
      (hpiecesCompact j).image continuous_subtype_val
    have hKjUj : ambientPiece j ⊆ Uj := by
      rintro shift ⟨shiftCfg, hpiece, rfl⟩
      exact hpiecesChart j hpiece
    have hnodes : ContDiff ℝ ⊤ (nodes j) := by
      rw [contDiff_pi]
      intro x
      exact contDiff_const.add (contDiff_apply ℝ ℂ x.2)
    have hdenseRaw :=
      Dv.compact_expandedActualEvaluation_avoidance_dense
        degree orders (packets j).1 (packets j).2
        exponent hexponent hrows
        (nodes j) hnodes Uj (ambientPiece j)
        hUj hKjUj
        (fun h hh => hh.1)
        (fun h hh x => hh.2 x)
        hdim
    have hdense : Dense (good j) := by
      simpa only [good, family] using hdenseRaw
    have hfamilyOn : ContinuousOn (family j) (Set.univ ×ˢ Uj) := by
      exact Dv.continuousOn_expandedActualJetFamily
        orders (nodes j) hnodes.continuous Uj
          (fun h hh x => hh.2 x)
    have hopenRaw :=
      compactConfigurationAvoidance_isOpen_of_continuousOn_open
        (family j)
        (expandedDifferentialEvaluationRankDefect degree
          (Fintype.card (Σ i, Fin (orders i)))
          (packets j).1 exponent)
        (expandedDifferentialEvaluationRankDefect_isClosed degree
          (Fintype.card (Σ i, Fin (orders i)))
          (packets j).1 exponent)
        Uj hUj hfamilyOn (ambientPiece j) hKj hKjUj
    have hopen : IsOpen (good j) := by
      simpa only [good] using hopenRaw
    exact ⟨hdense, hopen⟩
  refine ⟨n, packets, pieces, hcover, hpiecesCompact, hpiecesChart,
    ?_, ?_, ?_⟩
  · exact dense_iInter_of_finite_isOpen good
      (fun j => (hgood j).2) (fun j => (hgood j).1)
  · exact isOpen_iInter_of_finite (fun j => (hgood j).2)
  · intro θ hθ shift hshift
    obtain ⟨j, hjpiece⟩ := Set.mem_iUnion.mp (hcover hshift)
    have hjchart := hpiecesChart j hjpiece
    refine ⟨packets j, hjchart.1, hjchart.2, ?_⟩
    have hjgood := Set.mem_iInter.mp hθ j
    have hambient : shift.1 ∈ ambientPiece j :=
      ⟨shift, hjpiece, rfl⟩
    have havoid := hjgood shift.1 hambient
    have hinjective : Function.Injective
        (expandedDifferentialEvaluationMatrix degree
          (Fintype.card (Σ i, Fin (orders i)))
          (packets j).1 exponent
          (family j (θ, shift.1))).mulVec := by
      simpa only [mem_expandedDifferentialEvaluationRankDefect_iff,
        not_not] using havoid
    change Function.Injective
      (expandedDifferentialEvaluationMatrix degree
        (Fintype.card (Σ i, Fin (orders i)))
        (packets j).1 exponent
        (family j (θ, shift.1))).mulVec
    exact hinjective

theorem global_injectiveShifts_expandedFullRankWitness_dense_residual (Dv : MovingDivisor)
    {row κ ι : Type}
    [Fintype row] [DecidableEq row]
    [Fintype κ] [DecidableEq κ]
    [Fintype ι] [DecidableEq ι]
    (degree : ℕ) (orders : ι → ℕ)
    (exponent :
      κ → (Fin (Fintype.card (Σ i, Fin (orders i))) →₀ ℕ))
    (hexponent : Function.Injective exponent)
    (hrows : Fintype.card (κ × Fin (degree + 1)) + degree <
      Fintype.card row)
    (hdim : Module.finrank ℝ (ι → ℂ) <
      2 * (Fintype.card row -
        Fintype.card (κ × Fin (degree + 1)) - degree + 1)) :
    let good : Set BoundedRealSequence := {θ |
      ∀ shift : InjectiveShiftConfiguration ι,
        Dv.expandedFullRankWitness
          (row := row) (κ := κ)
          degree orders exponent θ shift}
    Dense good ∧ good ∈ residual BoundedRealSequence := by
  dsimp only
  letI : BaireSpace BoundedRealSequence := by infer_instance
  apply globalWitness_dense_residual_of_sigmaCompact
    (fun θ (shift : InjectiveShiftConfiguration ι) =>
      Dv.expandedFullRankWitness
        (row := row) (κ := κ)
        degree orders exponent θ shift)
  intro Kshift hKshift
  obtain ⟨n, packets, pieces, hcover, hpiecesCompact, hpiecesChart,
      hDense, hOpen, hWitness⟩ :=
    Dv.compact_injectiveShiftPatch_has_dense_completeAtlas
      degree orders exponent hexponent hrows Kshift hKshift hdim
  exact ⟨_, hOpen, hDense, hWitness⟩

theorem allFinitePatterns_expandedFullRankWitness_dense_residual (Dv : MovingDivisor)
    {Γ : Type} [Countable Γ] :
    let fullRank : Set BoundedRealSequence := {θ |
      ∀ (p : FiniteDifferentialPattern Γ)
        (shift : InjectiveShiftConfiguration (CarrierPatternShift p)),
        Dv.expandedFullRankWitness
          (row := CarrierPatternRow p)
          (κ := CarrierPatternMonomial p)
          p.coefficientDegree p.orders
          (carrierPatternExponent p) θ shift}
    Dense fullRank ∧ fullRank ∈ residual BoundedRealSequence := by
  dsimp only
  letI : BaireSpace BoundedRealSequence := by infer_instance
  let goodPattern :
      FiniteDifferentialPattern Γ → Set BoundedRealSequence := fun p =>
    {θ | ∀ shift : InjectiveShiftConfiguration (CarrierPatternShift p),
      Dv.expandedFullRankWitness
        (row := CarrierPatternRow p)
        (κ := CarrierPatternMonomial p)
        p.coefficientDegree p.orders
        (carrierPatternExponent p) θ shift}
  have hgoodPattern : ∀ p : FiniteDifferentialPattern Γ,
      Dense (goodPattern p) ∧
        goodPattern p ∈ residual BoundedRealSequence := by
    intro p
    have hsource :=
      Dv.global_injectiveShifts_expandedFullRankWitness_dense_residual
        (row := CarrierPatternRow p)
        (κ := CarrierPatternMonomial p)
        (ι := CarrierPatternShift p)
        p.coefficientDegree p.orders
        (carrierPatternExponent p)
        (carrierPatternExponent_injective p)
        (carrierPattern_rows_strictly_dominate_columns p)
        (carrierPattern_shift_dimension_below_codimension p)
    change Dense (goodPattern p) ∧
      goodPattern p ∈ residual BoundedRealSequence at hsource
    exact hsource
  have hresidual : (⋂ p, goodPattern p) ∈
      residual BoundedRealSequence :=
    countable_iInter_mem.mpr fun p => (hgoodPattern p).2
  have heq : (⋂ p, goodPattern p) =
      {θ | ∀ (p : FiniteDifferentialPattern Γ)
        (shift : InjectiveShiftConfiguration (CarrierPatternShift p)),
        Dv.expandedFullRankWitness
          (row := CarrierPatternRow p)
          (κ := CarrierPatternMonomial p)
          p.coefficientDegree p.orders
          (carrierPatternExponent p) θ shift} := by
    ext θ
    simp only [Set.mem_iInter, goodPattern, Set.mem_setOf_eq]
  rw [heq] at hresidual
  exact ⟨dense_of_mem_residual hresidual, hresidual⟩

theorem allFinitePatterns_expandedRelationFree_dense_residual (Dv : MovingDivisor)
    {Γ : Type} [Countable Γ] :
    let relationFree : Set BoundedRealSequence := {θ |
      ∀ (p : FiniteDifferentialPattern Γ)
        (shift : InjectiveShiftConfiguration (CarrierPatternShift p))
        (coeff :
          CarrierPatternMonomial p × Fin (p.coefficientDegree + 1) → ℂ),
        Dv.expandedPatternRelationHolds
          (row := CarrierPatternRow p)
          p.coefficientDegree p.orders
          (carrierPatternExponent p) θ shift coeff →
        ∀ col, coeff col = 0}
    Dense relationFree ∧
      relationFree ∈ residual BoundedRealSequence := by
  dsimp only
  let fullRank : Set BoundedRealSequence := {θ |
    ∀ (p : FiniteDifferentialPattern Γ)
      (shift : InjectiveShiftConfiguration (CarrierPatternShift p)),
      Dv.expandedFullRankWitness
        (row := CarrierPatternRow p)
        (κ := CarrierPatternMonomial p)
        p.coefficientDegree p.orders
        (carrierPatternExponent p) θ shift}
  let relationFree : Set BoundedRealSequence := {θ |
    ∀ (p : FiniteDifferentialPattern Γ)
      (shift : InjectiveShiftConfiguration (CarrierPatternShift p))
      (coeff :
        CarrierPatternMonomial p × Fin (p.coefficientDegree + 1) → ℂ),
      Dv.expandedPatternRelationHolds
        (row := CarrierPatternRow p)
        p.coefficientDegree p.orders
        (carrierPatternExponent p) θ shift coeff →
      ∀ col, coeff col = 0}
  have hfull : Dense fullRank ∧
      fullRank ∈ residual BoundedRealSequence := by
    simpa only [fullRank] using
      (Dv.allFinitePatterns_expandedFullRankWitness_dense_residual
        (Γ := Γ))
  have hsubset : fullRank ⊆ relationFree := by
    intro θ hθ p shift coeff hrelation
    exact
      Dv.expandedPatternRelation_coefficients_eq_zero_of_fullRankWitness
        p.coefficientDegree p.orders
        (carrierPatternExponent p) θ shift
        (hθ p shift) coeff hrelation
  exact ⟨hfull.1.mono hsubset,
    Filter.mem_of_superset hfull.2 hsubset⟩

end MovingDivisor

end

end GaloisForLFunctions.HTGeometry
