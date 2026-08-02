import GaloisForLFunctions.HTGeometry.MovingCanonicalFiniteJetProbe
import GaloisForLFunctions.HTGeometry.DiscreteCauchyJetDerivatives
import GaloisForLFunctions.HTGeometry.ExpandedEvaluationCompactPatchDensity

/-!
# Finite moving-canonical jet submersions

This module connects actual derivatives of the regularized canonical logarithmic derivative to
the exact finite Cauchy probe. It supplies a smooth finite chart, computes its Fréchet derivative,
and proves that derivative surjective at every parameter.
-/

namespace GaloisForLFunctions.HTGeometry

open Set Topology Filter
open scoped ENNReal

noncomputable section

/-- Coherent normed-space specialization of `HasFDerivAt`. -/
abbrev HasNormedFDerivAt
    {E F : Type*} [nE : NormedAddCommGroup E] [sE : NormedSpace ℝ E]
    [nF : NormedAddCommGroup F] [sF : NormedSpace ℝ F]
    (f : E → F) (f' : E →L[ℝ] F) (x : E) : Prop :=
  @HasFDerivAt ℝ inferInstance E
    nE.toAddCommGroup
    sE.toModule
    nE.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace
    F
    nF.toAddCommGroup
    sF.toModule
    nF.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace
    f f' x

def movingCanonicalFinitePerturbation
    (D : ℕ) : (Fin D → ℝ) →ₗ[ℝ] BoundedRealSequence where
  toFun p := ∑ a : Fin D, lp.single ∞ a.1 (p a)
  map_add' p q := by
    ext n
    simp [Finset.sum_add_distrib]
  map_smul' r p := by
    ext n
    simp only [lp.coeFn_sum, Finset.sum_apply, lp.single_apply,
      Pi.single_apply, lp.coeFn_smul, Pi.smul_apply, RingHom.id_apply,
      smul_eq_mul]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro a ha
    by_cases han : n = a.1 <;> simp [han]

@[simp]
theorem movingCanonicalFinitePerturbation_apply
    (D : ℕ) (p : Fin D → ℝ) (n : ℕ) :
    movingCanonicalFinitePerturbation D p n =
      if h : n < D then p ⟨n, h⟩ else 0 := by
  simp only [movingCanonicalFinitePerturbation, LinearMap.coe_mk,
    AddHom.coe_mk, lp.coeFn_sum, Finset.sum_apply, lp.single_apply,
    Pi.single_apply]
  by_cases h : n < D
  · rw [dif_pos h, Finset.sum_eq_single ⟨n, h⟩]
    · simp
    · intro b hb hne
      rw [if_neg]
      intro hnb
      apply hne
      exact Fin.ext hnb.symm
    · simp
  · rw [dif_neg h]
    apply Finset.sum_eq_zero
    intro a ha
    rw [if_neg]
    intro hna
    apply h
    rw [hna]
    exact a.2

theorem continuous_movingCanonicalFinitePerturbation (D : ℕ) :
    Continuous (movingCanonicalFinitePerturbation D) :=
  (movingCanonicalFinitePerturbation D).continuous_of_finiteDimensional

def movingCanonicalFiniteChart
    (D : ℕ) (θ : BoundedRealSequence) (p : Fin D → ℝ) :
    BoundedRealSequence :=
  θ + movingCanonicalFinitePerturbation D p

@[simp]
theorem movingCanonicalFiniteChart_apply
    (D : ℕ) (θ : BoundedRealSequence) (p : Fin D → ℝ) (n : ℕ) :
    movingCanonicalFiniteChart D θ p n =
      θ n + if h : n < D then p ⟨n, h⟩ else 0 := by
  simp [movingCanonicalFiniteChart]

theorem contDiff_movingCanonicalFiniteChart
    (D : ℕ) (θ : BoundedRealSequence) :
    ContDiff ℝ ⊤ (movingCanonicalFiniteChart D θ) := by
  let L : (Fin D → ℝ) →L[ℝ] BoundedRealSequence :=
    ⟨movingCanonicalFinitePerturbation D,
      continuous_movingCanonicalFinitePerturbation D⟩
  exact contDiff_const.add
    L.contDiff

theorem movingCanonicalZero_finiteChart_hasFDerivAt
    (D : ℕ) (θ : BoundedRealSequence) (p : Fin D → ℝ) (a : Fin D) :
    HasNormedFDerivAt
      (fun q : Fin D → ℝ =>
        movingCanonicalZero (movingCanonicalFiniteChart D θ q) a.1)
      (canonicalZeroSpeed (θ a.1 + p a) •
        (ContinuousLinearMap.proj a :
          (Fin D → ℝ) →L[ℝ] ℝ)) p := by
  have hcoord : HasFDerivAt
      (fun q : Fin D → ℝ => θ a.1 + q a)
      (ContinuousLinearMap.proj a : (Fin D → ℝ) →L[ℝ] ℝ) p := by
    exact (ContinuousLinearMap.proj a :
      (Fin D → ℝ) →L[ℝ] ℝ).hasFDerivAt.const_add (θ a.1)
  have hdisp :=
    (canonicalZeroDisplacement_hasDerivAt (θ a.1 + p a)).comp_hasFDerivAt
      p hcoord
  have hzero := hdisp.const_add ((a.1 : ℝ) + 1)
  convert hzero using 1
  · funext q
    simp only [Function.comp_apply, movingCanonicalZero,
      movingCanonicalFiniteChart_apply, dif_pos a.2]

def movingCanonicalRegularizedTerm
    (θ : BoundedRealSequence) (a : ℕ) (z : ℂ) : ℂ :=
  ((movingCanonicalZero θ a : ℂ) - z)⁻¹ -
    (movingCanonicalZero θ a : ℂ)⁻¹

def movingCanonicalNormalizedJetTerm
    (θ : BoundedRealSequence) (k : ℕ) (a : ℕ) (z : ℂ) : ℂ :=
  if k = 0 then movingCanonicalRegularizedTerm θ a z
  else (((movingCanonicalZero θ a : ℂ) - z)⁻¹) ^ (k + 1)

def movingCanonicalNormalizedJet
    (θ : BoundedRealSequence) (k : ℕ) (z : ℂ) : ℂ :=
  ∑' a, movingCanonicalNormalizedJetTerm θ k a z

@[simp]
theorem movingCanonicalNormalizedJet_zero
    (θ : BoundedRealSequence) (z : ℂ) :
    movingCanonicalNormalizedJet θ 0 z =
      movingCanonicalLogDerivative θ z := by
  apply tsum_congr
  intro a
  rfl

theorem continuous_movingCanonicalZero_coordinate (a : ℕ) :
    Continuous (fun θ : BoundedRealSequence => movingCanonicalZero θ a) := by
  rw [continuous_iff_continuousAt]
  intro θ
  have heval : ContinuousAt (fun u : BoundedRealSequence => u a) θ :=
    (lp.evalCLM ℝ (fun _ : ℕ => ℝ) ∞ a).continuous.continuousAt
  have hdisp : ContinuousAt
      (fun u : BoundedRealSequence => canonicalZeroDisplacement (u a)) θ :=
    (canonicalZeroDisplacement_hasDerivAt (θ a)).continuousAt.comp
      (f := fun u : BoundedRealSequence => u a) heval
  change ContinuousAt
    ((fun _ : BoundedRealSequence => (a : ℝ) + 1) +
      fun u => canonicalZeroDisplacement (u a)) θ
  exact continuousAt_const.add hdisp

theorem continuousOn_movingCanonicalNormalizedJetTerm
    (k a : ℕ) :
    ContinuousOn
      (fun p : BoundedRealSequence × ℂ =>
        movingCanonicalNormalizedJetTerm p.1 k a p.2)
      (Set.univ ×ˢ upperHalfPlane) := by
  intro p hp
  have hzeroR : ContinuousAt
      (fun q : BoundedRealSequence × ℂ => movingCanonicalZero q.1 a) p :=
    (continuous_movingCanonicalZero_coordinate a).continuousAt.comp
      continuousAt_fst
  have hzero : ContinuousAt
      (fun q : BoundedRealSequence × ℂ =>
        (movingCanonicalZero q.1 a : ℂ)) p :=
    Complex.continuous_ofReal.continuousAt.comp hzeroR
  have hsub : ContinuousAt
      (fun q : BoundedRealSequence × ℂ =>
        (movingCanonicalZero q.1 a : ℂ) - q.2) p :=
    hzero.sub continuousAt_snd
  have hne : (movingCanonicalZero p.1 a : ℂ) - p.2 ≠ 0 := by
    intro h
    have him := congrArg Complex.im h
    simp at him
    exact (ne_of_gt hp.2) him
  have hzeroNe : (movingCanonicalZero p.1 a : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (ne_of_gt (movingCanonicalZero_pos p.1 a))
  unfold movingCanonicalNormalizedJetTerm movingCanonicalRegularizedTerm
  split_ifs
  · exact ((hsub.inv₀ hne).sub (hzero.inv₀ hzeroNe)).continuousWithinAt
  · exact ((hsub.inv₀ hne).pow _).continuousWithinAt

/-- Every differentiated moving-pole series is summable in the upper half-plane. -/
theorem summable_movingCanonicalCauchyPower
    (θ : BoundedRealSequence) (m : ℕ) {z : ℂ} (hz : 0 < z.im) :
    Summable (fun a =>
      (((movingCanonicalZero θ a : ℂ) - z)⁻¹) ^ (m + 2)) := by
  let C : ℝ := 1 + ‖z‖ / z.im
  have hC : 0 ≤ C := by
    dsimp [C]
    positivity
  have hmajor : Summable (fun a =>
      (C ^ 2 * (z.im)⁻¹ ^ m) *
        (1 / ‖(movingCanonicalZero θ a : ℂ)‖ ^ 2)) :=
    (summable_movingCanonicalZero_inv_sq θ).mul_left
      (C ^ 2 * (z.im)⁻¹ ^ m)
  apply hmajor.of_norm_bounded
  intro a
  let A : ℝ := ‖(movingCanonicalZero θ a : ℂ)‖
  let d : ℝ := ‖(movingCanonicalZero θ a : ℂ) - z‖
  have hApos : 0 < A := norm_pos_iff.mpr
    (Complex.ofReal_ne_zero.mpr (ne_of_gt (movingCanonicalZero_pos θ a)))
  have hdpos : 0 < d := by
    rw [norm_pos_iff]
    intro h
    have him := congrArg Complex.im h
    simp at him
    exact (ne_of_gt hz) him
  have hyd : z.im ≤ d := by
    have hi := Complex.abs_im_le_norm
      ((movingCanonicalZero θ a : ℂ) - z)
    have him :
        ((movingCanonicalZero θ a : ℂ) - z).im = -z.im := by simp
    rw [him, abs_neg, abs_of_pos hz] at hi
    exact hi
  have hAz : A ≤ d + ‖z‖ := by
    calc
      A = ‖(movingCanonicalZero θ a : ℂ)‖ := rfl
      _ = ‖((movingCanonicalZero θ a : ℂ) - z) + z‖ := by
        congr 2
        abel
      _ ≤ d + ‖z‖ := norm_add_le _ _
  have hzscale : ‖z‖ ≤ (‖z‖ / z.im) * d := by
    rw [div_mul_eq_mul_div, le_div_iff₀ hz]
    nlinarith [mul_le_mul_of_nonneg_left hyd (norm_nonneg z)]
  have hACd : A ≤ C * d := by
    dsimp [C]
    nlinarith
  have hinvAC : d⁻¹ ≤ C * A⁻¹ := by
    have hdiv : 1 / d ≤ C / A := by
      rw [div_le_div_iff₀ hdpos hApos]
      simpa [mul_comm] using hACd
    simpa [div_eq_mul_inv] using hdiv
  have hinvY : d⁻¹ ≤ (z.im)⁻¹ := by
    simpa [one_div] using one_div_le_one_div_of_le hz hyd
  rw [norm_pow, norm_inv, show m + 2 = m + 2 by rfl, pow_add]
  calc
    d⁻¹ ^ m * d⁻¹ ^ 2
        ≤ (z.im)⁻¹ ^ m * (C * A⁻¹) ^ 2 :=
      mul_le_mul (pow_le_pow_left₀ (by positivity) hinvY m)
        (pow_le_pow_left₀ (by positivity) hinvAC 2)
        (by positivity) (by positivity)
    _ = (C ^ 2 * (z.im)⁻¹ ^ m) * (1 / A ^ 2) := by
      field_simp

/-- Every normalized moving-canonical jet series converges in the upper half-plane. -/
theorem summable_movingCanonicalNormalizedJetTerm
    (θ : BoundedRealSequence) (k : ℕ) {z : ℂ} (hz : 0 < z.im) :
    Summable (fun a => movingCanonicalNormalizedJetTerm θ k a z) := by
  by_cases hk : k = 0
  · subst k
    simpa [movingCanonicalNormalizedJetTerm, movingCanonicalRegularizedTerm] using
      summable_movingCanonicalLogDerivative θ (fun a h => by
        have him := congrArg Complex.im h
        simp at him
        exact (ne_of_gt hz) him)
  · obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk
    simpa [movingCanonicalNormalizedJetTerm] using
      summable_movingCanonicalCauchyPower θ m hz

/-- Changing the first `D` bounded coordinates changes the exact jet series by the corresponding
finite sum and leaves the infinite tail literally fixed. -/
theorem movingCanonicalNormalizedJet_finiteChart
    (D : ℕ) (θ : BoundedRealSequence) (p : Fin D → ℝ)
    (k : ℕ) {z : ℂ} (hz : 0 < z.im) :
    movingCanonicalNormalizedJet (movingCanonicalFiniteChart D θ p) k z =
      movingCanonicalNormalizedJet θ k z +
        ∑ a : Fin D,
          (movingCanonicalNormalizedJetTerm
              (movingCanonicalFiniteChart D θ p) k a.1 z -
            movingCanonicalNormalizedJetTerm θ k a.1 z) := by
  let fnew : ℕ → ℂ := fun a =>
    movingCanonicalNormalizedJetTerm
      (movingCanonicalFiniteChart D θ p) k a z
  let fold : ℕ → ℂ := fun a =>
    movingCanonicalNormalizedJetTerm θ k a z
  have hnew : Summable fnew :=
    summable_movingCanonicalNormalizedJetTerm
      (movingCanonicalFiniteChart D θ p) k hz
  have hold : Summable fold :=
    summable_movingCanonicalNormalizedJetTerm θ k hz
  have htail : (∑' a :
      {a // a ∈ ((↑(Finset.range D) : Set ℕ)ᶜ)}, fnew a) =
      ∑' a : {a // a ∈ ((↑(Finset.range D) : Set ℕ)ᶜ)}, fold a := by
    apply tsum_congr
    intro a
    have ha : ¬a.1 < D := by
      simpa using a.2
    have hchart :
        movingCanonicalFiniteChart D θ p a.1 = θ a.1 := by
      simp [movingCanonicalFiniteChart_apply, ha]
    have hzero :
        movingCanonicalZero (movingCanonicalFiniteChart D θ p) a.1 =
          movingCanonicalZero θ a.1 := by
      simp only [movingCanonicalZero, hchart]
    simp only [fnew, fold]
    rw [show movingCanonicalNormalizedJetTerm
      (movingCanonicalFiniteChart D θ p) k a.1 z =
        movingCanonicalNormalizedJetTerm θ k a.1 z by
          simp [movingCanonicalNormalizedJetTerm,
            movingCanonicalRegularizedTerm, hzero]]
  have hsplitNew := hnew.sum_add_tsum_compl
    (s := Finset.range D)
  have hsplitOld := hold.sum_add_tsum_compl
    (s := Finset.range D)
  change (∑' a, fnew a) =
    (∑' a, fold a) + ∑ a : Fin D, (fnew a.1 - fold a.1)
  rw [← hsplitNew, ← hsplitOld, htail]
  have hfin :
      (∑ a : Fin D, (fnew a.1 - fold a.1)) =
        ∑ i ∈ Finset.range D, (fnew i - fold i) :=
    Fin.sum_univ_eq_sum_range (fun i => fnew i - fold i) D
  rw [hfin]
  rw [Finset.sum_sub_distrib]
  abel

/-- The regularized canonical logarithmic derivative is analytic throughout the upper half-plane. -/
theorem analyticAt_movingCanonicalLogDerivative
    (θ : BoundedRealSequence) {z : ℂ} (hz : 0 < z.im) :
    AnalyticAt ℂ (movingCanonicalLogDerivative θ) z := by
  have hproduct : AnalyticAt ℂ (movingCanonicalProduct θ) z :=
    movingCanonicalProduct_analytic θ z (Set.mem_univ z)
  have hproductNe : movingCanonicalProduct θ z ≠ 0 := by
    intro hzero
    obtain ⟨a, ha⟩ :=
      (movingCanonicalProduct_eq_zero_iff θ z).mp hzero
    have him := congrArg Complex.im ha
    simp at him
    exact (ne_of_gt hz) him
  have hlog : AnalyticAt ℂ
      (fun w => -logDeriv (movingCanonicalProduct θ) w) z := by
    have hquot : AnalyticAt ℂ
        (fun w => deriv (movingCanonicalProduct θ) w /
          movingCanonicalProduct θ w) z :=
      hproduct.deriv.div hproduct hproductNe
    change AnalyticAt ℂ
      (fun w => -(deriv (movingCanonicalProduct θ) w /
        movingCanonicalProduct θ w)) z
    exact hquot.neg
  refine hlog.congr ?_
  filter_upwards [isOpen_upperHalfPlane.mem_nhds hz] with w hw
  exact neg_logDeriv_movingCanonicalProduct_eq θ (fun a ha => by
    have him := congrArg Complex.im ha
    simp at him
    exact (ne_of_gt hw) him)

/-- Every actual differential jet of the canonical carrier remains analytic in the node. -/
theorem analyticAt_iteratedDeriv_movingCanonicalLogDerivative
    (θ : BoundedRealSequence) (k : ℕ) {z : ℂ} (hz : 0 < z.im) :
    AnalyticAt ℂ (iteratedDeriv k (movingCanonicalLogDerivative θ)) z := by
  induction k with
  | zero =>
      simpa [iteratedDeriv_zero] using
        analyticAt_movingCanonicalLogDerivative θ hz
  | succ k ih =>
      rw [iteratedDeriv_succ]
      exact ih.deriv

/-- One pole's exact actual differential-jet contribution. -/
def movingCanonicalDifferentialJetTerm
    (θ : BoundedRealSequence) (k : ℕ) (a : ℕ) (z : ℂ) : ℂ :=
  if k = 0 then movingCanonicalRegularizedTerm θ a z
  else (k.factorial : ℂ) *
    (((movingCanonicalZero θ a : ℂ) - z)⁻¹) ^ (k + 1)

def regularizedPoleDifferentialJetTerm
    (k : ℕ) (t : ℝ) (z : ℂ) : ℂ :=
  if k = 0 then
    (((t : ℂ) - z)⁻¹ - (t : ℂ)⁻¹)
  else (k.factorial : ℂ) * (((t : ℂ) - z)⁻¹) ^ (k + 1)

theorem movingCanonicalDifferentialJetTerm_eq
    (θ : BoundedRealSequence) (k a : ℕ) (z : ℂ) :
    movingCanonicalDifferentialJetTerm θ k a z =
      regularizedPoleDifferentialJetTerm k (movingCanonicalZero θ a) z :=
  rfl

theorem regularizedPoleDifferentialJetTerm_zero_hasDerivAt
    (t : ℝ) (ht : t ≠ 0) {z : ℂ} (hz : 0 < z.im) :
    HasDerivAt (fun s : ℝ => (((s : ℂ) - z)⁻¹ - (s : ℂ)⁻¹))
      (-1 / (((t : ℂ) - z) ^ 2) - (-1 / ((t : ℂ) ^ 2))) t := by
  have htZ : (t : ℂ) - z ≠ 0 := by
    intro h
    have him := congrArg Complex.im h
    simp at him
    exact (ne_of_gt hz) him
  have hofReal : HasDerivAt (fun s : ℝ => (s : ℂ)) 1 t := by
    exact (hasDerivAt_id t).ofReal_comp
  exact ((hofReal.sub_const z).inv htZ).sub
    (hofReal.inv (Complex.ofReal_ne_zero.mpr ht))

theorem regularizedPoleDifferentialJetTerm_succ_hasDerivAt
    (k : ℕ) (t : ℝ) {z : ℂ} (hz : 0 < z.im) :
    @HasDerivAt ℝ inferInstance ℂ
      instCommCStarAlgebraComplex.toCStarAlgebra.toAddCommGroup inferInstance
      inferInstance inferInstance
      (fun s : ℝ =>
        (k.factorial : ℂ) * (((s : ℂ) - z)⁻¹) ^ (k + 1))
      (-((Nat.factorial (k + 1) : ℂ) *
        (((t : ℂ) - z)⁻¹) ^ (k + 2))) t := by
  have htZ : (t : ℂ) - z ≠ 0 := by
    intro h
    have him := congrArg Complex.im h
    simp at him
    exact (ne_of_gt hz) him
  have hofReal : HasDerivAt (fun s : ℝ => (s : ℂ)) 1 t := by
    exact (hasDerivAt_id t).ofReal_comp
  have hbase : HasDerivAt (fun s : ℝ => ((s : ℂ) - z)⁻¹)
      (-(((t : ℂ) - z)⁻¹) ^ 2) t := by
    exact (hofReal.sub_const z).inv htZ |>.congr_deriv (by
      field_simp)
  have hpow := hbase.pow (k + 1)
  have hmul := hpow.const_mul (k.factorial : ℂ)
  convert hmul using 1
  · funext s
    rfl
  · rw [Nat.factorial_succ]
    push_cast
    rw [pow_add]
    ring

def movingCanonicalDifferentialJetCoefficient
    (k : ℕ) (t : ℝ) (z : ℂ) : ℂ :=
  (((if k = 0 then 1 / t ^ 2 else 0 : ℝ) : ℂ) -
    (Nat.factorial (k + 1) : ℂ) *
      ((((t : ℝ) : ℂ) - z)⁻¹) ^ (k + 2))

theorem movingCanonicalDifferentialJetCoefficient_eq_location_single
    {ι κ : Type*} (x : ι → ℂ) (n : ι → ℕ) (t : κ → ℝ)
    (a : κ) (s : Σ i, Fin (n i)) :
    movingCanonicalDifferentialJetCoefficient s.2.1 (t a) (x s.1) =
      movingPoleLocationJetRealLinearCombination x n t
        (Finsupp.single a 1) s := by
  symm
  exact movingPoleLocationJetRealLinearCombination_single_apply
    x n t a s

theorem movingCanonicalFiniteParameterJetLinearMap_apply
    {ι : Type*} [Fintype ι]
    (x : ι → ℂ) (n : ι → ℕ) (θ : BoundedRealSequence)
    (p : Fin (movingCanonicalLocationProbeCard n) → ℝ)
    (s : Σ i, Fin (n i)) :
    movingCanonicalFiniteParameterJetLinearMap x n θ p s =
      ∑ a : Fin (movingCanonicalLocationProbeCard n),
        p a • (canonicalZeroSpeed (θ a.1) •
          movingCanonicalDifferentialJetCoefficient
            s.2.1 (movingCanonicalZero θ a.1) (x s.1)) := by
  let D := movingCanonicalLocationProbeCard n
  let r : Fin D → ℝ := fun a => canonicalZeroSpeed (θ a.1) * p a
  have hr : (Finsupp.linearEquivFunOnFinite ℝ ℝ (Fin D)).symm r =
      ∑ a : Fin D, Finsupp.single a (r a) := by
    ext a
    rw [congrFun
      (Finsupp.linearEquivFunOnFinite_symm_apply ℝ ℝ (Fin D) r) a]
    exact (congrFun (Finsupp.coe_univ_sum_single r) a).symm
  change movingPoleLocationJetRealLinearCombination x n
      (fun a : Fin D => movingCanonicalZero θ a.1)
      ((Finsupp.linearEquivFunOnFinite ℝ ℝ (Fin D)).symm r) s = _
  rw [hr, map_sum]
  rw [Finset.sum_apply]
  apply Finset.sum_congr rfl
  intro a ha
  have hsingle : Finsupp.single a (r a) =
      r a • Finsupp.single a (1 : ℝ) := by
    ext b
    by_cases hba : b = a <;> simp [hba]
  rw [hsingle, map_smul]
  rw [Pi.smul_apply]
  rw [movingCanonicalDifferentialJetCoefficient_eq_location_single
    (κ := Fin D) x n
      (fun b : Fin D => movingCanonicalZero θ b.1) a s]
  simp only [r, smul_smul]
  ring

theorem movingCanonicalDifferentialJetTerm_finiteChart_hasFDerivAt
    (D : ℕ) (θ : BoundedRealSequence) (p : Fin D → ℝ)
    (k : ℕ) (a : Fin D) {z : ℂ} (hz : 0 < z.im) :
    HasNormedFDerivAt
      (fun q : Fin D → ℝ =>
        movingCanonicalDifferentialJetTerm
          (movingCanonicalFiniteChart D θ q) k a.1 z)
      ((ContinuousLinearMap.proj a : (Fin D → ℝ) →L[ℝ] ℝ).smulRight
        (canonicalZeroSpeed (θ a.1 + p a) •
          movingCanonicalDifferentialJetCoefficient k
            (movingCanonicalZero
              (movingCanonicalFiniteChart D θ p) a.1) z)) p := by
  let t := movingCanonicalZero
    (movingCanonicalFiniteChart D θ p) a.1
  have ht : t ≠ 0 :=
    ne_of_gt (movingCanonicalZero_pos
      (movingCanonicalFiniteChart D θ p) a.1)
  have hzero := movingCanonicalZero_finiteChart_hasFDerivAt D θ p a
  by_cases hk : k = 0
  · subst k
    have hout :=
      (regularizedPoleDifferentialJetTerm_zero_hasDerivAt t ht hz).hasFDerivAt
    have hcomp := hout.comp p hzero
    convert hcomp using 1
    · funext q
      simp [Function.comp_apply, movingCanonicalDifferentialJetTerm,
        movingCanonicalRegularizedTerm]
    · ext v
      simp only [FunLike.coe_smul, Pi.smul_apply,
        smul_eq_mul, ContinuousLinearMap.smulRight_apply,
        ContinuousLinearMap.comp_apply,
        ContinuousLinearMap.toSpanSingleton_apply]
      dsimp only [movingCanonicalDifferentialJetCoefficient]
      simp only [if_pos, Nat.zero_add, Nat.factorial_one, Nat.cast_one,
        one_mul, Complex.real_smul]
      dsimp only [t] at ht ⊢
      push_cast
      field_simp [ht]
      ring
  · have hout :=
      (regularizedPoleDifferentialJetTerm_succ_hasDerivAt
        k t hz).hasFDerivAt
    have hcomp := hout.comp p hzero
    convert hcomp using 1
    · funext q
      simp [Function.comp_apply, movingCanonicalDifferentialJetTerm, hk]
    · ext v
      simp only [FunLike.coe_smul, Pi.smul_apply,
        smul_eq_mul, ContinuousLinearMap.smulRight_apply,
        ContinuousLinearMap.comp_apply,
        ContinuousLinearMap.toSpanSingleton_apply]
      dsimp only [movingCanonicalDifferentialJetCoefficient]
      rw [if_neg hk]
      simp only [Complex.real_smul]
      norm_num
      ring

/-- Exact derivatives of one regularized real pole. -/
theorem iteratedDeriv_movingCanonicalRegularizedTerm
    (θ : BoundedRealSequence) (a k : ℕ) {z : ℂ} (hz : 0 < z.im) :
    iteratedDeriv k (movingCanonicalRegularizedTerm θ a) z =
      movingCanonicalDifferentialJetTerm θ k a z := by
  by_cases hk : k = 0
  · subst k
    simp [movingCanonicalDifferentialJetTerm, iteratedDeriv_zero]
  · have hkernel : ContDiffAt ℂ (k : ℕ∞)
        (fun w : ℂ => ((movingCanonicalZero θ a : ℂ) - w)⁻¹) z := by
      have hne : (movingCanonicalZero θ a : ℂ) - z ≠ 0 := by
        intro h
        have him := congrArg Complex.im h
        simp at him
        exact (ne_of_gt hz) him
      fun_prop
    have hconst : ContDiffAt ℂ (k : ℕ∞)
        (fun _ : ℂ => (movingCanonicalZero θ a : ℂ)⁻¹) z :=
      contDiffAt_const
    change iteratedDeriv k
      ((fun w : ℂ => ((movingCanonicalZero θ a : ℂ) - w)⁻¹) -
        fun _ : ℂ => (movingCanonicalZero θ a : ℂ)⁻¹) z = _
    rw [iteratedDeriv_sub hkernel hconst,
      iteratedDeriv_realCauchyKernel (movingCanonicalZero θ a) k z hz,
      iteratedDeriv_const]
    simp [movingCanonicalDifferentialJetTerm, hk]

/-- Finite-coordinate canonical perturbation changes every actual node jet by the exact finite
sum of the corresponding pole contributions. -/
theorem iteratedDeriv_movingCanonicalLogDerivative_finiteChart
    (D : ℕ) (θ : BoundedRealSequence) (p : Fin D → ℝ)
    (k : ℕ) {z : ℂ} (hz : 0 < z.im) :
    iteratedDeriv k
        (movingCanonicalLogDerivative (movingCanonicalFiniteChart D θ p)) z =
      iteratedDeriv k (movingCanonicalLogDerivative θ) z +
        ∑ a : Fin D,
          (movingCanonicalDifferentialJetTerm
              (movingCanonicalFiniteChart D θ p) k a.1 z -
            movingCanonicalDifferentialJetTerm θ k a.1 z) := by
  have heq : movingCanonicalLogDerivative
      (movingCanonicalFiniteChart D θ p) =ᶠ[nhds z]
      fun w => movingCanonicalLogDerivative θ w +
        ∑ a : Fin D,
          (movingCanonicalRegularizedTerm
              (movingCanonicalFiniteChart D θ p) a.1 w -
            movingCanonicalRegularizedTerm θ a.1 w) := by
    filter_upwards [isOpen_upperHalfPlane.mem_nhds hz] with w hw
    simpa [movingCanonicalNormalizedJetTerm] using
      movingCanonicalNormalizedJet_finiteChart D θ p 0 hw
  rw [heq.iteratedDeriv_eq k]
  have hbase : ContDiffAt ℂ (k : ℕ∞)
      (movingCanonicalLogDerivative θ) z :=
    (analyticAt_movingCanonicalLogDerivative θ hz).contDiffAt.of_le
      (WithTop.coe_le_coe.mpr le_rfl)
  have hterm : ∀ a : Fin D,
      ContDiffAt ℂ (k : ℕ∞)
          (movingCanonicalRegularizedTerm
            (movingCanonicalFiniteChart D θ p) a.1) z ∧
        ContDiffAt ℂ (k : ℕ∞)
          (movingCanonicalRegularizedTerm θ a.1) z := by
    intro a
    have hneNew :
        (movingCanonicalZero (movingCanonicalFiniteChart D θ p) a.1 : ℂ) - z ≠ 0 := by
      intro h
      have him := congrArg Complex.im h
      simp at him
      exact (ne_of_gt hz) him
    have hneOld : (movingCanonicalZero θ a.1 : ℂ) - z ≠ 0 := by
      intro h
      have him := congrArg Complex.im h
      simp at him
      exact (ne_of_gt hz) him
    constructor <;> unfold movingCanonicalRegularizedTerm <;> fun_prop
  have hsum : ContDiffAt ℂ (k : ℕ∞)
      (fun w => ∑ a : Fin D,
        (movingCanonicalRegularizedTerm
            (movingCanonicalFiniteChart D θ p) a.1 w -
          movingCanonicalRegularizedTerm θ a.1 w)) z :=
    ContDiffAt.sum (s := Finset.univ)
      (fun a _ => (hterm a).1.sub (hterm a).2)
  change iteratedDeriv k
      (movingCanonicalLogDerivative θ +
        fun w => ∑ a : Fin D,
          (movingCanonicalRegularizedTerm
              (movingCanonicalFiniteChart D θ p) a.1 w -
            movingCanonicalRegularizedTerm θ a.1 w)) z = _
  rw [iteratedDeriv_add hbase hsum]
  have hsumDeriv :
      iteratedDeriv k
          (fun w => ∑ a : Fin D,
            (movingCanonicalRegularizedTerm
                (movingCanonicalFiniteChart D θ p) a.1 w -
              movingCanonicalRegularizedTerm θ a.1 w)) z =
        ∑ a : Fin D, iteratedDeriv k
          (fun w =>
            movingCanonicalRegularizedTerm
                (movingCanonicalFiniteChart D θ p) a.1 w -
              movingCanonicalRegularizedTerm θ a.1 w) z := by
    have hfun :
        (fun w => ∑ a : Fin D,
          (movingCanonicalRegularizedTerm
              (movingCanonicalFiniteChart D θ p) a.1 w -
            movingCanonicalRegularizedTerm θ a.1 w)) =
          ∑ a : Fin D,
            (movingCanonicalRegularizedTerm
                (movingCanonicalFiniteChart D θ p) a.1 -
              movingCanonicalRegularizedTerm θ a.1) := by
      funext w
      simp
    rw [hfun]
    exact iteratedDeriv_sum
      (I := Finset.univ)
      (fun a _ => (hterm a).1.sub (hterm a).2)
  rw [hsumDeriv]
  apply congrArg₂ (· + ·) rfl
  apply Finset.sum_congr rfl
  intro a ha
  change iteratedDeriv k
      (movingCanonicalRegularizedTerm
          (movingCanonicalFiniteChart D θ p) a.1 -
        movingCanonicalRegularizedTerm θ a.1) z = _
  rw [iteratedDeriv_sub]
  · rw [iteratedDeriv_movingCanonicalRegularizedTerm
      (movingCanonicalFiniteChart D θ p) a.1 k hz,
      iteratedDeriv_movingCanonicalRegularizedTerm θ a.1 k hz]
  · exact (hterm a).1
  · exact (hterm a).2

def movingCanonicalFiniteActualJetFamily
    {ι : Type*} [Fintype ι]
    (x : ι → ℂ) (n : ι → ℕ) (θ : BoundedRealSequence)
    (p : Fin (movingCanonicalLocationProbeCard n) → ℝ) :
    (Σ i, Fin (n i)) → ℂ :=
  fun s => iteratedDeriv s.2.1
    (movingCanonicalLogDerivative
      (movingCanonicalFiniteChart
        (movingCanonicalLocationProbeCard n) θ p)) (x s.1)

theorem movingCanonicalFiniteActualJetFamily_coordinate_hasFDerivAt
    {ι : Type*} [Fintype ι]
    (x : ι → ℂ) (hupper : ∀ i, 0 < (x i).im)
    (n : ι → ℕ) (θ : BoundedRealSequence)
    (p : Fin (movingCanonicalLocationProbeCard n) → ℝ)
    (s : Σ i, Fin (n i)) :
    HasNormedFDerivAt
      (fun q => movingCanonicalFiniteActualJetFamily x n θ q s)
      (∑ a : Fin (movingCanonicalLocationProbeCard n),
        (ContinuousLinearMap.proj a :
          (Fin (movingCanonicalLocationProbeCard n) → ℝ) →L[ℝ] ℝ).smulRight
          (canonicalZeroSpeed (θ a.1 + p a) •
            movingCanonicalDifferentialJetCoefficient s.2.1
              (movingCanonicalZero
                (movingCanonicalFiniteChart
                  (movingCanonicalLocationProbeCard n) θ p) a.1)
              (x s.1))) p := by
  let D := movingCanonicalLocationProbeCard n
  have hterm : ∀ a : Fin D, HasNormedFDerivAt
      (fun q : Fin D → ℝ =>
        movingCanonicalDifferentialJetTerm
            (movingCanonicalFiniteChart D θ q) s.2.1 a.1 (x s.1) -
          movingCanonicalDifferentialJetTerm θ s.2.1 a.1 (x s.1))
      ((ContinuousLinearMap.proj a : (Fin D → ℝ) →L[ℝ] ℝ).smulRight
        (canonicalZeroSpeed (θ a.1 + p a) •
          movingCanonicalDifferentialJetCoefficient s.2.1
            (movingCanonicalZero
              (movingCanonicalFiniteChart D θ p) a.1) (x s.1))) p := by
    intro a
    have hnew :=
      movingCanonicalDifferentialJetTerm_finiteChart_hasFDerivAt
        D θ p s.2.1 a (hupper s.1)
    have hadjusted := hnew.add_const
      (-movingCanonicalDifferentialJetTerm θ s.2.1 a.1 (x s.1))
    convert hadjusted using 1
    funext q
    simp only [sub_eq_add_neg]
  have hsum := HasFDerivAt.sum
    (u := (Finset.univ : Finset (Fin D)))
    (fun a _ => hterm a)
  have hfull := hsum.const_add
    (iteratedDeriv s.2.1 (movingCanonicalLogDerivative θ) (x s.1))
  convert hfull using 1
  funext q
  dsimp only [movingCanonicalFiniteActualJetFamily]
  rw [Finset.sum_apply]
  exact iteratedDeriv_movingCanonicalLogDerivative_finiteChart
    D θ q s.2.1 (hupper s.1)

def movingCanonicalFiniteParameterJetCLM
    {ι : Type*} [Fintype ι]
    (x : ι → ℂ) (n : ι → ℕ) (θ : BoundedRealSequence) :
    (Fin (movingCanonicalLocationProbeCard n) → ℝ) →L[ℝ]
      ((Σ i, Fin (n i)) → ℂ) :=
  LinearMap.toContinuousLinearMap
    (movingCanonicalFiniteParameterJetLinearMap x n θ)

theorem movingCanonicalFiniteActualJetFamily_hasFDerivAt
    {ι : Type*} [Fintype ι]
    (x : ι → ℂ) (hupper : ∀ i, 0 < (x i).im)
    (n : ι → ℕ) (θ : BoundedRealSequence)
    (p : Fin (movingCanonicalLocationProbeCard n) → ℝ) :
    HasNormedFDerivAt
      (movingCanonicalFiniteActualJetFamily x n θ)
      (movingCanonicalFiniteParameterJetCLM x n
        (movingCanonicalFiniteChart
          (movingCanonicalLocationProbeCard n) θ p)) p := by
  let D := movingCanonicalLocationProbeCard n
  let derivative : (Σ i, Fin (n i)) →
      (Fin D → ℝ) →L[ℝ] ℂ := fun s =>
    ∑ a : Fin D,
      (ContinuousLinearMap.proj a : (Fin D → ℝ) →L[ℝ] ℝ).smulRight
        (canonicalZeroSpeed (θ a.1 + p a) •
          movingCanonicalDifferentialJetCoefficient s.2.1
            (movingCanonicalZero
              (movingCanonicalFiniteChart D θ p) a.1) (x s.1))
  have hpi : HasNormedFDerivAt
      (movingCanonicalFiniteActualJetFamily x n θ)
      (ContinuousLinearMap.pi derivative) p := by
    apply (hasFDerivAt_pi).2
    intro s
    exact movingCanonicalFiniteActualJetFamily_coordinate_hasFDerivAt
      x hupper n θ p s
  convert hpi using 1
  ext v s
  rw [movingCanonicalFiniteParameterJetCLM]
  change movingCanonicalFiniteParameterJetLinearMap x n
      (movingCanonicalFiniteChart D θ p) v s = derivative s v
  rw [movingCanonicalFiniteParameterJetLinearMap_apply]
  simp only [derivative, sum_apply,
    ContinuousLinearMap.smulRight_apply]
  apply Finset.sum_congr rfl
  intro a ha
  rw [movingCanonicalFiniteChart_apply, dif_pos a.2]
  change
    v a • canonicalZeroSpeed (θ a.1 + p a) •
        movingCanonicalDifferentialJetCoefficient s.2.1
          (movingCanonicalZero (movingCanonicalFiniteChart D θ p) a.1)
          (x s.1) =
      v a • canonicalZeroSpeed (θ a.1 + p a) •
        movingCanonicalDifferentialJetCoefficient s.2.1
          (movingCanonicalZero (movingCanonicalFiniteChart D θ p) a.1)
          (x s.1)
  rfl

theorem contDiff_real_tanh : ContDiff ℝ ⊤ Real.tanh := by
  have hneg : ContDiff ℝ ⊤ (fun x : ℝ => -x) := contDiff_id.neg
  have hexpNeg : ContDiff ℝ ⊤ (fun x : ℝ => Real.exp (-x)) :=
    Real.contDiff_exp.comp hneg
  have hquot : ContDiff ℝ ⊤
      (fun x : ℝ =>
        (Real.exp x - Real.exp (-x)) /
          (Real.exp x + Real.exp (-x))) :=
    (Real.contDiff_exp.sub hexpNeg).div
      (Real.contDiff_exp.add hexpNeg)
      (fun x => ne_of_gt (add_pos (Real.exp_pos x) (Real.exp_pos (-x))))
  convert hquot using 1
  funext x
  exact Real.tanh_eq x

theorem contDiff_movingCanonicalZero_finiteChart
    (D : ℕ) (θ : BoundedRealSequence) (a : Fin D) :
    ContDiff ℝ ⊤
      (fun p : Fin D → ℝ =>
        movingCanonicalZero (movingCanonicalFiniteChart D θ p) a.1) := by
  have hcoord : ContDiff ℝ ⊤
      (fun p : Fin D → ℝ => θ a.1 + p a) :=
    contDiff_const.add
      (ContinuousLinearMap.proj a :
        (Fin D → ℝ) →L[ℝ] ℝ).contDiff
  have hcomp := contDiff_real_tanh.comp hcoord
  unfold movingCanonicalZero canonicalZeroDisplacement
  simp only [movingCanonicalFiniteChart_apply, dif_pos a.2]
  exact contDiff_const.add (contDiff_const.mul hcomp)

theorem contDiff_movingCanonicalZero_finiteChart_ofReal
    (D : ℕ) (θ : BoundedRealSequence) (a : Fin D) :
    ContDiff ℝ ⊤
      (fun p : Fin D → ℝ =>
        (movingCanonicalZero
          (movingCanonicalFiniteChart D θ p) a.1 : ℂ)) :=
  Complex.ofRealCLM.contDiff.comp
    (contDiff_movingCanonicalZero_finiteChart D θ a)

theorem contDiff_movingCanonicalDifferentialJetTerm_finiteChart
    (D : ℕ) (θ : BoundedRealSequence)
    (k : ℕ) (a : Fin D) {z : ℂ} (hz : 0 < z.im) :
    ContDiff ℝ ⊤
      (fun p : Fin D → ℝ =>
        movingCanonicalDifferentialJetTerm
          (movingCanonicalFiniteChart D θ p) k a.1 z) := by
  have htanh : ContDiff ℝ ⊤ Real.tanh := by
    have hneg : ContDiff ℝ ⊤ (fun x : ℝ => -x) := contDiff_id.neg
    have hexpNeg : ContDiff ℝ ⊤ (fun x : ℝ => Real.exp (-x)) :=
      Real.contDiff_exp.comp hneg
    have hquot : ContDiff ℝ ⊤
        (fun x : ℝ =>
          (Real.exp x - Real.exp (-x)) /
            (Real.exp x + Real.exp (-x))) :=
      (Real.contDiff_exp.sub hexpNeg).div
        (Real.contDiff_exp.add hexpNeg)
        (fun x => ne_of_gt (add_pos (Real.exp_pos x) (Real.exp_pos (-x))))
    convert hquot using 1
    funext x
    exact Real.tanh_eq x
  have hzero : ContDiff ℝ ⊤
      (fun p : Fin D → ℝ =>
        movingCanonicalZero (movingCanonicalFiniteChart D θ p) a.1) := by
    have hcoord : ContDiff ℝ ⊤
        (fun p : Fin D → ℝ => θ a.1 + p a) :=
      contDiff_const.add
        (ContinuousLinearMap.proj a :
          (Fin D → ℝ) →L[ℝ] ℝ).contDiff
    have hcomp := htanh.comp hcoord
    unfold movingCanonicalZero canonicalZeroDisplacement
    simp only [movingCanonicalFiniteChart_apply, dif_pos a.2]
    exact contDiff_const.add (contDiff_const.mul hcomp)
  have hzeroC : ContDiff ℝ ⊤
      (fun p : Fin D → ℝ =>
        (movingCanonicalZero
          (movingCanonicalFiniteChart D θ p) a.1 : ℂ)) := by
    exact Complex.ofRealCLM.contDiff.comp hzero
  have hsep : ∀ p : Fin D → ℝ,
      (movingCanonicalZero
        (movingCanonicalFiniteChart D θ p) a.1 : ℂ) - z ≠ 0 := by
    intro p h
    have him := congrArg Complex.im h
    simp at him
    exact (ne_of_gt hz) him
  have hne : ∀ p : Fin D → ℝ,
      (movingCanonicalZero
        (movingCanonicalFiniteChart D θ p) a.1 : ℂ) ≠ 0 := by
    intro p
    exact Complex.ofReal_ne_zero.mpr
      (ne_of_gt (movingCanonicalZero_pos
        (movingCanonicalFiniteChart D θ p) a.1))
  by_cases hk : k = 0
  · subst k
    simp only [movingCanonicalDifferentialJetTerm, if_pos,
      movingCanonicalRegularizedTerm]
    fun_prop
  · simp only [movingCanonicalDifferentialJetTerm, if_neg hk]
    fun_prop

theorem contDiff_movingCanonicalFiniteActualJetFamily
    {ι : Type*} [Fintype ι]
    (x : ι → ℂ) (hupper : ∀ i, 0 < (x i).im)
    (n : ι → ℕ) (θ : BoundedRealSequence) :
    ContDiff ℝ ⊤ (movingCanonicalFiniteActualJetFamily x n θ) := by
  rw [contDiff_pi]
  intro s
  let D := movingCanonicalLocationProbeCard n
  have hfun :
      (fun p : Fin D → ℝ =>
        movingCanonicalFiniteActualJetFamily x n θ p s) =
        fun p =>
          iteratedDeriv s.2.1
              (movingCanonicalLogDerivative θ) (x s.1) +
            ∑ a : Fin D,
              (movingCanonicalDifferentialJetTerm
                  (movingCanonicalFiniteChart D θ p)
                  s.2.1 a.1 (x s.1) -
                movingCanonicalDifferentialJetTerm
                  θ s.2.1 a.1 (x s.1)) := by
    funext p
    exact iteratedDeriv_movingCanonicalLogDerivative_finiteChart
      D θ p s.2.1 (hupper s.1)
  rw [hfun]
  apply contDiff_const.add
  simpa only [Finset.sum_const_zero, add_zero] using
    (ContDiff.sum (s := (Finset.univ : Finset (Fin D)))
      (fun a _ =>
        (contDiff_movingCanonicalDifferentialJetTerm_finiteChart
          D θ s.2.1 a (hupper s.1)).sub contDiff_const))

theorem fderiv_movingCanonicalFiniteActualJetFamily
    {ι : Type*} [Fintype ι]
    (x : ι → ℂ) (hupper : ∀ i, 0 < (x i).im)
    (n : ι → ℕ) (θ : BoundedRealSequence)
    (p : Fin (movingCanonicalLocationProbeCard n) → ℝ) :
    fderiv ℝ (movingCanonicalFiniteActualJetFamily x n θ) p =
      movingCanonicalFiniteParameterJetCLM x n
        (movingCanonicalFiniteChart
          (movingCanonicalLocationProbeCard n) θ p) :=
  (movingCanonicalFiniteActualJetFamily_hasFDerivAt
    x hupper n θ p).fderiv

theorem movingCanonicalFiniteParameterJetCLM_surjective
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (x : ι → ℂ) (hx : Function.Injective x)
    (hupper : ∀ i, 0 < (x i).im)
    (n : ι → ℕ) (θ : BoundedRealSequence) :
    Function.Surjective
      (movingCanonicalFiniteParameterJetCLM x n θ) := by
  intro y
  obtain ⟨p, hp⟩ :=
    movingCanonicalFiniteParameterJetLinearMap_surjective
      x hx hupper n θ y
  refine ⟨p, ?_⟩
  exact hp

theorem fderiv_movingCanonicalFiniteActualJetFamily_surjective
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (x : ι → ℂ) (hx : Function.Injective x)
    (hupper : ∀ i, 0 < (x i).im)
    (n : ι → ℕ) (θ : BoundedRealSequence)
    (p : Fin (movingCanonicalLocationProbeCard n) → ℝ) :
    Function.Surjective
      (fderiv ℝ (movingCanonicalFiniteActualJetFamily x n θ) p) := by
  rw [fderiv_movingCanonicalFiniteActualJetFamily x hupper n θ p]
  exact movingCanonicalFiniteParameterJetCLM_surjective
    x hx hupper n
      (movingCanonicalFiniteChart
        (movingCanonicalLocationProbeCard n) θ p)

end

end GaloisForLFunctions.HTGeometry
