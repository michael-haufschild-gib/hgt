import GaloisForLFunctions.HTGeometry.MovingCanonicalFiniteJetSubmersion
import GaloisForLFunctions.HTGeometry.MovingDivisorJetControllability
import GaloisForLFunctions.HTGeometry.MovingDivisorProduct

/-!
# Finite jet data of a moving divisor

The finite chart of the bounded parameter is divisor-independent, so only the location derivative
and the normalized differential jets of the carrier have to be transported to a general moving
divisor: the chart derivative, the continuity of every jet term in the parameter and the evaluation
point, and the summability of every differentiated pole series in the upper half-plane.
-/

namespace GaloisForLFunctions.HTGeometry

open Set Topology Filter
open scoped ENNReal

noncomputable section

namespace MovingDivisor

/-- The locations of the divisor at a bounded parameter. -/
def zeroAt (Dv : MovingDivisor) (θ : BoundedRealSequence) (a : ℕ) : ℝ :=
  Dv.zero (θ : ℕ → ℝ) a

theorem zeroAt_pos (Dv : MovingDivisor) (θ : BoundedRealSequence) (a : ℕ) :
    0 < Dv.zeroAt θ a := Dv.zero_pos _ a

theorem summable_zeroAt_inv_norm_sq (Dv : MovingDivisor) (θ : BoundedRealSequence) :
    Summable (fun a => 1 / ‖(Dv.zeroAt θ a : ℂ)‖ ^ 2) :=
  Dv.summable_inv_norm_sq _

/-- The location derivative along the finite chart of the bounded parameter. -/
theorem zeroAt_finiteChart_hasFDerivAt
    (Dv : MovingDivisor) (D : ℕ) (θ : BoundedRealSequence) (p : Fin D → ℝ) (a : Fin D) :
    HasNormedFDerivAt
      (fun q : Fin D → ℝ => Dv.zeroAt (movingCanonicalFiniteChart D θ q) a.1)
      (Dv.coordinateSpeed a.1 (θ a.1 + p a) •
        (ContinuousLinearMap.proj a : (Fin D → ℝ) →L[ℝ] ℝ)) p := by
  have hcoord : HasFDerivAt (fun q : Fin D → ℝ => θ a.1 + q a)
      (ContinuousLinearMap.proj a : (Fin D → ℝ) →L[ℝ] ℝ) p :=
    (ContinuousLinearMap.proj a : (Fin D → ℝ) →L[ℝ] ℝ).hasFDerivAt.const_add (θ a.1)
  have hdisp := (Dv.coordinate_hasDerivAt a.1 (θ a.1 + p a)).comp_hasFDerivAt p hcoord
  have hfun : (fun q : Fin D → ℝ => Dv.zeroAt (movingCanonicalFiniteChart D θ q) a.1)
      = (fun s : ℝ => Dv.base a.1 + Dv.radius a.1 * Real.tanh s) ∘ (fun q => θ a.1 + q a) := by
    funext q
    simp only [Function.comp_apply, MovingDivisor.zeroAt, MovingDivisor.zero,
      movingCanonicalFiniteChart_apply, dif_pos a.2]
  rw [hfun]
  exact hdisp

/-- The regularized pole term of the divisor. -/
def regularizedTerm (Dv : MovingDivisor) (θ : BoundedRealSequence) (a : ℕ) (z : ℂ) : ℂ :=
  ((Dv.zeroAt θ a : ℂ) - z)⁻¹ - (Dv.zeroAt θ a : ℂ)⁻¹

/-- The normalized differential jet terms of the carrier. -/
def normalizedJetTerm (Dv : MovingDivisor) (θ : BoundedRealSequence) (k : ℕ) (a : ℕ) (z : ℂ) : ℂ :=
  if k = 0 then Dv.regularizedTerm θ a z
  else (((Dv.zeroAt θ a : ℂ) - z)⁻¹) ^ (k + 1)

/-- The normalized differential jets of the carrier. -/
def normalizedJet (Dv : MovingDivisor) (θ : BoundedRealSequence) (k : ℕ) (z : ℂ) : ℂ :=
  ∑' a, Dv.normalizedJetTerm θ k a z

@[simp]
theorem normalizedJet_zero (Dv : MovingDivisor) (θ : BoundedRealSequence) (z : ℂ) :
    Dv.normalizedJet θ 0 z = Dv.logDerivative (θ : ℕ → ℝ) z := by
  apply tsum_congr
  intro a
  rfl

theorem continuous_zeroAt_coordinate (Dv : MovingDivisor) (a : ℕ) :
    Continuous (fun θ : BoundedRealSequence => Dv.zeroAt θ a) := by
  have heval : Continuous (fun u : BoundedRealSequence => (u : ℕ → ℝ) a) :=
    (lp.evalCLM ℝ (fun _ : ℕ => ℝ) ∞ a).continuous
  have htanh : Continuous Real.tanh := by
    have heq : Real.tanh = fun x => Real.sinh x / Real.cosh x := by
      funext x
      rw [Real.tanh_eq_sinh_div_cosh]
    rw [heq]
    exact Real.continuous_sinh.div Real.continuous_cosh (fun x => (Real.cosh_pos x).ne')
  exact continuous_const.add (continuous_const.mul (htanh.comp heval))

theorem continuousOn_normalizedJetTerm (Dv : MovingDivisor) (k a : ℕ) :
    ContinuousOn
      (fun p : BoundedRealSequence × ℂ => Dv.normalizedJetTerm p.1 k a p.2)
      (Set.univ ×ˢ upperHalfPlane) := by
  intro p hp
  have hzeroR : ContinuousAt
      (fun q : BoundedRealSequence × ℂ => Dv.zeroAt q.1 a) p :=
    (Dv.continuous_zeroAt_coordinate a).continuousAt.comp continuousAt_fst
  have hzero : ContinuousAt
      (fun q : BoundedRealSequence × ℂ => (Dv.zeroAt q.1 a : ℂ)) p :=
    Complex.continuous_ofReal.continuousAt.comp hzeroR
  have hsub : ContinuousAt
      (fun q : BoundedRealSequence × ℂ => (Dv.zeroAt q.1 a : ℂ) - q.2) p :=
    hzero.sub continuousAt_snd
  have hne : (Dv.zeroAt p.1 a : ℂ) - p.2 ≠ 0 := by
    intro h
    have him := congrArg Complex.im h
    simp at him
    exact (ne_of_gt hp.2) him
  have hzeroNe : (Dv.zeroAt p.1 a : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (ne_of_gt (Dv.zeroAt_pos p.1 a))
  unfold normalizedJetTerm regularizedTerm
  split_ifs
  · exact ((hsub.inv₀ hne).sub (hzero.inv₀ hzeroNe)).continuousWithinAt
  · exact ((hsub.inv₀ hne).pow _).continuousWithinAt

theorem summable_cauchyPower
    (Dv : MovingDivisor) (θ : BoundedRealSequence) (m : ℕ) {z : ℂ} (hz : 0 < z.im) :
    Summable (fun a =>
      (((Dv.zeroAt θ a : ℂ) - z)⁻¹) ^ (m + 2)) := by
  let C : ℝ := 1 + ‖z‖ / z.im
  have hC : 0 ≤ C := by
    dsimp [C]
    positivity
  have hmajor : Summable (fun a =>
      (C ^ 2 * (z.im)⁻¹ ^ m) *
        (1 / ‖(Dv.zeroAt θ a : ℂ)‖ ^ 2)) :=
    (Dv.summable_zeroAt_inv_norm_sq θ).mul_left
      (C ^ 2 * (z.im)⁻¹ ^ m)
  apply hmajor.of_norm_bounded
  intro a
  let A : ℝ := ‖(Dv.zeroAt θ a : ℂ)‖
  let d : ℝ := ‖(Dv.zeroAt θ a : ℂ) - z‖
  have hApos : 0 < A := norm_pos_iff.mpr
    (Complex.ofReal_ne_zero.mpr (ne_of_gt (Dv.zeroAt_pos θ a)))
  have hdpos : 0 < d := by
    rw [norm_pos_iff]
    intro h
    have him := congrArg Complex.im h
    simp at him
    exact (ne_of_gt hz) him
  have hyd : z.im ≤ d := by
    have hi := Complex.abs_im_le_norm
      ((Dv.zeroAt θ a : ℂ) - z)
    have him :
        ((Dv.zeroAt θ a : ℂ) - z).im = -z.im := by simp
    rw [him, abs_neg, abs_of_pos hz] at hi
    exact hi
  have hAz : A ≤ d + ‖z‖ := by
    calc
      A = ‖(Dv.zeroAt θ a : ℂ)‖ := rfl
      _ = ‖((Dv.zeroAt θ a : ℂ) - z) + z‖ := by
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
theorem summable_normalizedJetTerm
    (Dv : MovingDivisor) (θ : BoundedRealSequence) (k : ℕ) {z : ℂ} (hz : 0 < z.im) :
    Summable (fun a => Dv.normalizedJetTerm θ k a z) := by
  by_cases hk : k = 0
  · subst k
    simpa [normalizedJetTerm, regularizedTerm, zeroAt] using
      Dv.summable_logDerivative (θ : ℕ → ℝ) (fun a h => by
        have him := congrArg Complex.im h
        simp at him
        exact (ne_of_gt hz) him)
  · obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk
    simpa [normalizedJetTerm] using
      Dv.summable_cauchyPower θ m hz


theorem normalizedJet_finiteChart
    (Dv : MovingDivisor) (D : ℕ) (θ : BoundedRealSequence) (p : Fin D → ℝ)
    (k : ℕ) {z : ℂ} (hz : 0 < z.im) :
    Dv.normalizedJet (movingCanonicalFiniteChart D θ p) k z =
      Dv.normalizedJet θ k z +
        ∑ a : Fin D,
          (Dv.normalizedJetTerm (movingCanonicalFiniteChart D θ p) k a.1 z -
            Dv.normalizedJetTerm θ k a.1 z) := by
  let fnew : ℕ → ℂ := fun a =>
    Dv.normalizedJetTerm (movingCanonicalFiniteChart D θ p) k a z
  let fold : ℕ → ℂ := fun a =>
    Dv.normalizedJetTerm θ k a z
  have hnew : Summable fnew :=
    Dv.summable_normalizedJetTerm (movingCanonicalFiniteChart D θ p) k hz
  have hold : Summable fold :=
    Dv.summable_normalizedJetTerm θ k hz
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
        Dv.zeroAt (movingCanonicalFiniteChart D θ p) a.1 =
          Dv.zeroAt θ a.1 := by
      simp only [MovingDivisor.zeroAt, MovingDivisor.zero, hchart]
    simp only [fnew, fold]
    rw [show Dv.normalizedJetTerm (movingCanonicalFiniteChart D θ p) k a.1 z =
        Dv.normalizedJetTerm θ k a.1 z by
          simp [MovingDivisor.normalizedJetTerm, MovingDivisor.regularizedTerm, hzero]]
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
theorem analyticAt_logDerivative
    (Dv : MovingDivisor) (θ : BoundedRealSequence) {z : ℂ} (hz : 0 < z.im) :
    AnalyticAt ℂ (Dv.logDerivative (θ : ℕ → ℝ)) z := by
  have hproduct : AnalyticAt ℂ (Dv.canonicalProduct (θ : ℕ → ℝ)) z :=
    Dv.canonicalProduct_analytic (θ : ℕ → ℝ) z (Set.mem_univ z)
  have hproductNe : Dv.canonicalProduct (θ : ℕ → ℝ) z ≠ 0 := by
    intro hzero
    obtain ⟨a, ha⟩ :=
      (Dv.canonicalProduct_eq_zero_iff (θ : ℕ → ℝ) z).mp hzero
    have him := congrArg Complex.im ha
    simp at him
    exact (ne_of_gt hz) him
  have hlog : AnalyticAt ℂ
      (fun w => -logDeriv (Dv.canonicalProduct (θ : ℕ → ℝ)) w) z := by
    have hquot : AnalyticAt ℂ
        (fun w => deriv (Dv.canonicalProduct (θ : ℕ → ℝ)) w /
          Dv.canonicalProduct (θ : ℕ → ℝ) w) z :=
      hproduct.deriv.div hproduct hproductNe
    change AnalyticAt ℂ
      (fun w => -(deriv (Dv.canonicalProduct (θ : ℕ → ℝ)) w /
        Dv.canonicalProduct (θ : ℕ → ℝ) w)) z
    exact hquot.neg
  refine hlog.congr ?_
  filter_upwards [isOpen_upperHalfPlane.mem_nhds hz] with w hw
  exact Dv.neg_logDeriv_canonicalProduct_eq (θ : ℕ → ℝ) (fun a ha => by
    have him := congrArg Complex.im ha
    simp at him
    exact (ne_of_gt hw) him)

/-- Every actual differential jet of the canonical carrier remains analytic in the node. -/
theorem analyticAt_iteratedDeriv_logDerivative
    (Dv : MovingDivisor) (θ : BoundedRealSequence) (k : ℕ) {z : ℂ} (hz : 0 < z.im) :
    AnalyticAt ℂ (iteratedDeriv k (Dv.logDerivative (θ : ℕ → ℝ))) z := by
  induction k with
  | zero =>
      simpa [iteratedDeriv_zero] using
        Dv.analyticAt_logDerivative θ hz
  | succ k ih =>
      rw [iteratedDeriv_succ]
      exact ih.deriv


end MovingDivisor

end

end GaloisForLFunctions.HTGeometry
