import GaloisForLFunctions.RHTower.SuzukiCausalDepthGammaFiniteSectionNakedTraceCollapseNoGo
import GaloisForLFunctions.RHTower.SoninFiniteRankWardBoundaryEnergy
import GaloisForLFunctions.RHTower.SoninResidualApertureHilbertSchmidtContinuity
import GaloisForLFunctions.HTGeometry.BoundedBelowRangeProjection

/-!
# Projection-cutoff anomaly no-go for the causal-depth Gamma feature

An orthogonal projection cannot amplify Hilbert--Schmidt source energy: the squared
Hilbert--Schmidt norm of its commutator with a source is at most twice the source energy.  Hence a
moving source whose energy is sublinear on the Suzuki transition-core mesh cannot manufacture the
linear correction required by rectangular Ward semiboundedness, regardless of cutoff rank, motion,
nesting, or convergence rate.  Conversely, any successful projection anomaly forces the source
itself to carry linear Hilbert--Schmidt energy.

For a fixed Hilbert--Schmidt source the obstruction is stronger.  Every family of orthogonal
cutoffs converging strongly to the identity has commutator energy tending to zero.  In particular,
no moving orthogonal cutoff of the actual fixed causal-depth Gamma feature can close the positive
transition-core Ward premise.

All statements are unconditional.  They use no RH premise, zero-location information, numerical
computation, asymptotic interchange, finite-rank hypothesis, or added axiom.
-/

open Complex Filter ContinuousLinearMap
open scoped Topology
open GaloisForLFunctions.HTGeometry
open GaloisForLFunctions.RHTower

namespace RHTower

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Every orthogonal projection has operator norm at most one, including the zero projection. -/
theorem opNorm_le_one_of_adjoint_eq_self_of_mul_self_eq
    (Q : H →L[ℂ] H) (hQ : adjoint Q = Q) (hQ2 : Q * Q = Q) :
    ‖Q‖ ≤ 1 := by
  refine ContinuousLinearMap.opNorm_le_bound Q (by norm_num) fun x => ?_
  have hself : IsSelfAdjoint Q := hQ
  have hidem : IsIdempotentElem Q := hQ2
  simpa using HTGeometry.norm_apply_le_of_isSelfAdjoint_isIdempotentElem hself hidem x

/-- The complement of every orthogonal projection has operator norm at most one. -/
theorem one_sub_opNorm_le_one_of_adjoint_eq_self_of_mul_self_eq
    (Q : H →L[ℂ] H) (hQ : adjoint Q = Q) (hQ2 : Q * Q = Q) :
    ‖1 - Q‖ ≤ 1 := by
  have hAdj : adjoint (1 - Q) = 1 - Q := by
    rw [map_sub, hQ]
    congr 1
    exact ContinuousLinearMap.adjoint_id
  have hIdem : (1 - Q) * (1 - Q) = 1 - Q := by
    rw [show (1 - Q) * (1 - Q) = 1 - Q - Q + Q * Q by noncomm_ring, hQ2]
    noncomm_ring
  exact opNorm_le_one_of_adjoint_eq_self_of_mul_self_eq (1 - Q) hAdj hIdem

set_option maxHeartbeats 1000000 in
/-- **Projection-commutator capacity law.** An orthogonal cutoff can expose at most twice the
Hilbert--Schmidt energy already carried by the source. -/
theorem hsNormSq_ccmCommutator_le_two_mul
    (F Q : H →L[ℂ] H) (hF : IsHilbertSchmidt F)
    (hQ : adjoint Q = Q) (hQ2 : Q * Q = Q) :
    hsNormSq (ccmCommutator F Q) ≤ 2 * hsNormSq F := by
  rw [hsNormSq_commutator_eq_boundary_sum_of_hilbertSchmidt Q F hQ2 hQ hF]
  have hQnorm := opNorm_le_one_of_adjoint_eq_self_of_mul_self_eq Q hQ hQ2
  have hQcnorm := one_sub_opNorm_le_one_of_adjoint_eq_self_of_mul_self_eq Q hQ hQ2
  have hQsq : ‖Q‖ ^ 2 ≤ 1 := by nlinarith [norm_nonneg Q]
  have hQcsq : ‖1 - Q‖ ^ 2 ≤ 1 := by nlinarith [norm_nonneg (1 - Q)]
  have hLowerBase : IsHilbertSchmidt ((1 - Q) * F) := hF.comp_left (1 - Q)
  have hUpperBase : IsHilbertSchmidt (F * (1 - Q)) := hF.comp_right (1 - Q)
  have hLowerRight :
      hsNormSq (((1 - Q) * F) ∘L Q) ≤ hsNormSq ((1 - Q) * F) := by
    calc
      hsNormSq (((1 - Q) * F) ∘L Q) ≤
          ‖Q‖ ^ 2 * hsNormSq ((1 - Q) * F) :=
        hsNormSq_comp_right_le (T := (1 - Q) * F) hLowerBase Q
      _ ≤ 1 * hsNormSq ((1 - Q) * F) :=
        mul_le_mul_of_nonneg_right hQsq (hsNormSq_nonneg _)
      _ = hsNormSq ((1 - Q) * F) := by ring
  have hLowerLeft : hsNormSq ((1 - Q) ∘L F) ≤ hsNormSq F := by
    calc
      hsNormSq ((1 - Q) ∘L F) ≤ ‖1 - Q‖ ^ 2 * hsNormSq F :=
        hsNormSq_comp_left_le (T := F) hF (1 - Q)
      _ ≤ 1 * hsNormSq F :=
        mul_le_mul_of_nonneg_right hQcsq (hsNormSq_nonneg _)
      _ = hsNormSq F := by ring
  have hLower : hsNormSq ((1 - Q) * F * Q) ≤ hsNormSq F :=
    hLowerRight.trans hLowerLeft
  have hUpperLeft : hsNormSq (Q ∘L (F * (1 - Q))) ≤ hsNormSq (F * (1 - Q)) := by
    calc
      hsNormSq (Q ∘L (F * (1 - Q))) ≤ ‖Q‖ ^ 2 * hsNormSq (F * (1 - Q)) :=
        hsNormSq_comp_left_le (T := F * (1 - Q)) hUpperBase Q
      _ ≤ 1 * hsNormSq (F * (1 - Q)) :=
        mul_le_mul_of_nonneg_right hQsq (hsNormSq_nonneg _)
      _ = hsNormSq (F * (1 - Q)) := by ring
  have hUpperRight : hsNormSq (F ∘L (1 - Q)) ≤ hsNormSq F := by
    calc
      hsNormSq (F ∘L (1 - Q)) ≤ ‖1 - Q‖ ^ 2 * hsNormSq F :=
        hsNormSq_comp_right_le (T := F) hF (1 - Q)
      _ ≤ 1 * hsNormSq F :=
        mul_le_mul_of_nonneg_right hQcsq (hsNormSq_nonneg _)
      _ = hsNormSq F := by ring
  have hUpper : hsNormSq (Q * F * (1 - Q)) ≤ hsNormSq F := by
    rw [mul_assoc]
    exact hUpperLeft.trans hUpperRight
  exact add_le_add hLower hUpper |>.trans_eq (by ring)

/-- Hilbert--Schmidt energy carried by a moving cutoff reporter. -/
def suzukiProjectionCutoffCommutatorAnomaly
    (F Q : ℕ → H →L[ℂ] H) (N : ℕ) : ℝ :=
  hsNormSq (ccmCommutator (F N) (Q N))

/-- A moving source has sublinear Hilbert--Schmidt energy on the transition-core mesh. -/
def SuzukiProjectionCutoffSourceHSEnergySublinear
    (F : ℕ → H →L[ℂ] H) : Prop :=
  Tendsto (fun n : ℕ => hsNormSq (F (8 * n)) / (n : ℝ)) atTop (nhds 0)

/-- Orthogonal cutoffs cannot amplify sublinear source Hilbert--Schmidt energy into a linear
transition-core correction. -/
theorem suzukiProjectionCutoffCommutatorAnomaly_sublinear
    (F Q : ℕ → H →L[ℂ] H)
    (hF : ∀ N, IsHilbertSchmidt (F N))
    (hQ : ∀ N, adjoint (Q N) = Q N)
    (hQ2 : ∀ N, Q N * Q N = Q N)
    (hsource : SuzukiProjectionCutoffSourceHSEnergySublinear F) :
    SuzukiTransitionCoreCorrectionSublinear
      (suzukiProjectionCutoffCommutatorAnomaly F Q) := by
  rw [SuzukiTransitionCoreCorrectionSublinear]
  have hlimit : Tendsto
      (fun n : ℕ => 2 * hsNormSq (F (8 * n)) / (n : ℝ)) atTop (nhds 0) := by
    simpa [SuzukiProjectionCutoffSourceHSEnergySublinear, mul_div_assoc] using
      (tendsto_const_nhds.mul hsource)
  refine squeeze_zero (fun n => div_nonneg (hsNormSq_nonneg _) (Nat.cast_nonneg n))
    (fun n => ?_) hlimit
  exact div_le_div_of_nonneg_right
    (hsNormSq_ccmCommutator_le_two_mul (F (8 * n)) (Q (8 * n))
      (hF (8 * n)) (hQ (8 * n)) (hQ2 (8 * n)))
    (Nat.cast_nonneg n)

/-- **Projection-cutoff anomaly no-go.** No Hilbert--Schmidt source with sublinear energy,
combined with any moving family of orthogonal cutoffs, can supply the semibounded rectangular Ward
premise for the positive Suzuki transition core. -/
theorem no_sublinear_hilbertSchmidt_projectionCutoff_rectangularWardProducer :
    ¬ ∃ (L : ℝ) (F Q : ℕ → H →L[ℂ] H) (lower : ℝ),
      (∀ N, IsHilbertSchmidt (F N)) ∧
      (∀ N, adjoint (Q N) = Q N) ∧
      (∀ N, Q N * Q N = Q N) ∧
      SuzukiProjectionCutoffSourceHSEnergySublinear F ∧
      ∀ᶠ n : ℕ in atTop,
        lower ≤ suzukiRectangularWardDefect L
          (fun N => suzukiNaturalApertureTransitionCoreCauchyEnergy N -
            suzukiProjectionCutoffCommutatorAnomaly F Q N)
          (8 * n) := by
  rintro ⟨L, F, Q, lower, hF, hQ, hQ2, hsource, hlower⟩
  exact no_sublinear_transitionCore_rectangularWardProducer
    ⟨L, suzukiProjectionCutoffCommutatorAnomaly F Q, lower,
      suzukiProjectionCutoffCommutatorAnomaly_sublinear F Q hF hQ hQ2 hsource,
      hlower⟩

/-- **Projection-anomaly capacity law.** If a cutoff commutator does leave the transition-core
Ward defect lower-semibounded, the moving source itself carries linear Hilbert--Schmidt energy.
Cutoff rank and motion cannot create that scale. -/
theorem eventually_linear_le_sourceHSEnergy_of_projectionCutoffWardDefect_bddBelow
    (L : ℝ) (F Q : ℕ → H →L[ℂ] H) (lower : ℝ)
    (hF : ∀ N, IsHilbertSchmidt (F N))
    (hQ : ∀ N, adjoint (Q N) = Q N)
    (hQ2 : ∀ N, Q N * Q N = Q N)
    (hlower : ∀ᶠ n : ℕ in atTop,
      lower ≤ suzukiRectangularWardDefect L
        (fun N => suzukiNaturalApertureTransitionCoreCauchyEnergy N -
          suzukiProjectionCutoffCommutatorAnomaly F Q N)
        (8 * n)) :
    ∀ᶠ n : ℕ in atTop, (n : ℝ) / 1152 ≤ hsNormSq (F (8 * n)) := by
  have hlinear :=
    eventually_linear_le_correction_of_transitionCoreWardDefect_bddBelow
      L (suzukiProjectionCutoffCommutatorAnomaly F Q) lower hlower
  filter_upwards [hlinear] with n hn
  have hcap := hsNormSq_ccmCommutator_le_two_mul
    (F (8 * n)) (Q (8 * n)) (hF (8 * n)) (hQ (8 * n)) (hQ2 (8 * n))
  dsimp [suzukiProjectionCutoffCommutatorAnomaly] at hn
  nlinarith

/-- Actual fixed causal-depth Gamma feature has sublinear source energy. -/
theorem suzukiCanonicalCausalDepthGammaFeatureOperator_projectionCutoffSourceHSEnergySublinear :
    SuzukiProjectionCutoffSourceHSEnergySublinear
      (fun _ : ℕ => suzukiCanonicalCausalDepthGammaFeatureOperator) := by
  rw [SuzukiProjectionCutoffSourceHSEnergySublinear]
  exact Tendsto.div_atTop tendsto_const_nhds
    (tendsto_natCast_atTop_atTop (R := ℝ))

/-- Every moving orthogonal cutoff of the actual fixed causal-depth Gamma feature is excluded from
the semibounded transition-core Ward producer class. -/
theorem no_canonicalCausalDepthGamma_projectionCutoff_rectangularWardProducer :
    ¬ ∃ (L : ℝ)
      (Q : ℕ → SuzukiCausalDepthGammaTraceL2 →L[ℂ]
        SuzukiCausalDepthGammaTraceL2) (lower : ℝ),
      (∀ N, adjoint (Q N) = Q N) ∧
      (∀ N, Q N * Q N = Q N) ∧
      ∀ᶠ n : ℕ in atTop,
        lower ≤ suzukiRectangularWardDefect L
          (fun N => suzukiNaturalApertureTransitionCoreCauchyEnergy N -
            suzukiProjectionCutoffCommutatorAnomaly
              (fun _ : ℕ => suzukiCanonicalCausalDepthGammaFeatureOperator) Q N)
          (8 * n) := by
  rintro ⟨L, Q, lower, hQ, hQ2, hlower⟩
  apply no_sublinear_hilbertSchmidt_projectionCutoff_rectangularWardProducer
    (H := SuzukiCausalDepthGammaTraceL2)
  exact ⟨L, (fun _ : ℕ => suzukiCanonicalCausalDepthGammaFeatureOperator), Q, lower,
    (fun _ => suzukiCanonicalCausalDepthGammaFeatureOperator_isHilbertSchmidt), hQ, hQ2,
    suzukiCanonicalCausalDepthGammaFeatureOperator_projectionCutoffSourceHSEnergySublinear,
    hlower⟩

/-- **Exhaustive-cutoff vanishing law.** If orthogonal cutoffs converge strongly to the identity,
the Hilbert--Schmidt commutator anomaly of every fixed Hilbert--Schmidt source converges to zero.
No rank, monotonicity, or convergence-rate hypothesis is required. -/
theorem tendsto_hsNormSq_ccmCommutator_projection_strong_id_zero
    (F : H →L[ℂ] H) (hF : IsHilbertSchmidt F)
    (Q : ℕ → H →L[ℂ] H)
    (hQ : ∀ N, adjoint (Q N) = Q N)
    (hQ2 : ∀ N, Q N * Q N = Q N)
    (hstrong : ∀ x : H, Tendsto (fun N => Q N x) atTop (nhds x)) :
    Tendsto (fun N => hsNormSq (ccmCommutator F (Q N))) atTop (nhds 0) := by
  let A : ℕ → H →L[ℂ] H := fun N => 1 - Q N
  have hAnorm : ∀ N, ‖A N‖ ≤ 1 := by
    intro N
    exact one_sub_opNorm_le_one_of_adjoint_eq_self_of_mul_self_eq
      (Q N) (hQ N) (hQ2 N)
  have hQnorm : ∀ N, ‖Q N‖ ≤ 1 := by
    intro N
    exact opNorm_le_one_of_adjoint_eq_self_of_mul_self_eq (Q N) (hQ N) (hQ2 N)
  have hAstrong : ∀ x : H, Tendsto (fun N => A N x) atTop (nhds 0) := by
    intro x
    have hconst : Tendsto (fun _ : ℕ => x) atTop (nhds x) := tendsto_const_nhds
    have hx := hconst.sub (hstrong x)
    simpa [A, sub_apply] using hx
  have hAadj : ∀ N, adjoint (A N) = A N := by
    intro N
    dsimp [A]
    rw [map_sub, hQ N]
    congr 1
    exact ContinuousLinearMap.adjoint_id
  have hAadjStrong : ∀ x : H,
      Tendsto (fun N => adjoint (A N) x) atTop (nhds 0) := by
    intro x
    convert hAstrong x using 1
    funext N
    rw [hAadj N]
  have hAF : Tendsto (fun N => hsNormSq (A N * F)) atTop (nhds 0) :=
    tendsto_hsNormSq_comp_left_zero_of_strong A F hF hAstrong
      zero_le_one hAnorm
  have hLower : Tendsto (fun N => hsNormSq (A N * F * Q N)) atTop (nhds 0) :=
    tendsto_hsNormSq_comp_right_zero_of_hsNormSq
      (fun N => A N * F) Q (fun N => hF.comp_left (A N)) hAF zero_le_one hQnorm
  have hFA : Tendsto (fun N => hsNormSq (F * A N)) atTop (nhds 0) :=
    tendsto_hsNormSq_comp_right_zero_of_adjoint_strong A F hF hAadjStrong
      zero_le_one hAnorm
  have hUpper : Tendsto (fun N => hsNormSq (Q N * (F * A N))) atTop (nhds 0) :=
    tendsto_hsNormSq_comp_left_zero_of_hsNormSq
      Q (fun N => F * A N) (fun N => hF.comp_right (A N)) hFA zero_le_one hQnorm
  have hsum : Tendsto
      (fun N => hsNormSq (A N * F * Q N) + hsNormSq (Q N * (F * A N)))
      atTop (nhds 0) := by
    simpa using hLower.add hUpper
  refine hsum.congr' ?_
  filter_upwards [] with N
  have hsplit := hsNormSq_commutator_eq_boundary_sum_of_hilbertSchmidt
    (Q N) F (hQ2 N) (hQ N) hF
  simpa [A, crossBoundary, upperBoundary, mul_assoc] using hsplit.symm

end

end RHTower
