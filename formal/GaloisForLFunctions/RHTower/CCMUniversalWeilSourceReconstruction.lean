import GaloisForLFunctions.RHTower.XiHurwitzOrientationSeparatedSourceReconstruction
import GaloisForLFunctions.RHTower.CCMRectangularWeilCompleteness

/-!
# Universal continued-source reconstruction of Xi--Weil evaluations

Every multiplicity-safe square-summable evaluation on the centered Xi divisor decomposes into
complete spectral fibers.  Normalized Cauchy pole exhaustion places each such fiber in the
Hilbert closure of the analytically continued prime--Gamma source core.  Pairwise-separated finite
Cauchy packets therefore approximate every Xi--Weil evaluation, and their exact finite source
energies converge to the corresponding Weil quadratic value.

For the fixed rectangular logarithmic family this produces one cofinal sequence of explicit
finite source packets with error smaller than `1/(n+1)`.  Eventual lower boundedness of any such
section is equivalent to RH.  The packet section is selected through target-side Hilbert closure;
the theorem does not supply the remaining source-only or semilocal selection mechanism.
-/

open Complex Metric Function Filter Topology
open scoped BigOperators

namespace RHTower

noncomputable section

def xiWeilEvaluationFiberVector
    (F : ℂ → ℂ) (ρ : XiDivisorSupport) :
    lp (fun _ : XiZeroCopy => ℂ) 2 :=
  F (xiSpectralPointSupport ρ) •
    xiWeilFiberIndicatorLp (xiSpectralPointSupport ρ)

theorem xiWeilEvaluationFiberVector_mem_continuedCauchyHilbertSubspace
    (F : ℂ → ℂ) (ρ : XiDivisorSupport) :
    xiWeilEvaluationFiberVector F ρ ∈
      xiWeilContinuedCauchyHilbertSubspace := by
  apply xiWeilContinuedCauchyHilbertSubspace.smul_mem
  simpa only [xiSpectralPoint_eq_support] using!
    xiWeilFiberIndicatorLp_mem_continuedCauchyHilbertSubspace
      (xiFirstZeroCopy ρ)

theorem sum_xiWeilEvaluation_single_fiber
    (F : ℂ → ℂ) (ρ : XiDivisorSupport) :
    (∑ j : Fin (Int.toNat ((MeromorphicOn.divisor xi Set.univ) (ρ : ℂ))),
      lp.single 2 (⟨ρ, j⟩ : XiZeroCopy)
        (F (xiSpectralPoint (⟨ρ, j⟩ : XiZeroCopy)))) =
      xiWeilEvaluationFiberVector F ρ := by
  apply Subtype.ext
  funext q
  rcases q with ⟨τ, k⟩
  simp only [lp.coeFn_sum, Finset.sum_apply]
  by_cases hτρ : τ = ρ
  · subst τ
    have hleft :
        (∑ j : Fin (Int.toNat ((MeromorphicOn.divisor xi Set.univ) (ρ : ℂ))),
          (lp.single (E := fun _ : XiZeroCopy => ℂ) 2 (⟨ρ, j⟩ : XiZeroCopy)
            (F (xiSpectralPoint (⟨ρ, j⟩ : XiZeroCopy))))
              (⟨ρ, k⟩ : XiZeroCopy)) =
          F (xiSpectralPoint (⟨ρ, k⟩ : XiZeroCopy)) := by
      rw [Fintype.sum_eq_single k]
      · rw [lp.single_apply_self]
      · intro j hj
        rw [lp.single_apply_ne]
        intro heq
        apply hj
        cases heq
        rfl
    rw [hleft]
    simp [xiWeilEvaluationFiberVector, xiWeilFiberIndicatorLp_apply,
      xiSpectralPoint_eq_support]
  · have hspec : xiSpectralPointSupport τ ≠ xiSpectralPointSupport ρ := by
      intro heq
      exact hτρ (xiSpectralPointSupport_injective heq)
    have hleft :
        (∑ j : Fin (Int.toNat ((MeromorphicOn.divisor xi Set.univ) (ρ : ℂ))),
          (lp.single (E := fun _ : XiZeroCopy => ℂ) 2 (⟨ρ, j⟩ : XiZeroCopy)
            (F (xiSpectralPoint (⟨ρ, j⟩ : XiZeroCopy))))
              (⟨τ, k⟩ : XiZeroCopy)) = 0 := by
      apply Finset.sum_eq_zero
      intro j _hj
      rw [lp.single_apply_ne]
      intro heq
      have hfst := congrArg Sigma.fst heq
      exact hτρ hfst
    rw [hleft]
    simp [xiWeilEvaluationFiberVector, xiWeilFiberIndicatorLp_apply,
      xiSpectralPoint_eq_support, hspec]

theorem hasSum_xiWeilEvaluationFiberVector
    (F : ℂ → ℂ) (hF : XiWeilSquareSummable F) :
    HasSum (xiWeilEvaluationFiberVector F) (xiWeilEvaluationLp F hF) := by
  let f : XiZeroCopy → lp (fun _ : XiZeroCopy => ℂ) 2 := fun q =>
    lp.single 2 q (xiWeilEvaluationLp F hF q)
  have hall : HasSum f (xiWeilEvaluationLp F hF) :=
    lp.hasSum_single (by norm_num : (2 : ENNReal) ≠ ⊤) (xiWeilEvaluationLp F hF)
  apply hall.sigma
  intro ρ
  rw [← sum_xiWeilEvaluation_single_fiber F ρ]
  simpa only [f, xiWeilEvaluationLp_apply] using
    (hasSum_fintype (fun j : Fin (Int.toNat
      ((MeromorphicOn.divisor xi Set.univ) (ρ : ℂ))) =>
        lp.single (E := fun _ : XiZeroCopy => ℂ) 2 (⟨ρ, j⟩ : XiZeroCopy)
          (F (xiSpectralPoint (⟨ρ, j⟩ : XiZeroCopy)))))

theorem xiWeilEvaluationLp_mem_continuedCauchyHilbertSubspace
    (F : ℂ → ℂ) (hF : XiWeilSquareSummable F) :
    xiWeilEvaluationLp F hF ∈ xiWeilContinuedCauchyHilbertSubspace := by
  have hmem : (∑' ρ : XiDivisorSupport, xiWeilEvaluationFiberVector F ρ) ∈
      xiWeilContinuedCauchyHilbertSubspace :=
    tsum_mem
      (Submodule.isClosed_topologicalClosure
        xiWeilContinuedCauchyAlgebraicSubspace)
      (xiWeilEvaluationFiberVector_mem_continuedCauchyHilbertSubspace F)
  rw [(hasSum_xiWeilEvaluationFiberVector F hF).tsum_eq] at hmem
  exact hmem

theorem xiWeilEvaluationLp_mem_closure_separatedPacketEvaluations
    (F : ℂ → ℂ) (hF : XiWeilSquareSummable F) :
    xiWeilEvaluationLp F hF ∈
      closure xiSeparatedContinuedCauchyPacketEvaluationSet := by
  have hclosure : closure
      (xiWeilContinuedCauchyAlgebraicSubspace :
        Set (lp (fun _ : XiZeroCopy => ℂ) 2)) ⊆
      closure xiSeparatedContinuedCauchyPacketEvaluationSet :=
    closure_minimal
      continuedCauchyAlgebraicSubspace_le_closure_separatedPacketEvaluations
      isClosed_closure
  exact hclosure (xiWeilEvaluationLp_mem_continuedCauchyHilbertSubspace F hF)

theorem exists_separatedContinuedCauchyPackets_tendsto_evaluation
    (F : ℂ → ℂ) (hF : XiWeilSquareSummable F) :
    ∃ P : ℕ → XiSeparatedContinuedCauchyPacket,
      Tendsto (fun n => (P n).evaluation) atTop
        (nhds (xiWeilEvaluationLp F hF)) := by
  have hclosure := xiWeilEvaluationLp_mem_closure_separatedPacketEvaluations F hF
  have happ : ∀ n : ℕ, ∃ v,
      v ∈ xiSeparatedContinuedCauchyPacketEvaluationSet ∧
      dist (xiWeilEvaluationLp F hF) v < 1 / ((n : ℝ) + 1) := by
    intro n
    exact Metric.mem_closure_iff.mp hclosure _ (by positivity)
  choose v hv hdist using happ
  choose P hP using hv
  refine ⟨P, Metric.tendsto_atTop.mpr ?_⟩
  intro ε hε
  obtain ⟨N, hN⟩ := exists_nat_one_div_lt hε
  refine ⟨N, fun n hn => ?_⟩
  have hden : (N : ℝ) + 1 ≤ (n : ℝ) + 1 := by
    exact_mod_cast Nat.add_le_add_right hn 1
  rw [show (P n).evaluation = v n by exact hP n]
  rw [dist_comm]
  exact (hdist n).trans
    ((one_div_le_one_div_of_le (by positivity) hden).trans_lt hN)

theorem xiWeilPolarization_separatedContinuedSource_reconstruction
    (F : ℂ → ℂ) (hF : XiWeilSquareSummable F) :
    ∃ P : ℕ → XiSeparatedContinuedCauchyPacket,
      Tendsto (fun n => (P n).evaluation) atTop
        (nhds (xiWeilEvaluationLp F hF)) ∧
      Tendsto (fun n => (P n).sourceEnergy) atTop
        (nhds (xiWeilPolarization F F).re) := by
  obtain ⟨P, hP⟩ := exists_separatedContinuedCauchyPackets_tendsto_evaluation F hF
  refine ⟨P, hP, ?_⟩
  have hQ := continuous_xiWeilHilbertQuadratic.continuousAt.tendsto.comp hP
  rw [xiWeilHilbertQuadratic_evaluation_eq_polarization_re] at hQ
  apply hQ.congr'
  exact Eventually.of_forall fun n =>
    (P n).sourceEnergy_eq_hilbertQuadratic.symm

theorem xiRectangularWeil_separatedContinuedSource_reconstruction
    (L a : ℝ) :
    ∃ P : ℕ → XiSeparatedContinuedCauchyPacket,
      Tendsto (fun n => (P n).evaluation) atTop
        (nhds (xiWeilEvaluationLp (xiRectangularTwoEdgeTransform L a)
          (xiRectangularTwoEdgeTransform_squareSummable L a))) ∧
      Tendsto (fun n => (P n).sourceEnergy) atTop
        (nhds (xiWeilPolarization (xiRectangularTwoEdgeTransform L a)
          (xiRectangularTwoEdgeTransform L a)).re) := by
  exact xiWeilPolarization_separatedContinuedSource_reconstruction
    (xiRectangularTwoEdgeTransform L a)
    (xiRectangularTwoEdgeTransform_squareSummable L a)

def xiRectangularLogSampleValue (L : ℝ) (n : ℕ) : ℝ :=
  (xiWeilPolarization
    (xiRectangularTwoEdgeTransform L (Real.log n / 2))
    (xiRectangularTwoEdgeTransform L (Real.log n / 2))).re

def IsRectangularSeparatedSourceSection
    (L : ℝ) (P : ℕ → XiSeparatedContinuedCauchyPacket) : Prop :=
  ∀ n : ℕ,
    |(P n).sourceEnergy - xiRectangularLogSampleValue L n| <
      1 / ((n : ℝ) + 1)

theorem exists_rectangularSeparatedSourceSection (L : ℝ) :
    ∃ P : ℕ → XiSeparatedContinuedCauchyPacket,
      IsRectangularSeparatedSourceSection L P := by
  have happ : ∀ n : ℕ, ∃ P : XiSeparatedContinuedCauchyPacket,
      |P.sourceEnergy - xiRectangularLogSampleValue L n| <
        1 / ((n : ℝ) + 1) := by
    intro n
    obtain ⟨P, _hP, hE⟩ :=
      xiRectangularWeil_separatedContinuedSource_reconstruction
        L (Real.log n / 2)
    have heps : 0 < 1 / ((n : ℝ) + 1) := by positivity
    obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp hE _ heps
    refine ⟨P N, ?_⟩
    have hdist := hN N le_rfl
    simpa only [Real.dist_eq, xiRectangularLogSampleValue] using hdist
  choose P hP using happ
  exact ⟨P, hP⟩

theorem riemannHypothesis_iff_rectangularSeparatedSourceSection_eventually_bddBelow
    {L : ℝ} (hL : 0 < L)
    (P : ℕ → XiSeparatedContinuedCauchyPacket)
    (hP : IsRectangularSeparatedSourceSection L P) :
    RiemannHypothesis ↔
      ∃ B : ℝ, ∃ N0 : ℕ, ∀ n : ℕ, N0 ≤ n → B ≤ (P n).sourceEnergy := by
  constructor
  · intro hRH
    refine ⟨-1, 0, ?_⟩
    intro n _hn
    have hq : 0 ≤ xiRectangularLogSampleValue L n := by
      exact (riemannHypothesis_iff_rectangular_logSample_weil_nonneg hL).mp hRH n
    have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    have hden : (1 : ℝ) ≤ (n : ℝ) + 1 := by linarith
    have heps : 1 / ((n : ℝ) + 1) ≤ 1 :=
      (div_le_one (by positivity : (0 : ℝ) < (n : ℝ) + 1)).2 hden
    have hlo := (abs_lt.mp (hP n)).1
    linarith
  · rintro ⟨B, N0, hlower⟩
    apply (riemannHypothesis_iff_rectangular_logSample_weil_eventually_bddBelow hL).mpr
    refine ⟨B - 1, N0, ?_⟩
    intro n hn _hLn
    have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    have hden : (1 : ℝ) ≤ (n : ℝ) + 1 := by linarith
    have heps : 1 / ((n : ℝ) + 1) ≤ 1 :=
      (div_le_one (by positivity : (0 : ℝ) < (n : ℝ) + 1)).2 hden
    have hhi := (abs_lt.mp (hP n)).2
    have hsrc := hlower n hn
    dsimp only [xiRectangularLogSampleValue] at hhi ⊢
    linarith

theorem exists_rectangularSeparatedSourceSection_rh_criterion
    {L : ℝ} (hL : 0 < L) :
    ∃ P : ℕ → XiSeparatedContinuedCauchyPacket,
      IsRectangularSeparatedSourceSection L P ∧
      (RiemannHypothesis ↔
        ∃ B : ℝ, ∃ N0 : ℕ, ∀ n : ℕ, N0 ≤ n → B ≤ (P n).sourceEnergy) := by
  obtain ⟨P, hP⟩ := exists_rectangularSeparatedSourceSection L
  exact ⟨P, hP,
    riemannHypothesis_iff_rectangularSeparatedSourceSection_eventually_bddBelow
      hL P hP⟩

end

end RHTower
