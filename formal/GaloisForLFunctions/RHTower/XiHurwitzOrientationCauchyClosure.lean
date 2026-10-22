import GaloisForLFunctions.RHTower.XiHurwitzOrientationWeilSector
import GaloisForLFunctions.RHTower.XiHurwitzOrientationEnergyConsumers
import GaloisForLFunctions.RHTower.XiWeilCauchyPoleExhaustion
import GaloisForLFunctions.RHTower.CCM.CCMTwoPoleSourceCriterion

/-!
# Cauchy-source closure of the Xi--Hurwitz orientation vector

Every multiplicity-fiber indicator is a norm limit of normalized regular Cauchy vectors.  The
canonical `ell^(2 : ℕ)` coordinate expansion of the Xi--Hurwitz orientation vector can be regrouped over
these finite multiplicity fibers.  Closedness then puts the complete orientation vector in the
regular-Cauchy Hilbert core without an RH assumption.
-/

open Complex Filter Topology

namespace RHTower

noncomputable section

/-- A regular Cauchy point on which both reflected evaluations of the analytically continued
prime--archimedean source are valid. -/
abbrev XiContinuedCauchyPoint :=
  {z : XiCRegularPoint // CCMContinuedCauchyDomain (z : ℂ)}

/-- Cauchy evaluation restricted to the genuine analytically continued prime--Gamma source
domain. -/
def xiWeilContinuedCauchyLp (z : XiContinuedCauchyPoint) :
    lp (fun _ : XiZeroCopy => ℂ) 2 :=
  xiWeilCauchyLp z.1

/-- Algebraic span of the regular Cauchy vectors whose poles lie in the continued prime--Gamma
source domain. -/
def xiWeilContinuedCauchyAlgebraicSubspace :
    Submodule ℂ (lp (fun _ : XiZeroCopy => ℂ) 2) :=
  Submodule.span ℂ (Set.range xiWeilContinuedCauchyLp)

/-- Hilbert closure of the analytically continued prime--Gamma Cauchy source core. -/
def xiWeilContinuedCauchyHilbertSubspace :
    Submodule ℂ (lp (fun _ : XiZeroCopy => ℂ) 2) :=
  xiWeilContinuedCauchyAlgebraicSubspace.topologicalClosure

theorem xiWeilContinuedCauchyAlgebraicSubspace_le_cauchyAlgebraicSubspace :
    xiWeilContinuedCauchyAlgebraicSubspace ≤ xiWeilCauchyAlgebraicSubspace := by
  apply Submodule.span_le.mpr
  rintro _ ⟨z, rfl⟩
  exact Submodule.subset_span ⟨z.1, rfl⟩

theorem xiWeilContinuedCauchyHilbertSubspace_le_cauchyHilbertSubspace :
    xiWeilContinuedCauchyHilbertSubspace ≤ xiWeilCauchyHilbertSubspace :=
  Submodule.topologicalClosure_mono
    xiWeilContinuedCauchyAlgebraicSubspace_le_cauchyAlgebraicSubspace

/-- Every actual Xi spectral fiber is a norm limit of Cauchy vectors that stay inside the
analytically continued prime--Gamma source domain. -/
theorem xiWeilFiberIndicatorLp_mem_continuedCauchyHilbertSubspace (q : XiZeroCopy) :
    xiWeilFiberIndicatorLp (xiSpectralPoint q) ∈
      xiWeilContinuedCauchyHilbertSubspace := by
  obtain ⟨c, _hc, _hcap, z, hzform, hzlim⟩ :=
    exists_normalizedCauchyLp_tendsto_fiberIndicator_with_cap
      (xiSpectralPoint q) zero_lt_one
  apply (Submodule.isClosed_topologicalClosure
    xiWeilContinuedCauchyAlgebraicSubspace).mem_of_tendsto hzlim
  exact Filter.Eventually.of_forall fun n =>
    xiWeilContinuedCauchyHilbertSubspace.smul_mem
      (xiSpectralPoint q - (z n : ℂ))
      (xiWeilContinuedCauchyAlgebraicSubspace.le_topologicalClosure
        (Submodule.subset_span ⟨
          (⟨z n, ccmContinuedCauchyDomain_of_regular_same_spectral_im q
            (z n).property (by rw [hzform n]; simp [Complex.div_im])⟩ :
              XiContinuedCauchyPoint),
          rfl⟩))

/-- Every spectral-fiber indicator belongs to the closed regular-Cauchy Hilbert core. -/
theorem xiWeilFiberIndicatorLp_mem_cauchyHilbertSubspace (alpha : ℂ) :
    xiWeilFiberIndicatorLp alpha ∈ xiWeilCauchyHilbertSubspace := by
  obtain ⟨z, hz⟩ := exists_normalizedCauchyLp_tendsto_fiberIndicator alpha
  apply (Submodule.isClosed_topologicalClosure
    xiWeilCauchyAlgebraicSubspace).mem_of_tendsto hz
  exact Filter.Eventually.of_forall fun n =>
    xiWeilCauchyHilbertSubspace.smul_mem
      (alpha - (z n : ℂ)) (xiWeilCauchyLp_mem_hilbertSubspace (z n))

/-- The common signed orientation coefficient on one analytic-multiplicity fiber. -/
def xiHurwitzOrientationFiberCoefficient (ρ : XiDivisorSupport) : ℂ :=
  xiHurwitzOrientationCoordinate (xiFirstZeroCopy ρ)

/-- One complete multiplicity fiber of the Xi--Hurwitz orientation vector. -/
def xiHurwitzOrientationFiberVector (ρ : XiDivisorSupport) :
    lp (fun _ : XiZeroCopy => ℂ) 2 :=
  xiHurwitzOrientationFiberCoefficient ρ •
    xiWeilFiberIndicatorLp (xiSpectralPointSupport ρ)

theorem xiHurwitzOrientationFiberVector_mem_cauchyHilbertSubspace
    (ρ : XiDivisorSupport) :
    xiHurwitzOrientationFiberVector ρ ∈ xiWeilCauchyHilbertSubspace := by
  exact xiWeilCauchyHilbertSubspace.smul_mem _
    (xiWeilFiberIndicatorLp_mem_cauchyHilbertSubspace _)

theorem xiHurwitzOrientationFiberVector_mem_continuedCauchyHilbertSubspace
    (ρ : XiDivisorSupport) :
    xiHurwitzOrientationFiberVector ρ ∈
      xiWeilContinuedCauchyHilbertSubspace := by
  exact xiWeilContinuedCauchyHilbertSubspace.smul_mem _
    (xiWeilFiberIndicatorLp_mem_continuedCauchyHilbertSubspace
      (xiFirstZeroCopy ρ))

theorem xiHurwitzOrientationCoordinate_eq_fiberCoefficient (q : XiZeroCopy) :
    xiHurwitzOrientationCoordinate q =
      xiHurwitzOrientationFiberCoefficient q.1 := by
  rfl

/-- The finite sum of single-copy coordinates over one multiplicity fiber is exactly its scalar
fiber-indicator vector. -/
theorem sum_xiHurwitzOrientationCoordinate_single_fiber (ρ : XiDivisorSupport) :
    (∑ j : Fin (Int.toNat ((MeromorphicOn.divisor xi Set.univ) (ρ : ℂ))),
      lp.single 2 (⟨ρ, j⟩ : XiZeroCopy)
        (xiHurwitzOrientationCoordinate (⟨ρ, j⟩ : XiZeroCopy))) =
      xiHurwitzOrientationFiberVector ρ := by
  apply Subtype.ext
  funext q
  rcases q with ⟨τ, k⟩
  simp only [lp.coeFn_sum, Finset.sum_apply]
  change
    (∑ j : Fin (Int.toNat ((MeromorphicOn.divisor xi Set.univ) (ρ : ℂ))),
      (lp.single (E := fun _ : XiZeroCopy => ℂ) 2 (⟨ρ, j⟩ : XiZeroCopy)
        (xiHurwitzOrientationCoordinate (⟨ρ, j⟩ : XiZeroCopy)))
          (⟨τ, k⟩ : XiZeroCopy)) =
      xiHurwitzOrientationFiberVector ρ (⟨τ, k⟩ : XiZeroCopy)
  by_cases hτρ : τ = ρ
  · subst τ
    have hleft :
        (∑ j : Fin (Int.toNat ((MeromorphicOn.divisor xi Set.univ) (ρ : ℂ))),
          (lp.single (E := fun _ : XiZeroCopy => ℂ) 2 (⟨ρ, j⟩ : XiZeroCopy)
            (xiHurwitzOrientationCoordinate (⟨ρ, j⟩ : XiZeroCopy)))
              (⟨ρ, k⟩ : XiZeroCopy)) =
          xiHurwitzOrientationCoordinate (⟨ρ, k⟩ : XiZeroCopy) := by
      rw [Fintype.sum_eq_single k]
      · rw [lp.single_apply_self]
      · intro j hj
        rw [lp.single_apply_ne]
        intro heq
        apply hj
        cases heq
        rfl
    rw [hleft]
    simp [xiHurwitzOrientationFiberVector, xiHurwitzOrientationFiberCoefficient,
      xiWeilFiberIndicatorLp_apply, xiSpectralPoint_eq_support,
      xiHurwitzOrientationCoordinate]
  · have hspec : xiSpectralPointSupport τ ≠ xiSpectralPointSupport ρ := by
      intro heq
      exact hτρ (xiSpectralPointSupport_injective heq)
    have hleft :
        (∑ j : Fin (Int.toNat ((MeromorphicOn.divisor xi Set.univ) (ρ : ℂ))),
          (lp.single (E := fun _ : XiZeroCopy => ℂ) 2 (⟨ρ, j⟩ : XiZeroCopy)
            (xiHurwitzOrientationCoordinate (⟨ρ, j⟩ : XiZeroCopy)))
              (⟨τ, k⟩ : XiZeroCopy)) = 0 := by
      apply Finset.sum_eq_zero
      intro j _hj
      rw [lp.single_apply_ne]
      intro heq
      have hfst := congrArg Sigma.fst heq
      exact hτρ hfst
    rw [hleft]
    simp [xiHurwitzOrientationFiberVector, xiHurwitzOrientationFiberCoefficient,
      xiWeilFiberIndicatorLp_apply, xiSpectralPoint_eq_support, hspec]

/-- The fiber vectors sum to the complete canonical orientation vector. -/
theorem hasSum_xiHurwitzOrientationFiberVector :
    HasSum xiHurwitzOrientationFiberVector xiHurwitzOrientationVector := by
  let f : XiZeroCopy → lp (fun _ : XiZeroCopy => ℂ) 2 := fun q =>
    lp.single 2 q (xiHurwitzOrientationVector q)
  have hall : HasSum f xiHurwitzOrientationVector :=
    lp.hasSum_single (by norm_num : (2 : ENNReal) ≠ ⊤) xiHurwitzOrientationVector
  apply hall.sigma
  intro ρ
  rw [← sum_xiHurwitzOrientationCoordinate_single_fiber ρ]
  simpa only [f, xiHurwitzOrientationVector_apply] using
    (hasSum_fintype (fun j : Fin (Int.toNat
      ((MeromorphicOn.divisor xi Set.univ) (ρ : ℂ))) =>
        lp.single (E := fun _ : XiZeroCopy => ℂ) 2 (⟨ρ, j⟩ : XiZeroCopy)
          (xiHurwitzOrientationCoordinate (⟨ρ, j⟩ : XiZeroCopy))))

/-- **Unconditional source-closure law.**  The canonical Xi--Hurwitz orientation vector belongs to
the Hilbert closure of the regular Cauchy/relative-resolvent source core. -/
theorem xiHurwitzOrientationVector_mem_cauchyHilbertSubspace :
    xiHurwitzOrientationVector ∈ xiWeilCauchyHilbertSubspace := by
  have hmem : (∑' ρ : XiDivisorSupport, xiHurwitzOrientationFiberVector ρ) ∈
      xiWeilCauchyHilbertSubspace :=
    tsum_mem (Submodule.isClosed_topologicalClosure xiWeilCauchyAlgebraicSubspace)
      xiHurwitzOrientationFiberVector_mem_cauchyHilbertSubspace
  rw [hasSum_xiHurwitzOrientationFiberVector.tsum_eq] at hmem
  exact hmem

/-- **Analytically continued source-closure law.**  The complete canonical Xi--Hurwitz
orientation vector belongs to the Hilbert closure generated only by regular Cauchy points on which
the reflected prime--Gamma source values are analytically valid. -/
theorem xiHurwitzOrientationVector_mem_continuedCauchyHilbertSubspace :
    xiHurwitzOrientationVector ∈ xiWeilContinuedCauchyHilbertSubspace := by
  have hmem : (∑' ρ : XiDivisorSupport, xiHurwitzOrientationFiberVector ρ) ∈
      xiWeilContinuedCauchyHilbertSubspace :=
    tsum_mem
      (Submodule.isClosed_topologicalClosure
        xiWeilContinuedCauchyAlgebraicSubspace)
      xiHurwitzOrientationFiberVector_mem_continuedCauchyHilbertSubspace
  rw [hasSum_xiHurwitzOrientationFiberVector.tsum_eq] at hmem
  exact hmem

/-- The analytically continued source-closure law strictly discharges the earlier unrestricted
Cauchy-closure membership. -/
theorem xiHurwitzOrientationVector_mem_cauchyHilbertSubspace_of_continued :
    xiHurwitzOrientationVector ∈ xiWeilCauchyHilbertSubspace :=
  xiWeilContinuedCauchyHilbertSubspace_le_cauchyHilbertSubspace
    xiHurwitzOrientationVector_mem_continuedCauchyHilbertSubspace

/-- The canonical orientation vector is the norm limit of an actual sequence of finite algebraic
Cauchy-source vectors, all taken inside the analytically continued prime--Gamma domain. -/
theorem exists_continuedCauchyCore_tendsto_xiHurwitzOrientationVector :
    ∃ V : ℕ → lp (fun _ : XiZeroCopy => ℂ) 2,
      (∀ n, V n ∈ xiWeilContinuedCauchyAlgebraicSubspace) ∧
      Tendsto V atTop (𝓝 xiHurwitzOrientationVector) := by
  have hclosure : xiHurwitzOrientationVector ∈
      closure (↑xiWeilContinuedCauchyAlgebraicSubspace :
        Set (lp (fun _ : XiZeroCopy => ℂ) 2)) := by
    exact xiHurwitzOrientationVector_mem_continuedCauchyHilbertSubspace
  have happ : ∀ n : ℕ, ∃ v,
      v ∈ xiWeilContinuedCauchyAlgebraicSubspace ∧
      dist xiHurwitzOrientationVector v < 1 / ((n : ℝ) + 1) := by
    intro n
    exact Metric.mem_closure_iff.mp hclosure _ (by positivity)
  choose V hVmem hVdist using happ
  refine ⟨V, hVmem, Metric.tendsto_atTop.mpr ?_⟩
  intro ε hε
  obtain ⟨N, hN⟩ := exists_nat_one_div_lt hε
  refine ⟨N, fun n hn => ?_⟩
  rw [dist_comm]
  have hden : (N : ℝ) + 1 ≤ (n : ℝ) + 1 := by
    exact_mod_cast Nat.add_le_add_right hn 1
  exact (hVdist n).trans
    ((one_div_le_one_div_of_le (by positivity) hden).trans_lt hN)

/-- **Continued Cauchy-source reconstruction law.**  There is an unconditional sequence of finite
Cauchy vectors whose poles lie in the analytically continued prime--Gamma domain, converging to
the canonical Xi--Hurwitz orientation vector; their Hilbert Weil values converge exactly to minus
the global orientation energy. -/
theorem xiHurwitzOrientationEnergy_continuedCauchy_reconstruction :
    ∃ V : ℕ → lp (fun _ : XiZeroCopy => ℂ) 2,
      (∀ n, V n ∈ xiWeilContinuedCauchyAlgebraicSubspace) ∧
      Tendsto V atTop (𝓝 xiHurwitzOrientationVector) ∧
      Tendsto (fun n => xiWeilHilbertQuadratic (V n)) atTop
        (𝓝 (-xiHurwitzOrientationEnergy)) := by
  obtain ⟨V, hVmem, hV⟩ :=
    exists_continuedCauchyCore_tendsto_xiHurwitzOrientationVector
  refine ⟨V, hVmem, hV, ?_⟩
  have hQ := continuous_xiWeilHilbertQuadratic.continuousAt.tendsto.comp hV
  rw [xiWeilHilbertQuadratic_xiHurwitzOrientationVector] at hQ
  exact hQ

/-- Positive global orientation energy produces a negative finite source-core vector directly,
without first passing through a proof of `¬ RH`. -/
theorem exists_continuedCauchyCore_weil_negative_of_orientationEnergy_pos
    (hE : 0 < xiHurwitzOrientationEnergy) :
    ∃ v ∈ xiWeilContinuedCauchyAlgebraicSubspace,
      xiWeilHilbertQuadratic v < 0 := by
  obtain ⟨V, hVmem, _hV, hQ⟩ :=
    xiHurwitzOrientationEnergy_continuedCauchy_reconstruction
  obtain ⟨n, hn⟩ :=
    (hQ.eventually_lt_const (neg_lt_zero.mpr hE)).exists
  exact ⟨V n, hVmem n, hn⟩

/-- The finite continued-source witnesses are robust: for every requested norm accuracy, positive
orientation energy yields an approximant within that accuracy whose negative Weil value retains
at least half of the global defect. -/
theorem exists_continuedCauchyCore_close_weil_lt_neg_half_energy
    (hE : 0 < xiHurwitzOrientationEnergy) {ε : ℝ} (hε : 0 < ε) :
    ∃ v ∈ xiWeilContinuedCauchyAlgebraicSubspace,
      dist v xiHurwitzOrientationVector < ε ∧
      xiWeilHilbertQuadratic v < -xiHurwitzOrientationEnergy / 2 := by
  obtain ⟨V, hVmem, hV, hQ⟩ :=
    xiHurwitzOrientationEnergy_continuedCauchy_reconstruction
  have hclose : ∀ᶠ n in atTop,
      dist (V n) xiHurwitzOrientationVector < ε := by
    obtain ⟨N, hN⟩ := (Metric.tendsto_atTop.mp hV) ε hε
    exact Filter.eventually_atTop.2 ⟨N, hN⟩
  have hhalf : -xiHurwitzOrientationEnergy <
      -xiHurwitzOrientationEnergy / 2 := by linarith
  have hnegative : ∀ᶠ n in atTop,
      xiWeilHilbertQuadratic (V n) < -xiHurwitzOrientationEnergy / 2 :=
    hQ.eventually_lt_const hhalf
  obtain ⟨n, hnclose, hnnegative⟩ := (hclose.and hnegative).exists
  exact ⟨V n, hVmem n, hnclose, hnnegative⟩

/-- **Source-core RH discharge.**  Nonnegativity of the unconditional Weil Hilbert form on the
algebraic regular-Cauchy source core alone implies RH; no separate closure or density hypothesis
remains. -/
theorem riemannHypothesis_of_cauchyCore_nonnegative
    (hpos : ∀ v ∈ xiWeilCauchyAlgebraicSubspace,
      0 ≤ xiWeilHilbertQuadratic v) :
    RiemannHypothesis :=
  riemannHypothesis_of_cauchyCore_nonneg_of_orientationVector_mem hpos
    xiHurwitzOrientationVector_mem_cauchyHilbertSubspace

end

end RHTower
