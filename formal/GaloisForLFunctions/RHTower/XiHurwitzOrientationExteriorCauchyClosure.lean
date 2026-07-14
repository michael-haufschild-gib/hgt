import GaloisForLFunctions.RHTower.XiHurwitzOrientationCauchyClosure
import GaloisForLFunctions.RHTower.PrimeArchExactOffLineQuartetAccretivity
import GaloisForLFunctions.RHTower.XiContinuedCauchyPacketDensity
import GaloisForLFunctions.RHTower.XiHurwitzOrientationSourceSequenceGate

/-!
# Exterior continued-Cauchy closure of Hurwitz orientation

The exact off-line-quartet budget does more than prove a central zero-free band.  It removes the
whole central continued-Cauchy source family from the remaining orientation problem.

For every exact quartet-admissible radius `R`, an off-critical Xi divisor point has ordinate
strictly larger than `R + 1 / 2` in absolute value.  The normalized horizontal Cauchy poles used
to isolate its multiplicity fiber can therefore be chosen with displacement at most `1 / 4`, so
that every approximating pole still satisfies `R < |re z|`.  A critical-line fiber has zero
Hurwitz orientation coefficient and needs no approximation.  Regrouping the canonical `ell^2`
expansion over multiplicity fibers consequently places the complete orientation vector in the
Hilbert closure generated only by exterior continued-source Cauchy vectors.

Thus source-core positivity need only be proved on the high-ordinate exterior span.  This is an
unconditional support reduction, not a zero-location or RH assumption.
-/

open Complex Filter Topology

namespace RHTower

noncomputable section

/-- A continued prime--Gamma Cauchy pole lying outside the central frequency band. -/
abbrev XiExteriorContinuedCauchyPoint (R : ℝ) :=
  {z : XiContinuedCauchyPoint // R < |(z : ℂ).re|}

/-- The Xi-divisor Cauchy evaluation vector at an exterior continued-source pole. -/
def xiWeilExteriorContinuedCauchyLp (R : ℝ)
    (z : XiExteriorContinuedCauchyPoint R) :
    lp (fun _ : XiZeroCopy => ℂ) 2 :=
  xiWeilContinuedCauchyLp z.1

/-- Algebraic source span generated only by continued Cauchy poles outside `[-R,R]`. -/
def xiWeilExteriorContinuedCauchyAlgebraicSubspace (R : ℝ) :
    Submodule ℂ (lp (fun _ : XiZeroCopy => ℂ) 2) :=
  Submodule.span ℂ (Set.range (xiWeilExteriorContinuedCauchyLp R))

/-- Hilbert closure of the exterior continued-Cauchy source core. -/
def xiWeilExteriorContinuedCauchyHilbertSubspace (R : ℝ) :
    Submodule ℂ (lp (fun _ : XiZeroCopy => ℂ) 2) :=
  (xiWeilExteriorContinuedCauchyAlgebraicSubspace R).topologicalClosure

/-- The exterior algebraic core is contained in the full continued-source core. -/
theorem xiWeilExteriorContinuedCauchyAlgebraicSubspace_le (R : ℝ) :
    xiWeilExteriorContinuedCauchyAlgebraicSubspace R ≤
      xiWeilContinuedCauchyAlgebraicSubspace := by
  apply Submodule.span_le.mpr
  rintro _ ⟨z, rfl⟩
  exact Submodule.subset_span ⟨z.1, rfl⟩

/-- The exterior Hilbert core is contained in the full continued-source Hilbert core. -/
theorem xiWeilExteriorContinuedCauchyHilbertSubspace_le (R : ℝ) :
    xiWeilExteriorContinuedCauchyHilbertSubspace R ≤
      xiWeilContinuedCauchyHilbertSubspace :=
  Submodule.topologicalClosure_mono
    (xiWeilExteriorContinuedCauchyAlgebraicSubspace_le R)

/-- An off-critical multiplicity fiber is isolated by continued-source Cauchy poles which all
remain outside any exact quartet-admissible central band. -/
theorem xiWeilFiberIndicatorLp_mem_exteriorContinuedCauchyHilbertSubspace
    (R : ℝ) (hband : XiOffLineQuartetAccretiveBand R)
    (q : XiZeroCopy) (hoff : (q.1 : ℂ).re ≠ 1 / 2) :
    xiWeilFiberIndicatorLp (xiSpectralPoint q) ∈
      xiWeilExteriorContinuedCauchyHilbertSubspace R := by
  let alpha : ℂ := xiSpectralPoint q
  obtain ⟨c, hc, hcap, z, hzform, hzlim⟩ :=
    exists_normalizedCauchyLp_tendsto_fiberIndicator_with_cap
      alpha (by norm_num : (0 : ℝ) < 1 / 4)
  have halphaRe : alpha.re = (q.1 : ℂ).im := by
    simp [alpha, xiSpectralPoint, mul_re]
  have hheight : R + 1 / 2 < |alpha.re| := by
    rw [halphaRe]
    exact
      xiOffLineQuartetAccretiveBand_add_half_lt_abs_im_of_offLine
        R hband q hoff
  have hzExterior : ∀ n, R < |(z n : ℂ).re| := by
    intro n
    have hrpos : 0 < c / (n + 1 : ℕ) := div_pos hc (by positivity)
    have hrle : c / (n + 1 : ℕ) ≤ c := by
      have hden : (1 : ℝ) ≤ (n + 1 : ℕ) := by
        exact_mod_cast Nat.succ_pos n
      exact div_le_self hc.le hden
    have hrquarter : c / (n + 1 : ℕ) ≤ 1 / 4 := hrle.trans hcap
    have hzre : (z n : ℂ).re = alpha.re + c / (n + 1 : ℕ) := by
      rw [hzform n]
      simp only [add_re, ofReal_re]
    by_cases halpha : 0 ≤ alpha.re
    · have habs : |alpha.re| = alpha.re := abs_of_nonneg halpha
      rw [habs] at hheight
      rw [hzre, abs_of_pos (by linarith)]
      linarith
    · have halphaneg : alpha.re < 0 := lt_of_not_ge halpha
      have habs : |alpha.re| = -alpha.re := abs_of_neg halphaneg
      rw [habs] at hheight
      have hzneg : alpha.re + c / (n + 1 : ℕ) < 0 := by
        linarith [hband.1]
      rw [hzre, abs_of_neg hzneg]
      linarith
  apply (Submodule.isClosed_topologicalClosure
    (xiWeilExteriorContinuedCauchyAlgebraicSubspace R)).mem_of_tendsto hzlim
  exact Eventually.of_forall fun n =>
    (xiWeilExteriorContinuedCauchyHilbertSubspace R).smul_mem
      (alpha - (z n : ℂ))
      ((xiWeilExteriorContinuedCauchyAlgebraicSubspace R).le_topologicalClosure
        (Submodule.subset_span ⟨
          (⟨⟨z n, ccmContinuedCauchyDomain_of_regular_same_spectral_im q
              (z n).property (by rw [hzform n]; simp [alpha, Complex.div_im])⟩,
            hzExterior n⟩ : XiExteriorContinuedCauchyPoint R),
          rfl⟩))

/-- A critical-line divisor fiber has zero signed Hurwitz orientation coefficient. -/
theorem xiHurwitzOrientationFiberCoefficient_eq_zero_of_re_eq_half
    (ρ : XiDivisorSupport) (hρ : (ρ : ℂ).re = 1 / 2) :
    xiHurwitzOrientationFiberCoefficient ρ = 0 := by
  have hdefect : xiHurwitzOrientationDefect ρ = 0 :=
    (xiHurwitzOrientationDefect_eq_zero_iff_re_eq_half ρ).mpr hρ
  have him : (xiHurwitzMonodromyCharacter ρ).im = 0 :=
    (xiHurwitzOrientationDefect_eq_zero_iff ρ).mp hdefect
  rw [xiHurwitzOrientationFiberCoefficient, xiHurwitzOrientationCoordinate]
  simp only [xiFirstZeroCopy_fst, him, zero_div, ofReal_zero]

/-- Every complete orientation multiplicity fiber belongs to the exterior source closure.  The
off-line case uses exterior pole exhaustion; the on-line case is the zero vector. -/
theorem xiHurwitzOrientationFiberVector_mem_exteriorContinuedCauchyHilbertSubspace
    (R : ℝ) (hband : XiOffLineQuartetAccretiveBand R)
    (ρ : XiDivisorSupport) :
    xiHurwitzOrientationFiberVector ρ ∈
      xiWeilExteriorContinuedCauchyHilbertSubspace R := by
  by_cases hoff : (ρ : ℂ).re ≠ 1 / 2
  · exact (xiWeilExteriorContinuedCauchyHilbertSubspace R).smul_mem _
      (by
        simpa only [xiSpectralPoint_eq_support] using
          xiWeilFiberIndicatorLp_mem_exteriorContinuedCauchyHilbertSubspace
            R hband (xiFirstZeroCopy ρ) (by simpa using hoff))
  · have hρ : (ρ : ℂ).re = 1 / 2 := not_ne_iff.mp hoff
    rw [xiHurwitzOrientationFiberVector,
      xiHurwitzOrientationFiberCoefficient_eq_zero_of_re_eq_half ρ hρ,
      zero_smul]
    exact (xiWeilExteriorContinuedCauchyHilbertSubspace R).zero_mem

/-- **Exterior source-closure law.**  For every exact quartet-admissible radius, the complete
canonical Xi--Hurwitz orientation vector belongs to the Hilbert closure generated only by
continued prime--Gamma Cauchy poles outside the central band. -/
theorem xiHurwitzOrientationVector_mem_exteriorContinuedCauchyHilbertSubspace
    (R : ℝ) (hband : XiOffLineQuartetAccretiveBand R) :
    xiHurwitzOrientationVector ∈
      xiWeilExteriorContinuedCauchyHilbertSubspace R := by
  have hmem :
      (∑' ρ : XiDivisorSupport, xiHurwitzOrientationFiberVector ρ) ∈
        xiWeilExteriorContinuedCauchyHilbertSubspace R :=
    tsum_mem
      (Submodule.isClosed_topologicalClosure
        (xiWeilExteriorContinuedCauchyAlgebraicSubspace R))
      (xiHurwitzOrientationFiberVector_mem_exteriorContinuedCauchyHilbertSubspace
        R hband)
  rw [hasSum_xiHurwitzOrientationFiberVector.tsum_eq] at hmem
  exact hmem

/-- Positivity on the exterior algebraic continued-source core extends to its Hilbert closure. -/
theorem xiWeilHilbertQuadratic_nonneg_on_exteriorContinuedCauchyHilbertSubspace
    (R : ℝ)
    (hpos : ∀ v ∈ xiWeilExteriorContinuedCauchyAlgebraicSubspace R,
      0 ≤ xiWeilHilbertQuadratic v) :
    ∀ v ∈ xiWeilExteriorContinuedCauchyHilbertSubspace R,
      0 ≤ xiWeilHilbertQuadratic v := by
  intro v hv
  have hclosed : IsClosed {w | 0 ≤ xiWeilHilbertQuadratic w} :=
    isClosed_Ici.preimage continuous_xiWeilHilbertQuadratic
  exact (closure_minimal hpos hclosed) hv

/-! ## Exact exterior prime--Gamma source surface -/

/-- Every exterior algebraic source vector has a finite packet representation whose poles are
still exterior. -/
theorem exists_finsupp_indexedExteriorCauchyPacket_eq_of_mem
    (R : ℝ) (v : lp (fun _ : XiZeroCopy => ℂ) 2)
    (hv : v ∈ xiWeilExteriorContinuedCauchyAlgebraicSubspace R) :
    ∃ c : XiExteriorContinuedCauchyPoint R →₀ ℂ,
      xiWeilContinuedCauchyPacketLp
        (fun i : {x // x ∈ c.support} ↦ c i.1)
        (fun i : {x // x ∈ c.support} ↦ i.1.1) = v := by
  rw [xiWeilExteriorContinuedCauchyAlgebraicSubspace] at hv
  obtain ⟨c, hc⟩ := Finsupp.mem_span_range_iff_exists_finsupp.mp hv
  refine ⟨c, ?_⟩
  rw [← hc]
  unfold xiWeilContinuedCauchyPacketLp
  rw [Finsupp.sum]
  exact (Finset.sum_subtype c.support (fun _ => Iff.rfl)
    (fun i => c i • xiWeilExteriorContinuedCauchyLp R i)).symm

/-- A finite exterior packet can be approximated by pairwise conjugate-separated packets which
remain exterior, and their exact continued prime--Gamma energies converge to the packet's Weil
Hilbert value. -/
theorem exists_pairwiseConjSeparatedExteriorContinuedSourceEnergy_tendsto
    (R : ℝ) {ι : Type*} [Fintype ι] (c : ι → ℂ)
    (z : ι → XiExteriorContinuedCauchyPoint R) :
    ∃ w : ℕ → ι → XiExteriorContinuedCauchyPoint R,
      (∀ n i j, (w n i : ℂ) ≠ (starRingEnd ℂ) (w n j : ℂ)) ∧
      Tendsto
        (fun n ↦ xiWeilContinuedCauchyPacketLp c (fun i ↦ (w n i).1))
        atTop
        (nhds (xiWeilContinuedCauchyPacketLp c (fun i ↦ (z i).1))) ∧
      Tendsto
        (fun n ↦ continuedCauchyPacketSourceEnergy c (fun i ↦ (w n i).1))
        atTop
        (nhds (xiWeilHilbertQuadratic
          (xiWeilContinuedCauchyPacketLp c (fun i ↦ (z i).1)))) := by
  obtain ⟨w0, hw0sep, hw0⟩ :=
    exists_pairwiseConjSeparatedContinuedCauchyPacket_tendsto
      (fun i ↦ (z i).1)
  have hopen : IsOpen {u : ℂ | R < |u.re|} :=
    isOpen_lt continuous_const (continuous_abs.comp Complex.continuous_re)
  have hw0Exterior : ∀ᶠ n in atTop, ∀ i, R < |(w0 n i : ℂ).re| := by
    rw [Filter.eventually_all]
    intro i
    exact (hw0 i).eventually (hopen.mem_nhds (z i).property)
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 hw0Exterior
  let w : ℕ → ι → XiExteriorContinuedCauchyPoint R := fun n i ↦
    ⟨w0 (n + N) i, hN (n + N) (Nat.le_add_left N n) i⟩
  have hwpoint : ∀ i,
      Tendsto (fun n ↦ (w n i : ℂ)) atTop (nhds (z i : ℂ)) := by
    intro i
    exact (hw0 i).comp (tendsto_add_atTop_nat N)
  have hwvec : Tendsto
      (fun n ↦ xiWeilContinuedCauchyPacketLp c (fun i ↦ (w n i).1))
      atTop
      (nhds (xiWeilContinuedCauchyPacketLp c (fun i ↦ (z i).1))) := by
    unfold xiWeilContinuedCauchyPacketLp
    apply tendsto_finsetSum
    intro i _hi
    exact (tendsto_xiWeilCauchyLp (hwpoint i)).const_smul (c i)
  have hwsep : ∀ n i j,
      (w n i : ℂ) ≠ (starRingEnd ℂ) (w n j : ℂ) := by
    intro n i j
    exact hw0sep (n + N) i j
  refine ⟨w, hwsep, hwvec, ?_⟩
  have hQ := continuous_xiWeilHilbertQuadratic.continuousAt.tendsto.comp hwvec
  apply hQ.congr'
  exact Eventually.of_forall fun n ↦ by
    simpa [continuedCauchyPacketSourceEnergy] using
      xiWeilHilbertQuadratic_indexedCauchyPacket_eq_continuedSource_re
        c (fun i ↦ (w n i).1) (hwsep n)

/-- Positivity of every exact finite prime--Gamma divided-difference energy whose poles lie
outside the central band. -/
def XiExteriorContinuedCauchySourcePassivity (R : ℝ) : Prop :=
  ∀ (ι : Type) [Fintype ι] (c : ι → ℂ)
    (z : ι → XiExteriorContinuedCauchyPoint R),
    (∀ i j, (z i : ℂ) ≠ (starRingEnd ℂ) (z j : ℂ)) →
      0 ≤ continuedCauchyPacketSourceEnergy c (fun i ↦ (z i).1)

/-- Exact exterior source passivity implies nonnegativity of the Weil Hilbert form on the whole
exterior algebraic Cauchy core, including packets with removable source collisions. -/
theorem exteriorContinuedCauchyCore_nonnegative_of_sourcePassivity
    (R : ℝ) (hsource : XiExteriorContinuedCauchySourcePassivity R) :
    ∀ v ∈ xiWeilExteriorContinuedCauchyAlgebraicSubspace R,
      0 ≤ xiWeilHilbertQuadratic v := by
  intro v hv
  obtain ⟨c, hc⟩ := exists_finsupp_indexedExteriorCauchyPacket_eq_of_mem R v hv
  let ι := {x // x ∈ c.support}
  let coeff : ι → ℂ := fun i ↦ c i.1
  let pole : ι → XiExteriorContinuedCauchyPoint R := fun i ↦ i.1
  obtain ⟨w, hwsep, _hwvec, hwenergy⟩ :=
    exists_pairwiseConjSeparatedExteriorContinuedSourceEnergy_tendsto
      R coeff pole
  have hnonneg : ∀ n,
      0 ≤ continuedCauchyPacketSourceEnergy coeff (fun i ↦ (w n i).1) := by
    intro n
    exact hsource ι coeff (w n) (hwsep n)
  have hlimit :
      0 ≤ xiWeilHilbertQuadratic
        (xiWeilContinuedCauchyPacketLp coeff (fun i ↦ (pole i).1)) :=
    ge_of_tendsto hwenergy (Eventually.of_forall hnonneg)
  rw [show xiWeilContinuedCauchyPacketLp coeff (fun i ↦ (pole i).1) = v by
    exact hc] at hlimit
  exact hlimit

/-- **Exterior source-core discharge.**  At any exact quartet-admissible radius, positivity of the
unconditional Weil form only on the high-ordinate continued-Cauchy algebraic span implies RH. -/
theorem riemannHypothesis_of_exteriorContinuedCauchyCore_nonnegative
    (R : ℝ) (hband : XiOffLineQuartetAccretiveBand R)
    (hpos : ∀ v ∈ xiWeilExteriorContinuedCauchyAlgebraicSubspace R,
      0 ≤ xiWeilHilbertQuadratic v) :
    RiemannHypothesis := by
  apply riemannHypothesis_iff_xiHurwitzOrientationVector_weil_nonneg.mpr
  exact xiWeilHilbertQuadratic_nonneg_on_exteriorContinuedCauchyHilbertSubspace
    R hpos xiHurwitzOrientationVector
      (xiHurwitzOrientationVector_mem_exteriorContinuedCauchyHilbertSubspace R hband)

/-- **Prime--Gamma exterior value criterion.**  At an exact quartet-admissible radius, positivity
of the explicit finite divided-difference source energies only for exterior poles implies RH. -/
theorem riemannHypothesis_of_exteriorContinuedCauchySourcePassivity
    (R : ℝ) (hband : XiOffLineQuartetAccretiveBand R)
    (hsource : XiExteriorContinuedCauchySourcePassivity R) :
    RiemannHypothesis :=
  riemannHypothesis_of_exteriorContinuedCauchyCore_nonnegative R hband
    (exteriorContinuedCauchyCore_nonnegative_of_sourcePassivity R hsource)

/-- RH supplies exterior source passivity at every radius. -/
theorem exteriorContinuedCauchySourcePassivity_of_riemannHypothesis
    (R : ℝ) (hRH : RiemannHypothesis) :
    XiExteriorContinuedCauchySourcePassivity R := by
  intro ι _inst c z hsep
  have hnonneg := xiWeilHilbertQuadratic_nonneg_of_riemannHypothesis hRH
    (xiWeilContinuedCauchyPacketLp c (fun i ↦ (z i).1))
  simpa only [continuedCauchyPacketSourceEnergy,
    xiWeilHilbertQuadratic_indexedCauchyPacket_eq_continuedSource_re
      c (fun i ↦ (z i).1) hsep] using hnonneg

/-- Exact source-value criterion on every quartet-admissible exterior domain. -/
theorem exteriorContinuedCauchySourcePassivity_iff_riemannHypothesis
    (R : ℝ) (hband : XiOffLineQuartetAccretiveBand R) :
    XiExteriorContinuedCauchySourcePassivity R ↔ RiemannHypothesis :=
  ⟨riemannHypothesis_of_exteriorContinuedCauchySourcePassivity R hband,
    exteriorContinuedCauchySourcePassivity_of_riemannHypothesis R⟩

/-- Clean rational exterior source-core criterion: all central poles with
`|re z| ≤ 218 / 25` are unnecessary for the remaining source-positivity proof. -/
theorem riemannHypothesis_of_exteriorContinuedCauchyCore_nonnegative_twoHundredEighteen_twentyFifths
    (hpos : ∀ v ∈
        xiWeilExteriorContinuedCauchyAlgebraicSubspace (218 / 25),
      0 ≤ xiWeilHilbertQuadratic v) :
    RiemannHypothesis :=
  riemannHypothesis_of_exteriorContinuedCauchyCore_nonnegative
    (218 / 25) xiOffLineQuartetAccretiveBand_twoHundredEighteen_twentyFifths hpos

/-- Clean rational prime--Gamma source-value criterion outside `|re z| ≤ 218 / 25`. -/
theorem exteriorContinuedCauchySourcePassivity_twoHundredEighteen_twentyFifths_iff_rh :
    XiExteriorContinuedCauchySourcePassivity (218 / 25) ↔
      RiemannHypothesis :=
  exteriorContinuedCauchySourcePassivity_iff_riemannHypothesis
    (218 / 25) xiOffLineQuartetAccretiveBand_twoHundredEighteen_twentyFifths

end

end RHTower
