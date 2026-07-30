import GaloisForLFunctions.RHTower.XiContinuedCauchySeparatedDensity

/-!
# Pairwise-separated density of finite continued Cauchy packets

Every finite continued prime--Gamma Cauchy packet is an `ell²` limit of packets for which no pole
is the conjugate of any other pole.  A common vanishing perturbation in the direction `1 + I`
separates exact conjugate pairs by its imaginary component; distinct limiting pairs are eventually
separated by the Hausdorff property.  Regularity and the full continued source domain persist
locally.

Consequently every approximating packet can be evaluated by the existing exact finite
prime--Gamma divided-difference formula.  The theorem is analytic density only: it does not prove
the remaining source sign or select a packet sequence independently of Xi divisor data.
-/

open Complex Metric Function Filter
open scoped Topology BigOperators

namespace RHTower

noncomputable section

/-- The two-sided continued Cauchy domain persists along every sequence converging to one of its
regular points. -/
theorem eventually_ccmContinuedCauchyDomain_of_tendsto
    {w : ℕ → ℂ} {z : XiContinuedCauchyPoint}
    (hw : Tendsto w atTop (nhds (z : ℂ))) :
    ∀ᶠ n in atTop, CCMContinuedCauchyDomain (w n) := by
  have hzlo : -(1 / 2 : ℝ) < (z : ℂ).im := by
    have h := z.property.2.2.2.1
    simp [mul_re] at h
    linarith
  have hzhi : (z : ℂ).im < 1 / 2 := by
    have h := z.property.1
    simp [mul_re] at h
    linarith
  have hwim : Tendsto (fun n ↦ (w n).im) atTop (nhds (z : ℂ).im) :=
    Complex.continuous_im.continuousAt.tendsto.comp hw
  have hstrip : ∀ᶠ n in atTop,
      -(1 / 2 : ℝ) < (w n).im ∧ (w n).im < 1 / 2 :=
    hwim.eventually (Ioo_mem_nhds hzlo hzhi)
  have hXi : Tendsto (fun n ↦ XiC (w n)) atTop (nhds (XiC (z : ℂ))) :=
    (XiC_analytic (z : ℂ) (Set.mem_univ _)).continuousAt.tendsto.comp hw
  have hregular : ∀ᶠ n in atTop, XiC (w n) ≠ 0 :=
    hXi.eventually_ne z.1.property
  filter_upwards [hstrip, hregular] with n hn hne
  exact ccmContinuedCauchyDomain_of_regular_mem_centeredStrip hn.1 hn.2 hne

/-- Positive vanishing perturbation scale. -/
def continuedCauchyPacketEpsilon (n : ℕ) : ℝ :=
  1 / ((n + 1 : ℕ) : ℝ)

theorem continuedCauchyPacketEpsilon_pos (n : ℕ) :
    0 < continuedCauchyPacketEpsilon n := by
  unfold continuedCauchyPacketEpsilon
  positivity

theorem tendsto_continuedCauchyPacketEpsilon :
    Tendsto continuedCauchyPacketEpsilon atTop (nhds 0) := by
  change Tendsto (fun n : ℕ => 1 / ((n + 1 : ℕ) : ℝ)) atTop (nhds 0)
  simpa only [Function.comp_def, Nat.cast_add, Nat.cast_one] using!
    (tendsto_const_div_atTop_nhds_zero_nat (1 : ℝ)).comp (tendsto_add_atTop_nat 1)

/-- Move every pole by the same vanishing complex offset. -/
def continuedCauchyPacketPerturbation
    {ι : Type*} (z : ι → XiContinuedCauchyPoint) (n : ℕ) (i : ι) : ℂ :=
  (z i : ℂ) + (continuedCauchyPacketEpsilon n : ℂ) * (1 + I)

theorem tendsto_continuedCauchyPacketPerturbation
    {ι : Type*} (z : ι → XiContinuedCauchyPoint) (i : ι) :
    Tendsto (fun n ↦ continuedCauchyPacketPerturbation z n i)
      atTop (nhds (z i : ℂ)) := by
  simpa [continuedCauchyPacketPerturbation] using
    tendsto_const_nhds.add
      ((Complex.ofRealCLM.continuous.tendsto 0 |>.comp
        tendsto_continuedCauchyPacketEpsilon).mul tendsto_const_nhds)

/-- The common `1 + I` perturbation eventually removes every pairwise conjugate collision in a
finite packet. -/
theorem eventually_pairwise_conjSeparated_continuedCauchyPacketPerturbation
    {ι : Type*} [Fintype ι] (z : ι → XiContinuedCauchyPoint) :
    ∀ᶠ n in atTop, ∀ i j,
      continuedCauchyPacketPerturbation z n i ≠
        (starRingEnd ℂ) (continuedCauchyPacketPerturbation z n j) := by
  rw [Filter.eventually_all]
  intro i
  rw [Filter.eventually_all]
  intro j
  by_cases hij : (z i : ℂ) = (starRingEnd ℂ) (z j : ℂ)
  · exact Eventually.of_forall fun n hEq ↦ by
      have him := congrArg Complex.im hEq
      have heps := continuedCauchyPacketEpsilon_pos n
      simp [continuedCauchyPacketPerturbation, mul_im, hij] at him
      linarith
  · have hi := tendsto_continuedCauchyPacketPerturbation z i
    have hj : Tendsto
        (fun n ↦ (starRingEnd ℂ) (continuedCauchyPacketPerturbation z n j))
        atTop (nhds ((starRingEnd ℂ) (z j : ℂ))) :=
      Complex.continuous_conj.continuousAt.tendsto.comp
        (tendsto_continuedCauchyPacketPerturbation z j)
    have hsub := hi.sub hj
    have hne : (z i : ℂ) - (starRingEnd ℂ) (z j : ℂ) ≠ 0 :=
      sub_ne_zero.mpr hij
    exact (hsub.eventually_ne hne).mono fun n hn ↦ sub_ne_zero.mp hn

/-- Every finite continued-source pole packet is a coordinatewise limit of pairwise
conjugate-separated packets staying in the same source domain. -/
theorem exists_pairwiseConjSeparatedContinuedCauchyPacket_tendsto
    {ι : Type*} [Fintype ι] (z : ι → XiContinuedCauchyPoint) :
    ∃ w : ℕ → ι → XiContinuedCauchyPoint,
      (∀ n i j, (w n i : ℂ) ≠ (starRingEnd ℂ) (w n j : ℂ)) ∧
      (∀ i, Tendsto (fun n ↦ (w n i : ℂ)) atTop (nhds (z i : ℂ))) := by
  have hdom : ∀ᶠ n in atTop, ∀ i,
      CCMContinuedCauchyDomain (continuedCauchyPacketPerturbation z n i) := by
    rw [Filter.eventually_all]
    intro i
    exact eventually_ccmContinuedCauchyDomain_of_tendsto
      (tendsto_continuedCauchyPacketPerturbation z i)
  have hsep := eventually_pairwise_conjSeparated_continuedCauchyPacketPerturbation z
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 (hdom.and hsep)
  let wval : ℕ → ι → ℂ := fun n i ↦
    continuedCauchyPacketPerturbation z (n + N) i
  have hwdom : ∀ n i, CCMContinuedCauchyDomain (wval n i) := by
    intro n i
    exact (hN (n + N) (Nat.le_add_left N n)).1 i
  have hwregular : ∀ n i, XiC (wval n i) ≠ 0 := by
    intro n i
    exact XiC_ne_zero_of_continuedPrimeArch_domain
      (hwdom n i).1 (hwdom n i).2.1 (hwdom n i).2.2.1
  let w : ℕ → ι → XiContinuedCauchyPoint := fun n i ↦
    ⟨⟨wval n i, hwregular n i⟩, hwdom n i⟩
  refine ⟨w, ?_, ?_⟩
  · intro n i j
    exact (hN (n + N) (Nat.le_add_left N n)).2 i j
  · intro i
    have hshift : Tendsto (fun n : ℕ ↦ n + N) atTop atTop := tendsto_add_atTop_nat N
    exact (tendsto_continuedCauchyPacketPerturbation z i).comp hshift

/-- The `ell²` evaluation vector of a finite continued Cauchy packet. -/
def xiWeilContinuedCauchyPacketLp
    {ι : Type*} [Fintype ι] (c : ι → ℂ)
    (z : ι → XiContinuedCauchyPoint) :
    lp (fun _ : XiZeroCopy => ℂ) 2 :=
  ∑ i, c i • xiWeilContinuedCauchyLp (z i)

/-- Pairwise-separated packets are dense in every fixed finite continued Cauchy packet in the Xi
divisor `ell²` norm. -/
theorem exists_pairwiseConjSeparatedContinuedCauchyPacketLp_tendsto
    {ι : Type*} [Fintype ι] (c : ι → ℂ)
    (z : ι → XiContinuedCauchyPoint) :
    ∃ w : ℕ → ι → XiContinuedCauchyPoint,
      (∀ n i j, (w n i : ℂ) ≠ (starRingEnd ℂ) (w n j : ℂ)) ∧
      Tendsto (fun n ↦ xiWeilContinuedCauchyPacketLp c (w n)) atTop
        (nhds (xiWeilContinuedCauchyPacketLp c z)) := by
  obtain ⟨w, hwsep, hw⟩ :=
    exists_pairwiseConjSeparatedContinuedCauchyPacket_tendsto z
  refine ⟨w, hwsep, ?_⟩
  unfold xiWeilContinuedCauchyPacketLp
  apply tendsto_finset_sum
  intro i _hi
  exact (tendsto_xiWeilCauchyLp (hw i)).const_smul (c i)

/-- The test function represented by an indexed finite continued Cauchy packet. -/
def xiWeilIndexedCauchyPacket
    {ι : Type*} [Fintype ι] (c : ι → ℂ)
    (z : ι → XiContinuedCauchyPoint) (x : ℂ) : ℂ :=
  ∑ i, c i * xiWeilCauchyTest (z i : ℂ) x

theorem xiWeilIndexedCauchyPacket_squareSummable
    {ι : Type*} [Fintype ι] (c : ι → ℂ)
    (z : ι → XiContinuedCauchyPoint) :
    XiWeilSquareSummable (xiWeilIndexedCauchyPacket c z) := by
  have hs := HilbertSchmidt.summable_coe_sq
    (xiWeilContinuedCauchyPacketLp c z)
  unfold XiWeilSquareSummable
  apply hs.congr
  intro q
  congr 2
  rw [xiWeilIndexedCauchyPacket, xiWeilContinuedCauchyPacketLp,
    lp.coeFn_sum, Finset.sum_apply]
  apply Finset.sum_congr rfl
  intro i _hi
  rfl

theorem xiWeilEvaluationLp_indexedCauchyPacket
    {ι : Type*} [Fintype ι] (c : ι → ℂ)
    (z : ι → XiContinuedCauchyPoint) :
    xiWeilEvaluationLp (xiWeilIndexedCauchyPacket c z)
        (xiWeilIndexedCauchyPacket_squareSummable c z) =
      xiWeilContinuedCauchyPacketLp c z := by
  apply Subtype.ext
  funext q
  rw [xiWeilEvaluationLp_apply, xiWeilIndexedCauchyPacket,
    xiWeilContinuedCauchyPacketLp, lp.coeFn_sum, Finset.sum_apply]
  apply Finset.sum_congr rfl
  intro i _hi
  rfl

/-- Exact continued prime--Gamma divided-difference formula for an indexed finite packet with no
pairwise conjugate collisions. -/
theorem xiWeilPolarization_indexedCauchyPacket_eq_continuedSource
    {ι : Type*} [Fintype ι] (c : ι → ℂ)
    (z : ι → XiContinuedCauchyPoint)
    (hsep : ∀ i j, (z i : ℂ) ≠ (starRingEnd ℂ) (z j : ℂ)) :
    xiWeilPolarization (xiWeilIndexedCauchyPacket c z)
        (xiWeilIndexedCauchyPacket c z) =
      ∑ i, ∑ j, c i * (starRingEnd ℂ) (c j) *
        ccmContinuedCauchyKernel (z i : ℂ) (z j : ℂ) := by
  let term : ι → ι → XiZeroCopy → ℂ := fun i j q =>
    c i * (starRingEnd ℂ) (c j) *
      (xiWeilCauchyTest (z i : ℂ) (xiSpectralPoint q) *
        xiWeilSharp (xiWeilCauchyTest (z j : ℂ)) (xiSpectralPoint q))
  have hterm (i j : ι) : Summable (term i j) := by
    have hp := xiWeilPairSummable_cauchy
      (XiC_ne_zero_of_continuedPrimeArch_domain
        (z i).property.1 (z i).property.2.1 (z i).property.2.2.1)
      (XiC_ne_zero_of_continuedPrimeArch_domain
        (z j).property.2.2.2.1 (z j).property.2.2.2.2.1
          (z j).property.2.2.2.2.2)
      (hsep i j)
    exact (show Summable (fun q : XiZeroCopy =>
      xiWeilCauchyTest (z i : ℂ) (xiSpectralPoint q) *
        xiWeilSharp (xiWeilCauchyTest (z j : ℂ)) (xiSpectralPoint q)) from hp).mul_left _
  rw [xiWeilPolarization]
  calc
    (∑' q : XiZeroCopy,
        xiWeilIndexedCauchyPacket c z (xiSpectralPoint q) *
          xiWeilSharp (xiWeilIndexedCauchyPacket c z) (xiSpectralPoint q)) =
        ∑' q : XiZeroCopy, ∑ i, ∑ j, term i j q := by
      apply tsum_congr
      intro q
      rw [xiWeilIndexedCauchyPacket, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i _hi
      rw [xiWeilSharp, xiWeilIndexedCauchyPacket, map_sum,
        Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _hj
      simp only [term, map_mul]
      rw [show (starRingEnd ℂ)
          (xiWeilCauchyTest (z j : ℂ) ((starRingEnd ℂ) (xiSpectralPoint q))) =
          xiWeilSharp (xiWeilCauchyTest (z j : ℂ)) (xiSpectralPoint q) by rfl]
      ring
    _ = ∑ i, ∑ j, ∑' q : XiZeroCopy, term i j q := by
      rw [Summable.tsum_finsetSum (fun i _hi => summable_sum fun j _hj => hterm i j)]
      apply Finset.sum_congr rfl
      intro i _hi
      rw [Summable.tsum_finsetSum (fun j _hj => hterm i j)]
    _ = ∑ i, ∑ j, c i * (starRingEnd ℂ) (c j) *
          xiWeilPolarization (xiWeilCauchyTest (z i : ℂ))
            (xiWeilCauchyTest (z j : ℂ)) := by
      apply Finset.sum_congr rfl
      intro i _hi
      apply Finset.sum_congr rfl
      intro j _hj
      change (∑' q : XiZeroCopy,
        c i * (starRingEnd ℂ) (c j) *
          (xiWeilCauchyTest (z i : ℂ) (xiSpectralPoint q) *
            xiWeilSharp (xiWeilCauchyTest (z j : ℂ)) (xiSpectralPoint q))) = _
      rw [tsum_mul_left]
      rfl
    _ = ∑ i, ∑ j, c i * (starRingEnd ℂ) (c j) *
          ccmContinuedCauchyKernel (z i : ℂ) (z j : ℂ) := by
      apply Finset.sum_congr rfl
      intro i _hi
      apply Finset.sum_congr rfl
      intro j _hj
      rw [xiWeilPolarization_cauchy_eq_continuedPrimeArchSource_dividedDifference
        (z i).property.1 (z i).property.2.1 (z i).property.2.2.1
        (z j).property.2.2.2.1 (z j).property.2.2.2.2.1
        (z j).property.2.2.2.2.2 (hsep i j)]
      rfl

/-- The explicit finite prime--Gamma source energy is exactly the unconditional Xi Weil Hilbert
quadratic value of a pairwise-separated indexed packet. -/
theorem xiWeilHilbertQuadratic_indexedCauchyPacket_eq_continuedSource_re
    {ι : Type*} [Fintype ι] (c : ι → ℂ)
    (z : ι → XiContinuedCauchyPoint)
    (hsep : ∀ i j, (z i : ℂ) ≠ (starRingEnd ℂ) (z j : ℂ)) :
    xiWeilHilbertQuadratic (xiWeilContinuedCauchyPacketLp c z) =
      (∑ i, ∑ j, c i * (starRingEnd ℂ) (c j) *
        ccmContinuedCauchyKernel (z i : ℂ) (z j : ℂ)).re := by
  rw [← xiWeilEvaluationLp_indexedCauchyPacket c z,
    xiWeilHilbertQuadratic_evaluation_eq_polarization_re,
    xiWeilPolarization_indexedCauchyPacket_eq_continuedSource c z hsep]

/-- The explicit real continued prime--Gamma energy of an indexed packet. -/
def continuedCauchyPacketSourceEnergy
    {ι : Type*} [Fintype ι] (c : ι → ℂ)
    (z : ι → XiContinuedCauchyPoint) : ℝ :=
  (∑ i, ∑ j, c i * (starRingEnd ℂ) (c j) *
    ccmContinuedCauchyKernel (z i : ℂ) (z j : ℂ)).re

/-- Every finite packet is approximated by pairwise-separated packets whose exact explicit
prime--Gamma energies converge to its unconditional Xi Weil Hilbert value. -/
theorem exists_pairwiseConjSeparatedContinuedSourceEnergy_tendsto
    {ι : Type*} [Fintype ι] (c : ι → ℂ)
    (z : ι → XiContinuedCauchyPoint) :
    ∃ w : ℕ → ι → XiContinuedCauchyPoint,
      (∀ n i j, (w n i : ℂ) ≠ (starRingEnd ℂ) (w n j : ℂ)) ∧
      Tendsto (fun n ↦ xiWeilContinuedCauchyPacketLp c (w n)) atTop
        (nhds (xiWeilContinuedCauchyPacketLp c z)) ∧
      Tendsto (fun n ↦ continuedCauchyPacketSourceEnergy c (w n)) atTop
        (nhds (xiWeilHilbertQuadratic (xiWeilContinuedCauchyPacketLp c z))) := by
  obtain ⟨w, hwsep, hw⟩ :=
    exists_pairwiseConjSeparatedContinuedCauchyPacketLp_tendsto c z
  refine ⟨w, hwsep, hw, ?_⟩
  have hQ := continuous_xiWeilHilbertQuadratic.continuousAt.tendsto.comp hw
  apply hQ.congr'
  exact Eventually.of_forall fun n ↦ by
    simpa [continuedCauchyPacketSourceEnergy] using
      xiWeilHilbertQuadratic_indexedCauchyPacket_eq_continuedSource_re
        c (w n) (hwsep n)

/-- Every vector in the continued Cauchy algebraic span has an actual finite indexed packet
representation. -/
theorem exists_finsupp_indexedCauchyPacket_eq_of_mem
    (v : lp (fun _ : XiZeroCopy => ℂ) 2)
    (hv : v ∈ xiWeilContinuedCauchyAlgebraicSubspace) :
    ∃ c : XiContinuedCauchyPoint →₀ ℂ,
      xiWeilContinuedCauchyPacketLp
        (fun i : {x // x ∈ c.support} ↦ c i.1)
        (fun i : {x // x ∈ c.support} ↦ i.1) = v := by
  rw [xiWeilContinuedCauchyAlgebraicSubspace] at hv
  obtain ⟨c, hc⟩ :=
    Finsupp.mem_span_range_iff_exists_finsupp.mp hv
  refine ⟨c, ?_⟩
  rw [← hc]
  unfold xiWeilContinuedCauchyPacketLp
  rw [Finsupp.sum]
  exact (Finset.sum_subtype c.support (fun _ => Iff.rfl)
    (fun i => c i • xiWeilContinuedCauchyLp i)).symm

end

end RHTower
