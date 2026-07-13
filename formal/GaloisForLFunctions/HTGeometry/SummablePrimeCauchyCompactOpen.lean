import GaloisForLFunctions.HTGeometry.UniversalPrimeOrientationCompactOpen

/-!
# Compact-open gauge invariance for summable prime-log residues

The compact-open chamber law is not specific to signs.  Any two absolutely summable real residue
assignments on the prime-log divisor differ by a normally convergent series of rational Cauchy
atoms.  Hence they generate the same compact-open completed function ring once the common rational
atoms and complex constants are included.
-/

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions Topology Filter
open scoped BigOperators

noncomputable section

/-- A prime-log Cauchy carrier with an arbitrary real residue-mass sequence. -/
def summablePrimeCauchyCarrier (a : Nat.Primes → ℝ) (z : ℂ) : ℂ :=
  discreteHerglotz primeLogSupport a z

/-- The rational atom series changing one summable residue sequence into another. -/
def summablePrimeCauchyTransitionTerm
    (a b : Nat.Primes → ℝ) (p : Nat.Primes) (z : ℂ) : ℂ :=
  ((b p - a p : ℝ) : ℂ) * ((primeLogSupport p : ℂ) - z)⁻¹

/-- The transition atoms sum locally uniformly to the exact difference of the carriers. -/
theorem hasSumLocallyUniformlyOn_summablePrimeCauchyTransition
    (a b : Nat.Primes → ℝ)
    (ha : Summable fun p => ‖(a p : ℂ)‖)
    (hb : Summable fun p => ‖(b p : ℂ)‖) :
    HasSumLocallyUniformlyOn
      (fun p => summablePrimeCauchyTransitionTerm a b p)
      (fun z => summablePrimeCauchyCarrier b z - summablePrimeCauchyCarrier a z)
      upperHalfPlane := by
  have hB :=
    (summableLocallyUniformlyOn_discreteHerglotz primeLogSupport b hb).hasSumLocallyUniformlyOn
  have hA :=
    (summableLocallyUniformlyOn_discreteHerglotz primeLogSupport a ha).hasSumLocallyUniformlyOn
  have h := hB.sub hA
  simpa only [HasSumLocallyUniformlyOn, summablePrimeCauchyTransitionTerm,
    summablePrimeCauchyCarrier, discreteHerglotz, Finset.sum_sub_distrib,
    Pi.sub_apply, Complex.ofReal_sub, sub_mul] using h

/-- A finite rational transition between two summable residue assignments. -/
def summablePrimeCauchyFiniteTransition
    (a b : Nat.Primes → ℝ) (F : Finset Nat.Primes) (z : ℂ) : ℂ :=
  summablePrimeCauchyCarrier a z +
    ∑ p ∈ F, summablePrimeCauchyTransitionTerm a b p z

/-- Finite rational residue changes converge locally uniformly to the target carrier. -/
theorem tendstoLocallyUniformlyOn_summablePrimeCauchyFiniteTransition
    (a b : Nat.Primes → ℝ)
    (ha : Summable fun p => ‖(a p : ℂ)‖)
    (hb : Summable fun p => ‖(b p : ℂ)‖) :
    TendstoLocallyUniformlyOn
      (fun F => summablePrimeCauchyFiniteTransition a b F)
      (summablePrimeCauchyCarrier b) atTop upperHalfPlane := by
  have hcorr := hasSumLocallyUniformlyOn_summablePrimeCauchyTransition a b ha hb
  have hconst : TendstoLocallyUniformlyOn
      (fun _ : Finset Nat.Primes => summablePrimeCauchyCarrier a)
      (summablePrimeCauchyCarrier a) atTop upperHalfPlane := by
    apply TendstoUniformlyOn.tendstoLocallyUniformlyOn
    intro u hu
    exact Filter.Eventually.of_forall fun _ _ _ => refl_mem_uniformity hu
  have hadd := hconst.add hcorr
  have hshape : TendstoLocallyUniformlyOn
      (fun F => summablePrimeCauchyFiniteTransition a b F)
      (summablePrimeCauchyCarrier a + fun z =>
        summablePrimeCauchyCarrier b z - summablePrimeCauchyCarrier a z)
      atTop upperHalfPlane := by
    apply hadd.congr
    intro F z _
    rfl
  exact hshape.congr_right fun z _ => by simp

/-- A summable prime-log Cauchy carrier in the compact-open function space. -/
def summablePrimeCauchyContinuous
    (a : Nat.Primes → ℝ) (ha : Summable fun p => ‖(a p : ℂ)‖) :
    C(PrimeOrientationDomain, ℂ) where
  toFun z := summablePrimeCauchyCarrier a z
  continuous_toFun := continuousOn_iff_continuous_restrict.mp <|
    (differentiableOn_discreteHerglotz_upperHalfPlane primeLogSupport a ha).continuousOn

/-- A finite rational transition in the compact-open function space. -/
def summablePrimeCauchyFiniteTransitionContinuous
    (a b : Nat.Primes → ℝ) (ha : Summable fun p => ‖(a p : ℂ)‖)
    (F : Finset Nat.Primes) : C(PrimeOrientationDomain, ℂ) :=
  summablePrimeCauchyContinuous a ha +
    ∑ p ∈ F, ContinuousMap.const PrimeOrientationDomain ((b p - a p : ℝ) : ℂ) *
      primeOrientationCauchyAtom p

theorem coe_summablePrimeCauchyFiniteTransitionContinuous
    (a b : Nat.Primes → ℝ) (ha : Summable fun p => ‖(a p : ℂ)‖)
    (F : Finset Nat.Primes) (z : PrimeOrientationDomain) :
    summablePrimeCauchyFiniteTransitionContinuous a b ha F z =
      summablePrimeCauchyFiniteTransition a b F z := by
  simp [summablePrimeCauchyFiniteTransitionContinuous,
    summablePrimeCauchyFiniteTransition, summablePrimeCauchyTransitionTerm,
    summablePrimeCauchyContinuous, primeOrientationCauchyAtom]

/-- Finite rational transitions converge to their target in the compact-open topology. -/
theorem tendsto_summablePrimeCauchyFiniteTransitionContinuous
    (a b : Nat.Primes → ℝ)
    (ha : Summable fun p => ‖(a p : ℂ)‖)
    (hb : Summable fun p => ‖(b p : ℂ)‖) :
    Tendsto (summablePrimeCauchyFiniteTransitionContinuous a b ha)
      atTop (nhds (summablePrimeCauchyContinuous b hb)) := by
  apply ContinuousMap.tendsto_of_tendstoLocallyUniformly
  have h := tendstoLocallyUniformlyOn_summablePrimeCauchyFiniteTransition a b ha hb
  rw [tendstoLocallyUniformlyOn_iff_tendstoLocallyUniformly_comp_coe] at h
  simpa [Function.comp_def, coe_summablePrimeCauchyFiniteTransitionContinuous,
    summablePrimeCauchyContinuous] using h

/-- The algebraic ring generated by one summable carrier and the common rational atoms. -/
def summablePrimeCauchyAlgebraicRing
    (a : Nat.Primes → ℝ) (ha : Summable fun p => ‖(a p : ℂ)‖) :
    Subring C(PrimeOrientationDomain, ℂ) :=
  Subring.closure
    (insert (summablePrimeCauchyContinuous a ha) primeOrientationCommonGenerators)

/-- The compact-open completed ring generated by a summable carrier and the common atoms. -/
def summablePrimeCauchyCompletedRing
    (a : Nat.Primes → ℝ) (ha : Summable fun p => ‖(a p : ℂ)‖) :
    Subring C(PrimeOrientationDomain, ℂ) :=
  (summablePrimeCauchyAlgebraicRing a ha).topologicalClosure

theorem summablePrimeCauchyFiniteTransitionContinuous_mem_algebraicRing
    (a b : Nat.Primes → ℝ) (ha : Summable fun p => ‖(a p : ℂ)‖)
    (F : Finset Nat.Primes) :
    summablePrimeCauchyFiniteTransitionContinuous a b ha F ∈
      summablePrimeCauchyAlgebraicRing a ha := by
  apply Subring.add_mem
  · exact Subring.subset_closure (Set.mem_insert _ _)
  · apply Subring.sum_mem
    intro p hp
    apply Subring.mul_mem
    · apply Subring.subset_closure
      exact Set.mem_insert_iff.mpr <| Or.inr <| Or.inl ⟨_, rfl⟩
    · apply Subring.subset_closure
      exact Set.mem_insert_iff.mpr <| Or.inr <| Or.inr ⟨p, rfl⟩

/-- Every summable carrier belongs to the completed ring generated by every other summable
carrier and the common rational atoms. -/
theorem summablePrimeCauchyContinuous_mem_completedRing
    (a b : Nat.Primes → ℝ)
    (ha : Summable fun p => ‖(a p : ℂ)‖)
    (hb : Summable fun p => ‖(b p : ℂ)‖) :
    summablePrimeCauchyContinuous b hb ∈ summablePrimeCauchyCompletedRing a ha := by
  show summablePrimeCauchyContinuous b hb ∈
    closure (summablePrimeCauchyAlgebraicRing a ha : Set C(PrimeOrientationDomain, ℂ))
  exact mem_closure_of_tendsto
    (tendsto_summablePrimeCauchyFiniteTransitionContinuous a b ha hb)
    (Filter.Eventually.of_forall fun F =>
      summablePrimeCauchyFiniteTransitionContinuous_mem_algebraicRing a b ha F)

/-- Closed-ring membership cannot distinguish two summable residue carriers once the common
rational atoms and constants are present.  This applies in particular to every compact-open
closed differential subring satisfying the same generator condition. -/
theorem summablePrimeCauchyContinuous_mem_closedRing_iff
    (a b : Nat.Primes → ℝ)
    (ha : Summable fun p => ‖(a p : ℂ)‖)
    (hb : Summable fun p => ‖(b p : ℂ)‖)
    (R : Subring C(PrimeOrientationDomain, ℂ))
    (hR : IsClosed (R : Set C(PrimeOrientationDomain, ℂ)))
    (hcommon : primeOrientationCommonGenerators ⊆ R) :
    summablePrimeCauchyContinuous a ha ∈ R ↔
      summablePrimeCauchyContinuous b hb ∈ R := by
  constructor
  · intro haR
    apply hR.mem_of_tendsto
      (tendsto_summablePrimeCauchyFiniteTransitionContinuous a b ha hb)
    exact Filter.Eventually.of_forall fun F => by
      apply R.add_mem haR
      apply R.sum_mem
      intro p hp
      exact R.mul_mem
        (hcommon (Or.inl ⟨_, rfl⟩))
        (hcommon (Or.inr ⟨p, rfl⟩))
  · intro hbR
    apply hR.mem_of_tendsto
      (tendsto_summablePrimeCauchyFiniteTransitionContinuous b a hb ha)
    exact Filter.Eventually.of_forall fun F => by
      apply R.add_mem hbR
      apply R.sum_mem
      intro p hp
      exact R.mul_mem
        (hcommon (Or.inl ⟨_, rfl⟩))
        (hcommon (Or.inr ⟨p, rfl⟩))

/-- **Summable-residue gauge invariance.** Every absolutely summable real residue assignment on
one fixed prime-log divisor generates the same compact-open completed rational Cauchy ring. -/
theorem summablePrimeCauchyCompletedRing_eq
    (a b : Nat.Primes → ℝ)
    (ha : Summable fun p => ‖(a p : ℂ)‖)
    (hb : Summable fun p => ‖(b p : ℂ)‖) :
    summablePrimeCauchyCompletedRing a ha = summablePrimeCauchyCompletedRing b hb := by
  apply le_antisymm
  · intro f hf
    change f ∈ closure
      (summablePrimeCauchyAlgebraicRing a ha : Set C(PrimeOrientationDomain, ℂ)) at hf
    apply (closure_minimal _ (Subring.isClosed_topologicalClosure
      (summablePrimeCauchyAlgebraicRing b hb))) hf
    apply Subring.closure_le.mpr
    intro g hg
    rcases hg with rfl | hg
    · exact summablePrimeCauchyContinuous_mem_completedRing b a hb ha
    · exact Subring.le_topologicalClosure (summablePrimeCauchyAlgebraicRing b hb)
        (Subring.subset_closure (Set.mem_insert_iff.mpr (Or.inr hg)))
  · intro f hf
    change f ∈ closure
      (summablePrimeCauchyAlgebraicRing b hb : Set C(PrimeOrientationDomain, ℂ)) at hf
    apply (closure_minimal _ (Subring.isClosed_topologicalClosure
      (summablePrimeCauchyAlgebraicRing a ha))) hf
    apply Subring.closure_le.mpr
    intro g hg
    rcases hg with rfl | hg
    · exact summablePrimeCauchyContinuous_mem_completedRing a b ha hb
    · exact Subring.le_topologicalClosure (summablePrimeCauchyAlgebraicRing a ha)
        (Subring.subset_closure (Set.mem_insert_iff.mpr (Or.inr hg)))

end

end GaloisForLFunctions.HTGeometry
