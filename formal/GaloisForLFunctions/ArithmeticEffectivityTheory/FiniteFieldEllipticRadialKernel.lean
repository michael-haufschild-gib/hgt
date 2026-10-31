import GaloisForLFunctions.ArithmeticEffectivityTheory.FiniteFieldEllipticCylinderIntegrals

/-!
# The actual adelic radial spectral kernel

The logarithmic local heights have finite support away from infinity.
Integral translations preserve them, so the global kernel is continuous.
On each finite cylinder it is exactly the product of the local kernels.
-/

namespace GaloisForLFunctions.ArithmeticEffectivityTheory.FiniteFieldEllipticBase
open MeasureTheory Filter Function
open HTGeometry.DiscreteValuationHaar HTGeometry.LoopEisenstein
open scoped NNReal Topology WithZero WithZeroMulInt
noncomputable section

local instance radialKernelFiniteMeasurable (v : FinitePlace) :
    MeasurableSpace (v.adicCompletion K) := borel _
local instance radialKernelFiniteBorel (v : FinitePlace) :
    BorelSpace (v.adicCompletion K) := ⟨rfl⟩
local instance radialKernelIntegerSecondCountable (v : FinitePlace) :
    SecondCountableTopology (v.adicCompletionIntegers K) :=
  (Valued.isOpen_valuationSubring (v.adicCompletion K)).isOpenEmbedding_subtypeVal.isEmbedding.secondCountableTopology
local instance radialKernelInfinityMeasurable : MeasurableSpace InfinityCompletion := borel _
local instance radialKernelInfinityBorel : BorelSpace InfinityCompletion := ⟨rfl⟩

private theorem max_valuation_add_integral {L : Type*} [Field L]
    (v : Valuation L ℤᵐ⁰) (x y : L) (hy : v y ≤ 1) :
    max 1 (v (x+y)) = max 1 (v x) := by
  apply le_antisymm
  · exact max_le (le_max_left _ _) ((v.map_add x y).trans
      (max_le (le_max_right _ _) (hy.trans (le_max_left _ _))))
  · apply max_le (le_max_left _ _)
    have h := v.map_sub (x+y) y
    rw [add_sub_cancel_right] at h
    exact h.trans (max_le (le_max_right _ _) (hy.trans (le_max_left _ _)))

private theorem max_magnitude_add_integral {L : Type*} [Field L]
    (v : Valuation L ℤᵐ⁰) (q : ℝ≥0) (hq : 1 < q) (x y : L) (hy : v y ≤ 1) :
    max 1 (WithZeroMulInt.toNNReal hq.ne_zero (v (x+y)) : ℝ) =
      max 1 (WithZeroMulInt.toNNReal hq.ne_zero (v x) : ℝ) := by
  have hm : Monotone (WithZeroMulInt.toNNReal hq.ne_zero) :=
    (WithZeroMulInt.toNNReal_strictMono hq).monotone
  have hmag : max 1 (WithZeroMulInt.toNNReal hq.ne_zero (v (x+y))) =
      max 1 (WithZeroMulInt.toNNReal hq.ne_zero (v x)) := by
    calc
      _ = WithZeroMulInt.toNNReal hq.ne_zero (max 1 (v (x+y))) := by
        rw [hm.map_max, map_one]
      _ = WithZeroMulInt.toNNReal hq.ne_zero (max 1 (v x)) :=
        congrArg (WithZeroMulInt.toNNReal hq.ne_zero) (max_valuation_add_integral v x y hy)
      _ = _ := by rw [hm.map_max, map_one]
  exact_mod_cast hmag

local instance radialKernelFiniteCompact (v : FinitePlace) : CompactSpace (Integer (v.adicCompletion K)) :=
  finiteCompletionInteger_compact v

private theorem finiteResidue_gt_one (v : FinitePlace) :
    (1 : ℝ≥0) < Nat.card (RingOfIntegers ⧸ v.asIdeal) := by
  have hcard : Nat.card (Residue (v.adicCompletion K)) =
      Nat.card (RingOfIntegers ⧸ v.asIdeal) := Nat.card_congr (finiteCompletionResidueEquiv v).toEquiv
  rw [← hcard]
  exact_mod_cast residue_card_gt_one (v.adicCompletion K)

/-- The finite-place logarithmic radial height. -/
def finiteCompletionLogHeight (v : FinitePlace) (x : v.adicCompletion K) : ℝ :=
  Real.log (max 1 (finiteCompletionMagnitude v x : ℝ))

/-- The infinity logarithmic radial height. -/
def infinityCompletionLogHeight (x : InfinityCompletion) : ℝ :=
  Real.log (max 1 (infinityCompletionMagnitude x : ℝ))

private theorem finiteLogHeight_add_integral (v : FinitePlace) (x y : v.adicCompletion K)
    (hy : y ∈ v.adicCompletionIntegers K) :
    finiteCompletionLogHeight v (x+y) = finiteCompletionLogHeight v x := by
  apply congrArg Real.log
  change max 1 (WithZeroMulInt.toNNReal (finiteResidue_gt_one v).ne_zero
      (Valued.v (x+y)) : ℝ) =
    max 1 (WithZeroMulInt.toNNReal (finiteResidue_gt_one v).ne_zero (Valued.v x) : ℝ)
  exact max_magnitude_add_integral Valued.v _ (finiteResidue_gt_one v) x y hy

private theorem infinityLogHeight_add_integral (x y : InfinityCompletion)
    (hy : y ∈ Integer InfinityCompletion) :
    infinityCompletionLogHeight (x+y) = infinityCompletionLogHeight x := by
  apply congrArg Real.log
  change max 1 (WithZeroMulInt.toNNReal (by norm_num : (3:ℝ≥0) ≠ 0)
      (Valued.v (x+y)) : ℝ) =
    max 1 (WithZeroMulInt.toNNReal (by norm_num : (3:ℝ≥0) ≠ 0) (Valued.v x) : ℝ)
  exact max_magnitude_add_integral Valued.v 3 (by norm_num) x y hy

private theorem finiteLogHeight_zero_of_integral (v : FinitePlace) (x : v.adicCompletion K)
    (hx : x ∈ v.adicCompletionIntegers K) : finiteCompletionLogHeight v x = 0 := by
  have h := finiteLogHeight_add_integral v 0 x hx
  simpa only [zero_add, finiteCompletionLogHeight, map_zero, NNReal.coe_zero,
    max_eq_left zero_le_one, Real.log_one] using h

/-- Restricted-product integrality makes the logarithmic local height finitely supported. -/
theorem finiteCompletionLogHeight_support (a : FiniteAdeles) :
    HasFiniteSupport (fun v : FinitePlace => finiteCompletionLogHeight v (a v)) := by
  apply Filter.eventually_cofinite.mp
  filter_upwards [a.2] with v hv
  exact finiteLogHeight_zero_of_integral v (a v) hv

/-- The sum of the actual normalized logarithmic local heights. -/
def adelicLogHeight (a : Adeles) : ℝ :=
  (∑ᶠ v : FinitePlace, finiteCompletionLogHeight v (a.1 v)) + infinityCompletionLogHeight a.2

/-- The actual adelic radial spectral kernel. -/
def ellipticAdeleSpectralKernel (s : ℂ) (a : Adeles) : ℂ :=
  Complex.exp (-(s+1) * (adelicLogHeight a : ℂ))

/-- Integral translations leave every local and global radial height unchanged. -/
theorem adelicLogHeight_add_integral (a b : Adeles) (hb : b ∈ integralAdeles) :
    adelicLogHeight (a+b) = adelicLogHeight a := by
  unfold adelicLogHeight
  congr 1
  · exact finsum_congr fun v => finiteLogHeight_add_integral v (a.1 v) (b.1 v) (hb.1 v)
  · exact infinityLogHeight_add_integral a.2 b.2 hb.2

/-- The global radial height is constant on each open integral-adele coset. -/
theorem continuous_adelicLogHeight : Continuous adelicLogHeight := by
  apply continuous_iff_continuousAt.mpr
  intro a
  let V : Set Adeles := {b | b-a ∈ integralAdeles}
  have hopen : IsOpen V := integralAdeles_isOpen.preimage (continuous_id.sub continuous_const)
  have ha : a ∈ V := by
    change a-a ∈ integralAdeles
    rw [sub_self]
    exact ⟨fun _ => zero_mem _, zero_mem _⟩
  have heq : (fun _ : Adeles => adelicLogHeight a) =ᶠ[𝓝 a] adelicLogHeight := by
    filter_upwards [hopen.mem_nhds ha] with b hb
    have he : a+(b-a) = b := by abel
    exact (adelicLogHeight_add_integral a (b-a) hb).symm.trans
      (congrArg adelicLogHeight he)
  exact tendsto_const_nhds.congr' heq

/-- The actual adelic spectral kernel is continuous. -/
theorem continuous_ellipticAdeleSpectralKernel (s : ℂ) :
    Continuous (ellipticAdeleSpectralKernel s) :=
  Complex.continuous_exp.comp
    (continuous_const.mul (Complex.continuous_ofReal.comp continuous_adelicLogHeight))

/-- Complex absolute values are exactly the real-parameter radial kernel. -/
theorem norm_ellipticAdeleSpectralKernel (s : ℂ) (a : Adeles) :
    ‖ellipticAdeleSpectralKernel s a‖ =
      Real.exp (-(s.re+1) * adelicLogHeight a) := by
  rw [ellipticAdeleSpectralKernel, Complex.norm_exp]
  simp only [Complex.mul_re, Complex.neg_re, Complex.add_re, Complex.one_re,
    Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]


/-- On an actual finite cylinder the global logarithmic height is a finite sum. -/
theorem adelicLogHeight_cylinder (S : Finset FinitePlace)
    (x : EllipticCylinderCoordinates S) :
    adelicLogHeight (ellipticCylinderAssembly S x) =
      (∑ v : S, finiteCompletionLogHeight v.1 (x.1.1 v)) +
        infinityCompletionLogHeight x.2 := by
  classical
  have hs : support (fun v : FinitePlace =>
      finiteCompletionLogHeight v ((ellipticCylinderAssembly S x).1 v)) ⊆ S := by
    intro v hv
    by_contra hn
    apply hv
    change finiteCompletionLogHeight v ((finiteCylinderAssembly S x.1 : FiniteAdeles) v) = 0
    rw [finiteCylinderAssembly_apply_notMem S x.1 ⟨v, hn⟩]
    exact finiteLogHeight_zero_of_integral v _ (x.1.2 ⟨v, hn⟩).property
  unfold adelicLogHeight
  rw [finsum_eq_sum_of_support_subset _ hs]
  congr 1
  rw [← Finset.sum_attach]
  apply Finset.sum_congr rfl
  intro v _
  exact congrArg (finiteCompletionLogHeight v.1)
    (finiteCylinderAssembly_apply_mem S x.1 v)

/-- The global kernel restricts to the independently defined finite local product. -/
theorem ellipticAdeleSpectralKernel_cylinder (S : Finset FinitePlace) (s : ℂ)
    (x : EllipticCylinderCoordinates S) :
    ellipticAdeleSpectralKernel s (ellipticCylinderAssembly S x) =
      ellipticCylinderSpectralKernel S s x := by
  rw [ellipticAdeleSpectralKernel, adelicLogHeight_cylinder,
    Complex.ofReal_add, mul_add, Complex.exp_add]
  unfold ellipticCylinderSpectralKernel finiteCylinderSpectralKernel
  congr 1
  rw [Complex.ofReal_sum, Finset.mul_sum, Complex.exp_sum]
  rfl

/-- The actual global kernel is integrable on every finite cylinder for positive real part. -/
theorem ellipticAdeleSpectralKernel_integrableOn_cylinder (S : Finset FinitePlace)
    (s : ℂ) (hs : 0 < s.re) :
    IntegrableOn (ellipticAdeleSpectralKernel s) (ellipticAdeleCylinder S) adeleHaar := by
  apply ((ellipticCylinderAssembly_measurePreserving S).integrable_comp_emb
    (ellipticCylinderAssembly_isOpenEmbedding S).measurableEmbedding).mp
  have he : ellipticAdeleSpectralKernel s ∘ ellipticCylinderAssembly S =
      ellipticCylinderSpectralKernel S s := by
    funext x
    exact ellipticAdeleSpectralKernel_cylinder S s x
  rw [he]
  exact ellipticCylinderSpectralKernel_integrable S s hs

end
end GaloisForLFunctions.ArithmeticEffectivityTheory.FiniteFieldEllipticBase

#print axioms GaloisForLFunctions.ArithmeticEffectivityTheory.FiniteFieldEllipticBase.continuous_ellipticAdeleSpectralKernel
#print axioms GaloisForLFunctions.ArithmeticEffectivityTheory.FiniteFieldEllipticBase.ellipticAdeleSpectralKernel_cylinder
#print axioms GaloisForLFunctions.ArithmeticEffectivityTheory.FiniteFieldEllipticBase.ellipticAdeleSpectralKernel_integrableOn_cylinder
