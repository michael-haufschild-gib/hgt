import GaloisForLFunctions.RHTower.Suzuki.SuzukiCausalDepthGammaTraceClassFeatureRobinTraceNoGo
import GaloisForLFunctions.HTGeometry.AtomicHausdorffSource
import GaloisForLFunctions.HTGeometry.TanhSubstitution

/-!
# Exact kernel of the infinite Suzuki causal-depth Gamma feature

Finite-packet strict positive definiteness does not imply faithfulness on an infinite Hilbert
source. This module proves the missing infinite statement for the literal causal-depth Gamma
feature operator.

The analytic input is complex atomic Hausdorff determinacy: an absolutely summable complex
family on distinct unit-interval nodes is zero when all its moments vanish. Applying this to the
surviving Gamma Jacobi tail shows that the global feature operator loses exactly the
feature-coordinate sector and no arithmetic source direction. Its positive trace-class energy
has the same exact kernel.

No Xi zero, Riemann-hypothesis premise, finite-support premise, numerical computation, or added
axiom is used.
-/

open scoped BigOperators ENNReal NNReal
open MeasureTheory
open GaloisForLFunctions.HTGeometry

noncomputable section

namespace GaloisForLFunctions.HTGeometry

/-- Absolutely summable complex atoms at distinct unit-interval nodes are determined by all
power moments. -/
theorem summableComplexAtom_eq_zero_of_moments_eq_zero
    {ι : Type*} [Countable ι] {b : ι → ℂ} {x : ι → HausdorffSourceSpace}
    (hb : Summable b) (hinj : Function.Injective x)
    (hmom : ∀ m : ℕ, ∑' i, b i * ((x i : ℝ) : ℂ) ^ m = 0) :
    ∀ i, b i = 0 := by
  have real_atom_zero {c : ι → ℝ} (hc : Summable c)
      (hmomc : ∀ m : ℕ, ∑' i, c i * (x i : ℝ) ^ m = 0) :
      ∀ i, c i = 0 := by
    let cp : ι → ℝ := fun i => max (c i) 0
    let cn : ι → ℝ := fun i => max (-c i) 0
    have hcp0 : ∀ i, 0 ≤ cp i := fun i => by simp [cp]
    have hcn0 : ∀ i, 0 ≤ cn i := fun i => by simp [cn]
    have hcp_le : ∀ i, cp i ≤ |c i| := by
      intro i
      dsimp [cp]
      rcases le_total 0 (c i) with h | h
      · simp [h, abs_of_nonneg h]
      · simp [h, abs_of_nonpos h]
    have hcn_le : ∀ i, cn i ≤ |c i| := by
      intro i
      dsimp [cn]
      rcases le_total 0 (c i) with h | h
      · simp [h, abs_of_nonneg h]
      · simp [h, abs_of_nonpos h]
    have hcp : Summable cp := Summable.of_nonneg_of_le hcp0 hcp_le hc.abs
    have hcn : Summable cn := Summable.of_nonneg_of_le hcn0 hcn_le hc.abs
    have hsplit : ∀ i, c i = cp i - cn i := by
      intro i
      dsimp [cp, cn]
      rcases le_total 0 (c i) with h | h
      · simp [h]
      · simp [h]
    let μp := atomicHausdorffSource cp x
    let μn := atomicHausdorffSource cn x
    letI : IsFiniteMeasure μp := isFiniteMeasure_atomicHausdorffSource hcp0 hcp
    letI : IsFiniteMeasure μn := isFiniteMeasure_atomicHausdorffSource hcn0 hcn
    have heq : μp = μn := hausdorffSource_eq_of_moments_eq (fun m => by
      rw [hausdorffMoment_atomicHausdorffSource hcp0 hcp,
        hausdorffMoment_atomicHausdorffSource hcn0 hcn]
      have hp : Summable (fun i => cp i * (x i : ℝ) ^ m) := by
        refine Summable.of_nonneg_of_le
          (fun i => mul_nonneg (hcp0 i) (pow_nonneg (x i).2.1 m)) (fun i => ?_) hcp
        exact mul_le_of_le_one_right (hcp0 i) (pow_le_one₀ (x i).2.1 (x i).2.2)
      have hn : Summable (fun i => cn i * (x i : ℝ) ^ m) := by
        refine Summable.of_nonneg_of_le
          (fun i => mul_nonneg (hcn0 i) (pow_nonneg (x i).2.1 m)) (fun i => ?_) hcn
        exact mul_le_of_le_one_right (hcn0 i) (pow_le_one₀ (x i).2.1 (x i).2.2)
      rw [← sub_eq_zero, ← hp.tsum_sub hn, ← hmomc m]
      exact tsum_congr (fun i => by rw [hsplit i, sub_mul]))
    intro i
    have hatom : ENNReal.ofReal (cp i) = ENNReal.ofReal (cn i) := by
      rw [← atomicHausdorffSource_singleton hinj i,
        ← atomicHausdorffSource_singleton hinj i]
      exact congrArg (fun μ : Measure HausdorffSourceSpace => μ {x i}) heq
    have hparts : cp i = cn i :=
      (ENNReal.ofReal_eq_ofReal_iff (hcp0 i) (hcn0 i)).mp hatom
    linarith [hsplit i]
  have hbre : Summable (fun i => (b i).re) :=
    (Complex.reCLM : ℂ →L[ℝ] ℝ).summable hb
  have hbim : Summable (fun i => (b i).im) :=
    (Complex.imCLM : ℂ →L[ℝ] ℝ).summable hb
  have hs (m : ℕ) : Summable (fun i => b i * ((x i : ℝ) : ℂ) ^ m) := by
    refine Summable.of_norm_bounded hb.norm (fun i => ?_)
    rw [norm_mul, ← Complex.ofReal_pow, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (pow_nonneg (x i).2.1 m)]
    exact mul_le_of_le_one_right (norm_nonneg (b i))
      (pow_le_one₀ (x i).2.1 (x i).2.2)
  have hre : ∀ i, (b i).re = 0 := real_atom_zero hbre (fun m => by
    have h := congrArg Complex.re (hmom m)
    rw [Complex.zero_re, Complex.re_tsum (hs m)] at h
    simpa [← Complex.ofReal_pow, Complex.mul_re] using h)
  have him : ∀ i, (b i).im = 0 := real_atom_zero hbim (fun m => by
    have h := congrArg Complex.im (hmom m)
    rw [Complex.zero_im, Complex.im_tsum (hs m)] at h
    simpa [← Complex.ofReal_pow, Complex.mul_im] using h)
  intro i
  exact Complex.ext (hre i) (him i)

end GaloisForLFunctions.HTGeometry

namespace RHTower

/-- Compact Hausdorff node attached to one positive prime-depth Gamma frequency. -/
def suzukiCausalDepthGammaHausdorffNode
    (pe : Nat.Primes × ℕ) : HausdorffSourceSpace :=
  ⟨Real.tanh (suzukiCausalDepthGammaFrequency pe),
    (tanh_pos_of_pos (suzukiCausalDepthGammaFrequency_pos pe)).le,
    (Real.tanh_lt_one _).le⟩

theorem suzukiCausalDepthGammaHausdorffNode_injective :
    Function.Injective suzukiCausalDepthGammaHausdorffNode := by
  intro x y h
  apply suzukiCausalDepthGammaFrequency_injective
  exact HTGeometry.tanh_strictMono.injective (congrArg Subtype.val h)

theorem suzukiCausalDepthGammaFeatureOperator_apply_inr
    (h a : ℝ) (hh : 0 < h) (ha : 0 < a)
    (v : SuzukiCausalDepthGammaTraceL2) (k : ℕ) :
    suzukiCausalDepthGammaFeatureOperator h a hh ha v (Sum.inr k) =
      ∑' pe : Nat.Primes × ℕ,
        (suzukiCausalDepthGammaWeightedFeature h a pe k : ℂ) * v (Sum.inl pe) := by
  let f : SuzukiCausalDepthGammaTraceIndex → ℂ := fun j =>
    suzukiCausalDepthGammaFeatureKernel h a (Sum.inr k, j) * v j
  have hall : Summable f :=
    HilbertSchmidt.summable_row_mul
      (suzukiCausalDepthGammaFeatureKernel_isHS hh ha) v (Sum.inr k)
  have hleft : HasSum (f ∘ Sum.inl)
      (∑' pe : Nat.Primes × ℕ,
        (suzukiCausalDepthGammaWeightedFeature h a pe k : ℂ) * v (Sum.inl pe)) := by
    have hs := (hall.comp_injective Sum.inl_injective).hasSum
    simpa [f, suzukiCausalDepthGammaFeatureKernel] using hs
  have hright : HasSum (f ∘ Sum.inr) 0 := by
    have hz : (f ∘ Sum.inr) = (fun _ : ℕ => (0 : ℂ)) := by
      funext l
      simp [f, suzukiCausalDepthGammaFeatureKernel]
    rw [hz]
    exact hasSum_zero
  have hsum := hleft.sum hright
  rw [suzukiCausalDepthGammaFeatureOperator, HilbertSchmidt.toOperator_apply,
    show (∑' j, suzukiCausalDepthGammaFeatureKernel h a (Sum.inr k, j) * v j) =
        ∑' j, f j by rfl,
    hsum.tsum_eq, add_zero]

theorem summable_suzukiCausalDepthGammaFeatureOperator_source_row
    (h a : ℝ) (hh : 0 < h) (ha : 0 < a)
    (v : SuzukiCausalDepthGammaTraceL2) (k : ℕ) :
    Summable (fun pe : Nat.Primes × ℕ =>
      (suzukiCausalDepthGammaWeightedFeature h a pe k : ℂ) * v (Sum.inl pe)) := by
  have hall :=
    HilbertSchmidt.summable_row_mul
      (suzukiCausalDepthGammaFeatureKernel_isHS hh ha) v (Sum.inr k)
  have hs := hall.comp_injective Sum.inl_injective
  change Summable (fun pe : Nat.Primes × ℕ =>
    (suzukiCausalDepthGammaWeightedFeature h a pe k : ℂ) * v (Sum.inl pe)) at hs
  exact hs

/-- Infinite Gamma-source faithfulness: the actual feature loses no arithmetic source direction. -/
theorem suzukiCausalDepthGammaFeatureOperator_source_eq_zero
    (h a : ℝ) (hh : 0 < h) (ha : 0 < a)
    {v : SuzukiCausalDepthGammaTraceL2}
    (hv : suzukiCausalDepthGammaFeatureOperator h a hh ha v = 0)
    (pe : Nat.Primes × ℕ) :
    v (Sum.inl pe) = 0 := by
  let c : (Nat.Primes × ℕ) → ℂ := fun qe =>
    (suzukiCausalDepthGammaWeightedFeature h a qe 1 : ℂ) * v (Sum.inl qe)
  have hc : Summable c := by
    simpa [c] using
      summable_suzukiCausalDepthGammaFeatureOperator_source_row h a hh ha v 1
  have hrowzero (m : ℕ) :
      (∑' qe : Nat.Primes × ℕ,
        (suzukiCausalDepthGammaWeightedFeature h a qe (m + 1) : ℂ) *
          v (Sum.inl qe)) = 0 := by
    have hcoord := congrArg (fun w : SuzukiCausalDepthGammaTraceL2 => w (Sum.inr (m + 1))) hv
    rw [suzukiCausalDepthGammaFeatureOperator_apply_inr] at hcoord
    simpa using hcoord
  have hmom (m : ℕ) :
      (∑' qe : Nat.Primes × ℕ,
        c qe * (((suzukiCausalDepthGammaHausdorffNode qe : HausdorffSourceSpace) : ℝ) : ℂ) ^ m) =
        0 := by
    let A : ℝ := semilocalArchimedeanJacobiNormalization 3
    let B : ℝ := semilocalArchimedeanJacobiNormalization (m + 3)
    have hidentity :
        (A : ℂ) *
            (∑' qe : Nat.Primes × ℕ,
              (suzukiCausalDepthGammaWeightedFeature h a qe (m + 1) : ℂ) *
                v (Sum.inl qe)) =
          (B : ℂ) *
            (∑' qe : Nat.Primes × ℕ,
              c qe *
                (((suzukiCausalDepthGammaHausdorffNode qe :
                  HausdorffSourceSpace) : ℝ) : ℂ) ^ m) := by
      rw [← tsum_mul_left, ← tsum_mul_left]
      apply tsum_congr
      intro qe
      simp only [c, A, B, suzukiCausalDepthGammaWeightedFeature,
        suzukiCausalDepthGammaFeature, suzukiCausalDepthGammaSurvivingDegree,
        gammaConductorJacobiFeature, suzukiCausalDepthGammaHausdorffNode]
      rw [show m + 3 = 3 + m by omega, pow_add]
      push_cast
      ring
    rw [hrowzero m, mul_zero, eq_comm] at hidentity
    have hB : (B : ℂ) ≠ 0 := by
      exact Complex.ofReal_ne_zero.mpr
        (ne_of_gt (semilocalArchimedeanJacobiNormalization_pos (m + 3)))
    exact (mul_eq_zero.mp hidentity).resolve_left hB
  have hczero :=
    GaloisForLFunctions.HTGeometry.summableComplexAtom_eq_zero_of_moments_eq_zero hc
      suzukiCausalDepthGammaHausdorffNode_injective hmom pe
  have hwf : 0 < suzukiCausalDepthGammaWeightedFeature h a pe 1 := by
    exact mul_pos (suzukiCausalDepthGammaWeight_pos hh ha pe)
      (gammaConductorJacobiFeature_pos 3
        (suzukiCausalDepthGammaFrequency_pos pe))
  exact (mul_eq_zero.mp hczero).resolve_left
    (Complex.ofReal_ne_zero.mpr (ne_of_gt hwf))

theorem suzukiCausalDepthGammaFeatureOperator_apply_inl
    (h a : ℝ) (hh : 0 < h) (ha : 0 < a)
    (v : SuzukiCausalDepthGammaTraceL2) (pe : Nat.Primes × ℕ) :
    suzukiCausalDepthGammaFeatureOperator h a hh ha v (Sum.inl pe) = 0 := by
  rw [suzukiCausalDepthGammaFeatureOperator, HilbertSchmidt.toOperator_apply]
  simp [suzukiCausalDepthGammaFeatureKernel]

/-- Closed linear sector consisting of pure surviving-feature coordinates. -/
def suzukiCausalDepthGammaFeatureSector : Submodule ℂ SuzukiCausalDepthGammaTraceL2 where
  carrier := {v | ∀ pe : Nat.Primes × ℕ, v (Sum.inl pe) = 0}
  zero_mem' := by simp
  add_mem' := by
    intro v w hv hw pe
    simp [hv pe, hw pe]
  smul_mem' := by
    intro c v hv pe
    simp [hv pe]

theorem suzukiCausalDepthGammaFeatureOperator_eq_zero_iff
    (h a : ℝ) (hh : 0 < h) (ha : 0 < a)
    (v : SuzukiCausalDepthGammaTraceL2) :
    suzukiCausalDepthGammaFeatureOperator h a hh ha v = 0 ↔
      v ∈ suzukiCausalDepthGammaFeatureSector := by
  constructor
  · intro hv
    exact fun pe =>
      suzukiCausalDepthGammaFeatureOperator_source_eq_zero h a hh ha hv pe
  · intro hv
    change ∀ pe : Nat.Primes × ℕ, v (Sum.inl pe) = 0 at hv
    apply lp.ext
    funext i
    rcases i with pe | k
    · rw [suzukiCausalDepthGammaFeatureOperator_apply_inl]
      rfl
    · rw [suzukiCausalDepthGammaFeatureOperator_apply_inr]
      simp [hv]

/-- Exact kernel of the actual infinite Gamma feature. -/
theorem suzukiCausalDepthGammaFeatureOperator_ker_eq_featureSector
    (h a : ℝ) (hh : 0 < h) (ha : 0 < a) :
    (suzukiCausalDepthGammaFeatureOperator h a hh ha).toLinearMap.ker =
        suzukiCausalDepthGammaFeatureSector := by
  ext v
  exact suzukiCausalDepthGammaFeatureOperator_eq_zero_iff h a hh ha v

/-- Exact kernel of the positive trace-class Gamma energy. -/
theorem suzukiCausalDepthGammaEnergyOperator_ker_eq_featureSector
    (h a : ℝ) (hh : 0 < h) (ha : 0 < a) :
    (suzukiCausalDepthGammaEnergyOperator h a hh ha).toLinearMap.ker =
        suzukiCausalDepthGammaFeatureSector := by
  rw [suzukiCausalDepthGammaEnergyOperator]
  calc
    (ContinuousLinearMap.adjoint
          (suzukiCausalDepthGammaFeatureOperator h a hh ha) ∘L
        suzukiCausalDepthGammaFeatureOperator h a hh ha).toLinearMap.ker =
        (suzukiCausalDepthGammaFeatureOperator h a hh ha).toLinearMap.ker := by
      simpa using ContinuousLinearMap.ker_adjoint_comp_self
        (suzukiCausalDepthGammaFeatureOperator h a hh ha)
    _ = suzukiCausalDepthGammaFeatureSector :=
      suzukiCausalDepthGammaFeatureOperator_ker_eq_featureSector h a hh ha

end RHTower
