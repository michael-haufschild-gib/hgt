/-
First-pass row majorants adapted from OpenAI's formalization, Apache-2.0.
See LICENSE and NOTICE in the parent directory for source attribution.
-/
import GaloisForLFunctions.MetaplecticMobiusDescent.CubicSieve.FirstPassGaussBlocks

/-!
# First-pass row majorants

Row majorants and fixed residue columns of the first pass: residue phases become scalars
outside the second input row and cost at most four in the squared energy. Integrated transfer
of the global second mode (`SecondPassIntegration`).
-/

noncomputable section
open MeasureTheory Set Filter
open scoped BigOperators Classical Topology InnerProductSpace ComplexConjugate MatrixGroups ENNReal
namespace GaloisForLFunctions.MetaplecticMobiusDescent.CubicEisenstein
open Eisenstein CubicJacobi CubicKubota CubicRamified
open scoped NNReal Pointwise
open RationalSource
open scoped Manifold ContDiff
open scoped Matrix
open UniqueFactorizationMonoid
open Asymptotics
open scoped ContDiff FourierTransform SchwartzMap
open scoped ContDiff FourierTransform SchwartzMap
open scoped BigOperators Topology
open Filter Asymptotics MeasureTheory
open scoped BigOperators Topology
open Filter Asymptotics MeasureTheory
open scoped BigOperators
open scoped BigOperators Topology
open Filter Asymptotics MeasureTheory
open scoped BigOperators Topology
open Filter Asymptotics MeasureTheory
open scoped BigOperators Topology
open Filter
open scoped BigOperators Classical SchwartzMap
open scoped BigOperators Classical SchwartzMap
open scoped Classical SchwartzMap FourierTransform ContDiff

namespace FirstPassCubeLabels
open Eisenstein SchwartzPlanePoisson SecondPassArithmetic MeasureTheory
open scoped Classical SchwartzMap

theorem firstResidueWeight_norm_le {ι : Type*} [DecidableEq ι] (p : ι → O)
    (D : Finset ι) (h : O) (r : QuadraticRayRing × QuadraticRayRing) :
    ‖firstResidueWeight p rayQuadraticPair D h r‖ ≤ 2 := by
  have hm : ‖primeCoprimeMask p D h‖ ≤ 1 := by
    rw [primeCoprimeMask_indicator]
    split_ifs <;> simp
  have hμ : ‖supportMobius D‖ = 1 := by simp [supportMobius]
  rw [firstResidueWeight, norm_mul, norm_mul, hμ, one_mul]
  exact (mul_le_mul hm (rayQuadraticPair_norm _ _) (norm_nonneg _) zero_le_one).trans_eq (one_mul 2)

def firstRayIntegrand {ι : Type*} [DecidableEq ι]
    (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hg : ∀ i, lambda ∉ Ideal.span {p i}) (F D B : Finset ι)
    (v : ι → ℕ) (ε₁ ε₂ : ι → Bool) (negative : Bool)
    (r : QuadraticRayRing × QuadraticRayRing) (C : Finset ι → ℂ) (V : ℝ → ℂ)
    (y : Finset ι → ℝ) (c d f h : O) (b : 𝓢(ℝ, ℂ)) (t : ℝ) : ℝ :=
  ‖b t‖ * ‖cubeBaseFactor p hp hg B v ε₁ ε₂ d h‖ * ‖firstResidueWeight p rayQuadraticPair D h r‖ *
    ‖firstResidueColumn p (fun i => complexSexticChar (Ideal.span {p i}) (hg i)) F D (if negative then r.1 else r.2)
      (cubeLogCoefficient p hg B v ε₁ ε₂ negative
        (originalLabelColumn p hg B ε₁ ε₂ negative C c f) V y t d)
      h‖ ^ 2

theorem firstRayIntegrand_integrable {ι : Type*} [DecidableEq ι]
    (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (hg : ∀ i, lambda ∉ Ideal.span {p i}) (F D B : Finset ι)
    (v : ι → ℕ) (ε₁ ε₂ : ι → Bool) (hv : ∀ j ∈ B, 0 < v j)
    (negative : Bool) (r : QuadraticRayRing × QuadraticRayRing) (C : Finset ι → ℂ) (V : ℝ → ℂ)
    (y : Finset ι → ℝ) (c d f h : O) (b : 𝓢(ℝ, ℂ)) :
    Integrable (firstRayIntegrand p hp hg F D B v ε₁ ε₂ negative r C V y c d f h b) volume := by
  have hi := dilatedCoreRow_integrable p hg F D B v ε₁ ε₂ negative
    (if negative then r.1 else r.2) C V y c d (h * f ^ 2 * dilationLabel p B v ε₁ ε₂)
    b.integrable.norm
  convert hi.mul_const (‖cubeBaseFactor p hp hg B v ε₁ ε₂ d h‖ * ‖firstResidueWeight p rayQuadraticPair D h r‖ *
    ‖beforeDilationLabel p hg p B v ε₁ ε₂ negative c d f D‖ ^ 2) using 1
  funext t
  simp only [firstRayIntegrand, firstResidueColumn_cube_labels p hg F D B (if negative then r.1 else r.2) v ε₁ ε₂ hv,
    norm_mul, mul_pow, dilatedCoreRow]
  ring

theorem first_ray_energy_integral (deltaLoss : ℝ) (hδ : 0 < deltaLoss) :
    ∃ K : ℝ, 0 < K ∧ ∀ {ι : Type*} [DecidableEq ι]
      (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
      (hinj : Function.Injective (fun i => Ideal.span {p i}))
        (hg : ∀ i, lambda ∉ Ideal.span {p i})
      (hc : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2)
      (F D B : Finset ι) (v : ι → ℕ) (ε₁ ε₂ : ι → Bool) (hv : ∀ j ∈ B, 0 < v j)
      (negative : Bool) (r : QuadraticRayRing × QuadraticRayRing) (C : Finset ι → ℂ)
      (V : ℝ → ℂ) (y : Finset ι → ℝ) (c d : O)
      (s : Finset (Ideal O × O)) (T : Finset O) (w : Ideal O × O → ℂ)
      (b : Ideal O × O → 𝓢(ℝ, ℂ)) (J : ℕ) (M H Y : ℝ),
      0 ≤ M → 0 ≤ H →
      (∀ x ∈ s, DescentWeightedCauchy.firstElementRowMap (dilationLabel p B v ε₁ ε₂) x ∈ T) →
      (∀ z ∈ T, z ≠ 0) → (∀ z ∈ T, (Ideal.absNorm (Ideal.span {z}) : ℝ) ≤ Y) →
      (∀ x ∈ s, ‖w x‖ ≤ M) →
      (∀ x ∈ s, ∀ t : ℝ, ‖b x t‖ ≤ H * firstLogDensity J t) →
      (∑ x ∈ s, ‖w x‖ * ∫ t : ℝ,
        firstRayIntegrand p hp hg F D B v ε₁ ε₂ negative r C V y c d
          (cubicIdealGenerator x.1) x.2 (b x) t) ≤
      (M * H * K * Y ^ deltaLoss * (2 : ℝ)) *
        ∫ t : ℝ, firstLogDensity J t * ∑ z ∈ T,
          ‖dilatedCoreRow p hg F D B v ε₁ ε₂ negative
            (if negative then r.1 else r.2) C V y c d t z‖ ^ 2 := by
  obtain ⟨K, hK, hpoint⟩ := first_cube_energy_small_power deltaLoss hδ
  refine ⟨K, hK, ?_⟩
  intro ι _ p hp _ hinj hg hc F D B v ε₁ ε₂ hv negative r C V y c d s T w b J M H Y hM hH hmap hT hnorm hw hdom
  let Ψ := fun t z => dilatedCoreRow p hg F D B v ε₁ ε₂ negative
    (if negative then r.1 else r.2) C V y c d t z
  let source := fun t : ℝ => ∑ x ∈ s, ‖w x‖ *
    firstRayIntegrand p hp hg F D B v ε₁ ε₂ negative r C V y c d
      (cubicIdealGenerator x.1) x.2 (b x) t
  let target := fun t : ℝ => firstLogDensity J t * ∑ z ∈ T, ‖Ψ t z‖ ^ 2
  have isource : Integrable source volume := by
    apply integrable_finsetSum
    intro x hx
    exact (firstRayIntegrand_integrable p hp hinj hg F D B v ε₁ ε₂ hv negative r C V y c d _ _ (b x)).const_mul ‖w x‖
  have itarget : Integrable target volume := by
    simp only [target, Finset.mul_sum]
    exact integrable_finsetSum _ (fun z hz =>
      dilatedCoreRow_integrable p hg F D B v ε₁ ε₂ negative
        (if negative then r.1 else r.2) C V y c d z (firstLogDensity_integrable J))
  have hst (t : ℝ) : source t ≤ (M * H * K * Y ^ deltaLoss * (2 : ℝ)) * target t := by
    let wt := fun x : Ideal O × O => w x * (b x t) *
      cubeBaseFactor p hp hg B v ε₁ ε₂ d x.2 * firstResidueWeight p rayQuadraticPair D x.2 r
    have hwt (x) (hx : x ∈ s) : ‖wt x‖ ≤ M * H * firstLogDensity J t * (2 : ℝ) := by
      simp only [wt, norm_mul]
      calc
        _ ≤ M * (H * firstLogDensity J t) * 1 * (2 : ℝ) := by
          have hden := firstLogDensity_nonneg J t
          gcongr <;> first
            | positivity
            | exact hw x hx
            | exact hdom x hx t
            | exact cubeBaseFactor_norm_le_one p hp hinj hg hc B v ε₁ ε₂ d x.2
            | exact firstResidueWeight_norm_le p D x.2 r
        _ = _ := by ring
    have hh := hpoint p hg F D B v ε₁ ε₂ hv negative
      (if negative then r.1 else r.2) C V y t c d s T wt
      (M * H * firstLogDensity J t * (2 : ℝ)) Y
      (by exact mul_nonneg (mul_nonneg (mul_nonneg hM hH) (firstLogDensity_nonneg J t)) (by norm_num))
      hmap hT hnorm hwt
    convert hh using 1
    · apply Finset.sum_congr rfl
      intro x hx
      simp only [firstRayIntegrand, wt, norm_mul]
      ring
    · dsimp only [target, Ψ, dilatedCoreRow]
      ring
  calc
    _ = ∫ t : ℝ, source t := by
      rw [integral_finsetSum _ (fun x hx =>
        (firstRayIntegrand_integrable p hp hinj hg F D B v ε₁ ε₂ hv negative r C V y c d _ _ (b x)).const_mul ‖w x‖)]
      exact Finset.sum_congr rfl (fun x hx => (integral_const_mul _ _).symm)
    _ ≤ ∫ t : ℝ, (M * H * K * Y ^ deltaLoss * (2 : ℝ)) * target t :=
      integral_mono isource (itarget.const_mul _) hst
    _ = _ := integral_const_mul _ _

end FirstPassCubeLabels

namespace FirstPassCubeLabels
open Eisenstein SchwartzPlanePoisson SecondPassArithmetic MeasureTheory
open scoped Classical SchwartzMap

theorem firstColumnEnergy_eq_sum_integrals {ι : Type*} [DecidableEq ι]
    (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (hg : ∀ i, lambda ∉ Ideal.span {p i}) (F B : Finset ι)
    (v : ι → ℕ) (ε₁ ε₂ : ι → Bool) (hv : ∀ j ∈ B, 0 < v j)
    (negative : Bool) (C : Finset ι → ℂ) (V : ℝ → ℂ) (X : ℝ)
    (c d f h : O) (b : 𝓢(ℝ, ℂ)) :
    firstColumnEnergy p hp hg F B v ε₁ ε₂ negative
      (originalLabelColumn p hg B ε₁ ε₂ negative C c f) V X d h b =
    ∑ D ∈ F.powerset, ∑ r : QuadraticRayRing × QuadraticRayRing,
      ∫ t : ℝ, firstRayIntegrand p hp hg F D B v ε₁ ε₂ negative r
        (normalizedColumn p C) V (columnLog p X) c d f h b t := by
  have hi (r : QuadraticRayRing × QuadraticRayRing) (D : Finset ι) :=
    firstRayIntegrand_integrable p hp hinj hg F D B v ε₁ ε₂ hv negative r
      (normalizedColumn p C) V (columnLog p X) c d f h b
  calc
    _ = ∫ t : ℝ, ∑ D ∈ F.powerset, ∑ r : QuadraticRayRing × QuadraticRayRing,
      firstRayIntegrand p hp hg F D B v ε₁ ε₂ negative r
        (normalizedColumn p C) V (columnLog p X) c d f h b t := by
      unfold firstColumnEnergy
      rw [normalized_originalLabelColumn]
      apply integral_congr_ae
      filter_upwards [] with t
      simp only [firstResidueEnergy, firstRayIntegrand, Finset.mul_sum, mul_assoc]
    _ = _ := by
      rw [integral_finsetSum _ (fun D hD => integrable_finsetSum _ (fun r hr => hi r D))]
      apply Finset.sum_congr rfl
      intro D hD
      exact integral_finsetSum _ (fun r hr => hi r D)

theorem first_column_energy_integral (deltaLoss : ℝ) (hδ : 0 < deltaLoss) :
    ∃ K : ℝ, 0 < K ∧ ∀ {ι : Type*} [DecidableEq ι]
      (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
      (_hinj : Function.Injective (fun i => Ideal.span {p i}))
        (hg : ∀ i, lambda ∉ Ideal.span {p i})
      (_hc : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2)
      (F B : Finset ι) (v : ι → ℕ) (ε₁ ε₂ : ι → Bool) (_hv : ∀ j ∈ B, 0 < v j)
      (negative : Bool) (C : Finset ι → ℂ) (V : ℝ → ℂ) (X : ℝ) (c d : O)
      (s : Finset (Ideal O × O)) (T : Finset O) (w : Ideal O × O → ℂ)
      (b : Ideal O × O → 𝓢(ℝ, ℂ)) (J : ℕ) (M H Y : ℝ),
      0 ≤ M → 0 ≤ H →
      (∀ x ∈ s, DescentWeightedCauchy.firstElementRowMap (dilationLabel p B v ε₁ ε₂) x ∈ T) →
      (∀ z ∈ T, z ≠ 0) → (∀ z ∈ T, (Ideal.absNorm (Ideal.span {z}) : ℝ) ≤ Y) →
      (∀ x ∈ s, ‖w x‖ ≤ M) →
      (∀ x ∈ s, ∀ t : ℝ, ‖b x t‖ ≤ H * firstLogDensity J t) →
      (∑ x ∈ s, ‖w x‖ * firstColumnEnergy p hp hg F B v ε₁ ε₂ negative
        (originalLabelColumn p hg B ε₁ ε₂ negative C c (cubicIdealGenerator x.1))
          V X d x.2 (b x)) ≤
      (M * H * K * Y ^ deltaLoss) * ∑ D ∈ F.powerset, ∑ r : QuadraticRayRing × QuadraticRayRing,
        (2 : ℝ) * ∫ t : ℝ, firstLogDensity J t * ∑ z ∈ T,
          ‖dilatedCoreRow p hg F D B v ε₁ ε₂ negative
            (if negative then r.1 else r.2) (normalizedColumn p C) V (columnLog p X) c d t z‖ ^ 2 := by
  obtain ⟨K, hK, hbound⟩ := first_ray_energy_integral deltaLoss hδ
  refine ⟨K, hK, ?_⟩
  intro ι _ p hp _ hinj hg hc F B v ε₁ ε₂ hv negative C V X c d s T w b J M H Y hM hH hmap hT hnorm hw hdom
  simp_rw [firstColumnEnergy_eq_sum_integrals p hp hinj hg F B v ε₁ ε₂ hv,
    Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_le_sum
  intro D hD
  rw [Finset.sum_comm]
  apply Finset.sum_le_sum
  intro r hr
  have h := hbound p hp hinj hg hc F D B v ε₁ ε₂ hv negative r
    (normalizedColumn p C) V (columnLog p X) c d s T w b J M H Y
    hM hH hmap hT hnorm hw hdom
  simpa only [mul_assoc, Finset.mul_sum] using h


def firstOutputEnergy {ι : Type*} [DecidableEq ι]
    (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hg : ∀ i, lambda ∉ Ideal.span {p i}) (F B : Finset ι)
    (v : ι → ℕ) (ε₁ ε₂ : ι → Bool) (negative : Bool)
    (C : Finset ι → ℂ) (V : ℝ → ℂ) (X : ℝ) (c d : O) (J : ℕ) (T : Finset O) : ℝ :=
  ∑ D ∈ F.powerset, ∑ r : QuadraticRayRing × QuadraticRayRing,
    (2 : ℝ) * ∫ t : ℝ, firstLogDensity J t * ∑ z ∈ T,
      ‖dilatedCoreRow p hg F D B v ε₁ ε₂ negative
        (if negative then r.1 else r.2) (normalizedColumn p C) V (columnLog p X) c d t z‖ ^ 2

theorem firstOutputEnergy_nonneg {ι : Type*} [DecidableEq ι]
    (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hg : ∀ i, lambda ∉ Ideal.span {p i}) (F B : Finset ι)
    (v : ι → ℕ) (ε₁ ε₂ : ι → Bool) (negative : Bool)
    (C : Finset ι → ℂ) (V : ℝ → ℂ) (X : ℝ) (c d : O) (J : ℕ) (T : Finset O) :
    0 ≤ firstOutputEnergy p hp hg F B v ε₁ ε₂ negative C V X c d J T := by
  apply Finset.sum_nonneg
  intro r hr
  apply Finset.sum_nonneg
  intro D hD
  apply mul_nonneg (by norm_num : (0 : ℝ) ≤ 2)
  apply integral_nonneg
  intro t
  exact mul_nonneg (firstLogDensity_nonneg J t) (Finset.sum_nonneg (fun _ _ => sq_nonneg _))


end FirstPassCubeLabels

namespace FirstPassCubeLabels
open Eisenstein SchwartzPlanePoisson SecondPassArithmetic MeasureTheory
open scoped Classical SchwartzMap

theorem first_passage_transfer
    (W : 𝓢(ℝ, ℂ)) (V₁ V₂ : ℝ → ℂ)
    (M₁ M₂ : ℝ) (hM₁ : 0 ≤ M₁) (hM₂ : 0 ≤ M₂)
    (hV₁ : ∀ x, V₁ x ≠ 0 → |x| ≤ M₁) (hV₂ : ∀ y, V₂ y ≠ 0 → |y| ≤ M₂)
    (J : ℕ) (deltaLoss : ℝ) (hδ : 0 < deltaLoss) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀
      {ι : Type*} [DecidableEq ι]
      (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
      (hinj : Function.Injective (fun i => Ideal.span {p i}))
      (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
      (hg : ∀ i, lambda ∉ Ideal.span {p i})
      (hc : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2)
      (hpr : ∀ i, lambda ^ 2 ∣ p i - 1) (F B : Finset ι) (hFB : Disjoint F B)
      (v : ι → ℕ) (ε₁ ε₂ : ι → Bool) (hv : ∀ j ∈ B, 0 < v j)
      (C₁ C₂ : Finset ι → ℂ) (X₁ X₂ : ℝ) (hX₁ : 0 < X₁) (hX₂ : 0 < X₂), ∀ lengthScale : ℝ, 0 < lengthScale → ∀ c d : O, d ≠ 0 →
      ∀ (s : Finset (Ideal O × O)) (T : Finset O) (w : Ideal O × O → ℂ) (M Y : ℝ),
      0 ≤ M → 0 ≤ Y → (∀ x ∈ s, x.2 ≠ 0) →
      (∀ x ∈ s, DescentWeightedCauchy.firstElementRowMap (dilationLabel p B v ε₁ ε₂) x ∈ T) →
      (∀ z ∈ T, z ≠ 0) → (∀ z ∈ T, (Ideal.absNorm (Ideal.span {z}) : ℝ) ≤ Y) →
      (∀ x ∈ s, ‖w x‖ ≤ M) →
      ‖∑ x ∈ s, w x * actualFirstKernel p hp hg F B v ε₁ ε₂
        (originalLabelColumn p hg B ε₁ ε₂ true C₁ c (cubicIdealGenerator x.1))
        (originalLabelColumn p hg B ε₁ ε₂ false C₂ c (cubicIdealGenerator x.1))
        W V₁ V₂ X₁ X₂ lengthScale d x.2‖ ≤
      (lengthScale / ‖ringComplex (∏ i ∈ cubeActiveSupport B v ε₁ ε₂, p i)‖) * (M * K * Y ^ deltaLoss) *
        Real.sqrt (firstOutputEnergy p hp hg F B v ε₁ ε₂ true C₁ V₁ X₁ c d J T) *
        Real.sqrt (firstOutputEnergy p hp hg F B v ε₁ ε₂ false C₂ V₂ X₂ c d J T) := by
  obtain ⟨H, hH, hsep⟩ := actual_first_kernel_uniform_energy_envelope
    W V₁ V₂ M₁ M₂ hM₁ hM₂ hV₁ hV₂ 0 J
  obtain ⟨K, hK, hpush⟩ := first_column_energy_integral deltaLoss hδ
  refine ⟨H * K, mul_nonneg hH hK.le, ?_⟩
  intro ι _ p hp _ hinj hcop hg hc hpr F B hFB v ε₁ ε₂ hv C₁ C₂ X₁ X₂ hX₁ hX₂
  have hsep := hsep p hp hinj hcop hg hc hpr F B hFB v ε₁ ε₂ X₁ X₂ hX₁ hX₂
  intro lengthScale hL c d hd s T w M Y hM hY hnonzero hmap hT hnorm hw
  let A₁ := fun x : Ideal O × O => originalLabelColumn p hg B ε₁ ε₂ true C₁ c (cubicIdealGenerator x.1)
  let A₂ := fun x : Ideal O × O => originalLabelColumn p hg B ε₁ ε₂ false C₂ c (cubicIdealGenerator x.1)
  let q := lengthScale / ‖ringComplex (∏ i ∈ cubeActiveSupport B v ε₁ ε₂, p i)‖
  have hq : 0 ≤ q := div_nonneg hL.le (norm_nonneg _)
  have hfam : ∀ x : Ideal O × O, ∃ b : 𝓢(ℝ, ℂ), x ∈ s →
      (∀ t : ℝ, ‖b t‖ ≤ H * firstLogDensity J t) ∧
      ‖actualFirstKernel p hp hg F B v ε₁ ε₂ (A₁ x) (A₂ x) W V₁ V₂ X₁ X₂ lengthScale d x.2‖ ≤
        q * Real.sqrt (firstColumnEnergy p hp hg F B v ε₁ ε₂ true (A₁ x) V₁ X₁ d x.2 b) *
          Real.sqrt (firstColumnEnergy p hp hg F B v ε₁ ε₂ false (A₂ x) V₂ X₂ d x.2 b) := by
    intro x
    by_cases hx : x ∈ s
    · obtain ⟨b, hb, hk⟩ := hsep lengthScale hL d x.2 hd (hnonzero x hx)
      refine ⟨b, fun _ => ⟨?_, hk (A₁ x) (A₂ x)⟩⟩
      simpa only [pow_zero, one_mul] using hb
    · exact ⟨0, fun hx' => (hx hx').elim⟩
  choose b hb using hfam
  let E₁ := fun x => firstColumnEnergy p hp hg F B v ε₁ ε₂ true (A₁ x) V₁ X₁ d x.2 (b x)
  let E₂ := fun x => firstColumnEnergy p hp hg F B v ε₁ ε₂ false (A₂ x) V₂ X₂ d x.2 (b x)
  let O₁ := firstOutputEnergy p hp hg F B v ε₁ ε₂ true C₁ V₁ X₁ c d J T
  let O₂ := firstOutputEnergy p hp hg F B v ε₁ ε₂ false C₂ V₂ X₂ c d J T
  let P := M * H * K * Y ^ deltaLoss
  have hP : 0 ≤ P := mul_nonneg (mul_nonneg (mul_nonneg hM hH) hK.le) (Real.rpow_nonneg hY deltaLoss)
  have hE₁ (x) : 0 ≤ E₁ x := firstColumnEnergy_nonneg p hp hg F B v ε₁ ε₂ true _ _ _ _ _ _
  have hE₂ (x) : 0 ≤ E₂ x := firstColumnEnergy_nonneg p hp hg F B v ε₁ ε₂ false _ _ _ _ _ _
  have hdom : ∀ x ∈ s, ∀ t : ℝ, ‖b x t‖ ≤ H * firstLogDensity J t := fun x hx => (hb x hx).1
  have hsum₁ : (∑ x ∈ s, ‖w x‖ * E₁ x) ≤ P * O₁ :=
    hpush p hp hinj hg hc F B v ε₁ ε₂ hv true C₁ V₁ X₁ c d s T w b J M H Y
      hM hH hmap hT hnorm hw hdom
  have hsum₂ : (∑ x ∈ s, ‖w x‖ * E₂ x) ≤ P * O₂ :=
    hpush p hp hinj hg hc F B v ε₁ ε₂ hv false C₂ V₂ X₂ c d s T w b J M H Y
      hM hH hmap hT hnorm hw hdom
  have hterm (x) : ‖w x‖ * (Real.sqrt (E₁ x) * Real.sqrt (E₂ x)) =
      Real.sqrt (‖w x‖ * E₁ x) * Real.sqrt (‖w x‖ * E₂ x) := by
    rw [Real.sqrt_mul (norm_nonneg _), Real.sqrt_mul (norm_nonneg _)]
    calc
      _ = (Real.sqrt ‖w x‖) ^ 2 * (Real.sqrt (E₁ x) * Real.sqrt (E₂ x)) := by
        rw [Real.sq_sqrt (norm_nonneg _)]
      _ = _ := by ring
  calc
    _ ≤ ∑ x ∈ s, ‖w x * actualFirstKernel p hp hg F B v ε₁ ε₂
        (A₁ x) (A₂ x) W V₁ V₂ X₁ X₂ lengthScale d x.2‖ := norm_sum_le _ _
    _ ≤ ∑ x ∈ s, q * (Real.sqrt (‖w x‖ * E₁ x) * Real.sqrt (‖w x‖ * E₂ x)) := by
      apply Finset.sum_le_sum
      intro x hx
      rw [norm_mul, ← hterm]
      calc
        _ ≤ ‖w x‖ * (q * Real.sqrt (E₁ x) * Real.sqrt (E₂ x)) :=
          mul_le_mul_of_nonneg_left (hb x hx).2 (norm_nonneg _)
        _ = _ := by ring
    _ = q * (∑ x ∈ s, Real.sqrt (‖w x‖ * E₁ x) * Real.sqrt (‖w x‖ * E₂ x)) :=
      (Finset.mul_sum _ _ _).symm
    _ ≤ q * (Real.sqrt (∑ x ∈ s, ‖w x‖ * E₁ x) * Real.sqrt (∑ x ∈ s, ‖w x‖ * E₂ x)) :=
      mul_le_mul_of_nonneg_left (Real.sum_sqrt_mul_sqrt_le s
        (fun x => mul_nonneg (norm_nonneg _) (hE₁ x))
        (fun x => mul_nonneg (norm_nonneg _) (hE₂ x))) hq
    _ ≤ q * (Real.sqrt (P * O₁) * Real.sqrt (P * O₂)) := by
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul (Real.sqrt_le_sqrt hsum₁) (Real.sqrt_le_sqrt hsum₂)
          (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)) hq
    _ = _ := by
      rw [Real.sqrt_mul hP, Real.sqrt_mul hP]
      calc
        _ = q * (Real.sqrt P)^2 * Real.sqrt O₁ * Real.sqrt O₂ := by ring
        _ = _ := by rw [Real.sq_sqrt hP]; dsimp only [P]; ring

end FirstPassCubeLabels

namespace FirstPassCubeLabels
open Eisenstein SchwartzPlanePoisson SecondPassArithmetic MeasureTheory
open scoped Classical SchwartzMap

variable {ι : Type*} [DecidableEq ι] (p : ι → O)
  [∀ i, (Ideal.span {p i}).IsMaximal]
  (hp : ∀ i, p i ≠ 0) (hg : ∀ i, lambda ∉ Ideal.span {p i})

def dilatedCoreTest (D B : Finset ι) (v : ι → ℕ) (ε₁ ε₂ : ι → Bool)
    (negative : Bool) (r : QuadraticRayRing) (C : Finset ι → ℂ)
    (V : ℝ → ℂ) (y : Finset ι → ℝ) (t : ℝ) : Finset ι → ℂ :=
  firstResidueMask p r (fun U => cubeCoreCoefficient p hg B v ε₁ ε₂ negative C V y t (D ∪ U))

theorem dilatedCoreRow_eq_input (F D B : Finset ι) (v : ι → ℕ) (ε₁ ε₂ : ι → Bool)
    (negative : Bool) (r : QuadraticRayRing) (C : Finset ι → ℂ)
    (V : ℝ → ℂ) (y : Finset ι → ℝ) (c d : O) (t : ℝ) (z : O) :
    dilatedCoreRow p hg F D B v ε₁ ε₂ negative r C V y c d t z =
      inputConjugateRow p (fun i => complexSexticChar (Ideal.span {p i}) (hg i)) (F \ D)
        (1 : O →* ℂ) (b0Label p B v ε₁ ε₂) (c * jLabel p B v ε₁ ε₂) d
        (dilatedCoreTest p hg D B v ε₁ ε₂ negative r C V y t) z :=
  dilatedResidueColumn_eq_inputRow p hg F D r _ p B v ε₁ ε₂ c d z

/-- The first-pass energy enters the second Poisson formula with the same cube labels. -/
theorem dilatedCoreRow_second_frequency_expansion
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (F D B : Finset ι) (v : ι → ℕ) (ε₁ ε₂ : ι → Bool)
    (negative : Bool) (r : QuadraticRayRing) (C : Finset ι → ℂ)
    (V : ℝ → ℂ) (y : Finset ι → ℝ) (c d : O) (t : ℝ)
    (W : 𝓢(ℝ, ℂ)) (Y : ℝ) (hY : 0 < Y) :
    (∑' z : O, W (‖ringComplex z‖ ^ 2 / Y) *
      (‖dilatedCoreRow p hg F D B v ε₁ ε₂ negative r C V y c d t z‖ ^ 2 : ℝ)) =
      ∑ G ∈ (F \ D).powerset,
        (‖secondInputCoefficient p (fun i => complexSexticChar (Ideal.span {p i}) (hg i))
          (1 : O →* ℂ) (b0Label p B v ε₁ ε₂) (c * jLabel p B v ε₁ ε₂) d (fun _ => 1) G‖ ^ 2 : ℝ) *
        ∑ E ∈ G.powerset, (supportMobius E / (‖ringComplex (∏ i ∈ E, p i)‖ ^ 2 : ℝ)) *
          ∑' k : O, secondFrequencyKernel p hp hg (F \ D) (1 : O →* ℂ) (1 : O →* ℂ)
            (b0Label p B v ε₁ ε₂) (∏ i ∈ G \ E, p i) (c * jLabel p B v ε₁ ε₂) d
            (∏ i ∈ E, p i) k
            (fun U => dilatedCoreTest p hg D B v ε₁ ε₂ negative r C V y t (G ∪ U))
            (fun U => dilatedCoreTest p hg D B v ε₁ ε₂ negative r C V y t (G ∪ U)) W Y := by
  simp_rw [dilatedCoreRow_eq_input]
  exact inputConjugateRow_second_frequency_expansion p hp hg hinj (F \ D)
    (1 : O →* ℂ) (b0Label p B v ε₁ ε₂) (c * jLabel p B v ε₁ ε₂) d
    (dilatedCoreTest p hg D B v ε₁ ε₂ negative r C V y t) W Y hY

end FirstPassCubeLabels

namespace FirstPassCubeLabels
open Eisenstein SchwartzPlanePoisson SecondPassArithmetic
open scoped Classical

variable {ι : Type*} [DecidableEq ι] (p : ι → O)
  [∀ i, (Ideal.span {p i}).IsMaximal]
  (hg : ∀ i, lambda ∉ Ideal.span {p i})

/-- Fixed residue columns contain all primewise phases; cube data occur only in outer factors. -/
def firstFixedColumn (negative : Bool) (r : QuadraticRayRing)
    (H : Finset ι → ℂ) (U : Finset ι) : ℂ :=
  firstResidueMask p r (fun U =>
    star (primeSubsetRow p (fun i => complexSexticChar (Ideal.span {p i}) (hg i)) U 4) *
      (if negative then star (primeSubsetRow p (fun i => complexSexticChar (Ideal.span {p i}) (hg i)) U (-1)) else 1) * H U) U

def firstCoreOuter (B : Finset ι) (v : ι → ℕ) (ε₁ ε₂ : ι → Bool)
    (negative : Bool) (D : Finset ι) (r : QuadraticRayRing) : ℂ :=
  let a := Ideal.Quotient.mk (Ideal.span {(4 : O)}) (∏ i ∈ D, p i) * r
  let b := Ideal.Quotient.mk (Ideal.span {(4 : O)}) (∏ i ∈ cubeOddSupport B v ε₁ ε₂, p i)
  (if negative then star (rayQuadraticPair a b) else rayQuadraticPair a b) *
    (star (primeSubsetRow p (fun i => complexSexticChar (Ideal.span {p i}) (hg i)) D 4) /
      star (rayQuadraticPhase a)) *
    (if negative then star (primeSubsetRow p (fun i => complexSexticChar (Ideal.span {p i}) (hg i)) D (-1)) else 1)

def firstCoreTest (C : Finset ι → ℂ) (V : ℝ → ℂ) (y : Finset ι → ℝ)
    (negative : Bool) (t : ℝ) (D U : Finset ι) : ℂ :=
  C (D ∪ U) * (if negative then star (V (y (D ∪ U)) * kernelLogPhase t (-(y (D ∪ U))))
    else V (y (D ∪ U)) * kernelLogPhase t (-(y (D ∪ U))))

theorem cubeCoreCoefficient_residue (D U B : Finset ι) (hDU : Disjoint D U)
    (v : ι → ℕ) (ε₁ ε₂ : ι → Bool) (negative : Bool) (r : QuadraticRayRing)
    (C : Finset ι → ℂ) (V : ℝ → ℂ) (y : Finset ι → ℝ) (t : ℝ) :
    dilatedCoreTest p hg D B v ε₁ ε₂ negative r C V y t U =
      firstCoreOuter p hg B v ε₁ ε₂ negative D r *
        firstFixedColumn p hg negative r (firstCoreTest C V y negative t D) U := by
  unfold dilatedCoreTest firstFixedColumn firstResidueMask
  by_cases hr : Ideal.Quotient.mk (Ideal.span {(4 : O)}) (∏ i ∈ U, p i) = r
  · simp only [if_pos hr]
    cases negative <;>
      simp only [cubeCoreCoefficient, firstCoreOuter, firstCoreTest, firstColumnPhase,
        subsetTraceRayFactor_eq_row, fixedRayExpansion, Finset.prod_union hDU, map_mul,
        primeSubsetRow_union p _ D U hDU, hr, Bool.false_eq_true, ite_false, ite_true,
        star_mul, star_inv₀, div_eq_mul_inv] <;> ring
  · simp only [if_neg hr, mul_zero]

theorem firstFixedColumn_norm_le (negative : Bool) (r : QuadraticRayRing)
    (H : Finset ι → ℂ) (U : Finset ι) :
    ‖firstFixedColumn p hg negative r H U‖ ≤ ‖H U‖ := by
  unfold firstFixedColumn firstResidueMask
  by_cases hr : Ideal.Quotient.mk (Ideal.span {(4 : O)}) (∏ i ∈ U, p i) = r
  · simp only [if_pos hr]
    rw [norm_mul, norm_mul, norm_star]
    have h4 := primeSubsetRow_norm_le_one p (fun i => complexSexticChar (Ideal.span {p i}) (hg i)) U 4
    have hm : ‖(if negative then star (primeSubsetRow p (fun i => complexSexticChar (Ideal.span {p i}) (hg i)) U (-1)) else 1)‖ ≤ 1 := by
      cases negative
      · simp
      · simpa only [ite_true, norm_star] using
          primeSubsetRow_norm_le_one p (fun i => complexSexticChar (Ideal.span {p i}) (hg i)) U (-1)
    exact mul_le_of_le_one_left (norm_nonneg _)
      ((mul_le_mul h4 hm (norm_nonneg _) zero_le_one).trans_eq (one_mul 1))
  · simp only [if_neg hr, norm_zero]
    exact norm_nonneg _

theorem firstCoreOuter_norm_le (B : Finset ι) (v : ι → ℕ) (ε₁ ε₂ : ι → Bool)
    (negative : Bool) (D : Finset ι) (r : QuadraticRayRing) :
    ‖firstCoreOuter p hg B v ε₁ ε₂ negative D r‖ ≤ 2 := by
  let a := Ideal.Quotient.mk (Ideal.span {(4 : O)}) (∏ i ∈ D, p i) * r
  let b := Ideal.Quotient.mk (Ideal.span {(4 : O)}) (∏ i ∈ cubeOddSupport B v ε₁ ε₂, p i)
  have hphase : ‖(star (rayQuadraticPhase a))⁻¹‖ ≤ 1 := by
    simpa only [norm_inv, norm_star, rayQuadraticPhase] using
      (fixedDualAverage_bounds (QuadraticPhase.Eisenstein.GaussianShiftedPartition.representative 4 a)).2
  have h4 := primeSubsetRow_norm_le_one p (fun i => complexSexticChar (Ideal.span {p i}) (hg i)) D 4
  have hm := primeSubsetRow_norm_le_one p (fun i => complexSexticChar (Ideal.span {p i}) (hg i)) D (-1)
  have hab := rayQuadraticPair_norm a b
  cases negative <;> simp only [firstCoreOuter, Bool.false_eq_true, ite_false, ite_true,
    div_eq_mul_inv, norm_mul, norm_star, norm_one, mul_one]
  · exact (mul_le_mul hab ((mul_le_mul h4 hphase (norm_nonneg _) zero_le_one).trans_eq (one_mul 1))
      (by positivity) (by norm_num)).trans_eq (mul_one 2)
  · exact (mul_le_mul
      ((mul_le_mul hab ((mul_le_mul h4 hphase (norm_nonneg _) zero_le_one).trans_eq (one_mul 1))
        (by positivity) (by norm_num)).trans_eq (mul_one 2)) hm
      (norm_nonneg _) (by norm_num)).trans_eq (mul_one 2)

/-- A fixed residue turns cube-dependent phases into a scalar outside the second input row. -/
theorem dilatedCoreRow_eq_fixed_input (F D B : Finset ι) (v : ι → ℕ) (ε₁ ε₂ : ι → Bool)
    (negative : Bool) (r : QuadraticRayRing) (C : Finset ι → ℂ)
    (V : ℝ → ℂ) (y : Finset ι → ℝ) (c d : O) (t : ℝ) (z : O) :
    dilatedCoreRow p hg F D B v ε₁ ε₂ negative r C V y c d t z =
      firstCoreOuter p hg B v ε₁ ε₂ negative D r *
        inputConjugateRow p (fun i => complexSexticChar (Ideal.span {p i}) (hg i)) (F \ D)
          (1 : O →* ℂ) (b0Label p B v ε₁ ε₂) (c * jLabel p B v ε₁ ε₂) d
          (firstFixedColumn p hg negative r (firstCoreTest C V y negative t D)) z := by
  rw [dilatedCoreRow_eq_input]
  unfold inputConjugateRow supportConjugateSum
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro U hU
  unfold secondInputCoefficient
  rw [cubeCoreCoefficient_residue p hg D U B
    (Finset.disjoint_of_subset_right (Finset.mem_powerset.mp hU) disjoint_sdiff_self_right)]
  ring

end FirstPassCubeLabels

namespace FirstPassCubeLabels
open Eisenstein SchwartzPlanePoisson SecondPassArithmetic MeasureTheory
open scoped Classical SchwartzMap

variable {ι : Type*} [DecidableEq ι] (p : ι → O)
  [∀ i, (Ideal.span {p i}).IsMaximal]
  (hg : ∀ i, lambda ∉ Ideal.span {p i})

def multiplicativeCoreColumn (Ψ : O →* ℂ) (m : O) (H : Finset ι → ℂ) (S : Finset ι) : ℂ :=
  Ψ (∏ i ∈ S, p i) * primeCoprimeMask p S m * H S

include hg in
theorem firstCoreTest_multiplicative (Ψ : O →* ℂ) (m : O) (H : Finset ι → ℂ)
    (V : ℝ → ℂ) (y : Finset ι → ℝ) (negative : Bool) (t : ℝ)
    (D U : Finset ι) (hDU : Disjoint D U) :
    firstCoreTest (multiplicativeCoreColumn p Ψ m H) V y negative t D U =
      (Ψ (∏ i ∈ D, p i) * primeCoprimeMask p D m) *
        (Ψ (∏ i ∈ U, p i) * primeCoprimeMask p U m * firstCoreTest H V y negative t D U) := by
  simp only [firstCoreTest, multiplicativeCoreColumn, Finset.prod_union hDU, map_mul,
    mask_union p hg D U hDU]
  ring

def firstCoreInputRow (F D B : Finset ι) (v : ι → ℕ) (ε₁ ε₂ : ι → Bool)
    (negative : Bool) (r : QuadraticRayRing) (Ψ : O →* ℂ) (m : O)
    (H : Finset ι → ℂ) (V : ℝ → ℂ) (y : Finset ι → ℝ)
    (c d : O) (t : ℝ) (z : O) : ℂ :=
  inputConjugateRow p (fun i => complexSexticChar (Ideal.span {p i}) (hg i)) (F \ D)
    Ψ (m * b0Label p B v ε₁ ε₂) (c * jLabel p B v ε₁ ε₂) d
    (firstFixedColumn p hg negative r (firstCoreTest H V y negative t D)) z

theorem dilatedCoreRow_multiplicative (F D B : Finset ι) (v : ι → ℕ) (ε₁ ε₂ : ι → Bool)
    (negative : Bool) (r : QuadraticRayRing) (Ψ : O →* ℂ) (m : O)
    (H : Finset ι → ℂ) (V : ℝ → ℂ) (y : Finset ι → ℝ)
    (c d : O) (t : ℝ) (z : O) :
    dilatedCoreRow p hg F D B v ε₁ ε₂ negative r
      (multiplicativeCoreColumn p Ψ m H) V y c d t z =
      (firstCoreOuter p hg B v ε₁ ε₂ negative D r *
        (Ψ (∏ i ∈ D, p i) * primeCoprimeMask p D m)) *
        firstCoreInputRow p hg F D B v ε₁ ε₂ negative r Ψ m H V y c d t z := by
  rw [dilatedCoreRow_eq_fixed_input, mul_assoc]
  apply congrArg (fun x : ℂ => firstCoreOuter p hg B v ε₁ ε₂ negative D r * x)
  unfold firstCoreInputRow inputConjugateRow supportConjugateSum
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro U hU
  have hDU : Disjoint D U := Finset.disjoint_of_subset_right
    (Finset.mem_powerset.mp hU) disjoint_sdiff_self_right
  unfold secondInputCoefficient firstFixedColumn firstResidueMask
  rw [mask_mul p hg U]
  by_cases hr : Ideal.Quotient.mk (Ideal.span {(4 : O)}) (∏ i ∈ U, p i) = r
  · simp only [if_pos hr]
    rw [firstCoreTest_multiplicative p hg Ψ m H V y negative t D U hDU]
    simp only [MonoidHom.one_apply]
    ring
  · simp only [if_neg hr, mul_zero, zero_mul]

theorem firstCoreTest_continuous (H : Finset ι → ℂ) (V : ℝ → ℂ) (y : Finset ι → ℝ)
    (negative : Bool) (D U : Finset ι) :
    Continuous (fun t => firstCoreTest H V y negative t D U) := by
  have ht := kernelLogPhase_continuous_left (-(y (D ∪ U)))
  cases negative <;> simp only [firstCoreTest, Bool.false_eq_true, ite_false, ite_true] <;> fun_prop

theorem firstCoreTest_norm_time (H : Finset ι → ℂ) (V : ℝ → ℂ) (y : Finset ι → ℝ)
    (negative : Bool) (D U : Finset ι) (t : ℝ) :
    ‖firstCoreTest H V y negative t D U‖ = ‖firstCoreTest H V y negative 0 D U‖ := by
  cases negative <;> simp only [firstCoreTest, Bool.false_eq_true, ite_false, ite_true,
    norm_mul, norm_star, kernelLogPhase_norm]

theorem firstCoreInputRow_continuous (F D B : Finset ι) (v : ι → ℕ) (ε₁ ε₂ : ι → Bool)
    (negative : Bool) (r : QuadraticRayRing) (Ψ : O →* ℂ) (m : O)
    (H : Finset ι → ℂ) (V : ℝ → ℂ) (y : Finset ι → ℝ) (c d z : O) :
    Continuous (fun t => firstCoreInputRow p hg F D B v ε₁ ε₂ negative r Ψ m H V y c d t z) := by
  unfold firstCoreInputRow inputConjugateRow supportConjugateSum secondInputCoefficient
  apply continuous_finsetSum
  intro U _
  unfold firstFixedColumn firstResidueMask
  have ht := firstCoreTest_continuous H V y negative D U
  split_ifs <;> fun_prop

theorem firstCoreInputRow_uniform_bound (F D B : Finset ι) (v : ι → ℕ) (ε₁ ε₂ : ι → Bool)
    (negative : Bool) (r : QuadraticRayRing) (Ψ : O →* ℂ) (m : O)
    (H : Finset ι → ℂ) (V : ℝ → ℂ) (y : Finset ι → ℝ) (c d z : O) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ t,
      ‖firstCoreInputRow p hg F D B v ε₁ ε₂ negative r Ψ m H V y c d t z‖ ≤ M := by
  let q := fun (t : ℝ) (U : Finset ι) => supportMobius U *
    secondInputCoefficient p (fun i => complexSexticChar (Ideal.span {p i}) (hg i))
      Ψ (m * b0Label p B v ε₁ ε₂) (c * jLabel p B v ε₁ ε₂) d
      (firstFixedColumn p hg negative r (firstCoreTest H V y negative t D)) U *
      star (primeSubsetRow p (fun i => complexSexticChar (Ideal.span {p i}) (hg i)) U z)
  refine ⟨∑ U ∈ (F \ D).powerset, ‖q 0 U‖, by positivity, ?_⟩
  intro t
  change ‖∑ U ∈ (F \ D).powerset, q t U‖ ≤ _
  apply (norm_sum_le _ _).trans_eq
  apply Finset.sum_congr rfl
  intro U _
  dsimp only [q, secondInputCoefficient, firstFixedColumn, firstResidueMask]
  split_ifs <;> simp only [norm_mul, firstCoreTest_norm_time]

theorem firstCoreInputRow_integrable (F D B : Finset ι) (v : ι → ℕ) (ε₁ ε₂ : ι → Bool)
    (negative : Bool) (r : QuadraticRayRing) (Ψ : O →* ℂ) (m : O)
    (H : Finset ι → ℂ) (V : ℝ → ℂ) (y : Finset ι → ℝ) (c d z : O)
    {k : ℝ → ℝ} (hk : Integrable k volume) :
    Integrable (fun t => k t *
      ‖firstCoreInputRow p hg F D B v ε₁ ε₂ negative r Ψ m H V y c d t z‖ ^ 2) volume := by
  obtain ⟨M, hM, hb⟩ := firstCoreInputRow_uniform_bound p hg F D B v ε₁ ε₂ negative r Ψ m H V y c d z
  apply hk.mul_bdd (c := M ^ 2)
  · exact ((firstCoreInputRow_continuous p hg F D B v ε₁ ε₂ negative r Ψ m H V y c d z).norm.pow 2).aestronglyMeasurable
  · exact Filter.Eventually.of_forall (fun t => by
      rw [Real.norm_of_nonneg (sq_nonneg _)]
      exact pow_le_pow_left₀ (norm_nonneg _) (hb t) 2)

end FirstPassCubeLabels

namespace FirstPassCubeLabels
open Eisenstein SchwartzPlanePoisson SecondPassArithmetic MeasureTheory
open scoped Classical SchwartzMap

variable {ι : Type*} [DecidableEq ι] (p : ι → O)
  [∀ i, (Ideal.span {p i}).IsMaximal]
  (hg : ∀ i, lambda ∉ Ideal.span {p i})

theorem dilatedCoreRow_sq_le_input (F D B : Finset ι) (v : ι → ℕ) (ε₁ ε₂ : ι → Bool)
    (negative : Bool) (r : QuadraticRayRing) (Ψ : O →* ℂ) (m : O)
    (H : Finset ι → ℂ) (V : ℝ → ℂ) (y : Finset ι → ℝ) (c d : O) (t : ℝ) (z : O)
    (hΨ : ‖Ψ (∏ i ∈ D, p i)‖ ≤ 1) :
    ‖dilatedCoreRow p hg F D B v ε₁ ε₂ negative r
      (multiplicativeCoreColumn p Ψ m H) V y c d t z‖ ^ 2 ≤
      4 * ‖firstCoreInputRow p hg F D B v ε₁ ε₂ negative r Ψ m H V y c d t z‖ ^ 2 := by
  rw [dilatedCoreRow_multiplicative, norm_mul, mul_pow]
  apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
  have hb : ‖firstCoreOuter p hg B v ε₁ ε₂ negative D r *
      (Ψ (∏ i ∈ D, p i) * primeCoprimeMask p D m)‖ ≤ 2 := by
    rw [norm_mul, norm_mul]
    exact (mul_le_mul (firstCoreOuter_norm_le p hg B v ε₁ ε₂ negative D r)
      ((mul_le_mul hΨ (primeCoprimeMask_norm_le_one p D m) (norm_nonneg _) zero_le_one).trans_eq (one_mul 1))
      (by positivity) (by norm_num)).trans_eq (mul_one 2)
  calc
    _ ≤ (2 : ℝ) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hb 2
    _ = 4 := by norm_num

/-- Fixed residue phases cost at most four in the squared first-pass energy. -/
theorem dilatedCoreRow_energy_le_input (F D B : Finset ι) (v : ι → ℕ) (ε₁ ε₂ : ι → Bool)
    (negative : Bool) (r : QuadraticRayRing) (Ψ : O →* ℂ) (m : O)
    (H : Finset ι → ℂ) (V : ℝ → ℂ) (y : Finset ι → ℝ) (c d : O)
    (T : Finset O) (k : ℝ → ℝ) (hk : Integrable k volume) (hk0 : ∀ t, 0 ≤ k t)
    (hΨ : ‖Ψ (∏ i ∈ D, p i)‖ ≤ 1) :
    (∫ t : ℝ, k t * ∑ z ∈ T,
      ‖dilatedCoreRow p hg F D B v ε₁ ε₂ negative r
        (multiplicativeCoreColumn p Ψ m H) V y c d t z‖ ^ 2) ≤
      4 * ∫ t : ℝ, k t * ∑ z ∈ T,
        ‖firstCoreInputRow p hg F D B v ε₁ ε₂ negative r Ψ m H V y c d t z‖ ^ 2 := by
  have iP : Integrable (fun t => k t * ∑ z ∈ T,
      ‖dilatedCoreRow p hg F D B v ε₁ ε₂ negative r
        (multiplicativeCoreColumn p Ψ m H) V y c d t z‖ ^ 2) volume := by
    simp only [Finset.mul_sum]
    exact integrable_finsetSum _ (fun z _ => dilatedCoreRow_integrable p hg F D B v ε₁ ε₂
      negative r (multiplicativeCoreColumn p Ψ m H) V y c d z hk)
  have iQ : Integrable (fun t => k t * ∑ z ∈ T,
      ‖firstCoreInputRow p hg F D B v ε₁ ε₂ negative r Ψ m H V y c d t z‖ ^ 2) volume := by
    simp only [Finset.mul_sum]
    exact integrable_finsetSum _ (fun z _ => firstCoreInputRow_integrable p hg F D B v ε₁ ε₂
      negative r Ψ m H V y c d z hk)
  rw [← integral_const_mul]
  apply integral_mono iP (iQ.const_mul 4)
  intro t
  dsimp only
  rw [← mul_assoc, mul_comm 4 (k t), mul_assoc]
  apply mul_le_mul_of_nonneg_left _ (hk0 t)
  rw [Finset.mul_sum]
  exact Finset.sum_le_sum (fun z _ => dilatedCoreRow_sq_le_input p hg F D B v ε₁ ε₂
    negative r Ψ m H V y c d t z hΨ)

end FirstPassCubeLabels

namespace FirstPassCubeLabels
open Eisenstein SchwartzPlanePoisson SecondPassArithmetic MeasureTheory
open scoped Classical SchwartzMap

variable {ι : Type*} [DecidableEq ι] (p : ι → O)
  [∀ i, (Ideal.span {p i}).IsMaximal]
  (hp : ∀ i, p i ≠ 0) (hg : ∀ i, lambda ∉ Ideal.span {p i})

theorem normalized_multiplicativeCoreColumn (Ψ : O →* ℂ) (m : O) (H : Finset ι → ℂ) :
    normalizedColumn p (multiplicativeCoreColumn p Ψ m H) =
      multiplicativeCoreColumn p Ψ m (normalizedColumn p H) := by
  funext S
  simp only [normalizedColumn, multiplicativeCoreColumn, div_eq_mul_inv]
  ring

def firstInputFamilyEnergy (F B : Finset ι) (v : ι → ℕ) (ε₁ ε₂ : ι → Bool)
    (negative : Bool) (Ψ : O →* ℂ) (m : O) (H : Finset ι → ℂ)
    (V : ℝ → ℂ) (X : ℝ) (c d : O) (J : ℕ) (T : Finset O) : ℝ :=
  ∑ D ∈ F.powerset, ∑ r : QuadraticRayRing × QuadraticRayRing,
    (2 : ℝ) * ∫ t : ℝ, firstLogDensity J t * ∑ z ∈ T,
      ‖firstCoreInputRow p hg F D B v ε₁ ε₂ negative (if negative then r.1 else r.2)
        Ψ m (normalizedColumn p H) V (columnLog p X) c d t z‖ ^ 2

theorem firstInputFamilyEnergy_nonneg (F B : Finset ι) (v : ι → ℕ) (ε₁ ε₂ : ι → Bool)
    (negative : Bool) (Ψ : O →* ℂ) (m : O) (H : Finset ι → ℂ)
    (V : ℝ → ℂ) (X : ℝ) (c d : O) (J : ℕ) (T : Finset O) :
    0 ≤ firstInputFamilyEnergy p hg F B v ε₁ ε₂ negative Ψ m H V X c d J T := by
  apply Finset.sum_nonneg
  intro D _
  apply Finset.sum_nonneg
  intro r _
  apply mul_nonneg (by norm_num : (0 : ℝ) ≤ 2)
  apply integral_nonneg
  intro t
  exact mul_nonneg (firstLogDensity_nonneg J t) (Finset.sum_nonneg (fun z _ => sq_nonneg _))

theorem firstOutputEnergy_le_input_family (F B : Finset ι) (v : ι → ℕ) (ε₁ ε₂ : ι → Bool)
    (negative : Bool) (Ψ : O →* ℂ) (m : O) (H : Finset ι → ℂ)
    (V : ℝ → ℂ) (X : ℝ) (c d : O) (J : ℕ) (T : Finset O)
    (hΨ : ∀ D ∈ F.powerset, ‖Ψ (∏ i ∈ D, p i)‖ ≤ 1) :
    firstOutputEnergy p hp hg F B v ε₁ ε₂ negative (multiplicativeCoreColumn p Ψ m H) V X c d J T ≤
      4 * firstInputFamilyEnergy p hg F B v ε₁ ε₂ negative Ψ m H V X c d J T := by
  unfold firstOutputEnergy firstInputFamilyEnergy
  rw [normalized_multiplicativeCoreColumn]
  simp only [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro D hD
  apply Finset.sum_le_sum
  intro r _
  have h := mul_le_mul_of_nonneg_left
    (dilatedCoreRow_energy_le_input p hg F D B v ε₁ ε₂ negative
      (if negative then r.1 else r.2) Ψ m (normalizedColumn p H) V (columnLog p X) c d T
      (firstLogDensity J) (firstLogDensity_integrable J) (firstLogDensity_nonneg J) (hΨ D hD))
    (by norm_num : (0 : ℝ) ≤ 2)
  simpa only [Finset.mul_sum, mul_assoc, mul_left_comm, mul_comm] using h

/-- The complete first passage ends in fixed-residue second-input families. -/
theorem first_passage_to_input_family
    (W : 𝓢(ℝ, ℂ)) (V₁ V₂ : ℝ → ℂ)
    (M₁ M₂ : ℝ) (hM₁ : 0 ≤ M₁) (hM₂ : 0 ≤ M₂)
    (hV₁ : ∀ x, V₁ x ≠ 0 → |x| ≤ M₁) (hV₂ : ∀ y, V₂ y ≠ 0 → |y| ≤ M₂)
    (J : ℕ) (δ : ℝ) (hδ : 0 < δ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀
      {ι : Type*} [DecidableEq ι]
      (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
      (hinj : Function.Injective (fun i => Ideal.span {p i}))
      (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
      (hg : ∀ i, lambda ∉ Ideal.span {p i})
      (hc : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2)
      (hpr : ∀ i, lambda ^ 2 ∣ p i - 1) (F B : Finset ι) (hFB : Disjoint F B)
      (v : ι → ℕ) (ε₁ ε₂ : ι → Bool) (hv : ∀ j ∈ B, 0 < v j)
      (Ψ₁ Ψ₂ : O →* ℂ) (m₁ m₂ : O) (H₁ H₂ : Finset ι → ℂ)
      (hΨ₁ : ∀ D ∈ F.powerset, ‖Ψ₁ (∏ i ∈ D, p i)‖ ≤ 1)
      (hΨ₂ : ∀ D ∈ F.powerset, ‖Ψ₂ (∏ i ∈ D, p i)‖ ≤ 1)
      (X₁ X₂ : ℝ) (hX₁ : 0 < X₁) (hX₂ : 0 < X₂), ∀ L : ℝ, 0 < L → ∀ c d : O, d ≠ 0 →
      ∀ (s : Finset (Ideal O × O)) (T : Finset O) (w : Ideal O × O → ℂ) (M Y : ℝ),
      0 ≤ M → 0 ≤ Y → (∀ x ∈ s, x.2 ≠ 0) →
      (∀ x ∈ s, DescentWeightedCauchy.firstElementRowMap (dilationLabel p B v ε₁ ε₂) x ∈ T) →
      (∀ z ∈ T, z ≠ 0) → (∀ z ∈ T, (Ideal.absNorm (Ideal.span {z}) : ℝ) ≤ Y) →
      (∀ x ∈ s, ‖w x‖ ≤ M) →
      ‖∑ x ∈ s, w x * actualFirstKernel p hp hg F B v ε₁ ε₂
        (originalLabelColumn p hg B ε₁ ε₂ true (multiplicativeCoreColumn p Ψ₁ m₁ H₁) c (cubicIdealGenerator x.1))
        (originalLabelColumn p hg B ε₁ ε₂ false (multiplicativeCoreColumn p Ψ₂ m₂ H₂) c (cubicIdealGenerator x.1))
        W V₁ V₂ X₁ X₂ L d x.2‖ ≤
      (L / ‖ringComplex (∏ i ∈ cubeActiveSupport B v ε₁ ε₂, p i)‖) * (M * K * Y ^ δ) *
        Real.sqrt (firstInputFamilyEnergy p hg F B v ε₁ ε₂ true Ψ₁ m₁ H₁ V₁ X₁ c d J T) *
        Real.sqrt (firstInputFamilyEnergy p hg F B v ε₁ ε₂ false Ψ₂ m₂ H₂ V₂ X₂ c d J T) := by
  obtain ⟨K, hK, hb⟩ := first_passage_transfer W V₁ V₂ M₁ M₂ hM₁ hM₂ hV₁ hV₂ J δ hδ
  refine ⟨4 * K, mul_nonneg (by norm_num) hK, ?_⟩
  intro ι _ p hp _ hinj hcop hg hc hpr F B hFB v ε₁ ε₂ hv Ψ₁ Ψ₂ m₁ m₂ H₁ H₂ hΨ₁ hΨ₂ X₁ X₂ hX₁ hX₂
  have hb := hb p hp hinj hcop hg hc hpr F B hFB v ε₁ ε₂ hv
    (multiplicativeCoreColumn p Ψ₁ m₁ H₁) (multiplicativeCoreColumn p Ψ₂ m₂ H₂) X₁ X₂ hX₁ hX₂
  intro L hL c d hd s T w M Y hM hY hn hmap hT hnorm hw
  have h := hb L hL c d hd s T w M Y hM hY hn hmap hT hnorm hw
  let E₁ := firstInputFamilyEnergy p hg F B v ε₁ ε₂ true Ψ₁ m₁ H₁ V₁ X₁ c d J T
  let E₂ := firstInputFamilyEnergy p hg F B v ε₁ ε₂ false Ψ₂ m₂ H₂ V₂ X₂ c d J T
  have hb₁ := firstOutputEnergy_le_input_family p hp hg F B v ε₁ ε₂ true Ψ₁ m₁ H₁ V₁ X₁ c d J T hΨ₁
  have hb₂ := firstOutputEnergy_le_input_family p hp hg F B v ε₁ ε₂ false Ψ₂ m₂ H₂ V₂ X₂ c d J T hΨ₂
  have hscale : 0 ≤ (L / ‖ringComplex (∏ i ∈ cubeActiveSupport B v ε₁ ε₂, p i)‖) * (M * K * Y ^ δ) :=
    mul_nonneg (div_nonneg hL.le (norm_nonneg _))
      (mul_nonneg (mul_nonneg hM hK) (Real.rpow_nonneg hY δ))
  apply h.trans
  calc
    _ ≤ ((L / ‖ringComplex (∏ i ∈ cubeActiveSupport B v ε₁ ε₂, p i)‖) * (M * K * Y ^ δ)) *
        (Real.sqrt (4 * E₁) * Real.sqrt (4 * E₂)) := by
      rw [mul_assoc]
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul (Real.sqrt_le_sqrt hb₁) (Real.sqrt_le_sqrt hb₂)
          (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)) hscale
    _ = _ := by
      rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 4), Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 4)]
      norm_num <;> ring

end FirstPassCubeLabels

namespace FirstPassCubeLabels
open Eisenstein SchwartzPlanePoisson SecondPassArithmetic
open scoped Classical

variable {ι : Type*} [DecidableEq ι] (p : ι → O)
  [∀ i, (Ideal.span {p i}).IsMaximal]
  (hg : ∀ i, lambda ∉ Ideal.span {p i})

def firstFixedTransition (negative : Bool) (G : Finset ι) (r s : QuadraticRayRing) : ℂ :=
  star (primeSubsetRow p (fun i => complexSexticChar (Ideal.span {p i}) (hg i)) G 4) *
    (if negative then star (primeSubsetRow p (fun i => complexSexticChar (Ideal.span {p i}) (hg i)) G (-1)) else 1) *
    (if Ideal.Quotient.mk (Ideal.span {(4 : O)}) (∏ i ∈ G, p i) * s = r then 1 else 0)

theorem firstFixedTransition_norm_le (negative : Bool) (G : Finset ι) (r s : QuadraticRayRing) :
    ‖firstFixedTransition p hg negative G r s‖ ≤ 1 := by
  have h4 := primeSubsetRow_norm_le_one p (fun i => complexSexticChar (Ideal.span {p i}) (hg i)) G 4
  have hm := primeSubsetRow_norm_le_one p (fun i => complexSexticChar (Ideal.span {p i}) (hg i)) G (-1)
  unfold firstFixedTransition
  by_cases hr : Ideal.Quotient.mk (Ideal.span {(4 : O)}) (∏ i ∈ G, p i) * s = r
  · simp only [if_pos hr, mul_one, norm_mul, norm_star]
    cases negative
    · simpa using h4
    · simpa only [ite_true, norm_star] using
        (mul_le_mul h4 hm (norm_nonneg _) zero_le_one).trans_eq (one_mul 1)
  · simp only [if_neg hr, mul_zero, norm_zero, zero_le_one]

/-- Common-prime removal preserves the finite family of fixed residue columns. -/
theorem firstFixedColumn_union (negative : Bool) (G U : Finset ι) (hGU : Disjoint G U)
    (r : QuadraticRayRing) (H : Finset ι → ℂ) :
    firstFixedColumn p hg negative r H (G ∪ U) =
      ∑ s : QuadraticRayRing, firstFixedTransition p hg negative G r s *
        firstFixedColumn p hg negative s (fun T => H (G ∪ T)) U := by
  symm
  rw [Finset.sum_eq_single (Ideal.Quotient.mk (Ideal.span {(4 : O)}) (∏ i ∈ U, p i))]
  · unfold firstFixedTransition firstFixedColumn firstResidueMask
    dsimp only
    rw [Finset.prod_union hGU, map_mul, primeSubsetRow_union p _ G U hGU,
      primeSubsetRow_union p _ G U hGU]
    simp only [if_pos rfl, star_mul]
    cases negative <;> simp only [Bool.false_eq_true, ite_false, ite_true] <;> split_ifs <;> ring
  · intro s _ hs
    simp only [firstFixedColumn, firstResidueMask, if_neg hs.symm, mul_zero]
  · intro h
    exact (h (Finset.mem_univ _)).elim

end FirstPassCubeLabels

namespace FirstPassCubeLabels
open Eisenstein SchwartzPlanePoisson MeasureTheory
open scoped Classical SchwartzMap

abbrev rowMajorant : 𝓢(ℝ, ℂ) := sieveCutoff

lemma rowMajorant_nonneg (s : ℝ) : 0 ≤ (rowMajorant s).re := by
  change 0 ≤ sieveBump s
  exact sieveBump.nonneg

lemma rowMajorant_one (s : ℝ) (hs0 : 0 ≤ s) (hs1 : s ≤ 1) : rowMajorant s = 1 := by
  simp only [rowMajorant, sieveCutoff_apply, sieveBump_eq_one hs0 hs1, Complex.ofReal_one]

lemma rowMajorant_zero (s : ℝ) (hs : 2 < s) : rowMajorant s = 0 := by
  rw [rowMajorant, sieveCutoff_apply, Complex.ofReal_eq_zero]
  by_contra h
  change s ∈ Function.support sieveBump at h
  rw [sieveBump.support_eq] at h
  have hh : |s| < 2 := by
    simpa only [Metric.mem_ball, Real.dist_eq, sub_zero, sieveBump] using h
  linarith [le_abs_self s]

def rowMajorantBall (Y : ℝ) : Finset O :=
  (finite_norm_sublevel (Real.sqrt (2 * Y))).toFinset

lemma rowMajorant_zero_outside (Y : ℝ) (hY : 0 < Y) (z : O)
    (hz : z ∉ rowMajorantBall Y) : rowMajorant (‖ringComplex z‖ ^ 2 / Y) = 0 := by
  apply rowMajorant_zero
  apply (lt_div_iff₀ hY).2
  by_contra hn
  have hn' : ‖ringComplex z‖ ^ 2 ≤ 2 * Y := le_of_not_gt hn
  apply hz
  change z ∈ (finite_norm_sublevel (Real.sqrt (2 * Y))).toFinset
  rw [Set.Finite.mem_toFinset]
  change ‖ringComplex z‖ ≤ Real.sqrt (2 * Y)
  calc
    _ = Real.sqrt (‖ringComplex z‖ ^ 2) := (Real.sqrt_sq (norm_nonneg _)).symm
    _ ≤ _ := Real.sqrt_le_sqrt hn'

lemma rowMajorant_tsum_eq_sum (P : O → ℂ) (Y : ℝ) (hY : 0 < Y) :
    (∑' z : O, rowMajorant (‖ringComplex z‖ ^ 2 / Y) * (‖P z‖ ^ 2 : ℝ)) =
      ∑ z ∈ rowMajorantBall Y, rowMajorant (‖ringComplex z‖ ^ 2 / Y) * (‖P z‖ ^ 2 : ℝ) := by
  apply tsum_eq_sum
  intro z hz
  rw [rowMajorant_zero_outside Y hY z hz, zero_mul]

lemma rowMajorant_summable (P : O → ℂ) (Y : ℝ) (hY : 0 < Y) :
    Summable (fun z : O => rowMajorant (‖ringComplex z‖ ^ 2 / Y) * (‖P z‖ ^ 2 : ℝ)) := by
  apply (hasSum_sum_of_ne_finset_zero (s := rowMajorantBall Y) ?_).summable
  intro z hz
  rw [rowMajorant_zero_outside Y hY z hz, zero_mul]

/-- The existing compact sieve cutoff dominates every finite row ball. -/
theorem finite_row_energy_le_rowMajorant (P : O → ℂ) (T : Finset O)
    (Y : ℝ) (hY : 0 < Y)
    (hT : ∀ z ∈ T, (Ideal.absNorm (Ideal.span {z}) : ℝ) ≤ Y) :
    (∑ z ∈ T, ‖P z‖ ^ 2) ≤
      (∑' z : O, rowMajorant (‖ringComplex z‖ ^ 2 / Y) * (‖P z‖ ^ 2 : ℝ)).re := by
  have hs := rowMajorant_summable P Y hY
  rw [Complex.re_tsum hs]
  calc
    _ = ∑ z ∈ T, (rowMajorant (‖ringComplex z‖ ^ 2 / Y) * (‖P z‖ ^ 2 : ℝ)).re := by
      apply Finset.sum_congr rfl
      intro z hz
      have hratio : ‖ringComplex z‖ ^ 2 / Y ≤ 1 := by
        apply (div_le_one hY).2
        rw [ringComplex_norm_sq_eq_absNorm_span]
        exact hT z hz
      rw [rowMajorant_one _ (div_nonneg (sq_nonneg _) hY.le) hratio, one_mul, Complex.ofReal_re]
    _ ≤ _ := by
      apply (Complex.hasSum_re hs.hasSum).summable.sum_le_tsum
      intro z hz
      simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
      exact mul_nonneg (rowMajorant_nonneg _) (sq_nonneg _)

end FirstPassCubeLabels

namespace FirstPassCubeLabels
open Eisenstein SchwartzPlanePoisson SecondPassArithmetic MeasureTheory
open scoped Classical SchwartzMap

variable {ι : Type*} [DecidableEq ι] (p : ι → O)
  [∀ i, (Ideal.span {p i}).IsMaximal]
  (hg : ∀ i, lambda ∉ Ideal.span {p i})

theorem firstCoreInputRow_majorant_integrable
    (F D B : Finset ι) (v : ι → ℕ) (ε₁ ε₂ : ι → Bool)
    (negative : Bool) (r : QuadraticRayRing) (Ψ : O →* ℂ) (m : O)
    (H : Finset ι → ℂ) (V : ℝ → ℂ) (y : Finset ι → ℝ) (c d : O)
    (Y : ℝ) (hY : 0 < Y)
    {k : ℝ → ℝ} (hk : Integrable k volume) :
    Integrable (fun t : ℝ => k t *
      (∑' z : O, rowMajorant (‖ringComplex z‖ ^ 2 / Y) *
        (↑(‖firstCoreInputRow p hg F D B v ε₁ ε₂ negative r Ψ m H V y c d t z‖ ^ 2) : ℂ)).re) volume := by
  simp_rw [rowMajorant_tsum_eq_sum _ Y hY, Complex.re_sum,
    Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
  simp only [Finset.mul_sum]
  apply integrable_finsetSum
  intro z hz
  simpa only [mul_assoc, mul_left_comm, mul_comm] using
    (firstCoreInputRow_integrable p hg F D B v ε₁ ε₂ negative r Ψ m H V y c d z hk).const_mul
      (rowMajorant (‖ringComplex z‖ ^ 2 / Y)).re

theorem firstCoreInputRow_integrated_le_majorant
    (F D B : Finset ι) (v : ι → ℕ) (ε₁ ε₂ : ι → Bool)
    (negative : Bool) (r : QuadraticRayRing) (Ψ : O →* ℂ) (m : O)
    (H : Finset ι → ℂ) (V : ℝ → ℂ) (y : Finset ι → ℝ) (c d : O)
    (T : Finset O) (Y : ℝ) (hY : 0 < Y)
    (hT : ∀ z ∈ T, (Ideal.absNorm (Ideal.span {z}) : ℝ) ≤ Y)
    {k : ℝ → ℝ} (hk : Integrable k volume) (hk0 : ∀ t, 0 ≤ k t) :
    (∫ t : ℝ, k t * ∑ z ∈ T,
      ‖firstCoreInputRow p hg F D B v ε₁ ε₂ negative r Ψ m H V y c d t z‖ ^ 2) ≤
    ∫ t : ℝ, k t *
      (∑' z : O, rowMajorant (‖ringComplex z‖ ^ 2 / Y) *
        (↑(‖firstCoreInputRow p hg F D B v ε₁ ε₂ negative r Ψ m H V y c d t z‖ ^ 2) : ℂ)).re := by
  apply integral_mono
  · simp only [Finset.mul_sum]
    exact integrable_finsetSum _ (fun z hz =>
      firstCoreInputRow_integrable p hg F D B v ε₁ ε₂ negative r Ψ m H V y c d z hk)
  · exact firstCoreInputRow_majorant_integrable p hg F D B v ε₁ ε₂ negative r Ψ m H V y c d Y hY hk
  · intro t
    exact mul_le_mul_of_nonneg_left (finite_row_energy_le_rowMajorant _ T Y hY hT) (hk0 t)

end FirstPassCubeLabels

namespace FirstPassCubeLabels
open Eisenstein SchwartzPlanePoisson SecondPassArithmetic MeasureTheory
open scoped Classical SchwartzMap

variable {ι : Type*} [DecidableEq ι] (p : ι → O)
  [∀ i, (Ideal.span {p i}).IsMaximal]
  (hp : ∀ i, p i ≠ 0) (hg : ∀ i, lambda ∉ Ideal.span {p i})

/-- Fixed first-pass columns admit the full divisor and frequency expansion of the second passage. -/
theorem firstCoreInputRow_frequency_expansion
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (F D B : Finset ι) (v : ι → ℕ) (ε₁ ε₂ : ι → Bool)
    (negative : Bool) (r : QuadraticRayRing) (Ψ : O →* ℂ) (m : O)
    (H : Finset ι → ℂ) (V : ℝ → ℂ) (y : Finset ι → ℝ) (c d : O) (t : ℝ)
    (W : 𝓢(ℝ, ℂ)) (Y : ℝ) (hY : 0 < Y) :
    (∑' z : O, W (‖ringComplex z‖ ^ 2 / Y) *
      (‖firstCoreInputRow p hg F D B v ε₁ ε₂ negative r Ψ m H V y c d t z‖ ^ 2 : ℝ)) =
      ∑ G ∈ (F \ D).powerset,
        (‖secondInputCoefficient p (fun i => complexSexticChar (Ideal.span {p i}) (hg i))
          Ψ (m * b0Label p B v ε₁ ε₂) (c * jLabel p B v ε₁ ε₂) d (fun _ => 1) G‖ ^ 2 : ℝ) *
        ∑ E ∈ G.powerset, (supportMobius E / (‖ringComplex (∏ i ∈ E, p i)‖ ^ 2 : ℝ)) *
          ∑' k : O, secondFrequencyKernel p hp hg (F \ D) Ψ Ψ
            (m * b0Label p B v ε₁ ε₂) (∏ i ∈ G \ E, p i) (c * jLabel p B v ε₁ ε₂) d
            (∏ i ∈ E, p i) k
            (fun U => firstFixedColumn p hg negative r (firstCoreTest H V y negative t D) (G ∪ U))
            (fun U => firstFixedColumn p hg negative r (firstCoreTest H V y negative t D) (G ∪ U)) W Y :=
  inputConjugateRow_second_frequency_expansion p hp hg hinj (F \ D) Ψ
    (m * b0Label p B v ε₁ ε₂) (c * jLabel p B v ε₁ ε₂) d
    (firstFixedColumn p hg negative r (firstCoreTest H V y negative t D)) W Y hY

theorem firstCoreInputRow_finite_le_frequency_expansion
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (F D B : Finset ι) (v : ι → ℕ) (ε₁ ε₂ : ι → Bool)
    (negative : Bool) (r : QuadraticRayRing) (Ψ : O →* ℂ) (m : O)
    (H : Finset ι → ℂ) (V : ℝ → ℂ) (y : Finset ι → ℝ) (c d : O) (t : ℝ)
    (T : Finset O) (Y : ℝ) (hY : 0 < Y)
    (hT : ∀ z ∈ T, (Ideal.absNorm (Ideal.span {z}) : ℝ) ≤ Y) :
    (∑ z ∈ T, ‖firstCoreInputRow p hg F D B v ε₁ ε₂ negative r Ψ m H V y c d t z‖ ^ 2) ≤
      (∑ G ∈ (F \ D).powerset,
        (‖secondInputCoefficient p (fun i => complexSexticChar (Ideal.span {p i}) (hg i))
          Ψ (m * b0Label p B v ε₁ ε₂) (c * jLabel p B v ε₁ ε₂) d (fun _ => 1) G‖ ^ 2 : ℝ) *
        ∑ E ∈ G.powerset, (supportMobius E / (‖ringComplex (∏ i ∈ E, p i)‖ ^ 2 : ℝ)) *
          ∑' k : O, secondFrequencyKernel p hp hg (F \ D) Ψ Ψ
            (m * b0Label p B v ε₁ ε₂) (∏ i ∈ G \ E, p i) (c * jLabel p B v ε₁ ε₂) d
            (∏ i ∈ E, p i) k
            (fun U => firstFixedColumn p hg negative r (firstCoreTest H V y negative t D) (G ∪ U))
            (fun U => firstFixedColumn p hg negative r (firstCoreTest H V y negative t D) (G ∪ U)) rowMajorant Y).re := by
  rw [← firstCoreInputRow_frequency_expansion p hp hg hinj F D B v ε₁ ε₂ negative r Ψ m H V y c d t rowMajorant Y hY]
  exact finite_row_energy_le_rowMajorant _ T Y hY hT

end FirstPassCubeLabels

namespace FirstPassCubeLabels
open Eisenstein SchwartzPlanePoisson SecondPassArithmetic JointLogSeparation
open scoped Classical

def firstSignedHeight (negative : Bool) (t : ℝ) : ℝ := if negative then t else -t

lemma kernelLogPhase_neg_right (t x : ℝ) : kernelLogPhase t (-x) = kernelLogPhase (-t) x := by
  unfold kernelLogPhase
  congr 1
  push_cast
  ring

variable {ι : Type*} [DecidableEq ι] (p : ι → O) (hp : ∀ i, p i ≠ 0)

include hp in
theorem firstCoreTest_normPhase (H : Finset ι → ℂ) (V : ℝ → ℂ)
    (X : ℝ) (hX : 0 < X) (negative : Bool) (t : ℝ) (D U : Finset ι) :
    firstCoreTest H V (columnLog p X) negative t D U =
      kernelLogPhase (firstSignedHeight negative t) (-Real.log X) *
        normPhase (firstSignedHeight negative t) (∏ i ∈ D ∪ U, p i) *
        firstCoreTest H V (columnLog p X) negative 0 D U := by
  have hz (x : ℝ) : kernelLogPhase 0 x = 1 := by simp [kernelLogPhase]
  cases negative <;>
    simp only [firstCoreTest, firstSignedHeight, Bool.false_eq_true, ite_false, ite_true,
      hz, mul_one, star_mul, kernelLogPhase_neg_right, kernelLogPhase_conjugate, neg_neg] <;>
    rw [kernelLogPhase_columnLog p hp X _ hX] <;>
    simp only [kernelLogPhase_neg_right, neg_neg] <;> ring

variable [∀ i, (Ideal.span {p i}).IsMaximal] (hg : ∀ i, lambda ∉ Ideal.span {p i})

include hp in
/-- The logarithmic Fourier variable changes only the norm height of the multiplicative twist. -/
theorem firstCoreInputRow_normPhase (F D B : Finset ι) (v : ι → ℕ) (ε₁ ε₂ : ι → Bool)
    (negative : Bool) (r : QuadraticRayRing) (Ψ : O →* ℂ) (m : O)
    (H : Finset ι → ℂ) (V : ℝ → ℂ) (X : ℝ) (hX : 0 < X)
    (c d : O) (t : ℝ) (z : O) :
    firstCoreInputRow p hg F D B v ε₁ ε₂ negative r Ψ m H V (columnLog p X) c d t z =
      (kernelLogPhase (firstSignedHeight negative t) (-Real.log X) *
        normPhase (firstSignedHeight negative t) (∏ i ∈ D, p i)) *
        firstCoreInputRow p hg F D B v ε₁ ε₂ negative r
          (normHeightTwist Ψ (firstSignedHeight negative t)) m H V (columnLog p X) c d 0 z := by
  unfold firstCoreInputRow inputConjugateRow supportConjugateSum
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro U hU
  have hd : Disjoint D U := Finset.disjoint_of_subset_right
    (Finset.mem_powerset.mp hU) disjoint_sdiff_self_right
  simp only [secondInputCoefficient, normHeightTwist, MonoidHom.mul_apply]
  unfold firstFixedColumn firstResidueMask
  by_cases hr : Ideal.Quotient.mk (Ideal.span {(4 : O)}) (∏ i ∈ U, p i) = r
  · simp only [if_pos hr]
    rw [firstCoreTest_normPhase p hp H V X hX negative t D U, Finset.prod_union hd, map_mul]
    ring
  · simp only [if_neg hr, mul_zero, zero_mul]

include hp in
theorem firstCoreInputRow_normHeight (F D B : Finset ι) (v : ι → ℕ) (ε₁ ε₂ : ι → Bool)
    (negative : Bool) (r : QuadraticRayRing) (Ψ : O →* ℂ) (m : O)
    (H : Finset ι → ℂ) (V : ℝ → ℂ) (X : ℝ) (hX : 0 < X)
    (c d : O) (t : ℝ) (z : O) :
    ‖firstCoreInputRow p hg F D B v ε₁ ε₂ negative r Ψ m H V (columnLog p X) c d t z‖ =
      ‖firstCoreInputRow p hg F D B v ε₁ ε₂ negative r
        (normHeightTwist Ψ (firstSignedHeight negative t)) m H V (columnLog p X) c d 0 z‖ := by
  rw [firstCoreInputRow_normPhase p hp hg F D B v ε₁ ε₂ negative r Ψ m H V X hX,
    norm_mul, norm_mul, kernelLogPhase_norm,
    normPhase_norm _ _ (Finset.prod_ne_zero_iff.mpr (fun i _ => hp i)), one_mul, one_mul]

end FirstPassCubeLabels

namespace FirstPassCubeLabels
open Eisenstein SchwartzPlanePoisson SecondPassArithmetic SecondPassIntegration JointLogSeparation
open scoped Classical SchwartzMap ContDiff

def firstColumnProfile (negative : Bool) (g : 𝓢(ℝ, ℂ)) : 𝓢(ℝ, ℂ) :=
  if negative then conjugateProfile g else g

lemma firstColumnProfile_support (negative : Bool) (g : 𝓢(ℝ, ℂ)) (s : ℝ) :
    firstColumnProfile negative g s ≠ 0 ↔ g s ≠ 0 := by
  cases negative <;> simp [firstColumnProfile]

variable {ι : Type*} [DecidableEq ι] (p : ι → O) (hp : ∀ i, p i ≠ 0)

theorem firstCoreTest_normalized_profile (H : Finset ι → ℂ) (g : 𝓢(ℝ, ℂ))
    (y : Finset ι → ℝ) (negative : Bool) (D N : Finset ι) :
    firstCoreTest (normalizedColumn p H) g y negative 0 D N =
      H (D ∪ N) * normalizedColumn p (fun S => firstColumnProfile negative g (y S)) (D ∪ N) := by
  have hz (x : ℝ) : kernelLogPhase 0 x = 1 := by simp [kernelLogPhase]
  cases negative <;>
    simp only [firstCoreTest, firstColumnProfile, normalizedColumn, Bool.false_eq_true,
      ite_false, ite_true, hz, mul_one, conjugateProfile_apply, div_eq_mul_inv] <;> ring

include hp in
theorem firstCoreTest_shifted_profile (H : Finset ι → ℂ) (g : 𝓢(ℝ, ℂ))
    (negative : Bool) (D N : Finset ι) (hDN : Disjoint D N)
    (X X₀ : ℝ) (hX : 0 < X) (hX₀ : 0 < X₀)
    (U : ℝ → ℂ) (hUc : HasCompactSupport U) (hUs : ContDiff ℝ ∞ U)
    (hU : ∀ s, g s ≠ 0 → U s = 1) :
    firstCoreTest (normalizedColumn p H) g (columnLog p X) negative 0 D N =
      (Real.sqrt X : ℂ)⁻¹ * H (D ∪ N) *
        halfNormalizationCLM U (firstColumnProfile negative g)
          (Real.log (primeProductNorm p D * X₀ / X) + columnLog p X₀ N) := by
  rw [firstCoreTest_normalized_profile]
  rw [normalizedColumn_union_test p hp D N hDN X X₀ hX hX₀ U hUc hUs
    (firstColumnProfile negative g) (fun s hs => hU s ((firstColumnProfile_support negative g s).mp hs))]
  ring

variable [∀ i, (Ideal.span {p i}).IsMaximal] (hg : ∀ i, lambda ∉ Ideal.span {p i})

include hp in
/-- First-pass column normalization is absorbed into one fixed Schwartz profile. -/
theorem firstCoreInputRow_shifted_profile (F D B : Finset ι) (v : ι → ℕ) (ε₁ ε₂ : ι → Bool)
    (negative : Bool) (r : QuadraticRayRing) (Ψ : O →* ℂ) (m : O)
    (H : Finset ι → ℂ) (g : 𝓢(ℝ, ℂ)) (X X₀ : ℝ) (hX : 0 < X) (hX₀ : 0 < X₀)
    (U : ℝ → ℂ) (hUc : HasCompactSupport U) (hUs : ContDiff ℝ ∞ U)
    (hU : ∀ s, g s ≠ 0 → U s = 1) (c d z : O) :
    firstCoreInputRow p hg F D B v ε₁ ε₂ negative r Ψ m
      (normalizedColumn p H) g (columnLog p X) c d 0 z =
      (Real.sqrt X : ℂ)⁻¹ *
        inputConjugateRow p (fun i => complexSexticChar (Ideal.span {p i}) (hg i)) (F \ D)
          Ψ (m * b0Label p B v ε₁ ε₂) (c * jLabel p B v ε₁ ε₂) d
          (firstFixedColumn p hg negative r (fun N => H (D ∪ N) *
            halfNormalizationCLM U (firstColumnProfile negative g)
              (Real.log (primeProductNorm p D * X₀ / X) + columnLog p X₀ N))) z := by
  unfold firstCoreInputRow inputConjugateRow supportConjugateSum
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro N hN
  have hDN : Disjoint D N := Finset.disjoint_of_subset_right
    (Finset.mem_powerset.mp hN) disjoint_sdiff_self_right
  unfold secondInputCoefficient firstFixedColumn firstResidueMask
  by_cases hr : Ideal.Quotient.mk (Ideal.span {(4 : O)}) (∏ i ∈ N, p i) = r
  · simp only [if_pos hr]
    rw [firstCoreTest_shifted_profile p hp H g negative D N hDN X X₀ hX hX₀ U hUc hUs hU]
    ring
  · simp only [if_neg hr, mul_zero, zero_mul]

end FirstPassCubeLabels

namespace SecondPassArithmetic
open Eisenstein SchwartzPlanePoisson
open scoped Classical

variable {ι : Type*} [DecidableEq ι] (p : ι → O)
  [∀ i, (Ideal.span {p i}).IsMaximal] (hg : ∀ i, lambda ∉ Ideal.span {p i})

/-- Residues of common prime factors affect only bounded outer coefficients. -/
theorem secondChildKernelPair_ray_separation_weighted
    (F V : Finset ι) (Ψ₁ Ψ₂ : O →* ℂ) (m r c d e k₁ k₂ : O)
    (r₁ r₂ : QuadraticRayRing) (H₁ H₂ : Finset ι → ℂ) (K : Finset ι → Finset ι → ℂ) :
    secondChildKernelPair p hg F V Ψ₁ Ψ₂ m r c d e k₁ k₂
      (secondRayMask p hg r₁ H₁) (secondRayMask p hg r₂ H₂) K =
      ∑ s : QuadraticRayRing × QuadraticRayRing,
        (star (secondRayTransition p hg V r₁ s.1) * secondRayTransition p hg V r₂ s.2) *
          fixedChildKernelPair p hg (F \ V) Ψ₁ Ψ₂ (m * r)
            (c * e * ∏ i ∈ V, p i) (d * e * k₁) (d * e * k₂)
            (secondRayColumn p hg s.1 (fun U => H₁ (V ∪ U)))
            (secondRayColumn p hg s.2 (fun U => H₂ (V ∪ U)))
            (fun N M => K (V ∪ N) (V ∪ M)) := by
  let Q := fun (N M : Finset ι) (s : QuadraticRayRing × QuadraticRayRing) =>
    (star (secondRayTransition p hg V r₁ s.1) * secondRayTransition p hg V r₂ s.2) *
      (star (secondChildColumn p hg Ψ₁ (m * r) (c * e * ∏ i ∈ V, p i)
          (d * e * k₁) (secondRayColumn p hg s.1 (fun U => H₁ (V ∪ U))) N) *
        secondChildColumn p hg Ψ₂ (m * r) (c * e * ∏ i ∈ V, p i)
          (d * e * k₂) (secondRayColumn p hg s.2 (fun U => H₂ (V ∪ U))) M * K (V ∪ N) (V ∪ M))
  calc
    _ = ∑ N ∈ (F \ V).powerset, ∑ M ∈ (F \ V).powerset,
        ∑ s : QuadraticRayRing × QuadraticRayRing, Q N M s := by
      apply Finset.sum_congr rfl
      intro N hN
      apply Finset.sum_congr rfl
      intro M hM
      have hdN : Disjoint V N := Finset.disjoint_of_subset_right
        (Finset.mem_powerset.mp hN) disjoint_sdiff_self_right
      have hdM : Disjoint V M := Finset.disjoint_of_subset_right
        (Finset.mem_powerset.mp hM) disjoint_sdiff_self_right
      rw [secondChildColumn_rayMask_union p hg Ψ₁ _ _ _ V N hdN,
        secondChildColumn_rayMask_union p hg Ψ₂ _ _ _ V M hdM]
      simp only [star_sum, star_mul, Finset.sum_mul, Finset.mul_sum, Fintype.sum_prod_type, Q]
      conv_lhs => rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro s hs
      apply Finset.sum_congr rfl
      intro t ht
      ring
    _ = ∑ N ∈ (F \ V).powerset, ∑ s : QuadraticRayRing × QuadraticRayRing,
        ∑ M ∈ (F \ V).powerset, Q N M s := by
      apply Finset.sum_congr rfl
      intro N hN
      exact Finset.sum_comm
    _ = _ := by
      rw [Finset.sum_comm]
      simp only [Q, fixedChildKernelPair, Finset.mul_sum]

theorem secondChildKernelPair_ray_fixed_pool_weighted
    (F V : Finset ι) (Ψ₁ Ψ₂ : O →* ℂ) (m r c d e k₁ k₂ : O)
    (r₁ r₂ : QuadraticRayRing) (H₁ H₂ : Finset ι → ℂ) (K : Finset ι → Finset ι → ℂ) :
    secondChildKernelPair p hg F V Ψ₁ Ψ₂ m r c d e k₁ k₂
      (secondRayMask p hg r₁ H₁) (secondRayMask p hg r₂ H₂) K =
      ∑ s : QuadraticRayRing × QuadraticRayRing,
        (star (secondRayTransition p hg V r₁ s.1) * secondRayTransition p hg V r₂ s.2) *
          fixedChildKernelPair p hg F Ψ₁ Ψ₂ (m * r)
            (c * e * ∏ i ∈ V, p i) (d * e * k₁) (d * e * k₂)
            (secondRayColumn p hg s.1 (fun U => H₁ (V ∪ U)))
            (secondRayColumn p hg s.2 (fun U => H₂ (V ∪ U)))
            (fun N M => K (V ∪ N) (V ∪ M)) := by
  rw [secondChildKernelPair_ray_separation_weighted]
  simp only [fixedChildKernelPair_fixed_pool]

end SecondPassArithmetic

namespace FirstPassCubeLabels
open Eisenstein SchwartzPlanePoisson SecondPassArithmetic
open scoped Classical

variable {ι : Type*} [DecidableEq ι] (p : ι → O)
  [∀ i, (Ideal.span {p i}).IsMaximal]
  (hg : ∀ i, lambda ∉ Ideal.span {p i})

/-- Two fixed residue masks retain the phases from both Poisson passages. -/
def combinedFixedColumn (negative : Bool) (r s : QuadraticRayRing)
    (H : Finset ι → ℂ) : Finset ι → ℂ :=
  secondRayColumn p hg s (firstFixedColumn p hg negative r H)

theorem combinedFixedColumn_norm_le (negative : Bool) (r s : QuadraticRayRing)
    (H : Finset ι → ℂ) (N : Finset ι) :
    ‖combinedFixedColumn p hg negative r s H N‖ ≤ ‖H N‖ :=
  (secondRayColumn_norm_le p hg s _ N).trans (firstFixedColumn_norm_le p hg negative r H N)

/-- The second residue mask commutes with removal of the first common prime factors. -/
theorem secondRayColumn_firstFixed_union (negative : Bool) (G N : Finset ι) (hGN : Disjoint G N)
    (r s : QuadraticRayRing) (H : Finset ι → ℂ) :
    secondRayColumn p hg s (fun U => firstFixedColumn p hg negative r H (G ∪ U)) N =
      ∑ q : QuadraticRayRing, firstFixedTransition p hg negative G r q *
        combinedFixedColumn p hg negative q s (fun U => H (G ∪ U)) N := by
  simp only [combinedFixedColumn, secondRayColumn]
  by_cases hs : Ideal.Quotient.mk (Ideal.span {(4 : O)}) (∏ i ∈ N, p i) = s
  · simp only [if_pos hs]
    rw [firstFixedColumn_union p hg negative G N hGN]
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro q _
    ring
  · simp only [if_neg hs, mul_zero, Finset.sum_const_zero]

lemma secondChildColumn_firstFixed_union (Ψ : O →* ℂ) (m f y : O)
    (negative : Bool) (G N : Finset ι) (hGN : Disjoint G N)
    (r s : QuadraticRayRing) (H : Finset ι → ℂ) :
    secondChildColumn p hg Ψ m f y
      (secondRayColumn p hg s (fun U => firstFixedColumn p hg negative r H (G ∪ U))) N =
      ∑ q : QuadraticRayRing, firstFixedTransition p hg negative G r q *
        secondChildColumn p hg Ψ m f y
          (combinedFixedColumn p hg negative q s (fun U => H (G ∪ U))) N := by
  rw [secondChildColumn, secondRayColumn_firstFixed_union p hg negative G N hGN]
  simp only [secondChildColumn, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro q _
  ring

/-- Both arithmetic phase families reduce to a fixed finite collection of descendant columns. -/
theorem fixedChildKernelPair_first_residue_separation
    (F G : Finset ι) (Ψ₁ Ψ₂ : O →* ℂ) (m f y₁ y₂ : O)
    (negative₁ negative₂ : Bool) (r₁ r₂ s₁ s₂ : QuadraticRayRing)
    (H₁ H₂ : Finset ι → ℂ) (K : Finset ι → Finset ι → ℂ) :
    fixedChildKernelPair p hg (F \ G) Ψ₁ Ψ₂ m f y₁ y₂
      (secondRayColumn p hg s₁ (fun U => firstFixedColumn p hg negative₁ r₁ H₁ (G ∪ U)))
      (secondRayColumn p hg s₂ (fun U => firstFixedColumn p hg negative₂ r₂ H₂ (G ∪ U))) K =
      ∑ q : QuadraticRayRing × QuadraticRayRing,
        (star (firstFixedTransition p hg negative₁ G r₁ q.1) * firstFixedTransition p hg negative₂ G r₂ q.2) *
          fixedChildKernelPair p hg (F \ G) Ψ₁ Ψ₂ m f y₁ y₂
            (combinedFixedColumn p hg negative₁ q.1 s₁ (fun U => H₁ (G ∪ U)))
            (combinedFixedColumn p hg negative₂ q.2 s₂ (fun U => H₂ (G ∪ U))) K := by
  let Q := fun (N M : Finset ι) (q : QuadraticRayRing × QuadraticRayRing) =>
    (star (firstFixedTransition p hg negative₁ G r₁ q.1) * firstFixedTransition p hg negative₂ G r₂ q.2) *
      (star (secondChildColumn p hg Ψ₁ m f y₁
        (combinedFixedColumn p hg negative₁ q.1 s₁ (fun U => H₁ (G ∪ U))) N) *
      secondChildColumn p hg Ψ₂ m f y₂
        (combinedFixedColumn p hg negative₂ q.2 s₂ (fun U => H₂ (G ∪ U))) M * K N M)
  calc
    _ = ∑ N ∈ (F \ G).powerset, ∑ M ∈ (F \ G).powerset,
        ∑ q : QuadraticRayRing × QuadraticRayRing, Q N M q := by
      apply Finset.sum_congr rfl
      intro N hN
      apply Finset.sum_congr rfl
      intro M hM
      have hGN : Disjoint G N := Finset.disjoint_of_subset_right
        (Finset.mem_powerset.mp hN) disjoint_sdiff_self_right
      have hGM : Disjoint G M := Finset.disjoint_of_subset_right
        (Finset.mem_powerset.mp hM) disjoint_sdiff_self_right
      rw [secondChildColumn_firstFixed_union p hg Ψ₁ m f y₁ negative₁ G N hGN,
        secondChildColumn_firstFixed_union p hg Ψ₂ m f y₂ negative₂ G M hGM]
      simp only [star_sum, star_mul, Finset.sum_mul, Finset.mul_sum, Fintype.sum_prod_type, Q]
      conv_lhs => rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro a _
      apply Finset.sum_congr rfl
      intro b _
      ring
    _ = ∑ N ∈ (F \ G).powerset, ∑ q : QuadraticRayRing × QuadraticRayRing,
        ∑ M ∈ (F \ G).powerset, Q N M q := by
      apply Finset.sum_congr rfl
      intro N _
      exact Finset.sum_comm
    _ = _ := by
      rw [Finset.sum_comm]
      simp only [Q, fixedChildKernelPair, Finset.mul_sum]

end FirstPassCubeLabels

namespace SecondPassArithmetic
open Eisenstein SchwartzPlanePoisson
open scoped Classical

variable {ι : Type*} [DecidableEq ι] (p : ι → O)
  [∀ i, (Ideal.span {p i}).IsMaximal]
  (χ : ∀ i, MulChar (O ⧸ Ideal.span {p i}) ℂ)

/-- Removing a prime support from a row sum is exactly multiplication of its coprimality label. -/
theorem inputConjugateRow_fixed_pool
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (F G : Finset ι) (Ψ : O →* ℂ) (m c d : O) (H : Finset ι → ℂ) (z : O) :
    inputConjugateRow p χ (F \ G) Ψ m c d H z =
      inputConjugateRow p χ F Ψ (m * ∏ i ∈ G, p i) c d H z := by
  unfold inputConjugateRow supportConjugateSum
  rw [sum_remove_common_pool p hinj F G]
  apply Finset.sum_congr rfl
  intro U _
  rw [secondInputCoefficient_fixed_mask]
  ring

end SecondPassArithmetic

namespace FirstPassCubeLabels
open Eisenstein SchwartzPlanePoisson SecondPassArithmetic
open scoped Classical

variable {ι : Type*} [DecidableEq ι] (p : ι → O)
  [∀ i, (Ideal.span {p i}).IsMaximal]
  (hg : ∀ i, lambda ∉ Ideal.span {p i})

theorem firstCoreInputRow_fixed_pool
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (F D B : Finset ι) (v : ι → ℕ) (ε₁ ε₂ : ι → Bool)
    (negative : Bool) (r : QuadraticRayRing) (Ψ : O →* ℂ) (m : O)
    (H : Finset ι → ℂ) (V : ℝ → ℂ) (y : Finset ι → ℝ)
    (c d : O) (t : ℝ) (z : O) :
    firstCoreInputRow p hg F D B v ε₁ ε₂ negative r Ψ m H V y c d t z =
      inputConjugateRow p (fun i => complexSexticChar (Ideal.span {p i}) (hg i)) F
        Ψ (m * b0Label p B v ε₁ ε₂ * ∏ i ∈ D, p i) (c * jLabel p B v ε₁ ε₂) d
        (firstFixedColumn p hg negative r (firstCoreTest H V y negative t D)) z :=
  inputConjugateRow_fixed_pool p _ hinj F D Ψ (m * b0Label p B v ε₁ ε₂)
    (c * jLabel p B v ε₁ ε₂) d _ z

end FirstPassCubeLabels

namespace FirstPassCubeLabels
open Eisenstein SchwartzPlanePoisson SecondPassArithmetic MeasureTheory
open scoped Classical SchwartzMap

variable {ι : Type*} [DecidableEq ι] (p : ι → O)
  [∀ i, (Ideal.span {p i}).IsMaximal]
  (hp : ∀ i, p i ≠ 0) (hg : ∀ i, lambda ∉ Ideal.span {p i})

/-- The actual divisor-frequency sum obtained by reflecting a fixed first-pass input. -/
def firstCoreFrequencySum (F D B : Finset ι) (v : ι → ℕ) (ε₁ ε₂ : ι → Bool)
    (negative : Bool) (r : QuadraticRayRing) (Ψ : O →* ℂ) (m : O)
    (H : Finset ι → ℂ) (V : ℝ → ℂ) (y : Finset ι → ℝ) (c d : O) (t Y : ℝ) : ℂ :=
  ∑ G ∈ (F \ D).powerset,
    (‖secondInputCoefficient p (fun i => complexSexticChar (Ideal.span {p i}) (hg i))
      Ψ (m * b0Label p B v ε₁ ε₂) (c * jLabel p B v ε₁ ε₂) d (fun _ => 1) G‖ ^ 2 : ℝ) *
    ∑ E ∈ G.powerset, (supportMobius E / (‖ringComplex (∏ i ∈ E, p i)‖ ^ 2 : ℝ)) *
      ∑' k : O, secondFrequencyKernel p hp hg (F \ D) Ψ Ψ
        (m * b0Label p B v ε₁ ε₂) (∏ i ∈ G \ E, p i) (c * jLabel p B v ε₁ ε₂) d
        (∏ i ∈ E, p i) k
        (fun U => firstFixedColumn p hg negative r (firstCoreTest H V y negative t D) (G ∪ U))
        (fun U => firstFixedColumn p hg negative r (firstCoreTest H V y negative t D) (G ∪ U)) rowMajorant Y

theorem firstCoreFrequencySum_eq_majorant
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (F D B : Finset ι) (v : ι → ℕ) (ε₁ ε₂ : ι → Bool)
    (negative : Bool) (r : QuadraticRayRing) (Ψ : O →* ℂ) (m : O)
    (H : Finset ι → ℂ) (V : ℝ → ℂ) (y : Finset ι → ℝ) (c d : O)
    (t Y : ℝ) (hY : 0 < Y) :
    firstCoreFrequencySum p hp hg F D B v ε₁ ε₂ negative r Ψ m H V y c d t Y =
      ∑' z : O, rowMajorant (‖ringComplex z‖ ^ 2 / Y) *
        (‖firstCoreInputRow p hg F D B v ε₁ ε₂ negative r Ψ m H V y c d t z‖ ^ 2 : ℝ) :=
  (firstCoreInputRow_frequency_expansion p hp hg hinj F D B v ε₁ ε₂ negative r Ψ m H V y c d t rowMajorant Y hY).symm

theorem firstCoreFrequencySum_re_nonneg
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (F D B : Finset ι) (v : ι → ℕ) (ε₁ ε₂ : ι → Bool)
    (negative : Bool) (r : QuadraticRayRing) (Ψ : O →* ℂ) (m : O)
    (H : Finset ι → ℂ) (V : ℝ → ℂ) (y : Finset ι → ℝ) (c d : O)
    (t Y : ℝ) (hY : 0 < Y) :
    0 ≤ (firstCoreFrequencySum p hp hg F D B v ε₁ ε₂ negative r Ψ m H V y c d t Y).re := by
  rw [firstCoreFrequencySum_eq_majorant p hp hg hinj F D B v ε₁ ε₂ negative r Ψ m H V y c d t Y hY,
    rowMajorant_tsum_eq_sum _ Y hY, Complex.re_sum]
  apply Finset.sum_nonneg
  intro z _
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
  exact mul_nonneg (rowMajorant_nonneg _) (sq_nonneg _)

def firstReflectedFamilyEnergy (F B : Finset ι) (v : ι → ℕ) (ε₁ ε₂ : ι → Bool)
    (negative : Bool) (Ψ : O →* ℂ) (m : O) (H : Finset ι → ℂ)
    (V : ℝ → ℂ) (X : ℝ) (c d : O) (J : ℕ) (Y : ℝ) : ℝ :=
  ∑ D ∈ F.powerset, ∑ r : QuadraticRayRing × QuadraticRayRing,
    (2 : ℝ) * ∫ t : ℝ, firstLogDensity J t *
      (firstCoreFrequencySum p hp hg F D B v ε₁ ε₂ negative (if negative then r.1 else r.2)
        Ψ m (normalizedColumn p H) V (columnLog p X) c d t Y).re

theorem firstInputFamilyEnergy_le_reflection
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (F B : Finset ι) (v : ι → ℕ) (ε₁ ε₂ : ι → Bool)
    (negative : Bool) (Ψ : O →* ℂ) (m : O) (H : Finset ι → ℂ)
    (V : ℝ → ℂ) (X : ℝ) (c d : O) (J : ℕ) (T : Finset O) (Y : ℝ) (hY : 0 < Y)
    (hT : ∀ z ∈ T, (Ideal.absNorm (Ideal.span {z}) : ℝ) ≤ Y) :
    firstInputFamilyEnergy p hg F B v ε₁ ε₂ negative Ψ m H V X c d J T ≤
      firstReflectedFamilyEnergy p hp hg F B v ε₁ ε₂ negative Ψ m H V X c d J Y := by
  unfold firstInputFamilyEnergy firstReflectedFamilyEnergy
  apply Finset.sum_le_sum
  intro D _
  apply Finset.sum_le_sum
  intro r _
  apply mul_le_mul_of_nonneg_left _ (by norm_num : (0 : ℝ) ≤ 2)
  simp_rw [firstCoreFrequencySum_eq_majorant p hp hg hinj F D B v ε₁ ε₂ negative
    (if negative then r.1 else r.2) Ψ m (normalizedColumn p H) V (columnLog p X) c d _ Y hY]
  exact firstCoreInputRow_integrated_le_majorant p hg F D B v ε₁ ε₂ negative
    (if negative then r.1 else r.2) Ψ m (normalizedColumn p H) V (columnLog p X) c d T Y hY hT
    (firstLogDensity_integrable J) (firstLogDensity_nonneg J)

end FirstPassCubeLabels

namespace SecondPassArithmetic
open Eisenstein SchwartzPlanePoisson SecondPassFiber
open scoped Classical

/-- Actual expansion data have the same small divisor-fiber loss as their ideal encoding. -/
theorem globalSecond_energy_pushforward (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ {ι : Type*} [DecidableEq ι]
      (p : ι → O) [∀ i, (Ideal.span {p i}).IsMaximal]
      (hinj : Function.Injective (fun i => Ideal.span {p i}))
      (s : Finset (GlobalSecondData ι)) (T : Finset (Ideal O × O))
      (q : Ideal O × Ideal O × Ideal O) (w : GlobalSecondData ι → ℂ)
      (P : Ideal O × O → ℂ) (B H : ℝ),
      q.1 ≠ ⊥ → 0 ≤ B →
      (∀ x ∈ s, GlobalSecondAdmissible x) →
      (∀ x ∈ s, globalSecondFixedTriple p x = q) →
      (∀ x ∈ s, (newLabel (globalSecondTuple p x), newRow (globalSecondTuple p x)) ∈ T) →
      (∀ z ∈ T, z.1 ≠ ⊥) →
      (∀ z ∈ T, (Ideal.absNorm z.1 : ℝ) ≤ H) →
      (∀ x ∈ s, ‖w x‖ ≤ B) →
      (∑ x ∈ s, ‖w x‖ * ‖P (newLabel (globalSecondTuple p x), newRow (globalSecondTuple p x))‖ ^ 2) ≤
        B * C * (H * Ideal.absNorm q.1) ^ ε * ∑ z ∈ T, ‖P z‖ ^ 2 := by
  obtain ⟨C, hC, hc⟩ := globalSecond_fiber_card ε hε
  refine ⟨C, hC, ?_⟩
  intro ι _ p _ hinj s T q w P B H hq hB ha htr hmap ht hnorm hw
  have hpush := DescentWeightedCauchy.bounded_energy_pushforward s T
    (fun x => (newLabel (globalSecondTuple p x), newRow (globalSecondTuple p x))) w P B hmap hw
  apply hpush.trans
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro z hz
  let S := s.filter (fun x => (newLabel (globalSecondTuple p x), newRow (globalSecondTuple p x)) = z)
  have hsa : ∀ x ∈ S, GlobalSecondAdmissible x := fun x hx => ha x (Finset.mem_filter.mp hx).1
  have hsq : ∀ x ∈ S, globalSecondFixedTriple p x = q := fun x hx => htr x (Finset.mem_filter.mp hx).1
  have hsl : ∀ x ∈ S, newLabel (globalSecondTuple p x) = z.1 :=
    fun x hx => congrArg Prod.fst (Finset.mem_filter.mp hx).2
  have hsr : ∀ x ∈ S, newRow (globalSecondTuple p x) = z.2 :=
    fun x hx => congrArg Prod.snd (Finset.mem_filter.mp hx).2
  have hfiber := hc p hinj S q z.1 z.2 hsa (ht z hz) hq hsq hsl hsr
  have hgrowth : (Ideal.absNorm z.1 : ℝ) * Ideal.absNorm q.1 ≤ H * Ideal.absNorm q.1 :=
    mul_le_mul_of_nonneg_right (hnorm z hz) (by positivity)
  have hcard := hfiber.trans (mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow (by positivity) hgrowth hε.le) hC.le)
  simpa only [mul_assoc] using mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hcard hB) (sq_nonneg ‖P z‖)

theorem globalSecond_energy_selected_family {κ : Type*} [Fintype κ] (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ {ι : Type*} [DecidableEq ι]
      (p : ι → O) [∀ i, (Ideal.span {p i}).IsMaximal]
      (hinj : Function.Injective (fun i => Ideal.span {p i}))
      (s : Finset (GlobalSecondData ι)) (T : Finset (Ideal O × O))
      (q : Ideal O × Ideal O × Ideal O) (w : GlobalSecondData ι → ℂ)
      (P : κ → Ideal O × O → ℂ) (sel : GlobalSecondData ι → κ) (B H : ℝ),
      q.1 ≠ ⊥ → 0 ≤ B →
      (∀ x ∈ s, GlobalSecondAdmissible x) →
      (∀ x ∈ s, globalSecondFixedTriple p x = q) →
      (∀ x ∈ s, (newLabel (globalSecondTuple p x), newRow (globalSecondTuple p x)) ∈ T) →
      (∀ z ∈ T, z.1 ≠ ⊥) → (∀ z ∈ T, (Ideal.absNorm z.1 : ℝ) ≤ H) →
      (∀ x ∈ s, ‖w x‖ ≤ B) →
      (∑ x ∈ s, ‖w x‖ * ‖P (sel x) (newLabel (globalSecondTuple p x), newRow (globalSecondTuple p x))‖ ^ 2) ≤
        B * C * (H * Ideal.absNorm q.1) ^ ε * ∑ u : κ, ∑ z ∈ T, ‖P u z‖ ^ 2 := by
  obtain ⟨C, hC, hb⟩ := globalSecond_energy_pushforward ε hε
  refine ⟨C, hC, ?_⟩
  intro ι _ p _ hinj s T q w P sel B H hq hB ha htr hmap ht hnorm hw
  calc
    _ ≤ ∑ x ∈ s, ‖w x‖ * ∑ u : κ,
        ‖P u (newLabel (globalSecondTuple p x), newRow (globalSecondTuple p x))‖ ^ 2 := by
      apply Finset.sum_le_sum
      intro x _
      apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
      exact Finset.single_le_sum (s := Finset.univ) (a := sel x)
        (f := fun u : κ => ‖P u (newLabel (globalSecondTuple p x), newRow (globalSecondTuple p x))‖ ^ 2)
        (fun u _ => sq_nonneg _) (Finset.mem_univ _)
    _ = ∑ u : κ, ∑ x ∈ s, ‖w x‖ *
        ‖P u (newLabel (globalSecondTuple p x), newRow (globalSecondTuple p x))‖ ^ 2 := by
      simp only [Finset.mul_sum]
      exact Finset.sum_comm
    _ ≤ ∑ u : κ, B * C * (H * Ideal.absNorm q.1) ^ ε * ∑ z ∈ T, ‖P u z‖ ^ 2 :=
      Finset.sum_le_sum (fun u _ => hb p hinj s T q w (P u) B H hq hB ha htr hmap ht hnorm hw)
    _ = _ := by rw [Finset.mul_sum]

end SecondPassArithmetic

namespace SecondPassArithmetic
open Eisenstein SecondPassFiber
open scoped Classical
local instance : Finite Oˣ := cubic_units_finite
local instance : Fintype Oˣ := Fintype.ofFinite _

/-- A fixed descendant mode summed over the actual two-pass expansion data. -/
def globalSecondMode {ι : Type*} [DecidableEq ι] (p : ι → O)
    [∀ i, (Ideal.span {p i}).IsMaximal] (hg : ∀ i, lambda ∉ Ideal.span {p i})
    (s : Finset (GlobalSecondData ι)) (w : GlobalSecondData ι → ℂ)
    (label : GlobalSecondData ι → O) (F : Finset ι) (Ψ₁ Ψ₂ : O →* ℂ)
    (m : O) (H₁ H₂ : Finset ι → ℂ) : ℂ :=
  ∑ x ∈ s, w x *
    star (fixedChildRow p hg F Ψ₁ m H₁ (label x) (newRow (globalSecondTuple p x))) *
      fixedChildRow p hg F Ψ₂ m H₂ (label x) (-newRow (globalSecondTuple p x))

theorem globalSecond_labeled_child_energy (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ {ι : Type*} [DecidableEq ι]
      (p : ι → O) [∀ i, (Ideal.span {p i}).IsMaximal]
      (hinj : Function.Injective (fun i => Ideal.span {p i}))
      (hg : ∀ i, lambda ∉ Ideal.span {p i})
      (s : Finset (GlobalSecondData ι)) (T : Finset (Ideal O × O))
      (q : Ideal O × Ideal O × Ideal O) (w : GlobalSecondData ι → ℂ)
      (B L : ℝ) (label : GlobalSecondData ι → O) (F : Finset ι)
      (Ψ : O →* ℂ) (m : O) (H : Finset ι → ℂ) (negative : Bool),
      q.1 ≠ ⊥ → 0 ≤ B →
      (∀ x ∈ s, GlobalSecondAdmissible x) →
      (∀ x ∈ s, globalSecondFixedTriple p x = q) →
      (∀ x ∈ s, (newLabel (globalSecondTuple p x), newRow (globalSecondTuple p x)) ∈ T) →
      (∀ z ∈ T, z.1 ≠ ⊥) → (∀ z ∈ T, (Ideal.absNorm z.1 : ℝ) ≤ L) →
      (∀ x ∈ s, ‖w x‖ ≤ B) →
      (∀ x ∈ s, Ideal.span {label x} = newLabel (globalSecondTuple p x)) →
      (∑ x ∈ s, ‖w x‖ * ‖fixedChildRow p hg F Ψ m H (label x)
        (if negative then -newRow (globalSecondTuple p x) else newRow (globalSecondTuple p x))‖ ^ 2) ≤
      B * C * (L * Ideal.absNorm q.1) ^ ε *
        ∑ u : Oˣ, ∑ z ∈ T, ‖idealChildRow p hg F Ψ m H negative u z‖ ^ 2 := by
  obtain ⟨C, hC, hb⟩ := globalSecond_energy_selected_family (κ := Oˣ) ε hε
  refine ⟨C, hC, ?_⟩
  intro ι _ p _ hinj hg s T q w B L label F Ψ m H negative hq hB ha ht hm hT hn hw hl
  let sel : GlobalSecondData ι → Oˣ := fun x => if hx : x ∈ s then
    Classical.choose (exists_label_unit (label x) (newLabel (globalSecondTuple p x)) (hl x hx)) else 1
  have hsel (x) (hx : x ∈ s) :
      label x = (sel x : O) * cubicIdealGenerator (newLabel (globalSecondTuple p x)) := by
    simp only [sel, dif_pos hx]
    exact Classical.choose_spec (exists_label_unit (label x) (newLabel (globalSecondTuple p x)) (hl x hx))
  have h := hb p hinj s T q w (idealChildRow p hg F Ψ m H negative) sel B L hq hB ha ht hm hT hn hw
  convert h using 1
  apply Finset.sum_congr rfl
  intro x hx
  rw [hsel x hx]
  rfl

/-- Global expansion multiplicities cost only a small power after fixing three divisor ideals. -/
theorem globalSecond_mode_transfer (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ {ι : Type*} [DecidableEq ι]
      (p : ι → O) [∀ i, (Ideal.span {p i}).IsMaximal]
      (hinj : Function.Injective (fun i => Ideal.span {p i}))
      (hg : ∀ i, lambda ∉ Ideal.span {p i})
      (s : Finset (GlobalSecondData ι)) (T : Finset (Ideal O × O))
      (q : Ideal O × Ideal O × Ideal O) (w : GlobalSecondData ι → ℂ)
      (B L : ℝ) (label : GlobalSecondData ι → O) (F : Finset ι)
      (Ψ₁ Ψ₂ : O →* ℂ) (m : O) (H₁ H₂ : Finset ι → ℂ),
      q.1 ≠ ⊥ → 0 ≤ B → 0 ≤ L →
      (∀ x ∈ s, GlobalSecondAdmissible x) →
      (∀ x ∈ s, globalSecondFixedTriple p x = q) →
      (∀ x ∈ s, (newLabel (globalSecondTuple p x), newRow (globalSecondTuple p x)) ∈ T) →
      (∀ z ∈ T, z.1 ≠ ⊥) → (∀ z ∈ T, (Ideal.absNorm z.1 : ℝ) ≤ L) →
      (∀ x ∈ s, ‖w x‖ ≤ B) →
      (∀ x ∈ s, Ideal.span {label x} = newLabel (globalSecondTuple p x)) →
      ‖globalSecondMode p hg s w label F Ψ₁ Ψ₂ m H₁ H₂‖ ≤
        (B * C * (L * Ideal.absNorm q.1) ^ ε) *
        Real.sqrt (∑ u : Oˣ, ∑ z ∈ T, ‖idealChildRow p hg F Ψ₁ m H₁ false u z‖ ^ 2) *
        Real.sqrt (∑ u : Oˣ, ∑ z ∈ T, ‖idealChildRow p hg F Ψ₂ m H₂ true u z‖ ^ 2) := by
  obtain ⟨C, hC, hpush⟩ := globalSecond_labeled_child_energy ε hε
  refine ⟨C, hC, ?_⟩
  intro ι _ p _ hinj hg s T q w B L label F Ψ₁ Ψ₂ m H₁ H₂ hq hB hL ha ht hm hT hn hw hl
  let P₁ := fun x => fixedChildRow p hg F Ψ₁ m H₁ (label x) (newRow (globalSecondTuple p x))
  let P₂ := fun x => fixedChildRow p hg F Ψ₂ m H₂ (label x) (-newRow (globalSecondTuple p x))
  have h₁ := hpush p hinj hg s T q w B L label F Ψ₁ m H₁ false hq hB ha ht hm hT hn hw hl
  have h₂ := hpush p hinj hg s T q w B L label F Ψ₂ m H₂ true hq hB ha ht hm hT hn hw hl
  simp only [Bool.false_eq_true, ite_false, ite_true] at h₁ h₂
  let D : ℝ := B * C * (L * Ideal.absNorm q.1) ^ ε
  have hD : 0 ≤ D := by dsimp only [D]; positivity
  have hcauchy := DescentWeightedCauchy.weighted_cauchy s w P₂ P₁
  have heq : globalSecondMode p hg s w label F Ψ₁ Ψ₂ m H₁ H₂ =
      ∑ x ∈ s, w x * P₂ x * star (P₁ x) := by
    unfold globalSecondMode
    apply Finset.sum_congr rfl
    intro x _
    dsimp only [P₁, P₂]
    ring
  rw [heq]
  apply hcauchy.trans
  calc
    _ ≤ Real.sqrt (D * (∑ u : Oˣ, ∑ z ∈ T, ‖idealChildRow p hg F Ψ₂ m H₂ true u z‖ ^ 2)) *
        Real.sqrt (D * (∑ u : Oˣ, ∑ z ∈ T, ‖idealChildRow p hg F Ψ₁ m H₁ false u z‖ ^ 2)) := by
      gcongr
    _ = _ := by
      rw [Real.sqrt_mul hD, Real.sqrt_mul hD]
      calc
        _ = (Real.sqrt D) ^ 2 *
            Real.sqrt (∑ u : Oˣ, ∑ z ∈ T, ‖idealChildRow p hg F Ψ₁ m H₁ false u z‖ ^ 2) *
            Real.sqrt (∑ u : Oˣ, ∑ z ∈ T, ‖idealChildRow p hg F Ψ₂ m H₂ true u z‖ ^ 2) := by ring
        _ = _ := by rw [Real.sq_sqrt hD]

end SecondPassArithmetic

namespace SecondPassIntegration
open Eisenstein SchwartzPlanePoisson SecondPassArithmetic SecondPassFiber JointLogSeparation MeasureTheory
open scoped Classical SchwartzMap FourierTransform
local instance : Finite Oˣ := cubic_units_finite
local instance : Fintype Oˣ := Fintype.ofFinite _

def globalIntegratedSecondMode {ι : Type*} [DecidableEq ι]
    (p : ι → O) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hg : ∀ i, lambda ∉ Ideal.span {p i}) (H₁ H₂ : Finset ι → ℂ)
    (b₁ b₂ b₃ : 𝓢(ℝ, ℂ)) (s : Finset (GlobalSecondData ι))
    (w : Frequency → GlobalSecondData ι → ℂ) (label : GlobalSecondData ι → O)
    (F : Finset ι) (Ψ₁ Ψ₂ : O →* ℂ) (m : O) (V₁ V₂ : ℝ → ℂ) (X₁ X₂ : ℝ) : ℂ :=
  ∫ t₁ : ℝ, ∫ t₂ : ℝ, ∫ t₃ : ℝ, tripleCoefficient b₁ b₂ b₃ (t₁,t₂,t₃) *
    globalSecondMode p hg s (w (t₁,t₂,t₃)) label F Ψ₁ Ψ₂ m
      (weightedSecondTest p H₁ V₁ X₁ t₁ t₃ true) (weightedSecondTest p H₂ V₂ X₂ t₂ t₃ false)

theorem globalSecond_integrated_mode_transfer (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ {ι : Type*} [DecidableEq ι]
      (p : ι → O) [∀ i, (Ideal.span {p i}).IsMaximal]
      (hinj : Function.Injective (fun i => Ideal.span {p i}))
      (hg : ∀ i, lambda ∉ Ideal.span {p i}), ∀ (H₁ H₂ : Finset ι → ℂ) (s : Finset (GlobalSecondData ι)) (T : Finset (Ideal O × O))
      (q0 : Ideal O × Ideal O × Ideal O) (w : Frequency → (GlobalSecondData ι) → ℂ) (B lengthScale : ℝ) (label : (GlobalSecondData ι) → O)
      (F : Finset ι) (Ψ₁ Ψ₂ : O →* ℂ) (m : O) (V₁ V₂ : ℝ → ℂ) (X₁ X₂ : ℝ)
      (b₁ b₂ b₃ : 𝓢(ℝ, ℂ)),
      q0.1 ≠ ⊥ → 0 ≤ B → 0 ≤ lengthScale →
      (∀ x ∈ s, GlobalSecondAdmissible x) →
      (∀ x ∈ s, globalSecondFixedTriple p x = q0) →
      (∀ x ∈ s, (newLabel (globalSecondTuple p x), newRow (globalSecondTuple p x)) ∈ T) →
      (∀ z ∈ T, z.1 ≠ ⊥) → (∀ z ∈ T, (Ideal.absNorm z.1 : ℝ) ≤ lengthScale) →
      (∀ q, ∀ x ∈ s, ‖w q x‖ ≤ B) → (∀ x ∈ s, Continuous (fun q => w q x)) →
      (∀ x ∈ s, Ideal.span {label x} = newLabel (globalSecondTuple p x)) →
      ‖globalIntegratedSecondMode p hg H₁ H₂ b₁ b₂ b₃ s w label F Ψ₁ Ψ₂ m V₁ V₂ X₁ X₂‖ ≤
        (B * C * (lengthScale * Ideal.absNorm q0.1)^ε) *
        (∫ t₁ : ℝ, ∫ t₂ : ℝ, ∫ t₃ : ℝ,
          ‖tripleCoefficient b₁ b₂ b₃ (t₁,t₂,t₃)‖ *
            childGeometricMean p hg H₁ H₂ F Ψ₁ Ψ₂ m T V₁ V₂ X₁ X₂ (t₁,t₂,t₃)) := by
  obtain ⟨C, hC, hb⟩ := globalSecond_mode_transfer ε hε
  refine ⟨C, hC, ?_⟩
  intro ι _ p _ hinj hg
  have hb := hb p hinj hg
  intro H₁ H₂ s T q0 w B lengthScale label F Ψ₁ Ψ₂ m V₁ V₂ X₁ X₂ b₁ b₂ b₃ hb0 hB hL hv htq hm ht hn hw hwc hl
  let f : Frequency → ℂ := fun q => globalSecondMode p hg s (w q) label F Ψ₁ Ψ₂ m
    (weightedSecondTest p H₁ V₁ X₁ q.1 q.2.2 true) (weightedSecondTest p H₂ V₂ X₂ q.2.1 q.2.2 false)
  let G := childGeometricMean p hg H₁ H₂ F Ψ₁ Ψ₂ m T V₁ V₂ X₁ X₂
  have hc₁ := childEnergy_continuous p hg H₁ F Ψ₁ m T V₁ X₁ true false
    (fun q : Frequency => q.1) (fun q : Frequency => q.2.2) continuous_fst continuous_snd.snd
  have hc₂ := childEnergy_continuous p hg H₂ F Ψ₂ m T V₂ X₂ false true
    (fun q : Frequency => q.2.1) (fun q : Frequency => q.2.2) continuous_snd.fst continuous_snd.snd
  have hG : Continuous G := (Real.continuous_sqrt.comp hc₁).mul (Real.continuous_sqrt.comp hc₂)
  have hG0 : ∀ q, 0 ≤ G q := fun q => mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  let M := Real.sqrt (energyMagnitude p hg H₁ F Ψ₁ m T V₁ X₁ true false) *
    Real.sqrt (energyMagnitude p hg H₂ F Ψ₂ m T V₂ X₂ false true)
  have hM : ∀ q, G q ≤ M := by
    intro q
    dsimp [G, childGeometricMean, M]
    gcongr
    · exact childEnergy_le p hg H₁ F Ψ₁ m T V₁ X₁ true false q.1 q.2.2
    · exact childEnergy_le p hg H₂ F Ψ₂ m T V₂ X₂ false true q.2.1 q.2.2
  have hf : Continuous f := by
    unfold f globalSecondMode
    apply continuous_finsetSum
    intro x hx
    have hwx := hwc x hx
    have hc₁ := fixedRow_continuous p hg H₁ F Ψ₁ m (label x) (newRow (globalSecondTuple p x)) V₁ X₁ true
      (fun q : Frequency => q.1) (fun q : Frequency => q.2.2) continuous_fst continuous_snd.snd
    have hc₂ := fixedRow_continuous p hg H₂ F Ψ₂ m (label x) (-newRow (globalSecondTuple p x)) V₂ X₂ false
      (fun q : Frequency => q.2.1) (fun q : Frequency => q.2.2) continuous_snd.fst continuous_snd.snd
    exact (hwx.mul hc₁.star).mul hc₂
  have hpoint : ∀ q, ‖f q‖ ≤ (B * C * (lengthScale * Ideal.absNorm q0.1)^ε) * G q := by
    intro q
    have hh := hb s T q0 (w q) B lengthScale label F Ψ₁ Ψ₂ m
      (weightedSecondTest p H₁ V₁ X₁ q.1 q.2.2 true) (weightedSecondTest p H₂ V₂ X₂ q.2.1 q.2.2 false)
      hb0 hB hL hv htq hm ht hn (hw q) hl
    simpa only [f, G, childGeometricMean, childEnergy, mul_assoc] using hh
  exact triple_integral_bound b₁ b₂ b₃ f G hf hG hG0
    (B * C * (lengthScale * Ideal.absNorm q0.1)^ε) M (by positivity) hM hpoint

end SecondPassIntegration

namespace SecondPassIntegration
open Eisenstein SchwartzPlanePoisson SecondPassArithmetic SecondPassFiber JointLogSeparation MeasureTheory
open scoped Classical SchwartzMap FourierTransform
local instance : Finite Oˣ := cubic_units_finite
local instance : Fintype Oˣ := Fintype.ofFinite _
variable {ι : Type*} [DecidableEq ι]
  (p : ι → O) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hg : ∀ i, lambda ∉ Ideal.span {p i})
  (H₁ H₂ : Finset ι → ℂ)

def globalTupleSourceSum (s : Finset (GlobalSecondData ι)) (w : (GlobalSecondData ι) → ℂ) (label : (GlobalSecondData ι) → O)
    (F : Finset ι) (Ψ₁ Ψ₂ : O →* ℂ) (m : O) (A₁ A₂ W : 𝓢(ℝ, ℂ))
    (V : Fin 7 → ℝ → ℂ) (z ud ue uv kap : (GlobalSecondData ι) → ℝ) (X₁ X₂ R : ℝ) : ℂ :=
  ∑ x ∈ s, w x * postCommonSmoothPair p hg H₁ H₂ F Ψ₁ Ψ₂ m (label x)
    (newRow (globalSecondTuple p x)) (-newRow (globalSecondTuple p x)) A₁ A₂ W V (z x) (ud x) (ue x) (uv x) (kap x) X₁ X₂ R

theorem globalTupleSource_eq_globalIntegratedSecondMode
    (s : Finset (GlobalSecondData ι)) (w : (GlobalSecondData ι) → ℂ) (label : (GlobalSecondData ι) → O)
    (F : Finset ι) (Ψ₁ Ψ₂ : O →* ℂ) (m : O) (A₁ A₂ W b : 𝓢(ℝ, ℂ))
    (V : Fin 7 → ℝ → ℂ) (z ud ue uv kap : (GlobalSecondData ι) → ℝ) (X₁ X₂ R : ℝ)
    (hsep : ∀ x ∈ s,
      postCommonSmoothPair p hg H₁ H₂ F Ψ₁ Ψ₂ m (label x) (newRow (globalSecondTuple p x)) (-newRow (globalSecondTuple p x))
        A₁ A₂ W V (z x) (ud x) (ue x) (uv x) (kap x) X₁ X₂ R =
      separatedPostCommon p hg H₁ H₂ F Ψ₁ Ψ₂ m (label x) (newRow (globalSecondTuple p x)) (-newRow (globalSecondTuple p x))
        A₁ A₂ b V (z x) (ud x) (ue x) (uv x) (kap x) X₁ X₂) :
    globalTupleSourceSum p hg H₁ H₂ s w label F Ψ₁ Ψ₂ m A₁ A₂ W V z ud ue uv kap X₁ X₂ R =
      globalIntegratedSecondMode p hg H₁ H₂ (𝓕 A₁) (𝓕 A₂) b s
        (tupleOuterWeight V w z ud ue uv kap) label F Ψ₁ Ψ₂ m (V 5) (V 6) X₁ X₂ := by
  let Q : (GlobalSecondData ι) → Frequency → ℂ := fun x q =>
    tupleOuterWeight V w z ud ue uv kap q x *
      star (fixedChildRow p hg F Ψ₁ m
        (weightedSecondTest p H₁ (V 5) X₁ q.1 q.2.2 true) (label x) (newRow (globalSecondTuple p x))) *
      fixedChildRow p hg F Ψ₂ m
        (weightedSecondTest p H₂ (V 6) X₂ q.2.1 q.2.2 false) (label x) (-newRow (globalSecondTuple p x))
  let M : (GlobalSecondData ι) → ℝ := fun x =>
    (‖w x‖ * ‖outerWindow V (z x) (ud x) (ue x) (uv x) (kap x)‖) *
      rowMagnitude p hg H₁ F Ψ₁ m (label x) (newRow (globalSecondTuple p x)) (V 5) X₁ true *
      rowMagnitude p hg H₂ F Ψ₂ m (label x) (-newRow (globalSecondTuple p x)) (V 6) X₂ false
  have hc (x : (GlobalSecondData ι)) : Continuous (Q x) := by
    have hw := tupleOuterWeight_continuous V w z ud ue uv kap x
    have h₁ := fixedRow_continuous p hg H₁ F Ψ₁ m (label x) (newRow (globalSecondTuple p x)) (V 5) X₁ true
      (fun q : Frequency => q.1) (fun q : Frequency => q.2.2) continuous_fst continuous_snd.snd
    have h₂ := fixedRow_continuous p hg H₂ F Ψ₂ m (label x) (-newRow (globalSecondTuple p x)) (V 6) X₂ false
      (fun q : Frequency => q.2.1) (fun q : Frequency => q.2.2) continuous_snd.fst continuous_snd.snd
    exact (hw.mul h₁.star).mul h₂
  have hbound (x : (GlobalSecondData ι)) (q : Frequency) : ‖Q x q‖ ≤ M x := by
    dsimp only [Q, M]
    rw [norm_mul, norm_mul, norm_star, tupleOuterWeight_norm]
    have h₁ := fixedRow_norm_le p hg H₁ F Ψ₁ m (label x) (newRow (globalSecondTuple p x)) (V 5) X₁ q.1 q.2.2 true
    have h₂ := fixedRow_norm_le p hg H₂ F Ψ₂ m (label x) (-newRow (globalSecondTuple p x)) (V 6) X₂ q.2.1 q.2.2 false
    have hn₁ := rowMagnitude_nonneg p hg H₁ F Ψ₁ m (label x) (newRow (globalSecondTuple p x)) (V 5) X₁ true
    have hn₂ := rowMagnitude_nonneg p hg H₂ F Ψ₂ m (label x) (-newRow (globalSecondTuple p x)) (V 6) X₂ false
    gcongr
  calc
    _ = ∑ x ∈ s, ∫ t₁ : ℝ, ∫ t₂ : ℝ, ∫ t₃ : ℝ,
        tripleCoefficient (𝓕 A₁) (𝓕 A₂) b (t₁,t₂,t₃) * Q x (t₁,t₂,t₃) := by
      apply Finset.sum_congr rfl
      intro x hx
      rw [hsep x hx]
      unfold separatedPostCommon
      simp_rw [← integral_const_mul]
      apply integral_congr_ae
      filter_upwards [] with t₁
      apply integral_congr_ae
      filter_upwards [] with t₂
      apply integral_congr_ae
      filter_upwards [] with t₃
      dsimp [tripleCoefficient, Q, tupleOuterWeight]
      ring
    _ = ∫ t₁ : ℝ, ∫ t₂ : ℝ, ∫ t₃ : ℝ,
        tripleCoefficient (𝓕 A₁) (𝓕 A₂) b (t₁,t₂,t₃) * (∑ x ∈ s, Q x (t₁,t₂,t₃)) :=
      finite_triple_bounded_integral s (𝓕 A₁) (𝓕 A₂) b Q (fun x _ => hc x) M (fun x _ => hbound x)
    _ = _ := rfl

theorem globalTupleSource_transfer (ε : ℝ) (hε : 0 < ε)
    (A₁ A₂ W : 𝓢(ℝ, ℂ)) (V : Fin 7 → ℝ → ℂ) (M : Fin 7 → ℝ)
    (hM : ∀ j, 0 ≤ M j) (hV : ∀ j x, V j x ≠ 0 → |x| ≤ M j) (A J : ℕ) :
    ∃ Cₐ : ℝ, 0 < Cₐ ∧ ∃ Cₛ : ℝ, 0 ≤ Cₛ ∧ ∀ R : ℝ, 0 < R → ∃ b : 𝓢(ℝ, ℂ),
      (∀ t₁ t₂ t₃ : ℝ, (1 + R)^A * ‖(𝓕 A₁) t₁ * (𝓕 A₂) t₂ * b t₃‖ ≤
        Cₛ * firstLogDensity J t₁ *
          firstLogDensity J t₂ * firstLogDensity J t₃) ∧
      ∀ {ι : Type*} [DecidableEq ι]
      (p : ι → O) [∀ i, (Ideal.span {p i}).IsMaximal]
      (hinj : Function.Injective (fun i => Ideal.span {p i}))
      (hg : ∀ i, lambda ∉ Ideal.span {p i}), ∀ (H₁ H₂ : Finset ι → ℂ) (s : Finset (GlobalSecondData ι)) (T : Finset (Ideal O × O)) (q0 : Ideal O × Ideal O × Ideal O)
        (w : (GlobalSecondData ι) → ℂ) (B lengthScale : ℝ) (label : (GlobalSecondData ι) → O)
        (F : Finset ι) (Ψ₁ Ψ₂ : O →* ℂ) (m : O)
        (z ud ue uv kap : (GlobalSecondData ι) → ℝ) (X₁ X₂ : ℝ),
        q0.1 ≠ ⊥ → 0 ≤ B → 0 ≤ lengthScale →
        (∀ x ∈ s, GlobalSecondAdmissible x) →
        (∀ x ∈ s, globalSecondFixedTriple p x = q0) →
        (∀ x ∈ s, (newLabel (globalSecondTuple p x), newRow (globalSecondTuple p x)) ∈ T) →
        (∀ z ∈ T, z.1 ≠ ⊥) → (∀ z ∈ T, (Ideal.absNorm z.1 : ℝ) ≤ lengthScale) →
        (∀ x ∈ s, ‖w x‖ * ‖outerWindow V (z x) (ud x) (ue x) (uv x) (kap x)‖ ≤ B) →
        (∀ x ∈ s, Ideal.span {label x} = newLabel (globalSecondTuple p x)) →
        ‖globalTupleSourceSum p hg H₁ H₂ s w label F Ψ₁ Ψ₂ m A₁ A₂ W V z ud ue uv kap X₁ X₂ R‖ ≤
          (B * Cₐ * (lengthScale * Ideal.absNorm q0.1)^ε) *
          (∫ t₁ : ℝ, ∫ t₂ : ℝ, ∫ t₃ : ℝ,
            ‖tripleCoefficient (𝓕 A₁) (𝓕 A₂) b (t₁,t₂,t₃)‖ *
              childGeometricMean p hg H₁ H₂ F Ψ₁ Ψ₂ m T (V 5) (V 6) X₁ X₂ (t₁,t₂,t₃)) := by
  obtain ⟨Cₐ, hCₐ, htrans⟩ := globalSecond_integrated_mode_transfer ε hε
  obtain ⟨Cₛ, hCₛ, hsep⟩ := full_uniform_postCommonSmoothPair_fixed_tests A₁ A₂ W V M hM hV A J
  refine ⟨Cₐ, hCₐ, Cₛ, hCₛ, ?_⟩
  intro R hR
  obtain ⟨b, hpoint, hid⟩ := hsep R hR
  refine ⟨b, hpoint, ?_⟩
  intro ι _ p _ hinj hg H₁ H₂
  have htrans := htrans p hinj hg H₁ H₂
  have hid := hid p hg H₁ H₂
  intro s T q0 w B lengthScale label F Ψ₁ Ψ₂ m z ud ue uv kap X₁ X₂ hb0 hB hL hv htq hm ht hn hw hl
  have hsource := globalTupleSource_eq_globalIntegratedSecondMode p hg H₁ H₂ s w label F Ψ₁ Ψ₂ m A₁ A₂ W b
    V z ud ue uv kap X₁ X₂ R (fun x hx => hid F Ψ₁ Ψ₂ m (label x) (newRow (globalSecondTuple p x)) (-newRow (globalSecondTuple p x))
      (z x) (ud x) (ue x) (uv x) (kap x) X₁ X₂)
  rw [hsource]
  apply htrans s T q0 (tupleOuterWeight V w z ud ue uv kap) B lengthScale label F Ψ₁ Ψ₂ m
    (V 5) (V 6) X₁ X₂ (𝓕 A₁) (𝓕 A₂) b hb0 hB hL hv htq hm ht hn
  · intro q x hx
    rw [tupleOuterWeight_norm]
    exact hw x hx
  · intro x hx
    exact tupleOuterWeight_continuous V w z ud ue uv kap x
  · exact hl

end SecondPassIntegration

end GaloisForLFunctions.MetaplecticMobiusDescent.CubicEisenstein
