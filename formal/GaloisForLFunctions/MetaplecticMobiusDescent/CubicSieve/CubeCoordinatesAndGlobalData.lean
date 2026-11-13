/-
Cube coordinates and global second data adapted from OpenAI's formalization, Apache-2.0.
See LICENSE and NOTICE in the parent directory for source attribution.
-/
import GaloisForLFunctions.MetaplecticMobiusDescent.Mellin.JointLogSeparation

/-!
# Cube coordinates and global second data

Cube coordinates `CubeCoordinates` with their admissible bits, the global second-pass data and
expansion data. Fixed coefficients survive logarithmic twisting and uniform radial decay
survives the divisor-tuple transfer; Gauss blocks partition by cube exponents.
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

namespace SecondPassArithmetic
open Eisenstein SchwartzPlanePoisson JointLogSeparation MeasureTheory
open scoped Classical SchwartzMap FourierTransform

variable {ι : Type*} [DecidableEq ι] (p : ι → O)
  [∀ i, (Ideal.span {p i}).IsMaximal] (hg : ∀ i, lambda ∉ Ideal.span {p i})
  (H₁ H₂ : Finset ι → ℂ)

def postCommonSmoothPair (F : Finset ι) (Ψ₁ Ψ₂ : O →* ℂ) (m f y₁ y₂ : O)
    (A₁ A₂ W : 𝓢(ℝ, ℂ)) (V : Fin 7 → ℝ → ℂ)
    (z ud ue uv kap X₁ X₂ R : ℝ) : ℂ :=
  ∑ N ∈ F.powerset, ∑ M ∈ F.powerset,
    star (secondChildColumn p hg Ψ₁ m f y₁ H₁ N) *
      secondChildColumn p hg Ψ₂ m f y₂ H₂ M *
      (outerWindow V z ud ue uv kap * V 5 (columnLog p X₁ N) * V 6 (columnLog p X₂ M) *
        A₁ (z + columnLog p X₁ N) * A₂ (z + columnLog p X₂ M) *
        paperRadialFourier W
          (R * Real.exp (kap - ud - 2 * ue - 2 * uv - columnLog p X₁ N - columnLog p X₂ M)))

def fixedSecondTest (V : ℝ → ℂ) (X t s : ℝ) (negative : Bool) (N : Finset ι) : ℂ :=
  if negative then star (fixedColumnTest V (t-s) (columnLog p X N))
  else fixedColumnTest V (t-s) (columnLog p X N)

/-- Fixed arithmetic coefficients are retained under logarithmic twisting. -/
def weightedSecondTest (H : Finset ι → ℂ) (V : ℝ → ℂ)
    (X t s : ℝ) (negative : Bool) (N : Finset ι) : ℂ :=
  H N * fixedSecondTest p V X t s negative N

theorem postCommonSmoothPair_fixed_tests
    (F : Finset ι) (Ψ₁ Ψ₂ : O →* ℂ) (m f y₁ y₂ : O)
    (A₁ A₂ W : 𝓢(ℝ, ℂ)) (V : Fin 7 → ℝ → ℂ)
    (z ud ue uv kap X₁ X₂ R : ℝ) (b : 𝓢(ℝ, ℂ))
    (hsep : ∀ a a' : ℝ,
      outerWindow V z ud ue uv kap * V 5 a * V 6 a' * A₁ (z+a) * A₂ (z+a') *
        paperRadialFourier W (R * Real.exp (kap-ud-2*ue-2*uv-a-a')) =
      ∫ t₁ : ℝ, ∫ t₂ : ℝ, ∫ t₃ : ℝ,
        outerWindow V z ud ue uv kap * kernelLogPhase (t₁+t₂) z *
          kernelLogPhase t₃ (kap-ud-2*ue-2*uv) *
          fixedColumnTest (V 5) (t₁-t₃) a * fixedColumnTest (V 6) (t₂-t₃) a' *
          ((𝓕 A₁) t₁ * (𝓕 A₂) t₂ * b t₃)) :
    postCommonSmoothPair p hg H₁ H₂ F Ψ₁ Ψ₂ m f y₁ y₂ A₁ A₂ W V z ud ue uv kap X₁ X₂ R =
    ∫ t₁ : ℝ, ∫ t₂ : ℝ, ∫ t₃ : ℝ,
      (outerWindow V z ud ue uv kap * kernelLogPhase (t₁+t₂) z *
        kernelLogPhase t₃ (kap-ud-2*ue-2*uv) * ((𝓕 A₁) t₁ * (𝓕 A₂) t₂ * b t₃)) *
      star (fixedChildRow p hg F Ψ₁ m
        (weightedSecondTest p H₁ (V 5) X₁ t₁ t₃ true) f y₁) *
      fixedChildRow p hg F Ψ₂ m
        (weightedSecondTest p H₂ (V 6) X₂ t₂ t₃ false) f y₂ := by
  let B₁ := fun N => secondChildColumn p hg Ψ₁ m f y₁ H₁ N
  let B₂ := fun M => secondChildColumn p hg Ψ₂ m f y₂ H₂ M
  let q := fun (i : Finset ι × Finset ι) =>
    outerWindow V z ud ue uv kap * V 5 (columnLog p X₁ i.1) * V 6 (columnLog p X₂ i.2) *
      star (B₁ i.1) * B₂ i.2
  let K := fun (i : Finset ι × Finset ι) (t₁ t₂ t₃ : ℝ) =>
    (kernelLogPhase t₁ (z + columnLog p X₁ i.1) * (𝓕 A₁) t₁) *
      ((kernelLogPhase t₂ (z + columnLog p X₂ i.2) * (𝓕 A₂) t₂) *
        ((kernelLogPhase t₃ (kap-ud-2*ue-2*uv-columnLog p X₁ i.1-columnLog p X₂ i.2) * b t₃) * q i))
  have hterm (N M : Finset ι) : star (B₁ N) * B₂ M *
      (outerWindow V z ud ue uv kap * V 5 (columnLog p X₁ N) * V 6 (columnLog p X₂ M) *
        A₁ (z+columnLog p X₁ N) * A₂ (z+columnLog p X₂ M) *
        paperRadialFourier W
          (R * Real.exp (kap-ud-2*ue-2*uv-columnLog p X₁ N-columnLog p X₂ M))) =
      ∫ t₁ : ℝ, ∫ t₂ : ℝ, ∫ t₃ : ℝ, K (N,M) t₁ t₂ t₃ := by
    rw [hsep]
    simp_rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [] with t₁
    apply integral_congr_ae
    filter_upwards [] with t₂
    apply integral_congr_ae
    filter_upwards [] with t₃
    have hphase := JointLogSeparation.seven_phase_factor z ud ue uv kap
      (columnLog p X₁ N) (columnLog p X₂ M) t₁ t₂ t₃
    dsimp only [K, q]
    unfold fixedColumnTest
    calc
      _ = (outerWindow V z ud ue uv kap * V 5 (columnLog p X₁ N) * V 6 (columnLog p X₂ M) *
        star (B₁ N) * B₂ M) *
        (kernelLogPhase (t₁+t₂) z * kernelLogPhase t₃ (kap-ud-2*ue-2*uv) *
          kernelLogPhase (t₁-t₃) (columnLog p X₁ N) * kernelLogPhase (t₂-t₃) (columnLog p X₂ M)) *
        ((𝓕 A₁) t₁ * (𝓕 A₂) t₂ * b t₃) := by ring
      _ = _ := by rw [← hphase]; ring
  calc
    _ = ∑ i ∈ F.powerset ×ˢ F.powerset, ∫ t₁ : ℝ, ∫ t₂ : ℝ, ∫ t₃ : ℝ, K i t₁ t₂ t₃ := by
      simp only [postCommonSmoothPair, Finset.sum_product]
      exact Finset.sum_congr rfl (fun N _ => Finset.sum_congr rfl (fun M _ => hterm N M))
    _ = ∫ t₁ : ℝ, ∫ t₂ : ℝ, ∫ t₃ : ℝ, ∑ i ∈ F.powerset ×ˢ F.powerset, K i t₁ t₂ t₃ :=
      JointLogSeparation.finite_triple_phase_integral _ (𝓕 A₁) (𝓕 A₂) b _ _ _ q
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [] with t₁
      apply integral_congr_ae
      filter_upwards [] with t₂
      apply integral_congr_ae
      filter_upwards [] with t₃
      simp only [Finset.sum_product]
      have hcols : (∑ N ∈ F.powerset, ∑ M ∈ F.powerset, K (N,M) t₁ t₂ t₃) =
          (outerWindow V z ud ue uv kap * kernelLogPhase (t₁+t₂) z *
            kernelLogPhase t₃ (kap-ud-2*ue-2*uv) * ((𝓕 A₁) t₁ * (𝓕 A₂) t₂ * b t₃)) *
          (∑ N ∈ F.powerset, star (B₁ N) * fixedColumnTest (V 5) (t₁-t₃) (columnLog p X₁ N)) *
          (∑ M ∈ F.powerset, B₂ M * fixedColumnTest (V 6) (t₂-t₃) (columnLog p X₂ M)) := by
        simp only [Finset.mul_sum, Finset.sum_mul]
        conv_rhs => rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro N hN
        apply Finset.sum_congr rfl
        intro M hM
        have hphase := JointLogSeparation.seven_phase_factor z ud ue uv kap
          (columnLog p X₁ N) (columnLog p X₂ M) t₁ t₂ t₃
        dsimp only [K, q]
        unfold fixedColumnTest
        calc
          _ = (outerWindow V z ud ue uv kap * V 5 (columnLog p X₁ N) * V 6 (columnLog p X₂ M) *
            star (B₁ N) * B₂ M) *
            (kernelLogPhase t₁ (z+columnLog p X₁ N) * kernelLogPhase t₂ (z+columnLog p X₂ M) *
              kernelLogPhase t₃ (kap-ud-2*ue-2*uv-columnLog p X₁ N-columnLog p X₂ M)) *
            ((𝓕 A₁) t₁ * (𝓕 A₂) t₂ * b t₃) := by ring
          _ = _ := by rw [hphase]; ring
      rw [hcols]
      have hleft : (∑ N ∈ F.powerset, star (B₁ N) *
          fixedColumnTest (V 5) (t₁-t₃) (columnLog p X₁ N)) =
          star (fixedChildRow p hg F Ψ₁ m
            (weightedSecondTest p H₁ (V 5) X₁ t₁ t₃ true) f y₁) := by
        simp only [fixedChildRow, star_sum]
        apply Finset.sum_congr rfl
        intro N hN
        simp only [secondChildColumn, weightedSecondTest, fixedSecondTest, ite_true, B₁,
          star_mul, star_star, mul_one]
        ring
      have hright : (∑ N ∈ F.powerset, B₂ N *
          fixedColumnTest (V 6) (t₂-t₃) (columnLog p X₂ N)) =
          fixedChildRow p hg F Ψ₂ m
            (weightedSecondTest p H₂ (V 6) X₂ t₂ t₃ false) f y₂ := by
        apply Finset.sum_congr rfl
        intro N hN
        simp only [secondChildColumn, weightedSecondTest, fixedSecondTest, Bool.false_eq_true, ite_false, B₂, mul_one]
        ring
      rw [hleft, hright]

def separatedPostCommon (F : Finset ι) (Ψ₁ Ψ₂ : O →* ℂ) (m f y₁ y₂ : O)
    (A₁ A₂ b : 𝓢(ℝ, ℂ)) (V : Fin 7 → ℝ → ℂ)
    (z ud ue uv kap X₁ X₂ : ℝ) : ℂ :=
  ∫ t₁ : ℝ, ∫ t₂ : ℝ, ∫ t₃ : ℝ,
    (outerWindow V z ud ue uv kap * kernelLogPhase (t₁+t₂) z *
      kernelLogPhase t₃ (kap-ud-2*ue-2*uv) * ((𝓕 A₁) t₁ * (𝓕 A₂) t₂ * b t₃)) *
    star (fixedChildRow p hg F Ψ₁ m
      (weightedSecondTest p H₁ (V 5) X₁ t₁ t₃ true) f y₁) *
    fixedChildRow p hg F Ψ₂ m
      (weightedSecondTest p H₂ (V 6) X₂ t₂ t₃ false) f y₂

theorem postCommonSmoothPair_uniform_fixed_tests
    (A₁ A₂ W : 𝓢(ℝ, ℂ)) (V : Fin 7 → ℝ → ℂ) (M : Fin 7 → ℝ)
    (hM : ∀ j, 0 ≤ M j) (hV : ∀ j x, V j x ≠ 0 → |x| ≤ M j) (A J : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ R : ℝ, 0 < R → ∃ b : 𝓢(ℝ, ℂ),
      (∀ t₁ t₂ t₃ : ℝ, (1+R)^A * ‖(𝓕 A₁) t₁ * (𝓕 A₂) t₂ * b t₃‖ ≤
        C * firstLogDensity J t₁ * firstLogDensity J t₂ * firstLogDensity J t₃) ∧
      ∀ (F : Finset ι) (Ψ₁ Ψ₂ : O →* ℂ) (m f y₁ y₂ : O)
        (z ud ue uv kap X₁ X₂ : ℝ),
        postCommonSmoothPair p hg H₁ H₂ F Ψ₁ Ψ₂ m f y₁ y₂ A₁ A₂ W V
          z ud ue uv kap X₁ X₂ R =
        separatedPostCommon p hg H₁ H₂ F Ψ₁ Ψ₂ m f y₁ y₂ A₁ A₂ b V
          z ud ue uv kap X₁ X₂ := by
  obtain ⟨C, hC, hsep⟩ := JointLogSeparation.seven_kernel_separation A₁ A₂ W V M hM hV A J
  refine ⟨C, hC, ?_⟩
  intro R hR
  obtain ⟨b, hb, hpoint, hint⟩ := hsep R hR
  refine ⟨b, hpoint, ?_⟩
  intro F Ψ₁ Ψ₂ m f y₁ y₂ z ud ue uv kap X₁ X₂
  exact postCommonSmoothPair_fixed_tests p hg H₁ H₂ F Ψ₁ Ψ₂ m f y₁ y₂ A₁ A₂ W V
    z ud ue uv kap X₁ X₂ R b (hb z ud ue uv kap)

end SecondPassArithmetic

namespace SecondPassIntegration
open Eisenstein SchwartzPlanePoisson SecondPassArithmetic SecondPassFiber JointLogSeparation MeasureTheory
open scoped Classical SchwartzMap FourierTransform
local instance : Finite Oˣ := cubic_units_finite
local instance : Fintype Oˣ := Fintype.ofFinite _

variable {ι : Type*} [DecidableEq ι] (p : ι → O)
  [∀ i, (Ideal.span {p i}).IsMaximal] (hg : ∀ i, lambda ∉ Ideal.span {p i})
  (H₀ : Finset ι → ℂ)

omit [DecidableEq ι] [∀ (i : ι), (Ideal.span {p i}).IsMaximal] in
lemma fixedTest_continuous (V : ℝ → ℂ) (X : ℝ) (negative : Bool) (N : Finset ι)
    (τ σ : Frequency → ℝ) (hτ : Continuous τ) (hσ : Continuous σ) :
    Continuous (fun t => weightedSecondTest p H₀ V X (τ t) (σ t) negative N) := by
  have hh := (kernelLogPhase_continuous_left (columnLog p X N)).comp (hτ.sub hσ)
  cases negative <;> simp only [weightedSecondTest, fixedSecondTest, Bool.false_eq_true, ite_false, ite_true,
    fixedColumnTest] <;> fun_prop

lemma fixedColumn_norm_frequency (Ψ : O →* ℂ) (m f y : O) (V : ℝ → ℂ) (X a b : ℝ)
    (negative : Bool) (N : Finset ι) :
    ‖secondChildColumn p hg Ψ m f y (weightedSecondTest p H₀ V X a b negative) N‖ =
    ‖secondChildColumn p hg Ψ m f y (weightedSecondTest p H₀ V X 0 0 negative) N‖ := by
  cases negative <;> simp only [secondChildColumn, weightedSecondTest, fixedSecondTest, Bool.false_eq_true, ite_false,
    ite_true, fixedColumnTest, norm_mul, norm_star, kernelLogPhase_norm]

lemma fixedRow_continuous (F : Finset ι) (Ψ : O →* ℂ) (m f y : O) (V : ℝ → ℂ) (X : ℝ)
    (negative : Bool) (τ σ : Frequency → ℝ) (hτ : Continuous τ) (hσ : Continuous σ) :
    Continuous (fun t => fixedChildRow p hg F Ψ m
      (weightedSecondTest p H₀ V X (τ t) (σ t) negative) f y) := by
  unfold fixedChildRow
  apply continuous_finsetSum
  intro N hN
  have hh := fixedTest_continuous p H₀ V X negative N τ σ hτ hσ
  unfold secondChildColumn
  fun_prop

def rowMagnitude (F : Finset ι) (Ψ : O →* ℂ) (m f y : O) (V : ℝ → ℂ) (X : ℝ)
    (negative : Bool) : ℝ :=
  ∑ N ∈ F.powerset,
    ‖secondChildColumn p hg Ψ m f y (weightedSecondTest p H₀ V X 0 0 negative) N‖

lemma rowMagnitude_nonneg (F : Finset ι) (Ψ : O →* ℂ) (m f y : O) (V : ℝ → ℂ) (X : ℝ)
    (negative : Bool) : 0 ≤ rowMagnitude p hg H₀ F Ψ m f y V X negative := by
  unfold rowMagnitude
  positivity

lemma fixedRow_norm_le (F : Finset ι) (Ψ : O →* ℂ) (m f y : O) (V : ℝ → ℂ) (X a b : ℝ)
    (negative : Bool) :
    ‖fixedChildRow p hg F Ψ m (weightedSecondTest p H₀ V X a b negative) f y‖ ≤
      rowMagnitude p hg H₀ F Ψ m f y V X negative := by
  unfold fixedChildRow rowMagnitude
  apply (norm_sum_le _ _).trans_eq
  exact Finset.sum_congr rfl (fun N hN => fixedColumn_norm_frequency p hg H₀ Ψ m f y V X a b negative N)

def childEnergy (F : Finset ι) (Ψ : O →* ℂ) (m : O) (T : Finset (Ideal O × O))
    (V : ℝ → ℂ) (X : ℝ) (testNegative rowNegative : Bool) (a b : ℝ) : ℝ :=
  ∑ u : Oˣ, ∑ z ∈ T,
    ‖idealChildRow p hg F Ψ m (weightedSecondTest p H₀ V X a b testNegative) rowNegative u z‖ ^ 2

def energyMagnitude (F : Finset ι) (Ψ : O →* ℂ) (m : O) (T : Finset (Ideal O × O))
    (V : ℝ → ℂ) (X : ℝ) (testNegative rowNegative : Bool) : ℝ :=
  ∑ u : Oˣ, ∑ z ∈ T,
    (rowMagnitude p hg H₀ F Ψ m ((u : O) * cubicIdealGenerator z.1)
      (if rowNegative then -z.2 else z.2) V X testNegative) ^ 2

lemma childEnergy_nonneg (F : Finset ι) (Ψ : O →* ℂ) (m : O) (T : Finset (Ideal O × O))
    (V : ℝ → ℂ) (X : ℝ) (testNegative rowNegative : Bool) (a b : ℝ) :
    0 ≤ childEnergy p hg H₀ F Ψ m T V X testNegative rowNegative a b := by
  unfold childEnergy
  positivity

lemma childEnergy_le (F : Finset ι) (Ψ : O →* ℂ) (m : O) (T : Finset (Ideal O × O))
    (V : ℝ → ℂ) (X : ℝ) (testNegative rowNegative : Bool) (a b : ℝ) :
    childEnergy p hg H₀ F Ψ m T V X testNegative rowNegative a b ≤
      energyMagnitude p hg H₀ F Ψ m T V X testNegative rowNegative := by
  unfold childEnergy energyMagnitude idealChildRow
  apply Finset.sum_le_sum
  intro u hu
  apply Finset.sum_le_sum
  intro z hz
  exact pow_le_pow_left₀ (norm_nonneg _) (fixedRow_norm_le p hg H₀ F Ψ m _ _ V X a b testNegative) 2

lemma childEnergy_continuous (F : Finset ι) (Ψ : O →* ℂ) (m : O) (T : Finset (Ideal O × O))
    (V : ℝ → ℂ) (X : ℝ) (testNegative rowNegative : Bool)
    (τ σ : Frequency → ℝ) (hτ : Continuous τ) (hσ : Continuous σ) :
    Continuous (fun t => childEnergy p hg H₀ F Ψ m T V X testNegative rowNegative (τ t) (σ t)) := by
  unfold childEnergy
  apply continuous_finsetSum
  intro u hu
  apply continuous_finsetSum
  intro z hz
  unfold idealChildRow
  exact (fixedRow_continuous p hg H₀ F Ψ m _ _ V X testNegative τ σ hτ hσ).norm.pow 2
variable (H₁ H₂ : Finset ι → ℂ)

def integratedSecondMode (b₁ b₂ b₃ : 𝓢(ℝ, ℂ))
    (s : Finset OldTuple) (w : Frequency → OldTuple → ℂ) (label : OldTuple → O)
    (F : Finset ι) (Ψ₁ Ψ₂ : O →* ℂ) (m : O) (V₁ V₂ : ℝ → ℂ) (X₁ X₂ : ℝ) : ℂ :=
  ∫ t₁ : ℝ, ∫ t₂ : ℝ, ∫ t₃ : ℝ, tripleCoefficient b₁ b₂ b₃ (t₁,t₂,t₃) *
    fixedSecondMode p hg s (w (t₁,t₂,t₃)) label F Ψ₁ Ψ₂ m
      (weightedSecondTest p H₁ V₁ X₁ t₁ t₃ true) (weightedSecondTest p H₂ V₂ X₂ t₂ t₃ false)

def childGeometricMean (F : Finset ι) (Ψ₁ Ψ₂ : O →* ℂ) (m : O) (T : Finset (Ideal O × O))
    (V₁ V₂ : ℝ → ℂ) (X₁ X₂ : ℝ) (q : Frequency) : ℝ :=
  Real.sqrt (childEnergy p hg H₁ F Ψ₁ m T V₁ X₁ true false q.1 q.2.2) *
    Real.sqrt (childEnergy p hg H₂ F Ψ₂ m T V₂ X₂ false true q.2.1 q.2.2)


end SecondPassIntegration

namespace SecondPassIntegration
open Eisenstein SchwartzPlanePoisson SecondPassArithmetic JointLogSeparation MeasureTheory
open scoped Classical SchwartzMap FourierTransform
local instance : Finite Oˣ := cubic_units_finite
local instance : Fintype Oˣ := Fintype.ofFinite _

open SecondPassFiber

theorem full_uniform_integrated_fixed_second_mode_transfer (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ {ι : Type*} [DecidableEq ι]
      (p : ι → O) [∀ i, (Ideal.span {p i}).IsMaximal]
      (hg : ∀ i, lambda ∉ Ideal.span {p i}), ∀ (H₁ H₂ : Finset ι → ℂ) (s : Finset OldTuple) (T : Finset (Ideal O × O))
      (b0 : Ideal O) (w : Frequency → OldTuple → ℂ) (B lengthScale : ℝ) (label : OldTuple → O)
      (F : Finset ι) (Ψ₁ Ψ₂ : O →* ℂ) (m : O) (V₁ V₂ : ℝ → ℂ) (X₁ X₂ : ℝ)
      (b₁ b₂ b₃ : 𝓢(ℝ, ℂ)),
      b0 ≠ ⊥ → 0 ≤ B → 0 ≤ lengthScale →
      (∀ x ∈ s, Valid x (newLabel x) b0 (newRow x)) →
      (∀ x ∈ s, (newLabel x, newRow x) ∈ T) →
      (∀ z ∈ T, z.1 ≠ ⊥) → (∀ z ∈ T, (Ideal.absNorm z.1 : ℝ) ≤ lengthScale) →
      (∀ q, ∀ x ∈ s, ‖w q x‖ ≤ B) → (∀ x ∈ s, Continuous (fun q => w q x)) →
      (∀ x ∈ s, Ideal.span {label x} = newLabel x) →
      ‖integratedSecondMode p hg H₁ H₂ b₁ b₂ b₃ s w label F Ψ₁ Ψ₂ m V₁ V₂ X₁ X₂‖ ≤
        (B * C * (lengthScale * Ideal.absNorm b0)^ε) *
        (∫ t₁ : ℝ, ∫ t₂ : ℝ, ∫ t₃ : ℝ,
          ‖tripleCoefficient b₁ b₂ b₃ (t₁,t₂,t₃)‖ *
            childGeometricMean p hg H₁ H₂ F Ψ₁ Ψ₂ m T V₁ V₂ X₁ X₂ (t₁,t₂,t₃)) := by
  obtain ⟨C, hC, hb⟩ := full_uniform_fixed_second_mode_transfer ε hε
  refine ⟨C, hC, ?_⟩
  intro ι _ p _ hg
  have hb := hb p hg
  intro H₁ H₂ s T b0 w B lengthScale label F Ψ₁ Ψ₂ m V₁ V₂ X₁ X₂ b₁ b₂ b₃ hb0 hB hL hv hm ht hn hw hwc hl
  let f : Frequency → ℂ := fun q => fixedSecondMode p hg s (w q) label F Ψ₁ Ψ₂ m
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
    unfold f fixedSecondMode
    apply continuous_finsetSum
    intro x hx
    have hwx := hwc x hx
    have hc₁ := fixedRow_continuous p hg H₁ F Ψ₁ m (label x) (newRow x) V₁ X₁ true
      (fun q : Frequency => q.1) (fun q : Frequency => q.2.2) continuous_fst continuous_snd.snd
    have hc₂ := fixedRow_continuous p hg H₂ F Ψ₂ m (label x) (-newRow x) V₂ X₂ false
      (fun q : Frequency => q.2.1) (fun q : Frequency => q.2.2) continuous_snd.fst continuous_snd.snd
    exact (hwx.mul hc₁.star).mul hc₂
  have hpoint : ∀ q, ‖f q‖ ≤ (B * C * (lengthScale * Ideal.absNorm b0)^ε) * G q := by
    intro q
    have hh := hb s T b0 (w q) B lengthScale label F Ψ₁ Ψ₂ m
      (weightedSecondTest p H₁ V₁ X₁ q.1 q.2.2 true) (weightedSecondTest p H₂ V₂ X₂ q.2.1 q.2.2 false)
      hb0 hB hL hv hm ht hn (hw q) hl
    simpa only [f, G, childGeometricMean, childEnergy, mul_assoc] using hh
  exact triple_integral_bound b₁ b₂ b₃ f G hf hG hG0
    (B * C * (lengthScale * Ideal.absNorm b0)^ε) M (by positivity) hM hpoint

end SecondPassIntegration

namespace SecondPassIntegration

section
open Eisenstein SchwartzPlanePoisson SecondPassArithmetic JointLogSeparation MeasureTheory
open scoped Classical SchwartzMap FourierTransform
open SecondPassFiber (OldTuple newLabel newRow Valid)

def tupleOuterWeight {α : Type*} (V : Fin 7 → ℝ → ℂ) (w : α → ℂ)
    (z ud ue uv kap : α → ℝ) (q : Frequency) (x : α) : ℂ :=
  w x * outerWindow V (z x) (ud x) (ue x) (uv x) (kap x) *
    kernelLogPhase (q.1 + q.2.1) (z x) * kernelLogPhase q.2.2 (kap x - ud x - 2 * ue x - 2 * uv x)

lemma tupleOuterWeight_continuous {α : Type*} (V : Fin 7 → ℝ → ℂ) (w : α → ℂ)
    (z ud ue uv kap : α → ℝ) (x : α) :
    Continuous (fun q => tupleOuterWeight V w z ud ue uv kap q x) := by
  have h₁ : Continuous (fun q : Frequency => kernelLogPhase (q.1 + q.2.1) (z x)) :=
    (kernelLogPhase_continuous_left (z x)).comp
    (continuous_fst.add continuous_snd.fst)
  have h₂ : Continuous (fun q : Frequency => kernelLogPhase q.2.2 (kap x - ud x - 2 * ue x - 2 * uv x)) :=
    (kernelLogPhase_continuous_left (kap x - ud x - 2 * ue x - 2 * uv x)).comp
    continuous_snd.snd
  unfold tupleOuterWeight
  fun_prop

lemma tupleOuterWeight_norm {α : Type*} (V : Fin 7 → ℝ → ℂ) (w : α → ℂ)
    (z ud ue uv kap : α → ℝ) (q : Frequency) (x : α) :
    ‖tupleOuterWeight V w z ud ue uv kap q x‖ =
      ‖w x‖ * ‖outerWindow V (z x) (ud x) (ue x) (uv x) (kap x)‖ := by
  simp only [tupleOuterWeight, norm_mul, kernelLogPhase_norm, mul_one]

variable {ι : Type*} [DecidableEq ι]
  (p : ι → O) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hg : ∀ i, lambda ∉ Ideal.span {p i})
  (H₁ H₂ : Finset ι → ℂ)

def tupleSourceSum (s : Finset OldTuple) (w : OldTuple → ℂ) (label : OldTuple → O)
    (F : Finset ι) (Ψ₁ Ψ₂ : O →* ℂ) (m : O) (A₁ A₂ W : 𝓢(ℝ, ℂ))
    (V : Fin 7 → ℝ → ℂ) (z ud ue uv kap : OldTuple → ℝ) (X₁ X₂ R : ℝ) : ℂ :=
  ∑ x ∈ s, w x * postCommonSmoothPair p hg H₁ H₂ F Ψ₁ Ψ₂ m (label x)
    (newRow x) (-newRow x) A₁ A₂ W V (z x) (ud x) (ue x) (uv x) (kap x) X₁ X₂ R

theorem tupleSource_eq_integratedSecondMode
    (s : Finset OldTuple) (w : OldTuple → ℂ) (label : OldTuple → O)
    (F : Finset ι) (Ψ₁ Ψ₂ : O →* ℂ) (m : O) (A₁ A₂ W b : 𝓢(ℝ, ℂ))
    (V : Fin 7 → ℝ → ℂ) (z ud ue uv kap : OldTuple → ℝ) (X₁ X₂ R : ℝ)
    (hsep : ∀ x ∈ s,
      postCommonSmoothPair p hg H₁ H₂ F Ψ₁ Ψ₂ m (label x) (newRow x) (-newRow x)
        A₁ A₂ W V (z x) (ud x) (ue x) (uv x) (kap x) X₁ X₂ R =
      separatedPostCommon p hg H₁ H₂ F Ψ₁ Ψ₂ m (label x) (newRow x) (-newRow x)
        A₁ A₂ b V (z x) (ud x) (ue x) (uv x) (kap x) X₁ X₂) :
    tupleSourceSum p hg H₁ H₂ s w label F Ψ₁ Ψ₂ m A₁ A₂ W V z ud ue uv kap X₁ X₂ R =
      integratedSecondMode p hg H₁ H₂ (𝓕 A₁) (𝓕 A₂) b s
        (tupleOuterWeight V w z ud ue uv kap) label F Ψ₁ Ψ₂ m (V 5) (V 6) X₁ X₂ := by
  let Q : OldTuple → Frequency → ℂ := fun x q =>
    tupleOuterWeight V w z ud ue uv kap q x *
      star (fixedChildRow p hg F Ψ₁ m
        (weightedSecondTest p H₁ (V 5) X₁ q.1 q.2.2 true) (label x) (newRow x)) *
      fixedChildRow p hg F Ψ₂ m
        (weightedSecondTest p H₂ (V 6) X₂ q.2.1 q.2.2 false) (label x) (-newRow x)
  let M : OldTuple → ℝ := fun x =>
    (‖w x‖ * ‖outerWindow V (z x) (ud x) (ue x) (uv x) (kap x)‖) *
      rowMagnitude p hg H₁ F Ψ₁ m (label x) (newRow x) (V 5) X₁ true *
      rowMagnitude p hg H₂ F Ψ₂ m (label x) (-newRow x) (V 6) X₂ false
  have hc (x : OldTuple) : Continuous (Q x) := by
    have hw := tupleOuterWeight_continuous V w z ud ue uv kap x
    have h₁ := fixedRow_continuous p hg H₁ F Ψ₁ m (label x) (newRow x) (V 5) X₁ true
      (fun q : Frequency => q.1) (fun q : Frequency => q.2.2) continuous_fst continuous_snd.snd
    have h₂ := fixedRow_continuous p hg H₂ F Ψ₂ m (label x) (-newRow x) (V 6) X₂ false
      (fun q : Frequency => q.2.1) (fun q : Frequency => q.2.2) continuous_snd.fst continuous_snd.snd
    exact (hw.mul h₁.star).mul h₂
  have hbound (x : OldTuple) (q : Frequency) : ‖Q x q‖ ≤ M x := by
    dsimp only [Q, M]
    rw [norm_mul, norm_mul, norm_star, tupleOuterWeight_norm]
    have h₁ := fixedRow_norm_le p hg H₁ F Ψ₁ m (label x) (newRow x) (V 5) X₁ q.1 q.2.2 true
    have h₂ := fixedRow_norm_le p hg H₂ F Ψ₂ m (label x) (-newRow x) (V 6) X₂ q.2.1 q.2.2 false
    have hn₁ := rowMagnitude_nonneg p hg H₁ F Ψ₁ m (label x) (newRow x) (V 5) X₁ true
    have hn₂ := rowMagnitude_nonneg p hg H₂ F Ψ₂ m (label x) (-newRow x) (V 6) X₂ false
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

end

end SecondPassIntegration

namespace SecondPassArithmetic
open Eisenstein SchwartzPlanePoisson MeasureTheory
open scoped Classical SchwartzMap FourierTransform

theorem full_uniform_postCommonSmoothPair_fixed_tests
    (A₁ A₂ W : 𝓢(ℝ, ℂ)) (V : Fin 7 → ℝ → ℂ) (M : Fin 7 → ℝ)
    (hM : ∀ j, 0 ≤ M j) (hV : ∀ j x, V j x ≠ 0 → |x| ≤ M j) (A J : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ R : ℝ, 0 < R → ∃ b : 𝓢(ℝ, ℂ),
      (∀ t₁ t₂ t₃ : ℝ, (1+R)^A * ‖(𝓕 A₁) t₁ * (𝓕 A₂) t₂ * b t₃‖ ≤
        C * firstLogDensity J t₁ * firstLogDensity J t₂ * firstLogDensity J t₃) ∧
      ∀ {ι : Type*} [DecidableEq ι]
      (p : ι → O) [∀ i, (Ideal.span {p i}).IsMaximal]
      (hg : ∀ i, lambda ∉ Ideal.span {p i}), ∀ (H₁ H₂ : Finset ι → ℂ) (F : Finset ι) (Ψ₁ Ψ₂ : O →* ℂ) (m f y₁ y₂ : O)
        (z ud ue uv kap X₁ X₂ : ℝ),
        postCommonSmoothPair p hg H₁ H₂ F Ψ₁ Ψ₂ m f y₁ y₂ A₁ A₂ W V
          z ud ue uv kap X₁ X₂ R =
        separatedPostCommon p hg H₁ H₂ F Ψ₁ Ψ₂ m f y₁ y₂ A₁ A₂ b V
          z ud ue uv kap X₁ X₂ := by
  obtain ⟨C, hC, hsep⟩ := JointLogSeparation.seven_kernel_separation A₁ A₂ W V M hM hV A J
  refine ⟨C, hC, ?_⟩
  intro R hR
  obtain ⟨b, hb, hpoint, hint⟩ := hsep R hR
  refine ⟨b, hpoint, ?_⟩
  intro ι _ p _ hg H₁ H₂
    F Ψ₁ Ψ₂ m f y₁ y₂ z ud ue uv kap X₁ X₂
  exact postCommonSmoothPair_fixed_tests p hg H₁ H₂ F Ψ₁ Ψ₂ m f y₁ y₂ A₁ A₂ W V
    z ud ue uv kap X₁ X₂ R b (hb z ud ue uv kap)

end SecondPassArithmetic

namespace SecondPassIntegration
open Eisenstein SchwartzPlanePoisson SecondPassArithmetic JointLogSeparation MeasureTheory
open scoped Classical SchwartzMap FourierTransform
local instance : Finite Oˣ := cubic_units_finite
local instance : Fintype Oˣ := Fintype.ofFinite _
open SecondPassFiber (OldTuple newLabel newRow Valid)

theorem full_uniform_tupleSource_transfer (ε : ℝ) (hε : 0 < ε)
    (A₁ A₂ W : 𝓢(ℝ, ℂ)) (V : Fin 7 → ℝ → ℂ) (M : Fin 7 → ℝ)
    (hM : ∀ j, 0 ≤ M j) (hV : ∀ j x, V j x ≠ 0 → |x| ≤ M j) (A J : ℕ) :
    ∃ Cₐ : ℝ, 0 < Cₐ ∧ ∃ Cₛ : ℝ, 0 ≤ Cₛ ∧ ∀ R : ℝ, 0 < R → ∃ b : 𝓢(ℝ, ℂ),
      (∀ t₁ t₂ t₃ : ℝ, (1 + R)^A * ‖(𝓕 A₁) t₁ * (𝓕 A₂) t₂ * b t₃‖ ≤
        Cₛ * firstLogDensity J t₁ *
          firstLogDensity J t₂ * firstLogDensity J t₃) ∧
      ∀ {ι : Type*} [DecidableEq ι]
      (p : ι → O) [∀ i, (Ideal.span {p i}).IsMaximal]
      (hg : ∀ i, lambda ∉ Ideal.span {p i}), ∀ (H₁ H₂ : Finset ι → ℂ) (s : Finset OldTuple) (T : Finset (Ideal O × O)) (b0 : Ideal O)
        (w : OldTuple → ℂ) (B lengthScale : ℝ) (label : OldTuple → O)
        (F : Finset ι) (Ψ₁ Ψ₂ : O →* ℂ) (m : O)
        (z ud ue uv kap : OldTuple → ℝ) (X₁ X₂ : ℝ),
        b0 ≠ ⊥ → 0 ≤ B → 0 ≤ lengthScale →
        (∀ x ∈ s, Valid x (newLabel x) b0 (newRow x)) →
        (∀ x ∈ s, (newLabel x, newRow x) ∈ T) →
        (∀ z ∈ T, z.1 ≠ ⊥) → (∀ z ∈ T, (Ideal.absNorm z.1 : ℝ) ≤ lengthScale) →
        (∀ x ∈ s, ‖w x‖ * ‖outerWindow V (z x) (ud x) (ue x) (uv x) (kap x)‖ ≤ B) →
        (∀ x ∈ s, Ideal.span {label x} = newLabel x) →
        ‖tupleSourceSum p hg H₁ H₂ s w label F Ψ₁ Ψ₂ m A₁ A₂ W V z ud ue uv kap X₁ X₂ R‖ ≤
          (B * Cₐ * (lengthScale * Ideal.absNorm b0)^ε) *
          (∫ t₁ : ℝ, ∫ t₂ : ℝ, ∫ t₃ : ℝ,
            ‖tripleCoefficient (𝓕 A₁) (𝓕 A₂) b (t₁,t₂,t₃)‖ *
              childGeometricMean p hg H₁ H₂ F Ψ₁ Ψ₂ m T (V 5) (V 6) X₁ X₂ (t₁,t₂,t₃)) := by
  obtain ⟨Cₐ, hCₐ, htrans⟩ := full_uniform_integrated_fixed_second_mode_transfer ε hε
  obtain ⟨Cₛ, hCₛ, hsep⟩ := full_uniform_postCommonSmoothPair_fixed_tests A₁ A₂ W V M hM hV A J
  refine ⟨Cₐ, hCₐ, Cₛ, hCₛ, ?_⟩
  intro R hR
  obtain ⟨b, hpoint, hid⟩ := hsep R hR
  refine ⟨b, hpoint, ?_⟩
  intro ι _ p _ hg H₁ H₂
  have htrans := htrans p hg H₁ H₂
  have hid := hid p hg H₁ H₂
  intro s T b0 w B lengthScale label F Ψ₁ Ψ₂ m z ud ue uv kap X₁ X₂ hb0 hB hL hv hm ht hn hw hl
  have hsource := tupleSource_eq_integratedSecondMode p hg H₁ H₂ s w label F Ψ₁ Ψ₂ m A₁ A₂ W b
    V z ud ue uv kap X₁ X₂ R (fun x hx => hid F Ψ₁ Ψ₂ m (label x) (newRow x) (-newRow x)
      (z x) (ud x) (ue x) (uv x) (kap x) X₁ X₂)
  rw [hsource]
  apply htrans s T b0 (tupleOuterWeight V w z ud ue uv kap) B lengthScale label F Ψ₁ Ψ₂ m
    (V 5) (V 6) X₁ X₂ (𝓕 A₁) (𝓕 A₂) b hb0 hB hL hv hm ht hn
  · intro q x hx
    rw [tupleOuterWeight_norm]
    exact hw x hx
  · intro x hx
    exact tupleOuterWeight_continuous V w z ud ue uv kap x
  · exact hl

end SecondPassIntegration

open scoped Classical SchwartzMap FourierTransform ContDiff

namespace SecondPassIntegration
open Eisenstein SchwartzPlanePoisson JointLogSeparation SecondPassArithmetic

lemma sqrtProductNorm {ι : Type*} (p : ι → O) (S : Finset ι) :
    Real.sqrt (primeProductNorm p S) = ‖ringComplex (∏ i ∈ S, p i)‖ := by
  simp only [primeProductNorm, Real.sqrt_sq_eq_abs, abs_of_nonneg (norm_nonneg _)]

theorem columnLog_union_scale {ι : Type*} [DecidableEq ι]
    (p : ι → O) (hp : ∀ i, p i ≠ 0) (V N : Finset ι) (hVN : Disjoint V N)
    (X X₀ : ℝ) (hX : 0 < X) (hX₀ : 0 < X₀) :
    columnLog p X (V ∪ N) =
      Real.log (primeProductNorm p V * X₀ / X) + columnLog p X₀ N := by
  have hV := primeProductNorm_pos p hp V
  have hN := primeProductNorm_pos p hp N
  unfold columnLog
  rw [primeProductNorm_union p V N hVN, ← Real.log_mul
    (ne_of_gt (div_pos (mul_pos hV hX₀) hX)) (ne_of_gt (div_pos hN hX₀))]
  congr 1
  field_simp

lemma halfNormalization_at_ratio (U : ℝ → ℂ) (hUc : HasCompactSupport U)
    (hUs : ContDiff ℝ ∞ U) (g : 𝓢(ℝ, ℂ)) (hU : ∀ s, g s ≠ 0 → U s = 1)
    (N X : ℝ) (hN : 0 < N) (hX : 0 < X) :
    halfNormalizationCLM U g (Real.log (N / X)) / (Real.sqrt X : ℂ) =
      g (Real.log (N / X)) / (Real.sqrt N : ℂ) := by
  rw [halfNormalization_exact U hUc hUs g hU, Real.exp_log (div_pos hN hX), div_div]
  congr 1
  rw [← Complex.ofReal_mul, ← Real.sqrt_mul (div_pos hN hX).le]
  congr 2
  field_simp

theorem normalizedColumn_union_test {ι : Type*} [DecidableEq ι]
    (p : ι → O) (hp : ∀ i, p i ≠ 0) (V N : Finset ι) (hVN : Disjoint V N)
    (X X₀ : ℝ) (hX : 0 < X) (hX₀ : 0 < X₀)
    (U : ℝ → ℂ) (hUc : HasCompactSupport U) (hUs : ContDiff ℝ ∞ U)
    (g : 𝓢(ℝ, ℂ)) (hU : ∀ s, g s ≠ 0 → U s = 1) :
    normalizedColumn p (fun S => g (columnLog p X S)) (V ∪ N) =
      halfNormalizationCLM U g
        (Real.log (primeProductNorm p V * X₀ / X) + columnLog p X₀ N) / (Real.sqrt X : ℂ) := by
  rw [← columnLog_union_scale p hp V N hVN X X₀ hX hX₀]
  change g (Real.log (primeProductNorm p (V ∪ N) / X)) /
    (‖ringComplex (∏ i ∈ V ∪ N, p i)‖ : ℂ) = _
  rw [← sqrtProductNorm]
  exact (halfNormalization_at_ratio U hUc hUs g hU (primeProductNorm p (V ∪ N)) X
    (primeProductNorm_pos p hp _) hX).symm

end SecondPassIntegration

namespace SecondPassIntegration
open Eisenstein SchwartzPlanePoisson JointLogSeparation SecondPassArithmetic
open scoped Classical SchwartzMap FourierTransform ContDiff

def elementNorm (a : O) : ℝ := ‖ringComplex a‖ ^ 2

lemma elementNorm_pos (a : O) (ha : a ≠ 0) : 0 < elementNorm a := by
  exact sq_pos_of_pos (norm_pos_iff.mpr (ringComplex_ne_zero ha))

lemma elementNorm_mul (a b : O) : elementNorm (a*b) = elementNorm a * elementNorm b := by
  simp only [elementNorm, map_mul, norm_mul, mul_pow]

theorem seven_radial_ratio (d e v n₁ n₂ k D E V X K Y : ℝ)
    (hd : 0 < d) (he : 0 < e) (hv : 0 < v) (hn₁ : 0 < n₁) (hn₂ : 0 < n₂)
    (hk : 0 < k) (hD : 0 < D) (hE : 0 < E) (hV : 0 < V) (hX : 0 < X) (hK : 0 < K) :
    Y * k / (e * v ^ 2 * n₁ * n₂) =
      (Y * K / (D * E ^ 2 * V ^ 2 * X ^ 2)) * Real.exp
        (Real.log (d*e*k/K) - Real.log (d/D) - 2*Real.log (e/E) -
          2*Real.log (v/V) - Real.log (n₁/X) - Real.log (n₂/X)) := by
  rw [show 2 * Real.log (e/E) = Real.log (e/E) + Real.log (e/E) by ring,
    show 2 * Real.log (v/V) = Real.log (v/V) + Real.log (v/V) by ring]
  simp only [Real.exp_sub, Real.exp_add, Real.exp_log (div_pos hd hD),
    Real.exp_log (div_pos he hE), Real.exp_log (div_pos hv hV),
    Real.exp_log (div_pos hn₁ hX), Real.exp_log (div_pos hn₂ hX),
    Real.exp_log (div_pos (mul_pos (mul_pos hd he) hk) hK)]
  field_simp

theorem second_radial_dyadic_argument {ι : Type*} [DecidableEq ι]
    (p : ι → O) (hp : ∀ i, p i ≠ 0) (V N M : Finset ι)
    (hVN : Disjoint V N) (hVM : Disjoint V M)
    (d e k : O) (hd : d ≠ 0) (he : e ≠ 0) (hk : k ≠ 0)
    (D E V₀ X₀ K Y : ℝ) (hD : 0 < D) (hE : 0 < E)
    (hV₀ : 0 < V₀) (hX₀ : 0 < X₀) (hK : 0 < K) :
    Y * ‖ringComplex k‖ ^ 2 /
      (‖ringComplex e‖ ^ 2 * primeProductNorm p (V∪N) * primeProductNorm p (V∪M)) =
      (Y * K / (D * E ^ 2 * V₀ ^ 2 * X₀ ^ 2)) * Real.exp
        (Real.log (elementNorm (d*e*k) / K) - Real.log (elementNorm d / D) -
          2*Real.log (elementNorm e / E) - 2*Real.log (primeProductNorm p V / V₀) -
          columnLog p X₀ N - columnLog p X₀ M) := by
  rw [primeProductNorm_union p V N hVN, primeProductNorm_union p V M hVM]
  simp only [elementNorm_mul, columnLog]
  have h := seven_radial_ratio (elementNorm d) (elementNorm e) (primeProductNorm p V)
    (primeProductNorm p N) (primeProductNorm p M) (elementNorm k) D E V₀ X₀ K Y
    (elementNorm_pos d hd) (elementNorm_pos e he) (primeProductNorm_pos p hp V)
    (primeProductNorm_pos p hp N) (primeProductNorm_pos p hp M) (elementNorm_pos k hk)
    hD hE hV₀ hX₀ hK
  convert h using 1 ; unfold elementNorm ; ring

def conjugateProfile (g : 𝓢(ℝ, ℂ)) : 𝓢(ℝ, ℂ) :=
  SchwartzMap.postcompCLM Complex.conjCLE.toContinuousLinearMap g

@[simp] lemma conjugateProfile_apply (g : 𝓢(ℝ, ℂ)) (s : ℝ) :
    conjugateProfile g s = star (g s) := rfl

theorem normalizedColumn_pair_union {ι : Type*} [DecidableEq ι]
    (p : ι → O) (hp : ∀ i, p i ≠ 0) (V N M : Finset ι)
    (hVN : Disjoint V N) (hVM : Disjoint V M)
    (X X₀ : ℝ) (hX : 0 < X) (hX₀ : 0 < X₀)
    (U : ℝ → ℂ) (hUc : HasCompactSupport U) (hUs : ContDiff ℝ ∞ U)
    (g₁ g₂ : 𝓢(ℝ, ℂ)) (hU₁ : ∀ s, g₁ s ≠ 0 → U s = 1)
    (hU₂ : ∀ s, g₂ s ≠ 0 → U s = 1) :
    star (normalizedColumn p (fun S => g₁ (columnLog p X S)) (V∪N)) *
      normalizedColumn p (fun S => g₂ (columnLog p X S)) (V∪M) =
    (X : ℂ)⁻¹ *
      conjugateProfile (halfNormalizationCLM U g₁)
        (Real.log (primeProductNorm p V * X₀ / X) + columnLog p X₀ N) *
      halfNormalizationCLM U g₂
        (Real.log (primeProductNorm p V * X₀ / X) + columnLog p X₀ M) := by
  rw [normalizedColumn_union_test p hp V N hVN X X₀ hX hX₀ U hUc hUs g₁ hU₁,
    normalizedColumn_union_test p hp V M hVM X X₀ hX hX₀ U hUc hUs g₂ hU₂]
  simp only [conjugateProfile_apply, star_div₀, Complex.star_def, Complex.conj_ofReal]
  have hs : (Real.sqrt X : ℂ) * (Real.sqrt X : ℂ) = (X : ℂ) := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt hX.le]
  simp only [div_eq_mul_inv]
  calc
    _ = ((Real.sqrt X : ℂ) * (Real.sqrt X : ℂ))⁻¹ *
        star (halfNormalizationCLM U g₁
          (Real.log (primeProductNorm p V * X₀ / X) + columnLog p X₀ N)) *
        halfNormalizationCLM U g₂
          (Real.log (primeProductNorm p V * X₀ / X) + columnLog p X₀ M) := by
      rw [mul_inv_rev]
      simp only [Complex.star_def, div_eq_mul_inv]
      ring
    _ = _ := by rw [hs]; simp only [Complex.star_def, div_eq_mul_inv]

end SecondPassIntegration

namespace SecondPassIntegration
open Eisenstein SchwartzPlanePoisson JointLogSeparation SecondPassArithmetic
open scoped Classical SchwartzMap ContDiff
variable {ι : Type*} [DecidableEq ι] (p : ι → O) (hp : ∀ i, p i ≠ 0)

include hp in
theorem radialPairKernel_dyadic_normalization
    (V N M : Finset ι) (hVN : Disjoint V N) (hVM : Disjoint V M)
    (d e k : O) (hd : d ≠ 0) (he : e ≠ 0) (hk : k ≠ 0)
    (D E V₀ X X₀ K Y : ℝ) (hD : 0 < D) (hE : 0 < E)
    (hV₀ : 0 < V₀) (hX : 0 < X) (hX₀ : 0 < X₀) (hK : 0 < K)
    (U : ℝ → ℂ) (hUc : HasCompactSupport U) (hUs : ContDiff ℝ ∞ U)
    (g₁ g₂ W : 𝓢(ℝ, ℂ)) (hU₁ : ∀ s, g₁ s ≠ 0 → U s = 1)
    (hU₂ : ∀ s, g₂ s ≠ 0 → U s = 1) :
    radialPairKernel p e k W g₁ g₂ X X Y (V∪N) (V∪M) =
      (X : ℂ)⁻¹ *
      (conjugateProfile (halfNormalizationCLM U g₁)
        (Real.log (primeProductNorm p V * X₀ / X) + columnLog p X₀ N) *
      halfNormalizationCLM U g₂
        (Real.log (primeProductNorm p V * X₀ / X) + columnLog p X₀ M) *
      paperRadialFourier W
        ((Y * K / (D * E ^ 2 * V₀ ^ 2 * X₀ ^ 2)) * Real.exp
          (Real.log (elementNorm (d*e*k) / K) - Real.log (elementNorm d / D) -
            2*Real.log (elementNorm e / E) - 2*Real.log (primeProductNorm p V / V₀) -
            columnLog p X₀ N - columnLog p X₀ M))) := by
  unfold radialPairKernel
  rw [normalizedColumn_pair_union p hp V N M hVN hVM X X₀ hX hX₀ U hUc hUs g₁ g₂ hU₁ hU₂,
    second_radial_dyadic_argument p hp V N M hVN hVM d e k hd he hk D E V₀ X₀ K Y hD hE hV₀ hX₀ hK]
  ring

variable [∀ i, (Ideal.span {p i}).IsMaximal]
  (hg : ∀ i, lambda ∉ Ideal.span {p i})

include hp in
theorem fixedChildKernelPair_eq_postCommon
    (F V : Finset ι) (Ψ₁ Ψ₂ : O →* ℂ) (m r c d e k : O)
    (H₁ H₂ : Finset ι → ℂ)
    (hd : d ≠ 0) (he : e ≠ 0) (hk : k ≠ 0)
    (D E V₀ X X₀ K Y : ℝ) (hD : 0 < D) (hE : 0 < E)
    (hV₀ : 0 < V₀) (hX : 0 < X) (hX₀ : 0 < X₀) (hK : 0 < K)
    (U : ℝ → ℂ) (hUc : HasCompactSupport U) (hUs : ContDiff ℝ ∞ U)
    (g₁ g₂ W : 𝓢(ℝ, ℂ)) (hU₁ : ∀ s, g₁ s ≠ 0 → U s = 1)
    (hU₂ : ∀ s, g₂ s ≠ 0 → U s = 1) (windows : Fin 7 → ℝ → ℂ) :
    let A₁ := conjugateProfile (halfNormalizationCLM U g₁)
    let A₂ := halfNormalizationCLM U g₂
    let z := Real.log (primeProductNorm p V * X₀ / X)
    let ud := Real.log (elementNorm d / D)
    let ue := Real.log (elementNorm e / E)
    let uv := Real.log (primeProductNorm p V / V₀)
    let kap := Real.log (elementNorm (d*e*k) / K)
    outerWindow windows z ud ue uv kap = 1 →
    (∀ a : ℝ, A₁ (z+a) ≠ 0 → windows 5 a = 1) →
    (∀ a : ℝ, A₂ (z+a) ≠ 0 → windows 6 a = 1) →
    fixedChildKernelPair p hg F Ψ₁ Ψ₂ (m*r) (c*e*∏ i ∈ V, p i)
      (d*e*k) (d*e*(-k)) H₁ H₂
      (fun N M => radialPairKernel p e k W g₁ g₂ X X Y (V∪N) (V∪M)) =
      (X : ℂ)⁻¹ * postCommonSmoothPair p hg H₁ H₂ F Ψ₁ Ψ₂ (m*r)
        (c*e*∏ i ∈ V, p i) (d*e*k) (d*e*(-k)) A₁ A₂ W windows
        z ud ue uv kap X₀ X₀ (Y*K/(D*E^2*V₀^2*X₀^2)) := by
  dsimp only
  intro houter hcut₁ hcut₂
  simp only [fixedChildKernelPair, postCommonSmoothPair, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro N hN
  apply Finset.sum_congr rfl
  intro M hM
  by_cases hVN : Disjoint V N
  · by_cases hVM : Disjoint V M
    · rw [radialPairKernel_dyadic_normalization p hp V N M hVN hVM d e k hd he hk
        D E V₀ X X₀ K Y hD hE hV₀ hX hX₀ hK U hUc hUs g₁ g₂ W hU₁ hU₂, houter]
      by_cases h₁ : conjugateProfile (halfNormalizationCLM U g₁)
          (Real.log (primeProductNorm p V * X₀ / X) + columnLog p X₀ N) = 0
      · rw [h₁]; ring
      · by_cases h₂ : halfNormalizationCLM U g₂
            (Real.log (primeProductNorm p V * X₀ / X) + columnLog p X₀ M) = 0
        · rw [h₂]; ring
        · rw [hcut₁ _ h₁, hcut₂ _ h₂]; ring
    · rw [secondChildColumn_zero_of_overlap p hg Ψ₂ (m*r) c e
        (d*e*(-k)) H₂ V M hVM]
      ring
  · rw [secondChildColumn_zero_of_overlap p hg Ψ₁ (m*r) c e
      (d*e*k) H₁ V N hVN, star_zero]
    ring

end SecondPassIntegration

namespace SecondPassIntegration
open Eisenstein SchwartzPlanePoisson JointLogSeparation SecondPassArithmetic
open scoped Classical SchwartzMap ContDiff
section

theorem halfNormalization_support_bound (U : ℝ → ℂ) (hUc : HasCompactSupport U)
    (hUs : ContDiff ℝ ∞ U) (g : 𝓢(ℝ, ℂ)) (A : ℝ)
    (hg : ∀ s, g s ≠ 0 → |s| ≤ A) :
    ∀ s, halfNormalizationCLM U g s ≠ 0 → |s| ≤ A := by
  intro s hs
  apply hg s
  intro hzero
  apply hs
  rw [halfNormalizationCLM_apply U hUc hUs, hzero, mul_zero]

lemma translated_support_bound (g : ℝ → ℂ) (A B z x : ℝ)
    (hg : ∀ s, g s ≠ 0 → |s| ≤ A) (hz : |z| ≤ B) (hx : g (z+x) ≠ 0) :
    |x| ≤ A+B := by
  have ht := hg (z+x) hx
  have ha : |x| ≤ |z+x| + |z| := by
    calc
      |x| = |(z+x)-z| := by congr 1; ring
      _ ≤ |z+x| + |z| := abs_sub _ _
  linarith

theorem exists_fixed_sector_windows (A B : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B) :
    ∃ windows : Fin 7 → ℝ → ℂ,
      (∀ j, HasCompactSupport (windows j)) ∧
      (∀ j, ContDiff ℝ ∞ (windows j)) ∧
      (∀ j s, windows j s ≠ 0 → |s| ≤ A+B+1) ∧
      (∀ z ud ue uv kap : ℝ,
        |z| ≤ B → |ud| ≤ B → |ue| ≤ B → |uv| ≤ B → |kap| ≤ B →
        outerWindow windows z ud ue uv kap = 1) ∧
      (∀ (g : ℝ → ℂ) (z : ℝ), (∀ s, g s ≠ 0 → |s| ≤ A) → |z| ≤ B →
        ∀ j x, g (z+x) ≠ 0 → windows j x = 1) := by
  obtain ⟨w, hwc, hws, hweq, hwsupp, hwzero⟩ :=
    JointLogSeparation.exists_complex_smooth_cutoff (A+B) (add_nonneg hA hB)
  refine ⟨fun _ => w, fun _ => hwc, fun _ => hws, ?_, ?_, ?_⟩
  · intro j s hs
    have hh := hwsupp (subset_closure hs)
    exact abs_le.mpr hh
  · intro z ud ue uv kap hz hd he hv hk
    have heq (s : ℝ) (hs : |s| ≤ B) : w s = 1 := hweq s (by linarith)
    simp only [outerWindow, heq z hz, heq ud hd, heq ue he, heq uv hv, heq kap hk,
      one_mul]
  · intro g z hg hz j x hx
    exact hweq x (translated_support_bound g A B z x hg hz hx)

end

open Eisenstein SchwartzPlanePoisson JointLogSeparation SecondPassArithmetic

theorem exists_fixed_normalized_child_tests {ι : Type*} [DecidableEq ι]
    (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
      (hg : ∀ i, lambda ∉ Ideal.span {p i})
    (g₁ g₂ W : 𝓢(ℝ, ℂ)) (A B : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hg₁ : ∀ s, g₁ s ≠ 0 → |s| ≤ A) (hg₂ : ∀ s, g₂ s ≠ 0 → |s| ≤ A) :
    ∃ (A₁ A₂ : 𝓢(ℝ, ℂ)) (windows : Fin 7 → ℝ → ℂ),
      (∀ j, HasCompactSupport (windows j)) ∧
      (∀ j, ContDiff ℝ ∞ (windows j)) ∧
      (∀ j s, windows j s ≠ 0 → |s| ≤ A+B+1) ∧
      ∀ (D E V₀ X X₀ K Y : ℝ), 0 < D → 0 < E → 0 < V₀ → 0 < X → 0 < X₀ → 0 < K →
      ∀ (F V : Finset ι) (Ψ₁ Ψ₂ : O →* ℂ) (m r c d e k : O) (H₁ H₂ : Finset ι → ℂ),
        d ≠ 0 → e ≠ 0 → k ≠ 0 →
        |Real.log (primeProductNorm p V * X₀ / X)| ≤ B →
        |Real.log (elementNorm d / D)| ≤ B →
        |Real.log (elementNorm e / E)| ≤ B →
        |Real.log (primeProductNorm p V / V₀)| ≤ B →
        |Real.log (elementNorm (d*e*k) / K)| ≤ B →
        fixedChildKernelPair p hg F Ψ₁ Ψ₂ (m*r) (c*e*∏ i ∈ V, p i)
          (d*e*k) (d*e*(-k)) H₁ H₂
          (fun N M => radialPairKernel p e k W g₁ g₂ X X Y (V∪N) (V∪M)) =
        (X : ℂ)⁻¹ * postCommonSmoothPair p hg H₁ H₂ F Ψ₁ Ψ₂ (m*r)
          (c*e*∏ i ∈ V, p i) (d*e*k) (d*e*(-k)) A₁ A₂ W windows
          (Real.log (primeProductNorm p V * X₀ / X)) (Real.log (elementNorm d / D))
          (Real.log (elementNorm e / E)) (Real.log (primeProductNorm p V / V₀))
          (Real.log (elementNorm (d*e*k) / K)) X₀ X₀ (Y*K/(D*E^2*V₀^2*X₀^2)) := by
  obtain ⟨U, hUc, hUs, hUone, hUsupp, hUzero⟩ :=
    JointLogSeparation.exists_complex_smooth_cutoff A hA
  have hU₁ : ∀ s, g₁ s ≠ 0 → U s = 1 := fun s hs => hUone s (hg₁ s hs)
  have hU₂ : ∀ s, g₂ s ≠ 0 → U s = 1 := fun s hs => hUone s (hg₂ s hs)
  let A₁ := conjugateProfile (halfNormalizationCLM U g₁)
  let A₂ := halfNormalizationCLM U g₂
  have hA₁ : ∀ s, A₁ s ≠ 0 → |s| ≤ A := by
    intro s hs
    apply halfNormalization_support_bound U hUc hUs g₁ A hg₁ s
    intro hz
    exact hs (by simp [A₁, hz])
  have hA₂ : ∀ s, A₂ s ≠ 0 → |s| ≤ A :=
    halfNormalization_support_bound U hUc hUs g₂ A hg₂
  obtain ⟨windows, hwc, hws, hwb, hwo, hwt⟩ := exists_fixed_sector_windows A B hA hB
  refine ⟨A₁, A₂, windows, hwc, hws, hwb, ?_⟩
  intro D E V₀ X X₀ K Y hD hE hV₀ hX hX₀ hK F V Ψ₁ Ψ₂ m r c d e k H₁ H₂ hd he hk hz hud hue huv hkap
  apply fixedChildKernelPair_eq_postCommon p hp hg F V Ψ₁ Ψ₂ m r c d e k H₁ H₂ hd he hk
    D E V₀ X X₀ K Y hD hE hV₀ hX hX₀ hK U hUc hUs g₁ g₂ W hU₁ hU₂ windows
  · exact hwo _ _ _ _ _ hz hud hue huv hkap
  · exact fun a ha => hwt A₁ _ hA₁ hz 5 a ha
  · exact fun a ha => hwt A₂ _ hA₂ hz 6 a ha

end SecondPassIntegration

namespace SecondPassIntegration
open Eisenstein SchwartzPlanePoisson SecondPassArithmetic JointLogSeparation MeasureTheory
open scoped Classical SchwartzMap FourierTransform
local instance : Finite Oˣ := cubic_units_finite
local instance : Fintype Oˣ := Fintype.ofFinite _

def densityChildEnergy {ι : Type*} [DecidableEq ι]
    (p : ι → O) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hg : ∀ i, lambda ∉ Ideal.span {p i}) (H₁ H₂ : Finset ι → ℂ)
    (F : Finset ι) (Ψ₁ Ψ₂ : O →* ℂ) (m : O) (T : Finset (Ideal O × O))
    (V₁ V₂ : ℝ → ℂ) (X₁ X₂ : ℝ) (J : ℕ) : ℝ :=
  ∫ t₁ : ℝ, ∫ t₂ : ℝ, ∫ t₃ : ℝ,
    tripleLogDensity J (t₁,t₂,t₃) *
      childGeometricMean p hg H₁ H₂ F Ψ₁ Ψ₂ m T V₁ V₂ X₁ X₂ (t₁,t₂,t₃)

theorem child_coefficient_density_bound {ι : Type*} [DecidableEq ι]
    (p : ι → O) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hg : ∀ i, lambda ∉ Ideal.span {p i}) (H₁ H₂ : Finset ι → ℂ)
    (F : Finset ι) (Ψ₁ Ψ₂ : O →* ℂ) (m : O) (T : Finset (Ideal O × O))
    (V₁ V₂ : ℝ → ℂ) (X₁ X₂ : ℝ) (b₁ b₂ b₃ : 𝓢(ℝ, ℂ)) (J : ℕ) (S C : ℝ)
    (hpoint : ∀ t₁ t₂ t₃ : ℝ, S * ‖b₁ t₁*b₂ t₂*b₃ t₃‖ ≤
      C * firstLogDensity J t₁ *
        firstLogDensity J t₂ * firstLogDensity J t₃) :
    S * (∫ t₁ : ℝ, ∫ t₂ : ℝ, ∫ t₃ : ℝ,
      ‖tripleCoefficient b₁ b₂ b₃ (t₁,t₂,t₃)‖ *
        childGeometricMean p hg H₁ H₂ F Ψ₁ Ψ₂ m T V₁ V₂ X₁ X₂ (t₁,t₂,t₃)) ≤
    C * densityChildEnergy p hg H₁ H₂ F Ψ₁ Ψ₂ m T V₁ V₂ X₁ X₂ J := by
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
  exact triple_coefficient_density_bound b₁ b₂ b₃ J G hG hG0 M hM S C hpoint

end SecondPassIntegration

namespace SecondPassIntegration
open Eisenstein SchwartzPlanePoisson SecondPassArithmetic SecondPassFiber JointLogSeparation MeasureTheory
open scoped Classical SchwartzMap FourierTransform
local instance : Finite Oˣ := cubic_units_finite
local instance : Fintype Oˣ := Fintype.ofFinite _

/-- Uniform radial decay survives the divisor-tuple transfer to fixed descendant energies. -/
theorem full_uniform_tuple_density_transfer (ε : ℝ) (hε : 0 < ε)
    (A₁ A₂ W : 𝓢(ℝ, ℂ)) (V : Fin 7 → ℝ → ℂ) (M : Fin 7 → ℝ)
    (hM : ∀ j, 0 ≤ M j) (hV : ∀ j x, V j x ≠ 0 → |x| ≤ M j) (A J : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ R : ℝ, 0 < R →
      ∀ {ι : Type*} [DecidableEq ι] (p : ι → O) [∀ i, (Ideal.span {p i}).IsMaximal]
      (hg : ∀ i, lambda ∉ Ideal.span {p i}) (H₁ H₂ : Finset ι → ℂ)
      (s : Finset OldTuple) (T : Finset (Ideal O × O)) (b0 : Ideal O)
      (w : OldTuple → ℂ) (B lengthScale : ℝ) (label : OldTuple → O)
      (F : Finset ι) (Ψ₁ Ψ₂ : O →* ℂ) (m : O)
      (z ud ue uv kap : OldTuple → ℝ) (X₁ X₂ : ℝ),
      b0 ≠ ⊥ → 0 ≤ B → 0 ≤ lengthScale →
      (∀ x ∈ s, Valid x (newLabel x) b0 (newRow x)) →
      (∀ x ∈ s, (newLabel x, newRow x) ∈ T) →
      (∀ z ∈ T, z.1 ≠ ⊥) → (∀ z ∈ T, (Ideal.absNorm z.1 : ℝ) ≤ lengthScale) →
      (∀ x ∈ s, ‖w x‖ * ‖outerWindow V (z x) (ud x) (ue x) (uv x) (kap x)‖ ≤ B) →
      (∀ x ∈ s, Ideal.span {label x} = newLabel x) →
      (1 + R)^A * ‖tupleSourceSum p hg H₁ H₂ s w label F Ψ₁ Ψ₂ m
        A₁ A₂ W V z ud ue uv kap X₁ X₂ R‖ ≤
        B * C * (lengthScale * Ideal.absNorm b0)^ε *
          densityChildEnergy p hg H₁ H₂ F Ψ₁ Ψ₂ m T (V 5) (V 6) X₁ X₂ J := by
  obtain ⟨Cₐ, hCₐ, Cₛ, hCₛ, ht⟩ :=
    full_uniform_tupleSource_transfer ε hε A₁ A₂ W V M hM hV A J
  refine ⟨Cₐ * Cₛ, mul_nonneg hCₐ.le hCₛ, ?_⟩
  intro R hR
  obtain ⟨b, hpoint, htransfer⟩ := ht R hR
  intro ι _ p _ hg H₁ H₂ s T b0 w B lengthScale label F Ψ₁ Ψ₂ m
    z ud ue uv kap X₁ X₂ hb0 hB hL hv hm ht hn hw hl
  have hsource := htransfer p hg H₁ H₂ s T b0 w B lengthScale label F Ψ₁ Ψ₂ m
    z ud ue uv kap X₁ X₂ hb0 hB hL hv hm ht hn hw hl
  have hdensity := child_coefficient_density_bound p hg H₁ H₂ F Ψ₁ Ψ₂ m T
    (V 5) (V 6) X₁ X₂ (𝓕 A₁) (𝓕 A₂) b J ((1 + R)^A) Cₛ hpoint
  calc
    _ ≤ (1 + R)^A * ((B * Cₐ * (lengthScale * Ideal.absNorm b0)^ε) *
        (∫ t₁ : ℝ, ∫ t₂ : ℝ, ∫ t₃ : ℝ,
          ‖tripleCoefficient (𝓕 A₁) (𝓕 A₂) b (t₁,t₂,t₃)‖ *
            childGeometricMean p hg H₁ H₂ F Ψ₁ Ψ₂ m T (V 5) (V 6) X₁ X₂ (t₁,t₂,t₃))) :=
      mul_le_mul_of_nonneg_left hsource (by positivity)
    _ = (B * Cₐ * (lengthScale * Ideal.absNorm b0)^ε) * ((1 + R)^A *
        (∫ t₁ : ℝ, ∫ t₂ : ℝ, ∫ t₃ : ℝ,
          ‖tripleCoefficient (𝓕 A₁) (𝓕 A₂) b (t₁,t₂,t₃)‖ *
            childGeometricMean p hg H₁ H₂ F Ψ₁ Ψ₂ m T (V 5) (V 6) X₁ X₂ (t₁,t₂,t₃))) := by ring
    _ ≤ (B * Cₐ * (lengthScale * Ideal.absNorm b0)^ε) *
        (Cₛ * densityChildEnergy p hg H₁ H₂ F Ψ₁ Ψ₂ m T (V 5) (V 6) X₁ X₂ J) :=
      mul_le_mul_of_nonneg_left hdensity (by positivity)
    _ = _ := by ring

end SecondPassIntegration

namespace SecondPassIntegration
open Eisenstein SchwartzPlanePoisson SecondPassArithmetic JointLogSeparation MeasureTheory
open scoped Classical SchwartzMap FourierTransform
local instance : Finite Oˣ := cubic_units_finite
local instance : Fintype Oˣ := Fintype.ofFinite _
variable {ι : Type*} [DecidableEq ι] (p : ι → O)
  [∀ i, (Ideal.span {p i}).IsMaximal] (hg : ∀ i, lambda ∉ Ideal.span {p i})

lemma childEnergy_eq_difference (H : Finset ι → ℂ) (F : Finset ι) (Ψ : O →* ℂ) (m : O)
    (T : Finset (Ideal O × O)) (V : ℝ → ℂ) (X a b : ℝ)
    (testNegative rowNegative : Bool) :
    childEnergy p hg H F Ψ m T V X testNegative rowNegative a b =
      childEnergy p hg H F Ψ m T V X testNegative rowNegative (a-b) 0 := by
  have he : weightedSecondTest p H V X a b testNegative =
      weightedSecondTest p H V X (a-b) 0 testNegative := by
    funext N
    simp only [weightedSecondTest, fixedSecondTest, sub_zero]
  simp only [childEnergy, he]

theorem densityChildEnergy_polynomial_bound (H₁ H₂ : Finset ι → ℂ) (F : Finset ι) (Ψ₁ Ψ₂ : O →* ℂ)
    (m : O) (T : Finset (Ideal O × O)) (V₁ V₂ : ℝ → ℂ) (X₁ X₂ : ℝ)
    (J : ℕ) (B₁ B₂ : ℝ) (hB₁ : 0 ≤ B₁) (hB₂ : 0 ≤ B₂)
    (h₁ : ∀ a : ℝ, childEnergy p hg H₁ F Ψ₁ m T V₁ X₁ true false a 0 ≤
      B₁ * (1+‖a‖)^(2*J))
    (h₂ : ∀ a : ℝ, childEnergy p hg H₂ F Ψ₂ m T V₂ X₂ false true a 0 ≤
      B₂ * (1+‖a‖)^(2*J)) :
    densityChildEnergy p hg H₁ H₂ F Ψ₁ Ψ₂ m T V₁ V₂ X₁ X₂ (2*J) ≤
      (Real.sqrt B₁ * Real.sqrt B₂) *
        (∫ t : ℝ, firstLogDensity 0 t)^3 := by
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
  have hsqrt (B a e : ℝ) (hB : 0 ≤ B) (he : e ≤ B*(1+‖a‖)^(2*J)) :
      Real.sqrt e ≤ Real.sqrt B * (1+‖a‖)^J := by
    calc
      _ ≤ Real.sqrt (B*(1+‖a‖)^(2*J)) := Real.sqrt_le_sqrt he
      _ = _ := by
        rw [Real.sqrt_mul hB, mul_comm 2 J, pow_mul, Real.sqrt_sq (by positivity)]
  have hbound (q : Frequency) : G q ≤
      (Real.sqrt B₁ * Real.sqrt B₂) *
        (1+‖q.1‖)^(2*J)*(1+‖q.2.1‖)^(2*J)*(1+‖q.2.2‖)^(2*J) := by
    have hleft := h₁ (q.1-q.2.2)
    have hright := h₂ (q.2.1-q.2.2)
    rw [← childEnergy_eq_difference p hg H₁ F Ψ₁ m T V₁ X₁ q.1 q.2.2 true false] at hleft
    rw [← childEnergy_eq_difference p hg H₂ F Ψ₂ m T V₂ X₂ q.2.1 q.2.2 false true] at hright
    calc
      _ ≤ (Real.sqrt B₁ * (1+‖q.1-q.2.2‖)^J) *
          (Real.sqrt B₂ * (1+‖q.2.1-q.2.2‖)^J) :=
        mul_le_mul (hsqrt B₁ _ _ hB₁ hleft) (hsqrt B₂ _ _ hB₂ hright)
          (Real.sqrt_nonneg _) (by positivity)
      _ = (Real.sqrt B₁ * Real.sqrt B₂) *
          ((1+‖q.1-q.2.2‖)^J * (1+‖q.2.1-q.2.2‖)^J) := by ring
      _ ≤ _ := by
        have hh := mul_le_mul_of_nonneg_left (difference_height_weight_le q.1 q.2.1 q.2.2 J)
          (mul_nonneg (Real.sqrt_nonneg B₁) (Real.sqrt_nonneg B₂))
        simpa only [mul_assoc] using hh
  exact triple_density_polynomial_bound G hG hG0 M hM (2*J)
    (Real.sqrt B₁ * Real.sqrt B₂) hbound

end SecondPassIntegration

namespace SecondPassArithmetic
open Eisenstein SchwartzPlanePoisson
open scoped Classical SchwartzMap

def normPhase (t : ℝ) : O →* ℂ where
  toFun z := if z=0 then 0 else kernelLogPhase t (Real.log (‖ringComplex z‖^2))
  map_one' := by simp [kernelLogPhase]
  map_mul' a b := by
    by_cases ha : a=0
    · simp [ha]
    by_cases hb : b=0
    · simp [hb]
    simp only [if_neg ha,if_neg hb,if_neg (mul_ne_zero ha hb),map_mul,norm_mul,mul_pow]
    rw [Real.log_mul (pow_ne_zero _ (norm_ne_zero_iff.mpr (ringComplex_ne_zero ha)))
      (pow_ne_zero _ (norm_ne_zero_iff.mpr (ringComplex_ne_zero hb))),kernelLogPhase_add]

@[simp] theorem normPhase_zero (t : ℝ) : normPhase t 0=0 := by simp [normPhase]

theorem normPhase_of_ne_zero (t : ℝ) (z : O) (hz : z≠0) :
    normPhase t z=kernelLogPhase t (Real.log (‖ringComplex z‖^2)) := by simp [normPhase,hz]

theorem normPhase_norm (t : ℝ) (z : O) (hz : z≠0) : ‖normPhase t z‖=1 := by
  rw [normPhase_of_ne_zero t z hz,kernelLogPhase_norm]

theorem normPhase_norm_le_one (t : ℝ) (z : O) : ‖normPhase t z‖≤1 := by
  by_cases hz : z=0
  · simp [hz]
  · rw [normPhase_norm t z hz]

theorem normPhase_add (s t : ℝ) : normPhase (s+t)=normPhase s*normPhase t := by
  ext z
  by_cases hz : z=0
  · simp [hz]
  · simp only [MonoidHom.mul_apply,normPhase_of_ne_zero _ z hz,JointLogSeparation.kernelLogPhase_add_frequency]

theorem normPhase_star (t : ℝ) (z : O) : star (normPhase t z)=normPhase (-t) z := by
  by_cases hz : z=0
  · simp [hz]
  · simp only [normPhase_of_ne_zero _ z hz,JointLogSeparation.kernelLogPhase_conjugate]

def normHeightTwist (Ψ : O →* ℂ) (t : ℝ) : O →* ℂ := Ψ*normPhase t

theorem normHeightTwist_norm_le (Ψ : O →* ℂ) (t : ℝ) (z : O) :
    ‖normHeightTwist Ψ t z‖≤‖Ψ z‖ := by
  simp only [normHeightTwist,MonoidHom.mul_apply,norm_mul]
  exact mul_le_of_le_one_right (norm_nonneg _) (normPhase_norm_le_one t z)

theorem normHeightTwist_twice (Ψ : O →* ℂ) (s t : ℝ) :
    normHeightTwist (normHeightTwist Ψ s) t=normHeightTwist Ψ (s+t) := by
  simp only [normHeightTwist,normPhase_add,mul_assoc]

theorem normHeightTwist_mul (Ψ Ξ : O →* ℂ) (t : ℝ) :
    normHeightTwist (Ψ*Ξ) t=normHeightTwist Ψ t*Ξ := by
  unfold normHeightTwist
  ac_rfl

variable {ι : Type*} [DecidableEq ι] (p : ι → O) (hp : ∀i,p i≠0)

include hp in
omit [DecidableEq ι] in
theorem kernelLogPhase_columnLog (X t : ℝ) (hX : 0<X) (S : Finset ι) :
    kernelLogPhase t (columnLog p X S)=
      kernelLogPhase t (-Real.log X)*normPhase t (∏i∈S,p i) := by
  rw [normPhase_of_ne_zero t _ (Finset.prod_ne_zero_iff.mpr (fun i _=>hp i))]
  rw [columnLog,Real.log_div (primeProductNorm_pos p hp S).ne' hX.ne']
  rw [sub_eq_add_neg,kernelLogPhase_add]
  exact mul_comm _ _


end SecondPassArithmetic

namespace SecondPassArithmetic
open Eisenstein SchwartzPlanePoisson
open scoped Classical SchwartzMap

def secondSignedHeight (negative : Bool) (a b : ℝ) : ℝ :=
  if negative then b-a else a-b

variable {ι : Type*} [DecidableEq ι] (p : ι → O) (hp : ∀i,p i≠0)

include hp in
omit [DecidableEq ι] in
theorem fixedSecondTest_normPhase (V : ℝ → ℂ) (X a b : ℝ) (hX : 0<X)
    (negative : Bool) (S : Finset ι) :
    fixedSecondTest p V X a b negative S=
      kernelLogPhase (secondSignedHeight negative a b) (-Real.log X)*
      normPhase (secondSignedHeight negative a b) (∏i∈S,p i)*
      fixedSecondTest p V X 0 0 negative S := by
  have hz (x : ℝ) : kernelLogPhase 0 x=1 := by simp [kernelLogPhase]
  cases negative <;>
    simp only [secondSignedHeight,fixedSecondTest,JointLogSeparation.fixedColumnTest,
      Bool.false_eq_true,ite_false,ite_true,sub_self,hz,mul_one,star_mul,
      JointLogSeparation.kernelLogPhase_conjugate,neg_sub] <;>
    rw [kernelLogPhase_columnLog p hp X _ hX S] ; ring

variable [∀i,(Ideal.span {p i}).IsMaximal]
  (hg : ∀i,lambda∉Ideal.span {p i})

include hp in
theorem fixedChildRow_secondTest_normPhase (H : Finset ι → ℂ) (pool : Finset ι) (Ψ : O →* ℂ) (m f y : O)
    (V : ℝ → ℂ) (X a b : ℝ) (hX : 0<X) (negative : Bool) :
    fixedChildRow p hg pool Ψ m (weightedSecondTest p H V X a b negative) f y=
      kernelLogPhase (secondSignedHeight negative a b) (-Real.log X)*
      fixedChildRow p hg pool (normHeightTwist Ψ (secondSignedHeight negative a b)) m
        (weightedSecondTest p H V X 0 0 negative) f y := by
  unfold fixedChildRow
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro S hS
  simp only [secondChildColumn,weightedSecondTest,fixedSecondTest_normPhase p hp V X a b hX negative S,
    normHeightTwist,MonoidHom.mul_apply]
  ring

end SecondPassArithmetic

namespace SecondPassIntegration
open Eisenstein SchwartzPlanePoisson SecondPassArithmetic JointLogSeparation
local instance : Finite Oˣ := cubic_units_finite
local instance : Fintype Oˣ := Fintype.ofFinite _

variable {ι : Type*} [DecidableEq ι] (p : ι → O) (hp : ∀i,p i≠0)
  [∀i,(Ideal.span {p i}).IsMaximal]
  (hg : ∀i,lambda∉Ideal.span {p i})

include hp in
theorem childEnergy_normHeight (H : Finset ι → ℂ) (pool : Finset ι) (Ψ : O →* ℂ) (m : O)
    (T : Finset (Ideal O × O)) (V : ℝ → ℂ) (X a b : ℝ) (hX : 0<X)
    (testNegative rowNegative : Bool) :
    childEnergy p hg H pool Ψ m T V X testNegative rowNegative a b=
      childEnergy p hg H pool (normHeightTwist Ψ (secondSignedHeight testNegative a b))
        m T V X testNegative rowNegative 0 0 := by
  unfold childEnergy idealChildRow
  simp_rw [fixedChildRow_secondTest_normPhase p hp hg H pool Ψ m _ _ V X a b hX testNegative,
    norm_mul,kernelLogPhase_norm,one_mul]

include hp in
theorem childEnergy_previousNormHeight (H : Finset ι → ℂ) (pool : Finset ι) (Ψ : O →* ℂ) (m : O)
    (T : Finset (Ideal O × O)) (V : ℝ → ℂ) (X t a b : ℝ) (hX : 0<X)
    (testNegative rowNegative : Bool) :
    childEnergy p hg H pool (normHeightTwist Ψ t) m T V X testNegative rowNegative a b=
      childEnergy p hg H pool (normHeightTwist Ψ (t+secondSignedHeight testNegative a b))
        m T V X testNegative rowNegative 0 0 := by
  rw [childEnergy_normHeight p hp hg H pool (normHeightTwist Ψ t) m T V X a b hX
    testNegative rowNegative,normHeightTwist_twice]

end SecondPassIntegration

namespace SecondPassIntegration
open Eisenstein SchwartzPlanePoisson SecondPassArithmetic JointLogSeparation MeasureTheory
open scoped Classical SchwartzMap
local instance : Finite Oˣ := cubic_units_finite
local instance : Fintype Oˣ := Fintype.ofFinite _

private theorem sqrt_height_weight (B t : ℝ) (hB : 0≤B) (J : ℕ) :
    Real.sqrt (B*(1+‖t‖)^(2*J))=Real.sqrt B*(1+‖t‖)^J := by
  rw [show 2*J=J*2 from Nat.mul_comm _ _,pow_mul,Real.sqrt_mul hB,
    Real.sqrt_sq (pow_nonneg (by positivity : 0≤1+‖t‖) J)]

variable {ι : Type*} [DecidableEq ι] (p : ι → O) (hp : ∀i,p i≠0)
  [∀i,(Ideal.span {p i}).IsMaximal]
  (hg : ∀i,lambda∉Ideal.span {p i})
  (H₁ H₂ : Finset ι → ℂ)

include hp in
theorem densityChildEnergy_normHeight_polynomial
    (pool : Finset ι) (Ψ₁ Ψ₂ : O →* ℂ) (m : O) (T : Finset (Ideal O × O))
    (V₁ V₂ : ℝ → ℂ) (X₁ X₂ t₁ t₂ B₁ B₂ : ℝ) (J : ℕ)
    (hX₁ : 0<X₁) (hX₂ : 0<X₂) (hB₁ : 0≤B₁) (hB₂ : 0≤B₂)
    (h₁ : ∀t,childEnergy p hg H₁ pool (normHeightTwist Ψ₁ t) m T V₁ X₁ true false 0 0≤
      B₁*(1+‖t‖)^(2*J))
    (h₂ : ∀t,childEnergy p hg H₂ pool (normHeightTwist Ψ₂ t) m T V₂ X₂ false true 0 0≤
      B₂*(1+‖t‖)^(2*J)) :
    densityChildEnergy p hg H₁ H₂ pool (normHeightTwist Ψ₁ t₁) (normHeightTwist Ψ₂ t₂)
      m T V₁ V₂ X₁ X₂ (2*J)≤
      Real.sqrt B₁*Real.sqrt B₂*(1+‖t₁‖)^J*(1+‖t₂‖)^J*
        (∫t : ℝ,firstLogDensity 0 t)^3 := by
  have ha₁ (a : ℝ) : childEnergy p hg H₁ pool (normHeightTwist Ψ₁ t₁) m T V₁ X₁ true false a 0≤
      (B₁*(1+‖t₁‖)^(2*J))*(1+‖a‖)^(2*J) := by
    rw [childEnergy_previousNormHeight p hp hg H₁ pool Ψ₁ m T V₁ X₁ t₁ a 0 hX₁ true false]
    simp only [secondSignedHeight,ite_true,zero_sub,←sub_eq_add_neg]
    calc
      _ ≤ B₁*(1+‖t₁-a‖)^(2*J) := h₁ (t₁-a)
      _ ≤ B₁*((1+‖t₁‖)*(1+‖a‖))^(2*J) :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity)
          (JointLogSeparation.one_add_norm_sub_le t₁ a) _) hB₁
      _ = _ := by rw [mul_pow]; ring
  have ha₂ (a : ℝ) : childEnergy p hg H₂ pool (normHeightTwist Ψ₂ t₂) m T V₂ X₂ false true a 0≤
      (B₂*(1+‖t₂‖)^(2*J))*(1+‖a‖)^(2*J) := by
    rw [childEnergy_previousNormHeight p hp hg H₂ pool Ψ₂ m T V₂ X₂ t₂ a 0 hX₂ false true]
    simp only [secondSignedHeight,Bool.false_eq_true,ite_false,sub_zero]
    have hsum : 1+‖t₂+a‖≤(1+‖t₂‖)*(1+‖a‖) := by
      simpa only [sub_neg_eq_add,norm_neg] using JointLogSeparation.one_add_norm_sub_le t₂ (-a)
    calc
      _ ≤ B₂*(1+‖t₂+a‖)^(2*J) := h₂ (t₂+a)
      _ ≤ B₂*((1+‖t₂‖)*(1+‖a‖))^(2*J) :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hsum _) hB₂
      _ = _ := by rw [mul_pow]; ring
  have hd := densityChildEnergy_polynomial_bound p hg H₁ H₂ pool
    (normHeightTwist Ψ₁ t₁) (normHeightTwist Ψ₂ t₂) m T V₁ V₂ X₁ X₂ J
    (B₁*(1+‖t₁‖)^(2*J)) (B₂*(1+‖t₂‖)^(2*J))
    (mul_nonneg hB₁ (by positivity)) (mul_nonneg hB₂ (by positivity)) ha₁ ha₂
  rw [sqrt_height_weight B₁ t₁ hB₁ J,sqrt_height_weight B₂ t₂ hB₂ J] at hd
  exact hd.trans_eq (by ring)

end SecondPassIntegration

namespace SecondPassArithmetic
open Eisenstein SchwartzPlanePoisson FirstPassCubeLabels UniqueFactorizationMonoid
open scoped Classical

section
variable {ι : Type*} [DecidableEq ι] (P : ι → Ideal O)
  [∀ i, (P i).IsMaximal] (hinj : Function.Injective P)
include hinj

theorem primeIdealProduct_emultiplicity (S : Finset ι) (v : ι → ℕ) (i : ι) :
    emultiplicity (P i) (∏ j ∈ S, P j ^ v j) = if i ∈ S then (v i : ℕ∞) else 0 := by
  have hp (j : ι) : Prime (P j) := Ideal.prime_of_isPrime (NeZero.ne (P j)) inferInstance
  rw [Finset.emultiplicity_prod (hp i)]
  have hz (j : ι) (hji : j ≠ i) : emultiplicity (P i) (P j ^ v j) = 0 := by
    rw [emultiplicity_pow (hp i), emultiplicity_eq_zero_of_irreducible_ne
      (hp i).irreducible (hp j).irreducible (fun he => hji (hinj he).symm), mul_zero]
  by_cases hi : i ∈ S
  · rw [if_pos hi,Finset.sum_eq_single i]
    · exact emultiplicity_pow_self_of_prime (hp i) (v i)
    · intro j hj hji
      exact hz j hji
    · exact fun hn => (hn hi).elim
  · rw [if_neg hi]
    apply Finset.sum_eq_zero
    intro j hj
    exact hz j (fun he => hi (he ▸ hj))

theorem primeIdealProduct_exponents_eq
    (B C : Finset ι) (v w : ι → ℕ)
    (hv : ∀ i, i ∉ B → v i = 0) (hw : ∀ i, i ∉ C → w i = 0)
    (heq : (∏ i ∈ B, P i ^ v i) = ∏ i ∈ C, P i ^ w i) : v = w := by
  funext i
  have he := congrArg (fun I => emultiplicity (P i) I) heq
  rw [primeIdealProduct_emultiplicity P hinj,primeIdealProduct_emultiplicity P hinj] at he
  have hB : (if i ∈ B then (v i : ℕ∞) else 0) = (v i : ℕ∞) := by
    by_cases h : i ∈ B <;> simp [h,hv i]
  have hC : (if i ∈ C then (w i : ℕ∞) else 0) = (w i : ℕ∞) := by
    by_cases h : i ∈ C <;> simp [h,hw i]
  rw [hB,hC] at he
  exact_mod_cast he

end

theorem primeProduct_span_exponents_eq {ι : Type*} [DecidableEq ι]
    (p : ι → O) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (B C : Finset ι) (v w : ι → ℕ)
    (hv : ∀ i, i ∉ B → v i = 0) (hw : ∀ i, i ∉ C → w i = 0)
    (heq : Ideal.span {FirstPassCubeLabels.primeProduct p B v} =
      Ideal.span {FirstPassCubeLabels.primeProduct p C w}) : v = w := by
  apply primeIdealProduct_exponents_eq (fun i => Ideal.span {p i}) hinj B C v w hv hw
  simpa only [FirstPassCubeLabels.primeProduct,span_finset_prime_product,
    ←Ideal.span_singleton_pow] using heq


theorem primeIdealFamily_product_injective {ι : Type*} [DecidableEq ι]
    (P : ι → Ideal O) [∀ i, (P i).IsMaximal] (hinj : Function.Injective P) :
    Function.Injective (fun S : Finset ι => ∏ i ∈ S, P i) := by
  intro S T he
  ext i
  have h := congrArg (fun I => emultiplicity (P i) I) he
  have hS := primeIdealProduct_emultiplicity P hinj S (fun _ => 1) i
  have hT := primeIdealProduct_emultiplicity P hinj T (fun _ => 1) i
  simp only [pow_one] at hS hT
  rw [hS, hT] at h
  by_cases hs : i ∈ S <;> by_cases ht : i ∈ T <;> simp_all

@[ext] structure SecondExpansionData (ι : Type*) where
  sourceCommon : Finset ι
  divisor : Finset ι
  overlap : Finset ι
  frequency : O
  deriving DecidableEq

@[ext] structure CubeCoordinates (ι : Type*) where
  leftExponent : ι →₀ ℕ
  rightExponent : ι →₀ ℕ
  leftDivisor : Finset ι
  rightDivisor : Finset ι

namespace CubeCoordinates
variable {ι : Type*} [DecidableEq ι]

def support (x : CubeCoordinates ι) : Finset ι :=
  x.leftExponent.support ∪ x.rightExponent.support

def leftBit (x : CubeCoordinates ι) (i : ι) : Bool := decide (i ∈ x.leftDivisor)
def rightBit (x : CubeCoordinates ι) (i : ι) : Bool := decide (i ∈ x.rightDivisor)

def Admissible (x : CubeCoordinates ι) : Prop :=
  x.leftDivisor ⊆ x.support ∧ x.rightDivisor ⊆ x.support

theorem support_pos (x : CubeCoordinates ι) (i : ι) (hi : i ∈ x.support) :
    0 < x.leftExponent i+x.rightExponent i := by
  simp only [support,Finset.mem_union,Finsupp.mem_support_iff] at hi
  omega

theorem left_off (x : CubeCoordinates ι) (i : ι) (hi : i ∉ x.support) :
    x.leftExponent i=0 := by
  by_contra hv
  exact hi (Finset.mem_union_left _ (Finsupp.mem_support_iff.mpr hv))

theorem right_off (x : CubeCoordinates ι) (i : ι) (hi : i ∉ x.support) :
    x.rightExponent i=0 := by
  by_contra hv
  exact hi (Finset.mem_union_right _ (Finsupp.mem_support_iff.mpr hv))

theorem aLabel_left (p : ι → O) (x : CubeCoordinates ι) (hx : x.Admissible) :
    aLabel p x.support x.leftBit = ∏ i ∈ x.leftDivisor,p i := by
  simp only [aLabel,primeProduct,leftBit,FirstPassCubeLabels.bit,decide_eq_true_eq]
  simp_rw [apply_ite, pow_one, pow_zero]
  rw [← Finset.prod_filter]
  have he : x.support.filter (fun i => i ∈ x.leftDivisor)=x.leftDivisor := by
    ext i
    simp only [Finset.mem_filter]
    exact and_iff_right_of_imp (fun hi => hx.1 hi)
  rw [he]

theorem aLabel_right (p : ι → O) (x : CubeCoordinates ι) (hx : x.Admissible) :
    aLabel p x.support x.rightBit = ∏ i ∈ x.rightDivisor,p i := by
  simp only [aLabel,primeProduct,rightBit,FirstPassCubeLabels.bit,decide_eq_true_eq]
  simp_rw [apply_ite, pow_one, pow_zero]
  rw [← Finset.prod_filter]
  have he : x.support.filter (fun i => i ∈ x.rightDivisor)=x.rightDivisor := by
    ext i
    simp only [Finset.mem_filter]
    exact and_iff_right_of_imp (fun hi => hx.2 hi)
  rw [he]

end CubeCoordinates

@[ext] structure GlobalSecondData (ι : Type*) where
  cube : CubeCoordinates ι
  firstCommon : Finset ι
  common : Finset ι
  firstDivisor : Finset ι
  source : SecondExpansionData ι

variable {ι : Type*} [DecidableEq ι]
  (p : ι → O) [∀ i, (Ideal.span {p i}).IsMaximal]

def globalSecondTuple (x : GlobalSecondData ι) : SecondPassFiber.OldTuple :=
  actualSecondTuple p x.cube.support x.common x.firstDivisor x.source.divisor x.source.overlap
    x.cube.leftExponent x.cube.rightExponent x.cube.leftBit x.cube.rightBit x.source.frequency

def globalSecondFixedTriple (x : GlobalSecondData ι) : Ideal O × Ideal O × Ideal O :=
  (Ideal.span {b0Label p x.cube.support
    (fun i => x.cube.leftExponent i+x.cube.rightExponent i) x.cube.leftBit x.cube.rightBit},
   ∏ i ∈ x.firstCommon,Ideal.span {p i},
   ∏ i ∈ x.source.sourceCommon\x.source.divisor,Ideal.span {p i})

def GlobalSecondAdmissible (x : GlobalSecondData ι) : Prop :=
  x.cube.Admissible ∧ x.source.divisor ⊆ x.source.sourceCommon ∧
  Disjoint x.common x.cube.support ∧ x.firstDivisor ⊆ x.common∪x.cube.support

omit [∀ (i : ι), (Ideal.span {p i}).IsMaximal] in
theorem globalSecondTuple_valid (x : GlobalSecondData ι) (hx : GlobalSecondAdmissible x) :
    SecondPassFiber.Valid (globalSecondTuple p x)
      (SecondPassFiber.newLabel (globalSecondTuple p x))
      (globalSecondFixedTriple p x).1
      (SecondPassFiber.newRow (globalSecondTuple p x)) := by
  unfold globalSecondTuple
  rw [actualSecondTuple_newLabel, actualSecondTuple_newRow]
  exact actualSecondTuple_valid p x.cube.support x.common x.firstDivisor x.source.divisor x.source.overlap
    hx.2.2.1 hx.2.2.2 x.cube.leftExponent x.cube.rightExponent x.cube.leftBit x.cube.rightBit
    x.cube.support_pos x.source.frequency

theorem globalSecondFixedTriple_nonzero (hp : ∀ i,p i ≠ 0) (x : GlobalSecondData ι) :
    (globalSecondFixedTriple p x).1 ≠ ⊥ ∧
    (globalSecondFixedTriple p x).2.1 ≠ ⊥ ∧
    (globalSecondFixedTriple p x).2.2 ≠ ⊥ := by
  refine ⟨?_, ?_, ?_⟩
  · change Ideal.span {_} ≠ ⊥
    intro h
    exact primeProduct_ne_zero p hp _ _ (Ideal.span_singleton_eq_bot.mp h)
  · exact Finset.prod_ne_zero_iff.mpr (fun i _ => NeZero.ne (Ideal.span {p i}))
  · exact Finset.prod_ne_zero_iff.mpr (fun i _ => NeZero.ne (Ideal.span {p i}))

omit [∀ (i : ι), (Ideal.span {p i}).IsMaximal] in
theorem globalSecondFixedTriple_norm_bounds (hp : ∀ i,p i ≠ 0)
    (x : GlobalSecondData ι) (B H J T R : ℝ) (hB : 0 ≤ B) (hJ : 0 < J)
    (hb₁ : ‖ringComplex (primeProduct p x.cube.support x.cube.leftExponent)‖^2 ≤ B)
    (hb₂ : ‖ringComplex (primeProduct p x.cube.support x.cube.rightExponent)‖^2 ≤ B)
    (hactive : ‖ringComplex (∏ i ∈ cubeActiveSupport x.cube.support
      (fun i => x.cube.leftExponent i+x.cube.rightExponent i) x.cube.leftBit x.cube.rightBit,p i)‖ ≤ H)
    (hlabel : J ≤ ‖ringComplex (jLabel p x.cube.support
      (fun i => x.cube.leftExponent i+x.cube.rightExponent i) x.cube.leftBit x.cube.rightBit)‖^2)
    (ht : primeProductNorm p x.firstCommon ≤ T)
    (hr : primeProductNorm p (x.source.sourceCommon\x.source.divisor) ≤ R) :
    (Ideal.absNorm (globalSecondFixedTriple p x).1 : ℝ) ≤ B*H/J ∧
    (Ideal.absNorm (globalSecondFixedTriple p x).2.1 : ℝ) ≤ T ∧
    (Ideal.absNorm (globalSecondFixedTriple p x).2.2 : ℝ) ≤ R := by
  obtain ⟨_,_,hb0⟩ := cube_label_norm_bounds p hp x.cube.support
    x.cube.leftExponent x.cube.rightExponent x.cube.leftBit x.cube.rightBit
    x.cube.support_pos B hB hb₁ hb₂
  refine ⟨?_,?_,?_⟩
  · change (Ideal.absNorm (Ideal.span {_}) : ℝ) ≤ _
    rw [← ringComplex_norm_sq_eq_absNorm_span]
    apply hb0.trans
    exact div_le_div₀ (mul_nonneg hB ((norm_nonneg _).trans hactive))
      (mul_le_mul_of_nonneg_left hactive hB) hJ hlabel
  · exact (primeProductNorm_eq_ideal_norm p _).symm ▸ ht
  · exact (primeProductNorm_eq_ideal_norm p _).symm ▸ hr


end SecondPassArithmetic

namespace SecondPassArithmetic
open Eisenstein SchwartzPlanePoisson FirstPassCubeLabels
open scoped Classical

/-- Three ideal norm bounds control the number of fixed divisor triples. -/
theorem fixed_triple_count
    (s : Finset (Ideal O × Ideal O × Ideal O)) (B T W : ℝ)
    (hB : 1 ≤ B) (hT : 1 ≤ T) (hW : 1 ≤ W)
    (hN : ∀ x ∈ s, (Ideal.absNorm x.1 : ℝ) ≤ B ∧
      (Ideal.absNorm x.2.1 : ℝ) ≤ T ∧ (Ideal.absNorm x.2.2 : ℝ) ≤ W) :
    (s.card : ℝ) ≤ (diagonalControl sieveCutoff) ^ 3 * B * T * W := by
  let a := s.image Prod.fst
  let b := s.image (fun x => x.2.1)
  let c := s.image (fun x => x.2.2)
  have hsub : s ⊆ a ×ˢ (b ×ˢ c) := by
    intro x hx
    exact Finset.mem_product.mpr ⟨Finset.mem_image.mpr ⟨x, hx, rfl⟩,
      Finset.mem_product.mpr ⟨Finset.mem_image.mpr ⟨x, hx, rfl⟩,
        Finset.mem_image.mpr ⟨x, hx, rfl⟩⟩⟩
  have ha : (a.card : ℝ) ≤ diagonalControl sieveCutoff * B := by
    apply finite_ideal_card_bound a B hB
    intro I hI
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hI
    exact (hN x hx).1
  have hb : (b.card : ℝ) ≤ diagonalControl sieveCutoff * T := by
    apply finite_ideal_card_bound b T hT
    intro I hI
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hI
    exact (hN x hx).2.1
  have hc : (c.card : ℝ) ≤ diagonalControl sieveCutoff * W := by
    apply finite_ideal_card_bound c W hW
    intro I hI
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hI
    exact (hN x hx).2.2
  have hs : (s.card : ℝ) ≤ (a.card : ℝ) * ((b.card : ℝ) * c.card) := by
    have hcard := Finset.card_le_card hsub
    simp only [Finset.card_product] at hcard
    exact_mod_cast hcard
  apply hs.trans
  calc
    _ ≤ (diagonalControl sieveCutoff * B) *
        ((diagonalControl sieveCutoff * T) * (diagonalControl sieveCutoff * W)) :=
      mul_le_mul ha
        (mul_le_mul hb hc (Nat.cast_nonneg _) ((Nat.cast_nonneg _).trans hb))
        (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)) ((Nat.cast_nonneg _).trans ha)
    _ = _ := by ring

variable {ι : Type*} [DecidableEq ι]
  (p : ι → O) [∀ i, (Ideal.span {p i}).IsMaximal]

theorem globalSecondFixedTriple_count (hp : ∀ i,p i ≠ 0)
    (s : Finset (GlobalSecondData ι)) (B H J T R : ℝ)
    (hB : 0 ≤ B) (hJ : 0 < J) (hscale : 1 ≤ B*H/J) (hT : 1 ≤ T) (hR : 1 ≤ R)
    (hb₁ : ∀ x∈s, ‖ringComplex (primeProduct p x.cube.support x.cube.leftExponent)‖^2 ≤ B)
    (hb₂ : ∀ x∈s, ‖ringComplex (primeProduct p x.cube.support x.cube.rightExponent)‖^2 ≤ B)
    (hactive : ∀ x∈s, ‖ringComplex (∏ i ∈ cubeActiveSupport x.cube.support
      (fun i => x.cube.leftExponent i+x.cube.rightExponent i) x.cube.leftBit x.cube.rightBit,p i)‖ ≤ H)
    (hlabel : ∀ x∈s, J ≤ ‖ringComplex (jLabel p x.cube.support
      (fun i => x.cube.leftExponent i+x.cube.rightExponent i) x.cube.leftBit x.cube.rightBit)‖^2)
    (ht : ∀ x∈s, primeProductNorm p x.firstCommon ≤ T)
    (hr : ∀ x∈s, primeProductNorm p (x.source.sourceCommon\x.source.divisor) ≤ R) :
    ((s.image (globalSecondFixedTriple p)).card : ℝ) ≤ (diagonalControl sieveCutoff)^3*(B*H/J)*T*R := by
  apply fixed_triple_count _ _ _ _ hscale hT hR
  intro q hq
  obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hq
  exact globalSecondFixedTriple_norm_bounds p hp x B H J T R hB hJ
      (hb₁ x hx) (hb₂ x hx) (hactive x hx) (hlabel x hx) (ht x hx) (hr x hx)

omit [∀ (i : ι), (Ideal.span {p i}).IsMaximal] in
theorem sum_globalSecondFixedTriple {M : Type*} [AddCommMonoid M]
    (s : Finset (GlobalSecondData ι)) (f : GlobalSecondData ι → M) :
    ∑ x∈s,f x = ∑ q∈s.image (globalSecondFixedTriple p),
      ∑ x∈s with globalSecondFixedTriple p x=q,f x := by
  symm
  exact Finset.sum_fiberwise_of_maps_to (fun x hx => Finset.mem_image.mpr ⟨x,hx,rfl⟩) f

variable (hinj : Function.Injective (fun i => Ideal.span {p i}))
include hinj

theorem globalSecondTuple_cube_eq {x y : GlobalSecondData ι}
    (hx : x.cube.Admissible) (hy : y.cube.Admissible)
    (h : globalSecondTuple p x=globalSecondTuple p y) : x.cube=y.cube := by
  have h₁ := congrArg (fun z : SecondPassFiber.OldTuple => z.core 4) h
  have h₂ := congrArg SecondPassFiber.OldTuple.b2 h
  have hA₁ := congrArg (fun z : SecondPassFiber.OldTuple => z.core 5) h
  have hA₂ := congrArg (fun z : SecondPassFiber.OldTuple => z.core 6) h
  change Ideal.span {primeProduct p x.cube.support x.cube.leftExponent} =
    Ideal.span {primeProduct p y.cube.support y.cube.leftExponent} at h₁
  change Ideal.span {primeProduct p x.cube.support x.cube.rightExponent} =
    Ideal.span {primeProduct p y.cube.support y.cube.rightExponent} at h₂
  have hv₁ := primeProduct_span_exponents_eq p hinj x.cube.support y.cube.support
    x.cube.leftExponent y.cube.leftExponent x.cube.left_off y.cube.left_off h₁
  have hv₂ := primeProduct_span_exponents_eq p hinj x.cube.support y.cube.support
    x.cube.rightExponent y.cube.rightExponent x.cube.right_off y.cube.right_off h₂
  change Ideal.span {aLabel p x.cube.support x.cube.leftBit} =
    Ideal.span {aLabel p y.cube.support y.cube.leftBit} at hA₁
  change Ideal.span {aLabel p x.cube.support x.cube.rightBit} =
    Ideal.span {aLabel p y.cube.support y.cube.rightBit} at hA₂
  rw [CubeCoordinates.aLabel_left p x.cube hx,CubeCoordinates.aLabel_left p y.cube hy,
    span_finset_prime_product,span_finset_prime_product] at hA₁
  rw [CubeCoordinates.aLabel_right p x.cube hx,CubeCoordinates.aLabel_right p y.cube hy,
    span_finset_prime_product,span_finset_prime_product] at hA₂
  apply CubeCoordinates.ext
  · exact Finsupp.ext (congrFun hv₁)
  · exact Finsupp.ext (congrFun hv₂)
  · exact primeIdealFamily_product_injective _ hinj hA₁
  · exact primeIdealFamily_product_injective _ hinj hA₂

theorem globalSecondEncoding_injective {x y : GlobalSecondData ι}
    (hx : GlobalSecondAdmissible x) (hy : GlobalSecondAdmissible y)
    (ht : globalSecondFixedTriple p x=globalSecondFixedTriple p y)
    (h : globalSecondTuple p x=globalSecondTuple p y) : x=y := by
  have hc := globalSecondTuple_cube_eq p hinj hx.1 hy.1 h
  have hA := congrArg (fun q : Ideal O × Ideal O × Ideal O => q.2.1) ht
  have hR := congrArg (fun q : Ideal O × Ideal O × Ideal O => q.2.2) ht
  have hC := congrArg (fun z : SecondPassFiber.OldTuple => z.core 1) h
  have hD := congrArg (fun z : SecondPassFiber.OldTuple => z.core 7) h
  have hE := congrArg (fun z : SecondPassFiber.OldTuple => z.core 2) h
  have hV := congrArg SecondPassFiber.OldTuple.v h
  have hk := congrArg SecondPassFiber.OldTuple.row h
  have hA' : x.firstCommon=y.firstCommon := primeIdealFamily_product_injective _ hinj hA
  have hC' : x.common=y.common := primeIdealFamily_product_injective _ hinj hC
  have hD' : x.firstDivisor=y.firstDivisor := primeIdealFamily_product_injective _ hinj hD
  have hE' : x.source.divisor=y.source.divisor := primeIdealFamily_product_injective _ hinj hE
  have hV' : x.source.overlap=y.source.overlap := primeIdealFamily_product_injective _ hinj hV
  have hR' : x.source.sourceCommon\x.source.divisor=y.source.sourceCommon\y.source.divisor :=
    primeIdealFamily_product_injective _ hinj hR
  have hG : x.source.sourceCommon=y.source.sourceCommon := by
    calc
      _ = x.source.divisor ∪ (x.source.sourceCommon\x.source.divisor) :=
        (Finset.union_sdiff_of_subset hx.2.1).symm
      _ = y.source.divisor ∪ (y.source.sourceCommon\y.source.divisor) := by rw [hR',hE']
      _ = _ := Finset.union_sdiff_of_subset hy.2.1
  have hk' : x.source.frequency = y.source.frequency := by
    change (subsetProductUnit p x.firstDivisor : O) *
        (subsetProductUnit p x.source.divisor : O) * x.source.frequency =
      (subsetProductUnit p y.firstDivisor : O) *
        (subsetProductUnit p y.source.divisor : O) * y.source.frequency at hk
    rw [hD', hE'] at hk
    exact mul_left_cancel₀ (mul_ne_zero (Units.ne_zero _) (Units.ne_zero _)) hk
  exact GlobalSecondData.ext hc hA' hC' hD' (SecondExpansionData.ext hG hE' hV' hk')

omit hinj in
theorem globalSecond_fiber_card (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ {ι : Type*} [DecidableEq ι]
      (p : ι → O) [∀ i, (Ideal.span {p i}).IsMaximal]
      (hinj : Function.Injective (fun i => Ideal.span {p i})) (s : Finset (GlobalSecondData ι))
      (q : Ideal O × Ideal O × Ideal O) (f : Ideal O) (y : O),
      (∀ x∈s,GlobalSecondAdmissible x) → f ≠ ⊥ → q.1 ≠ ⊥ →
      (∀ x∈s,globalSecondFixedTriple p x=q) →
      (∀ x∈s,SecondPassFiber.newLabel (globalSecondTuple p x)=f) →
      (∀ x∈s,SecondPassFiber.newRow (globalSecondTuple p x)=y) →
      (s.card : ℝ) ≤ C*((Ideal.absNorm f : ℝ)*Ideal.absNorm q.1)^ε := by
  obtain ⟨C,hC,hbound⟩ := SecondPassFiber.valid_tuple_small_power ε hε
  refine ⟨C,hC,?_⟩
  intro ι _ p _ hinj s q f y hs hf hq htr hlabel hrow
  have hi : Set.InjOn (globalSecondTuple p) s := by
    intro x hx z hz he
    exact globalSecondEncoding_injective p hinj (hs x hx) (hs z hz)
      ((htr x hx).trans (htr z hz).symm) he
  rw [← Finset.card_image_of_injOn hi]
  apply hbound _ f q.1 y hf hq
  intro t ht
  obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp ht
  have hv := globalSecondTuple_valid p x (hs x hx)
  simpa only [htr x hx,hlabel x hx,hrow x hx] using hv

end SecondPassArithmetic

namespace FirstPassCubeLabels
open Eisenstein SchwartzPlanePoisson SecondPassArithmetic CubicJacobi
open scoped Classical

def crossSymbol {ι : Type*} (p : ι → O) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hg : ∀ i, lambda ∉ Ideal.span {p i}) (i k : ι) : ℂ :=
  complexSexticChar (Ideal.span {p i}) (hg i) (Ideal.Quotient.mk (Ideal.span {p i}) (p k))

def quadraticCrossPhase {ι : Type*} (p : ι → O) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hg : ∀ i, lambda ∉ Ideal.span {p i}) (S T : Finset ι) : ℂ :=
  ∏ i ∈ S, ∏ k ∈ T, crossSymbol p hg i k ^ 3 * crossSymbol p hg k i ^ 3

lemma cross_square_primary {ι : Type*} (p : ι → O)
    [∀ i, (Ideal.span {p i}).IsMaximal] (hg : ∀ i, lambda ∉ Ideal.span {p i})
    (hpr : ∀ i, lambda ^ 2 ∣ p i - 1) (i k : ι) :
    crossSymbol p hg i k ^ 2 = crossSymbol p hg k i ^ 2 := by
  have hi := sexticRow_square_symbol p hg {i} (p k)
  have hk := sexticRow_square_symbol p hg {k} (p i)
  simp only [primeSubsetRow, Finset.prod_singleton] at hi hk
  rw [crossSymbol, crossSymbol, hi, hk, symbol_reciprocity _ _ (hpr k) (hpr i)]

private theorem cross_sixth {ι : Type*}
    (p : ι → O) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i, lambda ∉ Ideal.span {p i}) (i k : ι) (hik : i ≠ k) :
    crossSymbol p hg i k ^ 6 = 1 := by
  have hnot : p k ∉ Ideal.span {p i} := by
    intro hm
    have hle : Ideal.span {p k} ≤ Ideal.span {p i} :=
      Ideal.span_le.mpr (Set.singleton_subset_iff.mpr hm)
    have ht := (hcop hik).sup_eq
    rw [sup_eq_left.mpr hle] at ht
    exact (inferInstance : (Ideal.span {p i}).IsMaximal).ne_top ht
  have hm : primeCoprimeMask p {i} (p k) = 1 := by
    rw [primeCoprimeMask_indicator]
    apply if_pos
    intro j hj hd
    have hji := Finset.mem_singleton.mp hj
    subst j
    exact hnot (Ideal.mem_span_singleton.mpr hd)
  simpa only [primeSubsetRow, Finset.prod_singleton, crossSymbol] using
    (row_sixth p hg {i} (p k)).trans hm

theorem reverse_cross_eq_quadratic {ι : Type*}
    (p : ι → O) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i, lambda ∉ Ideal.span {p i})
    (hpr : ∀ i, lambda ^ 2 ∣ p i - 1) (i k : ι) (hik : i ≠ k) :
    crossSymbol p hg k i = crossSymbol p hg i k *
      (crossSymbol p hg i k ^ 3 * crossSymbol p hg k i ^ 3) := by
  have hr : crossSymbol p hg i k ^ 2 = crossSymbol p hg k i ^ 2 :=
    cross_square_primary p hg hpr i k
  symm
  calc
    _ = crossSymbol p hg i k ^ 4 *
        (crossSymbol p hg k i ^ 2 * crossSymbol p hg k i) := by ring
    _ = crossSymbol p hg i k ^ 6 * crossSymbol p hg k i := by rw [← hr]; ring
    _ = _ := by rw [cross_sixth p hcop hg i k hik, one_mul]

private theorem local_quadratic_sq {ι : Type*}
    (p : ι → O) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i, lambda ∉ Ideal.span {p i}) (i k : ι) (hik : i ≠ k) :
    (crossSymbol p hg i k ^ 3 * crossSymbol p hg k i ^ 3) ^ 2 = 1 := by
  rw [mul_pow, ← pow_mul, ← pow_mul]
  norm_num only [show 3 * 2 = 6 by decide, cross_sixth p hcop hg i k hik,
    cross_sixth p hcop hg k i hik.symm, one_mul]

private theorem crt_exponent_table (side parityBit ε₁ ε₂ : Bool)
    (he : conductorExponent parityBit ε₁ ε₂ ≠ 0) :
    ((if side then 5 else 1) + (conductorExponent parityBit ε₁ ε₂).val) % 6 =
      ((if side then 5 else 1) * crtExponent side parityBit ε₁ ε₂) % 6 := by
  cases side <;> cases parityBit <;> cases ε₁ <;> cases ε₂ <;>
    first | exact False.elim (he (by decide)) | decide

theorem active_cube_cross_local {ι : Type*}
    (p : ι → O) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i, lambda ∉ Ideal.span {p i})
    (hpr : ∀ i, lambda ^ 2 ∣ p i - 1) (i k : ι) (hik : i ≠ k)
    (side parityBit ε₁ ε₂ : Bool) (he : conductorExponent parityBit ε₁ ε₂ ≠ 0) :
    crossSymbol p hg i k ^ (if side then 5 else 1) *
      crossSymbol p hg k i ^ (conductorExponent parityBit ε₁ ε₂).val =
    (if side then star (crossSymbol p hg i k ^ crtExponent side parityBit ε₁ ε₂)
      else crossSymbol p hg i k ^ crtExponent side parityBit ε₁ ε₂) *
      (crossSymbol p hg i k ^ 3 * crossSymbol p hg k i ^ 3) ^
        (conductorExponent parityBit ε₁ ε₂).val := by
  let x := crossSymbol p hg i k
  let q := crossSymbol p hg i k ^ 3 * crossSymbol p hg k i ^ 3
  have hrev : crossSymbol p hg k i = x * q := reverse_cross_eq_quadratic p hcop hg hpr i k hik
  have h6 : x ^ 6 = 1 := cross_sixth p hcop hg i k hik
  have hs : star x = x ^ 5 := by
    simpa only [primeSubsetRow, Finset.prod_singleton, crossSymbol, x] using
      sexticRow_star p hg {i} (p k)
  calc
    _ = x ^ ((if side then 5 else 1) + (conductorExponent parityBit ε₁ ε₂).val) *
        q ^ (conductorExponent parityBit ε₁ ε₂).val := by rw [hrev, mul_pow, pow_add]; ring
    _ = _ := by
      congr 1
      cases side
      · change x ^ (1 + (conductorExponent parityBit ε₁ ε₂).val) = x ^ crtExponent false parityBit ε₁ ε₂
        conv_lhs => rw [pow_eq_pow_mod _ h6]
        conv_rhs => rw [pow_eq_pow_mod _ h6]
        congr 1
        simpa only [Bool.false_eq_true, ↓reduceIte, one_mul] using crt_exponent_table false parityBit ε₁ ε₂ he
      · change x ^ (5 + (conductorExponent parityBit ε₁ ε₂).val) = star (x ^ crtExponent true parityBit ε₁ ε₂)
        rw [star_pow, hs, ← pow_mul]
        conv_lhs => rw [pow_eq_pow_mod _ h6]
        conv_rhs => rw [pow_eq_pow_mod _ h6]
        congr 1
        exact crt_exponent_table true parityBit ε₁ ε₂ he

def cubeOddSupport {ι : Type*} (B : Finset ι) (v : ι → ℕ) (ε₁ ε₂ : ι → Bool) : Finset ι :=
  B.filter fun k => (conductorExponent (parity (v k)) (ε₁ k) (ε₂ k)).val % 2 = 1

def mixedCubeCross {ι : Type*}
    (p : ι → O) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hg : ∀ i, lambda ∉ Ideal.span {p i}) (U B : Finset ι)
    (v : ι → ℕ) (ε₁ ε₂ : ι → Bool) (side : Bool) : ℂ :=
  ∏ i ∈ U, ∏ k ∈ B.filter (fun k => conductorExponent (parity (v k)) (ε₁ k) (ε₂ k) ≠ 0),
    crossSymbol p hg i k ^ (if side then 5 else 1) *
      crossSymbol p hg k i ^ (conductorExponent (parity (v k)) (ε₁ k) (ε₂ k)).val

theorem mixedCubeCross_eq_ordered {ι : Type*}
    (p : ι → O) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hg : ∀ i, lambda ∉ Ideal.span {p i}) (U B : Finset ι)
    (v : ι → ℕ) (ε₁ ε₂ : ι → Bool) (side : Bool) :
    mixedCubeCross p hg U B v ε₁ ε₂ side =
      (∏ i ∈ U, ∏ k ∈ B.filter (fun k => conductorExponent (parity (v k)) (ε₁ k) (ε₂ k) ≠ 0),
        crossSymbol p hg i k ^ (if side then 5 else 1)) *
      (∏ k ∈ B.filter (fun k => conductorExponent (parity (v k)) (ε₁ k) (ε₂ k) ≠ 0),
        ∏ i ∈ U, crossSymbol p hg k i ^ (conductorExponent (parity (v k)) (ε₁ k) (ε₂ k)).val) := by
  rw [Finset.prod_comm (s := B.filter _) (t := U)]
  simp only [mixedCubeCross, Finset.prod_mul_distrib]

private theorem cube_cross_local_if {ι : Type*}
    (p : ι → O) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i, lambda ∉ Ideal.span {p i})
    (hpr : ∀ i, lambda ^ 2 ∣ p i - 1) (i k : ι) (hik : i ≠ k)
    (side parityBit ε₁ ε₂ : Bool) :
    (if conductorExponent parityBit ε₁ ε₂ ≠ 0 then
      crossSymbol p hg i k ^ (if side then 5 else 1) *
        crossSymbol p hg k i ^ (conductorExponent parityBit ε₁ ε₂).val else 1) =
    (if side then star (crossSymbol p hg i k ^ crtExponent side parityBit ε₁ ε₂)
      else crossSymbol p hg i k ^ crtExponent side parityBit ε₁ ε₂) *
      (if (conductorExponent parityBit ε₁ ε₂).val % 2 = 1 then
        crossSymbol p hg i k ^ 3 * crossSymbol p hg k i ^ 3 else 1) := by
  by_cases he : conductorExponent parityBit ε₁ ε₂ = 0
  · simp [he, crtExponent]
  · rw [if_pos he, active_cube_cross_local p hcop hg hpr i k hik side parityBit ε₁ ε₂ he]
    congr 1
    rw [pow_eq_pow_mod _ (local_quadratic_sq p hcop hg i k hik)]
    by_cases ho : (conductorExponent parityBit ε₁ ε₂).val % 2 = 1
    · simp [ho]
    · have hz : (conductorExponent parityBit ε₁ ε₂).val % 2 = 0 := by omega
      simp [ hz]

theorem mixedCubeCross_eq_row_quadratic {ι : Type*} [DecidableEq ι]
    (p : ι → O) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i, lambda ∉ Ideal.span {p i})
    (hpr : ∀ i, lambda ^ 2 ∣ p i - 1) (U B : Finset ι) (hd : Disjoint U B)
    (v : ι → ℕ) (ε₁ ε₂ : ι → Bool) (side : Bool) :
    mixedCubeCross p hg U B v ε₁ ε₂ side =
      (if side then star (primeSubsetRow p (fun i => complexSexticChar (Ideal.span {p i}) (hg i)) U
          (crtLabel p B v ε₁ ε₂ side))
        else primeSubsetRow p (fun i => complexSexticChar (Ideal.span {p i}) (hg i)) U
          (crtLabel p B v ε₁ ε₂ side)) *
      quadraticCrossPhase p hg U (cubeOddSupport B v ε₁ ε₂) := by
  have hr : primeSubsetRow p (fun i => complexSexticChar (Ideal.span {p i}) (hg i)) U
      (crtLabel p B v ε₁ ε₂ side) =
      ∏ i ∈ U, ∏ k ∈ B, crossSymbol p hg i k ^
        crtExponent side (parity (v k)) (ε₁ k) (ε₂ k) := by
    simp only [primeSubsetRow, crtLabel, primeProduct, map_prod, map_pow, crossSymbol]
  calc
    _ = (∏ i ∈ U, ∏ k ∈ B,
        if side then star (crossSymbol p hg i k ^ crtExponent side (parity (v k)) (ε₁ k) (ε₂ k))
        else crossSymbol p hg i k ^ crtExponent side (parity (v k)) (ε₁ k) (ε₂ k)) *
      (∏ i ∈ U, ∏ k ∈ B,
        if (conductorExponent (parity (v k)) (ε₁ k) (ε₂ k)).val % 2 = 1 then
          crossSymbol p hg i k ^ 3 * crossSymbol p hg k i ^ 3 else 1) := by
      simp only [mixedCubeCross, Finset.prod_filter, ← Finset.prod_mul_distrib]
      apply Finset.prod_congr rfl
      intro i hi
      apply Finset.prod_congr rfl
      intro k hk
      apply cube_cross_local_if p hcop hg hpr i k
      exact fun he => Finset.disjoint_left.mp hd hi (he ▸ hk)
    _ = _ := by
      congr 1
      · rw [hr]
        cases side <;> simp only [Bool.false_eq_true, ↓reduceIte, star_prod]
      · simp only [quadraticCrossPhase, cubeOddSupport, Finset.prod_filter]


end FirstPassCubeLabels

namespace FirstPassCubeLabels
open Eisenstein SchwartzPlanePoisson SecondPassArithmetic
open scoped Classical

def localTraceGauss (p : O) (hp : p ≠ 0) [IsMaximal : (Ideal.span {p}).IsMaximal]
    (hg : lambda ∉ Ideal.span {p}) (e : ℕ) : ℂ :=
  residueRowGauss p hp (fun z =>
    (complexSexticChar (Ideal.span {p}) hg ^ e) (Ideal.Quotient.mk (Ideal.span {p}) z)) /
      (‖ringComplex p‖ : ℂ)

def gaussBlock {ι : Type*} [DecidableEq ι]
    (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hg : ∀ i, lambda ∉ Ideal.span {p i}) (S : Finset ι) (e : ι → ℕ) : ℂ :=
  ∏ i ∈ S, (∏ k ∈ S.erase i, crossSymbol p hg i k ^ e i) *
    localTraceGauss (p i) (hp i) (hg i) (e i)

def blockCross {ι : Type*}
    (p : ι → O) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hg : ∀ i, lambda ∉ Ideal.span {p i}) (S T : Finset ι) (e : ι → ℕ) : ℂ :=
  ∏ i ∈ S, ∏ k ∈ T,
    crossSymbol p hg i k ^ e i * crossSymbol p hg k i ^ e k

theorem gaussBlock_union {ι : Type*} [DecidableEq ι]
    (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hg : ∀ i, lambda ∉ Ideal.span {p i}) (S T : Finset ι) (hd : Disjoint S T)
    (e : ι → ℕ) :
    gaussBlock p hp hg (S ∪ T) e =
      gaussBlock p hp hg S e * gaussBlock p hp hg T e * blockCross p hg S T e := by
  have hS (i : ι) (hi : i ∈ S) :
      (∏ k ∈ (S ∪ T).erase i, crossSymbol p hg i k ^ e i) =
      (∏ k ∈ S.erase i, crossSymbol p hg i k ^ e i) *
        ∏ k ∈ T, crossSymbol p hg i k ^ e i := by
    have hn : i ∉ T := fun h => Finset.disjoint_left.mp hd hi h
    rw [Finset.erase_union_distrib, Finset.erase_eq_of_notMem hn,
      Finset.prod_union (hd.mono_left (Finset.erase_subset _ _))]
  have hT (i : ι) (hi : i ∈ T) :
      (∏ k ∈ (S ∪ T).erase i, crossSymbol p hg i k ^ e i) =
      (∏ k ∈ T.erase i, crossSymbol p hg i k ^ e i) *
        ∏ k ∈ S, crossSymbol p hg i k ^ e i := by
    have hn : i ∉ S := fun h => Finset.disjoint_left.mp hd h hi
    rw [Finset.union_comm S T, Finset.erase_union_distrib, Finset.erase_eq_of_notMem hn,
      Finset.prod_union (hd.symm.mono_left (Finset.erase_subset _ _))]
  have hpS : (∏ i ∈ S, (∏ k ∈ (S ∪ T).erase i, crossSymbol p hg i k ^ e i) *
      localTraceGauss (p i) (hp i) (hg i) (e i)) =
      gaussBlock p hp hg S e * (∏ i ∈ S, ∏ k ∈ T, crossSymbol p hg i k ^ e i) := by
    rw [gaussBlock, ← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro i hi
    rw [hS i hi]
    ring
  have hpT : (∏ i ∈ T, (∏ k ∈ (S ∪ T).erase i, crossSymbol p hg i k ^ e i) *
      localTraceGauss (p i) (hp i) (hg i) (e i)) =
      gaussBlock p hp hg T e * (∏ i ∈ T, ∏ k ∈ S, crossSymbol p hg i k ^ e i) := by
    rw [gaussBlock, ← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro i hi
    rw [hT i hi]
    ring
  rw [gaussBlock, Finset.prod_union hd, hpS, hpT,
    Finset.prod_comm (s := T) (t := S)]
  simp only [blockCross, Finset.prod_mul_distrib]
  ring

theorem gaussBlock_congr {ι : Type*} [DecidableEq ι]
    (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hg : ∀ i, lambda ∉ Ideal.span {p i}) (S : Finset ι) (e f : ι → ℕ)
    (he : ∀ i ∈ S, e i = f i) : gaussBlock p hp hg S e = gaussBlock p hp hg S f := by
  apply Finset.prod_congr rfl
  intro i hi
  rw [he i hi]

def blockCubeExponent {ι : Type*} [DecidableEq ι] (U : Finset ι)
    (v : ι → ℕ) (ε₁ ε₂ : ι → Bool) (side : Bool) (i : ι) : ℕ :=
  if i ∈ U then (if side then 5 else 1)
  else (conductorExponent (parity (v i)) (ε₁ i) (ε₂ i)).val

theorem gaussBlock_cube_partition {ι : Type*} [DecidableEq ι]
    (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hg : ∀ i, lambda ∉ Ideal.span {p i}) (U B : Finset ι) (hd : Disjoint U B)
    (v : ι → ℕ) (ε₁ ε₂ : ι → Bool) (side : Bool) :
    gaussBlock p hp hg (U ∪ cubeActiveSupport B v ε₁ ε₂)
      (blockCubeExponent U v ε₁ ε₂ side) =
    gaussBlock p hp hg U (fun _ => if side then 5 else 1) *
      gaussBlock p hp hg (cubeActiveSupport B v ε₁ ε₂)
        (fun k => (conductorExponent (parity (v k)) (ε₁ k) (ε₂ k)).val) *
      mixedCubeCross p hg U B v ε₁ ε₂ side := by
  have hdc : Disjoint U (cubeActiveSupport B v ε₁ ε₂) := hd.mono_right (Finset.filter_subset _ _)
  have hU : ∀ i ∈ U, blockCubeExponent U v ε₁ ε₂ side i = (if side then 5 else 1) := by
    intro i hi
    simp only [blockCubeExponent, if_pos hi]
  have hB : ∀ i ∈ cubeActiveSupport B v ε₁ ε₂, blockCubeExponent U v ε₁ ε₂ side i =
      (conductorExponent (parity (v i)) (ε₁ i) (ε₂ i)).val := by
    intro i hi
    exact if_neg (fun hu => Finset.disjoint_left.mp hdc hu hi)
  rw [gaussBlock_union p hp hg U _ hdc,
    gaussBlock_congr p hp hg U _ _ hU, gaussBlock_congr p hp hg _ _ _ hB]
  congr 1
  apply Finset.prod_congr rfl
  intro i hi
  apply Finset.prod_congr rfl
  intro k hk
  rw [hU i hi, hB k hk]


theorem gaussBlock_cube_partition_row {ι : Type*} [DecidableEq ι]
    (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i, lambda ∉ Ideal.span {p i}) (hpr : ∀ i, lambda ^ 2 ∣ p i - 1)
    (U B : Finset ι) (hd : Disjoint U B) (v : ι → ℕ) (ε₁ ε₂ : ι → Bool) (side : Bool) :
    gaussBlock p hp hg (U ∪ cubeActiveSupport B v ε₁ ε₂)
      (blockCubeExponent U v ε₁ ε₂ side) =
    gaussBlock p hp hg U (fun _ => if side then 5 else 1) *
      gaussBlock p hp hg (cubeActiveSupport B v ε₁ ε₂)
        (fun k => (conductorExponent (parity (v k)) (ε₁ k) (ε₂ k)).val) *
      ((if side then star (primeSubsetRow p
          (fun i => complexSexticChar (Ideal.span {p i}) (hg i)) U (crtLabel p B v ε₁ ε₂ side))
        else primeSubsetRow p (fun i => complexSexticChar (Ideal.span {p i}) (hg i)) U
          (crtLabel p B v ε₁ ε₂ side)) * quadraticCrossPhase p hg U (cubeOddSupport B v ε₁ ε₂)) := by
  rw [gaussBlock_cube_partition p hp hg U B hd,
    mixedCubeCross_eq_row_quadratic p hcop hg hpr U B hd]

theorem blockCross_two_eq_row_four {ι : Type*}
    (p : ι → O) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hg : ∀ i, lambda ∉ Ideal.span {p i})
    (hpr : ∀ i, lambda ^ 2 ∣ p i - 1) (S T : Finset ι) :
    blockCross p hg S T (fun _ => 2) =
      primeSubsetRow p (fun i => complexSexticChar (Ideal.span {p i}) (hg i)) S (∏ k ∈ T, p k) ^ 4 := by
  simp only [blockCross, primeSubsetRow, map_prod, ← Finset.prod_pow]
  apply Finset.prod_congr rfl
  intro i hi
  apply Finset.prod_congr rfl
  intro k hk
  have hr : crossSymbol p hg i k ^ 2 = crossSymbol p hg k i ^ 2 :=
    cross_square_primary p hg hpr i k
  change crossSymbol p hg i k ^ 2 * crossSymbol p hg k i ^ 2 = crossSymbol p hg i k ^ 4
  rw [← hr]
  ring


end FirstPassCubeLabels

end GaloisForLFunctions.MetaplecticMobiusDescent.CubicEisenstein
