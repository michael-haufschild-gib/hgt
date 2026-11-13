/-
Initial ray attachment adapted from OpenAI's formalization, Apache-2.0.
See LICENSE and NOTICE in the parent directory for source attribution.
-/
import GaloisForLFunctions.MetaplecticMobiusDescent.MeanSquare.InitialMeanSquareRows
import GaloisForLFunctions.MetaplecticMobiusDescent.Descent.InitialChildrenAndGenerators

/-!
# Initial ray attachment

Sources of the initial inverse arithmetic and their second ray coefficients. The total residue
phase of the mixed Gauss reflection becomes character twists by finite Fourier expansion;
clipped column energies and the physical kernel bridge.
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
open scoped Classical
open scoped Classical
open scoped Classical
open scoped Classical SchwartzMap
open MeasureTheory
open scoped BigOperators Classical ContDiff SchwartzMap FourierTransform
open MeasureTheory
open scoped BigOperators Classical SchwartzMap ContDiff

namespace InverseClippingProfiles
open InverseMoment Eisenstein SchwartzPlanePoisson JointLogSeparation MeasureTheory
open scoped BigOperators Classical SchwartzMap FourierTransform ContDiff
def firstRootExponent (y : Fin 9 → ℝ) : ℝ :=
  -y 3-y 4/2-y 5-(y 7+y 8)/2

def secondRootExponent (y : Fin 6 → ℝ) : ℝ :=
  -y 1-y 2-(y 4+y 5)/2

theorem first_root_coupled_identity (y : Fin 9 → ℝ) :
    firstRootExponent y = -y 3-y 4/2+(y 0+y 1)/2+y 2 -
      ((∑ i, firstLeftSlope i*y i)+(∑ i, firstRightSlope i*y i))/2 := by
  simp [firstRootExponent, firstLeftSlope, firstRightSlope, Fin.sum_univ_succ]
  ring

theorem second_root_coupled_identity (y : Fin 6 → ℝ) :
    secondRootExponent y = -y 1+y 0 -
      ((∑ i, secondLeftSlope i*y i)+(∑ i, secondRightSlope i*y i))/2 := by
  simp [secondRootExponent, secondLeftSlope, secondRightSlope, Fin.sum_univ_succ]
  ring

theorem first_root_budget (y : Fin 9 → ℝ) (L : ℝ)
    (h0 : |y 0| ≤ L) (h1 : |y 1| ≤ L) (h2 : |y 2| ≤ L)
    (h3 : |y 3| ≤ L) (h4 : |y 4| ≤ L)
    (hl : |∑ i, firstLeftSlope i*y i| ≤ L)
    (hr : |∑ i, firstRightSlope i*y i| ≤ L) :
    firstRootExponent y ≤ (9/2:ℝ)*L := by
  rw [first_root_coupled_identity]
  rcases abs_le.mp h0 with ⟨_, h0⟩
  rcases abs_le.mp h1 with ⟨_, h1⟩
  rcases abs_le.mp h2 with ⟨_, h2⟩
  rcases abs_le.mp h3 with ⟨h3, _⟩
  rcases abs_le.mp h4 with ⟨h4, _⟩
  rcases abs_le.mp hl with ⟨hl, _⟩
  rcases abs_le.mp hr with ⟨hr, _⟩
  linarith

theorem second_root_budget (y : Fin 6 → ℝ) (L : ℝ)
    (h0 : |y 0| ≤ L) (h1 : |y 1| ≤ L)
    (hl : |∑ i, secondLeftSlope i*y i| ≤ 4*L)
    (hr : |∑ i, secondRightSlope i*y i| ≤ 4*L) :
    secondRootExponent y ≤ 6*L := by
  rw [second_root_coupled_identity]
  rcases abs_le.mp h0 with ⟨_, h0⟩
  rcases abs_le.mp h1 with ⟨h1, _⟩
  rcases abs_le.mp hl with ⟨hl, _⟩
  rcases abs_le.mp hr with ⟨hr, _⟩
  linarith

def firstRootSlope : Fin 9 → ℝ := ![0,0,0,-1,-(1/2),-1,0,-(1/2),-(1/2)]
def secondRootSlope : Fin 6 → ℝ := ![0,-1,-1,0,-(1/2),-(1/2)]

lemma inverseNormWindow_exp (V : ℝ → ℂ) (y : ℝ) :
    inverseNormWindow V y = (Real.exp (-y) : ℂ)*V y := by
  simp only [inverseNormWindow, Real.exp_neg, Complex.ofReal_inv, div_eq_mul_inv]
  ring

lemma inverseRootWindow_exp (V : ℝ → ℂ) (y : ℝ) :
    inverseRootWindow V y = (Real.exp (-(y/2)) : ℂ)*V y := by
  rw [inverseRootWindow, ← Real.exp_half, Real.exp_neg, Complex.ofReal_inv]
  ring

theorem firstRootWindows_exp (V : Fin 9 → ℝ → ℂ) (i : Fin 9) (y : ℝ) :
    firstRootWindows V i y = (Real.exp (firstRootSlope i*y) : ℂ)*V i y := by
  fin_cases i <;> simp [firstRootWindows, firstRootSlope, inverseNormWindow_exp,
    inverseRootWindow_exp, neg_mul]
  all_goals left; congr 1; ring

theorem secondRootWindows_exp (V : Fin 6 → ℝ → ℂ) (i : Fin 6) (y : ℝ) :
    secondRootWindows V i y = (Real.exp (secondRootSlope i*y) : ℂ)*V i y := by
  fin_cases i <;> simp [secondRootWindows, secondRootSlope, inverseNormWindow_exp,
    inverseRootWindow_exp, neg_mul]
  all_goals left; congr 1; ring

theorem firstRootWindows_prod (V : Fin 9 → ℝ → ℂ) (y : Fin 9 → ℝ) :
    (∏ i, firstRootWindows V i (y i)) =
      (Real.exp (firstRootExponent y) : ℂ) * ∏ i, V i (y i) := by
  simp_rw [firstRootWindows_exp]
  rw [Finset.prod_mul_distrib, ← Complex.ofReal_prod, ← Real.exp_sum]
  congr 2
  simp only [firstRootSlope, firstRootExponent, Fin.sum_univ_succ,
    Matrix.cons_val_zero, Matrix.cons_val_succ, Matrix.cons_val_fin_one]
  norm_num
  ring_nf
  rfl

theorem secondRootWindows_prod (V : Fin 6 → ℝ → ℂ) (y : Fin 6 → ℝ) :
    (∏ i, secondRootWindows V i (y i)) =
      (Real.exp (secondRootExponent y) : ℂ) * ∏ i, V i (y i) := by
  simp_rw [secondRootWindows_exp]
  rw [Finset.prod_mul_distrib, ← Complex.ofReal_prod, ← Real.exp_sum]
  congr 2
  simp only [secondRootSlope, secondRootExponent, Fin.sum_univ_succ,
    Matrix.cons_val_zero, Matrix.cons_val_succ, Matrix.cons_val_fin_one]
  norm_num
  ring_nf
  rfl

theorem first_profile_normalized_identity (W₁ W₂ : ℝ → ℂ) (Φ : 𝓢(ℝ, ℂ))
    (V : Fin 9 → ℝ → ℂ) (R L : ℝ) (y : Fin 9 → ℝ) :
    (Real.exp (-(9/2:ℝ)*L) : ℂ)*firstPoissonProfile W₁ W₂ Φ V R y =
      (Real.exp (firstRootExponent y-(9/2:ℝ)*L) : ℂ) *
      (∏ i, V i (y i)) * W₁ (Real.exp (∑ i, firstLeftSlope i*y i)) *
      W₂ (Real.exp (∑ i, firstRightSlope i*y i)) *
      SchwartzPlanePoisson.paperRadialFourier Φ
        (R*Real.exp (∑ i, firstKernelSlope i*y i)) := by
  rw [firstPoissonProfile, firstRootWindows_prod]
  simp only [Real.exp_sub, div_eq_mul_inv, neg_mul, Real.exp_neg,
    Complex.ofReal_mul, Complex.ofReal_inv]
  ring

theorem second_profile_normalized_identity (W₁ W₂ : ℝ → ℂ) (Φ : 𝓢(ℝ, ℂ))
    (V : Fin 6 → ℝ → ℂ) (R L : ℝ) (y : Fin 6 → ℝ) :
    (Real.exp (-6*L) : ℂ)*secondPoissonProfile W₁ W₂ Φ V R y =
      (Real.exp (secondRootExponent y-6*L) : ℂ) *
      (∏ i, V i (y i)) * W₁ (Real.exp (∑ i, secondLeftSlope i*y i)) *
      W₂ (Real.exp (∑ i, secondRightSlope i*y i)) *
      SchwartzPlanePoisson.paperRadialFourier Φ
        (R*Real.exp (∑ i, secondKernelSlope i*y i)) := by
  rw [secondPoissonProfile, secondRootWindows_prod]
  simp only [Real.exp_sub, div_eq_mul_inv, neg_mul, Real.exp_neg,
    Complex.ofReal_mul, Complex.ofReal_inv]
  ring


end InverseClippingProfiles

namespace InverseInitialProfile
open InverseMoment Eisenstein SchwartzPlanePoisson JointLogSeparation MeasureTheory
open scoped BigOperators Classical SchwartzMap FourierTransform ContDiff
def clippedTwist (g : 𝓢(ℝ, ℂ)) (c θ : ℝ) : 𝓢(ℝ, ℂ) :=
  frequencyTwist (SchwartzMap.compSubConstCLM ℂ (-Real.log c) g) θ

@[simp] theorem clippedTwist_apply (g : 𝓢(ℝ, ℂ)) (c θ y : ℝ) :
    clippedTwist g c θ y = kernelLogPhase θ y * g (y + Real.log c) := by
  simp [clippedTwist]

def sourceDensity (g : 𝓢(ℝ, ℂ)) (c θ t : ℝ) : ℂ :=
  kernelLogPhase (t-θ) (Real.log c) * (𝓕 g) (t-θ)

theorem fourier_clippedTwist (g : 𝓢(ℝ, ℂ)) (c θ t : ℝ) :
    (𝓕 (clippedTwist g c θ)) t = sourceDensity g c θ t := by
  rw [SchwartzMap.fourier_coe]
  have he : (clippedTwist g c θ : ℝ → ℂ) =
      fun y => kernelLogPhase θ y * g (y + Real.log c) := by ext y; simp
  rw [he, InverseClippingProfiles.fourier_translated_twist]
  rfl

theorem sourceDensity_joint_measurable (g : 𝓢(ℝ, ℂ)) :
    StronglyMeasurable (fun p : (ℝ × ℝ) × ℝ => sourceDensity g p.1.1 p.1.2 p.2) := by
  unfold sourceDensity kernelLogPhase
  apply Measurable.stronglyMeasurable
  apply Measurable.mul
  · exact Complex.continuous_exp.measurable.comp (by fun_prop)
  · exact (𝓕 g : 𝓢(ℝ, ℂ)).continuous.measurable.comp (by fun_prop)

theorem sourceDensity_norm (g : 𝓢(ℝ, ℂ)) (c θ t : ℝ) :
    ‖sourceDensity g c θ t‖ = ‖(𝓕 g) (t-θ)‖ := by
  simp [sourceDensity, kernelLogPhase_norm]

theorem sourceDensity_moment_uniform (g : 𝓢(ℝ, ℂ)) (J : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ c θ : ℝ,
      Integrable (fun t : ℝ => (1+‖t‖)^J * ‖sourceDensity g c θ t‖) ∧
      (∫ t : ℝ, (1+‖t‖)^J * ‖sourceDensity g c θ t‖) ≤
        C*(1+‖θ‖)^(InverseClippingProfiles.momentOrder J) := by
  obtain ⟨C, hC, hb⟩ := InverseClippingProfiles.translated_twist_moment_uniform g J
  refine ⟨C, hC, ?_⟩
  intro c θ
  simpa only [InverseClippingProfiles.fourier_translated_twist, sourceDensity,
    SchwartzMap.fourier_coe] using hb (Real.log c) θ

def clippedSource (W : ℝ → ℂ) (c θ x : ℝ) : ℂ :=
  kernelLogPhase θ (Real.log x) * W (c*x)

theorem clipped_log_source (W : ℝ → ℂ) (a b : ℝ) (ha : 0 < a)
    (hs : Function.support W ⊆ Set.Icc a b) (hW : ContDiff ℝ ∞ W)
    {c : ℝ} (hc : 0 < c) (θ y : ℝ) :
    clippedTwist (CanonicalCubeSeparation.sourceLogProfile W a b ha hs hW) c θ y =
      clippedSource W c θ (Real.exp y) := by
  simp only [clippedTwist_apply, CanonicalCubeSeparation.sourceLogProfile_apply,
    clippedSource, Real.log_exp, Real.exp_add, Real.exp_log hc]
  rw [mul_comm (Real.exp y) c]

def rootExponent (y : Fin 6 → ℝ) : ℝ := -y 1-y 2-(y 4+y 5)/2

theorem root_coupled_identity (y : Fin 6 → ℝ) :
    rootExponent y = -y 1+y 0-((y 0+y 2+y 4)+(y 0+y 2+y 5))/2 := by
  unfold rootExponent
  ring

theorem root_budget (y : Fin 6 → ℝ) (L : ℝ)
    (hd : |y 1| ≤ L) (hC : |y 0| ≤ L)
    (hc₁ : |y 0+y 2+y 4| ≤ L) (hc₂ : |y 0+y 2+y 5| ≤ L) :
    rootExponent y ≤ 3*L := by
  rw [root_coupled_identity]
  have hd' := (abs_le.mp hd).1
  have hC' := (abs_le.mp hC).2
  have h1 := (abs_le.mp hc₁).1
  have h2 := (abs_le.mp hc₂).1
  linarith

def normalizedProfile (W₁ W₂ : ℝ → ℂ) (Φ : 𝓢(ℝ, ℂ))
    (V : Fin 6 → ℝ → ℂ) (R L : ℝ) (y : Fin 6 → ℝ) : ℂ :=
  (Real.exp (-3*L) : ℂ) * secondPoissonProfile W₁ W₂ Φ V R y

theorem normalizedProfile_exact (W₁ W₂ : ℝ → ℂ) (Φ : 𝓢(ℝ, ℂ))
    (V : Fin 6 → ℝ → ℂ) (R L : ℝ) (y : Fin 6 → ℝ) :
    normalizedProfile W₁ W₂ Φ V R L y =
      (Real.exp (rootExponent y-3*L) : ℂ) * (∏ i, V i (y i)) *
      W₁ (Real.exp (y 0+y 2+y 4)) * W₂ (Real.exp (y 0+y 2+y 5)) *
      paperRadialFourier Φ (R*Real.exp (y 3-y 1-2*y 2-y 4-y 5)) := by
  unfold normalizedProfile secondPoissonProfile
  rw [InverseClippingProfiles.secondRootWindows_prod]
  have hleft : (∑ i, secondLeftSlope i*y i) = y 0+y 2+y 4 := by
    simp [secondLeftSlope, Fin.sum_univ_succ]
    ring
  have hright : (∑ i, secondRightSlope i*y i) = y 0+y 2+y 5 := by
    simp [secondRightSlope, Fin.sum_univ_succ]
    ring
  have hker : (∑ i, secondKernelSlope i*y i) = y 3-y 1-2*y 2-y 4-y 5 := by
    simp [secondKernelSlope, Fin.sum_univ_succ]
    ring
  rw [hleft, hright, hker]
  change (Real.exp (-3*L) : ℂ) * (((Real.exp (rootExponent y) : ℂ)*_)*_*_*_) = _
  rw [show Real.exp (rootExponent y-3*L) = Real.exp (-3*L)*Real.exp (rootExponent y) by
    rw [← Real.exp_add]; congr 1; ring, Complex.ofReal_mul]
  ring

def familyDensity (g : Fin 6 → 𝓢(ℝ, ℂ)) (g₁ g₂ b₃ : 𝓢(ℝ, ℂ))
    (c₁ c₂ θ₁ θ₂ L : ℝ) (p : Frequency × (Fin 6 → ℝ)) : ℂ :=
  (Real.exp (-3*L) : ℂ) * fullProfileDensity g
    (𝓕 (clippedTwist g₁ c₁ θ₁)) (𝓕 (clippedTwist g₂ c₂ θ₂)) b₃ p

theorem familyDensity_formula (g : Fin 6 → 𝓢(ℝ, ℂ)) (g₁ g₂ b₃ : 𝓢(ℝ, ℂ))
    (c₁ c₂ θ₁ θ₂ L : ℝ) (p : Frequency × (Fin 6 → ℝ)) :
    familyDensity g g₁ g₂ b₃ c₁ c₂ θ₁ θ₂ L p =
      (Real.exp (-3*L) : ℂ) *
        (sourceDensity g₁ c₁ θ₁ p.1.1 *
          (sourceDensity g₂ c₂ θ₂ p.1.2.1 * b₃ p.1.2.2)) * coordinateDensity g p.2 := by
  simp only [familyDensity, fullProfileDensity, tripleCoefficient, fourier_clippedTwist]
  ring

theorem familyDensity_weighted_integrable
    (g : Fin 6 → 𝓢(ℝ, ℂ)) (g₁ g₂ b₃ : 𝓢(ℝ, ℂ))
    (c₁ c₂ θ₁ θ₂ L : ℝ) (J : ℕ) :
    Integrable (fun p : Frequency × (Fin 6 → ℝ) =>
      tripleHeight J p.1 * coordinateHeight J p.2 *
        ‖familyDensity g g₁ g₂ b₃ c₁ c₂ θ₁ θ₂ L p‖) := by
  convert (InverseMoment.fullProfileDensity_weighted_integrable g
    (𝓕 (clippedTwist g₁ c₁ θ₁)) (𝓕 (clippedTwist g₂ c₂ θ₂)) b₃ J).const_mul
      (Real.exp (-3*L)) using 1
  funext p
  simp only [familyDensity, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (Real.exp_pos _)]
  ring

theorem familyDensity_weighted_integral
    (g : Fin 6 → 𝓢(ℝ, ℂ)) (g₁ g₂ b₃ : 𝓢(ℝ, ℂ))
    (c₁ c₂ θ₁ θ₂ L : ℝ) (J : ℕ) :
    (∫ p : Frequency × (Fin 6 → ℝ),
      tripleHeight J p.1 * coordinateHeight J p.2 *
        ‖familyDensity g g₁ g₂ b₃ c₁ c₂ θ₁ θ₂ L p‖) =
    Real.exp (-3*L) *
      (∫ t : ℝ, (1+‖t‖)^J * ‖sourceDensity g₁ c₁ θ₁ t‖) *
      (∫ t : ℝ, (1+‖t‖)^J * ‖sourceDensity g₂ c₂ θ₂ t‖) *
      (∫ t : ℝ, (1+‖t‖)^J * ‖b₃ t‖) *
      ∏ i, ∫ u : ℝ, (1+‖u‖)^J * ‖(𝓕 (g i)) u‖ := by
  have he (p : Frequency × (Fin 6 → ℝ)) :
      tripleHeight J p.1 * coordinateHeight J p.2 *
        ‖familyDensity g g₁ g₂ b₃ c₁ c₂ θ₁ θ₂ L p‖ =
      Real.exp (-3*L) * (tripleHeight J p.1 * coordinateHeight J p.2 *
        ‖fullProfileDensity g (𝓕 (clippedTwist g₁ c₁ θ₁))
          (𝓕 (clippedTwist g₂ c₂ θ₂)) b₃ p‖) := by
    simp only [familyDensity, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (Real.exp_pos _)]
    ring
  simp_rw [he]
  rw [integral_const_mul, InverseMoment.fullProfileDensity_weighted_integral]
  simp only [tripleHeight]
  rw [tripleCoefficient_weighted_integral]
  simp only [fourier_clippedTwist]
  ring

def logFamilyProfile (g₁ g₂ : 𝓢(ℝ, ℂ)) (Φ : 𝓢(ℝ, ℂ))
    (V : Fin 6 → ℝ → ℂ) (c₁ c₂ θ₁ θ₂ R L : ℝ) (y : Fin 6 → ℝ) : ℂ :=
  (Real.exp (-3*L) : ℂ) *
    ((∏ i, secondRootWindows V i (y i)) *
      clippedTwist g₁ c₁ θ₁ (∑ i, secondLeftSlope i*y i) *
      clippedTwist g₂ c₂ θ₂ (∑ i, secondRightSlope i*y i) *
      paperRadialFourier Φ (R*Real.exp (∑ i, secondKernelSlope i*y i)))

theorem family_common_measure
    (g₁ g₂ Φ : 𝓢(ℝ, ℂ)) (V : Fin 6 → ℝ → ℂ) (M : Fin 6 → ℝ)
    (hV : ∀ i, ContDiff ℝ ∞ (V i)) (hS : ∀ i, HasCompactSupport (V i))
    (hM : ∀ i, 0 ≤ M i) (hbox : ∀ i y, V i y ≠ 0 → |y| ≤ M i) (A J : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ R : ℝ, 0 < R → ∃ b₃ : 𝓢(ℝ, ℂ),
      ∀ c₁ c₂ θ₁ θ₂ L : ℝ, 0 ≤ L →
      (∀ y : Fin 6 → ℝ,
        logFamilyProfile g₁ g₂ Φ V c₁ c₂ θ₁ θ₂ R L y =
          ∫ p : Frequency × (Fin 6 → ℝ),
            familyDensity (secondRootSchwartz V hV hS) g₁ g₂ b₃ c₁ c₂ θ₁ θ₂ L p *
              pureProfileMode secondLeftSlope secondRightSlope secondKernelSlope y p.1 p.2) ∧
      Integrable (fun p : Frequency × (Fin 6 → ℝ) =>
        tripleHeight J p.1 * coordinateHeight J p.2 *
          ‖familyDensity (secondRootSchwartz V hV hS) g₁ g₂ b₃ c₁ c₂ θ₁ θ₂ L p‖) ∧
      (1+R)^A * (∫ p : Frequency × (Fin 6 → ℝ),
        tripleHeight J p.1 * coordinateHeight J p.2 *
          ‖familyDensity (secondRootSchwartz V hV hS) g₁ g₂ b₃ c₁ c₂ θ₁ θ₂ L p‖) ≤
        C * ((1+‖θ₁‖)^(InverseClippingProfiles.momentOrder J) *
          (1+‖θ₂‖)^(InverseClippingProfiles.momentOrder J)) := by
  have hb : ∀ i y, secondRootWindows V i y ≠ 0 → |y| ≤ M i := by
    intro i y hy
    fin_cases i <;> apply hbox _ y
    all_goals first | exact hy | exact (div_ne_zero_iff.mp hy).1
  obtain ⟨C₃, hC₃, hsep⟩ := radial_profile_envelope
    Φ (secondRootWindows V) secondKernelSlope M hM hb A J
  obtain ⟨C₁, hC₁, h₁⟩ := sourceDensity_moment_uniform g₁ J
  obtain ⟨C₂, hC₂, h₂⟩ := sourceDensity_moment_uniform g₂ J
  let D : ℝ := ∏ i, ∫ u : ℝ, (1+‖u‖)^J *
    ‖(𝓕 (secondRootSchwartz V hV hS i)) u‖
  have hD : 0 ≤ D := Finset.prod_nonneg (fun i _ => integral_nonneg (fun u => by positivity))
  refine ⟨C₁*C₂*C₃*D, by positivity, ?_⟩
  intro R hR
  obtain ⟨b₃, he, _, hm, _⟩ := hsep R hR
  refine ⟨b₃, ?_⟩
  intro c₁ c₂ θ₁ θ₂ L hL
  refine ⟨?_, familyDensity_weighted_integrable _ _ _ _ _ _ _ _ _ _, ?_⟩
  · intro y
    have hid := descent_profile_identity (clippedTwist g₁ c₁ θ₁) (clippedTwist g₂ c₂ θ₂)
      Φ (secondRootWindows V) secondLeftSlope secondRightSlope secondKernelSlope R b₃ he y
    have habs := profile_integral_coordinate_absorption (secondRootSchwartz V hV hS)
      (𝓕 (clippedTwist g₁ c₁ θ₁)) (𝓕 (clippedTwist g₂ c₂ θ₂)) b₃
      secondLeftSlope secondRightSlope secondKernelSlope y
    have hid' : logFamilyProfile g₁ g₂ Φ V c₁ c₂ θ₁ θ₂ R L y =
        (Real.exp (-3*L) : ℂ) *
          ∫ p : Frequency × (Fin 6 → ℝ),
            fullProfileDensity (secondRootSchwartz V hV hS)
              (𝓕 (clippedTwist g₁ c₁ θ₁)) (𝓕 (clippedTwist g₂ c₂ θ₂)) b₃ p *
              pureProfileMode secondLeftSlope secondRightSlope secondKernelSlope y p.1 p.2 := by
      unfold logFamilyProfile
      rw [hid]
      congr 1
      rw [full_density_mode_fubini]
      simpa only [profileMode, secondRootSchwartz, rootSchwartz_apply] using habs
    rw [hid', ← integral_const_mul]
    apply integral_congr_ae
    filter_upwards with p
    unfold familyDensity
    ring
  · rw [familyDensity_weighted_integral]
    have h1 := (h₁ c₁ θ₁).2
    have h2 := (h₂ c₂ θ₂).2
    have h12 := mul_le_mul h1 h2 (integral_nonneg (fun _ => by positivity))
      (mul_nonneg hC₁ (by positivity))
    have hm0 : 0 ≤ (1+R)^A * ∫ t : ℝ, (1+‖t‖)^J * ‖b₃ t‖ := by positivity
    have h123 := mul_le_mul h12 hm hm0 (by positivity)
    have h123D := mul_le_mul_of_nonneg_right h123 hD
    have hnorm : Real.exp (-3*L) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
    have heq : (1+R)^A * (Real.exp (-3*L) *
        (∫ t : ℝ, (1+‖t‖)^J * ‖sourceDensity g₁ c₁ θ₁ t‖) *
        (∫ t : ℝ, (1+‖t‖)^J * ‖sourceDensity g₂ c₂ θ₂ t‖) *
        (∫ t : ℝ, (1+‖t‖)^J * ‖b₃ t‖) * D) =
      Real.exp (-3*L) * (((∫ t : ℝ, (1+‖t‖)^J * ‖sourceDensity g₁ c₁ θ₁ t‖) *
        (∫ t : ℝ, (1+‖t‖)^J * ‖sourceDensity g₂ c₂ θ₂ t‖)) *
        ((1+R)^A * ∫ t : ℝ, (1+‖t‖)^J * ‖b₃ t‖) * D) := by ring
    change (1+R)^A * (_ * _ * _ * _ * D) ≤ _
    rw [heq]
    exact (mul_le_mul_of_nonneg_left h123D (Real.exp_pos _).le).trans
      ((mul_le_of_le_one_left (by positivity) hnorm).trans_eq (by ring))

theorem sourceDensity_moment_seminorm (g : 𝓢(ℝ, ℂ)) (M b : ℝ)
    (hM : 0 ≤ M) (hb : 1 ≤ b) (hg : Function.support g ⊆ Set.Icc (-M) M)
    (J : ℕ) {c : ℝ} (hc : 1 ≤ c) (hcb : c ≤ b) (θ : ℝ) :
    (∫ t : ℝ, (1+‖t‖)^J * ‖sourceDensity g c θ t‖) ≤
      InverseClippingProfiles.windowMomentConstant g M (Real.log b) 0 J *
        (1+‖θ‖)^(InverseClippingProfiles.momentOrder J) := by
  have hc0 : 0 < c := lt_of_lt_of_le zero_lt_one hc
  have hlog : |Real.log c| ≤ Real.log b * 1 := by
    rw [mul_one, abs_of_nonneg (Real.log_nonneg hc)]
    exact Real.log_le_log hc0 hcb
  have he : clippedTwist g c θ = frequencyTwist
      (InverseClippingProfiles.rootSchwartz g M (Real.log b) 1 (Real.log c) 0 0
        zero_lt_one hlog hg) θ := by
    ext y
    simp [InverseClippingProfiles.rootSchwartz_apply,
      InverseClippingProfiles.rootedWindow, InverseClippingProfiles.logWindow]
  have hm := InverseClippingProfiles.rooted_twist_fourier_moment g M (Real.log b)
    1 (Real.log c) 0 0 θ hM (Real.log_nonneg hb) le_rfl hlog hg (by simp) J
  simp_rw [← fourier_clippedTwist, he]
  simpa only [InverseClippingProfiles.windowMomentConstant, one_pow, mul_one] using hm

theorem clippedSource_conjugate (W : ℝ → ℂ) (c θ x : ℝ) :
    star (clippedSource W c θ x) = clippedSource (fun x => star (W x)) c (-θ) x := by
  simp only [clippedSource, star_mul, JointLogSeparation.kernelLogPhase_conjugate]
  ring

theorem familyDensity_joint_measurable
    (g : Fin 6 → 𝓢(ℝ, ℂ)) (g₁ g₂ b₃ : 𝓢(ℝ, ℂ)) (L : ℝ) :
    StronglyMeasurable (fun z : ((ℝ × ℝ) × (ℝ × ℝ)) × (Frequency × (Fin 6 → ℝ)) =>
      familyDensity g g₁ g₂ b₃ z.1.1.1 z.1.2.1 z.1.1.2 z.1.2.2 L z.2) := by
  simp_rw [familyDensity_formula]
  apply Measurable.stronglyMeasurable
  unfold sourceDensity coordinateDensity kernelLogPhase
  have h1 : Measurable ((𝓕 g₁ : 𝓢(ℝ, ℂ)) : ℝ → ℂ) := (𝓕 g₁ : 𝓢(ℝ, ℂ)).continuous.measurable
  have h2 : Measurable ((𝓕 g₂ : 𝓢(ℝ, ℂ)) : ℝ → ℂ) := (𝓕 g₂ : 𝓢(ℝ, ℂ)).continuous.measurable
  have h3 : Measurable (b₃ : ℝ → ℂ) := b₃.continuous.measurable
  have hu (i : Fin 6) : Measurable ((𝓕 (g i) : 𝓢(ℝ, ℂ)) : ℝ → ℂ) :=
    (𝓕 (g i) : 𝓢(ℝ, ℂ)).continuous.measurable
  have hexp : Measurable Complex.exp := Complex.continuous_exp.measurable
  fun_prop

theorem fresh_cutoff_one (W w : ℝ → ℂ) (a b bclip A₀ B₀ A₂ B₂ : ℝ)
    (_ha : 0 < a) (hA₀ : 0 < A₀) (hA₂ : 0 < A₂) (hclip : 1 ≤ bclip)
    (hW : Function.support W ⊆ Set.Icc a b)
    (hω : ∀ x ∈ Set.Icc (a/(bclip*B₀*B₂)) (b/(A₀*A₂)), w x = 1)
    {c u v x : ℝ} (hc : 1 ≤ c) (hcb : c ≤ bclip)
    (hu : u ∈ Set.Icc A₀ B₀) (hv : v ∈ Set.Icc A₂ B₂) (hx : 0 < x)
    (hs : W (c*(u*v*x)) ≠ 0) : w x = 1 := by
  have hu0 : 0 < u := hA₀.trans_le hu.1
  have hv0 : 0 < v := hA₂.trans_le hv.1
  have hB₀ : 0 < B₀ := hu0.trans_le hu.2
  have hB₂ : 0 < B₂ := hv0.trans_le hv.2
  have hc0 : 0 < c := zero_lt_one.trans_le hc
  have hs' := hW hs
  have hlo : A₀*A₂ ≤ c*(u*v) := by
    have hprod := mul_le_mul hu.1 hv.1 hA₂.le hu0.le
    exact hprod.trans (le_mul_of_one_le_left (mul_nonneg hu0.le hv0.le) hc)
  have hhi : c*(u*v) ≤ bclip*B₀*B₂ := by
    have hprod := mul_le_mul hu.2 hv.2 hv0.le hB₀.le
    exact (mul_le_mul hcb hprod (mul_nonneg hu0.le hv0.le)
      (zero_lt_one.trans_le hclip).le).trans_eq (by ring)
  apply hω x
  constructor
  · apply (div_le_iff₀ (by positivity : 0 < bclip*B₀*B₂)).mpr
    have hh := mul_le_mul_of_nonneg_right hhi hx.le
    nlinarith [hs'.1]
  · apply (le_div_iff₀ (mul_pos hA₀ hA₂)).mpr
    have hh := mul_le_mul_of_nonneg_right hlo hx.le
    nlinarith [hs'.2]

def columnCenter (D B v : ℝ) : ℝ := D-B-v
def prefactorCenter (m D B θ : ℝ) : ℝ := m-2*D+B-θ
def radialCenter (m H θ D B : ℝ) : ℝ := m+H-θ-2*(D-B)

theorem original_column_scale {Z : ℝ} (hZ : 0 < Z) (D B v : ℝ) :
    Z^B * Z^v * Z^(columnCenter D B v) = Z^D := by
  rw [← Real.rpow_add hZ, ← Real.rpow_add hZ]
  congr 1
  unfold columnCenter
  ring

theorem initial_prefactor_scale {Z : ℝ} (hZ : 0 < Z) (D B v m θ : ℝ) :
    Z^(-D) * Z^m / (Z^θ * Z^v * Z^(columnCenter D B v)) =
      Z^(prefactorCenter m D B θ) := by
  rw [← Real.rpow_add hZ, ← Real.rpow_add hZ, ← Real.rpow_add hZ,
    ← Real.rpow_sub hZ]
  congr 1
  unfold columnCenter prefactorCenter
  ring

theorem initial_radial_scale {Z : ℝ} (hZ : 0 < Z) (D B v m θ H : ℝ) :
    Z^m * Z^H / (Z^θ * (Z^v)^2 * (Z^(columnCenter D B v))^2) =
      Z^(radialCenter m H θ D B) := by
  simp only [pow_two]
  rw [← Real.rpow_add hZ, ← Real.rpow_add hZ, ← Real.rpow_add hZ,
    ← Real.rpow_add hZ, ← Real.rpow_add hZ, ← Real.rpow_sub hZ]
  congr 1
  unfold columnCenter radialCenter
  ring

theorem initial_normalization_scalar {Z : ℝ} (hZ : 0 < Z) (κ η : ℝ) :
    Z^(κ+3*η) * Real.exp (-3*(η*Real.log Z)) = Z^κ := by
  have he : Real.exp (-3*(η*Real.log Z)) = Z^(-3*η) := by
    rw [Real.rpow_def_of_pos hZ]
    congr 1
    ring
  rw [he, ← Real.rpow_add hZ]
  congr 1
  ring

def physicalKernel (W₁ W₂ : ℝ → ℂ) (Φ : 𝓢(ℝ, ℂ))
    (Z D m : ℝ) (q : Fin 6 → ℝ) : ℂ :=
  ((Z^(-D)*Z^m/(q 1*q 2*Real.sqrt (q 4*q 5)) : ℝ) : ℂ) *
    W₁ (q 0*q 2*q 4/Z^D) * W₂ (q 0*q 2*q 5/Z^D) *
      paperRadialFourier Φ (Z^m*q 3/(q 1*(q 2)^2*q 4*q 5))

theorem physicalKernel_eq_secondNorm (W₁ W₂ : ℝ → ℂ) (Φ : 𝓢(ℝ, ℂ))
    (Z D m : ℝ) (q : Fin 6 → ℝ) (hq : ∀ i, 0 < q i) :
    physicalKernel W₁ W₂ Φ Z D m q =
      ((Z^(-D)*Z^m : ℝ) : ℂ) *
        secondNormProfile (fun x => W₁ (x/Z^D)) (fun x => W₂ (x/Z^D))
          Φ (fun _ _ => 1) (Z^m) q := by
  unfold physicalKernel secondNormProfile
  rw [Real.sqrt_mul (hq 4).le]
  simp only [Finset.prod_const_one, one_mul, Complex.ofReal_div, Complex.ofReal_mul]
  ring

theorem physicalKernel_nominal (W₁ W₂ : ℝ → ℂ) (Φ : 𝓢(ℝ, ℂ))
    {Z : ℝ} (hZ : 0 < Z) (D B v m θ H : ℝ)
    (q : Fin 6 → ℝ) (hq : ∀ i, 0 < q i) :
    physicalKernel W₁ W₂ Φ Z D m q =
      (Z^(prefactorCenter m D B θ) : ℝ) *
        secondNormProfile W₁ W₂ Φ (fun _ _ => 1) (Z^(radialCenter m H θ D B))
          (secondRelativeNorm q (Z^B) (Z^θ) (Z^v) (Z^H) (Z^(columnCenter D B v))) := by
  have hn := secondNormProfile_nominal W₁ W₂ Φ
    (Z^B) (Z^θ) (Z^v) (Z^H) (Z^(columnCenter D B v)) (Z^m)
    (Real.rpow_pos_of_pos hZ _) (Real.rpow_pos_of_pos hZ _)
    (Real.rpow_pos_of_pos hZ _) (Real.rpow_pos_of_pos hZ _)
    (Real.rpow_pos_of_pos hZ _) q hq
  rw [original_column_scale hZ D B v, initial_radial_scale hZ D B v m θ H] at hn
  rw [physicalKernel_eq_secondNorm W₁ W₂ Φ Z D m q hq, hn]
  change ((Z^(-D)*Z^m : ℝ) : ℂ) *
      (((Z^θ*Z^v*Z^(columnCenter D B v) : ℝ) : ℂ)⁻¹ * _) = _
  rw [← mul_assoc, ← Complex.ofReal_inv, ← Complex.ofReal_mul,
    ← div_eq_mul_inv, initial_prefactor_scale hZ D B v m θ]
  rfl

theorem normalizedProfile_eq_family (W₁ W₂ : ℝ → ℂ) (a b : ℝ) (ha : 0 < a)
    (hs₁ : Function.support W₁ ⊆ Set.Icc a b) (hs₂ : Function.support W₂ ⊆ Set.Icc a b)
    (hW₁ : ContDiff ℝ ∞ W₁) (hW₂ : ContDiff ℝ ∞ W₂)
    (Φ : 𝓢(ℝ, ℂ)) (V : Fin 6 → ℝ → ℂ)
    {c₁ c₂ : ℝ} (hc₁ : 0 < c₁) (hc₂ : 0 < c₂) (θ₁ θ₂ R L : ℝ)
    (y : Fin 6 → ℝ) :
    normalizedProfile (clippedSource W₁ c₁ θ₁) (clippedSource W₂ c₂ θ₂) Φ V R L y =
      logFamilyProfile (CanonicalCubeSeparation.sourceLogProfile W₁ a b ha hs₁ hW₁)
        (CanonicalCubeSeparation.sourceLogProfile W₂ a b ha hs₂ hW₂)
        Φ V c₁ c₂ θ₁ θ₂ R L y := by
  unfold normalizedProfile logFamilyProfile secondPoissonProfile
  rw [clipped_log_source W₁ a b ha hs₁ hW₁ hc₁,
    clipped_log_source W₂ a b ha hs₂ hW₂ hc₂]

theorem fresh_profile_restore (W₁ W₂ w₁ w₂ : ℝ → ℂ) (Φ : 𝓢(ℝ, ℂ))
    (V : Fin 6 → ℝ → ℂ) (R L : ℝ) (x : Fin 6 → ℝ) (hx : ∀ i, 0 < x i)
    (hw₁ : W₁ (x 0*x 2*x 4) ≠ 0 → w₁ (x 4) = 1)
    (hw₂ : W₂ (x 0*x 2*x 5) ≠ 0 → w₂ (x 5) = 1)
    (hV : w₁ (x 4) ≠ 0 → w₂ (x 5) ≠ 0 → ∀ i, V i (Real.log (x i)) = 1) :
    (Real.exp (-3*L) : ℂ) * secondNormProfile W₁ W₂ Φ (fun _ _ => 1) R x =
      (w₁ (x 4)*w₂ (x 5)) * normalizedProfile W₁ W₂ Φ V R L (fun i => Real.log (x i)) := by
  unfold normalizedProfile
  rw [secondPoissonProfile_log W₁ W₂ Φ V R x hx]
  by_cases h1 : W₁ (x 0*x 2*x 4) = 0
  · simp only [secondNormProfile, h1, mul_zero, zero_mul, zero_div]
  by_cases h2 : W₂ (x 0*x 2*x 5) = 0
  · simp only [secondNormProfile, h2, mul_zero, zero_mul, zero_div]
  have hv := hV (by rw [hw₁ h1]; exact one_ne_zero) (by rw [hw₂ h2]; exact one_ne_zero)
  simp only [secondNormProfile, hv, hw₁ h1, hw₂ h2, Finset.prod_const_one, one_mul]

def relativeNorm (q : Fin 6 → ℝ) (Z D B v θ H : ℝ) : Fin 6 → ℝ :=
  secondRelativeNorm q (Z^B) (Z^θ) (Z^v) (Z^H) (Z^(columnCenter D B v))

def relativeLog (q : Fin 6 → ℝ) (Z D B v θ H : ℝ) (i : Fin 6) : ℝ :=
  Real.log (relativeNorm q Z D B v θ H i)

theorem relativeNorm_pos (q : Fin 6 → ℝ) (hq : ∀ i, 0 < q i)
    {Z : ℝ} (hZ : 0 < Z) (D B v θ H : ℝ) :
    ∀ i, 0 < relativeNorm q Z D B v θ H i :=
  secondRelativeNorm_pos q hq _ _ _ _ _
    (Real.rpow_pos_of_pos hZ _) (Real.rpow_pos_of_pos hZ _)
    (Real.rpow_pos_of_pos hZ _) (Real.rpow_pos_of_pos hZ _)
    (Real.rpow_pos_of_pos hZ _)

theorem initial_kernel_restore (W₁ W₂ w₁ w₂ : ℝ → ℂ) (Φ : 𝓢(ℝ, ℂ))
    (V : Fin 6 → ℝ → ℂ) {Z : ℝ} (hZ : 0 < Z) (D B v m θ H η : ℝ)
    (q : Fin 6 → ℝ) (hq : ∀ i, 0 < q i)
    (hw₁ : W₁ (relativeNorm q Z D B v θ H 0 * relativeNorm q Z D B v θ H 2 *
      relativeNorm q Z D B v θ H 4) ≠ 0 → w₁ (relativeNorm q Z D B v θ H 4) = 1)
    (hw₂ : W₂ (relativeNorm q Z D B v θ H 0 * relativeNorm q Z D B v θ H 2 *
      relativeNorm q Z D B v θ H 5) ≠ 0 → w₂ (relativeNorm q Z D B v θ H 5) = 1)
    (hV : w₁ (relativeNorm q Z D B v θ H 4) ≠ 0 →
      w₂ (relativeNorm q Z D B v θ H 5) ≠ 0 → ∀ i, V i (relativeLog q Z D B v θ H i) = 1) :
    physicalKernel W₁ W₂ Φ Z D m q =
      (Z^(prefactorCenter m D B θ + 3*η) : ℝ) *
        (w₁ (relativeNorm q Z D B v θ H 4)*w₂ (relativeNorm q Z D B v θ H 5)) *
        normalizedProfile W₁ W₂ Φ V (Z^(radialCenter m H θ D B))
          (η*Real.log Z) (relativeLog q Z D B v θ H) := by
  rw [physicalKernel_nominal W₁ W₂ Φ hZ D B v m θ H q hq]
  have hs := fresh_profile_restore W₁ W₂ w₁ w₂ Φ V (Z^(radialCenter m H θ D B))
    (η*Real.log Z) (relativeNorm q Z D B v θ H)
    (relativeNorm_pos q hq hZ D B v θ H) hw₁ hw₂ hV
  have hn : ((Z^(prefactorCenter m D B θ) : ℝ) : ℂ) =
      (Z^(prefactorCenter m D B θ+3*η) : ℝ) * (Real.exp (-3*(η*Real.log Z)) : ℂ) := by
    rw [← Complex.ofReal_mul, initial_normalization_scalar hZ]
  rw [show relativeLog q Z D B v θ H =
    (fun i => Real.log (relativeNorm q Z D B v θ H i)) by rfl]
  rw [hn, mul_assoc]
  simpa only [mul_assoc, relativeNorm] using congrArg
    (fun z : ℂ => (Z^(prefactorCenter m D B θ+3*η) : ℝ) * z) hs

def PhysicalIdentityAt (W₁ W₂ : ℝ → ℂ) (Φ : 𝓢(ℝ, ℂ))
    (V : Fin 6 → ℝ → ℂ) (g : Fin 6 → 𝓢(ℝ, ℂ)) (g₁ g₂ b₃ : 𝓢(ℝ, ℂ))
    (Z D B v m θ H η c₁ c₂ θ₁ θ₂ : ℝ) : Prop :=
  ∀ (w₁ w₂ : ℝ → ℂ) (q : Fin 6 → ℝ), (∀ i, 0 < q i) →
    (clippedSource W₁ c₁ θ₁
      (relativeNorm q Z D B v θ H 0 * relativeNorm q Z D B v θ H 2 *
        relativeNorm q Z D B v θ H 4) ≠ 0 → w₁ (relativeNorm q Z D B v θ H 4) = 1) →
    (clippedSource W₂ c₂ θ₂
      (relativeNorm q Z D B v θ H 0 * relativeNorm q Z D B v θ H 2 *
        relativeNorm q Z D B v θ H 5) ≠ 0 → w₂ (relativeNorm q Z D B v θ H 5) = 1) →
    (w₁ (relativeNorm q Z D B v θ H 4) ≠ 0 →
      w₂ (relativeNorm q Z D B v θ H 5) ≠ 0 →
      ∀ i, V i (relativeLog q Z D B v θ H i) = 1) →
    physicalKernel (clippedSource W₁ c₁ θ₁) (clippedSource W₂ c₂ θ₂) Φ Z D m q =
      (Z^(prefactorCenter m D B θ + 3*η) : ℝ) *
        (w₁ (relativeNorm q Z D B v θ H 4)*w₂ (relativeNorm q Z D B v θ H 5)) *
        ∫ p : Frequency × (Fin 6 → ℝ),
          familyDensity g g₁ g₂ b₃ c₁ c₂ θ₁ θ₂ (η*Real.log Z) p *
            pureProfileMode secondLeftSlope secondRightSlope secondKernelSlope
              (relativeLog q Z D B v θ H) p.1 p.2

theorem initial_physical_family_common_measure
    (W₁ W₂ : ℝ → ℂ) (a b : ℝ) (ha : 0 < a)
    (hs₁ : Function.support W₁ ⊆ Set.Icc a b) (hs₂ : Function.support W₂ ⊆ Set.Icc a b)
    (hW₁ : ContDiff ℝ ∞ W₁) (hW₂ : ContDiff ℝ ∞ W₂)
    (Φ : 𝓢(ℝ, ℂ)) (V : Fin 6 → ℝ → ℂ) (M : Fin 6 → ℝ)
    (hV : ∀ i, ContDiff ℝ ∞ (V i)) (hS : ∀ i, HasCompactSupport (V i))
    (hM : ∀ i, 0 ≤ M i) (hbox : ∀ i y, V i y ≠ 0 → |y| ≤ M i) (A J : ℕ) :
    let g := secondRootSchwartz V hV hS
    let g₁ := CanonicalCubeSeparation.sourceLogProfile W₁ a b ha hs₁ hW₁
    let g₂ := CanonicalCubeSeparation.sourceLogProfile W₂ a b ha hs₂ hW₂
    ∃ C : ℝ, 0 ≤ C ∧ ∀ Z D B v m θ H η : ℝ, 0 < Z → 0 ≤ η*Real.log Z →
      ∃ b₃ : 𝓢(ℝ, ℂ), ∀ c₁ c₂ θ₁ θ₂ : ℝ, 0 < c₁ → 0 < c₂ →
      PhysicalIdentityAt W₁ W₂ Φ V g g₁ g₂ b₃ Z D B v m θ H η c₁ c₂ θ₁ θ₂ ∧
      Integrable (fun p : Frequency × (Fin 6 → ℝ) =>
        tripleHeight J p.1 * coordinateHeight J p.2 *
          ‖familyDensity g g₁ g₂ b₃ c₁ c₂ θ₁ θ₂ (η*Real.log Z) p‖) ∧
      (1+Z^(radialCenter m H θ D B))^A * (∫ p : Frequency × (Fin 6 → ℝ),
        tripleHeight J p.1 * coordinateHeight J p.2 *
          ‖familyDensity g g₁ g₂ b₃ c₁ c₂ θ₁ θ₂ (η*Real.log Z) p‖) ≤
        C * ((1+‖θ₁‖)^(InverseClippingProfiles.momentOrder J) *
          (1+‖θ₂‖)^(InverseClippingProfiles.momentOrder J)) := by
  dsimp only
  obtain ⟨C, hC, hsep⟩ := family_common_measure
    (CanonicalCubeSeparation.sourceLogProfile W₁ a b ha hs₁ hW₁)
    (CanonicalCubeSeparation.sourceLogProfile W₂ a b ha hs₂ hW₂)
    Φ V M hV hS hM hbox A J
  refine ⟨C, hC, ?_⟩
  intro Z D B v m θ H η hZ hL
  obtain ⟨b₃, hb₃⟩ := hsep (Z^(radialCenter m H θ D B)) (Real.rpow_pos_of_pos hZ _)
  refine ⟨b₃, ?_⟩
  intro c₁ c₂ θ₁ θ₂ hc₁ hc₂
  obtain ⟨he, hi, hbound⟩ := hb₃ c₁ c₂ θ₁ θ₂ (η*Real.log Z) hL
  refine ⟨?_, hi, hbound⟩
  intro w₁ w₂ q hq hw₁ hw₂ hcut
  rw [initial_kernel_restore _ _ w₁ w₂ Φ V hZ D B v m θ H η q hq hw₁ hw₂ hcut,
    normalizedProfile_eq_family W₁ W₂ a b ha hs₁ hs₂ hW₁ hW₂ Φ V hc₁ hc₂, he]

theorem fresh_cutoff_one_clippedSource (W w : ℝ → ℂ) (a b bclip A₀ B₀ A₂ B₂ : ℝ)
    (ha : 0 < a) (hA₀ : 0 < A₀) (hA₂ : 0 < A₂) (hclip : 1 ≤ bclip)
    (hW : Function.support W ⊆ Set.Icc a b)
    (hw : ∀ x ∈ Set.Icc (a/(bclip*B₀*B₂)) (b/(A₀*A₂)), w x = 1)
    {c u v x : ℝ} (hc : 1 ≤ c) (hcb : c ≤ bclip)
    (hu : u ∈ Set.Icc A₀ B₀) (hv : v ∈ Set.Icc A₂ B₂) (hx : 0 < x)
    (θ : ℝ) (hs : clippedSource W c θ (u*v*x) ≠ 0) : w x = 1 := by
  exact fresh_cutoff_one W w a b bclip A₀ B₀ A₂ B₂ ha hA₀ hA₂ hclip hW hw
    hc hcb hu hv hx (mul_ne_zero_iff.mp hs).2

theorem clipped_column_ratio {Z : ℝ} (hZ : 0 < Z) (N q : ℝ) :
    q / Z^N = Z^(max 0 N-N) * (q / Z^(max 0 N)) := by
  rw [Real.rpow_sub hZ]
  field_simp [ne_of_gt (Real.rpow_pos_of_pos hZ N),
    ne_of_gt (Real.rpow_pos_of_pos hZ (max 0 N))]

theorem clipped_column_source_identity (w : ℝ → ℂ) {Z q : ℝ}
    (hZ : 0 < Z) (hq : 0 < q) (N θ : ℝ) :
    kernelLogPhase θ (Real.log (q/Z^N)) * w (q/Z^N) =
      kernelLogPhase θ (Real.log (Z^(max 0 N-N))) *
        clippedSource w (Z^(max 0 N-N)) θ (q/Z^(max 0 N)) := by
  rw [clipped_column_ratio hZ N q]
  rw [Real.log_mul (ne_of_gt (Real.rpow_pos_of_pos hZ _))
    (ne_of_gt (div_pos hq (Real.rpow_pos_of_pos hZ _))), kernelLogPhase_add]
  unfold clippedSource
  ring

theorem retained_initial_clipping (w : ℝ → ℂ) (a b : ℝ) (ha : 0 < a) (hb : 1 ≤ b)
    (hw : Function.support w ⊆ Set.Icc a b) (hs : ContDiff ℝ ∞ w) (J : ℕ) :
    let g := CanonicalCubeSeparation.sourceLogProfile w a b ha hw hs
    ∃ C : ℝ, 0 ≤ C ∧ ∀ Z N q : ℝ, 1 < Z → 1 ≤ q → w (q/Z^N) ≠ 0 →
      let c := Z^(max 0 N-N)
      1 ≤ c ∧ c ≤ b ∧
      Function.support (fun x => w (c*x)) ⊆ Set.Icc (a/b) b ∧
      (∀ θ : ℝ, kernelLogPhase θ (Real.log (q/Z^N)) * w (q/Z^N) =
        kernelLogPhase θ (Real.log c) * clippedSource w c θ (q/Z^(max 0 N))) ∧
      (∀ θ : ℝ, Integrable (fun t : ℝ => (1+‖t‖)^J * ‖sourceDensity g c θ t‖) ∧
        (∫ t : ℝ, (1+‖t‖)^J * ‖sourceDensity g c θ t‖) ≤
          C*(1+‖θ‖)^(InverseClippingProfiles.momentOrder J)) := by
  dsimp only
  obtain ⟨C, hC, hbound⟩ := sourceDensity_moment_uniform
    (CanonicalCubeSeparation.sourceLogProfile w a b ha hw hs) J
  refine ⟨C, hC, ?_⟩
  intro Z N q hZ hq hwitness
  obtain ⟨hc, hcb, hsupport, _⟩ := InverseClippingProfiles.retained_clipped_column
    w Z N q a b hZ hq ha hb hw hwitness
  refine ⟨hc, hcb, hsupport, ?_, fun θ => hbound _ θ⟩
  exact fun θ => clipped_column_source_identity w (zero_lt_one.trans hZ)
    (zero_lt_one.trans_le hq) N θ

end InverseInitialProfile

namespace InverseInitialArithmetic
open Eisenstein SchwartzPlanePoisson FirstPassCubeLabels SecondPassArithmetic
open InverseMoment InverseInitialFibers CompletedGauss TruncatedPrincipalPoisson
open scoped BigOperators Classical
local notation "λ₀" => lambda
variable {ι σ : Type*} [DecidableEq ι] [DecidableEq σ]
  (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i, λ₀ ∉ Ideal.span {p i})

def sourceIdeal (S : Finset ι) : Ideal O := Ideal.span {∏ i∈S,p i}

include hp in
omit [DecidableEq ι] [∀ (i : ι), (Ideal.span {p i}).IsMaximal] in
theorem sourceIdeal_ne_zero (S : Finset ι) : sourceIdeal p S≠0 :=
  Ideal.span_singleton_eq_bot.not.mpr (Finset.prod_ne_zero_iff.mpr (fun i _=>hp i))

omit [∀ (i : ι), (Ideal.span {p i}).IsMaximal] in
theorem sourceIdeal_union (S T : Finset ι) (hst : Disjoint S T) :
    sourceIdeal p (S∪T)=sourceIdeal p S*sourceIdeal p T := by
  simp only [sourceIdeal,Finset.prod_union hst,Ideal.span_singleton_mul_span_singleton]

include hp in
omit [∀ (i : ι), (Ideal.span {p i}).IsMaximal] in
theorem sourceIdeal_gen (hpr : ∀ i,λ₀^2∣p i-1) (S : Finset ι) :
    primaryIdealGenerator (sourceIdeal p S)=∏ i∈S,p i := by
  apply primaryIdealGenerator_span _ (Finset.prod_ne_zero_iff.mpr (fun i _=>hp i))
  induction S using Finset.induction_on with
  | empty => simp
  | @insert i S hi ih =>
    rw [Finset.prod_insert hi]
    have he : p i*(∏ j∈S,p j)-1=(p i-1)*(∏ j∈S,p j)+((∏ j∈S,p j)-1) := by ring
    rw [he]
    exact dvd_add (dvd_mul_of_dvd_left (hpr i) _) ih

omit [∀ (i : ι), (Ideal.span {p i}).IsMaximal] in
theorem sourceIdeal_dvd (E G : Finset ι) (hEG : E⊆G) : sourceIdeal p E∣sourceIdeal p G := by
  refine ⟨sourceIdeal p (G\E),?_⟩
  rw [←sourceIdeal_union p E (G\E) (by exact Finset.disjoint_left.mpr (fun i hi hj=>(Finset.mem_sdiff.mp hj).2 hi)),
    Finset.union_sdiff_of_subset hEG]

def sourcePrime (i : ι) : InverseInitialFibers.PrimeIdeal :=
  ⟨Ideal.span {p i},Ideal.prime_of_isPrime (NeZero.ne _) inferInstance⟩

def sourceTuple {J : ℕ} (G E V : Finset ι) (h : O) (assigned : Fin J→ι) : InitialTuple J :=
  ⟨sourceIdeal p G,sourceIdeal p E,sourceIdeal p V,h,fun i=>sourcePrime p (assigned i)⟩

omit [DecidableEq ι] in
theorem source_prime_dvd (S : Finset ι) (i : ι) (hi : i∈S) :
    (sourcePrime p i).val∣sourceIdeal p S := by
  apply Ideal.dvd_iff_le.mpr
  apply Ideal.span_singleton_le_span_singleton.mpr
  exact Finset.dvd_prod_of_mem p hi

include hp in

theorem sourceTuple_valid (hpr : ∀ i,λ₀^2∣p i-1) {J : ℕ}
    (G E V : Finset ι) (h : O) (assigned : Fin J→ι)
    (hEG : E⊆G) (ha : ∀ i,assigned i∈G∪V) :
    InitialSourceValid (sourceTuple p G E V h assigned) := by
  refine ⟨sourceIdeal_ne_zero p hp G,sourceIdeal_ne_zero p hp V,?_,
    sourceIdeal_dvd p E G hEG,?_⟩
  · change primaryIdealGenerator (sourceIdeal p E)≠0
    rw [sourceIdeal_gen p hp hpr E]
    exact Finset.prod_ne_zero_iff.mpr (fun i _=>hp i)
  · intro i
    change (sourcePrime p (assigned i)).val∣sourceIdeal p G*sourceIdeal p V
    rcases Finset.mem_union.mp (ha i) with hi|hi
    · exact dvd_mul_of_dvd_left (source_prime_dvd p G (assigned i) hi) _
    · exact dvd_mul_of_dvd_right (source_prime_dvd p V (assigned i) hi) _

include hp in

omit [∀ (i : ι), (Ideal.span {p i}).IsMaximal] in
theorem source_quotient (G E : Finset ι) (hEG : E⊆G) :
    quadraticIdealQuotient (sourceIdeal p E) (sourceIdeal p G)=
      sourceIdeal p (G\E) := by
  apply mul_left_cancel₀ (sourceIdeal_ne_zero p hp E)
  rw [quadraticIdeal_mul_quotient (sourceIdeal_dvd p E G hEG)]
  rw [←sourceIdeal_union p E (G\E) (by exact Finset.disjoint_left.mpr (fun i hi hj=>(Finset.mem_sdiff.mp hj).2 hi)),
    Finset.union_sdiff_of_subset hEG]

include hp in

theorem source_child (hpr : ∀ i,λ₀^2∣p i-1) {J : ℕ}
    (G E V : Finset ι) (h : O) (assigned : Fin J→ι) (hEG : E⊆G) :
    initialChild (sourceTuple p G E V h assigned)=
      (sourceIdeal p (G\E),sourceIdeal p E*sourceIdeal p V,(∏ i∈E,p i)*h) := by
  simp only [initialChild,sourceTuple,source_quotient p hp G E hEG,sourceIdeal_gen p hp hpr E]

theorem sourceIdeal_injective (hinj : Function.Injective (fun i=>Ideal.span {p i})) :
    Function.Injective (sourceIdeal p) := by
  intro S T he
  simp only [sourceIdeal,span_finset_prime_product] at he
  exact primeIdealFamily_product_injective _ hinj he

@[ext] structure Source (J : ℕ) where
  common : Finset ι
  divisor : Finset ι
  overlap : Finset ι
  frequency : O
  assigned : Fin J→ι

def toTuple {J : ℕ} (x : Source (ι:=ι) J) : InitialTuple J :=
  sourceTuple p x.common x.divisor x.overlap x.frequency x.assigned

theorem toTuple_injective (hinj : Function.Injective (fun i=>Ideal.span {p i})) {J : ℕ} :
    Function.Injective (toTuple p (J:=J)) := by
  intro x y he
  have hC := congrArg InitialTuple.common he
  have hD := congrArg InitialTuple.divisor he
  have hV := congrArg InitialTuple.residual he
  have hf := congrArg InitialTuple.frequency he
  have ha := congrArg InitialTuple.assigned he
  apply Source.ext
  · exact sourceIdeal_injective p hinj hC
  · exact sourceIdeal_injective p hinj hD
  · exact sourceIdeal_injective p hinj hV
  · exact hf
  · funext i
    apply hinj
    exact congrArg Subtype.val (congrFun ha i)

def assignedTerm {J : ℕ} (lists : Fin J→Finset ι) (a : Fin J→ι→ℂ)
    (outer : Finset ι) (assigned : Fin J→ι) : ℂ :=
  ∏ i, if assigned i∈lists i ∧ assigned i∈outer then a i (assigned i) else 0

theorem assignedTerm_source {J : ℕ} (lists : Fin J→Finset ι) (a : Fin J→ι→ℂ)
    (outer : Finset ι) (assigned : Fin J→ι) (h : assignedTerm lists a outer assigned≠0) :
    ∀ i,assigned i∈lists i ∧ assigned i∈outer := by
  intro i
  have hn := Finset.prod_ne_zero_iff.mp h i (Finset.mem_univ i)
  by_contra hi
  simp only [hi,ite_false,ne_eq,not_true_eq_false] at hn

include hp in

theorem actual_source_valid (hpr : ∀ i,λ₀^2∣p i-1) {J : ℕ}
    (x : Source (ι:=ι) J) (hdiv : x.divisor⊆x.common)
    (lists : Fin J→Finset ι) (a : Fin J→ι→ℂ)
    (hterm : assignedTerm lists a (x.common∪x.overlap) x.assigned≠0) :
    InitialSourceValid (toTuple p x) :=
  sourceTuple_valid p hp hpr x.common x.divisor x.overlap x.frequency x.assigned hdiv
    (fun i=>(assignedTerm_source lists a _ _ hterm i).2)

include hp in

theorem actual_source_fiber_bound
    (hinj : Function.Injective (fun i=>Ideal.span {p i}))
    (hpr : ∀ i,λ₀^2∣p i-1) {J : ℕ}
    (sources : Finset (Source (ι:=ι) J))
    (lists : Fin J→Finset ι) (a : Fin J→ι→ℂ)
    (hdiv : ∀ x∈sources,x.divisor⊆x.common)
    (hterm : ∀ x∈sources,assignedTerm lists a (x.common∪x.overlap) x.assigned≠0)
    (t f : Ideal O) (k : O) (ht : t≠0) (hf : f≠0) :
    (sources.filter (fun x=>initialChild (toTuple p x)=(t,f,k))).card ≤
      (idealDivisors f).card^(J+1)*
        (idealDivisors t).card^J := by
  let S := sources.filter (fun x=>initialChild (toTuple p x)=(t,f,k))
  let T := S.image (toTuple p)
  have hvalid : ∀ y∈T, Valid y t f k := by
    intro y hy
    obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hy
    obtain ⟨hxs,hchild⟩ := Finset.mem_filter.mp hx
    have hv := initialChild_valid (toTuple p x)
      (actual_source_valid p hp hpr x (hdiv x hxs) lists a (hterm x hxs))
    simpa only [hchild] using hv
  have hh := valid_tuple_card_le_separated T t f k ht hf hvalid
  have hcard : T.card=S.card := Finset.card_image_of_injective _ (toTuple_injective p hinj)
  rw [hcard] at hh
  exact hh

include hp in

omit [∀ (i : ι), (Ideal.span {p i}).IsMaximal] in
theorem poisson_generator_unit (hpr : ∀ i,λ₀^2∣p i-1) (E : Finset ι) :
    ∃ u : Oˣ, primeSubsetGenerator (fun i=>Ideal.span {p i}) E=
      (u : O)*primaryIdealGenerator (sourceIdeal p E) := by
  have hg0 : primaryIdealGenerator (sourceIdeal p E)≠0 := by
    rw [sourceIdeal_gen p hp hpr E]
    exact Finset.prod_ne_zero_iff.mpr (fun i _=>hp i)
  have hs : Ideal.span {primaryIdealGenerator (sourceIdeal p E)}=
      Ideal.span {primeSubsetGenerator (fun i=>Ideal.span {p i}) E} := by
    rw [(primaryIdealGenerator_spec _ hg0).1]
    rw [primeSubsetGenerator_span]
    exact span_finset_prime_product p E
  obtain ⟨u,hu⟩ := Ideal.span_singleton_eq_span_singleton.mp hs
  exact ⟨u,by simpa only [mul_comm] using hu.symm⟩

def sectorSource {J : ℕ} (u : Oˣ) (x : Source (ι:=ι) J) : Source (ι:=ι) J :=
  {x with frequency := (u : O)^5*x.frequency}

omit [DecidableEq ι] in
theorem sectorSource_injective {J : ℕ} (u : Oˣ) :
    Function.Injective (sectorSource (J:=J) (ι:=ι) u) := by
  intro x y he
  apply Source.ext
  · simpa only [sectorSource] using congrArg (fun z : Source (ι:=ι) J=>z.common) he
  · simpa only [sectorSource] using congrArg (fun z : Source (ι:=ι) J=>z.divisor) he
  · simpa only [sectorSource] using congrArg (fun z : Source (ι:=ι) J=>z.overlap) he
  · have hh := congrArg Source.frequency he
    exact mul_left_cancel₀ (pow_ne_zero 5 (Units.ne_zero u)) hh
  · simpa only [sectorSource] using congrArg (fun z : Source (ι:=ι) J=>z.assigned) he

include hp in

omit hp in
theorem sectorTuple_injective (hinj : Function.Injective (fun i=>Ideal.span {p i}))
    {J : ℕ} (u : Oˣ) :
    Function.Injective (fun x : Source (ι:=ι) J=>toTuple p (sectorSource u x)) :=
  (toTuple_injective p hinj).comp (sectorSource_injective u)

include hp in

theorem actual_sector_fiber_bound
    (hinj : Function.Injective (fun i=>Ideal.span {p i}))
    (hpr : ∀ i,λ₀^2∣p i-1) {J : ℕ} (u : Oˣ)
    (sources : Finset (Source (ι:=ι) J))
    (lists : Fin J→Finset ι) (a : Fin J→ι→ℂ)
    (hdiv : ∀ x∈sources,x.divisor⊆x.common)
    (hterm : ∀ x∈sources,assignedTerm lists a (x.common∪x.overlap) x.assigned≠0)
    (t f : Ideal O) (k : O) (ht : t≠0) (hf : f≠0) :
    (sources.filter (fun x=>initialChild (toTuple p (sectorSource u x))=(t,f,k))).card ≤
      (idealDivisors f).card^(J+1)*
        (idealDivisors t).card^J := by
  let S := sources.filter (fun x=>initialChild (toTuple p (sectorSource u x))=(t,f,k))
  let T := S.image (fun x=>toTuple p (sectorSource u x))
  have hv : ∀ y∈T, Valid y t f k := by
    intro y hy
    obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hy
    obtain ⟨hxs,hchild⟩ := Finset.mem_filter.mp hx
    have he := initialChild_valid (toTuple p (sectorSource u x))
      (actual_source_valid p hp hpr (sectorSource u x) (hdiv x hxs) lists a (hterm x hxs))
    simpa only [hchild] using he
  have hh := valid_tuple_card_le_separated T t f k ht hf hv
  have hcard : T.card=S.card := Finset.card_image_of_injective _ (sectorTuple_injective p hinj u)
  rw [hcard] at hh
  exact hh


end InverseInitialArithmetic

namespace InverseInitialOverlapFourier
open InverseMoment Eisenstein SchwartzPlanePoisson JointLogSeparation MeasureTheory
open scoped BigOperators Classical SchwartzMap FourierTransform ContDiff

variable {σ ι : Type*} [DecidableEq σ] [DecidableEq ι]

def density (g : 𝓢(ℝ,ℂ)) (xj t : ℝ) : ℂ := (𝓕 g) t*kernelLogPhase t xj

theorem density_norm (g : 𝓢(ℝ,ℂ)) (xj t : ℝ) : ‖density g xj t‖=‖(𝓕 g) t‖ := by
  simp only [density,norm_mul,kernelLogPhase_norm,mul_one]

theorem density_moment (g : 𝓢(ℝ,ℂ)) (J : ℕ) :
    ∃C:ℝ,0≤C ∧ ∀xj,
      Integrable (fun t:ℝ=>(1+‖t‖)^J*‖density g xj t‖) ∧
      (∫t:ℝ,(1+‖t‖)^J*‖density g xj t‖)≤C := by
  refine ⟨∫t:ℝ,(1+‖t‖)^J*‖(𝓕 g) t‖,integral_nonneg (fun t=>by positivity),?_⟩
  intro xj
  simp only [density_norm]
  exact ⟨CanonicalCubeSeparation.weighted_schwartz_integrable (𝓕 g) J,le_rfl⟩

lemma phase_neg (t x : ℝ) : kernelLogPhase (-t) x=kernelLogPhase t (-x) := by
  unfold kernelLogPhase
  congr 1
  push_cast
  ring

lemma phase_sub (t xj xc y : ℝ) :
    kernelLogPhase t xj*kernelLogPhase t xc*kernelLogPhase (-t) y=kernelLogPhase t (xj+xc-y) := by
  rw [phase_neg,←kernelLogPhase_add,←kernelLogPhase_add]
  rfl

lemma fourier_phase_integrable (g : 𝓢(ℝ,ℂ)) (x : ℝ) (a : ℂ) :
    Integrable (fun t:ℝ=>(𝓕 g) t*kernelLogPhase t x*a) := by
  have h : Integrable (fun t:ℝ=>(𝓕 g) t*kernelLogPhase t x) (volume:Measure ℝ) :=
    (𝓕 g).integrable.mul_bdd (c:=1)
    (kernelLogPhase_continuous_left x).aestronglyMeasurable
    (Filter.Eventually.of_forall (fun t=>le_of_eq (kernelLogPhase_norm t x)))
  exact h.mul_const a

theorem tuple_mark_phase (I : Finset σ) (L : σ→Finset ι) (a : σ→ι→ℂ)
    (y : σ→ι→ℝ) (A : Finset ι) (t : ℝ) :
    primeMark I L (fun i p=>a i p*kernelLogPhase (-t) (y i p)) A =
      ∑p∈I.pi L,(∏i∈I.attach,if p i.val i.property∈A then a i.val (p i.val i.property) else 0)*
        kernelLogPhase (-t) (∑i∈I.attach,y i.val (p i.val i.property)) := by
  rw [primeMark_eq_tuple_sum]
  apply Finset.sum_congr rfl
  intro p hp
  rw [kernelLogPhase_sum,←Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro i hi
  split_ifs <;> simp

theorem overlap_tuple_separation (g : 𝓢(ℝ,ℂ))
    (I : Finset σ) (L : σ→Finset ι) (a : σ→ι→ℂ) (y : σ→ι→ℝ)
    (A : Finset ι) (xj xc : ℝ) :
    (∑p∈I.pi L,(∏i∈I.attach,if p i.val i.property∈A then a i.val (p i.val i.property) else 0)*
      g (xj+xc-∑i∈I.attach,y i.val (p i.val i.property))) =
      ∫t:ℝ,density g xj t*kernelLogPhase t xc*
        primeMark I L (fun i p=>a i p*kernelLogPhase (-t) (y i p)) A := by
  simp_rw [tuple_mark_phase]
  simp only [Finset.mul_sum,density]
  have he (p : ∀i∈I,ι) (t:ℝ) :
      (𝓕 g) t*kernelLogPhase t xj*kernelLogPhase t xc*
        ((∏i∈I.attach,if p i.val i.property∈A then a i.val (p i.val i.property) else 0)*
          kernelLogPhase (-t) (∑i∈I.attach,y i.val (p i.val i.property))) =
      (𝓕 g) t*kernelLogPhase t (xj+xc-∑i∈I.attach,y i.val (p i.val i.property))*
        (∏i∈I.attach,if p i.val i.property∈A then a i.val (p i.val i.property) else 0) := by
    rw [←phase_sub]
    ring
  simp_rw [he]
  rw [integral_finsetSum _ (fun p hp=>fourier_phase_integrable g _ _)]
  apply Finset.sum_congr rfl
  intro p hp
  rw [integral_mul_const]
  have hinv := schwartz_phase_inversion g
    (xj+xc-∑i∈I.attach,y i.val (p i.val i.property))
  rw [mul_comm (∏i∈I.attach,if p i.val i.property∈A then a i.val (p i.val i.property) else 0)]
  congr 1
  rw [hinv]
  apply integral_congr_ae
  filter_upwards with t
  ring

theorem overlap_mode_integrable (g : 𝓢(ℝ,ℂ))
    (I : Finset σ) (L : σ→Finset ι) (a : σ→ι→ℂ) (y : σ→ι→ℝ)
    (A : Finset ι) (xj xc : ℝ) :
    Integrable (fun t:ℝ=>density g xj t*kernelLogPhase t xc*
      primeMark I L (fun i p=>a i p*kernelLogPhase (-t) (y i p)) A) := by
  simp_rw [tuple_mark_phase]
  simp only [Finset.mul_sum,density]
  apply integrable_finsetSum
  intro p hp
  convert fourier_phase_integrable g
    (xj+xc-∑i∈I.attach,y i.val (p i.val i.property))
    (∏i∈I.attach,if p i.val i.property∈A then a i.val (p i.val i.property) else 0) using 1 <;> first
  | rfl
  | (funext t; rw [←phase_sub]; ring)

theorem actual_overlap_separation
    (W : ℝ→ℂ) (a₀ b₀ : ℝ) (ha₀ : 0<a₀)
    (hs : Function.support W⊆Set.Icc a₀ b₀) (hW : ContDiff ℝ ∞ W)
    (I : Finset σ) (L : σ→Finset ι) (a : σ→ι→ℂ) (y : σ→ι→ℝ)
    (hy : ∀i∈I,∀p∈L i,0<y i p) (A : Finset ι)
    (yj yc : ℝ) (hj : 0<yj) (hc : 0<yc) :
    (∑p∈I.pi L,(∏i∈I.attach,if p i.val i.property∈A then a i.val (p i.val i.property) else 0)*
      W (yj*yc/(∏i∈I.attach,y i.val (p i.val i.property)))) =
      ∫t:ℝ,density (CanonicalCubeSeparation.sourceLogProfile W a₀ b₀ ha₀ hs hW) (Real.log yj) t*
        kernelLogPhase t (Real.log yc)*
        primeMark I L (fun i p=>a i p*kernelLogPhase (-t) (Real.log (y i p))) A := by
  rw [←overlap_tuple_separation]
  apply Finset.sum_congr rfl
  intro p hp
  congr 1
  simp only [CanonicalCubeSeparation.sourceLogProfile_apply,Real.exp_sub,Real.exp_add,
    Real.exp_log hj,Real.exp_log hc,Real.exp_sum]
  congr 2
  apply Finset.prod_congr rfl
  intro i hi
  exact (Real.exp_log (hy i.val i.property (p i.val i.property)
    ((Finset.mem_pi.mp hp) i.val i.property))).symm

end InverseInitialOverlapFourier

namespace InverseInitialArithmetic
open Eisenstein SchwartzPlanePoisson FirstPassCubeLabels SecondPassArithmetic
open InverseMoment InverseInitialFibers CompletedGauss
open scoped BigOperators Classical
local notation "λ₀" => lambda
variable {ι σ : Type*} [DecidableEq ι] [DecidableEq σ]
  (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i, λ₀ ∉ Ideal.span {p i})

private theorem initial_character_one (S : Finset ι) :
    primeSubsetRow p (fun i => complexSexticChar (Ideal.span {p i}) (hg i)) S 1 = 1 := by
  simp only [primeSubsetRow,map_one,Finset.prod_const_one]

def initialColumn (Ψ : O →* ℂ) (j C d h : O)
    (H : Finset ι→ℂ) (S : Finset ι) : ℂ :=
  secondColumnCoefficient p S * Ψ (∏ i∈S,p i) *
    primeCoprimeMask p S (j*C) *
    star (primeSubsetRow p (fun i => complexSexticChar (Ideal.span {p i}) (hg i)) S d) *
    primeSubsetRow p (fun i => complexSexticChar (Ideal.span {p i}) (hg i)) S h * H S

theorem initialColumn_eq_secondPre (Ψ : O →* ℂ) (j C d h : O)
    (H : Finset ι→ℂ) (S : Finset ι) :
    initialColumn p hg Ψ j C d h H S =
      secondPreColumn p hg Ψ (j*C) 1 1 d h H S := by
  have hone := initial_character_one p hg S
  simp only [initialColumn,secondPreColumn,hone,one_pow,mul_one]

include hp hcop in
theorem initial_common_extraction (hpr : ∀ i,λ₀^2∣p i-1)
    (Ψ : O →* ℂ) (j t d h : O) (H : Finset ι→ℂ)
    (V N : Finset ι) (hVN : Disjoint V N) :
    initialColumn p hg Ψ j (d*t) d h H (V∪N) =
      initialColumn p hg Ψ j (d*t) d h (fun _=>1) V *
      secondChildColumn p hg Ψ (j*t) (d*∏ i∈V,p i) (d*h)
        (fun U=>H (V∪U)) N := by
  simp only [initialColumn_eq_secondPre]
  simpa only [one_mul] using secondPreColumn_union p hg hp (fun i j hij => (Ideal.isCoprime_span_singleton_iff _ _).mp (hcop hij)) hpr Ψ j t 1 1 d h H V N hVN

theorem initial_marked_child (F V A : Finset ι) (Ψ : O →* ℂ) (j t d h : O)
    (slots : Finset σ) (lists : σ→Finset ι) (a : σ→ι→ℂ)
    (W : ℝ→ℂ) (X : ℝ) :
    (∑ N∈(F\V).powerset,
      secondChildColumn p hg Ψ (j*t) (d*∏ i∈V,p i) (d*h)
        (fun U=>primeMark slots lists a (A∪V∪U)*
          W (primeProductNorm p (V∪U)/X)) N) =
    ∑ J∈slots.powerset,primeMark J lists a (A∪V)*
      finiteCanonicalMarkedRow p hg F Ψ (j*t) (d*∏ i∈V,p i) (d*h)
        (slots\J) (fun i=>lists i\A) a W (X/primeProductNorm p V) := by
  simpa only [secondChildSum,one_mul,←Finset.union_assoc] using
    secondChildSum_marked_fixed_pool p hg F V A Ψ j t 1 1 d h slots lists a W X

theorem initial_input_row (F : Finset ι) (Ψ : O →* ℂ) (j : O)
    (H : Finset ι→ℂ) (z : O) :
    inputConjugateRow p (fun i => complexSexticChar (Ideal.span {p i}) (hg i)) F Ψ j 1 1 H z =
      supportConjugateSum p (fun i => complexSexticChar (Ideal.span {p i}) (hg i)) F
        (fun S=>Ψ (∏ i∈S,p i)*primeCoprimeMask p S j*H S) z := by
  unfold inputConjugateRow
  congr 1
  funext S
  have hone := initial_character_one p hg S
  simp only [secondInputCoefficient,hone,one_pow,mul_one]

include hp hcop in
theorem initial_pair_children
    (hinj : Function.Injective (fun i=>Ideal.span {p i}))
    (hpr : ∀ i,λ₀^2∣p i-1) (F : Finset ι) (Ψ₁ Ψ₂ : O →* ℂ)
    (j t d h₁ h₂ : O) (H₁ H₂ : Finset ι→ℂ) :
    (∑ S∈F.powerset,∑ T∈F.powerset,if Disjoint S T then
      star (initialColumn p hg Ψ₁ j (d*t) d h₁ H₁ S)*
        initialColumn p hg Ψ₂ j (d*t) d h₂ H₂ T else 0) =
    ∑ V∈F.powerset,
      (supportMobius V *
        star (initialColumn p hg Ψ₁ j (d*t) d h₁ (fun _=>1) V)*
          initialColumn p hg Ψ₂ j (d*t) d h₂ (fun _=>1) V) *
        star (∑ N∈(F\V).powerset,secondChildColumn p hg Ψ₁
          (j*t) (d*∏ i∈V,p i) (d*h₁) (fun U=>H₁ (V∪U)) N) *
        (∑ N∈(F\V).powerset,secondChildColumn p hg Ψ₂
          (j*t) (d*∏ i∈V,p i) (d*h₂) (fun U=>H₂ (V∪U)) N) := by
  simp only [initialColumn_eq_secondPre]
  simpa only [secondSeparatedPair,secondCommonWeight,secondChildSum,one_mul] using
    secondSeparatedPair_eq_children p hg hp (fun i j hij => (Ideal.isCoprime_span_singleton_iff _ _).mp (hcop hij)) hpr F Ψ₁ Ψ₂ j t 1 1 d h₁ h₂ H₁ H₂

include hp in
theorem initial_poisson_child_normalized
    (hpr : ∀ i,λ₀^2∣p i-1) (G E V : Finset ι) (Ψ : O →* ℂ)
    (j e t h : O) (he : Ideal.span {e}=sourceIdeal p E)
    (ht : Ideal.span {t}=sourceIdeal p (G\E)) :
    ∃ u : Oˣ, e=(u:O)*primaryIdealGenerator (sourceIdeal p E) ∧
      ∀ (H : Finset ι→ℂ) (N : Finset ι),
        secondChildColumn p hg Ψ (j*t) (e*∏ i∈V,p i) (e*h) H N =
          secondChildColumn p hg Ψ
            (j*primaryIdealGenerator (sourceIdeal p (G\E)))
            (primaryIdealGenerator (sourceIdeal p E*sourceIdeal p V))
            (primaryIdealGenerator (sourceIdeal p E)*((u:O)^5*h)) H N := by
  have hgE : primaryIdealGenerator (sourceIdeal p E)≠0 := by
    rw [sourceIdeal_gen p hp hpr E]
    exact Finset.prod_ne_zero_iff.mpr (fun i _=>hp i)
  obtain ⟨u,hu⟩ := generator_eq_unit_primary (sourceIdeal p E) e he hgE
  refine ⟨u,hu,?_⟩
  intro H N
  have hts : Ideal.span {t}=Ideal.span {primaryIdealGenerator (sourceIdeal p (G\E))} := by
    rw [ht,sourceIdeal_gen p hp hpr (G\E)]
    rfl
  have hmask := primeCoprimeMask_congr_span p N
    (show Ideal.span {j*t}=Ideal.span {j*primaryIdealGenerator (sourceIdeal p (G\E))} by
      rw [←Ideal.span_singleton_mul_span_singleton,←Ideal.span_singleton_mul_span_singleton,hts])
  have hchange : secondChildColumn p hg Ψ (j*t) (e*∏ i∈V,p i) (e*h) H N =
      secondChildColumn p hg Ψ (j*primaryIdealGenerator (sourceIdeal p (G\E)))
        (e*∏ i∈V,p i) (e*h) H N := by
    simp only [secondChildColumn,hmask]
  rw [hchange,hu,primaryIdealGenerator_mul,sourceIdeal_gen p hp hpr V]
  rw [mul_assoc (u:O)]
  exact secondChildColumn_generator_unit p hg Ψ u _ _ _ h H N

end InverseInitialArithmetic

namespace InverseAmbientProfileTower
open Eisenstein SchwartzPlanePoisson InverseMoment JointLogSeparation SecondPassArithmetic FirstPassCubeLabels MeasureTheory
open scoped BigOperators Classical SchwartzMap FourierTransform ContDiff

abbrev Ambient (ι : Type*) := Frequency × (ι → ℝ)

def ambientWeight {ι : Type*} [Fintype ι] (J : ℕ) (p : Ambient ι) : ℝ :=
  ((1 + ‖p.1.1‖)^J * (1 + ‖p.1.2.1‖)^J * (1 + ‖p.1.2.2‖)^J) *
    ∏ i, (1 + ‖p.2 i‖)^J

theorem ambientWeight_eq_pow {ι : Type*} [Fintype ι] (J : ℕ) (p : Ambient ι) :
    ambientWeight J p = (ambientWeight 1 p)^J := by
  simp [ambientWeight, mul_pow, Finset.prod_pow]

theorem ambientWeight_one_le {ι : Type*} [Fintype ι] (J : ℕ) (p : Ambient ι) :
    1 ≤ ambientWeight J p := by
  unfold ambientWeight
  exact one_le_mul_of_one_le_of_one_le
    (one_le_mul_of_one_le_of_one_le
      (one_le_mul_of_one_le_of_one_le (one_le_pow₀ (by linarith [norm_nonneg p.1.1]))
        (one_le_pow₀ (by linarith [norm_nonneg p.1.2.1])))
        (one_le_pow₀ (by linarith [norm_nonneg p.1.2.2])))
    (Finset.one_le_prod (fun i _ => one_le_pow₀ (by linarith [norm_nonneg (p.2 i)])))

theorem ambientWeight_add {ι : Type*} [Fintype ι] (J K : ℕ) (p : Ambient ι) :
    ambientWeight (J + K) p = ambientWeight J p * ambientWeight K p := by
  rw [ambientWeight_eq_pow (J+K), ambientWeight_eq_pow J, ambientWeight_eq_pow K, pow_add]

def inheritedLeft {ι : Type*} (i : ι) (p : Ambient ι) : ℝ :=
  p.2 i + p.1.1 - p.1.2.2

def inheritedRight {ι : Type*} (i : ι) (p : Ambient ι) : ℝ :=
  -(p.2 i + p.1.2.1 - p.1.2.2)

private theorem one_add_norm_add_le (x y : ℝ) :
    1 + ‖x + y‖ ≤ (1 + ‖x‖) * (1 + ‖y‖) := by
  have h := norm_add_le x y
  have hx := norm_nonneg x
  have hy := norm_nonneg y
  nlinarith [mul_nonneg hx hy]

private theorem coordinate_factor_le {ι : Type*} [Fintype ι]
    (i : ι) (u : ι → ℝ) :
    1 + ‖u i‖ ≤ ∏ j, (1 + ‖u j‖) :=
  by
  have hm (j : ι) : max (1 + ‖u j‖) 1 = 1 + ‖u j‖ :=
    max_eq_left (by linarith [norm_nonneg (u j)])
  simpa only [hm] using
    Finset.le_prod_max_one (Finset.mem_univ i) (fun j => 1 + ‖u j‖)

theorem inheritedLeft_bound {ι : Type*} [Fintype ι] (i : ι) (p : Ambient ι) :
    1 + ‖inheritedLeft i p‖ ≤ ambientWeight 1 p := by
  have h := (one_add_norm_add_le (p.2 i + p.1.1) (-p.1.2.2)).trans
    (mul_le_mul_of_nonneg_right (one_add_norm_add_le (p.2 i) p.1.1) (by positivity))
  simp only [norm_neg, ← sub_eq_add_neg] at h
  have hc := coordinate_factor_le i p.2
  have ht : (1 + ‖p.1.1‖) * (1 + ‖p.1.2.2‖) ≤
      (1 + ‖p.1.1‖) * (1 + ‖p.1.2.1‖) * (1 + ‖p.1.2.2‖) := by
    nlinarith [norm_nonneg p.1.1, norm_nonneg p.1.2.1, norm_nonneg p.1.2.2,
      mul_nonneg (mul_nonneg (show 0 ≤ 1 + ‖p.1.1‖ by positivity)
        (norm_nonneg p.1.2.1)) (show 0 ≤ 1 + ‖p.1.2.2‖ by positivity)]
  have hh := mul_le_mul hc ht (by positivity)
    (Finset.prod_nonneg (fun j _ => by positivity))
  change _ ≤ (∏ j, (1 + ‖p.2 j‖)) * _ at hh
  exact h.trans (by simpa [ambientWeight, inheritedLeft, mul_comm, mul_left_comm, mul_assoc] using hh)

theorem inheritedRight_bound {ι : Type*} [Fintype ι] (i : ι) (p : Ambient ι) :
    1 + ‖inheritedRight i p‖ ≤ ambientWeight 1 p := by
  have h := inheritedLeft_bound i ((p.1.2.1, p.1.1, p.1.2.2), p.2)
  change 1 + ‖-(p.2 i + p.1.2.1 - p.1.2.2)‖ ≤ _
  rw [norm_neg]
  simpa [inheritedLeft, ambientWeight, mul_comm, mul_left_comm, mul_assoc] using h

theorem inherited_pair_weight_bound {ι : Type*} [Fintype ι]
    (i j : ι) (J K : ℕ) (p : Ambient ι) :
    ambientWeight J p * ((1 + ‖inheritedLeft i p‖)^K *
      (1 + ‖inheritedRight j p‖)^K) ≤ ambientWeight (J + 2*K) p := by
  have h₁ := pow_le_pow_left₀ (by positivity) (inheritedLeft_bound i p) K
  have h₂ := pow_le_pow_left₀ (by positivity) (inheritedRight_bound j p) K
  have hh := mul_le_mul h₁ h₂ (by positivity)
    (pow_nonneg (le_trans zero_le_one (ambientWeight_one_le 1 p)) K)
  rw [← pow_add] at hh
  rw [ambientWeight_add, ambientWeight_eq_pow (2*K)]
  exact mul_le_mul_of_nonneg_left (by simpa [two_mul] using hh)
    (le_trans zero_le_one (ambientWeight_one_le J p))


end InverseAmbientProfileTower

namespace InverseInitialClippedColumns
open Eisenstein SchwartzPlanePoisson InverseMoment JointLogSeparation SecondPassArithmetic FirstPassCubeLabels MeasureTheory
open scoped BigOperators Classical SchwartzMap FourierTransform ContDiff

def clippedTest (w : ℝ → ℂ) (c h : ℝ) : ℝ → ℂ :=
  childLogTest (fun x => w (c*x)) h

theorem clippedTest_eq_source (w : ℝ → ℂ) (c h x : ℝ) :
    clippedTest w c h x = InverseInitialProfile.clippedSource w c h x := by
  unfold clippedTest childLogTest InverseInitialProfile.clippedSource
  ring

theorem child_test_clipping (w : ℝ → ℂ) {Z q : ℝ} (hZ : 0 < Z) (hq : 0 < q)
    (N h : ℝ) :
    childLogTest w h (q/Z^N) = kernelLogPhase h (Real.log (Z^(max 0 N-N))) *
      clippedTest w (Z^(max 0 N-N)) h (q/Z^(max 0 N)) := by
  rw [clippedTest_eq_source]
  simpa only [childLogTest,mul_comm] using
    InverseInitialProfile.clipped_column_source_identity w hZ hq N h

section Arithmetic
variable {ι σ : Type*} [DecidableEq ι]
  (p : ι → O) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hg : ∀ i, lambda ∉ Ideal.span {p i})

def freshColumns (pool : Finset ι) (w : ℝ → ℂ) (X : ℝ) : Finset (Finset ι) :=
  pool.powerset.filter (fun U => w (primeProductNorm p U/X) ≠ 0)

omit [DecidableEq ι] [∀ i, (Ideal.span {p i}).IsMaximal] in
theorem mem_freshColumns (pool : Finset ι) (w : ℝ → ℂ) (X : ℝ) (U : Finset ι) :
    U ∈ freshColumns p pool w X ↔ U ⊆ pool ∧ w (primeProductNorm p U/X) ≠ 0 := by
  simp [freshColumns]

omit [DecidableEq ι] [∀ i, (Ideal.span {p i}).IsMaximal] in
theorem freshColumns_clipping_range (hp : ∀ i, p i ≠ 0) (pool : Finset ι) (w : ℝ → ℂ)
    (a b Z N : ℝ) (hZ : 1 < Z) (hb : 1 ≤ b)
    (hw : Function.support w ⊆ Set.Icc a b)
    (hn : (freshColumns p pool w (Z^N)).Nonempty) :
    1 ≤ Z^(max 0 N-N) ∧ Z^(max 0 N-N) ≤ b := by
  obtain ⟨U,hU⟩ := hn
  exact InverseClippingProfiles.clipping_ratio_of_column_witness w Z N
    (primeProductNorm p U) a b hZ (primeProductNorm_ge_one p hp U) hb hw
    ((mem_freshColumns p pool w (Z^N) U).mp hU).2

omit [DecidableEq ι] [∀ i, (Ideal.span {p i}).IsMaximal] in
theorem freshColumns_initial_clipping_shift (hp : ∀ i, p i ≠ 0) (pool : Finset ι) (w : ℝ → ℂ)
    (a b Z N η : ℝ) (hZ : 1 < Z) (hb : 1 ≤ b)
    (hw : Function.support w ⊆ Set.Icc a b)
    (hn : (freshColumns p pool w (Z^N)).Nonempty)
    (hthreshold : Real.log b ≤ 3*η*Real.log Z) :
    0 ≤ max 0 N-N ∧ max 0 N-N ≤ 3*η := by
  have hc := freshColumns_clipping_range p hp pool w a b Z N hZ hb hw hn
  have hz : 0 < Z := zero_lt_one.trans hZ
  have hl := Real.log_le_log (Real.rpow_pos_of_pos hz _) hc.2
  rw [Real.log_rpow hz] at hl
  refine ⟨sub_nonneg.mpr (le_max_right _ _), ?_⟩
  exact (mul_le_mul_iff_left₀ (Real.log_pos hZ)).mp (hl.trans hthreshold)

omit [DecidableEq ι] [∀ i, (Ideal.span {p i}).IsMaximal] in
theorem clippedTest_support_of_freshColumns (hp : ∀ i, p i ≠ 0) (pool : Finset ι) (w : ℝ → ℂ)
    (a b Z N h : ℝ) (ha : 0 < a) (hb : 1 ≤ b) (hZ : 1 < Z)
    (hw : Function.support w ⊆ Set.Icc a b)
    (hn : (freshColumns p pool w (Z^N)).Nonempty) :
    Function.support (clippedTest w (Z^(max 0 N-N)) h) ⊆ Set.Icc (a/b) b := by
  obtain ⟨hc,hcb⟩ := freshColumns_clipping_range p hp pool w a b Z N hZ hb hw hn
  have hs := InverseClippingProfiles.clipped_positive_support w a b _ ha hc hcb hw
  intro x hx
  exact hs (mul_ne_zero_iff.mp hx).1

theorem canonical_row_zero_of_freshColumns_empty
    (pool : Finset ι) (Ψ : O →* ℂ) (m f k : O)
    (slots : Finset σ) (lists : σ → Finset ι) (a : σ → ι → ℂ)
    (w : ℝ → ℂ) (X h : ℝ) (he : freshColumns p pool w X = ∅) :
    finiteCanonicalMarkedRow p hg pool Ψ m f k slots lists a
      (childLogTest w h) X = 0 := by
  unfold finiteCanonicalMarkedRow fixedChildRow
  apply Finset.sum_eq_zero
  intro U hU
  have hw : w (primeProductNorm p U/X) = 0 := by
    by_contra hw
    have hu : U ∈ freshColumns p pool w X := Finset.mem_filter.mpr ⟨hU,hw⟩
    rw [he] at hu
    exact Finset.notMem_empty U hu
  simp only [secondChildColumn,childLogTest,hw,zero_mul,mul_zero]

theorem canonical_row_nonzero_freshColumns
    (pool : Finset ι) (Ψ : O →* ℂ) (m f k : O)
    (slots : Finset σ) (lists : σ → Finset ι) (a : σ → ι → ℂ)
    (w : ℝ → ℂ) (X h : ℝ)
    (hn : finiteCanonicalMarkedRow p hg pool Ψ m f k slots lists a
      (childLogTest w h) X ≠ 0) : (freshColumns p pool w X).Nonempty := by
  by_contra he
  exact hn (canonical_row_zero_of_freshColumns_empty p hg pool Ψ m f k
    slots lists a w X h (Finset.not_nonempty_iff_eq_empty.mp he))

theorem canonical_row_clipping
    (hp : ∀ i, p i ≠ 0)
    (pool : Finset ι) (Ψ : O →* ℂ) (m f k : O)
    (slots : Finset σ) (lists : σ → Finset ι) (a : σ → ι → ℂ)
    (w : ℝ → ℂ) {Z : ℝ} (hZ : 0 < Z) (N h : ℝ) :
    finiteCanonicalMarkedRow p hg pool Ψ m f k slots lists a
      (childLogTest w h) (Z^N) =
      kernelLogPhase h (Real.log (Z^(max 0 N-N))) *
        finiteCanonicalMarkedRow p hg pool Ψ m f k slots lists a
          (clippedTest w (Z^(max 0 N-N)) h) (Z^(max 0 N)) := by
  unfold finiteCanonicalMarkedRow fixedChildRow
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro U hU
  simp only [secondChildColumn]
  rw [child_test_clipping w hZ (primeProductNorm_pos p hp U) N h]
  ring

theorem canonical_row_clipping_norm
    (hp : ∀ i, p i ≠ 0)
    (pool : Finset ι) (Ψ : O →* ℂ) (m f k : O)
    (slots : Finset σ) (lists : σ → Finset ι) (a : σ → ι → ℂ)
    (w : ℝ → ℂ) {Z : ℝ} (hZ : 0 < Z) (N h : ℝ) :
    ‖finiteCanonicalMarkedRow p hg pool Ψ m f k slots lists a
      (childLogTest w h) (Z^N)‖ =
    ‖finiteCanonicalMarkedRow p hg pool Ψ m f k slots lists a
      (clippedTest w (Z^(max 0 N-N)) h) (Z^(max 0 N))‖ := by
  rw [canonical_row_clipping p hg hp pool Ψ m f k slots lists a w hZ N h,
    norm_mul,kernelLogPhase_norm,one_mul]

def columnEnergy (pool : Finset ι) (Ψ : O →* ℂ) (m : O)
    (slots : Finset σ) (lists : σ → Finset ι) (a : σ → ι → ℂ)
    (labels : Finset (Ideal O)) (rows : Finset O) (D : Ideal O → ℝ)
    (W : ℝ → ℂ) (X : ℝ) : ℝ :=
  ∑ f ∈ labels, D f * ∑ k ∈ rows,
    ‖finiteCanonicalMarkedRow p hg pool Ψ m (primaryIdealGenerator f) k
      slots lists a W X‖^2

theorem columnEnergy_clipping
    (hp : ∀ i, p i ≠ 0)
    (pool : Finset ι) (Ψ : O →* ℂ) (m : O)
    (slots : Finset σ) (lists : σ → Finset ι) (a : σ → ι → ℂ)
    (labels : Finset (Ideal O)) (rows : Finset O) (D : Ideal O → ℝ)
    (w : ℝ → ℂ) {Z : ℝ} (hZ : 0 < Z) (N h : ℝ) :
    columnEnergy p hg pool Ψ m slots lists a labels rows D
      (childLogTest w h) (Z^N) =
    columnEnergy p hg pool Ψ m slots lists a labels rows D
      (clippedTest w (Z^(max 0 N-N)) h) (Z^(max 0 N)) := by
  unfold columnEnergy
  simp_rw [canonical_row_clipping_norm p hg hp pool Ψ m _ _ slots lists a w hZ N h]

theorem canonical_pair_clipping
    (hp : ∀ i, p i ≠ 0)
    (pool : Finset ι) (Ψ : O →* ℂ) (m f k : O)
    (slots₁ slots₂ : Finset σ) (lists₁ lists₂ : σ → Finset ι)
    (a₁ a₂ : σ → ι → ℂ) (w₁ w₂ : ℝ → ℂ)
    {Z : ℝ} (hZ : 0 < Z) (N h₁ h₂ : ℝ) :
    finiteCanonicalMarkedRow p hg pool Ψ m f k slots₁ lists₁ a₁
      (childLogTest w₁ h₁) (Z^N) *
    star (finiteCanonicalMarkedRow p hg pool Ψ m f k slots₂ lists₂ a₂
      (childLogTest w₂ (-h₂)) (Z^N)) =
    kernelLogPhase (h₁+h₂) (Real.log (Z^(max 0 N-N))) *
      (finiteCanonicalMarkedRow p hg pool Ψ m f k slots₁ lists₁ a₁
        (clippedTest w₁ (Z^(max 0 N-N)) h₁) (Z^(max 0 N)) *
      star (finiteCanonicalMarkedRow p hg pool Ψ m f k slots₂ lists₂ a₂
        (clippedTest w₂ (Z^(max 0 N-N)) (-h₂)) (Z^(max 0 N)))) := by
  rw [canonical_row_clipping p hg hp pool Ψ m f k slots₁ lists₁ a₁ w₁ hZ,
    canonical_row_clipping p hg hp pool Ψ m f k slots₂ lists₂ a₂ w₂ hZ]
  simp only [star_mul,JointLogSeparation.kernelLogPhase_conjugate,neg_neg,
    kernelLogPhase_add_frequency]
  ring

theorem canonical_pair_clipping_left_conjugate
    (hp : ∀ i, p i ≠ 0)
    (pool : Finset ι) (Ψ : O →* ℂ) (m f k : O)
    (slots₁ slots₂ : Finset σ) (lists₁ lists₂ : σ → Finset ι)
    (a₁ a₂ : σ → ι → ℂ) (w₁ w₂ : ℝ → ℂ)
    {Z : ℝ} (hZ : 0 < Z) (N h₁ h₂ : ℝ) :
    star (finiteCanonicalMarkedRow p hg pool Ψ m f k slots₁ lists₁ a₁
      (childLogTest w₁ (-h₁)) (Z^N)) *
    finiteCanonicalMarkedRow p hg pool Ψ m f k slots₂ lists₂ a₂
      (childLogTest w₂ h₂) (Z^N) =
    kernelLogPhase (h₁+h₂) (Real.log (Z^(max 0 N-N))) *
      (star (finiteCanonicalMarkedRow p hg pool Ψ m f k slots₁ lists₁ a₁
        (clippedTest w₁ (Z^(max 0 N-N)) (-h₁)) (Z^(max 0 N))) *
      finiteCanonicalMarkedRow p hg pool Ψ m f k slots₂ lists₂ a₂
        (clippedTest w₂ (Z^(max 0 N-N)) h₂) (Z^(max 0 N))) := by
  rw [canonical_row_clipping p hg hp pool Ψ m f k slots₁ lists₁ a₁ w₁ hZ,
    canonical_row_clipping p hg hp pool Ψ m f k slots₂ lists₂ a₂ w₂ hZ]
  simp only [star_mul,JointLogSeparation.kernelLogPhase_conjugate,neg_neg,
    kernelLogPhase_add_frequency]
  ring

def normalizedColumnEnergy (pool : Finset ι) (Ψ : O →* ℂ) (m : O)
    (slots : Finset σ) (lists : σ → Finset ι) (a : σ → ι → ℂ)
    (labels : Finset (Ideal O)) (rows : Finset O) (D : Ideal O → ℝ)
    (W : ℝ → ℂ) (X Z F : ℝ) : ℝ :=
  ∑ f ∈ labels, D f * ∑ k ∈ rows,
    ‖((Z^(-F/2) : ℝ) : ℂ) *
      finiteCanonicalMarkedRow p hg pool Ψ m (primaryIdealGenerator f) k
        slots lists a W X‖^2

theorem columnEnergy_normalization
    (pool : Finset ι) (Ψ : O →* ℂ) (m : O)
    (slots : Finset σ) (lists : σ → Finset ι) (a : σ → ι → ℂ)
    (labels : Finset (Ideal O)) (rows : Finset O) (D : Ideal O → ℝ)
    (W : ℝ → ℂ) (X : ℝ) {Z : ℝ} (hZ : 0 < Z) (F : ℝ) :
    columnEnergy p hg pool Ψ m slots lists a labels rows D W X =
      Z^F * normalizedColumnEnergy p hg pool Ψ m slots lists a
        labels rows D W X Z F := by
  have hr : Z^F * (Z^(-F/2))^2 = 1 := by
    rw [← Real.rpow_mul_natCast hZ.le, ← Real.rpow_add hZ]
    rw [show F+(-F/2)*(2:ℕ) = 0 by ring, Real.rpow_zero]
  unfold columnEnergy normalizedColumnEnergy
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro f hf
  rw [← mul_assoc, mul_comm (Z^F) (D f), mul_assoc]
  congr 1
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,
    abs_of_pos (Real.rpow_pos_of_pos hZ _),mul_pow,← mul_assoc,hr,one_mul]

theorem initial_columnEnergy_clipping_normalized
    (hp : ∀ i, p i ≠ 0)
    (pool : Finset ι) (Ψ : O →* ℂ) (m : O)
    (slots : Finset σ) (lists : σ → Finset ι) (a : σ → ι → ℂ)
    (labels : Finset (Ideal O)) (rows : Finset O) (D : Ideal O → ℝ)
    (w : ℝ → ℂ) {Z : ℝ} (hZ : 0 < Z) (N V h : ℝ) :
    columnEnergy p hg pool Ψ m slots lists a labels rows D
      (childLogTest w h) (Z^N) =
      Z^(max 0 N+V) * normalizedColumnEnergy p hg pool Ψ m slots lists a
        labels rows D (clippedTest w (Z^(max 0 N-N)) h) (Z^(max 0 N)) Z (max 0 N+V) := by
  rw [columnEnergy_clipping p hg hp pool Ψ m slots lists a labels rows D w hZ N h]
  exact columnEnergy_normalization p hg pool Ψ m slots lists a labels rows D
    _ _ hZ _

end Arithmetic

def leftHeight (z : Frequency × (Fin 6 → ℝ)) : ℝ := z.2 4+z.1.1-z.1.2.2
def rightHeight (z : Frequency × (Fin 6 → ℝ)) : ℝ := z.2 5+z.1.2.1-z.1.2.2

theorem leftHeight_eq (z : Frequency × (Fin 6 → ℝ)) :
    leftHeight z = profileHeight secondLeftSlope secondRightSlope secondKernelSlope z.1 z.2 4 := by
  simp [leftHeight,profileHeight,secondLeftSlope,secondRightSlope,secondKernelSlope]
  ring

theorem rightHeight_eq (z : Frequency × (Fin 6 → ℝ)) :
    rightHeight z = profileHeight secondLeftSlope secondRightSlope secondKernelSlope z.1 z.2 5 := by
  simp [rightHeight,profileHeight,secondLeftSlope,secondRightSlope,secondKernelSlope]
  ring

def clippingPhase (c : ℝ) (z : Frequency × (Fin 6 → ℝ)) : ℂ :=
  kernelLogPhase (leftHeight z+rightHeight z) (Real.log c)

theorem clippingPhase_norm (c : ℝ) (z : Frequency × (Fin 6 → ℝ)) :
    ‖clippingPhase c z‖ = 1 := kernelLogPhase_norm _ _

theorem clippingPhase_continuous (c : ℝ) : Continuous (clippingPhase c) := by
  unfold clippingPhase leftHeight rightHeight kernelLogPhase
  fun_prop

theorem fresh_pair_mode_clipping (w₁ w₂ : ℝ → ℂ)
    {Z q₁ q₂ : ℝ} (hZ : 0 < Z) (hq₁ : 0 < q₁) (hq₂ : 0 < q₂)
    (N : ℝ) (y : Fin 6 → ℝ) (z : Frequency × (Fin 6 → ℝ))
    (hy₁ : y 4 = Real.log (q₁/Z^N)) (hy₂ : y 5 = Real.log (q₂/Z^N)) :
    (w₁ (q₁/Z^N)*star (w₂ (q₂/Z^N))) *
      pureProfileMode secondLeftSlope secondRightSlope secondKernelSlope y z.1 z.2 =
    secondOuterPhase (profileHeight secondLeftSlope secondRightSlope secondKernelSlope z.1 z.2) y *
      clippingPhase (Z^(max 0 N-N)) z *
      (clippedTest w₁ (Z^(max 0 N-N)) (leftHeight z) (q₁/Z^(max 0 N)) *
      star (clippedTest w₂ (Z^(max 0 N-N)) (-rightHeight z) (q₂/Z^(max 0 N)))) := by
  rw [second_mode_split,← leftHeight_eq,← rightHeight_eq,hy₁,hy₂]
  have h1 := child_test_clipping w₁ hZ hq₁ N (leftHeight z)
  have h2 := child_test_clipping w₂ hZ hq₂ N (-rightHeight z)
  calc
    _ = secondOuterPhase
        (profileHeight secondLeftSlope secondRightSlope secondKernelSlope z.1 z.2) y *
        (childLogTest w₁ (leftHeight z) (q₁/Z^N) *
          star (childLogTest w₂ (-rightHeight z) (q₂/Z^N))) := by
      simp only [childLogTest,star_mul,JointLogSeparation.kernelLogPhase_conjugate,neg_neg]
      ring
    _ = _ := by
      rw [h1,h2]
      simp only [clippingPhase,star_mul,JointLogSeparation.kernelLogPhase_conjugate,
        neg_neg,kernelLogPhase_add_frequency]
      ring

theorem child_height_moment_bound (K : ℕ) (z : Frequency × (Fin 6 → ℝ)) :
    (1+‖leftHeight z‖)^K * (1+‖rightHeight z‖)^K ≤
      tripleHeight (2*K) z.1 * coordinateHeight (2*K) z.2 := by
  have hh := InverseAmbientProfileTower.inherited_pair_weight_bound 4 5 0 K z
  simpa only [InverseAmbientProfileTower.ambientWeight,
    InverseAmbientProfileTower.inheritedLeft,InverseAmbientProfileTower.inheritedRight,
    leftHeight,rightHeight,norm_neg,pow_zero,Finset.prod_const_one,
    mul_one,one_mul,zero_add,tripleHeight,coordinateHeight] using hh

def outerCutoff (ψ : Fin 4 → ℝ → ℂ) (x : Fin 6 → ℝ) : ℂ :=
  ψ 0 (x 0)*ψ 1 (x 1)*ψ 2 (x 2)*ψ 3 (x 3)

def retainedCutoffs (ψ : Fin 4 → ℝ → ℂ) (w₁ w₂ : ℝ → ℂ) : Fin 6 → ℝ → ℂ :=
  ![ψ 0,ψ 1,ψ 2,ψ 3,w₁,w₂]

theorem retainedCutoffs_nonzero (ψ : Fin 4 → ℝ → ℂ) (w₁ w₂ : ℝ → ℂ)
    (x : Fin 6 → ℝ) (ho : outerCutoff ψ x ≠ 0)
    (h₁ : w₁ (x 4) ≠ 0) (h₂ : w₂ (x 5) ≠ 0) :
    ∀ i, retainedCutoffs ψ w₁ w₂ i (x i) ≠ 0 := by
  have h := mul_ne_zero_iff.mp ho
  have h' := mul_ne_zero_iff.mp h.1
  have h'' := mul_ne_zero_iff.mp h'.1
  intro i
  fin_cases i <;> simp only [retainedCutoffs]
  · exact h''.1
  · exact h''.2
  · exact h'.2
  · exact h.2
  · exact h₁
  · exact h₂

theorem larger_windows_one (ψ : Fin 4 → ℝ → ℂ) (w₁ w₂ : ℝ → ℂ)
    (Ω : Fin 6 → ℝ → ℂ)
    (hΩ : ∀ i x, retainedCutoffs ψ w₁ w₂ i x ≠ 0 → Ω i x = 1)
    (x : Fin 6 → ℝ) (hx : ∀ i, 0 < x i) (ho : outerCutoff ψ x ≠ 0)
    (h₁ : w₁ (x 4) ≠ 0) (h₂ : w₂ (x 5) ≠ 0) :
    ∀ i, Ω i (Real.exp (Real.log (x i))) = 1 := by
  intro i
  rw [Real.exp_log (hx i)]
  exact hΩ i (x i) (retainedCutoffs_nonzero ψ w₁ w₂ x ho h₁ h₂ i)

theorem retained_physical_kernel_restore
    (W₁ W₂ w₁ w₂ : ℝ → ℂ) (Φ : 𝓢(ℝ, ℂ))
    (ψ : Fin 4 → ℝ → ℂ) (Ω : Fin 6 → ℝ → ℂ)
    (a b A₀ B₀ A₂ B₂ : ℝ) (hA₀ : 0 < A₀) (hA₂ : 0 < A₂)
    (hW₁ : Function.support W₁ ⊆ Set.Icc a b)
    (hW₂ : Function.support W₂ ⊆ Set.Icc a b)
    (hψ₀ : ∀ x, ψ 0 x ≠ 0 → x ∈ Set.Icc A₀ B₀)
    (hψ₂ : ∀ x, ψ 2 x ≠ 0 → x ∈ Set.Icc A₂ B₂)
    (hw₁ : ∀ x ∈ Set.Icc (a/(B₀*B₂)) (b/(A₀*A₂)), w₁ x = 1)
    (hw₂ : ∀ x ∈ Set.Icc (a/(B₀*B₂)) (b/(A₀*A₂)), w₂ x = 1)
    (hΩ : ∀ i x, retainedCutoffs ψ w₁ w₂ i x ≠ 0 → Ω i x = 1)
    {Z : ℝ} (hZ : 0 < Z) (D B v m θ H η : ℝ)
    (q : Fin 6 → ℝ) (hq : ∀ i, 0 < q i) :
    let x := InverseInitialProfile.relativeNorm q Z D B v θ H
    outerCutoff ψ x * InverseInitialProfile.physicalKernel W₁ W₂ Φ Z D m q =
      (Z^(InverseInitialProfile.prefactorCenter m D B θ+3*η) : ℝ) *
        outerCutoff ψ x * (w₁ (x 4)*w₂ (x 5)) *
        InverseInitialProfile.normalizedProfile W₁ W₂ Φ (fun i y => Ω i (Real.exp y))
          (Z^(InverseInitialProfile.radialCenter m H θ D B)) (η*Real.log Z)
          (InverseInitialProfile.relativeLog q Z D B v θ H) := by
  dsimp only
  let x := InverseInitialProfile.relativeNorm q Z D B v θ H
  have hx : ∀ i, 0 < x i := InverseInitialProfile.relativeNorm_pos q hq hZ D B v θ H
  by_cases ho : outerCutoff ψ x = 0
  · change outerCutoff ψ x * _ = _ * outerCutoff ψ x * _ * _
    simp only [ho,zero_mul,mul_zero]
  have hc : ψ 0 (x 0) ≠ 0 := ((mul_ne_zero_iff.mp (mul_ne_zero_iff.mp ho).1).1 |> mul_ne_zero_iff.mp).1
  have hs : ψ 2 (x 2) ≠ 0 := (mul_ne_zero_iff.mp (mul_ne_zero_iff.mp ho).1).2
  have h1 : W₁ (x 0*x 2*x 4) ≠ 0 → w₁ (x 4) = 1 :=
    fresh_window_eq_one W₁ w₁ a b A₀ B₀ A₂ B₂ (x 0) (x 2) (x 4)
      hW₁ hA₀ hA₂ (hψ₀ _ hc) (hψ₂ _ hs) (hx 4).le hw₁
  have h2 : W₂ (x 0*x 2*x 5) ≠ 0 → w₂ (x 5) = 1 :=
    fresh_window_eq_one W₂ w₂ a b A₀ B₀ A₂ B₂ (x 0) (x 2) (x 5)
      hW₂ hA₀ hA₂ (hψ₀ _ hc) (hψ₂ _ hs) (hx 5).le hw₂
  have hcut : w₁ (x 4) ≠ 0 → w₂ (x 5) ≠ 0 →
      ∀ i, Ω i (Real.exp (InverseInitialProfile.relativeLog q Z D B v θ H i)) = 1 := by
    intro hleft hright
    exact larger_windows_one ψ w₁ w₂ Ω hΩ x hx ho hleft hright
  have he := InverseInitialProfile.initial_kernel_restore W₁ W₂ w₁ w₂ Φ
    (fun i y => Ω i (Real.exp y)) hZ D B v m θ H η q hq h1 h2 hcut
  rw [he]
  ring

end InverseInitialClippedColumns

namespace InverseInitialProfileBounds
open Eisenstein SchwartzPlanePoisson InverseMoment JointLogSeparation SecondPassArithmetic FirstPassCubeLabels MeasureTheory
open scoped BigOperators Classical SchwartzMap FourierTransform ContDiff

open InverseInitialProfile
theorem clipped_norm (W:ℝ→ℂ)(c θ x:ℝ):‖clippedSource W c θ x‖=‖W (c*x)‖:=by
  simp only [clippedSource,norm_mul,kernelLogPhase_norm,one_mul]

theorem clipped_bound (W:ℝ→ℂ)(B:ℝ)(hW:∀x,‖W x‖≤B)(c θ x:ℝ):
    ‖clippedSource W c θ x‖≤B:=by rw [clipped_norm];exact hW _

theorem clipped_support (W:ℝ→ℂ)(a b c cmax θ:ℝ)(ha:0<a)(hc:1≤c)(hcm:c≤cmax)
    (hW:Function.support W⊆Set.Icc a b):
    Function.support (clippedSource W c θ)⊆Set.Icc (a/cmax) b:=by
  intro x hx
  have hn:W (c*x)≠0:=(mul_ne_zero_iff.mp hx).2
  have hs:=hW hn
  have hcp:0<c:=zero_lt_one.trans_le hc
  have hxpos:0<x:=pos_of_mul_pos_right (ha.trans_le hs.1) hcp.le
  constructor
  · apply (div_le_iff₀ (hcp.trans_le hcm)).mpr
    exact hs.1.trans (by nlinarith)
  · have hxc:x≤c*x:=le_mul_of_one_le_left hxpos.le hc
    exact hxc.trans hs.2

theorem clipped_support_upper (W:ℝ→ℂ)(a b c θ:ℝ)(ha:0<a)(hc:1≤c)
    (hW:Function.support W⊆Set.Icc a b):Function.support (clippedSource W c θ)⊆Set.Iic b:=
  fun _ hx=>(clipped_support W a b c c θ ha hc le_rfl hW hx).2

theorem childLogTest_eq_clipped (W:ℝ→ℂ)(θ:ℝ):childLogTest W θ=clippedSource W 1 θ:=by
  funext x
  simp only [childLogTest,clippedSource,mul_comm,mul_one]

theorem childLogTest_norm (W:ℝ→ℂ)(θ x:ℝ):‖childLogTest W θ x‖=‖W x‖:=by
  rw [childLogTest_eq_clipped,clipped_norm,one_mul]

end InverseInitialProfileBounds

namespace InverseInitialRayAttachment
open Eisenstein SchwartzPlanePoisson SecondPassArithmetic FirstPassCubeLabels
open RayFourExpansion InitialMeanSquare InverseInitialArithmetic
open scoped BigOperators Classical

/-- The total residue phase in the mixed Gauss reflection. -/
def initialTracePhase (r : QuadraticRayRing) : ℂ :=
  initialResiduePhase r / rayQuadraticPhase r

def initialPairPhase (r s : QuadraticRayRing) : ℂ :=
  rayQuadraticPair r s * star (initialTracePhase r) * initialTracePhase s

def initialPairCoefficient (χ η : RayCharacter) : ℂ :=
  phaseCoeff (fun s => phaseCoeff (fun r => initialPairPhase r s) χ) η

theorem initial_pair_phase_expansion (x y : O)
    (hx : IsUnit (Ideal.Quotient.mk (Ideal.span {(4 : O)}) x))
    (hy : IsUnit (Ideal.Quotient.mk (Ideal.span {(4 : O)}) y)) :
    initialPairPhase (Ideal.Quotient.mk (Ideal.span {(4 : O)}) x)
      (Ideal.Quotient.mk (Ideal.span {(4 : O)}) y) =
      ∑ χ : RayCharacter, ∑ η : RayCharacter,
        initialPairCoefficient χ η * rayMonoid χ x * rayMonoid η y := by
  have h₁ := phase_expansion
    (fun r => initialPairPhase r (Ideal.Quotient.mk (Ideal.span {(4 : O)}) y)) x
  rw [if_pos hx,one_mul] at h₁
  rw [h₁]
  apply Finset.sum_congr rfl
  intro χ hχ
  have h₂ := phase_expansion (fun s => phaseCoeff (fun r => initialPairPhase r s) χ) y
  rw [if_pos hy,one_mul] at h₂
  rw [h₂,Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro η hη
  unfold initialPairCoefficient
  ring

abbrev SecondRayIndex := RayCharacter × RayCharacter

def secondRayCoefficient (ρ : SecondRayIndex) : ℂ := initialPairCoefficient ρ.1 ρ.2

def secondRayMinus (Ψ : O →* ℂ) (ρ : SecondRayIndex) : O →* ℂ :=
  ((starRingEnd ℂ).toMonoidHom.comp (rayMonoid ρ.1)) * Ψ

def secondRayPlus (Ψ : O →* ℂ) (ρ : SecondRayIndex) : O →* ℂ :=
  rayMonoid ρ.2 * Ψ

@[simp] theorem secondRayMinus_apply (Ψ : O →* ℂ) (ρ : SecondRayIndex) (x : O) :
    secondRayMinus Ψ ρ x = star (rayMonoid ρ.1 x) * Ψ x := rfl

@[simp] theorem secondRayPlus_apply (Ψ : O →* ℂ) (ρ : SecondRayIndex) (x : O) :
    secondRayPlus Ψ ρ x = rayMonoid ρ.2 x * Ψ x := rfl

variable {ι : Type*} [DecidableEq ι] (p : ι → O) (hp : ∀ i,p i ≠ 0)
  [∀ i,(Ideal.span {p i}).IsMaximal] (hg : ∀ i,lambda ∉ Ideal.span {p i})

theorem subsetTraceRayFactor_eq_phase
    (hc : ∀ i,ringChar (O ⧸ Ideal.span {p i}) ≠ 2)
    (hpr : ∀ i,lambda ^ 2 ∣ p i - 1) (S : Finset ι) :
    subsetTraceRayFactor p hg S =
      initialTracePhase (Ideal.Quotient.mk (Ideal.span {(4 : O)}) (∏ i ∈ S,p i)) := by
  rw [subsetTraceRayFactor_eq_row,initial_row_four p hg hc hpr,
    initialTracePhase,initialResiduePhase_mk]

/-- Finite residue Fourier expansion turns the reflection phase into character twists. -/
theorem initial_gauss_ray_expansion
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (hc : ∀ i,ringChar (O ⧸ Ideal.span {p i}) ≠ 2)
    (hpr : ∀ i,lambda ^ 2 ∣ p i - 1)
    (Ψ₁ Ψ₂ : O →* ℂ) (m c d e k : O) (H₁ H₂ : Finset ι → ℂ)
    (S T : Finset ι) (hd : Disjoint S T) :
    star (supportMobius S * secondInputCoefficient p
      (fun i => complexSexticChar (Ideal.span {p i}) (hg i)) Ψ₁ m c d H₁ S) *
      (supportMobius T * secondInputCoefficient p
      (fun i => complexSexticChar (Ideal.span {p i}) (hg i)) Ψ₂ m c d H₂ T) *
      secondNormalizedGaussTerm p hp hg S T e k =
      ∑ ρ : SecondRayIndex,secondRayCoefficient ρ *
        star (secondPreColumn p hg (secondRayMinus Ψ₁ ρ) m c d e k H₁ S) *
        secondPreColumn p hg (secondRayPlus Ψ₂ ρ) m c d e (-k) H₂ T := by
  have hunit (U : Finset ι) :
      IsUnit (Ideal.Quotient.mk (Ideal.span {(4 : O)}) (∏ i ∈ U,p i)) := by
    induction U using Finset.induction_on with
    | empty => simp
    | @insert i U hi ih =>
      rw [Finset.prod_insert hi,map_mul]
      exact (prime_unit_mod_four (p i) (hc i)).mul ih
  have hpre (Ψ : O →* ℂ) (H : Finset ι → ℂ) (U : Finset ι) (k : O) :
      secondPreColumn p hg Ψ m c d e k (fun A => subsetTraceRayFactor p hg A * H A) U =
        initialTracePhase (Ideal.Quotient.mk (Ideal.span {(4 : O)}) (∏ i ∈ U,p i)) *
          secondPreColumn p hg Ψ m c d e k H U := by
    rw [secondPreColumn,subsetTraceRayFactor_eq_phase p hg hc hpr]
    unfold secondPreColumn
    ring
  rw [secondGaussTerm_restoration p hp hg hinj hc hpr Ψ₁ Ψ₂ m c d e k H₁ H₂ S T hd]
  rw [hpre,hpre,star_mul]
  have he := initial_pair_phase_expansion (∏ i ∈ S,p i) (∏ i ∈ T,p i) (hunit S) (hunit T)
  calc
    _ = initialPairPhase (Ideal.Quotient.mk (Ideal.span {(4 : O)}) (∏ i ∈ S,p i))
        (Ideal.Quotient.mk (Ideal.span {(4 : O)}) (∏ i ∈ T,p i)) *
        star (secondPreColumn p hg Ψ₁ m c d e k H₁ S) *
        secondPreColumn p hg Ψ₂ m c d e (-k) H₂ T := by
      unfold initialPairPhase
      ring
    _ = _ := by
      rw [he]
      simp only [Fintype.sum_prod_type,Finset.sum_mul,Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro χ hχ
      apply Finset.sum_congr rfl
      intro η hη
      simp only [secondRayCoefficient,secondPreColumn,secondRayMinus_apply,
        secondRayPlus_apply,star_mul,star_star]
      ring

end InverseInitialRayAttachment

namespace InverseInitialRayAttachment
open Eisenstein SchwartzPlanePoisson FirstPassCubeLabels SecondPassArithmetic
open InverseInitialArithmetic InverseInitialProfile
open scoped BigOperators Classical SchwartzMap
variable {ι : Type*} [DecidableEq ι]
  (p : ι → O) (hp : ∀ i,p i ≠ 0) [∀ i,(Ideal.span {p i}).IsMaximal]
  (hg : ∀ i,lambda ∉ Ideal.span {p i})

def initialTest (σ : Finset ι → ℂ) (V : ℝ → ℂ) (Z D : ℝ) (A : Finset ι) : ℂ :=
  σ A*V (primeProductNorm p A/Z^D)

def initialBeta (Ψ : O →* ℂ) (j : O) (G : Finset ι) : ℂ :=
  (‖Ψ (∏ i ∈ G,p i)*primeCoprimeMask p G j‖^2 : ℝ)

theorem initial_overlap_weight (Ψ : O →* ℂ) (j : O)
    (σ : Finset ι → ℂ) (V : ℝ → ℂ) (Z D : ℝ) (G U T : Finset ι) :
    overlapPairWeight p (fun i => complexSexticChar (Ideal.span {p i}) (hg i)) Ψ j 1 1 (initialTest p σ V Z D) G U T =
      initialBeta p Ψ j G *
        star (supportMobius U *
          secondInputCoefficient p (fun i => complexSexticChar (Ideal.span {p i}) (hg i)) Ψ j 1 1 (fun A => σ (G∪A)) U) *
        (supportMobius T *
          secondInputCoefficient p (fun i => complexSexticChar (Ideal.span {p i}) (hg i)) Ψ j 1 1 (fun A => σ (G∪A)) T) *
        star (V (primeProductNorm p (G∪U)/Z^D))*V (primeProductNorm p (G∪T)/Z^D) := by
  have hrow (A : Finset ι) :
      primeSubsetRow p (fun i => complexSexticChar (Ideal.span {p i}) (hg i)) A 1 = 1 :=
    by simp only [primeSubsetRow,map_one,Finset.prod_const_one]
  simp only [overlapPairWeight,secondInputCoefficient,initialBeta,initialTest,
    hrow,one_pow,mul_one,star_mul]
  ring

theorem initial_pair_rays
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (hc : ∀ i,ringChar (O ⧸ Ideal.span {p i})≠2)
    (hpr : ∀ i,lambda^2∣p i-1)
    (Ψ : O →* ℂ) (j e h : O) (σ : Finset ι → ℂ)
    (G U T : Finset ι) (hGU : Disjoint G U) (hGT : Disjoint G T) (hUT : Disjoint U T) :
    star (supportMobius U *
      secondInputCoefficient p (fun i => complexSexticChar (Ideal.span {p i}) (hg i)) Ψ j 1 1 (fun A => σ (G∪A)) U) *
      (supportMobius T *
        secondInputCoefficient p (fun i => complexSexticChar (Ideal.span {p i}) (hg i)) Ψ j 1 1 (fun A => σ (G∪A)) T) *
      secondNormalizedGaussTerm p hp hg U T e h =
    ∑ ρ : SecondRayIndex,secondRayCoefficient ρ *
      star (initialColumn p hg (secondRayMinus Ψ ρ) j (∏ i ∈ G,p i) e h
        (fun A => σ (G∪A)) U) *
      initialColumn p hg (secondRayPlus Ψ ρ) j (∏ i ∈ G,p i) e (-h)
        (fun A => σ (G∪A)) T := by
  have hm (A : Finset ι) (hAG : Disjoint A G) :
      secondInputCoefficient p (fun i => complexSexticChar (Ideal.span {p i}) (hg i)) Ψ (j*∏ i ∈ G,p i) 1 1 (fun A => σ (G∪A)) A =
        secondInputCoefficient p (fun i => complexSexticChar (Ideal.span {p i}) (hg i)) Ψ j 1 1 (fun A => σ (G∪A)) A := by
    erw [secondInputCoefficient_fixed_mask,commonProduct_mask p hinj]
    simp only [hAG,ite_true,one_mul]
  have he := initial_gauss_ray_expansion p hp hg hinj hc hpr Ψ Ψ
    (j*∏ i ∈ G,p i) 1 1 e h (fun A => σ (G∪A)) (fun A => σ (G∪A)) U T hUT
  rw [hm U hGU.symm,hm T hGT.symm] at he
  simpa only [Fintype.sum_prod_type,secondRayCoefficient,secondRayMinus,secondRayPlus,
    initialColumn_eq_secondPre] using he


end InverseInitialRayAttachment

namespace InverseInitialKernelBridge
open Eisenstein SchwartzPlanePoisson InverseInitialProfile
open scoped BigOperators Classical SchwartzMap
local notation "N" => fun I : Ideal O => (Ideal.absNorm I : ℝ)

private theorem physicalKernel_vector (W₁ W₂ : ℝ → ℂ) (Φ : 𝓢(ℝ,ℂ))
    (Z D m q₀ q₁ q₂ q₃ q₄ q₅ : ℝ) :
    physicalKernel W₁ W₂ Φ Z D m ![q₀,q₁,q₂,q₃,q₄,q₅] =
      ((Z^(-D)*Z^m/(q₁*q₂*Real.sqrt (q₄*q₅)) : ℝ) : ℂ)*
        W₁ (q₀*q₂*q₄/Z^D)*W₂ (q₀*q₂*q₅/Z^D)*
          paperRadialFourier Φ (Z^m*q₃/(q₁*q₂^2*q₄*q₅)) := rfl

def physicalCoordinates (C d s n₁ n₂ : Ideal O) (h : O) : Fin 6 → ℝ :=
  ![N C,N d,N s,‖ringComplex h‖^2,N n₁,N n₂]

theorem physicalCoordinates_pos (C d s n₁ n₂ : Ideal O) (h : O)
    (hC : C ≠ 0) (hd : d ≠ 0) (hs : s ≠ 0) (h₁ : n₁ ≠ 0) (h₂ : n₂ ≠ 0) (hh : h ≠ 0) :
    ∀ i, 0 < physicalCoordinates C d s n₁ n₂ h i := by
  have hp (I : Ideal O) (hI : I ≠ 0) : 0 < N I := by
    change 0 < (Ideal.absNorm I : ℝ)
    exact_mod_cast Nat.pos_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr hI)
  intro i
  fin_cases i
  · exact hp C hC
  · exact hp d hd
  · exact hp s hs
  · exact sq_pos_of_pos (norm_pos_iff.mpr (ringComplex_ne_zero hh))
  · exact hp n₁ h₁
  · exact hp n₂ h₂

theorem physicalKernel_common_factor (C d s n₁ n₂ : Ideal O) (h : O)
    (W₁ W₂ : ℝ → ℂ) (Φ : 𝓢(ℝ,ℂ)) (Z D m : ℝ) :
    physicalKernel W₁ W₂ Φ Z D m (physicalCoordinates C d 1 (s*n₁) (s*n₂) h) =
      physicalKernel W₁ W₂ Φ Z D m (physicalCoordinates C d s n₁ n₂ h) := by
  have hroot : Real.sqrt ((N s*N n₁)*(N s*N n₂)) = N s*Real.sqrt (N n₁*N n₂) := by
    rw [show (N s*N n₁)*(N s*N n₂) = (N s)^2*(N n₁*N n₂) from by ring_nf,
      Real.sqrt_mul (sq_nonneg _),Real.sqrt_sq_eq_abs,abs_of_nonneg (Nat.cast_nonneg _)]
  unfold physicalCoordinates
  rw [physicalKernel_vector,physicalKernel_vector]
  simp only [map_one,Nat.cast_one,map_mul,Nat.cast_mul,mul_one,one_pow]
  rw [hroot]
  have hl : N C*(N s*N n₁)/Z^D = N C*N s*N n₁/Z^D := by ring_nf
  have hr : N C*(N s*N n₂)/Z^D = N C*N s*N n₂/Z^D := by ring_nf
  have hk : Z^m*‖ringComplex h‖^2/(N d*(N s*N n₁)*(N s*N n₂)) =
      Z^m*‖ringComplex h‖^2/(N d*(N s)^2*N n₁*N n₂) := by ring_nf
  rw [hl,hr,hk]
  push_cast
  ring_nf


end InverseInitialKernelBridge

end GaloisForLFunctions.MetaplecticMobiusDescent.CubicEisenstein
