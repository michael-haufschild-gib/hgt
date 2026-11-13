/-
The first global retained source adapted from OpenAI's formalization, Apache-2.0.
See LICENSE and NOTICE in the parent directory for source attribution.
-/
import GaloisForLFunctions.MetaplecticMobiusDescent.Descent.FirstBlocksAndFamilyEnergy

/-!
# The first global retained source

The first global retained source and original outer data; reopened rows of the first family
and the canonical second energy; whole-priority second energies of retained families.
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

namespace InverseMoment
open scoped BigOperators Classical SchwartzMap
open JointLogSeparation MeasureTheory
noncomputable section
open Eisenstein SchwartzPlanePoisson SecondPassArithmetic
open InverseFirstRayAttachment

theorem first_fresh_physical_profile
    (W₁ W₂ ω₁ ω₂ : ℝ → ℂ) (Φ : 𝓢(ℝ,ℂ)) (V : Fin 9 → ℝ → ℂ)
    (s q : Fin 9 → ℝ) (hspos : ∀ i, 0 < s i) (hq : ∀ i, 0 < q i) (K : ℝ)
    (density : Frequency × (Fin 9 → ℝ) → ℂ) (normalization : ℂ)
    (he : ∀ y : Fin 9 → ℝ, normalization * firstPoissonProfile W₁ W₂ Φ V
        (K*s 6/(s 3*s 4*(s 5)^2*s 7*s 8)) y =
      ∫ z : Frequency × (Fin 9 → ℝ),density z *
        pureProfileMode firstLeftSlope firstRightSlope firstKernelSlope y z.1 z.2)
    (hω₁ : W₁ (q 0*q 2*q 5*q 7/(s 0*s 2*s 5*s 7)) ≠ 0 → ω₁ (q 7/s 7) = 1)
    (hω₂ : W₂ (q 1*q 2*q 5*q 8/(s 1*s 2*s 5*s 8)) ≠ 0 → ω₂ (q 8/s 8) = 1)
    (hcut : ω₁ (q 7/s 7) ≠ 0 → ω₂ (q 8/s 8) ≠ 0 → ∀ i, V i (firstRelativeLog q s i) = 1) :
    normalization * firstNormProfile (fun x => W₁ (x/(s 0*s 2*s 5*s 7)))
      (fun x => W₂ (x/(s 1*s 2*s 5*s 8))) Φ (fun _ _ => 1) K q =
    (firstRootScale s:ℂ)⁻¹*(ω₁ (q 7/s 7)*ω₂ (q 8/s 8))*
      ∫ z : Frequency × (Fin 9 → ℝ),density z *
        pureProfileMode firstLeftSlope firstRightSlope firstKernelSlope (firstRelativeLog q s) z.1 z.2 := by
  by_cases hw₁ : ω₁ (q 7/s 7) = 0
  · have hh : W₁ (q 0*q 2*q 5*q 7/(s 0*s 2*s 5*s 7)) = 0 := by
      by_contra hn
      have := hω₁ hn
      simp only [hw₁,zero_ne_one] at this
    simp only [firstNormProfile,hh,hw₁,mul_zero,zero_mul,zero_div]
  by_cases hw₂ : ω₂ (q 8/s 8) = 0
  · have hh : W₂ (q 1*q 2*q 5*q 8/(s 1*s 2*s 5*s 8)) = 0 := by
      by_contra hn
      have := hω₂ hn
      simp only [hw₂,zero_ne_one] at this
    simp only [firstNormProfile,hh,hw₂,mul_zero,zero_mul,zero_div]
  have hcut' := hcut hw₁ hw₂
  have hnom := firstNormProfile_nominal W₁ W₂ Φ (fun _ _ => 1) s q hspos hq K
  have hfull : normalization * firstNormProfile W₁ W₂ Φ (fun _ _ => 1)
      (K*s 6/(s 3*s 4*(s 5)^2*s 7*s 8)) (fun i => q i/s i) =
      ∫ z : Frequency × (Fin 9 → ℝ), density z *
        pureProfileMode firstLeftSlope firstRightSlope firstKernelSlope (firstRelativeLog q s) z.1 z.2 := by
    have hp := firstPoissonProfile_log W₁ W₂ Φ V
      (K*s 6/(s 3*s 4*(s 5)^2*s 7*s 8)) (fun i => q i/s i)
      (fun i => div_pos (hq i) (hspos i))
    have hc : firstPoissonProfile W₁ W₂ Φ V
        (K*s 6/(s 3*s 4*(s 5)^2*s 7*s 8)) (firstRelativeLog q s) =
        firstNormProfile W₁ W₂ Φ (fun _ _ => 1)
          (K*s 6/(s 3*s 4*(s 5)^2*s 7*s 8)) (fun i => q i/s i) := by
      unfold firstRelativeLog
      rw [hp]
      simp only [firstRelativeLog] at hcut'
      simp only [firstNormProfile,hcut',Finset.prod_const_one]
    rw [← hc]
    exact he (firstRelativeLog q s)
  have hm : firstNormProfile (fun x => W₁ (x/(s 0*s 2*s 5*s 7)))
      (fun x => W₂ (x/(s 1*s 2*s 5*s 8))) Φ (fun _ _ => 1) K q =
      (ω₁ (q 7/s 7)*ω₂ (q 8/s 8)) *
      firstNormProfile (fun x => W₁ (x/(s 0*s 2*s 5*s 7)))
        (fun x => W₂ (x/(s 1*s 2*s 5*s 8))) Φ (fun _ _ => 1) K q := by
    by_cases h1 : W₁ (q 0*q 2*q 5*q 7/(s 0*s 2*s 5*s 7)) = 0
    · simp only [firstNormProfile,h1,mul_zero,zero_mul,zero_div]
    by_cases h2 : W₂ (q 1*q 2*q 5*q 8/(s 1*s 2*s 5*s 8)) = 0
    · simp only [firstNormProfile,h2,mul_zero,zero_mul,zero_div]
    simp only [hω₁ h1,hω₂ h2,one_mul]
  calc
    _ = (firstRootScale s:ℂ)⁻¹*(ω₁ (q 7/s 7)*ω₂ (q 8/s 8))*
        (normalization * firstNormProfile W₁ W₂ Φ (fun _ _ => 1)
          (K*s 6/(s 3*s 4*(s 5)^2*s 7*s 8)) (fun i => q i/s i)) := by
      conv_lhs => rw [hm,hnom]
      ring
    _ = _ := by rw [hfull]

theorem first_balanced_density_integrable (g : Fin 9 → 𝓢(ℝ,ℂ)) (g₁ g₂ b₃ : 𝓢(ℝ,ℂ))
    (ρ : Fin 9 → ℝ) (c₁ c₂ θ₁ θ₂ L : ℝ) :
    Integrable (InverseMomentFirstProfileUniform.density g g₁ g₂ b₃ ρ c₁ c₂ θ₁ θ₂ L) := by
  exact (full_density_integrable _ _ _ _).const_mul _

open InverseInitialRayAttachment Eisenstein SchwartzPlanePoisson FirstPassCubeLabels
open InverseFirstRayAttachment
local notation "Eis" => Eisenstein.O
variable {ι : Type*} [DecidableEq ι]
  (p : ι → Eis) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hg : ∀ i, lambda ∉ Ideal.span {p i})

include hp in
omit [DecidableEq ι] [∀ (i : ι), (Ideal.span {p i}).IsMaximal] in
theorem firstCommonNorms_pos (A₁ A₂ C R : ℝ) (hA₁ : 0 < A₁) (hA₂ : 0 < A₂)
    (hC : 0 < C) (hR : 0 < R) (d h : Eis) (hd : d ≠ 0) (hh : h ≠ 0)
    (j : FirstCommonIndex ι) : ∀ i,0 < firstCommonNorms p A₁ A₂ C R d h j i := by
  intro i
  fin_cases i <;> simp only [firstCommonNorms]
  · exact hA₁
  · exact hA₂
  · exact hC
  · exact sq_pos_of_pos (norm_pos_iff.mpr (ringComplex_ne_zero hd))
  · exact hR
  · exact primeProductNorm_pos p hp _
  · exact sq_pos_of_pos (norm_pos_iff.mpr (ringComplex_ne_zero hh))
  · exact primeProductNorm_pos p hp _
  · exact primeProductNorm_pos p hp _

include hp in

theorem actual_first_balanced_block (F : Finset ι) (selector : Finset ι → ℂ)
    (C₁ C₂ : Finset ι → ℂ) (W₁ W₂ ω₁ ω₂ : ℝ → ℂ) (Φ : 𝓢(ℝ,ℂ))
    (V : Fin 9 → ℝ → ℂ) (A₁ A₂ C R K L : ℝ)
    (hA₁ : 0 < A₁) (hA₂ : 0 < A₂) (hC : 0 < C) (hR : 0 < R)
    (d h : Eis) (hd : d ≠ 0) (hh : h ≠ 0) (s : Fin 9 → ℝ) (hs : ∀ i,0 < s i)
    (density : Frequency × (Fin 9 → ℝ) → ℂ) (hDensity : Integrable density)
    (hsep : ∀ y : Fin 9 → ℝ,
      (Real.exp (-(9/2:ℝ)*L):ℂ)*firstPoissonProfile W₁ W₂ Φ V
        (K*s 6/(s 3*s 4*(s 5)^2*s 7*s 8)) y =
      ∫ z : Frequency × (Fin 9 → ℝ),density z *
        pureProfileMode firstLeftSlope firstRightSlope firstKernelSlope y z.1 z.2)
    (hω₁ : ∀ j ∈ firstCommonIndices F,
      selector j.2.1*firstCommonWeight p hg C₁ C₂ h j ≠ 0 →
      W₁ (A₁*C*primeProductNorm p j.2.1*primeProductNorm p j.2.2.1/(s 0*s 2*s 5*s 7)) ≠ 0 →
      ω₁ (primeProductNorm p j.2.2.1/s 7) = 1)
    (hω₂ : ∀ j ∈ firstCommonIndices F,
      selector j.2.1*firstCommonWeight p hg C₁ C₂ h j ≠ 0 →
      W₂ (A₂*C*primeProductNorm p j.2.1*primeProductNorm p j.2.2.2/(s 1*s 2*s 5*s 8)) ≠ 0 →
      ω₂ (primeProductNorm p j.2.2.2/s 8) = 1)
    (hcut : ∀ j ∈ firstCommonIndices F,
      selector j.2.1*firstCommonWeight p hg C₁ C₂ h j ≠ 0 →
      ω₁ (primeProductNorm p j.2.2.1/s 7) ≠ 0 → ω₂ (primeProductNorm p j.2.2.2/s 8) ≠ 0 →
      ∀ i,V i (firstRelativeLog (firstCommonNorms p A₁ A₂ C R d h j) s i) = 1) :
    (Real.exp (-(9/2:ℝ)*L):ℂ)*firstBlockedPhysicalRows p hg F selector C₁ C₂
      (fun x => W₁ (x/(s 0*s 2*s 5*s 7))) (fun x => W₂ (x/(s 1*s 2*s 5*s 8)))
      Φ A₁ A₂ C R K d h =
    (firstRootScale s:ℂ)⁻¹*∫ z : Frequency × (Fin 9 → ℝ),density z*
      firstBlockedSeparatedRow p hg F selector C₁ C₂ ω₁ ω₂ A₁ A₂ C R d h s z := by
  apply first_block_normalized_density p hg F selector C₁ C₂ _ _ ω₁ ω₂ Φ A₁ A₂ C R K d h s density hDensity
  intro j hj hn
  exact first_fresh_physical_profile W₁ W₂ ω₁ ω₂ Φ V s
    (firstCommonNorms p A₁ A₂ C R d h j) hs
    (firstCommonNorms_pos p hp A₁ A₂ C R hA₁ hA₂ hC hR d h hd hh j) K density
    (Real.exp (-(9/2:ℝ)*L):ℂ) hsep
    (by simpa [firstCommonNorms] using hω₁ j hj hn)
    (by simpa [firstCommonNorms] using hω₂ j hj hn)
    (by simpa [firstCommonNorms] using hcut j hj hn)

end
end InverseMoment

namespace InverseMoment
open scoped BigOperators Classical SchwartzMap
open InverseInitialRayAttachment Eisenstein SchwartzPlanePoisson FirstPassCubeLabels RayFourExpansion
open JointLogSeparation MeasureTheory
noncomputable section
open Eisenstein SchwartzPlanePoisson SecondPassArithmetic
open InverseFirstRayAttachment
open InverseFirstRayAttachment
local notation "Eis" => Eisenstein.O
variable {ι κ : Type*} [DecidableEq ι]
  (p : ι → Eis) [∀ i,(Ideal.span {p i}).IsMaximal]
  (hg : ∀ i,lambda ∉ Ideal.span {p i})

theorem integrable_first_block_density (F : Finset ι) (selector C₁ C₂ : Finset ι → ℂ)
    (omega₁ omega₂ : ℝ → ℂ) (A₁ A₂ C R : ℝ) (d h : Eis) (s : Fin 9 → ℝ)
    (density : Frequency × (Fin 9 → ℝ) → ℂ) (hDensity : Integrable density) :
    Integrable (fun z : Frequency × (Fin 9 → ℝ) => density z*
      firstBlockedSeparatedRow p hg F selector C₁ C₂ omega₁ omega₂ A₁ A₂ C R d h s z) := by
  let coef (j : FirstCommonIndex ι) :=
    (selector j.2.1*firstCommonWeight p hg C₁ C₂ h j)*
      (omega₁ (primeProductNorm p j.2.2.1/s 7)*omega₂ (primeProductNorm p j.2.2.2/s 8))
  have he : (fun z : Frequency × (Fin 9 → ℝ) => density z*
      firstBlockedSeparatedRow p hg F selector C₁ C₂ omega₁ omega₂ A₁ A₂ C R d h s z) =
      fun z => ∑ j∈firstCommonIndices F,coef j*(density z*
        pureProfileMode firstLeftSlope firstRightSlope firstKernelSlope
          (firstRelativeLog (firstCommonNorms p A₁ A₂ C R d h j) s) z.1 z.2) := by
    funext z
    rw [←first_block_modes_eq_columns]
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    dsimp only [coef]
    ring
  rw [he]
  exact integrable_finsetSum _ (fun j hj => (integrable_density_mode density hDensity
    firstLeftSlope firstRightSlope firstKernelSlope
    (firstRelativeLog (firstCommonNorms p A₁ A₂ C R d h j) s)).const_mul (coef j))

theorem first_family_density_sum (source : Finset κ) (F : Finset ι)
    (selector C₁ C₂ : κ → Finset ι → ℂ) (w : κ → ℂ)
    (omega₁ omega₂ : ℝ → ℂ) (A₁ A₂ C R : κ → ℝ) (d h : κ → Eis) (s : Fin 9 → ℝ)
    (density : Frequency × (Fin 9 → ℝ) → ℂ) (hDensity : Integrable density) :
    (∑ x∈source,w x*∫ z : Frequency × (Fin 9 → ℝ),density z*
      firstBlockedSeparatedRow p hg F (selector x) (C₁ x) (C₂ x) omega₁ omega₂
        (A₁ x) (A₂ x) (C x) (R x) (d x) (h x) s z) =
    ∫ z : Frequency × (Fin 9 → ℝ),density z*
      firstFamilySeparatedRow p hg source F selector C₁ C₂ w omega₁ omega₂ A₁ A₂ C R d h s z := by
  simp only [←integral_const_mul]
  rw [←integral_finsetSum source (fun x hx =>
    (integrable_first_block_density p hg F (selector x) (C₁ x) (C₂ x) omega₁ omega₂
      (A₁ x) (A₂ x) (C x) (R x) (d x) (h x) s density hDensity).const_mul (w x))]
  apply integral_congr_ae
  filter_upwards with z
  simp only [firstFamilySeparatedRow,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x hx
  ring

def firstFamilyPhysicalRows (source : Finset κ) (F : Finset ι)
    (selector C₁ C₂ : κ → Finset ι → ℂ) (w : κ → ℂ)
    (W₁ W₂ : ℝ → ℂ) (Φ : 𝓢(ℝ,ℂ)) (A₁ A₂ C R : κ → ℝ) (K : ℝ)
    (d h : κ → Eis) (s : Fin 9 → ℝ) : ℂ :=
  ∑ x∈source,w x*firstBlockedPhysicalRows p hg F (selector x) (C₁ x) (C₂ x)
    (fun y => W₁ (y/(s 0*s 2*s 5*s 7))) (fun y => W₂ (y/(s 1*s 2*s 5*s 8)))
    Φ (A₁ x) (A₂ x) (C x) (R x) K (d x) (h x)

theorem actual_first_balanced_family (hp : ∀ i,p i ≠ 0)
    (source : Finset κ) (F : Finset ι) (selector C₁ C₂ : κ → Finset ι → ℂ) (w : κ → ℂ)
    (W₁ W₂ omega₁ omega₂ : ℝ → ℂ) (Φ : 𝓢(ℝ,ℂ)) (V : Fin 9 → ℝ → ℂ)
    (A₁ A₂ C R : κ → ℝ) (K L : ℝ) (d h : κ → Eis) (s : Fin 9 → ℝ)
    (hpos : ∀ x∈source,0 < A₁ x ∧ 0 < A₂ x ∧ 0 < C x ∧ 0 < R x ∧ d x ≠ 0 ∧ h x ≠ 0)
    (hs : ∀ i,0 < s i) (density : Frequency × (Fin 9 → ℝ) → ℂ) (hDensity : Integrable density)
    (hsep : ∀ y : Fin 9 → ℝ,
      (Real.exp (-(9/2:ℝ)*L):ℂ)*firstPoissonProfile W₁ W₂ Φ V
        (K*s 6/(s 3*s 4*(s 5)^2*s 7*s 8)) y =
      ∫ z : Frequency × (Fin 9 → ℝ),density z*
        pureProfileMode firstLeftSlope firstRightSlope firstKernelSlope y z.1 z.2)
    (homega₁ : ∀ x∈source,∀ j∈firstCommonIndices F,
      selector x j.2.1*firstCommonWeight p hg (C₁ x) (C₂ x) (h x) j ≠ 0 →
      W₁ (A₁ x*C x*primeProductNorm p j.2.1*primeProductNorm p j.2.2.1/(s 0*s 2*s 5*s 7)) ≠ 0 →
      omega₁ (primeProductNorm p j.2.2.1/s 7) = 1)
    (homega₂ : ∀ x∈source,∀ j∈firstCommonIndices F,
      selector x j.2.1*firstCommonWeight p hg (C₁ x) (C₂ x) (h x) j ≠ 0 →
      W₂ (A₂ x*C x*primeProductNorm p j.2.1*primeProductNorm p j.2.2.2/(s 1*s 2*s 5*s 8)) ≠ 0 →
      omega₂ (primeProductNorm p j.2.2.2/s 8) = 1)
    (hcut : ∀ x∈source,∀ j∈firstCommonIndices F,
      selector x j.2.1*firstCommonWeight p hg (C₁ x) (C₂ x) (h x) j ≠ 0 →
      omega₁ (primeProductNorm p j.2.2.1/s 7) ≠ 0 → omega₂ (primeProductNorm p j.2.2.2/s 8) ≠ 0 →
      ∀ i,V i (firstRelativeLog (firstCommonNorms p (A₁ x) (A₂ x) (C x) (R x) (d x) (h x) j) s i) = 1) :
    (Real.exp (-(9/2:ℝ)*L):ℂ)*firstFamilyPhysicalRows p hg source F selector C₁ C₂ w
      W₁ W₂ Φ A₁ A₂ C R K d h s =
    (firstRootScale s:ℂ)⁻¹*∫ z : Frequency × (Fin 9 → ℝ),density z*
      firstFamilySeparatedRow p hg source F selector C₁ C₂ w omega₁ omega₂ A₁ A₂ C R d h s z := by
  have hb (x : κ) (hx : x∈source) := actual_first_balanced_block p hp hg F (selector x) (C₁ x) (C₂ x)
    W₁ W₂ omega₁ omega₂ Φ V (A₁ x) (A₂ x) (C x) (R x) K L
    (hpos x hx).1 (hpos x hx).2.1 (hpos x hx).2.2.1 (hpos x hx).2.2.2.1
    (d x) (h x) (hpos x hx).2.2.2.2.1 (hpos x hx).2.2.2.2.2 s hs density hDensity hsep
    (homega₁ x hx) (homega₂ x hx) (hcut x hx)
  rw [←first_family_density_sum p hg source F selector C₁ C₂ w omega₁ omega₂ A₁ A₂ C R d h s density hDensity]
  simp only [firstFamilyPhysicalRows,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x hx
  calc
    _ = w x*((Real.exp (-(9/2:ℝ)*L):ℂ)*firstBlockedPhysicalRows p hg F (selector x) (C₁ x) (C₂ x)
      (fun y => W₁ (y/(s 0*s 2*s 5*s 7))) (fun y => W₂ (y/(s 1*s 2*s 5*s 8)))
      Φ (A₁ x) (A₂ x) (C x) (R x) K (d x) (h x)) := by ring
    _ = _ := by rw [hb x hx]; ring

end
end InverseMoment

namespace InverseMoment
open scoped BigOperators Classical SchwartzMap
open InverseInitialRayAttachment Eisenstein SchwartzPlanePoisson FirstPassCubeLabels SecondPassArithmetic
open Eisenstein (ringComplex)
noncomputable section
open Eisenstein SchwartzPlanePoisson SecondPassArithmetic
open InverseFirstRayAttachment
open InverseFirstRayAttachment
local notation "O" => Eisenstein.O
variable {ι : Type*} [DecidableEq ι]
  (p : ι→O) (hp : ∀ i,p i≠0) [∀ i,(Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
  (hg : ∀ i,lambda∉Ideal.span {p i})

def firstCanonicalCoefficient (b : CubeCoordinates ι) (C : Finset ι)
    (negative : Bool) (Ψ : O→*ℂ) (m d : O) (H : Finset ι→ℂ) (x : Ideal O×O) : Finset ι→ℂ :=
  firstBareCubeCoefficient p hg b.support (fun i=>b.leftExponent i+b.rightExponent i)
    b.leftBit b.rightBit negative
    (canonicalCubeResidual p hg b C negative Ψ m (cubicIdealGenerator x.1) H) d

theorem firstCanonicalCoefficient_old (b : CubeCoordinates ι) (C : Finset ι)
    (negative : Bool) (Ψ : O→*ℂ) (m d : O) (H : Finset ι→ℂ) (x : Ideal O×O) :
    firstCanonicalCoefficient p hg b C negative Ψ m d H x =
      firstOldLabelCoefficient p hp hcop hg b.support (fun i=>b.leftExponent i+b.rightExponent i)
        b.leftBit b.rightBit negative
        (multiplicativeCoreColumn p Ψ m
          (fun U=>H (((if negative then b.rightDivisor else b.leftDivisor)∪C)∪U)))
        (∏i∈C,p i) d x.1 := rfl

lemma first_unblocked_physical (F : Finset ι) (C₁ C₂ : Finset ι→ℂ)
    (W₁ W₂ : ℝ→ℂ) (Φ : 𝓢(ℝ,ℂ)) (A₁ A₂ C R K : ℝ) (d h : O) :
    firstBlockedPhysicalRows p hg F (fun _=>1) C₁ C₂ W₁ W₂ Φ A₁ A₂ C R K d h =
      firstPhysicalCommonRows p hg F C₁ C₂ W₁ W₂ Φ A₁ A₂ C R K d h := by
  rw [firstPhysicalCommonRows_indexed]
  simp only [firstBlockedPhysicalRows,one_mul]

theorem retained_first_physical_family (pool : Finset ι) (b : CubeCoordinates ι) (C : Finset ι)
    (Ψ₁ Ψ₂ : O→*ℂ) (m₁ m₂ d : O) (H₁ H₂ : Finset ι→ℂ)
    (W₁ W₂ : ℝ→ℂ) (Φ : 𝓢(ℝ,ℂ)) (K : ℝ)
    (source : Finset (Ideal O×O)) (a : Ideal O×O→ℂ)
    (s : Fin 9→ℝ) (hs : ∀ i,0<s i) :
    (∑ x∈source,a x*canonicalCubeOuter p hg b C Ψ₁ Ψ₂ m₁ m₂ (cubicIdealGenerator x.1)*
      firstCubePhysicalMode p hp hg pool b C Ψ₁ Ψ₂ m₁ m₂ (cubicIdealGenerator x.1)
        H₁ H₂ W₁ W₂ Φ K d x.2) =
    (K:ℂ)*firstFamilyPhysicalRows p hg source (pool\(b.support∪C)) (fun _ _=>1)
      (firstCanonicalCoefficient p hg b C true Ψ₁ m₁ d H₁)
      (firstCanonicalCoefficient p hg b C false Ψ₂ m₂ d H₂)
      (retainedCubeWeight p hp hg b C Ψ₁ Ψ₂ m₁ m₂ d a)
      (fun x=>star (W₁ ((s 0*s 2*s 5*s 7)*x)))
      (fun x=>W₂ ((s 1*s 2*s 5*s 8)*x)) Φ
      (fun _=>‖ringComplex (aLabel p b.support b.rightBit)‖^2)
      (fun _=>‖ringComplex (aLabel p b.support b.leftBit)‖^2)
      (fun _=>primeProductNorm p C)
      (fun _=>primeProductNorm p (cubeActiveSupport b.support (fun i=>b.leftExponent i+b.rightExponent i) b.leftBit b.rightBit))
      K (fun _=>d) Prod.snd s := by
  have hscale₁ : s 0*s 2*s 5*s 7≠0 := mul_ne_zero (mul_ne_zero (mul_ne_zero (hs 0).ne' (hs 2).ne') (hs 5).ne') (hs 7).ne'
  have hscale₂ : s 1*s 2*s 5*s 8≠0 := mul_ne_zero (mul_ne_zero (mul_ne_zero (hs 1).ne' (hs 2).ne') (hs 5).ne') (hs 8).ne'
  have hw₁ : (fun y=>star (W₁ ((s 0*s 2*s 5*s 7)*(y/(s 0*s 2*s 5*s 7))))) =
      fun y=>star (W₁ y) := by
    funext y
    rw [mul_div_cancel₀ _ hscale₁]
  have hw₂ : (fun y=>W₂ ((s 1*s 2*s 5*s 8)*(y/(s 1*s 2*s 5*s 8)))) = W₂ := by
    funext y
    rw [mul_div_cancel₀ _ hscale₂]
  simp only [firstFamilyPhysicalRows,Finset.mul_sum,hw₁,hw₂]
  apply Finset.sum_congr rfl
  intro x hx
  rw [first_unblocked_physical p hg]
  simp only [firstCubePhysicalMode,retainedCubeWeight,firstCanonicalCoefficient,
    firstBareCubeCoefficient,Bool.false_eq_true,ite_false,ite_true]
  ring

end
end InverseMoment

namespace InverseMoment
open scoped BigOperators Classical SchwartzMap
open InverseInitialRayAttachment Eisenstein SchwartzPlanePoisson FirstPassCubeLabels SecondPassArithmetic
open Eisenstein (ringComplex)
noncomputable section
open Eisenstein SchwartzPlanePoisson SecondPassArithmetic
open InverseFirstRayAttachment
open InverseFirstRayAttachment
local notation "O" => Eisenstein.O

theorem bounded_row_square_expansion {β : Type*}
    (C : Finset β) (a : β→ℂ) (r : β→O→ℂ) (hr : ∀b∈C,∀z,‖r b z‖≤1)
    (W : 𝓢(ℝ,ℂ)) (K : ℝ) (hK : 0<K) :
    (∑'z:O,W (‖ringComplex z‖^2/K)*(‖∑b∈C,a b*r b z‖^2:ℝ))=
      ∑b∈C,∑c∈C,(star (a b)*a c)*∑'z:O,(star (r b z)*r c z)*W (‖ringComplex z‖^2/K) := by
  have hs (b c : β) (hb:b∈C) (hc:c∈C) : Summable (fun z:O =>
      (star (r b z)*r c z)*W (‖ringComplex z‖^2/K)) := by
    have hW : Summable (fun z:O=>‖W (‖ringComplex z‖^2/K)‖) := by
      simpa only [SchwartzPlanePoisson.scaledRadialTest_apply] using
        SchwartzPlanePoisson.actual_eisenstein_summable_norm
          (SchwartzPlanePoisson.scaledRadialTest W K hK)
    apply Summable.of_norm
    apply Summable.of_nonneg_of_le (fun z=>norm_nonneg _) _ hW
    intro z
    simp only [norm_mul,norm_star]
    calc
      _ ≤ 1*1*‖W (‖ringComplex z‖^2/K)‖ := by
        gcongr
        · exact hr b hb z
        · exact hr c hc z
      _ = _ := by ring
  have he (z:O) : W (‖ringComplex z‖^2/K)*(‖∑b∈C,a b*r b z‖^2:ℝ)=
      ∑b∈C,∑c∈C,(star (a b)*a c)*((star (r b z)*r c z)*W (‖ringComplex z‖^2/K)) := by
    rw [Complex.sq_norm (∑b∈C,a b*r b z),Complex.normSq_eq_conj_mul_self]
    simp only [map_sum,map_mul,starRingEnd_apply]
    rw [Finset.sum_mul_sum]
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro b hb
    apply Finset.sum_congr rfl
    intro c hc
    ring
  simp_rw [he]
  rw [Summable.tsum_finsetSum (fun b hb=>summable_sum (fun c hc=>(hs b c hb hc).mul_left _))]
  apply Finset.sum_congr rfl
  intro b hb
  rw [Summable.tsum_finsetSum (fun c hc=>(hs b c hb hc).mul_left _)]
  apply Finset.sum_congr rfl
  intro c hc
  exact tsum_mul_left

variable {ι : Type*} [DecidableEq ι]
  (p : ι→O) (hp : ∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
  (hg : ∀i,lambda∉Ideal.span {p i})

def varyingReopenedRow (pool : Finset ι) (Q : Finset (ι→₀ℕ)) (β : (ι→₀ℕ)→ℂ)
    (Ψ : O→*ℂ) (m f : O) (H : (ι→₀ℕ)→Finset ι→ℂ) (z : O) : ℂ :=
  ∑v∈Q,∑S∈pool.powerset,
    (β v*canonicalSourceCoefficient p hg Ψ m f (H v) S)*
    (multiplicityRow p hg pool v z^3*
      primeSubsetRow p (fun i => complexSexticChar (Ideal.span {p i}) (hg i)) S z)

theorem varyingReopenedRow_const (pool : Finset ι) (Q : Finset (ι→₀ℕ)) (β : (ι→₀ℕ)→ℂ)
    (Ψ : O→*ℂ) (m f : O) (H : Finset ι→ℂ) (z : O) :
    varyingReopenedRow p hg pool Q β Ψ m f (fun _=>H) z =
      reopenedCanonicalRow p hg pool Q β Ψ m f H z := rfl

theorem varying_reopened_smoothed_expand
    (pool : Finset ι) (Q : Finset (ι→₀ℕ)) (hQ : ∀v∈Q,v.support⊆pool)
    (β : (ι→₀ℕ)→ℂ) (Ψ : O→*ℂ) (m f : O) (H : (ι→₀ℕ)→Finset ι→ℂ)
    (W : 𝓢(ℝ,ℂ)) (K : ℝ) (hK : 0<K) :
    (∑'z:O,W (‖ringComplex z‖^2/K)*(‖varyingReopenedRow p hg pool Q β Ψ m f H z‖^2:ℝ))=
      ∑v₂∈Q,∑v₁∈Q,(star (β v₂)*β v₁)*
        canonicalCubeCorrelation p hg pool (v₁.support∪v₂.support) v₁ v₂ Ψ Ψ m m f (H v₂) (H v₁) W K := by
  let a : (ι→₀ℕ)×Finset ι→ℂ := fun b=>β b.1*canonicalSourceCoefficient p hg Ψ m f (H b.1) b.2
  let r : (ι→₀ℕ)×Finset ι→O→ℂ := fun b z=>
    multiplicityRow p hg pool b.1 z^3*
      primeSubsetRow p (fun i => complexSexticChar (Ideal.span {p i}) (hg i)) b.2 z
  have hr (b : (ι→₀ℕ)×Finset ι) (hb:b∈Q×ˢpool.powerset) (z:O) : ‖r b z‖≤1 := by
    dsimp [r]
    rw [norm_mul,norm_pow]
    calc
      _ ≤ 1 * ‖primeSubsetRow p (fun i => complexSexticChar (Ideal.span {p i}) (hg i)) b.2 z‖ :=
        mul_le_mul_of_nonneg_right
          (pow_le_one₀ (norm_nonneg _) (multiplicityRow_norm_le_one p hg pool b.1 z))
          (norm_nonneg _)
      _ ≤ 1 := by simpa using primeSubsetRow_norm_le_one p (fun i => complexSexticChar (Ideal.span {p i}) (hg i)) b.2 z
  have he:=bounded_row_square_expansion (Q×ˢpool.powerset) a r hr W K hK
  simp only [Finset.sum_product] at he
  change (∑'z:O,W (‖ringComplex z‖^2/K)*
    (‖varyingReopenedRow p hg pool Q β Ψ m f H z‖^2:ℝ))=_ at he
  rw [he]
  apply Finset.sum_congr rfl
  intro v₂ hv₂
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro v₁ hv₁
  simp only [canonicalCubeCorrelation,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro S hS
  apply Finset.sum_congr rfl
  intro T hT
  have hB₁ : v₁.support⊆v₁.support∪v₂.support:=Finset.subset_union_left
  have hB₂ : v₂.support⊆v₁.support∪v₂.support:=Finset.subset_union_right
  have hr₁ (z:O) : multiplicityRow p hg pool v₁ z=
      multiplicityRow p hg (v₁.support∪v₂.support) v₁ z := by
    rw [multiplicityRow_support p hg pool v₁ (hQ v₁ hv₁),multiplicityRow_support p hg _ v₁ hB₁]
  have hr₂ (z:O) : multiplicityRow p hg pool v₂ z=
      multiplicityRow p hg (v₁.support∪v₂.support) v₂ z := by
    rw [multiplicityRow_support p hg pool v₂ (hQ v₂ hv₂),multiplicityRow_support p hg _ v₂ hB₂]
  simp only [a,r,canonicalCubeSourcePair,star_mul,hr₁,hr₂]
  have ht : (∑'z:O,(star (primeSubsetRow p (fun i => complexSexticChar (Ideal.span {p i}) (hg i)) S z)*
      star (multiplicityRow p hg (v₁.support∪v₂.support) v₂ z^3)*
      (multiplicityRow p hg (v₁.support∪v₂.support) v₁ z^3*
      primeSubsetRow p (fun i => complexSexticChar (Ideal.span {p i}) (hg i)) T z))*W (‖ringComplex z‖^2/K))=
      ∑'z:O,(star (primeSubsetRow p (fun i => complexSexticChar (Ideal.span {p i}) (hg i)) S z)*
      primeSubsetRow p (fun i => complexSexticChar (Ideal.span {p i}) (hg i)) T z*
      star (multiplicityRow p hg (v₁.support∪v₂.support) v₂ z^3)*
      multiplicityRow p hg (v₁.support∪v₂.support) v₁ z^3)*W (‖ringComplex z‖^2/K) := by
    apply tsum_congr
    intro z
    ring
  rw [ht]
  ring

end
end InverseMoment

namespace InverseMoment
noncomputable section
open Eisenstein SchwartzPlanePoisson SecondPassArithmetic
open InverseFirstRayAttachment
open scoped BigOperators Classical SchwartzMap
open InverseInitialRayAttachment Eisenstein SchwartzPlanePoisson FirstPassCubeLabels SecondPassArithmetic
open InverseFirstRayAttachment
local notation "O" => Eisenstein.O
variable {ι : Type*} [DecidableEq ι]
  (p : ι→O) (hp : ∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
  (hg : ∀i,lambda∉Ideal.span {p i})

omit [DecidableEq ι] in
lemma first_squarefree_row_zero_mem (U : Finset ι) (i : ι) (hi : i∈U) (n : O)
    (hn : n∈Ideal.span {p i}) : primeSubsetRow p (fun i => complexSexticChar (Ideal.span {p i}) (hg i)) U n=0 := by
  unfold primeSubsetRow
  apply Finset.prod_eq_zero hi
  rw [Ideal.Quotient.eq_zero_iff_mem.mpr hn,MulChar.map_zero]

lemma canonicalCubeResidual_zero_overlap (b : CubeCoordinates ι) (C U : Finset ι)
    (negative : Bool) (Ψ : O→*ℂ) (m f : O) (H : Finset ι→ℂ)
    (hn : ¬Disjoint U (b.support∪C)) : canonicalCubeResidual p hg b C negative Ψ m f H U=0 := by
  obtain ⟨i,hi,hib⟩ := Finset.not_disjoint_iff.mp hn
  rcases Finset.mem_union.mp hib with hib|hiC
  · have hm : cubeRadical p b.support∈Ideal.span {p i} :=
      Ideal.mem_span_singleton.mpr (Finset.dvd_prod_of_mem p hib)
    have hz : primeCoprimeMask p U (cubeRadical p b.support)=0 := by
      rw [primeCoprimeMask_indicator]
      exact if_neg (fun hh => hh i hi (Ideal.mem_span_singleton.mp hm))
    simp only [canonicalCubeResidual,originalLabelColumn,hz,mul_zero,zero_mul]
  · have hm : aLabel p b.support (if negative then b.rightBit else b.leftBit)*(∏j∈C,p j)∈Ideal.span {p i} :=
      Ideal.mem_span_singleton.mpr (dvd_mul_of_dvd_right (Finset.dvd_prod_of_mem p hiC) _)
    have hz := first_squarefree_row_zero_mem p hg U i hi _ hm
    simp only [canonicalCubeResidual,originalLabelColumn,hz,zero_pow (by norm_num : 4≠0),mul_zero,zero_mul]

lemma firstCanonicalCoefficient_zero_overlap (b : CubeCoordinates ι) (C U : Finset ι)
    (negative : Bool) (Ψ : O→*ℂ) (m d : O) (H : Finset ι→ℂ) (x : Ideal O×O)
    (hn : ¬Disjoint U (b.support∪C)) : firstCanonicalCoefficient p hg b C negative Ψ m d H x U=0 := by
  have hz := canonicalCubeResidual_zero_overlap p hg b C U negative Ψ m
    (cubicIdealGenerator x.1) H hn
  cases negative <;>
    simp only [firstCanonicalCoefficient,firstBareCubeCoefficient,Bool.false_eq_true,ite_false,ite_true,
      cubeMinusCoefficient,cubePlusCoefficient,firstPassColumnMinus,firstPassColumnPlus,hz,mul_zero]

lemma firstCommonIndices_membership (F : Finset ι) (j : FirstCommonIndex ι) :
    j∈firstCommonIndices F ↔ j.2.1⊆F ∧ j.2.2.1⊆F\j.2.1 ∧ j.2.2.2⊆F\j.2.1 := by
  simp [firstCommonIndices]

lemma firstCommonIndices_mono {F G : Finset ι} (h : F⊆G) : firstCommonIndices F⊆firstCommonIndices G := by
  intro j hj
  rcases (firstCommonIndices_membership F j).mp hj with ⟨hd,hu,hv⟩
  exact (firstCommonIndices_membership G j).mpr ⟨hd.trans h,
    hu.trans (Finset.sdiff_subset_sdiff h le_rfl),hv.trans (Finset.sdiff_subset_sdiff h le_rfl)⟩

lemma firstCommonWeight_zero_outside (F G : Finset ι) (C₁ C₂ : Finset ι→ℂ) (h : O)
    (hC₁ : ∀U,U⊆G → ¬U⊆F → C₁ U=0) (hC₂ : ∀U,U⊆G → ¬U⊆F → C₂ U=0)
    (j : FirstCommonIndex ι) (hj : j∈firstCommonIndices G) (hjF : j∉firstCommonIndices F) :
    firstCommonWeight p hg C₁ C₂ h j=0 := by
  rcases (firstCommonIndices_membership G j).mp hj with ⟨hd,hu,hv⟩
  by_cases hleft : j.2.1∪j.2.2.1⊆F
  · have hright : ¬j.2.1∪j.2.2.2⊆F := by
      intro hr
      apply hjF
      apply (firstCommonIndices_membership F j).mpr
      refine ⟨Finset.Subset.trans Finset.subset_union_left hleft,?_,?_⟩
      · intro i hi
        exact Finset.mem_sdiff.mpr ⟨hleft (Finset.mem_union_right _ hi),(Finset.mem_sdiff.mp (hu hi)).2⟩
      · intro i hi
        exact Finset.mem_sdiff.mpr ⟨hr (Finset.mem_union_right _ hi),(Finset.mem_sdiff.mp (hv hi)).2⟩
    have hz := hC₂ _ (Finset.union_subset hd (hv.trans Finset.sdiff_subset)) hright
    simp only [firstCommonWeight,firstCommonCoefficient,hz,mul_zero,zero_mul]
  · have hz := hC₁ _ (Finset.union_subset hd (hu.trans Finset.sdiff_subset)) hleft
    simp only [firstCommonWeight,firstCommonCoefficient,hz,mul_zero,zero_mul,star_zero]

theorem firstPhysicalCommonRows_fixed_pool (F G : Finset ι) (hFG : F⊆G)
    (C₁ C₂ : Finset ι→ℂ) (hC₁ : ∀U,U⊆G → ¬U⊆F → C₁ U=0)
    (hC₂ : ∀U,U⊆G → ¬U⊆F → C₂ U=0)
    (W₁ W₂ : ℝ→ℂ) (Φ : 𝓢(ℝ,ℂ)) (A₁ A₂ C R K : ℝ) (d h : O) :
    firstPhysicalCommonRows p hg F C₁ C₂ W₁ W₂ Φ A₁ A₂ C R K d h=
      firstPhysicalCommonRows p hg G C₁ C₂ W₁ W₂ Φ A₁ A₂ C R K d h := by
  rw [firstPhysicalCommonRows_indexed,firstPhysicalCommonRows_indexed]
  exact Finset.sum_subset (firstCommonIndices_mono hFG) (fun j hj hn=>by
    rw [firstCommonWeight_zero_outside p hg F G C₁ C₂ h hC₁ hC₂ j hj hn,zero_mul])

end
end InverseMoment

namespace InverseMoment
open scoped BigOperators Classical SchwartzMap
open InverseInitialRayAttachment Eisenstein SchwartzPlanePoisson FirstPassCubeLabels SecondPassArithmetic
open Eisenstein (ringComplex)

noncomputable section
open Eisenstein SchwartzPlanePoisson SecondPassArithmetic
open InverseFirstRayAttachment
open InverseFirstRayAttachment
local notation "O" => Eisenstein.O

def varyingCanonicalSourceTotal {ι : Type*} [DecidableEq ι]
    (p : ι→O) (hp : ∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
    (hg : ∀i,lambda∉Ideal.span {p i})
    (pool : Finset ι) (Q : Finset (ι→₀ℕ)) (labels : Finset (Ideal O))
    (β : Ideal O→(ι→₀ℕ)→ℂ) (Ψ : O→*ℂ) (m : O)
    (H : Ideal O→(ι→₀ℕ)→Finset ι→ℂ) (W : 𝓢(ℝ,ℂ)) (K : ℝ) : ℂ :=
  ∑b∈reopenedCubeFamily Q,∑C∈(pool\b.support).powerset,∑I∈labels,
    reopenedPairCoefficient β b C I *
      canonicalCubeBeforePoisson p hg pool b C Ψ Ψ m m (cubicIdealGenerator I)
        (H I b.rightExponent) (H I b.leftExponent) W K

theorem varying_reopened_smoothed_source {ι : Type*} [DecidableEq ι]
    (p : ι → Eisenstein.O) (hp : ∀ i,p i ≠ 0) [∀ i,(Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i,lambda ∉ Ideal.span {p i})
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (hpr : ∀ i,lambda^2 ∣ p i-1)
    (pool : Finset ι) (Q : Finset (ι →₀ ℕ)) (hQ : ∀ v ∈ Q,v.support ⊆ pool)
    (labels : Finset (Ideal Eisenstein.O)) (β : Ideal Eisenstein.O → (ι →₀ ℕ) → ℂ)
    (Ψ : Eisenstein.O →* ℂ) (m : Eisenstein.O) (H : Ideal O→(ι→₀ℕ)→Finset ι→ℂ) (W : 𝓢(ℝ,ℂ)) (K : ℝ) (hK : 0 < K) :
    (∑ I ∈ labels,∑' z : Eisenstein.O,W (‖ringComplex z‖^2/K)*
      (‖varyingReopenedRow p hg pool Q (β I) Ψ m (cubicIdealGenerator I)
        (H I) z‖^2 : ℝ)) =
    varyingCanonicalSourceTotal p hp hcop hg pool Q labels β Ψ m H W K := by
  rw [varyingCanonicalSourceTotal,sum_reopenedCubeFamily]
  simp only [reopenedPairCoefficient,CubeCoordinates.support]
  calc
    _ = ∑ I ∈ labels,∑ v₂ ∈ Q,∑ v₁ ∈ Q,(star (β I v₂)*β I v₁)*
        canonicalCubeCorrelation p hg pool (v₁.support∪v₂.support) v₁ v₂
          Ψ Ψ m m (cubicIdealGenerator I) (H I v₂)
          (H I v₁) W K := by
      apply Finset.sum_congr rfl
      intro I hI
      exact varying_reopened_smoothed_expand p hg pool Q hQ (β I) Ψ m
        (cubicIdealGenerator I) (H I) W K hK
    _ = ∑ v₂ ∈ Q,∑ v₁ ∈ Q,∑ I ∈ labels,(star (β I v₂)*β I v₁)*
        canonicalCubeCorrelation p hg pool (v₁.support∪v₂.support) v₁ v₂
          Ψ Ψ m m (cubicIdealGenerator I) (H I v₂)
          (H I v₁) W K := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro v₂ hv₂
      rw [Finset.sum_comm]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro v₂ hv₂
      apply Finset.sum_congr rfl
      intro v₁ hv₁
      have hs : v₁.support∪v₂.support ⊆ pool := Finset.union_subset (hQ v₁ hv₁) (hQ v₂ hv₂)
      simp_rw [canonicalCubeCorrelation_eq_blocks p hp hcop hg hinj hpr pool v₁ v₂ hs,
        Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro A₂ hA₂
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro A₁ hA₁
      rw [Finset.sum_comm]

end
end InverseMoment

namespace InverseMoment
noncomputable section
open Eisenstein SchwartzPlanePoisson SecondPassArithmetic
open InverseFirstRayAttachment
open scoped BigOperators Classical SchwartzMap
open InverseInitialRayAttachment Eisenstein SchwartzPlanePoisson FirstPassCubeLabels SecondPassArithmetic
open Eisenstein (ringComplex)

open InverseFirstRayAttachment
local notation "O" => Eisenstein.O
variable {ι : Type*} [DecidableEq ι]
  (p : ι→O) (hp : ∀ i,p i≠0) [∀ i,(Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
  (hg : ∀ i,lambda∉Ideal.span {p i})

def reopenedPhysicalSourceSum (pool : Finset ι) (Q : Finset (ι→₀ℕ))
    (labels : Finset (Ideal O)) (β : Ideal O→(ι→₀ℕ)→ℂ)
    (source : CubeCoordinates ι→Finset ι→Ideal O→ℂ) : ℂ :=
  ∑ b∈reopenedCubeFamily Q,∑ C∈(pool\b.support).powerset,∑ I∈labels,
    reopenedPairCoefficient β b C I*source b C I

def reopenedPhysicalCutoff (b : CubeCoordinates ι) (I : Ideal O)
    (R : Finset ι→ℝ) (D : Finset ι) : Finset O :=
  childFrequencyBall (firstPhysicalMultiplier p b.support b.leftExponent b.rightExponent
    b.leftBit b.rightBit I) (R D)

def reopenedPhysicalRetained (pool : Finset ι) (b : CubeCoordinates ι) (C : Finset ι)
    (Ψ : O→*ℂ) (m : O) (I : Ideal O)
    (mark : (ι→₀ℕ)→Finset ι→ℂ) (W : ℝ→ℂ) (Φ : 𝓢(ℝ,ℂ))
    (K : ℝ) (R : Finset ι→ℝ) : ℂ :=
  canonicalCubeOuter p hg b C Ψ Ψ m m (cubicIdealGenerator I)*
    ∑ D∈(C∪cubePrincipalSupport b.support b.leftExponent b.rightExponent b.leftBit b.rightBit).powerset,
      supportMobius D*
      ∑ h∈(reopenedPhysicalCutoff p b I R D).erase 0,
        firstCubePhysicalMode p hp hg pool b C Ψ Ψ m m (cubicIdealGenerator I)
          (mark b.rightExponent) (mark b.leftExponent) W W Φ K
          ((∏ i ∈ D,p i)) h

include hcop in
theorem original_reopened_physical_split
    (hinj : Function.Injective (fun i=>Ideal.span {p i}))
    (hc : ∀ i,ringChar (O⧸Ideal.span {p i})≠2)
    (hpr : ∀ i,lambda^2∣p i-1)
    (pool : Finset ι) (Q : Finset (ι→₀ℕ)) (hQ : ∀ v∈Q,v.support⊆pool)
    (labels : Finset (Ideal O)) (hlabels : ∀ I∈labels,I≠0)
    (β : Ideal O→(ι→₀ℕ)→ℂ) (Ψ : O→*ℂ) (m : O)
    (mark : Ideal O→(ι→₀ℕ)→Finset ι→ℂ) (W : ℝ→ℂ) (Φ : 𝓢(ℝ,ℂ))
    (K : ℝ) (hK : 0<K) (R : CubeCoordinates ι→Finset ι→Ideal O→Finset ι→ℝ)
    (hR : ∀ b∈reopenedCubeFamily Q,∀ C∈(pool\b.support).powerset,∀ I∈labels,∀ D,0≤ R b C I D) :
    (∑ I∈labels,∑' z:O,Φ (‖ringComplex z‖^2/K)*
      (‖varyingReopenedRow p hg pool Q (β I) Ψ m (cubicIdealGenerator I)
        (fun v U=>mark I v U*W (primeProductNorm p U)) z‖^2:ℝ)) =
    reopenedPhysicalSourceSum pool Q labels β (fun b C I=>
      canonicalCubeDualZero p hp hg pool b C Ψ Ψ m m (cubicIdealGenerator I)
        (fun U=>mark I b.rightExponent U*W (primeProductNorm p U))
        (fun U=>mark I b.leftExponent U*W (primeProductNorm p U)) Φ K) +
    reopenedPhysicalSourceSum pool Q labels β (fun b C I=>
      reopenedPhysicalRetained p hp hg pool b C Ψ m I (mark I) W Φ K (R b C I)) +
    reopenedPhysicalSourceSum pool Q labels β (fun b C I=>
      canonicalCubeDualTail p hp hg pool b C Ψ Ψ m m (cubicIdealGenerator I)
        (fun U=>mark I b.rightExponent U*W (primeProductNorm p U))
        (fun U=>mark I b.leftExponent U*W (primeProductNorm p U)) Φ K
        (reopenedPhysicalCutoff p b I (R b C I))) := by
  rw [varying_reopened_smoothed_source p hp hcop hg hinj hpr pool Q hQ labels β Ψ m]
  · unfold varyingCanonicalSourceTotal reopenedPhysicalSourceSum
    simp only [←Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro b hb
    apply Finset.sum_congr rfl
    intro C hC
    apply Finset.sum_congr rfl
    intro I hI
    have hCb : Disjoint C b.support := by
      exact Finset.disjoint_left.mpr (fun i hi hib=>
        (Finset.mem_sdiff.mp ((Finset.mem_powerset.mp hC) hi)).2 hib)
    have he := canonical_first_physical_split p hp hcop hg hinj hc hpr pool b
      (reopenedCubeFamily_admissible Q b hb) C hCb Ψ Ψ m m I (hlabels I hI)
      (mark I b.rightExponent) (mark I b.leftExponent) W W Φ K hK (R b C I) (hR b hb C hC I hI)
    dsimp only at he
    rw [he]
    simp only [reopenedPhysicalRetained]
    rw [show reopenedPhysicalCutoff p b I (R b C I) =
      (fun D=>childFrequencyBall (firstPhysicalMultiplier p b.support b.leftExponent b.rightExponent
        b.leftBit b.rightBit I) (R b C I D)) from rfl]
    ring
  · exact hK

end
end InverseMoment

namespace InverseMoment
open scoped BigOperators Classical SchwartzMap
open InverseInitialRayAttachment Eisenstein SchwartzPlanePoisson FirstPassCubeLabels SecondPassArithmetic
noncomputable section
open Eisenstein SchwartzPlanePoisson SecondPassArithmetic
open InverseFirstRayAttachment
open InverseFirstRayAttachment
local notation "O" => Eisenstein.O
variable {ι : Type*} [DecidableEq ι]

def firstRetainedSource (p : ι→O) (labels : Finset (Ideal O)) (b : CubeCoordinates ι) (Y : ℝ) :
    Finset (Ideal O×O) :=
  labels.biUnion (fun f=> (nonzeroChildFrequencyBall
    (firstPhysicalMultiplier p b.support b.leftExponent b.rightExponent b.leftBit b.rightBit f) Y).image
      (fun h=>(f,h)))

theorem mem_firstRetainedSource (p : ι→O) (labels : Finset (Ideal O)) (b : CubeCoordinates ι) (Y : ℝ)
    (x : Ideal O×O) :
    x∈firstRetainedSource p labels b Y ↔ x.1∈labels ∧ x.2∈nonzeroChildFrequencyBall
      (firstPhysicalMultiplier p b.support b.leftExponent b.rightExponent b.leftBit b.rightBit x.1) Y := by
  rcases x with ⟨f,h⟩
  simp [firstRetainedSource]

theorem sum_firstRetainedSource {A : Type*} [AddCommMonoid A]
    (p : ι→O) (labels : Finset (Ideal O)) (b : CubeCoordinates ι) (Y : ℝ) (H : Ideal O×O→A) :
    ∑ x∈firstRetainedSource p labels b Y,H x =
    ∑ f∈labels,∑ h∈nonzeroChildFrequencyBall
      (firstPhysicalMultiplier p b.support b.leftExponent b.rightExponent b.leftBit b.rightBit f) Y,H (f,h) := by
  unfold firstRetainedSource
  rw [Finset.sum_biUnion]
  · apply Finset.sum_congr rfl
    intro f hf
    exact Finset.sum_image (fun h hh k hk he=>congrArg Prod.snd he)
  · intro f hf g hg hfg
    apply Finset.disjoint_left.mpr
    intro x hx hy
    obtain ⟨h,hh,rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨k,hk,he⟩ := Finset.mem_image.mp hy
    exact hfg (congrArg Prod.fst he).symm

variable (p : ι→O) (hp : ∀ i,p i≠0) [∀ i,(Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
  (hg : ∀ i,lambda∉Ideal.span {p i})

include hcop in
theorem original_retained_label_family
    (hinj : Function.Injective (fun i=>Ideal.span {p i}))
    (hc : ∀ i,ringChar (O⧸Ideal.span {p i})≠2)
    (hpr : ∀ i,lambda^2∣p i-1)
    (pool : Finset ι) (b : CubeCoordinates ι) (hb : b.Admissible)
    (C : Finset ι) (hC : Disjoint C b.support)
    (Ψ₁ Ψ₂ : O→*ℂ) (m₁ m₂ : O) (H₁ H₂ : Finset ι→ℂ)
    (W₁ W₂ : ℝ→ℂ) (Φ : 𝓢(ℝ,ℂ)) (K : ℝ)
    (labels : Finset (Ideal O)) (a : Ideal O→ℂ) (R : Finset ι→ℝ) :
    (∑ f∈labels,a f*canonicalCubeDualFinite p hp hg pool b C Ψ₁ Ψ₂ m₁ m₂
      (cubicIdealGenerator f)
      (fun U=>H₁ U*W₁ (primeProductNorm p U)) (fun U=>H₂ U*W₂ (primeProductNorm p U)) Φ K
      (fun D=>childFrequencyBall
        (firstPhysicalMultiplier p b.support b.leftExponent b.rightExponent b.leftBit b.rightBit f) (R D))) =
    ∑ D∈(C∪cubePrincipalSupport b.support b.leftExponent b.rightExponent b.leftBit b.rightBit).powerset,
      supportMobius D*
      ∑ x∈firstRetainedSource p labels b (R D),a x.1*
        canonicalCubeOuter p hg b C Ψ₁ Ψ₂ m₁ m₂ (cubicIdealGenerator x.1)*
        firstCubePhysicalMode p hp hg pool b C Ψ₁ Ψ₂ m₁ m₂ (cubicIdealGenerator x.1)
          H₁ H₂ W₁ W₂ Φ K ((∏ i ∈ D,p i)) x.2 := by
  simp_rw [canonical_retained_physical p hp hcop hg hinj hc hpr pool b hb C hC]
  simp only [Finset.mul_sum,sum_firstRetainedSource,nonzeroChildFrequencyBall]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro D hD
  apply Finset.sum_congr rfl
  intro f hf
  apply Finset.sum_congr rfl
  intro h hh
  ring

end
end InverseMoment

namespace InverseMoment
open scoped BigOperators Classical
open InverseInitialRayAttachment Eisenstein SchwartzPlanePoisson FirstPassCubeLabels SecondPassArithmetic RayFourExpansion
open Eisenstein (ringComplex)
noncomputable section
open Eisenstein SchwartzPlanePoisson SecondPassArithmetic
open InverseFirstRayAttachment
open InverseFirstRayAttachment
local notation "Eis" => Eisenstein.O
variable {ι σ : Type*} [DecidableEq ι] [DecidableEq σ]
  (p : ι→Eis) (hp : ∀ i,p i≠0) [∀ i,(Ideal.span {p i}).IsMaximal]
  (hg : ∀ i,lambda∉Ideal.span {p i})

theorem first_fresh_real_energy
    (hinj : Function.Injective (fun i=>Ideal.span {p i}))
    (hc : ∀ i,ringChar (Eis ⧸ Ideal.span {p i})≠2)
    (F D B : Finset ι) (v : ι→ℕ) (ε₁ ε₂ : ι→Bool)
    (negative : Bool) (χ : RayCharacter) (Ψ : Eis→*ℂ) (m : Eis)
    (H : Finset ι→ℂ) (omega : ℝ→ℂ) (X : ℝ) (c d : Eis)
    (core : FirstCoreIndex) (height Y : ℝ) (hY : 0<Y) :
    (firstFreshSecondPoisson p hp hg hinj F D B v ε₁ ε₂ negative χ Ψ m H omega X c d core height Y).re =
    ∑ z∈rowMajorantBall Y,(rowMajorant (‖ringComplex z‖^2/Y)).re *
      ‖firstCoreInputRow p hg F D B v ε₁ ε₂ negative χ Ψ m H
        (fun u=>omega (Real.exp u)) (columnLog p (primeProductNorm p D*X)) c d core (-height) z‖^2 := by
  unfold firstFreshSecondPoisson
  rw [←firstCoreInputRow_smoothed_second_poisson p hg hp hinj hc F D B v ε₁ ε₂ negative χ Ψ m
    H (fun u=>omega (Real.exp u)) (columnLog p (primeProductNorm p D*X)) c d core (-height) rowMajorant Y hY,
    rowMajorant_tsum_eq_sum _ Y hY]
  let P := fun z=>firstCoreInputRow p hg F D B v ε₁ ε₂ negative χ Ψ m H
    (fun u=>omega (Real.exp u)) (columnLog p (primeProductNorm p D*X)) c d core (-height) z
  change (∑ z∈rowMajorantBall Y,rowMajorant (‖ringComplex z‖^2/Y)*(‖P z‖^2 : ℝ)).re =
    ∑ z∈rowMajorantBall Y,(rowMajorant (‖ringComplex z‖^2/Y)).re*‖P z‖^2
  simp only [Complex.re_sum,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,mul_zero,sub_zero]

lemma priority_norm_sum_sq {α : Type*} (s : Finset α) (f : α→ℂ) :
    ‖∑ i∈s,f i‖^2≤(s.card:ℝ)*∑ i∈s,‖f i‖^2 := by
  have hnorm := pow_le_pow_left₀ (norm_nonneg _) (norm_sum_le s f) 2
  apply hnorm.trans
  simpa using Finset.sum_mul_sq_le_sq_mul_sq s (fun _=>(1:ℝ)) (fun i=>‖f i‖)

theorem first_fresh_priority_energy
    (hinj : Function.Injective (fun i=>Ideal.span {p i}))
    (hc : ∀ i,ringChar (Eis ⧸ Ideal.span {p i})≠2)
    (F D B A : Finset ι) (v : ι→ℕ) (ε₁ ε₂ : ι→Bool)
    (negative : Bool) (χ : RayCharacter) (Ψ : Eis→*ℂ) (m : Eis)
    (slots : Finset σ) (lists : σ→Finset ι) (a : σ→ι→ℂ)
    (H : Finset ι→ℂ) (omega : ℝ→ℂ) (X : ℝ) (c d : Eis)
    (core : FirstCoreIndex) (height Y : ℝ) (hY : 0<Y) :
    (firstFreshSecondPoisson p hp hg hinj F D B v ε₁ ε₂ negative χ Ψ m
      (fun U=>primeMark slots lists a (A∪U)*H U) omega X c d core height Y).re ≤
    (2:ℝ)^slots.card * ∑ J∈slots.powerset,‖primeMark J lists a (A∪D)‖^2 *
      (firstFreshSecondPoisson p hp hg hinj F D B v ε₁ ε₂ negative χ Ψ m
        (fun U=>primeMark (slots\J) (fun i=>lists i\(A∪D)) a U*H U) omega X c d core height Y).re := by
  rw [first_fresh_real_energy p hp hg hinj hc F D B v ε₁ ε₂ negative χ Ψ m _ omega X c d core height Y hY]
  calc
    _ ≤ ∑ z∈rowMajorantBall Y,(rowMajorant (‖ringComplex z‖^2/Y)).re *
        ((slots.powerset.card:ℝ)*∑ J∈slots.powerset,
          ‖primeMark J lists a (A∪D) * firstCoreInputRow p hg F D B v ε₁ ε₂ negative χ Ψ m
            (fun U=>primeMark (slots\J) (fun i=>lists i\(A∪D)) a U*H U)
            (fun u=>omega (Real.exp u)) (columnLog p (primeProductNorm p D*X)) c d core (-height) z‖^2) := by
      apply Finset.sum_le_sum
      intro z hz
      apply mul_le_mul_of_nonneg_left _ (rowMajorant_nonneg _)
      rw [firstCoreInputRow_marked_priority]
      exact priority_norm_sum_sq _ _
    _ = _ := by
      simp_rw [first_fresh_real_energy p hp hg hinj hc F D B v ε₁ ε₂ negative χ Ψ m _ omega X c d core height Y hY]
      simp only [Finset.card_powerset,Nat.cast_pow,Nat.cast_ofNat,Finset.mul_sum,norm_mul,mul_pow]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro J hJ
      apply Finset.sum_congr rfl
      intro z hz
      ring

end
end InverseMoment

namespace InverseMoment
open scoped BigOperators Classical SchwartzMap
open InverseInitialRayAttachment Eisenstein SchwartzPlanePoisson FirstPassCubeLabels SecondPassArithmetic RayFourExpansion
noncomputable section
open Eisenstein SchwartzPlanePoisson SecondPassArithmetic
open InverseFirstRayAttachment
open InverseFirstRayAttachment
local notation "O" => Eisenstein.O

variable {ι : Type*} [DecidableEq ι]
  (p : ι→O) (hp : ∀ i,p i≠0) [∀ i,(Ideal.span {p i}).IsMaximal]
  (hg : ∀ i,lambda∉Ideal.span {p i})

def firstCanonicalSecondEnergy (hinj : Function.Injective (fun i=>Ideal.span {p i}))
    (F : Finset ι) (b : CubeCoordinates ι) (C : Finset ι) (negative : Bool)
    (Ψ : O→*ℂ) (m d : O) (H selector : Finset ι→ℂ) (omega : ℝ→ℂ) (X t Y : ℝ) : ℝ :=
  firstCoreMassBound*∑ r : RayCharacter×RayCharacter,∑ D∈F.powerset,
    (‖crossCoeff r.1 r.2‖*‖selector D‖)*∑ core : FirstCoreIndex,
      ‖firstCoreOuter p hg b.support (fun i=>b.leftExponent i+b.rightExponent i) b.leftBit b.rightBit negative Ψ m D core‖ *
      (firstFreshSecondPoisson p hp hg hinj F D b.support (fun i=>b.leftExponent i+b.rightExponent i)
        b.leftBit b.rightBit negative (if negative then r.1 else r.2) Ψ m
        (fun U=>H (((if negative then b.rightDivisor else b.leftDivisor)∪C)∪U)) omega X (∏i∈C,p i) d core t Y).re

theorem firstCanonicalSecondEnergy_nonneg (hinj : Function.Injective (fun i=>Ideal.span {p i}))
    (hc : ∀ i,ringChar (O⧸Ideal.span {p i})≠2)
    (F : Finset ι) (b : CubeCoordinates ι) (C : Finset ι) (negative : Bool)
    (Ψ : O→*ℂ) (m d : O) (H selector : Finset ι→ℂ) (omega : ℝ→ℂ) (X t Y : ℝ) (hY : 0<Y) :
    0≤ firstCanonicalSecondEnergy p hp hg hinj F b C negative Ψ m d H selector omega X t Y := by
  unfold firstCanonicalSecondEnergy
  apply mul_nonneg firstCoreMassBound_nonneg
  apply Finset.sum_nonneg
  intro r hr
  apply Finset.sum_nonneg
  intro D hD
  apply mul_nonneg (by positivity)
  apply Finset.sum_nonneg
  intro core hcore
  apply mul_nonneg (norm_nonneg _)
  rw [first_fresh_real_energy p hp hg hinj hc F D b.support
    (fun i=>b.leftExponent i+b.rightExponent i) b.leftBit b.rightBit negative
    (if negative then r.1 else r.2) Ψ m _ omega X (∏i∈C,p i) d core t Y hY]
  exact Finset.sum_nonneg (fun z hz=>mul_nonneg (rowMajorant_nonneg _) (sq_nonneg _))

theorem first_retained_actual_second_energy (ε : ℝ) (hε : 0<ε) :
    ∃ K : ℝ,0<K ∧ ∀ {ι : Type*} [DecidableEq ι]
      (p : ι→O) (hp : ∀ i,p i≠0) [∀ i,(Ideal.span {p i}).IsMaximal]
      (hinj : Function.Injective (fun i=>Ideal.span {p i}))
      (hcop : Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
      (hg : ∀ i,lambda∉Ideal.span {p i})
      (_hc : ∀ i,ringChar (O⧸Ideal.span {p i})≠2)
      (_hpr : ∀ i,lambda^2∣p i-1)
      (F : Finset ι) (b : CubeCoordinates ι) (C : Finset ι)
      (Ψ₁ Ψ₂ : O→*ℂ),(∀ u,‖Ψ₁ u‖≤1) → (∀ u,‖Ψ₂ u‖≤1) →
      ∀ (m₁ m₂ d : O) (labels : Finset (Ideal O)) (a : Ideal O×O→ℂ) (Γ Y : ℝ),0≤Γ → 0<Y →
      (∀ f∈labels,Squarefree f) → (∀ f∈labels,f≠0) → (∀ x∈firstRetainedSource p labels b Y,‖a x‖≤Γ) →
      ∀ (negative : Bool) (H selector : Finset ι→ℂ) (omega : ℝ→ℂ) (X t : ℝ),0<X →
      firstFamilyEnergy p hg (firstRetainedSource p labels b Y) F (fun _=>selector)
        (firstCanonicalCoefficient p hg b C negative
          (if negative then Ψ₁ else Ψ₂) (if negative then m₁ else m₂) d H)
        (retainedCubeWeight p hp hg b C Ψ₁ Ψ₂ m₁ m₂ d a) negative omega X t Prod.snd ≤
      Γ*K*Y^ε * firstCanonicalSecondEnergy p hp hg hinj F b C negative
        (if negative then Ψ₁ else Ψ₂) (if negative then m₁ else m₂) d H selector omega X t Y := by
  obtain ⟨K,hK,hstep⟩ := retained_cube_energy_to_second ε hε
  refine ⟨K,hK,?_⟩
  intro ι _ p hp _ hinj hcop hg hc hpr F b C Ψ₁ Ψ₂ hΨ₁ hΨ₂ m₁ m₂ d labels a Γ Y hΓ hY
    hlabels hn ha negative H selector omega X t hX
  have he := hstep p hp hinj hcop hg hc hpr F b C Ψ₁ Ψ₂ hΨ₁ hΨ₂ m₁ m₂ d a
    (firstRetainedSource p labels b Y) Γ Y hΓ hY
    (fun x hx=>hlabels x.1 ((mem_firstRetainedSource p labels b Y x).mp hx).1)
    (fun x hx=>hn x.1 ((mem_firstRetainedSource p labels b Y x).mp hx).1) ha
    (fun x hx=>((mem_firstRetainedSource p labels b Y x).mp hx).2)
    negative H selector omega X t hX
  have hcoef : firstCanonicalCoefficient p hg b C negative
      (if negative then Ψ₁ else Ψ₂) (if negative then m₁ else m₂) d H =
      fun x=>firstOldLabelCoefficient p hp hcop hg b.support
        (fun i=>b.leftExponent i+b.rightExponent i) b.leftBit b.rightBit negative
        (multiplicativeCoreColumn p (if negative then Ψ₁ else Ψ₂) (if negative then m₁ else m₂)
          (fun U=>H (((if negative then b.rightDivisor else b.leftDivisor)∪C)∪U)))
        (∏i∈C,p i) d x.1 := by
    funext x
    exact firstCanonicalCoefficient_old p hp hcop hg b C negative _ _ d H x
  rw [hcoef]
  exact he

end
end InverseMoment

namespace InverseMoment
open scoped BigOperators Classical SchwartzMap
open InverseInitialRayAttachment Eisenstein SchwartzPlanePoisson FirstPassCubeLabels SecondPassArithmetic RayFourExpansion
noncomputable section
open Eisenstein SchwartzPlanePoisson SecondPassArithmetic
open InverseFirstRayAttachment
open InverseFirstRayAttachment
local notation "O" => Eisenstein.O
variable {ι σ : Type*} [DecidableEq ι] [DecidableEq σ]
  (p : ι→O) (hp : ∀ i,p i≠0) [∀ i,(Ideal.span {p i}).IsMaximal]
  (hg : ∀ i,lambda∉Ideal.span {p i})

def firstPrioritySecondEnergy (hinj : Function.Injective (fun i=>Ideal.span {p i}))
    (F : Finset ι) (b : CubeCoordinates ι) (C : Finset ι) (negative : Bool)
    (Ψ : O→*ℂ) (m d : O) (slots : Finset σ) (lists : σ→Finset ι) (a : σ→ι→ℂ)
    (selector : Finset ι→ℂ) (omega : ℝ→ℂ) (X t Y : ℝ) : ℝ :=
  let A := (if negative then b.rightDivisor else b.leftDivisor)∪C
  firstCoreMassBound*(2:ℝ)^slots.card * ∑ r : RayCharacter×RayCharacter,∑ D∈F.powerset,
    (‖crossCoeff r.1 r.2‖*‖selector D‖)*∑ core : FirstCoreIndex,
      ‖firstCoreOuter p hg b.support (fun i=>b.leftExponent i+b.rightExponent i) b.leftBit b.rightBit negative Ψ m D core‖ *
      ∑ J∈slots.powerset,‖primeMark J lists a (A∪D)‖^2 *
        (firstFreshSecondPoisson p hp hg hinj F D b.support (fun i=>b.leftExponent i+b.rightExponent i)
          b.leftBit b.rightBit negative (if negative then r.1 else r.2) Ψ m
          (fun U=>primeMark (slots\J) (fun i=>lists i\(A∪D)) a U)
          omega X (∏i∈C,p i) d core t Y).re

theorem first_actual_second_prime_priority
    (hinj : Function.Injective (fun i=>Ideal.span {p i}))
    (hc : ∀ i,ringChar (O⧸Ideal.span {p i})≠2)
    (F : Finset ι) (b : CubeCoordinates ι) (C : Finset ι) (negative : Bool)
    (Ψ : O→*ℂ) (m d : O) (slots : Finset σ) (lists : σ→Finset ι) (a : σ→ι→ℂ)
    (selector : Finset ι→ℂ) (omega : ℝ→ℂ) (X t Y : ℝ) (hY : 0<Y) :
    firstCanonicalSecondEnergy p hp hg hinj F b C negative Ψ m d
      (primeMark slots lists a) selector omega X t Y ≤
    firstPrioritySecondEnergy p hp hg hinj F b C negative Ψ m d slots lists a selector omega X t Y := by
  let A := (if negative then b.rightDivisor else b.leftDivisor)∪C
  have hb (r : RayCharacter×RayCharacter) (D : Finset ι) (core : FirstCoreIndex) :=
    first_fresh_priority_energy p hp hg hinj hc F D b.support A
      (fun i=>b.leftExponent i+b.rightExponent i) b.leftBit b.rightBit negative
      (if negative then r.1 else r.2) Ψ m slots lists a (fun _=>1)
      omega X (∏i∈C,p i) d core t Y hY
  simp only [mul_one] at hb
  unfold firstCanonicalSecondEnergy firstPrioritySecondEnergy
  simp only [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro r hr
  apply Finset.sum_le_sum
  intro D hD
  apply Finset.sum_le_sum
  intro core hcore
  have h := mul_le_mul_of_nonneg_left (hb r D core)
    (show 0≤firstCoreMassBound*(‖crossCoeff r.1 r.2‖*‖selector D‖)*
      ‖firstCoreOuter p hg b.support (fun i=>b.leftExponent i+b.rightExponent i)
        b.leftBit b.rightBit negative Ψ m D core‖ from mul_nonneg (mul_nonneg firstCoreMassBound_nonneg (mul_nonneg (norm_nonneg _) (norm_nonneg _))) (norm_nonneg _))
  convert h using 1
  · dsimp only [A]
    ring
  · simp only [A,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro J hJ
    ring

end
end InverseMoment

namespace InverseMoment
open scoped BigOperators Classical SchwartzMap
open InverseInitialRayAttachment Eisenstein SchwartzPlanePoisson FirstPassCubeLabels SecondPassArithmetic InverseSecondFibers
open InverseInitialArithmetic (sourceIdeal)
noncomputable section
open Eisenstein SchwartzPlanePoisson SecondPassArithmetic
open InverseFirstRayAttachment
open InverseInitialRayAttachment InverseFirstRayAttachment
open InverseFirstRayAttachment
local notation "Eis" => Eisenstein.O
variable {ι σ : Type*} [DecidableEq ι] [DecidableEq σ]

omit [DecidableEq ι] in
@[simp] theorem secondParentOf_attach {Jo : ℕ} (parent : SecondParentSource ι Jo)
    (x : SecondExpansionData ι) : secondParentOf (attachSecondExpansion parent x) = parent := rfl

def attachedSecondFamily {Jo : ℕ} (parents : Finset (SecondParentSource ι Jo))
    (source : SecondParentSource ι Jo → Finset (SecondExpansionData ι)) :
    Finset (MarkedSecondSource ι Jo 0) :=
  parents.biUnion (fun parent => (source parent).image (attachSecondExpansion parent))

omit [DecidableEq ι] in
theorem mem_attachedSecondFamily {Jo : ℕ} (parents : Finset (SecondParentSource ι Jo))
    (source : SecondParentSource ι Jo → Finset (SecondExpansionData ι))
    (x : MarkedSecondSource ι Jo 0) :
    x∈attachedSecondFamily parents source ↔
      secondParentOf x∈parents ∧ x.second∈source (secondParentOf x) := by
  simp only [attachedSecondFamily,Finset.mem_biUnion,Finset.mem_image]
  constructor
  · rintro ⟨parent,hp,y,hy,rfl⟩
    exact ⟨hp,hy⟩
  · rintro ⟨hp,hx⟩
    exact ⟨secondParentOf x,hp,x.second,hx,attachSecondExpansion_recover x⟩

omit [DecidableEq ι] in
theorem sum_attachedSecondFamily {Jo : ℕ} (parents : Finset (SecondParentSource ι Jo))
    (source : SecondParentSource ι Jo → Finset (SecondExpansionData ι))
    {A : Type*} [AddCommMonoid A] (H : MarkedSecondSource ι Jo 0 → A) :
    ∑ x∈attachedSecondFamily parents source,H x =
      ∑ parent∈parents,∑ x∈source parent,H (attachSecondExpansion parent x) := by
  unfold attachedSecondFamily
  rw [Finset.sum_biUnion]
  · apply Finset.sum_congr rfl
    intro parent hp
    exact Finset.sum_image (fun x hx y hy he => attachSecondExpansion_injective parent he)
  · intro a ha b hb hab
    apply Finset.disjoint_left.mpr
    intro x hx hy
    obtain ⟨y,hy,rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨z,hz,he⟩ := Finset.mem_image.mp hy
    exact hab (congrArg secondParentOf he).symm

variable (p : ι → Eis) (hp : ∀ i,p i ≠ 0) [∀ i,(Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i,lambda ∉ Ideal.span {p i})

omit [∀ (i : ι), (Ideal.span {p i}).IsMaximal] in
theorem attached_family_conditions {Jo : ℕ} (parents : Finset (SecondParentSource ι Jo))
    (source : SecondParentSource ι Jo → Finset (SecondExpansionData ι))
    (ha : ∀ parent∈parents,parent.cube.Admissible)
    (hC : ∀ parent∈parents,Disjoint parent.firstCommon parent.cube.support)
    (hD : ∀ parent∈parents,parent.firstDivisor ⊆ parent.firstCommon∪parent.cube.support)
    (hE : ∀ parent∈parents,∀ x∈source parent,x.divisor ⊆ x.sourceCommon)
    (hold : ∀ parent∈parents,∀ i,(parent.oldAssigned i).val ∣
      sourceIdeal p parent.cube.support*sourceIdeal p parent.firstCommon*parent.quotient)
    (hq : ∀ parent∈parents,parent.quotient ≠ 0) :
    ActualSecondSourceConditions p (attachedSecondFamily parents source) := by
  have h (x : MarkedSecondSource ι Jo 0) (hx : x∈attachedSecondFamily parents source) :=
    (mem_attachedSecondFamily parents source x).mp hx
  constructor
  · intro x hx; exact ha (secondParentOf x) (h x hx).1
  · intro x hx; exact hC (secondParentOf x) (h x hx).1
  · intro x hx; exact hD (secondParentOf x) (h x hx).1
  · intro x hx; exact hE (secondParentOf x) (h x hx).1 x.second (h x hx).2
  · intro x hx i; exact hold (secondParentOf x) (h x hx).1 i
  · intro x hx i; exact Fin.elim0 i
  · intro x hx; exact hq (secondParentOf x) (h x hx).1

include hp hcop in
theorem secondExpansionSource_whole_parent_family
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (hpr : ∀ i,lambda^2 ∣ p i-1)
    {Jo : ℕ} (parents : Finset (SecondParentSource ι Jo))
    (source : SecondParentSource ι Jo → Finset (SecondExpansionData ι))
    (hE : ∀ parent∈parents,∀ x∈source parent,x.divisor ⊆ x.sourceCommon)
    (w : SecondParentSource ι Jo → ℂ)
    (pool : Finset ι) (Ψ : Eis →* ℂ) (m : Eis) (z : SecondRayIndex)
    (slots₁ slots₂ : Finset σ) (lists₁ lists₂ : σ → Finset ι) (a₁ a₂ : σ → ι → ℂ)
    (W₁ W₂ : ℝ → ℂ) (Φ : 𝓢(ℝ,ℂ)) (X Y : ℝ) :
    (∑ parent∈parents,w parent*secondExpansionSource p hg pool Ψ
      (secondParentPuncture p m parent) (secondParentLabel p parent) (secondParentDivisor p parent)
      z (source parent)
      (fun U => primeMark slots₁ lists₁ a₁ U*W₁ (primeProductNorm p U/X))
      (fun U => primeMark slots₂ lists₂ a₂ U*W₂ (primeProductNorm p U/X)) Φ Y) =
    (Y : ℂ)*secondRayCoefficient z *
      ∑ x∈attachedSecondFamily parents source,
        (w (secondParentOf x)*actualSecondSignedWeight p hg Ψ
          (m*cubicIdealGenerator x.quotient) z x)*
          actualSecondProfileRow p hg pool (secondInheritedProfile p x Ψ m z)
            slots₁ slots₂ lists₁ lists₂ a₁ a₂ W₁ W₂ Φ Y X := by
  rw [sum_attachedSecondFamily]
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro parent hparent
  rw [secondExpansionSource_attached p hp hg hinj hpr parent (source parent) (hE parent hparent)]
  rw [Finset.sum_image (fun x hx y hy he => attachSecondExpansion_injective parent he)]
  simp only [Finset.mul_sum,secondParentOf_attach]
  apply Finset.sum_congr rfl
  intro x hx
  ring

end
end InverseMoment

noncomputable section
open Eisenstein SchwartzPlanePoisson SecondPassArithmetic
open InverseFirstRayAttachment
open scoped BigOperators Classical SchwartzMap

namespace InverseMoment
open InverseInitialRayAttachment Eisenstein SchwartzPlanePoisson FirstPassCubeLabels SecondPassArithmetic RayFourExpansion
open Eisenstein SchwartzPlanePoisson InverseFirstRayAttachment
open InverseFirstRayAttachment
local notation "Eis"=>Eisenstein.O
variable {ι κ:Type*} [DecidableEq ι] [DecidableEq κ]

def firstGlobalRetainedSource (p:ι→Eis) (outer:Finset κ)
    (labels:κ→Finset (Ideal Eis)) (cube:κ→CubeCoordinates ι) (Y:ℝ):
    Finset (Σ _ : κ,Ideal Eis×Eis):=
  outer.sigma (fun k=>firstRetainedSource p (labels k) (cube k) Y)

omit [DecidableEq κ] in
theorem first_global_retained_push (ε:ℝ)(hε:0<ε):
    ∃ K:ℝ,0<K ∧ ∀ (p:ι→Eis)(hp:∀i,p i≠0)
    [∀i,(Ideal.span {p i}).IsMaximal]
    (hinj:Function.Injective (fun i=>Ideal.span {p i}))
    (hcop:Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
    (hg:∀i,lambda∉Ideal.span {p i})
    (_hc:∀i,ringChar (Eis⧸Ideal.span {p i})≠2)
    (_hpr:∀i,lambda^2∣p i-1)
    (F:Finset ι)(outer:Finset κ)(cube:κ→CubeCoordinates ι)(common:κ→Finset ι)
    (Ψ₁ Ψ₂:Eis→*ℂ)(m₁ m₂:Eis)(d:κ→Eis)
    (labels:κ→Finset (Ideal Eis))(a:κ→Ideal Eis×Eis→ℂ)(Γ Y:ℝ),
    (∀u,‖Ψ₁ u‖≤1)→(∀u,‖Ψ₂ u‖≤1)→0≤Γ→0<Y→
    (∀k∈outer,∀f∈labels k,Squarefree f)→(∀k∈outer,∀f∈labels k,f≠0)→
    (∀k∈outer,∀x∈firstRetainedSource p (labels k) (cube k) Y,‖a k x‖≤Γ)→
    ∀(negative:Bool)(H selector:κ→Finset ι→ℂ)(omega:ℝ→ℂ)(X t:ℝ),0<X→
    firstFamilyEnergy p hg (firstGlobalRetainedSource p outer labels cube Y) F
      (fun x=>selector x.1)
      (fun x=>firstCanonicalCoefficient p hg (cube x.1) (common x.1) negative
        (if negative then Ψ₁ else Ψ₂) (if negative then m₁ else m₂) (d x.1) (H x.1) x.2)
      (fun x=>retainedCubeWeight p hp hg (cube x.1) (common x.1) Ψ₁ Ψ₂ m₁ m₂
        (d x.1) (a x.1) x.2)
      negative omega X t (fun x=>x.2.2) ≤
    Γ*K*Y^ε*∑k∈outer,firstCanonicalSecondEnergy p hp hg hinj F (cube k) (common k)
      negative (if negative then Ψ₁ else Ψ₂) (if negative then m₁ else m₂) (d k)
      (H k) (selector k) omega X t Y := by
  obtain ⟨K,hK,hpush⟩:=first_retained_actual_second_energy ε hε
  refine ⟨K,hK,?_⟩
  intro p hp _ hinj hcop hg hc hpr F outer cube common Ψ₁ Ψ₂ m₁ m₂ d labels a Γ Y
    hΨ₁ hΨ₂ hΓ hY hs hn ha negative H selector omega X t hX
  simp only [firstFamilyEnergy,firstGlobalRetainedSource,Finset.sum_sigma]
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro k hk
  exact hpush p hp hinj hcop hg hc hpr F (cube k) (common k) Ψ₁ Ψ₂ hΨ₁ hΨ₂ m₁ m₂
    (d k) (labels k) (a k) Γ Y hΓ hY (hs k hk) (hn k hk) (ha k hk)
    negative (H k) (selector k) omega X t hX

end InverseMoment

end

namespace InverseMoment
noncomputable section
open Eisenstein SchwartzPlanePoisson SecondPassArithmetic
open InverseFirstRayAttachment
open scoped BigOperators Classical SchwartzMap
open InverseInitialRayAttachment Eisenstein SchwartzPlanePoisson FirstPassCubeLabels SecondPassArithmetic
open InverseFirstRayAttachment
local notation "O" => Eisenstein.O
variable {ι : Type*} [DecidableEq ι]

abbrev FirstOriginalOuter (ι : Type*) := Σ _ : CubeCoordinates ι,Σ _ : Finset ι,Finset ι

def firstOriginalOuter (pool : Finset ι) (Q : Finset (ι→₀ℕ)) : Finset (FirstOriginalOuter ι) :=
  (reopenedCubeFamily Q).sigma (fun b=>(pool\b.support).powerset.sigma
    (fun C=>(C∪cubePrincipalSupport b.support b.leftExponent b.rightExponent b.leftBit b.rightBit).powerset))

lemma mem_firstOriginalOuter (pool : Finset ι) (Q : Finset (ι→₀ℕ)) (k : FirstOriginalOuter ι) :
    k∈firstOriginalOuter pool Q ↔ k.1∈reopenedCubeFamily Q ∧ k.2.1∈(pool\k.1.support).powerset ∧
      k.2.2∈(k.2.1∪cubePrincipalSupport k.1.support k.1.leftExponent k.1.rightExponent k.1.leftBit k.1.rightBit).powerset := by
  simp [firstOriginalOuter]

lemma retained_cutoff_enlargement (E : O) (hE : E≠0) (R Y : ℝ) (hRY : R≤ Y) (f : O→ℂ) :
    (∑h∈(childFrequencyBall E R).erase 0,f h)=
      ∑h∈nonzeroChildFrequencyBall E Y,(if h∈childFrequencyBall E R then (1:ℂ) else 0)*f h := by
  have hsub : (childFrequencyBall E R).erase 0⊆nonzeroChildFrequencyBall E Y := by
    intro h hh
    rcases Finset.mem_erase.mp hh with ⟨hn,hm⟩
    exact Finset.mem_erase.mpr ⟨hn,(mem_childFrequencyBall E hE Y h).mpr
      (((mem_childFrequencyBall E hE R h).mp hm).trans hRY)⟩
  calc
    _=∑h∈(childFrequencyBall E R).erase 0,(if h∈childFrequencyBall E R then (1:ℂ) else 0)*f h := by
      apply Finset.sum_congr rfl
      intro h hh
      simp [(Finset.mem_erase.mp hh).2]
    _=_ := Finset.sum_subset hsub (by
      intro h hh hn
      have hne := (Finset.mem_erase.mp hh).1
      have hout : h∉childFrequencyBall E R := fun hm=>hn (Finset.mem_erase.mpr ⟨hne,hm⟩)
      simp [hout])

variable (p : ι→O) (hp : ∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
  (hg : ∀i,lambda∉Ideal.span {p i})

def firstOriginalWeight (β : Ideal O→(ι→₀ℕ)→ℂ)
    (R : CubeCoordinates ι→Finset ι→Ideal O→Finset ι→ℝ)
    (k : FirstOriginalOuter ι) (x : Ideal O×O) : ℂ :=
  reopenedPairCoefficient β k.1 k.2.1 x.1 *
    supportMobius k.2.2 *
    (if x.2∈reopenedPhysicalCutoff p k.1 x.1 (R k.1 k.2.1 x.1) k.2.2 then 1 else 0)

omit [∀ (i : ι), (Ideal.span {p i}).IsMaximal] in
lemma firstOriginalWeight_norm_le (β : Ideal O→(ι→₀ℕ)→ℂ)
    (R : CubeCoordinates ι→Finset ι→Ideal O→Finset ι→ℝ)
    (k : FirstOriginalOuter ι) (x : Ideal O×O) :
    ‖firstOriginalWeight p β R k x‖≤‖reopenedPairCoefficient β k.1 k.2.1 x.1‖ := by
  unfold firstOriginalWeight
  split_ifs
  · simp only [mul_one,norm_mul]
    exact mul_le_of_le_one_right (norm_nonneg _)
      (supportMobius_norm k.2.2).le
  · simp

theorem original_retained_global_index
    (pool : Finset ι) (Q : Finset (ι→₀ℕ)) (labels : Finset (Ideal O)) (hlabels : ∀I∈labels,I≠0)
    (β : Ideal O→(ι→₀ℕ)→ℂ) (Ψ : O→*ℂ) (m : O)
    (mark : (ι→₀ℕ)→Finset ι→ℂ) (W : ℝ→ℂ) (Φ : 𝓢(ℝ,ℂ)) (K Y : ℝ)
    (R : CubeCoordinates ι→Finset ι→Ideal O→Finset ι→ℝ)
    (hRY : ∀k∈firstOriginalOuter pool Q,∀f∈labels,R k.1 k.2.1 f k.2.2≤ Y) :
    reopenedPhysicalSourceSum pool Q labels β (fun b C I=>
      reopenedPhysicalRetained p hp hg pool b C Ψ m I mark W Φ K (R b C I)) =
    ∑x∈firstGlobalRetainedSource p (firstOriginalOuter pool Q) (fun _=>labels) (fun k=>k.1) Y,
      firstOriginalWeight p β R x.1 x.2 *
      canonicalCubeOuter p hg x.1.1 x.1.2.1 Ψ Ψ m m (cubicIdealGenerator x.2.1)*
      firstCubePhysicalMode p hp hg pool x.1.1 x.1.2.1 Ψ Ψ m m
        (cubicIdealGenerator x.2.1) (mark x.1.1.rightExponent) (mark x.1.1.leftExponent)
        W W Φ K ((∏ i ∈ x.1.2.2,p i)) x.2.2 := by
  simp only [firstGlobalRetainedSource,firstOriginalOuter,Finset.sum_sigma,sum_firstRetainedSource]
  unfold reopenedPhysicalSourceSum reopenedPhysicalRetained
  apply Finset.sum_congr rfl
  intro b hb
  apply Finset.sum_congr rfl
  intro C hC
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro D hD
  apply Finset.sum_congr rfl
  intro f hf
  have hE := firstPhysicalMultiplier_ne_zero p hp b.support b.leftExponent b.rightExponent
    b.leftBit b.rightBit f (hlabels f hf)
  have hRY' := hRY ⟨b,⟨C,D⟩⟩ ((mem_firstOriginalOuter pool Q _).mpr ⟨hb,hC,hD⟩) f hf
  rw [show reopenedPhysicalCutoff p b f (R b C f) D=
    childFrequencyBall (firstPhysicalMultiplier p b.support b.leftExponent b.rightExponent b.leftBit b.rightBit f) (R b C f D) from rfl]
  rw [retained_cutoff_enlargement _ hE _ Y hRY']
  apply Finset.sum_congr rfl
  intro h hh
  simp only [firstOriginalWeight,reopenedPhysicalCutoff]
  ac_rfl

end
end InverseMoment

namespace InverseMoment
noncomputable section
open Eisenstein SchwartzPlanePoisson SecondPassArithmetic
open InverseFirstRayAttachment
open scoped BigOperators Classical SchwartzMap
open InverseInitialRayAttachment Eisenstein SchwartzPlanePoisson FirstPassCubeLabels SecondPassArithmetic
open Eisenstein (ringComplex)
open InverseFirstRayAttachment
local notation "O" => Eisenstein.O
variable {ι : Type*} [DecidableEq ι]
  (p : ι→O) (hp : ∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
  (hg : ∀i,lambda∉Ideal.span {p i})

theorem firstCubePhysicalMode_fixed_pool (pool : Finset ι) (b : CubeCoordinates ι) (C : Finset ι)
    (Ψ₁ Ψ₂ : O→*ℂ) (m₁ m₂ d : O) (H₁ H₂ : Finset ι→ℂ)
    (W₁ W₂ : ℝ→ℂ) (Φ : 𝓢(ℝ,ℂ)) (K : ℝ) (x : Ideal O×O) :
    firstCubePhysicalMode p hp hg pool b C Ψ₁ Ψ₂ m₁ m₂
      (cubicIdealGenerator x.1) H₁ H₂ W₁ W₂ Φ K d x.2=
    (K:ℂ)*cubeBaseFactor p hp hg b.support (fun i=>b.leftExponent i+b.rightExponent i) b.leftBit b.rightBit d x.2 *
      firstPhysicalCommonRows p hg pool
        (firstCanonicalCoefficient p hg b C true Ψ₁ m₁ d H₁ x)
        (firstCanonicalCoefficient p hg b C false Ψ₂ m₂ d H₂ x)
        (fun y=>star (W₁ y)) W₂ Φ
        (‖ringComplex (aLabel p b.support b.rightBit)‖^2)
        (‖ringComplex (aLabel p b.support b.leftBit)‖^2)
        (primeProductNorm p C)
        (primeProductNorm p (cubeActiveSupport b.support (fun i=>b.leftExponent i+b.rightExponent i) b.leftBit b.rightBit)) K d x.2 := by
  change _*firstPhysicalCommonRows p hg (pool\(b.support∪C))
      (firstCanonicalCoefficient p hg b C true Ψ₁ m₁ d H₁ x)
      (firstCanonicalCoefficient p hg b C false Ψ₂ m₂ d H₂ x) _ _ _ _ _ _ _ _ _ _ = _
  apply congrArg (fun z : ℂ =>
    (K : ℂ) * cubeBaseFactor p hp hg b.support
      (fun i => b.leftExponent i + b.rightExponent i) b.leftBit b.rightBit d x.2 * z)
  apply firstPhysicalCommonRows_fixed_pool p hg _ pool Finset.sdiff_subset
  · intro U hU hn
    apply firstCanonicalCoefficient_zero_overlap p hg
    intro hd
    apply hn
    intro i hi
    exact Finset.mem_sdiff.mpr ⟨hU hi,fun he=>Finset.disjoint_left.mp hd hi he⟩
  · intro U hU hn
    apply firstCanonicalCoefficient_zero_overlap p hg
    intro hd
    apply hn
    intro i hi
    exact Finset.mem_sdiff.mpr ⟨hU hi,fun he=>Finset.disjoint_left.mp hd hi he⟩

theorem original_retained_global_family
    (pool : Finset ι) (Q : Finset (ι→₀ℕ)) (labels : Finset (Ideal O)) (hlabels : ∀I∈labels,I≠0)
    (β : Ideal O→(ι→₀ℕ)→ℂ) (Ψ : O→*ℂ) (m : O)
    (mark : (ι→₀ℕ)→Finset ι→ℂ) (W : ℝ→ℂ) (Φ : 𝓢(ℝ,ℂ)) (K Y : ℝ)
    (R : CubeCoordinates ι→Finset ι→Ideal O→Finset ι→ℝ)
    (hRY : ∀k∈firstOriginalOuter pool Q,∀f∈labels,R k.1 k.2.1 f k.2.2≤ Y)
    (s : Fin 9→ℝ) (hs : ∀i,0<s i) :
    reopenedPhysicalSourceSum pool Q labels β (fun b C I=>
      reopenedPhysicalRetained p hp hg pool b C Ψ m I mark W Φ K (R b C I)) =
    (K:ℂ)*firstFamilyPhysicalRows p hg
      (firstGlobalRetainedSource p (firstOriginalOuter pool Q) (fun _=>labels) (fun k=>k.1) Y) pool
      (fun _ _=>1)
      (fun x=>firstCanonicalCoefficient p hg x.1.1 x.1.2.1 true Ψ m
        ((∏ i ∈ x.1.2.2,p i)) (mark x.1.1.rightExponent) x.2)
      (fun x=>firstCanonicalCoefficient p hg x.1.1 x.1.2.1 false Ψ m
        ((∏ i ∈ x.1.2.2,p i)) (mark x.1.1.leftExponent) x.2)
      (fun x=>retainedCubeWeight p hp hg x.1.1 x.1.2.1 Ψ Ψ m m
        ((∏ i ∈ x.1.2.2,p i)) (firstOriginalWeight p β R x.1) x.2)
      (fun y=>star (W ((s 0*s 2*s 5*s 7)*y))) (fun y=>W ((s 1*s 2*s 5*s 8)*y)) Φ
      (fun x=>‖ringComplex (aLabel p x.1.1.support x.1.1.rightBit)‖^2)
      (fun x=>‖ringComplex (aLabel p x.1.1.support x.1.1.leftBit)‖^2)
      (fun x=>primeProductNorm p x.1.2.1)
      (fun x=>primeProductNorm p (cubeActiveSupport x.1.1.support
        (fun i=>x.1.1.leftExponent i+x.1.1.rightExponent i) x.1.1.leftBit x.1.1.rightBit)) K
      (fun x=>(∏ i ∈ x.1.2.2,p i)) (fun x=>x.2.2) s := by
  rw [original_retained_global_index p hp hg pool Q labels hlabels β Ψ m mark W Φ K Y R hRY]
  have hleft : s 0*s 2*s 5*s 7≠0 := mul_ne_zero (mul_ne_zero (mul_ne_zero (ne_of_gt (hs 0)) (ne_of_gt (hs 2))) (ne_of_gt (hs 5))) (ne_of_gt (hs 7))
  have hright : s 1*s 2*s 5*s 8≠0 := mul_ne_zero (mul_ne_zero (mul_ne_zero (ne_of_gt (hs 1)) (ne_of_gt (hs 2))) (ne_of_gt (hs 5))) (ne_of_gt (hs 8))
  have hw₁ : (fun y=>star (W ((s 0*s 2*s 5*s 7)*(y/(s 0*s 2*s 5*s 7)))))=fun y=>star (W y) := by
    funext y
    rw [mul_div_cancel₀ _ hleft]
  have hw₂ : (fun y=>W ((s 1*s 2*s 5*s 8)*(y/(s 1*s 2*s 5*s 8))))=W := by
    funext y
    rw [mul_div_cancel₀ _ hright]
  simp only [firstFamilyPhysicalRows,Finset.mul_sum,hw₁,hw₂]
  apply Finset.sum_congr rfl
  intro x hx
  rw [first_unblocked_physical,firstCubePhysicalMode_fixed_pool p hp hg]
  unfold retainedCubeWeight
  ring

end
end InverseMoment

namespace InverseMoment
noncomputable section
open Eisenstein SchwartzPlanePoisson SecondPassArithmetic
open InverseFirstRayAttachment
open scoped BigOperators Classical SchwartzMap
open InverseInitialRayAttachment Eisenstein SchwartzPlanePoisson FirstPassCubeLabels SecondPassArithmetic
open Eisenstein (ringComplex)

open InverseFirstRayAttachment
local notation "O" => Eisenstein.O
variable {ι : Type*} [DecidableEq ι]
  (p : ι→O) (hp : ∀ i,p i≠0) [∀ i,(Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
  (hg : ∀ i,lambda∉Ideal.span {p i})

theorem rowFamilyEnergy_le_of_full_split (labels : Finset (Ideal O))
    (P : Ideal O→O→ℂ) (K : ℝ) (hK : 0<K) (A B C : ℂ)
    (he : (∑ I∈labels,∑' z:O,rowMajorant (‖ringComplex z‖^2/K)*(‖P I z‖^2:ℝ))=A+B+C) :
    CanonicalRowCompletion.rowFamilyEnergy labels P K ≤ ‖A‖+‖B‖+‖C‖ := by
  unfold CanonicalRowCompletion.rowFamilyEnergy
  simp only [nonzeroRowMajorantSum_eq_sub _ K hK,Finset.sum_sub_distrib,Complex.sub_re]
  rw [he]
  have hn : 0≤(∑ I∈labels,((‖P I 0‖^2:ℝ):ℂ)).re := by
    simp only [Complex.re_sum,Complex.ofReal_re]
    exact Finset.sum_nonneg (fun I hI=>sq_nonneg _)
  simp only [Complex.add_re]
  linarith [Complex.re_le_norm A,Complex.re_le_norm B,Complex.re_le_norm C]

include hcop in
theorem original_reopened_physical_energy
    (hinj : Function.Injective (fun i=>Ideal.span {p i}))
    (hc : ∀ i,ringChar (O⧸Ideal.span {p i})≠2)
    (hpr : ∀ i,lambda^2∣p i-1)
    (pool : Finset ι) (Q : Finset (ι→₀ℕ)) (hQ : ∀ v∈Q,v.support⊆pool)
    (labels : Finset (Ideal O)) (hlabels : ∀ I∈labels,I≠0)
    (β : Ideal O→(ι→₀ℕ)→ℂ) (Ψ : O→*ℂ) (m : O)
    (mark : Ideal O→(ι→₀ℕ)→Finset ι→ℂ) (W : ℝ→ℂ)
    (K : ℝ) (hK : 0<K) (R : CubeCoordinates ι→Finset ι→Ideal O→Finset ι→ℝ)
    (hR : ∀ b∈reopenedCubeFamily Q,∀ C∈(pool\b.support).powerset,∀ I∈labels,∀ D,0≤ R b C I D) :
    CanonicalRowCompletion.rowFamilyEnergy labels (fun I z=>
      varyingReopenedRow p hg pool Q (β I) Ψ m (cubicIdealGenerator I)
        (fun v U=>mark I v U*W (primeProductNorm p U)) z) K ≤
    ‖reopenedPhysicalSourceSum pool Q labels β (fun b C I=>
      canonicalCubeDualZero p hp hg pool b C Ψ Ψ m m (cubicIdealGenerator I)
        (fun U=>mark I b.rightExponent U*W (primeProductNorm p U))
        (fun U=>mark I b.leftExponent U*W (primeProductNorm p U)) rowMajorant K)‖ +
    ‖reopenedPhysicalSourceSum pool Q labels β (fun b C I=>
      reopenedPhysicalRetained p hp hg pool b C Ψ m I (mark I) W rowMajorant K (R b C I))‖ +
    ‖reopenedPhysicalSourceSum pool Q labels β (fun b C I=>
      canonicalCubeDualTail p hp hg pool b C Ψ Ψ m m (cubicIdealGenerator I)
        (fun U=>mark I b.rightExponent U*W (primeProductNorm p U))
        (fun U=>mark I b.leftExponent U*W (primeProductNorm p U)) rowMajorant K
        (reopenedPhysicalCutoff p b I (R b C I)))‖ := by
  apply rowFamilyEnergy_le_of_full_split labels _ K hK
  exact original_reopened_physical_split p hp hcop hg hinj hc hpr pool Q hQ labels hlabels
    β Ψ m mark W rowMajorant K hK R hR

end
end InverseMoment

namespace InverseMoment
noncomputable section
open Eisenstein SchwartzPlanePoisson SecondPassArithmetic
open InverseFirstRayAttachment
open scoped BigOperators Classical SchwartzMap
open InverseInitialRayAttachment Eisenstein SchwartzPlanePoisson FirstPassCubeLabels SecondPassArithmetic
open Eisenstein (ringComplex)

open InverseFirstRayAttachment
local notation "O" => Eisenstein.O
variable {ι : Type*} [DecidableEq ι]
  (p : ι→O) (hp : ∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
  (hg : ∀i,lambda∉Ideal.span {p i})

def originalRetainedFamily
    (pool : Finset ι) (Q : Finset (ι→₀ℕ)) (labels : Finset (Ideal O))
    (β : Ideal O→(ι→₀ℕ)→ℂ) (Ψ : O→*ℂ) (m : O)
    (mark : (ι→₀ℕ)→Finset ι→ℂ) (W : ℝ→ℂ) (Φ : 𝓢(ℝ,ℂ)) (K Y : ℝ)
    (R : CubeCoordinates ι→Finset ι→Ideal O→Finset ι→ℝ) (s : Fin 9→ℝ) : ℂ :=
  firstFamilyPhysicalRows p hg
      (firstGlobalRetainedSource p (firstOriginalOuter pool Q) (fun _=>labels) (fun k=>k.1) Y) pool
      (fun _ _=>1)
      (fun x=>firstCanonicalCoefficient p hg x.1.1 x.1.2.1 true Ψ m
        ((∏ i ∈ x.1.2.2,p i)) (mark x.1.1.rightExponent) x.2)
      (fun x=>firstCanonicalCoefficient p hg x.1.1 x.1.2.1 false Ψ m
        ((∏ i ∈ x.1.2.2,p i)) (mark x.1.1.leftExponent) x.2)
      (fun x=>retainedCubeWeight p hp hg x.1.1 x.1.2.1 Ψ Ψ m m
        ((∏ i ∈ x.1.2.2,p i)) (firstOriginalWeight p β R x.1) x.2)
      (fun y=>star (W ((s 0*s 2*s 5*s 7)*y))) (fun y=>W ((s 1*s 2*s 5*s 8)*y)) Φ
      (fun x=>‖ringComplex (aLabel p x.1.1.support x.1.1.rightBit)‖^2)
      (fun x=>‖ringComplex (aLabel p x.1.1.support x.1.1.leftBit)‖^2)
      (fun x=>primeProductNorm p x.1.2.1)
      (fun x=>primeProductNorm p (cubeActiveSupport x.1.1.support
        (fun i=>x.1.1.leftExponent i+x.1.1.rightExponent i) x.1.1.leftBit x.1.1.rightBit)) K
      (fun x=>(∏ i ∈ x.1.2.2,p i)) (fun x=>x.2.2) s

include hcop in
theorem original_global_physical_energy
    (hinj : Function.Injective (fun i=>Ideal.span {p i}))
    (hc : ∀ i,ringChar (O⧸Ideal.span {p i})≠2)
    (hpr : ∀ i,lambda^2∣p i-1)
    (pool : Finset ι) (Q : Finset (ι→₀ℕ)) (hQ : ∀v∈Q,v.support⊆pool)
    (labels : Finset (Ideal O)) (hlabels : ∀I∈labels,I≠0)
    (β : Ideal O→(ι→₀ℕ)→ℂ) (Ψ : O→*ℂ) (m : O)
    (mark : (ι→₀ℕ)→Finset ι→ℂ) (W : ℝ→ℂ) (K Y : ℝ) (hK : 0<K)
    (R : CubeCoordinates ι→Finset ι→Ideal O→Finset ι→ℝ)
    (hR : ∀ b∈reopenedCubeFamily Q,∀ C∈(pool\b.support).powerset,∀ I∈labels,∀ D,0≤ R b C I D)
    (hRY : ∀k∈firstOriginalOuter pool Q,∀f∈labels,R k.1 k.2.1 f k.2.2≤ Y)
    (s : Fin 9→ℝ) (hs : ∀i,0<s i) :
    CanonicalRowCompletion.rowFamilyEnergy labels (fun I z=>
      varyingReopenedRow p hg pool Q (β I) Ψ m (cubicIdealGenerator I)
        (fun v U=>mark v U*W (primeProductNorm p U)) z) K ≤
    ‖reopenedPhysicalSourceSum pool Q labels β (fun b C I=>
      canonicalCubeDualZero p hp hg pool b C Ψ Ψ m m (cubicIdealGenerator I)
        (fun U=>mark b.rightExponent U*W (primeProductNorm p U))
        (fun U=>mark b.leftExponent U*W (primeProductNorm p U)) rowMajorant K)‖ +
    K*‖originalRetainedFamily p hp hg pool Q labels β Ψ m mark W rowMajorant K Y R s‖ +
    ‖reopenedPhysicalSourceSum pool Q labels β (fun b C I=>
      canonicalCubeDualTail p hp hg pool b C Ψ Ψ m m (cubicIdealGenerator I)
        (fun U=>mark b.rightExponent U*W (primeProductNorm p U))
        (fun U=>mark b.leftExponent U*W (primeProductNorm p U)) rowMajorant K
        (reopenedPhysicalCutoff p b I (R b C I)))‖ := by
  have he := original_reopened_physical_energy p hp hcop hg hinj hc hpr pool Q hQ labels hlabels
    β Ψ m (fun _=>mark) W K hK R hR
  rw [original_retained_global_family p hp hg pool Q labels hlabels β Ψ m mark W rowMajorant K Y R hRY s hs] at he
  simpa only [originalRetainedFamily,norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hK] using he

end
end InverseMoment

namespace InverseMoment
open scoped BigOperators Classical SchwartzMap
open InverseInitialRayAttachment Eisenstein SchwartzPlanePoisson FirstPassCubeLabels SecondPassArithmetic RayFourExpansion
noncomputable section
open Eisenstein SchwartzPlanePoisson SecondPassArithmetic
open InverseFirstRayAttachment
open InverseInitialRayAttachment InverseFirstRayAttachment
local notation "O" => Eisenstein.O
variable {ι σ : Type*} [DecidableEq ι] [DecidableEq σ]
  (p : ι→O) (hp : ∀ i,p i≠0) [∀ i,(Ideal.span {p i}).IsMaximal]
  (hg : ∀ i,lambda∉Ideal.span {p i})

def firstWholePrioritySecondEnergy (hinj : Function.Injective (fun i=>Ideal.span {p i}))
    (F : Finset ι) (b : CubeCoordinates ι) (C extra : Finset ι) (negative : Bool)
    (Ψ : O→*ℂ) (m d : O) (slots : Finset σ) (lists : σ→Finset ι) (a : σ→ι→ℂ)
    (selector : Finset ι→ℂ) (omega : ℝ→ℂ) (X t Y : ℝ) : ℝ :=
  let A := extra∪((if negative then b.rightDivisor else b.leftDivisor)∪C)
  firstCoreMassBound*(2:ℝ)^slots.card * ∑ r : RayCharacter×RayCharacter,∑ D∈F.powerset,
    (‖crossCoeff r.1 r.2‖*‖selector D‖)*∑ core : FirstCoreIndex,
      ‖firstCoreOuter p hg b.support (fun i=>b.leftExponent i+b.rightExponent i) b.leftBit b.rightBit negative Ψ m D core‖ *
      ∑ J∈slots.powerset,‖primeMark J lists a (A∪D)‖^2 *
        (firstFreshSecondPoisson p hp hg hinj F D b.support (fun i=>b.leftExponent i+b.rightExponent i)
          b.leftBit b.rightBit negative (if negative then r.1 else r.2) Ψ m
          (fun U=>primeMark (slots\J) (fun i=>lists i\(A∪D)) a U)
          omega X (∏i∈C,p i) d core t Y).re

theorem first_actual_second_whole_cube_priority
    (hinj : Function.Injective (fun i=>Ideal.span {p i}))
    (hc : ∀ i,ringChar (O⧸Ideal.span {p i})≠2)
    (F : Finset ι) (b : CubeCoordinates ι) (C extra : Finset ι) (negative : Bool)
    (Ψ : O→*ℂ) (m d : O) (slots : Finset σ) (lists : σ→Finset ι) (a : σ→ι→ℂ)
    (selector : Finset ι→ℂ) (omega : ℝ→ℂ) (X t Y : ℝ) (hY : 0<Y) :
    firstCanonicalSecondEnergy p hp hg hinj F b C negative Ψ m d
      (fun U=>primeMark slots lists a (extra∪U)) selector omega X t Y ≤
    firstWholePrioritySecondEnergy p hp hg hinj F b C extra negative Ψ m d slots lists a selector omega X t Y := by
  let A := extra∪((if negative then b.rightDivisor else b.leftDivisor)∪C)
  have hb (r : RayCharacter×RayCharacter) (D : Finset ι) (core : FirstCoreIndex) :=
    first_fresh_priority_energy p hp hg hinj hc F D b.support A
      (fun i=>b.leftExponent i+b.rightExponent i) b.leftBit b.rightBit negative
      (if negative then r.1 else r.2) Ψ m slots lists a (fun _=>1)
      omega X (∏i∈C,p i) d core t Y hY
  simp only [mul_one] at hb
  unfold firstCanonicalSecondEnergy firstWholePrioritySecondEnergy
  simp only [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro r hr
  apply Finset.sum_le_sum
  intro D hD
  apply Finset.sum_le_sum
  intro core hcore
  have h := mul_le_mul_of_nonneg_left (hb r D core)
    (show 0≤firstCoreMassBound*(‖crossCoeff r.1 r.2‖*‖selector D‖)*
      ‖firstCoreOuter p hg b.support (fun i=>b.leftExponent i+b.rightExponent i)
        b.leftBit b.rightBit negative Ψ m D core‖ from mul_nonneg (mul_nonneg firstCoreMassBound_nonneg (mul_nonneg (norm_nonneg _) (norm_nonneg _))) (norm_nonneg _))
  convert h using 1
  · dsimp only [A]
    simp only [Finset.union_assoc]
    ring
  · simp only [A,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro J hJ
    ring

end
end InverseMoment

end GaloisForLFunctions.MetaplecticMobiusDescent.CubicEisenstein
