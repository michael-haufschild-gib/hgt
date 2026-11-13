/-
The first amplification choice adapted from OpenAI's formalization, Apache-2.0.
See LICENSE and NOTICE in the parent directory for source attribution.
-/
import GaloisForLFunctions.MetaplecticMobiusDescent.Moments.FirstPhysicalSources

/-!
# The first amplification choice

Original data, error removal and moving parts of the first amplification choice; child inputs
and ball profiles; zero-radius physical masses and source partition counts.
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

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter

namespace CenteredMomentFirstSourceReduction
open HeckeFamily CanonicalQuadraticSieve CenteredMomentCommonRadialData
open CenteredMomentOriginalCommonHarmonic CenteredMomentSourceMass CenteredMomentSourceRow
open CenteredMomentExceptionalAmplitudePair CenteredMomentSourceInputTailUniform
open CenteredMomentSourceInputFirstRemainder CenteredMomentFirstRetainedNorm
open CenteredMomentFirstSectorTransform CenteredMomentFirstSectors CenteredMomentFirstEnergy
open CenteredMomentActiveSource (activeSource)
local notation "O"=> Eisenstein.O
variable {ι:Type*}[Fintype ι][DecidableEq ι]
local instance : DecidableEq (ι⊕Fin 2):=Classical.decEq _

def physicalMass (s:Input ι)(R seed:Ideal O)(m A:O)(Φ:𝓢(ℝ,ℂ))(K Z ξ:ℝ):ℝ:=
  let β:=coefficient s R seed
  let T:=activeSource (finiteColumns (Fintype.piFinset s.pools)) β
  ∑p:commonLabels (supportedColumns T) (supportedColumns T),
    sectorMass s R seed m A s.t T p.val.1 p.val.2
      (commonLabels_supported T p).1 (commonLabels_supported T p).2 Φ K
      (volume s.toData) Z ξ

 theorem original_first_physical_reduction (hi:ι→ℝ)(wlo whi B ε ξ saving:ℝ)
    (hhi:∀i,0≤ hi i)(hwlo:0< wlo)(hwhi:0≤ whi)(hB:0≤ B)(hε:0<ε)(hξ:0<ξ):
    ∃Sdiag Stail:Finset (ℕ×ℕ),∃Cdiag Ctail:ℝ,0< Cdiag ∧ 0< Ctail ∧
      ∀ᶠZ:ℝ in atTop,1< Z ∧ ∀(s:Input ι)(W₁ W₂:𝓢(ℝ,ℂ)),
      s.W₁=W₁→s.W₂=W₂→Function.support (W₁:ℝ→ℂ)⊆Set.Icc wlo whi→
      Function.support (W₂:ℝ→ℂ)⊆Set.Icc wlo whi→(∀i,s.hi i≤ hi i)→
      ∀(m A:O),lambda∣m→(2:O)∣m→
      ∀(R seed:Ideal O)(Φ:𝓢(ℝ,ℂ))(K:ℝ),0< K→
      volume s.toData≤ Z^B→K⁻¹≤ Z^B→
      ‖finiteHeckeEnergy s.η m A s.t (finiteColumns (Fintype.piFinset s.pools))
          (coefficient s R seed) Φ K‖/volume s.toData≤
      physicalMass s R seed m A Φ K Z ξ/volume s.toData+
      Cdiag*(plainControl s W₁ W₂)^2*Sdiag.sup (schwartzSeminormFamily ℝ ℝ ℂ) Φ*K*Z^ε+
      Ctail*(plainControl s W₁ W₂)^2*Stail.sup (schwartzSeminormFamily ℝ ℝ ℂ) Φ*K*Z^(-saving):=by
  obtain ⟨Sdiag,Stail,Cdiag,Ctail,hCdiag,hCtail,hrem⟩:=
    original_first_remainder hi wlo whi B ε ξ saving hhi hwlo hwhi hB hε hξ
  refine ⟨Sdiag,Stail,Cdiag,Ctail,hCdiag,hCtail,?_⟩
  filter_upwards [hrem] with Z hZ
  refine ⟨hZ.1,?_⟩
  intro s W₁ W₂ he₁ he₂ hs₁ hs₂ hshi m A hml hm2 R seed Φ K hK hVcap hKi
  have hz (W:𝓢(ℝ,ℂ))(hs:Function.support (W:ℝ→ℂ)⊆Set.Icc wlo whi):W 0=0:=by
    by_contra hn
    exact (not_le_of_gt hwlo) (hs hn).1
  have hr:=original_retained_norm s R seed (he₁.symm ▸ hz W₁ hs₁) (he₂.symm ▸ hz W₂ hs₂)
    m A s.t (finiteColumns (Fintype.piFinset s.pools)) Φ K (volume s.toData) Z ξ hK
  change ‖CenteredMomentFirstSectorLocalization.retainedEnergy s.η m A s.t
    (finiteColumns (Fintype.piFinset s.pools)) (coefficient s R seed) Φ K
      (volume s.toData) Z ξ‖≤ physicalMass s R seed m A Φ K Z ξ at hr
  have he:=hZ.2 s W₁ W₂ he₁ he₂ hs₁ hs₂ hshi m A hml hm2 R seed Φ K hK hVcap hKi
  have htri:=norm_le_norm_sub_add
    (finiteHeckeEnergy s.η m A s.t (finiteColumns (Fintype.piFinset s.pools)) (coefficient s R seed) Φ K)
    (CenteredMomentFirstSectorLocalization.retainedEnergy s.η m A s.t
      (finiteColumns (Fintype.piFinset s.pools)) (coefficient s R seed) Φ K (volume s.toData) Z ξ)
  have hdiv:=div_le_div_of_nonneg_right htri (volume_pos s).le
  rw [add_div] at hdiv
  have hrdiv:=div_le_div_of_nonneg_right hr (volume_pos s).le
  linarith

end CenteredMomentFirstSourceReduction

end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson
namespace CenteredMomentFirstAmplifiedFourCoefficients
def lossVector (sigma delta reserve paid eps Mcap saving:ℝ):Fin 4→ℝ:=
  ![paid,3*sigma/2+5*(delta+reserve)/6,
    2*sigma+delta+reserve+eps*Mcap,2*sigma+delta+reserve-saving]


end CenteredMomentFirstAmplifiedFourCoefficients

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped BigOperators Classical SchwartzMap
namespace CenteredMomentChildEnergy
open CanonicalQuadraticSieve CenteredMomentGaussEnergy CenteredMomentCauchy
open CenteredMomentSmooth
local notation "O" => Eisenstein.O

theorem leftColumn_eq_gaussPolynomial {α : Type*} (S : Finset α) (a : α → O)
    (ha : ∀ i, Supported (Ideal.span {a i})) (c : α → ℂ)
    (V : ℝ → ℂ) (u : α → ℝ) (z : O) (t : ℝ) :
    leftColumn S (fun i => c i * gaussRow (a i) (ha i) z) V u t =
      gaussPolynomial S a ha (fun i => c i * columnPhase V (u i) t) z := by
  unfold leftColumn gaussPolynomial
  apply Finset.sum_congr rfl
  intro i hi
  ring

theorem rightColumn_eq_star_gaussPolynomial {α : Type*} (S : Finset α) (a : α → O)
    (ha : ∀ i, Supported (Ideal.span {a i})) (c : α → ℂ)
    (V : ℝ → ℂ) (u : α → ℝ) (z : O) (t : ℝ) :
    rightColumn S (fun i => c i * gaussRow (a i) (ha i) z) V u t =
      star (gaussPolynomial S a ha (fun i => c i * star (columnPhase V (u i) t)) z) := by
  simp only [rightColumn, gaussPolynomial, star_sum, star_mul, star_star]
  apply Finset.sum_congr rfl
  intro i hi
  ring

theorem whole_kernel_gauss_child_bound (W : 𝓢(ℝ, ℂ)) (V : Fin 4 → ℝ → ℂ)
    (M : Fin 4 → ℝ) (hM : ∀ i, 0 ≤ M i)
    (hV : ∀ i y, V i y ≠ 0 → |y| ≤ M i) (A J₁ J₂ : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ R : ℝ, 0 < R →
      ∀ {α β : Type*} (rows : Finset O) (S : Finset α) (T : Finset β)
        (a : α → O) (b : β → O)
        (ha : ∀ i, Supported (Ideal.span {a i}))
        (hb : ∀ j, Supported (Ideal.span {b j}))
        (c : α → ℂ) (d : β → ℂ) (u : α → ℝ) (v : β → ℝ)
        (ρ x : O → ℝ) (η : O → ℂ),
      (∀ z ∈ rows, ‖η z‖ ≤ 1) →
      (∀ z ∈ rows, ‖V 0 (ρ z)‖ ≤ 1) → (∀ z ∈ rows, ‖V 1 (x z)‖ ≤ 1) →
      ∀ (U : 𝓢(ℝ, ℂ)) (K : ℝ), 0 < K →
      (∀ z : O, 0 ≤ (U (‖ringComplex z‖ ^ 2 / K)).re) →
      (∀ z ∈ rows, 1 ≤ (U (‖ringComplex z‖ ^ 2 / K)).re) →
      ∀ E₁ E₂ : ℝ, 0 ≤ E₁ → 0 ≤ E₂ →
      (∀ t : ℝ, (gaussEnergy S a ha (fun i => c i * columnPhase (V 2) (u i) t) U K).re ≤
        (E₁ * (1 + ‖t‖) ^ J₁) ^ 2) →
      (∀ t : ℝ, (gaussEnergy T b hb (fun j => d j * star (columnPhase (V 3) (v j) t)) U K).re ≤
        (E₂ * (1 + ‖t‖) ^ J₂) ^ 2) →
      (1 + R) ^ A * ‖∑ z ∈ rows, η z *
        (∑ i ∈ S, ∑ j ∈ T,
          ((c i * gaussRow (a i) (ha i) z) * star (d j * gaussRow (b j) (hb j) z)) *
            wholeKernel W V R (ρ z) (x z) (u i) (v j))‖ ≤ C * (E₁ * E₂) := by
  obtain ⟨C, hC, hbound⟩ := whole_kernel_row_estimate W V M hM hV A (J₁ + J₂)
  refine ⟨C, hC, ?_⟩
  intro R hR α β rows S T a b ha hb c d u v ρ x η hη hV₀ hV₁ U K hK hU hmajor
    E₁ E₂ hE₁ hE₂ hleft hright
  apply hbound R hR rows S T
    (fun z i => c i * gaussRow (a i) (ha i) z)
    (fun z j => d j * gaussRow (b j) (hb j) z) u v ρ x η hη hV₀ hV₁
    (E₁ * E₂) (mul_nonneg hE₁ hE₂)
  intro t
  have hL := (finite_energy_le_gaussEnergy S a ha
    (fun i => c i * columnPhase (V 2) (u i) t) U K hK rows hU hmajor).trans (hleft t)
  have hR' := (finite_energy_le_gaussEnergy T b hb
    (fun j => d j * star (columnPhase (V 3) (v j) t)) U K hK rows hU hmajor).trans (hright t)
  have hl : Real.sqrt (∑ z ∈ rows,
      ‖gaussPolynomial S a ha (fun i => c i * columnPhase (V 2) (u i) t) z‖ ^ 2) ≤
      E₁ * (1 + ‖t‖) ^ J₁ := (Real.sqrt_le_iff).mpr ⟨by positivity, hL⟩
  have hr : Real.sqrt (∑ z ∈ rows,
      ‖gaussPolynomial T b hb (fun j => d j * star (columnPhase (V 3) (v j) t)) z‖ ^ 2) ≤
      E₂ * (1 + ‖t‖) ^ J₂ := (Real.sqrt_le_iff).mpr ⟨by positivity, hR'⟩
  simp only [leftColumn_eq_gaussPolynomial, rightColumn_eq_star_gaussPolynomial, norm_star]
  calc
    _ ≤ (E₁ * (1 + ‖t‖) ^ J₁) * (E₂ * (1 + ‖t‖) ^ J₂) :=
      mul_le_mul hl hr (Real.sqrt_nonneg _) (by positivity)
    _ = _ := by rw [pow_add]; ring

end CenteredMomentChildEnergy

end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped BigOperators Classical SchwartzMap
namespace CenteredMomentReflectedChild
open CanonicalQuadraticSieve CenteredMomentGaussEnergy CenteredMomentCauchy
open CenteredMomentSmooth CenteredMomentChildEnergy
local notation "O" => Eisenstein.O

theorem finite_reflected_energy_le_gaussEnergy {α : Type*} (S : Finset α) (a : α → O)
    (ha : ∀ i, Supported (Ideal.span {a i})) (c : α → ℂ)
    (W : 𝓢(ℝ, ℂ)) (K : ℝ) (hK : 0 < K) (rows : Finset O)
    (hW : ∀ z : O, 0 ≤ (W (‖ringComplex z‖ ^ 2 / K)).re)
    (hmajor : ∀ z ∈ rows, 1 ≤ (W (‖ringComplex z‖ ^ 2 / K)).re) :
    (∑ z ∈ rows, ‖gaussPolynomial S a ha c (-z)‖ ^ 2) ≤
      (gaussEnergy S a ha c W K).re := by
  have hh := finite_energy_le_gaussEnergy S a ha c W K hK (rows.image Neg.neg) hW
    (by intro z hz;obtain ⟨w,hw,rfl⟩ := Finset.mem_image.mp hz
        simpa only [map_neg,norm_neg] using hmajor w hw)
  rw [Finset.sum_image] at hh
  · exact hh
  · intro x hx y hy hxy
    exact neg_injective hxy

theorem whole_kernel_reflected_gauss_child_bound (W : 𝓢(ℝ, ℂ)) (V : Fin 4 → ℝ → ℂ)
    (M : Fin 4 → ℝ) (hM : ∀ i, 0 ≤ M i)
    (hV : ∀ i y, V i y ≠ 0 → |y| ≤ M i) (A J₁ J₂ : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ R : ℝ, 0 < R →
      ∀ {α β : Type*} (rows : Finset O) (S : Finset α) (T : Finset β)
        (a : α → O) (b : β → O)
        (ha : ∀ i, Supported (Ideal.span {a i}))
        (hb : ∀ j, Supported (Ideal.span {b j}))
        (c : α → ℂ) (d : β → ℂ) (u : α → ℝ) (v : β → ℝ)
        (ρ x : O → ℝ) (η : O → ℂ),
      (∀ z ∈ rows, ‖η z‖ ≤ 1) →
      (∀ z ∈ rows, ‖V 0 (ρ z)‖ ≤ 1) → (∀ z ∈ rows, ‖V 1 (x z)‖ ≤ 1) →
      ∀ (U : 𝓢(ℝ, ℂ)) (K : ℝ), 0 < K →
      (∀ z : O, 0 ≤ (U (‖ringComplex z‖ ^ 2 / K)).re) →
      (∀ z ∈ rows, 1 ≤ (U (‖ringComplex z‖ ^ 2 / K)).re) →
      ∀ E₁ E₂ : ℝ, 0 ≤ E₁ → 0 ≤ E₂ →
      (∀ t : ℝ, (gaussEnergy S a ha (fun i => c i * columnPhase (V 2) (u i) t) U K).re ≤
        (E₁ * (1 + ‖t‖) ^ J₁) ^ 2) →
      (∀ t : ℝ, (gaussEnergy T b hb (fun j => d j * star (columnPhase (V 3) (v j) t)) U K).re ≤
        (E₂ * (1 + ‖t‖) ^ J₂) ^ 2) →
      (1 + R) ^ A * ‖∑ z ∈ rows, η z *
        (∑ i ∈ S, ∑ j ∈ T,
          ((c i * gaussRow (a i) (ha i) z) * star (d j * gaussRow (b j) (hb j) (-z))) *
            wholeKernel W V R (ρ z) (x z) (u i) (v j))‖ ≤ C * (E₁ * E₂) := by
  obtain ⟨C, hC, hbound⟩ := whole_kernel_row_estimate W V M hM hV A (J₁ + J₂)
  refine ⟨C, hC, ?_⟩
  intro R hR α β rows S T a b ha hb c d u v ρ x η hη hV₀ hV₁ U K hK hU hmajor
    E₁ E₂ hE₁ hE₂ hleft hright
  apply hbound R hR rows S T
    (fun z i => c i * gaussRow (a i) (ha i) z)
    (fun z j => d j * gaussRow (b j) (hb j) (-z)) u v ρ x η hη hV₀ hV₁
    (E₁ * E₂) (mul_nonneg hE₁ hE₂)
  intro t
  have hL := (finite_energy_le_gaussEnergy S a ha
    (fun i => c i * columnPhase (V 2) (u i) t) U K hK rows hU hmajor).trans (hleft t)
  have hR' := (finite_reflected_energy_le_gaussEnergy T b hb
    (fun j => d j * star (columnPhase (V 3) (v j) t)) U K hK rows hU hmajor).trans (hright t)
  have hl : Real.sqrt (∑ z ∈ rows,
      ‖gaussPolynomial S a ha (fun i => c i * columnPhase (V 2) (u i) t) z‖ ^ 2) ≤
      E₁ * (1 + ‖t‖) ^ J₁ := (Real.sqrt_le_iff).mpr ⟨by positivity, hL⟩
  have hr : Real.sqrt (∑ z ∈ rows,
      ‖gaussPolynomial T b hb (fun j => d j * star (columnPhase (V 3) (v j) t)) (-z)‖ ^ 2) ≤
      E₂ * (1 + ‖t‖) ^ J₂ := (Real.sqrt_le_iff).mpr ⟨by positivity, hR'⟩
  simp only [leftColumn_eq_gaussPolynomial, rightColumn_eq_star_gaussPolynomial, norm_star]
  calc
    _ ≤ (E₁ * (1 + ‖t‖) ^ J₁) * (E₂ * (1 + ‖t‖) ^ J₂) :=
      mul_le_mul hl hr (Real.sqrt_nonneg _) (by positivity)
    _ = _ := by rw [pow_add]; ring

end CenteredMomentReflectedChild

end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped BigOperators Classical SchwartzMap

namespace CenteredMomentFirstChildBound
open CanonicalQuadraticSieve CenteredMomentSupportedCorrelation CenteredMomentFirstAssembly
open CenteredMomentFirstColumns CenteredMomentGaussEnergy CenteredMomentReflectedChild
open CenteredMomentChildAssembly CenteredMomentMobiusRegroup CenteredMomentSmooth RayFourExpansion
local notation "O" => Eisenstein.O

private theorem weighted_norm_sum {α : Type*} (S : Finset α) (a f : α → ℂ)
    (r : ℝ) (hr : 0 ≤ r) (B : α → ℝ)
    (hB : ∀ i ∈ S, r*‖f i‖ ≤ B i) :
    r*‖∑ i ∈ S, a i*f i‖ ≤ ∑ i ∈ S, ‖a i‖*B i := by
  calc
    _ ≤ r*∑ i ∈ S, ‖a i*f i‖ := mul_le_mul_of_nonneg_left (norm_sum_le _ _) hr
    _ = ∑ i ∈ S, ‖a i‖*(r*‖f i‖) := by simp only [Finset.mul_sum,norm_mul]; congr 1; funext i; ring
    _ ≤ _ := Finset.sum_le_sum (fun i hi => mul_le_mul_of_nonneg_left (hB i hi) (norm_nonneg _))

theorem finite_first_ray_divisor_bound (L : Finset (Ideal O))
    (F : Ideal O → RayCharacter → RayCharacter → ℂ)
    (r C : ℝ) (hr : 0 ≤ r) (hC : 0 ≤ C) (B₁ B₂ : Ideal O → ℝ)
    (hB₁ : ∀ I ∈ L, 0 ≤ B₁ I) (hB₂ : ∀ I ∈ L, 0 ≤ B₂ I)
    (hF : ∀ I ∈ L, ∀ χ ξ, r*‖F I χ ξ‖ ≤ C*(B₁ I*B₂ I)) :
    r*‖∑ I ∈ L, (UniqueFactorizationMonoid.moebius I : ℂ)*
      ∑ χ : RayCharacter, ∑ ξ : RayCharacter, pairCoeff (firstPhaseTable) χ ξ * F I χ ξ‖ ≤
      (256*C)*∑ I ∈ L, ‖(UniqueFactorizationMonoid.moebius I : ℂ)‖*(B₁ I*B₂ I) := by
  have he (I : Ideal O) (hI : I ∈ L) :
      r*‖∑ χ : RayCharacter, ∑ ξ : RayCharacter,
        pairCoeff (firstPhaseTable) χ ξ*F I χ ξ‖ ≤ (256*C)*(B₁ I*B₂ I) := by
    calc
      _ ≤ ∑ χ : RayCharacter, ∑ ξ : RayCharacter,
          ‖pairCoeff (firstPhaseTable) χ ξ‖*(C*(B₁ I*B₂ I)) := by
        have h := weighted_norm_sum Finset.univ (fun _ : RayCharacter => (1 : ℂ))
          (fun χ => ∑ ξ : RayCharacter, pairCoeff (firstPhaseTable) χ ξ*F I χ ξ) r hr
          (fun χ => ∑ ξ : RayCharacter, ‖pairCoeff (firstPhaseTable) χ ξ‖*(C*(B₁ I*B₂ I)))
          (fun χ _ => weighted_norm_sum Finset.univ _ _ r hr _ (fun ξ _ => hF I hI χ ξ))
        simpa only [one_mul,norm_one] using h
      _ = (∑ χ : RayCharacter, ∑ ξ : RayCharacter, ‖pairCoeff (firstPhaseTable) χ ξ‖)*
          (C*(B₁ I*B₂ I)) := by simp only [Finset.sum_mul]
      _ ≤ _ := by
        have h := mul_le_mul_of_nonneg_right (firstPhaseTable_mass)
          (mul_nonneg hC (mul_nonneg (hB₁ I hI) (hB₂ I hI)))
        convert h using 1 <;> first | rfl | ring
  have h := weighted_norm_sum L (fun I => (UniqueFactorizationMonoid.moebius I : ℂ))
    (fun I => ∑ χ : RayCharacter, ∑ ξ : RayCharacter, pairCoeff (firstPhaseTable) χ ξ*F I χ ξ)
    r hr (fun I => (256*C)*(B₁ I*B₂ I)) he
  convert h using 1
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro I hI
  ring

theorem first_row_children {α β : Type*} (rows : Finset O) (S : Finset α) (T : Finset β)
    (a : α → O) (b : β → O)
    (ha : ∀ i,Supported (Ideal.span {a i})) (hb : ∀ j,Supported (Ideal.span {b j}))
    (hpa : ∀ i,lambda^2∣a i-1)
    (hpb : ∀ j,lambda^2∣b j-1)
    (c : α → ℂ) (d : β → ℂ) (e r : O) (ρ : O → ℂ)
    (hρ : ∀ x y,ρ (x*y)=ρ x*ρ y) (q : O → ℂ) (K : O → α → β → ℂ) :
    (∑ z∈rows,q z*∑ i∈S,∑ j∈T,
      ((if IsCoprime (a i) (b j) then originalPhase e r ρ (a i) (b j) else 0)*(c i*star (d j)))*
        (gaussRow (a i) (ha i) z*star (gaussRow (b j) (hb j) (-z)))*K z i j)=
      ∑ L∈divisorPool T (fun j => Ideal.span {b j}),
        (UniqueFactorizationMonoid.moebius L:ℂ)*
          ∑ χ : RayCharacter,∑ ξ : RayCharacter,pairCoeff firstPhaseTable χ ξ*
            ∑ z∈rows,(q z*ρ e)*∑ i∈S,∑ j∈T,
              ((divisorCoefficient L a (fun i => c i*leftCoefficient e r ρ (a i)) χ i*gaussRow (a i) (ha i) z)*
                star (divisorCoefficient L b (fun j => d j*rightCoefficient e r ρ (b j)) (ξ⁻¹) j*
                  gaussRow (b j) (hb j) (-z)))*K z i j := by
  simp_rw [finite_first_children S T a b ha hb hpa hpb c d e r ρ hρ]
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm (s:=rows)]
  apply Finset.sum_congr rfl
  intro L hL
  rw [Finset.sum_comm (s:=rows)]
  apply Finset.sum_congr rfl
  intro χ hχ
  rw [Finset.sum_comm (s:=rows)]
  apply Finset.sum_congr rfl
  intro ξ hξ
  apply Finset.sum_congr rfl
  intro z hz
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  ring

theorem whole_kernel_first_child_bound (W : 𝓢(ℝ,ℂ)) (V : Fin 4 → ℝ → ℂ)
    (M : Fin 4 → ℝ) (hM : ∀ i,0≤ M i)
    (hV : ∀ i y,V i y≠0 → |y|≤ M i) (A J₁ J₂ : ℕ) :
    ∃ C : ℝ,0≤ C ∧ ∀ R : ℝ,0< R →
      ∀ {α β : Type*} (rows : Finset O) (S : Finset α) (T : Finset β)
        (a : α → O) (b : β → O)
        (ha : ∀ i,Supported (Ideal.span {a i})) (hb : ∀ j,Supported (Ideal.span {b j})),
      (∀ i,lambda^2∣a i-1) →
      (∀ j,lambda^2∣b j-1) →
      ∀ (c : α → ℂ) (d : β → ℂ) (e r : O) (ρ : O → ℂ),
      (∀ x y,ρ (x*y)=ρ x*ρ y) → ‖ρ e‖≤1 →
      ∀ (q : O → ℂ) (u : α → ℝ) (v : β → ℝ) (ρ₀ x : O → ℝ),
      (∀ z∈rows,‖q z‖≤1) →
      (∀ z∈rows,‖V 0 (ρ₀ z)‖≤1) → (∀ z∈rows,‖V 1 (x z)‖≤1) →
      ∀ (U : 𝓢(ℝ,ℂ)) (K : ℝ),0< K →
      (∀ z : O,0≤(U (‖ringComplex z‖^2/K)).re) →
      (∀ z∈rows,1≤(U (‖ringComplex z‖^2/K)).re) →
      ∀ (B₁ B₂ : Ideal O → ℝ),
      (∀ L∈divisorPool T (fun j => Ideal.span {b j}),0≤ B₁ L) →
      (∀ L∈divisorPool T (fun j => Ideal.span {b j}),0≤ B₂ L) →
      (∀ L∈divisorPool T (fun j => Ideal.span {b j}),∀ χ : RayCharacter,∀ t : ℝ,
        (gaussEnergy S a ha (fun i =>
          divisorCoefficient L a (fun i => c i*leftCoefficient e r ρ (a i)) χ i*
            columnPhase (V 2) (u i) t) U K).re≤(B₁ L*(1+‖t‖)^J₁)^2) →
      (∀ L∈divisorPool T (fun j => Ideal.span {b j}),∀ ξ : RayCharacter,∀ t : ℝ,
        (gaussEnergy T b hb (fun j =>
          divisorCoefficient L b (fun j => d j*rightCoefficient e r ρ (b j)) ξ j*
            star (columnPhase (V 3) (v j) t)) U K).re≤(B₂ L*(1+‖t‖)^J₂)^2) →
      (1+R)^A*‖∑ z∈rows,q z*∑ i∈S,∑ j∈T,
        ((if IsCoprime (a i) (b j) then originalPhase e r ρ (a i) (b j) else 0)*(c i*star (d j)))*
          (gaussRow (a i) (ha i) z*star (gaussRow (b j) (hb j) (-z)))*
            wholeKernel W V R (ρ₀ z) (x z) (u i) (v j)‖≤
        C*∑ L∈divisorPool T (fun j => Ideal.span {b j}),
          ‖(UniqueFactorizationMonoid.moebius L:ℂ)‖*(B₁ L*B₂ L) := by
  obtain ⟨C,hC,hbound⟩ := whole_kernel_reflected_gauss_child_bound W V M hM hV A J₁ J₂
  refine ⟨256*C,mul_nonneg (by norm_num) hC,?_⟩
  intro R hR α β rows S T a b ha hb hpa hpb c d e r ρ hρ hρe q u v ρ₀ x hq hV₀ hV₁ U K hK hU hmajor
    B₁ B₂ hB₁ hB₂ hleft hright
  rw [first_row_children rows S T a b ha hb hpa hpb c d e r ρ hρ]
  apply finite_first_ray_divisor_bound _ _ ((1+R)^A) C (by positivity) hC B₁ B₂ hB₁ hB₂
  intro L hL χ ξ
  exact hbound R hR rows S T a b ha hb
    (divisorCoefficient L a (fun i => c i*leftCoefficient e r ρ (a i)) χ)
    (divisorCoefficient L b (fun j => d j*rightCoefficient e r ρ (b j)) (ξ⁻¹))
    u v ρ₀ x (fun z => q z*ρ e)
    (fun z hz => by rw [norm_mul];exact (mul_le_of_le_one_left (norm_nonneg _) (hq z hz)).trans hρe)
    hV₀ hV₁ U K hK hU hmajor (B₁ L) (B₂ L) (hB₁ L hL) (hB₂ L hL)
    (hleft L hL χ) (hright L hL (ξ⁻¹))

end CenteredMomentFirstChildBound

end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace CenteredMomentFirstPhysicalSource
open Eisenstein  
open HeckeFamily CanonicalQuadraticSieve CenteredMomentSourceRow
open CenteredMomentCanonicalFirst CenteredMomentFirstCanonicalFamily CenteredMomentCompleteCommon
open CenteredMomentSupportedCorrelation CenteredMomentCommonSupport CenteredMomentFirstReduced
open CenteredMomentFirstColumns CenteredMomentFirstAssembly CenteredMomentGaussEnergy
open CenteredMomentFirstChildBound CenteredMomentChildAssembly CenteredMomentMobiusRegroup
open CenteredMomentSmooth RayFourExpansion 
local notation "O"=> Eisenstein.O

theorem physical_block_child_bound (W:𝓢(ℝ,ℂ))(V:Fin 4→ℝ→ℂ)
    (M:Fin 4→ℝ)(hM:∀i,0≤ M i)(hV:∀i y,V i y≠0→|y|≤ M i)(A J₁ J₂:ℕ):
    ∃Cbound:ℝ,0≤ Cbound ∧
    ∀(η:Character)(m:O)(t:ℝ)(S:Finset (Ideal O))(c:Ideal O→ℂ)
      (C D:Ideal O)(hC:Supported C)(hD:Supported D),primeSupport C=primeSupport D→
    ∀(E:Finset (CommonIndex C D))(rows:Finset O),(∀h∈rows,h≠0)→
    ∀K K₀ H₀ A₀ B₀:ℝ,0< K→0< K₀→0< H₀→0< A₀→0< B₀→
    let e:=TruncatedPrincipalPoisson.primeSubsetGenerator (fun P:CommonIndex C D=> P.val) E;
    let k:=K/‖ringComplex e‖^2;
    let r:=activeConductor C D;
    let ρ:=finiteSexticRow (activePrime C D) (activeGood C D hC) (activeExponent C D);
    (∀h∈rows,‖V 0 (Real.log ((k/‖ringComplex r‖^2)/K₀))‖≤1)→
    (∀h∈rows,‖V 1 (Real.log (‖ringComplex h‖^2/H₀))‖≤1)→
    ∀(U:𝓢(ℝ,ℂ))(H:ℝ),0< H→
    (∀h:O,0≤(U (‖ringComplex h‖^2/H)).re)→
    (∀h∈rows,1≤(U (‖ringComplex h‖^2/H)).re)→
    ∀B₁ B₂:Ideal O→ℝ,
    (∀L∈divisorPool (Finset.univ:Finset (columns C D hD.1 S))
      (fun b=> Ideal.span {element C D hD.1 S b}),0≤ B₁ L)→
    (∀L∈divisorPool (Finset.univ:Finset (columns C D hD.1 S))
      (fun b=> Ideal.span {element C D hD.1 S b}),0≤ B₂ L)→
    (∀L∈divisorPool (Finset.univ:Finset (columns C D hD.1 S))
      (fun b=> Ideal.span {element C D hD.1 S b}),∀χ:RayCharacter,∀v:ℝ,
      (gaussEnergy Finset.univ (element C C hC.1 S) (element_supported C C hC.1 S)
        (fun a=> divisorCoefficient L (element C C hC.1 S)
          (fun a=> coefficient η m 1 t c C a*leftCoefficient e r ρ (element C C hC.1 S a)) χ a*
          columnPhase (V 2) (Real.log (‖ringComplex (element C C hC.1 S a)‖^2/A₀)) v) U H).re
            ≤(B₁ L*(1+‖v‖)^J₁)^2)→
    (∀L∈divisorPool (Finset.univ:Finset (columns C D hD.1 S))
      (fun b=> Ideal.span {element C D hD.1 S b}),∀χ:RayCharacter,∀v:ℝ,
      (gaussEnergy Finset.univ (element C D hD.1 S) (element_supported C D hD.1 S)
        (fun b=> divisorCoefficient L (element C D hD.1 S)
          (fun b=> coefficient η m 1 t c D b*rightCoefficient e r ρ (element C D hD.1 S b)) χ b*
          star (columnPhase (V 3) (Real.log (‖ringComplex (element C D hD.1 S b)‖^2/B₀)) v)) U H).re
            ≤(B₂ L*(1+‖v‖)^J₂)^2)→
    (1+K₀*H₀/(A₀*B₀))^A*‖block η m 1 t S c C D hC hD E rows W V K K₀ H₀ A₀ B₀‖≤
      ‖scalar C D hC E K A₀ B₀‖*Cbound*
        ∑L∈divisorPool (Finset.univ:Finset (columns C D hD.1 S))
          (fun b=> Ideal.span {element C D hD.1 S b}),
          ‖(UniqueFactorizationMonoid.moebius L:ℂ)‖*(B₁ L*B₂ L):=by
  obtain ⟨Cbound,hCbound,hbound⟩:=whole_kernel_first_child_bound.{0,0} W V M hM hV A J₁ J₂
  refine ⟨Cbound,hCbound,?_⟩
  intro η m t S c C D hC hD hCD E rows hrows K K₀ H₀ A₀ B₀ hK hK₀ hH₀ hA₀ hB₀
  dsimp only
  intro hV₀ hV₁ U H hH hU hmajor B₁ B₂ hB₁ hB₂ hleft hright
  have hh:=hbound (K₀*H₀/(A₀*B₀)) (div_pos (mul_pos hK₀ hH₀) (mul_pos hA₀ hB₀))
    rows Finset.univ Finset.univ (element C C hC.1 S) (element C D hD.1 S)
    (element_supported C C hC.1 S) (element_supported C D hD.1 S)
    (element_primary C C hC.1 S) (element_primary C D hD.1 S)
    (fun a=> coefficient η m 1 t c C a) (fun b=> coefficient η m 1 t c D b)
    (TruncatedPrincipalPoisson.primeSubsetGenerator (fun P:CommonIndex C D=> P.val) E) (activeConductor C D)
    (finiteSexticRow (activePrime C D) (activeGood C D hC) (activeExponent C D))
    (finiteSexticRow_mul _ _ _) (SchwartzPlanePoisson.finiteSexticRow_norm_le_one _ _ _ _)
    (fun h=> star (finiteSexticRow (activePrime C D) (activeGood C D hC) (activeExponent C D) h))
    (fun a=> Real.log (‖ringComplex (element C C hC.1 S a)‖^2/A₀))
    (fun b=> Real.log (‖ringComplex (element C D hD.1 S b)‖^2/B₀))
    (fun _=> Real.log ((K/‖ringComplex (TruncatedPrincipalPoisson.primeSubsetGenerator (fun P:CommonIndex C D=> P.val) E)‖^2/
      ‖ringComplex (activeConductor C D)‖^2)/K₀))
    (fun h=> Real.log (‖ringComplex h‖^2/H₀))
    (fun h _=> by rw [norm_star];exact SchwartzPlanePoisson.finiteSexticRow_norm_le_one _ _ _ _)
    hV₀ hV₁ U H hH hU hmajor B₁ B₂ hB₁ hB₂ hleft hright
  rw [block_eq_whole η m 1 t S c C D hC hD hCD E rows hrows W V K K₀ H₀ A₀ B₀ hK hK₀ hH₀ hA₀ hB₀,
    norm_mul]
  convert mul_le_mul_of_nonneg_left hh (norm_nonneg (scalar C D hC E K A₀ B₀)) using 1 <;> first | rfl | ring

end CenteredMomentFirstPhysicalSource

end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace CenteredMomentFirstMaskedFamily
open HeckeFamily HeckeRowClosure CanonicalRowCompletion CanonicalQuadraticSieve
open  CompletedGauss RayFourExpansion
open CenteredMomentFixedRowMask
open CenteredMomentFirstFamily CenteredMomentFirstIdealFamily CenteredMomentFirstCanonicalFamily
open CenteredMomentFirstColumns CenteredMomentCanonicalFirst CenteredMomentCommonSupport
open CenteredMomentHeckeExpansion CenteredMomentHeckeColumnWindow CenteredMomentSourceRow
open CenteredMomentOriginalChildEnergy
open CenteredMomentGaussEnergy CenteredMomentLiveDomain CenteredMomentPrimaryCharacter
open Eisenstein  CenteredMomentChildAssembly CenteredMomentChildRows
local notation "O" => Eisenstein.O
local notation "fixedBadMask" => (lambda*(2:O))

lemma fixed_mask_ne_zero : fixedBadMask≠0 :=
  mul_ne_zero residue_lambda_prime.ne_zero (by norm_num)

def idealMask (u : O) (I : Ideal O) : ℂ := if IsCoprime I (Ideal.span {u}) then 1 else 0

def maskedSource (u : O) (β : Ideal O → ℂ) (I : Ideal O) : ℂ := β I * idealMask u I

lemma idealMask_span (u n : O) : idealMask u (Ideal.span {n}) =
    if IsCoprime n u then 1 else 0 := by
  simp only [idealMask, Ideal.isCoprime_span_singleton_iff]

lemma idealMask_primary (u : O) (I : Ideal O) (hI : Supported I) :
    idealMask u I = if IsCoprime (primaryIdealGenerator I) u then 1 else 0 := by
  conv_lhs => rw [←primary_span_supported I hI, idealMask_span]

lemma row_mask_factor (η : Character) (u z n : O) :
    rowTwist (elementHom η) (fixedBadMask*u) 1 z n =
      (if IsCoprime n u then (1:ℂ) else 0)*
        rowTwist (elementHom η) fixedBadMask 1 z n := by
  have h := row_mask_mul η fixedBadMask u 1 z n
    (dvd_mul_right lambda (2:O)) (dvd_mul_left (2:O) lambda)
  simp only [one_mul] at h
  rw [h]
  split_ifs <;> simp

lemma rowWeight_mask_factor (η : Character) (u : O) (I : Ideal O)
    (hI : Supported I) (t : ℝ) :
    rowWeight η (fixedBadMask*u) 1 1 t I =
      idealMask u I * rowWeight η fixedBadMask 1 1 t I := by
  rw [rowWeight_one_primary η (fixedBadMask*u) t I hI,
    rowWeight_one_primary η fixedBadMask t I hI, idealMask_primary u I hI]
  change elementCoeff η (primaryIdealGenerator I) *
      (if IsCoprime (fixedBadMask*u) (primaryIdealGenerator I) then (1:ℂ) else 0) *
      (Ideal.absNorm I:ℂ)^(Complex.I*t) =
    (if IsCoprime (primaryIdealGenerator I) u then (1:ℂ) else 0) *
      (elementCoeff η (primaryIdealGenerator I) *
        (if IsCoprime fixedBadMask (primaryIdealGenerator I) then (1:ℂ) else 0) *
        (Ideal.absNorm I:ℂ)^(Complex.I*t))
  rw [IsCoprime.mul_left_iff]
  by_cases hm : IsCoprime fixedBadMask (primaryIdealGenerator I)
  <;> by_cases hu : IsCoprime (primaryIdealGenerator I) u
  <;> simp [hm, hu, show IsCoprime u (primaryIdealGenerator I) ↔
      IsCoprime (primaryIdealGenerator I) u from isCoprime_comm]

theorem exists_first_masked_character (η : Character) (e r : O)
    (he : Supported (Ideal.span {e})) (hr : Supported (Ideal.span {r}))
    (χ : MulChar (Residue r) ℂ) (ξ : RayCharacter) :
    ∃ τ : Character,
      τ.modulus = η.modulus*Ideal.span {fixedBadMask}*Ideal.span {(72:O)}*Ideal.span {e*r} ∧
      (∀ n : O, elementCoeff τ n =
        rowTwist (elementHom η) fixedBadMask 1 (e*r) n * maskedPrimaryHom r χ n *
          elementCoeff (CenteredMomentFixedRay.primaryRayCharacter ξ) n) ∧
      ∀ u n : O,
        rowTwist (elementHom η) (fixedBadMask*u) 1 (e*r) n * maskedPrimaryHom r χ n *
          elementCoeff (CenteredMomentFixedRay.primaryRayCharacter ξ) n =
        (if IsCoprime n u then (1:ℂ) else 0)*elementCoeff τ n := by
  obtain ⟨τ,hM,hτ,_⟩ := exists_first_character η fixedBadMask e r fixed_mask_ne_zero
    he hr (dvd_mul_right lambda (2:O)) (dvd_mul_left (2:O) lambda) χ ξ
  refine ⟨τ,hM,hτ,?_⟩
  intro u n
  rw [row_mask_factor,hτ]
  ring

theorem exists_canonical_masked_pair (η : Character) (C D : Ideal O)
    (hC : Supported C) (E : Finset (CommonIndex C D)) (ξ₁ ξ₂ : RayCharacter) :
    let e := TruncatedPrincipalPoisson.primeSubsetGenerator (fun P : CommonIndex C D => P.val) E
    let r := activeConductor C D
    let ρ := finiteSexticRow (activePrime C D) (activeGood C D hC) (activeExponent C D)
    let M := η.modulus*Ideal.span {fixedBadMask}*Ideal.span {(72:O)}*Ideal.span {e*r}
    ∃ τ₁ τ₂ : Character, τ₁.modulus=M ∧ τ₂.modulus=M ∧
      (∀ I : Ideal O, Supported I → ∀ t : ℝ,
        heightCoeff τ₁ t I=rowWeight η fixedBadMask 1 1 t I*
          (leftCoefficient e r ρ (primaryIdealGenerator I)*rayMonoid ξ₁ (primaryIdealGenerator I))) ∧
      (∀ I : Ideal O, Supported I → ∀ t : ℝ,
        heightCoeff τ₂ t I=rowWeight η fixedBadMask 1 1 t I*
          (rightCoefficient e r ρ (primaryIdealGenerator I)*rayMonoid ξ₂ (primaryIdealGenerator I))) ∧
      (∀ u : O, ∀ I : Ideal O, Supported I → ∀ t : ℝ,
        rowWeight η (fixedBadMask*u) 1 1 t I*
          (leftCoefficient e r ρ (primaryIdealGenerator I)*rayMonoid ξ₁ (primaryIdealGenerator I)) =
          idealMask u I*heightCoeff τ₁ t I) ∧
      (∀ u : O, ∀ I : Ideal O, Supported I → ∀ t : ℝ,
        rowWeight η (fixedBadMask*u) 1 1 t I*
          (rightCoefficient e r ρ (primaryIdealGenerator I)*rayMonoid ξ₂ (primaryIdealGenerator I)) =
          idealMask u I*heightCoeff τ₂ t I) := by
  obtain ⟨τ₁,τ₂,hM₁,hM₂,h₁,h₂⟩ := exists_first_ideal_pair η fixedBadMask fixed_mask_ne_zero
    (dvd_mul_right lambda (2:O)) (dvd_mul_left (2:O) lambda) C D hC E ξ₁ ξ₂
  refine ⟨τ₁,τ₂,hM₁,hM₂,h₁,h₂,?_,?_⟩
  · intro u I hI t
    rw [rowWeight_mask_factor η u I hI t,heightCoeff,h₁ I hI t]
    ring
  · intro u I hI t
    rw [rowWeight_mask_factor η u I hI t,heightCoeff,h₂ I hI t]
    ring

lemma divisor_column_masked (η τ : Character) (F : O → ℂ) (ξ : RayCharacter)
    (hτ : ∀ I : Ideal O, Supported I → ∀ t : ℝ,
      heightCoeff τ t I=rowWeight η fixedBadMask 1 1 t I*
        (F (primaryIdealGenerator I)*rayMonoid ξ (primaryIdealGenerator I)))
    (u : O) (L I : Ideal O) (hI : Supported I) (β : Ideal O → ℂ) (t : ℝ) :
    divisorCoefficient L (fun J : Ideal O => primaryIdealGenerator J)
      (fun J => β J*rowWeight η (fixedBadMask*u) 1 1 t J*F (primaryIdealGenerator J)) ξ I =
      (if L∣I then maskedSource u β I else 0)*heightCoeff τ t I := by
  rw [divisorCoefficient,primary_span_supported I hI,rowWeight_mask_factor η u I hI t,hτ I hI t]
  split_ifs
  · simp only [maskedSource]; ring
  · ring

lemma sourceGaussEnergy_congr (Q : Finset (Ideal O)) (c f c' f' : Ideal O → ℂ)
    (h : ∀ I ∈ Q, Supported I → c I*f I=c' I*f' I)
    (W : 𝓢(ℝ,ℂ)) (K : ℝ) : sourceGaussEnergy Q c f W K=sourceGaussEnergy Q c' f' W K := by
  unfold sourceGaussEnergy
  congr 1
  funext I
  exact h I (Finset.mem_filter.mp I.property).1 (Finset.mem_filter.mp I.property).2

lemma first_source_energy (η τ : Character) (F : O → ℂ)
    (hτ : ∀ I : Ideal O, Supported I → ∀ t : ℝ,
      heightCoeff τ t I=rowWeight η fixedBadMask 1 1 t I*F (primaryIdealGenerator I))
    (Q : Finset (Ideal O)) (β : Ideal O → ℂ) (u : O) (t : ℝ) (W : 𝓢(ℝ,ℂ)) (K : ℝ) :
    sourceGaussEnergy Q β
      (fun I => rowWeight η (fixedBadMask*u) 1 1 t I*F (primaryIdealGenerator I)) W K =
    sourceGaussEnergy Q (maskedSource u β) (heightCoeff τ t) W K := by
  apply sourceGaussEnergy_congr
  intro I _ hI
  rw [rowWeight_mask_factor η u I hI t,hτ I hI t]
  simp only [maskedSource]
  ring

lemma maskedSource_eq_of_live (u : O) (β : Ideal O → ℂ)
    (h : ∀ I, β I≠0 → IsCoprime I (Ideal.span {u})) : maskedSource u β=β := by
  funext I
  by_cases hi : β I=0
  · simp [maskedSource,hi]
  · simp [maskedSource,idealMask,h I hi]

lemma extracted_masked_coefficient (η : Character) (u : O) (C I : Ideal O)
    (hI : Supported I) (β : Ideal O → ℂ) (t : ℝ) (f : ℂ) :
    β (C*I)*rowWeight η (fixedBadMask*u) 1 1 t (C*I)*f =
      (β (C*I)*rowWeight η (fixedBadMask*u) 1 1 t C*idealMask u I)*
        (rowWeight η fixedBadMask 1 1 t I*f) := by
  rw [map_mul,rowWeight_mask_factor η u I hI t]
  ring

lemma idealMask_generator (R I : Ideal O) :
    idealMask (cubicIdealGenerator R) I = if IsCoprime I R then 1 else 0 := by
  rw [idealMask,span_cubicIdealGenerator]

lemma maskedSource_punctured (u : O) (R : Ideal O) (β : Ideal O → ℂ) (I : Ideal O) :
    maskedSource u (fun J => if IsCoprime J R then β J else 0) I =
      if IsCoprime I R ∧ IsCoprime I (Ideal.span {u}) then β I else 0 := by
  unfold maskedSource idealMask
  split_ifs <;> simp_all

lemma first_gauss_row (η τ : Character) (F : O → ℂ)
    (hτ : ∀ I : Ideal O, Supported I → ∀ t : ℝ,
      heightCoeff τ t I=rowWeight η fixedBadMask 1 1 t I*F (primaryIdealGenerator I))
    (Q : Finset (Ideal O)) (β : Ideal O → ℂ) (u : O) (t : ℝ) (z : O) :
    gaussPolynomial Finset.univ (sourceGenerator Q) (sourceGenerator_supported Q)
      (fun I : supportedColumns Q => β I*
        (rowWeight η (fixedBadMask*u) 1 1 t I*F (primaryIdealGenerator I))) z =
    gaussPolynomial Finset.univ (sourceGenerator Q) (sourceGenerator_supported Q)
      (fun I : supportedColumns Q => maskedSource u β I*heightCoeff τ t I) z := by
  apply congrArg (fun c => gaussPolynomial Finset.univ (sourceGenerator Q)
    (sourceGenerator_supported Q) c z)
  funext I
  have hI := (Finset.mem_filter.mp I.property).2
  rw [rowWeight_mask_factor η u I hI t,hτ I hI t]
  dsimp only [maskedSource]
  ring

theorem exists_canonical_source_pair (η : Character) (C D : Ideal O)
    (hC : Supported C) (E : Finset (CommonIndex C D)) (ξ₁ ξ₂ : RayCharacter) :
    let e := TruncatedPrincipalPoisson.primeSubsetGenerator (fun P : CommonIndex C D => P.val) E
    let r := activeConductor C D
    let ρ := finiteSexticRow (activePrime C D) (activeGood C D hC) (activeExponent C D)
    let M := η.modulus*Ideal.span {fixedBadMask}*Ideal.span {(72:O)}*Ideal.span {e*r}
    ∃ τ₁ τ₂ : Character, τ₁.modulus=M ∧ τ₂.modulus=M ∧
      (∀ I : Ideal O, Supported I → ∀ t : ℝ,
        heightCoeff τ₁ t I=rowWeight η fixedBadMask 1 1 t I*
          (leftCoefficient e r ρ (primaryIdealGenerator I)*rayMonoid ξ₁ (primaryIdealGenerator I))) ∧
      (∀ I : Ideal O, Supported I → ∀ t : ℝ,
        heightCoeff τ₂ t I=rowWeight η fixedBadMask 1 1 t I*
          (rightCoefficient e r ρ (primaryIdealGenerator I)*rayMonoid ξ₂ (primaryIdealGenerator I))) ∧
      ∀ (Q₁ Q₂ : Finset (Ideal O)) (β₁ β₂ : Ideal O → ℂ) (u₁ u₂ : O)
        (t : ℝ) (W : 𝓢(ℝ,ℂ)) (K : ℝ),
      sourceGaussEnergy Q₁ β₁ (fun I => rowWeight η (fixedBadMask*u₁) 1 1 t I*
        (leftCoefficient e r ρ (primaryIdealGenerator I)*rayMonoid ξ₁ (primaryIdealGenerator I))) W K =
        sourceGaussEnergy Q₁ (maskedSource u₁ β₁) (heightCoeff τ₁ t) W K ∧
      sourceGaussEnergy Q₂ β₂ (fun I => rowWeight η (fixedBadMask*u₂) 1 1 t I*
        (rightCoefficient e r ρ (primaryIdealGenerator I)*rayMonoid ξ₂ (primaryIdealGenerator I))) W K =
        sourceGaussEnergy Q₂ (maskedSource u₂ β₂) (heightCoeff τ₂ t) W K := by
  obtain ⟨τ₁,τ₂,hM₁,hM₂,h₁,h₂,_,_⟩ := exists_canonical_masked_pair η C D hC E ξ₁ ξ₂
  refine ⟨τ₁,τ₂,hM₁,hM₂,h₁,h₂,?_⟩
  intro Q₁ Q₂ β₁ β₂ u₁ u₂ t W K
  constructor
  · apply sourceGaussEnergy_congr
    intro I _ hI
    rw [rowWeight_mask_factor η u₁ I hI t,h₁ I hI t]
    dsimp only [maskedSource]
    ring
  · apply sourceGaussEnergy_congr
    intro I _ hI
    rw [rowWeight_mask_factor η u₂ I hI t,h₂ I hI t]
    dsimp only [maskedSource]
    ring


end CenteredMomentFirstMaskedFamily

end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped BigOperators Classical

namespace CanonicalRowCompletion

/-- A maximal ideal avoids the two excluded primes exactly when its residue
field has odd characteristic and the ramified element is nonzero. -/
theorem prime_good_iff_not_bad (P : Ideal Eisenstein.O) [P.IsMaximal] :
    (lambda ∉ P ∧ ringChar (Eisenstein.O ⧸ P) ≠ 2) ↔ P ∉ fixedBadPrimes := by
  have hp : Prime P := Ideal.prime_of_isPrime (NeZero.ne P) inferInstance
  have hram : lambda ∈ P ↔ P = ramifiedIdeal := by
    constructor
    · intro h
      have hm : ramifiedIdeal.IsMaximal :=
        (Ideal.isPrime_of_prime ramifiedIdeal_prime).isMaximal ramifiedIdeal_prime.ne_zero
      exact (hm.eq_of_le (Ideal.IsMaximal.ne_top (inferInstance : P.IsMaximal))
        (Ideal.span_le.mpr (Set.singleton_subset_iff.mpr h))).symm
    · rintro rfl
      exact Ideal.subset_span (Set.mem_singleton _)
  rw [fixedBadPrimes, Finset.mem_insert, Finset.mem_singleton, not_or]
  exact and_congr (not_congr hram) (not_congr (prime_ideal_char_two_iff P hp))

end CanonicalRowCompletion

namespace CenteredMomentPrimeElements
open HeckeFamily CanonicalQuadraticSieve CompletedGauss
open CenteredMomentPrimePool CenteredMomentAmplificationGlobal
local notation "O" => Eisenstein.O

def elementPool (P : Finset (Ideal O)) : Finset O := P.image primaryIdealPrime

theorem primaryIdealPrime_data (P : Ideal O) (hp : Prime P) (hbad : P ∉ fixedBadPrimes) :
    Prime (primaryIdealPrime P) ∧ Ideal.span {primaryIdealPrime P} = P ∧
    lambda^2 ∣ primaryIdealPrime P - 1 ∧
    Supported (Ideal.span {primaryIdealPrime P}) ∧
    lambda ∉ Ideal.span {primaryIdealPrime P} ∧
    ringChar (O ⧸ Ideal.span {primaryIdealPrime P}) ≠ 2 := by
  let : P.IsMaximal := (Ideal.isPrime_of_prime hp).isMaximal hp.ne_zero
  have hg := (prime_good_iff_not_bad P).mpr hbad
  have hn := primaryIdealPrime_ne_zero P hg.1
  have hs := (primaryIdealPrime_spec P hn).2.2
  have hsupport : Supported P := by
    refine ⟨hp.ne_zero,?_⟩
    intro Q hQ
    have he : Q = P := by
      simpa only [UniqueFactorizationMonoid.normalizedFactors_irreducible hp.irreducible,
        normalize_eq,Multiset.mem_singleton] using hQ
    subst Q
    exact hg
  refine ⟨?_,hs.1,hs.2,?_,?_,?_⟩
  · apply (Ideal.span_singleton_prime hn).mp
    rw [hs.1]
    infer_instance
  · rwa [hs.1]
  · rw [hs.1]
    exact hg.1
  · rw [hs.1]
    exact hg.2

theorem elementPool_card (P : Finset (Ideal O))
    (hp : ∀ Q ∈ P, Prime Q) (hbad : ∀ Q ∈ P, Q ∉ fixedBadPrimes) :
    (elementPool P).card = P.card := by
  apply Finset.card_image_of_injOn
  intro Q hQ R hR he
  rw [← (primaryIdealPrime_data Q (hp Q hQ) (hbad Q hQ)).2.1,
    ← (primaryIdealPrime_data R (hp R hR) (hbad R hR)).2.1,he]

theorem elementPool_data (P : Finset (Ideal O))
    (hp : ∀ Q ∈ P, Prime Q) (hbad : ∀ Q ∈ P, Q ∉ fixedBadPrimes)
    (p : O) (hpm : p ∈ elementPool P) :
    Prime p ∧ Ideal.span {p} ∈ P ∧
    lambda^2 ∣ p-1 ∧
    Supported (Ideal.span {p}) ∧
    lambda ∉ Ideal.span {p} ∧
    ringChar (O ⧸ Ideal.span {p}) ≠ 2 := by
  obtain ⟨Q,hQ,rfl⟩ := Finset.mem_image.mp hpm
  obtain ⟨hpr,hspan,hprim,hs,hg,hc⟩ := primaryIdealPrime_data Q (hp Q hQ) (hbad Q hQ)
  exact ⟨hpr,hspan.symm ▸ hQ,hprim,hs,hg,hc⟩

theorem eligible_not_dvd (P : Finset (Ideal O))
    (hp : ∀ Q ∈ P, Prime Q) (hbad : ∀ Q ∈ P, Q ∉ fixedBadPrimes)
    (R : Ideal O) (h : O) (hh : Ideal.span {h} ∣ R)
    (p : O) (hpm : p ∈ elementPool (eligiblePool P R)) : ¬p ∣ h := by
  have hd := elementPool_data (eligiblePool P R)
    (fun Q hQ => hp Q (Finset.mem_filter.mp hQ).1)
    (fun Q hQ => hbad Q (Finset.mem_filter.mp hQ).1) p hpm
  intro hph
  apply (Finset.mem_filter.mp hd.2.1).2
  exact (Ideal.dvd_iff_le.mpr (Ideal.span_singleton_le_span_singleton.mpr hph)).trans hh

theorem primePool_data (M : Ideal O) [NeZero M] (H : Subgroup (O ⧸ M)ˣ)
    (S : Finset (Ideal O)) (hS : fixedBadPrimes ⊆ S) (a b x : ℝ)
    (Q : Ideal O) (hQ : Q ∈ primePool M H S a b x) :
    Prime Q ∧ Q ∉ fixedBadPrimes := by
  obtain ⟨hQ,hQS⟩ := Finset.mem_sdiff.mp hQ
  exact ⟨((PNT.AnnularPrimeMass.mem_annularPrimeIdeals _ _ _ _ _).mp hQ).2.1,
    fun hbad => hQS (hS hbad)⟩

theorem elementPool_eligible (P : Finset (Ideal O))
    (hp : ∀ Q ∈ P, Prime Q) (hbad : ∀ Q ∈ P, Q ∉ fixedBadPrimes)
    (R : Ideal O) :
    (elementPool P).filter (fun p => ¬Ideal.span {p} ∣ R) =
      elementPool (eligiblePool P R) := by
  ext p
  simp only [elementPool,eligiblePool,Finset.mem_filter,Finset.mem_image]
  constructor
  · rintro ⟨⟨Q,hQ,rfl⟩,hnot⟩
    refine ⟨Q,⟨hQ,?_⟩,rfl⟩
    rwa [← (primaryIdealPrime_data Q (hp Q hQ) (hbad Q hQ)).2.1]
  · rintro ⟨Q,⟨hQ,hnot⟩,rfl⟩
    refine ⟨⟨Q,hQ,rfl⟩,?_⟩
    rwa [(primaryIdealPrime_data Q (hp Q hQ) (hbad Q hQ)).2.1]

theorem eligible_element_card_half (P : Finset (Ideal O))
    (hp : ∀ Q ∈ P, Prime Q) (hbad : ∀ Q ∈ P, Q ∉ fixedBadPrimes)
    (R : Ideal O) (hR : R ≠ 0) (Z ell B : ℝ) (hZ : 1 < Z) (hell : 0 < ell)
    (hlower : ∀ Q ∈ P, Z^ell ≤ (Ideal.absNorm Q : ℝ))
    (hupper : (Ideal.absNorm R : ℝ) ≤ Z^B) (hsize : 2*(B/ell) ≤ P.card) :
    (P.card : ℝ)/2 ≤ ((elementPool P).filter (fun p => ¬Ideal.span {p} ∣ R)).card := by
  rw [elementPool_eligible P hp hbad R,elementPool_card (eligiblePool P R)
    (fun Q hQ => hp Q (Finset.mem_filter.mp hQ).1)
    (fun Q hQ => hbad Q (Finset.mem_filter.mp hQ).1)]
  exact eligiblePool_half P hp R hR Z ell B hZ hell hlower hupper hsize

theorem ideal_pool_polynomial_bound {α : Type*} (S : Finset α) (a : α → O)
    (ha : ∀ i, Supported (Ideal.span {a i})) (c : α → ℂ)
    (P : Finset (Ideal O)) (hne : P.Nonempty)
    (hp : ∀ Q ∈ P, Prime Q) (hbad : ∀ Q ∈ P, Q ∉ fixedBadPrimes)
    (h : O) (hh : ∀ Q ∈ P, ¬Q ∣ Ideal.span {h}) :
    ‖CenteredMomentGaussEnergy.gaussPolynomial S a ha c h‖^2 ≤ (4/(P.card : ℝ))*
      ∑ p ∈ elementPool P,
        (‖CenteredMomentGaussEnergy.gaussPolynomial S a ha c (p^6*h)‖^2 +
        ‖amplificationError S a ha c (fun i => multiplicity p (a i)) p 1 h‖^2 +
        ‖amplificationError S a ha c (fun i => multiplicity p (a i)) p 6 h‖^2 +
        ‖amplificationError S a ha c (fun i => multiplicity p (a i)) p 7 h‖^2) := by
  have he := polynomial_pool_bound S a ha c (elementPool P) (Finset.Nonempty.image hne _)
    (fun p hpm => (elementPool_data P hp hbad p hpm).1)
    (fun p hpm => (elementPool_data P hp hbad p hpm).2.2.2.1)
    (fun p hpm => (elementPool_data P hp hbad p hpm).2.2.2.2.1)
    (fun p hpm => (elementPool_data P hp hbad p hpm).2.2.2.2.2) h (by
      intro p hpm hph
      apply hh (Ideal.span {p}) (elementPool_data P hp hbad p hpm).2.1
      exact Ideal.dvd_iff_le.mpr (Ideal.span_singleton_le_span_singleton.mpr hph))
  simpa only [elementPool_card P hp hbad] using he

end CenteredMomentPrimeElements

end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped BigOperators Classical SchwartzMap

namespace CenteredMomentGaussNormalization
open CanonicalQuadraticSieve CenteredMomentGaussEnergy CenteredMomentOriginalChildEnergy
open CenteredMomentDivisorRawEnergy CenteredMomentSourceRow
local notation "O" => Eisenstein.O

theorem gaussPolynomial_const_mul {α : Type*} (S : Finset α) (a : α → O)
    (ha : ∀ i,Supported (Ideal.span {a i})) (c : α → ℂ) (d : ℂ) (z : O) :
    gaussPolynomial S a ha (fun i => d*c i) z=d*gaussPolynomial S a ha c z := by
  simp only [gaussPolynomial,Finset.mul_sum,mul_assoc]

theorem gaussEnergy_const_mul {α : Type*} (S : Finset α) (a : α → O)
    (ha : ∀ i,Supported (Ideal.span {a i})) (c : α → ℂ) (d : ℂ)
    (W : 𝓢(ℝ,ℂ)) (K : ℝ) :
    gaussEnergy S a ha (fun i => d*c i) W K=((‖d‖^2:ℝ):ℂ)*gaussEnergy S a ha c W K := by
  simp only [gaussEnergy,gaussPolynomial_const_mul,norm_mul,mul_pow,Complex.ofReal_mul,mul_assoc,tsum_mul_left]

theorem gaussEnergy_central {α : Type*} (S : Finset α) (a : α → O)
    (ha : ∀ i,Supported (Ideal.span {a i})) (c : α → ℂ)
    (T : ℝ) (hT : 0< T) (W : 𝓢(ℝ,ℂ)) (K : ℝ) :
    (gaussEnergy S a ha (fun i => (Real.sqrt T:ℂ)⁻¹*c i) W K).re=
      (gaussEnergy S a ha c W K).re/T := by
  rw [gaussEnergy_const_mul,norm_inv,Complex.norm_real,Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg _),inv_pow,Real.sq_sqrt hT.le]
  simp only [Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero,div_eq_mul_inv,mul_comm]

theorem sourceGaussEnergy_central (Q : Finset (Ideal O)) (c f : Ideal O → ℂ)
    (T : ℝ) (hT : 0< T) (W : 𝓢(ℝ,ℂ)) (K : ℝ) :
    (sourceGaussEnergy Q (fun I => (Real.sqrt T:ℂ)⁻¹*c I) f W K).re=
      (sourceGaussEnergy Q c f W K).re/T := by
  unfold sourceGaussEnergy
  simp only [mul_assoc]
  exact gaussEnergy_central Finset.univ (sourceGenerator Q) (sourceGenerator_supported Q)
    (fun I : supportedColumns Q => c I*f I) T hT W K

theorem sourceGaussEnergy_nonneg (Q : Finset (Ideal O)) (c f : Ideal O → ℂ)
    (W : 𝓢(ℝ,ℂ)) (K : ℝ) (hK : 0< K)
    (hW : ∀ z : O,0≤(W (‖ringComplex z‖^2/K)).re) :
    0≤(sourceGaussEnergy Q c f W K).re := by
  have hs := CenteredMomentSmoothedWindowEnergy.gaussEnergy_hasSum_re Finset.univ
    (sourceGenerator Q) (sourceGenerator_supported Q) (fun I : supportedColumns Q => c I*f I) W K hK
  change 0≤(gaussEnergy Finset.univ (sourceGenerator Q) (sourceGenerator_supported Q) _ W K).re
  rw [←hs.tsum_eq]
  exact tsum_nonneg (fun z => mul_nonneg (sq_nonneg _) (hW z))

end CenteredMomentGaussNormalization

end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson
namespace CenteredMomentAmplificationErrorEnergy
local notation "O" => Eisenstein.O
def localErrorCost (p : O) (n : ℕ) : ℝ :=
  if n=5 then (1-(Ideal.absNorm (Ideal.span {p}):ℝ)⁻¹)^2
  else (Ideal.absNorm (Ideal.span {p}):ℝ)⁻¹

theorem localErrorCost_nonneg (p : O) (n : ℕ) : 0≤ localErrorCost p n := by
  unfold localErrorCost
  split_ifs <;> positivity


end CenteredMomentAmplificationErrorEnergy

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson
namespace CenteredMomentAmplificationActiveFactor
def errorMovingExponent (n : ℕ) : ℕ := if n=5 then 0 else 1


end CenteredMomentAmplificationActiveFactor

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped BigOperators Classical SchwartzMap ContDiff
open Filter

namespace CenteredMomentFirstAmplificationChoice
open HeckeFamily CanonicalQuadraticSieve 
open CenteredMomentSectorLocalization CenteredMomentPrimePool
open CenteredMomentPrimeElements
open CenteredMomentGaussEnergy
open CenteredMomentSourceRow CenteredMomentGaussNormalization
open CenteredMomentAmplificationErrorEnergy
open CenteredMomentAmplificationGlobal
local notation "O" => Eisenstein.O

/-- A nonnegative cutoff equal to one on the unit radial interval. -/
abbrev ballProfile : 𝓢(ℝ,ℂ) := SchwartzPlanePoisson.sieveCutoff

theorem ballProfile_nonneg (x : ℝ) : 0 ≤ (ballProfile x).re := by
  simpa only [ballProfile,SchwartzPlanePoisson.sieveCutoff_apply,Complex.ofReal_re]
    using (SchwartzPlanePoisson.sieveBump.nonneg (x:=x))

theorem ballProfile_le_one (x : ℝ) : (ballProfile x).re ≤ 1 := by
  simpa only [ballProfile,SchwartzPlanePoisson.sieveCutoff_apply,Complex.ofReal_re]
    using (SchwartzPlanePoisson.sieveBump.le_one (x:=x))

theorem ballProfile_one (x : ℝ) (hx : 0≤ x) (hx1 : x≤1) : ballProfile x=1 := by
  simp only [ballProfile,SchwartzPlanePoisson.sieveCutoff_apply,
    SchwartzPlanePoisson.sieveBump_eq_one hx hx1,Complex.ofReal_one]

theorem ballProfile_majorizes (Y : ℝ) (hY : 0< Y) (z : O)
    (hz : normValue z≤ Y) : 1≤(ballProfile (‖ringComplex z‖^2/Y)).re := by
  rw [←normValue_eq_embedding]
  have he := ballProfile_one (normValue z/Y)
    (div_nonneg (by unfold normValue; positivity) hY.le) ((div_le_one hY).mpr hz)
  rw [he]
  norm_num

def mainGain (D0 c sigma : ℝ) : ℝ := max (D0-c) 0+2*sigma

def errorRemoval (p : O) (Z : ℝ) (k : ℕ) : ℝ :=
  (k:ℝ)*Real.logb Z (normValue p)

def errorMoving (p : O) (Z : ℝ) (k : ℕ) : ℝ :=
  if k=6 then 0 else Real.logb Z (normValue p)

def errorGain (D0 c sigma Z : ℝ) (p : O) (k : ℕ) : ℝ :=
  max (D0-c-2*errorRemoval p Z k+errorMoving p Z k) 0+sigma

theorem mainGain_bounds (D0 c sigma : ℝ) (hs : 0≤ sigma) :
    2*sigma≤ mainGain D0 c sigma ∧ D0-c+sigma≤ mainGain D0 c sigma := by
  have h0 := le_max_right (D0-c) (0:ℝ)
  have h1 := le_max_left (D0-c) (0:ℝ)
  unfold mainGain
  constructor <;> linarith

theorem errorGain_bounds (D0 c sigma Z : ℝ) (p : O) (k : ℕ) (hs : 0≤ sigma) :
    sigma≤ errorGain D0 c sigma Z p k ∧
    D0-c-2*errorRemoval p Z k+errorMoving p Z k+sigma≤ errorGain D0 c sigma Z p k ∧
    errorGain D0 c sigma Z p k≤
      max (D0-c-2*errorRemoval p Z k+errorMoving p Z k) 0+2*sigma := by
  have h0 := le_max_right (D0-c-2*errorRemoval p Z k+errorMoving p Z k) (0:ℝ)
  have h1 := le_max_left (D0-c-2*errorRemoval p Z k+errorMoving p Z k) (0:ℝ)
  unfold errorGain
  constructor
  · linarith
  constructor <;> linarith

theorem error_lengths (p : O) (Z sigma : ℝ) (hs : 0≤ sigma) (k : ℕ)
    (hk : k=1 ∨ k=6 ∨ k=7)
    (hl : 0≤ Real.logb Z (normValue p))
    (hu : Real.logb Z (normValue p)≤ sigma/3) :
    0≤ errorMoving p Z k ∧ errorMoving p Z k≤ errorRemoval p Z k ∧
      errorRemoval p Z k≤7*sigma/3 := by
  have hk1 : (1:ℝ)≤ k := by rcases hk with rfl|rfl|rfl <;> norm_num
  have hk7 : (k:ℝ)≤7 := by rcases hk with rfl|rfl|rfl <;> norm_num
  unfold errorMoving errorRemoval
  split_ifs <;> refine ⟨?_,?_,?_⟩ <;> nlinarith

open CenteredMomentSourceProfileMass CenteredMomentSourceMass
open CenteredMomentAddedZeroUniform CenteredMomentOriginalChildEnergy
open CenteredMomentCommonAllocationSum CenteredMomentSourceLiveColumn
open CenteredMomentAmplificationLiveMask CenteredMomentHeckeExpansion
open  CanonicalRowCompletion RayFourExpansion
open HeckeRowClosure CenteredMomentChildRows CenteredMomentHeckeColumnWindow
open CenteredMomentAmplificationActiveFactor

local instance {ι : Type*} : DecidableEq (ι ⊕ Fin 2) := Classical.decEq _

structure OriginalData (ι : Type*) [Fintype ι] where
  S : (ι ⊕ Fin 2) → Finset (Ideal O)
  R : Ideal O
  s : Ideal O
  nu : ι → Ideal O → ℂ
  slot : ι → ℝ → ℂ
  lengths : ι → ℝ
  W₁ : ℝ → ℂ
  W₂ : ℝ → ℂ
  X₁ : ℝ
  X₂ : ℝ
  Y₁ : ℝ
  Y₂ : ℝ
  B₁ : Ideal O
  B₂ : Ideal O

namespace OriginalData
variable {ι : Type*} [Fintype ι]

def profile (D : OriginalData ι) : Tuple ι → ℂ :=
  profileCoefficient D.R D.nu D.slot D.lengths D.W₁ D.W₂
    D.X₁ D.X₂ D.Y₁ D.Y₂ D.B₁ D.B₂ D.s

def columns (D : OriginalData ι) : Finset (Ideal O) :=
  finiteColumns (Fintype.piFinset D.S)

def beta (D : OriginalData ι) : Ideal O → ℂ :=
  finiteColumnCoefficient (Fintype.piFinset D.S) D.profile

def coefficient (D : OriginalData ι) (η : Character) (m : O) (t T : ℝ)
    : supportedColumns D.columns → ℂ :=
  fun I => (Real.sqrt T:ℂ)⁻¹*(D.beta I*rowWeight η m 1 1 t I)

theorem coefficient_eq (D : OriginalData ι) (η : Character) (m : O) (t T : ℝ) :
    D.coefficient η m t T = fun I : supportedColumns D.columns =>
      (Real.sqrt T:ℂ)⁻¹*(D.beta I*rowWeight η m 1 1 t I) := rfl

def childEnergy (D : OriginalData ι) (τ : RayCharacter → Character)
    (p : O) (n : ℕ) (t T K : ℝ) : ℝ :=
  let C := (Ideal.span {p})^(n+1)
  (16*(n+2:ℝ)*localErrorCost p n) *
    ((∑ χ : RayCharacter,∑ B : actualAllocations D.S C,
      (sourceGaussEnergy
        (finiteColumns (liveBox D.S B (allocation_data D.S C B (Finset.mem_filter.mp B.property).1).1))
        (finiteColumnCoefficient
          (liveBox D.S B (allocation_data D.S C B (Finset.mem_filter.mp B.property).1).1)
          (maskedLiveProfile B C D.R D.s D.nu D.slot D.lengths D.W₁ D.W₂
            D.X₁ D.X₂ D.Y₁ D.Y₂ D.B₁ D.B₂))
        (heightCoeff (τ χ) t) ballProfile K).re) /
      (T/(Ideal.absNorm (Ideal.span {p}):ℝ)^(n+1)))

theorem childEnergy_nonneg (D : OriginalData ι) (τ : RayCharacter → Character)
    (p : O) (n : ℕ) (t T K : ℝ) (hT : 0≤ T) (hK : 0< K) :
    0≤ D.childEnergy τ p n t T K := by
  apply mul_nonneg (mul_nonneg (by positivity) (localErrorCost_nonneg p n))
  apply div_nonneg _ (div_nonneg hT (by positivity))
  exact Finset.sum_nonneg (fun χ _ => Finset.sum_nonneg (fun B _ =>
    sourceGaussEnergy_nonneg _ _ _ ballProfile K hK (fun _ => ballProfile_nonneg _)))

end OriginalData

namespace OriginalData
variable {ι : Type*} [Fintype ι]

def active (D : OriginalData ι) : OriginalData ι :=
  { D with S := fun i => match i with
    | Sum.inl j => (D.S i).filter (fun I => D.slot j ((Ideal.absNorm I:ℝ)/D.lengths j)≠0)
    | Sum.inr _ => D.S i }

theorem active_subset (D : OriginalData ι) (i : ι ⊕ Fin 2) : D.active.S i⊆D.S i := by
  cases i <;> simp only [active]
  · exact Finset.filter_subset _ _
  · exact fun _ h => h

theorem active_profile (D : OriginalData ι) : D.active.profile=D.profile := rfl

theorem active_slot (D : OriginalData ι) (i : ι) (I : Ideal O) (hI : I∈D.active.S (Sum.inl i)) :
    D.active.slot i ((Ideal.absNorm I:ℝ)/D.active.lengths i)≠0 :=
  (Finset.mem_filter.mp hI).2

theorem active_profile_zero (D : OriginalData ι) (v : Tuple ι)
    (hv : v∈Fintype.piFinset D.S) (hn : v∉Fintype.piFinset D.active.S) : D.profile v=0 := by
  have hn' : ¬∀i,v i∈D.active.S i := by simpa only [Fintype.mem_piFinset] using hn
  obtain ⟨i,hi⟩ := not_forall.mp hn'
  have hvi := Fintype.mem_piFinset.mp hv i
  cases i with
  | inr j => exact False.elim (hi hvi)
  | inl j =>
    have hz : D.slot j ((Ideal.absNorm (v (Sum.inl j)):ℝ)/D.lengths j)=0 := by
      by_contra hne
      exact hi (Finset.mem_filter.mpr ⟨hvi,hne⟩)
    have hp : (∏k,D.nu k (v (Sum.inl k))*D.slot k
        ((Ideal.absNorm (v (Sum.inl k)):ℝ)/D.lengths k))=0 := by
      apply Finset.prod_eq_zero (Finset.mem_univ j)
      rw [hz,mul_zero]
    simp only [profile,profileCoefficient,hp,zero_mul]

theorem active_beta (D : OriginalData ι) : D.active.beta=D.beta := by
  funext I
  unfold beta finiteColumnCoefficient
  rw [active_profile]
  apply Finset.sum_subset (Finset.filter_subset_filter _
    (Fintype.piFinset_subset _ _ (D.active_subset)))
  intro v hv hn
  have hv' := Finset.mem_filter.mp hv
  apply D.active_profile_zero v hv'.1
  intro hm
  exact hn (Finset.mem_filter.mpr ⟨hm,hv'.2⟩)

theorem active_columns_subset (D : OriginalData ι) : D.active.columns⊆D.columns :=
  Finset.image_subset_image (Fintype.piFinset_subset _ _ D.active_subset)

theorem active_gaussPolynomial (D : OriginalData ι) (η : Character) (m : O)
    (t T : ℝ) (h : O) :
    gaussPolynomial Finset.univ (sourceGenerator D.active.columns)
      (sourceGenerator_supported D.active.columns) (D.active.coefficient η m t T) h=
    gaussPolynomial Finset.univ (sourceGenerator D.columns)
      (sourceGenerator_supported D.columns) (D.coefficient η m t T) h := by
  unfold coefficient
  rw [D.active_beta]
  rw [CenteredMomentLiveDomain.source_gaussPolynomial D.active.columns
    (fun I => (Real.sqrt T:ℂ)⁻¹*(D.beta I*rowWeight η m 1 1 t I)) h,
    CenteredMomentLiveDomain.source_gaussPolynomial D.columns
    (fun I => (Real.sqrt T:ℂ)⁻¹*(D.beta I*rowWeight η m 1 1 t I)) h]
  apply Finset.sum_subset (Finset.filter_subset_filter _ D.active_columns_subset)
  intro I hI hn
  have hz : D.beta I=0 := by
    by_contra hne
    have hm := CenteredMomentLiveDomain.finite_column_mem
      (Fintype.piFinset D.active.S) D.active.profile I
      (by change D.active.beta I≠0;rw [D.active_beta];exact hne)
    exact hn (Finset.mem_filter.mpr ⟨hm,(Finset.mem_filter.mp hI).2⟩)
  rw [hz,zero_mul,mul_zero,zero_mul]

theorem active_gaussEnergy (D : OriginalData ι) (η : Character) (m : O)
    (t T : ℝ) (W : 𝓢(ℝ,ℂ)) (K : ℝ) :
    gaussEnergy Finset.univ (sourceGenerator D.active.columns)
      (sourceGenerator_supported D.active.columns) (D.active.coefficient η m t T) W K=
    gaussEnergy Finset.univ (sourceGenerator D.columns)
      (sourceGenerator_supported D.columns) (D.coefficient η m t T) W K := by
  unfold gaussEnergy
  simp_rw [D.active_gaussPolynomial]

end OriginalData

open CenteredMomentFirstScale CenteredMomentCanonicalFirst CenteredMomentCompleteCommon
open CenteredMomentFirstCanonicalFamily
open CenteredMomentDescentLedger CenteredMomentCommonSupport
open CenteredMomentFirstColumns CenteredMomentRankinRadical Eisenstein

def nominalLog (I J E : Ideal O) (K X Z : ℝ) : ℝ :=
  Real.logb Z (firstNominalScale I J E K X)

theorem canonical_active_log_le (η τ : Character) (m : O) (I J : Ideal O)
    (E : Finset (CommonIndex I J)) (Z : ℝ) (hZ : 1< Z)
    (hmod : τ.modulus=η.modulus*Ideal.span {m}*Ideal.span {(72:O)}*
      Ideal.span {TruncatedPrincipalPoisson.primeSubsetGenerator (fun P : CommonIndex I J => P.val) E*activeConductor I J}) :
    0≤ Real.logb Z (τ.modulus.absNorm:ℝ) ∧
    Real.logb Z ((Ideal.span {activeConductor I J}).absNorm:ℝ)≤
      Real.logb Z (τ.modulus.absNorm:ℝ) := by
  have hpos : 0<τ.modulus.absNorm := Nat.pos_of_ne_zero
    (Ideal.absNorm_eq_zero_iff.not.mpr τ.modulus_ne_bot)
  have hd : Ideal.span {activeConductor I J}∣τ.modulus := by
    rw [hmod,←Ideal.span_singleton_mul_span_singleton]
    exact (dvd_mul_left (Ideal.span {activeConductor I J}) _).trans (dvd_mul_left _ _)
  have hN : (Ideal.absNorm (Ideal.span {activeConductor I J}):ℝ)≤(τ.modulus.absNorm:ℝ) := by
    exact_mod_cast Nat.le_of_dvd hpos (map_dvd Ideal.absNorm hd)
  refine ⟨Real.logb_nonneg hZ (by exact_mod_cast hpos),?_⟩
  exact Real.logb_le_logb_of_le hZ (active_norm_pos I J) hN

theorem pool_prime_log_range (M : Ideal O) [NeZero M] (H : Subgroup (O ⧸ M)ˣ)
    (Sbad : Finset (Ideal O)) (hbad : fixedBadPrimes⊆Sbad)
    (Z sigma : ℝ) (hZ : 1< Z) (p : O)
    (hp : p∈elementPool (primePool M H Sbad (1/2) 1 (Z^(sigma/3)))) :
    0≤ Real.logb Z (normValue p) ∧ Real.logb Z (normValue p)≤ sigma/3 := by
  have hd := elementPool_data _
    (fun Q hQ => (primePool_data M H Sbad hbad (1/2) 1 (Z^(sigma/3)) Q hQ).1)
    (fun Q hQ => (primePool_data M H Sbad hbad (1/2) 1 (Z^(sigma/3)) Q hQ).2) p hp
  have hb := PNT.AnnularPrimeMass.norm_bounds_of_mem_annularPrimeIdeals
    (by norm_num : (0:ℝ)≤1/2) (by norm_num : (1/2:ℝ)≤1)
    (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) (sigma/3)) (Finset.mem_sdiff.mp hd.2.1).1
  have hu : normValue p≤ Z^(sigma/3) := by simpa only [normValue,mul_one] using hb.2
  refine ⟨Real.logb_nonneg hZ (normValue_ge_one p hd.1.ne_zero),?_⟩
  have hh := Real.logb_le_logb_of_le hZ (normValue_pos p hd.1.ne_zero) hu
  rwa [Real.logb_rpow (zero_lt_one.trans hZ) (ne_of_gt hZ)] at hh

theorem errorRemoval_power (p : O) (hp : p≠0) (Z : ℝ) (hZ : 1< Z) (k : ℕ) :
    Z^(errorRemoval p Z k)=(normValue p)^k := by
  unfold errorRemoval
  rw [mul_comm,Real.rpow_mul_natCast (zero_lt_one.trans hZ).le,
    Real.rpow_logb (zero_lt_one.trans hZ) (ne_of_gt hZ) (normValue_pos p hp)]

theorem errorMoving_power (p : O) (hp : p≠0) (Z : ℝ) (hZ : 1< Z)
    (n : ℕ) (hn : n=0 ∨ n=5 ∨ n=6) :
    Z^(2*errorMoving p Z (n+1))=normValue (p^(2*errorMovingExponent n)) := by
  have he := errorRemoval_power p hp Z hZ 2
  have hn2 : normValue (p^2)=(normValue p)^2 := by
    unfold normValue
    rw [←Ideal.span_singleton_pow,map_pow,Nat.cast_pow]
  rcases hn with rfl|rfl|rfl
  · simpa only [errorMoving,errorMovingExponent,show ¬(0:ℕ)=5 by decide,
      show ¬(1:ℕ)=6 by decide,ite_false,Nat.reduceAdd,mul_one,hn2,errorRemoval,Nat.cast_ofNat] using he
  · norm_num [errorMoving,errorMovingExponent,normValue]
  · simpa only [errorMoving,errorMovingExponent,show ¬(6:ℕ)=5 by decide,
      show ¬(7:ℕ)=6 by decide,ite_false,Nat.reduceAdd,mul_one,hn2,errorRemoval,Nat.cast_ofNat] using he

theorem shortened_raw_exact (p : O) (hp : p≠0) (Z : ℝ) (hZ : 1< Z) (T : ℝ) (k : ℕ) :
    T/(Ideal.absNorm (Ideal.span {p}):ℝ)^k=T/Z^(errorRemoval p Z k) := by
  rw [errorRemoval_power p hp Z hZ]
  rfl


end CenteredMomentFirstAmplificationChoice

end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical BigOperators

namespace CenteredMomentFirstPhysicalSource
open Eisenstein   HeckeFamily CanonicalQuadraticSieve
open CenteredMomentSecondHeightFamily CenteredMomentCanonicalFirst CenteredMomentFirstCanonicalFamily
open CenteredMomentFirstColumns CenteredMomentHeckeColumnWindow CenteredMomentHeckeExpansion
open CenteredMomentFirstMaskedFamily CenteredMomentSourceRow CenteredMomentFirstAmplificationChoice
open CenteredMomentSourceProfileMass CenteredMomentSupportedZeroEnergy CenteredMomentCommonSupport
open CenteredMomentChildAssembly CenteredMomentAddedZeroUniform RayFourExpansion CompletedGauss
local notation "O"=> Eisenstein.O

structure FixedPair (η:Character)(C D:Ideal O)(hC:Supported C)
    (E:Finset (CommonIndex C D))(ξ₁ ξ₂:RayCharacter) where
  left : Character
  right : Character
  left_modulus : left.modulus=η.modulus*Ideal.span {fixedBadMask}*Ideal.span {(72:O)}*
    Ideal.span {TruncatedPrincipalPoisson.primeSubsetGenerator (fun P:CommonIndex C D=> P.val) E*activeConductor C D}
  right_modulus : right.modulus=η.modulus*Ideal.span {fixedBadMask}*Ideal.span {(72:O)}*
    Ideal.span {TruncatedPrincipalPoisson.primeSubsetGenerator (fun P:CommonIndex C D=> P.val) E*activeConductor C D}
  left_height : ∀I:Ideal O,Supported I→∀t:ℝ,
    heightCoeff left t I=rowWeight η fixedBadMask 1 1 t I*
      (leftCoefficient (TruncatedPrincipalPoisson.primeSubsetGenerator (fun P:CommonIndex C D=> P.val) E)
        (activeConductor C D) (finiteSexticRow (activePrime C D) (activeGood C D hC)
          (activeExponent C D)) (primaryIdealGenerator I)*rayMonoid ξ₁ (primaryIdealGenerator I))
  right_height : ∀I:Ideal O,Supported I→∀t:ℝ,
    heightCoeff right t I=rowWeight η fixedBadMask 1 1 t I*
      (rightCoefficient (TruncatedPrincipalPoisson.primeSubsetGenerator (fun P:CommonIndex C D=> P.val) E)
        (activeConductor C D) (finiteSexticRow (activePrime C D) (activeGood C D hC)
          (activeExponent C D)) (primaryIdealGenerator I)*rayMonoid ξ₂ (primaryIdealGenerator I))

def fixedPair (η:Character)(C D:Ideal O)(hC:Supported C)
    (E:Finset (CommonIndex C D))(ξ₁ ξ₂:RayCharacter):FixedPair η C D hC E ξ₁ ξ₂:=
  Classical.choice (by
    obtain ⟨τ₁,τ₂,hM₁,hM₂,h₁,h₂,_,_⟩:=exists_canonical_masked_pair η C D hC E ξ₁ ξ₂
    exact ⟨⟨τ₁,τ₂,hM₁,hM₂,h₁,h₂⟩⟩)

theorem FixedPair.conductor_caps {η:Character}{C D:Ideal O}{hC:Supported C}
    {E:Finset (CommonIndex C D)}{ξ₁ ξ₂:RayCharacter}(F:FixedPair η C D hC E ξ₁ ξ₂):
    (F.left.modulus.absNorm:ℝ)≤ fixedPresentationCost*(η.modulus.absNorm:ℝ)*
      ‖ringComplex (TruncatedPrincipalPoisson.primeSubsetGenerator (fun P:CommonIndex C D=> P.val) E)‖^2*
      ‖ringComplex (activeConductor C D)‖^2 ∧
    (F.right.modulus.absNorm:ℝ)≤ fixedPresentationCost*(η.modulus.absNorm:ℝ)*
      ‖ringComplex (TruncatedPrincipalPoisson.primeSubsetGenerator (fun P:CommonIndex C D=> P.val) E)‖^2*
      ‖ringComplex (activeConductor C D)‖^2:=
  fixed_pair_presentation_caps η F.left F.right C D E F.left_modulus F.right_modulus

variable {ι:Type*}[Fintype ι]
local instance firstFixedFamilyDecidableEq : DecidableEq (ι⊕Fin 2):=Classical.decEq _

theorem beta_coprime (s:OriginalData ι)(I:Ideal O)(h:s.beta I≠0):IsCoprime I s.R:=by
  obtain ⟨v,hv,hv0,he⟩:=finiteColumnCoefficient_witness (Fintype.piFinset s.S) s.profile I h
  rw [←he]
  by_contra hn
  apply hv0
  simp only [OriginalData.profile,profileCoefficient,hn,ite_false,mul_zero,zero_mul]

lemma extracted_mask_redundant (s:OriginalData ι)(C:Ideal O):
    maskedSource (cubicIdealGenerator s.R) (fun I=> s.beta (C*I))=(fun I=> s.beta (C*I)):=by
  apply maskedSource_eq_of_live
  intro I hI
  rw [span_cubicIdealGenerator]
  exact (beta_coprime s (C*I) hI).of_mul_left_right

theorem fixed_divisor_column (s:OriginalData ι)(η τ:Character)(C:Ideal O)
    (F:O→ℂ)(ξ:RayCharacter)
    (hτ:∀I:Ideal O,Supported I→∀t:ℝ,heightCoeff τ t I=
      rowWeight η fixedBadMask 1 1 t I*(F (primaryIdealGenerator I)*rayMonoid ξ (primaryIdealGenerator I)))
    (L I:Ideal O)(hI:Supported I)(t:ℝ):
    divisorCoefficient L (fun J:Ideal O=> primaryIdealGenerator J)
      (fun J=> s.beta (C*J)*rowWeight η (fixedBadMask*cubicIdealGenerator s.R) 1 1 t J*
        F (primaryIdealGenerator J)) ξ I=
      (if L∣I then s.beta (C*I) else 0)*heightCoeff τ t I:=by
  have hh:=divisor_column_masked η τ F ξ hτ (cubicIdealGenerator s.R) L I hI (fun J=> s.beta (C*J)) t
  rw [extracted_mask_redundant] at hh
  exact hh

end CenteredMomentFirstPhysicalSource

end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped BigOperators Classical

namespace CenteredMomentAmplificationAllocationCost
open CenteredMomentCommonAllocationSum CenteredMomentSupport 
open CenteredMomentAddedZeroUniform CenteredMomentCommonSectors
local notation "O" => Eisenstein.O
variable {ι : Type*} [Fintype ι]
local instance : DecidableEq (ι ⊕ Fin 2) := Classical.decEq _

 theorem allocation_slot_one (S : (ι ⊕ Fin 2) → Finset (Ideal O))
    (P : Ideal O) (hP : P≠0) (k : ℕ)
    (hslot : ∀ i,∀ I∈S (Sum.inl i),I≠0 ∧ IsCoprime P I)
    (B : actualAllocations S (P^k)) (i : ι) : B.val (Sum.inl i)=1 := by
  obtain ⟨v,hv,hvB⟩ := Finset.mem_image.mp (Finset.mem_filter.mp B.property).1
  have hi := Fintype.mem_piFinset.mp hv (Sum.inl i)
  have hd := hslot i (v (Sum.inl i)) hi
  have he := congrFun hvB (Sum.inl i)
  have hc : IsCoprime (P^k) (v (Sum.inl i)) := hd.2.pow_left
  have hh := supportExtract_of_disjoint (v (Sum.inl i)) (primeSupport (P^k))
    ((CenteredMomentSupport.primeSupport_disjoint_iff (pow_ne_zero k hP) hd.1).mpr hc).symm
  exact he.symm.trans hh

 theorem allocation_plain_product (S : (ι ⊕ Fin 2) → Finset (Ideal O))
    (P : Ideal O) (hP : P≠0) (k : ℕ)
    (hslot : ∀ i,∀ I∈S (Sum.inl i),I≠0 ∧ IsCoprime P I)
    (B : actualAllocations S (P^k)) : B.val (Sum.inr 0)*B.val (Sum.inr 1)=P^k := by
  have he := (Finset.mem_filter.mp B.property).2
  rw [Fintype.prod_sum_type,show (∏ i : ι,B.val (Sum.inl i))=1 by
    simp only [allocation_slot_one S P hP k hslot B,Finset.prod_const_one],one_mul,
    Fin.prod_univ_two] at he
  exact he

 theorem allocation_plain_injective (S : (ι ⊕ Fin 2) → Finset (Ideal O))
    (P : Ideal O) (hP : P≠0) (k : ℕ)
    (hslot : ∀ i,∀ I∈S (Sum.inl i),I≠0 ∧ IsCoprime P I) :
    Function.Injective (fun B : actualAllocations S (P^k) => B.val (Sum.inr 0)) := by
  intro B D he
  have hb := allocation_plain_product S P hP k hslot B
  have hd := allocation_plain_product S P hP k hslot D
  have hb0 := (allocation_data S (P^k) B (Finset.mem_filter.mp B.property).1).1 (Sum.inr 0)
  have he1 : B.val (Sum.inr 1)=D.val (Sum.inr 1) := by
    apply mul_left_cancel₀ hb0
    exact (hb.trans hd.symm).trans (congrArg (fun x => x*D.val (Sum.inr 1)) he.symm)
  apply Subtype.ext
  funext i
  cases i with
  | inl i => rw [allocation_slot_one S P hP k hslot B,allocation_slot_one S P hP k hslot D]
  | inr i => fin_cases i <;> assumption

 theorem idealDivisors_prime_power_card (P : Ideal O) (hP : Prime P) (k : ℕ) :
    (idealDivisors (P^k)).card≤ k+1 := by
  have hs : idealDivisors (P^k)⊆(Finset.range (k+1)).image (fun j => P^j) := by
    intro I hI
    obtain ⟨j,hj,he⟩ := (dvd_prime_pow hP k).mp ((mem_idealDivisors (pow_ne_zero k hP.ne_zero)).mp hI)
    have heq : I=P^j := dvd_antisymm he.dvd he.symm.dvd
    exact Finset.mem_image.mpr ⟨j,Finset.mem_range.mpr (by omega),heq.symm⟩
  exact (Finset.card_le_card hs).trans ((Finset.card_image_le).trans_eq (Finset.card_range (k+1)))

theorem actual_amplification_allocations_card (S : (ι ⊕ Fin 2) → Finset (Ideal O))
    (P : Ideal O) (hP : Prime P) (k : ℕ)
    (hslot : ∀ i,∀ I∈S (Sum.inl i),I≠0 ∧ IsCoprime P I) :
    (actualAllocations S (P^k)).card≤ k+1 := by
  let f : actualAllocations S (P^k) → idealDivisors (P^k) := fun B =>
    ⟨B.val (Sum.inr 0),(mem_idealDivisors (pow_ne_zero k hP.ne_zero)).mpr
      ⟨B.val (Sum.inr 1),(allocation_plain_product S P hP.ne_zero k hslot B).symm⟩⟩
  have hf : Function.Injective f := by
    intro B D he
    exact allocation_plain_injective S P hP.ne_zero k hslot (congrArg Subtype.val he)
  have hh := Fintype.card_le_of_injective f hf
  simp only [Fintype.card_coe] at hh
  exact hh.trans (idealDivisors_prime_power_card P hP k)

 theorem actual_error_allocations_card (S : (ι ⊕ Fin 2) → Finset (Ideal O))
    (P : Ideal O) (hP : Prime P) (k : ℕ) (hk : k=1 ∨ k=6 ∨ k=7)
    (hslot : ∀ i,∀ I∈S (Sum.inl i),I≠0 ∧ IsCoprime P I) :
    (actualAllocations S (P^k)).card≤8 := by
  have hh := actual_amplification_allocations_card S P hP k hslot
  rcases hk with rfl|rfl|rfl <;> omega

end CenteredMomentAmplificationAllocationCost

end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped BigOperators Classical

namespace CenteredMomentAmplificationAllocationScale
open CenteredMomentAmplificationAllocationCost CenteredMomentCommonAllocationSum
open CenteredMomentCommonProfile CenteredMomentSourceLiveColumn CenteredMomentCommonRawScale
open CenteredMomentAddedZeroUniform
local notation "O" => Eisenstein.O
variable {ι : Type*} [Fintype ι]

 theorem all_slots_live (S : (ι ⊕ Fin 2) → Finset (Ideal O))
    (P : Ideal O) (hP : P≠0) (k : ℕ)
    (hslot : ∀ i,∀ I∈S (Sum.inl i),I≠0 ∧ IsCoprime P I)
    (B : actualAllocations S (P^k)) : liveIndices (B : Tuple ι)=Finset.univ := by
  apply Finset.filter_eq_self.mpr
  intro i hi
  exact allocation_slot_one S P hP k hslot B i

 theorem frozenCoefficient_exact (S : (ι ⊕ Fin 2) → Finset (Ideal O))
    (P : Ideal O) (hP : P≠0) (k : ℕ)
    (hslot : ∀ i,∀ I∈S (Sum.inl i),I≠0 ∧ IsCoprime P I)
    (B : actualAllocations S (P^k)) (R : Ideal O)
    (ν : ι → Ideal O → ℂ) (Wslot : ι → ℝ → ℂ) (scale : ι → ℝ) :
    frozenCoefficient B (P^k) R ν Wslot scale=(if IsCoprime (P^k) R then 1 else 0) := by
  unfold frozenCoefficient
  have he : Finset.univ.filter (fun i => B.val (Sum.inl i)≠1)=∅ := by
    apply Finset.filter_eq_empty_iff.mpr
    intro i hi
    exact not_not_intro (allocation_slot_one S P hP k hslot B i)
  rw [he,Finset.prod_empty,one_mul]

 theorem frozenCoefficient_norm_le (S : (ι ⊕ Fin 2) → Finset (Ideal O))
    (P : Ideal O) (hP : P≠0) (k : ℕ)
    (hslot : ∀ i,∀ I∈S (Sum.inl i),I≠0 ∧ IsCoprime P I)
    (B : actualAllocations S (P^k)) (R : Ideal O)
    (ν : ι → Ideal O → ℂ) (Wslot : ι → ℝ → ℂ) (scale : ι → ℝ) :
    ‖frozenCoefficient B (P^k) R ν Wslot scale‖≤1 := by
  rw [frozenCoefficient_exact S P hP k hslot B R ν Wslot scale]
  split_ifs <;> simp

 theorem rawReduction_exact (S : (ι ⊕ Fin 2) → Finset (Ideal O))
    (P : Ideal O) (hP : P≠0) (k : ℕ)
    (hslot : ∀ i,∀ I∈S (Sum.inl i),I≠0 ∧ IsCoprime P I)
    (B : actualAllocations S (P^k)) (scale : ι → ℝ) :
    rawReduction B scale=(Ideal.absNorm P:ℝ)^k := by
  unfold rawReduction plainNorm frozenScale
  simp only [allocation_slot_one S P hP k hslot B,ite_true,Finset.prod_const_one,mul_one]
  rw [← Nat.cast_mul,← map_mul,allocation_plain_product S P hP k hslot B,map_pow,Nat.cast_pow]

 theorem live_slot_card (S : (ι ⊕ Fin 2) → Finset (Ideal O))
    (P : Ideal O) (hP : P≠0) (k : ℕ)
    (hslot : ∀ i,∀ I∈S (Sum.inl i),I≠0 ∧ IsCoprime P I)
    (B : actualAllocations S (P^k)) : Fintype.card (liveIndices (B : Tuple ι))=Fintype.card ι := by
  rw [Fintype.card_coe,all_slots_live S P hP k hslot B,Finset.card_univ]

theorem remainingRaw_exact (S : (ι ⊕ Fin 2) → Finset (Ideal O))
    (P : Ideal O) (hP : P≠0) (k : ℕ)
    (hslot : ∀ i,∀ I∈S (Sum.inl i),I≠0 ∧ IsCoprime P I)
    (B : actualAllocations S (P^k)) (scale : ι → ℝ) (Traw : ℝ) :
    remainingRaw B Traw scale=(Traw*∏ i,scale i)/(Ideal.absNorm P:ℝ)^k := by
  have hb := (allocation_data S (P^k) B (Finset.mem_filter.mp B.property).1).1
  have he := raw_scale_identity B hb Traw scale
  rw [rawReduction_exact S P hP k hslot B scale] at he
  have hn : (Ideal.absNorm P:ℝ)≠0 := by
    exact_mod_cast Ideal.absNorm_eq_zero_iff.not.mpr hP
  exact (eq_div_iff (pow_ne_zero k hn)).mpr he

end CenteredMomentAmplificationAllocationScale

end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace CenteredMomentAmplificationChildInput
open HeckeFamily CanonicalQuadraticSieve  RayFourExpansion
open CenteredMomentCommonRadialData CenteredMomentCommonAllocationSum CenteredMomentCommonProfile
open CenteredMomentSourceRectangle CenteredMomentSourceProfileMass CenteredMomentSourceMass
open CenteredMomentSourceLiveColumn CenteredMomentAddedZeroUniform CenteredMomentRemainingBox
open CenteredMomentAmplificationAllocationCost CenteredMomentAmplificationAllocationScale
open CenteredMomentHeckeColumnWindow CenteredMomentAmplificationErrorEnergy
open CenteredMomentAmplificationLiveMask CenteredMomentFirstAmplificationChoice
open CenteredMomentOriginalChildEnergy CenteredMomentSecondHeightFamily
open CenteredMomentFirstSectors CenteredMomentRectangle CenteredMomentExtraction
local notation "O" => Eisenstein.O
variable {ι : Type*} [Fintype ι]
local instance {κ : Type*} : DecidableEq κ := Classical.decEq _

def original (s : Input ι) (R seed : Ideal O) : OriginalData ι where
  S := s.pools
  R := R
  s := seed
  nu := s.ν
  slot := s.W
  lengths := s.P
  W₁ := s.W₁
  W₂ := s.W₂
  X₁ := s.X₁
  X₂ := s.X₂
  Y₁ := s.Y₁
  Y₂ := s.Y₂
  B₁ := 1
  B₂ := 1

theorem residual_ne (S : Finset (Ideal O)) (hS : ∀I∈S,I≠0)
    (B : Ideal O) (hB : B≠0) : ∀I∈residualPool B hB S,I≠0 := by
  intro I hI
  exact right_ne_zero_of_mul (hS (B*I) ((mem_residualPool B hB S I).mp hI))

theorem residual_one (S : Finset (Ideal O)) (h : (1:Ideal O)≠0) :
    residualPool 1 h S=S := by
  ext I
  simp only [mem_residualPool,one_mul]

theorem residual_coverage (S : Finset (Ideal O)) (W : ℝ→ℂ)
    (B : Ideal O) (hB : B≠0) (X Y : ℝ) (h : PlainCoverage S W 1 X Y) :
    PlainCoverage (residualPool B hB S) W 1 (X/B.absNorm) (Y/B.absNorm) := by
  have he := plainCoverage_residualPool S W 1 B hB X Y h
  intro I hi
  apply he I
  simpa only [one_mul,map_mul,map_one,Nat.cast_mul,Nat.cast_one,mul_one,div_div_eq_mul_div,mul_comm] using hi

def child (s : Input ι) (C R : Ideal O) (B : actualAllocations s.pools C)
    (τ : Character) (t : ℝ) : Input (liveIndices B.val) where
  toData := {commonData s C R B with η:=τ,t:=t}
  plain₁ := residualPool (B.val (Sum.inr 0)) (alloc_ne s C B _) s.plain₁
  plain₂ := residualPool (B.val (Sum.inr 1)) (alloc_ne s C B _) s.plain₂
  plain₁_ne := residual_ne s.plain₁ s.plain₁_ne _ _
  plain₂_ne := residual_ne s.plain₂ s.plain₂_ne _ _
  coverage₁ := residual_coverage s.plain₁ s.W₁ _ _ _ _ s.coverage₁
  coverage₂ := residual_coverage s.plain₂ s.W₂ _ _ _ _ s.coverage₂
  ν_bound := fun i=> s.ν_bound i.val
  W_bound := fun i=> s.W_bound i.val
  lower := s.lower
  upper := s.upper
  lower_pos := s.lower_pos
  lower_le := fun i=> s.lower_le i.val
  upper_ge := fun i=> s.upper_ge i.val

@[simp] theorem child_modulus (s : Input ι) (C R : Ideal O) (B : actualAllocations s.pools C)
    (τ : Character) (t : ℝ) : (child s C R B τ t).m=fixedBadMask*cubicIdealGenerator (R*C) := rfl

@[simp] theorem child_character (s : Input ι) (C R : Ideal O) (B : actualAllocations s.pools C)
    (τ : Character) (t : ℝ) : (child s C R B τ t).η=τ := rfl

@[simp] theorem child_height (s : Input ι) (C R : Ideal O) (B : actualAllocations s.pools C)
    (τ : Character) (t : ℝ) : (child s C R B τ t).t=t := rfl

theorem live_slot_one (B : Tuple ι) (i : liveIndices B) : B (Sum.inl i.val)=1 :=
  (Finset.mem_filter.mp i.property).2

theorem child_tuplePool (s : Input ι) (C R : Ideal O) (B : actualAllocations s.pools C)
    (τ : Character) (t : ℝ) :
    liveBox s.pools B (allocation_data s.pools C B (Finset.mem_filter.mp B.property).1).1 =
      Fintype.piFinset (child s C R B τ t).pools := by
  ext v
  simp only [liveBox,Fintype.mem_piFinset]
  constructor <;> intro h j
  all_goals
    cases j with
    | inl i =>
      have hi:=h (Sum.inl i)
      simpa only [remainingSets,child,commonData,Input.pools,Sum.elim_inl,live_slot_one B.val i,
        residual_one] using hi
    | inr j =>
      fin_cases j
      · simpa [remainingSets,child,commonData,Input.pools] using h (Sum.inr 0)
      · simpa [remainingSets,child,commonData,Input.pools] using h (Sum.inr 1)

theorem child_profile (s : Input ι) (C R seed : Ideal O) (B : actualAllocations s.pools C)
    (τ : Character) (t : ℝ) :
    maskedLiveProfile B C R seed s.ν s.W s.P s.W₁ s.W₂
      s.X₁ s.X₂ s.Y₁ s.Y₂ 1 1 = (original (child s C R B τ t) (R*C) seed).profile := by
  funext v
  simp only [maskedLiveProfile,OriginalData.profile,original,child,commonData,
    profileCoefficient,one_mul,idealRectangle_extract]
  rfl

theorem prime_slot_one (s : Input ι) (Q : Ideal O) (hQ : Q≠0) (k : ℕ)
    (hslot : ∀i,∀I∈s.slots i,IsCoprime Q I)
    (B : actualAllocations s.pools (Q^k)) (i : ι) : B.val (Sum.inl i)=1 :=
  allocation_slot_one s.pools Q hQ k
    (fun i I hI=>⟨(s.prime i I hI).ne_zero,hslot i I hI⟩) B i

theorem prime_slots_live (s : Input ι) (Q : Ideal O) (hQ : Q≠0) (k : ℕ)
    (hslot : ∀i,∀I∈s.slots i,IsCoprime Q I)
    (B : actualAllocations s.pools (Q^k)) : liveIndices B.val=Finset.univ :=
  all_slots_live s.pools Q hQ k (fun i I hI=>⟨(s.prime i I hI).ne_zero,hslot i I hI⟩) B

theorem prime_plain_norm_product (s : Input ι) (Q : Ideal O) (hQ : Q≠0) (k : ℕ)
    (hslot : ∀i,∀I∈s.slots i,IsCoprime Q I)
    (B : actualAllocations s.pools (Q^k)) :
    (B.val (Sum.inr 0)).absNorm*(B.val (Sum.inr 1)).absNorm=Q.absNorm^k := by
  rw [←map_mul,allocation_plain_product s.pools Q hQ k
    (fun i I hI=>⟨(s.prime i I hI).ne_zero,hslot i I hI⟩) B,map_pow]

theorem child_products (s : Input ι) (Q : Ideal O) (hQ : Q≠0) (k : ℕ)
    (hslot : ∀i,∀I∈s.slots i,IsCoprime Q I) (R : Ideal O)
    (B : actualAllocations s.pools (Q^k)) (τ : Character) (t : ℝ) :
    (child s (Q^k) R B τ t).X₁*(child s (Q^k) R B τ t).X₂=
      (s.X₁*s.X₂)/(Q.absNorm:ℝ)^k ∧
    (child s (Q^k) R B τ t).Y₁*(child s (Q^k) R B τ t).Y₂=
      (s.X₁*s.X₂)/(Q.absNorm:ℝ)^k := by
  have hnorm : ((B.val (Sum.inr 0)).absNorm:ℝ)*(B.val (Sum.inr 1)).absNorm=(Q.absNorm:ℝ)^k := by
    exact_mod_cast prime_plain_norm_product s Q hQ k hslot B
  change (s.X₁/_)*(s.X₂/_)=_ ∧ (s.Y₁/_)*(s.Y₂/_)=_
  rw [div_mul_div_comm,div_mul_div_comm,hnorm,s.same_product]
  exact ⟨rfl,rfl⟩

theorem child_volume (s : Input ι) (Q : Ideal O) (hQ : Q≠0) (k : ℕ)
    (hslot : ∀i,∀I∈s.slots i,IsCoprime Q I) (R : Ideal O)
    (B : actualAllocations s.pools (Q^k)) (τ : Character) (t : ℝ) :
    volume (child s (Q^k) R B τ t)=volume s/(Q.absNorm:ℝ)^k := by
  change (s.X₁/(B.val (Sum.inr 0)).absNorm)*(s.X₂/(B.val (Sum.inr 1)).absNorm)*
    (∏i:liveIndices B.val,s.P i.val)=_
  rw [div_mul_div_comm]
  exact remainingRaw_exact s.pools Q hQ k
    (fun i I hI=>⟨(s.prime i I hI).ne_zero,hslot i I hI⟩) B s.P (s.X₁*s.X₂)

theorem child_slot_card (s : Input ι) (Q : Ideal O) (hQ : Q≠0) (k : ℕ)
    (hslot : ∀i,∀I∈s.slots i,IsCoprime Q I)
    (B : actualAllocations s.pools (Q^k)) : Fintype.card (liveIndices B.val)=Fintype.card ι :=
  live_slot_card s.pools Q hQ k (fun i I hI=>⟨(s.prime i I hI).ne_zero,hslot i I hI⟩) B

theorem child_slot_scale_ge_one (s : Input ι) (hs : ∀i,1≤ s.P i)
    (C R : Ideal O) (B : actualAllocations s.pools C) (τ : Character) (t : ℝ) :
    ∀i,1≤(child s C R B τ t).P i := fun i=> hs i.val

theorem child_plain_annuli (s : Input ι) (C R : Ideal O) (B : actualAllocations s.pools C)
    (τ : Character) (t a₁ a₂ b₁ b₂ : ℝ)
    (h₁ : Function.support s.W₁⊆Set.Icc a₁ b₁)
    (h₂ : Function.support s.W₂⊆Set.Icc a₂ b₂) :
    Function.support (child s C R B τ t).W₁⊆Set.Icc a₁ b₁ ∧
    Function.support (child s C R B τ t).W₂⊆Set.Icc a₂ b₂ := ⟨h₁,h₂⟩

theorem child_columns (s : Input ι) (C R seed : Ideal O) (B : actualAllocations s.pools C)
    (τ : Character) (t : ℝ) :
    finiteColumns (liveBox s.pools B (allocation_data s.pools C B (Finset.mem_filter.mp B.property).1).1)=
      (original (child s C R B τ t) (R*C) seed).columns ∧
    finiteColumnCoefficient
      (liveBox s.pools B (allocation_data s.pools C B (Finset.mem_filter.mp B.property).1).1)
      (maskedLiveProfile B C R seed s.ν s.W s.P s.W₁ s.W₂ s.X₁ s.X₂ s.Y₁ s.Y₂ 1 1)=
      (original (child s C R B τ t) (R*C) seed).beta := by
  dsimp only [OriginalData.columns, OriginalData.beta, original]
  rw [child_tuplePool s C R B τ t,child_profile s C R seed B τ t]
  dsimp only [original]
  constructor
  · apply congrArg finiteColumns
    ext v
    simp only [Fintype.mem_piFinset]
  · apply congrArg (fun S => finiteColumnCoefficient S _)
    ext v
    simp only [Fintype.mem_piFinset]

theorem child_gauss_source (s : Input ι) (C R seed : Ideal O) (B : actualAllocations s.pools C)
    (τ : Character) (t : ℝ) (W : 𝓢(ℝ,ℂ)) (K : ℝ) :
    sourceGaussEnergy
      (finiteColumns (liveBox s.pools B (allocation_data s.pools C B (Finset.mem_filter.mp B.property).1).1))
      (finiteColumnCoefficient
        (liveBox s.pools B (allocation_data s.pools C B (Finset.mem_filter.mp B.property).1).1)
        (maskedLiveProfile B C R seed s.ν s.W s.P s.W₁ s.W₂ s.X₁ s.X₂ s.Y₁ s.Y₂ 1 1))
      (heightCoeff τ t) W K=
    sourceGaussEnergy (original (child s C R B τ t) (R*C) seed).columns
      (original (child s C R B τ t) (R*C) seed).beta
      (heightCoeff (child s C R B τ t).η (child s C R B τ t).t) W K := by
  obtain ⟨hcols,hcoeff⟩ := child_columns s C R seed B τ t
  rw [hcols,hcoeff]
  rfl

def normalizedGaussSource (s : Input ι) (R seed : Ideal O) (W : 𝓢(ℝ,ℂ)) (K : ℝ) : ℝ :=
  (sourceGaussEnergy (original s R seed).columns (original s R seed).beta
    (heightCoeff s.η s.t) W K).re / volume s

def childNormalizedGaussSource (s : Input ι) (C R seed : Ideal O)
    (B : actualAllocations s.pools C) (τ : Character) (t : ℝ) (W : 𝓢(ℝ,ℂ)) (K : ℝ) : ℝ :=
  normalizedGaussSource (child s C R B τ t) (R*C) seed W K

theorem original_childEnergy_eq_inputs (s : Input ι) (R seed : Ideal O)
    (τ : RayCharacter→Character) (p : O) (hp : p≠0)
    (hslot : ∀i,∀I∈s.slots i,IsCoprime (Ideal.span {p}) I)
    (n : ℕ) (t K : ℝ) :
    (original s R seed).childEnergy τ p n t (volume s) K=
      (16*(n+2:ℝ)*localErrorCost p n)*
        ∑χ:RayCharacter,∑B:actualAllocations s.pools ((Ideal.span {p})^(n+1)),
          childNormalizedGaussSource s ((Ideal.span {p})^(n+1)) R seed B (τ χ) t ballProfile K := by
  have hQ : (Ideal.span {p}:Ideal O)≠0 := Ideal.span_singleton_eq_bot.not.mpr hp
  unfold OriginalData.childEnergy
  simp only [original,Finset.sum_div]
  apply congrArg (fun x : ℝ => (16*(n+2:ℝ)*localErrorCost p n)*x)
  apply Finset.sum_congr rfl
  intro χ hχ
  apply Finset.sum_congr rfl
  intro B hB
  unfold childNormalizedGaussSource normalizedGaussSource
  rw [child_volume s (Ideal.span {p}) hQ (n+1) hslot R B (τ χ) t,
    child_gauss_source s ((Ideal.span {p})^(n+1)) R seed B (τ χ) t ballProfile K]

end CenteredMomentAmplificationChildInput

end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace CenteredMomentFirstPhysicalOriginalMask
open HeckeFamily CanonicalQuadraticSieve  CenteredMomentCommonRadialData
open CenteredMomentAmplificationChildInput CenteredMomentFirstPhysicalSource
open CenteredMomentFirstMaskedFamily CenteredMomentSecondHeightFamily
open CenteredMomentOriginalCommonHarmonic CenteredMomentCommonSupport
open CenteredMomentFirstRetainedNorm CenteredMomentFirstSourceReduction
open CenteredMomentCanonicalFirst CenteredMomentFirstSectors
local notation "O" => Eisenstein.O
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
local instance : DecidableEq (ι ⊕ Fin 2) := Classical.decEq _

omit [DecidableEq ι] in
lemma original_coefficient (s : Input ι) (R seed C I : Ideal O)
    (hI : Supported I) (t : ℝ) :
    CenteredMomentFirstPhysicalSource.coefficient s.η (fixedBadMask*cubicIdealGenerator R) 1 t
      (CenteredMomentOriginalCommonHarmonic.coefficient s R seed) C I =
    CenteredMomentFirstPhysicalSource.coefficient s.η fixedBadMask 1 t
      (CenteredMomentOriginalCommonHarmonic.coefficient s R seed) C I := by
  unfold CenteredMomentFirstPhysicalSource.coefficient
  by_cases h : CenteredMomentOriginalCommonHarmonic.coefficient s R seed (C*I)=0
  · simp [h]
  · have hc : IsCoprime I R :=
      (beta_coprime (original s R seed) (C*I) h).of_mul_left_right
    have hw := rowWeight_mask_factor s.η (cubicIdealGenerator R) I hI t
    change CenteredMomentHeckeExpansion.rowWeight s.η (fixedBadMask*cubicIdealGenerator R) 1 1 t I =
      idealMask (cubicIdealGenerator R) I * CenteredMomentHeckeExpansion.rowWeight s.η fixedBadMask 1 1 t I at hw
    rw [hw]
    simp only [idealMask, span_cubicIdealGenerator, hc, ite_true, one_mul]

omit [DecidableEq ι] in
theorem original_block (s : Input ι) (R seed : Ideal O) (t : ℝ)
    (S : Finset (Ideal O)) (C D : Ideal O) (hC : Supported C) (hD : Supported D)
    (E : Finset (CommonIndex C D)) (rows : Finset O) (W : 𝓢(ℝ,ℂ))
    (V : Fin 4→ℝ→ℂ) (K K₀ H₀ A₀ B₀ : ℝ) :
    block s.η (fixedBadMask*cubicIdealGenerator R) 1 t S
      (CenteredMomentOriginalCommonHarmonic.coefficient s R seed)
      C D hC hD E rows W V K K₀ H₀ A₀ B₀ =
    block s.η fixedBadMask 1 t S
      (CenteredMomentOriginalCommonHarmonic.coefficient s R seed)
      C D hC hD E rows W V K K₀ H₀ A₀ B₀ := by
  unfold block
  apply congrArg (fun z : ℂ => inactiveWeight C D E * z)
  apply Finset.sum_congr rfl
  intro h hh
  apply Finset.sum_congr rfl
  intro a ha
  apply Finset.sum_congr rfl
  intro b hb
  dsimp only
  rw [original_coefficient s R seed C a (column_supported C C hC.1 S a) t,
    original_coefficient s R seed D b (column_supported C D hD.1 S b) t]

omit [DecidableEq ι] in
lemma original_sector (s : Input ι) (R seed : Ideal O) (t : ℝ)
    (S : Finset (Ideal O)) (C D : Ideal O) (hC : Supported C) (hD : Supported D)
    (W : 𝓢(ℝ,ℂ)) (K X Z ξ : ℝ) :
    sector s R seed (fixedBadMask*cubicIdealGenerator R) 1 t S C D hC hD W K X Z ξ =
    sector s R seed fixedBadMask 1 t S C D hC hD W K X Z ξ := by
  unfold sector
  simp_rw [original_block]

omit [DecidableEq ι] in
lemma original_sectorMass (s : Input ι) (R seed : Ideal O) (t : ℝ)
    (S : Finset (Ideal O)) (C D : Ideal O) (hC : Supported C) (hD : Supported D)
    (W : 𝓢(ℝ,ℂ)) (K X Z ξ : ℝ) :
    sectorMass s R seed (fixedBadMask*cubicIdealGenerator R) 1 t S C D hC hD W K X Z ξ =
    sectorMass s R seed fixedBadMask 1 t S C D hC hD W K X Z ξ := by
  unfold sectorMass
  simp_rw [original_block]

omit [DecidableEq ι] in
theorem original_physicalMass (s : Input ι) (R seed : Ideal O)
    (W : 𝓢(ℝ,ℂ)) (K Z ξ : ℝ) :
    physicalMass s R seed (fixedBadMask*cubicIdealGenerator R) 1 W K Z ξ =
    physicalMass s R seed fixedBadMask 1 W K Z ξ := by
  unfold physicalMass
  simp_rw [original_sectorMass]

end CenteredMomentFirstPhysicalOriginalMask

end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace CenteredMomentFirstPhysicalZeroRadius
open HeckeFamily CanonicalQuadraticSieve 
open CenteredMomentCommonRadialData CenteredMomentOriginalCommonHarmonic
open CenteredMomentFirstPhysicalSource CenteredMomentFirstRetainedNorm
open CenteredMomentFirstSourceReduction CenteredMomentCommonSupport
open CenteredMomentCanonicalFirst CenteredMomentFirstSectors
open CenteredMomentOriginalChildEnergy CenteredMomentGaussEnergy
local notation "O" => Eisenstein.O
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
local instance : DecidableEq (ι ⊕ Fin 2) := Classical.decEq _

omit [DecidableEq ι] in
lemma coefficient_zero (s : Input ι) (R seed : Ideal O)
    (h₁ : s.W₁ 0=0) (h₂ : s.W₂ 0=0) (hH : sourceRadius s≤0) (I : Ideal O) :
    CenteredMomentOriginalCommonHarmonic.coefficient s R seed I=0 := by
  by_contra h
  obtain ⟨hI,hN⟩ := original_column_norm s R seed I h₁ h₂ h
  have hn : 1≤(I.absNorm:ℝ) := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr hI)
  linarith

omit [DecidableEq ι] in
lemma block_zero (s : Input ι) (R seed : Ideal O)
    (h₁ : s.W₁ 0=0) (h₂ : s.W₂ 0=0) (hH : sourceRadius s≤0)
    (m A : O) (t : ℝ) (S : Finset (Ideal O)) (C D : Ideal O)
    (hC : Supported C) (hD : Supported D) (E : Finset (CommonIndex C D))
    (rows : Finset O) (W : 𝓢(ℝ,ℂ)) (V : Fin 4→ℝ→ℂ) (K K₀ H₀ A₀ B₀ : ℝ) :
    block s.η m A t S (CenteredMomentOriginalCommonHarmonic.coefficient s R seed)
      C D hC hD E rows W V K K₀ H₀ A₀ B₀=0 := by
  simp [block,CenteredMomentFirstPhysicalSource.coefficient,coefficient_zero s R seed h₁ h₂ hH]

omit [DecidableEq ι] in
lemma sectorMass_zero (s : Input ι) (R seed : Ideal O)
    (h₁ : s.W₁ 0=0) (h₂ : s.W₂ 0=0) (hH : sourceRadius s≤0)
    (m A : O) (t : ℝ) (S : Finset (Ideal O)) (C D : Ideal O)
    (hC : Supported C) (hD : Supported D) (W : 𝓢(ℝ,ℂ)) (K X Z ξ : ℝ) :
    sectorMass s R seed m A t S C D hC hD W K X Z ξ=0 := by
  unfold sectorMass
  simp only [block_zero s R seed h₁ h₂ hH,norm_zero,Finset.sum_const_zero]

omit [DecidableEq ι] in
theorem physicalMass_zero (s : Input ι) (R seed : Ideal O)
    (h₁ : s.W₁ 0=0) (h₂ : s.W₂ 0=0) (hH : sourceRadius s≤0)
    (m A : O) (W : 𝓢(ℝ,ℂ)) (K Z ξ : ℝ) :
    physicalMass s R seed m A W K Z ξ=0 := by
  unfold physicalMass
  simp only [sectorMass_zero s R seed h₁ h₂ hH,Finset.sum_const_zero]

omit [DecidableEq ι] in
theorem sourceGaussEnergy_zero (s : Input ι) (R seed : Ideal O)
    (h₁ : s.W₁ 0=0) (h₂ : s.W₂ 0=0) (hH : sourceRadius s≤0)
    (S : Finset (Ideal O)) (f : Ideal O→ℂ) (W : 𝓢(ℝ,ℂ)) (K : ℝ) :
    sourceGaussEnergy S (CenteredMomentOriginalCommonHarmonic.coefficient s R seed) f W K=0 := by
  simp [sourceGaussEnergy,gaussEnergy,gaussPolynomial,coefficient_zero s R seed h₁ h₂ hH]

end CenteredMomentFirstPhysicalZeroRadius

end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped BigOperators Classical
namespace CenteredMomentRankinScale
open  CenteredMomentRankinRadical CenteredMomentRankinLabels
local notation "O" => Eisenstein.O

theorem source_partition_count (B δ : ℝ) (hB : 0 ≤ B) (hδ : 0 < δ) :
    ∃ C : ℝ,0 < C ∧ ∀ (Z p s₀ : ℝ),1 ≤ Z → 0 ≤ p → p ≤ B →
      ∀ (s : Ideal O),Squarefree s → s ≠ 0 → Z^s₀ ≤ (Ideal.absNorm s:ℝ) →
      ∀ S : Finset ((Ideal O × Ideal O) × Finset (Ideal O)),
      (∀ v ∈ S,v.1.1 ≠ 0 ∧ v.1.2 ≠ 0) →
      (∀ v ∈ S,primeSupport v.1.1=primeSupport v.1.2) →
      (∀ v ∈ S,s ∣ v.1.1 ∧ s ∣ v.1.2) →
      (∀ v ∈ S,v.2 ⊆ primeSupport (commonRadical v.1.1 v.1.2)) →
      (∀ v ∈ S,(Ideal.absNorm v.1.1:ℝ) ≤ Z^B ∧ (Ideal.absNorm v.1.2:ℝ) ≤ Z^B) →
      (∀ v ∈ S,(Ideal.absNorm (commonRadical v.1.1 v.1.2):ℝ) ≤ Z^p) →
      (S.card:ℝ) ≤ C*Z^(p-s₀+δ) := by
  let a : ℝ := δ/(3*(B+1))
  have ha : 0 < a := div_pos hδ (by positivity)
  obtain ⟨C,hC,hcount⟩ := partitioned_common_pair_count a a ha ha
  refine ⟨C,hC,?_⟩
  intro Z p s₀ hZ hp hpB s hs hs0 hNs S hS heq hdiv hpart hN hR
  have hZ0 : 0 < Z := zero_lt_one.trans_le hZ
  have hb := hcount s hs hs0 S hS heq hdiv hpart (Z^B) (Z^B) (Z^p)
    (Real.rpow_pos_of_pos hZ0 _) (Real.rpow_pos_of_pos hZ0 _)
    (Real.rpow_pos_of_pos hZ0 _) hN hR
  have hpower : B*a+B*a+p*(1+a) ≤ p+δ := by
    have he : a*(3*(B+1))=δ := by dsimp only [a]; field_simp
    have hpa := mul_le_mul_of_nonneg_right hpB ha.le
    nlinarith
  calc
    _ ≤ C*(Z^B)^a*(Z^B)^a*(Z^p)^(1+a)/(Ideal.absNorm s:ℝ) := hb
    _ ≤ C*(Z^B)^a*(Z^B)^a*(Z^p)^(1+a)/(Z^s₀) :=
      div_le_div_of_nonneg_left (by positivity) (Real.rpow_pos_of_pos hZ0 _) hNs
    _ = C*Z^(B*a+B*a+p*(1+a)-s₀) := by
      rw [← Real.rpow_mul hZ0.le,← Real.rpow_mul hZ0.le]
      rw [div_eq_mul_inv,← Real.rpow_neg hZ0.le]
      simp only [sub_eq_add_neg]
      rw [Real.rpow_add hZ0,Real.rpow_add hZ0,Real.rpow_add hZ0]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hZ (by linarith)) hC.le

end CenteredMomentRankinScale

end

end

end GaloisForLFunctions.MetaplecticMobiusDescent.CubicEisenstein
