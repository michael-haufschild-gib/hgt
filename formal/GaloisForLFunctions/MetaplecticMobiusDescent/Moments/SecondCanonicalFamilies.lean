/-
Second canonical families adapted from OpenAI's formalization, Apache-2.0.
See LICENSE and NOTICE in the parent directory for source attribution.
-/
import GaloisForLFunctions.MetaplecticMobiusDescent.Moments.PartitionsAndForcingIdeals
import GaloisForLFunctions.MetaplecticMobiusDescent.Moments.CommonAllocations

/-!
# Second canonical families

Fixed bad masks of the second height family, common and nonunit frequency generators, sector
pools and moving coefficients; transport of fixed inducing rows to second family
presentations.
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
open scoped BigOperators Classical SchwartzMap

namespace CenteredMomentSecondSourceEnergy
open HeckeFamily CanonicalQuadraticSieve CanonicalRowCompletion CompletedGauss
open CenteredMomentGaussEnergy CenteredMomentSourceRow CenteredMomentLiveDomain
open CenteredMomentOriginalChildEnergy CenteredMomentHeckeColumnWindow
open CenteredMomentFirstSectors CenteredMomentCommonSectors 
local notation "O" => Eisenstein.O

def secondSourceKernel (I J : Ideal O) (W : 𝓢(ℝ,ℂ)) (K : ℝ) : ℂ :=
  ∑' h : O,(primaryGaussRow I h*star (primaryGaussRow J h))*
    W (‖ringComplex h‖^2/K)

theorem heightCoeff_mul (τ : Character) (t : ℝ) (I J : Ideal O) :
    heightCoeff τ t (I*J)=heightCoeff τ t I*heightCoeff τ t J := by
  have hpow : ((Ideal.absNorm I:ℂ)*(Ideal.absNorm J:ℂ))^(Complex.I*t)=
      (Ideal.absNorm I:ℂ)^(Complex.I*t)*(Ideal.absNorm J:ℂ)^(Complex.I*t) := by
    exact_mod_cast Complex.mul_cpow_ofReal_nonneg
      (Nat.cast_nonneg (Ideal.absNorm I):(0:ℝ)≤ Ideal.absNorm I)
      (Nat.cast_nonneg (Ideal.absNorm J):(0:ℝ)≤ Ideal.absNorm J) (Complex.I*t)
  simp only [heightCoeff,map_mul,Nat.cast_mul,hpow]
  ring

theorem source_energy_common_sectors (τ : Character) (t : ℝ)
    (S : Finset (Ideal O)) (β : Ideal O → ℂ) (W : 𝓢(ℝ,ℂ)) (K : ℝ) (hK : 0< K) :
    sourceGaussEnergy S β (heightCoeff τ t) W K=
      ∑ p∈commonLabels (supportedColumns S) (supportedColumns S),
        ∑ q∈pairSector p.1 p.2 (supportedColumns S) (supportedColumns S),
          ((β q.1*heightCoeff τ t q.1)*star (β q.2*heightCoeff τ t q.2))*
            secondSourceKernel q.1 q.2 W K := by
  rw [sourceGaussEnergy,gaussEnergy_expand _ _ _ _ W K hK]
  have hk (I J : supportedColumns S) :
      (∑' h : O,(gaussRow (sourceGenerator S I) (sourceGenerator_supported S I) h*
        star (gaussRow (sourceGenerator S J) (sourceGenerator_supported S J) h))*
          W (‖ringComplex h‖^2/K))=secondSourceKernel I J W K := by
    unfold secondSourceKernel
    apply tsum_congr
    intro h
    simp only [primaryGaussRow,dif_pos (Finset.mem_filter.mp I.property).2,
      dif_pos (Finset.mem_filter.mp J.property).2,sourceGenerator]
  simp_rw [hk]
  let F := fun I J : Ideal O =>
    ((β I*heightCoeff τ t I)*star (β J*heightCoeff τ t J))*secondSourceKernel I J W K
  change (∑ I : supportedColumns S,∑ J : supportedColumns S,F I J)=_
  have he (I : Ideal O) : (∑ J : supportedColumns S,F I J)=∑ J∈supportedColumns S,F I J :=
    Finset.sum_coe_sort (supportedColumns S) (F I)
  simp_rw [he]
  rw [Finset.sum_coe_sort (supportedColumns S) (fun I => ∑ J∈supportedColumns S,F I J)]
  exact sum_common_sectors _ _ _

theorem source_sector_independent_columns (τ : Character) (t : ℝ)
    (S : Finset (Ideal O)) (β : Ideal O → ℂ) (C D : Ideal O)
    (hC : C≠0) (hD : D≠0) (hCD : primeSupport C=primeSupport D)
    (W : 𝓢(ℝ,ℂ)) (K : ℝ) :
    (∑ q∈pairSector C D (supportedColumns S) (supportedColumns S),
      ((β q.1*heightCoeff τ t q.1)*star (β q.2*heightCoeff τ t q.2))*secondSourceKernel q.1 q.2 W K)=
      heightCoeff τ t C*star (heightCoeff τ t D)*
        ∑ a∈residualPool C hC (supportedColumns S),∑ b∈residualPool D hD (supportedColumns S),
          if IsCoprime C a ∧ IsCoprime C b ∧ IsCoprime a b then
            ((β (C*a)*heightCoeff τ t a)*star (β (D*b)*heightCoeff τ t b))*
              secondSourceKernel (C*a) (D*b) W K else 0 := by
  rw [pairSector_double_sum C D hC hD hCD _ _
    (fun I hI => (Finset.mem_filter.mp hI).2.1)
    (fun I hI => (Finset.mem_filter.mp hI).2.1)
    (fun I J => ((β I*heightCoeff τ t I)*star (β J*heightCoeff τ t J))*secondSourceKernel I J W K),Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a ha
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro b hb
  split_ifs <;> simp only [heightCoeff_mul,star_mul,mul_zero]
  ring

end CenteredMomentSecondSourceEnergy

end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped BigOperators Classical SchwartzMap

namespace CenteredMomentSecondSourcePoisson
open HeckeFamily CanonicalQuadraticSieve CompletedGauss  SchwartzPlanePoisson
open CenteredMomentGaussEnergy CenteredMomentSourceRow CenteredMomentLiveDomain
open CenteredMomentOriginalChildEnergy CenteredMomentHeckeColumnWindow
open CenteredMomentFourier CenteredMomentPoisson
open CenteredMomentSecondSourceEnergy CenteredMomentSupportedCorrelation CenteredMomentRowNorm
local notation "O" => Eisenstein.O

theorem secondSourceKernel_poisson (I J : Ideal O) (hI : Supported I) (hJ : Supported J)
    (W : 𝓢(ℝ,ℂ)) (K : ℝ) (hK : 0< K) :
    secondSourceKernel I J W K=
      (K:ℂ)/((Real.sqrt (Ideal.absNorm I:ℝ):ℂ)*(Real.sqrt (Ideal.absNorm J:ℝ):ℂ))*
        ∑' h : O,actualCorrelation (primaryIdealGenerator I) (primaryIdealGenerator J)
          (by rw [primary_span_supported I hI];exact hI)
          (by rw [primary_span_supported J hJ];exact hJ) (-h)*
          paperRadialFourier W (K*‖ringComplex h‖^2/
            ‖ringComplex (primaryIdealGenerator I*primaryIdealGenerator J)‖^2) := by
  unfold secondSourceKernel
  simp only [primaryGaussRow,dif_pos hI,dif_pos hJ,gaussRow]
  rw [sextic_gauss_pair_poisson _ _ ((supported_span_primaryIdealGenerator_iff I).mpr hI)
    ((supported_span_primaryIdealGenerator_iff J).mpr hJ) W K hK]
  simp only [primary_span_supported I hI,primary_span_supported J hJ]

theorem sourceGaussEnergy_poisson (τ : Character) (t : ℝ)
    (S : Finset (Ideal O)) (β : Ideal O → ℂ)
    (W : 𝓢(ℝ,ℂ)) (K : ℝ) (hK : 0< K) :
    sourceGaussEnergy S β (heightCoeff τ t) W K=
      ∑ I : supportedColumns S,∑ J : supportedColumns S,
        ((β I*heightCoeff τ t I)*star (β J*heightCoeff τ t J))*
          ((K:ℂ)/((Real.sqrt (Ideal.absNorm (I:Ideal O):ℝ):ℂ)*(Real.sqrt (Ideal.absNorm (J:Ideal O):ℝ):ℂ)))*
            ∑' h : O,actualCorrelation (sourceGenerator S I) (sourceGenerator S J)
              (sourceGenerator_supported S I) (sourceGenerator_supported S J) (-h)*
              paperRadialFourier W (K*‖ringComplex h‖^2/
                ‖ringComplex (sourceGenerator S I*sourceGenerator S J)‖^2) := by
  rw [sourceGaussEnergy,gaussEnergy_poisson _ _ _ _ W K hK]
  apply Finset.sum_congr rfl
  intro I hI
  apply Finset.sum_congr rfl
  intro J hJ
  simp only [sourceGenerator,primary_span_supported I (Finset.mem_filter.mp I.property).2,
    primary_span_supported J (Finset.mem_filter.mp J.property).2]
  ring

end CenteredMomentSecondSourcePoisson

end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped BigOperators Classical SchwartzMap
namespace CenteredMomentPlainEnergy
open CanonicalQuadraticSieve CenteredMomentRowNorm 
open CanonicalRowCompletion
local notation "O" => Eisenstein.O

theorem rowEnergy_summable {α : Type*} (S : Finset α) (a : α → O)
    (ha : ∀ i, Supported (Ideal.span {a i})) (c : α → ℂ)
    (W : 𝓢(ℝ, ℂ)) (K : ℝ) (hK : 0 < K) :
    Summable (fun z : O => ((‖rowPolynomial S a c z‖^2 : ℝ) : ℂ) *
      W (‖ringComplex z‖^2/K)) := by
  have hs (i j : α) := (row_pair_summable (a i) (a j) (ha i) (ha j) W K hK).mul_left
    (c i * star (c j))
  simp only [mul_assoc] at hs
  simp only [rowPolynomial_norm_sq,Finset.sum_mul,mul_assoc]
  exact (hasSum_sum (fun i _ => (hasSum_sum (fun j _ => (hs i j).hasSum)))).summable

theorem finite_energy_le_rowEnergy {α : Type*} (S : Finset α) (a : α → O)
    (ha : ∀ i, Supported (Ideal.span {a i})) (c : α → ℂ)
    (W : 𝓢(ℝ, ℂ)) (K : ℝ) (hK : 0 < K) (rows : Finset O)
    (hW : ∀ z : O, 0 ≤ (W (‖ringComplex z‖^2/K)).re)
    (hmajor : ∀ z ∈ rows, 1 ≤ (W (‖ringComplex z‖^2/K)).re) :
    (∑ z ∈ rows, ‖rowPolynomial S a c z‖^2) ≤ (CenteredMomentRowNorm.rowEnergy S a c W K).re := by
  have hs := Complex.hasSum_re (rowEnergy_summable S a ha c W K hK).hasSum
  change HasSum _ (CenteredMomentRowNorm.rowEnergy S a c W K).re at hs
  simp only [Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero] at hs
  calc
    _ ≤ ∑ z ∈ rows, ‖rowPolynomial S a c z‖^2*(W (‖ringComplex z‖^2/K)).re := by
      apply Finset.sum_le_sum
      intro z hz
      exact le_mul_of_one_le_right (sq_nonneg _) (hmajor z hz)
    _ ≤ _ := sum_le_hasSum rows (fun z _ => mul_nonneg (sq_nonneg _) (hW z)) hs

theorem finite_negative_energy_le_rowEnergy {α : Type*} (S : Finset α) (a : α → O)
    (ha : ∀ i, Supported (Ideal.span {a i})) (c : α → ℂ)
    (W : 𝓢(ℝ, ℂ)) (K : ℝ) (hK : 0 < K) (rows : Finset O)
    (hW : ∀ z : O, 0 ≤ (W (‖ringComplex z‖^2/K)).re)
    (hmajor : ∀ z ∈ rows, 1 ≤ (W (‖ringComplex z‖^2/K)).re) :
    (∑ z ∈ rows, ‖rowPolynomial S a c (-z)‖^2) ≤ (CenteredMomentRowNorm.rowEnergy S a c W K).re := by
  have he := finite_energy_le_rowEnergy S a ha c W K hK (rows.image Neg.neg) hW (by
    intro z hz
    obtain ⟨w,hw,rfl⟩ := Finset.mem_image.mp hz
    simpa only [map_neg,norm_neg] using hmajor w hw)
  rwa [Finset.sum_image (fun x hx y hy hxy => neg_injective hxy)] at he

end CenteredMomentPlainEnergy

end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped BigOperators Classical SchwartzMap
namespace CenteredMomentPlainChildEnergy
open CanonicalQuadraticSieve CanonicalRowCompletion CenteredMomentRowNorm CenteredMomentPlainEnergy CenteredMomentCauchy
open CenteredMomentSmooth
local notation "O" => Eisenstein.O

theorem leftColumn_eq_rowPolynomial {α : Type*} (S : Finset α) (a : α → O)
    (c : α → ℂ)
    (V : ℝ → ℂ) (u : α → ℝ) (z : O) (t : ℝ) :
    leftColumn S (fun i => c i * idealRowHom z (Ideal.span {a i})) V u t =
      rowPolynomial S a (fun i => c i * columnPhase V (u i) t) z := by
  unfold leftColumn rowPolynomial
  apply Finset.sum_congr rfl
  intro i hi
  ring

theorem rightColumn_eq_star_rowPolynomial {α : Type*} (S : Finset α) (a : α → O)
    (c : α → ℂ)
    (V : ℝ → ℂ) (u : α → ℝ) (z : O) (t : ℝ) :
    rightColumn S (fun i => c i * idealRowHom z (Ideal.span {a i})) V u t =
      star (rowPolynomial S a (fun i => c i * star (columnPhase V (u i) t)) z) := by
  simp only [rightColumn, rowPolynomial, star_sum, star_mul, star_star]
  apply Finset.sum_congr rfl
  intro i hi
  ring

theorem whole_kernel_plain_child_bound (W : 𝓢(ℝ, ℂ)) (V : Fin 4 → ℝ → ℂ)
    (M : Fin 4 → ℝ) (hM : ∀ i, 0 ≤ M i)
    (hV : ∀ i y, V i y ≠ 0 → |y| ≤ M i) (A J₁ J₂ : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ R : ℝ, 0 < R →
      ∀ {α β : Type*} (rows : Finset O) (S : Finset α) (T : Finset β)
        (a : α → O) (b : β → O)
        (_ha : ∀ i, Supported (Ideal.span {a i}))
        (_hb : ∀ j, Supported (Ideal.span {b j}))
        (c : α → ℂ) (d : β → ℂ) (u : α → ℝ) (v : β → ℝ)
        (ρ x : O → ℝ) (η : O → ℂ),
      (∀ z ∈ rows, ‖η z‖ ≤ 1) →
      (∀ z ∈ rows, ‖V 0 (ρ z)‖ ≤ 1) → (∀ z ∈ rows, ‖V 1 (x z)‖ ≤ 1) →
      ∀ (U : 𝓢(ℝ, ℂ)) (K : ℝ), 0 < K →
      (∀ z : O, 0 ≤ (U (‖ringComplex z‖ ^ 2 / K)).re) →
      (∀ z ∈ rows, 1 ≤ (U (‖ringComplex z‖ ^ 2 / K)).re) →
      ∀ E₁ E₂ : ℝ, 0 ≤ E₁ → 0 ≤ E₂ →
      (∀ t : ℝ, (CenteredMomentRowNorm.rowEnergy S a (fun i => c i * columnPhase (V 2) (u i) t) U K).re ≤
        (E₁ * (1 + ‖t‖) ^ J₁) ^ 2) →
      (∀ t : ℝ, (CenteredMomentRowNorm.rowEnergy T b (fun j => d j * star (columnPhase (V 3) (v j) t)) U K).re ≤
        (E₂ * (1 + ‖t‖) ^ J₂) ^ 2) →
      (1 + R) ^ A * ‖∑ z ∈ rows, η z *
        (∑ i ∈ S, ∑ j ∈ T,
          ((c i * idealRowHom z (Ideal.span {a i})) * star (d j * idealRowHom (-z) (Ideal.span {b j}))) *
            wholeKernel W V R (ρ z) (x z) (u i) (v j))‖ ≤ C * (E₁ * E₂) := by
  obtain ⟨C, hC, hbound⟩ := whole_kernel_row_estimate W V M hM hV A (J₁ + J₂)
  refine ⟨C, hC, ?_⟩
  intro R hR α β rows S T a b ha hb c d u v ρ x η hη hV₀ hV₁ U K hK hU hmajor
    E₁ E₂ hE₁ hE₂ hleft hright
  apply hbound R hR rows S T
    (fun z i => c i * idealRowHom z (Ideal.span {a i}))
    (fun z j => d j * idealRowHom (-z) (Ideal.span {b j})) u v ρ x η hη hV₀ hV₁
    (E₁ * E₂) (mul_nonneg hE₁ hE₂)
  intro t
  have hL := (finite_energy_le_rowEnergy S a ha
    (fun i => c i * columnPhase (V 2) (u i) t) U K hK rows hU hmajor).trans (hleft t)
  have hR' := (finite_negative_energy_le_rowEnergy T b hb
    (fun j => d j * star (columnPhase (V 3) (v j) t)) U K hK rows hU hmajor).trans (hright t)
  have hl : Real.sqrt (∑ z ∈ rows,
      ‖rowPolynomial S a (fun i => c i * columnPhase (V 2) (u i) t) z‖ ^ 2) ≤
      E₁ * (1 + ‖t‖) ^ J₁ := (Real.sqrt_le_iff).mpr ⟨by positivity, hL⟩
  have hr : Real.sqrt (∑ z ∈ rows,
      ‖rowPolynomial T b (fun j => d j * star (columnPhase (V 3) (v j) t)) (-z)‖ ^ 2) ≤
      E₂ * (1 + ‖t‖) ^ J₂ := (Real.sqrt_le_iff).mpr ⟨by positivity, hR'⟩
  simp only [leftColumn_eq_rowPolynomial, rightColumn_eq_star_rowPolynomial, norm_star]
  calc
    _ ≤ (E₁ * (1 + ‖t‖) ^ J₁) * (E₂ * (1 + ‖t‖) ^ J₂) :=
      mul_le_mul hl hr (Real.sqrt_nonneg _) (by positivity)
    _ = _ := by rw [pow_add]; ring

end CenteredMomentPlainChildEnergy

end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped BigOperators Classical SchwartzMap

namespace CenteredMomentSecondDescent
open CanonicalRowCompletion CanonicalQuadraticSieve CenteredMomentSupportedCorrelation
open CenteredMomentChildAssembly CenteredMomentMobiusRegroup CenteredMomentFixedRay
open CenteredMomentRowNorm CenteredMomentSmooth CenteredMomentPlainChildEnergy RayFourExpansion
local notation "O" => Eisenstein.O

private theorem weighted_norm_sum {α : Type*} (S : Finset α) (a f : α → ℂ)
    (r : ℝ) (hr : 0 ≤ r) (B : α → ℝ)
    (hB : ∀ i ∈ S, r*‖f i‖ ≤ B i) :
    r*‖∑ i ∈ S, a i*f i‖ ≤ ∑ i ∈ S, ‖a i‖*B i := by
  calc
    _ ≤ r*∑ i ∈ S, ‖a i*f i‖ := mul_le_mul_of_nonneg_left (norm_sum_le _ _) hr
    _ = ∑ i ∈ S, ‖a i‖*(r*‖f i‖) := by simp only [Finset.mul_sum,norm_mul]; congr 1; funext i; ring
    _ ≤ _ := Finset.sum_le_sum (fun i hi => mul_le_mul_of_nonneg_left (hB i hi) (norm_nonneg _))

theorem actual_row_children {α β : Type*} (rows : Finset O) (S : Finset α) (T : Finset β)
    (D E : O) (a : α → O) (b : β → O)
    (hD : Supported (Ideal.span {D})) (hE : Supported (Ideal.span {E}))
    (ha : ∀ i, Supported (Ideal.span {a i})) (hb : ∀ j, Supported (Ideal.span {b j}))
    (hpD : lambda^2 ∣ D-1)
    (hpE : lambda^2 ∣ E-1)
    (hpa : ∀ i, lambda^2 ∣ a i-1)
    (hpb : ∀ j, lambda^2 ∣ b j-1)
    (hcopA : ∀ i, IsCoprime (D*E) (a i)) (hcopB : ∀ j, IsCoprime (D*E) (b j))
    (q : O → ℂ) (c : α → ℂ) (d : β → ℂ) (K : O → α → β → ℂ) :
    (∑ z ∈ rows, q z * ∑ i ∈ S, ∑ j ∈ T,
      (if IsCoprime (a i) (b j) then
        actualCorrelation (D*a i) (E*b j)
          (supported_mul_elements _ _ hD (ha i)) (supported_mul_elements _ _ hE (hb j)) z
        else 0) * (c i*star (d j))*K z i j) =
      ∑ L ∈ divisorPool T (fun j => Ideal.span {b j}),
        (UniqueFactorizationMonoid.moebius L : ℂ) *
          ∑ χ : RayCharacter, ∑ ξ : RayCharacter, pairCoeff (phaseTable D E) χ ξ *
            ∑ z ∈ rows, (q z*actualCorrelation D E hD hE z) *
              ∑ i ∈ S, ∑ j ∈ T,
                ((divisorCoefficient L a c χ i*idealRowHom z (Ideal.span {a i})) *
                  star (divisorCoefficient L b d (ξ⁻¹) j*idealRowHom (-z) (Ideal.span {b j}))) * K z i j := by
  simp_rw [finite_correlation_children S T D E a b hD hE ha hb hpD hpE hpa hpb hcopA hcopB]
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm (s := rows)]
  apply Finset.sum_congr rfl
  intro L hL
  rw [Finset.sum_comm (s := rows)]
  apply Finset.sum_congr rfl
  intro χ hχ
  rw [Finset.sum_comm (s := rows)]
  apply Finset.sum_congr rfl
  intro ξ hξ
  apply Finset.sum_congr rfl
  intro z hz
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  ring

theorem finite_ray_divisor_bound (L : Finset (Ideal O)) (D E : O)
    (F : Ideal O → RayCharacter → RayCharacter → ℂ)
    (r C : ℝ) (hr : 0 ≤ r) (hC : 0 ≤ C) (B₁ B₂ : Ideal O → ℝ)
    (hB₁ : ∀ I ∈ L, 0 ≤ B₁ I) (hB₂ : ∀ I ∈ L, 0 ≤ B₂ I)
    (hF : ∀ I ∈ L, ∀ χ ξ, r*‖F I χ ξ‖ ≤ C*(B₁ I*B₂ I)) :
    r*‖∑ I ∈ L, (UniqueFactorizationMonoid.moebius I : ℂ)*
      ∑ χ : RayCharacter, ∑ ξ : RayCharacter, pairCoeff (phaseTable D E) χ ξ * F I χ ξ‖ ≤
      (256*C)*∑ I ∈ L, ‖(UniqueFactorizationMonoid.moebius I : ℂ)‖*(B₁ I*B₂ I) := by
  have he (I : Ideal O) (hI : I ∈ L) :
      r*‖∑ χ : RayCharacter, ∑ ξ : RayCharacter,
        pairCoeff (phaseTable D E) χ ξ*F I χ ξ‖ ≤ (256*C)*(B₁ I*B₂ I) := by
    calc
      _ ≤ ∑ χ : RayCharacter, ∑ ξ : RayCharacter,
          ‖pairCoeff (phaseTable D E) χ ξ‖*(C*(B₁ I*B₂ I)) := by
        have h := weighted_norm_sum Finset.univ (fun _ : RayCharacter => (1 : ℂ))
          (fun χ => ∑ ξ : RayCharacter, pairCoeff (phaseTable D E) χ ξ*F I χ ξ) r hr
          (fun χ => ∑ ξ : RayCharacter, ‖pairCoeff (phaseTable D E) χ ξ‖*(C*(B₁ I*B₂ I)))
          (fun χ _ => weighted_norm_sum Finset.univ _ _ r hr _ (fun ξ _ => hF I hI χ ξ))
        simpa only [one_mul,norm_one] using h
      _ = (∑ χ : RayCharacter, ∑ ξ : RayCharacter, ‖pairCoeff (phaseTable D E) χ ξ‖)*
          (C*(B₁ I*B₂ I)) := by simp only [Finset.sum_mul]
      _ ≤ _ := by
        have h := mul_le_mul_of_nonneg_right (phaseTable_mass D E)
          (mul_nonneg hC (mul_nonneg (hB₁ I hI) (hB₂ I hI)))
        convert h using 1 <;> first | rfl | ring
  have h := weighted_norm_sum L (fun I => (UniqueFactorizationMonoid.moebius I : ℂ))
    (fun I => ∑ χ : RayCharacter, ∑ ξ : RayCharacter, pairCoeff (phaseTable D E) χ ξ*F I χ ξ)
    r hr (fun I => (256*C)*(B₁ I*B₂ I)) he
  convert h using 1
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro I hI
  ring

theorem whole_kernel_actual_second_bound (W : 𝓢(ℝ, ℂ)) (V : Fin 4 → ℝ → ℂ)
    (M : Fin 4 → ℝ) (hM : ∀ i, 0 ≤ M i)
    (hV : ∀ i y, V i y ≠ 0 → |y| ≤ M i) (A J₁ J₂ : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ R : ℝ, 0 < R →
      ∀ {α β : Type*} (rows : Finset O) (S : Finset α) (T : Finset β)
        (D E : O) (a : α → O) (b : β → O)
        (hD : Supported (Ideal.span {D})) (hE : Supported (Ideal.span {E}))
        (ha : ∀ i, Supported (Ideal.span {a i})) (hb : ∀ j, Supported (Ideal.span {b j})),
      (lambda^2 ∣ D-1) →
      (lambda^2 ∣ E-1) →
      (∀ i, lambda^2 ∣ a i-1) →
      (∀ j, lambda^2 ∣ b j-1) →
      (∀ i, IsCoprime (D*E) (a i)) → (∀ j, IsCoprime (D*E) (b j)) →
      ∀ (q : O → ℂ) (c : α → ℂ) (d : β → ℂ) (u : α → ℝ) (v : β → ℝ)
        (ρ x : O → ℝ),
      (∀ z ∈ rows, ‖q z*actualCorrelation D E hD hE z‖ ≤ 1) →
      (∀ z ∈ rows, ‖V 0 (ρ z)‖ ≤ 1) → (∀ z ∈ rows, ‖V 1 (x z)‖ ≤ 1) →
      ∀ (U : 𝓢(ℝ, ℂ)) (K : ℝ), 0 < K →
      (∀ z : O, 0 ≤ (U (‖ringComplex z‖^2/K)).re) →
      (∀ z ∈ rows, 1 ≤ (U (‖ringComplex z‖^2/K)).re) →
      ∀ (B₁ B₂ : Ideal O → ℝ),
      (∀ L ∈ divisorPool T (fun j => Ideal.span {b j}), 0 ≤ B₁ L) →
      (∀ L ∈ divisorPool T (fun j => Ideal.span {b j}), 0 ≤ B₂ L) →
      (∀ L ∈ divisorPool T (fun j => Ideal.span {b j}), ∀ χ : RayCharacter, ∀ t : ℝ,
        (CenteredMomentRowNorm.rowEnergy S a (fun i => divisorCoefficient L a c χ i*columnPhase (V 2) (u i) t) U K).re ≤
          (B₁ L*(1+‖t‖)^J₁)^2) →
      (∀ L ∈ divisorPool T (fun j => Ideal.span {b j}), ∀ ξ : RayCharacter, ∀ t : ℝ,
        (CenteredMomentRowNorm.rowEnergy T b (fun j => divisorCoefficient L b d ξ j*star (columnPhase (V 3) (v j) t)) U K).re ≤
          (B₂ L*(1+‖t‖)^J₂)^2) →
      (1+R)^A * ‖∑ z ∈ rows, q z * ∑ i ∈ S, ∑ j ∈ T,
        (if IsCoprime (a i) (b j) then
          actualCorrelation (D*a i) (E*b j)
            (supported_mul_elements _ _ hD (ha i)) (supported_mul_elements _ _ hE (hb j)) z
          else 0) * (c i*star (d j))*wholeKernel W V R (ρ z) (x z) (u i) (v j)‖ ≤
        C*∑ L ∈ divisorPool T (fun j => Ideal.span {b j}),
          ‖(UniqueFactorizationMonoid.moebius L : ℂ)‖*(B₁ L*B₂ L) := by
  obtain ⟨C,hC,hbound⟩ := whole_kernel_plain_child_bound W V M hM hV A J₁ J₂
  refine ⟨256*C,mul_nonneg (by norm_num) hC,?_⟩
  intro R hR α β rows S T D E a b hD hE ha hb hpD hpE hpa hpb hcopA hcopB
    q c d u v ρ x hq hV₀ hV₁ U K hK hU hmajor B₁ B₂ hB₁ hB₂ hleft hright
  rw [actual_row_children rows S T D E a b hD hE ha hb hpD hpE hpa hpb hcopA hcopB]
  apply finite_ray_divisor_bound _ D E _ ((1+R)^A) C (by positivity) hC B₁ B₂ hB₁ hB₂
  intro L hL χ ξ
  exact hbound R hR rows S T a b ha hb
    (divisorCoefficient L a c χ) (divisorCoefficient L b d (ξ⁻¹)) u v ρ x
    (fun z => q z*actualCorrelation D E hD hE z) hq hV₀ hV₁ U K hK hU hmajor
    (B₁ L) (B₂ L) (hB₁ L hL) (hB₂ L hL) (hleft L hL χ) (hright L hL (ξ⁻¹))

end CenteredMomentSecondDescent

end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped BigOperators Classical SchwartzMap

namespace CenteredMomentSecondScaled
open CanonicalRowCompletion CanonicalQuadraticSieve CenteredMomentSupportedCorrelation
open CenteredMomentChildAssembly CenteredMomentMobiusRegroup CenteredMomentFixedRay
open CenteredMomentRowNorm CenteredMomentSmooth CenteredMomentPlainChildEnergy RayFourExpansion
open CenteredMomentSecondDescent CenteredMomentProductCRT CenteredMomentUnequal CenteredMomentPartition
local notation "O" => Eisenstein.O

def movingCoefficient {α : Type*} (A : O) (a : α → O) (c : α → ℂ) (i : α) : ℂ :=
  c i*idealRowHom A (Ideal.span {a i})

theorem divisorCoefficient_moving {α : Type*} (L : Ideal O) (A : O) (a : α → O)
    (c : α → ℂ) (χ : RayCharacter) (i : α) :
    divisorCoefficient L a (movingCoefficient A a c) χ i =
      divisorCoefficient L a c χ i*idealRowHom A (Ideal.span {a i}) := by
  unfold divisorCoefficient movingCoefficient
  split_ifs <;> ring

theorem actual_child_column {α : Type*} (L : Ideal O) (η : HeckeFamily.Character)
    (χ : RayCharacter) (m A₀ h : O) (a : α → O) (β : α → ℂ) (i : α)
    (ha : Supported (Ideal.span {a i}))
    (hp : lambda^2 ∣ a i-1) :
    divisorCoefficient L a (movingCoefficient A₀ a
      (fun j => β j*HeckeFamily.elementCoeff η (a j)*coprimalityMask m (a j))) χ i *
      idealRowHom h (Ideal.span {a i}) =
    (if L ∣ Ideal.span {a i} then β i else 0) *
      rowTwist (HeckeRowClosure.elementHom (CenteredMomentChildRows.childCharacter η χ))
        m 1 (A₀*h) (a i) := by
  rw [CenteredMomentChildRows.child_row_primary η χ m A₀ h (a i) ha hp]
  simp only [divisorCoefficient,movingCoefficient,idealRowHom_argument_mul]
  split_ifs <;> ring

theorem scaled_partition_scalar {ι : Type*} [Fintype ι] [DecidableEq ι]
    (p : ι → O) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hp : ∀ i, Supported (Ideal.span {p i}))
    (hg : ∀ i, lambda ∉ Ideal.span {p i})
    (hchar : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2)
    (hcop : Pairwise (Function.onFun IsCoprime p))
    (c d : ι → ℕ) (hc : ∀ i, 1 ≤ c i) (hd : ∀ i, 1 ≤ d i)
    (U : Finset ι) (part : O → Prop) (V₀ h : O)
    (hpart : part (V₀*h) → ∀ i ∈ U, c i=d i ∧ ¬6∣c i ∧
      ¬p i∣CenteredMomentPartition.dividedFrequency p c d (V₀*h) i) :
    ‖(if part (V₀*h) then (1:ℂ)/(CenteredMomentPartition.partitionNormalizer p c d U : ℂ) else 0) *
      actualCorrelation (∏ i, p i^c i) (∏ i, p i^d i)
        (supported_product _ (fun i => supported_power (p i) (hp i) (c i)))
        (supported_product _ (fun i => supported_power (p i) (hp i) (d i)))
        (((∏ i, p i^min (c i) (d i))*V₀)*h)‖ ≤ 1 := by
  have hb := CenteredMomentPartition.normalized_partition_norm_le_one
    p hp hg hchar hcop c d hc hd U part (V₀*h) hpart
  by_cases hh : part (V₀*h)
  · simpa only [if_pos hh,one_div,div_eq_mul_inv,mul_assoc,mul_comm,mul_left_comm,one_mul] using hb
  · simp only [if_neg hh,zero_mul,norm_zero,zero_le_one]

theorem actual_scaled_row_children {α β : Type*} (rows : Finset O) (S : Finset α) (T : Finset β)
    (D E A₀ : O) (a : α → O) (b : β → O)
    (hD : Supported (Ideal.span {D})) (hE : Supported (Ideal.span {E}))
    (ha : ∀ i, Supported (Ideal.span {a i})) (hb : ∀ j, Supported (Ideal.span {b j}))
    (hpD : lambda^2 ∣ D-1)
    (hpE : lambda^2 ∣ E-1)
    (hpa : ∀ i, lambda^2 ∣ a i-1)
    (hpb : ∀ j, lambda^2 ∣ b j-1)
    (hcopA : ∀ i, IsCoprime (D*E) (a i)) (hcopB : ∀ j, IsCoprime (D*E) (b j))
    (q : O → ℂ) (c : α → ℂ) (d : β → ℂ) (K : O → α → β → ℂ) :
    (∑ z ∈ rows, q z * ∑ i ∈ S, ∑ j ∈ T,
      (if IsCoprime (a i) (b j) then
        actualCorrelation (D*a i) (E*b j)
          (supported_mul_elements _ _ hD (ha i)) (supported_mul_elements _ _ hE (hb j)) (A₀*z)
        else 0) * (c i*star (d j))*K z i j) =
      ∑ L ∈ divisorPool T (fun j => Ideal.span {b j}),
        (UniqueFactorizationMonoid.moebius L : ℂ) *
          ∑ χ : RayCharacter, ∑ ξ : RayCharacter, pairCoeff (phaseTable D E) χ ξ *
            ∑ z ∈ rows, (q z*actualCorrelation D E hD hE (A₀*z)) *
              ∑ i ∈ S, ∑ j ∈ T,
                ((divisorCoefficient L a (movingCoefficient A₀ a c) χ i*idealRowHom z (Ideal.span {a i})) *
                  star (divisorCoefficient L b (movingCoefficient A₀ b d) (ξ⁻¹) j*idealRowHom (-z) (Ideal.span {b j}))) * K z i j := by
  simp_rw [finite_correlation_children S T D E a b hD hE ha hb hpD hpE hpa hpb hcopA hcopB]
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm (s := rows)]
  apply Finset.sum_congr rfl
  intro L hL
  rw [Finset.sum_comm (s := rows)]
  apply Finset.sum_congr rfl
  intro χ hχ
  rw [Finset.sum_comm (s := rows)]
  apply Finset.sum_congr rfl
  intro ξ hξ
  apply Finset.sum_congr rfl
  intro z hz
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  rw [show -(A₀*z)=A₀*(-z) by ring]
  simp only [idealRowHom_argument_mul,divisorCoefficient_moving,star_mul]
  ring

theorem whole_kernel_scaled_second_bound (W : 𝓢(ℝ, ℂ)) (V : Fin 4 → ℝ → ℂ)
    (M : Fin 4 → ℝ) (hM : ∀ i, 0 ≤ M i)
    (hV : ∀ i y, V i y ≠ 0 → |y| ≤ M i) (A J₁ J₂ : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ R : ℝ, 0 < R →
      ∀ {α β : Type*} (rows : Finset O) (S : Finset α) (T : Finset β)
        (D E A₀ : O) (a : α → O) (b : β → O)
        (hD : Supported (Ideal.span {D})) (hE : Supported (Ideal.span {E}))
        (ha : ∀ i, Supported (Ideal.span {a i})) (hb : ∀ j, Supported (Ideal.span {b j})),
      (lambda^2 ∣ D-1) →
      (lambda^2 ∣ E-1) →
      (∀ i, lambda^2 ∣ a i-1) →
      (∀ j, lambda^2 ∣ b j-1) →
      (∀ i, IsCoprime (D*E) (a i)) → (∀ j, IsCoprime (D*E) (b j)) →
      ∀ (q : O → ℂ) (c : α → ℂ) (d : β → ℂ) (u : α → ℝ) (v : β → ℝ)
        (ρ x : O → ℝ),
      (∀ z ∈ rows, ‖q z*actualCorrelation D E hD hE (A₀*z)‖ ≤ 1) →
      (∀ z ∈ rows, ‖V 0 (ρ z)‖ ≤ 1) → (∀ z ∈ rows, ‖V 1 (x z)‖ ≤ 1) →
      ∀ (U : 𝓢(ℝ, ℂ)) (K : ℝ), 0 < K →
      (∀ z : O, 0 ≤ (U (‖ringComplex z‖^2/K)).re) →
      (∀ z ∈ rows, 1 ≤ (U (‖ringComplex z‖^2/K)).re) →
      ∀ (B₁ B₂ : Ideal O → ℝ),
      (∀ L ∈ divisorPool T (fun j => Ideal.span {b j}), 0 ≤ B₁ L) →
      (∀ L ∈ divisorPool T (fun j => Ideal.span {b j}), 0 ≤ B₂ L) →
      (∀ L ∈ divisorPool T (fun j => Ideal.span {b j}), ∀ χ : RayCharacter, ∀ t : ℝ,
        (CenteredMomentRowNorm.rowEnergy S a (fun i => divisorCoefficient L a (movingCoefficient A₀ a c) χ i*columnPhase (V 2) (u i) t) U K).re ≤
          (B₁ L*(1+‖t‖)^J₁)^2) →
      (∀ L ∈ divisorPool T (fun j => Ideal.span {b j}), ∀ ξ : RayCharacter, ∀ t : ℝ,
        (CenteredMomentRowNorm.rowEnergy T b (fun j => divisorCoefficient L b (movingCoefficient A₀ b d) ξ j*star (columnPhase (V 3) (v j) t)) U K).re ≤
          (B₂ L*(1+‖t‖)^J₂)^2) →
      (1+R)^A * ‖∑ z ∈ rows, q z * ∑ i ∈ S, ∑ j ∈ T,
        (if IsCoprime (a i) (b j) then
          actualCorrelation (D*a i) (E*b j)
            (supported_mul_elements _ _ hD (ha i)) (supported_mul_elements _ _ hE (hb j)) (A₀*z)
          else 0) * (c i*star (d j))*wholeKernel W V R (ρ z) (x z) (u i) (v j)‖ ≤
        C*∑ L ∈ divisorPool T (fun j => Ideal.span {b j}),
          ‖(UniqueFactorizationMonoid.moebius L : ℂ)‖*(B₁ L*B₂ L) := by
  obtain ⟨C,hC,hbound⟩ := whole_kernel_plain_child_bound W V M hM hV A J₁ J₂
  refine ⟨256*C,mul_nonneg (by norm_num) hC,?_⟩
  intro R hR α β rows S T D E A₀ a b hD hE ha hb hpD hpE hpa hpb hcopA hcopB
    q c d u v ρ x hq hV₀ hV₁ U K hK hU hmajor B₁ B₂ hB₁ hB₂ hleft hright
  rw [actual_scaled_row_children rows S T D E A₀ a b hD hE ha hb hpD hpE hpa hpb hcopA hcopB]
  apply finite_ray_divisor_bound _ D E _ ((1+R)^A) C (by positivity) hC B₁ B₂ hB₁ hB₂
  intro L hL χ ξ
  exact hbound R hR rows S T a b ha hb
    (divisorCoefficient L a (movingCoefficient A₀ a c) χ) (divisorCoefficient L b (movingCoefficient A₀ b d) (ξ⁻¹)) u v ρ x
    (fun z => q z*actualCorrelation D E hD hE (A₀*z)) hq hV₀ hV₁ U K hK hU hmajor
    (B₁ L) (B₂ L) (hB₁ L hL) (hB₂ L hL) (hleft L hL χ) (hright L hL (ξ⁻¹))

end CenteredMomentSecondScaled

end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped BigOperators Classical

namespace CenteredMomentSecondSectorColumns
open HeckeFamily CanonicalQuadraticSieve CanonicalRowCompletion CompletedGauss
open CenteredMomentSourceRow CenteredMomentHeckeColumnWindow CenteredMomentSecondSourceEnergy
open CenteredMomentFirstSectors CenteredMomentFirstSectorTransform CenteredMomentCommonSectors
open CenteredMomentSecondScaled CenteredMomentSupportedCorrelation CenteredMomentChildAssembly
open CenteredMomentFixedRay CenteredMomentMobiusRegroup RayFourExpansion
local notation "O" => Eisenstein.O

def sectorPool (C : Ideal O) (hC : C≠0) (S : Finset (Ideal O)) : Finset (Ideal O) :=
  (residualPool C hC (supportedColumns S)).filter (IsCoprime C)

theorem sectorPool_supported (C : Ideal O) (hC : C≠0) (S : Finset (Ideal O))
    (a : sectorPool C hC S) : Supported (a:Ideal O) :=
  residualPool_supported C hC S ⟨a,(Finset.mem_filter.mp a.property).1⟩

def sectorElement (C : Ideal O) (hC : C≠0) (S : Finset (Ideal O))
    (a : sectorPool C hC S) : O := primaryIdealGenerator a

theorem sectorElement_span (C : Ideal O) (hC : C≠0) (S : Finset (Ideal O))
    (a : sectorPool C hC S) : Ideal.span {sectorElement C hC S a}=a :=
  primary_span_supported a (sectorPool_supported C hC S a)

theorem sectorElement_supported (C : Ideal O) (hC : C≠0) (S : Finset (Ideal O))
    (a : sectorPool C hC S) : Supported (Ideal.span {sectorElement C hC S a}) := by
  rw [sectorElement_span]
  exact sectorPool_supported C hC S a

theorem sectorElement_primary (C : Ideal O) (hC : C≠0) (S : Finset (Ideal O))
    (a : sectorPool C hC S) : lambda^2∣sectorElement C hC S a-1 :=
  (primaryIdealGenerator_spec a (supported_primaryIdealGenerator_ne_zero a (sectorPool_supported C hC S a))).2

theorem coprime_of_same_support (C D a : Ideal O) (hC : C≠0) (hD : D≠0) (ha : a≠0)
    (hCD : primeSupport C=primeSupport D) :
    IsCoprime C a ↔ IsCoprime D a := by
  change primeSupport C=primeSupport D at hCD
  rw [←CenteredMomentSupport.primeSupport_disjoint_iff hC ha,
    ←CenteredMomentSupport.primeSupport_disjoint_iff hD ha,hCD]

theorem sectorElement_coprime (C D : Ideal O) (hC : Supported C) (hD : Supported D)
    (hCD : primeSupport C=primeSupport D)
    (S : Finset (Ideal O)) (a : sectorPool C hC.1 S) :
    IsCoprime (primaryIdealGenerator C*primaryIdealGenerator D) (sectorElement C hC.1 S a) := by
  apply (Ideal.isCoprime_span_singleton_iff _ _).mp
  rw [←Ideal.span_singleton_mul_span_singleton,primary_span_supported C hC,
    primary_span_supported D hD,sectorElement_span]
  have hc := (Finset.mem_filter.mp a.property).2
  exact hc.mul_left ((coprime_of_same_support C D a hC.1 hD.1
    (sectorPool_supported C hC.1 S a).1 hCD).mp hc)

theorem independent_sector_pools (C D : Ideal O) (hC : C≠0) (hD : D≠0)
    (hCD : primeSupport C=primeSupport D)
    (S : Finset (Ideal O)) (F : Ideal O → Ideal O → ℂ) :
    (∑ a∈residualPool C hC (supportedColumns S),∑ b∈residualPool D hD (supportedColumns S),
      if IsCoprime C a ∧ IsCoprime C b ∧ IsCoprime a b then F a b else 0)=
    ∑ a : sectorPool C hC S,∑ b : sectorPool D hD S,
      if IsCoprime (a:Ideal O) (b:Ideal O) then F a b else 0 := by
  have he (a : Ideal O) :
      (∑ b : sectorPool D hD S,if IsCoprime a (b:Ideal O) then F a b else 0)=
      ∑ b∈sectorPool D hD S,if IsCoprime a b then F a b else 0 :=
    Finset.sum_coe_sort (sectorPool D hD S) (fun b : Ideal O => if IsCoprime a b then F a b else 0)
  simp_rw [he]
  rw [Finset.sum_coe_sort (sectorPool C hC S)
    (fun a => ∑ b∈sectorPool D hD S,if IsCoprime a b then F a b else 0)]
  simp only [sectorPool,Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro a ha
  by_cases hCa : IsCoprime C a
  · simp only [hCa,ite_true,true_and]
    apply Finset.sum_congr rfl
    intro b hb
    have hcb := coprime_of_same_support C D b hC hD
      (residualPool_supported D hD S ⟨b,hb⟩).1 hCD
    by_cases hDb : IsCoprime D b <;> simp [hcb,hDb]
  · simp only [hCa,ite_false,false_and,Finset.sum_const_zero]

end CenteredMomentSecondSectorColumns

end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped BigOperators Classical

namespace CenteredMomentSecondCanonical
open HeckeFamily CanonicalQuadraticSieve CompletedGauss 
open CenteredMomentCanonicalFirst CenteredMomentCompleteCommon CenteredMomentFirstCanonicalFamily
open CenteredMomentSecondLedger CenteredMomentPartition CenteredMomentSupportedCorrelation
open CenteredMomentSourceRow UniqueFactorizationMonoid CenteredMomentSupport CenteredMomentUnequal
local notation "O" => Eisenstein.O

def commonPrime (C D : Ideal O) (P : CommonIndex C D) : O := primaryIdealGenerator P.val

theorem commonPrime_supported_ideal (C D : Ideal O) (hC : Supported C) (P : CommonIndex C D) :
    Supported P.val :=
  supported_of_dvd P.val C hC
    (dvd_of_mem_normalizedFactors (Multiset.mem_toFinset.mp (Finset.mem_inter.mp P.property).1))

theorem commonPrime_span (C D : Ideal O) (hC : Supported C) (P : CommonIndex C D) :
    Ideal.span {commonPrime C D P}=P.val :=
  primary_span_supported P.val (commonPrime_supported_ideal C D hC P)

theorem commonPrime_supported (C D : Ideal O) (hC : Supported C) (P : CommonIndex C D) :
    Supported (Ideal.span {commonPrime C D P}) := by
  rw [commonPrime_span C D hC P]
  exact commonPrime_supported_ideal C D hC P

theorem commonPrime_coprime (C D : Ideal O) (hC : Supported C) :
    Pairwise (Function.onFun IsCoprime (commonPrime C D)) := by
  intro P Q hPQ
  change IsCoprime (commonPrime C D P) (commonPrime C D Q)
  rw [←Ideal.isCoprime_span_singleton_iff,commonPrime_span C D hC P,commonPrime_span C D hC Q]
  exact Ideal.isCoprime_of_isMaximal (fun he=> hPQ (Subtype.ext he))

theorem commonPart_eq_left (C D : Ideal O) (hC : C≠0)
    (hCD : primeSupport C=primeSupport D) : commonPart C D=C := by
  have hs : commonSupport C D=commonSupport C C := by
    change primeSupport C∩primeSupport D=
      primeSupport C∩primeSupport C
    rw [hCD]
  calc
    commonPart C D=commonPart C C := by unfold commonPart;rw [hs]
    _=C := commonPart_self C hC

theorem left_ideal_product (C D : Ideal O) (hC : Supported C)
    (hCD : primeSupport C=primeSupport D) :
    (∏ P : CommonIndex C D,Ideal.span {commonPrime C D P}^leftExponent C D P)=C := by
  simp_rw [commonPrime_span C D hC]
  rw [←commonPart_left_product,commonPart_eq_left C D hC.1 hCD]

theorem right_ideal_product (C D : Ideal O) (hC : Supported C) (hD : Supported D)
    (hCD : primeSupport C=primeSupport D) :
    (∏ P : CommonIndex C D,Ideal.span {commonPrime C D P}^rightExponent C D P)=D := by
  simp_rw [commonPrime_span C D hC]
  rw [←commonPart_right_product,commonPart_eq_left D C hD.1 hCD.symm]

theorem left_generator_product (C D : Ideal O) (hC : Supported C)
    (hCD : primeSupport C=primeSupport D) :
    (∏ P : CommonIndex C D,commonPrime C D P^leftExponent C D P)=primaryIdealGenerator C := by
  have he := congrArg primaryIdealGeneratorHom (left_ideal_product C D hC hCD)
  simp_rw [commonPrime_span C D hC] at he
  simpa only [map_prod,map_pow,primaryIdealGeneratorHom,MonoidWithZeroHom.coe_mk,
    ZeroHom.coe_mk,commonPrime] using he

theorem right_generator_product (C D : Ideal O) (hC : Supported C) (hD : Supported D)
    (hCD : primeSupport C=primeSupport D) :
    (∏ P : CommonIndex C D,commonPrime C D P^rightExponent C D P)=primaryIdealGenerator D := by
  have he := congrArg primaryIdealGeneratorHom (right_ideal_product C D hC hD hCD)
  simp_rw [commonPrime_span C D hC] at he
  simpa only [map_prod,map_pow,primaryIdealGeneratorHom,MonoidWithZeroHom.coe_mk,
    ZeroHom.coe_mk,commonPrime] using he

def commonFrequencyGenerator (C D : Ideal O) : O :=
  ∏ P : CommonIndex C D,commonPrime C D P^min (leftExponent C D P) (rightExponent C D P)

theorem actual_ideal_secondSaving_lower (C D : Ideal O) (hC : Supported C) (hD : Supported D)
    (hCD : primeSupport C=primeSupport D)
    (w : O) (Z : ℝ) (hZ : 1< Z)
    (hne : idealCorrelation C D hC hD (commonFrequencyGenerator C D*w)≠0) :
    (Real.logb Z (Ideal.absNorm C:ℝ)+Real.logb Z (Ideal.absNorm D:ℝ))/3≤
      secondSaving (commonPrime C D) (leftExponent C D) (rightExponent C D) w Z := by
  let (P : CommonIndex C D) : (Ideal.span {commonPrime C D P}).IsMaximal := by
    rw [commonPrime_span C D hC P]
    infer_instance
  have hg (P : CommonIndex C D) : lambda∉Ideal.span {commonPrime C D P} := by
    rw [commonPrime_span C D hC P]
    exact common_good C D hC P
  have hc (P : CommonIndex C D) : ringChar (O⧸Ideal.span {commonPrime C D P})≠2 := by
    rw [commonPrime_span C D hC P]
    exact common_odd C D hC P
  have hn : actualCorrelation (∏ P : CommonIndex C D,commonPrime C D P^leftExponent C D P)
      (∏ P : CommonIndex C D,commonPrime C D P^rightExponent C D P)
      (supported_product _ (fun P=> supported_power _ (commonPrime_supported C D hC P) _))
      (supported_product _ (fun P=> supported_power _ (commonPrime_supported C D hC P) _))
      (commonFrequencyGenerator C D*w)≠0 := by
    simpa only [left_generator_product C D hC hCD,right_generator_product C D hC hD hCD,
      idealCorrelation] using hne
  have hh := actual_secondSaving_lower (commonPrime C D) (commonPrime_supported C D hC) hg hc
    (commonPrime_coprime C D hC) (leftExponent C D) (rightExponent C D)
    (leftExponent_pos C D) (rightExponent_pos C D) w Z hZ hn
  rw [left_ideal_product C D hC hCD,right_ideal_product C D hC hD hCD] at hh
  exact hh

end CenteredMomentSecondCanonical

end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped BigOperators Classical

namespace CenteredMomentSecondCanonicalFrequency
open CanonicalQuadraticSieve CompletedGauss  
open CenteredMomentSecondCanonical CenteredMomentCanonicalFirst CenteredMomentSecondLedger
open CenteredMomentPartition CenteredMomentSupport CenteredMomentSupportedCorrelation
open CenteredMomentCorrelation CenteredMomentUnequal
local notation "O" => Eisenstein.O

theorem commonFrequencyGenerator_ne_zero (C D : Ideal O) (hC : Supported C) :
    commonFrequencyGenerator C D≠0 := by
  apply Finset.prod_ne_zero_iff.mpr
  intro P hP
  exact pow_ne_zero _ (supported_element_ne_zero _ (commonPrime_supported C D hC P))

theorem commonFrequencyGenerator_dvd (C D : Ideal O) (hC : Supported C) (hD : Supported D)
    (hCD : primeSupport C=primeSupport D) :
    commonFrequencyGenerator C D∣primaryIdealGenerator C ∧
    commonFrequencyGenerator C D∣primaryIdealGenerator D := by
  rw [←left_generator_product C D hC hCD,←right_generator_product C D hC hD hCD]
  constructor
  · exact Finset.prod_dvd_prod_of_dvd _ _ (fun P _=> pow_dvd_pow _ (min_le_left _ _))
  · exact Finset.prod_dvd_prod_of_dvd _ _ (fun P _=> pow_dvd_pow _ (min_le_right _ _))

theorem idealCorrelation_zero_outside_common (C D : Ideal O) (hC : Supported C) (hD : Supported D)
    (hCD : primeSupport C=primeSupport D)
    (j : O) (hj : ¬commonFrequencyGenerator C D∣j) : idealCorrelation C D hC hD j=0 := by
  have hd := commonFrequencyGenerator_dvd C D hC hD hCD
  let := finiteEisensteinQuotientOfNonzero (supported_primaryIdealGenerator_ne_zero C hC)
  let := finiteEisensteinQuotientOfNonzero (supported_primaryIdealGenerator_ne_zero D hD)
  let : Fintype (O⧸Ideal.span {primaryIdealGenerator C}) := Fintype.ofFinite _
  let : Fintype (O⧸Ideal.span {primaryIdealGenerator D}) := Fintype.ofFinite _
  unfold idealCorrelation actualCorrelation
  exact fullModulusCorrelation_eq_zero_of_common_not_dvd _ _ _ _ _ _ hd.1 hd.2 hj

theorem idealCorrelation_tsum_common (C D : Ideal O) (hC : Supported C) (hD : Supported D)
    (hCD : primeSupport C=primeSupport D) (F : O→ℂ) :
    (∑' j : O,idealCorrelation C D hC hD j*F j)=
      ∑' w : O,idealCorrelation C D hC hD (commonFrequencyGenerator C D*w)*
        F (commonFrequencyGenerator C D*w) := by
  apply Eq.symm
  refine (mul_right_injective₀ (commonFrequencyGenerator_ne_zero C D hC)).tsum_eq (f := fun j => idealCorrelation C D hC hD j*F j) ?_
  intro j hj
  have hd : commonFrequencyGenerator C D∣j := by
    by_contra hn
    exact hj (by dsimp only;rw [idealCorrelation_zero_outside_common C D hC hD hCD j hn,zero_mul])
  obtain ⟨w,hw⟩ := hd
  exact ⟨w,hw.symm⟩

def canonicalPartition (C D : Ideal O) (U : Finset (CommonIndex C D)) (w : O) : Prop :=
  actualUnitSet (commonPrime C D) (leftExponent C D) (rightExponent C D) w=U

def canonicalPartitionScalar (C D : Ideal O) (U : Finset (CommonIndex C D)) (w : O) : ℂ :=
  if canonicalPartition C D U w then
    (partitionNormalizer (commonPrime C D) (leftExponent C D) (rightExponent C D) U:ℂ)⁻¹ else 0

theorem actual_ideal_partition_scalar (C D : Ideal O) (hC : Supported C) (hD : Supported D)
    (hCD : primeSupport C=primeSupport D)
    (U : Finset (CommonIndex C D)) (w : O) :
    ‖canonicalPartitionScalar C D U w*
      idealCorrelation C D hC hD (commonFrequencyGenerator C D*w)‖≤1 := by
  let (P : CommonIndex C D) : (Ideal.span {commonPrime C D P}).IsMaximal := by
    rw [commonPrime_span C D hC P];infer_instance
  have hg (P : CommonIndex C D) : lambda∉Ideal.span {commonPrime C D P} := by
    rw [commonPrime_span C D hC P];exact common_good C D hC P
  have hc (P : CommonIndex C D) : ringChar (O⧸Ideal.span {commonPrime C D P})≠2 := by
    rw [commonPrime_span C D hC P];exact common_odd C D hC P
  have hp : canonicalPartition C D U w→∀ i∈U,
      leftExponent C D i=rightExponent C D i ∧ ¬6∣leftExponent C D i ∧
        ¬commonPrime C D i∣dividedFrequency (commonPrime C D) (leftExponent C D) (rightExponent C D) w i := by
    intro h i hi
    rw [canonicalPartition] at h
    rw [←h] at hi
    exact (Finset.mem_filter.mp hi).2
  have hh := normalized_partition_norm_le_one (commonPrime C D) (commonPrime_supported C D hC)
    hg hc (commonPrime_coprime C D hC) (leftExponent C D) (rightExponent C D)
    (leftExponent_pos C D) (rightExponent_pos C D) U (canonicalPartition C D U) w hp
  simp only [left_generator_product C D hC hCD,right_generator_product C D hC hD hCD] at hh
  by_cases hw : canonicalPartition C D U w
  · simpa only [canonicalPartitionScalar,if_pos hw,div_eq_mul_inv,mul_comm,
      idealCorrelation,commonFrequencyGenerator] using hh
  · simp only [canonicalPartitionScalar,if_neg hw,zero_mul,norm_zero,zero_le_one]

end CenteredMomentSecondCanonicalFrequency

end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped BigOperators Classical

namespace CenteredMomentSecondCanonicalNonunit
open CanonicalQuadraticSieve CompletedGauss 
open CenteredMomentSecondCanonical CenteredMomentSecondCanonicalFrequency CenteredMomentCanonicalFirst
open CenteredMomentSecondLedger CenteredMomentPartition CenteredMomentProductCRT
open CenteredMomentSupport
local notation "O" => Eisenstein.O

def equalActiveSet (C D : Ideal O) : Finset (CommonIndex C D) :=
  Finset.univ.filter (fun P=> leftExponent C D P=rightExponent C D P ∧ ¬6∣leftExponent C D P)

def nonunitPartitionSet (C D : Ideal O) (U : Finset (CommonIndex C D)) : Finset (CommonIndex C D) :=
  equalActiveSet C D\U

def nonunitFrequencyGenerator (C D : Ideal O) (U : Finset (CommonIndex C D)) : O :=
  ∏ P∈nonunitPartitionSet C D U,commonPrime C D P

theorem commonPrime_dividedFrequency_iff (C D : Ideal O) (hC : Supported C)
    (w : O) (P : CommonIndex C D) :
    commonPrime C D P∣dividedFrequency (commonPrime C D) (leftExponent C D) (rightExponent C D) w P ↔
      commonPrime C D P∣w := by
  classical
  have hc : IsCoprime (commonPrime C D P)
      (CenteredMomentProductCRT.cuspPrimeCofactor (fun Q=> commonPrime C D Q^min (leftExponent C D Q) (rightExponent C D Q)) P) := by
    unfold CenteredMomentProductCRT.cuspPrimeCofactor
    apply IsCoprime.prod_right
    intro Q hQ
    exact (commonPrime_coprime C D hC (Finset.mem_erase.mp hQ).1.symm).pow_right
  constructor
  · exact fun h=> hc.dvd_of_dvd_mul_left h
  · exact fun h=> h.trans (dvd_mul_left _ _)

theorem nonunitPartitionSet_eq_actual (C D : Ideal O) (U : Finset (CommonIndex C D))
    (w : O) (hpart : canonicalPartition C D U w) :
    nonunitPartitionSet C D U=actualNonunitSet (commonPrime C D) (leftExponent C D) (rightExponent C D) w := by
  unfold canonicalPartition at hpart
  rw [nonunitPartitionSet,←hpart]
  ext P
  simp only [equalActiveSet,actualUnitSet,actualNonunitSet,Finset.mem_sdiff,Finset.mem_filter,
    Finset.mem_univ,true_and]
  tauto

theorem nonunitFrequencyGenerator_ne_zero (C D : Ideal O) (hC : Supported C)
    (U : Finset (CommonIndex C D)) : nonunitFrequencyGenerator C D U≠0 :=
  Finset.prod_ne_zero_iff.mpr (fun P _=>
    CenteredMomentSupportedCorrelation.supported_element_ne_zero _ (commonPrime_supported C D hC P))

theorem nonunitFrequencyGenerator_dvd (C D : Ideal O) (hC : Supported C)
    (U : Finset (CommonIndex C D)) (w : O) (hpart : canonicalPartition C D U w) :
    nonunitFrequencyGenerator C D U∣w := by
  apply Finset.prod_dvd_of_coprime ?_ ?_
  · intro P hP Q hQ hPQ
    exact commonPrime_coprime C D hC hPQ
  · intro P hP
    rw [nonunitPartitionSet_eq_actual C D U w hpart] at hP
    exact (commonPrime_dividedFrequency_iff C D hC w P).mp (Finset.mem_filter.mp hP).2.2.2

theorem partition_tsum_nonunit (C D : Ideal O) (hC : Supported C) (hD : Supported D)
    (U : Finset (CommonIndex C D)) (F : O→ℂ) :
    (∑' w : O,if canonicalPartition C D U w then
      idealCorrelation C D hC hD (commonFrequencyGenerator C D*w)*F w else 0)=
      ∑' h : O,if canonicalPartition C D U (nonunitFrequencyGenerator C D U*h) then
        idealCorrelation C D hC hD ((commonFrequencyGenerator C D*nonunitFrequencyGenerator C D U)*h)*
          F (nonunitFrequencyGenerator C D U*h) else 0 := by
  let f : O→ℂ := fun w=> if canonicalPartition C D U w then
    idealCorrelation C D hC hD (commonFrequencyGenerator C D*w)*F w else 0
  have hs : Function.support f⊆Set.range (fun h=> nonunitFrequencyGenerator C D U*h) := by
    intro w hw
    have hp : canonicalPartition C D U w := by
      by_contra hn
      exact hw (by simp only [f,if_neg hn])
    obtain ⟨h,hh⟩ := nonunitFrequencyGenerator_dvd C D hC U w hp
    exact ⟨h,hh.symm⟩
  have he := (mul_right_injective₀ (nonunitFrequencyGenerator_ne_zero C D hC U)).tsum_eq hs
  simpa only [f,mul_assoc] using he.symm

end CenteredMomentSecondCanonicalNonunit

end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped BigOperators Classical
namespace CenteredMomentRankinSubset
open  CenteredMomentRankinCount
local notation "O" => Eisenstein.O

theorem supported_power_count (a ε : ℝ) (ha : 0 < a) (hε : 0 < ε) :
    ∃ C : ℝ,0 < C ∧ ∀ (Q : Ideal O),Q ≠ 0 → ∀ S : Finset (Ideal O),
      (∀ I ∈ S,I ≠ 0) → (∀ I ∈ S,primeSupport I ⊆ primeSupport Q) →
      ∀ X : ℝ,0 < X → (∀ I ∈ S,(Ideal.absNorm I:ℝ) ≤ X) →
      (S.card:ℝ) ≤ C*X^a*(Ideal.absNorm Q:ℝ)^ε := by
  obtain ⟨C,hC,hcount⟩ := fixed_support_count a ha
  obtain ⟨D,hD,hsub⟩ := CompletedGauss.prime_support_subsets_bound ε hε
  refine ⟨C*D,mul_pos hC hD,?_⟩
  intro Q hQ S hS hs X hX hN
  have hf : ∀ I ∈ S,primeSupport I ∈ (primeSupport Q).powerset :=
    fun I hI => Finset.mem_powerset.mpr (hs I hI)
  have he := Finset.card_eq_sum_card_fiberwise hf
  have hfiber (R : Finset (Ideal O)) (hR : R ∈ (primeSupport Q).powerset) :
      ((S.filter (fun I => primeSupport I=R)).card:ℝ) ≤ C*X^a := by
    apply hcount R _ (fun P hP => support_prime ((Finset.mem_powerset.mp hR) hP))
      (fun I hI => hS I (Finset.mem_filter.mp hI).1)
      (fun I hI => (Finset.mem_filter.mp hI).2) X hX
      (fun I hI => hN I (Finset.mem_filter.mp hI).1)
  calc
    _ = ∑ R ∈ (primeSupport Q).powerset,((S.filter (fun I => primeSupport I=R)).card:ℝ) := by
      exact_mod_cast he
    _ ≤ ∑ _R ∈ (primeSupport Q).powerset,C*X^a := Finset.sum_le_sum hfiber
    _ = (2:ℝ)^(primeSupport Q).card*(C*X^a) := by simp
    _ ≤ (D*(Ideal.absNorm Q:ℝ)^ε)*(C*X^a) :=
      mul_le_mul_of_nonneg_right (hsub Q hQ) (mul_nonneg hC.le (Real.rpow_nonneg hX.le _))
    _ = _ := by ring

theorem supported_power_pair_count (a ε : ℝ) (ha : 0 < a) (hε : 0 < ε) :
    ∃ C : ℝ,0 < C ∧ ∀ (Q : Ideal O),Q ≠ 0 → ∀ S : Finset (Ideal O × Ideal O),
      (∀ v ∈ S,v.1 ≠ 0 ∧ v.2 ≠ 0) →
      (∀ v ∈ S,primeSupport v.1 ⊆ primeSupport Q ∧ primeSupport v.2 ⊆ primeSupport Q) →
      ∀ X Y : ℝ,0 < X → 0 < Y →
      (∀ v ∈ S,(Ideal.absNorm v.1:ℝ) ≤ X ∧ (Ideal.absNorm v.2:ℝ) ≤ Y) →
      (S.card:ℝ) ≤ C*X^a*Y^a*(Ideal.absNorm Q:ℝ)^ε := by
  obtain ⟨C,hC,hcount⟩ := supported_power_count a (ε/2) ha (by positivity)
  refine ⟨C ^ 2,pow_pos hC _,?_⟩
  intro Q hQ S hS hs X Y hX hY hN
  have hfst : ((S.image Prod.fst).card:ℝ) ≤ C*X^a*(Ideal.absNorm Q:ℝ)^(ε/2) := by
    refine hcount Q hQ _ ?_ ?_ X hX ?_
    · intro I hI
      obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp hI
      exact (hS v hv).1
    · intro I hI
      obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp hI
      exact (hs v hv).1
    · intro I hI
      obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp hI
      exact (hN v hv).1
  have hsnd : ((S.image Prod.snd).card:ℝ) ≤ C*Y^a*(Ideal.absNorm Q:ℝ)^(ε/2) := by
    refine hcount Q hQ _ ?_ ?_ Y hY ?_
    · intro I hI
      obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp hI
      exact (hS v hv).2
    · intro I hI
      obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp hI
      exact (hs v hv).2
    · intro I hI
      obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp hI
      exact (hN v hv).2
  have hin : S ⊆ (S.image Prod.fst) ×ˢ (S.image Prod.snd) := by
    intro v hv
    exact Finset.mem_product.mpr ⟨Finset.mem_image_of_mem _ hv,Finset.mem_image_of_mem _ hv⟩
  have hn : (0:ℝ) < Ideal.absNorm Q := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hQ)
  calc
    _ ≤ ((S.image Prod.fst).card:ℝ)*((S.image Prod.snd).card:ℝ) := by
      exact_mod_cast (Finset.card_le_card hin).trans_eq (Finset.card_product _ _)
    _ ≤ (C*X^a*(Ideal.absNorm Q:ℝ)^(ε/2))*(C*Y^a*(Ideal.absNorm Q:ℝ)^(ε/2)) :=
      mul_le_mul hfst hsnd (Nat.cast_nonneg _) (by positivity)
    _ = C ^ 2*X^a*Y^a*((Ideal.absNorm Q:ℝ)^(ε/2)*(Ideal.absNorm Q:ℝ)^(ε/2)) := by ring
    _ = _ := by rw [← Real.rpow_add hn]; congr 2; ring

end CenteredMomentRankinSubset

end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped BigOperators Classical
namespace CenteredMomentRankinLabels
open  CenteredMomentRankinRadical CenteredMomentRankinSubset
local notation "O" => Eisenstein.O

theorem common_pair_count (a ε : ℝ) (ha : 0 < a) (hε : 0 < ε) :
    ∃ C : ℝ,0 < C ∧ ∀ (s : Ideal O),Squarefree s → s ≠ 0 →
      ∀ S : Finset (Ideal O × Ideal O),
      (∀ v ∈ S,v.1 ≠ 0 ∧ v.2 ≠ 0) →
      (∀ v ∈ S,primeSupport v.1=primeSupport v.2) →
      (∀ v ∈ S,s ∣ v.1 ∧ s ∣ v.2) →
      ∀ X₁ X₂ Y : ℝ,0 < X₁ → 0 < X₂ → 0 < Y →
      (∀ v ∈ S,(Ideal.absNorm v.1:ℝ) ≤ X₁ ∧ (Ideal.absNorm v.2:ℝ) ≤ X₂) →
      (∀ v ∈ S,(Ideal.absNorm (commonRadical v.1 v.2):ℝ) ≤ Y) →
      (S.card:ℝ) ≤ C*X₁^a*X₂^a*Y^(1+ε)/(Ideal.absNorm s:ℝ) := by
  obtain ⟨C,hC,hcount⟩ := supported_power_pair_count a ε ha hε
  refine ⟨128*C,by positivity,?_⟩
  intro s hs hs0 S hS heq hdiv X₁ X₂ Y hX₁ hX₂ hY hN hR
  let rad : Ideal O × Ideal O → Ideal O := fun v => commonRadical v.1 v.2
  have hfiber (R : Ideal O) (hRmem : R ∈ S.image rad) :
      ((S.filter (fun v => rad v=R)).card:ℝ) ≤ C*X₁^a*X₂^a*Y^ε := by
    obtain ⟨v,hv,hvR⟩ := Finset.mem_image.mp hRmem
    have hR0 : R ≠ 0 := hvR ▸ commonRadical_ne_zero v.1 v.2
    have hRN : (Ideal.absNorm R:ℝ) ≤ Y := hvR ▸ hR v hv
    have hb := hcount R hR0 (S.filter (fun v => rad v=R))
      (fun v hv => hS v (Finset.mem_filter.mp hv).1)
      (by
        intro w hw
        obtain ⟨hw,hwr⟩ := Finset.mem_filter.mp hw
        have he : primeSupport R=primeSupport w.1 := by
          rw [← hwr,commonRadical_support,← heq w hw,Finset.inter_self]
        rw [he,heq w hw]
        exact ⟨Finset.Subset.refl _,Finset.Subset.refl _⟩)
      X₁ X₂ hX₁ hX₂ (fun w hw => hN w (Finset.mem_filter.mp hw).1)
    exact hb.trans (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow (Nat.cast_nonneg _) hRN hε.le) (by positivity))
  have hrad := old_mask_radical_count S Prod.fst Prod.snd s hs hs0
    (fun v hv => (hS v hv).1) (fun v hv => (hS v hv).2)
    (fun v hv => (hdiv v hv).1) (fun v hv => (hdiv v hv).2) Y hY.le hR
  have he := Finset.card_eq_sum_card_fiberwise
    (fun v (hv : v ∈ S) => Finset.mem_image_of_mem rad hv)
  calc
    _ = ∑ R ∈ S.image rad,((S.filter (fun v => rad v=R)).card:ℝ) := by exact_mod_cast he
    _ ≤ ∑ _R ∈ S.image rad,C*X₁^a*X₂^a*Y^ε := Finset.sum_le_sum hfiber
    _ = ((S.image rad).card:ℝ)*(C*X₁^a*X₂^a*Y^ε) := by simp
    _ ≤ (128*Y/(Ideal.absNorm s:ℝ))*(C*X₁^a*X₂^a*Y^ε) :=
      mul_le_mul_of_nonneg_right hrad (by positivity)
    _ = _ := by rw [Real.rpow_add hY,Real.rpow_one]; ring

theorem partitioned_common_pair_count (a ε : ℝ) (ha : 0 < a) (hε : 0 < ε) :
    ∃ C : ℝ,0 < C ∧ ∀ (s : Ideal O),Squarefree s → s ≠ 0 →
      ∀ S : Finset ((Ideal O × Ideal O) × Finset (Ideal O)),
      (∀ v ∈ S,v.1.1 ≠ 0 ∧ v.1.2 ≠ 0) →
      (∀ v ∈ S,primeSupport v.1.1=primeSupport v.1.2) →
      (∀ v ∈ S,s ∣ v.1.1 ∧ s ∣ v.1.2) →
      (∀ v ∈ S,v.2 ⊆ primeSupport (commonRadical v.1.1 v.1.2)) →
      ∀ X₁ X₂ Y : ℝ,0 < X₁ → 0 < X₂ → 0 < Y →
      (∀ v ∈ S,(Ideal.absNorm v.1.1:ℝ) ≤ X₁ ∧ (Ideal.absNorm v.1.2:ℝ) ≤ X₂) →
      (∀ v ∈ S,(Ideal.absNorm (commonRadical v.1.1 v.1.2):ℝ) ≤ Y) →
      (S.card:ℝ) ≤ C*X₁^a*X₂^a*Y^(1+ε)/(Ideal.absNorm s:ℝ) := by
  obtain ⟨C,hC,hcount⟩ := common_pair_count a (ε/2) ha (by positivity)
  obtain ⟨D,hD,hpow⟩ := CompletedGauss.prime_support_subsets_bound (ε/2) (by positivity)
  refine ⟨C*D,mul_pos hC hD,?_⟩
  intro s hs hs0 S hS heq hdiv hpart X₁ X₂ Y hX₁ hX₂ hY hN hR
  have hpairs := hcount s hs hs0 (S.image Prod.fst)
    (by intro v hv; obtain ⟨w,hw,rfl⟩ := Finset.mem_image.mp hv; exact hS w hw)
    (by intro v hv; obtain ⟨w,hw,rfl⟩ := Finset.mem_image.mp hv; exact heq w hw)
    (by intro v hv; obtain ⟨w,hw,rfl⟩ := Finset.mem_image.mp hv; exact hdiv w hw)
    X₁ X₂ Y hX₁ hX₂ hY
    (by intro v hv; obtain ⟨w,hw,rfl⟩ := Finset.mem_image.mp hv; exact hN w hw)
    (by intro v hv; obtain ⟨w,hw,rfl⟩ := Finset.mem_image.mp hv; exact hR w hw)
  have hfiber (v : Ideal O × Ideal O) (hv : v ∈ S.image Prod.fst) :
      ((S.filter (fun w => w.1=v)).card:ℝ) ≤ D*Y^(ε/2) := by
    have hin : (S.filter (fun w => w.1=v)).image Prod.snd ⊆
        (primeSupport (commonRadical v.1 v.2)).powerset := by
      intro A hA
      obtain ⟨w,hw,rfl⟩ := Finset.mem_image.mp hA
      obtain ⟨hw,hwe⟩ := Finset.mem_filter.mp hw
      exact Finset.mem_powerset.mpr (hwe ▸ hpart w hw)
    have hinj : Set.InjOn (fun w : (Ideal O × Ideal O) × Finset (Ideal O) => w.2)
        (↑(S.filter (fun w => w.1=v)) : Set ((Ideal O × Ideal O) × Finset (Ideal O))) := by
      intro w hw z hz he
      exact Prod.ext ((Finset.mem_filter.mp hw).2.trans (Finset.mem_filter.mp hz).2.symm) he
    have hc : ((S.filter (fun w => w.1=v)).card:ℝ) ≤
        (2:ℝ)^(primeSupport (commonRadical v.1 v.2)).card := by
      have hb := Finset.card_le_card hin
      rw [Finset.card_image_of_injOn hinj,Finset.card_powerset] at hb
      exact_mod_cast hb
    obtain ⟨w,hw,hwe⟩ := Finset.mem_image.mp hv
    have hb := hpow (commonRadical v.1 v.2) (commonRadical_ne_zero _ _)
    have hn : (Ideal.absNorm (commonRadical v.1 v.2):ℝ) ≤ Y := hwe ▸ hR w hw
    exact hc.trans (hb.trans (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow (Nat.cast_nonneg _) hn (by positivity)) hD.le))
  have he := Finset.card_eq_sum_card_fiberwise
    (fun v (hv : v ∈ S) => Finset.mem_image_of_mem Prod.fst hv)
  calc
    _ = ∑ v ∈ S.image Prod.fst,((S.filter (fun w => w.1=v)).card:ℝ) := by exact_mod_cast he
    _ ≤ ∑ _v ∈ S.image Prod.fst,D*Y^(ε/2) := Finset.sum_le_sum hfiber
    _ = ((S.image Prod.fst).card:ℝ)*(D*Y^(ε/2)) := by simp
    _ ≤ (C*X₁^a*X₂^a*Y^(1+ε/2)/(Ideal.absNorm s:ℝ))*(D*Y^(ε/2)) :=
      mul_le_mul_of_nonneg_right hpairs (by positivity)
    _ = (C*D)*X₁^a*X₂^a*(Y^(1+ε/2)*Y^(ε/2))/(Ideal.absNorm s:ℝ) := by ring
    _ = _ := by rw [← Real.rpow_add hY]; congr 3; ring

end CenteredMomentRankinLabels

end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped BigOperators Classical

namespace CenteredMomentSecondCanonicalLedger
open CanonicalQuadraticSieve CompletedGauss
open CenteredMomentSecondCanonical CenteredMomentSecondCanonicalFrequency CenteredMomentSecondCanonicalNonunit
open CenteredMomentCanonicalFirst CenteredMomentSecondLedger CenteredMomentPartition CenteredMomentPartitionNorm
open CenteredMomentSupport CenteredMomentForcing
local notation "O" => Eisenstein.O

theorem span_finset_product {ι : Type*} (S : Finset ι) (p : ι→O) :
    Ideal.span {∏ i∈S,p i}=∏ i∈S,Ideal.span {p i} := by
  induction S using Finset.induction_on with
  | empty => simp
  | @insert i S hi ih => rw [Finset.prod_insert hi,Finset.prod_insert hi,
      ←Ideal.span_singleton_mul_span_singleton,ih]

theorem commonFrequencyGenerator_span (C D : Ideal O) (_hC : Supported C) :
    Ideal.span {commonFrequencyGenerator C D}=
      commonIdeal (commonPrime C D) (leftExponent C D) (rightExponent C D) := by
  simp only [commonFrequencyGenerator,span_finset_product,←Ideal.span_singleton_pow,commonIdeal]

theorem nonunitFrequencyGenerator_span (C D : Ideal O)
    (U : Finset (CommonIndex C D)) :
    Ideal.span {nonunitFrequencyGenerator C D U}=
      unitIdeal (commonPrime C D) (nonunitPartitionSet C D U) := by
  simp only [nonunitFrequencyGenerator,span_finset_product,unitIdeal]

theorem actual_partitionNormalizer (C D : Ideal O) (hC : Supported C)
    (U : Finset (CommonIndex C D)) :
    partitionNormalizer (commonPrime C D) (leftExponent C D) (rightExponent C D) U=
      (Ideal.absNorm (Ideal.span {commonFrequencyGenerator C D}):ℝ)/
        Ideal.absNorm (∏ P∈U,P.val) := by
  rw [partitionNormalizer_eq_norm_ratio _ (commonPrime_supported C D hC) _ _
    (leftExponent_pos C D) (rightExponent_pos C D),←commonFrequencyGenerator_span C D hC]
  simp only [unitIdeal,commonPrime_span C D hC]

theorem actual_second_ledger_lower (C D : Ideal O) (hC : Supported C) (hD : Supported D)
    (hCD : primeSupport C=primeSupport D)
    (U : Finset (CommonIndex C D)) (w : O) (hpart : canonicalPartition C D U w)
    (Z : ℝ) (hZ : 1< Z)
    (hne : idealCorrelation C D hC hD (commonFrequencyGenerator C D*w)≠0) :
    (Real.logb Z (Ideal.absNorm C:ℝ)+Real.logb Z (Ideal.absNorm D:ℝ))/3≤
      Real.logb Z (Ideal.absNorm C:ℝ)+Real.logb Z (Ideal.absNorm D:ℝ)-
      5*Real.logb Z (Ideal.absNorm (Ideal.span {commonFrequencyGenerator C D}):ℝ)/6-
      Real.logb Z (Ideal.absNorm (∏ P : CommonIndex C D,P.val):ℝ)+
      Real.logb Z (Ideal.absNorm (∏ P∈U,P.val):ℝ)+
      Real.logb Z (Ideal.absNorm (Ideal.span {nonunitFrequencyGenerator C D U}):ℝ)/6+
      Real.logb Z (Ideal.absNorm (forcingIdeal (fun P : CommonIndex C D=> P.val)
        (leftExponent C D) (rightExponent C D) (nonunitPartitionSet C D U)):ℝ)/3 := by
  have hh := actual_ideal_secondSaving_lower C D hC hD hCD w Z hZ hne
  rw [secondSaving_eq_norm_ledger _ (commonPrime_supported C D hC)] at hh
  rw [left_ideal_product C D hC hCD,right_ideal_product C D hC hD hCD,
    ←commonFrequencyGenerator_span C D hC] at hh
  change actualUnitSet (commonPrime C D) (leftExponent C D) (rightExponent C D) w=U at hpart
  rw [hpart,←nonunitPartitionSet_eq_actual C D U w hpart,
    ←nonunitFrequencyGenerator_span C D U] at hh
  simpa only [unitIdeal,commonPrime_span C D hC,forcingIdeal] using hh

theorem actual_partition_count (ε : ℝ) (hε : 0<ε) :
    ∃ B : ℝ,0< B ∧ ∀ C D : Ideal O,C≠0 →
      (Fintype.card (Finset (CommonIndex C D)):ℝ)≤ B*(Ideal.absNorm C:ℝ)^ε := by
  obtain ⟨B,hB,hcount⟩ := CompletedGauss.prime_support_subsets_bound ε hε
  refine ⟨B,hB,?_⟩
  intro C D hC
  have hc : Fintype.card (CommonIndex C D)≤(primeSupport C).card := by
    rw [Fintype.card_coe]
    exact Finset.card_le_card Finset.inter_subset_left
  have hh : (Fintype.card (Finset (CommonIndex C D)):ℝ)≤
      (2:ℝ)^(primeSupport C).card := by
    rw [Fintype.card_finset,Nat.cast_pow,Nat.cast_ofNat]
    exact pow_le_pow_right₀ (by norm_num) hc
  exact hh.trans (hcount C hC)

end CenteredMomentSecondCanonicalLedger

end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped BigOperators Classical

namespace CenteredMomentSecondMovingSupport
open CanonicalQuadraticSieve CanonicalRowCompletion CompletedGauss 
open CenteredMomentSecondCanonical CenteredMomentSecondCanonicalFrequency CenteredMomentSecondCanonicalNonunit
open CenteredMomentCanonicalFirst CenteredMomentSecondLedger CenteredMomentPartition CenteredMomentPartitionNorm
open CenteredMomentSupport CenteredMomentSupportedCorrelation CenteredMomentUnequal
local notation "O" => Eisenstein.O

theorem actual_unequal_min_six (C D : Ideal O) (hC : Supported C) (hD : Supported D)
    (hCD : primeSupport C=primeSupport D) (w : O)
    (hne : idealCorrelation C D hC hD (commonFrequencyGenerator C D*w)≠0)
    (P : CommonIndex C D) (hneq : leftExponent C D P≠rightExponent C D P) :
    6∣min (leftExponent C D P) (rightExponent C D P) := by
  let (P : CommonIndex C D) : (Ideal.span {commonPrime C D P}).IsMaximal := by
    rw [commonPrime_span C D hC P];infer_instance
  have hglobal : actualCorrelation (∏ P : CommonIndex C D,commonPrime C D P^leftExponent C D P)
      (∏ P : CommonIndex C D,commonPrime C D P^rightExponent C D P)
      (supported_product _ (fun P=> supported_power _ (commonPrime_supported C D hC P) _))
      (supported_product _ (fun P=> supported_power _ (commonPrime_supported C D hC P) _))
      ((∏ P : CommonIndex C D,commonPrime C D P^min (leftExponent C D P) (rightExponent C D P))*w)≠0 := by
    simpa only [left_generator_product C D hC hCD,right_generator_product C D hC hD hCD,
      commonFrequencyGenerator,idealCorrelation] using hne
  have hl := local_nonzero_of_global (commonPrime C D) (commonPrime_supported C D hC)
    (commonPrime_coprime C D hC) (leftExponent C D) (rightExponent C D) w hglobal P
  exact nonzero_unequal_min_six (commonPrime C D P) (commonPrime_supported C D hC P)
    (by rw [commonPrime_span C D hC P];exact common_good C D hC P)
    (by rw [commonPrime_span C D hC P];exact common_odd C D hC P)
    _ _ (leftExponent_pos C D P) (rightExponent_pos C D P) hneq _ hl

def fixedExponent (C D : Ideal O) (U : Finset (CommonIndex C D)) (P : CommonIndex C D) : ℕ :=
  min (leftExponent C D P) (rightExponent C D P)+if P∈nonunitPartitionSet C D U then 1 else 0

def fixedActiveSet (C D : Ideal O) (U : Finset (CommonIndex C D)) : Finset (CommonIndex C D) :=
  Finset.univ.filter (fun P=>¬6∣fixedExponent C D U P)

theorem fixedActiveSet_subset (C D : Ideal O) (hC : Supported C) (hD : Supported D)
    (hCD : primeSupport C=primeSupport D)
    (U : Finset (CommonIndex C D)) (w : O)
    (hne : idealCorrelation C D hC hD (commonFrequencyGenerator C D*w)≠0) :
    fixedActiveSet C D U⊆U∪nonunitPartitionSet C D U := by
  intro P hP
  have ha := (Finset.mem_filter.mp hP).2
  by_contra hn
  have hU : P∉U := fun h=> hn (Finset.mem_union_left _ h)
  have hV : P∉nonunitPartitionSet C D U := fun h=> hn (Finset.mem_union_right _ h)
  have heq : ¬(leftExponent C D P=rightExponent C D P ∧ ¬6∣leftExponent C D P) := by
    intro he
    exact hV (Finset.mem_sdiff.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _,he⟩,hU⟩)
  rw [fixedExponent,if_neg hV,add_zero] at ha
  by_cases hc : leftExponent C D P=rightExponent C D P
  · rw [hc,min_self] at ha
    exact heq ⟨hc,by simpa only [hc] using ha⟩
  · exact ha (actual_unequal_min_six C D hC hD hCD w hne P hc)

theorem fixed_active_log_bound (C D : Ideal O) (hC : Supported C) (hD : Supported D)
    (hCD : primeSupport C=primeSupport D)
    (U : Finset (CommonIndex C D)) (w : O)
    (hne : idealCorrelation C D hC hD (commonFrequencyGenerator C D*w)≠0)
    (Z : ℝ) (hZ : 1< Z) :
    Real.logb Z (Ideal.absNorm (∏P∈fixedActiveSet C D U,P.val):ℝ)≤
      Real.logb Z (Ideal.absNorm (∏P∈U,P.val):ℝ)+
        Real.logb Z (Ideal.absNorm (Ideal.span {nonunitFrequencyGenerator C D U}):ℝ) := by
  have hn (P : CommonIndex C D) : 0≤ Real.logb Z (Ideal.absNorm P.val:ℝ) :=
    Real.logb_nonneg hZ (by exact_mod_cast (Nat.one_le_iff_ne_zero.mpr
      (Ideal.absNorm_eq_zero_iff.not.mpr (commonPrime_supported_ideal C D hC P).1)))
  have hlog (T : Finset (CommonIndex C D)) :
      Real.logb Z (Ideal.absNorm (∏P∈T,P.val):ℝ)=∑P∈T,Real.logb Z (Ideal.absNorm P.val:ℝ) := by
    simp only [map_prod,Nat.cast_prod]
    exact Real.logb_prod _ _ (fun P _=> Nat.cast_ne_zero.mpr
      (Ideal.absNorm_eq_zero_iff.not.mpr (commonPrime_supported_ideal C D hC P).1))
  rw [CenteredMomentSecondCanonicalLedger.nonunitFrequencyGenerator_span,unitIdeal]
  simp only [commonPrime_span C D hC]
  have hdis : Disjoint U (nonunitPartitionSet C D U) := by
    apply Finset.disjoint_left.mpr
    intro P hU hV
    exact (Finset.mem_sdiff.mp hV).2 hU
  rw [hlog,hlog,hlog,←Finset.sum_union hdis]
  exact Finset.sum_le_sum_of_subset_of_nonneg (fixedActiveSet_subset C D hC hD hCD U w hne)
    (fun P _ _=> hn P)

end CenteredMomentSecondMovingSupport

end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson
open TruncatedPrincipalPoisson


noncomputable section
open scoped BigOperators Classical

namespace CenteredMomentFirstChildProfile
open HeckeFamily CenteredMomentFirstIdealFamily CenteredMomentHeckeColumnWindow
open CenteredMomentFirstCanonicalFamily CenteredMomentCanonicalFirst CenteredMomentHeckeExpansion
open CenteredMomentFirstColumns CenteredMomentChildAssembly CenteredMomentSourceRow
open Eisenstein CanonicalQuadraticSieve  RayFourExpansion
local notation "O" => Eisenstein.O

theorem divisor_column_of_family (η τ : Character) (m : O) (F : O → ℂ) (ξ : RayCharacter)
    (hτ : ∀ I : Ideal O,Supported I → ∀ t : ℝ,
      heightCoeff τ t I=rowWeight η m 1 1 t I*(F (primaryIdealGenerator I)*
        rayMonoid ξ (primaryIdealGenerator I)))
    (L I : Ideal O) (hI : Supported I) (β : Ideal O → ℂ) (t : ℝ) :
    divisorCoefficient L (fun J : Ideal O => primaryIdealGenerator J)
      (fun J => β J*rowWeight η m 1 1 t J*F (primaryIdealGenerator J)) ξ I=
      (if L∣I then β I else 0)*heightCoeff τ t I := by
  rw [divisorCoefficient,primary_span_supported I hI,hτ I hI t]
  split_ifs <;> ring

theorem exists_first_divisor_pair (η : Character) (m : O) (hm : m≠0)
    (hmLam : lambda∣m) (hm2 : (2:O)∣m)
    (C D : Ideal O) (hC : Supported C) (E : Finset (CommonIndex C D))
    (ξ₁ ξ₂ : RayCharacter) :
    let e := primeSubsetGenerator (fun P : CommonIndex C D => P.val) E
    let r := activeConductor C D
    let ρ := finiteSexticRow (activePrime C D) (activeGood C D hC) (activeExponent C D)
    let M := η.modulus*Ideal.span {m}*Ideal.span {(72:O)}*Ideal.span {e*r}
    ∃ τ₁ τ₂ : Character,τ₁.modulus=M ∧ τ₂.modulus=M ∧
      (∀ L I : Ideal O,Supported I → ∀ β : Ideal O → ℂ,∀ t : ℝ,
        divisorCoefficient L (fun J : Ideal O => primaryIdealGenerator J)
          (fun J => β J*rowWeight η m 1 1 t J*leftCoefficient e r ρ (primaryIdealGenerator J)) ξ₁ I=
          (if L∣I then β I else 0)*heightCoeff τ₁ t I) ∧
      (∀ L I : Ideal O,Supported I → ∀ β : Ideal O → ℂ,∀ t : ℝ,
        divisorCoefficient L (fun J : Ideal O => primaryIdealGenerator J)
          (fun J => β J*rowWeight η m 1 1 t J*rightCoefficient e r ρ (primaryIdealGenerator J)) ξ₂ I=
          (if L∣I then β I else 0)*heightCoeff τ₂ t I) := by
  obtain ⟨τ₁,τ₂,hM₁,hM₂,h₁,h₂⟩ := exists_first_ideal_pair η m hm hmLam hm2 C D hC E ξ₁ ξ₂
  refine ⟨τ₁,τ₂,hM₁,hM₂,?_,?_⟩
  · intro L I hI β t
    exact divisor_column_of_family η τ₁ m _ ξ₁ h₁ L I hI β t
  · intro L I hI β t
    exact divisor_column_of_family η τ₂ m _ ξ₂ h₂ L I hI β t

end CenteredMomentFirstChildProfile

end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson
open TruncatedPrincipalPoisson


noncomputable section
open scoped BigOperators Classical

namespace CenteredMomentSecondChildProfile
open HeckeFamily HeckeRowClosure CenteredMomentChildRows CenteredMomentHeckeExpansion
open CenteredMomentHeckeColumnWindow CenteredMomentSourceRow CenteredMomentChildAssembly
open CenteredMomentSecondScaled CanonicalRowCompletion CanonicalQuadraticSieve RayFourExpansion
open  CenteredMomentCommonSupport
local notation "O" => Eisenstein.O

theorem child_ideal_primary (η : Character) (χ : RayCharacter)
    (I : Ideal O) (hI : Supported I) :
    idealCoeff (childCharacter η χ) I=idealCoeff η I*rayMonoid χ (primaryIdealGenerator I) := by
  have hn := supported_primaryIdealGenerator_ne_zero I hI
  have hs := primary_span_supported I hI
  have hc := idealCoeff_span (childCharacter η χ) hn
  have he := idealCoeff_span η hn
  rw [hs] at hc he
  rw [hc,childCharacter_primary η χ _ (by rw [hs];exact hI)
    (primaryIdealGenerator_spec I hn).2,←he]

theorem exists_second_height_character (η : Character) (χ : RayCharacter) (m A : O)
    (hm : m≠0) (hA : A≠0) (hmLam : lambda∣m) (hm2 : (2:O)∣m) :
    ∃ τ : Character,τ.modulus.absNorm≤ rowConductorBound (childCharacter η χ) m 1 A ∧
      ∀ I : Ideal O,Supported I → ∀ t : ℝ,
        heightCoeff τ t I=rowWeight η m 1 1 t I*idealRowHom A I*
          rayMonoid χ (primaryIdealGenerator I) := by
  obtain ⟨τ,hN,hτ⟩ := exists_row_character_with_conductor (childCharacter η χ) m 1 A hm one_ne_zero hA hmLam hm2
  refine ⟨τ,hN,?_⟩
  intro I hI t
  have he := idealCoeff_eq_row (childCharacter η χ) τ m 1 A hτ I
  simp only [one_pow,mul_one] at he
  change idealCoeff τ I*(Ideal.absNorm I:ℂ)^(Complex.I*t)=
    ((idealCoeff η I*idealRowHom (m^6*(1*1)) I)*(Ideal.absNorm I:ℂ)^(Complex.I*t))*
      idealRowHom A I*rayMonoid χ (primaryIdealGenerator I)
  rw [he,child_ideal_primary η χ I hI,idealRowHom_argument_mul]
  simp only [mul_one]
  ring

theorem second_divisor_column (η τ : Character) (χ : RayCharacter) (m A : O)
    (hτ : ∀ I : Ideal O,Supported I → ∀ t : ℝ,
      heightCoeff τ t I=rowWeight η m 1 1 t I*idealRowHom A I*
        rayMonoid χ (primaryIdealGenerator I))
    (L I : Ideal O) (hI : Supported I) (β : Ideal O → ℂ) (t : ℝ) :
    divisorCoefficient L (fun J : Ideal O => primaryIdealGenerator J)
      (movingCoefficient A (fun J : Ideal O => primaryIdealGenerator J)
        (fun J => β J*rowWeight η m 1 1 t J)) χ I=
      (if L∣I then β I else 0)*heightCoeff τ t I := by
  rw [divisorCoefficient,movingCoefficient,primary_span_supported I hI,hτ I hI t]
  split_ifs <;> ring

end CenteredMomentSecondChildProfile

end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson
open TruncatedPrincipalPoisson


noncomputable section
open scoped BigOperators Classical

namespace CenteredMomentSecondHeightFamily
open HeckeFamily CanonicalQuadraticSieve CanonicalRowCompletion CompletedGauss
open CenteredMomentSourceRow CenteredMomentHeckeColumnWindow CenteredMomentHeckeExpansion
open CenteredMomentSecondChildProfile CenteredMomentChildRows CenteredMomentChildAssembly
open CenteredMomentSecondScaled RayFourExpansion  Eisenstein
local notation "O" => Eisenstein.O

def fixedBadMask : O := lambda*2

theorem fixedBadMask_ne_zero : fixedBadMask≠0 :=
  mul_ne_zero residue_lambda_prime.ne_zero (by norm_num)

theorem fixedBadMask_coprime (n : O) (hn : Supported (Ideal.span {n})) :
    IsCoprime fixedBadMask n := by
  have hl := residue_lambda_prime.irreducible.coprime_iff_not_dvd.mpr
    ((CanonicalQuadraticSieve.supported_span_iff n).mp hn).1
  have h2 := negative_two_prime.irreducible.coprime_iff_not_dvd.mpr
    (by simpa only [neg_dvd] using ((CanonicalQuadraticSieve.supported_span_iff n).mp hn).2)
  have htwo : IsCoprime (2:O) n := h2.of_isCoprime_of_dvd_left ⟨-1,by ring⟩
  exact hl.mul_left htwo

theorem heightCoeff_eq_fixed_rowWeight (τ : Character) (t : ℝ)
    (I : Ideal O) (hI : Supported I) :
    heightCoeff τ t I=rowWeight τ fixedBadMask 1 1 t I := by
  have hc : IsCoprime (Ideal.span {fixedBadMask}) I := by
    rw [←primary_span_supported I hI,Ideal.isCoprime_span_singleton_iff]
    exact fixedBadMask_coprime _ ((supported_span_primaryIdealGenerator_iff I).mpr hI)
  have hs := idealRowHom_sixth_mask fixedBadMask I ((supported_iff_native _).mp hI)
  rw [if_pos hc.symm] at hs
  change idealCoeff τ I*(Ideal.absNorm I:ℂ)^(Complex.I*t)=
    ((idealCoeff τ I*idealRowHom (fixedBadMask^6*(1*1)) I)*(Ideal.absNorm I:ℂ)^(Complex.I*t))
  simp only [mul_one,hs]

theorem exists_second_family (η : Character) (χ : RayCharacter) (A : O) (hA : A≠0) :
    ∃ τ : Character,
      τ.modulus.absNorm≤ HeckeRowClosure.rowConductorBound (childCharacter η χ) fixedBadMask 1 A ∧
      ∀ I : Ideal O,Supported I → ∀ t : ℝ,
        heightCoeff τ t I=heightCoeff η t I*idealRowHom A I*
          rayMonoid χ (primaryIdealGenerator I) := by
  obtain ⟨τ,hN,hτ⟩ := exists_second_height_character η χ fixedBadMask A fixedBadMask_ne_zero hA
    (by exact dvd_mul_right lambda (2:O)) (by exact dvd_mul_left (2:O) lambda)
  refine ⟨τ,hN,?_⟩
  intro I hI t
  rw [hτ I hI t,←heightCoeff_eq_fixed_rowWeight η t I hI]

theorem second_height_divisor_column (η τ : Character) (χ : RayCharacter) (A : O)
    (hτ : ∀ I : Ideal O,Supported I → ∀ t : ℝ,
      heightCoeff τ t I=heightCoeff η t I*idealRowHom A I*rayMonoid χ (primaryIdealGenerator I))
    (L I : Ideal O) (hI : Supported I) (β : Ideal O → ℂ) (t : ℝ) :
    divisorCoefficient L (fun J : Ideal O => primaryIdealGenerator J)
      (movingCoefficient A (fun J : Ideal O => primaryIdealGenerator J)
        (fun J => β J*heightCoeff η t J)) χ I=
      (if L∣I then β I else 0)*heightCoeff τ t I := by
  rw [divisorCoefficient,movingCoefficient,primary_span_supported I hI,hτ I hI t]
  split_ifs <;> ring

end CenteredMomentSecondHeightFamily

end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson
open TruncatedPrincipalPoisson


noncomputable section
open scoped BigOperators Classical
namespace CenteredMomentRadicalFamily
open HeckeFamily HeckeRowClosure CanonicalRowCompletion CanonicalQuadraticSieve
open CenteredMomentFirstFamily CenteredMomentSupportedCorrelation
local notation "O" => Eisenstein.O

theorem elementCoeff_power_pos (χ : Character) (e : ℕ) (he : 0< e) (n : O) :
    elementCoeff (χ.power e) n=(elementCoeff χ n)^e := by
  by_cases hn : IsUnit (Ideal.Quotient.mk χ.modulus n)
  · exact elementCoeff_power_of_unit χ e n hn
  · have hz : elementCoeff χ n=0 := MulChar.map_nonunit _ hn
    have hp : elementCoeff (χ.power e) n=0 := MulChar.map_nonunit _ hn
    rw [hp,hz,zero_pow (Nat.ne_zero_of_lt he)]

theorem exists_product_presentation {ι : Type*} (S : Finset ι) (base : Character)
    (χ : ι→Character) (e : ι→ℕ) (he : ∀i∈S,0< e i)
    (M : Ideal O) (hb : M≤ base.modulus) (hχ : ∀i∈S,M≤(χ i).modulus) :
    ∃τ : Character,M≤τ.modulus ∧ ∀n:O,
      elementCoeff τ n=elementCoeff base n*∏i∈S,(elementCoeff (χ i) n)^(e i) := by
  induction S using Finset.induction_on with
  | empty => exact ⟨base,hb,by simp⟩
  | @insert a S ha ih =>
    obtain ⟨τ,hτ,ht⟩ := ih (fun i hi=> he i (Finset.mem_insert_of_mem hi))
      (fun i hi=> hχ i (Finset.mem_insert_of_mem hi))
    refine ⟨τ.product ((χ a).power (e a)),le_inf hτ (hχ a (Finset.mem_insert_self _ _)),?_⟩
    intro n
    rw [elementCoeff_product,elementCoeff_power_pos _ _ (he a (Finset.mem_insert_self _ _)),
      ht,Finset.prod_insert ha]
    ring

theorem single_row_on_base (η : Character) (m p n : O)
    (hmLam : lambda∣m) (hm2 : (2:O)∣m)
    (hn : rowTwist (elementHom η) m 1 1 n≠0) :
    rowTwist (elementHom (η.power 0)) m 1 p n=idealRowHom p (Ideal.span {n}) := by
  have hs := (rowTwist_nonzero_coprime η m 1 1 n hmLam hm2 hn).1
  have hη : elementCoeff η n≠0 := left_ne_zero_of_mul hn
  have hunit := MulChar.apply_ne_zero_iff.mp hη
  have hp : elementCoeff (η.power 0) n=1 := by
    rw [elementCoeff_power_of_unit η 0 n hunit,pow_zero]
  have hm : IsCoprime m n := by
    by_contra h
    apply hn
    rw [rowTwist_extract_sixth_mask _ m 1 1 n ((supported_iff_native _).mp hs)]
    simp [coprimalityMask,h]
  rw [rowTwist_extract_sixth_mask _ m 1 p n ((supported_iff_native _).mp hs)]
  change elementCoeff (η.power 0) n*coprimalityMask m n*idealRowHom (1^4*p) _=_
  rw [hp,one_pow,one_mul]
  simp [coprimalityMask,hm]

theorem row_product_formula {ι : Type*} (S : Finset ι)
    (η : Character) (m : O) (p : ι→O) (e : ι→ℕ)
    (hmLam : lambda∣m) (hm2 : (2:O)∣m) (n : O) :
    rowTwist (elementHom η) m 1 1 n*
      (∏i∈S,(rowTwist (elementHom (η.power 0)) m 1 (p i) n)^(e i))=
      rowTwist (elementHom η) m 1 (∏i∈S,(p i)^(e i)) n := by
  conv_rhs => rw [rowTwist_row_factor]
  by_cases hn : rowTwist (elementHom η) m 1 1 n=0
  · rw [hn,zero_mul,zero_mul]
  have hs := (rowTwist_nonzero_coprime η m 1 1 n hmLam hm2 hn).1
  congr 1
  simp_rw [single_row_on_base η m _ n hmLam hm2 hn]
  induction S using Finset.induction_on with
  | empty => simpa using (idealRowHom_one_supported (Ideal.span {n}) hs).symm
  | @insert a S ha ih =>
    rw [Finset.prod_insert ha,Finset.prod_insert ha,idealRowHom_argument_mul,
      idealRowHom_argument_pow _ _ _ (supported_primaryIdealGenerator_ne_zero _ hs),ih]

theorem exists_radical_row_presentation {ι : Type*} [Fintype ι]
    (η : Character) (m : O) (hm : m≠0) (hmLam : lambda∣m) (hm2 : (2:O)∣m)
    (p : ι→O) (hp : ∀i,Supported (Ideal.span {p i}))
    (e : ι→ℕ) (he : ∀i,0< e i) :
    ∃τ : Character,
      η.modulus*Ideal.span {m}*Ideal.span {(72:O)}*(∏i,Ideal.span {p i})≤τ.modulus ∧
      τ.modulus.absNorm≤η.modulus.absNorm*(Ideal.span {m}).absNorm*
        (Ideal.span {(72:O)}).absNorm*∏i,(Ideal.span {p i}).absNorm ∧
      ∀n:O,elementCoeff τ n=rowTwist (elementHom η) m 1 (∏i,(p i)^(e i)) n := by
  obtain ⟨base,hbase,hbasec⟩ := exists_supported_row_presentation η m 1 hm
    CenteredMomentAddedZero.supported_one_element hmLam hm2
  choose χ hχ hc using fun i=> exists_supported_row_presentation (η.power 0) m (p i) hm
    (hp i) hmLam hm2
  let B := η.modulus*Ideal.span {m}*Ideal.span {(72:O)}
  let M := B*∏i,Ideal.span {p i}
  have hb : M≤ base.modulus := by
    rw [hbase,Ideal.span_singleton_one,←Ideal.one_eq_top,mul_one]
    exact Ideal.mul_le_right
  have hch (i : ι) : M≤(χ i).modulus := by
    rw [hχ i]
    change B*(∏j,Ideal.span {p j})≤ B*Ideal.span {p i}
    apply Ideal.dvd_iff_le.mp
    exact mul_dvd_mul_left B (Finset.dvd_prod_of_mem (fun j=> Ideal.span {p j}) (Finset.mem_univ i))
  obtain ⟨τ,hM,ht⟩ := exists_product_presentation Finset.univ base χ e (fun i _=> he i) M hb
    (fun i _=> hch i)
  have hMn : M≠0 := mul_ne_zero
    (mul_ne_zero (mul_ne_zero η.modulus_ne_bot (Ideal.span_singleton_eq_bot.not.mpr hm))
      (Ideal.span_singleton_eq_bot.not.mpr (by norm_num)))
    (Finset.prod_ne_zero_iff.mpr (fun i _=>(hp i).1))
  refine ⟨τ,hM,?_,?_⟩
  · have hd : τ.modulus∣M := Ideal.dvd_iff_le.mpr hM
    have hn := Nat.le_of_dvd (Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hMn))
      (map_dvd Ideal.absNorm hd)
    simpa only [M,B,map_mul,map_prod] using hn
  · intro n
    rw [ht,hbasec]
    simp_rw [hc]
    exact row_product_formula Finset.univ η m p e hmLam hm2 n

end CenteredMomentRadicalFamily

end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson
open TruncatedPrincipalPoisson


noncomputable section
open scoped Classical BigOperators
namespace CenteredMomentExceptionalReflection
open HeckeFamily HeckeRowClosure CenteredExceptionalProfile CenteredMomentChildRows
open CenteredMomentFixedRay CenteredMomentExceptionalPair RayFourExpansion
open CanonicalRowCompletion CanonicalQuadraticSieve
local notation "O" => Eisenstein.O

theorem child_rows_zero_off_support (η : Character) (χ ξ : RayCharacter)
    (m A z n : O) (hmLam : lambda ∣ m) (hm2 : (2 : O) ∣ m)
    (hn : ¬Supported (Ideal.span {n})) :
    rowTwist (elementHom (childCharacter η χ)) m 1 (A*z) n = 0 ∧
      rowTwist (elementHom (childCharacter η ξ)) m 1 (A*(-z)) n = 0 := by
  exact ⟨rowTwist_zero_of_not_supported _ _ _ _ _ hmLam hm2 ((supported_iff_native _).not.mp hn),
    rowTwist_zero_of_not_supported _ _ _ _ _ hmLam hm2 ((supported_iff_native _).not.mp hn)⟩

theorem child_row_reflection (η : Character) (χ ξ : RayCharacter)
    (m A z : O) (hmLam : lambda ∣ m) (hm2 : (2 : O) ∣ m) (n : O) :
    rowTwist (elementHom (childCharacter η ξ)) m 1 (A*(-z)) n =
      rowTwist (elementHom (childCharacter η χ)) m 1 (A*z) n *
        elementCoeff (reflectionRatio χ ξ) n := by
  by_cases hn : Supported (Ideal.span {n})
  · rw [rowTwist_extract_sixth_mask _ m 1 (A*(-z)) n ((supported_iff_native _).mp hn),
      rowTwist_extract_sixth_mask _ m 1 (A*z) n ((supported_iff_native _).mp hn)]
    simp only [one_pow, one_mul]
    change elementCoeff (childCharacter η ξ) n * coprimalityMask m n *
        idealRowHom (A*(-z)) (Ideal.span {n}) =
      (elementCoeff (childCharacter η χ) n * coprimalityMask m n *
        idealRowHom (A*z) (Ideal.span {n})) * elementCoeff (reflectionRatio χ ξ) n
    rw [childCharacter_ratio, reflectionRatio, elementCoeff_product,
      HeckeUnitRows.elementCoeff_character]
    have hu : unitSupplement (-1 : Oˣ) n = idealRowHom (-1) (Ideal.span {n}) := by
      change (if quadraticSupported (Ideal.span {n}) then
        idealRowHom ((-1 : Oˣ) : O) (Ideal.span {n}) else 0) = _
      rw [if_pos ((supported_iff_native _).mp hn)]
      rfl
    rw [hu, show A*(-z) = (-1)*(A*z) by ring, idealRowHom_argument_mul]
    ring
  · obtain ⟨hleft, hright⟩ := child_rows_zero_off_support η χ ξ m A z n hmLam hm2 hn
    rw [hleft, hright, zero_mul]

theorem child_row_reflection_hom (η : Character) (χ ξ : RayCharacter)
    (m A z : O) (hmLam : lambda ∣ m) (hm2 : (2 : O) ∣ m) :
    rowTwist (elementHom (childCharacter η ξ)) m 1 (A*(-z)) =
      rowTwist (elementHom (childCharacter η χ)) m 1 (A*z) *
        elementHom (reflectionRatio χ ξ) := by
  ext n
  exact child_row_reflection η χ ξ m A z hmLam hm2 n

theorem fixedInducingRow_reflected (η : Character) (χ ξ : RayCharacter)
    (Q : Ideal O) (hQ : Q ≤ Ideal.span {(72 : O)})
    (m A z : O) (hmLam : lambda ∣ m) (hm2 : (2 : O) ∣ m)
    (hex : FixedInducingRow (childCharacter η χ) Q m A z) :
    FixedInducingRow (childCharacter η ξ) Q m A (-z) := by
  exact fixedInducingRow_of_product (childCharacter η χ) (childCharacter η ξ)
    (reflectionRatio χ ξ) Q m A z (-z) (reflectionRatio_modulus χ ξ Q hQ)
    (child_row_reflection η χ ξ m A z hmLam hm2) hex

theorem fixedInducingRow_reflection_iff (η : Character) (χ ξ : RayCharacter)
    (Q : Ideal O) (hQ : Q ≤ Ideal.span {(72 : O)})
    (m A z : O) (hmLam : lambda ∣ m) (hm2 : (2 : O) ∣ m) :
    FixedInducingRow (childCharacter η χ) Q m A z ↔
      FixedInducingRow (childCharacter η ξ) Q m A (-z) := by
  constructor
  · exact fixedInducingRow_reflected η χ ξ Q hQ m A z hmLam hm2
  · intro hex
    simpa only [neg_neg] using
      fixedInducingRow_reflected η ξ χ Q hQ m A (-z) hmLam hm2 hex

theorem not_fixedInducingRow_reflection_iff (η : Character) (χ ξ : RayCharacter)
    (Q : Ideal O) (hQ : Q ≤ Ideal.span {(72 : O)})
    (m A z : O) (hmLam : lambda ∣ m) (hm2 : (2 : O) ∣ m) :
    (¬FixedInducingRow (childCharacter η χ) Q m A z) ↔
      ¬FixedInducingRow (childCharacter η ξ) Q m A (-z) :=
  not_congr (fixedInducingRow_reflection_iff η χ ξ Q hQ m A z hmLam hm2)

end CenteredMomentExceptionalReflection

end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson
open TruncatedPrincipalPoisson


noncomputable section
open scoped BigOperators Classical SchwartzMap
namespace CenteredMomentRestrictedEnergy
open CanonicalQuadraticSieve CanonicalRowCompletion CenteredMomentRowNorm
open CenteredMomentPlainEnergy CenteredMomentPlainChildEnergy CenteredMomentCauchy CenteredMomentSmooth
local notation "O" => Eisenstein.O

def restrictedEnergy {α : Type*} (keep : O → Prop) (S : Finset α) (a : α → O)
    (c : α → ℂ) (W : 𝓢(ℝ, ℂ)) (K : ℝ) : ℝ :=
  ∑' z : O, if keep z then ‖rowPolynomial S a c z‖^2*(W (‖ringComplex z‖^2/K)).re else 0

theorem restricted_summable {α : Type*} (keep : O → Prop) (S : Finset α) (a : α → O)
    (ha : ∀ i, Supported (Ideal.span {a i})) (c : α → ℂ)
    (W : 𝓢(ℝ, ℂ)) (K : ℝ) (hK : 0 < K) :
    Summable (fun z : O => if keep z then
      ‖rowPolynomial S a c z‖^2*(W (‖ringComplex z‖^2/K)).re else 0) := by
  have hs := Complex.hasSum_re (rowEnergy_summable S a ha c W K hK).hasSum
  simp only [Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero] at hs
  exact hs.summable.indicator {z | keep z}

theorem finite_energy_le_restricted {α : Type*} (keep : O → Prop) (S : Finset α) (a : α → O)
    (ha : ∀ i, Supported (Ideal.span {a i})) (c : α → ℂ)
    (W : 𝓢(ℝ, ℂ)) (K : ℝ) (hK : 0 < K) (rows : Finset O)
    (hkeep : ∀ z ∈ rows, keep z)
    (hW : ∀ z : O, 0 ≤ (W (‖ringComplex z‖^2/K)).re)
    (hmajor : ∀ z ∈ rows, 1 ≤ (W (‖ringComplex z‖^2/K)).re) :
    (∑ z ∈ rows, ‖rowPolynomial S a c z‖^2) ≤ restrictedEnergy keep S a c W K := by
  calc
    _ ≤ ∑ z ∈ rows, if keep z then
        ‖rowPolynomial S a c z‖^2*(W (‖ringComplex z‖^2/K)).re else 0 := by
      apply Finset.sum_le_sum
      intro z hz
      rw [if_pos (hkeep z hz)]
      exact le_mul_of_one_le_right (sq_nonneg _) (hmajor z hz)
    _ ≤ _ := sum_le_hasSum rows
      (by intro z hz; split_ifs; exact mul_nonneg (sq_nonneg _) (hW z); exact le_rfl)
      (restricted_summable keep S a ha c W K hK).hasSum

theorem finite_negative_energy_le_restricted {α : Type*} (keep : O → Prop)
    (S : Finset α) (a : α → O) (ha : ∀ i, Supported (Ideal.span {a i})) (c : α → ℂ)
    (W : 𝓢(ℝ, ℂ)) (K : ℝ) (hK : 0 < K) (rows : Finset O)
    (hkeep : ∀ z ∈ rows, keep (-z))
    (hW : ∀ z : O, 0 ≤ (W (‖ringComplex z‖^2/K)).re)
    (hmajor : ∀ z ∈ rows, 1 ≤ (W (‖ringComplex z‖^2/K)).re) :
    (∑ z ∈ rows, ‖rowPolynomial S a c (-z)‖^2) ≤ restrictedEnergy keep S a c W K := by
  have he := finite_energy_le_restricted keep S a ha c W K hK (rows.image Neg.neg)
    (by intro z hz; obtain ⟨w,hw,rfl⟩ := Finset.mem_image.mp hz; exact hkeep w hw) hW
    (by intro z hz; obtain ⟨w,hw,rfl⟩ := Finset.mem_image.mp hz
        simpa only [map_neg,norm_neg] using hmajor w hw)
  rwa [Finset.sum_image (fun x hx y hy hxy => neg_injective hxy)] at he

def nonexceptional (η : HeckeFamily.Character) (χ : RayFourExpansion.RayCharacter)
    (Q : Ideal O) (m A₀ z : O) : Prop :=
  z ≠ 0 ∧ ¬CenteredExceptionalProfile.FixedInducingRow
    (CenteredMomentChildRows.childCharacter η χ) Q m A₀ z

theorem nonexceptional_reflection (η : HeckeFamily.Character)
    (χ ξ : RayFourExpansion.RayCharacter) (Q : Ideal O)
    (hQ : Q ≤ Ideal.span {(72:O)}) (m A₀ z : O)
    (hmLam : lambda ∣ m) (hm2 : (2:O) ∣ m) :
    nonexceptional η χ Q m A₀ z ↔ nonexceptional η ξ Q m A₀ (-z) := by
  unfold nonexceptional
  rw [neg_ne_zero]
  exact and_congr Iff.rfl (CenteredMomentExceptionalReflection.not_fixedInducingRow_reflection_iff
    η χ ξ Q hQ m A₀ z hmLam hm2)

theorem nonexceptional_ray_independent (η : HeckeFamily.Character)
    (χ ξ : RayFourExpansion.RayCharacter) (Q : Ideal O)
    (hQ : Q ≤ Ideal.span {(72:O)}) (m A₀ z : O)
    (hmLam : lambda ∣ m) (hm2 : (2:O) ∣ m) :
    nonexceptional η χ Q m A₀ z ↔ nonexceptional η ξ Q m A₀ z := by
  have h₁ := nonexceptional_reflection η χ ξ Q hQ m A₀ z hmLam hm2
  have h₂ := nonexceptional_reflection η ξ ξ Q hQ m A₀ (-z) hmLam hm2
  simpa only [neg_neg] using h₁.trans h₂

theorem whole_kernel_restricted_child_bound (W : 𝓢(ℝ, ℂ)) (V : Fin 4 → ℝ → ℂ)
    (M : Fin 4 → ℝ) (hM : ∀ i, 0 ≤ M i)
    (hV : ∀ i y, V i y ≠ 0 → |y| ≤ M i) (A J₁ J₂ : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ R : ℝ, 0 < R →
      ∀ {α β : Type*} (rows : Finset O) (S : Finset α) (T : Finset β)
        (a : α → O) (b : β → O)
        (_ha : ∀ i, Supported (Ideal.span {a i}))
        (_hb : ∀ j, Supported (Ideal.span {b j}))
        (c : α → ℂ) (d : β → ℂ) (u : α → ℝ) (v : β → ℝ)
        (ρ x : O → ℝ) (η : O → ℂ) (keep₁ keep₂ : O → Prop),
      (∀ z ∈ rows, keep₁ z) → (∀ z ∈ rows, keep₂ (-z)) →
      (∀ z ∈ rows, ‖η z‖ ≤ 1) →
      (∀ z ∈ rows, ‖V 0 (ρ z)‖ ≤ 1) → (∀ z ∈ rows, ‖V 1 (x z)‖ ≤ 1) →
      ∀ (U : 𝓢(ℝ, ℂ)) (K : ℝ), 0 < K →
      (∀ z : O, 0 ≤ (U (‖ringComplex z‖ ^ 2 / K)).re) →
      (∀ z ∈ rows, 1 ≤ (U (‖ringComplex z‖ ^ 2 / K)).re) →
      ∀ E₁ E₂ : ℝ, 0 ≤ E₁ → 0 ≤ E₂ →
      (∀ t : ℝ, (restrictedEnergy keep₁ S a (fun i => c i * columnPhase (V 2) (u i) t) U K) ≤
        (E₁ * (1 + ‖t‖) ^ J₁) ^ 2) →
      (∀ t : ℝ, (restrictedEnergy keep₂ T b (fun j => d j * star (columnPhase (V 3) (v j) t)) U K) ≤
        (E₂ * (1 + ‖t‖) ^ J₂) ^ 2) →
      (1 + R) ^ A * ‖∑ z ∈ rows, η z *
        (∑ i ∈ S, ∑ j ∈ T,
          ((c i * idealRowHom z (Ideal.span {a i})) * star (d j * idealRowHom (-z) (Ideal.span {b j}))) *
            wholeKernel W V R (ρ z) (x z) (u i) (v j))‖ ≤ C * (E₁ * E₂) := by
  obtain ⟨C, hC, hbound⟩ := whole_kernel_row_estimate W V M hM hV A (J₁ + J₂)
  refine ⟨C, hC, ?_⟩
  intro R hR α β rows S T a b ha hb c d u v ρ x η keep₁ keep₂ hkeep₁ hkeep₂ hη hV₀ hV₁ U K hK hU hmajor
    E₁ E₂ hE₁ hE₂ hleft hright
  apply hbound R hR rows S T
    (fun z i => c i * idealRowHom z (Ideal.span {a i}))
    (fun z j => d j * idealRowHom (-z) (Ideal.span {b j})) u v ρ x η hη hV₀ hV₁
    (E₁ * E₂) (mul_nonneg hE₁ hE₂)
  intro t
  have hL := (finite_energy_le_restricted keep₁ S a ha
    (fun i => c i * columnPhase (V 2) (u i) t) U K hK rows hkeep₁ hU hmajor).trans (hleft t)
  have hR' := (finite_negative_energy_le_restricted keep₂ T b hb
    (fun j => d j * star (columnPhase (V 3) (v j) t)) U K hK rows hkeep₂ hU hmajor).trans (hright t)
  have hl : Real.sqrt (∑ z ∈ rows,
      ‖rowPolynomial S a (fun i => c i * columnPhase (V 2) (u i) t) z‖ ^ 2) ≤
      E₁ * (1 + ‖t‖) ^ J₁ := (Real.sqrt_le_iff).mpr ⟨by positivity, hL⟩
  have hr : Real.sqrt (∑ z ∈ rows,
      ‖rowPolynomial T b (fun j => d j * star (columnPhase (V 3) (v j) t)) (-z)‖ ^ 2) ≤
      E₂ * (1 + ‖t‖) ^ J₂ := (Real.sqrt_le_iff).mpr ⟨by positivity, hR'⟩
  simp only [leftColumn_eq_rowPolynomial, rightColumn_eq_star_rowPolynomial, norm_star]
  calc
    _ ≤ (E₁ * (1 + ‖t‖) ^ J₁) * (E₂ * (1 + ‖t‖) ^ J₂) :=
      mul_le_mul hl hr (Real.sqrt_nonneg _) (by positivity)
    _ = _ := by rw [pow_add]; ring

end CenteredMomentRestrictedEnergy

end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson
open TruncatedPrincipalPoisson


noncomputable section
open scoped BigOperators Classical

namespace CenteredMomentSecondFamilyTransport
open HeckeFamily HeckeRowClosure CanonicalQuadraticSieve CanonicalRowCompletion CompletedGauss
open CenteredMomentSecondHeightFamily CenteredMomentSecondChildProfile CenteredMomentChildRows
open CenteredMomentSourceRow CenteredMomentHeckeColumnWindow CenteredMomentHeckeExpansion
open CenteredExceptionalProfile CenteredMomentRestrictedEnergy RayFourExpansion
local notation "O" => Eisenstein.O

theorem row_presentation_height (η τ : Character) (χ : RayCharacter) (A : O)
    (hτ : ∀ n,elementCoeff τ n=rowTwist (elementHom (childCharacter η χ)) fixedBadMask 1 A n)
    (I : Ideal O) (hI : Supported I) (t : ℝ) :
    heightCoeff τ t I=heightCoeff η t I*idealRowHom A I*rayMonoid χ (primaryIdealGenerator I) := by
  have he := idealCoeff_eq_row (childCharacter η χ) τ fixedBadMask 1 A hτ I
  have he' : heightCoeff τ t I=rowWeight (childCharacter η χ) fixedBadMask 1 A t I := by
    change idealCoeff τ I*(Ideal.absNorm I:ℂ)^(Complex.I*t)=_
    rw [he]
    simp only [rowWeight,MonoidWithZeroHom.coe_mk,ZeroHom.coe_mk,one_pow,one_mul,mul_one]
  rw [he',rowWeight_split,←heightCoeff_eq_fixed_rowWeight (childCharacter η χ) t I hI]
  simp only [heightCoeff,child_ideal_primary η χ I hI]
  ring

theorem exists_second_family_presentation (η : Character) (χ : RayCharacter)
    (A : O) (hA : A≠0) :
    ∃ τ : Character,
      τ.modulus.absNorm≤ rowConductorBound (childCharacter η χ) fixedBadMask 1 A ∧
      (∀ n,elementCoeff τ n=rowTwist (elementHom (childCharacter η χ)) fixedBadMask 1 A n) ∧
      ∀ I : Ideal O,Supported I → ∀ t : ℝ,
        heightCoeff τ t I=heightCoeff η t I*idealRowHom A I*rayMonoid χ (primaryIdealGenerator I) := by
  obtain ⟨τ,hN,hτ⟩ := exists_row_character_with_conductor (childCharacter η χ) fixedBadMask 1 A
    fixedBadMask_ne_zero one_ne_zero hA (dvd_mul_right _ _) (dvd_mul_left _ _)
  exact ⟨τ,hN,hτ,fun I hI t => row_presentation_height η τ χ A hτ I hI t⟩

theorem row_presentation_twist (η τ : Character) (χ : RayCharacter) (A : O)
    (hτ : ∀ n,elementCoeff τ n=rowTwist (elementHom (childCharacter η χ)) fixedBadMask 1 A n)
    (z n : O) :
    rowTwist (elementHom τ) fixedBadMask 1 z n=
      rowTwist (elementHom (childCharacter η χ)) fixedBadMask 1 (A*z) n := by
  by_cases hn : Supported (Ideal.span {n})
  · have hc : coprimalityMask fixedBadMask n=1 := by
      change (if IsCoprime fixedBadMask n then (1:ℂ) else 0)=1
      rw [if_pos (fixedBadMask_coprime n hn)]
    have ht := hτ n
    rw [rowTwist_extract_sixth_mask _ _ _ _ n ((supported_iff_native _).mp hn)] at ht
    rw [rowTwist_extract_sixth_mask _ _ _ _ n ((supported_iff_native _).mp hn),rowTwist_extract_sixth_mask _ _ _ _ n ((supported_iff_native _).mp hn)]
    change elementCoeff τ n*coprimalityMask fixedBadMask n*idealRowHom (1^4*z) (Ideal.span {n})=_
    rw [ht,hc]
    simp only [one_pow,one_mul,mul_one,idealRowHom_argument_mul]
    ring
  · have hmLam : lambda∣fixedBadMask := dvd_mul_right _ _
    have hm2 : (2:O)∣fixedBadMask := dvd_mul_left _ _
    exact (rowTwist_zero_of_not_supported (elementHom τ) fixedBadMask 1 z n hmLam hm2 ((supported_iff_native _).not.mp hn)).trans
      (rowTwist_zero_of_not_supported (elementHom (childCharacter η χ)) fixedBadMask 1 (A*z) n hmLam hm2 ((supported_iff_native _).not.mp hn)).symm

theorem fixedInducingRow_transport (η τ : Character) (χ : RayCharacter) (A : O)
    (hτ : ∀ n,elementCoeff τ n=rowTwist (elementHom (childCharacter η χ)) fixedBadMask 1 A n)
    (Q : Ideal O) (z : O) :
    FixedInducingRow τ Q fixedBadMask 1 z ↔
      FixedInducingRow (childCharacter η χ) Q fixedBadMask A z := by
  unfold FixedInducingRow
  simp only [one_mul,row_presentation_twist η τ χ A hτ]

theorem nonexceptional_transport (η τ : Character) (χ : RayCharacter) (A : O)
    (hτ : ∀ n,elementCoeff τ n=rowTwist (elementHom (childCharacter η χ)) fixedBadMask 1 A n)
    (Q : Ideal O) (z : O) :
    nonexceptional η χ Q fixedBadMask A z ↔
      z≠0 ∧ ¬FixedInducingRow τ Q fixedBadMask 1 z := by
  rw [nonexceptional,fixedInducingRow_transport η τ χ A hτ Q z]

end CenteredMomentSecondFamilyTransport

end

end

end GaloisForLFunctions.MetaplecticMobiusDescent.CubicEisenstein
