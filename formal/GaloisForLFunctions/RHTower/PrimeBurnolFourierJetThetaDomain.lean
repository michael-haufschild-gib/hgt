import GaloisForLFunctions.RHTower.PrimeBurnolFourierJetNeutralGraph
import GaloisForLFunctions.RHTower.PrimeBurnolThetaModularHolonomy
import GaloisForLFunctions.RHTower.SoninBandLimitedShellVanishing

/-!
# Actual theta polarization on the even Fourier-jet graph

Physical Fourier on both outputs implements the source-channel swap isometrically.
The literal single-prime theta polarization is a scalar combination of this swap,
the identity and the original neutral operation. It is bounded exactly at balanced
visibility and contrast. Its cubic displacement has a graph bound exactly at zero
theta parameter. These statements retain the original maximal-domain source action.
-/

open Complex MeasureTheory Set Filter Topology
open GaloisForLFunctions GaloisForLFunctions.HTGeometry
noncomputable section
namespace RHTower

def burnolJetSwap : BurnolJetAmbient →ₗᵢ[ℂ] BurnolJetAmbient where
  toFun z := ((z.1.2,z.1.1),(fourierUnitary z.2.1,fourierUnitary z.2.2))
  map_add' z w := by simp only [Prod.fst_add,Prod.snd_add,map_add,Prod.mk_add_mk]
  map_smul' a z := by simp only [Prod.smul_fst,Prod.smul_snd,map_smul,Prod.smul_mk,
    RingHom.id_apply]
  norm_map' z := by
    change max (max ‖z.1.2‖ ‖z.1.1‖)
      (max ‖fourierUnitary z.2.1‖ ‖fourierUnitary z.2.2‖) = _
    rw [fourierUnitary.norm_map,fourierUnitary.norm_map,max_comm ‖z.1.2‖ ‖z.1.1‖]
    rfl

theorem burnolJetSwap_source (f g : burnolSquarePosition.domain)
    (_hf : (f : SoninL2) ∈ evenSubspace) (hg : (g : SoninL2) ∈ evenSubspace) :
    burnolJetSwap (burnolJetGraphVector f g) = burnolJetGraphVector g f := by
  apply Prod.ext
  · rfl
  · change (fourierUnitary ((f : SoninL2)+fourierUnitary (g : SoninL2)),
      fourierUnitary (burnolSquarePosition f+fourierUnitary (burnolSquarePosition g))) =
      ((g : SoninL2)+fourierUnitary (f : SoninL2),
      burnolSquarePosition g+fourierUnitary (burnolSquarePosition f))
    rw [map_add,map_add,fourierUnitary_fourierUnitary_of_mem_evenSubspace hg,
      fourierUnitary_fourierUnitary_of_mem_evenSubspace (burnolSquarePosition_mem_evenSubspace g hg)]
    exact Prod.ext (add_comm _ _) (add_comm _ _)

theorem burnolJetSwap_preserves_closure :
    MapsTo burnolJetSwap (primeBurnolFourierJetEvenGraph.topologicalClosure : Set BurnolJetAmbient)
      (primeBurnolFourierJetEvenGraph.topologicalClosure : Set BurnolJetAmbient) := by
  have hc : IsClosed (burnolJetSwap ⁻¹'
      (primeBurnolFourierJetEvenGraph.topologicalClosure : Set BurnolJetAmbient)) :=
    primeBurnolFourierJetEvenGraph.isClosed_topologicalClosure.preimage burnolJetSwap.continuous
  apply closure_minimal _ hc
  intro z hz
  obtain ⟨f,g,hf,hg,rfl⟩ := (mem_primeBurnolFourierJetEvenGraph z).mp hz
  change burnolJetSwap (burnolJetGraphVector f g) ∈
    primeBurnolFourierJetEvenGraph.topologicalClosure
  rw [burnolJetSwap_source f g hf hg]
  exact primeBurnolFourierJetEvenGraph.le_topologicalClosure
    ((mem_primeBurnolFourierJetEvenGraph _).mpr ⟨g,f,hg,hf,rfl⟩)

def burnolJetGraphLinear : (burnolSquarePosition.domain × burnolSquarePosition.domain) →ₗ[ℂ]
    BurnolJetAmbient where
  toFun z := burnolJetGraphVector z.1 z.2
  map_add' z w := by
    apply Prod.ext
    · rfl
    · exact primeBurnolFourierJetSynthesis.map_add z w
  map_smul' a z := by
    apply Prod.ext
    · rfl
    · exact primeBurnolFourierJetSynthesis.map_smul a z

def burnolJetThetaSource (u w : ℂ) :
    Module.End ℂ (burnolSquarePosition.domain × burnolSquarePosition.domain) where
  toFun z := (u • z.1+w • z.2,w • z.1+(1-u) • z.2)
  map_add' z t := by
    apply Prod.ext <;> simp only [Prod.fst_add,Prod.snd_add] <;> module
  map_smul' a z := by
    apply Prod.ext <;> simp only [Prod.smul_fst,Prod.smul_snd,RingHom.id_apply] <;> module

def burnolJetNeutralSource :
    Module.End ℂ (burnolSquarePosition.domain × burnolSquarePosition.domain) where
  toFun z := (z.1,0)
  map_add' z w := by simp
  map_smul' a z := by simp

theorem burnolJetThetaSource_graph (u w : ℂ) (f g : burnolSquarePosition.domain)
    (hf : (f : SoninL2) ∈ evenSubspace) (hg : (g : SoninL2) ∈ evenSubspace) :
    burnolJetGraphLinear (burnolJetThetaSource u w (f,g)) =
      (1-u) • burnolJetGraphVector f g + (2*u-1) • burnolJetGraphVector f 0 +
        w • burnolJetSwap (burnolJetGraphVector f g) := by
  rw [burnolJetSwap_source f g hf hg]
  change burnolJetGraphLinear _ = (1-u) • burnolJetGraphLinear (f,g) +
    (2*u-1) • burnolJetGraphLinear (f,0) + w • burnolJetGraphLinear (g,f)
  rw [← map_smul,← map_smul,← map_smul,← map_add,← map_add]
  congr 1
  apply Prod.ext <;> simp only [burnolJetThetaSource,LinearMap.coe_mk,AddHom.coe_mk,
    Prod.fst_add,Prod.snd_add,Prod.smul_fst,Prod.smul_snd] <;> module

private theorem affine_neutral_bound_iff (a b d : ℂ) :
    (∃ C : ℝ, 0 ≤ C ∧ ∀ f g : burnolSquarePosition.domain,
      (f : SoninL2) ∈ evenSubspace → (g : SoninL2) ∈ evenSubspace →
      ‖a • burnolJetGraphVector f 0+b • burnolJetGraphVector f g+
        d • burnolJetSwap (burnolJetGraphVector f g)‖ ≤ C*‖burnolJetGraphVector f g‖) ↔ a=0 := by
  constructor
  · rintro ⟨C,hC,hbound⟩
    by_contra ha
    have hna : 0 < ‖a‖ := norm_pos_iff.mpr ha
    apply burnolJetNeutral_no_source_graph_bound
    refine ⟨(C+‖b‖+‖d‖)/‖a‖,div_nonneg (by positivity) hna.le,?_⟩
    intro f g hf hg
    have he : a • burnolJetGraphVector f 0 =
        (a • burnolJetGraphVector f 0+b • burnolJetGraphVector f g+
        d • burnolJetSwap (burnolJetGraphVector f g)) -
        b • burnolJetGraphVector f g-d • burnolJetSwap (burnolJetGraphVector f g) := by abel
    have hh : ‖a‖*‖burnolJetGraphVector f 0‖ ≤
        (C+‖b‖+‖d‖)*‖burnolJetGraphVector f g‖ := by
      rw [← norm_smul,he]
      have h1 := norm_sub_le
        (a • burnolJetGraphVector f 0+b • burnolJetGraphVector f g+
          d • burnolJetSwap (burnolJetGraphVector f g) - b • burnolJetGraphVector f g)
        (d • burnolJetSwap (burnolJetGraphVector f g))
      have h2 := norm_sub_le
        (a • burnolJetGraphVector f 0+b • burnolJetGraphVector f g+
          d • burnolJetSwap (burnolJetGraphVector f g)) (b • burnolJetGraphVector f g)
      rw [norm_smul,burnolJetSwap.norm_map] at h1
      rw [norm_smul] at h2
      have h3 := hbound f g hf hg
      nlinarith
    rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ hna).mpr
    simpa only [mul_comm ‖a‖ ‖burnolJetGraphVector f 0‖] using hh
  · rintro rfl
    refine ⟨‖b‖+‖d‖,by positivity,?_⟩
    intro f g hf hg
    simp only [zero_smul,zero_add]
    calc
      _ ≤ ‖b • burnolJetGraphVector f g‖+
          ‖d • burnolJetSwap (burnolJetGraphVector f g)‖ := norm_add_le _ _
      _ = _ := by rw [norm_smul,norm_smul,burnolJetSwap.norm_map]; ring

theorem burnolJetThetaSource_bounded_iff (u w : ℂ) :
    (∃ C : ℝ, 0 ≤ C ∧ ∀ f g : burnolSquarePosition.domain,
      (f : SoninL2) ∈ evenSubspace → (g : SoninL2) ∈ evenSubspace →
      ‖burnolJetGraphLinear (burnolJetThetaSource u w (f,g))‖ ≤ C*‖burnolJetGraphVector f g‖) ↔
        2*u=1 := by
  rw [← sub_eq_zero]
  rw [← affine_neutral_bound_iff (2*u-1) (1-u) w]
  constructor <;> rintro ⟨C,hC,hb⟩ <;> refine ⟨C,hC,?_⟩ <;> intro f g hf hg
  · have h := hb f g hf hg
    rw [burnolJetThetaSource_graph u w f g hf hg] at h
    simpa only [add_comm ((1-u) • _) ((2*u-1) • _)] using h
  · rw [burnolJetThetaSource_graph u w f g hf hg]
    simpa only [add_comm ((1-u) • _) ((2*u-1) • _)] using hb f g hf hg

theorem burnolJetThetaSource_displacement_square (u w : ℂ) :
    (burnolJetThetaSource u w-burnolJetNeutralSource)^2 =
      ((u-1)^2+w^2) • (1 : Module.End ℂ
        (burnolSquarePosition.domain × burnolSquarePosition.domain)) := by
  apply LinearMap.ext
  intro z
  apply Prod.ext <;>
    simp only [pow_two,Module.End.mul_apply,LinearMap.sub_apply,burnolJetThetaSource,
      burnolJetNeutralSource,LinearMap.coe_mk,AddHom.coe_mk,Prod.fst_sub,Prod.snd_sub,
      LinearMap.smul_apply,Module.End.one_apply,Prod.smul_fst,Prod.smul_snd] <;> module


def burnolJetRotationSource (v c : ℂ) :
    Module.End ℂ (burnolSquarePosition.domain × burnolSquarePosition.domain) where
  toFun z := (v • z.1-c • z.2,c • z.1+v • z.2)
  map_add' z t := by
    apply Prod.ext <;> simp only [Prod.fst_add,Prod.snd_add] <;> module
  map_smul' a z := by
    apply Prod.ext <;> simp only [Prod.smul_fst,Prod.smul_snd,RingHom.id_apply] <;> module

theorem burnolJetRotationSource_inverse_product (v c : ℂ) :
    burnolJetRotationSource v c * burnolJetRotationSource v (-c) =
      (v^2+c^2) • (1 : Module.End ℂ
        (burnolSquarePosition.domain × burnolSquarePosition.domain)) := by
  apply LinearMap.ext
  intro z
  apply Prod.ext <;>
    simp only [Module.End.mul_apply,burnolJetRotationSource,LinearMap.coe_mk,AddHom.coe_mk,
      LinearMap.smul_apply,Module.End.one_apply,Prod.smul_fst,Prod.smul_snd] <;> module

def burnolJetPrimeThetaSource (p : Nat.Primes) (a : ℝ) :=
  burnolJetThetaSource ((primeBurnolThetaVisibility a p : ℂ)^2)
    ((primeBurnolThetaVisibility a p : ℂ)*(primeBurnolThetaContrast a p : ℂ))

theorem burnolJetPrimeThetaSource_frame (p : Nat.Primes) (a : ℝ) :
    burnolJetPrimeThetaSource p a =
      burnolJetRotationSource (primeBurnolThetaVisibility a p) (primeBurnolThetaContrast a p) *
      burnolJetNeutralSource *
      burnolJetRotationSource (primeBurnolThetaVisibility a p) (-(primeBurnolThetaContrast a p)) := by
  have h : 1-(primeBurnolThetaVisibility a p : ℂ)^2 =
      (primeBurnolThetaContrast a p : ℂ)^2 := by
    have hh : (primeBurnolThetaVisibility a p : ℂ)^2+(primeBurnolThetaContrast a p : ℂ)^2=1 := by
      exact_mod_cast primeBurnolThetaVisibility_sq_add_contrast_sq a p
    linear_combination -hh
  apply LinearMap.ext
  intro z
  apply Prod.ext <;>
    simp only [Module.End.mul_apply,burnolJetRotationSource,burnolJetNeutralSource,
      burnolJetPrimeThetaSource,burnolJetThetaSource,LinearMap.coe_mk,AddHom.coe_mk,h] <;> module

theorem burnolJetPrimeThetaRotation_inverse (p : Nat.Primes) (a : ℝ) :
    burnolJetRotationSource (primeBurnolThetaVisibility a p) (primeBurnolThetaContrast a p) *
      burnolJetRotationSource (primeBurnolThetaVisibility a p) (-(primeBurnolThetaContrast a p)) = 1 := by
  rw [burnolJetRotationSource_inverse_product]
  have h : (primeBurnolThetaVisibility a p : ℂ)^2+(primeBurnolThetaContrast a p : ℂ)^2=1 := by
    exact_mod_cast primeBurnolThetaVisibility_sq_add_contrast_sq a p
  rw [h,one_smul]

theorem burnolJetPrimeThetaSource_bounded_iff (p : Nat.Primes) (a : ℝ) :
    (∃ C : ℝ, 0 ≤ C ∧ ∀ f g : burnolSquarePosition.domain,
      (f : SoninL2) ∈ evenSubspace → (g : SoninL2) ∈ evenSubspace →
      ‖burnolJetGraphLinear (burnolJetPrimeThetaSource p a (f,g))‖ ≤
        C*‖burnolJetGraphVector f g‖) ↔
      primeBurnolThetaVisibility a p^2 = primeBurnolThetaContrast a p^2 := by
  rw [burnolJetPrimeThetaSource,burnolJetThetaSource_bounded_iff]
  have he : 2*(primeBurnolThetaVisibility a p : ℂ)^2=1 ↔
      2*primeBurnolThetaVisibility a p^2=1 := by norm_cast
  rw [he]
  have h := primeBurnolThetaVisibility_sq_add_contrast_sq a p
  constructor <;> intro he <;> linarith

theorem burnolJetPrimeTheta_displacement_cube (p : Nat.Primes) (a : ℝ) :
    (burnolJetPrimeThetaSource p a-burnolJetNeutralSource)^3 =
      (primeBurnolThetaContrast a p : ℂ)^2 •
        (burnolJetPrimeThetaSource p a-burnolJetNeutralSource) := by
  have h : (primeBurnolThetaVisibility a p : ℂ)^2+
      (primeBurnolThetaContrast a p : ℂ)^2=1 := by
    exact_mod_cast primeBurnolThetaVisibility_sq_add_contrast_sq a p
  have hk : ((primeBurnolThetaVisibility a p : ℂ)^2-1)^2+
      ((primeBurnolThetaVisibility a p : ℂ)*(primeBurnolThetaContrast a p : ℂ))^2 =
      (primeBurnolThetaContrast a p : ℂ)^2 := by
    have hu : (primeBurnolThetaVisibility a p : ℂ)^2-1 =
        -(primeBurnolThetaContrast a p : ℂ)^2 := by linear_combination h
    rw [hu]
    calc
      _ = (primeBurnolThetaContrast a p : ℂ)^2 *
          ((primeBurnolThetaVisibility a p : ℂ)^2+(primeBurnolThetaContrast a p : ℂ)^2) := by ring
      _ = _ := by rw [h,mul_one]
  change (burnolJetThetaSource _ _-burnolJetNeutralSource)^3 = _
  rw [pow_succ,burnolJetThetaSource_displacement_square,hk,smul_mul_assoc,one_mul]
  rfl

theorem burnolJetPrimeTheta_displacement_cube_graph (p : Nat.Primes) (a : ℝ)
    (f g : burnolSquarePosition.domain)
    (hf : (f : SoninL2) ∈ evenSubspace) (hg : (g : SoninL2) ∈ evenSubspace) :
    burnolJetGraphLinear (((burnolJetPrimeThetaSource p a-burnolJetNeutralSource)^3) (f,g)) =
      (-2*(primeBurnolThetaContrast a p : ℂ)^4) • burnolJetGraphVector f 0 +
      (primeBurnolThetaContrast a p : ℂ)^4 • burnolJetGraphVector f g +
      ((primeBurnolThetaVisibility a p : ℂ)*(primeBurnolThetaContrast a p : ℂ)^3) •
        burnolJetSwap (burnolJetGraphVector f g) := by
  have h : (primeBurnolThetaVisibility a p : ℂ)^2 =
      1-(primeBurnolThetaContrast a p : ℂ)^2 := by
    have hh : (primeBurnolThetaVisibility a p : ℂ)^2+
        (primeBurnolThetaContrast a p : ℂ)^2=1 := by
      exact_mod_cast primeBurnolThetaVisibility_sq_add_contrast_sq a p
    linear_combination hh
  rw [burnolJetPrimeTheta_displacement_cube,LinearMap.smul_apply,map_smul,
    LinearMap.sub_apply,map_sub]
  change (primeBurnolThetaContrast a p : ℂ)^2 •
    (burnolJetGraphLinear (burnolJetThetaSource _ _ (f,g))-burnolJetGraphVector f 0) = _
  rw [burnolJetThetaSource_graph _ _ f g hf hg,h]
  module

theorem burnolJetPrimeTheta_displacement_cube_bounded_iff (p : Nat.Primes) (a : ℝ) :
    (∃ C : ℝ, 0 ≤ C ∧ ∀ f g : burnolSquarePosition.domain,
      (f : SoninL2) ∈ evenSubspace → (g : SoninL2) ∈ evenSubspace →
      ‖burnolJetGraphLinear (((burnolJetPrimeThetaSource p a-burnolJetNeutralSource)^3) (f,g))‖ ≤
        C*‖burnolJetGraphVector f g‖) ↔ primeBurnolThetaContrast a p=0 := by
  have he := affine_neutral_bound_iff (-2*(primeBurnolThetaContrast a p : ℂ)^4)
    ((primeBurnolThetaContrast a p : ℂ)^4)
    ((primeBurnolThetaVisibility a p : ℂ)*(primeBurnolThetaContrast a p : ℂ)^3)
  have hz : (-2*(primeBurnolThetaContrast a p : ℂ)^4=0) ↔ primeBurnolThetaContrast a p=0 := by
    norm_num
  rw [← hz,← he]
  constructor <;> rintro ⟨C,hC,hb⟩ <;> refine ⟨C,hC,?_⟩ <;> intro f g hf hg
  · have h := hb f g hf hg
    rwa [burnolJetPrimeTheta_displacement_cube_graph p a f g hf hg] at h
  · rw [burnolJetPrimeTheta_displacement_cube_graph p a f g hf hg]
    exact hb f g hf hg

theorem primeBurnolThetaContrast_eq_zero_iff (p : Nat.Primes) (a : ℝ) :
    primeBurnolThetaContrast a p=0 ↔ a=0 := by
  have hlog : Real.log (p : ℝ) ≠ 0 := (primeBurnolLogRate p).property.ne'
  have ht : Real.tanh (a*Real.log (p : ℝ)/2)=0 ↔ a*Real.log (p : ℝ)/2=0 := by
    constructor
    · intro h
      exact HTGeometry.tanh_strictMono.injective (h.trans Real.tanh_zero.symm)
    · intro h
      rw [h,Real.tanh_zero]
  change Real.tanh (a*Real.log (p : ℝ)/2)=0 ↔ a=0
  rw [ht]
  simp [hlog]

theorem burnolJetPrimeTheta_displacement_cube_bounded_iff_zero (p : Nat.Primes) (a : ℝ) :
    (∃ C : ℝ, 0 ≤ C ∧ ∀ f g : burnolSquarePosition.domain,
      (f : SoninL2) ∈ evenSubspace → (g : SoninL2) ∈ evenSubspace →
      ‖burnolJetGraphLinear (((burnolJetPrimeThetaSource p a-burnolJetNeutralSource)^3) (f,g))‖ ≤
        C*‖burnolJetGraphVector f g‖) ↔ a=0 := by
  rw [burnolJetPrimeTheta_displacement_cube_bounded_iff,primeBurnolThetaContrast_eq_zero_iff]

end RHTower
