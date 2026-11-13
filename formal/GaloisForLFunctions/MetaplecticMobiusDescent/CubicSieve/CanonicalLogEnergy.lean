/-
Canonical logarithmic energy adapted from OpenAI's formalization, Apache-2.0.
See LICENSE and NOTICE in the parent directory for source attribution.
-/
import GaloisForLFunctions.MetaplecticMobiusDescent.CubicSieve.ReopenedCubeFamilies

/-!
# Canonical logarithmic energy

The canonical logarithmic energy `canonicalLogEnergy` of the cube residuals and its oriented
log profiles. The phases at four cancel between the two passages; each source mode is an
oriented first-pass block with its Möbius coefficient.
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
open Eisenstein SchwartzPlanePoisson
open scoped Classical

def nonzeroRowMajorantSum (P : O → ℂ) (Y : ℝ) : ℂ :=
  ∑' z : O, if z = 0 then 0 else
    rowMajorant (‖ringComplex z‖ ^ 2 / Y) * (↑(‖P z‖ ^ 2) : ℂ)

lemma nonzeroRowMajorant_summable (P : O → ℂ) (Y : ℝ) (hY : 0 < Y) :
    Summable (fun z : O => if z = 0 then 0 else
      rowMajorant (‖ringComplex z‖ ^ 2 / Y) * (↑(‖P z‖ ^ 2) : ℂ)) := by
  apply (hasSum_sum_of_ne_finset_zero (s := rowMajorantBall Y) ?_).summable
  intro z hz
  rw [rowMajorant_zero_outside Y hY z hz]
  simp

theorem nonzeroRowMajorantSum_eq_sub (P : O → ℂ) (Y : ℝ) (hY : 0 < Y) :
    nonzeroRowMajorantSum P Y =
      (∑' z : O, rowMajorant (‖ringComplex z‖ ^ 2 / Y) * (↑(‖P z‖ ^ 2) : ℂ)) -
        (↑(‖P 0‖ ^ 2) : ℂ) := by
  have h := (rowMajorant_summable P Y hY).tsum_eq_add_tsum_ite 0
  have h0 : rowMajorant (0 : ℝ) = 1 := rowMajorant_one 0 (by norm_num) (by norm_num)
  simp only [map_zero, norm_zero, zero_pow (by decide : (2 : ℕ) ≠ 0), zero_div, h0, one_mul] at h
  change _ = _ + nonzeroRowMajorantSum P Y at h
  rw [h]
  ring

theorem finite_nonzero_row_energy_le_majorant (P : O → ℂ) (T : Finset O)
    (Y : ℝ) (hY : 0 < Y)
    (hT : ∀ z ∈ T, (Ideal.absNorm (Ideal.span {z}) : ℝ) ≤ Y)
    (hT0 : ∀ z ∈ T, z ≠ 0) :
    (∑ z ∈ T, ‖P z‖ ^ 2) ≤ (nonzeroRowMajorantSum P Y).re := by
  have hs := nonzeroRowMajorant_summable P Y hY
  unfold nonzeroRowMajorantSum
  rw [Complex.re_tsum hs]
  calc
    _ = ∑ z ∈ T, (if z = 0 then (0 : ℂ) else
        rowMajorant (‖ringComplex z‖ ^ 2 / Y) * (↑(‖P z‖ ^ 2) : ℂ)).re := by
      apply Finset.sum_congr rfl
      intro z hz
      have hratio : ‖ringComplex z‖ ^ 2 / Y ≤ 1 := by
        apply (div_le_one hY).2
        rw [ringComplex_norm_sq_eq_absNorm_span]
        exact hT z hz
      rw [if_neg (hT0 z hz), rowMajorant_one _ (div_nonneg (sq_nonneg _) hY.le) hratio, one_mul, Complex.ofReal_re]
    _ ≤ _ := by
      apply (Complex.hasSum_re hs.hasSum).summable.sum_le_tsum
      intro z hz
      split_ifs
      · norm_num
      · simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
        exact mul_nonneg (rowMajorant_nonneg _) (sq_nonneg _)

/-- The finite Eisenstein disk measured by squared complex norm. -/
def firstFrequencyDisk (K : ℝ) : Finset O :=
  (finite_norm_sublevel (Real.sqrt (max K 0))).toFinset.filter
    (fun z => ‖ringComplex z‖^2 ≤ K)

lemma mem_firstFrequencyDisk (K : ℝ) (z : O) :
    z ∈ firstFrequencyDisk K ↔ ‖ringComplex z‖^2 ≤ K := by
  constructor
  · exact fun h => (Finset.mem_filter.mp h).2
  · intro h
    apply Finset.mem_filter.mpr
    refine ⟨?_, h⟩
    rw [Set.Finite.mem_toFinset]
    change ‖ringComplex z‖ ≤ Real.sqrt (max K 0)
    calc
      _ = Real.sqrt (‖ringComplex z‖^2) := (Real.sqrt_sq (norm_nonneg _)).symm
      _ ≤ _ := Real.sqrt_le_sqrt (h.trans (le_max_left _ _))

lemma outside_firstFrequencyDisk (K : ℝ) (z : O) (h : z ∉ firstFrequencyDisk K) :
    K < ‖ringComplex z‖^2 := lt_of_not_ge (fun hz => h ((mem_firstFrequencyDisk K z).mpr hz))

end FirstPassCubeLabels

namespace SecondPassArithmetic
open Eisenstein SchwartzPlanePoisson FirstPassCubeLabels
open scoped Classical

def childLabelRotation (u : Oˣ) (negative : Bool) (z : Ideal O × O) : Ideal O × O :=
  (z.1,(u : O)^4*(if negative then -z.2 else z.2))

theorem childLabelRotation_injective (u : Oˣ) (negative : Bool) :
    Function.Injective (childLabelRotation u negative) := by
  intro z w he
  have hf := congrArg Prod.fst he
  change z.1=w.1 at hf
  have hs := congrArg Prod.snd he
  change (u : O)^4*(if negative then -z.2 else z.2)=
    (u : O)^4*(if negative then -w.2 else w.2) at hs
  have hz := mul_left_cancel₀ (pow_ne_zero 4 u.ne_zero) hs
  apply Prod.ext hf
  cases negative <;> simpa only [Bool.false_eq_true,ite_false,ite_true,neg_inj] using hz

theorem childLabelRotation_norm (u : Oˣ) (negative : Bool) (z : Ideal O × O) :
    ‖ringComplex (childLabelRotation u negative z).2‖^2=‖ringComplex z.2‖^2 := by
  cases negative <;> simp only [childLabelRotation,Bool.false_eq_true,ite_false,ite_true,
    map_mul,norm_mul,map_pow,norm_pow,norm_ringComplex_unit,
    one_pow,one_mul,map_neg,norm_neg]

theorem childLabelRotation_ne_zero (u : Oˣ) (negative : Bool) (z : Ideal O × O)
    (hz : z.2≠0) : (childLabelRotation u negative z).2≠0 := by
  apply mul_ne_zero (pow_ne_zero 4 u.ne_zero)
  cases negative <;> simpa using hz

section
variable {ι : Type*} [DecidableEq ι] (p : ι → O)
  [∀i,(Ideal.span {p i}).IsMaximal]
  (hg : ∀i,lambda∉Ideal.span {p i})

theorem fixedChildRow_label_mul (pool : Finset ι) (Ψ : O →* ℂ) (m : O)
    (H : Finset ι → ℂ) (u f z : O) :
    fixedChildRow p hg pool Ψ m H (u*f) z=
      fixedChildRow p hg pool Ψ m H f (u^4*z) := by
  unfold fixedChildRow
  apply Finset.sum_congr rfl
  intro S hS
  simp only [secondChildColumn,subsetRow_mul,row_pow,mul_pow]
  ring

theorem idealChildRow_eq_rotated (pool : Finset ι) (Ψ : O →* ℂ) (m : O)
    (H : Finset ι → ℂ) (negative : Bool) (u : Oˣ) (z : Ideal O × O) :
    idealChildRow p hg pool Ψ m H negative u z=
      fixedChildRow p hg pool Ψ m H
        (cubicIdealGenerator (childLabelRotation u negative z).1)
        (childLabelRotation u negative z).2 := by
  exact fixedChildRow_label_mul p hg pool Ψ m H (u : O) _ _

def canonicalSmoothedEnergy (pool : Finset ι) (Ψ : O →* ℂ) (m : O)
    (labels : Finset (Ideal O)) (H : Finset ι → ℂ) (K : ℝ) : ℝ :=
  (∑I∈labels,nonzeroRowMajorantSum
    (fixedChildRow p hg pool Ψ m H (cubicIdealGenerator I)) K).re

theorem canonicalSmoothedEnergy_nonneg (pool : Finset ι) (Ψ : O →* ℂ) (m : O)
    (labels : Finset (Ideal O)) (H : Finset ι → ℂ) (K : ℝ) (hK : 0<K) :
    0≤canonicalSmoothedEnergy p hg pool Ψ m labels H K := by
  unfold canonicalSmoothedEnergy
  rw [Complex.re_sum]
  apply Finset.sum_nonneg
  intro I hI
  have he := finite_nonzero_row_energy_le_majorant
    (fixedChildRow p hg pool Ψ m H (cubicIdealGenerator I)) ∅ K hK
    (by simp) (by simp)
  simpa using he

theorem canonicalSmoothedEnergy_zero_correction (pool : Finset ι) (Ψ : O →* ℂ) (m : O)
    (labels : Finset (Ideal O)) (H : Finset ι → ℂ) (K : ℝ) (hK : 0<K) :
    canonicalSmoothedEnergy p hg pool Ψ m labels H K=
      (∑I∈labels,∑'z:O,rowMajorant (‖ringComplex z‖^2/K)*
        (‖fixedChildRow p hg pool Ψ m H (cubicIdealGenerator I) z‖^2:ℝ)).re-
      ∑I∈labels,‖fixedChildRow p hg pool Ψ m H (cubicIdealGenerator I) 0‖^2 := by
  unfold canonicalSmoothedEnergy
  simp only [nonzeroRowMajorantSum_eq_sub _ K hK,Finset.sum_sub_distrib,Complex.sub_re,
    Complex.re_sum,Complex.ofReal_re]

theorem idealChildRow_energy_le_canonical (pool : Finset ι) (Ψ : O →* ℂ) (m : O)
    (H : Finset ι → ℂ) (negative : Bool) (u : Oˣ)
    (T : Finset (Ideal O × O)) (labels : Finset (Ideal O)) (K : ℝ) (hK : 0<K)
    (hlabels : ∀z∈T,z.1∈labels)
    (hrows : ∀z∈T,‖ringComplex z.2‖^2≤K) (hzero : ∀z∈T,z.2≠0) :
    (∑z∈T,‖idealChildRow p hg pool Ψ m H negative u z‖^2)≤
      canonicalSmoothedEnergy p hg pool Ψ m labels H K := by
  let f : Ideal O × O → ℝ := fun z=>
    ‖fixedChildRow p hg pool Ψ m H (cubicIdealGenerator z.1) z.2‖^2
  let R := (firstFrequencyDisk K).erase 0
  have hsub : T.image (childLabelRotation u negative)⊆labels.product R := by
    intro w hw
    obtain ⟨z,hz,rfl⟩ := Finset.mem_image.mp hw
    apply Finset.mem_product.mpr
    refine ⟨hlabels z hz,Finset.mem_erase.mpr ⟨childLabelRotation_ne_zero u negative z (hzero z hz),?_⟩⟩
    apply (mem_firstFrequencyDisk K _).mpr
    rw [childLabelRotation_norm]
    exact hrows z hz
  calc
    _ = ∑w∈T.image (childLabelRotation u negative),f w := by
      rw [Finset.sum_image]
      · apply Finset.sum_congr rfl
        intro z hz
        rw [idealChildRow_eq_rotated]
      · exact fun _ _ _ _ he=>childLabelRotation_injective u negative he
    _ ≤ ∑w∈labels.product R,f w :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _=>sq_nonneg _)
    _ = ∑I∈labels,∑z∈R,f (I,z) := by rw [Finset.product_eq_sprod,Finset.sum_product]
    _ ≤ ∑I∈labels,(nonzeroRowMajorantSum
        (fixedChildRow p hg pool Ψ m H (cubicIdealGenerator I)) K).re := by
      apply Finset.sum_le_sum
      intro I hI
      apply finite_nonzero_row_energy_le_majorant _ R K hK
      · intro z hz
        rw [←ringComplex_norm_sq_eq_absNorm_span]
        exact (mem_firstFrequencyDisk K z).mp (Finset.mem_erase.mp hz).2
      · exact fun z hz=>(Finset.mem_erase.mp hz).1
    _ = _ := by unfold canonicalSmoothedEnergy; rw [Complex.re_sum]

def canonicalLogEnergy (H : Finset ι → ℂ) (pool : Finset ι) (Ψ : O →* ℂ) (m : O)
    (labels : Finset (Ideal O)) (V : ℝ → ℂ) (X K : ℝ) : ℝ :=
  canonicalSmoothedEnergy p hg pool Ψ m labels (fun S=>H S * V (columnLog p X S)) K

end

def orientedLogProfile (negative : Bool) (V : ℝ → ℂ) : ℝ → ℂ :=
  if negative then fun s=>star (V s) else V

theorem fixedSecondTest_zero_profile {ι : Type*} [DecidableEq ι] (p : ι → O)
    (V : ℝ → ℂ) (X : ℝ) (negative : Bool) :
    fixedSecondTest p V X 0 0 negative=(fun S=>orientedLogProfile negative V (columnLog p X S)) := by
  funext S
  cases negative <;> simp [fixedSecondTest,orientedLogProfile,JointLogSeparation.fixedColumnTest,kernelLogPhase]

end SecondPassArithmetic

namespace SecondPassIntegration
open Eisenstein SchwartzPlanePoisson SecondPassArithmetic
open scoped Classical
local instance : Finite Oˣ := cubic_units_finite
local instance : Fintype Oˣ := Fintype.ofFinite _
variable {ι : Type*} [DecidableEq ι] (p : ι → O) (hp : ∀i,p i≠0)
  [∀i,(Ideal.span {p i}).IsMaximal] (hg : ∀i,lambda∉Ideal.span {p i})

theorem childEnergy_le_canonicalSmoothed (H : Finset ι → ℂ) (pool : Finset ι) (Ψ : O →* ℂ) (m : O)
    (T : Finset (Ideal O × O)) (labels : Finset (Ideal O)) (V : ℝ → ℂ)
    (X K a b : ℝ) (hK : 0<K) (testNegative rowNegative : Bool)
    (hlabels : ∀z∈T,z.1∈labels)
    (hrows : ∀z∈T,‖ringComplex z.2‖^2≤K) (hzero : ∀z∈T,z.2≠0) :
    childEnergy p hg H pool Ψ m T V X testNegative rowNegative a b≤
      (Fintype.card Oˣ : ℝ)*canonicalSmoothedEnergy p hg pool Ψ m labels
        (weightedSecondTest p H V X a b testNegative) K := by
  apply idealChildRow_unit_energy_le
  intro u
  exact idealChildRow_energy_le_canonical p hg pool Ψ m _ rowNegative u
    T labels K hK hlabels hrows hzero

include hp in
theorem childEnergy_le_canonicalLogEnergy (H : Finset ι → ℂ) (pool : Finset ι) (Ψ : O →* ℂ) (m : O)
    (T : Finset (Ideal O × O)) (labels : Finset (Ideal O)) (V : ℝ → ℂ)
    (X K a b : ℝ) (hX : 0<X) (hK : 0<K) (testNegative rowNegative : Bool)
    (hlabels : ∀z∈T,z.1∈labels)
    (hrows : ∀z∈T,‖ringComplex z.2‖^2≤K) (hzero : ∀z∈T,z.2≠0) :
    childEnergy p hg H pool Ψ m T V X testNegative rowNegative a b≤
      (Fintype.card Oˣ : ℝ)*canonicalLogEnergy p hg H pool
        (normHeightTwist Ψ (secondSignedHeight testNegative a b)) m labels
        (orientedLogProfile testNegative V) X K := by
  rw [childEnergy_normHeight p hp hg H pool Ψ m T V X a b hX testNegative rowNegative]
  have ht : weightedSecondTest p H V X 0 0 testNegative =
      (fun S => H S * orientedLogProfile testNegative V (columnLog p X S)) := by
    funext S
    unfold weightedSecondTest
    rw [fixedSecondTest_zero_profile]
  simpa only [canonicalLogEnergy,ht] using
    childEnergy_le_canonicalSmoothed p hg H pool
      (normHeightTwist Ψ (secondSignedHeight testNegative a b)) m T labels V X K 0 0 hK
      testNegative rowNegative hlabels hrows hzero

include hp in
theorem childEnergy_le_canonicalLogEnergy_actual_labels (H : Finset ι → ℂ) (pool : Finset ι) (Ψ : O →* ℂ) (m : O)
    (T : Finset (Ideal O × O)) (V : ℝ → ℂ)
    (X K a b : ℝ) (hX : 0<X) (hK : 0<K) (testNegative rowNegative : Bool)
    (hrows : ∀z∈T,‖ringComplex z.2‖^2≤K) (hzero : ∀z∈T,z.2≠0) :
    childEnergy p hg H pool Ψ m T V X testNegative rowNegative a b≤
      (Fintype.card Oˣ : ℝ)*canonicalLogEnergy p hg H pool
        (normHeightTwist Ψ (secondSignedHeight testNegative a b)) m (T.image Prod.fst)
        (orientedLogProfile testNegative V) X K :=
  childEnergy_le_canonicalLogEnergy p hp hg H pool Ψ m T (T.image Prod.fst) V X K a b hX hK
    testNegative rowNegative (fun z hz=>Finset.mem_image.mpr ⟨z,hz,rfl⟩) hrows hzero

end SecondPassIntegration

namespace SecondPassIntegration
open Eisenstein SchwartzPlanePoisson SecondPassArithmetic MeasureTheory
open scoped Classical
local instance : Finite Oˣ := cubic_units_finite
local instance : Fintype Oˣ := Fintype.ofFinite _
variable {ι : Type*} [DecidableEq ι] (p : ι → O) (hp : ∀i,p i≠0)
  [∀i,(Ideal.span {p i}).IsMaximal] (hg : ∀i,lambda∉Ideal.span {p i})

include hp in
theorem densityChildEnergy_from_canonical_state
    (H₁ H₂ : Finset ι → ℂ) (pool : Finset ι) (Ψ₁ Ψ₂ : O →* ℂ) (m : O)
    (T : Finset (Ideal O × O)) (labels : Finset (Ideal O)) (V₁ V₂ : ℝ → ℂ)
    (X F K E t₁ t₂ : ℝ) (J : ℕ) (hX : 0<X) (hK : 0<K) (hE : 0≤E)
    (hlabels : ∀z∈T,z.1∈labels)
    (hrows : ∀z∈T,‖ringComplex z.2‖^2≤K) (hzero : ∀z∈T,z.2≠0)
    (h₁ : ∀t,canonicalLogEnergy p hg H₁ pool (normHeightTwist Ψ₁ t) m labels
      (orientedLogProfile true V₁) X K≤E*(X*F)^2*(1+‖t‖)^(2*J))
    (h₂ : ∀t,canonicalLogEnergy p hg H₂ pool (normHeightTwist Ψ₂ t) m labels
      (orientedLogProfile false V₂) X K≤E*(X*F)^2*(1+‖t‖)^(2*J)) :
    densityChildEnergy p hg H₁ H₂ pool (normHeightTwist Ψ₁ t₁) (normHeightTwist Ψ₂ t₂)
      m T V₁ V₂ X X (2*J)≤
      (Fintype.card Oˣ : ℝ)*E*(X*F)^2*(1+‖t₁‖)^J*(1+‖t₂‖)^J*
        (∫t : ℝ,firstLogDensity 0 t)^3 := by
  have hleft (t : ℝ) : childEnergy p hg H₁ pool (normHeightTwist Ψ₁ t) m T V₁ X true false 0 0≤
      ((Fintype.card Oˣ : ℝ)*E*(X*F)^2)*(1+‖t‖)^(2*J) := by
    have hh := childEnergy_le_canonicalLogEnergy p hp hg H₁ pool (normHeightTwist Ψ₁ t) m
      T labels V₁ X K 0 0 hX hK true false hlabels hrows hzero
    simp only [normHeightTwist_twice,secondSignedHeight,ite_true,sub_self,add_zero] at hh
    exact hh.trans ((mul_le_mul_of_nonneg_left (h₁ t) (by positivity : (0:ℝ)≤Fintype.card Oˣ)).trans_eq (by ring))
  have hright (t : ℝ) : childEnergy p hg H₂ pool (normHeightTwist Ψ₂ t) m T V₂ X false true 0 0≤
      ((Fintype.card Oˣ : ℝ)*E*(X*F)^2)*(1+‖t‖)^(2*J) := by
    have hh := childEnergy_le_canonicalLogEnergy p hp hg H₂ pool (normHeightTwist Ψ₂ t) m
      T labels V₂ X K 0 0 hX hK false true hlabels hrows hzero
    simp only [normHeightTwist_twice,secondSignedHeight,Bool.false_eq_true,ite_false,sub_self,add_zero] at hh
    exact hh.trans ((mul_le_mul_of_nonneg_left (h₂ t) (by positivity : (0:ℝ)≤Fintype.card Oˣ)).trans_eq (by ring))
  have hb : 0≤(Fintype.card Oˣ : ℝ)*E*(X*F)^2 := by positivity
  have hd := densityChildEnergy_normHeight_polynomial p hp hg H₁ H₂ pool Ψ₁ Ψ₂ m T V₁ V₂
    X X t₁ t₂ ((Fintype.card Oˣ : ℝ)*E*(X*F)^2) ((Fintype.card Oˣ : ℝ)*E*(X*F)^2) J hX hX hb hb hleft hright
  rw [Real.mul_self_sqrt hb] at hd
  exact hd

end SecondPassIntegration

namespace SecondPassArithmetic
open Eisenstein SchwartzPlanePoisson FirstPassCubeLabels
open scoped Classical
variable {ι : Type*} [DecidableEq ι] (p : ι → O) (hp : ∀i,p i≠0)
  [∀i,(Ideal.span {p i}).IsMaximal]

def globalCanonicalLabels (source : Finset (GlobalSecondData ι)) (side : Bool)
    (q : Ideal O × Ideal O × Ideal O) (j : GlobalLogIndex) : Finset (Ideal O) :=
  (globalArithmeticTargets p source side q j).image Prod.fst

include hp in
theorem globalCanonicalLabels_bounds (source : Finset (GlobalSecondData ι)) (side : Bool)
    (q : Ideal O × Ideal O × Ideal O) (j : GlobalLogIndex)
    (hk : ∀x∈source,x.source.frequency≠0) :
    ∀I∈globalCanonicalLabels p source side q j,
      I≠⊥ ∧ Squarefree I ∧ (Ideal.absNorm I:ℝ)≤globalPooledLabelScale j := by
  intro I hI
  obtain ⟨z,hz,rfl⟩ := Finset.mem_image.mp hI
  have hb := globalArithmeticTargets_bounds p hp source side q j hk z hz
  exact ⟨hb.1,globalArithmeticTargets_squarefree p source side q j z hz,hb.2.1⟩

include hp in
theorem globalArithmeticTargets_ne_zero (source : Finset (GlobalSecondData ι)) (side : Bool)
    (q : Ideal O × Ideal O × Ideal O) (j : GlobalLogIndex)
    (hk : ∀x∈source,x.source.frequency≠0) :
    ∀z∈globalArithmeticTargets p source side q j,z.2≠0 := by
  intro z hz
  obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hz
  have hxs := (Finset.mem_filter.mp (Finset.mem_filter.mp hx).1).1
  dsimp only
  unfold globalSecondTuple
  rw [actualSecondTuple_newRow]
  exact actualSecondRow_ne_zero p hp _ _ _ (hk x hxs)

end SecondPassArithmetic

namespace SecondPassArithmetic
open Eisenstein SchwartzPlanePoisson FirstPassCubeLabels
open scoped Classical SchwartzMap

theorem nonzeroRowMajorantSum_exact_disk (P : O → ℂ) (K : ℝ) (hK : 0<K) :
    nonzeroRowMajorantSum P K=
      ∑z∈(firstFrequencyDisk (2*K)).erase 0,
        rowMajorant (‖ringComplex z‖^2/K)*(‖P z‖^2:ℝ) := by
  unfold nonzeroRowMajorantSum
  have hz (z : O) (hz : z∉(firstFrequencyDisk (2*K)).erase 0) :
      (if z=0 then 0 else rowMajorant (‖ringComplex z‖^2/K)*(‖P z‖^2:ℝ))=0 := by
    by_cases hzero : z=0
    · simp [hzero]
    have hn : z∉firstFrequencyDisk (2*K) := by
      intro hm
      exact hz (Finset.mem_erase.mpr ⟨hzero,hm⟩)
    have hlarge : 2<‖ringComplex z‖^2/K :=
      (lt_div_iff₀ hK).mpr (outside_firstFrequencyDisk (2*K) z hn)
    rw [if_neg hzero,rowMajorant_zero _ hlarge,zero_mul]
  rw [tsum_eq_sum hz]
  apply Finset.sum_congr rfl
  intro z hz
  rw [if_neg (Finset.mem_erase.mp hz).1]

def canonicalTerminalConstant (A M : ℝ) : ℝ :=
  2*(diagonalControl sieveCutoff)^4*SchwartzMap.seminorm ℝ 0 0 rowMajorant*(Real.exp A*M)^2

theorem canonicalTerminalConstant_nonneg (A M : ℝ) : 0≤canonicalTerminalConstant A M := by
  unfold canonicalTerminalConstant
  positivity

variable {ι : Type*} [DecidableEq ι] (p : ι → O) (hp : ∀i,p i≠0)
  [∀i,(Ideal.span {p i}).IsMaximal] (hg : ∀i,lambda∉Ideal.span {p i})

theorem canonicalSmoothedEnergy_uniform_row_bound (pool : Finset ι) (Ψ : O →* ℂ) (m : O)
    (labels : Finset (Ideal O)) (H : Finset ι → ℂ) (F K D : ℝ)
    (hF : 1≤F) (hK : 1≤K) (_hD : 0≤D)
    (hI0 : ∀I∈labels,I≠⊥) (hIF : ∀I∈labels,(Ideal.absNorm I:ℝ)≤F)
    (hrow : ∀I∈labels,∀z,‖fixedChildRow p hg pool Ψ m H
      (cubicIdealGenerator I) z‖≤D) :
    canonicalSmoothedEnergy p hg pool Ψ m labels H K≤
      2*(diagonalControl sieveCutoff)^2*SchwartzMap.seminorm ℝ 0 0 rowMajorant*F*K*D^2 := by
  have hdc := diagonalControl_nonneg sieveCutoff
  have hK0 : 0<K := zero_lt_one.trans_le hK
  let R := (firstFrequencyDisk (2*K)).erase 0
  have hR : (R.card:ℝ)≤(diagonalControl sieveCutoff)*(2*K) := by
    apply finite_norm_ball_card_bound R (2*K) (by linarith)
    exact fun z hz=>(mem_firstFrequencyDisk (2*K) z).mp (Finset.mem_erase.mp hz).2
  have hI : (labels.card:ℝ)≤(diagonalControl sieveCutoff)*F := finite_ideal_card_bound labels F hF hIF
  have hm : 0≤SchwartzMap.seminorm ℝ 0 0 rowMajorant := by positivity
  unfold canonicalSmoothedEnergy
  simp_rw [nonzeroRowMajorantSum_exact_disk _ K hK0]
  rw [Complex.re_sum]
  calc
    _ ≤ ∑I∈labels,∑z∈R,SchwartzMap.seminorm ℝ 0 0 rowMajorant*D^2 := by
      apply Finset.sum_le_sum
      intro I hIL
      rw [Complex.re_sum]
      apply Finset.sum_le_sum
      intro z hz
      simp only [Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,mul_zero,sub_zero]
      exact mul_le_mul
        ((Complex.re_le_norm _).trans (rowMajorant.norm_le_seminorm ℝ _))
        (pow_le_pow_left₀ (norm_nonneg _) (hrow I hIL z) 2) (sq_nonneg _) hm
    _ = (labels.card:ℝ)*R.card*(SchwartzMap.seminorm ℝ 0 0 rowMajorant*D^2) := by simp; ring
    _ ≤ ((diagonalControl sieveCutoff)*F)*((diagonalControl sieveCutoff)*(2*K))*(SchwartzMap.seminorm ℝ 0 0 rowMajorant*D^2) :=
      mul_le_mul_of_nonneg_right (mul_le_mul hI hR (Nat.cast_nonneg _) (by positivity)) (by positivity)
    _ = _ := by ring

include hp in
theorem canonicalLogEnergy_subunit (H : Finset ι → ℂ) (pool : Finset ι) (Ψ : O →* ℂ) (m : O)
    (labels : Finset (Ideal O)) (V : ℝ → ℂ) (X K A : ℝ) (hX : 0<X)
    (hV : ∀s,V s≠0→|s|≤A) (hsmall : X*Real.exp A<1) :
    canonicalLogEnergy p hg H pool Ψ m labels V X K=0 := by
  have hcol (S : Finset ι) : V (columnLog p X S)=0 := by
    by_contra hn
    have hupper := columnLog_norm_upper p hp X A hX S ((le_abs_self _).trans (hV _ hn))
    have hlower := primeProductNorm_ge_one p hp S
    linarith
  have hrow (f y : O) : fixedChildRow p hg pool Ψ m
      (fun S=>H S * V (columnLog p X S)) f y=0 := by
    unfold fixedChildRow
    apply Finset.sum_eq_zero
    intro S hS
    simp only [secondChildColumn,hcol,mul_zero]
  simp only [canonicalLogEnergy,canonicalSmoothedEnergy,nonzeroRowMajorantSum,hrow,norm_zero,
    zero_pow (by decide : (2:ℕ)≠0),Complex.ofReal_zero,mul_zero,ite_self,tsum_zero,
    Finset.sum_const_zero,Complex.zero_re]

include hp in
theorem canonicalLogEnergy_terminal
    (hinj : Function.Injective (fun i=>Ideal.span {p i})) (hpr : ∀i,lambda^2∣p i-1)
    (H : Finset ι → ℂ) (hH : ∀S, ‖H S‖≤1)
    (pool : Finset ι) (Ψ : O →* ℂ) (hΨ : ∀z,‖Ψ z‖≤1) (m : O)
    (labels : Finset (Ideal O)) (V : ℝ → ℂ) (X F K A M : ℝ)
    (hX : 0<X) (hF : 1≤F) (hK : 1≤K) (hKF : K≤F) (hM : 0≤M)
    (hV : ∀s,‖V s‖≤M) (hVs : ∀s,V s≠0→|s|≤A)
    (hI0 : ∀I∈labels,I≠⊥) (hIF : ∀I∈labels,(Ideal.absNorm I:ℝ)≤F) :
    canonicalLogEnergy p hg H pool Ψ m labels V X K≤canonicalTerminalConstant A M*(X*F)^2 := by
  by_cases hscale : 1≤X*Real.exp A
  · have hcol : ∀S,V (columnLog p X S)≠0→primeProductNorm p S≤X*Real.exp A :=
      fun S hn=>columnLog_norm_upper p hp X A hX S ((le_abs_self _).trans (hVs _ hn))
    have hrow (I : Ideal O) (hI : I∈labels) (z : O) :
        ‖fixedChildRow p hg pool Ψ m (fun S=>H S * V (columnLog p X S))
          (cubicIdealGenerator I) z‖≤(diagonalControl sieveCutoff)*(X*Real.exp A)*M :=
      fixedChildRow_elementary p hp hg hinj hpr pool Ψ hΨ m _ z _ (X*Real.exp A) M hscale hM
        (fun S=>by
          rw [norm_mul]
          exact (mul_le_mul_of_nonneg_right (hH S) (norm_nonneg _)).trans
            (by simpa only [one_mul] using hV (columnLog p X S)))
        (fun S hs=>hcol S ((mul_ne_zero_iff.mp hs).2))
    have hb := canonicalSmoothedEnergy_uniform_row_bound p hg pool Ψ m labels
      (fun S=>H S * V (columnLog p X S)) F K ((diagonalControl sieveCutoff)*(X*Real.exp A)*M) hF hK (by have := diagonalControl_nonneg sieveCutoff; positivity) hI0 hIF hrow
    change canonicalLogEnergy p hg H pool Ψ m labels V X K≤_ at hb
    calc
      _ ≤ 2*(diagonalControl sieveCutoff)^2*SchwartzMap.seminorm ℝ 0 0 rowMajorant*F*K*((diagonalControl sieveCutoff)*(X*Real.exp A)*M)^2 := hb
      _ = canonicalTerminalConstant A M*X^2*F*K := by unfold canonicalTerminalConstant; ring
      _ ≤ canonicalTerminalConstant A M*X^2*F*F :=
        mul_le_mul_of_nonneg_left hKF (by have := canonicalTerminalConstant_nonneg A M; positivity)
      _ = _ := by ring
  · rw [canonicalLogEnergy_subunit p hp hg H pool Ψ m labels V X K A hX hVs (lt_of_not_ge hscale)]
    exact mul_nonneg (canonicalTerminalConstant_nonneg A M) (sq_nonneg _)

end SecondPassArithmetic

open scoped Classical
open scoped Classical

namespace FirstPassCubeLabels
open Eisenstein SchwartzPlanePoisson SecondPassArithmetic
open scoped Classical
variable {ι : Type*} [DecidableEq ι] (p : ι → O)
  [∀i,(Ideal.span {p i}).IsMaximal] (hg : ∀i,lambda∉Ideal.span {p i})

theorem primeCoprimeMask_four (hc : ∀i,ringChar (O ⧸ Ideal.span {p i})≠2) (S : Finset ι) :
    primeCoprimeMask p S 4 = 1 := by
  unfold primeCoprimeMask
  apply Finset.prod_eq_one
  intro i hi
  let : Field (O ⧸ Ideal.span {p i}) := Ideal.Quotient.field _
  let : Fintype (O ⧸ Ideal.span {p i}) := Fintype.ofFinite _
  have htwo : (2 : O ⧸ Ideal.span {p i}) ≠ 0 := by
    intro hz
    exact hc i ((Nat.prime_dvd_prime_iff_eq (CharP.char_is_prime (O ⧸ Ideal.span {p i}) _)
      Nat.prime_two).mp ((ringChar.spec (O ⧸ Ideal.span {p i}) 2).mp hz))
  have hfour : (4 : O ⧸ Ideal.span {p i}) ≠ 0 := by
    simpa only [show (2 : O ⧸ Ideal.span {p i})^2=4 by norm_num] using pow_ne_zero 2 htwo
  have hn : ¬ p i ∣ (4 : O) := by
    intro hd
    apply hfour
    simpa only [map_ofNat] using
      Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton.mpr hd)
  simp only [if_neg hn,sub_zero]

theorem primeSubsetRow_star_neg_one (S : Finset ι) :
    star (primeSubsetRow p (fun i=>complexSexticChar (Ideal.span {p i}) (hg i)) S (-1)) =
      primeSubsetRow p (fun i=>complexSexticChar (Ideal.span {p i}) (hg i)) S (-1) := by
  let z := primeSubsetRow p (fun i=>complexSexticChar (Ideal.span {p i}) (hg i)) S (-1)
  have hz : z^2=1 := by
    rw [pow_two,←subsetRow_mul]
    simp only [neg_one_mul,neg_neg,primeSubsetRow,map_one,Finset.prod_const_one]
  rw [sexticRow_star]
  change z^5=z
  calc
    _ = z*(z^2)^2 := by ring
    _ = z := by rw [hz]; ring

/-- The phases at four cancel between the two passages. -/
theorem combinedFixedColumn_eq_residue
    (hc : ∀i,ringChar (O ⧸ Ideal.span {p i})≠2)
    (negative : Bool) (r s : QuadraticRayRing) (H : Finset ι → ℂ) :
    combinedFixedColumn p hg negative r s H =
      if r=s then firstResidueMask p r (fun S=>
        (if negative then primeSubsetRow p (fun i=>complexSexticChar (Ideal.span {p i}) (hg i)) S (-1)
          else 1)*H S) else (fun _=>0) := by
  funext S
  have hfour := primeSubsetRow_diagonal p (fun i=>complexSexticChar (Ideal.span {p i}) (hg i)) S 4
  rw [primeCoprimeMask_four p hc S] at hfour
  by_cases hrs : r=s
  · subst s
    simp only [combinedFixedColumn,secondRayColumn,firstFixedColumn,firstResidueMask,
      ite_true,primeSubsetRow_star_neg_one]
    by_cases hr : Ideal.Quotient.mk (Ideal.span {(4 : O)}) (∏i∈S,p i)=r
    · simp only [if_pos hr]
      calc
        _ = (star (primeSubsetRow p (fun i=>complexSexticChar (Ideal.span {p i}) (hg i)) S 4)*
          primeSubsetRow p (fun i=>complexSexticChar (Ideal.span {p i}) (hg i)) S 4)*
            ((if negative then primeSubsetRow p (fun i=>complexSexticChar (Ideal.span {p i}) (hg i)) S (-1)
              else 1)*H S) := by ring
        _ = _ := by rw [hfour,one_mul]
    · simp only [if_neg hr,mul_zero]
  · simp only [combinedFixedColumn,secondRayColumn,firstFixedColumn,firstResidueMask,if_neg hrs]
    split_ifs with hs hr <;> simp_all

end FirstPassCubeLabels

namespace FirstPassCubeLabels
open Eisenstein SchwartzPlanePoisson SecondPassArithmetic
open scoped Classical
variable {ι : Type*} [DecidableEq ι] (p : ι → O)
  [∀i,(Ideal.span {p i}).IsMaximal] (hg : ∀i,lambda∉Ideal.span {p i})

lemma combinedFixedColumn_mul (negative : Bool) (r s : QuadraticRayRing)
    (H V : Finset ι → ℂ) :
    (fun S=>combinedFixedColumn p hg negative r s H S * V S)=
      combinedFixedColumn p hg negative r s (fun S=>H S*V S) := by
  funext S
  simp only [combinedFixedColumn,secondRayColumn,firstFixedColumn,firstResidueMask]
  split_ifs <;> ring

end FirstPassCubeLabels

namespace FirstPassCubeLabels
open Eisenstein SchwartzPlanePoisson SecondPassArithmetic
open scoped Classical

theorem conductorExponent_val (parityBit ε₁ ε₂ : Bool) :
    (conductorExponent parityBit ε₁ ε₂).val = (bit ε₁ + 5 * bit ε₂ + 3 * bit parityBit) % 6 := by
  cases parityBit <;> cases ε₁ <;> cases ε₂ <;> decide

theorem cube_pair_exponent_mod (m₁ m₂ : ℕ) (ε₁ ε₂ : Bool) :
    (bit ε₁ + 5 * bit ε₂ + 3 * m₁ + 15 * m₂) % 6 =
      (conductorExponent (parity (m₁ + m₂)) ε₁ ε₂).val := by
  have hmod := Nat.mod_lt (m₁ + m₂) (by decide : 0 < 2)
  rw [conductorExponent_val]
  cases ε₁ <;> cases ε₂ <;> by_cases h : (m₁ + m₂) % 2 = 1 <;>
    norm_num [parity, bit, h] <;> omega

def cubePairLocal (P : Ideal O) [P.IsMaximal] (hg : lambda ∉ P)
    (m₁ m₂ : ℕ) (ε₁ ε₂ : Bool) (z : O) : ℂ :=
  let q := complexSexticChar P hg (Ideal.Quotient.mk P z)
  q ^ bit ε₁ * star (q ^ bit ε₂) * q ^ (3 * m₁) * star (q ^ (3 * m₂))

theorem cubePairLocal_eq_character
    (P : Ideal O) [P.IsMaximal] (hg : lambda ∉ P)
    (m₁ m₂ : ℕ) (ε₁ ε₂ : Bool) (hm : 0 < m₁ + m₂ + bit ε₁ + bit ε₂) (z : O) :
    cubePairLocal P hg m₁ m₂ ε₁ ε₂ z =
      (complexSexticChar P hg ^ (conductorExponent (parity (m₁ + m₂)) ε₁ ε₂).val)
        (Ideal.Quotient.mk P z) := by
  let q := complexSexticChar P hg (Ideal.Quotient.mk P z)
  have hstar : star q = q ^ 5 := by
    have he : (complexSexticChar P hg)⁻¹ = complexSexticChar P hg ^ 5 := by
      calc
        _ = complexSexticChar P hg ^ 5 * (complexSexticChar P hg ^ 6)⁻¹ := by group
        _ = _ := by rw [(complexSexticChar_powers P hg).2.2,inv_one,mul_one]
    change star (complexSexticChar P hg (Ideal.Quotient.mk P z)) = _
    rw [MulChar.star_apply',he,MulChar.pow_apply' _ (by decide : (5:ℕ)≠0)]
  have hleft : cubePairLocal P hg m₁ m₂ ε₁ ε₂ z =
      q ^ (bit ε₁ + 5 * bit ε₂ + 3 * m₁ + 15 * m₂) := by
    change q ^ bit ε₁ * star (q ^ bit ε₂) * q ^ (3 * m₁) * star (q ^ (3 * m₂)) = _
    simp only [star_pow, hstar, ← pow_mul, ← pow_add]
    congr 1
    omega
  rw [hleft]
  by_cases hz : z ∈ P
  · have hq : q = 0 := by
      change complexSexticChar P hg (Ideal.Quotient.mk P z) = 0
      rw [Ideal.Quotient.eq_zero_iff_mem.mpr hz, MulChar.map_zero]
    rw [hq, Ideal.Quotient.eq_zero_iff_mem.mpr hz, MulChar.map_zero]
    exact zero_pow (by omega)
  · have hu : IsUnit (Ideal.Quotient.mk P z) := by
      let : Field (O ⧸ P) := Ideal.Quotient.field P
      exact isUnit_iff_ne_zero.mpr (fun h => hz (Ideal.Quotient.eq_zero_iff_mem.mp h))
    have h6 : q ^ 6 = 1 := by
      change complexSexticChar P hg (Ideal.Quotient.mk P z)^6=1
      rw [←MulChar.pow_apply' _ (by decide : (6:ℕ)≠0),(complexSexticChar_powers P hg).2.2]
      exact MulChar.one_apply hu
    rw [pow_eq_pow_mod _ h6, cube_pair_exponent_mod]
    exact (MulChar.pow_apply_coe _ _ hu.unit).symm

def cubeConductorSupport {κ : Type*} (B : Finset κ) (v₁ v₂ : κ → ℕ)
    (ε₁ ε₂ : κ → Bool) : Finset κ :=
  B.filter (fun j => conductorExponent (parity (v₁ j + v₂ j)) (ε₁ j) (ε₂ j) ≠ 0)

def cubePrincipalSupport {κ : Type*} (B : Finset κ) (v₁ v₂ : κ → ℕ)
    (ε₁ ε₂ : κ → Bool) : Finset κ :=
  B.filter (fun j => conductorExponent (parity (v₁ j + v₂ j)) (ε₁ j) (ε₂ j) = 0)

theorem cubeConductorExponent_ne_zero {κ : Type*} (B : Finset κ)
    (v₁ v₂ : κ → ℕ) (ε₁ ε₂ : κ → Bool) (j : cubeConductorSupport B v₁ v₂ ε₁ ε₂) :
    (conductorExponent (parity (v₁ j.val + v₂ j.val)) (ε₁ j.val) (ε₂ j.val)).val ≠ 0 := by
  exact (ZMod.val_eq_zero _).not.mpr (Finset.mem_filter.mp j.property).2

theorem cubeConductorExponent_lt_six {κ : Type*} (B : Finset κ)
    (v₁ v₂ : κ → ℕ) (ε₁ ε₂ : κ → Bool) (j : cubeConductorSupport B v₁ v₂ ε₁ ε₂) :
    (conductorExponent (parity (v₁ j.val + v₂ j.val)) (ε₁ j.val) (ε₂ j.val)).val < 6 :=
  ZMod.val_lt _

def multiplicityRow {κ : Type*} (p : κ → O) [∀ j, (Ideal.span {p j}).IsMaximal]
    (hg : ∀ j, lambda ∉ Ideal.span {p j}) (B : Finset κ) (v : κ → ℕ) (z : O) : ℂ :=
  ∏ j ∈ B, complexSexticChar (Ideal.span {p j}) (hg j) (Ideal.Quotient.mk (Ideal.span {p j}) z) ^ v j

def cubePairRow {κ : Type*} (p : κ → O) [∀ j, (Ideal.span {p j}).IsMaximal]
    (hg : ∀ j, lambda ∉ Ideal.span {p j}) (B : Finset κ) (v₁ v₂ : κ → ℕ)
    (ε₁ ε₂ : κ → Bool) (z : O) : ℂ :=
  primeSubsetRow p (fun j=>complexSexticChar (Ideal.span {p j}) (hg j)) (B.filter fun j => ε₁ j) z *
    star (primeSubsetRow p (fun j=>complexSexticChar (Ideal.span {p j}) (hg j)) (B.filter fun j => ε₂ j) z) *
    multiplicityRow p hg B v₁ z ^ 3 * star (multiplicityRow p hg B v₂ z ^ 3)

private theorem row_filter_eq_power_product {κ : Type*}
    (p : κ → O) [∀ j, (Ideal.span {p j}).IsMaximal] (hg : ∀ j, lambda ∉ Ideal.span {p j})
    (B : Finset κ) (ε : κ → Bool) (z : O) :
    primeSubsetRow p (fun j=>complexSexticChar (Ideal.span {p j}) (hg j)) (B.filter fun j => ε j) z =
      ∏ j ∈ B, complexSexticChar (Ideal.span {p j}) (hg j) (Ideal.Quotient.mk (Ideal.span {p j}) z) ^ bit (ε j) := by
  simp only [primeSubsetRow, Finset.prod_filter]
  apply Finset.prod_congr rfl
  intro j hj
  cases ε j <;> simp [bit]

theorem cubePairRow_eq_product {κ : Type*}
    (p : κ → O) [∀ j, (Ideal.span {p j}).IsMaximal] (hg : ∀ j, lambda ∉ Ideal.span {p j})
    (B : Finset κ) (v₁ v₂ : κ → ℕ) (ε₁ ε₂ : κ → Bool) (z : O) :
    cubePairRow p hg B v₁ v₂ ε₁ ε₂ z =
      ∏ j ∈ B, cubePairLocal (Ideal.span {p j}) (hg j) (v₁ j) (v₂ j) (ε₁ j) (ε₂ j) z := by
  simp only [cubePairRow, row_filter_eq_power_product, multiplicityRow,
    ← Finset.prod_pow, star_prod, ← Finset.prod_mul_distrib, ← pow_mul]
  apply Finset.prod_congr rfl
  intro j hj
  simp only [cubePairLocal, Nat.mul_comm]

private theorem principal_product_eq_mask {κ : Type*}
    (p : κ → O) [∀j,(Ideal.span {p j}).IsMaximal] (B : Finset κ) (z : O) :
    (∏j∈B,(1 : MulChar (O ⧸ Ideal.span {p j}) ℂ) (Ideal.Quotient.mk (Ideal.span {p j}) z)) =
      primeCoprimeMask p B z := by
  unfold primeCoprimeMask
  apply Finset.prod_congr rfl
  intro j hj
  by_cases hd : p j∣z
  · rw [Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton.mpr hd),MulChar.map_zero,if_pos hd]
    ring
  · rw [if_neg hd,sub_zero]
    apply MulChar.one_apply
    let : Field (O ⧸ Ideal.span {p j}) := Ideal.Quotient.field _
    apply isUnit_iff_ne_zero.mpr
    exact fun hz=>hd (Ideal.mem_span_singleton.mp (Ideal.Quotient.eq_zero_iff_mem.mp hz))

theorem cubePairRow_conductor_selection {κ : Type*}
    (p : κ → O) [∀ j, (Ideal.span {p j}).IsMaximal] (hg : ∀ j, lambda ∉ Ideal.span {p j})
    (B : Finset κ) (v₁ v₂ : κ → ℕ) (ε₁ ε₂ : κ → Bool)
    (hcover : ∀ j ∈ B, 0 < v₁ j + v₂ j + bit (ε₁ j) + bit (ε₂ j)) (z : O) :
    cubePairRow p hg B v₁ v₂ ε₁ ε₂ z =
      primeCoprimeMask p (cubePrincipalSupport B v₁ v₂ ε₁ ε₂) z *
        blockRow p hg (cubeActiveSupport B (fun j=>v₁ j+v₂ j) ε₁ ε₂)
          (fun j=>(conductorExponent (parity (v₁ j+v₂ j)) (ε₁ j) (ε₂ j)).val) z := by
  let e := fun j => conductorExponent (parity (v₁ j + v₂ j)) (ε₁ j) (ε₂ j)
  let f := fun j => (complexSexticChar (Ideal.span {p j}) (hg j) ^ (e j).val) (Ideal.Quotient.mk (Ideal.span {p j}) z)
  have hlocal : cubePairRow p hg B v₁ v₂ ε₁ ε₂ z = ∏ j ∈ B, f j := by
    rw [cubePairRow_eq_product]
    apply Finset.prod_congr rfl
    intro j hj
    exact cubePairLocal_eq_character (Ideal.span {p j}) (hg j) (v₁ j) (v₂ j)
      (ε₁ j) (ε₂ j) (hcover j hj) z
  have hzero : (∏ j ∈ B.filter (fun j => e j = 0), f j) =
      primeCoprimeMask p (cubePrincipalSupport B v₁ v₂ ε₁ ε₂) z := by
    rw [← principal_product_eq_mask]
    apply Finset.prod_congr rfl
    intro j hj
    have he : e j = 0 := (Finset.mem_filter.mp hj).2
    simp only [f, he, ZMod.val_zero, pow_zero]
  rw [hlocal, ← Finset.prod_filter_mul_prod_filter_not B (fun j => e j = 0) f, hzero]
  congr 1


end FirstPassCubeLabels

namespace SecondPassArithmetic
open Eisenstein SchwartzPlanePoisson FirstPassCubeLabels
open scoped Classical
variable {ι : Type*} [DecidableEq ι] (p : ι → O) (hp : ∀i,p i≠0)
  [∀i,(Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
  (hg : ∀i,lambda∉Ideal.span {p i})

def canonicalSourceCoefficient (Ψ : O→*ℂ) (m f : O)
    (H : Finset ι→ℂ) (S : Finset ι) : ℂ :=
  secondColumnCoefficient p S * Ψ (∏i∈S,p i) *
    primeCoprimeMask p S m *
    primeSubsetRow p (fun i=>complexSexticChar (Ideal.span {p i}) (hg i)) S f^4 * H S

include hp hcop in
theorem canonicalSourceCoefficient_union
    (hpr : ∀ i,lambda^2∣p i-1) (Ψ : O→*ℂ) (m f : O)
    (H : Finset ι→ℂ) (D S : Finset ι) (hd : Disjoint D S) :
    canonicalSourceCoefficient p hg Ψ m f H (D∪S) =
      canonicalSourceCoefficient p hg Ψ m f (fun _ => 1) D *
      (secondColumnCoefficient p S *
        multiplicativeCoreColumn p Ψ m (fun U => H (D∪U)) S *
        primeSubsetRow p (fun i=>complexSexticChar (Ideal.span {p i}) (hg i)) S (∏i∈D,p i)^4 *
        primeSubsetRow p (fun i=>complexSexticChar (Ideal.span {p i}) (hg i)) S f^4) := by
  have helem : Pairwise (Function.onFun IsCoprime p) := fun i j hij=>
    (Ideal.isCoprime_span_singleton_iff _ _).mp (hcop hij)
  have hA := secondColumnCoefficient_union p hp hg hpr helem D S hd
  simp only [canonicalSourceCoefficient,hA,Finset.prod_union hd,map_mul,
    primeSubsetRow_union p (fun i=>complexSexticChar (Ideal.span {p i}) (hg i)) D S hd,mask_union p hg D S hd,mul_pow,multiplicativeCoreColumn]
  ring

theorem canonicalCube_pair_row
    (B C N P : Finset ι) (v₁ v₂ : ι→ℕ) (ε₁ ε₂ : ι→Bool)
    (hcover : ∀ i∈B,0<v₁ i+v₂ i)
    (hCB : Disjoint C B) (hNC : Disjoint N C) (hPC : Disjoint P C)
    (hNB : Disjoint N B) (hPB : Disjoint P B) (hNP : Disjoint N P)
    (z : O) :
    star (primeSubsetRow p (fun i=>complexSexticChar (Ideal.span {p i}) (hg i))
      (((B.filter fun i => ε₂ i)∪C)∪N) z) *
      primeSubsetRow p (fun i=>complexSexticChar (Ideal.span {p i}) (hg i))
        (((B.filter fun i => ε₁ i)∪C)∪P) z *
      star (multiplicityRow p hg B v₂ z^3) *
      multiplicityRow p hg B v₁ z^3 =
    primeCoprimeMask p
      (C∪cubePrincipalSupport B v₁ v₂ ε₁ ε₂) z *
    blockRow p hg ((N∪P)∪cubeActiveSupport B (fun i => v₁ i+v₂ i) ε₁ ε₂)
      (threeBlockExponent N P (fun i => v₁ i+v₂ i) ε₁ ε₂) z := by
  have hA₁C : Disjoint (B.filter fun i => ε₁ i) C := hCB.symm.mono_left (Finset.filter_subset _ _)
  have hA₂C : Disjoint (B.filter fun i => ε₂ i) C := hCB.symm.mono_left (Finset.filter_subset _ _)
  have hA₁P : Disjoint (B.filter fun i => ε₁ i) P := hPB.symm.mono_left (Finset.filter_subset _ _)
  have hA₂N : Disjoint (B.filter fun i => ε₂ i) N := hNB.symm.mono_left (Finset.filter_subset _ _)
  have hCp : Disjoint C (cubePrincipalSupport B v₁ v₂ ε₁ ε₂) :=
    hCB.mono_right (Finset.filter_subset _ _)
  have hsel : cubePairRow p hg B v₁ v₂ ε₁ ε₂ z =
      primeCoprimeMask p (cubePrincipalSupport B v₁ v₂ ε₁ ε₂) z *
      blockRow p hg (cubeActiveSupport B (fun i => v₁ i+v₂ i) ε₁ ε₂)
        (fun i => (conductorExponent (parity (v₁ i+v₂ i)) (ε₁ i) (ε₂ i)).val) z := by
    exact cubePairRow_conductor_selection p hg B v₁ v₂ ε₁ ε₂
      (fun i hi => by have := hcover i hi;omega) z
  rw [primeSubsetRow_union p (fun i=>complexSexticChar (Ideal.span {p i}) (hg i)) _ N (Finset.disjoint_union_left.mpr ⟨hA₂N,hNC.symm⟩),
    primeSubsetRow_union p (fun i=>complexSexticChar (Ideal.span {p i}) (hg i)) _ P (Finset.disjoint_union_left.mpr ⟨hA₁P,hPC.symm⟩),
    primeSubsetRow_union p (fun i=>complexSexticChar (Ideal.span {p i}) (hg i)) _ C hA₂C,primeSubsetRow_union p (fun i=>complexSexticChar (Ideal.span {p i}) (hg i)) _ C hA₁C]
  simp only [star_mul]
  calc
    _ = (star (primeSubsetRow p (fun i=>complexSexticChar (Ideal.span {p i}) (hg i)) C z)*
        primeSubsetRow p (fun i=>complexSexticChar (Ideal.span {p i}) (hg i)) C z)*
      (star (primeSubsetRow p (fun i=>complexSexticChar (Ideal.span {p i}) (hg i)) N z)*
        primeSubsetRow p (fun i=>complexSexticChar (Ideal.span {p i}) (hg i)) P z)*
      cubePairRow p hg B v₁ v₂ ε₁ ε₂ z := by
        simp only [cubePairRow];ring
    _ = _ := by
      rw [primeSubsetRow_diagonal p (fun i=>complexSexticChar (Ideal.span {p i}) (hg i)) C z,
        hsel,
        threeBlockRow_factor p hg N P B hNP hNB hPB,
        mask_union p hg C _ hCp]
      ring

include hp hcop in
theorem canonicalSourceCoefficient_cube_split
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (hpr : ∀ i,lambda^2∣p i-1) (Ψ : O→*ℂ) (m f : O)
    (H : Finset ι→ℂ) (B C S : Finset ι) (ε₁ ε₂ : ι→Bool) (negative : Bool)
    (hCB : Disjoint C B) (hSC : Disjoint S C) (hSB : Disjoint S B) :
    let A := B.filter (fun i => if negative then ε₂ i else ε₁ i)
    canonicalSourceCoefficient p hg Ψ m f H ((A∪C)∪S) =
      canonicalSourceCoefficient p hg Ψ m f (fun _ => 1) (A∪C) *
      (secondColumnCoefficient p S *
        originalLabelColumn p hg B ε₁ ε₂ negative
          (multiplicativeCoreColumn p Ψ m (fun U => H ((A∪C)∪U)))
          (∏i∈C,p i) f S) := by
  dsimp only
  have hAC : Disjoint (B.filter fun i => if negative then ε₂ i else ε₁ i) C :=
    hCB.symm.mono_left (Finset.filter_subset _ _)
  have hAS : Disjoint (B.filter fun i => if negative then ε₂ i else ε₁ i) S :=
    hSB.symm.mono_left (Finset.filter_subset _ _)
  rw [canonicalSourceCoefficient_union p hp hcop hg hpr Ψ m f H _ S
    (Finset.disjoint_union_left.mpr ⟨hAS,hSC.symm⟩)]
  have hA : (∏i∈B.filter (fun i => if negative then ε₂ i else ε₁ i),p i) =
      aLabel p B (if negative then ε₂ else ε₁) := by
    cases negative <;> simp only [Bool.false_eq_true,ite_false,ite_true,aLabel,primeProduct,
      Finset.prod_filter,bit]
    all_goals
      apply Finset.prod_congr rfl
      intro i hi
      split_ifs <;> simp_all
  rw [Finset.prod_union hAC,hA]
  simp only [originalLabelColumn,cubeRadical,commonProduct_mask p hinj S B,if_pos hSB,mul_one]
  ring

end SecondPassArithmetic

namespace FirstPassCubeLabels
open Eisenstein SchwartzPlanePoisson SecondPassArithmetic
open scoped Classical SchwartzMap
variable {ι : Type*} [DecidableEq ι] (p : ι → O) (hp : ∀i,p i≠0)
  [∀i,(Ideal.span {p i}).IsMaximal] (hg : ∀i,lambda∉Ideal.span {p i})

def canonicalPairMode (N P B : Finset ι) (v : ι→ℕ) (ε₁ ε₂ : ι→Bool)
    (C₁ C₂ : Finset ι→ℂ) (W : 𝓢(ℝ,ℂ)) (V₁ V₂ : ℝ→ℂ)
    (X₁ X₂ K : ℝ) (d h : O) : ℂ :=
  (V₁ (columnLog p X₁ N)*V₂ (columnLog p X₂ P))*
    ((K:ℂ)/(‖ringComplex (∏i∈(N∪P)∪cubeActiveSupport B v ε₁ ε₂,p i)‖:ℂ))*
    paperRadialFourier W (K*‖ringComplex h‖^2/
      (‖ringComplex d‖^2*primeProductNorm p ((N∪P)∪cubeActiveSupport B v ε₁ ε₂)))*
    threeGaussRowFactor p hp hg N P B v ε₁ ε₂ C₁ C₂ d h

lemma canonicalPairMode_summable (N P B : Finset ι) (v : ι→ℕ) (ε₁ ε₂ : ι→Bool)
    (C₁ C₂ : Finset ι→ℂ) (W : 𝓢(ℝ,ℂ)) (V₁ V₂ : ℝ→ℂ)
    (X₁ X₂ K : ℝ) (hK : 0<K) (d : O) (hd : d≠0) :
    Summable (canonicalPairMode p hp hg N P B v ε₁ ε₂ C₁ C₂ W V₁ V₂ X₁ X₂ K d) := by
  let S := (N∪P)∪cubeActiveSupport B v ε₁ ε₂
  let e := threeBlockExponent N P v ε₁ ε₂
  let t := K/(‖ringComplex d‖^2*primeProductNorm p S)
  have ht : 0<t := div_pos hK (mul_pos
    (sq_pos_of_pos (norm_pos_iff.mpr (ringComplex_ne_zero hd))) (primeProductNorm_pos p hp S))
  have hs : Summable (fun h : O => paperRadialFourier W (t*‖ringComplex h‖^2)*star (blockRow p hg S e h)) := by
    apply Summable.of_norm
    apply Summable.of_nonneg_of_le (fun _ => norm_nonneg _) _
      (paperRadialFourier_lattice_summable_norm W t ht)
    intro h
    rw [norm_mul,norm_star]
    exact mul_le_of_le_one_right (norm_nonneg _) (blockRow_norm_le_one p hg S e h)
  let a : ℂ := (V₁ (columnLog p X₁ N)*V₂ (columnLog p X₂ P))*
    ((K:ℂ)/(‖ringComplex (∏i∈S,p i)‖:ℂ))*
    (star (secondColumnCoefficient p N*C₁ N)*(secondColumnCoefficient p P*C₂ P)*
    normalizedSubsetTraceGauss p hp (fun i=>complexSexticChar (Ideal.span {p i}) (hg i)^e i) S)*blockRow p hg S e d
  apply (hs.mul_left a).congr
  intro h
  dsimp only [canonicalPairMode,threeGaussRowFactor,a,t,S,e]
  have ht' : K/(‖ringComplex d‖^2*primeProductNorm p ((N∪P)∪cubeActiveSupport B v ε₁ ε₂))*
      ‖ringComplex h‖^2 = K*‖ringComplex h‖^2/(‖ringComplex d‖^2*
        primeProductNorm p ((N∪P)∪cubeActiveSupport B v ε₁ ε₂)) := by ring
  rw [ht']
  ring

lemma actualFirstKernel_summable (F B : Finset ι) (v : ι→ℕ) (ε₁ ε₂ : ι→Bool)
    (C₁ C₂ : Finset ι→ℂ) (W : 𝓢(ℝ,ℂ)) (V₁ V₂ : ℝ→ℂ)
    (X₁ X₂ K : ℝ) (hK : 0<K) (d : O) (hd : d≠0) :
    Summable (actualFirstKernel p hp hg F B v ε₁ ε₂ C₁ C₂ W V₁ V₂ X₁ X₂ K d) := by
  apply summable_sum
  intro N hN
  apply summable_sum
  intro P hP
  by_cases hNP : Disjoint N P
  · simp only [hNP,ite_true]
    change Summable (canonicalPairMode p hp hg N P B v ε₁ ε₂ C₁ C₂ W V₁ V₂ X₁ X₂ K d)
    exact
      canonicalPairMode_summable p hp hg N P B v ε₁ ε₂ C₁ C₂ W V₁ V₂ X₁ X₂ K hK d hd
  · simp only [hNP,ite_false]
    exact summable_zero

theorem canonicalPair_first_poisson
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (hc : ∀i,ringChar (O⧸Ideal.span {p i})≠2)
    (M N P B : Finset ι) (v : ι→ℕ) (ε₁ ε₂ : ι→Bool)
    (C₁ C₂ : Finset ι→ℂ) (W : 𝓢(ℝ,ℂ)) (V₁ V₂ : ℝ→ℂ)
    (X₁ X₂ K : ℝ) (hK : 0<K) :
    (V₁ (columnLog p X₁ N)*V₂ (columnLog p X₂ P))*
      (star (secondColumnCoefficient p N*C₁ N)*(secondColumnCoefficient p P*C₂ P))*
      (∑'z:O,primeCoprimeMask p M z*
        blockRow p hg ((N∪P)∪cubeActiveSupport B v ε₁ ε₂)
          (threeBlockExponent N P v ε₁ ε₂) z*W (‖ringComplex z‖^2/K)) =
    ∑D∈M.powerset,supportMobius D/
      (primeProductNorm p D:ℂ)*
      ∑'h:O,canonicalPairMode p hp hg N P B v ε₁ ε₂ C₁ C₂ W V₁ V₂ X₁ X₂ K
        (∏i∈D,p i) h := by
  have he : ∀i∈(N∪P)∪cubeActiveSupport B v ε₁ ε₂,threeBlockExponent N P v ε₁ ε₂ i≠0 := by
    intro i hi
    by_cases hn:i∈N
    · simp [threeBlockExponent,hn]
    by_cases hp':i∈P
    · simp [threeBlockExponent,hn,hp']
    · have hiC:i∈cubeActiveSupport B v ε₁ ε₂ := by simpa [hn,hp'] using hi
      simp only [threeBlockExponent,if_neg hn,if_neg hp']
      exact (ZMod.val_eq_zero _).not.mpr (Finset.mem_filter.mp hiC).2
  have he6 : ∀i∈(N∪P)∪cubeActiveSupport B v ε₁ ε₂,threeBlockExponent N P v ε₁ ε₂ i<6 := by
    intro i hi
    unfold threeBlockExponent
    split_ifs <;> first | omega | exact ZMod.val_lt _
  rw [masked_block_radial_poisson_product p hp hinj hg hc M _ _ he he6 W K hK]
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro D hD
  simp only [←tsum_mul_left]
  apply tsum_congr
  intro h
  dsimp only [canonicalPairMode,threeGaussRowFactor]
  simp only [primeProductNorm]
  ring

lemma tsum_actualFirstKernel (F B : Finset ι) (v : ι→ℕ) (ε₁ ε₂ : ι→Bool)
    (C₁ C₂ : Finset ι→ℂ) (W : 𝓢(ℝ,ℂ)) (V₁ V₂ : ℝ→ℂ)
    (X₁ X₂ K : ℝ) (hK : 0<K) (d : O) (hd : d≠0) :
    (∑'h:O,actualFirstKernel p hp hg F B v ε₁ ε₂ C₁ C₂ W V₁ V₂ X₁ X₂ K d h)=
      ∑N∈F.powerset,∑P∈F.powerset,if Disjoint N P then
        ∑'h:O,canonicalPairMode p hp hg N P B v ε₁ ε₂ C₁ C₂ W V₁ V₂ X₁ X₂ K d h else 0 := by
  have hs (N P : Finset ι) : Summable (fun h:O => if Disjoint N P then
      canonicalPairMode p hp hg N P B v ε₁ ε₂ C₁ C₂ W V₁ V₂ X₁ X₂ K d h else 0) := by
    by_cases hNP : Disjoint N P
    · simp only [hNP,ite_true]
      exact canonicalPairMode_summable p hp hg N P B v ε₁ ε₂ C₁ C₂ W V₁ V₂ X₁ X₂ K hK d hd
    · simp only [hNP,ite_false]
      exact summable_zero
  change (∑'h:O,∑N∈F.powerset,∑P∈F.powerset,if Disjoint N P then
      canonicalPairMode p hp hg N P B v ε₁ ε₂ C₁ C₂ W V₁ V₂ X₁ X₂ K d h else 0)=_
  rw [Summable.tsum_finsetSum (fun N hN => summable_sum (fun P hP => hs N P))]
  apply Finset.sum_congr rfl
  intro N hN
  rw [Summable.tsum_finsetSum (fun P hP => hs N P)]
  apply Finset.sum_congr rfl
  intro P hP
  split_ifs <;> simp

def disjointCanonicalSource (F M B : Finset ι) (v : ι→ℕ) (ε₁ ε₂ : ι→Bool)
    (C₁ C₂ : Finset ι→ℂ) (W : 𝓢(ℝ,ℂ)) (V₁ V₂ : ℝ→ℂ) (X₁ X₂ K : ℝ) : ℂ :=
  ∑N∈F.powerset,∑P∈F.powerset,if Disjoint N P then
    (V₁ (columnLog p X₁ N)*V₂ (columnLog p X₂ P))*
      (star (secondColumnCoefficient p N*C₁ N)*(secondColumnCoefficient p P*C₂ P))*
      (∑'z:O,primeCoprimeMask p M z*
        blockRow p hg ((N∪P)∪cubeActiveSupport B v ε₁ ε₂)
          (threeBlockExponent N P v ε₁ ε₂) z*W (‖ringComplex z‖^2/K)) else 0

theorem disjointCanonicalSource_poisson
    (hinj : Function.Injective (fun i=>Ideal.span {p i}))
    (hc : ∀i,ringChar (O⧸Ideal.span {p i})≠2)
    (F M B : Finset ι) (v : ι→ℕ) (ε₁ ε₂ : ι→Bool)
    (C₁ C₂ : Finset ι→ℂ) (W : 𝓢(ℝ,ℂ)) (V₁ V₂ : ℝ→ℂ)
    (X₁ X₂ K : ℝ) (hK : 0<K) :
    disjointCanonicalSource p hg F M B v ε₁ ε₂ C₁ C₂ W V₁ V₂ X₁ X₂ K =
    ∑D∈M.powerset,supportMobius D/
      (primeProductNorm p D:ℂ)*
      ∑'h:O,actualFirstKernel p hp hg F B v ε₁ ε₂ C₁ C₂ W V₁ V₂ X₁ X₂ K
        (∏i∈D,p i) h := by
  simp_rw [tsum_actualFirstKernel p hp hg F B v ε₁ ε₂ C₁ C₂ W V₁ V₂ X₁ X₂ K hK _
    (Finset.prod_ne_zero_iff.mpr (fun i _=>hp i))]
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro N hN
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro P hP
  by_cases hNP : Disjoint N P
  · simp only [hNP,ite_true]
    exact canonicalPair_first_poisson p hp hg hinj hc M N P B v ε₁ ε₂ C₁ C₂ W V₁ V₂ X₁ X₂ K hK
  · simp only [hNP,ite_false,mul_zero,Finset.sum_const_zero]

end FirstPassCubeLabels

open scoped Classical

namespace SecondPassArithmetic
open Eisenstein SchwartzPlanePoisson FirstPassCubeLabels
open scoped Classical SchwartzMap
variable {ι : Type*} [DecidableEq ι] (p : ι → O) (hp : ∀i,p i≠0)
  [∀i,(Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
  (hg : ∀i,lambda∉Ideal.span {p i})

def canonicalCubeSourcePair (B S T : Finset ι) (v₁ v₂ : ι→ℕ)
    (Ψ₁ Ψ₂ : O→*ℂ) (m₁ m₂ f : O) (H₁ H₂ : Finset ι→ℂ)
    (W : 𝓢(ℝ,ℂ)) (K : ℝ) : ℂ :=
  star (canonicalSourceCoefficient p hg Ψ₁ m₁ f H₁ S)*
    canonicalSourceCoefficient p hg Ψ₂ m₂ f H₂ T*
    ∑'z:O,(star (primeSubsetRow p (fun i=>complexSexticChar (Ideal.span {p i}) (hg i)) S z)*
      primeSubsetRow p (fun i=>complexSexticChar (Ideal.span {p i}) (hg i)) T z*
      star (multiplicityRow p hg B v₂ z^3)*
      multiplicityRow p hg B v₁ z^3)*W (‖ringComplex z‖^2/K)

def canonicalCubeOuter (b : CubeCoordinates ι) (C : Finset ι)
    (Ψ₁ Ψ₂ : O→*ℂ) (m₁ m₂ f : O) : ℂ :=
  star (canonicalSourceCoefficient p hg Ψ₁ m₁ f (fun _=>1) (b.rightDivisor∪C))*
    canonicalSourceCoefficient p hg Ψ₂ m₂ f (fun _=>1) (b.leftDivisor∪C)

def canonicalCubeResidual (b : CubeCoordinates ι) (C : Finset ι) (negative : Bool)
    (Ψ : O→*ℂ) (m f : O) (H : Finset ι→ℂ) : Finset ι→ℂ :=
  originalLabelColumn p hg b.support b.leftBit b.rightBit negative
    (multiplicativeCoreColumn p Ψ m (fun S=>H (((if negative then b.rightDivisor else b.leftDivisor)∪C)∪S)))
    (∏i∈C,p i) f

def canonicalCubeBeforePoisson (pool : Finset ι) (b : CubeCoordinates ι) (C : Finset ι)
    (Ψ₁ Ψ₂ : O→*ℂ) (m₁ m₂ f : O) (H₁ H₂ : Finset ι→ℂ)
    (W : 𝓢(ℝ,ℂ)) (K : ℝ) : ℂ :=
  canonicalCubeOuter p hg b C Ψ₁ Ψ₂ m₁ m₂ f*
    disjointCanonicalSource p hg (pool\(b.support∪C))
      (C∪cubePrincipalSupport b.support b.leftExponent b.rightExponent b.leftBit b.rightBit)
      b.support (fun i=>b.leftExponent i+b.rightExponent i) b.leftBit b.rightBit
      (canonicalCubeResidual p hg b C true Ψ₁ m₁ f H₁)
      (canonicalCubeResidual p hg b C false Ψ₂ m₂ f H₂)
      W (fun _=>1) (fun _=>1) 1 1 K

lemma cube_filter_left (b : CubeCoordinates ι) (hb : b.Admissible) :
    b.support.filter (fun i=>b.leftBit i)=b.leftDivisor := by
  ext i
  simp only [CubeCoordinates.leftBit,Finset.mem_filter,decide_eq_true_eq]
  exact and_iff_right_of_imp (fun hi=>hb.1 hi)

lemma cube_filter_right (b : CubeCoordinates ι) (hb : b.Admissible) :
    b.support.filter (fun i=>b.rightBit i)=b.rightDivisor := by
  ext i
  simp only [CubeCoordinates.rightBit,Finset.mem_filter,decide_eq_true_eq]
  exact and_iff_right_of_imp (fun hi=>hb.2 hi)

include hp hcop in
theorem canonicalCubeSourcePair_factor
    (hinj : Function.Injective (fun i=>Ideal.span {p i}))
    (hpr : ∀i,lambda^2∣p i-1)
    (b : CubeCoordinates ι) (hb : b.Admissible) (C N P : Finset ι)
    (hCB : Disjoint C b.support) (hNC : Disjoint N C) (hPC : Disjoint P C)
    (hNB : Disjoint N b.support) (hPB : Disjoint P b.support) (hNP : Disjoint N P)
    (Ψ₁ Ψ₂ : O→*ℂ) (m₁ m₂ f : O) (H₁ H₂ : Finset ι→ℂ)
    (W : 𝓢(ℝ,ℂ)) (K : ℝ) :
    canonicalCubeSourcePair p hg b.support ((b.rightDivisor∪C)∪N) ((b.leftDivisor∪C)∪P)
      b.leftExponent b.rightExponent Ψ₁ Ψ₂ m₁ m₂ f H₁ H₂ W K =
    canonicalCubeOuter p hg b C Ψ₁ Ψ₂ m₁ m₂ f*
      (star (secondColumnCoefficient p N*canonicalCubeResidual p hg b C true Ψ₁ m₁ f H₁ N)*
        (secondColumnCoefficient p P*canonicalCubeResidual p hg b C false Ψ₂ m₂ f H₂ P))*
      ∑'z:O,primeCoprimeMask p
        (C∪cubePrincipalSupport b.support b.leftExponent b.rightExponent b.leftBit b.rightBit) z*
        blockRow p hg ((N∪P)∪cubeActiveSupport b.support (fun i=>b.leftExponent i+b.rightExponent i) b.leftBit b.rightBit)
          (threeBlockExponent N P (fun i=>b.leftExponent i+b.rightExponent i) b.leftBit b.rightBit) z*
        W (‖ringComplex z‖^2/K) := by
  have hN := canonicalSourceCoefficient_cube_split p hp hcop hg hinj hpr Ψ₁ m₁ f H₁
    b.support C N b.leftBit b.rightBit true hCB hNC hNB
  have hP := canonicalSourceCoefficient_cube_split p hp hcop hg hinj hpr Ψ₂ m₂ f H₂
    b.support C P b.leftBit b.rightBit false hCB hPC hPB
  simp only [Bool.false_eq_true,ite_true,ite_false,cube_filter_left b hb,cube_filter_right b hb] at hN hP
  have hz (z : O) := canonicalCube_pair_row p hg b.support C N P b.leftExponent b.rightExponent
    b.leftBit b.rightBit b.support_pos hCB hNC hPC hNB hPB hNP z
  simp only [cube_filter_left b hb,cube_filter_right b hb] at hz
  simp only [canonicalCubeSourcePair,hN,hP,star_mul,canonicalCubeOuter,canonicalCubeResidual]
  simp only [Bool.false_eq_true,ite_true,ite_false]
  simp_rw [hz]
  ring

def canonicalCubeCorrelation (pool B : Finset ι) (v₁ v₂ : ι→ℕ)
    (Ψ₁ Ψ₂ : O→*ℂ) (m₁ m₂ f : O) (H₁ H₂ : Finset ι→ℂ)
    (W : 𝓢(ℝ,ℂ)) (K : ℝ) : ℂ :=
  ∑S∈pool.powerset,∑T∈pool.powerset,
    canonicalCubeSourcePair p hg B S T v₁ v₂ Ψ₁ Ψ₂ m₁ m₂ f H₁ H₂ W K

include hp hcop in
theorem canonicalCubeCorrelation_eq_blocks
    (hinj : Function.Injective (fun i=>Ideal.span {p i}))
    (hpr : ∀i,lambda^2∣p i-1) (pool : Finset ι) (v₁ v₂ : ι→₀ℕ)
    (hB : v₁.support∪v₂.support⊆pool)
    (Ψ₁ Ψ₂ : O→*ℂ) (m₁ m₂ f : O) (H₁ H₂ : Finset ι→ℂ)
    (W : 𝓢(ℝ,ℂ)) (K : ℝ) :
    canonicalCubeCorrelation p hg pool (v₁.support∪v₂.support) v₁ v₂ Ψ₁ Ψ₂ m₁ m₂ f H₁ H₂ W K =
      ∑A₂∈(v₁.support∪v₂.support).powerset,∑A₁∈(v₁.support∪v₂.support).powerset,
        ∑C∈(pool\(v₁.support∪v₂.support)).powerset,
          canonicalCubeBeforePoisson p hg pool ⟨v₁,v₂,A₁,A₂⟩ C Ψ₁ Ψ₂ m₁ m₂ f H₁ H₂ W K := by
  unfold canonicalCubeCorrelation
  rw [FiniteOverlapDecomposition.sum_pair_split_cube pool _ hB]
  apply Finset.sum_congr rfl
  intro A₂ hA₂
  apply Finset.sum_congr rfl
  intro A₁ hA₁
  apply Finset.sum_congr rfl
  intro C hC
  let b : CubeCoordinates ι:=⟨v₁,v₂,A₁,A₂⟩
  have hb : b.Admissible:=⟨Finset.mem_powerset.mp hA₁,Finset.mem_powerset.mp hA₂⟩
  have hCB : Disjoint C b.support := Finset.disjoint_left.mpr (fun i hiC hiB =>
    (Finset.mem_sdiff.mp ((Finset.mem_powerset.mp hC) hiC)).2 hiB)
  have hpool : (pool\(v₁.support∪v₂.support))\C=pool\(b.support∪C) := by
    ext i
    simp only [CubeCoordinates.support,b,Finset.mem_sdiff,Finset.mem_union]
    tauto
  rw [hpool]
  change _=canonicalCubeBeforePoisson p hg pool b C Ψ₁ Ψ₂ m₁ m₂ f H₁ H₂ W K
  simp only [canonicalCubeBeforePoisson,disjointCanonicalSource,Finset.mul_sum,one_mul]
  apply Finset.sum_congr rfl
  intro N hN
  apply Finset.sum_congr rfl
  intro P hP
  by_cases hNP : Disjoint N P
  · simp only [hNP,ite_true]
    have hNC : Disjoint N C:=Finset.disjoint_left.mpr (fun i hiN hiC =>
      (Finset.mem_sdiff.mp ((Finset.mem_powerset.mp hN) hiN)).2 (Finset.mem_union_right _ hiC))
    have hPC : Disjoint P C:=Finset.disjoint_left.mpr (fun i hiP hiC =>
      (Finset.mem_sdiff.mp ((Finset.mem_powerset.mp hP) hiP)).2 (Finset.mem_union_right _ hiC))
    have hNB : Disjoint N b.support:=Finset.disjoint_left.mpr (fun i hiN hiB =>
      (Finset.mem_sdiff.mp ((Finset.mem_powerset.mp hN) hiN)).2 (Finset.mem_union_left _ hiB))
    have hPB : Disjoint P b.support:=Finset.disjoint_left.mpr (fun i hiP hiB =>
      (Finset.mem_sdiff.mp ((Finset.mem_powerset.mp hP) hiP)).2 (Finset.mem_union_left _ hiB))
    simpa only [mul_assoc,b,CubeCoordinates.support] using canonicalCubeSourcePair_factor p hp hcop hg hinj hpr b hb C N P
      hCB hNC hPC hNB hPB hNP Ψ₁ Ψ₂ m₁ m₂ f H₁ H₂ W K
  · simp only [hNP,ite_false,mul_zero]

include hp in
theorem canonicalCubeBeforePoisson_eq_all_modes
    (hinj : Function.Injective (fun i=>Ideal.span {p i}))
    (hc : ∀i,ringChar (O⧸Ideal.span {p i})≠2)
    (pool:Finset ι) (b:CubeCoordinates ι) (C:Finset ι)
    (Ψ₁ Ψ₂:O→*ℂ) (m₁ m₂ f:O) (H₁ H₂:Finset ι→ℂ)
    (W:𝓢(ℝ,ℂ)) (K:ℝ) (hK:0<K) :
    canonicalCubeBeforePoisson p hg pool b C Ψ₁ Ψ₂ m₁ m₂ f H₁ H₂ W K =
      canonicalCubeOuter p hg b C Ψ₁ Ψ₂ m₁ m₂ f *
      ∑D∈(C∪cubePrincipalSupport b.support b.leftExponent b.rightExponent b.leftBit b.rightBit).powerset,
        supportMobius D/(primeProductNorm p D:ℂ)*
        ∑'h:O,actualFirstKernel p hp hg (pool\(b.support∪C)) b.support
          (fun i=>b.leftExponent i+b.rightExponent i) b.leftBit b.rightBit
          (canonicalCubeResidual p hg b C true Ψ₁ m₁ f H₁)
          (canonicalCubeResidual p hg b C false Ψ₂ m₂ f H₂)
          W (fun _=>1) (fun _=>1) 1 1 K
          (∏i∈D,p i) h := by
  unfold canonicalCubeBeforePoisson
  rw [disjointCanonicalSource_poisson p hp hg hinj hc _ _ _ _ _ _ _ _ _ _ _ _ _ _ hK]


include hp in
lemma canonicalSourceCoefficient_norm_le_one
    (hinj : Function.Injective (fun i=>Ideal.span {p i})) (hpr : ∀i,lambda^2∣p i-1)
    (Ψ : O →* ℂ) (hΨ : ∀u,‖Ψ u‖≤1) (m f : O) (S : Finset ι) :
    ‖canonicalSourceCoefficient p hg Ψ m f (fun _=>1) S‖≤1 := by
  have he : canonicalSourceCoefficient p hg Ψ m f (fun _=>1) S =
      secondChildColumn p hg Ψ m f 1 (fun _=>1) S := by
    simp only [canonicalSourceCoefficient,secondChildColumn,primeSubsetRow,map_one,Finset.prod_const_one,mul_one]
  rw [he]
  simpa only [norm_one] using secondChildColumn_norm_le_test p hp hg hinj hpr Ψ hΨ m f 1 (fun _=>1) S

include hp in
lemma canonicalCubeOuter_norm_le_one
    (hinj : Function.Injective (fun i=>Ideal.span {p i})) (hpr : ∀i,lambda^2∣p i-1)
    (b : CubeCoordinates ι) (C : Finset ι) (Ψ₁ Ψ₂ : O →* ℂ)
    (hΨ₁ : ∀u,‖Ψ₁ u‖≤1) (hΨ₂ : ∀u,‖Ψ₂ u‖≤1) (m₁ m₂ f : O) :
    ‖canonicalCubeOuter p hg b C Ψ₁ Ψ₂ m₁ m₂ f‖≤1 := by
  simp only [canonicalCubeOuter,norm_mul,norm_star]
  exact (mul_le_of_le_one_left (norm_nonneg _)
    (canonicalSourceCoefficient_norm_le_one p hp hg hinj hpr Ψ₁ hΨ₁ m₁ f _)).trans
    (canonicalSourceCoefficient_norm_le_one p hp hg hinj hpr Ψ₂ hΨ₂ m₂ f _)

end SecondPassArithmetic

namespace SecondPassArithmetic
open Eisenstein SchwartzPlanePoisson FirstPassCubeLabels MeasureTheory
open scoped Classical SchwartzMap

variable {ι : Type*} [DecidableEq ι] (p : ι → O) (hp : ∀i,p i≠0)
  [∀i,(Ideal.span {p i}).IsMaximal] (hg : ∀i,lambda∉Ideal.span {p i})
include hp in
omit [∀ (i : ι), (Ideal.span {p i}).IsMaximal] in
lemma columnLog_three_split (A C S:Finset ι) (hAC:Disjoint A C)
    (hAS:Disjoint A S) (hCS:Disjoint C S) (ell:ℝ) (hell:0<ell) :
    columnLog p ell ((A∪C)∪S)=columnLog p (ell/(primeProductNorm p A*primeProductNorm p C)) S := by
  unfold columnLog
  rw [primeProductNorm_union p _ _ (Finset.disjoint_union_left.mpr ⟨hAS,hCS⟩),
    primeProductNorm_union p A C hAC]
  congr 1
  have hA := (primeProductNorm_pos p hp A).ne'
  have hC := (primeProductNorm_pos p hp C).ne'
  field_simp

include hp in
lemma canonicalCubeResidual_log
    (b:CubeCoordinates ι) (hb:b.Admissible) (C S:Finset ι)
    (hCB:Disjoint C b.support) (hSC:Disjoint S C) (hSB:Disjoint S b.support)
    (negative:Bool) (Ψ:O→*ℂ) (m f:O) (g:𝓢(ℝ,ℂ)) (ell:ℝ) (hell:0<ell) :
    canonicalCubeResidual p hg b C negative Ψ m f (fun U=>g (columnLog p ell U)) S =
      originalLabelColumn p hg b.support b.leftBit b.rightBit negative
        (multiplicativeCoreColumn p Ψ m (fun U=>g (columnLog p
          (ell/(primeProductNorm p (b.sideDivisor (!negative))*primeProductNorm p C)) U)))
        (∏i∈C,p i) f S := by
  have hA : b.sideDivisor (!negative)⊆b.support := by
    cases negative
    · exact hb.1
    · exact hb.2
  have hlog:=columnLog_three_split p hp (b.sideDivisor (!negative)) C S
    (hCB.symm.mono_left hA) (hSB.symm.mono_left hA) hSC.symm ell hell
  unfold canonicalCubeResidual originalLabelColumn multiplicativeCoreColumn
  have hside : (if negative then b.rightDivisor else b.leftDivisor)=b.sideDivisor (!negative) := by cases negative <;> rfl
  rw [hside]
  dsimp only
  rw [hlog]

lemma actualFirstKernel_insert_windows
    (F B:Finset ι) (v:ι→ℕ) (ε₁ ε₂:ι→Bool) (Ψ₁ Ψ₂:O→*ℂ)
    (m₁ m₂ c f:O) (g₁ g₂ W V₁ V₂:𝓢(ℝ,ℂ)) (X₁ X₂ K:ℝ) (d h:O)
    (hV₁:∀t,g₁ t≠0→V₁ t=1) (hV₂:∀t,g₂ t≠0→V₂ t=1) :
    actualFirstKernel p hp hg F B v ε₁ ε₂
      (originalLabelColumn p hg B ε₁ ε₂ true
        (multiplicativeCoreColumn p Ψ₁ m₁ (fun S=>g₁ (columnLog p X₁ S))) c f)
      (originalLabelColumn p hg B ε₁ ε₂ false
        (multiplicativeCoreColumn p Ψ₂ m₂ (fun S=>g₂ (columnLog p X₂ S))) c f)
      W (fun _=>1) (fun _=>1) X₁ X₂ K d h =
    actualFirstKernel p hp hg F B v ε₁ ε₂
      (originalLabelColumn p hg B ε₁ ε₂ true
        (multiplicativeCoreColumn p Ψ₁ m₁ (fun S=>g₁ (columnLog p X₁ S))) c f)
      (originalLabelColumn p hg B ε₁ ε₂ false
        (multiplicativeCoreColumn p Ψ₂ m₂ (fun S=>g₂ (columnLog p X₂ S))) c f)
      W V₁ V₂ X₁ X₂ K d h := by
  unfold actualFirstKernel
  apply Finset.sum_congr rfl
  intro N hN
  apply Finset.sum_congr rfl
  intro P hP
  by_cases hNP:Disjoint N P
  · simp only [hNP,ite_true,one_mul]
    by_cases h₁:g₁ (columnLog p X₁ N)=0
    · simp only [threeGaussRowFactor,originalLabelColumn,multiplicativeCoreColumn,h₁,mul_zero,zero_mul,star_zero]
    by_cases h₂:g₂ (columnLog p X₂ P)=0
    · simp only [threeGaussRowFactor,originalLabelColumn,multiplicativeCoreColumn,h₂,mul_zero,zero_mul]
    rw [hV₁ _ h₁,hV₂ _ h₂,one_mul,one_mul]
  · simp only [hNP,ite_false]

end SecondPassArithmetic

open scoped Classical SchwartzMap

namespace FirstPassCubeLabels
open Eisenstein SchwartzPlanePoisson

lemma conductor_zero_swap (parityBit a b:Bool) :
    conductorExponent parityBit a b=0 ↔ conductorExponent parityBit b a=0 := by
  cases parityBit <;> cases a <;> cases b <;> decide

lemma conductor_parity_swap (parityBit a b:Bool) :
    (conductorExponent parityBit a b).val%2=(conductorExponent parityBit b a).val%2 := by
  cases parityBit <;> cases a <;> cases b <;> decide

lemma dilationExponent_swap (parityBit a b:Bool) :
    dilationExponent parityBit a b=dilationExponent parityBit b a := by
  cases parityBit <;> cases a <;> cases b <;> rfl

lemma retained_swap (parityBit a b:Bool) : retained parityBit a b=retained parityBit b a := by
  cases parityBit <;> cases a <;> cases b <;> rfl

lemma b0Exponent_swap (m:ℕ) (a b:Bool) : b0Exponent m a b=b0Exponent m b a := by
  cases a <;> cases b <;> simp [b0Exponent,evenDouble]

variable {ι:Type*} (p:ι→O) (B:Finset ι) (v:ι→ℕ) (ε₁ ε₂:ι→Bool)

lemma cubeActiveSupport_swap : cubeActiveSupport B v ε₁ ε₂=cubeActiveSupport B v ε₂ ε₁ := by
  ext i
  simp only [cubeActiveSupport,Finset.mem_filter]
  constructor
  · rintro ⟨hi,he⟩
    exact ⟨hi,fun hx=>he ((conductor_zero_swap (parity (v i)) (ε₁ i) (ε₂ i)).mpr hx)⟩
  · rintro ⟨hi,he⟩
    exact ⟨hi,fun hx=>he ((conductor_zero_swap (parity (v i)) (ε₁ i) (ε₂ i)).mp hx)⟩

lemma cubeOddSupport_swap : cubeOddSupport B v ε₁ ε₂=cubeOddSupport B v ε₂ ε₁ := by
  ext i
  simp only [cubeOddSupport,Finset.mem_filter,conductor_parity_swap (parity (v i)) (ε₁ i) (ε₂ i)]

lemma dilationLabel_swap : dilationLabel p B v ε₁ ε₂=dilationLabel p B v ε₂ ε₁ := by
  unfold dilationLabel primeProduct
  apply Finset.prod_congr rfl
  intro i hi
  dsimp only
  rw [dilationExponent_swap (parity (v i)) (ε₁ i) (ε₂ i)]

lemma jLabel_swap : jLabel p B v ε₁ ε₂=jLabel p B v ε₂ ε₁ := by
  unfold jLabel primeProduct
  apply Finset.prod_congr rfl
  intro i hi
  dsimp only
  rw [retained_swap (parity (v i)) (ε₁ i) (ε₂ i)]

lemma b0Label_swap : b0Label p B v ε₁ ε₂=b0Label p B v ε₂ ε₁ := by
  unfold b0Label primeProduct
  apply Finset.prod_congr rfl
  intro i hi
  dsimp only
  rw [b0Exponent_swap (v i) (ε₁ i) (ε₂ i)]
end FirstPassCubeLabels

namespace SecondPassArithmetic

section
open Eisenstein SchwartzPlanePoisson FirstPassCubeLabels

theorem firstInputFamilyEnergy_swap {ι:Type*} [DecidableEq ι]
    (p:ι→O) [∀i,(Ideal.span {p i}).IsMaximal] (hg:∀i,lambda∉Ideal.span {p i})
    (F B:Finset ι) (v:ι→ℕ) (ε₁ ε₂:ι→Bool) (negative:Bool)
    (Ψ:O→*ℂ) (m:O) (H:Finset ι→ℂ) (V:ℝ→ℂ) (X:ℝ) (c d:O) (J:ℕ) (T:Finset O) :
    firstInputFamilyEnergy p hg F B v ε₁ ε₂ negative Ψ m H V X c d J T =
    firstInputFamilyEnergy p hg F B v ε₂ ε₁ negative Ψ m H V X c d J T := by
  simp only [firstInputFamilyEnergy,firstCoreOuter,firstCoreInputRow,
    cubeOddSupport_swap B v ε₁ ε₂,b0Label_swap p B v ε₁ ε₂,jLabel_swap p B v ε₁ ε₂]

namespace CubeCoordinates
variable {ι:Type*}
def swap (b:CubeCoordinates ι) : CubeCoordinates ι :=
  ⟨b.rightExponent,b.leftExponent,b.rightDivisor,b.leftDivisor⟩
@[simp] lemma swap_swap (b:CubeCoordinates ι) : b.swap.swap=b := by cases b;rfl
end CubeCoordinates
end
end SecondPassArithmetic

namespace SecondPassArithmetic
open Eisenstein SchwartzPlanePoisson FirstPassCubeLabels MeasureTheory
open scoped Classical SchwartzMap

variable {ι : Type*} [DecidableEq ι] (p : ι → O) (hp : ∀i,p i≠0)
  [∀i,(Ideal.span {p i}).IsMaximal] (hg : ∀i,lambda∉Ideal.span {p i})
omit [∀ (i : ι), (Ideal.span {p i}).IsMaximal] in
theorem globalCubeCoefficient_side (K ell B F : ℝ) (b : GlobalCubeBlock ι) (side : Bool) :
    globalCubeCoefficient p K ell B F side b=globalCubeCoefficient p K ell B F true b := by
  simp [globalCubeCoefficient,globalFirstCoefficient,globalBinFirstCoefficient,globalFirstIndex,
    globalScaleIndex,globalScaleVector,globalLogRep,GlobalFirstData.append,GlobalCubeBlock.withCommon,globalCubeActiveRoot]

omit [∀ (i : ι), (Ideal.span {p i}).IsMaximal] in
theorem globalFirstPooledRow_side (K ell B F : ℝ) (b : GlobalCubeBlock ι) (side : Bool) :
    globalFirstPooledRow p K ell B F side (b.withCommon ∅)=globalFirstPooledRow p K ell B F true (b.withCommon ∅) := by
  simp [globalFirstPooledRow,globalPooledRowScale,globalFirstIndex,globalScaleIndex,globalScaleVector,
    globalLogRep,GlobalFirstData.append,GlobalCubeBlock.withCommon,globalCubeJNorm]

include hp in
theorem globalCube_first_scalar_bound (K ell B F : ℝ) (hK : 0<K) (hell : 0<ell) (hB : 0<B) (hF : 0<F)
    (b : GlobalCubeBlock ι) :
    (ell*B^2*F)⁻¹*((K/primeProductNorm p b.firstDivisor)/
      ‖ringComplex (∏ i∈cubeActiveSupport b.cube.support
        (fun i => b.cube.leftExponent i+b.cube.rightExponent i) b.cube.leftBit b.cube.rightBit,p i)‖) ≤
      globalCubeCoefficient p K ell B F true b := by
  have h := globalBin_first_coefficient_bound p hp K ell B F hK.le hell hB hF true
    ((b.withCommon ∅).append ⟨∅,∅,∅,1⟩) (by exact one_ne_zero)
  change K/(primeProductNorm p b.firstDivisor*ell*B^2*F*
    ‖ringComplex (∏ i∈cubeActiveSupport b.cube.support
      (fun i => b.cube.leftExponent i+b.cube.rightExponent i) b.cube.leftBit b.cube.rightBit,p i)‖) ≤ _ at h
  change _ ≤ globalCubeCoefficient p K ell B F true b at h
  simpa only [div_eq_mul_inv, mul_inv_rev, mul_assoc, mul_left_comm, mul_comm] using h

def orientedCubeFirstBlock (pool : Finset ι) (b : GlobalCubeBlock ι)
    (s : Finset (Ideal O × O)) (a : Ideal O × O → ℂ)
    (Ψ₁ Ψ₂ : O →* ℂ) (m₁ m₂ : O) (g₁ g₂ W V₁ V₂ : 𝓢(ℝ,ℂ)) (K ell : ℝ) : ℂ :=
  let c := (∏ i∈b.common,p i)
  let d := (∏ i∈b.firstDivisor,p i)
  let X₁ := globalCubeColumnScale p ell true b
  let X₂ := globalCubeColumnScale p ell false b
  (primeProductNorm p b.firstDivisor : ℂ)⁻¹ * ∑ x∈s,a x*actualFirstKernel p hp hg (globalCubePool pool b) b.cube.support
    (fun i => b.cube.leftExponent i+b.cube.rightExponent i) b.cube.rightBit b.cube.leftBit
    (originalLabelColumn p hg b.cube.support b.cube.rightBit b.cube.leftBit true
      (multiplicativeCoreColumn p Ψ₁ m₁ (fun S => g₁ (columnLog p X₁ S))) c (cubicIdealGenerator x.1))
    (originalLabelColumn p hg b.cube.support b.cube.rightBit b.cube.leftBit false
      (multiplicativeCoreColumn p Ψ₂ m₂ (fun S => g₂ (columnLog p X₂ S))) c (cubicIdealGenerator x.1))
    W V₁ V₂ X₁ X₂ K d x.2

end SecondPassArithmetic

namespace SecondPassArithmetic
open Eisenstein SchwartzPlanePoisson FirstPassCubeLabels MeasureTheory
open scoped Classical SchwartzMap
theorem orientedCubeFirstBlock_input_transfer
    (W V₁ V₂ : 𝓢(ℝ,ℂ)) (M₁ M₂ : ℝ) (hM₁ : 0≤M₁) (hM₂ : 0≤M₂)
    (hV₁ : ∀ t,V₁ t≠0 → |t|≤M₁) (hV₂ : ∀ t,V₂ t≠0 → |t|≤M₂)
    (J : ℕ) (deltaLoss : ℝ) (hδ : 0<deltaLoss) :
    ∃ C : ℝ,0≤C ∧ ∀ {ι : Type*} [DecidableEq ι]
      (p : ι → O) (hp : ∀ i,p i ≠ 0) [∀ i,(Ideal.span {p i}).IsMaximal]
      (_hinj : Function.Injective (fun i => Ideal.span {p i}))
      (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
      (hg : ∀ i,lambda ∉ Ideal.span {p i})
      (_hc : ∀ i,ringChar (O ⧸ Ideal.span {p i}) ≠ 2) (_hpr : ∀ i,lambda^2 ∣ p i-1)
      (pool : Finset ι) (blocks : Finset (GlobalCubeBlock ι))
      (s : GlobalCubeBlock ι → Finset (Ideal O × O)) (a : GlobalCubeBlock ι → Ideal O × O → ℂ)
      (w : GlobalCubeBlock ι → ℝ) (T : GlobalCubeBlock ι → Finset O)
      (Ψ₁ Ψ₂ : O →* ℂ) (m₁ m₂ : O) (g₁ g₂ : 𝓢(ℝ,ℂ)) (K ell B F Ymax : ℝ),
      0<K → 0<ell → 0<B → 0<F →
      (∀ u,‖Ψ₁ u‖≤1) → (∀ u,‖Ψ₂ u‖≤1) →
      (∀ b∈blocks,0≤w b) → (∀ b∈blocks,∀ x∈s b,‖a b x‖≤w b) →
      (∀ b∈blocks,globalFirstPooledRow p K ell B F true (b.withCommon ∅)≤Ymax) →
      (∀ b∈blocks,∀ x∈s b,Squarefree x.1) → (∀ b∈blocks,∀ x∈s b,x.2≠0) →
      (∀ b∈blocks,∀ x∈s b,DescentWeightedCauchy.firstElementRowMap
        (dilationLabel p b.cube.support (fun i => b.cube.leftExponent i+b.cube.rightExponent i)
          b.cube.leftBit b.cube.rightBit) x∈T b) →
      (∀ b∈blocks,∀ z∈T b,z≠0) →
      (∀ b∈blocks,∀ z∈T b,(Ideal.absNorm (Ideal.span {z}) : ℝ)≤
        globalFirstPooledRow p K ell B F true (b.withCommon ∅)) →
      ‖(ell*B^2*F : ℂ)⁻¹*∑ b∈blocks,orientedCubeFirstBlock p hp hg pool b (s b) (a b)
        Ψ₁ Ψ₂ m₁ m₂ g₁ g₂ W V₁ V₂ K ell‖ ≤
      C*Ymax^deltaLoss*
        Real.sqrt (∑ b∈blocks,w b*globalCubeCoefficient p K ell B F true b*
          globalCubeInputFamilyEnergy p hg pool b Ψ₁ m₁ g₁ V₁ ell true J (T b)) *
        Real.sqrt (∑ b∈blocks,w b*globalCubeCoefficient p K ell B F false b*
          globalCubeInputFamilyEnergy p hg pool b Ψ₂ m₂ g₂ V₂ ell false J (T b)) := by
  obtain ⟨C,hC,hfirst⟩ := first_passage_to_input_family W V₁ V₂ M₁ M₂ hM₁ hM₂ hV₁ hV₂ J deltaLoss hδ
  refine ⟨C,hC,?_⟩
  intro ι _ p hp _ hinj hcop hg hc hpr pool blocks s a w T Ψ₁ Ψ₂ m₁ m₂ g₁ g₂ K ell B F Ymax hK hell hB hF hΨ₁ hΨ₂ hw ha hYmax hsf hs0 hmap hT0 hT
  by_cases hempty : blocks=∅
  · subst blocks
    simp only [Finset.sum_empty,mul_zero,norm_zero,Real.sqrt_zero,le_refl]
  have hne : blocks.Nonempty := Finset.nonempty_iff_ne_empty.mpr hempty
  let E₁ := fun b => globalCubeInputFamilyEnergy p hg pool b Ψ₁ m₁ g₁ V₁ ell true J (T b)
  let E₂ := fun b => globalCubeInputFamilyEnergy p hg pool b Ψ₂ m₂ g₂ V₂ ell false J (T b)
  let v := fun b => w b*globalCubeCoefficient p K ell B F true b
  have hv (b) (hb : b∈blocks) : 0≤v b := mul_nonneg (hw b hb)
    (globalBinFirstCoefficient_nonneg K ell B F hK.le hell hB hF _)
  have hE₁ (b) : 0≤E₁ b := firstInputFamilyEnergy_nonneg p hg _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
  have hE₂ (b) : 0≤E₂ b := firstInputFamilyEnergy_nonneg p hg _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
  have hden : 0<ell*B^2*F := by positivity
  have hYmax0 : 0≤Ymax := by
    obtain ⟨b,hb⟩ := hne
    exact (globalPooledRowScale_pos K ell B F hK hell hB hF _).le.trans (hYmax b hb)
  have hpref : 0≤C*Ymax^deltaLoss := mul_nonneg hC (Real.rpow_nonneg hYmax0 deltaLoss)
  have hpoint (b) (hb : b∈blocks) : (ell*B^2*F)⁻¹*
      ‖orientedCubeFirstBlock p hp hg pool b (s b) (a b) Ψ₁ Ψ₂ m₁ m₂ g₁ g₂ W V₁ V₂ K ell‖ ≤
      (C*Ymax^deltaLoss)*v b*(Real.sqrt (E₁ b)*Real.sqrt (E₂ b)) := by
    have hFB : Disjoint (globalCubePool pool b) b.cube.support := by
      apply Finset.disjoint_left.mpr
      intro i hi hiB
      exact (Finset.mem_sdiff.mp hi).2 (Finset.mem_union_left _ hiB)
    have hX₁ := globalCubeColumnScale_pos p hp ell hell true b
    have hX₂ := globalCubeColumnScale_pos p hp ell hell false b
    have hD := primeProductNorm_pos p hp b.firstDivisor
    have hY := globalPooledRowScale_pos K ell B F hK hell hB hF (globalFirstIndex p true (b.withCommon ∅))
    have hswapD := FirstPassCubeLabels.dilationLabel_swap p b.cube.support
      (fun i=>b.cube.leftExponent i+b.cube.rightExponent i) b.cube.rightBit b.cube.leftBit
    have hh := hfirst p hp hinj hcop hg hc hpr (globalCubePool pool b) b.cube.support hFB
      (fun i => b.cube.leftExponent i+b.cube.rightExponent i) b.cube.rightBit b.cube.leftBit b.cube.support_pos
      Ψ₁ Ψ₂ m₁ m₂ (fun A => g₁ (columnLog p (globalCubeColumnScale p ell true b) A))
      (fun A => g₂ (columnLog p (globalCubeColumnScale p ell false b) A))
      (fun A hA => hΨ₁ _) (fun A hA => hΨ₂ _)
      _ _ hX₁ hX₂ K hK ((∏ i∈b.common,p i))
      ((∏ i∈b.firstDivisor,p i)) (Finset.prod_ne_zero_iff.mpr (fun i _ => hp i))
      (s b) (T b) (a b) (w b) (globalFirstPooledRow p K ell B F true (b.withCommon ∅))
      (hw b hb) hY.le (hs0 b hb) (by simpa only [hswapD] using hmap b hb) (hT0 b hb) (hT b hb) (ha b hb)
    rw [firstInputFamilyEnergy_swap p hg (globalCubePool pool b) b.cube.support
        (fun i=>b.cube.leftExponent i+b.cube.rightExponent i) b.cube.rightBit b.cube.leftBit true,
      firstInputFamilyEnergy_swap p hg (globalCubePool pool b) b.cube.support
        (fun i=>b.cube.leftExponent i+b.cube.rightExponent i) b.cube.rightBit b.cube.leftBit false,
      FirstPassCubeLabels.cubeActiveSupport_swap b.cube.support
        (fun i=>b.cube.leftExponent i+b.cube.rightExponent i) b.cube.rightBit b.cube.leftBit] at hh
    have hscl := globalCube_first_scalar_bound p hp K ell B F hK hell hB hF b
    have hpow := Real.rpow_le_rpow hY.le (hYmax b hb) hδ.le
    have hmul := mul_le_mul_of_nonneg_left hh
      (show 0≤(ell*B^2*F)⁻¹*(primeProductNorm p b.firstDivisor)⁻¹ by positivity)
    simp only [orientedCubeFirstBlock,norm_mul,norm_inv,Complex.norm_real,
      Real.norm_of_nonneg hD.le,←mul_assoc]
    apply hmul.trans
    calc
      _ = ((ell*B^2*F)⁻¹*((K/primeProductNorm p b.firstDivisor)/
          ‖ringComplex (∏ i∈cubeActiveSupport b.cube.support
            (fun i => b.cube.leftExponent i+b.cube.rightExponent i) b.cube.leftBit b.cube.rightBit,p i)‖))*
          (w b*C*(globalFirstPooledRow p K ell B F true (b.withCommon ∅))^deltaLoss)*
          (Real.sqrt (E₁ b)*Real.sqrt (E₂ b)) := by dsimp [E₁,E₂,globalCubeInputFamilyEnergy];ring
      _ ≤ globalCubeCoefficient p K ell B F true b*(w b*C*Ymax^deltaLoss)*
          (Real.sqrt (E₁ b)*Real.sqrt (E₂ b)) := by
        apply mul_le_mul_of_nonneg_right _ (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
        apply mul_le_mul hscl
          (mul_le_mul_of_nonneg_left hpow (mul_nonneg (hw b hb) hC))
          (mul_nonneg (mul_nonneg (hw b hb) hC) (Real.rpow_nonneg hY.le _))
          (globalBinFirstCoefficient_nonneg K ell B F hK.le hell hB hF _)
      _ = _ := by dsimp [v];ring
  rw [norm_mul, norm_inv]
  have hn : ‖(ell*B^2*F : ℂ)‖=ell*B^2*F := by
    norm_cast
    exact abs_of_pos hden
  rw [hn]
  calc
    _ ≤ (ell*B^2*F)⁻¹*∑ b∈blocks,‖orientedCubeFirstBlock p hp hg pool b (s b) (a b) Ψ₁ Ψ₂ m₁ m₂ g₁ g₂ W V₁ V₂ K ell‖ :=
      mul_le_mul_of_nonneg_left (norm_sum_le _ _) (inv_nonneg.mpr hden.le)
    _ ≤ ∑ b∈blocks,(C*Ymax^deltaLoss)*v b*(Real.sqrt (E₁ b)*Real.sqrt (E₂ b)) := by
      rw [Finset.mul_sum]
      exact Finset.sum_le_sum hpoint
    _ = (C*Ymax^deltaLoss)*∑ b∈blocks,Real.sqrt (v b*E₁ b)*Real.sqrt (v b*E₂ b) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro b hb
      rw [Real.sqrt_mul (hv b hb),Real.sqrt_mul (hv b hb)]
      have hs := Real.sq_sqrt (hv b hb)
      calc
        _ = (C*Ymax^deltaLoss)*(Real.sqrt (v b))^2*(Real.sqrt (E₁ b)*Real.sqrt (E₂ b)) := by rw [hs]
        _ = _ := by ring
    _ ≤ (C*Ymax^deltaLoss)*(Real.sqrt (∑ b∈blocks,v b*E₁ b)*Real.sqrt (∑ b∈blocks,v b*E₂ b)) :=
      mul_le_mul_of_nonneg_left (by
        have hcauchy := Real.sum_sqrt_mul_sqrt_le blocks.attach
          (fun b => mul_nonneg (hv b.val b.property) (hE₁ b.val))
          (fun b => mul_nonneg (hv b.val b.property) (hE₂ b.val))
        simpa only [Finset.sum_attach (f := fun b => Real.sqrt (v b*E₁ b)*Real.sqrt (v b*E₂ b)),
          Finset.sum_attach (f := fun b => v b*E₁ b),Finset.sum_attach (f := fun b => v b*E₂ b)] using hcauchy) hpref
    _ = _ := by simp only [v,E₁,E₂,globalCubeCoefficient_side,mul_assoc]

end SecondPassArithmetic

namespace SecondPassArithmetic
open Eisenstein SchwartzPlanePoisson FirstPassCubeLabels MeasureTheory
open scoped Classical SchwartzMap ContDiff

/-- The integrated first-pass bound, including diagonal, descendants and tail. -/
def globalFirstQuantitativeBudget {ι : Type*} [DecidableEq ι]
    (p : ι → O) [∀i,(Ideal.span {p i}).IsMaximal] (hg : ∀i,lambda∉Ideal.span {p i})
    (pool : Finset ι) (blocks : Finset (GlobalCubeBlock ι)) (Ψ : O →* ℂ) (m : O)
    (windows : Fin 7 → ℝ → ℂ) (C Cd Ct Γ ε K ell B F M H U : ℝ)
    (A J N : ℕ) (side : Bool) : ℝ :=
  let family := (globalFirstFamilySet pool blocks).filter
    (fun b => primeProductNorm p b.common ≤ U ∧ primeProductNorm p b.firstCommon ≤ U)
  let source := globalFirstSupportedPool p pool family
    (fun b G E => (globalFirstConcreteCutoff p K ell B F M H side b G E).erase 0) ell M side
  let I := globalLogBox (globalNormCaps ell B (globalRowScaleFloor K ell B F M) M H)
  (2 * (Fintype.card (QuadraticRayRing × QuadraticRayRing) : ℝ)) *
    (∫ t, firstLogDensity 0 t) *
    (Cd * Γ * (ell*B^3*F) * (B*U)^ε +
      globalChildBudget p hg pool source Ψ m windows (Γ*C) ε K ell B F I A J side +
      Ct * Γ * (ell*B^3*F) * (B*U)^ε * (U * globalFirstTailFactor K ell B F U H N))

theorem orientedTwoPassage_quantitative
    (W g₁ g₂ V₁ V₂ : 𝓢(ℝ,ℂ)) (M₁ M₂ N₁ N₂ : ℝ)
    (hM₁ : 0≤M₁) (hM₂ : 0≤M₂) (hN₁ : 0≤N₁) (hN₂ : 0≤N₂)
    (hg₁ : ∀ t,g₁ t≠0 → |t|≤M₁) (hg₂ : ∀ t,g₂ t≠0 → |t|≤M₂)
    (hV₁ : ∀ t,V₁ t≠0 → |t|≤N₁) (hV₂ : ∀ t,V₂ t≠0 → |t|≤N₂)
    (ε deltaLoss : ℝ) (hε : 0<ε) (hδ : 0<deltaLoss) (A J N : ℕ) :
    ∃ (windows₁ windows₂ : Fin 7 → ℝ → ℂ) (Cfirst C₁ Cd₁ Ct₁ C₂ Cd₂ Ct₂ : ℝ),
      0≤Cfirst ∧ 0≤C₁ ∧ 0<Cd₁ ∧ 0<Ct₁ ∧ 0≤C₂ ∧ 0<Cd₂ ∧ 0<Ct₂ ∧
      (∀ i,HasCompactSupport (windows₁ i)) ∧ (∀ i,ContDiff ℝ ∞ (windows₁ i)) ∧
      (∀ i t,windows₁ i t≠0 → |t|≤M₁+6+1) ∧
      (∀ i,HasCompactSupport (windows₂ i)) ∧ (∀ i,ContDiff ℝ ∞ (windows₂ i)) ∧
      (∀ i t,windows₂ i t≠0 → |t|≤M₂+6+1) ∧
      ∀ {ι : Type*} [DecidableEq ι]
      (p : ι → O) (hp : ∀ i,p i ≠ 0) [∀ i,(Ideal.span {p i}).IsMaximal]
      (_hinj : Function.Injective (fun i => Ideal.span {p i}))
      (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
      (hg : ∀ i,lambda ∉ Ideal.span {p i})
      (_hc : ∀ i,ringChar (O ⧸ Ideal.span {p i}) ≠ 2) (_hpr : ∀ i,lambda^2 ∣ p i-1)
      (pool : Finset ι) (blocks : Finset (GlobalCubeBlock ι))
      (s : GlobalCubeBlock ι → Finset (Ideal O × O)) (a : GlobalCubeBlock ι → Ideal O × O → ℂ)
      (w : GlobalCubeBlock ι → ℝ)
      (Ψ₁ Ψ₂ : O →* ℂ) (m₁ m₂ : O) (Γ K ell B F H U : ℝ),
      0≤Γ → 0<K → 0<ell → 1≤B → 0<F → 0≤H → 1≤U → ell*Real.exp M₁≤U → ell*Real.exp M₂≤U →
      (∀ u,‖Ψ₁ u‖≤1) → (∀ u,‖Ψ₂ u‖≤1) →
      (∀ b∈blocks,0≤w b ∧ w b≤Γ) → (∀ b∈blocks,∀ x∈s b,‖a b x‖≤w b) →
      (∀ b∈blocks,GlobalCubeAdmissible b) →
      (∀ b∈blocks,‖ringComplex (primeProduct p b.cube.support b.cube.leftExponent)‖^2≤B) →
      (∀ b∈blocks,‖ringComplex (primeProduct p b.cube.support b.cube.rightExponent)‖^2≤B) →
      (∀ b∈blocks,∀ x∈s b,Squarefree x.1) → (∀ b∈blocks,∀ x∈s b,x.2≠0) →
      (∀ b∈blocks,∀ x∈s b,(Ideal.absNorm x.1 : ℝ)≤F) →
      (∀ b∈blocks,∀ x∈s b,‖ringComplex x.2‖^2≤globalFirstFrequencyScale p K ell b) →
      ‖(ell*B^2*F : ℂ)⁻¹*∑ b∈blocks,orientedCubeFirstBlock p hp hg pool b (s b) (a b)
        Ψ₁ Ψ₂ m₁ m₂ g₁ g₂ W V₁ V₂ K ell‖ ≤
      Cfirst*(globalFirstRowCap K ell B F)^deltaLoss*
        Real.sqrt (globalFirstQuantitativeBudget p hg pool blocks Ψ₁ m₁ windows₁ C₁ Cd₁ Ct₁ Γ ε K ell B F M₁ H U A J N true) *
        Real.sqrt (globalFirstQuantitativeBudget p hg pool blocks Ψ₂ m₂ windows₂ C₂ Cd₂ Ct₂ Γ ε K ell B F M₂ H U A J N false) := by
  obtain ⟨Cfirst,hCfirst,hfirst⟩ := orientedCubeFirstBlock_input_transfer W V₁ V₂ N₁ N₂ hN₁ hN₂ hV₁ hV₂ (2*(J+2)) deltaLoss hδ
  obtain ⟨windows₁,C₁,Cd₁,Ct₁,hC₁,hCd₁,hCt₁,hwc₁,hws₁,hwb₁,hleft⟩ :=
    globalCubeInputFamilyEnergy_quantitative_transfer ε hε g₁ V₁ M₁ hM₁ hg₁ true A J N
  obtain ⟨windows₂,C₂,Cd₂,Ct₂,hC₂,hCd₂,hCt₂,hwc₂,hws₂,hwb₂,hright⟩ :=
    globalCubeInputFamilyEnergy_quantitative_transfer ε hε g₂ V₂ M₂ hM₂ hg₂ false A J N
  refine ⟨windows₁,windows₂,Cfirst,C₁,Cd₁,Ct₁,C₂,Cd₂,Ct₂,hCfirst,hC₁,hCd₁,hCt₁,hC₂,hCd₂,hCt₂,
    hwc₁,hws₁,hwb₁,hwc₂,hws₂,hwb₂,?_⟩
  intro ι _ p hp _ hinj hcop hg hc hpr pool blocks s a w Ψ₁ Ψ₂ m₁ m₂ Γ K ell B F H U
    hΓ hK hell hB hF hH hU hellU1 hellU2 hΨ₁ hΨ₂ hw ha hadm hb₁ hb₂ hsf hs0 hf hh
  have hB0 : 0<B := by linarith
  let T := fun b => globalCubeFirstTargets p b (s b)
  have hT0 (b : GlobalCubeBlock ι) (hb : b∈blocks) (z : O) (hz : z∈T b) : z≠0 :=
    globalCubeFirstTargets_ne_zero p hp b (s b) (fun x hx => Squarefree.ne_zero (hsf b hb x hx)) (hs0 b hb) z hz
  have hT (b : GlobalCubeBlock ι) (hb : b∈blocks) (z : O) (hz : z∈T b) :
      (Ideal.absNorm (Ideal.span {z}) : ℝ)≤globalFirstPooledRow p K ell B F true (b.withCommon ∅) :=
    globalCubeFirstTargets_norm_bound p hp b (s b) K ell B F hK hell hB0 hF
      (hb₁ b hb) (hb₂ b hb) (hf b hb) (hh b hb) z hz
  have hTc (b : GlobalCubeBlock ι) (hb : b∈blocks) (z : O) (hz : z∈T b) :
      (Ideal.absNorm (Ideal.span {z}) : ℝ)≤globalFirstPooledRow p K ell B F false (b.withCommon ∅) := by
    rw [globalFirstPooledRow_side]
    exact hT b hb z hz
  have hblock := hfirst p hp hinj hcop hg hc hpr pool blocks s a w T Ψ₁ Ψ₂ m₁ m₂ g₁ g₂ K ell B F
    (globalFirstRowCap K ell B F) hK hell hB0 hF hΨ₁ hΨ₂ (fun b hb => (hw b hb).1) ha
    (fun b hb => globalFirstPooledRow_le_cap p hp K ell B F hK hell hB0 hF b (hadm b hb) (hb₁ b hb) (hb₂ b hb))
    hsf hs0 (fun b _ x hx => globalCubeFirstTargets_mem p b (s b) x hx) hT0 hT
  have hl := hleft p hp hg hinj hc hpr pool blocks w Γ K ell B F H U Ψ₁ m₁ T
    hΓ hw hK hell hB hF hH hU hellU1 hadm hΨ₁ hb₁ hb₂ hT
  have hr := hright p hp hg hinj hc hpr pool blocks w Γ K ell B F H U Ψ₂ m₂ T
    hΓ hw hK hell hB hF hH hU hellU2 hadm hΨ₂ hb₁ hb₂ hTc
  have hprefix : 0≤Cfirst*(globalFirstRowCap K ell B F)^deltaLoss :=
    mul_nonneg hCfirst (Real.rpow_nonneg (globalFirstRowCap_pos K ell B F hK hell hB0 hF).le _)
  exact hblock.trans (mul_le_mul (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hl) hprefix)
    (Real.sqrt_le_sqrt hr) (Real.sqrt_nonneg _) (mul_nonneg hprefix (Real.sqrt_nonneg _)))

end SecondPassArithmetic

namespace SecondPassArithmetic
open Eisenstein SchwartzPlanePoisson FirstPassCubeLabels
open scoped Classical SchwartzMap
variable {ι : Type*} [DecidableEq ι] (p : ι → O) (hp : ∀i,p i≠0)
  [∀i,(Ideal.span {p i}).IsMaximal] (hg : ∀i,lambda∉Ideal.span {p i})
def sourceGlobalBlock (b:CubeCoordinates ι) (C D:Finset ι) : GlobalCubeBlock ι :=
  ⟨b.swap,C,D⟩

lemma cube_swap_support (b:CubeCoordinates ι) : b.swap.support=b.support := by
  simp only [CubeCoordinates.swap,CubeCoordinates.support,Finset.union_comm]

omit [DecidableEq ι] in
lemma cube_swap_sum (b:CubeCoordinates ι) :
    (fun i=>b.swap.leftExponent i+b.swap.rightExponent i)=
      (fun i=>b.leftExponent i+b.rightExponent i) := by
  funext i
  exact Nat.add_comm _ _

lemma orientedCubeFirstBlock_single_source
    (pool:Finset ι) (b:CubeCoordinates ι) (C D:Finset ι) (I:Ideal O) (h:O)
    (Ψ₁ Ψ₂:O→*ℂ) (m₁ m₂:O) (g₁ g₂ W V₁ V₂:𝓢(ℝ,ℂ)) (K ell:ℝ) :
    orientedCubeFirstBlock p hp hg pool (sourceGlobalBlock b C D) {(I,h)} (fun _=>1)
      Ψ₁ Ψ₂ m₁ m₂ g₁ g₂ W V₁ V₂ K ell =
    (primeProductNorm p D:ℂ)⁻¹ *
      actualFirstKernel p hp hg (pool\(b.support∪C)) b.support
        (fun i=>b.leftExponent i+b.rightExponent i) b.leftBit b.rightBit
        (originalLabelColumn p hg b.support b.leftBit b.rightBit true
          (multiplicativeCoreColumn p Ψ₁ m₁ (fun S=>g₁ (columnLog p
            (ell/(primeProductNorm p b.rightDivisor*primeProductNorm p C)) S)))
          ((∏i∈C,p i)) (cubicIdealGenerator I))
        (originalLabelColumn p hg b.support b.leftBit b.rightBit false
          (multiplicativeCoreColumn p Ψ₂ m₂ (fun S=>g₂ (columnLog p
            (ell/(primeProductNorm p b.leftDivisor*primeProductNorm p C)) S)))
          ((∏i∈C,p i)) (cubicIdealGenerator I))
        W V₁ V₂ (ell/(primeProductNorm p b.rightDivisor*primeProductNorm p C))
          (ell/(primeProductNorm p b.leftDivisor*primeProductNorm p C)) K
          ((∏i∈D,p i)) h := by
  have hl : b.swap.leftBit=b.rightBit := rfl
  have hr : b.swap.rightBit=b.leftBit := rfl
  have hst : b.swap.sideDivisor true=b.rightDivisor := rfl
  have hsf : b.swap.sideDivisor false=b.leftDivisor := rfl
  simp only [orientedCubeFirstBlock,sourceGlobalBlock,globalCubePool,globalCubeColumnScale,
    globalFirstBlockColumnScale,GlobalCubeBlock.withCommon,cube_swap_support,cube_swap_sum,
    hl,hr,hst,hsf,Finset.sum_singleton,one_mul]

lemma canonical_log_kernel
    (pool:Finset ι) (b:CubeCoordinates ι) (hb:b.Admissible) (C:Finset ι)
    (hCB:Disjoint C b.support) (Ψ₁ Ψ₂:O→*ℂ) (m₁ m₂ f d h:O)
    (g₁ g₂ W:𝓢(ℝ,ℂ)) (K ell:ℝ) (hell:0<ell) :
    actualFirstKernel p hp hg (pool\(b.support∪C)) b.support
      (fun i=>b.leftExponent i+b.rightExponent i) b.leftBit b.rightBit
      (canonicalCubeResidual p hg b C true Ψ₁ m₁ f (fun U=>g₁ (columnLog p ell U)))
      (canonicalCubeResidual p hg b C false Ψ₂ m₂ f (fun U=>g₂ (columnLog p ell U)))
      W (fun _=>1) (fun _=>1) 1 1 K d h =
    actualFirstKernel p hp hg (pool\(b.support∪C)) b.support
      (fun i=>b.leftExponent i+b.rightExponent i) b.leftBit b.rightBit
      (originalLabelColumn p hg b.support b.leftBit b.rightBit true
        (multiplicativeCoreColumn p Ψ₁ m₁ (fun S=>g₁ (columnLog p
          (ell/(primeProductNorm p b.rightDivisor*primeProductNorm p C)) S))) (∏i∈C,p i) f)
      (originalLabelColumn p hg b.support b.leftBit b.rightBit false
        (multiplicativeCoreColumn p Ψ₂ m₂ (fun S=>g₂ (columnLog p
          (ell/(primeProductNorm p b.leftDivisor*primeProductNorm p C)) S))) (∏i∈C,p i) f)
      W (fun _=>1) (fun _=>1) (ell/(primeProductNorm p b.rightDivisor*primeProductNorm p C))
        (ell/(primeProductNorm p b.leftDivisor*primeProductNorm p C)) K d h := by
  unfold actualFirstKernel
  apply Finset.sum_congr rfl
  intro N hN
  apply Finset.sum_congr rfl
  intro P hP
  have hdis (S:Finset ι) (hS:S∈(pool\(b.support∪C)).powerset) :
      Disjoint S C ∧ Disjoint S b.support := by
    constructor <;> apply Finset.disjoint_left.mpr
    · intro i hi hx
      exact (Finset.mem_sdiff.mp ((Finset.mem_powerset.mp hS) hi)).2 (Finset.mem_union_right _ hx)
    · intro i hi hx
      exact (Finset.mem_sdiff.mp ((Finset.mem_powerset.mp hS) hi)).2 (Finset.mem_union_left _ hx)
  have h₁:=canonicalCubeResidual_log p hp hg b hb C N hCB (hdis N hN).1 (hdis N hN).2 true Ψ₁ m₁ f g₁ ell hell
  have h₂:=canonicalCubeResidual_log p hp hg b hb C P hCB (hdis P hP).1 (hdis P hP).2 false Ψ₂ m₂ f g₂ ell hell
  simp only [CubeCoordinates.sideDivisor,Bool.not_true,Bool.not_false,Bool.false_eq_true,ite_false,ite_true] at h₁ h₂
  simp only [threeGaussRowFactor,h₁,h₂]

/-- Each source mode is an oriented first-pass block with its Möbius coefficient. -/
theorem canonicalSource_mode_attachment
    (pool:Finset ι) (b:CubeCoordinates ι) (hb:b.Admissible) (C D:Finset ι)
    (hCB:Disjoint C b.support) (I:Ideal O) (h:O)
    (Ψ₁ Ψ₂:O→*ℂ) (m₁ m₂:O) (g₁ g₂ W V₁ V₂:𝓢(ℝ,ℂ)) (K ell:ℝ) (hell:0<ell)
    (hV₁:∀t,g₁ t≠0→V₁ t=1) (hV₂:∀t,g₂ t≠0→V₂ t=1) :
    (supportMobius D/(primeProductNorm p D:ℂ))*
      actualFirstKernel p hp hg (pool\(b.support∪C)) b.support
        (fun i=>b.leftExponent i+b.rightExponent i) b.leftBit b.rightBit
        (canonicalCubeResidual p hg b C true Ψ₁ m₁ (cubicIdealGenerator I) (fun U=>g₁ (columnLog p ell U)))
        (canonicalCubeResidual p hg b C false Ψ₂ m₂ (cubicIdealGenerator I) (fun U=>g₂ (columnLog p ell U)))
        W (fun _=>1) (fun _=>1) 1 1 K (∏i∈D,p i) h =
    supportMobius D*orientedCubeFirstBlock p hp hg pool (sourceGlobalBlock b C D)
      {(I,h)} (fun _=>1) Ψ₁ Ψ₂ m₁ m₂ g₁ g₂ W V₁ V₂ K ell := by
  rw [canonical_log_kernel p hp hg pool b hb C hCB Ψ₁ Ψ₂ m₁ m₂ (cubicIdealGenerator I) _ h g₁ g₂ W K ell hell]
  rw [actualFirstKernel_insert_windows p hp hg _ _ _ _ _ Ψ₁ Ψ₂ m₁ m₂ _ _
    g₁ g₂ W V₁ V₂ _ _ K _ h hV₁ hV₂]
  rw [orientedCubeFirstBlock_single_source]
  ring
lemma orientedCubeFirstBlock_eq_sum_single (pool:Finset ι) (b:GlobalCubeBlock ι)
    (s:Finset (Ideal O×O)) (a:Ideal O×O→ℂ)
    (Ψ₁ Ψ₂:O→*ℂ) (m₁ m₂:O) (g₁ g₂ W V₁ V₂:𝓢(ℝ,ℂ)) (K ell:ℝ) :
    orientedCubeFirstBlock p hp hg pool b s a Ψ₁ Ψ₂ m₁ m₂ g₁ g₂ W V₁ V₂ K ell=
      ∑x∈s,a x*orientedCubeFirstBlock p hp hg pool b {x} (fun _=>1)
        Ψ₁ Ψ₂ m₁ m₂ g₁ g₂ W V₁ V₂ K ell := by
  unfold orientedCubeFirstBlock
  simp only [Finset.sum_singleton,one_mul]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x hx
  ring

def rawCanonicalBlock (pool:Finset ι) (b:GlobalCubeBlock ι)
    (s:Finset (Ideal O×O)) (a:Ideal O×O→ℂ)
    (Ψ₁ Ψ₂:O→*ℂ) (m₁ m₂:O) (g₁ g₂ W:𝓢(ℝ,ℂ)) (K ell:ℝ) : ℂ :=
  let q:=b.cube.swap
  ∑x∈s,a x*(supportMobius b.firstDivisor/
    (primeProductNorm p b.firstDivisor:ℂ))*
    actualFirstKernel p hp hg (pool\(q.support∪b.common)) q.support
      (fun i=>q.leftExponent i+q.rightExponent i) q.leftBit q.rightBit
      (canonicalCubeResidual p hg q b.common true Ψ₁ m₁ (cubicIdealGenerator x.1)
        (fun U=>g₁ (columnLog p ell U)))
      (canonicalCubeResidual p hg q b.common false Ψ₂ m₂ (cubicIdealGenerator x.1)
        (fun U=>g₂ (columnLog p ell U)))
      W (fun _=>1) (fun _=>1) 1 1 K
      ((∏i∈b.firstDivisor,p i)) x.2

/-- The raw source is the sum of its oriented Möbius-weighted blocks. -/
theorem rawCanonicalBlock_eq_oriented
    (pool:Finset ι) (b:GlobalCubeBlock ι) (hb:GlobalCubeAdmissible b)
    (s:Finset (Ideal O×O)) (a:Ideal O×O→ℂ)
    (Ψ₁ Ψ₂:O→*ℂ) (m₁ m₂:O) (g₁ g₂ W V₁ V₂:𝓢(ℝ,ℂ)) (K ell:ℝ) (hell:0<ell)
    (hV₁:∀t,g₁ t≠0→V₁ t=1) (hV₂:∀t,g₂ t≠0→V₂ t=1) :
    rawCanonicalBlock p hp hg pool b s a Ψ₁ Ψ₂ m₁ m₂ g₁ g₂ W K ell =
      orientedCubeFirstBlock p hp hg pool b s (fun x=>supportMobius b.firstDivisor*a x)
        Ψ₁ Ψ₂ m₁ m₂ g₁ g₂ W V₁ V₂ K ell := by
  have hq : b.cube.swap.Admissible := by
    constructor
    · change b.cube.rightDivisor⊆b.cube.swap.support
      rw [cube_swap_support]
      exact hb.1.2
    · change b.cube.leftDivisor⊆b.cube.swap.support
      rw [cube_swap_support]
      exact hb.1.1
  have hc : Disjoint b.common b.cube.swap.support := by
    rw [cube_swap_support]
    exact hb.2.1
  have hback : sourceGlobalBlock b.cube.swap b.common b.firstDivisor=b := by
    cases b
    simp only [sourceGlobalBlock,CubeCoordinates.swap_swap]
  rw [orientedCubeFirstBlock_eq_sum_single]
  unfold rawCanonicalBlock
  dsimp only
  apply Finset.sum_congr rfl
  intro x hx
  have hm := canonicalSource_mode_attachment p hp hg pool b.cube.swap hq b.common b.firstDivisor hc
    x.1 x.2 Ψ₁ Ψ₂ m₁ m₂ g₁ g₂ W V₁ V₂ K ell hell hV₁ hV₂
  rw [hback] at hm
  calc
    _ = a x*((supportMobius b.firstDivisor/(primeProductNorm p b.firstDivisor:ℂ))*
        actualFirstKernel p hp hg (pool\(b.cube.swap.support∪b.common)) b.cube.swap.support
          (fun i=>b.cube.swap.leftExponent i+b.cube.swap.rightExponent i) b.cube.swap.leftBit b.cube.swap.rightBit
          (canonicalCubeResidual p hg b.cube.swap b.common true Ψ₁ m₁ (cubicIdealGenerator x.1)
            (fun U=>g₁ (columnLog p ell U)))
          (canonicalCubeResidual p hg b.cube.swap b.common false Ψ₂ m₂ (cubicIdealGenerator x.1)
            (fun U=>g₂ (columnLog p ell U)))
          W (fun _=>1) (fun _=>1) 1 1 K (∏i∈b.firstDivisor,p i) x.2) := by ring
    _ = _ := by rw [hm]; ring

end SecondPassArithmetic

namespace FirstPassCubeLabels
open Eisenstein SchwartzPlanePoisson SecondPassArithmetic
open scoped Classical SchwartzMap

variable {ι : Type*} [DecidableEq ι] (p : ι → O) (hp : ∀i,p i≠0)
  [∀i,(Ideal.span {p i}).IsMaximal] (hg : ∀i,lambda∉Ideal.span {p i})
theorem actualFirstKernel_truncate
    (F B:Finset ι) (v:ι→ℕ) (ε₁ ε₂:ι→Bool)
    (C₁ C₂:Finset ι→ℂ) (W:𝓢(ℝ,ℂ)) (V₁ V₂:ℝ→ℂ)
    (X₁ X₂ K:ℝ) (hK:0<K) (d:O) (hd:d≠0) (T:Finset O) :
    (∑'h:O,actualFirstKernel p hp hg F B v ε₁ ε₂ C₁ C₂ W V₁ V₂ X₁ X₂ K d h)=
      (∑h∈T,actualFirstKernel p hp hg F B v ε₁ ε₂ C₁ C₂ W V₁ V₂ X₁ X₂ K d h)+
      ∑'h:{h:O//h∉T},actualFirstKernel p hp hg F B v ε₁ ε₂ C₁ C₂ W V₁ V₂ X₁ X₂ K d h.val := by
  exact (actualFirstKernel_summable p hp hg F B v ε₁ ε₂ C₁ C₂ W V₁ V₂ X₁ X₂ K hK d hd).sum_add_tsum_subtype_compl T |>.symm

end FirstPassCubeLabels

end GaloisForLFunctions.MetaplecticMobiusDescent.CubicEisenstein
