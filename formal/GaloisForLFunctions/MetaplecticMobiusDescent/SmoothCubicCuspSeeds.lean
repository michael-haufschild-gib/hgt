/-
Smooth cubic cusp seeds adapted from OpenAI's formalization, Apache-2.0.
See LICENSE and NOTICE for source attribution.
-/
import GaloisForLFunctions.MetaplecticMobiusDescent.CharacterEquivariantCubicCuspProfiles
import GaloisForLFunctions.MetaplecticMobiusDescent.CubicIncomingHeightProfiles
import GaloisForLFunctions.MetaplecticMobiusDescent.HyperbolicHeightProfiles

/-!
# Smooth character-equivariant incoming seeds

Bounded integral rows make high cusp heights locally finite. Smooth height
profiles therefore give smooth cubic-equivariant sums. The explicit height
Laplacian proves their defect equation, and the actual cubic character
kernel lets both seed and defect descend to the quotient.
-/

noncomputable section
open Filter MeasureTheory
open scoped BigOperators Classical Topology ContDiff MatrixGroups
namespace GaloisForLFunctions.MetaplecticMobiusDescent.CubicEisenstein
open Eisenstein CubicKubota

lemma locally_finite_high_rows (p : SpatialCoordinates) (hp : 0<p 2) :
    ∃U : Set SpatialCoordinates, IsOpen U ∧ p∈U ∧ ∃S : Finset CuspCosets,
      ∀q∈U, 0<q 2 ∧ ∀r∉S,rowHeight (embeddedRow r) q<1 := by
  let w := upperPoint (spatialHorizontal p) (p 2) hp
  obtain ⟨U,hU,hw,T,hT⟩ := principal_high_locally_finite w
  have ht : p∈hyperbolicSpatialChart.target := by
    have he : hyperbolicSpatialChart w=p := by
      simp only [w,hyperbolicSpatialChart_apply,hyperbolicSpatialCoordinates,spatialHorizontal,
        hyperbolicHorizontal_upperPoint,hyperbolicHeight_upperPoint]
      ext j
      fin_cases j <;> simp
    rw [←he]
    exact hyperbolicSpatialChart.map_source (Set.mem_univ _)
  have he : hyperbolicSpatialChart.symm p=w := by
    rw [hyperbolicSpatialChart_symm_eq ht]
  have hnear := (hyperbolicSpatialChart.continuousAt_symm ht)
    (by simpa only [he] using hU.mem_nhds hw)
  have hrows : ∀ᶠq in 𝓝 p,0<q 2 ∧ ∀r∉T,rowHeight (embeddedRow r) q<1 := by
    filter_upwards [hnear,hyperbolicSpatialChart.open_target.mem_nhds ht] with q hq hqt
    have hpos := hyperbolicSpatialChart_target_positive hqt
    refine ⟨hpos,fun r hr => ?_⟩
    rw [←cosetHeight_upperPoint_rowHeight r q hpos]
    change cosetHeight r (upperPoint (spatialHorizontal q) (q 2) hpos)<1
    rw [←hyperbolicSpatialChart_symm_eq hqt]
    exact hT _ hq r hr
  obtain ⟨V,hV,hVo,hpV⟩ := mem_nhds_iff.mp hrows
  exact ⟨V,hVo,hpV,T,fun q hq => hV hq⟩

def heightPoincareField (F : ℝ → ℂ) (p : SpatialCoordinates) : ℂ :=
  ∑'r : CuspCosets,(cosetCharacter r)⁻¹*F (rowHeight (embeddedRow r) p)

lemma heightPoincareField_locally_finite (F : ℝ → ℂ) (hF : ∀v≤1,F v=0)
    (p : SpatialCoordinates) (hp : 0<p 2) :
    ∃S : Finset CuspCosets, heightPoincareField F =ᶠ[𝓝 p]
      (fun q => ∑r∈S,(cosetCharacter r)⁻¹*F (rowHeight (embeddedRow r) q)) := by
  obtain ⟨U,hU,hpU,S,hrows⟩ := locally_finite_high_rows p hp
  refine ⟨S,?_⟩
  filter_upwards [hU.mem_nhds hpU] with q hq
  apply tsum_eq_sum
  intro r hr
  rw [hF _ ((hrows q hq).2 r hr).le,mul_zero]

lemma heightPoincareField_contDiffAt (F : ℝ → ℂ) (hzero : ∀v≤1,F v=0)
    (hF : ∀v,0<v→ContDiffAt ℝ ∞ F v) (p : SpatialCoordinates) (hp : 0<p 2) :
    ContDiffAt ℝ ∞ (heightPoincareField F) p := by
  obtain ⟨S,hS⟩ := heightPoincareField_locally_finite F hzero p hp
  apply ContDiffAt.congr_of_eventuallyEq _ hS
  apply ContDiffAt.sum
  intro r hr
  exact contDiffAt_const.mul ((hF _ (rowHeight_pos _ (embeddedRow_ne_zero r) p hp)).comp p
    (rowHeight_contDiffAt _ (embeddedRow_ne_zero r) p hp))

lemma heightPoincareField_eq_cuspCorrection (F : ℝ → ℂ) (hzero : ∀v≤1,F v=0)
    (p : SpatialCoordinates) (hp : 0<p 2) :
    heightPoincareField F p=cuspCutoffCorrection 1 F
      (upperPoint ((p 0:ℂ)+(p 1:ℂ)*Complex.I) (p 2) hp) := by
  unfold heightPoincareField cuspCutoffCorrection
  apply tsum_congr
  intro r
  rw [cuspCutoffTerm,cosetHeight_upperPoint_rowHeight]
  split_ifs with h
  · rfl
  · rw [hzero _ (le_of_not_gt h),mul_zero]

def smoothCuspSeed (a b : ℝ) (s : ℂ) : HyperbolicSpace → ℂ :=
  cuspCutoffCorrection 1 (cuspSeedProfile a b s)

def smoothCuspSeedDefect (a b : ℝ) (s : ℂ) : HyperbolicSpace → ℂ :=
  cuspCutoffCorrection 1 (cuspSeedDefectProfile a b s)

lemma smoothCuspSeed_automorphy (a b : ℝ) (s : ℂ) (M : levelThree) (w : HyperbolicSpace) :
    smoothCuspSeed a b s (complexMatrix M • w)=complexCharacter M*smoothCuspSeed a b s w :=
  cuspCutoffCorrection_automorphy 1 le_rfl _ M w
lemma smoothCuspSeedDefect_automorphy (a b : ℝ) (s : ℂ) (M : levelThree) (w : HyperbolicSpace) :
    smoothCuspSeedDefect a b s (complexMatrix M • w)=complexCharacter M*smoothCuspSeedDefect a b s w :=
  cuspCutoffCorrection_automorphy 1 le_rfl _ M w

lemma smoothCuspSeed_coordinate (a b : ℝ) (s : ℂ) (ha : 1<a) (hab : a<b)
    (p : SpatialCoordinates) (hp : 0<p 2) :
    smoothCuspSeed a b s (upperPoint ((p 0:ℂ)+(p 1:ℂ)*Complex.I) (p 2) hp)=
      heightPoincareField (cuspSeedProfile a b s) p :=
  (heightPoincareField_eq_cuspCorrection _
    (fun v hv => cuspSeedProfile_zero a b s v hab (hv.trans ha.le)) p hp).symm
lemma smoothCuspSeedDefect_coordinate (a b : ℝ) (s : ℂ) (ha : 1<a) (hab : a<b)
    (p : SpatialCoordinates) (hp : 0<p 2) :
    smoothCuspSeedDefect a b s (upperPoint ((p 0:ℂ)+(p 1:ℂ)*Complex.I) (p 2) hp)=
      heightPoincareField (cuspSeedDefectProfile a b s) p :=
  (heightPoincareField_eq_cuspCorrection _
    (fun v hv => cuspSeedDefectProfile_zero a b s v hab (Or.inl (lt_of_le_of_lt hv ha))) p hp).symm

lemma smoothCuspSeed_contDiffAt (a b : ℝ) (s : ℂ) (ha : 1<a) (hab : a<b)
    (p : SpatialCoordinates) (hp : 0<p 2) :
    ContDiffAt ℝ ∞ (heightPoincareField (cuspSeedProfile a b s)) p :=
  heightPoincareField_contDiffAt _ (fun v hv => cuspSeedProfile_zero a b s v hab (hv.trans ha.le))
    (cuspSeedProfile_contDiffAt a b s) p hp
lemma smoothCuspSeedDefect_contDiffAt (a b : ℝ) (s : ℂ) (ha : 1<a) (hab : a<b)
    (p : SpatialCoordinates) (hp : 0<p 2) :
    ContDiffAt ℝ ∞ (heightPoincareField (cuspSeedDefectProfile a b s)) p :=
  heightPoincareField_contDiffAt _
    (fun v hv => cuspSeedDefectProfile_zero a b s v hab (Or.inl (lt_of_le_of_lt hv ha)))
    (cuspSeedDefectProfile_contDiffAt a b s) p hp

lemma cuspCutoffCorrection_upperPoint (F : ℝ → ℂ) (z : ℂ) (v : ℝ) (hv : 0<v) (h1v : 1<v) :
    cuspCutoffCorrection 1 F (upperPoint z v hv)=F v := by
  have hh : cosetHeight (cosetOf 1) (upperPoint z v hv)=v := by
    rw [cosetHeight_cosetOf,map_one,one_smul,hyperbolicHeight_upperPoint]
  rw [cuspCutoffCorrection_eq 1 le_rfl _ _ (cosetOf 1) (hh.symm ▸ h1v),hh,
    cosetCharacter_cosetOf,map_one,inv_one,one_mul]

lemma smoothCuspSeed_incoming (a b : ℝ) (s : ℂ) (ha : 1<a) (hab : a<b)
    (z : ℂ) (v : ℝ) (hv : 0<v) (hbv : b≤v) :
    smoothCuspSeed a b s (upperPoint z v hv)=(v:ℂ)^s := by
  rw [smoothCuspSeed,cuspCutoffCorrection_upperPoint _ z v hv (lt_of_lt_of_le (ha.trans hab) hbv)]
  exact cuspSeedProfile_incoming a b s v hab hbv hv

lemma smoothCuspSeedDefect_support (a b : ℝ) (s : ℂ) (hab : a<b) (w : HyperbolicSpace)
    (hw : smoothCuspSeedDefect a b s w≠0) :
    ∃r : CuspCosets, a≤cosetHeight r w ∧ cosetHeight r w≤b := by
  by_contra hn
  apply hw
  unfold smoothCuspSeedDefect cuspCutoffCorrection
  calc
    _ = ∑'r : CuspCosets, (0:ℂ) := by
      apply tsum_congr
      intro r
      have hout : cosetHeight r w<a ∨ b<cosetHeight r w := by
        have h := not_exists.mp hn r
        simpa only [not_and_or,not_le] using h
      simp [cuspCutoffTerm,cuspSeedDefectProfile_zero a b s _ hab hout]
    _ = 0 := tsum_zero
lemma cuspSeed_row_defect (a b : ℝ) (s c : ℂ) (u : Fin 2 → ℂ) (hu : u≠0)
    (p : SpatialCoordinates) (hp : 0<p 2) :
    axisLaplacian (fun q => c*cuspSeedProfile a b s (rowHeight u q)) p-
      s*(s-2)*(c*cuspSeedProfile a b s (rowHeight u p))=
        c*cuspSeedDefectProfile a b s (rowHeight u p) := by
  rw [axisLaplacian_const_mul,rowProfile_laplacian _ (cuspSeedProfile_contDiffAt a b s) u hu p hp]
  have h := cuspSeedProfile_laplace_defect a b s (rowHeight u p) (rowHeight_pos u hu p hp).ne'
  linear_combination c*h

theorem heightPoincare_cuspSeed_laplace_defect (a b : ℝ) (s : ℂ) (ha : 1<a) (hab : a<b)
    (p : SpatialCoordinates) (hp : 0<p 2) :
    axisLaplacian (heightPoincareField (cuspSeedProfile a b s)) p-
      s*(s-2)*heightPoincareField (cuspSeedProfile a b s) p=
        heightPoincareField (cuspSeedDefectProfile a b s) p := by
  obtain ⟨U,hU,hpU,S,hrows⟩ := locally_finite_high_rows p hp
  let f : CuspCosets → SpatialCoordinates → ℂ :=
    fun r q => (cosetCharacter r)⁻¹*cuspSeedProfile a b s (rowHeight (embeddedRow r) q)
  have heq : heightPoincareField (cuspSeedProfile a b s) =ᶠ[𝓝 p] (fun q => ∑r∈S,f r q) := by
    filter_upwards [hU.mem_nhds hpU] with q hq
    apply tsum_eq_sum
    intro r hr
    rw [cuspSeedProfile_zero a b s _ hab (le_trans ((hrows q hq).2 r hr).le ha.le),mul_zero]
  have hD : heightPoincareField (cuspSeedDefectProfile a b s) p=
      ∑r∈S,(cosetCharacter r)⁻¹*cuspSeedDefectProfile a b s (rowHeight (embeddedRow r) p) := by
    apply tsum_eq_sum
    intro r hr
    rw [cuspSeedDefectProfile_zero a b s _ hab (Or.inl (((hrows p hpU).2 r hr).trans ha)),mul_zero]
  have hreg : ∀r∈S,∀q,0<q 2→∀j : Fin 3,
      DifferentiableAt ℝ (axisSlice (f r) q j) (q j) ∧
      DifferentiableAt ℝ (deriv (axisSlice (f r) q j)) (q j) := by
    intro r hr q hq j
    have hc : ∀v,0<v→ContDiffAt ℝ ∞ (fun v => (cosetCharacter r)⁻¹*cuspSeedProfile a b s v) v :=
      fun v hv => contDiffAt_const.mul (cuspSeedProfile_contDiffAt a b s v hv)
    have h := rowProfile_axis_derivatives _ hc (embeddedRow r) (embeddedRow_ne_zero r) q hq j
    exact ⟨h.1.differentiableAt,h.2.differentiableAt⟩
  rw [axisLaplacian_congr_eventuallyEq _ _ p heq,axisLaplacian_finset_sum S f hreg p hp,
    heq.eq_of_nhds,hD,Finset.mul_sum,← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro r hr
  exact cuspSeed_row_defect a b s (cosetCharacter r)⁻¹ (embeddedRow r) (embeddedRow_ne_zero r) p hp

def smoothCuspSeedField (a b : ℝ) (s : ℂ) (p : SpatialCoordinates) : ℂ :=
  if hp : 0<p 2 then smoothCuspSeed a b s
    (upperPoint ((p 0:ℂ)+(p 1:ℂ)*Complex.I) (p 2) hp) else 0

def smoothCuspSeedDefectField (a b : ℝ) (s : ℂ) (p : SpatialCoordinates) : ℂ :=
  if hp : 0<p 2 then smoothCuspSeedDefect a b s
    (upperPoint ((p 0:ℂ)+(p 1:ℂ)*Complex.I) (p 2) hp) else 0

lemma smoothCuspSeedField_eq (a b : ℝ) (s : ℂ) (ha : 1<a) (hab : a<b)
    (p : SpatialCoordinates) (hp : 0<p 2) :
    smoothCuspSeedField a b s p=heightPoincareField (cuspSeedProfile a b s) p := by
  rw [smoothCuspSeedField,dif_pos hp,smoothCuspSeed_coordinate a b s ha hab p hp]
lemma smoothCuspSeedDefectField_eq (a b : ℝ) (s : ℂ) (ha : 1<a) (hab : a<b)
    (p : SpatialCoordinates) (hp : 0<p 2) :
    smoothCuspSeedDefectField a b s p=heightPoincareField (cuspSeedDefectProfile a b s) p := by
  rw [smoothCuspSeedDefectField,dif_pos hp,smoothCuspSeedDefect_coordinate a b s ha hab p hp]

lemma actual_smoothCuspSeed_contDiffAt (a b : ℝ) (s : ℂ) (ha : 1<a) (hab : a<b)
    (p : SpatialCoordinates) (hp : 0<p 2) : ContDiffAt ℝ ∞ (smoothCuspSeedField a b s) p := by
  have heq : smoothCuspSeedField a b s =ᶠ[𝓝 p] heightPoincareField (cuspSeedProfile a b s) := by
    filter_upwards [(continuous_apply 2).continuousAt.eventually_const_lt hp] with q hq
    exact smoothCuspSeedField_eq a b s ha hab q hq
  exact (smoothCuspSeed_contDiffAt a b s ha hab p hp).congr_of_eventuallyEq heq

theorem actual_smoothCuspSeed_laplace_defect (a b : ℝ) (s : ℂ) (ha : 1<a) (hab : a<b)
    (p : SpatialCoordinates) (hp : 0<p 2) :
    axisLaplacian (smoothCuspSeedField a b s) p-s*(s-2)*smoothCuspSeedField a b s p=
      smoothCuspSeedDefectField a b s p := by
  rw [axisLaplacian_congr_positive _ _ (fun q hq => smoothCuspSeedField_eq a b s ha hab q hq) p hp,
    smoothCuspSeedField_eq a b s ha hab p hp,smoothCuspSeedDefectField_eq a b s ha hab p hp]
  exact heightPoincare_cuspSeed_laplace_defect a b s ha hab p hp

lemma cuspCutoffCorrection_parameter_entire (F : ℂ → ℝ → ℂ)
    (hF : ∀v,Differentiable ℂ (fun s => F s v)) (w : HyperbolicSpace) :
    Differentiable ℂ (fun s => cuspCutoffCorrection 1 (F s) w) := by
  let S := (high_cosets_finite 1 le_rfl w).toFinset
  have heq : (fun s => cuspCutoffCorrection 1 (F s) w)=
      (fun s => ∑r∈S,cuspCutoffTerm 1 (F s) r w) := by
    funext s
    apply tsum_eq_sum
    intro r hr
    have hh : ¬1<cosetHeight r w := by simpa only [S,Set.Finite.mem_toFinset,Set.mem_setOf_eq] using hr
    simp [cuspCutoffTerm,hh]
  rw [heq]
  apply Differentiable.fun_sum
  intro r hr
  unfold cuspCutoffTerm
  split_ifs
  · exact (differentiable_const _).mul (hF _)
  · exact differentiable_const _

theorem smoothCuspSeed_entire (a b : ℝ) (w : HyperbolicSpace) :
    Differentiable ℂ (fun s => smoothCuspSeed a b s w) :=
  cuspCutoffCorrection_parameter_entire _ (cuspSeedProfile_entire a b) w

theorem smoothCuspSeedDefect_entire (a b : ℝ) (w : HyperbolicSpace) :
    Differentiable ℂ (fun s => smoothCuspSeedDefect a b s w) :=
  cuspCutoffCorrection_parameter_entire _ (cuspSeedDefectProfile_entire a b) w

lemma kernel_seed_invariant (a b : ℝ) (s : ℂ) (M : globalKubotaKernel) (w : HyperbolicSpace) :
    smoothCuspSeed a b s (M • w)=smoothCuspSeed a b s w := by
  obtain ⟨hM,hchar⟩ := (globalKubotaKernel_mem (M:SL(2,O))).mp M.property
  have he := smoothCuspSeed_automorphy a b s (⟨(M:SL(2,O)),hM⟩ : levelThree) w
  rw [hchar,one_mul] at he
  exact he

lemma kernel_defect_invariant (a b : ℝ) (s : ℂ) (M : globalKubotaKernel) (w : HyperbolicSpace) :
    smoothCuspSeedDefect a b s (M • w)=smoothCuspSeedDefect a b s w := by
  obtain ⟨hM,hchar⟩ := (globalKubotaKernel_mem (M:SL(2,O))).mp M.property
  have he := smoothCuspSeedDefect_automorphy a b s (⟨(M:SL(2,O)),hM⟩ : levelThree) w
  rw [hchar,one_mul] at he
  exact he

def kernelQuotientSeed (a b : ℝ) (s : ℂ) : IntegralOrbitQuotient globalKubotaKernel → ℂ :=
  Quotient.lift (smoothCuspSeed a b s) (by
    rintro w u ⟨M,hM⟩
    rw [←hM]
    exact (kernel_seed_invariant a b s M w).symm)

def kernelQuotientDefect (a b : ℝ) (s : ℂ) : IntegralOrbitQuotient globalKubotaKernel → ℂ :=
  Quotient.lift (smoothCuspSeedDefect a b s) (by
    rintro w u ⟨M,hM⟩
    rw [←hM]
    exact (kernel_defect_invariant a b s M w).symm)

#print axioms locally_finite_high_rows
#print axioms actual_smoothCuspSeed_laplace_defect
#print axioms smoothCuspSeedDefect_entire
#print axioms kernel_defect_invariant
end GaloisForLFunctions.MetaplecticMobiusDescent.CubicEisenstein
