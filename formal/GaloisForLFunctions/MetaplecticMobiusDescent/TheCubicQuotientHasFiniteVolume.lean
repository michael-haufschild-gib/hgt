/-
The quotient-volume proof is adapted from OpenAI’s formalization,
Apache-2.0. See LICENSE and NOTICE for source attribution.
-/
import GaloisForLFunctions.MetaplecticMobiusDescent.HyperbolicVolumeIsInvariant
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Function.L2Space

/-!
# Positive finite volume of the cubic quotient

Restrict invariant hyperbolic volume to the measurable fundamental selector
and push it to the orbit quotient. Invariance makes this construction
independent of the selector. Positivity follows from the countable translate
cover. The exact cusp-box integral and finite Ford cover prove finite mass
for every finite-index subgroup of level three, including the cubic kernel.
The cubic Eisenstein source series descends to this actual quotient.
-/

noncomputable section
open Filter MeasureTheory
open scoped BigOperators Classical Topology MatrixGroups Matrix Pointwise ENNReal
namespace GaloisForLFunctions.MetaplecticMobiusDescent.CubicEisenstein
open Eisenstein CubicKubota

instance integralSubgroupMeasurableAction (H : Subgroup (SL(2,O))) :
    MeasurableConstSMul H HyperbolicSpace :=
  ⟨fun M => (continuous_hyperbolic_action (integralComplexMatrix (M:SL(2,O)))).measurable⟩

instance integralSubgroupVolumeInvariant (H : Subgroup (SL(2,O))) :
    SMulInvariantMeasure H HyperbolicSpace hyperbolicVolume where
  measure_preimage_smul M s hs := by
    have hm := (continuous_hyperbolic_action (integralComplexMatrix (M:SL(2,O)))).measurable
    have he := congrArg (fun ν : Measure HyperbolicSpace => ν s)
      (hyperbolicVolume_invariant (integralComplexMatrix (M:SL(2,O))))
    simpa only [Measure.map_apply hm hs,integralSubgroup_smul] using he

lemma measurable_integralOrbitProjection (H : Subgroup (SL(2,O))) :
    Measurable (integralOrbitProjection H) := measurable_quotient_mk' (s := integralOrbitRel H)

/-- Quotient volume obtained from the actual measurable fundamental selector. -/
def integralQuotientVolume (H : Subgroup (SL(2,O))) : Measure (IntegralOrbitQuotient H) :=
  Measure.map (integralOrbitProjection H) (hyperbolicVolume.restrict (hyperbolicFundamentalSet H))

lemma quotient_projection_measurePreserving (H : Subgroup (SL(2,O))) :
    MeasurePreserving (integralOrbitProjection H)
      (hyperbolicVolume.restrict (hyperbolicFundamentalSet H)) (integralQuotientVolume H) :=
  ⟨measurable_integralOrbitProjection H,rfl⟩

/-- Any measurable fundamental domain gives the same quotient measure. -/
theorem integralQuotientVolume_independent (H : Subgroup (SL(2,O))) (hH : H≤levelThree)
    (D : Set HyperbolicSpace) (hD : IsFundamentalDomain H D hyperbolicVolume) :
    Measure.map (integralOrbitProjection H) (hyperbolicVolume.restrict D)=integralQuotientVolume H := by
  apply Measure.ext
  intro S hS
  have hp := measurable_integralOrbitProjection H
  unfold integralQuotientVolume
  rw [Measure.map_apply hp hS,Measure.map_apply hp hS,Measure.restrict_apply (hp hS),
    Measure.restrict_apply (hp hS)]
  apply hD.measure_set_eq (hyperbolicFundamentalSet_isFundamentalDomain H hH hyperbolicVolume) (hp hS)
  intro M
  ext w
  change integralOrbitProjection H (M • w)∈S ↔ integralOrbitProjection H w∈S
  rw [integralSubgroup_smul,integralOrbitProjection_eq]

lemma integralQuotientVolume_integral (H : Subgroup (SL(2,O)))
    (f : IntegralOrbitQuotient H → ℂ) (hf : AEStronglyMeasurable f (integralQuotientVolume H)) :
    (∫q,f q∂integralQuotientVolume H)=
      ∫w in hyperbolicFundamentalSet H,f (integralOrbitProjection H w)∂hyperbolicVolume :=
  integral_map (measurable_integralOrbitProjection H).aemeasurable hf

lemma hyperbolicEuclideanVolume_ne_zero : hyperbolicEuclideanVolume≠0 := by
  have hU : IsOpen euclideanUpperHalf := isOpen_lt continuous_const (by fun_prop)
  have hne : euclideanUpperHalf.Nonempty := ⟨WithLp.toLp 2 ![0,0,1],by change (0:ℝ)<1; norm_num⟩
  have hpos : 0<volume euclideanUpperHalf := hU.measure_pos volume hne
  have hAC : (volume.restrict euclideanUpperHalf) ≪ hyperbolicEuclideanVolume := by
    apply withDensity_absolutelyContinuous' hyperbolicDensity_measurable.aemeasurable
    filter_upwards [ae_restrict_mem euclideanUpperHalf_measurable] with p hp
    apply ne_of_gt
    change 0<ENNReal.ofReal ((p 2)^3)⁻¹
    apply ENNReal.ofReal_pos.mpr
    exact inv_pos.mpr (pow_pos hp 3)
  intro hz
  have hh : (volume.restrict euclideanUpperHalf) Set.univ=0 := hAC (by rw [hz]; simp)
  simp only [Measure.restrict_apply MeasurableSet.univ,Set.univ_inter] at hh
  exact hpos.ne' hh

lemma hyperbolicVolume_ne_zero : hyperbolicVolume≠0 :=
  (Measure.map_ne_zero_iff euclideanToHyperbolic_measurable.aemeasurable).mpr hyperbolicEuclideanVolume_ne_zero

/-- A null fundamental domain would make its countable translate cover null. -/
lemma integralQuotientVolume_ne_zero (H : Subgroup (SL(2,O))) (hH : H≤levelThree) :
    integralQuotientVolume H≠0 := by
  apply (Measure.map_ne_zero_iff (measurable_integralOrbitProjection H).aemeasurable).mpr
  intro hz
  have hD := MeasureTheory.IsFundamentalDomain.measure_ne_zero hyperbolicVolume_ne_zero
    (hyperbolicFundamentalSet_isFundamentalDomain H hH hyperbolicVolume)
  have hh := congrArg (fun ν : Measure HyperbolicSpace => ν Set.univ) hz
  simp only [Measure.restrict_apply MeasurableSet.univ,Set.univ_inter] at hh
  exact hD hh

/-- The complex `L²` space of the actual cubic quotient. -/
abbrev KernelQuotientL2 := Lp ℂ 2 (integralQuotientVolume globalKubotaKernel)
example : InnerProductSpace ℂ KernelQuotientL2 := inferInstance
example : CompleteSpace KernelQuotientL2 := inferInstance

lemma kernel_eisenstein_invariant (M : globalKubotaKernel) (s : ℂ) (hs : 2<s.re)
    (w : HyperbolicSpace) :
    hyperbolicEisenstein s (M • w)=hyperbolicEisenstein s w := by
  obtain ⟨hM,hchar⟩ := (globalKubotaKernel_mem (M:SL(2,O))).mp M.property
  have he := hyperbolicEisenstein_automorphy (⟨(M:SL(2,O)),hM⟩ : levelThree) s hs w
  rw [hchar,one_mul] at he
  exact he

/-- The convergent cubic source series descended to its character kernel quotient. -/
def kernelQuotientEisenstein (s : ℂ) (hs : 2<s.re) :
    IntegralOrbitQuotient globalKubotaKernel → ℂ :=
  Quotient.lift (hyperbolicEisenstein s) (by
    rintro w u ⟨M,hM⟩
    rw [←hM]
    exact (kernel_eisenstein_invariant M s hs w).symm)

lemma kernelQuotientEisenstein_mk (s : ℂ) (hs : 2<s.re) (w : HyperbolicSpace) :
    kernelQuotientEisenstein s hs (integralOrbitProjection globalKubotaKernel w)=
      hyperbolicEisenstein s w := rfl


/-- Exact integral of the inverse cube of height above a positive cutoff. -/
lemma cusp_height_volume (a : ℝ) (ha : 0<a) :
    (∫⁻v in Set.Ioi a,ENNReal.ofReal ((v^3)⁻¹))=ENNReal.ofReal (1/(2*a^2)) := by
  have hi : IntegrableOn (fun v : ℝ => (v^3)⁻¹) (Set.Ioi a) volume := by
    simpa only [show (-3:ℝ)=-(3:ℕ) by norm_num,Real.rpow_neg_natCast,zpow_neg,
      zpow_natCast] using (integrableOn_Ioi_rpow_of_lt (by norm_num : (-3:ℝ) < -1) ha)
  have hn : 0≤ᵐ[volume.restrict (Set.Ioi a)] (fun v : ℝ => (v^3)⁻¹) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with v hv
    exact inv_nonneg.mpr (pow_nonneg (ha.trans hv).le 3)
  rw [←ofReal_integral_eq_lintegral_ofReal hi hn]
  congr 1
  have he := integral_Ioi_rpow_of_lt (by norm_num : (-3:ℝ) < -1) ha
  norm_num only at he
  simp only [show (-3:ℝ)=-(3:ℕ) by norm_num,Real.rpow_neg_natCast,zpow_neg,
    zpow_natCast] at he
  rw [he]
  norm_num [show (-3:ℝ)+1=-2 by norm_num]
  field_simp


/-- Any set meeting every orbit has at least the fundamental-domain measure. -/
lemma fundamentalSet_measure_le_cover (H : Subgroup (SL(2,Eisenstein.O)))
    (hH : H≤CubicKubota.levelThree) (B : Set HyperbolicSpace)
    (hB : ∀w,∃M:H,M • w∈B) :
    hyperbolicVolume (hyperbolicFundamentalSet H)≤hyperbolicVolume B := by
  rw [(hyperbolicFundamentalSet_isFundamentalDomain H hH hyperbolicVolume).measure_eq_tsum B]
  apply le_trans (measure_mono ?_) (measure_iUnion_le _)
  intro w hw
  obtain ⟨M,hM⟩ := hB w
  apply Set.mem_iUnion.mpr
  refine ⟨M⁻¹,?_,hw⟩
  exact ⟨M • w,hM,inv_smul_smul M w⟩


/-- Separate the vertical coordinate from the horizontal plane without changing volume. -/
def spatialHeightSplit : EuclideanSpatial ≃ᵐ ℝ × (Fin 2 → ℝ) :=
  (MeasurableEquiv.toLp 2 (Fin 3 → ℝ)).symm.trans
    (MeasurableEquiv.piFinSuccAbove (fun _ : Fin 3 => ℝ) 2)

lemma spatialHeightSplit_fst (p : EuclideanSpatial) : (spatialHeightSplit p).1=p 2 := rfl
lemma spatialHeightSplit_snd_zero (p : EuclideanSpatial) : (spatialHeightSplit p).2 0=p 0 := rfl
lemma spatialHeightSplit_snd_one (p : EuclideanSpatial) : (spatialHeightSplit p).2 1=p 1 := rfl

lemma spatialHeightSplit_preserves_volume : MeasurePreserving spatialHeightSplit volume volume :=
  (volume_preserving_piFinSuccAbove (fun _ : Fin 3 => ℝ) 2).comp
    (EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp (Fin 3))

def horizontalUnitBox : Set (Fin 2 → ℝ) := Set.pi Set.univ (fun _ => Set.Icc (-1) 1)
lemma horizontalUnitBox_measurable : MeasurableSet horizontalUnitBox :=
  MeasurableSet.pi (Set.to_countable _) (fun _ _ => measurableSet_Icc)
lemma horizontalUnitBox_volume : volume horizontalUnitBox=4 := by
  rw [horizontalUnitBox,volume_pi_pi]
  norm_num

def euclideanCuspBox (a : ℝ) : Set EuclideanSpatial :=
  spatialHeightSplit ⁻¹' (Set.Ioi a ×ˢ horizontalUnitBox)
lemma euclideanCuspBox_measurable (a : ℝ) : MeasurableSet (euclideanCuspBox a) :=
  spatialHeightSplit.measurable (measurableSet_Ioi.prod horizontalUnitBox_measurable)
lemma euclideanCuspBox_positive (a : ℝ) (ha : 0≤a) : euclideanCuspBox a ⊆ euclideanUpperHalf := by
  intro p hp
  exact ha.trans_lt hp.1

/-- A horizontal square of area four above height `a` has hyperbolic volume `2/a²`. -/
theorem euclideanCuspBox_volume (a : ℝ) (ha : 0<a) :
    hyperbolicEuclideanVolume (euclideanCuspBox a)=4*ENNReal.ofReal (1/(2*a^2)) := by
  unfold hyperbolicEuclideanVolume
  rw [withDensity_apply _ (euclideanCuspBox_measurable a),
    Measure.restrict_restrict (euclideanCuspBox_measurable a),
    Set.inter_eq_left.mpr (euclideanCuspBox_positive a ha.le)]
  change (∫⁻p in spatialHeightSplit ⁻¹' (Set.Ioi a ×ˢ horizontalUnitBox),
    ENNReal.ofReal (((spatialHeightSplit p).1^3)⁻¹))=_
  rw [spatialHeightSplit_preserves_volume.setLIntegral_comp_preimage
    (f := fun q : ℝ × (Fin 2 → ℝ) => ENNReal.ofReal ((q.1^3)⁻¹))
    (measurableSet_Ioi.prod horizontalUnitBox_measurable) (by fun_prop)]
  change (∫⁻q : ℝ × (Fin 2 → ℝ) in Set.Ioi a ×ˢ horizontalUnitBox,
    ENNReal.ofReal ((q.1^3)⁻¹) ∂((volume : Measure ℝ).prod volume))=_
  rw [setLIntegral_prod _ (by fun_prop)]
  simp only [lintegral_const,Measure.restrict_apply MeasurableSet.univ,Set.univ_inter,
    horizontalUnitBox_volume]
  rw [lintegral_mul_const _ (by fun_prop),cusp_height_volume a ha]
  exact mul_comm _ _


instance fullSLMeasurableAction : MeasurableConstSMul (SL(2,ℂ)) HyperbolicSpace :=
  ⟨fun g => (continuous_hyperbolic_action g).measurable⟩
instance fullSLVolumeInvariant : SMulInvariantMeasure (SL(2,ℂ)) HyperbolicSpace hyperbolicVolume where
  measure_preimage_smul g s hs := by
    have he := congrArg (fun ν : Measure HyperbolicSpace => ν s) (hyperbolicVolume_invariant g)
    simpa only [Measure.map_apply (continuous_hyperbolic_action g).measurable hs] using he

def hyperbolicCuspBox (a : ℝ) : Set HyperbolicSpace :=
  {w | ‖hyperbolicHorizontal w‖≤1 ∧ a<hyperbolicHeight w}

lemma hyperbolicCuspBox_measurable (a : ℝ) : MeasurableSet (hyperbolicCuspBox a) :=
  (isClosed_le hyperbolicHorizontal_continuous.norm continuous_const).measurableSet.inter
    (isOpen_lt continuous_const hyperbolicHeight_continuous).measurableSet

lemma hyperbolicCuspBox_volume_le (a : ℝ) (ha : 0<a) :
    hyperbolicVolume (hyperbolicCuspBox a)≤4*ENNReal.ofReal (1/(2*a^2)) := by
  rw [hyperbolicVolume,Measure.map_apply euclideanToHyperbolic_measurable
    (hyperbolicCuspBox_measurable a),←euclideanCuspBox_volume a ha]
  apply measure_mono_ae
  filter_upwards [hyperbolicEuclideanVolume_ae_positive] with p hp hB
  change euclideanToHyperbolic p ∈ hyperbolicCuspBox a at hB
  change p ∈ euclideanCuspBox a
  rw [euclideanToHyperbolic_positive p hp] at hB
  change ‖hyperbolicHorizontal (upperPoint _ _ hp)‖≤1 ∧ a<hyperbolicHeight (upperPoint _ _ hp) at hB
  rw [hyperbolicHorizontal_upperPoint,hyperbolicHeight_upperPoint] at hB
  refine ⟨hB.2,?_⟩
  intro j hj
  fin_cases j
  · change -1≤p 0 ∧ p 0≤1
    have hh := (Complex.abs_re_le_norm ((p 0:ℂ)+Complex.I*(p 1:ℂ))).trans hB.1
    simpa using abs_le.mp hh
  · change -1≤p 1 ∧ p 1≤1
    have hh := (Complex.abs_im_le_norm ((p 0:ℂ)+Complex.I*(p 1:ℂ))).trans hB.1
    simpa using abs_le.mp hh

lemma hyperbolicCuspBox_volume_lt_top (a : ℝ) (ha : 0<a) :
    hyperbolicVolume (hyperbolicCuspBox a)<⊤ :=
  (hyperbolicCuspBox_volume_le a ha).trans_lt (ENNReal.mul_lt_top (by norm_num) ENNReal.ofReal_lt_top)

/-- The finite Ford cover bounds fundamental-domain volume by finitely many cusp boxes. -/
theorem hyperbolicFundamentalSet_volume_lt_top (H : Subgroup (SL(2,O)))
    (hH : H≤CubicKubota.levelThree) [H.FiniteIndex] :
    hyperbolicVolume (hyperbolicFundamentalSet H)<⊤ := by
  obtain ⟨S,hS⟩ := finiteIndex_ford_cover H
  let a : ℝ := Real.sqrt (2/3)/2
  have ha : 0<a := by dsimp [a]; positivity
  let B : Set HyperbolicSpace := ⋃r∈S,integralComplexMatrix r⁻¹ • hyperbolicCuspBox a
  have hcover : ∀w,∃M:H,M • w∈B := by
    intro w
    obtain ⟨M,r,hr,z,v,hv,hM,hz,hfloor⟩ := hS w
    refine ⟨M,?_⟩
    rw [integralSubgroup_smul,hM]
    apply Set.mem_iUnion.mpr
    refine ⟨r,Set.mem_iUnion.mpr ⟨hr,?_⟩⟩
    apply Set.mem_smul_set.mpr
    refine ⟨upperPoint z v hv,?_,rfl⟩
    change ‖hyperbolicHorizontal (upperPoint z v hv)‖≤1 ∧ a<hyperbolicHeight (upperPoint z v hv)
    rw [hyperbolicHorizontal_upperPoint,hyperbolicHeight_upperPoint]
    refine ⟨?_,?_⟩
    · rw [Complex.normSq_eq_norm_sq] at hz
      nlinarith [norm_nonneg z]
    · dsimp [a] at *
      linarith
  apply (fundamentalSet_measure_le_cover H hH B hcover).trans_lt
  apply (measure_biUnion_finset_le S (fun r => integralComplexMatrix r⁻¹ • hyperbolicCuspBox a)).trans_lt
  apply ENNReal.sum_lt_top.mpr
  intro r hr
  rw [measure_smul]
  exact hyperbolicCuspBox_volume_lt_top a ha

lemma integralQuotientVolume_univ (H : Subgroup (SL(2,O))) :
    integralQuotientVolume H Set.univ=hyperbolicVolume (hyperbolicFundamentalSet H) := by
  rw [integralQuotientVolume,Measure.map_apply (measurable_integralOrbitProjection H) MeasurableSet.univ]
  simp

theorem integralQuotientVolume_finite (H : Subgroup (SL(2,O)))
    (hH : H≤CubicKubota.levelThree) [H.FiniteIndex] : IsFiniteMeasure (integralQuotientVolume H) :=
  ⟨by rw [integralQuotientVolume_univ]; exact hyperbolicFundamentalSet_volume_lt_top H hH⟩

/-- The constructed cubic kernel has finite covolume. -/
instance kernelQuotientVolume_finite : IsFiniteMeasure (integralQuotientVolume globalKubotaKernel) := by
  let : globalKubotaKernel.FiniteIndex := globalKubotaKernel_finiteIndex
  exact integralQuotientVolume_finite globalKubotaKernel globalKubotaKernel_le_levelThree

/-- The actual cubic quotient has positive, finite invariant volume. -/
theorem kernelQuotientVolume_pos_finite :
    0 < integralQuotientVolume globalKubotaKernel Set.univ ∧
      integralQuotientVolume globalKubotaKernel Set.univ < ⊤ := by
  exact ⟨Measure.measure_univ_pos.mpr
    (integralQuotientVolume_ne_zero _ globalKubotaKernel_le_levelThree),
    measure_lt_top _ _⟩

#print axioms integralQuotientVolume_independent
#print axioms euclideanCuspBox_volume
#print axioms kernelQuotientVolume_pos_finite
#print axioms kernel_eisenstein_invariant

end GaloisForLFunctions.MetaplecticMobiusDescent.CubicEisenstein
