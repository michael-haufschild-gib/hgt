/-
Bianchi reduction and the cusp cover are adapted from OpenAI’s formalization,
Apache-2.0. See LICENSE and NOTICE for source attribution.
-/
import GaloisForLFunctions.MetaplecticMobiusDescent.HyperbolicThreeSpace
import GaloisForLFunctions.MetaplecticMobiusDescent.EisensteinNearestPoint
import GaloisForLFunctions.MetaplecticMobiusDescent.TheCubicKubotaMultiplier

/-!
# Bianchi reduction and compact truncations

Integral bottom rows have finite bounded-energy sublevels. Choose maximal
orbit height, then translate to the Eisenstein nearest-point hexagon.
Inversion forces `|z|²+v²≥1`, hence `v≥√(2/3)`. Finite coset representatives
transfer this cover to every finite-index integral subgroup. Cutting off
height gives a compact core and finitely many explicit cusp tails.
-/

noncomputable section
open scoped BigOperators Classical Topology MatrixGroups Matrix
namespace GaloisForLFunctions.MetaplecticMobiusDescent.CubicEisenstein
open Eisenstein CubicKubota

def integralComplexMatrix : SL(2,O)→*SL(2,ℂ) :=
  Matrix.SpecialLinearGroup.map ringComplex

def rowCoordinates (v : Fin 2 → O) : (Fin 2 × Fin 2) → ℤ :=
  fun i => if i.2 = 0 then (Coordinates.coords (v i.1)).1
    else (Coordinates.coords (v i.1)).2

lemma rowCoordinates_injective : Function.Injective rowCoordinates := by
  intro v w hvw
  funext i
  apply Coordinates.coordinateEquiv.injective
  apply Prod.ext
  · exact congrFun hvw (i,0)
  · exact congrFun hvw (i,1)

lemma coordinates_norm_bound (v : Fin 2→O) :
    ‖rowCoordinates v‖≤2*‖fun i => ringComplex (v i)‖ := by
  apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr
  intro i
  have h := coordinates_norm_le (v i.1)
  rw [Prod.norm_def,max_le_iff] at h
  have hi := norm_le_pi_norm (fun j => ringComplex (v j)) i.1
  dsimp only [rowCoordinates]
  split_ifs
  · exact h.1.trans (mul_le_mul_of_nonneg_left hi (by norm_num))
  · exact h.2.trans (mul_le_mul_of_nonneg_left hi (by norm_num))

def rowBound (g : SL(2,ℂ)) : ℝ := 2 * (1 + ‖rowOperator g⁻¹‖)

lemma rowBound_pos (g : SL(2,ℂ)) : 0 < rowBound g := by unfold rowBound; positivity

lemma coordinates_le_transformed_energy (g : SL(2,ℂ)) (v : Fin 2 → O) :
    ‖rowCoordinates v‖ ≤ rowBound g *
      Real.sqrt (rowEnergy (rowOperator g (fun i => ringComplex (v i)))) := by
  have hi := (rowOperator g⁻¹).le_opNorm (rowOperator g (fun i => ringComplex (v i)))
  rw [rowOperator_mul, mul_inv_cancel, rowOperator_one] at hi
  have hb := coordinates_norm_bound v
  have he := norm_le_sqrt_rowEnergy (rowOperator g (fun i => ringComplex (v i)))
  have hm := mul_le_mul_of_nonneg_left he (norm_nonneg (rowOperator g⁻¹))
  dsimp only [rowBound]
  nlinarith [Real.sqrt_nonneg (rowEnergy (rowOperator g (fun i => ringComplex (v i))))]

def integralBottomRow (M : SL(2,O)) : Fin 2 → O := fun j => M 1 j
def integralRowEnergy (g : SL(2,ℂ)) (v : Fin 2 → O) : ℝ :=
  rowEnergy (rowOperator g (fun j => ringComplex (v j)))

/-- Bounded transformed energy bounds all four integral row coordinates. -/
lemma integralRowEnergy_sublevel_finite (g : SL(2,ℂ)) (C : ℝ) :
    Set.Finite {v : Fin 2 → O | integralRowEnergy g v≤C} := by
  have hb : Set.Finite (Metric.closedBall (0 : (Fin 2×Fin 2)→ℤ) (rowBound g*Real.sqrt C)) :=
    (isCompact_closedBall _ _).finite_of_discrete
  apply (Set.Finite.preimage rowCoordinates_injective.injOn hb).subset
  intro v hv
  change rowCoordinates v∈Metric.closedBall 0 (rowBound g*Real.sqrt C)
  rw [Metric.mem_closedBall,dist_zero_right]
  exact (coordinates_le_transformed_energy g v).trans
    (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hv) (rowBound_pos g).le)

lemma integral_height_action_matrix (M : SL(2,O)) (g : SL(2,ℂ)) :
    hyperbolicHeight (integralComplexMatrix M • (QuotientGroup.mk g : HyperbolicSpace))=
      (integralRowEnergy g (integralBottomRow M))⁻¹ := by
  change (rowEnergy (complexBottomRow (integralComplexMatrix M*g)))⁻¹=_
  rw [complexBottomRow_mul]
  rfl

lemma integralRowEnergy_bottom_pos (g : SL(2,ℂ)) (M : SL(2,O)) :
    0 < integralRowEnergy g (integralBottomRow M) := by
  have h := hyperbolicHeight_pos (integralComplexMatrix M • (QuotientGroup.mk g : HyperbolicSpace))
  rw [integral_height_action_matrix,inv_pos] at h
  exact h

/-- The inverse row-energy height attains its maximum on each integral orbit. -/
theorem exists_maximal_integral_height (w : HyperbolicSpace) :
    ∃N : SL(2,O), ∀M : SL(2,O),
      hyperbolicHeight (integralComplexMatrix M • w)≤hyperbolicHeight (integralComplexMatrix N • w) := by
  induction w using Quotient.inductionOn with
  | _ g =>
    let P : Set (Fin 2 → O) := Set.range integralBottomRow
    let C := integralRowEnergy g (integralBottomRow 1)
    let S : Set (Fin 2 → O) := {v | integralRowEnergy g v≤C} ∩ P
    have hS : Set.Finite S := (integralRowEnergy_sublevel_finite g C).inter_of_left P
    have hSne : S.Nonempty := by
      refine ⟨integralBottomRow 1,?_⟩
      change C≤C ∧ integralBottomRow 1∈Set.range integralBottomRow
      exact ⟨le_rfl,1,rfl⟩
    obtain ⟨v,hv,hmin⟩ := Set.exists_min_image S (integralRowEnergy g) hS hSne
    obtain ⟨N,hN⟩ := hv.2
    refine ⟨N,fun M => ?_⟩
    have hNM : integralRowEnergy g (integralBottomRow N)≤ integralRowEnergy g (integralBottomRow M) := by
      rw [hN]
      by_cases hM : integralRowEnergy g (integralBottomRow M)≤C
      · exact hmin _ ⟨hM,⟨M,rfl⟩⟩
      · exact hv.1.trans (le_of_not_ge hM)
    rw [integral_height_action_matrix,integral_height_action_matrix]
    exact inv_anti₀ (integralRowEnergy_bottom_pos g N) hNM

def integralTranslation (n : O) : SL(2,O) :=
  ⟨!![1,n;0,1],by simp [Matrix.det_fin_two]⟩
def integralInversion : SL(2,O) :=
  ⟨!![0,-1;1,0],by simp [Matrix.det_fin_two]⟩

lemma integralTranslation_action (n : O) (z : ℂ) (v : ℝ) (hv : 0<v) :
    integralComplexMatrix (integralTranslation n) • upperPoint z v hv=
      upperPoint (z+ringComplex n) v hv := by
  change (QuotientGroup.mk (integralComplexMatrix (integralTranslation n)*upperSection z v hv) : HyperbolicSpace)=
    QuotientGroup.mk (upperSection (z+ringComplex n) v hv)
  apply congrArg (fun g : SL(2,ℂ) => (QuotientGroup.mk g : HyperbolicSpace))
  apply Subtype.ext
  change (integralComplexMatrix (integralTranslation n) : Matrix (Fin 2) (Fin 2) ℂ) *
    (upperSection z v hv : Matrix (Fin 2) (Fin 2) ℂ) =
    (upperSection (z + ringComplex n) v hv : Matrix (Fin 2) (Fin 2) ℂ)
  simp only [integralComplexMatrix, Matrix.SpecialLinearGroup.map_apply_coe]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [integralTranslation,RingHom.mapMatrix_apply,Matrix.map_apply,upperSection,Matrix.mul_apply,
      Fin.sum_univ_two,div_eq_mul_inv] ; ring

lemma integralInversion_height (z : ℂ) (v : ℝ) (hv : 0<v) :
    hyperbolicHeight (integralComplexMatrix integralInversion • upperPoint z v hv)=
      v/(‖z‖^2+v^2) := by
  have h10 : integralComplexMatrix integralInversion 1 0 = 1 := by
    change ringComplex 1 = 1
    exact map_one ringComplex
  have h11 : integralComplexMatrix integralInversion 1 1 = 0 := by
    change ringComplex 0 = 0
    exact map_zero ringComplex
  rw [hyperbolicHeight_action_upperPoint, h10, h11]
  simp

/-- At maximal height, nearest-point translation gives the Ford inequalities. -/
theorem bianchi_ford_cover (w : HyperbolicSpace) :
    ∃M : SL(2,O), ∃z : ℂ, ∃v : ℝ, ∃hv : 0<v,
      integralComplexMatrix M • w=upperPoint z v hv ∧
      Complex.normSq z≤1/3 ∧ 1≤Complex.normSq z+v^2 ∧
      ∀R : SL(2,O),hyperbolicHeight (integralComplexMatrix R • upperPoint z v hv)≤v := by
  obtain ⟨N,hN⟩ := exists_maximal_integral_height w
  obtain ⟨z,v,hv,hpoint⟩ := upperPoint_surjective (integralComplexMatrix N • w)
  obtain ⟨n,hn⟩ := exists_eisenstein_distance_sq_le_third z
  let M : SL(2,O) := integralTranslation (-n)*N
  let z' := z-ringComplex n
  have hMw : integralComplexMatrix M • w=upperPoint z' v hv := by
    dsimp [M]
    rw [map_mul,mul_smul,← hpoint,integralTranslation_action,map_neg]
    rfl
  have hNv : hyperbolicHeight (integralComplexMatrix N • w)=v := by
    rw [← hpoint,hyperbolicHeight_upperPoint]
  have hmax (R : SL(2,O)) :
      hyperbolicHeight (integralComplexMatrix R • upperPoint z' v hv)≤v := by
    have h := hN (R*M)
    rwa [map_mul,mul_smul,hMw,hNv] at h
  have hinv := hmax integralInversion
  rw [integralInversion_height] at hinv
  have hden : 0<‖z'‖^2+v^2 := by positivity
  have hunit : 1≤‖z'‖^2+v^2 := by
    have hm := (div_le_iff₀ hden).mp hinv
    by_contra hh
    have hlt := mul_lt_mul_of_pos_left (lt_of_not_ge hh) hv
    linarith
  refine ⟨M,z',v,hv,hMw,hn,?_,hmax⟩
  simpa only [Complex.normSq_eq_norm_sq] using hunit

/-- The hexagonal covering bound forces a uniform positive height floor. -/
theorem bianchi_reduction_height_floor (w : HyperbolicSpace) :
    ∃M : SL(2,O), ∃z : ℂ, ∃v : ℝ, ∃hv : 0<v,
      integralComplexMatrix M • w=upperPoint z v hv ∧
      Complex.normSq z≤1/3 ∧ Real.sqrt (2/3)≤v := by
  obtain ⟨M,z,v,hv,hMw,hz,hunit,hmax⟩ := bianchi_ford_cover w
  refine ⟨M,z,v,hv,hMw,hz,?_⟩
  apply (Real.sqrt_le_iff).mpr
  exact ⟨hv.le,by linarith⟩

def truncatedFordBox (T : ℝ) : Set (ℂ×ℝ) :=
  Metric.closedBall 0 1 ×ˢ Set.Icc (Real.sqrt (2/3)) T
lemma truncatedFordBox_isCompact (T : ℝ) : IsCompact (truncatedFordBox T) :=
  (isCompact_closedBall _ _).prod isCompact_Icc

lemma mem_truncatedFordBox (z : ℂ) (v T : ℝ)
    (hz : Complex.normSq z≤1/3) (hv : Real.sqrt (2/3)≤v) (hT : v≤T) :
    (z,v)∈truncatedFordBox T := by
  refine ⟨?_,hv,hT⟩
  rw [Metric.mem_closedBall,dist_zero_right]
  rw [Complex.normSq_eq_norm_sq] at hz
  nlinarith [norm_nonneg z]

lemma finite_right_representatives {G : Type*} [Group G] (H : Subgroup G) [H.FiniteIndex] :
    ∃S : Finset G, ∀g : G,∃r∈S,r⁻¹*g∈H := by
  let : Fintype (G ⧸ H) := Fintype.ofFinite _
  let S : Finset G := Finset.univ.image (fun q : G ⧸ H => Quotient.out q)
  refine ⟨S,fun g => ?_⟩
  let q : G ⧸ H := QuotientGroup.mk g
  refine ⟨Quotient.out q,?_,?_⟩
  · exact Finset.mem_image.mpr ⟨q,Finset.mem_univ _,rfl⟩
  · exact QuotientGroup.leftRel_apply.mp (Quotient.exact' (Quotient.out_eq' q))

theorem finiteIndex_ford_cover (H : Subgroup (SL(2,O))) [H.FiniteIndex] :
    ∃S : Finset (SL(2,O)), ∀w : HyperbolicSpace,
      ∃h : H, ∃r∈S, ∃z : ℂ, ∃v : ℝ, ∃hv : 0<v,
        integralComplexMatrix (h:SL(2,O)) • w=
          integralComplexMatrix r⁻¹ • upperPoint z v hv ∧
        Complex.normSq z≤1/3 ∧ Real.sqrt (2/3)≤v := by
  obtain ⟨S,hS⟩ := finite_right_representatives H
  refine ⟨S,fun w => ?_⟩
  obtain ⟨M,z,v,hv,hMw,hz,hfloor⟩ := bianchi_reduction_height_floor w
  obtain ⟨r,hr,hh⟩ := hS M
  refine ⟨⟨r⁻¹*M,hh⟩,r,hr,z,v,hv,?_,hz,hfloor⟩
  change integralComplexMatrix (r⁻¹*M) • w=_
  rw [map_mul,mul_smul,hMw]

theorem globalKubotaKernel_ford_cover :
    ∃S : Finset (SL(2,O)), ∀w : HyperbolicSpace,
      ∃h : globalKubotaKernel, ∃r∈S, ∃z : ℂ, ∃v : ℝ, ∃hv : 0<v,
        integralComplexMatrix (h:SL(2,O)) • w=integralComplexMatrix r⁻¹ • upperPoint z v hv ∧
        Complex.normSq z≤1/3 ∧ Real.sqrt (2/3)≤v := by
  let : globalKubotaKernel.FiniteIndex := globalKubotaKernel_finiteIndex
  exact finiteIndex_ford_cover globalKubotaKernel

def integralOrbitRel (H : Subgroup (SL(2,O))) : Setoid HyperbolicSpace where
  r w w' := ∃h : H, integralComplexMatrix (h:SL(2,O)) • w = w'
  iseqv := ⟨by intro w; exact ⟨1,by simp⟩,
    by
      rintro w w' ⟨h,hh⟩
      refine ⟨h⁻¹,?_⟩
      rw [←hh]
      simp [←mul_smul],
    by
      rintro w w' w'' ⟨h,hh⟩ ⟨k,hk⟩
      refine ⟨k*h,?_⟩
      simpa only [Subgroup.coe_mul,map_mul,mul_smul,hh] using hk⟩

abbrev IntegralOrbitQuotient (H : Subgroup (SL(2,O))) := Quotient (integralOrbitRel H)

def integralOrbitProjection (H : Subgroup (SL(2,O))) :
    HyperbolicSpace → IntegralOrbitQuotient H := Quotient.mk _

lemma continuous_integralOrbitProjection (H : Subgroup (SL(2,O))) :
    Continuous (integralOrbitProjection H) := continuous_quotient_mk'

lemma integralOrbitProjection_eq (H : Subgroup (SL(2,O))) (h : H) (w : HyperbolicSpace) :
    integralOrbitProjection H (integralComplexMatrix (h:SL(2,O)) • w)=
      integralOrbitProjection H w := by
  apply Eq.symm
  exact Quotient.sound ⟨h,rfl⟩

def truncatedFordLift (T : ℝ) (p : truncatedFordBox T) : UpperCoordinates :=
  ⟨p.1,lt_of_lt_of_le (Real.sqrt_pos.mpr (by norm_num : (0:ℝ)<2/3)) p.2.2.1⟩

lemma continuous_truncatedFordLift (T : ℝ) : Continuous (truncatedFordLift T) :=
  continuous_subtype_val.subtype_mk _

def fordOrbitChart (H : Subgroup (SL(2,O))) (r : SL(2,O)) (p : UpperCoordinates) :
    IntegralOrbitQuotient H := integralOrbitProjection H
      (integralComplexMatrix r⁻¹ • upperPoint p.1.1 p.1.2 p.2)

lemma continuous_fordOrbitChart (H : Subgroup (SL(2,O))) (r : SL(2,O)) :
    Continuous (fordOrbitChart H r) :=
  (continuous_integralOrbitProjection H).comp
    (continuous_translatedUpperCoordinates (integralComplexMatrix r⁻¹))

/-- Finite union of truncated coordinate images in the integral orbit quotient. -/
def compactFordCore (H : Subgroup (SL(2,O))) (S : Finset (SL(2,O))) (T : ℝ) :
    Set (IntegralOrbitQuotient H) :=
  ⋃r∈S, Set.range (fun p : truncatedFordBox T => fordOrbitChart H r (truncatedFordLift T p))

lemma compactFordCore_isCompact (H : Subgroup (SL(2,O))) (S : Finset (SL(2,O))) (T : ℝ) :
    IsCompact (compactFordCore H S T) := by
  let : CompactSpace (truncatedFordBox T) :=
    isCompact_iff_compactSpace.mp (truncatedFordBox_isCompact T)
  apply S.isCompact_biUnion
  intro r hr
  exact isCompact_range ((continuous_fordOrbitChart H r).comp (continuous_truncatedFordLift T))

def fordCuspTail (H : Subgroup (SL(2,O))) (r : SL(2,O)) (T : ℝ) :
    Set (IntegralOrbitQuotient H) :=
  fordOrbitChart H r '' {p : UpperCoordinates | Complex.normSq p.1.1≤1/3 ∧
    Real.sqrt (2/3)≤p.1.2 ∧ T<p.1.2}

/-- A finite-index quotient is covered by a compact truncation and finitely many cusp tails. -/
theorem finiteIndex_compact_core_cusp_cover (H : Subgroup (SL(2,O))) [H.FiniteIndex] :
    ∃S : Finset (SL(2,O)), ∀T : ℝ,
      IsCompact (compactFordCore H S T) ∧
      Set.univ=compactFordCore H S T ∪ ⋃r∈S, fordCuspTail H r T := by
  obtain ⟨S,hS⟩ := finiteIndex_ford_cover H
  refine ⟨S,fun T => ⟨compactFordCore_isCompact H S T,?_⟩⟩
  apply Set.Subset.antisymm
  · intro q hq
    induction q using Quotient.inductionOn with | _ w =>
      obtain ⟨h,r,hr,z,v,hv,heq,hz,hfloor⟩ := hS w
      have hqeq : integralOrbitProjection H w=fordOrbitChart H r ⟨(z,v),hv⟩ := by
        rw [←integralOrbitProjection_eq H h w,heq]
        rfl
      change integralOrbitProjection H w∈_
      rw [hqeq]
      by_cases hT : v≤T
      · apply Or.inl
        apply Set.mem_iUnion.mpr
        refine ⟨r,Set.mem_iUnion.mpr ⟨hr,?_⟩⟩
        exact ⟨⟨(z,v),mem_truncatedFordBox z v T hz hfloor hT⟩,rfl⟩
      · apply Or.inr
        apply Set.mem_iUnion.mpr
        refine ⟨r,Set.mem_iUnion.mpr ⟨hr,?_⟩⟩
        exact ⟨⟨(z,v),hv⟩,⟨hz,hfloor,lt_of_not_ge hT⟩,rfl⟩
  · exact Set.subset_univ _

/-- The actual cubic kernel has a compact core and finitely many cusp tails. -/
theorem globalKubotaKernel_compact_core_cusp_cover :
    ∃S : Finset (SL(2,O)), ∀T : ℝ,
      IsCompact (compactFordCore globalKubotaKernel S T) ∧
      Set.univ=compactFordCore globalKubotaKernel S T ∪ ⋃r∈S, fordCuspTail globalKubotaKernel r T := by
  let : globalKubotaKernel.FiniteIndex := globalKubotaKernel_finiteIndex
  exact finiteIndex_compact_core_cusp_cover globalKubotaKernel


end GaloisForLFunctions.MetaplecticMobiusDescent.CubicEisenstein

#print axioms GaloisForLFunctions.MetaplecticMobiusDescent.CubicEisenstein.exists_maximal_integral_height
#print axioms GaloisForLFunctions.MetaplecticMobiusDescent.CubicEisenstein.bianchi_ford_cover
#print axioms GaloisForLFunctions.MetaplecticMobiusDescent.CubicEisenstein.bianchi_reduction_height_floor
#print axioms GaloisForLFunctions.MetaplecticMobiusDescent.CubicEisenstein.finiteIndex_compact_core_cusp_cover
#print axioms GaloisForLFunctions.MetaplecticMobiusDescent.CubicEisenstein.globalKubotaKernel_compact_core_cusp_cover
