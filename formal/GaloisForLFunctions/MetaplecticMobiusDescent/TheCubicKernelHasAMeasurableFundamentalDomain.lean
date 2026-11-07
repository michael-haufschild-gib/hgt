/-
The fundamental-domain construction is adapted from OpenAI’s formalization,
Apache-2.0. See LICENSE and NOTICE for source attribution.
-/
import GaloisForLFunctions.MetaplecticMobiusDescent.TheCubicEisensteinSeries
import Mathlib.MeasureTheory.Group.FundamentalDomain

/-!
# A measurable fundamental domain for the cubic kernel

Integral Frobenius sublevels are finite. Lexicographically ordering the
Frobenius norm and Gram entries gives a measurable minimum in every orbit.
For level-three matrices, trace divisibility by nine excludes nontrivial
unitary conjugates. This proves freeness and uniqueness of the translating
matrix, hence a fundamental domain for every Borel measure.
-/

noncomputable section
open Filter MeasureTheory
open scoped BigOperators Classical Topology MatrixGroups Matrix
namespace GaloisForLFunctions.MetaplecticMobiusDescent.CubicEisenstein
open Eisenstein CubicKubota

instance hyperbolicMeasurableSpace : MeasurableSpace HyperbolicSpace := borel HyperbolicSpace
instance hyperbolicBorelSpace : BorelSpace HyperbolicSpace := ⟨rfl⟩

lemma continuous_hyperbolic_action (g : SL(2,ℂ)) :
    Continuous (fun w : HyperbolicSpace => g • w) := by
  apply (QuotientGroup.isQuotientMap_mk compactSubgroup).continuous_iff.mpr
  exact continuous_hyperbolicProjection.comp (continuous_complexSL_mul g)

/-- The positive Hermitian Gram matrix determines a point of `SL₂(ℂ)/SU₂`. -/
lemma hyperbolicGram_injective : Function.Injective hyperbolicGram := by
  intro w w' hw
  induction w using Quotient.inductionOn with | _ g =>
    induction w' using Quotient.inductionOn with | _ h =>
      change matrixGram g=matrixGram h at hw
      apply Quotient.sound
      apply QuotientGroup.leftRel_apply.mpr
      change (g⁻¹*h:SL(2,ℂ))∈compactSubgroup
      apply Matrix.mem_unitaryGroup_iff.mpr
      have hgi : ((g⁻¹:SL(2,ℂ)):Matrix (Fin 2) (Fin 2) ℂ)*
          (g:Matrix (Fin 2) (Fin 2) ℂ)=1 :=
        congrArg (fun x : SL(2,ℂ) => (x:Matrix (Fin 2) (Fin 2) ℂ)) (inv_mul_cancel g)
      have hgis : star (g:Matrix (Fin 2) (Fin 2) ℂ)*
          star ((g⁻¹:SL(2,ℂ)):Matrix (Fin 2) (Fin 2) ℂ)=1 := by
        simpa only [star_mul,star_one] using congrArg star hgi
      simp only [Matrix.SpecialLinearGroup.coe_mul,star_mul]
      calc
        _ = ((g⁻¹:SL(2,ℂ)):Matrix (Fin 2) (Fin 2) ℂ)*matrixGram h*
            star ((g⁻¹:SL(2,ℂ)):Matrix (Fin 2) (Fin 2) ℂ) := by unfold matrixGram; noncomm_ring
        _ = ((g⁻¹:SL(2,ℂ)):Matrix (Fin 2) (Fin 2) ℂ)*matrixGram g*
            star ((g⁻¹:SL(2,ℂ)):Matrix (Fin 2) (Fin 2) ℂ) := by rw [hw]
        _ = (((g⁻¹:SL(2,ℂ)):Matrix (Fin 2) (Fin 2) ℂ)*(g:Matrix (Fin 2) (Fin 2) ℂ))*
            (star (g:Matrix (Fin 2) (Fin 2) ℂ)*star ((g⁻¹:SL(2,ℂ)):Matrix (Fin 2) (Fin 2) ℂ)) := by
          unfold matrixGram
          noncomm_ring
        _ = 1 := by rw [hgi,hgis]; simp

def complexMatrixRow (g : SL(2,ℂ)) (i : Fin 2) : Fin 2 → ℂ := fun j => g i j

lemma complexMatrixRow_mul (g h : SL(2,ℂ)) (i : Fin 2) :
    complexMatrixRow (g*h) i=rowOperator h (complexMatrixRow g i) := by
  funext j
  simp only [complexMatrixRow,rowOperator_apply,Matrix.SpecialLinearGroup.coe_mul,
    Matrix.mul_apply,Matrix.vecMul,dotProduct]

def matrixFrobenius (g : SL(2,ℂ)) : ℝ :=
  rowEnergy (complexMatrixRow g 0)+rowEnergy (complexMatrixRow g 1)

lemma matrixFrobenius_right_unitary (g k : SL(2,ℂ)) (hk : k∈compactSubgroup) :
    matrixFrobenius (g*k)=matrixFrobenius g := by
  simp only [matrixFrobenius,complexMatrixRow_mul,rowEnergy_unitary k hk]

/-- Sum of squared matrix-entry norms, independent of the unitary representative. -/
def hyperbolicFrobenius : HyperbolicSpace → ℝ :=
  Quotient.lift matrixFrobenius (by
    intro g h hgh
    have hk : g⁻¹*h∈compactSubgroup := QuotientGroup.leftRel_apply.mp hgh
    have hh : h=g*(g⁻¹*h) := by group
    rw [hh]
    exact (matrixFrobenius_right_unitary g (g⁻¹*h) hk).symm)

lemma matrixFrobenius_continuous : Continuous matrixFrobenius := by
  have he (i j : Fin 2) : Continuous (fun g : SL(2,ℂ) => g i j) :=
    (continuous_apply j).comp ((continuous_apply i).comp continuous_complexSL_coe)
  unfold matrixFrobenius rowEnergy complexMatrixRow
  exact ((he 0 0).norm.pow 2 |>.add ((he 0 1).norm.pow 2)).add
    ((he 1 0).norm.pow 2 |>.add ((he 1 1).norm.pow 2))

lemma hyperbolicFrobenius_continuous : Continuous hyperbolicFrobenius :=
  matrixFrobenius_continuous.quotient_lift _

def integralRowPair (M : SL(2,O)) : (Fin 2 → O)×(Fin 2 → O) :=
  (fun j => M 0 j,fun j => M 1 j)

lemma integralRowPair_injective : Function.Injective integralRowPair := by
  intro M N h
  apply Subtype.ext
  funext i j
  fin_cases i
  · exact congrFun (congrArg Prod.fst h) j
  · exact congrFun (congrArg Prod.snd h) j

lemma matrixFrobenius_integral (M : SL(2,O)) (g : SL(2,ℂ)) :
    matrixFrobenius (integralComplexMatrix M*g)=
      integralRowEnergy g (integralRowPair M).1+integralRowEnergy g (integralRowPair M).2 := by
  rw [matrixFrobenius,complexMatrixRow_mul,complexMatrixRow_mul]
  rfl

lemma integralRowEnergy_nonneg (g : SL(2,ℂ)) (v : Fin 2 → O) : 0 ≤ integralRowEnergy g v := by
  unfold integralRowEnergy rowEnergy
  positivity

/-- Bounded transformed matrix energy bounds every integral coordinate. -/
theorem integral_frobenius_sublevel_finite (g : SL(2,ℂ)) (C : ℝ) :
    Set.Finite {M : SL(2,O) | matrixFrobenius (integralComplexMatrix M*g)≤C} := by
  have hs := integralRowEnergy_sublevel_finite g C
  apply (Set.Finite.preimage integralRowPair_injective.injOn (hs.prod hs)).subset
  intro M hM
  change integralRowEnergy g (integralRowPair M).1≤C ∧ integralRowEnergy g (integralRowPair M).2≤C
  change matrixFrobenius (integralComplexMatrix M*g)≤C at hM
  rw [matrixFrobenius_integral] at hM
  exact ⟨by linarith [integralRowEnergy_nonneg g (integralRowPair M).2],
    by linarith [integralRowEnergy_nonneg g (integralRowPair M).1]⟩

theorem integral_hyperbolic_sublevel_finite (w : HyperbolicSpace) (C : ℝ) :
    Set.Finite {M : SL(2,O) | hyperbolicFrobenius (integralComplexMatrix M • w)≤C} := by
  induction w using Quotient.inductionOn with | _ g =>
    exact integral_frobenius_sublevel_finite g C

theorem subgroup_hyperbolic_sublevel_finite (H : Subgroup (SL(2,O)))
    (w : HyperbolicSpace) (C : ℝ) :
    Set.Finite {M : H | hyperbolicFrobenius (integralComplexMatrix (M:SL(2,O)) • w)≤C} := by
  exact Set.Finite.preimage Subtype.val_injective.injOn (integral_hyperbolic_sublevel_finite w C)

theorem subgroup_orbit_minimum (H : Subgroup (SL(2,O))) (w : HyperbolicSpace) :
    ∃M : H,∀N : H,
      hyperbolicFrobenius (integralComplexMatrix (M:SL(2,O)) • w)≤
        hyperbolicFrobenius (integralComplexMatrix (N:SL(2,O)) • w) := by
  let S : Set H := {M | hyperbolicFrobenius (integralComplexMatrix (M:SL(2,O)) • w)≤hyperbolicFrobenius w}
  have hs : Set.Finite S := subgroup_hyperbolic_sublevel_finite H w _
  have hne : S.Nonempty := ⟨1,by simp [S]⟩
  obtain ⟨M,hM,hmin⟩ := Set.exists_min_image S
    (fun M : H => hyperbolicFrobenius (integralComplexMatrix (M:SL(2,O)) • w)) hs hne
  refine ⟨M,fun N => ?_⟩
  by_cases hN : N∈S
  · exact hmin N hN
  · exact hM.trans (le_of_lt (lt_of_not_ge hN))


lemma one_le_normSq_embedding (a : O) (ha : a≠0) : 1≤Complex.normSq (ringComplex a) := by
  have hp := Coordinates.coordinate_norm_pos (Coordinates.coords a).1 (Coordinates.coords a).2
    (by rwa [Coordinates.eval_coords])
  have hh : 1≤(Coordinates.coords a).1^2-(Coordinates.coords a).1*(Coordinates.coords a).2+
      (Coordinates.coords a).2^2 := by omega
  rw [Complex.normSq_eq_norm_sq,←Coordinates.eval_coords a,Coordinates.complex_norm_eval_sq]
  exact_mod_cast hh

lemma integralComplexMatrix_levelThree (M : levelThree) :
    integralComplexMatrix (M:SL(2,O))=complexMatrix M := rfl

lemma integralComplexMatrix_injective : Function.Injective integralComplexMatrix := by
  intro M N h
  apply Subtype.ext
  funext i j
  apply ringComplex_injective
  exact congrArg (fun A : SL(2,ℂ) => A i j) h

/-- The determinant relation upgrades trace congruence from three to nine. -/
lemma levelThree_trace_divisible_nine (M : levelThree) :
    (9:O)∣((M:SL(2,O)) 0 0+(M:SL(2,O)) 1 1-2) := by
  have ha : (3:O)∣((M:SL(2,O)) 0 0-1) := by simpa using levelThree_entry M 0 0
  have hd : (3:O)∣((M:SL(2,O)) 1 1-1) := by simpa using levelThree_entry M 1 1
  have hb : (3:O)∣(M:SL(2,O)) 0 1 := by simpa using levelThree_entry M 0 1
  have hc : (3:O)∣(M:SL(2,O)) 1 0 := by simpa using levelThree_entry M 1 0
  have hdet : (M:SL(2,O)) 0 0*(M:SL(2,O)) 1 1-(M:SL(2,O)) 0 1*(M:SL(2,O)) 1 0=1 := by
    simpa only [Matrix.det_fin_two] using (M:SL(2,O)).property
  have he : (M:SL(2,O)) 0 0+(M:SL(2,O)) 1 1-2=
      (M:SL(2,O)) 0 1*(M:SL(2,O)) 1 0-
        ((M:SL(2,O)) 0 0-1)*((M:SL(2,O)) 1 1-1) := by linear_combination hdet
  rw [he]
  exact dvd_sub (by simpa only [show (3:O)*3=9 by ring] using mul_dvd_mul hb hc) (by simpa only [show (3:O)*3=9 by ring] using mul_dvd_mul ha hd)

lemma unitary_row_normSq (k : SL(2,ℂ)) (hk : k∈compactSubgroup) (i : Fin 2) :
    Complex.normSq (k i 0)+Complex.normSq (k i 1)=1 := by
  have hu := Matrix.mem_unitaryGroup_iff.mp hk
  have he := congrArg (fun A : Matrix (Fin 2) (Fin 2) ℂ => (A i i).re) hu
  simp only [Matrix.mul_apply,Fin.sum_univ_two,Matrix.star_apply,Matrix.one_apply_eq,
    Complex.add_re,Complex.mul_re,Complex.star_def,Complex.conj_re,Complex.conj_im,Complex.one_re] at he
  simp only [Complex.normSq_apply]
  nlinarith

lemma unitary_trace_norm_le_two (k : SL(2,ℂ)) (hk : k∈compactSubgroup) : ‖k 0 0+k 1 1‖≤2 := by
  have h0 := unitary_row_normSq k hk 0
  have h1 := unitary_row_normSq k hk 1
  have ha : ‖k 0 0‖≤1 := by
    rw [Complex.normSq_eq_norm_sq] at h0
    nlinarith [norm_nonneg (k 0 0),Complex.normSq_nonneg (k 0 1)]
  have hd : ‖k 1 1‖≤1 := by
    rw [Complex.normSq_eq_norm_sq,Complex.normSq_eq_norm_sq] at h1
    nlinarith [norm_nonneg (k 1 1),sq_nonneg ‖k 1 0‖]
  exact (norm_add_le _ _).trans (by linarith)

lemma unitary_trace_two_eq_one (k : SL(2,ℂ)) (hk : k∈compactSubgroup)
    (ht : k 0 0+k 1 1=2) : k=1 := by
  have h0 := unitary_row_normSq k hk 0
  have h1 := unitary_row_normSq k hk 1
  have htR := congrArg Complex.re ht
  norm_num [Complex.add_re] at htR
  have hs : Complex.normSq (k 0 0-1)+Complex.normSq (k 0 1)+
      Complex.normSq (k 1 0)+Complex.normSq (k 1 1-1)=0 := by
    simp only [Complex.normSq_apply,Complex.sub_re,Complex.one_re,Complex.sub_im,Complex.one_im,sub_zero] at *
    nlinarith
  have ha : k 0 0=1 := sub_eq_zero.mp (Complex.normSq_eq_zero.mp (by
    nlinarith [Complex.normSq_nonneg (k 0 0-1),Complex.normSq_nonneg (k 0 1),
      Complex.normSq_nonneg (k 1 0),Complex.normSq_nonneg (k 1 1-1)]))
  have hb : k 0 1=0 := Complex.normSq_eq_zero.mp (by
    nlinarith [Complex.normSq_nonneg (k 0 0-1),Complex.normSq_nonneg (k 0 1),
      Complex.normSq_nonneg (k 1 0),Complex.normSq_nonneg (k 1 1-1)])
  have hc : k 1 0=0 := Complex.normSq_eq_zero.mp (by
    nlinarith [Complex.normSq_nonneg (k 0 0-1),Complex.normSq_nonneg (k 0 1),
      Complex.normSq_nonneg (k 1 0),Complex.normSq_nonneg (k 1 1-1)])
  have hd : k 1 1=1 := sub_eq_zero.mp (Complex.normSq_eq_zero.mp (by
    nlinarith [Complex.normSq_nonneg (k 0 0-1),Complex.normSq_nonneg (k 0 1),
      Complex.normSq_nonneg (k 1 0),Complex.normSq_nonneg (k 1 1-1)]))
  apply Subtype.ext
  funext i j
  fin_cases i <;> fin_cases j <;> simpa using (by first | exact ha | exact hb | exact hc | exact hd)

lemma matrix_trace_conjugate (g h : SL(2,ℂ)) :
    (g⁻¹*h*g) 0 0+(g⁻¹*h*g) 1 1=h 0 0+h 1 1 := by
  have ht := Matrix.trace_mul_cycle
    (((g⁻¹:SL(2,ℂ)):Matrix (Fin 2) (Fin 2) ℂ))
    (h:Matrix (Fin 2) (Fin 2) ℂ) (g:Matrix (Fin 2) (Fin 2) ℂ)
  have hi : (g:Matrix (Fin 2) (Fin 2) ℂ)*(((g⁻¹:SL(2,ℂ)):Matrix (Fin 2) (Fin 2) ℂ))=1 :=
    congrArg (fun A : SL(2,ℂ) => (A:Matrix (Fin 2) (Fin 2) ℂ)) (mul_inv_cancel g)
  rw [hi,Matrix.one_mul] at ht
  simpa only [Matrix.SpecialLinearGroup.coe_mul,Matrix.trace,Matrix.diag_apply,Fin.sum_univ_two] using ht

/-- A unitary trace lies within four of two; a nonzero multiple of nine cannot. -/
lemma levelThree_unitary_conjugate_eq_one (M : levelThree) (g : SL(2,ℂ))
    (hk : g⁻¹*complexMatrix M*g∈compactSubgroup) : M=1 := by
  let k := g⁻¹*complexMatrix M*g
  have htr := matrix_trace_conjugate g (complexMatrix M)
  have hnorm : ‖complexMatrix M 0 0+complexMatrix M 1 1-2‖≤4 := by
    have hb := unitary_trace_norm_le_two k hk
    rw [htr] at hb
    have hn := norm_sub_le (complexMatrix M 0 0+complexMatrix M 1 1) (2:ℂ)
    norm_num at hn
    linarith
  obtain ⟨a,ha⟩ := levelThree_trace_divisible_nine M
  have hmap : complexMatrix M 0 0+complexMatrix M 1 1-2=(9:ℂ)*ringComplex a := by
    change ringComplex ((M:SL(2,O)) 0 0)+ringComplex ((M:SL(2,O)) 1 1)-2=(9:ℂ)*ringComplex a
    simpa only [map_add,map_sub,map_ofNat,map_mul] using congrArg ringComplex ha
  have haz : a=0 := by
    by_contra hne
    have hn := one_le_normSq_embedding a hne
    rw [Complex.normSq_eq_norm_sq] at hn
    have hn1 : 1≤‖ringComplex a‖ := by nlinarith [norm_nonneg (ringComplex a)]
    rw [hmap,norm_mul] at hnorm
    norm_num at hnorm
    linarith
  have ht2 : k 0 0+k 1 1=2 := by
    rw [htr]
    apply sub_eq_zero.mp
    rw [hmap,haz,map_zero,mul_zero]
  have hk1 : k=1 := unitary_trace_two_eq_one k hk ht2
  have hM1 : complexMatrix M=1 := by
    have h := congrArg (fun A : SL(2,ℂ) => g*A*g⁻¹) hk1
    simpa [k,mul_assoc] using h
  apply Subtype.ext
  apply integralComplexMatrix_injective
  simpa only [map_one,integralComplexMatrix_levelThree] using hM1

/-- No nonidentity level-three matrix fixes a hyperbolic point. -/
theorem levelThree_action_free (M : levelThree) (w : HyperbolicSpace)
    (hw : complexMatrix M • w=w) : M=1 := by
  induction w using Quotient.inductionOn with | _ g =>
    apply levelThree_unitary_conjugate_eq_one M g
    have hrel := QuotientGroup.leftRel_apply.mp (Quotient.exact' hw.symm)
    simpa only [mul_assoc,smul_eq_mul] using hrel

def hyperbolicKeyCoordinates (w : HyperbolicSpace) : Fin 9 → ℝ :=
  ![hyperbolicFrobenius w,(hyperbolicGram w 0 0).re,(hyperbolicGram w 0 0).im,
    (hyperbolicGram w 0 1).re,(hyperbolicGram w 0 1).im,
    (hyperbolicGram w 1 0).re,(hyperbolicGram w 1 0).im,
    (hyperbolicGram w 1 1).re,(hyperbolicGram w 1 1).im]

/-- Frobenius energy first; real Gram entries resolve ties. -/
def hyperbolicOrderKey (w : HyperbolicSpace) : Lex (Fin 9 → ℝ) := toLex (hyperbolicKeyCoordinates w)

lemma hyperbolicOrderKey_injective : Function.Injective hyperbolicOrderKey := by
  intro w u h
  have hc : hyperbolicKeyCoordinates w=hyperbolicKeyCoordinates u := congrArg ofLex h
  apply hyperbolicGram_injective
  funext i j
  fin_cases i <;> fin_cases j <;> apply Complex.ext
  · exact congrFun hc 1
  · exact congrFun hc 2
  · exact congrFun hc 3
  · exact congrFun hc 4
  · exact congrFun hc 5
  · exact congrFun hc 6
  · exact congrFun hc 7
  · exact congrFun hc 8

lemma hyperbolicOrderKey_lt_of_frobenius {w u : HyperbolicSpace}
    (h : hyperbolicFrobenius w<hyperbolicFrobenius u) : hyperbolicOrderKey w<hyperbolicOrderKey u := by
  refine ⟨0,?_,h⟩
  intro j hj
  exact False.elim (not_lt_of_ge (Fin.zero_le j) hj)

attribute [fun_prop] hyperbolicGram_continuous hyperbolicFrobenius_continuous

lemma hyperbolicKeyCoordinates_continuous (i : Fin 9) :
    Continuous (fun w => hyperbolicKeyCoordinates w i) := by
  fin_cases i <;> simp only [hyperbolicKeyCoordinates] <;> fun_prop

lemma hyperbolicOrderKey_lt_measurable {X : Type*} [TopologicalSpace X] [MeasurableSpace X]
    [BorelSpace X] (f g : X → HyperbolicSpace) (hf : Continuous f) (hg : Continuous g) :
    MeasurableSet {x | hyperbolicOrderKey (f x)<hyperbolicOrderKey (g x)} := by
  change MeasurableSet {x | ∃i : Fin 9,(∀j : Fin 9,j < i → hyperbolicKeyCoordinates (f x) j=hyperbolicKeyCoordinates (g x) j) ∧
    hyperbolicKeyCoordinates (f x) i<hyperbolicKeyCoordinates (g x) i}
  simp only [Set.setOf_exists,Set.setOf_and,Set.setOf_forall]
  apply MeasurableSet.iUnion
  intro i
  apply MeasurableSet.inter
  · apply MeasurableSet.iInter
    intro j
    apply MeasurableSet.iInter
    intro hj
    exact (isClosed_eq ((hyperbolicKeyCoordinates_continuous j).comp hf)
      ((hyperbolicKeyCoordinates_continuous j).comp hg)).measurableSet
  · exact measurableSet_lt ((hyperbolicKeyCoordinates_continuous i).comp hf).measurable
      ((hyperbolicKeyCoordinates_continuous i).comp hg).measurable

lemma hyperbolicOrderKey_le_measurable {X : Type*} [TopologicalSpace X] [MeasurableSpace X]
    [BorelSpace X] (f g : X → HyperbolicSpace) (hf : Continuous f) (hg : Continuous g) :
    MeasurableSet {x | hyperbolicOrderKey (f x)≤hyperbolicOrderKey (g x)} := by
  have he : {x | hyperbolicOrderKey (f x)≤hyperbolicOrderKey (g x)}=
      {x | hyperbolicOrderKey (g x)<hyperbolicOrderKey (f x)}ᶜ := by
    ext x
    change hyperbolicOrderKey (f x)≤hyperbolicOrderKey (g x) ↔ ¬hyperbolicOrderKey (g x)<hyperbolicOrderKey (f x)
    exact ⟨fun h => not_lt_of_ge h,fun h => le_of_not_gt h⟩
  rw [he]
  exact (hyperbolicOrderKey_lt_measurable g f hg hf).compl

instance integralSLCountable : Countable (SL(2,O)) := by
  let : Countable O := Coordinates.coordinateEquiv.injective.countable
  let : Countable (Matrix (Fin 2) (Fin 2) O) := inferInstanceAs (Countable (Fin 2 → Fin 2 → O))
  exact inferInstanceAs (Countable {A : Matrix (Fin 2) (Fin 2) O // A.det=1})

instance integralSubgroupHyperbolicAction (H : Subgroup (SL(2,O))) : MulAction H HyperbolicSpace :=
  MulAction.compHom HyperbolicSpace (integralComplexMatrix.comp H.subtype)

lemma integralSubgroup_smul (H : Subgroup (SL(2,O))) (M : H) (w : HyperbolicSpace) :
    M • w=integralComplexMatrix (M:SL(2,O)) • w := rfl

/-- The lexicographically least point in each integral subgroup orbit. -/
def hyperbolicFundamentalSet (H : Subgroup (SL(2,O))) : Set HyperbolicSpace :=
  {w | ∀M : H,hyperbolicOrderKey w≤hyperbolicOrderKey (M • w)}

lemma hyperbolicFundamentalSet_measurable (H : Subgroup (SL(2,O))) :
    MeasurableSet (hyperbolicFundamentalSet H) := by
  unfold hyperbolicFundamentalSet
  simp only [Set.setOf_forall]
  apply MeasurableSet.iInter
  intro M
  exact hyperbolicOrderKey_le_measurable _ _ continuous_id
    (continuous_hyperbolic_action (integralComplexMatrix (M:SL(2,O))))

lemma exists_key_orbit_minimum (H : Subgroup (SL(2,O))) (w : HyperbolicSpace) :
    ∃M : H,∀N : H,hyperbolicOrderKey (M • w)≤hyperbolicOrderKey (N • w) := by
  let S : Set H := {M | hyperbolicFrobenius (M • w)≤hyperbolicFrobenius w}
  have hs : Set.Finite S := subgroup_hyperbolic_sublevel_finite H w _
  have hne : S.Nonempty := ⟨1,by simp [S]⟩
  obtain ⟨M,hM,hmin⟩ := Set.exists_min_image S (fun M : H => hyperbolicOrderKey (M • w)) hs hne
  refine ⟨M,fun N => ?_⟩
  by_cases hN : N∈S
  · exact hmin N hN
  · apply le_of_lt
    apply hyperbolicOrderKey_lt_of_frobenius
    exact hM.trans_lt (lt_of_not_ge hN)

lemma hyperbolicFundamentalSet_covers (H : Subgroup (SL(2,O))) (w : HyperbolicSpace) :
    ∃M : H,M • w∈hyperbolicFundamentalSet H := by
  obtain ⟨M,hM⟩ := exists_key_orbit_minimum H w
  refine ⟨M,fun N => ?_⟩
  simpa only [mul_smul] using hM (N*M)

lemma hyperbolicFundamentalSet_orbit_unique (H : Subgroup (SL(2,O))) (w : HyperbolicSpace)
    (hw : w∈hyperbolicFundamentalSet H) (M : H)
    (hMw : M • w∈hyperbolicFundamentalSet H) : M • w=w := by
  apply hyperbolicOrderKey_injective
  apply le_antisymm
  · simpa only [inv_smul_smul] using hMw M⁻¹
  · exact hw M

lemma subgroup_action_free (H : Subgroup (SL(2,O))) (hH : H≤levelThree) (M : H)
    (w : HyperbolicSpace) (hM : M • w=w) : M=1 := by
  have he := levelThree_action_free (⟨(M:SL(2,O)),hH M.property⟩ : levelThree) w hM
  apply Subtype.ext
  exact congrArg (fun N : levelThree => (N:SL(2,O))) he

/-- Freeness upgrades the unique orbit representative to a unique group element. -/
theorem hyperbolicFundamentalSet_unique (H : Subgroup (SL(2,O)))
    (hH : H≤levelThree) (w : HyperbolicSpace) :
    ∃! M : H,M • w∈hyperbolicFundamentalSet H := by
  obtain ⟨M,hM⟩ := hyperbolicFundamentalSet_covers H w
  refine ⟨M,hM,fun N hN => ?_⟩
  have he : (N*M⁻¹) • (M • w)=M • w :=
    hyperbolicFundamentalSet_orbit_unique H (M • w) hM (N*M⁻¹) (by
      simpa only [mul_smul,inv_smul_smul] using hN)
  have hNM : N*M⁻¹=1 := subgroup_action_free H hH _ _ he
  exact mul_inv_eq_one.mp hNM

theorem hyperbolicFundamentalSet_isFundamentalDomain (H : Subgroup (SL(2,O)))
    (hH : H≤levelThree) (μ : Measure HyperbolicSpace) :
    IsFundamentalDomain H (hyperbolicFundamentalSet H) μ :=
  IsFundamentalDomain.mk' (hyperbolicFundamentalSet_measurable H).nullMeasurableSet
    (hyperbolicFundamentalSet_unique H hH)

lemma globalKubotaKernel_le_levelThree : globalKubotaKernel≤levelThree := by
  intro M hM
  exact ((globalKubotaKernel_mem M).mp hM).choose

/-- The actual cubic kernel has a measurable fundamental domain for any Borel measure. -/
theorem globalKubotaKernel_isFundamentalDomain (μ : Measure HyperbolicSpace) :
    IsFundamentalDomain globalKubotaKernel (hyperbolicFundamentalSet globalKubotaKernel) μ :=
  hyperbolicFundamentalSet_isFundamentalDomain _ globalKubotaKernel_le_levelThree μ


#print axioms levelThree_action_free
#print axioms integral_frobenius_sublevel_finite
#print axioms hyperbolicFundamentalSet_measurable
#print axioms hyperbolicFundamentalSet_unique
#print axioms globalKubotaKernel_isFundamentalDomain

end GaloisForLFunctions.MetaplecticMobiusDescent.CubicEisenstein
