/-
Source Mellin weights adapted from OpenAI's formalization, Apache-2.0.
See LICENSE and NOTICE in the parent directory for source attribution.
-/
import GaloisForLFunctions.MetaplecticMobiusDescent.Detector.PrincipalContours

/-!
# Source Mellin weights

The Mellin weight of the three physical scale variables, frequency weights and initial high
series on lines; full high indices and raw source indices; physical nesting of the counting
integrals.
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

open scoped Classical BigOperators Topology
open Complex Set MeasureTheory Filter
namespace ProbePrincipalRemainderBounds
open HeckeFamily ProbePhysical ProbeEuler ProbeLocal CompletedGauss
open ProbeFiniteProductBounds ProbeFiniteProductX PrincipalMellinResidues
open PrincipalMellinGrowth ProbeMellinBoundary ProbePrincipalContours
local notation "Id" => Ideal Eisenstein.O

lemma active_prime_sum_bound (T : Finset PrimeIdeal) (W : ℝ→ℝ)
    (c d B P ξ : ℝ) (hc : 0< c) (hd : c≤ d) (hB : 0≤ B) (hP : 0< P)
    (hthreshold : 480≤ c*P) (hξ : ξ≤1)
    (hW : ∀x,0≤ W x ∧ W x≤ B) (hsupp : Function.support W⊆Icc c d) :
    (∑p∈T,W ((Ideal.absNorm p.val:ℝ)/P)*(Ideal.absNorm p.val:ℝ)^(ξ-1))
      ≤(128*d*B*c^(ξ-1))*P^ξ := by
  let A := T.filter (fun p=> W ((Ideal.absNorm p.val:ℝ)/P)≠0)
  have hA (p : PrimeIdeal) (hp : p∈A) :
      c*P≤(Ideal.absNorm p.val:ℝ) ∧ (Ideal.absNorm p.val:ℝ)≤ d*P := by
    have h := hsupp (Finset.mem_filter.mp hp).2
    exact ⟨(le_div_iff₀ hP).mp h.1,(div_le_iff₀ hP).mp h.2⟩
  have he : (∑p∈T,W ((Ideal.absNorm p.val:ℝ)/P)*(Ideal.absNorm p.val:ℝ)^(ξ-1))=
      ∑p∈A,W ((Ideal.absNorm p.val:ℝ)/P)*(Ideal.absNorm p.val:ℝ)^(ξ-1) := by
    symm
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro p hp hn
    have hw : W ((Ideal.absNorm p.val:ℝ)/P)=0 := by
      by_contra hh
      exact hn (Finset.mem_filter.mpr ⟨hp,hh⟩)
    simp [hw]
  have hcount : (A.card:ℝ)≤128*(d*P) := by
    have h := EisensteinLatticeCount.finite_ideal_count_real (A.image Subtype.val) (d*P)
      (by nlinarith) (by
        intro I hI; obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hI; exact p.property.ne_zero)
      (by intro I hI; obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hI; exact (hA p hp).2)
    simpa only [Finset.card_image_of_injective _ Subtype.val_injective] using h
  have hp (p : PrimeIdeal) (hp : p∈A) : (Ideal.absNorm p.val:ℝ)^(ξ-1)≤ c^(ξ-1)*P^(ξ-1) := by
    rw [←Real.mul_rpow hc.le hP.le]
    exact Real.rpow_le_rpow_of_nonpos (mul_pos hc hP) (hA p hp).1 (by linarith)
  rw [he]
  calc
    _≤∑_p∈A,B*(c^(ξ-1)*P^(ξ-1)) := Finset.sum_le_sum (fun p hpA=>
      mul_le_mul (hW _).2 (hp p hpA) (Real.rpow_nonneg (Nat.cast_nonneg _) _) hB)
    _=(A.card:ℝ)*(B*(c^(ξ-1)*P^(ξ-1))) := by simp
    _≤(128*(d*P))*(B*(c^(ξ-1)*P^(ξ-1))) :=
      mul_le_mul_of_nonneg_right hcount (by positivity)
    _=(128*d*B*c^(ξ-1))*P^ξ := by
      have heP : P*P^(ξ-1)=P^ξ := by
        calc
          _=P^(1:ℝ)*P^(ξ-1) := by rw [Real.rpow_one]
          _=P^ξ := by rw [←Real.rpow_add hP];congr 1;ring
      calc
        _=(128*d*B*c^(ξ-1))*(P*P^(ξ-1)) := by ring
        _=_ := by rw [heP]

def slotConstant {ι : Type*} (J : Finset ι) (c d B ξ : ℝ) : ℝ :=
  (3/2)*∏_j∈J,(1+1440*(480:ℝ)^(-(7/8:ℝ)))*(128*d*B*c^(ξ-1))

lemma slotConstant_nonneg {ι : Type*} (J : Finset ι) {c d B ξ : ℝ}
    (hc : 0< c) (hd : c≤ d) (hB : 0≤ B) : 0≤ slotConstant J c d B ξ := by
  have hd0 : 0≤ d := hc.le.trans hd
  unfold slotConstant
  apply mul_nonneg (by norm_num)
  exact Finset.prod_nonneg (fun _ _=> by positivity)

theorem window_sharp_bound {ι : Type*} (η : Character) (S : Finset Id)
    (hS : CorrectionTail S) (J : Finset ι) (c d B ξ : ℝ)
    (hc : 0< c) (hd : c≤ d) (hB : 0≤ B) (hξ : ξ≤1)
    (W : ι→ℝ→ℝ) (hW : ∀j∈J,∀x,0≤ W j x ∧ W j x≤ B)
    (hsupp : ∀j∈J,Function.support (W j)⊆Icc c d)
    (P : ι→ℝ) (hP : ∀j∈J,0< P j)
    (hthreshold : ∀j∈J,480≤ c*P j)
    (hmod : ∀j∈J,(Ideal.absNorm η.modulus:ℝ)< c*P j)
    (T : ι→Finset PrimeIdeal) (s w z : ℂ)
    (hs : 7/8≤ s.re) (hw : 19/20≤ w.re) (hz : z.re=ξ) (hzlo : 33/200≤ξ) :
    ‖globalClosedCorrection η S s w z *
      windowMultiplier η J T (fun j x=>(W j x:ℂ)) P s w z‖≤
      slotConstant J c d B ξ * ∏j∈J,(P j)^ξ := by
  let A (j : ι) := (T j).filter (fun p=> W j ((Ideal.absNorm p.val:ℝ)/P j)≠0)
  have hA (j : ι) (hj : j∈J) (p : PrimeIdeal) (hp : p∈A j) : c*P j≤(Ideal.absNorm p.val:ℝ) :=
    (le_div_iff₀ (hP j hj)).mp ((hsupp j hj) (Finset.mem_filter.mp hp).2).1
  have he : windowMultiplier η J T (fun j x=>(W j x:ℂ)) P s w z =
      slotMultiplier η J A (fun j p=>(W j ((Ideal.absNorm p.val:ℝ)/P j):ℂ)) s w z := by
    unfold windowMultiplier slotMultiplier
    apply Finset.prod_congr rfl
    intro j hj
    symm
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro p hp hn
    have hh : W j ((Ideal.absNorm p.val:ℝ)/P j)=0 := by
      by_contra h; exact hn (Finset.mem_filter.mpr ⟨hp,h⟩)
    simp [hh]
  rw [he]
  have h := combined_slot_bound_sharp η S hS J A
    (fun j p=> W j ((Ideal.absNorm p.val:ℝ)/P j)) 480 (by norm_num)
    (fun j hj p _=>(hW j hj _).1)
    (fun j hj p hp=>(hthreshold j hj).trans (hA j hj p hp))
    (fun j hj p hp=> HeckeFamily.idealCoeff_norm_one_of_coprime η p.val p.property.ne_zero
      (PrincipalSignalComparison.prime_coprime_of_norm_gt η p (by
        exact_mod_cast (hmod j hj).trans_le (hA j hj p hp)))) s w z hs hw (by rw [hz];exact hzlo)
  apply h.trans
  simp only [hz]
  calc
    _≤(3/2)*∏j∈J,(1+1440*(480:ℝ)^(-(7/8:ℝ)))*((128*d*B*c^(ξ-1))*(P j)^ξ) := by
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      apply Finset.prod_le_prod
      · intro j hj; apply mul_nonneg (by positivity);exact Finset.sum_nonneg (fun p _=> by
          exact mul_nonneg (hW j hj _).1 (Real.rpow_nonneg (Nat.cast_nonneg _) _))
      · intro j hj
        exact mul_le_mul_of_nonneg_left (active_prime_sum_bound (A j) (W j) c d B (P j) ξ
          hc hd hB (hP j hj) (hthreshold j hj) hξ (hW j hj) (hsupp j hj)) (by positivity)
    _=_ := by simp only [slotConstant,←mul_assoc,Finset.prod_mul_distrib]

def scalePower (X Y Z a ξ υ : ℝ) : ℝ :=
  X^(1/2-ξ)*Z^(a+ξ-1)*Y^(υ-1)

lemma scalePower_nonneg {X Y Z a ξ υ : ℝ} (hX : 0≤ X) (hY : 0≤ Y) (hZ : 0≤ Z) :
    0≤ scalePower X Y Z a ξ υ := by unfold scalePower;positivity

section Pointwise
variable {ι : Type*} (η : Character) (S : Finset Id) (hS : SourceExclusions S)
  (J : Finset ι) (c d B ξ : ℝ) (hc : 0< c) (hd : c≤ d) (hB : 0≤ B) (hξ : ξ≤1)
  (W : ι→ℝ→ℝ) (hW : ∀j∈J,∀x,0≤ W j x ∧ W j x≤ B)
  (hsupp : ∀j∈J,Function.support (W j)⊆Icc c d)
  (P : ι→ℝ) (hP : ∀j∈J,0< P j) (hthreshold : ∀j∈J,480≤ c*P j)
  (hmod : ∀j∈J,(Ideal.absNorm η.modulus:ℝ)< c*P j) (T : ι→Finset PrimeIdeal)
  (W0 W1 : SchwartzMap ℝ ℂ) (X Y Z a υ C : ℝ) (hX : 0< X) (hY : 0< Y) (hZ : 0< Z)
  (ha : 7/8≤ a) (hυ : 19/20≤υ) (hzlo : 33/200≤ξ) (hC : 0≤ C)
  (hR : ∀s : ℂ,a≤ s.re→‖HeckeReciprocal.reciprocal (η.excludePrimes S hS.prime) s‖≤ C*(1+|s.im|^2))

include hc hd hB hξ hW hsupp hP hthreshold hmod hX hY hZ ha hυ hzlo hC hR

lemma continued_source_sharp_pointwise (t v u : ℝ) :
    ‖continuedSourceMultiplier η S hS.prime J T
      (fun j p=>(W j ((Ideal.absNorm p.val:ℝ)/P j):ℂ)) W0 W1 X Y Z
      ((a:ℂ)+t*I) ((υ:ℂ)+u*I) ((ξ:ℂ)+v*I)‖ ≤
    scalePower X Y Z a ξ υ*(C*slotConstant J c d B ξ)*(∏j∈J,(P j)^ξ)*
      jointHeight t v u^2*‖onLines W0 W1 a ξ υ ((t,v),u)‖ := by
  have hslot := window_sharp_bound η S hS.tail J c d B ξ hc hd hB hξ W hW hsupp
    P hP hthreshold hmod T ((a:ℂ)+t*I) ((υ:ℂ)+u*I) ((ξ:ℂ)+v*I)
    (by simpa using ha) (by simpa using hυ) (by simp) hzlo
  have hr : ‖HeckeReciprocal.reciprocal (η.excludePrimes S hS.prime) ((a:ℂ)+t*I)‖≤ C*jointHeight t v u^2 := by
    apply (hR _ (by simp)).trans
    simp only [add_im,ofReal_im,mul_im,ofReal_re,I_im,I_re,mul_one,mul_zero,add_zero,zero_add]
    apply mul_le_mul_of_nonneg_left _ hC
    have hh := height_le_joint_s t v u
    have hh0 := height_pos t
    unfold height jointHeight at *
    nlinarith [abs_nonneg t,abs_nonneg v,abs_nonneg u]
  have hx : ‖(X:ℂ)^(1/2-((ξ:ℂ)+v*I))‖=X^(1/2-ξ) := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hX];congr 1;simp
  have hz : ‖(Z:ℂ)^(((a:ℂ)+t*I)+((ξ:ℂ)+v*I)-1)‖=Z^(a+ξ-1) := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hZ];congr 1;simp
  have hy : ‖(Y:ℂ)^(((υ:ℂ)+u*I)-1)‖=Y^(υ-1) := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hY];congr 1;simp
  have he : continuedSourceMultiplier η S hS.prime J T
      (fun j p=>(W j ((Ideal.absNorm p.val:ℝ)/P j):ℂ)) W0 W1 X Y Z
      ((a:ℂ)+t*I) ((υ:ℂ)+u*I) ((ξ:ℂ)+v*I) =
      (X:ℂ)^(1/2-((ξ:ℂ)+v*I))*(Z:ℂ)^(((a:ℂ)+t*I)+((ξ:ℂ)+v*I)-1)*
      (Y:ℂ)^(((υ:ℂ)+u*I)-1)*HeckeReciprocal.reciprocal (η.excludePrimes S hS.prime) ((a:ℂ)+t*I)*
      (globalClosedCorrection η S ((a:ℂ)+t*I) ((υ:ℂ)+u*I) ((ξ:ℂ)+v*I)*
        windowMultiplier η J T (fun j x=>(W j x:ℂ)) P ((a:ℂ)+t*I) ((υ:ℂ)+u*I) ((ξ:ℂ)+v*I))*
      onLines W0 W1 a ξ υ ((t,v),u) := by
    unfold continuedSourceMultiplier windowMultiplier onLines profile;ring
  rw [he,norm_mul,norm_mul,norm_mul,norm_mul,norm_mul,hx,hz,hy]
  calc
    _≤ X^(1/2-ξ)*Z^(a+ξ-1)*Y^(υ-1)*(C*jointHeight t v u^2)*
      (slotConstant J c d B ξ*(∏j∈J,(P j)^ξ))*‖onLines W0 W1 a ξ υ ((t,v),u)‖ := by
      gcongr
    _=_ := by unfold scalePower;ring

lemma full_sharp_pointwise (hυhi : υ≤2) (hυ1 : υ≠1) (hξ1 : 6*ξ≠1) (p : HeightSpace) :
    ‖continuedSourceMultiplier η S hS.prime J T
      (fun j p=>(W j ((Ideal.absNorm p.val:ℝ)/P j):ℂ)) W0 W1 X Y Z
      ((a:ℂ)+p.1.1*I) ((υ:ℂ)+p.2*I) ((ξ:ℂ)+p.1.2*I)*
      LFunction (fixedSourcePrincipal S hS.prime) (6*((ξ:ℂ)+p.1.2*I))*
      LFunction (fixedSourcePrincipal S hS.prime) ((υ:ℂ)+p.2*I)‖ ≤
    (C*slotConstant J c d B ξ*(zBoxAmplitude (∏q∈S,q) 1/|6*ξ-1|)*
      (wAmplitude (∏q∈S,q) 2/|υ-1|)) *
      (scalePower X Y Z a ξ υ*(∏j∈J,(P j)^ξ))*
      (jointHeight p.1.1 p.1.2 p.2^8*‖onLines W0 W1 a ξ υ p‖) := by
  let : NeZero (∏q∈S,q) := ⟨fixedPrimeProduct_ne_zero S hS.prime⟩
  have h0 := continued_source_sharp_pointwise η S hS J c d B ξ hc hd hB hξ W hW hsupp P hP
    hthreshold hmod T W0 W1 X Y Z a υ C hX hY hZ ha hυ hzlo hC hR p.1.1 p.1.2 p.2
  have hlz := fixed_principal_z_bound (∏q∈S,q) 1 ξ p.1.2 ⟨hzlo,hξ⟩ hξ1
  have hlw := fixed_principal_w_bound (∏q∈S,q) (by norm_num : (1:ℝ)<2) ⟨hυ,hυhi⟩ hυ1 p.2
  have hAZ := div_nonneg (zBoxAmplitude_nonneg (∏q∈S,q) 1) (abs_nonneg (6*ξ-1))
  have hAW := div_nonneg (wAmplitude_pos (∏q∈S,q) (by norm_num : (1:ℝ)<2)).le (abs_nonneg (υ-1))
  have hmass : 0≤∏j∈J,(P j)^ξ := Finset.prod_nonneg (fun j hj=> Real.rpow_nonneg (hP j hj).le _)
  have hslot := slotConstant_nonneg J (ξ:=ξ) hc hd hB
  have hs := scalePower_nonneg (a:=a) (ξ:=ξ) (υ:=υ) hX.le hY.le hZ.le
  have ht := (height_pos p.1.1).le
  have hv := (height_pos p.1.2).le
  have hu := (height_pos p.2).le
  have hj := (jointHeight_pos p.1.1 p.1.2 p.2).le
  rw [norm_mul,norm_mul]
  calc
    _≤(scalePower X Y Z a ξ υ*(C*slotConstant J c d B ξ)*(∏j∈J,(P j)^ξ)*
      jointHeight p.1.1 p.1.2 p.2^2*‖onLines W0 W1 a ξ υ p‖)*
      ((zBoxAmplitude (∏q∈S,q) 1/|6*ξ-1|)*height p.1.2^3)*
      ((wAmplitude (∏q∈S,q) 2/|υ-1|)*height p.2^3) := by
      gcongr <;> first | positivity | exact h0 | exact hlz | exact hlw
    _≤(scalePower X Y Z a ξ υ*(C*slotConstant J c d B ξ)*(∏j∈J,(P j)^ξ)*
      jointHeight p.1.1 p.1.2 p.2^2*‖onLines W0 W1 a ξ υ p‖)*
      ((zBoxAmplitude (∏q∈S,q) 1/|6*ξ-1|)*jointHeight p.1.1 p.1.2 p.2^3)*
      ((wAmplitude (∏q∈S,q) 2/|υ-1|)*jointHeight p.1.1 p.1.2 p.2^3) := by
      have hs := scalePower_nonneg (a:=a) (ξ:=ξ) (υ:=υ) hX.le hY.le hZ.le
      gcongr <;> first | positivity | exact height_le_joint_z _ _ _ | exact height_le_joint_w _ _ _
    _=_ := by ring

omit hυ in
lemma residue_sharp_pointwise (hξ1 : 6*ξ≠1) (q : ℝ×ℝ) :
    ‖continuedSourceMultiplier η S hS.prime J T
      (fun j p=>(W j ((Ideal.absNorm p.val:ℝ)/P j):ℂ)) W0 W1 X Y Z
      ((a:ℂ)+q.1*I) 1 ((ξ:ℂ)+q.2*I)*
      LFunction (fixedSourcePrincipal S hS.prime) (6*((ξ:ℂ)+q.2*I))‖ ≤
    (C*slotConstant J c d B ξ*(zBoxAmplitude (∏p∈S,p) 1/|6*ξ-1|)) *
      (scalePower X Y Z a ξ 1*(∏j∈J,(P j)^ξ))*
      (jointHeight q.1 q.2 0^5*‖onLines W0 W1 a ξ 1 ((q.1,q.2),0)‖) := by
  let : NeZero (∏p∈S,p) := ⟨fixedPrimeProduct_ne_zero S hS.prime⟩
  have h0 := continued_source_sharp_pointwise η S hS J c d B ξ hc hd hB hξ W hW hsupp P hP
    hthreshold hmod T W0 W1 X Y Z a 1 C hX hY hZ ha (by norm_num) hzlo hC hR q.1 q.2 0
  simp only [ofReal_one,ofReal_zero,zero_mul,add_zero] at h0
  have hlz := fixed_principal_z_bound (∏p∈S,p) 1 ξ q.2 ⟨hzlo,hξ⟩ hξ1
  have hAZ := div_nonneg (zBoxAmplitude_nonneg (∏p∈S,p) 1) (abs_nonneg (6*ξ-1))
  have hmass : 0≤∏j∈J,(P j)^ξ := Finset.prod_nonneg (fun j hj=> Real.rpow_nonneg (hP j hj).le _)
  have hslot := slotConstant_nonneg J (ξ:=ξ) hc hd hB
  have hs := scalePower_nonneg (a:=a) (ξ:=ξ) (υ:=1) hX.le hY.le hZ.le
  have hv := (height_pos q.2).le
  rw [norm_mul]
  calc
    _≤(scalePower X Y Z a ξ 1*(C*slotConstant J c d B ξ)*(∏j∈J,(P j)^ξ)*
      jointHeight q.1 q.2 0^2*‖onLines W0 W1 a ξ 1 ((q.1,q.2),0)‖)*
      ((zBoxAmplitude (∏p∈S,p) 1/|6*ξ-1|)*height q.2^3) := by
      gcongr ; first | positivity | exact h0 | exact hlz
    _≤(scalePower X Y Z a ξ 1*(C*slotConstant J c d B ξ)*(∏j∈J,(P j)^ξ)*
      jointHeight q.1 q.2 0^2*‖onLines W0 W1 a ξ 1 ((q.1,q.2),0)‖)*
      ((zBoxAmplitude (∏p∈S,p) 1/|6*ξ-1|)*jointHeight q.1 q.2 0^3) := by
      gcongr ; first | positivity | exact height_le_joint_z _ _ _
    _=_ := by ring
end Pointwise

lemma vertical_triple_eq_joint (F : ℂ→ℂ→ℂ→ℂ) (a ξ υ : ℝ)
    (hi : Integrable (fun p : HeightSpace=> F ((a:ℂ)+p.1.1*I) ((υ:ℂ)+p.2*I)
      ((ξ:ℂ)+p.1.2*I)) heightMeasure) :
    verticalIntegral a (fun s=> verticalIntegral ξ (fun z=> verticalIntegral υ (fun w=> F s w z))) =
    (((1/(2*Real.pi):ℝ):ℂ))^3*
      ∫p : HeightSpace,F ((a:ℂ)+p.1.1*I) ((υ:ℂ)+p.2*I) ((ξ:ℂ)+p.1.2*I) ∂heightMeasure := by
  rw [integral_prod _ hi,integral_prod _ hi.integral_prod_left]
  simp only [verticalIntegral,integral_const_mul]
  ring

lemma vertical_pair_eq_joint (F : ℂ→ℂ→ℂ) (a ξ : ℝ)
    (hi : Integrable (fun q : ℝ×ℝ=> F ((a:ℂ)+q.1*I) ((ξ:ℂ)+q.2*I)) (volume.prod volume)) :
    verticalIntegral a (fun s=> verticalIntegral ξ (fun z=> F s z)) =
    (((1/(2*Real.pi):ℝ):ℂ))^2*
      ∫q : ℝ×ℝ,F ((a:ℂ)+q.1*I) ((ξ:ℂ)+q.2*I) ∂volume.prod volume := by
  rw [integral_prod _ hi]
  simp only [verticalIntegral,integral_const_mul]
  ring

lemma normalizer_norm_pos : 0<‖(((1/(2*Real.pi):ℝ):ℂ))‖ := by
  apply norm_pos_iff.mpr
  exact_mod_cast (one_div_ne_zero (mul_ne_zero (by norm_num : (2:ℝ)≠0) Real.pi_ne_zero))

section Uniform
variable {ι : Type*} (η : Character) (S : Finset Id) (hS : SourceExclusions S)
  (J : Finset ι) (c d B : ℝ) (hc : 0< c) (hd : c≤ d) (hB : 0≤ B)
  (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0< a0) (ha1 : 0< a1)
  (hW0 : Function.support W0⊆Icc a0 b0) (hW1 : Function.support W1⊆Icc a1 b1)
  (a ξ : ℝ) (ha : a∈Icc (7/8:ℝ) 2) (hβ : HeckeZeroSupremum.beta< a)
  (hξ : ξ∈Icc (33/200:ℝ) 1) (hξ1 : 6*ξ≠1)
include hc hd hB ha0 ha1 hW0 hW1 ha hβ hξ hξ1

theorem full_scale_bound (υ : ℝ) (hυ : υ∈Icc (19/20:ℝ) 2) (hυ1 : υ≠1) :
    ∃K : ℝ,0< K ∧ ∀(W : ι→ℝ→ℝ),
    (∀j∈J,∀x,0≤ W j x ∧ W j x≤ B) →
    (∀j∈J,Function.support (W j)⊆Icc c d) → ∀P : ι→ℝ,
    (∀j∈J,0< P j) → (∀j∈J,480≤ c*P j) →
    (∀j∈J,(Ideal.absNorm η.modulus:ℝ)< c*P j) → ∀T : ι→Finset PrimeIdeal,
    (∀j∈J,∀p∈T j,p.val∉S) → ∀X Y Z : ℝ,0< X→0< Y→0< Z→
    let F := fun p : HeightSpace =>
      sourceMultiplier W0 W1 X Y Z (η.excludePrimes S hS.prime) ((a:ℂ)+p.1.1*I)
        (globalClosedCorrection η S ((a:ℂ)+p.1.1*I))
        (windowMultiplier η J T (fun j x=>(W j x:ℂ)) P ((a:ℂ)+p.1.1*I))
        ((υ:ℂ)+p.2*I) ((ξ:ℂ)+p.1.2*I)*
      LFunction (fixedSourcePrincipal S hS.prime) (6*((ξ:ℂ)+p.1.2*I))*
      LFunction (fixedSourcePrincipal S hS.prime) ((υ:ℂ)+p.2*I)
    Integrable F heightMeasure ∧
      (∫p,‖F p‖ ∂heightMeasure)≤ K/(|6*ξ-1| *|υ-1|)*
        (scalePower X Y Z a ξ υ*(∏j∈J,(P j)^ξ)) := by
  let : NeZero (∏q∈S,q) := ⟨fixedPrimeProduct_ne_zero S hS.prime⟩
  obtain ⟨C,hC,hR⟩ := HeckeReciprocalGrowth.polynomial_reciprocal_bound (η.excludePrimes S hS.prime) a hβ
  obtain ⟨D,hD,hprofile⟩ := profile_uniform_moments W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
    (7/8) 2 (33/200) 1 (19/20) 2 (by norm_num) 8
  let K := C*slotConstant J c d B ξ*zBoxAmplitude (∏q∈S,q) 1*wAmplitude (∏q∈S,q) 2*D
  have hslot := slotConstant_nonneg J (ξ:=ξ) hc hd hB
  have hZA := zBoxAmplitude_nonneg (∏q∈S,q) 1
  have hWA := (wAmplitude_pos (∏q∈S,q) (by norm_num : (1:ℝ)<2)).le
  have hK : 0≤ K := by dsimp [K];positivity
  refine ⟨K+1,by positivity,?_⟩
  intro W hW hsupp P hP hthreshold hmod T hT X Y Z hX hY hZ
  dsimp only
  let b : ι→PrimeIdeal→ℂ := fun j p=>(W j ((Ideal.absNorm p.val:ℝ)/P j):ℂ)
  have hi := continued_source_joint_integrable η S hS J T b hT W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
    X Y Z a ξ υ 2 hX hY hZ ha.1 hβ hξ.1 (by norm_num) hυ hξ1 hυ1
  have hae := continued_joint_ae_raw η S hS.prime J T b W0 W1 X Y Z a ξ υ
  have hae' := (hae.mul (EventuallyEq.rfl (f:=fun p : HeightSpace=>
    LFunction (fixedSourcePrincipal S hS.prime) (6*((ξ:ℂ)+p.1.2*I))))).mul
    (EventuallyEq.rfl (f:=fun p : HeightSpace=> LFunction (fixedSourcePrincipal S hS.prime) ((υ:ℂ)+p.2*I)))
  refine ⟨hi.congr hae',?_⟩
  refine (integral_congr_ae (hae'.fun_comp norm)).symm.le.trans ?_
  let A := C*slotConstant J c d B ξ*(zBoxAmplitude (∏q∈S,q) 1/|6*ξ-1|)*(wAmplitude (∏q∈S,q) 2/|υ-1|)
  let E := scalePower X Y Z a ξ υ*(∏j∈J,(P j)^ξ)
  have hA : 0≤ A := by dsimp [A];positivity
  have hE : 0≤ E := mul_nonneg (scalePower_nonneg hX.le hY.le hZ.le)
    (Finset.prod_nonneg (fun j hj=> Real.rpow_nonneg (hP j hj).le _))
  have hp := hprofile a ha ξ hξ υ hυ
  calc
    _≤∫p : HeightSpace,A*E*(jointHeight p.1.1 p.1.2 p.2^8*‖onLines W0 W1 a ξ υ p‖) ∂heightMeasure := by
      apply integral_mono hi.norm (hp.1.const_mul (A*E))
      intro p
      exact full_sharp_pointwise η S hS J c d B ξ hc hd hB hξ.2 W hW hsupp P hP hthreshold
        hmod T W0 W1 X Y Z a υ C hX hY hZ ha.1 hυ.1 hξ.1 hC hR hυ.2 hυ1 hξ1 p
    _=A*E*(∫p : HeightSpace,jointHeight p.1.1 p.1.2 p.2^8*‖onLines W0 W1 a ξ υ p‖ ∂heightMeasure) := integral_const_mul _ _
    _≤ A*E*D := mul_le_mul_of_nonneg_left hp.2 (mul_nonneg hA hE)
    _=K/(|6*ξ-1| *|υ-1|)*E := by dsimp [A,K];simp only [div_eq_mul_inv,mul_inv_rev];ring
    _≤(K+1)/(|6*ξ-1| *|υ-1|)*E := by gcongr;linarith

theorem residue_scale_bound :
    ∃K : ℝ,0< K ∧ ∀(W : ι→ℝ→ℝ),
    (∀j∈J,∀x,0≤ W j x ∧ W j x≤ B) →
    (∀j∈J,Function.support (W j)⊆Icc c d) → ∀P : ι→ℝ,
    (∀j∈J,0< P j) → (∀j∈J,480≤ c*P j) →
    (∀j∈J,(Ideal.absNorm η.modulus:ℝ)< c*P j) → ∀T : ι→Finset PrimeIdeal,
    (∀j∈J,∀p∈T j,p.val∉S) → ∀X Y Z : ℝ,0< X→0< Y→0< Z→
    let F := fun q : ℝ×ℝ =>
      sourceMultiplier W0 W1 X Y Z (η.excludePrimes S hS.prime) ((a:ℂ)+q.1*I)
        (globalClosedCorrection η S ((a:ℂ)+q.1*I))
        (windowMultiplier η J T (fun j x=>(W j x:ℂ)) P ((a:ℂ)+q.1*I))
        1 ((ξ:ℂ)+q.2*I)*LFunction (fixedSourcePrincipal S hS.prime) (6*((ξ:ℂ)+q.2*I))
    Integrable F (volume.prod volume) ∧
      (∫q,‖F q‖ ∂volume.prod volume)≤ K/|6*ξ-1| *
        (scalePower X Y Z a ξ 1*(∏j∈J,(P j)^ξ)) := by
  let : NeZero (∏p∈S,p) := ⟨fixedPrimeProduct_ne_zero S hS.prime⟩
  obtain ⟨C,hC,hR⟩ := HeckeReciprocalGrowth.polynomial_reciprocal_bound (η.excludePrimes S hS.prime) a hβ
  obtain ⟨D,hD,hprofile⟩ := profile_uniform_slices W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
    (7/8) 2 (33/200) 1 1 1 (by norm_num) 5 0
  let K := C*slotConstant J c d B ξ*zBoxAmplitude (∏p∈S,p) 1*D
  have hslot := slotConstant_nonneg J (ξ:=ξ) hc hd hB
  have hZA := zBoxAmplitude_nonneg (∏p∈S,p) 1
  have hK : 0≤ K := by dsimp [K];positivity
  refine ⟨K+1,by positivity,?_⟩
  intro W hW hsupp P hP hthreshold hmod T hT X Y Z hX hY hZ
  dsimp only
  let b : ι→PrimeIdeal→ℂ := fun j p=>(W j ((Ideal.absNorm p.val:ℝ)/P j):ℂ)
  have hi := continued_residue_pair_integrable η S hS J T b hT W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
    X Y Z a ξ hX hZ ha.1 hβ hξ.1 hξ1
  have hae : (fun q : ℝ×ℝ => continuedSourceMultiplier η S hS.prime J T b W0 W1 X Y Z
      ((a:ℂ)+q.1*I) 1 ((ξ:ℂ)+q.2*I)*LFunction (fixedSourcePrincipal S hS.prime) (6*((ξ:ℂ)+q.2*I))) =ᵐ[volume.prod volume]
    (fun q : ℝ×ℝ => sourceMultiplier W0 W1 X Y Z (η.excludePrimes S hS.prime)
      ((a:ℂ)+q.1*I) (globalClosedCorrection η S ((a:ℂ)+q.1*I))
      (windowMultiplier η J T (fun j x=>(W j x:ℂ)) P ((a:ℂ)+q.1*I)) 1 ((ξ:ℂ)+q.2*I)*
      LFunction (fixedSourcePrincipal S hS.prime) (6*((ξ:ℂ)+q.2*I))) := by
    have hh : ∀ᵐq : ℝ×ℝ ∂volume.prod volume,q.1≠0 :=
      Measure.quasiMeasurePreserving_fst.ae (Measure.ae_ne volume (0:ℝ))
    filter_upwards [hh] with q hq
    have h0 : (a:ℂ)+q.1*I≠0 := by intro h;exact hq (by simpa using congrArg Complex.im h)
    have h1 : (a:ℂ)+q.1*I≠1 := by intro h;exact hq (by simpa using congrArg Complex.im h)
    rw [continued_source_eq_raw η S hS.prime J T b W0 W1 X Y Z _ _ _ h0 h1]
    rfl
  refine ⟨hi.congr hae,?_⟩
  refine (integral_congr_ae (hae.fun_comp norm)).symm.le.trans ?_
  let A := C*slotConstant J c d B ξ*(zBoxAmplitude (∏p∈S,p) 1/|6*ξ-1|)
  let E := scalePower X Y Z a ξ 1*(∏j∈J,(P j)^ξ)
  have hA : 0≤ A := by dsimp [A];positivity
  have hE : 0≤ E := mul_nonneg (scalePower_nonneg hX.le hY.le hZ.le)
    (Finset.prod_nonneg (fun j hj=> Real.rpow_nonneg (hP j hj).le _))
  have hp := hprofile a ha ξ hξ 1 ⟨le_rfl,le_rfl⟩ .w 0
  simp only [sliceMap,pow_zero,div_one] at hp
  calc
    _≤∫q : ℝ×ℝ,A*E*(jointHeight q.1 q.2 0^5*‖onLines W0 W1 a ξ 1 ((q.1,q.2),0)‖) ∂volume.prod volume := by
      apply integral_mono hi.norm (hp.1.const_mul (A*E))
      intro q
      exact residue_sharp_pointwise η S hS J c d B ξ hc hd hB hξ.2 W hW hsupp P hP hthreshold
        hmod T W0 W1 X Y Z a C hX hY hZ ha.1 hξ.1 hC hR hξ1 q
    _=A*E*(∫q : ℝ×ℝ,jointHeight q.1 q.2 0^5*‖onLines W0 W1 a ξ 1 ((q.1,q.2),0)‖ ∂volume.prod volume) := integral_const_mul _ _
    _≤ A*E*D := mul_le_mul_of_nonneg_left hp.2 (mul_nonneg hA hE)
    _=K/|6*ξ-1| *E := by dsimp [A,K];ring
    _≤(K+1)/|6*ξ-1| *E := by gcongr;linarith

theorem full_vertical_scale_bound (υ : ℝ) (hυ : υ∈Icc (19/20:ℝ) 2) (hυ1 : υ≠1) :
    ∃K : ℝ,0< K ∧ ∀(W : ι→ℝ→ℝ),
    (∀j∈J,∀x,0≤ W j x ∧ W j x≤ B) →
    (∀j∈J,Function.support (W j)⊆Icc c d) → ∀P : ι→ℝ,
    (∀j∈J,0< P j) → (∀j∈J,480≤ c*P j) →
    (∀j∈J,(Ideal.absNorm η.modulus:ℝ)< c*P j) → ∀T : ι→Finset PrimeIdeal,
    (∀j∈J,∀p∈T j,p.val∉S) → ∀X Y Z : ℝ,0< X→0< Y→0< Z→
    let K0 := fun s=> sourceMultiplier W0 W1 X Y Z (η.excludePrimes S hS.prime) s
      (globalClosedCorrection η S s) (windowMultiplier η J T (fun j x=>(W j x:ℂ)) P s)
    let π := fixedSourcePrincipal S hS.prime
    ‖verticalIntegral a (fun s=> verticalIntegral ξ (fun z=> verticalIntegral υ
      (fun w=> K0 s w z*LFunction π (6*z)*LFunction π w)))‖≤
      K/(|6*ξ-1| *|υ-1|)*(scalePower X Y Z a ξ υ*(∏j∈J,(P j)^ξ)) := by
  obtain ⟨K,hK,hbound⟩ := full_scale_bound η S hS J c d B hc hd hB W0 W1 a0 b0 a1 b1
    ha0 ha1 hW0 hW1 a ξ ha hβ hξ hξ1 υ hυ hυ1
  let k := ‖(((1/(2*Real.pi):ℝ):ℂ))‖^3
  have hk : 0< k := pow_pos normalizer_norm_pos _
  refine ⟨k*K,mul_pos hk hK,?_⟩
  intro W hW hsupp P hP hthreshold hmod T hT X Y Z hX hY hZ
  dsimp only
  have hh := hbound W hW hsupp P hP hthreshold hmod T hT X Y Z hX hY hZ
  dsimp only at hh
  rw [vertical_triple_eq_joint _ a ξ υ hh.1,norm_mul,norm_pow]
  calc
    _≤ k*(∫p : HeightSpace,‖sourceMultiplier W0 W1 X Y Z (η.excludePrimes S hS.prime)
        ((a:ℂ)+p.1.1*I) (globalClosedCorrection η S ((a:ℂ)+p.1.1*I))
        (windowMultiplier η J T (fun j x=>(W j x:ℂ)) P ((a:ℂ)+p.1.1*I))
        ((υ:ℂ)+p.2*I) ((ξ:ℂ)+p.1.2*I)*
      LFunction (fixedSourcePrincipal S hS.prime) (6*((ξ:ℂ)+p.1.2*I))*
      LFunction (fixedSourcePrincipal S hS.prime) ((υ:ℂ)+p.2*I)‖ ∂heightMeasure) :=
      mul_le_mul_of_nonneg_left (norm_integral_le_integral_norm _) hk.le
    _≤ k*(K/(|6*ξ-1| *|υ-1|)*(scalePower X Y Z a ξ υ*(∏j∈J,(P j)^ξ))) :=
      mul_le_mul_of_nonneg_left hh.2 hk.le
    _=_ := by ring

theorem residue_vertical_scale_bound :
    ∃K : ℝ,0< K ∧ ∀(W : ι→ℝ→ℝ),
    (∀j∈J,∀x,0≤ W j x ∧ W j x≤ B) →
    (∀j∈J,Function.support (W j)⊆Icc c d) → ∀P : ι→ℝ,
    (∀j∈J,0< P j) → (∀j∈J,480≤ c*P j) →
    (∀j∈J,(Ideal.absNorm η.modulus:ℝ)< c*P j) → ∀T : ι→Finset PrimeIdeal,
    (∀j∈J,∀p∈T j,p.val∉S) → ∀X Y Z : ℝ,0< X→0< Y→0< Z→
    let K0 := fun s=> sourceMultiplier W0 W1 X Y Z (η.excludePrimes S hS.prime) s
      (globalClosedCorrection η S s) (windowMultiplier η J T (fun j x=>(W j x:ℂ)) P s)
    let π := fixedSourcePrincipal S hS.prime
    ‖HeckeReciprocal.regularizedL π 1 * verticalIntegral a (fun s=> verticalIntegral ξ
      (fun z=> K0 s 1 z*LFunction π (6*z)))‖≤
      K/|6*ξ-1| *(scalePower X Y Z a ξ 1*(∏j∈J,(P j)^ξ)) := by
  obtain ⟨K,hK,hbound⟩ := residue_scale_bound η S hS J c d B hc hd hB W0 W1 a0 b0 a1 b1
    ha0 ha1 hW0 hW1 a ξ ha hβ hξ hξ1
  let R := HeckeReciprocal.regularizedL (fixedSourcePrincipal S hS.prime) 1
  let k := ‖(((1/(2*Real.pi):ℝ):ℂ))‖^2
  have hk : 0< k := pow_pos normalizer_norm_pos _
  refine ⟨(1+‖R‖)*k*K,by positivity,?_⟩
  intro W hW hsupp P hP hthreshold hmod T hT X Y Z hX hY hZ
  dsimp only
  have hh := hbound W hW hsupp P hP hthreshold hmod T hT X Y Z hX hY hZ
  dsimp only at hh
  rw [vertical_pair_eq_joint _ a ξ hh.1,norm_mul,norm_mul,norm_pow]
  calc
    _≤(1+‖R‖)*(k*(∫q : ℝ×ℝ,‖sourceMultiplier W0 W1 X Y Z (η.excludePrimes S hS.prime)
        ((a:ℂ)+q.1*I) (globalClosedCorrection η S ((a:ℂ)+q.1*I))
        (windowMultiplier η J T (fun j x=>(W j x:ℂ)) P ((a:ℂ)+q.1*I))
        1 ((ξ:ℂ)+q.2*I)*LFunction (fixedSourcePrincipal S hS.prime) (6*((ξ:ℂ)+q.2*I))‖ ∂volume.prod volume)) := by
      apply mul_le_mul (by dsimp [R];linarith [norm_nonneg (HeckeReciprocal.regularizedL (fixedSourcePrincipal S hS.prime) 1)])
        (mul_le_mul_of_nonneg_left (norm_integral_le_integral_norm _) hk.le) (by positivity) (by positivity)
    _≤(1+‖R‖)*(k*(K/|6*ξ-1| *(scalePower X Y Z a ξ 1*(∏j∈J,(P j)^ξ)))) := by
      gcongr;exact hh.2
    _=_ := by ring
end Uniform

theorem ordered_remainders_scale_bound {ι : Type*}
    (η : Character) (S : Finset Id) (hS : SourceExclusions S)
    (J : Finset ι) (c d B : ℝ) (hc : 0< c) (hd : c≤ d) (hB : 0≤ B)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0< a0) (ha1 : 0< a1)
    (hW0 : Function.support W0⊆Icc a0 b0) (hW1 : Function.support W1⊆Icc a1 b1)
    (a e : ℝ) (ha : a∈Icc (7/8:ℝ) 2) (hβ : HeckeZeroSupremum.beta< a)
    (he : 0< e) (hehi : e≤5/6) :
    ∃C : ℝ,0< C ∧ ∀(W : ι→ℝ→ℝ),
    (∀j∈J,∀x,0≤ W j x ∧ W j x≤ B) →
    (∀j∈J,Function.support (W j)⊆Icc c d) → ∀P : ι→ℝ,
    (∀j∈J,0< P j) → (∀j∈J,480≤ c*P j) →
    (∀j∈J,(Ideal.absNorm η.modulus:ℝ)< c*P j) → ∀T : ι→Finset PrimeIdeal,
    (∀j∈J,∀p∈T j,p.val∉S) → ∀X Y Z : ℝ,0< X→0< Y→0< Z→
    let K0 := fun s=> sourceMultiplier W0 W1 X Y Z (η.excludePrimes S hS.prime) s
      (globalClosedCorrection η S s) (windowMultiplier η J T (fun j x=>(W j x:ℂ)) P s)
    let π := fixedSourcePrincipal S hS.prime
    (‖verticalIntegral a (fun s=> verticalIntegral (1/6+e) (fun z=> verticalIntegral (19/20)
      (fun w=> K0 s w z*LFunction π (6*z)*LFunction π w)))‖≤
      C/e*(scalePower X Y Z a (1/6+e) (19/20)*(∏j∈J,(P j)^(1/6+e)))) ∧
    (‖HeckeReciprocal.regularizedL π 1 * verticalIntegral a (fun s=> verticalIntegral (33/200)
      (fun z=> K0 s 1 z*LFunction π (6*z)))‖≤
      C*(scalePower X Y Z a (33/200) 1*(∏j∈J,(P j)^(33/200:ℝ)))) := by
  obtain ⟨A,hA,hfirst⟩ := full_vertical_scale_bound η S hS J c d B hc hd hB W0 W1 a0 b0 a1 b1
    ha0 ha1 hW0 hW1 a (1/6+e) ha hβ ⟨by linarith,by linarith⟩ (by linarith)
    (19/20) (by norm_num) (by norm_num)
  obtain ⟨D,hD,hsecond⟩ := residue_vertical_scale_bound η S hS J c d B hc hd hB W0 W1 a0 b0 a1 b1
    ha0 ha1 hW0 hW1 a (33/200) ha hβ (by norm_num) (by norm_num)
  refine ⟨(10/3)*A+100*D,by positivity,?_⟩
  intro W hW hsupp P hP hthreshold hmod T hT X Y Z hX hY hZ
  dsimp only
  have hf := hfirst W hW hsupp P hP hthreshold hmod T hT X Y Z hX hY hZ
  have hg := hsecond W hW hsupp P hP hthreshold hmod T hT X Y Z hX hY hZ
  dsimp only at hf hg
  have hegap : |6*((1/6:ℝ)+e)-1|=6*e := by rw [abs_of_pos (by linarith)];ring
  rw [hegap] at hf
  norm_num only [show |(19/20:ℝ)-1|=1/20 by norm_num] at hf
  norm_num only [show |6*(33/200:ℝ)-1|=1/100 by norm_num] at hg
  have hm (ξ : ℝ) : 0≤∏j∈J,(P j)^ξ := Finset.prod_nonneg (fun j hj=> Real.rpow_nonneg (hP j hj).le _)
  constructor
  · apply hf.trans
    apply mul_le_mul_of_nonneg_right _ (mul_nonneg (scalePower_nonneg hX.le hY.le hZ.le) (hm _))
    have heq : A/(6*e*(1/20))=((10/3)*A)/e := by field_simp;ring
    rw [heq]
    apply div_le_div_of_nonneg_right _ he.le
    nlinarith
  · apply hg.trans
    apply mul_le_mul_of_nonneg_right _ (mul_nonneg (scalePower_nonneg hX.le hY.le hZ.le) (hm _))
    norm_num
    linarith

lemma source_scale_identity {ι : Type*} (J : Finset ι) (ell : ι→ℝ)
    (hell : ∑j∈J,ell j=1/6) (Z a ξ υ : ℝ) (hZ : 0< Z) :
    scalePower (Z^(17/48:ℝ)) (Z^(23/48:ℝ)) Z a ξ υ *
      (∏j∈J,(Z^(ell j))^ξ) =
    Z^(a-11/16+(13/16)*(ξ-1/6)+(23/48)*(υ-1)) := by
  have hp : (∏j∈J,(Z^(ell j))^ξ)=Z^((1/6)*ξ) := by
    simp only [←Real.rpow_mul hZ.le]
    rw [←Real.rpow_sum_of_pos hZ,←Finset.sum_mul,hell]
  rw [hp,scalePower,←Real.rpow_mul hZ.le,←Real.rpow_mul hZ.le]
  rw [←Real.rpow_add hZ,←Real.rpow_add hZ,←Real.rpow_add hZ]
  congr 1
  ring

lemma source_w_scale_identity {ι : Type*} (J : Finset ι) (ell : ι→ℝ)
    (hell : ∑j∈J,ell j=1/6) (Z a e : ℝ) (hZ : 0< Z) :
    scalePower (Z^(17/48:ℝ)) (Z^(23/48:ℝ)) Z a (1/6+e) (19/20) *
      (∏j∈J,(Z^(ell j))^(1/6+e)) = Z^(a-11/16+(13/16)*e-23/960) := by
  rw [source_scale_identity J ell hell Z a (1/6+e) (19/20) hZ]
  congr 1;ring

lemma source_z_scale_identity {ι : Type*} (J : Finset ι) (ell : ι→ℝ)
    (hell : ∑j∈J,ell j=1/6) (Z a : ℝ) (hZ : 0< Z) :
    scalePower (Z^(17/48:ℝ)) (Z^(23/48:ℝ)) Z a (33/200) 1 *
      (∏j∈J,(Z^(ell j))^(33/200:ℝ)) = Z^(a-11/16-13/9600) := by
  rw [source_scale_identity J ell hell Z a (33/200) 1 hZ]
  congr 1;ring

lemma eventual_annulus_threshold {ι : Type*} (η : Character) (J : Finset ι)
    (c : ℝ) (hc : 0< c) (ell : ι→ℝ) (hell : ∀j∈J,0< ell j) :
    ∃Z0 : ℝ,1≤ Z0 ∧ ∀Z : ℝ,Z0≤ Z→∀j∈J,
      480≤ c*Z^(ell j) ∧ (Ideal.absNorm η.modulus:ℝ)< c*Z^(ell j) := by
  have hh : ∀ᶠZ : ℝ in atTop,∀j∈J,
      480≤ c*Z^(ell j) ∧ (Ideal.absNorm η.modulus:ℝ)< c*Z^(ell j) := by
    apply (Filter.eventually_all_finset J).mpr
    intro j hj
    have ht := (tendsto_rpow_atTop (hell j hj)).const_mul_atTop hc
    exact (ht.eventually (eventually_ge_atTop 480)).and
      (ht.eventually (eventually_gt_atTop (Ideal.absNorm η.modulus:ℝ)))
  obtain ⟨Z0,hZ0⟩ := eventually_atTop.mp hh
  refine ⟨max 1 Z0,le_max_left _ _,?_⟩
  intro Z hZ
  exact hZ0 Z ((le_max_right _ _).trans hZ)

theorem source_remainders_power_bound {ι : Type*}
    (η : Character) (S : Finset Id) (hS : SourceExclusions S)
    (J : Finset ι) (c d B : ℝ) (hc : 0< c) (hd : c≤ d) (hB : 0≤ B)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0< a0) (ha1 : 0< a1)
    (hW0 : Function.support W0⊆Icc a0 b0) (hW1 : Function.support W1⊆Icc a1 b1)
    (a e : ℝ) (ha : a∈Icc (7/8:ℝ) 2) (hβ : HeckeZeroSupremum.beta< a)
    (he : 0< e) (hehi : e≤5/6) :
    ∃C : ℝ,0< C ∧ ∀(ell : ι→ℝ),(∑j∈J,ell j=1/6) → ∀(W : ι→ℝ→ℝ),
    (∀j∈J,∀x,0≤ W j x ∧ W j x≤ B) →
    (∀j∈J,Function.support (W j)⊆Icc c d) → ∀T : ι→Finset PrimeIdeal,
    (∀j∈J,∀p∈T j,p.val∉S) → ∀Z : ℝ,0< Z→
    (∀j∈J,480≤ c*Z^(ell j)) → (∀j∈J,(Ideal.absNorm η.modulus:ℝ)< c*Z^(ell j)) →
    let K0 := fun s=> sourceMultiplier W0 W1 (Z^(17/48:ℝ)) (Z^(23/48:ℝ)) Z
      (η.excludePrimes S hS.prime) s (globalClosedCorrection η S s)
      (windowMultiplier η J T (fun j x=>(W j x:ℂ)) (fun j=> Z^(ell j)) s)
    let π := fixedSourcePrincipal S hS.prime
    (‖verticalIntegral a (fun s=> verticalIntegral (1/6+e) (fun z=> verticalIntegral (19/20)
      (fun w=> K0 s w z*LFunction π (6*z)*LFunction π w)))‖≤
      C/e*Z^(a-11/16+(13/16)*e-23/960)) ∧
    (‖HeckeReciprocal.regularizedL π 1 * verticalIntegral a (fun s=> verticalIntegral (33/200)
      (fun z=> K0 s 1 z*LFunction π (6*z)))‖≤ C*Z^(a-11/16-13/9600)) := by
  obtain ⟨C,hC,hbound⟩ := ordered_remainders_scale_bound η S hS J c d B hc hd hB
    W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1 a e ha hβ he hehi
  refine ⟨C,hC,?_⟩
  intro ell hell W hW hsupp T hT Z hZ hthreshold hmod
  dsimp only
  have hh := hbound W hW hsupp (fun j=> Z^(ell j)) (fun _ _=> Real.rpow_pos_of_pos hZ _)
    hthreshold hmod T hT (Z^(17/48:ℝ)) (Z^(23/48:ℝ)) Z
    (Real.rpow_pos_of_pos hZ _) (Real.rpow_pos_of_pos hZ _) hZ
  dsimp only at hh
  rw [source_w_scale_identity J ell hell Z a e hZ,source_z_scale_identity J ell hell Z a hZ] at hh
  exact hh

lemma source_w_strict_exponent (β e : ℝ) (he : e≤1/1000) :
    (β+e)-11/16+(13/16)*e-23/960≤β-11/16-17/48000 := by linarith

lemma source_z_strict_exponent (β e : ℝ) (he : e≤1/1000) :
    (β+e)-11/16-13/9600≤β-11/16-17/48000 := by linarith

theorem source_remainders_strict_saving {ι : Type*}
    (η : Character) (S : Finset Id) (hS : SourceExclusions S)
    (J : Finset ι) (c d B : ℝ) (hc : 0< c) (hd : c≤ d) (hB : 0≤ B)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0< a0) (ha1 : 0< a1)
    (hW0 : Function.support W0⊆Icc a0 b0) (hW1 : Function.support W1⊆Icc a1 b1)
    (e : ℝ) (he : 0< e) (hehi : e≤1/1000)
    (ha : HeckeZeroSupremum.beta+e∈Icc (7/8:ℝ) 2) :
    ∃C : ℝ,0< C ∧ ∀(ell : ι→ℝ),(∑j∈J,ell j=1/6) → ∀(W : ι→ℝ→ℝ),
    (∀j∈J,∀x,0≤ W j x ∧ W j x≤ B) →
    (∀j∈J,Function.support (W j)⊆Icc c d) → ∀T : ι→Finset PrimeIdeal,
    (∀j∈J,∀p∈T j,p.val∉S) → ∀Z : ℝ,1≤ Z→
    (∀j∈J,480≤ c*Z^(ell j)) → (∀j∈J,(Ideal.absNorm η.modulus:ℝ)< c*Z^(ell j)) →
    let K0 := fun s=> sourceMultiplier W0 W1 (Z^(17/48:ℝ)) (Z^(23/48:ℝ)) Z
      (η.excludePrimes S hS.prime) s (globalClosedCorrection η S s)
      (windowMultiplier η J T (fun j x=>(W j x:ℂ)) (fun j=> Z^(ell j)) s)
    let π := fixedSourcePrincipal S hS.prime
    (‖verticalIntegral (HeckeZeroSupremum.beta+e) (fun s=> verticalIntegral (1/6+e)
      (fun z=> verticalIntegral (19/20) (fun w=> K0 s w z*LFunction π (6*z)*LFunction π w)))‖≤
      C/e*Z^(HeckeZeroSupremum.beta-11/16-17/48000)) ∧
    (‖HeckeReciprocal.regularizedL π 1 * verticalIntegral (HeckeZeroSupremum.beta+e)
      (fun s=> verticalIntegral (33/200) (fun z=> K0 s 1 z*LFunction π (6*z)))‖≤
      C*Z^(HeckeZeroSupremum.beta-11/16-17/48000)) := by
  obtain ⟨C,hC,hbound⟩ := source_remainders_power_bound η S hS J c d B hc hd hB
    W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1 (HeckeZeroSupremum.beta+e) e ha (by linarith) he (by linarith)
  refine ⟨C,hC,?_⟩
  intro ell hell W hW hsupp T hT Z hZ hthreshold hmod
  dsimp only
  have hh := hbound ell hell W hW hsupp T hT Z (by linarith) hthreshold hmod
  dsimp only at hh
  constructor
  · exact hh.1.trans (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le hZ (source_w_strict_exponent HeckeZeroSupremum.beta e hehi))
      (div_nonneg hC.le he.le))
  · exact hh.2.trans (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le hZ (source_z_strict_exponent HeckeZeroSupremum.beta e hehi)) hC.le)

end ProbePrincipalRemainderBounds

end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open MeasureTheory
namespace ProbePhysical
open SchwartzPlanePoisson

/-- Mellin weight obtained from the three physical scale variables. -/
def sourceMellinWeight (W0 W1 : SchwartzMap ℝ ℂ) (X Y Z : ℝ) (x w z : ℂ) : ℂ :=
  (X:ℂ)^(1/2-z)*(Z:ℂ)^(x+z-1)*(Y:ℂ)^(w-1)*
    Complex.exp ((x+z-1)^2)*mellin (paperRadialFourier W0) z*mellin W1 w

lemma sourceMellinWeight_marked (W0 W1 : SchwartzMap ℝ ℂ) (X Y Z Q : ℝ)
    (hZ : 0< Z) (hQ : 0< Q) (x w z : ℂ) :
    sourceMellinWeight W0 W1 X Y (Z*Q) x w z=
      (Q:ℂ)^(x+z-1)*sourceMellinWeight W0 W1 X Y Z x w z := by
  unfold sourceMellinWeight
  rw [Complex.ofReal_mul,Complex.mul_cpow_ofReal_nonneg hZ.le hQ.le]
  ring

lemma sourceMellinWeight_rescaled (W0 W1 : SchwartzMap ℝ ℂ) (X Y Z Q : ℝ)
    (hX : 0< X) (hY : 0< Y) (hQ : 0< Q) (x w z : ℂ) :
    ((Q^(-(3/2:ℝ)):ℝ):ℂ)*sourceMellinWeight W0 W1 (X/Q) (Y/Q) Z x w z=
      (Q:ℂ)^(z-w-1)*sourceMellinWeight W0 W1 X Y Z x w z := by
  have hQc : (Q:ℂ)≠0 := Complex.ofReal_ne_zero.mpr hQ.ne'
  unfold sourceMellinWeight
  rw [positive_div_cpow X Q hX.le hQ,positive_div_cpow Y Q hY.le hQ,
    Complex.ofReal_cpow hQ.le]
  simp only [div_eq_mul_inv,←Complex.cpow_neg]
  have he : (Q:ℂ)^((-(3/2:ℝ):ℝ):ℂ)*(Q:ℂ)^(-(1/2-z))*(Q:ℂ)^(-(w-1))=(Q:ℂ)^(z-w-1) := by
    rw [←Complex.cpow_add _ _ hQc,←Complex.cpow_add _ _ hQc]
    congr 1
    push_cast
    ring
  calc
    _ = ((Q:ℂ)^((-(3/2:ℝ):ℝ):ℂ)*(Q:ℂ)^(-(1/2-z))*(Q:ℂ)^(-(w-1))) *
        ((X:ℂ)^(1/2-z)*(Z:ℂ)^(x+z-1)*(Y:ℂ)^(w-1)*
        Complex.exp ((x+z-1)^2)*mellin (paperRadialFourier W0) z*mellin W1 w) := by ring_nf
    _ = _ := by rw [he]; simp only [div_eq_mul_inv]

lemma sourceMellinWeight_marked_factor (W0 W1 : SchwartzMap ℝ ℂ) (X Y Z Q : ℝ)
    (hZ : 0< Z) (hQ : 0< Q) (eta x w z : ℂ) :
    star eta*sourceMellinWeight W0 W1 X Y (Z*Q) x w z=
      (Q:ℂ)^(z-1)*(star eta*(Q:ℂ)^x)*sourceMellinWeight W0 W1 X Y Z x w z := by
  rw [sourceMellinWeight_marked W0 W1 X Y Z Q hZ hQ x w z]
  rw [show x+z-1=(z-1)+x by ring,
    Complex.cpow_add _ _ (Complex.ofReal_ne_zero.mpr hQ.ne')]
  ring

end ProbePhysical
end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical
namespace ProbePhysical
open Eisenstein CompletedGauss CanonicalRowCompletion CubicEisenstein 
local notation "O" => Eisenstein.O
local notation "Id" => Ideal O
abbrev NonzeroFrequency := {u : O // u≠0}

def frequencyWeight (z : ℂ) (u : NonzeroFrequency) : ℂ := (elementNorm u.val:ℂ)^(-z)

lemma frequencyWeight_norm (z : ℂ) (u : NonzeroFrequency) :
    ‖frequencyWeight z u‖=‖ringComplex u.val‖^(-2*z.re) := by
  have hn : 0<‖ringComplex u.val‖ := norm_pos_iff.mpr (ringComplex_ne_zero u.property)
  unfold frequencyWeight elementNorm
  have hN : (Ideal.absNorm (Ideal.span {u.val}):ℝ)=‖ringComplex u.val‖^2 :=
    (ringComplex_norm_sq_eq_absNorm_span u.val).symm
  rw [hN,
    Complex.norm_cpow_eq_rpow_re_of_pos (sq_pos_of_pos hn), Complex.neg_re,
    ← Real.rpow_natCast_mul hn.le 2]
  congr 1
  ring

theorem frequencyWeight_summable_norm (z : ℂ) (hz : 1< z.re) :
    Summable (fun u : NonzeroFrequency => ‖frequencyWeight z u‖) := by
  simp only [frequencyWeight_norm]
  exact (summable_embedding_rpow (-2*z.re) (by linarith)).subtype _

def highAbsoluteMajorant (x w z : ℂ) (p : (Id×Id)×(Id×Id)) : ℝ :=
  ‖fullIdealWeight (x-1/2) p.1.1‖ * ‖fullIdealWeight (3*x-2) p.1.2‖ *
  ‖fullIdealWeight (w-1) p.2.1‖ * ‖fullIdealWeight (6*z) p.2.2‖

lemma highAbsoluteMajorant_nonneg (x w z : ℂ) (p : (Id×Id)×(Id×Id)) :
    0≤ highAbsoluteMajorant x w z p := by unfold highAbsoluteMajorant; positivity

lemma highAbsoluteMajorant_summable (x w z : ℂ)
    (hx : 3/2< x.re) (hw : 2< w.re) (hz : 1/6< z.re) : Summable (highAbsoluteMajorant x w z) := by
  have h1 := fullIdealWeight_summable_norm (x-1/2) (by norm_num [Complex.sub_re,Complex.div_re]; linarith)
  have h2 := fullIdealWeight_summable_norm (3*x-2) (by norm_num [Complex.sub_re,Complex.mul_re]; linarith)
  have h3 := fullIdealWeight_summable_norm (w-1) (by simp only [Complex.sub_re,Complex.one_re]; linarith)
  have h4 := fullIdealWeight_summable_norm (6*z) (by norm_num [Complex.mul_re]; linarith)
  have h12 := h1.mul_of_nonneg h2 (fun _=> norm_nonneg _) (fun _=> norm_nonneg _)
  have h34 := h3.mul_of_nonneg h4 (fun _=> norm_nonneg _) (fun _=> norm_nonneg _)
  have hall := h12.mul_of_nonneg h34
    (fun _=> mul_nonneg (norm_nonneg _) (norm_nonneg _))
    (fun _=> mul_nonneg (norm_nonneg _) (norm_nonneg _))
  unfold highAbsoluteMajorant
  simpa only [mul_assoc] using hall

theorem fullHighSummand_summable (S : Finset Id) (D : Id) (η : HeckeFamily.Character)
    (x w z : ℂ) (hx : 3/2< x.re) (hw : 2< w.re) (hz : 1< z.re)
    (mask : NonzeroFrequency→ℂ) (hmask : ∀u,‖mask u‖≤1) :
    Summable (fun p : NonzeroFrequency×((Id×Id)×(Id×Id)) =>
      mask p.1 * frequencyWeight z p.1 *
        markedIdealHighSummand S D η p.1.val x w z p.2.1.1 p.2.1.2 p.2.2.1 p.2.2.2) := by
  have hm := (frequencyWeight_summable_norm z hz).mul_of_nonneg
    (highAbsoluteMajorant_summable x w z hx hw (by linarith))
    (fun _=> norm_nonneg _) (highAbsoluteMajorant_nonneg x w z)
  apply Summable.of_norm
  apply Summable.of_nonneg_of_le (fun _=> norm_nonneg _) _ hm
  intro p
  rw [norm_mul,norm_mul]
  have hcoeff := (markedIdealHighSummand_norm_le S D η p.1.val x w z
    p.2.1.1 p.2.1.2 p.2.2.1 p.2.2.2).trans
    (bareIdealHighSummand_norm_le η p.1.val x w z p.2.1.1 p.2.1.2 p.2.2.1 p.2.2.2)
  change _≤‖frequencyWeight z p.1‖*highAbsoluteMajorant x w z p.2
  calc
    _ ≤ (1*‖frequencyWeight z p.1‖)*highAbsoluteMajorant x w z p.2 := by
      apply mul_le_mul
      · exact mul_le_mul_of_nonneg_right (hmask p.1) (norm_nonneg _)
      · exact hcoeff
      · exact norm_nonneg _
      · positivity
    _ = _ := by rw [one_mul]

end ProbePhysical
end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical
open MeasureTheory
namespace ProbePhysical
open Eisenstein ProbeRow
attribute [local fun_prop] fullIdealWeight_continuous
local notation "O" => Eisenstein.O
abbrev FullHighIndex := NonzeroFrequency×((Ideal O×Ideal O)×(Ideal O×Ideal O))

/-- Product majorant separating frequency decay from the four ideal variables. -/
def initialHighMajorant (σ υ ξ : ℝ) (p : FullHighIndex) : ℝ :=
  ‖frequencyWeight (ξ:ℂ) p.1‖*highAbsoluteMajorant (σ:ℂ) (υ:ℂ) (ξ:ℂ) p.2

lemma initialHighMajorant_nonneg (σ υ ξ : ℝ) (p : FullHighIndex) :
    0≤ initialHighMajorant σ υ ξ p := mul_nonneg (norm_nonneg _) (highAbsoluteMajorant_nonneg _ _ _ _)

lemma initialHighMajorant_summable (σ υ ξ : ℝ) (hσ : 3/2<σ) (hυ : 2<υ) (hξ : 1<ξ) :
    Summable (initialHighMajorant σ υ ξ) := by
  exact (frequencyWeight_summable_norm (ξ:ℂ) hξ).mul_of_nonneg
    (highAbsoluteMajorant_summable (σ:ℂ) (υ:ℂ) (ξ:ℂ) hσ hυ (by simpa using (show (1/6:ℝ)<ξ by linarith)))
    (fun _=> norm_nonneg _) (highAbsoluteMajorant_nonneg _ _ _)

lemma frequencyWeight_norm_eq_of_re (z z' : ℂ) (h : z.re=z'.re) (H : NonzeroFrequency) :
    ‖frequencyWeight z H‖=‖frequencyWeight z' H‖ := by simp only [frequencyWeight_norm,h]

lemma highAbsoluteMajorant_eq_of_re (x w z x' w' z' : ℂ)
    (hx : x.re=x'.re) (hw : w.re=w'.re) (hz : z.re=z'.re)
    (p : (Ideal O×Ideal O)×(Ideal O×Ideal O)) :
    highAbsoluteMajorant x w z p=highAbsoluteMajorant x' w' z' p := by
  unfold highAbsoluteMajorant
  rw [fullIdealWeight_norm_eq_of_re (x-1/2) (x'-1/2) (by simp [hx]),
    fullIdealWeight_norm_eq_of_re (3*x-2) (3*x'-2) (by simp [hx]),
    fullIdealWeight_norm_eq_of_re (w-1) (w'-1) (by simp [hw]),
    fullIdealWeight_norm_eq_of_re (6*z) (6*z') (by simp [hz])]

def fullHighCoefficient (S : Finset (Ideal O)) (D : Ideal O) (η : HeckeFamily.Character)
    (mask : NonzeroFrequency→ℂ) (x w z : ℂ) (p : FullHighIndex) : ℂ :=
  mask p.1*frequencyWeight z p.1*
    markedIdealHighSummand S D η p.1.val x w z p.2.1.1 p.2.1.2 p.2.2.1 p.2.2.2

lemma fullHighCoefficient_norm_le (S : Finset (Ideal O)) (D : Ideal O) (η : HeckeFamily.Character)
    (mask : NonzeroFrequency→ℂ) (hm : ∀H,‖mask H‖≤1) (x w z : ℂ)
    (σ υ ξ : ℝ) (hx : x.re=σ) (hw : w.re=υ) (hz : z.re=ξ) (p : FullHighIndex) :
    ‖fullHighCoefficient S D η mask x w z p‖≤ initialHighMajorant σ υ ξ p := by
  unfold fullHighCoefficient
  rw [norm_mul,norm_mul]
  have hb := (markedIdealHighSummand_norm_le S D η p.1.val x w z p.2.1.1 p.2.1.2 p.2.2.1 p.2.2.2).trans
    (bareIdealHighSummand_norm_le η p.1.val x w z p.2.1.1 p.2.1.2 p.2.2.1 p.2.2.2)
  calc
    _ ≤ (1*‖frequencyWeight z p.1‖)*highAbsoluteMajorant x w z p.2 :=
      mul_le_mul (mul_le_mul_of_nonneg_right (hm _) (norm_nonneg _)) hb (norm_nonneg _) (by positivity)
    _ = initialHighMajorant σ υ ξ p := by
      rw [one_mul,frequencyWeight_norm_eq_of_re z (ξ:ℂ) hz,
        highAbsoluteMajorant_eq_of_re x w z (σ:ℂ) (υ:ℂ) (ξ:ℂ) hx hw hz]
      rfl

lemma fullHighCoefficient_continuous (S : Finset (Ideal O)) (D : Ideal O) (η : HeckeFamily.Character)
    (mask : NonzeroFrequency→ℂ) (p : FullHighIndex) :
    Continuous (fun q : (ℂ × ℂ) × ℂ => fullHighCoefficient S D η mask q.1.1 q.1.2 q.2 p) := by
  have hH : (elementNorm p.1.val:ℂ)≠0 := Complex.ofReal_ne_zero.mpr (elementNorm_pos _ p.1.property).ne'
  unfold fullHighCoefficient frequencyWeight markedIdealHighSummand bareIdealHighSummand
  have hc : Continuous (fun q : (ℂ × ℂ) × ℂ => (elementNorm p.1.val:ℂ)^(-q.2)) :=
    continuous_snd.neg.const_cpow (Or.inl hH)
  have h1 : Continuous (fun q : (ℂ × ℂ) × ℂ => fullIdealWeight (q.1.1+1/2) p.2.1.1) :=
    (fullIdealWeight_continuous _).comp (by fun_prop)
  have h2 : Continuous (fun q : (ℂ × ℂ) × ℂ => fullIdealWeight (1+3*q.1.1) p.2.1.2) :=
    (fullIdealWeight_continuous _).comp (by fun_prop)
  have h3 : Continuous (fun q : (ℂ × ℂ) × ℂ => fullIdealWeight q.1.2 p.2.2.1) :=
    (fullIdealWeight_continuous _).comp (by fun_prop)
  have h4 : Continuous (fun q : (ℂ × ℂ) × ℂ => fullIdealWeight (6*q.2) p.2.2.2) :=
    (fullIdealWeight_continuous _).comp (by fun_prop)
  exact (continuous_const.mul hc).mul
    (continuous_const.mul ((((continuous_const.mul h1).mul h2).mul h3).mul h4))

end ProbePhysical
end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical
open MeasureTheory
namespace ProbePhysical
open ProbeMellinBoundary
local notation "O" => Eisenstein.O
local instance : Countable O := Eisenstein.Coordinates.coordinateEquiv.injective.countable
local instance : Countable (Ideal O) := CubicEisenstein.cubicIdealGenerator_injective.countable

def initialHighOnLines (S : Finset (Ideal O)) (D : Ideal O) (η : HeckeFamily.Character)
    (mask : NonzeroFrequency→ℂ) (σ υ ξ : ℝ) (i : FullHighIndex) (p : HeightSpace) : ℂ :=
  fullHighCoefficient S D η mask ((σ:ℂ)+p.1.1*Complex.I)
    ((υ:ℂ)+p.2*Complex.I) ((ξ:ℂ)+p.1.2*Complex.I) i

lemma initialHighOnLines_continuous (S : Finset (Ideal O)) (D : Ideal O) (η : HeckeFamily.Character)
    (mask : NonzeroFrequency→ℂ) (σ υ ξ : ℝ) (i : FullHighIndex) :
    Continuous (initialHighOnLines S D η mask σ υ ξ i) := by
  unfold initialHighOnLines
  have hc : Continuous (fun p : HeightSpace =>
      (((σ:ℂ)+p.1.1*Complex.I,(υ:ℂ)+p.2*Complex.I),(ξ:ℂ)+p.1.2*Complex.I)) := by fun_prop
  have hh := (fullHighCoefficient_continuous S D η mask i).comp hc
  simpa only [Function.comp_def] using hh

lemma initialHighOnLines_norm_le (S : Finset (Ideal O)) (D : Ideal O) (η : HeckeFamily.Character)
    (mask : NonzeroFrequency→ℂ) (hm : ∀H,‖mask H‖≤1) (σ υ ξ : ℝ)
    (i : FullHighIndex) (p : HeightSpace) :
    ‖initialHighOnLines S D η mask σ υ ξ i p‖≤ initialHighMajorant σ υ ξ i := by
  exact fullHighCoefficient_norm_le S D η mask hm _ _ _ σ υ ξ (by simp) (by simp) (by simp) i

lemma initial_profile_integrable (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ)
    (ha0 : 0< a0) (ha1 : 0< a1) (hW0 : Function.support W0⊆Set.Icc a0 b0)
    (hW1 : Function.support W1⊆Set.Icc a1 b1) (σ ξ υ : ℝ) (hξ : 0<ξ) :
    Integrable (onLines W0 W1 σ ξ υ) heightMeasure := by
  simpa only [one_mul] using profile_arithmetic_integrable W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
    σ ξ υ hξ (fun _=>1) aestronglyMeasurable_const 1 0 (fun _=> by simp)

theorem initialHigh_integral_tsum (S : Finset (Ideal O)) (D : Ideal O) (η : HeckeFamily.Character)
    (mask : NonzeroFrequency→ℂ) (hm : ∀H,‖mask H‖≤1)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ)
    (ha0 : 0< a0) (ha1 : 0< a1) (hW0 : Function.support W0⊆Set.Icc a0 b0)
    (hW1 : Function.support W1⊆Set.Icc a1 b1)
    (σ υ ξ : ℝ) (hσ : 3/2<σ) (hυ : 2<υ) (hξ : 1<ξ) :
    (∫p,∑'i : FullHighIndex, initialHighOnLines S D η mask σ υ ξ i p*
      onLines W0 W1 σ ξ υ p ∂heightMeasure)=
      ∑'i : FullHighIndex, ∫p,initialHighOnLines S D η mask σ υ ξ i p*
        onLines W0 W1 σ ξ υ p ∂heightMeasure := by
  have hξ0 : 0<ξ := by linarith
  have hp := initial_profile_integrable W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1 σ ξ υ hξ0
  let F := fun i p=> initialHighOnLines S D η mask σ υ ξ i p*onLines W0 W1 σ ξ υ p
  have hb (i : FullHighIndex) (p : HeightSpace) :
      ‖F i p‖≤ initialHighMajorant σ υ ξ i*‖onLines W0 W1 σ ξ υ p‖ := by
    dsimp only [F]
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_right (initialHighOnLines_norm_le S D η mask hm σ υ ξ i p) (norm_nonneg _)
  have hF (i : FullHighIndex) : Integrable (F i) heightMeasure := by
    apply (hp.norm.const_mul (initialHighMajorant σ υ ξ i)).mono'
    · exact ((initialHighOnLines_continuous S D η mask σ υ ξ i).mul
        (onLines_continuous W0 W1 a1 b1 ha1 hW1 σ ξ υ hξ0)).aestronglyMeasurable
    · exact Filter.Eventually.of_forall (hb i)
  have hsum : Summable (fun i : FullHighIndex=>∫p,‖F i p‖ ∂heightMeasure) := by
    apply Summable.of_nonneg_of_le (fun i=> integral_nonneg (fun _=> norm_nonneg _))
      (fun i=>?_) ((initialHighMajorant_summable σ υ ξ hσ hυ hξ).mul_right
        (∫p,‖onLines W0 W1 σ ξ υ p‖ ∂heightMeasure))
    rw [←integral_const_mul]
    exact integral_mono (hF i).norm (hp.norm.const_mul _) (hb i)
  exact (integral_tsum_of_summable_integral_norm hF hsum).symm

theorem initialHigh_integral_tsum_test (S : Finset (Ideal O)) (D : Ideal O) (η : HeckeFamily.Character)
    (mask : NonzeroFrequency→ℂ) (hm : ∀H,‖mask H‖≤1)
    (σ υ ξ : ℝ) (hσ : 3/2<σ) (hυ : 2<υ) (hξ : 1<ξ)
    (T : HeightSpace→ℂ) (hT : Integrable T heightMeasure) :
    (∫p,∑'i : FullHighIndex, initialHighOnLines S D η mask σ υ ξ i p*T p ∂heightMeasure)=
      ∑'i : FullHighIndex, ∫p,initialHighOnLines S D η mask σ υ ξ i p*T p ∂heightMeasure := by
  let F := fun i p=> initialHighOnLines S D η mask σ υ ξ i p*T p
  have hb (i : FullHighIndex) (p : HeightSpace) :
      ‖F i p‖≤ initialHighMajorant σ υ ξ i*‖T p‖ := by
    dsimp only [F]
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_right (initialHighOnLines_norm_le S D η mask hm σ υ ξ i p) (norm_nonneg _)
  have hF (i : FullHighIndex) : Integrable (F i) heightMeasure := by
    apply (hT.norm.const_mul (initialHighMajorant σ υ ξ i)).mono'
    · exact (initialHighOnLines_continuous S D η mask σ υ ξ i).aestronglyMeasurable.mul hT.aestronglyMeasurable
    · exact Filter.Eventually.of_forall (hb i)
  have hsum : Summable (fun i : FullHighIndex=>∫p,‖F i p‖ ∂heightMeasure) := by
    apply Summable.of_nonneg_of_le (fun i=> integral_nonneg (fun _=> norm_nonneg _))
      (fun i=>?_) ((initialHighMajorant_summable σ υ ξ hσ hυ hξ).mul_right
        (∫p,‖T p‖ ∂heightMeasure))
    rw [←integral_const_mul]
    exact integral_mono (hF i).norm (hT.norm.const_mul _) (hb i)
  exact (integral_tsum_of_summable_integral_norm hF hsum).symm

end ProbePhysical
end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open MeasureTheory
namespace ProbePhysical
open ProbeMellinBoundary

def sourceScale (X Y Z : ℝ) (x w z : ℂ) : ℂ :=
  (X:ℂ)^(1/2-z)*(Z:ℂ)^(x+z-1)*(Y:ℂ)^(w-1)

lemma sourceMellinWeight_eq_scale (W0 W1 : SchwartzMap ℝ ℂ) (X Y Z : ℝ) (x w z : ℂ) :
    sourceMellinWeight W0 W1 X Y Z x w z=sourceScale X Y Z x w z*profile W0 W1 x w z := by
  unfold sourceMellinWeight sourceScale profile
  ring

lemma sourceScale_continuous (X Y Z : ℝ) (hX : 0< X) (hY : 0< Y) (hZ : 0< Z) :
    Continuous (fun q : (ℂ × ℂ) × ℂ => sourceScale X Y Z q.1.1 q.1.2 q.2) := by
  have hx : (X:ℂ)≠0 := Complex.ofReal_ne_zero.mpr hX.ne'
  have hy : (Y:ℂ)≠0 := Complex.ofReal_ne_zero.mpr hY.ne'
  have hz : (Z:ℂ)≠0 := Complex.ofReal_ne_zero.mpr hZ.ne'
  unfold sourceScale
  exact (((by fun_prop : Continuous (fun q : (ℂ × ℂ) × ℂ =>(1/2:ℂ)-q.2)).const_cpow (Or.inl hx)).mul
    (((by fun_prop : Continuous (fun q : (ℂ × ℂ) × ℂ => q.1.1+q.2-1)).const_cpow (Or.inl hz)))) |>.mul
      ((by fun_prop : Continuous (fun q : (ℂ × ℂ) × ℂ => q.1.2-1)).const_cpow (Or.inl hy))

lemma sourceScale_norm (X Y Z : ℝ) (hX : 0< X) (hY : 0< Y) (hZ : 0< Z) (x w z : ℂ) :
    ‖sourceScale X Y Z x w z‖=X^(1/2-z.re)*Z^(x.re+z.re-1)*Y^(w.re-1) := by
  simp only [sourceScale,norm_mul,Complex.norm_cpow_eq_rpow_re_of_pos hX,
    Complex.norm_cpow_eq_rpow_re_of_pos hY,Complex.norm_cpow_eq_rpow_re_of_pos hZ]
  norm_num [Complex.sub_re,Complex.add_re]

theorem sourceMellinWeight_initial_integrable (W0 W1 : SchwartzMap ℝ ℂ)
    (a0 b0 a1 b1 : ℝ) (ha0 : 0< a0) (ha1 : 0< a1)
    (hW0 : Function.support W0⊆Set.Icc a0 b0) (hW1 : Function.support W1⊆Set.Icc a1 b1)
    (X Y Z : ℝ) (hX : 0< X) (hY : 0< Y) (hZ : 0< Z)
    (σ ξ υ : ℝ) (hξ : 0<ξ) :
    Integrable (fun p : HeightSpace=> sourceMellinWeight W0 W1 X Y Z
      ((σ:ℂ)+p.1.1*Complex.I) ((υ:ℂ)+p.2*Complex.I) ((ξ:ℂ)+p.1.2*Complex.I)) heightMeasure := by
  let G := fun p : HeightSpace=> sourceScale X Y Z
    ((σ:ℂ)+p.1.1*Complex.I) ((υ:ℂ)+p.2*Complex.I) ((ξ:ℂ)+p.1.2*Complex.I)
  have hc0 := (sourceScale_continuous X Y Z hX hY hZ).comp
    (show Continuous (fun p : HeightSpace=>(((σ:ℂ)+p.1.1*Complex.I,(υ:ℂ)+p.2*Complex.I),
      (ξ:ℂ)+p.1.2*Complex.I)) by fun_prop)
  have hc : Continuous G := by simpa only [G,Function.comp_def] using hc0
  have hb (p : HeightSpace) : ‖G p‖≤(X^(1/2-ξ)*Z^(σ+ξ-1)*Y^(υ-1))*jointHeight p.1.1 p.1.2 p.2^0 := by
    simp only [G,sourceScale_norm X Y Z hX hY hZ]
    simp
  simpa only [sourceMellinWeight_eq_scale,onLines,G] using
    profile_arithmetic_integrable W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1 σ ξ υ hξ G
      hc.aestronglyMeasurable _ 0 hb

lemma sourceMellinWeight_initial_continuous (W0 W1 : SchwartzMap ℝ ℂ)
    (a1 b1 : ℝ) (ha1 : 0< a1) (hW1 : Function.support W1⊆Set.Icc a1 b1)
    (X Y Z : ℝ) (hX : 0< X) (hY : 0< Y) (hZ : 0< Z)
    (σ ξ υ : ℝ) (hξ : 0<ξ) :
    Continuous (fun p : HeightSpace=> sourceMellinWeight W0 W1 X Y Z
      ((σ:ℂ)+p.1.1*Complex.I) ((υ:ℂ)+p.2*Complex.I) ((ξ:ℂ)+p.1.2*Complex.I)) := by
  have hc := (sourceScale_continuous X Y Z hX hY hZ).comp
    (show Continuous (fun p : HeightSpace=>(((σ:ℂ)+p.1.1*Complex.I,(υ:ℂ)+p.2*Complex.I),
      (ξ:ℂ)+p.1.2*Complex.I)) by fun_prop)
  simpa only [Function.comp_def,Pi.mul_def,sourceMellinWeight_eq_scale,onLines] using
    hc.mul (onLines_continuous W0 W1 a1 b1 ha1 hW1 σ ξ υ hξ)

end ProbePhysical
end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open MeasureTheory
namespace ProbePhysical
open ProbeMellinBoundary
local notation "O" => Eisenstein.O

theorem source_initial_integral_tsum (S : Finset (Ideal O)) (D : Ideal O) (η : HeckeFamily.Character)
    (mask : NonzeroFrequency→ℂ) (hm : ∀H,‖mask H‖≤1)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ)
    (ha0 : 0< a0) (ha1 : 0< a1) (hW0 : Function.support W0⊆Set.Icc a0 b0)
    (hW1 : Function.support W1⊆Set.Icc a1 b1)
    (X Y Z : ℝ) (hX : 0< X) (hY : 0< Y) (hZ : 0< Z)
    (σ υ ξ : ℝ) (hσ : 3/2<σ) (hυ : 2<υ) (hξ : 1<ξ) :
    (∫p : HeightSpace,∑'i : FullHighIndex, initialHighOnLines S D η mask σ υ ξ i p*
      sourceMellinWeight W0 W1 X Y Z ((σ:ℂ)+p.1.1*Complex.I)
        ((υ:ℂ)+p.2*Complex.I) ((ξ:ℂ)+p.1.2*Complex.I) ∂heightMeasure)=
      ∑'i : FullHighIndex, ∫p : HeightSpace,initialHighOnLines S D η mask σ υ ξ i p*
        sourceMellinWeight W0 W1 X Y Z ((σ:ℂ)+p.1.1*Complex.I)
          ((υ:ℂ)+p.2*Complex.I) ((ξ:ℂ)+p.1.2*Complex.I) ∂heightMeasure := by
  exact initialHigh_integral_tsum_test S D η mask hm σ υ ξ hσ hυ hξ _
    (sourceMellinWeight_initial_integrable W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
      X Y Z hX hY hZ σ ξ υ (by linarith))

end ProbePhysical
end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open MeasureTheory
namespace ProbePhysical
open ProbeMellinBoundary
local notation "O" => Eisenstein.O

abbrev RawHighIndex := NonzeroFrequency×((Ideal O×Ideal O)×Ideal O)

def rawHighEmbedding (p : RawHighIndex) : FullHighIndex := (p.1,(p.2.1,(p.2.2,1)))

lemma rawHighEmbedding_injective : Function.Injective rawHighEmbedding := by
  rintro ⟨h,⟨ij,k⟩⟩ ⟨h',⟨ij',k'⟩⟩ he
  simpa only [rawHighEmbedding,Prod.mk.injEq,and_true] using he

theorem initialHigh_integral_tsum_subseries {ι : Type*} [Countable ι]
    (e : ι→FullHighIndex) (he : Function.Injective e)
    (S : Finset (Ideal O)) (D : Ideal O) (η : HeckeFamily.Character)
    (mask : NonzeroFrequency→ℂ) (hm : ∀H,‖mask H‖≤1)
    (σ υ ξ : ℝ) (hσ : 3/2<σ) (hυ : 2<υ) (hξ : 1<ξ)
    (T : HeightSpace→ℂ) (hT : Integrable T heightMeasure) :
    (∫p,∑'i : ι, initialHighOnLines S D η mask σ υ ξ (e i) p*T p ∂heightMeasure)=
      ∑'i : ι, ∫p,initialHighOnLines S D η mask σ υ ξ (e i) p*T p ∂heightMeasure := by
  let F := fun i p=> initialHighOnLines S D η mask σ υ ξ (e i) p*T p
  have hb (i : ι) (p : HeightSpace) :
      ‖F i p‖≤ initialHighMajorant σ υ ξ (e i)*‖T p‖ := by
    dsimp only [F]
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_right (initialHighOnLines_norm_le S D η mask hm σ υ ξ (e i) p) (norm_nonneg _)
  have hF (i : ι) : Integrable (F i) heightMeasure := by
    apply (hT.norm.const_mul (initialHighMajorant σ υ ξ (e i))).mono'
    · exact (initialHighOnLines_continuous S D η mask σ υ ξ (e i)).aestronglyMeasurable.mul hT.aestronglyMeasurable
    · exact Filter.Eventually.of_forall (hb i)
  have hsum : Summable (fun i : ι=>∫p,‖F i p‖ ∂heightMeasure) := by
    apply Summable.of_nonneg_of_le (fun i=> integral_nonneg (fun _=> norm_nonneg _))
      (fun i=>?_) (((initialHighMajorant_summable σ υ ξ hσ hυ hξ).comp_injective he).mul_right
        (∫p,‖T p‖ ∂heightMeasure))
    rw [←integral_const_mul]
    exact integral_mono (hF i).norm (hT.norm.const_mul _) (hb i)
  exact (integral_tsum_of_summable_integral_norm hF hsum).symm

end ProbePhysical
end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open MeasureTheory
namespace ProbePhysical
open ProbeMellinBoundary
local notation "O" => Eisenstein.O

theorem initialHigh_counting_product_integrable {ι : Type*} [Countable ι]
    [MeasurableSpace ι] [MeasurableSingletonClass ι]
    (e : ι→FullHighIndex) (he : Function.Injective e)
    (S : Finset (Ideal O)) (D : Ideal O) (η : HeckeFamily.Character)
    (mask : NonzeroFrequency→ℂ) (hm : ∀H,‖mask H‖≤1)
    (σ υ ξ : ℝ) (hσ : 3/2<σ) (hυ : 2<υ) (hξ : 1<ξ)
    (T : HeightSpace→ℂ) (hT : Integrable T heightMeasure) (hcT : Continuous T) :
    Integrable (fun p : ι×HeightSpace=> initialHighOnLines S D η mask σ υ ξ (e p.1) p.2*T p.2)
      ((Measure.count:Measure ι).prod heightMeasure) := by
  have hb : Integrable (fun i : ι=> initialHighMajorant σ υ ξ (e i)) Measure.count := by
    rw [integrable_count_iff]
    simpa only [Function.comp_def,Real.norm_eq_abs,abs_of_nonneg (initialHighMajorant_nonneg _ _ _ _)] using
      (initialHighMajorant_summable σ υ ξ hσ hυ hξ).comp_injective he
  apply (hb.mul_prod hT.norm).mono'
  · apply Measurable.aestronglyMeasurable
    apply measurable_from_prod_countable_right
    intro i
    exact ((initialHighOnLines_continuous S D η mask σ υ ξ (e i)).mul hcT).measurable
  · apply Filter.Eventually.of_forall
    intro p
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_right
      (initialHighOnLines_norm_le S D η mask hm σ υ ξ (e p.1) p.2) (norm_nonneg _)

end ProbePhysical
end

end

noncomputable section
open CubicSieve Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
namespace ProbePhysical
open Eisenstein CompletedGauss CanonicalRowCompletion CanonicalQuadraticSieve ProbeRow ProbePhase
local notation "O" => Eisenstein.O

def calibratedHighCoefficient (C : CalibrationData) (η : HeckeFamily.Character)
    (I : Ideal O) (hI : primaryIdealGenerator I≠0) (A s : O) (hA : A≠0) (H : O) : ℂ :=
  actualCongruenceCoefficient C A s hA H * idealRowHom C.generator (Ideal.span {s}) /
    ((Real.sqrt (elementNorm C.generator):ℂ)*C.tau*C.residueMonoid s) *
    gaussTwo I hI * star (CompletedGauss.angularFactor A * ProbePhase.G A) *
    targetMonoid η A * (C.Xi A)⁻¹ * reciprocitySign A s

lemma div_mul_frequency_cancel (a b c m : ℂ) (hc : c≠0) :
    c*(a/(b*c)*m)=a/b*m := by
  simp only [div_eq_mul_inv,mul_inv_rev]
  calc
    _ = (c*c⁻¹)*(a*b⁻¹*m) := by ring
    _ = _ := by rw [mul_inv_cancel₀ hc,one_mul]

theorem calibratedHighCoefficient_eq_bare (S : Finset (Ideal O)) (hS : ∀P∈S,P.IsMaximal)
    (η : HeckeFamily.Character) (I : Ideal O) (hI : primaryIdealGenerator I≠0)
    (A s : O) (hA : Supported (Ideal.span {A})) (hs : Supported (Ideal.span {s}))
    (hcop : IsCoprime (calibrationForSet S hS).generator (A*s)) (H : O) :
    calibratedHighCoefficient (calibrationForSet S hS) η I hI A s (CenteredMomentSupportedCorrelation.supported_element_ne_zero A hA) H=
      star ((calibrationForSet S hS).residueMonoid H)*
        bareSourceCoefficient η I hI A s (CenteredMomentSupportedCorrelation.supported_element_ne_zero A hA) H := by
  let C := calibrationForSet S hS
  by_cases hH : IsCoprime C.generator H
  · have hn : star (C.residueMonoid H)≠0 := by
      apply star_ne_zero.mpr
      exact C.residue.apply_ne_zero_iff.mpr ((CubicEisenstein.isUnit_quotient_span_iff C.generator H).mpr hH)
    have he := sourceHighCoefficient_eq_bare S hS η I hI A s hA hs hcop H 1 (by simpa using hH)
    simp only [one_pow,mul_one] at he
    rw [←he]
    unfold sourceHighCoefficient calibratedHighCoefficient
    simp only [one_pow,mul_one]
    symm
    convert div_mul_frequency_cancel
      (actualCongruenceCoefficient C A s (CenteredMomentSupportedCorrelation.supported_element_ne_zero A hA) H * idealRowHom C.generator (Ideal.span {s}))
      ((Real.sqrt (elementNorm C.generator):ℂ)*C.tau*C.residueMonoid s)
      (star (C.residueMonoid H))
      (gaussTwo I hI*star (CompletedGauss.angularFactor A*ProbePhase.G A)*targetMonoid η A*(C.Xi A)⁻¹*reciprocitySign A s)
      hn using 1 <;> first | rfl | (dsimp only [C]; ring)
  · have hz := actualCongruenceCoefficient_zero_off_calibration S hS A s
      (CenteredMomentSupportedCorrelation.supported_element_ne_zero A hA) (CenteredMomentSupportedCorrelation.supported_element_ne_zero s hs) hcop H hH
    have hξ : C.residueMonoid H=0 := by
      change C.residue (Ideal.Quotient.mk _ H)=0
      apply MulChar.map_nonunit
      exact fun h=> hH ((CubicEisenstein.isUnit_quotient_span_iff _ _).mp h)
    dsimp only [C] at hξ
    simp only [calibratedHighCoefficient,hz,zero_mul,zero_div,hξ,star_zero]

end ProbePhysical
end

end

noncomputable section
open CubicSieve Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
namespace ProbePhysical
open Eisenstein CompletedGauss CanonicalRowCompletion CanonicalQuadraticSieve
open ProbeCompleted ProbeRow ProbePhase  CubicEisenstein
local notation "O" => Eisenstein.O

lemma rayMask_supported (a : O) (ha : Supported (Ideal.span {a})) : ProbeCompleted.rayMask a=1 := by
  let : (Ideal.span {(2:O)}).IsMaximal := by
    simpa only [cubicTwoIdeal,Ideal.span_singleton_neg] using cubicTwoIdeal_isMaximal
  let : Field (O⧸Ideal.span {(2:O)}) := Ideal.Quotient.field _
  have h2 : IsCoprime (2:O) a := by
    apply (isUnit_quotient_span_iff _ _).mp
    apply isUnit_iff_ne_zero.mpr
    intro hz
    exact ((CanonicalQuadraticSieve.supported_span_iff a).mp ha).2
      (Ideal.mem_span_singleton.mp (Ideal.Quotient.eq_zero_iff_mem.mp hz))
  have h4 : IsCoprime (4:O) a := by
    simpa only [show (2:O)^2=4 by norm_num] using (h2.pow_left : IsCoprime ((2:O)^2) a)
  exact if_pos ((isUnit_quotient_span_iff (4:O) a).mpr h4)

lemma completedCorrection_supported (I J : Ideal O) (hI : Supported I) (hJ : Supported J) :
    completedCorrection I J=star (G (completedIndex I J)) := by
  rw [completedCorrection_eq_phase,rayMask_supported]
  · exact one_mul _
  · exact supported_completed _ _ ((supported_span_primaryIdealGenerator_iff I).mpr hI)
      ((supported_span_primaryIdealGenerator_iff J).mpr hJ)

lemma baseRowCoefficient_unit_apply (η : HeckeFamily.Character) (C : CalibrationData)
    (s : O) (hs : Supported (Ideal.span {s})) (A : O) (hA : Supported (Ideal.span {A}))
    (hcop : IsCoprime C.generator A) :
    baseRowCoefficient η C.Xi s hs A=targetMonoid η A*(C.Xi A)⁻¹*reciprocitySign A s := by
  change targetMonoid η A*star (C.Xi A)*sexticReciprocityPhase s A=_
  have hc : star (C.Xi A)=(C.Xi A)⁻¹ := (Complex.inv_eq_conj (C.Xi_norm_one A hA hcop)).symm
  rw [hc]
  congr 1
  change reciprocitySign s A = reciprocitySign A s
  exact reciprocitySign_symm s A

theorem spectralSummand_source_coefficient (S : Finset (Ideal O)) (D I J : Ideal O)
    (η : HeckeFamily.Character) (C : CalibrationData) (s : O) (hs : Supported (Ideal.span {s}))
    (hI : Supported I) (hJ : Supported J) (hsf : Squarefree I)
    (hcop : IsCoprime C.generator (completedIndex I J)) (t : ℂ) :
    spectralSummand S D (baseRowCoefficient η C.Xi s hs) t I J=
      completedMask S D I J *
        (gaussTwo I (supported_primaryIdealGenerator_ne_zero I hI)*
          star (CompletedGauss.angularFactor (completedIndex I J)*G (completedIndex I J))*
          targetMonoid η (completedIndex I J)*(C.Xi (completedIndex I J))⁻¹*
          reciprocitySign (completedIndex I J) s) /
        ((Real.sqrt (Ideal.absNorm I):ℂ)*(Ideal.absNorm J:ℂ)) *
        (fullIdealWeight t I*fullIdealWeight (3*t) J) := by
  have hA := supported_completed _ _ ((supported_span_primaryIdealGenerator_iff I).mpr hI)
    ((supported_span_primaryIdealGenerator_iff J).mpr hJ)
  have hb := baseRowCoefficient_unit_apply η C s hs (completedIndex I J) hA hcop
  have hangle : CompletedGauss.angularFactor (completedIndex I J)=
      CompletedGauss.angularFactor (primaryIdealGenerator I)*CompletedGauss.angularFactor (primaryIdealGenerator J)^3 := by
    rw [completedIndex,angularFactor_mul,show primaryIdealGenerator J^3=(primaryIdealGenerator J*primaryIdealGenerator J)*primaryIdealGenerator J by ring,
      angularFactor_mul,angularFactor_mul]
    ring
  have hm : baseRowCoefficient η C.Xi s hs (primaryIdealGenerator I)*
      baseRowCoefficient η C.Xi s hs (primaryIdealGenerator J)^3=
        targetMonoid η (completedIndex I J)*(C.Xi (completedIndex I J))⁻¹*reciprocitySign (completedIndex I J) s := by
    rw [←map_pow,←map_mul]
    exact hb
  unfold spectralSummand CompletedGauss.columnWeight
  rw [completedCorrection_supported I J hI hJ,squarefreeGaussCoefficient_eq I hsf
    (supported_primaryIdealGenerator_ne_zero I hI)]
  change _*(star (CompletedGauss.angularFactor (primaryIdealGenerator J))^3*
      baseRowCoefficient η C.Xi s hs (primaryIdealGenerator J)^3/(Ideal.absNorm J:ℂ))*_=_
  rw [hangle]
  simp only [star_mul,star_pow]
  calc
    _ = completedMask S D I J*
      (gaussTwo I (supported_primaryIdealGenerator_ne_zero I hI)*
        (star (CompletedGauss.angularFactor (primaryIdealGenerator I))*
         star (CompletedGauss.angularFactor (primaryIdealGenerator J))^3)*star (G (completedIndex I J))*
        (baseRowCoefficient η C.Xi s hs (primaryIdealGenerator I)*baseRowCoefficient η C.Xi s hs (primaryIdealGenerator J)^3)) /
      ((Real.sqrt (Ideal.absNorm I):ℂ)*(Ideal.absNorm J:ℂ))*(fullIdealWeight t I*fullIdealWeight (3*t) J) := by ring
    _ = _ := by rw [hm];ring

end ProbePhysical
end

end

noncomputable section
open CubicSieve Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
namespace ProbePhysical
open Eisenstein CompletedGauss CanonicalRowCompletion CanonicalQuadraticSieve
open ProbeCompleted ProbeRow CubicEisenstein
local notation "O" => Eisenstein.O

theorem physical_spectral_coefficient_scale (S : Finset (Ideal O)) (D I J : Ideal O)
    (η : HeckeFamily.Character) (C : CalibrationData) (s : O) (hs : Supported (Ideal.span {s}))
    (hI : Supported I) (hJ : Supported J) (hsf : Squarefree I)
    (hcop : IsCoprime C.generator (completedIndex I J)) (X : ℝ) (hX : 0< X) (t : ℂ) (H : O) :
    let A := completedIndex I J
    let hA := CenteredMomentSupportedCorrelation.supported_element_ne_zero A (supported_completed _ _
      ((supported_span_primaryIdealGenerator_iff I).mpr hI) ((supported_span_primaryIdealGenerator_iff J).mpr hJ))
    let K := elementNorm C.generator*elementNorm s*X
    idealRowHom C.generator (Ideal.span {s}) /
      (C.tau*C.residueMonoid s*(Real.sqrt K:ℂ)) * (Real.sqrt (elementNorm s):ℂ)⁻¹ *
      spectralSummand S D (baseRowCoefficient η C.Xi s hs) t I J *
      ((K/elementNorm (C.generator*A):ℝ):ℂ)*actualCongruenceCoefficient C A s hA H =
    (Real.sqrt X:ℂ) * completedMask S D I J *
      calibratedHighCoefficient C η I (supported_primaryIdealGenerator_ne_zero I hI) A s hA H /
      ((elementNorm A:ℂ)*(Real.sqrt (Ideal.absNorm I):ℂ)*(Ideal.absNorm J:ℂ)) *
      (fullIdealWeight t I*fullIdealWeight (3*t) J) := by
  dsimp only
  have hA := CenteredMomentSupportedCorrelation.supported_element_ne_zero (completedIndex I J) (supported_completed _ _
    ((supported_span_primaryIdealGenerator_iff I).mpr hI) ((supported_span_primaryIdealGenerator_iff J).mpr hJ))
  have he := physical_poisson_prefactor (elementNorm C.generator) (elementNorm (completedIndex I J))
    (elementNorm s) X (elementNorm_pos _ C.generator_ne_zero) (elementNorm_pos _ hA)
    (elementNorm_pos _ (CenteredMomentSupportedCorrelation.supported_element_ne_zero s hs)) hX
  rw [spectralSummand_source_coefficient S D I J η C s hs hI hJ hsf hcop t]
  simp only [elementNorm_mul,Complex.ofReal_div,Complex.ofReal_mul] at he ⊢
  unfold calibratedHighCoefficient
  have hh := congrArg (fun v : ℂ=> v*
    (idealRowHom C.generator (Ideal.span {s})/(C.tau*C.residueMonoid s))*
    (completedMask S D I J *
      (gaussTwo I (supported_primaryIdealGenerator_ne_zero I hI)*
        star (CompletedGauss.angularFactor (completedIndex I J)*ProbePhase.G (completedIndex I J))*
        targetMonoid η (completedIndex I J)*(C.Xi (completedIndex I J))⁻¹*
        ProbePhase.reciprocitySign (completedIndex I J) s)/
      ((Real.sqrt (Ideal.absNorm I):ℂ)*(Ideal.absNorm J:ℂ)))*
    (fullIdealWeight t I*fullIdealWeight (3*t) J)*
    actualCongruenceCoefficient C (completedIndex I J) s hA H) he
  convert hh using 1 <;> first | rfl | ring

end ProbePhysical
end

end

noncomputable section
open CubicSieve Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
namespace ProbePhysical
open ProbeEuler

lemma sourceNormPower_identity (I J H X : ℝ) (hI : 0< I) (hJ : 0< J) (hH : 0< H) (hX : 0< X)
    (t z : ℂ) :
    ((I*J^3:ℝ):ℂ)⁻¹*((X*H/(I*J^3):ℝ):ℂ)^(-z)*
      ((I:ℂ)^(-t)*(J:ℂ)^(-3*t)) /
      ((Real.sqrt I:ℂ)*(J:ℂ)) * (Real.sqrt X:ℂ) =
      (X:ℂ)^(1/2-z)*(H:ℂ)^(-z)*
        (I:ℂ)^(-(t+1-z)-1/2)*(J:ℂ)^(-(1+3*(t+1-z))) := by
  have hi : (I:ℂ)≠0 := Complex.ofReal_ne_zero.mpr hI.ne'
  have hj : (J:ℂ)≠0 := Complex.ofReal_ne_zero.mpr hJ.ne'
  have hh : (H:ℂ)≠0 := Complex.ofReal_ne_zero.mpr hH.ne'
  have hx : (X:ℂ)≠0 := Complex.ofReal_ne_zero.mpr hX.ne'
  rw [←cpow_half_eq_sqrt I hI.le,←cpow_half_eq_sqrt X hX.le]
  rw [positive_div_cpow (X*H) (I*J^3) (mul_pos hX hH).le (mul_pos hI (pow_pos hJ 3))]
  simp only [Complex.ofReal_mul,Complex.ofReal_pow]
  rw [Complex.mul_cpow_ofReal_nonneg hX.le hH.le]
  have hmul : ((I:ℂ)*(J:ℂ)^3)^(-z)=(I:ℂ)^(-z)*((J:ℂ)^3)^(-z) := by
    simpa only [Complex.ofReal_pow] using Complex.mul_cpow_ofReal_nonneg hI.le (pow_pos hJ 3).le (-z)
  rw [hmul]
  have hp : ((J:ℂ)^3)^(-z)=(J:ℂ)^((3:ℂ)*(-z)) := by
    simpa only [Real.rpow_ofNat,Real.rpow_natCast,Complex.ofReal_pow,Complex.cpow_ofNat,Complex.ofReal_ofNat] using
      (Complex.cpow_mul_ofReal_nonneg hJ.le (3:ℝ) (-z)).symm
  rw [hp]
  rw [show (J:ℂ)^3=(J:ℂ)^(3:ℂ) by simp]
  have hir : (I:ℂ)=Complex.exp (Complex.log (I:ℂ)) := (Complex.exp_log hi).symm
  have hjr : (J:ℂ)=Complex.exp (Complex.log (J:ℂ)) := (Complex.exp_log hj).symm
  simp only [Complex.cpow_def_of_ne_zero hi,Complex.cpow_def_of_ne_zero hj,
    Complex.cpow_def_of_ne_zero hh,Complex.cpow_def_of_ne_zero hx,div_eq_mul_inv,
    mul_inv_rev,←Complex.exp_neg,←Complex.exp_add]
  rw [hir,hjr]
  simp only [←Complex.exp_neg,←Complex.exp_add]
  rw [Complex.exp_log hi,Complex.exp_log hj]
  congr 1
  ring

end ProbePhysical
end

end

noncomputable section
open CubicSieve Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
namespace ProbePhysical
open Eisenstein CompletedGauss CanonicalRowCompletion CanonicalQuadraticSieve
open ProbeCompleted ProbeRow CubicEisenstein
local notation "O" => Eisenstein.O

lemma completedIndex_norm (I J : Ideal O) (hI : Supported I) (hJ : Supported J) :
    elementNorm (completedIndex I J)=(Ideal.absNorm I:ℝ)*(Ideal.absNorm J:ℝ)^3 := by
  rw [completedIndex, elementNorm_mul, elementNorm_pow]
  unfold elementNorm
  rw [(primaryIdealGenerator_spec I (supported_primaryIdealGenerator_ne_zero I hI)).1,
    (primaryIdealGenerator_spec J (supported_primaryIdealGenerator_ne_zero J hJ)).1]

theorem physical_mellin_coefficient (S : Finset (Ideal O)) (hS : ∀P∈S,P.IsMaximal)
    (D I J : Ideal O) (η : HeckeFamily.Character) (s : O) (hs : Supported (Ideal.span {s}))
    (hI : Supported I) (hJ : Supported J) (hsf : Squarefree I)
    (hcop : IsCoprime (calibrationForSet S hS).generator (completedIndex I J*s))
    (X : ℝ) (hX : 0< X) (H : O) (hH : H≠0) (t z : ℂ) :
    let C := calibrationForSet S hS
    let A := completedIndex I J
    let hA := CenteredMomentSupportedCorrelation.supported_element_ne_zero A (supported_completed _ _
      ((supported_span_primaryIdealGenerator_iff I).mpr hI) ((supported_span_primaryIdealGenerator_iff J).mpr hJ))
    let K := elementNorm C.generator*elementNorm s*X
    idealRowHom C.generator (Ideal.span {s}) /
      (C.tau*C.residueMonoid s*(Real.sqrt K:ℂ)) * (Real.sqrt (elementNorm s):ℂ)⁻¹ *
      spectralSummand S D (baseRowCoefficient η C.Xi s hs) t I J *
      ((K/elementNorm (C.generator*A):ℝ):ℂ)*actualCongruenceCoefficient C A s hA H *
      ((K*elementNorm H/elementNorm ((C.generator*A)*s)):ℂ)^(-z) =
    (X:ℂ)^(1/2-z)*(elementNorm H:ℂ)^(-z)*completedMask S D I J*star (C.residueMonoid H)*
      bareSourceCoefficient η I (supported_primaryIdealGenerator_ne_zero I hI) A s hA H *
      (fullIdealWeight (t+1-z+1/2) I*fullIdealWeight (1+3*(t+1-z)) J) := by
  dsimp only
  have hA : Supported (Ideal.span {completedIndex I J}) := supported_completed _ _ ((supported_span_primaryIdealGenerator_iff I).mpr hI)
    ((supported_span_primaryIdealGenerator_iff J).mpr hJ)
  rw [physical_spectral_coefficient_scale S D I J η (calibrationForSet S hS) s hs hI hJ hsf
    hcop.of_mul_right_left X hX t H]
  rw [calibratedHighCoefficient_eq_bare S hS η I (supported_primaryIdealGenerator_ne_zero I hI)
    (completedIndex I J) s hA hs hcop H]
  have hr := congrArg (fun r : ℝ => (r : ℂ)) (physical_radial_argument
    (calibrationForSet S hS).generator (completedIndex I J) s H X
    (elementNorm_pos _ (calibrationForSet S hS).generator_ne_zero).ne'
    (elementNorm_pos _ (CenteredMomentSupportedCorrelation.supported_element_ne_zero s hs)).ne')
  simp only [Complex.ofReal_div, Complex.ofReal_mul] at hr
  simp only [Complex.ofReal_mul]
  rw [hr]
  rw [completedIndex_norm I J hI hJ]
  have hi : (0:ℝ)< Ideal.absNorm I := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hI.1)
  have hj : (0:ℝ)< Ideal.absNorm J := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hJ.1)
  have hn := sourceNormPower_identity (Ideal.absNorm I) (Ideal.absNorm J) (elementNorm H) X
    hi hj (elementNorm_pos H hH) hX t z
  rw [show -(t+1-z)-1/2= -(t+1-z+1/2) by ring] at hn
  simp only [fullIdealWeight,hI.1,hJ.1,ite_false,Complex.ofReal_natCast,Complex.ofReal_div,Complex.ofReal_mul,Complex.ofReal_pow] at hn ⊢
  have he := congrArg (fun v : ℂ=> v*completedMask S D I J*
    star ((calibrationForSet S hS).residueMonoid H)*
    bareSourceCoefficient η I (supported_primaryIdealGenerator_ne_zero I hI) (completedIndex I J) s
      (CenteredMomentSupportedCorrelation.supported_element_ne_zero _ hA) H) hn
  convert he using 1 <;> first | rfl | ring_nf

end ProbePhysical
end

end

noncomputable section
open CubicSieve Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical BigOperators
namespace ProbePhysical
open Eisenstein CompletedGauss ProbeCompleted ProbeRow CanonicalQuadraticSieve
open SchwartzPlanePoisson
local notation "O" => Eisenstein.O
local notation "Id" => Ideal O

lemma spectralSummand_mask_nonzero (S : Finset Id) (D I J : Id) (Ψ : O→*ℂ) (t : ℂ)
    (h : spectralSummand S D Ψ t I J≠0) : completedMask S D I J≠0 := by
  intro hz
  exact h (by simp only [spectralSummand,hz,zero_mul])

lemma spectralSummand_calibration_coprime (S : Finset Id) (hS : ∀P∈S,P.IsMaximal)
    (D I J : Id) (Ψ : O→*ℂ) (t : ℂ) (h : spectralSummand S D Ψ t I J≠0) :
    IsCoprime (calibrationForSet S hS).generator (completedIndex I J) := by
  have hm := spectralSummand_mask_nonzero S D I J Ψ t h
  have hA : completedIndex I J≠0 := by
    intro hz
    exact h (spectralSummand_zero_completedIndex S D I J Ψ t hz)
  have hout : ∀P∈S,¬P∣I*J^3 := by
    unfold completedMask at hm
    split_ifs at hm with hd
    · exact hd.2
    · exact False.elim (hm rfl)
  apply calibrationForSet_coprime_of_excluded S hS
  rw [completedIndex_eq_primaryIdealGenerator] at hA ⊢
  rw [(primaryIdealGenerator_spec (I*J^3) hA).1]
  exact hout


end ProbePhysical
end

end

noncomputable section
open CubicSieve Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical
namespace ProbePhysical
open Eisenstein CompletedGauss CanonicalQuadraticSieve
open ProbeCompleted ProbeRow SecondPassArithmetic
local notation "O" => Eisenstein.O

lemma supported_of_source_exclusions (S : Finset (Ideal O))
    (hbad : fixedBadPrimes⊆S) (I : Ideal O) (hI : I≠0)
    (hS : ∀P∈S,¬P∣I) : Supported I := by
  refine ⟨hI,?_⟩
  intro P hP
  have hp : Prime P := UniqueFactorizationMonoid.prime_of_normalized_factor P hP
  let : P.IsMaximal := (Ideal.isPrime_of_prime hp).isMaximal hp.ne_zero
  apply (prime_good_iff_not_bad P).mpr
  intro hb
  exact hS P (hbad hb) (UniqueFactorizationMonoid.dvd_of_mem_normalizedFactors hP)

lemma spectralSummand_support (S : Finset (Ideal O)) (hbad : fixedBadPrimes⊆S)
    (D I J : Ideal O) (Ψ : O→*ℂ) (t : ℂ)
    (h : spectralSummand S D Ψ t I J≠0) :
    Squarefree I ∧ Supported I ∧ Supported J := by
  have hI : I≠0 := by
    intro hz
    subst I
    exact h (by simp [spectralSummand])
  have hJ : J≠0 := by
    intro hz
    subst J
    exact h (by simp [spectralSummand])
  have hsf : Squarefree I := by
    by_contra hn
    exact h (by simp [spectralSummand,columnWeight,squarefreeGaussCoefficient,hn])
  have hm := spectralSummand_mask_nonzero S D I J Ψ t h
  have hex : ∀P∈S,¬P∣I*J^3 := by
    unfold completedMask at hm
    split_ifs at hm with hd
    · exact hd.2
    · exact False.elim (hm rfl)
  refine ⟨hsf,supported_of_source_exclusions S hbad I hI ?_,
    supported_of_source_exclusions S hbad J hJ ?_⟩
  · intro P hP hd
    exact hex P hP (dvd_mul_of_dvd_left hd _)
  · intro P hP hd
    exact hex P hP (dvd_mul_of_dvd_right (hd.trans (dvd_pow_self J (by decide : 3≠0))) _)

end ProbePhysical
end

end

noncomputable section
open CubicSieve Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical
namespace ProbePhysical
open Eisenstein CompletedGauss CanonicalQuadraticSieve CanonicalRowCompletion
open ProbeCompleted ProbeRow CubicEisenstein
local notation "O" => Eisenstein.O

def physicalMellinCoefficientTerm (η : HeckeFamily.Character) (C : CalibrationData)
    (S : Finset (Ideal O)) (D I J : Ideal O) (s : O) (hs : Supported (Ideal.span {s}))
    (X : ℝ) (H : O) (t z : ℂ) : ℂ :=
  if hA : completedIndex I J≠0 then
    let K := elementNorm C.generator*elementNorm s*X
    idealRowHom C.generator (Ideal.span {s}) /
      (C.tau*C.residueMonoid s*(Real.sqrt K:ℂ)) * (Real.sqrt (elementNorm s):ℂ)⁻¹ *
      spectralSummand S D (baseRowCoefficient η C.Xi s hs) t I J *
      ((K/elementNorm (C.generator*completedIndex I J):ℝ):ℂ)*
      actualCongruenceCoefficient C (completedIndex I J) s hA H *
      ((K*elementNorm H/elementNorm ((C.generator*completedIndex I J)*s)):ℂ)^(-z)
  else 0

def guardedHighMellinCoefficient (η : HeckeFamily.Character) (C : CalibrationData)
    (S : Finset (Ideal O)) (D I J : Ideal O) (s : O) (X : ℝ) (H : O) (x z : ℂ) : ℂ :=
  if h : Squarefree I ∧ Supported I ∧ Supported J then
    (X:ℂ)^(1/2-z)*(elementNorm H:ℂ)^(-z)*completedMask S D I J*star (C.residueMonoid H)*
      bareSourceCoefficient η I (supported_primaryIdealGenerator_ne_zero I h.2.1)
        (completedIndex I J) s (CenteredMomentSupportedCorrelation.supported_element_ne_zero _ (supported_completed _ _
          ((supported_span_primaryIdealGenerator_iff I).mpr h.2.1)
          ((supported_span_primaryIdealGenerator_iff J).mpr h.2.2))) H *
      (fullIdealWeight (x+1/2) I*fullIdealWeight (1+3*x) J)
  else 0

theorem physicalMellinCoefficientTerm_eq_guarded (η : HeckeFamily.Character)
    (S : Finset (Ideal O)) (hS : ∀P∈S,P.IsMaximal) (hbad : fixedBadPrimes⊆S)
    (D I J : Ideal O) (s : O) (hs : Supported (Ideal.span {s}))
    (hcs : IsCoprime (calibrationForSet S hS).generator s)
    (X : ℝ) (hX : 0< X) (H : O) (hH : H≠0) (t z : ℂ) :
    physicalMellinCoefficientTerm η (calibrationForSet S hS) S D I J s hs X H t z=
      guardedHighMellinCoefficient η (calibrationForSet S hS) S D I J s X H (t+1-z) z := by
  by_cases hg : Squarefree I ∧ Supported I ∧ Supported J
  · have hA : completedIndex I J≠0 := CenteredMomentSupportedCorrelation.supported_element_ne_zero _ (supported_completed _ _
      ((supported_span_primaryIdealGenerator_iff I).mpr hg.2.1)
      ((supported_span_primaryIdealGenerator_iff J).mpr hg.2.2))
    rw [physicalMellinCoefficientTerm,dif_pos hA,guardedHighMellinCoefficient,dif_pos hg]
    dsimp only
    by_cases hm : completedMask S D I J=0
    · simp only [spectralSummand,hm,zero_mul,mul_zero]
    · have hc : IsCoprime (calibrationForSet S hS).generator (completedIndex I J) := by
        apply calibrationForSet_coprime_of_excluded S hS
        rw [completedIndex_eq_primaryIdealGenerator] at hA ⊢
        rw [(primaryIdealGenerator_spec (I*J^3) hA).1]
        unfold completedMask at hm
        split_ifs at hm with hd
        · exact hd.2
        · exact False.elim (hm rfl)
      exact physical_mellin_coefficient S hS D I J η s hs hg.2.1 hg.2.2 hg.1
        (hc.mul_right hcs) X hX H hH t z
  · have hz : spectralSummand S D (baseRowCoefficient η (calibrationForSet S hS).Xi s hs) t I J=0 := by
      by_contra hn
      exact hg (spectralSummand_support S hbad D I J _ t hn)
    rw [guardedHighMellinCoefficient,dif_neg hg]
    unfold physicalMellinCoefficientTerm
    split_ifs <;> simp only [hz,mul_zero,zero_mul]

theorem guardedHighMellinCoefficient_eq_high (η : HeckeFamily.Character) (C : CalibrationData)
    (S : Finset (Ideal O)) (hS : ∀P∈S,Prime P) (D I J K : Ideal O)
    (hK : Supported K) (hKS : ∀P∈S,¬P∣K) (X : ℝ) (H : O) (x w z : ℂ) :
    guardedHighMellinCoefficient η C S D I J (primaryIdealGenerator K) X H x z *
      fullIdealWeight w K =
    (X:ℂ)^(1/2-z)*(elementNorm H:ℂ)^(-z)*star (C.residueMonoid H)*
      markedIdealHighSummand S D η H x w z I J K 1 := by
  have h1 : ∀P∈S,¬P∣(1:Ideal O) := by
    intro P hP hd
    exact (hS P hP).not_unit (isUnit_of_dvd_one hd)
  have hw : fullIdealWeight (6*z) (1:Ideal O)=1 := (IdealEuler.normWeight (6*z)).map_one
  unfold guardedHighMellinCoefficient markedIdealHighSummand highIdealMask
    bareIdealHighSummand bareIdealHighCoefficient
  simp only [if_pos hKS,if_pos h1,mul_one,hw,primaryIdealGenerator_one,one_pow]
  by_cases hg : Squarefree I ∧ Supported I ∧ Supported J
  · have hfull : Squarefree I ∧ Supported I ∧ Supported J ∧ Supported K ∧ Supported (1:Ideal O) :=
      ⟨hg.1,hg.2.1,hg.2.2,hK,CenteredMomentAddedZero.supported_one_ideal⟩
    rw [dif_pos hg,dif_pos hfull]
    dsimp only [completedIndex]
    ring
  · have hfull : ¬(Squarefree I ∧ Supported I ∧ Supported J ∧ Supported K ∧ Supported (1:Ideal O)) :=
      fun h=> hg ⟨h.1,h.2.1,h.2.2.1⟩
    rw [dif_neg hg,dif_neg hfull]
    simp only [mul_zero,zero_mul]

end ProbePhysical
end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open MeasureTheory
namespace ProbePhysical
open ProbeMellinBoundary

def sourceHeightShear : HeightSpace ≃ᵐ HeightSpace where
  toFun p := ((p.1.1+p.1.2,p.1.2),p.2)
  invFun p := ((p.1.1-p.1.2,p.1.2),p.2)
  left_inv p := by rcases p with ⟨⟨t,v⟩,w⟩;simp
  right_inv p := by rcases p with ⟨⟨t,v⟩,w⟩;simp
  measurable_toFun := by
    change Measurable (fun p : HeightSpace=>((p.1.1+p.1.2,p.1.2),p.2))
    fun_prop
  measurable_invFun := by
    change Measurable (fun p : HeightSpace=>((p.1.1-p.1.2,p.1.2),p.2))
    fun_prop

lemma sourceHeightShear_preserving : MeasurePreserving sourceHeightShear heightMeasure heightMeasure := by
  exact (measurePreserving_add_prod (volume:Measure ℝ) volume).prod (MeasurePreserving.id volume)

lemma sourceHeightShear_integral (F : HeightSpace→ℂ) :
    (∫p,F (sourceHeightShear p) ∂heightMeasure)=∫p,F p ∂heightMeasure :=
  sourceHeightShear_preserving.integral_comp' F

theorem source_contour_shear (F : ℂ→ℂ→ℂ→ℂ) (σ ξ υ : ℝ) :
    (∫p : HeightSpace,F (((σ:ℂ)+p.1.1*Complex.I)+((ξ:ℂ)+p.1.2*Complex.I)-1)
      ((υ:ℂ)+p.2*Complex.I) ((ξ:ℂ)+p.1.2*Complex.I) ∂heightMeasure)=
    ∫p : HeightSpace,F (((σ+ξ-1:ℝ):ℂ)+p.1.1*Complex.I)
      ((υ:ℂ)+p.2*Complex.I) ((ξ:ℂ)+p.1.2*Complex.I) ∂heightMeasure := by
  have hh := sourceHeightShear_integral (fun p : HeightSpace=> F
    (((σ+ξ-1:ℝ):ℂ)+p.1.1*Complex.I) ((υ:ℂ)+p.2*Complex.I) ((ξ:ℂ)+p.1.2*Complex.I))
  convert hh using 1
  · congr 1
    funext p
    dsimp only [sourceHeightShear,MeasurableEquiv.coe_mk,Equiv.coe_fn_mk]
    congr 2 ; push_cast ; ring
  all_goals rfl

lemma sourceMellinWeight_shear (W0 W1 : SchwartzMap ℝ ℂ) (X Y Z : ℝ) (t w z : ℂ) :
    sourceMellinWeight W0 W1 X Y Z (t+1-z) w z=
      (X:ℂ)^(1/2-z)*(Z:ℂ)^t*(Y:ℂ)^(w-1)*Complex.exp (t^2)*
        mellin (SchwartzPlanePoisson.paperRadialFourier W0) z*mellin W1 w := by
  simp only [sourceMellinWeight,show t+1-z+z-1=t by ring]

end ProbePhysical
end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical
namespace ProbePhysical
open ProbeCompleted ProbeRow CompletedGauss CanonicalQuadraticSieve CubicEisenstein
open SchwartzPlanePoisson
local notation "O" => Eisenstein.O

def rawPhysicalMellinTerm (η : HeckeFamily.Character) (C : CalibrationData)
    (S : Finset (Ideal O)) (D I J K : Ideal O) (hK : Supported K)
    (W0 W1 : SchwartzMap ℝ ℂ) (X Y Z : ℝ) (H : O) (t w z : ℂ) : ℂ :=
  physicalMellinCoefficientTerm η C S D I J (primaryIdealGenerator K)
    ((supported_span_primaryIdealGenerator_iff K).mpr hK) X H t z *fullIdealWeight w K*
    (Y:ℂ)^(w-1)*(Z:ℂ)^t*Complex.exp (t^2)*mellin (paperRadialFourier W0) z*mellin W1 w

theorem rawPhysicalMellinTerm_eq_source (η : HeckeFamily.Character)
    (S : Finset (Ideal O)) (hS : ∀P∈S,P.IsMaximal) (hpS : ∀P∈S,Prime P)
    (hbad : fixedBadPrimes⊆S) (D I J K : Ideal O) (hK : Supported K)
    (hKS : ∀P∈S,¬P∣K) (W0 W1 : SchwartzMap ℝ ℂ)
    (X Y Z : ℝ) (hX : 0< X) (H : NonzeroFrequency) (t w z : ℂ) :
    rawPhysicalMellinTerm η (calibrationForSet S hS) S D I J K hK W0 W1 X Y Z H.val t w z=
      sourceMellinWeight W0 W1 X Y Z (t+1-z) w z *
        fullHighCoefficient S D η (fun h=> star ((calibrationForSet S hS).residueMonoid h.val))
          (t+1-z) w z (rawHighEmbedding (H,((I,J),K))) := by
  have hcs : IsCoprime (calibrationForSet S hS).generator (primaryIdealGenerator K) := by
    apply calibrationForSet_coprime_of_excluded S hS
    rw [(primaryIdealGenerator_spec K (supported_primaryIdealGenerator_ne_zero K hK)).1]
    exact hKS
  unfold rawPhysicalMellinTerm
  rw [physicalMellinCoefficientTerm_eq_guarded η S hS hbad D I J (primaryIdealGenerator K)
    ((supported_span_primaryIdealGenerator_iff K).mpr hK) hcs X hX H.val H.property t z,
    guardedHighMellinCoefficient_eq_high η (calibrationForSet S hS) S hpS D I J K hK hKS X H.val
      (t+1-z) w z,sourceMellinWeight_shear]
  simp only [fullHighCoefficient,frequencyWeight,rawHighEmbedding]
  ring

end ProbePhysical
end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical
open MeasureTheory
namespace ProbePhysical
open ProbeMellinBoundary CanonicalQuadraticSieve
local notation "O" => Eisenstein.O
local instance : Countable O := Eisenstein.Coordinates.coordinateEquiv.injective.countable
local instance : Countable (Ideal O) := CubicEisenstein.cubicIdealGenerator_injective.countable

def SourceRawIndex (S : Finset (Ideal O)) :=
  {p : RawHighIndex // Supported p.2.2 ∧ ∀P∈S,¬P∣p.2.2}

instance (S : Finset (Ideal O)) : Countable (SourceRawIndex S) := inferInstanceAs (Countable {_p : RawHighIndex // _})

def sourceRawEmbedding (S : Finset (Ideal O)) (i : SourceRawIndex S) : FullHighIndex :=
  rawHighEmbedding i.val

lemma sourceRawEmbedding_injective (S : Finset (Ideal O)) : Function.Injective (sourceRawEmbedding S) :=
  rawHighEmbedding_injective.comp Subtype.val_injective

def originalRawOnLines (η : HeckeFamily.Character) (S : Finset (Ideal O))
    (hS : ∀P∈S,P.IsMaximal) (D : Ideal O) (W0 W1 : SchwartzMap ℝ ℂ) (X Y Z : ℝ)
    (i : SourceRawIndex S) (p : HeightSpace) : ℂ :=
  rawPhysicalMellinTerm η (calibrationForSet S hS) S D i.val.2.1.1 i.val.2.1.2 i.val.2.2 i.property.1
    W0 W1 X Y Z i.val.1.val ((4:ℂ)+p.1.1*Complex.I)
      ((3:ℂ)+p.2*Complex.I) ((2:ℂ)+p.1.2*Complex.I)

theorem originalRaw_counting_product_integrable (η : HeckeFamily.Character)
    (S : Finset (Ideal O)) (hS : ∀P∈S,P.IsMaximal) (hpS : ∀P∈S,Prime P)
    (hbad : fixedBadPrimes⊆S) [MeasurableSpace (SourceRawIndex S)] [MeasurableSingletonClass (SourceRawIndex S)]
    (D : Ideal O) (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ)
    (ha0 : 0< a0) (ha1 : 0< a1) (hW0 : Function.support W0⊆Set.Icc a0 b0)
    (hW1 : Function.support W1⊆Set.Icc a1 b1)
    (X Y Z : ℝ) (hX : 0< X) (hY : 0< Y) (hZ : 0< Z) :
    Integrable (fun p : SourceRawIndex S×HeightSpace=> originalRawOnLines η S hS D W0 W1 X Y Z p.1 p.2)
      ((Measure.count:Measure (SourceRawIndex S)).prod heightMeasure) := by
  let mask := fun H : NonzeroFrequency=> star ((calibrationForSet S hS).residueMonoid H.val)
  have hm (H : NonzeroFrequency) : ‖mask H‖≤1 := by
    simpa only [mask,norm_star] using (calibrationForSet S hS).residueMonoid_norm_le_one H.val
  let T := fun p : HeightSpace=> sourceMellinWeight W0 W1 X Y Z
    ((3:ℂ)+p.1.1*Complex.I) ((3:ℂ)+p.2*Complex.I) ((2:ℂ)+p.1.2*Complex.I)
  have hT : Integrable T heightMeasure := sourceMellinWeight_initial_integrable W0 W1 a0 b0 a1 b1
    ha0 ha1 hW0 hW1 X Y Z hX hY hZ 3 2 3 (by norm_num)
  have hcT : Continuous T := sourceMellinWeight_initial_continuous W0 W1 a1 b1 ha1 hW1
    X Y Z hX hY hZ 3 2 3 (by norm_num)
  have hi := initialHigh_counting_product_integrable (sourceRawEmbedding S) (sourceRawEmbedding_injective S)
    S D η mask hm 3 3 2 (by norm_num) (by norm_num) (by norm_num) T hT hcT
  have hp := (MeasurePreserving.id (Measure.count:Measure (SourceRawIndex S))).prod
    (sourceHeightShear_preserving.symm sourceHeightShear)
  have hh := hp.integrable_comp_of_integrable hi
  apply hh.congr
  apply Filter.Eventually.of_forall
  intro p
  dsimp only [Function.comp_def,Prod.map]
  rw [originalRawOnLines,rawPhysicalMellinTerm_eq_source η S hS hpS hbad D _ _ _ p.1.property.1
    p.1.property.2 W0 W1 X Y Z hX p.1.val.1]
  have he : (4:ℂ)+p.2.1.1*Complex.I+1-((2:ℂ)+p.2.1.2*Complex.I)=
      3+((p.2.1.1-p.2.1.2:ℝ):ℂ)*Complex.I := by push_cast;ring
  have hsh : sourceHeightShear.symm p.2=((p.2.1.1-p.2.1.2,p.2.1.2),p.2.2) := rfl
  simp only [he,initialHighOnLines,T,hsh,sourceRawEmbedding,mask,id_eq,Complex.ofReal_ofNat]
  ring

end ProbePhysical
end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open MeasureTheory
namespace ProbePhysical

lemma count_product {A B : Type*} [Countable A] [Countable B]
    [MeasurableSpace A] [MeasurableSpace B] [MeasurableSingletonClass A] [MeasurableSingletonClass B] :
    (Measure.count:Measure A).prod (Measure.count:Measure B)=Measure.count := by
  apply Measure.ext_of_singleton
  rintro ⟨a,b⟩
  rw [←Set.singleton_prod_singleton,Measure.prod_prod]
  simp

lemma count_equiv_preserving {A B : Type*} [Countable A] [Countable B]
    [MeasurableSpace A] [MeasurableSpace B] [MeasurableSingletonClass A] [MeasurableSingletonClass B]
    (e : A≃ᵐB) : MeasurePreserving e Measure.count Measure.count := by
  refine ⟨e.measurable,?_⟩
  apply Measure.ext_of_singleton
  intro b
  rw [Measure.map_apply e.measurable (measurableSet_singleton b)]
  have he : e ⁻¹' {b}={e.symm b} := by
    ext a
    change e a = b ↔ a = e.symm b
    constructor
    · intro h
      exact (e.symm_apply_apply a).symm.trans (congrArg e.symm h)
    · rintro rfl
      exact e.apply_symm_apply b
  rw [he]
  simp

def quadShuffle {A B C D : Type*} [MeasurableSpace A] [MeasurableSpace B]
    [MeasurableSpace C] [MeasurableSpace D] : (A×B)×(C×D) ≃ᵐ (A×C)×(B×D) where
  toFun p := ((p.1.1,p.2.1),(p.1.2,p.2.2))
  invFun p := ((p.1.1,p.2.1),(p.1.2,p.2.2))
  left_inv p := rfl
  right_inv p := rfl
  measurable_toFun := by change Measurable (fun p : (A×B)×(C×D)=>((p.1.1,p.2.1),(p.1.2,p.2.2)));fun_prop
  measurable_invFun := by change Measurable (fun p : (A×C)×(B×D)=>((p.1.1,p.2.1),(p.1.2,p.2.2)));fun_prop

lemma quadShuffle_preserving {A B C D : Type*} [MeasurableSpace A] [MeasurableSpace B]
    [MeasurableSpace C] [MeasurableSpace D] (μA : Measure A) (μB : Measure B)
    (μC : Measure C) (μD : Measure D) [SFinite μA] [SFinite μB] [SFinite μC] [SFinite μD] :
    MeasurePreserving (quadShuffle : (A×B)×(C×D) ≃ᵐ (A×C)×(B×D))
      ((μA.prod μB).prod (μC.prod μD)) ((μA.prod μC).prod (μB.prod μD)) := by
  have h1 := measurePreserving_prodAssoc μA μB (μC.prod μD)
  have h2 := (MeasurePreserving.id μA).prod ((measurePreserving_prodAssoc μB μC μD).symm MeasurableEquiv.prodAssoc)
  have h3 := (MeasurePreserving.id μA).prod
    ((Measure.measurePreserving_swap (μ:=μB) (ν:=μC)).prod (MeasurePreserving.id μD))
  have h4 := (MeasurePreserving.id μA).prod (measurePreserving_prodAssoc μC μB μD)
  have h5 := (measurePreserving_prodAssoc μA μC (μB.prod μD)).symm MeasurableEquiv.prodAssoc
  exact h5.comp (h4.comp (h3.comp (h2.comp h1)))

def physicalNestingEquiv {A B C D E F : Type*} [MeasurableSpace A] [MeasurableSpace B]
    [MeasurableSpace C] [MeasurableSpace D] [MeasurableSpace E] [MeasurableSpace F] :
    (A×(B×C))×((D×E)×F) ≃ᵐ A×(F×(D×(B×(E×C)))) where
  toFun p := (p.1.1,(p.2.2,(p.2.1.1,(p.1.2.1,(p.2.1.2,p.1.2.2)))))
  invFun p := ((p.1,(p.2.2.2.1,p.2.2.2.2.2)),((p.2.2.1,p.2.2.2.2.1),p.2.1))
  left_inv p := rfl
  right_inv p := rfl
  measurable_toFun := by
    change Measurable (fun p : (A×(B×C))×((D×E)×F)=>
      (p.1.1,(p.2.2,(p.2.1.1,(p.1.2.1,(p.2.1.2,p.1.2.2))))))
    fun_prop
  measurable_invFun := by
    change Measurable (fun p : A×(F×(D×(B×(E×C))))=>
      ((p.1,(p.2.2.2.1,p.2.2.2.2.2)),((p.2.2.1,p.2.2.2.2.1),p.2.1)))
    fun_prop

lemma physicalNesting_preserving {A B C D E F : Type*} [MeasurableSpace A] [MeasurableSpace B]
    [MeasurableSpace C] [MeasurableSpace D] [MeasurableSpace E] [MeasurableSpace F]
    (μA : Measure A) (μB : Measure B) (μC : Measure C)
    (μD : Measure D) (μE : Measure E) (μF : Measure F)
    [SFinite μA] [SFinite μB] [SFinite μC] [SFinite μD] [SFinite μE] [SFinite μF] :
    MeasurePreserving (physicalNestingEquiv : (A×(B×C))×((D×E)×F) ≃ᵐ A×(F×(D×(B×(E×C)))))
      ((μA.prod (μB.prod μC)).prod ((μD.prod μE).prod μF))
      (μA.prod (μF.prod (μD.prod (μB.prod (μE.prod μC))))) := by
  have h1 := measurePreserving_prodAssoc μA (μB.prod μC) ((μD.prod μE).prod μF)
  have hr := (Measure.measurePreserving_swap (μ:=(μB.prod μC).prod (μD.prod μE)) (ν:=μF)).comp
    ((measurePreserving_prodAssoc (μB.prod μC) (μD.prod μE) μF).symm MeasurableEquiv.prodAssoc)
  have hq := quadShuffle_preserving μB μC μD μE
  have hs := (Measure.measurePreserving_swap (μ:=μB) (ν:=μD)).prod
    (Measure.measurePreserving_swap (μ:=μC) (ν:=μE))
  have ha := measurePreserving_prodAssoc μD μB (μE.prod μC)
  exact ((MeasurePreserving.id μA).prod
    (((MeasurePreserving.id μF).prod (ha.comp (hs.comp hq))).comp hr)).comp h1

lemma integral_count_eq_tsum {A : Type*} [Countable A] [MeasurableSpace A]
    [MeasurableSingletonClass A] (f : A→ℂ) (hf : Integrable f Measure.count) :
    (∫a,f a ∂Measure.count)=∑'a,f a := by
  simpa using integral_countable hf

theorem integral_physical_nesting {A B C : Type*} [Countable A] [Countable B] [Countable C]
    [MeasurableSpace A] [MeasurableSpace B] [MeasurableSpace C]
    [MeasurableSingletonClass A] [MeasurableSingletonClass B] [MeasurableSingletonClass C]
    (F : A×(ℝ×(ℝ×(B×(ℝ×C))))→ℂ)
    (hF : Integrable F ((Measure.count:Measure A).prod (volume.prod (volume.prod
      ((Measure.count:Measure B).prod (volume.prod (Measure.count:Measure C))))))) :
    (∫p,F p ∂((Measure.count:Measure A).prod (volume.prod (volume.prod
      ((Measure.count:Measure B).prod (volume.prod (Measure.count:Measure C)))))))=
      ∑'a : A,∫w : ℝ,∫t : ℝ,∑'b : B,∫z : ℝ,∑'c : C,F (a,(w,(t,(b,(z,c))))) := by
  rw [integral_prod _ hF,integral_count_eq_tsum _ hF.integral_prod_left]
  apply tsum_congr
  intro a
  have ha := (Measure.ae_count_iff.mp hF.prod_right_ae) a
  rw [integral_prod _ ha]
  apply integral_congr_ae
  filter_upwards [ha.prod_right_ae] with w hw
  rw [integral_prod _ hw]
  apply integral_congr_ae
  filter_upwards [hw.prod_right_ae] with t ht
  rw [integral_prod _ ht,integral_count_eq_tsum _ ht.integral_prod_left]
  apply tsum_congr
  intro b
  have hb := (Measure.ae_count_iff.mp ht.prod_right_ae) b
  rw [integral_prod _ hb]
  apply integral_congr_ae
  filter_upwards [hb.prod_right_ae] with z hz
  exact integral_count_eq_tsum _ hz

end ProbePhysical
end

end

end GaloisForLFunctions.MetaplecticMobiusDescent.CubicEisenstein
