/-
Central rectangles adapted from OpenAI's formalization, Apache-2.0.
See LICENSE and NOTICE in the parent directory for source attribution.
-/
import GaloisForLFunctions.MetaplecticMobiusDescent.PrimeRows.BufferedRowAmplitudes

/-!
# Central rectangles

Central cube and rectangle integrals, uniform height tails and row errors; central prime-tuple
counts and the arbitrary saving of finite rectangle rows.
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
open CubicSieve CenteredMomentFourier Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical BigOperators
open MeasureTheory Set Complex
namespace ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical ProbeMellinBoundary
local notation "O" => Eisenstein.O

theorem uniform_original_x_height_tail (K : ℕ)
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hmax : ∀P∈S,P.IsMaximal)
    (hfirst : FirstTail (1/4) S)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0< a0) (ha1 : 0< a1)
    (hW0 : Function.support W0⊆Icc a0 b0) (hW1 : Function.support W1⊆Icc a1 b1)
    (N : ℕ) (r : ℝ) (hr : (17/50:ℝ)≤ r) (hr1 : r≤1) :
    ∃C : ℝ,0≤ C ∧ ∀(η : Character) (u : FreeRow),u.val≠1 →
      ∀(P : Fin K→ HeckeIdealSeries.PrimeIdeal),Function.Injective P → ∀hPS : ∀j,(P j).val∉S,∀υ∈Icc (-(1/100:ℝ)) (1/2),∀X Y Z : ℝ,0< X → 0< Y → 0< Z →
      ∀H : ℝ,0≤ H →
      (∫p : HeightSpace in {t : HeightSpace | |t.1.1|≤ H}ᶜ,
        ‖continuedRowOnLines S hS hmax P hPS η u W0 W1 X Y Z 2 υ r p‖ ∂heightMeasure)≤
        C*contourArithmeticCost η u P*(X^(1/2-r)*Z^(2+r-1)*Y^(υ-1))/(1+H)^N := by
  obtain ⟨A0,hA0,hrow0⟩ := rowAmplitudeOnLines_first_polynomial K S hS hfirst hmax
  obtain ⟨D,hD,hprofile⟩ := source_profile_arithmetic_tails W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
    2 2 r r (-(1/100)) (1/2) (by linarith) 2 N
  refine ⟨9*A0*D,by positivity,?_⟩
  intro η u hu P hP hPS υ hυ X Y Z hX hY hZ H hH
  let A := A0*contourArithmeticCost η u P
  have hA := mul_nonneg hA0 (contourArithmeticCost_nonneg η u P)
  have hrow := hrow0 η u hu P hP hPS
  let G := rowAmplitudeOnLines S hS hmax P hPS η u 2 υ r
  have hG : Measurable G := rowAmplitudeOnLines_measurable S hS hmax P hPS η u 2 υ r
  have hb (t : HeightSpace) : ‖G t‖≤(9*A)*jointHeight t.1.1 t.1.2 t.2^2 := by
    have hh : 3+|t.2|≤3*jointHeight t.1.1 t.1.2 t.2 := by
      unfold jointHeight
      linarith [abs_nonneg t.1.1,abs_nonneg t.1.2,abs_nonneg t.2]
    apply (hrow υ hυ.1 r ⟨hr,hr1⟩ t).trans
    calc
      _ ≤ A*(3*jointHeight t.1.1 t.1.2 t.2)^2 := mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (by positivity) hh 2) hA
      _ = _ := by ring
  have ht := hprofile 2 ⟨le_rfl,le_rfl⟩ r ⟨le_rfl,le_rfl⟩ υ hυ
    (9*A) (by positivity) X Y Z hX hY hZ G hG.aestronglyMeasurable hb
  have ht' : Integrable (continuedRowOnLines S hS hmax P hPS η u W0 W1 X Y Z 2 υ r) heightMeasure ∧
      ∀T : ℝ,0≤ T →
      (∫p : HeightSpace in outsideBox T,‖continuedRowOnLines S hS hmax P hPS η u W0 W1 X Y Z 2 υ r p‖ ∂heightMeasure)≤
        (9*A)*D*(X^(1/2-r)*Z^(2+r-1)*Y^(υ-1))/(1+T)^N := by
    have hfun : continuedRowOnLines S hS hmax P hPS η u W0 W1 X Y Z 2 υ r=
        (fun p : HeightSpace=> sourceMellinWeight W0 W1 X Y Z ((2:ℂ)+p.1.1*I) ((υ:ℂ)+p.2*I) ((r:ℂ)+p.1.2*I)*G p) := by
      funext p
      exact continuedRowOnLines_eq_amplitude ..
    rw [hfun]
    exact ht
  apply le_trans _ ((ht'.2 H hH).trans_eq (by dsimp [A];ring))
  apply setIntegral_mono_set ht'.1.norm.integrableOn (Filter.Eventually.of_forall (fun _=> norm_nonneg _))
  apply Filter.Eventually.of_forall
  intro p hp
  have hx : H < |p.1.1| := lt_of_not_ge hp
  exact Or.inl hx

end ProbeHighRowFamily

end

end

noncomputable section
open CubicSieve CenteredMomentFourier Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical BigOperators
open MeasureTheory Set Complex
namespace ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical ProbeMellinBoundary
local notation "O" => Eisenstein.O
variable {ι : Type*} [Fintype ι]

theorem uniform_original_row_central_error (K : ℕ)
    (e : ℝ) (he : 0< e) (he' : e<1/1000)
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hmax : ∀P∈S,P.IsMaximal)
    (hfirst : FirstTail (4*e) S)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0< a0) (ha1 : 0< a1)
    (hW0 : Function.support W0⊆Icc a0 b0) (hW1 : Function.support W1⊆Icc a1 b1)
    (N : ℕ) :
    ∃C : ℝ,0≤ C ∧ ∀(η : Character) (u : FreeRow),u.val≠1 →
      ∀(P : Fin K→ HeckeIdealSeries.PrimeIdeal),Function.Injective P → ∀hPS : ∀j,(P j).val∉S,
      ∀ψ : ι→ Character,∀X Y Z : ℝ,0< X → 0< Y → 1≤ Z → ∀a B H : ℝ,∀i : ℕ,
      (51/100:ℝ)≤ a → a≤1 → 2< B → 0≤ H → H≤(3*i+2:ℕ)*B →
      detectorMaximum (sourceDetectorFamily S hS.prime η u ψ) (3*(i+1:ℕ)*B)< a+2*e →
      ‖rowIntegral η S (calibrationForSet S hmax) (fun j=> primaryIdealGenerator (P j).val) W0 W1 X Y Z u-
        centralRowIntegral S hS hmax P hPS η u W0 W1 X Y Z a e H‖≤
        C*contourArithmeticCost η u P*(X^(1/2-(17/50:ℝ))*Z^(2+(17/50:ℝ)-1)*Y^((1-a-6*e)-1))/height H^N := by
  obtain ⟨Cj,hCj,hjoin0⟩ := uniform_buffered_horizontal_join_decay (ι:=ι) K e he he' S hS hmax hfirst
    W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1 N (17/50) le_rfl (by norm_num)
  obtain ⟨Ct,hCt,htail0⟩ := uniform_original_x_height_tail K S hS hmax (hfirst.mono_parameter (by linarith))
    W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1 N (17/50) le_rfl (by norm_num)
  let n : ℂ := ((1/(2*Real.pi):ℝ):ℂ)^3
  refine ⟨‖n‖*(2*Cj+Ct),by positivity,?_⟩
  intro η u hu P hP hPS ψ X Y Z hX hY hZ a B H i ha haTop hB hH0 hH hbin
  have hjoin := hjoin0 η u hu P hP hPS ψ
  have htail := htail0 η u hu P hP hPS
  have hcost := contourArithmeticCost_nonneg η u P
  have hZ0 : 0< Z := by linarith
  let k := fun σ p=> continuedRowOnLines S hS hmax P hPS η u W0 W1 X Y Z σ (1-a-6*e) (17/50) p
  let E : Set HeightSpace := {t | |t.1.1|≤ H}
  let J := fun tx : ℝ=>∫q : ℝ×ℝ,(∫v : ℝ in (a+16*e)..2,k v ((tx,q.1),q.2)) ∂volume.prod volume
  let tail := ∫p : HeightSpace in Eᶜ,k 2 p ∂heightMeasure
  let A : ℝ := contourArithmeticCost η u P*(X^(1/2-(17/50:ℝ))*Z^(2+(17/50:ℝ)-1)*Y^((1-a-6*e)-1))/height H^N
  have hA : 0≤ A := by dsimp [A];exact div_nonneg (by positivity) (pow_nonneg (height_pos _).le _)
  have hj (tx : ℝ) (htx : |tx|=H) : ‖J tx‖≤ Cj*A := by
    apply (norm_integral_le_integral_norm _).trans
    have hb := (hjoin X Y Z hX hY hZ0 a B H i ha haTop hB hH hbin tx htx).2
    rw [scaleBound_eq_rpow_of_one_le hZ (by norm_num)] at hb
    exact hb.trans_eq (by dsimp only [A]; ring)
  have ht : ‖tail‖≤ Ct*A := by
    apply (norm_integral_le_integral_norm _).trans
    have hb := htail (1-a-6*e) ⟨by linarith,by linarith⟩ X Y Z hX hY hZ0 H hH0
    exact hb.trans_eq (by dsimp only [A,height]; rw [abs_of_nonneg hH0]; ring)
  have hdec := (rowIntegral_central_decomposition e a B H i he he' ha haTop hB hH0 hH S hS hmax hfirst
    P hP hPS η u hu ψ hbin W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1 X Y Z hX hY hZ0).2
  have heq : rowIntegral η S (calibrationForSet S hmax) (fun j=> primaryIdealGenerator (P j).val) W0 W1 X Y Z u-
      centralRowIntegral S hS hmax P hPS η u W0 W1 X Y Z a e H=n*(I*(J (-H)-J H)+tail) := by
    rw [hdec]
    dsimp [centralRowIntegral,n,J,tail,k,E]
    ring
  rw [heq,norm_mul]
  calc
    _ ≤ ‖n‖*(‖J (-H)‖+‖J H‖+‖tail‖) := by
      apply mul_le_mul_of_nonneg_left _ (norm_nonneg n)
      apply (norm_add_le (I*(J (-H)-J H)) tail).trans
      rw [norm_mul,norm_I,one_mul]
      exact add_le_add (norm_sub_le (J (-H)) (J H)) (le_refl ‖tail‖)
    _ ≤ ‖n‖*(Cj*A+Cj*A+Ct*A) := by
      gcongr
      · exact hj (-H) (by rw [abs_neg,abs_of_nonneg hH0])
      · exact hj H (abs_of_nonneg hH0)
    _ = _ := by dsimp [A];ring

end ProbeHighRowFamily

end

end

noncomputable section
open CubicSieve CenteredMomentFourier Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical BigOperators
open MeasureTheory Set Complex
namespace ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical ProbeMellinBoundary
local notation "O" => Eisenstein.O
variable {ι : Type*} [Fintype ι]

theorem uniform_central_w_height_tail (K : ℕ)
    (e : ℝ) (he : 0< e) (he' : e<1/1000)
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hmax : ∀P∈S,P.IsMaximal)
    (hfirst : FirstTail (4*e) S)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0< a0) (ha1 : 0< a1)
    (hW0 : Function.support W0⊆Icc a0 b0) (hW1 : Function.support W1⊆Icc a1 b1)
    (N : ℕ) (r : ℝ) (hr : (17/50:ℝ)≤ r) (hr1 : r≤1) :
    ∃C : ℝ,0≤ C ∧ ∀(η : Character) (u : FreeRow),u.val≠1 →
      ∀(P : Fin K→ HeckeIdealSeries.PrimeIdeal),Function.Injective P → ∀hPS : ∀j,(P j).val∉S,
      ∀ψ : ι→ Character,∀X Y Z : ℝ,0< X → 0< Y → 0< Z → ∀a B H : ℝ,∀i : ℕ,
      (51/100:ℝ)≤ a → a≤1 → 2< B → 0≤ H → H≤(3*i+2:ℕ)*B →
      detectorMaximum (sourceDetectorFamily S hS.prime η u ψ) (3*(i+1:ℕ)*B)< a+2*e →
      ∀σ∈Icc (a+16*e) 2,
      (∫p : HeightSpace in {t : HeightSpace | |t.1.1|≤ H ∧ H < |t.2|},
        ‖continuedRowOnLines S hS hmax P hPS η u W0 W1 X Y Z σ (1-a-6*e) r p‖ ∂heightMeasure)≤
        C*contourArithmeticCost η u P*(X^(1/2-r)*Z^(σ+r-1)*Y^((1-a-6*e)-1))/height H^N := by
  obtain ⟨A0,hA0,hrow0⟩ := rowAmplitudeOnLines_buffered_polynomial (ι:=ι) K e he he' S hS hfirst hmax
  obtain ⟨D,hD,hprofile⟩ := source_profile_arithmetic_tails W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
    (51/100) 2 r r (-(1/100)) (1/2) (by linarith) 2 (N+2)
  refine ⟨81*A0*D,by positivity,?_⟩
  intro η u hu P hP hPS ψ X Y Z hX hY hZ a B H i ha haTop hB hH0 hH hbin σ hσ
  let E : Set HeightSpace := {t | |t.1.1|≤ H}
  let R : Set HeightSpace := {t | |t.1.1|≤ H ∧ H < |t.2|}
  have hE : MeasurableSet E := measurableSet_le (by fun_prop) measurable_const
  have hR : MeasurableSet R := hE.inter (measurableSet_lt measurable_const (show Measurable (fun t : HeightSpace => |t.2|) by fun_prop))
  let A := A0*contourArithmeticCost η u P
  have hA : 0≤ A := mul_nonneg hA0 (contourArithmeticCost_nonneg η u P)
  let G := E.indicator (rowAmplitudeOnLines S hS hmax P hPS η u σ (1-a-6*e) r)
  have hG : Measurable G := (rowAmplitudeOnLines_measurable S hS hmax P hPS η u σ (1-a-6*e) r).indicator hE
  have hb (t : HeightSpace) : ‖G t‖≤(9*A*(3+|H|)^2)*jointHeight t.1.1 t.1.2 t.2^2 := by
    by_cases ht : t∈E
    · rw [show G t=rowAmplitudeOnLines S hS hmax P hPS η u σ (1-a-6*e) r t by exact Set.indicator_of_mem ht _]
      have hh : 3+|t.2|≤3*jointHeight t.1.1 t.1.2 t.2 := by
        unfold jointHeight
        linarith [abs_nonneg t.1.1,abs_nonneg t.1.2,abs_nonneg t.2]
      apply (hrow0 η u hu P hP hPS ψ a B H i ha haTop hB hH hbin σ hσ r ⟨hr,hr1⟩ t ht).trans
      calc
        _ ≤ (A*(3+|H|)^2)*(3*jointHeight t.1.1 t.1.2 t.2)^2 :=
          mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hh 2) (by positivity)
        _ = _ := by ring
    · simp only [G,Set.indicator_of_notMem ht,norm_zero]
      positivity
  let F := fun t : HeightSpace=> sourceMellinWeight W0 W1 X Y Z
    ((σ:ℂ)+t.1.1*I) ((((1-a-6*e):ℝ):ℂ)+t.2*I) ((r:ℂ)+t.1.2*I)*G t
  have hp := hprofile σ ⟨by linarith [hσ.1],hσ.2⟩ r ⟨le_rfl,le_rfl⟩ (1-a-6*e)
    ⟨by linarith,by linarith⟩ (9*A*(3+|H|)^2) (by positivity)
    X Y Z hX hY hZ G hG.aestronglyMeasurable hb
  have hFR (t : HeightSpace) (ht : t∈R) : F t=continuedRowOnLines S hS hmax P hPS η u W0 W1 X Y Z σ (1-a-6*e) r t := by
    dsimp only [F,G]
    rw [Set.indicator_of_mem (show t∈E from ht.1),continuedRowOnLines_eq_amplitude]
  have hb' : (∫t in R,‖F t‖ ∂heightMeasure)≤
      (9*A*(3+|H|)^2)*D*(X^(1/2-r)*Z^(σ+r-1)*Y^((1-a-6*e)-1))/(1+H)^(N+2) := by
    apply le_trans _ (hp.2 H hH0)
    apply setIntegral_mono_set hp.1.norm.integrableOn (Filter.Eventually.of_forall (fun _=> norm_nonneg _))
    exact Filter.Eventually.of_forall (fun t ht=> Or.inr (Or.inr ht.2))
  have heq : (∫t in R,‖F t‖ ∂heightMeasure)=
      ∫t in R,‖continuedRowOnLines S hS hmax P hPS η u W0 W1 X Y Z σ (1-a-6*e) r t‖ ∂heightMeasure :=
    setIntegral_congr_fun hR (fun t ht=> congrArg norm (hFR t ht))
  rw [heq] at hb'
  apply hb'.trans
  have hpow : (3+|H|)^2≤9*(height H)^2 := by
    have hh : 3+|H|≤3*height H := by unfold height;linarith [abs_nonneg H]
    have hh' := pow_le_pow_left₀ (by positivity) hh 2
    norm_num [mul_pow] at hh'
    exact hh'
  have hheight : 1+H=height H := by simp [height,abs_of_nonneg hH0]
  have hden : 0< height H := height_pos H
  rw [hheight]
  calc
    _ ≤ (9*A*(9*height H^2))*D*(X^(1/2-r)*Z^(σ+r-1)*Y^((1-a-6*e)-1))/height H^(N+2) := by
      gcongr
    _ = _ := by dsimp [A];rw [pow_add];field_simp;ring

end ProbeHighRowFamily

end

end

noncomputable section
open CubicSieve CenteredMomentFourier Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical BigOperators
open MeasureTheory Set Complex
namespace ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical ProbeMellinBoundary
local notation "O" => Eisenstein.O
variable {ι : Type*} [Fintype ι]

theorem uniform_central_z_height_tail (K : ℕ)
    (e : ℝ) (he : 0< e) (he' : e<1/1000)
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hmax : ∀P∈S,P.IsMaximal)
    (hfirst : FirstTail (4*e) S)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0< a0) (ha1 : 0< a1)
    (hW0 : Function.support W0⊆Icc a0 b0) (hW1 : Function.support W1⊆Icc a1 b1)
    (N : ℕ) (r : ℝ) (hr : (17/50:ℝ)≤ r) (hr1 : r≤1) :
    ∃C : ℝ,0≤ C ∧ ∀(η : Character) (u : FreeRow),u.val≠1 →
      ∀(P : Fin K→ HeckeIdealSeries.PrimeIdeal),Function.Injective P → ∀hPS : ∀j,(P j).val∉S,
      ∀ψ : ι→ Character,∀X Y Z : ℝ,0< X → 0< Y → 0< Z → ∀a B H : ℝ,∀i : ℕ,
      (51/100:ℝ)≤ a → a≤1 → 2< B → 0≤ H → H≤(3*i+2:ℕ)*B →
      detectorMaximum (sourceDetectorFamily S hS.prime η u ψ) (3*(i+1:ℕ)*B)< a+2*e →
      ∀σ∈Icc (a+16*e) 2,
      (∫p : HeightSpace in {t : HeightSpace | |t.1.1|≤ H ∧ H < |t.1.2|},
        ‖continuedRowOnLines S hS hmax P hPS η u W0 W1 X Y Z σ (1-a-6*e) r p‖ ∂heightMeasure)≤
        C*contourArithmeticCost η u P*(X^(1/2-r)*Z^(σ+r-1)*Y^((1-a-6*e)-1))/height H^N := by
  obtain ⟨A0,hA0,hrow0⟩ := rowAmplitudeOnLines_buffered_polynomial (ι:=ι) K e he he' S hS hfirst hmax
  obtain ⟨D,hD,hprofile⟩ := source_profile_arithmetic_tails W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
    (51/100) 2 r r (-(1/100)) (1/2) (by linarith) 2 (N+2)
  refine ⟨81*A0*D,by positivity,?_⟩
  intro η u hu P hP hPS ψ X Y Z hX hY hZ a B H i ha haTop hB hH0 hH hbin σ hσ
  let E : Set HeightSpace := {t | |t.1.1|≤ H}
  let R : Set HeightSpace := {t | |t.1.1|≤ H ∧ H < |t.1.2|}
  have hE : MeasurableSet E := measurableSet_le (by fun_prop) measurable_const
  have hR : MeasurableSet R := hE.inter (measurableSet_lt measurable_const (show Measurable (fun t : HeightSpace => |t.1.2|) by fun_prop))
  let A := A0*contourArithmeticCost η u P
  have hA : 0≤ A := mul_nonneg hA0 (contourArithmeticCost_nonneg η u P)
  let G := E.indicator (rowAmplitudeOnLines S hS hmax P hPS η u σ (1-a-6*e) r)
  have hG : Measurable G := (rowAmplitudeOnLines_measurable S hS hmax P hPS η u σ (1-a-6*e) r).indicator hE
  have hb (t : HeightSpace) : ‖G t‖≤(9*A*(3+|H|)^2)*jointHeight t.1.1 t.1.2 t.2^2 := by
    by_cases ht : t∈E
    · rw [show G t=rowAmplitudeOnLines S hS hmax P hPS η u σ (1-a-6*e) r t by exact Set.indicator_of_mem ht _]
      have hh : 3+|t.2|≤3*jointHeight t.1.1 t.1.2 t.2 := by
        unfold jointHeight
        linarith [abs_nonneg t.1.1,abs_nonneg t.1.2,abs_nonneg t.2]
      apply (hrow0 η u hu P hP hPS ψ a B H i ha haTop hB hH hbin σ hσ r ⟨hr,hr1⟩ t ht).trans
      calc
        _ ≤ (A*(3+|H|)^2)*(3*jointHeight t.1.1 t.1.2 t.2)^2 :=
          mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hh 2) (by positivity)
        _ = _ := by ring
    · simp only [G,Set.indicator_of_notMem ht,norm_zero]
      positivity
  let F := fun t : HeightSpace=> sourceMellinWeight W0 W1 X Y Z
    ((σ:ℂ)+t.1.1*I) ((((1-a-6*e):ℝ):ℂ)+t.2*I) ((r:ℂ)+t.1.2*I)*G t
  have hp := hprofile σ ⟨by linarith [hσ.1],hσ.2⟩ r ⟨le_rfl,le_rfl⟩ (1-a-6*e)
    ⟨by linarith,by linarith⟩ (9*A*(3+|H|)^2) (by positivity)
    X Y Z hX hY hZ G hG.aestronglyMeasurable hb
  have hFR (t : HeightSpace) (ht : t∈R) : F t=continuedRowOnLines S hS hmax P hPS η u W0 W1 X Y Z σ (1-a-6*e) r t := by
    dsimp only [F,G]
    rw [Set.indicator_of_mem (show t∈E from ht.1),continuedRowOnLines_eq_amplitude]
  have hb' : (∫t in R,‖F t‖ ∂heightMeasure)≤
      (9*A*(3+|H|)^2)*D*(X^(1/2-r)*Z^(σ+r-1)*Y^((1-a-6*e)-1))/(1+H)^(N+2) := by
    apply le_trans _ (hp.2 H hH0)
    apply setIntegral_mono_set hp.1.norm.integrableOn (Filter.Eventually.of_forall (fun _=> norm_nonneg _))
    exact Filter.Eventually.of_forall (fun t ht=> Or.inr (Or.inl ht.2))
  have heq : (∫t in R,‖F t‖ ∂heightMeasure)=
      ∫t in R,‖continuedRowOnLines S hS hmax P hPS η u W0 W1 X Y Z σ (1-a-6*e) r t‖ ∂heightMeasure :=
    setIntegral_congr_fun hR (fun t ht=> congrArg norm (hFR t ht))
  rw [heq] at hb'
  apply hb'.trans
  have hpow : (3+|H|)^2≤9*(height H)^2 := by
    have hh : 3+|H|≤3*height H := by unfold height;linarith [abs_nonneg H]
    have hh' := pow_le_pow_left₀ (by positivity) hh 2
    norm_num [mul_pow] at hh'
    exact hh'
  have hheight : 1+H=height H := by simp [height,abs_of_nonneg hH0]
  have hden : 0< height H := height_pos H
  rw [hheight]
  calc
    _ ≤ (9*A*(9*height H^2))*D*(X^(1/2-r)*Z^(σ+r-1)*Y^((1-a-6*e)-1))/height H^(N+2) := by
      gcongr
    _ = _ := by dsimp [A];rw [pow_add];field_simp;ring

end ProbeHighRowFamily

end

end

noncomputable section
open CubicSieve CenteredMomentFourier Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical BigOperators
open MeasureTheory Set Complex
namespace ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical ProbeMellinBoundary
local notation "O" => Eisenstein.O
variable {ι : Type*} [Fintype ι]

/-- The shifted row integral with both row heights truncated. -/
def centralRectangleIntegral {K : ℕ} (S : Finset (Ideal O)) (hS : SourceExclusions S)
    (hmax : ∀P∈S,P.IsMaximal) (P : Fin K→ HeckeIdealSeries.PrimeIdeal) (hPS : ∀i,(P i).val∉S)
    (η : Character) (u : FreeRow) (W0 W1 : SchwartzMap ℝ ℂ) (X Y Z a e H : ℝ) : ℂ :=
  ((1/(2*Real.pi):ℝ):ℂ)^3*
    ∫p : HeightSpace in {t : HeightSpace | |t.1.1|≤ H ∧ |t.2|≤ H},
      continuedRowOnLines S hS hmax P hPS η u W0 W1 X Y Z (a+16*e) (1-a-6*e) (17/50) p ∂heightMeasure

theorem central_row_w_cutoff_error (K : ℕ)
    (e : ℝ) (he : 0< e) (he' : e<1/1000)
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hmax : ∀P∈S,P.IsMaximal)
    (hfirst : FirstTail (4*e) S)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0< a0) (ha1 : 0< a1)
    (hW0 : Function.support W0⊆Icc a0 b0) (hW1 : Function.support W1⊆Icc a1 b1)
    (N : ℕ) :
    ∃C : ℝ,0≤ C ∧ ∀(η : Character) (u : FreeRow),u.val≠1 →
      ∀(P : Fin K→ HeckeIdealSeries.PrimeIdeal),Function.Injective P → ∀hPS : ∀j,(P j).val∉S,
      ∀ψ : ι→ Character,∀X Y Z : ℝ,0< X → 0< Y → 0< Z → ∀a B H : ℝ,∀i : ℕ,
      (51/100:ℝ)≤ a → a≤1 → 2< B → 0≤ H → H≤(3*i+2:ℕ)*B →
      detectorMaximum (sourceDetectorFamily S hS.prime η u ψ) (3*(i+1:ℕ)*B)< a+2*e →
      ‖centralRowIntegral S hS hmax P hPS η u W0 W1 X Y Z a e H-
        centralRectangleIntegral S hS hmax P hPS η u W0 W1 X Y Z a e H‖≤
        C*contourArithmeticCost η u P*(X^(1/2-(17/50:ℝ))*Z^(a+16*e+(17/50:ℝ)-1)*Y^((1-a-6*e)-1))/height H^N := by
  obtain ⟨C,hC,hbound⟩ := uniform_central_w_height_tail (ι:=ι) K e he he' S hS hmax hfirst
    W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1 N (17/50) le_rfl (by norm_num)
  let n : ℂ := ((1/(2*Real.pi):ℝ):ℂ)^3
  refine ⟨‖n‖*C,mul_nonneg (norm_nonneg _) hC,?_⟩
  intro η u hu P hP hPS ψ X Y Z hX hY hZ a B H i ha haTop hB hH0 hH hbin
  let E : Set HeightSpace := {t | |t.1.1|≤ H}
  let T : Set HeightSpace := {t | |t.1.1|≤ H ∧ |t.2|≤ H}
  let R : Set HeightSpace := {t | |t.1.1|≤ H ∧ H < |t.2|}
  let f := continuedRowOnLines S hS hmax P hPS η u W0 W1 X Y Z (a+16*e) (1-a-6*e) (17/50)
  have hE : MeasurableSet E := measurableSet_le (by fun_prop) measurable_const
  have hT : MeasurableSet T := hE.inter (measurableSet_le (show Measurable (fun t : HeightSpace => |t.2|) by fun_prop) measurable_const)
  have hi : IntegrableOn f E heightMeasure := continuedPhysicalRowKernel_buffered_integrable e a B H i he he' ha haTop hB hH
    S hS hmax hfirst P hPS η u hu ψ hbin W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1 X Y Z hX hY hZ
    (a+16*e) (17/50) le_rfl (by linarith) le_rfl
  have hdiff : E\T=R := by
    ext t
    change (|t.1.1|≤ H ∧ ¬(|t.1.1|≤ H ∧ |t.2|≤ H)) ↔ (|t.1.1|≤ H ∧ H < |t.2|)
    constructor
    · rintro ⟨hx,hw⟩
      exact ⟨hx,lt_of_not_ge (fun h=> hw ⟨hx,h⟩)⟩
    · rintro ⟨hx,hw⟩
      exact ⟨hx,fun h=> not_le_of_gt hw h.2⟩
  have heq : centralRowIntegral S hS hmax P hPS η u W0 W1 X Y Z a e H-
        centralRectangleIntegral S hS hmax P hPS η u W0 W1 X Y Z a e H=
      n*(∫t in R,f t ∂heightMeasure) := by
    rw [← hdiff,setIntegral_sdiff hT hi (fun t ht=> ht.1)]
    dsimp [centralRowIntegral,centralRectangleIntegral,n,E,T,f]
    ring
  rw [heq,norm_mul]
  calc
    _ ≤ ‖n‖*(∫t in R,‖f t‖ ∂heightMeasure) := mul_le_mul_of_nonneg_left (norm_integral_le_integral_norm _) (norm_nonneg _)
    _ ≤ ‖n‖*(C*contourArithmeticCost η u P*(X^(1/2-(17/50:ℝ))*Z^(a+16*e+(17/50:ℝ)-1)*Y^((1-a-6*e)-1))/height H^N) :=
      mul_le_mul_of_nonneg_left (hbound η u hu P hP hPS ψ X Y Z hX hY hZ a B H i ha haTop hB hH0 hH hbin
        (a+16*e) ⟨le_rfl,by linarith⟩) (norm_nonneg _)
    _ = _ := by ring

theorem uniform_original_row_rectangle_error (K : ℕ)
    (e : ℝ) (he : 0< e) (he' : e<1/1000)
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hmax : ∀P∈S,P.IsMaximal)
    (hfirst : FirstTail (4*e) S)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0< a0) (ha1 : 0< a1)
    (hW0 : Function.support W0⊆Icc a0 b0) (hW1 : Function.support W1⊆Icc a1 b1)
    (N : ℕ) :
    ∃C : ℝ,0≤ C ∧ ∀(η : Character) (u : FreeRow),u.val≠1 →
      ∀(P : Fin K→ HeckeIdealSeries.PrimeIdeal),Function.Injective P → ∀hPS : ∀j,(P j).val∉S,
      ∀ψ : ι→ Character,∀X Y Z : ℝ,0< X → 0< Y → 1≤ Z → ∀a B H : ℝ,∀i : ℕ,
      (51/100:ℝ)≤ a → a≤1 → 2< B → 0≤ H → H≤(3*i+2:ℕ)*B →
      detectorMaximum (sourceDetectorFamily S hS.prime η u ψ) (3*(i+1:ℕ)*B)< a+2*e →
      ‖rowIntegral η S (calibrationForSet S hmax) (fun j=> primaryIdealGenerator (P j).val) W0 W1 X Y Z u-
        centralRectangleIntegral S hS hmax P hPS η u W0 W1 X Y Z a e H‖≤
        C*contourArithmeticCost η u P*(X^(1/2-(17/50:ℝ))*Z^(2+(17/50:ℝ)-1)*Y^((1-a-6*e)-1))/height H^N := by
  obtain ⟨C0,hC0,h0⟩ := uniform_original_row_central_error (ι:=ι) K e he he' S hS hmax hfirst
    W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1 N
  obtain ⟨C1,hC1,h1⟩ := central_row_w_cutoff_error (ι:=ι) K e he he' S hS hmax hfirst
    W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1 N
  refine ⟨C0+C1,add_nonneg hC0 hC1,?_⟩
  intro η u hu P hP hPS ψ X Y Z hX hY hZ a B H i ha haTop hB hH0 hH hbin
  have h0' := h0 η u hu P hP hPS ψ X Y Z hX hY hZ a B H i ha haTop hB hH0 hH hbin
  have h1' := h1 η u hu P hP hPS ψ X Y Z hX hY (by linarith) a B H i ha haTop hB hH0 hH hbin
  have hcost := contourArithmeticCost_nonneg η u P
  have hz : Z^(a+16*e+(17/50:ℝ)-1)≤ Z^(2+(17/50:ℝ)-1) :=
    Real.rpow_le_rpow_of_exponent_le hZ (by linarith)
  have h1'' : ‖centralRowIntegral S hS hmax P hPS η u W0 W1 X Y Z a e H-
      centralRectangleIntegral S hS hmax P hPS η u W0 W1 X Y Z a e H‖≤
      C1*contourArithmeticCost η u P*(X^(1/2-(17/50:ℝ))*Z^(2+(17/50:ℝ)-1)*Y^((1-a-6*e)-1))/height H^N := by
    apply h1'.trans
    gcongr
    exact pow_nonneg (height_pos _).le _
  apply (norm_sub_le_norm_sub_add_norm_sub _ (centralRowIntegral S hS hmax P hPS η u W0 W1 X Y Z a e H) _).trans
  exact (add_le_add h0' h1'').trans_eq (by ring)

end ProbeHighRowFamily

end

end

noncomputable section
open CubicSieve CenteredMomentFourier Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical BigOperators
open MeasureTheory Set Complex
namespace ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical ProbeMellinBoundary
local notation "O" => Eisenstein.O
variable {ι : Type*} [Fintype ι]

/-- The shifted row integral with all three height coordinates truncated. -/
def centralCubeIntegral {K : ℕ} (S : Finset (Ideal O)) (hS : SourceExclusions S)
    (hmax : ∀P∈S,P.IsMaximal) (P : Fin K→ HeckeIdealSeries.PrimeIdeal) (hPS : ∀i,(P i).val∉S)
    (η : Character) (u : FreeRow) (W0 W1 : SchwartzMap ℝ ℂ) (X Y Z a e H : ℝ) : ℂ :=
  ((1/(2*Real.pi):ℝ):ℂ)^3*
    ∫p : HeightSpace in {t : HeightSpace | (|t.1.1|≤ H ∧ |t.2|≤ H) ∧ |t.1.2|≤ H},
      continuedRowOnLines S hS hmax P hPS η u W0 W1 X Y Z (a+16*e) (1-a-6*e) (17/50) p ∂heightMeasure

theorem central_rectangle_z_cutoff_error (K : ℕ)
    (e : ℝ) (he : 0< e) (he' : e<1/1000)
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hmax : ∀P∈S,P.IsMaximal)
    (hfirst : FirstTail (4*e) S)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0< a0) (ha1 : 0< a1)
    (hW0 : Function.support W0⊆Icc a0 b0) (hW1 : Function.support W1⊆Icc a1 b1)
    (N : ℕ) :
    ∃C : ℝ,0≤ C ∧ ∀(η : Character) (u : FreeRow),u.val≠1 →
      ∀(P : Fin K→ HeckeIdealSeries.PrimeIdeal),Function.Injective P → ∀hPS : ∀j,(P j).val∉S,
      ∀ψ : ι→ Character,∀X Y Z : ℝ,0< X → 0< Y → 0< Z → ∀a B H : ℝ,∀i : ℕ,
      (51/100:ℝ)≤ a → a≤1 → 2< B → 0≤ H → H≤(3*i+2:ℕ)*B →
      detectorMaximum (sourceDetectorFamily S hS.prime η u ψ) (3*(i+1:ℕ)*B)< a+2*e →
      ‖centralRectangleIntegral S hS hmax P hPS η u W0 W1 X Y Z a e H-
        centralCubeIntegral S hS hmax P hPS η u W0 W1 X Y Z a e H‖≤
        C*contourArithmeticCost η u P*(X^(1/2-(17/50:ℝ))*Z^(a+16*e+(17/50:ℝ)-1)*Y^((1-a-6*e)-1))/height H^N := by
  obtain ⟨C,hC,hbound⟩ := uniform_central_z_height_tail (ι:=ι) K e he he' S hS hmax hfirst
    W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1 N (17/50) le_rfl (by norm_num)
  let n : ℂ := ((1/(2*Real.pi):ℝ):ℂ)^3
  refine ⟨‖n‖*C,mul_nonneg (norm_nonneg _) hC,?_⟩
  intro η u hu P hP hPS ψ X Y Z hX hY hZ a B H i ha haTop hB hH0 hH hbin
  let E : Set HeightSpace := {t | |t.1.1|≤ H ∧ |t.2|≤ H}
  let T : Set HeightSpace := {t | (|t.1.1|≤ H ∧ |t.2|≤ H) ∧ |t.1.2|≤ H}
  let R : Set HeightSpace := {t | (|t.1.1|≤ H ∧ |t.2|≤ H) ∧ H < |t.1.2|}
  let f := continuedRowOnLines S hS hmax P hPS η u W0 W1 X Y Z (a+16*e) (1-a-6*e) (17/50)
  have hE : MeasurableSet E := (measurableSet_le (show Measurable (fun t : HeightSpace=>|t.1.1|) by fun_prop) measurable_const).inter
    (measurableSet_le (show Measurable (fun t : HeightSpace=>|t.2|) by fun_prop) measurable_const)
  have hT : MeasurableSet T := hE.inter (measurableSet_le (show Measurable (fun t : HeightSpace => |t.1.2|) by fun_prop) measurable_const)
  have hi0 : IntegrableOn f {t : HeightSpace | |t.1.1|≤ H} heightMeasure := continuedPhysicalRowKernel_buffered_integrable e a B H i he he' ha haTop hB hH
    S hS hmax hfirst P hPS η u hu ψ hbin W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1 X Y Z hX hY hZ
    (a+16*e) (17/50) le_rfl (by linarith) le_rfl
  have hi : IntegrableOn f E heightMeasure := hi0.mono_set (fun t ht=> ht.1)
  have hdiff : E\T=R := by
    ext t
    change ((|t.1.1|≤ H ∧ |t.2|≤ H) ∧ ¬((|t.1.1|≤ H ∧ |t.2|≤ H) ∧ |t.1.2|≤ H)) ↔ ((|t.1.1|≤ H ∧ |t.2|≤ H) ∧ H < |t.1.2|)
    constructor
    · rintro ⟨hx,hw⟩
      exact ⟨hx,lt_of_not_ge (fun h=> hw ⟨hx,h⟩)⟩
    · rintro ⟨hx,hw⟩
      exact ⟨hx,fun h=> not_le_of_gt hw h.2⟩
  have heq : centralRectangleIntegral S hS hmax P hPS η u W0 W1 X Y Z a e H-
        centralCubeIntegral S hS hmax P hPS η u W0 W1 X Y Z a e H=
      n*(∫t in R,f t ∂heightMeasure) := by
    rw [← hdiff,setIntegral_sdiff hT hi (fun t ht=> ht.1)]
    dsimp [centralRectangleIntegral,centralCubeIntegral,n,E,T,f]
    ring
  have htail : (∫t in R,‖f t‖ ∂heightMeasure)≤
      C*contourArithmeticCost η u P*(X^(1/2-(17/50:ℝ))*Z^(a+16*e+(17/50:ℝ)-1)*Y^((1-a-6*e)-1))/height H^N := by
    apply le_trans _ (hbound η u hu P hP hPS ψ X Y Z hX hY hZ a B H i ha haTop hB hH0 hH hbin
      (a+16*e) ⟨le_rfl,by linarith⟩)
    apply setIntegral_mono_set ((show IntegrableOn (fun t=>‖f t‖) {t : HeightSpace | |t.1.1|≤ H} heightMeasure from hi0.norm).mono_set (fun t ht=> ht.1)) (Filter.Eventually.of_forall (fun _=> norm_nonneg _))
    exact Filter.Eventually.of_forall (fun t ht=>⟨ht.1.1,ht.2⟩)
  rw [heq,norm_mul]
  calc
    _ ≤ ‖n‖*(∫t in R,‖f t‖ ∂heightMeasure) := mul_le_mul_of_nonneg_left (norm_integral_le_integral_norm _) (norm_nonneg _)
    _ ≤ ‖n‖*(C*contourArithmeticCost η u P*(X^(1/2-(17/50:ℝ))*Z^(a+16*e+(17/50:ℝ)-1)*Y^((1-a-6*e)-1))/height H^N) :=
      mul_le_mul_of_nonneg_left htail (norm_nonneg _)
    _ = _ := by ring

theorem uniform_original_row_cube_error (K : ℕ)
    (e : ℝ) (he : 0< e) (he' : e<1/1000)
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hmax : ∀P∈S,P.IsMaximal)
    (hfirst : FirstTail (4*e) S)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0< a0) (ha1 : 0< a1)
    (hW0 : Function.support W0⊆Icc a0 b0) (hW1 : Function.support W1⊆Icc a1 b1)
    (N : ℕ) :
    ∃C : ℝ,0≤ C ∧ ∀(η : Character) (u : FreeRow),u.val≠1 →
      ∀(P : Fin K→ HeckeIdealSeries.PrimeIdeal),Function.Injective P → ∀hPS : ∀j,(P j).val∉S,
      ∀ψ : ι→ Character,∀X Y Z : ℝ,0< X → 0< Y → 1≤ Z → ∀a B H : ℝ,∀i : ℕ,
      (51/100:ℝ)≤ a → a≤1 → 2< B → 0≤ H → H≤(3*i+2:ℕ)*B →
      detectorMaximum (sourceDetectorFamily S hS.prime η u ψ) (3*(i+1:ℕ)*B)< a+2*e →
      ‖rowIntegral η S (calibrationForSet S hmax) (fun j=> primaryIdealGenerator (P j).val) W0 W1 X Y Z u-
        centralCubeIntegral S hS hmax P hPS η u W0 W1 X Y Z a e H‖≤
        C*contourArithmeticCost η u P*(X^(1/2-(17/50:ℝ))*Z^(2+(17/50:ℝ)-1)*Y^((1-a-6*e)-1))/height H^N := by
  obtain ⟨C0,hC0,h0⟩ := uniform_original_row_rectangle_error (ι:=ι) K e he he' S hS hmax hfirst
    W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1 N
  obtain ⟨C1,hC1,h1⟩ := central_rectangle_z_cutoff_error (ι:=ι) K e he he' S hS hmax hfirst
    W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1 N
  refine ⟨C0+C1,add_nonneg hC0 hC1,?_⟩
  intro η u hu P hP hPS ψ X Y Z hX hY hZ a B H i ha haTop hB hH0 hH hbin
  have h0' := h0 η u hu P hP hPS ψ X Y Z hX hY hZ a B H i ha haTop hB hH0 hH hbin
  have h1' := h1 η u hu P hP hPS ψ X Y Z hX hY (by linarith) a B H i ha haTop hB hH0 hH hbin
  have hcost := contourArithmeticCost_nonneg η u P
  have hz : Z^(a+16*e+(17/50:ℝ)-1)≤ Z^(2+(17/50:ℝ)-1) :=
    Real.rpow_le_rpow_of_exponent_le hZ (by linarith)
  have h1'' : ‖centralRectangleIntegral S hS hmax P hPS η u W0 W1 X Y Z a e H-
      centralCubeIntegral S hS hmax P hPS η u W0 W1 X Y Z a e H‖≤
      C1*contourArithmeticCost η u P*(X^(1/2-(17/50:ℝ))*Z^(2+(17/50:ℝ)-1)*Y^((1-a-6*e)-1))/height H^N := by
    apply h1'.trans
    gcongr
    exact pow_nonneg (height_pos _).le _
  apply (norm_sub_le_norm_sub_add_norm_sub _ (centralRectangleIntegral S hS hmax P hPS η u W0 W1 X Y Z a e H) _).trans
  exact (add_le_add h0' h1'').trans_eq (by ring)

end ProbeHighRowFamily

end

end

noncomputable section
open CubicSieve CenteredMomentFourier Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical BigOperators
open MeasureTheory Set Complex
namespace ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical ProbeMellinBoundary
local notation "O" => Eisenstein.O
variable {ι : Type*} [Fintype ι]

lemma central_source_crude_scale {Z a e : ℝ} (hZ : 1≤ Z) (ha : 0≤ a) (he : 0≤ e) :
    (Z^(17/48:ℝ))^(1/2-(17/50:ℝ))*Z^(2+(17/50:ℝ)-1)*
      (Z^(23/48:ℝ))^((1-a-6*e)-1)≤ Z^(2:ℝ) := by
  have hZ0 : 0< Z := lt_of_lt_of_le zero_lt_one hZ
  simp_rw [←Real.rpow_mul hZ0.le]
  rw [←Real.rpow_add hZ0,←Real.rpow_add hZ0]
  exact Real.rpow_le_rpow_of_exponent_le hZ (by nlinarith)

lemma central_prime_product_bound {K : ℕ} (P : Fin K→ HeckeIdealSeries.PrimeIdeal)
    (Z b : ℝ) (hZ : 0< Z) (_hb : 0≤ b) (length : Fin K→ℝ)
    (hlength : ∑j,length j=(1/6:ℝ)) (hP : ∀j,((P j).val.absNorm:ℝ)≤ b*Z^(length j)) :
    (∏j,((P j).val.absNorm:ℝ))≤ b^K*Z^(1/6:ℝ) := by
  calc
    _ ≤ ∏j,b*Z^(length j) := Finset.prod_le_prod (fun j _=> Nat.cast_nonneg _) (fun j _=> hP j)
    _ = _ := by rw [Finset.prod_mul_distrib,Finset.prod_const,Finset.card_univ,Fintype.card_fin,←Real.rpow_sum_of_pos hZ,hlength]

lemma central_arithmetic_cost_bound {K : ℕ} (η : Character) (u : FreeRow) (P : Fin K→ HeckeIdealSeries.PrimeIdeal)
    (Z b ζ : ℝ) (hZ : 1≤ Z) (hb : 0≤ b) (hζ : ζ≤1/48)
    (hu : ((Ideal.span {u.val}:Ideal O).absNorm:ℝ)≤ Z^((13/16:ℝ)+ζ))
    (length : Fin K→ℝ) (hlength : ∑j,length j=(1/6:ℝ))
    (hP : ∀j,((P j).val.absNorm:ℝ)≤ b*Z^(length j)) :
    contourArithmeticCost η u P≤(η.modulus.absNorm:ℝ)^2*(b^K)^3*Z^(13/2:ℝ) := by
  have hZ0 : 0< Z := lt_of_lt_of_le zero_lt_one hZ
  have hu' : ((Ideal.span {u.val}:Ideal O).absNorm:ℝ)≤ Z :=
    hu.trans (by simpa using Real.rpow_le_rpow_of_exponent_le hZ (show (13/16:ℝ)+ζ≤1 by linarith))
  have hp := central_prime_product_bound P Z b hZ0 hb length hlength hP
  have hp0 : 0≤∏j,((P j).val.absNorm:ℝ) := Finset.prod_nonneg (fun j _=> Nat.cast_nonneg _)
  unfold contourArithmeticCost
  calc
    _ ≤ (η.modulus.absNorm:ℝ)^2*Z^6*(b^K*Z^(1/6:ℝ))^3 := by
      exact mul_le_mul (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (Nat.cast_nonneg _) hu' 6) (sq_nonneg _))
        (pow_le_pow_left₀ hp0 hp 3) (pow_nonneg hp0 3) (mul_nonneg (sq_nonneg _) (pow_nonneg hZ0.le 6))
    _ = _ := by
      rw [mul_pow,←Real.rpow_mul_natCast hZ0.le,←Real.rpow_natCast Z 6]
      have heq : Z^(6:ℝ)*Z^((1/6:ℝ)*(3:ℕ))=Z^(13/2:ℝ) := by rw [←Real.rpow_add hZ0];norm_num
      rw [←heq]
      norm_num only [Nat.cast_ofNat]
      ring

theorem original_row_rectangle_arbitrary_saving (K : ℕ) (τ saving b ζ : ℝ)
    (hτ : 0<τ) (hb : 0< b) (hζ : ζ≤1/48)
    (e : ℝ) (he : 0< e) (he' : e<1/1000)
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hmax : ∀P∈S,P.IsMaximal)
    (hfirst : FirstTail (4*e) S)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0< a0) (ha1 : 0< a1)
    (hW0 : Function.support W0⊆Icc a0 b0) (hW1 : Function.support W1⊆Icc a1 b1) :
    ∃C : ℝ,0≤ C ∧ ∀(η : Character) (u : FreeRow),u.val≠1 →
      ∀(P : Fin K→ HeckeIdealSeries.PrimeIdeal),Function.Injective P → ∀hPS : ∀j,(P j).val∉S,
      ∀ψ : ι→ Character,∀Z : ℝ,1≤ Z →
      ((Ideal.span {u.val}:Ideal O).absNorm:ℝ)≤ Z^((13/16:ℝ)+ζ) →
      ∀length : Fin K→ℝ,(∑j,length j)=(1/6:ℝ) →
      (∀j,((P j).val.absNorm:ℝ)≤ b*Z^(length j)) →
      ∀a B H : ℝ,∀i : ℕ,(51/100:ℝ)≤ a → a≤1 → 2< B → Z^τ≤ H → H≤(3*i+2:ℕ)*B →
      detectorMaximum (sourceDetectorFamily S hS.prime η u ψ) (3*(i+1:ℕ)*B)< a+2*e →
      ‖rowIntegral η S (calibrationForSet S hmax) (fun j=> primaryIdealGenerator (P j).val)
          W0 W1 (Z^(17/48:ℝ)) (Z^(23/48:ℝ)) Z u-
        centralRectangleIntegral S hS hmax P hPS η u W0 W1 (Z^(17/48:ℝ)) (Z^(23/48:ℝ)) Z a e H‖≤
        C*(η.modulus.absNorm:ℝ)^2*Z^(-saving) := by
  obtain ⟨N,hN⟩ := exists_nat_gt (((17/2:ℝ)+saving)/τ)
  have hN' : (17/2:ℝ)+saving<τ*N := by exact (div_lt_iff₀ hτ).mp hN |>.trans_eq (mul_comm _ _)
  obtain ⟨C,hC,hbound⟩ := uniform_original_row_rectangle_error (ι:=ι) K e he he' S hS hmax hfirst
    W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1 N
  refine ⟨C*(b^K)^3,mul_nonneg hC (pow_nonneg (pow_nonneg hb.le _) _),?_⟩
  intro η u hu P hP hPS ψ Z hZ huZ length hl hp a B H i ha haTop hB hHlo hH hbin
  have hZ0 : 0< Z := lt_of_lt_of_le zero_lt_one hZ
  have hH0 : 0≤ H := (Real.rpow_nonneg hZ0.le τ).trans hHlo
  have hmain := hbound η u hu P hP hPS ψ (Z^(17/48:ℝ)) (Z^(23/48:ℝ)) Z
    (Real.rpow_pos_of_pos hZ0 _) (Real.rpow_pos_of_pos hZ0 _) hZ a B H i ha haTop hB hH0 hH hbin
  have hcost := central_arithmetic_cost_bound η u P Z b ζ hZ hb.le hζ huZ length hl hp
  have hscale := central_source_crude_scale hZ (by linarith : 0≤ a) he.le
  have hden : Z^(τ*N)≤ height H^N := by
    rw [Real.rpow_mul_natCast hZ0.le]
    apply pow_le_pow_left₀ (Real.rpow_nonneg hZ0.le _) (hHlo.trans _) N
    simp only [height,abs_of_nonneg hH0]
    linarith
  have hsave : Z^(17/2:ℝ)/Z^(τ*N)≤ Z^(-saving) := by
    rw [←Real.rpow_sub hZ0]
    exact Real.rpow_le_rpow_of_exponent_le hZ (by linarith)
  apply hmain.trans
  calc
    _ ≤ C*((η.modulus.absNorm:ℝ)^2*(b^K)^3*Z^(13/2:ℝ))*Z^(2:ℝ)/height H^N := by
      apply div_le_div_of_nonneg_right _ (pow_nonneg (height_pos _).le _)
      exact mul_le_mul (mul_le_mul_of_nonneg_left hcost hC) hscale (by positivity) (by positivity)
    _ = (C*(b^K)^3*(η.modulus.absNorm:ℝ)^2)*(Z^(17/2:ℝ)/height H^N) := by
      have hh : Z^(13/2:ℝ)*Z^(2:ℝ)=Z^(17/2:ℝ) := by rw [←Real.rpow_add hZ0];norm_num
      rw [←hh]
      ring
    _ ≤ (C*(b^K)^3*(η.modulus.absNorm:ℝ)^2)*(Z^(17/2:ℝ)/Z^(τ*N)) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact div_le_div_of_nonneg_left (Real.rpow_nonneg hZ0.le _) (Real.rpow_pos_of_pos hZ0 _) hden
    _ ≤ _ := mul_le_mul_of_nonneg_left hsave (by positivity)

end ProbeHighRowFamily

end

end

noncomputable section
open CubicSieve CenteredMomentFourier Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical BigOperators
open MeasureTheory Set Complex
namespace ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical ProbeMellinBoundary
local notation "O" => Eisenstein.O
variable {ι : Type*} [Fintype ι]

lemma central_prime_tuple_count {K : ℕ} (T : Fin K→ Finset HeckeIdealSeries.PrimeIdeal)
    (Z b : ℝ) (hZ : 0< Z) (hb : 0≤ b) (length : Fin K→ℝ)
    (hl : ∑j,length j=(1/6:ℝ))
    (hT : ∀j P,P∈T j → (P.val.absNorm:ℝ)≤ b*Z^(length j)) :
    (Fintype.card (∀j,T j):ℝ)≤(128*b)^K*Z^(1/6:ℝ) := by
  have hc (j : Fin K) : ((T j).card:ℝ)≤128*b*Z^(length j) := by
    have hh := ProbeSelectedPrimeSums.finite_ideal_count ((T j).image Subtype.val) (b*Z^(length j)) (by positivity)
      (by intro I hI;obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hI;exact p.property.ne_zero)
      (by intro I hI;obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hI;exact hT j p hp)
    simpa only [Finset.card_image_of_injective _ Subtype.val_injective,mul_assoc] using hh
  rw [Fintype.card_pi,Nat.cast_prod]
  simp only [Fintype.card_coe]
  calc
    _ ≤ ∏j,128*b*Z^(length j) := Finset.prod_le_prod (fun j _=> Nat.cast_nonneg _) (fun j _=> hc j)
    _ = _ := by rw [Finset.prod_mul_distrib,Finset.prod_const,Finset.card_univ,Fintype.card_fin,←Real.rpow_sum_of_pos hZ,hl]

/-- The finite weighted sum of truncated row integrals. -/
def finiteCentralRectangleRows {K : ℕ} (S : Finset (Ideal O)) (hS : SourceExclusions S)
    (hmax : ∀P∈S,P.IsMaximal) (η : Character) (R : Finset FreeRow)
    (T : Fin K→ Finset HeckeIdealSeries.PrimeIdeal) (hT : ∀i P,P∈T i → P.val∉S)
    (W : Fin K→ℝ→ℂ) (Yp : Fin K→ℝ) (W0 W1 : SchwartzMap ℝ ℂ)
    (X Y Z e : ℝ) (a H : FreeRow→ℝ) : ℂ :=
  ∑u∈R,∑P:(∀i,T i),(∏i,W i (((P i).val.val.absNorm:ℝ)/Yp i))*
    centralRectangleIntegral S hS hmax (fun i=>(P i).val) (fun i=> hT i _ (P i).property)
      η u W0 W1 X Y Z (a u) e (H u)

theorem finite_rectangle_arbitrary_saving (K : ℕ) (τ saving b ζ A : ℝ)
    (hτ : 0<τ) (hb : 0< b) (hζ : ζ≤1/48) (hA : 0≤ A)
    (e : ℝ) (he : 0< e) (he' : e<1/1000)
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hmax : ∀P∈S,P.IsMaximal)
    (hfirst : FirstTail (4*e) S)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0< a0) (ha1 : 0< a1)
    (hW0 : Function.support W0⊆Icc a0 b0) (hW1 : Function.support W1⊆Icc a1 b1) :
    ∃C : ℝ,0≤ C ∧ ∀(η : Character) (Z : ℝ),1≤ Z → ∀R : Finset FreeRow,
      (∀u∈R,u.val≠1 ∧ ((Ideal.span {u.val}:Ideal O).absNorm:ℝ)≤ Z^((13/16:ℝ)+ζ)) →
      ∀(T : Fin K→ Finset HeckeIdealSeries.PrimeIdeal) (hT : ∀i P,P∈T i → P.val∉S),
      (∀P:(∀i,T i),Function.Injective (fun i=>(P i).val)) →
      ∀length : Fin K→ℝ,(∑j,length j)=(1/6:ℝ) →
      (∀j P,P∈T j → (P.val.absNorm:ℝ)≤ b*Z^(length j)) →
      ∀W : Fin K→ℝ→ℂ,(∀j y,‖W j y‖≤ A) →
      ∀(a B H : FreeRow→ℝ) (idx : FreeRow→ℕ) (ψ : FreeRow→ι→ Character),
      (∀u∈R,(51/100:ℝ)≤ a u ∧ a u≤1 ∧ 2< B u ∧ Z^τ≤ H u ∧ H u≤(3*idx u+2:ℕ)*B u ∧
        detectorMaximum (sourceDetectorFamily S hS.prime η u (ψ u)) (3*(idx u+1:ℕ)*B u)< a u+2*e) →
      ‖finitePhysicalRows S hmax η R T W (fun j=> Z^(length j)) W0 W1 (Z^(17/48:ℝ)) (Z^(23/48:ℝ)) Z-
        finiteCentralRectangleRows S hS hmax η R T hT W (fun j=> Z^(length j)) W0 W1
          (Z^(17/48:ℝ)) (Z^(23/48:ℝ)) Z e a H‖≤ C*(η.modulus.absNorm:ℝ)^2*Z^(-saving) := by
  obtain ⟨C,hC,hrow⟩ := original_row_rectangle_arbitrary_saving (ι:=ι) K τ (saving+2) b ζ hτ hb hζ e he he'
    S hS hmax hfirst W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
  refine ⟨128*(128*b)^K*A^K*C,by positivity,?_⟩
  intro η Z hZ R hR T hT hdis length hl hp W hW a B H idx ψ hbin
  have hZ0 : 0< Z := lt_of_lt_of_le zero_lt_one hZ
  have hrange : Z^((13/16:ℝ)+ζ)≤ Z := by
    simpa using Real.rpow_le_rpow_of_exponent_le hZ (show (13/16:ℝ)+ζ≤1 by linarith)
  have hcR : (R.card:ℝ)≤128*Z := freeRow_count R Z hZ (by
    intro u hu
    exact (hR u hu).2.trans hrange)
  have hcT : (Fintype.card (∀j,T j):ℝ)≤(128*b)^K*Z :=
    (central_prime_tuple_count T Z b hZ0 hb.le length hl hp).trans
      (mul_le_mul_of_nonneg_left (by simpa using Real.rpow_le_rpow_of_exponent_le hZ (show (1/6:ℝ)≤1 by norm_num)) (by positivity))
  let E := C*(η.modulus.absNorm:ℝ)^2*Z^(-(saving+2))
  have hE : 0≤ E := by dsimp [E];positivity
  have herr (u : FreeRow) (hu : u∈R) (P : ∀j,T j) :
      ‖rowIntegral η S (calibrationForSet S hmax) (fun j=> primaryIdealGenerator (P j).val.val)
          W0 W1 (Z^(17/48:ℝ)) (Z^(23/48:ℝ)) Z u-
        centralRectangleIntegral S hS hmax (fun j=>(P j).val) (fun j=> hT j _ (P j).property)
          η u W0 W1 (Z^(17/48:ℝ)) (Z^(23/48:ℝ)) Z (a u) e (H u)‖≤ E := by
    rcases hbin u hu with ⟨ha,ha',hB,hHlo,hH,hzero⟩
    exact hrow η u (hR u hu).1 (fun j=>(P j).val) (hdis P) (fun j=> hT j _ (P j).property)
      (ψ u) Z hZ (hR u hu).2 length hl (fun j=> hp j _ (P j).property)
      (a u) (B u) (H u) (idx u) ha ha' hB hHlo hH hzero
  have hw (P : ∀j,T j) : ‖∏j,W j (((P j).val.val.absNorm:ℝ)/Z^(length j))‖≤ A^K := by
    rw [norm_prod]
    calc
      _ ≤ ∏j : Fin K,A := Finset.prod_le_prod (fun j _=> norm_nonneg _) (fun j _=> hW j _)
      _ = _ := by simp
  unfold finitePhysicalRows finiteCentralRectangleRows
  rw [←Finset.sum_sub_distrib]
  calc
    _ ≤ ∑u∈R,‖(∑P:(∀j,T j),(∏j,W j (((P j).val.val.absNorm:ℝ)/Z^(length j)))*
        rowIntegral η S (calibrationForSet S hmax) (fun j=> primaryIdealGenerator (P j).val.val) W0 W1 (Z^(17/48:ℝ)) (Z^(23/48:ℝ)) Z u)-
      ∑P:(∀j,T j),(∏j,W j (((P j).val.val.absNorm:ℝ)/Z^(length j)))*
        centralRectangleIntegral S hS hmax (fun j=>(P j).val) (fun j=> hT j _ (P j).property)
          η u W0 W1 (Z^(17/48:ℝ)) (Z^(23/48:ℝ)) Z (a u) e (H u)‖ := norm_sum_le _ _
    _ ≤ ∑_u∈R,∑_P:(∀j,T j),A^K*E := by
      apply Finset.sum_le_sum
      intro u hu
      rw [←Finset.sum_sub_distrib]
      apply (norm_sum_le _ _).trans
      apply Finset.sum_le_sum
      intro P hP
      rw [←mul_sub,norm_mul]
      exact mul_le_mul (hw P) (herr u hu P) (norm_nonneg _) (pow_nonneg hA _)
    _ = (R.card:ℝ)*(Fintype.card (∀j,T j):ℝ)*(A^K*E) := by simp;ring
    _ ≤ (128*Z)*((128*b)^K*Z)*(A^K*E) := by
      exact mul_le_mul_of_nonneg_right (mul_le_mul hcR hcT (Nat.cast_nonneg _) (by positivity)) (mul_nonneg (pow_nonneg hA _) hE)
    _ = _ := by
      have hz : Z^2*Z^(-(saving+2))=Z^(-saving) := by
        rw [←Real.rpow_two,←Real.rpow_add hZ0]
        congr 1
        ring
      dsimp [E]
      calc
        _ = (128*(128*b)^K*A^K*C*(η.modulus.absNorm:ℝ)^2)*(Z^2*Z^(-(saving+2))) := by ring
        _ = _ := by rw [hz]

end ProbeHighRowFamily

end

end

end GaloisForLFunctions.MetaplecticMobiusDescent.CubicEisenstein
