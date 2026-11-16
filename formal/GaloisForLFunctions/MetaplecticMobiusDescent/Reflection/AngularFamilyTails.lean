import GaloisForLFunctions.MetaplecticMobiusDescent.Inversion.AngularArithmeticTails
import GaloisForLFunctions.MetaplecticMobiusDescent.Reflection.AngularWholeRows
import GaloisForLFunctions.MetaplecticMobiusDescent.Reflection.UniformDegreeBudgets

/-!
# Uniform truncation of whole angular reflected rows

The angular denominator is a bounded weight independent of the dyadic variable.
Absolute convergence and radial decay give the original family and whole-row tail
costs, with one polynomial height order across all arithmetic data.
-/

open scoped BigOperators Classical ContDiff ComplexConjugate
namespace GaloisForLFunctions.MetaplecticMobiusDescent.CubicEisenstein
open Eisenstein CubicJacobi CubicKubota CubicRamified RationalSource CompletedGauss
open CompletedDyadic CanonicalRowCompletion SchwartzPlanePoisson NormalizedReflection
open CanonicalQuadraticSieve InverseMoment
namespace InverseReflectedPhase
noncomputable section
local notation "Eis" => Eisenstein.O
universe u v

theorem angular_original_family_dyadic_tail_uniform_degree (ℓ : ℕ) (lo hi : ℝ) (hlo : 0< lo) (A : ℕ)
    (W : ℝ→ℂ) (hWs : Function.support W⊆Set.Icc lo hi) (hW : ContDiff ℝ ∞ W) :
    ∃ (degree : ℕ) (C : ℝ), 0< C ∧
    ∀ {N a c : Eis} {mode : Bool}, ∀ {φ : Type u} {σ : Type v} [Fintype φ] [Fintype σ]
      (F : PrimeFamily φ) (K : Ideal Eis) (hK : Admissible K) (S : PrimeFamily σ)
      (D : ControlledStratumArithmetic (F.reflected K hK S).generator N a c mode)
      (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode)) (hc : c≠0),
      (9:Eis)*c∣N → (if mode then lambda^2∣a-1 else lambda^2∣c-1) →
      (∀ i, ringChar (Eis⧸(F.reflected K hK S).ideal i)≠2) →
    ∀ jF : φ→ℕ, (∀ i, jF i<6) → ∀ (u : Eisˣ) (θ X T QK QP : ℝ),
      0< X → 0< T → 0< QK → 0< QP →
      (Ideal.absNorm K:ℝ)≤ QK → (Ideal.absNorm (∏ i,S.ideal i):ℝ)≤ QP →
      ‖∑' i : ℕ×ℕ×ℕ, if i∉retainedDyads (familyRawScale F s X QK QP) (16*T) then
        angularLiteralDyadicBlock ℓ (F.reflected K hK S) D s hc (reflectedExponent jF)
          (slotIndices φ (PrimeIndex K) σ) (CompletedHeight.normTwistedSource W θ) X u i else 0‖≤
        C*(1+‖θ‖)^degree*((Ideal.absNorm (∏ i,F.ideal i):ℝ)*QK*QP)*
          T^(-(A:ℝ))*(familyRawScale F s X QK QP^2)⁻¹ := by
  obtain ⟨degree,C,hC,hbound⟩ := InverseReflectedArithmeticHeight.angular_literal_dyadic_tail_height_arithmetic_uniform ℓ lo hi hlo A W hWs hW
  refine ⟨degree,C,hC,?_⟩
  intro N a c mode φ σ _ _ F K hK S D s hc hN hbase hchar jF hj u θ X T QK QP hX hT hQK hQP hKr hPr
  have hs := familyRawScale_le_literal F K hK S s hc X QK QP hX hKr hPr
  have hsp := familyRawScale_pos F s hc X QK QP hX hQK hQP
  have hcut (i : ℕ×ℕ×ℕ) (hi : i∉retainedDyads (familyRawScale F s X QK QP) (16*T)) :
      16*T≤ rawDyadicCenter (literalRawScale (F.reflected K hK S) s X) i := by
    have hlt := lt_of_not_ge (fun h => hi ((mem_retainedDyads _ _ hsp i).mpr h))
    apply hlt.le.trans
    unfold rawDyadicCenter
    rw [ramifiedScale_one_cube]
    gcongr
  have hj' : ∀ i : φ ⊕ (PrimeIndex K ⊕ σ), reflectedExponent jF i<6 := by
    intro i
    rcases i with f | k | p
    · exact hj f
    · norm_num [reflectedExponent]
    · norm_num [reflectedExponent]
  have hh := hbound (N:=N) (a:=a) (c:=c) (mode:=mode) (F.reflected K hK S) D s hc hN hbase hchar (reflectedExponent jF) hj'
    (slotIndices φ (PrimeIndex K) σ) u θ X T hX hT
    (fun i => i∉retainedDyads (familyRawScale F s X QK QP) (16*T)) hcut
  have hleft : ‖∑' i : ℕ×ℕ×ℕ, if i∉retainedDyads (familyRawScale F s X QK QP) (16*T) then
        angularLiteralDyadicBlock ℓ (F.reflected K hK S) D s hc (reflectedExponent jF)
          (slotIndices φ (PrimeIndex K) σ) (CompletedHeight.normTwistedSource W θ) X u i else 0‖≤
      C*(1+‖θ‖)^degree*(Ideal.absNorm (∏ i,(F.reflected K hK S).ideal i):ℝ)*T^(-(A:ℝ))*
        (literalRawScale (F.reflected K hK S) s X^2)⁻¹ := by
    apply le_trans ?_ hh
    apply le_of_eq
    congr 1
    apply tsum_congr
    intro i
    by_cases hi : i∈retainedDyads (familyRawScale F s X QK QP) (16*T) <;> simp [hi]
  apply hleft.trans
  have hnorm := reflected_norm_le_centers F K hK S QK QP hKr hPr
  gcongr

theorem angular_original_family_row_tail_uniform_degree (ℓ : ℕ) (lo hi : ℝ) (hlo : 0< lo) (A : ℕ)
    (W : ℝ→ℂ) (hWs : Function.support W⊆Set.Icc lo hi) (hW : ContDiff ℝ ∞ W) :
    ∃ (degree : ℕ) (C : ℝ), 0< C ∧
    ∀ {N a c : Eis} {mode : Bool}, ∀ {φ : Type u} {σ : Type v} [Fintype φ] [Fintype σ]
      (F : PrimeFamily φ) (K : Ideal Eis) (hK : Admissible K)
      (S : Ideal Eis→PrimeFamily σ) (jF : φ→ℕ) (Pset : Finset (Ideal Eis))
      (D : ∀ P : Pset, IsCoprime K P.val →
        ControlledStratumArithmetic (F.reflected K hK (S P.val)).generator N a c mode)
      (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode)) (hc : c≠0),
      (9:Eis)*c∣N → (if mode then lambda^2∣a-1 else lambda^2∣c-1) →
      (∀ P∈Pset, ∀ i, ringChar (Eis⧸(F.reflected K hK (S P)).ideal i)≠2) →
      (∀ i,jF i<6) → (∀ P∈Pset,(∏ j,(S P).ideal j)=P) →
    ∀ (u : Eisˣ) (θ X T QK QP : ℝ) (r aw : Ideal Eis→ℂ),
      0< X → 0< T → 0< QK → 0< QP →
      (Ideal.absNorm K:ℝ)≤ QK → (∀ P∈Pset,(Ideal.absNorm P:ℝ)≤ QP) →
      ‖r K‖≤1 → (∀ P∈Pset,‖aw P‖≤1) →
      ‖(∑' i : ℕ×ℕ×ℕ,angularLiteralDyadicRow ℓ F K hK S jF Pset D s hc u i W θ X r aw)-
        ∑ i∈retainedDyads (familyRawScale F s X QK QP) (16*T),
          angularLiteralDyadicRow ℓ F K hK S jF Pset D s hc u i W θ X r aw‖≤
        Pset.card*(C*(1+‖θ‖)^degree*((Ideal.absNorm (∏ i,F.ideal i):ℝ)*QK*QP)*
          T^(-(A:ℝ))*(familyRawScale F s X QK QP^2)⁻¹) := by
  obtain ⟨degree,C,hC,hbound⟩ := angular_original_family_dyadic_tail_uniform_degree ℓ lo hi hlo A W hWs hW
  refine ⟨degree,C,hC,?_⟩
  intro N a c mode φ σ _ _ F K hK S jF Pset D s hc hN hbase hchar hj hprod u θ X T QK QP r aw hX hT hQK hQP hKr hPr hr haw
  let L := {P : Pset // IsCoprime K P.val}
  let block := fun (P : L) i => angularLiteralDyadicBlock ℓ (F.reflected K hK (S P.val.val))
    (D P.val P.property) s hc (reflectedExponent jF) (slotIndices φ (PrimeIndex K) σ)
    (CompletedHeight.normTwistedSource W θ) X u i
  let J := retainedDyads (familyRawScale F s X QK QP) (16*T)
  have htw : ContDiff ℝ ∞ (CompletedHeight.normTwistedSource W θ) := by
    have he : (CompletedHeight.uniformTwistedSchwartz W lo hi hlo hWs hW θ:ℝ→ℂ)=
        CompletedHeight.normTwistedSource W θ := by
      funext x
      exact CompletedHeight.uniformTwistedSchwartz_apply W lo hi hlo hWs hW θ x
    rw [←he]
    exact (CompletedHeight.uniformTwistedSchwartz W lo hi hlo hWs hW θ).smooth ⊤
  have hj' : ∀ i : φ ⊕ (PrimeIndex K ⊕ σ), reflectedExponent jF i<6 := by
    intro i
    rcases i with f | k | p
    · exact hj f
    · norm_num [reflectedExponent]
    · norm_num [reflectedExponent]
  have hs (P : L) : Summable (block P) :=
    angularLiteralDyadicBlock_summable ℓ (F.reflected K hK (S P.val.val)) (D P.val P.property) s hc hN hbase
      (hchar P.val.val P.val.property) (reflectedExponent jF) hj' (slotIndices φ (PrimeIndex K) σ)
      (CompletedHeight.normTwistedSource W θ) lo hi hlo
      ((CompletedHeight.normTwistedSource_support W θ).trans hWs) htw X hX u
  have he (P : L) : ‖(∑' i,block P i)-∑ i∈J,block P i‖≤
      C*(1+‖θ‖)^degree*((Ideal.absNorm (∏ i,F.ideal i):ℝ)*QK*QP)*
        T^(-(A:ℝ))*(familyRawScale F s X QK QP^2)⁻¹ := by
    rw [tsum_sub_finset_eq_tail (block P) (hs P) J]
    have hh := hbound F K hK (S P.val.val) (D P.val P.property) s hc hN hbase
      (hchar P.val.val P.val.property) jF hj u θ X T QK QP hX hT hQK hQP hKr
      (by rw [hprod P.val.val P.val.property]; exact hPr P.val.val P.val.property)
    apply le_trans ?_ hh
    apply le_of_eq
    congr 1
    apply tsum_congr
    intro i
    by_cases hi : i∈J <;> simp [J] at hi ⊢ <;> simp [hi,block]
  let wt := fun P : L => r K*aw P.val.val*
    angularCuspDenominatorPhase ℓ (c*∏ j,(F.reflected K hK (S P.val.val)).generator j)
  have hw (P : L) : ‖wt P‖≤1 := by
    have hrw : ‖r K*aw P.val.val‖≤1 := by
      rw [norm_mul]
      exact (mul_le_mul hr (haw P.val.val P.val.property) (norm_nonneg _) zero_le_one).trans_eq (one_mul 1)
    rw [wt,norm_mul]
    exact (mul_le_mul hrw (angularCuspDenominatorPhase_norm_le_one ℓ _) (norm_nonneg _) zero_le_one).trans_eq (one_mul 1)
  have hh := finite_weighted_truncation_norm block wt J _ hs hw he
  change ‖(∑' i,∑ P : L,wt P*block P i)-∑ i∈J,∑ P : L,wt P*block P i‖≤ _
  apply hh.trans
  apply mul_le_mul_of_nonneg_right
  · exact_mod_cast (Fintype.card_subtype_le (fun P : Pset => IsCoprime K P.val)).trans_eq (Fintype.card_coe Pset)
  · positivity

theorem angular_original_family_whole_tail_uniform_degree (ℓ : ℕ) (lo hi : ℝ) (hlo : 0< lo) (A : ℕ)
    (W : ℝ→ℂ) (hWs : Function.support W⊆Set.Icc lo hi) (hW : ContDiff ℝ ∞ W) :
    ∃ (degree : ℕ) (C : ℝ), 0< C ∧
    ∀ {N a c : Eis} {mode : Bool}, ∀ {φ : Type u} {σ : Type v} [Fintype φ] [Fintype σ]
      (F : PrimeFamily φ) (K : Ideal Eis) (hK : Admissible K)
      (S : Ideal Eis→PrimeFamily σ) (jF : φ→ℕ) (Pset : Finset (Ideal Eis))
      (D : ∀ P : Pset, IsCoprime K P.val →
        ControlledStratumArithmetic (F.reflected K hK (S P.val)).generator N a c mode)
      (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode)) (hc : c≠0),
      (9:Eis)*c∣N → (if mode then lambda^2∣a-1 else lambda^2∣c-1) →
      (∀ P∈Pset, ∀ i, ringChar (Eis⧸(F.reflected K hK (S P)).ideal i)≠2) →
      (∀ i,jF i<6) → (∀ P∈Pset,(∏ j,(S P).ideal j)=P) →
      (∀ P∈Pset,CubicSieve.Admissible P) →
    ∀ (θ X T QK QP : ℝ) (r aw : Ideal Eis→ℂ),
      0< X → 0< T → 0< QK → 0< QP →
      (Ideal.absNorm K:ℝ)≤ QK → (∀ P∈Pset,(Ideal.absNorm P:ℝ)≤ QP) →
      ‖r K‖≤1 → (∀ P∈Pset,‖aw P‖≤1) →
      ‖angularLiteralWholeRow ℓ F K hK S jF Pset D s hc W θ X r aw-
        (fixedRadialCoefficientScalar*s.stratumShapeFactor (c*primaryIdealGenerator (∏ i,F.ideal i)))*
          ∑' u : Eisˣ,∑ i∈retainedDyads (familyRawScale F s X QK QP) (16*T),
            angularLiteralDyadicRow ℓ F K hK S jF Pset D s hc u i W θ X
              (fun K => r K*shapeArgument (primaryIdealGenerator K))
              (fun P => aw P*shapeArgument (primaryIdealGenerator P))‖≤
        (6*‖fixedRadialCoefficientScalar‖*‖s.stratumShapeFactor c‖)*Pset.card*
          (C*(1+‖θ‖)^degree*((Ideal.absNorm (∏ i,F.ideal i):ℝ)*QK*QP)*
            T^(-(A:ℝ))*(familyRawScale F s X QK QP^2)⁻¹) := by
  obtain ⟨degree,C,hC,hbound⟩ := angular_original_family_row_tail_uniform_degree ℓ lo hi hlo A W hWs hW
  refine ⟨degree,C,hC,?_⟩
  intro N a c mode φ σ _ _ F K hK S jF Pset D s hc hN hbase hchar hj hprod hPad θ X T QK QP r aw hX hT hQK hQP hKr hPr hr haw
  let : Finite Eisˣ := cubic_units_finite
  let : Fintype Eisˣ := Fintype.ofFinite _
  let J := retainedDyads (familyRawScale F s X QK QP) (16*T)
  let rr := fun K => r K*shapeArgument (primaryIdealGenerator K)
  let aa := fun P => aw P*shapeArgument (primaryIdealGenerator P)
  let E := C*(1+‖θ‖)^degree*((Ideal.absNorm (∏ i,F.ideal i):ℝ)*QK*QP)*
    T^(-(A:ℝ))*(familyRawScale F s X QK QP^2)⁻¹
  have hb (v : Eisˣ) :
      ‖(∑' i,angularLiteralDyadicRow ℓ F K hK S jF Pset D s hc v i W θ X rr aa)-
        ∑ i∈J,angularLiteralDyadicRow ℓ F K hK S jF Pset D s hc v i W θ X rr aa‖≤ Pset.card*E :=
    hbound (N:=N) (a:=a) (c:=c) (mode:=mode) F K hK S jF Pset D s hc hN hbase hchar hj hprod v θ X T QK QP rr aa hX hT hQK hQP hKr hPr
      (by simpa only [rr,row_shape_weight_norm r K hK] using hr)
      (fun P hp => by simpa only [aa,slot_shape_weight_norm aw P (hPad P hp)] using haw P hp)
  have hcard : (Fintype.card Eisˣ : ℝ) ≤ 6 := by
    exact_mod_cast EisensteinLatticeCount.card_units_le_six
  rw [angularLiteralWholeRow_eq_dyadic ℓ F K hK S jF Pset D s hc hN hbase hchar hj hprod W lo hi hlo hWs hW θ X hX r aw]
  rw [←mul_sub,norm_mul, norm_mul,stratumShapeFactor_frozen_norm]
  simp only [tsum_fintype]
  rw [←Finset.sum_sub_distrib]
  calc
    _ ≤ (‖fixedRadialCoefficientScalar‖*‖s.stratumShapeFactor c‖)*
        ∑ v : Eisˣ,‖(∑' i,angularLiteralDyadicRow ℓ F K hK S jF Pset D s hc v i W θ X rr aa)-
          ∑ i∈J,angularLiteralDyadicRow ℓ F K hK S jF Pset D s hc v i W θ X rr aa‖ := by
      exact mul_le_mul_of_nonneg_left (norm_sum_le _ _) (by positivity)
    _ ≤ (‖fixedRadialCoefficientScalar‖*‖s.stratumShapeFactor c‖)*∑ _v : Eisˣ,Pset.card*E := by
      exact mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun v _ => hb v)) (by positivity)
    _ ≤ (‖fixedRadialCoefficientScalar‖*‖s.stratumShapeFactor c‖)*(6*(Pset.card*E)) := by
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact mul_le_mul_of_nonneg_right hcard (by dsimp only [E]; positivity)
    _ = _ := by dsimp only [E]; ring

end
end InverseReflectedPhase
end GaloisForLFunctions.MetaplecticMobiusDescent.CubicEisenstein
