/-
Closed forms of the high rows adapted from OpenAI's formalization, Apache-2.0.
See LICENSE and NOTICE in the parent directory for source attribution.
-/
import GaloisForLFunctions.MetaplecticMobiusDescent.Detector.CompensatedRows

/-!
# Closed forms of the high rows

Closed marked row series and ramified closed corrections; first-region halves of the Euler
coordinates; small and large ramified selected bounds and compensated phase errors.
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
open scoped Classical BigOperators
namespace ProbePrimePower
open Eisenstein CompletedGauss 
local notation "O" => Eisenstein.O

lemma gaussValuationTable_above (Q G : ℂ) (r n j : ℕ) (hj : n+1≤ j) :
    gaussValuationTable Q G r n j=if 6∣r then Q^(n+1)-Q^n else 0 := by
  unfold gaussValuationTable
  by_cases hd : 6∣r
  · rw [if_pos hd,if_pos hd,if_pos hj,if_pos (by omega)]
  · rw [if_neg hd,if_neg hd,if_neg (by omega)]

theorem positiveScalar_stable_large (p : O) (hp : Prime p)
    [(Ideal.span {p}:Ideal O).IsMaximal] (hg : lambda∉Ideal.span {p})
    (hc : ringChar (O ⧸ Ideal.span {p})≠2) (n k j j' : ℕ)
    (hj : n+1< j) (hj' : n+1< j') :
    positiveScalar p hp.ne_zero (complexSexticChar (Ideal.span {p}) hg) n k j=
      positiveScalar p hp.ne_zero (complexSexticChar (Ideal.span {p}) hg) n k j' := by
  simp only [positiveScalar_actual_table p hp hg hc,
    show 1≤ j by omega,show 1≤ j' by omega,and_true,
    gaussValuationTable_above _ _ _ n j (by omega),
    gaussValuationTable_above _ _ _ n j' (by omega),
    gaussValuationTable_above _ _ _ n (j-1) (by omega),
    gaussValuationTable_above _ _ _ n (j'-1) (by omega)]

end ProbePrimePower
namespace ProbeEuler
open Eisenstein CompletedGauss  ProbePrimePower
local notation "O" => Eisenstein.O
variable (p : O) (hp : Prime p) [(Ideal.span {p}:Ideal O).IsMaximal]
  (hg : lambda∉Ideal.span {p}) (hc : ringChar (O ⧸ Ideal.span {p})≠2)
include hc

theorem rowMarkedTerm_base_tail (eta a X W V rho : ℂ)
    (j e l k m : ℕ) (ht : 0< e+3*l) (ht6 : e+3*l≤6) :
    rowMarkedTerm p hp hg eta a X W V rho j e l k (m+2)=
      rowMarkedTerm p hp hg eta a X W V rho j e l k 2*V^m := by
  unfold rowMarkedTerm
  rw [if_neg (by omega),if_neg (by omega),
    ProbePrimePower.positiveScalar_stable_large p hp hg hc (e+3*l-1) k (j+6*(m+2)) (j+6*2) (by omega) (by omega)]
  unfold rowWeightedScalar weightedScalar
  rw [pow_add V m 2]
  ring

theorem rowInner_base_rational (eta a X W V rho : ℂ) (hV : ‖V‖<1)
    (j e l : ℕ) (ht : 0< e+3*l) (ht6 : e+3*l≤6) :
    rowInner p hp hg eta a X W V rho j e l=
      ∑ k : Fin 2,
        (rowMarkedTerm p hp hg eta a X W V rho j e l k.val 0+
         rowMarkedTerm p hp hg eta a X W V rho j e l k.val 1+
         rowMarkedTerm p hp hg eta a X W V rho j e l k.val 2/(1-V)) := by
  have hsum (k : ℕ) : (∑' m,rowMarkedTerm p hp hg eta a X W V rho j e l k m)=
      rowMarkedTerm p hp hg eta a X W V rho j e l k 0+
      rowMarkedTerm p hp hg eta a X W V rho j e l k 1+
      rowMarkedTerm p hp hg eta a X W V rho j e l k 2/(1-V) := by
    have ht' : HasSum (fun m=> rowMarkedTerm p hp hg eta a X W V rho j e l k (m+2))
        (rowMarkedTerm p hp hg eta a X W V rho j e l k 2/(1-V)) := by
      have hgeo := (hasSum_geometric_of_norm_lt_one hV).mul_left (rowMarkedTerm p hp hg eta a X W V rho j e l k 2)
      rw [←div_eq_mul_inv] at hgeo
      exact hgeo.congr_fun fun m =>
        rowMarkedTerm_base_tail p hp hg hc eta a X W V rho j e l k m ht ht6
    have h := ht'.sum_range_add (f:=fun m=> rowMarkedTerm p hp hg eta a X W V rho j e l k m) (k:=2)
    simpa only [Finset.sum_range_succ,Finset.sum_range_zero,zero_add] using h.tsum_eq
  rw [rowInner_two,hsum 0,hsum 1]
  simp only [Fin.sum_univ_two,Fin.val_zero,Fin.val_one]

end ProbeEuler
end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical BigOperators
namespace ProbeEuler
open Eisenstein CompletedGauss  ProbePrimePower
local notation "O" => Eisenstein.O
variable (p : O) (hp : Prime p) [(Ideal.span {p}:Ideal O).IsMaximal]
  (hg : lambda∉Ideal.span {p})

def rowZeroIndexTerm (χ : MulChar (O ⧸ Ideal.span {p}) ℂ) (W V : ℂ) (j k m : ℕ) : ℂ :=
  (if k=0 then 1 else (χ^k) (Ideal.Quotient.mk _ (p^(j+6*m))))*W^k*V^m

theorem sourceRowTerm_zero (eta a rho x w z : ℂ) (j k m : ℕ) :
    sourceRowTerm p hp hg eta a rho x w z j 0 0 k m=
      rowZeroIndexTerm p (complexSexticChar (Ideal.span {p}) hg)
        (rho*((Ideal.absNorm (Ideal.span {p}):ℂ)^(-w)))
        (coordV (Ideal.absNorm (Ideal.span {p})) z) j k m := by
  unfold sourceRowTerm
  rw [sourceWeightedScalar_actual p hp hg]
  simp only [rowZeroIndexTerm,sourceScalar,weightedScalar,localCubePhase,
    coordV,Complex.ofReal_natCast,mul_zero,add_zero,pow_zero,one_mul,mul_one,
    zero_mul,Nat.choose_zero_succ,ite_true,div_one,mul_pow]
  ring

omit [(Ideal.span {p}).IsMaximal] in
lemma rowZeroIndex_zero (χ : MulChar (O ⧸ Ideal.span {p}) ℂ) (W V : ℂ)
    (j : ℕ) (hV : ‖V‖<1) :
    HasSum (fun m=> rowZeroIndexTerm p χ W V j 0 m) (1/(1-V)) := by
  simpa only [rowZeroIndexTerm,ite_true,pow_zero,one_mul,one_div] using
    hasSum_geometric_of_norm_lt_one hV

include hp in
theorem rowZeroIndex_pos_ramified (χ : MulChar (O ⧸ Ideal.span {p}) ℂ) (W V : ℂ)
    (j k m : ℕ) (hj : j≠0) (hk : k≠0) : rowZeroIndexTerm p χ W V j k m=0 := by
  rw [rowZeroIndexTerm,if_neg hk,zero_index_scalar p hp χ k (j+6*m) hk,
    if_neg (by omega),zero_mul,zero_mul]

include hp in
theorem rowZeroIndexSeries_eq (χ : MulChar (O ⧸ Ideal.span {p}) ℂ) (W V : ℂ)
    (j : ℕ) (hW : ‖W‖<1) (hV : ‖V‖<1) :
    (∑' k,∑' m,rowZeroIndexTerm p χ W V j k m)=
      1/(1-V)+(if j=0 then W/(1-W) else 0) := by
  by_cases hj : j=0
  · subst j
    simp only [rowZeroIndexTerm,zero_add,ite_true]
    exact zeroIndexSeries_eq p hp χ W V hW hV
  · rw [if_neg hj,add_zero]
    rw [tsum_eq_single 0]
    · exact (rowZeroIndex_zero p χ W V j hV).tsum_eq
    · intro k hk
      simp only [rowZeroIndex_pos_ramified p hp χ W V j k _ hj hk,tsum_zero]

end ProbeEuler
end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical BigOperators
namespace ProbeEuler
open Eisenstein CompletedGauss  ProbePrimePower
local notation "O" => Eisenstein.O
variable (p : O) (hp : Prime p) [(Ideal.span {p}:Ideal O).IsMaximal]
  (hg : lambda∉Ideal.span {p}) (hc : ringChar (O ⧸ Ideal.span {p})≠2)

def rowBaseFinite (eta a X W V rho : ℂ) (j e l : ℕ) : ℂ :=
  ∑ k : Fin 2,
    (rowMarkedTerm p hp hg eta a X W V rho j e l k.val 0+
     rowMarkedTerm p hp hg eta a X W V rho j e l k.val 1+
     rowMarkedTerm p hp hg eta a X W V rho j e l k.val 2/(1-V))

def rowClosedMarked (eta a X W V rho : ℂ) (j : ℕ) : ℂ :=
  (rowBaseFinite p hp hg eta a X W V rho j 0 2+
   rowBaseFinite p hp hg eta a X W V rho j 1 0+
   rowBaseFinite p hp hg eta a X W V rho j 0 1+
   rowBaseFinite p hp hg eta a X W V rho j 1 1)/
    (1-evenRatio (Ideal.absNorm (Ideal.span {p})) a X V)

include hc in
theorem rowMarkedSeries_eq_closed (eta a X W V rho : ℂ) (hρ : rho^6=1)
    (hV : ‖V‖<1) (hR : ‖evenRatio (Ideal.absNorm (Ideal.span {p})) a X V‖<1)
    (j : ℕ) (hj : j<6) :
    rowMarkedSeries p hp hg eta a X W V rho j=rowClosedMarked p hp hg eta a X W V rho j := by
  rw [rowMarkedSeries_four_families p hp hg hc eta a X W V rho hρ hV hR j hj]
  unfold rowClosedMarked rowBaseFinite
  rw [rowInner_base_rational p hp hg hc eta a X W V rho hV j 0 2 (by omega) (by omega),
    rowInner_base_rational p hp hg hc eta a X W V rho hV j 1 0 (by omega) (by omega),
    rowInner_base_rational p hp hg hc eta a X W V rho hV j 0 1 (by omega) (by omega),
    rowInner_base_rational p hp hg hc eta a X W V rho hV j 1 1 (by omega) (by omega)]

include hc in
lemma rowInner_zero_squarefree_summable (eta a X W V rho : ℂ) (hρ : rho^6=1)
    (hV : ‖V‖<1) (hR : ‖evenRatio (Ideal.absNorm (Ideal.span {p})) a X V‖<1)
    (j : ℕ) (hj : j<6) : Summable (fun l=> rowInner p hp hg eta a X W V rho j 0 l) := by
  have h02 := rowInner_family_hasSum p hp hg hc eta a X W V rho hρ hV hR j 0 2 hj (by omega)
  have h01 := rowInner_family_hasSum p hp hg hc eta a X W V rho hρ hV hR j 0 1 hj (by omega)
  have hs : HasSum (fun r=> rowInner p hp hg eta a X W V rho j 0 (2*(r+1)))
      (rowInner p hp hg eta a X W V rho j 0 2/(1-evenRatio (Ideal.absNorm (Ideal.span {p})) a X V)) := by
    convert h02 using 1
    funext r
    congr 1
    omega
  have he := hs.sum_range_add (f:=fun r=> rowInner p hp hg eta a X W V rho j 0 (2*r)) (k:=1)
  have ho : HasSum (fun r=> rowInner p hp hg eta a X W V rho j 0 (2*r+1))
      (rowInner p hp hg eta a X W V rho j 0 1/(1-evenRatio (Ideal.absNorm (Ideal.span {p})) a X V)) := by
    simpa only [Nat.add_comm 1] using h01
  exact (he.even_add_odd ho).summable

def sourceRowSeries (eta a rho x w z : ℂ) (j : ℕ) : ℂ :=
  ∑ e : Fin 2,∑' l,∑' k,∑' m,sourceRowTerm p hp hg eta a rho x w z j e.val l k m

include hc in

theorem sourceRowSeries_eq_closed (eta a rho x w z : ℂ) (hρ : rho^6=1)
    (hV : ‖coordV (Ideal.absNorm (Ideal.span {p})) z‖<1)
    (hR : ‖evenRatio (Ideal.absNorm (Ideal.span {p})) a
      ((Ideal.absNorm (Ideal.span {p}):ℂ)^(-x)) (coordV (Ideal.absNorm (Ideal.span {p})) z)‖<1)
    (hW : ‖rho*((Ideal.absNorm (Ideal.span {p}):ℂ)^(-w))‖<1) (j : ℕ) (hj : j<6) :
    sourceRowSeries p hp hg eta a rho x w z j=
      1/(1-coordV (Ideal.absNorm (Ideal.span {p})) z)+
      (if j=0 then (rho*((Ideal.absNorm (Ideal.span {p}):ℂ)^(-w)))/
        (1-rho*((Ideal.absNorm (Ideal.span {p}):ℂ)^(-w))) else 0)+
      rowClosedMarked p hp hg eta a ((Ideal.absNorm (Ideal.span {p}):ℂ)^(-x))
        ((Ideal.absNorm (Ideal.span {p}):ℂ)^(-w)) (coordV (Ideal.absNorm (Ideal.span {p})) z) rho j := by
  let X : ℂ := (Ideal.absNorm (Ideal.span {p}):ℂ)^(-x)
  let W : ℂ := (Ideal.absNorm (Ideal.span {p}):ℂ)^(-w)
  let V : ℂ := coordV (Ideal.absNorm (Ideal.span {p})) z
  let Z0 := 1/(1-V)+(if j=0 then rho*W/(1-rho*W) else 0)
  have he0 (l : ℕ) : (∑' k,∑' m,sourceRowTerm p hp hg eta a rho x w z j 0 l k m)=
      rowInner p hp hg eta a X W V rho j 0 l+(if l=0 then Z0 else 0) := by
    by_cases hl : l=0
    · subst l
      simp only [sourceRowTerm_zero,rowInner_zero,ite_true,zero_add]
      exact rowZeroIndexSeries_eq p hp (complexSexticChar (Ideal.span {p}) hg) (rho*W) V j hW hV
    · rw [if_neg hl,add_zero]
      apply tsum_congr
      intro k
      apply tsum_congr
      intro m
      exact sourceRowTerm_pos p hp hg eta a rho x w z j 0 l k m (by omega)
  have he1 (l : ℕ) : (∑' k,∑' m,sourceRowTerm p hp hg eta a rho x w z j 1 l k m)=
      rowInner p hp hg eta a X W V rho j 1 l := by
    apply tsum_congr
    intro k
    apply tsum_congr
    intro m
    exact sourceRowTerm_pos p hp hg eta a rho x w z j 1 l k m (by omega)
  have hs := rowInner_zero_squarefree_summable p hp hg hc eta a X W V rho hρ hV hR j hj
  have hc' := rowMarkedSeries_eq_closed p hp hg hc eta a X W V rho hρ hV hR j hj
  unfold rowMarkedSeries at hc'
  simp only [Fin.sum_univ_two,Fin.val_zero,Fin.val_one] at hc'
  unfold sourceRowSeries
  simp only [Fin.sum_univ_two,Fin.val_zero,Fin.val_one,he0,he1]
  rw [hs.tsum_add (hasSum_ite_eq 0 Z0).summable,tsum_ite_eq]
  change _=Z0+rowClosedMarked p hp hg eta a X W V rho j
  rw [←hc']
  ring

end ProbeEuler
end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical BigOperators
namespace ProbePhysical
open Eisenstein CompletedGauss  ProbePrimePower ProbeEuler
open CanonicalQuadraticSieve CanonicalRowCompletion ProbeRow CubicEisenstein
local notation "O" => Eisenstein.O

theorem complexSexticChar_unit_six (p b : O) [(Ideal.span {p}:Ideal O).IsMaximal]
    (hg : lambda∉Ideal.span {p}) (hc : ringChar (O ⧸ Ideal.span {p})≠2)
    (hb : IsCoprime b p) :
    (complexSexticChar (Ideal.span {p}) hg (Ideal.Quotient.mk _ b))^6=1 := by
  have h := congrArg (fun χ : MulChar (O ⧸ Ideal.span {p}) ℂ =>
    χ (Ideal.Quotient.mk _ b)) (complexSexticChar_six _ hg hc)
  simpa only [MulChar.pow_apply' _ (by decide : (6:ℕ)≠0),
    MulChar.one_apply ((isUnit_quotient_span_iff p b).mpr hb.symm)] using h

theorem idealRowHighLocalFactor_eq_closed (η : HeckeFamily.Character) (p : O) (hp : Prime p)
    [(Ideal.span {p}:Ideal O).IsMaximal] (hg : lambda∉Ideal.span {p})
    (hc : ringChar (O ⧸ Ideal.span {p})≠2) (hprimary : lambda^2∣p-1)
    (hs : Supported (Ideal.span {p})) (b : O) (hb : IsCoprime b p)
    (j : ℕ) (hj : j<6) (x w z : ℂ)
    (hV : ‖coordV (Ideal.absNorm (Ideal.span {p})) z‖<1)
    (hR : ‖evenRatio (Ideal.absNorm (Ideal.span {p})) (actualACube η p)
      ((Ideal.absNorm (Ideal.span {p}):ℂ)^(-x)) (coordV (Ideal.absNorm (Ideal.span {p})) z)‖<1)
    (hW : ‖complexSexticChar (Ideal.span {p}) hg (Ideal.Quotient.mk _ b)*
      ((Ideal.absNorm (Ideal.span {p}):ℂ)^(-w))‖<1) :
    idealRowHighLocalFactor η (b*p^j) (Ideal.span {p}) x w z=
      1/(1-coordV (Ideal.absNorm (Ideal.span {p})) z)+
      (if j=0 then
        (complexSexticChar (Ideal.span {p}) hg (Ideal.Quotient.mk _ b)*
          ((Ideal.absNorm (Ideal.span {p}):ℂ)^(-w)))/
        (1-complexSexticChar (Ideal.span {p}) hg (Ideal.Quotient.mk _ b)*
          ((Ideal.absNorm (Ideal.span {p}):ℂ)^(-w))) else 0)+
      rowClosedMarked p hp hg (targetMonoid η p) (actualACube η p)
        ((Ideal.absNorm (Ideal.span {p}):ℂ)^(-x))
        ((Ideal.absNorm (Ideal.span {p}):ℂ)^(-w)) (coordV (Ideal.absNorm (Ideal.span {p})) z)
        (complexSexticChar (Ideal.span {p}) hg (Ideal.Quotient.mk _ b)) j := by
  rw [idealRowHighLocalFactor_eq_source η p hp hg hc hprimary hs b hb j x w z]
  exact sourceRowSeries_eq_closed p hp hg hc _ _ _ x w z
    (complexSexticChar_unit_six p b hg hc hb) hV hR hW j hj

end ProbePhysical
end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical BigOperators
namespace ProbeEuler
open Eisenstein CompletedGauss  ProbePrimePower
local notation "O" => Eisenstein.O
variable (p : O) (hp : Prime p) [(Ideal.span {p}:Ideal O).IsMaximal]
  (hg : lambda∉Ideal.span {p}) (hc : ringChar (O ⧸ Ideal.span {p})≠2)

lemma rowMarkedTerm_unramified (eta a X W V rho : ℂ) (e l k m : ℕ) :
    rowMarkedTerm p hp hg eta a X W V rho 0 e l k m=
      principalMarkedTerm p hp hg (eta/rho) (a/rho^3) X (rho*W) V e l k m := by
  unfold rowMarkedTerm principalMarkedTerm
  split_ifs
  · rfl
  · simp only [zero_add,rowWeightedScalar_parameters]

lemma rowMarkedSeries_unramified (eta a X W V rho : ℂ) :
    rowMarkedSeries p hp hg eta a X W V rho 0=
      principalMarkedSeries p hp hg (eta/rho) (a/rho^3) X (rho*W) V := by
  unfold rowMarkedSeries principalMarkedSeries rowInner principalInner
  apply Finset.sum_congr rfl
  intro e he
  apply tsum_congr
  intro l
  apply tsum_congr
  intro k
  apply tsum_congr
  intro m
  exact rowMarkedTerm_unramified p hp hg eta a X W V rho e.val l k m

include hc in
lemma rowClosedMarked_unramified (eta a X W V rho : ℂ) (hρ : rho^6=1)
    (hV : ‖V‖<1) (hR : ‖evenRatio (Ideal.absNorm (Ideal.span {p})) a X V‖<1) :
    rowClosedMarked p hp hg eta a X W V rho 0=
      markedFactor (evenRatio (Ideal.absNorm (Ideal.span {p})) a X V) V
        (Ideal.absNorm (Ideal.span {p}):ℂ)⁻¹
        (eta*((Ideal.absNorm (Ideal.span {p}):ℂ)-1)*X*W)
        (-(eta/rho)*X+(rho*W)*evenRatio (Ideal.absNorm (Ideal.span {p})) a X V) 1 := by
  have hn : rho≠0 := by intro h; simp [h] at hρ
  rw [←rowMarkedSeries_eq_closed p hp hg hc eta a X W V rho hρ hV hR 0 (by decide),
    rowMarkedSeries_unramified p hp hg,
    principalMarkedSeries_eq p hp hg hc _ _ _ _ _ hV
      (by simpa only [evenRatio_unit _ _ _ _ _ hρ] using hR),
    evenRatio_unit _ _ _ _ _ hρ]
  congr 1
  field_simp

include hc in

theorem sourceRowSeries_unramified_euler (eta a rho x w z : ℂ) (hρ : rho^6=1)
    (hV : ‖coordV (Ideal.absNorm (Ideal.span {p})) z‖<1)
    (hR : ‖coordR (Ideal.absNorm (Ideal.span {p})) (a^2) x z‖<1)
    (hW : ‖coordW (Ideal.absNorm (Ideal.span {p})) rho w‖<1)
    (hD : 1-coordD (Ideal.absNorm (Ideal.span {p})) eta rho x≠0) :
    let Q : ℝ := Ideal.absNorm (Ideal.span {p})
    sourceRowSeries p hp hg eta a rho x w z 0=
      (1-coordD Q eta rho x)/((1-coordV Q z)*(1-coordW Q rho w))*
        unramifiedClosed Q (a^2) eta rho x w z := by
  dsimp only
  have hQ : (0:ℝ)< Ideal.absNorm (Ideal.span {p}) := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr
      (Ideal.span_singleton_eq_bot.not.mpr hp.ne_zero))
  have hr := evenRatio_eq_coordR (Ideal.absNorm (Ideal.span {p}):ℝ) hQ a x z
  simp only [Complex.ofReal_natCast] at hr
  have hr' : ‖evenRatio (Ideal.absNorm (Ideal.span {p})) a
      ((Ideal.absNorm (Ideal.span {p}):ℂ)^(-x)) (coordV (Ideal.absNorm (Ideal.span {p})) z)‖<1 := by
    rw [hr]; exact hR
  rw [sourceRowSeries_eq_closed p hp hg hc eta a rho x w z hρ hV hr' hW 0 (by decide)]
  rw [rowClosedMarked_unramified p hp hg hc _ _ _ _ _ _ hρ hV hr',hr]
  have hk := coordK_eq_geometric (Ideal.absNorm (Ideal.span {p}):ℝ) hQ eta x w
  simp only [Complex.ofReal_natCast] at hk
  rw [←hk]
  have hinv : rho⁻¹=star rho := Complex.inv_eq_conj (Complex.norm_eq_one_of_pow_eq_one hρ (by decide))
  have hv := one_sub_ne_zero_of_norm_lt_one _ hV
  have hw := one_sub_ne_zero_of_norm_lt_one _ hW
  simp only [ite_true,div_eq_mul_inv,hinv]
  unfold unramifiedClosed ProbeLocal.continuedCorrection
  dsimp only
  simp only [coordW,coordD,Complex.ofReal_natCast] at hD hw ⊢
  field_simp [hD,hv,hw]
  ; ring

end ProbeEuler
end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
namespace ProbePhysical
open Eisenstein CanonicalQuadraticSieve CanonicalRowCompletion CompletedGauss
open ProbeEuler ProbeRow  ProbePrimePower
local notation "O" => Eisenstein.O

lemma row_initial_geometric (η : HeckeFamily.Character) (p : O) (hp : Prime p)
    [(Ideal.span {p}:Ideal O).IsMaximal] (hg : lambda∉Ideal.span {p})
    (hc : ringChar (O ⧸ Ideal.span {p})≠2) (b : O) (hb : IsCoprime b p)
    (x w z : ℂ) (hx : 3/2< x.re) (hw : 2< w.re) (hz : 1/6< z.re) :
    let Q : ℝ := Ideal.absNorm (Ideal.span {p})
    let rho := complexSexticChar (Ideal.span {p}) hg (Ideal.Quotient.mk _ b)
    ‖coordV Q z‖<1 ∧ ‖coordR Q ((actualACube η p)^2) x z‖<1 ∧
      ‖coordW Q rho w‖<1 ∧ ‖coordD Q (targetMonoid η p) rho x‖<1 := by
  dsimp only
  have hP : Prime (Ideal.span {p}:Ideal O) := (Ideal.prime_span_singleton_iff).mpr hp
  have hQ2 : (2:ℝ)≤ Ideal.absNorm (Ideal.span {p}) := by
    exact_mod_cast HeckeIdealSeries.prime_norm_two_le ⟨_,hP⟩
  have hQ0 : (0:ℝ)< Ideal.absNorm (Ideal.span {p}) := by linarith
  have hQ1 : (1:ℝ)< Ideal.absNorm (Ideal.span {p}) := by linarith
  have hn : ‖complexSexticChar (Ideal.span {p}) hg (Ideal.Quotient.mk _ b)‖≤1 :=
    (Complex.norm_eq_one_of_pow_eq_one (complexSexticChar_unit_six p b hg hc hb) (by decide)).le
  refine ⟨?_,?_,?_,?_⟩
  · rw [coordV_norm _ hQ0]
    exact Real.rpow_lt_one_of_one_lt_of_neg hQ1 (by linarith)
  · rw [actualACube_sq]
    apply (coordR_norm_le _ hQ0 _ x z (actualAPhase_norm_le_one η p)).trans_lt
    exact Real.rpow_lt_one_of_one_lt_of_neg hQ1 (by linarith)
  · apply (coordW_norm_le _ hQ0 _ w hn).trans_lt
    exact Real.rpow_lt_one_of_one_lt_of_neg hQ1 (by linarith)
  · apply (coordD_norm_le _ hQ0 _ _ x (targetMonoid_norm_le_one η p) hn).trans_lt
    exact Real.rpow_lt_one_of_one_lt_of_neg hQ1 (by linarith)

theorem idealRowHighLocalFactor_unramified (η : HeckeFamily.Character) (p : O) (hp : Prime p)
    [(Ideal.span {p}:Ideal O).IsMaximal] (hg : lambda∉Ideal.span {p})
    (hc : ringChar (O ⧸ Ideal.span {p})≠2) (hprimary : lambda^2∣p-1)
    (hs : Supported (Ideal.span {p})) (b : O) (hb : IsCoprime b p)
    (x w z : ℂ) (hx : 3/2< x.re) (hw : 2< w.re) (hz : 1/6< z.re) :
    let Q : ℝ := Ideal.absNorm (Ideal.span {p})
    let rho := complexSexticChar (Ideal.span {p}) hg (Ideal.Quotient.mk _ b)
    idealRowHighLocalFactor η b (Ideal.span {p}) x w z=
      (1-coordD Q (targetMonoid η p) rho x)/((1-coordV Q z)*(1-coordW Q rho w))*
        unramifiedClosed Q (actualAPhase η p) (targetMonoid η p) rho x w z := by
  have hd := row_initial_geometric η p hp hg hc b hb x w z hx hw hz
  dsimp only at hd ⊢
  have he := idealRowHighLocalFactor_eq_source η p hp hg hc hprimary hs b hb 0 x w z
  simp only [pow_zero,mul_one] at he
  rw [he]
  simpa only [actualACube_sq,ProbeEuler.sourceRowSeries] using
    sourceRowSeries_unramified_euler p hp hg hc (targetMonoid η p) (actualACube η p)
      _ x w z (complexSexticChar_unit_six p b hg hc hb) hd.1 hd.2.1 hd.2.2.1
      (one_sub_ne_zero_of_norm_lt_one _ hd.2.2.2)

end ProbePhysical
end

end

noncomputable section
open CenteredMomentFourier Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical BigOperators
namespace ProbePrimePower
open Eisenstein CompletedGauss  CubicEisenstein 
local notation "O" => Eisenstein.O

lemma primeGauss_norm_le (p : O) (hp : p≠0)
    (χ : MulChar (O ⧸ Ideal.span {p}) ℂ) (h : O) :
    ‖primeGauss p hp χ h‖≤(Ideal.absNorm (Ideal.span {p}):ℝ) := by
  let := finiteEisensteinQuotientOfNonzero hp
  let : Fintype (O ⧸ Ideal.span {p}) := Fintype.ofFinite _
  rw [primeGauss,tsum_fintype]
  calc
    _ ≤ ∑ x : O ⧸ Ideal.span {p},‖χ x*primitiveTrace p hp (Ideal.Quotient.mk _ h*x)‖ := norm_sum_le _ _
    _ ≤ ∑ _x : O ⧸ Ideal.span {p},(1:ℝ) := Finset.sum_le_sum fun x _=> by
      rw [norm_mul,(primitiveTrace p hp).norm_apply,mul_one]
      exact FiniteRayExpansion.norm_char_le_one χ x
    _ = _ := by simp [Ideal.absNorm_apply,Submodule.cardQuot_apply,Nat.card_eq_fintype_card]

lemma primeGauss_actual_norm (p : O) (hp : p≠0) [(Ideal.span {p}:Ideal O).IsMaximal]
    (hg : lambda∉Ideal.span {p}) (hc : ringChar (O ⧸ Ideal.span {p})≠2) :
    ‖primeGauss p hp (complexSexticChar (Ideal.span {p}) hg) 1‖=
      Real.sqrt (Ideal.absNorm (Ideal.span {p}):ℝ) := by
  let : Field (O ⧸ Ideal.span {p}) := Ideal.Quotient.field _
  let : Fintype (O ⧸ Ideal.span {p}) := Fintype.ofFinite _
  have hn := localGamma_norm_one p hp hg hc 1 (by decide) (by decide)
  simp only [localGamma,pow_one,norm_div,Complex.norm_real,
    Real.norm_eq_abs,abs_of_nonneg (Real.sqrt_nonneg _)] at hn
  have hQ : (0:ℝ)< Ideal.absNorm (Ideal.span {p}) := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr
      (Ideal.span_singleton_eq_bot.not.mpr hp))
  exact (div_eq_one_iff_eq (Real.sqrt_pos.mpr hQ).ne').mp hn

lemma gaussValuationTable_norm_le (Q : ℝ) (hQ : 1≤ Q) (G : ℂ) (hG : ‖G‖≤ Q)
    (r n j : ℕ) : ‖gaussValuationTable (Q:ℂ) G r n j‖≤2*Q^(n+1) := by
  have hQ0 : 0≤ Q := by linarith
  have hn : Q^n≤ Q^(n+1) := by simpa only [pow_succ] using
    (le_mul_of_one_le_right (pow_nonneg hQ0 n) hQ)
  have hpow (a : ℕ) : ‖(Q:ℂ)^a‖=Q^a := by simp [norm_pow,abs_of_nonneg hQ0]
  have hi (a : ℕ) : ‖(if a≤ j then (Q:ℂ)^a else 0)‖≤ Q^a := by
    split_ifs
    · exact (hpow a).le
    · simpa only [norm_zero] using pow_nonneg hQ0 a
  unfold gaussValuationTable
  by_cases hr : 6∣r
  · rw [if_pos hr]
    exact (norm_sub_le _ _).trans ((add_le_add (hi (n+1)) (hi n)).trans (by linarith))
  · rw [if_neg hr]
    by_cases hj : j=n
    · rw [if_pos hj,norm_mul,hpow]
      calc
        _ ≤ Q^n*Q := mul_le_mul_of_nonneg_left hG (pow_nonneg hQ0 n)
        _ ≤ 2*Q^(n+1) := by rw [←pow_succ];nlinarith [pow_nonneg hQ0 (n+1)]
    · rw [if_neg hj,norm_zero]
      positivity

lemma positiveScalar_norm_le (p : O) (hp : Prime p) [(Ideal.span {p}:Ideal O).IsMaximal]
    (hg : lambda∉Ideal.span {p}) (hc : ringChar (O ⧸ Ideal.span {p})≠2)
    (n k j : ℕ) (hk : k≤1) :
    ‖positiveScalar p hp.ne_zero (complexSexticChar (Ideal.span {p}) hg) n k j‖≤
      2*(Ideal.absNorm (Ideal.span {p}):ℝ)^(n+1)*
        (Real.sqrt (Ideal.absNorm (Ideal.span {p}):ℝ))^k := by
  have hP : Prime (Ideal.span {p}:Ideal O) := Ideal.prime_span_singleton_iff.mpr hp
  have hQ : (1:ℝ)≤ Ideal.absNorm (Ideal.span {p}) := by
    have hh := HeckeIdealSeries.prime_norm_two_le ⟨_,hP⟩
    change 2≤ Ideal.absNorm (Ideal.span {p}) at hh
    exact_mod_cast (by omega : 1≤ Ideal.absNorm (Ideal.span {p}))
  have ht (r j : ℕ) := gaussValuationTable_norm_le (Ideal.absNorm (Ideal.span {p}):ℝ) hQ
    (primeGauss p hp.ne_zero (complexSexticChar (Ideal.span {p}) hg^r) 1)
    (primeGauss_norm_le p hp.ne_zero _ _) r n j
  have ho : ‖complexSexticChar (Ideal.span {p}) hg (-1)‖=1 :=
    Complex.norm_eq_one_of_pow_eq_one (complexSexticChar_neg_one_sq _ hg) (by decide)
  rw [positiveScalar_actual_table p hp hg hc]
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hk with rfl|rfl
  · simpa only [ite_true,pow_zero,mul_one,Complex.ofReal_natCast] using ht (n+1) j
  · simp only [Nat.one_ne_zero,ite_false,true_and]
    split_ifs
    · rw [norm_mul,norm_mul,norm_inv,ho,inv_one,one_mul,primeGauss_actual_norm p hp.ne_zero hg hc]
      simpa only [pow_one,mul_comm,Complex.ofReal_natCast] using
        mul_le_mul_of_nonneg_left (ht n (j-1)) (Real.sqrt_nonneg (Ideal.absNorm (Ideal.span {p}):ℝ))
    · simp only [norm_zero,pow_one]
      positivity

end ProbePrimePower
end

end

noncomputable section
open CenteredMomentFourier Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
namespace ProbeEuler
open Eisenstein CompletedGauss  ProbePrimePower
local notation "O" => Eisenstein.O

lemma sourceWeightedScalar_norm_le (Q : ℝ) (hQ : 0< Q)
    (eta a gamma C omega x w z scalar : ℂ) (heta : ‖eta‖≤1) (ha : ‖a‖≤1)
    (hgamma : ‖gamma‖=1) (hC : ‖C‖=1) (ho : ‖omega‖=1) (e l k m : ℕ) :
    ‖sourceWeightedScalar Q eta a gamma C omega x w z scalar e l k m‖≤
      ‖scalar‖*Q^(-(x.re+1/2)*(e:ℝ)-(1+3*x.re)*(l:ℝ)-w.re*(k:ℝ)-6*z.re*(m:ℝ)) := by
  let coeff : ℂ := (-1:ℂ)^e*gamma^(-(e:ℤ))*eta^e*(a*C)^l*
    omega^((((e+3*l)*k:ℕ):ℤ)-(e*l+l.choose 2:ℕ))
  have hn : ‖coeff‖≤1 := by
    simp only [coeff,norm_mul,norm_pow,norm_zpow,hgamma,hC,ho,norm_neg,norm_one,
      one_pow,one_zpow,mul_one,one_mul]
    exact (mul_le_of_le_one_left (by positivity) (pow_le_one₀ (norm_nonneg _) heta)).trans (pow_le_one₀ (norm_nonneg _) ha)
  change ‖coeff*scalar*(Q:ℂ)^_‖≤ _
  rw [norm_mul,norm_mul,Complex.norm_cpow_eq_rpow_re_of_pos hQ]
  have he : (-(x+1/2)*(e:ℂ)-(1+3*x)*(l:ℂ)-w*(k:ℂ)-6*z*(m:ℂ)).re=
      -(x.re+1/2)*(e:ℝ)-(1+3*x.re)*(l:ℝ)-w.re*(k:ℝ)-6*z.re*(m:ℝ) := by simp
  rw [he]
  exact mul_le_mul_of_nonneg_right (mul_le_of_le_one_left (norm_nonneg _) hn) (by positivity)

lemma scalar_spectral_power (Q x w z : ℝ) (hQ : 0< Q) (e l k m : ℕ) :
    (2*Q^(e+3*l)*(Real.sqrt Q)^k)*
      Q^(-(x+1/2)*(e:ℝ)-(1+3*x)*(l:ℝ)-w*(k:ℝ)-6*z*(m:ℝ))=
      2*Q^((1/2-x)*(e:ℝ)+(2-3*x)*(l:ℝ)+(1/2-w)*(k:ℝ)-6*z*(m:ℝ)) := by
  rw [Real.sqrt_eq_rpow,←Real.rpow_mul_natCast hQ.le,←Real.rpow_natCast Q (e+3*l)]
  rw [mul_assoc 2,←Real.rpow_add hQ,mul_assoc 2,←Real.rpow_add hQ]
  congr 1
  push_cast
  ring_nf

theorem sourceRowTerm_norm_le (p : O) (hp : Prime p) [(Ideal.span {p}:Ideal O).IsMaximal]
    (hg : lambda∉Ideal.span {p}) (hc : ringChar (O ⧸ Ideal.span {p})≠2)
    (eta a rho x w z : ℂ) (heta : ‖eta‖≤1) (ha : ‖a‖≤1) (hρ : rho^6=1)
    (j e l k m : ℕ) (ht : 0< e+3*l) (hk : k≤1) :
    ‖sourceRowTerm p hp hg eta a rho x w z j e l k m‖≤
      2*(Ideal.absNorm (Ideal.span {p}):ℝ)^((1/2-x.re)*(e:ℝ)+(2-3*x.re)*(l:ℝ)+
        (1/2-w.re)*(k:ℝ)-6*z.re*(m:ℝ)) := by
  have hQ : (0:ℝ)< Ideal.absNorm (Ideal.span {p}) := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr
      (Ideal.span_singleton_eq_bot.not.mpr hp.ne_zero))
  have hrho := Complex.norm_eq_one_of_pow_eq_one hρ (by decide : (6:ℕ)≠0)
  rw [sourceRowTerm,norm_mul,norm_div,norm_pow,norm_pow,hrho,one_pow,one_pow,div_self (by norm_num : (1:ℝ)≠0),one_mul]
  apply (sourceWeightedScalar_norm_le _ hQ eta a _ _ _ x w z _ heta ha
    (localGamma_norm_one p hp.ne_zero hg hc 1 (by decide) (by decide))
    (by rw [norm_star];exact localGamma_norm_one p hp.ne_zero hg hc 3 (by decide) (by decide))
    (Complex.norm_eq_one_of_pow_eq_one (complexSexticChar_neg_one_sq _ hg) (by decide)) e l k m).trans
  have hs := positiveScalar_norm_le p hp hg hc (e+3*l-1) k (j+6*m) hk
  rw [show e+3*l-1+1=e+3*l by omega] at hs
  rw [sourceScalar,if_neg (by omega)]
  exact (mul_le_mul_of_nonneg_right hs (by positivity)).trans_eq
    (scalar_spectral_power _ x.re w.re z.re hQ e l k m)

end ProbeEuler
end

end

noncomputable section
open CenteredMomentFourier Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical BigOperators
namespace ProbeEuler
open Eisenstein CompletedGauss  ProbePrimePower
local notation "O" => Eisenstein.O
variable (p : O) (hp : Prime p) [(Ideal.span {p}:Ideal O).IsMaximal]
  (hg : lambda∉Ideal.span {p}) (hc : ringChar (O ⧸ Ideal.span {p})≠2)

include hc in
lemma rowMarkedTerm_second_region (eta a rho x w z : ℂ)
    (heta : ‖eta‖≤1) (ha : ‖a‖≤1) (hρ : rho^6=1)
    (hx : (7/8:ℝ)≤ x.re) (hw : (19/20:ℝ)≤ w.re) (hz : (33/200:ℝ)≤ z.re)
    (j e l k m : ℕ) (ht : 0< e+3*l) (hk : k≤1) :
    ‖rowMarkedTerm p hp hg eta a ((Ideal.absNorm (Ideal.span {p}):ℂ)^(-x))
      ((Ideal.absNorm (Ideal.span {p}):ℂ)^(-w)) (coordV (Ideal.absNorm (Ideal.span {p})) z)
      rho j e l k m‖≤2 := by
  rw [←sourceRowTerm_pos p hp hg eta a rho x w z j e l k m (by omega)]
  apply (sourceRowTerm_norm_le p hp hg hc eta a rho x w z heta ha hρ j e l k m ht hk).trans
  have hP : Prime (Ideal.span {p}:Ideal O) := Ideal.prime_span_singleton_iff.mpr hp
  have hQ1 : (1:ℝ)≤ Ideal.absNorm (Ideal.span {p}) := by
    have hh := HeckeIdealSeries.prime_norm_two_le ⟨_,hP⟩
    change 2≤ Ideal.absNorm (Ideal.span {p}) at hh
    exact_mod_cast (by omega : 1≤ Ideal.absNorm (Ideal.span {p}))
  have he : (1/2-x.re)*(e:ℝ)+(2-3*x.re)*(l:ℝ)+(1/2-w.re)*(k:ℝ)-6*z.re*(m:ℝ)≤0 := by
    have h1 := mul_nonpos_of_nonpos_of_nonneg (show 1/2-x.re≤0 by linarith) (Nat.cast_nonneg e : (0:ℝ)≤ _)
    have h2 := mul_nonpos_of_nonpos_of_nonneg (show 2-3*x.re≤0 by linarith) (Nat.cast_nonneg l : (0:ℝ)≤ _)
    have h3 := mul_nonpos_of_nonpos_of_nonneg (show 1/2-w.re≤0 by linarith) (Nat.cast_nonneg k : (0:ℝ)≤ _)
    have h4 : 0≤6*z.re*(m:ℝ) := by positivity
    linarith
  have hh := Real.rpow_le_one_of_one_le_of_nonpos hQ1 he
  linarith

lemma second_region_V_half (Q : ℝ) (hQ : 4≤ Q) (z : ℂ) (hz : (33/200:ℝ)≤ z.re) :
    ‖coordV Q z‖≤1/2 := by
  rw [coordV_norm Q (by linarith)]
  exact rpow_le_half Q _ hQ (by linarith)

lemma second_region_R_half (Q : ℝ) (hQ : 4≤ Q) (a x z : ℂ) (ha : ‖a‖≤1)
    (hx : (7/8:ℝ)≤ x.re) (hz : (33/200:ℝ)≤ z.re) :
    ‖evenRatio Q a ((Q:ℂ)^(-x)) (coordV Q z)‖≤1/2 := by
  rw [evenRatio_eq_coordR Q (by linarith)]
  apply (coordR_norm_le Q (by linarith) (a^2) x z (by simpa only [norm_pow] using pow_le_one₀ (norm_nonneg a) ha)).trans
  exact rpow_le_half Q _ hQ (by linarith)

include hc in
lemma rowBaseFinite_second_region (eta a rho x w z : ℂ)
    (hQ : (4:ℝ)≤ Ideal.absNorm (Ideal.span {p}))
    (heta : ‖eta‖≤1) (ha : ‖a‖≤1) (hρ : rho^6=1)
    (hx : (7/8:ℝ)≤ x.re) (hw : (19/20:ℝ)≤ w.re) (hz : (33/200:ℝ)≤ z.re)
    (j e l : ℕ) (ht : 0< e+3*l) :
    ‖rowBaseFinite p hp hg eta a ((Ideal.absNorm (Ideal.span {p}):ℂ)^(-x))
      ((Ideal.absNorm (Ideal.span {p}):ℂ)^(-w)) (coordV (Ideal.absNorm (Ideal.span {p})) z)
      rho j e l‖≤16 := by
  have hv := ProbeLocal.inv_one_sub_norm_le_two _ (second_region_V_half _ hQ z hz)
  have ht' (k : Fin 2) (m : ℕ) := rowMarkedTerm_second_region p hp hg hc eta a rho x w z heta ha hρ hx hw hz
    j e l k.val m ht (by omega)
  unfold rowBaseFinite
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑ _k : Fin 2,(8:ℝ) := by
      apply Finset.sum_le_sum
      intro k hk
      apply (norm_add_le _ _).trans
      have hab := (norm_add_le _ _).trans (add_le_add (ht' k 0) (ht' k 1))
      have hd : ‖rowMarkedTerm p hp hg eta a ((Ideal.absNorm (Ideal.span {p}):ℂ)^(-x))
          ((Ideal.absNorm (Ideal.span {p}):ℂ)^(-w)) (coordV (Ideal.absNorm (Ideal.span {p})) z)
          rho j e l k.val 2/(1-coordV (Ideal.absNorm (Ideal.span {p})) z)‖≤4 := by
        rw [div_eq_mul_inv,norm_mul]
        exact (mul_le_mul (ht' k 2) hv (norm_nonneg _) (by norm_num)).trans_eq (by norm_num)
      linarith
    _ = _ := by norm_num

include hc in
theorem rowClosedMarked_second_region (eta a rho x w z : ℂ)
    (hQ : (4:ℝ)≤ Ideal.absNorm (Ideal.span {p}))
    (heta : ‖eta‖≤1) (ha : ‖a‖≤1) (hρ : rho^6=1)
    (hx : (7/8:ℝ)≤ x.re) (hw : (19/20:ℝ)≤ w.re) (hz : (33/200:ℝ)≤ z.re) (j : ℕ) :
    ‖rowClosedMarked p hp hg eta a ((Ideal.absNorm (Ideal.span {p}):ℂ)^(-x))
      ((Ideal.absNorm (Ideal.span {p}):ℂ)^(-w)) (coordV (Ideal.absNorm (Ideal.span {p})) z) rho j‖≤128 := by
  have h02 := rowBaseFinite_second_region p hp hg hc eta a rho x w z hQ heta ha hρ hx hw hz j 0 2 (by omega)
  have h10 := rowBaseFinite_second_region p hp hg hc eta a rho x w z hQ heta ha hρ hx hw hz j 1 0 (by omega)
  have h01 := rowBaseFinite_second_region p hp hg hc eta a rho x w z hQ heta ha hρ hx hw hz j 0 1 (by omega)
  have h11 := rowBaseFinite_second_region p hp hg hc eta a rho x w z hQ heta ha hρ hx hw hz j 1 1 (by omega)
  have hr := ProbeLocal.inv_one_sub_norm_le_two _ (second_region_R_half _ hQ a x z ha hx hz)
  simp only [Complex.ofReal_natCast] at hr
  unfold rowClosedMarked
  rw [div_eq_mul_inv,norm_mul]
  apply (mul_le_mul_of_nonneg_right
    ((norm_add_le _ _).trans (add_le_add
      ((norm_add_le _ _).trans (add_le_add
        ((norm_add_le _ _).trans (add_le_add h02 h10)) h01)) h11)) (norm_nonneg _)).trans
  nlinarith

end ProbeEuler
end

end

noncomputable section
open CenteredMomentFourier Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
namespace ProbeEuler
open Eisenstein CompletedGauss  ProbePrimePower
local notation "O" => Eisenstein.O
variable (p : O) (hp : Prime p) [(Ideal.span {p}:Ideal O).IsMaximal]
  (hg : lambda∉Ideal.span {p}) (hc : ringChar (O ⧸ Ideal.span {p})≠2)

def ramifiedClosed (eta a rho x w z : ℂ) (j : ℕ) : ℂ :=
  1+(1-coordV (Ideal.absNorm (Ideal.span {p})) z)*
    rowClosedMarked p hp hg eta a ((Ideal.absNorm (Ideal.span {p}):ℂ)^(-x))
      ((Ideal.absNorm (Ideal.span {p}):ℂ)^(-w)) (coordV (Ideal.absNorm (Ideal.span {p})) z) rho j

include hc in
theorem ramifiedClosed_bound (eta a rho x w z : ℂ)
    (hQ : (4:ℝ)≤ Ideal.absNorm (Ideal.span {p}))
    (heta : ‖eta‖≤1) (ha : ‖a‖≤1) (hρ : rho^6=1)
    (hx : (7/8:ℝ)≤ x.re) (hw : (19/20:ℝ)≤ w.re) (hz : (33/200:ℝ)≤ z.re) (j : ℕ) :
    ‖ramifiedClosed p hp hg eta a rho x w z j‖≤193 := by
  have hb := rowClosedMarked_second_region p hp hg hc eta a rho x w z hQ heta ha hρ hx hw hz j
  have hv := second_region_V_half _ hQ z hz
  have hs := norm_sub_le (1:ℂ) (coordV (Ideal.absNorm (Ideal.span {p})) z)
  simp only [norm_one] at hs
  unfold ramifiedClosed
  apply (norm_add_le _ _).trans
  rw [norm_one,norm_mul]
  have hm := mul_le_mul (show ‖1-coordV (Ideal.absNorm (Ideal.span {p})) z‖≤3/2 by linarith)
    hb (norm_nonneg _) (by norm_num : (0:ℝ)≤3/2)
  linarith

include hc in

theorem sourceRowSeries_ramified (eta a rho x w z : ℂ) (hρ : rho^6=1)
    (hV : ‖coordV (Ideal.absNorm (Ideal.span {p})) z‖<1)
    (hR : ‖evenRatio (Ideal.absNorm (Ideal.span {p})) a
      ((Ideal.absNorm (Ideal.span {p}):ℂ)^(-x)) (coordV (Ideal.absNorm (Ideal.span {p})) z)‖<1)
    (hW : ‖rho*((Ideal.absNorm (Ideal.span {p}):ℂ)^(-w))‖<1)
    (j : ℕ) (hj0 : j≠0) (hj : j<6) :
    sourceRowSeries p hp hg eta a rho x w z j*(1-coordV (Ideal.absNorm (Ideal.span {p})) z)=
      ramifiedClosed p hp hg eta a rho x w z j := by
  rw [sourceRowSeries_eq_closed p hp hg hc eta a rho x w z hρ hV hR hW j hj,if_neg hj0,add_zero]
  unfold ramifiedClosed
  have hn := one_sub_ne_zero_of_norm_lt_one _ hV
  field_simp

end ProbeEuler
end

end

noncomputable section
open CenteredMomentFourier Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical BigOperators
namespace ProbeEuler
open Eisenstein CompletedGauss  ProbePrimePower
local notation "O" => Eisenstein.O
variable (p : O) (hp : Prime p) [(Ideal.span {p}:Ideal O).IsMaximal]
  (hg : lambda∉Ideal.span {p})

lemma rowMarkedTerm_differentiableAt (eta a rho : ℂ) (X W V : ℂ→ℂ) (t : ℂ)
    (hX : DifferentiableAt ℂ X t) (hW : DifferentiableAt ℂ W t) (hV : DifferentiableAt ℂ V t)
    (j e l k m : ℕ) :
    DifferentiableAt ℂ (fun s=> rowMarkedTerm p hp hg eta a (X s) (W s) (V s) rho j e l k m) t := by
  unfold rowMarkedTerm
  split_ifs
  · fun_prop
  · unfold rowWeightedScalar weightedScalar
    fun_prop

lemma rowBaseFinite_differentiableAt (eta a rho : ℂ) (X W V : ℂ→ℂ) (t : ℂ)
    (hX : DifferentiableAt ℂ X t) (hW : DifferentiableAt ℂ W t) (hV : DifferentiableAt ℂ V t)
    (hv : 1-V t≠0) (j e l : ℕ) :
    DifferentiableAt ℂ (fun s=> rowBaseFinite p hp hg eta a (X s) (W s) (V s) rho j e l) t := by
  have hd (k m : ℕ) := rowMarkedTerm_differentiableAt p hp hg eta a rho X W V t hX hW hV j e l k m
  unfold rowBaseFinite
  fun_prop (disch := assumption)

lemma rowClosedMarked_differentiableAt (eta a rho : ℂ) (X W V : ℂ→ℂ) (t : ℂ)
    (hX : DifferentiableAt ℂ X t) (hW : DifferentiableAt ℂ W t) (hV : DifferentiableAt ℂ V t)
    (hv : 1-V t≠0) (hr : 1-evenRatio (Ideal.absNorm (Ideal.span {p})) a (X t) (V t)≠0) (j : ℕ) :
    DifferentiableAt ℂ (fun s=> rowClosedMarked p hp hg eta a (X s) (W s) (V s) rho j) t := by
  have hd (e l : ℕ) := rowBaseFinite_differentiableAt p hp hg eta a rho X W V t hX hW hV hv j e l
  have hR : DifferentiableAt ℂ (fun s=> evenRatio (Ideal.absNorm (Ideal.span {p})) a (X s) (V s)) t := by
    unfold evenRatio
    fun_prop
  unfold rowClosedMarked
  fun_prop (disch := assumption)

lemma ramifiedClosed_differentiableAt (eta a rho : ℂ) (X W Z : ℂ→ℂ) (t : ℂ)
    (hX : DifferentiableAt ℂ X t) (hW : DifferentiableAt ℂ W t) (hZ : DifferentiableAt ℂ Z t)
    (hv : 1-coordV (Ideal.absNorm (Ideal.span {p})) (Z t)≠0)
    (hr : 1-coordR (Ideal.absNorm (Ideal.span {p})) (a^2) (X t) (Z t)≠0) (j : ℕ) :
    DifferentiableAt ℂ (fun s=> ramifiedClosed p hp hg eta a rho (X s) (W s) (Z s) j) t := by
  have hQ : (0:ℝ)< Ideal.absNorm (Ideal.span {p}) := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr
      (Ideal.span_singleton_eq_bot.not.mpr hp.ne_zero))
  have hcx : DifferentiableAt ℂ (fun s=>(Ideal.absNorm (Ideal.span {p}):ℂ)^(-X s)) t := by
    exact hX.neg.const_cpow (Or.inl (by exact_mod_cast hQ.ne'))
  have hcw : DifferentiableAt ℂ (fun s=>(Ideal.absNorm (Ideal.span {p}):ℂ)^(-W s)) t := by
    exact hW.neg.const_cpow (Or.inl (by exact_mod_cast hQ.ne'))
  have hcv := (coordV_differentiable _ hQ).differentiableAt.comp t hZ
  change DifferentiableAt ℂ (fun s=> coordV (Ideal.absNorm (Ideal.span {p})) (Z s)) t at hcv
  have hr' := evenRatio_eq_coordR (Ideal.absNorm (Ideal.span {p}):ℝ) hQ a (X t) (Z t)
  simp only [Complex.ofReal_natCast] at hr'
  have hd := rowClosedMarked_differentiableAt p hp hg eta a rho _ _ _ t hcx hcw hcv hv
    (by rw [hr'];exact hr) j
  unfold ramifiedClosed
  fun_prop

lemma ramifiedClosed_analytic_x (eta a rho w z : ℂ)
    (hQ : (4:ℝ)≤ Ideal.absNorm (Ideal.span {p})) (ha : ‖a‖≤1) (hz : (4/25:ℝ)≤ z.re) (j : ℕ) :
    AnalyticOnNhd ℂ (fun x=> ramifiedClosed p hp hg eta a rho x w z j) {x : ℂ|7/8< x.re} := by
  apply DifferentiableOn.analyticOnNhd _ (isOpen_lt continuous_const Complex.continuous_re)
  intro x hx
  have hd := open_region_denominators _ (a^2) 0 0 x z hQ
    (by simpa only [norm_pow] using pow_le_one₀ (norm_nonneg a) ha) (by norm_num) (by norm_num) hx.le hz
  exact (ramifiedClosed_differentiableAt p hp hg eta a rho id (fun _=> w) (fun _=> z) x
    differentiableAt_id (differentiableAt_const w) (differentiableAt_const z) hd.2.1 hd.1 j).differentiableWithinAt

lemma ramifiedClosed_analytic_w (eta a rho x z : ℂ)
    (hQ : (4:ℝ)≤ Ideal.absNorm (Ideal.span {p})) (ha : ‖a‖≤1)
    (hx : (7/8:ℝ)≤ x.re) (hz : (4/25:ℝ)≤ z.re) (j : ℕ) :
    Differentiable ℂ (fun w=> ramifiedClosed p hp hg eta a rho x w z j) := by
  intro w
  have hd := open_region_denominators _ (a^2) 0 0 x z hQ
    (by simpa only [norm_pow] using pow_le_one₀ (norm_nonneg a) ha) (by norm_num) (by norm_num) hx hz
  exact ramifiedClosed_differentiableAt p hp hg eta a rho (fun _=> x) id (fun _=> z) w
    (differentiableAt_const x) differentiableAt_id (differentiableAt_const z) hd.2.1 hd.1 j

lemma ramifiedClosed_analytic_z (eta a rho x w : ℂ)
    (hQ : (4:ℝ)≤ Ideal.absNorm (Ideal.span {p})) (ha : ‖a‖≤1) (hx : (7/8:ℝ)≤ x.re) (j : ℕ) :
    AnalyticOnNhd ℂ (fun z=> ramifiedClosed p hp hg eta a rho x w z j) {z : ℂ|4/25< z.re} := by
  apply DifferentiableOn.analyticOnNhd _ (isOpen_lt continuous_const Complex.continuous_re)
  intro z hz
  have hd := open_region_denominators _ (a^2) 0 0 x z hQ
    (by simpa only [norm_pow] using pow_le_one₀ (norm_nonneg a) ha) (by norm_num) (by norm_num) hx hz.le
  exact (ramifiedClosed_differentiableAt p hp hg eta a rho (fun _=> x) (fun _=> w) id z
    (differentiableAt_const x) (differentiableAt_const w) differentiableAt_id hd.2.1 hd.1 j).differentiableWithinAt

end ProbeEuler
end

end

noncomputable section
open CenteredMomentFourier Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
namespace ProbeEuler

lemma first_open_region_denominators (Q : ℝ) (A eta v x z : ℂ)
    (hQ : 4≤ Q) (hA : ‖A‖≤1) (he : ‖eta‖≤1) (hv : ‖v‖≤1)
    (hx : 1/2≤ x.re) (hz : 1/3≤ z.re) :
    1-coordR Q A x z≠0 ∧ 1-coordV Q z≠0 ∧ 1-coordD Q eta v x≠0 := by
  have hQ0 : 0< Q := by linarith
  have hQ1 : 1≤ Q := by linarith
  have hR : ‖coordR Q A x z‖≤1/2 := by
    apply (coordR_norm_le Q hQ0 A x z hA).trans
    apply rpow_le_half Q _ hQ
    linarith
  have hV : ‖coordV Q z‖≤1/2 := by
    rw [coordV_norm Q hQ0]
    apply rpow_le_half Q _ hQ
    linarith
  have hD : ‖coordD Q eta v x‖≤1/2 := by
    apply (coordD_norm_le Q hQ0 eta v x he hv).trans
    apply rpow_le_half Q _ hQ
    linarith
  exact ⟨ProbeLocal.one_sub_ne_zero_of_norm_le_half _ hR,
    ProbeLocal.one_sub_ne_zero_of_norm_le_half _ hV,ProbeLocal.one_sub_ne_zero_of_norm_le_half _ hD⟩

theorem unramifiedClosed_first_analytic_x (Q : ℝ) (A eta v w z : ℂ)
    (hQ : 4≤ Q) (hA : ‖A‖≤1) (he : ‖eta‖≤1) (hv : ‖v‖≤1) (hz : 1/3≤ z.re) :
    AnalyticOnNhd ℂ (fun x=> unramifiedClosed Q A eta v x w z) {x : ℂ|1/2< x.re} := by
  apply DifferentiableOn.analyticOnNhd _ (isOpen_lt continuous_const Complex.continuous_re)
  intro x hx
  have hd := first_open_region_denominators Q A eta v x z hQ hA he hv hx.le hz
  exact (unramifiedClosed_differentiableAt Q (by linarith) A eta v x w z hd.1 hd.2.1 hd.2.2).differentiableWithinAt

theorem unramifiedClosed_first_analytic_w (Q : ℝ) (A eta v x z : ℂ)
    (hQ : 4≤ Q) (hA : ‖A‖≤1) (he : ‖eta‖≤1) (hv : ‖v‖≤1)
    (hx : 1/2≤ x.re) (hz : 1/3≤ z.re) :
    AnalyticOnNhd ℂ (fun w=> unramifiedClosed Q A eta v x w z) (Set.univ : Set ℂ) := by
  apply DifferentiableOn.analyticOnNhd _ isOpen_univ
  intro w hw
  have hd := first_open_region_denominators Q A eta v x z hQ hA he hv hx hz
  exact (unramifiedClosed_differentiableAt_w Q (by linarith) A eta v x w z hd.1 hd.2.1 hd.2.2).differentiableWithinAt

theorem unramifiedClosed_first_analytic_z (Q : ℝ) (A eta v x w : ℂ)
    (hQ : 4≤ Q) (hA : ‖A‖≤1) (he : ‖eta‖≤1) (hv : ‖v‖≤1) (hx : 1/2≤ x.re) :
    AnalyticOnNhd ℂ (fun z=> unramifiedClosed Q A eta v x w z) {z : ℂ|1/3< z.re} := by
  apply DifferentiableOn.analyticOnNhd _ (isOpen_lt continuous_const Complex.continuous_re)
  intro z hz
  have hd := first_open_region_denominators Q A eta v x z hQ hA he hv hx hz.le
  exact (unramifiedClosed_differentiableAt_z Q (by linarith) A eta v x w z hd.1 hd.2.1 hd.2.2).differentiableWithinAt

open Eisenstein CompletedGauss  ProbePrimePower
local notation "O" => Eisenstein.O
variable (p : O) (hp : Prime p) [(Ideal.span {p}:Ideal O).IsMaximal]
  (hg : lambda∉Ideal.span {p})

lemma ramifiedClosed_first_analytic_x (eta a rho w z : ℂ)
    (hQ : (4:ℝ)≤ Ideal.absNorm (Ideal.span {p})) (ha : ‖a‖≤1) (hz : (1/3:ℝ)≤ z.re) (j : ℕ) :
    AnalyticOnNhd ℂ (fun x=> ramifiedClosed p hp hg eta a rho x w z j) {x : ℂ|1/2< x.re} := by
  apply DifferentiableOn.analyticOnNhd _ (isOpen_lt continuous_const Complex.continuous_re)
  intro x hx
  have hd := first_open_region_denominators _ (a^2) 0 0 x z hQ
    (by simpa only [norm_pow] using pow_le_one₀ (norm_nonneg a) ha) (by norm_num) (by norm_num) hx.le hz
  exact (ramifiedClosed_differentiableAt p hp hg eta a rho id (fun _=> w) (fun _=> z) x
    differentiableAt_id (differentiableAt_const w) (differentiableAt_const z) hd.2.1 hd.1 j).differentiableWithinAt

lemma ramifiedClosed_first_analytic_w (eta a rho x z : ℂ)
    (hQ : (4:ℝ)≤ Ideal.absNorm (Ideal.span {p})) (ha : ‖a‖≤1)
    (hx : (1/2:ℝ)≤ x.re) (hz : (1/3:ℝ)≤ z.re) (j : ℕ) :
    Differentiable ℂ (fun w=> ramifiedClosed p hp hg eta a rho x w z j) := by
  intro w
  have hd := first_open_region_denominators _ (a^2) 0 0 x z hQ
    (by simpa only [norm_pow] using pow_le_one₀ (norm_nonneg a) ha) (by norm_num) (by norm_num) hx hz
  exact ramifiedClosed_differentiableAt p hp hg eta a rho (fun _=> x) id (fun _=> z) w
    (differentiableAt_const x) differentiableAt_id (differentiableAt_const z) hd.2.1 hd.1 j

lemma ramifiedClosed_first_analytic_z (eta a rho x w : ℂ)
    (hQ : (4:ℝ)≤ Ideal.absNorm (Ideal.span {p})) (ha : ‖a‖≤1) (hx : (1/2:ℝ)≤ x.re) (j : ℕ) :
    AnalyticOnNhd ℂ (fun z=> ramifiedClosed p hp hg eta a rho x w z j) {z : ℂ|1/3< z.re} := by
  apply DifferentiableOn.analyticOnNhd _ (isOpen_lt continuous_const Complex.continuous_re)
  intro z hz
  have hd := first_open_region_denominators _ (a^2) 0 0 x z hQ
    (by simpa only [norm_pow] using pow_le_one₀ (norm_nonneg a) ha) (by norm_num) (by norm_num) hx hz.le
  exact (ramifiedClosed_differentiableAt p hp hg eta a rho (fun _=> x) (fun _=> w) id z
    (differentiableAt_const x) (differentiableAt_const w) differentiableAt_id hd.2.1 hd.1 j).differentiableWithinAt

end ProbeEuler
end

end

noncomputable section
open CenteredMomentFourier Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical BigOperators
namespace ProbePrimePower
open Eisenstein CompletedGauss  CubicEisenstein
local notation "O" => Eisenstein.O
variable (p : O) (hp : Prime p) [(Ideal.span {p}:Ideal O).IsMaximal]
  (hg : lambda∉Ideal.span {p}) (hc : ringChar (O ⧸ Ideal.span {p})≠2)

include hc in
lemma primeGauss_actual_pow_norm (r : ℕ) (hr : r≠0) (hr6 : r<6) :
    ‖primeGauss p hp.ne_zero (complexSexticChar (Ideal.span {p}) hg^r) 1‖=
      Real.sqrt (Ideal.absNorm (Ideal.span {p}):ℝ) := by
  let : Field (O ⧸ Ideal.span {p}) := Ideal.Quotient.field _
  let : Fintype (O ⧸ Ideal.span {p}) := Fintype.ofFinite _
  have hn := localGamma_norm_one p hp.ne_zero hg hc r hr hr6
  simp only [localGamma,norm_div,Complex.norm_real,
    Real.norm_eq_abs,abs_of_nonneg (Real.sqrt_nonneg _)] at hn
  have hQ : (0:ℝ)< Ideal.absNorm (Ideal.span {p}) := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr
      (Ideal.span_singleton_eq_bot.not.mpr hp.ne_zero))
  exact (div_eq_one_iff_eq (Real.sqrt_pos.mpr hQ).ne').mp hn

include hc in
lemma nonprincipal_kzero_norm (n j : ℕ) (hn : n<5) :
    ‖positiveScalar p hp.ne_zero (complexSexticChar (Ideal.span {p}) hg) n 0 j‖≤
      (Ideal.absNorm (Ideal.span {p}):ℝ)^n*Real.sqrt (Ideal.absNorm (Ideal.span {p}):ℝ) := by
  rw [positiveScalar_kzero,complexSexticChar_primePowerGauss_at_pow p hp hg hc,
    if_neg (by omega : ¬6∣n+1)]
  split_ifs
  · rw [norm_mul,norm_pow,Complex.norm_natCast,primeGauss_actual_pow_norm p hp hg hc (n+1) (by omega) (by omega)]
  · simp only [norm_zero]
    positivity

include hc in
lemma nonprincipal_kone_norm (n j : ℕ) (hn : 0< n) (hn6 : n<6) :
    ‖positiveScalar p hp.ne_zero (complexSexticChar (Ideal.span {p}) hg) n 1 j‖≤
      (Ideal.absNorm (Ideal.span {p}):ℝ)^(n+1) := by
  rw [positiveScalar_actual_table p hp hg hc,if_neg (by decide : (1:ℕ)≠0)]
  by_cases hj : 1≤ j
  · rw [if_pos ⟨rfl,hj⟩,gaussValuationTable,if_neg (by omega : ¬6∣n)]
    split_ifs
    · rw [norm_mul,norm_mul,norm_inv,
        Complex.norm_eq_one_of_pow_eq_one (complexSexticChar_neg_one_sq _ hg) (by decide),inv_one,one_mul,
        primeGauss_actual_norm p hp.ne_zero hg hc,norm_mul,norm_pow,Complex.norm_natCast,
        primeGauss_actual_pow_norm p hp hg hc n (by omega) hn6]
      have hsq := Real.sq_sqrt (Nat.cast_nonneg (Ideal.absNorm (Ideal.span {p})) : (0:ℝ)≤ _)
      rw [pow_succ]
      apply le_of_eq
      calc
        _ = (Ideal.absNorm (Ideal.span {p}):ℝ)^n*(Real.sqrt (Ideal.absNorm (Ideal.span {p}):ℝ))^2 := by ring
        _ = _ := by rw [hsq]
    · simp only [mul_zero,norm_zero]
      positivity
  · rw [if_neg (by omega),norm_zero]
    positivity

include hc in
lemma even_base_kzero_norm (m j : ℕ) (hj : j<6) :
    ‖positiveScalar p hp.ne_zero (complexSexticChar (Ideal.span {p}) hg) 5 0 (j+6*m)‖≤
      if m=0 then (Ideal.absNorm (Ideal.span {p}):ℝ)^5 else (Ideal.absNorm (Ideal.span {p}):ℝ)^6 := by
  have he := row_even_kzero p hp hg hc 0 m j hj
  norm_num only [Nat.mul_zero,zero_add] at he
  rw [he]
  by_cases hm : m=0
  · subst m
    norm_num only [Nat.reduceLeDiff,ite_false,ite_true,and_true]
    split_ifs <;> simp [norm_pow]
  · rw [if_pos (by omega),if_neg hm,norm_mul,norm_pow,Complex.norm_natCast]
    have hQ1 : (1:ℝ)≤ Ideal.absNorm (Ideal.span {p}) := by
      have hh := HeckeIdealSeries.prime_norm_two_le
        ⟨Ideal.span {p},Ideal.prime_span_singleton_iff.mpr hp⟩
      change 2≤ Ideal.absNorm (Ideal.span {p}) at hh
      exact_mod_cast (by omega : 1≤ Ideal.absNorm (Ideal.span {p}))
    have hsub : ‖(Ideal.absNorm (Ideal.span {p}):ℂ)-1‖=(Ideal.absNorm (Ideal.span {p}):ℝ)-1 := by
      rw [←Complex.ofReal_natCast,←Complex.ofReal_one,←Complex.ofReal_sub,Complex.norm_real,
        Real.norm_eq_abs,abs_of_nonneg (by linarith)]
    rw [hsub,show (Ideal.absNorm (Ideal.span {p}):ℝ)^6=(Ideal.absNorm (Ideal.span {p}):ℝ)^5*(Ideal.absNorm (Ideal.span {p}):ℝ) by ring]
    exact mul_le_mul_of_nonneg_left (by linarith) (by positivity)

include hc in
lemma even_base_kone_zero (j : ℕ) (hj : j<6) :
    positiveScalar p hp.ne_zero (complexSexticChar (Ideal.span {p}) hg) 5 1 j=0 := by
  rw [positiveScalar_actual_table p hp hg hc,if_neg (by decide : (1:ℕ)≠0)]
  by_cases hj1 : 1≤ j
  · rw [if_pos ⟨rfl,hj1⟩,gaussValuationTable,if_neg (by decide : ¬6∣5),
      if_neg (by omega : j-1≠5),mul_zero]
  · rw [if_neg (by omega)]

end ProbePrimePower
end

end

noncomputable section
open CenteredMomentFourier Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical
namespace ProbeEuler
open Eisenstein CompletedGauss  ProbePrimePower
local notation "O" => Eisenstein.O
variable (p : O) (hp : Prime p) [(Ideal.span {p}:Ideal O).IsMaximal]
  (hg : lambda∉Ideal.span {p}) (hc : ringChar (O ⧸ Ideal.span {p})≠2)

lemma pow_mul_sqrt (Q : ℝ) (hQ : 0< Q) (n : ℕ) : Q^n*Real.sqrt Q=Q^((n:ℝ)+1/2) := by
  rw [Real.rpow_add hQ,Real.rpow_natCast,Real.sqrt_eq_rpow]

include hc in
lemma sourceRowTerm_norm_from_scalar (eta a rho x w z : ℂ)
    (heta : ‖eta‖≤1) (ha : ‖a‖≤1) (hρ : rho^6=1)
    (j e l k m : ℕ) (nu : ℝ)
    (hs : ‖sourceScalar p hp hg (e+3*l) k (j+6*m)‖≤2*(Ideal.absNorm (Ideal.span {p}):ℝ)^nu)
    (he : nu-(x.re+1/2)*(e:ℝ)-(1+3*x.re)*(l:ℝ)-w.re*(k:ℝ)-6*z.re*(m:ℝ)≤0) :
    ‖sourceRowTerm p hp hg eta a rho x w z j e l k m‖≤2 := by
  have hP : Prime (Ideal.span {p}:Ideal O) := Ideal.prime_span_singleton_iff.mpr hp
  have hQ2 : (2:ℝ)≤ Ideal.absNorm (Ideal.span {p}) := by exact_mod_cast HeckeIdealSeries.prime_norm_two_le ⟨_,hP⟩
  have hQ : (0:ℝ)< Ideal.absNorm (Ideal.span {p}) := by linarith
  have hrho := Complex.norm_eq_one_of_pow_eq_one hρ (by decide : (6:ℕ)≠0)
  rw [sourceRowTerm,norm_mul,norm_div,norm_pow,norm_pow,hrho,one_pow,one_pow,div_self (by norm_num : (1:ℝ)≠0),one_mul]
  apply (sourceWeightedScalar_norm_le _ hQ eta a _ _ _ x w z _ heta ha
    (localGamma_norm_one p hp.ne_zero hg hc 1 (by decide) (by decide))
    (by rw [norm_star];exact localGamma_norm_one p hp.ne_zero hg hc 3 (by decide) (by decide))
    (Complex.norm_eq_one_of_pow_eq_one (complexSexticChar_neg_one_sq _ hg) (by decide)) e l k m).trans
  calc
    _ ≤ (2*(Ideal.absNorm (Ideal.span {p}):ℝ)^nu)*
      (Ideal.absNorm (Ideal.span {p}):ℝ)^(-(x.re+1/2)*(e:ℝ)-(1+3*x.re)*(l:ℝ)-w.re*(k:ℝ)-6*z.re*(m:ℝ)) :=
      mul_le_mul_of_nonneg_right hs (by positivity)
    _ = 2*(Ideal.absNorm (Ideal.span {p}):ℝ)^(nu-(x.re+1/2)*(e:ℝ)-(1+3*x.re)*(l:ℝ)-w.re*(k:ℝ)-6*z.re*(m:ℝ)) := by
      rw [mul_assoc,←Real.rpow_add hQ]
      congr 2
      ring
    _ ≤ 2 := by
      have hh := Real.rpow_le_one_of_one_le_of_nonpos (show (1:ℝ)≤ Ideal.absNorm (Ideal.span {p}) by linarith) he
      linarith

/-- Norm exponent for the four nonzero base positions of the marked local series. -/
private def sourceBaseExponent (e l k m : ℕ) : ℝ :=
  if e=0 ∧ l=2 then if m=0 then 5 else 6
  else if e=1 ∧ l=0 then 1/2+(k:ℝ)
  else (e:ℝ)+5/2+(k:ℝ)/2

private lemma sourceBase_le_twice (v : ℝ) (hv : 0≤v) : v≤2*v := by
  linarith only [hv]

include hp in
private lemma sourceBase_norm_pos : (0:ℝ)<Ideal.absNorm (Ideal.span {p}) := by
  exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr
    (Ideal.span_singleton_eq_bot.not.mpr hp.ne_zero))

include hc in
private lemma sourceBase_kzero (n J : ℕ) (hn : n<5) :
    ‖sourceScalar p hp hg (n+1) 0 J‖≤
      2*(Ideal.absNorm (Ideal.span {p}):ℝ)^((n:ℝ)+1/2) := by
  rw [sourceScalar,if_neg (by omega : n+1≠0),Nat.add_sub_cancel]
  have hQ := sourceBase_norm_pos p hp
  have hs := nonprincipal_kzero_norm p hp hg hc n J hn
  rw [pow_mul_sqrt _ hQ] at hs
  exact hs.trans (sourceBase_le_twice _ (Real.rpow_nonneg hQ.le _))

include hc in
private lemma sourceBase_kone (n J : ℕ) (hn : 0<n) (hn6 : n<6) :
    ‖sourceScalar p hp hg (n+1) 1 J‖≤
      2*(Ideal.absNorm (Ideal.span {p}):ℝ)^((n+1:ℕ):ℝ) := by
  rw [sourceScalar,if_neg (by omega : n+1≠0),Nat.add_sub_cancel,Real.rpow_natCast]
  exact (nonprincipal_kone_norm p hp hg hc n J hn hn6).trans
    (sourceBase_le_twice _ (pow_nonneg (Nat.cast_nonneg _) _))

include hc in
private lemma sourceBase_principal_kone (J : ℕ) :
    ‖sourceScalar p hp hg 1 1 J‖≤
      2*(Ideal.absNorm (Ideal.span {p}):ℝ)^(3/2:ℝ) := by
  rw [sourceScalar,if_neg (by decide : (1:ℕ)≠0)]
  simp only [Nat.reduceSub]
  have hs := positiveScalar_norm_le p hp hg hc 0 1 J (by decide)
  simp only [Nat.zero_add,pow_one] at hs
  have he : (Ideal.absNorm (Ideal.span {p}):ℝ)*Real.sqrt (Ideal.absNorm (Ideal.span {p}):ℝ)=
      (Ideal.absNorm (Ideal.span {p}):ℝ)^(3/2:ℝ) := by
    have ht := pow_mul_sqrt _ (sourceBase_norm_pos p hp) 1
    norm_num only [Nat.cast_one,pow_one] at ht
    exact ht
  simpa only [mul_assoc,he] using hs

include hc in
private lemma sourceBase_even (j k m : ℕ) (hj : j<6) (hk : k≤1) :
    ‖sourceScalar p hp hg 6 k (j+6*m)‖≤
      2*(Ideal.absNorm (Ideal.span {p}):ℝ)^(if m=0 then (5:ℝ) else 6) := by
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hk with rfl|rfl
  · have hs := even_base_kzero_norm p hp hg hc m j hj
    rw [sourceScalar,if_neg (by decide : (6:ℕ)≠0)]
    simp only [Nat.reduceSub]
    by_cases hm : m=0
    · rw [if_pos hm] at hs ⊢
      simpa only [Real.rpow_ofNat] using
        hs.trans (sourceBase_le_twice _ (pow_nonneg (Nat.cast_nonneg _) 5))
    · rw [if_neg hm] at hs ⊢
      simpa only [Real.rpow_ofNat] using
        hs.trans (sourceBase_le_twice _ (pow_nonneg (Nat.cast_nonneg _) 6))
  · by_cases hm : m=0
    · subst m
      simp only [sourceScalar,Nat.reduceEqDiff,ite_false,Nat.reduceSub,mul_zero,add_zero,
        even_base_kone_zero p hp hg hc j hj,norm_zero,ite_true]
      positivity
    · rw [if_neg hm]
      simpa only [Nat.reduceAdd,Nat.cast_ofNat] using
        sourceBase_kone p hp hg hc 5 (j+6*m) (by decide) (by decide)

include hc in
private lemma sourceBase_scalar_bound (j e l k m : ℕ) (hj : j<6) (hk : k≤1)
    (hf : (e=0 ∧ l=2) ∨ (e=1 ∧ l=0) ∨ (e=0 ∧ l=1) ∨ (e=1 ∧ l=1)) :
    ‖sourceScalar p hp hg (e+3*l) k (j+6*m)‖≤
      2*(Ideal.absNorm (Ideal.span {p}):ℝ)^(sourceBaseExponent e l k m) := by
  rcases hf with ⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩
  · simpa [sourceBaseExponent] using sourceBase_even p hp hg hc j k m hj hk
  · rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hk with rfl|rfl
    · have hs := sourceBase_kzero p hp hg hc 0 (j+6*m) (by decide)
      norm_num [sourceBaseExponent] at hs ⊢
      exact hs
    · have hs := sourceBase_principal_kone p hp hg hc (j+6*m)
      norm_num [sourceBaseExponent] at hs ⊢
      exact hs
  · rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hk with rfl|rfl
    · have hs := sourceBase_kzero p hp hg hc 2 (j+6*m) (by decide)
      norm_num [sourceBaseExponent] at hs ⊢
      exact hs
    · have hs := sourceBase_kone p hp hg hc 2 (j+6*m) (by decide) (by decide)
      norm_num [sourceBaseExponent] at hs ⊢
      exact hs
  · rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hk with rfl|rfl
    · have hs := sourceBase_kzero p hp hg hc 3 (j+6*m) (by decide)
      norm_num [sourceBaseExponent] at hs ⊢
      exact hs
    · have hs := sourceBase_kone p hp hg hc 3 (j+6*m) (by decide) (by decide)
      norm_num [sourceBaseExponent] at hs ⊢
      exact hs

private lemma sourceBase_first_exponent (X W Z : ℝ)
    (hx : 51/100≤X) (hw : -(1/100)≤W) (hz : 17/50≤Z) (hxw : 1≤X+W)
    (e l k m : ℕ) (hk : k≤1)
    (hf : (e=0 ∧ l=2) ∨ (e=1 ∧ l=0) ∨ (e=0 ∧ l=1) ∨ (e=1 ∧ l=1)) :
    sourceBaseExponent e l k m-(X+1/2)*(e:ℝ)-(1+3*X)*(l:ℝ)-W*(k:ℝ)-6*Z*(m:ℝ)≤0 := by
  have hzm : 0≤6*Z*(m:ℝ) := by positivity
  have hzm1 (hm : m≠0) : 6*Z≤6*Z*(m:ℝ) := by
    have hm1 : (1:ℝ)≤ m := by exact_mod_cast (by omega : 1≤ m)
    have hzpos : 0≤6*Z := by linarith only [hz]
    nlinarith only [mul_nonneg hzpos (sub_nonneg.mpr hm1)]
  rcases hf with ⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩
  all_goals rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hk with rfl|rfl
  all_goals by_cases hm : m=0
  all_goals norm_num [sourceBaseExponent,hm]
  all_goals first
    | linarith only [hx,hw,hz,hxw,hzm]
    | linarith only [hx,hw,hz,hxw,hzm,hzm1 hm]


include hc in
theorem sourceRowTerm_first_base (eta a rho x w z : ℂ)
    (heta : ‖eta‖≤1) (ha : ‖a‖≤1) (hρ : rho^6=1)
    (hx : (51/100:ℝ)≤ x.re) (_hw : -(1/100:ℝ)≤ w.re) (hz : (17/50:ℝ)≤ z.re)
    (hxw : 1≤ x.re+w.re) (j e l k m : ℕ) (hj : j<6) (hk : k≤1)
    (hf : (e=0 ∧ l=2) ∨ (e=1 ∧ l=0) ∨ (e=0 ∧ l=1) ∨ (e=1 ∧ l=1)) :
    ‖sourceRowTerm p hp hg eta a rho x w z j e l k m‖≤2 := by
  apply sourceRowTerm_norm_from_scalar p hp hg hc eta a rho x w z heta ha hρ
    j e l k m (sourceBaseExponent e l k m)
  · exact sourceBase_scalar_bound p hp hg hc j e l k m hj hk hf
  · exact sourceBase_first_exponent x.re w.re z.re hx _hw hz hxw e l k m hk hf

end ProbeEuler
end

end

noncomputable section
open CenteredMomentFourier Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical BigOperators
namespace ProbeEuler
open Eisenstein CompletedGauss  ProbePrimePower
local notation "O" => Eisenstein.O
variable (p : O) (hp : Prime p) [(Ideal.span {p}:Ideal O).IsMaximal]
  (hg : lambda∉Ideal.span {p}) (hc : ringChar (O ⧸ Ideal.span {p})≠2)

lemma first_region_V_half (Q : ℝ) (hQ : 4≤ Q) (z : ℂ) (hz : (17/50:ℝ)≤ z.re) :
    ‖coordV Q z‖≤1/2 := by
  rw [coordV_norm Q (by linarith)]
  exact rpow_le_half Q _ hQ (by linarith)

lemma first_region_R_half (Q : ℝ) (hQ : 4≤ Q) (a x z : ℂ) (ha : ‖a‖≤1)
    (hx : (51/100:ℝ)≤ x.re) (hz : (17/50:ℝ)≤ z.re) :
    ‖evenRatio Q a ((Q:ℂ)^(-x)) (coordV Q z)‖≤1/2 := by
  rw [evenRatio_eq_coordR Q (by linarith)]
  apply (coordR_norm_le Q (by linarith) (a^2) x z (by simpa only [norm_pow] using pow_le_one₀ (norm_nonneg a) ha)).trans
  exact rpow_le_half Q _ hQ (by linarith)

include hc in
lemma rowBaseFinite_first_region (eta a rho x w z : ℂ)
    (hQ : (4:ℝ)≤ Ideal.absNorm (Ideal.span {p}))
    (heta : ‖eta‖≤1) (ha : ‖a‖≤1) (hρ : rho^6=1)
    (hx : (51/100:ℝ)≤ x.re) (hw : -(1/100:ℝ)≤ w.re) (hz : (17/50:ℝ)≤ z.re)
    (hxw : 1≤ x.re+w.re) (j e l : ℕ) (hj : j<6)
    (hf : (e=0 ∧ l=2) ∨ (e=1 ∧ l=0) ∨ (e=0 ∧ l=1) ∨ (e=1 ∧ l=1)) :
    ‖rowBaseFinite p hp hg eta a ((Ideal.absNorm (Ideal.span {p}):ℂ)^(-x))
      ((Ideal.absNorm (Ideal.span {p}):ℂ)^(-w)) (coordV (Ideal.absNorm (Ideal.span {p})) z)
      rho j e l‖≤16 := by
  have hv := ProbeLocal.inv_one_sub_norm_le_two _ (first_region_V_half _ hQ z hz)
  have ht' (k : Fin 2) (m : ℕ) :
      ‖rowMarkedTerm p hp hg eta a ((Ideal.absNorm (Ideal.span {p}):ℂ)^(-x))
        ((Ideal.absNorm (Ideal.span {p}):ℂ)^(-w)) (coordV (Ideal.absNorm (Ideal.span {p})) z)
        rho j e l k.val m‖≤2 := by
    have ht : e+3*l≠0 := by rcases hf with h|h|h|h <;> omega
    rw [←sourceRowTerm_pos p hp hg eta a rho x w z j e l k.val m ht]
    exact sourceRowTerm_first_base p hp hg hc eta a rho x w z heta ha hρ hx hw hz hxw
      j e l k.val m hj (by omega) hf
  unfold rowBaseFinite
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑ _k : Fin 2,(8:ℝ) := by
      apply Finset.sum_le_sum
      intro k hk
      apply (norm_add_le _ _).trans
      have hab := (norm_add_le _ _).trans (add_le_add (ht' k 0) (ht' k 1))
      have hd : ‖rowMarkedTerm p hp hg eta a ((Ideal.absNorm (Ideal.span {p}):ℂ)^(-x))
          ((Ideal.absNorm (Ideal.span {p}):ℂ)^(-w)) (coordV (Ideal.absNorm (Ideal.span {p})) z)
          rho j e l k.val 2/(1-coordV (Ideal.absNorm (Ideal.span {p})) z)‖≤4 := by
        rw [div_eq_mul_inv,norm_mul]
        exact (mul_le_mul (ht' k 2) hv (norm_nonneg _) (by norm_num)).trans_eq (by norm_num)
      linarith
    _ = _ := by norm_num

include hc in
theorem rowClosedMarked_first_region (eta a rho x w z : ℂ)
    (hQ : (4:ℝ)≤ Ideal.absNorm (Ideal.span {p}))
    (heta : ‖eta‖≤1) (ha : ‖a‖≤1) (hρ : rho^6=1)
    (hx : (51/100:ℝ)≤ x.re) (hw : -(1/100:ℝ)≤ w.re) (hz : (17/50:ℝ)≤ z.re) (hxw : 1≤ x.re+w.re) (j : ℕ) (hj : j<6) :
    ‖rowClosedMarked p hp hg eta a ((Ideal.absNorm (Ideal.span {p}):ℂ)^(-x))
      ((Ideal.absNorm (Ideal.span {p}):ℂ)^(-w)) (coordV (Ideal.absNorm (Ideal.span {p})) z) rho j‖≤128 := by
  have h02 := rowBaseFinite_first_region p hp hg hc eta a rho x w z hQ heta ha hρ hx hw hz hxw j 0 2 hj (by omega)
  have h10 := rowBaseFinite_first_region p hp hg hc eta a rho x w z hQ heta ha hρ hx hw hz hxw j 1 0 hj (by omega)
  have h01 := rowBaseFinite_first_region p hp hg hc eta a rho x w z hQ heta ha hρ hx hw hz hxw j 0 1 hj (by omega)
  have h11 := rowBaseFinite_first_region p hp hg hc eta a rho x w z hQ heta ha hρ hx hw hz hxw j 1 1 hj (by omega)
  have hr := ProbeLocal.inv_one_sub_norm_le_two _ (first_region_R_half _ hQ a x z ha hx hz)
  simp only [Complex.ofReal_natCast] at hr
  unfold rowClosedMarked
  rw [div_eq_mul_inv,norm_mul]
  apply (mul_le_mul_of_nonneg_right
    ((norm_add_le _ _).trans (add_le_add
      ((norm_add_le _ _).trans (add_le_add
        ((norm_add_le _ _).trans (add_le_add h02 h10)) h01)) h11)) (norm_nonneg _)).trans
  nlinarith

include hc in
theorem ramifiedClosed_first_region_bound (eta a rho x w z : ℂ)
    (hQ : (4:ℝ)≤ Ideal.absNorm (Ideal.span {p}))
    (heta : ‖eta‖≤1) (ha : ‖a‖≤1) (hρ : rho^6=1)
    (hx : (51/100:ℝ)≤ x.re) (hw : -(1/100:ℝ)≤ w.re) (hz : (17/50:ℝ)≤ z.re) (hxw : 1≤ x.re+w.re) (j : ℕ) (hj : j<6) :
    ‖ramifiedClosed p hp hg eta a rho x w z j‖≤193 := by
  have hb := rowClosedMarked_first_region p hp hg hc eta a rho x w z hQ heta ha hρ hx hw hz hxw j hj
  have hv := first_region_V_half _ hQ z hz
  have hs := norm_sub_le (1:ℂ) (coordV (Ideal.absNorm (Ideal.span {p})) z)
  simp only [norm_one] at hs
  unfold ramifiedClosed
  apply (norm_add_le _ _).trans
  rw [norm_one,norm_mul]
  have hm := mul_le_mul (show ‖1-coordV (Ideal.absNorm (Ideal.span {p})) z‖≤3/2 by linarith)
    hb (norm_nonneg _) (by norm_num : (0:ℝ)≤3/2)
  linarith

end ProbeEuler
end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
namespace ProbeEuler

theorem unramifiedClosed_first_region_bound (Q : ℝ) (A eta v x w z : ℂ) (eps : ℝ)
    (hQ : 4≤ Q) (hA : ‖A‖≤1) (heta : ‖eta‖≤1) (hv : ‖v‖≤1)
    (heps : 0< eps) (hx : (51/100:ℝ)≤ x.re) (hz : (17/50:ℝ)≤ z.re)
    (hw : -(1/100:ℝ)≤ w.re) (hxw : 1+eps≤ x.re+w.re) :
    ‖unramifiedClosed Q A eta v x w z-1‖≤240*Q^(-1-min eps (1/50:ℝ)) := by
  have hQ0 : 0< Q := by linarith
  have hQ1 : 1≤ Q := by linarith
  let V := coordV Q z
  let R := coordR Q A x z
  let W := coordW Q v w
  let D := coordD Q eta v x
  let K := coordK Q eta x w
  let L := Q^(1/100:ℝ)
  let E := Q^(-(109/100:ℝ))
  let T := Q^(-1-min eps (1/50:ℝ))
  have hL1 : 1≤ L := Real.one_le_rpow hQ1 (by norm_num)
  have hT : 0≤ T := Real.rpow_nonneg hQ0.le _
  have hV : ‖V‖≤ Q^(-(51/25:ℝ)) := by
    rw [show V=coordV Q z from rfl,coordV_norm Q hQ0]
    exact Real.rpow_le_rpow_of_exponent_le hQ1 (by linarith)
  have hR : ‖R‖≤ Q^(-(11/10:ℝ)) :=
    (coordR_norm_le Q hQ0 A x z hA).trans (Real.rpow_le_rpow_of_exponent_le hQ1 (by linarith))
  have hW : ‖W‖≤ L :=
    (coordW_norm_le Q hQ0 v w hv).trans (Real.rpow_le_rpow_of_exponent_le hQ1 (by linarith))
  have hD : ‖D‖≤ Q^(-(51/100:ℝ)) :=
    (coordD_norm_le Q hQ0 eta v x heta hv).trans (Real.rpow_le_rpow_of_exponent_le hQ1 (by linarith))
  have hK : ‖K‖≤ Q^(-eps) :=
    (coordK_norm_le Q hQ1 eta x w heta).trans (Real.rpow_le_rpow_of_exponent_le hQ1 (by linarith))
  have hVh : ‖V‖≤1/2 := hV.trans (rpow_le_half Q _ hQ (by norm_num))
  have hRh : ‖R‖≤1/2 := hR.trans (rpow_le_half Q _ hQ (by norm_num))
  have hDh : ‖D‖≤1/2 := hD.trans (rpow_le_half Q _ hQ (by norm_num))
  have hqi : ‖(Q:ℂ)⁻¹‖≤1 := by
    rw [norm_inv,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hQ0,←one_div]
    exact (div_le_one hQ0).mpr hQ1
  have hprod (a b aa bb c : ℝ) (ha : 0≤ a) (hb : 0≤ b)
      (haa : a≤ Q^aa) (hbb : b≤ Q^bb) (hc : aa+bb≤ c) : a*b≤ Q^c := by
    calc
      a*b≤ Q^aa*Q^bb := mul_le_mul haa hbb hb (Real.rpow_nonneg hQ0.le _)
      _=Q^(aa+bb) := (Real.rpow_add hQ0 _ _).symm
      _≤ Q^c := Real.rpow_le_rpow_of_exponent_le hQ1 hc
  have hRL : ‖R‖*L≤ E := hprod _ _ _ _ _ (norm_nonneg _) (by positivity) hR le_rfl (by norm_num)
  have hKV : ‖K‖*‖V‖≤ E := hprod _ _ _ _ _ (norm_nonneg _) (norm_nonneg _) hK hV (by linarith)
  have hRW : ‖R‖*(1+‖W‖)≤2*E := by
    calc
      _≤‖R‖*(2*L) := mul_le_mul_of_nonneg_left (by linarith) (norm_nonneg _)
      _≤2*E := by nlinarith
  let P := markedFactor R V (Q:ℂ)⁻¹ K (-D+W*R) 1
  have hPE : ‖P+D‖≤28*E := by
    have hh := ProbeLocal.unramified_marked_error_bound R V (Q:ℂ)⁻¹ K W D hRh hVh hqi hDh
    dsimp only [P]
    nlinarith
  have hEL : E*L≤ T := hprod _ _ _ _ _ (by positivity) (by positivity) le_rfl le_rfl
    (by have := min_le_right eps (1/50:ℝ);linarith)
  have hWE : (1+‖W‖)*‖P+D‖≤56*T := by
    calc
      _≤(2*L)*(28*E) := mul_le_mul (by linarith) hPE (norm_nonneg _) (by positivity)
      _≤56*T := by nlinarith
  have hDV : ‖D‖*‖V‖≤ T := hprod _ _ _ _ _ (norm_nonneg _) (norm_nonneg _) hD hV
    (by have := min_le_right eps (1/50:ℝ);linarith)
  have hVW : ‖V‖*‖W‖≤ T := hprod _ _ _ _ _ (norm_nonneg _) (norm_nonneg _) hV hW
    (by have := min_le_right eps (1/50:ℝ);linarith)
  have hDW : ‖D‖*‖W‖≤ T := hprod _ _ _ _ _ (norm_nonneg _) (norm_nonneg _)
    (coordD_norm_le Q hQ0 eta v x heta hv) (coordW_norm_le Q hQ0 v w hv)
    (by have := min_le_left eps (1/50:ℝ);linarith)
  have hDVW : ‖D‖*‖V‖*‖W‖≤ T := by
    calc
      _ = (‖D‖*‖W‖)*‖V‖ := by ring
      _ ≤ ‖D‖*‖W‖ := mul_le_of_le_one_right (by positivity) (by linarith)
      _ ≤ T := hDW
  have hh := ProbeLocal.continuedCorrection_defect_bound V W D P hVh hDh
  change ‖ProbeLocal.continuedCorrection V W D P-1‖≤240*T
  nlinarith

end ProbeEuler
end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
namespace ProbeEuler

theorem unramifiedClosed_first_neighborhood_bound (Q : ℝ) (A eta v x w z : ℂ) (eps : ℝ)
    (hQ : 4≤ Q) (hA : ‖A‖≤1) (heta : ‖eta‖≤1) (hv : ‖v‖≤1)
    (heps : 0< eps) (hx : (101/200:ℝ)≤ x.re) (hz : (27/80:ℝ)≤ z.re)
    (hw : -(3/200:ℝ)≤ w.re) (hxw : 1+eps≤ x.re+w.re) :
    ‖unramifiedClosed Q A eta v x w z-1‖≤240*Q^(-1-min eps (1/50:ℝ)) := by
  have hQ0 : 0< Q := by linarith
  have hQ1 : 1≤ Q := by linarith
  let V := coordV Q z
  let R := coordR Q A x z
  let W := coordW Q v w
  let D := coordD Q eta v x
  let K := coordK Q eta x w
  let L := Q^(3/200:ℝ)
  let E := Q^(-(26/25:ℝ))
  let T := Q^(-1-min eps (1/50:ℝ))
  have hL1 : 1≤ L := Real.one_le_rpow hQ1 (by norm_num)
  have hT : 0≤ T := Real.rpow_nonneg hQ0.le _
  have hV : ‖V‖≤ Q^(-(81/40:ℝ)) := by
    rw [show V=coordV Q z from rfl,coordV_norm Q hQ0]
    exact Real.rpow_le_rpow_of_exponent_le hQ1 (by linarith)
  have hR : ‖R‖≤ Q^(-(211/200:ℝ)) :=
    (coordR_norm_le Q hQ0 A x z hA).trans (Real.rpow_le_rpow_of_exponent_le hQ1 (by linarith))
  have hW : ‖W‖≤ L :=
    (coordW_norm_le Q hQ0 v w hv).trans (Real.rpow_le_rpow_of_exponent_le hQ1 (by linarith))
  have hD : ‖D‖≤ Q^(-(101/200:ℝ)) :=
    (coordD_norm_le Q hQ0 eta v x heta hv).trans (Real.rpow_le_rpow_of_exponent_le hQ1 (by linarith))
  have hK : ‖K‖≤ Q^(-eps) :=
    (coordK_norm_le Q hQ1 eta x w heta).trans (Real.rpow_le_rpow_of_exponent_le hQ1 (by linarith))
  have hVh : ‖V‖≤1/2 := hV.trans (rpow_le_half Q _ hQ (by norm_num))
  have hRh : ‖R‖≤1/2 := hR.trans (rpow_le_half Q _ hQ (by norm_num))
  have hDh : ‖D‖≤1/2 := hD.trans (rpow_le_half Q _ hQ (by norm_num))
  have hqi : ‖(Q:ℂ)⁻¹‖≤1 := by
    rw [norm_inv,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hQ0,←one_div]
    exact (div_le_one hQ0).mpr hQ1
  have hprod (a b aa bb c : ℝ) (ha : 0≤ a) (hb : 0≤ b)
      (haa : a≤ Q^aa) (hbb : b≤ Q^bb) (hc : aa+bb≤ c) : a*b≤ Q^c := by
    calc
      a*b≤ Q^aa*Q^bb := mul_le_mul haa hbb hb (Real.rpow_nonneg hQ0.le _)
      _=Q^(aa+bb) := (Real.rpow_add hQ0 _ _).symm
      _≤ Q^c := Real.rpow_le_rpow_of_exponent_le hQ1 hc
  have hRL : ‖R‖*L≤ E := hprod _ _ _ _ _ (norm_nonneg _) (by positivity) hR le_rfl (by norm_num)
  have hKV : ‖K‖*‖V‖≤ E := hprod _ _ _ _ _ (norm_nonneg _) (norm_nonneg _) hK hV (by linarith)
  have hRW : ‖R‖*(1+‖W‖)≤2*E := by
    calc
      _≤‖R‖*(2*L) := mul_le_mul_of_nonneg_left (by linarith) (norm_nonneg _)
      _≤2*E := by nlinarith
  let P := markedFactor R V (Q:ℂ)⁻¹ K (-D+W*R) 1
  have hPE : ‖P+D‖≤28*E := by
    have hh := ProbeLocal.unramified_marked_error_bound R V (Q:ℂ)⁻¹ K W D hRh hVh hqi hDh
    dsimp only [P]
    nlinarith
  have hEL : E*L≤ T := hprod _ _ _ _ _ (by positivity) (by positivity) le_rfl le_rfl
    (by have := min_le_right eps (1/50:ℝ);linarith)
  have hWE : (1+‖W‖)*‖P+D‖≤56*T := by
    calc
      _≤(2*L)*(28*E) := mul_le_mul (by linarith) hPE (norm_nonneg _) (by positivity)
      _≤56*T := by nlinarith
  have hDV : ‖D‖*‖V‖≤ T := hprod _ _ _ _ _ (norm_nonneg _) (norm_nonneg _) hD hV
    (by have := min_le_right eps (1/50:ℝ);linarith)
  have hVW : ‖V‖*‖W‖≤ T := hprod _ _ _ _ _ (norm_nonneg _) (norm_nonneg _) hV hW
    (by have := min_le_right eps (1/50:ℝ);linarith)
  have hDW : ‖D‖*‖W‖≤ T := hprod _ _ _ _ _ (norm_nonneg _) (norm_nonneg _)
    (coordD_norm_le Q hQ0 eta v x heta hv) (coordW_norm_le Q hQ0 v w hv)
    (by have := min_le_left eps (1/50:ℝ);linarith)
  have hDVW : ‖D‖*‖V‖*‖W‖≤ T := by
    calc
      _ = (‖D‖*‖W‖)*‖V‖ := by ring
      _ ≤ ‖D‖*‖W‖ := mul_le_of_le_one_right (by positivity) (by linarith)
      _ ≤ T := hDW
  have hh := ProbeLocal.continuedCorrection_defect_bound V W D P hVh hDh
  change ‖ProbeLocal.continuedCorrection V W D P-1‖≤240*T
  nlinarith

end ProbeEuler
end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical
namespace ProbeEuler
open Eisenstein CompletedGauss  ProbePrimePower
local notation "O" => Eisenstein.O
variable (p : O) (hp : Prime p) [(Ideal.span {p}:Ideal O).IsMaximal]
  (hg : lambda∉Ideal.span {p}) (hc : ringChar (O ⧸ Ideal.span {p})≠2)

include hc in
lemma sourceRowTerm_norm_from_scalar_power (eta a rho x w z : ℂ)
    (heta : ‖eta‖≤1) (ha : ‖a‖≤1) (hρ : rho^6=1)
    (j e l k m : ℕ) (nu B : ℝ)
    (hs : ‖sourceScalar p hp hg (e+3*l) k (j+6*m)‖≤2*(Ideal.absNorm (Ideal.span {p}):ℝ)^nu)
    (he : nu-(x.re+1/2)*(e:ℝ)-(1+3*x.re)*(l:ℝ)-w.re*(k:ℝ)-6*z.re*(m:ℝ)≤ B) :
    ‖sourceRowTerm p hp hg eta a rho x w z j e l k m‖≤2*(Ideal.absNorm (Ideal.span {p}):ℝ)^B := by
  have hP : Prime (Ideal.span {p}:Ideal O) := Ideal.prime_span_singleton_iff.mpr hp
  have hQ2 : (2:ℝ)≤ Ideal.absNorm (Ideal.span {p}) := by exact_mod_cast HeckeIdealSeries.prime_norm_two_le ⟨_,hP⟩
  have hQ : (0:ℝ)< Ideal.absNorm (Ideal.span {p}) := by linarith
  have hrho := Complex.norm_eq_one_of_pow_eq_one hρ (by decide : (6:ℕ)≠0)
  rw [sourceRowTerm,norm_mul,norm_div,norm_pow,norm_pow,hrho,one_pow,one_pow,div_self (by norm_num : (1:ℝ)≠0),one_mul]
  apply (sourceWeightedScalar_norm_le _ hQ eta a _ _ _ x w z _ heta ha
    (localGamma_norm_one p hp.ne_zero hg hc 1 (by decide) (by decide))
    (by rw [norm_star];exact localGamma_norm_one p hp.ne_zero hg hc 3 (by decide) (by decide))
    (Complex.norm_eq_one_of_pow_eq_one (complexSexticChar_neg_one_sq _ hg) (by decide)) e l k m).trans
  calc
    _ ≤ (2*(Ideal.absNorm (Ideal.span {p}):ℝ)^nu)*
      (Ideal.absNorm (Ideal.span {p}):ℝ)^(-(x.re+1/2)*(e:ℝ)-(1+3*x.re)*(l:ℝ)-w.re*(k:ℝ)-6*z.re*(m:ℝ)) :=
      mul_le_mul_of_nonneg_right hs (by positivity)
    _ = 2*(Ideal.absNorm (Ideal.span {p}):ℝ)^(nu-(x.re+1/2)*(e:ℝ)-(1+3*x.re)*(l:ℝ)-w.re*(k:ℝ)-6*z.re*(m:ℝ)) := by
      rw [mul_assoc,←Real.rpow_add hQ]
      congr 2
      ring
    _ ≤ 2*(Ideal.absNorm (Ideal.span {p}):ℝ)^B := by
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      exact Real.rpow_le_rpow_of_exponent_le (show (1:ℝ)≤ Ideal.absNorm (Ideal.span {p}) by linarith) he

private lemma sourceBase_selected_exponent (X W Z : ℝ)
    (hx : 7/8≤X) (hw : 1/2≤W) (hz : 17/50≤Z)
    (e l k m : ℕ) (hk : k≤1)
    (hf : (e=0 ∧ l=2) ∨ (e=1 ∧ l=0) ∨ (e=0 ∧ l=1) ∨ (e=1 ∧ l=1)) :
    sourceBaseExponent e l k m-(X+1/2)*(e:ℝ)-(1+3*X)*(l:ℝ)-W*(k:ℝ)-6*Z*(m:ℝ)≤
      -X+max (1-W) 0 := by
  have hb0 : (0:ℝ)≤ max (1-W) 0 := le_max_right _ _
  have hb1 : 1-W≤ max (1-W) 0 := le_max_left _ _
  have hzm : 0≤6*Z*(m:ℝ) := by positivity
  rcases hf with ⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩
  all_goals rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hk with rfl|rfl
  all_goals by_cases hm : m=0
  all_goals norm_num only [sourceBaseExponent,hm,Nat.cast_zero,Nat.cast_one,Nat.cast_ofNat,
    Nat.reduceEqDiff,and_true,and_false,ite_true,ite_false,zero_mul,one_mul,mul_zero,mul_one,
    sub_zero,add_zero,zero_add]
  all_goals linarith only [hx,hw,hz,hb0,hb1,hzm]


include hc in
theorem sourceRowTerm_selected_base (eta a rho x w z : ℂ)
    (heta : ‖eta‖≤1) (ha : ‖a‖≤1) (hρ : rho^6=1)
    (hx : (7/8:ℝ)≤ x.re) (_hw : (1/2:ℝ)≤ w.re) (hz : (17/50:ℝ)≤ z.re)
    (j e l k m : ℕ) (hj : j<6) (hk : k≤1)
    (hf : (e=0 ∧ l=2) ∨ (e=1 ∧ l=0) ∨ (e=0 ∧ l=1) ∨ (e=1 ∧ l=1)) :
    ‖sourceRowTerm p hp hg eta a rho x w z j e l k m‖≤2*(Ideal.absNorm (Ideal.span {p}):ℝ)^(-x.re+max (1-w.re) 0) := by
  apply sourceRowTerm_norm_from_scalar_power p hp hg hc eta a rho x w z heta ha hρ
    j e l k m (sourceBaseExponent e l k m) (-x.re+max (1-w.re) 0)
  · exact sourceBase_scalar_bound p hp hg hc j e l k m hj hk hf
  · exact sourceBase_selected_exponent x.re w.re z.re hx _hw hz e l k m hk hf

end ProbeEuler
end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical BigOperators
namespace ProbeEuler
open Eisenstein CompletedGauss  ProbePrimePower
local notation "O" => Eisenstein.O
variable (p : O) (hp : Prime p) [(Ideal.span {p}:Ideal O).IsMaximal]
  (hg : lambda∉Ideal.span {p}) (hc : ringChar (O ⧸ Ideal.span {p})≠2)

include hc in
lemma rowBaseFinite_selected_bound (eta a rho x w z : ℂ)
    (hQ : (4:ℝ)≤ Ideal.absNorm (Ideal.span {p}))
    (heta : ‖eta‖≤1) (ha : ‖a‖≤1) (hρ : rho^6=1)
    (hx : (7/8:ℝ)≤ x.re) (hw : (1/2:ℝ)≤ w.re) (hz : (17/50:ℝ)≤ z.re)
    (j e l : ℕ) (hj : j<6)
    (hf : (e=0 ∧ l=2) ∨ (e=1 ∧ l=0) ∨ (e=0 ∧ l=1) ∨ (e=1 ∧ l=1)) :
    ‖rowBaseFinite p hp hg eta a ((Ideal.absNorm (Ideal.span {p}):ℂ)^(-x))
      ((Ideal.absNorm (Ideal.span {p}):ℂ)^(-w)) (coordV (Ideal.absNorm (Ideal.span {p})) z)
      rho j e l‖≤16*(Ideal.absNorm (Ideal.span {p}):ℝ)^(-x.re+max (1-w.re) 0) := by
  have hpow : 0≤(Ideal.absNorm (Ideal.span {p}):ℝ)^(-x.re+max (1-w.re) 0) := by positivity
  have hv := ProbeLocal.inv_one_sub_norm_le_two _ (first_region_V_half _ hQ z hz)
  have ht' (k : Fin 2) (m : ℕ) :
      ‖rowMarkedTerm p hp hg eta a ((Ideal.absNorm (Ideal.span {p}):ℂ)^(-x))
        ((Ideal.absNorm (Ideal.span {p}):ℂ)^(-w)) (coordV (Ideal.absNorm (Ideal.span {p})) z)
        rho j e l k.val m‖≤2*(Ideal.absNorm (Ideal.span {p}):ℝ)^(-x.re+max (1-w.re) 0) := by
    have ht : e+3*l≠0 := by rcases hf with h|h|h|h <;> omega
    rw [←sourceRowTerm_pos p hp hg eta a rho x w z j e l k.val m ht]
    exact sourceRowTerm_selected_base p hp hg hc eta a rho x w z heta ha hρ hx hw hz
      j e l k.val m hj (by omega) hf
  unfold rowBaseFinite
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑ _k : Fin 2,8*(Ideal.absNorm (Ideal.span {p}):ℝ)^(-x.re+max (1-w.re) 0) := by
      apply Finset.sum_le_sum
      intro k hk
      apply (norm_add_le _ _).trans
      have hab := (norm_add_le _ _).trans (add_le_add (ht' k 0) (ht' k 1))
      have hd : ‖rowMarkedTerm p hp hg eta a ((Ideal.absNorm (Ideal.span {p}):ℂ)^(-x))
          ((Ideal.absNorm (Ideal.span {p}):ℂ)^(-w)) (coordV (Ideal.absNorm (Ideal.span {p})) z)
          rho j e l k.val 2/(1-coordV (Ideal.absNorm (Ideal.span {p})) z)‖≤4*(Ideal.absNorm (Ideal.span {p}):ℝ)^(-x.re+max (1-w.re) 0) := by
        rw [div_eq_mul_inv,norm_mul]
        exact (mul_le_mul (ht' k 2) hv (norm_nonneg _) (by positivity)).trans_eq (by ring)
      linarith
    _ = _ := by simp;ring

include hc in
theorem rowClosedMarked_selected_bound (eta a rho x w z : ℂ)
    (hQ : (4:ℝ)≤ Ideal.absNorm (Ideal.span {p}))
    (heta : ‖eta‖≤1) (ha : ‖a‖≤1) (hρ : rho^6=1)
    (hx : (7/8:ℝ)≤ x.re) (hw : (1/2:ℝ)≤ w.re) (hz : (17/50:ℝ)≤ z.re) (j : ℕ) (hj : j<6) :
    ‖rowClosedMarked p hp hg eta a ((Ideal.absNorm (Ideal.span {p}):ℂ)^(-x))
      ((Ideal.absNorm (Ideal.span {p}):ℂ)^(-w)) (coordV (Ideal.absNorm (Ideal.span {p})) z) rho j‖≤128*(Ideal.absNorm (Ideal.span {p}):ℝ)^(-x.re+max (1-w.re) 0) := by
  have hpow : 0≤(Ideal.absNorm (Ideal.span {p}):ℝ)^(-x.re+max (1-w.re) 0) := by positivity
  have h02 := rowBaseFinite_selected_bound p hp hg hc eta a rho x w z hQ heta ha hρ hx hw hz j 0 2 hj (by omega)
  have h10 := rowBaseFinite_selected_bound p hp hg hc eta a rho x w z hQ heta ha hρ hx hw hz j 1 0 hj (by omega)
  have h01 := rowBaseFinite_selected_bound p hp hg hc eta a rho x w z hQ heta ha hρ hx hw hz j 0 1 hj (by omega)
  have h11 := rowBaseFinite_selected_bound p hp hg hc eta a rho x w z hQ heta ha hρ hx hw hz j 1 1 hj (by omega)
  have hr := ProbeLocal.inv_one_sub_norm_le_two _ (first_region_R_half _ hQ a x z ha (by linarith) hz)
  simp only [Complex.ofReal_natCast] at hr
  unfold rowClosedMarked
  rw [div_eq_mul_inv,norm_mul]
  apply (mul_le_mul_of_nonneg_right
    ((norm_add_le _ _).trans (add_le_add
      ((norm_add_le _ _).trans (add_le_add
        ((norm_add_le _ _).trans (add_le_add h02 h10)) h01)) h11)) (norm_nonneg _)).trans
  nlinarith

end ProbeEuler
end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
namespace ProbeEuler
open Eisenstein CompletedGauss  ProbePrimePower
local notation "O" => Eisenstein.O
variable (p : O) (hp : Prime p) [(Ideal.span {p}:Ideal O).IsMaximal]
  (hg : lambda∉Ideal.span {p}) (hc : ringChar (O ⧸ Ideal.span {p})≠2)

def ramifiedSelected (eta a rho x w z : ℂ) (j : ℕ) : ℂ :=
  star eta*(Ideal.absNorm (Ideal.span {p}):ℂ)^x*(1-coordV (Ideal.absNorm (Ideal.span {p})) z)*
    rowClosedMarked p hp hg eta a ((Ideal.absNorm (Ideal.span {p}):ℂ)^(-x))
      ((Ideal.absNorm (Ideal.span {p}):ℂ)^(-w)) (coordV (Ideal.absNorm (Ideal.span {p})) z) rho j -
    (Ideal.absNorm (Ideal.span {p}):ℂ)^(-w)*ramifiedClosed p hp hg eta a rho x w z j

lemma ramifiedSelected_eq_replacement (eta a rho x w z : ℂ) (j : ℕ) :
    ramifiedSelected p hp hg eta a rho x w z j =
      ProbeLocal.compensatedReplacement (coordV (Ideal.absNorm (Ideal.span {p})) z) 0 0
        (rowClosedMarked p hp hg eta a ((Ideal.absNorm (Ideal.span {p}):ℂ)^(-x))
          ((Ideal.absNorm (Ideal.span {p}):ℂ)^(-w)) (coordV (Ideal.absNorm (Ideal.span {p})) z) rho j)
        (star eta*(Ideal.absNorm (Ideal.span {p}):ℂ)^x) ((Ideal.absNorm (Ideal.span {p}):ℂ)^(-w)) := by
  rw [ProbeLocal.continued_ramified_compensation]
  simp only [ramifiedSelected,ramifiedClosed,ProbeLocal.continuedCorrection,mul_zero,sub_zero,mul_one,div_one]

include hc in
theorem ramifiedSelected_bound (eta a rho x w z : ℂ)
    (hQ : (4:ℝ)≤ Ideal.absNorm (Ideal.span {p}))
    (heta : ‖eta‖≤1) (ha : ‖a‖≤1) (hρ : rho^6=1)
    (hx : (7/8:ℝ)≤ x.re) (hw : (1/2:ℝ)≤ w.re) (hz : (17/50:ℝ)≤ z.re) (j : ℕ) (hj : j<6) :
    ‖ramifiedSelected p hp hg eta a rho x w z j‖≤385*(Ideal.absNorm (Ideal.span {p}):ℝ)^(max (1-w.re) 0) := by
  let Q : ℝ := Ideal.absNorm (Ideal.span {p})
  let B : ℝ := max (1-w.re) 0
  have hQ0 : 0< Q := by dsimp [Q];linarith
  have hQ1 : 1≤ Q := by dsimp [Q];linarith
  have hB0 : 0≤ B := le_max_right _ _
  have hM := rowClosedMarked_selected_bound p hp hg hc eta a rho x w z hQ heta ha hρ hx hw hz j hj
  have hH := ramifiedClosed_first_region_bound p hp hg hc eta a rho x w z hQ heta ha hρ
    (by linarith) (by linarith) hz (by linarith) j hj
  have hV := first_region_V_half _ hQ z hz
  have h1V : ‖1-coordV (Ideal.absNorm (Ideal.span {p})) z‖≤3/2 := by
    have hh := norm_sub_le (1:ℂ) (coordV (Ideal.absNorm (Ideal.span {p})) z)
    simp only [norm_one] at hh
    linarith
  have hphase : ‖star eta*(Ideal.absNorm (Ideal.span {p}):ℂ)^x‖≤ Q^x.re := by
    change ‖star eta*(Q:ℂ)^x‖≤ Q^x.re
    rw [norm_mul,norm_star,Complex.norm_cpow_eq_rpow_re_of_pos hQ0]
    exact mul_le_of_le_one_left (Real.rpow_nonneg hQ0.le _) heta
  have hq : ‖(Ideal.absNorm (Ideal.span {p}):ℂ)^(-w)‖≤ Q^B := by
    change ‖(Q:ℂ)^(-w)‖≤ Q^B
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hQ0,Complex.neg_re]
    exact Real.rpow_le_rpow_of_exponent_le hQ1 (by dsimp [B];linarith)
  have he : Q^x.re*Q^(-x.re+B)=Q^B := by rw [←Real.rpow_add hQ0];congr 1;ring
  unfold ramifiedSelected
  apply (norm_sub_le _ _).trans
  simp only [norm_mul] at hphase ⊢
  calc
    _ ≤ (Q^x.re*(3/2))*(128*Q^(-x.re+B))+Q^B*193 := by
      gcongr
    _ = 385*Q^B := by nlinarith [he]

include hc in
theorem ramifiedSelected_small_bound (eta a rho x z : ℂ)
    (hQ : (4:ℝ)≤ Ideal.absNorm (Ideal.span {p}))
    (heta : ‖eta‖≤1) (ha : ‖a‖≤1) (hρ : rho^6=1)
    (hx : (7/8:ℝ)≤ x.re) (hz : (17/50:ℝ)≤ z.re) (t : ℝ) (j : ℕ) (hj : j<6) :
    ‖ramifiedSelected p hp hg eta a rho x ((1/2:ℂ)+t*Complex.I) z j‖≤
      385*(Ideal.absNorm (Ideal.span {p}):ℝ)^(1/2:ℝ) := by
  have hh := ramifiedSelected_bound p hp hg hc eta a rho x ((1/2:ℂ)+t*Complex.I) z hQ heta ha hρ hx
    (by norm_num [Complex.mul_re]) hz j hj
  norm_num [Complex.mul_re] at hh ⊢
  exact hh

include hc in
theorem ramifiedSelected_large_bound (eta a rho x w z : ℂ)
    (hQ : (4:ℝ)≤ Ideal.absNorm (Ideal.span {p}))
    (heta : ‖eta‖≤1) (ha : ‖a‖≤1) (hρ : rho^6=1)
    (hx : (7/8:ℝ)≤ x.re) (hw : 1≤ w.re) (hz : (17/50:ℝ)≤ z.re) (j : ℕ) (hj : j<6) :
    ‖ramifiedSelected p hp hg eta a rho x w z j‖≤385 := by
  have hh := ramifiedSelected_bound p hp hg hc eta a rho x w z hQ heta ha hρ hx (by linarith) hz j hj
  simpa only [max_eq_right (by linarith : 1-w.re≤0),Real.rpow_zero,mul_one] using hh

end ProbeEuler
end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
namespace ProbeLocal
theorem compensated_phase_error_bound (V W D P B q vInv : ℂ) (T : ℝ)
    (_hT : 0 ≤ T) (hV : ‖V‖ ≤ 1 / 2) (hW : ‖W‖ ≤ 1)
    (hD : ‖D‖ ≤ 1 / 2) (hq : ‖q‖ ≤ 1)
    (hVT : ‖V‖ ≤ T) (hDT : ‖D‖ ≤ T)
    (hE : ‖P + D‖ ≤ 28 * T) (hBE : ‖B‖ * ‖P + D‖ ≤ 28 * T)
    (hv : ‖vInv‖≤1) (hBD : B * D = vInv) (hWq : vInv*W = q) :
    ‖compensatedReplacement V W D P B q + continuedCorrection V W D P*vInv‖ ≤ 720 * T := by
  have h1V : ‖1 - V‖ ≤ 2 := by
    have := norm_sub_le (1 : ℂ) V
    simp only [norm_one] at this
    linarith
  have h1W : ‖1 - W‖ ≤ 2 := by
    have := norm_sub_le (1 : ℂ) W
    simp only [norm_one] at this
    linarith
  have h1q : ‖vInv - q‖ ≤ 2 := by
    have := norm_sub_le vInv q
    linarith
  have hiV := inv_one_sub_norm_le_two V hV
  have hiD := inv_one_sub_norm_le_two D hD
  have hfac : ‖(1 - V) * (1 - W) / (1 - D)‖ ≤ 8 := by
    rw [div_eq_mul_inv, norm_mul, norm_mul]
    calc
      ‖1 - V‖ * ‖1 - W‖ * ‖(1 - D)⁻¹‖ ≤ (2 : ℝ) * 2 * 2 := by gcongr
      _ = 8 := by norm_num
  have hleft : ‖(vInv - q) * (V / (1 - V) - D)‖ ≤ 6 * T := by
    calc
      _ = ‖vInv - q‖ * ‖V / (1 - V) - D‖ := norm_mul _ _
      _ ≤ 2 * (‖V‖ * 2 + ‖D‖) := by
        gcongr
        calc
          _ ≤ ‖V / (1 - V)‖ + ‖D‖ := norm_sub_le _ _
          _ ≤ _ := by rw [div_eq_mul_inv, norm_mul]; gcongr
      _ ≤ 6 * T := by linarith
  have hright : ‖(B + vInv - q) * (P + D)‖ ≤ 84 * T := by
    have hc : ‖B + vInv - q‖ ≤ ‖B‖ + 2 := by
      calc
        _ = ‖B + (vInv - q)‖ := by congr 1; ring
        _ ≤ ‖B‖ + ‖vInv - q‖ := norm_add_le _ _
        _ ≤ _ := by linarith
    calc
      _ = ‖B + vInv - q‖ * ‖P + D‖ := norm_mul _ _
      _ ≤ (‖B‖ + 2) * ‖P + D‖ := mul_le_mul_of_nonneg_right hc (norm_nonneg _)
      _ ≤ 84 * T := by nlinarith
  have hid := continued_normalized_cancellation V W D P B q vInv
    (one_sub_ne_zero_of_norm_le_half V hV) (one_sub_ne_zero_of_norm_le_half D hD)
    hBD hWq
  rw [hid, norm_mul]
  calc
    _ ≤ 8 * (‖(vInv - q) * (V / (1 - V) - D)‖ + ‖(B + vInv - q) * (P + D)‖) := by
      gcongr
      exact norm_add_le _ _
    _ ≤ 720 * T := by linarith

end ProbeLocal
end

end

end GaloisForLFunctions.MetaplecticMobiusDescent.CubicEisenstein
