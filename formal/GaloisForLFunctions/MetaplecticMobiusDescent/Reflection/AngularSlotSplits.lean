import GaloisForLFunctions.MetaplecticMobiusDescent.Reflection.AngularSlotRows
import GaloisForLFunctions.MetaplecticMobiusDescent.Reflection.OriginalSlotSplits

/-!
# Dyadic and original-slot identities for angular rows

Dyadic partitions and supported slot choices preserve the angular reflected source.
Finite Cauchy–Schwarz aggregation has the same dyadic cardinality cost.
-/

open scoped BigOperators Classical ContDiff ComplexConjugate
namespace GaloisForLFunctions.MetaplecticMobiusDescent.CubicEisenstein
open Eisenstein CubicJacobi CubicKubota CubicRamified RationalSource CompletedGauss
open CompletedDyadic CanonicalRowCompletion SchwartzPlanePoisson NormalizedReflection
open CanonicalQuadraticSieve InverseMoment InverseTerminalWidths
namespace InverseReflectedPhase
noncomputable section
local notation "Eis" => Eisenstein.O
section
variable (ℓ : ℕ)
variable {φ σ : Type*} [Fintype φ] [Fintype σ]
variable {N a c : Eis} {mode : Bool}
variable (G : PrimeFamily φ) (rows : Finset (Ideal Eis)) (hrows : ∀ K∈rows,Admissible K)
    (tuples : Finset (σ→Ideal Eis)) (hmax : ∀ p∈tuples,∀ i,(p i).IsMaximal)
    (hgood : ∀ p∈tuples,∀ i,lambda∉p i) (Hrow Hslot : ℝ)
variable (C : ∀ i : Fin (columnDyadicLength Hrow+1),∀ j : Fin (columnDyadicLength Hslot+1),
    ∀ K : divisorDyadicBin rows Hrow i,∀ p : activeTupleDyad tuples Hslot j,
      IsCoprime K.val (slotTupleProduct p.val)→
      ControlledStratumArithmetic (G.reflected K.val (hrows K.val (divisorDyadicBin_subset rows Hrow i K.property))
        (memberTupleFamily tuples hmax hgood ⟨p.val,activeTupleDyad_subset tuples Hslot j p.property⟩)).generator N a c mode)
variable (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode)) (hc : c≠0)
    (jF : φ→ℕ) (W : ℝ→ℂ) (θ X : ℝ) (r : Ideal Eis→ℂ) (aw : (σ→Ideal Eis)→ℂ)

def angularDyadicPhysicalTerm (K : rows) (p : tuples) : ℂ :=
  if hp:IsCoprime K.val (slotTupleProduct p.val) then
    r K.val*aw p.val*angularMixedReflectedValue ℓ
      (dyadicTupleControlled G rows hrows tuples hmax hgood Hrow Hslot C K p hp) s
      (G.reflected K.val (hrows K.val K.property) (memberTupleFamily tuples hmax hgood p)).generator_ne_zero hc
      (G.reflected K.val (hrows K.val K.property) (memberTupleFamily tuples hmax hgood p)).generator_good
      (reflectedExponent jF) (slotIndices φ (PrimeIndex K.val) σ) (CompletedHeight.normTwistedSource W θ) X else 0

lemma angularDyadicPhysicalTerm_at (i : Fin (columnDyadicLength Hrow+1))
    (j : Fin (columnDyadicLength Hslot+1))
    (K : divisorDyadicBin rows Hrow i) (p : activeTupleDyad tuples Hslot j) :
    angularDyadicPhysicalTerm ℓ G rows hrows tuples hmax hgood Hrow Hslot C s hc jF W θ X r aw
      ⟨K.val,divisorDyadicBin_subset rows Hrow i K.property⟩
      ⟨p.val,activeTupleDyad_subset tuples Hslot j p.property⟩=
    if hp:IsCoprime K.val (slotTupleProduct p.val) then
      r K.val*aw p.val*angularMixedReflectedValue ℓ (C i j K p hp) s
        (G.reflected K.val (hrows K.val (divisorDyadicBin_subset rows Hrow i K.property))
          (memberTupleFamily tuples hmax hgood ⟨p.val,activeTupleDyad_subset tuples Hslot j p.property⟩)).generator_ne_zero hc
        (G.reflected K.val (hrows K.val (divisorDyadicBin_subset rows Hrow i K.property))
          (memberTupleFamily tuples hmax hgood ⟨p.val,activeTupleDyad_subset tuples Hslot j p.property⟩)).generator_good
        (reflectedExponent jF) (slotIndices φ (PrimeIndex K.val) σ) (CompletedHeight.normTwistedSource W θ) X else 0 := by
  unfold angularDyadicPhysicalTerm
  split_ifs with hp
  · rw [dyadicTupleControlled_at]
  · rfl

theorem angular_dyadic_physical_energy (E : ℝ)
    (hE : ∀ i : Fin (columnDyadicLength Hrow+1),∀ j : Fin (columnDyadicLength Hslot+1),
      (∑ K : rows.filter (fun K => divisorDyadicLabel Hrow K=i),
        ‖∑ p : tuples.filter (fun p => divisorDyadicLabel Hslot (slotTupleProduct p)=j),
          angularDyadicPhysicalTerm ℓ G rows hrows tuples hmax hgood Hrow Hslot C s hc jF W θ X r aw
            ⟨K.val,(Finset.mem_filter.mp K.property).1⟩
            ⟨p.val,(Finset.mem_filter.mp p.property).1⟩‖^2)≤ E) :
    (∑ K : rows,‖∑ p : tuples,
      angularDyadicPhysicalTerm ℓ G rows hrows tuples hmax hgood Hrow Hslot C s hc jF W θ X r aw K p‖^2)≤
      (columnDyadicLength Hrow+1:ℝ)*(columnDyadicLength Hslot+1:ℝ)^2*E := by
  have he := dependent_partition_energy rows tuples (divisorDyadicLabel Hrow)
    (fun p => divisorDyadicLabel Hslot (slotTupleProduct p))
    (angularDyadicPhysicalTerm ℓ G rows hrows tuples hmax hgood Hrow Hslot C s hc jF W θ X r aw)
  apply he.trans
  have hb := Finset.sum_le_sum (s:=Finset.univ) (fun i _ =>
    Finset.sum_le_sum (s:=Finset.univ) (fun j _ => hE i j))
  apply (mul_le_mul_of_nonneg_left hb (Nat.cast_nonneg (Fintype.card (Fin (columnDyadicLength Hslot+1))))).trans_eq
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,Nat.cast_add,Nat.cast_one]
  ring

end

section
variable (ℓ : ℕ)
variable {φ σ : Type*} [Fintype φ] [Fintype σ]
variable {N a c : Eis} {mode : Bool}
variable (G : PrimeFamily φ) (rows : Finset (Ideal Eis)) (hrows : ∀ K∈rows,Admissible K)
    (tuples : Finset (σ→Ideal Eis)) (hmax : ∀ p∈tuples,∀ i,(p i).IsMaximal)
    (hgood : ∀ p∈tuples,∀ i,lambda∉p i) (Hrow Hslot : ℝ)

variable (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode)) (hc : c≠0)
    (jF : φ→ℕ) (W : ℝ→ℂ) (X : ℝ)

def angularCellPhysicalTerm (i : Fin (columnDyadicLength Hrow+1)) (j : Fin (columnDyadicLength Hslot+1))
    (D : CellCompletion (N:=N) (a:=a) (c:=c) (mode:=mode) G rows hrows tuples hmax hgood Hrow Hslot i j)
    (θ : ℝ) (r : Ideal Eis→ℂ) (aw : (σ→Ideal Eis)→ℂ)
    (K : divisorDyadicBin rows Hrow i) (p : activeTupleDyad tuples Hslot j) : ℂ :=
    if hp:IsCoprime K.val (slotTupleProduct p.val) then
      r K.val*aw p.val*angularMixedReflectedValue ℓ (D K p hp) s
        (G.reflected K.val (hrows K.val (divisorDyadicBin_subset rows Hrow i K.property))
          (memberTupleFamily tuples hmax hgood ⟨p.val,activeTupleDyad_subset tuples Hslot j p.property⟩)).generator_ne_zero hc
        (G.reflected K.val (hrows K.val (divisorDyadicBin_subset rows Hrow i K.property))
          (memberTupleFamily tuples hmax hgood ⟨p.val,activeTupleDyad_subset tuples Hslot j p.property⟩)).generator_good
        (reflectedExponent jF) (slotIndices φ (PrimeIndex K.val) σ) (CompletedHeight.normTwistedSource W θ) X else 0

theorem angular_physical_dyad_selection_energy (E : ℝ→ℝ) (hE : ∀ θ,0≤ E θ)
    (he : ∀ i : Fin (columnDyadicLength Hrow+1),∀ j : Fin (columnDyadicLength Hslot+1),
      (divisorDyadicBin rows Hrow i).Nonempty → (activeTupleDyad tuples Hslot j).Nonempty →
      ∃ D : CellCompletion (N:=N) (a:=a) (c:=c) (mode:=mode) G rows hrows tuples hmax hgood Hrow Hslot i j,
      ∀ (θ : ℝ) (r : Ideal Eis→ℂ) (aw : (σ→Ideal Eis)→ℂ),
        (∀ K∈rows,‖r K‖≤1) → (∀ p∈tuples,‖aw p‖≤1) →
        (∑ K : divisorDyadicBin rows Hrow i,‖∑ p : activeTupleDyad tuples Hslot j,
          angularCellPhysicalTerm ℓ G rows hrows tuples hmax hgood Hrow Hslot s hc jF W X i j D θ r aw K p‖^2)≤ E θ) :
    ∃ D : ∀ i : Fin (columnDyadicLength Hrow+1),∀ j : Fin (columnDyadicLength Hslot+1),
      CellCompletion (N:=N) (a:=a) (c:=c) (mode:=mode) G rows hrows tuples hmax hgood Hrow Hslot i j,
      ∀ (θ : ℝ) (r : Ideal Eis→ℂ) (aw : (σ→Ideal Eis)→ℂ),
        (∀ K∈rows,‖r K‖≤1) → (∀ p∈tuples,‖aw p‖≤1) →
        (∑ K : rows,‖∑ p : tuples,
          angularDyadicPhysicalTerm ℓ G rows hrows tuples hmax hgood Hrow Hslot D s hc jF W θ X r aw K p‖^2)≤
          (columnDyadicLength Hrow+1:ℝ)*(columnDyadicLength Hslot+1:ℝ)^2*E θ := by
  have hall : ∀ i : Fin (columnDyadicLength Hrow+1),∀ j : Fin (columnDyadicLength Hslot+1),
      ∃ D : CellCompletion (N:=N) (a:=a) (c:=c) (mode:=mode) G rows hrows tuples hmax hgood Hrow Hslot i j,
      ∀ (θ : ℝ) (r : Ideal Eis→ℂ) (aw : (σ→Ideal Eis)→ℂ),
        (∀ K∈rows,‖r K‖≤1) → (∀ p∈tuples,‖aw p‖≤1) →
        (∑ K : divisorDyadicBin rows Hrow i,‖∑ p : activeTupleDyad tuples Hslot j,
          angularCellPhysicalTerm ℓ G rows hrows tuples hmax hgood Hrow Hslot s hc jF W X i j D θ r aw K p‖^2)≤ E θ := by
    intro i j
    by_cases hi : (divisorDyadicBin rows Hrow i).Nonempty
    · by_cases hj : (activeTupleDyad tuples Hslot j).Nonempty
      · exact he i j hi hj
      · let D : CellCompletion (N:=N) (a:=a) (c:=c) (mode:=mode) G rows hrows tuples hmax hgood Hrow Hslot i j :=
          fun K p hp => (hj ⟨p.val,p.property⟩).elim
        refine ⟨D,?_⟩
        intro θ r aw hr haw
        have hzero : ∀ K : divisorDyadicBin rows Hrow i,
            (∑ p : activeTupleDyad tuples Hslot j,
              angularCellPhysicalTerm ℓ G rows hrows tuples hmax hgood Hrow Hslot s hc jF W X i j D θ r aw K p)=0 := by
          intro K
          apply Finset.sum_eq_zero
          intro p hp
          exact (hj ⟨p.val,p.property⟩).elim
        simp_rw [hzero,norm_zero,zero_pow (by norm_num : (2:ℕ)≠0),Finset.sum_const_zero]
        exact hE θ
    · let D : CellCompletion (N:=N) (a:=a) (c:=c) (mode:=mode) G rows hrows tuples hmax hgood Hrow Hslot i j :=
        fun K p hp => (hi ⟨K.val,K.property⟩).elim
      refine ⟨D,?_⟩
      intro θ r aw hr haw
      have hzero : (∑ K : divisorDyadicBin rows Hrow i,‖∑ p : activeTupleDyad tuples Hslot j,
          angularCellPhysicalTerm ℓ G rows hrows tuples hmax hgood Hrow Hslot s hc jF W X i j D θ r aw K p‖^2)=0 := by
        apply Finset.sum_eq_zero
        intro K hK
        exact (hi ⟨K.val,K.property⟩).elim
      rw [hzero]
      exact hE θ
  choose D hD using hall
  refine ⟨D,?_⟩
  intro θ r aw hr haw
  apply angular_dyadic_physical_energy ℓ G rows hrows tuples hmax hgood Hrow Hslot D s hc jF W θ X r aw (E θ)
  intro i j
  have hid : (∑ K : divisorDyadicBin rows Hrow i,‖∑ p : activeTupleDyad tuples Hslot j,
      angularDyadicPhysicalTerm ℓ G rows hrows tuples hmax hgood Hrow Hslot D s hc jF W θ X r aw
        ⟨K.val,divisorDyadicBin_subset rows Hrow i K.property⟩
        ⟨p.val,activeTupleDyad_subset tuples Hslot j p.property⟩‖^2)=
      ∑ K : divisorDyadicBin rows Hrow i,‖∑ p : activeTupleDyad tuples Hslot j,
        angularCellPhysicalTerm ℓ G rows hrows tuples hmax hgood Hrow Hslot s hc jF W X i j (D i j) θ r aw K p‖^2 := by
    apply Finset.sum_congr rfl
    intro K hK
    apply congrArg (fun z : ℂ => ‖z‖^2)
    apply Finset.sum_congr rfl
    intro p hp
    exact angularDyadicPhysicalTerm_at ℓ G rows hrows tuples hmax hgood Hrow Hslot D s hc jF W θ X r aw i j K p
  exact hid.trans_le (hD i j θ r aw hr haw)
end

section
variable (ℓ : ℕ)
variable {σ φ τ : Type*} [Fintype σ] [DecidableEq σ] [Fintype τ]
variable (L : σ→Finset (Ideal Eis)) (F : φ→Ideal Eis)
    (hmax : ∀ i,∀ P∈L i,P.IsMaximal)
    (hgood : ∀ i,∀ P∈L i,lambda∉P)

variable {N a c : Eis} {mode : Bool} (G : PrimeFamily τ) (K : Ideal Eis) (hK : Admissible K)
variable (D : ∀ p : fixedSlotTupleSet L F,IsCoprime K (slotTupleProduct p.val)→
    ControlledStratumArithmetic (G.reflected K hK
      (memberTupleFamily (fixedSlotTupleSet L F) (originalTupleMax L F hmax) (originalTupleGood L F hgood) p)).generator N a c mode)

theorem angular_member_source_eq_original_choices
    (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode)) (hc : c≠0)
    (jF : τ→ℕ) (W : ℝ→ℂ) (X : ℝ) (r : ℂ) (w : ∀ i,L i→ℂ) :
    (∑ p : fixedSlotTupleSet L F,if hp:IsCoprime K (slotTupleProduct p.val) then
      r*fixedTupleCoefficient L w p.val*angularMixedReflectedValue ℓ (D p hp) s
        (G.reflected K hK (memberTupleFamily (fixedSlotTupleSet L F)
          (originalTupleMax L F hmax) (originalTupleGood L F hgood) p)).generator_ne_zero hc
        (G.reflected K hK (memberTupleFamily (fixedSlotTupleSet L F)
          (originalTupleMax L F hmax) (originalTupleGood L F hgood) p)).generator_good
        (reflectedExponent jF) (slotIndices τ (PrimeIndex K) σ) W X else 0)=
    ∑ p : supportedSlotChoices L F K,r*(∏ i,w i (p.val i))*
      angularMixedReflectedValue ℓ (memberChoiceControlled L F hmax hgood G K hK D p) s
        (G.reflected K hK (slotChoiceFamily L hmax hgood p.val)).generator_ne_zero hc
        (G.reflected K hK (slotChoiceFamily L hmax hgood p.val)).generator_good
        (reflectedExponent jF) (slotIndices τ (PrimeIndex K) σ) W X := by
  let e := supportedSlotTupleEquiv L F K
  have he := sum_subtype_dite_decidable (fun p : fixedSlotTupleSet L F => IsCoprime K (slotTupleProduct p.val))
    (fun p hp => r*fixedTupleCoefficient L w p.val*angularMixedReflectedValue ℓ (D p hp) s
      (G.reflected K hK (memberTupleFamily (fixedSlotTupleSet L F)
        (originalTupleMax L F hmax) (originalTupleGood L F hgood) p)).generator_ne_zero hc
      (G.reflected K hK (memberTupleFamily (fixedSlotTupleSet L F)
        (originalTupleMax L F hmax) (originalTupleGood L F hgood) p)).generator_good
      (reflectedExponent jF) (slotIndices τ (PrimeIndex K) σ) W X)
  rw [←he,←e.sum_comp]
  apply Finset.sum_congr rfl
  intro p hp
  change r*fixedTupleCoefficient L w (fun i => (p.val i).val)*_=_
  rw [fixedTupleCoefficient_at]
  rfl
end

end
end InverseReflectedPhase
end GaloisForLFunctions.MetaplecticMobiusDescent.CubicEisenstein
