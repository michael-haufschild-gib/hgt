import GaloisForLFunctions.HTGeometry.Quantum.TwoCopyChargeObservations
import Mathlib.GroupTheory.FreeAbelianGroup

/-!
# Characters of the occupied charge gaps

Two-copy and three-copy superselection data together have a universal
ambiguity group. It has one generator per occupied gap and one additive
relation per occupied triangle. Each indistinguishable matrix determines a
unique circle character of this group, even for sparse charge spectra.
-/

noncomputable section
namespace GaloisForLFunctions.HTGeometry.Quantum.ChargeGaps
open FreeAbelianGroup
variable {κ V : Type*} [AddCommGroup κ] [AddCommGroup V]

/-- Every additive triangle in the observed support gives one relation. -/
def relations (D : Set κ) : AddSubgroup (FreeAbelianGroup D) :=
  AddSubgroup.closure {r | ∃ a b c : D, a.val+b.val=c.val ∧ r=of a+of b-of c}

abbrev Presentation (D : Set κ) := FreeAbelianGroup D ⧸ relations D

def gen (D : Set κ) (d : D) : Presentation D := QuotientAddGroup.mk' (relations D) (of d)

theorem triangle (D : Set κ) (a b c : D) (h : a.val+b.val=c.val) :
    gen D a + gen D b = gen D c := by
  apply sub_eq_zero.mp
  simp only [gen,← map_add,← map_sub]
  exact (QuotientAddGroup.eq_zero_iff _).2 (AddSubgroup.subset_closure ⟨a,b,c,h,rfl⟩)

/-- Homomorphisms out of the presentation are determined on occupied gaps. -/
theorem hom_ext (D : Set κ) (f g : Presentation D →+ V)
    (h : ∀ d, f (gen D d)=g (gen D d)) : f=g := by
  let π := QuotientAddGroup.mk' (relations D)
  have he : f.comp π = g.comp π := FreeAbelianGroup.lift_ext _ _ h
  apply DFunLike.ext
  intro x
  obtain ⟨y,rfl⟩ := QuotientAddGroup.mk'_surjective (relations D) x
  exact DFunLike.congr_fun he y

/-- An assigned value on each generator extends uniquely precisely when it
respects additive triangles of the support. -/
theorem extends_iff (D : Set κ) (u : D → V) :
    (∃! f : Presentation D →+ V, ∀ d, f (gen D d) = u d) ↔
      ∀ a b c : D, a.val+b.val=c.val → u a+u b=u c := by
  constructor
  · rintro ⟨f,hf,_⟩ a b c h
    rw [← hf,← hf,← hf,← map_add,triangle D a b c h]
  · intro h
    let f := FreeAbelianGroup.lift u
    have hk : relations D ≤ f.ker := by
      apply (AddSubgroup.closure_le _).mpr
      rintro _ ⟨a,b,c,he,rfl⟩
      change f (of a+of b-of c)=0
      simp only [map_sub,map_add,f,lift_apply_of,h a b c he,sub_self]
    let F := QuotientAddGroup.lift (relations D) f hk
    have H (d : D) : F (gen D d) = u d := FreeAbelianGroup.lift_apply_of u d
    exact ⟨F,H,fun g hg => hom_ext D g F fun d => (hg d).trans (H d).symm⟩

/-- Every formal gap has an actual charge, via the homomorphism sending
generators to their given labels. -/
def charge (D : Set κ) : Presentation D →+ κ :=
  ((extends_iff D (fun d => d.val)).2 (fun _ _ _ h => h)).exists.choose

theorem charge_gen (D : Set κ) (d : D) : charge D (gen D d) = d.val :=
  ((extends_iff D (fun d => d.val)).2 (fun _ _ _ h => h)).exists.choose_spec d

/-- The charge map is an isomorphism for a fully occupied charge group. -/
def fullEquiv : Presentation (Set.univ : Set κ) ≃+ κ := by
  let g (d : κ) := gen (Set.univ : Set κ) ⟨d,Set.mem_univ _⟩
  have hadd (a b : κ) : g (a+b) = g a+g b := (triangle _ _ _ _ rfl).symm
  let G : κ →+ Presentation (Set.univ : Set κ) :=
    { toFun := g, map_add' := hadd, map_zero' := by
        have h := hadd 0 0
        rw [add_zero] at h
        exact add_left_cancel (show g 0 + g 0 = g 0 + 0 by rw [← h,add_zero]) }
  have h₁ : G.comp (charge Set.univ) = AddMonoidHom.id _ := by
    apply hom_ext
    intro d
    rw [AddMonoidHom.comp_apply,charge_gen]
    rfl
  exact { charge Set.univ with invFun := G
                               left_inv := fun x => DFunLike.congr_fun h₁ x
                               right_inv := fun x => charge_gen _ ⟨x,Set.mem_univ _⟩ }

variable {ι : Type*} [Fintype ι] [DecidableEq ι] [DecidableEq κ]

/-- The character relating two observed matrices is unique even with missing
gaps. At zero entries the second matrix must vanish. -/
theorem observation_fiber (q : ι → κ) (A B : Matrix ι ι ℂ) :
    let D := {d | occupiedGap q A d}
    (pairedCharge q A = pairedCharge q B ∧ tripleCharge q A = tripleCharge q B) ↔
      ((∀ i j, A i j=0 → B i j=0) ∧ ∃! f : Presentation D →+ Additive Circle,
        ∀ i j (ha : A i j ≠ 0), B i j =
          (((f (gen D ⟨q i-q j,i,j,rfl,ha⟩)).toMul : Circle) : ℂ)*A i j) := by
  classical
  intro D
  constructor
  · rintro ⟨hp,ht⟩
    obtain ⟨u,hu,he⟩ := (pairedCharge_eq_iff_gap_phases q A B).1 hp
    let v (d : κ) : Circle := ⟨u d,mem_sphere_zero_iff_norm.2 (hu d)⟩
    have hb : B = fun i j => (v (q i-q j) : ℂ)*A i j := funext fun i => funext fun j => he i j
    rw [hb] at ht
    have h := (tripleCharge_eq_iff_phase_add q A v).1 ht
    have hv (a b c : D) (heq : a.val+b.val=c.val) :
        Additive.ofMul (v a.val) + Additive.ofMul (v b.val) = Additive.ofMul (v c.val) := by
      change v a.val*v b.val = v c.val
      rw [← heq]
      exact (h a b a.property b.property (heq ▸ c.property)).symm
    obtain ⟨f,hf,_⟩ := (extends_iff D (fun d => Additive.ofMul (v d.val))).2 hv
    refine ⟨fun i j hz => by rw [he,hz,mul_zero],f,?_,?_⟩
    · intro i j ha
      rw [hf]
      exact he i j
    · intro g hg
      apply hom_ext
      intro d
      obtain ⟨i,j,hd,ha⟩ := d.property
      have hgen : (⟨q i-q j,i,j,rfl,ha⟩ : D) = d := Subtype.ext hd
      have hs := hg i j ha
      rw [hgen,he,hd] at hs
      rw [hf]
      apply Circle.ext
      exact (mul_right_cancel₀ ha hs).symm
  · rintro ⟨hz,⟨f,hf,_⟩⟩
    let u (d : κ) : Circle := if h : d ∈ D then (f (gen D ⟨d,h⟩)).toMul else 1
    have he (i j : ι) : B i j = (u (q i-q j) : ℂ)*A i j := by
      by_cases ha : A i j=0
      · rw [ha,hz i j ha,mul_zero]
      · simpa only [u,dif_pos (show q i-q j ∈ D from ⟨i,j,rfl,ha⟩)] using hf i j ha
    refine ⟨(pairedCharge_eq_iff_gap_phases q A B).2 ⟨_,fun d => (u d).norm_coe,he⟩,?_⟩
    rw [show B = fun i j => (u (q i-q j) : ℂ)*A i j from funext fun i => funext fun j => he i j]
    apply (tripleCharge_eq_iff_phase_add q A u).2
    intro a b ha hb hc
    simp only [u,dif_pos (show a ∈ D from ha),dif_pos (show b ∈ D from hb),
      dif_pos (show a+b ∈ D from hc)]
    exact congrArg Additive.toMul (((congrArg f (triangle D ⟨a,ha⟩ ⟨b,hb⟩ ⟨a+b,hc⟩ rfl)).symm).trans
      (f.map_add _ _))

end GaloisForLFunctions.HTGeometry.Quantum.ChargeGaps

#print axioms GaloisForLFunctions.HTGeometry.Quantum.ChargeGaps.triangle
#print axioms GaloisForLFunctions.HTGeometry.Quantum.ChargeGaps.hom_ext
#print axioms GaloisForLFunctions.HTGeometry.Quantum.ChargeGaps.extends_iff
#print axioms GaloisForLFunctions.HTGeometry.Quantum.ChargeGaps.charge_gen
#print axioms GaloisForLFunctions.HTGeometry.Quantum.ChargeGaps.fullEquiv
#print axioms GaloisForLFunctions.HTGeometry.Quantum.ChargeGaps.observation_fiber
