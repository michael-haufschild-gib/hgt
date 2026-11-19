import GaloisForLFunctions.HTGeometry.Lattices.IntegralCartanComponents
import GaloisForLFunctions.HTGeometry.Lattices.IntegralCartanForest
import GaloisForLFunctions.HTGeometry.Lattices.RootedCartanArms
import GaloisForLFunctions.HTGeometry.Lattices.ClassicalCartanCoordinates
import GaloisForLFunctions.HTGeometry.Lattices.TrivalentCartanEnergy
import Mathlib.Data.Fin.Tuple.Sort

/-!
# Large components of an integral norm-one shell

Every connected component is a path or has a single branching center.
Testing the integral form on a linear ramp along each arm restricts its
three lengths to the finite Cartan triples. Beyond eight vertices only a
path or a fork with two one-vertex arms remains.
-/

noncomputable section
open Finset
namespace GaloisForLFunctions.HTGeometry.IntegralRootShell
open CartanPath ClassicalCartan
local notation "consℤ" => Fin.cons (α := fun _ => ℤ)
variable {J : Type*} [Fintype J] (Q : Form J) (hQ : Q.PosDef)

noncomputable local instance : Fintype (Component Q hQ) := Fintype.ofFinite _
noncomputable local instance (c : Component Q hQ) : Fintype (Part Q hQ c) := Fintype.ofFinite _
noncomputable local instance (c : Component Q hQ) : Fintype ↥c :=
  inferInstanceAs (Fintype (Part Q hQ c))
noncomputable local instance (c : Component Q hQ) : DecidableRel c.toSimpleGraph.Adj := Classical.decRel _

private theorem part_degree (c : Component Q hQ) (i : Part Q hQ c) :
    c.toSimpleGraph.degree i=(neighbors Q hQ i.val).card := by
  classical
  let e : c.toSimpleGraph.neighborSet i ≃ (neighbors Q hQ i.val) :=
    { toFun := fun j => ⟨j.val.val,(mem_neighbors Q hQ _ _).mpr j.property⟩
      invFun := fun j =>
        let edge := (mem_neighbors Q hQ _ _).mp j.property
        ⟨⟨j.val,(SimpleGraph.ConnectedComponent.sound edge.reachable).symm.trans i.property⟩,edge⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  simpa only [SimpleGraph.card_neighborSet_eq_degree,Fintype.card_coe] using Fintype.card_congr e

private theorem component_tree (c : Component Q hQ) : c.toSimpleGraph.IsTree :=
  ⟨c.connected_toSimpleGraph,(cartan_acyclic Q hQ).induce c.supp⟩

private theorem part_leaf (c : Component Q hQ) : ∃ i : Part Q hQ c, c.toSimpleGraph.degree i≤1 := by
  letI : Nonempty ↥c := c.connected_toSimpleGraph.nonempty
  let f := (SimpleGraph.Embedding.induce (G:=cartanGraph Q hQ) c.supp).toCopy
  obtain ⟨i,small,_⟩ := copy_leaf Q hQ c.toSimpleGraph f
  exact ⟨i,small⟩

/-- Path coordinates preserve the full form before taking its unit shell. -/
private theorem path_form (c : Component Q hQ) {n : ℕ} (e : Fin n ≃ Part Q hQ c)
    (edges : ∀ i j,c.toSimpleGraph.Adj (e i) (e j) ↔ i.val+1=j.val ∨ j.val+1=i.val)
    (a : Fin n → ℤ) : componentForm Q hQ c (fun v => a (e.symm v))=pathEnergy a := by
  rw [← path_parent_energy]
  apply component_parent_energy Q hQ c e previous
  · intro i j
    change c.toSimpleGraph.Adj (e i) (e j) ↔ _
    rw [edges,previous_eq,previous_eq,or_comm]
  · intro i j h h'
    have u := (previous_eq i j).mp h
    have v := (previous_eq j i).mp h'
    omega

private theorem path_count (c : Component Q hQ) (degrees : ∀ i : Part Q hQ c,c.toSimpleGraph.degree i≤2) :
    Nat.card (Root (componentForm Q hQ c))=Nat.card (Part Q hQ c)*(Nat.card (Part Q hQ c)+1) := by
  obtain ⟨i,leaf⟩ := part_leaf Q hQ c
  obtain ⟨n,e,_,edges⟩ := rooted_numbering _ i c.connected_toSimpleGraph.preconnected leaf degrees
  let E : {a : Fin (n+1) → ℤ // pathEnergy a=1} ≃ Root (componentForm Q hQ c) :=
    { toFun := fun a => ⟨fun j => a.val (e.symm j),(path_form Q hQ c e edges a.val).trans a.property⟩
      invFun := fun x => ⟨fun i => x.val (e i),by
        rw [←path_form Q hQ c e edges]
        simpa only [e.apply_symm_apply] using x.property⟩
      left_inv := fun _ => Subtype.ext (funext fun _ => by simp only [e.symm_apply_apply])
      right_inv := fun _ => Subtype.ext (funext fun _ => by simp only [e.apply_symm_apply]) }
  have card : Nat.card (Part Q hQ c)=n+1 := (Nat.card_congr e).symm.trans (Nat.card_fin _)
  rw [←Nat.card_congr E,path_root_count,card,Nat.mul_comm]

private def radialField {T : Type*} {d : T → ℕ} (t : ℤ) (f : ∀ j,Fin (d j+1) → ℤ) : Radial T d → ℤ
  | none => t
  | some ⟨j,i⟩ => f j i

private theorem radial_edge_term {T : Type*} {d : T → ℕ} (t : ℤ) (f : ∀ j,Fin (d j+1) → ℤ)
    (j : T) (i : Fin (d j+1)) :
    (radialParent (some ⟨j,i⟩ : Radial T d)).elim 0
      (fun y => f j i*radialField t f y)=f j i*consℤ t (f j) i.castSucc := by
  by_cases z : i.val=0
  · have he : i.castSucc=0 := Fin.ext z
    simp [radialParent,z,radialField,he]
  · let k : Fin (d j+1) := ⟨i.val-1,by omega⟩
    have he : i.castSucc=k.succ := Fin.ext (by dsimp [k]; omega)
    simp only [radialParent,dif_neg z,radialField,Option.elim,he,Fin.cons_succ]
    rfl

private theorem radial_form {T : Type*} [Fintype T] {d : T → ℕ} (c : Component Q hQ)
    (e : Radial T d ≃ Part Q hQ c)
    (edges : ∀ x y, c.toSimpleGraph.Adj (e x) (e y) ↔ radialParent x=some y ∨ radialParent y=some x)
    (t : ℤ) (f : ∀ j,Fin (d j+1) → ℤ) :
    componentForm Q hQ c (fun v => radialField t f (e.symm v))=t^2+∑ j,armPiece t (f j) := by
  rw [component_parent_energy Q hQ c e radialParent edges radial_asymm]
  let a := radialField t f
  have L : (∑ x : Radial T d,(a x)^2)=t^2+∑ j,∑ i,(f j i)^2 := by
    rw [Fintype.sum_option,Fintype.sum_sigma]
    rfl
  have R : (∑ x : Radial T d,(radialParent x).elim 0 (fun y => a x*a y))=
      ∑ j,∑ i,f j i*consℤ t (f j) i.castSucc := by
    rw [Fintype.sum_option,Fintype.sum_sigma]
    change 0+_=_
    rw [zero_add]
    exact sum_congr rfl fun j _ => sum_congr rfl fun i _ => radial_edge_term t f j i
  rw [L,R]
  simp only [armPiece,sum_sub_distrib]
  ring

/-- A single integral test vector detects the sign of the trivalent
Schur complement. The center is the product of the three denominators. -/
private theorem radial_center {T : Type*} [Fintype T] {d : T → ℕ} (c : Component Q hQ)
    (e : Radial T d ≃ Part Q hQ c)
    (edges : ∀ x y, c.toSimpleGraph.Adj (e x) (e y) ↔ radialParent x=some y ∨ radialParent y=some x)
    (g : Fin 3 ≃ T) : 0<TrivalentCartan.center (d (g 0)+1) (d (g 1)+1) (d (g 2)+1) := by
  let N (j : T) := ((d j:ℤ)+2)
  let t := N (g 0)*N (g 1)*N (g 2)
  let slope (j : T) := ![N (g 1)*N (g 2),N (g 0)*N (g 2),N (g 0)*N (g 1)] (g.symm j)
  have ht : 0<t := by dsimp [t,N]; positivity
  have link (j : T) : ((d j+1:ℕ)+1:ℤ)*slope j=t := by
    obtain ⟨i,rfl⟩ := g.surjective j
    fin_cases i <;> simp [slope,t,N] <;> ring
  let f (j : T) (i : Fin (d j+1)) := t-((i.val:ℤ)+1)*slope j
  have arm (j : T) : 2*armPiece t (f j)=t*slope j-t^2 := by
    have h := ramp_piece (n:=d j+1) (slope j)
    dsimp only at h
    rw [link j] at h
    calc
      _ = (((d j+1:ℕ):ℤ)+1)*(slope j)^2-t^2 := h
      _ = _ := by rw [←link j]; ring
  have nz : (fun v => radialField t f (e.symm v))≠0 := by
    intro h
    have h0 := congrFun h (e none)
    exact ht.ne' (by simpa only [e.symm_apply_apply,radialField,Pi.zero_apply] using h0)
  have pos := componentForm_posDef Q hQ c _ nz
  rw [radial_form Q hQ c e edges] at pos
  have gc : Fintype.card T=3 := (Fintype.card_congr g).symm.trans (Fintype.card_fin 3)
  have twice : 2*(t^2+∑ j,armPiece t (f j))=t*((∑ j,slope j)-t) := by
    rw [mul_add,mul_sum]
    simp_rw [arm]
    rw [sum_sub_distrib,← mul_sum,sum_const,card_univ,gc]
    ring
  have sumPos := (mul_pos_iff_of_pos_left ht).mp (twice ▸ (mul_pos (by norm_num : (0:ℤ)<2) pos))
  rw [← g.sum_comp slope,Fin.sum_univ_three] at sumPos
  simp only [slope,g.symm_apply_apply,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two] at sumPos
  let b := N (g 1)*N (g 2)+N (g 0)*N (g 2)+N (g 0)*N (g 1)-t
  have bp : (0:ℝ)<(b:ℝ) := by exact_mod_cast sumPos
  have tr : (0:ℝ)<(t:ℝ) := by exact_mod_cast ht
  apply (div_pos bp tr).trans_eq
  change (b:ℝ)/(t:ℝ)=1/(((d (g 0)+1:ℕ):ℝ)+1)+1/(((d (g 1)+1:ℕ):ℝ)+1)+1/(((d (g 2)+1:ℕ):ℝ)+1)-1
  dsimp [b,t,N]
  push_cast
  field_simp
  ring

private theorem radial_card {T : Type*} [Fintype T] {d : T → ℕ} (c : Component Q hQ)
    (e : Radial T d ≃ Part Q hQ c) (g : Fin 3 ≃ T) :
    Nat.card (Part Q hQ c)=(d (g 0)+1)+(d (g 1)+1)+(d (g 2)+1)+1 := by
  rw [← Nat.card_congr e,Nat.card_eq_fintype_card]
  change Fintype.card (Option (Σ j, Fin (d j+1)))=_
  rw [Fintype.card_option,Fintype.card_sigma]
  simp only [Fintype.card_fin]
  rw [←g.sum_comp (fun j => d j+1),Fin.sum_univ_three]

private theorem single_arm {m : ℕ} (one : m=0) (t : ℤ) (f : Fin (m+1) → ℤ) :
    armPiece t f=(f 0)^2-f 0*t := by
  subst m
  simp [armPiece]

private theorem fork_count {T : Type*} [Fintype T] {d : T → ℕ} (c : Component Q hQ)
    (e : Radial T d ≃ Part Q hQ c)
    (edges : ∀ x y, c.toSimpleGraph.Adj (e x) (e y) ↔ radialParent x=some y ∨ radialParent y=some x)
    (g : Fin 3 ≃ T) (short₀ : d (g 0)=0) (short₁ : d (g 1)=0) :
    Nat.card (Root (componentForm Q hQ c))≤
      2*Nat.card (Part Q hQ c)*(Nat.card (Part Q hQ c)-1) := by
  classical
  let R := Root (componentForm Q hQ c)
  let t (x : R) := x.val (e none)
  let a (x : R) (j : T) (i : Fin (d j+1)) := x.val (e (some ⟨j,i⟩))
  let trunk (x : R) := consℤ (t x) (a x (g 2))
  let encode (x : R) : Fork (d (g 2)+2) :=
    (fun i => trunk x i.rev,a x (g 0) 0,a x (g 1) 0)
  have coordinates (x : R) : (fun v => radialField (t x) (a x) (e.symm v))=x.val := by
    funext v
    obtain ⟨w,rfl⟩ := e.surjective v
    rw [e.symm_apply_apply]
    rcases w with _|⟨j,i⟩ <;> rfl
  have unit (x : R) : forkEnergy (encode x)=1 := by
    have energy := radial_form Q hQ c e edges (t x) (a x)
    rw [coordinates,x.property,←g.sum_comp (fun j => armPiece (t x) (a x j)),Fin.sum_univ_three,
      single_arm short₀,single_arm short₁] at energy
    change forkEnergy (fun i => trunk x i.rev,a x (g 0) 0,a x (g 1) 0)=1
    rw [fork_head_energy,path_cons_arm]
    change (t x)^2+armPiece (t x) (a x (g 2))+(a x (g 0) 0)^2+(a x (g 1) 0)^2-
      t x*(a x (g 0) 0+a x (g 1) 0)=1
    linarith only [energy]
  let f (x : R) : {b : Fork (d (g 2)+2) // forkEnergy b=1} := ⟨encode x,unit x⟩
  have inj : Function.Injective f := by
    intro x y h
    have he : encode x=encode y := congrArg Subtype.val h
    have eqT (i) : trunk x i=trunk y i := by
      simpa only [encode,Fin.rev_rev] using congrArg (fun z : Fork (d (g 2)+2) => z.1 i.rev) he
    have eqU : a x (g 0) 0=a y (g 0) 0 := congrArg (fun z : Fork (d (g 2)+2) => z.2.1) he
    have eqV : a x (g 1) 0=a y (g 1) 0 := congrArg (fun z : Fork (d (g 2)+2) => z.2.2) he
    apply Subtype.ext
    funext v
    obtain ⟨w,rfl⟩ := e.surjective v
    rcases w with _|⟨j,i⟩
    · simpa only [trunk,Fin.cons_zero,t] using eqT 0
    · obtain ⟨z,rfl⟩ := g.surjective j
      fin_cases z
      · change Fin (d (g 0)+1) at i
        have hi := i.isLt
        have eq : i=0 := Fin.ext (show i.val=0 by omega)
        subst i
        exact eqU
      · change Fin (d (g 1)+1) at i
        have hi := i.isLt
        have eq : i=0 := Fin.ext (show i.val=0 by omega)
        subst i
        exact eqV
      · change Fin (d (g 2)+1) at i
        exact (Fin.cons_succ (α := fun _ => ℤ) (t x) (a x (g 2)) i).symm.trans
          ((eqT i.succ).trans (Fin.cons_succ (α := fun _ => ℤ) (t y) (a y (g 2)) i))
  let F := (forkRootEquiv (d (g 2)+2)) ∘ f
  have le := Nat.card_le_card_of_injective F ((forkRootEquiv _).injective.comp inj)
  rw [IntegralZeroSum.card_twoShell,Fintype.card_fin] at le
  let s := Nat.card (Part Q hQ c)
  have card : s=d (g 2)+2+2 := by
    have h := radial_card Q hQ c e g
    rw [short₀,short₁] at h
    dsimp [s]
    omega
  rw [←card] at le
  have count : (s-1)*s=2*s.choose 2 := by
    simpa [Nat.descFactorial] using Nat.descFactorial_eq_factorial_mul_choose s 2
  apply le.trans
  change 4*s.choose 2≤2*s*(s-1)
  rw [show 4*s.choose 2=2*(2*s.choose 2) by ring,←count]
  exact Nat.le_of_eq (by ring)

/-- A component of rank at least nine contains at most as many signed unit
vectors as a D lattice of that rank. -/
theorem large_component_bound (c : Component Q hQ) (large : 9≤Nat.card (Part Q hQ c)) :
    Nat.card (Root (componentForm Q hQ c))≤
      2*Nat.card (Part Q hQ c)*(Nat.card (Part Q hQ c)-1) := by
  classical
  let H := c.toSimpleGraph
  by_cases path : ∀ i : Part Q hQ c,H.degree i≤2
  · rw [path_count Q hQ c path]
    let s := Nat.card (Part Q hQ c)
    change s*(s+1)≤2*s*(s-1)
    calc
      _ ≤ s*(2*(s-1)) := Nat.mul_le_mul_left _ (by dsimp [s]; omega)
      _ = _ := by ring
  · push Not at path
    obtain ⟨r,branch⟩ := path
    have three : H.degree r=3 := by
      have le := degree_le_three Q hQ r.val
      change c.toSimpleGraph.degree r=3
      change 2 < c.toSimpleGraph.degree r at branch
      rw [part_degree Q hQ c r] at branch ⊢
      omega
    have away (v : Part Q hQ c) (ne : v≠r) : H.degree v≤2 := by
      by_contra! high
      apply ne
      apply Subtype.ext
      apply trivalent_unique_in_component Q hQ v.val r.val
      · exact SimpleGraph.ConnectedComponent.eq.mp (v.property.trans r.property.symm)
      · rw [← part_degree Q hQ c v]
        exact high
      · rw [← part_degree Q hQ c r]
        exact three.ge
    choose d e start edges using arm_numbering H r away
    let E := radialEquiv H r (component_tree Q hQ c) d e
    have edge := radial_edges H r (component_tree Q hQ c) d e start edges
    let g₀ : Fin 3 ≃ H.neighborSet r := (Fintype.equivFinOfCardEq
      ((SimpleGraph.card_neighborSet_eq_degree H r).trans three)).symm
    let g := (Tuple.sort (fun i => d (g₀ i))).trans g₀
    have sorted : Monotone (fun i => d (g i)) := Tuple.monotone_sort (fun i => d (g₀ i))
    have center := radial_center Q hQ c E edge g
    have shape := (TrivalentCartan.ordered_finite_shape (d (g 0)+1) (d (g 1)+1) (d (g 2)+1)
      (Nat.succ_pos _) (Nat.succ_le_succ (sorted (by decide : (0:Fin 3)≤1)))
      (Nat.succ_le_succ (sorted (by decide : (1:Fin 3)≤2)))).mp
        ((TrivalentCartan.integer_positive_iff _ _ _).mpr ((TrivalentCartan.positive_iff _ _ _).mpr center))
    have card := radial_card Q hQ c E g
    exact fork_count Q hQ c E edge g (by omega) (by omega)


private theorem small_component_count (c : Component Q hQ) (hs : Nat.card (Part Q hQ c)≤8) :
    Nat.card (Root (componentForm Q hQ c))≤30*Nat.card (Part Q hQ c) := by
  let s := Nat.card (Part Q hQ c)
  have root : Nat.card (Root (componentForm Q hQ c)) ≤ 2*(s+2).choose 3 := by
    simpa only [s,Nat.card_eq_fintype_card] using
      root_card_le (componentForm Q hQ c) (componentForm_posDef Q hQ c)
  have six : 6*(s+2).choose 3=s*((s+1)*(s+2)) := by
    have e := Nat.descFactorial_eq_factorial_mul_choose (s+2) 3
    norm_num [Nat.descFactorial] at e
    simpa only [show s+2-2=s by omega,show s+2-1=s+1 by omega,Nat.mul_assoc] using e.symm
  have p : (s+1)*(s+2)≤9*10 := Nat.mul_le_mul (by omega) (by omega)
  have le := Nat.mul_le_mul_left s p
  rw [← six] at le
  omega

/-- Combining a linear small-component estimate with quadratic growth in
large components pays only for the sum of their simple ranks. -/
private theorem aggregate_components
    (large : ∀ c : Component Q hQ, 9≤Nat.card (Part Q hQ c) →
      Nat.card (Root (componentForm Q hQ c))≤2*Nat.card (Part Q hQ c)*(Nat.card (Part Q hQ c)-1)) :
    Nat.card (Root Q)≤2*max 15 (Fintype.card J-1)*Fintype.card J := by
  classical
  let W := 2*max 15 (Fintype.card J-1)
  have total : (∑ c : Component Q hQ, Nat.card (Part Q hQ c))≤Fintype.card J :=
    (sum_component_ranks Q hQ).le.trans (simple_card_le Q hQ)
  have localBound (c : Component Q hQ) :
      Nat.card (Root (componentForm Q hQ c))≤W*Nat.card (Part Q hQ c) := by
    let s := Nat.card (Part Q hQ c)
    have sd : s≤Fintype.card J := (single_le_sum (f:=fun t : Component Q hQ => Nat.card (Part Q hQ t))
      (fun _ _ => Nat.zero_le _) (mem_univ c)).trans total
    by_cases h : s≤8
    · apply (small_component_count Q hQ c h).trans
      exact Nat.mul_le_mul_right _ (Nat.mul_le_mul_left 2 (le_max_left 15 (Fintype.card J-1)))
    · apply (large c (by omega)).trans
      rw [Nat.mul_right_comm]
      exact Nat.mul_le_mul_right _ (Nat.mul_le_mul_left 2 ((Nat.sub_le_sub_right sd 1).trans (le_max_right _ _)))
  rw [component_root_count Q hQ]
  exact (sum_le_sum fun c _ => localBound c).trans (by rw [← mul_sum]; exact Nat.mul_le_mul_left W total)

include hQ

/-- The signed shell of every integral positive quadratic form in rank d
has at most 2d max(15,d−1) points, including nonclassical forms. -/
theorem quadratic_root_bound : Nat.card (Root Q)≤2*max 15 (Fintype.card J-1)*Fintype.card J :=
  aggregate_components Q hQ (large_component_bound Q hQ)

/-- The uniform 480-versus-quadratic bound for the complete signed shell. -/
theorem uniform_quadratic_root_bound :
    Nat.card (Root Q) ≤ max 480 (2*Fintype.card J*(Fintype.card J-1)) := by
  let d := Fintype.card J
  have h := quadratic_root_bound Q hQ
  change Nat.card (Root Q)≤2*max 15 (d-1)*d at h
  rcases le_total (d-1) 15 with small|large
  · rw [max_eq_left small] at h
    exact (h.trans (by omega : 2*15*d≤480)).trans (le_max_left _ _)
  · rw [max_eq_right large,Nat.mul_right_comm] at h
    exact h.trans (le_max_right _ _)

/-- A set of different root lines costs at most d max(15,d−1) unoriented
directions. Parity fibers account exactly for the factor of two. -/
theorem quadratic_line_bound {I : Type*} [Fintype I] (x : I → Root Q)
    (separate : ∀ i j, (x i).val=(x j).val ∨ (x i).val= -(x j).val → i=j) :
    Fintype.card I≤Fintype.card J*max 15 (Fintype.card J-1) := by
  let f (i : I) : Occupied Q := ⟨parity (x i).val,x i,rfl⟩
  have inj : Function.Injective f := fun i j h =>
    separate i j ((root_parity_iff Q hQ _ _).mp (congrArg Subtype.val h))
  have embeds := Nat.card_le_card_of_injective f inj
  rw [Nat.card_eq_fintype_card (α:=I)] at embeds
  have h := quadratic_root_bound Q hQ
  rw [card_roots Q hQ,Nat.mul_assoc,Nat.mul_comm (max 15 (Fintype.card J-1))] at h
  omega

#print axioms large_component_bound
#print axioms quadratic_root_bound
#print axioms uniform_quadratic_root_bound
#print axioms quadratic_line_bound
end GaloisForLFunctions.HTGeometry.IntegralRootShell
