import GaloisForLFunctions.HTGeometry.Polynomial.SignedGridInterpolation

/-!
# The exact degree missed by a signed injective grid

The generating polynomial of the squared alphabet is the product of
`1+s²Z`. Removing the n occupied factors leaves degree |S|−n.
Its first missing coefficient gives a nonzero polynomial invisible on
every signed injective tuple. Removing the factors commutes, so this
witness depends only on the multiset of squared coordinates. The
coordinate-slice bound proves minimality.
-/

noncomputable section
open Finset MvPolynomial
namespace GaloisForLFunctions.HTGeometry.SignedGrid

/-- Remove a linear factor from a sequence of coefficients, starting at the
constant term. The first k resulting coefficients use only input indices ≤ k. -/
private def cut {R : Type*} [CommRing R] (a : R) (c : ℕ → R) : ℕ → R
  | 0 => c 0
  | k+1 => c (k+1)-a*cut a c k

private def removeFactors {R : Type*} [CommRing R] (c : ℕ → R) : List R → ℕ → R
  | [] => c
  | a::xs => removeFactors (cut a c) xs

/- Multiplication by 1+aZ is invertible on coefficient sequences. Its
inverse commutes with removal of any other linear factor. -/
private def put {R : Type*} [CommRing R] (a : R) (c : ℕ → R) : ℕ → R
  | 0 => c 0
  | k+1 => c (k+1)+a*c k

private theorem put_cut {R : Type*} [CommRing R] (a : R) (c : ℕ → R) : put a (cut a c)=c := by
  funext k
  cases k with
  | zero => rfl
  | succ k => exact sub_add_cancel _ _

private theorem cut_put {R : Type*} [CommRing R] (a : R) (c : ℕ → R) : cut a (put a c)=c := by
  funext k
  induction k with
  | zero => rfl
  | succ k ih => simp only [cut,put,ih,add_sub_cancel_right]

private theorem put_comm {R : Type*} [CommRing R] (a b : R) (c : ℕ → R) : put a (put b c)=put b (put a c) := by
  funext k
  cases k with
  | zero => rfl
  | succ k => cases k <;> simp only [put] <;> ring

private theorem cut_comm {R : Type*} [CommRing R] (a b : R) (c : ℕ → R) : cut a (cut b c)=cut b (cut a c) := by
  have inj (t : R) : Function.Injective (put t) := Function.LeftInverse.injective (cut_put t)
  apply inj a
  apply inj b
  rw [put_cut,put_cut,put_comm b a,put_cut,put_cut]

private theorem remove_perm {R : Type*} [CommRing R] {xs ys : List R} (perm : xs.Perm ys) :
    ∀ c, removeFactors c xs=removeFactors c ys := by
  induction perm with
  | nil => intro c; rfl
  | cons a _ ih => exact fun c => ih (cut a c)
  | swap a b xs => intro c; simp only [removeFactors,cut_comm a b]
  | trans _ _ ih jh => exact fun c => (ih c).trans (jh c)

private def elementary (S : Finset ℝ) (k : ℕ) :=
  (∏ a∈S, (1+Polynomial.C (a^2)*Polynomial.X : Polynomial ℝ)).coeff k

private theorem insert_coeff (S : Finset ℝ) (a : ℝ) (ha : a∉S) (k : ℕ) :
    elementary (insert a S) (k+1)=elementary S (k+1)+a^2*elementary S k := by
  simp only [elementary,prod_insert ha,add_mul,one_mul,mul_assoc,Polynomial.coeff_add,
    Polynomial.coeff_C_mul,Polynomial.coeff_X_mul]

private theorem insert_const (S : Finset ℝ) (a : ℝ) (ha : a∉S) :
    elementary (insert a S) 0=elementary S 0 := by
  simp [elementary,prod_insert ha,add_mul,mul_assoc]

private theorem coefficient_range (S : Finset ℝ) (positive : ∀ s∈S, 0<s) (k : ℕ) :
    (k≤S.card → 0<elementary S k) ∧ (S.card<k → elementary S k=0) := by
  classical
  induction S using Finset.induction_on generalizing k with
  | empty =>
    cases k <;> simp [elementary,Polynomial.coeff_one]
  | @insert a S fresh ih =>
    have pos (s : ℝ) (hs : s∈S) := positive s (mem_insert_of_mem hs)
    have pa := positive a (mem_insert_self _ _)
    rw [card_insert_of_notMem fresh]
    cases k with
    | zero =>
      rw [insert_const S a fresh]
      exact ⟨fun _ => (ih pos 0).1 (Nat.zero_le _),fun h => (by omega : False).elim⟩
    | succ k =>
      rw [insert_coeff S a fresh]
      constructor
      · intro le
        have low := (ih pos k).1 (by omega)
        have high : 0≤elementary S (k+1) := by
          by_cases h : k+1≤S.card
          · exact ((ih pos (k+1)).1 h).le
          · rw [(ih pos (k+1)).2 (lt_of_not_ge h)]
        exact add_pos_of_nonneg_of_pos high (mul_pos (sq_pos_of_pos pa) low)
      · intro gt
        rw [(ih pos (k+1)).2 (by omega),(ih pos k).2 (by omega),mul_zero,add_zero]

private theorem cut_exact (S : Finset ℝ) (a : ℝ) (ha : a∈S) :
    cut (a^2) (elementary S)=elementary (S.erase a) := by
  funext k
  induction k with
  | zero =>
    change elementary S 0=_
    simpa only [insert_erase ha] using insert_const (S.erase a) a (by simp)
  | succ k ih =>
    rw [cut,ih]
    have he := insert_coeff (S.erase a) a (by simp) k
    rw [insert_erase ha] at he
    rw [he,add_sub_cancel_right]

private theorem remove_exact (S : Finset ℝ) (xs : List ℝ) (nodup : xs.Nodup) (mem : ∀ a∈xs, a∈S) :
    removeFactors (elementary S) (xs.map (·^2))=elementary (S \ xs.toFinset) := by
  classical
  induction xs generalizing S with
  | nil => simp [removeFactors]
  | cons a xs ih =>
    obtain ⟨fresh,nd⟩ := List.nodup_cons.mp nodup
    have ha := mem a List.mem_cons_self
    have away (b : ℝ) (hb : b∈xs) : b∈S.erase a := mem_erase.mpr
      ⟨fun eq => fresh (eq ▸ hb),mem b (List.mem_cons_of_mem _ hb)⟩
    rw [List.map_cons,removeFactors,cut_exact S a ha,ih _ nd away]
    congr 1
    ext b
    simp only [mem_sdiff,mem_erase,List.toFinset_cons,mem_insert]
    tauto

private theorem map_cut {R A : Type*} [CommRing R] [CommRing A] (φ : R →+* A) (a : R) (c : ℕ → R) (k : ℕ) :
    φ (cut a c k)=cut (φ a) (fun k => φ (c k)) k := by
  induction k with
  | zero => rfl
  | succ k ih => simp only [cut,map_sub,map_mul,ih]

private theorem map_removal {R A : Type*} [CommRing R] [CommRing A] (φ : R →+* A)
    (xs : List R) (c : ℕ → R) (k : ℕ) :
    φ (removeFactors c xs k)=removeFactors (fun k => φ (c k)) (xs.map φ) k := by
  induction xs generalizing c with
  | nil => rfl
  | cons a xs ih =>
    simp only [List.map_cons,removeFactors,ih,map_cut]

private theorem cut_degree {n : ℕ} (a : MvPolynomial (Fin n) ℝ) (ha : a.totalDegree≤2)
    (c : ℕ → MvPolynomial (Fin n) ℝ) (hc : ∀ k,(c k).totalDegree≤2*k) (k : ℕ) :
    (cut a c k).totalDegree≤2*k := by
  induction k with
  | zero => exact hc 0
  | succ k ih =>
    apply (totalDegree_sub _ _).trans (max_le (hc _) ?_)
    have h := (totalDegree_mul a (cut a c k)).trans (Nat.add_le_add ha ih)
    omega

private theorem remove_degree {n : ℕ} (xs : List (MvPolynomial (Fin n) ℝ))
    (hx : ∀ a∈xs,a.totalDegree≤2) (c : ℕ → MvPolynomial (Fin n) ℝ) (hc : ∀ k,(c k).totalDegree≤2*k) (k : ℕ) :
    (removeFactors c xs k).totalDegree≤2*k := by
  induction xs generalizing c with
  | nil => exact hc k
  | cons a xs ih =>
    exact ih (fun b hb => hx b (List.mem_cons_of_mem _ hb)) _ (cut_degree a (hx _ List.mem_cons_self) c hc)

private def gridRelation (S : Finset ℝ) (n k : ℕ) : MvPolynomial (Fin n) ℝ :=
  removeFactors (fun j => C (elementary S j)) (List.ofFn fun i : Fin n => (X i)^2) k

private theorem gridRelation_degree (S : Finset ℝ) (n k : ℕ) : (gridRelation S n k).totalDegree≤2*k := by
  apply remove_degree
  · intro a ha
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp ha
    exact (totalDegree_pow _ _).trans (by simp)
  · intro j
    rw [totalDegree_C]
    omega

private theorem relation_eval (S : Finset ℝ) {n k : ℕ} (x : Fin n → ℝ) :
    eval x (gridRelation S n k)=removeFactors (elementary S) (List.ofFn fun i => (x i)^2) k := by
  simp only [gridRelation,map_removal,eval_C,List.map_ofFn,Function.comp_def,map_pow,eval_X]

private theorem relation_at_origin (S : Finset ℝ) (n k : ℕ) :
    eval (fun _ => 0) (gridRelation S n k)=elementary S k := by
  have cut0 (c : ℕ → ℝ) : cut 0 c=c := by funext j; cases j <;> simp [cut]
  have h (xs : List ℝ) (hz : ∀ x∈xs,x=0) (c : ℕ → ℝ) : removeFactors c xs=c := by
    induction xs generalizing c with
    | nil => rfl
    | cons a xs ih =>
      rw [removeFactors,hz a List.mem_cons_self,cut0,ih _ _]
      exact fun b hb => hz b (List.mem_cons_of_mem _ hb)
  rw [relation_eval,h _ (by intro a ha; obtain ⟨i,rfl⟩ := List.mem_ofFn.mp ha; norm_num)]

/-- Vanishing at all signed distinct tuples of a finite positive alphabet. -/
def invisible {n : ℕ} (S : Finset ℝ) (p : MvPolynomial (Fin n) ℝ) :=
  ∀ x : Fin n → ℝ, (∀ i, |x i|∈S) → Function.Injective (fun i => |x i|) → eval x p=0

/-- The polynomial depends only on the unordered squared coordinates. -/
def signedInvariant {n : ℕ} (p : MvPolynomial (Fin n) ℝ) :=
  ∀ x y : Fin n → ℝ, (List.ofFn fun i => (x i)^2).Perm (List.ofFn fun i => (y i)^2) → eval x p=eval y p

private theorem relation_invariant (S : Finset ℝ) (n k : ℕ) : signedInvariant (gridRelation S n k) := by
  intro x y h
  rw [relation_eval,relation_eval,remove_perm h (elementary S)]

private theorem missing_coefficient (S : Finset ℝ) (positive : ∀ s∈S,0<s) (n : ℕ) (fit : n+1≤S.card) :
    invisible S (gridRelation S (n+1) (S.card-n)) := by
  intro x hx inj
  let xs := List.ofFn fun i => |x i|
  have nd : xs.Nodup := List.nodup_ofFn_ofInjective inj
  have mem (s : ℝ) (hs : s∈xs) : s∈S := by
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hs
    exact hx i
  have eq : List.ofFn (fun i => (x i)^2)=xs.map (·^2) := by simp only [xs,List.map_ofFn,Function.comp_def,sq_abs]
  rw [relation_eval,eq,remove_exact S xs nd mem]
  have cs : (S \ xs.toFinset).card=S.card-(n+1) := by
    rw [card_sdiff_of_subset (fun s hs => mem s (List.mem_toFinset.mp hs)),List.toFinset_card_of_nodup nd]
    simp only [xs,List.length_ofFn]
  exact (coefficient_range _ (fun s hs => positive s (mem_sdiff.mp hs).1) _).2 (by omega)

private theorem degree_lower (S : Finset ℝ) (positive : ∀ s∈S,0<s) (n : ℕ)
    (p : MvPolynomial (Fin (n+1)) ℝ) (nonzero : p≠0) (van : invisible S p) : 2*(S.card-n)≤p.totalDegree := by
  by_contra! small
  exact nonzero ((interpolation S positive p (fun i => by simp only [Nat.add_sub_cancel]; omega)).mpr van)

private theorem threshold_witness (S : Finset ℝ) (positive : ∀ s∈S,0<s) (n : ℕ) :
    ∃ p : MvPolynomial (Fin (n+1)) ℝ, p≠0 ∧ p.totalDegree=2*(S.card-n) ∧ invisible S p ∧ signedInvariant p := by
  by_cases fit : n+1≤S.card
  · let p := gridRelation S (n+1) (S.card-n)
    have van := missing_coefficient S positive n fit
    have nonzero : p≠0 := by
      intro e
      have he := relation_at_origin S (n+1) (S.card-n)
      change eval _ p=_ at he
      rw [e,map_zero] at he
      exact ((coefficient_range S positive _).1 (Nat.sub_le _ _)).ne' he.symm
    exact ⟨p,nonzero,le_antisymm (gridRelation_degree _ _ _) (degree_lower S positive n p nonzero van),
      van,relation_invariant _ _ _⟩
  · refine ⟨1,one_ne_zero,by rw [totalDegree_one]; omega,?_,fun x y _ => (map_one _).trans (map_one _).symm⟩
    intro x hx hi
    let f (i : Fin (n+1)) : S := ⟨|x i|,hx i⟩
    have le := Fintype.card_le_of_injective f (fun i j e => hi (congrArg Subtype.val e))
    simp only [Fintype.card_fin,Fintype.card_coe] at le
    exact (fit le).elim

/-- In n+1 variables the least total degree invisible on signed distinct
tuples of S is twice (|S|−n), with natural subtraction. If there are too
few nodes, even the constant polynomial is invisible. -/
theorem least_invisible_degree (S : Finset ℝ) (positive : ∀ s∈S,0<s) (n : ℕ) :
    IsLeast {d : ℕ | ∃ p : MvPolynomial (Fin (n+1)) ℝ, p≠0 ∧ p.totalDegree=d ∧ invisible S p}
      (2*(S.card-n)) := by
  obtain ⟨p,h,hd,hv,_⟩ := threshold_witness S positive n
  refine ⟨⟨p,h,hd,hv⟩,?_⟩
  rintro d ⟨q,hq,rfl,van⟩
  exact degree_lower S positive n q hq van

/-- Even for polynomials invariant under every sign change and coordinate
permutation, the exact first invisible degree is the same. -/
theorem least_invariant_invisible_degree (S : Finset ℝ) (positive : ∀ s∈S,0<s) (n : ℕ) :
    IsLeast {d : ℕ | ∃ p : MvPolynomial (Fin (n+1)) ℝ, p≠0 ∧ p.totalDegree=d ∧ invisible S p ∧ signedInvariant p}
      (2*(S.card-n)) := by
  refine ⟨threshold_witness S positive n,?_⟩
  rintro d ⟨p,h,rfl,van,_⟩
  exact degree_lower S positive n p h van

#print axioms least_invisible_degree
#print axioms least_invariant_invisible_degree
end GaloisForLFunctions.HTGeometry.SignedGrid
