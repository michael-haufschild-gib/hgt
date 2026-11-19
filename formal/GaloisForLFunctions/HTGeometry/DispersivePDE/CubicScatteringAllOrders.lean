import GaloisForLFunctions.HTGeometry.DispersivePDE.CubicScatteringBoundary
import GaloisForLFunctions.HTGeometry.DispersivePDE.ReflectionDiscriminant
import GaloisForLFunctions.HTGeometry.Polynomial.SignedGridInterpolation
import Mathlib.Algebra.MvPolynomial.Funext

/-!
# The all-orders cubic Hirota polynomial condition

For every real combination of the five simple cubic dispersions of Shi,
arXiv:2611.22194, Proposition 6.8, the cleared Hirota residual vanishes
on every finite list of momenta. The soft and collision recursions force
the squared signed-permutation discriminant to divide the residual. Its
degree exceeds the available degree starting with four waves.
-/

noncomputable section
open MvPolynomial
namespace GaloisForLFunctions.HTGeometry.DispersivePDE.CubicHierarchy
namespace WaveList
open ReflectionDiscriminant

private def symb {R : Type*} [CommRing R] (f : ℝ →+* R) (w : Weights) (u v : R) :=
  (u^3-v)*(f w.w4*u+f w.w6*(u^3+f 2*v)+f w.w8*u^2*(u^3-f 4*v)+
      f w.w10*u*(u^3-f 4*v)*(u^3+f 2*v)+f w.w12*(u^3-f 4*v)*(u^6+f 28*u^3*v+f 16*v^2))

private theorem map_factors {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S)
    (g : R → R) (h : S → S) (xs : List R) (he : ∀ y, φ (g y) = h (φ y)) :
    φ (factors g xs) = factors h (xs.map φ) := by
  induction xs with
  | nil => simp [factors]
  | cons x xs ih => simp only [factors,map_mul,he,ih,List.map_cons]

private theorem map_pairWeight {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S) (xs : List R) :
    φ (pairWeight xs) = pairWeight (xs.map φ) := by
  induction xs with
  | nil => simp [pairWeight]
  | cons x xs ih =>
    simp only [pairWeight,List.map_cons,map_mul,ih]
    rw [map_factors φ _ (fun y => (φ x-y)^2) _ (fun y => by simp)]

private theorem map_signSum {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S) (xs : List R)
    (F : List R → R) (G : List S → S) (he : ∀ ys, φ (F ys) = G (ys.map φ)) :
    φ (signSum xs F) = signSum (xs.map φ) G := by
  induction xs generalizing F G with
  | nil => exact he []
  | cons x xs ih =>
    simp only [signSum,List.map_cons,map_add]
    exact congrArg₂ (·+·) (ih _ _ fun ys => he (x::ys))
      (ih _ _ fun ys => by simpa only [List.map_cons,map_neg] using he ((-x)::ys))

private theorem map_reduced {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S) (xs : List R)
    (F : R → R → R) (G : S → S → S) (he : ∀ u v, φ (F u v) = G (φ u) (φ v)) :
    φ (reduced F xs) = reduced G (xs.map φ) := by
  apply map_signSum
  intro ys
  simp only [term,cubicSum,map_mul,map_pairWeight,he,map_list_sum,List.map_map,Function.comp_def,map_pow]

/-- The signed residual in n independent polynomial variables. -/
def universal (n : ℕ) (w : Weights) : Poly n := reduced (symb C w) (List.ofFn X)

private theorem specialize {n : ℕ} (w : Weights) (x : Fin n → ℝ) :
    eval x (universal n w) = reduced (dispersion w) (List.ofFn x) := by
  rw [universal,map_reduced (eval x) _ _ (dispersion w) (fun u v => by simp [symb,dispersion,graph])]
  simp [List.ofFn_eq_map,List.map_map,Function.comp_def]

private theorem dadd {n a b : ℕ} {p q : Poly n} (hp : p.totalDegree ≤ a) (hq : q.totalDegree ≤ b) :
    (p+q).totalDegree ≤ max a b := (totalDegree_add _ _).trans (max_le_max hp hq)
private theorem dsub {n a b : ℕ} {p q : Poly n} (hp : p.totalDegree ≤ a) (hq : q.totalDegree ≤ b) :
    (p-q).totalDegree ≤ max a b := (totalDegree_sub _ _).trans (max_le_max hp hq)
private theorem dmul {n a b : ℕ} {p q : Poly n} (hp : p.totalDegree ≤ a) (hq : q.totalDegree ≤ b) :
    (p*q).totalDegree ≤ a+b := (totalDegree_mul _ _).trans (Nat.add_le_add hp hq)
private theorem dpow {n a : ℕ} {p : Poly n} (hp : p.totalDegree ≤ a) (k : ℕ) :
    (p^k).totalDegree ≤ k*a := (totalDegree_pow _ _).trans (Nat.mul_le_mul_left k hp)

private theorem symb_degree {n : ℕ} (w : Weights) {u v : Poly n} (hu : u.totalDegree ≤ 1)
    (hv : v.totalDegree ≤ 3) : (symb C w u v).totalDegree ≤ 12 := by
  have hc (r : ℝ) : (C r : Poly n).totalDegree ≤ 0 := (totalDegree_C _).le
  have g := dsub (dpow hu 3) hv
  have a := dsub (dpow hu 3) (dmul (hc 4) hv)
  have b := dadd (dpow hu 3) (dmul (hc 2) hv)
  have c := dadd (dadd (dpow hu 6) (dmul (dmul (hc 28) (dpow hu 3)) hv)) (dmul (hc 16) (dpow hv 2))
  exact dmul g (dadd (dadd (dadd (dadd (dmul (hc _) hu) (dmul (hc _) b))
    (dmul (dmul (hc _) (dpow hu 2)) a)) (dmul (dmul (dmul (hc _) hu) a) b))
    (dmul (dmul (hc _) a) c))

private theorem sum_degree {n b : ℕ} (xs : List (Poly n)) (hb : ∀ x ∈ xs, x.totalDegree ≤ b) :
    xs.sum.totalDegree ≤ b := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    simpa only [List.sum_cons,max_self] using
      (dadd (hb x List.mem_cons_self) (ih fun y hy => hb _ (List.mem_cons_of_mem _ hy)))

private theorem factors_degree {n b : ℕ} (f : Poly n → Poly n) (xs : List (Poly n))
    (hb : ∀ x ∈ xs, (f x).totalDegree ≤ b) : (factors f xs).totalDegree ≤ b*xs.length := by
  induction xs with
  | nil => simp [factors]
  | cons x xs ih =>
    simpa only [factors,List.length_cons,Nat.mul_succ,Nat.add_comm b] using
      dmul (hb x List.mem_cons_self) (ih fun y hy => hb _ (List.mem_cons_of_mem _ hy))

private def pairDegree : ℕ → ℕ | 0 => 0 | n+1 => 2*n+pairDegree n

private theorem pairDegree_square (n : ℕ) : pairDegree n+n = n^2 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [pairDegree]
    nlinarith only [ih]

private theorem pair_degree {n : ℕ} (xs : List (Poly n)) (hs : ∀ x ∈ xs, x.totalDegree ≤ 1) :
    (pairWeight xs).totalDegree ≤ pairDegree xs.length := by
  induction xs with
  | nil => simp [pairWeight,pairDegree]
  | cons x xs ih =>
    have ht (z) (hz : z ∈ xs) := hs z (List.mem_cons_of_mem x hz)
    exact dmul (factors_degree (fun z => (x-z)^2) xs fun z hz =>
      dpow (dsub (hs x List.mem_cons_self) (ht z hz)) 2) (ih ht)

private theorem sign_degree {n d : ℕ} (xs : List (Poly n)) (F : List (Poly n) → Poly n)
    (hx : ∀ x ∈ xs, x.totalDegree ≤ 1)
    (hF : ∀ ys : List (Poly n), ys.length = xs.length → (∀ x ∈ ys, x.totalDegree ≤ 1) →
      (F ys).totalDegree ≤ d) : (signSum xs F).totalDegree ≤ d := by
  induction xs generalizing F with
  | nil => exact hF [] rfl (by simp)
  | cons x xs ih =>
    have ht (y) (hy : y ∈ xs) := hx y (List.mem_cons_of_mem x hy)
    have hx' := hx x List.mem_cons_self
    have H (y : Poly n) (hy : y.totalDegree ≤ 1) : (signSum xs (fun zs => F (y::zs))).totalDegree ≤ d := by
      apply ih _ ht
      intro zs hl hz
      apply hF _ (by simp only [List.length_cons,hl])
      intro z h
      rcases List.mem_cons.mp h with rfl|h
      · exact hy
      · exact hz _ h
    simpa only [signSum,max_self] using dadd (H x hx') (H (-x) (by simpa using hx'))

private theorem reduced_degree {n d : ℕ} (P : Poly n → Poly n → Poly n)
    (hP : ∀ u v, u.totalDegree ≤ 1 → v.totalDegree ≤ 3 → (P u v).totalDegree ≤ d) :
    (reduced P (List.ofFn X)).totalDegree ≤ d+pairDegree n := by
  apply sign_degree
  · intro x hx
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hx
    exact (totalDegree_X i).le
  · intro ys hl hy
    simp only [List.length_ofFn] at hl
    have hc : (cubicSum ys).totalDegree ≤ 3 := by
      apply sum_degree
      intro z hz
      obtain ⟨x,hx,rfl⟩ := List.mem_map.mp hz
      exact dpow (hy _ hx) 3
    simpa only [term,hl] using dmul (hP _ _ (sum_degree _ hy) hc) (pair_degree ys hy)

/-- The five dispersions have weighted degree at most twelve. -/
private theorem degree_bound (n : ℕ) (w : Weights) :
    (universal n w).totalDegree ≤ 12+pairDegree n :=
  reduced_degree _ fun _ _ => symb_degree w

/-- Pair differences contribute at most n(n−1) degrees and the dispersion
contributes at most twelve. -/
theorem universal_degree (n : ℕ) (w : Weights) :
    (universal n w).totalDegree ≤ 12+n*(n-1) := by
  have he : pairDegree n = n*(n-1) := by
    cases n with
    | zero => rfl
    | succ k =>
      have h := pairDegree_square (k+1)
      simp only [Nat.succ_sub_one]
      nlinarith only [h]
  simpa only [he] using degree_bound n w

private theorem sign_map {ι R : Type*} [CommRing R] (is : List ι) (x y : ι → R)
    (h : ∀ i, x i = y i ∨ x i = -y i) (F : List R → R) :
    signSum (is.map x) F = signSum (is.map y) F := by
  induction is generalizing F with
  | nil => rfl
  | cons i is ih =>
    simp only [List.map_cons,signSum,ih]
    rcases h i with he|he
    · rw [he]
    · rw [he,neg_neg,add_comm]

private theorem extract {α : Type*} {i : α} {xs : List α} (h : i ∈ xs) :
    ∃ ys, xs.Perm (i::ys) := by
  induction xs with
  | nil => simp at h
  | cons a xs ih =>
    rcases List.mem_cons.mp h with rfl|h
    · exact ⟨xs,.refl _⟩
    · obtain ⟨zs,hz⟩ := ih h
      exact ⟨a::zs,(hz.cons a).trans (.swap _ _ _)⟩

private theorem projected_zero {n : ℕ} (P : ℝ → ℝ → ℝ) (v : Wall n) (x : Fin n → ℝ)
    (ih : ∀ ys : List ℝ, ys.length < n → reduced P ys = 0) :
    reduced P (List.ofFn (project v x)) = 0 := by
  let p := project v x
  let is := List.finRange n
  have hm (k : Fin n) : k ∈ is := List.mem_finRange k
  obtain ⟨ys,hy⟩ := extract (hm v.1)
  have hlen : ys.length+1 = n := by simpa only [List.length_cons,List.length_finRange,is] using hy.length_eq.symm
  rw [List.ofFn_eq_map]
  change reduced _ (is.map p) = 0
  rw [reduced_perm _ _ _ (hy.map p),List.map_cons]
  by_cases he : v.1 = v.2
  · have hz : p v.1 = 0 := by simp [p,project,ReflectionDiscriminant.mate,he]
    rw [hz,reduced_zero,ih _ (by simp only [List.length_map]; omega),mul_zero]
  · have hj : v.2 ∈ ys := (List.mem_cons.mp (hy.mem_iff.mp (hm v.2))).resolve_left (Ne.symm he)
    obtain ⟨zs,hz⟩ := extract hj
    have hk : zs.length+1 = ys.length := by simpa only [List.length_cons] using hz.length_eq.symm
    rw [reduced_perm _ _ _ ((hz.map p).cons (p v.1)),List.map_cons]
    have ht : reduced P (zs.map p) = 0 := ih _ (by simp only [List.length_map]; omega)
    by_cases hl : v.1 < v.2
    · have hp : p v.1 = p v.2 := by simp [p,project,ReflectionDiscriminant.mate,he,Ne.symm he,hl]
      rw [hp,reduced_collision,ht,mul_zero]
    · have hp : p v.1 = -p v.2 := by simp [p,project,ReflectionDiscriminant.mate,he,Ne.symm he,hl]
      rw [hp,reduced_opposite,ht,mul_zero]

private theorem reflected_eq {n : ℕ} (P : ℝ → ℝ → ℝ) (v : Wall n) (x : Fin n → ℝ) :
    reduced P (List.ofFn (reflect v x)) = reduced P (List.ofFn x) := by
  let s := Equiv.swap v.1 v.2
  have hs (k : Fin n) : reflect v x k = (x ∘ s) k ∨ reflect v x k = -(x ∘ s) k := by
    by_cases he : v.1 = v.2
    · by_cases hk : k = v.2 <;> simp [s,reflect,he,hk]
    · by_cases hk : k = v.1 <;> by_cases hj : k = v.2 <;> by_cases hl : v.1 < v.2 <;>
        simp_all [s,reflect,ReflectionDiscriminant.mate,Equiv.swap_apply_def]
  calc
    _ = reduced P (List.ofFn (x ∘ s)) := by
      simp only [List.ofFn_eq_map,reduced]
      exact sign_map _ _ _ hs _
    _ = _ := reduced_perm _ _ _ (s.ofFn_comp_perm x)

private theorem eval_cut {n : ℕ} (v : Wall n) (x : Fin n → ℝ) (p : Poly n) :
    eval x (cut v p) = eval (project v x) p := by
  change eval₂Hom (RingHom.id ℝ) x (bind₁ _ p) = _
  rw [eval₂Hom_bind₁]
  apply congrArg (fun v : Fin n → ℝ => eval₂Hom (RingHom.id ℝ) v p)
  funext k
  unfold project ReflectionDiscriminant.mate
  split_ifs <;> simp

private theorem eval_flip {n : ℕ} (v : Wall n) (x : Fin n → ℝ) (p : Poly n) :
    eval x (flip v p) = eval (reflect v x) p := by
  change eval₂Hom (RingHom.id ℝ) x (bind₁ _ p) = _
  rw [eval₂Hom_bind₁]
  apply congrArg (fun v : Fin n → ℝ => eval₂Hom (RingHom.id ℝ) v p)
  funext k
  unfold reflect ReflectionDiscriminant.mate
  split_ifs <;> simp

private theorem residual_walls {n : ℕ} (P : ℝ → ℝ → ℝ) (p : Poly n)
    (he : ∀ x, eval x p = reduced P (List.ofFn x))
    (ih : ∀ ys : List ℝ, ys.length<n → reduced P ys=0) :
    (∀ v, cut v p=0) ∧ (∀ v, ReflectionDiscriminant.flip v p=p) := by
  constructor
  · intro v
    apply MvPolynomial.funext
    intro z
    rw [eval_cut,he,projected_zero P v z ih,map_zero]
  · intro v
    apply MvPolynomial.funext
    intro z
    rw [eval_flip,he,he,reflected_eq]

private theorem vanish_above_degree {n d : ℕ} (P : ℝ → ℝ → ℝ) (p : Poly n)
    (he : ∀ x, eval x p = reduced P (List.ofFn x))
    (hd : p.totalDegree ≤ d+pairDegree n) (large : d<n*(n+1))
    (ih : ∀ ys : List ℝ, ys.length<n → reduced P ys=0) : p=0 := by
  obtain ⟨walls,symm⟩ := residual_walls P p he ih
  exact zero_of_degree_lt p (hd.trans_lt (by nlinarith only [pairDegree_square n,large])) walls symm

/-- A term of a differential symbol, with space and cubic-time orders. -/
structure SymbolTerm where
  space : ℕ
  time : ℕ
  coeff : ℝ

/-- Evaluate a finite differential symbol in a real algebra. -/
def symbolValue {R : Type*} [CommRing R] (f : ℝ →+* R) (u v : R) : List SymbolTerm → R
  | [] => 0
  | m::ms => f m.coeff*u^m.space*v^m.time+symbolValue f u v ms

/-- Weighted degree, with weights one in space and three in time. -/
def symbolWeight : List SymbolTerm → ℕ
  | [] => 0
  | m::ms => max (m.space+3*m.time) (symbolWeight ms)

private theorem symbol_degree {n : ℕ} (u v : Poly n) (hu : u.totalDegree≤1)
    (hv : v.totalDegree≤3) (ms : List SymbolTerm) :
    (symbolValue C u v ms).totalDegree ≤ symbolWeight ms := by
  induction ms with
  | nil => simp [symbolValue,symbolWeight]
  | cons m ms ih =>
    have hc : (C m.coeff : Poly n).totalDegree ≤ 0 := (totalDegree_C _).le
    have hm := dmul (dmul hc (dpow hu m.space)) (dpow hv m.time)
    exact dadd (by simpa only [zero_add,Nat.mul_one,Nat.mul_comm m.time] using hm) ih

private theorem eval_symbol {n : ℕ} (x : Fin n → ℝ) (u v : Poly n) (ms : List SymbolTerm) :
    eval x (symbolValue C u v ms)=symbolValue (RingHom.id ℝ) (eval x u) (eval x v) ms := by
  induction ms with
  | nil => simp [symbolValue]
  | cons m ms ih => simp only [symbolValue,map_add,map_mul,map_pow,eval_C,RingHom.id_apply,ih]

private def symbolResidual (n : ℕ) (ms : List SymbolTerm) : Poly n :=
  reduced (fun u v => symbolValue C u v ms) (List.ofFn X)

private theorem eval_residual {n : ℕ} (ms : List SymbolTerm) (x : Fin n → ℝ) :
    eval x (symbolResidual n ms)=reduced (fun u v => symbolValue (RingHom.id ℝ) u v ms) (List.ofFn x) := by
  rw [symbolResidual,map_reduced (eval x) _ _ (fun u v => symbolValue (RingHom.id ℝ) u v ms)
    (fun u v => eval_symbol x u v ms)]
  simp [List.ofFn_eq_map,List.map_map,Function.comp_def]

private theorem residual_degree (n : ℕ) (ms : List SymbolTerm) :
    (symbolResidual n ms).totalDegree ≤ symbolWeight ms+pairDegree n :=
  reduced_degree _ fun u v hu hv => symbol_degree u v hu hv ms

/-- The consecutive positive momenta avoid every reflecting wall. -/
def testGrid (n : ℕ) (i : Fin n) : ℝ := (i.val:ℝ)+1

private theorem regular_evaluation {n : ℕ} (x : Fin n → ℝ)
    (nonzero : ∀ i,x i≠0) (distinct : Function.Injective (fun i => |x i|)) :
    eval x (discriminant n)≠0 := by
  classical
  rw [discriminant,map_prod]
  apply Finset.prod_ne_zero_iff.mpr
  rintro ⟨i,j⟩ _
  rw [map_pow]
  apply pow_ne_zero
  by_cases eq : i=j
  · subst j
    simpa only [L,wall,mate,if_true,sub_zero,eval_X] using nonzero i
  · by_cases lt : i<j
    · simp only [L,wall,mate,eq,lt,if_false,if_true,map_sub,eval_X,sub_ne_zero]
      exact fun h => eq (distinct (congrArg abs h))
    · simp only [L,wall,mate,eq,lt,if_false,sub_neg_eq_add,map_add,eval_X]
      intro h
      have e : x i= -x j := eq_neg_of_add_eq_zero_left h
      exact eq (distinct ((congrArg abs e).trans (abs_neg _)))

private theorem grid_regular (n : ℕ) : eval (testGrid n) (discriminant n)≠0 := by
  have pos (i : Fin n) : 0<testGrid n i := by unfold testGrid; positivity
  apply regular_evaluation _ (fun i => (pos i).ne')
  intro i j h
  change |testGrid n i|=|testGrid n j| at h
  rw [abs_of_pos (pos i),abs_of_pos (pos j)] at h
  exact Fin.ext (by exact_mod_cast (add_right_cancel h : (i.val:ℝ)=j.val))

/-- At the limiting degree every residual vanishing on the smaller wave
sets is a scalar multiple of the discriminant. One regular grid therefore
detects the whole remaining obstruction. -/
private theorem critical_test {n : ℕ} (ms : List SymbolTerm) (bound : symbolWeight ms≤n*(n+1))
    (ih : ∀ ys : List ℝ, ys.length<n → reduced (fun u v => symbolValue (RingHom.id ℝ) u v ms) ys=0)
    (hg : eval (testGrid n) (symbolResidual n ms)=0) : symbolResidual n ms=0 := by
  obtain ⟨hw,hs⟩ := residual_walls _ _ (eval_residual ms) ih
  obtain ⟨q,hq⟩ := discriminant_dvd _ hw hs
  by_contra hn
  have nz := mul_ne_zero_iff.mp (hq ▸ hn)
  have hd := residual_degree n ms
  rw [hq,totalDegree_mul_of_isDomain nz.1 nz.2,discriminant_degree] at hd
  have hq0 : q.totalDegree=0 := by nlinarith only [hd,pairDegree_square n,bound]
  have hc := totalDegree_eq_zero_iff_eq_C.mp hq0
  rw [hq,map_mul,hc,eval_C] at hg
  have zero := (mul_eq_zero.mp hg).resolve_left (grid_regular n)
  exact nz.2 (hc.trans (by rw [zero,map_zero]))

/-- A polynomial cubic-flow symbol passes every signed wave test if and
only if it passes all orders n with n(n+1) strictly below its weight.
At equality the single list of momenta 1 through n suffices. -/
theorem critical_grid_criterion (ms : List SymbolTerm) :
    let P := fun u v => symbolValue (RingHom.id ℝ) u v ms
    (∀ xs, reduced P xs=0) ↔
      (∀ xs : List ℝ, xs.length*(xs.length+1)<symbolWeight ms → reduced P xs=0) ∧
      (∀ n, n*(n+1)=symbolWeight ms → reduced P (List.ofFn (testGrid n))=0) := by
  dsimp only
  constructor
  · exact fun H => ⟨fun xs _ => H xs,fun n _ => H _⟩
  · rintro ⟨below,atGrid⟩ xs
    let P := fun u v => symbolValue (RingHom.id ℝ) u v ms
    suffices all : ∀ n, ∀ x : Fin n → ℝ, reduced P (List.ofFn x)=0 by
      simpa only [List.ofFn_get] using all xs.length xs.get
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro x
      have smaller (ys : List ℝ) (hy : ys.length<n) : reduced P ys=0 := by
        simpa only [List.ofFn_get] using ih ys.length hy ys.get
      rcases lt_trichotomy (n*(n+1)) (symbolWeight ms) with low|eq|high
      · exact below _ (by simpa only [List.length_ofFn] using low)
      · have zero := critical_test ms eq.ge smaller ((eval_residual ms _).trans (atGrid n eq))
        rw [← eval_residual,zero,map_zero]
      · have zero := vanish_above_degree P _ (eval_residual ms) (residual_degree n ms) high smaller
        rw [← eval_residual,zero,map_zero]

/-- The number of necessary wave orders grows at most as the square root
of the weighted degree. -/
theorem finite_wave_criterion (ms : List SymbolTerm) :
    let P := fun u v => symbolValue (RingHom.id ℝ) u v ms
    (∀ xs, reduced P xs=0) ↔
      (∀ xs : List ℝ, xs.length*(xs.length+1) ≤ symbolWeight ms → reduced P xs=0) := by
  constructor
  · exact fun H xs _ => H xs
  · intro H
    apply (critical_grid_criterion ms).mpr
    exact ⟨fun xs h => H xs h.le,fun n h => H _ (by simpa only [List.length_ofFn] using h.le)⟩

/-- For weighted degree at most twelve, after the zero-, one- and two-wave
conditions only the single triple of momenta (1,2,3) remains. -/
theorem degree_twelve_criterion (ms : {ms : List SymbolTerm // symbolWeight ms≤12}) :
    let P := fun u v => symbolValue (RingHom.id ℝ) u v ms.val
    (∀ xs, reduced P xs=0) ↔
      (∀ xs : List ℝ, xs.length≤2 → reduced P xs=0) ∧ reduced P [1,2,3]=0 := by
  dsimp only
  constructor
  · exact fun H => ⟨fun xs _ => H xs,H _⟩
  · rintro ⟨pairs,triple⟩
    apply (critical_grid_criterion ms.val).mpr
    have lim := ms.property
    constructor
    · intro xs small
      apply pairs
      by_contra! h
      have lower := Nat.mul_le_mul (show 3≤xs.length by omega) (show 4≤xs.length+1 by omega)
      omega
    · intro n eq
      by_cases few : n≤2
      · exact pairs _ (by simpa only [List.length_ofFn] using few)
      · have three : n=3 := by
          by_contra ne
          have lower := Nat.mul_le_mul (show 4≤n by omega) (show 5≤n+1 by omega)
          omega
        subst n
        have grid : List.ofFn (testGrid 3) = [1,2,3] := by norm_num [testGrid,List.ofFn_succ,List.ofFn_zero]
        rwa [grid]

/-- Every real simple cubic symbol satisfies the division-free N-wave
condition for every list, including soft momenta and signed collisions. -/
theorem all_orders (w : Weights) (xs : List ℝ) : reduced (dispersion w) xs = 0 := by
  suffices H : ∀ n, ∀ x : Fin n → ℝ, reduced (dispersion w) (List.ofFn x) = 0 by
    simpa only [List.ofFn_get] using H xs.length xs.get
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro x
    by_cases hn : n < 4
    · interval_cases n
      · simp [List.ofFn_zero,reduced,signSum,term,cubicSum,dispersion,graph]
      · simp [List.ofFn_succ,List.ofFn_zero,reduced,signSum,term,cubicSum,dispersion,graph]
      · simp only [List.ofFn_succ,List.ofFn_zero]
        exact reduced_two w _ _
      · simp only [List.ofFn_succ,List.ofFn_zero]
        exact reduced_three w _ _ _
    · have hi (ys : List ℝ) (hy : ys.length < n) : reduced (dispersion w) ys = 0 := by
        simpa only [List.ofFn_get] using ih ys.length hy ys.get
      have large : 12<n*(n+1) := by
        have hn4 : 4≤n := by omega
        nlinarith only [Nat.mul_self_le_mul_self hn4,hn4]
      have hz := vanish_above_degree (dispersion w) _ (specialize w) (degree_bound n w) large hi
      rw [← specialize,hz,map_zero]

/-- Number of positive magnitudes needed at wave order n. After dividing by
the signed discriminant, only D−n(n+1) degrees remain. -/
def trialWidth (D n : ℕ) := n+(D-n*(n+1))/2

private def magnitude : ℕ ↪ ℝ where
  toFun k := (k:ℝ)+1
  inj' i j h := by exact_mod_cast (add_right_cancel h : (i:ℝ)=(j:ℝ))

private def alphabet (k : ℕ) := (Finset.range k).map magnitude

private theorem alphabet_pos {k : ℕ} {t : ℝ} (ht : t∈alphabet k) : 0<t := by
  obtain ⟨j,_,rfl⟩ := Finset.mem_map.mp ht
  change 0<(j:ℝ)+1
  positivity

/-- All unordered n-wave trials on the first `trialWidth D n` positive integers. -/
def waveTrials (D n : ℕ) := (alphabet (trialWidth D n)).powersetCard n

private theorem sortedTrial {n : ℕ} (x : Fin n → ℝ) (hi : Function.Injective x) :
    (List.ofFn x).Perm ((Finset.univ.image x).sort (·≤·)) := by
  apply (List.perm_ext_iff_of_nodup (List.nodup_ofFn_ofInjective hi) (Finset.sort_nodup _ _)).mpr
  intro z
  simp only [List.mem_ofFn,Finset.mem_sort,Finset.mem_image,Finset.mem_univ,true_and]

private theorem strict_table_test {n D : ℕ} (ms : List SymbolTerm) (degree : symbolWeight ms≤D)
    (small : n*(n+1)≤D)
    (ih : ∀ ys : List ℝ, ys.length<n →
      reduced (fun u v => symbolValue (RingHom.id ℝ) u v ms) ys=0)
    (table : ∀ s∈waveTrials D n,
      reduced (fun u v => symbolValue (RingHom.id ℝ) u v ms) (s.sort (·≤·))=0) : symbolResidual n ms=0 := by
  classical
  let P := fun u v => symbolValue (RingHom.id ℝ) u v ms
  obtain ⟨walls,symm⟩ := residual_walls P _ (eval_residual ms) ih
  obtain ⟨q,factor⟩ := discriminant_dvd _ walls symm
  by_contra nonzero
  have hn := mul_ne_zero_iff.mp (factor ▸ nonzero)
  have hd := residual_degree n ms
  rw [factor,totalDegree_mul_of_isDomain hn.1 hn.2,discriminant_degree] at hd
  have threshold : 2*n^2=pairDegree n+n*(n+1) := by nlinarith only [pairDegree_square n]
  rw [threshold] at hd
  have bound : q.totalDegree≤D-n*(n+1) := by omega
  let S := alphabet (trialWidth D n)
  have size (i : Fin n) : q.totalDegree+2*(n-1)<2*S.card := by
    have card : S.card=trialWidth D n := by simp [S,alphabet]
    rw [card,trialWidth]
    have hi := i.isLt
    omega
  apply hn.2
  apply (SignedGrid.interpolation S (fun _ h => alphabet_pos h) q size).mpr
  intro x hx inject
  let z := fun i => |x i|
  let s := Finset.univ.image z
  have hs : s∈waveTrials D n := Finset.mem_powersetCard.mpr
    ⟨by rintro y hy; obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hy; exact hx i,
     (Finset.card_image_of_injective Finset.univ (show Function.Injective z from inject)).trans
       (Finset.card_univ.trans (Fintype.card_fin n))⟩
  have signed : reduced P (List.ofFn x)=reduced P (List.ofFn z) := by
    simp only [List.ofFn_eq_map,reduced]
    apply sign_map
    intro i
    rcases le_total 0 (x i) with hi|hi
    · exact Or.inl (abs_of_nonneg hi).symm
    · exact Or.inr (by simp only [z,abs_of_nonpos hi,neg_neg])
  have hres : eval x (symbolResidual n ms)=0 := (eval_residual ms x).trans
    (signed.trans ((reduced_perm P _ _ (sortedTrial z inject)).trans (table s hs)))
  rw [factor,map_mul] at hres
  exact (mul_eq_zero.mp hres).resolve_left (regular_evaluation x
    (fun i eq => by have h := alphabet_pos (hx i); rw [eq,abs_zero] at h; exact h.false) inject)

/-- Finitely many scalar evaluations decide the entire real N-wave identity.
Every test uses an increasing list of distinct positive integers. -/
theorem finite_table_criterion (D : ℕ) (ms : {ms : List SymbolTerm // symbolWeight ms≤D}) :
    let P := fun u v => symbolValue (RingHom.id ℝ) u v ms.val
    (∀ xs, reduced P xs=0) ↔
      ∀ n, n*(n+1)≤D → ∀ s∈waveTrials D n, reduced P (s.sort (·≤·))=0 := by
  dsimp only
  constructor
  · exact fun h _ _ _ _ => h _
  · intro table xs
    let P := fun u v => symbolValue (RingHom.id ℝ) u v ms.val
    suffices all : ∀ n, ∀ x : Fin n → ℝ, reduced P (List.ofFn x)=0 by
      simpa only [List.ofFn_get] using all xs.length xs.get
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro x
      have smaller (ys : List ℝ) (hy : ys.length<n) : reduced P ys=0 := by
        simpa only [List.ofFn_get] using ih ys.length hy ys.get
      by_cases low : n*(n+1)≤D
      · have zero := strict_table_test ms.val ms.property low smaller (table n low)
        rw [← eval_residual,zero,map_zero]
      · have high : symbolWeight ms.val<n*(n+1) := ms.property.trans_lt (lt_of_not_ge low)
        have zero := vanish_above_degree P _ (eval_residual ms.val) (residual_degree n ms.val) high smaller
        rw [← eval_residual,zero,map_zero]

/-- Exactly 18 scalar tests suffice through weight twelve: one empty input,
six singletons, the ten pairs from the first five momenta and the triple
(1,2,3). No values at negative momenta or collisions need be supplied. -/
theorem eighteen_test_criterion (ms : {ms : List SymbolTerm // symbolWeight ms≤12}) :
    let P := fun u v => symbolValue (RingHom.id ℝ) u v ms.val
    ((∀ xs, reduced P xs=0) ↔ ∀ n<4, ∀ s∈waveTrials 12 n, reduced P (s.sort (·≤·))=0) ∧
    (waveTrials 12 0).card=1 ∧ (waveTrials 12 1).card=6 ∧
    (waveTrials 12 2).card=10 ∧ (waveTrials 12 3).card=1 := by
  dsimp only
  refine ⟨⟨fun h _ _ _ _ => h _,fun table => ?_⟩,?_⟩
  · apply (finite_table_criterion 12 ms).mpr
    intro n hn
    apply table n
    by_contra! four
    have bad := Nat.mul_le_mul four (show 5≤n+1 by omega)
    omega
  · simp only [waveTrials,Finset.card_powersetCard,alphabet,Finset.card_map,Finset.card_range,trialWidth]
    norm_num [Nat.choose]

#print axioms finite_table_criterion
#print axioms eighteen_test_criterion
#print axioms universal_degree
#print axioms degree_twelve_criterion
#print axioms critical_grid_criterion
#print axioms finite_wave_criterion
#print axioms all_orders
end WaveList
end GaloisForLFunctions.HTGeometry.DispersivePDE.CubicHierarchy
