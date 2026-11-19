import GaloisForLFunctions.RHTower.Chebyshev.OrbitCubicIntegerHull

/-!
# Ehrhart polynomial of the cubic trace-one integer hull

In centered coordinates a+b+c=nk, where m=n+2 and k is the dilation.
The nonnegative triples form the inner triangle. Each remaining triple
has exactly one cyclic transition from a nonnegative to a negative
coordinate. Each such sector consists of rows of length (n+1)v+1 for
0 ≤ v < k. This counts every dilation, including the zero dilation.
-/

noncomputable section
namespace RHTower.OrbitCubic.IntegerHull.Ehrhart

@[ext] structure Triple where
  a : ℤ
  b : ℤ
  c : ℤ

def rot (x : Triple) : Triple := ⟨x.c,x.a,x.b⟩

private theorem cube (x : Triple) : rot (rot (rot x))=x := by cases x; rfl

/-- Cyclic inequalities of the dilated triangle, in integer coordinates. -/
def inside (n k : ℕ) (x : Triple) :=
  x.a+x.b+x.c=(n:ℤ)*k ∧ x.a≤(n+1:ℤ)*(x.b+k) ∧ x.b≤(n+1:ℤ)*(x.c+k) ∧ x.c≤(n+1:ℤ)*(x.a+k)

def dilated (n k : ℕ) (p : ℤ × ℤ) :=
  0≤leftMass ((n:ℤ)+2) p.1 p.2 ∧ 0≤rightMass ((n:ℤ)+2) p.1 p.2 ∧
    leftMass ((n:ℤ)+2) p.1 p.2+rightMass ((n:ℤ)+2) p.1 p.2≤(k:ℤ)*index ((n:ℤ)+2)

abbrev latticePoint (n k : ℕ) := {p : ℤ × ℤ // dilated n k p}

private def coord (n k : ℕ) (u v : ℤ) : Triple :=
  ⟨u,v-k,((n:ℤ)+1)*k-u-v⟩

private theorem coordinates (n k : ℕ) (u v : ℤ) :
    inside n k (coord n k u v) ↔ 0≤leftMass ((n:ℤ)+2) u v ∧ 0≤rightMass ((n:ℤ)+2) u v ∧
      leftMass ((n:ℤ)+2) u v+rightMass ((n:ℤ)+2) u v ≤ (k:ℤ)*index ((n:ℤ)+2) := by
  simp only [inside,coord,leftMass,rightMass,index]
  constructor
  · rintro ⟨_,ha,hb,hc⟩
    exact ⟨by linarith only [hc],by linarith only [ha],by linarith only [hb]⟩
  · rintro ⟨h1,h2,h3⟩
    exact ⟨by ring,by linarith only [h2],by linarith only [h3],by linarith only [h1]⟩

private def coordEquiv (n k : ℕ) : latticePoint n k ≃ {x : Triple // inside n k x} where
  toFun p := ⟨coord n k p.val.1 p.val.2,(coordinates _ _ _ _).mpr p.property⟩
  invFun x := ⟨(x.val.a,x.val.b+k),(coordinates _ _ _ _).mp (by
    have he : coord n k x.val.a (x.val.b+k)=x.val := by
      ext <;> simp only [coord] <;> linarith only [x.property.1]
    rw [he]
    exact x.property)⟩
  left_inv p := by apply Subtype.ext; apply Prod.ext <;> simp [coord]
  right_inv x := by apply Subtype.ext; ext <;> simp only [coord] <;> linarith only [x.property.1]

private theorem rotate_inside {n k : ℕ} {x : Triple} (h : inside n k x) : inside n k (rot x) :=
  ⟨by change x.c+x.a+x.b=_; linarith only [h.1],h.2.2.2,h.2.1,h.2.2.1⟩

abbrev Fan (n k : ℕ) := (v : Fin k) × Fin ((n+1)*v.val+1)

private def core {n k : ℕ} (s : TriangleIndex (n*k)) : Triple :=
  ⟨s.2.val,(s.1.val:ℤ)-s.2.val,(n:ℤ)*k-s.1.val⟩

private def fan {n k : ℕ} (s : Fan n k) : Triple := coord n k s.2.val s.1.val

private theorem core_nonneg {n k : ℕ} (s : TriangleIndex (n*k)) :
    0≤(core s).a ∧ 0≤(core s).b ∧ 0≤(core s).c := by
  obtain ⟨i,j⟩ := s
  have hi := i.isLt
  have hj := j.isLt
  simp only [core]
  rw [← Nat.cast_mul]
  omega

private theorem core_inside {n k : ℕ} (s : TriangleIndex (n*k)) : inside n k (core s) := by
  obtain ⟨a,b,c⟩ := core_nonneg s
  have hs : (core s).a+(core s).b+(core s).c=(n:ℤ)*k := by simp only [core]; ring
  have nonneg (x : ℤ) (hx : 0≤x) := mul_nonneg (Int.natCast_nonneg n) hx
  exact ⟨hs,by linarith only [a,b,c,hs,nonneg _ b,Int.natCast_nonneg k],
    by linarith only [a,b,c,hs,nonneg _ c,Int.natCast_nonneg k],
    by linarith only [a,b,c,hs,nonneg _ a,Int.natCast_nonneg k]⟩

private theorem core_exists {n k : ℕ} {x : Triple} (hs : inside n k x)
    (ha : 0≤x.a) (hb : 0≤x.b) (hc : 0≤x.c) : ∃ s : TriangleIndex (n*k), core s=x := by
  have h := hs.1
  rw [← Nat.cast_mul] at h
  let i : Fin (n*k+1) := ⟨(x.a+x.b).toNat,by omega⟩
  let j : Fin (i.val+1) := ⟨x.a.toNat,by dsimp [i]; omega⟩
  refine ⟨⟨i,j⟩,?_⟩
  ext <;> simp only [core,i,j,← Nat.cast_mul] <;> omega

private theorem core_inj {n k : ℕ} : Function.Injective (@core n k) := by
  rintro ⟨i,j⟩ ⟨i',j'⟩ h
  have h1 := congrArg Triple.a h
  have h2 := congrArg Triple.b h
  change (j.val:ℤ)=j'.val at h1
  change (i.val:ℤ)-j.val=(i'.val:ℤ)-j'.val at h2
  have hi : i=i' := Fin.ext (by omega)
  subst i'
  have hj : j=j' := Fin.ext (by omega)
  subst j'
  rfl

private theorem fan_sign {n k : ℕ} (s : Fan n k) : 0≤(fan s).a ∧ (fan s).b<0 := by
  have h := s.1.isLt
  change 0≤(s.2.val:ℤ) ∧ (s.1.val:ℤ)-k<0
  omega

private theorem fan_inside {n k : ℕ} (s : Fan n k) : inside n k (fan s) := by
  obtain ⟨v,u⟩ := s
  have hv : (v.val:ℤ) ≤ k := by exact_mod_cast v.isLt.le
  have hu : (u.val:ℤ) ≤ ((n:ℤ)+1)*v.val := by exact_mod_cast (Nat.le_of_lt_succ u.isLt)
  have hm : 0 ≤ (n:ℤ)+1 := by positivity
  have ht : (v.val:ℤ)-k ≤ 0 := by linarith only [hv]
  have hc : 0 ≤ ((n:ℤ)+1)*k-u.val-v.val+k := by
    linarith only [hu,hv,mul_nonneg hm (sub_nonneg.mpr hv)]
  simp only [inside,fan,coord]
  exact ⟨by ring,by linarith only [hu],by linarith only [ht,mul_nonneg hm hc],
    by linarith only [mul_nonneg hm (Int.natCast_nonneg u.val),Int.natCast_nonneg u.val,Int.natCast_nonneg v.val]⟩

private theorem fan_exists {n k : ℕ} {x : Triple} (hs : inside n k x)
    (ha : 0≤x.a) (hb : x.b<0) : ∃ s : Fan n k, fan s=x := by
  have h := hs.2.1
  have hv : 0 ≤ x.b+k := by
    by_contra! hn
    exact (mul_neg_of_pos_of_neg (by positivity : (0:ℤ)<n+1) hn).not_ge (ha.trans h)
  let v : Fin k := ⟨(x.b+k).toNat,by omega⟩
  have he : (v.val:ℤ)=x.b+k := Int.toNat_of_nonneg hv
  have hu : x.a.toNat ≤ (n+1)*v.val := by
    exact_mod_cast (show (x.a.toNat:ℤ)≤((n:ℤ)+1)*v.val by rw [Int.toNat_of_nonneg ha,he]; exact h)
  refine ⟨⟨v,⟨x.a.toNat,Nat.lt_succ_of_le hu⟩⟩,?_⟩
  ext <;> simp only [fan,coord,Int.toNat_of_nonneg ha,he] <;> linarith only [hs.1]

private theorem fan_inj {n k : ℕ} : Function.Injective (@fan n k) := by
  rintro ⟨i,j⟩ ⟨i',j'⟩ h
  have h1 := congrArg Triple.a h
  have h2 := congrArg Triple.b h
  change (j.val:ℤ)=j'.val at h1
  change (i.val:ℤ)-k=(i'.val:ℤ)-k at h2
  have hi : i=i' := Fin.ext (by omega)
  subst i'
  have hj : j=j' := Fin.ext (by omega)
  subst j'
  rfl

/-- Inner triangle and three half-open outer sectors. -/
abbrev Chart (n k : ℕ) := TriangleIndex (n*k) ⊕ (Fan n k ⊕ (Fan n k ⊕ Fan n k))

private def vertex {n k : ℕ} : Chart n k → Triple
  | .inl s => core s
  | .inr (.inl s) => fan s
  | .inr (.inr (.inl s)) => rot (fan s)
  | .inr (.inr (.inr s)) => rot (rot (fan s))

private theorem vertex_inside {n k : ℕ} (s : Chart n k) : inside n k (vertex s) := by
  rcases s with s|s|s|s
  · exact core_inside s
  · exact fan_inside s
  · exact rotate_inside (fan_inside s)
  · exact rotate_inside (rotate_inside (fan_inside s))

private theorem vertex_inj {n k : ℕ} : Function.Injective (@vertex n k) := by
  have ro : Function.Injective rot := fun x y h => (cube x).symm.trans ((congrArg (fun z => rot (rot z)) h).trans (cube y))
  rintro (s|s|s|s) (t|t|t|t) h
  all_goals first
    | exact congrArg Sum.inl (core_inj h)
    | exact congrArg (fun x => Sum.inr (Sum.inl x)) (fan_inj h)
    | exact congrArg (fun x => Sum.inr (Sum.inr (Sum.inl x))) (fan_inj (ro h))
    | exact congrArg (fun x => Sum.inr (Sum.inr (Sum.inr x))) (fan_inj (ro (ro h)))
    | have a := congrArg Triple.a h; have b := congrArg Triple.b h; have c := congrArg Triple.c h
      simp only [vertex,rot] at a b c
      first | have hs := core_nonneg s | have hs := fan_sign s
      first | have ht := core_nonneg t | have ht := fan_sign t
      omega

private theorem vertex_surj {n k : ℕ} (x : Triple) (hx : inside n k x) :
    ∃ s : Chart n k, vertex s=x := by
  by_cases ha : 0≤x.a
  · by_cases hb : 0≤x.b
    · by_cases hc : 0≤x.c
      · obtain ⟨s,h⟩ := core_exists hx ha hb hc
        exact ⟨.inl s,h⟩
      · obtain ⟨s,h⟩ := fan_exists (rotate_inside (rotate_inside hx)) hb (lt_of_not_ge hc)
        exact ⟨.inr (.inr (.inl s)),(congrArg rot h).trans (cube x)⟩
    · obtain ⟨s,h⟩ := fan_exists hx ha (lt_of_not_ge hb)
      exact ⟨.inr (.inl s),h⟩
  · by_cases hc : 0≤x.c
    · obtain ⟨s,h⟩ := fan_exists (rotate_inside hx) hc (lt_of_not_ge ha)
      exact ⟨.inr (.inr (.inr s)),(congrArg (fun z => rot (rot z)) h).trans (cube x)⟩
    · have hb : 0≤x.b := by linarith only [hx.1,lt_of_not_ge ha,lt_of_not_ge hc,Int.natCast_nonneg (n*k),
        show ((n*k:ℕ):ℤ)=(n:ℤ)*k from Nat.cast_mul ..]
      obtain ⟨s,h⟩ := fan_exists (rotate_inside (rotate_inside hx)) hb (lt_of_not_ge hc)
      exact ⟨.inr (.inr (.inl s)),(congrArg rot h).trans (cube x)⟩

/-- Explicit row enumeration in every dilated integer hull. -/
def triangulation (n k : ℕ) : Chart n k ≃ latticePoint n k :=
  (Equiv.ofBijective (fun s : Chart n k => (⟨vertex s,vertex_inside s⟩ : {x // inside n k x}))
    ⟨fun _ _ he => vertex_inj (congrArg Subtype.val he),fun x => by
      obtain ⟨s,h⟩ := vertex_surj x.val x.property
      exact ⟨s,Subtype.ext h⟩⟩).trans (coordEquiv n k).symm

/-- Rotation acts on height k by an affine map whose translation is k
times the translation at height one. -/
def turnPoint (n k : ℕ) (p : ℤ × ℤ) : ℤ × ℤ := (((n:ℤ)+1)*k-p.1-p.2,p.1+k)

/-- Each lattice point belongs to the inner simplex or a rotation of a
row at distance strictly less than k from its outer vertex. -/
theorem sector_cover (n k : ℕ) (p : latticePoint n k) :
    (∃ u v : ℤ, 0≤u ∧ 0≤v ∧ u+v≤(n:ℤ)*k ∧ p.val=(u,v+k)) ∨
      ∃ u v : ℤ, 0≤u ∧ 0≤v ∧ v<k ∧ u≤((n:ℤ)+1)*v ∧
        (p.val=(u,v) ∨ p.val=turnPoint n k (u,v) ∨ p.val=turnPoint n k (turnPoint n k (u,v))) := by
  obtain ⟨s,rfl⟩ := (triangulation n k).surjective p
  rcases s with s|s|s|s
  · left
    refine ⟨(core s).a,(core s).b,(core_nonneg s).1,(core_nonneg s).2.1,?_,rfl⟩
    have h := (core_inside s).1
    linarith only [h,(core_nonneg s).2.2]
  all_goals
    right
    refine ⟨s.2.val,s.1.val,by positivity,by positivity,by exact_mod_cast s.1.isLt,
      by exact_mod_cast Nat.le_of_lt_succ s.2.isLt,?_⟩
  · left
    change ((s.2.val:ℤ),(s.1.val:ℤ)-k+k)=_
    simp
  · right; left
    rfl
  · right; right
    apply Prod.ext
    · change (s.1.val:ℤ)-k = ((n:ℤ)+1)*k-(((n:ℤ)+1)*k-s.2.val-s.1.val)-(s.2.val+k)
      ring
    · rfl

private theorem twice_fan (n k : ℕ) : 2*Fintype.card (Fan n k)=(n+1)*k*(k-1)+2*k := by
  rw [Fintype.card_sigma]
  simp only [Fintype.card_fin,Finset.sum_add_distrib,
    ← Finset.mul_sum,Finset.sum_const,Finset.card_univ,smul_eq_mul,mul_one]
  rw [Fin.sum_univ_eq_sum_range (fun i : ℕ => i) k]
  have h := Finset.sum_range_id_mul_two k
  nlinarith only [congrArg (fun x => (n+1)*x) h]

/-- Twice the Ehrhart polynomial is Dk²+3k+2, where D=m(m−1)+1.
The boundary coefficient is independent of the cubic parameter. -/
theorem ehrhart (n k : ℕ) :
    2*Nat.card (latticePoint n k)=((n+2)*(n+1)+1)*k^2+3*k+2 := by
  rw [← Nat.card_congr (triangulation n k),Nat.card_eq_fintype_card]
  simp only [Chart,Fintype.card_sum]
  have hf := twice_fan n k
  have hcore : 2*Fintype.card (TriangleIndex (n*k))=(n*k+1)*(n*k)+2*(n*k+1) := by
    simpa [Fan,TriangleIndex] using twice_fan 0 (n*k+1)
  cases k with
  | zero => nlinarith only [hf,hcore]
  | succ k =>
    simp only [Nat.succ_sub_one] at hf
    nlinarith only [hf,hcore]

end RHTower.OrbitCubic.IntegerHull.Ehrhart
