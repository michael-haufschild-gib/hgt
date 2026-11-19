import Mathlib.Algebra.MvPolynomial.Monad
import Mathlib.Algebra.MvPolynomial.NoZeroDivisors
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.RingTheory.MvPolynomial.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

/-!
# The signed-permutation discriminant in the cleared Hirota condition

A polynomial invariant under sign changes and signed transpositions vanishes
to even order on their reflecting hyperplanes. Vanishing on all the zero
and collision walls therefore costs at least `2n²` total degrees. This is
the degree obstruction in Shi, arXiv:2611.22194, Proposition 6.8.
-/

noncomputable section
open MvPolynomial Finset
namespace GaloisForLFunctions.HTGeometry.DispersivePDE.ReflectionDiscriminant
variable {n : ℕ}
abbrev Wall (n : ℕ) := Fin n × Fin n
abbrev Poly (n : ℕ) := MvPolynomial (Fin n) ℝ

/-- Diagonal indices give coordinate zero, increasing indices equality,
and decreasing indices equality after changing sign. -/
def mate {R : Type*} [Ring R] (w : Wall n) (x : Fin n → R) : R :=
  if w.1 = w.2 then 0 else if w.1 < w.2 then x w.2 else -x w.2

def wall {R : Type*} [Ring R] (w : Wall n) (x : Fin n → R) : R := x w.1 - mate w x

def project {R : Type*} [Ring R] (w : Wall n) (x : Fin n → R) (k : Fin n) : R :=
  if k = w.1 then mate w x else x k

def reflect {R : Type*} [Ring R] (w : Wall n) (x : Fin n → R) (k : Fin n) : R :=
  if k = w.1 then
    if w.1 = w.2 then -x w.1 else mate w x
  else if k = w.2 then (if w.1 < w.2 then x w.1 else -x w.1)
  else x k

abbrev L (w : Wall n) : Poly n := wall w X
abbrev cut (w : Wall n) := bind₁ (project w (X : Fin n → Poly n))
abbrev flip (w : Wall n) := bind₁ (reflect w (X : Fin n → Poly n))

private theorem map_mate {A B : Type*} [Ring A] [Ring B] (f : A →+* B) (w : Wall n) (x : Fin n → A) :
    f (mate w x) = mate w (fun i => f (x i)) := by
  unfold mate
  split_ifs <;> simp

private theorem map_wall {A B : Type*} [Ring A] [Ring B] (f : A →+* B) (w : Wall n) (x : Fin n → A) :
    f (wall w x) = wall w (fun i => f (x i)) := by rw [wall,map_sub,map_mate]; rfl

private theorem cut_wall (w : Wall n) : cut w (L w) = 0 := by
  change (cut w).toRingHom (wall w X) = 0
  rw [map_wall (cut w).toRingHom]
  change wall w (fun i => cut w (X i)) = 0
  simp only [bind₁_X_right]
  by_cases h : w.1 = w.2
  · simp [wall,project,mate,h]
  · by_cases hlt : w.1 < w.2 <;> simp [wall,project,mate,h,Ne.symm h,hlt]

private theorem flip_wall (w : Wall n) : flip w (L w) = -L w := by
  change (flip w).toRingHom (wall w X) = -L w
  rw [map_wall (flip w).toRingHom]
  change wall w (fun i => flip w (X i)) = -L w
  simp only [bind₁_X_right]
  by_cases h : w.1 = w.2
  · simp [wall,reflect,mate,h]
  · by_cases hlt : w.1 < w.2 <;> simp [wall,reflect,mate,h,Ne.symm h,hlt]
    ring

private theorem cut_flip (w : Wall n) (p : Poly n) : cut w (flip w p) = cut w p := by
  rw [bind₁_bind₁]
  apply congrArg (fun v : Fin n → Poly n => bind₁ v p)
  funext k
  by_cases h : w.1 = w.2
  · by_cases hk : k = w.2 <;> simp [reflect,project,mate,h,hk]
  · by_cases hk : k = w.1
    · subst k
      by_cases hl : w.1 < w.2 <;> simp [reflect,project,mate,h,Ne.symm h,hl]
    · by_cases hj : k = w.2
      · subst k
        by_cases hl : w.1 < w.2 <;> simp [reflect,project,mate,h,Ne.symm h,hl]
      · simp [reflect,project,hk,hj]

private theorem wall_nonzero (w : Wall n) : L w ≠ 0 := by
  let x := fun k : Fin n => if k = w.1 then (1 : ℝ) else 0
  have h : eval x (L w) = 1 := by
    rw [map_wall]
    by_cases he : w.1 = w.2
    · simp [wall,mate,x,he]
    · by_cases hl : w.1 < w.2 <;> simp [wall,mate,x,he,Ne.symm he,hl]
  intro hz
  rw [hz,map_zero] at h
  exact zero_ne_one h

private theorem dvd_sub_cut (w : Wall n) (p : Poly n) : L w ∣ p-cut w p := by
  induction p using MvPolynomial.induction_on with
  | C r => simp
  | add p q hp hq =>
    rw [map_add,show p+q-(cut w p+cut w q) = (p-cut w p)+(q-cut w q) by abel]
    exact dvd_add hp hq
  | mul_X p k hp =>
    have hX : L w ∣ (X k : Poly n)-cut w (X k) := by
      by_cases h : k = w.1
      · subst k; simp only [bind₁_X_right,project,ite_true]; exact dvd_refl _
      · simp [project,h]
    rw [map_mul,show p*X k - cut w p*cut w (X k) =
        (p-cut w p)*X k+cut w p*(X k-cut w (X k)) by ring]
    exact dvd_add (dvd_mul_of_dvd_left hp _) (dvd_mul_of_dvd_right hX _)

private theorem wall_dvd_iff (w : Wall n) (p : Poly n) : L w ∣ p ↔ cut w p = 0 := by
  constructor
  · rintro ⟨q,rfl⟩
    rw [map_mul,cut_wall,zero_mul]
  · intro h
    simpa only [h,sub_zero] using dvd_sub_cut w p

private theorem wall_prime (w : Wall n) : Prime (L w) := by
  refine ⟨wall_nonzero w,?_,fun a b h => ?_⟩
  · intro h
    exact not_isUnit_zero ((cut_wall w) ▸ h.map (cut w).toRingHom)
  · rw [wall_dvd_iff,map_mul,mul_eq_zero] at h
    exact h.imp ((wall_dvd_iff _ _).mpr) ((wall_dvd_iff _ _).mpr)

/-- Reflection invariance doubles the multiplicity forced by a zero on a wall. -/
theorem reflection_double_zero (w : Wall n) (p : Poly n) :
    cut w p = 0 → flip w p = p → L w^2 ∣ p := by
  intro hz he
  obtain ⟨q,hq⟩ := (wall_dvd_iff _ _).mpr hz
  have hflip : flip w q = -q := by
    rw [hq,map_mul,flip_wall] at he
    apply mul_left_cancel₀ (wall_nonzero w)
    linear_combination -he
  have hcut := congrArg (cut w) hflip
  rw [cut_flip,map_neg] at hcut
  have hzero : cut w q = 0 := by
    have htwo : (2 : Poly n)*cut w q = 0 := by linear_combination hcut
    exact (mul_eq_zero.mp htwo).resolve_left (by norm_num)
  obtain ⟨s,hs⟩ := (wall_dvd_iff _ _).mpr hzero
  exact ⟨s,by rw [hq,hs,pow_two,mul_assoc]⟩

/-- Integer point on the chosen wall, with all other absolute coordinates distinct. -/
private def witness (w : Wall n) : Fin n → ℤ := project w (fun i => (i.val : ℤ)+1)

private theorem witness_unique (w v : Wall n) (h : wall v (witness w) = 0) : w = v := by
  rcases w with ⟨i,j⟩
  rcases v with ⟨a,b⟩
  let g (k : Fin n) : ℤ := if k=i then
    (if i=j then 0 else if i<j then (j.val:ℤ)+1 else -((j.val:ℤ)+1)) else (k.val:ℤ)+1
  change g a-(if a=b then 0 else if a<b then g b else -g b)=0 at h
  suffices e : i.val=a.val ∧ j.val=b.val from Prod.ext (Fin.ext e.1) (Fin.ext e.2)
  dsimp only [g] at h
  split_ifs at h <;> constructor <;> omega

private theorem no_wall_divides (w v : Wall n) (h : w ≠ v) : ¬ L w ∣ L v := by
  let f := eval (fun k => (witness w k : ℝ))
  have value (t : Wall n) : f (L t) = (wall t (witness w) : ℤ) := by
    dsimp only [f]
    rw [map_wall]
    simp only [eval_X]
    exact (map_wall (Int.castRingHom ℝ) t (witness w)).symm
  have hw : wall w (witness w) = 0 := by
    by_cases he : w.1 = w.2
    · simp [wall,witness,project,mate,he]
    · by_cases hl : w.1 < w.2 <;> simp [wall,witness,project,mate,he,Ne.symm he,hl]
  rintro ⟨q,hq⟩
  have hv := congrArg f hq
  rw [map_mul,value,value,hw,Int.cast_zero,zero_mul] at hv
  exact h (witness_unique _ _ (by exact_mod_cast hv))

private theorem degree_wall (w : Wall n) : (L w).totalDegree = 1 := by
  have hu : (L w).totalDegree ≤ 1 := by
    change (X w.1 - mate w X : Poly n).totalDegree ≤ 1
    apply (totalDegree_sub _ _).trans
    by_cases h : w.1 = w.2
    · simp [mate,h,totalDegree_X]
    · by_cases hlt : w.1 < w.2 <;> simp [mate,h,hlt,totalDegree_X]
  have hn : (L w).totalDegree ≠ 0 := by
    intro hz
    have hc := totalDegree_eq_zero_iff_eq_C.mp hz
    have he := congrArg (cut w) hc
    rw [cut_wall,bind₁_C_right] at he
    exact wall_nonzero w (hc.trans he.symm)
  omega

/-- Product of the squares of all reflecting linear forms. -/
def discriminant (n : ℕ) : Poly n := ∏ w : Wall n, L w^2

theorem discriminant_degree (n : ℕ) : (discriminant n).totalDegree = 2*n^2 := by
  classical
  have H (s : Finset (Wall n)) : (∏ w ∈ s, L w^2).totalDegree = 2*s.card := by
    induction s using Finset.induction_on with
    | empty => simp
    | insert w s hw ih =>
      have hn := pow_ne_zero 2 (wall_nonzero w)
      rw [prod_insert hw,totalDegree_mul_of_isDomain hn
        (Finset.prod_ne_zero_iff.mpr fun v _ => pow_ne_zero _ (wall_nonzero v)),ih,
        pow_two,totalDegree_mul_of_isDomain (wall_nonzero w) (wall_nonzero w),
        degree_wall,card_insert_of_notMem hw]
      omega
  simpa [discriminant,Wall,pow_two] using H univ

/-- The signed-permutation discriminant divides every invariant polynomial
vanishing on all zero, equal and opposite coordinate walls. -/
theorem discriminant_dvd (p : Poly n) :
    (∀ w, cut w p = 0) → (∀ w, flip w p = p) → discriminant n ∣ p := by
  intro h0 hi
  apply Fintype.prod_dvd_of_isRelPrime
  · intro w v h
    exact ((wall_prime w).irreducible.isRelPrime_iff_not_dvd.mpr (no_wall_divides w v h)).pow
  · exact fun w => reflection_double_zero w p (h0 w) (hi w)

/-- Below degree 2n², the wall conditions characterize the zero polynomial. -/
theorem zero_of_degree_lt (p : Poly n) : p.totalDegree < 2*n^2 →
    (∀ w, cut w p = 0) → (∀ w, flip w p = p) → p = 0 := by
  intro hd hz he
  obtain ⟨q,hq⟩ := discriminant_dvd p hz he
  by_contra hp
  have hn : discriminant n ≠ 0 ∧ q ≠ 0 := mul_ne_zero_iff.mp (hq ▸ hp)
  rw [hq,totalDegree_mul_of_isDomain hn.1 hn.2,discriminant_degree] at hd
  omega

#print axioms reflection_double_zero
#print axioms discriminant_degree
#print axioms discriminant_dvd
#print axioms zero_of_degree_lt
end GaloisForLFunctions.HTGeometry.DispersivePDE.ReflectionDiscriminant
