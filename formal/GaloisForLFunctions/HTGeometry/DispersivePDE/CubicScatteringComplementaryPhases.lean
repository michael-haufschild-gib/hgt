import GaloisForLFunctions.HTGeometry.DispersivePDE.CubicScatteringAllOrders

/-!
# Complementary phases in the cubic Hirota expansion

Assign each wave occurring once to one of the two copies of the tau
function. The two normalized phases multiply to the signed Vandermonde
divided by one common denominator. This transfers the polynomial
all-orders condition to the coefficients of the exponential ansatz.
-/

noncomputable section
namespace GaloisForLFunctions.HTGeometry.DispersivePDE.CubicHierarchy.WaveList

/-- Sum over ordered complementary sublists, retaining the order within each. -/
def splitSum {α : Type*} : List α → (List α → List α → ℝ) → ℝ
  | [],F => F [] []
  | x::xs,F => splitSum xs (fun a b => F (x::a) b)+splitSum xs (fun a b => F a (x::b))

theorem slide {α : Type*} (x : α) (a b : List α) :
    (x::(a++b)).Perm (a++(x::b)) := by
  induction a with
  | nil => exact .refl _
  | cons y a ih => exact (List.Perm.swap y x _).trans (ih.cons y)

theorem split_congr {α : Type*} (xs : List α) (F G : List α → List α → ℝ)
    (he : ∀ a b, (a++b).Perm xs → F a b=G a b) : splitSum xs F=splitSum xs G := by
  induction xs generalizing F G with
  | nil => exact he [] [] (.refl _)
  | cons x xs ih =>
    exact congrArg₂ (·+·) (ih _ _ fun a b hp => he _ _ (hp.cons x))
      (ih _ _ fun a b hp => he _ _ ((slide x a b).symm.trans (hp.cons x)))

theorem split_scale {α : Type*} (xs : List α) (c : ℝ) (F : List α → List α → ℝ) :
    splitSum xs (fun a b => c*F a b)=c*splitSum xs F := by
  induction xs generalizing F with
  | nil => rfl
  | cons x xs ih => simp only [splitSum,ih,mul_add]

private theorem signed_split (xs : List ℝ) (F : List ℝ → ℝ)
    (hf : ∀ {a b}, a.Perm b → F a=F b) :
    signSum xs F=splitSum xs (fun a b => F (a++b.map Neg.neg)) := by
  induction xs generalizing F with
  | nil => rfl
  | cons x xs ih =>
    rw [signSum,splitSum,ih _ (fun h => hf (h.cons x)),ih _ (fun h => hf (h.cons (-x)))]
    apply congrArg₂ (·+·) rfl
    apply split_congr
    exact fun a b _ => hf (slide (-x) a (b.map Neg.neg))

/-- Pair denominators for the ordinary KdV phase (k−l)²/(k+l)². -/
def pairDen : List ℝ → ℝ
  | [] => 1
  | x::xs => factors (fun y => (x+y)^2) xs*pairDen xs

def phase (xs : List ℝ) := pairWeight xs/pairDen xs

private def cross : List ℝ → List ℝ → ℝ
  | [],_ => 1
  | x::xs,ys => factors (fun y => (x+y)^2) ys*cross xs ys

theorem factors_append (f : ℝ → ℝ) (a b : List ℝ) :
    factors f (a++b)=factors f a*factors f b := by
  induction a with
  | nil => simp [factors]
  | cons x a ih => simp only [List.cons_append,factors,ih,mul_assoc]

private theorem factors_neg (f : ℝ → ℝ) (a : List ℝ) :
    factors f (a.map Neg.neg)=factors (fun t => f (-t)) a := by
  induction a with
  | nil => rfl
  | cons x a ih => simp only [List.map_cons,factors,ih]

theorem den_perm {a b : List ℝ} (h : a.Perm b) : pairDen a=pairDen b := by
  induction h with
  | nil => rfl
  | cons x h ih => rw [pairDen,pairDen,factors_perm _ h,ih]
  | swap x y l => simp only [pairDen,factors]; rw [add_comm x y]; ring
  | trans _ _ h k => exact h.trans k

private theorem den_append (a b : List ℝ) : pairDen (a++b)=pairDen a*pairDen b*cross a b := by
  induction a with
  | nil => simp [pairDen,cross]
  | cons x a ih => simp only [List.cons_append,pairDen,cross,factors_append,ih]; ring

private theorem weight_neg (b : List ℝ) : pairWeight (b.map Neg.neg)=pairWeight b := by
  induction b with
  | nil => rfl
  | cons x b ih =>
    simp only [List.map_cons,pairWeight,factors_neg,ih]
    rw [show (fun y : ℝ => (-x- -y)^2)=(fun y => (x-y)^2) by funext y; ring]

private theorem weight_split (a b : List ℝ) :
    pairWeight (a++b.map Neg.neg)=pairWeight a*pairWeight b*cross a b := by
  induction a with
  | nil => simp [weight_neg,pairWeight,cross]
  | cons x a ih =>
    simp only [List.cons_append,pairWeight,factors_append,factors_neg,sub_neg_eq_add,ih,cross]
    ring

private theorem den_pos (a : List ℝ) (h : ∀ x∈a, 0<x) : 0<pairDen a := by
  have hs (x : ℝ) (hx : 0<x) (b : List ℝ) (hb : ∀ y∈b, 0<y) :
      0<factors (fun y => (x+y)^2) b := by
    induction b with
    | nil => exact zero_lt_one
    | cons y b ih =>
      exact mul_pos (sq_pos_of_pos (add_pos hx (hb _ List.mem_cons_self)))
        (ih fun z hz => hb z (List.mem_cons_of_mem _ hz))
  induction a with
  | nil => exact zero_lt_one
  | cons x a ih =>
    have ht (y) (hy : y∈a) := h y (List.mem_cons_of_mem _ hy)
    exact mul_pos (hs _ (h _ List.mem_cons_self) _ ht) (ih ht)

/-- Splitting a phase into opposite wave lists preserves the signed
Vandermonde after multiplication by the common pair denominator. -/
theorem complementary_weight (a b : List ℝ) (h : ∀ x∈a++b, 0<x) :
    pairDen (a++b)*(phase a*phase b)=pairWeight (a++b.map Neg.neg) := by
  have ha := den_pos a fun x hx => h x (List.mem_append_left _ hx)
  have hb := den_pos b fun x hx => h x (List.mem_append_right _ hx)
  rw [weight_split,den_append,phase,phase]
  field_simp [ha.ne',hb.ne']

private theorem signed_sums (a b : List ℝ) :
    (a++b.map Neg.neg).sum=a.sum-b.sum ∧ cubicSum (a++b.map Neg.neg)=cubicSum a-cubicSum b := by
  have hn (c : List ℝ) : (c.map Neg.neg).sum = -c.sum := by
    induction c with
    | nil => simp
    | cons x c ih => simp only [List.map_cons,List.sum_cons,ih,neg_add]
  constructor
  · rw [List.sum_append,hn,sub_eq_add_neg]
  · unfold cubicSum
    simp only [List.map_append,List.sum_append,List.map_map,Function.comp_def]
    have H := hn (b.map fun x => x^3)
    simp only [List.map_map,Function.comp_def] at H
    simp only [show ∀ x : ℝ, (-x)^3= -(x^3) by intro x; ring,H,sub_eq_add_neg]

/-- The normalized sum over the two complementary occupied wave sets
vanishes at every positive finite wave list and every hierarchy symbol. -/
theorem positive_complementary_cancellation (w : Weights) (xs : List ℝ) (pos : ∀ t∈xs, 0<t) :
    splitSum xs (fun a b => phase a*phase b*dispersion w (a.sum-b.sum) (cubicSum a-cubicSum b))=0 := by
  have hz := all_orders w xs
  unfold reduced at hz
  rw [signed_split _ _ (fun h => by simp only [term,cubicSum,h.sum_eq,(h.map _).sum_eq,pairWeight_perm h])] at hz
  suffices he : pairDen xs * splitSum xs
      (fun a b => phase a*phase b*dispersion w (a.sum-b.sum) (cubicSum a-cubicSum b)) = 0 from
    (mul_eq_zero.mp he).resolve_left (den_pos xs pos).ne'
  rw [← split_scale,← hz]
  apply split_congr
  intro a b h
  rw [← den_perm h,term,(signed_sums a b).1,(signed_sums a b).2]
  have he := complementary_weight a b (fun t ht => pos t (h.mem_iff.mp ht))
  linear_combination dispersion w (a.sum-b.sum) (cubicSum a-cubicSum b)*he

/-- Logarithmic probe labels parameterize every positive momentum. -/
theorem complementary_cancellation (w : Weights) (rs : List ℝ) :
    let xs := rs.map Real.exp
    splitSum xs (fun a b => phase a*phase b*dispersion w (a.sum-b.sum) (cubicSum a-cubicSum b))=0 := by
  apply positive_complementary_cancellation
  intro t ht
  obtain ⟨v,_,rfl⟩ := List.mem_map.mp ht
  exact Real.exp_pos v

#print axioms complementary_weight
#print axioms complementary_cancellation
end GaloisForLFunctions.HTGeometry.DispersivePDE.CubicHierarchy.WaveList
