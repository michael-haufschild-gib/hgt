import GaloisForLFunctions.HTGeometry.DispersivePDE.CubicGraphThreeWave

/-!
# Soft and colliding momenta in the cubic Hirota residual

In family (a) of Shi, arXiv:2611.22194, Proposition 6.8, clearing the
two-body phase leaves a squared Vandermonde. The reduced signed residual
on any finite wave list has exact boundary recursions. A zero momentum
deletes one wave. Two equal or opposite momenta delete both, with an
explicit surviving factor that retains the other pairwise collisions.
-/

noncomputable section
namespace GaloisForLFunctions.HTGeometry.DispersivePDE.CubicHierarchy
namespace WaveList
variable {R : Type*} [CommRing R]

/-- Product of one scalar readout at each momentum. -/
def factors (g : R → R) : List R → R
  | [] => 1
  | x::xs => g x*factors g xs

private theorem factors_mul (g h : R → R) (xs : List R) :
    factors (fun x => g x*h x) xs = factors g xs*factors h xs := by
  induction xs with
  | nil => simp [factors]
  | cons x xs ih => rw [factors,factors,factors,ih]; ring

/-- Sum over every choice of signed momenta. -/
def signSum : List R → (List R → R) → R
  | [],f => f []
  | x::xs,f => signSum xs (fun ys => f (x::ys)) + signSum xs (fun ys => f ((-x)::ys))

private theorem signs_const_mul (k : R) (xs : List R) (f : List R → R) :
    signSum xs (fun ys => k*f ys) = k*signSum xs f := by
  induction xs generalizing f with
  | nil => rfl
  | cons x xs ih => simp only [signSum,ih,mul_add]

private theorem signs_zero (xs : List R) : signSum xs (fun _ => (0:R)) = 0 := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp only [signSum,ih,add_zero]

private theorem signs_even_factors (g : R → R) (hg : ∀ x, g (-x) = g x) (xs : List R) (f : List R → R) :
    signSum xs (fun ys => factors g ys*f ys) = factors g xs*signSum xs f := by
  induction xs generalizing f with
  | nil => rfl
  | cons x xs ih =>
    simp only [signSum,factors,hg,mul_assoc,signs_const_mul,ih,mul_add]

/-- Squared product of pair differences on a list of signed momenta. -/
def pairWeight : List R → R
  | [] => 1
  | x::xs => factors (fun y => (x-y)^2) xs*pairWeight xs

/-- Second component of the total cubic phase vector. -/
def cubicSum (xs : List R) := (xs.map fun x => x^3).sum

/-- Contribution of one sign pattern to the cleared Hirota condition. -/
def term (P : R → R → R) (xs : List R) := P xs.sum (cubicSum xs)*pairWeight xs

/-- The polynomial reduced residual after clearing the KdV pair denominators. -/
def reduced (P : R → R → R) (xs : List R) := signSum xs (term P)

/-- The cleared residual is even in the added momentum. -/
theorem reduced_neg (P : R → R → R) (s : R) (xs : List R) :
    reduced P ((-s)::xs) = reduced P (s::xs) := by simp [reduced,signSum,add_comm]

private theorem zero_term (P : R → R → R) (xs : List R) :
    term P (0::xs) = factors (fun y => y^2) xs*term P xs := by
  simp only [term,pairWeight,cubicSum,List.map_cons,List.sum_cons,
    zero_pow (by norm_num : 3 ≠ 0),zero_add,zero_sub,even_two.neg_pow]
  ring

private theorem equal_term (P : R → R → R) (s : R) (xs : List R) : term P (s::s::xs) = 0 := by
  simp [term,pairWeight,factors]

private theorem opposite_term (P : R → R → R) (s : R) (xs : List R) :
    term P (s::(-s)::xs) =
      4*s^2*(factors (fun y => (s^2-y^2)^2) xs*term P xs) := by
  have hf : factors (fun y => (s^2-y^2)^2) xs =
      factors (fun y => (s-y)^2) xs*factors (fun y => (-s-y)^2) xs := by
    rw [← factors_mul]
    congr 1
    funext y
    ring
  simp only [term,cubicSum,List.map_cons,List.sum_cons,pairWeight,factors,hf]
  rw [show s+(-s+xs.sum) = xs.sum by ring,
    show s^3+((-s)^3+(xs.map fun x => x^3).sum) = (xs.map fun x => x^3).sum by ring]
  ring

/-- Soft reduction multiplies the shorter residual by twice the product
of the squared surviving momenta. -/
theorem reduced_zero (P : R → R → R) (xs : List R) :
    reduced P (0::xs) = 2*(xs.map (fun y => y^2)).prod*reduced P xs := by
  have hf : factors (fun y : R => y^2) xs = (xs.map (fun y => y^2)).prod := by
    induction xs with
    | nil => rfl
    | cons x xs ih => simp only [factors,List.map_cons,List.prod_cons,ih]
  simp only [reduced,signSum,neg_zero,zero_term,
    signs_even_factors (fun y : R => y^2) (fun x => even_two.neg_pow x),hf]
  ring

/-- Collision reduction has a double zero for every other momentum of the
same magnitude. It holds at every order and for every cofactor. -/
theorem reduced_collision (P : R → R → R) (s : R) (xs : List R) :
    reduced P (s::s::xs) =
      8*s^2*(xs.map (fun y => (s^2-y^2)^2)).prod*reduced P xs := by
  let g := fun y : R => (s^2-y^2)^2
  have hg (x : R) : g (-x) = g x := by simp [g]
  have hf : factors g xs = (xs.map g).prod := by
    induction xs with
    | nil => rfl
    | cons x xs ih => simp only [factors,List.map_cons,List.prod_cons,ih]
  have ho (ys : List R) : term P ((-s)::s::ys) = 4*s^2*(factors g ys*term P ys) := by
    simpa only [g,even_two.neg_pow,neg_neg] using opposite_term P (-s) ys
  have ho' (ys : List R) : term P (s::(-s)::ys) = 4*s^2*(factors g ys*term P ys) := opposite_term P s ys
  simp only [reduced,signSum,equal_term,signs_zero,ho,ho',signs_const_mul,signs_even_factors g hg,hf,g]
  ring

theorem factors_perm (g : R → R) {xs ys : List R} (h : xs.Perm ys) : factors g xs = factors g ys := by
  induction h with
  | nil => rfl
  | cons x _ ih => simp only [factors,ih]
  | swap x y l => simp only [factors]; ring
  | trans _ _ ih jh => exact ih.trans jh

theorem pairWeight_perm {xs ys : List R} (h : xs.Perm ys) : pairWeight xs = pairWeight ys := by
  induction h with
  | nil => rfl
  | cons x h ih => simp only [pairWeight,factors_perm _ h,ih]
  | swap x y l =>
    simp only [pairWeight,factors]
    rw [show (x-y)^2 = (y-x)^2 by ring]
    ring
  | trans _ _ ih jh => exact ih.trans jh

private theorem signSum_perm {xs ys : List R} (h : xs.Perm ys) (f : List R → R)
    (hf : ∀ {v w}, List.Perm v w → f v = f w) : signSum xs f = signSum ys f := by
  induction h generalizing f with
  | nil => rfl
  | cons x h ih =>
    simp only [signSum]
    exact congrArg₂ (·+·) (ih _ fun hh => hf (.cons x hh)) (ih _ fun hh => hf (.cons (-x) hh))
  | swap x y l =>
    have sw (s t : R) : signSum l (fun v => f (s::t::v)) = signSum l (fun v => f (t::s::v)) :=
      congrArg (signSum l) (funext fun v => hf (.swap t s v))
    simp only [signSum]
    rw [sw y x,sw y (-x),sw (-y) x,sw (-y) (-x)]
    abel
  | trans _ _ ih jh => exact (ih f hf).trans (jh f hf)

/-- Only the multiset of wave momenta matters for the reduced condition. -/
theorem reduced_perm (P : R → R → R) (xs ys : List R) :
    xs.Perm ys → reduced P xs = reduced P ys := fun h =>
  signSum_perm h _ fun H => by simp only [term,cubicSum,H.sum_eq,(H.map _).sum_eq,pairWeight_perm H]

/-- The soft and collision formulas also apply at repeated absolute values
of opposite sign. -/
theorem reduced_opposite (P : R → R → R) (s : R) (xs : List R) :
    reduced P ((-s)::s::xs) =
      8*s^2*(xs.map (fun y => (s^2-y^2)^2)).prod*reduced P xs := by
  rw [reduced_neg,reduced_collision]

private theorem pair_cancel (w : Weights) (a b : ℝ) :
    term (dispersion w) [a,b]+term (dispersion w) [a,-b] = 0 := by
  simp only [term,cubicSum,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero,
    pairWeight,factors,mul_one,sub_neg_eq_add,show (-b)^3 = -(b^3) by ring,← sub_eq_add_neg]
  rw [sum_symbol,difference_symbol]
  ring

/-- The two-wave condition remains exact at every singular or degenerate
momentum pair, in its division-free polynomial form. -/
theorem reduced_two (w : Weights) (a b : ℝ) : reduced (dispersion w) [a,b] = 0 := by
  change (term _ [a,b]+term _ [a,-b])+(term _ [-a,b]+term _ [-a,-b]) = 0
  rw [pair_cancel,pair_cancel,add_zero]

private theorem term_three (P : ℝ → ℝ → ℝ) (a b c : ℝ) :
    term P [a,b,c] = P (a+b+c) (a^3+b^3+c^3) * vandermonde a b c^2 := by
  simp only [term,cubicSum,pairWeight,factors,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,
    add_zero,mul_one,vandermonde,add_assoc]
  ring

/-- Shi's three-wave identity is the actual signed sum, with simultaneous
negation supplying the second copy of each relative sign pattern. -/
theorem reduced_three (w : Weights) (a b c : ℝ) : reduced (dispersion w) [a,b,c] = 0 := by
  let f := fun x y z => dispersion w (x+y+z) (x^3+y^3+z^3)*vandermonde x y z^2
  have rev (x y z : ℝ) : f (-x) (-y) (-z) = f x y z := by
    have hs : -x+-y+-z = -(x+y+z) := by ring
    have ht : (-x)^3+(-y)^3+(-z)^3 = -(x^3+y^3+z^3) := by ring
    unfold f
    rw [hs,ht]
    have he (u v : ℝ) : dispersion w (-u) (-v) = dispersion w u v := by unfold dispersion graph; ring
    rw [he]
    congr 1
    unfold vandermonde
    ring
  have h := threeWave_vanishes w 0 a b c
  change paritySum _ a b c = 0 at h
  simp only [mul_zero,pow_zero,one_mul,zero_add,pow_one,paritySum] at h
  change f a b c + f a (-b) (-c) + f (-a) b (-c) + f (-a) (-b) c = 0 at h
  simp only [reduced,signSum,term_three]
  change (f a b c+f a b (-c))+(f a (-b) c+f a (-b) (-c))+
      ((f (-a) b c+f (-a) b (-c))+(f (-a) (-b) c+f (-a) (-b) (-c))) = 0
  have h1 := rev a b c
  have h2 := rev a (-b) (-c)
  have h3 := rev (-a) b (-c)
  have h4 := rev (-a) (-b) c
  simp only [neg_neg] at h2 h3 h4
  linarith only [h,h1,h2,h3,h4]

#print axioms reduced_neg
#print axioms reduced_zero
#print axioms reduced_collision
#print axioms reduced_perm
#print axioms reduced_opposite
#print axioms reduced_two
#print axioms reduced_three
end WaveList
end GaloisForLFunctions.HTGeometry.DispersivePDE.CubicHierarchy
