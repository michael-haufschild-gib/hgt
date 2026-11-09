import GaloisForLFunctions.HTGeometry.MonicRootDiscriminant

/-!
# Discriminants and cross-resultants

For monic polynomials the formal degree in the second resultant argument
can be enlarged freely. Reduction by a multiple then factors the derivative
resultant, giving the exact square of the cross-resultant in the product
law. No separability or integral-domain assumption is required.
-/

noncomputable section
open Polynomial
namespace GaloisForLFunctions.HTGeometry
variable {R : Type*} [CommRing R]

/-- A monic first argument removes dependence on the padded second degree. -/
theorem monic_resultant_right_degree {f : R[X]} (hf : f.Monic)
    (g : R[X]) (n : ℕ) (hn : g.natDegree ≤ n) :
    resultant f g f.natDegree n = resultant f g := by
  conv_lhs => arg 4; rw [← Nat.add_sub_of_le hn]
  rw [resultant_add_right_deg _ _ _ _ _ le_rfl]
  simp only [coeff_natDegree, hf.leadingCoeff, one_pow, one_mul]

/-- The monic resultant is multiplicative without assumptions on the other arguments. -/
theorem monic_resultant_mul_right {f : R[X]} (hf : f.Monic) (g h : R[X]) :
    resultant f (g * h) = resultant f g * resultant f h := by
  rw [← monic_resultant_right_degree hf (g * h) _ natDegree_mul_le]
  exact resultant_mul_right f g h f.natDegree le_rfl

/-- Adding a multiple of a monic polynomial does not change its resultant. -/
theorem monic_resultant_add_mul {f : R[X]} (hf : f.Monic) (g h : R[X]) :
    resultant f (g + f * h) = resultant f g := by
  let n := max (g + f * h).natDegree (max g.natDegree (h.natDegree + f.natDegree))
  have ha : (g + f * h).natDegree ≤ n := le_max_left _ _
  have hb : g.natDegree ≤ n := (le_max_left _ _).trans (le_max_right _ _)
  have hc : h.natDegree + f.natDegree ≤ n := (le_max_right _ _).trans (le_max_right _ _)
  rw [← monic_resultant_right_degree hf _ n ha,
    ← monic_resultant_right_degree hf _ n hb]
  exact resultant_add_mul_right f g h f.natDegree n hc le_rfl

/-- The derivative resultant gives the signed discriminant, also for the monic constant one. -/
theorem monic_resultant_derivative {f : R[X]} (hf : f.Monic) :
    resultant f f.derivative = (-1) ^ (f.natDegree * (f.natDegree - 1) / 2) * f.discr := by
  by_cases hz : f.natDegree = 0
  · obtain rfl := eq_one_of_monic_natDegree_zero hf hz
    have hd : (1 : R[X]).discr = 1 := Polynomial.discr_C 1
    simp only [derivative_one, natDegree_one, Nat.zero_mul, Nat.zero_div,
      pow_zero, hd, mul_one, resultant_one_left]
  have h := resultant_deriv (f := f)
    (natDegree_pos_iff_degree_pos.mp (Nat.pos_of_ne_zero hz))
  rw [monic_resultant_right_degree hf _ _ (natDegree_derivative_le f),
    hf.leadingCoeff, mul_one] at h
  exact h

private theorem discriminantExponent_add (m n : ℕ) :
    (m + n) * (m + n - 1) / 2 =
      m * (m - 1) / 2 + n * (n - 1) / 2 + m * n := by
  have h : (m + n) * (m + n - 1) =
      m * (m - 1) + n * (n - 1) + (m * n) * 2 := by
    cases m with
    | zero => simp
    | succ m =>
      cases n with
      | zero => simp
      | succ n =>
        have hs : (m + 1 + (n + 1)) - 1 = m + n + 1 := by omega
        simp only [Nat.add_sub_cancel] at *
        rw [hs]
        ring
  have hm := Nat.div_mul_cancel m.even_mul_pred_self.two_dvd
  have hn := Nat.div_mul_cancel n.even_mul_pred_self.two_dvd
  have hmn := Nat.div_mul_cancel (m + n).even_mul_pred_self.two_dvd
  omega

/-- The product discriminant retains the exact square of the cross-resultant over every ring. -/
theorem discr_mul_of_monic {f g : R[X]} (hf : f.Monic) (hg : g.Monic) :
    (f * g).discr = f.discr * g.discr * resultant f g ^ 2 := by
  have hn : (f * g).natDegree = f.natDegree + g.natDegree := hf.natDegree_mul hg
  have hleft : resultant f (f * g).derivative =
      resultant f f.derivative * resultant f g := by
    rw [derivative_mul, monic_resultant_add_mul hf,
      monic_resultant_mul_right hf]
  have hright : resultant g (f * g).derivative =
      resultant g g.derivative * resultant g f := by
    rw [mul_comm f g, derivative_mul, monic_resultant_add_mul hg,
      monic_resultant_mul_right hg]
  have h := resultant_mul_left f g (f * g).derivative (f * g).derivative.natDegree le_rfl
  rw [← hn, monic_resultant_derivative (hf.mul hg), hleft, hright,
    monic_resultant_derivative hf, monic_resultant_derivative hg,
    resultant_comm g f, hn, discriminantExponent_add, pow_add, pow_add] at h
  rw [Nat.mul_comm g.natDegree f.natDegree] at h
  let s : R := (-1) ^ (f.natDegree * (f.natDegree - 1) / 2) *
    (-1) ^ (g.natDegree * (g.natDegree - 1) / 2) *
    (-1) ^ (f.natDegree * g.natDegree)
  have he : s * (f * g).discr = s * (f.discr * g.discr * resultant f g ^ 2) := by
    dsimp only [s]
    convert h using 1; ring
  have hsquare (k : ℕ) : ((-1 : R) ^ k) ^ 2 = 1 := by
    rw [← pow_mul, Nat.mul_comm k 2, pow_mul, neg_one_sq, one_pow]
  have hsq : s ^ 2 = 1 := by
    dsimp only [s]
    rw [mul_pow, mul_pow, hsquare, hsquare, hsquare, one_mul, one_mul]
  have hh := congrArg (fun a => s * a) he
  simpa only [← mul_assoc, ← pow_two, hsq, one_mul] using hh

/-- Over a field, a monic polynomial has zero discriminant exactly when it is inseparable. -/
theorem monic_discr_eq_zero_iff_not_separable {F : Type*} [Field F]
    {f : F[X]} (hf : f.Monic) : f.discr = 0 ↔ ¬ f.Separable := by
  have h := Polynomial.resultant_eq_zero_iff (f := f) (g := f.derivative)
  rw [monic_resultant_derivative hf] at h
  have hs : (-1 : F) ^ (f.natDegree * (f.natDegree - 1) / 2) ≠ 0 :=
    pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero)
  have hn : f ≠ 0 ∨ f.derivative ≠ 0 := Or.inl hf.ne_zero
  simpa only [mul_eq_zero, hs, false_or, hn, true_and,
    Polynomial.Separable] using h

/-- The cross-resultants of a list of factors, keeping their actual coefficient values. -/
def listCrossResultant : List R[X] → R
  | [] => 1
  | f :: s => resultant f s.prod * listCrossResultant s

/-- A monic resultant against a product is the product of its pairwise resultants. -/
theorem monic_resultant_list_prod {f : R[X]} (hf : f.Monic) (s : List R[X]) :
    resultant f s.prod = (s.map (fun g => resultant f g)).prod := by
  induction s with
  | nil => simp only [List.prod_nil, List.map_nil, resultant_one_right,
      natDegree_one, pow_zero]
  | cons g s ih =>
    rw [List.prod_cons, monic_resultant_mul_right hf, ih, List.map_cons, List.prod_cons]

private theorem list_prod_monic (s : List R[X]) (hs : ∀ f ∈ s, f.Monic) : s.prod.Monic := by
  induction s with
  | nil => exact monic_one
  | cons f s ih =>
    exact (hs f (List.mem_cons_self)).mul
      (ih (fun g hg => hs g (List.mem_cons_of_mem f hg)))

/-- The full discriminant is the product of factor discriminants times one explicit square. -/
theorem discr_list_prod_of_monic (s : List R[X]) (hs : ∀ f ∈ s, f.Monic) :
    s.prod.discr = (s.map Polynomial.discr).prod * listCrossResultant s ^ 2 := by
  induction s with
  | nil =>
    simp only [List.prod_nil, List.map_nil, listCrossResultant, one_pow, mul_one]
    exact Polynomial.discr_C 1
  | cons f s ih =>
    have hf := hs f List.mem_cons_self
    have ht : ∀ g ∈ s, g.Monic := fun g hg => hs g (List.mem_cons_of_mem f hg)
    rw [List.prod_cons, discr_mul_of_monic hf (list_prod_monic s ht), ih ht,
      List.map_cons, List.prod_cons, listCrossResultant]
    ring

#print axioms monic_resultant_right_degree
#print axioms monic_resultant_mul_right
#print axioms monic_resultant_add_mul
#print axioms monic_resultant_derivative
#print axioms discr_mul_of_monic
#print axioms monic_discr_eq_zero_iff_not_separable
#print axioms monic_resultant_list_prod
#print axioms discr_list_prod_of_monic
end GaloisForLFunctions.HTGeometry
