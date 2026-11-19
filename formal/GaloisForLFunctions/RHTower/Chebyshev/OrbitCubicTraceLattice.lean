import GaloisForLFunctions.RHTower.Chebyshev.OrbitCubicTraceMoments
import GaloisForLFunctions.RHTower.Chebyshev.OrbitCubicIntegralOrder

/-!
# An orthonormal integral basis for the positive orbit-cubic trace form

For the weight X(X−1)/f'(X), the three functions 1, 1/X and 1/(X−1)
are orthonormal on the roots. At integral parameters both reciprocals
are integral polynomials and the basis change is unimodular. This gives
three totally positive trace-one squares and a triangle of further
trace-one elements, the input counted in Oller, Proposition 4.1.
-/

noncomputable section
namespace RHTower.OrbitCubic

def weighted (a b c : ℝ) (f : ℝ → ℝ) :=
  weight a b c*f a + weight b c a*f b + weight c a b*f c

/-- Coordinates relative to 1, the reciprocal root and its reciprocal translate. -/
def traceBasis (u v w x : ℝ) := u+v*x⁻¹+w*(x-1)⁻¹

private theorem root_inverses {m x : ℝ} (h : binary (m-1/2) x 1 = 0) :
    x ≠ 0 ∧ x-1 ≠ 0 ∧ x⁻¹ = 2-(x-m)*(x-1) ∧ (x-1)⁻¹ = (x-m)*x-2 := by
  rw [arrowhead_secular] at h
  have h0 : x ≠ 0 := by rintro rfl; norm_num at h
  have h1 : x-1 ≠ 0 := by intro he; rw [sub_eq_zero.mp he] at h; norm_num at h
  refine ⟨h0,h1,?_,?_⟩
  · rw [inv_eq_one_div,eq_comm,eq_div_iff h0]
    linear_combination -h
  · rw [inv_eq_one_div,eq_comm,eq_div_iff h1]
    linear_combination h

private def centeredQuadratic (m A B C x : ℝ) := A+B*(x-m)+C*(x-m)^2

private theorem basis_quadratic {m x : ℝ} (h : binary (m-1/2) x 1 = 0) (u v w : ℝ) :
    traceBasis u v w x = centeredQuadratic m (u-2*(w-v)) (v+m*(w-v)) (w-v) x := by
  obtain ⟨_,_,h0,h1⟩ := root_inverses h
  rw [traceBasis,h0,h1]
  unfold centeredQuadratic
  ring

private theorem quadratic_energy (m a b c A B C : ℝ) :
    weighted a b c (fun x => (centeredQuadratic m A B C x)^2) =
      A^2*moment a b c m 0+2*A*B*moment a b c m 1+(B^2+2*A*C)*moment a b c m 2+
        2*B*C*moment a b c m 3+C^2*moment a b c m 4 := by
  unfold weighted centeredQuadratic moment
  ring

/-- The normalized derivative residues give the Euclidean form on all three
reciprocal coordinates. The first coordinate is the exact weighted trace. -/
theorem exists_orthonormal_trace_basis (m : ℝ) :
    ∃ a b c : ℝ, binary (m-1/2) a 1 = 0 ∧ binary (m-1/2) b 1 = 0 ∧
      binary (m-1/2) c 1 = 0 ∧ 0 < weight a b c ∧ 0 < weight b c a ∧ 0 < weight c a b ∧
      ∀ u v w : ℝ, weighted a b c (traceBasis u v w) = u ∧
        weighted a b c (fun x => (traceBasis u v w x)^2) = u^2+v^2+w^2 := by
  obtain ⟨a,b,c,ha,hb,hc,pa,pb,pc,hM⟩ := centered_trace_invariants (m-1/2)
  simp only [sub_add_cancel] at hM
  obtain ⟨M0,M1,M2,M3,M4,_⟩ := hM
  refine ⟨a,b,c,ha,hb,hc,pa,pb,pc,fun u v w => ?_⟩
  let A := u-2*(w-v)
  let B := v+m*(w-v)
  let C := w-v
  have hfirst : weighted a b c (traceBasis u v w) =
      A*moment a b c m 0+B*moment a b c m 1+C*moment a b c m 2 := by
    unfold weighted moment
    rw [basis_quadratic ha,basis_quadratic hb,basis_quadratic hc]
    unfold centeredQuadratic
    dsimp only [A,B,C]
    ring
  have hsecond : weighted a b c (fun x => (traceBasis u v w x)^2) =
      weighted a b c (fun x => (centeredQuadratic m A B C x)^2) := by
    simp only [weighted,basis_quadratic ha,basis_quadratic hb,basis_quadratic hc,A,B,C]
  rw [hfirst,hsecond,quadratic_energy,M0,M1,M2,M3,M4]
  dsimp only [A,B,C]
  constructor <;> ring

/-- The centered power-basis coefficients map integrally and invertibly to
the orthonormal basis. In particular the isometry has no lattice index. -/
def traceLatticeEquiv (m : ℤ) : (ℤ × ℤ × ℤ) ≃ₗ[ℤ] (ℤ × ℤ × ℤ) where
  toFun p := (p.1+2*p.2.2,p.2.1-m*p.2.2,p.2.1+(1-m)*p.2.2)
  invFun z := (z.1-2*(z.2.2-z.2.1),z.2.1+m*(z.2.2-z.2.1),z.2.2-z.2.1)
  left_inv := by rintro ⟨A,B,C⟩; ext <;> dsimp <;> ring
  right_inv := by rintro ⟨u,v,w⟩; ext <;> dsimp <;> ring
  map_add' := by rintro ⟨A,B,C⟩ ⟨D,E,F⟩; ext <;> dsimp <;> ring
  map_smul' := by rintro k ⟨A,B,C⟩; ext <;> simp <;> ring

/-- At any root the squares of the two extra basis units have linear
coordinates. Their traces are both one. -/
theorem reciprocal_square_coordinates (m : ℝ) :
    ∀ x, binary (m-1/2) x 1 = 0 →
      x⁻¹^2 = traceBasis 1 (1-m) (-1) x ∧
      (x-1)⁻¹^2 = traceBasis 1 1 (-m) x := by
  intro x h
  obtain ⟨_,_,hU,hV⟩ := root_inverses h
  rw [arrowhead_secular,sub_add_cancel] at h
  obtain ⟨_,_,_,_,hu,hv⟩ := reciprocal_polynomial_table m x h
  rw [traceBasis,traceBasis,hU,hV]
  exact ⟨by linear_combination hu,by linear_combination hv⟩

private theorem cone_strict (x : ℝ) {b c : ℝ}
    (hb : 0 ≤ b) (hc : 0 ≤ c) (hs : b+c < 1) :
    0 < (1-b-c)+b*x⁻¹^2+c*(x-1)⁻¹^2 := by
  linarith only [hs,mul_nonneg hb (sq_nonneg x⁻¹),mul_nonneg hc (sq_nonneg (x-1)⁻¹)]

/-- The lattice triangle lies strictly inside the positive cone at all three embeddings. -/
theorem positive_triangle {m u v x : ℝ} (hm : 2 ≤ m) (hu : 0 ≤ u) (hv : 1 ≤ v)
    (huv : u+v ≤ m-1) (hx : binary (m-1/2) x 1 = 0) : 0 < traceBasis 1 (-u) (-v) x := by
  let d := m*(m-1)+1
  have hd : 0 < d := by dsimp [d]; nlinarith only [hm,sq_nonneg (m-1)]
  let B := (m*u+v)/d
  let C := ((m-1)*v-u)/d
  have hB : 0 ≤ B := div_nonneg (add_nonneg (mul_nonneg (by linarith) hu) (by linarith)) hd.le
  have hC : 0 ≤ C := by
    apply div_nonneg _ hd.le
    nlinarith only [huv,hv,mul_nonneg (sub_nonneg.mpr (show 1 ≤ m by linarith)) (sub_nonneg.mpr hv)]
  have hsum : B+C < 1 := by
    dsimp only [B,C]
    rw [← add_div,div_lt_one hd]
    dsimp only [d]
    nlinarith only [hu,mul_nonneg (by linarith only [hm] : 0 ≤ m) (sub_nonneg.mpr huv)]
  have h := cone_strict x hB hC hsum
  obtain ⟨hU,hV⟩ := reciprocal_square_coordinates m x hx
  rw [hU,hV] at h
  convert h using 1
  unfold traceBasis
  dsimp only [B,C]
  field_simp [hd.ne']
  dsimp only [d]
  ring

/-- A triangular array of integral coordinates gives strictly positive
trace-one elements. Row i has i+1 distinct coefficient pairs. -/
theorem triangular_trace_one (n : ℕ) :
    let m : ℝ := n+2
    ∃ a b c : ℝ, binary (m-1/2) a 1 = 0 ∧ binary (m-1/2) b 1 = 0 ∧ binary (m-1/2) c 1 = 0 ∧
      (∀ u v w, weighted a b c (fun x => (traceBasis u v w x)^2) = u^2+v^2+w^2) ∧
      ∀ i : Fin (n+1), ∀ j : Fin (i.val+1),
        let u : ℝ := j.val
        let v : ℝ := i.val+1-u
        let L := traceBasis 1 (-u) (-v)
        0 < L a ∧ 0 < L b ∧ 0 < L c ∧ weighted a b c L = 1 := by
  intro m
  obtain ⟨a,b,c,ha,hb,hc,_,_,_,ht⟩ := exists_orthonormal_trace_basis m
  refine ⟨a,b,c,ha,hb,hc,fun u v w => (ht u v w).2,fun i j => ?_⟩
  intro u v L
  have hm : 2 ≤ m := by dsimp [m]; linarith only [Nat.cast_nonneg (α := ℝ) n]
  have hu : 0 ≤ u := Nat.cast_nonneg _
  have hv : 1 ≤ v := by
    have hj : (j.val : ℝ) ≤ (i.val : ℝ) := by exact_mod_cast (show j.val ≤ i.val by omega)
    dsimp [u,v]; linarith only [hj]
  have huv : u+v ≤ m-1 := by
    have hi : (i.val : ℝ) ≤ (n:ℝ) := by exact_mod_cast (show i.val ≤ n by omega)
    dsimp [u,v,m]; linarith only [hi]
  exact ⟨positive_triangle hm hu hv huv ha,positive_triangle hm hu hv huv hb,
    positive_triangle hm hu hv huv hc,(ht _ _ _).1⟩

open Polynomial

/-- Integral polynomials restrict on all three roots to integral reciprocal
coordinates. Multiplication by the generator sends (A,B,C) to
(mA+B+C,A,A+C). -/
theorem integral_polynomial_coordinates (m : ℤ) (P : ℤ[X]) :
    ∃ A B C : ℤ, ∀ x : ℝ, binary ((m:ℝ)-1/2) x 1 = 0 →
      P.eval₂ (Int.castRingHom ℝ) x = traceBasis A B C x := by
  induction P using Polynomial.induction_on with
  | C a =>
    exact ⟨a,0,0,fun x _ => by rw [Polynomial.eval₂_C]; simp [traceBasis]⟩
  | add P Q ihP ihQ =>
    obtain ⟨A,B,C,hP⟩ := ihP
    obtain ⟨D,E,F,hQ⟩ := ihQ
    refine ⟨A+D,B+E,C+F,fun x hx => ?_⟩
    rw [Polynomial.eval₂_add,hP x hx,hQ x hx]
    push_cast
    unfold traceBasis
    ring
  | monomial n a ih =>
    obtain ⟨A,B,C,h⟩ := ih
    refine ⟨m*A+B+C,A,A+C,fun x hx => ?_⟩
    rw [pow_succ,← mul_assoc,Polynomial.eval₂_mul,Polynomial.eval₂_X,h x hx]
    obtain ⟨h0,h1,hU,hV⟩ := root_inverses hx
    have he : x = (m:ℝ)+x⁻¹+(x-1)⁻¹ := by rw [hU,hV]; ring
    have hu := mul_inv_cancel₀ h0
    have hv := mul_inv_cancel₀ h1
    unfold traceBasis
    push_cast
    linear_combination (A:ℝ)*he + (B:ℝ)*hu + (C:ℝ)*hv

/-- A single integral quadratic realizes each lattice element on all roots. -/
def coordinatePolynomial (m A B D : ℤ) : ℤ[X] :=
  C A + C B*(2-(X-C m)*(X-1))+C D*((X-C m)*X-2)

theorem coordinatePolynomial_evaluation (m A B D : ℤ) :
    ∀ x : ℝ, binary ((m:ℝ)-1/2) x 1 = 0 →
      (coordinatePolynomial m A B D).eval₂ (Int.castRingHom ℝ) x = traceBasis A B D x := by
  intro x hx
  obtain ⟨_,_,hU,hV⟩ := root_inverses hx
  simp only [coordinatePolynomial,Polynomial.eval₂_add,Polynomial.eval₂_mul,Polynomial.eval₂_sub,
    Polynomial.eval₂_C,Polynomial.eval₂_X]
  simp [traceBasis,hU,hV]

#print axioms exists_orthonormal_trace_basis
#print axioms traceLatticeEquiv
#print axioms reciprocal_square_coordinates
#print axioms triangular_trace_one
#print axioms integral_polynomial_coordinates
#print axioms coordinatePolynomial_evaluation
end RHTower.OrbitCubic
