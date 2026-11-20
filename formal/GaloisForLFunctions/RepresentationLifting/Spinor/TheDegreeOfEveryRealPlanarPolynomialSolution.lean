import GaloisForLFunctions.RepresentationLifting.Spinor.TheCartesianEquationOfARealPlanarHomogeneousPolynomial
import GaloisForLFunctions.HTGeometry.MvPolynomialTopHomogeneousComponent

/-!
# Degree of every real planar polynomial solution

The degree-(3d−4) component of the cleared p-Laplacian of a polynomial
of degree d comes entirely from its degree-d part. Thus planar homogeneous
rigidity excludes nonlinear real polynomial solutions of arbitrary shape.
-/

noncomputable section
open MvPolynomial Finset
open GaloisForLFunctions.ArithmeticHarmonicAnalysis
namespace GaloisForLFunctions.RepresentationLifting.Spinor

section Grading
variable {σ R : Type*} [CommSemiring R]
local notation "Poly" => MvPolynomial σ R

/-- Above the indicated degree the coefficients vanish; at that degree
they agree with the indicated homogeneous polynomial. -/
private structure TopPart (n : ℕ) (P Q : Poly) : Prop where
  hom : Q.IsHomogeneous n
  high : ∀ m : σ →₀ ℕ, n < m.degree → P.coeff m = 0
  edge : ∀ m : σ →₀ ℕ, m.degree = n → P.coeff m = Q.coeff m

private theorem TopPart.totalDegree_le {n : ℕ} {P Q : Poly} (h : TopPart n P Q) : P.totalDegree ≤ n :=
  Finset.sup_le fun m hm => le_of_not_gt fun hl => mem_support_iff.mp hm (h.high m hl)

private theorem TopPart.component {n : ℕ} {P Q : Poly} (h : TopPart n P Q) :
    homogeneousComponent n P = Q := by
  rw [←homogeneousComponent_eq_self h.hom]
  ext m
  simp only [coeff_homogeneousComponent]
  split
  · exact h.edge m ‹_›
  · rfl

private theorem top_part_component {n : ℕ} (P : Poly) (h : P.totalDegree ≤ n) :
    TopPart n P (homogeneousComponent n P) :=
  ⟨homogeneousComponent_isHomogeneous _ _,fun _ hm => coeff_eq_zero_of_totalDegree_lt (h.trans_lt hm),
    fun m hm => by rw [coeff_homogeneousComponent,if_pos hm]⟩

private theorem TopPart.add {n : ℕ} {P Q U V : Poly} (h : TopPart n P Q) (k : TopPart n U V) :
    TopPart n (P+U) (Q+V) :=
  ⟨h.hom.add k.hom,fun m hm => by rw [coeff_add,h.high m hm,k.high m hm,zero_add],
    fun m hm => by rw [coeff_add,coeff_add,h.edge m hm,k.edge m hm]⟩

private theorem TopPart.C_mul {n : ℕ} {P Q : Poly} (h : TopPart n P Q) (c : R) :
    TopPart n (C c*P) (C c*Q) :=
  ⟨h.hom.C_mul _,fun m hm => by rw [coeff_C_mul,h.high m hm,mul_zero],
    fun m hm => by rw [coeff_C_mul,coeff_C_mul,h.edge m hm]⟩

private theorem TopPart.map {S : Type*} [CommSemiring S] {n : ℕ} {P Q : Poly}
    (h : TopPart n P Q) (f : R →+* S) : TopPart n (MvPolynomial.map f P) (MvPolynomial.map f Q) :=
  ⟨h.hom.map f,fun m hm => by rw [coeff_map,h.high m hm,map_zero],
    fun m hm => by rw [coeff_map,coeff_map,h.edge m hm]⟩

private theorem TopPart.mul {a b : ℕ} {P Q U V : Poly} (h : TopPart a P Q) (k : TopPart b U V) :
    TopPart (a+b) (P*U) (Q*V) := by
  classical
  have hd {s t m : σ →₀ ℕ} (hst : (s,t) ∈ antidiagonal m) : s.degree+t.degree=m.degree := by
    rw [←map_add,mem_antidiagonal.mp hst]
  refine ⟨h.hom.mul k.hom,?_,?_⟩
  · intro m hm
    rw [coeff_mul]
    refine sum_eq_zero fun ⟨s,t⟩ hst => ?_
    have hs := hd hst
    by_cases ha : a < s.degree
    · rw [h.high s ha,zero_mul]
    · rw [k.high t (by omega),mul_zero]
  · intro m hm
    rw [coeff_mul,coeff_mul]
    refine sum_congr rfl fun ⟨s,t⟩ hst => ?_
    have hs := hd hst
    by_cases ha : a < s.degree
    · rw [h.high s ha,coeff_eq_zero_of_totalDegree_lt (h.hom.totalDegree_le.trans_lt ha),zero_mul,zero_mul]
    by_cases hb : b < t.degree
    · rw [k.high t hb,coeff_eq_zero_of_totalDegree_lt (k.hom.totalDegree_le.trans_lt hb),mul_zero,mul_zero]
    rw [h.edge s (by omega),k.edge t (by omega)]

private theorem TopPart.partial {n : ℕ} {P Q : Poly} (h : TopPart (n+1) P Q) (i : σ) :
    TopPart n (pderiv i P) (pderiv i Q) := by
  have hh := h.hom.pderiv (i:=i)
  refine ⟨by simpa only [Nat.add_sub_cancel] using hh,?_,?_⟩
  · intro m hm
    rw [coeff_pderiv,h.high _ (by rw [map_add,Finsupp.degree_single]; omega),zero_mul]
  · intro m hm
    rw [coeff_pderiv,coeff_pderiv,h.edge _ (by rw [map_add,Finsupp.degree_single,hm])]

private theorem top_part_sum {ι : Type*} (s : Finset ι) {n : ℕ} {P Q : ι → Poly}
    (h : ∀ i, TopPart n (P i) (Q i)) : TopPart n (∑ i ∈ s, P i) (∑ i ∈ s, Q i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [sum_empty]
    exact ⟨isHomogeneous_zero _ _ _,fun _ _ => coeff_zero _, fun _ _ => rfl⟩
  | @insert i s hi ih =>
    simp only [sum_insert hi]
    exact (h i).add ih

end Grading

/-- Extraction of the leading nonlinear symbol in any finite dimension.
At input degree d+2 the possible highest output degree is 3d+2. -/
theorem highest_degree_of_cleared_p_laplacian {σ : Type*} [Fintype σ] [DecidableEq σ]
    (p : ℂ) (P : MvPolynomial σ ℂ) (d : ℕ) (hP : P.totalDegree ≤ d+2) :
    homogeneousComponent (3*d+2) (clearedPLaplacian p P) =
      clearedPLaplacian p (homogeneousComponent (d+2) P) := by
  let Q := homogeneousComponent (d+2) P
  have base : TopPart ((d+1)+1) P Q := top_part_component _ hP
  have grad (i : σ) := base.partial i
  have hess (i j : σ) := (grad j).partial i
  have lap := top_part_sum univ (fun i : σ => hess i i)
  have norm := top_part_sum univ (fun i : σ => (grad i).mul (grad i))
  have inf := top_part_sum univ (fun i : σ => top_part_sum univ (fun j : σ =>
    ((grad i).mul (grad j)).mul (hess i j)))
  have hs := ((norm.mul lap).add (inf.C_mul (p-2))).component
  simpa only [Q,clearedPLaplacian,euclideanPolynomialLaplacian,infinityPolynomial,sq,
    show (d+1+(d+1))+d=3*d+2 by omega] using hs

/-- For every nonlinear elliptic exponent, all real Cartesian polynomial
solutions in the plane have degree at most one, and every affine form solves
the cleared equation. -/
theorem real_planar_polynomial_p_laplacian_iff_affine {p : ℝ} (hp : 1<p) (hp₂ : p≠2)
    (P : MvPolynomial (Fin 2) ℝ) :
    clearedPLaplacian (p:ℂ) (MvPolynomial.map Complex.ofRealHom P)=0 ↔ P.totalDegree≤1 := by
  let Q := MvPolynomial.map Complex.ofRealHom P
  constructor
  · intro hzero
    by_contra! hdeg
    let d := P.totalDegree-2
    have hD : d+2=P.totalDegree := by dsimp only [d]; omega
    have hP : P≠0 := by rintro rfl; simpa using hdeg
    let H := homogeneousComponent (d+2) P
    have hH : H.IsHomogeneous (d+2) := homogeneousComponent_isHomogeneous _ _
    have htop : TopPart (d+2) Q (MvPolynomial.map Complex.ofRealHom H) :=
      (top_part_component P hD.ge).map _
    have hs := highest_degree_of_cleared_p_laplacian (p:ℂ) Q d
      htop.totalDegree_le
    change clearedPLaplacian (p:ℂ) Q=0 at hzero
    rw [hzero,map_zero,htop.component] at hs
    have hvan := (real_homogeneous_cartesian_p_laplacian (by omega : 2≤d+2) H hH hp hp₂).mp hs.symm
    exact HTGeometry.homogeneousComponent_totalDegree_ne_zero hP (by simpa only [H,hD] using hvan)
  · intro hdeg
    have hh (i j : Fin 2) : pderiv i (pderiv j Q)=0 := by
      ext m
      have hlarge : P.totalDegree < (m+Finsupp.single i 1+Finsupp.single j 1).degree := by
        rw [map_add,map_add,Finsupp.degree_single,Finsupp.degree_single]
        omega
      simp only [coeff_pderiv,Q,coeff_map,coeff_eq_zero_of_totalDegree_lt hlarge,map_zero,zero_mul,coeff_zero]
    change clearedPLaplacian (p:ℂ) Q=0
    simp only [clearedPLaplacian,euclideanPolynomialLaplacian,infinityPolynomial,hh,mul_zero,sum_const_zero,add_zero]

#print axioms highest_degree_of_cleared_p_laplacian
#print axioms real_planar_polynomial_p_laplacian_iff_affine

end GaloisForLFunctions.RepresentationLifting.Spinor
