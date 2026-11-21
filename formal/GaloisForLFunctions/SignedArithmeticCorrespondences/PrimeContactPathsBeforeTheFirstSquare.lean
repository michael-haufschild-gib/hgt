import GaloisForLFunctions.SignedArithmeticCorrespondences.ThePathsInAFourfoldWeilComb
import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
import Mathlib.LinearAlgebra.Matrix.Charpoly.Eigs
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff

/-!
# Prime contact paths before the first square ratio

In the integer interval (N,B] with B < 4(N+1), only doubling and
tripling can give a contact. A triple starting at m belongs to a
three-site path when m is odd and to a four-site path when m is
even. The remaining doubles are isolated edges.
-/
noncomputable section
open Finset ArithmeticFunction
open scoped Classical ArithmeticFunction.vonMangoldt
open GaloisForLFunctions.HodgeTheoryOfAFixedPart
namespace GaloisForLFunctions.SignedArithmeticCorrespondences

/-- Admissible path labels for arbitrary integer endpoints. -/
def FourfoldPath.inWindow (N B : ℕ) : FourfoldPath → Prop
  | .pair a => N < a ∧ 2*a ≤ B ∧ B < 3*a ∧ (2*a ≤ 3*N ∨ a%3 ≠ 0)
  | .triple b => N < b ∧ 3*b ≤ B ∧ b%2=1
  | .quad i => N < 2*i ∧ 6*i ≤ B

/-- Increasingly oriented edges of a single path. -/
def FourfoldPath.hasEdge : FourfoldPath → ℕ → ℕ → Prop
  | .pair a,x,y => x=a ∧ y=2*a
  | .triple b,x,y => x=b ∧ (y=2*b ∨ y=3*b)
  | .quad i,x,y => (x=2*i ∧ (y=4*i ∨ y=6*i)) ∨ (x=3*i ∧ y=6*i)

private theorem edge_sites {u : FourfoldPath} {x y : ℕ} (edge : u.hasEdge x y) :
    x ∈ u.sites ∧ y ∈ u.sites := by
  cases u <;> simp only [FourfoldPath.hasEdge,FourfoldPath.sites,mem_insert,mem_singleton] at * <;> omega

/-- Distinct mixed-band components are disjoint even at unaligned cutoffs. -/
theorem short_contact_paths_disjoint {N B : ℕ} (short : B < 4*(N+1)) {u v : FourfoldPath}
    (hu : u.inWindow N B) (hv : v.inWindow N B) (ne : u ≠ v) : Disjoint u.sites v.sites := by
  apply disjoint_left.mpr
  intro n hn hm
  cases u <;> cases v <;>
    simp only [FourfoldPath.inWindow,FourfoldPath.sites,mem_insert,mem_singleton] at hu hv hn hm <;>
    first | (apply ne;congr 1 <;> omega) | omega

private theorem label_for_edge {N B x y : ℕ} (lo : N < x) (hi : y ≤ B)
    (step : y=2*x ∨ y=3*x) : ∃ u : FourfoldPath,u.inWindow N B ∧ u.hasEdge x y := by
  by_cases triple : 3*x ≤ B
  · by_cases odd : x%2=1
    · exact ⟨.triple x,⟨lo,triple,odd⟩,rfl,step⟩
    · refine ⟨.quad (x/2),?_,?_⟩ <;> simp only [FourfoldPath.inWindow,FourfoldPath.hasEdge] <;> omega
  · have twice : y=2*x := by omega
    by_cases lone : 2*x ≤ 3*N ∨ x%3 ≠ 0
    · exact ⟨.pair x,⟨lo,by omega,by omega,lone⟩,rfl,twice⟩
    · refine ⟨.quad (x/3),?_,?_⟩ <;> simp only [FourfoldPath.inWindow,FourfoldPath.hasEdge] <;> omega

/-- Every divisibility contact has exactly one path label. Every edge
of an admissible label is a doubling or a tripling. -/
theorem short_contact_path_classification {N B x y : ℕ} (short : B < 4*(N+1))
    (lo : N < x) (xy : x < y) (hi : y ≤ B) :
    x ∣ y ↔ ∃! u : FourfoldPath,u.inWindow N B ∧ u.hasEdge x y := by
  constructor
  · rintro ⟨k,rfl⟩
    have kl : 1 < k := Nat.lt_of_mul_lt_mul_left (by simpa only [Nat.mul_one] using xy : x*1 < x*k)
    have ku : k < 4 := Nat.lt_of_mul_lt_mul_left (show x*k < x*4 by
      rw [Nat.mul_comm x 4];exact hi.trans_lt (short.trans_le (Nat.mul_le_mul_left 4 lo)))
    have step : x*k=2*x ∨ x*k=3*x := by
      rcases (show k=2 ∨ k=3 by omega) with rfl|rfl
      · exact Or.inl (Nat.mul_comm ..)
      · exact Or.inr (Nat.mul_comm ..)
    obtain ⟨u,hu,edge⟩ := label_for_edge lo hi step
    refine ⟨u,⟨hu,edge⟩,?_⟩
    rintro v ⟨hv,other⟩
    by_contra ne
    exact disjoint_left.mp (short_contact_paths_disjoint short hv hu ne) (edge_sites other).1 (edge_sites edge).1
  · rintro ⟨u,⟨_,h⟩,_⟩
    have step : y=2*x ∨ y=3*x := by
      cases u <;> simp only [FourfoldPath.hasEdge] at h <;> omega
    rcases step with rfl|rfl <;> exact dvd_mul_left .. 

/-- The actual Mangoldt edge weight is log 2 or log 3 according to its
dilation. All other off-diagonal entries in this band are zero. -/
theorem short_mangoldt_contact_entry {N B x y : ℕ} (short : B < 4*(N+1))
    (lo : N < x) (xy : x < y) (hi : y ≤ B) :
    contactW vonMangoldt x y = if y=2*x then Real.log 2 else if y=3*x then Real.log 3 else 0 := by
  have xp : 0 < x := (Nat.zero_le _).trans_lt lo
  have rev : ¬y ∣ x := fun d => xy.not_ge (Nat.le_of_dvd xp d)
  rw [contactW,if_neg rev,add_zero]
  by_cases dv : x ∣ y
  · obtain ⟨u,⟨_,h⟩,_⟩ := (short_contact_path_classification short lo xy hi).mp dv
    have step : y=2*x ∨ y=3*x := by cases u <;> simp only [FourfoldPath.hasEdge] at h <;> omega
    rw [if_pos dv]
    rcases step with rfl|rfl
    · simp [Nat.mul_div_cancel _ xp,vonMangoldt_apply_prime Nat.prime_two]
    · simp [show 3*x ≠ 2*x by omega,Nat.mul_div_cancel _ xp,vonMangoldt_apply_prime Nat.prime_three]
  · have absent (d : ℕ) : y ≠ d*x := fun e => dv (by rw [e];exact dvd_mul_left ..)
    rw [if_neg dv,if_neg (absent 2),if_neg (absent 3)]

private abbrev entry := contactW vonMangoldt

/-- Rectangular incidence matrix between the two lower and two upper
vertices of the four-vertex component. -/
def fourSitePrimeBlock (i : ℕ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![entry (2*i) (4*i), entry (2*i) (6*i);entry (3*i) (4*i), entry (3*i) (6*i)]

private theorem double_entry {N B x : ℕ} (short : B < 4*(N+1)) (lo : N < x) (hi : 2*x ≤ B) :
    entry x (2*x)=Real.log 2 := by
  dsimp only [entry]
  rw [short_mangoldt_contact_entry short lo (by omega) hi,if_pos rfl]

private theorem triple_entry {N B x : ℕ} (short : B < 4*(N+1)) (lo : N < x) (hi : 3*x ≤ B) :
    entry x (3*x)=Real.log 3 := by
  dsimp only [entry]
  rw [short_mangoldt_contact_entry short lo (by omega) hi,if_neg (by omega : 3*x≠2*x),if_pos rfl]

/-- The three-vertex component has one nonzero singular value, the
Euclidean norm of its row of two prime contacts. -/
theorem triple_contact_singular_value {N B x : ℕ} (short : B < 4*(N+1))
    (valid : (FourfoldPath.triple x).inWindow N B) :
    Real.sqrt ((entry x (2*x))^2+(entry x (3*x))^2) =
      Real.sqrt ((Real.log 2)^2+(Real.log 3)^2) := by
  obtain ⟨lo,top,_⟩ := valid
  rw [double_entry short lo (by omega),triple_entry short lo top]

private theorem four_site_block {N B i : ℕ} (short : B < 4*(N+1))
    (valid : (FourfoldPath.quad i).inWindow N B) :
    fourSitePrimeBlock i = !![Real.log 2, Real.log 3;0, Real.log 2] := by
  obtain ⟨lo,hi⟩ := valid
  have nz : entry (3*i) (4*i)=0 := by
    dsimp only [entry]
    rw [short_mangoldt_contact_entry short (by omega : N < 3*i) (by omega : 3*i<4*i) (by omega : 4*i≤B),
      if_neg (by omega),if_neg (by omega)]
  have d1 := double_entry short lo (by omega : 2*(2*i)≤B)
  have t := triple_entry short lo (by omega : 3*(2*i)≤B)
  have d2 := double_entry short (by omega : N < 3*i) (by omega : 2*(3*i)≤B)
  rw [show 2*(2*i)=4*i by omega] at d1
  rw [show 3*(2*i)=6*i by omega] at t
  rw [show 2*(3*i)=6*i by omega] at d2
  rw [fourSitePrimeBlock,d1,t,d2,nz]

private theorem two_by_two_gram {a b z : ℝ} (b0 : 0 ≤ b) (z0 : 0 ≤ z) :
    let M : Matrix (Fin 2) (Fin 2) ℝ := !![a,b;0,a]
    z^2 ∈ spectrum ℝ (M.transpose*M) ↔
      z=(Real.sqrt (b^2+4*a^2)+b)/2 ∨ z=(Real.sqrt (b^2+4*a^2)-b)/2 := by
  let D := Real.sqrt (b^2+4*a^2)
  let p := (D+b)/2
  let m := (D-b)/2
  have Dsq : D^2 = b^2+4*a^2 := Real.sq_sqrt (by positivity)
  have base : b ≤ D := (Real.sqrt_sq b0).symm.le.trans (Real.sqrt_le_sqrt (by linarith only [sq_nonneg a]))
  have p0 : 0 ≤ p := by dsimp only [p];linarith only [b0,base]
  have m0 : 0 ≤ m := by dsimp only [m];linarith only [base]
  have total : p^2+m^2=2*a^2+b^2 := by dsimp only [p,m];nlinarith only [Dsq]
  have product : p*m=a^2 := by dsimp only [p,m];nlinarith only [Dsq]
  have fac : (z^2)^2-(2*a^2+b^2)*z^2+a^4=(z^2-p^2)*(z^2-m^2) := by
    calc _ = (z^2)^2-(p^2+m^2)*z^2+(p*m)^2 := by rw [total,product];ring
         _ = _ := by ring
  have tr : (!![a,b;0,a] : Matrix (Fin 2) (Fin 2) ℝ).transpose=!![a,0;b,a] := by
    ext i j;fin_cases i <;> fin_cases j <;> rfl
  dsimp only
  rw [tr,Matrix.mul_fin_two,Matrix.mem_spectrum_iff_isRoot_charpoly,Polynomial.IsRoot,
    Matrix.charpoly_fin_two,Matrix.trace_fin_two_of,Matrix.det_fin_two_of]
  simp only [Polynomial.eval_add,Polynomial.eval_sub,Polynomial.eval_mul,Polynomial.eval_pow,
    Polynomial.eval_X,Polynomial.eval_C]
  change _ ↔ z=p ∨ z=m
  calc
    _ ↔ (z^2)^2-(2*a^2+b^2)*z^2+a^4=0 := by congr 1 <;> ring
    _ ↔ _ := by simp only [fac,mul_eq_zero,sub_eq_zero,sq_eq_sq₀ z0 p0,sq_eq_sq₀ z0 m0]

/-- Both singular values of the actual four-site block, characterized
by the spectrum of its Gram matrix. -/
theorem four_site_contact_singular_values {N B i : ℕ} (short : B < 4*(N+1))
    (valid : (FourfoldPath.quad i).inWindow N B) {z : ℝ} (z0 : 0 ≤ z) :
    z^2 ∈ spectrum ℝ ((fourSitePrimeBlock i).transpose * fourSitePrimeBlock i) ↔
      z=(Real.sqrt ((Real.log 3)^2+4*(Real.log 2)^2)+Real.log 3)/2 ∨
      z=(Real.sqrt ((Real.log 3)^2+4*(Real.log 2)^2)-Real.log 3)/2 := by
  rw [four_site_block short valid]
  exact two_by_two_gram (Real.log_nonneg (by norm_num)) z0

end GaloisForLFunctions.SignedArithmeticCorrespondences
