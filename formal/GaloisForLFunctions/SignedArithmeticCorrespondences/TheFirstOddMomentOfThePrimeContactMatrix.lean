import GaloisForLFunctions.SignedArithmeticCorrespondences.TheIsolatedSitesOfThePrimeContactMatrix
import Mathlib.NumberTheory.ArithmeticFunction.Liouville
import Mathlib.LinearAlgebra.Matrix.Trace

/-!
# First odd spectral moment of the Mangoldt contacts

On the full integer window (N,B] the Liouville signs reverse every prime
contact precisely up to the first square-ratio triangle. Above that
threshold each triple x,2x,4x contributes (log 2)³ to the cubic trace.
This distinguishes the true prime block from its negative in every
sufficiently wide window.
-/
noncomputable section
open Finset ArithmeticFunction GaloisForLFunctions.HodgeTheoryOfAFixedPart
open scoped ArithmeticFunction.vonMangoldt
namespace GaloisForLFunctions.SignedArithmeticCorrespondences.PrimeContactMoments

/-- Actual von Mangoldt contact between two unit masses. -/
abbrev edge (m n : ℕ) := contactW vonMangoldt m n
private theorem edge_symm (m n : ℕ) : edge m n=edge n m := add_comm _ _
private theorem edge_nonneg (m n : ℕ) : 0 ≤ edge m n := by
  unfold edge contactW
  split_ifs <;> positivity
private theorem edge_diag {m : ℕ} (hm : 0<m) : edge m m=0 := by
  simp [edge,contactW,Nat.div_self hm]

/-- The sign of the Liouville function, acting on real comb profiles. -/
def paritySign (m : ℕ) : ℝ := liouville m
private theorem sign_sq {m : ℕ} (hm : 0<m) : paritySign m^2=1 := by
  simp only [paritySign,liouville_apply hm.ne',Int.cast_pow,Int.cast_neg,Int.cast_one]
  rw [←pow_mul,Nat.mul_comm, pow_mul]
  norm_num
private theorem sign_prime {p : ℕ} (hp : p.Prime) (m : ℕ) :
    paritySign (m*p) = -paritySign m := by
  have hw := cardFactors_eq_one_iff_prime.mpr hp
  simp [paritySign,liouville_apply_mul,liouville_apply hp.ne_zero,hw]

private theorem edge_mul {m k : ℕ} (hm : 0<m) (hk : 1<k) :
    edge m (m*k)=Λ k := by
  have hn : ¬m*k∣m := fun hd => (Nat.not_lt_of_ge (Nat.le_of_dvd hm hd))
    (by simpa using Nat.mul_lt_mul_of_pos_left hk hm)
  simp only [edge,contactW,dvd_mul_right,if_true,if_neg hn,add_zero,Nat.mul_div_cancel_left _ hm]

private theorem short_flip_ordered {N B m n : ℕ} (hm : m∈Ioc N B) (hn : n∈Ioc N B)
    (hmn : m<n) (hB : B<4*(N+1)) : paritySign m*paritySign n*edge m n= -edge m n := by
  by_cases hd : m ∣ n
  · obtain ⟨k,rfl⟩ := hd
    have hm0 := (Nat.zero_le _).trans_lt (mem_Ioc.mp hm).1
    have hk : 1<k := by
      have h' : m*1<m*k := by simpa using hmn
      exact Nat.lt_of_mul_lt_mul_left h'
    have hk' : k<4 := by
      have h' : m*k < m*4 := calc
        m*k ≤ B := (mem_Ioc.mp hn).2
        _ < 4*(N+1) := hB
        _ ≤ m*4 := by rw [Nat.mul_comm m]; exact Nat.mul_le_mul_left _ (mem_Ioc.mp hm).1
      exact Nat.lt_of_mul_lt_mul_left h'
    have hprime : k.Prime := by
      rcases (by omega : k=2 ∨ k=3) with rfl|rfl
      · exact Nat.prime_two
      · exact Nat.prime_three
    rw [sign_prime hprime]
    have hsq := sign_sq hm0
    calc _ = -(paritySign m^2)*edge m (m*k) := by ring
         _ = _ := by rw [hsq];ring
  · have hrev : ¬n∣m := fun h => hmn.not_ge (Nat.le_of_dvd ((Nat.zero_le _).trans_lt (mem_Ioc.mp hm).1) h)
    simp [edge,contactW,hd,hrev]

private theorem short_flip {N B : ℕ} (hB : B<4*(N+1)) {m n : ℕ}
    (hm : m∈Ioc N B) (hn : n∈Ioc N B) : paritySign m*paritySign n*edge m n= -edge m n := by
  rcases lt_trichotomy m n with h|rfl|h
  · exact short_flip_ordered hm hn h hB
  · rw [edge_diag ((Nat.zero_le _).trans_lt (mem_Ioc.mp hm).1),mul_zero,neg_zero]
  · simpa only [edge_symm n m,mul_comm (paritySign n) (paritySign m)] using short_flip_ordered hn hm h hB

private theorem double_edge {m : ℕ} (h : 0<m) : edge m (2*m)=Real.log 2 := by
  rw [Nat.mul_comm 2,edge_mul h (by decide),vonMangoldt_apply_prime Nat.prime_two]
private theorem quadruple_edge {m : ℕ} (h : 0<m) : edge m (4*m)=Real.log 2 := by
  rw [Nat.mul_comm 4,edge_mul h (by decide),show 4=2^2 by norm_num,
    vonMangoldt_apply_pow (by decide),vonMangoldt_apply_prime Nat.prime_two]

/-- The first nonzero odd moment of the contact adjacency on a finite comb. -/
def cubicTrace (S : Finset ℕ) : ℝ :=
  ∑ i∈S, ∑ j∈S, ∑ k∈S, edge i j*edge j k*edge k i

/-- This is the ordinary trace of the cube of the finite contact matrix. -/
theorem cubicTrace_eq_matrix (S : Finset ℕ) :
    cubicTrace S = Matrix.trace ((fun i j : S => edge i.val j.val : Matrix S S ℝ)^3) := by
  classical
  simp only [cubicTrace,pow_succ,pow_zero,one_mul,Matrix.mul_apply,Matrix.trace,
    Matrix.diag_apply,Finset.sum_mul]
  simp only [Finset.sum_coe_sort]
  apply sum_congr rfl
  intro i _
  rw [sum_comm]

/-- Cubic trace of the actual unit-spaced prime block. -/
theorem cubic_prime_contact_matrix (N B : ℕ) :
    Matrix.trace ((primeContactMatrix N B)^3)=cubicTrace (Ioc N B) := (cubicTrace_eq_matrix _).symm

private theorem cube_mono {S : Finset ℕ} {i j k : ℕ} (hj : j∈S) (hk : k∈S) :
    edge i j*edge j k*edge k i ≤ ∑ u∈S,∑ v∈S,edge i u*edge u v*edge v i :=
  (single_le_sum (fun v _ => mul_nonneg (mul_nonneg (edge_nonneg _ _) (edge_nonneg _ _)) (edge_nonneg _ _)) hk).trans
    (single_le_sum (fun u _ => sum_nonneg fun _ _ => mul_nonneg
      (mul_nonneg (edge_nonneg _ _) (edge_nonneg _ _)) (edge_nonneg _ _)) hj)

/-- Each possible start of a 1:2:4 triple contributes to the trace even
in the presence of every other actual prime and prime-power contact. -/
theorem cubic_trace_lower (N B : ℕ) :
    ((B/4-N:ℕ):ℝ)*Real.log 2^3 ≤ cubicTrace (Ioc N B) := by
  let S := Ioc N B
  let U := Ioc N (B/4)
  have sub : U⊆S := fun i hi => mem_Ioc.mpr ⟨(mem_Ioc.mp hi).1,(mem_Ioc.mp hi).2.trans (Nat.div_le_self _ _)⟩
  have hprice (i : ℕ) (hi : i∈U) :
      Real.log 2^3 ≤ ∑ j∈S,∑ k∈S,edge i j*edge j k*edge k i := by
    have hh := mem_Ioc.mp hi
    have hp := (Nat.zero_le _).trans_lt hh.1
    have hb : i*4 ≤ B := (Nat.le_div_iff_mul_le (by decide)).mp hh.2
    have h := cube_mono (S:=S) (i:=i) (j:=2*i) (k:=4*i)
      (mem_Ioc.mpr ⟨by omega,by omega⟩) (mem_Ioc.mpr ⟨by omega,by omega⟩)
    rw [double_edge hp,show 4*i=2*(2*i) by ring,double_edge (by omega),edge_symm _ i,
      ←show 4*i=2*(2*i) by ring,quadruple_edge hp] at h
    exact (by ring : Real.log 2^3=Real.log 2*Real.log 2*Real.log 2).le.trans h
  have h := (sum_le_sum hprice).trans (sum_le_sum_of_subset_of_nonneg sub fun i _ _ =>
    sum_nonneg fun j _ => sum_nonneg fun k _ => mul_nonneg (mul_nonneg (edge_nonneg _ _)
      (edge_nonneg _ _)) (edge_nonneg _ _))
  simpa only [U,S,sum_const,Nat.card_Ioc,nsmul_eq_mul,cubicTrace] using h

private theorem trace_zero_of_flip {S : Finset ℕ} {f : ℕ → ℝ}
    (hf : ∀ i∈S, f i^2=1) (h : ∀ i∈S,∀ j∈S,f i*f j*edge i j= -edge i j) :
    cubicTrace S=0 := by
  apply sum_eq_zero
  intro i hi
  apply sum_eq_zero
  intro j hj
  apply sum_eq_zero
  intro k hk
  have hmul := congrArg₂ (· * ·) (congrArg₂ (· * ·) (h i hi j hj) (h j hj k hk)) (h k hk i hi)
  have hd : (f i*f j*edge i j)*(f j*f k*edge j k)*(f k*f i*edge k i)=
      f i^2*f j^2*f k^2*(edge i j*edge j k*edge k i) := by ring
  rw [hd,hf i hi,hf j hj,hf k hk] at hmul
  linarith only [hmul]

/-- Exact endpoint of sign symmetry. The integer window is short enough
for Liouville reversal iff its cubic trace vanishes, iff any diagonal
choice of signs can reverse the matrix. -/
theorem cubic_zero_iff_short (N B : ℕ) : cubicTrace (Ioc N B)=0 ↔ B<4*(N+1) := by
  constructor
  · intro h
    by_contra! hh
    have hpos : 0 < B/4-N := by
      have hd := (Nat.le_div_iff_mul_le (by decide : 0<4)).mpr
        (by omega : (N+1)*4≤B)
      omega
    have hl := Real.log_pos (by norm_num : (1:ℝ)<2)
    have hlt := mul_pos (Nat.cast_pos.mpr hpos : 0<((B/4-N:ℕ):ℝ)) (pow_pos hl 3)
    exact (hlt.trans_le (cubic_trace_lower N B)).ne' h
  · intro hB
    exact trace_zero_of_flip (fun i hi => sign_sq ((Nat.zero_le _).trans_lt (mem_Ioc.mp hi).1))
      (fun _ hi _ hj => short_flip hB hi hj)

theorem reversible_contact_signs_iff (N B : ℕ) :
    (∃ f : ℕ → ℝ, (∀ i∈Ioc N B, f i^2=1) ∧
      ∀ i∈Ioc N B,∀ j∈Ioc N B,f i*f j*edge i j= -edge i j) ↔ B<4*(N+1) := by
  constructor
  · rintro ⟨f,hf,h⟩
    exact (cubic_zero_iff_short _ _).mp (trace_zero_of_flip hf h)
  · intro h
    exact ⟨paritySign,fun i hi => sign_sq ((Nat.zero_le _).trans_lt (mem_Ioc.mp hi).1),
      fun _ hi _ hj => short_flip h hi hj⟩

#print axioms cubicTrace_eq_matrix
#print axioms cubic_trace_lower
#print axioms cubic_zero_iff_short
#print axioms reversible_contact_signs_iff
end GaloisForLFunctions.SignedArithmeticCorrespondences.PrimeContactMoments
