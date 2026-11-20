import GaloisForLFunctions.RestrictedFactorizationCalculus.ThePrimeOnlyQuotientRowsOfTheRoughInterior
import Mathlib.NumberTheory.Primorial

/-!
# The terminal atom of the rough interior

An interval consisting only of n reads divisors of n. An active quotient
has a squarefree cofactor prime to the sieve wall, so the largest possible
cofactor is exactly the product of the surviving prime divisors. This
determines the entire support and the weighted maximum of the row.
-/
noncomputable section
open Finset Filter ArithmeticFunction RHTower.CoprimeMobius
open scoped Classical Topology ArithmeticFunction.Moebius
open GaloisForLFunctions.BezoutValuationIncidence
namespace GaloisForLFunctions.RestrictedFactorizationCalculus

/-- Product of the distinct prime divisors of n above y. -/
def survivingRadical (y n : ℕ) := ∏ p∈n.primeFactors.filter (y < ·),p

private theorem rad_factors (y n : ℕ) :
    (survivingRadical y n).primeFactors=n.primeFactors.filter (y < ·) :=
  Nat.primeFactors_prod fun _ hp => Nat.prime_of_mem_primeFactors (mem_filter.mp hp).1

private theorem rad_divides (y n : ℕ) : survivingRadical y n ∣ n :=
  (prod_dvd_prod_of_subset _ _ id (filter_subset ..)).trans (Nat.prod_primeFactors_dvd n)

private theorem rad_squarefree (y n : ℕ) : Squarefree (survivingRadical y n) := by
  let S := n.primeFactors.filter (y < ·)
  have pr (p : ℕ) (hp : p∈S) := Nat.prime_of_mem_primeFactors (mem_filter.mp hp).1
  change Squarefree (∏ p∈S,p)
  refine Finset.squarefree_prod_of_pairwise_isCoprime ?_ (fun p hp => (pr p hp).squarefree)
  intro p hp q hq ne
  exact Nat.coprime_iff_isRelPrime.mp ((Nat.coprime_primes (pr p hp) (pr q hq)).mpr ne)

private theorem rad_coprime (y n : ℕ) : (primorial y).Coprime (survivingRadical y n) := by
  apply (Nat.disjoint_primeFactors (primorial_ne_zero _) (rad_squarefree y n).ne_zero).mp
  rw [primeFactors_primorial,rad_factors]
  exact disjoint_left.mpr (fun p hp hq => (mem_filter.mp hq).2.not_ge (Nat.mem_primesLE.mp hp).1)

/-- An arithmetic divisor is a squarefree surviving cofactor exactly
when it divides the surviving radical. -/
theorem dvd_surviving_radical_iff {n d : ℕ} (np : 0 < n) (y : ℕ) :
    d ∣ survivingRadical y n ↔ d ∣ n ∧ Squarefree d ∧ (primorial y).Coprime d := by
  constructor
  · intro dvd
    exact ⟨dvd.trans (rad_divides y n),Squarefree.squarefree_of_dvd dvd (rad_squarefree y n),
      Nat.Coprime.coprime_dvd_right dvd (rad_coprime y n)⟩
  · rintro ⟨dn,sd,cop⟩
    rw [←Nat.prod_primeFactors_of_squarefree sd]
    apply prod_dvd_prod_of_subset _ _ id
    intro p hp
    have prime := Nat.prime_of_mem_primeFactors hp
    have hn := Nat.primeFactors_mono dn np.ne' hp
    refine mem_filter.mpr ⟨hn,lt_of_not_ge (fun small => ?_)⟩
    have hp' : p ∈ (primorial y).primeFactors := by rw [primeFactors_primorial];exact Nat.mem_primesLE.mpr ⟨small,prime⟩
    exact disjoint_left.mp cop.disjoint_primeFactors hp' hp

private abbrev weight (y d : ℕ) := coprimeMoebiusIndicator (primorial y) d

/-- Removing the entire prefix through n−1 leaves the single Möbius
increment at n/q precisely when q divides n. -/
theorem terminal_interior_kernel (y : ℕ) {n q : ℕ} (np : 0 < n) :
    interiorKernel y n (n-1) q=if q ∣ n then weight y (n/q) else 0 := by
  obtain ⟨k,rfl⟩ := Nat.exists_eq_succ_of_ne_zero np.ne'
  simp only [interiorKernel,Nat.succ_sub_one,min_eq_right (Nat.le_succ k)]
  have h := Nat.succ_div (a:=k) (b:=q)
  by_cases dv : q ∣ k+1
  · rw [if_pos dv]
    have eq : (k+1)/q=k/q+1 := by simpa only [if_pos dv] using h
    simp only [eq,coprimeMoebiusSum,sum_Icc_succ_top (Nat.succ_le_succ (Nat.zero_le (k/q))),add_sub_cancel_left,weight]
  · rw [if_neg dv]
    have eq : (k+1)/q=k/q := by simpa only [if_neg dv,add_zero] using h
    rw [eq,sub_self]

private theorem abs_weight (y d : ℕ) :
    |weight y d|=if Squarefree d ∧ (primorial y).Coprime d then 1 else 0 := by
  by_cases cop : (primorial y).Coprime d
  · simp only [weight,coprimeMoebiusIndicator,if_pos cop,←Int.cast_abs,abs_moebius]
    split_ifs <;> simp_all
  · simp [weight,coprimeMoebiusIndicator,cop]

/-- All nonzero coordinates have unit magnitude. The cofactor n/q runs
through the complete divisor set of the surviving radical. -/
theorem terminal_kernel_magnitude (y : ℕ) {n q : ℕ} (np : 0 < n) :
    |interiorKernel y n (n-1) q| = if q ∣ n ∧ n/q ∣ survivingRadical y n then 1 else 0 := by
  rw [terminal_interior_kernel y np]
  by_cases dv : q ∣ n
  · have sub := Nat.div_dvd_of_dvd dv
    rw [if_pos dv,abs_weight]
    simp only [dv,true_and,dvd_surviving_radical_iff np y,sub]
  · simp [dv]

private theorem actual (y : ℕ) {n d : ℕ} (np : 0 < n) (dvd : d ∣ survivingRadical y n) :
    n/d∈Icc 1 n ∧ |interiorKernel y n (n-1) (n/d)|=1 := by
  have dn := dvd.trans (rad_divides y n)
  have dp := Nat.pos_of_dvd_of_pos dn np
  have qp := Nat.div_pos (Nat.le_of_dvd np dn) dp
  have qd := Nat.div_dvd_of_dvd dn
  have ratio := Nat.div_div_self dn np.ne'
  refine ⟨mem_Icc.mpr ⟨qp,Nat.div_le_self ..⟩,?_⟩
  rw [terminal_kernel_magnitude y np,if_pos ⟨qd,by rwa [ratio]⟩]

/-- Positive weight exponents select the last site. Negative exponents
select the quotient by the largest squarefree cofactor surviving the wall. -/
theorem sharp_terminal_weighted_site (y : ℕ) {n : ℕ} (np : 0 < n) (s : ℝ) :
    IsGreatest {v : ℝ | ∃ q∈Icc 1 n,v=(q:ℝ)^s*|interiorKernel y n (n-1) q|}
      (if 0 ≤ s then (n:ℝ)^s else ((n/survivingRadical y n:ℕ):ℝ)^s) := by
  let R := survivingRadical y n
  have dp : 0 < R := Nat.pos_of_ne_zero (rad_squarefree y n).ne_zero
  have qlo := (mem_Icc.mp (actual y np (dvd_refl R)).1).1
  by_cases sp : 0 ≤ s
  · rw [if_pos sp]
    have last := actual y np (one_dvd R)
    simp only [Nat.div_one] at last
    refine ⟨⟨n,last.1,by rw [last.2,mul_one]⟩,?_⟩
    rintro _ ⟨q,hq,rfl⟩
    obtain ⟨p,le⟩ := mem_Icc.mp hq
    rw [terminal_kernel_magnitude y np]
    split
    · rw [mul_one];exact Real.rpow_le_rpow (Nat.cast_nonneg _) (Nat.cast_le.mpr le) sp
    · rw [mul_zero];exact Real.rpow_nonneg (Nat.cast_nonneg _) _
  · rw [if_neg sp]
    have first := actual y np (dvd_refl R)
    refine ⟨⟨n/R,first.1,by rw [first.2,mul_one]⟩,?_⟩
    rintro _ ⟨q,hq,rfl⟩
    rw [terminal_kernel_magnitude y np]
    split_ifs with active
    · obtain ⟨divides,thin⟩ := active
      have before : n/R ≤ q := by
        have small := Nat.le_of_dvd dp thin
        have qp := Nat.pos_of_dvd_of_pos (Nat.div_dvd_of_dvd divides) np
        exact (Nat.div_le_div_left small qp).trans_eq (Nat.div_div_self divides np.ne')
      rw [mul_one]
      exact Real.rpow_le_rpow_of_nonpos (Nat.cast_pos.mpr qlo) (Nat.cast_le.mpr before) (le_of_not_ge sp)
    · rw [mul_zero];exact Real.rpow_nonneg (Nat.cast_nonneg _) _

/-- Testing the full terminal row against any function that vanishes
on zero entries is the same as testing the divisors of its radical. -/
theorem terminal_divisor_readout (y : ℕ) {n : ℕ} (np : 0 < n) (f : ℕ → ℝ → ℝ)
    (zero : ∀ q,f q 0=0) :
    (∑ q∈Icc 1 n,f q (interiorKernel y n (n-1) q)) =
      ∑ d∈(survivingRadical y n).divisors,f (n/d) ((μ d:ℤ):ℝ) := by
  let R := survivingRadical y n
  let S := (Icc 1 n).filter (fun q => q ∣ n ∧ n/q ∣ R)
  have shrunk :
      (∑ q∈S,f q (interiorKernel y n (n-1) q))=∑ q∈Icc 1 n,f q (interiorKernel y n (n-1) q) := by
    apply sum_subset (filter_subset ..)
    intro q hq away
    have off : ¬(q ∣ n ∧ n/q ∣ R) := fun h => away (mem_filter.mpr ⟨hq,h⟩)
    have empty := terminal_kernel_magnitude (q:=q) y np
    rw [if_neg off,abs_eq_zero] at empty
    rw [empty,zero]
  rw [←shrunk]
  have r0 : R ≠ 0 := (rad_squarefree y n).ne_zero
  apply sum_nbij' (fun q => n/q) (fun d => n/d)
  · intro q hq
    exact Nat.mem_divisors.mpr ⟨(mem_filter.mp hq).2.2,r0⟩
  · intro d hd
    have div := (Nat.mem_divisors.mp hd).1
    have dn := div.trans (rad_divides y n)
    have qn := Nat.div_dvd_of_dvd dn
    exact mem_filter.mpr ⟨(actual y np div).1,qn,by rwa [Nat.div_div_self dn np.ne']⟩
  · intro q hq
    exact Nat.div_div_self (mem_filter.mp hq).2.1 np.ne'
  · intro d hd
    exact Nat.div_div_self ((Nat.mem_divisors.mp hd).1.trans (rad_divides y n)) np.ne'
  · intro q hq
    obtain ⟨qn,thin⟩ := (mem_filter.mp hq).2
    have free := ((dvd_surviving_radical_iff np y).mp thin).2.2
    rw [Nat.div_div_self qn np.ne',terminal_interior_kernel y np,if_pos qn]
    simp only [weight,coprimeMoebiusIndicator,if_pos free]

private def powerWeight (s : ℝ) : ArithmeticFunction ℝ :=
  ⟨fun n => if n=0 then 0 else (n:ℝ)^s,by simp⟩

private theorem power_mult (s : ℝ) : (powerWeight s).IsMultiplicative := by
  rw [IsMultiplicative.iff_ne_zero]
  refine ⟨by simp [powerWeight],fun {a b} ha hb _ => ?_⟩
  simp only [powerWeight,coe_mk,if_neg ha,if_neg hb,if_neg (Nat.mul_ne_zero ha hb),
    Nat.cast_mul,Real.mul_rpow (Nat.cast_nonneg a) (Nat.cast_nonneg b)]

private theorem weighted_profile (y : ℕ) {n : ℕ} (np : 0 < n) (s : ℝ) (f : ℝ → ℝ) (hf : f 0=0) :
    (∑ q∈Icc 1 n,(q:ℝ)^s*f (interiorKernel y n (n-1) q)) =
      (n:ℝ)^s*∑ d∈(survivingRadical y n).divisors,f ((μ d:ℤ):ℝ)*powerWeight (-s) d := by
  rw [terminal_divisor_readout y np (fun q z => (q:ℝ)^s*f z) (fun q => by rw [hf,mul_zero]),mul_sum]
  apply sum_congr rfl
  intro d hd
  have dvd := (Nat.mem_divisors.mp hd).1.trans (rad_divides y n)
  have dp := Nat.pos_of_dvd_of_pos dvd np
  have eq : (n:ℝ)^s=((n/d:ℕ):ℝ)^s*(d:ℝ)^s := by
    rw [←Real.mul_rpow (Nat.cast_nonneg _) (Nat.cast_nonneg d),←Nat.cast_mul,Nat.div_mul_cancel dvd]
  simp only [powerWeight,coe_mk,if_neg dp.ne',Real.rpow_neg (Nat.cast_nonneg d),eq]
  field_simp [(Real.rpow_pos_of_pos (Nat.cast_pos.mpr dp) s).ne']

/-- The signed and absolute terminal readouts are complementary Euler
products at the primes of n that survive the wall. -/
theorem terminal_signed_and_absolute_products (y : ℕ) {n : ℕ} (np : 0 < n) (s : ℝ) :
    (∑ q∈Icc 1 n,(q:ℝ)^s*interiorKernel y n (n-1) q) =
      (n:ℝ)^s*∏ p∈n.primeFactors.filter (y < ·),(1-(p:ℝ)^(-s)) ∧
    (∑ q∈Icc 1 n,(q:ℝ)^s*|interiorKernel y n (n-1) q|) =
      (n:ℝ)^s*∏ p∈n.primeFactors.filter (y < ·),(1+(p:ℝ)^(-s)) := by
  let R := survivingRadical y n
  have sq := rad_squarefree y n
  have pm := power_mult (-s)
  have factors (p : ℕ) (hp : p ∈ R.primeFactors) : powerWeight (-s) p=(p:ℝ)^(-s) :=
    if_neg (Nat.prime_of_mem_primeFactors hp).ne_zero
  constructor
  · have mult := ArithmeticFunction.IsMultiplicative.prodPrimeFactors_one_sub_of_squarefree (powerWeight (-s)) pm sq
    have row := weighted_profile y np s id rfl
    simp only [id_eq] at row
    rw [row,←mult,←rad_factors]
    exact congrArg ((n:ℝ)^s * ·) (prod_congr rfl fun p hp => by rw [factors p hp])
  · rw [weighted_profile y np s abs abs_zero]
    have units (d : ℕ) (hd : d ∈ R.divisors) : |((μ d:ℤ):ℝ)|=1 := by
      have dSq := Squarefree.squarefree_of_dvd (Nat.mem_divisors.mp hd).1 sq
      exact_mod_cast abs_moebius_eq_one_of_squarefree dSq
    have reduce : (∑ d∈R.divisors,|((μ d:ℤ):ℝ)| * powerWeight (-s) d)=∑ d∈R.divisors,powerWeight (-s) d :=
      sum_congr rfl fun d hd => by rw [units d hd,one_mul]
    rw [reduce,←pm.prodPrimeFactors_one_add_of_squarefree sq,←rad_factors]
    exact congrArg ((n:ℝ)^s * ·) (prod_congr rfl fun p hp => by rw [factors p hp])

end GaloisForLFunctions.RestrictedFactorizationCalculus
