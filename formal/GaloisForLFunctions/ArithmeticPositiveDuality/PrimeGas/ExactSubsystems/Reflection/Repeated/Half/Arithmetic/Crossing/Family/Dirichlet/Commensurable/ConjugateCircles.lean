import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.Reflection.Repeated.Half.Arithmetic.Crossing.Family.Dirichlet.Commensurable.Stabilization

/-! # Exact singletons from the moduli of algebraic conjugates -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.Repeated.Half.Arithmetic.Crossing.Family.Dirichlet

open Real Set Finset
open scoped Polynomial

/-- A shell polynomial bounds the cardinality of the entire set of normalized
forced targets, independently of the positive rational dilation. -/
theorem accumulated_card_le (n : ℕ+) (hn : 1<n.val) {t : ℝ} (ht : 0<t)
    (P : ℤ[X]) (ne : P ≠ 0) (root : Polynomial.aeval (shellPower t n) P=0) :
    (accumulated t).ncard ≤ P.natDegree := by
  have h := Set.ncard_le_ncard (accumulated_subset_roots n hn ht P ne root) (rootOrders n P).finite_toSet
  exact (h.trans_eq (Set.ncard_coe_finset _)).trans (rootOrders_card_le n P)

/-- If all conjugate moduli are the shell coordinate, its reciprocal, or one,
each rational dilation has a physical spectrum with just one positive blind order. -/
theorem singleton_of_root_moduli (n : ℕ+) (hn : 1<n.val) {t : ℝ} (ht : 0<t)
    (P : ℤ[X]) (ne : P ≠ 0) (root : Polynomial.aeval (shellPower t n) P=0)
    (circles : ∀ z : ℂ, Polynomial.aeval z P=0 →
      ‖z‖=1 ∨ ‖z‖=shellPower t n ∨ ‖z‖=(shellPower t n)⁻¹) (q : ℚ) (hq : 0<q) :
    Attainable {((q : ℝ)*t)} := by
  classical
  have en : 0<energy n := log_pos (Nat.one_lt_cast.mpr hn)
  have logX : log (shellPower t n)=t*energy n := by rw [shellPower_exp,log_exp]
  have valueX : |log (shellPower t n)|/energy n=t := by
    rw [logX,abs_of_pos (mul_pos ht en),mul_div_cancel_right₀ _ en.ne']
  have only {u : ℝ} (hit : u ∈ accumulated t) : u=t := by
    have possible := accumulated_subset_roots n hn ht P ne root hit
    change u ∈ (P.map (algebraMap ℤ ℂ)).roots.toFinset.image _ at possible
    obtain ⟨z,mem,eq⟩ := Finset.mem_image.mp possible
    have hz := (Polynomial.mem_roots_map_of_injective (Int.cast_injective (α := ℂ)) ne).mp
      (Multiset.mem_toFinset.mp mem)
    change |log ‖z‖|/energy n=u at eq
    rcases circles z hz with unit | same | inv
    · rw [unit,log_one,abs_zero,zero_div] at eq
      exact (hit.1.ne eq).elim
    · rw [same] at eq
      exact eq.symm.trans valueX
    · rw [inv,log_inv,abs_neg] at eq
      exact eq.symm.trans valueX
  have res := algebraic_shell_resonant n hn ht ((IsFractionRing.isAlgebraic_iff ℤ ℚ ℝ).mp ⟨P,ne,root⟩)
  have qp := (Rat.cast_pos.mpr hq : (0 : ℝ)<q)
  have pos := mul_pos qp ht
  have eq : consequences ((q : ℝ)*t)={((q : ℝ)*t)} := by
    ext v
    constructor
    · intro hit
      have hu := div_pos hit.1 qp
      have force : Forces ((q : ℝ)*t) ((q : ℝ)*(v/q)) := by rw [mul_div_cancel₀ _ qp.ne']; exact hit.2
      have base := only ((accumulated_iff_rational ht hu).mpr ⟨q,hq,force⟩)
      exact Set.mem_singleton_iff.mpr ((div_eq_iff qp.ne').mp base |>.trans (mul_comm _ _))
    · intro mem
      rw [Set.mem_singleton_iff.mp mem]
      exact ⟨pos,fun _ _ h => h⟩
  rw [← eq]
  exact least_spectrum pos ((resonant_rational_iff ht q hq).mpr res)

/-- The positive root of X²−kX−1. Its conjugate is its negative reciprocal. -/
def quadraticUnit (k : ℕ) : ℝ := ((k : ℝ)+sqrt ((k : ℝ)^2+4))/2

theorem quadratic_unit_singleton (n : ℕ+) (hn : 1<n.val) (k : ℕ) (hk : 0<k)
    (q : ℚ) (hq : 0<q) : Attainable {((q : ℝ)*(log (quadraticUnit k)/energy n))} := by
  let a := quadraticUnit k
  have pos : 0<a := by
    dsimp only [a,quadraticUnit]
    positivity
  have equation : a^2-(k : ℝ)*a-1=0 := by
    dsimp only [a,quadraticUnit]
    nlinarith only [sq_sqrt (by positivity : 0 ≤ (k : ℝ)^2+4)]
  have large : 1<a := by
    by_contra! small
    have k1 : (1 : ℝ)≤k := by exact_mod_cast Nat.succ_le_of_lt hk
    nlinarith only [mul_nonpos_of_nonneg_of_nonpos pos.le (sub_nonpos.mpr (small.trans k1)),equation]
  let t := log a/energy n
  have en : 0<energy n := log_pos (Nat.one_lt_cast.mpr hn)
  have ht : 0<t := div_pos (log_pos large) en
  have coord : shellPower t n=a := by
    rw [shellPower_exp]
    change exp ((log a/energy n)*energy n)=a
    rw [div_mul_cancel₀ _ en.ne',exp_log pos]
  let P : ℤ[X] := Polynomial.X^2-Polynomial.C (k : ℤ)*Polynomial.X-1
  have eval {K : Type} [Field K] [CharZero K] (z : K) :
      Polynomial.aeval z P=z^2-(k : K)*z-1 := by simp [P]
  have ne : P ≠ 0 := by
    intro h
    have bad := eval (0 : ℝ)
    norm_num [h] at bad
  apply singleton_of_root_moduli n hn ht P ne (by rw [coord,eval]; exact equation) _ q hq
  intro z hz
  rw [eval] at hz
  have rel : (a : ℂ)^2-(k : ℂ)*(a : ℂ)-1=0 := by exact_mod_cast equation
  have prod : (z-(a : ℂ))*(z+((a : ℂ)-k))=0 := by linear_combination hz-rel
  have reciprocal : (a : ℂ)-(k : ℂ)=(a : ℂ)⁻¹ := by
    rw [← one_div,eq_div_iff (Complex.ofReal_ne_zero.mpr pos.ne')]
    linear_combination rel
  rw [coord]
  rcases mul_eq_zero.mp prod with plus | minus
  · rw [sub_eq_zero.mp plus,Complex.norm_real,Real.norm_eq_abs,abs_of_pos pos]
    exact Or.inr (Or.inl rfl)
  · rw [reciprocal] at minus
    rw [eq_neg_of_add_eq_zero_left minus,norm_neg,norm_inv,Complex.norm_real,Real.norm_eq_abs,abs_of_pos pos]
    exact Or.inr (Or.inr rfl)

/-- Any finite family can use different shells, quadratic units, and rational dilations. -/
theorem quadratic_unit_schedule {ι : Type*} [Finite ι] (n : ι → ℕ+) (k : ι → ℕ) (q : ι → ℚ)
    (hn : ∀ i, 1<(n i).val) (hk : ∀ i, 0<k i) (hq : ∀ i, 0<q i) :
    Attainable (Set.range (fun i => (q i : ℝ)*(log (quadraticUnit (k i))/energy (n i)))) := by
  classical
  let f (i : ι) := (q i : ℝ)*(log (quadraticUnit (k i))/energy (n i))
  have fin := Set.finite_range f
  change Attainable (Set.range f)
  rw [← fin.coe_toFinset]
  apply finite_isolated_orders
  intro v mem
  obtain ⟨i,rfl⟩ := fin.mem_toFinset.mp mem
  exact quadratic_unit_singleton (n i) (hn i) (k i) (hk i) (q i) (hq i)

#print axioms accumulated_card_le
#print axioms singleton_of_root_moduli
#print axioms quadratic_unit_singleton
#print axioms quadratic_unit_schedule

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.Repeated.Half.Arithmetic.Crossing.Family.Dirichlet
