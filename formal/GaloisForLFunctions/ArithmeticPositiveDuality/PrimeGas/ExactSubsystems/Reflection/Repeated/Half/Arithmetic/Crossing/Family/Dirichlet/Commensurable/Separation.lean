import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.Reflection.Repeated.Half.Arithmetic.Crossing.Family.Dirichlet.Commensurable.Height
import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.Reflection.Repeated.Half.Arithmetic.Crossing.Family.Dirichlet.Commensurable.ScaleBound
import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.Reflection.Repeated.Half.Arithmetic.Crossing.Family.Dirichlet.Harmonics

/-! # Incomparability of all distinct commensurable resonant orders -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.Repeated.Half.Arithmetic.Crossing.Family.Dirichlet

open Finset Set MvPolynomial

private theorem amplification {p q : ℕ} (hp : 0<p) (lt : p<q) (C : ℝ) :
    ∃ n : ℕ, C*(↑(p^n) : ℝ)<↑(q^n) := by
  have pp : (0 : ℝ)<p := Nat.cast_pos.mpr hp
  have rat : 1<(q : ℝ)/p := (one_lt_div pp).mpr (Nat.cast_lt.mpr lt)
  obtain ⟨n,large⟩ := pow_unbounded_of_one_lt C rat
  rw [div_pow,lt_div_iff₀ (pow_pos pp n)] at large
  exact ⟨n,by simpa only [Nat.cast_pow] using large⟩

/-- Distinct positive integer multiples of a resonant order have incomparable
prime evaluation kernels, even in the direction of decreasing order. -/
theorem kernel_scales_equal {t : ℝ} (ht : 0<t) (res : Resonant t) {p q : ℕ}
    (hp : 0<p) (hq : 0<q) (h : kernel (t*p) ≤ kernel (t*q)) : p=q := by
  classical
  obtain ⟨S,C,_,bound⟩ := resonance_scale_bound ht res
  let a (i : S) := label i.val
  rcases lt_trichotomy p q with lt | eq | gt
  · obtain ⟨n,large⟩ := amplification hp lt C
    have step := restrict_kernel a (iterate_step h n 1)
    simp only [mul_one] at step
    exact ((bound _ _ (pow_pos hp _) (pow_pos hq _) step).asymm large).elim
  · exact eq
  · obtain ⟨n,large⟩ := amplification hq gt C
    apply False.elim
    apply no_strict_dilations a t (pow_pos hp n) (pow_pos hq n)
    intro k hk
    have step := restrict_kernel a (iterate_step h n k)
    apply lt_of_le_of_ne step
    intro eq
    have rev := bound _ _ (mul_pos (pow_pos hq _) hk) (mul_pos (pow_pos hp _) hk) eq.ge
    rw [Nat.cast_mul,Nat.cast_mul,← mul_assoc] at rev
    exact large.asymm ((mul_lt_mul_iff_left₀ (Nat.cast_pos.mpr hk : (0 : ℝ)<k)).mp rev)

theorem zero_kernel {t : ℝ} (reg : ¬Resonant t) : kernel t=⊥ := by
  apply bot_unique
  intro P hp
  change P=0
  by_contra ne
  exact reg ((resonant_iff_polynomial t).mpr ⟨P,ne,hp⟩)

/-- Integral rescaling preserves arithmetic resonance in both directions. -/
theorem resonant_nat_iff {t : ℝ} (ht : 0<t) {m : ℕ} (hm : 0 < m) :
    Resonant (t*m) ↔ Resonant t := by
  constructor
  · intro bad
    obtain ⟨P,hP,z⟩ := (resonant_iff_polynomial _).mp bad
    refine (resonant_iff_polynomial t).mpr ⟨expand m P,(expand_ne_zero hm).mpr hP,?_⟩
    have eq (p : Nat.Primes) : (coordinates t p)^m=coordinates (t*m) p :=
      (Real.rpow_mul_natCast (by positivity : 0 ≤ (p.val : ℝ)) t m).symm
    change aeval (coordinates t) (expand m P)=0
    rw [aeval_expand,show (coordinates t)^m=coordinates (t*m) from funext eq]
    exact z
  · intro res
    by_contra no
    have inc : kernel (t*m) ≤ kernel (t*(m+1 : ℕ)) := by rw [zero_kernel no]; exact bot_le
    exact (Nat.lt_succ_self m).ne (kernel_scales_equal ht res hm (Nat.succ_pos _) inc)

theorem natural_ratio (q : ℚ) (hq : 0<q) :
    ∃ a b : ℕ, 0<a ∧ 0<b ∧ (q : ℝ)*b=a := by
  have num : 0<q.num := Rat.num_pos.mpr hq
  refine ⟨q.num.toNat,q.den,(by omega),q.den_pos,?_⟩
  have eq : (q.num.toNat : ℝ)=(q.num : ℝ) := by exact_mod_cast Int.toNat_of_nonneg num.le
  rw [eq,Rat.cast_def,div_mul_cancel₀ _ (Nat.cast_ne_zero.mpr q.den_pos.ne')]

theorem resonant_rational_iff {t : ℝ} (ht : 0<t) (q : ℚ) (hq : 0<q) :
    Resonant ((q : ℝ)*t) ↔ Resonant t := by
  obtain ⟨a,b,ha,hb,eq⟩ := natural_ratio q hq
  have scale : (q : ℝ)*t*b=t*a := by linear_combination t*eq
  rw [← resonant_nat_iff (mul_pos (Rat.cast_pos.mpr hq) ht) hb,scale,resonant_nat_iff ht ha]

/-- Two distinct orders on the same positive rational orbit of a resonance
never force one another. At a nonresonant source every passing spectrum reflects. -/
theorem rational_forces_iff {t : ℝ} (ht : 0<t) (q : ℚ) (hq : 0<q) :
    Forces t ((q : ℝ)*t) ↔ q=1 ∨ ¬Resonant t := by
  have hu := mul_pos (Rat.cast_pos.mpr hq : (0 : ℝ)<q) ht
  constructor
  · intro force
    by_cases res : Resonant t
    · left
      obtain ⟨a,b,ha,hb,eq⟩ := natural_ratio q hq
      have inc := squared_step ht hu force a b (by linear_combination t*eq)
      have powers := kernel_scales_equal ht res (pow_pos hb _) (pow_pos ha _) inc
      have ba : b=a := Nat.pow_left_injective (by norm_num : (2 : ℕ) ≠ 0) powers
      have r : (q : ℝ)=1 := by
        apply mul_left_cancel₀ (Nat.cast_ne_zero.mpr hb.ne' : (b : ℝ)≠0)
        rw [mul_comm (b : ℝ),eq,mul_one,ba]
      exact_mod_cast r
    · exact Or.inr res
  · rintro (rfl | reg)
    · simp only [Rat.cast_one,one_mul]
      exact fun _ _ h => h
    · exact (forces_iff ht hu).mpr (Or.inl (by rw [zero_kernel reg]; exact bot_le))

/-- Across the entire rational orbit, every forced positive order is at most
a fixed multiple of its source. The same constant works at every rational scale. -/
theorem uniform_forced_bound {t : ℝ} (ht : 0<t) (res : Resonant t) :
    ∃ C : ℝ, 0<C ∧ ∀ (q : ℚ), 0<q → ∀ r : ℝ, 0<r →
      Forces ((q : ℝ)*t) (r*((q : ℝ)*t)) → r<C := by
  obtain ⟨S,C,pos,bound⟩ := resonance_radial_bound ht res
  refine ⟨C,pos,fun q hq r hr force => ?_⟩
  obtain ⟨a,b,ha,_,rep⟩ := natural_ratio q hq
  have ap : (0 : ℝ)<a := Nat.cast_pos.mpr ha
  have source : (q : ℝ)*t*b=t*a := by linear_combination t*rep
  have target : r*((q : ℝ)*t)*b=t*(r*a) := by linear_combination r*t*rep
  have scaled := forces_dilate force b
  rw [source,target] at scaled
  have signs := (forces_iff (mul_pos ht ap) (mul_pos ht (mul_pos hr ap))).mp scaled
  have limit : |r*(a : ℝ)|<C*a := by
    rcases signs with plus | minus
    · exact bound a ha _ (restrict_kernel _ plus)
    · rw [← mul_neg] at minus
      simpa only [abs_neg] using bound a ha (-(r*a)) (restrict_kernel _ minus)
  rw [abs_of_pos (mul_pos hr ap)] at limit
  exact (mul_lt_mul_iff_left₀ ap).mp limit

#print axioms uniform_forced_bound
#print axioms kernel_scales_equal
#print axioms resonant_rational_iff
#print axioms rational_forces_iff

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.Repeated.Half.Arithmetic.Crossing.Family.Dirichlet
