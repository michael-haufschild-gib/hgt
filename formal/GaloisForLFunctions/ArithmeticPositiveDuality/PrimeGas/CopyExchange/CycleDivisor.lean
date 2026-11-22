import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.CopyExchange.CycleBoundary
import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.PrimeParityPartition

/-!
# Reading cycle lengths from the permutation partition

The pole order at the reciprocal of a positive integer counts the cycles of
that length. In the open right half of the critical strip, only fixed copies
can contribute to the zeta divisor.
-/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.CopyExchange

open GaloisForLFunctions.HTGeometry GaloisForLFunctions.ZeroForcingCalculus
open scoped Classical

variable {I : Type*} [Fintype I]

def cycleCount (π : Equiv.Perm I) (k : ℕ) : ℕ :=
  (Finset.univ.filter (fun c => cycleLength π c = k)).card

private theorem dilation_ne (π : Equiv.Perm I) (c : Cycle π) : (cycleLength π c : ℂ) ≠ 0 :=
  Nat.cast_ne_zero.mpr (cycleLength_pos π c).ne'

theorem cyclePartition_meromorphic (π : Equiv.Perm I) (s : ℂ) : MeromorphicAt (cyclePartition π) s := by
  unfold cyclePartition
  apply MeromorphicAt.fun_prod
  exact fun c _ => (meromorphicOrderAt_riemannZeta_const_mul (dilation_ne π c) s).1

theorem cyclePartition_order (π : Equiv.Perm I) (s : ℂ) :
    meromorphicOrderAt (cyclePartition π) s = ∑ c, meromorphicOrderAt riemannZeta ((cycleLength π c : ℂ)*s) := by
  have hm (c : Cycle π) := meromorphicOrderAt_riemannZeta_const_mul (dilation_ne π c) s
  unfold cyclePartition
  rw [meromorphicOrderAt_fun_prod (fun c _ => (hm c).1)]
  exact Finset.sum_congr rfl fun c _ => (hm c).2

private theorem real_order (x : ℝ) (hx : 0 < x) :
    meromorphicOrderAt riemannZeta (x : ℂ) = ((if x=1 then -1 else 0 : ℤ) : WithTop ℤ) := by
  by_cases h : x=1
  · subst x
    simp only [Complex.ofReal_one]
    exact meromorphicOrderAt_riemannZeta_one
  · rw [if_neg h]
    apply meromorphicOrderAt_eq_zero_of_analyticAt_ne_zero (HTGeometry.analyticAt_riemannZeta (by exact_mod_cast h))
    rcases lt_or_ge x 1 with hlt | hge
    · exact _root_.RHTower.riemannZeta_real_strip_ne_zero hx hlt
    · exact riemannZeta_ne_zero_of_one_le_re hge

/-- Positive real pole order counts exactly the cycles resonant at that temperature. -/
theorem cycle_order_positive (π : Equiv.Perm I) (x : {t : ℝ // 0 < t}) :
    meromorphicOrderAt (cyclePartition π) (x.val : ℂ) =
      ↑(-((Finset.univ.filter (fun c => (cycleLength π c : ℝ)*x.val=1)).card : ℤ)) := by
  let P (c : Cycle π) := (cycleLength π c : ℝ)*x.val=1
  have hc (c : Cycle π) : meromorphicOrderAt riemannZeta ((cycleLength π c : ℂ)*(x.val : ℂ)) =
      ((if P c then -1 else 0 : ℤ) : WithTop ℤ) := by
    have hpos : 0 < (cycleLength π c : ℝ) := by exact_mod_cast cycleLength_pos π c
    simpa only [Complex.ofReal_mul,Complex.ofReal_natCast,P] using
      real_order ((cycleLength π c : ℝ)*x.val) (mul_pos hpos x.property)
  rw [cyclePartition_order,Finset.sum_congr rfl fun c _ => hc c]
  rw [← WithTop.coe_sum,WithTop.coe_inj]
  rw [← Finset.sum_filter]
  simp [P]

/-- Pole spectroscopy recovers the multiplicity of every cycle length. -/
theorem cycle_order_reciprocal (π : Equiv.Perm I) (k : ℕ+) :
    meromorphicOrderAt (cyclePartition π) ((1/(k : ℝ) : ℝ) : ℂ) = ((-(cycleCount π k : ℤ) : ℤ) : WithTop ℤ) := by
  have hk : 0 < (k : ℝ) := by exact_mod_cast k.pos
  have he (c : Cycle π) : (cycleLength π c : ℝ)*(1/(k : ℝ))=1 ↔ cycleLength π c = (k : ℕ) := by
    rw [← div_eq_mul_one_div,div_eq_iff hk.ne',one_mul]
    exact_mod_cast Iff.rfl
  rw [cycle_order_positive π ⟨_,one_div_pos.mpr hk⟩]
  simp only [he,cycleCount]

theorem same_positive_divisor_iff {J : Type*} [Fintype J] (π : Equiv.Perm I) (τ : Equiv.Perm J) :
    (∀ k : ℕ+, meromorphicOrderAt (cyclePartition π) ((1/(k : ℝ) : ℝ) : ℂ) =
      meromorphicOrderAt (cyclePartition τ) ((1/(k : ℝ) : ℝ) : ℂ)) ↔
      ∀ k : ℕ+, cycleCount π k = cycleCount τ k := by
  simp only [cycle_order_reciprocal,WithTop.coe_inj,neg_inj,Nat.cast_inj]

private theorem zeta_order_zero (z : ℂ) (hz : 1 < z.re) :
    meromorphicOrderAt riemannZeta z = 0 := by
  have hne : z ≠ 1 := fun h => hz.ne' (by rw [h]; rfl)
  exact meromorphicOrderAt_eq_zero_of_analyticAt_ne_zero (HTGeometry.analyticAt_riemannZeta hne)
    (riemannZeta_ne_zero_of_one_lt_re hz)

/-- Nonreal arguments remain regular after a positive dilation reaches the closed zeta half-plane. -/
private theorem regular_dilation (k : ℕ) (hk : 0 < k) (s : ℂ)
    (hb : 1 ≤ (k : ℝ)*s.re) (ht : s.im ≠ 0) :
    riemannZeta ((k : ℂ)*s) ≠ 0 ∧ meromorphicOrderAt riemannZeta ((k : ℂ)*s) = 0 := by
  have hn : riemannZeta ((k : ℂ)*s) ≠ 0 :=
    riemannZeta_ne_zero_of_one_le_re (by simpa [Complex.mul_re] using hb)
  refine ⟨hn,meromorphicOrderAt_eq_zero_of_analyticAt_ne_zero (HTGeometry.analyticAt_riemannZeta ?_) hn⟩
  intro h
  have he := congrArg Complex.im h
  simp only [Complex.mul_im,Complex.natCast_re,Complex.natCast_im,zero_mul,add_zero,Complex.one_im] at he
  exact (mul_ne_zero (Nat.cast_ne_zero.mpr hk.ne') ht) he

private theorem singleton_order (π : Equiv.Perm I) (s : ℂ)
    (hregular : ∀ c, cycleLength π c ≠ 1 → meromorphicOrderAt riemannZeta ((cycleLength π c : ℂ)*s) = 0) :
    meromorphicOrderAt (cyclePartition π) s = cycleCount π 1 • meromorphicOrderAt riemannZeta s := by
  rw [cyclePartition_order]
  have he (c : Cycle π) : meromorphicOrderAt riemannZeta ((cycleLength π c : ℂ)*s) =
      if cycleLength π c = 1 then meromorphicOrderAt riemannZeta s else 0 := by
    by_cases h : cycleLength π c = 1
    · simp [h]
    · rw [if_neg h,hregular c h]
  rw [Finset.sum_congr rfl fun c _ => he c, ← Finset.sum_filter]
  simp [cycleCount]

/-- In Re(s)>1/2 the divisor remembers precisely the singleton copies. -/
theorem cycle_order_right (π : Equiv.Perm I) (s : {w : ℂ // 1/2 < w.re}) :
    meromorphicOrderAt (cyclePartition π) s.val = cycleCount π 1 • meromorphicOrderAt riemannZeta s.val := by
  apply singleton_order
  intro c h
  have hp := cycleLength_pos π c
  have hc : (2 : ℝ) ≤ cycleLength π c := by exact_mod_cast (show 2 ≤ cycleLength π c by omega)
  apply zeta_order_zero
  rw [Complex.mul_re]
  simp only [Complex.natCast_re,Complex.natCast_im,zero_mul,sub_zero]
  exact (by linarith only [s.property] : 1 < 2*s.val.re).trans_le
    (mul_le_mul_of_nonneg_right hc (by linarith only [s.property]))

/-- On the nonreal critical line the original zeta divisor survives with exactly its singleton multiplicity. -/
theorem cycle_order_critical (π : Equiv.Perm I) (s : {w : ℂ // w.re = 1/2 ∧ w.im ≠ 0}) :
    meromorphicOrderAt (cyclePartition π) s.val = cycleCount π 1 • meromorphicOrderAt riemannZeta s.val := by
  apply singleton_order
  intro c h
  have hp := cycleLength_pos π c
  have hc : (2 : ℝ) ≤ cycleLength π c := by exact_mod_cast (show 2 ≤ cycleLength π c by omega)
  exact (regular_dilation _ hp s.val (by rw [s.property.1]; linarith only [hc]) s.property.2).2

/-- Every fixed-label heat partition is zero-free on its genuine trace domain. -/
theorem cyclePartition_ne_zero (π : Equiv.Perm I) (s : {w : ℂ // InCycleDomain π w}) :
    cyclePartition π s.val ≠ 0 := by
  apply Finset.prod_ne_zero_iff.mpr
  intro c _
  apply riemannZeta_ne_zero_of_one_lt_re
  simpa [Complex.mul_re] using s.property c

/-- The trace-class boundary is the rightmost pole of the continued fixed-label partition. -/
theorem rightmost_pole [Nonempty I] (π : Equiv.Perm I) :
    meromorphicOrderAt (cyclePartition π) ((1/(shortestCycle π : ℝ) : ℝ) : ℂ) < 0 ∧
      ∀ z : ℂ, 1/(shortestCycle π : ℝ) < z.re → meromorphicOrderAt (cyclePartition π) z = 0 := by
  constructor
  · let k : ℕ+ := ⟨shortestCycle π,shortest_pos π⟩
    obtain ⟨c,hc⟩ := exists_shortest π
    have hcount : 0 < cycleCount π k := Finset.card_pos.mpr ⟨c,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hc⟩⟩
    change meromorphicOrderAt (cyclePartition π) ((1/(k : ℝ) : ℝ) : ℂ) < 0
    rw [cycle_order_reciprocal]
    apply WithTop.coe_lt_coe.mpr
    exact neg_neg_of_pos (by exact_mod_cast hcount)
  · intro z hz
    have hd := (fixedHeat_traceClass_iff π z).mp ((fixedHeat_shortest_iff π z).mpr hz)
    rw [cyclePartition_order]
    exact Finset.sum_eq_zero fun c _ => zeta_order_zero _ (by simpa [Complex.mul_re] using hd c)

/-- Away from the real axis, even the boundary of the fixed-label trace domain is zero-free. -/
theorem closed_halfplane_nonreal [Nonempty I] (π : Equiv.Perm I)
    (z : {w : ℂ // 1/(shortestCycle π : ℝ) ≤ w.re ∧ w.im ≠ 0}) :
    cyclePartition π z.val ≠ 0 ∧ meromorphicOrderAt (cyclePartition π) z.val = 0 := by
  have hp : 0 < (shortestCycle π : ℝ) := by exact_mod_cast shortest_pos π
  have hz : 0 ≤ z.val.re := (one_div_pos.mpr hp).le.trans z.property.1
  have hb := (div_le_iff₀ hp).mp z.property.1
  have hr (c : Cycle π) := regular_dilation _ (cycleLength_pos π c) z.val (by
    have hl : (shortestCycle π : ℝ) ≤ cycleLength π c := by exact_mod_cast shortest_le π c
    simpa only [mul_comm z.val.re] using hb.trans (mul_le_mul_of_nonneg_left hl hz)) z.property.2
  refine ⟨Finset.prod_ne_zero_iff.mpr (fun c _ => (hr c).1),?_⟩
  rw [cyclePartition_order]
  exact Finset.sum_eq_zero fun c _ => (hr c).2

/-- Permutations detecting binary isometry have a zero-free partition strictly to its right. -/
theorem split_detector_zero_free [Nonempty I] (π : Equiv.Perm I) (h : DetectsSplit π)
    (s : {w : ℂ // 1/2 < w.re}) :
    cyclePartition π s.val ≠ 0 ∧ meromorphicOrderAt (cyclePartition π) s.val = 0 := by
  have h₂ := (shortest_two_iff π).mpr ((split_detecting_permutations π).mp h)
  have hr : 1/(shortestCycle π : ℝ) < s.val.re := by simpa only [h₂,Nat.cast_ofNat] using s.property
  have hd := (fixedHeat_traceClass_iff π s.val).mp ((fixedHeat_shortest_iff π s.val).mpr hr)
  exact ⟨cyclePartition_ne_zero π ⟨_,hd⟩,(rightmost_pole π).2 _ hr⟩

#print axioms cyclePartition_meromorphic
#print axioms cyclePartition_order
#print axioms cycle_order_positive
#print axioms cycle_order_reciprocal
#print axioms same_positive_divisor_iff
#print axioms cycle_order_right
#print axioms cycle_order_critical
#print axioms cyclePartition_ne_zero
#print axioms rightmost_pole
#print axioms closed_halfplane_nonreal
#print axioms split_detector_zero_free

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.CopyExchange
