import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.FiniteField.SquareFieldTraceFibers

/-!
# A common injectivity criterion for all finite-field trace fibers

Differences of points in one trace fiber lie in the trace kernel. Translation
therefore turns injectivity of any additive map on a nonempty fiber into the
same intersection-of-kernels test. The explicit trace-one element discharges
nonemptiness for the Kummer trace fibers. Linearized polynomials inherit the
criterion without assumptions on their coefficients.
-/

open Finset

namespace GaloisForLFunctions.ArithmeticCastelnuovoSeveri
noncomputable section

private theorem additive_fiber_injective_iff
    {A B C : Type*} [AddCommGroup A] [AddCommGroup B] [AddCommGroup C]
    (T : A →+ B) (L : A →+ C) (u : A) :
    Set.InjOn L {x | T x = T u} ↔ ∀ x, T x = 0 → L x = 0 → x = 0 := by
  constructor
  · intro h x hx hL
    have he : u + x = u := h
      (by change T (u + x) = T u; rw [map_add, hx, add_zero])
      (by rfl)
      (by rw [map_add, hL, add_zero])
    exact add_left_cancel (he.trans (add_zero u).symm)
  · intro h x hx y hy hxy
    apply sub_eq_zero.mp
    apply h (x - y)
    · rw [map_sub, hx, hy, sub_self]
    · rw [map_sub, hxy, sub_self]

variable (p : ℕ) [Fact p.Prime]

/-- Zero and one trace fibers impose exactly the same injectivity condition. -/
theorem squareFieldTrace_injOn_one_iff_zero (s : ℕ)
    (L : SquareConstantField p s →+ SquareConstantField p s) :
    Set.InjOn L {x | squareFieldTrace p s x = 1} ↔
      Set.InjOn L {x | squareFieldTrace p s x = 0} := by
  have h1 := additive_fiber_injective_iff (squareFieldTrace p s) L (squareTraceOne p s)
  have h0 := additive_fiber_injective_iff (squareFieldTrace p s) L 0
  rw [squareTraceOne_trace] at h1
  rw [map_zero] at h0
  exact h1.trans h0.symm

/-- Every fiber is either empty or has the same kernel obstruction. -/
theorem squareFieldTrace_injOn_fiber_iff (s : ℕ)
    (L : SquareConstantField p s →+ SquareConstantField p s) (a : SquareConstantField p s) :
    Set.InjOn L {x | squareFieldTrace p s x = a} ↔
      a ∉ squareFrobeniusFixedField p s ∨
        ∀ x, squareFieldTrace p s x = 0 → L x = 0 → x = 0 := by
  by_cases ha : a ∈ squareFrobeniusFixedField p s
  · obtain ⟨u, hu⟩ := (squareFieldTrace_exists_iff p s a).mpr ha
    rw [or_iff_right (not_not.mpr ha)]
    simpa only [hu] using additive_fiber_injective_iff (squareFieldTrace p s) L u
  · constructor
    · intro _; exact Or.inl ha
    · intro _ x hx
      exact False.elim (ha ((squareFieldTrace_exists_iff p s a).mp ⟨x, hx⟩))

/-- Frobenius powers with arbitrary field coefficients define an additive polynomial. -/
def squareFieldLinearizedMap (s : ℕ) {k : ℕ} (c : Fin k → SquareConstantField p s) :
    SquareConstantField p s →+ SquareConstantField p s where
  toFun x := ∑ i, c i * x ^ p ^ (i : ℕ)
  map_zero' := by
    have hp : p ≠ 0 := (Fact.out : p.Prime).ne_zero
    simp only [zero_pow (pow_ne_zero _ hp), mul_zero, sum_const_zero]
  map_add' x y := by
    simp only [add_pow_char_pow, mul_add, sum_add_distrib]

/-- Linearized polynomials are injective on the trace-one fiber exactly when
their zero set meets the trace-zero fiber only at zero. -/
theorem squareFieldLinearized_injOn_one_iff (s : ℕ) {k : ℕ}
    (c : Fin k → SquareConstantField p s) :
    Set.InjOn (fun x : SquareConstantField p s => ∑ i, c i * x ^ p ^ (i : ℕ))
      {x | squareFieldTrace p s x = 1} ↔
      ∀ x : SquareConstantField p s,
        squareFieldTrace p s x = 0 → (∑ i, c i * x ^ p ^ (i : ℕ)) = 0 → x = 0 := by
  have h := additive_fiber_injective_iff (squareFieldTrace p s)
    (squareFieldLinearizedMap p s c) (squareTraceOne p s)
  rw [squareTraceOne_trace] at h
  exact h

#print axioms squareFieldTrace_injOn_one_iff_zero
#print axioms squareFieldTrace_injOn_fiber_iff
#print axioms squareFieldLinearized_injOn_one_iff

end
end GaloisForLFunctions.ArithmeticCastelnuovoSeveri
