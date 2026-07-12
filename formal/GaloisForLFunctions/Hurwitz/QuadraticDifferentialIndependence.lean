import GaloisForLFunctions.Hurwitz.AllNHZeta
import GaloisForLFunctions.Hurwitz.LadderDeformation

/-!
# Quadratic differential independence of Hurwitz zeta in its shift

The classical shift-derivative identity identifies the finite differential jet of
`a ↦ ζ(s,a)` with the shifted-exponent ladder `ζ(s+k,a)`.  Combining that exact value relation
with the all-`N` quadratic ladder theorem gives quadratic differential independence of the single
Hurwitz function.
-/

open Complex HurwitzZetaShift Polynomial

namespace HurwitzLadder

/-- **Quadratic differential independence in the Hurwitz shift.**  Fix a nonintegral exponent
`s` with `Re s > 1`.  A polynomial-coefficient differential relation of total degree at most two
among any finite jet of `a ↦ ζ(s,a)`, valid on the upper half-plane, has only zero coefficients. -/
theorem hzeta_quadratic_differential_independent
    {N : ℕ} {s : ℂ} (hs1 : 1 < s.re)
    (hsZ : ∀ k : ℤ, (k : ℂ) ≠ s)
    (q : Fin (N + 1) → Fin (N + 1) → Polynomial ℂ)
    (l : Fin (N + 1) → Polynomial ℂ) (cc : Polynomial ℂ)
    (hSymm : ∀ i j, q i j = q j i)
    (hrel : ∀ a : ℂ, 0 < a.im →
      (∑ i : Fin (N + 1), ∑ j : Fin (N + 1), (q i j).eval a
          * (iteratedDeriv (i : ℕ) (hzeta s) a * iteratedDeriv (j : ℕ) (hzeta s) a))
        + (∑ k : Fin (N + 1), (l k).eval a * iteratedDeriv (k : ℕ) (hzeta s) a)
        + cc.eval a = 0) :
    (∀ i j, q i j = 0) ∧ (∀ j, l j = 0) ∧ cc = 0 := by
  let c : Fin (N + 1) → ℂ := fun i =>
    (-1 : ℂ) ^ (i : ℕ) * (ascPochhammer ℂ (i : ℕ)).eval s
  let q' : Fin (N + 1) → Fin (N + 1) → Polynomial ℂ := fun i j =>
    Polynomial.C (c i * c j) * q i j
  let l' : Fin (N + 1) → Polynomial ℂ := fun i => Polynomial.C (c i) * l i
  have hc : ∀ i, c i ≠ 0 := by
    intro i
    exact mul_ne_zero (pow_ne_zero _ (by norm_num))
      (ascPochhammer_eval_ne_zero_of_one_lt_re (i : ℕ) hs1)
  have hSymm' : ∀ i j, q' i j = q' j i := by
    intro i j
    dsimp [q']
    rw [hSymm i j]
    congr 1
    ring_nf
  have hrel' : ∀ a : ℂ, 0 < a.im →
      (∑ i : Fin (N + 1), ∑ j : Fin (N + 1), (q' i j).eval a
          * (hzeta (s + (i : ℂ)) a * hzeta (s + (j : ℂ)) a))
        + (∑ k : Fin (N + 1), (l' k).eval a * hzeta (s + (k : ℂ)) a)
        + cc.eval a = 0 := by
    intro a ha
    have h := hrel a ha
    have hjet : ∀ i : Fin (N + 1), iteratedDeriv (i : ℕ) (hzeta s) a =
        c i * hzeta (s + (i : ℂ)) a := by
      intro i
      simpa [c] using hzeta_iteratedDeriv (i : ℕ) hs1 (a := a) ha
    simp_rw [hjet] at h
    simpa [q', l', Polynomial.eval_mul, Polynomial.eval_C, mul_assoc, mul_left_comm,
      mul_comm] using h
  obtain ⟨hq', hl', hcc⟩ :=
    HurwitzAllNHZeta.hurwitz_allN_hzeta_upper_half_plane hs1 hsZ q' l' cc hSymm' hrel'
  refine ⟨?_, ?_, hcc⟩
  · intro i j
    have hmul := hq' i j
    dsimp [q'] at hmul
    exact (mul_eq_zero.mp hmul).resolve_left
      (Polynomial.C_ne_zero.mpr (mul_ne_zero (hc i) (hc j)))
  · intro i
    have hmul := hl' i
    dsimp [l'] at hmul
    exact (mul_eq_zero.mp hmul).resolve_left (Polynomial.C_ne_zero.mpr (hc i))

end HurwitzLadder
