import GaloisForLFunctions.HTGeometry.TranslationShiftAffineRigidity

/-!
# A rational function cannot have a nonzero constant scaling defect

If `R(λz) = R(z) + c` for a rational `R` and `λ ≠ 0`, then `c = 0`.

Coprimality is preserved by the scaling substitution, so the scaled denominator divides the
denominator; the two have the same degree, hence differ by a unit.  Cancelling reduces the relation
to the numerators, and evaluating at the fixed point `0` finishes whenever the denominator does not
vanish there.  When it does, the unit is `1`, the denominator is scaling invariant, so `λ` is a root
of unity, and iterating the numerator relation through a full period returns `p` while adding a
nonzero multiple of `q`.

Together with the parabolic case this is the complete translation-stabilizer dichotomy: a Möbius
reparametrization realizing a nonzero constant shift of a rational function must be parabolic, and
then the function is affine.

* `GaloisForLFunctions.HTGeometry.scale_const_quotient_eq_zero`.
-/

namespace GaloisForLFunctions.HTGeometry

open Polynomial

/-- The scaling substitution is a coefficientwise dilation. -/
theorem natDegree_comp_C_mul_X {lam : ℂ} (hlam : lam ≠ 0) (p : ℂ[X]) :
    (p.comp (C lam * X)).natDegree = p.natDegree := by
  have hdeg : (C lam * X).natDegree = 1 := by
    rw [natDegree_C_mul hlam, natDegree_X]
  rw [natDegree_comp, hdeg, mul_one]

theorem comp_C_mul_X_ne_zero {lam : ℂ} (hlam : lam ≠ 0) {p : ℂ[X]} (hp : p ≠ 0) :
    p.comp (C lam * X) ≠ 0 := by
  intro h0
  have hcoeff : (p.comp (C lam * X)).coeff p.natDegree = p.coeff p.natDegree * lam ^ p.natDegree :=
    comp_C_mul_X_coeff
  rw [h0, coeff_zero] at hcoeff
  have hlead : p.coeff p.natDegree ≠ 0 := by
    rw [← leadingCoeff]
    exact leadingCoeff_ne_zero.2 hp
  exact (mul_ne_zero hlead (pow_ne_zero _ hlam)) hcoeff.symm

theorem comp_C_mul_X_comp_C_mul_X (p : ℂ[X]) (lam : ℂ) (j : ℕ) :
    (p.comp (C (lam ^ j) * X)).comp (C lam * X) = p.comp (C (lam ^ (j + 1)) * X) := by
  rw [comp_assoc]
  congr 1
  rw [mul_comp, C_comp, X_comp, ← mul_assoc, ← C_mul, pow_succ]

/-- **A rational function has no nonzero constant scaling defect.**  In terms of a coprime
representation `p/q`, the relation `p(λX)·q = (p + c·q)·q(λX)` with `λ ≠ 0` forces `c = 0`. -/
theorem scale_const_quotient_eq_zero {p q : ℂ[X]} {c lam : ℂ} (hq : q ≠ 0) (hlam : lam ≠ 0)
    (hco : IsCoprime p q)
    (h : p.comp (C lam * X) * q = (p + C c * q) * q.comp (C lam * X)) :
    c = 0 := by
  classical
  set A : ℂ[X] := q.comp (C lam * X) with hA
  have hAne : A ≠ 0 := comp_C_mul_X_ne_zero hlam hq
  have hcs : IsCoprime (p.comp (C lam * X)) A := by
    have hmap := hco.map (Polynomial.aeval (C lam * X) : ℂ[X] →ₐ[ℂ] ℂ[X]).toRingHom
    simpa only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, ← comp_eq_aeval, hA] using hmap
  have hdvd : A ∣ q := by
    refine (hcs.symm).dvd_of_dvd_mul_left ?_
    exact ⟨p + C c * q, by rw [hA, h]; ring⟩
  obtain ⟨t, ht⟩ := hdvd
  have htne : t ≠ 0 := by
    intro h0
    rw [h0, mul_zero] at ht
    exact hq ht
  have hdegA : A.natDegree = q.natDegree := natDegree_comp_C_mul_X hlam q
  have hdegt : t.natDegree = 0 := by
    have := natDegree_mul hAne htne
    rw [← ht, hdegA] at this
    omega
  obtain ⟨u, hu⟩ : ∃ u : ℂ, t = C u := ⟨t.coeff 0, (eq_C_of_natDegree_eq_zero hdegt)⟩
  have hqA : q = C u * A := by rw [ht, hu]; ring
  have hnum : C u * p.comp (C lam * X) = p + C c * q := by
    have hcancel : (C u * p.comp (C lam * X)) * A = (p + C c * q) * A := by
      calc (C u * p.comp (C lam * X)) * A = p.comp (C lam * X) * (C u * A) := by ring
        _ = p.comp (C lam * X) * q := by rw [← hqA]
        _ = (p + C c * q) * A := by rw [hA] at h ⊢; exact h
    exact mul_right_cancel₀ hAne hcancel
  have heval0 : (p.comp (C lam * X)).eval 0 = p.eval 0 := by
    rw [eval_comp]
    simp
  have hi : u * p.eval 0 = p.eval 0 + c * q.eval 0 := by
    have := congrArg (Polynomial.eval (0 : ℂ)) hnum
    simpa only [eval_mul, eval_C, eval_add, heval0] using this
  have hii : q.eval 0 = u * (A.eval 0) := by
    have := congrArg (Polynomial.eval (0 : ℂ)) hqA
    simpa only [eval_mul, eval_C] using this
  have hAeval : A.eval 0 = q.eval 0 := by
    rw [hA, eval_comp]
    simp
  rw [hAeval] at hii
  by_cases hq0 : q.eval 0 = 0
  · -- the denominator vanishes at the fixed point
    have hp0 : p.eval 0 ≠ 0 := by
      obtain ⟨a, b, hab⟩ := hco
      intro hzero
      have := congrArg (Polynomial.eval (0 : ℂ)) hab
      rw [eval_add, eval_mul, eval_mul, eval_one, hzero, hq0, mul_zero, mul_zero,
        add_zero] at this
      exact zero_ne_one this
    have hu1 : u = 1 := by
      rw [hq0, mul_zero, add_zero] at hi
      exact mul_right_cancel₀ hp0 (by rw [hi, one_mul])
    have hqfix : q.comp (C lam * X) = q := by
      rw [← hA, hqA, hu1, map_one, one_mul]
    have hN : q.natDegree ≠ 0 := by
      intro h0
      have hqC : q = C (q.coeff 0) := eq_C_of_natDegree_eq_zero h0
      have : q.eval 0 = q.coeff 0 := by rw [hqC]; simp
      rw [hq0] at this
      exact hq (by rw [hqC, ← this, map_zero])
    have hroot : lam ^ q.natDegree = 1 := by
      have hcoeff : q.coeff q.natDegree * lam ^ q.natDegree = q.coeff q.natDegree := by
        have := congrArg (fun f : ℂ[X] => f.coeff q.natDegree) hqfix
        simpa only [comp_C_mul_X_coeff] using this
      have hlead : q.coeff q.natDegree ≠ 0 := by
        rw [← leadingCoeff]
        exact leadingCoeff_ne_zero.2 hq
      have hmul : q.coeff q.natDegree * lam ^ q.natDegree = q.coeff q.natDegree * 1 := by
        rw [mul_one]
        exact hcoeff
      exact mul_left_cancel₀ hlead hmul
    have hpnum : p.comp (C lam * X) = p + C c * q := by
      rw [← hnum, hu1, map_one, one_mul]
    have hiter : ∀ j : ℕ, p.comp (C (lam ^ j) * X) = p + C ((j : ℂ) * c) * q := by
      intro j
      induction j with
      | zero => simp
      | succ j ih =>
          rw [← comp_C_mul_X_comp_C_mul_X, ih, add_comp, mul_comp, C_comp, hpnum, hqfix]
          rw [Nat.cast_add, Nat.cast_one, add_mul, one_mul, C_add]
          ring
    have hfull := hiter q.natDegree
    rw [hroot, map_one, one_mul, comp_X] at hfull
    have hzero : C (((q.natDegree : ℂ)) * c) * q = 0 := by
      have : p + C ((q.natDegree : ℂ) * c) * q = p + 0 := by rw [add_zero]; exact hfull.symm
      exact add_left_cancel this
    have hcz : ((q.natDegree : ℂ)) * c = 0 := by
      rcases mul_eq_zero.1 hzero with hC | hqz
      · exact (map_eq_zero_iff C C_injective).1 hC
      · exact absurd hqz hq
    have hNc : ((q.natDegree : ℂ)) ≠ 0 := Nat.cast_ne_zero.2 hN
    exact (mul_eq_zero.1 hcz).resolve_left hNc
  · -- the denominator is nonzero at the fixed point
    have hu1 : u = 1 := by
      exact mul_right_cancel₀ hq0 (by rw [one_mul]; exact hii.symm)
    rw [hu1, one_mul] at hi
    have : c * q.eval 0 = 0 := by linear_combination -hi
    exact (mul_eq_zero.1 this).resolve_right hq0

end GaloisForLFunctions.HTGeometry
