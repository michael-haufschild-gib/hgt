import GaloisForLFunctions.RHTower.SquarefreeCoronaPrimeCurrentField

/-!
# The prime-winning face unit is a unit on the strict critical half-plane

Each face of the prime-winning cover contributes the transition factor

```text
R_{p,m}(s) = p^{-ms} (1 - p^{-s}) / (1 - p^{-(m+1)s}),
```

and the face unit is `U_{F,m}(s) = ζ((m+1)s)⁻¹ ∏_{p ∈ F} R_{p,m}(s)`.  For `m ≥ 1` and
`Re s > 1/2` every ingredient is holomorphic and nonvanishing: the doubled abscissa
`Re((m+1)s) > 1` keeps `ζ((m+1)s)` off its zeros, and the local factors are geometric.  Hence the
face unit is invertible throughout the strict critical half-plane, and adjoining one prime to a
face multiplies it by that prime's transition factor alone — a flat rank-one system on the
finite-subset nerve.
-/

open Complex

noncomputable section

namespace RHTower

/-- The face transition factor `R_{p,m}(s)`. -/
def faceTransitionUnit (p : Nat.Primes) (m : ℕ) (s : ℂ) : ℂ :=
  (((p : ℕ) : ℂ) ^ (-((m : ℂ) * s)) * (1 - ((p : ℕ) : ℂ) ^ (-s))) /
    (1 - ((p : ℕ) : ℂ) ^ (-(((m : ℂ) + 1) * s)))

/-- The face unit `U_{F,m}(s)`. -/
def faceUnit (F : Finset Nat.Primes) (m : ℕ) (s : ℂ) : ℂ :=
  (riemannZeta (((m : ℂ) + 1) * s))⁻¹ * ∏ p ∈ F, faceTransitionUnit p m s

/-! ## Local nonvanishing -/

theorem norm_primeCpow_neg_lt_one {s : ℂ} (hs : 0 < s.re) (p : Nat.Primes) :
    ‖((p : ℕ) : ℂ) ^ (-s)‖ < 1 := by
  rw [norm_primeCpowNeg]
  exact Real.rpow_lt_one_of_one_lt_of_neg (by exact_mod_cast p.prop.one_lt) (by simpa using hs)

theorem one_sub_primeCpow_neg_ne_zero {s : ℂ} (hs : 0 < s.re) (p : Nat.Primes) :
    1 - ((p : ℕ) : ℂ) ^ (-s) ≠ 0 := by
  intro h
  have hval : ((p : ℕ) : ℂ) ^ (-s) = 1 := by
    have := sub_eq_zero.mp h
    exact this.symm
  have hlt := norm_primeCpow_neg_lt_one hs p
  rw [hval, norm_one] at hlt
  exact lt_irrefl 1 hlt

theorem primeCpow_neg_ne_zero (z : ℂ) (p : Nat.Primes) :
    ((p : ℕ) : ℂ) ^ z ≠ 0 := by
  rw [Ne, Complex.cpow_eq_zero_iff]
  intro h
  exact (Nat.cast_ne_zero.mpr p.prop.ne_zero) (by exact_mod_cast h.1)

/-- The doubled abscissa of a face lies in the Euler half-plane. -/
theorem one_lt_re_succ_mul {m : ℕ} (hm : 1 ≤ m) {s : ℂ} (hs : 1 / 2 < s.re) :
    1 < ((((m : ℂ) + 1) * s)).re := by
  have hcast : ((((m : ℂ) + 1) * s)).re = ((m : ℝ) + 1) * s.re := by
    simp [Complex.mul_re, Complex.add_re, Complex.natCast_re, Complex.add_im,
      Complex.natCast_im]
  rw [hcast]
  have hm' : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  nlinarith

theorem faceTransitionUnit_ne_zero {m : ℕ} (hm : 1 ≤ m) {s : ℂ} (hs : 1 / 2 < s.re)
    (p : Nat.Primes) : faceTransitionUnit p m s ≠ 0 := by
  have hs0 : 0 < s.re := by linarith
  have hnum1 : ((p : ℕ) : ℂ) ^ (-((m : ℂ) * s)) ≠ 0 := primeCpow_neg_ne_zero _ p
  have hnum2 : 1 - ((p : ℕ) : ℂ) ^ (-s) ≠ 0 := one_sub_primeCpow_neg_ne_zero hs0 p
  have hden : 1 - ((p : ℕ) : ℂ) ^ (-(((m : ℂ) + 1) * s)) ≠ 0 := by
    apply one_sub_primeCpow_neg_ne_zero
    have := one_lt_re_succ_mul hm hs
    linarith
  rw [faceTransitionUnit]
  exact div_ne_zero (mul_ne_zero hnum1 hnum2) hden

/-- **The face unit is invertible on the strict critical half-plane.** -/
theorem faceUnit_ne_zero {m : ℕ} (hm : 1 ≤ m) {s : ℂ} (hs : 1 / 2 < s.re)
    (F : Finset Nat.Primes) : faceUnit F m s ≠ 0 := by
  have hzeta : riemannZeta (((m : ℂ) + 1) * s) ≠ 0 :=
    riemannZeta_ne_zero_of_one_lt_re (one_lt_re_succ_mul hm hs)
  rw [faceUnit]
  refine mul_ne_zero (inv_ne_zero hzeta) ?_
  exact Finset.prod_ne_zero_iff.mpr fun p _ => faceTransitionUnit_ne_zero hm hs p

/-! ## Holomorphy -/

theorem differentiableAt_faceTransitionUnit {m : ℕ} (hm : 1 ≤ m) {s : ℂ} (hs : 1 / 2 < s.re)
    (p : Nat.Primes) :
    DifferentiableAt ℂ (fun z => faceTransitionUnit p m z) s := by
  have hne : (((p : ℕ) : ℂ)) ≠ 0 := by
    exact_mod_cast Nat.cast_ne_zero.mpr p.prop.ne_zero
  have hs0 : 0 < s.re := by linarith
  have hpow : ∀ c : ℂ, DifferentiableAt ℂ (fun z : ℂ => ((p : ℕ) : ℂ) ^ (-(c * z))) s := by
    intro c
    exact (((differentiable_id.const_mul c).neg).const_cpow (Or.inl hne)).differentiableAt
  have hpow' : DifferentiableAt ℂ (fun z : ℂ => ((p : ℕ) : ℂ) ^ (-z)) s :=
    ((differentiable_neg).const_cpow (Or.inl hne)).differentiableAt
  have hden : 1 - ((p : ℕ) : ℂ) ^ (-(((m : ℂ) + 1) * s)) ≠ 0 := by
    apply one_sub_primeCpow_neg_ne_zero
    have := one_lt_re_succ_mul hm hs
    linarith
  exact ((hpow (m : ℂ)).mul ((differentiableAt_const 1).sub hpow')).div
    ((differentiableAt_const 1).sub (hpow ((m : ℂ) + 1))) hden

theorem differentiableAt_faceUnit {m : ℕ} (hm : 1 ≤ m) {s : ℂ} (hs : 1 / 2 < s.re)
    (F : Finset Nat.Primes) :
    DifferentiableAt ℂ (fun z => faceUnit F m z) s := by
  have hzeta : riemannZeta (((m : ℂ) + 1) * s) ≠ 0 :=
    riemannZeta_ne_zero_of_one_lt_re (one_lt_re_succ_mul hm hs)
  have hone : (((m : ℂ) + 1) * s) ≠ 1 := by
    intro h
    have := one_lt_re_succ_mul hm hs
    rw [h] at this
    simp at this
  have hzetaDiff : DifferentiableAt ℂ (fun z : ℂ => riemannZeta (((m : ℂ) + 1) * z)) s :=
    (differentiableAt_riemannZeta hone).comp s (by fun_prop)
  refine (hzetaDiff.inv hzeta).mul ?_
  exact DifferentiableAt.fun_finsetProd fun p _ => differentiableAt_faceTransitionUnit hm hs p

/-! ## The flat transition law -/

/-- **Flat rank-one transition.**  Adjoining one prime to a face multiplies the face unit by that
prime's transition factor, independently of the face. -/
theorem faceUnit_insert {F : Finset Nat.Primes} {p : Nat.Primes} (hp : p ∉ F) (m : ℕ) (s : ℂ) :
    faceUnit (insert p F) m s = faceTransitionUnit p m s * faceUnit F m s := by
  rw [faceUnit, faceUnit, Finset.prod_insert hp]
  ring

end RHTower
