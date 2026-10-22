import GaloisForLFunctions.RHTower.Suzuki.SuzukiPacketCoefficientSeries
import GaloisForLFunctions.RHTower.Suzuki.SuzukiTailSummatoryErrorTransform

/-!
# The shifted Euler quotient is a positive twisted cocycle with zero algebraic curvature

For a nonzero function `F` the full shifted quotient is

`R_ω(s) = F(s - ω) / F(s + ω)`.

It satisfies the exact nonperturbative twisted-cocycle law `R_{ω+η}(s) = R_ω(s-η) R_η(s+ω)`, whose
associativity curvature vanishes identically: both bracketings of `R_{ω+η+κ}` give the *same*
three-factor product, because the law is the exact ratio coboundary of `F` and the intermediate
values of `F` cancel.

For `F = ζ` the Euler coefficient streams `c_ω(n) = n^ω ∏_{p ∣ n}(1 - p^{-2ω})` are strictly
positive off `n = 1` (where the value is `1`), and the cocycle law is the twisted Dirichlet
convolution `c_{ω+η} = (n ↦ n^η c_ω(n)) ⍟ (n ↦ n^{-ω} c_η(n))`.

Nothing here is an obstruction: the uncompressed full-shift law is flat.  The Route C object is the
compressed Schur curvature, which is *not* covered by these identities.

The coefficient stream, its `ζ(s-ω)/ζ(s+ω)` Dirichlet series and the convolution factorisation are
the corpus's `RHTower.suzukiShiftedCoefficient`, `RHTower.LSeries_suzukiShiftedCoefficient` and
`RHTower.suzukiCoeffAF_eq_convolution`.
-/

open ArithmeticFunction GaloisForLFunctions.HTGeometry
open scoped ArithmeticFunction

namespace RHTower

noncomputable section

/-! ## The exact twisted cocycle and its vanishing curvature -/

/-- The full shifted quotient `R_ω(s) = F(s-ω)/F(s+ω)`. -/
def shiftedQuotient (F : ℂ → ℂ) (omega : ℝ) (s : ℂ) : ℂ :=
  F (s - (omega : ℂ)) / F (s + (omega : ℂ))

/-- **Theorem A, equation (3).**  The exact twisted-cocycle law.  The only side condition is that
the intermediate value of `F` — the one that telescopes away — is nonzero, which is exactly where
the middle quotient is defined. -/
theorem shiftedQuotient_cocycle (F : ℂ → ℂ) (omega eta : ℝ) (s : ℂ)
    (hmid : F (s + (omega : ℂ) - (eta : ℂ)) ≠ 0) :
    shiftedQuotient F (omega + eta) s =
      shiftedQuotient F omega (s - (eta : ℂ)) * shiftedQuotient F eta (s + (omega : ℂ)) := by
  unfold shiftedQuotient
  push_cast
  rw [show (s - (eta : ℂ) + (omega : ℂ)) = (s + (omega : ℂ) - (eta : ℂ)) by ring,
    show (s - (eta : ℂ) - (omega : ℂ)) = (s - ((omega : ℂ) + (eta : ℂ))) by ring,
    show (s + ((omega : ℂ) + (eta : ℂ))) = (s + (omega : ℂ) + (eta : ℂ)) by ring,
    div_mul_div_comm,
    mul_comm (F (s - ((omega : ℂ) + (eta : ℂ))))
      (F (s + (omega : ℂ) - (eta : ℂ))),
    mul_div_mul_left _ _ hmid]

/-- **Theorem C, equation (6).**  Splitting `(ω+η)+κ` first at `ω+η` produces the canonical
three-factor product. -/
theorem shiftedQuotient_triple_left (F : ℂ → ℂ) (omega eta kappa : ℝ) (s : ℂ)
    (h1 : F (s + (omega : ℂ) + (eta : ℂ) - (kappa : ℂ)) ≠ 0)
    (h2 : F (s + (omega : ℂ) - (eta : ℂ) - (kappa : ℂ)) ≠ 0) :
    shiftedQuotient F (omega + eta + kappa) s =
      shiftedQuotient F omega (s - (eta : ℂ) - (kappa : ℂ)) *
        shiftedQuotient F eta (s + (omega : ℂ) - (kappa : ℂ)) *
        shiftedQuotient F kappa (s + (omega : ℂ) + (eta : ℂ)) := by
  have hstep := shiftedQuotient_cocycle F (omega + eta) kappa s (by
    have hrw : (s + (((omega + eta : ℝ)) : ℂ) - (kappa : ℂ))
        = (s + (omega : ℂ) + (eta : ℂ) - (kappa : ℂ)) := by push_cast; ring
    rw [hrw]
    exact h1)
  rw [hstep]
  have hinner := shiftedQuotient_cocycle F omega eta (s - (kappa : ℂ)) (by
    have hrw : ((s - (kappa : ℂ)) + (omega : ℂ) - (eta : ℂ))
        = (s + (omega : ℂ) - (eta : ℂ) - (kappa : ℂ)) := by ring
    rw [hrw]
    exact h2)
  rw [hinner,
    show (s - (kappa : ℂ) - (eta : ℂ)) = (s - (eta : ℂ) - (kappa : ℂ)) by ring,
    show (s - (kappa : ℂ) + (omega : ℂ)) = (s + (omega : ℂ) - (kappa : ℂ)) by ring,
    show (((omega + eta : ℝ)) : ℂ) = (omega : ℂ) + (eta : ℂ) by push_cast; ring,
    show (s + ((omega : ℂ) + (eta : ℂ))) = (s + (omega : ℂ) + (eta : ℂ)) by ring]

/-- **Theorem C, equation (6), the other bracketing.**  Splitting `ω+(η+κ)` first at `η+κ`
produces the *same* three-factor product. -/
theorem shiftedQuotient_triple_right (F : ℂ → ℂ) (omega eta kappa : ℝ) (s : ℂ)
    (h1 : F (s + (omega : ℂ) - (eta : ℂ) - (kappa : ℂ)) ≠ 0)
    (h2 : F (s + (omega : ℂ) + (eta : ℂ) - (kappa : ℂ)) ≠ 0) :
    shiftedQuotient F (omega + (eta + kappa)) s =
      shiftedQuotient F omega (s - (eta : ℂ) - (kappa : ℂ)) *
        shiftedQuotient F eta (s + (omega : ℂ) - (kappa : ℂ)) *
        shiftedQuotient F kappa (s + (omega : ℂ) + (eta : ℂ)) := by
  have hstep := shiftedQuotient_cocycle F omega (eta + kappa) s (by
    have hrw : (s + (omega : ℂ) - (((eta + kappa : ℝ)) : ℂ))
        = (s + (omega : ℂ) - (eta : ℂ) - (kappa : ℂ)) := by push_cast; ring
    rw [hrw]
    exact h1)
  rw [hstep]
  have hinner := shiftedQuotient_cocycle F eta kappa (s + (omega : ℂ)) (by
    have hrw : ((s + (omega : ℂ)) + (eta : ℂ) - (kappa : ℂ))
        = (s + (omega : ℂ) + (eta : ℂ) - (kappa : ℂ)) := by ring
    rw [hrw]
    exact h2)
  rw [hinner,
    show (((eta + kappa : ℝ)) : ℂ) = (eta : ℂ) + (kappa : ℂ) by push_cast; ring,
    show (s - ((eta : ℂ) + (kappa : ℂ))) = (s - (eta : ℂ) - (kappa : ℂ)) by ring]
  ring

/-- **Zero algebraic curvature.**  The two iterated decompositions of `R_{ω+η+κ}` are equal, so the
associativity curvature of the full shifted quotient vanishes identically. -/
theorem shiftedQuotient_curvature_eq (F : ℂ → ℂ) (omega eta kappa : ℝ) (s : ℂ)
    (h1 : F (s + (omega : ℂ) + (eta : ℂ) - (kappa : ℂ)) ≠ 0)
    (h2 : F (s + (omega : ℂ) - (eta : ℂ) - (kappa : ℂ)) ≠ 0) :
    shiftedQuotient F (omega + eta + kappa) s = shiftedQuotient F (omega + (eta + kappa)) s := by
  rw [shiftedQuotient_triple_left F omega eta kappa s h1 h2,
    shiftedQuotient_triple_right F omega eta kappa s h2 h1]

/-! ## Euler positivity of the coefficient streams -/

/-- `c_ω(1) = 1`. -/
@[simp]
theorem suzukiShiftedCoefficient_one (omega : ℝ) : suzukiShiftedCoefficient omega 1 = 1 := by
  simp [suzukiShiftedCoefficient]

/-- **Theorem B, equation (5).**  Every Euler coefficient stream is strictly positive on the
positive integers. -/
theorem suzukiShiftedCoefficient_pos {omega : ℝ} (homega : 0 < omega) {n : ℕ} (hn : 0 < n) :
    0 < suzukiShiftedCoefficient omega n := by
  rw [suzukiShiftedCoefficient]
  refine mul_pos (Real.rpow_pos_of_pos (by exact_mod_cast hn) omega) ?_
  refine Finset.prod_pos fun p hp => ?_
  have hp2 : (2 : ℕ) ≤ p := (Nat.prime_of_mem_primeFactors hp).two_le
  have hp1 : (1 : ℝ) < (p : ℝ) := by exact_mod_cast lt_of_lt_of_le one_lt_two hp2
  have hlt : (p : ℝ) ^ (-2 * omega) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg hp1 (by linarith)
  linarith

/-! ## The twisted Dirichlet convolution -/

theorem dirichletShift_one (a : ℂ) : dirichletShift a (1 : ArithmeticFunction ℂ) = 1 := by
  ext n
  rcases eq_or_ne n 1 with rfl | hn
  · simp [dirichletShift_apply, cpowWeight]
  · simp [dirichletShift_apply, hn]

/-- **Theorem A, equation (4).**  The cocycle law read on coefficients: the shifted Euler stream at
`ω + η` is the twisted Dirichlet convolution of the `η`-twisted stream at `ω` with the
`(-ω)`-twisted stream at `η`. -/
theorem suzukiCoeffAF_add_eq_twistedConvolution (omega eta : ℝ) :
    suzukiCoeffAF (omega + eta) =
      dirichletShift (-((eta : ℝ) : ℂ)) (suzukiCoeffAF omega) *
        dirichletShift (((omega : ℝ) : ℂ)) (suzukiCoeffAF eta) := by
  classical
  set Z : ArithmeticFunction ℂ := ((zeta : ArithmeticFunction ℕ) : ArithmeticFunction ℂ) with hZ
  set M : ArithmeticFunction ℂ := ((moebius : ArithmeticFunction ℤ) : ArithmeticFunction ℂ) with hM
  have hMZ : M * Z = 1 := by
    rw [hM, hZ]
    exact coe_moebius_mul_coe_zeta
  rw [suzukiCoeffAF_eq_convolution, suzukiCoeffAF_eq_convolution, suzukiCoeffAF_eq_convolution,
    ← hZ, ← hM, dirichletShift_mul, dirichletShift_mul,
    dirichletShift_dirichletShift, dirichletShift_dirichletShift,
    dirichletShift_dirichletShift, dirichletShift_dirichletShift]
  have e1 : (-((eta : ℝ) : ℂ) + -((omega : ℝ) : ℂ)) = -(((omega + eta : ℝ)) : ℂ) := by
    push_cast
    ring
  have e2 : (-((eta : ℝ) : ℂ) + ((omega : ℝ) : ℂ)) = ((omega : ℂ) - (eta : ℂ)) := by
    ring
  have e3 : (((omega : ℝ) : ℂ) + -((eta : ℝ) : ℂ)) = ((omega : ℂ) - (eta : ℂ)) := by
    ring
  have e4 : (((omega : ℝ) : ℂ) + ((eta : ℝ) : ℂ)) = (((omega + eta : ℝ)) : ℂ) := by
    push_cast
    ring
  rw [e1, e2, e3, e4]
  have hcancel :
      dirichletShift ((omega : ℂ) - (eta : ℂ)) M * dirichletShift ((omega : ℂ) - (eta : ℂ)) Z
        = 1 := by
    rw [← dirichletShift_mul, hMZ, dirichletShift_one]
  calc dirichletShift (-(((omega + eta : ℝ)) : ℂ)) Z *
        dirichletShift (((omega + eta : ℝ)) : ℂ) M
      = dirichletShift (-(((omega + eta : ℝ)) : ℂ)) Z *
          (dirichletShift ((omega : ℂ) - (eta : ℂ)) M *
            dirichletShift ((omega : ℂ) - (eta : ℂ)) Z) *
          dirichletShift (((omega + eta : ℝ)) : ℂ) M := by rw [hcancel]; ring
    _ = dirichletShift (-(((omega + eta : ℝ)) : ℂ)) Z *
          dirichletShift ((omega : ℂ) - (eta : ℂ)) M *
          (dirichletShift ((omega : ℂ) - (eta : ℂ)) Z *
            dirichletShift (((omega + eta : ℝ)) : ℂ) M) := by ring

/-! ## The Dirichlet-series reading of the quotient -/

/-- **Equation (2).**  On the common Euler half-plane the shifted zeta quotient is the ordinary
Dirichlet series of the coefficient stream `c_ω`. -/
theorem shiftedQuotient_riemannZeta_eq_LSeries (omega : ℝ) {s : ℂ}
    (h1 : 1 < (s - (omega : ℂ)).re) (h2 : 1 < (s + (omega : ℂ)).re) :
    shiftedQuotient riemannZeta omega s
      = LSeries (fun n => ((suzukiShiftedCoefficient omega n : ℝ) : ℂ)) s := by
  rw [LSeries_suzukiShiftedCoefficient omega h1 h2, shiftedQuotient]

end

end RHTower
