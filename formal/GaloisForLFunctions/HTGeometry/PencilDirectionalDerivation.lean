import GaloisForLFunctions.HTGeometry.EulerOperatorDiagonal

/-!
# The directional derivation of a pencil carrier is the Euler operator

A pencil carrier along the facet phase `L` has the shape `z ↦ Ψ (exp (L z))`.  Differentiating in a
constant direction `w` moves the inner exponential by the constant factor `L w`, so

```text
D_w (Ψ ∘ exp ∘ L) = L w · (Θ Ψ) ∘ exp ∘ L,    Θ Ψ (u) = u · Ψ'(u),
```

and iterating replaces `Θ` by `Θ^r` and `L w` by `(L w)^r`.  Since `Θ` multiplies the `m`-th inner
Taylor coefficient by `m`, an `r`-fold directional derivative multiplies it by `(m · L w)^r`.

* `dirDeriv` — the directional derivative;
* `phaseComp` — the carrier shape;
* `dirDeriv_phaseComp`, `dirDeriv_iterate_phaseComp` — the bridge;
* `iteratedDeriv_inner_dirDeriv_iterate` — the resulting diagonal action on inner coefficients.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {d : ℕ}

/-- The derivative in a constant direction. -/
def dirDeriv (w : Fin d → ℂ) (f : (Fin d → ℂ) → ℂ) : (Fin d → ℂ) → ℂ :=
  fun z => deriv (fun t : ℂ => f (z + t • w)) 0

/-- A carrier read through a facet phase. -/
def phaseComp (L : (Fin d → ℂ) →ₗ[ℂ] ℂ) (Ψ : ℂ → ℂ) : (Fin d → ℂ) → ℂ :=
  fun z => Ψ (Complex.exp (L z))

theorem iteratedDeriv_const_mul' {g : ℂ → ℂ} (hg : ContDiff ℂ (⊤ : ℕ∞) g) (c : ℂ) (n : ℕ) :
    iteratedDeriv n (fun u => c * g u) = fun u => c * iteratedDeriv n g u := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [iteratedDeriv_succ, ih]
    funext u
    rw [deriv_const_mul _ ((differentiable_iteratedDeriv hg n) u), ← iteratedDeriv_succ]

/-- Scaling passes through the Euler operator. -/
theorem eulerOp_const_mul {Ψ : ℂ → ℂ} (hΨ : Differentiable ℂ Ψ) (c : ℂ) :
    eulerOp (fun u => c * Ψ u) = fun u => c * eulerOp Ψ u := by
  funext u
  show u * deriv (fun u => c * Ψ u) u = c * (u * deriv Ψ u)
  rw [deriv_const_mul _ (hΨ u)]
  ring

/-- **The directional derivation is the Euler operator, scaled by the phase of the direction.** -/
theorem dirDeriv_phaseComp {L : (Fin d → ℂ) →ₗ[ℂ] ℂ} {Ψ : ℂ → ℂ}
    (hΨ : Differentiable ℂ Ψ) (w : Fin d → ℂ) :
    dirDeriv w (phaseComp L Ψ) = phaseComp L (fun u => L w * eulerOp Ψ u) := by
  funext z
  show deriv (fun t : ℂ => phaseComp L Ψ (z + t • w)) 0 = L w * eulerOp Ψ (Complex.exp (L z))
  have hfun : (fun t : ℂ => phaseComp L Ψ (z + t • w))
      = fun t : ℂ => Ψ (Complex.exp (L z) * Complex.exp (t * L w)) := by
    funext t
    show Ψ (Complex.exp (L (z + t • w))) = _
    rw [map_add, map_smul, smul_eq_mul, Complex.exp_add]
  rw [hfun]
  have h1 : HasDerivAt (fun t : ℂ => t * L w) (L w) 0 := by
    simpa using (hasDerivAt_id (0 : ℂ)).mul_const (L w)
  have hg : HasDerivAt (fun t : ℂ => Complex.exp (L z) * Complex.exp (t * L w))
      (Complex.exp (L z) * (Complex.exp ((0 : ℂ) * L w) * L w)) 0 :=
    (h1.cexp).const_mul _
  have hΨat : HasDerivAt Ψ
      (deriv Ψ (Complex.exp (L z) * Complex.exp ((0 : ℂ) * L w)))
      (Complex.exp (L z) * Complex.exp ((0 : ℂ) * L w)) := (hΨ _).hasDerivAt
  have hcomp : HasDerivAt (fun t : ℂ => Ψ (Complex.exp (L z) * Complex.exp (t * L w)))
      (deriv Ψ (Complex.exp (L z) * Complex.exp ((0 : ℂ) * L w))
        * (Complex.exp (L z) * (Complex.exp ((0 : ℂ) * L w) * L w))) 0 :=
    hΨat.comp (0 : ℂ) hg
  rw [hcomp.deriv]
  show deriv Ψ (Complex.exp (L z) * Complex.exp ((0 : ℂ) * L w))
      * (Complex.exp (L z) * (Complex.exp ((0 : ℂ) * L w) * L w))
    = L w * (Complex.exp (L z) * deriv Ψ (Complex.exp (L z)))
  rw [show ((0 : ℂ) * L w) = 0 by ring, Complex.exp_zero, mul_one, one_mul]
  ring

/-- **Iterated directional derivatives of a pencil carrier.** -/
theorem dirDeriv_iterate_phaseComp {L : (Fin d → ℂ) →ₗ[ℂ] ℂ} {Ψ : ℂ → ℂ}
    (hΨ : ContDiff ℂ (⊤ : ℕ∞) Ψ) (w : Fin d → ℂ) (r : ℕ) :
    (dirDeriv w)^[r] (phaseComp L Ψ)
      = phaseComp L (fun u => (L w) ^ r * (eulerOp^[r] Ψ) u) := by
  induction r with
  | zero => simp
  | succ r ih =>
    have hiter : ContDiff ℂ (⊤ : ℕ∞) (eulerOp^[r] Ψ) := by
      clear ih
      induction r with
      | zero => simpa using hΨ
      | succ r ihr =>
        rw [Function.iterate_succ_apply']
        exact contDiff_eulerOp ihr
    have hdiff : Differentiable ℂ fun u => (L w) ^ r * (eulerOp^[r] Ψ) u :=
      (hiter.differentiable (by simp)).const_mul _
    rw [Function.iterate_succ_apply', ih, dirDeriv_phaseComp hdiff w]
    have hscale : eulerOp (fun u => (L w) ^ r * (eulerOp^[r] Ψ) u)
        = fun u => (L w) ^ r * eulerOp (eulerOp^[r] Ψ) u :=
      eulerOp_const_mul (hiter.differentiable (by simp)) _
    rw [hscale]
    show phaseComp L (fun u => L w * ((L w) ^ r * eulerOp (eulerOp^[r] Ψ) u)) = _
    have hfun : (fun u => L w * ((L w) ^ r * eulerOp (eulerOp^[r] Ψ) u))
        = fun u => (L w) ^ (r + 1) * (eulerOp^[r + 1] Ψ) u := by
      funext u
      rw [Function.iterate_succ_apply', pow_succ]
      ring
    rw [hfun]

/-- **The inner coefficients see an `r`-fold directional derivative as multiplication by
`(m · L w)^r`.** -/
theorem iteratedDeriv_inner_dirDeriv_iterate {L : (Fin d → ℂ) →ₗ[ℂ] ℂ} {Ψ : ℂ → ℂ}
    (hΨ : ContDiff ℂ (⊤ : ℕ∞) Ψ) (w : Fin d → ℂ) (r m : ℕ) :
    iteratedDeriv m (fun u => (L w) ^ r * (eulerOp^[r] Ψ) u) 0
      = ((m : ℂ) * L w) ^ r * iteratedDeriv m Ψ 0 := by
  have hiter : ContDiff ℂ (⊤ : ℕ∞) (eulerOp^[r] Ψ) := by
    induction r with
    | zero => simpa using hΨ
    | succ r ihr =>
      rw [Function.iterate_succ_apply']
      exact contDiff_eulerOp ihr
  rw [iteratedDeriv_const_mul' hiter _ m]
  show (L w) ^ r * iteratedDeriv m (eulerOp^[r] Ψ) 0 = _
  rw [iteratedDeriv_eulerOp_iterate_zero hΨ r m]
  ring

end

end GaloisForLFunctions.HTGeometry
