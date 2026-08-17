import GaloisForLFunctions.HTGeometry.UnivariateSumOfTwoSquares

/-!
# One conjugate pair: unfolding-nonnegativity is also sufficient

The unfolding obstruction says a sum of Hermitian squares must stay nonnegative when growth and
phase are decoupled.  For a comparison with **one** conjugate pair the converse holds, so the
obstruction is the whole story:

`R(t) - 2 e^{βt} cos(γ t)` is a sum of Hermitian squares  ⟺  `R(t) ≥ 2 e^{βt}` for all `t`,

the right-hand side being exactly nonnegativity of the unfolding.  The proof splits

`R(t) - 2 e^{βt} cos(γ t) = [R(t) - 2 e^{βt}] + 2 e^{βt}(1 - cos γ t)`,

exhibits the second bracket as a single Hermitian square, and writes the first — a nonnegative
signomial with commensurable exponents — as a sum of two squares of signomials, using the univariate
Positivstellensatz after the substitution `y ↦ y²`.
-/

open Polynomial

namespace GaloisForLFunctions.HTGeometry

/-- A real function is a sum of Hermitian squares of exponential polynomials. -/
def IsSumHermitianSquares (f : ℝ → ℝ) : Prop :=
  ∃ (L m : ℕ) (v : Fin L → Fin m → ℂ) (μ : Fin m → ℂ),
    ∀ t : ℝ, f t = ∑ l, Complex.normSq (∑ j, v l j * Complex.exp (μ j * t))

theorem IsSumHermitianSquares.add {f g : ℝ → ℝ} (hf : IsSumHermitianSquares f)
    (hg : IsSumHermitianSquares g) : IsSumHermitianSquares (fun t => f t + g t) := by
  obtain ⟨L₁, m₁, v₁, μ₁, hv₁⟩ := hf
  obtain ⟨L₂, m₂, v₂, μ₂, hv₂⟩ := hg
  refine ⟨L₁ + L₂, m₁ + m₂,
    fun l => Fin.addCases (fun i => Fin.append (v₁ i) (fun _ => (0 : ℂ)))
      (fun i => Fin.append (fun _ => (0 : ℂ)) (v₂ i)) l,
    Fin.append μ₁ μ₂, fun t => ?_⟩
  show f t + g t = _
  have hrow₁ : ∀ i : Fin L₁,
      (∑ j, Fin.append (v₁ i) (fun _ => (0 : ℂ)) j * Complex.exp (Fin.append μ₁ μ₂ j * t))
        = ∑ j, v₁ i j * Complex.exp (μ₁ j * t) := by
    intro i
    rw [Fin.sum_univ_add]
    simp [Fin.append_left, Fin.append_right]
  have hrow₂ : ∀ i : Fin L₂,
      (∑ j, Fin.append (fun _ => (0 : ℂ)) (v₂ i) j * Complex.exp (Fin.append μ₁ μ₂ j * t))
        = ∑ j, v₂ i j * Complex.exp (μ₂ j * t) := by
    intro i
    rw [Fin.sum_univ_add]
    simp [Fin.append_left, Fin.append_right]
  rw [hv₁ t, hv₂ t, Fin.sum_univ_add]
  congr 1
  · refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [Fin.addCases_left, hrow₁ i]
  · refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [Fin.addCases_right, hrow₂ i]

/-- The square of a signomial `e^{τ t} A(e^{σ t})` is a Hermitian square. -/
theorem isSumHermitianSquares_sq_polyExp (A : ℝ[X]) (σ τ : ℝ) :
    IsSumHermitianSquares (fun t => (Real.exp (τ * t) * A.eval (Real.exp (σ * t))) ^ 2) := by
  refine ⟨1, A.natDegree + 1, ![fun j => ((A.coeff (j : ℕ) : ℝ) : ℂ)],
    fun j => (((j : ℕ) * σ + τ : ℝ) : ℂ), fun t => ?_⟩
  have hrow : (∑ j : Fin (A.natDegree + 1),
        ((A.coeff (j : ℕ) : ℝ) : ℂ) * Complex.exp ((((j : ℕ) * σ + τ : ℝ) : ℂ) * t))
      = ((Real.exp (τ * t) * A.eval (Real.exp (σ * t)) : ℝ) : ℂ) := by
    rw [eval_eq_sum_range]
    push_cast
    rw [Finset.mul_sum, ← Fin.sum_univ_eq_sum_range
      (fun j => ((Real.exp (τ * t) : ℂ) * ((A.coeff j : ℝ) : ℂ)
        * ((Real.exp (σ * t) : ℂ) ^ j)))]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [show ((((j : ℕ) : ℝ) * σ + τ : ℝ) : ℂ) * (t : ℂ)
        = (((σ * t : ℝ) : ℂ)) * (j : ℕ) + ((τ * t : ℝ) : ℂ) from by push_cast; ring,
      Complex.exp_add, Complex.exp_nat_mul]
    push_cast
    ring
  rw [Fin.sum_univ_one, Matrix.cons_val_zero, hrow, Complex.normSq_ofReal]
  ring

/-- **A nonnegative signomial with commensurable exponents is a sum of two squares.** -/
theorem isSumHermitianSquares_signomial (p : ℝ[X]) (ρ m : ℝ)
    (hp : ∀ y : ℝ, 0 < y → 0 ≤ p.eval y) :
    IsSumHermitianSquares (fun t => Real.exp (-(m * t)) * p.eval (Real.exp (ρ * t))) := by
  have hp0 : ∀ y : ℝ, 0 ≤ y → 0 ≤ p.eval y := by
    intro y hy
    rcases eq_or_lt_of_le hy with heq | hlt
    · -- continuity at the endpoint
      by_contra hcon
      push Not at hcon
      have hcont : ContinuousAt (fun z => p.eval z) y := (Polynomial.continuous p).continuousAt
      have hev : ∀ᶠ z in nhds y, p.eval z < 0 := hcont.eventually (eventually_lt_nhds hcon)
      obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.mp hev
      have hy2 : p.eval (y + ε / 2) < 0 := by
        refine hball ?_
        rw [Real.dist_eq, add_sub_cancel_left, abs_of_pos (by linarith)]
        linarith
      exact absurd (hp (y + ε / 2) (by rw [← heq]; linarith)) (not_le.mpr hy2)
    · exact (hp y hlt).le.trans_eq' rfl |>.trans (le_refl _)
  obtain ⟨A, B, hAB⟩ := exists_sq_add_sq_comp_sq p hp0
  have hrewrite : ∀ t : ℝ, Real.exp (-(m * t)) * p.eval (Real.exp (ρ * t))
      = (Real.exp (-(m / 2) * t) * A.eval (Real.exp ((ρ / 2) * t))) ^ 2
        + (Real.exp (-(m / 2) * t) * B.eval (Real.exp ((ρ / 2) * t))) ^ 2 := by
    intro t
    have hy : Real.exp ((ρ / 2) * t) ^ 2 = Real.exp (ρ * t) := by
      rw [← Real.exp_nat_mul]
      congr 1
      ring
    have hex : Real.exp (-(m / 2) * t) ^ 2 = Real.exp (-(m * t)) := by
      rw [← Real.exp_nat_mul]
      congr 1
      ring
    calc Real.exp (-(m * t)) * p.eval (Real.exp (ρ * t))
        = Real.exp (-(m / 2) * t) ^ 2 * p.eval (Real.exp ((ρ / 2) * t) ^ 2) := by
          rw [hy, hex]
      _ = Real.exp (-(m / 2) * t) ^ 2
            * ((A.eval (Real.exp ((ρ / 2) * t))) ^ 2 + (B.eval (Real.exp ((ρ / 2) * t))) ^ 2) := by
          rw [hAB]
      _ = _ := by ring
  have h1 := isSumHermitianSquares_sq_polyExp A (ρ / 2) (-(m / 2))
  have h2 := isSumHermitianSquares_sq_polyExp B (ρ / 2) (-(m / 2))
  have := h1.add h2
  obtain ⟨L, m', v, μ, hv⟩ := this
  exact ⟨L, m', v, μ, fun t => by rw [hrewrite t, ← hv t]⟩

/-- The one-pair contribution is a single Hermitian square. -/
theorem isSumHermitianSquares_pair (β γ : ℝ) :
    IsSumHermitianSquares (fun t => 2 * Real.exp (β * t) * (1 - Real.cos (γ * t))) := by
  refine ⟨1, 2, extV, extMu β γ, fun t => ?_⟩
  have h1 := ext_isHermitianSOS β γ t
  have h2 := ext_unfold β γ t t
  rw [unfoldSum_diag] at h2
  rw [h1] at h2
  rw [← Complex.ofReal_sum] at h2
  exact (Complex.ofReal_inj.mp h2).symm

/-- **Sufficiency for one conjugate pair.**  If `R(t) - 2e^{βt}` is a nonnegative signomial with
commensurable exponents — equivalently, if the unfolding of `R(t) - 2e^{βt}cos(γ t)` is nonnegative —
then that comparison is a sum of Hermitian squares. -/
theorem onePair_isSumHermitianSquares (p : ℝ[X]) (ρ m β γ : ℝ)
    (hp : ∀ y : ℝ, 0 < y → 0 ≤ p.eval y) :
    IsSumHermitianSquares (fun t =>
      Real.exp (-(m * t)) * p.eval (Real.exp (ρ * t))
        + 2 * Real.exp (β * t) * (1 - Real.cos (γ * t))) :=
  (isSumHermitianSquares_signomial p ρ m hp).add (isSumHermitianSquares_pair β γ)

end GaloisForLFunctions.HTGeometry
