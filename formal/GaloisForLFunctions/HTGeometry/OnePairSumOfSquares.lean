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
    simp only [Fin.addCases_left]
    rw [hrow₁ i]
  · refine Finset.sum_congr rfl (fun i _ => ?_)
    simp only [Fin.addCases_right]
    rw [hrow₂ i]

/-- The square of a real exponential sum is a Hermitian square. -/
theorem isSumHermitianSquares_sq {m : ℕ} (d a : Fin m → ℝ) :
    IsSumHermitianSquares (fun t => (∑ j, d j * Real.exp (a j * t)) ^ (2 : ℕ)) := by
  refine ⟨1, m, ![fun j => ((d j : ℝ) : ℂ)], fun j => ((a j : ℝ) : ℂ), fun t => ?_⟩
  show (∑ j, d j * Real.exp (a j * t)) ^ (2 : ℕ) = _
  rw [Fin.sum_univ_one, Matrix.cons_val_zero]
  have hz : (∑ j, ((d j : ℝ) : ℂ) * Complex.exp (((a j : ℝ) : ℂ) * t))
      = (((∑ j, d j * Real.exp (a j * t) : ℝ)) : ℂ) := by
    rw [Complex.ofReal_sum]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [Complex.ofReal_mul,
      show ((a j : ℝ) : ℂ) * (t : ℂ) = ((a j * t : ℝ) : ℂ) from by push_cast; ring,
      ← Complex.ofReal_exp]
  rw [hz, Complex.normSq_ofReal]
  ring

/-- A polynomial in `e^{σ t}` scaled by `e^{τ t}` is a real exponential sum. -/
theorem polyExp_eq_expSumReal (A : ℝ[X]) (σ τ t : ℝ) :
    Real.exp (τ * t) * A.eval (Real.exp (σ * t))
      = ∑ j : Fin (A.natDegree + 1), A.coeff (j : ℕ) * Real.exp ((((j : ℕ) : ℝ) * σ + τ) * t) := by
  rw [Fin.sum_univ_eq_sum_range
      (fun j => A.coeff j * Real.exp (((j : ℝ) * σ + τ) * t)) (A.natDegree + 1),
    eval_eq_sum_range, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [show ((j : ℝ) * σ + τ) * t = (j : ℝ) * (σ * t) + τ * t from by ring, Real.exp_add,
    ← Real.exp_nat_mul]
  ring

/-- **A nonnegative signomial with commensurable exponents is a sum of two squares.** -/
theorem isSumHermitianSquares_signomial (p : ℝ[X]) (ρ m : ℝ)
    (hp : ∀ y : ℝ, 0 < y → 0 ≤ p.eval y) :
    IsSumHermitianSquares (fun t => Real.exp (-(m * t)) * p.eval (Real.exp (ρ * t))) := by
  have hp0 : ∀ y : ℝ, 0 ≤ y → 0 ≤ p.eval y := by
    intro y hy
    rcases eq_or_lt_of_le hy with heq | hlt
    · by_contra hcon
      push Not at hcon
      have hcont : ContinuousAt (fun z => p.eval z) y := (Polynomial.continuous p).continuousAt
      have hev : ∀ᶠ z in nhds y, p.eval z < 0 := hcont.eventually (eventually_lt_nhds hcon)
      obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.mp hev
      have hy2 : p.eval (y + ε / 2) < 0 := by
        refine hball ?_
        rw [Real.dist_eq, add_sub_cancel_left, abs_of_pos (by linarith)]
        linarith
      exact absurd (hp (y + ε / 2) (by rw [← heq]; linarith)) (not_le.mpr hy2)
    · exact hp y hlt
  obtain ⟨A, B, hAB⟩ := exists_sq_add_sq_comp_sq p hp0
  have hrewrite : ∀ t : ℝ, Real.exp (-(m * t)) * p.eval (Real.exp (ρ * t))
      = (Real.exp (-(m / 2) * t) * A.eval (Real.exp ((ρ / 2) * t))) ^ (2 : ℕ)
        + (Real.exp (-(m / 2) * t) * B.eval (Real.exp ((ρ / 2) * t))) ^ (2 : ℕ) := by
    intro t
    have hy : Real.exp ((ρ / 2) * t) ^ (2 : ℕ) = Real.exp (ρ * t) := by
      rw [← Real.exp_nat_mul]
      congr 1
      ring
    have hex : Real.exp (-(m / 2) * t) ^ (2 : ℕ) = Real.exp (-(m * t)) := by
      rw [← Real.exp_nat_mul]
      congr 1
      ring
    calc Real.exp (-(m * t)) * p.eval (Real.exp (ρ * t))
        = Real.exp (-(m / 2) * t) ^ (2 : ℕ) * p.eval (Real.exp ((ρ / 2) * t) ^ (2 : ℕ)) := by rw [hy, hex]
      _ = Real.exp (-(m / 2) * t) ^ (2 : ℕ)
            * ((A.eval (Real.exp ((ρ / 2) * t))) ^ (2 : ℕ) + (B.eval (Real.exp ((ρ / 2) * t))) ^ (2 : ℕ)) := by
          rw [hAB]
      _ = _ := by ring
  have hsqA : IsSumHermitianSquares
      (fun t => (Real.exp (-(m / 2) * t) * A.eval (Real.exp ((ρ / 2) * t))) ^ (2 : ℕ)) := by
    obtain ⟨L, m', v, μ, hv⟩ := isSumHermitianSquares_sq
      (fun j : Fin (A.natDegree + 1) => A.coeff (j : ℕ))
      (fun j : Fin (A.natDegree + 1) => ((j : ℕ) : ℝ) * (ρ / 2) + -(m / 2))
    refine ⟨L, m', v, μ, fun t => ?_⟩
    show (Real.exp (-(m / 2) * t) * A.eval (Real.exp ((ρ / 2) * t))) ^ (2 : ℕ) = _
    rw [polyExp_eq_expSumReal A (ρ / 2) (-(m / 2)) t]
    exact hv t
  have hsqB : IsSumHermitianSquares
      (fun t => (Real.exp (-(m / 2) * t) * B.eval (Real.exp ((ρ / 2) * t))) ^ (2 : ℕ)) := by
    obtain ⟨L, m', v, μ, hv⟩ := isSumHermitianSquares_sq
      (fun j : Fin (B.natDegree + 1) => B.coeff (j : ℕ))
      (fun j : Fin (B.natDegree + 1) => ((j : ℕ) : ℝ) * (ρ / 2) + -(m / 2))
    refine ⟨L, m', v, μ, fun t => ?_⟩
    show (Real.exp (-(m / 2) * t) * B.eval (Real.exp ((ρ / 2) * t))) ^ (2 : ℕ) = _
    rw [polyExp_eq_expSumReal B (ρ / 2) (-(m / 2)) t]
    exact hv t
  obtain ⟨L, m', v, μ, hv⟩ := hsqA.add hsqB
  refine ⟨L, m', v, μ, fun t => ?_⟩
  show Real.exp (-(m * t)) * p.eval (Real.exp (ρ * t)) = _
  rw [hrewrite t]
  exact hv t

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
