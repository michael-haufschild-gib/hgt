import GaloisForLFunctions.RHTower.Sieve.KuzminLandau

/-!
# Kuzmin–Landau on an interval of sample points

The band form of the Kuzmin–Landau inequality transfers to unit-spaced real sample points of
a differentiable phase: if `g'` is monotone on the span and confined to one integer band
`[m+δ, m+1−δ]`, the increments `g(x+j+1) − g(x+j)` are values of `g'` at interlacing mean
value points, so after subtracting the integer `m` per step they satisfy the discrete band
hypotheses, and the integer shift leaves every phase `e(g)` unchanged.
-/

namespace RHTower.Sieve

open Real

/-- Integer shifts do not move the phase. -/
theorem exp_two_pi_I_sub_int (y : ℝ) (k : ℤ) :
    Complex.exp (((2 * Real.pi * (y - k) : ℝ) : ℂ) * Complex.I)
      = Complex.exp (((2 * Real.pi * y : ℝ) : ℂ) * Complex.I) := by
  have hsplit : ((2 * Real.pi * (y - k) : ℝ) : ℂ) * Complex.I
      = ((2 * Real.pi * y : ℝ) : ℂ) * Complex.I - k * (2 * Real.pi * Complex.I) := by
    push_cast
    ring
  rw [hsplit, Complex.exp_sub, Complex.exp_int_mul_two_pi_mul_I, div_one]

/-- **Kuzmin–Landau at unit-spaced sample points.**  A differentiable phase whose derivative
is monotone and confined to one integer band `[m+δ, m+1−δ]` on the span has exponential sum
at most `3/(2δ) + 1` over the sample points, uniformly in their number. -/
theorem kuzminLandau_interval (g g' : ℝ → ℝ) (x₀ : ℝ) (M : ℕ) (m : ℤ) {δ : ℝ}
    (hδ0 : 0 < δ)
    (hderiv : ∀ x ∈ Set.Icc x₀ (x₀ + (M : ℕ)), HasDerivAt g (g' x) x)
    (hmono : MonotoneOn g' (Set.Icc x₀ (x₀ + (M : ℕ))))
    (hband_lo : ∀ x ∈ Set.Icc x₀ (x₀ + (M : ℕ)), (m : ℝ) + δ ≤ g' x)
    (hband_hi : ∀ x ∈ Set.Icc x₀ (x₀ + (M : ℕ)), g' x ≤ (m : ℝ) + 1 - δ) :
    ‖∑ j ∈ Finset.range (M + 1),
        Complex.exp (((2 * Real.pi * g (x₀ + j) : ℝ) : ℂ) * Complex.I)‖
      ≤ 3 / (2 * δ) + 1 := by
  classical
  set φ : ℕ → ℝ := fun j => g (x₀ + j) - (m : ℝ) * j with hφ
  -- the mean value point of one unit step
  have hMVT : ∀ j : ℕ, j < M →
      ∃ ξ ∈ Set.Ioo (x₀ + (j : ℝ)) (x₀ + (j : ℝ) + 1),
        g' ξ = g (x₀ + (j + 1 : ℕ)) - g (x₀ + j) := by
    intro j hj
    have hab : x₀ + (j : ℝ) < x₀ + (j : ℝ) + 1 := by linarith
    have hsub : Set.Icc (x₀ + (j : ℝ)) (x₀ + (j : ℝ) + 1)
        ⊆ Set.Icc x₀ (x₀ + (M : ℕ)) := by
      intro x hx
      rcases hx with ⟨h1, h2⟩
      constructor
      · have : (0 : ℝ) ≤ (j : ℝ) := Nat.cast_nonneg j
        linarith
      · have : (j : ℝ) + 1 ≤ (M : ℕ) := by
          exact_mod_cast Nat.succ_le_of_lt hj
        linarith
    have hcont : ContinuousOn g (Set.Icc (x₀ + (j : ℝ)) (x₀ + (j : ℝ) + 1)) := by
      intro x hx
      exact (hderiv x (hsub hx)).continuousAt.continuousWithinAt
    have hd : ∀ x ∈ Set.Ioo (x₀ + (j : ℝ)) (x₀ + (j : ℝ) + 1), HasDerivAt g (g' x) x := by
      intro x hx
      exact hderiv x (hsub (Set.mem_Icc_of_Ioo hx))
    obtain ⟨ξ, hξ, hslope⟩ := exists_hasDerivAt_eq_slope g g' hab hcont hd
    refine ⟨ξ, hξ, ?_⟩
    rw [hslope]
    have hcast : x₀ + ((j + 1 : ℕ) : ℝ) = x₀ + (j : ℝ) + 1 := by
      push_cast
      ring
    rw [hcast]
    field_simp
    ring
  have hmem : ∀ j : ℕ, j < M →
      ∀ ξ ∈ Set.Ioo (x₀ + (j : ℝ)) (x₀ + (j : ℝ) + 1),
        ξ ∈ Set.Icc x₀ (x₀ + (M : ℕ)) := by
    intro j hj ξ hξ
    rcases hξ with ⟨h1, h2⟩
    constructor
    · have : (0 : ℝ) ≤ (j : ℝ) := Nat.cast_nonneg j
      linarith
    · have : (j : ℝ) + 1 ≤ (M : ℕ) := by
        exact_mod_cast Nat.succ_le_of_lt hj
      linarith
  -- increments of φ
  have hincr : ∀ j : ℕ, j < M →
      φ (j + 1) - φ j = (g (x₀ + (j + 1 : ℕ)) - g (x₀ + j)) - m := by
    intro j hj
    simp only [hφ]
    push_cast
    ring
  have hlo : ∀ j < M, δ ≤ φ (j + 1) - φ j := by
    intro j hj
    obtain ⟨ξ, hξ, hval⟩ := hMVT j hj
    rw [hincr j hj, ← hval]
    have := hband_lo ξ (hmem j hj ξ hξ)
    linarith
  have hhi : ∀ j < M, φ (j + 1) - φ j ≤ 1 - δ := by
    intro j hj
    obtain ⟨ξ, hξ, hval⟩ := hMVT j hj
    rw [hincr j hj, ← hval]
    have := hband_hi ξ (hmem j hj ξ hξ)
    linarith
  have hmono' : ∀ j, j + 1 < M → φ (j + 1) - φ j ≤ φ (j + 2) - φ (j + 1) := by
    intro j hj
    have hj0 : j < M := by omega
    have hj1 : j + 1 < M := hj
    obtain ⟨ξ, hξ, hval⟩ := hMVT j hj0
    obtain ⟨ξ', hξ', hval'⟩ := hMVT (j + 1) hj1
    have hle : ξ ≤ ξ' := by
      rcases hξ with ⟨_, h2⟩
      rcases hξ' with ⟨h1', _⟩
      have hcast : x₀ + ((j + 1 : ℕ) : ℝ) = x₀ + (j : ℝ) + 1 := by
        push_cast
        ring
      rw [hcast] at h1'
      linarith
    have hg'le := hmono (hmem j hj0 ξ hξ) (hmem (j + 1) hj1 ξ' hξ') hle
    have e1 := hincr j hj0
    have e2 := hincr (j + 1) hj1
    rw [show j + 1 + 1 = j + 2 from rfl] at e2
    rw [e1, e2, ← hval, ← hval']
    linarith
  -- the shifted phases agree with the original ones
  have hphase : ∀ j : ℕ,
      Complex.exp (((2 * Real.pi * φ j : ℝ) : ℂ) * Complex.I)
        = Complex.exp (((2 * Real.pi * g (x₀ + j) : ℝ) : ℂ) * Complex.I) := by
    intro j
    have hval : φ j = g (x₀ + j) - ((m * j : ℤ) : ℝ) := by
      simp only [hφ]
      push_cast
      ring
    rw [hval]
    exact exp_two_pi_I_sub_int (g (x₀ + j)) (m * j)
  have hband := kuzminLandau_band φ M hδ0 hlo hhi hmono'
  calc ‖∑ j ∈ Finset.range (M + 1),
        Complex.exp (((2 * Real.pi * g (x₀ + j) : ℝ) : ℂ) * Complex.I)‖
      = ‖∑ j ∈ Finset.range (M + 1),
          Complex.exp (((2 * Real.pi * φ j : ℝ) : ℂ) * Complex.I)‖ := by
        congr 1
        exact Finset.sum_congr rfl fun j _ => (hphase j).symm
    _ ≤ 3 / (2 * δ) + 1 := hband

end RHTower.Sieve
