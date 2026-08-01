import GaloisForLFunctions.HTGeometry.BohrHullCharacterSeparation

/-!
# Lattice translations are almost periods

If every frequency of the hull lies in an arithmetic progression `βℤ`, then the translations by the
dual lattice `(2π/β)ℤ` fix every approximating character, so they move the function by at most twice
the approximation error.  This is the step that makes the Fejér kernel on `βℤ` an approximate
identity for such a function: its peaks sit exactly on the dual lattice, where the function barely
moves.
-/

open Filter Topology

open scoped BoundedContinuousFunction Real

namespace GaloisForLFunctions

open _root_.HTGeometry

variable {f : ℝ →ᵇ ℂ}

/-- **Dual-lattice translations are almost periods.** -/
theorem norm_translate_sub_le_of_freq_lattice {β : ℝ} (hβ : β ≠ 0)
    (hf : UniformContinuous fun x => f x) (htb : HasTotallyBoundedOrbit fun x => f x)
    (hfreq : ∀ μ : ℝ, IsBohrHullFrequency f μ → ∃ k : ℤ, μ = k * β)
    {ε : ℝ} (hε : 0 < ε) (m : ℤ) (t : ℝ) :
    ‖f (t + m * (2 * Real.pi / β)) - f t‖ ≤ 2 * ε := by
  classical
  obtain ⟨n, c, lam, hlamfreq, happrox⟩ := exists_trig_approx_hullFreq hf htb hε
  set u : ℝ := m * (2 * Real.pi / β) with hu
  -- the approximating polynomial is invariant under the lattice translation
  have hinv : ∀ j : Fin n,
      Complex.exp ((lam j * (t + u) : ℝ) * Complex.I)
        = Complex.exp ((lam j * t : ℝ) * Complex.I) := by
    intro j
    obtain ⟨k, hk⟩ := hfreq (lam j) (hlamfreq j)
    have hphase : (lam j * (t + u) : ℝ)
        = (lam j * t : ℝ) + ((k * m : ℤ) : ℝ) * (2 * Real.pi) := by
      rw [hk, hu]
      push_cast
      field_simp
    rw [hphase]
    push_cast
    rw [add_mul, Complex.exp_add]
    rw [show (((k : ℂ) * (m : ℂ)) * (2 * (Real.pi : ℂ))) * Complex.I
        = ((k : ℂ) * (m : ℂ)) * (2 * (Real.pi : ℂ) * Complex.I) by ring]
    rw [show ((k : ℂ) * (m : ℂ)) = (((k * m : ℤ) : ℂ)) by push_cast; ring]
    rw [Complex.exp_int_mul_two_pi_mul_I, mul_one]
  have hpoly : (∑ j, c j * Complex.exp ((lam j * (t + u) : ℝ) * Complex.I))
      = ∑ j, c j * Complex.exp ((lam j * t : ℝ) * Complex.I) :=
    Finset.sum_congr rfl fun j _ => by rw [hinv j]
  have h1 := happrox (t + u)
  have h2 := happrox t
  calc ‖f (t + u) - f t‖
      = ‖(f (t + u) - ∑ j, c j * Complex.exp ((lam j * (t + u) : ℝ) * Complex.I))
        - (f t - ∑ j, c j * Complex.exp ((lam j * t : ℝ) * Complex.I))‖ := by
        rw [hpoly]
        congr 1
        ring
    _ ≤ ‖f (t + u) - ∑ j, c j * Complex.exp ((lam j * (t + u) : ℝ) * Complex.I)‖
        + ‖f t - ∑ j, c j * Complex.exp ((lam j * t : ℝ) * Complex.I)‖ := norm_sub_le _ _
    _ ≤ ε + ε := add_le_add h1 h2
    _ = 2 * ε := by ring

end GaloisForLFunctions
