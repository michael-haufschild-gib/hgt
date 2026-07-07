import Mathlib
import GaloisForLFunctions.Hypertranscendence

/-!
# A pole-counting transcendence criterion, and Γ transcendental over ℂ(s)

Hölder (1887) proved Γ satisfies no algebraic *differential* equation.  Its order-zero shadow — Γ is not
an algebraic function over `ℂ(s)` — is proved here from a general criterion isolated from the argument:

**`not_algebraic_of_infinite_poles`.**  A zero-free meromorphic-type function `f` whose reciprocal is
continuous and vanishes on an infinite set (`f`'s poles) satisfies no nonzero polynomial relation
`P(s, f(s)) ≡ 0`.  The mechanism: dividing such a relation by `f^{deg}` and letting `s` approach a pole
(where `f⁻¹ → 0`) forces the leading coefficient to vanish there; a nonzero polynomial cannot vanish on
an infinite set.

Instances: `gamma_not_algebraic` (Γ, poles at `−ℕ`) and `csc_not_algebraic` (`1/sin`, poles at `πℤ`).
These are the base rung of `Hypertranscendental`; the differential rungs remain the frontier.
-/

open Complex Polynomial Filter Topology

namespace GaloisForLFunctions

/-- **Pole-counting transcendence criterion.**  If `f⁻¹` is continuous, vanishes on an infinite set `Z`
(the poles of `f`), and `f` is nonzero on a punctured neighbourhood of each pole, then `f` satisfies no
nonzero polynomial relation over `ℂ(s)`: `f` is transcendental as a function. -/
theorem not_algebraic_of_infinite_poles (f : ℂ → ℂ)
    (hcont : Continuous fun s => (f s)⁻¹)
    (Z : Set ℂ) (hZinf : Z.Infinite) (hZ : ∀ z ∈ Z, (f z)⁻¹ = 0)
    (hpunct : ∀ z ∈ Z, ∀ᶠ s in 𝓝[≠] z, f s ≠ 0)
    (p : Polynomial (Polynomial ℂ)) (hp : p ≠ 0) :
    ∃ s : ℂ, p.eval₂ (Polynomial.evalRingHom s) (f s) ≠ 0 := by
  by_contra hcon
  simp only [not_exists, ne_eq, not_not] at hcon
  set d := p.natDegree with hd
  set F : ℂ → ℂ := fun s => ∑ j ∈ Finset.range (d + 1),
    (p.coeff j).eval s * (f s)⁻¹ ^ (d - j) with hF
  have hFcont : Continuous F := by
    apply continuous_finsetSum
    intro j _
    exact (p.coeff j).continuous.mul (hcont.pow (d - j))
  have hF0 : ∀ s, f s ≠ 0 → F s = 0 := by
    intro s hs
    have hrw : F s = (f s)⁻¹ ^ d * p.eval₂ (Polynomial.evalRingHom s) (f s) := by
      rw [hF, Polynomial.eval₂_eq_sum_range, Finset.mul_sum, ← hd]
      refine Finset.sum_congr rfl (fun j hj => ?_)
      simp only [Finset.mem_range, Nat.lt_succ_iff] at hj
      have hpow : (f s)⁻¹ ^ (d - j) = (f s)⁻¹ ^ d * f s ^ j := by
        rw [inv_pow, inv_pow, pow_sub₀ _ hs hj, mul_inv, inv_inv]
      rw [hpow, Polynomial.coe_evalRingHom]; ring
    rw [hrw, hcon s, mul_zero]
  have hlead : ∀ z ∈ Z, (p.coeff d).eval z = 0 := by
    intro z hz
    have hFk : F z = (p.coeff d).eval z := by
      simp only [hF]
      rw [Finset.sum_eq_single d]
      · rw [Nat.sub_self, pow_zero, mul_one]
      · intro j hj hjd
        simp only [Finset.mem_range, Nat.lt_succ_iff] at hj
        rw [hZ z hz, zero_pow (by omega : d - j ≠ 0), mul_zero]
      · intro h; exact absurd (Finset.mem_range.mpr (Nat.lt_succ_self d)) h
    have hev : ∀ᶠ s in 𝓝[≠] z, F s = 0 := (hpunct z hz).mono (fun s hs => hF0 s hs)
    have h1 : Tendsto F (𝓝[≠] z) (𝓝 (F z)) := hFcont.continuousAt.continuousWithinAt
    have h2 : Tendsto F (𝓝[≠] z) (𝓝 0) := tendsto_const_nhds.congr' (hev.mono (fun _ h => h.symm))
    rw [← hFk]; exact tendsto_nhds_unique h1 h2
  have hlc_ne : p.coeff d ≠ 0 := by
    rw [hd, ← Polynomial.leadingCoeff]; exact Polynomial.leadingCoeff_ne_zero.mpr hp
  have hinf : {x : ℂ | (p.coeff d).IsRoot x}.Infinite :=
    hZinf.mono (fun z hz => hlead z hz)
  exact hlc_ne (Polynomial.eq_zero_of_infinite_isRoot _ hinf)

/-- **Γ is transcendental over `ℂ(s)`.**  Γ has no zeros and poles at every `−k` (`k ∈ ℕ`); by the
pole-counting criterion it satisfies no nonzero polynomial relation `P(s, Γ(s)) ≡ 0`.  The order-zero
rung of `Hypertranscendental Complex.Gamma`. -/
theorem gamma_not_algebraic (p : Polynomial (Polynomial ℂ)) (hp : p ≠ 0) :
    ∃ s : ℂ, p.eval₂ (Polynomial.evalRingHom s) (Complex.Gamma s) ≠ 0 := by
  refine not_algebraic_of_infinite_poles Complex.Gamma
    Complex.differentiable_one_div_Gamma.continuous {x : ℂ | ∃ k : ℕ, x = -(k : ℂ)}
    (Set.infinite_of_injective_forall_mem (f := fun k : ℕ => -(k : ℂ))
      (fun a b hab => by simpa using hab) (fun k => ⟨k, rfl⟩))
    (fun z ⟨k, hk⟩ => by rw [hk, Complex.Gamma_neg_nat_eq_zero, inv_zero]) ?_ p hp
  rintro z ⟨k, rfl⟩
  have hball : ∀ᶠ s in 𝓝[≠] (-(k : ℂ)), s ∈ Metric.ball (-(k : ℂ)) (1 / 2) :=
    eventually_nhdsWithin_of_eventually_nhds (Metric.ball_mem_nhds _ (by norm_num))
  have hne : ∀ᶠ s in 𝓝[≠] (-(k : ℂ)), s ≠ -(k : ℂ) := self_mem_nhdsWithin
  filter_upwards [hball, hne] with s hsb hsne
  apply Complex.Gamma_ne_zero
  intro m hm
  rcases eq_or_ne m k with rfl | hmk
  · exact hsne hm
  · rw [Metric.mem_ball, Complex.dist_eq, hm] at hsb
    have : (1 : ℝ) ≤ ‖(-(m : ℂ)) - (-(k : ℂ))‖ := by
      rw [show (-(m : ℂ)) - (-(k : ℂ)) = (((k : ℤ) - m : ℤ) : ℂ) by push_cast; ring,
        show ((((k : ℤ) - m : ℤ)) : ℂ) = (((k : ℤ) - m : ℤ) : ℝ) by push_cast; ring,
        Complex.norm_real, Real.norm_eq_abs]
      exact_mod_cast Int.one_le_abs (by omega : ((k : ℤ) - m) ≠ 0)
    linarith

/-- **`csc = 1/sin` is transcendental over `ℂ(s)`.**  A second instance of the pole-counting
criterion: `1/sin` is zero-free with poles at every `kπ` (`k ∈ ℤ`), so it satisfies no nonzero
polynomial relation `P(s, csc s) ≡ 0`. -/
theorem csc_not_algebraic (p : Polynomial (Polynomial ℂ)) (hp : p ≠ 0) :
    ∃ s : ℂ, p.eval₂ (Polynomial.evalRingHom s) (Complex.sin s)⁻¹ ≠ 0 := by
  refine not_algebraic_of_infinite_poles (fun s => (Complex.sin s)⁻¹)
    (by simp_rw [inv_inv]; exact Complex.continuous_sin)
    {x : ℂ | ∃ k : ℤ, x = k * Real.pi}
    (Set.infinite_of_injective_forall_mem (f := fun k : ℤ => (k : ℂ) * Real.pi)
      (fun a b hab => by
        have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
        field_simp at hab; exact_mod_cast hab)
      (fun k => ⟨k, rfl⟩))
    (fun z ⟨k, hk⟩ => by
      rw [hk, inv_inv, Complex.sin_eq_zero_iff]; exact ⟨k, by ring⟩) ?_ p hp
  rintro z ⟨k, rfl⟩
  have hpipos : (0 : ℝ) < Real.pi := Real.pi_pos
  have hball : ∀ᶠ s in 𝓝[≠] ((k : ℂ) * Real.pi),
      s ∈ Metric.ball ((k : ℂ) * Real.pi) (Real.pi / 2) :=
    eventually_nhdsWithin_of_eventually_nhds (Metric.ball_mem_nhds _ (by positivity))
  have hne : ∀ᶠ s in 𝓝[≠] ((k : ℂ) * Real.pi), s ≠ (k : ℂ) * Real.pi := self_mem_nhdsWithin
  filter_upwards [hball, hne] with s hsb hsne
  simp only [ne_eq, inv_eq_zero]
  rw [Complex.sin_eq_zero_iff]
  rintro ⟨m, hm⟩
  rcases eq_or_ne m k with rfl | hmk
  · exact hsne (by rw [hm])
  · rw [Metric.mem_ball, Complex.dist_eq, hm] at hsb
    have h1 : (m : ℂ) * Real.pi - (k : ℂ) * Real.pi = ((m - k : ℤ) : ℂ) * (Real.pi : ℂ) := by
      push_cast; ring
    rw [h1, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hpipos] at hsb
    have hge : (1 : ℝ) ≤ ‖((m - k : ℤ) : ℂ)‖ := by
      rw [Complex.norm_intCast]
      exact_mod_cast Int.one_le_abs (by omega : (m - k : ℤ) ≠ 0)
    nlinarith [mul_le_mul_of_nonneg_right hge hpipos.le]

end GaloisForLFunctions
