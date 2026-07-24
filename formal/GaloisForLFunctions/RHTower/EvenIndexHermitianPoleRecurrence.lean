import GaloisForLFunctions.RHTower.EvenIndexHermitianRecurrence
import GaloisForLFunctions.HTGeometry.MellinPoleRadialGrowth

/-!
# The even-index Hermitian pole recurrence

Assembling the campaign: for a coefficient sequence whose exponential profile `A(e^{-x})` is realised
through a Mellin/Gamma identity by a Dirichlet function `D`, a right half-plane pole of `D` forces the
real parts of the even-index mixed additive convolution powers to be positive at infinitely many
indices (`frequently_re_pos_of_dirichletPole`).  This is the qualitative pole-theoretic consequence
`(9)` of the even-index parity law, now unconditional once the Mellin realisation `(6)` and the decay
hypotheses are supplied.

The proof chains three unconditional facts: a right half-plane Dirichlet pole makes the exponential
profile blow up radially (`HTGeometry.not_isBigO_zero_of_mellin_eq_Gamma_mul`); radial blow-up yields a
radius exceeding any prefix bound (`exists_norm_gt_of_not_isBigO`); and radial blow-up forces cofinal
positivity of the even-index real parts (`frequently_re_pos_of_norm_unbounded`).
-/

open Complex Filter Topology Asymptotics MeasureTheory

namespace RHTower

/-- **Radial blow-up from an unbounded exponential profile.**  If the exponential profile
`Af x = ∑' a_N e^{-Nx}` is not bounded near `x = 0⁺`, then for every bound `B` there is a radius
`r ∈ [0,1)` at which the Hermitian modulus exceeds `B`.  The witness is `r = e^{-x}` for a small `x`
where `‖Af x‖ > B`. -/
theorem exists_norm_gt_of_not_isBigO (a : ℕ → ℂ) {Af : ℝ → ℂ}
    (hAf : ∀ x : ℝ, Af x = ∑' N : ℕ, a N * (Real.exp (-x) : ℂ) ^ N)
    (hnb : ¬ (Af =O[𝓝[>] (0:ℝ)] fun x => x ^ (-(0:ℝ)))) :
    ∀ B : ℝ, ∃ r : ℝ, 0 ≤ r ∧ r < 1 ∧ B < ‖∑' N : ℕ, a N * (r : ℂ) ^ N‖ := by
  have hcongr : (fun x : ℝ => x ^ (-(0:ℝ))) =ᶠ[𝓝[>] (0:ℝ)] fun _ => (1:ℝ) := by
    filter_upwards [self_mem_nhdsWithin] with x hx
    rw [neg_zero, Real.rpow_zero]
  have hnb1 : ¬ (Af =O[𝓝[>] (0:ℝ)] fun _ => (1:ℝ)) :=
    fun h => hnb (h.congr' EventuallyEq.rfl hcongr.symm)
  have hbdd : ¬ IsBoundedUnder (· ≤ ·) (𝓝[>] (0:ℝ)) (fun x => ‖Af x‖) := by
    rw [Asymptotics.isBigO_const_iff, not_and] at hnb1
    exact hnb1 (fun h10 => absurd h10 one_ne_zero)
  intro B
  have hfreq : ∃ᶠ x in 𝓝[>] (0:ℝ), B < ‖Af x‖ := by
    by_contra hcon
    rw [Filter.not_frequently] at hcon
    apply hbdd
    refine ⟨B, ?_⟩
    rw [Filter.eventually_map]
    filter_upwards [hcon] with x hx
    exact not_lt.mp hx
  obtain ⟨x, hBx, hx0⟩ := (hfreq.and_eventually self_mem_nhdsWithin).exists
  refine ⟨Real.exp (-x), (Real.exp_pos _).le, ?_, ?_⟩
  · exact Real.exp_lt_one_iff.mpr (by simpa using hx0)
  · rw [hAf x] at hBx; exact hBx

/-- **Even-index pole recurrence `(9)`.**  Let `a` have absolutely convergent radial series on
`[0,1)`, with exponential profile `Af x = ∑' a_N e^{-Nx}` locally integrable on `(0,∞)` and decaying
exponentially at infinity, realised through the Mellin identity `mellin Af = Γ · D` near a right
half-plane point `ρ`.  If `D` is not holomorphic at `ρ`, then for every `k ≥ 1` the real parts of the
`2k`-fold even-index mixed additive convolution powers are positive at infinitely many indices. -/
theorem frequently_re_pos_of_dirichletPole (a : ℕ → ℂ) (D : ℂ → ℂ) {k : ℕ} (hk : 1 ≤ k)
    {ρ : ℂ} {a₀ : ℝ} (ha0 : 0 < a₀) (hρ : 0 < ρ.re)
    (habs : ∀ r : ℝ, 0 ≤ r → r < 1 → Summable (fun N => ‖a N * (r : ℂ) ^ N‖))
    (hint : LocallyIntegrableOn (fun x => ∑' N : ℕ, a N * (Real.exp (-x) : ℂ) ^ N)
      (Set.Ioi 0) volume)
    (htop : (fun x => ∑' N : ℕ, a N * (Real.exp (-x) : ℂ) ^ N) =O[atTop]
      fun t => Real.exp (-a₀ * t))
    (hMellin : ∀ᶠ s in 𝓝 ρ,
      mellin (fun x => ∑' N : ℕ, a N * (Real.exp (-x) : ℂ) ^ N) s = Complex.Gamma s * D s)
    (hpole : ¬ DifferentiableAt ℂ D ρ) :
    ∃ᶠ q in Filter.atTop, 0 < (mixedAdditiveConvolutionPower a k (2 * q)).re := by
  have hnb := GaloisForLFunctions.HTGeometry.not_isBigO_zero_of_mellin_eq_Gamma_mul
    ha0 hint htop hρ hρ hMellin hpole
  exact frequently_re_pos_of_norm_unbounded a hk habs
    (exists_norm_gt_of_not_isBigO a (fun x => rfl) hnb)

end RHTower
