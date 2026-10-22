import GaloisForLFunctions.RHTower.CCM.CCMEvansBoundaryInfiniteRank

/-!
# The logarithmic Dirichlet reconstruction: coercivity, Carleman domination, observability

Four exact mechanisms of the card are formalized.

*The positive lower bound.*  A continuous, everywhere positive symbol that grows at infinity has a
strictly positive infimum — this is `γ_a > 0` of `(2)`.

*Carleman domination of the cross kernel.*  With `s = x−a`, `t = a−y` the exterior displacement is
`s + t` and the logarithmic kernel `e^{-(s+t)}/(s+t)` is dominated by the Carleman kernel
`1/(s+t)` — equations `(14)`–`(15)`.

*Coercive reconstruction.*  A coercive form gives the exact inverse bound `‖u_f‖ ≤ γ^{-1}‖f‖` —
equations `(17)`–`(18)`.

*Observability.*  Composing with the bounded cross block gives `(8)`, hence the admissible
characteristic space is everything, `(9)`.

The heat-semigroup representation `(13)`, the norm of the Carleman operator, the first
representation theorem and the multiplier calculus are cited parents and stay outside the Lean
statement.
-/

open Filter Topology Set

noncomputable section

namespace GaloisForLFunctions.RHTower

/-! ## The positive lower bound of the zero-free factor -/

/-- **Equation (2), `γ_a > 0`.**  A continuous positive symbol growing at infinity is bounded below
by a positive constant. -/
theorem exists_pos_lower_bound_of_tendsto_atTop {c : ℝ → ℝ} (hcont : Continuous c)
    (hpos : ∀ ξ, 0 < c ξ) (hgrow : Tendsto c (cocompact ℝ) atTop) :
    ∃ γ : ℝ, 0 < γ ∧ ∀ ξ, γ ≤ c ξ := by
  have hev : {ξ : ℝ | (1 : ℝ) ≤ c ξ} ∈ cocompact ℝ := hgrow (eventually_ge_atTop 1)
  obtain ⟨K, hK, hKsub⟩ := Filter.mem_cocompact.mp hev
  rcases K.eq_empty_or_nonempty with hempty | hne
  · refine ⟨1, one_pos, fun ξ => ?_⟩
    refine hKsub ?_
    rw [hempty]
    exact Set.notMem_empty ξ
  · obtain ⟨ξ₀, hξ₀K, hmin⟩ := hK.exists_isMinOn hne hcont.continuousOn
    refine ⟨min 1 (c ξ₀), lt_min one_pos (hpos ξ₀), fun ξ => ?_⟩
    by_cases hmem : ξ ∈ K
    · exact le_trans (min_le_right _ _) (hmin hmem)
    · exact le_trans (min_le_left _ _) (hKsub hmem)

/-! ## Carleman domination of the cross-boundary kernel -/

/-- **Equations (14)–(15).**  The logarithmic cross kernel is dominated by the Carleman kernel. -/
theorem log_cross_kernel_le_carleman {s t : ℝ} (hs : 0 < s) (ht : 0 < t) :
    |(-Real.exp (-(s + t)) / (s + t))| ≤ 1 / (s + t) := by
  have hst : 0 < s + t := by linarith
  have hexp : Real.exp (-(s + t)) ≤ 1 := by
    rw [Real.exp_le_one_iff]
    linarith
  have hexppos : 0 < Real.exp (-(s + t)) := Real.exp_pos _
  rw [abs_div, abs_neg, abs_of_pos hexppos, abs_of_pos hst]
  exact div_le_div_of_nonneg_right hexp (le_of_lt hst)

/-! ## Coercive reconstruction -/

/-- **Equations (17)–(18).**  A coercive form gives the exact inverse bound. -/
theorem norm_le_of_coercive {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    {γ : ℝ} (hγ : 0 < γ) {u f : H} (hcoer : γ * ‖u‖ ^ (2 : ℕ) ≤ inner ℝ f u) :
    ‖u‖ ≤ γ⁻¹ * ‖f‖ := by
  have hcs : (inner ℝ f u : ℝ) ≤ ‖f‖ * ‖u‖ := real_inner_le_norm f u
  have hchain : γ * ‖u‖ ^ (2 : ℕ) ≤ ‖f‖ * ‖u‖ := le_trans hcoer hcs
  rcases eq_or_lt_of_le (norm_nonneg u) with hzero | hposu
  · rw [← hzero]
    positivity
  · have hkey : γ * ‖u‖ ≤ ‖f‖ := by
      nlinarith [hposu, hchain]
    rw [inv_mul_eq_div, le_div_iff₀ hγ, mul_comm]
    exact hkey

/-! ## Observability -/

/-- **Equations (8)–(9).**  The exterior trace of the reconstruction is bounded by the cross-block
norm times the coercivity constant: every interior forcing is admissible. -/
theorem observability_bound {H E : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [NormedAddCommGroup E] {K : H → E} {M γ : ℝ} (hM : 0 ≤ M)
    (hKbound : ∀ x, ‖K x‖ ≤ M * ‖x‖) {u f : H} (hu : ‖u‖ ≤ γ⁻¹ * ‖f‖) :
    ‖K u‖ ≤ M * (γ⁻¹ * ‖f‖) :=
  le_trans (hKbound u) (mul_le_mul_of_nonneg_left hu hM)

end GaloisForLFunctions.RHTower

end
