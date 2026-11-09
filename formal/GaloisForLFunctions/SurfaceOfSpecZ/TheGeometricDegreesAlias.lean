import GaloisForLFunctions.SurfaceOfSpecZ.ARealZeroMasksTheShallowerZeros

/-!
# The geometric degrees alias

Over `𝔽_q` the degrees are the powers `qⁿ`. Sampled at `u = n log q`, the exponents `z` and
`z + 2πim/log q` cannot be told apart, and a zero at height `2πm/log q` looks like a real zero.

* `aliasing_geometricDegrees`: for every `q ≥ 2` the off-line pair `{¾ + iγ, ¼ + iγ}`, `γ = 2π/log q`,
  has no real zero, and its spline traces at the degrees `qⁿ` are
  `2 Re(c₁) q^{n/4} + 2 Re(c₂) q^{−n/4}` (`two_re_lagStructure_aliasPair`): they are bounded on one
  side. At the geometric degrees at least one of the two one-sided criteria fails, while at all `u ≥ 0`
  the upper bound sees every zero (`TheOtherSideSeesEveryZero`) and the lower bound every non-real
  one (`TheStepanovSideIsBlindToRealZeros`).

On a curve the aliasing heights are the real Frobenius eigenvalues `α = q^ρ`. The integer and the
prime degrees have no aliasing: the `log n` are not commensurable.
-/

open Complex Set

noncomputable section

namespace GaloisForLFunctions.SurfaceOfSpecZ

open ArithmeticOrientationGeometry ArithmeticCastelnuovoSeveri SquareRootThreshold Zeta23

/-- The aliasing height `2π/log q`. -/
def aliasHeight (q : ℕ) : ℝ := 2 * Real.pi / Real.log q

/-- The off-line pair `{¾ + iγ, ¼ + iγ}` at the aliasing height. -/
abbrev aliasPair (q : ℕ) : ZeroConfig := _root_.RHTower.offLinePairConfig (aliasHeight q)

theorem temperedConfig_aliasPair (q : ℕ) : TemperedConfig (aliasPair q) := by
  have hfin : (aliasPair q).carrier.Finite := (Set.finite_singleton _).insert _
  haveI := hfin.to_subtype
  exact Summable.of_finite

theorem mem_aliasPair_iff (q : ℕ) (ρ : ℂ) : ρ ∈ (aliasPair q).carrier ↔
    ρ = ⟨3 / 4, aliasHeight q⟩ ∨ ρ = ⟨1 / 4, aliasHeight q⟩ := Iff.rfl

/-- **The lag structure of the pair.** -/
theorem lagStructure_aliasPair (q : ℕ) (u : ℝ) :
    lagStructure (aliasPair q) (boxSpline 1 3) u =
      lagCoeff (aliasPair q) (boxSpline 1 3) ((1 / 4 : ℂ) + aliasHeight q * I) *
          cexp (((1 / 4 : ℂ) + aliasHeight q * I) * u) +
        lagCoeff (aliasPair q) (boxSpline 1 3) ((-1 / 4 : ℂ) + aliasHeight q * I) *
          cexp (((-1 / 4 : ℂ) + aliasHeight q * I) * u) := by
  have hb := contDiff_boxSpline (r := 1) one_pos 2
  have hbs := boxSpline_support (r := 1) one_pos 3
  obtain ⟨-, he⟩ := lagStructure_eq_tsum_lagCoeff (aliasPair q) (temperedConfig_aliasPair q) hb hbs u
  set z₁ : ℂ := (1 / 4 : ℂ) + aliasHeight q * I with hz₁
  set z₂ : ℂ := (-1 / 4 : ℂ) + aliasHeight q * I with hz₂
  have hne : z₁ ≠ z₂ := fun h => by
    have := congrArg Complex.re h; simp [hz₁, hz₂] at this; linarith
  have hsupp : ∀ z ∉ ({z₁, z₂} : Finset ℂ),
      lagCoeff (aliasPair q) (boxSpline 1 3) z * cexp (z * u) = 0 := by
    intro z hz
    have hnot : (1 / 2 + z) ∉ (aliasPair q).carrier := by
      rw [mem_aliasPair_iff]
      rintro (h | h)
      · apply hz; rw [Finset.mem_insert]; left
        have h1 := congrArg Complex.re h; have h2 := congrArg Complex.im h
        simp at h1 h2
        apply Complex.ext <;> simp [hz₁] <;> linarith
      · apply hz; rw [Finset.mem_insert, Finset.mem_singleton]; right
        have h1 := congrArg Complex.re h; have h2 := congrArg Complex.im h
        simp at h1 h2
        apply Complex.ext <;> simp [hz₂] <;> linarith
    rw [lagCoeff, Set.indicator_of_notMem hnot, zero_mul]
  rw [he, tsum_eq_sum hsupp, Finset.sum_pair hne]

/-- **The traces at the degrees `qⁿ`.** At `u = n log q` the oscillation `e^{iγu}` is `1`. -/
theorem two_re_lagStructure_aliasPair {q : ℕ} (hq : 2 ≤ q) (n : ℕ) :
    2 * (lagStructure (aliasPair q) (boxSpline 1 3) (n * Real.log q)).re =
      2 * (lagCoeff (aliasPair q) (boxSpline 1 3) ((1 / 4 : ℂ) + aliasHeight q * I)).re *
          Real.exp (n * Real.log q / 4) +
        2 * (lagCoeff (aliasPair q) (boxSpline 1 3) ((-1 / 4 : ℂ) + aliasHeight q * I)).re *
          Real.exp (-(n * Real.log q / 4)) := by
  have hlog : 0 < Real.log q := Real.log_pos (by exact_mod_cast hq)
  have hγ : (aliasHeight q : ℝ) * (n * Real.log q) = n * (2 * Real.pi) := by
    unfold aliasHeight; field_simp
  have hγc : ((aliasHeight q : ℝ) : ℂ) * ((n * Real.log q : ℝ) : ℂ) = (n : ℂ) * (2 * (Real.pi : ℂ)) := by
    rw [← Complex.ofReal_mul, hγ]; push_cast; ring
  have e1 : cexp (((1 / 4 : ℂ) + (aliasHeight q : ℂ) * I) * ((n * Real.log q : ℝ) : ℂ)) =
      ((Real.exp (n * Real.log q / 4) : ℝ) : ℂ) := by
    have h1 : ((1 / 4 : ℂ) + (aliasHeight q : ℂ) * I) * ((n * Real.log q : ℝ) : ℂ) =
        ((n * Real.log q / 4 : ℝ) : ℂ) + (n : ℂ) * (2 * Real.pi * I) := by
      have : ((n * Real.log q / 4 : ℝ) : ℂ) = (1 / 4 : ℂ) * ((n * Real.log q : ℝ) : ℂ) := by
        push_cast; ring
      rw [this]; linear_combination I * hγc
    rw [h1, Complex.exp_add, Complex.exp_nat_mul_two_pi_mul_I, mul_one, Complex.ofReal_exp]
  have e2 : cexp (((-1 / 4 : ℂ) + (aliasHeight q : ℂ) * I) * ((n * Real.log q : ℝ) : ℂ)) =
      ((Real.exp (-(n * Real.log q / 4)) : ℝ) : ℂ) := by
    have h1 : ((-1 / 4 : ℂ) + (aliasHeight q : ℂ) * I) * ((n * Real.log q : ℝ) : ℂ) =
        ((-(n * Real.log q / 4) : ℝ) : ℂ) + (n : ℂ) * (2 * Real.pi * I) := by
      have : ((-(n * Real.log q / 4) : ℝ) : ℂ) = (-1 / 4 : ℂ) * ((n * Real.log q : ℝ) : ℂ) := by
        push_cast; ring
      rw [this]; linear_combination I * hγc
    rw [h1, Complex.exp_add, Complex.exp_nat_mul_two_pi_mul_I, mul_one, Complex.ofReal_exp]
  rw [lagStructure_aliasPair, e1, e2, Complex.add_re, Complex.mul_re, Complex.mul_re,
    Complex.ofReal_re, Complex.ofReal_im, Complex.ofReal_re, Complex.ofReal_im]
  ring

/-- **The geometric degrees alias.** For every `q ≥ 2` there is an off-line configuration without
real zeros whose spline traces at the degrees `qⁿ` are bounded on one side. -/
theorem aliasing_geometricDegrees {q : ℕ} (hq : 2 ≤ q) :
    (∀ ρ ∈ (aliasPair q).carrier, ρ.im ≠ 0) ∧ (∃ ρ ∈ (aliasPair q).carrier, ρ.re ≠ 1 / 2) ∧
      ((∃ K : ℝ, ∀ n : ℕ,
          -K ≤ 2 * (lagStructure (aliasPair q) (boxSpline 1 3) (n * Real.log q)).re) ∨
        (∃ K : ℝ, ∀ n : ℕ,
          2 * (lagStructure (aliasPair q) (boxSpline 1 3) (n * Real.log q)).re ≤ K)) := by
  have hlog : 0 < Real.log q := Real.log_pos (by exact_mod_cast hq)
  have hγ : 0 < aliasHeight q := by unfold aliasHeight; positivity
  refine ⟨fun ρ hρ => ?_, ⟨⟨3 / 4, aliasHeight q⟩, (mem_aliasPair_iff q _).mpr (Or.inl rfl),
    by norm_num⟩, ?_⟩
  · rcases (mem_aliasPair_iff q ρ).mp hρ with h | h <;> rw [h] <;> exact hγ.ne'
  set c₁ := (lagCoeff (aliasPair q) (boxSpline 1 3) ((1 / 4 : ℂ) + aliasHeight q * I)).re
  set c₂ := (lagCoeff (aliasPair q) (boxSpline 1 3) ((-1 / 4 : ℂ) + aliasHeight q * I)).re
  have hform : ∀ n : ℕ, 2 * (lagStructure (aliasPair q) (boxSpline 1 3) (n * Real.log q)).re =
      2 * c₁ * Real.exp (n * Real.log q / 4) + 2 * c₂ * Real.exp (-(n * Real.log q / 4)) :=
    fun n => two_re_lagStructure_aliasPair hq n
  have hdecay : ∀ n : ℕ, Real.exp (-(n * Real.log q / 4)) ≤ 1 := fun n =>
    Real.exp_le_one_iff.mpr (by have := Nat.cast_nonneg (α := ℝ) n; nlinarith)
  have hdpos : ∀ n : ℕ, 0 < Real.exp (-(n * Real.log q / 4)) := fun n => Real.exp_pos _
  rcases le_total 0 c₁ with h | h
  · left
    refine ⟨2 * |c₂|, fun n => ?_⟩
    rw [hform n]
    have h1 : 0 ≤ 2 * c₁ * Real.exp (n * Real.log q / 4) := by positivity
    have h2 : -(2 * |c₂|) ≤ 2 * c₂ * Real.exp (-(n * Real.log q / 4)) := by
      have := mul_le_mul_of_nonneg_left (hdecay n) (abs_nonneg c₂)
      nlinarith [neg_abs_le c₂, hdpos n]
    linarith
  · right
    refine ⟨2 * |c₂|, fun n => ?_⟩
    rw [hform n]
    have h1 : 2 * c₁ * Real.exp (n * Real.log q / 4) ≤ 0 := by
      have := Real.exp_pos (n * Real.log q / 4); nlinarith
    have h2 : 2 * c₂ * Real.exp (-(n * Real.log q / 4)) ≤ 2 * |c₂| := by
      have := mul_le_mul_of_nonneg_left (hdecay n) (abs_nonneg c₂)
      nlinarith [le_abs_self c₂, hdpos n]
    linarith

end GaloisForLFunctions.SurfaceOfSpecZ
