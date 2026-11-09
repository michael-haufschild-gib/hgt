import GaloisForLFunctions.SurfaceOfSpecZ.TheSamplingSetsOfTheTopLayer

/-!
# A real top keeps the lower side bounded

`TheSamplingSetsOfTheTopLayer` shows that a lower bound on the spline traces at a sampling set,
for a configuration with an attained maximal real part `Re ρ₀ > ½`, forces `Re ρ₀` to be a real zero.
The converse boundary:

* `tendsto_normTrace_of_realTop`: if the only exponent of maximal real part `b` is `b` itself, the
  normalized trace `F(u) = 2 Re S(u) e^{−bu}` tends to its coefficient `e_b`.
* `bddBelow_two_re_lagStructure_of_realTop`: if `β > ½` is a real zero and every other zero has
  real part `< β`, then `2 Re S_Z(u) ≥ −K` for all `u ≥ 0`, in particular at every degree, while
  `Z` is off the line. Since `e_b > 0` (`evenCoeff_spline_pos_of_real`), `F ≥ 0` for large `u`.
* `tendsto_two_re_lagStructure_of_realTop`: in the same situation `2 Re S_Z(u) → +∞`, so no upper
  bound holds.

So the lower side at any set of degrees is blind to a configuration whose top layer is one real
zero, and sees every other attained top. For `L(s, χ)` with `χ` real this is the Siegel zero:
a lower-side count cannot rule it out, an upper-side count must.
-/

open Complex Filter Topology
open scoped ComplexConjugate

noncomputable section

namespace GaloisForLFunctions.SurfaceOfSpecZ

open ArithmeticOrientationGeometry ArithmeticCastelnuovoSeveri SquareRootThreshold Zeta23

/-- **The normalized trace tends to the real top coefficient** when `b` is the only exponent of
real part `b`. -/
theorem tendsto_normTrace_of_realTop {Z : ZeroConfig} (hZ : TemperedConfig Z) {b : ℝ}
    (h : TopDepth Z b) (honly : ∀ z, evenCoeff Z (boxSpline 1 3) z ≠ 0 → z.re = b → z = b) :
    Tendsto (normTrace Z b) atTop (𝓝 (evenCoeff Z (boxSpline 1 3) b).re) := by
  set e := evenCoeff Z (boxSpline 1 3) with hedef
  have hE := summable_norm_evenCoeff_spline hZ
  have hc : Tendsto (fun u : ℝ => ∑' z, e z * cexp ((z - b) * u)) atTop
      (𝓝 (∑' z : ℂ, if z = (b : ℂ) then e z else 0)) := by
    refine tendsto_tsum_of_dominated_convergence hE (fun z => ?_) ?_
    · by_cases hzb : z = (b : ℂ)
      · simp only [if_pos hzb]
        have hconst : ∀ u : ℝ, e z * cexp ((z - b) * u) = e z := by
          intro u; rw [hzb, sub_self, zero_mul, Complex.exp_zero, mul_one]
        simp only [hconst]
        exact tendsto_const_nhds
      · simp only [if_neg hzb]
        by_cases hz : e z = 0
        · simp [hz]
        have hlt : z.re < b := lt_of_le_of_ne (h z hz) (fun heq => hzb (honly z hz heq))
        have hexp : Tendsto (fun u : ℝ => cexp ((z - b) * u)) atTop (𝓝 0) := by
          rw [tendsto_zero_iff_norm_tendsto_zero]
          have hn : ∀ u : ℝ, ‖cexp ((z - b) * u)‖ = Real.exp ((z.re - b) * u) := by
            intro u; rw [Complex.norm_exp]; simp
          simp only [hn]
          exact Real.tendsto_exp_atBot.comp (tendsto_id.const_mul_atTop_of_neg (by linarith))
        simpa using hexp.const_mul (e z)
    · filter_upwards [eventually_ge_atTop 0] with u hu
      intro z
      exact norm_evenCoeff_mul_cexp_le h z hu
  rw [tsum_ite_eq] at hc
  have hc' := (Complex.continuous_re.tendsto _).comp hc
  refine hc'.congr' (Eventually.of_forall fun u => ?_)
  simp only [Function.comp_def]
  rw [← ofReal_normTrace hZ u, Complex.ofReal_re]

/-- The trace is the normalized trace times `e^{bu}`. -/
theorem two_re_lagStructure_eq_normTrace_mul (Z : ZeroConfig) (b u : ℝ) :
    2 * (lagStructure Z (boxSpline 1 3) u).re = normTrace Z b u * Real.exp (b * u) := by
  have h1 : Real.exp (-(b * u)) * Real.exp (b * u) = 1 := by rw [← Real.exp_add]; simp
  simp only [normTrace]
  linear_combination (-(2 * (lagStructure Z (boxSpline 1 3) u).re)) * h1

section RealTop

variable {Z : ZeroConfig} {β : ℝ}

/-- With a real zero `β` and every other zero left of it, the depth `β − ½` bounds every exponent and
`β − ½` is the only exponent of that real part. -/
theorem topDepth_and_only_of_realTop (hlt : ∀ ρ ∈ Z.carrier, ρ ≠ β → ρ.re < β) :
    TopDepth Z (β - 1 / 2) ∧
      ∀ z, evenCoeff Z (boxSpline 1 3) z ≠ 0 → z.re = β - 1 / 2 → z = ((β - 1 / 2 : ℝ) : ℂ) := by
  have hle : ∀ ρ ∈ Z.carrier, ρ.re ≤ β := fun ρ hρ => by
    by_cases h : ρ = β
    · rw [h]; simp
    · exact (hlt ρ hρ h).le
  constructor
  · intro z hz
    rcases mem_of_evenCoeff_ne_zero hz with h | h
    · have h1 := hle _ h; simp at h1; linarith
    · have h1 := hle _ h; simp at h1; linarith
  · intro z hz hzre
    rcases mem_of_evenCoeff_ne_zero hz with h | h
    · by_cases heq : (1 / 2 + z) = (β : ℂ)
      · push_cast; linear_combination heq
      · have := hlt _ h heq; simp at this; linarith
    · by_cases heq : (1 / 2 + conj z) = (β : ℂ)
      · have hc := congrArg conj heq
        simp only [map_add, Complex.conj_conj, Complex.conj_ofReal, map_div₀, map_one,
          map_ofNat] at hc
        push_cast; linear_combination hc
      · have := hlt _ h heq; simp at this; linarith

theorem evenCoeff_re_pos_of_realTop (hβ : (β : ℂ) ∈ Z.carrier) (hβh : 1 / 2 < β) :
    0 < (evenCoeff Z (boxSpline 1 3) ((β - 1 / 2 : ℝ) : ℂ)).re := by
  have hx : (1 / 2 + ((β - 1 / 2 : ℝ) : ℂ)) ∈ Z.carrier := by
    have : (1 / 2 + ((β - 1 / 2 : ℝ) : ℂ)) = (β : ℂ) := by push_cast; ring
    rw [this]; exact hβ
  exact evenCoeff_spline_pos_of_real Z hx (by simp; linarith) (by simp)

/-- **A real top keeps the lower side bounded.** If `β > ½` is a real zero and every other zero has
real part `< β`, the spline traces are bounded below on `u ≥ 0`. -/
theorem bddBelow_two_re_lagStructure_of_realTop (hZ : TemperedConfig Z)
    (hβ : (β : ℂ) ∈ Z.carrier) (hβh : 1 / 2 < β) (hlt : ∀ ρ ∈ Z.carrier, ρ ≠ β → ρ.re < β) :
    ∃ K : ℝ, ∀ u : ℝ, 0 ≤ u → -K ≤ 2 * (lagStructure Z (boxSpline 1 3) u).re := by
  set b : ℝ := β - 1 / 2 with hbdef
  have hb0 : 0 < b := by rw [hbdef]; linarith
  obtain ⟨htop, honly⟩ := topDepth_and_only_of_realTop hlt
  have hlim := tendsto_normTrace_of_realTop hZ htop honly
  obtain ⟨U, hU⟩ := eventually_atTop.mp
    (hlim.eventually (lt_mem_nhds (evenCoeff_re_pos_of_realTop hβ hβh)))
  set E := ∑' z, ‖evenCoeff Z (boxSpline 1 3) z‖ with hEdef
  have hE0 : 0 ≤ E := tsum_nonneg fun _ => norm_nonneg _
  refine ⟨E * Real.exp (b * max U 0), fun u hu => ?_⟩
  rw [two_re_lagStructure_eq_normTrace_mul Z b u]
  have hK0 : 0 ≤ E * Real.exp (b * max U 0) := mul_nonneg hE0 (Real.exp_pos _).le
  rcases le_total U u with hUu | huU
  · have := mul_nonneg (hU u hUu).le (Real.exp_pos (b * u)).le
    linarith
  · have hF := abs_normTrace_le hZ htop hu
    have h1 : Real.exp (b * u) ≤ Real.exp (b * max U 0) :=
      Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (huU.trans (le_max_left _ _)) hb0.le)
    have h3 : -E * Real.exp (b * u) ≤ normTrace Z b u * Real.exp (b * u) :=
      mul_le_mul_of_nonneg_right (abs_le.mp hF).1 (Real.exp_pos _).le
    have h4 : E * Real.exp (b * u) ≤ E * Real.exp (b * max U 0) := mul_le_mul_of_nonneg_left h1 hE0
    linarith

/-- At every degree `n ≥ 1`, in particular at the prime powers. -/
theorem bddBelow_natDegrees_of_realTop (hZ : TemperedConfig Z)
    (hβ : (β : ℂ) ∈ Z.carrier) (hβh : 1 / 2 < β) (hlt : ∀ ρ ∈ Z.carrier, ρ ≠ β → ρ.re < β) :
    ∃ K : ℝ, ∀ n : ℕ, -K ≤ 2 * (lagStructure Z (boxSpline 1 3) (Real.log n)).re := by
  obtain ⟨K, hK⟩ := bddBelow_two_re_lagStructure_of_realTop hZ hβ hβh hlt
  exact ⟨K, fun n => hK _ (Real.log_natCast_nonneg n)⟩

/-- **The upper side sees a real top**: the traces tend to `+∞`. -/
theorem tendsto_two_re_lagStructure_of_realTop (hZ : TemperedConfig Z)
    (hβ : (β : ℂ) ∈ Z.carrier) (hβh : 1 / 2 < β) (hlt : ∀ ρ ∈ Z.carrier, ρ ≠ β → ρ.re < β) :
    Tendsto (fun u => 2 * (lagStructure Z (boxSpline 1 3) u).re) atTop atTop := by
  set b : ℝ := β - 1 / 2 with hbdef
  have hb0 : 0 < b := by rw [hbdef]; linarith
  obtain ⟨htop, honly⟩ := topDepth_and_only_of_realTop hlt
  have hlim := tendsto_normTrace_of_realTop hZ htop honly
  have hexp : Tendsto (fun u : ℝ => Real.exp (b * u)) atTop atTop :=
    Real.tendsto_exp_atTop.comp (tendsto_id.const_mul_atTop hb0)
  refine (hlim.pos_mul_atTop (evenCoeff_re_pos_of_realTop hβ hβh) hexp).congr fun u => ?_
  exact (two_re_lagStructure_eq_normTrace_mul Z b u).symm

end RealTop

end GaloisForLFunctions.SurfaceOfSpecZ
