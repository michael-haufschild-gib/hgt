import GaloisForLFunctions.RHTower.ConnesPadicWeilShellIntegral

/-!
# Radial functions on `ℚ_p^*` and the local Weil term

Appendix II (9)-(10) of

  A. Connes, *Trace formula in noncommutative geometry and the zeros of the Riemann zeta
  function*, arXiv:math/9811068,

in closed form.  A radial function on `ℚ_p^*` is a function of the valuation alone.  Its
multiplicative-Haar integral is the plain sum of its shell values, because the unit group has
normalized mass one.  Multiplying by the local Weil kernel `|1-u|^{-1}` reweights the shell
`m` by `min(1, p^m)`, so the local Weil term of a radial function vanishing on the unit shell
is the explicit series `∑_{m ≠ 0} min(1, p^m) h(m)`.
-/

open MeasureTheory

namespace GaloisForLFunctions.RHTower

noncomputable section

variable (p : ℕ) [Fact p.Prime]

/-- The normalized unit Haar measure of `ℤ_p^*` is a probability measure. -/
theorem connes_padic_unitHaar_isProbability :
    IsProbabilityMeasure (fieldOnePadicUnitNormalizedHaar p) :=
  ⟨fieldOnePadicUnitNormalizedHaar_univ p⟩

/-- The radial function attached to a shell profile `h : ℤ → ℂ`. -/
def connesPadicRadial (h : ℤ → ℂ) : ℚ_[p]ˣ → ℂ :=
  fun a => h (Padic.valuation (a : ℚ_[p]))

theorem connesPadicRadial_chart (h : ℤ → ℂ) (m : ℤ) (u : ℤ_[p]ˣ) :
    connesPadicRadial p h
        (fieldOnePadicValuationUnitContinuousMulEquiv p (Multiplicative.ofAdd m, u)) = h m := by
  unfold connesPadicRadial
  rw [fieldOnePadicValuationUnitContinuousMulEquiv_apply]
  simpa using congrArg h (fieldOnePadic_valuation_forward p (Multiplicative.ofAdd m, u))

/-- **A radial function is multiplicatively integrable iff its shell profile is summable.** -/
theorem connes_padic_radial_integrable (h : ℤ → ℂ) (hs : Summable fun m : ℤ => ‖h m‖) :
    Integrable (connesPadicRadial p h) (fieldOnePadicMultiplicativeHaar p) := by
  haveI := connes_padic_unitHaar_isProbability p
  let e := fieldOnePadicValuationUnitContinuousMulEquiv p
  let μ := fieldOnePadicValuationUnitProductHaar p
  let F : Multiplicative ℤ × ℤ_[p]ˣ → ℂ := fun z => h z.1.toAdd
  have hcomp : (fun z => connesPadicRadial p h (e z)) = F := by
    funext z
    have hzpair : z = (Multiplicative.ofAdd z.1.toAdd, z.2) :=
      Prod.ext (Multiplicative.ofAdd.apply_symm_apply z.1).symm rfl
    change connesPadicRadial p h (e z) = F z
    rw [hzpair]
    exact connesPadicRadial_chart p h z.1.toAdd z.2
  have hshellmeas : Measurable fun k : Multiplicative ℤ => h k.toAdd :=
    continuous_of_discreteTopology.measurable
  have hFmeas : AEStronglyMeasurable F μ :=
    (hshellmeas.comp measurable_fst).aestronglyMeasurable
  have hsum' : Summable fun k : Multiplicative ℤ => ‖h k.toAdd‖ :=
    (Multiplicative.ofAdd (α := ℤ)).summable_iff.mp hs
  have hFint : Integrable F μ := by
    change Integrable F (Measure.count.prod (fieldOnePadicUnitNormalizedHaar p))
    refine (integrable_prod_iff hFmeas).mpr ⟨?_, ?_⟩
    · filter_upwards with k
      exact integrable_const (h k.toAdd)
    · have houter : (fun k : Multiplicative ℤ =>
          ∫ _u, ‖F (k, _u)‖ ∂fieldOnePadicUnitNormalizedHaar p) = fun k => ‖h k.toAdd‖ := by
        funext k
        simp [F, Measure.real]
      rw [houter, integrable_count_iff]
      simpa using hsum'
  change Integrable (connesPadicRadial p h) (Measure.map e μ)
  apply (integrable_map_equiv e.toHomeomorph.toMeasurableEquiv _).mpr
  change Integrable (fun z => connesPadicRadial p h (e z)) μ
  rw [hcomp]
  exact hFint

/-- **The multiplicative-Haar integral of a radial function is the sum of its shell values.** -/
theorem connes_padic_radial_integral (h : ℤ → ℂ) (hs : Summable fun m : ℤ => ‖h m‖) :
    ∫ a, connesPadicRadial p h a ∂fieldOnePadicMultiplicativeHaar p = ∑' m : ℤ, h m := by
  haveI := connes_padic_unitHaar_isProbability p
  rw [fieldOnePadicMultiplicativeHaar_integral_eq_tsum p _
    (connes_padic_radial_integrable p h hs)]
  have hterm : (fun k : Multiplicative ℤ =>
      ∫ u : ℤ_[p]ˣ, connesPadicRadial p h
        (fieldOnePadicValuationUnitContinuousMulEquiv p (k, u))
        ∂fieldOnePadicUnitNormalizedHaar p) = fun k => h k.toAdd := by
    funext k
    have hkrep : k = Multiplicative.ofAdd k.toAdd :=
      (Multiplicative.ofAdd.apply_symm_apply k).symm
    rw [hkrep]
    simp only [connesPadicRadial_chart p h k.toAdd]
    simp [Measure.real]
  rw [hterm]
  exact ((Multiplicative.ofAdd (α := ℤ)).tsum_eq fun k => h k.toAdd).symm

/-- **Appendix II (9)/(10) in closed form.**  For a radial profile vanishing on the unit shell
the local non-archimedean Weil term is the explicit series `∑_{m} min(1, p^m) h(m)`. -/
theorem connes_padic_weil_radial (h : ℤ → ℂ) (h0 : h 0 = 0)
    (hs : Summable fun m : ℤ => ‖((min 1 ((p : ℝ) ^ m) : ℝ) : ℂ) * h m‖) :
    ∫ a, connesPadicRadial p h a * ((‖1 - (a : ℚ_[p])‖⁻¹ : ℝ) : ℂ)
        ∂fieldOnePadicMultiplicativeHaar p
      = ∑' m : ℤ, ((min 1 ((p : ℝ) ^ m) : ℝ) : ℂ) * h m := by
  set h' : ℤ → ℂ := fun m => ((min 1 ((p : ℝ) ^ m) : ℝ) : ℂ) * h m with hh'
  have hpoint : (fun a : ℚ_[p]ˣ =>
      connesPadicRadial p h a * ((‖1 - (a : ℚ_[p])‖⁻¹ : ℝ) : ℂ)) = connesPadicRadial p h' := by
    funext a
    by_cases hm : Padic.valuation (a : ℚ_[p]) = 0
    · have hz : connesPadicRadial p h a = 0 := by
        unfold connesPadicRadial; rw [hm, h0]
      have hz' : connesPadicRadial p h' a = 0 := by
        unfold connesPadicRadial; rw [hm]; simp [hh', h0]
      rw [hz, hz', zero_mul]
    · have hnorm : ‖(a : ℚ_[p])‖ = (p : ℝ) ^ (-Padic.valuation (a : ℚ_[p])) :=
        Padic.norm_eq_zpow_neg_valuation (Units.ne_zero a)
      rw [connes_padic_weilKernel_shell hm hnorm]
      unfold connesPadicRadial
      rw [hh']
      exact mul_comm _ _
  rw [hpoint]
  exact connes_padic_radial_integral p h' hs

end

end GaloisForLFunctions.RHTower
