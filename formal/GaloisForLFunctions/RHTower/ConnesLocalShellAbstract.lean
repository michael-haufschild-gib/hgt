import GaloisForLFunctions.RHTower.ConnesUnramifiedLocalZeta

/-!
# The local Tate computations over an arbitrary non-archimedean local field

Appendix I (25)-(26) and Lemma 1 of

  A. Connes, *Trace formula in noncommutative geometry and the zeros of the Riemann zeta
  function*, arXiv:math/9811068.

For every non-archimedean local field the valuation/unit decomposition identifies the
multiplicative group with `π^ℤ × O^*` and the multiplicative Haar measure, normalized by
`vol(O^*) = 1`, with `counting ⊗ (probability Haar on the units)`.  All of Connes' local
computations depend on the field only through that structure, so they are proved here once and
for all on the abstract shell space `Multiplicative ℤ × U` with `U` any probability space: the
radial integral is the plain shell sum, an unramified quasi-character gives the geometric factor
`(1 - Χ(π)q^{-s})^{-1}`, and a ramified one gives zero.  The `ℚ_p` statements of the preceding
modules are the instance `U = ℤ_p^*`.
-/

open MeasureTheory

namespace GaloisForLFunctions.RHTower

noncomputable section

variable {U : Type*} [MeasurableSpace U] (ν : Measure U) [IsProbabilityMeasure ν]

/-- The multiplicative Haar measure of a non-archimedean local field in the valuation/unit
chart: counting measure on the valuation times normalized Haar on the units. -/
def connesShellMeasure : Measure (Multiplicative ℤ × U) := (Measure.count).prod ν

/-- A radial function on the shell space: a function of the valuation alone. -/
def connesShellRadial (h : ℤ → ℂ) : Multiplicative ℤ × U → ℂ := fun z => h z.1.toAdd

theorem connes_shell_radial_integrable {h : ℤ → ℂ} (hs : Summable fun m : ℤ => ‖h m‖) :
    Integrable (connesShellRadial h) (connesShellMeasure ν) := by
  have hmeas : AEStronglyMeasurable (connesShellRadial h) (connesShellMeasure ν) := by
    refine (Measurable.aestronglyMeasurable ?_)
    exact (continuous_of_discreteTopology (α := Multiplicative ℤ)
      (β := ℂ) (f := fun k => h k.toAdd)).measurable.comp measurable_fst
  have hsum' : Summable fun k : Multiplicative ℤ => ‖h k.toAdd‖ :=
    (Multiplicative.ofAdd (α := ℤ)).summable_iff.mp hs
  rw [connesShellMeasure]
  refine (integrable_prod_iff hmeas).mpr ⟨?_, ?_⟩
  · filter_upwards with k
    exact integrable_const (h k.toAdd)
  · have houter : (fun k : Multiplicative ℤ =>
        ∫ _u, ‖connesShellRadial h (k, _u)‖ ∂ν) = fun k => ‖h k.toAdd‖ := by
      funext k
      simp [connesShellRadial, Measure.real]
    rw [houter, integrable_count_iff]
    simpa using hsum'

/-- **The radial integral is the shell sum.** -/
theorem connes_shell_radial_integral {h : ℤ → ℂ} (hs : Summable fun m : ℤ => ‖h m‖) :
    (∫ z, connesShellRadial h z ∂(connesShellMeasure ν)) = ∑' m : ℤ, h m := by
  have hint := connes_shell_radial_integrable ν hs
  rw [connesShellMeasure] at hint ⊢
  rw [integral_prod _ hint]
  have houter : (fun k : Multiplicative ℤ =>
      ∫ _u, connesShellRadial h (k, _u) ∂ν) = fun k => h k.toAdd := by
    funext k
    simp [connesShellRadial, Measure.real]
  have hsum' : Summable fun k : Multiplicative ℤ => ‖h k.toAdd‖ :=
    ((Multiplicative.ofAdd (α := ℤ)).summable_iff
      (f := fun k : Multiplicative ℤ => ‖h k.toAdd‖)).mp hs
  have hcount : Integrable (fun k : Multiplicative ℤ => h k.toAdd) Measure.count := by
    rw [integrable_count_iff]
    simpa using hsum'
  rw [houter, integral_countable]
  · have hsmul : ∀ k : Multiplicative ℤ,
        (Measure.count (α := Multiplicative ℤ)).real {k} • h k.toAdd = h k.toAdd := by
      intro k
      simp [Measure.real, Measure.count_apply]
    rw [tsum_congr hsmul]
    exact (Multiplicative.ofAdd (α := ℤ)).tsum_eq (fun k : Multiplicative ℤ => h k.toAdd)
  · exact hcount

/-- The unit-ball shell sum of an unramified quasi-character. -/
theorem connes_unitBallProfile_tsum {w : ℂ} (hw : ‖w‖ < 1) :
    (∑' m : ℤ, connesPadicUnitBallProfile w m) = (1 - w)⁻¹ := by
  have hsummable : Summable (connesPadicUnitBallProfile w) :=
    (connes_padic_unitBallProfile_summable hw).of_norm
  have hnat : Summable fun n : ℕ => connesPadicUnitBallProfile w (n : ℤ) :=
    hsummable.comp_injective (fun a b hab => by exact_mod_cast hab)
  have hneg : Summable fun n : ℕ => connesPadicUnitBallProfile w (-((n : ℤ) + 1)) := by
    refine summable_zero.congr fun n => ?_
    rw [connesPadicUnitBallProfile, if_neg (by omega : ¬ (0 : ℤ) ≤ -((n : ℤ) + 1))]
  rw [tsum_of_nat_of_neg_add_one hnat hneg]
  have hzero : (∑' n : ℕ, connesPadicUnitBallProfile w (-((n : ℤ) + 1))) = 0 := by
    have hfun : (fun n : ℕ => connesPadicUnitBallProfile w (-((n : ℤ) + 1)))
        = fun _ : ℕ => (0 : ℂ) := by
      funext n
      rw [connesPadicUnitBallProfile, if_neg (by omega : ¬ (0 : ℤ) ≤ -((n : ℤ) + 1))]
    rw [hfun, tsum_zero]
  have hpos : (∑' n : ℕ, connesPadicUnitBallProfile w (n : ℤ)) = (1 - w)⁻¹ := by
    have hcongr : (fun n : ℕ => connesPadicUnitBallProfile w (n : ℤ)) = fun n : ℕ => w ^ n := by
      funext n
      rw [connesPadicUnitBallProfile, if_pos (Int.natCast_nonneg n), Int.toNat_natCast]
    rw [hcongr, tsum_geometric_of_norm_lt_one hw]
  rw [hzero, hpos, add_zero]

/-- **Appendix I (25)/(26) over an arbitrary non-archimedean local field.**  The Tate zeta
integral of an unramified quasi-character over the unit ball is `(1 - Χ(π) q^{-s})^{-1}`. -/
theorem connes_shell_unitBall_geometric {w : ℂ} (hw : ‖w‖ < 1) :
    (∫ z, connesShellRadial (connesPadicUnitBallProfile w) z ∂(connesShellMeasure ν))
      = (1 - w)⁻¹ := by
  rw [connes_shell_radial_integral ν (connes_padic_unitBallProfile_summable hw),
    connes_unitBallProfile_tsum hw]

/-- **Appendix I Lemma 1 at a ramified place, over an arbitrary non-archimedean local field.**
If the angular profile has zero mean on the units, the local integral vanishes. -/
theorem connes_shell_ramified_vanishes (f : Multiplicative ℤ × U → ℂ) (g : ℤ → ℂ) (a : U → ℂ)
    (hcoord : ∀ (m : ℤ) (u : U), f (Multiplicative.ofAdd m, u) = g m * a u)
    (hmean : (∫ u, a u ∂ν) = 0)
    (hf : Integrable f (connesShellMeasure ν)) :
    (∫ z, f z ∂(connesShellMeasure ν)) = 0 := by
  rw [connesShellMeasure] at hf ⊢
  rw [integral_prod _ hf]
  have hinner : ∀ k : Multiplicative ℤ, (∫ u, f (k, u) ∂ν) = 0 := by
    intro k
    have hpoint : ∀ u : U, f (k, u) = g k.toAdd * a u := by
      intro u
      have hkrep : k = Multiplicative.ofAdd k.toAdd :=
        (Multiplicative.ofAdd.apply_symm_apply k).symm
      rw [hkrep]
      exact hcoord k.toAdd u
    rw [integral_congr_ae (Filter.Eventually.of_forall hpoint), integral_const_mul, hmean,
      mul_zero]
  simp [hinner]

omit [IsProbabilityMeasure ν] in
/-- **Transfer to a concrete local field.**  Any multiplicative group whose Haar measure is the
push-forward of the shell measure inherits all the shell formulas. -/
theorem connes_shell_transfer_integral {G : Type*} [MeasurableSpace G] (μ : Measure G)
    (e : Multiplicative ℤ × U ≃ᵐ G) (hμ : μ = Measure.map e (connesShellMeasure ν))
    (F : G → ℂ) :
    (∫ x, F x ∂μ) = ∫ z, F (e z) ∂(connesShellMeasure ν) := by
  rw [hμ, integral_map_equiv]

end

end GaloisForLFunctions.RHTower
