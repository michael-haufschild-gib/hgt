import GaloisForLFunctions.RHTower.DeBruijnLaguerreLargeHeight
import GaloisForLFunctions.HTGeometry.EntireZeroSetNull

/-!
# The Laguerre shadow of the off-line zeros of `Ξ`

Write `Ξ = H_0` (`Ξ(z) = ξ(½ + iz)`). A zero `ζ = γ − i(β − ½)` of `Ξ` casts the *shadow*
`(γ − |β − ½|, γ + |β − ½|)` on the real axis. By the local pair law, a conjugate pair of zeros never
obstructs vertical growth of `|Ξ|` at abscissae outside its shadow, so at every real `x` outside
the union `S` of all shadows (`xiShadow`):

* `y ↦ |Ξ(x + iy)|` is nondecreasing on `y ≥ 0`;
* the first Laguerre inequality `Ξ'(x)² − Ξ(x)Ξ''(x) ≥ 0` holds
  (`monotoneOn_laguerre_of_not_mem_xiShadow`).

The Riemann hypothesis is exactly `S = ∅` (`riemannHypothesis_iff_xiShadow_eq_empty`), and the
failure set is small in measure when the off-line zeros are close to the line:
`vol(S ∩ [a, b]) ≤ Σ 2|Im ζ|` over the zeros with `Re ζ ∈ [a − ½, b + ½]`
(`volume_xiShadow_inter_Icc_le`), i.e. twice the horizontal first moment `Σ (β − ½)⁺` of the
off-line zeros of `ζ` at heights in that window.
-/

open Complex Filter Topology Set MeasureTheory

namespace RHTower.DeBruijn

noncomputable section

/-- The union of the shadows of the zeros of `Ξ = H_0`. -/
def xiShadow : Set ℝ := {x | ∃ ζ : ℂ, riemannHeat 0 ζ = 0 ∧ (ζ.re - x) ^ 2 < ζ.im ^ 2}

/-- **Vertical monotonicity and Laguerre off the shadow.** -/
theorem monotoneOn_laguerre_of_not_mem_xiShadow {x : ℝ} (hx : x ∉ xiShadow) :
    MonotoneOn (fun y : ℝ => ‖riemannHeat 0 ((x : ℂ) + I * y)‖) (Ici 0) ∧
      0 ≤ (deriv (riemannHeat 0) x ^ 2 -
        riemannHeat 0 x * deriv (deriv (riemannHeat 0)) x).re := by
  have hloc : ∀ ζ, riemannHeat 0 ζ = 0 → ζ.im ^ 2 ≤ (ζ.re - x) ^ 2 := by
    intro ζ hζ
    by_contra h
    exact hx ⟨ζ, hζ, not_le.mp h⟩
  have hmono := monotoneOn_norm_riemannHeat_vertical le_rfl hloc
  exact ⟨hmono, laguerre_of_monotoneOn_norm_vertical (differentiable_riemannHeat le_rfl)
    (riemannHeat_conj le_rfl) hmono⟩

/-- **RH is the emptiness of the shadow.** -/
theorem riemannHypothesis_iff_xiShadow_eq_empty : RiemannHypothesis ↔ xiShadow = ∅ := by
  rw [riemannHypothesis_iff_riemannHeat_zero_real]
  constructor
  · intro h
    ext x
    simp only [xiShadow, mem_setOf_eq, mem_empty_iff_false, iff_false, not_exists, not_and]
    intro ζ hζ
    rw [h ζ hζ]
    nlinarith [sq_nonneg (ζ.re - x)]
  · intro h ζ hζ
    by_contra hne
    have : ζ.re ∈ xiShadow := ⟨ζ, hζ, by simp; positivity⟩
    rw [h] at this
    exact this

/-- The shadow is covered by the open intervals `(Re ζ − |Im ζ|, Re ζ + |Im ζ|)`. -/
theorem xiShadow_subset :
    xiShadow ⊆ ⋃ ζ ∈ {ζ : ℂ | riemannHeat 0 ζ = 0}, Ioo (ζ.re - |ζ.im|) (ζ.re + |ζ.im|) := by
  intro x ⟨ζ, hζ, hlt⟩
  refine mem_biUnion hζ ?_
  have h := sq_lt_sq.mp hlt
  rw [abs_lt] at h
  constructor <;> linarith [h.1, h.2, le_abs_self ζ.im, neg_abs_le ζ.im]

theorem countable_xi_zeros : {ζ : ℂ | riemannHeat 0 ζ = 0}.Countable :=
  HTGeometry.countable_setOf_eq_zero_of_analyticOnNhd (riemannHeat_analytic le_rfl)
    ⟨0, riemannHeat_zero_ne le_rfl⟩

/-- **The measure of the shadow.** On `[a, b]` the shadow has measure at most the sum of
`2|Im ζ|` over the zeros `ζ` of `Ξ` with `a − ½ ≤ Re ζ ≤ b + ½`. -/
theorem volume_xiShadow_inter_Icc_le (a b : ℝ) :
    volume (xiShadow ∩ Icc a b) ≤
      ∑' ζ : {ζ : ℂ | riemannHeat 0 ζ = 0 ∧ ζ.re ∈ Icc (a - 1 / 2) (b + 1 / 2)},
        ENNReal.ofReal (2 * |(ζ : ℂ).im|) := by
  set Z := {ζ : ℂ | riemannHeat 0 ζ = 0 ∧ ζ.re ∈ Icc (a - 1 / 2) (b + 1 / 2)} with hZ
  have hZc : Z.Countable := countable_xi_zeros.mono fun ζ hζ => hζ.1
  have hsub : xiShadow ∩ Icc a b ⊆ ⋃ ζ ∈ Z, Ioo (ζ.re - |ζ.im|) (ζ.re + |ζ.im|) := by
    intro x ⟨⟨ζ, hζ, hlt⟩, hxab⟩
    have h := sq_lt_sq.mp hlt
    rw [abs_lt] at h
    have him : ζ.im ^ 2 ≤ 1 / 4 := by
      have h0 : cosTransform riemannKernelReal ζ = 0 := by
        rw [cosTransform_riemannKernel, ← riemannHeat_zero]; exact hζ
      exact riemannKernel_zeros_im_sq_le ζ h0
    have habs : |ζ.im| ≤ 1 / 2 := by
      rw [← sq_le_sq₀ (abs_nonneg _) (by norm_num), sq_abs]; linarith
    refine mem_biUnion (x := ζ) ⟨hζ, ?_, ?_⟩ ?_
    · linarith [hxab.1, h.2]
    · linarith [hxab.2, h.1]
    · constructor <;> linarith [h.1, h.2, le_abs_self ζ.im, neg_abs_le ζ.im]
  calc volume (xiShadow ∩ Icc a b)
      ≤ volume (⋃ ζ ∈ Z, Ioo (ζ.re - |ζ.im|) (ζ.re + |ζ.im|)) := measure_mono hsub
    _ ≤ ∑' ζ : Z, volume (Ioo ((ζ : ℂ).re - |(ζ : ℂ).im|) ((ζ : ℂ).re + |(ζ : ℂ).im|)) :=
        measure_biUnion_le volume hZc _
    _ = ∑' ζ : Z, ENNReal.ofReal (2 * |(ζ : ℂ).im|) := by
        congr 1
        funext ζ
        rw [Real.volume_Ioo]
        congr 1
        ring

end

end RHTower.DeBruijn
