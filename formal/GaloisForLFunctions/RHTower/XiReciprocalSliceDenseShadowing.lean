import GaloisForLFunctions.RHTower.XiReciprocalSliceNearestZero
import GaloisForLFunctions.RHTower.RiemannTower

/-!
# Reciprocal positivity on a dense set of heights shadows every zero

Reciprocal slice positivity at a height `t` puts the nearest zero of `ξ` to `½ + it` on the
critical line (`exists_critical_zero_within_of_reciprocal_nonneg`).

**Theorem** (`exists_critical_shadow_of_dense`).  If reciprocal slice positivity holds on a dense
set of heights, then every zero `ρ` of `ξ` is *shadowed*: some critical zero `½ + iγ` satisfies
`|γ − Im ρ| ≤ |Re ρ − ½|`.  In particular this holds when positivity fails only on a null set
(`exists_critical_shadow_of_ae`).

So almost-every-height reciprocal positivity excludes *exposed* off-line zeros: zeros whose
distance to the critical line is smaller than the vertical distance to every critical zero.  The
known zero statistics (positive proportions of simple critical zeros, zero-density estimates near
the line) do not exclude a positive proportion of such zeros within `O(1/log t)` of the line.
Almost-every-height reciprocal positivity is therefore at least as strong as excluding all exposed
near-line off-line zeros.  This is why the unconditional results stop at positive density.

The proof argues by contradiction.  If `ρ` is not shadowed, the finitely many critical ordinates
near `Im ρ` keep a margin `ε` beyond `|Re ρ − ½|`.  A positive height `t` within `ε/2` of `Im ρ`
then has a critical zero within `|Re ρ − ½| + |t − Im ρ|` of `t`, which violates the margin.
-/

open Complex Metric MeasureTheory

namespace RHTower

noncomputable section

/-- **Dense positivity shadows every zero.** -/
theorem exists_critical_shadow_of_dense {D : Set ℝ} (hD : Dense D)
    (hpos : ∀ t ∈ D, XiReciprocalSlicePositive t) {ρ : ℂ} (hρ : xi ρ = 0) :
    ∃ γ : ℝ, xi (1 / 2 + (γ : ℂ) * I) = 0 ∧ |γ - ρ.im| ≤ |ρ.re - 1 / 2| := by
  by_contra hno
  push Not at hno
  set δ := |ρ.re - 1 / 2| with hδ
  -- the critical ordinates near `Im ρ` form a finite set
  set W : Set ℝ := {γ | xi (1 / 2 + (γ : ℂ) * I) = 0 ∧ |γ - ρ.im| ≤ δ + 2} with hW
  have hWfin : W.Finite := by
    have hfin := xi_zeros_finite_ball (1 / 2 + (ρ.im : ℂ) * I) (δ + 3)
    refine (hfin.preimage (f := fun γ : ℝ => 1 / 2 + (γ : ℂ) * I) ?_).subset ?_
    · intro a _ b _ hab
      have := congrArg Complex.im hab
      simpa using this
    · intro γ hγ
      refine ⟨?_, hγ.1⟩
      rw [mem_ball, dist_eq_norm,
        show 1 / 2 + (γ : ℂ) * I - (1 / 2 + (ρ.im : ℂ) * I) = ((γ - ρ.im : ℝ) : ℂ) * I by
          push_cast; ring, norm_mul, Complex.norm_I, mul_one, Complex.norm_real,
        Real.norm_eq_abs]
      linarith [hγ.2]
  -- a uniform margin `ε` beyond `δ`
  obtain ⟨ε, hε0, hε1, hεW⟩ : ∃ ε : ℝ, 0 < ε ∧ ε ≤ 1 ∧ ∀ γ ∈ W, δ + ε ≤ |γ - ρ.im| := by
    rcases W.eq_empty_or_nonempty with hWe | hWne
    · exact ⟨1, one_pos, le_rfl, fun γ hγ => by rw [hWe] at hγ; exact absurd hγ id⟩
    · obtain ⟨γ₀, hγ₀, hmin⟩ := Set.exists_min_image W (fun γ => |γ - ρ.im|) hWfin hWne
      have hgap : δ < |γ₀ - ρ.im| := hno γ₀ hγ₀.1
      refine ⟨min 1 (|γ₀ - ρ.im| - δ), lt_min one_pos (by linarith), min_le_left _ _,
        fun γ hγ => ?_⟩
      have := hmin γ hγ
      have := min_le_right 1 (|γ₀ - ρ.im| - δ)
      linarith
  -- a positivity height close to `Im ρ`
  obtain ⟨t, htb, htD⟩ := Metric.dense_iff.mp hD ρ.im (ε / 2) (by positivity)
  rw [mem_ball, Real.dist_eq] at htb
  obtain ⟨γ, hγ, hle⟩ := exists_critical_zero_within_of_reciprocal_nonneg (hpos t htD) hρ
  have hnorm : ‖ρ - (1 / 2 + (t : ℂ) * I)‖ ≤ δ + |t - ρ.im| := by
    refine (Complex.norm_le_abs_re_add_abs_im _).trans (le_of_eq ?_)
    simp only [Complex.sub_re, Complex.add_re, Complex.mul_re, Complex.I_re, Complex.I_im,
      Complex.ofReal_re, Complex.ofReal_im, Complex.sub_im, Complex.add_im, Complex.mul_im]
    norm_num
    rw [hδ, abs_sub_comm ρ.im t]
  have hclose : |γ - ρ.im| < δ + ε := by
    have h1 : |γ - ρ.im| ≤ |γ - t| + |t - ρ.im| := abs_sub_le γ t ρ.im
    linarith
  have hγW : γ ∈ W := ⟨hγ, by linarith⟩
  have := hεW γ hγW
  linarith

/-- **Almost-everywhere positivity shadows every zero.** -/
theorem exists_critical_shadow_of_ae
    (hae : volume {t : ℝ | ¬ XiReciprocalSlicePositive t} = 0) {ρ : ℂ} (hρ : xi ρ = 0) :
    ∃ γ : ℝ, xi (1 / 2 + (γ : ℂ) * I) = 0 ∧ |γ - ρ.im| ≤ |ρ.re - 1 / 2| := by
  refine exists_critical_shadow_of_dense (D := {t : ℝ | XiReciprocalSlicePositive t}) ?_
    (fun t ht => ht) hρ
  rw [Metric.dense_iff]
  intro x r hr
  by_contra hempty
  rw [Set.not_nonempty_iff_eq_empty] at hempty
  have hsub : ball x r ⊆ {t : ℝ | ¬ XiReciprocalSlicePositive t} := by
    intro t ht hpos
    have : t ∈ ball x r ∩ {t : ℝ | XiReciprocalSlicePositive t} := ⟨ht, hpos⟩
    rw [hempty] at this
    exact this
  have h0 := measure_mono_null hsub hae
  rw [Real.volume_ball] at h0
  have : (0 : ℝ) < 2 * r := by positivity
  simp only [ENNReal.ofReal_eq_zero] at h0
  linarith

end

end RHTower
