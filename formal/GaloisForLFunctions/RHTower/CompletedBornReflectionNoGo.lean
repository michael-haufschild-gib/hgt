import GaloisForLFunctions.RHTower.XiRealAnchorPositive

/-!
# The completed zeta admits no Born reflection

Two reflections of the temperature line at distance `1/2` — the scalar functional-equation
reflection `s ↦ 1 - s` of the completed zeta and the Born reflection `s ↦ 2 - s` induced on
the trace argument by the state reflection `σ ↦ 1 - σ` at `β = 2σ` — generate the unit
translation.  A function invariant under both is `1`-periodic; the completed zeta has a pole
at `0` and is finite at `2`, so it carries exactly one of the two reflections: the scalar
functional equation, never the Born reflection.

The unique dilation gauge in which the completed zeta does carry the Born reflection is the
half-dilated `β ↦ Λ(β/2)`, symmetric about `β = 1` — the gauge whose discrete Hamiltonian is
`log √n`.  At the self-dual point this partition value is a strictly negative real,
`Λ(1/2) = -8·ξ(1/2)` with `ξ(1/2)` positive real, so no ungraded Gibbs trace realizes it:
any dynamical realization must carry a grading.
-/

noncomputable section

namespace RHTower

open Filter Complex

/-- Two mirror symmetries of the line at distance `1/2` compose to the unit shift: a function
invariant under both `s ↦ 1 - s` and `s ↦ 2 - s` is `1`-periodic. -/
theorem doubly_reflected_periodic {α : Type*} {f : ℂ → α}
    (h1 : ∀ s, f (1 - s) = f s) (h2 : ∀ s, f (2 - s) = f s) (s : ℂ) :
    f (s + 1) = f s := by
  have ha := h2 (s + 1)
  rw [show (2 : ℂ) - (s + 1) = 1 - s by ring] at ha
  rw [← ha]
  exact h1 s

/-- The completed zeta has a simple pole at `0` with residue `-1`:
`s · Λ(s) → -1` as `s → 0` off the pole. -/
theorem tendsto_mul_completedRiemannZeta_zero :
    Tendsto (fun s : ℂ => s * completedRiemannZeta s)
      (nhdsWithin 0 {(0 : ℂ)}ᶜ) (nhds (-1)) := by
  have hcont : ContinuousAt
      (fun s : ℂ => s * completedRiemannZeta₀ s - 1 - s / (1 - s)) 0 := by
    have h₀ : ContinuousAt (fun s : ℂ => s * completedRiemannZeta₀ s) 0 :=
      continuousAt_id.mul differentiable_completedZeta₀.continuous.continuousAt
    have h₁ : ContinuousAt (fun s : ℂ => s / (1 - s)) 0 :=
      ContinuousAt.div continuousAt_id
        ((continuous_const.sub continuous_id).continuousAt) (by norm_num)
    exact (h₀.sub continuousAt_const).sub h₁
  have hval : (fun s : ℂ => s * completedRiemannZeta₀ s - 1 - s / (1 - s)) 0 = -1 := by
    norm_num
  have hbase : Tendsto (fun s : ℂ => s * completedRiemannZeta₀ s - 1 - s / (1 - s))
      (nhdsWithin 0 {(0 : ℂ)}ᶜ) (nhds (-1)) := by
    rw [← hval]
    exact hcont.tendsto.mono_left nhdsWithin_le_nhds
  refine hbase.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with s hs
  have hs0 : (s : ℂ) ≠ 0 := hs
  rw [completedRiemannZeta_eq, mul_sub, mul_sub, mul_one_div, mul_one_div, div_self hs0]

/-- The reflected completed zeta is continuous at the pole: `Λ(2-s) → Λ(2)` as `s → 0`. -/
theorem tendsto_completedRiemannZeta_two_sub :
    Tendsto (fun s : ℂ => completedRiemannZeta (2 - s)) (nhds 0)
      (nhds (completedRiemannZeta 2)) := by
  have hfun : (fun s : ℂ => completedRiemannZeta (2 - s))
      = fun s : ℂ => completedRiemannZeta₀ (2 - s) - 1 / (2 - s) - 1 / (1 - (2 - s)) := by
    funext s
    rw [completedRiemannZeta_eq]
  have hcont : ContinuousAt
      (fun s : ℂ => completedRiemannZeta₀ (2 - s) - 1 / (2 - s) - 1 / (1 - (2 - s))) 0 := by
    have hsub : Continuous fun s : ℂ => (2 : ℂ) - s := continuous_const.sub continuous_id
    have h₀ : ContinuousAt (fun s : ℂ => completedRiemannZeta₀ (2 - s)) 0 :=
      (differentiable_completedZeta₀.continuous.comp hsub).continuousAt
    have h₁ : ContinuousAt (fun s : ℂ => 1 / (2 - s)) 0 :=
      ContinuousAt.div continuousAt_const hsub.continuousAt (by norm_num)
    have h₂ : ContinuousAt (fun s : ℂ => 1 / (1 - (2 - s))) 0 :=
      ContinuousAt.div continuousAt_const
        ((continuous_const.sub hsub).continuousAt) (by norm_num)
    exact (h₀.sub h₁).sub h₂
  rw [hfun, completedRiemannZeta_eq]
  have hval : completedRiemannZeta₀ (2 - (0 : ℂ)) - 1 / (2 - (0 : ℂ))
      - 1 / (1 - (2 - (0 : ℂ)))
      = completedRiemannZeta₀ 2 - 1 / 2 - 1 / (1 - 2) := by
    norm_num
  rw [← hval]
  exact hcont.tendsto

/-- **The completed zeta admits no Born reflection.**  There is no identity
`Λ(2-s) = Λ(s)` off the exceptional points `{0, 1, 2}`: the left end `0` of the reflected
pair is a pole while the right end `2` is regular. -/
theorem completedRiemannZeta_no_born_reflection :
    ¬ ∀ s : ℂ, s ≠ 0 → s ≠ 1 → s ≠ 2 →
      completedRiemannZeta (2 - s) = completedRiemannZeta s := by
  intro h
  have hev : ∀ᶠ s : ℂ in nhdsWithin 0 {(0 : ℂ)}ᶜ,
      s * completedRiemannZeta (2 - s) = s * completedRiemannZeta s := by
    have h1 : ∀ᶠ s : ℂ in nhds (0 : ℂ), s ≠ 1 := eventually_ne_nhds (by norm_num)
    have h2 : ∀ᶠ s : ℂ in nhds (0 : ℂ), s ≠ 2 := eventually_ne_nhds (by norm_num)
    filter_upwards [self_mem_nhdsWithin,
      (h1.and h2).filter_mono nhdsWithin_le_nhds] with s hs0 hs12
    rw [h s hs0 hs12.1 hs12.2]
  have hzero : Tendsto (fun s : ℂ => s * completedRiemannZeta (2 - s))
      (nhdsWithin 0 {(0 : ℂ)}ᶜ) (nhds 0) := by
    have := (continuousAt_id (x := (0 : ℂ))).tendsto.mul tendsto_completedRiemannZeta_two_sub
    simpa using this.mono_left nhdsWithin_le_nhds
  have hneg : Tendsto (fun s : ℂ => s * completedRiemannZeta (2 - s))
      (nhdsWithin 0 {(0 : ℂ)}ᶜ) (nhds (-1)) :=
    tendsto_mul_completedRiemannZeta_zero.congr' (by filter_upwards [hev] with s hs; exact hs.symm)
  have : (0 : ℂ) = -1 := tendsto_nhds_unique hzero hneg
  norm_num at this

/-- **The half-dilated completed zeta carries the Born reflection.**  `Z(β) = Λ(β/2)`
satisfies `Z(2-β) = Z(β)`: in this dilation gauge the functional equation is exactly the
temperature reflection about `β = 1`. -/
theorem completedRiemannZeta_half_dilated_born_reflection (β : ℂ) :
    completedRiemannZeta ((2 - β) / 2) = completedRiemannZeta (β / 2) := by
  rw [show (2 - β) / 2 = 1 - β / 2 by ring, completedRiemannZeta_one_sub]

/-- The completed zeta at the self-dual point is `-8` times the completed `ξ` there. -/
theorem completedRiemannZeta_half_eq :
    completedRiemannZeta (1 / 2 : ℂ) = -8 * xi (1 / 2 : ℂ) := by
  have hxi := xi_eq_half_mul (s := (1 / 2 : ℂ)) (by norm_num) (by norm_num)
  linear_combination (8 : ℂ) * hxi

/-- **The self-dual partition value is a strictly negative real**: `Λ(1/2) = -8·ξ(1/2)`
with `ξ(1/2)` positive real.  No ungraded Gibbs trace attains it; a dynamical realization of
the half-dilated completed partition function must carry a grading. -/
theorem completedRiemannZeta_half_neg :
    (completedRiemannZeta (1 / 2 : ℂ)).re < 0 ∧ (completedRiemannZeta (1 / 2 : ℂ)).im = 0 := by
  have hcast : ((1 / 2 : ℝ) : ℂ) = (1 / 2 : ℂ) := by norm_num
  have hpos : 0 < (xi (1 / 2 : ℂ)).re := by
    rw [← hcast]
    exact xi_pos_on_real_anchor (by norm_num) (by norm_num)
  have him : (xi (1 / 2 : ℂ)).im = 0 := by
    rw [← hcast]
    exact xi_real_on_real_anchor (by norm_num) (by norm_num)
  constructor
  · rw [completedRiemannZeta_half_eq]
    have hre : ((-8 : ℂ) * xi (1 / 2 : ℂ)).re = -8 * (xi (1 / 2 : ℂ)).re := by
      simp [Complex.mul_re]
    rw [hre]
    linarith
  · rw [completedRiemannZeta_half_eq]
    have him' : ((-8 : ℂ) * xi (1 / 2 : ℂ)).im = -8 * (xi (1 / 2 : ℂ)).im := by
      simp [Complex.mul_im]
    rw [him', him, mul_zero]

end RHTower
