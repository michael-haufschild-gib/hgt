/-
The reflection rigidity of the completed zeta, carried by its pole.

The entire completion `ξ = ½·s(s−1)·Λ` loses the pole of `Λ = completedRiemannZeta` at `s = 1`,
and with it the cheap proof that the functional equation is the *only* reflection symmetry: for
`ξ` that fact needs its transcendental growth (recorded as the hypothesis `hap` in
`SeamOfflineReflection`).  For the meromorphic `Λ` itself it is unconditional and elementary — the
pole set `{0, 1}` is finite, and a reflection permutes it.

* `completedRiemannZeta_continuousAt` / `_not_continuousAt_zero` / `_not_continuousAt_one` — `Λ` is
  continuous exactly off `{0, 1}`, with genuine poles at both (read off `Λ = Λ₀ − 1/s − 1/(1−s)`,
  `Λ₀` entire).
* `completedRiemannZeta_reflection_center_eq_half` — **the wall, unconditional.**  Any reflection
  `s ↦ b − s` fixing `Λ` has `b = 1`: it is the functional equation, whose fixed point `b/2 = 1/2`
  lies on the critical line.  The reflection sends the pole `0` to `b` and the pole `1` to `b − 1`;
  both must land back in `{0, 1}`, and only `b = 1` satisfies both.

The rigidity is thus a statement about the **pole** — the single arithmetic pole of `ζ` at `s = 1`,
dual to the divisor/zero side the parity program reads.  The functional equation is pinned as the
unique reflection by the arithmetic mass, not by the zeros; off the pole, on the entire model `ξ`,
the same uniqueness costs the full transcendence of the completed zeta.
-/
import GaloisForLFunctions.RHTower.SeamOfflineReflection

open Complex Filter Topology

namespace RHTower

/-! ### §1 The pole structure of the completed zeta -/

/-- Away from `{0, 1}` the completed zeta is continuous: `Λ = Λ₀ − 1/s − 1/(1−s)` with `Λ₀`
entire and both simple terms regular there. -/
theorem completedRiemannZeta_continuousAt {s : ℂ} (h0 : s ≠ 0) (h1 : s ≠ 1) :
    ContinuousAt completedRiemannZeta s := by
  have hrw : completedRiemannZeta
      = fun z => completedRiemannZeta₀ z - 1 / z - 1 / (1 - z) := by
    funext z; exact completedRiemannZeta_eq z
  rw [hrw]
  have h1s : (1 : ℂ) - s ≠ 0 := sub_ne_zero.mpr (Ne.symm h1)
  refine ContinuousAt.sub (ContinuousAt.sub ?_ ?_) ?_
  · exact differentiable_completedZeta₀.continuous.continuousAt
  · exact continuousAt_const.div continuousAt_id h0
  · exact continuousAt_const.div (continuousAt_const.sub continuousAt_id) h1s

/-- The reciprocal `1/(1−s)` has a genuine pole at `1`: it is not continuous there, since
`(1−s)·(1/(1−s)) = 1` off `1` yet the product of the two factors tends to `0`. -/
theorem inv_one_sub_not_continuousAt_one :
    ¬ ContinuousAt (fun s : ℂ => 1 / (1 - s)) 1 := by
  intro h
  have hval : (fun s : ℂ => 1 / (1 - s)) 1 = 0 := by norm_num
  have hlim : Tendsto (fun s : ℂ => 1 / (1 - s)) (𝓝 1) (𝓝 0) := hval ▸ h.tendsto
  have h1s : Tendsto (fun s : ℂ => 1 - s) (𝓝 1) (𝓝 0) := by
    have : Tendsto (fun s : ℂ => 1 - s) (𝓝 1) (𝓝 (1 - 1)) :=
      (continuous_const.sub continuous_id).tendsto 1
    simpa using this
  have hprod : Tendsto (fun s : ℂ => (1 - s) * (1 / (1 - s))) (𝓝 1) (𝓝 (0 * 0)) :=
    h1s.mul hlim
  rw [mul_zero] at hprod
  have hpunc : Tendsto (fun s : ℂ => (1 - s) * (1 / (1 - s))) (𝓝[≠] 1) (𝓝 1) := by
    refine Tendsto.congr' ?_ tendsto_const_nhds
    filter_upwards [self_mem_nhdsWithin] with s hs
    have hne : (1 : ℂ) - s ≠ 0 := sub_ne_zero.mpr (fun hh => hs hh.symm)
    field_simp
  exact one_ne_zero (tendsto_nhds_unique (hprod.mono_left nhdsWithin_le_nhds) hpunc).symm

/-- The reciprocal `1/s` has a genuine pole at `0`. -/
theorem inv_not_continuousAt_zero :
    ¬ ContinuousAt (fun s : ℂ => 1 / s) 0 := by
  intro h
  have hlim : Tendsto (fun s : ℂ => 1 / s) (𝓝 0) (𝓝 0) := by
    have h2 := h.tendsto; simp only [div_zero] at h2; exact h2
  have hid : Tendsto (fun s : ℂ => s) (𝓝 0) (𝓝 0) := by
    simpa using (continuous_id.tendsto (0 : ℂ))
  have hprod : Tendsto (fun s : ℂ => s * (1 / s)) (𝓝 0) (𝓝 (0 * 0)) := hid.mul hlim
  rw [mul_zero] at hprod
  have hpunc : Tendsto (fun s : ℂ => s * (1 / s)) (𝓝[≠] 0) (𝓝 1) := by
    refine Tendsto.congr' ?_ tendsto_const_nhds
    filter_upwards [self_mem_nhdsWithin] with s hs
    have hne : s ≠ 0 := hs
    field_simp
  exact one_ne_zero (tendsto_nhds_unique (hprod.mono_left nhdsWithin_le_nhds) hpunc).symm

/-- The completed zeta has a genuine pole at `1`: were it continuous there, `1/(1−s)` would be
too, since `Λ₀` and `1/s` are. -/
theorem completedRiemannZeta_not_continuousAt_one :
    ¬ ContinuousAt completedRiemannZeta 1 := by
  intro h
  apply inv_one_sub_not_continuousAt_one
  have heq : (fun s : ℂ => 1 / (1 - s))
      = fun s => completedRiemannZeta₀ s - 1 / s - completedRiemannZeta s := by
    funext s; rw [completedRiemannZeta_eq s]; ring
  rw [heq]
  exact (differentiable_completedZeta₀.continuous.continuousAt.sub
    (continuousAt_const.div continuousAt_id one_ne_zero)).sub h

/-- The completed zeta has a genuine pole at `0`: were it continuous there, `1/s` would be too. -/
theorem completedRiemannZeta_not_continuousAt_zero :
    ¬ ContinuousAt completedRiemannZeta 0 := by
  intro h
  apply inv_not_continuousAt_zero
  have h1s : (1 : ℂ) - (0 : ℂ) ≠ 0 := by norm_num
  have heq : (fun s : ℂ => 1 / s)
      = fun s => completedRiemannZeta₀ s - 1 / (1 - s) - completedRiemannZeta s := by
    funext s; rw [completedRiemannZeta_eq s]; ring
  rw [heq]
  exact (differentiable_completedZeta₀.continuous.continuousAt.sub
    (continuousAt_const.div (continuousAt_const.sub continuousAt_id) h1s)).sub h

/-! ### §2 The wall: the functional equation is the only reflection of `Λ` -/

/-- **The reflection rigidity of the completed zeta, unconditional.**  Any reflection
`s ↦ b − s` under which `Λ = completedRiemannZeta` is invariant has `b = 1`: it is the functional
equation `Λ(1 − s) = Λ(s)`, whose fixed point `b/2 = 1/2` lies on the critical line.

The reflection carries the pole at `0` to `b` and the pole at `1` to `b − 1`; `Λ` is continuous off
`{0, 1}`, so both images lie in `{0, 1}`, forcing `b = 1`.  No growth or transcendence input is
needed — the finiteness of the pole set does all the work. -/
theorem completedRiemannZeta_reflection_center_eq_half {b : ℂ}
    (hb : ∀ s, completedRiemannZeta (b - s) = completedRiemannZeta s) : b = 1 := by
  have hcomp : completedRiemannZeta ∘ (fun s => b - s) = completedRiemannZeta := by
    funext s; exact hb s
  have transfer : ∀ x : ℂ,
      ContinuousAt completedRiemannZeta (b - x) → ContinuousAt completedRiemannZeta x := by
    intro x hx
    have hR : ContinuousAt (fun s : ℂ => b - s) x := continuousAt_const.sub continuousAt_id
    have hcx : ContinuousAt (completedRiemannZeta ∘ (fun s => b - s)) x := hx.comp hR
    rwa [hcomp] at hcx
  have hb01 : b = 0 ∨ b = 1 := by
    by_contra hcon
    rw [not_or] at hcon
    have hcb : ContinuousAt completedRiemannZeta b :=
      completedRiemannZeta_continuousAt hcon.1 hcon.2
    have h0 : ContinuousAt completedRiemannZeta 0 := by
      have ht := transfer 0
      rw [sub_zero] at ht
      exact ht hcb
    exact completedRiemannZeta_not_continuousAt_zero h0
  have hb11 : b - 1 = 0 ∨ b - 1 = 1 := by
    by_contra hcon
    rw [not_or] at hcon
    have hcb : ContinuousAt completedRiemannZeta (b - 1) :=
      completedRiemannZeta_continuousAt hcon.1 hcon.2
    exact completedRiemannZeta_not_continuousAt_one (transfer 1 hcb)
  rcases hb01 with h | h
  · exfalso
    rcases hb11 with h' | h' <;> rw [h] at h' <;> norm_num at h'
  · exact h

/-- **Every reflection symmetry of the completed zeta is fixed on the critical line.**  The fixed
point of an invariant reflection `s ↦ b − s` is `b/2 = 1/2`: `Λ` has no reflection whose fixed
point leaves the critical line, a direct restatement of `b = 1`. -/
theorem completedRiemannZeta_reflection_fixed_point {b : ℂ}
    (hb : ∀ s, completedRiemannZeta (b - s) = completedRiemannZeta s) :
    b / 2 = (1 : ℂ) / 2 := by
  rw [completedRiemannZeta_reflection_center_eq_half hb]

/-! ### §3 The completed zeta is not periodic -/

/-- **The completed zeta has no nonzero period.**  For `ω ≠ 0`, `Λ` is not `ω`-periodic: the pole at
`1` would translate to poles at `1 + ω` and `1 + 2ω`, at least one of which lies outside the pole
set `{0, 1}`, where `Λ` is continuous.  This is the unconditional analogue, for the meromorphic
completion, of the aperiodicity hypothesis `hap` that the entire model `ξ` requires — here it is a
theorem, because `Λ` carries the pole that `ξ = ½·s(s−1)·Λ` cancels. -/
theorem completedRiemannZeta_not_periodic {ω : ℂ} (hω : ω ≠ 0) :
    ¬ (∀ s, completedRiemannZeta (s + ω) = completedRiemannZeta s) := by
  intro hper
  have hcomp : completedRiemannZeta ∘ (fun s => s + ω) = completedRiemannZeta := by
    funext s; exact hper s
  have transfer : ∀ x : ℂ,
      ContinuousAt completedRiemannZeta (x + ω) → ContinuousAt completedRiemannZeta x := by
    intro x hx
    have hT : ContinuousAt (fun s : ℂ => s + ω) x := continuousAt_id.add continuousAt_const
    have hcx : ContinuousAt (completedRiemannZeta ∘ (fun s : ℂ => s + ω)) x :=
      ContinuousAt.comp (f := fun s : ℂ => s + ω) hx hT
    rwa [hcomp] at hcx
  have p1 : ¬ ContinuousAt completedRiemannZeta (1 + ω) := fun hc =>
    completedRiemannZeta_not_continuousAt_one (transfer 1 hc)
  have p2 : ¬ ContinuousAt completedRiemannZeta (1 + 2 * ω) := by
    intro hc
    refine p1 (transfer (1 + ω) ?_)
    have hrw : (1 + ω) + ω = 1 + 2 * ω := by ring
    rwa [hrw]
  by_cases h1 : 1 + ω = 0 ∨ 1 + ω = 1
  · have hω1 : (1 : ℂ) + ω = 0 := by
      rcases h1 with h | h
      · exact h
      · exact absurd (by linear_combination h : ω = 0) hω
    have hv : (1 : ℂ) + 2 * ω = -1 := by linear_combination 2 * hω1
    exact p2 (by rw [hv]; exact completedRiemannZeta_continuousAt (by norm_num) (by norm_num))
  · rw [not_or] at h1
    exact p1 (completedRiemannZeta_continuousAt h1.1 h1.2)

end RHTower
