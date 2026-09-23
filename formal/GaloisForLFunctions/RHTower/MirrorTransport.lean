/-
The mirror-annulus transport: the vertical-line reflection carries the whole
root-trace theory of a line-symmetric member from an off-line annulus to its
mirror annulus, holonomy INTACT.

The reflection maps the circle at `ρ` to the circle at the mirror center with
the parameter reversed; the Schwarz-mirrored trace `θ ↦ conj (U (π − θ))` is a
continuous root trace at the mirror circle with the SAME `±1` holonomy — an
antiholomorphic map reverses both the traversal and the sheet phase, and the
two reversals cancel on the holonomy.  Consequently an isolated odd-order zero
whose annulus the carrier dominates on one circle empties the carrier's
periodic mass at the mirror circle as well: zero-mass events come in mirror
pairs.

At a line-centered annulus the reflection acts on the enclosed configuration
itself, and the involution pairing makes mirror-paired off-line zeros drop out
of every trace holonomy: the holonomy — hence the port sign observable, hence
the periodic mass — reads exactly the ON-line enclosed count mod 2.
-/
import GaloisForLFunctions.RHTower.CarrierPeriodicMass

noncomputable section

namespace RHTower

open Complex Metric Set

/-! ### §1 Mirror geometry -/

/-- The reflection is an isometry. -/
theorem norm_lineReflection_sub (μ : ℝ) (z w : ℂ) :
    ‖lineReflection μ z - lineReflection μ w‖ = ‖z - w‖ := by
  rw [lineReflection, lineReflection,
    show ((2 * μ : ℝ) : ℂ) - (starRingEnd ℂ) z
        - (((2 * μ : ℝ) : ℂ) - (starRingEnd ℂ) w)
      = (starRingEnd ℂ) (w - z) by rw [map_sub]; ring,
    norm_conj, norm_sub_rev]

/-- The reflection maps an annulus to the mirror annulus. -/
theorem lineReflection_mem_mirror_annulus {μ : ℝ} {ρ : ℂ} {r₀ R : ℝ} {z : ℂ}
    (hz : z ∈ ball ρ R \ closedBall ρ r₀) :
    lineReflection μ z ∈ ball (lineReflection μ ρ) R
      \ closedBall (lineReflection μ ρ) r₀ := by
  constructor
  · rw [mem_ball, dist_eq_norm, norm_lineReflection_sub]
    have h1 := hz.1
    rwa [mem_ball, dist_eq_norm] at h1
  · intro hmem
    apply hz.2
    rw [mem_closedBall, dist_eq_norm, norm_lineReflection_sub] at hmem
    rwa [mem_closedBall, dist_eq_norm]

/-- The reflection conjugates the circle parametrization: the circle at `ρ` maps
to the circle at the mirror center with the parameter reversed through `π`. -/
theorem lineReflection_circleMap (μ : ℝ) (ρ : ℂ) (r θ : ℝ) :
    lineReflection μ (circleMap ρ r θ)
      = circleMap (lineReflection μ ρ) r (Real.pi - θ) := by
  rw [lineReflection, lineReflection, circleMap, circleMap, map_add,
    show ((Real.pi - θ : ℝ) : ℂ) * I
      = (Real.pi : ℂ) * I + ((-θ : ℝ) : ℂ) * I by push_cast; ring,
    Complex.exp_add, Complex.exp_pi_mul_I, map_mul, Complex.conj_ofReal,
    ← Complex.exp_conj,
    show (starRingEnd ℂ) ((θ : ℝ) * I) = ((-θ : ℝ) : ℂ) * I by
      rw [map_mul, Complex.conj_ofReal, Complex.conj_I]; push_cast; ring]
  ring

/-! ### §2 The mirrored trace and holonomy transport -/

/-- The Schwarz-mirrored trace: conjugate values, parameter reversed through
`π`. -/
noncomputable def mirrorTrace (U : ℝ → ℂ) : ℝ → ℂ := fun θ =>
  (starRingEnd ℂ) (U (Real.pi - θ))

theorem mirrorTrace_continuousOn {U : ℝ → ℂ}
    (hUc : ContinuousOn U (Icc (-(Real.pi / 2)) (3 * Real.pi / 2))) :
    ContinuousOn (mirrorTrace U) (Icc (-(Real.pi / 2)) (3 * Real.pi / 2)) := by
  apply Complex.continuous_conj.comp_continuousOn
  refine hUc.comp (continuous_const.sub continuous_id).continuousOn ?_
  intro θ hθ
  constructor
  · have := hθ.2
    linarith
  · have := hθ.1
    linarith

/-- The mirrored trace is a root trace of the line-symmetric member at the
mirror circle. -/
theorem mirrorTrace_sq {μ : ℝ} {f : ℂ → ℂ} {ρ : ℂ} {r₀ r R : ℝ}
    (h0 : 0 ≤ r₀) (hr₀ : r₀ < r) (hrR : r < R)
    (hsym : ∀ z ∈ ball ρ R \ closedBall ρ r₀,
      f (lineReflection μ z) = (starRingEnd ℂ) (f z))
    {U : ℝ → ℂ}
    (hUsq : ∀ θ ∈ Icc (-(Real.pi / 2)) (3 * Real.pi / 2),
      U θ ^ (2 : ℕ) = f (circleMap ρ r θ)) :
    ∀ θ ∈ Icc (-(Real.pi / 2)) (3 * Real.pi / 2),
      mirrorTrace U θ ^ (2 : ℕ)
        = f (circleMap (lineReflection μ ρ) r θ) := by
  intro θ hθ
  have hθ' : Real.pi - θ ∈ Icc (-(Real.pi / 2)) (3 * Real.pi / 2) := by
    constructor
    · have := hθ.2
      linarith
    · have := hθ.1
      linarith
  show ((starRingEnd ℂ) (U (Real.pi - θ))) ^ (2 : ℕ) = _
  rw [← map_pow, hUsq _ hθ',
    ← hsym _ (circleMap_mem_annulus h0 hr₀ hrR (Real.pi - θ)),
    lineReflection_circleMap,
    show Real.pi - (Real.pi - θ) = θ by ring]

/-- **Holonomy transport**: the mirrored trace carries the SAME `±1` holonomy —
the antiholomorphic reflection reverses both the traversal and the sheet
phase, and the two reversals cancel. -/
theorem mirrorTrace_holonomy {U : ℝ → ℂ} {σ : ℂ} (hσpm : σ = 1 ∨ σ = -1)
    (hhol : U (3 * Real.pi / 2) = σ * U (-(Real.pi / 2))) :
    mirrorTrace U (3 * Real.pi / 2) = σ * mirrorTrace U (-(Real.pi / 2)) := by
  show (starRingEnd ℂ) (U (Real.pi - 3 * Real.pi / 2))
    = σ * (starRingEnd ℂ) (U (Real.pi - -(Real.pi / 2)))
  rw [show Real.pi - 3 * Real.pi / 2 = -(Real.pi / 2) by ring,
    show Real.pi - -(Real.pi / 2) = 3 * Real.pi / 2 by ring, hhol, map_mul]
  rcases hσpm with h | h <;> subst h <;> simp

/-! ### §3 Zero-mass events come in mirror pairs -/

/-- **The mirror seam capstone**: an isolated odd-order zero of `g`, with a
line-symmetric carrier nonvanishing on the annulus and dominating on one
interior circle, flips every carrier trace at the MIRROR circle as well, and
the carrier's periodic mass vanishes there — zero-mass circles come in mirror
pairs. -/
theorem carrier_mass_zero_mirror_of_odd_isolated_zero {μ : ℝ} {g F : ℂ → ℂ}
    {ρ : ℂ} {r₀ r R : ℝ} (h0 : 0 < r₀) (hr₀ : r₀ < r) (hrR : r < R)
    (hg : AnalyticOnNhd ℂ g (ball ρ R))
    (hiso : ∀ z ∈ ball ρ R, z ≠ ρ → g z ≠ 0)
    {m : ℕ} (hm : analyticOrderAt g ρ = m) (hodd : Odd m)
    (hFan : AnalyticOnNhd ℂ F (ball ρ R \ closedBall ρ r₀))
    (hF0 : ∀ z ∈ ball ρ R \ closedBall ρ r₀, F z ≠ 0)
    (hFsym : ∀ z ∈ ball ρ R \ closedBall ρ r₀,
      F (lineReflection μ z) = (starRingEnd ℂ) (F z))
    (hdom : ∀ θ ∈ Icc (-(Real.pi / 2)) (3 * Real.pi / 2),
      ‖g (circleMap ρ r θ) - F (circleMap ρ r θ)‖
        < ‖F (circleMap ρ r θ)‖) :
    ∃ W : ℝ → ℂ,
      ContinuousOn W (Icc (-(Real.pi / 2)) (3 * Real.pi / 2)) ∧
      (∀ θ ∈ Icc (-(Real.pi / 2)) (3 * Real.pi / 2),
        W θ ^ (2 : ℕ) = F (circleMap (lineReflection μ ρ) r θ)) ∧
      W (3 * Real.pi / 2) = -W (-(Real.pi / 2)) ∧
      ∀ p : ℝ → ℂ,
        ContinuousOn p
          (Icc (-(Real.pi / 2)) (3 * Real.pi / 2 + 2 * Real.pi)) →
        (∀ θ ∈ Icc (-(Real.pi / 2)) (3 * Real.pi / 2),
          p (θ + 2 * Real.pi) = p θ) →
        ∫ θ in (-(Real.pi / 2))..(3 * Real.pi / 2 + 2 * Real.pi),
          doubledTrace (-1) (W) θ * p θ = 0 := by
  obtain ⟨V, hVc, hVsq⟩ := exists_circle_trace h0 hr₀ hrR hFan hF0
  obtain ⟨hVflip, -⟩ := carrier_mass_zero_of_odd_isolated_zero h0 hr₀ hrR hg
    hiso hm hodd hFan hF0 hdom hVc hVsq
  refine ⟨mirrorTrace V, mirrorTrace_continuousOn hVc,
    mirrorTrace_sq (le_of_lt h0) hr₀ hrR hFsym hVsq, ?_, ?_⟩
  · have := mirrorTrace_holonomy (σ := -1) (Or.inr rfl)
      (by rw [neg_one_mul]; exact hVflip)
    rwa [neg_one_mul] at this
  · intro p hp hper
    have hflip : mirrorTrace V (3 * Real.pi / 2)
        = -mirrorTrace V (-(Real.pi / 2)) := by
      have := mirrorTrace_holonomy (σ := -1) (Or.inr rfl)
        (by rw [neg_one_mul]; exact hVflip)
      rwa [neg_one_mul] at this
    exact doubledTrace_pairing_eq_zero (mirrorTrace_continuousOn hVc) hflip
      hp hper

/-- **The mirror seam at the completed zeta**: an isolated odd-order ξ-zero
whose annulus the finite carrier dominates on one circle empties the carrier's
periodic mass at the mirror circle across the critical line as well. -/
theorem carrier_mass_zero_mirror_of_odd_xi_zero {N : ℕ} (hN : 1 ≤ N) {ρ : ℂ}
    {r₀ r R : ℝ} (h0 : 0 < r₀) (hr₀ : r₀ < r) (hrR : r < R)
    (hstrip : ∀ z ∈ ball ρ R \ closedBall ρ r₀, 0 < z.re ∧ z.re < 1)
    (hiso : ∀ z ∈ ball ρ R, z ≠ ρ → xi z ≠ 0)
    {m : ℕ} (hm : analyticOrderAt xi ρ = m) (hodd : Odd m)
    (hF0 : ∀ z ∈ ball ρ R \ closedBall ρ r₀, completedSEM N z ≠ 0)
    (hdom : ∀ θ ∈ Icc (-(Real.pi / 2)) (3 * Real.pi / 2),
      ‖xi (circleMap ρ r θ) - completedSEM N (circleMap ρ r θ)‖
        < ‖completedSEM N (circleMap ρ r θ)‖) :
    ∃ W : ℝ → ℂ,
      ContinuousOn W (Icc (-(Real.pi / 2)) (3 * Real.pi / 2)) ∧
      (∀ θ ∈ Icc (-(Real.pi / 2)) (3 * Real.pi / 2),
        W θ ^ (2 : ℕ) = completedSEM N
          (circleMap (lineReflection (1 / 2) ρ) r θ)) ∧
      W (3 * Real.pi / 2) = -W (-(Real.pi / 2)) ∧
      ∀ p : ℝ → ℂ,
        ContinuousOn p
          (Icc (-(Real.pi / 2)) (3 * Real.pi / 2 + 2 * Real.pi)) →
        (∀ θ ∈ Icc (-(Real.pi / 2)) (3 * Real.pi / 2),
          p (θ + 2 * Real.pi) = p θ) →
        ∫ θ in (-(Real.pi / 2))..(3 * Real.pi / 2 + 2 * Real.pi),
          doubledTrace (-1) (W) θ * p θ = 0 := by
  have hFsym : ∀ z ∈ ball ρ R \ closedBall ρ r₀,
      completedSEM N (lineReflection (1 / 2) z)
        = (starRingEnd ℂ) (completedSEM N z) := by
    intro z hz
    obtain ⟨h1, h2⟩ := hstrip z hz
    rw [lineReflection_half]
    exact completedSEM_lineReflection h1 h2
  exact carrier_mass_zero_mirror_of_odd_isolated_zero h0 hr₀ hrR
    (xi_analyticOnNhd _) hiso hm hodd
    (fun z hz => completedSEM_analyticOnNhd_strip hN z (hstrip z hz))
    hF0 hFsym hdom

/-! ### §4 Mirror pairs drop out: the on-line count identity -/

/-- **Equivariant parity**: for a configuration carried by a multiplicity-
preserving reflection involution, the total-order parity is the parity of the
on-line part — the free orbits pair off. -/
theorem neg_one_pow_sum_reflection_equivariant {ι : Type*} {μ : ℝ}
    (s : Finset ι) (ρc : ι → ℂ) (m : ι → ℕ) (σf : ι → ι)
    (hσmem : ∀ i ∈ s, σf i ∈ s)
    (hσρ : ∀ i ∈ s, ρc (σf i) = lineReflection μ (ρc i))
    (hσm : ∀ i ∈ s, m (σf i) = m i)
    (hσinv : ∀ i ∈ s, σf (σf i) = i) :
    ((-1 : ℂ)) ^ (∑ i ∈ s, m i)
      = (-1) ^ (∑ i ∈ s.filter (fun i => (ρc i).re = μ), m i) := by
  classical
  rw [← Finset.sum_filter_add_sum_filter_not s (fun i => (ρc i).re = μ) m]
  have heven : Even (∑ i ∈ s.filter (fun i => ¬(ρc i).re = μ), m i) := by
    rw [even_iff_two_dvd,
      ← ZMod.natCast_eq_zero_iff (∑ i ∈ s.filter (fun i => ¬(ρc i).re = μ), m i) 2]
    push_cast
    refine Finset.sum_involution (fun i _ => σf i) ?_ ?_ ?_ ?_
    · intro i hi
      obtain ⟨his, -⟩ := Finset.mem_filter.mp hi
      show (m i : ZMod 2) + (m (σf i) : ZMod 2) = 0
      rw [hσm i his]
      exact CharTwo.add_self_eq_zero _
    · intro i hi _
      obtain ⟨his, hnot⟩ := Finset.mem_filter.mp hi
      intro heq
      have heq' : σf i = i := heq
      apply hnot
      have hρeq : ρc i = lineReflection μ (ρc i) := by
        rw [← hσρ i his, heq']
      have hre := congrArg Complex.re hρeq
      rw [lineReflection_re] at hre
      linarith
    · intro i hi
      obtain ⟨his, hnot⟩ := Finset.mem_filter.mp hi
      show σf i ∈ s.filter (fun i => ¬(ρc i).re = μ)
      rw [Finset.mem_filter]
      refine ⟨hσmem i his, ?_⟩
      rw [hσρ i his, lineReflection_re]
      intro heq
      apply hnot
      linarith
    · intro i hi
      show σf (σf i) = i
      exact hσinv i (Finset.mem_filter.mp hi).1
  rw [pow_add, heven.neg_one_pow, mul_one]

/-- **The on-line count identity**: at a line-centered annulus enclosing a
reflection-equivariant configuration, every continuous root trace's holonomy
reads exactly the ON-line enclosed count mod 2 — mirror-paired off-line zeros
drop out of the invariant, the port sign observable, and the periodic mass. -/
theorem trace_holonomy_online_count {ι : Type*} (s : Finset ι)
    (ρc : ι → ℂ) (m : ι → ℕ) (σf : ι → ι) {μ : ℝ}
    {f h G₁ G₂ : ℂ → ℂ} {a : ℂ} {r₀ r R : ℝ}
    (h0 : 0 ≤ r₀) (hr₀ : r₀ < r) (hrR : r < R)
    (hσmem : ∀ i ∈ s, σf i ∈ s)
    (hσρ : ∀ i ∈ s, ρc (σf i) = lineReflection μ (ρc i))
    (hσm : ∀ i ∈ s, m (σf i) = m i)
    (hσinv : ∀ i ∈ s, σf (σf i) = i)
    (hρ : ∀ i ∈ s, ‖ρc i - a‖ ≤ r₀)
    (hh : AnalyticOnNhd ℂ h (ball a R)) (hh0 : ∀ z ∈ ball a R, h z ≠ 0)
    (hfact : ∀ z ∈ ball a R, f z = (∏ i ∈ s, (z - ρc i) ^ m i) * h z)
    (hG₁ : AnalyticOnNhd ℂ G₁ (chartRA a r₀ R))
    (hG₂ : AnalyticOnNhd ℂ G₂ (chartLA a r₀ R))
    (hpG₁ : ∀ z ∈ chartRA a r₀ R, G₁ z ^ (2 : ℕ) = f z)
    (hpG₂ : ∀ z ∈ chartLA a r₀ R, G₂ z ^ (2 : ℕ) = f z)
    {U : ℝ → ℂ}
    (hUc : ContinuousOn U (Icc (-(Real.pi / 2)) (3 * Real.pi / 2)))
    (hUsq : ∀ θ ∈ Icc (-(Real.pi / 2)) (3 * Real.pi / 2),
      U θ ^ (2 : ℕ) = f (circleMap a r θ)) :
    U (3 * Real.pi / 2)
      = (-1) ^ (∑ i ∈ s.filter (fun i => (ρc i).re = μ), m i)
        * U (-(Real.pi / 2)) := by
  rw [continuous_trace_holonomy_neg_one_pow s ρc m h0 hr₀ hrR hρ hh hh0 hfact
    hG₁ hG₂ hpG₁ hpG₂ hUc hUsq]
  congr 1
  exact neg_one_pow_sum_reflection_equivariant s ρc m σf hσmem hσρ hσm hσinv

/-- **Blindness, stated positively**: a purely off-line, mirror-paired enclosed
configuration closes every trace up — the periodic mass at the line-centered
circle is the full modulus mass, whatever the off-line pairs do. -/
theorem trace_closes_of_offline_mirror_pairs {ι : Type*} (s : Finset ι)
    (ρc : ι → ℂ) (m : ι → ℕ) (σf : ι → ι) {μ : ℝ}
    {f h G₁ G₂ : ℂ → ℂ} {a : ℂ} {r₀ r R : ℝ}
    (h0 : 0 ≤ r₀) (hr₀ : r₀ < r) (hrR : r < R)
    (hσmem : ∀ i ∈ s, σf i ∈ s)
    (hσρ : ∀ i ∈ s, ρc (σf i) = lineReflection μ (ρc i))
    (hσm : ∀ i ∈ s, m (σf i) = m i)
    (hσinv : ∀ i ∈ s, σf (σf i) = i)
    (hoffline : ∀ i ∈ s, (ρc i).re ≠ μ)
    (hρ : ∀ i ∈ s, ‖ρc i - a‖ ≤ r₀)
    (hh : AnalyticOnNhd ℂ h (ball a R)) (hh0 : ∀ z ∈ ball a R, h z ≠ 0)
    (hfact : ∀ z ∈ ball a R, f z = (∏ i ∈ s, (z - ρc i) ^ m i) * h z)
    (hG₁ : AnalyticOnNhd ℂ G₁ (chartRA a r₀ R))
    (hG₂ : AnalyticOnNhd ℂ G₂ (chartLA a r₀ R))
    (hpG₁ : ∀ z ∈ chartRA a r₀ R, G₁ z ^ (2 : ℕ) = f z)
    (hpG₂ : ∀ z ∈ chartLA a r₀ R, G₂ z ^ (2 : ℕ) = f z)
    {U : ℝ → ℂ}
    (hUc : ContinuousOn U (Icc (-(Real.pi / 2)) (3 * Real.pi / 2)))
    (hUsq : ∀ θ ∈ Icc (-(Real.pi / 2)) (3 * Real.pi / 2),
      U θ ^ (2 : ℕ) = f (circleMap a r θ)) :
    U (3 * Real.pi / 2) = U (-(Real.pi / 2)) := by
  classical
  have hkey := trace_holonomy_online_count s ρc m σf h0 hr₀ hrR hσmem hσρ
    hσm hσinv hρ hh hh0 hfact hG₁ hG₂ hpG₁ hpG₂ hUc hUsq
  rw [Finset.filter_false_of_mem hoffline, Finset.sum_empty, pow_zero,
    one_mul] at hkey
  exact hkey

end RHTower
