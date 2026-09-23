import GaloisForLFunctions.Bottcher.BoundaryCollarExtension

open Complex Metric Set Filter Topology

namespace Bottcher

/-- **The dyadic-doubling orbit of any circle arc covers the circle.** For a nonempty metric ball
`ball ζ₀ r` around a boundary point `ζ₀` (`|ζ₀| = 1`), every circle point `ζ` is `ζ'^{2ⁿ}` for some
`ζ'` in that ball. Parametrize by angle `e θ = exp(θ i)`; the preimages `(φ + 2πk)/2ⁿ` of the target
angle `φ` are `2π/2ⁿ`-spaced, so for `n` large a rounded `k` lands the base angle within `ε` of `θ₀`,
i.e. `ζ' = e θ` in the ball, and `ζ'^{2ⁿ} = e φ = ζ`. -/
theorem doubling_orbit_covers {ζ₀ : ℂ} (hζ₀ : ‖ζ₀‖ = 1) {r : ℝ} (hr : 0 < r)
    (ζ : ℂ) (hζ : ‖ζ‖ = 1) :
    ∃ ζ' : ℂ, ‖ζ'‖ = 1 ∧ ζ' ∈ Metric.ball ζ₀ r ∧ ∃ n : ℕ, ζ = ζ' ^ (2 ^ n) := by
  set e : ℝ → ℂ := fun θ => Complex.exp (↑θ * I) with hedef
  have he_cont : Continuous e := by fun_prop
  have he_norm : ∀ θ : ℝ, ‖e θ‖ = 1 := by
    intro θ; rw [hedef, Complex.norm_exp]; simp
  have heθ₀ : e (Complex.arg ζ₀) = ζ₀ := by
    have := norm_mul_exp_arg_mul_I ζ₀; rw [hζ₀] at this; simpa [hedef] using this
  have heφ : e (Complex.arg ζ) = ζ := by
    have := norm_mul_exp_arg_mul_I ζ; rw [hζ] at this; simpa [hedef] using this
  set θ₀ : ℝ := Complex.arg ζ₀ with hθ₀
  set φ : ℝ := Complex.arg ζ with hφ
  -- an interval of angles around θ₀ maps into the ball
  have hnhds : ∀ᶠ θ in nhds θ₀, e θ ∈ Metric.ball ζ₀ r := by
    have hmem : e θ₀ ∈ Metric.ball ζ₀ r := by rw [heθ₀]; exact Metric.mem_ball_self hr
    exact he_cont.continuousAt.eventually_mem (Metric.isOpen_ball.mem_nhds hmem)
  rw [Metric.eventually_nhds_iff] at hnhds
  obtain ⟨ε, hε, hball⟩ := hnhds
  -- pick n with 2ⁿ > π/ε
  obtain ⟨n, hn⟩ : ∃ n : ℕ, Real.pi / ε < 2 ^ n :=
    pow_unbounded_of_one_lt (Real.pi / ε) (by norm_num : (1:ℝ) < 2)
  have h2n : (0:ℝ) < 2 ^ n := by positivity
  have hpi : (0:ℝ) < 2 * Real.pi := by positivity
  set x : ℝ := (2 ^ n * θ₀ - φ) / (2 * Real.pi) with hx
  set k : ℤ := round x with hk
  set θk : ℝ := (φ + 2 * Real.pi * (k : ℝ)) / 2 ^ n with hθk
  have hclose : |θk - θ₀| < ε := by
    have hkx : |(k : ℝ) - x| ≤ 1/2 := by rw [abs_sub_comm]; exact abs_sub_round x
    have heq : θk - θ₀ = (2 * Real.pi) * ((k : ℝ) - x) / 2 ^ n := by
      rw [hθk, hx]; field_simp; ring
    rw [heq, abs_div, abs_mul, abs_of_pos hpi, abs_of_pos h2n]
    have hb : 2 * Real.pi * |(k : ℝ) - x| ≤ Real.pi := by
      nlinarith [hkx, Real.pi_pos, abs_nonneg ((k : ℝ) - x)]
    have hmono : 2 * Real.pi * |(k : ℝ) - x| / 2 ^ n ≤ Real.pi / 2 ^ n :=
      (div_le_div_iff_of_pos_right h2n).mpr hb
    have hpi2 : Real.pi / 2 ^ n < ε := by
      rw [div_lt_iff₀ h2n, mul_comm]
      rw [div_lt_iff₀ hε] at hn; linarith
    linarith
  refine ⟨e θk, he_norm θk, ?_, n, ?_⟩
  · exact @hball θk (by rw [Real.dist_eq]; exact hclose)
  · rw [← heφ]
    have harg : (↑(2 ^ n : ℕ) : ℂ) * (↑θk * I) = ↑φ * I + (↑k : ℂ) * (2 * ↑Real.pi * I) := by
      rw [hθk]; push_cast; field_simp
    have hpow : (e θk) ^ (2 ^ n) = e φ := by
      rw [hedef, ← Complex.exp_nat_mul, harg, Complex.exp_add,
        Complex.exp_int_mul_two_pi_mul_I, mul_one]
    exact hpow.symm

/-- **task02 §1, closed.** If `h` is holomorphic on the unit disk, solves the Böttcher functional
equation there, and continues across every point of a nonempty boundary arc `ball ζ₀ r ∩ (circle)`,
then it extends holomorphically to a strictly larger disk. The doubling-covering `hgen` input of
`holo_extend_of_continuesAcross_generating` is discharged by `doubling_orbit_covers`. -/
theorem holo_extend_of_continuesAcross_arc {h : ℂ → ℂ} {c : ℂ} {ζ₀ : ℂ} {r : ℝ}
    (hζ₀ : ‖ζ₀‖ = 1) (hr : 0 < r)
    (hhd : DifferentiableOn ℂ h (ball 0 1))
    (hfe : ∀ t ∈ ball (0 : ℂ) 1, h (t ^ (2 : ℕ)) = (h t) ^ (2 : ℕ) + c * t ^ (2 : ℕ))
    (harc : ∀ ζ : ℂ, ‖ζ‖ = 1 → ζ ∈ Metric.ball ζ₀ r → ContinuesAcross h ζ) :
    ∃ ρ : ℝ, 1 < ρ ∧ ∃ H : ℂ → ℂ, DifferentiableOn ℂ H (ball 0 ρ) ∧ EqOn H h (ball 0 1) := by
  refine holo_extend_of_continuesAcross_generating (A := {ζ : ℂ | ‖ζ‖ = 1 ∧ ζ ∈ Metric.ball ζ₀ r})
    hhd hfe ?_ ?_
  · rintro ζ ⟨hζ1, hζr⟩; exact ⟨hζ1, harc ζ hζ1 hζr⟩
  · intro ζ hζ
    obtain ⟨ζ', hζ'1, hζ'r, n, hn⟩ := doubling_orbit_covers hζ₀ hr ζ hζ
    exact ⟨ζ', ⟨hζ'1, hζ'r⟩, n, hn⟩

/-- **Abstract connected-case natural boundary (task02, answer-02 core).** For `c ∉ {0, -2}`, an even
holomorphic solution `h` of the Böttcher functional equation on the unit disk (`h 0 = 1`) does NOT
continue analytically across any boundary arc: the unit circle is a natural boundary for `h`. This is
the contrapositive of the §1–§5 classification — an arc-continuation would extend `h` holomorphically
to a larger disk (`holo_extend_of_continuesAcross_arc`), which forces `c ∈ {0, -2}`
(`c_mem_of_even_holo_ball`). -/
theorem natural_boundary_of_even_fe {h : ℂ → ℂ} {c : ℂ} {ζ₀ : ℂ} {r : ℝ}
    (hc0 : c ≠ 0) (hc2 : c ≠ -2) (hζ₀ : ‖ζ₀‖ = 1) (hr : 0 < r)
    (hhd : DifferentiableOn ℂ h (ball 0 1))
    (hhe : ∀ z ∈ ball (0 : ℂ) 1, h (-z) = h z)
    (hfe : ∀ t ∈ ball (0 : ℂ) 1, h (t ^ (2 : ℕ)) = (h t) ^ (2 : ℕ) + c * t ^ (2 : ℕ))
    (hh0 : h 0 = 1) :
    ¬ (∀ ζ : ℂ, ‖ζ‖ = 1 → ζ ∈ Metric.ball ζ₀ r → ContinuesAcross h ζ) := by
  intro harc
  obtain ⟨ρ, hρ, H, hHd, hHh⟩ :=
    holo_extend_of_continuesAcross_arc hζ₀ hr hhd hfe harc
  -- `H` is even on `ball ρ` by the identity theorem
  have hHeven : ∀ z ∈ ball (0 : ℂ) ρ, H (-z) = H z := by
    have hneg : DifferentiableOn ℂ (fun z => H (-z)) (ball 0 ρ) :=
      hHd.comp differentiable_neg.differentiableOn (fun z hz => by
        rw [mem_ball_zero_iff, norm_neg]; rwa [mem_ball_zero_iff] at hz)
    have hA1 : AnalyticOnNhd ℂ (fun z => H (-z)) (ball 0 ρ) := hneg.analyticOnNhd isOpen_ball
    have hA2 : AnalyticOnNhd ℂ H (ball 0 ρ) := hHd.analyticOnNhd isOpen_ball
    have hev : (fun z => H (-z)) =ᶠ[𝓝 (0 : ℂ)] H := by
      filter_upwards [isOpen_ball.mem_nhds (mem_ball_self one_pos)] with z hz
      have hnz : -z ∈ ball (0 : ℂ) 1 := by
        rw [mem_ball_zero_iff, norm_neg]; rwa [mem_ball_zero_iff] at hz
      rw [hHh hnz, hhe z hz, hHh hz]
    exact hA1.eqOn_of_preconnected_of_eventuallyEq hA2 (convex_ball 0 ρ).isPreconnected
      (mem_ball_self (by linarith)) hev
  -- `H` satisfies the functional equation on `ball 1`
  have hHfe : ∀ t ∈ ball (0 : ℂ) 1, H (t ^ (2 : ℕ)) = (H t) ^ (2 : ℕ) + c * t ^ (2 : ℕ) := by
    intro t ht
    have ht2 : t ^ (2 : ℕ) ∈ ball (0 : ℂ) 1 := by
      rw [mem_ball_zero_iff] at ht ⊢; rw [norm_pow]; nlinarith [norm_nonneg t, ht]
    rw [hHh ht2, hHh ht, hfe t ht]
  have hH0 : H 0 = 1 := by rw [hHh (mem_ball_self one_pos), hh0]
  rcases c_mem_of_even_holo_ball hρ hHd hHeven hHfe hH0 with h0 | h2
  · exact hc0 h0
  · exact hc2 h2

end Bottcher
