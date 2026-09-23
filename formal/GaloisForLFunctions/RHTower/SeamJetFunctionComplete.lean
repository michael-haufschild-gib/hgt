import GaloisForLFunctions.RHTower.XiEntireReal

/-!
# The all-order seam jet is function complete

For an entire `Φ` with `Φ 0 ≠ 0`, a seam-log germ is a function `L` with `exp (L z) = Φ z / Φ 0`
near the origin.  Two such germs with the same Taylor coefficients agree near the origin
(`eventuallyEq_of_iteratedDeriv_eq`), hence the normalized functions `Φ / Φ 0` agree near the
origin and therefore everywhere by the identity theorem.

So the full seam-log jet determines the function up to its central scalar
(`seamJet_proportional`), hence determines the zero set (`seamJet_zero_set_eq`); together with the
central scalar it determines the function itself, and for an even function presented as
`F w = Φ (w²)` it determines `F` (`seamJet_even_function_complete`).
-/

noncomputable section

namespace RHTower

open Complex Filter Topology

/-- Two holomorphic germs at the origin with the same Taylor coefficients agree near the
origin. -/
theorem eventuallyEq_of_iteratedDeriv_eq {L₁ L₂ : ℂ → ℂ} {r : ℝ} (hr : 0 < r)
    (h₁ : DifferentiableOn ℂ L₁ (Metric.ball 0 r))
    (h₂ : DifferentiableOn ℂ L₂ (Metric.ball 0 r))
    (h : ∀ n : ℕ, iteratedDeriv n L₁ 0 = iteratedDeriv n L₂ 0) :
    ∀ᶠ z in 𝓝 (0 : ℂ), L₁ z = L₂ z := by
  have hball : ∀ z ∈ Metric.ball (0 : ℂ) r, L₁ z = L₂ z := by
    intro z hz
    rw [← Complex.taylorSeries_eq_on_ball' (hz := hz) h₁,
      ← Complex.taylorSeries_eq_on_ball' (hz := hz) h₂]
    exact tsum_congr (fun n => by rw [h n])
  exact Filter.eventually_iff_exists_mem.mpr
    ⟨Metric.ball (0 : ℂ) r, Metric.ball_mem_nhds 0 hr, hball⟩

/-- Two entire functions with the same Taylor coefficients at the origin are equal. -/
theorem entire_eq_of_iteratedDeriv_eq {f g : ℂ → ℂ} (hf : Differentiable ℂ f)
    (hg : Differentiable ℂ g) (h : ∀ n : ℕ, iteratedDeriv n f 0 = iteratedDeriv n g 0) :
    f = g := by
  funext z
  rw [← Complex.taylorSeries_eq_of_entire' hf (c := 0) (z := z),
    ← Complex.taylorSeries_eq_of_entire' hg (c := 0) (z := z)]
  exact tsum_congr (fun n => by rw [h n])

/-- Two entire functions agreeing near the origin are equal. -/
theorem entire_eq_of_eventuallyEq {f g : ℂ → ℂ} (hf : Differentiable ℂ f)
    (hg : Differentiable ℂ g) (h : ∀ᶠ z in 𝓝 (0 : ℂ), f z = g z) : f = g := by
  have hfa : AnalyticOnNhd ℂ f Set.univ := Complex.analyticOnNhd_univ_iff_differentiable.mpr hf
  have hga : AnalyticOnNhd ℂ g Set.univ := Complex.analyticOnNhd_univ_iff_differentiable.mpr hg
  funext z
  exact hfa.eqOn_of_preconnected_of_eventuallyEq hga isPreconnected_univ
    (Set.mem_univ (0 : ℂ)) h (Set.mem_univ z)

/-- **The all-order seam-log jet is function complete.**  Two entire functions nonzero at the
origin whose seam-log germs agree near the origin are proportional; with equal central scalars
they are equal. -/
theorem seamJet_function_complete {Φ₁ Φ₂ L₁ L₂ : ℂ → ℂ}
    (h₁ : Differentiable ℂ Φ₁) (h₂ : Differentiable ℂ Φ₂)
    (hL₁ : ∀ᶠ z in 𝓝 (0 : ℂ), Complex.exp (L₁ z) = Φ₁ z / Φ₁ 0)
    (hL₂ : ∀ᶠ z in 𝓝 (0 : ℂ), Complex.exp (L₂ z) = Φ₂ z / Φ₂ 0)
    (hLeq : ∀ᶠ z in 𝓝 (0 : ℂ), L₁ z = L₂ z) :
    (fun z => Φ₁ z / Φ₁ 0) = fun z => Φ₂ z / Φ₂ 0 := by
  refine entire_eq_of_eventuallyEq (h₁.div_const _) (h₂.div_const _) ?_
  filter_upwards [hL₁, hL₂, hLeq] with z e₁ e₂ e
  rw [← e₁, ← e₂, e]

/-- The proportionality form: the seam-log jet determines the function up to its central
scalar. -/
theorem seamJet_proportional {Φ₁ Φ₂ L₁ L₂ : ℂ → ℂ}
    (h₁ : Differentiable ℂ Φ₁) (h₂ : Differentiable ℂ Φ₂)
    (hz₁ : Φ₁ 0 ≠ 0) (hz₂ : Φ₂ 0 ≠ 0)
    (hL₁ : ∀ᶠ z in 𝓝 (0 : ℂ), Complex.exp (L₁ z) = Φ₁ z / Φ₁ 0)
    (hL₂ : ∀ᶠ z in 𝓝 (0 : ℂ), Complex.exp (L₂ z) = Φ₂ z / Φ₂ 0)
    (hLeq : ∀ᶠ z in 𝓝 (0 : ℂ), L₁ z = L₂ z) :
    ∀ z, Φ₁ z = (Φ₁ 0 / Φ₂ 0) * Φ₂ z := by
  intro z
  have h := congrFun (seamJet_function_complete h₁ h₂ hL₁ hL₂ hLeq) z
  have h2 : Φ₁ z * Φ₂ 0 = Φ₂ z * Φ₁ 0 := (div_eq_div_iff hz₁ hz₂).mp h
  rw [div_mul_eq_mul_div, eq_div_iff hz₂]
  linear_combination h2

/-- The zero divisor is determined: the two functions have the same zero set. -/
theorem seamJet_zero_set_eq {Φ₁ Φ₂ L₁ L₂ : ℂ → ℂ}
    (h₁ : Differentiable ℂ Φ₁) (h₂ : Differentiable ℂ Φ₂)
    (hz₁ : Φ₁ 0 ≠ 0) (hz₂ : Φ₂ 0 ≠ 0)
    (hL₁ : ∀ᶠ z in 𝓝 (0 : ℂ), Complex.exp (L₁ z) = Φ₁ z / Φ₁ 0)
    (hL₂ : ∀ᶠ z in 𝓝 (0 : ℂ), Complex.exp (L₂ z) = Φ₂ z / Φ₂ 0)
    (hLeq : ∀ᶠ z in 𝓝 (0 : ℂ), L₁ z = L₂ z) :
    ∀ z, Φ₁ z = 0 ↔ Φ₂ z = 0 := by
  intro z
  have hprop := seamJet_proportional h₁ h₂ hz₁ hz₂ hL₁ hL₂ hLeq z
  have hc : Φ₁ 0 / Φ₂ 0 ≠ 0 := div_ne_zero hz₁ hz₂
  rw [hprop, mul_eq_zero]
  exact or_iff_right hc

/-- **With the central scalar, the even function itself is determined.** -/
theorem seamJet_even_function_complete {F₁ F₂ Φ₁ Φ₂ L₁ L₂ : ℂ → ℂ}
    (hF₁ : ∀ w, F₁ w = Φ₁ (w ^ (2 : ℕ))) (hF₂ : ∀ w, F₂ w = Φ₂ (w ^ (2 : ℕ)))
    (h₁ : Differentiable ℂ Φ₁) (h₂ : Differentiable ℂ Φ₂)
    (hz₁ : Φ₁ 0 ≠ 0) (hz₂ : Φ₂ 0 ≠ 0) (hscalar : Φ₁ 0 = Φ₂ 0)
    (hL₁ : ∀ᶠ z in 𝓝 (0 : ℂ), Complex.exp (L₁ z) = Φ₁ z / Φ₁ 0)
    (hL₂ : ∀ᶠ z in 𝓝 (0 : ℂ), Complex.exp (L₂ z) = Φ₂ z / Φ₂ 0)
    (hLeq : ∀ᶠ z in 𝓝 (0 : ℂ), L₁ z = L₂ z) :
    F₁ = F₂ := by
  funext w
  rw [hF₁, hF₂]
  have hprop := seamJet_proportional h₁ h₂ hz₁ hz₂ hL₁ hL₂ hLeq (w ^ (2 : ℕ))
  rw [hprop, hscalar, div_self hz₂, one_mul]

/-! ### Triangular seam coordinates -/

/-- The `n`-th Taylor coefficient of a seam-log germ. -/
def seamLogCoeff (L : ℂ → ℂ) (n : ℕ) : ℂ :=
  ((Nat.factorial n : ℕ) : ℂ)⁻¹ * iteratedDeriv n L 0

theorem iteratedDeriv_eq_of_seamLogCoeff_eq {L₁ L₂ : ℂ → ℂ}
    (h : ∀ n : ℕ, seamLogCoeff L₁ n = seamLogCoeff L₂ n) (n : ℕ) :
    iteratedDeriv n L₁ 0 = iteratedDeriv n L₂ 0 := by
  have hn : ((Nat.factorial n : ℕ) : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n)
  have := h n
  rw [seamLogCoeff, seamLogCoeff] at this
  field_simp at this
  exact this

/-- **A triangular coordinate change is invertible.**  If each new coordinate is a nonzero multiple
of the corresponding old one plus an arbitrary expression in the strictly earlier ones, then the
new sequence determines the old one. -/
theorem triangular_determines {a : ℕ → ℂ} (ha : ∀ n, a n ≠ 0)
    (P : ∀ n : ℕ, (Fin n → ℂ) → ℂ) {l l' : ℕ → ℂ}
    (h : ∀ n : ℕ, a n * l n + P n (fun i : Fin n => l (i : ℕ)) =
      a n * l' n + P n (fun i : Fin n => l' (i : ℕ))) : l = l' := by
  funext n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    have hprev : (fun i : Fin n => l (i : ℕ)) = fun i : Fin n => l' (i : ℕ) :=
      funext fun i => ih i i.2
    have hn := h n
    rw [hprev] at hn
    exact mul_left_cancel₀ (ha n) (by linear_combination hn)

/-- **Triangular seam coordinates are function complete.**  Any all-order coordinate sequence that
is triangular over the seam-log coefficients determines the function up to its central scalar. -/
theorem triangularSeam_function_complete {a : ℕ → ℂ} (ha : ∀ n, a n ≠ 0)
    (P : ∀ n : ℕ, (Fin n → ℂ) → ℂ)
    {Φ₁ Φ₂ L₁ L₂ : ℂ → ℂ} {r : ℝ} (hr : 0 < r)
    (h₁ : Differentiable ℂ Φ₁) (h₂ : Differentiable ℂ Φ₂)
    (hz₁ : Φ₁ 0 ≠ 0) (hz₂ : Φ₂ 0 ≠ 0)
    (hd₁ : DifferentiableOn ℂ L₁ (Metric.ball 0 r))
    (hd₂ : DifferentiableOn ℂ L₂ (Metric.ball 0 r))
    (hL₁ : ∀ᶠ z in 𝓝 (0 : ℂ), Complex.exp (L₁ z) = Φ₁ z / Φ₁ 0)
    (hL₂ : ∀ᶠ z in 𝓝 (0 : ℂ), Complex.exp (L₂ z) = Φ₂ z / Φ₂ 0)
    (hc : ∀ n : ℕ,
      a n * seamLogCoeff L₁ n + P n (fun i : Fin n => seamLogCoeff L₁ (i : ℕ)) =
        a n * seamLogCoeff L₂ n + P n (fun i : Fin n => seamLogCoeff L₂ (i : ℕ))) :
    ∀ z, Φ₁ z = (Φ₁ 0 / Φ₂ 0) * Φ₂ z := by
  have hcoeff : seamLogCoeff L₁ = seamLogCoeff L₂ := triangular_determines ha P hc
  have hderiv : ∀ n : ℕ, iteratedDeriv n L₁ 0 = iteratedDeriv n L₂ 0 :=
    iteratedDeriv_eq_of_seamLogCoeff_eq (fun n => congrFun hcoeff n)
  exact seamJet_proportional h₁ h₂ hz₁ hz₂ hL₁ hL₂
    (eventuallyEq_of_iteratedDeriv_eq hr hd₁ hd₂ hderiv)

/-- The zero divisor is determined by any triangular seam coordinate sequence. -/
theorem triangularSeam_zero_set_eq {a : ℕ → ℂ} (ha : ∀ n, a n ≠ 0)
    (P : ∀ n : ℕ, (Fin n → ℂ) → ℂ)
    {Φ₁ Φ₂ L₁ L₂ : ℂ → ℂ} {r : ℝ} (hr : 0 < r)
    (h₁ : Differentiable ℂ Φ₁) (h₂ : Differentiable ℂ Φ₂)
    (hz₁ : Φ₁ 0 ≠ 0) (hz₂ : Φ₂ 0 ≠ 0)
    (hd₁ : DifferentiableOn ℂ L₁ (Metric.ball 0 r))
    (hd₂ : DifferentiableOn ℂ L₂ (Metric.ball 0 r))
    (hL₁ : ∀ᶠ z in 𝓝 (0 : ℂ), Complex.exp (L₁ z) = Φ₁ z / Φ₁ 0)
    (hL₂ : ∀ᶠ z in 𝓝 (0 : ℂ), Complex.exp (L₂ z) = Φ₂ z / Φ₂ 0)
    (hc : ∀ n : ℕ,
      a n * seamLogCoeff L₁ n + P n (fun i : Fin n => seamLogCoeff L₁ (i : ℕ)) =
        a n * seamLogCoeff L₂ n + P n (fun i : Fin n => seamLogCoeff L₂ (i : ℕ))) :
    ∀ z, Φ₁ z = 0 ↔ Φ₂ z = 0 := by
  intro z
  have hprop := triangularSeam_function_complete ha P hr h₁ h₂ hz₁ hz₂ hd₁ hd₂ hL₁ hL₂ hc z
  have hcne : Φ₁ 0 / Φ₂ 0 ≠ 0 := div_ne_zero hz₁ hz₂
  rw [hprop, mul_eq_zero]
  exact or_iff_right hcne

end RHTower
