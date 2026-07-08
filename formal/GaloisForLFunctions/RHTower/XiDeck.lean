/-
The ξ-layer wiring of the deck cocycle (MWM lane; the A3 arc meets Arc A).

* `xi_orderAt_ne_top` — ξ has finite vanishing order everywhere.
* `xi_peel_ball` — around any point, ξ = (z−ρ₀)^m · h on a small ball with h analytic and
  NONVANISHING (peeling + continuity shrink).
* `xi_deckClass` — around any ρ₀ there is R₀ > 0 such that for all radii 0 < R ≤ R₀ and
  all n > 0, ANY local analytic n-th roots of ξ on the two slit charts have deck class
  exp(2πi·m/n), m = (analyticOrderAt xi ρ₀).toNat: **the box invariant of the actual
  completed zeta counts the zero's multiplicity mod n.**
* `exp_two_pi_mul_div_eq_one_iff` — the class is 1 iff n ∣ m.
* `xi_deckClass_eq_one_iff_ladder_dvd` — at n = 2^k the triviality of the deck class IS
  the divisibility clause of `RHLadder k`, the statement `rh_iff_forall_ladder`
  quantifies over. The ladder's local obstruction is the deck class, end to end, with no
  argument principle anywhere.
-/
import GaloisForLFunctions.RHTower.DeckMultiZero
import GaloisForLFunctions.RHTower.RiemannTower

namespace RHTower

open Complex Metric

/-- ξ has finite vanishing order everywhere (it is not identically zero). -/
theorem xi_orderAt_ne_top (ρ : ℂ) : analyticOrderAt xi ρ ≠ ⊤ := by
  exact xi_order_ne_top ρ

/-- Around any point, ξ peels on a small ball with a nonvanishing analytic cofactor. -/
theorem xi_peel_ball (ρ₀ : ℂ) :
    ∃ R₀ > 0, ∃ h : ℂ → ℂ, AnalyticOnNhd ℂ h (ball ρ₀ R₀) ∧
      (∀ z ∈ ball ρ₀ R₀, h z ≠ 0) ∧
      ∀ z ∈ ball ρ₀ R₀, xi z = (z - ρ₀) ^ (analyticOrderAt xi ρ₀).toNat * h z := by
  have hm : analyticOrderAt xi ρ₀ = ((analyticOrderAt xi ρ₀).toNat : ℕ∞) :=
    (ENat.coe_toNat (xi_orderAt_ne_top ρ₀)).symm
  obtain ⟨h, hhan, hh0, hfact, -⟩ :=
    exists_peel isOpen_univ xi_analyticOnNhd_univ (Set.mem_univ ρ₀) hm
  have hcont : ContinuousAt h ρ₀ :=
    (hhan ρ₀ (Set.mem_univ ρ₀)).continuousAt
  have hev : ∀ᶠ z in nhds ρ₀, h z ≠ 0 := hcont.eventually_ne hh0
  obtain ⟨R₀, hR₀, hball⟩ := Metric.eventually_nhds_iff.mp hev
  refine ⟨R₀, hR₀, h, fun z _ => hhan z (Set.mem_univ z), ?_, ?_⟩
  · intro z hz
    exact hball (by rwa [mem_ball] at hz)
  · intro z _
    exact hfact z (Set.mem_univ z)

/-- **The deck class of ξ counts multiplicity.** Around any ρ₀ there is R₀ > 0 such that
for every radius 0 < R ≤ R₀ and every n > 0, ANY local analytic n-th roots of ξ on the
two slit charts have deck class exp(2πi·m/n) with m the vanishing order of ξ at ρ₀. -/
theorem xi_deckClass (ρ₀ : ℂ) :
    ∃ R₀ > 0, ∀ {R : ℝ}, 0 < R → R ≤ R₀ → ∀ {n : ℕ}, 0 < n → ∀ {G₁ G₂ : ℂ → ℂ},
      AnalyticOnNhd ℂ G₁ (chartR ρ₀ R) → AnalyticOnNhd ℂ G₂ (chartL ρ₀ R) →
      (∀ z ∈ chartR ρ₀ R, G₁ z ^ n = xi z) → (∀ z ∈ chartL ρ₀ R, G₂ z ^ n = xi z) →
      deckClass G₁ G₂ (ρ₀ + ((R / 2 : ℝ) : ℂ) * I) (ρ₀ - ((R / 2 : ℝ) : ℂ) * I) =
        exp (2 * (Real.pi : ℂ) * I * ((analyticOrderAt xi ρ₀).toNat : ℕ) / n) := by
  obtain ⟨R₀, hR₀, h, hhan, hh0, hfact⟩ := xi_peel_ball ρ₀
  refine ⟨R₀, hR₀, ?_⟩
  intro R hR hRle n hn G₁ G₂ hG₁ hG₂ hpG₁ hpG₂
  have hsub : ball ρ₀ R ⊆ ball ρ₀ R₀ := ball_subset_ball hRle
  exact deckClass_single_zero hR hn
    (fun z hz => hhan z (hsub hz)) (fun z hz => hh0 z (hsub hz))
    (fun z hz => hfact z (hsub hz)) hG₁ hG₂ hpG₁ hpG₂

/-- The root-of-unity criterion: `exp(2πi·m/n) = 1 ↔ n ∣ m`. -/
theorem exp_two_pi_mul_div_eq_one_iff {n : ℕ} (hn : 0 < n) (m : ℕ) :
    exp (2 * (Real.pi : ℂ) * I * m / n) = 1 ↔ n ∣ m := by
  rw [Complex.exp_eq_one_iff]
  have hn0 : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
  have hπI : (2 : ℂ) * Real.pi * I ≠ 0 := by
    refine mul_ne_zero (mul_ne_zero two_ne_zero ?_) I_ne_zero
    exact_mod_cast Real.pi_ne_zero
  constructor
  · rintro ⟨k, hk⟩
    have hmn : (m : ℂ) = k * n := by
      have h2 : (2 : ℂ) * Real.pi * I * m / n = k * (2 * Real.pi * I) := hk
      field_simp at h2
      -- h2 : 2 * π * I * m = k * (2 * π * I) * n (up to arrangement)
      have h3 : (2 : ℂ) * Real.pi * I * m = 2 * Real.pi * I * (k * n) := by
        rw [h2]; ring
      exact mul_left_cancel₀ hπI h3
    have hmZ : (m : ℤ) = k * n := by exact_mod_cast hmn
    have : (n : ℤ) ∣ (m : ℤ) := ⟨k, by linarith [hmZ]⟩
    exact_mod_cast this
  · rintro ⟨c, rfl⟩
    refine ⟨c, ?_⟩
    push_cast
    field_simp

/-- **The ladder's local obstruction is the deck class.** At `n = 2^k`, triviality of the
deck class of any local roots of ξ at a zero ρ₀ is EXACTLY the divisibility clause
`(2^k : ℕ∞) ∣ analyticOrderAt xi ρ₀` that `RHLadder k` (hence `rh_iff_forall_ladder`)
quantifies over. -/
theorem xi_deckClass_eq_one_iff_ladder_dvd (ρ₀ : ℂ) (k : ℕ) :
    ∃ R₀ > 0, ∀ {R : ℝ}, 0 < R → R ≤ R₀ → ∀ {G₁ G₂ : ℂ → ℂ},
      AnalyticOnNhd ℂ G₁ (chartR ρ₀ R) → AnalyticOnNhd ℂ G₂ (chartL ρ₀ R) →
      (∀ z ∈ chartR ρ₀ R, G₁ z ^ (2 ^ k) = xi z) →
      (∀ z ∈ chartL ρ₀ R, G₂ z ^ (2 ^ k) = xi z) →
      (deckClass G₁ G₂ (ρ₀ + ((R / 2 : ℝ) : ℂ) * I) (ρ₀ - ((R / 2 : ℝ) : ℂ) * I) = 1 ↔
        ((2 ^ k : ℕ) : ℕ∞) ∣ analyticOrderAt xi ρ₀) := by
  obtain ⟨R₀, hR₀, hclass⟩ := xi_deckClass ρ₀
  refine ⟨R₀, hR₀, ?_⟩
  intro R hR hRle G₁ G₂ hG₁ hG₂ hpG₁ hpG₂
  have h2k : 0 < 2 ^ k := pow_pos (by norm_num) k
  rw [hclass hR hRle h2k hG₁ hG₂ hpG₁ hpG₂,
    exp_two_pi_mul_div_eq_one_iff h2k]
  set m : ℕ := (analyticOrderAt xi ρ₀).toNat with hm_def
  have hm : (m : ℕ∞) = analyticOrderAt xi ρ₀ := ENat.coe_toNat (xi_orderAt_ne_top ρ₀)
  constructor
  · rintro ⟨c, hc⟩
    rw [← hm, hc]
    exact ⟨(c : ℕ∞), by push_cast; ring⟩
  · intro hdvd
    rw [← hm] at hdvd
    exact natCast_dvd_natCast_of_enat (pow_ne_zero k two_ne_zero) hdvd

end RHTower
