/-
# The ξ-tower and the RH_{2^k} ladder — machine-checked equivalences for mathlib's ζ

Arc A2 of the MWM lane (docs/drafts/rh-monodromy-weight-mismatch/).  The entire completed
`xi` (reference implementation: rh-formal-atlas `JensenLadder.RvMXiEntire.xiE`, same
toolchain; re-derived here to keep this repo self-contained), its FE, the zero
correspondence with `riemannZeta`, and the three main statements:

* `rh_iff_xi_ne_zero_right` — mathlib's `RiemannHypothesis` ⟺ `xi` has no zeros on `Re s > ½`;
* `rhLadder_iff_root` — level `k` of the ladder ⟺ an analytic `2^k`-th root of `xi` exists
  on the half-plane (the Kummer-obstruction capstone applied to `ξ`);
* `rh_iff_tower`, `rh_iff_forall_ladder` — RH ⟺ the coherent ℤ₂-Kummer tower of `ξ` exists
  on `Re s > ½` ⟺ every ladder level holds.

Everything is unconditional bookkeeping about branching; no zero-location input.
-/
import GaloisForLFunctions.RHTower.CoherentTower

namespace RHTower

open Complex Filter Set Metric

/-! ## The entire completed ξ -/

/-- The entire completed Riemann ξ: `ξ(s) = s(s-1)/2 · Λ₀(s) + ½` with
`Λ₀ = completedRiemannZeta₀`; equals `s(s-1)/2 · Λ(s)` away from `{0,1}`. -/
noncomputable def xi (s : ℂ) : ℂ := s * (s - 1) / 2 * completedRiemannZeta₀ s + 1 / 2

theorem xi_differentiable : Differentiable ℂ xi := by
  unfold xi
  have h := differentiable_completedZeta₀
  fun_prop

theorem xi_analyticOnNhd_univ : AnalyticOnNhd ℂ xi Set.univ :=
  xi_differentiable.differentiableOn.analyticOnNhd isOpen_univ

theorem xi_analyticOnNhd (U : Set ℂ) : AnalyticOnNhd ℂ xi U :=
  fun z _ => xi_analyticOnNhd_univ z (Set.mem_univ z)

theorem xi_eq_half_mul {s : ℂ} (h0 : s ≠ 0) (h1 : s ≠ 1) :
    xi s = s * (s - 1) / 2 * completedRiemannZeta s := by
  unfold xi
  rw [completedRiemannZeta_eq]
  have hs1 : (1 : ℂ) - s ≠ 0 := sub_ne_zero.mpr (Ne.symm h1)
  field_simp
  ring

theorem xi_one_sub (s : ℂ) : xi (1 - s) = xi s := by
  unfold xi
  rw [completedRiemannZeta₀_one_sub]
  ring

theorem xi_zero : xi 0 = 1 / 2 := by simp [xi]

theorem xi_one : xi 1 = 1 / 2 := by simp [xi]

theorem xi_two : xi 2 = completedRiemannZeta 2 := by
  rw [xi_eq_half_mul (by norm_num) (by norm_num)]
  norm_num

theorem xi_two_ne_zero : xi 2 ≠ 0 := by
  rw [xi_two]
  intro h
  have hζ : riemannZeta 2 ≠ 0 := riemannZeta_ne_zero_of_one_lt_re (by norm_num)
  have hd := riemannZeta_def_of_ne_zero (by norm_num : (2 : ℂ) ≠ 0)
  rw [h, zero_div] at hd
  exact hζ hd

/-! ## Zero correspondence with `riemannZeta` -/

theorem xi_eq_zero_iff {s : ℂ} (hre : 0 < s.re) (h1 : s ≠ 1) :
    xi s = 0 ↔ riemannZeta s = 0 := by
  have h0 : s ≠ 0 := by
    intro h
    rw [h] at hre
    simp at hre
  have hΓ : Gammaℝ s ≠ 0 := Complex.Gammaℝ_ne_zero_of_re_pos hre
  have hs2 : s * (s - 1) / 2 ≠ 0 :=
    div_ne_zero (mul_ne_zero h0 (sub_ne_zero.mpr h1)) two_ne_zero
  rw [xi_eq_half_mul h0 h1, riemannZeta_def_of_ne_zero h0]
  constructor
  · intro h
    rcases mul_eq_zero.mp h with h' | h'
    · exact absurd h' hs2
    · rw [h', zero_div]
  · intro h
    have hΛ : completedRiemannZeta s = 0 := by
      rcases div_eq_zero_iff.mp h with h' | h'
      · exact h'
      · exact absurd h' hΓ
    rw [hΛ, mul_zero]

/-- A nontrivial zero of `ζ` (other than the guards of mathlib's `RiemannHypothesis`) is a
zero of `ξ` — valid at every real part, via `Λ = ζ · Γℝ` and `Γℝ`'s zeros being trivial. -/
theorem xi_eq_zero_of_zeta_eq_zero {s : ℂ} (hζ : riemannZeta s = 0)
    (htriv : ¬∃ n : ℕ, s = -2 * ((n : ℂ) + 1)) (hs1 : s ≠ 1) : xi s = 0 := by
  have h0 : s ≠ 0 := by
    intro h
    rw [h, riemannZeta_zero] at hζ
    norm_num at hζ
  have hΓ : Gammaℝ s ≠ 0 := by
    rw [Ne, Complex.Gammaℝ_eq_zero_iff]
    rintro ⟨n, rfl⟩
    rcases Nat.eq_zero_or_pos n with hn | hn
    · subst hn
      exact h0 (by norm_num)
    · apply htriv
      refine ⟨n - 1, ?_⟩
      have : ((n - 1 : ℕ) : ℂ) = (n : ℂ) - 1 := by
        push_cast [Nat.cast_sub hn]
        ring
      rw [this]
      ring
  have hd := riemannZeta_def_of_ne_zero h0
  rw [hζ] at hd
  have hΛ : completedRiemannZeta s = 0 := by
    rcases div_eq_zero_iff.mp hd.symm with h | h
    · exact h
    · exact absurd h hΓ
  rw [xi_eq_half_mul h0 hs1, hΛ, mul_zero]

/-! ## The half-plane, its geometry, and local finiteness of the ξ-divisor -/

/-- The open right half-plane `Re s > ½`. -/
def rightHalf : Set ℂ := {s : ℂ | 1 / 2 < s.re}

theorem mem_rightHalf {s : ℂ} : s ∈ rightHalf ↔ 1 / 2 < s.re := Iff.rfl

theorem isOpen_rightHalf : IsOpen rightHalf :=
  isOpen_Ioi.preimage Complex.continuous_re

theorem convex_rightHalf : Convex ℝ rightHalf := convex_halfSpace_re_gt (1 / 2)

theorem two_mem_rightHalf : (2 : ℂ) ∈ rightHalf := by
  simp [mem_rightHalf]
  norm_num

/-- The set where `ξ` does not vanish is codiscrete in `ℂ` (i.e. the ξ-divisor is discrete):
`ξ` is entire and not identically zero. -/
theorem xi_ne_zero_codiscrete : {x | xi x ≠ 0} ∈ codiscreteWithin (Set.univ : Set ℂ) := by
  rcases xi_analyticOnNhd_univ.eqOn_zero_or_eventually_ne_zero_of_preconnected
      isPreconnected_univ with h | h
  · exact absurd (by simpa using h (Set.mem_univ (2 : ℂ))) xi_two_ne_zero
  · exact h

/-- Local finiteness of the ξ-zeros: finitely many in each bounded piece of the half-plane. -/
theorem xi_zeros_finite_in_ball (R : ℕ) :
    {s ∈ rightHalf ∩ ball (2 : ℂ) ((R : ℝ) + 1) | xi s = 0}.Finite := by
  have hK : IsCompact (closedBall (2 : ℂ) ((R : ℝ) + 1)) := isCompact_closedBall _ _
  have hmem : {x | xi x ≠ 0} ∈ codiscreteWithin (closedBall (2 : ℂ) ((R : ℝ) + 1)) :=
    Filter.codiscreteWithin_mono (subset_univ _) xi_ne_zero_codiscrete
  refine (hK.finite_diff_of_mem_codiscreteWithin hmem).subset ?_
  rintro x ⟨⟨_, hxb⟩, hx0⟩
  exact ⟨ball_subset_closedBall hxb, by simpa using hx0⟩

/-! ## The ladder and the main equivalences -/

/-- Level `k` of the RH ladder: every ξ-zero right of the critical line has vanishing order
divisible by `2^k`. -/
def RHLadder (k : ℕ) : Prop :=
  ∀ ρ ∈ rightHalf, xi ρ = 0 → ((2 ^ k : ℕ) : ℕ∞) ∣ analyticOrderAt xi ρ

/-- **Ladder ⟺ root.**  Level `k` holds iff `ξ` has an analytic `2^k`-th root on the
half-plane. -/
theorem rhLadder_iff_root (k : ℕ) :
    RHLadder k ↔
      ∃ g, AnalyticOnNhd ℂ g rightHalf ∧ ∀ s ∈ rightHalf, g s ^ 2 ^ k = xi s :=
  (exists_root_iff_orders_dvd (pow_pos two_pos k) isOpen_rightHalf convex_rightHalf
    two_mem_rightHalf (xi_analyticOnNhd _) xi_two_ne_zero xi_zeros_finite_in_ball).symm

/-- **RH ⟺ no ξ-zeros right of the line** (mathlib's `RiemannHypothesis`). -/
theorem rh_iff_xi_ne_zero_right :
    RiemannHypothesis ↔ ∀ s ∈ rightHalf, xi s ≠ 0 := by
  constructor
  · intro hRH s hs h0
    have hs1 : s ≠ 1 := by
      rintro rfl
      rw [xi_one] at h0
      norm_num at h0
    have hre : 0 < s.re := lt_trans (by norm_num) hs
    have hζ := (xi_eq_zero_iff hre hs1).mp h0
    have htriv : ¬∃ n : ℕ, s = -2 * ((n : ℂ) + 1) := by
      rintro ⟨n, rfl⟩
      have hre' : ((-2 : ℂ) * ((n : ℂ) + 1)).re = -2 * ((n : ℝ) + 1) := by
        simp [Complex.mul_re]
      rw [mem_rightHalf, hre'] at hs
      have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
      nlinarith
    have := hRH s hζ htriv hs1
    rw [mem_rightHalf, this] at hs
    exact lt_irrefl _ hs
  · intro hnz s hζ htriv hs1
    have hxi : xi s = 0 := xi_eq_zero_of_zeta_eq_zero hζ htriv hs1
    by_contra hre
    rcases lt_or_gt_of_ne hre with hlt | hgt
    · have hmem : (1 : ℂ) - s ∈ rightHalf := by
        rw [mem_rightHalf]
        simp only [Complex.sub_re, Complex.one_re]
        linarith
      exact hnz _ hmem (by rw [xi_one_sub]; exact hxi)
    · exact hnz s (mem_rightHalf.mpr hgt) hxi

/-- **RH ⟺ the coherent ℤ₂-Kummer tower of ξ exists on `Re s > ½`.** -/
theorem rh_iff_tower : RiemannHypothesis ↔ Nonempty (CoherentTower xi rightHalf) := by
  rw [rh_iff_xi_ne_zero_right,
    ← coherentTower_iff_nonvanishing isOpen_rightHalf
      (isSimplyConnected_of_convex convex_rightHalf ⟨2, two_mem_rightHalf⟩)
      convex_rightHalf.isPreconnected (xi_analyticOnNhd _) two_mem_rightHalf xi_two_ne_zero]

/-- **RH ⟺ every ladder level.**  The multiplicity-parity ladder exhausts RH. -/
theorem rh_iff_forall_ladder : RiemannHypothesis ↔ ∀ k, RHLadder k := by
  rw [rh_iff_xi_ne_zero_right]
  constructor
  · intro h k ρ hρ h0
    exact absurd h0 (h ρ hρ)
  · intro h ρ hρ hρ0
    have hord : analyticOrderAt xi ρ ≠ ⊤ := by
      intro htop
      have hev0 : xi =ᶠ[nhds ρ] (0 : ℂ → ℂ) := by
        filter_upwards [analyticOrderAt_eq_top.mp htop] with z hz
        simpa using hz
      exact xi_two_ne_zero
        (xi_analyticOnNhd_univ.eqOn_zero_of_preconnected_of_eventuallyEq_zero
          isPreconnected_univ (Set.mem_univ ρ) hev0 (Set.mem_univ 2))
    set m : ℕ := (analyticOrderAt xi ρ).toNat with hmdef
    have hm : (m : ℕ∞) = analyticOrderAt xi ρ := ENat.coe_toNat hord
    have hdvd : ∀ k : ℕ, 2 ^ k ∣ m := by
      intro k
      have hthis := h k ρ hρ hρ0
      rw [← hm] at hthis
      exact natCast_dvd_natCast_of_enat (pow_ne_zero k two_ne_zero) hthis
    have hm0 : m = 0 := by
      by_contra hm0
      have h2 : 2 ^ m ≤ m := Nat.le_of_dvd (Nat.pos_of_ne_zero hm0) (hdvd m)
      have h3 : m < 2 ^ m := Nat.lt_pow_self (by norm_num)
      omega
    have hne : analyticOrderAt xi ρ ≠ 0 :=
      analyticOrderAt_ne_zero.mpr ⟨xi_analyticOnNhd_univ ρ (Set.mem_univ ρ), hρ0⟩
    rw [← hm, hm0] at hne
    exact hne rfl

end RHTower
