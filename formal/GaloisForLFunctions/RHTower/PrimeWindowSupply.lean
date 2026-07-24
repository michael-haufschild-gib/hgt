import GaloisForLFunctions.RHTower.PsiRatioDescent
import GaloisForLFunctions.RHTower.PsiWindowUpperBound
import GaloisForLFunctions.RHTower.WeightedEulerPrimeNodeAssembly

/-!
# Unconditional prime supply in multiplicative windows

From the elementary prime number theorem `ψ(N) = N + o(N)`:

* `θ(N) = N + o(N)` — the prime-power correction is `≤ 2√N·log N`,
  linearly dominated past the quartic threshold;
* every multiplicative window `[e^y, e^{y+η}]` eventually contains a
  prime: the `θ`-mass of the window is at least
  `(e^η − 1)e^y/4 > 0` once the PNT error is below
  `(e^η − 1)/(8e^η)`;
* hence the separated prime-log node families of
  `exists_separated_primeLog_nodes` exist unconditionally in every unit
  interval far enough to the right.
-/

noncomputable section

namespace RHTower

open ArithmeticFunction Finset

/-- **`θ`-form of the prime number theorem**:
`|θ(N) − N| ≤ ε·N` eventually. -/
theorem chebyshevTheta_remainder_eventually_le {ε : ℝ} (hε : 0 < ε) :
    ∃ x₀ : ℕ, ∀ N : ℕ, x₀ ≤ N →
      |Chebyshev.theta N - N| ≤ ε * N := by
  obtain ⟨x₁, hx₁⟩ := psiRemainder_eventually_le
    (show (0 : ℝ) < ε / 2 by linarith)
  refine ⟨max x₁ (max ⌈(16 / ε) ^ 4⌉₊ 1), fun N hN => ?_⟩
  have hNx₁ : x₁ ≤ N := le_trans (le_max_left _ _) hN
  have hNc : ⌈(16 / ε) ^ 4⌉₊ ≤ N :=
    le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hN
  have hN1 : 1 ≤ N :=
    le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hN
  have hNR1 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN1
  have hNR0 : (0 : ℝ) ≤ (N : ℝ) := by linarith
  have hψ := hx₁ N hNx₁
  have hunfold : psiRemainder N = Chebyshev.psi N - N := by
    simp only [psiRemainder]
    rw [chebyshevPsi_eq_psi]
  rw [hunfold] at hψ
  have hψ' := abs_le.1 hψ
  have hθψ : Chebyshev.psi N - Chebyshev.theta N
      ≤ 2 * Real.sqrt N * Real.log N :=
    Chebyshev.psi_sub_theta_le hNR1
  have hθψ0 : Chebyshev.theta N ≤ Chebyshev.psi N :=
    Chebyshev.theta_le_psi _
  have hquartic : (16 / ε) ^ 4 ≤ (N : ℝ) := by
    have h1 := Nat.le_ceil ((16 / ε) ^ 4)
    have h2 : ((⌈(16 / ε) ^ 4⌉₊ : ℕ) : ℝ) ≤ (N : ℝ) := by
      exact_mod_cast hNc
    linarith
  have hsqrtN : 2 * Real.sqrt N * Real.log N ≤ ε / 2 * N :=
    HTGeometry.two_sqrt_mul_log_le_of_quartic_ge hε hquartic
  rw [abs_le]
  constructor
  · linarith
  · linarith

/-- **Unconditional prime supply**: every multiplicative window
`[e^y, e^{y+η}]` with `y` past an explicit threshold contains a prime. -/
theorem exists_prime_log_window {η : ℝ} (hη : 0 < η) :
    ∃ R₀ : ℝ, ∀ y : ℝ, R₀ ≤ y →
      ∃ p : ℕ, p.Prime ∧ y ≤ Real.log p ∧ Real.log p ≤ y + η := by
  have hexpη1 : 1 < Real.exp η := by linarith [Real.add_one_le_exp η]
  have hD0 : 0 < Real.exp η - 1 := by linarith
  have hεw0 : 0 < (Real.exp η - 1) / (8 * Real.exp η) :=
    div_pos hD0 (by positivity)
  obtain ⟨x₀, hx₀⟩ := chebyshevTheta_remainder_eventually_le hεw0
  refine ⟨max (Real.log ((x₀ : ℝ) + 1))
    (Real.log (2 / (Real.exp η - 1))), fun y hy => ?_⟩
  have hey0 : 0 < Real.exp y := Real.exp_pos y
  have hey1 : (x₀ : ℝ) + 1 ≤ Real.exp y := by
    have h1 : Real.log ((x₀ : ℝ) + 1) ≤ y :=
      le_trans (le_max_left _ _) hy
    have h2 := Real.exp_le_exp.2 h1
    rwa [Real.exp_log (by positivity)] at h2
  have hey2 : 2 / (Real.exp η - 1) ≤ Real.exp y := by
    have h1 : Real.log (2 / (Real.exp η - 1)) ≤ y :=
      le_trans (le_max_right _ _) hy
    have h2 := Real.exp_le_exp.2 h1
    rwa [Real.exp_log (by positivity)] at h2
  have hDe : 2 ≤ Real.exp y * (Real.exp η - 1) := by
    rw [div_le_iff₀ hD0] at hey2
    linarith
  have ha1 : 1 ≤ ⌈Real.exp y⌉₊ := Nat.ceil_pos.2 hey0
  have haR : Real.exp y ≤ (⌈Real.exp y⌉₊ : ℝ) := Nat.le_ceil _
  have haR' : (⌈Real.exp y⌉₊ : ℝ) < Real.exp y + 1 :=
    Nat.ceil_lt_add_one hey0.le
  have hbR : (⌊Real.exp (y + η)⌋₊ : ℝ) ≤ Real.exp (y + η) :=
    Nat.floor_le (by positivity)
  have hbR' : Real.exp (y + η) < (⌊Real.exp (y + η)⌋₊ : ℝ) + 1 :=
    Nat.lt_floor_add_one _
  have hexpadd : Real.exp (y + η) = Real.exp y * Real.exp η :=
    Real.exp_add y η
  have hcastm : ((⌈Real.exp y⌉₊ - 1 : ℕ) : ℝ) = (⌈Real.exp y⌉₊ : ℝ) - 1 := by
    rw [Nat.cast_sub ha1, Nat.cast_one]
  have hmb : ⌈Real.exp y⌉₊ - 1 < ⌊Real.exp (y + η)⌋₊ := by
    have h1 : ((⌈Real.exp y⌉₊ - 1 : ℕ) : ℝ) < Real.exp y := by
      rw [hcastm]
      linarith
    have h2 : Real.exp y + 1 ≤ (⌊Real.exp (y + η)⌋₊ : ℝ) + 1 := by
      nlinarith [hbR', hDe, hexpadd]
    have h3 : ((⌈Real.exp y⌉₊ - 1 : ℕ) : ℝ) < (⌊Real.exp (y + η)⌋₊ : ℝ) := by
      linarith
    exact_mod_cast h3
  have hmx₀ : x₀ ≤ ⌈Real.exp y⌉₊ - 1 := by
    have h1 : (x₀ : ℝ) ≤ ((⌈Real.exp y⌉₊ - 1 : ℕ) : ℝ) := by
      rw [hcastm]
      linarith
    exact_mod_cast h1
  have hbx₀ : x₀ ≤ ⌊Real.exp (y + η)⌋₊ := le_trans hmx₀ (le_of_lt hmb)
  have hθm := abs_le.1 (hx₀ (⌈Real.exp y⌉₊ - 1) hmx₀)
  have hθb := abs_le.1 (hx₀ ⌊Real.exp (y + η)⌋₊ hbx₀)
  -- the window carries positive `θ`-mass
  have hbm : Real.exp y * (Real.exp η - 1) / 2
      ≤ (⌊Real.exp (y + η)⌋₊ : ℝ) - ((⌈Real.exp y⌉₊ - 1 : ℕ) : ℝ) := by
    rw [hcastm]
    nlinarith [hbR', haR', hDe, hexpadd]
  have hbm2 : (⌊Real.exp (y + η)⌋₊ : ℝ) + ((⌈Real.exp y⌉₊ - 1 : ℕ) : ℝ)
      ≤ 2 * Real.exp y * Real.exp η := by
    rw [hcastm]
    have h1 : Real.exp y ≤ Real.exp y * Real.exp η := by
      nlinarith [hey0, hexpη1]
    nlinarith [haR', hbR, hexpadd, h1]
  have hεbm : (Real.exp η - 1) / (8 * Real.exp η)
        * ((⌊Real.exp (y + η)⌋₊ : ℝ) + ((⌈Real.exp y⌉₊ - 1 : ℕ) : ℝ))
      ≤ Real.exp y * (Real.exp η - 1) / 4 := by
    have h1 := mul_le_mul_of_nonneg_left hbm2 hεw0.le
    have h2 : (Real.exp η - 1) / (8 * Real.exp η)
        * (2 * Real.exp y * Real.exp η)
        = Real.exp y * (Real.exp η - 1) / 4 := by
      field_simp
      ring
    linarith
  have hpos : 0 < Chebyshev.theta ↑⌊Real.exp (y + η)⌋₊
      - Chebyshev.theta ↑(⌈Real.exp y⌉₊ - 1) := by
    have h2 := hθb.1
    have h3 := hθm.2
    -- θ(b) ≥ b − ε·b, θ(m) ≤ m + ε·m, so the gap is at least
    -- (b − m) − ε(b + m) ≥ D·e^y/2 − D·e^y/4 = D·e^y/4 ≥ 1/2.
    nlinarith [h2, h3, hbm, hεbm, hDe]
  have hwin := theta_window_eq (le_of_lt hmb)
  rw [hwin] at hpos
  have hne : ((Finset.Ioc (⌈Real.exp y⌉₊ - 1) ⌊Real.exp (y + η)⌋₊).filter
      Nat.Prime).Nonempty := by
    by_contra h
    rw [Finset.not_nonempty_iff_eq_empty] at h
    rw [h, Finset.sum_empty] at hpos
    exact lt_irrefl 0 hpos
  obtain ⟨p, hp⟩ := hne
  rw [Finset.mem_filter, Finset.mem_Ioc] at hp
  refine ⟨p, hp.2, ?_, ?_⟩
  · have hpa : ⌈Real.exp y⌉₊ ≤ p := by omega
    have h1 : Real.exp y ≤ (p : ℝ) :=
      le_trans haR (by exact_mod_cast hpa)
    have h2 := Real.log_le_log hey0 h1
    rwa [Real.log_exp] at h2
  · have h1 : (p : ℝ) ≤ Real.exp (y + η) :=
      le_trans (by exact_mod_cast hp.1.2) hbR
    have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.2.pos
    have h2 := Real.log_le_log hp0 h1
    rwa [Real.log_exp] at h2

/-- **Unconditional separated prime-log node families**: for every `N`,
all unit intervals far enough right carry `N + 1` prime logarithms with
pairwise separation `1/(4(N+1))`. -/
theorem exists_separated_primeLog_nodes_unconditional (N : ℕ) :
    ∃ R₀ : ℝ, ∀ R : ℝ, R₀ ≤ R →
      ∃ s : Finset ℝ, s.card = N + 1 ∧ ↑s ⊆ Set.Icc R (R + 1) ∧
        (∀ t ∈ s, ∀ u ∈ s, t ≠ u → 1 / (4 * ((N : ℝ) + 1)) ≤ |t - u|) ∧
        (∀ t ∈ s, ∃ p : ℕ, p.Prime ∧ t = Real.log p) := by
  obtain ⟨R₀, hR₀⟩ := exists_prime_log_window
    (show (0 : ℝ) < 1 / (4 * ((N : ℝ) + 1)) by positivity)
  refine ⟨R₀, fun R hR => ?_⟩
  apply exists_separated_primeLog_nodes
  intro i
  apply hR₀
  have h1 : (0 : ℝ) ≤ 4 * (1 / (4 * ((N : ℝ) + 1))) * (i : ℕ) := by
    positivity
  linarith

end RHTower
