import GaloisForLFunctions.RHTower.PsiRatioRecursionStep
import GaloisForLFunctions.HTGeometry.SqrtLogLinearDomination

/-!
# The single-pass ψ-ratio improvement

If `|R(t)| ≤ a·t` holds from some floor on and the parameters
`δ, ρ, κ, Q, x₁` satisfy the window-geometry constraints with
`ε' = δ + ρ(log(1/ρ)+3) + κ < a`, then eventually

`|R(N)| ≤ (a − θ/2 + 12a/x₁)·N`,   `θ = (a − ε')·ρ/(8·log(2Q))`.

The recursion step is instantiated at the `N`-dependent cutoff
`c(N) = ⌈2Q·(S(N)+2)⌉` with
`S(N) = 2/ρ + x₀ + (16/κ)⁴ + (2/κ)(log N + 1) + 2`, so every width,
floor, and junk hypothesis holds by construction; `c(N) = O(log N)`
keeps `c(N)·x₁ ≤ N` and the recursion constant
`C(N) = O(√log N)` below `(θ/2)·log N` past an explicit threshold, so
half the contraction survives the division by `log²N`.
-/

noncomputable section

namespace RHTower

open ArithmeticFunction Finset

/-- `log x ≤ 2√x` for `0 < x`. -/
theorem log_le_two_sqrt {x : ℝ} (hx : 0 < x) :
    Real.log x ≤ 2 * Real.sqrt x := by
  have h1 : Real.log (Real.sqrt x) = Real.log x / 2 :=
    Real.log_sqrt hx.le
  have h2 : Real.log (Real.sqrt x) ≤ Real.sqrt x - 1 :=
    Real.log_le_sub_one_of_pos (Real.sqrt_pos.2 hx)
  rw [h1] at h2
  have h3 : 0 ≤ Real.sqrt x := Real.sqrt_nonneg x
  linarith

/-- Subadditivity of the square root. -/
theorem sqrt_add_le_add_sqrt {u v : ℝ} (hu : 0 ≤ u) (hv : 0 ≤ v) :
    Real.sqrt (u + v) ≤ Real.sqrt u + Real.sqrt v := by
  rw [show Real.sqrt u + Real.sqrt v
      = Real.sqrt ((Real.sqrt u + Real.sqrt v) ^ 2) from
      (Real.sqrt_sq (by positivity)).symm]
  apply Real.sqrt_le_sqrt
  nlinarith [Real.sq_sqrt hu, Real.sq_sqrt hv,
    mul_nonneg (Real.sqrt_nonneg u) (Real.sqrt_nonneg v)]

/-- The natural logarithm eventually exceeds any bound. -/
theorem exists_nat_log_ge (y : ℝ) :
    ∃ M : ℕ, ∀ N : ℕ, M ≤ N → y ≤ Real.log N := by
  refine ⟨⌈Real.exp y⌉₊ + 1, fun N hN => ?_⟩
  have h1 : Real.exp y ≤ (N : ℝ) := by
    have h2 : Real.exp y ≤ (⌈Real.exp y⌉₊ : ℝ) := Nat.le_ceil _
    have h3 : ((⌈Real.exp y⌉₊ + 1 : ℕ) : ℝ) ≤ (N : ℝ) := by
      exact_mod_cast hN
    push_cast at h3
    linarith
  have h4 := Real.log_le_log (Real.exp_pos y) h1
  rwa [Real.log_exp] at h4

set_option maxHeartbeats 3200000 in
/-- **Single-pass ratio improvement.** -/
theorem psi_ratio_improve {a δ ρ κ : ℝ} {Q x₀ x₁ : ℕ}
    (ha : 0 < a) (hδ : 0 < δ) (hρ0 : 0 < ρ) (hρ1 : ρ ≤ 1 / 2)
    (hκ0 : 0 < κ) (hQ1 : 1 ≤ Q) (hQ : 40 / δ + 2 < Real.log Q)
    (hx₁8 : 8 ≤ x₁) (hx₁ρ : 8 / ρ ≤ (x₁ : ℝ))
    (hx₁Q : Real.log ((2 * Q : ℕ) : ℝ) + 2 ≤ 2 * Real.log x₁)
    (hε'a : δ + ρ * (Real.log (1 / ρ) + 3) + κ < a)
    (hratio : ∀ t : ℕ, x₀ ≤ t → |psiRemainder t| ≤ a * t) :
    ∃ x₀' : ℕ, ∀ N : ℕ, x₀' ≤ N →
      |psiRemainder N| ≤ (a - (a - (δ + ρ * (Real.log (1 / ρ) + 3) + κ))
          * ρ / (16 * Real.log ((2 * Q : ℕ) : ℝ)) + 12 * a / x₁) * N := by
  set ε' : ℝ := δ + ρ * (Real.log (1 / ρ) + 3) + κ with hε'
  set L : ℝ := Real.log ((2 * Q : ℕ) : ℝ) with hL
  set θ : ℝ := (a - ε') * ρ / (8 * L) with hθ
  have hLhalf : 1 / 2 ≤ L := by
    have h1 : Real.log 2 ≤ L := by
      rw [hL]
      apply Real.log_le_log (by norm_num)
      exact_mod_cast (by omega : 2 ≤ 2 * Q)
    linarith [Real.log_two_gt_d9]
  have hL0 : 0 < L := by linarith
  have hθpos : 0 < θ := by
    rw [hθ]
    exact div_pos (mul_pos (by linarith) hρ0) (by linarith)
  have hx₁0 : 0 < x₁ := by omega
  have hx₁R : (0 : ℝ) < x₁ := by exact_mod_cast hx₁0
  have hQR : (1 : ℝ) ≤ (Q : ℝ) := by exact_mod_cast hQ1
  have hlogx₁0 : 0 ≤ Real.log x₁ :=
    Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ x₁))
  have hGx₁0 : 0 ≤ Real.log x₁ ^ 2 + 2 * Real.log x₁ := by positivity
  -- the growth constants of the cutoff
  set B₁ : ℝ := 2 / ρ + (x₀ : ℝ) + (16 / κ) ^ 4 + 4 + 2 / κ with hB₁
  set K₁ : ℝ := 2 * (Q : ℝ) * B₁ + 1 with hK₁
  set K₂ : ℝ := 2 * (Q : ℝ) * (2 / κ) with hK₂
  have hx₀0R : (0 : ℝ) ≤ (x₀ : ℝ) := Nat.cast_nonneg x₀
  have hB₁0 : 0 < B₁ := by
    rw [hB₁]
    have h1 : 0 < 2 / ρ := by positivity
    have h2 : (0 : ℝ) < (16 / κ) ^ 4 := by positivity
    have h3 : 0 < 2 / κ := by positivity
    linarith
  have hK₁1 : 1 ≤ K₁ := by
    rw [hK₁]
    nlinarith [hB₁0, hQR]
  have hK₂0 : 0 < K₂ := by
    rw [hK₂]
    positivity
  set K₃ : ℝ := 80 * a + 8 * (Real.log x₁ ^ 2 + 2 * Real.log x₁) + 8466
    + 64 * Real.sqrt K₁ with hK₃
  set K₄ : ℝ := 64 * Real.sqrt K₂ with hK₄
  have hK₃0 : 0 < K₃ := by
    rw [hK₃]
    have := Real.sqrt_nonneg K₁
    nlinarith [hGx₁0, ha]
  have hK₄0 : 0 < K₄ := by
    rw [hK₄]
    have := Real.sqrt_pos.2 hK₂0
    linarith
  -- thresholds
  obtain ⟨M₁, hM₁⟩ := exists_nat_log_ge 1
  obtain ⟨M₂, hM₂⟩ := exists_nat_log_ge (max (4 * K₃ / θ) ((4 * K₄ / θ) ^ 2))
  set x₀' : ℕ := max (max M₁ M₂)
    (max (⌈2 * (x₁ : ℝ) * K₁⌉₊ + 1) (⌈(4 * (x₁ : ℝ) * K₂) ^ 2⌉₊ + 1))
    with hx₀'def
  refine ⟨x₀', fun N hN => ?_⟩
  have hNM₁ : M₁ ≤ N :=
    le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hN
  have hNM₂ : M₂ ≤ N :=
    le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hN
  have hNA : ⌈2 * (x₁ : ℝ) * K₁⌉₊ + 1 ≤ N :=
    le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hN
  have hNB : ⌈(4 * (x₁ : ℝ) * K₂) ^ 2⌉₊ + 1 ≤ N :=
    le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hN
  have hN0 : 0 < N := by omega
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN0
  have hlogN1 : 1 ≤ Real.log N := hM₁ N hNM₁
  have hlogN0 : 0 ≤ Real.log N := by linarith
  have hy₂ := hM₂ N hNM₂
  have hNK₁ : 2 * (x₁ : ℝ) * K₁ ≤ (N : ℝ) := by
    have h1 : 2 * (x₁ : ℝ) * K₁ ≤ (⌈2 * (x₁ : ℝ) * K₁⌉₊ : ℝ) :=
      Nat.le_ceil _
    have h2 : ((⌈2 * (x₁ : ℝ) * K₁⌉₊ + 1 : ℕ) : ℝ) ≤ (N : ℝ) := by
      exact_mod_cast hNA
    push_cast at h2
    linarith
  have hNK₂sq : (4 * (x₁ : ℝ) * K₂) ^ 2 ≤ (N : ℝ) := by
    have h1 : (4 * (x₁ : ℝ) * K₂) ^ 2
        ≤ (⌈(4 * (x₁ : ℝ) * K₂) ^ 2⌉₊ : ℝ) := Nat.le_ceil _
    have h2 : ((⌈(4 * (x₁ : ℝ) * K₂) ^ 2⌉₊ + 1 : ℕ) : ℝ) ≤ (N : ℝ) := by
      exact_mod_cast hNB
    push_cast at h2
    linarith
  -- the N-dependent cutoff
  set S : ℝ := 2 / ρ + (x₀ : ℝ) + (16 / κ) ^ 4 + (2 / κ) * (Real.log N + 1)
    + 2 with hS
  have hSc : 0 ≤ (2 / κ) * (Real.log N + 1) :=
    mul_nonneg (by positivity) (by linarith)
  have hS2 : 2 ≤ S := by
    rw [hS]
    have h1 : 0 < 2 / ρ := by positivity
    have h2 : (0 : ℝ) < (16 / κ) ^ 4 := by positivity
    linarith
  set c : ℕ := ⌈2 * (Q : ℝ) * (S + 2)⌉₊ with hcdef
  have hcR : 2 * (Q : ℝ) * (S + 2) ≤ (c : ℝ) := Nat.le_ceil _
  have hcR' : (c : ℝ) ≤ 2 * (Q : ℝ) * (S + 2) + 1 := by
    have h1 := Nat.ceil_lt_add_one
      (show (0 : ℝ) ≤ 2 * (Q : ℝ) * (S + 2) by nlinarith [hS2, hQR])
    rw [hcdef]
    linarith
  have hcQ : S + 1 ≤ (c : ℝ) / (2 * Q) - 1 := by
    rw [le_sub_iff_add_le, le_div_iff₀ (by linarith : (0 : ℝ) < 2 * (Q : ℝ))]
    nlinarith [hcR]
  -- instantiation hypotheses for the recursion step
  have hc8 : 8 * Q ≤ c := by
    have h2 : ((8 * Q : ℕ) : ℝ) ≤ (c : ℝ) := by
      push_cast
      nlinarith [hcR, hS2, hQR]
    exact_mod_cast h2
  have hcomp1 : 2 / ρ ≤ S := by
    rw [hS]
    have h2 : (0 : ℝ) < (16 / κ) ^ 4 := by positivity
    linarith
  have hcomp2 : (x₀ : ℝ) ≤ S := by
    rw [hS]
    have h1 : 0 < 2 / ρ := by positivity
    have h2 : (0 : ℝ) < (16 / κ) ^ 4 := by positivity
    linarith
  have hcomp3 : (16 / κ) ^ 4 ≤ S := by
    rw [hS]
    have h1 : 0 < 2 / ρ := by positivity
    linarith
  have hcomp4 : (2 / κ) * (Real.log N + 1) ≤ S := by
    rw [hS]
    have h1 : 0 < 2 / ρ := by positivity
    have h2 : (0 : ℝ) < (16 / κ) ^ 4 := by positivity
    linarith
  have hρc : 2 / ρ ≤ (c : ℝ) / (2 * Q) - 1 := by linarith
  have hx₀c : (x₀ : ℝ) ≤ (c : ℝ) / (2 * Q) - 1 := by linarith
  have hjunkc : ∀ t : ℕ, (c : ℝ) / (2 * Q) - 1 ≤ (t : ℝ) →
      Real.log N + 1 + 2 * Real.sqrt t * Real.log t ≤ κ * t := by
    intro t ht
    exact HTGeometry.add_two_sqrt_mul_log_le_of_threshold hκ0
      (by linarith) (by linarith) (t : ℝ) ht
  -- `c ≤ K₁ + K₂·log N` and `c·x₁ ≤ N`
  have hcup : (c : ℝ) ≤ K₁ + K₂ * Real.log N := by
    have hid : 2 * (Q : ℝ) * (S + 2) + 1 = K₁ + K₂ * Real.log N := by
      rw [hS, hK₁, hK₂, hB₁]
      ring
    linarith
  have hcx₁N : c * x₁ ≤ N := by
    have hstep : (c : ℝ) * (x₁ : ℝ)
        ≤ (x₁ : ℝ) * K₁ + (x₁ : ℝ) * K₂ * Real.log N := by
      have h1 := mul_le_mul_of_nonneg_right hcup hx₁R.le
      nlinarith [h1]
    have h4K : 4 * (x₁ : ℝ) * K₂ ≤ Real.sqrt N := by
      have h1 := Real.sqrt_le_sqrt hNK₂sq
      rwa [Real.sqrt_sq (by positivity)] at h1
    have hlog2s : Real.log N ≤ 2 * Real.sqrt N :=
      log_le_two_sqrt hNR
    have hs2 : (x₁ : ℝ) * K₂ * Real.log N
        ≤ (x₁ : ℝ) * K₂ * (2 * Real.sqrt N) :=
      mul_le_mul_of_nonneg_left hlog2s (by positivity)
    have hNs : Real.sqrt N * Real.sqrt N = (N : ℝ) :=
      Real.mul_self_sqrt (Nat.cast_nonneg N)
    have hs3 : (x₁ : ℝ) * K₂ * (2 * Real.sqrt N) ≤ (N : ℝ) / 2 := by
      nlinarith [mul_le_mul_of_nonneg_right h4K
        (Real.sqrt_nonneg (N : ℝ)), hNs]
    have h5 : (c : ℝ) * (x₁ : ℝ) ≤ (N : ℝ) := by linarith
    have h6 : ((c * x₁ : ℕ) : ℝ) ≤ (N : ℝ) := by
      push_cast
      linarith
    exact_mod_cast h6
  -- the recursion step at the constructed cutoff
  have hD := psi_ratio_recursion_step ha hδ hρ0 hρ1 hκ0.le hQ1 hQ hx₁8
    hx₁ρ hx₁Q (le_of_lt hε'a) hratio hc8 hρc hx₀c hcx₁N hjunkc
  rw [← hε', ← hL, ← hθ] at hD
  -- the recursion constant sits below `(θ/2)·log N`
  have hc0R : (0 : ℝ) < c := by
    have : (2 : ℝ) ≤ 2 * (Q : ℝ) * (S + 2) := by nlinarith [hS2, hQR]
    linarith [hcR]
  have hlogc : Real.log c
      ≤ 2 * Real.sqrt K₁ + 2 * (Real.sqrt K₂ * Real.sqrt (Real.log N)) := by
    have h1 := log_le_two_sqrt hc0R
    have h2 : Real.sqrt c ≤ Real.sqrt (K₁ + K₂ * Real.log N) :=
      Real.sqrt_le_sqrt hcup
    have h3 : Real.sqrt (K₁ + K₂ * Real.log N)
        ≤ Real.sqrt K₁ + Real.sqrt (K₂ * Real.log N) :=
      sqrt_add_le_add_sqrt (by linarith) (mul_nonneg hK₂0.le hlogN0)
    have h4 : Real.sqrt (K₂ * Real.log N)
        = Real.sqrt K₂ * Real.sqrt (Real.log N) :=
      Real.sqrt_mul hK₂0.le _
    rw [h4] at h3
    linarith
  have hCK : 80 * a + 32 * Real.log c
      + 8 * (Real.log x₁ ^ 2 + 2 * Real.log x₁) + 8466
      ≤ K₃ + K₄ * Real.sqrt (Real.log N) := by
    rw [hK₃, hK₄]
    linarith [hlogc]
  have hR2a : K₃ ≤ θ / 4 * Real.log N := by
    have h1 : 4 * K₃ / θ ≤ Real.log N :=
      le_trans (le_max_left _ _) hy₂
    rw [div_le_iff₀ hθpos] at h1
    linarith
  have hR2b : K₄ * Real.sqrt (Real.log N) ≤ θ / 4 * Real.log N := by
    have h1 : (4 * K₄ / θ) ^ 2 ≤ Real.log N :=
      le_trans (le_max_right _ _) hy₂
    have h2 : 4 * K₄ / θ ≤ Real.sqrt (Real.log N) := by
      have h3 := Real.sqrt_le_sqrt h1
      rwa [Real.sqrt_sq (by positivity)] at h3
    have h3 : 4 * K₄ ≤ θ * Real.sqrt (Real.log N) := by
      rw [div_le_iff₀ hθpos] at h2
      linarith
    have huu : Real.sqrt (Real.log N) * Real.sqrt (Real.log N)
        = Real.log N := Real.mul_self_sqrt hlogN0
    nlinarith [mul_le_mul_of_nonneg_right h3
      (Real.sqrt_nonneg (Real.log N)), huu]
  have hCθ : 80 * a + 32 * Real.log c
      + 8 * (Real.log x₁ ^ 2 + 2 * Real.log x₁) + 8466
      ≤ θ / 2 * Real.log N := by linarith
  -- divide the recursion step by `log²N`
  have hlog2pos : (0 : ℝ) < Real.log N ^ 2 := by positivity
  have h1 : (80 * a + 32 * Real.log c
        + 8 * (Real.log x₁ ^ 2 + 2 * Real.log x₁) + 8466)
        * (N : ℝ) * Real.log N
      ≤ θ / 2 * (N : ℝ) * Real.log N ^ 2 := by
    have h2 := mul_le_mul_of_nonneg_right hCθ
      (by positivity : (0 : ℝ) ≤ (N : ℝ) * Real.log N)
    nlinarith [h2]
  have hkey : |psiRemainder N| * Real.log N ^ 2
      ≤ ((a - θ + 12 * a / x₁) * N + θ / 2 * N) * Real.log N ^ 2 := by
    have hexp : ((a - θ + 12 * a / x₁) * (N : ℝ) + θ / 2 * N)
          * Real.log N ^ 2
        = (a - θ + 12 * a / x₁) * (N : ℝ) * Real.log N ^ 2
          + θ / 2 * (N : ℝ) * Real.log N ^ 2 := by
      ring
    rw [hexp]
    linarith [hD, h1]
  have hfin : |psiRemainder N|
      ≤ (a - θ + 12 * a / x₁) * N + θ / 2 * N :=
    le_of_mul_le_mul_right hkey hlog2pos
  have hhalf : (a - θ + 12 * a / x₁) * (N : ℝ) + θ / 2 * N
      = (a - (a - ε') * ρ / (16 * L) + 12 * a / x₁) * N := by
    rw [hθ]
    field_simp
    ring
  linarith [hfin, le_of_eq hhalf]

end RHTower
