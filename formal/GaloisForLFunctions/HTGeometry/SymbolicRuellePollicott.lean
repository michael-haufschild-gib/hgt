import GaloisForLFunctions.HTGeometry.SymbolicQuasiCompactness

/-!
# The Ruelle–Pollicott continuation for Hölder suspensions of mixing subshifts

Let `φ ≥ r_min > 0` be a Hölder roof on a mixing subshift of finite type whose periodic-orbit sums
`Z_n(σ) = Σ_{σⁿp = p} e^{−σ φⁿ(p)}` satisfy `Σ Z_n(σ)/n < ∞` for every `σ > 1`.  Then there are
`ε > 0` and a function `F` holomorphic on `Re s > 1 − ε` with

  `F(s) = exp(−Σ_{n≥1} Z_n(s)/n)` for `Re s > 1`

(`exists_holomorphic_reciprocal`).  `F` is glued (`exists_continuation`) from the local values
`det(1 − L_s|_W) exp(−Σ (Z_n(s) − tr(L_sⁿ|_W))/n)` of the transfer operator on the Hölder space.
The defects are summable by the **local trace estimate** (`local_trace_estimate`): with the level
`m = ⌊n/q⌋ + m₂`,

  `Z_n − tr(Lⁿ|_W) = (Z_n − Z_n^{(m)}) + R_n^{(m)} + (tr(L_mⁿ|_{W_m}) − tr(Lⁿ|_W))`,

where the three terms are `O(n θ^m e^{nκ})`, `O(k^m ρⁿ)` and `O(n e^{nκ} (θ/ϑ)^m)`, all
`O(n τ^{⌊n/q⌋})` with `τ < 1`.
-/

namespace GaloisForLFunctions.HTGeometry.Symbolic

open Metric Filter Topology FiniteRank Module

noncomputable section

variable {k : ℕ} {A : Fin k → Fin k → Prop}

/-- `K cᴺ < aᴺ` for all large `N` when `0 ≤ c < a`. -/
theorem eventually_mul_pow_lt {c a : ℝ} (hc0 : 0 ≤ c) (hca : c < a) (K : ℝ) :
    ∀ᶠ N : ℕ in atTop, K * c ^ N < a ^ N := by
  have ha : 0 < a := lt_of_le_of_lt hc0 hca
  have hq0 : 0 ≤ c / a := div_nonneg hc0 ha.le
  have hq1 : c / a < 1 := (div_lt_one ha).mpr hca
  have ht : Tendsto (fun N : ℕ => |K| * (c / a) ^ N) atTop (𝓝 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hq0 hq1).const_mul |K|
  filter_upwards [ht.eventually (gt_mem_nhds one_pos)] with N hN
  have hpow : 0 < a ^ N := pow_pos ha N
  calc K * c ^ N ≤ |K| * c ^ N := mul_le_mul_of_nonneg_right (le_abs_self K) (pow_nonneg hc0 N)
    _ = |K| * (c / a) ^ N * a ^ N := by rw [div_pow, mul_assoc, div_mul_cancel₀ _ hpow.ne']
    _ < 1 * a ^ N := mul_lt_mul_of_pos_right hN hpow
    _ = a ^ N := one_mul _

/-- `e^{nκ} ≤ e^{qκ} (e^{qκ})^{⌊n/q⌋}`. -/
theorem exp_mul_le_pow_div {κ : ℝ} (hκ : 0 ≤ κ) {q : ℕ} (hq : 1 ≤ q) (n : ℕ) :
    Real.exp (n * κ) ≤ Real.exp (q * κ) * Real.exp (q * κ) ^ (n / q) := by
  rw [← Real.exp_nat_mul, ← Real.exp_add]
  refine Real.exp_le_exp.mpr ?_
  have h := Nat.lt_div_mul_add (a := n) (b := q) (by omega)
  have h' : (n : ℝ) ≤ (n / q : ℕ) * q + q := by exact_mod_cast h.le
  nlinarith

/-- `x^m ≤ x^{⌊n/q⌋}` for `0 ≤ x ≤ 1` and `m ≥ ⌊n/q⌋`. -/
theorem pow_le_pow_div {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) {m n q : ℕ} (hm : n / q ≤ m) :
    x ^ m ≤ x ^ (n / q) := pow_le_pow_of_le_one hx0 hx1 hm

section Estimate

variable {ϑ : ℝ} (hϑ : 0 < ϑ) (hϑ1 : ϑ ≤ 1) {φ : (ℕ → Fin k) → ℝ} {R₀ C θ : ℝ}
  (hφ : IsHolderPotential A φ R₀ C θ) (hC : 0 ≤ C) (hθ0 : 0 ≤ θ) (hθϑ : θ ≤ ϑ) (hθ1 : θ < 1)

include hϑ hϑ1 hφ hC hθ0 hθϑ hθ1 in
/-- **The level-`m` periodic sum versus the outer trace of `L_s`**:
`|Z_n^{(m)} − tr(L_sⁿ|_W)| ≤ k^m ρ^{n+1} 4Λ₀ + 2r (n K₁² e^{nκ} + 8 ρ^{n+1} Λ₀²) ‖L_m − L‖`. -/
theorem levelSum_sub_outerTrace_le (s : ℂ) {ρ Λ₀ : ℝ} (hρ : 0 < ρ) {m n : ℕ} [NeZero n]
    (hm : 2 ≤ m) (hmn : m ≤ n + 1)
    (hT : ∀ w ∈ sphere (0 : ℂ) ρ, w ∈ resolventSet ℂ (transferOp hϑ hϑ1 hφ hC hθ0 hθϑ hθ1 s))
    (hTΛ : ∀ w ∈ sphere (0 : ℂ) ρ,
      ‖resolvent (transferOp hϑ hϑ1 hφ hC hθ0 hθϑ hθ1 s) w‖ ≤ 2 * Λ₀)
    (hTm : ∀ w ∈ sphere (0 : ℂ) ρ, w ∈ resolventSet ℂ (transferOp hϑ hϑ1
      (isHolderPotential_levelPotential hφ hθ0 m) hC hθ0 hθϑ hθ1 s))
    (hTmΛ : ∀ w ∈ sphere (0 : ℂ) ρ, ‖resolvent (transferOp hϑ hϑ1
      (isHolderPotential_levelPotential hφ hθ0 m) hC hθ0 hθϑ hθ1 s) w‖ ≤ 4 * Λ₀)
    (hpert : 2 * ‖transferOp hϑ hϑ1 (isHolderPotential_levelPotential hφ hθ0 m) hC hθ0 hθϑ hθ1 s -
      transferOp hϑ hϑ1 hφ hC hθ0 hθϑ hθ1 s‖ * (2 * Λ₀) ≤ 1)
    {r : ℕ} [FiniteDimensional ℂ (opRange (outerProj (transferOp hϑ hϑ1 hφ hC hθ0 hθϑ hθ1 s) ρ))]
    [FiniteDimensional ℂ (opRange (outerProj (transferOp hϑ hϑ1
      (isHolderPotential_levelPotential hφ hθ0 m) hC hθ0 hθϑ hθ1 s) ρ))]
    (hr : finrank ℂ (opRange (outerProj (transferOp hϑ hϑ1 hφ hC hθ0 hθϑ hθ1 s) ρ)) ≤ r)
    (hr' : finrank ℂ (opRange (outerProj (transferOp hϑ hϑ1
      (isHolderPotential_levelPotential hφ hθ0 m) hC hθ0 hθϑ hθ1 s) ρ)) ≤ r)
    (hrange : ∀ v, outerProj (transferOp hϑ hϑ1 (isHolderPotential_levelPotential hφ hθ0 m) hC hθ0
      hθϑ hθ1 s) ρ v ∈ levelSpace A ϑ (m - 1))
    {K₁ κ : ℝ} (hK₁ : 0 ≤ K₁) (hκ : 0 ≤ κ)
    (hpowT : ∀ i : ℕ, ‖transferOp hϑ hϑ1 hφ hC hθ0 hθϑ hθ1 s ^ i‖ ≤ K₁ * Real.exp (i * κ))
    (hpowTm : ∀ i : ℕ, ‖transferOp hϑ hϑ1 (isHolderPotential_levelPotential hφ hθ0 m) hC hθ0 hθϑ
      hθ1 s ^ i‖ ≤ K₁ * Real.exp (i * κ)) :
    ‖(∑ p ∈ periodicPoints A n, Complex.exp (-(s * birkhoff (levelPotential A φ m) n p))) -
        outerTrace (transferOp hϑ hϑ1 hφ hC hθ0 hθϑ hθ1 s) ρ n‖ ≤
      k ^ m * (ρ ^ (n + 1) * (4 * Λ₀)) +
        2 * r * (n * K₁ ^ 2 * Real.exp (n * κ) * ‖transferOp hϑ hϑ1
          (isHolderPotential_levelPotential hφ hθ0 m) hC hθ0 hθϑ hθ1 s -
            transferOp hϑ hϑ1 hφ hC hθ0 hθϑ hθ1 s‖ +
          ρ ^ (n + 1) * (2 * (2 * Λ₀) ^ 2 * ‖transferOp hϑ hϑ1
            (isHolderPotential_levelPotential hφ hθ0 m) hC hθ0 hθϑ hθ1 s -
              transferOp hϑ hϑ1 hφ hC hθ0 hθϑ hθ1 s‖)) := by
  set T := transferOp hϑ hϑ1 hφ hC hθ0 hθϑ hθ1 s
  set Tm := transferOp hϑ hϑ1 (isHolderPotential_levelPotential hφ hθ0 m) hC hθ0 hθϑ hθ1 s
  obtain ⟨R, hR, hRb⟩ := periodicSum_eq_outerTrace_add hϑ hϑ1
    (isHolderPotential_levelPotential hφ hθ0 m) hC hθ0 hθϑ hθ1 (isLocal_levelPotential φ m) hm s
    hρ hTm hTmΛ hrange hmn
  have hAL := norm_outerTrace_sub_le T Tm hρ hT hTΛ hpert hr hr' n
  have hpow := norm_pow_sub_pow_le_of_exp_bound Tm T hK₁ hκ hpowTm hpowT n
  rw [hR]
  calc ‖outerTrace Tm ρ n + R - outerTrace T ρ n‖
      ≤ ‖R‖ + ‖outerTrace Tm ρ n - outerTrace T ρ n‖ := by
        rw [show outerTrace Tm ρ n + R - outerTrace T ρ n =
          R + (outerTrace Tm ρ n - outerTrace T ρ n) by ring]
        exact norm_add_le _ _
    _ ≤ k ^ m * (ρ ^ (n + 1) * (4 * Λ₀)) +
        2 * r * (n * K₁ ^ 2 * Real.exp (n * κ) * ‖Tm - T‖ +
          ρ ^ (n + 1) * (2 * (2 * Λ₀) ^ 2 * ‖Tm - T‖)) := by
        refine add_le_add hRb (hAL.trans ?_)
        gcongr

include hφ hθ0 in
/-- **Changing the potential to its level-`m` approximation changes periodic sums little**:
`|Z_n − Z_n^{(m)}| ≤ Z_n(σ) |s| n C θ^m e^{|s| n C θ^m}`. -/
theorem norm_periodicSum_sub_levelSum_le (s : ℂ) (n m : ℕ) [NeZero n] :
    ‖(∑ p ∈ periodicPoints A n, Complex.exp (-(s * birkhoff φ n p))) -
        ∑ p ∈ periodicPoints A n, Complex.exp (-(s * birkhoff (levelPotential A φ m) n p))‖ ≤
      periodicSumR A φ n s.re *
        (‖s‖ * (n * (C * θ ^ m)) * Real.exp (‖s‖ * (n * (C * θ ^ m)))) := by
  rw [← Finset.sum_sub_distrib, periodicSumR, Finset.sum_mul]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun p hp => ?_)
  have hpa : IsAdmissible A p := (mem_periodicPoints.mp hp).1
  have hclose : ∀ y, IsAdmissible A y → |levelPotential A φ m y - φ y| ≤ C * θ ^ m :=
    fun y hy => abs_levelPotential_sub_le hφ m hy
  have hd := abs_birkhoff_sub_birkhoff_le hclose n hpa
  rw [abs_sub_comm] at hd
  have hC : 0 ≤ C := hφ.const_nonneg hpa
  refine (norm_cexp_neg_mul_sub_le s _ _).trans ?_
  refine mul_le_mul_of_nonneg_left ?_ (Real.exp_pos _).le
  gcongr

end Estimate

/-- First error term: `Z_n(σ) |s| n C θ^m e^{|s| n C θ^m} ≤ c₁ n τ^{⌊n/q⌋}`. -/
theorem defect_arith_first {Zr sn S C θ B ε κ τ : ℝ} {m q n : ℕ} (hmj : n / q ≤ m) (hq : 1 ≤ q)
    (hZr : Zr ≤ B * ε⁻¹ * Real.exp (n * κ)) (hsn : sn ≤ S) (hsn0 : 0 ≤ sn)
    (hSθ : S * C * ((n : ℝ) ^ 1 * θ ^ (n / q)) ≤ 1) (hC : 0 ≤ C) (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1)
    (hκ : 0 ≤ κ) (hB : 0 ≤ B) (hε : 0 < ε) (hτθ : θ * Real.exp (q * κ) ≤ τ) :
    Zr * (sn * (n * (C * θ ^ m)) * Real.exp (sn * (n * (C * θ ^ m)))) ≤
      (B * ε⁻¹ * (S * C * Real.exp 1) * Real.exp (q * κ)) * (n * τ ^ (n / q)) := by
  have hS0 : 0 ≤ S := hsn0.trans hsn
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hE0 : 0 ≤ Real.exp (q * κ) := (Real.exp_pos _).le
  have he1 : θ ^ m ≤ θ ^ (n / q) := pow_le_pow_of_le_one hθ0 hθ1 hmj
  have he3 := exp_mul_le_pow_div hκ hq n
  have h2 : sn * (n * (C * θ ^ m)) ≤ S * C * (n * θ ^ (n / q)) := by
    calc sn * (n * (C * θ ^ m)) ≤ S * (n * (C * θ ^ (n / q))) :=
          mul_le_mul hsn (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left he1 hC) hn0)
            (mul_nonneg hn0 (mul_nonneg hC (pow_nonneg hθ0 _))) hS0
      _ = S * C * (n * θ ^ (n / q)) := by ring
  have hsmall : sn * (n * (C * θ ^ m)) ≤ 1 := h2.trans (by rw [pow_one] at hSθ; exact hSθ)
  have h1 : sn * (n * (C * θ ^ m)) * Real.exp (sn * (n * (C * θ ^ m))) ≤
      S * C * (n * θ ^ (n / q)) * Real.exp 1 :=
    mul_le_mul h2 (Real.exp_le_exp.mpr hsmall) (Real.exp_pos _).le
      (mul_nonneg (mul_nonneg hS0 hC) (mul_nonneg hn0 (pow_nonneg hθ0 _)))
  have hZr0' : 0 ≤ B * ε⁻¹ * (Real.exp (q * κ) * Real.exp (q * κ) ^ (n / q)) :=
    mul_nonneg (mul_nonneg hB (inv_nonneg.mpr hε.le)) (mul_nonneg hE0 (pow_nonneg hE0 _))
  have h4 : (θ * Real.exp (q * κ)) ^ (n / q) ≤ τ ^ (n / q) :=
    pow_le_pow_left₀ (mul_nonneg hθ0 hE0) hτθ _
  have hc : 0 ≤ B * ε⁻¹ * (S * C * Real.exp 1) * n :=
    mul_nonneg (mul_nonneg (mul_nonneg hB (inv_nonneg.mpr hε.le))
      (mul_nonneg (mul_nonneg hS0 hC) (Real.exp_pos 1).le)) hn0
  have hZrle : Zr ≤ B * ε⁻¹ * (Real.exp (q * κ) * Real.exp (q * κ) ^ (n / q)) :=
    hZr.trans (mul_le_mul_of_nonneg_left he3 (mul_nonneg hB (inv_nonneg.mpr hε.le)))
  calc Zr * (sn * (n * (C * θ ^ m)) * Real.exp (sn * (n * (C * θ ^ m))))
      ≤ (B * ε⁻¹ * (Real.exp (q * κ) * Real.exp (q * κ) ^ (n / q))) *
          (S * C * (n * θ ^ (n / q)) * Real.exp 1) :=
        mul_le_mul hZrle h1 (mul_nonneg (mul_nonneg hsn0 (mul_nonneg hn0
          (mul_nonneg hC (pow_nonneg hθ0 _)))) (Real.exp_pos _).le) hZr0'
    _ = (B * ε⁻¹ * (S * C * Real.exp 1)) * n *
          (Real.exp (q * κ) * (θ * Real.exp (q * κ)) ^ (n / q)) := by rw [mul_pow]; ring
    _ ≤ (B * ε⁻¹ * (S * C * Real.exp 1)) * n * (Real.exp (q * κ) * τ ^ (n / q)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h4 hE0) hc
    _ = (B * ε⁻¹ * (S * C * Real.exp 1) * Real.exp (q * κ)) * (n * τ ^ (n / q)) := by ring

/-- Second error term: `k^m ρ^{n+1} 4Λ₀ ≤ k^{m₂} ρ 4Λ₀ τ^{⌊n/q⌋}`. -/
theorem defect_arith_second {Λ₀ ρ τ : ℝ} {k m m₂ q n : ℕ} (hm : m = n / q + m₂)
    (hΛ₀ : 0 ≤ Λ₀) (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1) (hτk : (k : ℝ) * ρ ^ q ≤ τ) :
    (k : ℝ) ^ m * (ρ ^ (n + 1) * (4 * Λ₀)) ≤ (k : ℝ) ^ m₂ * (ρ * (4 * Λ₀)) * τ ^ (n / q) := by
  have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have hρn : ρ ^ (n + 1) ≤ ρ * (ρ ^ q) ^ (n / q) := by
    rw [pow_succ', ← pow_mul]
    exact mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one hρ0 hρ1 (Nat.mul_div_le n q)) hρ0
  have hkρ : ((k : ℝ) * ρ ^ q) ^ (n / q) ≤ τ ^ (n / q) :=
    pow_le_pow_left₀ (mul_nonneg hk0 (pow_nonneg hρ0 q)) hτk _
  calc (k : ℝ) ^ m * (ρ ^ (n + 1) * (4 * Λ₀))
      ≤ (k : ℝ) ^ m * (ρ * (ρ ^ q) ^ (n / q) * (4 * Λ₀)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hρn (by positivity))
          (pow_nonneg hk0 m)
    _ = (k : ℝ) ^ m₂ * (ρ * (4 * Λ₀)) * ((k : ℝ) * ρ ^ q) ^ (n / q) := by
        rw [hm, pow_add, mul_pow]; ring
    _ ≤ (k : ℝ) ^ m₂ * (ρ * (4 * Λ₀)) * τ ^ (n / q) :=
        mul_le_mul_of_nonneg_left hkρ (mul_nonneg (pow_nonneg hk0 _) (by positivity))

/-- Third error term: the comparison of outer traces is `≤ c₃ (n + 1) τ^{⌊n/q⌋}`. -/
theorem defect_arith_third {θ ϑ κ K₁ Λ₀ ρ Δ Pb τ : ℝ} {r m q n : ℕ} (hmj : n / q ≤ m)
    (hq : 1 ≤ q) (hΔ : Δ ≤ 3 * Pb * (θ / ϑ) ^ m) (hΔ0 : 0 ≤ Δ) (hθ0 : 0 ≤ θ) (hϑ : 0 < ϑ)
    (hθϑ : θ ≤ ϑ) (hκ : 0 ≤ κ) (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1)
    (hPb : 0 ≤ Pb) (hτθϑ : θ / ϑ * Real.exp (q * κ) ≤ τ) (hτq : θ / ϑ ≤ τ) :
    2 * r * (n * K₁ ^ 2 * Real.exp (n * κ) * Δ + ρ ^ (n + 1) * (2 * (2 * Λ₀) ^ 2 * Δ)) ≤
      2 * r * (K₁ ^ 2 * (3 * Pb) * Real.exp (q * κ) + 2 * (2 * Λ₀) ^ 2 * (3 * Pb)) *
        ((n : ℝ) + 1) * τ ^ (n / q) := by
  have hq0 : 0 ≤ θ / ϑ := div_nonneg hθ0 hϑ.le
  have hq1 : θ / ϑ ≤ 1 := (div_le_one hϑ).mpr hθϑ
  have hE0 : 0 ≤ Real.exp (q * κ) := (Real.exp_pos _).le
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hτ0 : 0 ≤ τ := hq0.trans hτq
  have hτj : 0 ≤ τ ^ (n / q) := pow_nonneg hτ0 _
  have he2 : (θ / ϑ) ^ m ≤ (θ / ϑ) ^ (n / q) := pow_le_pow_of_le_one hq0 hq1 hmj
  have he3 := exp_mul_le_pow_div hκ hq n
  have hΔj : Δ ≤ 3 * Pb * (θ / ϑ) ^ (n / q) :=
    hΔ.trans (mul_le_mul_of_nonneg_left he2 (by positivity))
  have hf1 : Real.exp (n * κ) * Δ ≤ 3 * Pb * Real.exp (q * κ) * τ ^ (n / q) := by
    calc Real.exp (n * κ) * Δ
        ≤ (Real.exp (q * κ) * Real.exp (q * κ) ^ (n / q)) * (3 * Pb * (θ / ϑ) ^ (n / q)) :=
          mul_le_mul he3 hΔj hΔ0 (mul_nonneg hE0 (pow_nonneg hE0 _))
      _ = 3 * Pb * Real.exp (q * κ) * (θ / ϑ * Real.exp (q * κ)) ^ (n / q) := by
          rw [mul_pow]; ring
      _ ≤ 3 * Pb * Real.exp (q * κ) * τ ^ (n / q) :=
          mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (mul_nonneg hq0 hE0) hτθϑ _)
            (by positivity)
  have hf2 : ρ ^ (n + 1) * Δ ≤ 3 * Pb * τ ^ (n / q) := by
    calc ρ ^ (n + 1) * Δ ≤ 1 * (3 * Pb * (θ / ϑ) ^ (n / q)) :=
          mul_le_mul (pow_le_one₀ hρ0 hρ1) hΔj hΔ0 zero_le_one
      _ ≤ 3 * Pb * τ ^ (n / q) := by
          rw [one_mul]
          exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hq0 hτq _) (by positivity)
  have hr0 : (0 : ℝ) ≤ 2 * r := by positivity
  have h1 : 0 ≤ K₁ ^ 2 * (3 * Pb) * Real.exp (q * κ) := by positivity
  have h2 : 0 ≤ 2 * (2 * Λ₀) ^ 2 * (3 * Pb) := by positivity
  calc 2 * r * (n * K₁ ^ 2 * Real.exp (n * κ) * Δ + ρ ^ (n + 1) * (2 * (2 * Λ₀) ^ 2 * Δ))
      = 2 * r * (n * K₁ ^ 2 * (Real.exp (n * κ) * Δ) +
          2 * (2 * Λ₀) ^ 2 * (ρ ^ (n + 1) * Δ)) := by ring
    _ ≤ 2 * r * (n * K₁ ^ 2 * (3 * Pb * Real.exp (q * κ) * τ ^ (n / q)) +
          2 * (2 * Λ₀) ^ 2 * (3 * Pb * τ ^ (n / q))) := by
        refine mul_le_mul_of_nonneg_left (add_le_add ?_ ?_) hr0
        · exact mul_le_mul_of_nonneg_left hf1 (by positivity)
        · exact mul_le_mul_of_nonneg_left hf2 (by positivity)
    _ = 2 * r * ((K₁ ^ 2 * (3 * Pb) * Real.exp (q * κ)) * n * τ ^ (n / q) +
          (2 * (2 * Λ₀) ^ 2 * (3 * Pb)) * τ ^ (n / q)) := by ring
    _ ≤ 2 * r * ((K₁ ^ 2 * (3 * Pb) * Real.exp (q * κ)) * ((n : ℝ) + 1) * τ ^ (n / q) +
          (2 * (2 * Λ₀) ^ 2 * (3 * Pb)) * ((n : ℝ) + 1) * τ ^ (n / q)) := by
        refine mul_le_mul_of_nonneg_left (add_le_add ?_ ?_) hr0
        · exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (by linarith) h1) hτj
        · have := mul_le_mul_of_nonneg_left (by linarith : (1 : ℝ) ≤ n + 1) h2
          calc 2 * (2 * Λ₀) ^ 2 * (3 * Pb) * τ ^ (n / q)
              = 2 * (2 * Λ₀) ^ 2 * (3 * Pb) * 1 * τ ^ (n / q) := by ring
            _ ≤ 2 * (2 * Λ₀) ^ 2 * (3 * Pb) * ((n : ℝ) + 1) * τ ^ (n / q) :=
                mul_le_mul_of_nonneg_right this hτj
    _ = _ := by ring

/-- **Perturbing an operator with a bounded resolvent on a circle**: a perturbation of size at most
`1/(8Λ₀)` of an operator with resolvent bound `2Λ₀` keeps the circle, with resolvent bound `4Λ₀`. -/
theorem resolvent_bound_of_small_perturb {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [CompleteSpace E] (T T' : E →L[ℂ] E) {ρ Λ₀ : ℝ} (hΛ₀ : 0 < Λ₀)
    (h : ∀ w ∈ sphere (0 : ℂ) ρ, w ∈ resolventSet ℂ T)
    (hb : ∀ w ∈ sphere (0 : ℂ) ρ, ‖resolvent T w‖ ≤ 2 * Λ₀) (hp : ‖T' - T‖ ≤ (8 * Λ₀)⁻¹) :
    (∀ w ∈ sphere (0 : ℂ) ρ, w ∈ resolventSet ℂ T') ∧
      (∀ w ∈ sphere (0 : ℂ) ρ, ‖resolvent T' w‖ ≤ 4 * Λ₀) ∧ 2 * ‖T' - T‖ * (2 * Λ₀) ≤ 1 := by
  have hsmall : 2 * ‖T' - T‖ * (2 * Λ₀) ≤ 1 := by
    have : ‖T' - T‖ * (8 * Λ₀) ≤ 1 := by
      calc ‖T' - T‖ * (8 * Λ₀) ≤ (8 * Λ₀)⁻¹ * (8 * Λ₀) :=
            mul_le_mul_of_nonneg_right hp (by positivity)
        _ = 1 := inv_mul_cancel₀ (by positivity)
    nlinarith [norm_nonneg (T' - T)]
  obtain ⟨h1, h2⟩ := resolvent_bound_of_perturb T T' h hb hsmall
  exact ⟨h1, fun w hw => (h2 w hw).trans (le_of_eq (by ring)), hsmall⟩

section Main

variable {M : ℕ} (hmix : IsMixing A M) (hM : 1 ≤ M) {φ : (ℕ → Fin k) → ℝ} {R₀ C θ : ℝ}
  (hφ : IsHolderPotential A φ R₀ C θ) (hR₀ : 0 ≤ R₀) (hC : 0 ≤ C) (hθ0 : 0 < θ) (hθ1 : θ < 1)
  (hpos : ∀ y, IsAdmissible A y → 0 ≤ φ y) {ϑ : ℝ} (hϑ : 0 < ϑ) (hϑ1 : ϑ ≤ 1) (hθϑ : θ ≤ ϑ)

include hφ hR₀ hC hθ0 hθ1 hϑ hϑ1 hθϑ in
/-- **A neighbourhood on which a circle stays admissible**, with resolvent bound `2Λ₀`. -/
theorem local_neighbourhood {ε : ℝ} {s₀ : ℂ} (hs₀ : 1 - ε < s₀.re) {ρ : ℝ}
    (hρ : ∀ w ∈ sphere (0 : ℂ) ρ, w ∈ resolventSet ℂ (transferOp hϑ hϑ1 hφ hC hθ0.le hθϑ hθ1 s₀)) :
    ∃ δ₀ > 0, ∃ Λ₀ > 0, ∀ s ∈ ball s₀ δ₀, 1 - ε < s.re ∧ ‖s‖ ≤ ‖s₀‖ + δ₀ ∧
      (∀ w ∈ sphere (0 : ℂ) ρ, w ∈ resolventSet ℂ (transferOp hϑ hϑ1 hφ hC hθ0.le hθϑ hθ1 s)) ∧
      ∀ w ∈ sphere (0 : ℂ) ρ,
        ‖resolvent (transferOp hϑ hϑ1 hφ hC hθ0.le hθϑ hθ1 s) w‖ ≤ 2 * Λ₀ := by
  obtain ⟨Λ₀, hΛ₀pos, hΛ₀⟩ :=
    exists_norm_resolvent_le_on_sphere (transferOp hϑ hϑ1 hφ hC hθ0.le hθϑ hθ1 s₀) hρ
  have hTc : ContinuousAt (fun s => transferOp hϑ hϑ1 hφ hC hθ0.le hθϑ hθ1 s) s₀ :=
    (differentiable_transferOp hϑ hϑ1 hφ hC hθ0.le hθϑ hθ1 hR₀ s₀).continuousAt
  have hev1 : ∀ᶠ s in 𝓝 s₀, ‖transferOp hϑ hϑ1 hφ hC hθ0.le hθϑ hθ1 s -
      transferOp hϑ hϑ1 hφ hC hθ0.le hθϑ hθ1 s₀‖ < (4 * Λ₀)⁻¹ := by
    have := (hTc.sub continuousAt_const).norm
      (f := fun s => transferOp hϑ hϑ1 hφ hC hθ0.le hθϑ hθ1 s -
        transferOp hϑ hϑ1 hφ hC hθ0.le hθϑ hθ1 s₀)
    have h0 : ‖transferOp hϑ hϑ1 hφ hC hθ0.le hθϑ hθ1 s₀ -
        transferOp hϑ hϑ1 hφ hC hθ0.le hθϑ hθ1 s₀‖ < (4 * Λ₀)⁻¹ := by
      rw [sub_self, norm_zero]; positivity
    exact this.eventually (gt_mem_nhds h0)
  have hev2 : ∀ᶠ s in 𝓝 s₀, 1 - ε < s.re :=
    (isOpen_lt continuous_const Complex.continuous_re).mem_nhds hs₀
  obtain ⟨δ₀, hδ₀, hball⟩ := Metric.eventually_nhds_iff_ball.mp (hev1.and hev2)
  refine ⟨δ₀, hδ₀, Λ₀, hΛ₀pos, fun s hs => ⟨(hball s hs).2, ?_, ?_⟩⟩
  · have h1 : ‖s - s₀‖ < δ₀ := by rw [← dist_eq_norm]; exact hs
    have h2 := norm_sub_norm_le s s₀
    linarith
  · refine resolvent_bound_of_perturb _ _ hρ hΛ₀ ?_
    have h1 := (hball s hs).1
    have : ‖transferOp hϑ hϑ1 hφ hC hθ0.le hθϑ hθ1 s -
        transferOp hϑ hϑ1 hφ hC hθ0.le hθϑ hθ1 s₀‖ * (4 * Λ₀) < 1 := by
      calc _ < (4 * Λ₀)⁻¹ * (4 * Λ₀) := mul_lt_mul_of_pos_right h1 (by positivity)
        _ = 1 := inv_mul_cancel₀ (by positivity)
    nlinarith

include hφ hC hθ0 hθ1 hϑ hϑ1 hθϑ hR₀ in
/-- **Level potentials perturb the transfer operator by `O((θ/ϑ)^m)`, uniformly on `‖s‖ ≤ S`.** -/
theorem level_perturb_le {S : ℝ} {s : ℂ} (hs : ‖s‖ ≤ S) (m : ℕ) :
    ‖transferOp hϑ hϑ1 (isHolderPotential_levelPotential hφ hθ0.le m) hC hθ0.le hθϑ hθ1 s -
      transferOp hϑ hϑ1 hφ hC hθ0.le hθϑ hθ1 s‖ ≤
      3 * ((k : ℝ) * Real.exp (S * R₀) * (S * C * Real.exp (S * C))) * (θ / ϑ) ^ m := by
  have h := norm_transferOp_sub_le hϑ hϑ1 hφ (isHolderPotential_levelPotential hφ hθ0.le m) hC
    hθ0.le hθϑ hθ1 (fun y hy => abs_levelPotential_sub_le hφ m hy) s
  refine h.trans (mul_le_mul_of_nonneg_right ?_ (pow_nonneg (div_nonneg hθ0.le hϑ.le) m))
  have hre : |s.re| ≤ S := (Complex.abs_re_le_norm s).trans hs
  unfold perturbConst
  have e1 : Real.exp (|s.re| * R₀) ≤ Real.exp (S * R₀) :=
    Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hre hR₀)
  have e2 : ‖s‖ * C * Real.exp (‖s‖ * C) ≤ S * C * Real.exp (S * C) :=
    mul_le_mul (mul_le_mul_of_nonneg_right hs hC)
      (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hs hC)) (Real.exp_pos _).le
      (mul_nonneg ((norm_nonneg s).trans hs) hC)
  have e3 := mul_le_mul e1 e2 (by positivity) (Real.exp_pos _).le
  have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have := mul_le_mul_of_nonneg_left e3 hk
  nlinarith [this]

include hφ hC hθ0 hθ1 hϑ hϑ1 hθϑ hR₀ hpos in
/-- **The refined defect bound at a point**: `|Z_n(s) − tr(L_sⁿ|_W)| ≤ (c₁ + c₂ + c₃)(n + 1)
τ^{⌊n/q⌋}`, comparing with the level `m = ⌊n/q⌋ + m₂`. -/
theorem defect_bound_at {ε B κ S K₁ Λ₀ τ ρ Pb : ℝ} {r m₂ q n : ℕ} [NeZero n] (s : ℂ)
    (hε : 0 < ε) (hB0 : 0 ≤ B)
    (hB : ∀ n : ℕ, periodicSumR A φ (n + 1) (1 + ε) ≤ B * ((n : ℝ) + 1))
    (hεκ : ε * (2 * R₀ + 1) ≤ κ) (hκ0 : 0 ≤ κ) (hs : 1 - ε < s.re) (hsS : ‖s‖ ≤ S)
    (hq : 1 ≤ q) (hm2 : 2 ≤ n / q + m₂) (hmn : n / q + m₂ ≤ n + 1)
    (hSθ : S * C * ((n : ℝ) ^ 1 * θ ^ (n / q)) ≤ 1) (hρ0 : 0 < ρ) (hρ1 : ρ ≤ 1)
    (hΛ₀ : 0 ≤ Λ₀) (hK₁ : 0 ≤ K₁) (hPb : 0 ≤ Pb)
    (hT : ∀ w ∈ sphere (0 : ℂ) ρ, w ∈ resolventSet ℂ (transferOp hϑ hϑ1 hφ hC hθ0.le hθϑ hθ1 s))
    (hTΛ : ∀ w ∈ sphere (0 : ℂ) ρ,
      ‖resolvent (transferOp hϑ hϑ1 hφ hC hθ0.le hθϑ hθ1 s) w‖ ≤ 2 * Λ₀)
    (hTm : ∀ w ∈ sphere (0 : ℂ) ρ, w ∈ resolventSet ℂ (transferOp hϑ hϑ1
      (isHolderPotential_levelPotential hφ hθ0.le (n / q + m₂)) hC hθ0.le hθϑ hθ1 s))
    (hTmΛ : ∀ w ∈ sphere (0 : ℂ) ρ, ‖resolvent (transferOp hϑ hϑ1
      (isHolderPotential_levelPotential hφ hθ0.le (n / q + m₂)) hC hθ0.le hθϑ hθ1 s) w‖ ≤ 4 * Λ₀)
    (hpert : 2 * ‖transferOp hϑ hϑ1 (isHolderPotential_levelPotential hφ hθ0.le (n / q + m₂)) hC
      hθ0.le hθϑ hθ1 s - transferOp hϑ hϑ1 hφ hC hθ0.le hθϑ hθ1 s‖ * (2 * Λ₀) ≤ 1)
    [FiniteDimensional ℂ (opRange (outerProj (transferOp hϑ hϑ1 hφ hC hθ0.le hθϑ hθ1 s) ρ))]
    [FiniteDimensional ℂ (opRange (outerProj (transferOp hϑ hϑ1
      (isHolderPotential_levelPotential hφ hθ0.le (n / q + m₂)) hC hθ0.le hθϑ hθ1 s) ρ))]
    (hr : finrank ℂ (opRange (outerProj (transferOp hϑ hϑ1 hφ hC hθ0.le hθϑ hθ1 s) ρ)) ≤ r)
    (hr' : finrank ℂ (opRange (outerProj (transferOp hϑ hϑ1
      (isHolderPotential_levelPotential hφ hθ0.le (n / q + m₂)) hC hθ0.le hθϑ hθ1 s) ρ)) ≤ r)
    (hrange : ∀ v, outerProj (transferOp hϑ hϑ1 (isHolderPotential_levelPotential hφ hθ0.le
      (n / q + m₂)) hC hθ0.le hθϑ hθ1 s) ρ v ∈ levelSpace A ϑ (n / q + m₂ - 1))
    (hpowT : ∀ i : ℕ, ‖transferOp hϑ hϑ1 hφ hC hθ0.le hθϑ hθ1 s ^ i‖ ≤ K₁ * Real.exp (i * κ))
    (hpowTm : ∀ i : ℕ, ‖transferOp hϑ hϑ1 (isHolderPotential_levelPotential hφ hθ0.le
      (n / q + m₂)) hC hθ0.le hθϑ hθ1 s ^ i‖ ≤ K₁ * Real.exp (i * κ))
    (hΔ : ‖transferOp hϑ hϑ1 (isHolderPotential_levelPotential hφ hθ0.le (n / q + m₂)) hC
      hθ0.le hθϑ hθ1 s - transferOp hϑ hϑ1 hφ hC hθ0.le hθϑ hθ1 s‖ ≤
        3 * Pb * (θ / ϑ) ^ (n / q + m₂))
    (hτθ : θ * Real.exp (q * κ) ≤ τ) (hτθϑ : θ / ϑ * Real.exp (q * κ) ≤ τ) (hτq : θ / ϑ ≤ τ)
    (hτk : (k : ℝ) * ρ ^ q ≤ τ) :
    ‖(∑ p ∈ periodicPoints A n, Complex.exp (-(s * birkhoff φ n p))) -
        outerTrace (transferOp hϑ hϑ1 hφ hC hθ0.le hθϑ hθ1 s) ρ n‖ ≤
      (B * ε⁻¹ * (S * C * Real.exp 1) * Real.exp (q * κ) + (k : ℝ) ^ m₂ * (ρ * (4 * Λ₀)) +
        2 * r * (K₁ ^ 2 * (3 * Pb) * Real.exp (q * κ) + 2 * (2 * Λ₀) ^ 2 * (3 * Pb))) *
          ((n : ℝ) + 1) * τ ^ (n / q) := by
  set m := n / q + m₂ with hmdef
  have hA := norm_periodicSum_sub_levelSum_le hφ hθ0.le s n m
  have hZr : periodicSumR A φ n s.re ≤ B * ε⁻¹ * Real.exp (n * κ) := by
    refine (periodicSumR_le_exp hφ hR₀ hpos hε hB0 hB hs n).trans ?_
    exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr
      (mul_le_mul_of_nonneg_left hεκ (Nat.cast_nonneg n))) (by positivity)
  have hBC := levelSum_sub_outerTrace_le hϑ hϑ1 hφ hC hθ0.le hθϑ hθ1 s hρ0 hm2 hmn hT hTΛ hTm hTmΛ
    hpert hr hr' hrange hK₁ hκ0 hpowT hpowTm
  have h1 := defect_arith_first (m := m) (by omega) hq hZr hsS (norm_nonneg s) hSθ hC hθ0.le
    hθ1.le hκ0 hB0 hε hτθ
  have h2 := defect_arith_second (k := k) (Λ₀ := Λ₀) (n := n) (q := q) (m₂ := m₂) hmdef hΛ₀
    hρ0.le hρ1 hτk
  have h3 := defect_arith_third (r := r) (K₁ := K₁) (Λ₀ := Λ₀) (n := n) (m := m) (by omega) hq hΔ
    (norm_nonneg _) hθ0.le hϑ hθϑ hκ0 hρ0.le hρ1 hPb hτθϑ hτq
  set z := ∑ p ∈ periodicPoints A n, Complex.exp (-(s * birkhoff φ n p))
  set zm := ∑ p ∈ periodicPoints A n, Complex.exp (-(s * birkhoff (levelPotential A φ m) n p))
  have hτ0 : 0 ≤ τ := le_trans (div_nonneg hθ0.le hϑ.le) hτq
  have hτj : 0 ≤ τ ^ (n / q) := pow_nonneg hτ0 _
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hc1 : 0 ≤ B * ε⁻¹ * (S * C * Real.exp 1) * Real.exp (q * κ) := by
    have hS0 : 0 ≤ S := (norm_nonneg s).trans hsS
    exact mul_nonneg (mul_nonneg (mul_nonneg hB0 (inv_nonneg.mpr hε.le))
      (mul_nonneg (mul_nonneg hS0 hC) (Real.exp_pos 1).le)) (Real.exp_pos _).le
  have hc2 : 0 ≤ (k : ℝ) ^ m₂ * (ρ * (4 * Λ₀)) := by positivity
  calc ‖z - outerTrace (transferOp hϑ hϑ1 hφ hC hθ0.le hθϑ hθ1 s) ρ n‖
      ≤ ‖z - zm‖ + ‖zm - outerTrace (transferOp hϑ hϑ1 hφ hC hθ0.le hθϑ hθ1 s) ρ n‖ :=
        norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ ≤ (B * ε⁻¹ * (S * C * Real.exp 1) * Real.exp (q * κ)) * (n * τ ^ (n / q)) +
        ((k : ℝ) ^ m₂ * (ρ * (4 * Λ₀)) * τ ^ (n / q) +
          2 * r * (K₁ ^ 2 * (3 * Pb) * Real.exp (q * κ) + 2 * (2 * Λ₀) ^ 2 * (3 * Pb)) *
            ((n : ℝ) + 1) * τ ^ (n / q)) := by
        refine add_le_add (hA.trans h1) (hBC.trans (add_le_add h2 h3))
    _ ≤ _ := by
        nlinarith [mul_nonneg hc1 hτj, mul_nonneg hc2 hτj, mul_nonneg (mul_nonneg hc2 hn0) hτj]

include hφ hC hθ0 hθ1 hϑ hϑ1 hθϑ hR₀ hpos in
/-- **The crude defect bound at a point**: `|Z_n(s) − tr(L_sⁿ|_W)| ≤ (B/ε + r K₁(1 + 2ρΛ₀))
e^{nκ}`. -/
theorem crude_bound_at {ε B κ K₁ Λ₀ ρ : ℝ} {r n : ℕ} [NeZero n] (s : ℂ) (hε : 0 < ε)
    (hB0 : 0 ≤ B) (hB : ∀ n : ℕ, periodicSumR A φ (n + 1) (1 + ε) ≤ B * ((n : ℝ) + 1))
    (hεκ : ε * (2 * R₀ + 1) ≤ κ) (hs : 1 - ε < s.re) (hρ0 : 0 < ρ) (hK₁ : 0 ≤ K₁)
    (hT : ∀ w ∈ sphere (0 : ℂ) ρ, w ∈ resolventSet ℂ (transferOp hϑ hϑ1 hφ hC hθ0.le hθϑ hθ1 s))
    (hTΛ : ∀ w ∈ sphere (0 : ℂ) ρ,
      ‖resolvent (transferOp hϑ hϑ1 hφ hC hθ0.le hθϑ hθ1 s) w‖ ≤ 2 * Λ₀)
    [FiniteDimensional ℂ (opRange (outerProj (transferOp hϑ hϑ1 hφ hC hθ0.le hθϑ hθ1 s) ρ))]
    (hr : finrank ℂ (opRange (outerProj (transferOp hϑ hϑ1 hφ hC hθ0.le hθϑ hθ1 s) ρ)) ≤ r)
    (hpowT : ∀ i : ℕ, ‖transferOp hϑ hϑ1 hφ hC hθ0.le hθϑ hθ1 s ^ i‖ ≤ K₁ * Real.exp (i * κ)) :
    ‖(∑ p ∈ periodicPoints A n, Complex.exp (-(s * birkhoff φ n p))) -
        outerTrace (transferOp hϑ hϑ1 hφ hC hθ0.le hθϑ hθ1 s) ρ n‖ ≤
      (B * ε⁻¹ + r * K₁ * (1 + ρ * (2 * Λ₀))) * Real.exp (n * κ) := by
  set T := transferOp hϑ hϑ1 hφ hC hθ0.le hθϑ hθ1 s
  have hz : ‖∑ p ∈ periodicPoints A n, Complex.exp (-(s * birkhoff φ n p))‖ ≤
      B * ε⁻¹ * Real.exp (n * κ) := by
    refine (norm_sum_le _ _).trans ?_
    have heq : ∑ p ∈ periodicPoints A n, ‖Complex.exp (-(s * birkhoff φ n p))‖ =
        periodicSumR A φ n s.re :=
      Finset.sum_congr rfl fun p _ => norm_cexp_neg_mul_ofReal s _
    rw [heq]
    refine (periodicSumR_le_exp hφ hR₀ hpos hε hB0 hB hs n).trans ?_
    exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr
      (mul_le_mul_of_nonneg_left hεκ (Nat.cast_nonneg n))) (by positivity)
  have hQ : ‖outerProj T ρ‖ ≤ 1 + ρ * (2 * Λ₀) := by
    have hP := norm_pow_mul_rieszProjection_le T hρ0.le hT hTΛ 0
    rw [pow_zero, one_mul, zero_add, pow_one] at hP
    calc ‖outerProj T ρ‖ ≤ ‖(1 : HolderSpace A ϑ →L[ℂ] HolderSpace A ϑ)‖ +
          ‖rieszProjection T 0 ρ‖ := norm_sub_le _ _
      _ ≤ 1 + ρ * (2 * Λ₀) := add_le_add ContinuousLinearMap.norm_id_le hP
  have htr : ‖outerTrace T ρ n‖ ≤ r * K₁ * (1 + ρ * (2 * Λ₀)) * Real.exp (n * κ) := by
    have hm : ∀ v, (T ^ n * outerProj T ρ) v ∈ opRange (outerProj T ρ) := fun v => by
      rw [(Commute.pow_left (commute_outerProj hρ0 hT) n).eq]; exact mem_opRange _ _
    refine (norm_finiteRankTrace_le _ _ hm).trans ?_
    have hΛ0 : 0 ≤ Λ₀ := by
      have := (norm_nonneg _).trans (hTΛ ρ (by simp [abs_of_pos hρ0]))
      linarith
    calc (finrank ℂ (opRange (outerProj T ρ)) : ℝ) * ‖T ^ n * outerProj T ρ‖
        ≤ r * (K₁ * Real.exp (n * κ) * (1 + ρ * (2 * Λ₀))) := by
          refine mul_le_mul (by exact_mod_cast hr) ((norm_mul_le _ _).trans
            (mul_le_mul (hpowT n) hQ (norm_nonneg _) (by positivity))) (norm_nonneg _)
            (Nat.cast_nonneg _)
      _ = r * K₁ * (1 + ρ * (2 * Λ₀)) * Real.exp (n * κ) := by ring
  calc _ ≤ ‖∑ p ∈ periodicPoints A n, Complex.exp (-(s * birkhoff φ n p))‖ +
        ‖outerTrace T ρ n‖ := norm_sub_le _ _
    _ ≤ B * ε⁻¹ * Real.exp (n * κ) + r * K₁ * (1 + ρ * (2 * Λ₀)) * Real.exp (n * κ) :=
        add_le_add hz htr
    _ = _ := by ring

include hφ hR₀ hC hθ0 hθ1 hpos hϑ hϑ1 hθϑ in
/-- The core of the local trace estimate: from uniform spectral data on a set `V`, a summable
majorant of the defects on `V`. -/
theorem local_trace_estimate_core {ε B κ S K₁ K₂ Pb Λ₀ ρ ρ₂ : ℝ} {m₂ q : ℕ} {V : Set ℂ}
    (hε : 0 < ε) (hB0 : 0 ≤ B)
    (hB : ∀ n : ℕ, periodicSumR A φ (n + 1) (1 + ε) ≤ B * ((n : ℝ) + 1))
    (hεκ : ε * (2 * R₀ + 1) ≤ κ) (hκ0 : 0 ≤ κ) (hρpos : 0 < ρ) (hρ1 : ρ < 1) (hρρ₂ : ρ ≤ ρ₂)
    (hcρ : ϑ * Real.exp κ < ρ) (hq : 2 ≤ q) (hkq : (k : ℝ) * ρ₂ ^ q < 1)
    (hθq : θ / ϑ * Real.exp (q * κ) < 1) (hS0 : 0 ≤ S) (hK₁ : 0 ≤ K₁) (hPb : 0 ≤ Pb)
    (hΛ₀ : 0 < Λ₀) (hm₂2 : 2 ≤ m₂)
    (hnb : ∀ s ∈ V, 1 - ε < s.re ∧ ‖s‖ ≤ S ∧
      (∀ w ∈ sphere (0 : ℂ) ρ, w ∈ resolventSet ℂ (transferOp hϑ hϑ1 hφ hC hθ0.le hθϑ hθ1 s)) ∧
      ∀ w ∈ sphere (0 : ℂ) ρ,
        ‖resolvent (transferOp hϑ hϑ1 hφ hC hθ0.le hθϑ hθ1 s) w‖ ≤ 2 * Λ₀)
    (hOB : ∀ s ∈ V,
      (∀ n : ℕ, ‖transferOp hϑ hϑ1 hφ hC hθ0.le hθϑ hθ1 s ^ n‖ ≤ K₁ * Real.exp (n * κ)) ∧
      ∀ n : ℕ, 1 ≤ n → ‖transferOp hϑ hϑ1 hφ hC hθ0.le hθϑ hθ1 s ^ n * (1 - cylAverage hϑ n)‖ ≤
        K₂ * (ϑ * Real.exp κ) ^ n)
    (hOBm : ∀ s ∈ V, ∀ m, m₂ ≤ m →
      (∀ n : ℕ, ‖transferOp hϑ hϑ1 (isHolderPotential_levelPotential hφ hθ0.le m) hC hθ0.le hθϑ
        hθ1 s ^ n‖ ≤ K₁ * Real.exp (n * κ)) ∧
      ∀ n : ℕ, 1 ≤ n → ‖transferOp hϑ hϑ1 (isHolderPotential_levelPotential hφ hθ0.le m) hC
        hθ0.le hθϑ hθ1 s ^ n * (1 - cylAverage hϑ n)‖ ≤ K₂ * (ϑ * Real.exp κ) ^ n)
    (hΔ : ∀ s ∈ V, ∀ m, ‖transferOp hϑ hϑ1 (isHolderPotential_levelPotential hφ hθ0.le m)
      hC hθ0.le hθϑ hθ1 s - transferOp hϑ hϑ1 hφ hC hθ0.le hθϑ hθ1 s‖ ≤ 3 * Pb * (θ / ϑ) ^ m)
    (hadmm : ∀ s ∈ V, ∀ m, m₂ ≤ m →
      (∀ w ∈ sphere (0 : ℂ) ρ, w ∈ resolventSet ℂ (transferOp hϑ hϑ1
        (isHolderPotential_levelPotential hφ hθ0.le m) hC hθ0.le hθϑ hθ1 s)) ∧
      (∀ w ∈ sphere (0 : ℂ) ρ, ‖resolvent (transferOp hϑ hϑ1
        (isHolderPotential_levelPotential hφ hθ0.le m) hC hθ0.le hθϑ hθ1 s) w‖ ≤ 4 * Λ₀) ∧
      2 * ‖transferOp hϑ hϑ1 (isHolderPotential_levelPotential hφ hθ0.le m) hC hθ0.le hθϑ hθ1 s -
        transferOp hϑ hϑ1 hφ hC hθ0.le hθϑ hθ1 s‖ * (2 * Λ₀) ≤ 1) :
    ∃ u : ℕ → ℝ, Summable u ∧ ∀ s ∈ V, ∀ n : ℕ, ‖(periodicZ A φ (n + 1) s -
        outerTrace (transferOp hϑ hϑ1 hφ hC hθ0.le hθϑ hθ1 s) ρ (n + 1)) / ((n : ℂ) + 1)‖ ≤
          u n := by
  have hc0 : 0 ≤ ϑ * Real.exp κ := by positivity
  -- the rank bound
  obtain ⟨n₀, hn₀1, hn₀⟩ : ∃ n₀, 1 ≤ n₀ ∧
      ρ * (4 * Λ₀) * (K₂ * (ϑ * Real.exp κ) ^ n₀) < ρ ^ n₀ := by
    obtain ⟨N, hN⟩ := eventually_atTop.mp
      ((eventually_mul_pow_lt hc0 hcρ (ρ * (4 * Λ₀) * K₂)).and (eventually_ge_atTop 1))
    exact ⟨N, (hN N le_rfl).2, by have := (hN N le_rfl).1; linarith⟩
  have hfinT : ∀ s ∈ V,
      FiniteDimensional ℂ (opRange (outerProj (transferOp hϑ hϑ1 hφ hC hθ0.le hθϑ hθ1 s) ρ)) ∧
      finrank ℂ (opRange (outerProj (transferOp hϑ hϑ1 hφ hC hθ0.le hθϑ hθ1 s) ρ)) ≤ k ^ n₀ := by
    intro s hs
    refine finiteDimensional_outerProj hϑ _ hρpos (hnb s hs).2.2.1 (hnb s hs).2.2.2 hn₀1 ?_
    have h1 := (hOB s hs).2 n₀ hn₀1
    have h2 : ρ * (2 * Λ₀) ≤ ρ * (4 * Λ₀) := by nlinarith
    calc _ ≤ ρ * (4 * Λ₀) * (K₂ * (ϑ * Real.exp κ) ^ n₀) :=
          mul_le_mul h2 h1 (norm_nonneg _) (by positivity)
      _ < ρ ^ n₀ := hn₀
  have hfinTm : ∀ s ∈ V, ∀ m, m₂ ≤ m →
      FiniteDimensional ℂ (opRange (outerProj (transferOp hϑ hϑ1
        (isHolderPotential_levelPotential hφ hθ0.le m) hC hθ0.le hθϑ hθ1 s) ρ)) ∧
      finrank ℂ (opRange (outerProj (transferOp hϑ hϑ1
        (isHolderPotential_levelPotential hφ hθ0.le m) hC hθ0.le hθϑ hθ1 s) ρ)) ≤ k ^ n₀ := by
    intro s hs m hm
    refine finiteDimensional_outerProj hϑ _ hρpos (hadmm s hs m hm).1 (hadmm s hs m hm).2.1 hn₀1 ?_
    have h1 := (hOBm s hs m hm).2 n₀ hn₀1
    calc _ ≤ ρ * (4 * Λ₀) * (K₂ * (ϑ * Real.exp κ) ^ n₀) :=
          mul_le_mul_of_nonneg_left h1 (by positivity)
      _ < ρ ^ n₀ := hn₀
  have hrange : ∀ s ∈ V, ∀ m, m₂ ≤ m → ∀ v, outerProj (transferOp hϑ hϑ1
      (isHolderPotential_levelPotential hφ hθ0.le m) hC hθ0.le hθϑ hθ1 s) ρ v ∈
        levelSpace A ϑ (m - 1) := fun s hs m hm v =>
    outerProj_apply_mem_levelSpace hϑ hϑ1 (isHolderPotential_levelPotential hφ hθ0.le m) hC
      hθ0.le hθϑ hθ1 (isLocal_levelPotential φ m) (hm₂2.trans hm) s hρpos (hadmm s hs m hm).1
      (hadmm s hs m hm).2.1 hc0 hcρ (hOBm s hs m hm).2 v
  -- decay rate and threshold
  obtain ⟨τ, hτdef⟩ : ∃ τ : ℝ, τ = max (θ / ϑ * Real.exp (q * κ)) ((k : ℝ) * ρ₂ ^ q) :=
    ⟨_, rfl⟩
  have hτ1 : τ < 1 := by rw [hτdef]; exact max_lt hθq hkq
  have hq0 : 0 ≤ θ / ϑ := div_nonneg hθ0.le hϑ.le
  have hτθϑ : θ / ϑ * Real.exp (q * κ) ≤ τ := by rw [hτdef]; exact le_max_left _ _
  have hτq : θ / ϑ ≤ τ :=
    (le_mul_of_one_le_right hq0 (Real.one_le_exp (by positivity))).trans hτθϑ
  have hτθ : θ * Real.exp (q * κ) ≤ τ :=
    (mul_le_mul_of_nonneg_right (le_div_self hθ0.le hϑ hϑ1) (Real.exp_pos _).le).trans hτθϑ
  have hτk : (k : ℝ) * ρ ^ q ≤ τ := by
    rw [hτdef]
    exact (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hρpos.le hρρ₂ q) (Nat.cast_nonneg k)).trans
      (le_max_right _ _)
  have hτ0 : 0 ≤ τ := hq0.trans hτq
  have hsumθ : Summable fun n : ℕ => (n : ℝ) ^ 1 * θ ^ (n / q) :=
    summable_pow_mul_pow_div hθ0.le hθ1 (by omega) 1
  obtain ⟨n₃, hn₃⟩ : ∃ n₃ : ℕ, ∀ n : ℕ, n₃ ≤ n →
      S * C * ((n : ℝ) ^ 1 * θ ^ (n / q)) ≤ 1 ∧ 2 * m₂ ≤ n := by
    have ht : Tendsto (fun n : ℕ => S * C * ((n : ℝ) ^ 1 * θ ^ (n / q))) atTop (𝓝 0) := by
      simpa using hsumθ.tendsto_atTop_zero.const_mul (S * C)
    exact eventually_atTop.mp ((ht.eventually (ge_mem_nhds one_pos)).and
      (eventually_ge_atTop (2 * m₂)))
  -- the majorant
  obtain ⟨cR, hcRdef⟩ : ∃ cR : ℝ, cR = B * ε⁻¹ * (S * C * Real.exp 1) * Real.exp (q * κ) +
      (k : ℝ) ^ m₂ * (ρ * (4 * Λ₀)) + 2 * ((k ^ n₀ : ℕ) : ℝ) *
        (K₁ ^ 2 * (3 * Pb) * Real.exp (q * κ) + 2 * (2 * Λ₀) ^ 2 * (3 * Pb)) := ⟨_, rfl⟩
  have hcR : 0 ≤ cR := by
    rw [hcRdef]
    have hS' : 0 ≤ S * C * Real.exp 1 := by positivity
    have : 0 ≤ B * ε⁻¹ := mul_nonneg hB0 (inv_nonneg.mpr hε.le)
    positivity
  obtain ⟨cC, hcCdef⟩ : ∃ cC : ℝ, cC = (B * ε⁻¹ + ((k ^ n₀ : ℕ) : ℝ) * K₁ * (1 + ρ * (2 * Λ₀))) *
      Real.exp (n₃ * κ) := ⟨_, rfl⟩
  refine ⟨fun n => (if n + 1 < n₃ then cC else 0) +
    cR * ((((n + 1 : ℕ) : ℝ)) + 1) * τ ^ ((n + 1) / q), ?_, fun s hs n => ?_⟩
  · refine Summable.add ?_ ?_
    · refine summable_of_ne_finset_zero (s := Finset.range n₃) fun n hn => ?_
      rw [if_neg]
      intro h
      exact hn (Finset.mem_range.mpr (by omega))
    · have h1 := summable_pow_mul_pow_div hτ0 hτ1 (by omega : 1 ≤ q) 1
      have h0 := summable_pow_mul_pow_div hτ0 hτ1 (by omega : 1 ≤ q) 0
      have hsum : Summable fun n : ℕ => cR * ((n : ℝ) + 1) * τ ^ (n / q) :=
        ((h1.add h0).mul_left cR).congr fun n => by ring
      exact (summable_nat_add_iff 1).mpr hsum
  · have hn1 : (1 : ℝ) ≤ ‖((n : ℂ) + 1)‖ := by
      rw [show ((n : ℂ) + 1) = ((n + 1 : ℕ) : ℂ) by push_cast; ring, Complex.norm_natCast]
      exact_mod_cast Nat.succ_pos n
    rw [norm_div]
    refine (div_le_self (norm_nonneg _) hn1).trans ?_
    have hz : periodicZ A φ (n + 1) s =
        ∑ p ∈ periodicPoints A (n + 1), Complex.exp (-(s * birkhoff φ (n + 1) p)) := rfl
    rw [hz]
    haveI := (hfinT s hs).1
    have hrefined0 : 0 ≤ cR * ((((n + 1 : ℕ) : ℝ)) + 1) * τ ^ ((n + 1) / q) := by positivity
    beta_reduce
    by_cases hsmall : n + 1 < n₃
    · rw [if_pos hsmall]
      have h := crude_bound_at hφ hR₀ hC hθ0 hθ1 hpos hϑ hϑ1 hθϑ (n := n + 1) s hε hB0 hB hεκ
        (hnb s hs).1 hρpos hK₁ (hnb s hs).2.2.1 (hnb s hs).2.2.2 (hfinT s hs).2 (hOB s hs).1
      refine h.trans ?_
      rw [hcCdef]
      have hexp : Real.exp (((n + 1 : ℕ) : ℝ) * κ) ≤ Real.exp (n₃ * κ) :=
        Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right (by exact_mod_cast hsmall.le) hκ0)
      have hc : 0 ≤ B * ε⁻¹ + ((k ^ n₀ : ℕ) : ℝ) * K₁ * (1 + ρ * (2 * Λ₀)) := by
        have : 0 ≤ B * ε⁻¹ := mul_nonneg hB0 (inv_nonneg.mpr hε.le)
        positivity
      nlinarith [mul_le_mul_of_nonneg_left hexp hc]
    · rw [if_neg hsmall, zero_add]
      have hn3 := hn₃ (n + 1) (not_lt.mp hsmall)
      have hdq : (n + 1) / q ≤ (n + 1) / 2 := Nat.div_le_div_left hq (by norm_num)
      have hd2 := Nat.div_mul_le_self (n + 1) 2
      have hmm : m₂ ≤ (n + 1) / q + m₂ := Nat.le_add_left _ _
      have hm2 : 2 ≤ (n + 1) / q + m₂ := hm₂2.trans hmm
      have hm₂half : m₂ ≤ (n + 1) / 2 := (Nat.le_div_iff_mul_le (by norm_num)).mpr (by omega)
      have hmn : (n + 1) / q + m₂ ≤ n + 1 + 1 := by
        have h1 : (n + 1) / q + m₂ ≤ (n + 1) / 2 + (n + 1) / 2 := Nat.add_le_add hdq hm₂half
        have h2 : (n + 1) / 2 + (n + 1) / 2 = (n + 1) / 2 * 2 := by ring
        omega
      haveI := (hfinTm s hs _ hmm).1
      have h := defect_bound_at hφ hR₀ hC hθ0 hθ1 hpos hϑ hϑ1 hθϑ (r := k ^ n₀) (m₂ := m₂)
        (n := n + 1) (q := q) (S := S) (Pb := Pb) s hε hB0 hB hεκ hκ0 (hnb s hs).1 (hnb s hs).2.1
        (by omega) hm2 hmn hn3.1 hρpos hρ1.le hΛ₀.le hK₁ hPb (hnb s hs).2.2.1 (hnb s hs).2.2.2
        (hadmm s hs _ hmm).1 (hadmm s hs _ hmm).2.1 (hadmm s hs _ hmm).2.2 (hfinT s hs).2
        (hfinTm s hs _ hmm).2 (hrange s hs _ hmm) (hOB s hs).1 (hOBm s hs _ hmm).1 (hΔ s hs _)
        hτθ hτθϑ hτq hτk
      refine h.trans (le_of_eq ?_)
      rw [hcRdef]

include hmix hM hφ hR₀ hC hθ0 hθ1 hpos hϑ hϑ1 hθϑ in
/-- **The local trace estimate**: near each point of `Re s > 1 − ε` and for each admissible circle,
the defects `(Z_n(s) − tr(L_sⁿ|_W))/n` are bounded by a summable sequence. -/
theorem local_trace_estimate {ε B κ : ℝ} (hε : 0 < ε) (hB0 : 0 ≤ B)
    (hB : ∀ n : ℕ, periodicSumR A φ (n + 1) (1 + ε) ≤ B * ((n : ℝ) + 1))
    (hκ : ε * (2 * R₀ + 2) = κ) {ρ₁ ρ₂ : ℝ} (hρ₁ : 0 < ρ₁) (hρ₂ : ρ₂ < 1)
    (hϑρ : ϑ * Real.exp κ < ρ₁) {q : ℕ} (hq : 2 ≤ q) (hkq : (k : ℝ) * ρ₂ ^ q < 1)
    (hθq : θ / ϑ * Real.exp (q * κ) < 1) {s₀ : ℂ} (hs₀ : 1 - ε < s₀.re) {ρ : ℝ}
    (hρ : IsAdmissibleRadius (transferOp hϑ hϑ1 hφ hC hθ0.le hθϑ hθ1 s₀) ρ₁ ρ₂ ρ) :
    ∃ V ∈ 𝓝 s₀, ∃ u : ℕ → ℝ, Summable u ∧ ∀ s ∈ V,
      IsAdmissibleRadius (transferOp hϑ hϑ1 hφ hC hθ0.le hθϑ hθ1 s) ρ₁ ρ₂ ρ ∧
      ∀ n : ℕ, ‖(periodicZ A φ (n + 1) s -
        outerTrace (transferOp hϑ hϑ1 hφ hC hθ0.le hθϑ hθ1 s) ρ (n + 1)) / ((n : ℂ) + 1)‖ ≤
          u n := by
  have hκ0 : 0 ≤ κ := by rw [← hκ]; positivity
  have hεκ : ε * (2 * R₀ + 1) ≤ κ := by rw [← hκ]; nlinarith
  have hρpos : 0 < ρ := hρ₁.trans_le hρ.1.1
  have hρ1 : ρ < 1 := hρ.1.2.trans_lt hρ₂
  have hcρ : ϑ * Real.exp κ < ρ := hϑρ.trans_le hρ.1.1
  have hc0 : 0 ≤ ϑ * Real.exp κ := by positivity
  obtain ⟨δ₀, hδ₀, Λ₀, hΛ₀, hnb⟩ :=
    local_neighbourhood hφ hR₀ hC hθ0 hθ1 hϑ hϑ1 hθϑ hs₀ hρ.2
  obtain ⟨S, hSdef⟩ : ∃ S : ℝ, S = ‖s₀‖ + δ₀ := ⟨_, rfl⟩
  have hS0 : 0 ≤ S := by rw [hSdef]; positivity
  obtain ⟨K, hK, m₀, hm₀, hU⟩ :=
    uniform_partition_bounds hmix hM hφ hR₀ hC hθ0.le hθ1 hpos hε hB0 hB S
  obtain ⟨Lb, hLbdef⟩ : ∃ Lb : ℝ, Lb = 2 + S * (C / (1 - θ)) * Real.exp (S * (C / (1 - θ))) :=
    ⟨_, rfl⟩
  have hLb : 0 ≤ Lb := by
    have : 0 ≤ C / (1 - θ) := div_nonneg hC (by linarith)
    rw [hLbdef]; positivity
  obtain ⟨K₁, hK₁def⟩ : ∃ K₁ : ℝ, K₁ = max 1 (K * (Lb + 1)) := ⟨_, rfl⟩
  obtain ⟨K₂, hK₂def⟩ : ∃ K₂ : ℝ, K₂ = K * (Lb + 2) := ⟨_, rfl⟩
  have hK₁ : 0 ≤ K₁ := by rw [hK₁def]; exact le_trans zero_le_one (le_max_left _ _)
  have hK₂ : 0 ≤ K₂ := by rw [hK₂def]; positivity
  have hsS : ∀ s ∈ ball s₀ δ₀, ‖s‖ ≤ S := fun s hs => by rw [hSdef]; exact (hnb s hs).2.1
  -- operator bounds along the neighbourhood
  have hOB : ∀ s ∈ ball s₀ δ₀,
      (∀ n : ℕ, ‖transferOp hϑ hϑ1 hφ hC hθ0.le hθϑ hθ1 s ^ n‖ ≤ K₁ * Real.exp (n * κ)) ∧
      ∀ n : ℕ, 1 ≤ n → ‖transferOp hϑ hϑ1 hφ hC hθ0.le hθϑ hθ1 s ^ n * (1 - cylAverage hϑ n)‖ ≤
        K₂ * (ϑ * Real.exp κ) ^ n := by
    intro s hs
    have h := transferOp_bounds hϑ hϑ1 hφ hC hθ0.le hθϑ hθ1 s (κ := κ) (hsS s hs) hK
      (fun n hn x => by rw [← hκ]; exact (hU s (hsS s hs) (hnb s hs).1 n hn x).1)
    rw [hK₁def, hK₂def, hLbdef]
    exact h
  have hOBm : ∀ s ∈ ball s₀ δ₀, ∀ m, m₀ ≤ m →
      (∀ n : ℕ, ‖transferOp hϑ hϑ1 (isHolderPotential_levelPotential hφ hθ0.le m) hC hθ0.le hθϑ
        hθ1 s ^ n‖ ≤ K₁ * Real.exp (n * κ)) ∧
      ∀ n : ℕ, 1 ≤ n → ‖transferOp hϑ hϑ1 (isHolderPotential_levelPotential hφ hθ0.le m) hC
        hθ0.le hθϑ hθ1 s ^ n * (1 - cylAverage hϑ n)‖ ≤ K₂ * (ϑ * Real.exp κ) ^ n := by
    intro s hs m hm
    have h := transferOp_bounds hϑ hϑ1 (isHolderPotential_levelPotential hφ hθ0.le m) hC hθ0.le
      hθϑ hθ1 s (κ := κ) (hsS s hs) hK
      (fun n hn x => by rw [← hκ]; exact (hU s (hsS s hs) (hnb s hs).1 n hn x).2 m hm)
    rw [hK₁def, hK₂def, hLbdef]
    exact h
  -- the perturbation threshold
  obtain ⟨Pb, hPbdef⟩ : ∃ Pb : ℝ, Pb = (k : ℝ) * Real.exp (S * R₀) * (S * C * Real.exp (S * C)) :=
    ⟨_, rfl⟩
  have hPb : 0 ≤ Pb := by rw [hPbdef]; positivity
  have hq0 : 0 ≤ θ / ϑ := div_nonneg hθ0.le hϑ.le
  have hθϑq : θ / ϑ < 1 := by
    have : θ / ϑ ≤ θ / ϑ * Real.exp (q * κ) :=
      le_mul_of_one_le_right hq0 (Real.one_le_exp (by positivity))
    linarith
  obtain ⟨m₁, hm₁⟩ : ∃ m₁, ∀ m, m₁ ≤ m → 3 * Pb * (θ / ϑ) ^ m ≤ (8 * Λ₀)⁻¹ := by
    have ht : Tendsto (fun m : ℕ => 3 * Pb * (θ / ϑ) ^ m) atTop (𝓝 0) := by
      simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hq0 hθϑq).const_mul (3 * Pb)
    exact eventually_atTop.mp (ht.eventually (ge_mem_nhds (by positivity)))
  obtain ⟨m₂, hm₂def⟩ : ∃ m₂, m₂ = max (max m₀ m₁) 2 := ⟨_, rfl⟩
  have hm₂0 : m₀ ≤ m₂ := by rw [hm₂def]; exact le_trans (le_max_left _ _) (le_max_left _ _)
  have hm₂1 : m₁ ≤ m₂ := by rw [hm₂def]; exact le_trans (le_max_right _ _) (le_max_left _ _)
  have hm₂2 : 2 ≤ m₂ := by rw [hm₂def]; exact le_max_right _ _
  have hΔ : ∀ s ∈ ball s₀ δ₀, ∀ m, ‖transferOp hϑ hϑ1 (isHolderPotential_levelPotential hφ hθ0.le m)
      hC hθ0.le hθϑ hθ1 s - transferOp hϑ hϑ1 hφ hC hθ0.le hθϑ hθ1 s‖ ≤ 3 * Pb * (θ / ϑ) ^ m :=
    fun s hs m => by rw [hPbdef]; exact level_perturb_le hφ hR₀ hC hθ0 hθ1 hϑ hϑ1 hθϑ (hsS s hs) m
  have hadmm : ∀ s ∈ ball s₀ δ₀, ∀ m, m₂ ≤ m →
      (∀ w ∈ sphere (0 : ℂ) ρ, w ∈ resolventSet ℂ (transferOp hϑ hϑ1
        (isHolderPotential_levelPotential hφ hθ0.le m) hC hθ0.le hθϑ hθ1 s)) ∧
      (∀ w ∈ sphere (0 : ℂ) ρ, ‖resolvent (transferOp hϑ hϑ1
        (isHolderPotential_levelPotential hφ hθ0.le m) hC hθ0.le hθϑ hθ1 s) w‖ ≤ 4 * Λ₀) ∧
      2 * ‖transferOp hϑ hϑ1 (isHolderPotential_levelPotential hφ hθ0.le m) hC hθ0.le hθϑ hθ1 s -
        transferOp hϑ hϑ1 hφ hC hθ0.le hθϑ hθ1 s‖ * (2 * Λ₀) ≤ 1 := fun s hs m hm =>
    resolvent_bound_of_small_perturb _ _ hΛ₀ (hnb s hs).2.2.1 (hnb s hs).2.2.2
      ((hΔ s hs m).trans (hm₁ m (hm₂1.trans hm)))
  obtain ⟨u, hu, hbound⟩ := local_trace_estimate_core hφ hR₀ hC hθ0 hθ1 hpos hϑ hϑ1 hθϑ
    (V := ball s₀ δ₀) hε hB0 hB hεκ hκ0 hρpos hρ1 hρ.1.2 hcρ hq hkq hθq hS0 hK₁ hPb hΛ₀ hm₂2
    (fun s hs => ⟨(hnb s hs).1, hsS s hs, (hnb s hs).2.2.1, (hnb s hs).2.2.2⟩) hOB
    (fun s hs m hm => hOBm s hs m (hm₂0.trans hm)) hΔ hadmm
  exact ⟨ball s₀ δ₀, ball_mem_nhds s₀ hδ₀, u, hu, fun s hs =>
    ⟨⟨hρ.1, (hnb s hs).2.2.1⟩, hbound s hs⟩⟩

include hmix hM hφ hR₀ hC hθ0 hθ1 in
/-- **The Ruelle–Pollicott continuation.**  For a positive Hölder roof on a mixing subshift with
`Σ_n Z_n(σ)/n < ∞` for `σ > 1`, there are `ε > 0` and a function `F`, holomorphic on
`Re s > 1 − ε`, with `F(s) = exp(−Σ_{n≥1} Z_n(s)/n)` for `Re s > 1`. -/
theorem exists_holomorphic_reciprocal {rmin : ℝ} (hrmin : 0 < rmin)
    (hmin : ∀ y, IsAdmissible A y → rmin ≤ φ y)
    (hsum : ∀ σ : ℝ, 1 < σ → Summable fun n : ℕ => periodicSumR A φ (n + 1) σ / ((n : ℝ) + 1)) :
    ∃ ε > 0, ∃ F : ℂ → ℂ, DifferentiableOn ℂ F {s | 1 - ε < s.re} ∧
      ∀ s : ℂ, 1 < s.re →
        F s = Complex.exp (-∑' n : ℕ, periodicZ A φ (n + 1) s / ((n : ℂ) + 1)) := by
  have hpos : ∀ y, IsAdmissible A y → 0 ≤ φ y := fun y hy => hrmin.le.trans (hmin y hy)
  -- the Hölder exponent and the radii
  obtain ⟨ϑ, hϑdef⟩ : ∃ ϑ : ℝ, ϑ = (1 + θ) / 2 := ⟨_, rfl⟩
  have hϑ : 0 < ϑ := by rw [hϑdef]; linarith
  have hθϑ' : θ < ϑ := by rw [hϑdef]; linarith
  have hθϑ : θ ≤ ϑ := hθϑ'.le
  have hϑlt : ϑ < 1 := by rw [hϑdef]; linarith
  have hϑ1 : ϑ ≤ 1 := hϑlt.le
  obtain ⟨ρ₁, hρ₁def⟩ : ∃ ρ₁ : ℝ, ρ₁ = (1 + ϑ) / 2 := ⟨_, rfl⟩
  obtain ⟨ρ₂, hρ₂def⟩ : ∃ ρ₂ : ℝ, ρ₂ = (3 + ϑ) / 4 := ⟨_, rfl⟩
  have hρ₁ : 0 < ρ₁ := by rw [hρ₁def]; linarith
  have hϑρ₁ : ϑ < ρ₁ := by rw [hρ₁def]; linarith
  have hρ₁₂ : ρ₁ < ρ₂ := by rw [hρ₁def, hρ₂def]; linarith
  have hρ₂ : ρ₂ < 1 := by rw [hρ₂def]; linarith
  have hρ₂0 : 0 ≤ ρ₂ := by linarith
  -- the level divisor
  obtain ⟨q, hq, hkq⟩ : ∃ q : ℕ, 2 ≤ q ∧ (k : ℝ) * ρ₂ ^ q < 1 := by
    have ht : Tendsto (fun q : ℕ => (k : ℝ) * ρ₂ ^ q) atTop (𝓝 0) := by
      simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hρ₂0 hρ₂).const_mul (k : ℝ)
    obtain ⟨N, hN⟩ := eventually_atTop.mp ((ht.eventually (gt_mem_nhds one_pos)).and
      (eventually_ge_atTop 2))
    exact ⟨N, (hN N le_rfl).2, (hN N le_rfl).1⟩
  -- the growth rate
  obtain ⟨γ, hγdef⟩ : ∃ γ : ℝ, γ = min (ϑ / θ) (ρ₁ / ϑ) := ⟨_, rfl⟩
  have hγ : 1 < γ := by
    rw [hγdef]
    exact lt_min ((one_lt_div hθ0).mpr hθϑ') ((one_lt_div hϑ).mpr hϑρ₁)
  have hlogγ : 0 < Real.log γ := Real.log_pos hγ
  have hq0 : (0 : ℝ) < q := by exact_mod_cast (show 0 < q by omega)
  obtain ⟨κ, hκdef⟩ : ∃ κ : ℝ, κ = Real.log γ / (2 * q) := ⟨_, rfl⟩
  have hκ0 : 0 < κ := by rw [hκdef]; positivity
  have hqκ : Real.exp (q * κ) < γ := by
    have : (q : ℝ) * κ = Real.log γ / 2 := by rw [hκdef]; field_simp
    rw [this]
    calc Real.exp (Real.log γ / 2) < Real.exp (Real.log γ) := Real.exp_lt_exp.mpr (by linarith)
      _ = γ := Real.exp_log (lt_trans one_pos hγ)
  have hκq : Real.exp κ ≤ Real.exp (q * κ) := by
    refine Real.exp_le_exp.mpr ?_
    have : (1 : ℝ) ≤ q := by exact_mod_cast (show 1 ≤ q by omega)
    nlinarith
  obtain ⟨ε, hεdef⟩ : ∃ ε : ℝ, ε = κ / (2 * R₀ + 2) := ⟨_, rfl⟩
  have hε : 0 < ε := by rw [hεdef]; positivity
  have hεκ : ε * (2 * R₀ + 2) = κ := by rw [hεdef]; field_simp
  have hϑρ : ϑ * Real.exp κ < ρ₁ := by
    have h1 : Real.exp κ < ρ₁ / ϑ :=
      (hκq.trans_lt hqκ).trans_le (by rw [hγdef]; exact min_le_right _ _)
    rwa [lt_div_iff₀ hϑ, mul_comm] at h1
  have hθq : θ / ϑ * Real.exp (q * κ) < 1 := by
    have h1 : Real.exp (q * κ) < ϑ / θ := hqκ.trans_le (by rw [hγdef]; exact min_le_left _ _)
    have h2 : θ / ϑ * (ϑ / θ) = 1 := by field_simp
    calc θ / ϑ * Real.exp (q * κ) < θ / ϑ * (ϑ / θ) :=
          mul_lt_mul_of_pos_left h1 (div_pos hθ0 hϑ)
      _ = 1 := h2
  obtain ⟨B, hB0, hB⟩ := exists_periodicSumR_le (hsum (1 + ε) (by linarith))
  -- the continuation theorem
  have hΩ : IsOpen {s : ℂ | 1 - ε < s.re} := isOpen_lt continuous_const Complex.continuous_re
  have hexists : ∀ s ∈ {s : ℂ | 1 - ε < s.re}, ∃ ρ, IsAdmissibleRadius
      (transferOp hϑ hϑ1 hφ hC hθ0.le hθϑ hθ1 s) ρ₁ ρ₂ ρ := by
    intro s hs
    obtain ⟨K, hK, m₀, -, hU⟩ :=
      uniform_partition_bounds hmix hM hφ hR₀ hC hθ0.le hθ1 hpos hε hB0 hB ‖s‖
    have hb := (transferOp_bounds hϑ hϑ1 hφ hC hθ0.le hθϑ hθ1 s (κ := κ) le_rfl hK
      (fun n hn x => by rw [← hεκ]; exact (hU s le_rfl hs n hn x).1)).2
    set K₂ := K * (2 + ‖s‖ * (C / (1 - θ)) * Real.exp (‖s‖ * (C / (1 - θ))) + 2)
    obtain ⟨N, hN⟩ := eventually_atTop.mp ((eventually_mul_pow_lt (by positivity)
      (hϑρ) K₂).and (eventually_ge_atTop 1))
    exact exists_admissibleRadius hϑ _ hρ₁ hρ₁₂ (hN N le_rfl).2
      (lt_of_le_of_lt (hb N (hN N le_rfl).2) (hN N le_rfl).1)
  have hfin : ∀ s ∈ {s : ℂ | 1 - ε < s.re}, ∀ ρ, IsAdmissibleRadius
      (transferOp hϑ hϑ1 hφ hC hθ0.le hθϑ hθ1 s) ρ₁ ρ₂ ρ →
      FiniteDimensional ℂ (opRange (outerProj (transferOp hϑ hϑ1 hφ hC hθ0.le hθϑ hθ1 s) ρ)) := by
    intro s hs ρ hρ
    have hρpos : 0 < ρ := hρ₁.trans_le hρ.1.1
    obtain ⟨Λ, hΛpos, hΛ⟩ := exists_norm_resolvent_le_on_sphere
      (transferOp hϑ hϑ1 hφ hC hθ0.le hθϑ hθ1 s) hρ.2
    obtain ⟨K, hK, m₀, -, hU⟩ :=
      uniform_partition_bounds hmix hM hφ hR₀ hC hθ0.le hθ1 hpos hε hB0 hB ‖s‖
    have hb := (transferOp_bounds hϑ hϑ1 hφ hC hθ0.le hθϑ hθ1 s (κ := κ) le_rfl hK
      (fun n hn x => by rw [← hεκ]; exact (hU s le_rfl hs n hn x).1)).2
    set K₂ := K * (2 + ‖s‖ * (C / (1 - θ)) * Real.exp (‖s‖ * (C / (1 - θ))) + 2)
    obtain ⟨N, hN⟩ := eventually_atTop.mp ((eventually_mul_pow_lt (by positivity)
      (hϑρ.trans_le hρ.1.1) (ρ * Λ * K₂)).and (eventually_ge_atTop 1))
    refine (finiteDimensional_outerProj hϑ _ hρpos hρ.2 hΛ (hN N le_rfl).2 ?_).1
    calc ρ * Λ * ‖transferOp hϑ hϑ1 hφ hC hθ0.le hθϑ hθ1 s ^ N * (1 - cylAverage hϑ N)‖
        ≤ ρ * Λ * (K₂ * (ϑ * Real.exp κ) ^ N) :=
          mul_le_mul_of_nonneg_left (hb N (hN N le_rfl).2) (by positivity)
      _ = ρ * Λ * K₂ * (ϑ * Real.exp κ) ^ N := by ring
      _ < ρ ^ N := (hN N le_rfl).1
  have hloc : ∀ s₀ ∈ {s : ℂ | 1 - ε < s.re}, ∀ ρ, IsAdmissibleRadius
      (transferOp hϑ hϑ1 hφ hC hθ0.le hθϑ hθ1 s₀) ρ₁ ρ₂ ρ → ∃ V ∈ 𝓝 s₀, ∃ u : ℕ → ℝ,
      Summable u ∧ ∀ s ∈ V, IsAdmissibleRadius (transferOp hϑ hϑ1 hφ hC hθ0.le hθϑ hθ1 s) ρ₁ ρ₂ ρ ∧
        ∀ n, ‖(periodicZ A φ (n + 1) s - outerTrace (transferOp hϑ hϑ1 hφ hC hθ0.le hθϑ hθ1 s) ρ
          (n + 1)) / ((n : ℂ) + 1)‖ ≤ u n := by
    intro s₀ hs₀ ρ hρ
    exact local_trace_estimate hmix hM hφ hR₀ hC hθ0 hθ1 hpos hϑ hϑ1 hθϑ hε hB0 hB hεκ hρ₁ hρ₂
      hϑρ hq hkq hθq hs₀ hρ
  obtain ⟨F, hFd, hFv⟩ :=
    exists_continuation (T := fun s => transferOp hϑ hϑ1 hφ hC hθ0.le hθϑ hθ1 s)
      hΩ (differentiable_transferOp hϑ hϑ1 hφ hC hθ0.le hθϑ hθ1 hR₀).differentiableOn hρ₁ hρ₂
      (z := periodicZ A φ) (differentiable_periodicZ φ) hexists hfin hloc
  refine ⟨ε, hε, F, hFd, fun s hs => ?_⟩
  have hsΩ : s ∈ {s : ℂ | 1 - ε < s.re} := by show 1 - ε < s.re; linarith
  obtain ⟨c, τ, hc, hτ0, hτ1, hΨ⟩ :=
    exists_partitionFun_le_geometric hmix hM hφ hθ0.le hθ1 hrmin hmin hsum hs
  set L := lyConst C θ s
  have hL : 0 ≤ L := lyConst_nonneg hC hθ1 s
  refine hFv s hsΩ (max 1 (c * (L + 1))) τ hτ0 hτ1 (fun n => ?_) ?_
  · rcases Nat.eq_zero_or_pos n with rfl | hn
    · rw [pow_zero, pow_zero, mul_one]
      exact ContinuousLinearMap.norm_id_le.trans (le_max_left _ _)
    · have h := norm_transferOp_pow_le hϑ hϑ1 hφ hC hθ0.le hθϑ hθ1 s n
        (by positivity : 0 ≤ c * τ ^ n) fun x _ => hΨ n hn x
      refine h.trans ?_
      calc c * τ ^ n * (L + 1) = c * (L + 1) * τ ^ n := by ring
        _ ≤ max 1 (c * (L + 1)) * τ ^ n :=
            mul_le_mul_of_nonneg_right (le_max_right _ _) (pow_nonneg hτ0 n)
  · refine Summable.of_norm_bounded (hsum s.re hs) fun n => ?_
    rw [norm_div]
    have hn1 : ‖((n : ℂ) + 1)‖ = (n : ℝ) + 1 := by
      have := Complex.norm_natCast (n + 1)
      push_cast at this
      exact this
    rw [hn1]
    exact div_le_div_of_nonneg_right (norm_periodicZ_le φ n s) (by positivity)

end Main


end

end GaloisForLFunctions.HTGeometry.Symbolic
