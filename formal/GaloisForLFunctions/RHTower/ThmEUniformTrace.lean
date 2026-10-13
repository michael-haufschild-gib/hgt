import GaloisForLFunctions.RHTower.ThmEUniformArchimedean
import Zeta23.Chebyshev

/-!
# The prime-side trace of Dirichlet L-functions, uniformly in the modulus

For a character `χ` of parity `κ` modulo `q` with coefficient sequence `c`, the diagonal entries of the
prime-side Gram matrix are `G_kk = ∫ φ̂(r)² ν(τ_k + r) dr` with `ν = μ_q + P_c`.  Since
`μ_q = μ_1 + (log q)/(2π)` and `∫ φ̂² = 2π a L`,

`tr G̃(q, c) = tr G̃(1, 0) + 2π a d (log q)/(2π) + L⁻¹ Σ_k ∫ φ̂(r)² P_c(τ_k + r) dr`   (`trGtChiA_shift`),

where `tr G̃(1, 0)` involves only the archimedean density of modulus one and `d = ⌊LT/2π⌋`.  With
Alpöge–Furman's fixed-modulus evaluation at `q = 1` and their bound for the prime part (which uses only
`|c(n)| ≤ 1`), this gives

`|tr G̃ − a L N| ≤ C (1 + log q) L √X`   whenever `|N − (T/2π) ℓ_{1,q}(T)| ≤ A log T`
                                                                         (`prop_trace_uniform`),

with `C` and the threshold for `T` independent of `q` and of the coefficients.
-/

open MeasureTheory Real Set Zeta23 Zeta23.ThmE Zeta23.PrimeSide
open scoped ArithmeticFunction

noncomputable section

namespace RHTower

variable {cϱ : ℝ} {p : Setting} {F : LocalFun}

theorem coeffOK_one_zero : CoeffOK 1 (fun _ => (0 : ℂ)) := ⟨fun _ => by simp, fun _ _ => rfl⟩

theorem PXc_zero (X τ : ℝ) : PXc (fun _ => (0 : ℂ)) X τ = 0 := by simp [PXc]

/-- **Diagonal entries under the modulus shift.** -/
theorem GentryChiA_diag_shift {κ q : ℕ} (hκ : κ ≤ 1) (hq : 1 ≤ q) {c : ℕ → ℂ}
    (hc : CoeffOK q c) (hF : LocalHypsCoreW cϱ p F) (k : ℤ) (hk : 0 < p.tau k) :
    GentryChiA κ q c p F k k
      = GentryChiA κ 1 (fun _ => 0) p F k k + Real.log q / (2 * π) * (2 * π * F.a * p.L)
        + ∫ r, F.phiHat r ^ 2 * PXc c p.X (p.tau k + r) := by
  have hΓq := GammaChi.gammaFactsChi hκ hq
  have hΓ1 := GammaChi.gammaFactsChi hκ le_rfl
  rw [GentryChiA_diag_eq hΓq hq hF hc k hk, GentryChiA_diag_eq hΓ1 le_rfl hF coeffOK_one_zero k hk]
  simp only [PXc_zero, mul_zero, integral_zero, add_zero]
  have hsplit : (fun r => F.phiHat r ^ 2 * muq κ q (p.tau k + r))
      = fun r => F.phiHat r ^ 2 * muq κ 1 (p.tau k + r) + Real.log q / (2 * π) * F.phiHat r ^ 2 := by
    funext r; rw [muq_eq_muq_one_add κ q hq]; ring
  rw [hsplit, integral_add (muq_part_integrable hΓ1 le_rfl hF hk)
    (hF.phiHat_sq_integrable.const_mul _), integral_const_mul, hF.phiHat_sq_integral]

/-- **The trace under the modulus shift.** -/
theorem trGtChiA_shift {κ q : ℕ} (hκ : κ ≤ 1) (hq : 1 ≤ q) {c : ℕ → ℂ} (hc : CoeffOK q c)
    (hF : LocalHypsCoreW cϱ p F) (hT : 0 < p.T) :
    trGtChiA κ q c p F
      = trGtChiA κ 1 (fun _ => 0) p F + 2 * π * F.a * p.d * (Real.log q / (2 * π))
        + (p.L)⁻¹ * ∑ k ∈ Finset.range p.d, ∫ r, F.phiHat r ^ 2 * PXc c p.X (p.tau k + r) := by
  have hL : 0 < p.L := by linarith [hF.eight_le_L]
  unfold trGtChiA
  rw [Fin.sum_univ_eq_sum_range (fun k => GentryChiA κ q c p F k k) p.d,
    Fin.sum_univ_eq_sum_range (fun k => GentryChiA κ 1 (fun _ => 0) p F k k) p.d]
  have hsum : ∑ k ∈ Finset.range p.d, GentryChiA κ q c p F k k
      = ∑ k ∈ Finset.range p.d, GentryChiA κ 1 (fun _ => 0) p F k k
        + p.d * (Real.log q / (2 * π) * (2 * π * F.a * p.L))
        + ∑ k ∈ Finset.range p.d, ∫ r, F.phiHat r ^ 2 * PXc c p.X (p.tau k + r) := by
    have hterm : ∀ k ∈ Finset.range p.d, GentryChiA κ q c p F (k : ℤ) (k : ℤ)
        = GentryChiA κ 1 (fun _ => 0) p F k k + Real.log q / (2 * π) * (2 * π * F.a * p.L)
          + ∫ r, F.phiHat r ^ 2 * PXc c p.X (p.tau k + r) := fun k hk =>
      GentryChiA_diag_shift hκ hq hc hF k (by linarith [(p.tau_mem hL hT.le hk).1])
    rw [Finset.sum_congr rfl hterm, Finset.sum_add_distrib, Finset.sum_add_distrib,
      Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  rw [hsum]
  field_simp

/-- `|2π a d − a L T| ≤ 2π a`. -/
theorem abs_two_pi_d_sub_le (hL : 0 < p.L) (hT : 0 < p.T) {a : ℝ} (ha : 0 ≤ a) :
    |2 * π * a * p.d - a * p.L * p.T| ≤ 2 * π * a := by
  have hx : 0 ≤ p.L * p.T / (2 * π) := by positivity
  have h1 : (p.d : ℝ) ≤ p.L * p.T / (2 * π) := Nat.floor_le hx
  have h2 : p.L * p.T / (2 * π) < p.d + 1 := Nat.lt_floor_add_one _
  have hπ : 0 < 2 * π := by positivity
  rw [le_div_iff₀ hπ] at h1
  rw [div_lt_iff₀ hπ] at h2
  rw [abs_le]
  constructor <;> nlinarith

variable (cϱ) in
/-- **[prop:trace] for `L(s, χ)`, uniformly in the modulus and the coefficients.** -/
theorem prop_trace_uniform {lam : ℝ} (hlam : 0 < lam ∧ lam ≤ 1) (A : ℝ) :
    ∃ C T₀ : ℝ, 0 ≤ C ∧ ∀ κ q : ℕ, κ ≤ 1 → 1 ≤ q → ∀ c : ℕ → ℂ, CoeffOK q c →
      ∀ (p : Setting) (F : LocalFun), p.lam = lam → T₀ ≤ p.T → LocalHypsCore cϱ p F →
      ∀ N : ℝ, |N - p.T / (2 * π) * ell1q q p.T| ≤ A * Real.log p.T →
        |trGtChiA κ q c p F - F.a * p.L * N| ≤ C * (1 + Real.log q) * (p.L * Real.sqrt p.X) := by
  obtain ⟨C₀, T₀₀, hC₀⟩ := prop_trace_chi (κ := 0) (q := 1) (c := fun _ => 0) (cϱ := cϱ)
    (lam := lam) (GammaChi.gammaFactsChi (by norm_num) le_rfl) Cheb.chebyshevMertens
    coeffOK_one_zero hlam A le_rfl
  obtain ⟨C₁, T₀₁, hC₁⟩ := prop_trace_chi (κ := 1) (q := 1) (c := fun _ => 0) (cϱ := cϱ)
    (lam := lam) (GammaChi.gammaFactsChi le_rfl le_rfl) Cheb.chebyshevMertens
    coeffOK_one_zero hlam A le_rfl
  obtain ⟨x₀, hx₀⟩ := Cheb.chebyshevMertens.cheb1b
  have hlog2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  refine ⟨|C₀| + |C₁| + 1 + 3 / Real.log 2,
    max (max T₀₀ T₀₁) (max (2 * π * Real.exp (|x₀| / lam)) 1), by positivity,
    fun κ q hκ hq c hc p F hp hT hF N hN => ?_⟩
  have hT₀ : max T₀₀ T₀₁ ≤ p.T := (le_max_left _ _).trans hT
  have hTx : 2 * π * Real.exp (|x₀| / lam) ≤ p.T := ((le_max_left _ _).trans (le_max_right _ _)).trans hT
  have hT1 : 1 ≤ p.T := ((le_max_right _ _).trans (le_max_right _ _)).trans hT
  have hT0 : 0 < p.T := by linarith
  have hL : 0 < p.L := hF.L_pos
  have hlam0 : 0 < p.lam := hp ▸ hlam.1
  have hX : x₀ ≤ p.X := Setting.le_X_of_T hlam0 (by rw [hp]; exact hTx)
  have hX1 : 1 ≤ Real.sqrt p.X := by
    rw [Real.le_sqrt' one_pos, one_pow]
    exact Real.one_le_exp hL.le
  have hS1 : 1 ≤ p.L * Real.sqrt p.X := by nlinarith [hF.eight_le_L]
  have hlq : 0 ≤ Real.log q := Real.log_nonneg (by exact_mod_cast hq)
  have ha0 : 0 ≤ F.a := hF.a_pos.le
  have ha1 : F.a ≤ 1 := hF.a_le_one
  -- the modulus-one data
  set N₁ := N - p.T * (Real.log q / (2 * π)) with hN₁
  have hN₁b : |N₁ - p.T / (2 * π) * ell1q 1 p.T| ≤ A * Real.log p.T := by
    have hell : ell1q q p.T = ell1q 1 p.T + Real.log q := by
      unfold ell1q
      rw [Nat.cast_one, one_mul, mul_div_assoc, Real.log_mul (by exact_mod_cast (show q ≠ 0 by omega))
        (by positivity)]
      ring
    have : N₁ - p.T / (2 * π) * ell1q 1 p.T = N - p.T / (2 * π) * ell1q q p.T := by
      rw [hN₁, hell]; field_simp; ring
    rwa [this]
  have hbase : |trGtChiA κ 1 (fun _ => 0) p F - F.a * p.L * N₁| ≤ (|C₀| + |C₁|) * (p.L * Real.sqrt p.X) := by
    have hS0 : 0 ≤ p.L * Real.sqrt p.X := by positivity
    beta_reduce at hC₀ hC₁
    interval_cases κ
    · refine (hC₀ p F hp ((le_max_left _ _).trans hT₀) hF N₁ hN₁b).trans ?_
      exact mul_le_mul_of_nonneg_right (by linarith [le_abs_self C₀, abs_nonneg C₁]) hS0
    · refine (hC₁ p F hp ((le_max_right _ _).trans hT₀) hF N₁ hN₁b).trans ?_
      exact mul_le_mul_of_nonneg_right (by linarith [le_abs_self C₁, abs_nonneg C₀]) hS0
  -- the shift term
  have hshift : |2 * π * F.a * p.d * (Real.log q / (2 * π)) - F.a * p.L * (p.T * (Real.log q / (2 * π)))|
      ≤ Real.log q := by
    have h := abs_two_pi_d_sub_le hL hT0 ha0
    have hc0 : 0 ≤ Real.log q / (2 * π) := div_nonneg hlq (by positivity)
    have e : 2 * π * F.a * p.d * (Real.log q / (2 * π)) - F.a * p.L * (p.T * (Real.log q / (2 * π)))
        = (2 * π * F.a * p.d - F.a * p.L * p.T) * (Real.log q / (2 * π)) := by ring
    rw [e, abs_mul, abs_of_nonneg hc0]
    calc |2 * π * F.a * p.d - F.a * p.L * p.T| * (Real.log q / (2 * π))
        ≤ 2 * π * F.a * (Real.log q / (2 * π)) := mul_le_mul_of_nonneg_right h hc0
      _ = F.a * Real.log q := by field_simp
      _ ≤ 1 * Real.log q := mul_le_mul_of_nonneg_right ha1 hlq
      _ = Real.log q := one_mul _
  -- the prime part
  have hP : |(p.L)⁻¹ * ∑ k ∈ Finset.range p.d, ∫ r, F.phiHat r ^ 2 * PXc c p.X (p.tau k + r)|
      ≤ 3 / Real.log 2 * (p.L * Real.sqrt p.X) := by
    have h := sum_P_part_chi_bound hF.toCoreW hc
    have hconv : ∑ n ∈ Finset.Ioc 0 ⌊p.X⌋₊, (Λ n : ℝ) * (n : ℝ) ^ (-(1/2 : ℝ))
        = ∑ n ∈ Finset.Ioc 0 ⌊p.X⌋₊, Λ n / Real.sqrt n := by
      refine Finset.sum_congr rfl fun n _ => ?_
      rw [Real.rpow_neg (Nat.cast_nonneg n), ← Real.sqrt_eq_rpow, div_eq_mul_inv]
    rw [hconv] at h
    have h3 := hx₀ p.X hX
    rw [abs_mul, abs_of_pos (inv_pos.mpr hL)]
    calc (p.L)⁻¹ * |∑ k ∈ Finset.range p.d, ∫ r, F.phiHat r ^ 2 * PXc c p.X (p.tau k + r)|
        ≤ (p.L)⁻¹ * (p.L ^ 2 / Real.log 2 * (3 * Real.sqrt p.X)) := by
          refine mul_le_mul_of_nonneg_left (h.trans ?_) (by positivity)
          exact mul_le_mul_of_nonneg_left h3 (by positivity)
      _ = 3 / Real.log 2 * (p.L * Real.sqrt p.X) := by field_simp
  rw [trGtChiA_shift hκ hq hc hF.toCoreW hT0]
  have hsplit : trGtChiA κ 1 (fun _ => 0) p F + 2 * π * F.a * p.d * (Real.log q / (2 * π))
        + (p.L)⁻¹ * (∑ k ∈ Finset.range p.d, ∫ r, F.phiHat r ^ 2 * PXc c p.X (p.tau k + r))
        - F.a * p.L * N
      = (trGtChiA κ 1 (fun _ => 0) p F - F.a * p.L * N₁)
        + (2 * π * F.a * p.d * (Real.log q / (2 * π)) - F.a * p.L * (p.T * (Real.log q / (2 * π))))
        + (p.L)⁻¹ * ∑ k ∈ Finset.range p.d, ∫ r, F.phiHat r ^ 2 * PXc c p.X (p.tau k + r) := by
    rw [hN₁]; ring
  refine (le_of_eq (congrArg abs hsplit)).trans ?_
  have htri := abs_add_three (trGtChiA κ 1 (fun _ => 0) p F - F.a * p.L * N₁)
    (2 * π * F.a * p.d * (Real.log q / (2 * π)) - F.a * p.L * (p.T * (Real.log q / (2 * π))))
    ((p.L)⁻¹ * ∑ k ∈ Finset.range p.d, ∫ r, F.phiHat r ^ 2 * PXc c p.X (p.tau k + r))
  have hlqS : Real.log q ≤ Real.log q * (p.L * Real.sqrt p.X) := le_mul_of_one_le_right hlq hS1
  have hS0 : 0 ≤ p.L * Real.sqrt p.X := by linarith
  have hC0 : 0 ≤ |C₀| + |C₁| + 1 + 3 / Real.log 2 := by positivity
  have hfin : (|C₀| + |C₁|) * (p.L * Real.sqrt p.X) + Real.log q * (p.L * Real.sqrt p.X)
        + 3 / Real.log 2 * (p.L * Real.sqrt p.X)
      ≤ (|C₀| + |C₁| + 1 + 3 / Real.log 2) * (1 + Real.log q) * (p.L * Real.sqrt p.X) := by
    have h1 : (|C₀| + |C₁|) ≤ (|C₀| + |C₁|) * (1 + Real.log q) :=
      le_mul_of_one_le_right (by positivity) (by linarith)
    have h2 : 3 / Real.log 2 ≤ 3 / Real.log 2 * (1 + Real.log q) :=
      le_mul_of_one_le_right (by positivity) (by linarith)
    have h3 : Real.log q ≤ 1 * (1 + Real.log q) := by linarith
    nlinarith [mul_le_mul_of_nonneg_right h1 hS0, mul_le_mul_of_nonneg_right h2 hS0,
      mul_le_mul_of_nonneg_right h3 hS0, mul_nonneg (mul_nonneg hlq hS0) (abs_nonneg C₀)]
  linarith

end RHTower
