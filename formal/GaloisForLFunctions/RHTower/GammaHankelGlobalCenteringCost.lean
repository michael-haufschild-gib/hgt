import GaloisForLFunctions.RHTower.MobiusLaplaceGammaHankelWall
import GaloisForLFunctions.RHTower.MertensThirdTheorem

/-!
# Global centering cost of the Gamma--Hankel energy

For real coefficients `a_1, …, a_N` let
`E_N(a; r) = Γ(r) ∑_{m,n ≤ N} a_m a_n / (m + n)^r`.
Polarization of the quadratic form gives, for every real `b`,

`2 E_N(a) + 2 E_N(a - b) = E_N(2a - b) + b² E_N(1)`,

so positivity of the Gamma--Hankel form yields
`E_N(a) + E_N(a - b) ≥ b² E_N(1) / 2 ≥ Γ(r) b² N² / (2 (2N)^r)`, with equality in the first
bound at `a = b/2`.  With the squared Mertens product `b_N = ∏_{p ≤ N} (1 - 1/p)²` as the
centering constant, Mertens' third theorem makes the lower bound of order `N^{2-r} / (log N)^4`,
so for `0 < r < 2` the two energies cannot both stay bounded, for every triangular coefficient
array.
-/

open Filter Topology Asymptotics
open scoped BigOperators

namespace RHTower

noncomputable section

/-- Polarization of the Gamma--Hankel form against a constant shift:
`2E(a) + 2E(a - b) = E(2a - b) + b² E(1)`. -/
theorem finiteGammaHankelEnergy_centering_polarization (a : ℕ → ℝ) (b : ℝ) (N : ℕ) (r : ℝ) :
    2 * finiteGammaHankelEnergy a N r + 2 * finiteGammaHankelEnergy (fun n => a n - b) N r =
      finiteGammaHankelEnergy (fun n => 2 * a n - b) N r +
        b ^ 2 * finiteGammaHankelEnergy (fun _ => 1) N r := by
  simp only [finiteGammaHankelEnergy, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun m _ => Finset.sum_congr rfl fun n _ => ?_
  ring

/-- **Centering lower bound.**  `E_N(a) + E_N(a - b) ≥ b² E_N(1) / 2` for `r > 0`. -/
theorem finiteGammaHankelEnergy_add_centered_ge (a : ℕ → ℝ) (b : ℝ) (N : ℕ) {r : ℝ}
    (hr : 0 < r) :
    b ^ 2 * finiteGammaHankelEnergy (fun _ => 1) N r / 2 ≤
      finiteGammaHankelEnergy a N r + finiteGammaHankelEnergy (fun n => a n - b) N r := by
  have h := finiteGammaHankelEnergy_centering_polarization a b N r
  have h0 := finiteGammaHankelEnergy_nonneg (fun n => 2 * a n - b) N hr
  linarith

/-- The constant `1/2` is sharp: equality holds for the constant coefficients `a_n = b/2`. -/
theorem finiteGammaHankelEnergy_add_centered_half (b : ℝ) (N : ℕ) (r : ℝ) :
    finiteGammaHankelEnergy (fun _ => b / 2) N r +
        finiteGammaHankelEnergy (fun _ => b / 2 - b) N r =
      b ^ 2 * finiteGammaHankelEnergy (fun _ => 1) N r / 2 := by
  have h := finiteGammaHankelEnergy_centering_polarization (fun _ => b / 2) b N r
  have hz : 2 * (b / 2) - b = 0 := by ring
  have h0 : finiteGammaHankelEnergy (fun _ => 2 * (b / 2) - b) N r = 0 := by
    simp [finiteGammaHankelEnergy, hz]
  beta_reduce at h
  rw [h0] at h
  linarith

/-- The flat source has Gamma--Hankel energy at least `Γ(r) N² / (2N)^r`. -/
theorem finiteGammaHankelEnergy_one_ge (N : ℕ) {r : ℝ} (hr : 0 < r) :
    Real.Gamma r * (N : ℝ) ^ 2 / ((2 * N : ℝ) ^ r) ≤
      finiteGammaHankelEnergy (fun _ => 1) N r := by
  have hG := Real.Gamma_pos_of_pos hr
  have hterm : ∀ m ∈ Finset.range N, ∀ n ∈ Finset.range N,
      1 / ((2 * N : ℝ) ^ r) ≤ 1 * 1 / (((m + n + 2 : ℕ) : ℝ) ^ r) := by
    intro m hm n hn
    rw [Finset.mem_range] at hm hn
    rw [one_mul]
    apply one_div_le_one_div_of_le (by positivity)
    apply Real.rpow_le_rpow (by positivity) _ hr.le
    have : m + n + 2 ≤ 2 * N := by omega
    exact_mod_cast this
  have hsum := Finset.sum_le_sum fun m hm => Finset.sum_le_sum fun n hn => hterm m hm n hn
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at hsum
  rw [finiteGammaHankelEnergy]
  calc Real.Gamma r * (N : ℝ) ^ 2 / ((2 * N : ℝ) ^ r)
      = Real.Gamma r * ((N : ℝ) * ((N : ℝ) * (1 / ((2 * N : ℝ) ^ r)))) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hsum hG.le

/-- **Theorem (first part).**  For `r > 0`, `N ≥ 1` and real `b`,
`E_N(a) + E_N(a - b) ≥ b² E_N(1)/2 ≥ Γ(r) b² N² / (2 (2N)^r)`. -/
theorem finiteGammaHankelEnergy_centering_chain (a : ℕ → ℝ) (b : ℝ) (N : ℕ) {r : ℝ}
    (hr : 0 < r) :
    b ^ 2 * finiteGammaHankelEnergy (fun _ => 1) N r / 2 ≤
        finiteGammaHankelEnergy a N r + finiteGammaHankelEnergy (fun n => a n - b) N r ∧
      Real.Gamma r * b ^ 2 * (N : ℝ) ^ 2 / (2 * (2 * N : ℝ) ^ r) ≤
        b ^ 2 * finiteGammaHankelEnergy (fun _ => 1) N r / 2 := by
  refine ⟨finiteGammaHankelEnergy_add_centered_ge a b N hr, ?_⟩
  have h := mul_le_mul_of_nonneg_left (finiteGammaHankelEnergy_one_ge N hr) (sq_nonneg b)
  calc Real.Gamma r * b ^ 2 * (N : ℝ) ^ 2 / (2 * (2 * N : ℝ) ^ r)
      = b ^ 2 * (Real.Gamma r * (N : ℝ) ^ 2 / ((2 * N : ℝ) ^ r)) / 2 := by ring
    _ ≤ _ := by linarith

/-- `P_N^4 N^s → ∞` for every `s > 0`, where `P_N = ∏_{p ≤ N} (1 - 1/p)`. -/
theorem tendsto_mertensPrimeProduct_pow_four_mul_rpow {s : ℝ} (hs : 0 < s) :
    Tendsto (fun N : ℕ => mertensPrimeProduct N ^ 4 * (N : ℝ) ^ s) atTop atTop := by
  have hc : 0 < Real.exp (-Real.eulerMascheroniConstant) ^ 4 := by positivity
  have h1 := tendsto_mertensPrimeProduct_mul_log.pow 4
  have hlo := (isLittleO_log_rpow_rpow_atTop (4 : ℝ) hs).tendsto_div_nhds_zero
  have hpos : ∀ᶠ x : ℝ in atTop, 0 < Real.log x ^ (4 : ℝ) / x ^ s := by
    filter_upwards [eventually_gt_atTop 1] with x hx
    have := Real.log_pos hx
    positivity
  have h2 : Tendsto (fun x : ℝ => (Real.log x ^ (4 : ℝ) / x ^ s)⁻¹) atTop atTop :=
    Tendsto.inv_tendsto_nhdsGT_zero (tendsto_nhdsWithin_iff.mpr ⟨hlo, hpos⟩)
  have h3 := h2.comp tendsto_natCast_atTop_atTop
  refine (Tendsto.pos_mul_atTop hc h1 h3).congr' ?_
  filter_upwards [eventually_gt_atTop 1] with N hN
  have hN1 : (1 : ℝ) < N := by exact_mod_cast hN
  have hlog : Real.log N ≠ 0 := (Real.log_pos hN1).ne'
  have hNs : (N : ℝ) ^ s ≠ 0 := (Real.rpow_pos_of_pos (by linarith) s).ne'
  simp only [Function.comp_apply, Real.rpow_ofNat]
  field_simp

/-- **Divergence of the centering cost.**  For `0 < r < 2`, every triangular array `a_N` and the
squared Mertens centering `b_N = P_N²`, `E_N(a_N) + E_N(a_N - b_N) → ∞`. -/
theorem tendsto_finiteGammaHankelEnergy_centering_cost (a : ℕ → ℕ → ℝ) {r : ℝ} (hr0 : 0 < r)
    (hr2 : r < 2) :
    Tendsto (fun N => finiteGammaHankelEnergy (a N) N r +
      finiteGammaHankelEnergy (fun n => a N n - mertensPrimeProduct N ^ 2) N r) atTop atTop := by
  have hG := Real.Gamma_pos_of_pos hr0
  have hc : 0 < Real.Gamma r / (2 * 2 ^ r) := by positivity
  have h := (tendsto_mertensPrimeProduct_pow_four_mul_rpow (sub_pos.mpr hr2)).const_mul_atTop hc
  refine tendsto_atTop_mono' atTop ?_ h
  filter_upwards [eventually_ge_atTop 1] with N hN
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  obtain ⟨h1, h2⟩ := finiteGammaHankelEnergy_centering_chain (a N) (mertensPrimeProduct N ^ 2) N hr0
  have heq : Real.Gamma r / (2 * 2 ^ r) * (mertensPrimeProduct N ^ 4 * (N : ℝ) ^ (2 - r)) =
      Real.Gamma r * (mertensPrimeProduct N ^ 2) ^ 2 * (N : ℝ) ^ 2 / (2 * (2 * N : ℝ) ^ r) := by
    have h2r : (0 : ℝ) < 2 ^ r := Real.rpow_pos_of_pos (by norm_num) r
    have hNr : (0 : ℝ) < (N : ℝ) ^ r := Real.rpow_pos_of_pos hN0 r
    rw [Real.mul_rpow (by norm_num) hN0.le, Real.rpow_sub hN0, Real.rpow_two]
    field_simp
  rw [heq]
  linarith

/-- **Eventual disjunction.**  For every `A, B`, eventually `E_N(a_N) > A` or
`E_N(a_N - b_N) > B`. -/
theorem eventually_centering_energy_gt (a : ℕ → ℕ → ℝ) {r : ℝ} (hr0 : 0 < r) (hr2 : r < 2)
    (A B : ℝ) :
    ∀ᶠ N in atTop, A < finiteGammaHankelEnergy (a N) N r ∨
      B < finiteGammaHankelEnergy (fun n => a N n - mertensPrimeProduct N ^ 2) N r := by
  filter_upwards [(tendsto_finiteGammaHankelEnergy_centering_cost a hr0 hr2).eventually_gt_atTop
    (A + B)] with N hN
  by_contra h
  rw [not_or, not_lt, not_lt] at h
  linarith [h.1, h.2]

/-- The exponents `r_k = 1 + 1/(k+2)` lie in the critical range `0 < r_k < 2`. -/
theorem criticalHankelExponent_mem (k : ℕ) :
    0 < 1 + 1 / ((k : ℝ) + 2) ∧ 1 + 1 / ((k : ℝ) + 2) < 2 := by
  have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  refine ⟨by positivity, ?_⟩
  have : 1 / ((k : ℝ) + 2) < 1 := by
    rw [div_lt_one (by linarith)]; linarith
  linarith

/-- **Möbius instance.**  For the Möbius coefficients `μ(1), …, μ(N)` and every `r_k`, the sum
of the physical and the globally centered Gamma--Hankel energies diverges. -/
theorem tendsto_mobius_centering_cost (k : ℕ) :
    Tendsto (fun N => finiteGammaHankelEnergy shiftedMobiusRealCoefficient N
        (1 + 1 / ((k : ℝ) + 2)) +
      finiteGammaHankelEnergy (fun n => shiftedMobiusRealCoefficient n - mertensPrimeProduct N ^ 2)
        N (1 + 1 / ((k : ℝ) + 2))) atTop atTop :=
  tendsto_finiteGammaHankelEnergy_centering_cost (fun _ => shiftedMobiusRealCoefficient)
    (criticalHankelExponent_mem k).1 (criticalHankelExponent_mem k).2

/-- **Möbius eventual disjunction** at every `r_k`. -/
theorem eventually_mobius_centering_energy_gt (k : ℕ) (A B : ℝ) :
    ∀ᶠ N in atTop, A < finiteGammaHankelEnergy shiftedMobiusRealCoefficient N
        (1 + 1 / ((k : ℝ) + 2)) ∨
      B < finiteGammaHankelEnergy
        (fun n => shiftedMobiusRealCoefficient n - mertensPrimeProduct N ^ 2) N
        (1 + 1 / ((k : ℝ) + 2)) :=
  eventually_centering_energy_gt (fun _ => shiftedMobiusRealCoefficient)
    (criticalHankelExponent_mem k).1 (criticalHankelExponent_mem k).2 A B

end

end RHTower
