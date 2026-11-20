import GaloisForLFunctions.RHTower.SteinhausComplexSecondMoment
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity

/-!
# Fractional gradients of multiplicatively shifted Dirichlet sections

Douanla's one-mode fractional-gradient estimate compares the symbol after a
frequency shift with its value at the carrier. Integer modulation n ↦ Mn puts
all logarithmic frequencies on one half-line. Steinhaus orthogonality then
gives the exact mean-square error, with the largest frequency attaining the
operator norm. The relevant bandwidth is log N / log M.
-/

noncomputable section
open Finset Filter Topology MeasureTheory Complex
open _root_.RHTower.SteinhausModel
namespace GaloisForLFunctions.MultiscaleMollifiedZetaField.RandomDirichletJets

/-- Normalized fractional derivative of the modulated section, less the
carrier contribution. The common unit phase of the fractional gradient
is omitted. The shifted arithmetic character is evaluated at M*n. -/
def fractionalModulationError (s : ℝ) (M N : ℕ) (a : ℕ → ℂ) (ω : Omega) : ℂ :=
  (∑ n ∈ Icc 1 N, (((Real.log (M*n:ℕ)/Real.log M)^s:ℝ):ℂ)*a n*X (M*n) ω) -
    X M ω*(∑ n ∈ Icc 1 N, a n*X n ω)

/-- Relative change of the positive-frequency symbol at the outermost mode. -/
def fractionalModulationLoss (s : ℝ) (M N : ℕ) : ℝ :=
  (1+Real.log N/Real.log M)^s-1

private theorem symbol_shift {M n : ℕ} (hM : 2 ≤ M) (hn : 1 ≤ n) (s : ℝ) :
    (Real.log (M*n:ℕ)/Real.log M)^s-1 = fractionalModulationLoss s M n := by
  have hM0 : (0:ℝ)<M := Nat.cast_pos.mpr (by omega)
  have hn0 : (0:ℝ)<n := Nat.cast_pos.mpr hn
  have hL := Real.log_pos (show (1:ℝ)<M by exact_mod_cast (show 1 < M by omega))
  rw [Nat.cast_mul,Real.log_mul hM0.ne' hn0.ne',add_div,div_self hL.ne',fractionalModulationLoss]

private theorem loss_nonneg {M n : ℕ} (hM : 2 ≤ M) (hn : 1 ≤ n) {s : ℝ} (hs : 0 ≤ s) :
    0 ≤ fractionalModulationLoss s M n := by
  have hL : 0 ≤ Real.log M := Real.log_nonneg (by exact_mod_cast (show 1 ≤ M by omega))
  have hQ := div_nonneg (Real.log_nonneg (Nat.one_le_cast.mpr hn)) hL
  exact sub_nonneg.mpr (Real.one_le_rpow (by linarith only [hQ]) hs)

private theorem loss_le {M n N : ℕ} (hM : 2 ≤ M) (hn : 1 ≤ n) (hnN : n ≤ N)
    {s : ℝ} (hs : 0 ≤ s) : fractionalModulationLoss s M n ≤ fractionalModulationLoss s M N := by
  have hL : 0 ≤ Real.log M := Real.log_nonneg (by exact_mod_cast (show 1 ≤ M by omega))
  have hn1 : (1:ℝ) ≤ n := Nat.one_le_cast.mpr hn
  have hlog := Real.log_le_log (zero_lt_one.trans_le hn1) (Nat.cast_le.mpr hnN : (n:ℝ) ≤ N)
  exact sub_le_sub_right (Real.rpow_le_rpow (add_nonneg zero_le_one
    (div_nonneg (Real.log_nonneg hn1) hL)) (add_le_add le_rfl (div_le_div_of_nonneg_right hlog hL)) hs) _

/-- Exact Plancherel formula for the error on a modulated polynomial.
The multiplier remains diagonal even if a prime divides both M and n. -/
theorem fractional_modulation_energy (s : ℝ) {M : ℕ} (hM : 2 ≤ M) (N : ℕ) (a : ℕ → ℂ) :
    (∫ ω, ‖fractionalModulationError s M N a ω‖^2 ∂steinhausMeasure) =
    ∑ n ∈ Icc 1 N, (fractionalModulationLoss s M n)^2*‖a n‖^2 := by
  let b (n : ℕ) : ℂ := (fractionalModulationLoss s M n:ℂ)*a n
  have he (ω : Omega) : fractionalModulationError s M N a ω =
      X M ω*(∑ n ∈ Icc 1 N, b n*X n ω) := by
    rw [fractionalModulationError,mul_sum,mul_sum,←sum_sub_distrib]
    apply sum_congr rfl
    intro n hn
    have hn1 := (mem_Icc.mp hn).1
    rw [X_mul (by omega : M ≠ 0) (by omega : n ≠ 0)]
    have hc := congrArg Complex.ofReal (symbol_shift hM hn1 s)
    simp only [ofReal_sub,ofReal_one] at hc
    dsimp only [b]
    rw [←hc]
    ring
  simp_rw [he,norm_mul,norm_X,one_mul]
  rw [integral_normSq_dpoly_complex _ _ (fun n hn => Nat.ne_of_gt (mem_Icc.mp hn).1)]
  simp only [b,norm_mul,Complex.norm_real,Real.norm_eq_abs,mul_pow,sq_abs]

/-- Optimal squared relative error for all coefficient rows at a fixed
arithmetic cutoff. A single top-frequency character attains equality. -/
theorem optimal_fractional_modulation_energy_iff {s : ℝ} (hs : 0 ≤ s) {M N : ℕ}
    (hM : 2 ≤ M) (hN : 1 ≤ N) (C : ℝ) :
    (∀ a : ℕ → ℂ, (∫ ω, ‖fractionalModulationError s M N a ω‖^2 ∂steinhausMeasure) ≤
      C*∑ n ∈ Icc 1 N, ‖a n‖^2) ↔ (fractionalModulationLoss s M N)^2 ≤ C := by
  constructor
  · intro h
    have hb := h (fun n => if n=N then 1 else 0)
    rw [fractional_modulation_energy s hM] at hb
    have hn : N ∈ Icc 1 N := mem_Icc.mpr ⟨hN,le_rfl⟩
    simpa [apply_ite,norm_one,norm_zero,mul_ite,hn] using hb
  · intro h a
    rw [fractional_modulation_energy s hM,mul_sum]
    apply sum_le_sum
    intro n hn
    have hnn := mem_Icc.mp hn
    exact mul_le_mul_of_nonneg_right ((pow_le_pow_left₀ (loss_nonneg hM hnn.1 hs)
      (loss_le hM hnn.1 hnn.2 hs) 2).trans h) (sq_nonneg _)

/-- For orders between zero and one, collinear logarithmic frequencies
give a linear bound in the relative bandwidth. -/
theorem fractional_modulation_loss_le_bandwidth {s : ℝ} (hs : s ≤ 1) {M N : ℕ}
    (hM : 2 ≤ M) (hN : 1 ≤ N) :
    fractionalModulationLoss s M N ≤ Real.log N/Real.log M := by
  have hL : 0 ≤ Real.log M := Real.log_nonneg (by exact_mod_cast (show 1 ≤ M by omega))
  have hq := div_nonneg (Real.log_nonneg (Nat.one_le_cast.mpr hN)) hL
  have H := Real.rpow_le_self_of_one_le (show 1 ≤ 1+Real.log N/Real.log M by linarith only [hq]) hs
  unfold fractionalModulationLoss
  linarith only [H]

/-- At N=M^j the exact norm is independent of the integer carrier M. -/
theorem fractional_modulation_loss_at_power (s : ℝ) {M : ℕ} (hM : 2 ≤ M) (j : ℕ) :
    fractionalModulationLoss s M (M^j)=(1+(j:ℝ))^s-1 := by
  have hL := Real.log_pos (show (1:ℝ)<M by exact_mod_cast (show 1 < M by omega))
  rw [fractionalModulationLoss,Nat.cast_pow,Real.log_pow,mul_div_cancel_right₀ _ hL.ne']

/-- Uniform approximation along a moving arithmetic window holds exactly
when the logarithmic bandwidth is negligible relative to the carrier. -/
theorem fractional_modulation_loss_tendsto_zero_iff {s : ℝ} (hs : 0 < s) (M N : ℕ → ℕ)
    (hM : ∀ k, 2 ≤ M k) (hN : ∀ k, 1 ≤ N k) :
    Tendsto (fun k => fractionalModulationLoss s (M k) (N k)) atTop (𝓝 0) ↔
    Tendsto (fun k => Real.log (N k)/Real.log (M k)) atTop (𝓝 0) := by
  let Q (k : ℕ) := Real.log (N k)/Real.log (M k)
  have hq (k : ℕ) : 0 ≤ Q k := div_nonneg (Real.log_nonneg (Nat.one_le_cast.mpr (hN k)))
    (Real.log_nonneg (by exact_mod_cast (show 1 ≤ M k by have := hM k; omega)))
  constructor
  · intro h
    have h1 := (tendsto_const_nhds (x:=(1:ℝ))).add h
    have h2 := h1.rpow_const (p:=s⁻¹) (Or.inr (inv_nonneg.mpr hs.le))
    have hcancel (k : ℕ) : (1+fractionalModulationLoss s (M k) (N k))^s⁻¹ - 1 = Q k := by
      change (1+((1+Q k)^s-1))^s⁻¹-1=Q k
      rw [show 1+((1+Q k)^s-1)=(1+Q k)^s by ring,
        ←Real.rpow_mul (add_nonneg zero_le_one (hq k)),mul_inv_cancel₀ hs.ne',Real.rpow_one]
      ring
    have H := h2.sub (tendsto_const_nhds (x:=(1:ℝ)))
    simpa only [Pi.sub_apply,Pi.add_apply,add_zero,Real.one_rpow,sub_self,hcancel] using H
  · intro h
    have h1 := (tendsto_const_nhds (x:=(1:ℝ))).add h
    have H := (h1.rpow_const (p:=s) (Or.inr hs.le)).sub (tendsto_const_nhds (x:=(1:ℝ)))
    simpa only [fractionalModulationLoss,Pi.sub_apply,Pi.add_apply,add_zero,Real.one_rpow,sub_self] using H

#print axioms fractional_modulation_energy
#print axioms optimal_fractional_modulation_energy_iff
#print axioms fractional_modulation_loss_at_power
#print axioms fractional_modulation_loss_tendsto_zero_iff

end GaloisForLFunctions.MultiscaleMollifiedZetaField.RandomDirichletJets
