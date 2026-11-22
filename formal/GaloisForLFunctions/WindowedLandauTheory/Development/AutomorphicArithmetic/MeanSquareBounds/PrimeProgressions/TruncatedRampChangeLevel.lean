import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.MeanSquareBounds.PrimeProgressions.EulerRampCorrection
import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.MeanSquareBounds.PrimeProgressions.TruncatedRampStatement
import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.MeanSquareBounds.PrimeProgressions.ZeroChangeLevel

/-! The finite zero sum transfers from an inducing character to the ambient modulus. -/

open Complex Finset WindowedLandauTheory.HC WindowedLandauTheory.ZeroFreeDirichlet

noncomputable section

namespace QH.PrimeProgressions

theorem truncated_ramp_changeLevel {N M : ℕ} [NeZero N] [NeZero M] (hNM : N ∣ M)
    (ψ : DirichletCharacter ℂ N) {κ T C : ℝ} (hκ : κ ≤ 1 / 20) (hT : 2 ≤ T) (hC : 0 ≤ C)
    (h : TruncatedRamp ψ κ T C) : TruncatedRamp (ψ.changeLevel hNM) κ T (C + 8) := by
  obtain ⟨Z, K, hZ, hpos, hcount, herror⟩ := h
  obtain ⟨E, hE⟩ := normalized_ramp_changeLevel hNM ψ
  let χ := ψ.changeLevel hNM
  have hM : (1 : ℝ) ≤ M := by exact_mod_cast NeZero.pos M
  have hN : (1 : ℝ) ≤ N := by exact_mod_cast NeZero.pos N
  have hle : (N : ℝ) ≤ M := by exact_mod_cast Nat.le_of_dvd (NeZero.pos M) hNM
  have hlog {a : ℝ} (ha : 0 < a) : Real.log ((N : ℝ) * a) ≤ Real.log ((M : ℝ) * a) :=
    Real.log_le_log (by positivity) (mul_le_mul_of_nonneg_right hle ha.le)
  have hmain (y : ℝ) : rampMain χ y = rampMain ψ y := by
    by_cases hψ : ψ = 1 <;>
      simp [rampMain, χ, DirichletCharacter.changeLevel_eq_one_iff, hψ]
  have hzero (ρ : ℂ) : ρ ∈ Z ↔ IsLZero χ ρ ∧ Cutoff κ T ρ := by
    rw [hZ]
    constructor
    · rintro ⟨hz, hr⟩
      have hp : 0 < ρ.re := by have := hr.1; linarith
      exact ⟨(zero_changeLevel hNM ψ hp hz.1).1.mpr hz, hr⟩
    · rintro ⟨hz, hr⟩
      have hp : 0 < ρ.re := by have := hr.1; linarith
      have hn : ρ ≠ 1 := by
        intro e
        have hr' := re_lt_one_of_isLZero hz
        rw [e, one_re] at hr'
        exact lt_irrefl _ hr'
      exact ⟨(zero_changeLevel hNM ψ hp (Or.inr hn)).1.mp hz, hr⟩
  have hord (ρ : ℂ) (hρ : ρ ∈ Z) : analyticOrderNatAt χ.LFunction ρ = analyticOrderNatAt ψ.LFunction ρ := by
    obtain ⟨hz, hr⟩ := (hZ ρ).mp hρ
    have hp : 0 < ρ.re := by have := hr.1; linarith
    exact (zero_changeLevel hNM ψ hp hz.1).2
  refine ⟨Z, K + E, hzero, fun ρ hρ => (hord ρ hρ).symm ▸ hpos ρ hρ, ?_, ?_⟩
  · intro t
    have he : (∑ ρ ∈ Z.filter (fun ρ => |ρ.im - t| ≤ 1), (analyticOrderNatAt χ.LFunction ρ : ℝ)) =
        ∑ ρ ∈ Z.filter (fun ρ => |ρ.im - t| ≤ 1), (analyticOrderNatAt ψ.LFunction ρ : ℝ) :=
      sum_congr rfl fun ρ hρ => by rw [hord ρ (mem_filter.mp hρ).1]
    rw [he]
    have hMlog : 0 ≤ Real.log ((M : ℝ) * (|t| + 2)) :=
      Real.log_nonneg ((show (1 : ℝ) ≤ |t| + 2 by linarith [abs_nonneg t]).trans
        (le_mul_of_one_le_left (by positivity) hM))
    exact (hcount t).trans ((mul_le_mul_of_nonneg_left (hlog (by positivity)) hC).trans
      (mul_le_mul_of_nonneg_right (by linarith) hMlog))
  · intro y hy
    have hsum : (∑ ρ ∈ Z, (analyticOrderNatAt χ.LFunction ρ : ℂ) * QH.zeroKernel y ρ) =
        ∑ ρ ∈ Z, (analyticOrderNatAt ψ.LFunction ρ : ℂ) * QH.zeroKernel y ρ :=
      sum_congr rfl fun ρ hρ => by rw [hord ρ hρ]
    let R := An.sumLamChi ψ y / (y : ℂ) - K - rampMain ψ y +
      ∑ ρ ∈ Z, (analyticOrderNatAt ψ.LFunction ρ : ℂ) * QH.zeroKernel y ρ
    let D := An.sumLamChi χ y / (y : ℂ) - An.sumLamChi ψ y / (y : ℂ) - E
    have hr : An.sumLamChi χ y / (y : ℂ) - (K + E) - rampMain χ y +
        ∑ ρ ∈ Z, (analyticOrderNatAt χ.LFunction ρ : ℂ) * QH.zeroKernel y ρ = R + D := by
      rw [hmain, hsum]
      dsimp only [R, D]
      ring
    rw [hr]
    refine (norm_add_le R D).trans ((add_le_add (herror y hy) (hE y hy)).trans ?_)
    have hlogN : 0 ≤ Real.log ((N : ℝ) * T) :=
      Real.log_nonneg ((show (1 : ℝ) ≤ T by linarith).trans (le_mul_of_one_le_left (by positivity) hN))
    have hlogT := hlog (show 0 < T by linarith)
    have hbound : C * ((N : ℝ) ^ 3 * y ^ (-(κ / 2)) + Real.log ((N : ℝ) * T) ^ 2 / T) ≤
        C * ((M : ℝ) ^ 3 * y ^ (-(κ / 2)) + Real.log ((M : ℝ) * T) ^ 2 / T) := by
      apply mul_le_mul_of_nonneg_left _ hC
      exact add_le_add
        (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (Nat.cast_nonneg _) hle 3) (by positivity))
        (div_le_div_of_nonneg_right (pow_le_pow_left₀ hlogN hlogT 2) (by linarith))
    have hy₀ : 0 ≤ y := by linarith
    have hpow : (Real.sqrt y)⁻¹ ≤ y ^ (-(κ / 2)) := by
      rw [Real.sqrt_eq_rpow, ← Real.rpow_neg hy₀]
      exact Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
    have hMp : (M : ℝ) ^ 2 ≤ (M : ℝ) ^ 3 := pow_le_pow_right₀ hM (by norm_num)
    have hd : 8 * (M : ℝ) ^ 2 / Real.sqrt y ≤ 8 * ((M : ℝ) ^ 3 * y ^ (-(κ / 2))) := by
      rw [div_eq_mul_inv, mul_assoc]
      exact mul_le_mul_of_nonneg_left (mul_le_mul hMp hpow (by positivity) (by positivity)) (by norm_num)
    have htail : 0 ≤ Real.log ((M : ℝ) * T) ^ 2 / T := by positivity
    nlinarith only [hbound, hd, htail]

theorem TruncatedRamp.mono {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N} {κ T C C' : ℝ}
    (h : TruncatedRamp χ κ T C) (hC : C ≤ C') (hT : 2 ≤ T) : TruncatedRamp χ κ T C' := by
  obtain ⟨Z, K, hZ, hpos, hcount, herror⟩ := h
  refine ⟨Z, K, hZ, hpos, ?_, fun y hy => (herror y hy).trans
    (mul_le_mul_of_nonneg_right hC (by positivity))⟩
  intro t
  have hN : (1 : ℝ) ≤ N := by exact_mod_cast NeZero.pos N
  have hlog : 0 ≤ Real.log ((N : ℝ) * (|t| + 2)) :=
    Real.log_nonneg ((show (1 : ℝ) ≤ |t| + 2 by linarith [abs_nonneg t]).trans
      (le_mul_of_one_le_left (by positivity) hN))
  exact (hcount t).trans (mul_le_mul_of_nonneg_right hC hlog)

end QH.PrimeProgressions
