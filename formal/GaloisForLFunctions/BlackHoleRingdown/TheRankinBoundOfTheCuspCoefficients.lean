import GaloisForLFunctions.BlackHoleRingdown.TheSmoothedRankinSelbergSums

/-!
# Rankin's bound for the cusp coefficients

For a cusp form `g` of the modular horizon with Whittaker coefficients `ρ(n)` there is `δ > 0` with

  `|ρ(n)| ≤ C |n|^{½ - δ}`   (`rankin_bound`),

an improvement over the bound `|ρ(n)| ≪ |n|^{½}` that follows from the mean-square law alone. In ringdown
terms: no single horocyclic harmonic of a cusp mode carries a fixed fraction of the energy of its frequency
band.

**Proof.** With `f(m) = |ρ(m)|² + |ρ(-m)|²`, the smoothed-sum estimate at `y = 1/n` and width `Δ = n^{-β}`,
`β = 1/(4(N+1))`, reads `Σ_m f(m)φ_Δ(m/n) ≤ A e n + K n^{β(N+1)} n^{3/4}`. All terms are nonnegative, and the
`m = n` term is `f(n) G(0)/Δ = f(n) n^β/(2√π)`. Hence
`f(n) ≤ 2√π(A e n^{1-β} + K n^{βN + 3/4}) = 2√π(Ae + K) n^{1-β}`, since `βN + ¾ = 1 - β`.
Summability of the nonnegative series: for `my ≥ e^8`, `G(log(my)/Δ) ≤ (my)^{-2}/(2√π)`.
-/

open Complex MeasureTheory Set Filter Topology Asymptotics
open scoped MatrixGroups UpperHalfPlane

noncomputable section

namespace GaloisForLFunctions.BlackHoleRingdown

open _root_.RHTower GaloisForLFunctions.HTGeometry GaloisForLFunctions.RHTower.DeckPointPair

namespace CuspRB

open HeckeCusp CuspL CuspRSC CuspMS CuspSRS

variable {lamE : ℝ} {g : UpperHalfPlane → ℂ} {ρ : ℤ → ℂ}

/-- The real summand `f(m) φ_Δ(m y)`. -/
def smTerm (ρ : ℤ → ℂ) (Δ y : ℝ) (m : ℕ) : ℝ :=
  rsCoeff ρ m * (smoothAFELogGaussian (Real.log (m * y) / Δ) / Δ)

theorem smSum_eq_ofReal (Δ y : ℝ) : smSum ρ Δ y = ((∑' m : ℕ, smTerm ρ Δ y m : ℝ) : ℂ) := by
  rw [Complex.ofReal_tsum]
  unfold smSum smTerm lgW
  push_cast
  rfl

theorem smTerm_nonneg {Δ : ℝ} (hΔ : 0 < Δ) (y : ℝ) (m : ℕ) : 0 ≤ smTerm ρ Δ y m :=
  mul_nonneg (rsCoeff_nonneg m) (div_nonneg (smoothAFELogGaussian_nonneg _) hΔ.le)

theorem summable_smTerm (hg : g ∈ cuspSpace lamE) (hρ0 : ρ 0 = 0)
    (hρ : ∀ n : ℤ, ∀ y, 0 < y → fourierCoeff g n y = ρ n * (Real.sqrt y : ℂ) *
      modifiedBesselKOrder (2 * Real.pi * |(n : ℝ)| * y) (nu lamE)) {Δ : ℝ} (hΔ : 0 < Δ) (hΔ1 : Δ ≤ 1)
    {y : ℝ} (hy : 0 < y) : Summable (smTerm ρ Δ y) := by
  have hS := summable_nterm hg hρ0 hρ (σ := 2) (by norm_num)
  have hpi : 0 < 2 * Real.sqrt Real.pi := by positivity
  refine Summable.of_norm_bounded_eventually
    (g := fun m => (y ^ (-(2 : ℝ)) / (2 * Real.sqrt Real.pi * Δ)) *
      nterm (fun n => ((rsCoeff ρ n : ℝ) : ℂ)) 2 m) (hS.mul_left _) ?_
  rw [Nat.cofinite_eq_atTop]
  filter_upwards [eventually_ge_atTop (⌈Real.exp 8 / y⌉₊ + 1)] with m hm
  have hm1 : 1 ≤ m := le_trans (Nat.le_add_left 1 _) hm
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm1
  have hmy : Real.exp 8 ≤ m * y := by
    have h1 : Real.exp 8 / y ≤ ⌈Real.exp 8 / y⌉₊ := Nat.le_ceil _
    have h2 : ((⌈Real.exp 8 / y⌉₊ : ℕ) : ℝ) ≤ m := by exact_mod_cast le_trans (Nat.le_succ _) hm
    rw [div_le_iff₀ hy] at h1
    nlinarith
  have hmy0 : 0 < (m : ℝ) * y := by positivity
  have hlog : 8 ≤ Real.log (m * y) := by
    rw [← Real.log_exp 8]; exact Real.log_le_log (Real.exp_pos _) hmy
  have hG : smoothAFELogGaussian (Real.log (m * y) / Δ) ≤ ((m : ℝ) * y) ^ (-(2 : ℝ)) / (2 * Real.sqrt Real.pi) := by
    unfold smoothAFELogGaussian
    apply div_le_div_of_nonneg_right _ hpi.le
    rw [Real.rpow_def_of_pos hmy0]
    apply Real.exp_le_exp.2
    have hL := Real.log (m * y)
    have h1 : Real.log (m * y) ^ 2 ≤ (Real.log (m * y) / Δ) ^ 2 := by
      rw [div_pow]; apply le_div_self (sq_nonneg _) (by positivity)
      nlinarith
    nlinarith
  rw [Real.norm_of_nonneg (smTerm_nonneg hΔ y m)]
  unfold smTerm nterm
  simp only [Nat.pos_iff_ne_zero.1 hm1, if_false, Complex.norm_real,
    Real.norm_of_nonneg (rsCoeff_nonneg m)]
  calc rsCoeff ρ m * (smoothAFELogGaussian (Real.log (m * y) / Δ) / Δ)
      ≤ rsCoeff ρ m * (((m : ℝ) ^ (-(2 : ℝ)) * y ^ (-(2 : ℝ))) / (2 * Real.sqrt Real.pi) / Δ) := by
        gcongr
        · exact rsCoeff_nonneg m
        · rw [← Real.mul_rpow hm0.le hy.le]; exact hG
    _ = y ^ (-(2 : ℝ)) / (2 * Real.sqrt Real.pi * Δ) * (rsCoeff ρ m / (m : ℝ) ^ (2 : ℝ)) := by
        rw [Real.rpow_neg hm0.le]; field_simp

/-- **Rankin's bound, in mean-square form**: `f(n) ≤ C n^{1-β}` for some `β > 0`. -/
theorem exists_rsCoeff_le (hg : g ∈ cuspSpace lamE) (hρ0 : ρ 0 = 0)
    (hρ : ∀ n : ℤ, ∀ y, 0 < y → fourierCoeff g n y = ρ n * (Real.sqrt y : ℂ) *
      modifiedBesselKOrder (2 * Real.pi * |(n : ℝ)| * y) (nu lamE)) :
    ∃ C β : ℝ, 0 ≤ C ∧ 0 < β ∧ ∀ n : ℕ, 1 ≤ n → rsCoeff ρ n ≤ C * (n : ℝ) ^ (1 - β) := by
  obtain ⟨K, N, hK, hb⟩ := norm_smSum_sub_le hg hρ0 hρ
  set A := msConst lamE g with hAdef
  have hA : 0 ≤ A := by
    simp only [hAdef, msConst]
    have : 0 ≤ ∫ z in ModularGroup.fd, ‖g z‖ ^ 2 := integral_nonneg fun z => sq_nonneg _
    positivity
  set β : ℝ := 1 / (4 * ((N : ℝ) + 1)) with hβdef
  have hβ : 0 < β := by positivity
  refine ⟨2 * Real.sqrt Real.pi * (A * Real.exp 1 + K), β, by positivity, hβ, fun n hn => ?_⟩
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  set u := (n : ℝ) ^ β with hudef
  have hu : 1 ≤ u := Real.one_le_rpow hn1 hβ.le
  have hu0 : 0 < u := by linarith
  set Δ := u⁻¹ with hΔdef
  have hΔ : 0 < Δ := inv_pos.2 hu0
  have hΔ1 : Δ ≤ 1 := inv_le_one_of_one_le₀ hu
  set y := (n : ℝ)⁻¹ with hydef
  have hy : 0 < y := inv_pos.2 hn0
  have hbound := hb Δ hΔ hΔ1 y hy
  have hmain : (A : ℂ) * Complex.exp (Δ ^ 2) * ((y : ℂ)⁻¹ * Complex.exp (-(y : ℂ))) =
      ((A * Real.exp (Δ ^ 2) * (y⁻¹ * Real.exp (-y)) : ℝ) : ℂ) := by push_cast; ring
  rw [smSum_eq_ofReal, hmain, ← ofReal_sub, Complex.norm_real, Real.norm_eq_abs] at hbound
  have hupper := (abs_le.1 hbound).2
  have hsum := summable_smTerm hg hρ0 hρ hΔ hΔ1 hy
  have hlow := hsum.le_tsum n (fun j _ => smTerm_nonneg hΔ y j)
  have hterm : smTerm ρ Δ y n = rsCoeff ρ n * u / (2 * Real.sqrt Real.pi) := by
    unfold smTerm
    rw [show (n : ℝ) * y = 1 by simp only [hydef]; field_simp, Real.log_one, zero_div]
    unfold smoothAFELogGaussian
    simp only [hΔdef]
    norm_num
    field_simp
  -- the main term and the error at `y = 1/n`
  have hE1 : A * Real.exp (Δ ^ 2) * (y⁻¹ * Real.exp (-y)) ≤ A * Real.exp 1 * n := by
    have h1 : Real.exp (Δ ^ 2) ≤ Real.exp 1 := Real.exp_le_exp.2 (by nlinarith)
    have h2 : Real.exp (-y) ≤ 1 := Real.exp_le_one_iff.2 (by linarith)
    rw [hydef, inv_inv]
    calc A * Real.exp (Δ ^ 2) * (n * Real.exp (-(n : ℝ)⁻¹)) ≤ A * Real.exp 1 * (n * 1) := by
          gcongr
      _ = A * Real.exp 1 * n := by ring
  have hE2 : K * (Δ⁻¹) ^ (N + 1) * y ^ (-(3 / 4 : ℝ)) = K * u ^ (N + 1) * (n : ℝ) ^ (3 / 4 : ℝ) := by
    rw [hΔdef, inv_inv, hydef, Real.inv_rpow hn0.le, Real.rpow_neg hn0.le, inv_inv]
  have hchain : rsCoeff ρ n * u / (2 * Real.sqrt Real.pi) ≤ A * Real.exp 1 * n + K * u ^ (N + 1) * (n : ℝ) ^ (3 / 4 : ℝ) := by
    rw [← hterm, ← hE2]
    linarith
  have hpi : 0 < 2 * Real.sqrt Real.pi := by positivity
  rw [div_le_iff₀ hpi] at hchain
  -- divide by `u`
  have hdiv : rsCoeff ρ n ≤ 2 * Real.sqrt Real.pi * (A * Real.exp 1 * ((n : ℝ) / u) +
      K * (u ^ N * (n : ℝ) ^ (3 / 4 : ℝ))) := by
    have h := hchain
    rw [show (A * Real.exp 1 * n + K * u ^ (N + 1) * (n : ℝ) ^ (3 / 4 : ℝ)) * (2 * Real.sqrt Real.pi) =
      (2 * Real.sqrt Real.pi * (A * Real.exp 1 * ((n : ℝ) / u) + K * (u ^ N * (n : ℝ) ^ (3 / 4 : ℝ)))) * u by
      field_simp; ring] at h
    exact le_of_mul_le_mul_right h hu0
  have hp1 : (n : ℝ) / u = (n : ℝ) ^ (1 - β) := by
    rw [hudef, Real.rpow_sub hn0, Real.rpow_one]
  have hp2 : u ^ N * (n : ℝ) ^ (3 / 4 : ℝ) = (n : ℝ) ^ (1 - β) := by
    rw [hudef, ← Real.rpow_natCast, ← Real.rpow_mul hn0.le, ← Real.rpow_add hn0]
    congr 1
    simp only [hβdef]
    field_simp
    ring
  rw [hp1, hp2] at hdiv
  calc rsCoeff ρ n ≤ 2 * Real.sqrt Real.pi * (A * Real.exp 1 * (n : ℝ) ^ (1 - β) + K * (n : ℝ) ^ (1 - β)) := hdiv
    _ = 2 * Real.sqrt Real.pi * (A * Real.exp 1 + K) * (n : ℝ) ^ (1 - β) := by ring

/-- **Rankin's bound**: `|ρ(n)| ≤ C |n|^{½ - δ}` for some `δ > 0`. -/
theorem rankin_bound (hg : g ∈ cuspSpace lamE) (hρ0 : ρ 0 = 0)
    (hρ : ∀ n : ℤ, ∀ y, 0 < y → fourierCoeff g n y = ρ n * (Real.sqrt y : ℂ) *
      modifiedBesselKOrder (2 * Real.pi * |(n : ℝ)| * y) (nu lamE)) :
    ∃ C δ : ℝ, 0 ≤ C ∧ 0 < δ ∧ ∀ n : ℤ, n ≠ 0 → ‖ρ n‖ ≤ C * |(n : ℝ)| ^ (1 / 2 - δ) := by
  obtain ⟨C, β, hC, hβ, h⟩ := exists_rsCoeff_le hg hρ0 hρ
  refine ⟨Real.sqrt C, β / 2, Real.sqrt_nonneg _, by positivity, fun n hn => ?_⟩
  set m := n.natAbs
  have hm : 1 ≤ m := Int.natAbs_pos.2 hn
  have hmn : |(n : ℝ)| = (m : ℝ) := by
    simp only [m, Nat.cast_natAbs, Int.cast_abs]
  have hsq : ‖ρ n‖ ^ 2 ≤ rsCoeff ρ m := by
    unfold rsCoeff
    rcases Int.natAbs_eq n with h' | h'
    · rw [← h']; exact le_add_of_nonneg_right (sq_nonneg _)
    · rw [show (-(m : ℤ)) = n from h'.symm]; exact le_add_of_nonneg_left (sq_nonneg _)
  have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg _
  calc ‖ρ n‖ = Real.sqrt (‖ρ n‖ ^ 2) := (Real.sqrt_sq (norm_nonneg _)).symm
    _ ≤ Real.sqrt (C * (m : ℝ) ^ (1 - β)) := Real.sqrt_le_sqrt (hsq.trans (h m hm))
    _ = Real.sqrt C * (m : ℝ) ^ ((1 - β) * (1 / 2)) := by
        rw [Real.sqrt_mul hC, Real.sqrt_eq_rpow ((m : ℝ) ^ (1 - β)), ← Real.rpow_mul hm0]
    _ = Real.sqrt C * |(n : ℝ)| ^ (1 / 2 - β / 2) := by rw [hmn]; congr 2; ring

end CuspRB

end GaloisForLFunctions.BlackHoleRingdown
