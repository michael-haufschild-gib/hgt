import GaloisForLFunctions.HTGeometry.ShiftSumDominance
import GaloisForLFunctions.HTGeometry.ShiftPolynomialDegreeBound
import GaloisForLFunctions.HTGeometry.DominantTransferObstruction
import GaloisForLFunctions.HTGeometry.ZetaTailRegularProfile

/-!
# The irrational-power Barnes tail solves no linear analytic equation

The formal Barnes tail `R̂_s(t) = ∑_{k ≥ 1} (−1)^k ζ(−s k) t^k` has a **regular profile**: its
coefficients are bounded above by `Θ(k) = C Γ(1+sk) ((2π)^{-s})^k` everywhere, and bounded below by a
fixed multiple of the same `Θ` along an infinite set — the two sides differ only by the sine factor,
which irrationality of `s` keeps away from zero infinitely often.

That profile is a regular factorial profile of exponent `s`, so the shift comparison applies: in the
coefficient recursion of `L R̂_s = G` with `L` convergent and `G` convergent, the leading Newton
vertex of `L` — which is unique because `s` is irrational — dominates the whole rest of the
recursion, and reading the recursion at an index where the lower bound is realised gives a
contradiction.

No factorization of `L` along its Newton polygon is used: the estimate compares the leading vertex
with each other shift directly.
-/

open Filter Topology
open scoped Nat

namespace GaloisForLFunctions.HTGeometry

/-- The zeta-tail profile is a regular factorial profile of exponent `s`. -/
theorem exists_isRegularFactorialProfile_zetaTailProfile {s : ℝ} (hs : 0 < s)
    (hirr : Irrational s) :
    ∃ c₁ c₂ : ℝ, IsRegularFactorialProfile s c₁ c₂ (zetaTailProfile s) := by
  have hK : (0 : ℝ) < max 1 ‖riemannZeta ((1 + s : ℝ) : ℂ)‖ / Real.pi := by
    have h1 : (1 : ℝ) ≤ max 1 ‖riemannZeta ((1 + s : ℝ) : ℂ)‖ := le_max_left _ _
    have h2 : (0 : ℝ) < Real.pi := Real.pi_pos
    positivity
  have h := (isRegularFactorialProfile_gammaProfile_of_irrational hs hirr
    (zetaTailBase_pos s)).const_mul hK
  exact ⟨_, _, h⟩

/-- A geometric sequence is beaten by a power of a factorial. -/
theorem tendsto_geom_mul_factorial_rpow_neg {s : ℝ} (hs : 0 < s) {L : ℝ} (hL : 0 < L) (ν : ℕ) :
    Tendsto (fun n : ℕ => L ^ n * ((((n - ν)! : ℕ) : ℝ)) ^ (-s)) atTop (𝓝 0) := by
  have hmaj := tendsto_halfFactorial_ratio_mul hs (le_max_left 1 L) 0 ν
  refine squeeze_zero' (Eventually.of_forall fun n => by positivity) ?_ hmaj
  filter_upwards with n
  have hden : (0 : ℝ) < ((((n - ν)! : ℕ) : ℝ)) := Nat.cast_pos.mpr (Nat.factorial_pos _)
  have hnum : (1 : ℝ) ≤ ((((n / 2)! : ℕ) : ℝ)) := by
    have := Nat.one_le_iff_ne_zero.mpr (Nat.factorial_ne_zero (n / 2))
    exact_mod_cast this
  have hratio : ((((n - ν)! : ℕ) : ℝ))⁻¹ ≤ ((((n / 2)! : ℕ) : ℝ)) / ((((n - ν)! : ℕ) : ℝ)) := by
    rw [div_eq_mul_inv]
    have hmul := mul_le_mul_of_nonneg_right hnum (le_of_lt (inv_pos.mpr hden))
    rwa [one_mul] at hmul
  have hrpow : ((((n - ν)! : ℕ) : ℝ)) ^ (-s)
      ≤ (((((n / 2)! : ℕ) : ℝ)) / ((((n - ν)! : ℕ) : ℝ))) ^ s := by
    rw [Real.rpow_neg hden.le, ← Real.inv_rpow hden.le]
    exact Real.rpow_le_rpow (by positivity) hratio hs.le
  have hLm : L ^ n ≤ (max 1 L) ^ n := pow_le_pow_left₀ hL.le (le_max_right _ _) n
  calc L ^ n * ((((n - ν)! : ℕ) : ℝ)) ^ (-s)
      ≤ (max 1 L) ^ n * (((((n / 2)! : ℕ) : ℝ)) / ((((n - ν)! : ℕ) : ℝ))) ^ s :=
        mul_le_mul hLm hrpow (Real.rpow_nonneg hden.le _)
          (pow_nonneg (le_trans zero_le_one (le_max_left 1 L)) n)
    _ = ((n : ℝ) + 1) ^ (0 : ℕ) * (max 1 L) ^ n *
          (((((n / 2)! : ℕ) : ℝ)) / ((((n - ν)! : ℕ) : ℝ))) ^ s := by
        rw [pow_zero, one_mul]

/-! ### The obstruction -/

/-- **The irrational-power Barnes tail is not a formal solution of any nonzero linear analytic
Euler-form equation with analytic right-hand side.** -/
theorem not_eulerLinearOp_barnesTail_eq {m : ℕ} (B : Fin (m + 1) → PowerSeries ℂ)
    (hB : ∀ j, IsGevreySeries 0 (B j)) {j₀ : Fin (m + 1)} (hB0 : B j₀ ≠ 0)
    {G : PowerSeries ℂ} (hG : IsGevreySeries 0 G)
    {s : ℝ} (hs : 0 < s) (hirr : Irrational s) :
    eulerLinearOp B (barnesTailSeries s) ≠ G := by
  classical
  intro hsol
  have hdeg : ∀ μ, (shiftPolynomial B μ).natDegree ≤ m := natDegree_shiftPolynomial_le B
  obtain ⟨C, ρ, hC, hρ, hbd⟩ := exists_bound_shiftPolynomial_natDegree B hB
  have hex : ∃ μ, PowerSeries.coeff μ (B j₀) ≠ 0 := by
    by_contra hc
    push Not at hc
    exact hB0 (PowerSeries.ext fun n => by rw [hc n, map_zero])
  obtain ⟨μ₀, hμ₀⟩ := hex
  have hΦμ₀ : shiftPolynomial B μ₀ ≠ 0 := shiftPolynomial_ne_zero_of_coeff hμ₀
  obtain ⟨ν, hν, hνmax⟩ := exists_max_weightedLevel hs hdeg hΦμ₀
  have hmax : ∀ μ, shiftPolynomial B μ ≠ 0 → μ ≠ ν →
      weightedLevel s (shiftPolynomial B) μ < weightedLevel s (shiftPolynomial B) ν := by
    intro μ hΦ hμν
    rcases lt_or_eq_of_le (hνmax μ hΦ) with h | h
    · exact h
    · exact absurd (weightedLevel_injective_of_irrational hirr (shiftPolynomial B) h) hμν
  obtain ⟨c₁, c₂, hprof⟩ := exists_isRegularFactorialProfile_zetaTailProfile hs hirr
  set dν : ℕ := (shiftPolynomial B ν).natDegree with hdν
  set Θ : ℕ → ℝ := zetaTailProfile s with hΘdef
  have hΘpos : ∀ k, 0 < Θ k := hprof.pos
  have hZpos : ∀ n : ℕ, (0 : ℝ) < ((n : ℝ) + 1) ^ ((dν : ℕ) : ℝ) * Θ (n - ν) := by
    intro n
    exact mul_pos (Real.rpow_pos_of_pos (by positivity) _) (hΘpos (n - ν))
  have hup : ∀ k, ‖PowerSeries.coeff k (barnesTailSeries s)‖ ≤ Θ k := by
    intro k
    rw [norm_coeff_barnesTailSeries, hΘdef]
    exact abs_zetaTailModulus_le_profile hs k
  have hδ : (0 : ℝ) < 1 / (2 * max 1 ‖riemannZeta ((1 + s : ℝ) : ℂ)‖) := by
    have h1 : (1 : ℝ) ≤ max 1 ‖riemannZeta ((1 + s : ℝ) : ℂ)‖ := le_max_left _ _
    positivity
  have hS := infinite_setOf_profile_le_abs_zetaTailModulus hs hirr
  have hlow : ∀ k ∈ {k : ℕ | (1 / (2 * max 1 ‖riemannZeta ((1 + s : ℝ) : ℂ)‖)) *
      zetaTailProfile s k ≤ |zetaTailModulus s k|},
      (1 / (2 * max 1 ‖riemannZeta ((1 + s : ℝ) : ℂ)‖)) * Θ k
        ≤ ‖PowerSeries.coeff k (barnesTailSeries s)‖ := by
    intro k hk
    rw [norm_coeff_barnesTailSeries, hΘdef]
    exact hk
  obtain ⟨cl, hcl, N, hNl⟩ := exists_lower_bound_eval_natCast (shiftPolynomial B ν) hν
  set D : ℕ → ℝ := fun n => (cl / 2 ^ dν) * (((n : ℝ) + 1) ^ ((dν : ℕ) : ℝ) * Θ (n - ν))
    with hDdef
  have hDpos : ∀ n, 0 < D n := by
    intro n
    exact mul_pos (by positivity) (hZpos n)
  have hdom : ∀ᶠ n : ℕ in atTop,
      D n ≤ ‖(shiftPolynomial B ν).eval (((n - ν : ℕ) : ℕ) : ℂ)‖ * Θ (n - ν) := by
    filter_upwards [eventually_ge_atTop (N + ν), eventually_ge_atTop (2 * ν)] with n hn1 hn2
    have hshift : N ≤ n - ν := by omega
    have hlowev := hNl (n - ν) hshift
    have hhalf : ((n : ℝ) + 1) / 2 ≤ (((n - ν : ℕ) : ℝ)) + 1 := half_le_cast_sub_add_one hn2
    have hmono : ((((n : ℝ) + 1) / 2)) ^ dν ≤ ((((n - ν : ℕ) : ℝ)) + 1) ^ dν :=
      pow_le_pow_left₀ (by positivity) hhalf dν
    have hrw : ((n : ℝ) + 1) ^ ((dν : ℕ) : ℝ) = ((n : ℝ) + 1) ^ dν := Real.rpow_natCast _ _
    have hchain : (cl / 2 ^ dν) * ((n : ℝ) + 1) ^ ((dν : ℕ) : ℝ)
        ≤ ‖(shiftPolynomial B ν).eval (((n - ν : ℕ) : ℕ) : ℂ)‖ := by
      rw [hrw]
      refine le_trans (le_of_eq ?_) (le_trans (mul_le_mul_of_nonneg_left hmono hcl.le) hlowev)
      rw [div_pow]
      field_simp
    calc D n = ((cl / 2 ^ dν) * ((n : ℝ) + 1) ^ ((dν : ℕ) : ℝ)) * Θ (n - ν) := by
          rw [hDdef]; ring
      _ ≤ ‖(shiftPolynomial B ν).eval (((n - ν : ℕ) : ℕ) : ℂ)‖ * Θ (n - ν) :=
          mul_le_mul_of_nonneg_right hchain (hΘpos (n - ν)).le
  have hdominance := tendsto_shiftTail_div_leading hC hρ hs hdeg hbd hprof hmax
  obtain ⟨CG, AG, hCG, hAG, hGbd⟩ := hG
  set b : ℝ := min 1 c₁ with hbdef
  have hbpos : (0 : ℝ) < b := by
    rw [hbdef]
    exact lt_min zero_lt_one hprof.c₁_pos
  have hsource : Tendsto (fun n : ℕ => ‖PowerSeries.coeff n G‖ /
      (((n : ℝ) + 1) ^ ((dν : ℕ) : ℝ) * Θ (n - ν))) atTop (𝓝 0) := by
    have hmaj := (tendsto_geom_mul_factorial_rpow_neg hs
      (div_pos hAG hbpos) ν).const_mul (CG / Θ 0)
    rw [mul_zero] at hmaj
    refine squeeze_zero' (Eventually.of_forall fun n => ?_) (Eventually.of_forall fun n => ?_) hmaj
    · exact div_nonneg (norm_nonneg _) (hZpos n).le
    · have hone : (1 : ℝ) ≤ ((n : ℝ) + 1) ^ ((dν : ℕ) : ℝ) := by
        refine Real.one_le_rpow ?_ (Nat.cast_nonneg _)
        have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
        linarith
      have hΘ0 : (0 : ℝ) < Θ 0 := hΘpos 0
      have hFpos : (0 : ℝ) < ((((n - ν)! : ℕ) : ℝ)) ^ s :=
        Real.rpow_pos_of_pos (Nat.cast_pos.mpr (Nat.factorial_pos _)) _
      have hbn : (0 : ℝ) < b ^ n := pow_pos hbpos n
      have hbc : b ^ n ≤ c₁ ^ (n - ν) := by
        rcases le_total 1 c₁ with h | h
        · rw [hbdef, min_eq_left h, one_pow]
          exact one_le_pow₀ h
        · rw [hbdef, min_eq_right h]
          exact pow_le_pow_of_le_one hprof.c₁_pos.le h (Nat.sub_le n ν)
      have hblock := hprof.block_lower (Nat.zero_le (n - ν))
      have hfac0 : ((Nat.factorial 0 : ℕ) : ℝ) = 1 := by norm_num
      rw [hfac0, div_one, Nat.sub_zero] at hblock
      have hchain : Θ 0 * b ^ n * ((((n - ν)! : ℕ) : ℝ)) ^ s
          ≤ ((n : ℝ) + 1) ^ ((dν : ℕ) : ℝ) * Θ (n - ν) := by
        have h1 : Θ 0 * b ^ n * ((((n - ν)! : ℕ) : ℝ)) ^ s
            ≤ Θ 0 * c₁ ^ (n - ν) * ((((n - ν)! : ℕ) : ℝ)) ^ s := by
          refine mul_le_mul_of_nonneg_right ?_ hFpos.le
          exact mul_le_mul_of_nonneg_left hbc hΘ0.le
        have h2 : Θ (n - ν) ≤ ((n : ℝ) + 1) ^ ((dν : ℕ) : ℝ) * Θ (n - ν) := by
          nlinarith [hΘpos (n - ν), hone]
        linarith [h1, hblock, h2]
      have hMnn : (0 : ℝ) ≤ CG / Θ 0 * ((AG / b) ^ n * ((((n - ν)! : ℕ) : ℝ)) ^ (-s)) := by
        have : (0 : ℝ) ≤ (AG / b) ^ n := by positivity
        have h2 : (0 : ℝ) ≤ ((((n - ν)! : ℕ) : ℝ)) ^ (-s) :=
          Real.rpow_nonneg (Nat.cast_nonneg _) _
        have h3 : (0 : ℝ) ≤ CG / Θ 0 := by positivity
        exact mul_nonneg h3 (mul_nonneg this h2)
      have hGn : ‖PowerSeries.coeff n G‖ ≤ CG * AG ^ n := by
        have h := hGbd n
        simpa using h
      rw [div_le_iff₀ (hZpos n)]
      have hval : CG * AG ^ n
          = (CG / Θ 0 * ((AG / b) ^ n * ((((n - ν)! : ℕ) : ℝ)) ^ (-s))) *
            (Θ 0 * b ^ n * ((((n - ν)! : ℕ) : ℝ)) ^ s) := by
        rw [Real.rpow_neg (Nat.cast_nonneg _), div_pow]
        field_simp
      calc ‖PowerSeries.coeff n G‖ ≤ CG * AG ^ n := hGn
        _ = (CG / Θ 0 * ((AG / b) ^ n * ((((n - ν)! : ℕ) : ℝ)) ^ (-s))) *
              (Θ 0 * b ^ n * ((((n - ν)! : ℕ) : ℝ)) ^ s) := hval
        _ ≤ (CG / Θ 0 * ((AG / b) ^ n * ((((n - ν)! : ℕ) : ℝ)) ^ (-s))) *
              (((n : ℝ) + 1) ^ ((dν : ℕ) : ℝ) * Θ (n - ν)) :=
            mul_le_mul_of_nonneg_left hchain hMnn
  have hrest : Tendsto (fun n : ℕ =>
      (‖PowerSeries.coeff n G‖ + ∑ μ ∈ (Finset.range (n + 1)).erase ν,
        ‖(shiftPolynomial B μ).eval (((n - μ : ℕ) : ℕ) : ℂ)‖ * Θ (n - μ)) / D n)
      atTop (𝓝 0) := by
    have hsum : Tendsto (fun n : ℕ =>
        (‖PowerSeries.coeff n G‖ + ∑ μ ∈ (Finset.range (n + 1)).erase ν,
          ‖(shiftPolynomial B μ).eval (((n - μ : ℕ) : ℕ) : ℂ)‖ * Θ (n - μ)) /
          (((n : ℝ) + 1) ^ ((dν : ℕ) : ℝ) * Θ (n - ν))) atTop (𝓝 0) := by
      have h := hsource.add hdominance
      rw [add_zero] at h
      refine h.congr fun n => ?_
      rw [add_div]
    have hcongr := hsum.const_mul (2 ^ dν / cl)
    rw [mul_zero] at hcongr
    refine hcongr.congr fun n => ?_
    rw [hDdef]
    field_simp
  exact false_of_dominant_transfer B hsol Θ hup hδ hS hlow ν D hDpos hdom hrest

end GaloisForLFunctions.HTGeometry
