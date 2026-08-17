import GaloisForLFunctions.RHTower.Sieve.VonMangoldtTwistScaledWidth
import GaloisForLFunctions.RHTower.VonMangoldtLogSummatory
import GaloisForLFunctions.RHTower.ChebyshevPsiScaling

/-!
# The Route-T twisted Chebyshev bound, uniformly in the height

Below a fixed height the twisted sum has no cancellation to exhibit and the Chebyshev bound
`ψ(K) ≤ 7K` is already of the shape `K/(1+|τ|)`; above it the balanced contour estimate applies.
Joining the two gives one inequality valid for every real frequency: a contour term carrying the
Route-T power saving `(3K)^{-w(τ)/3}` and a height term decaying like `1/(1+|τ|)`.
-/

namespace RHTower.Sieve

open Complex ArithmeticFunction

/-- The height factor of the Route-T twisted contour bound: the reciprocal height together with
the logarithmic cost of the zero-free width at that height. -/
noncomputable def routeTTwistHeightFactor (A τ : ℝ) : ℝ :=
  1 / (1 + |τ|) + Real.log (3 * |τ| / 2 + 3) / routeTZeroFreeWidth A (3 * |τ| / 2 + 1)

theorem routeTTwistHeightFactor_nonneg (A τ : ℝ) : 0 ≤ routeTTwistHeightFactor A τ := by
  have hW : 0 < routeTZeroFreeWidth A (3 * |τ| / 2 + 1) := routeTZeroFreeWidth_pos _ _
  have habs : (0 : ℝ) ≤ |τ| := abs_nonneg τ
  have hlog : 0 ≤ Real.log (3 * |τ| / 2 + 3) := Real.log_nonneg (by linarith)
  have h1 : (0 : ℝ) ≤ 1 / (1 + |τ|) := by positivity
  have h2 : (0 : ℝ) ≤ Real.log (3 * |τ| / 2 + 3) / routeTZeroFreeWidth A (3 * |τ| / 2 + 1) :=
    div_nonneg hlog hW.le
  rw [routeTTwistHeightFactor]
  linarith

/-! ## Two arithmetic collapses -/

/-- The contour regime: the balanced contour bound is dominated by one contour term and one
height term. -/
theorem twistCollapse_contour {Ctot Kr Z P E F L2 LK t C : ℝ}
    (hCtot : 0 < Ctot) (hK : 0 < Kr) (hZ : 0 ≤ Z) (hP : 0 ≤ P) (hE : 0 ≤ E)
    (hFE : F ≤ 2 * E) (hL2 : 0 ≤ L2) (hLK : 0 ≤ LK) (ht : 2 ≤ t)
    (hC : Ctot + 1 ≤ C) :
    Ctot * Kr * (P * (L2 / t + F * (1 / t ^ 2)) + Z * F) / (2 * Real.pi)
        + LK * (Kr * Z)
      ≤ C * Kr * (Z * (E + LK) + (1 + P * (L2 + E)) / (1 + t)) := by
  have ht0 : (0 : ℝ) < t := by linarith
  have hden : (0 : ℝ) < 1 + t := by linarith
  have hinv : 1 / t ≤ 2 * (1 / (1 + t)) := by
    have heq : 2 * (1 / (1 + t)) = 2 / (1 + t) := by ring
    rw [heq, div_le_div_iff₀ ht0 hden]
    linarith
  have hinv2 : 1 / t ^ 2 ≤ 2 * (1 / (1 + t)) := by
    have hsq : (1 : ℝ) / t ^ 2 ≤ 1 / t := by
      rw [div_le_div_iff₀ (by positivity) ht0]
      nlinarith
    linarith
  -- the two normalized groups
  have hQ0 : (0 : ℝ) ≤ P * (L2 + E) / (1 + t) := by positivity
  have hS0 : (0 : ℝ) ≤ Z * E := mul_nonneg hZ hE
  have hT0 : (0 : ℝ) ≤ Z * LK := mul_nonneg hZ hLK
  have hA1 : L2 / t ≤ 2 * (L2 / (1 + t)) := by
    have hstep := mul_le_mul_of_nonneg_left hinv hL2
    calc L2 / t = L2 * (1 / t) := by ring
      _ ≤ L2 * (2 * (1 / (1 + t))) := hstep
      _ = 2 * (L2 / (1 + t)) := by ring
  have hA2 : F * (1 / t ^ 2) ≤ 4 * (E / (1 + t)) := by
    have hstep : F * (1 / t ^ 2) ≤ (2 * E) * (2 * (1 / (1 + t))) :=
      mul_le_mul hFE hinv2 (by positivity) (by linarith)
    calc F * (1 / t ^ 2) ≤ (2 * E) * (2 * (1 / (1 + t))) := hstep
      _ = 4 * (E / (1 + t)) := by ring
  have hinner : P * (L2 / t + F * (1 / t ^ 2)) + Z * F
      ≤ 4 * (P * (L2 + E) / (1 + t) + Z * E) := by
    have hsum : L2 / t + F * (1 / t ^ 2) ≤ 4 * ((L2 + E) / (1 + t)) := by
      have hexp : 4 * ((L2 + E) / (1 + t)) = 2 * (L2 / (1 + t)) + 4 * (E / (1 + t))
          + 2 * (L2 / (1 + t)) := by
        field_simp
        ring
      have hL2div : (0 : ℝ) ≤ L2 / (1 + t) := by positivity
      rw [hexp]
      linarith
    have hstep := mul_le_mul_of_nonneg_left hsum hP
    have hZF : Z * F ≤ 2 * (Z * E) := by
      have := mul_le_mul_of_nonneg_left hFE hZ
      linarith
    have hPQ : P * (4 * ((L2 + E) / (1 + t))) = 4 * (P * (L2 + E) / (1 + t)) := by
      field_simp
    rw [hPQ] at hstep
    linarith
  have hpi : (4 : ℝ) ≤ 2 * Real.pi := by
    have := Real.pi_gt_three
    linarith
  have hpi0 : (0 : ℝ) < 2 * Real.pi := by positivity
  have hbase : (0 : ℝ) ≤ P * (L2 + E) / (1 + t) + Z * E := by linarith
  have hstep1 : Ctot * Kr * (P * (L2 / t + F * (1 / t ^ 2)) + Z * F) / (2 * Real.pi)
      ≤ Ctot * Kr * (P * (L2 + E) / (1 + t) + Z * E) := by
    rw [div_le_iff₀ hpi0]
    have hCK : (0 : ℝ) ≤ Ctot * Kr := by positivity
    have hprod : (0 : ℝ)
        ≤ (Ctot * Kr * (P * (L2 + E) / (1 + t) + Z * E)) * (2 * Real.pi - 4) :=
      mul_nonneg (mul_nonneg hCK hbase) (by linarith)
    nlinarith [mul_le_mul_of_nonneg_left hinner hCK, hprod]
  have hsplit : (1 + P * (L2 + E)) / (1 + t) = 1 / (1 + t) + P * (L2 + E) / (1 + t) := by
    field_simp
  have hone : (0 : ℝ) ≤ 1 / (1 + t) := by positivity
  rw [hsplit]
  have hexpand : C * Kr * (Z * (E + LK) + (1 / (1 + t) + P * (L2 + E) / (1 + t)))
      = C * Kr * (Z * E) + C * Kr * (Z * LK) + C * Kr * (1 / (1 + t))
        + C * Kr * (P * (L2 + E) / (1 + t)) := by ring
  rw [hexpand]
  have hlhs : LK * (Kr * Z) = Kr * (Z * LK) := by ring
  rw [hlhs]
  have hCpos : (0 : ℝ) < C := by linarith
  have h1 : Ctot * Kr * (P * (L2 + E) / (1 + t) + Z * E)
      = Ctot * Kr * (Z * E) + Ctot * Kr * (P * (L2 + E) / (1 + t)) := by ring
  rw [h1] at hstep1
  have hCC : (0 : ℝ) ≤ C - Ctot := by linarith
  have hC1 : (0 : ℝ) ≤ C - 1 := by linarith
  have hd1 : Ctot * Kr * (Z * E) ≤ C * Kr * (Z * E) := by
    nlinarith [mul_nonneg (mul_nonneg hCC hK.le) hS0]
  have hd2 : Ctot * Kr * (P * (L2 + E) / (1 + t)) ≤ C * Kr * (P * (L2 + E) / (1 + t)) := by
    nlinarith [mul_nonneg (mul_nonneg hCC hK.le) hQ0]
  have hd3 : Kr * (Z * LK) ≤ C * Kr * (Z * LK) := by
    nlinarith [mul_nonneg (mul_nonneg hC1 hK.le) hT0]
  have hd4 : (0 : ℝ) ≤ C * Kr * (1 / (1 + t)) := by positivity
  linarith

/-- The trivial regime: below a fixed height the Chebyshev bound already has the shape of the
height term. -/
theorem twistCollapse_trivial {Kr Z P E L2 LK t τ₀ C : ℝ}
    (hK : 0 < Kr) (hZ : 0 ≤ Z) (hP : 0 ≤ P) (hE : 0 ≤ E) (hL2 : 0 ≤ L2) (hLK : 0 ≤ LK)
    (ht : 0 ≤ t) (htτ : t ≤ τ₀) (hC : 7 * (1 + τ₀) ≤ C) :
    7 * Kr ≤ C * Kr * (Z * (E + LK) + (1 + P * (L2 + E)) / (1 + t)) := by
  have hden : (0 : ℝ) < 1 + t := by linarith
  have hden₀ : (0 : ℝ) < 1 + τ₀ := by linarith
  have hstep : (1 : ℝ) / (1 + τ₀) ≤ 1 / (1 + t) :=
    one_div_le_one_div_of_le hden (by linarith)
  have hPterm : (0 : ℝ) ≤ P * (L2 + E) / (1 + t) := by positivity
  have hsplit : (1 + P * (L2 + E)) / (1 + t) = 1 / (1 + t) + P * (L2 + E) / (1 + t) := by
    field_simp
  have hZterm : (0 : ℝ) ≤ Z * (E + LK) := by positivity
  have hCpos : (0 : ℝ) < C := by linarith
  have hbase : 7 * Kr ≤ C * Kr * (1 / (1 + τ₀)) := by
    have hval : C * Kr * (1 / (1 + τ₀)) = C * Kr / (1 + τ₀) := by ring
    rw [hval, le_div_iff₀ hden₀]
    nlinarith [mul_le_mul_of_nonneg_right hC hK.le]
  have hmid : C * Kr * (1 / (1 + τ₀)) ≤ C * Kr * (1 / (1 + t)) :=
    mul_le_mul_of_nonneg_left hstep (by positivity)
  rw [hsplit]
  have hfin : C * Kr * (Z * (E + LK) + (1 / (1 + t) + P * (L2 + E) / (1 + t)))
      = C * Kr * (Z * (E + LK)) + C * Kr * (1 / (1 + t))
        + C * Kr * (P * (L2 + E) / (1 + t)) := by ring
  rw [hfin]
  have h1 : (0 : ℝ) ≤ C * Kr * (Z * (E + LK)) := by positivity
  have h2 : (0 : ℝ) ≤ C * Kr * (P * (L2 + E) / (1 + t)) := by positivity
  linarith

set_option maxHeartbeats 1000000 in
/-- **The Route-T twisted Chebyshev bound, uniform in the frequency.**  For every real `τ` the
partial sum of `Λ(n)n^{-iτ}` is bounded by a contour term carrying the Route-T saving
`(3K)^{-w(τ)/3}` plus a height term decaying like `1/(1+|τ|)`. -/
theorem exists_norm_partialSum_vonMangoldtTwist_routeT_uniform :
    ∃ A delta C : ℝ, 0 < delta ∧ 0 < C ∧
      ∀ (K : ℕ) (τ : ℝ), Real.exp 9 ≤ (K : ℝ) →
        ‖∑ n ∈ Finset.range (K + 1), vonMangoldtTwist τ n‖
          ≤ C * (K : ℝ)
              * ((3 * (K : ℝ)) ^ (-(routeTUniformRegWidth A delta (3 * |τ| / 2) / 3))
                    * (routeTTwistHeightFactor A τ + Real.log (2 * (K : ℝ)))
                  + (1 + (3 * (K : ℝ)) ^ (2 * routeTUniformRegWidth A delta (3 * |τ| / 2) / 3)
                        * ((Real.log (K : ℝ)) ^ 2 + routeTTwistHeightFactor A τ))
                      / (1 + |τ|)) := by
  obtain ⟨A, Creg, delta, Ctot, τ₀, hCreg, hdelta, hCtot, hτ₀, hbound⟩ :=
    exists_norm_partialSum_vonMangoldtTwist_routeT_balancedWidth
  refine ⟨A, delta, 7 * (1 + τ₀) + Ctot + 1, hdelta, by linarith, ?_⟩
  intro K τ hK
  have hexp9 : (10 : ℝ) ≤ Real.exp 9 := by
    have := Real.add_one_le_exp (9 : ℝ)
    linarith
  have hK10 : (10 : ℝ) ≤ (K : ℝ) := le_trans hexp9 hK
  have hK0 : (0 : ℝ) < (K : ℝ) := by linarith
  have h3K0 : (0 : ℝ) < 3 * (K : ℝ) := by linarith
  have habs : (0 : ℝ) ≤ |τ| := abs_nonneg τ
  have hZ0 : (0 : ℝ) ≤ (3 * (K : ℝ)) ^ (-(routeTUniformRegWidth A delta (3 * |τ| / 2) / 3)) :=
    (Real.rpow_pos_of_pos h3K0 _).le
  have hP0 : (0 : ℝ) ≤ (3 * (K : ℝ)) ^ (2 * routeTUniformRegWidth A delta (3 * |τ| / 2) / 3) :=
    (Real.rpow_pos_of_pos h3K0 _).le
  have hE0 : (0 : ℝ) ≤ routeTTwistHeightFactor A τ := routeTTwistHeightFactor_nonneg A τ
  have hlogK : (0 : ℝ) ≤ Real.log (K : ℝ) := Real.log_nonneg (by linarith)
  have hlog2K : (0 : ℝ) ≤ Real.log (2 * (K : ℝ)) := Real.log_nonneg (by linarith)
  have hlogsq : (0 : ℝ) ≤ (Real.log (K : ℝ)) ^ 2 := by positivity
  rcases le_or_gt τ₀ |τ| with hcase | hcase
  · have hτ2 : (2 : ℝ) ≤ |τ| := le_trans hτ₀ hcase
    have hτ0 : (0 : ℝ) < |τ| := by linarith
    have hW : 0 < routeTZeroFreeWidth A (3 * |τ| / 2 + 1) := routeTZeroFreeWidth_pos _ _
    have hFE : 1 / |τ| + Real.log (3 * |τ| / 2) / routeTZeroFreeWidth A (3 * |τ| / 2 + 1)
        ≤ 2 * routeTTwistHeightFactor A τ := by
      have hden : (0 : ℝ) < 1 + |τ| := by linarith
      have h1 : 1 / |τ| ≤ 2 * (1 / (1 + |τ|)) := by
        have heq : 2 * (1 / (1 + |τ|)) = 2 / (1 + |τ|) := by ring
        rw [heq, div_le_div_iff₀ hτ0 hden]
        linarith
      have h2 : Real.log (3 * |τ| / 2) ≤ Real.log (3 * |τ| / 2 + 3) :=
        Real.log_le_log (by linarith) (by linarith)
      have h3 : Real.log (3 * |τ| / 2) / routeTZeroFreeWidth A (3 * |τ| / 2 + 1)
          ≤ Real.log (3 * |τ| / 2 + 3) / routeTZeroFreeWidth A (3 * |τ| / 2 + 1) :=
        div_le_div_of_nonneg_right h2 hW.le
      have hlogpos : (0 : ℝ) ≤ Real.log (3 * |τ| / 2 + 3)
          / routeTZeroFreeWidth A (3 * |τ| / 2 + 1) :=
        div_nonneg (Real.log_nonneg (by linarith)) hW.le
      rw [routeTTwistHeightFactor]
      linarith
    refine (hbound K τ hK hcase).trans ?_
    exact twistCollapse_contour hCtot hK0 hZ0 hP0 hE0 hFE hlogsq hlog2K hτ2 (by linarith)
  · have hpsi : ‖∑ n ∈ Finset.range (K + 1), vonMangoldtTwist τ n‖ ≤ 7 * (K : ℝ) := by
      refine le_trans (norm_sum_le _ _) ?_
      have heq : ∑ n ∈ Finset.range (K + 1), ‖vonMangoldtTwist τ n‖
          = ∑ n ∈ Finset.range (K + 1), (vonMangoldt n : ℝ) :=
        Finset.sum_congr rfl fun n _ => norm_vonMangoldtTwist τ n
      rw [heq]
      have hch : ∑ n ∈ Finset.range (K + 1), (vonMangoldt n : ℝ) = chebyshevPsi K := by
        rw [sum_range_succ_vonMangoldt_eq_sum_Icc]
        rfl
      rw [hch]
      exact chebyshevPsi_le_seven K
    refine hpsi.trans ?_
    exact twistCollapse_trivial hK0 hZ0 hP0 hE0 hlogsq hlog2K habs hcase.le (by linarith)

end RHTower.Sieve
