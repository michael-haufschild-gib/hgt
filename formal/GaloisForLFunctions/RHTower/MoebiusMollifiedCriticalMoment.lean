import GaloisForLFunctions.RHTower.MoebiusMollifiedZetaField
import GaloisForLFunctions.RHTower.VonMangoldtMollifierPolynomialMeanSquare
import GaloisForLFunctions.RHTower.Sieve.InghamCriticalGlobalErrorMomentPolylog
import GaloisForLFunctions.RHTower.Sieve.CriticalDivisorAffineMeanSquare
import GaloisForLFunctions.HTGeometry.StripSquareMeanConvexity

/-!
# The mean square of `ζ M_X` on the critical line

The square `M_X(s)²` of the Möbius mollifier is a Dirichlet polynomial of length `X²` whose
coefficients are bounded by the divisor function; on the critical line its coefficients carry the
harmonic divisor-square mass `Σ_{n ≤ X²} d(n)²/n ≤ (1 + log X²)⁴`. The mean value theorem gives

`∫_{T₁}^{T₂} |M_X(1/2+it)|⁴ ≤ (T₂ − T₁ + 8X²(1 + log X²)) (1 + log X²)⁴`
(`integral_norm_edPoly_mob_critical_pow_four_le`),

and Cauchy–Schwarz against the fourth moment of `ζ` gives, for `N ≥ 4`,

`∫_{−N}^{N} |ζ M_X(1/2+it)|² ≤ √((2N + 8X²(1+log X²))(1+log X²)⁴ · D N (1 + log N)⁴)`
(`exists_integral_normSq_zeta_mul_edPoly_mob_critical_le`).
-/

noncomputable section

open Complex MeasureTheory

namespace RHTower

theorem norm_highBlockMollifierCoeffNat_mob_sq_le (m : ℕ) :
    ‖highBlockMollifierCoeffNat 0 mobCoeff m‖ ^ 2 ≤ 1 / ((m : ℝ) + 1) := by
  rw [norm_highBlockMollifierCoeffNat_sq_eq]
  have h1 : ‖mobCoeff (m + 1)‖ ^ 2 ≤ 1 := by
    have := norm_mobCoeff_le (m + 1)
    have h0 := norm_nonneg (mobCoeff (m + 1))
    nlinarith
  have h2 : ((m : ℝ) + 1) ^ (2 * (0 : ℝ) - 1) = 1 / ((m : ℝ) + 1) := by
    rw [show 2 * (0 : ℝ) - 1 = -1 by ring, Real.rpow_neg_one, one_div]
  rw [h2]
  exact mul_le_of_le_one_left (by positivity) h1

/-- The fibre of a product index injects into the divisors. -/
theorem card_dirConv_fibre_le (N : ℕ) (r : Fin (N * N)) :
    ((Finset.univ : Finset (Fin N × Fin N)).filter
      (fun q => ((q.1 : ℕ) + 1) * ((q.2 : ℕ) + 1) = (r : ℕ) + 1)).card ≤
        ((r : ℕ) + 1).divisors.card := by
  apply Finset.card_le_card_of_injOn (fun q => (q.1 : ℕ) + 1)
  · intro q hq
    have hq' := (Finset.mem_filter.mp (Finset.mem_coe.mp hq)).2
    rw [Finset.mem_coe, Nat.mem_divisors]
    exact ⟨⟨(q.2 : ℕ) + 1, hq'.symm⟩, by omega⟩
  · intro q hq q' hq' h
    have e1 := (Finset.mem_filter.mp (Finset.mem_coe.mp hq)).2
    have e2 := (Finset.mem_filter.mp (Finset.mem_coe.mp hq')).2
    simp only at h
    have h1 : (q.1 : ℕ) = q'.1 := by omega
    have h2 : (q.2 : ℕ) + 1 = (q'.2 : ℕ) + 1 := by
      rw [h] at e1
      exact Nat.eq_of_mul_eq_mul_left (by omega) (e1.trans e2.symm)
    exact Prod.ext (Fin.ext h1) (Fin.ext (by omega))

theorem norm_dirConv_mob_sq_le (N : ℕ) (r : Fin (N * N)) :
    ‖Sieve.dirConv N N (fun m => highBlockMollifierCoeffNat 0 mobCoeff m)
        (fun m => highBlockMollifierCoeffNat 0 mobCoeff m) r‖ ^ 2 ≤
      (((r : ℕ) + 1).divisors.card : ℝ) ^ 2 / ((r : ℝ) + 1) := by
  set a : Fin N → ℂ := fun m => highBlockMollifierCoeffNat 0 mobCoeff m with ha
  set S := (Finset.univ : Finset (Fin N × Fin N)).filter
    (fun q => ((q.1 : ℕ) + 1) * ((q.2 : ℕ) + 1) = (r : ℕ) + 1) with hS
  have hr0 : (0 : ℝ) < (r : ℝ) + 1 := by positivity
  have hcoef : ∀ m : ℕ, ‖highBlockMollifierCoeffNat 0 mobCoeff m‖ ≤ Real.sqrt (1 / ((m : ℝ) + 1)) :=
    fun m => Real.le_sqrt_of_sq_le (norm_highBlockMollifierCoeffNat_mob_sq_le m)
  have hterm : ∀ q ∈ S, ‖a q.1 * a q.2‖ ≤ Real.sqrt (1 / ((r : ℝ) + 1)) := by
    intro q hq
    have e := (Finset.mem_filter.mp hq).2
    rw [norm_mul]
    have hprod : Real.sqrt (1 / (((q.1 : ℕ) : ℝ) + 1)) * Real.sqrt (1 / (((q.2 : ℕ) : ℝ) + 1)) =
        Real.sqrt (1 / ((r : ℝ) + 1)) := by
      rw [← Real.sqrt_mul (by positivity)]
      congr 1
      have ecast : ((((q.1 : ℕ) : ℝ) + 1) * (((q.2 : ℕ) : ℝ) + 1)) = (r : ℝ) + 1 := by
        exact_mod_cast e
      rw [div_mul_div_comm, one_mul, ecast]
    rw [← hprod]
    exact mul_le_mul (hcoef _) (hcoef _) (norm_nonneg _) (Real.sqrt_nonneg _)
  have hnorm : ‖Sieve.dirConv N N a a r‖ ≤ S.card * Real.sqrt (1 / ((r : ℝ) + 1)) := by
    unfold Sieve.dirConv
    refine (norm_sum_le _ _).trans ?_
    calc ∑ q ∈ S, ‖a q.1 * a q.2‖ ≤ ∑ _q ∈ S, Real.sqrt (1 / ((r : ℝ) + 1)) :=
          Finset.sum_le_sum hterm
      _ = S.card * Real.sqrt (1 / ((r : ℝ) + 1)) := by rw [Finset.sum_const, nsmul_eq_mul]
  have hcard : (S.card : ℝ) ≤ ((r : ℕ) + 1).divisors.card := by
    exact_mod_cast card_dirConv_fibre_le N r
  calc ‖Sieve.dirConv N N a a r‖ ^ 2 ≤ (S.card * Real.sqrt (1 / ((r : ℝ) + 1))) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) hnorm 2
    _ = (S.card : ℝ) ^ 2 * (1 / ((r : ℝ) + 1)) := by
        rw [mul_pow, Real.sq_sqrt (by positivity)]
    _ ≤ (((r : ℕ) + 1).divisors.card : ℝ) ^ 2 * (1 / ((r : ℝ) + 1)) := by
        gcongr
    _ = (((r : ℕ) + 1).divisors.card : ℝ) ^ 2 / ((r : ℝ) + 1) := by ring

/-- **The fourth moment of the Möbius mollifier on the critical line.** -/
theorem integral_norm_edPoly_mob_critical_pow_four_le {X : ℕ} (hX : 1 ≤ X) {T₁ T₂ : ℝ}
    (hT : T₁ ≤ T₂) :
    ∫ t in T₁..T₂, ‖edPoly mobCoeff (Finset.Icc 1 X) (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I)‖ ^ 4 ≤
      (T₂ - T₁ + 8 * ((X * X : ℕ) : ℝ) * (1 + Real.log ((X * X : ℕ) : ℝ))) *
        (1 + Real.log ((X * X : ℕ) : ℝ)) ^ 4 := by
  set a : Fin X → ℂ := fun m => highBlockMollifierCoeffNat 0 mobCoeff m with ha
  have hpt : ∀ t : ℝ,
      ‖edPoly mobCoeff (Finset.Icc 1 X) (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I)‖ ^ 4 =
        ‖Sieve.dirPoly (X * X) (Sieve.dirConv X X a a) (-t)‖ ^ (2 : ℕ) := by
    intro t
    have hline : (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I) = displacedLinePt 0 t := by
      unfold displacedLinePt; norm_num
    rw [hline, edPoly_Icc_eq_dirPoly, ← Sieve.dirPoly_mul_eq_dirPoly, norm_mul, ← sq, ← pow_mul]
  rw [intervalIntegral.integral_congr (fun t _ => hpt t)]
  have hmvt := Sieve.dirichlet_meanValue_window_neg (X * X) (Sieve.dirConv X X a a) T₁ T₂
  have hXX : 1 ≤ X * X := Nat.one_le_iff_ne_zero.mpr (by positivity)
  have henergy : ∑ r : Fin (X * X), ‖Sieve.dirConv X X a a r‖ ^ (2 : ℕ) ≤
      (1 + Real.log ((X * X : ℕ) : ℝ)) ^ 4 := by
    calc ∑ r : Fin (X * X), ‖Sieve.dirConv X X a a r‖ ^ (2 : ℕ)
        ≤ ∑ r : Fin (X * X), (((r : ℕ) + 1).divisors.card : ℝ) ^ 2 / ((r : ℝ) + 1) :=
          Finset.sum_le_sum fun r _ => norm_dirConv_mob_sq_le X r
      _ = ∑ n ∈ Finset.Icc 1 (X * X), (n.divisors.card : ℝ) ^ 2 / (n : ℝ) := by
          rw [← Sieve.sum_fin_eq_sum_Icc (X * X) (fun n => (n.divisors.card : ℝ) ^ 2 / (n : ℝ))]
          refine Finset.sum_congr rfl fun r _ => ?_
          push_cast
          rfl
      _ ≤ (1 + Real.log ((X * X : ℕ) : ℝ)) ^ 4 :=
          Sieve.sum_card_divisors_sq_div_le_polylog (X * X) hXX
  have hle := (abs_le.mp hmvt).2
  have hE0 : 0 ≤ ∑ r : Fin (X * X), ‖Sieve.dirConv X X a a r‖ ^ (2 : ℕ) :=
    Finset.sum_nonneg fun r _ => by positivity
  have hlen : 0 ≤ T₂ - T₁ + 8 * ((X * X : ℕ) : ℝ) * (1 + Real.log ((X * X : ℕ) : ℝ)) := by
    have : 0 ≤ Real.log ((X * X : ℕ) : ℝ) := Real.log_nonneg (by exact_mod_cast hXX)
    have : (0 : ℝ) ≤ ((X * X : ℕ) : ℝ) := Nat.cast_nonneg _
    nlinarith
  have hstep : (∫ t in T₁..T₂, ‖Sieve.dirPoly (X * X) (Sieve.dirConv X X a a) (-t)‖ ^ (2 : ℕ)) ≤
      (T₂ - T₁ + 8 * ((X * X : ℕ) : ℝ) * (1 + Real.log ((X * X : ℕ) : ℝ))) *
        ∑ r : Fin (X * X), ‖Sieve.dirConv X X a a r‖ ^ (2 : ℕ) := by
    linarith
  exact hstep.trans (mul_le_mul_of_nonneg_left henergy hlen)

/-- The corpus fourth moment of `ζ` on `[−N, N]`, as an interval integral. -/
theorem exists_integral_norm_riemannZeta_critical_pow_four_le :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ {N : ℕ}, 4 ≤ N →
      ∫ t in (-(N : ℝ))..(N : ℝ), ‖riemannZeta (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I)‖ ^ 4 ≤
        D * N * (1 + Real.log N) ^ 4 := by
  obtain ⟨D, hD, hbound⟩ := Sieve.exists_inghamCriticalZetaFourthMoment_symmetric_nat_le_polylog
  refine ⟨D, hD, fun {N} hN => ?_⟩
  have hb := hbound hN
  have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  have heq : Sieve.inghamCriticalZetaFourthMoment (-(N : ℝ)) (N : ℝ) =
      ∫ t in (-(N : ℝ))..(N : ℝ), ‖riemannZeta (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I)‖ ^ 4 := by
    unfold Sieve.inghamCriticalZetaFourthMoment
    rw [intervalIntegral.integral_of_le (by linarith), ← integral_Icc_eq_integral_Ioc]
    refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
    have hpt : Sieve.inghamCriticalPoint t = ((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I := by
      unfold Sieve.inghamCriticalPoint; push_cast; ring
    simp only [hpt]
    rw [show (4 : ℝ) = ((4 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  rw [← heq]
  exact hb

theorem continuous_riemannZeta_critical :
    Continuous fun t : ℝ => riemannZeta (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I) := by
  refine continuous_iff_continuousAt.mpr fun t => ?_
  have hne : (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I) ≠ 1 := by
    intro h
    have := congrArg Complex.re h
    simp at this
  exact ContinuousAt.comp (g := riemannZeta) (f := fun t : ℝ => ((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I)
    (differentiableAt_riemannZeta hne).continuousAt (by fun_prop)

/-- **The mean square of `ζ M_X` on the critical line.** -/
theorem exists_integral_normSq_zeta_mul_edPoly_mob_critical_le :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ {X N : ℕ}, 1 ≤ X → 4 ≤ N →
      ∫ t in (-(N : ℝ))..(N : ℝ), ‖riemannZeta (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I) *
          edPoly mobCoeff (Finset.Icc 1 X) (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I)‖ ^ 2 ≤
        Real.sqrt ((2 * N + 8 * ((X * X : ℕ) : ℝ) * (1 + Real.log ((X * X : ℕ) : ℝ))) *
          (1 + Real.log ((X * X : ℕ) : ℝ)) ^ 4 * (D * N * (1 + Real.log N) ^ 4)) := by
  obtain ⟨D, hD, hZ⟩ := exists_integral_norm_riemannZeta_critical_pow_four_le
  refine ⟨D, hD, fun {X N} hX hN => ?_⟩
  have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  have hs : ∀ n ∈ Finset.Icc 1 X, 1 ≤ n := fun n hn => (Finset.mem_Icc.mp hn).1
  set M : ℝ → ℂ := fun t => edPoly mobCoeff (Finset.Icc 1 X) (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I)
    with hMdef
  set Z : ℝ → ℂ := fun t => riemannZeta (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I) with hZdef
  have hMc : Continuous M := (differentiable_edPoly mobCoeff hs).continuous.comp (by fun_prop)
  have hZc : Continuous Z := continuous_riemannZeta_critical
  have hXX : 1 ≤ X * X := Nat.one_le_iff_ne_zero.mpr (by positivity)
  set SA : ℝ := (2 * N + 8 * ((X * X : ℕ) : ℝ) * (1 + Real.log ((X * X : ℕ) : ℝ))) *
    (1 + Real.log ((X * X : ℕ) : ℝ)) ^ 4 with hSA
  have hSA0 : 0 < SA := by
    have : 0 ≤ Real.log ((X * X : ℕ) : ℝ) := Real.log_nonneg (by exact_mod_cast hXX)
    have : (1 : ℝ) ≤ ((X * X : ℕ) : ℝ) := by exact_mod_cast hXX
    positivity
  have hfS : ∫ t in (-(N : ℝ))..(N : ℝ), ‖M t ^ 2‖ ^ 2 ≤ SA := by
    have h := integral_norm_edPoly_mob_critical_pow_four_le hX (T₁ := -(N : ℝ)) (T₂ := N)
      (by linarith)
    have hpt : ∀ t : ℝ, ‖M t ^ 2‖ ^ 2 = ‖M t‖ ^ 4 := by
      intro t; rw [norm_pow, ← pow_mul]
    simp only [hpt]
    rw [show (N : ℝ) - -(N : ℝ) = 2 * N by ring] at h
    exact h
  have hcs := GaloisForLFunctions.HTGeometry.integral_norm_mul_le_sqrt_of_bound
    (A := -(N : ℝ)) (B := N) (by linarith) (hMc.pow 2) (hZc.pow 2) hSA0 hfS
  have hgS : ∫ t in (-(N : ℝ))..(N : ℝ), ‖Z t ^ 2‖ ^ 2 ≤ D * N * (1 + Real.log N) ^ 4 := by
    have hpt : ∀ t : ℝ, ‖Z t ^ 2‖ ^ 2 = ‖Z t‖ ^ 4 := by
      intro t; rw [norm_pow, ← pow_mul]
    simp only [hpt]
    exact hZ hN
  have hlhs : ∫ t in (-(N : ℝ))..(N : ℝ), ‖Z t * M t‖ ^ 2 =
      ∫ t in (-(N : ℝ))..(N : ℝ), ‖M t ^ 2‖ * ‖Z t ^ 2‖ := by
    refine intervalIntegral.integral_congr fun t _ => ?_
    simp only [norm_mul, norm_pow]
    ring
  rw [hlhs]
  refine hcs.trans (Real.sqrt_le_sqrt ?_)
  exact mul_le_mul_of_nonneg_left hgS hSA0.le

end RHTower
