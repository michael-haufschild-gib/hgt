import GaloisForLFunctions.RHTower.HighBlockDirectMeanSquare
import GaloisForLFunctions.RHTower.MertensVonMangoldtEulerConstant
import GaloisForLFunctions.RHTower.ChebyshevSquareWeight
import GaloisForLFunctions.RHTower.BarbanVehovMollifiedZetaTail

/-!
# Mean squares of Dirichlet polynomials on displaced lines, and the von Mangoldt head

For any coefficients `c` and any real displacement `d`, the Dirichlet polynomial
`Σ_{n ≤ N} c_n n^{-s}` on the line `Re s = 1/2 − d` satisfies

`∫_{T₁}^{T₂} ‖Σ c_n n^{-(1/2-d+iτ)}‖² dτ ≤ (T₂ − T₁ + 8N(1+log N)) Σ ‖c_n‖² n^{2d-1}`
(`integral_normSq_edPoly_displaced_le`).

For the von Mangoldt head `P_N = Σ_{n ≤ N} Λ(n)/log N · n^{-s}` the energy is controlled by
Chebyshev's bound through the Mellin identity `Σ Λ(n) n^{-s} = s∫_1^∞ ψ(t) t^{-s-1} dt`:
`Σ Λ(n) n^{-s} ≤ 6s/(s−1)` (`tsum_vonMangoldt_div_rpow_le_six`), and, since
`log n · n^{-δ} ≤ 1/(eδ)`,

`Σ_{n ≤ N} Λ(n)² n^{-1-2δ} ≤ 5/δ²`  for `0 < δ ≤ 1`  (`sum_vonMangoldt_sq_rpow_le`),

uniformly in `N`. On the right-shifted line `Re s = 1/2 + δ` the mean square of `P_N` is therefore
at most `5/(δ log N)²` times the window length (plus the mean-value error).
-/

noncomputable section

open Complex MeasureTheory Set Filter
open scoped Chebyshev
open ArithmeticFunction (vonMangoldt)

namespace RHTower

/-- **Chebyshev's bound for the von Mangoldt series:** `Σ Λ(n) n^{-s} ≤ 6s/(s−1)` for `s > 1`. -/
theorem tsum_vonMangoldt_div_rpow_le_six {s : ℝ} (hs : 1 < s) :
    ∑' n : ℕ, vonMangoldt n / (n : ℝ) ^ s ≤ 6 * s / (s - 1) := by
  rw [tsum_vonMangoldt_div_rpow_eq hs]
  have hs0 : 0 < s := by linarith
  have hint6 : IntegrableOn (fun t : ℝ => 6 * t ^ (-s)) (Ioi 1) :=
    (integrableOn_Ioi_rpow_of_lt (show -s < -1 by linarith) one_pos).const_mul 6
  have hbound : ∀ t ∈ Ioi (1 : ℝ), ψ t * t ^ (-s - 1) ≤ 6 * t ^ (-s) := by
    intro t ht
    have ht0 : 0 < t := lt_trans one_pos ht
    have hψ : ψ t ≤ 6 * t := by
      have h := Chebyshev.psi_le_const_mul_self ht0.le
      have hlog4 : Real.log 4 + 4 ≤ 6 := by
        have h4 : Real.log 4 = 2 * Real.log 2 := by
          rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
          push_cast
          ring
        have := Real.log_two_lt_d9
        linarith
      nlinarith
    calc ψ t * t ^ (-s - 1) ≤ (6 * t) * t ^ (-s - 1) :=
          mul_le_mul_of_nonneg_right hψ (Real.rpow_nonneg ht0.le _)
      _ = 6 * t ^ (-s) := by rw [mul_assoc, mul_rpow_neg_sub_one ht0]
  have hnonneg : ∀ t ∈ Ioi (1 : ℝ), 0 ≤ ψ t * t ^ (-s - 1) := fun t ht =>
    mul_nonneg (Chebyshev.psi_nonneg t) (Real.rpow_nonneg (lt_trans one_pos ht).le _)
  have hintψ : IntegrableOn (fun t : ℝ => ψ t * t ^ (-s - 1)) (Ioi 1) := by
    refine hint6.mono' ((measurable_psi.mul (measurable_id.pow_const _)).aestronglyMeasurable) ?_
    rw [ae_restrict_iff' measurableSet_Ioi]
    refine Filter.Eventually.of_forall fun t ht => ?_
    rw [Real.norm_eq_abs, abs_of_nonneg (hnonneg t ht)]
    exact hbound t ht
  have hmono := setIntegral_mono_on hintψ hint6 measurableSet_Ioi hbound
  have hval : ∫ t in Ioi (1 : ℝ), 6 * t ^ (-s) = 6 / (s - 1) := by
    rw [integral_const_mul, integral_Ioi_rpow_of_lt (show -s < -1 by linarith) one_pos,
      Real.one_rpow]
    have h1 : s - 1 ≠ 0 := by linarith
    have h2 : -s + 1 ≠ 0 := by linarith
    field_simp
    ring
  rw [hval] at hmono
  calc s * ∫ t in Ioi 1, ψ t * t ^ (-s - 1) ≤ s * (6 / (s - 1)) :=
        mul_le_mul_of_nonneg_left hmono hs0.le
    _ = 6 * s / (s - 1) := by ring

/-- `log n · n^{-δ} ≤ 1/(eδ)`. -/
theorem log_mul_rpow_neg_le {δ : ℝ} (hδ : 0 < δ) {x : ℝ} (hx : 1 ≤ x) :
    Real.log x * x ^ (-δ) ≤ 1 / (Real.exp 1 * δ) := by
  have hx0 : 0 < x := by linarith
  have hlog : 0 ≤ Real.log x := Real.log_nonneg hx
  have h1 := Real.add_one_le_exp (δ * Real.log x - 1)
  rw [Real.exp_sub, sub_add_cancel] at h1
  have hxδ : Real.exp (δ * Real.log x) = x ^ δ := by
    rw [Real.rpow_def_of_pos hx0, mul_comm]
  rw [hxδ] at h1
  have hxδpos : 0 < x ^ δ := Real.rpow_pos_of_pos hx0 δ
  rw [Real.rpow_neg hx0.le, ← div_eq_mul_inv, div_le_div_iff₀ hxδpos (by positivity)]
  rw [le_div_iff₀ (Real.exp_pos 1)] at h1
  nlinarith [Real.exp_pos 1]

/-- **The von Mangoldt square energy on the right-shifted line.** -/
theorem sum_vonMangoldt_sq_rpow_le {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) (N : ℕ) :
    ∑ n ∈ Finset.Icc 1 N, vonMangoldt n ^ 2 * (n : ℝ) ^ (-1 - 2 * δ) ≤ 5 / δ ^ 2 := by
  have hs : (1 : ℝ) < 1 + δ := by linarith
  have hsum : Summable fun n : ℕ => vonMangoldt n / (n : ℝ) ^ (1 + δ) :=
    summable_vonMangoldt_div_rpow_mertensVonMangoldtEulerConstant hs
  have hpt : ∀ n ∈ Finset.Icc 1 N, vonMangoldt n ^ 2 * (n : ℝ) ^ (-1 - 2 * δ) ≤
      1 / (Real.exp 1 * δ) * (vonMangoldt n / (n : ℝ) ^ (1 + δ)) := by
    intro n hn
    have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (Finset.mem_Icc.mp hn).1
    have hn0 : (0 : ℝ) < n := by linarith
    have hΛ0 : 0 ≤ vonMangoldt n := ArithmeticFunction.vonMangoldt_nonneg
    have hΛ : vonMangoldt n ≤ Real.log n := ArithmeticFunction.vonMangoldt_le_log
    have hsplit : (n : ℝ) ^ (-1 - 2 * δ) = (n : ℝ) ^ (-δ) * ((n : ℝ) ^ (1 + δ))⁻¹ := by
      rw [← Real.rpow_neg hn0.le, ← Real.rpow_add hn0]
      congr 1
      ring
    have hkey := log_mul_rpow_neg_le hδ hn1
    have hpos : 0 ≤ ((n : ℝ) ^ (1 + δ))⁻¹ := by positivity
    have hnδ : 0 ≤ (n : ℝ) ^ (-δ) := Real.rpow_nonneg hn0.le _
    rw [hsplit, div_eq_mul_inv]
    calc vonMangoldt n ^ 2 * ((n : ℝ) ^ (-δ) * ((n : ℝ) ^ (1 + δ))⁻¹)
        = vonMangoldt n * (vonMangoldt n * (n : ℝ) ^ (-δ)) * ((n : ℝ) ^ (1 + δ))⁻¹ := by ring
      _ ≤ vonMangoldt n * (Real.log n * (n : ℝ) ^ (-δ)) * ((n : ℝ) ^ (1 + δ))⁻¹ := by
          gcongr
      _ ≤ vonMangoldt n * (1 / (Real.exp 1 * δ)) * ((n : ℝ) ^ (1 + δ))⁻¹ := by
          gcongr
      _ = 1 / (Real.exp 1 * δ) * (vonMangoldt n * ((n : ℝ) ^ (1 + δ))⁻¹) := by ring
  have hterm0 : ∀ n : ℕ, 0 ≤ 1 / (Real.exp 1 * δ) * (vonMangoldt n / (n : ℝ) ^ (1 + δ)) :=
    fun n => mul_nonneg (by positivity)
      (div_nonneg ArithmeticFunction.vonMangoldt_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _))
  calc ∑ n ∈ Finset.Icc 1 N, vonMangoldt n ^ 2 * (n : ℝ) ^ (-1 - 2 * δ)
      ≤ ∑ n ∈ Finset.Icc 1 N, 1 / (Real.exp 1 * δ) * (vonMangoldt n / (n : ℝ) ^ (1 + δ)) :=
        Finset.sum_le_sum hpt
    _ ≤ ∑' n : ℕ, 1 / (Real.exp 1 * δ) * (vonMangoldt n / (n : ℝ) ^ (1 + δ)) :=
        (hsum.mul_left _).sum_le_tsum _ fun n _ => hterm0 n
    _ = 1 / (Real.exp 1 * δ) * ∑' n : ℕ, vonMangoldt n / (n : ℝ) ^ (1 + δ) := tsum_mul_left
    _ ≤ 1 / (Real.exp 1 * δ) * (6 * (1 + δ) / (1 + δ - 1)) :=
        mul_le_mul_of_nonneg_left (tsum_vonMangoldt_div_rpow_le_six hs) (by positivity)
    _ ≤ 5 / δ ^ 2 := by
        have he : (2.7 : ℝ) ≤ Real.exp 1 := by
          have := Real.exp_one_gt_d9
          linarith
        rw [show (1 + δ - 1) = δ by ring]
        rw [div_mul_div_comm, div_le_div_iff₀ (by positivity) (by positivity)]
        nlinarith [mul_pos hδ hδ]

/-- The square norm of a displaced mollifier coefficient. -/
theorem norm_highBlockMollifierCoeffNat_sq_eq (d : ℝ) (c : ℕ → ℂ) (m : ℕ) :
    ‖highBlockMollifierCoeffNat d c m‖ ^ 2 = ‖c (m + 1)‖ ^ 2 * (((m : ℝ) + 1) ^ (2 * d - 1)) := by
  unfold highBlockMollifierCoeffNat
  rw [norm_mul, mul_pow]
  congr 1
  have hpos : (0 : ℝ) < (m : ℝ) + 1 := by positivity
  have hcast : ((m : ℂ) + 1) = (((m : ℝ) + 1 : ℝ) : ℂ) := by push_cast; ring
  rw [hcast, Complex.norm_cpow_eq_rpow_re_of_pos hpos, Complex.neg_re, displacedLinePt_re,
    ← Real.rpow_natCast (((m : ℝ) + 1) ^ (-(1 / 2 - d))) 2, ← Real.rpow_mul hpos.le]
  congr 1
  push_cast
  ring

/-- **Mean-value bound for a Dirichlet polynomial on a displaced line.** -/
theorem integral_normSq_edPoly_displaced_le (d : ℝ) (c : ℕ → ℂ) (N : ℕ) (T₁ T₂ : ℝ) :
    (∫ τ in T₁..T₂, ‖edPoly c (Finset.Icc 1 N) (displacedLinePt d τ)‖ ^ 2) ≤
      (T₂ - T₁ + 8 * N * (1 + Real.log N)) *
        ∑ n ∈ Finset.Icc 1 N, ‖c n‖ ^ 2 * (n : ℝ) ^ (2 * d - 1) := by
  have hpoint : ∀ τ : ℝ, ‖edPoly c (Finset.Icc 1 N) (displacedLinePt d τ)‖ ^ 2 =
      ‖Sieve.dirPoly N (fun m => highBlockMollifierCoeffNat d c m) (-τ)‖ ^ (2 : ℕ) := by
    intro τ
    rw [edPoly_Icc_eq_dirPoly]
  rw [intervalIntegral.integral_congr (fun τ _ => hpoint τ)]
  have hmvt := Sieve.dirichlet_meanValue_window_neg N
    (fun m => highBlockMollifierCoeffNat d c (m : ℕ)) T₁ T₂
  have hE : ∑ m : Fin N, ‖highBlockMollifierCoeffNat d c (m : ℕ)‖ ^ (2 : ℕ) =
      ∑ n ∈ Finset.Icc 1 N, ‖c n‖ ^ 2 * (n : ℝ) ^ (2 * d - 1) := by
    have := Sieve.sum_fin_eq_sum_Icc N (fun n => ‖c n‖ ^ 2 * (n : ℝ) ^ (2 * d - 1))
    rw [← this]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [norm_highBlockMollifierCoeffNat_sq_eq]
    push_cast
    rfl
  rw [hE] at hmvt
  have hle := (abs_le.mp hmvt).2
  have hE0 : 0 ≤ ∑ n ∈ Finset.Icc 1 N, ‖c n‖ ^ 2 * (n : ℝ) ^ (2 * d - 1) :=
    Finset.sum_nonneg fun n _ => mul_nonneg (by positivity) (Real.rpow_nonneg (Nat.cast_nonneg _) _)
  nlinarith

/-- **The von Mangoldt head on the right-shifted line** `Re s = 1/2 + δ`. -/
theorem integral_normSq_hbVonMangoldt_right_le {N : ℕ} (hN : 2 ≤ N) {δ : ℝ} (hδ : 0 < δ)
    (hδ1 : δ ≤ 1) {T₁ T₂ : ℝ} (hT : T₁ ≤ T₂) :
    (∫ τ in T₁..T₂,
        ‖edPoly (hbVonMangoldtCoeff N) (Finset.Icc 1 N) (displacedLinePt (-δ) τ)‖ ^ 2) ≤
      (T₂ - T₁ + 8 * N * (1 + Real.log N)) * (5 / (δ ^ 2 * Real.log N ^ 2)) := by
  refine (integral_normSq_edPoly_displaced_le (-δ) _ N T₁ T₂).trans ?_
  have hlogN : 0 < Real.log (N : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < N))
  have hlen : 0 ≤ T₂ - T₁ + 8 * N * (1 + Real.log N) := by
    have : 0 ≤ Real.log (N : ℝ) := hlogN.le
    have : (0 : ℝ) ≤ N := Nat.cast_nonneg N
    nlinarith
  refine mul_le_mul_of_nonneg_left ?_ hlen
  have hterm : ∀ n ∈ Finset.Icc 1 N,
      ‖hbVonMangoldtCoeff N n‖ ^ 2 * (n : ℝ) ^ (2 * (-δ) - 1) =
        (vonMangoldt n ^ 2 * (n : ℝ) ^ (-1 - 2 * δ)) / Real.log N ^ 2 := by
    intro n _
    unfold hbVonMangoldtCoeff
    rw [Complex.norm_real, Real.norm_eq_abs, sq_abs, div_pow,
      show 2 * (-δ) - 1 = -1 - 2 * δ by ring]
    ring
  rw [Finset.sum_congr rfl hterm, ← Finset.sum_div, div_le_div_iff₀ (by positivity) (by positivity)]
  have := sum_vonMangoldt_sq_rpow_le hδ hδ1 N
  rw [le_div_iff₀ (by positivity)] at this
  nlinarith [this, sq_nonneg (Real.log N)]

end RHTower
