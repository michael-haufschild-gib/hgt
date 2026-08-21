import GaloisForLFunctions.RHTower.SmoothAFEZetaSquarePrimalAffineMeanSquare
import GaloisForLFunctions.RHTower.HardyZSmoothAFEReal
import GaloisForLFunctions.RHTower.Sieve.InghamRightEdgeMeanSquare

/-! # Observation-height derivative of the primal Gaussian square AFE -/

noncomputable section

open Complex Set Filter Topology

namespace RHTower

/-- A single term of the height derivative of the primal square-AFE source. -/
def smoothAFEZetaSquarePrimalHeightDerivativeTerm
    (N : ℕ) (t : ℝ) (n : ℕ) : ℂ :=
  ((n + 1).divisors.card : ℂ) *
    ((n + 1 : ℂ) ^ (-linePt t) *
      Complex.log (n + 1 : ℂ) * (-I)) *
    smoothAFECutoff ((n + 1 : ℝ) / (N : ℝ))

/-- Height derivative of the primal square-AFE source. -/
def smoothAFEZetaSquarePrimalHeightDerivativeSourceField
    (N : ℕ) (t : ℝ) : ℂ :=
  ∑' n : ℕ, smoothAFEZetaSquarePrimalHeightDerivativeTerm N t n

private theorem hasDerivAt_smoothAFEZetaSquarePrimalSourceTerm
    (N : ℕ) (t : ℝ) (n : ℕ) :
    HasDerivAt
      (fun u : ℝ =>
        ((n + 1).divisors.card : ℂ) *
          (n + 1 : ℂ) ^ (-linePt u) *
          smoothAFECutoff ((n + 1 : ℝ) / (N : ℝ)))
      (smoothAFEZetaSquarePrimalHeightDerivativeTerm N t n) t := by
  have hn : (n + 1 : ℂ) ≠ 0 := by exact_mod_cast (show n + 1 ≠ 0 by omega)
  have hpC :=
    (Complex.hasStrictDerivAt_const_cpow
      (x := (n + 1 : ℂ)) (y := -linePt t) (Or.inl hn)).hasDerivAt
  have hp := hpC.comp t (hasDerivAt_linePt t).neg
  have h := (hp.const_mul ((n + 1).divisors.card : ℂ)).mul_const
    (smoothAFECutoff ((n + 1 : ℝ) / (N : ℝ)))
  simpa only [Function.comp_apply, Pi.neg_apply,
    smoothAFEZetaSquarePrimalHeightDerivativeTerm] using h

/-- Absolute summability of the differentiated primal source at the reference phase. -/
theorem summable_norm_smoothAFEZetaSquarePrimalHeightDerivativeTerm_zero
    {N : ℕ} (hN : 4 ≤ N) :
    Summable (fun n : ℕ =>
      ‖smoothAFEZetaSquarePrimalHeightDerivativeTerm N 0 n‖) := by
  obtain ⟨K, hK, hcut⟩ := exists_norm_smoothAFEZetaSquarePrimalCutoff_high_le
  let C : ℝ := 16 * K * (N : ℝ)
  let q : ℕ → ℝ := fun n => C *
    (((n + 1).divisors.card : ℝ) * (n + 1 : ℝ) ^ (-(5 / 4 : ℝ)))
  have hbase : Summable (fun m : ℕ =>
      (m.divisors.card : ℝ) * (m : ℝ) ^ (-(5 / 4 : ℝ))) :=
    Sieve.summable_card_divisors_mul_rpow (by norm_num)
  have hq : Summable q := by
    simpa only [q, Function.comp_apply, Nat.succ_eq_add_one,
      Nat.cast_add, Nat.cast_one] using
      ((hbase.comp_injective Nat.succ_injective).mul_left C)
  refine Summable.of_nonneg_of_le (fun n => norm_nonneg _) (fun n => ?_) hq
  have hm1 : 1 ≤ n + 1 := by omega
  have hm0 : (0 : ℝ) < n + 1 := by positivity
  have hcut' := hcut hN hm1
  have hlog0 : 0 ≤ Real.log (n + 1 : ℝ) :=
    Real.log_nonneg (by exact_mod_cast hm1)
  have hlog : Real.log (n + 1 : ℝ) ≤
      4 * (n + 1 : ℝ) ^ (1 / 4 : ℝ) := by
    have hraw := Real.log_le_rpow_div (le_of_lt hm0) (show (0 : ℝ) < 1 / 4 by norm_num)
    calc
      Real.log (n + 1 : ℝ) ≤ (n + 1 : ℝ) ^ (1 / 4 : ℝ) / (1 / 4 : ℝ) := hraw
      _ = 4 * (n + 1 : ℝ) ^ (1 / 4 : ℝ) := by
        norm_num [div_eq_mul_inv]
        ring
  have hcast : (n : ℂ) + 1 = (((n : ℝ) + 1 : ℝ) : ℂ) := by norm_cast
  have hnormlog : ‖Complex.log (n + 1 : ℂ)‖ = Real.log (n + 1 : ℝ) := by
    rw [hcast, ← Complex.ofReal_log hm0.le, Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonneg hlog0]
  simp_rw [smoothAFEZetaSquarePrimalHeightDerivativeTerm, norm_mul]
  rw [Complex.norm_natCast, hnormlog, norm_natSucc_cpow_neg_linePt]
  norm_num only [norm_neg, norm_I, mul_one]
  have hp0 : 0 ≤ (n + 1 : ℝ) ^ (-(1 / 2 : ℝ)) := Real.rpow_nonneg hm0.le _
  have hd0 : 0 ≤ ((n + 1).divisors.card : ℝ) := by positivity
  have hcutAFE :
      ‖smoothAFECutoff ((n + 1 : ℝ) / (N : ℝ))‖ ≤
        4 * K * (N : ℝ) / (n + 1 : ℝ) := by
    have hNR : (N : ℝ) ≠ 0 := by positivity
    rw [← smoothAFEZetaSquarePrimalCutoff_mul_conductor hNR]
    simpa only [Nat.cast_add, Nat.cast_one] using hcut'
  have hinner :
      (n + 1 : ℝ) ^ (-(1 / 2 : ℝ)) * Real.log (n + 1 : ℝ) ≤
        (n + 1 : ℝ) ^ (-(1 / 2 : ℝ)) *
          (4 * (n + 1 : ℝ) ^ (1 / 4 : ℝ)) :=
    mul_le_mul_of_nonneg_left hlog hp0
  have hpow :
      (n + 1 : ℝ) ^ (1 / 4 : ℝ) *
          (n + 1 : ℝ) ^ (-(1 / 2 : ℝ)) *
          (n + 1 : ℝ) ^ (-1 : ℝ) =
        (n + 1 : ℝ) ^ (-(5 / 4 : ℝ)) := by
    rw [← Real.rpow_add hm0, ← Real.rpow_add hm0]
    congr 1
    ring
  calc
    ((n + 1).divisors.card : ℝ) *
          ((n + 1 : ℝ) ^ (-(1 / 2 : ℝ)) *
            Real.log (n + 1 : ℝ)) *
          ‖smoothAFECutoff ((n + 1 : ℝ) / (N : ℝ))‖
        ≤ ((n + 1).divisors.card : ℝ) *
          ((n + 1 : ℝ) ^ (-(1 / 2 : ℝ)) *
            (4 * (n + 1 : ℝ) ^ (1 / 4 : ℝ))) *
          (4 * K * (N : ℝ) / (n + 1 : ℝ)) := by
            have hfirst := mul_le_mul_of_nonneg_left hinner hd0
            have hcut0 : 0 ≤
                ((n + 1).divisors.card : ℝ) *
                ((4 * (n + 1 : ℝ) ^ (1 / 4 : ℝ)) *
                    (n + 1 : ℝ) ^ (-(1 / 2 : ℝ))) := by positivity
            exact (mul_le_mul_of_nonneg_right hfirst (norm_nonneg _)).trans
              (by
                convert mul_le_mul_of_nonneg_left hcutAFE hcut0 using 1 <;> ring)
    _ = q n := by
      dsimp only [q, C]
      have hdiv :
          4 * K * (N : ℝ) / (n + 1 : ℝ) =
            4 * K * (N : ℝ) * (n + 1 : ℝ) ^ (-1 : ℝ) := by
        rw [Real.rpow_neg_one]
        ring
      rw [hdiv]
      calc
        ((n + 1).divisors.card : ℝ) *
              ((n + 1 : ℝ) ^ (-(1 / 2 : ℝ)) *
                (4 * (n + 1 : ℝ) ^ (1 / 4 : ℝ))) *
              (4 * K * (N : ℝ) * (n + 1 : ℝ) ^ (-1 : ℝ)) =
            16 * K * (N : ℝ) * ((n + 1).divisors.card : ℝ) *
              ((n + 1 : ℝ) ^ (1 / 4 : ℝ) *
                (n + 1 : ℝ) ^ (-(1 / 2 : ℝ)) *
                (n + 1 : ℝ) ^ (-1 : ℝ)) := by ring
        _ = 16 * K * (N : ℝ) *
            (((n + 1).divisors.card : ℝ) *
              (n + 1 : ℝ) ^ (-(5 / 4 : ℝ))) := by rw [hpow]; ring

/-- Differentiated primal coefficient norms are independent of observation height. -/
theorem norm_smoothAFEZetaSquarePrimalHeightDerivativeTerm_independent
    (N : ℕ) (t : ℝ) (n : ℕ) :
    ‖smoothAFEZetaSquarePrimalHeightDerivativeTerm N t n‖ =
      ‖smoothAFEZetaSquarePrimalHeightDerivativeTerm N 0 n‖ := by
  have hm0 : (0 : ℝ) < n + 1 := by positivity
  simp only [smoothAFEZetaSquarePrimalHeightDerivativeTerm,
    norm_mul, Complex.norm_natCast,
    norm_natSucc_cpow_neg_linePt, norm_neg, norm_I, mul_one]

/-- Absolute summability of the differentiated primal source at every observation height. -/
theorem summable_norm_smoothAFEZetaSquarePrimalHeightDerivativeTerm
    {N : ℕ} (hN : 4 ≤ N) (t : ℝ) :
    Summable (fun n : ℕ =>
      ‖smoothAFEZetaSquarePrimalHeightDerivativeTerm N t n‖) := by
  refine (summable_norm_smoothAFEZetaSquarePrimalHeightDerivativeTerm_zero hN).congr
    (fun n => ?_)
  exact (norm_smoothAFEZetaSquarePrimalHeightDerivativeTerm_independent N t n).symm

/-- The primal square-AFE source differentiates termwise in observation height. -/
theorem hasDerivAt_smoothAFEZetaSquarePrimalSourceField
    {N : ℕ} (hN : 4 ≤ N) (t : ℝ) :
    HasDerivAt (smoothAFEZetaSquarePrimalSourceField N)
      (smoothAFEZetaSquarePrimalHeightDerivativeSourceField N t) t := by
  let f : ℕ → ℝ → ℂ := fun n u =>
    ((n + 1).divisors.card : ℂ) *
      (n + 1 : ℂ) ^ (-linePt u) *
      smoothAFECutoff ((n + 1 : ℝ) / (N : ℝ))
  let f' : ℕ → ℝ → ℂ := fun n u =>
    smoothAFEZetaSquarePrimalHeightDerivativeTerm N u n
  let q : ℕ → ℝ := fun n =>
    ‖smoothAFEZetaSquarePrimalHeightDerivativeTerm N 0 n‖
  have hq : Summable q :=
    summable_norm_smoothAFEZetaSquarePrimalHeightDerivativeTerm_zero hN
  have hderiv : ∀ n u, HasDerivAt (f n) (f' n u) u :=
    fun n u => hasDerivAt_smoothAFEZetaSquarePrimalSourceTerm N u n
  have hbound : ∀ n u, ‖f' n u‖ ≤ q n := by
    intro n u
    exact (norm_smoothAFEZetaSquarePrimalHeightDerivativeTerm_independent N u n).le
  have hsum0 : Summable (fun n => f n 0) := by
    have hcoeff :=
      (summable_smoothAFEZetaSquarePrimalNatCoefficient_affine_masses hN 0).1
    have htail := hcoeff.comp_injective Nat.succ_injective
    apply Summable.of_norm
    refine htail.congr (fun n => ?_)
    simp only [Function.comp_apply, Nat.succ_eq_add_one]
    rw [smoothAFEZetaSquarePrimalNatCoefficient_succ]
    have hNR : (N : ℝ) ≠ 0 := by positivity
    rw [smoothAFEZetaSquarePrimalCutoff_mul_conductor hNR]
    dsimp only [f]
    congr 2
    unfold linePt
    norm_num
  have h := hasDerivAt_tsum hq hderiv hbound hsum0 t
  change HasDerivAt
    (fun u : ℝ => ∑' n : ℕ,
      ((n + 1).divisors.card : ℂ) *
        (n + 1 : ℂ) ^ (-linePt u) *
        smoothAFECutoff ((n + 1 : ℝ) / (N : ℝ)))
    (smoothAFEZetaSquarePrimalHeightDerivativeSourceField N t) t
  simpa only [f, f', smoothAFEZetaSquarePrimalHeightDerivativeSourceField] using h

end RHTower
