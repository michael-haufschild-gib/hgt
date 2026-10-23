import GaloisForLFunctions.RHTower.Sieve.DirichletWideRectangle
import GaloisForLFunctions.RHTower.Sieve.ZetaLineLittleOh
import GaloisForLFunctions.RHTower.Sieve.HarmonicLogBound
import GaloisForLFunctions.RHTower.Sieve.ZetaPartialSumTruncation

/-!
# `ζ` itself on the wide rectangle

The wide strip of `DirichletWideRectangle` is a bound for a partial sum; `ζ` differs from it by the
two truncation terms of `norm_riemannZeta_le_partialSum`, both `O(1)` at the truncation point
`lineTruncation t ≍ t³`.

Right of the abscissa no derivative test is needed: `∑_{k ≤ N} k^(-Re w) ≤ ∑_{k ≤ N} 1/k
≤ 1 + log N`, which is `O(log t)`.  Combining the two sides gives a bound that is uniform on a
rectangle straddling `Re s = 1`, which is what a Landau-type disc estimate consumes.
-/

namespace RHTower.Sieve

open Finset Complex

/-- Index bridge for a general abscissa. -/
theorem sum_Icc_cpow_eq_sum_Ico_sigma (σ t : ℝ) (M : ℕ) :
    ∑ k ∈ Finset.Icc 1 M, ((k : ℝ) : ℂ) ^ (-((σ : ℂ) + Complex.I * (t : ℂ)))
      = ∑ n ∈ Finset.Ico (1 : ℕ) (M + 1), (n : ℂ) ^ (-(σ : ℂ) - Complex.I * (t : ℂ)) := by
  rw [← Finset.Ico_add_one_right_eq_Icc]
  refine Finset.sum_congr rfl fun k _ => ?_
  have hbase : ((k : ℝ) : ℂ) = (k : ℂ) := by push_cast; ring
  have hexp : (-((σ : ℂ) + Complex.I * (t : ℂ))) = -(σ : ℂ) - Complex.I * (t : ℂ) := by ring
  rw [hbase, hexp]

/-- The truncation point is logarithmically small on the scale of `t`. -/
theorem log_lineTruncation_le {t : ℝ} (ht16 : 16 * Real.pi ≤ t) :
    Real.log ((lineTruncation t : ℕ) : ℝ) ≤ 3 * wideScale t + 1 := by
  have hπ := Real.pi_pos
  have ht0 : (0 : ℝ) < t := by nlinarith
  have hlog2pos : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hlog2le : Real.log 2 ≤ 1 := by
    have h2 := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num); linarith
  have hN1 : 1 ≤ lineTruncation t := one_le_lineTruncation t
  have hNR : (1 : ℝ) ≤ ((lineTruncation t : ℕ) : ℝ) := by exact_mod_cast hN1
  have hadd := lineTruncation_add_one t
  have hcast : ((lineTruncation t : ℕ) : ℝ) + 1 = (2 : ℝ) ^ (topExponent t + 1) := by
    have := congrArg (fun n : ℕ => (n : ℝ)) hadd
    push_cast at this
    linarith
  have hle : ((lineTruncation t : ℕ) : ℝ) ≤ (2 : ℝ) ^ (topExponent t + 1) := by linarith
  have hlog : Real.log ((lineTruncation t : ℕ) : ℝ)
      ≤ ((topExponent t : ℕ) : ℝ) * Real.log 2 + Real.log 2 := by
    have h1 : Real.log ((lineTruncation t : ℕ) : ℝ) ≤ Real.log ((2 : ℝ) ^ (topExponent t + 1)) :=
      Real.log_le_log (by linarith) hle
    rw [Real.log_pow] at h1
    push_cast at h1
    linarith
  have hT : ((topExponent t : ℕ) : ℝ) ≤ 3 * Real.log (t / (8 * Real.pi)) / Real.log 2 :=
    topExponent_le (by linarith)
  have hTlog : Real.log (t / (8 * Real.pi)) ≤ wideScale t := by
    refine Real.log_le_log (by positivity) ?_
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith
  rw [le_div_iff₀ hlog2pos] at hT
  linarith

/-- **Right of the abscissa the harmonic sum suffices.** -/
theorem norm_riemannZeta_ge_one_le {w : ℂ} (hre : 1 ≤ w.re) (him : 1 ≤ |w.im|) {N : ℕ}
    (hN : 1 ≤ N) :
    ‖riemannZeta w‖ ≤ 2 + Real.log ((N : ℕ) : ℝ) + ‖w‖ / ((N : ℕ) : ℝ) := by
  have hNR : (1 : ℝ) ≤ ((N : ℕ) : ℝ) := by exact_mod_cast hN
  have hN0 : (0 : ℝ) < ((N : ℕ) : ℝ) := by linarith
  have hw0 : 0 < w.re := by linarith
  have hwne1 : w ≠ 1 := by
    intro hcon
    rw [hcon] at him
    simp at him
    linarith
  have hbase := norm_riemannZeta_le_partialSum hw0 hwne1 hN
  -- head
  have hhead : ‖∑ k ∈ Finset.Icc 1 N, ((k : ℝ) : ℂ) ^ (-w)‖ ≤ 1 + Real.log ((N : ℕ) : ℝ) := by
    refine le_trans (norm_sum_le _ _) ?_
    refine le_trans (Finset.sum_le_sum (fun k hk => ?_))
      (sum_Icc_one_div_le_one_add_log N)
    have hk1 : 1 ≤ k := (Finset.mem_Icc.mp hk).1
    have hkR : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk1
    have hk0 : (0 : ℝ) < (k : ℝ) := by linarith
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hk0, Complex.neg_re]
    have hmono : (k : ℝ) ^ (-w.re) ≤ (k : ℝ) ^ (-1 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le hkR (by linarith)
    have hone : (k : ℝ) ^ (-1 : ℝ) = 1 / (k : ℝ) := by
      rw [Real.rpow_neg hk0.le, Real.rpow_one, one_div]
    rw [hone] at hmono
    exact hmono
  -- first tail
  have htail1 : ((N : ℕ) : ℝ) ^ (1 - w.re) / ‖w - 1‖ ≤ 1 := by
    have h1 : ((N : ℕ) : ℝ) ^ (1 - w.re) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos hNR (by linarith)
    have h2 : (1 : ℝ) ≤ ‖w - 1‖ := by
      refine le_trans him ?_
      have : |(w - 1).im| ≤ ‖w - 1‖ := Complex.abs_im_le_norm _
      simpa using this
    have h3 : (0 : ℝ) < ‖w - 1‖ := by linarith
    rw [div_le_one h3]
    linarith
  -- second tail
  have htail2 : ‖w‖ * (((N : ℕ) : ℝ) ^ (-w.re) / w.re) ≤ ‖w‖ / ((N : ℕ) : ℝ) := by
    have hmono : ((N : ℕ) : ℝ) ^ (-w.re) ≤ ((N : ℕ) : ℝ) ^ (-1 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le hNR (by linarith)
    have hone : ((N : ℕ) : ℝ) ^ (-1 : ℝ) = 1 / ((N : ℕ) : ℝ) := by
      rw [Real.rpow_neg hN0.le, Real.rpow_one, one_div]
    rw [hone] at hmono
    have hdiv : ((N : ℕ) : ℝ) ^ (-w.re) / w.re ≤ 1 / ((N : ℕ) : ℝ) := by
      have hstep : ((N : ℕ) : ℝ) ^ (-w.re) / w.re ≤ ((N : ℕ) : ℝ) ^ (-w.re) / 1 := by
        apply div_le_div_of_nonneg_left (Real.rpow_nonneg hN0.le _) (by norm_num) hre
      rw [div_one] at hstep
      linarith
    have hwnn : (0 : ℝ) ≤ ‖w‖ := norm_nonneg w
    calc ‖w‖ * (((N : ℕ) : ℝ) ^ (-w.re) / w.re)
        ≤ ‖w‖ * (1 / ((N : ℕ) : ℝ)) := mul_le_mul_of_nonneg_left hdiv hwnn
      _ = ‖w‖ / ((N : ℕ) : ℝ) := by ring
  linarith

/-! ### The rectangle bound for `ζ` -/

/-- **`ζ` on the wide rectangle.**  Left of the abscissa the derivative-test chain applies; right of
it the harmonic sum does. -/
theorem norm_riemannZeta_wide_le {w : ℂ} {K : ℕ}
    (hre : 1 - 1 / (6 * (2 : ℝ) ^ K) ≤ w.re) (hre2 : w.re ≤ 2)
    (him : 16 * Real.pi ≤ w.im) (hL : (10 : ℝ) ^ 16 ≤ wideScale w.im) (hK10 : 10 ≤ K)
    (hKlo : wideScale w.im < 120 * (2 : ℝ) ^ K * Real.log (wideScale w.im) ^ 2)
    (hKhi : 100 * (2 : ℝ) ^ K ≤ wideScale w.im) :
    ‖riemannZeta w‖ ≤ wideScale w.im ^ (34 : ℕ) + 5 := by
  have hπ := Real.pi_pos
  have hπd : (3.14 : ℝ) < Real.pi := Real.pi_gt_d2
  have ht0 : (0 : ℝ) < w.im := by linarith
  have hL0 : (0 : ℝ) < wideScale w.im := by linarith
  have hone : (1 : ℝ) ≤ wideScale w.im := by linarith
  have hPK : (0 : ℝ) < (2 : ℝ) ^ K := by positivity
  have hKR : (10 : ℝ) ≤ (K : ℝ) := by exact_mod_cast hK10
  have hbig : (1024 : ℝ) ≤ (2 : ℝ) ^ K := by
    calc (1024 : ℝ) = (2 : ℝ) ^ (10 : ℕ) := by norm_num
      _ ≤ (2 : ℝ) ^ K := pow_le_pow_right₀ (by norm_num) hK10
  have hetasmall : 1 / (6 * (2 : ℝ) ^ K) ≤ 1 / 2 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    linarith
  have hN1 : 1 ≤ lineTruncation w.im := one_le_lineTruncation w.im
  have hNR : (1 : ℝ) ≤ ((lineTruncation w.im : ℕ) : ℝ) := by exact_mod_cast hN1
  have hlogN := log_lineTruncation_le him
  have h34 : (3 : ℝ) * wideScale w.im + 4 ≤ wideScale w.im ^ (34 : ℕ) + 5 := by
    have hpow : wideScale w.im ^ (2 : ℕ) ≤ wideScale w.im ^ (34 : ℕ) :=
      pow_le_pow_right₀ hone (by norm_num)
    have hsq : (3 : ℝ) * wideScale w.im ≤ wideScale w.im ^ (2 : ℕ) := by
      linarith only [mul_le_mul_of_nonneg_right
        (by linarith only [hL] : (3 : ℝ) ≤ wideScale w.im) hL0.le]
    linarith only [hpow, hsq]
  have himabs : (1 : ℝ) ≤ |w.im| := by
    rw [abs_of_pos ht0]; linarith
  rcases lt_or_ge w.re 1 with hlt | hge
  · -- left of the abscissa
    have hσ0 : 0 < w.re := by linarith [hetasmall, hre]
    have hstrip : 1 - w.re ≤ 1 / (6 * (2 : ℝ) ^ K) := by linarith
    have hhead := norm_dirichlet_wide_rect hσ0 hlt him hL hK10 hKlo hKhi hstrip
    have hwne1 : w ≠ 1 := by
      intro hcon
      rw [hcon] at ht0
      simp at ht0
    have hbase := norm_riemannZeta_le_partialSum hσ0 hwne1 hN1
    have hw : ((w.re : ℝ) : ℂ) + Complex.I * ((w.im : ℝ) : ℂ) = w := by
      rw [mul_comm]; exact Complex.re_add_im w
    have hsum : ∑ k ∈ Finset.Icc 1 (lineTruncation w.im), ((k : ℝ) : ℂ) ^ (-w)
        = ∑ n ∈ Finset.Ico (1 : ℕ) (2 ^ (topExponent w.im + 1)),
            (n : ℂ) ^ (-((w.re : ℝ) : ℂ) - Complex.I * ((w.im : ℝ) : ℂ)) := by
      rw [← lineTruncation_add_one w.im,
        show (-w) = -(((w.re : ℝ) : ℂ) + Complex.I * ((w.im : ℝ) : ℂ)) by rw [hw]]
      exact sum_Icc_cpow_eq_sum_Ico_sigma w.re w.im (lineTruncation w.im)
    rw [hsum] at hbase
    -- the two tail terms
    have hexpL : Real.exp (wideScale w.im) ≤ w.im := by
      have hq : Real.exp (wideScale w.im) = w.im / (2 * Real.pi) :=
        Real.exp_log (by positivity)
      rw [hq, div_le_iff₀ (by positivity)]
      linarith only [mul_le_mul_of_nonneg_left
        (by linarith only [hπd] : (1 : ℝ) ≤ 2 * Real.pi) ht0.le]
    have htiny : ((lineTruncation w.im : ℕ) : ℝ) ^ (1 - w.re) ≤ w.im := by
      have hlogNnn : (0 : ℝ) ≤ Real.log ((lineTruncation w.im : ℕ) : ℝ) :=
        Real.log_nonneg hNR
      have hprod : (1 - w.re) * Real.log ((lineTruncation w.im : ℕ) : ℝ) ≤ wideScale w.im := by
        have hx := thirtyone_le_log_wideScale hL
        have hsq := hundredtwenty_log_sq_le_sqrt hL
        have hs : Real.sqrt (wideScale w.im) * Real.sqrt (wideScale w.im) = wideScale w.im :=
          Real.mul_self_sqrt hL0.le
        have hsnn : (0 : ℝ) ≤ Real.sqrt (wideScale w.im) := Real.sqrt_nonneg _
        have hs1 : (1 : ℝ) ≤ Real.sqrt (wideScale w.im) :=
          (Real.le_sqrt zero_le_one hL0.le).2 (by linarith)
        have hsmall : 1 - w.re ≤ 1 / (6 * (2 : ℝ) ^ K) := hstrip
        have hKlow : 1 / (6 * (2 : ℝ) ^ K) ≤ 20 * Real.log (wideScale w.im) ^ 2
            / wideScale w.im := by
          rw [div_le_div_iff₀ (by positivity) hL0]
          linarith only [hKlo]
        have hstep : (1 - w.re) * Real.log ((lineTruncation w.im : ℕ) : ℝ)
            ≤ (20 * Real.log (wideScale w.im) ^ 2 / wideScale w.im)
              * (3 * wideScale w.im + 1) := by
          have h1 : (1 - w.re) ≤ 20 * Real.log (wideScale w.im) ^ 2 / wideScale w.im :=
            le_trans hsmall hKlow
          have h2 : (0 : ℝ) ≤ 20 * Real.log (wideScale w.im) ^ 2 / wideScale w.im := by
            positivity
          exact (mul_le_mul_of_nonneg_right h1 hlogNnn).trans (mul_le_mul_of_nonneg_left hlogN h2)
        have hcancel : (20 * Real.log (wideScale w.im) ^ 2 / wideScale w.im)
            * (3 * wideScale w.im + 1) ≤ 80 * Real.log (wideScale w.im) ^ 2 := by
          rw [div_mul_eq_mul_div, div_le_iff₀ hL0]
          linarith only [mul_le_mul_of_nonneg_left hone (sq_nonneg (Real.log (wideScale w.im)))]
        linarith only [hstep, hcancel, hsq, hs, mul_le_mul_of_nonneg_left hs1 hsnn]
      have hrw : ((lineTruncation w.im : ℕ) : ℝ) ^ (1 - w.re)
          = Real.exp (Real.log ((lineTruncation w.im : ℕ) : ℝ) * (1 - w.re)) :=
        Real.rpow_def_of_pos (by linarith) _
      rw [hrw]
      calc Real.exp (Real.log ((lineTruncation w.im : ℕ) : ℝ) * (1 - w.re))
          ≤ Real.exp (wideScale w.im) := by
            refine Real.exp_le_exp.mpr ?_
            linarith only [hprod]
        _ ≤ w.im := hexpL
    have hnormsub : w.im ≤ ‖w - 1‖ := by
      have h := Complex.abs_im_le_norm (w - 1)
      have him' : (w - 1).im = w.im := by simp
      rw [him', abs_of_pos ht0] at h
      exact h
    have htail1 : ((lineTruncation w.im : ℕ) : ℝ) ^ (1 - w.re) / ‖w - 1‖ ≤ 1 := by
      rw [div_le_one (by linarith)]
      linarith
    have htail2 : ‖w‖ * (((lineTruncation w.im : ℕ) : ℝ) ^ (-w.re) / w.re) ≤ 4 := by
      have hmono : ((lineTruncation w.im : ℕ) : ℝ) ^ (-w.re)
          ≤ ((lineTruncation w.im : ℕ) : ℝ) ^ (-(1 : ℝ) / 2) :=
        Real.rpow_le_rpow_of_exponent_le hNR (by linarith)
      have hsqrtN : ((lineTruncation w.im : ℕ) : ℝ) ^ (-(1 : ℝ) / 2)
          = 1 / Real.sqrt ((lineTruncation w.im : ℕ) : ℝ) := by
        rw [Real.sqrt_eq_rpow, show (-(1 : ℝ) / 2) = -((1 : ℝ) / 2) by ring,
          Real.rpow_neg (by linarith)]
        exact (one_div _).symm
      have hNbig : (w.im + 2) ^ 2 ≤ 4 * ((lineTruncation w.im : ℕ) : ℝ) := by
        have hcube := cube_sub_one_le_lineTruncation (t := w.im) (by linarith)
        have hπlt : Real.pi < 3.15 := Real.pi_lt_d2
        have hπ2 : Real.pi ^ 2 < 10 := by
          linarith only [mul_self_lt_mul_self Real.pi_pos.le Real.pi_lt_d2]
        have hπ3 : Real.pi ^ 3 < 32 := by
          linarith only [mul_lt_mul'' hπ2 Real.pi_lt_d2 (sq_nonneg Real.pi) Real.pi_pos.le]
        have hform : (w.im / (8 * Real.pi)) ^ (3 : ℕ) = w.im ^ 3 / (512 * Real.pi ^ 3) := by
          field_simp; ring
        have himbig : (10 : ℝ) ^ 5 ≤ w.im := by
          have h := Real.add_one_le_exp (wideScale w.im)
          linarith only [h, hexpL, hL]
        have hden : w.im ^ 3 / 16384 ≤ (w.im / (8 * Real.pi)) ^ (3 : ℕ) := by
          rw [hform, div_le_div_iff₀ (by norm_num) (by positivity)]
          linarith only [mul_le_mul_of_nonneg_left hπ3.le (pow_pos ht0 3).le]
        have hcu2 : (10 : ℝ) ^ 5 * w.im ^ 2 ≤ w.im ^ 3 := by
          linarith only [mul_le_mul_of_nonneg_right himbig (sq_nonneg w.im)]
        linarith only [hcube, hden, hcu2, himbig, mul_le_mul_of_nonneg_right himbig ht0.le]
      have hsq : Real.sqrt ((lineTruncation w.im : ℕ) : ℝ)
          * Real.sqrt ((lineTruncation w.im : ℕ) : ℝ) = ((lineTruncation w.im : ℕ) : ℝ) :=
        Real.mul_self_sqrt (by linarith)
      have hsnn : (0 : ℝ) ≤ Real.sqrt ((lineTruncation w.im : ℕ) : ℝ) := Real.sqrt_nonneg _
      have hs2 : w.im + 2 ≤ 2 * Real.sqrt ((lineTruncation w.im : ℕ) : ℝ) := by
        have hhalf : (w.im + 2) / 2 ≤ Real.sqrt ((lineTruncation w.im : ℕ) : ℝ) :=
          (Real.le_sqrt (by positivity) (by linarith only [hNR])).mpr
            (by linarith only [hNbig])
        linarith only [hhalf]
      have hspos : (0 : ℝ) < Real.sqrt ((lineTruncation w.im : ℕ) : ℝ) := by
        linarith only [hs2, ht0]
      have hwnorm : ‖w‖ ≤ 2 + w.im := by
        refine le_trans (Complex.norm_le_abs_re_add_abs_im w) ?_
        rw [abs_of_pos ht0, abs_of_pos hσ0]
        linarith
      have hwnn : (0 : ℝ) ≤ ‖w‖ := norm_nonneg w
      have hdiv : ((lineTruncation w.im : ℕ) : ℝ) ^ (-w.re) / w.re
          ≤ 2 / Real.sqrt ((lineTruncation w.im : ℕ) : ℝ) := by
        have hre2' : (1 : ℝ) / 2 ≤ w.re := by linarith
        have hnum : ((lineTruncation w.im : ℕ) : ℝ) ^ (-w.re)
            ≤ 1 / Real.sqrt ((lineTruncation w.im : ℕ) : ℝ) := by
          rw [← hsqrtN]; exact hmono
        have hnn : (0 : ℝ) ≤ ((lineTruncation w.im : ℕ) : ℝ) ^ (-w.re) :=
          Real.rpow_nonneg (by linarith) _
        have hmul : ((lineTruncation w.im : ℕ) : ℝ) ^ (-w.re)
            * Real.sqrt ((lineTruncation w.im : ℕ) : ℝ) ≤ 1 := by
          have hh := mul_le_mul_of_nonneg_right hnum hspos.le
          rwa [one_div, inv_mul_cancel₀ (ne_of_gt hspos)] at hh
        rw [div_le_div_iff₀ hσ0 hspos]
        linarith only [hmul, hre2']
      calc ‖w‖ * (((lineTruncation w.im : ℕ) : ℝ) ^ (-w.re) / w.re)
          ≤ (2 + w.im) * (2 / Real.sqrt ((lineTruncation w.im : ℕ) : ℝ)) := by
            refine mul_le_mul hwnorm hdiv (by positivity) (by linarith)
        _ ≤ 4 := by
            rw [mul_comm, div_mul_eq_mul_div, div_le_iff₀ hspos]
            linarith only [hs2]
    linarith only [hbase, hhead, htail1, htail2]
  · -- right of the abscissa
    have h := norm_riemannZeta_ge_one_le hge himabs hN1
    have hwnorm : ‖w‖ ≤ 2 + w.im := by
      refine le_trans (Complex.norm_le_abs_re_add_abs_im w) ?_
      rw [abs_of_pos ht0, abs_of_pos (by linarith : (0 : ℝ) < w.re)]
      linarith
    have hdiv : ‖w‖ / ((lineTruncation w.im : ℕ) : ℝ) ≤ 1 := by
      rw [div_le_one (by linarith)]
      refine le_trans hwnorm ?_
      have hcube := cube_sub_one_le_lineTruncation (t := w.im) (by linarith)
      have hπ2 : Real.pi ^ 2 < 10 := by
        linarith only [mul_self_lt_mul_self Real.pi_pos.le Real.pi_lt_d2]
      have hπ3 : Real.pi ^ 3 < 32 := by
        linarith only [mul_lt_mul'' hπ2 Real.pi_lt_d2 (sq_nonneg Real.pi) Real.pi_pos.le]
      have hform : (w.im / (8 * Real.pi)) ^ (3 : ℕ) = w.im ^ 3 / (512 * Real.pi ^ 3) := by
        field_simp; ring
      have hexpL : Real.exp (wideScale w.im) ≤ w.im := by
        have hq : Real.exp (wideScale w.im) = w.im / (2 * Real.pi) :=
          Real.exp_log (by positivity)
        rw [hq, div_le_iff₀ (by positivity)]
        linarith only [mul_le_mul_of_nonneg_left
          (by linarith only [hπd] : (1 : ℝ) ≤ 2 * Real.pi) ht0.le]
      have himbig : (10 : ℝ) ^ 5 ≤ w.im := by
        have hh := Real.add_one_le_exp (wideScale w.im)
        linarith only [hh, hexpL, hL]
      have hden : w.im ^ 3 / 16384 ≤ (w.im / (8 * Real.pi)) ^ (3 : ℕ) := by
        rw [hform, div_le_div_iff₀ (by norm_num) (by positivity)]
        linarith only [mul_le_mul_of_nonneg_left hπ3.le (pow_pos ht0 3).le]
      have hsq2 : (10 : ℝ) ^ 10 ≤ w.im ^ 2 := by
        linarith only [pow_le_pow_left₀ (by norm_num) himbig 2]
      have hcu : (10 : ℝ) ^ 10 * w.im ≤ w.im ^ 3 := by
        linarith only [mul_le_mul_of_nonneg_right hsq2 ht0.le]
      linarith only [hcube, hden, hcu, himbig]
    linarith only [h, hlogN, h34, hdiv]

end RHTower.Sieve
