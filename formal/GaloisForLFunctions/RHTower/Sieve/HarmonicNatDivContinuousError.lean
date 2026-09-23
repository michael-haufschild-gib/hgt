import GaloisForLFunctions.RHTower.Sieve.NatDivLogPowerEndpointError
import GaloisForLFunctions.RHTower.Sieve.HarmonicLogWindowLowerMoments
import GaloisForLFunctions.RHTower.Sieve.GhsScaleSequence

open Finset

namespace RHTower.Sieve

noncomputable section

private theorem one_div_natDiv_add_one_le_div
    {N e : ℕ} (hN : 0 < N) (he : 0 < e) :
    1 / (((N / e + 1 : ℕ) : ℝ)) ≤ (e : ℝ) / (N : ℝ) := by
  have hlt := lt_div_add_one_mul (N := N) (D := e) he
  have hltR : (N : ℝ) < ((N / e + 1 : ℕ) : ℝ) * (e : ℝ) := by
    exact_mod_cast hlt
  have hden : (0 : ℝ) < ((N / e + 1 : ℕ) : ℝ) := by positivity
  have hNR : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  rw [div_le_div_iff₀ hden hNR]
  linarith

private theorem natCast_div_antitone_denominator
    {e L U : ℕ} (hL : 0 < L) (hLU : L ≤ U) :
    (e : ℝ) / (U : ℝ) ≤ (e : ℝ) / (L : ℝ) := by
  have hLR : (0 : ℝ) < (L : ℝ) := by exact_mod_cast hL
  have hUR : (0 : ℝ) < (U : ℝ) := by exact_mod_cast hL.trans_le hLU
  have hLUR : (L : ℝ) ≤ (U : ℝ) := by exact_mod_cast hLU
  have heR : (0 : ℝ) ≤ (e : ℝ) := by positivity
  exact div_le_div_of_nonneg_left heR hLR hLUR

private theorem log_nat_succ_le_log_nat_succ {L U : ℕ} (hLU : L ≤ U) :
    Real.log ((L + 1 : ℕ) : ℝ) ≤ Real.log ((U + 1 : ℕ) : ℝ) := by
  apply Real.log_le_log (by positivity)
  exact_mod_cast Nat.add_le_add_right hLU 1

theorem abs_harmonicLogWindowMoment_zero_natDiv_sub_continuous_le
    {L U e : ℕ} (he : 0 < e) (hscale : 8 * e ≤ L) (hLU : L ≤ U) :
    |harmonicLogWindowMoment 0 (L / e) (U / e) -
        (Real.log ((U : ℝ) / (e : ℝ)) -
          Real.log ((L : ℝ) / (e : ℝ)))| ≤
      3 * (e : ℝ) / (L : ℝ) := by
  have hL : 0 < L := by nlinarith
  have hU : 0 < U := hL.trans_le hLU
  have heL : e ≤ L := by nlinarith
  have heU : e ≤ U := heL.trans hLU
  have hA : 8 ≤ L / e := (Nat.le_div_iff_mul_le he).2 hscale
  have hAB : L / e ≤ U / e := Nat.div_le_div_right hLU
  have hsharp := abs_harmonicLogWindowMoment_zero_sub_log_le hA hAB
  have htail0 : 0 ≤ RHTower.logPowDivId 0 (U / e + 1 : ℕ) := by
    norm_num [RHTower.logPowDivId]
    positivity
  have hquad :
      |harmonicLogWindowMoment 0 (L / e) (U / e) -
          (Real.log (U / e + 1 : ℕ) - Real.log (L / e + 1 : ℕ))| ≤
        (e : ℝ) / (L : ℝ) := by
    refine hsharp.trans ?_
    calc
      RHTower.logPowDivId 0 (L / e + 1 : ℕ) -
          RHTower.logPowDivId 0 (U / e + 1 : ℕ) ≤
        RHTower.logPowDivId 0 (L / e + 1 : ℕ) := sub_le_self _ htail0
      _ = 1 / (((L / e + 1 : ℕ) : ℝ)) := by
        norm_num [RHTower.logPowDivId]
      _ ≤ (e : ℝ) / (L : ℝ) := one_div_natDiv_add_one_le_div hL he
  have hu := abs_log_natDiv_add_one_sub_log_div_le hU he
  have hl := abs_log_natDiv_add_one_sub_log_div_le hL he
  have hdiv := natCast_div_antitone_denominator (e := e) hL hLU
  have hend :
      |(Real.log (U / e + 1 : ℕ) - Real.log (L / e + 1 : ℕ)) -
          (Real.log ((U : ℝ) / (e : ℝ)) - Real.log ((L : ℝ) / (e : ℝ)))| ≤
        2 * ((e : ℝ) / (L : ℝ)) := by
    calc
      |(Real.log (U / e + 1 : ℕ) - Real.log (L / e + 1 : ℕ)) -
          (Real.log ((U : ℝ) / (e : ℝ)) - Real.log ((L : ℝ) / (e : ℝ)))| =
        |(Real.log (U / e + 1 : ℕ) - Real.log ((U : ℝ) / (e : ℝ))) +
          -(Real.log (L / e + 1 : ℕ) - Real.log ((L : ℝ) / (e : ℝ)))| := by
            congr 1
            ring
      _ ≤ |Real.log (U / e + 1 : ℕ) - Real.log ((U : ℝ) / (e : ℝ))| +
          |Real.log (L / e + 1 : ℕ) - Real.log ((L : ℝ) / (e : ℝ))| := by
            simpa only [abs_neg] using abs_add_le
              (Real.log (U / e + 1 : ℕ) - Real.log ((U : ℝ) / (e : ℝ)))
              (-(Real.log (L / e + 1 : ℕ) - Real.log ((L : ℝ) / (e : ℝ))))
      _ ≤ (e : ℝ) / (U : ℝ) + (e : ℝ) / (L : ℝ) := add_le_add hu hl
      _ ≤ 2 * ((e : ℝ) / (L : ℝ)) := by linarith
  calc
    |harmonicLogWindowMoment 0 (L / e) (U / e) -
        (Real.log ((U : ℝ) / (e : ℝ)) - Real.log ((L : ℝ) / (e : ℝ)))| ≤
      |harmonicLogWindowMoment 0 (L / e) (U / e) -
          (Real.log (U / e + 1 : ℕ) - Real.log (L / e + 1 : ℕ))| +
        |(Real.log (U / e + 1 : ℕ) - Real.log (L / e + 1 : ℕ)) -
          (Real.log ((U : ℝ) / (e : ℝ)) - Real.log ((L : ℝ) / (e : ℝ)))| := by
            simpa only [sub_add_sub_cancel] using abs_add_le
              (harmonicLogWindowMoment 0 (L / e) (U / e) -
                (Real.log (U / e + 1 : ℕ) - Real.log (L / e + 1 : ℕ)))
              ((Real.log (U / e + 1 : ℕ) - Real.log (L / e + 1 : ℕ)) -
                (Real.log ((U : ℝ) / (e : ℝ)) - Real.log ((L : ℝ) / (e : ℝ))))
    _ ≤ (e : ℝ) / (L : ℝ) + 2 * ((e : ℝ) / (L : ℝ)) := add_le_add hquad hend
    _ = 3 * (e : ℝ) / (L : ℝ) := by ring

theorem abs_harmonicLogWindowMoment_one_natDiv_sub_continuous_le
    {L U e : ℕ} (he : 0 < e) (hscale : 8 * e ≤ L) (hLU : L ≤ U) :
    |harmonicLogWindowMoment 1 (L / e) (U / e) -
        (Real.log ((U : ℝ) / (e : ℝ)) ^ (2 : ℕ) / 2 -
          Real.log ((L : ℝ) / (e : ℝ)) ^ (2 : ℕ) / 2)| ≤
      3 * Real.log ((U + 1 : ℕ) : ℝ) * ((e : ℝ) / (L : ℝ)) := by
  have hL : 0 < L := by nlinarith
  have hU : 0 < U := hL.trans_le hLU
  have heL : e ≤ L := by nlinarith
  have heU : e ≤ U := heL.trans hLU
  have hA : 8 ≤ L / e := (Nat.le_div_iff_mul_le he).2 hscale
  have hAB : L / e ≤ U / e := Nat.div_le_div_right hLU
  let K : ℝ := Real.log ((U + 1 : ℕ) : ℝ)
  have hK0 : 0 ≤ K := by
    dsimp [K]
    exact Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ U + 1))
  have hlogA : Real.log ((L / e + 1 : ℕ) : ℝ) ≤ K := by
    dsimp [K]
    apply Real.log_le_log (by positivity)
    exact_mod_cast (Nat.add_le_add_right ((Nat.div_le_self L e).trans hLU) 1)
  have hsharp := abs_harmonicLogWindowMoment_one_sub_logSquare_le hA hAB
  have htail0 : 0 ≤ RHTower.logPowDivId 1 (U / e + 1 : ℕ) := by
    rw [RHTower.logPowDivId]
    positivity
  have hrec := one_div_natDiv_add_one_le_div hL he
  have hquad :
      |harmonicLogWindowMoment 1 (L / e) (U / e) -
          (Real.log (U / e + 1 : ℕ) ^ (2 : ℕ) / 2 -
            Real.log (L / e + 1 : ℕ) ^ (2 : ℕ) / 2)| ≤
        K * ((e : ℝ) / (L : ℝ)) := by
    refine hsharp.trans ?_
    calc
      RHTower.logPowDivId 1 (L / e + 1 : ℕ) -
          RHTower.logPowDivId 1 (U / e + 1 : ℕ) ≤
        RHTower.logPowDivId 1 (L / e + 1 : ℕ) := sub_le_self _ htail0
      _ = Real.log ((L / e + 1 : ℕ) : ℝ) *
          (1 / (((L / e + 1 : ℕ) : ℝ))) := by
            rw [RHTower.logPowDivId]
            norm_num
            ring
      _ ≤ K * ((e : ℝ) / (L : ℝ)) :=
        mul_le_mul hlogA hrec (by positivity) hK0
  have hu := abs_log_natDiv_add_one_sq_sub_log_div_sq_le hU he heU
  have hl := abs_log_natDiv_add_one_sq_sub_log_div_sq_le hL he heL
  have hdiv := natCast_div_antitone_denominator (e := e) hL hLU
  have hlogLU := log_nat_succ_le_log_nat_succ hLU
  have hu' :
      |Real.log (U / e + 1 : ℕ) ^ (2 : ℕ) - Real.log ((U : ℝ) / (e : ℝ)) ^ (2 : ℕ)| / 2 ≤
        K * ((e : ℝ) / (L : ℝ)) := by
    calc
      _ ≤ (2 * K * ((e : ℝ) / (U : ℝ))) / 2 := div_le_div_of_nonneg_right hu (by norm_num)
      _ = K * ((e : ℝ) / (U : ℝ)) := by ring
      _ ≤ K * ((e : ℝ) / (L : ℝ)) := mul_le_mul_of_nonneg_left hdiv hK0
  have hl' :
      |Real.log (L / e + 1 : ℕ) ^ (2 : ℕ) - Real.log ((L : ℝ) / (e : ℝ)) ^ (2 : ℕ)| / 2 ≤
        K * ((e : ℝ) / (L : ℝ)) := by
    calc
      _ ≤ (2 * Real.log ((L + 1 : ℕ) : ℝ) * ((e : ℝ) / (L : ℝ))) / 2 :=
        div_le_div_of_nonneg_right hl (by norm_num)
      _ = Real.log ((L + 1 : ℕ) : ℝ) * ((e : ℝ) / (L : ℝ)) := by ring
      _ ≤ K * ((e : ℝ) / (L : ℝ)) :=
        mul_le_mul_of_nonneg_right hlogLU (by positivity)
  have hend :
      |(Real.log (U / e + 1 : ℕ) ^ (2 : ℕ) / 2 -
          Real.log (L / e + 1 : ℕ) ^ (2 : ℕ) / 2) -
        (Real.log ((U : ℝ) / (e : ℝ)) ^ (2 : ℕ) / 2 -
          Real.log ((L : ℝ) / (e : ℝ)) ^ (2 : ℕ) / 2)| ≤
        2 * K * ((e : ℝ) / (L : ℝ)) := by
    calc
      _ = |(Real.log (U / e + 1 : ℕ) ^ (2 : ℕ) -
            Real.log ((U : ℝ) / (e : ℝ)) ^ (2 : ℕ)) / 2 -
          (Real.log (L / e + 1 : ℕ) ^ (2 : ℕ) -
            Real.log ((L : ℝ) / (e : ℝ)) ^ (2 : ℕ)) / 2| := by
              congr 1
              ring
      _ ≤ |Real.log (U / e + 1 : ℕ) ^ (2 : ℕ) -
            Real.log ((U : ℝ) / (e : ℝ)) ^ (2 : ℕ)| / 2 +
          |Real.log (L / e + 1 : ℕ) ^ (2 : ℕ) -
            Real.log ((L : ℝ) / (e : ℝ)) ^ (2 : ℕ)| / 2 := by
              calc
                _ ≤ |(Real.log (U / e + 1 : ℕ) ^ (2 : ℕ) -
                        Real.log ((U : ℝ) / (e : ℝ)) ^ (2 : ℕ)) / 2| +
                    |(Real.log (L / e + 1 : ℕ) ^ (2 : ℕ) -
                        Real.log ((L : ℝ) / (e : ℝ)) ^ (2 : ℕ)) / 2| := abs_sub _ _
                _ = _ := by rw [abs_div, abs_div]; norm_num
      _ ≤ K * ((e : ℝ) / (L : ℝ)) + K * ((e : ℝ) / (L : ℝ)) := add_le_add hu' hl'
      _ = 2 * K * ((e : ℝ) / (L : ℝ)) := by ring
  calc
    |harmonicLogWindowMoment 1 (L / e) (U / e) -
        (Real.log ((U : ℝ) / (e : ℝ)) ^ (2 : ℕ) / 2 -
          Real.log ((L : ℝ) / (e : ℝ)) ^ (2 : ℕ) / 2)| ≤
      |harmonicLogWindowMoment 1 (L / e) (U / e) -
          (Real.log (U / e + 1 : ℕ) ^ (2 : ℕ) / 2 -
            Real.log (L / e + 1 : ℕ) ^ (2 : ℕ) / 2)| +
        |(Real.log (U / e + 1 : ℕ) ^ (2 : ℕ) / 2 -
            Real.log (L / e + 1 : ℕ) ^ (2 : ℕ) / 2) -
          (Real.log ((U : ℝ) / (e : ℝ)) ^ (2 : ℕ) / 2 -
            Real.log ((L : ℝ) / (e : ℝ)) ^ (2 : ℕ) / 2)| := by
              have heq :
                  harmonicLogWindowMoment 1 (L / e) (U / e) -
                      (Real.log ((U : ℝ) / (e : ℝ)) ^ (2 : ℕ) / 2 -
                        Real.log ((L : ℝ) / (e : ℝ)) ^ (2 : ℕ) / 2) =
                    (harmonicLogWindowMoment 1 (L / e) (U / e) -
                      (Real.log (U / e + 1 : ℕ) ^ (2 : ℕ) / 2 -
                        Real.log (L / e + 1 : ℕ) ^ (2 : ℕ) / 2)) +
                    ((Real.log (U / e + 1 : ℕ) ^ (2 : ℕ) / 2 -
                        Real.log (L / e + 1 : ℕ) ^ (2 : ℕ) / 2) -
                      (Real.log ((U : ℝ) / (e : ℝ)) ^ (2 : ℕ) / 2 -
                        Real.log ((L : ℝ) / (e : ℝ)) ^ (2 : ℕ) / 2)) := by ring
              rw [heq]
              exact abs_add_le _ _
    _ ≤ K * ((e : ℝ) / (L : ℝ)) + 2 * K * ((e : ℝ) / (L : ℝ)) :=
      add_le_add hquad hend
    _ = 3 * Real.log ((U + 1 : ℕ) : ℝ) * ((e : ℝ) / (L : ℝ)) := by
      dsimp [K]
      ring

theorem abs_harmonicLogWindowMoment_two_natDiv_sub_continuous_le
    {L U e : ℕ} (he : 0 < e) (hscale : 8 * e ≤ L) (hLU : L ≤ U) :
    |harmonicLogWindowMoment 2 (L / e) (U / e) -
        (Real.log ((U : ℝ) / (e : ℝ)) ^ (3 : ℕ) / 3 -
          Real.log ((L : ℝ) / (e : ℝ)) ^ (3 : ℕ) / 3)| ≤
      3 * Real.log ((U + 1 : ℕ) : ℝ) ^ (2 : ℕ) * ((e : ℝ) / (L : ℝ)) := by
  have hL : 0 < L := by nlinarith
  have hU : 0 < U := hL.trans_le hLU
  have heL : e ≤ L := by nlinarith
  have heU : e ≤ U := heL.trans hLU
  have hA : 8 ≤ L / e := (Nat.le_div_iff_mul_le he).2 hscale
  have hAB : L / e ≤ U / e := Nat.div_le_div_right hLU
  let K : ℝ := Real.log ((U + 1 : ℕ) : ℝ)
  have hK0 : 0 ≤ K := by
    dsimp [K]
    exact Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ U + 1))
  have hlogA : Real.log ((L / e + 1 : ℕ) : ℝ) ≤ K := by
    dsimp [K]
    apply Real.log_le_log (by positivity)
    exact_mod_cast (Nat.add_le_add_right ((Nat.div_le_self L e).trans hLU) 1)
  have hsharp := abs_harmonicLogWindowMoment_two_sub_cubic_le hA hAB
  have htail0 : 0 ≤ RHTower.logPowDivId 2 (U / e + 1 : ℕ) := by
    rw [RHTower.logPowDivId]
    positivity
  have hrec := one_div_natDiv_add_one_le_div hL he
  have hlogA0 : 0 ≤ Real.log ((L / e + 1 : ℕ) : ℝ) :=
    Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ L / e + 1))
  have hlogA2 : Real.log ((L / e + 1 : ℕ) : ℝ) ^ (2 : ℕ) ≤ K ^ (2 : ℕ) := by
    have h1 := mul_le_mul_of_nonneg_left hlogA hlogA0
    have h2 := mul_le_mul_of_nonneg_right hlogA hK0
    nlinarith
  have hquad :
      |harmonicLogWindowMoment 2 (L / e) (U / e) -
          (Real.log (U / e + 1 : ℕ) ^ (3 : ℕ) / 3 -
            Real.log (L / e + 1 : ℕ) ^ (3 : ℕ) / 3)| ≤
        K ^ (2 : ℕ) * ((e : ℝ) / (L : ℝ)) := by
    refine hsharp.trans ?_
    calc
      RHTower.logPowDivId 2 (L / e + 1 : ℕ) -
          RHTower.logPowDivId 2 (U / e + 1 : ℕ) ≤
        RHTower.logPowDivId 2 (L / e + 1 : ℕ) := sub_le_self _ htail0
      _ = Real.log ((L / e + 1 : ℕ) : ℝ) ^ (2 : ℕ) *
          (1 / (((L / e + 1 : ℕ) : ℝ))) := by
            rw [RHTower.logPowDivId]
            ring
      _ ≤ K ^ (2 : ℕ) * ((e : ℝ) / (L : ℝ)) :=
        mul_le_mul hlogA2 hrec (by positivity) (sq_nonneg K)
  have hu := abs_log_natDiv_add_one_cube_sub_log_div_cube_le hU he heU
  have hl := abs_log_natDiv_add_one_cube_sub_log_div_cube_le hL he heL
  have hdiv := natCast_div_antitone_denominator (e := e) hL hLU
  have hlogLU := log_nat_succ_le_log_nat_succ hLU
  have hlogL0 : 0 ≤ Real.log ((L + 1 : ℕ) : ℝ) :=
    Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ L + 1))
  have hlogL2 : Real.log ((L + 1 : ℕ) : ℝ) ^ (2 : ℕ) ≤ K ^ (2 : ℕ) := by
    have h1 := mul_le_mul_of_nonneg_left hlogLU hlogL0
    have h2 := mul_le_mul_of_nonneg_right hlogLU hK0
    nlinarith
  have hu' :
      |Real.log (U / e + 1 : ℕ) ^ (3 : ℕ) - Real.log ((U : ℝ) / (e : ℝ)) ^ (3 : ℕ)| / 3 ≤
        K ^ (2 : ℕ) * ((e : ℝ) / (L : ℝ)) := by
    calc
      _ ≤ (3 * K ^ (2 : ℕ) * ((e : ℝ) / (U : ℝ))) / 3 :=
        div_le_div_of_nonneg_right hu (by norm_num)
      _ = K ^ (2 : ℕ) * ((e : ℝ) / (U : ℝ)) := by ring
      _ ≤ K ^ (2 : ℕ) * ((e : ℝ) / (L : ℝ)) :=
        mul_le_mul_of_nonneg_left hdiv (sq_nonneg K)
  have hl' :
      |Real.log (L / e + 1 : ℕ) ^ (3 : ℕ) - Real.log ((L : ℝ) / (e : ℝ)) ^ (3 : ℕ)| / 3 ≤
        K ^ (2 : ℕ) * ((e : ℝ) / (L : ℝ)) := by
    calc
      _ ≤ (3 * Real.log ((L + 1 : ℕ) : ℝ) ^ (2 : ℕ) *
          ((e : ℝ) / (L : ℝ))) / 3 :=
        div_le_div_of_nonneg_right hl (by norm_num)
      _ = Real.log ((L + 1 : ℕ) : ℝ) ^ (2 : ℕ) * ((e : ℝ) / (L : ℝ)) := by ring
      _ ≤ K ^ (2 : ℕ) * ((e : ℝ) / (L : ℝ)) :=
        mul_le_mul_of_nonneg_right hlogL2 (by positivity)
  have hend :
      |(Real.log (U / e + 1 : ℕ) ^ (3 : ℕ) / 3 -
          Real.log (L / e + 1 : ℕ) ^ (3 : ℕ) / 3) -
        (Real.log ((U : ℝ) / (e : ℝ)) ^ (3 : ℕ) / 3 -
          Real.log ((L : ℝ) / (e : ℝ)) ^ (3 : ℕ) / 3)| ≤
        2 * K ^ (2 : ℕ) * ((e : ℝ) / (L : ℝ)) := by
    calc
      _ = |(Real.log (U / e + 1 : ℕ) ^ (3 : ℕ) -
            Real.log ((U : ℝ) / (e : ℝ)) ^ (3 : ℕ)) / 3 -
          (Real.log (L / e + 1 : ℕ) ^ (3 : ℕ) -
            Real.log ((L : ℝ) / (e : ℝ)) ^ (3 : ℕ)) / 3| := by
              congr 1
              ring
      _ ≤ |Real.log (U / e + 1 : ℕ) ^ (3 : ℕ) -
            Real.log ((U : ℝ) / (e : ℝ)) ^ (3 : ℕ)| / 3 +
          |Real.log (L / e + 1 : ℕ) ^ (3 : ℕ) -
            Real.log ((L : ℝ) / (e : ℝ)) ^ (3 : ℕ)| / 3 := by
              calc
                _ ≤ |(Real.log (U / e + 1 : ℕ) ^ (3 : ℕ) -
                        Real.log ((U : ℝ) / (e : ℝ)) ^ (3 : ℕ)) / 3| +
                    |(Real.log (L / e + 1 : ℕ) ^ (3 : ℕ) -
                        Real.log ((L : ℝ) / (e : ℝ)) ^ (3 : ℕ)) / 3| := abs_sub _ _
                _ = _ := by rw [abs_div, abs_div]; norm_num
      _ ≤ K ^ (2 : ℕ) * ((e : ℝ) / (L : ℝ)) + K ^ (2 : ℕ) * ((e : ℝ) / (L : ℝ)) :=
        add_le_add hu' hl'
      _ = 2 * K ^ (2 : ℕ) * ((e : ℝ) / (L : ℝ)) := by ring
  calc
    |harmonicLogWindowMoment 2 (L / e) (U / e) -
        (Real.log ((U : ℝ) / (e : ℝ)) ^ (3 : ℕ) / 3 -
          Real.log ((L : ℝ) / (e : ℝ)) ^ (3 : ℕ) / 3)| ≤
      |harmonicLogWindowMoment 2 (L / e) (U / e) -
          (Real.log (U / e + 1 : ℕ) ^ (3 : ℕ) / 3 -
            Real.log (L / e + 1 : ℕ) ^ (3 : ℕ) / 3)| +
        |(Real.log (U / e + 1 : ℕ) ^ (3 : ℕ) / 3 -
            Real.log (L / e + 1 : ℕ) ^ (3 : ℕ) / 3) -
          (Real.log ((U : ℝ) / (e : ℝ)) ^ (3 : ℕ) / 3 -
            Real.log ((L : ℝ) / (e : ℝ)) ^ (3 : ℕ) / 3)| := by
              have heq :
                  harmonicLogWindowMoment 2 (L / e) (U / e) -
                      (Real.log ((U : ℝ) / (e : ℝ)) ^ (3 : ℕ) / 3 -
                        Real.log ((L : ℝ) / (e : ℝ)) ^ (3 : ℕ) / 3) =
                    (harmonicLogWindowMoment 2 (L / e) (U / e) -
                      (Real.log (U / e + 1 : ℕ) ^ (3 : ℕ) / 3 -
                        Real.log (L / e + 1 : ℕ) ^ (3 : ℕ) / 3)) +
                    ((Real.log (U / e + 1 : ℕ) ^ (3 : ℕ) / 3 -
                        Real.log (L / e + 1 : ℕ) ^ (3 : ℕ) / 3) -
                      (Real.log ((U : ℝ) / (e : ℝ)) ^ (3 : ℕ) / 3 -
                        Real.log ((L : ℝ) / (e : ℝ)) ^ (3 : ℕ) / 3)) := by ring
              rw [heq]
              exact abs_add_le _ _
    _ ≤ K ^ (2 : ℕ) * ((e : ℝ) / (L : ℝ)) + 2 * K ^ (2 : ℕ) * ((e : ℝ) / (L : ℝ)) :=
      add_le_add hquad hend
    _ = 3 * Real.log ((U + 1 : ℕ) : ℝ) ^ (2 : ℕ) * ((e : ℝ) / (L : ℝ)) := by
      dsimp [K]
      ring

end

end RHTower.Sieve
