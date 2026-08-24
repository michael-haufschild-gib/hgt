import GaloisForLFunctions.RHTower.WoldBooleanAcceleratedType

/-!
# Finite-Rees normalizations lose the Boolean prime diagonal

For the Mertens scale `a_N` and Boolean diagonal dimension `2 ^ π(N)`, every positive
normalization `c_N` satisfying `log⁺c_N = O(a_N⁻ᵋ)` for one fixed `K` has

`c_N / 2 ^ π(N) → 0`.

This is the exact scalar obstruction behind the finite-Rees Wold normalization mismatch.
-/

open Filter Topology Asymptotics

namespace RHTower

noncomputable section

/-- Every fixed power of `log N` is negligible compared with `π(N)`. -/
theorem tendsto_log_pow_div_primeCounting_zero (K : ℕ) :
    Tendsto (fun N : ℕ => Real.log (N : ℝ) ^ K /
      (Nat.primeCounting N : ℝ)) atTop (nhds 0) := by
  have hreal := Real.isLittleO_pow_log_id_atTop (n := K + 1)
  have hcast : Tendsto (fun N : ℕ => (N : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop
  have hsmall : Tendsto (fun N : ℕ =>
      Real.log (N : ℝ) ^ (K + 1) / (N : ℝ)) atTop (nhds 0) := by
    simpa [Function.comp_def] using hreal.tendsto_div_nhds_zero.comp hcast
  have hratioInv : Tendsto (fun N : ℕ =>
      ((N : ℝ) / Real.log (N : ℝ)) / (Nat.primeCounting N : ℝ))
      atTop (nhds 1) := by
    have h : Tendsto (fun N : ℕ =>
        ((Nat.primeCounting N : ℝ) / ((N : ℝ) / Real.log (N : ℝ)))⁻¹)
        atTop (nhds 1) := by
      simpa using tendsto_primeCounting_nat_ratio.inv₀ one_ne_zero
    refine h.congr' ?_
    filter_upwards [eventually_gt_atTop (3 : ℕ),
      tendsto_primeCounting_nat_ratio.eventually
        (eventually_gt_nhds zero_lt_one)] with N hN hr
    have hNr : (1 : ℝ) < (N : ℝ) := by exact_mod_cast (show 1 < N by omega)
    have hden : 0 < (N : ℝ) / Real.log (N : ℝ) :=
      div_pos (by positivity) (Real.log_pos hNr)
    have hpipos : 0 < (Nat.primeCounting N : ℝ) := by
      have hpiform : (Nat.primeCounting N : ℝ) =
          ((Nat.primeCounting N : ℝ) / ((N : ℝ) / Real.log (N : ℝ))) *
            ((N : ℝ) / Real.log (N : ℝ)) := by
        field_simp [ne_of_gt (Real.log_pos hNr)]
      rw [hpiform]
      exact mul_pos hr hden
    change ((Nat.primeCounting N : ℝ) / ((N : ℝ) / Real.log (N : ℝ)))⁻¹ = _
    field_simp
  have hprod := hsmall.mul hratioInv
  rw [zero_mul] at hprod
  refine hprod.congr' ?_
  filter_upwards [eventually_gt_atTop (3 : ℕ),
    tendsto_primeCounting_nat_ratio.eventually
      (eventually_gt_nhds zero_lt_one)] with N hN hr
  have hNr : (1 : ℝ) < (N : ℝ) := by exact_mod_cast (show 1 < N by omega)
  have hlog : Real.log (N : ℝ) ≠ 0 := ne_of_gt (Real.log_pos hNr)
  have hpipos : 0 < (Nat.primeCounting N : ℝ) := by
    have hden : 0 < (N : ℝ) / Real.log (N : ℝ) :=
      div_pos (by positivity) (Real.log_pos hNr)
    have hpiform : (Nat.primeCounting N : ℝ) =
        ((Nat.primeCounting N : ℝ) / ((N : ℝ) / Real.log (N : ℝ))) *
          ((N : ℝ) / Real.log (N : ℝ)) := by
      field_simp [hlog]
    rw [hpiform]
    exact mul_pos hr hden
  field_simp
  ring

/-- Every fixed inverse power of the Mertens product is negligible compared with `π(N)`. -/
theorem tendsto_mertensProduct_inv_pow_div_primeCounting_zero (K : ℕ) :
    Tendsto (fun N : ℕ => (mertensPrimeProductBelow N)⁻¹ ^ K /
      (Nat.primeCounting N : ℝ)) atTop (nhds 0) := by
  have hbase : Tendsto (fun N : ℕ =>
      (mertensPrimeProductBelow N)⁻¹ / Real.log (N : ℝ)) atTop
      (nhds (Real.exp (-Real.eulerMascheroniConstant))⁻¹) := by
    have hinv := tendsto_mertensPrimeProductBelow_mul_log.inv₀
      (Real.exp_ne_zero _)
    refine hinv.congr' ?_
    filter_upwards [eventually_gt_atTop (1 : ℕ)] with N hN
    have hlog : Real.log (N : ℝ) ≠ 0 :=
      ne_of_gt (Real.log_pos (by exact_mod_cast hN))
    have ha : mertensPrimeProductBelow N ≠ 0 :=
      ne_of_gt (mertensPrimeProductBelow_pos N)
    change (mertensPrimeProductBelow N * Real.log (N : ℝ))⁻¹ = _
    field_simp
  have hpow : Tendsto (fun N : ℕ =>
      ((mertensPrimeProductBelow N)⁻¹ / Real.log (N : ℝ)) ^ K) atTop
      (nhds ((Real.exp (-Real.eulerMascheroniConstant))⁻¹ ^ K)) :=
    hbase.pow K
  have hprod := hpow.mul (tendsto_log_pow_div_primeCounting_zero K)
  rw [mul_zero] at hprod
  refine hprod.congr' ?_
  filter_upwards [eventually_gt_atTop (3 : ℕ),
    tendsto_primeCounting_nat_ratio.eventually
      (eventually_gt_nhds zero_lt_one)] with N hN hr
  have hNr : (1 : ℝ) < (N : ℝ) := by exact_mod_cast (show 1 < N by omega)
  have hlog : Real.log (N : ℝ) ≠ 0 := ne_of_gt (Real.log_pos hNr)
  have hpipos : 0 < (Nat.primeCounting N : ℝ) := by
    have hden : 0 < (N : ℝ) / Real.log (N : ℝ) :=
      div_pos (by positivity) (Real.log_pos hNr)
    have hpiform : (Nat.primeCounting N : ℝ) =
        ((Nat.primeCounting N : ℝ) / ((N : ℝ) / Real.log (N : ℝ))) *
          ((N : ℝ) / Real.log (N : ℝ)) := by
      field_simp [hlog]
    rw [hpiform]
    exact mul_pos hr hden
  have ha : mertensPrimeProductBelow N ≠ 0 :=
    ne_of_gt (mertensPrimeProductBelow_pos N)
  rw [div_pow]
  field_simp

/-- Positive part `log⁺`. -/
def woldLogPos (x : ℝ) : ℝ := max (Real.log x) 0

/-- A finite-Rees bound forces `log⁺c_N / π(N) → 0`. -/
theorem tendsto_woldLogPos_div_primeCounting_zero_of_isBigO
    {c : ℕ → ℝ} {K : ℕ}
    (hO : (fun N => woldLogPos (c N)) =O[atTop]
      (fun N => (mertensPrimeProductBelow N)⁻¹ ^ K)) :
    Tendsto (fun N : ℕ => woldLogPos (c N) /
      (Nat.primeCounting N : ℝ)) atTop (nhds 0) := by
  obtain ⟨C, hC⟩ := hO.bound
  let D : ℝ := max C 0
  have hupper : Tendsto (fun N : ℕ => D *
      ((mertensPrimeProductBelow N)⁻¹ ^ K / (Nat.primeCounting N : ℝ)))
      atTop (nhds 0) := by
    simpa using
      (tendsto_mertensProduct_inv_pow_div_primeCounting_zero K).const_mul D
  have hpi : ∀ᶠ N : ℕ in atTop, 0 < (Nat.primeCounting N : ℝ) := by
    filter_upwards [eventually_gt_atTop (3 : ℕ),
      tendsto_primeCounting_nat_ratio.eventually
        (eventually_gt_nhds zero_lt_one)] with N hN hr
    have hNr : (1 : ℝ) < (N : ℝ) := by exact_mod_cast (show 1 < N by omega)
    have hlog : Real.log (N : ℝ) ≠ 0 := ne_of_gt (Real.log_pos hNr)
    have hden : 0 < (N : ℝ) / Real.log (N : ℝ) :=
      div_pos (by positivity) (Real.log_pos hNr)
    have hpiform : (Nat.primeCounting N : ℝ) =
        ((Nat.primeCounting N : ℝ) / ((N : ℝ) / Real.log (N : ℝ))) *
          ((N : ℝ) / Real.log (N : ℝ)) := by
      field_simp [hlog]
    rw [hpiform]
    exact mul_pos hr hden
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le'
    (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (nhds 0)) hupper ?_ ?_
  · filter_upwards [hpi] with N hpiN
    exact div_nonneg (le_max_right _ _) hpiN.le
  · filter_upwards [hpi, hC] with N hpiN hbound
    have ha : 0 < mertensPrimeProductBelow N := mertensPrimeProductBelow_pos N
    have hnonneg : 0 ≤ (mertensPrimeProductBelow N)⁻¹ ^ K :=
      pow_nonneg (inv_nonneg.mpr ha.le) _
    have hf : ‖woldLogPos (c N)‖ = woldLogPos (c N) :=
      Real.norm_of_nonneg (le_max_right _ _)
    have hg : ‖(mertensPrimeProductBelow N)⁻¹ ^ K‖ =
        (mertensPrimeProductBelow N)⁻¹ ^ K := by
      rw [Real.norm_of_nonneg hnonneg]
    have hD : C ≤ D := le_max_left _ _
    rw [hf, hg] at hbound
    calc
      woldLogPos (c N) / (Nat.primeCounting N : ℝ) ≤
          (D * (mertensPrimeProductBelow N)⁻¹ ^ K) /
            (Nat.primeCounting N : ℝ) := by
              gcongr
              exact hbound.trans (mul_le_mul_of_nonneg_right hD hnonneg)
      _ = D * ((mertensPrimeProductBelow N)⁻¹ ^ K /
          (Nat.primeCounting N : ℝ)) := by ring

/-- Prime counting tends to infinity along natural cutoffs. -/
theorem tendsto_primeCounting_nat_atTop :
    Tendsto (fun N : ℕ => (Nat.primeCounting N : ℝ)) atTop atTop := by
  have hlogN : Tendsto (fun N : ℕ => Real.log (N : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hlogpi : Tendsto (fun N : ℕ => Real.log (Nat.primeCounting N : ℝ))
      atTop atTop := by
    have h := tendsto_log_primeCounting_div_log.pos_mul_atTop one_pos hlogN
    refine h.congr' ?_
    filter_upwards [eventually_gt_atTop (1 : ℕ)] with N hN
    have hne : Real.log (N : ℝ) ≠ 0 :=
      ne_of_gt (Real.log_pos (by exact_mod_cast hN))
    field_simp
  have h := Real.tendsto_exp_atTop.comp hlogpi
  refine h.congr' ?_
  filter_upwards [eventually_gt_atTop (3 : ℕ),
    tendsto_primeCounting_nat_ratio.eventually
      (eventually_gt_nhds zero_lt_one)] with N hN hr
  have hNr : (1 : ℝ) < (N : ℝ) := by exact_mod_cast (show 1 < N by omega)
  have hlog : Real.log (N : ℝ) ≠ 0 := ne_of_gt (Real.log_pos hNr)
  have hden : 0 < (N : ℝ) / Real.log (N : ℝ) :=
    div_pos (by positivity) (Real.log_pos hNr)
  have hpipos : 0 < (Nat.primeCounting N : ℝ) := by
    have hpiform : (Nat.primeCounting N : ℝ) =
        ((Nat.primeCounting N : ℝ) / ((N : ℝ) / Real.log (N : ℝ))) *
          ((N : ℝ) / Real.log (N : ℝ)) := by
      field_simp [hlog]
    rw [hpiform]
    exact mul_pos hr hden
  change Real.exp (Real.log (Nat.primeCounting N : ℝ)) = _
  rw [Real.exp_log hpipos]

/-- **Every fixed finite-Rees Wold normalization loses the Boolean diagonal.** -/
theorem tendsto_finiteRees_booleanDiagonalMass_zero
    {c : ℕ → ℝ} (hc : ∀ᶠ N in atTop, 0 < c N) {K : ℕ}
    (hO : (fun N => woldLogPos (c N)) =O[atTop]
      (fun N => (mertensPrimeProductBelow N)⁻¹ ^ K)) :
    Tendsto (fun N : ℕ => c N / booleanPrimeDiagonalScale N) atTop (nhds 0) := by
  have hratio := tendsto_woldLogPos_div_primeCounting_zero_of_isBigO hO
  let d : ℝ := Real.log 2 / 2
  have hd : 0 < d := div_pos (Real.log_pos (by norm_num)) (by norm_num)
  have hsmall : ∀ᶠ N : ℕ in atTop,
      woldLogPos (c N) / (Nat.primeCounting N : ℝ) < d :=
    hratio.eventually (eventually_lt_nhds hd)
  have hpi : ∀ᶠ N : ℕ in atTop, 0 < (Nat.primeCounting N : ℝ) :=
    tendsto_primeCounting_nat_atTop.eventually_gt_atTop 0
  have hmul : Tendsto (fun N : ℕ => d * (Nat.primeCounting N : ℝ)) atTop atTop :=
    Filter.Tendsto.const_mul_atTop hd tendsto_primeCounting_nat_atTop
  have hupper : Tendsto (fun N : ℕ =>
      Real.exp (-(d * (Nat.primeCounting N : ℝ)))) atTop (nhds 0) := by
    have hneg := tendsto_neg_atTop_atBot.comp hmul
    exact Real.tendsto_exp_atBot.comp hneg
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le'
    (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (nhds 0)) hupper ?_ ?_
  · filter_upwards [hc] with N hcN
    exact (div_pos hcN (booleanPrimeDiagonalScale_pos N)).le
  · filter_upwards [hc, hsmall, hpi] with N hcN hsmallN hpiN
    have hlogc : Real.log (c N) ≤ woldLogPos (c N) := le_max_left _ _
    have hposScale := booleanPrimeDiagonalScale_pos N
    have hmulsmall : woldLogPos (c N) <
        d * (Nat.primeCounting N : ℝ) :=
      (div_lt_iff₀ hpiN).mp hsmallN
    have hexponent : Real.log (c N / booleanPrimeDiagonalScale N) ≤
        -(d * (Nat.primeCounting N : ℝ)) := by
      rw [Real.log_div (ne_of_gt hcN) (ne_of_gt hposScale),
        log_booleanPrimeDiagonalScale]
      dsimp [d] at hmulsmall ⊢
      nlinarith
    rw [← Real.exp_log (div_pos hcN hposScale)]
    exact Real.exp_le_exp.mpr hexponent

end

end RHTower
