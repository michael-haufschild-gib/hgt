import GaloisForLFunctions.RHTower.AcceleratedWoldType
import GaloisForLFunctions.RHTower.MobiusPrimeApertureDifferentialOrder

/-!
# Accelerated type of the Boolean prime diagonal

The scalar normalization forced by the Boolean equality diagonal below cutoff `N` is
`2 ^ π(N)`.  Prime number theorem gives `log π(N) / log N → 1`; combining this with Mertens'
product theorem proves the exact saturated accelerated type

`a_N * ell2 (2 ^ π(N)) → exp (-γ)`.
-/

open Filter Topology

namespace RHTower

noncomputable section

/-- Natural-cutoff specialization of the real prime-counting asymptotic. -/
theorem tendsto_primeCounting_nat_ratio :
    Tendsto (fun N : ℕ => (Nat.primeCounting N : ℝ) /
      ((N : ℝ) / Real.log (N : ℝ))) atTop (nhds 1) := by
  have hcast : Tendsto (fun N : ℕ => (N : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop
  have h := tendsto_primeCounting_ratio.comp hcast
  refine h.congr' (Eventually.of_forall fun N => ?_)
  change (Nat.primeCounting ⌊(N : ℝ)⌋₊ : ℝ) /
      ((N : ℝ) / Real.log (N : ℝ)) = _
  rw [Nat.floor_natCast]

/-- Logarithmic prime-counting asymptotic: `log π(N) / log N → 1`. -/
theorem tendsto_log_primeCounting_div_log :
    Tendsto (fun N : ℕ => Real.log (Nat.primeCounting N : ℝ) /
      Real.log (N : ℝ)) atTop (nhds 1) := by
  let r : ℕ → ℝ := fun N => (Nat.primeCounting N : ℝ) /
    ((N : ℝ) / Real.log (N : ℝ))
  have hr : Tendsto r atTop (nhds 1) := tendsto_primeCounting_nat_ratio
  have hlogr : Tendsto (fun N => Real.log (r N)) atTop (nhds 0) := by
    change Tendsto (Real.log ∘ r) atTop (nhds 0)
    simpa only [Real.log_one] using
      (Real.continuousAt_log one_ne_zero).tendsto.comp hr
  have hlogN : Tendsto (fun N : ℕ => Real.log (N : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hinvlogN : Tendsto (fun N : ℕ => (Real.log (N : ℝ))⁻¹) atTop (nhds 0) :=
    hlogN.inv_tendsto_atTop
  have hlogrdiv : Tendsto (fun N : ℕ => Real.log (r N) / Real.log (N : ℝ))
      atTop (nhds 0) := by
    simpa [div_eq_mul_inv] using hlogr.mul hinvlogN
  have hloglogdiv : Tendsto (fun N : ℕ =>
      Real.log (Real.log (N : ℝ)) / Real.log (N : ℝ)) atTop (nhds 0) :=
    Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp hlogN
  have htarget : Tendsto (fun N : ℕ =>
      1 - Real.log (Real.log (N : ℝ)) / Real.log (N : ℝ) +
        Real.log (r N) / Real.log (N : ℝ)) atTop (nhds 1) := by
    simpa using (tendsto_const_nhds.sub hloglogdiv).add hlogrdiv
  refine htarget.congr' ?_
  filter_upwards [hr.eventually (eventually_gt_nhds zero_lt_one),
    eventually_gt_atTop (3 : ℕ)] with N hrN hN
  have hNr : (1 : ℝ) < (N : ℝ) := by exact_mod_cast (show 1 < N by omega)
  have hlogNpos : 0 < Real.log (N : ℝ) := Real.log_pos hNr
  have hNpos : 0 < (N : ℝ) := by positivity
  have hden : 0 < (N : ℝ) / Real.log (N : ℝ) := div_pos hNpos hlogNpos
  have hpiform : (Nat.primeCounting N : ℝ) = r N *
      ((N : ℝ) / Real.log (N : ℝ)) := by
    dsimp [r]
    field_simp
  have hpi : 0 < (Nat.primeCounting N : ℝ) := by
    rw [hpiform]
    exact mul_pos hrN hden
  rw [hpiform, Real.log_mul (ne_of_gt hrN) (ne_of_gt hden),
    Real.log_div (ne_of_gt hNpos) (ne_of_gt hlogNpos)]
  field_simp
  ring

/-- Mertens' product times `log π(N)` has the standard Euler--Mascheroni limit. -/
theorem tendsto_mertensProduct_mul_log_primeCounting :
    Tendsto (fun N : ℕ => mertensPrimeProductBelow N *
      Real.log (Nat.primeCounting N : ℝ)) atTop
      (nhds (Real.exp (-Real.eulerMascheroniConstant))) := by
  have hmul := tendsto_mertensPrimeProductBelow_mul_log.mul
    tendsto_log_primeCounting_div_log
  rw [mul_one] at hmul
  refine hmul.congr' ?_
  filter_upwards [eventually_gt_atTop (1 : ℕ)] with N hN
  have hlogN : Real.log (N : ℝ) ≠ 0 := by
    exact ne_of_gt (Real.log_pos (by exact_mod_cast hN))
  field_simp

/-- Boolean entropy scale for the prime cube below `N`. -/
def booleanPrimeDiagonalScale (N : ℕ) : ℝ :=
  (2 : ℝ) ^ Nat.primeCounting N

theorem booleanPrimeDiagonalScale_pos (N : ℕ) : 0 < booleanPrimeDiagonalScale N := by
  exact pow_pos (by norm_num) _

theorem log_booleanPrimeDiagonalScale (N : ℕ) :
    Real.log (booleanPrimeDiagonalScale N) =
      (Nat.primeCounting N : ℝ) * Real.log 2 := by
  rw [booleanPrimeDiagonalScale, Real.log_pow]

/-- **Exact accelerated type of the forced Boolean entropy normalization.** -/
theorem tendsto_mertensProduct_mul_ell2_booleanPrimeDiagonalScale :
    Tendsto (fun N : ℕ => mertensPrimeProductBelow N *
      ell2 (booleanPrimeDiagonalScale N)) atTop
      (nhds (Real.exp (-Real.eulerMascheroniConstant))) := by
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
  have hpi : Tendsto (fun N : ℕ => (Nat.primeCounting N : ℝ)) atTop atTop := by
    have h := Real.tendsto_exp_atTop.comp hlogpi
    refine h.congr' ?_
    filter_upwards [tendsto_primeCounting_nat_ratio.eventually
      (eventually_gt_nhds zero_lt_one), eventually_gt_atTop (3 : ℕ)] with N hr hN
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
    change Real.exp (Real.log (Nat.primeCounting N : ℝ)) = _
    rw [Real.exp_log hpipos]
  have hbig : Tendsto (fun N : ℕ => Real.log (booleanPrimeDiagonalScale N))
      atTop atTop := by
    have h := Filter.Tendsto.const_mul_atTop (Real.log_pos (by norm_num : (1 : ℝ) < 2)) hpi
    refine h.congr' (Eventually.of_forall fun N => ?_)
    change Real.log 2 * (Nat.primeCounting N : ℝ) =
      Real.log (booleanPrimeDiagonalScale N)
    rw [log_booleanPrimeDiagonalScale]
    ring
  have hconst : Tendsto (fun N : ℕ => mertensPrimeProductBelow N *
      Real.log (Real.log 2)) atTop (nhds 0) := by
    simpa using tendsto_mertensPrimeProductBelow_zero.mul_const (Real.log (Real.log 2))
  have hV : Tendsto (fun N : ℕ => mertensPrimeProductBelow N *
      Real.log (Real.log (booleanPrimeDiagonalScale N))) atTop
      (nhds (Real.exp (-Real.eulerMascheroniConstant))) := by
    have hsum := tendsto_mertensProduct_mul_log_primeCounting.add hconst
    rw [add_zero] at hsum
    refine hsum.congr' ?_
    filter_upwards [tendsto_primeCounting_nat_ratio.eventually
      (eventually_gt_nhds zero_lt_one), eventually_gt_atTop (3 : ℕ)] with N hr hN
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
    rw [log_booleanPrimeDiagonalScale,
      Real.log_mul (ne_of_gt hpipos) (ne_of_gt (Real.log_pos (by norm_num : (1 : ℝ) < 2)))]
    ring
  exact tendsto_mertensProduct_mul_ell2_of_tendsto
    (Eventually.of_forall booleanPrimeDiagonalScale_pos) hbig hV

end

end RHTower
