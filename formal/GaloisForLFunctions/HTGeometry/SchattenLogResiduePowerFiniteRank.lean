import GaloisForLFunctions.RHTower.SchattenLogResidueFiniteRankPerturbation

/-! # Finite-rank invariance of logarithmic energy at every positive order -/

namespace GaloisForLFunctions.HTGeometry
noncomputable section
open RHTower Filter
open scoped Topology
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

theorem abs_schattenPowerPartialSum_sub_le_of_finiteRank
    {A B : H →L[ℂ] H} {p : ℝ} (hp : 0 < p) {r N : ℕ} (hAB : HasRankLE (A - B) r) :
    |schattenPowerPartialSum p A N - schattenPowerPartialSum p B N| ≤
      schattenPowerPartialSum p A r + schattenPowerPartialSum p B r := by
  have hshift {T S : H →L[ℂ] H} (hTS : HasRankLE (T - S) r) (n : ℕ) :
      approxNumber T (r + n) ^ p ≤ approxNumber S n ^ p := by
    have h := approxNumber_add_finiteRank_shift_le (A := S) hTS n
    rw [show S + (T - S) = T by abel, Nat.add_comm] at h
    exact Real.rpow_le_rpow (approxNumber_nonneg _ _) h hp.le
  have hBA : HasRankLE (B - A) r := by simpa only [neg_sub] using hAB.neg
  have hA := sum_range_le_prefix_add_of_shift
    (fun n => Real.rpow_nonneg (approxNumber_nonneg A n) p) (hshift hAB) N
  have hB := sum_range_le_prefix_add_of_shift
    (fun n => Real.rpow_nonneg (approxNumber_nonneg B n) p) (hshift hBA) N
  have hAr : 0 ≤ schattenPowerPartialSum p A r :=
    Finset.sum_nonneg fun n _ => Real.rpow_nonneg (approxNumber_nonneg A n) p
  have hBr : 0 ≤ schattenPowerPartialSum p B r :=
    Finset.sum_nonneg fun n _ => Real.rpow_nonneg (approxNumber_nonneg B n) p
  change schattenPowerPartialSum p A N ≤
    schattenPowerPartialSum p A r + schattenPowerPartialSum p B N at hA
  change schattenPowerPartialSum p B N ≤
    schattenPowerPartialSum p B r + schattenPowerPartialSum p A N at hB
  rw [abs_le]
  constructor <;> linarith

theorem tendsto_schattenPowerPartialSum_log_difference_of_finiteRank
    {A B : H →L[ℂ] H} {p : ℝ} (hp : 0 < p) {r : ℕ} (hAB : HasRankLE (A - B) r) :
    Tendsto (fun N : ℕ => schattenPowerPartialSum p A N / Real.log (N + 1) -
      schattenPowerPartialSum p B N / Real.log (N + 1)) atTop (𝓝 0) := by
  have hlog : Tendsto (fun N : ℕ => Real.log (N + 1 : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp
      (tendsto_natCast_atTop_atTop.atTop_add (tendsto_const_nhds (x := (1 : ℝ))))
  refine squeeze_zero_norm' (a := fun N : ℕ =>
    (schattenPowerPartialSum p A r + schattenPowerPartialSum p B r) / Real.log (N + 1))
    ?_ (tendsto_const_nhds.div_atTop hlog)
  filter_upwards with N
  rw [← sub_div, Real.norm_eq_abs, abs_div, abs_of_nonneg (Real.log_nonneg (by norm_cast; omega))]
  exact div_le_div_of_nonneg_right (abs_schattenPowerPartialSum_sub_le_of_finiteRank hp hAB)
    (Real.log_nonneg (by norm_cast; omega))

theorem hasSchattenLogResidue_iff_of_finiteRank
    {A B : H →L[ℂ] H} {p : ℝ} (hp : 0 < p) {r : ℕ} (hAB : HasRankLE (A - B) r) (R : ℝ) :
    HasSchattenLogResidue p A R ↔ HasSchattenLogResidue p B R := by
  have hd := tendsto_schattenPowerPartialSum_log_difference_of_finiteRank hp hAB
  constructor
  · intro hA
    have h := hA.sub hd
    rw [sub_zero] at h
    exact h.congr fun N => by simp
  · intro hB
    have h := hB.add hd
    rw [add_zero] at h
    exact h.congr fun N => by simp

end
end GaloisForLFunctions.HTGeometry
