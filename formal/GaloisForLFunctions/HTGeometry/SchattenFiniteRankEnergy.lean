import GaloisForLFunctions.HTGeometry.SchattenOneBanach
import GaloisForLFunctions.RHTower.NuclearRankOneSchatten
import GaloisForLFunctions.HTGeometry.PencilSufficiencyLaw

/-!
# Fatou closure and finite-rank interpolation for Schatten energy

This module supplies two general approximation-number tools used by positive Toeplitz
localization.  Uniform Schatten energy is lower semicontinuous under operator-norm convergence,
and a finite-rank operator's `q`-energy is bounded by its operator norm to power `q - 1` times its
trace norm.  A finite rank-one expansion then replaces trace norm by its projective mass.
-/

open Filter Topology ContinuousLinearMap

namespace GaloisForLFunctions.HTGeometry

noncomputable section

open RHTower

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- A uniform Schatten-energy bound survives operator-norm convergence. -/
theorem memSchattenClass_and_schattenEnergy_le_of_tendsto
    [CompleteSpace H]
    {p : ℝ} (hp : 0 < p) {T : ℕ → H →L[ℂ] H} {K : H →L[ℂ] H} {r : ℝ}
    (hT : ∀ m, MemSchattenClass p (T m))
    (hlim : Tendsto T atTop (nhds K))
    (hbound : ∀ᶠ m in atTop, schattenNorm p (T m) ^ p ≤ r) :
    MemSchattenClass p K ∧ schattenNorm p K ^ p ≤ r := by
  have hfinite (s : Finset ℕ) :
      ∑ n ∈ s, approxNumber K n ^ p ≤ r := by
    have hsumlim : Tendsto
        (fun m ↦ ∑ n ∈ s, approxNumber (T m) n ^ p) atTop
        (nhds (∑ n ∈ s, approxNumber K n ^ p)) := by
      apply tendsto_finsetSum
      intro n _
      have happrox :=
        (approxNumber_lipschitz (H := H) n).continuous.continuousAt.tendsto.comp hlim
      exact (Real.continuousAt_rpow_const _ p (Or.inr hp.le)).tendsto.comp happrox
    apply le_of_tendsto hsumlim
    filter_upwards [hbound] with m hm
    rw [schattenNorm_rpow_eq_tsum hp] at hm
    exact ((hT m).sum_le_tsum s
      (fun n _ ↦ Real.rpow_nonneg (approxNumber_nonneg (T m) n) p)).trans hm
  have hsum : Summable fun n ↦ approxNumber K n ^ p :=
    summable_of_sum_le
      (fun n ↦ Real.rpow_nonneg (approxNumber_nonneg K n) p) hfinite
  have henergy : (∑' n, approxNumber K n ^ p) ≤ r :=
    Real.tsum_le_of_sum_le
      (fun n ↦ Real.rpow_nonneg (approxNumber_nonneg K n) p) hfinite
  refine ⟨hsum, ?_⟩
  rw [schattenNorm_rpow_eq_tsum hp]
  exact henergy

/-- A finite-rank operator's Schatten `q` energy interpolates between operator and trace norms. -/
theorem schattenEnergy_le_norm_rpow_sub_one_mul_traceNorm_of_hasRankLE
    {q : ℝ} (hq : 1 ≤ q) {T : H →L[ℂ] H} {N : ℕ}
    (hT : HasRankLE T N) :
    schattenNorm q T ^ q ≤ ‖T‖ ^ (q - 1) * traceNorm H T := by
  have hq0 : 0 < q := zero_lt_one.trans_le hq
  have hmemq : MemSchattenClass q T := memSchattenClass_of_hasRankLE hq0 hT
  have hmemone : MemSchattenClass 1 T := memSchattenClass_of_hasRankLE one_pos hT
  have hsumone : Summable fun n ↦ approxNumber T n :=
    hmemone.congr fun n => Real.rpow_one (approxNumber T n)
  have hterm : ∀ n : ℕ,
      approxNumber T n ^ q ≤ ‖T‖ ^ (q - 1) * approxNumber T n := by
    intro n
    have ha : 0 ≤ approxNumber T n := approxNumber_nonneg T n
    by_cases hazero : approxNumber T n = 0
    · simp [hazero, Real.zero_rpow hq0.ne']
    have hapos : 0 < approxNumber T n := lt_of_le_of_ne ha (Ne.symm hazero)
    calc
      approxNumber T n ^ q = approxNumber T n ^ ((q - 1) + 1) := by ring_nf
      _ = approxNumber T n ^ (q - 1) * approxNumber T n ^ (1 : ℝ) :=
        Real.rpow_add hapos _ _
      _ = approxNumber T n ^ (q - 1) * approxNumber T n := by
        rw [Real.rpow_one]
      _ ≤ ‖T‖ ^ (q - 1) * approxNumber T n := by
        exact mul_le_mul_of_nonneg_right
          (Real.rpow_le_rpow ha (approxNumber_le_norm T n) (sub_nonneg.mpr hq)) ha
  rw [schattenNorm_rpow_eq_tsum hq0, traceNorm]
  calc
    (∑' n, approxNumber T n ^ q) ≤
        ∑' n, ‖T‖ ^ (q - 1) * approxNumber T n :=
      hmemq.tsum_le_tsum hterm (hsumone.mul_left (‖T‖ ^ (q - 1)))
    _ = ‖T‖ ^ (q - 1) * ∑' n, approxNumber T n := by
      rw [tsum_mul_left]

/-- Finite sums of rank-one terms satisfy the interpolation bound with projective mass. -/
theorem schattenEnergy_finsetSum_le_norm_rpow_sub_one_mul_sum_norm_of_rankOne
    [CompleteSpace H] {q : ℝ} (hq : 1 ≤ q) {ι : Type*}
    (A : ι → H →L[ℂ] H) (hA : ∀ i, HasRankLE (A i) 1) (s : Finset ι) :
    schattenNorm q (∑ i ∈ s, A i) ^ q ≤
      ‖∑ i ∈ s, A i‖ ^ (q - 1) * ∑ i ∈ s, ‖A i‖ := by
  classical
  let T : H →L[ℂ] H := ∑ i ∈ s, A i
  have hRank : HasRankLE T s.card :=
    RHTower.hasRankLE_sum_finset_of_rankOne A hA s
  calc
    schattenNorm q T ^ q ≤ ‖T‖ ^ (q - 1) * traceNorm H T :=
      schattenEnergy_le_norm_rpow_sub_one_mul_traceNorm_of_hasRankLE hq hRank
    _ ≤ ‖T‖ ^ (q - 1) * ∑ i ∈ s, ‖A i‖ := by
      gcongr
      exact RHTower.traceNorm_sum_le_sum_norm_of_rankOneTerms A hA s

end

end GaloisForLFunctions.HTGeometry
