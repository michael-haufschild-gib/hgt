import GaloisForLFunctions.ArithmeticContinuationAndCriticalEnergy.IntegralMomentsOfTheEndpointDistribution
import GaloisForLFunctions.ExceptionalLayerTheory.SquareConductors.FirstPassageOfTheEighthPowerGcdShortfall
import GaloisForLFunctions.Hurwitz.RealOrdersOfPerturbedPowerTails

/-!
# Power moments of the eighth-grid endpoint discrepancy

Every positive power of the distribution lag has a finite positive
integral over the full cumulative axis. The missing integral beyond the
Nth endpoint is asymptotic to 2^(−p−1)/(p(p+1) N^p). Its coefficient
depends only on the leading harmonic jump, whereas the total integral
records all early arithmetic jumps.
-/

noncomputable section
open Filter Finset
open scoped Topology
open GaloisForLFunctions.CumulativeQuadrature GaloisForLFunctions.HurwitzPowerTails
namespace GaloisForLFunctions.ExceptionalLayerTheory.FactorialInterval
private abbrev D := powerGridGcdDeficit 8
private abbrev d (n : ℕ) := D (n+1)-D n
private abbrev j (p : ℝ) (n : ℕ) := (d n)^(p+1)

/-- Integrated p-th power of the distribution lag through the Nth endpoint. -/
def eighthLagMoment (p : ℝ) (N : ℕ) : ℝ :=
  ∫ y in D 0..D N, (endpointLag D N y)^p

private theorem moment_eq {p : ℝ} (hp : 0<p) (N : ℕ) :
    eighthLagMoment p N = (∑ n ∈ range N, j p n)/(p+1) :=
  integral_endpoint_lag_rpow (monotone_gcd_deficit _) N hp

private theorem jump_moment_tail {p : ℝ} (hp : 0<p) :
    Summable (j p) ∧ Tendsto (fun N : ℕ => (N:ℝ)^p*∑' k : ℕ, j p (k+N))
      atTop (𝓝 ((1/2:ℝ)^(p+1)/p)) := by
  let a := fun n : ℕ => ((n:ℝ)*d n)^(p+1)
  have h := eighth_gcd_jump_law
  have ht := (tendsto_natCast_atTop_atTop (R:=ℝ)).comp (tendsto_add_atTop_nat 1)
  have hsmall : Tendsto d atTop (𝓝 0) := (h.div_atTop ht).congr fun n => by
    change ((n+1:ℕ):ℝ)*d n/((n+1:ℕ):ℝ)=d n
    field_simp
  have hcoeff : Tendsto (fun n : ℕ => (n:ℝ)*d n) atTop (𝓝 (1/2)) := by
    have hh := h.sub hsmall
    rw [sub_zero] at hh
    exact hh.congr fun n => by change ((n+1:ℕ):ℝ)*d n-d n=_; push_cast; ring
  have hl : Tendsto a atTop (𝓝 ((1/2:ℝ)^(p+1))) :=
    hcoeff.rpow_const (Or.inr (by linarith only [hp]))
  obtain ⟨sm,lim⟩ := perturbed_power_tail hp hl
  have row (n : ℕ) (hn : 0<n) : a n*(n:ℝ)^(-(p+1)) = j p n := by
    have hr := (Nat.cast_pos (α:=ℝ)).mpr hn
    rw [show a n=((n:ℝ)*d n)^(p+1) from rfl,
      Real.mul_rpow hr.le (gcd_deficit_increment_bounds 8 n).1,
      mul_right_comm,←Real.rpow_add hr,add_neg_cancel,Real.rpow_zero,one_mul]
  refine ⟨Summable.congr_cofinite sm ?_,lim.congr' ?_⟩
  · rw [Nat.cofinite_eq_atTop]
    exact (eventually_gt_atTop 0).mono row
  · filter_upwards [eventually_gt_atTop (0:ℕ)] with N hn
    exact congrArg _ (tsum_congr fun k => row _ (by omega : 0<k+N))

/-- Positive finite limit, with the exact first power correction for
each real moment order. -/
theorem eighth_lag_moment_with_tail {p : ℝ} (hp : 0<p) :
    ∃ A : ℝ, 0<A ∧ Tendsto (eighthLagMoment p) atTop (𝓝 A) ∧
      Tendsto (fun N : ℕ => (N:ℝ)^p*(A-eighthLagMoment p N))
        atTop (𝓝 ((1/2:ℝ)^(p+1)/(p*(p+1)))) := by
  obtain ⟨sm,tail⟩ := jump_moment_tail hp
  have hden : 0 < p+1 := by linarith only [hp]
  refine ⟨(∑' n,j p n)/(p+1),div_pos ?_ hden,?_,?_⟩
  · have first : d 0 = Real.log 2 := by
      simp [d,D,powerGridGcdDeficit,octaveGcdProduct,
        max_eq_left (Real.log_nonneg (by norm_num : (1:ℝ) ≤ 2))]
    have hj : 0 < j p 0 := by
      dsimp only [j]; rw [first]; exact Real.rpow_pos_of_pos (Real.log_pos (by norm_num)) _
    exact hj.trans_le (sm.le_tsum _ (fun n _ => Real.rpow_nonneg (gcd_deficit_increment_bounds 8 n).1 _))
  · exact (sm.hasSum.tendsto_sum_nat.div_const (p+1)).congr fun N => (moment_eq hp N).symm
  · have ht := tail.div_const (p+1)
    rw [div_div] at ht
    apply ht.congr
    intro N
    rw [moment_eq hp,←sub_div,←sm.sum_add_tsum_nat_add N,add_sub_cancel_left]
    ring

#print axioms eighth_lag_moment_with_tail
end GaloisForLFunctions.ExceptionalLayerTheory.FactorialInterval
