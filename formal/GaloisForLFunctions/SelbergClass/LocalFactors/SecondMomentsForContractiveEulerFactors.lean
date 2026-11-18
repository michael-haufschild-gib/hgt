import GaloisForLFunctions.RHTower.AdamsOperations
import GaloisForLFunctions.RHTower.VonMangoldtLogSummatory
import GaloisForLFunctions.RHTower.VonMangoldtSquarePowerMoments
import Mathlib.Data.Nat.Factorization.PrimePow

/-!
# Sharp second-moment envelope for contractive Euler factors

For arbitrary local parameters in the closed unit disk, of fixed rank d,
the squared logarithmic coefficients have total mass at most 7d² N log N.
The all-one parameter system simultaneously maximizes every nonnegative
weighted second moment. The prime number theorem gives its first weighted
moment asymptotic with constant d²/2.
-/

noncomputable section
open Finset Filter Topology
open ArithmeticFunction (vonMangoldt)
namespace GaloisForLFunctions.SelbergClass.ContractiveMoments

abbrev Disk := {z : ℂ // ‖z‖ ≤ 1}
abbrev Parameters (d : ℕ) := ℕ → Fin d → Disk

/-- Logarithmic coefficient of the Euler family, extended by zero away from prime powers. -/
def coefficient {d : ℕ} (α : Parameters d) (n : ℕ) : ℂ :=
  (vonMangoldt n : ℂ) * adamsPowerSum (fun i => (α n.minFac i).val) (n.factorization n.minFac)

theorem at_prime_power {d : ℕ} (α : Parameters d) (p k : ℕ) (hp : p.Prime) (hk : k≠0) :
    coefficient α (p^k) = (Real.log p : ℂ)*adamsPowerSum (fun i => (α p i).val) k := by
  rw [coefficient,ArithmeticFunction.vonMangoldt_apply_pow hk,ArithmeticFunction.vonMangoldt_apply_prime hp,
    hp.pow_minFac hk,hp.factorization_pow,Finsupp.single_eq_same]

private theorem uniform_trace {d : ℕ} (α : Fin d → Disk) (k : ℕ) :
    ‖adamsPowerSum (fun i => (α i).val) k‖ ≤ d := by
  calc
    _ ≤ ∑ i, ‖(α i).val^k‖ := norm_sum_le _ _
    _ ≤ ∑ _i : Fin d, (1:ℝ) := sum_le_sum fun i _ => by
      rw [norm_pow]
      exact pow_le_one₀ (norm_nonneg _) (α i).property
    _ = _ := by simp

/-- The same family realizes the maximum for every weight and cutoff. -/
def aligned (d : ℕ) : Parameters d := fun _ _ => ⟨1,by simp⟩

private theorem aligned_norm (d n : ℕ) :
    ‖coefficient (aligned d) n‖ = (d:ℝ)*vonMangoldt n := by
  simp only [coefficient,aligned,adamsPowerSum,one_pow,sum_const,card_univ,Fintype.card_fin,
    nsmul_eq_mul,mul_one,norm_mul,Complex.norm_real,Real.norm_eq_abs,
    abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg,Complex.norm_natCast]
  ring

/-- Exact maximum over all local parameter systems for any nonnegative test weight. -/
theorem second_moment_maximum (d : ℕ) (S : Finset ℕ) (w : ℕ → NNReal) :
    IsGreatest (Set.range (fun α : Parameters d => ∑ n ∈ S, (w n:ℝ)*‖coefficient α n‖^2))
      ((d:ℝ)^2*∑ n ∈ S, (w n:ℝ)*vonMangoldt n^2) := by
  constructor
  · refine ⟨aligned d,?_⟩
    rw [mul_sum]
    apply sum_congr rfl
    intro n _
    rw [aligned_norm]
    ring
  · rintro _ ⟨α,rfl⟩
    rw [mul_sum]
    apply sum_le_sum
    intro n _
    have hl := (ArithmeticFunction.vonMangoldt_nonneg (n:=n))
    have h : ‖coefficient α n‖ ≤ vonMangoldt n*d := by
      rw [coefficient,norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hl]
      exact mul_le_mul_of_nonneg_left (uniform_trace _ _) hl
    calc
      _ ≤ (w n:ℝ)*(vonMangoldt n*d)^2 :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) h 2) (w n).property
      _ = _ := by ring

/-- A uniform version of the X log X estimate for every rank and every
contractive local family, with an absolute numerical constant. -/
theorem logarithmic_second_moment (d N : ℕ) (α : Parameters d) :
    ∑ n ∈ Icc 1 N, ‖coefficient α n‖^2 ≤ 7*(d:ℝ)^2*N*Real.log N := by
  have hb := (second_moment_maximum d (Icc 1 N) (fun _ => 1)).2 ⟨α,rfl⟩
  simp only [NNReal.coe_one,one_mul] at hb
  refine hb.trans ?_
  have hs : (∑ n ∈ Icc 1 N, vonMangoldt n^2) ≤ RHTower.chebyshevPsi N*Real.log N := by
    refine le_trans (sum_le_sum fun n _ => ?_) (RHTower.sum_vonMangoldt_mul_log_le N)
    simpa only [mul_comm (Real.log n)] using RHTower.vonMangoldt_sq_le_log_mul n
  have hlog : 0 ≤ Real.log N := by
    rcases Nat.eq_zero_or_pos N with rfl | h
    · simp
    · exact Real.log_nonneg (by exact_mod_cast Nat.succ_le_of_lt h)
  have h := mul_le_mul_of_nonneg_left (hs.trans
    (mul_le_mul_of_nonneg_right (RHTower.chebyshevPsi_le_seven N) hlog)) (sq_nonneg (d:ℝ))
  linarith only [h]

/-- The all-one extremizer has first weighted moment asymptotic
d² X² log(X)/2, including the empty local factor in rank zero. -/
theorem extremal_first_moment (d : ℕ) :
    Tendsto (fun X : ℝ => (∑ n ∈ Icc 0 ⌊X⌋₊, ‖coefficient (aligned d) n‖^2*n)/
      (X^2*Real.log X)) atTop (𝓝 ((d:ℝ)^2/2)) := by
  have h := RHTower.tendsto_sum_vonMangoldt_sq_mul_div.const_mul ((d:ℝ)^2)
  rw [show (d:ℝ)^2*(1/2)=(d:ℝ)^2/2 by ring] at h
  apply h.congr
  intro X
  simp only [aligned_norm,mul_pow,mul_div_assoc',mul_sum,mul_assoc]

end GaloisForLFunctions.SelbergClass.ContractiveMoments

#print axioms GaloisForLFunctions.SelbergClass.ContractiveMoments.at_prime_power
#print axioms GaloisForLFunctions.SelbergClass.ContractiveMoments.second_moment_maximum
#print axioms GaloisForLFunctions.SelbergClass.ContractiveMoments.logarithmic_second_moment
#print axioms GaloisForLFunctions.SelbergClass.ContractiveMoments.extremal_first_moment
