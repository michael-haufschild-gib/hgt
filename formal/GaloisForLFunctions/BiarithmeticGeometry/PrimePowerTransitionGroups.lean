import GaloisForLFunctions.BiarithmeticGeometry.ArithmeticEulerCharacteristic
import Mathlib.Data.ZMod.Basic
import Mathlib.GroupTheory.Index
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Prime-power transition groups at the integer horizon

Reduction between successive divisor-incidence periods is surjective. Its cyclic kernel
has order p exactly at a power of p and is trivial elsewhere. The fixed-horizon torsion
charge is itself a reduction kernel, giving an exact finite-group meaning to the box formula.
-/

noncomputable section
open Finset
open scoped ArithmeticFunction NNReal
namespace GaloisForLFunctions.BiarithmeticGeometry

/-- The divisor-incidence period grows by divisibility with the horizon. -/
theorem horizonPeriod_dvd_of_le {M N : ℕ} (h : M ≤ N) :
    Nat.lcmUpto M ∣ Nat.lcmUpto N := by
  apply Finset.lcm_dvd_iff.mpr
  intro d hd
  exact Finset.dvd_lcm (f := id) (Icc_subset_Icc le_rfl h hd)

/-- The exact integral increase of the divisor-incidence period. -/
def horizonPeriodJump (N : ℕ) : ℕ := Nat.lcmUpto (N + 1) / Nat.lcmUpto N

theorem horizonPeriodJump_pos (N : ℕ) : 0 < horizonPeriodJump N :=
  Nat.div_pos (Nat.le_of_dvd (Nat.lcmUpto_pos _) (horizonPeriod_dvd_of_le (Nat.le_succ N)))
    (Nat.lcmUpto_pos N)

theorem horizonPeriodJump_mul (N : ℕ) :
    horizonPeriodJump N * Nat.lcmUpto N = Nat.lcmUpto (N + 1) :=
  Nat.div_mul_cancel (horizonPeriod_dvd_of_le (Nat.le_succ N))

/-- The logarithm of the finite transition order is exactly the Mangoldt atom. -/
theorem log_horizonPeriodJump (N : ℕ) :
    Real.log (horizonPeriodJump N : ℝ) = Λ (N + 1) := by
  rw [horizonPeriodJump, Nat.cast_div
    (horizonPeriod_dvd_of_le (Nat.le_succ N)) (by exact_mod_cast Nat.lcmUpto_ne_zero N),
    Real.log_div (by exact_mod_cast Nat.lcmUpto_ne_zero (N + 1))
      (by exact_mod_cast Nat.lcmUpto_ne_zero N),
    ← Chebyshev.psi_eq_log_lcmUpto, ← Chebyshev.psi_eq_log_lcmUpto]
  simp only [Chebyshev.psi, Nat.floor_natCast]
  rw [Finset.sum_Ioc_succ_top (Nat.zero_le N)]
  ring

/-- No transition group appears away from prime powers. -/
theorem horizonPeriodJump_eq_one_iff (N : ℕ) :
    horizonPeriodJump N = 1 ↔ ¬ IsPrimePow (N + 1) := by
  rw [← ArithmeticFunction.vonMangoldt_eq_zero_iff, ← log_horizonPeriodJump]
  have hp : (0 : ℝ) < horizonPeriodJump N := by exact_mod_cast horizonPeriodJump_pos N
  constructor
  · intro h; rw [h, Nat.cast_one, Real.log_one]
  · intro h
    have heq : (horizonPeriodJump N : ℝ) = 1 :=
      Real.log_injOn_pos hp (by norm_num) (h.trans Real.log_one.symm)
    exact_mod_cast heq

/-- At a prime power the new transition order is the underlying prime. -/
theorem horizonPeriodJump_prime_pow (p : ℕ) (hp : p.Prime) (r : ℕ) :
    horizonPeriodJump (p ^ (r + 1) - 1) = p := by
  have hn : p ^ (r + 1) - 1 + 1 = p ^ (r + 1) := Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr (pow_ne_zero _ hp.ne_zero))
  have hlog := log_horizonPeriodJump (p ^ (r + 1) - 1)
  rw [hn, ArithmeticFunction.vonMangoldt_apply_pow (by omega),
    ArithmeticFunction.vonMangoldt_apply_prime hp] at hlog
  have hj : (0 : ℝ) < horizonPeriodJump (p ^ (r + 1) - 1) := by
    exact_mod_cast horizonPeriodJump_pos (p ^ (r + 1) - 1)
  exact_mod_cast Real.log_injOn_pos hj (show (0 : ℝ) < (p : ℝ) by exact_mod_cast hp.pos) hlog

/-- A canonical finite cyclic group at each integer horizon. -/
abbrev HorizonPeriodGroup (N : ℕ) := ZMod (Nat.lcmUpto N)

instance (N : ℕ) : NeZero (Nat.lcmUpto N) := ⟨Nat.lcmUpto_ne_zero N⟩

/-- Restriction of period classes to an earlier horizon. -/
def horizonPeriodRestriction {M N : ℕ} (h : M ≤ N) :
    HorizonPeriodGroup N →+* HorizonPeriodGroup M :=
  ZMod.castHom (horizonPeriod_dvd_of_le h) _

theorem horizonPeriodRestriction_surjective {M N : ℕ} (h : M ≤ N) :
    Function.Surjective (horizonPeriodRestriction h) := ZMod.castHom_surjective _

theorem horizonPeriodRestriction_comp {L M N : ℕ} (hLM : L ≤ M) (hMN : M ≤ N) :
    (horizonPeriodRestriction hLM).comp (horizonPeriodRestriction hMN) =
      horizonPeriodRestriction (hLM.trans hMN) := ZMod.castHom_comp _ _

/-- The transition group is the actual kernel of reduction to the preceding period. -/
abbrev HorizonTransition (N : ℕ) :=
  (horizonPeriodRestriction (Nat.le_succ N)).toAddMonoidHom.ker

private theorem card_reduction_kernel {m n : ℕ} (h : m ∣ n) :
    Nat.card ((ZMod.castHom h (ZMod m)).toAddMonoidHom.ker) * m = n := by
  let f := (ZMod.castHom h (ZMod m)).toAddMonoidHom
  have hs : Function.Surjective f := ZMod.castHom_surjective h
  have hcard := AddSubgroup.card_mul_index f.ker
  rw [AddSubgroup.index_ker, AddMonoidHom.range_eq_top.mpr hs,
    Nat.card_congr (AddSubgroup.topEquiv : (⊤ : AddSubgroup (ZMod m)) ≃+ ZMod m).toEquiv,
    Nat.card_zmod, Nat.card_zmod] at hcard
  exact hcard

/-- Every prime-power node adds precisely its prime-sized cyclic kernel. -/
theorem card_horizonTransition (N : ℕ) : Nat.card (HorizonTransition N) = horizonPeriodJump N := by
  have h := card_reduction_kernel (horizonPeriod_dvd_of_le (Nat.le_succ N))
  exact Nat.eq_of_mul_eq_mul_right (Nat.lcmUpto_pos N) (h.trans (horizonPeriodJump_mul N).symm)

/-- The transition kernel is cyclic, with its order determined by the Mangoldt jump. -/
def horizonTransitionEquiv (N : ℕ) :
    ZMod (horizonPeriodJump N) ≃+ HorizonTransition N := by
  rw [← card_horizonTransition]
  exact zmodAddCyclicAddEquiv inferInstance

theorem card_horizonTransition_prime_pow (p : ℕ) (hp : p.Prime) (r : ℕ) :
    Nat.card (HorizonTransition (p ^ (r + 1) - 1)) = p := by
  rw [card_horizonTransition, horizonPeriodJump_prime_pow p hp]

/-- The canonical map from a period class to its position within one horizon. -/
def horizonTorsionReduction (N : ℕ) : HorizonPeriodGroup (N + 1) →+* ZMod (N + 1) :=
  ZMod.castHom (horizon_dvd_period N) _

/-- The torsion charge is the kernel of reduction from period to horizon. -/
abbrev HorizonTorsionKernel (N : ℕ) := (horizonTorsionReduction N).toAddMonoidHom.ker

theorem horizonTorsionReduction_surjective (N : ℕ) :
    Function.Surjective (horizonTorsionReduction N) := ZMod.castHom_surjective _

theorem card_horizonTorsionKernel (N : ℕ) :
    Nat.card (HorizonTorsionKernel N) = horizonTorsionOrder N := by
  have h := card_reduction_kernel (horizon_dvd_period N)
  exact Nat.eq_of_mul_eq_mul_right (Nat.succ_pos N)
    (h.trans (horizonTorsionOrder_mul_horizon N).symm)

/-- The cyclic torsion group and the canonical reduction kernel are isomorphic. -/
def horizonTorsionKernelEquiv (N : ℕ) : HorizonTorsion N ≃+ HorizonTorsionKernel N := by
  change ZMod (horizonTorsionOrder N) ≃+ HorizonTorsionKernel N
  rw [← card_horizonTorsionKernel]
  exact zmodAddCyclicAddEquiv inferInstance

/-- The canonical kernel inclusion and reduction form an exact sequence. -/
theorem horizonTorsionKernel_exact (N : ℕ) :
    Function.Injective (fun x : HorizonTorsionKernel N => (x : HorizonPeriodGroup (N + 1))) ∧
    Function.Surjective (horizonTorsionReduction N) ∧
    ∀ x : HorizonPeriodGroup (N + 1), horizonTorsionReduction N x = 0 ↔
      ∃ y : HorizonTorsionKernel N, (y : HorizonPeriodGroup (N + 1)) = x := by
  refine ⟨Subtype.val_injective, horizonTorsionReduction_surjective N, ?_⟩
  intro x
  constructor
  · intro hx
    exact ⟨⟨x, hx⟩, rfl⟩
  · rintro ⟨y, rfl⟩
    exact y.property

/-- The integer-horizon box defect is degree minus the log order of a canonical kernel. -/
theorem boxDefect_eq_degree_sub_log_kernel (N : ℕ) :
    ArithmeticIncidencePositivity.chebyshevTwoPoleDefect (Real.log (N + 1 : ℕ)) =
      (N : ℝ) - Real.log (Nat.card (HorizonTorsionKernel N) : ℝ) := by
  rw [card_horizonTorsionKernel, boxDefect_eq_degree_sub_log_torsion]

/-- The prime-power divisor is exactly the log cardinality of the transition kernels. -/
theorem log_card_horizonTransition (N : ℕ) :
    Real.log (Nat.card (HorizonTransition N) : ℝ) = Λ (N + 1) := by
  rw [card_horizonTransition, log_horizonPeriodJump]

/-- Every aperture retains the canonical torsion kernel and its exact continuous remainder. -/
theorem boxDefect_all_apertures_kernel (s : ℝ≥0) :
    ArithmeticIncidencePositivity.chebyshevTwoPoleDefect (s : ℝ) =
      (arithmeticHorizon s : ℝ) -
        Real.log (Nat.card (HorizonTorsionKernel (arithmeticHorizon s)) : ℝ) +
        (Real.exp (s : ℝ) - (arithmeticHorizon s + 1 : ℕ)) +
          ((s : ℝ) - Real.log (arithmeticHorizon s + 1 : ℕ)) := by
  rw [card_horizonTorsionKernel, boxDefect_all_apertures]

end GaloisForLFunctions.BiarithmeticGeometry
