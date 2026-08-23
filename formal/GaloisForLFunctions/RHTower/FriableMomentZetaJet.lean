import GaloisForLFunctions.RHTower.FriableMomentEulerFlux
import GaloisForLFunctions.HTGeometry.LogDerivBellTransfer

/-!
# The friable zeta jet lands in the period filtration

The finite Euler product `ζ_S(s) = ∏_{p ∈ S}(1 - p^{-s})^{-1}` is analytic and nonvanishing off its
polar set, so the Bell transfer expresses `ζ_S^{(m)}/ζ_S` as a rational polynomial in the jet of its
logarithmic derivative.  That jet is minus the Euler flux jet, which at a positive integer argument
is a rational combination of powers of the prime logarithms.
-/

open GaloisForLFunctions

namespace RHTower

noncomputable section

theorem eulerProductL_ne_zero {k : ℕ} {p : Fin k → ℕ} {a : Fin k → ℂ} {s : ℂ}
    (h : ∀ i, a i * (p i : ℂ) ^ (-s) ≠ 1) : eulerProductL p a s ≠ 0 := by
  show (∏ i, (1 - a i * (p i : ℂ) ^ (-s))⁻¹) ≠ 0
  refine Finset.prod_ne_zero_iff.mpr fun i _ => ?_
  exact inv_ne_zero (sub_ne_zero.mpr (Ne.symm (h i)))

theorem differentiableAt_eulerProductL {k : ℕ} {p : Fin k → ℕ} (hp : ∀ i, 0 < p i)
    (a : Fin k → ℂ) {s : ℂ} (h : ∀ i, a i * (p i : ℂ) ^ (-s) ≠ 1) :
    DifferentiableAt ℂ (eulerProductL p a) s := by
  show DifferentiableAt ℂ (fun s : ℂ => ∏ i, (1 - a i * (p i : ℂ) ^ (-s))⁻¹) s
  refine DifferentiableAt.fun_finsetProd fun i _ => ?_
  exact ((hasDerivAt_one_sub_param (hp i) (a i) s).differentiableAt).inv
    (sub_ne_zero.mpr (Ne.symm (h i)))

theorem analyticAt_eulerProductL {k : ℕ} {p : Fin k → ℕ} (hp : ∀ i, 0 < p i)
    (a : Fin k → ℂ) {s : ℂ} (h : ∀ i, a i * (p i : ℂ) ^ (-s) ≠ 1) :
    AnalyticAt ℂ (eulerProductL p a) s := by
  have hopen := isOpen_eulerFluxDomain p hp a
  have hdiff : DifferentiableOn ℂ (eulerProductL p a) {s : ℂ | ∀ i, a i * (p i : ℂ) ^ (-s) ≠ 1} :=
    fun z hz => (differentiableAt_eulerProductL hp a hz).differentiableWithinAt
  exact hdiff.analyticAt (hopen.mem_nhds h)

/-- The logarithmic-derivative jet of the finite Euler product is minus the Euler flux jet. -/
theorem iteratedDeriv_logDeriv_eulerProductL {k : ℕ} {p : Fin k → ℕ} (hp : ∀ i, 0 < p i)
    (a : Fin k → ℂ) (m : ℕ) {s : ℂ} (h : ∀ i, a i * (p i : ℂ) ^ (-s) ≠ 1) :
    iteratedDeriv m (fun w => deriv (eulerProductL p a) w / eulerProductL p a w) s
      = -eulerFluxJet p a m s := by
  have hopen := isOpen_eulerFluxDomain p hp a
  have hev : (fun w => deriv (eulerProductL p a) w / eulerProductL p a w)
      =ᶠ[nhds s] fun w => -eulerFlux p a w := by
    filter_upwards [hopen.mem_nhds h] with z hz
    rw [eulerFlux_eq_neg_logDeriv hp a hz, neg_neg, logDeriv_apply]
  rw [hev.iteratedDeriv_eq]
  show iteratedDeriv m (-(eulerFlux p a)) s = -eulerFluxJet p a m s
  rw [iteratedDeriv_neg, iteratedDeriv_eulerFlux hp a m h]

theorem one_mul_cpow_ne_one {p : ℕ} (hp : 2 ≤ p) (j : ℕ) :
    (1 : ℂ) * (p : ℂ) ^ (-((j : ℂ) + 1)) ≠ 1 := by
  have hp0 : 0 < p := by omega
  rw [one_mul, cpow_neg_natSucc hp0 j]
  intro hcon
  have hq : (1 / (p : ℚ) ^ (j + 1) : ℚ) = 1 := by exact_mod_cast hcon
  have h2 : (2 : ℚ) ≤ (p : ℚ) := by exact_mod_cast hp
  have hpow : (2 : ℚ) ≤ (p : ℚ) ^ (j + 1) := by
    calc (2 : ℚ) = 2 ^ 1 := by norm_num
      _ ≤ (p : ℚ) ^ (j + 1) := by
          refine (pow_le_pow_left₀ (by norm_num) h2 1).trans ?_
          exact pow_le_pow_right₀ (by linarith) (by omega)
  have hpos : (0 : ℚ) < (p : ℚ) ^ (j + 1) := by linarith
  rw [div_eq_one_iff_eq (ne_of_gt hpos)] at hq
  linarith

/-- **The friable zeta jet at a positive integer lands in the weight-`m` period layer.** -/
theorem friableZetaJet_mem_periodFilt {k : ℕ} {S : Finset ℕ} {p : Fin k → ℕ}
    (hpS : ∀ i, p i ∈ S) (hp2 : ∀ i, 2 ≤ p i) (m j : ℕ) :
    iteratedDeriv m (eulerProductL p 1) ((j : ℂ) + 1) / eulerProductL p 1 ((j : ℂ) + 1)
      ∈ periodFilt S m := by
  have hp : ∀ i, 0 < p i := fun i => by have := hp2 i; omega
  have hdom : ∀ i, (1 : Fin k → ℂ) i * (p i : ℂ) ^ (-((j : ℂ) + 1)) ≠ 1 := by
    intro i
    rw [Pi.one_apply]
    exact one_mul_cpow_ne_one (hp2 i) j
  have hopen := isOpen_eulerFluxDomain p hp (1 : Fin k → ℂ)
  have hfan : ∀ z ∈ {s : ℂ | ∀ i, (1 : Fin k → ℂ) i * (p i : ℂ) ^ (-s) ≠ 1},
      AnalyticAt ℂ (eulerProductL p 1) z := fun z hz => analyticAt_eulerProductL hp 1 hz
  have hfne : ∀ z ∈ {s : ℂ | ∀ i, (1 : Fin k → ℂ) i * (p i : ℂ) ^ (-s) ≠ 1},
      eulerProductL p 1 z ≠ 0 := fun z hz => eulerProductL_ne_zero hz
  have hbell := iteratedDeriv_eq_bellCore_generic hopen hfan hfne m hdom
  have hzne : eulerProductL p 1 ((j : ℂ) + 1) ≠ 0 := eulerProductL_ne_zero hdom
  rw [hbell, mul_comm, mul_div_assoc, div_self hzne, mul_one, ← map_bellCoreQ m]
  refine eval_mem_periodFilt (isWeightedHomogeneous_bellCoreQ m) fun i => ?_
  rw [iteratedDeriv_logDeriv_eulerProductL hp 1 (i : ℕ) hdom]
  refine Submodule.neg_mem _ ?_
  rw [eulerFluxJet]
  refine Submodule.sum_mem _ fun t _ => ?_
  have hloc := localFluxJet_one_natSucc_mem_periodFilt (hpS t) (hp2 t) (i : ℕ) j
  simpa using hloc

end

end RHTower
