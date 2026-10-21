import GaloisForLFunctions.TransHorizonIncidenceMechanics.AVanishingFiniteLocalFactorPaysAWeightPretendingToOne

/-!
# Finite perturbations of every positive weight pretending to one are decided at the pole

Let `b ≥ 0` be multiplicative with `b(p) = 1` at every prime and `|b| ≤ B` (the squarefree indicator,
the constant one, the odd squarefree indicator, `1_{(·,q)=1}μ²`, …). For every kernel `k` on `[1, J]`
and `0 < ε ≤ 1/2`:

**the receiver of `k ⋆ (b d^{-ε})` is bounded if and only if `K(1 − ε) = Σ_j k(j) j^{-(1−ε)} = 0`.**

* Necessity: `b = 1` on the squarefree integers, so `b d^{-ε}` dominates the odd squarefree weight and
  carries its drift (density `4/π²` on late dyadic windows); the pole law of finite kernels applies.
* Sufficiency: `b = g ⋆ 1` with `g = b ⋆ μ` zero at every prime, hence `g d^{-ε}` critical Wiener; the
  convolutions commute, `k ⋆ (b d^{-ε}) = (g d^{-ε}) ⋆ (k ⋆ d^{-ε})`, and `k ⋆ d^{-ε}` is paid exactly on
  the hyperplane `K(1 − ε) = 0`.

So the paid hyperplane is universal: it depends neither on the base nor on its local factors — only
the value of the kernel at the pole enters, through the dilations `k ↦ jk`.
-/

open Finset Filter Topology
open scoped BigOperators

namespace GaloisForLFunctions.TransHorizonIncidenceMechanics

noncomputable section
set_option autoImplicit false

local notation "μR" => ((ArithmeticFunction.moebius : ArithmeticFunction ℤ) : ArithmeticFunction ℝ)

/-- A multiplicative function equal to one at the primes is one on the squarefree integers. -/
theorem eq_one_of_squarefree_of_primes_one {f : ArithmeticFunction ℝ} (hf : f.IsMultiplicative)
    (hfp : ∀ p : ℕ, p.Prime → f p = 1) {n : ℕ} (hn : Squarefree n) : f n = 1 := by
  induction n using Nat.recOnPosPrimePosCoprime with
  | prime_pow p k hp hk =>
    have hk1 : k = 1 := by
      by_contra h
      exact absurd hn (by rw [Nat.squarefree_pow_iff hp.ne_one (by omega)]; omega)
    rw [hk1, pow_one, hfp p hp]
  | zero => exact absurd hn not_squarefree_zero
  | one => exact hf.map_one
  | coprime a b ha hb hab iha ihb =>
    rw [hf.map_mul_of_coprime hab, iha (Squarefree.of_mul_left hn),
      ihb (Squarefree.of_mul_right hn), mul_one]

/-- **Finite perturbations of every positive weight pretending to one are decided at the pole.** -/
theorem receiverBounded_dirichletConv_primesOne_iff {b : ArithmeticFunction ℝ}
    (hb : b.IsMultiplicative) (hb0 : ∀ n, 0 ≤ b n) (hbp : ∀ p : ℕ, p.Prime → b p = 1) {B : ℝ}
    (hB : ∀ n, |b n| ≤ B) {ε : ℝ} (hε : 0 < ε) (hε2 : ε ≤ 1 / 2) {k : ℕ → ℝ} {J : ℕ}
    (hkJ : ∀ j, J < j → k j = 0) :
    ReceiverBounded (RHTower.dirichletConv k (dampedSignWeight ⇑b ε)) ↔ poleValue k J ε = 0 := by
  have hB0 : 0 ≤ B := (abs_nonneg _).trans (hB 1)
  constructor
  · intro hR
    by_contra hK
    have hD : 0 < RHTower.Sieve.squarefreeDensity := by
      rw [RHTower.Sieve.squarefreeDensity_eq]; positivity
    -- `b d^{-ε}` dominates the odd squarefree weight
    have hdom : ∀ d, oddSqfWeight ε d ≤ dampedSignWeight ⇑b ε d := fun d => by
      unfold oddSqfWeight dampedSignWeight
      refine mul_le_mul_of_nonneg_right ?_ (Real.rpow_nonneg (Nat.cast_nonneg d) _)
      rw [oddSqfAF_apply]
      split_ifs with h
      · rw [eq_one_of_squarefree_of_primes_one hb hbp h.2]
      · exact hb0 d
    have hdrift := (eventually_oddSqfWeight_drift hε).mono fun n hn => hn.trans
      (mul_le_mul_of_nonneg_left (sum_le_sum fun d _ =>
        div_le_div_of_nonneg_right (hdom d) (Nat.cast_nonneg d)) (Nat.cast_nonneg n))
    exact not_receiverBounded_dirichletConv_of_drift hε hε2 (q := dampedSignWeight ⇑b ε)
      (fun d => mul_nonneg (hb0 d) (Real.rpow_nonneg (Nat.cast_nonneg d) _))
      (K := B) (fun d => by
        show |b d * (d : ℝ) ^ (-ε)| ≤ B * (d : ℝ) ^ (-ε)
        rw [abs_mul, abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg d) _)]
        exact mul_le_mul_of_nonneg_right (hB d) (Real.rpow_nonneg (Nat.cast_nonneg d) _))
      (by positivity) hdrift hkJ hK hR
  · intro hK
    set g := b * μR
    have hg : g.IsMultiplicative := hb.mul ArithmeticFunction.isMultiplicative_moebius.intCast
    have hgp : ∀ p : ℕ, p.Prime → g p = 0 := fun p hp => by
      have := mul_moebius_apply_prime_pow b hp 0
      rwa [zero_add, pow_one, pow_zero, hb.map_one, hbp p hp, sub_self] at this
    have hW := criticalWiener_of_multiplicative hg hgp (B := 2 * B + 1) (by linarith)
      (fun p hp k hk => (abs_mul_moebius_apply_le hb hB hp k).trans
        (le_mul_of_one_le_right (by linarith) (by exact_mod_cast (by omega : 1 ≤ k)))) hε
    have hbg : b = g * ((ArithmeticFunction.zeta : ArithmeticFunction ℕ) : ArithmeticFunction ℝ) := by
      simp only [g]; rw [mul_assoc, ArithmeticFunction.coe_moebius_mul_coe_zeta, mul_one]
    have hbase : dampedSignWeight ⇑b ε =
        RHTower.dirichletConv (dampedSignWeight ⇑g ε) (dampedSignWeight unitSign ε) := by
      funext n
      rw [← dampedSignWeight_zeta hε.ne', ← dampedSignWeight_dirichletConv]
      conv_lhs => rw [hbg]
      simp only [dampedSignWeight, mul_apply_eq_dirichletConv]
    have hfun : RHTower.dirichletConv k (dampedSignWeight ⇑b ε) =
        RHTower.dirichletConv (dampedSignWeight ⇑g ε)
          (RHTower.dirichletConv k (dampedSignWeight unitSign ε)) := by
      funext n; rw [hbase, dirichletConv_left_comm]
    rw [hfun]
    have hinner := (receiverBounded_dirichletConv_unit_iff hε hε2 hkJ).mpr hK
    set L := ∑ j ∈ Icc 1 J, |undampedKernel k ε j|
    have hsign : ∀ d, |RHTower.dirichletConv (undampedKernel k ε) unitSign d| ≤ L := fun d => by
      unfold RHTower.dirichletConv
      refine (abs_sum_le_sum_abs _ _).trans ?_
      calc ∑ j ∈ d.divisors, |undampedKernel k ε j * unitSign (d / j)| ≤
            ∑ j ∈ d.divisors.filter (· ≤ J), |undampedKernel k ε j| := by
            rw [sum_filter]
            refine sum_le_sum fun j _ => ?_
            split_ifs with hj
            · rw [unitSign, mul_one]
            · rw [undampedKernel_support hkJ ε j (by omega), zero_mul, abs_zero]
        _ ≤ L := sum_le_sum_of_subset_of_nonneg (fun j hj => by
              obtain ⟨hjd, hjJ⟩ := mem_filter.mp hj
              exact mem_Icc.mpr ⟨Nat.pos_of_mem_divisors hjd, hjJ⟩) fun _ _ _ => abs_nonneg _
    have hs : Summable (fun d : ℕ =>
        |RHTower.dirichletConv k (dampedSignWeight unitSign ε) d / d|) := by
      rw [show RHTower.dirichletConv k (dampedSignWeight unitSign ε) =
          dampedSignWeight (RHTower.dirichletConv (undampedKernel k ε) unitSign) ε from
        funext (dirichletConv_damped_eq k unitSign ε)]
      refine ((Real.summable_nat_rpow.mpr (show -(1 + ε) < -1 by linarith)).mul_left L).of_nonneg_of_le
        (fun _ => abs_nonneg _) fun d => ?_
      rw [dampedSignWeight_div hε, abs_mul, abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg d) _),
        mul_comm]
      exact mul_le_mul_of_nonneg_right (hsign d) (Real.rpow_nonneg (Nat.cast_nonneg d) _)
    exact receiverBounded_dirichletConv hW hs hinner

end

end GaloisForLFunctions.TransHorizonIncidenceMechanics
