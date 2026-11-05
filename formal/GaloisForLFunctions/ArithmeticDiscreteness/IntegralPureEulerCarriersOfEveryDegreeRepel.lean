import GaloisForLFunctions.ArithmeticDiscreteness.DistinctRootsOfIntegerPolynomialsRepel
import GaloisForLFunctions.ArithmeticDiscreteness.EulerColumnsCollideOrRepelAtPolynomialScale
import GaloisForLFunctions.RHTower.FrobeniusTorsionLaw

/-!
# Integral pure Euler carriers of every degree repel at polynomial scale

The degree-two law of `IntegralPureEulerFactorsRepelAtPolynomialScale` holds in every degree. Let
each local factor be `F_i(p_i^{−s})` with `F_i ∈ ℤ[X]` monic and **pure**: every complex root has
modulus one (Ramanujan at `p_i` in the unitary normalisation).

* **Pure integral local roots are torsion** (`exists_pow_eq_one_of_pure`). A root of a monic
  integer polynomial whose roots all have modulus one is a root of unity: its conjugates are roots
  of the same polynomial, and Kronecker's theorem
  (`RHTower.exists_pow_eq_one_of_isIntegral_of_conjugates_norm_one`) applies. One exponent `N`
  serves all roots of all factors (`exists_common_order`).
* **Zeros lie on refined Euler columns** (`pureCarrier_zero_mem_column`). Every zero `s` of
  `∏_i F_i(p_i^{−s})` has `p_i^{−Ns} = 1` for some `i`, i.e. `N s` is a zero of
  `∏_i (1 − p_i^{−s})`.
* **Collide or repel at polynomial scale** (`pureCarrier_collide_or_repel`), from
  `eulerCarrier_collide_or_repel` at height `N T`.

So integrality plus purity of the local data turns every Euler carrier into a union of rational
refinements of Euler columns, and the transcendence of `⊕ ℤ log p` separates its zeros at
polynomial scale. With real pure data this fails (`real_pure_carrier_not_polynomial_repulsion`).
-/

open Polynomial Complex

noncomputable section

namespace GaloisForLFunctions.ArithmeticDiscreteness

/-- A monic integer polynomial is **pure** when all its complex roots have modulus one. -/
def IsPureLocal (F : ℤ[X]) : Prop := F.Monic ∧ ∀ z ∈ (toC F).roots, ‖z‖ = 1

/-- **Pure integral local roots are torsion.** -/
theorem exists_pow_eq_one_of_pure {F : ℤ[X]} (hF : IsPureLocal F) {w : ℂ}
    (hw : w ∈ (toC F).roots) : ∃ n : ℕ, 0 < n ∧ w ^ n = 1 := by
  have hint := isIntegral_of_mem_roots hF.1 hw
  refine RHTower.exists_pow_eq_one_of_isIntegral_of_conjugates_norm_one hint fun z hz => ?_
  -- a conjugate of `w` is a root of `F`
  have hdvd : minpoly ℚ w ∣ F.map (algebraMap ℤ ℚ) := by
    refine minpoly.dvd ℚ w ?_
    rw [aeval_map_algebraMap]
    exact (mem_roots_toC_iff hF.1).mp hw
  have hz0 : aeval z (minpoly ℚ w) = 0 := (mem_rootSet.mp hz).2
  have hzF : aeval z F = 0 := by
    obtain ⟨g, hg⟩ := hdvd
    have := congrArg (aeval z) hg
    rw [map_mul, hz0, zero_mul, aeval_map_algebraMap] at this
    exact this
  exact hF.2 z ((mem_roots_toC_iff hF.1).mpr hzF)

/-- **One order for all roots.** For finitely many pure local factors there is `N > 0` with
`w^N = 1` for every root `w` of every factor. -/
theorem exists_common_order {d : ℕ} (F : Fin d → ℤ[X]) (hF : ∀ i, IsPureLocal (F i)) :
    ∃ N : ℕ, 0 < N ∧ ∀ i, ∀ w ∈ (toC (F i)).roots, w ^ N = 1 := by
  classical
  -- the order of each root, and their product
  have hord : ∀ i, ∀ w : ℂ, ∃ n : ℕ, 0 < n ∧ (w ∈ (toC (F i)).roots → w ^ n = 1) := by
    intro i w
    by_cases hw : w ∈ (toC (F i)).roots
    · obtain ⟨n, hn, h⟩ := exists_pow_eq_one_of_pure (hF i) hw
      exact ⟨n, hn, fun _ => h⟩
    · exact ⟨1, one_pos, fun h => absurd h hw⟩
  choose n hn hpow using hord
  set N : ℕ := ∏ i, ∏ w ∈ (toC (F i)).roots.toFinset, n i w with hN
  refine ⟨N, Finset.prod_pos fun i _ => Finset.prod_pos fun w _ => hn i w, fun i w hw => ?_⟩
  have hdvd : n i w ∣ N :=
    (Finset.dvd_prod_of_mem (fun w => n i w) (Multiset.mem_toFinset.mpr hw)).trans
      (Finset.dvd_prod_of_mem (fun i => ∏ w ∈ (toC (F i)).roots.toFinset, n i w)
        (Finset.mem_univ i))
  obtain ⟨k, hk⟩ := hdvd
  rw [hk, pow_mul, hpow i w hw, one_pow]

/-- The Euler carrier `∏_i F_i(p_i^{−s})`. -/
def pureCarrier {d : ℕ} (p : Fin d → ℕ) (F : Fin d → ℤ[X]) (s : ℂ) : ℂ :=
  ∏ i, (toC (F i)).eval ((p i : ℂ) ^ (-s))

/-- **Zeros lie on refined Euler columns.** -/
theorem pureCarrier_zero_mem_column {d : ℕ} (p : Fin d → ℕ) (F : Fin d → ℤ[X]) (hF : ∀ i, IsPureLocal (F i)) {N : ℕ}
    (hN : ∀ i, ∀ w ∈ (toC (F i)).roots, w ^ N = 1) {s : ℂ} (hs : pureCarrier p F s = 0) :
    eulerCarrier p (N * s) = 0 := by
  unfold pureCarrier at hs
  obtain ⟨i, -, hi⟩ := Finset.prod_eq_zero_iff.mp hs
  have hmem : (p i : ℂ) ^ (-s) ∈ (toC (F i)).roots :=
    (mem_roots (toC_ne_zero (hF i).1)).mpr hi
  have hw := hN i _ hmem
  unfold eulerCarrier
  refine Finset.prod_eq_zero (Finset.mem_univ i) ?_
  rw [show -((N : ℂ) * s) = (N : ℂ) * -s by ring, Complex.cpow_nat_mul, hw, sub_self]

/-- **Integral pure Euler carriers collide or repel at polynomial scale.** For distinct primes
`p_i` and pure monic `F_i ∈ ℤ[X]` there are `c, C > 0` such that distinct zeros of
`∏_i F_i(p_i^{−s})` of height at most `T ≥ 1` are at distance `≥ c T^{−C}`. -/
theorem pureCarrier_collide_or_repel {d : ℕ} (p : Fin d → ℕ) (hp : Function.Injective p)
    (hprime : ∀ i, (p i).Prime) (F : Fin d → ℤ[X]) (hF : ∀ i, IsPureLocal (F i)) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ T : ℝ, 1 ≤ T → ∀ ρ ρ' : ℂ,
      pureCarrier p F ρ = 0 → pureCarrier p F ρ' = 0 → |ρ.im| ≤ T → |ρ'.im| ≤ T → ρ ≠ ρ' →
        c * T ^ (-C) ≤ ‖ρ - ρ'‖ := by
  obtain ⟨N, hN0, hN⟩ := exists_common_order F hF
  obtain ⟨c, C, hc, hC, hrep⟩ := eulerCarrier_collide_or_repel p hp hprime
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN0
  have hNr1 : (1 : ℝ) ≤ N := by exact_mod_cast hN0
  refine ⟨c * (N : ℝ) ^ (-C) / N, C, by positivity, hC, fun T hT ρ ρ' hρ hρ' hT1 hT2 hne => ?_⟩
  have hNc : (N : ℂ) ≠ 0 := by exact_mod_cast hN0.ne'
  have hNe : (N : ℂ) * ρ ≠ N * ρ' := fun h => hne (mul_left_cancel₀ hNc h)
  have him : ∀ z : ℂ, |((N : ℂ) * z).im| = N * |z.im| := fun z => by
    rw [show ((N : ℂ) * z).im = N * z.im by simp, abs_mul, abs_of_pos hNr]
  have h := hrep (N * T) (by nlinarith) (N * ρ) (N * ρ')
    (pureCarrier_zero_mem_column p F hF hN hρ) (pureCarrier_zero_mem_column p F hF hN hρ')
    (by rw [him]; exact mul_le_mul_of_nonneg_left hT1 hNr.le)
    (by rw [him]; exact mul_le_mul_of_nonneg_left hT2 hNr.le) hNe
  rw [← mul_sub, norm_mul, Complex.norm_natCast, Real.mul_rpow hNr.le (by linarith)] at h
  have h' : c * (N : ℝ) ^ (-C) * T ^ (-C) ≤ N * ‖ρ - ρ'‖ := by linarith
  have hgoal : c * (N : ℝ) ^ (-C) / N * T ^ (-C) = (c * (N : ℝ) ^ (-C) * T ^ (-C)) / N := by ring
  rw [hgoal, div_le_iff₀ hNr]
  linarith

end GaloisForLFunctions.ArithmeticDiscreteness
