import GaloisForLFunctions.BezoutValuationIncidence.VaughanAdmissionAboveHalfDamping
import Mathlib.Analysis.Normed.Group.Tannery

/-!
Above half damping, the three small Vaughan floor coefficients converge in
critical Wiener norm. Finite convolution stabilization supplies pointwise
convergence, and the divisor-square majorant supplies one summable envelope.
-/

open Finset Filter ArithmeticFunction RHTower
open GaloisForLFunctions.TransHorizonIncidenceMechanics
open scoped BigOperators Topology
noncomputable section
namespace GaloisForLFunctions.BezoutValuationIncidence
set_option autoImplicit false

/-- Once both cutoffs cover an index, the small-small coefficient is exactly Möbius. -/
theorem pmPronicVaughanSmallSmallCoeff_eq_moebius_of_le
    {U V n : ℕ} (hU : n ≤ U) (hV : n ≤ V) :
    pmPronicVaughanSmallSmallCoeff U V n = (moebius n : ℝ) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [pmPronicVaughanSmallSmallCoeff]
  have heq : (Sieve.truncatedMoebius U *
      (Sieve.truncatedMoebius V * (zeta : ArithmeticFunction ℝ))) n =
      (Sieve.truncatedMoebius U * 1) n := by
    rw [ArithmeticFunction.mul_apply, ArithmeticFunction.mul_apply]
    apply sum_congr rfl
    intro x hx
    have hd : x.2 ≤ V := (Nat.le_of_dvd hn
      (Nat.dvd_of_mem_divisors (Nat.snd_mem_divisors_of_mem_antidiagonal hx))).trans hV
    have hz := Sieve.moebiusZetaDefect_vanishesBelow V x.2 (by omega)
    change (1 : ArithmeticFunction ℝ) x.2 -
      (Sieve.truncatedMoebius V * (zeta : ArithmeticFunction ℝ)) x.2 = 0 at hz
    rw [← sub_eq_zero.mp hz]
  change (Sieve.truncatedMoebius U *
    (Sieve.truncatedMoebius V * (zeta : ArithmeticFunction ℝ))) n = _
  rw [heq, mul_one, Sieve.truncatedMoebius_apply, if_pos hU]

private theorem tendsto_criticalWiener_difference_of_vaughan_stabilization
    {ε : ℝ} (hε : 1 / 2 < ε) {a : ℕ → ℕ → ℝ} {b : ℕ → ℝ}
    (ha : ∀ t d, |a t d| ≤ pmVaughanFloorMajorant ε d)
    (hab : ∀ d, ∀ᶠ t : ℕ in atTop, a t d = b d) :
    Tendsto (fun t => ∑' d : ℕ,
      |a t d - b d| * (d : ℝ) ^ (-(1 / 2 : ℝ))) atTop (𝓝 0) := by
  have hpoint (d : ℕ) : Tendsto (fun t => a t d) atTop (𝓝 (b d)) :=
    (tendsto_congr' (hab d)).mpr tendsto_const_nhds
  have hb (d : ℕ) : |b d| ≤ pmVaughanFloorMajorant ε d :=
    le_of_tendsto' (hpoint d).abs (fun t => ha t d)
  have hs := criticalWiener_of_vaughan_floor_majorant hε
    (g := pmVaughanFloorMajorant ε) (fun d => by
      rw [abs_of_nonneg (pmVaughanFloorMajorant_nonneg ε d)])
  change Summable (fun d : ℕ =>
    |pmVaughanFloorMajorant ε d| * (d : ℝ) ^ (-(1 / 2 : ℝ))) at hs
  have hdom (t d : ℕ) :
      ‖|a t d - b d| * (d : ℝ) ^ (-(1 / 2 : ℝ))‖ ≤
        2 * (|pmVaughanFloorMajorant ε d| * (d : ℝ) ^ (-(1 / 2 : ℝ))) := by
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity),
      abs_of_nonneg (pmVaughanFloorMajorant_nonneg ε d)]
    have htriangle : |a t d - b d| ≤ |a t d| + |b d| := by
      simpa only [sub_zero, zero_sub, abs_neg] using abs_sub_le (a t d) 0 (b d)
    have hdiff : |a t d - b d| ≤ 2 * pmVaughanFloorMajorant ε d :=
      htriangle.trans (by linarith only [ha t d, hb d])
    calc
      _ ≤ (2 * pmVaughanFloorMajorant ε d) * (d : ℝ) ^ (-(1 / 2 : ℝ)) :=
        mul_le_mul_of_nonneg_right hdiff (Real.rpow_nonneg (Nat.cast_nonneg d) _)
      _ = _ := by ring
  have hzero (d : ℕ) : Tendsto
      (fun t => |a t d - b d| * (d : ℝ) ^ (-(1 / 2 : ℝ))) atTop (𝓝 (0 : ℝ)) := by
    simpa only [sub_self, abs_zero, zero_mul] using
      (((hpoint d).sub (tendsto_const_nhds (x := b d))).abs.mul_const
        ((d : ℝ) ^ (-(1 / 2 : ℝ))))
  simpa only [tsum_zero] using tendsto_tsum_of_dominated_convergence
    (hs.mul_left 2) hzero (Eventually.of_forall hdom)

private theorem abs_damped_truncatedMoebius_le_vaughan_majorant
    (ε : ℝ) (U d : ℕ) :
    |Sieve.truncatedMoebius U d * (d : ℝ) ^ (-ε)| ≤ pmVaughanFloorMajorant ε d := by
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · simp [pmVaughanFloorMajorant]
  have hc : (1 : ℝ) ≤ d.divisors.card := by
    exact_mod_cast (one_le_card.mpr ⟨1, Nat.mem_divisors.mpr ⟨one_dvd d, hd.ne'⟩⟩)
  have hc2 : (1 : ℝ) ≤ (d.divisors.card : ℝ) ^ 2 := by nlinarith only [hc]
  have hμ : |Sieve.truncatedMoebius U d| ≤ 1 := by
    simpa only [Real.norm_eq_abs] using Sieve.norm_truncatedMoebius_le_one U d
  rw [abs_mul, abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg d) _)]
  exact mul_le_mul_of_nonneg_right (hμ.trans hc2) (Real.rpow_nonneg (Nat.cast_nonneg d) _)

/-- Either truncated Möbius floor coefficient converges in critical Wiener norm above half damping. -/
theorem tendsto_criticalWiener_truncatedMoebius_sub_moebius
    {ε : ℝ} (hε : 1 / 2 < ε) {U : ℕ → ℕ} (hU : Tendsto U atTop atTop) :
    Tendsto (fun t => ∑' d : ℕ,
      |Sieve.truncatedMoebius (U t) d * (d : ℝ) ^ (-ε) -
        (moebius d : ℝ) * (d : ℝ) ^ (-ε)| *
          (d : ℝ) ^ (-(1 / 2 : ℝ))) atTop (𝓝 0) := by
  apply tendsto_criticalWiener_difference_of_vaughan_stabilization hε
    (fun t => abs_damped_truncatedMoebius_le_vaughan_majorant ε (U t))
  intro d
  filter_upwards [hU.eventually_ge_atTop d] with t ht
  rw [Sieve.truncatedMoebius_apply, if_pos ht]

/-- The signed small-small floor coefficient converges to negative Möbius in critical Wiener norm. -/
theorem tendsto_criticalWiener_neg_vaughanSmallSmall_sub_neg_moebius
    {ε : ℝ} (hε : 1 / 2 < ε) {U V : ℕ → ℕ}
    (hU : Tendsto U atTop atTop) (hV : Tendsto V atTop atTop) :
    Tendsto (fun t => ∑' d : ℕ,
      |-(pmPronicVaughanSmallSmallCoeff (U t) (V t) d * (d : ℝ) ^ (-ε)) -
        -((moebius d : ℝ) * (d : ℝ) ^ (-ε))| *
          (d : ℝ) ^ (-(1 / 2 : ℝ))) atTop (𝓝 0) := by
  apply tendsto_criticalWiener_difference_of_vaughan_stabilization hε
  · intro t d
    rw [abs_neg, abs_mul, abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg d) _)]
    exact mul_le_mul_of_nonneg_right
      (abs_pmPronicVaughanSmallSmallCoeff_le (U t) (V t) d)
      (Real.rpow_nonneg (Nat.cast_nonneg d) _)
  · intro d
    filter_upwards [hU.eventually_ge_atTop d, hV.eventually_ge_atTop d] with t htU htV
    rw [pmPronicVaughanSmallSmallCoeff_eq_moebius_of_le htU htV]

#print axioms pmPronicVaughanSmallSmallCoeff_eq_moebius_of_le
#print axioms tendsto_criticalWiener_truncatedMoebius_sub_moebius
#print axioms tendsto_criticalWiener_neg_vaughanSmallSmall_sub_neg_moebius
end GaloisForLFunctions.BezoutValuationIncidence
