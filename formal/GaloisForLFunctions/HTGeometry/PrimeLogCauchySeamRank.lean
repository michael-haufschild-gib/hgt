import GaloisForLFunctions.HTGeometry.PrimeLogHerglotz
import Mathlib.Algebra.Polynomial.Reverse

/-!
# Infinite renormalization rank of transported prime-log Cauchy sections

Every nonzero proper rational function has a finite, nonzero order at real infinity.  Combining
that order with the all-finite-order prime-log transport wall proves that no nonzero finite packet
of distinct upper-half-plane Cauchy sections becomes square-summable after any positive
exponential transport.  Equivalently, the transported sections are finitely linearly independent
modulo the prime square-summable class.
-/

open Filter Polynomial
open scoped Topology

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- A complex polynomial divided by its top real monomial tends to its leading coefficient. -/
theorem tendsto_eval_div_pow_natDegree (Q : ℂ[X]) :
    Tendsto (fun t : ℝ => Q.eval (t : ℂ) / (t : ℂ) ^ Q.natDegree)
      atTop (𝓝 Q.leadingCoeff) := by
  have hinv : Tendsto (fun t : ℝ => ((t⁻¹ : ℝ) : ℂ)) atTop (𝓝 0) := by
    simpa [Function.comp_def] using
      Complex.continuous_ofReal.continuousAt.tendsto.comp tendsto_inv_atTop_zero
  have hrev : Tendsto (fun t : ℝ => Q.reverse.eval ((t⁻¹ : ℝ) : ℂ))
      atTop (𝓝 Q.leadingCoeff) := by
    rw [show (fun t : ℝ => Q.reverse.eval ((t⁻¹ : ℝ) : ℂ)) =
      (fun x => Q.reverse.eval x) ∘ fun t : ℝ => ((t⁻¹ : ℝ) : ℂ) by rfl]
    have hzero : Q.reverse.eval 0 = Q.leadingCoeff := by
      rw [← Polynomial.coeff_zero_eq_eval_zero, Polynomial.coeff_zero_reverse]
    rw [← hzero]
    exact Q.reverse.continuous.continuousAt.tendsto.comp hinv
  apply hrev.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
  have ht0 : (t : ℂ) ≠ 0 := by exact_mod_cast ht.ne'
  letI : Invertible (t : ℂ) := invertibleOfNonzero ht0
  have hreverse := Polynomial.eval₂_reverse_mul_pow (RingHom.id ℂ) (t : ℂ) Q
  have hinvcast : ⅟(t : ℂ) = ((t⁻¹ : ℝ) : ℂ) := by
    apply invOf_eq_right_inv
    norm_cast
    exact mul_inv_cancel₀ ht.ne'
  rw [hinvcast] at hreverse
  simp only [Polynomial.eval₂_id] at hreverse
  rw [← hreverse]
  field_simp

/-- A proper rational function, multiplied by its order at infinity, tends to the quotient of
leading coefficients. -/
theorem tendsto_rational_mul_pow_order (Q D : ℂ[X])
    (hD : D ≠ 0) (hdeg : Q.natDegree < D.natDegree) :
    Tendsto (fun t : ℝ =>
        (t : ℂ) ^ (D.natDegree - Q.natDegree) *
          (Q.eval (t : ℂ) / D.eval (t : ℂ)))
      atTop (𝓝 (Q.leadingCoeff / D.leadingCoeff)) := by
  have hQlim := tendsto_eval_div_pow_natDegree Q
  have hDlim := tendsto_eval_div_pow_natDegree D
  have hlcD : D.leadingCoeff ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hD
  have hdiv : Tendsto (fun t : ℝ =>
      (Q.eval (t : ℂ) / (t : ℂ) ^ Q.natDegree) /
        (D.eval (t : ℂ) / (t : ℂ) ^ D.natDegree))
      atTop (𝓝 (Q.leadingCoeff / D.leadingCoeff)) :=
    hQlim.div hDlim hlcD
  apply hdiv.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
  have ht0 : (t : ℂ) ≠ 0 := by exact_mod_cast ht.ne'
  by_cases hDeval : D.eval (t : ℂ) = 0
  · simp [hDeval]
  · have hpow : (t : ℂ) ^ (D.natDegree - Q.natDegree) *
        (t : ℂ) ^ Q.natDegree = (t : ℂ) ^ D.natDegree := by
      rw [← pow_add]
      congr
      omega
    field_simp [ht0, hDeval]
    rw [← hpow]
    ring

/-- The scaled rational function is eventually bounded away from zero. -/
theorem eventually_rational_order_lower (Q D : ℂ[X])
    (hQ : Q ≠ 0) (hD : D ≠ 0) (hdeg : Q.natDegree < D.natDegree) :
    ∀ᶠ t : ℝ in atTop,
      (‖Q.leadingCoeff / D.leadingCoeff‖ / 2) ^ 2 ≤
        Complex.normSq ((t : ℂ) ^ (D.natDegree - Q.natDegree) *
          (Q.eval (t : ℂ) / D.eval (t : ℂ))) := by
  let a : ℂ := Q.leadingCoeff / D.leadingCoeff
  have hlcQ : Q.leadingCoeff ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hQ
  have hlcD : D.leadingCoeff ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hD
  have ha : a ≠ 0 := div_ne_zero hlcQ hlcD
  have hanorm : 0 < ‖a‖ := norm_pos_iff.mpr ha
  have hlim := tendsto_rational_mul_pow_order Q D hD hdeg
  have hnorm : Tendsto (fun t : ℝ =>
      ‖(t : ℂ) ^ (D.natDegree - Q.natDegree) *
        (Q.eval (t : ℂ) / D.eval (t : ℂ))‖) atTop (𝓝 ‖a‖) := by
    simpa [a] using hlim.norm
  filter_upwards [hnorm.eventually (lt_mem_nhds (by linarith : ‖a‖ / 2 < ‖a‖))] with t ht
  change (‖a‖ / 2) ^ 2 ≤ Complex.normSq _
  rw [Complex.normSq_eq_norm_sq]
  exact sq_le_sq₀ (by positivity) (norm_nonneg _)|>.2 ht.le

/-- A nonzero proper rational function is eventually bounded below by a Cauchy denominator of
its finite order at infinity. -/
theorem eventually_rational_cauchy_lower (Q D : ℂ[X])
    (hQ : Q ≠ 0) (hD : D ≠ 0) (hdeg : Q.natDegree < D.natDegree) :
    ∀ᶠ t : ℝ in atTop,
      (‖Q.leadingCoeff / D.leadingCoeff‖ / 2) ^ 2 /
          (1 + t ^ 2) ^ (D.natDegree - Q.natDegree) ≤
        Complex.normSq (Q.eval (t : ℂ) / D.eval (t : ℂ)) := by
  let m := D.natDegree - Q.natDegree
  filter_upwards [eventually_rational_order_lower Q D hQ hD hdeg,
    eventually_ge_atTop (1 : ℝ)] with t hlower ht
  have htpos : 0 < t := lt_of_lt_of_le zero_lt_one ht
  have hdenpos : 0 < (1 + t ^ 2) ^ m := by positivity
  have hnormmul : Complex.normSq ((t : ℂ) ^ m *
      (Q.eval (t : ℂ) / D.eval (t : ℂ))) =
      t ^ (2 * m) * Complex.normSq (Q.eval (t : ℂ) / D.eval (t : ℂ)) := by
    simp only [Complex.normSq_eq_norm_sq, norm_mul, norm_pow, Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonneg htpos.le]
    rw [show t ^ (2 * m) = (t ^ m) ^ 2 by rw [← pow_mul]; congr 1; omega]
    ring
  rw [hnormmul] at hlower
  have hpowle : t ^ (2 * m) ≤ (1 + t ^ 2) ^ m := by
    calc
      t ^ (2 * m) = (t ^ 2) ^ m := by rw [← pow_mul]
      _ ≤ (1 + t ^ 2) ^ m := by gcongr; linarith
  rw [div_le_iff₀ hdenpos]
  calc
    (‖Q.leadingCoeff / D.leadingCoeff‖ / 2) ^ 2 ≤
        t ^ (2 * m) * Complex.normSq (Q.eval (t : ℂ) / D.eval (t : ℂ)) := hlower
    _ ≤ Complex.normSq (Q.eval (t : ℂ) / D.eval (t : ℂ)) *
        (1 + t ^ 2) ^ m := by
      rw [mul_comm]
      gcongr
      exact Complex.normSq_nonneg _

/-- Prime logarithms tend to infinity along the cofinite filter. -/
theorem tendsto_primeLogSupport_cofinite :
    Tendsto primeLogSupport cofinite atTop := by
  rw [tendsto_atTop]
  intro R
  have hfinite : Set.Finite {p : Nat.Primes | primeLogSupport p ≤ R} :=
    finite_primeLogSupport_le R
  filter_upwards [hfinite.compl_mem_cofinite] with p hp
  have hlt : R < primeLogSupport p := lt_of_not_ge hp
  exact hlt.le

/-- Transported prime energy of a rational function evaluated on the prime-log support. -/
def primeLogRationalTransportEnergy (Q D : ℂ[X]) (b : ℝ) (p : Nat.Primes) : ℝ :=
  (p : ℝ) ^ (2 * b - 1) * Complex.normSq
    (Q.eval (primeLogSupport p : ℂ) / D.eval (primeLogSupport p : ℂ))

/-- Every nonzero proper rational function has divergent prime-log energy after every positive
exponential transport. -/
theorem not_summable_primeLogRationalTransportEnergy_of_pos
    (Q D : ℂ[X]) (hQ : Q ≠ 0) (hD : D ≠ 0)
    (hdeg : Q.natDegree < D.natDegree) {b : ℝ} (hb : 0 < b) :
    ¬ Summable (primeLogRationalTransportEnergy Q D b) := by
  intro hsum
  let m := D.natDegree - Q.natDegree
  let A : ℝ := (‖Q.leadingCoeff / D.leadingCoeff‖ / 2) ^ 2
  have hlcQ : Q.leadingCoeff ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hQ
  have hlcD : D.leadingCoeff ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hD
  have hratio : 0 < ‖Q.leadingCoeff / D.leadingCoeff‖ :=
    norm_pos_iff.mpr (div_ne_zero hlcQ hlcD)
  have hA : 0 < A := by
    dsimp [A]
    positivity
  have hmass_nonneg : ∀ p, 0 ≤ primeLogHerglotzTransportMassOrder m b p := by
    intro p
    rw [primeLogHerglotzTransportMassOrder]
    positivity
  have henergy_nonneg : ∀ p, 0 ≤ primeLogRationalTransportEnergy Q D b p := by
    intro p
    dsimp [primeLogRationalTransportEnergy]
    exact mul_nonneg (Real.rpow_nonneg (by positivity) _) (Complex.normSq_nonneg _)
  have hreal := eventually_rational_cauchy_lower Q D hQ hD hdeg
  have hprime : ∀ᶠ p : Nat.Primes in cofinite,
      A * primeLogHerglotzTransportMassOrder m b p ≤
        primeLogRationalTransportEnergy Q D b p := by
    have hcomp := tendsto_primeLogSupport_cofinite.eventually hreal
    filter_upwards [hcomp] with p hp
    have hp0 : 0 < (p : ℝ) := by exact_mod_cast p.prop.pos
    have hppos : 0 < (p : ℝ) ^ (2 * b - 1) := Real.rpow_pos_of_pos hp0 _
    dsimp [A, m] at hp ⊢
    rw [primeLogHerglotzTransportMassOrder]
    change (‖Q.leadingCoeff / D.leadingCoeff‖ / 2) ^ 2 *
        ((p : ℝ) ^ (2 * b - 1) /
          (1 + primeLogSupport p ^ 2) ^ (D.natDegree - Q.natDegree)) ≤ _
    dsimp [primeLogRationalTransportEnergy]
    calc
      _ = (p : ℝ) ^ (2 * b - 1) *
          ((‖Q.leadingCoeff / D.leadingCoeff‖ / 2) ^ 2 /
            (1 + primeLogSupport p ^ 2) ^ (D.natDegree - Q.natDegree)) := by ring
      _ ≤ (p : ℝ) ^ (2 * b - 1) * Complex.normSq
          (Q.eval (primeLogSupport p : ℂ) / D.eval (primeLogSupport p : ℂ)) := by
        gcongr
  let lower : Nat.Primes → ℝ := fun p =>
    if A * primeLogHerglotzTransportMassOrder m b p ≤
        primeLogRationalTransportEnergy Q D b p then
      A * primeLogHerglotzTransportMassOrder m b p
    else 0
  have hlower_nonneg : ∀ p, 0 ≤ lower p := by
    intro p
    dsimp [lower]
    split_ifs
    · exact mul_nonneg hA.le (hmass_nonneg p)
    · exact le_rfl
  have hlower_le : ∀ p, lower p ≤ primeLogRationalTransportEnergy Q D b p := by
    intro p
    dsimp [lower]
    split_ifs with h
    · exact h
    · exact henergy_nonneg p
  have hlower_sum : Summable lower :=
    Summable.of_nonneg_of_le hlower_nonneg hlower_le hsum
  have heq : lower =ᶠ[cofinite]
      (fun p => A * primeLogHerglotzTransportMassOrder m b p) := by
    filter_upwards [hprime] with p hp
    simp [lower, hp]
  have hscaled : Summable (fun p => A * primeLogHerglotzTransportMassOrder m b p) :=
    hlower_sum.congr_cofinite heq
  have hmass : Summable (primeLogHerglotzTransportMassOrder m b) :=
    (summable_mul_left_iff hA.ne').mp hscaled
  exact not_summable_primeLogHerglotzTransportMassOrder_of_pos m hb hmass

/-- Common denominator of a finite Cauchy packet. -/
def cauchyPacketDenominator {n : ℕ} (z : Fin n → ℂ) : ℂ[X] :=
  ∏ j, (Polynomial.C (z j) - Polynomial.X)

/-- Numerator of a finite Cauchy packet after clearing its common denominator. -/
def cauchyPacketNumerator {n : ℕ} (z c : Fin n → ℂ) : ℂ[X] :=
  ∑ j, Polynomial.C (c j) *
    ∏ k ∈ Finset.univ.erase j, (Polynomial.C (z k) - Polynomial.X)

/-- Evaluation of the packet numerator at one of its nodes. -/
theorem cauchyPacketNumerator_eval_node {n : ℕ} (z c : Fin n → ℂ) (m : Fin n) :
    (cauchyPacketNumerator z c).eval (z m) =
      c m * ∏ k ∈ Finset.univ.erase m, (z k - z m) := by
  rw [cauchyPacketNumerator]
  simp only [Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C,
    Polynomial.eval_prod, Polynomial.eval_sub, Polynomial.eval_X]
  rw [Finset.sum_eq_single m]
  · intro i _ hi
    rw [Finset.prod_eq_zero
      (Finset.mem_erase.mpr ⟨fun h => hi h.symm, Finset.mem_univ m⟩)]
    · ring
    · exact sub_self _
  · intro h
    exact absurd (Finset.mem_univ m) h

/-- Distinct nodes and a nonzero coefficient packet give a nonzero numerator. -/
theorem cauchyPacketNumerator_ne_zero {n : ℕ} (z c : Fin n → ℂ)
    (hz : Function.Injective z) (hc : c ≠ 0) :
    cauchyPacketNumerator z c ≠ 0 := by
  obtain ⟨m, hm⟩ := Function.ne_iff.mp hc
  simp only [Pi.zero_apply] at hm
  intro hzero
  have heval := congrArg (fun Q : ℂ[X] => Q.eval (z m)) hzero
  have heval' : (cauchyPacketNumerator z c).eval (z m) = 0 := by
    simpa only [Polynomial.eval_zero] using heval
  rw [cauchyPacketNumerator_eval_node z c m] at heval'
  have hprod : ∏ k ∈ Finset.univ.erase m, (z k - z m) ≠ 0 := by
    apply Finset.prod_ne_zero_iff.mpr
    intro k hk
    exact sub_ne_zero.mpr (fun h => (Finset.mem_erase.mp hk).1 (hz h))
  exact hm ((mul_eq_zero.mp heval').resolve_right hprod)

/-- A finite Cauchy denominator is nonzero. -/
theorem cauchyPacketDenominator_ne_zero {n : ℕ} (z : Fin n → ℂ) :
    cauchyPacketDenominator z ≠ 0 := by
  rw [cauchyPacketDenominator]
  apply Finset.prod_ne_zero_iff.mpr
  intro j _
  rw [show Polynomial.C (z j) - Polynomial.X =
    -(Polynomial.X - Polynomial.C (z j)) by ring]
  exact neg_ne_zero.mpr (Polynomial.X_sub_C_ne_zero (z j))

/-- The common denominator has degree equal to the packet size. -/
theorem cauchyPacketDenominator_natDegree {n : ℕ} (z : Fin n → ℂ) :
    (cauchyPacketDenominator z).natDegree = n := by
  rw [cauchyPacketDenominator,
    Polynomial.natDegree_prod _ _ (fun j _ => by
      rw [show Polynomial.C (z j) - Polynomial.X =
        -(Polynomial.X - Polynomial.C (z j)) by ring]
      exact neg_ne_zero.mpr (Polynomial.X_sub_C_ne_zero (z j)))]
  calc
    ∑ j, (Polynomial.C (z j) - Polynomial.X).natDegree = ∑ _j : Fin n, 1 := by
      apply Finset.sum_congr rfl
      intro j _
      rw [show Polynomial.C (z j) - Polynomial.X =
        -(Polynomial.X - Polynomial.C (z j)) by ring,
        Polynomial.natDegree_neg, Polynomial.natDegree_X_sub_C]
    _ = n := by simp

/-- A nonzero packet numerator has degree strictly below its common denominator. -/
theorem cauchyPacketNumerator_natDegree_lt {n : ℕ} (z c : Fin n → ℂ)
    (hc : c ≠ 0) :
    (cauchyPacketNumerator z c).natDegree < n := by
  have hn : 0 < n := by
    by_contra h
    have hn0 : n = 0 := Nat.eq_zero_of_not_pos h
    apply hc
    funext j
    exact Fin.elim0 (hn0 ▸ j)
  rw [cauchyPacketNumerator]
  refine lt_of_le_of_lt (Polynomial.natDegree_sum_le_of_forall_le _ _ (fun i _ => ?_))
    (Nat.sub_lt hn Nat.zero_lt_one)
  refine (Polynomial.natDegree_C_mul_le _ _).trans
    ((Polynomial.natDegree_prod_le _ _).trans ?_)
  refine (Finset.sum_le_sum (g := fun _ => 1)
    (fun k _ => (Polynomial.natDegree_sub_le _ _).trans (by simp))).trans ?_
  rw [Finset.sum_const, smul_eq_mul, mul_one,
    Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_univ]
  simp

/-- The cleared rational function equals the original finite Cauchy packet away from its nodes. -/
theorem cauchyPacket_eval_div_eq_sum {n : ℕ} (z c : Fin n → ℂ) (t : ℂ)
    (ht : ∀ j, z j ≠ t) :
    (cauchyPacketNumerator z c).eval t / (cauchyPacketDenominator z).eval t =
      ∑ j, c j * (z j - t)⁻¹ := by
  have hprodne : ∏ j, (z j - t) ≠ 0 := by
    apply Finset.prod_ne_zero_iff.mpr
    intro j _
    exact sub_ne_zero.mpr (ht j)
  have hden : (cauchyPacketDenominator z).eval t = ∏ j, (z j - t) := by
    rw [cauchyPacketDenominator, Polynomial.eval_prod]
    apply Finset.prod_congr rfl
    intro j _
    simp
  rw [div_eq_iff (hden ▸ hprodne), hden]
  have key : (∏ j, (z j - t)) * (∑ i, c i * (z i - t)⁻¹) =
      ∑ i, c i * ∏ j ∈ Finset.univ.erase i, (z j - t) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [← Finset.prod_erase_mul _ _ (Finset.mem_univ i)]
    have hi : z i - t ≠ 0 := sub_ne_zero.mpr (ht i)
    field_simp
  rw [cauchyPacketNumerator]
  simp only [Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C,
    Polynomial.eval_prod, Polynomial.eval_sub, Polynomial.eval_X]
  rw [← key]
  ring

/-- The squared prime-side energy of a finite packet of transported Cauchy sections. -/
def primeLogCauchyPacketTransportEnergy {n : ℕ}
    (z c : Fin n → ℂ) (b : ℝ) (p : Nat.Primes) : ℝ :=
  (p : ℝ) ^ (2 * b - 1) * Complex.normSq
    (∑ j, c j * (z j - (primeLogSupport p : ℂ))⁻¹)

/-- Every nonzero finite packet of distinct upper-half-plane Cauchy sections remains outside
the prime `ell^(2 : ℕ)` space after every positive exponential transport. -/
theorem not_summable_primeLogCauchyPacketTransportEnergy_of_pos {n : ℕ}
    (z c : Fin n → ℂ) (hz : Function.Injective z) (hzUpper : ∀ j, 0 < (z j).im)
    (hc : c ≠ 0) {b : ℝ} (hb : 0 < b) :
    ¬ Summable (primeLogCauchyPacketTransportEnergy z c b) := by
  let Q := cauchyPacketNumerator z c
  let D := cauchyPacketDenominator z
  have hQ : Q ≠ 0 := cauchyPacketNumerator_ne_zero z c hz hc
  have hD : D ≠ 0 := cauchyPacketDenominator_ne_zero z
  have hdeg : Q.natDegree < D.natDegree := by
    dsimp [Q, D]
    rw [cauchyPacketDenominator_natDegree]
    exact cauchyPacketNumerator_natDegree_lt z c hc
  intro hsum
  apply not_summable_primeLogRationalTransportEnergy_of_pos Q D hQ hD hdeg hb
  apply hsum.congr
  intro p
  have haway : ∀ j, z j ≠ (primeLogSupport p : ℂ) := by
    intro j h
    have him := congrArg Complex.im h
    simp at him
    exact (ne_of_gt (hzUpper j)) him
  have hid := cauchyPacket_eval_div_eq_sum z c (primeLogSupport p : ℂ) haway
  dsimp [primeLogCauchyPacketTransportEnergy, primeLogRationalTransportEnergy, Q, D]
  rw [hid]

/-- Exact finite independence modulo the transported prime square-summable class: a packet of
distinct upper-half-plane Cauchy sections has summable transported energy exactly when all of its
coefficients vanish. -/
theorem summable_primeLogCauchyPacketTransportEnergy_iff {n : ℕ}
    (z c : Fin n → ℂ) (hz : Function.Injective z) (hzUpper : ∀ j, 0 < (z j).im)
    {b : ℝ} (hb : 0 < b) :
    Summable (primeLogCauchyPacketTransportEnergy z c b) ↔ c = 0 := by
  constructor
  · intro hsum
    by_contra hc
    exact not_summable_primeLogCauchyPacketTransportEnergy_of_pos
      z c hz hzUpper hc hb hsum
  · rintro rfl
    have hzero : primeLogCauchyPacketTransportEnergy z 0 b = 0 := by
      funext p
      simp [primeLogCauchyPacketTransportEnergy]
    rw [hzero]
    exact summable_zero

end

end GaloisForLFunctions.HTGeometry
