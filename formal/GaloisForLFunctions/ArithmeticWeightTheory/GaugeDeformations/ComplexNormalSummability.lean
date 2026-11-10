import GaloisForLFunctions.ArithmeticWeightTheory.GaugeDeformations.NormalPropagation
import GaloisForLFunctions.ArithmeticWeightTheory.GaugeDeformations.RealNormalControl
import GaloisForLFunctions.ArithmeticWeightTheory.GaugeDeformations.JointPoleRigidity

/-!
# Joint pole germs force complex normal prime summability

A common pole germ supplies a common real summability exponent below one.
Baire, interval integration, and propagation of holomorphic smallness turn
this into a summable majorant on a complex parameter disk. Iterated
weighted Cauchy–Schwarz retains a positive power saving. The resulting
closed-disk suprema are summable at one exponent strictly below one.
-/

open Complex Filter Topology Metric Set MeasureTheory
open GaloisForLFunctions.HTGeometry
open GaloisForLFunctions.ArithmeticCorrelationGeometry
open GaloisForLFunctions.PrimeTorusTheory
open _root_.RHTower
noncomputable section
set_option autoImplicit false
namespace GaloisForLFunctions.ArithmeticWeightTheory.GaugeDeformations

/-- Iterated square roots retain a positive saving in a weighted prime sum. -/
theorem summable_prime_dyadic_rpow {a : Nat.Primes → ℝ} (ha : ∀ p, 0 ≤ a p)
    {δ : ℝ} (hδ : 0 < δ)
    (hs : Summable (fun p => a p * (p : ℝ) ^ (-(1 - δ)))) (k : ℕ) :
    Summable (fun p => a p ^ ((1 / 2 : ℝ) ^ k) *
      (p : ℝ) ^ (-(1 - δ / (4 : ℝ) ^ k))) := by
  induction k with
  | zero => simpa only [pow_zero, Real.rpow_one, div_one] using hs
  | succ k ih =>
    have he (p : Nat.Primes) : (a p ^ ((1 / 2 : ℝ) ^ (k + 1))) ^ 2 =
        a p ^ ((1 / 2 : ℝ) ^ k) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (ha p)]
      congr 1
      rw [pow_succ]
      ring
    have hsq : Summable (fun p => (a p ^ ((1 / 2 : ℝ) ^ (k + 1))) ^ 2 *
        (p : ℝ) ^ (-(1 - δ / (4 : ℝ) ^ k))) := by
      simpa only [he] using ih
    have hh := summable_absolute_prime_of_energy
      (show 0 < δ / (4 : ℝ) ^ k by positivity) hsq
    have hdiv : δ / (4 : ℝ) ^ k / 4 = δ / (4 : ℝ) ^ (k + 1) := by
      rw [pow_succ, div_div]
    simpa only [hdiv, abs_of_nonneg (Real.rpow_nonneg (ha _) _)] using hh

/-- A bounded holomorphic prime family with real power-saving sums has a complex normal majorant. -/
theorem exists_complex_normal_majorant {f : Nat.Primes → ℂ → ℂ} {R M ε σ₀ : ℝ}
    (hR : 0 < R) (hM : 0 < M) (hε : 0 < ε) (hσ₀ : 1 / 2 < σ₀) (hσ₁ : σ₀ < 1)
    (hd : ∀ p, DifferentiableOn ℂ (f p) (ball 0 R))
    (hb : ∀ p z, z ∈ ball (0 : ℂ) R → ‖f p z‖ ≤ M)
    (hs : ∀ t : ℝ, |t| < ε →
      Summable (fun p => ‖f p (t : ℂ)‖ * (p : ℝ) ^ (-σ₀))) :
    ∃ (ρ σ : ℝ) (b : Nat.Primes → ℝ),
      0 < ρ ∧ ρ < R ∧ 1 / 2 < σ ∧ σ < 1 ∧
      Summable (fun p => b p * (p : ℝ) ^ (-σ)) ∧
      ∀ p z, ‖z‖ ≤ ρ → ‖f p z‖ ≤ b p := by
  let S := min (R / 4) (ε / 2)
  have hS : 0 < S := lt_min (by positivity) (by positivity)
  have hSR : S ≤ R / 4 := min_le_left _ _
  have hSε : S ≤ ε / 2 := min_le_right _ _
  have hball (t : ℝ) (ht : |t| < S) : (t : ℂ) ∈ ball (0 : ℂ) R := by
    rw [mem_ball, dist_zero_right, norm_real, Real.norm_eq_abs]
    linarith only [ht, hSR, hR]
  have hc (p : Nat.Primes) : ContinuousOn (fun t : ℝ => ‖f p (t : ℂ)‖) (Ioo (-S) S) := by
    intro t ht
    exact (((hd p).differentiableAt (isOpen_ball.mem_nhds (hball t (abs_lt.mpr ht)))).continuousAt.comp
      Complex.continuous_ofReal.continuousAt).norm.continuousWithinAt
  -- Baire controls every finite weighted sum on one real interval.
  obtain ⟨c, r, C, hr, hC, hcr, hsum⟩ := exists_interval_sum_bound hS
    (f := fun p t => ‖f p (t : ℂ)‖ * (p : ℝ) ^ (-σ₀))
    (fun p => (hc p).mul continuousOn_const) (fun p t _ => by positivity)
    (fun t ht => hs t (by have ht' := abs_lt.mpr ht; linarith only [ht', hSε, hε]))
  have hab : c - r ≤ c + r := by linarith only [hr]
  have hdist (t : ℝ) (ht : t ∈ Icc (c - r) (c + r)) : |t - c| ≤ r :=
    abs_le.mpr ⟨by linarith only [ht.1], by linarith only [ht.2]⟩
  have hJsmall (t : ℝ) (ht : t ∈ Icc (c - r) (c + r)) : |t| < S := by
    have ha : |t| ≤ |t - c| + |c| := by
      simpa only [sub_add_cancel] using abs_add_le (t - c) c
    linarith only [ha, hdist t ht, hcr]
  have hJhalf (t : ℝ) (ht : t ∈ Icc (c - r) (c + r)) :
      (t : ℂ) ∈ ball (0 : ℂ) (R / 2) := by
    rw [mem_ball, dist_zero_right, norm_real, Real.norm_eq_abs]
    linarith only [hJsmall t ht, hSR, hR]
  have hcJ (p : Nat.Primes) : ContinuousOn (fun t : ℝ => ‖f p (t : ℂ)‖)
      (Icc (c - r) (c + r)) := (hc p).mono (fun t ht => abs_lt.mp (hJsmall t ht))
  let I : Nat.Primes → ℝ := fun p => ∫ t in (c - r)..(c + r), ‖f p (t : ℂ)‖
  have hI (p : Nat.Primes) : 0 ≤ I p :=
    intervalIntegral.integral_nonneg hab (fun t _ => norm_nonneg _)
  have hIs : Summable (fun p => I p * (p : ℝ) ^ (-σ₀)) := by
    have hh := summable_interval_integrals_of_sum_bound hab
      (f := fun p t => ‖f p (t : ℂ)‖ * (p : ℝ) ^ (-σ₀))
      (fun p => (hcJ p).mul continuousOn_const) (fun p t _ => by positivity)
      (fun t ht F => hsum t (hdist t ht) F)
    simpa only [intervalIntegral.integral_mul_const] using hh
  -- A summable positive tail avoids zero bases in fractional powers.
  let A : Nat.Primes → ℝ := fun p => I p + (p : ℝ) ^ (-2 : ℝ)
  have hA (p : Nat.Primes) : 0 < A p := add_pos_of_nonneg_of_pos (hI p)
    (Real.rpow_pos_of_pos (by exact_mod_cast p.2.pos) _)
  have hIA (p : Nat.Primes) : I p ≤ A p := le_add_of_nonneg_right (by positivity)
  have hAs : Summable (fun p => A p * (p : ℝ) ^ (-σ₀)) := by
    have hh := summable_primeDamping (show 1 < 2 + σ₀ by linarith only [hσ₀])
    change Summable (fun p : Nat.Primes => (p : ℝ) ^ (-(2 + σ₀))) at hh
    have he (p : Nat.Primes) : A p * (p : ℝ) ^ (-σ₀) =
        I p * (p : ℝ) ^ (-σ₀) + (p : ℝ) ^ (-(2 + σ₀)) := by
      dsimp only [A]
      rw [add_mul, ← Real.rpow_add (by exact_mod_cast p.2.pos : (0 : ℝ) < (p : ℝ))]
      congr 2
      ring
    simpa only [he] using hIs.add hh
  let L := 2 * M / R
  have hL : 0 ≤ L := by dsimp [L]; positivity
  let K := 4 * (L + M / r)
  have hK : 0 < K := by dsimp [K]; positivity
  have hpeak (p : Nat.Primes) (t : ℝ) (ht : |t - c| ≤ r / 2) :
      ‖f p (t : ℂ)‖ ≤ Real.sqrt (K * A p) := by
    have hh := sq_le_interval_integral_of_lipschitz hr hL hM (hcJ p)
      (fun t _ => norm_nonneg _) (fun t ht => hb p (t : ℂ) (hball t (hJsmall t ht)))
      (fun t ht u hu => by
        apply (abs_norm_sub_norm_le (f p (u : ℂ)) (f p (t : ℂ))).trans
        have hl := Bottcher.norm_sub_le_of_bounded_on_ball hR (hd p) (hb p)
          (hJhalf u hu) (hJhalf t ht)
        simpa only [← ofReal_sub, norm_real, Real.norm_eq_abs] using hl)
      ht
    have hsq : Real.sqrt (K * A p) ^ 2 = K * A p := Real.sq_sqrt (mul_nonneg hK.le (hA p).le)
    have hle := mul_le_mul_of_nonneg_left (hIA p) hK.le
    have hn := Real.sqrt_nonneg (K * A p)
    change ‖f p (t : ℂ)‖ ^ 2 ≤ K * I p at hh
    nlinarith only [hh, hsq, hle, hn, norm_nonneg (f p (t : ℂ))]
  -- Propagate each prime's interval bound to a common disk about zero.
  obtain ⟨ρ, N, hρ, hρR, hprop⟩ := exists_disk_power_bound
    (show 0 < r / 2 by linarith only [hr]) hM
    (show |c| + r / 2 < R by linarith only [hcr, hSR, hR, hr])
  let α : ℝ := (1 / 2 : ℝ) ^ (N + 2)
  let B : ℝ := M * (K ^ (1 / 2 : ℝ) / M) ^ ((1 / 2 : ℝ) ^ (N + 1))
  let b : Nat.Primes → ℝ := fun p => B * A p ^ α
  have hbnd (p : Nat.Primes) (z : ℂ) (hz : ‖z‖ ≤ ρ) : ‖f p z‖ ≤ b p := by
    have hh := hprop (f p) (Real.sqrt (K * A p)) (Real.sqrt_pos.mpr (mul_pos hK (hA p)))
      (hd p) (hb p) (hpeak p) z hz
    have he : M * (Real.sqrt (K * A p) / M) ^ ((1 / 2 : ℝ) ^ (N + 1)) = b p := by
      rw [Real.sqrt_eq_rpow, Real.mul_rpow hK.le (hA p).le]
      rw [show K ^ (1 / 2 : ℝ) * A p ^ (1 / 2 : ℝ) / M =
        (K ^ (1 / 2 : ℝ) / M) * A p ^ (1 / 2 : ℝ) by ring]
      rw [Real.mul_rpow (by positivity) (Real.rpow_nonneg (hA p).le _),
        ← Real.rpow_mul (hA p).le]
      have ha : (1 / 2 : ℝ) * (1 / 2 : ℝ) ^ (N + 1) = α := by
        dsimp only [α]
        simp only [pow_succ]
        ring
      rw [ha]
      exact (mul_assoc _ _ _).symm
    exact hh.trans_eq he
  -- Each square root divides the positive abscissa saving by four.
  let δ := 1 - σ₀
  have hδ : 0 < δ := by dsimp [δ]; linarith only [hσ₁]
  have hδhalf : δ < 1 / 2 := by dsimp [δ]; linarith only [hσ₀]
  let d := δ / (4 : ℝ) ^ (N + 2)
  have hdpos : 0 < d := by dsimp [d]; positivity
  have hdle : d ≤ δ := div_le_self hδ.le (one_le_pow₀ (by norm_num))
  have hsA := summable_prime_dyadic_rpow (fun p => (hA p).le) hδ
    (show Summable (fun p => A p * (p : ℝ) ^ (-(1 - δ))) by
      simpa only [δ, sub_sub_cancel] using hAs) (N + 2)
  have hbs : Summable (fun p => b p * (p : ℝ) ^ (-(1 - d))) := by
    simpa only [b, α, d, mul_assoc] using hsA.mul_left B
  exact ⟨ρ, 1 - d, b, hρ, hρR, by linarith only [hdle, hδhalf],
    by linarith only [hdpos], hbs, hbnd⟩

#print axioms exists_complex_normal_majorant

/-- Supremum of one prime-coordinate perturbation on a closed parameter disk. -/
def primeDiskDeviation (u : Nat.Primes → ℂ → ℂ) (ρ : ℝ) (p : Nat.Primes) : ℝ :=
  sSup ((fun z : ℂ => ‖u p z - 1‖) '' closedBall 0 ρ)

private theorem gaugeFibre_eq_trivial_of_prime_twist {x : GaugeTorus}
    (hx : ∀ p : Nat.Primes, twist x p = 1) {s : ℂ} (hs : 1 < s.re) :
    gaugeFibre x s = gaugeFibre 0 s := by
  have hv : (fun p : Nat.Primes => eulerVar s (twist x) p) =
      (fun p : Nat.Primes => eulerVar s (twist 0) p) := by
    funext p
    simp only [eulerVar, hx p, GaloisForLFunctions.ArithmeticCorrelationGeometry.twist_zero]
  have hr : (fun p : Nat.Primes => localRem s (twist x) p) =
      (fun p : Nat.Primes => localRem s (twist 0) p) := by
    funext p
    simp only [localRem, eulerVar, hx p, GaloisForLFunctions.ArithmeticCorrelationGeometry.twist_zero]
  rw [← exp_tsum_eq_gaugeFibre x hs, ← exp_tsum_eq_gaugeFibre 0 hs,
    hullRem, hullRem, hv, hr]

/-- Unit prime coordinates fix the initial residue even when unused gauge coordinates vary. -/
theorem regularized_prime_normalized_residue {x : ℝ → GaugeTorus}
    {u : Nat.Primes → ℂ → ℂ} {U : ℂ × ℂ → ℂ} {R : ℝ}
    (hR : 0 < R) (hu0 : ∀ p, u p 0 = 1)
    (hphase0 : ∀ p, u p 0 = twist (x 0) p)
    (hU : ContinuousAt U (0, 1))
    (hagree : ∀ σ : ℝ, 1 < σ → σ < 1 + R →
      U (0, (σ : ℂ)) = ((σ : ℂ) - 1) * gaugeFibre (x 0) (σ : ℂ)) :
    U (0, 1) = 1 := by
  have htw (p : Nat.Primes) : twist (x 0) p = 1 := by rw [← hphase0 p, hu0 p]
  apply regularized_gauge_initial_residue (x := fun _ => 0) hR rfl hU
  intro σ hσ hσR
  rw [hagree σ hσ hσR, gaugeFibre_eq_trivial_of_prime_twist htw hσ]

/-- Joint pole regularity forces normal prime summability on a complex parameter disk below one. -/
theorem joint_gauge_complex_normal_summability {x : ℝ → GaugeTorus}
    {u : Nat.Primes → ℂ → ℂ} {U : ℂ × ℂ → ℂ} {R M : ℝ}
    (hR : 0 < R) (hu0 : ∀ p, u p 0 = 1)
    (hu : ∀ p, DifferentiableOn ℂ (u p) (ball 0 R))
    (hbd : ∀ p z, z ∈ ball 0 R → ‖u p z‖ ≤ M)
    (hphase : ∀ t : ℝ, |t| < R → ∀ p, u p (t : ℂ) = twist (x t) p)
    (hU : AnalyticAt ℂ U (0, 1))
    (hagree : ∀ t : ℝ, |t| < R → ∀ s ∈ ball (1 : ℂ) R, 1 < s.re →
      U ((t : ℂ), s) = (s - 1) * gaugeFibre (x t) s) :
    ∃ ρ σ : ℝ, 0 < ρ ∧ ρ < R ∧ 1 / 2 < σ ∧ σ < 1 ∧
      Summable (fun p => primeDiskDeviation u ρ p * (p : ℝ) ^ (-σ)) := by
  have hphase0 (p : Nat.Primes) : u p 0 = twist (x 0) p := by
    simpa only [Complex.ofReal_zero] using hphase 0 (by simpa only [abs_zero] using hR) p
  have hUone : U (0, 1) = 1 :=
    regularized_prime_normalized_residue hR hu0 hphase0 hU.continuousAt
    (fun σ hσ hσR => hagree 0 (by simpa only [abs_zero] using hR) (σ : ℂ)
      (by
        rw [mem_ball, dist_eq_norm, ← ofReal_one, ← ofReal_sub, norm_real,
          Real.norm_eq_abs, abs_of_pos (by linarith only [hσ] : 0 < σ - 1)]
        linarith only [hσR]) hσ)
  have hUne : U (0, 1) ≠ 0 := by rw [hUone]; exact one_ne_zero
  obtain ⟨r, hr, hr₂, hs⟩ := joint_pole_common_absolute_summability hR hU hUne hagree
  have hσ₀ : 1 / 2 < 1 - r / 8 := by linarith only [hr₂]
  have hσ₁ : 1 - r / 8 < 1 := by linarith only [hr]
  obtain ⟨ρ, σ, b, hρ, hρR, hσ, hσone, hbs, hb⟩ := exists_complex_normal_majorant
    (f := fun p z => u p z - 1) hR
    (show 0 < |M| + 1 by positivity) (lt_min hr hR) hσ₀ hσ₁
    (fun p => (hu p).sub_const 1)
    (fun p z hz => (norm_sub_le (u p z) 1).trans (by
      rw [norm_one]
      linarith only [hbd p z hz, le_abs_self M]))
    (fun t ht => by
      have htr := ht.trans_le (min_le_left r R)
      have htR := ht.trans_le (min_le_right r R)
      simpa only [hphase t htR] using hs t htr)
  refine ⟨ρ, σ, hρ, hρR, hσ, hσone, ?_⟩
  have hsup (p : Nat.Primes) : 0 ≤ primeDiskDeviation u ρ p ∧ primeDiskDeviation u ρ p ≤ b p := by
    have hzero : (0 : ℂ) ∈ closedBall 0 ρ := mem_closedBall_self hρ.le
    have hne : ((fun z : ℂ => ‖u p z - 1‖) '' closedBall 0 ρ).Nonempty :=
      ⟨_, ⟨0, hzero, rfl⟩⟩
    have hupper : ∀ v ∈ ((fun z : ℂ => ‖u p z - 1‖) '' closedBall 0 ρ), v ≤ b p := by
      rintro v ⟨z, hz, rfl⟩
      exact hb p z (by simpa only [mem_closedBall, dist_zero_right] using hz)
    have hbounded : BddAbove ((fun z : ℂ => ‖u p z - 1‖) '' closedBall 0 ρ) := ⟨b p, hupper⟩
    exact ⟨(norm_nonneg (u p 0 - 1)).trans (le_csSup hbounded ⟨0, hzero, rfl⟩),
      csSup_le hne hupper⟩
  apply hbs.of_nonneg_of_le (fun p => mul_nonneg (hsup p).1 (by positivity))
  exact fun p => mul_le_mul_of_nonneg_right (hsup p).2 (by positivity)

#print axioms joint_gauge_complex_normal_summability

end GaloisForLFunctions.ArithmeticWeightTheory.GaugeDeformations
