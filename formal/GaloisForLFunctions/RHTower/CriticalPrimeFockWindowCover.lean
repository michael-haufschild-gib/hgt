import GaloisForLFunctions.RHTower.PolynomialFockAdaptedBregman
import GaloisForLFunctions.RHTower.CriticalPrimeFockWindowPhaseTransition
import GaloisForLFunctions.RHTower.PrimeLogPowZetaAbelPole

/-!
# Critical-prime cover at the polynomial Fock tangent scale

The exact tangent-Gaussian disk at a positive real center is no wider than the polynomial Fock
critical radius.  After recentering at the real part of a point inside that disk, a fixed factor
`2 ^ (m / 2 - 1)` suffices.  This turns overlap sums of prime-centered tangent disks into the
second-order Mertens mass of one logarithmic prime window.

The same module proves the scaled-window phase law needed downstream: fixed multiples of the
critical radius have bounded mass for `m ≥ 4`, and vanishing mass for `m > 4`.
-/

open Filter Topology

namespace RHTower

noncomputable section

/-- Fixed dilation needed when a tangent disk is recentered at the real part of one of its points. -/
def criticalPrimeFockCoverFactor (m : ℝ) : ℝ :=
  2 ^ (m / 2 - 1)

theorem criticalPrimeFockCoverFactor_pos (m : ℝ) :
    0 < criticalPrimeFockCoverFactor m :=
  Real.rpow_pos_of_pos (by norm_num) _

/-- The exact tangent-Gaussian radius is bounded by the polynomial critical radius. -/
theorem polynomialFockTangentRadius_le_criticalPrimeFockRadius
    {m x : ℝ} (hm : 4 ≤ m) (hx : 1 ≤ x) :
    polynomialFockTangentRadius m x ≤ criticalPrimeFockRadius m x := by
  have hm0 : 0 < m := by linarith
  have hx0 : 0 < x := lt_of_lt_of_le zero_lt_one hx
  have hA0 : 0 < 1 + x ^ 2 := by positivity
  have ha : 0 ≤ m / 2 - 1 := by linarith
  have hbase : x ^ 2 ≤ 1 + x ^ 2 := by linarith
  have hpow : (x ^ 2) ^ (m / 2 - 1) ≤
      (1 + x ^ 2) ^ (m / 2 - 1) :=
    Real.rpow_le_rpow (sq_nonneg x) hbase ha
  have hxpow : (x ^ 2) ^ (m / 2 - 1) = x ^ (m - 2) := by
    rw [show x ^ 2 = x ^ (2 : ℝ) by norm_num [Real.rpow_two],
      ← Real.rpow_mul hx0.le]
    congr 1
    ring
  have hden : x ^ (m - 2) ≤ m * (1 + x ^ 2) ^ (m / 2 - 1) := by
    rw [← hxpow]
    calc
      (x ^ 2) ^ (m / 2 - 1) ≤ (1 + x ^ 2) ^ (m / 2 - 1) := hpow
      _ ≤ m * (1 + x ^ 2) ^ (m / 2 - 1) := by
        have hp : 0 ≤ (1 + x ^ 2) ^ (m / 2 - 1) := Real.rpow_nonneg hA0.le _
        nlinarith
  have hsqrt : Real.sqrt (x ^ (m - 2)) ≤
      Real.sqrt (m * (1 + x ^ 2) ^ (m / 2 - 1)) :=
    Real.sqrt_le_sqrt hden
  have hsqrtPos : 0 < Real.sqrt (x ^ (m - 2)) := by positivity
  have hinv : (Real.sqrt (m * (1 + x ^ 2) ^ (m / 2 - 1)))⁻¹ ≤
      (Real.sqrt (x ^ (m - 2)))⁻¹ := by
    exact (inv_le_inv₀ (a := Real.sqrt (m * (1 + x ^ 2) ^ (m / 2 - 1)))
      (b := Real.sqrt (x ^ (m - 2))) (by positivity) hsqrtPos).2 hsqrt
  rw [polynomialFockTangentRadius]
  calc
    (Real.sqrt (m * (1 + x ^ 2) ^ (m / 2 - 1)))⁻¹ ≤
        (Real.sqrt (x ^ (m - 2)))⁻¹ := hinv
    _ = criticalPrimeFockRadius m x := by
      rw [criticalPrimeFockRadius_eq_rpow hx0.le]
      rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hx0.le, ← Real.rpow_neg hx0.le]
      congr 1
      ring

/-- Nearby positive centers have critical radii comparable by the fixed cover factor. -/
theorem criticalPrimeFockRadius_le_coverFactor_mul
    {m x y : ℝ} (hm : 4 ≤ m) (hy : 2 ≤ y) (hxy : |x - y| < 1) :
    criticalPrimeFockRadius m x ≤
      criticalPrimeFockCoverFactor m * criticalPrimeFockRadius m y := by
  have hy0 : 0 < y := by linarith
  have hxhalf : y / 2 ≤ x := by
    rw [abs_lt] at hxy
    linarith
  have hyhalf0 : 0 < y / 2 := by positivity
  have he : 1 - m / 2 ≤ 0 := by linarith
  rw [criticalPrimeFockRadius_eq_rpow (by linarith : 0 ≤ x),
    criticalPrimeFockRadius_eq_rpow hy0.le]
  calc
    x ^ (1 - m / 2) ≤ (y / 2) ^ (1 - m / 2) :=
      Real.rpow_le_rpow_of_nonpos hyhalf0 hxhalf he
    _ = criticalPrimeFockCoverFactor m * y ^ (1 - m / 2) := by
      rw [div_eq_mul_inv, Real.mul_rpow hy0.le (by norm_num : (0 : ℝ) ≤ 2⁻¹),
        Real.inv_rpow (by norm_num : (0 : ℝ) ≤ 2)]
      dsimp [criticalPrimeFockCoverFactor]
      rw [← Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2)]
      ring_nf

/-- Membership in a tangent disk forces its center into one critical window about the point's real
part. -/
theorem abs_center_sub_re_lt_coverFactor_mul_criticalPrimeFockRadius
    {m x : ℝ} (hm : 4 ≤ m) (hx : 1 ≤ x) {z : ℂ}
    (hzre : 2 ≤ z.re)
    (hz : ‖z - (x : ℂ)‖ < polynomialFockTangentRadius m x) :
    |x - z.re| <
      criticalPrimeFockCoverFactor m * criticalPrimeFockRadius m z.re := by
  have habs : |x - z.re| ≤ ‖z - (x : ℂ)‖ := by
    have h := Complex.abs_re_le_norm (z - (x : ℂ))
    simpa [abs_sub_comm] using h
  have htanCrit := polynomialFockTangentRadius_le_criticalPrimeFockRadius hm hx
  have hcritScale := criticalPrimeFockRadius_le_coverFactor_mul hm hzre (by
    calc
      |x - z.re| ≤ ‖z - (x : ℂ)‖ := habs
      _ < polynomialFockTangentRadius m x := hz
      _ ≤ 1 / 2 := polynomialFockTangentRadius_le_half hm
      _ < 1 := by norm_num)
  exact lt_of_le_of_lt habs (lt_of_lt_of_le hz (htanCrit.trans hcritScale))

/-- The critical polynomial Fock radius vanishes for every degree above two. -/
theorem criticalPrimeFockRadius_tendsto_zero
    {m : ℝ} (hm : 2 < m) :
    Tendsto (criticalPrimeFockRadius m) atTop (nhds 0) := by
  have h := tendsto_rpow_neg_atTop (by linarith : 0 < m / 2 - 1)
  apply h.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
  rw [criticalPrimeFockRadius_eq_rpow hx.le]
  congr 1
  ring

/-- Uniform Mertens asymptotics remain valid at any fixed positive multiple of the critical
radius. -/
theorem tendsto_primeLogWindowMass_scaledCritical_sub_main
    {m D : ℝ} (hm : 2 < m) (hD : 0 < D) :
    Tendsto (fun x : ℝ =>
      primeLogWindowMass x (D * criticalPrimeFockRadius m x) -
        2 * x * (D * criticalPrimeFockRadius m x)) atTop (nhds 0) := by
  have hrzero : Tendsto (fun x => D * criticalPrimeFockRadius m x) atTop (nhds 0) := by
    simpa using (criticalPrimeFockRadius_tendsto_zero hm).const_mul D
  have hrsmall : ∀ᶠ x : ℝ in atTop,
      D * criticalPrimeFockRadius m x < 1 :=
    hrzero.eventually_lt_const zero_lt_one
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨X, hX⟩ := primeLogWindowMass_uniform_asymptotic hε
  obtain ⟨N, hN⟩ := eventually_atTop.1 hrsmall
  refine ⟨max (max X N) 1, fun x hx => ?_⟩
  have hxXN : max X N ≤ x := le_trans (le_max_left _ _) hx
  have hxX : X ≤ x := le_trans (le_max_left _ _) hxXN
  have hxN : N ≤ x := le_trans (le_max_right _ _) hxXN
  have hx1 : (1 : ℝ) ≤ x := le_trans (le_max_right _ _) hx
  have hrpos : 0 < D * criticalPrimeFockRadius m x := by
    exact mul_pos hD (criticalPrimeFockRadius_pos (by linarith))
  have herr := hX x hxX _ hrpos (hN x hxN).le
  simpa [Real.dist_eq] using herr

/-- Every fixed dilation of the critical window has vanishing prime mass above quartic degree. -/
theorem tendsto_primeLogWindowMass_scaledCritical_zero
    {m D : ℝ} (hm : 4 < m) (hD : 0 < D) :
    Tendsto (fun x : ℝ =>
      primeLogWindowMass x (D * criticalPrimeFockRadius m x)) atTop (nhds 0) := by
  have herr := tendsto_primeLogWindowMass_scaledCritical_sub_main
    (m := m) (D := D) (by linarith) hD
  have hmain := (tendsto_criticalPrimeFockWindowMain_zero hm).const_mul D
  have hsum := herr.add hmain
  convert hsum using 1 <;> simp [criticalPrimeFockWindowMain] <;> ring

/-- Every fixed dilation of the quartic critical window has limiting mass `2D`. -/
theorem tendsto_primeLogWindowMass_scaledCritical_four
    {D : ℝ} (hD : 0 < D) :
    Tendsto (fun x : ℝ =>
      primeLogWindowMass x (D * criticalPrimeFockRadius 4 x)) atTop (nhds (2 * D)) := by
  have herr := tendsto_primeLogWindowMass_scaledCritical_sub_main
    (m := (4 : ℝ)) (D := D) (by norm_num) hD
  have hmain := tendsto_criticalPrimeFockWindowMain_four.const_mul D
  have hsum := herr.add hmain
  convert hsum using 1 <;> simp [criticalPrimeFockWindowMain] <;> ring

/-- A convergent scaled critical-window mass is uniformly bounded on the ray `x ≥ 2`. -/
theorem exists_primeLogWindowMass_scaledCritical_bound
    {m D L : ℝ} (hm : 2 ≤ m) (hD : 0 < D)
    (hlim : Tendsto (fun x : ℝ =>
      primeLogWindowMass x (D * criticalPrimeFockRadius m x)) atTop (nhds L)) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ x : ℝ, 2 ≤ x →
      primeLogWindowMass x (D * criticalPrimeFockRadius m x) ≤ B := by
  have htail : ∀ᶠ x : ℝ in atTop,
      primeLogWindowMass x (D * criticalPrimeFockRadius m x) < L + 1 := by
    have hdist := hlim.eventually (Metric.ball_mem_nhds L zero_lt_one)
    filter_upwards [hdist] with x hx
    rw [Real.dist_eq, abs_lt] at hx
    linarith
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.1 htail
  let N : ℝ := max 2 N₀
  let H : ℝ := primeLogPowSum 2 (Real.exp (N + D))
  refine ⟨max H (L + 1), le_trans (primeLogPowSum_nonneg 2 _) (le_max_left _ _),
    fun x hx => ?_⟩
  by_cases hxN : N ≤ x
  · exact (hN₀ x (le_trans (le_max_right _ _) hxN)).le.trans (le_max_right _ _)
  · have hxlt : x < N := lt_of_not_ge hxN
    have hrle : criticalPrimeFockRadius m x ≤ 1 :=
      criticalPrimeFockRadius_le_one hm (by linarith)
    have hrleD : D * criticalPrimeFockRadius m x ≤ D := by
      nlinarith [criticalPrimeFockRadius_pos (m := m) (by linarith : 0 < x)]
    have hupper : Real.exp (x + D * criticalPrimeFockRadius m x) ≤
        Real.exp (N + D) := Real.exp_le_exp.mpr (by linarith)
    have hmass : primeLogWindowMass x (D * criticalPrimeFockRadius m x) ≤ H := by
      rw [primeLogWindowMass]
      have hlow := primeLogPowSum_nonneg 2
        (Real.exp (x - D * criticalPrimeFockRadius m x))
      have hu := primeLogPowSum_mono 2 hupper
      dsimp [H]
      linarith
    exact hmass.trans (le_max_left _ _)

/-- Prime-window overlap mass is uniformly bounded at the tangent-disk cover scale for `m ≥ 4`. -/
theorem exists_primeLogWindowMass_coverFactor_bound
    {m : ℝ} (hm : 4 ≤ m) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ x : ℝ, 2 ≤ x →
      primeLogWindowMass x
        (criticalPrimeFockCoverFactor m * criticalPrimeFockRadius m x) ≤ B := by
  have hD := criticalPrimeFockCoverFactor_pos m
  rcases eq_or_lt_of_le hm with rfl | hm4
  · exact exists_primeLogWindowMass_scaledCritical_bound (by norm_num) hD
      (tendsto_primeLogWindowMass_scaledCritical_four hD)
  · exact exists_primeLogWindowMass_scaledCritical_bound (by linarith) hD
      (tendsto_primeLogWindowMass_scaledCritical_zero hm4 hD)

/-- Prime sampling weight is the degree-two prime log-power weight. -/
theorem criticalPrimeSamplingWeight_eq_primeLogPowWeight
    (p : Nat.Primes) :
    criticalPrimeSamplingWeight p = primeLogPowWeight 2 (p : ℕ) := by
  rw [criticalPrimeSamplingWeight, primeLogPowWeight, if_pos p.2]

/-- Strict logarithmic-window membership implies membership in the concrete finite prime window. -/
theorem mem_primeLogWindowFinset_of_abs_log_sub_lt
    {x r : ℝ} {n : ℕ} (hn0 : n ≠ 0) (h : |Real.log n - x| < r) :
    n ∈ Finset.Ioc ⌊Real.exp (x - r)⌋₊ ⌊Real.exp (x + r)⌋₊ := by
  rw [abs_lt] at h
  have hnposR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hn0
  have hl : Real.exp (x - r) < (n : ℝ) := by
    calc
      Real.exp (x - r) < Real.exp (Real.log (n : ℝ)) :=
        Real.exp_lt_exp.mpr (by linarith)
      _ = (n : ℝ) := Real.exp_log hnposR
  have hu : (n : ℝ) ≤ Real.exp (x + r) := by
    calc
      (n : ℝ) = Real.exp (Real.log (n : ℝ)) := (Real.exp_log hnposR).symm
      _ ≤ Real.exp (x + r) := (Real.exp_lt_exp.mpr (by linarith)).le
  exact Finset.mem_Ioc.mpr ⟨(Nat.floor_lt' hn0).mpr hl,
    (Nat.le_floor_iff (Real.exp_nonneg _)).mpr hu⟩

/-- Any finite family of primes strictly inside a logarithmic window has total sampling weight at
most the full prime-window mass. -/
theorem sum_criticalPrimeSamplingWeight_le_primeLogWindowMass
    (P : Finset Nat.Primes) {x r : ℝ} (hr : 0 ≤ r)
    (hP : ∀ p ∈ P, |Real.log (p : ℝ) - x| < r) :
    ∑ p ∈ P, criticalPrimeSamplingWeight p ≤ primeLogWindowMass x r := by
  classical
  let e : Nat.Primes ↪ ℕ := ⟨fun p => (p : ℕ), Subtype.val_injective⟩
  let Q : Finset ℕ := P.map e
  have hQsub : Q ⊆ Finset.Ioc ⌊Real.exp (x - r)⌋₊ ⌊Real.exp (x + r)⌋₊ := by
    intro n hn
    dsimp [Q] at hn
    obtain ⟨p, hp, hpn⟩ := Finset.mem_map.mp hn
    subst n
    exact mem_primeLogWindowFinset_of_abs_log_sub_lt
      (Nat.Prime.ne_zero p.2) (hP p hp)
  rw [primeLogWindowMass_eq_sum x hr]
  have hsumQ :
      ∑ p ∈ P, criticalPrimeSamplingWeight p = ∑ n ∈ Q, primeLogPowWeight 2 n := by
    have hmap := Finset.sum_map P e (primeLogPowWeight 2)
    have hmapQ : ∑ n ∈ Q, primeLogPowWeight 2 n =
        ∑ p ∈ P, primeLogPowWeight 2 (p : ℕ) := by
      simpa [Q, e] using hmap
    calc
      ∑ p ∈ P, criticalPrimeSamplingWeight p =
          ∑ p ∈ P, primeLogPowWeight 2 (p : ℕ) := by
        apply Finset.sum_congr rfl
        intro p hp
        exact criticalPrimeSamplingWeight_eq_primeLogPowWeight p
      _ = ∑ n ∈ Q, primeLogPowWeight 2 n := hmapQ.symm
  rw [hsumQ]
  exact Finset.sum_le_sum_of_subset_of_nonneg hQsub
    (fun i hi hnot => primeLogPowWeight_two_nonneg i)

end

end RHTower
