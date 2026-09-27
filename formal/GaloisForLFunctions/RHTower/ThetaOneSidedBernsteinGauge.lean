import GaloisForLFunctions.RHTower.ThetaPrimeDeletionBernsteinPureRay


/-!
# One-sided integer-shift theta gauges: all-sieve Bernstein cone and a two-anchor countermodel

For coefficients `c` with `∑ |c_m| √m < ∞` the one-sided gauge `g_c = ∑_{m ≥ 1} c_m k(· + log m)`
of the completed theta source is the weighted Gaussian atom sum with weights
`R_N = ∑_{m ∣ N} c_m √m`, and its finite-prime deletion `D_S g_c` is the weighted atom sum with
weights `R_{S,N} = ∑_{m ∣ N, (N/m, S) = 1} c_m √m`.

* **All-sieve classification.**  Every deleted flux `b_{D_S g_c}` is completely monotone iff all
  `c_m ≥ 0`; with both anchors (ordinary mass and critical half-charge of `k`) this forces `g_c = k`.
* **Countermodel.**  For `1/2 < α < 1/√2`, `κ = 2 - √2`, `d = √2 - 1`, the gauge
  `g_α = (1-dα) k + α k(· + log 2) - κα k(· + log 4)` has a completely monotone flux with rate
  weights `1-dα`, `1+α`, `1-d²α`, both anchors of `k`, is positive on `x ≥ 0`, is not even, and its
  Mellin transform `M_α(w) XiC(iw)` vanishes at some `σ + iπ/log 2` with `0 < σ < 1/2`; its first
  prime-deleted flux is not completely monotone.
-/

open MeasureTheory Set Filter Topology
open GaloisForLFunctions.HTGeometry

namespace RHTower

/-- **Divisor regrouping.**  A summable double series over `ℕ × ℕ` vanishing on the axes regroups
along the fibres of `(m,n) ↦ m n` into finite divisor sums. -/
theorem hasSum_divisorsAntidiagonal_regroup {f : ℕ × ℕ → ℝ} (hf : Summable f)
    (h0 : ∀ p : ℕ × ℕ, (p.1 = 0 ∨ p.2 = 0) → f p = 0) :
    HasSum (fun N : ℕ => ∑ p ∈ N.divisorsAntidiagonal, f p) (∑' p, f p) := by
  have h := hf.hasSum.tsum_fiberwise (fun p : ℕ × ℕ => p.1 * p.2)
  refine h.congr_fun (fun N => ?_)
  rw [tsum_subtype]
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · simp only [Nat.divisorsAntidiagonal_zero, Finset.sum_empty]
    have hz : ∀ p : ℕ × ℕ, ((fun p : ℕ × ℕ => p.1 * p.2) ⁻¹' {0}).indicator f p = 0 := by
      intro p
      by_cases hp : p ∈ (fun p : ℕ × ℕ => p.1 * p.2) ⁻¹' {0}
      · rw [Set.indicator_of_mem hp]
        exact h0 p (mul_eq_zero.mp hp)
      · rw [Set.indicator_of_notMem hp]
    simp only [hz, tsum_zero]
  · rw [tsum_eq_sum (s := N.divisorsAntidiagonal)]
    · apply Finset.sum_congr rfl
      intro p hp
      rw [Set.indicator_of_mem]
      simp only [mem_preimage, mem_singleton_iff]
      exact (Nat.mem_divisorsAntidiagonal.mp hp).1
    · intro p hp
      rw [Set.indicator_of_notMem]
      simp only [mem_preimage, mem_singleton_iff]
      intro h
      exact hp (Nat.mem_divisorsAntidiagonal.mpr ⟨h, hN.ne'⟩)


/-! ## Weighted Gaussian atom sums -/

/-- The weighted atom sum `∑ R_n a_n`. -/
noncomputable def thetaWeightedAtomSum (R : ℕ → ℝ) (x : ℝ) : ℝ :=
  ∑' n, R n * thetaCuspSourceTerm x n

theorem summable_weightedAtom {R : ℕ → ℝ} {B : ℝ} (hR : ∀ n, |R n| ≤ B) (x : ℝ) :
    Summable fun n => R n * thetaCuspSourceTerm x n :=
  Summable.of_norm_bounded ((summable_thetaCuspSourceTerm x).abs.mul_left B) (fun n => by
    rw [Real.norm_eq_abs, abs_mul]
    exact mul_le_mul_of_nonneg_right (hR n) (abs_nonneg _))

theorem continuous_thetaWeightedAtomSum {R : ℕ → ℝ} {B : ℝ} (hR : ∀ n, |R n| ≤ B) :
    Continuous (thetaWeightedAtomSum R) := by
  rw [continuous_iff_continuousAt]
  intro x
  set T := |x| + 1
  have hon : ContinuousOn (thetaWeightedAtomSum R) (Set.Icc (-T) T) := by
    apply continuousOn_tsum (u := fun n => B * thetaCuspSourceMajorant T n)
    · intro n
      exact (continuous_const.mul (continuous_thetaCuspSourceTerm n)).continuousOn
    · exact (summable_thetaCuspSourceMajorant T).mul_left B
    · intro n y hy
      rw [Real.norm_eq_abs, abs_mul]
      exact mul_le_mul (hR n) (abs_thetaCuspSourceTerm_le_majorant hy n) (abs_nonneg _)
        ((abs_nonneg _).trans (hR n))
  apply hon.continuousAt
  apply Icc_mem_nhds
  · simp only [T]; linarith [neg_abs_le x]
  · simp only [T]; linarith [le_abs_self x]

/-- Tail integral of a weighted atom sum with bounded weights. -/
theorem setIntegral_Ici_exp_half_mul_thetaWeightedAtomSum {R : ℕ → ℝ} {B : ℝ}
    (hR : ∀ n, |R n| ≤ B) (X : ℝ) :
    IntegrableOn (fun x => Real.exp (x / 2) * thetaWeightedAtomSum R x) (Ici X) ∧
      (∫ x in Ici X, Real.exp (x / 2) * thetaWeightedAtomSum R x) =
        ∑' n : ℕ, R n * thetaAtomFluxPotential n X := by
  set F : ℕ → ℝ → ℝ := fun n x => Real.exp (x / 2) * (R n * thetaCuspSourceTerm x n)
  have hF : ∀ n, Integrable (F n) (volume.restrict (Ici X)) := fun n => by
    have h := ((integrable_exp_half_mul_thetaCuspSourceTerm' n).integrableOn (s := Ici X)).const_mul
      (R n)
    refine Integrable.congr h (Eventually.of_forall fun x => ?_)
    simp only [F]; ring
  have hIF : ∀ n, (∫ x in Ici X, F n x) = R n * thetaAtomFluxPotential n X := by
    intro n
    simp only [F]
    rw [← setIntegral_Ici_exp_half_mul_thetaCuspSourceTerm n X, ← integral_const_mul]
    congr 1; funext x; ring
  obtain ⟨N0, hN0⟩ : ∃ N0 : ℕ, Real.exp (-X) ≤ N0 := exists_nat_ge _
  have hB : 0 ≤ B := (abs_nonneg _).trans (hR 0)
  have hnorm : ∀ᶠ n : ℕ in cofinite, ‖∫ x in Ici X, ‖F n x‖‖ ≤ B * thetaAtomFluxPotential n X := by
    rw [Nat.cofinite_eq_atTop]
    filter_upwards [eventually_ge_atTop N0] with n hn
    have hpos : ∀ x ∈ Ici X, 0 ≤ thetaCuspSourceTerm x n := by
      intro x hx
      apply thetaCuspSourceTerm_nonneg_of_one_le
      have hn' : Real.exp (-X) ≤ n := hN0.trans (by exact_mod_cast hn)
      have hex : Real.exp X ≤ Real.exp x := Real.exp_le_exp.mpr hx
      have h1 : Real.exp (-X) * Real.exp X = 1 := by rw [← Real.exp_add]; simp
      calc (1 : ℝ) = Real.exp (-X) * Real.exp X := h1.symm
        _ ≤ n * Real.exp x := mul_le_mul hn' hex (Real.exp_pos _).le (Nat.cast_nonneg n)
    have heq : (∫ x in Ici X, ‖F n x‖) = |R n| * thetaAtomFluxPotential n X := by
      rw [← setIntegral_Ici_exp_half_mul_thetaCuspSourceTerm n X, ← integral_const_mul]
      apply setIntegral_congr_fun measurableSet_Ici
      intro x hx
      simp only [F, Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _),
        abs_of_nonneg (hpos x hx)]
      ring
    rw [Real.norm_of_nonneg (integral_nonneg fun x => norm_nonneg _), heq]
    exact mul_le_mul_of_nonneg_right (hR n) (thetaAtomFluxPotential_nonneg n X)
  have hsum : Summable fun n => ∫ x in Ici X, ‖F n x‖ :=
    Summable.of_norm_bounded_eventually ((summable_thetaAtomFluxPotential X).mul_left B) hnorm
  have htsum : ∀ x, (∑' n, F n x) = Real.exp (x / 2) * thetaWeightedAtomSum R x := by
    intro x
    simp only [F, thetaWeightedAtomSum]
    rw [tsum_mul_left]
  constructor
  · have h := GaloisForLFunctions.HTGeometry.integrable_tsum_of_summable_integral_norm hF hsum
    exact h.congr (Eventually.of_forall fun x => htsum x)
  · have h := integral_tsum_of_summable_integral_norm hF hsum
    rw [← tsum_congr hIF, h]
    exact integral_congr_ae (Eventually.of_forall fun x => (htsum x).symm)

theorem thetaFluxSource_thetaWeightedAtomSum {R : ℕ → ℝ} {B : ℝ} (hR : ∀ n, |R n| ≤ B) :
    ThetaFluxSource (thetaWeightedAtomSum R) :=
  ⟨continuous_thetaWeightedAtomSum hR, fun X =>
    (setIntegral_Ici_exp_half_mul_thetaWeightedAtomSum hR X).1.mono_set Ioi_subset_Ici_self⟩

/-- **Flux of a weighted atom sum.**  `b(t) = ∑ R_n 2π n² e^{-π n² t}`. -/
theorem thetaNormalizedFlux_thetaWeightedAtomSum {R : ℕ → ℝ} {B : ℝ} (hR : ∀ n, |R n| ≤ B)
    {t : ℝ} (ht : 0 < t) :
    thetaNormalizedFlux (thetaWeightedAtomSum R) t =
      ∑' n, R n * thetaGaussWeight n * Real.exp (-thetaGaussRate n * t) := by
  rw [thetaNormalizedFlux, (setIntegral_Ici_exp_half_mul_thetaWeightedAtomSum hR _).2,
    ← tsum_mul_left]
  apply tsum_congr
  intro n
  rw [thetaAtomFluxPotential]
  have h3 : Real.exp (3 * (Real.log t / 2)) = t ^ (3 / 2 : ℝ) := by
    rw [Real.rpow_def_of_pos ht]; ring_nf
  have h2 : Real.exp (2 * (Real.log t / 2)) = t := by
    rw [show 2 * (Real.log t / 2) = Real.log t by ring, Real.exp_log ht]
  rw [h3, h2]
  have ht32 : t ^ (-(3 / 2 : ℝ)) * t ^ (3 / 2 : ℝ) = 1 := by
    rw [← Real.rpow_add ht]; simp
  unfold thetaGaussWeight thetaGaussRate
  have e : t ^ (-(3 / 2 : ℝ)) * (R n * (2 * Real.pi * (n : ℝ) ^ 2 * t ^ (3 / 2 : ℝ) *
      Real.exp (-Real.pi * (n : ℝ) ^ 2 * t))) = (t ^ (-(3 / 2 : ℝ)) * t ^ (3 / 2 : ℝ)) *
      (R n * (2 * Real.pi * (n : ℝ) ^ 2) * Real.exp (-(Real.pi * (n : ℝ) ^ 2) * t)) := by
    ring_nf
  rw [e, ht32, one_mul]

/-- A weighted atom sum with nonnegative weights and positive first weight is positive on the
positive ray. -/
theorem thetaWeightedAtomSum_pos_of_nonneg {R : ℕ → ℝ} {B : ℝ} (hR : ∀ n, |R n| ≤ B)
    (hR0 : ∀ n, 0 ≤ R n) (hR1 : 0 < R 1) {x : ℝ} (hx : 0 ≤ x) :
    0 < thetaWeightedAtomSum R x := by
  have hs := summable_weightedAtom hR x
  have hnn : ∀ n, 0 ≤ R n * thetaCuspSourceTerm x n := fun n =>
    mul_nonneg (hR0 n) (thetaCuspSourceTerm_nonneg_of_nonneg hx n)
  have ha1 : 0 < thetaCuspSourceTerm x 1 := by
    unfold thetaCuspSourceTerm
    apply mul_pos (Real.exp_pos _)
    apply thetaCuspSeed_pos
    have he : (1 : ℝ) ≤ Real.exp x := Real.one_le_exp hx
    have : (1 : ℝ) ≤ ((1 : ℕ) * Real.exp x) ^ 2 := by push_cast; nlinarith
    nlinarith [Real.pi_gt_three]
  exact lt_of_lt_of_le (mul_pos hR1 ha1) (hs.le_tsum 1 (fun n _ => hnn n))


/-! ## Integer-shift gauges as weighted atom sums -/

/-- Translation by `log m` rescales atoms: `a_n(x + log m) = √m a_{mn}(x)`. -/
theorem thetaCuspSourceTerm_add_log {m : ℕ} (hm : 0 < m) (x : ℝ) (n : ℕ) :
    thetaCuspSourceTerm (x + Real.log m) n = Real.sqrt m * thetaCuspSourceTerm x (m * n) := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  rw [← rpow_neg_half_mul_thetaCuspSourceTerm_add_log hm x n, ← mul_assoc,
    Real.sqrt_eq_rpow, ← Real.rpow_add hmR]
  norm_num

/-- Base atom sums translated by `log m`. -/
theorem thetaAtomSum_add_log (A : Set ℕ) {m : ℕ} (hm : 0 < m) (x : ℝ) :
    thetaAtomSum A (x + Real.log m) =
      Real.sqrt m * ∑' n, A.indicator (fun n => thetaCuspSourceTerm x (m * n)) n := by
  rw [thetaAtomSum, ← tsum_mul_left]
  apply tsum_congr
  intro n
  by_cases hn : n ∈ A
  · rw [Set.indicator_of_mem hn, Set.indicator_of_mem hn, thetaCuspSourceTerm_add_log hm]
  · rw [Set.indicator_of_notMem hn, Set.indicator_of_notMem hn, mul_zero]

/-- The weight `R_N = ∑_{m n = N, n ∈ A} c_m √m` of an integer-shift gauge over the base `A`. -/
noncomputable def thetaGaugeWeight (c : ℕ → ℝ) (A : Set ℕ) (N : ℕ) : ℝ :=
  ∑ p ∈ N.divisorsAntidiagonal, c p.1 * Real.sqrt p.1 * A.indicator 1 p.2

theorem abs_thetaGaugeWeight_le {c : ℕ → ℝ} (hc : Summable fun m => |c m| * Real.sqrt m)
    (A : Set ℕ) (N : ℕ) :
    |thetaGaugeWeight c A N| ≤ ∑' m, |c m| * Real.sqrt m := by
  unfold thetaGaugeWeight
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  have hle : ∀ p ∈ N.divisorsAntidiagonal, |c p.1 * Real.sqrt p.1 * A.indicator 1 p.2| ≤
      |c p.1| * Real.sqrt p.1 := by
    intro p _
    rw [abs_mul, abs_mul, abs_of_nonneg (Real.sqrt_nonneg _)]
    have : |A.indicator (1 : ℕ → ℝ) p.2| ≤ 1 := by
      by_cases h : p.2 ∈ A
      · simp [Set.indicator_of_mem h]
      · simp [Set.indicator_of_notMem h]
    exact mul_le_of_le_one_right (by positivity) this
  refine (Finset.sum_le_sum hle).trans ?_
  have hinj : Set.InjOn Prod.fst (N.divisorsAntidiagonal : Set (ℕ × ℕ)) := by
    intro p hp q hq h
    have hp' := Nat.mem_divisorsAntidiagonal.mp hp
    have hq' := Nat.mem_divisorsAntidiagonal.mp hq
    have h1 : p.1 ≠ 0 := by
      intro h0; rw [h0, zero_mul] at hp'; exact hp'.2 hp'.1.symm
    ext
    · exact h
    · have : p.1 * p.2 = q.1 * q.2 := hp'.1.trans hq'.1.symm
      rw [h] at this
      exact Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero (h ▸ h1)) this
  rw [← Finset.sum_image (f := fun m => |c m| * Real.sqrt m) hinj]
  exact hc.sum_le_tsum _ (fun m _ => by positivity)

/-- Gauge over a base atom set: `∑_m c_m (∑_{n ∈ A} a_n)(x + log m)`. -/
noncomputable def thetaBaseGauge (c : ℕ → ℝ) (A : Set ℕ) (x : ℝ) : ℝ :=
  ∑' m, c m * thetaAtomSum A (x + Real.log m)

/-- **Gauge regrouping.**  An integer-shift gauge over a base atom set is the weighted atom sum with
weights `thetaGaugeWeight c A`. -/
theorem thetaBaseGauge_eq_weightedAtomSum {c : ℕ → ℝ} (hc0 : c 0 = 0)
    (hc : Summable fun m => |c m| * Real.sqrt m) (A : Set ℕ) (x : ℝ) :
    thetaBaseGauge c A x = thetaWeightedAtomSum (thetaGaugeWeight c A) x ∧
      Summable fun m => c m * thetaAtomSum A (x + Real.log m) := by
  set F : ℕ × ℕ → ℝ := fun p => c p.1 * Real.sqrt p.1 * A.indicator 1 p.2 *
    thetaCuspSourceTerm x (p.1 * p.2)
  set G : ℕ × ℕ → ℝ := fun p => |c p.1| * Real.sqrt p.1 * |thetaCuspSourceTerm x (p.1 * p.2)|
  have ha := (summable_thetaCuspSourceTerm x).abs
  have hrow : ∀ m, Summable fun n => G (m, n) := by
    intro m
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · simp [G]
    · have hinj : Function.Injective (fun n : ℕ => m * n) := fun a b h =>
        Nat.eq_of_mul_eq_mul_left hm h
      exact (ha.comp_injective hinj).mul_left (|c m| * Real.sqrt m)
  have hrowle : ∀ m, (∑' n, G (m, n)) ≤ |c m| * Real.sqrt m * ∑' N, |thetaCuspSourceTerm x N| := by
    intro m
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · simp [G]
    · have hinj : Function.Injective (fun n : ℕ => m * n) := fun a b h =>
        Nat.eq_of_mul_eq_mul_left hm h
      simp only [G]
      rw [tsum_mul_left]
      exact mul_le_mul_of_nonneg_left
        (tsum_comp_le_tsum_of_inj ha (fun N => abs_nonneg _) hinj) (by positivity)
  have hG : Summable G := by
    rw [summable_prod_of_nonneg (fun p => by simp only [G, Pi.zero_apply]; positivity)]
    refine ⟨hrow, ?_⟩
    exact Summable.of_nonneg_of_le (fun m => tsum_nonneg fun n => by simp only [G]; positivity)
      hrowle (hc.mul_right _)
  have hF : Summable F := Summable.of_norm_bounded hG (fun p => by
    simp only [F, G, Real.norm_eq_abs, abs_mul, abs_of_nonneg (Real.sqrt_nonneg _)]
    have : |A.indicator (1 : ℕ → ℝ) p.2| ≤ 1 := by
      by_cases h : p.2 ∈ A
      · simp [Set.indicator_of_mem h]
      · simp [Set.indicator_of_notMem h]
    have h1 := mul_le_mul_of_nonneg_left this (by positivity : 0 ≤ |c p.1| * Real.sqrt p.1)
    nlinarith [abs_nonneg (thetaCuspSourceTerm x (p.1 * p.2))])
  have h0 : ∀ p : ℕ × ℕ, (p.1 = 0 ∨ p.2 = 0) → F p = 0 := by
    rintro ⟨m, n⟩ h
    have hmn : m * n = 0 := by
      rcases h with h | h
      · simp only at h; rw [h, zero_mul]
      · simp only at h; rw [h, mul_zero]
    simp only [F, hmn]
    simp [thetaCuspSourceTerm, thetaCuspSeed]
  have hreg := hasSum_divisorsAntidiagonal_regroup hF h0
  have hrowF : ∀ m, (∑' n, F (m, n)) = c m * thetaAtomSum A (x + Real.log m) := by
    intro m
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · simp [F, hc0]
    · rw [thetaAtomSum_add_log A hm x, ← mul_assoc, ← tsum_mul_left]
      apply tsum_congr
      intro n
      simp only [F]
      by_cases hn : n ∈ A
      · simp [Set.indicator_of_mem hn]
      · simp [Set.indicator_of_notMem hn]
  have hsumrows : Summable fun m => c m * thetaAtomSum A (x + Real.log m) := by
    have := hF.prod
    exact this.congr hrowF
  refine ⟨?_, hsumrows⟩
  rw [thetaBaseGauge, ← tsum_congr hrowF, ← hF.tsum_prod, ← hreg.tsum_eq, thetaWeightedAtomSum]
  apply tsum_congr
  intro N
  rw [thetaGaugeWeight, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro p hp
  simp only [F, (Nat.mem_divisorsAntidiagonal.mp hp).1]


/-- The one-sided integer-shift gauge `g_c = ∑_{m ≥ 1} c_m k(· + log m)`. -/
noncomputable def thetaIntegerShiftGauge (c : ℕ → ℝ) (x : ℝ) : ℝ :=
  ∑' m, c m * thetaCuspFullSource (x + Real.log m)

/-- The atom set coprime to a finite set of primes. -/
def thetaCoprimeLabels (S : Finset ℕ) : Set ℕ := {m | ∀ p ∈ S, ¬ p ∣ m}

theorem thetaIntegerShiftGauge_eq_baseGauge (c : ℕ → ℝ) :
    thetaIntegerShiftGauge c = thetaBaseGauge c Set.univ := by
  funext x
  simp [thetaIntegerShiftGauge, thetaBaseGauge, thetaAtomSum_univ]

theorem thetaPrimeDeletion_thetaCuspFullSource_eq_atomSum (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime) :
    thetaPrimeDeletion S thetaCuspFullSource = thetaAtomSum (thetaCoprimeLabels S) := by
  funext x
  rw [thetaPrimeDeletion_thetaCuspFullSource_eq_tsum S hS]
  rfl

/-- **Deleted gauge.**  `D_S g_c` is the gauge of `D_S k`, i.e. the gauge over the coprime base. -/
theorem thetaPrimeDeletion_thetaIntegerShiftGauge {c : ℕ → ℝ} (hc0 : c 0 = 0)
    (hc : Summable fun m => |c m| * Real.sqrt m) (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime) :
    thetaPrimeDeletion S (thetaIntegerShiftGauge c) =
      thetaBaseGauge c (thetaCoprimeLabels S) := by
  funext x
  have hsum : ∀ y, Summable fun m => c m * thetaCuspFullSource (y + Real.log m) := by
    intro y
    have := (thetaBaseGauge_eq_weightedAtomSum hc0 hc Set.univ y).2
    simpa [thetaAtomSum_univ] using this
  unfold thetaPrimeDeletion thetaIntegerShiftGauge thetaBaseGauge
  have hterm : ∀ T ∈ S.powerset,
      (-1 : ℝ) ^ T.card * ((((∏ p ∈ T, p : ℕ)) : ℝ) ^ (-(1 / 2 : ℝ)) *
        ∑' m, c m * thetaCuspFullSource (x + Real.log ((∏ p ∈ T, p : ℕ) : ℝ) + Real.log m)) =
      ∑' m, c m * ((-1 : ℝ) ^ T.card * ((((∏ p ∈ T, p : ℕ)) : ℝ) ^ (-(1 / 2 : ℝ)) *
        thetaCuspFullSource (x + Real.log m + Real.log ((∏ p ∈ T, p : ℕ) : ℝ)))) := by
    intro T _
    rw [← tsum_mul_left, ← tsum_mul_left]
    apply tsum_congr
    intro m
    rw [show x + Real.log ((∏ p ∈ T, p : ℕ) : ℝ) + Real.log m =
      x + Real.log m + Real.log ((∏ p ∈ T, p : ℕ) : ℝ) by ring]
    ring
  rw [Finset.sum_congr rfl hterm, ← Summable.tsum_finsetSum]
  · apply tsum_congr
    intro m
    rw [← Finset.mul_sum, ← thetaPrimeDeletion_thetaCuspFullSource_eq_atomSum S hS]
    rfl
  · intro T _
    refine ((hsum (x + Real.log ((∏ p ∈ T, p : ℕ) : ℝ))).mul_left
      ((-1 : ℝ) ^ T.card * (((∏ p ∈ T, p : ℕ)) : ℝ) ^ (-(1 / 2 : ℝ)))).congr fun m => ?_
    rw [show x + Real.log ((∏ p ∈ T, p : ℕ) : ℝ) + Real.log m =
      x + Real.log m + Real.log ((∏ p ∈ T, p : ℕ) : ℝ) by ring]
    ring

theorem thetaGaugeWeight_bound {c : ℕ → ℝ} (hc : Summable fun m => |c m| * Real.sqrt m)
    (A : Set ℕ) : ∀ N, |thetaGaugeWeight c A N| ≤ ∑' m, |c m| * Real.sqrt m :=
  abs_thetaGaugeWeight_le hc A

/-- Flux of a gauge over a base atom set. -/
theorem thetaNormalizedFlux_thetaBaseGauge {c : ℕ → ℝ} (hc0 : c 0 = 0)
    (hc : Summable fun m => |c m| * Real.sqrt m) (A : Set ℕ) {t : ℝ} (ht : 0 < t) :
    thetaNormalizedFlux (thetaBaseGauge c A) t =
      ∑' N, thetaGaugeWeight c A N * thetaGaussWeight N * Real.exp (-thetaGaussRate N * t) := by
  have heq : thetaBaseGauge c A = thetaWeightedAtomSum (thetaGaugeWeight c A) := by
    funext x; exact (thetaBaseGauge_eq_weightedAtomSum hc0 hc A x).1
  rw [heq, thetaNormalizedFlux_thetaWeightedAtomSum (thetaGaugeWeight_bound hc A) ht]

theorem thetaFluxSource_thetaBaseGauge {c : ℕ → ℝ} (hc0 : c 0 = 0)
    (hc : Summable fun m => |c m| * Real.sqrt m) (A : Set ℕ) :
    ThetaFluxSource (thetaBaseGauge c A) := by
  have heq : thetaBaseGauge c A = thetaWeightedAtomSum (thetaGaugeWeight c A) := by
    funext x; exact (thetaBaseGauge_eq_weightedAtomSum hc0 hc A x).1
  rw [heq]
  exact thetaFluxSource_thetaWeightedAtomSum (thetaGaugeWeight_bound hc A)

/-- For `S` the prime factors of `m₀`, the deleted gauge weight at `m₀` is `c_{m₀} √m₀`. -/
theorem thetaGaugeWeight_primeFactors (c : ℕ → ℝ) {m₀ : ℕ} (hm₀ : 0 < m₀) :
    thetaGaugeWeight c (thetaCoprimeLabels m₀.primeFactors) m₀ = c m₀ * Real.sqrt m₀ := by
  unfold thetaGaugeWeight
  rw [Finset.sum_eq_single (m₀, 1)]
  · have h1 : (1 : ℕ) ∈ thetaCoprimeLabels m₀.primeFactors := by
      intro p hp hdvd
      exact (Nat.prime_of_mem_primeFactors hp).one_lt.ne' (Nat.dvd_one.mp hdvd)
    rw [Set.indicator_of_mem h1, Pi.one_apply, mul_one]
  · intro p hp hne
    have hp' := Nat.mem_divisorsAntidiagonal.mp hp
    have h2 : p.2 ≠ 1 := by
      intro h
      apply hne
      ext
      · simp only; rw [← hp'.1, h, mul_one]
      · exact h
    rw [Set.indicator_of_notMem, mul_zero]
    intro hcop
    have hp2pos : 0 < p.2 := Nat.pos_of_ne_zero (fun h => by rw [h, mul_zero] at hp'; exact hp'.2 hp'.1.symm)
    obtain ⟨q, hq, hqd⟩ := Nat.exists_prime_and_dvd h2
    apply hcop q
    · rw [Nat.mem_primeFactors]
      exact ⟨hq, hqd.trans (Dvd.intro_left _ hp'.1), hm₀.ne'⟩
    · exact hqd
  · intro h
    exact absurd (Nat.mem_divisorsAntidiagonal.mpr ⟨by simp, hm₀.ne'⟩) h


theorem thetaGaugeWeight_nonneg {c : ℕ → ℝ} (hc : ∀ m, 0 ≤ c m) (A : Set ℕ) (N : ℕ) :
    0 ≤ thetaGaugeWeight c A N := by
  unfold thetaGaugeWeight
  apply Finset.sum_nonneg
  intro p _
  apply mul_nonneg (mul_nonneg (hc _) (Real.sqrt_nonneg _))
  by_cases h : p.2 ∈ A
  · simp [Set.indicator_of_mem h]
  · simp [Set.indicator_of_notMem h]

/-- **All-sieve Bernstein classification of one-sided integer-shift gauges.**  Every finite-prime
deleted flux of `g_c` is completely monotone if and only if all shift coefficients are
nonnegative. -/
theorem thetaIntegerShiftGauge_allSieve_iff {c : ℕ → ℝ} (hc0 : c 0 = 0)
    (hc : Summable fun m => |c m| * Real.sqrt m) :
    (∀ S : Finset ℕ, (∀ p ∈ S, p.Prime) →
        CompletelyMonotoneOn (thetaNormalizedFlux (thetaPrimeDeletion S (thetaIntegerShiftGauge c)))) ↔
      ∀ m, 0 ≤ c m := by
  set B := ∑' m, |c m| * Real.sqrt m
  have hB := thetaGaugeWeight_bound hc
  have hrep : ∀ S : Finset ℕ, (∀ p ∈ S, p.Prime) → ∀ t, 0 < t →
      thetaNormalizedFlux (thetaPrimeDeletion S (thetaIntegerShiftGauge c)) t =
        ∑' N, (thetaGaugeWeight c (thetaCoprimeLabels S) N * thetaGaussWeight N) *
          Real.exp (-thetaGaussRate N * t) := by
    intro S hS t ht
    rw [thetaPrimeDeletion_thetaIntegerShiftGauge hc0 hc S hS,
      thetaNormalizedFlux_thetaBaseGauge hc0 hc _ ht]
  have hsum : ∀ (S : Finset ℕ) t, 0 < t → Summable fun N =>
      |thetaGaugeWeight c (thetaCoprimeLabels S) N * thetaGaussWeight N| *
        Real.exp (-thetaGaussRate N * t) := by
    intro S t ht
    refine Summable.of_nonneg_of_le (fun N => by positivity) (fun N => ?_)
      ((summable_thetaGaussWeight ht).mul_left B)
    rw [abs_mul, abs_of_nonneg (thetaGaussWeight_nonneg N), mul_assoc]
    exact mul_le_mul_of_nonneg_right (hB _ N)
      (mul_nonneg (thetaGaussWeight_nonneg N) (Real.exp_pos _).le)
  constructor
  · intro h m
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · rw [hc0]
    · have hS : ∀ p ∈ m.primeFactors, p.Prime := fun p hp => Nat.prime_of_mem_primeFactors hp
      have hCM := (h m.primeFactors hS).congr_Ioi (fun t ht => hrep _ hS t ht)
      have hsign := tsum_coeff_nonneg_of_completelyMonotoneOn _ thetaGaussRate
        thetaGaussRate_nonneg (hsum m.primeFactors) hCM (thetaGaussRate m)
      rw [tsum_ite_lam_eq _ _ thetaGaussRate_injective m, thetaGaugeWeight_primeFactors c hm]
        at hsign
      have hw : 0 < thetaGaussWeight m := by
        unfold thetaGaussWeight
        have : (0 : ℝ) < m := by exact_mod_cast hm
        positivity
      have hsq : 0 < Real.sqrt m := Real.sqrt_pos.mpr (by exact_mod_cast hm)
      have := nonneg_of_mul_nonneg_left (by linarith [hsign] : 0 ≤ c m * Real.sqrt m *
        thetaGaussWeight m) hw
      exact nonneg_of_mul_nonneg_left this hsq
  · intro hcpos S hS
    have hw0 : ∀ N, 0 ≤ thetaGaugeWeight c (thetaCoprimeLabels S) N * thetaGaussWeight N :=
      fun N => mul_nonneg (thetaGaugeWeight_nonneg hcpos _ N) (thetaGaussWeight_nonneg N)
    exact (completelyMonotoneOn_tsum_exp _ thetaGaussRate hw0 thetaGaussRate_nonneg
      (fun t ht => by simpa [abs_of_nonneg (hw0 _)] using hsum S t ht)).congr_Ioi
      (fun t ht => (hrep S hS t ht).symm)

/-- Real Mellin anchors of a one-sided gauge: `∫ e^{wx} g_c = (∑ c_m m^{-w}) ∫ e^{wx} k`. -/
theorem integral_exp_mul_thetaIntegerShiftGauge {c : ℕ → ℝ} (hc0 : c 0 = 0)
    (hc : Summable fun m => |c m| * Real.sqrt m) {w : ℝ} (hw : 0 ≤ w) :
    Summable (fun m => c m * Real.exp (-(w * Real.log m))) ∧
      (∫ x : ℝ, Real.exp (w * x) * thetaIntegerShiftGauge c x) =
        (∑' m, c m * Real.exp (-(w * Real.log m))) *
          ∫ x : ℝ, Real.exp (w * x) * thetaCuspFullSource x := by
  set I := ∫ x : ℝ, Real.exp (w * x) * thetaCuspFullSource x
  have hk := HedenmalmThetaSource.integrable_exp_mul_thetaCuspFullSource w
  have hcabs : Summable fun m => |c m| := by
    refine Summable.of_nonneg_of_le (fun m => abs_nonneg _) (fun m => ?_) hc
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · simp [hc0]
    · have : (1 : ℝ) ≤ Real.sqrt m := by
        rw [Real.one_le_sqrt]; exact_mod_cast hm
      nlinarith [abs_nonneg (c m)]
  have hexp_le : ∀ m : ℕ, Real.exp (-(w * Real.log m)) ≤ 1 := fun m =>
    Real.exp_le_one_iff.mpr (by nlinarith [Real.log_natCast_nonneg m])
  have hcs : Summable fun m => c m * Real.exp (-(w * Real.log m)) :=
    Summable.of_norm_bounded hcabs (fun m => by
      rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
      exact mul_le_of_le_one_right (abs_nonneg _) (hexp_le m))
  set F : ℕ → ℝ → ℝ := fun m x => c m * (Real.exp (w * x) * thetaCuspFullSource (x + Real.log m))
  have htrans : ∀ m, (∫ x : ℝ, Real.exp (w * x) * thetaCuspFullSource (x + Real.log m)) =
      Real.exp (-(w * Real.log m)) * I := by
    intro m
    have h := integral_exp_mul_comp_sub w (-Real.log m) thetaCuspFullSource
    simp only [sub_neg_eq_add] at h
    rw [h, show w * -Real.log m = -(w * Real.log m) by ring]
  have hFint : ∀ m, Integrable (F m) := by
    intro m
    have h := ((hk.comp_add_right (Real.log m)).const_mul (Real.exp (-(w * Real.log m)))).const_mul
      (c m)
    refine h.congr (Eventually.of_forall fun x => ?_)
    simp only [F]
    rw [show w * (x + Real.log m) = w * x + w * Real.log m by ring, Real.exp_add]
    rw [show Real.exp (-(w * Real.log m)) * (Real.exp (w * x) * Real.exp (w * Real.log m) *
      thetaCuspFullSource (x + Real.log m)) = (Real.exp (-(w * Real.log m)) *
        Real.exp (w * Real.log m)) * (Real.exp (w * x) * thetaCuspFullSource (x + Real.log m))
      by ring, ← Real.exp_add, neg_add_cancel, Real.exp_zero, one_mul]
  have hnorm : ∀ m, (∫ x, ‖F m x‖) = |c m| * (Real.exp (-(w * Real.log m)) * I) := by
    intro m
    rw [← htrans, ← integral_const_mul]
    apply integral_congr_ae
    filter_upwards with x
    simp only [F, Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _),
      abs_of_pos (thetaCuspFullSource_pos_all _)]
  have hsumnorm : Summable fun m => ∫ x, ‖F m x‖ := by
    simp_rw [hnorm]
    refine Summable.of_nonneg_of_le (fun m => mul_nonneg (abs_nonneg _)
      (mul_nonneg (Real.exp_pos _).le (integral_exp_mul_thetaCuspFullSource_pos w).le))
      (fun m => ?_) (hcabs.mul_right I)
    exact mul_le_mul_of_nonneg_left
      (mul_le_of_le_one_left (integral_exp_mul_thetaCuspFullSource_pos w).le (hexp_le m))
      (abs_nonneg _)
  refine ⟨hcs, ?_⟩
  have h := integral_tsum_of_summable_integral_norm hFint hsumnorm
  have hsumF : ∀ x, (∑' m, F m x) = Real.exp (w * x) * thetaIntegerShiftGauge c x := by
    intro x
    simp only [F, thetaIntegerShiftGauge]
    rw [← tsum_mul_left]
    apply tsum_congr; intro m; ring
  rw [← integral_congr_ae (Eventually.of_forall hsumF), ← h, ← tsum_mul_right]
  apply tsum_congr
  intro m
  simp only [F]
  rw [integral_const_mul, htrans]
  ring

/-- **Two-anchor rigidity.**  An all-sieve positive one-sided gauge with the ordinary mass and the
critical half-charge of `k` is `k` itself. -/
theorem thetaIntegerShiftGauge_rigid {c : ℕ → ℝ} (hc0 : c 0 = 0)
    (hc : Summable fun m => |c m| * Real.sqrt m) (hpos : ∀ m, 0 ≤ c m)
    (hmass : (∫ x : ℝ, thetaIntegerShiftGauge c x) = ∫ x : ℝ, thetaCuspFullSource x)
    (hcharge : (∫ x : ℝ, Real.exp ((1 / 2 : ℝ) * x) * thetaIntegerShiftGauge c x) =
      ∫ x : ℝ, Real.exp ((1 / 2 : ℝ) * x) * thetaCuspFullSource x) :
    c = (fun m => if m = 1 then 1 else 0) ∧ thetaIntegerShiftGauge c = thetaCuspFullSource := by
  obtain ⟨hs0, h0⟩ := integral_exp_mul_thetaIntegerShiftGauge hc0 hc (w := 0) le_rfl
  obtain ⟨hs1, h1⟩ := integral_exp_mul_thetaIntegerShiftGauge hc0 hc (w := 1 / 2) (by norm_num)
  simp only [zero_mul, neg_zero, Real.exp_zero, mul_one, one_mul] at h0 hs0
  rw [h0] at hmass
  rw [h1] at hcharge
  have hI0 := integral_thetaCuspFullSource_pos
  have hI1 := integral_exp_mul_thetaCuspFullSource_pos (1 / 2)
  have hM0 : (∑' m, c m) = 1 := by
    have := mul_right_cancel₀ hI0.ne' (hmass.trans (one_mul _).symm)
    exact this
  have hM1 : (∑' m, c m * Real.exp (-(1 / 2 * Real.log m))) = 1 := by
    have := mul_right_cancel₀ hI1.ne' (hcharge.trans (one_mul _).symm)
    exact this
  have hterm_nn : ∀ m, 0 ≤ c m * (1 - Real.exp (-(1 / 2 * Real.log m))) := fun m =>
    mul_nonneg (hpos m) (by
      have := Real.exp_le_one_iff.mpr (show -(1 / 2 * Real.log m) ≤ 0 by
        nlinarith [Real.log_natCast_nonneg m])
      linarith)
  have hD : (∑' m, c m * (1 - Real.exp (-(1 / 2 * Real.log m)))) = 0 := by
    rw [show (fun m => c m * (1 - Real.exp (-(1 / 2 * Real.log m)))) =
      fun m => c m - c m * Real.exp (-(1 / 2 * Real.log m)) by funext m; ring,
      hs0.tsum_sub hs1, hM0, hM1, sub_self]
  have hsD : Summable fun m => c m * (1 - Real.exp (-(1 / 2 * Real.log m))) :=
    (hs0.sub hs1).congr fun m => by ring
  have hzero := (hasSum_zero_iff_of_nonneg hterm_nn).mp (hD ▸ hsD.hasSum)
  have hcm : ∀ m, 2 ≤ m → c m = 0 := by
    intro m hm
    have h := congrFun hzero m
    simp only [Pi.zero_apply] at h
    have hlog : 0 < Real.log m := Real.log_pos (by exact_mod_cast (by omega : 1 < m))
    have hexp : Real.exp (-(1 / 2 * Real.log m)) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
    rcases mul_eq_zero.mp h with h | h
    · exact h
    · linarith
  have hc1 : c 1 = 1 := by
    rw [← hM0, tsum_eq_single 1]
    intro m hm
    rcases Nat.lt_or_ge m 2 with h | h
    · interval_cases m
      · exact hc0
      · exact absurd rfl hm
    · exact hcm m h
  have hceq : c = fun m => if m = 1 then 1 else 0 := by
    funext m
    split_ifs with h
    · rw [h, hc1]
    · rcases Nat.lt_or_ge m 2 with h' | h'
      · interval_cases m
        · exact hc0
        · exact absurd rfl h
      · exact hcm m h'
  refine ⟨hceq, ?_⟩
  funext x
  rw [thetaIntegerShiftGauge, hceq, tsum_eq_single 1]
  · simp
  · intro m hm
    simp [hm]


/-- Complete monotonicity of a deleted gauge flux forces nonnegative deleted weights. -/
theorem thetaGaugeWeight_nonneg_of_completelyMonotone {c : ℕ → ℝ} (hc0 : c 0 = 0)
    (hc : Summable fun m => |c m| * Real.sqrt m) {S : Finset ℕ} (hS : ∀ p ∈ S, p.Prime)
    (hCM : CompletelyMonotoneOn
      (thetaNormalizedFlux (thetaPrimeDeletion S (thetaIntegerShiftGauge c)))) (N : ℕ) :
    0 ≤ thetaGaugeWeight c (thetaCoprimeLabels S) N * thetaGaussWeight N := by
  set B := ∑' m, |c m| * Real.sqrt m
  have hB := thetaGaugeWeight_bound hc
  have hsum : ∀ t, 0 < t → Summable fun N =>
      |thetaGaugeWeight c (thetaCoprimeLabels S) N * thetaGaussWeight N| *
        Real.exp (-thetaGaussRate N * t) := by
    intro t ht
    refine Summable.of_nonneg_of_le (fun N => by positivity) (fun N => ?_)
      ((summable_thetaGaussWeight ht).mul_left B)
    rw [abs_mul, abs_of_nonneg (thetaGaussWeight_nonneg N), mul_assoc]
    exact mul_le_mul_of_nonneg_right (hB _ N)
      (mul_nonneg (thetaGaussWeight_nonneg N) (Real.exp_pos _).le)
  have hCM' := hCM.congr_Ioi (fun t ht => by
    rw [thetaPrimeDeletion_thetaIntegerShiftGauge hc0 hc S hS,
      thetaNormalizedFlux_thetaBaseGauge hc0 hc _ ht])
  have h := tsum_coeff_nonneg_of_completelyMonotoneOn _ thetaGaussRate thetaGaussRate_nonneg hsum
    hCM' (thetaGaussRate N)
  rwa [tsum_ite_lam_eq _ _ thetaGaussRate_injective N] at h

/-! ## The one-sided two-anchor countermodel -/

/-- Shift coefficients `c₁ = 1 - dα`, `c₂ = α`, `c₄ = -κα` with `κ = 2 - √2`, `d = √2 - 1`. -/
noncomputable def oneSidedCoeff (α : ℝ) (m : ℕ) : ℝ :=
  if m = 1 then 1 - (Real.sqrt 2 - 1) * α else if m = 2 then α
    else if m = 4 then -((2 - Real.sqrt 2) * α) else 0

theorem oneSidedCoeff_zero (α : ℝ) : oneSidedCoeff α 0 = 0 := by simp [oneSidedCoeff]

theorem oneSidedCoeff_summable (α : ℝ) :
    Summable fun m => |oneSidedCoeff α m| * Real.sqrt m := by
  apply summable_of_hasFiniteSupport
  apply (Set.finite_le_nat 4).subset
  intro m hm
  simp only [Function.mem_support] at hm
  by_contra h
  simp only [Set.mem_setOf_eq, not_le] at h
  apply hm
  simp [oneSidedCoeff, show m ≠ 1 by omega, show m ≠ 2 by omega, show m ≠ 4 by omega]

/-- The one-sided gauge `g_α = (1-dα) k + α k(· + log 2) - κα k(· + log 4)`. -/
theorem thetaIntegerShiftGauge_oneSided (α x : ℝ) :
    thetaIntegerShiftGauge (oneSidedCoeff α) x =
      (1 - (Real.sqrt 2 - 1) * α) * thetaCuspFullSource x +
        α * thetaCuspFullSource (x + Real.log 2) -
          (2 - Real.sqrt 2) * α * thetaCuspFullSource (x + Real.log 4) := by
  rw [thetaIntegerShiftGauge, tsum_eq_sum (s := {1, 2, 4})]
  · simp [oneSidedCoeff, Finset.sum_insert, Finset.sum_singleton]
    ring
  · intro m hm
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hm
    simp [oneSidedCoeff, hm.1, hm.2.1, hm.2.2]

/-- The Gaussian rate weights `R_n` of the one-sided gauge. -/
theorem thetaGaugeWeight_oneSided (α : ℝ) {N : ℕ} (hN : 0 < N) :
    thetaGaugeWeight (oneSidedCoeff α) Set.univ N =
      1 - (Real.sqrt 2 - 1) * α + Real.sqrt 2 * α * (if 2 ∣ N then 1 else 0) -
        2 * (2 - Real.sqrt 2) * α * (if 4 ∣ N then 1 else 0) := by
  unfold thetaGaugeWeight
  simp only [Set.indicator_univ, Pi.one_apply, mul_one]
  rw [Nat.sum_divisorsAntidiagonal (fun a _ => oneSidedCoeff α a * Real.sqrt a)]
  have hsupp : ∀ d ∈ N.divisors, d ∉ ({1, 2, 4} : Finset ℕ) →
      oneSidedCoeff α d * Real.sqrt d = 0 := by
    intro d _ hd
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hd
    simp [oneSidedCoeff, hd.1, hd.2.1, hd.2.2]
  rw [← Finset.sum_subset (Finset.filter_subset (· ∈ ({1, 2, 4} : Finset ℕ)) N.divisors)
    (fun d hd hnot => hsupp d hd (fun h => hnot (Finset.mem_filter.mpr ⟨hd, h⟩)))]
  have h1 : 1 ∈ N.divisors := Nat.mem_divisors.mpr ⟨one_dvd N, hN.ne'⟩
  have hsqrt4 : Real.sqrt 4 = 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  by_cases h4 : 4 ∣ N
  · have h2 : 2 ∣ N := (show 2 ∣ 4 by norm_num).trans h4
    have hfilt : N.divisors.filter (· ∈ ({1, 2, 4} : Finset ℕ)) = {1, 2, 4} := by
      ext d
      simp only [Finset.mem_filter, Nat.mem_divisors, Finset.mem_insert, Finset.mem_singleton]
      constructor
      · exact fun h => h.2
      · rintro (rfl | rfl | rfl)
        · exact ⟨⟨one_dvd N, hN.ne'⟩, Or.inl rfl⟩
        · exact ⟨⟨h2, hN.ne'⟩, Or.inr (Or.inl rfl)⟩
        · exact ⟨⟨h4, hN.ne'⟩, Or.inr (Or.inr rfl)⟩
    rw [hfilt]
    simp [oneSidedCoeff, h2, h4, hsqrt4, Finset.sum_insert]
    ring
  · by_cases h2 : 2 ∣ N
    · have hfilt : N.divisors.filter (· ∈ ({1, 2, 4} : Finset ℕ)) = {1, 2} := by
        ext d
        simp only [Finset.mem_filter, Nat.mem_divisors, Finset.mem_insert, Finset.mem_singleton]
        constructor
        · rintro ⟨⟨hd, _⟩, rfl | rfl | rfl⟩
          · exact Or.inl rfl
          · exact Or.inr rfl
          · exact absurd hd h4
        · rintro (rfl | rfl)
          · exact ⟨⟨one_dvd N, hN.ne'⟩, Or.inl rfl⟩
          · exact ⟨⟨h2, hN.ne'⟩, Or.inr (Or.inl rfl)⟩
      rw [hfilt]
      simp [oneSidedCoeff, h2, h4]
      ring
    · have hfilt : N.divisors.filter (· ∈ ({1, 2, 4} : Finset ℕ)) = {1} := by
        ext d
        simp only [Finset.mem_filter, Nat.mem_divisors, Finset.mem_insert, Finset.mem_singleton]
        constructor
        · rintro ⟨⟨hd, _⟩, rfl | rfl | rfl⟩
          · rfl
          · exact absurd hd h2
          · exact absurd hd h4
        · rintro rfl
          exact ⟨⟨one_dvd N, hN.ne'⟩, Or.inl rfl⟩
      rw [hfilt]
      simp [oneSidedCoeff, h2, h4]


private theorem sqrt_two_facts : Real.sqrt 2 ^ 2 = 2 ∧ 0 < Real.sqrt 2 ∧ Real.sqrt 2 < 3 / 2 ∧
    (7 : ℝ) / 5 < Real.sqrt 2 := by
  have h2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hpos : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  refine ⟨h2, hpos, ?_, ?_⟩ <;> nlinarith

/-- All Gaussian rate weights of the one-sided gauge are positive for `0 < α < 1`. -/
theorem thetaGaugeWeight_oneSided_pos {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1) {N : ℕ} (hN : 0 < N) :
    0 < thetaGaugeWeight (oneSidedCoeff α) Set.univ N := by
  obtain ⟨h2, hpos, hlt, hgt⟩ := sqrt_two_facts
  rw [thetaGaugeWeight_oneSided α hN]
  by_cases h4 : 4 ∣ N
  · have h2' : 2 ∣ N := (show 2 ∣ 4 by norm_num).trans h4
    simp only [h4, h2', if_true, mul_one]
    nlinarith
  · by_cases h2' : 2 ∣ N
    · simp only [h4, h2', if_true, if_false, mul_one, mul_zero, sub_zero]; nlinarith
    · simp only [h4, h2', if_false, mul_zero, sub_zero, add_zero]; nlinarith

theorem thetaGaugeWeight_oneSided_nonneg {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1) (N : ℕ) :
    0 ≤ thetaGaugeWeight (oneSidedCoeff α) Set.univ N := by
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · simp [thetaGaugeWeight]
  · exact (thetaGaugeWeight_oneSided_pos hα0 hα1 hN).le

/-- **(1) Complete monotonicity** of the undeleted one-sided flux. -/
theorem completelyMonotoneOn_flux_oneSided {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1) :
    CompletelyMonotoneOn (thetaNormalizedFlux (thetaIntegerShiftGauge (oneSidedCoeff α))) := by
  have hc := oneSidedCoeff_summable α
  have hc0 := oneSidedCoeff_zero α
  have hw0 : ∀ N, 0 ≤ thetaGaugeWeight (oneSidedCoeff α) Set.univ N * thetaGaussWeight N :=
    fun N => mul_nonneg (thetaGaugeWeight_oneSided_nonneg hα0 hα1 N) (thetaGaussWeight_nonneg N)
  have hB := thetaGaugeWeight_bound hc Set.univ
  have hs : ∀ t, 0 < t → Summable fun N =>
      thetaGaugeWeight (oneSidedCoeff α) Set.univ N * thetaGaussWeight N *
        Real.exp (-thetaGaussRate N * t) := by
    intro t ht
    refine Summable.of_nonneg_of_le (fun N => mul_nonneg (hw0 N) (Real.exp_pos _).le)
      (fun N => ?_) ((summable_thetaGaussWeight ht).mul_left (∑' m, |oneSidedCoeff α m| * Real.sqrt m))
    rw [mul_assoc]
    exact mul_le_mul_of_nonneg_right ((le_abs_self _).trans (hB N))
      (mul_nonneg (thetaGaussWeight_nonneg N) (Real.exp_pos _).le)
  refine (completelyMonotoneOn_tsum_exp _ thetaGaussRate hw0 thetaGaussRate_nonneg hs).congr_Ioi
    (fun t ht => ?_)
  rw [thetaIntegerShiftGauge_eq_baseGauge, thetaNormalizedFlux_thetaBaseGauge hc0 hc _ ht]

/-- **(3) Positivity on the positive ray.** -/
theorem thetaIntegerShiftGauge_oneSided_pos {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1) {x : ℝ}
    (hx : 0 ≤ x) : 0 < thetaIntegerShiftGauge (oneSidedCoeff α) x := by
  have hc := oneSidedCoeff_summable α
  rw [thetaIntegerShiftGauge_eq_baseGauge,
    (thetaBaseGauge_eq_weightedAtomSum (oneSidedCoeff_zero α) hc Set.univ x).1]
  exact thetaWeightedAtomSum_pos_of_nonneg (thetaGaugeWeight_bound hc Set.univ)
    (thetaGaugeWeight_oneSided_nonneg hα0 hα1) (thetaGaugeWeight_oneSided_pos hα0 hα1 one_pos) hx

/-- **(2) Both anchors.** -/
theorem thetaIntegerShiftGauge_oneSided_anchors (α : ℝ) :
    (∫ x : ℝ, thetaIntegerShiftGauge (oneSidedCoeff α) x) = ∫ x : ℝ, thetaCuspFullSource x ∧
      (∫ x : ℝ, Real.exp ((1 / 2 : ℝ) * x) * thetaIntegerShiftGauge (oneSidedCoeff α) x) =
        ∫ x : ℝ, Real.exp ((1 / 2 : ℝ) * x) * thetaCuspFullSource x := by
  have hc := oneSidedCoeff_summable α
  have hc0 := oneSidedCoeff_zero α
  obtain ⟨h2, hpos, -, -⟩ := sqrt_two_facts
  have hsum : ∀ w : ℝ, (∑' m, oneSidedCoeff α m * Real.exp (-(w * Real.log m))) =
      (1 - (Real.sqrt 2 - 1) * α) + α * Real.exp (-(w * Real.log 2)) -
        (2 - Real.sqrt 2) * α * Real.exp (-(w * Real.log 4)) := by
    intro w
    rw [tsum_eq_sum (s := {1, 2, 4})]
    · simp [oneSidedCoeff, Finset.sum_insert]
      ring
    · intro m hm
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hm
      simp [oneSidedCoeff, hm.1, hm.2.1, hm.2.2]
  constructor
  · have h := (integral_exp_mul_thetaIntegerShiftGauge hc0 hc (w := 0) le_rfl).2
    have h0 := hsum 0
    simp only [zero_mul, neg_zero, Real.exp_zero, one_mul, mul_one] at h h0
    rw [h, h0]
    ring
  · rw [(integral_exp_mul_thetaIntegerShiftGauge hc0 hc (w := 1 / 2) (by norm_num)).2, hsum]
    have e2 : Real.exp (-(1 / 2 * Real.log 2)) = Real.sqrt 2 / 2 := by
      rw [show -(1 / 2 * Real.log 2) = Real.log ((Real.sqrt 2)⁻¹) by
        rw [Real.log_inv, Real.log_sqrt (by norm_num)]; ring, Real.exp_log (by positivity)]
      field_simp
      rw [h2]
    have e4 : Real.exp (-(1 / 2 * Real.log 4)) = 1 / 2 := by
      rw [show -(1 / 2 * Real.log 4) = Real.log (1 / 2) by
        rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow, one_div, Real.log_inv]; ring,
        Real.exp_log (by norm_num)]
    rw [e2, e4]
    ring_nf


/-- The Mellin multiplier `M_α(w) = 1 - dα + α 2^{-w} - κα 4^{-w}`. -/
noncomputable def oneSidedMultiplier (α : ℝ) (w : ℂ) : ℂ :=
  (1 - (Real.sqrt 2 - 1) * α : ℝ) + (α : ℂ) * Complex.exp (-(w * Real.log 2)) -
    ((2 - Real.sqrt 2) * α : ℝ) * Complex.exp (-(w * Real.log 4))

/-- **(4) Mellin law.**  `L_w g_α = M_α(w) XiC(i w)` for every complex `w`. -/
theorem integral_cexp_mul_oneSidedGauge (α : ℝ) (w : ℂ) :
    (∫ x : ℝ, Complex.exp (w * x) * (thetaIntegerShiftGauge (oneSidedCoeff α) x : ℂ)) =
      oneSidedMultiplier α w * XiC (Complex.I * w) := by
  have hk := integrable_cexp_mul_thetaCuspFullSource w
  have h2 := integrable_cexp_mul_comp_add (Real.log 2) (G := fun y => (thetaCuspFullSource y : ℂ)) hk
  have h4 := integrable_cexp_mul_comp_add (Real.log 4) (G := fun y => (thetaCuspFullSource y : ℂ)) hk
  have hfun : (fun x : ℝ => Complex.exp (w * x) *
      (thetaIntegerShiftGauge (oneSidedCoeff α) x : ℂ)) =
      fun x : ℝ => (((1 - (Real.sqrt 2 - 1) * α : ℝ)) : ℂ) *
          (Complex.exp (w * x) * (thetaCuspFullSource x : ℂ)) +
        (α : ℂ) * (Complex.exp (w * x) * (thetaCuspFullSource (x + Real.log 2) : ℂ)) -
        (((2 - Real.sqrt 2) * α : ℝ) : ℂ) *
          (Complex.exp (w * x) * (thetaCuspFullSource (x + Real.log 4) : ℂ)) := by
    funext x
    rw [thetaIntegerShiftGauge_oneSided]
    push_cast
    ring
  have h12 : Integrable (fun x : ℝ => (((1 - (Real.sqrt 2 - 1) * α : ℝ)) : ℂ) *
      (Complex.exp (w * x) * (thetaCuspFullSource x : ℂ)) +
      (α : ℂ) * (Complex.exp (w * x) * (thetaCuspFullSource (x + Real.log 2) : ℂ))) :=
    (hk.const_mul _).add (h2.const_mul _)
  rw [hfun, integral_sub h12 (h4.const_mul _),
    integral_add (hk.const_mul _) (h2.const_mul _), integral_const_mul, integral_const_mul,
    integral_const_mul,
    integral_cexp_mul_comp_add w (Real.log 2) (fun y => (thetaCuspFullSource y : ℂ)),
    integral_cexp_mul_comp_add w (Real.log 4) (fun y => (thetaCuspFullSource y : ℂ)),
    integral_cexp_mul_thetaCuspFullSource, oneSidedMultiplier]
  ring

/-- **(4) The off-line zero.**  For `1/2 < α < 1/√2` the multiplier, hence the Mellin transform of
`g_α`, vanishes at some `w = σ + iπ/log 2` with `0 < σ < 1/2`. -/
theorem exists_offLine_zero_oneSidedGauge {α : ℝ} (hα : 1 / 2 < α) (hα' : α < Real.sqrt 2 / 2) :
    ∃ w : ℂ, 0 < w.re ∧ w.re < 1 / 2 ∧ w.im = Real.pi / Real.log 2 ∧
      oneSidedMultiplier α w = 0 ∧
      (∫ x : ℝ, Complex.exp (w * x) * (thetaIntegerShiftGauge (oneSidedCoeff α) x : ℂ)) = 0 := by
  obtain ⟨h2s, hpos, hlt, hgt⟩ := sqrt_two_facts
  set r : ℝ := Real.sqrt 2 / 2
  set f : ℝ → ℝ := fun z => 1 - (Real.sqrt 2 - 1) * α + α * z - (2 - Real.sqrt 2) * α * z ^ 2
  have hf1 : f (-1) < 0 := by simp only [f]; nlinarith
  have hfr : 0 < f (-r) := by
    have e : f (-r) = 1 - Real.sqrt 2 * α := by
      simp only [f, r]
      linear_combination (-((2 - Real.sqrt 2) * α / 4)) * h2s
    have hsa : Real.sqrt 2 * α < 1 := by
      have := mul_lt_mul_of_pos_left hα' hpos
      simp only [r] at this
      nlinarith
    rw [e]; linarith
  have hcont : ContinuousOn f (Set.Icc (-1) (-r)) := by
    simp only [f]; fun_prop
  have hr1 : -1 ≤ -r := by simp only [r]; linarith
  obtain ⟨z₀, hz₀, hfz⟩ := intermediate_value_Icc hr1 hcont ⟨hf1.le, hfr.le⟩
  have hz1 : z₀ ≠ -1 := fun h => by rw [h] at hfz; linarith
  have hzr : z₀ ≠ -r := fun h => by rw [h] at hfz; linarith
  have hzlo : -1 < z₀ := lt_of_le_of_ne hz₀.1 (Ne.symm hz1)
  have hzhi : z₀ < -r := lt_of_le_of_ne hz₀.2 hzr
  have hrpos : 0 < r := by simp only [r]; positivity
  have hmz : 0 < -z₀ := by linarith
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  set σ : ℝ := -Real.log (-z₀) / Real.log 2
  have hlogz : Real.log (-z₀) < 0 := Real.log_neg hmz (by linarith)
  have hlogr : Real.log r = -(Real.log 2 / 2) := by
    simp only [r]
    rw [Real.log_div (by positivity) (by norm_num), Real.log_sqrt (by norm_num)]
    ring
  have hlogzr : Real.log r < Real.log (-z₀) := Real.log_lt_log hrpos (by linarith)
  have hσ0 : 0 < σ := by simp only [σ]; exact div_pos (by linarith) hlog2
  have hσ1 : σ < 1 / 2 := by
    simp only [σ]
    rw [div_lt_iff₀ hlog2]
    linarith
  set w₀ : ℂ := (σ : ℂ) + ((Real.pi / Real.log 2 : ℝ) : ℂ) * Complex.I
  have hσlog : σ * Real.log 2 = -Real.log (-z₀) := by
    simp only [σ]; field_simp
  have hπlog : Real.pi / Real.log 2 * Real.log 2 = Real.pi := by field_simp
  have hE2 : Complex.exp (-(w₀ * Real.log 2)) = z₀ := by
    have : -(w₀ * (Real.log 2 : ℂ)) = ((Real.log (-z₀) : ℝ) : ℂ) + (-(Real.pi : ℂ)) * Complex.I := by
      have h1 : ((σ * Real.log 2 : ℝ) : ℂ) = ((-Real.log (-z₀) : ℝ) : ℂ) := by rw [hσlog]
      have h2 : ((Real.pi / Real.log 2 * Real.log 2 : ℝ) : ℂ) = (Real.pi : ℂ) := by rw [hπlog]
      push_cast at h1 h2
      simp only [w₀]
      push_cast
      linear_combination (-1 : ℂ) * h1 - Complex.I * h2
    rw [this, Complex.exp_add, ← Complex.ofReal_exp, Real.exp_log hmz,
      show -(Real.pi : ℂ) * Complex.I = -(Real.pi * Complex.I) by ring, Complex.exp_neg,
      Complex.exp_pi_mul_I]
    push_cast
    ring
  have hE4 : Complex.exp (-(w₀ * Real.log 4)) = (z₀ : ℂ) ^ 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow, ← hE2, ← Complex.exp_nat_mul]
    congr 1
    push_cast
    ring
  have hM : oneSidedMultiplier α w₀ = 0 := by
    rw [oneSidedMultiplier, hE2, hE4]
    have : (f z₀ : ℂ) = 0 := by rw [hfz]; simp
    simp only [f] at this
    push_cast at this ⊢
    linear_combination this
  have hre : w₀.re = σ := by
    simp only [w₀, Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re,
      Complex.ofReal_im, Complex.I_im]
    ring
  have him : w₀.im = Real.pi / Real.log 2 := by
    simp only [w₀, Complex.add_im, Complex.ofReal_re, Complex.mul_im, Complex.I_re,
      Complex.ofReal_im, Complex.I_im]
    ring
  refine ⟨w₀, ?_, ?_, him, hM, ?_⟩
  · rw [hre]; exact hσ0
  · rw [hre]; exact hσ1
  · rw [integral_cexp_mul_oneSidedGauge, hM, zero_mul]

/-- **The one-sided gauge is not even.** -/
theorem oneSidedGauge_not_even {α : ℝ} (hα : 0 < α) :
    ∃ x : ℝ, thetaIntegerShiftGauge (oneSidedCoeff α) (-x) ≠
      thetaIntegerShiftGauge (oneSidedCoeff α) x := by
  by_contra hcon
  push Not at hcon
  obtain ⟨h2s, hpos, hlt, hgt⟩ := sqrt_two_facts
  have hreal : ∀ w : ℝ, (∫ x : ℝ, Real.exp (w * x) * thetaIntegerShiftGauge (oneSidedCoeff α) x) =
      ((1 - (Real.sqrt 2 - 1) * α) + α * Real.exp (-(w * Real.log 2)) -
        (2 - Real.sqrt 2) * α * Real.exp (-(w * Real.log 4))) *
        ∫ x : ℝ, Real.exp (w * x) * thetaCuspFullSource x := by
    intro w
    have h := integral_cexp_mul_oneSidedGauge α (w : ℂ)
    rw [integral_cexp_mul_ofReal_eq_ofReal_integral, ← integral_cexp_mul_thetaCuspFullSource,
      integral_cexp_mul_ofReal_eq_ofReal_integral, oneSidedMultiplier] at h
    apply Complex.ofReal_injective
    rw [h]
    push_cast
    ring
  have hsym : ∀ w : ℝ, (∫ x : ℝ, Real.exp (w * x) * thetaIntegerShiftGauge (oneSidedCoeff α) x) =
      ∫ x : ℝ, Real.exp (-w * x) * thetaIntegerShiftGauge (oneSidedCoeff α) x := by
    intro w
    rw [← integral_neg_eq_self (fun x => Real.exp (-w * x) *
      thetaIntegerShiftGauge (oneSidedCoeff α) x) volume]
    apply integral_congr_ae
    filter_upwards with x
    simp only [hcon x]
    ring_nf
  have hkeven : ∀ w : ℝ, (∫ x : ℝ, Real.exp (-w * x) * thetaCuspFullSource x) =
      ∫ x : ℝ, Real.exp (w * x) * thetaCuspFullSource x := by
    intro w
    rw [← integral_neg_eq_self (fun x => Real.exp (w * x) * thetaCuspFullSource x) volume]
    apply integral_congr_ae
    filter_upwards with x
    simp only [thetaCuspFullSource_neg]
    ring_nf
  have h1 := hsym 1
  rw [hreal 1, hreal (-1), hkeven 1] at h1
  have hI := integral_exp_mul_thetaCuspFullSource_pos 1
  have hmul := mul_right_cancel₀ hI.ne' h1
  have e2 : Real.exp (-(1 * Real.log 2)) = 1 / 2 := by
    rw [one_mul, Real.exp_neg, Real.exp_log (by norm_num), one_div]
  have e4 : Real.exp (-(1 * Real.log 4)) = 1 / 4 := by
    rw [one_mul, Real.exp_neg, Real.exp_log (by norm_num), one_div]
  have e2' : Real.exp (-(-1 * Real.log 2)) = 2 := by
    rw [show -(-1 * Real.log 2) = Real.log 2 by ring, Real.exp_log (by norm_num)]
  have e4' : Real.exp (-(-1 * Real.log 4)) = 4 := by
    rw [show -(-1 * Real.log 4) = Real.log 4 by ring, Real.exp_log (by norm_num)]
  rw [e2, e4, e2', e4'] at hmul
  nlinarith

/-- **The first prime deletion detects the countermodel.**  The `{2}`-deleted flux of `g_α` is not
completely monotone: its rate weight at `4π` is `-2κα < 0`. -/
theorem oneSidedGauge_deleted_two_not_completelyMonotone {α : ℝ} (hα : 0 < α) :
    ¬ CompletelyMonotoneOn (thetaNormalizedFlux
      (thetaPrimeDeletion {2} (thetaIntegerShiftGauge (oneSidedCoeff α)))) := by
  intro hCM
  have h := thetaGaugeWeight_nonneg_of_completelyMonotone (oneSidedCoeff_zero α)
    (oneSidedCoeff_summable α) (S := {2}) (by simp [Nat.prime_two]) hCM 4
  have hw : thetaGaugeWeight (oneSidedCoeff α) (thetaCoprimeLabels {2}) 4 =
      -(2 * (2 - Real.sqrt 2) * α) := by
    unfold thetaGaugeWeight
    rw [Nat.sum_divisorsAntidiagonal (fun a b => oneSidedCoeff α a * Real.sqrt a *
      (thetaCoprimeLabels {2}).indicator 1 b)]
    rw [show (4 : ℕ).divisors = {1, 2, 4} by decide]
    have hsqrt4 : Real.sqrt 4 = 2 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
    simp [oneSidedCoeff, thetaCoprimeLabels, Finset.sum_insert, Set.indicator_apply, hsqrt4]
    ring
  rw [hw] at h
  have hg : 0 < thetaGaussWeight 4 := by unfold thetaGaussWeight; positivity
  obtain ⟨-, -, hlt, -⟩ := sqrt_two_facts
  have : 0 < 2 * (2 - Real.sqrt 2) * α * thetaGaussWeight 4 :=
    mul_pos (mul_pos (mul_pos two_pos (by linarith)) hα) hg
  linarith

end RHTower
