import GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.TheSeparatedGammaTailIsUniformAtGrowingOverlap
import GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.TheNearAndFarGammaProfilesHaveOneFinitePart
import GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.TheGrowingNearPairMeanIsPolar
import GaloisForLFunctions.RenormalizedArithmeticPotentialTheory.TheCompleteWeilMatrixDecomposesAtEveryOverlap

/-!
# The far cross error at a growing overlap

At overlap `c ≥ 1` the complete Weil matrix keeps the cross replacement error only on the far
pairs `|log(j/n)| > 2w`, `w = c/N` (`separatedCrossErrorMatrix`). On Ramanujan packets it grows
linearly in `c`, and only at the pole:

`⟨Cr^sep R_e, R_{e'}⟩ = 2[e = e' = 1] c F_φ + O(√c (1 + log c) + c³/N)`
(`abs_farCrossPairing_sub_le`), with
`F_φ = ((∫φ)² log 2 − ∫_{−1}^1 G(t) log(2 + t) dt)/(2∫φ²)` (`farCrossFinitePart`).

The far pairs at scaled distance `ℓ = |log(j/n)|/w ∈ (2, T]`, `T = √c`, carry the singular
profile `σ(1/ℓ)` up to `O(w)` and average periodically to `2ūv̄ c ∫_2^T σ(1/ℓ) dℓ`
(`abs_nearPairSum_sub_le`); the pairs beyond `T` cost `O(c/T + c²/N)`
(`abs_farCross_pair_tail_le`). Hence `⟨Cr^sep R_e, R_{e'}⟩/c → 2[e = e' = 1] F_φ` along `c → ∞`,
`c²/N → 0` (`tendsto_farCrossPairing_div_overlap`).
-/

noncomputable section

open MeasureTheory Set Filter Topology Finset
open scoped RealInnerProductSpace

namespace GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations

open RenormalizedArithmeticPotentialTheory SpacingScaleHarmonicAnalysis BezoutValuationIncidence

/-- A matrix pairing of two Ramanujan packets as a double sum over the horizon. -/
theorem inner_matrix_ramanujanHorizonVector_eq {N : ℕ}
    (A : Matrix (PrimeHorizonIndex N) (PrimeHorizonIndex N) ℝ) (f : ℕ → ℕ → ℝ)
    (hA : ∀ n j : PrimeHorizonIndex N, A n j = f n j) {e e' : ℕ} (he : 0 < e) (he' : 0 < e') :
    ⟪Matrix.toEuclideanLin A (ramanujanHorizonVector e N), ramanujanHorizonVector e' N⟫ =
      (∑ n ∈ Finset.Icc 1 N, ∑ j ∈ Finset.Icc 1 N, ramanujanLagCoefficient e' n *
        ramanujanLagCoefficient e j * f n j / (Real.sqrt n * Real.sqrt j)) /
        (Real.sqrt e.totient * Real.sqrt e'.totient) := by
  rw [EuclideanSpace.inner_eq_star_dotProduct]
  change ∑ n : PrimeHorizonIndex N, ramanujanPoleProfile e' n *
    ∑ j : PrimeHorizonIndex N, A n j * ramanujanPoleProfile e j = _
  simp only [hA]
  rw [Finset.sum_coe_sort (Finset.Icc 1 N) (fun n => ramanujanPoleProfile e' n *
    ∑ j : PrimeHorizonIndex N, f n j * ramanujanPoleProfile e j), Finset.sum_div]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [Finset.sum_coe_sort (Finset.Icc 1 N) (fun j => f n j * ramanujanPoleProfile e j),
    Finset.mul_sum, Finset.sum_div]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [ramanujanPoleProfile_eq he, ramanujanPoleProfile_eq he']
  ring

theorem crossSingular_zero (φ : ℝ → ℝ) : crossSingular φ 0 = 0 := by
  simp [crossSingular]

/-- The Lipschitz constant of the singular profile on `[0, 1/2]`. -/
def farCrossLip (φ : ℝ → ℝ) : ℝ :=
  1 / (2 * ∫ u, φ u ^ 2) * ((1 / (1 - 1 / 2) ^ 2 + 1) * ∫ τ, |bumpAutocorr φ τ|)

theorem farCrossLip_nonneg (φ : ℝ → ℝ) : 0 ≤ farCrossLip φ := by
  have h1 : 0 ≤ ∫ u, φ u ^ 2 := integral_nonneg fun _ => sq_nonneg _
  have h2 : 0 ≤ ∫ τ, |bumpAutocorr φ τ| := integral_nonneg fun _ => abs_nonneg _
  unfold farCrossLip
  positivity

section Kernel

variable {φ : ℝ → ℝ} (hφ : ContDiff ℝ 2 φ) (hsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0)
  (hM : 0 < ∫ u, φ u ^ 2)
include hφ hsupp hM

omit hφ hsupp hM in
theorem inv_mem_Icc_zero_half {x : ℝ} (hx : 2 ≤ x) : 1 / x ∈ Set.Icc (0 : ℝ) (1 / 2) :=
  ⟨by have : 0 < x := by linarith
      positivity, one_div_le_one_div_of_le two_pos hx⟩

/-- `|σ(1/ℓ)| ≤ Lip/2` for `ℓ ≥ 2`. -/
theorem abs_crossSingular_inv_le {ℓ : ℝ} (hℓ : 2 ≤ ℓ) :
    |crossSingular φ (1 / ℓ)| ≤ farCrossLip φ / 2 := by
  have h1 := inv_mem_Icc_zero_half hℓ
  have h := abs_crossSingular_sub_le hφ hsupp hM (ρ := 1 / 2) (by norm_num) h1
    ⟨le_rfl, by norm_num⟩
  rw [crossSingular_zero, sub_zero, sub_zero, abs_of_nonneg h1.1] at h
  calc _ ≤ farCrossLip φ * (1 / ℓ) := h
    _ ≤ farCrossLip φ * (1 / 2) := mul_le_mul_of_nonneg_left h1.2 (farCrossLip_nonneg φ)
    _ = _ := by ring

/-- `ℓ ↦ σ(1/ℓ)` is `Lip/4`-Lipschitz on `[2, ∞)`. -/
theorem abs_crossSingular_inv_sub_le {x y : ℝ} (hx : 2 ≤ x) (hy : 2 ≤ y) :
    |crossSingular φ (1 / x) - crossSingular φ (1 / y)| ≤ farCrossLip φ / 4 * |x - y| := by
  have h := abs_crossSingular_sub_le hφ hsupp hM (ρ := 1 / 2) (by norm_num)
    (inv_mem_Icc_zero_half hx) (inv_mem_Icc_zero_half hy)
  have hx0 : x ≠ 0 := by linarith
  have hy0 : y ≠ 0 := by linarith
  have hxy0 : 0 < x * y := mul_pos (by linarith) (by linarith)
  have h4 : (4 : ℝ) ≤ x * y := by nlinarith
  have hxy : |1 / x - 1 / y| ≤ |x - y| / 4 := by
    have e : 1 / x - 1 / y = (y - x) / (x * y) := by field_simp
    rw [e, abs_div, abs_of_pos hxy0, abs_sub_comm]
    exact div_le_div_of_nonneg_left (abs_nonneg (x - y)) (by norm_num : (0 : ℝ) < 4) h4
  calc _ ≤ farCrossLip φ * |1 / x - 1 / y| := h
    _ ≤ farCrossLip φ * (|x - y| / 4) := mul_le_mul_of_nonneg_left hxy (farCrossLip_nonneg φ)
    _ = _ := by ring

end Kernel

/-- A pair sum over the window `(αw, βw]` with entries bounded by `D` is at most
`2DN(e^{βw} − 1)`. -/
theorem abs_sum_window_le {α β w D : ℝ} (hα : 0 ≤ α) (hαβ : α ≤ β) (hw : 0 < w) (hD : 0 ≤ D)
    {N : ℕ} (f : ℕ → ℕ → ℝ) (hf : ∀ n ∈ Finset.Icc 1 N, ∀ j ∈ Finset.Icc 1 N,
      α * w < |Real.log j - Real.log n| → |f n j| ≤ D) :
    |∑ n ∈ Finset.Icc 1 N, ∑ j ∈ Finset.Icc 1 N, if α * w < |Real.log j - Real.log n| ∧
        |Real.log j - Real.log n| ≤ β * w then f n j / (Real.sqrt n * Real.sqrt j) else 0| ≤
      2 * D * N * (Real.exp (β * w) - 1) := by
  have hcount : ∑ n ∈ Finset.Icc 1 N, ∑ j ∈ Finset.Icc 1 N, (if α * w < |Real.log j - Real.log n| ∧
      |Real.log j - Real.log n| ≤ β * w then 1 / (Real.sqrt n * Real.sqrt j) else 0) ≤
      2 * N * (Real.exp (β * w) - 1) := by
    have e : nearPairSum (fun _ => 1) α β w N (fun _ => 1) (fun _ => 1) (fun _ => 1) =
        ∑ n ∈ Finset.Icc 1 N, ∑ j ∈ Finset.Icc 1 N, (if α * w < |Real.log j - Real.log n| ∧
          |Real.log j - Real.log n| ≤ β * w then 1 / (Real.sqrt n * Real.sqrt j) else 0) := by
      simp only [nearPairSum, mul_one]
    rw [← e, nearPairSum_eq_rows _ hα hw]
    have hrow : ∀ m ∈ Finset.Icc 1 N,
        rowWindow (fun _ => 1) α β w N m (fun _ => 1) ≤ Real.exp (β * w) - 1 := by
      intro m hm
      have h := abs_rowWindow_le (K := fun _ => (1 : ℝ)) (A := 1) (B := 1)
        (p := fun _ => (1 : ℝ)) hw hα hαβ
        (fun _ _ => by norm_num) (fun _ => by norm_num) (N := N) (Finset.mem_Icc.mp hm).1
      linarith [le_abs_self (rowWindow (fun _ => 1) α β w N m (fun _ => 1))]
    calc ∑ m ∈ Finset.Icc 1 N, (fun _ => (1 : ℝ)) m *
          ((fun _ => (1 : ℝ)) m * rowWindow (fun _ => 1) α β w N m (fun _ => 1) +
            (fun _ => (1 : ℝ)) m * rowWindow (fun _ => 1) α β w N m (fun _ => 1))
        ≤ ∑ _m ∈ Finset.Icc 1 N, 2 * (Real.exp (β * w) - 1) :=
          Finset.sum_le_sum fun m hm => by simp only [one_mul]; linarith [hrow m hm]
      _ = 2 * N * (Real.exp (β * w) - 1) := by
          rw [Finset.sum_const, Nat.card_Icc, Nat.add_sub_cancel, nsmul_eq_mul]; ring
  calc _ ≤ ∑ n ∈ Finset.Icc 1 N, ∑ j ∈ Finset.Icc 1 N, D * (if α * w < |Real.log j - Real.log n| ∧
        |Real.log j - Real.log n| ≤ β * w then 1 / (Real.sqrt n * Real.sqrt j) else 0) := by
        refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun n hn => ?_)
        refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j hj => ?_)
        split_ifs with h
        · have hn0 : (0 : ℝ) < n := by exact_mod_cast (Finset.mem_Icc.mp hn).1
          have hj0 : (0 : ℝ) < j := by exact_mod_cast (Finset.mem_Icc.mp hj).1
          have hs : 0 < Real.sqrt n * Real.sqrt j := by positivity
          rw [abs_div, abs_of_pos hs, mul_one_div]
          exact div_le_div_of_nonneg_right (hf n hn j hj h.1) hs.le
        · simp
    _ = D * ∑ n ∈ Finset.Icc 1 N, ∑ j ∈ Finset.Icc 1 N, (if α * w < |Real.log j - Real.log n| ∧
        |Real.log j - Real.log n| ≤ β * w then 1 / (Real.sqrt n * Real.sqrt j) else 0) := by
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun n _ => by rw [Finset.mul_sum]
    _ ≤ D * (2 * N * (Real.exp (β * w) - 1)) := mul_le_mul_of_nonneg_left hcount hD
    _ = _ := by ring

/-- `|Σ_{m ≤ N} p(m) − N p̄| ≤ 2qB` for a `q`-periodic `p` bounded by `B`. -/
theorem abs_sum_Icc_sub_mean_le {p : ℕ → ℝ} {q : ℕ} (hq : 0 < q) (hp : ∀ n, p (n + q) = p n)
    {B : ℝ} (hpB : ∀ n, |p n| ≤ B) (N : ℕ) :
    |∑ m ∈ Finset.Icc 1 N, p m - N * periodicMean p q| ≤ 2 * q * B := by
  have h := abs_sum_range_shift_sub_mean_le hq hp hpB 1 N
  have e : ∑ i ∈ range N, (p (1 + i) - periodicMean p q) =
      ∑ m ∈ Finset.Icc 1 N, p m - N * periodicMean p q := by
    rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul,
      ← sum_range_succ_eq_sum_Icc]
    congr 1
    exact Finset.sum_congr rfl fun i _ => by rw [add_comm]
  rwa [e] at h

theorem abs_sum_Icc_le {p : ℕ → ℝ} {B : ℝ} (hpB : ∀ n, |p n| ≤ B) (N : ℕ) :
    |∑ m ∈ Finset.Icc 1 N, p m| ≤ N * B := by
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  calc ∑ m ∈ Finset.Icc 1 N, |p m| ≤ ∑ _m ∈ Finset.Icc 1 N, B :=
        Finset.sum_le_sum fun m _ => hpB m
    _ = N * B := by rw [Finset.sum_const, Nat.card_Icc, Nat.add_sub_cancel, nsmul_eq_mul]

/-- **The row integral against the periodic means.** With `I = ∫_2^T σ(1/ℓ) w e^{wℓ/2} dℓ`,
`I · Σ_{m ≤ N}(u(m)v̄ + v(m)ū) = 2wN ūv̄ F_φ` up to `O(w²T²N + q + wN/T)`. -/
theorem abs_farMain_sub_le {φ : ℝ → ℝ} (hφ : ContDiff ℝ 2 φ)
    (hsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0) (hM : 0 < ∫ u, φ u ^ 2) {T w : ℝ} (hT : 2 ≤ T)
    (hw : 0 < w) (hTw : T * w ≤ 1) {u v : ℕ → ℝ} {q : ℕ} (hq : 0 < q)
    (hu : ∀ n, u (n + q) = u n) (hv : ∀ n, v (n + q) = v n) {B : ℝ}
    (huB : ∀ n, |u n| ≤ B) (hvB : ∀ n, |v n| ≤ B)
    (hubar : |periodicMean u q| ≤ 1) (hvbar : |periodicMean v q| ≤ 1) (N : ℕ) :
    |(∫ ℓ in (2 : ℝ)..T, crossSingular φ (1 / ℓ) * (w * Real.exp (w * ℓ / 2))) *
        ∑ m ∈ Finset.Icc 1 N, (u m * periodicMean v q + v m * periodicMean u q) -
      2 * (w * N) * (periodicMean u q * periodicMean v q) * farCrossFinitePart φ| ≤
      farCrossLip φ * B * (w ^ 2 * T ^ 2 * N) + 2 * q * B * farCrossLip φ + 4 * (w * N) / T := by
  have hLσ := farCrossLip_nonneg φ
  set Lσ := farCrossLip φ
  have hB : 0 ≤ B := (abs_nonneg _).trans (huB 0)
  have hT0 : 0 < T := by linarith
  have hKb : ∀ ℓ, 2 ≤ ℓ → |crossSingular φ (1 / ℓ)| ≤ Lσ / 2 :=
    fun ℓ h => abs_crossSingular_inv_le hφ hsupp hM h
  have hKL : ∀ x ∈ Set.Icc (2 : ℝ) T, ∀ y ∈ Set.Icc (2 : ℝ) T,
      |crossSingular φ (1 / x) - crossSingular φ (1 / y)| ≤ Lσ / 4 * |x - y| :=
    fun x hx y hy => abs_crossSingular_inv_sub_le hφ hsupp hM hx.1 hy.1
  have hKc : ContinuousOn (fun ℓ => crossSingular φ (1 / ℓ)) (Set.Icc 2 T) :=
    continuousOn_of_abs_sub_le hKL
  set ubar := periodicMean u q
  set vbar := periodicMean v q
  set I := ∫ ℓ in (2 : ℝ)..T, crossSingular φ (1 / ℓ) * (w * Real.exp (w * ℓ / 2)) with hIdef
  set J := ∫ ℓ in (2 : ℝ)..T, crossSingular φ (1 / ℓ) with hJdef
  set F := farCrossFinitePart φ
  have hJF : |J - F| ≤ 2 / T := abs_integral_crossSingular_inv_sub_le hφ hsupp hM hT
  have hJ : |J| ≤ Lσ / 2 * T := by
    have h := intervalIntegral.norm_integral_le_of_norm_le_const (a := 2) (b := T)
      (f := fun ℓ => crossSingular φ (1 / ℓ)) (C := Lσ / 2) (fun x hx => by
        rw [Set.uIoc_of_le hT] at hx
        rw [Real.norm_eq_abs]; exact hKb x hx.1.le)
    rw [Real.norm_eq_abs, abs_of_nonneg (by linarith : (0 : ℝ) ≤ T - 2), ← hJdef] at h
    have := mul_le_mul_of_nonneg_left (by linarith : T - 2 ≤ T) (by linarith : (0 : ℝ) ≤ Lσ / 2)
    linarith
  have hIJ : |I - w * J| ≤ Lσ / 2 * w ^ 2 * T ^ 2 := by
    have hint1 : IntervalIntegrable (fun ℓ => crossSingular φ (1 / ℓ) * (w * Real.exp (w * ℓ / 2)))
        volume 2 T := by
      refine ContinuousOn.intervalIntegrable ?_
      rw [Set.uIcc_of_le hT]
      have hE : Continuous fun ℓ : ℝ => w * Real.exp (w * ℓ / 2) := by fun_prop
      exact hKc.mul hE.continuousOn
    have hint2 : IntervalIntegrable (fun ℓ => crossSingular φ (1 / ℓ)) volume 2 T := by
      refine ContinuousOn.intervalIntegrable ?_
      rw [Set.uIcc_of_le hT]; exact hKc
    have e : I - w * J = ∫ ℓ in (2 : ℝ)..T,
        (crossSingular φ (1 / ℓ) * (w * Real.exp (w * ℓ / 2)) - w * crossSingular φ (1 / ℓ)) := by
      rw [intervalIntegral.integral_sub hint1 (hint2.const_mul w),
        intervalIntegral.integral_const_mul]
    rw [e]
    have h := intervalIntegral.norm_integral_le_of_norm_le_const (a := 2) (b := T)
      (f := fun ℓ => crossSingular φ (1 / ℓ) * (w * Real.exp (w * ℓ / 2)) -
        w * crossSingular φ (1 / ℓ)) (C := Lσ / 2 * w * (w * T)) (fun x hx => by
        rw [Set.uIoc_of_le hT] at hx
        have hx2 : 2 < x := hx.1
        have hxT : x ≤ T := hx.2
        have hx0 : 0 < x := by linarith
        have hwx : 0 < w * x / 2 := by have := mul_pos hw hx0; linarith
        have hwxT : w * x ≤ w * T := mul_le_mul_of_nonneg_left hxT hw.le
        have he : |Real.exp (w * x / 2) - 1| ≤ w * T := by
          have h0 : |w * x / 2| ≤ 1 := by rw [abs_of_pos hwx]; linarith
          refine (Real.abs_exp_sub_one_le h0).trans ?_
          rw [abs_of_pos hwx]; linarith
        rw [Real.norm_eq_abs]
        have e2 : crossSingular φ (1 / x) * (w * Real.exp (w * x / 2)) -
            w * crossSingular φ (1 / x) =
            w * crossSingular φ (1 / x) * (Real.exp (w * x / 2) - 1) := by ring
        rw [e2, abs_mul, abs_mul, abs_of_pos hw]
        calc w * |crossSingular φ (1 / x)| * |Real.exp (w * x / 2) - 1|
            ≤ w * (Lσ / 2) * (w * T) :=
              mul_le_mul (mul_le_mul_of_nonneg_left (hKb x hx2.le) hw.le) he (abs_nonneg _)
                (mul_nonneg hw.le (by linarith))
          _ = Lσ / 2 * w * (w * T) := by ring)
    rw [Real.norm_eq_abs, abs_of_nonneg (by linarith : (0 : ℝ) ≤ T - 2)] at h
    have hnn : 0 ≤ Lσ / 2 * w * (w * T) := by
      have := mul_pos hw (mul_pos hw hT0); nlinarith
    calc _ ≤ Lσ / 2 * w * (w * T) * (T - 2) := h
      _ ≤ Lσ / 2 * w * (w * T) * T := mul_le_mul_of_nonneg_left (by linarith) hnn
      _ = _ := by ring
  -- the periodic sums
  set Su := ∑ m ∈ Finset.Icc 1 N, u m
  set Sv := ∑ m ∈ Finset.Icc 1 N, v m
  have hSu := abs_sum_Icc_sub_mean_le hq hu huB N
  have hSv := abs_sum_Icc_sub_mean_le hq hv hvB N
  have hSig : ∑ m ∈ Finset.Icc 1 N, (u m * vbar + v m * ubar) = vbar * Su + ubar * Sv := by
    rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
    congr 1 <;> exact Finset.sum_congr rfl fun m _ => by ring
  have hSigb : |vbar * Su + ubar * Sv| ≤ 2 * N * B := by
    have h1 := abs_sum_Icc_le huB N
    have h2 := abs_sum_Icc_le hvB N
    calc |vbar * Su + ubar * Sv| ≤ |vbar| * |Su| + |ubar| * |Sv| := by
          rw [← abs_mul, ← abs_mul]; exact abs_add_le _ _
      _ ≤ 1 * (N * B) + 1 * (N * B) := by gcongr
      _ = 2 * N * B := by ring
  rw [hSig]
  have e : I * (vbar * Su + ubar * Sv) - 2 * (w * N) * (ubar * vbar) * F =
      (I - w * J) * (vbar * Su + ubar * Sv) +
        w * J * (vbar * (Su - N * ubar) + ubar * (Sv - N * vbar)) + 2 * (w * N) * (ubar * vbar) * (J - F) := by
    ring
  rw [e]
  have b1 : |(I - w * J) * (vbar * Su + ubar * Sv)| ≤ Lσ * B * (w ^ 2 * T ^ 2 * N) := by
    rw [abs_mul]
    calc |I - w * J| * |vbar * Su + ubar * Sv| ≤ (Lσ / 2 * w ^ 2 * T ^ 2) * (2 * N * B) :=
          mul_le_mul hIJ hSigb (abs_nonneg _) (by positivity)
      _ = _ := by ring
  have b2 : |w * J * (vbar * (Su - N * ubar) + ubar * (Sv - N * vbar))| ≤ 2 * q * B * Lσ := by
    have hin : |vbar * (Su - N * ubar) + ubar * (Sv - N * vbar)| ≤ 4 * q * B := by
      calc _ ≤ |vbar| * |Su - N * ubar| + |ubar| * |Sv - N * vbar| := by
            rw [← abs_mul, ← abs_mul]; exact abs_add_le _ _
        _ ≤ 1 * (2 * q * B) + 1 * (2 * q * B) := by gcongr
        _ = 4 * q * B := by ring
    rw [abs_mul, abs_mul, abs_of_pos hw]
    calc w * |J| * |vbar * (Su - N * ubar) + ubar * (Sv - N * vbar)| ≤ w * (Lσ / 2 * T) * (4 * q * B) :=
          mul_le_mul (mul_le_mul_of_nonneg_left hJ hw.le) hin (abs_nonneg _)
            (mul_nonneg hw.le (mul_nonneg (by linarith) (by linarith)))
      _ = 2 * q * B * Lσ * (T * w) := by ring
      _ ≤ 2 * q * B * Lσ * 1 := mul_le_mul_of_nonneg_left hTw (by positivity)
      _ = _ := by ring
  have b3 : |2 * (w * N) * (ubar * vbar) * (J - F)| ≤ 4 * (w * N) / T := by
    have hubarvbar : |ubar * vbar| ≤ 1 := by rw [abs_mul]; nlinarith [abs_nonneg ubar, abs_nonneg vbar]
    rw [abs_mul, abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ 2 * (w * N))]
    calc 2 * (w * N) * |ubar * vbar| * |J - F| ≤ 2 * (w * N) * 1 * (2 / T) :=
          mul_le_mul (mul_le_mul_of_nonneg_left hubarvbar (by positivity)) hJF (abs_nonneg _)
            (by positivity)
      _ = _ := by ring
  calc _ ≤ |(I - w * J) * (vbar * Su + ubar * Sv) +
        w * J * (vbar * (Su - N * ubar) + ubar * (Sv - N * vbar))| +
        |2 * (w * N) * (ubar * vbar) * (J - F)| := abs_add_le _ _
    _ ≤ |(I - w * J) * (vbar * Su + ubar * Sv)| +
        |w * J * (vbar * (Su - N * ubar) + ubar * (Sv - N * vbar))| +
        |2 * (w * N) * (ubar * vbar) * (J - F)| := add_le_add (abs_add_le _ _) le_rfl
    _ ≤ _ := add_le_add (add_le_add b1 b2) b3

/-- The constant of the far cross estimate. -/
def farCrossConstant (φ : ℝ → ℝ) (q : ℕ) (B : ℝ) : ℝ :=
  2 * B * (2 * B * (farCrossLip φ / 2) +
      2 * (2 * q + 1) * B * (4 * (farCrossLip φ / 2) + 2 * (farCrossLip φ / 4)) +
      8 * B * (farCrossLip φ / 2)) +
    (farCrossLip φ * B + 2 * q * B * farCrossLip φ + 4) +
    4 * B ^ 2 * (5 / 2 * (∫ t, |bumpAutocorr φ t|) / (∫ u, φ u ^ 2)) +
    48 * B ^ 2 * (152 * (∫ u, |φ u|) ^ 2 / (∫ u, φ u ^ 2))

/-- The far pairs split into the window `(2w, Tw]` read by the singular profile, the window
error, and the tail beyond `Tw`. -/
theorem farCrossSum_eq (φ : ℝ → ℝ) {T w : ℝ} (hT : 2 ≤ T) (hw : 0 < w) (N : ℕ) (u v : ℕ → ℝ) :
    ∑ n ∈ Finset.Icc 1 N, ∑ j ∈ Finset.Icc 1 N, u n * v j *
        (if 2 * w < |Real.log j - Real.log n| then
          atomCrossErrorKernel (atomDilate φ w) n j else 0) / (Real.sqrt n * Real.sqrt j) =
      nearPairSum (fun ℓ => crossSingular φ (1 / ℓ)) 2 T w N u v (fun _ => 1) +
      (∑ n ∈ Finset.Icc 1 N, ∑ j ∈ Finset.Icc 1 N,
        if 2 * w < |Real.log j - Real.log n| ∧ |Real.log j - Real.log n| ≤ T * w then
          u n * v j * (atomCrossErrorKernel (atomDilate φ w) n j -
            crossSingular φ (w / |Real.log j - Real.log n|)) / (Real.sqrt n * Real.sqrt j)
        else 0) +
      (∑ n ∈ Finset.Icc 1 N, ∑ j ∈ Finset.Icc 1 N, if T * w < |Real.log j - Real.log n| then
        u n * v j * atomCrossErrorKernel (atomDilate φ w) n j / (Real.sqrt n * Real.sqrt j)
        else 0) := by
  simp only [nearPairSum, one_mul, one_div_div, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun n _ => Finset.sum_congr rfl fun j _ => ?_
  have h2T : 2 * w ≤ T * w := mul_le_mul_of_nonneg_right hT hw.le
  by_cases h2 : 2 * w < |Real.log j - Real.log n|
  · by_cases hT' : |Real.log j - Real.log n| ≤ T * w
    · rw [if_pos h2, if_pos ⟨h2, hT'⟩, if_pos ⟨h2, hT'⟩, if_neg (not_lt.mpr hT')]; ring
    · rw [if_pos h2, if_neg (fun h => hT' h.2), if_neg (fun h => hT' h.2),
        if_pos (not_le.mp hT')]; ring
  · rw [if_neg h2, if_neg (fun h => h2 h.1), if_neg (fun h => h2 h.1),
      if_neg (fun h => h2 (lt_of_le_of_lt h2T h))]; ring

/-- The window error: the far entries differ from the singular profile by `O(w)`. -/
theorem abs_farWindowError_le {φ : ℝ → ℝ} (hφ : ContDiff ℝ 2 φ)
    (hsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0) (hM : 0 < ∫ u, φ u ^ 2) {T w B : ℝ} (hT : 2 ≤ T)
    (hw : 0 < w) {u v : ℕ → ℝ} (huB : ∀ n, |u n| ≤ B) (hvB : ∀ n, |v n| ≤ B) (N : ℕ) :
    |∑ n ∈ Finset.Icc 1 N, ∑ j ∈ Finset.Icc 1 N,
        if 2 * w < |Real.log j - Real.log n| ∧ |Real.log j - Real.log n| ≤ T * w then
          u n * v j * (atomCrossErrorKernel (atomDilate φ w) n j -
            crossSingular φ (w / |Real.log j - Real.log n|)) / (Real.sqrt n * Real.sqrt j)
        else 0| ≤
      2 * (B * B * (5 / 2 * (∫ t, |bumpAutocorr φ t|) / (∫ u, φ u ^ 2) * w)) * N *
        (Real.exp (T * w) - 1) := by
  have hB : 0 ≤ B := (abs_nonneg _).trans (huB 0)
  have hC : 0 ≤ 5 / 2 * (∫ t, |bumpAutocorr φ t|) / (∫ u, φ u ^ 2) * w := by
    have : 0 ≤ ∫ t, |bumpAutocorr φ t| := integral_nonneg fun t => abs_nonneg _
    have : 0 ≤ ∫ u, φ u ^ 2 := hM.le
    positivity
  refine abs_sum_window_le (α := 2) (β := T) (by norm_num) hT hw (mul_nonneg (mul_nonneg hB hB) hC)
    (fun n j => u n * v j * (atomCrossErrorKernel (atomDilate φ w) n j -
      crossSingular φ (w / |Real.log j - Real.log n|))) fun n hn j hj hlt => ?_
  have hn1 := (Finset.mem_Icc.mp hn).1
  have hj1 := (Finset.mem_Icc.mp hj).1
  have hnj : n ≠ j := by
    rintro rfl
    rw [sub_self, abs_zero] at hlt
    linarith
  have hws : w < |Real.log j - Real.log n| := by linarith
  have hcr := abs_atomCrossErrorKernel_sub_crossSingular_le hφ hsupp hM hw hn1 hj1 hnj hws
  rw [abs_mul, abs_mul]
  exact mul_le_mul (mul_le_mul (huB n) (hvB j) (abs_nonneg _) hB) hcr (abs_nonneg _)
    (mul_nonneg hB hB)

/-- The near pair error of the window, in units of `√c(1 + log c) + c³/N`. -/
theorem farCross_nearError_le {Lσ B T c w : ℝ} {q N : ℕ} (hLσ : 0 ≤ Lσ) (hB : 0 ≤ B)
    (hT2 : 2 ≤ T) (hTT : T * T = c) (hw : 0 < w) (hwN : w * N = c) (hN0 : (0 : ℝ) < N) :
    2 * 1 * B * (2 * B * (Lσ / 2) + (2 * q + 1) * B * (4 * (Lσ / 2) + 2 * T * (Lσ / 4)) *
      (1 + Real.log (2 * T * w * N)) + (T * w * N + 1) * (4 * B * (Lσ / 2) * T * w)) ≤
      2 * B * (2 * B * (Lσ / 2) + 2 * (2 * q + 1) * B * (4 * (Lσ / 2) + 2 * (Lσ / 4)) +
        8 * B * (Lσ / 2)) * (T * (1 + Real.log c) + c ^ 3 / N) := by
  obtain ⟨E, hE⟩ : ∃ E, E = T * (1 + Real.log c) + c ^ 3 / N := ⟨_, rfl⟩
  rw [← hE]
  have hT0 : 0 < T := by linarith
  have hc4 : 4 ≤ c := by nlinarith
  have hc0 : 0 < c := by linarith
  have hlogc : 0 ≤ Real.log c := Real.log_nonneg (by linarith)
  have hlogT : Real.log T = Real.log c / 2 := by
    rw [← hTT, Real.log_mul hT0.ne' hT0.ne']; ring
  have hTL : 0 ≤ T * Real.log c := mul_nonneg hT0.le hlogc
  have hQ0 : 0 ≤ c ^ 3 / N := by positivity
  have hPE : T * (1 + Real.log c) ≤ E := by rw [hE]; linarith
  have hQE : c ^ 3 / N ≤ E := by rw [hE]; linarith
  have hE1 : 1 ≤ E := by rw [hE]; linarith
  have hTc : T * w * N = T * c := by rw [mul_assoc, hwN]
  have h2Tc : 2 * T * w * N = 2 * T * c := by rw [mul_assoc (2 * T), hwN]
  have h8 : 8 ≤ T * c := by have := mul_le_mul hT2 hc4 (by norm_num) hT0.le; linarith
  have hlog2 : Real.log 2 ≤ 1 := by have := Real.log_two_lt_d9; linarith
  have hlogbd : 1 + Real.log (2 * T * w * N) ≤ 2 * (1 + Real.log c) := by
    rw [h2Tc, Real.log_mul (by positivity) hc0.ne', Real.log_mul (by norm_num) hT0.ne', hlogT]
    linarith
  have hlog0 : 0 ≤ 1 + Real.log (2 * T * w * N) := by
    have : 0 ≤ Real.log (2 * T * w * N) := Real.log_nonneg (by rw [h2Tc]; linarith)
    linarith
  have hQ : T * c * (T * w) = c ^ 3 / N := by
    have hw' : w = c / N := by rw [← hwN]; field_simp
    rw [hw', ← hTT]; field_simp
  have t1 : 2 * B * (Lσ / 2) ≤ 2 * B * (Lσ / 2) * E :=
    le_mul_of_one_le_right (by positivity) hE1
  have hfac : 4 * (Lσ / 2) + 2 * T * (Lσ / 4) ≤ (4 * (Lσ / 2) + 2 * (Lσ / 4)) * T := by
    have := mul_le_mul_of_nonneg_left (show (1 : ℝ) ≤ T by linarith) hLσ
    linarith
  have hq0 : (0 : ℝ) ≤ (2 * q + 1) * B := by positivity
  have t2 : (2 * q + 1) * B * (4 * (Lσ / 2) + 2 * T * (Lσ / 4)) * (1 + Real.log (2 * T * w * N)) ≤
      2 * (2 * q + 1) * B * (4 * (Lσ / 2) + 2 * (Lσ / 4)) * E := by
    calc (2 * q + 1) * B * (4 * (Lσ / 2) + 2 * T * (Lσ / 4)) * (1 + Real.log (2 * T * w * N))
        ≤ (2 * q + 1) * B * ((4 * (Lσ / 2) + 2 * (Lσ / 4)) * T) * (2 * (1 + Real.log c)) :=
          mul_le_mul (mul_le_mul_of_nonneg_left hfac hq0) hlogbd hlog0
            (mul_nonneg hq0 (by positivity))
      _ = 2 * (2 * q + 1) * B * (4 * (Lσ / 2) + 2 * (Lσ / 4)) * (T * (1 + Real.log c)) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hPE (by positivity)
  have t3 : (T * w * N + 1) * (4 * B * (Lσ / 2) * T * w) ≤ 8 * B * (Lσ / 2) * E := by
    have h0 : 0 ≤ 4 * B * (Lσ / 2) * T * w := by positivity
    calc (T * w * N + 1) * (4 * B * (Lσ / 2) * T * w)
        ≤ (2 * (T * c)) * (4 * B * (Lσ / 2) * T * w) :=
          mul_le_mul_of_nonneg_right (by rw [hTc]; linarith) h0
      _ = 8 * B * (Lσ / 2) * (T * c * (T * w)) := by ring
      _ = 8 * B * (Lσ / 2) * (c ^ 3 / N) := by rw [hQ]
      _ ≤ _ := mul_le_mul_of_nonneg_left hQE (by positivity)
  have hsum := mul_le_mul_of_nonneg_left (add_le_add (add_le_add t1 t2) t3)
    (show (0 : ℝ) ≤ 2 * B by positivity)
  calc _ = 2 * B * (2 * B * (Lσ / 2) + (2 * q + 1) * B * (4 * (Lσ / 2) + 2 * T * (Lσ / 4)) *
        (1 + Real.log (2 * T * w * N)) + (T * w * N + 1) * (4 * B * (Lσ / 2) * T * w)) := by ring
    _ ≤ _ := hsum
    _ = _ := by ring

/-- The main-term error in units of `√c(1 + log c) + c³/N`. -/
theorem farCross_mainError_le {Lσ B T c w : ℝ} {q N : ℕ} (hLσ : 0 ≤ Lσ) (hB : 0 ≤ B)
    (hT2 : 2 ≤ T) (hTT : T * T = c) (hwN : w * N = c) (hN0 : (0 : ℝ) < N) :
    Lσ * B * (w ^ 2 * T ^ 2 * N) + 2 * q * B * Lσ + 4 * c / T ≤
      (Lσ * B + 2 * q * B * Lσ + 4) * (T * (1 + Real.log c) + c ^ 3 / N) := by
  obtain ⟨E, hE⟩ : ∃ E, E = T * (1 + Real.log c) + c ^ 3 / N := ⟨_, rfl⟩
  rw [← hE]
  have hT0 : 0 < T := by linarith
  have hc0 : 0 < c := by nlinarith
  have hlogc : 0 ≤ Real.log c := Real.log_nonneg (by nlinarith)
  have hTL : 0 ≤ T * Real.log c := mul_nonneg hT0.le hlogc
  have hQ0 : 0 ≤ c ^ 3 / N := by positivity
  have hTE : T ≤ E := by rw [hE]; linarith
  have hQE : c ^ 3 / N ≤ E := by rw [hE]; linarith
  have hE1 : 1 ≤ E := by linarith
  have hQ : w ^ 2 * T ^ 2 * N = c ^ 3 / N := by
    have hw' : w = c / N := by rw [← hwN]; field_simp
    rw [hw', show T ^ 2 = c by rw [sq]; exact hTT]; field_simp
  have e1 : 4 * c / T = 4 * T := by rw [← hTT]; field_simp
  rw [hQ, e1]
  have h1 : Lσ * B * (c ^ 3 / N) ≤ Lσ * B * E := mul_le_mul_of_nonneg_left hQE (by positivity)
  have h2 : 2 * q * B * Lσ ≤ 2 * q * B * Lσ * E := le_mul_of_one_le_right (by positivity) hE1
  have h3 : 4 * T ≤ 4 * E := by linarith
  calc _ ≤ Lσ * B * E + 2 * q * B * Lσ * E + 4 * E := by linarith
    _ = _ := by ring

/-- **The far cross sum.** For `q`-periodic weights bounded by `B` with means `|ū|, |v̄| ≤ 1`,
`c ≥ 4` and `√c · c ≤ N`, the far pair sum of the cross error is `2c ūv̄ F_φ` up to
`O(√c (1 + log c) + c³/N)`. -/
theorem abs_farCrossSum_sub_le {φ : ℝ → ℝ} (hφ : ContDiff ℝ 2 φ)
    (hsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0) (hM : 0 < ∫ u, φ u ^ 2) {u v : ℕ → ℝ} {q : ℕ}
    (hq : 0 < q) (hu : ∀ n, u (n + q) = u n) (hv : ∀ n, v (n + q) = v n) {B : ℝ}
    (huB : ∀ n, |u n| ≤ B) (hvB : ∀ n, |v n| ≤ B)
    (hubar : |periodicMean u q| ≤ 1) (hvbar : |periodicMean v q| ≤ 1)
    {c : ℝ} (hc : 4 ≤ c) {N : ℕ} (hcN : Real.sqrt c * c ≤ N) :
    |∑ n ∈ Finset.Icc 1 N, ∑ j ∈ Finset.Icc 1 N, u n * v j *
        (if 2 * (c / N) < |Real.log j - Real.log n| then
          atomCrossErrorKernel (atomDilate φ (c / N)) n j else 0) / (Real.sqrt n * Real.sqrt j) -
      2 * c * (periodicMean u q * periodicMean v q) * farCrossFinitePart φ| ≤
      farCrossConstant φ q B * (Real.sqrt c * (1 + Real.log c) + c ^ 3 / N) := by
  have hLσ := farCrossLip_nonneg φ
  have hB : 0 ≤ B := (abs_nonneg _).trans (huB 0)
  have hC₁ : 0 ≤ 5 / 2 * (∫ t, |bumpAutocorr φ t|) / (∫ u, φ u ^ 2) := by
    have : 0 ≤ ∫ t, |bumpAutocorr φ t| := integral_nonneg fun t => abs_nonneg _
    have : 0 ≤ ∫ u, φ u ^ 2 := hM.le
    positivity
  have hC₂ : 0 ≤ 152 * (∫ u, |φ u|) ^ 2 / (∫ u, φ u ^ 2) := by
    have : 0 ≤ ∫ u, φ u ^ 2 := hM.le
    positivity
  have hc0 : 0 < c := by linarith
  obtain ⟨T, hTdef⟩ : ∃ T, T = Real.sqrt c := ⟨_, rfl⟩
  rw [← hTdef] at hcN ⊢
  have hT0 : 0 ≤ T := by rw [hTdef]; exact Real.sqrt_nonneg c
  have hTT : T * T = c := by rw [hTdef]; exact Real.mul_self_sqrt hc0.le
  have hT2 : 2 ≤ T := by nlinarith
  have hTc : T ≤ c := by nlinarith
  have h8 : (8 : ℝ) ≤ T * c := by have := mul_le_mul hT2 hc (by norm_num) hT0; linarith
  have hN0 : (0 : ℝ) < N := by linarith
  have hN : 1 ≤ N := by exact_mod_cast (show (1 : ℝ) ≤ N by linarith)
  obtain ⟨w, hwdef⟩ : ∃ w, w = c / N := ⟨_, rfl⟩
  rw [← hwdef]
  have hw : 0 < w := by rw [hwdef]; exact div_pos hc0 hN0
  have hwN : w * N = c := by rw [hwdef]; field_simp
  have hTw : T * w ≤ 1 := by
    rw [hwdef, ← mul_div_assoc, div_le_one hN0]; exact hcN
  obtain ⟨E, hE⟩ : ∃ E, E = T * (1 + Real.log c) + c ^ 3 / N := ⟨_, rfl⟩
  rw [← hE]
  have hlogc : 0 ≤ Real.log c := Real.log_nonneg (by linarith)
  have hTL : 0 ≤ T * Real.log c := mul_nonneg hT0 hlogc
  have hQ0 : 0 ≤ c ^ 3 / N := by positivity
  have hTE : T ≤ E := by rw [hE]; linarith
  have hQE : c ^ 3 / N ≤ E := by rw [hE]; linarith
  have hc2E : c ^ 2 / N ≤ E := by
    have : c ^ 2 / N ≤ c ^ 3 / N := div_le_div_of_nonneg_right
      (pow_le_pow_right₀ (by linarith : (1 : ℝ) ≤ c) (by norm_num : 2 ≤ 3)) hN0.le
    linarith
  rw [farCrossSum_eq φ hT2 hw N u v]
  -- the window, averaged
  have hTwN : 1 ≤ 2 * T * w * N := by
    rw [mul_assoc (2 * T), hwN]; linarith
  have hNPb := abs_nearPairSum_sub_le (K := fun ℓ => crossSingular φ (1 / ℓ)) (α := 2) (β := T)
    (A := farCrossLip φ / 2) (L := farCrossLip φ / 4) (by norm_num) hT2 (by linarith) hw hTw
    (fun ℓ hℓ => abs_crossSingular_inv_le hφ hsupp hM hℓ.1)
    (fun x hx y hy => abs_crossSingular_inv_sub_le hφ hsupp hM hx.1 hy.1) (by positivity)
    hq hu hv huB hvB (ρ := fun _ => 1) (R := 1) (fun _ => by norm_num) hN hTwN
  simp only [one_mul] at hNPb
  have hk1 := farCross_nearError_le (q := q) hLσ hB hT2 hTT hw hwN hN0
  rw [← hE] at hk1
  have hmain := abs_farMain_sub_le hφ hsupp hM hT2 hw hTw hq hu hv huB hvB hubar hvbar N
  rw [hwN] at hmain
  have hk2 := farCross_mainError_le (q := q) (w := w) hLσ hB hT2 hTT hwN hN0
  rw [← hE] at hk2
  -- the window error
  have hD := abs_farWindowError_le hφ hsupp hM hT2 hw huB hvB N
  have hD' : 2 * (B * B * (5 / 2 * (∫ t, |bumpAutocorr φ t|) / (∫ u, φ u ^ 2) * w)) * N *
      (Real.exp (T * w) - 1) ≤ 4 * B ^ 2 * (5 / 2 * (∫ t, |bumpAutocorr φ t|) / (∫ u, φ u ^ 2)) * E := by
    have hTw0 : 0 < T * w := mul_pos (by linarith) hw
    have hexp : Real.exp (T * w) - 1 ≤ 2 * (T * w) := by
      have h0 : |T * w| ≤ 1 := by rw [abs_of_pos hTw0]; exact hTw
      have := Real.abs_exp_sub_one_le h0
      rw [abs_of_pos hTw0] at this
      linarith [le_abs_self (Real.exp (T * w) - 1)]
    have hTc2 : T * c ^ 2 ≤ c ^ 3 := by
      have := mul_le_mul_of_nonneg_right hTc (sq_nonneg c)
      linarith [show c * c ^ 2 = c ^ 3 by ring]
    have hw' : w = c / N := hwdef
    calc _ ≤ 2 * (B * B * (5 / 2 * (∫ t, |bumpAutocorr φ t|) / (∫ u, φ u ^ 2) * w)) * N *
          (2 * (T * w)) := mul_le_mul_of_nonneg_left hexp (by positivity)
      _ = 4 * B ^ 2 * (5 / 2 * (∫ t, |bumpAutocorr φ t|) / (∫ u, φ u ^ 2)) * (T * (w * N) * w) := by
          ring
      _ = 4 * B ^ 2 * (5 / 2 * (∫ t, |bumpAutocorr φ t|) / (∫ u, φ u ^ 2)) * (T * c ^ 2 / N) := by
          rw [hwN, hw']; ring
      _ ≤ _ := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          have : T * c ^ 2 / N ≤ c ^ 3 / N := div_le_div_of_nonneg_right hTc2 hN0.le
          linarith
  -- the tail
  have hTl := abs_farCross_pair_tail_le hφ hsupp hM hc0 hT2 hN huB hvB
  rw [← hwdef] at hTl
  have hTl' : B ^ 2 * (152 * (∫ u, |φ u|) ^ 2 / (∫ u, φ u ^ 2)) * (16 * c / T + 32 * c ^ 2 / N) ≤
      48 * B ^ 2 * (152 * (∫ u, |φ u|) ^ 2 / (∫ u, φ u ^ 2)) * E := by
    have e1 : 16 * c / T = 16 * T := by rw [← hTT]; field_simp
    have e2 : 32 * c ^ 2 / N = 32 * (c ^ 2 / N) := by ring
    rw [e1, e2]
    have : 16 * T + 32 * (c ^ 2 / N) ≤ 48 * E := by linarith
    calc _ ≤ B ^ 2 * (152 * (∫ u, |φ u|) ^ 2 / (∫ u, φ u ^ 2)) * (48 * E) :=
          mul_le_mul_of_nonneg_left this (by positivity)
      _ = _ := by ring
  have hsum : farCrossConstant φ q B * E =
      2 * B * (2 * B * (farCrossLip φ / 2) +
        2 * (2 * q + 1) * B * (4 * (farCrossLip φ / 2) + 2 * (farCrossLip φ / 4)) +
        8 * B * (farCrossLip φ / 2)) * E +
      (farCrossLip φ * B + 2 * q * B * farCrossLip φ + 4) * E +
      4 * B ^ 2 * (5 / 2 * (∫ t, |bumpAutocorr φ t|) / (∫ u, φ u ^ 2)) * E +
      48 * B ^ 2 * (152 * (∫ u, |φ u|) ^ 2 / (∫ u, φ u ^ 2)) * E := by
    unfold farCrossConstant; ring
  rw [hsum]
  have key : ∀ X₁ X₂ X₃ SD ST : ℝ,
      |X₁ + SD + ST - X₃| ≤ |X₁ - X₂| + |X₂ - X₃| + |SD| + |ST| := by
    intro X₁ X₂ X₃ SD ST
    have e : X₁ + SD + ST - X₃ = (X₁ - X₂) + (X₂ - X₃) + SD + ST := by ring
    rw [e]
    have a1 := abs_add_le ((X₁ - X₂) + (X₂ - X₃) + SD) ST
    have a2 := abs_add_le ((X₁ - X₂) + (X₂ - X₃)) SD
    have a3 := abs_add_le (X₁ - X₂) (X₂ - X₃)
    linarith
  refine (key _ ((∫ ℓ in (2 : ℝ)..T, crossSingular φ (1 / ℓ) * (w * Real.exp (w * ℓ / 2))) *
    ∑ m ∈ Finset.Icc 1 N, (u m * periodicMean v q + v m * periodicMean u q)) _ _ _).trans ?_
  exact add_le_add (add_le_add (add_le_add (hNPb.trans hk1) (hmain.trans hk2)) (hD.trans hD'))
    (hTl.trans hTl')

/-- **The far cross error at a growing overlap.** For `c ≥ 4` and `√c · c ≤ N`,
`|⟨Cr^sep R_e, R_{e'}⟩ − 2[e = e' = 1] c F_φ| ≤ C (√c (1 + log c) + c³/N)`. -/
theorem abs_farCrossPairing_sub_le {φ : ℝ → ℝ} (hφ : ContDiff ℝ 2 φ)
    (hsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0) (hM : 0 < ∫ u, φ u ^ 2) {e e' : ℕ} (he : 0 < e)
    (he' : 0 < e') {c : ℝ} (hc : 4 ≤ c) {N : ℕ} (hcN : Real.sqrt c * c ≤ N) :
    |⟪Matrix.toEuclideanLin (separatedCrossErrorMatrix φ c N) (ramanujanHorizonVector e N),
        ramanujanHorizonVector e' N⟫ -
      c * (if e = 1 ∧ e' = 1 then 2 * farCrossFinitePart φ else 0)| ≤
      farCrossConstant φ (e' * e) ((∑ d ∈ e.divisors, (d : ℝ)) + ∑ d ∈ e'.divisors, (d : ℝ)) *
        (Real.sqrt c * (1 + Real.log c) + c ^ 3 / N) := by
  set B : ℝ := (∑ d ∈ e.divisors, (d : ℝ)) + ∑ d ∈ e'.divisors, (d : ℝ) with hBdef
  have hq : 0 < e' * e := Nat.mul_pos he' he
  have hu : ∀ n, ramanujanLagCoefficient e' (n + e' * e) = ramanujanLagCoefficient e' n :=
    fun n => ramanujanLagCoefficient_add_mul e' n e
  have hv : ∀ n, ramanujanLagCoefficient e (n + e' * e) = ramanujanLagCoefficient e n :=
    fun n => by rw [mul_comm]; exact ramanujanLagCoefficient_add_mul e n e'
  have huB : ∀ n, |ramanujanLagCoefficient e' n| ≤ B := fun n =>
    (abs_ramanujanLagCoefficient_le e' n).trans (le_add_of_nonneg_left (by positivity))
  have hvB : ∀ n, |ramanujanLagCoefficient e n| ≤ B := fun n =>
    (abs_ramanujanLagCoefficient_le e n).trans (le_add_of_nonneg_right (by positivity))
  have hubar := periodicMean_ramanujan_of_dvd he' hq (dvd_mul_right e' e)
  have hvbar := periodicMean_ramanujan_of_dvd he hq (dvd_mul_left e e')
  have hubar1 : |periodicMean (ramanujanLagCoefficient e') (e' * e)| ≤ 1 := by
    rw [hubar]; split_ifs <;> norm_num
  have hvbar1 : |periodicMean (ramanujanLagCoefficient e) (e' * e)| ≤ 1 := by
    rw [hvbar]; split_ifs <;> norm_num
  have hS := abs_farCrossSum_sub_le hφ hsupp hM hq hu hv huB hvB hubar1 hvbar1 hc hcN
  rw [inner_matrix_ramanujanHorizonVector_eq (separatedCrossErrorMatrix φ c N) (fun n j : ℕ =>
    if 2 * (c / N) < |Real.log j - Real.log n| then
      atomCrossErrorKernel (atomDilate φ (c / N)) n j else 0) (fun n j => rfl) he he']
  have h1 : (1 : ℝ) ≤ e.totient := by exact_mod_cast Nat.totient_pos.mpr he
  have h1' : (1 : ℝ) ≤ e'.totient := by exact_mod_cast Nat.totient_pos.mpr he'
  have hZ1 : 1 ≤ Real.sqrt e.totient * Real.sqrt e'.totient :=
    one_le_mul_of_one_le_of_one_le (Real.one_le_sqrt.mpr h1) (Real.one_le_sqrt.mpr h1')
  have hZ0 : 0 < Real.sqrt e.totient * Real.sqrt e'.totient := by linarith
  have hmain : c * (if e = 1 ∧ e' = 1 then 2 * farCrossFinitePart φ else 0) *
      (Real.sqrt e.totient * Real.sqrt e'.totient) =
      2 * c * (periodicMean (ramanujanLagCoefficient e') (e' * e) *
        periodicMean (ramanujanLagCoefficient e) (e' * e)) * farCrossFinitePart φ := by
    rw [hubar, hvbar]
    by_cases h1 : e = 1
    · by_cases h2 : e' = 1
      · subst h1 h2
        simp only [and_self, if_true, Nat.totient_one, Nat.cast_one, Real.sqrt_one, mul_one]
        ring
      · simp [h2]
    · simp [h1]
  set S := ∑ n ∈ Finset.Icc 1 N, ∑ j ∈ Finset.Icc 1 N, ramanujanLagCoefficient e' n *
    ramanujanLagCoefficient e j * (if 2 * (c / N) < |Real.log j - Real.log n| then
      atomCrossErrorKernel (atomDilate φ (c / N)) n j else 0) / (Real.sqrt n * Real.sqrt j)
  set m := c * (if e = 1 ∧ e' = 1 then 2 * farCrossFinitePart φ else 0)
  have e1 : S / (Real.sqrt e.totient * Real.sqrt e'.totient) - m =
      (S - m * (Real.sqrt e.totient * Real.sqrt e'.totient)) /
        (Real.sqrt e.totient * Real.sqrt e'.totient) := by
    rw [sub_div, mul_div_assoc, div_self hZ0.ne', mul_one]
  rw [e1, abs_div, abs_of_pos hZ0, hmain]
  exact (div_le_self (abs_nonneg _) hZ1).trans hS

/-- **The far cross error is linear in the overlap.** Along `c → ∞`, `c²/N → 0`:
`⟨Cr^sep R_e, R_{e'}⟩/c → 2[e = e' = 1] F_φ`. -/
theorem tendsto_farCrossPairing_div_overlap {φ : ℝ → ℝ} (hφ : ContDiff ℝ 2 φ)
    (hsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0) (hM : 0 < ∫ u, φ u ^ 2) {e e' : ℕ} (he : 0 < e)
    (he' : 0 < e') {c : ℕ → ℝ} (hcinf : Tendsto c atTop atTop)
    (hcN : Tendsto (fun N : ℕ => c N ^ 2 / N) atTop (𝓝 0)) :
    Tendsto (fun N : ℕ => ⟪Matrix.toEuclideanLin (separatedCrossErrorMatrix φ (c N) N)
        (ramanujanHorizonVector e N), ramanujanHorizonVector e' N⟫ / c N) atTop
      (𝓝 (if e = 1 ∧ e' = 1 then 2 * farCrossFinitePart φ else 0)) := by
  set C := farCrossConstant φ (e' * e) ((∑ d ∈ e.divisors, (d : ℝ)) + ∑ d ∈ e'.divisors, (d : ℝ))
  set m := if e = 1 ∧ e' = 1 then 2 * farCrossFinitePart φ else 0
  have h1 : Tendsto (fun x : ℝ => (1 + Real.log x) / Real.sqrt x) atTop (𝓝 0) := by
    have ha : Tendsto (fun x : ℝ => 1 / Real.sqrt x) atTop (𝓝 0) := by
      simpa only [one_div, Function.comp_def] using
        tendsto_inv_atTop_zero.comp Real.tendsto_sqrt_atTop
    have hb : Tendsto (fun x : ℝ => Real.log x / Real.sqrt x) atTop (𝓝 0) := by
      refine (isLittleO_log_rpow_atTop (r := 1 / 2) (by norm_num)).tendsto_div_nhds_zero.congr
        fun x => ?_
      rw [Real.sqrt_eq_rpow]
    have := ha.add hb
    rw [add_zero] at this
    exact this.congr fun x => by rw [add_div]
  have hr : Tendsto (fun N : ℕ => C * ((1 + Real.log (c N)) / Real.sqrt (c N) + c N ^ 2 / N))
      atTop (𝓝 0) := by
    have := ((h1.comp hcinf).add hcN).const_mul C
    simpa only [Function.comp_def, add_zero, mul_zero] using this
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero' (Eventually.of_forall fun N => norm_nonneg _) ?_ hr
  filter_upwards [hcinf.eventually_ge_atTop 4, hcN.eventually (gt_mem_nhds zero_lt_one),
    eventually_ge_atTop 1] with N h4 h2 hN1
  have hc0 : 0 < c N := by linarith
  have hcne : c N ≠ 0 := hc0.ne'
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN1
  have hs := Real.mul_self_sqrt hc0.le
  have hs0 := Real.sqrt_nonneg (c N)
  have hcN' : Real.sqrt (c N) * c N ≤ N := by
    have h2' : c N ^ 2 < N := by rwa [div_lt_one hN0] at h2
    have hsq2 : 2 ≤ Real.sqrt (c N) := by nlinarith
    have hsc : Real.sqrt (c N) ≤ c N := by nlinarith
    have := mul_le_mul_of_nonneg_right hsc hc0.le
    linarith [show c N * c N = c N ^ 2 by ring]
  have hb := abs_farCrossPairing_sub_le hφ hsupp hM he he' h4 hcN'
  have e1 : ∀ X : ℝ, X / c N - m = (X - c N * m) / c N := fun X => by field_simp
  rw [Real.norm_eq_abs, e1, abs_div, abs_of_pos hc0, div_le_iff₀ hc0]
  calc _ ≤ C * (Real.sqrt (c N) * (1 + Real.log (c N)) + c N ^ 3 / N) := hb
    _ = C * ((1 + Real.log (c N)) * (c N / Real.sqrt (c N)) + c N ^ 2 / N * c N) := by
        rw [Real.div_sqrt]; ring
    _ = _ := by ring

end GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations
