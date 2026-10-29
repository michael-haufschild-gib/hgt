import GaloisForLFunctions.ArithmeticOfSquareRootPrecision.TheBatteryOfTheCount
import GaloisForLFunctions.RHTower.PrimeShortIntervalsSeventeenThirtiethsUnconditional

/-!
# The deciding-input theorem and the precision-blindness of producers

**Necessary properties of a deciding input** (`deciding_input_necessary_properties`). Let `S` be any
property of weights that implies the count. Then, unconditionally:
* `S` is **parity-breaking**: it fails for the Liouville twin;
* `S` is **precision-faithful**: no weight satisfies `S` together with its perturbation by
  `ε n^{−η}`, `0 ≤ η < ½`;
* `S` has **unbounded aperture**: every finite window of every weight extends to a weight
  failing `S`;
* the **stabilizer** of `S` at any weight lies in the square-root class `𝒬`.

Consequently a property that implies the count holds for no weight if it is stable under the
Liouville twist (`not_of_twist_stable`), determined by a finite window (`not_of_finite_window`),
or stable under one move outside `𝒬` (`not_of_stable_visible`).

**Producers are precision-blind** (`producers_are_precision_blind`). For `ε ≠ 0`, `0 < η < ½` the
weight `Λ + ε n^{−η}` satisfies the prime number theorem and the Guth–Maynard short-interval law
`ψ(x + x^α) − ψ(x) ∼ x^α` for every `α > 17/30`, and it never satisfies the count. Every error-term
law weaker than square root, `ψ(x) − x = O(E)` with `x^{1/2+κ} = O(E)`, is likewise inherited by a
weight that fails the count (`errorLaw_cannot_decide`).
-/

noncomputable section

open Filter Asymptotics Real Finset RHTower Topology
open ArithmeticFunction (vonMangoldt cardFactors)

namespace GaloisForLFunctions.ArithmeticOfSquareRootPrecision

/-! ### The deciding-input theorem -/

/-- The Liouville twist `a ↦ λ·a` of a weight. -/
def liouvilleTwist (a : ℕ → ℝ) (n : ℕ) : ℝ := (-1) ^ cardFactors n * a n

theorem liouvilleTwist_vonMangoldt : liouvilleTwist vonMangoldtWeight = liouvilleWeight := rfl

/-- The weight equal to `a` on `{0, …, X}` and to the Liouville twin beyond. -/
def liouvilleTail (a : ℕ → ℝ) (X : ℕ) (n : ℕ) : ℝ := if n ≤ X then a n else liouvilleWeight n

theorem not_count_liouvilleTail (a : ℕ → ℝ) (X : ℕ) : ¬ Count (liouvilleTail a X) :=
  not_count_of_eventually_eq_liouvilleWeight (N := X) fun n hn => by
    simp [liouvilleTail, not_le.mpr hn]

/-- **The deciding-input theorem.** Every property of weights that implies the count is
parity-breaking, precision-faithful, of unbounded aperture, and has stabilizer inside `𝒬`. -/
theorem deciding_input_necessary_properties (S : (ℕ → ℝ) → Prop) (hS : ∀ a, S a → Count a) :
    ¬ S liouvilleWeight ∧
    (∀ (a : ℕ → ℝ) (ε η : ℝ), ε ≠ 0 → 0 ≤ η → η < 1 / 2 → ¬ (S a ∧ S (a + ε • powerWeight η))) ∧
    (∀ (a : ℕ → ℝ) (X : ℕ), ∃ b : ℕ → ℝ, (∀ n ≤ X, b n = a n) ∧ ¬ S b) ∧
    (∀ a δ : ℕ → ℝ, S a → S (a + δ) → δ ∈ sqrtClass) :=
  ⟨fun h => not_count_liouvilleWeight (hS _ h),
    fun a _ _ hε hη0 hη ⟨h, h'⟩ =>
      not_count_and_count_add_smul_powerWeight a hε hη0 hη ⟨hS _ h, hS _ h'⟩,
    fun a X => ⟨liouvilleTail a X, fun n hn => by simp [liouvilleTail, hn],
      fun h => not_count_liouvilleTail a X (hS _ h)⟩,
    fun a δ h h' => (count_add_iff_mem_sqrtClass (hS a h) δ).mp (hS _ h')⟩

/-- A property stable under the Liouville twist and implying the count fails at `Λ`. -/
theorem not_of_twist_stable (S : (ℕ → ℝ) → Prop) (hS : ∀ a, S a → Count a)
    (htw : ∀ a, S a → S (liouvilleTwist a)) : ¬ S vonMangoldtWeight := fun h =>
  (deciding_input_necessary_properties S hS).1 (htw _ h)

/-- A property determined by a finite window and implying the count holds for no weight. -/
theorem not_of_finite_window (S : (ℕ → ℝ) → Prop) (hS : ∀ a, S a → Count a) (X : ℕ)
    (hwin : ∀ a b : ℕ → ℝ, (∀ n ≤ X, a n = b n) → (S a ↔ S b)) (a : ℕ → ℝ) : ¬ S a := fun h =>
  not_count_liouvilleTail a X
    (hS _ ((hwin a _ fun n hn => by simp [liouvilleTail, hn]).mp h))

/-- A property stable under one move outside `𝒬` and implying the count holds for no weight. -/
theorem not_of_stable_visible (S : (ℕ → ℝ) → Prop) (hS : ∀ a, S a → Count a) {δ : ℕ → ℝ}
    (hδ : δ ∉ sqrtClass) (hstab : ∀ a, S a → S (a + δ)) (a : ℕ → ℝ) : ¬ S a := fun h =>
  hδ ((deciding_input_necessary_properties S hS).2.2.2 a δ h (hstab a h))

/-! ### Upper bound for the power perturbation -/

/-- `x^r = o(x^s)` for `r < s`. -/
theorem rpow_isLittleO_rpow {r s : ℝ} (hrs : r < s) :
    (fun x : ℝ => x ^ r) =o[atTop] fun x => x ^ s := by
  rw [isLittleO_iff_tendsto' (by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx h
    exact absurd h (Real.rpow_pos_of_pos hx s).ne')]
  refine (tendsto_rpow_neg_atTop (y := s - r) (by linarith)).congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
  rw [← Real.rpow_sub hx]; ring_nf

/-- `Σ_{1 ≤ n ≤ N} n^{−η} ≤ 1 + ∫₁^N t^{−η} dt`, since `t^{−η}` is decreasing. -/
theorem sum_powerWeight_le_integral {η : ℝ} (hη : 0 ≤ η) {N : ℕ} (hN : 1 ≤ N) :
    ∑ n ∈ Ioc 0 N, powerWeight η n ≤ 1 + ∫ t in (1 : ℝ)..N, t ^ (-η) := by
  induction N, hN using Nat.le_induction with
  | base => simp [powerWeight]
  | succ N hN ih =>
    rw [sum_Ioc_succ_top (Nat.zero_le N)]
    have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
    have hint : ∀ a b : ℝ, 0 < a → a ≤ b → IntervalIntegrable (fun t : ℝ => t ^ (-η)) MeasureTheory.volume a b :=
      fun a b ha hab => (ContinuousOn.intervalIntegrable fun t ht => by
        rw [Set.uIcc_of_le hab] at ht
        exact (Real.continuousAt_rpow_const _ _ (Or.inl (by linarith [ht.1]))).continuousWithinAt)
    have hstep : powerWeight η (N + 1) ≤ ∫ t in (N : ℝ)..((N + 1 : ℕ) : ℝ), t ^ (-η) := by
      have hle : (N : ℝ) ≤ ((N + 1 : ℕ) : ℝ) := by push_cast; linarith
      calc powerWeight η (N + 1) = ∫ _ in (N : ℝ)..((N + 1 : ℕ) : ℝ), powerWeight η (N + 1) := by
            simp
        _ ≤ ∫ t in (N : ℝ)..((N + 1 : ℕ) : ℝ), t ^ (-η) :=
            intervalIntegral.integral_mono_on hle intervalIntegrable_const (hint _ _ hN0 hle)
              fun t ht => Real.rpow_le_rpow_of_nonpos (by linarith [ht.1]) ht.2 (by linarith)
    have hadd := intervalIntegral.integral_add_adjacent_intervals (hint 1 N one_pos
      (by exact_mod_cast hN)) (hint N ((N + 1 : ℕ) : ℝ) hN0 (by push_cast; linarith))
    linarith

/-- **Upper bound**: `Σ_{n ≤ x} n^{−η} ≤ 1 + x^{1−η}/(1 − η)` for `0 ≤ η < 1`, `x ≥ 1`. -/
theorem partialSum_powerWeight_le_rpow {η x : ℝ} (hη0 : 0 ≤ η) (hη1 : η < 1) (hx : 1 ≤ x) :
    partialSum (powerWeight η) x ≤ 1 + x ^ (1 - η) / (1 - η) := by
  have hN : 1 ≤ ⌊x⌋₊ := Nat.one_le_floor_iff x |>.mpr hx
  have h := sum_powerWeight_le_integral hη0 hN
  rw [integral_rpow (Or.inl (by linarith)), show -η + 1 = 1 - η by ring,
    Real.one_rpow] at h
  have hfl : ((⌊x⌋₊ : ℕ) : ℝ) ^ (1 - η) ≤ x ^ (1 - η) :=
    Real.rpow_le_rpow (Nat.cast_nonneg _) (Nat.floor_le (by linarith)) (by linarith)
  have h1 : 0 < 1 - η := by linarith
  calc partialSum (powerWeight η) x ≤ 1 + (((⌊x⌋₊ : ℕ) : ℝ) ^ (1 - η) - 1) / (1 - η) := h
    _ ≤ 1 + x ^ (1 - η) / (1 - η) := by gcongr; linarith

/-- `Σ_{n ≤ x} n^{−η} = o(x)` for `0 < η < 1`. -/
theorem partialSum_powerWeight_isLittleO {η : ℝ} (hη0 : 0 < η) (hη1 : η < 1) :
    partialSum (powerWeight η) =o[atTop] fun x => x := by
  have hrp : (fun x : ℝ => x ^ (1 - η)) =o[atTop] fun x => x :=
    (rpow_isLittleO_rpow (r := 1 - η) (s := 1) (by linarith)).congr_right fun x => Real.rpow_one x
  have hb : (fun x : ℝ => 1 + x ^ (1 - η) / (1 - η)) =o[atTop] fun x => x :=
    (isLittleO_const_id_atTop 1).add (hrp.const_mul_left (1 - η)⁻¹ |>.congr_left fun x => by
      rw [div_eq_inv_mul])
  refine IsBigO.trans_isLittleO (IsBigO.of_bound 1 ?_) hb
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with x hx
  have h0 := partialSum_nonneg (powerWeight_nonneg η) x
  have hup := partialSum_powerWeight_le_rpow hη0.le hη1 hx
  rw [Real.norm_of_nonneg h0, Real.norm_of_nonneg (by linarith), one_mul]
  exact hup

/-! ### The prime number theorem is precision-blind -/

/-- The **prime number law** of a weight: `A(x)/x → 1`. -/
def PrimeNumberLaw (a : ℕ → ℝ) : Prop := Tendsto (fun x => partialSum a x / x) atTop (𝓝 1)

theorem primeNumberLaw_vonMangoldt : PrimeNumberLaw vonMangoldtWeight :=
  tendsto_chebyshevPsiReal_div.congr fun x => by rw [chebyshevPsiReal_eq_psi]; rfl

/-- The prime number law survives every perturbation with partial sums `o(x)`. -/
theorem primeNumberLaw_add {a δ : ℕ → ℝ} (ha : PrimeNumberLaw a)
    (hδ : partialSum δ =o[atTop] fun x => x) : PrimeNumberLaw (a + δ) := by
  have h0 : Tendsto (fun x => partialSum δ x / x) atTop (𝓝 0) := hδ.tendsto_div_nhds_zero
  have := ha.add h0
  rw [add_zero] at this
  exact this.congr fun x => by rw [partialSum_add, add_div]

/-! ### The Guth–Maynard short-interval law is precision-blind -/

/-- The **short-interval law** at exponent `α`: `(A(x + x^α) − A(x)) / x^α → 1`. -/
def ShortIntervalLaw (α : ℝ) (a : ℕ → ℝ) : Prop :=
  Tendsto (fun x => (partialSum a (x + x ^ α) - partialSum a x) / x ^ α) atTop (𝓝 1)

/-- **Guth–Maynard**, unconditionally: `Λ` satisfies the short-interval law for `17/30 < α < 1`. -/
theorem shortIntervalLaw_vonMangoldt {α : ℝ} (hα : 17 / 30 < α) (hα1 : α < 1) :
    ShortIntervalLaw α vonMangoldtWeight :=
  tendsto_psi_short_window_div_seventeenThirtieths hα hα1

/-- A window of length `h ≥ 0` past `x > 0` carries at most `(h + 1) x^{−η}` of `n^{−η}`. -/
theorem window_powerWeight_le {η x h : ℝ} (hη : 0 ≤ η) (hx : 0 < x) (hh : 0 ≤ h) :
    0 ≤ partialSum (powerWeight η) (x + h) - partialSum (powerWeight η) x ∧
      partialSum (powerWeight η) (x + h) - partialSum (powerWeight η) x ≤ (h + 1) * x ^ (-η) := by
  have hmono : ⌊x⌋₊ ≤ ⌊x + h⌋₊ := Nat.floor_le_floor (by linarith)
  have hsplit : partialSum (powerWeight η) (x + h) - partialSum (powerWeight η) x =
      ∑ n ∈ Ioc ⌊x⌋₊ ⌊x + h⌋₊, powerWeight η n := by
    unfold partialSum
    rw [← sum_Ioc_consecutive _ (Nat.zero_le _) hmono]; ring
  rw [hsplit]
  refine ⟨sum_nonneg fun n _ => powerWeight_nonneg η n, ?_⟩
  have hterm : ∀ n ∈ Ioc ⌊x⌋₊ ⌊x + h⌋₊, powerWeight η n ≤ x ^ (-η) := fun n hn =>
    Real.rpow_le_rpow_of_nonpos hx (Nat.lt_floor_add_one x |>.le.trans
      (by exact_mod_cast (mem_Ioc.mp hn).1)) (by linarith)
  have hcard : ((Ioc ⌊x⌋₊ ⌊x + h⌋₊).card : ℝ) ≤ h + 1 := by
    rw [Nat.card_Ioc, Nat.cast_sub hmono]
    have h1 := Nat.floor_le (show 0 ≤ x + h by linarith)
    have h2 := Nat.lt_floor_add_one x
    linarith
  calc ∑ n ∈ Ioc ⌊x⌋₊ ⌊x + h⌋₊, powerWeight η n ≤ (Ioc ⌊x⌋₊ ⌊x + h⌋₊).card • x ^ (-η) :=
        sum_le_card_nsmul _ _ _ hterm
    _ ≤ (h + 1) * x ^ (-η) := by
        rw [nsmul_eq_mul]; exact mul_le_mul_of_nonneg_right hcard (Real.rpow_nonneg hx.le _)

/-- The short-interval law survives every perturbation `ε n^{−η}`, `η > 0`, at every `α > 0`. -/
theorem shortIntervalLaw_add_smul_powerWeight {a : ℕ → ℝ} {α η : ℝ} (hα : 0 < α) (hη : 0 < η)
    (ha : ShortIntervalLaw α a) (ε : ℝ) : ShortIntervalLaw α (a + ε • powerWeight η) := by
  have hbound : Tendsto (fun x : ℝ => x ^ (-η) + x ^ (-η - α)) atTop (𝓝 0) := by
    have h1 := tendsto_rpow_neg_atTop hη
    have h2 := tendsto_rpow_neg_atTop (y := η + α) (by linarith)
    simpa [show -η - α = -(η + α) by ring] using h1.add h2
  have h0 : Tendsto (fun x => (partialSum (powerWeight η) (x + x ^ α) -
      partialSum (powerWeight η) x) / x ^ α) atTop (𝓝 0) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hbound ?_ ?_
    · filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
      exact div_nonneg (window_powerWeight_le hη.le hx (Real.rpow_nonneg hx.le α)).1
        (Real.rpow_nonneg hx.le α)
    · filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
      have hxa : 0 < x ^ α := Real.rpow_pos_of_pos hx α
      rw [div_le_iff₀ hxa]
      have := (window_powerWeight_le hη.le hx (Real.rpow_nonneg hx.le α)).2
      have e1 : x ^ (-η - α) * x ^ α = x ^ (-η) := by rw [← Real.rpow_add hx]; ring_nf
      have he : (x ^ (-η) + x ^ (-η - α)) * x ^ α = (x ^ α + 1) * x ^ (-η) := by
        rw [add_mul, e1]; ring
      linarith
  have := ha.add (h0.const_mul ε)
  rw [mul_zero, add_zero] at this
  refine this.congr fun x => ?_
  simp only [partialSum_add, partialSum_smul]
  ring

/-! ### Error laws above square root -/

/-- The **error law** of scale `E`: `A(x) − x = O(E)`. -/
def ErrorLaw (E : ℝ → ℝ) (a : ℕ → ℝ) : Prop := (fun x => partialSum a x - x) =O[atTop] E

/-- An error law whose scale dominates `x^{1−η}` survives `ε n^{−η}`, `0 < η < 1`. -/
theorem errorLaw_add_smul_powerWeight {E : ℝ → ℝ} {η : ℝ} (hη0 : 0 < η) (hη1 : η < 1)
    (hE : (fun x => x ^ (1 - η)) =O[atTop] E) {a : ℕ → ℝ} (ha : ErrorLaw E a) (ε : ℝ) :
    ErrorLaw E (a + ε • powerWeight η) := by
  have hδ : partialSum (powerWeight η) =O[atTop] fun x => x ^ (1 - η) := by
    refine IsBigO.of_bound (1 + 1 / (1 - η)) ?_
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with x hx
    have hx0 : 0 < x := by linarith
    have hxr : 1 ≤ x ^ (1 - η) := Real.one_le_rpow hx (by linarith)
    have h1 : 0 < 1 - η := by linarith
    rw [Real.norm_of_nonneg (partialSum_nonneg (powerWeight_nonneg η) x),
      Real.norm_of_nonneg (by linarith)]
    calc partialSum (powerWeight η) x ≤ 1 + x ^ (1 - η) / (1 - η) :=
          partialSum_powerWeight_le_rpow hη0.le hη1 hx
      _ ≤ (1 + 1 / (1 - η)) * x ^ (1 - η) := by
          rw [add_mul, one_mul, div_mul_eq_mul_div, one_mul]; linarith
  have := ha.add ((hδ.trans hE).const_mul_left ε)
  refine this.congr' (Eventually.of_forall fun x => ?_) EventuallyEq.rfl
  simp only [partialSum_add, partialSum_smul]
  ring

/-- **Error laws above square root cannot decide.** If `ψ(x) − x = O(E)` with `x^{1/2+κ} = O(E)`,
`0 < κ < ½`, then some weight satisfies the same error law and fails the count. -/
theorem errorLaw_cannot_decide {E : ℝ → ℝ} {κ : ℝ} (hκ0 : 0 < κ) (hκ : κ < 1 / 2)
    (hE : (fun x => x ^ (1 / 2 + κ)) =O[atTop] E) (hΛ : ErrorLaw E vonMangoldtWeight) :
    ∃ b : ℕ → ℝ, ErrorLaw E b ∧ ¬ Count b := by
  refine ⟨vonMangoldtWeight + (1 : ℝ) • powerWeight (1 / 2 - κ),
    errorLaw_add_smul_powerWeight (by linarith) (by linarith) ?_ hΛ 1,
    not_count_vonMangoldt_add_smul_powerWeight one_ne_zero (by linarith) (by linarith)⟩
  exact hE.congr_left fun x => by rw [show (1 : ℝ) - (1 / 2 - κ) = 1 / 2 + κ by ring]

/-- **Producers are precision-blind.** For `ε ≠ 0` and `0 < η < ½` the weight `Λ + ε n^{−η}`
satisfies the prime number theorem and the Guth–Maynard law at every `α ∈ (17/30, 1)`, and
never satisfies the count. -/
theorem producers_are_precision_blind {ε η : ℝ} (hε : ε ≠ 0) (hη0 : 0 < η) (hη : η < 1 / 2) :
    PrimeNumberLaw (vonMangoldtWeight + ε • powerWeight η) ∧
      (∀ α : ℝ, 17 / 30 < α → α < 1 →
        ShortIntervalLaw α (vonMangoldtWeight + ε • powerWeight η)) ∧
      ¬ Count (vonMangoldtWeight + ε • powerWeight η) := by
  refine ⟨primeNumberLaw_add primeNumberLaw_vonMangoldt ?_, fun α hα hα1 =>
    shortIntervalLaw_add_smul_powerWeight (by linarith) hη0 (shortIntervalLaw_vonMangoldt hα hα1) ε,
    not_count_vonMangoldt_add_smul_powerWeight hε hη0.le hη⟩
  have := (partialSum_powerWeight_isLittleO hη0 (by linarith)).const_mul_left ε
  exact this.congr_left fun x => (partialSum_smul ε _ x).symm

end GaloisForLFunctions.ArithmeticOfSquareRootPrecision
