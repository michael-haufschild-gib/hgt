import GaloisForLFunctions.AbsoluteGeometryOfSpecZ.OnNestedWindowsTheCombFormTendsToWeilsFormOfTheStepPacket
import GaloisForLFunctions.AbsoluteGeometryOfSpecZ.UnderTheRiemannHypothesisWeilsFormOfAStepPacketIsNonnegative

/-!
# The Riemann hypothesis is the sign of Weil's form on step packets

A real divisor that is constant on the `J` blocks of `B` points above the scale `RB` is the
sample of a step packet: `σ_j e^{u/2}` on the window `(log(R + j), log(R + j + 1)]`.

* **Limit matrices** (`tendsto_combForm_blockFunction_div`). Weil's form on the comb of such a
  divisor, per point of a block, tends to Weil's form `𝔚_Q` of the step packet. The limit is a
  quadratic form in `σ` whose entries are values of `𝔚_Q` on flat packets of windows with
  integer ends, and these are elementary (`packetForm_flatPacket_eq`): the two pole moments
  `log(b/a)` and `b − a`, the closed form `W` of the jets, and the overlaps `(b/k − a)⁺` with
  the weights `Λ(k)`, `k ≤ Q`.
* **The Riemann hypothesis** (`riemannHypothesis_iff_forall_packetForm_stepPacket_nonneg`)
  holds iff `𝔚_{3K+1}` is nonnegative on the step packets of `3KR` blocks, for all `K, R`:
  a family of finite matrices with elementary entries.
* **The inequality at finite scale** (`riemannHypothesis_iff_eventually_combForm_ge`). The
  Riemann hypothesis holds iff for every window ratio and every `η > 0`, at all large scales
  every real divisor of the window has `2 d₁ d₂ − D·D ≥ −η Σ c_n²`. The direction from the
  Riemann hypothesis pads the window to complete blocks, passes to block averages
  (continuation) and uses the limit matrices.
-/

open Finset Filter Topology MeasureTheory
open Zeta23
open scoped ArithmeticFunction.vonMangoldt

noncomputable section

namespace GaloisForLFunctions.AbsoluteGeometryOfSpecZ

open HodgeTheoryOfAFixedPart (blockIndex lowerValue)

local notation "combW" => HodgeTheoryOfAFixedPart.combForm

/-! ### Step packets and nested windows -/

/-- The step packet with the value `σ j` on the window `(R + j, R + j + 1]`, `j < J`, in the
logarithmic coordinate. -/
def stepPacket (R J : ℕ) (σ : ℕ → ℝ) (u : ℝ) : ℝ :=
  ∑ j ∈ range J, σ j * flatPacket ((R + j : ℕ) : ℝ) ((R + (j + 1) : ℕ) : ℝ) u

/-- The coefficients of a step function on the nested windows `(R, R + j]`. -/
def nestedCoeff (J : ℕ) (σ : ℕ → ℝ) (j : ℕ) : ℝ :=
  lowerValue σ j - if j < J then σ j else 0

/-- Summation by parts: a step function through nested windows. -/
theorem sum_mul_sub_eq_nested (J : ℕ) (σ Ψ : ℕ → ℝ) :
    ∑ j ∈ range J, σ j * (Ψ (j + 1) - Ψ j) = ∑ j ∈ range (J + 1), nestedCoeff J σ j * Ψ j := by
  have h1 : ∑ j ∈ range (J + 1), lowerValue σ j * Ψ j = ∑ j ∈ range J, σ j * Ψ (j + 1) := by
    have h0 : lowerValue σ 0 = 0 := by rw [lowerValue, if_pos rfl]
    rw [Finset.sum_range_succ', h0, zero_mul, add_zero]
    exact Finset.sum_congr rfl fun j _ => by
      rw [lowerValue, if_neg (Nat.succ_ne_zero j), Nat.add_sub_cancel]
  have h2 : ∑ j ∈ range (J + 1), (if j < J then σ j else 0) * Ψ j =
      ∑ j ∈ range J, σ j * Ψ j := by
    rw [Finset.sum_range_succ, if_neg (lt_irrefl J), zero_mul, add_zero]
    exact Finset.sum_congr rfl fun j hj => by rw [if_pos (Finset.mem_range.mp hj)]
  simp only [nestedCoeff, sub_mul, mul_sub, Finset.sum_sub_distrib]
  rw [h1, h2]

theorem stepPacket_eq_nested {R : ℕ} (hR : 1 ≤ R) (J : ℕ) (σ : ℕ → ℝ) :
    stepPacket R J σ = fun u =>
      ∑ j ∈ range (J + 1), nestedCoeff J σ j * flatPacket (R : ℝ) ((R + j : ℕ) : ℝ) u := by
  funext u
  have hR' : (0 : ℝ) < R := by exact_mod_cast hR
  rw [stepPacket, ← sum_mul_sub_eq_nested J σ fun j => flatPacket (R : ℝ) ((R + j : ℕ) : ℝ) u]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [flatPacket_sub_flatPacket hR' (by exact_mod_cast Nat.le_add_right R j)
    (by exact_mod_cast Nat.add_le_add_left (Nat.le_succ j) R)]

/-- A divisor constant on blocks through the flat divisors of nested windows. -/
theorem blockFunction_eq_nested {R B J : ℕ} (hB : 0 < B) (σ : ℕ → ℝ) {n : ℕ}
    (hn : n ∈ Ioc (R * B) (R * B + B * J)) :
    σ (blockIndex (R * B) B n) =
      ∑ j ∈ range (J + 1), nestedCoeff J σ j * windowDivisor (R * B) ((R + j) * B) n := by
  rw [← sum_mul_sub_eq_nested J σ fun j => windowDivisor (R * B) ((R + j) * B) n]
  have hstep : ∀ j : ℕ, windowDivisor (R * B) ((R + (j + 1)) * B) n -
      windowDivisor (R * B) ((R + j) * B) n =
      windowDivisor ((R + j) * B) ((R + (j + 1)) * B) n := fun j =>
    windowDivisor_sub (Nat.mul_le_mul_right B (Nat.le_add_right R j))
      (Nat.mul_le_mul_right B (Nat.add_le_add_left (Nat.le_succ j) R)) n
  simp only [hstep]
  obtain ⟨hn1, hn2⟩ := Finset.mem_Ioc.mp hn
  obtain ⟨hb1, hb2⟩ := HodgeTheoryOfAFixedPart.blockIndex_bounds hB hn1
  have hiJ : blockIndex (R * B) B n < J := by
    by_contra h
    have h1 : B * J ≤ B * blockIndex (R * B) B n := Nat.mul_le_mul_left B (not_lt.mp h)
    omega
  rw [Finset.sum_eq_single (blockIndex (R * B) B n)]
  · rw [windowDivisor_of_mem, mul_one]
    rw [Finset.mem_Ioc]
    constructor <;> linarith
  · intro j _ hji
    rw [windowDivisor_of_notMem, mul_zero]
    rw [Finset.mem_Ioc]
    rintro ⟨h1, h2⟩
    apply hji
    have hlt1 : j < blockIndex (R * B) B n + 1 := by
      by_contra hc
      have := Nat.mul_le_mul_left B (not_lt.mp hc)
      linarith
    have hlt2 : blockIndex (R * B) B n < j + 1 := by
      by_contra hc
      have := Nat.mul_le_mul_left B (not_lt.mp hc)
      linarith
    omega
  · intro hnot
    exact absurd (Finset.mem_range.mpr hiJ) hnot

theorem sum_nestedCoeff_sq_le (J : ℕ) (σ : ℕ → ℝ) :
    ∑ j ∈ range (J + 1), nestedCoeff J σ j ^ 2 ≤ 4 * ∑ j ∈ range J, σ j ^ 2 := by
  have h1 : ∑ j ∈ range (J + 1), lowerValue σ j ^ 2 = ∑ j ∈ range J, σ j ^ 2 := by
    have h0 : lowerValue σ 0 = 0 := by rw [lowerValue, if_pos rfl]
    rw [Finset.sum_range_succ', h0, zero_pow two_ne_zero, add_zero]
    exact Finset.sum_congr rfl fun j _ => by
      rw [lowerValue, if_neg (Nat.succ_ne_zero j), Nat.add_sub_cancel]
  have h2 : ∑ j ∈ range (J + 1), (if j < J then σ j else 0) ^ 2 = ∑ j ∈ range J, σ j ^ 2 := by
    rw [Finset.sum_range_succ, if_neg (lt_irrefl J), zero_pow two_ne_zero, add_zero]
    exact Finset.sum_congr rfl fun j hj => by rw [if_pos (Finset.mem_range.mp hj)]
  calc ∑ j ∈ range (J + 1), nestedCoeff J σ j ^ 2
      ≤ ∑ j ∈ range (J + 1),
          (2 * lowerValue σ j ^ 2 + 2 * (if j < J then σ j else 0) ^ 2) :=
        Finset.sum_le_sum fun j _ => by
          rw [nestedCoeff]
          nlinarith [sq_nonneg (lowerValue σ j + if j < J then σ j else 0)]
    _ = 4 * ∑ j ∈ range J, σ j ^ 2 := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, h1, h2]
        ring

theorem sum_blockFunction_sq {R B J : ℕ} (hB : 0 < B) (σ : ℕ → ℝ) :
    ∑ n ∈ Ioc (R * B) (R * B + B * J), σ (blockIndex (R * B) B n) ^ 2 =
      B * ∑ j ∈ range J, σ j ^ 2 := by
  rw [HodgeTheoryOfAFixedPart.sum_Ioc_blocks, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  have h : ∀ a ∈ range B, σ (blockIndex (R * B) B (R * B + 1 + B * j + a)) ^ 2 = σ j ^ 2 :=
    fun a ha => by
      rw [HodgeTheoryOfAFixedPart.blockIndex_add hB (R * B) j (Finset.mem_range.mp ha)]
  rw [Finset.sum_congr rfl h, Finset.sum_const, Finset.card_range, nsmul_eq_mul]

/-! ### The limit matrices -/

section Limit

variable {R J Q : ℕ}

theorem nested_bounds (R J : ℕ) : ∀ j ∈ range (J + 1), R ≤ R + j ∧ R + j ≤ R + J :=
  fun j hj => ⟨Nat.le_add_right R j, by have := Finset.mem_range.mp hj; omega⟩

/-- **Limit matrices.** On the divisors constant on the `J` blocks above the scale `RB`, Weil's
form on the comb, per point of a block, tends to Weil's form of the step packet. -/
theorem tendsto_combForm_blockFunction_div (hR : 1 ≤ R) (hQ : R + J ≤ Q * R) (σ : ℕ → ℝ) :
    Tendsto (fun B : ℕ => combW (Ioc (R * B) (R * B + B * J))
        (fun n => σ (blockIndex (R * B) B n)) / B) atTop
      (𝓝 (packetForm Q (stepPacket R J σ))) := by
  have h := tendsto_combForm_nested_div (s := range (J + 1)) (x := fun j => R + j)
    (X := R + J) (Q := Q) hR (nested_bounds R J) hQ (nestedCoeff J σ)
  rw [stepPacket_eq_nested hR J σ]
  refine h.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with B hB
  have hwin : (R + J) * B = R * B + B * J := by ring
  rw [hwin]
  congr 1
  exact (combForm_congr fun n hn => blockFunction_eq_nested (by omega) σ hn).symm

/-- Under the Riemann hypothesis Weil's form is nonnegative on step packets. -/
theorem packetForm_stepPacket_nonneg_of_riemannHypothesis (hRH : RiemannHypothesis)
    (hR : 1 ≤ R) (hQ : R + J ≤ Q * R) (σ : ℕ → ℝ) : 0 ≤ packetForm Q (stepPacket R J σ) := by
  rw [stepPacket_eq_nested hR J σ]
  exact packetForm_step_nonneg_of_riemannHypothesis hRH (s := range (J + 1))
    (x := fun j => R + j) (X := R + J) hR (nested_bounds R J) hQ (nestedCoeff J σ)

/-- If Weil's form is nonnegative on the step packets of `J` blocks, then at all large block
sizes Weil's form on the comb is at least `−η Σ σ²` on every divisor constant on the blocks. -/
theorem eventually_combForm_blockFunction_ge (hR : 1 ≤ R) (hQ : R + J ≤ Q * R) {η : ℝ}
    (hη : 0 < η) (hnn : ∀ σ : ℕ → ℝ, 0 ≤ packetForm Q (stepPacket R J σ)) :
    ∀ᶠ B : ℕ in atTop, ∀ σ : ℕ → ℝ,
      -η * ∑ n ∈ Ioc (R * B) (R * B + B * J), σ (blockIndex (R * B) B n) ^ 2 ≤
        combW (Ioc (R * B) (R * B + B * J)) fun n => σ (blockIndex (R * B) B n) := by
  have hev := eventually_abs_combForm_nested_sub_le (s := range (J + 1)) (x := fun j => R + j)
    (X := R + J) (Q := Q) hR (nested_bounds R J) hQ (η := η / 4) (by positivity)
  filter_upwards [hev, eventually_ge_atTop 1] with B hB hB1 σ
  have hB0 : (0 : ℝ) < B := by exact_mod_cast hB1
  have h := hB (nestedCoeff J σ)
  have hwin : (R + J) * B = R * B + B * J := by ring
  have hc : combW (Ioc (R * B) (R * B + B * J)) (fun n => ∑ j ∈ range (J + 1),
        nestedCoeff J σ j * windowDivisor (R * B) ((R + j) * B) n) =
      combW (Ioc (R * B) (R * B + B * J)) fun n => σ (blockIndex (R * B) B n) :=
    (combForm_congr fun n hn => blockFunction_eq_nested (by omega) σ hn).symm
  rw [hwin, hc, ← stepPacket_eq_nested hR J σ] at h
  have hsq := sum_nestedCoeff_sq_le J σ
  have hpf := hnn σ
  have hσ : 0 ≤ ∑ j ∈ range J, σ j ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hlow : -(η * ∑ j ∈ range J, σ j ^ 2) ≤
      combW (Ioc (R * B) (R * B + B * J)) (fun n => σ (blockIndex (R * B) B n)) / B := by
    have h1 := (abs_le.mp h).1
    nlinarith
  rw [sum_blockFunction_sq (by omega) σ]
  have h3 := (le_div_iff₀ hB0).mp hlow
  linarith

end Limit

/-! ### The entries are elementary -/

/-- **Weil's form of the flat packet of a window with integer ends**, in closed form: the pole
moments, the closed form `W` of the jets on flat packets, and the overlaps with the weights of
the primes. -/
theorem packetForm_flatPacket_eq {a b : ℕ} (ha : 1 ≤ a) (hab : a < b) (Q : ℕ) :
    packetForm Q (flatPacket a b) =
      2 * ((Real.log b - Real.log a) * ((b : ℝ) - a)) -
        (flatPairing b b - 2 * flatPairing a b + flatPairing a a) -
        2 * ∑ k ∈ Icc 2 Q, (Λ k : ℝ) * max ((b : ℝ) / k - a) 0 := by
  have ha' : (0 : ℝ) < a := by exact_mod_cast ha
  have hab' : (a : ℝ) ≤ b := by exact_mod_cast hab.le
  have hsum : ∑ k ∈ Icc 2 Q, contactWeight k * packetAutocorr (flatPacket a b) (Real.log k) =
      ∑ k ∈ Icc 2 Q, (Λ k : ℝ) * max ((b : ℝ) / k - a) 0 :=
    Finset.sum_congr rfl fun k hk => by
      have hk1 : 1 ≤ k := by
        have := (Finset.mem_Icc.mp hk).1
        omega
      have hk0 : (0 : ℝ) < k := by exact_mod_cast hk1
      rw [← HodgeTheoryOfAFixedPart.packetAutocorr_flatPacket_log_div_exp ha hab.le hk1,
        contactWeight, Real.exp_half, Real.exp_log hk0]
      ring
  rw [packetForm, integral_flatPacket_mul_exp_neg ha' hab', integral_flatPacket_mul_exp ha' hab',
    hsum, flatPairing_window_eq_jumpForm ha hab]
  ring

/-! ### The Riemann hypothesis -/

/-- **The Riemann hypothesis is the sign of Weil's form on step packets.** It holds iff for all
`K, R` the form `𝔚_{3K+1}` is nonnegative on the step packets of `3KR` blocks of the window
`(R, (3K + 1)R]`. -/
theorem riemannHypothesis_iff_forall_packetForm_stepPacket_nonneg :
    RiemannHypothesis ↔ ∀ K : ℕ, 1 ≤ K → ∀ R : ℕ, 1 ≤ R → ∀ σ : ℕ → ℝ,
      0 ≤ packetForm (3 * K + 1) (stepPacket R (3 * K * R) σ) := by
  constructor
  · intro hRH K _ R hR σ
    exact packetForm_stepPacket_nonneg_of_riemannHypothesis hRH hR (le_of_eq (by ring)) σ
  · intro h
    refine HodgeTheoryOfAFixedPart.riemannHypothesis_of_frequently_blockFunction_combForm_ge
      fun K hK η hη R hR => ?_
    exact (eventually_combForm_blockFunction_ge hR (le_of_eq (by ring)) hη
      (h K hK R hR)).frequently

/-- **The inequality at finite scale from the Riemann hypothesis.** For every window ratio and
every `η > 0`, at all large scales every real divisor of the window has
`2 d₁ d₂ − D·D ≥ −η Σ c_n²`. -/
theorem eventually_combForm_ge_of_riemannHypothesis (hRH : RiemannHypothesis) (K : ℕ) {η : ℝ}
    (hη : 0 < η) :
    ∀ᶠ N : ℕ in atTop, ∀ c : ℕ → ℝ,
      -η * ∑ n ∈ Ioc N (N + 3 * K * N), c n ^ 2 ≤ combW (Ioc N (N + 3 * K * N)) c := by
  obtain ⟨R, hR, hred⟩ :=
    HodgeTheoryOfAFixedPart.exists_blockSize_combForm_ge_blockMean (6 * K + 2) (half_pos hη)
  have hQ : R + (6 * K + 1) * R ≤ (6 * K + 2) * R := le_of_eq (by ring)
  have hev := eventually_combForm_blockFunction_ge (J := (6 * K + 1) * R) (Q := 6 * K + 2) hR hQ
    (half_pos hη) fun σ => packetForm_stepPacket_nonneg_of_riemannHypothesis hRH hR hQ σ
  obtain ⟨B₀, hB₀⟩ := eventually_atTop.mp hev
  refine eventually_atTop.mpr ⟨R * (B₀ + 1), fun N hN c => ?_⟩
  -- the block size and the scale of complete blocks below `N`
  have hB1 : B₀ + 1 ≤ N / R := (Nat.le_div_iff_mul_le hR).mpr (by rw [Nat.mul_comm]; exact hN)
  have hBpos : 0 < N / R := by omega
  have hNle : R * (N / R) ≤ N := Nat.mul_div_le N R
  have hNlt : N ≤ R * (N / R) + R := by
    have := Nat.lt_mul_div_succ N hR
    linarith
  have hRB : R ≤ R * (N / R) := Nat.le_mul_of_pos_right R hBpos
  -- the window lies in the window of complete blocks
  have hsub : Ioc N (N + 3 * K * N) ⊆
      Ioc (R * (N / R)) (R * (N / R) + N / R * ((6 * K + 1) * R)) := by
    refine Finset.Ioc_subset_Ioc hNle ?_
    have h1 : (3 * K + 1) * N ≤ (3 * K + 1) * (R * (N / R) + R) := Nat.mul_le_mul_left _ hNlt
    have h2 : (3 * K + 1) * R ≤ (3 * K + 1) * (R * (N / R)) := Nat.mul_le_mul_left _ hRB
    linarith
  -- the divisor extended by zero
  have hform : combW (Ioc (R * (N / R)) (R * (N / R) + N / R * ((6 * K + 1) * R)))
        (fun n => if n ∈ Ioc N (N + 3 * K * N) then c n else 0) =
      combW (Ioc N (N + 3 * K * N)) c :=
    (combForm_of_subset hsub fun n _ hn => if_neg hn).trans
      (combForm_congr fun n hn => if_pos hn)
  have hsq : ∑ n ∈ Ioc (R * (N / R)) (R * (N / R) + N / R * ((6 * K + 1) * R)),
        (if n ∈ Ioc N (N + 3 * K * N) then c n else 0) ^ 2 =
      ∑ n ∈ Ioc N (N + 3 * K * N), c n ^ 2 := by
    rw [← Finset.sum_subset hsub fun n _ hn => by rw [if_neg hn]; ring]
    exact Finset.sum_congr rfl fun n hn => by rw [if_pos hn]
  -- block averages, then the limit matrices
  have hdiv : R * (N / R) / R = N / R := Nat.mul_div_cancel_left (N / R) hR
  have h1 := hred (R * (N / R)) ((6 * K + 1) * R) hRB
    (by rw [hdiv]; exact le_of_eq (by ring))
    (fun n => if n ∈ Ioc N (N + 3 * K * N) then c n else 0)
  rw [hdiv] at h1
  have h2 := hB₀ (N / R) (by omega)
    (HodgeTheoryOfAFixedPart.blockMean (R * (N / R)) (N / R) ((6 * K + 1) * R)
      fun n => if n ∈ Ioc N (N + 3 * K * N) then c n else 0)
  have h3 := HodgeTheoryOfAFixedPart.sum_blockMean_sq_le hBpos (R * (N / R)) ((6 * K + 1) * R)
    (fun n => if n ∈ Ioc N (N + 3 * K * N) then c n else 0)
  rw [hform, hsq] at h1
  rw [hsq] at h3
  nlinarith [mul_le_mul_of_nonneg_left h3 (half_pos hη).le]

/-- **The finite matrices are a criterion in both directions.** The Riemann hypothesis holds
iff for every window ratio and every `η > 0`, at all large scales Weil's form on the comb is
at least `−η Σ c_n²` on every real divisor of the window. -/
theorem riemannHypothesis_iff_eventually_combForm_ge :
    RiemannHypothesis ↔ ∀ K : ℕ, 1 ≤ K → ∀ η : ℝ, 0 < η → ∀ᶠ N : ℕ in atTop, ∀ c : ℕ → ℝ,
      -η * ∑ n ∈ Ioc N (N + 3 * K * N), c n ^ 2 ≤ combW (Ioc N (N + 3 * K * N)) c :=
  ⟨fun hRH K _ _ hη => eventually_combForm_ge_of_riemannHypothesis hRH K hη,
    fun h => HodgeTheoryOfAFixedPart.riemannHypothesis_of_frequently_combForm_ge
      fun K hK η hη => (h K hK η hη).frequently⟩

end GaloisForLFunctions.AbsoluteGeometryOfSpecZ
