import GaloisForLFunctions.TransHorizonIncidenceMechanics.FinitePerturbationsOfTheSmoothPowerAreDecidedAtThePole

/-!
# A pole of order two needs a zero of order two

Let `q ≥ 0` drift like `n Σ_{(n,2n]} q(d)/d ≥ κ n^{1−ε} log n` (a double pole at `s = 1 − ε`, as for
`log(d) d^{-ε}`), and let `k` be a kernel on `[1, J]` with Dirichlet polynomial `K`. The Mellin pairing
of the drift now has order `δ^{-2}`:

`Φ_q(1 − ε + δ) ≤ −(κσ/2) ((2/δ²)(M^{-δ} − 2/3) − log 2/δ)`,

from `log m ≥ (2/δ)(1 − m^{-δ/2})` and the tail bounds of `Σ m^{-1-δ}` and `Σ m^{-1-3δ/2}`. Against the
receiver bound `O(δ^{-1/2})` this forces **both `K(1 − ε) = 0` and `K'(1 − ε) = 0`** whenever the
receiver of `k ⋆ q` is bounded: if `K(1 − ε) ≠ 0` the product `K(σ)Φ_q(σ)` has order `δ^{-2}`, and if
`K(1 − ε) = 0 ≠ K'(1 − ε)` it still has order `δ^{-1}` since `K(σ) ≈ K'(1 − ε) δ`.

So the receiver reads the order of the pole: a double pole is repaired only by a double zero, and the
separating observables are the first two Taylor coefficients `Σ_j k(j) j^{-(1−ε)}` and
`Σ_j k(j) log j · j^{-(1−ε)}` of the kernel at the pole. In particular the Fermi kernel
`δ₁ − 2^{1−ε}δ₂`, which pays `d^{-ε}`, never pays `log(d) d^{-ε}` (its slope at the pole is `log 2`).
-/

open Finset Filter Topology
open scoped BigOperators

namespace GaloisForLFunctions.TransHorizonIncidenceMechanics

noncomputable section
set_option autoImplicit false

/-- The slope of the kernel at the pole, `−K'(1 − ε) = Σ_j k(j) log j · j^{-(1−ε)}`. -/
def poleSlope (k : ℕ → ℝ) (J : ℕ) (ε : ℝ) : ℝ := ∑ j ∈ Icc 1 J, k j * Real.log j * (j : ℝ) ^ (-(1 - ε))

/-- **The logarithmic sum near the pole**: for `M ≥ 2` and `0 < δ`,
`Σ_{m ≥ M} log m · m^{-1-δ} ≥ (2/δ²)(M^{-δ} − 2/3)`. -/
theorem tsum_log_mul_rpow_ge {M : ℕ} (hM : 2 ≤ M) {δ : ℝ} (hδ : 0 < δ) :
    (2 / δ ^ 2) * ((M : ℝ) ^ (-δ) - 2 / 3) ≤
      ∑' k : ℕ, Real.log ((M : ℝ) + k) * ((M : ℝ) + k) ^ (-δ - 1) := by
  obtain ⟨N, rfl⟩ : ∃ N, M = N + 1 := ⟨M - 1, by omega⟩
  have hN : 1 ≤ N := by omega
  have hs1 := HTGeometry.summable_shift_rpow (q := -δ) (by linarith) N
  have hs2 := HTGeometry.summable_shift_rpow (q := -(3 * δ / 2)) (by linarith) N
  have hlow := HTGeometry.tsum_shift_rpow_ge (q := -δ) (by linarith) N
  have hup := HTGeometry.tsum_shift_rpow_le (q := -(3 * δ / 2)) (by linarith) hN
  rw [neg_neg] at hlow hup
  have hN1 : ((N : ℝ)) ^ (-(3 * δ / 2)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by exact_mod_cast hN) (by linarith)
  -- `log x ≥ (2/δ)(1 − x^{-δ/2})`
  have hterm : ∀ k : ℕ, (2 / δ) * (((N : ℝ) + 1 + k) ^ (-δ - 1) - ((N : ℝ) + 1 + k) ^ (-(3 * δ / 2) - 1)) ≤
      Real.log (((N + 1 : ℕ) : ℝ) + k) * (((N + 1 : ℕ) : ℝ) + k) ^ (-δ - 1) := fun k => by
    push_cast
    set x : ℝ := (N : ℝ) + 1 + k
    have hx : 0 < x := by positivity
    have hlog : (2 / δ) * (1 - x ^ (-(δ / 2))) ≤ Real.log x := by
      have h := Real.one_sub_inv_le_log_of_pos (Real.rpow_pos_of_pos hx (δ / 2))
      rw [Real.log_rpow hx, ← Real.rpow_neg hx.le] at h
      calc (2 / δ) * (1 - x ^ (-(δ / 2))) ≤ (2 / δ) * (δ / 2 * Real.log x) :=
            mul_le_mul_of_nonneg_left h (by positivity)
        _ = Real.log x := by field_simp
    have hsplit : x ^ (-(3 * δ / 2) - 1) = x ^ (-(δ / 2)) * x ^ (-δ - 1) := by
      rw [← Real.rpow_add hx]; ring_nf
    rw [hsplit]
    have hp : 0 ≤ x ^ (-δ - 1) := Real.rpow_nonneg hx.le _
    calc (2 / δ) * (x ^ (-δ - 1) - x ^ (-(δ / 2)) * x ^ (-δ - 1))
        = (2 / δ) * (1 - x ^ (-(δ / 2))) * x ^ (-δ - 1) := by ring
      _ ≤ Real.log x * x ^ (-δ - 1) := mul_le_mul_of_nonneg_right hlog hp
  have hsum : Summable (fun k : ℕ => (2 / δ) * (((N : ℝ) + 1 + k) ^ (-δ - 1) -
      ((N : ℝ) + 1 + k) ^ (-(3 * δ / 2) - 1))) := (hs1.sub hs2).mul_left _
  have hsumL : Summable (fun k : ℕ => Real.log (((N + 1 : ℕ) : ℝ) + k) *
      (((N + 1 : ℕ) : ℝ) + k) ^ (-δ - 1)) := by
    refine (HTGeometry.summable_shift_rpow (q := -(δ / 2)) (by linarith) N |>.mul_left (2 / δ)).of_nonneg_of_le
      (fun k => mul_nonneg (Real.log_nonneg (by push_cast; linarith [show (0 : ℝ) ≤ k from Nat.cast_nonneg k]))
        (Real.rpow_nonneg (by positivity) _)) fun k => ?_
    push_cast
    set x : ℝ := (N : ℝ) + 1 + k
    have hx : 0 < x := by positivity
    have hlog := Real.log_le_rpow_div hx.le (show 0 < δ / 2 by linarith)
    have hp : 0 ≤ x ^ (-δ - 1) := Real.rpow_nonneg hx.le _
    calc Real.log x * x ^ (-δ - 1) ≤ x ^ (δ / 2) / (δ / 2) * x ^ (-δ - 1) :=
          mul_le_mul_of_nonneg_right hlog hp
      _ = (2 / δ) * x ^ (-(δ / 2) - 1) := by
          rw [div_eq_mul_inv, mul_comm (x ^ (δ / 2)), mul_assoc, ← Real.rpow_add hx]
          field_simp; ring_nf
  calc (2 / δ ^ 2) * ((((N + 1 : ℕ) : ℝ)) ^ (-δ) - 2 / 3)
      ≤ (2 / δ) * (((N : ℝ) + 1) ^ (-δ) / δ - 1 / (3 * δ / 2)) := by
        push_cast
        apply le_of_eq
        field_simp
    _ ≤ (2 / δ) * (∑' k : ℕ, ((N : ℝ) + 1 + k) ^ (-δ - 1) -
          ∑' k : ℕ, ((N : ℝ) + 1 + k) ^ (-(3 * δ / 2) - 1)) := by
        refine mul_le_mul_of_nonneg_left (sub_le_sub hlow ?_) (by positivity)
        exact hup.trans (div_le_div_of_nonneg_right hN1 (by positivity))
    _ = ∑' k : ℕ, (2 / δ) * (((N : ℝ) + 1 + k) ^ (-δ - 1) - ((N : ℝ) + 1 + k) ^ (-(3 * δ / 2) - 1)) := by
        rw [tsum_mul_left, hs1.tsum_sub hs2]
    _ ≤ _ := Summable.tsum_le_tsum hterm hsum hsumL

/-- **A logarithmic drift is a double pole.** If `q ≥ 0` has drift
`n Σ_{(n,2n]} q(d)/d ≥ κ n^{1−ε} log n` from `N₀ ≥ 1` on, then at `σ = 1 − ε + δ`
`Σ_n A_q(n) Δ_n(σ) ≤ −(κσ/2) ((2/δ²)((N₀+1)^{-δ} − 2/3) − log 2/δ)`. -/
theorem tsum_mul_mellinCell_le_of_log_drift {q : ℕ → ℝ} {m κ ε δ : ℝ} (hq : ∀ d, 0 ≤ q d)
    (hm : HasSum (fun d : ℕ => q d / d) m) (hκ : 0 ≤ κ) (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) (hδ : 0 < δ)
    {N₀ : ℕ} (hN₀ : 1 ≤ N₀)
    (hdrift : ∀ n, N₀ ≤ n →
      κ * (n : ℝ) ^ (1 - ε) * Real.log n ≤ (n : ℝ) * ∑ d ∈ Ioc n (2 * n), q d / d)
    (hs : Summable (fun n => weightCenteredPrefix q m n * mellinCell (1 - ε + δ) n)) :
    ∑' n, weightCenteredPrefix q m n * mellinCell (1 - ε + δ) n ≤
      -(κ * (1 - ε + δ) / 2) *
        ((2 / δ ^ 2) * ((((N₀ + 1 : ℕ) : ℝ)) ^ (-δ) - 2 / 3) - Real.log 2 / δ) := by
  set σ := 1 - ε + δ
  have hσ : 0 < σ := by simp only [σ]; linarith
  have hneg : ∀ n, weightCenteredPrefix q m n * mellinCell σ n ≤ 0 := fun n => by
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · rw [weightCenteredPrefix_zero, zero_mul]
    · have hA := weightCenteredPrefix_le_neg_drift hq hm n
      have hS : 0 ≤ (n : ℝ) * ∑ d ∈ Ioc n (2 * n), q d / d :=
        mul_nonneg (Nat.cast_nonneg n) (sum_nonneg fun d _ => div_nonneg (hq d) (Nat.cast_nonneg d))
      exact mul_nonpos_of_nonpos_of_nonneg (by linarith) (mellinCell_nonneg hσ hn)
  have hg := HTGeometry.summable_shift_rpow (q := -δ) (by linarith) N₀
  have hN₀R : (1 : ℝ) ≤ N₀ := by exact_mod_cast hN₀
  have hgL : Summable (fun k : ℕ => Real.log ((N₀ : ℝ) + 1 + k) * ((N₀ : ℝ) + 1 + k) ^ (-δ - 1)) := by
    refine (HTGeometry.summable_shift_rpow (q := -(δ / 2)) (by linarith) N₀ |>.mul_left (2 / δ)).of_nonneg_of_le
      (fun k => mul_nonneg (Real.log_nonneg (by
        have : (0 : ℝ) ≤ k := Nat.cast_nonneg k
        linarith)) (Real.rpow_nonneg (by positivity) _)) fun k => ?_
    set x : ℝ := (N₀ : ℝ) + 1 + k
    have hx : 0 < x := by positivity
    have hlog := Real.log_le_rpow_div hx.le (show 0 < δ / 2 by linarith)
    calc Real.log x * x ^ (-δ - 1) ≤ x ^ (δ / 2) / (δ / 2) * x ^ (-δ - 1) :=
          mul_le_mul_of_nonneg_right hlog (Real.rpow_nonneg hx.le _)
      _ = (2 / δ) * x ^ (-(δ / 2) - 1) := by
          rw [div_eq_mul_inv, mul_comm (x ^ (δ / 2)), mul_assoc, ← Real.rpow_add hx]
          field_simp; ring_nf
  -- the tail cells
  have htail : ∀ k : ℕ, weightCenteredPrefix q m (k + N₀) * mellinCell σ (k + N₀) ≤
      -(κ * σ / 2) * ((Real.log ((N₀ : ℝ) + 1 + k) - Real.log 2) * ((N₀ : ℝ) + 1 + k) ^ (-δ - 1)) := by
    intro k
    set n := k + N₀
    have hn : 1 ≤ n := by omega
    have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
    have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
    have hA := (weightCenteredPrefix_le_neg_drift hq hm n).trans (neg_le_neg (hdrift n (by omega)))
    have hb := (mellinCell_bounds hσ hn).1
    have hpow : ((n : ℝ) + 1) ^ (1 - ε) / 2 ≤ (n : ℝ) ^ (1 - ε) := by
      have h1 : ((n : ℝ) + 1) / 2 ≤ n := by linarith
      have h2 : ((1 : ℝ) / 2) ≤ (1 / 2 : ℝ) ^ (1 - ε) := by
        simpa using Real.rpow_le_rpow_of_exponent_ge (x := 1 / 2) (by norm_num) (by norm_num)
          (show 1 - ε ≤ 1 by linarith)
      calc ((n : ℝ) + 1) ^ (1 - ε) / 2 ≤ ((n : ℝ) + 1) ^ (1 - ε) * (1 / 2 : ℝ) ^ (1 - ε) := by
            rw [div_eq_mul_one_div]
            exact mul_le_mul_of_nonneg_left h2 (by positivity)
        _ = (((n : ℝ) + 1) / 2) ^ (1 - ε) := by
            rw [← Real.mul_rpow (by positivity) (by norm_num)]; ring_nf
        _ ≤ (n : ℝ) ^ (1 - ε) := Real.rpow_le_rpow (by positivity) h1 (by linarith)
    have hlog : Real.log ((n : ℝ) + 1) - Real.log 2 ≤ Real.log n := by
      rw [← Real.log_div (by positivity) (by norm_num)]
      exact Real.log_le_log (by positivity) (by linarith)
    have hlog0 : 0 ≤ Real.log ((n : ℝ) + 1) - Real.log 2 := by
      rw [sub_nonneg]; exact Real.log_le_log (by norm_num) (by linarith)
    have hexp : ((n : ℝ) + 1) ^ (1 - ε) * ((n : ℝ) + 1) ^ (-σ - 1) = ((n : ℝ) + 1) ^ (-δ - 1) := by
      rw [← Real.rpow_add (by positivity)]; congr 1; simp only [σ]; ring
    have hcast : (n : ℝ) + 1 = (N₀ : ℝ) + 1 + k := by simp only [n]; push_cast; ring
    have hΔ := mellinCell_nonneg hσ hn
    have hlower : κ * (((n : ℝ) + 1) ^ (1 - ε) / 2) * (Real.log ((n : ℝ) + 1) - Real.log 2) ≤
        κ * (n : ℝ) ^ (1 - ε) * Real.log n :=
      mul_le_mul (mul_le_mul_of_nonneg_left hpow hκ) hlog hlog0 (by positivity)
    calc weightCenteredPrefix q m n * mellinCell σ n
        ≤ -(κ * (n : ℝ) ^ (1 - ε) * Real.log n) * mellinCell σ n := mul_le_mul_of_nonneg_right hA hΔ
      _ ≤ -(κ * (((n : ℝ) + 1) ^ (1 - ε) / 2) * (Real.log ((n : ℝ) + 1) - Real.log 2)) *
            mellinCell σ n := mul_le_mul_of_nonneg_right (neg_le_neg hlower) hΔ
      _ ≤ -(κ * (((n : ℝ) + 1) ^ (1 - ε) / 2) * (Real.log ((n : ℝ) + 1) - Real.log 2)) *
            (σ * ((n : ℝ) + 1) ^ (-σ - 1)) :=
          mul_le_mul_of_nonpos_left hb (by
            have : 0 ≤ κ * (((n : ℝ) + 1) ^ (1 - ε) / 2) * (Real.log ((n : ℝ) + 1) - Real.log 2) := by
              positivity
            linarith)
      _ = -(κ * σ / 2) * ((Real.log ((n : ℝ) + 1) - Real.log 2) *
            (((n : ℝ) + 1) ^ (1 - ε) * ((n : ℝ) + 1) ^ (-σ - 1))) := by ring
      _ = _ := by rw [hexp, hcast]
  rw [← hs.sum_add_tsum_nat_add N₀]
  have hhead : ∑ n ∈ range N₀, weightCenteredPrefix q m n * mellinCell σ n ≤ 0 :=
    sum_nonpos fun n _ => hneg n
  have hdiff : Summable (fun k : ℕ => (Real.log ((N₀ : ℝ) + 1 + k) - Real.log 2) *
      ((N₀ : ℝ) + 1 + k) ^ (-δ - 1)) := (hgL.sub (hg.mul_left (Real.log 2))).congr fun k => by ring
  have htsum : ∑' k : ℕ, weightCenteredPrefix q m (k + N₀) * mellinCell σ (k + N₀) ≤
      -(κ * σ / 2) * ∑' k : ℕ, (Real.log ((N₀ : ℝ) + 1 + k) - Real.log 2) *
        ((N₀ : ℝ) + 1 + k) ^ (-δ - 1) := by
    rw [← tsum_mul_left]
    exact Summable.tsum_le_tsum htail ((summable_nat_add_iff N₀).mpr hs) (hdiff.mul_left _)
  -- the logarithmic tail sum
  have hlogsum := tsum_log_mul_rpow_ge (M := N₀ + 1) (by omega) hδ
  have hup := HTGeometry.tsum_shift_rpow_le (q := -δ) (by linarith) hN₀
  rw [neg_neg] at hup
  have hN1 : ((N₀ : ℝ)) ^ (-δ) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by exact_mod_cast hN₀) (by linarith)
  have hsplit : ∑' k : ℕ, (Real.log ((N₀ : ℝ) + 1 + k) - Real.log 2) * ((N₀ : ℝ) + 1 + k) ^ (-δ - 1) =
      ∑' k : ℕ, Real.log ((N₀ : ℝ) + 1 + k) * ((N₀ : ℝ) + 1 + k) ^ (-δ - 1) -
        Real.log 2 * ∑' k : ℕ, ((N₀ : ℝ) + 1 + k) ^ (-δ - 1) := by
    rw [← tsum_mul_left, ← hgL.tsum_sub (hg.mul_left _)]
    exact tsum_congr fun k => by ring
  have hcastM : ∀ k : ℕ, (((N₀ + 1 : ℕ) : ℝ) + k) = (N₀ : ℝ) + 1 + k := fun k => by push_cast; ring
  simp only [hcastM] at hlogsum
  have hLB : (2 / δ ^ 2) * ((((N₀ + 1 : ℕ) : ℝ)) ^ (-δ) - 2 / 3) - Real.log 2 / δ ≤
      ∑' k : ℕ, (Real.log ((N₀ : ℝ) + 1 + k) - Real.log 2) * ((N₀ : ℝ) + 1 + k) ^ (-δ - 1) := by
    rw [hsplit]
    have hl2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
    have h1 : Real.log 2 * ∑' k : ℕ, ((N₀ : ℝ) + 1 + k) ^ (-δ - 1) ≤ Real.log 2 / δ := by
      rw [div_eq_mul_one_div]
      exact mul_le_mul_of_nonneg_left (hup.trans (div_le_div_of_nonneg_right hN1 hδ.le)) hl2
    linarith
  have hκσ : 0 ≤ κ * σ / 2 := by positivity
  calc ∑ n ∈ range N₀, weightCenteredPrefix q m n * mellinCell σ n +
        ∑' k : ℕ, weightCenteredPrefix q m (k + N₀) * mellinCell σ (k + N₀)
      ≤ 0 + -(κ * σ / 2) * ∑' k : ℕ, (Real.log ((N₀ : ℝ) + 1 + k) - Real.log 2) *
          ((N₀ : ℝ) + 1 + k) ^ (-δ - 1) := add_le_add hhead htsum
    _ ≤ -(κ * σ / 2) * ((2 / δ ^ 2) * ((((N₀ + 1 : ℕ) : ℝ)) ^ (-δ) - 2 / 3) - Real.log 2 / δ) := by
        rw [zero_add, neg_mul, neg_mul, neg_le_neg_iff]
        exact mul_le_mul_of_nonneg_left hLB hκσ

/-- **A pole of order two needs a zero of order two.** Let `0 < ε ≤ 1/2`, let `q ≥ 0` lie in the
damped classes of every exponent below `ε`, with drift `n Σ_{(n,2n]} q(d)/d ≥ κ n^{1−ε} log n`
eventually, and let `k` be supported on `[1, J]`. If the receiver of `k ⋆ q` is bounded, then
`Σ_j k(j) j^{-(1−ε)} = 0` and `Σ_j k(j) log j · j^{-(1−ε)} = 0`. -/
theorem poleValue_eq_zero_and_poleSlope_eq_zero_of_receiverBounded {ε κ : ℝ} (hε : 0 < ε)
    (hε2 : ε ≤ 1 / 2) {q : ℕ → ℝ} (hq : ∀ d, 0 ≤ q d)
    (hclass : ∀ η : ℝ, 0 < η → η < ε → ∃ C : ℝ, DampedClass C (ε - η) q) (hκ : 0 < κ)
    (hdrift : ∀ᶠ n : ℕ in atTop,
      κ * (n : ℝ) ^ (1 - ε) * Real.log n ≤ (n : ℝ) * ∑ d ∈ Ioc n (2 * n), q d / d)
    {k : ℕ → ℝ} {J : ℕ} (hkJ : ∀ j, J < j → k j = 0)
    (hB : ReceiverBounded (RHTower.dirichletConv k q)) :
    poleValue k J ε = 0 ∧ poleSlope k J ε = 0 := by
  obtain ⟨E, hE⟩ := hB
  obtain ⟨N₁, hN₁⟩ := eventually_atTop.mp hdrift
  set N₀ := max N₁ 1
  have hN₀ : 1 ≤ N₀ := le_max_right _ _
  have hdrift' : ∀ n, N₀ ≤ n →
      κ * (n : ℝ) ^ (1 - ε) * Real.log n ≤ (n : ℝ) * ∑ d ∈ Ioc n (2 * n), q d / d :=
    fun n hn => hN₁ n ((le_max_left _ _).trans hn)
  -- the means
  obtain ⟨C₀, hC₀⟩ := hclass (ε / 2) (by linarith) (by linarith)
  have hqs : Summable (fun d : ℕ => q d / d) :=
    summable_div_of_dampedClass (by linarith : (0 : ℝ) < ε - ε / 2) hC₀
  set mq := ∑' d : ℕ, q d / d
  set mk := ∑ j ∈ Icc 1 J, k j / j
  have hkoff : ∀ j ∉ Icc 1 J, k j / j = 0 := fun j hj => by
    rw [mem_Icc, not_and_or] at hj
    rcases hj with hj | hj
    · rw [show j = 0 by omega, Nat.cast_zero, div_zero]
    · rw [hkJ j (by omega), zero_div]
  have hkhas : HasSum (fun j : ℕ => k j / j) mk := hasSum_sum_of_ne_finset_zero hkoff
  have hkabs : Summable (fun j : ℕ => |k j / j|) :=
    summable_of_ne_finset_zero (s := Icc 1 J) fun j hj => by rw [hkoff j hj, abs_zero]
  have hmean : ∑' n : ℕ, RHTower.dirichletConv k q n / n = mk * mq :=
    (hasSum_dirichletConv_div hkhas hqs.hasSum hkabs hqs.abs).tsum_eq
  have hE' : ∀ T, ∑ n ∈ Icc 1 T, weightCenteredPrefix (RHTower.dirichletConv k q) (mk * mq) n ^ 2 /
      ((n : ℝ) * ((n : ℝ) + 1)) ≤ E := fun T => by
    have := hE T; rwa [hmean] at this
  have hE0 : 0 ≤ E := by simpa using hE' 0
  set A := weightCenteredPrefix q mq
  set Ak := weightCenteredPrefix k mk
  have hA0 : A 0 = 0 := weightCenteredPrefix_zero _ _
  have hAk0 : Ak 0 = 0 := weightCenteredPrefix_zero _ _
  set L1 := ∑ j ∈ Icc 1 J, |k j|
  have hAk : ∀ n, |Ak n| ≤ L1 := abs_weightCenteredPrefix_finiteKernel_le hkJ
  have hL1 : 0 ≤ L1 := sum_nonneg fun j _ => abs_nonneg _
  have hconv : ∀ n, weightCenteredPrefix (RHTower.dirichletConv k q) (mk * mq) n =
      ∑ j ∈ Icc 1 J, k j * A (n / j) + mq * Ak n := fun n => by
    rw [weightCenteredPrefix_dirichletConv]
    congr 1
    have hsub1 : Icc 1 n ⊆ Icc 1 (n + J) := Icc_subset_Icc le_rfl (by omega)
    have hsub2 : Icc 1 J ⊆ Icc 1 (n + J) := Icc_subset_Icc le_rfl (by omega)
    rw [sum_subset hsub1 fun d hd hdn => ?_, sum_subset hsub2 fun d hd hdJ => ?_]
    · have : J < d := by simp only [mem_Icc] at hd hdJ; omega
      rw [hkJ d this, zero_mul]
    · have : n < d := by simp only [mem_Icc] at hd hdn; omega
      rw [Nat.div_eq_of_lt this, weightCenteredPrefix_zero, mul_zero]
  set Kσ : ℝ → ℝ := fun δ => ∑ j ∈ Icc 1 J, k j * (j : ℝ) ^ (-(1 - ε + δ))
  set M := (((N₀ + 1 : ℕ) : ℝ))
  set LB : ℝ → ℝ := fun δ => (2 / δ ^ 2) * (M ^ (-δ) - 2 / 3) - Real.log 2 / δ
  have hkey : ∀ δ : ℝ, 0 < δ → δ ≤ 1 / 2 → δ < ε →
      |Kσ δ| * (κ * (1 - ε + δ) / 2 * LB δ) ≤
        Real.sqrt E * Real.sqrt (2 * (1 - ε + δ) ^ 2 * (1 + 1 / (2 * (1 - ε + δ) - 1))) +
          |mq| * (L1 * ((1 - ε + δ) + 1)) := by
    intro δ hδ hδ2 hδε
    set σ := 1 - ε + δ
    have hσ : 1 / 2 < σ := by simp only [σ]; linarith
    have hσ0 : 0 < σ := by linarith
    obtain ⟨C, hC⟩ := hclass (δ / 2) (by linarith) (by linarith)
    have hC0 := nonneg_of_dampedClass hC
    set Cq := C * (1 + 1 / (1 - (ε - δ / 2)) + 1 / (ε - δ / 2))
    have hCq : 0 ≤ Cq := by
      have : 0 < 1 - (ε - δ / 2) := by linarith
      have : 0 < ε - δ / 2 := by linarith
      positivity
    have hAbound : ∀ n, 1 ≤ n → |A n| ≤ Cq * (n : ℝ) ^ (1 - (ε - δ / 2)) := fun n hn =>
      abs_weightCenteredPrefix_le_of_dampedClass (by linarith) (by linarith) hC hn
    have ha : 1 - (ε - δ / 2) < σ := by simp only [σ]; linarith
    have hsA : Summable (fun n => A n * mellinCell σ n) :=
      summable_mul_mellinCell hσ0 ha hA0 hAbound
    have hsAj : ∀ j ∈ Icc 1 J, Summable (fun n => A (n / j) * mellinCell σ n) := fun j hj => by
      refine summable_mul_mellinCell (C := Cq) hσ0 ha (by simp [hA0]) fun n hn => ?_
      rcases Nat.eq_zero_or_pos (n / j) with h0 | h1
      · rw [h0, hA0, abs_zero]; positivity
      · refine (hAbound _ h1).trans (mul_le_mul_of_nonneg_left ?_ hCq)
        exact Real.rpow_le_rpow (Nat.cast_nonneg _) (by exact_mod_cast Nat.div_le_self n j)
          (by linarith)
    have hsAk : Summable (fun n => Ak n * mellinCell σ n) :=
      summable_mul_mellinCell (a := 0) hσ0 hσ0 hAk0 fun n _ => by
        rw [Real.rpow_zero, mul_one]; exact hAk n
    have hsplit : ∀ n, weightCenteredPrefix (RHTower.dirichletConv k q) (mk * mq) n * mellinCell σ n =
        ∑ j ∈ Icc 1 J, k j * (A (n / j) * mellinCell σ n) + mq * (Ak n * mellinCell σ n) :=
      fun n => by
        rw [hconv, add_mul, Finset.sum_mul]
        congr 1
        · exact sum_congr rfl fun j _ => by ring
        · ring
    have hsJ : Summable (fun n => ∑ j ∈ Icc 1 J, k j * (A (n / j) * mellinCell σ n)) :=
      summable_sum fun j hj => (hsAj j hj).mul_left _
    have hsc : Summable (fun n =>
        weightCenteredPrefix (RHTower.dirichletConv k q) (mk * mq) n * mellinCell σ n) := by
      simp_rw [hsplit]; exact hsJ.add (hsAk.mul_left _)
    have hlaw : ∑' n, weightCenteredPrefix (RHTower.dirichletConv k q) (mk * mq) n * mellinCell σ n =
        Kσ δ * ∑' n, A n * mellinCell σ n + mq * ∑' n, Ak n * mellinCell σ n := by
      simp_rw [hsplit]
      rw [hsJ.tsum_add (hsAk.mul_left _), Summable.tsum_finsetSum fun j hj => (hsAj j hj).mul_left _,
        tsum_mul_left]
      congr 1
      simp only [Kσ, sum_mul]
      refine sum_congr rfl fun j hj => ?_
      rw [tsum_mul_left, tsum_comp_div_mul_mellinCell hA0 (mem_Icc.mp hj).1 hsA (hsAj j hj)]
      ring
    have hcs := abs_tsum_mul_mellinCell_le hσ (weightCenteredPrefix_zero _ _) hsc hE'
    have hPk : |∑' n, Ak n * mellinCell σ n| ≤ L1 * (σ + 1) := by
      have hZ := (Real.summable_nat_rpow.mpr (show -(σ + 1) < -1 by linarith)).mul_left (L1 * σ)
      have h := tsum_of_norm_bounded (f := fun n => Ak n * mellinCell σ n) hZ.hasSum fun n => by
        rcases Nat.eq_zero_or_pos n with rfl | hn
        · rw [hAk0, zero_mul, norm_zero]
          exact mul_nonneg (by positivity) (Real.rpow_nonneg (Nat.cast_nonneg _) _)
        · have hb := (mellinCell_bounds hσ0 hn).2
          rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (mellinCell_nonneg hσ0 hn),
            show -(σ + 1) = -σ - 1 by ring, mul_assoc]
          exact mul_le_mul (hAk n) hb (mellinCell_nonneg hσ0 hn) hL1
      rw [Real.norm_eq_abs, tsum_mul_left] at h
      refine h.trans ?_
      have hzeta := RHTower.Sieve.tsum_nat_rpow_neg_le (show 1 < σ + 1 by linarith)
      calc L1 * σ * ∑' n : ℕ, (n : ℝ) ^ (-(σ + 1)) ≤ L1 * σ * (1 + 1 / (σ + 1 - 1)) :=
            mul_le_mul_of_nonneg_left hzeta (by positivity)
        _ = L1 * (σ + 1) := by
            have hσne : σ ≠ 0 := hσ0.ne'
            rw [add_sub_cancel_right]; field_simp
    have hdrift'' := tsum_mul_mellinCell_le_of_log_drift hq hqs.hasSum hκ.le hε.le (by linarith) hδ
      hN₀ hdrift' hsA
    set Φ := ∑' n, A n * mellinCell σ n
    have hΦ : (κ * σ / 2) * LB δ ≤ |Φ| := by
      have := neg_le_abs Φ
      simp only [LB, M]; linarith
    have habs : |Kσ δ| * |Φ| ≤
        Real.sqrt E * Real.sqrt (2 * σ ^ 2 * (1 + 1 / (2 * σ - 1))) + |mq| * (L1 * (σ + 1)) := by
      rw [← abs_mul, show Kσ δ * Φ = (Kσ δ * Φ + mq * ∑' n, Ak n * mellinCell σ n) -
        mq * ∑' n, Ak n * mellinCell σ n by ring, ← hlaw]
      refine (abs_sub _ _).trans (add_le_add hcs ?_)
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left hPk (abs_nonneg _)
    calc |Kσ δ| * (κ * σ / 2 * LB δ) ≤ |Kσ δ| * |Φ| :=
          mul_le_mul_of_nonneg_left hΦ (abs_nonneg _)
      _ ≤ _ := habs
  -- the bound on the receiver term, scaled by `δ`
  have hBδ : ∀ δ : ℝ, 0 < δ → δ ≤ 1 / 2 →
      Real.sqrt (2 * (1 - ε + δ) ^ 2 * (1 + 1 / (2 * (1 - ε + δ) - 1))) * δ ≤
        Real.sqrt (9 / 2 * (δ ^ 2 + δ / 2)) := fun δ hδ hδ2 => by
    set σ := 1 - ε + δ
    have h2σ0 : 0 < 2 * σ - 1 := by simp only [σ]; linarith
    have hBnn : 0 ≤ 1 + 1 / (2 * σ - 1) := by positivity
    rw [show Real.sqrt (2 * σ ^ 2 * (1 + 1 / (2 * σ - 1))) * δ =
        Real.sqrt (2 * σ ^ 2 * (1 + 1 / (2 * σ - 1)) * δ ^ 2) by
      rw [Real.sqrt_mul (x := 2 * σ ^ 2 * (1 + 1 / (2 * σ - 1))) (by positivity) (δ ^ 2),
        Real.sqrt_sq hδ.le]]
    refine Real.sqrt_le_sqrt ?_
    have h2σ : 2 * δ ≤ 2 * σ - 1 := by simp only [σ]; linarith
    have hinv : 1 / (2 * σ - 1) ≤ 1 / (2 * δ) := one_div_le_one_div_of_le (by positivity) h2σ
    have hσ2 : σ ^ 2 ≤ 9 / 4 := by
      have : σ ≤ 3 / 2 := by simp only [σ]; linarith
      have : 0 ≤ σ := by simp only [σ]; linarith
      nlinarith
    calc 2 * σ ^ 2 * (1 + 1 / (2 * σ - 1)) * δ ^ 2 ≤ 2 * (9 / 4) * (1 + 1 / (2 * δ)) * δ ^ 2 := by
          refine mul_le_mul_of_nonneg_right ?_ (by positivity)
          exact mul_le_mul (by linarith) (by linarith) hBnn (by norm_num)
      _ = 9 / 2 * (δ ^ 2 + δ / 2) := by field_simp; ring
  -- `δ² LB(δ) → 2/3`
  have hG : Tendsto (fun δ : ℝ => 2 * (M ^ (-δ) - 2 / 3) - δ * Real.log 2) (𝓝 0) (𝓝 (2 / 3)) := by
    have hM0 : M ≠ 0 := by simp only [M]; positivity
    have hc : Continuous (fun δ : ℝ => 2 * (M ^ (-δ) - 2 / 3) - δ * Real.log 2) := by
      have : Continuous (fun δ : ℝ => M ^ (-δ)) := continuous_const.rpow (by fun_prop) fun _ => Or.inl hM0
      fun_prop
    have := hc.tendsto 0
    rw [neg_zero, Real.rpow_zero, zero_mul, sub_zero] at this
    convert this using 2; norm_num
  have hGeq : ∀ δ : ℝ, 0 < δ → δ ^ 2 * LB δ = 2 * (M ^ (-δ) - 2 / 3) - δ * Real.log 2 := fun δ hδ => by
    simp only [LB]; field_simp
  have hR : Tendsto (fun δ : ℝ => Real.sqrt E * Real.sqrt (9 / 2 * (δ ^ 2 + δ / 2)) +
      δ * (|mq| * (L1 * ((1 - ε + δ) + 1)))) (𝓝 0) (𝓝 0) := by
    have hc : Continuous (fun δ : ℝ => Real.sqrt E * Real.sqrt (9 / 2 * (δ ^ 2 + δ / 2)) +
        δ * (|mq| * (L1 * ((1 - ε + δ) + 1)))) := by fun_prop
    simpa using hc.tendsto 0
  have hKcont : Tendsto Kσ (𝓝 0) (𝓝 (Kσ 0)) := by
    have : Continuous Kσ := by
      refine continuous_finsetSum _ fun j hj => continuous_const.mul ?_
      have hj0 : (j : ℝ) ≠ 0 := by have := (mem_Icc.mp hj).1; positivity
      exact continuous_const.rpow (by fun_prop) fun _ => Or.inl hj0
    exact this.tendsto 0
  have hK0 : Kσ 0 = poleValue k J ε := by simp [Kσ, poleValue]
  -- `Kσ` has derivative `−poleSlope` at `0`
  have hderiv : HasDerivAt Kσ (-poleSlope k J ε) 0 := by
    have h : ∀ j ∈ Icc 1 J, HasDerivAt (fun δ : ℝ => k j * (j : ℝ) ^ (-(1 - ε + δ)))
        (k j * ((j : ℝ) ^ (-(1 - ε + 0)) * Real.log j * (-1))) 0 := fun j hj => by
      have hj0 : (0 : ℝ) < j := by exact_mod_cast (mem_Icc.mp hj).1
      have h1 : HasDerivAt (fun δ : ℝ => -(1 - ε + δ)) (-1) 0 := by
        have h := ((hasDerivAt_id (0 : ℝ)).const_add (1 - ε)).neg
        exact h.congr_of_eventuallyEq (Eventually.of_forall fun x => by simp)
      exact ((Real.hasStrictDerivAt_const_rpow hj0 _).hasDerivAt.comp 0 h1).const_mul (k j)
    refine (HasDerivAt.fun_sum h).congr_deriv ?_
    simp only [poleSlope, add_zero, ← sum_neg_distrib]
    exact sum_congr rfl fun j _ => by ring
  have hlin : Tendsto (fun δ : ℝ => κ * (1 - ε + δ) / 2) (𝓝 0) (𝓝 (κ * (1 - ε) / 2)) := by
    have hc : Continuous (fun δ : ℝ => κ * (1 - ε + δ) / 2) := by fun_prop
    simpa using hc.tendsto 0
  have hpos : 0 < κ * (1 - ε) / 2 * (2 / 3) := by
    have : 0 < 1 - ε := by linarith
    positivity
  -- part one: the pole value vanishes
  have hpart1 : poleValue k J ε = 0 := by
    by_contra hK
    have hlhs : Tendsto (fun δ : ℝ => |Kσ δ| * (κ * (1 - ε + δ) / 2 * (2 * (M ^ (-δ) - 2 / 3) -
        δ * Real.log 2))) (𝓝 0) (𝓝 (|poleValue k J ε| * (κ * (1 - ε) / 2 * (2 / 3)))) := by
      rw [← hK0]
      exact (continuous_abs.tendsto _ |>.comp hKcont).mul (hlin.mul hG)
    have hL0 : 0 < |poleValue k J ε| * (κ * (1 - ε) / 2 * (2 / 3)) :=
      mul_pos (abs_pos.mpr hK) hpos
    have hev : ∀ᶠ δ in 𝓝[>] (0 : ℝ),
        |poleValue k J ε| * (κ * (1 - ε) / 2 * (2 / 3)) / 2 <
          |Kσ δ| * (κ * (1 - ε + δ) / 2 * (2 * (M ^ (-δ) - 2 / 3) - δ * Real.log 2)) ∧
        δ * (Real.sqrt E * Real.sqrt (9 / 2 * (δ ^ 2 + δ / 2)) +
          δ * (|mq| * (L1 * ((1 - ε + δ) + 1)))) <
            |poleValue k J ε| * (κ * (1 - ε) / 2 * (2 / 3)) / 2 ∧
        0 < δ ∧ δ ≤ 1 / 2 ∧ δ < ε := by
      have hRδ : Tendsto (fun δ : ℝ => δ * (Real.sqrt E * Real.sqrt (9 / 2 * (δ ^ 2 + δ / 2)) +
          δ * (|mq| * (L1 * ((1 - ε + δ) + 1))))) (𝓝 0) (𝓝 0) := by
        simpa using (tendsto_id (x := 𝓝 (0 : ℝ))).mul hR
      refine (tendsto_nhdsWithin_of_tendsto_nhds hlhs |>.eventually (lt_mem_nhds (by linarith))).and
        ((tendsto_nhdsWithin_of_tendsto_nhds hRδ |>.eventually (gt_mem_nhds (by linarith))).and
        ((eventually_nhdsWithin_of_forall fun δ hδ => hδ).and
        ((tendsto_nhdsWithin_of_tendsto_nhds tendsto_id |>.eventually
          (eventually_le_nhds (by norm_num))).and
        (tendsto_nhdsWithin_of_tendsto_nhds tendsto_id |>.eventually (eventually_lt_nhds hε)))))
    obtain ⟨δ, h1, h2, hδ, hδ2, hδε⟩ := hev.exists
    have hk := hkey δ hδ hδ2 hδε
    have hb := hBδ δ hδ hδ2
    have hk2 : |Kσ δ| * (κ * (1 - ε + δ) / 2 * (2 * (M ^ (-δ) - 2 / 3) - δ * Real.log 2)) ≤
        δ * (Real.sqrt E * Real.sqrt (9 / 2 * (δ ^ 2 + δ / 2)) +
          δ * (|mq| * (L1 * ((1 - ε + δ) + 1)))) := by
      rw [← hGeq δ hδ]
      have hs := mul_le_mul_of_nonneg_left hk (sq_nonneg δ)
      calc |Kσ δ| * (κ * (1 - ε + δ) / 2 * (δ ^ 2 * LB δ))
          = δ ^ 2 * (|Kσ δ| * (κ * (1 - ε + δ) / 2 * LB δ)) := by ring
        _ ≤ δ ^ 2 * (Real.sqrt E * Real.sqrt (2 * (1 - ε + δ) ^ 2 * (1 + 1 / (2 * (1 - ε + δ) - 1))) +
            |mq| * (L1 * ((1 - ε + δ) + 1))) := hs
        _ = δ * (Real.sqrt E * (Real.sqrt (2 * (1 - ε + δ) ^ 2 * (1 + 1 / (2 * (1 - ε + δ) - 1))) * δ) +
            δ * (|mq| * (L1 * ((1 - ε + δ) + 1)))) := by ring
        _ ≤ _ := by
            refine mul_le_mul_of_nonneg_left (add_le_add ?_ le_rfl) hδ.le
            exact mul_le_mul_of_nonneg_left hb (Real.sqrt_nonneg _)
    linarith
  -- part two: the slope vanishes
  refine ⟨hpart1, ?_⟩
  by_contra hK'
  have hslope : Tendsto (fun δ : ℝ => δ⁻¹ * Kσ δ) (𝓝[>] 0) (𝓝 (-poleSlope k J ε)) := by
    have := hderiv.tendsto_slope_zero_right
    simp only [zero_add, smul_eq_mul, hK0, hpart1, sub_zero] at this
    exact this
  have hlhs : Tendsto (fun δ : ℝ => |δ⁻¹ * Kσ δ| * (κ * (1 - ε + δ) / 2 * (2 * (M ^ (-δ) - 2 / 3) -
      δ * Real.log 2))) (𝓝[>] 0) (𝓝 (|poleSlope k J ε| * (κ * (1 - ε) / 2 * (2 / 3)))) := by
    have h := (continuous_abs.tendsto _ |>.comp hslope).mul
      (tendsto_nhdsWithin_of_tendsto_nhds (hlin.mul hG))
    simpa [abs_neg] using h
  have hL0 : 0 < |poleSlope k J ε| * (κ * (1 - ε) / 2 * (2 / 3)) := mul_pos (abs_pos.mpr hK') hpos
  have hev : ∀ᶠ δ in 𝓝[>] (0 : ℝ),
      |poleSlope k J ε| * (κ * (1 - ε) / 2 * (2 / 3)) / 2 <
        |δ⁻¹ * Kσ δ| * (κ * (1 - ε + δ) / 2 * (2 * (M ^ (-δ) - 2 / 3) - δ * Real.log 2)) ∧
      Real.sqrt E * Real.sqrt (9 / 2 * (δ ^ 2 + δ / 2)) + δ * (|mq| * (L1 * ((1 - ε + δ) + 1))) <
        |poleSlope k J ε| * (κ * (1 - ε) / 2 * (2 / 3)) / 2 ∧
      0 < δ ∧ δ ≤ 1 / 2 ∧ δ < ε := by
    refine (hlhs.eventually (lt_mem_nhds (by linarith))).and
      ((tendsto_nhdsWithin_of_tendsto_nhds hR |>.eventually (gt_mem_nhds (by linarith))).and
      ((eventually_nhdsWithin_of_forall fun δ hδ => hδ).and
      ((tendsto_nhdsWithin_of_tendsto_nhds tendsto_id |>.eventually
        (eventually_le_nhds (by norm_num))).and
      (tendsto_nhdsWithin_of_tendsto_nhds tendsto_id |>.eventually (eventually_lt_nhds hε)))))
  obtain ⟨δ, h1, h2, hδ, hδ2, hδε⟩ := hev.exists
  have hk := hkey δ hδ hδ2 hδε
  have hb := hBδ δ hδ hδ2
  have hk2 : |δ⁻¹ * Kσ δ| * (κ * (1 - ε + δ) / 2 * (2 * (M ^ (-δ) - 2 / 3) - δ * Real.log 2)) ≤
      Real.sqrt E * Real.sqrt (9 / 2 * (δ ^ 2 + δ / 2)) + δ * (|mq| * (L1 * ((1 - ε + δ) + 1))) := by
    rw [← hGeq δ hδ, abs_mul, abs_of_pos (inv_pos.mpr hδ)]
    have hs := mul_le_mul_of_nonneg_left hk hδ.le
    calc δ⁻¹ * |Kσ δ| * (κ * (1 - ε + δ) / 2 * (δ ^ 2 * LB δ))
        = δ * (|Kσ δ| * (κ * (1 - ε + δ) / 2 * LB δ)) := by field_simp
      _ ≤ δ * (Real.sqrt E * Real.sqrt (2 * (1 - ε + δ) ^ 2 * (1 + 1 / (2 * (1 - ε + δ) - 1))) +
          |mq| * (L1 * ((1 - ε + δ) + 1))) := hs
      _ = Real.sqrt E * (Real.sqrt (2 * (1 - ε + δ) ^ 2 * (1 + 1 / (2 * (1 - ε + δ) - 1))) * δ) +
          δ * (|mq| * (L1 * ((1 - ε + δ) + 1))) := by ring
      _ ≤ _ := add_le_add (mul_le_mul_of_nonneg_left hb (Real.sqrt_nonneg _)) le_rfl
  linarith

/-- The logarithmic smooth power `log(d) d^{-ε}` drifts like `2^{-1-ε} n^{1−ε} log n`. -/
theorem logPow_drift {ε : ℝ} (hε : 0 ≤ ε) {n : ℕ} (hn : 1 ≤ n) :
    (2 : ℝ) ^ (-(1 + ε)) * (n : ℝ) ^ (1 - ε) * Real.log n ≤
      (n : ℝ) * ∑ d ∈ Ioc n (2 * n), Real.log d * (d : ℝ) ^ (-ε) / d := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hcell : ∀ d ∈ Ioc n (2 * n), Real.log n * (2 * (n : ℝ)) ^ (-(1 + ε)) ≤
      Real.log d * (d : ℝ) ^ (-ε) / d := fun d hd => by
    have hd := mem_Ioc.mp hd
    have hd0 : (0 : ℝ) < d := by exact_mod_cast (show 0 < d by omega)
    have hd1 : (n : ℝ) ≤ d := by exact_mod_cast hd.1.le
    have hd2 : (d : ℝ) ≤ 2 * n := by exact_mod_cast hd.2
    have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
    rw [mul_div_assoc, div_eq_mul_inv ((d : ℝ) ^ (-ε)), ← Real.rpow_neg_one, ← Real.rpow_add hd0,
      show -ε + -1 = -(1 + ε) by ring]
    exact mul_le_mul (Real.log_le_log hn0 hd1) (Real.rpow_le_rpow_of_nonpos hd0 hd2 (by linarith))
      (Real.rpow_nonneg (by positivity) _) (Real.log_nonneg (by linarith))
  have hsum := sum_le_sum hcell
  rw [sum_const, Nat.card_Ioc, show 2 * n - n = n by omega, nsmul_eq_mul] at hsum
  have hP : (2 * (n : ℝ)) ^ (-(1 + ε)) = (2 : ℝ) ^ (-(1 + ε)) * (n : ℝ) ^ (-(1 + ε)) :=
    Real.mul_rpow (by norm_num) hn0.le
  have hpow : (n : ℝ) * ((n : ℝ) * (n : ℝ) ^ (-(1 + ε))) = (n : ℝ) ^ (1 - ε) := by
    rw [show (1 - ε) = 1 + (1 + -(1 + ε)) by ring, Real.rpow_add hn0, Real.rpow_add hn0,
      Real.rpow_one]
  calc (2 : ℝ) ^ (-(1 + ε)) * (n : ℝ) ^ (1 - ε) * Real.log n
      = (n : ℝ) * ((n : ℝ) * (Real.log n * (2 * (n : ℝ)) ^ (-(1 + ε)))) := by rw [hP, ← hpow]; ring
    _ ≤ (n : ℝ) * ∑ d ∈ Ioc n (2 * n), Real.log d * (d : ℝ) ^ (-ε) / d :=
        mul_le_mul_of_nonneg_left hsum hn0.le

/-- **The Fermi kernel does not pay the logarithmic smooth power.** For `0 < ε ≤ 1/2` and any
kernel `k` on `[1, J]`: if the receiver of `k ⋆ (log(d) d^{-ε})` is bounded then `k` vanishes to second
order at the pole. In particular `δ₁ − 2^{1−ε}δ₂` (slope `log 2` at the pole) leaves it unpaid. -/
theorem poleValue_eq_zero_and_poleSlope_eq_zero_of_receiverBounded_log {ε : ℝ} (hε : 0 < ε)
    (hε2 : ε ≤ 1 / 2) {k : ℕ → ℝ} {J : ℕ} (hkJ : ∀ j, J < j → k j = 0)
    (hB : ReceiverBounded (RHTower.dirichletConv k (fun d => Real.log d * (d : ℝ) ^ (-ε)))) :
    poleValue k J ε = 0 ∧ poleSlope k J ε = 0 := by
  refine poleValue_eq_zero_and_poleSlope_eq_zero_of_receiverBounded hε hε2
    (fun d => mul_nonneg (Real.log_natCast_nonneg d) (Real.rpow_nonneg (Nat.cast_nonneg d) _))
    (fun η hη hηε => ⟨1 / η, fun d => ?_⟩) (κ := (2 : ℝ) ^ (-(1 + ε))) (by positivity)
    (by filter_upwards [eventually_ge_atTop 1] with n hn using logPow_drift hε.le hn) hkJ hB
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · show |Real.log ((0 : ℕ) : ℝ) * ((0 : ℕ) : ℝ) ^ (-ε)| ≤ 1 / η * ((0 : ℕ) : ℝ) ^ (-(ε - η))
    rw [Nat.cast_zero, Real.log_zero, zero_mul, abs_zero,
      Real.zero_rpow (show -(ε - η) ≠ 0 by linarith), mul_zero]
  have hd0 : (0 : ℝ) < d := by exact_mod_cast hd
  have hlog := Real.log_le_rpow_div hd0.le hη
  rw [abs_mul, abs_of_nonneg (Real.log_natCast_nonneg d),
    abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg d) _)]
  calc Real.log d * (d : ℝ) ^ (-ε) ≤ (d : ℝ) ^ η / η * (d : ℝ) ^ (-ε) :=
        mul_le_mul_of_nonneg_right hlog (Real.rpow_nonneg (Nat.cast_nonneg d) _)
    _ = 1 / η * (d : ℝ) ^ (-(ε - η)) := by
        rw [div_eq_mul_one_div, mul_comm ((d : ℝ) ^ η), mul_assoc, ← Real.rpow_add hd0]
        ring_nf

end

end GaloisForLFunctions.TransHorizonIncidenceMechanics
