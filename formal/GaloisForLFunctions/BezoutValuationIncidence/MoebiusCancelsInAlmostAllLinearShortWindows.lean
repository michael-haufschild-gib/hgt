import GaloisForLFunctions.RHTower.Sieve.MoebiusAveragedMeanSquareAllLengths
import GaloisForLFunctions.RHTower.Sieve.MarkerScaleTransfer
import GaloisForLFunctions.RHTower.Sieve.StartFibreLength

/-!
# Möbius cancels in almost all linear short windows

The fibre mean square of `RHTower.Sieve` is a mean square over multiplicative windows: at `x` the
fibre of the outer factor `a ∈ [√x, 2√x]` is the window `[x/a, (x + h√x)/a]`, of length
`h·(x/a)/√x`. On a range of starts `t ∈ [Y, Y + D)` take `√x = 2(Y - 1)` and `h = 2Hⱼ`. Every such
start is the fibre start of an outer factor in the block (`exists_start_preimage`), the fibre is
`(t, t + ℓ]` with `Hⱼ - 1 ≤ ℓ ≤ Hⱼ + Hⱼ(D+1)/(Y-1) + 1` (`fibreLen_bounds`), and the start determines
the outer factor. Cutting `[Q, 2Q)` into `m` such ranges, the linear windows `(t, t + H]` are fibres
up to `2 + 2(H+1)/m` points, so

`Σ_{Q ≤ t < 2Q} (Σ_{t < n ≤ t+H} f(n))² ≤ 32 ε' m (H+1)² Q + 2Q (2 + 2(H+1)/m)² + m H²`

whenever the fibre mean squares are `≤ ε' h² √x` at the `m` scales `x = (2(Y-1))²`. Hence for every
length `H(Q) → ∞` that grows by at most one per doubling, Matomäki–Radziwiłł holds in linear windows:

`Σ_{Q ≤ y < 2Q} (Σ_{y < n ≤ y+H} μ(n))² = o(H² Q)`.
-/

open Finset Filter Topology RHTower.Sieve
open scoped BigOperators

namespace GaloisForLFunctions.BezoutValuationIncidence

noncomputable section
set_option autoImplicit false

/-! ## §1. Interval sums -/

/-- Two windows with a common left end differ by at most the distance of their right ends. -/
theorem abs_sum_Ioc_sub_sum_Ioc_le {f : ℕ → ℝ} (hf : ∀ n, |f n| ≤ 1) {a b c : ℕ}
    (hab : a ≤ b) (hac : a ≤ c) :
    |∑ n ∈ Ioc a b, f n - ∑ n ∈ Ioc a c, f n| ≤ |(b : ℝ) - c| := by
  rcases le_total b c with hbc | hcb
  · rw [← sum_Ioc_consecutive f hab hbc, sub_add_cancel_left, abs_neg]
    refine (abs_sum_le_sum_abs _ _).trans ((sum_le_sum fun n _ => hf n).trans ?_)
    have : (b : ℝ) ≤ c := by exact_mod_cast hbc
    rw [sum_const, Nat.card_Ioc, nsmul_eq_mul, mul_one, abs_sub_comm, abs_of_nonneg (by linarith),
      Nat.cast_sub hbc]
  · rw [← sum_Ioc_consecutive f hac hcb, add_sub_cancel_left]
    refine (abs_sum_le_sum_abs _ _).trans ((sum_le_sum fun n _ => hf n).trans ?_)
    have : (c : ℝ) ≤ b := by exact_mod_cast hcb
    rw [sum_const, Nat.card_Ioc, nsmul_eq_mul, mul_one, abs_of_nonneg (by linarith),
      Nat.cast_sub hcb]

theorem abs_sum_Ioc_le_card {f : ℕ → ℝ} (hf : ∀ n, |f n| ≤ 1) (a b : ℕ) :
    |∑ n ∈ Ioc a b, f n| ≤ ((b - a : ℕ) : ℝ) := by
  refine (abs_sum_le_sum_abs _ _).trans ((sum_le_sum fun n _ => hf n).trans ?_)
  rw [sum_const, Nat.card_Ioc, nsmul_eq_mul, mul_one]

/-! ## §2. One range of starts -/

/-- **One range of starts.** At `x = X²`, `X = 2(Y - 1)`, `h = 2Hⱼ`, every start `t ∈ [Y, Y + D)` is the
fibre start of an outer factor in the block, and the fibre is `(t, t + ℓ]` with
`Hⱼ - 1 ≤ ℓ ≤ Hⱼ + Hⱼ(D+1)/(Y-1) + 1`. Hence the linear windows `(t, t + H]` are fibres up to
`δ = 2 + (H+1)(D+1)/(Y-1)` points, and their mean square is at most twice the fibre mean square plus
`2Dδ²`. -/
theorem sum_Ico_window_sq_le_fibre {f : ℕ → ℝ} (hf : ∀ n, |f n| ≤ 1) {Y D H Hj : ℕ}
    (hY : 3 ≤ Y) (hD : Y + D ≤ 2 * (Y - 1)) (hHj : Hj ≤ H + 1) (hHj' : H ≤ Hj + 1) :
    ∑ t ∈ Ico Y (Y + D), (∑ n ∈ Ioc t (t + H), f n) ^ 2 ≤
      2 * ∑ a ∈ outerBlock (((2 * (Y - 1) : ℕ) : ℝ) ^ 2) (2 * Hj),
          (∑ b ∈ innerFibre (((2 * (Y - 1) : ℕ) : ℝ) ^ 2) (2 * Hj) a, f b) ^ 2 +
        2 * D * (2 + (H + 1) * (D + 1) / ((Y - 1 : ℕ) : ℝ)) ^ 2 := by
  classical
  set X : ℕ := 2 * (Y - 1) with hXdef
  set x : ℝ := (X : ℝ) ^ 2 with hxdef
  set h : ℝ := 2 * (Hj : ℝ) with hhdef
  set δ : ℝ := 2 + (H + 1) * (D + 1) / ((Y - 1 : ℕ) : ℝ) with hδ
  have hXR : (X : ℝ) = 2 * ((Y - 1 : ℕ) : ℝ) := by rw [hXdef]; push_cast; ring
  have hY1 : (2 : ℝ) ≤ ((Y - 1 : ℕ) : ℝ) := by
    have : 2 ≤ Y - 1 := by omega
    exact_mod_cast this
  have hX4 : (4 : ℝ) ≤ X := by rw [hXR]; linarith
  have hsx : Real.sqrt x = X := by rw [hxdef, Real.sqrt_sq (Nat.cast_nonneg _)]
  have hx4 : (4 : ℝ) ≤ x := by rw [hxdef]; nlinarith
  have hh0 : 0 ≤ h := by positivity
  -- every start is realised
  have hex : ∀ t ∈ Ico Y (Y + D), ∃ a : ℕ, 1 ≤ a ∧ x / ((t : ℝ) + 1) ≤ (a : ℝ) ∧
      (a : ℝ) < x / (t : ℝ) := by
    intro t ht
    have ht' := mem_Ico.mp ht
    have htX : (t : ℝ) + 1 ≤ X := by
      have : t + 1 ≤ X := by omega
      exact_mod_cast this
    refine exists_start_preimage (by omega) ?_
    rw [hxdef]
    have : (0 : ℝ) ≤ t := Nat.cast_nonneg t
    nlinarith
  choose! a ha using hex
  -- the structure of the fibre above `a t`
  have hfib : ∀ t ∈ Ico Y (Y + D), a t ∈ outerBlock x h ∧ fibreStartIdx x (a t) = t ∧
      |∑ n ∈ Ioc t (t + H), f n - ∑ b ∈ innerFibre x h (a t), f b| ≤ δ := by
    intro t ht
    obtain ⟨ha1, hlow, hhigh⟩ := ha t ht
    have ht' := mem_Ico.mp ht
    have ht1 : 1 ≤ t := by omega
    have htR : ((Y - 1 : ℕ) : ℝ) < t := by
      have : Y - 1 < t := by omega
      exact_mod_cast this
    have htX : (t : ℝ) + 1 ≤ X := by
      have : t + 1 ≤ X := by omega
      exact_mod_cast this
    have ht0 : (0 : ℝ) < t := by exact_mod_cast ht1
    have hstart := fibreStartIdx_eq_of_start_interval ht1 ha1 hlow hhigh
    have hmem : a t ∈ outerBlock x h := by
      rw [mem_outerBlock, hsx]
      have hXa : (X : ℝ) ≤ a t := by
        refine le_trans ?_ hlow
        rw [le_div_iff₀ (by linarith), hxdef]
        nlinarith
      have ha2 : (a t : ℝ) ≤ 2 * X := by
        refine (le_of_lt hhigh).trans ?_
        rw [div_le_iff₀ ht0, hxdef]
        have : (X : ℝ) ≤ 2 * t := by rw [hXR]; linarith
        nlinarith
      refine ⟨⟨ha1, Nat.le_floor ?_⟩, hXa, ha2⟩
      have : 0 ≤ h * X := by positivity
      rw [hxdef]
      nlinarith
    refine ⟨hmem, hstart, ?_⟩
    have hlen := fibreLen_bounds hx4 hh0 ht1 ha1 hstart hlow hhigh
    rw [hsx] at hlen
    rw [innerFibre_eq_Ioc hx4 hh0 hmem, hstart]
    refine (abs_sum_Ioc_sub_sum_Ioc_le hf (by omega) (by omega)).trans ?_
    push_cast
    have hlo : (Hj : ℝ) - 1 ≤ fibreLen x h (a t) := by
      refine le_trans ?_ hlen.1
      rw [hhdef, hXR]
      have : (Hj : ℝ) ≤ 2 * Hj * t / (2 * ((Y - 1 : ℕ) : ℝ)) := by
        rw [le_div_iff₀ (by positivity)]
        have : (0 : ℝ) ≤ Hj := Nat.cast_nonneg _
        nlinarith
      linarith
    have hhi : (fibreLen x h (a t) : ℝ) ≤ Hj + (H + 1) * (D + 1) / ((Y - 1 : ℕ) : ℝ) + 1 := by
      refine hlen.2.trans ?_
      rw [hhdef, hXR]
      have htD : (t : ℝ) + 1 ≤ ((Y - 1 : ℕ) : ℝ) + (D + 1) := by
        have : t + 1 ≤ (Y - 1) + (D + 1) := by omega
        exact_mod_cast this
      have hHjR : (Hj : ℝ) ≤ H + 1 := by exact_mod_cast hHj
      have hpos : (0 : ℝ) < ((Y - 1 : ℕ) : ℝ) := by linarith
      have e : 2 * (Hj : ℝ) * ((t : ℝ) + 1) / (2 * ((Y - 1 : ℕ) : ℝ)) =
          Hj * ((t : ℝ) + 1) / ((Y - 1 : ℕ) : ℝ) := by field_simp
      rw [e]
      have : (Hj : ℝ) * ((t : ℝ) + 1) / ((Y - 1 : ℕ) : ℝ) ≤
          Hj + (H + 1) * (D + 1) / ((Y - 1 : ℕ) : ℝ) := by
        rw [div_le_iff₀ hpos, add_mul, div_mul_cancel₀ _ hpos.ne']
        have : (0 : ℝ) ≤ Hj := Nat.cast_nonneg _
        have : (0 : ℝ) ≤ (D : ℝ) + 1 := by positivity
        nlinarith
      linarith
    have hHR : (H : ℝ) ≤ Hj + 1 := by exact_mod_cast hHj'
    have hHR' : (Hj : ℝ) ≤ H + 1 := by exact_mod_cast hHj
    have hq : 0 ≤ (H + 1 : ℝ) * (D + 1) / ((Y - 1 : ℕ) : ℝ) := by positivity
    rw [abs_le]
    constructor <;> linarith
  -- square, sum, and push the fibres into the block through the injective choice
  have hinj : Set.InjOn a (Ico Y (Y + D) : Set ℕ) := by
    intro t ht t' ht' heq
    rw [← (hfib t ht).2.1, ← (hfib t' ht').2.1, heq]
  have hδ0 : 0 ≤ δ := by
    have : 0 ≤ (H + 1 : ℝ) * (D + 1) / ((Y - 1 : ℕ) : ℝ) := by positivity
    linarith
  calc ∑ t ∈ Ico Y (Y + D), (∑ n ∈ Ioc t (t + H), f n) ^ 2
      ≤ ∑ t ∈ Ico Y (Y + D), (2 * (∑ b ∈ innerFibre x h (a t), f b) ^ 2 + 2 * δ ^ 2) := by
        refine sum_le_sum fun t ht => ?_
        have hd := (hfib t ht).2.2
        set u := ∑ n ∈ Ioc t (t + H), f n
        set v := ∑ b ∈ innerFibre x h (a t), f b
        have hsq : (u - v) ^ 2 ≤ δ ^ 2 := by
          rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) hd 2
        nlinarith [sq_nonneg (u - 2 * v), sq_nonneg (u + v)]
    _ = 2 * ∑ t ∈ Ico Y (Y + D), (∑ b ∈ innerFibre x h (a t), f b) ^ 2 + 2 * D * δ ^ 2 := by
        rw [sum_add_distrib, ← mul_sum, sum_const, Nat.card_Ico, Nat.add_sub_cancel_left,
          nsmul_eq_mul]
        ring
    _ ≤ 2 * ∑ a' ∈ outerBlock x h, (∑ b ∈ innerFibre x h a', f b) ^ 2 + 2 * D * δ ^ 2 := by
        gcongr
        rw [← sum_image (f := fun a' => (∑ b ∈ innerFibre x h a', f b) ^ 2) hinj]
        refine sum_le_sum_of_subset_of_nonneg (fun a' ha' => ?_) fun _ _ _ => sq_nonneg _
        obtain ⟨t, ht, rfl⟩ := mem_image.mp ha'
        exact (hfib t ht).1

/-! ## §3. Almost all linear windows -/

theorem sum_Ico_eq_sum_range_blocks (g : ℕ → ℝ) (Q D m : ℕ) :
    ∑ t ∈ Ico Q (Q + m * D), g t = ∑ j ∈ range m, ∑ t ∈ Ico (Q + j * D) (Q + j * D + D), g t := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [show Q + (m + 1) * D = Q + m * D + D by ring,
      ← Finset.sum_Ico_consecutive g (Nat.le_add_right Q (m * D)) (Nat.le_add_right _ D), ih,
      Finset.sum_range_succ]

/-- The bound at one `Q`, from fibre bounds at the `m` scales `x = (2(Y-1))²`, `Y = Q + jD`. -/
theorem sum_window_sq_le_of_fibre_bounds {f : ℕ → ℝ} (hf : ∀ n, |f n| ≤ 1) {H : ℕ → ℕ}
    (hmono : Monotone H) (hslow : ∀ k, H (2 * k) ≤ H k + 1) {Q m : ℕ} (hm : 2 ≤ m)
    (hQ : 2 * m + 8 ≤ Q) {ε' : ℝ} (hε' : 0 ≤ ε')
    (hfib : ∀ Y, Q ≤ Y → Y ≤ 2 * Q →
      ∑ a ∈ outerBlock (((2 * (Y - 1) : ℕ) : ℝ) ^ 2) (2 * (H (Y - 1) : ℝ)),
          (∑ b ∈ innerFibre (((2 * (Y - 1) : ℕ) : ℝ) ^ 2) (2 * (H (Y - 1) : ℝ)) a, f b) ^ 2 ≤
        ε' * (2 * (H (Y - 1) : ℝ)) ^ 2 * ((2 * (Y - 1) : ℕ) : ℝ)) :
    ∑ t ∈ Ico Q (2 * Q), (∑ n ∈ Ioc t (t + H Q), f n) ^ 2 ≤
      32 * ε' * m * ((H Q : ℝ) + 1) ^ 2 * Q + 2 * Q * (2 + 2 * ((H Q : ℝ) + 1) / m) ^ 2 +
        m * (H Q : ℝ) ^ 2 := by
  have hmD : m * (Q / m) ≤ Q := Nat.mul_div_le Q m
  have hdm := Nat.div_add_mod Q m
  have hml := Nat.mod_lt Q (by omega : 0 < m)
  set D := Q / m with hDdef
  have hrem : Q - m * D < m := by omega
  have hD2 : D + 2 ≤ Q := by
    have : 2 * D ≤ m * D := Nat.mul_le_mul_right _ hm
    omega
  have hmR : (1 : ℝ) ≤ m := by exact_mod_cast (by omega : 1 ≤ m)
  have hQR : (0 : ℝ) ≤ Q := Nat.cast_nonneg _
  set HQ : ℝ := (H Q : ℝ)
  have hHQ0 : 0 ≤ HQ := Nat.cast_nonneg _
  -- the bound on one range
  have hrange : ∀ j < m, ∑ t ∈ Ico (Q + j * D) (Q + j * D + D), (∑ n ∈ Ioc t (t + H Q), f n) ^ 2 ≤
      32 * ε' * (HQ + 1) ^ 2 * Q + 2 * D * (2 + 2 * (HQ + 1) / m) ^ 2 := by
    intro j hj
    set Y := Q + j * D
    have hjD : j * D ≤ m * D := Nat.mul_le_mul_right _ hj.le
    have hYQ : Q ≤ Y := by omega
    have hY2 : Y ≤ 2 * Q := by omega
    have hHj : H (Y - 1) ≤ H Q + 1 :=
      (hmono (by omega : Y - 1 ≤ 2 * Q)).trans (hslow Q)
    have hHj' : H Q ≤ H (Y - 1) + 1 :=
      (hmono (by omega : Q ≤ 2 * (Q - 1))).trans ((hslow (Q - 1)).trans
        (by have := hmono (by omega : Q - 1 ≤ Y - 1); omega))
    have h1 := sum_Ico_window_sq_le_fibre hf (Y := Y) (D := D) (by omega) (by omega) hHj hHj'
    have h2 := hfib Y hYQ hY2
    have hHjR : (H (Y - 1) : ℝ) ≤ HQ + 1 := by
      have : ((H (Y - 1) : ℕ) : ℝ) ≤ ((H Q + 1 : ℕ) : ℝ) := by exact_mod_cast hHj
      push_cast at this
      exact this
    have hYR : ((2 * (Y - 1) : ℕ) : ℝ) ≤ 4 * Q := by
      have : 2 * (Y - 1) ≤ 4 * Q := by omega
      exact_mod_cast this
    have hfibb : ε' * (2 * (H (Y - 1) : ℝ)) ^ 2 * ((2 * (Y - 1) : ℕ) : ℝ) ≤
        16 * ε' * (HQ + 1) ^ 2 * Q := by
      have hsq : (2 * (H (Y - 1) : ℝ)) ^ 2 ≤ 4 * (HQ + 1) ^ 2 := by
        have : (0 : ℝ) ≤ H (Y - 1) := Nat.cast_nonneg _
        nlinarith
      calc ε' * (2 * (H (Y - 1) : ℝ)) ^ 2 * ((2 * (Y - 1) : ℕ) : ℝ)
          ≤ ε' * (4 * (HQ + 1) ^ 2) * (4 * Q) := by
            gcongr
      _ = 16 * ε' * (HQ + 1) ^ 2 * Q := by ring
    have hY1 : ((Y - 1 : ℕ) : ℝ) ≥ (Q : ℝ) - 1 := by
      have : Q - 1 ≤ Y - 1 := by omega
      have h' : ((Q - 1 : ℕ) : ℝ) ≤ ((Y - 1 : ℕ) : ℝ) := by exact_mod_cast this
      rw [Nat.cast_sub (by omega : 1 ≤ Q)] at h'
      push_cast at h'
      linarith
    have hδ : (HQ + 1) * (D + 1) / ((Y - 1 : ℕ) : ℝ) ≤ 2 * (HQ + 1) / m := by
      have hpos : (0 : ℝ) < ((Y - 1 : ℕ) : ℝ) := by
        have : 1 ≤ Y - 1 := by omega
        exact_mod_cast this
      rw [div_le_div_iff₀ hpos (by linarith), mul_assoc]
      have hmD' : (m : ℝ) * (D + 1) ≤ 2 * ((Y - 1 : ℕ) : ℝ) := by
        have : m * D + m ≤ 2 * (Y - 1) := by omega
        have h' : ((m * D + m : ℕ) : ℝ) ≤ ((2 * (Y - 1) : ℕ) : ℝ) := by exact_mod_cast this
        push_cast at h'
        linarith
      nlinarith
    calc _ ≤ 2 * (16 * ε' * (HQ + 1) ^ 2 * Q) +
          2 * D * (2 + (HQ + 1) * (D + 1) / ((Y - 1 : ℕ) : ℝ)) ^ 2 := by
          refine h1.trans (add_le_add (mul_le_mul_of_nonneg_left (h2.trans hfibb) (by norm_num))
            le_rfl)
      _ ≤ 32 * ε' * (HQ + 1) ^ 2 * Q + 2 * D * (2 + 2 * (HQ + 1) / m) ^ 2 := by
          have hq0 : 0 ≤ (HQ + 1) * (D + 1) / ((Y - 1 : ℕ) : ℝ) := by positivity
          have : (2 + (HQ + 1) * (D + 1) / ((Y - 1 : ℕ) : ℝ)) ^ 2 ≤
              (2 + 2 * (HQ + 1) / m) ^ 2 := pow_le_pow_left₀ (by linarith) (by linarith) 2
          have hD0 : (0 : ℝ) ≤ 2 * D := by positivity
          nlinarith
  -- the leftover starts
  have hleft : ∑ t ∈ Ico (Q + m * D) (2 * Q), (∑ n ∈ Ioc t (t + H Q), f n) ^ 2 ≤ m * HQ ^ 2 := by
    calc _ ≤ ∑ _t ∈ Ico (Q + m * D) (2 * Q), HQ ^ 2 := by
          refine sum_le_sum fun t _ => ?_
          have h := abs_sum_Ioc_le_card hf t (t + H Q)
          rw [Nat.add_sub_cancel_left] at h
          rw [← sq_abs]
          exact pow_le_pow_left₀ (abs_nonneg _) h 2
      _ = ((2 * Q - (Q + m * D) : ℕ) : ℝ) * HQ ^ 2 := by rw [sum_const, Nat.card_Ico, nsmul_eq_mul]
      _ ≤ m * HQ ^ 2 := by
          refine mul_le_mul_of_nonneg_right ?_ (sq_nonneg _)
          have : 2 * Q - (Q + m * D) ≤ m := by omega
          exact_mod_cast this
  rw [← sum_Ico_consecutive _ (by omega : Q ≤ Q + m * D) (by omega : Q + m * D ≤ 2 * Q),
    sum_Ico_eq_sum_range_blocks]
  have hsum := sum_le_sum fun j hj => hrange j (mem_range.mp hj)
  rw [sum_const, card_range, nsmul_eq_mul] at hsum
  have hmDR : (m : ℝ) * D ≤ Q := by exact_mod_cast hmD
  have hq : 0 ≤ (2 + 2 * (HQ + 1) / m) ^ 2 := sq_nonneg _
  calc _ ≤ (m : ℝ) * (32 * ε' * (HQ + 1) ^ 2 * Q + 2 * D * (2 + 2 * (HQ + 1) / m) ^ 2) +
        m * HQ ^ 2 := add_le_add hsum hleft
    _ ≤ _ := by nlinarith

/-- **Linear windows from fibres.** If the fibre mean square of a row bounded by one vanishes at the
lengths `h(x) = 2H(⌊√x⌋/2)`, with `H` monotone, unbounded and growing by at most one per doubling,
then `Σ_{Q ≤ t < 2Q} (Σ_{t < n ≤ t + H(Q)} f(n))² = o(H(Q)² Q)`. -/
theorem tendsto_sum_sq_window_div_of_averagedMeanSquare {f : ℕ → ℝ} (hf : ∀ n, |f n| ≤ 1)
    {H : ℕ → ℕ} (hHtop : Tendsto H atTop atTop) (hmono : Monotone H)
    (hslow : ∀ k, H (2 * k) ≤ H k + 1)
    (hms : AveragedMeanSquare f (fun x => 2 * (H (⌊Real.sqrt x⌋₊ / 2) : ℝ))) :
    Tendsto (fun Q : ℕ => (∑ t ∈ Ico Q (2 * Q), (∑ n ∈ Ioc t (t + H Q), f n) ^ 2) /
      ((H Q : ℝ) ^ 2 * Q)) atTop (𝓝 0) := by
  rw [tendsto_order]
  refine ⟨fun a ha => Eventually.of_forall fun Q => lt_of_lt_of_le ha (by positivity),
    fun ε hε => ?_⟩
  -- the number of ranges, the fibre threshold, and the scale beyond which it holds
  obtain ⟨m, hm2, hmε⟩ : ∃ m : ℕ, 2 ≤ m ∧ 512 / ε ≤ m :=
    ⟨⌈512 / ε⌉₊ + 2, by omega, by have := Nat.le_ceil (512 / ε); push_cast; linarith⟩
  have hmR : (2 : ℝ) ≤ m := by exact_mod_cast hm2
  set ε' : ℝ := ε / (1024 * m)
  have hε' : 0 < ε' := by positivity
  obtain ⟨X₀, hX₀⟩ := eventually_atTop.mp (hms.eventually (gt_mem_nhds hε'))
  have hHev : ∀ᶠ Q : ℕ in atTop, 128 / ε + 2 ≤ (H Q : ℝ) :=
    (tendsto_natCast_atTop_atTop.comp hHtop).eventually_ge_atTop _
  filter_upwards [hHev, eventually_ge_atTop (2 * m + 8), eventually_ge_atTop ⌈8 * m / ε⌉₊,
    eventually_ge_atTop ⌈X₀⌉₊] with Q hHQ hQ1 hQ2 hQ3
  set HQ : ℝ := (H Q : ℝ)
  have hHQ2 : 2 ≤ HQ := by have : 0 ≤ 128 / ε := by positivity
                           linarith
  have hQR : (2 * m + 8 : ℝ) ≤ Q := by exact_mod_cast hQ1
  have hQ0 : (0 : ℝ) < Q := by linarith
  -- the fibre bounds at the scales of the ranges
  have hfib : ∀ Y, Q ≤ Y → Y ≤ 2 * Q →
      ∑ a ∈ outerBlock (((2 * (Y - 1) : ℕ) : ℝ) ^ 2) (2 * (H (Y - 1) : ℝ)),
          (∑ b ∈ innerFibre (((2 * (Y - 1) : ℕ) : ℝ) ^ 2) (2 * (H (Y - 1) : ℝ)) a, f b) ^ 2 ≤
        ε' * (2 * (H (Y - 1) : ℝ)) ^ 2 * ((2 * (Y - 1) : ℕ) : ℝ) := by
    intro Y hYQ hY2
    set xY : ℝ := (((2 * (Y - 1) : ℕ) : ℝ)) ^ 2
    have hsx : Real.sqrt xY = ((2 * (Y - 1) : ℕ) : ℝ) := Real.sqrt_sq (Nat.cast_nonneg _)
    have hhh : 2 * (H (⌊Real.sqrt xY⌋₊ / 2) : ℝ) = 2 * (H (Y - 1) : ℝ) := by
      rw [hsx, Nat.floor_natCast, Nat.mul_div_cancel_left _ two_pos]
    have hHY : 1 ≤ H (Y - 1) := by
      have h1 := (hmono (by omega : Q ≤ 2 * (Q - 1))).trans (hslow (Q - 1))
      have h2 := hmono (by omega : Q - 1 ≤ Y - 1)
      have : 2 ≤ H Q := by exact_mod_cast (show (2 : ℝ) ≤ (H Q : ℝ) from hHQ2)
      omega
    have hX : X₀ ≤ xY := by
      have h1 : (X₀ : ℝ) ≤ Q := (Nat.le_ceil X₀).trans (by exact_mod_cast hQ3)
      have h2 : (Q : ℝ) ≤ ((2 * (Y - 1) : ℕ) : ℝ) := by
        have : Q ≤ 2 * (Y - 1) := by omega
        exact_mod_cast this
      have h3 : ((2 * (Y - 1) : ℕ) : ℝ) ≤ xY := by
        have : (1 : ℝ) ≤ ((2 * (Y - 1) : ℕ) : ℝ) := by
          have : 1 ≤ 2 * (Y - 1) := by omega
          exact_mod_cast this
        simp only [xY]; nlinarith
      linarith
    have hlt := hX₀ xY hX
    simp only at hlt
    rw [hhh, hsx] at hlt
    have hden : 0 < (2 * (H (Y - 1) : ℝ)) ^ 2 * ((2 * (Y - 1) : ℕ) : ℝ) := by
      have : (1 : ℝ) ≤ H (Y - 1) := by exact_mod_cast hHY
      have : (0 : ℝ) < ((2 * (Y - 1) : ℕ) : ℝ) := by
        have : 0 < 2 * (Y - 1) := by omega
        exact_mod_cast this
      positivity
    have := (div_lt_iff₀ hden).mp hlt
    nlinarith
  have hS := sum_window_sq_le_of_fibre_bounds hf hmono hslow hm2 hQ1 hε'.le hfib
  -- the three terms against `(ε/2) H² Q`
  have hpos : 0 < HQ ^ 2 * Q := by positivity
  have hQε : 8 * (m : ℝ) ≤ ε * Q := by
    have h := (Nat.le_ceil (8 * m / ε)).trans (by exact_mod_cast hQ2 : (⌈8 * m / ε⌉₊ : ℝ) ≤ Q)
    rw [div_le_iff₀ hε] at h
    linarith
  have hHε : 128 ≤ ε * HQ := by
    have h : 128 / ε ≤ HQ := by linarith
    rw [div_le_iff₀ hε] at h
    linarith
  have hmε' : 512 ≤ ε * m := by
    rw [div_le_iff₀ hε] at hmε
    linarith
  have t1 : 32 * ε' * m * (HQ + 1) ^ 2 * Q ≤ ε / 8 * (HQ ^ 2 * Q) := by
    have he : 32 * ε' * m = ε / 32 := by simp only [ε']; field_simp; ring
    have hsq : (HQ + 1) ^ 2 ≤ 4 * HQ ^ 2 := by nlinarith
    calc 32 * ε' * m * (HQ + 1) ^ 2 * Q = ε / 32 * ((HQ + 1) ^ 2 * Q) := by rw [he]; ring
      _ ≤ ε / 32 * (4 * HQ ^ 2 * Q) := by gcongr
      _ = ε / 8 * (HQ ^ 2 * Q) := by ring
  have t2 : 2 * Q * (2 + 2 * (HQ + 1) / m) ^ 2 ≤ ε / 4 * (HQ ^ 2 * Q) := by
    have hm0 : (0 : ℝ) < m := by linarith
    have hb : 2 * (HQ + 1) / m ≤ 4 * HQ / m := by
      rw [div_le_div_iff_of_pos_right hm0]; linarith
    have hsq : (2 + 2 * (HQ + 1) / m) ^ 2 ≤ 8 + 2 * (4 * HQ / m) ^ 2 := by
      have h0 : 0 ≤ 2 * (HQ + 1) / m := by positivity
      nlinarith [sq_nonneg (2 - 2 * (HQ + 1) / m)]
    have hA : 16 * (Q : ℝ) ≤ ε / 8 * (HQ ^ 2 * Q) := by
      have : 128 ≤ ε * HQ ^ 2 := by nlinarith
      nlinarith
    have hB : 4 * Q * (4 * HQ / m) ^ 2 ≤ ε / 8 * (HQ ^ 2 * Q) := by
      rw [div_pow, show 4 * (Q : ℝ) * ((4 * HQ) ^ 2 / (m : ℝ) ^ 2) =
        64 * (HQ ^ 2 * Q) / (m : ℝ) ^ 2 by ring, div_le_iff₀ (by positivity)]
      have : 512 ≤ ε * (m : ℝ) ^ 2 := by nlinarith
      nlinarith
    calc 2 * Q * (2 + 2 * (HQ + 1) / m) ^ 2 ≤ 2 * Q * (8 + 2 * (4 * HQ / m) ^ 2) := by gcongr
      _ = 16 * Q + 4 * Q * (4 * HQ / m) ^ 2 := by ring
      _ ≤ _ := by linarith
  have t3 : (m : ℝ) * HQ ^ 2 ≤ ε / 8 * (HQ ^ 2 * Q) := by nlinarith
  rw [div_lt_iff₀ hpos]
  have : 0 < ε * (HQ ^ 2 * Q) := by positivity
  linarith

/-- **Matomäki–Radziwiłł in linear windows.** For every length `H(Q) → ∞` that is monotone, at most
`Q`, and grows by at most one per doubling,
`Σ_{Q ≤ t < 2Q} (Σ_{t < n ≤ t + H(Q)} μ(n))² = o(H(Q)² Q)`. -/
theorem tendsto_sum_sq_moebius_window_div {H : ℕ → ℕ} (hHtop : Tendsto H atTop atTop)
    (hmono : Monotone H) (hslow : ∀ k, H (2 * k) ≤ H k + 1) (hle : ∀ k, H k ≤ k) :
    Tendsto (fun Q : ℕ => (∑ t ∈ Ico Q (2 * Q),
        (∑ n ∈ Ioc t (t + H Q), ((ArithmeticFunction.moebius n : ℤ) : ℝ)) ^ 2) /
      ((H Q : ℝ) ^ 2 * Q)) atTop (𝓝 0) := by
  have hf : ∀ n, |((ArithmeticFunction.moebius n : ℤ) : ℝ)| ≤ 1 := fun n => by
    exact_mod_cast ArithmeticFunction.abs_moebius_le_one
  have hk : Tendsto (fun x : ℝ => ⌊Real.sqrt x⌋₊ / 2) atTop atTop :=
    (Nat.tendsto_div_const_atTop two_ne_zero).comp (tendsto_nat_floor_atTop.comp
      Real.tendsto_sqrt_atTop)
  have hgrow : Tendsto (fun x : ℝ => 2 * (H (⌊Real.sqrt x⌋₊ / 2) : ℝ)) atTop atTop :=
    ((tendsto_natCast_atTop_atTop.comp (hHtop.comp hk))).const_mul_atTop two_pos
  have hsq : ∀ᶠ x : ℝ in atTop, 2 * (H (⌊Real.sqrt x⌋₊ / 2) : ℝ) ≤ Real.sqrt x := by
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with x hx
    have h1 : 2 * (⌊Real.sqrt x⌋₊ / 2) ≤ ⌊Real.sqrt x⌋₊ := Nat.mul_div_le _ _
    have h2 : 2 * H (⌊Real.sqrt x⌋₊ / 2) ≤ ⌊Real.sqrt x⌋₊ :=
      (Nat.mul_le_mul_left 2 (hle _)).trans h1
    have h3 : ((⌊Real.sqrt x⌋₊ : ℕ) : ℝ) ≤ Real.sqrt x := Nat.floor_le (Real.sqrt_nonneg x)
    have h4 : ((2 * H (⌊Real.sqrt x⌋₊ / 2) : ℕ) : ℝ) ≤ ((⌊Real.sqrt x⌋₊ : ℕ) : ℝ) := by
      exact_mod_cast h2
    push_cast at h4
    linarith
  exact tendsto_sum_sq_window_div_of_averagedMeanSquare hf hHtop hmono hslow
    (averagedMeanSquare_moebius_of_tendsto hgrow hsq)

end

end GaloisForLFunctions.BezoutValuationIncidence
