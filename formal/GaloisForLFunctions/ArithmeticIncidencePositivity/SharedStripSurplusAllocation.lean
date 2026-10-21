import GaloisForLFunctions.ArithmeticIncidencePositivity.NestedStripShellMicroFold

/-!
# Shared strip surplus: nested prime strips paid by one copy of the surplus

For an odd test `F` supported in `[−r, r]` and every `n ≥ 2` with `½ log n < r ≤ ½ log n + 1/12`, the
sharp micro-fold pays the atom of `n` from the surplus `T(S_n)` of its own strip `S_n = [log n − r, r]`
(`two_mul_primePowerShift_le_stripSurplus_sub_evenPart`). All strips end at `r`, so they are nested,
and summing these inequalities counts the pairs of the innermost strip once per atom. This file
allocates the one surplus `T(S_{n₀})` of the outermost strip so that no pair is counted twice.

* **Union allocation** (`sum_primeStripCharge_le_union`). Weights `θ_n ≥ 0` with `Σ θ_n ≤ 1` and
  `(1 + t_n) 2Λ(n)/√n ≤ θ_n λ₀(n)`: every strip draws the fraction `θ_n` of its own box, and the boxes
  are nested (`stripBoxEnergy_mono`).
* **Telescoping chain** (`sum_primeStripCharge_le_chain`). For `n₀ < n₁ < … < n_k` with each inner strip
  right of the centre of the previous one, strip `j` pays from the shell
  `T(S_{n_j}) − T(S_{n_{j+1}})` (`sharpMicroFold_shell_ge`) and the last from its box. The shells are
  disjoint and telescope to `T(S_{n₀})`; each atom keeps the shell constant
  `λ₀ − (r − p')((2 + η/2)/c + 1)` (`shellFoldConstant`), close to `λ₀` when the next strip is much
  thinner. Strips of very different widths therefore share nothing.
* **The atoms of `23` and `25` share one strip** (`primeStripCharge_twentyThree_twentyFive_le`). For
  `½ log 25 < r ≤ ½ log 25 + 1/250` both strips are thin, but `2Λ(23)/√23 + 2Λ(25)/5 > 1.95 > λ₀`, so no
  union allocation with the sharp micro-fold constant exists. The shell does it: `λ_sh ≥ 1.40` pays
  the atom of `23`, and `7/10` of the box of `25` pays twice the atom of `25`, whose even part then
  leaves the potential `16/25` on `S_25`.

The summand `primeStripCharge F r n t` is the atom term plus the potential `2 (Λ(n)/√n) t ∫_{S_n} F²`
that its even part leaves on the strip.
-/

open MeasureTheory Set Filter Topology
open RHTower RHTower.CHMDPolar RHTower.WeilLevyPoleGauss GaloisForLFunctions.ArithmeticCriticalityTheory

noncomputable section

namespace GaloisForLFunctions.ArithmeticIncidencePositivity

/-- The strip of `n` is thin at radius `r`: `½ log n < r ≤ ½ log n + 1/12`. -/
def ThinStrip (n : ℕ) (r : ℝ) : Prop := Real.log n / 2 < r ∧ r ≤ Real.log n / 2 + 1 / 12

/-- The sharp micro-fold constant `λ₀ = 1.9 − η/p − 3η²` of the strip of `n` at radius `r`,
`p = log n − r`, `η = r − ½ log n`. -/
def stripFoldConstant (n : ℕ) (r : ℝ) : ℝ :=
  19 / 10 - (r - (Real.log n - r)) / 2 / (Real.log n - r) - 3 * ((r - (Real.log n - r)) / 2) ^ 2

/-- The shell constant of the strip of `n` around the inner strip of `n'`:
`λ₀ − (r − p')((2 + η/2)/c + 1)`, `p' = log n' − r`, `c = p' − ½ log n`. -/
def shellFoldConstant (n n' : ℕ) (r : ℝ) : ℝ :=
  stripFoldConstant n r - (r - (Real.log n' - r)) *
    ((2 + (r - (Real.log n - r)) / 2 / 2) / (Real.log n' - r - Real.log n / 2) + 1)

/-- The atom of `n` with the potential its even part leaves on the strip:
`2 Λ(n)/√n ∫ F F(· + log n) + 2 (Λ(n)/√n) t ∫_{S_n} F²`. -/
def primeStripCharge (F : ℝ → ℝ) (r : ℝ) (n : ℕ) (t : ℝ) : ℝ :=
  2 * (vonMangoldtAtom n * ∫ x, F x * F (x + Real.log n)) +
    2 * vonMangoldtAtom n * t * ∫ x in (Real.log n - r)..r, F x ^ 2

theorem stripBoxEnergy_nonneg (F : ℝ → ℝ) {p r : ℝ} (hp : 0 < p) (hpr : p ≤ r) :
    0 ≤ stripBoxEnergy F p r :=
  intervalIntegral.integral_nonneg hpr fun _ hx => intervalIntegral.integral_nonneg hpr fun _ hy =>
    stripIntegrand_nonneg F (hp.trans_le hx.1) (hp.trans_le hy.1)

/-- A thin strip of `n ≥ 2` starts at `p = log n − r ≥ 0.263` and has width `r − p ≤ 1/6`. -/
theorem thinStrip_bounds {n : ℕ} {r : ℝ} (hn : 2 ≤ n) (h : ThinStrip n r) :
    26324 / 100000 ≤ Real.log n - r ∧ Real.log n - r < r ∧ r - (Real.log n - r) ≤ 1 / 6 := by
  have hl2 := Real.log_two_gt_d9
  have hn2 : Real.log 2 ≤ Real.log n := Real.log_le_log (by norm_num) (by exact_mod_cast hn)
  obtain ⟨hr, hr'⟩ := h
  refine ⟨by linarith, by linarith, by linarith⟩

section Allocation

variable {F : ℝ → ℝ} {K r : ℝ} (hF : Continuous F) (hFc : HasCompactSupport F)
  (hodd : ∀ x, F (-x) = -F x) (hFL : ∀ a b, |F a - F b| ≤ K * |a - b|)
  (hsupp : ∀ x, r < |x| → F x = 0)

include hF hFc hodd hFL hsupp in
/-- **Harnack across a prime-power shift, in box form.** For a thin strip of `n ≥ 2`, `θ ≥ 0`,
`t ≤ 1` and `(1 + t) 2Λ(n)/√n ≤ θ λ₀`: `primeStripCharge ≤ θ T(S_n)`. -/
theorem primeStripCharge_le_box {n : ℕ} {θ t : ℝ} (hn : 2 ≤ n) (hthin : ThinStrip n r)
    (hθ0 : 0 ≤ θ) (ht1 : t ≤ 1)
    (hθ : (1 + t) * (2 * vonMangoldtAtom n) ≤ θ * stripFoldConstant n r) :
    primeStripCharge F r n t ≤ θ * stripBoxEnergy F (Real.log n - r) r := by
  obtain ⟨hp, hpr, hr6⟩ := thinStrip_bounds hn hthin
  have h := two_mul_primePowerShift_le_stripSurplus_sub_evenPart hn hF hFc hodd hFL hsupp hthin.1
    hthin.2 hθ0 ht1 hθ
  have hT := integral_strip_eq_two_mul_stripSurplus hF hFL (by linarith : 0 < Real.log n - r)
    hpr.le (by linarith)
  unfold primeStripCharge stripBoxEnergy
  rw [hT]
  linarith

include hF hFc hodd hFL hsupp in
/-- **Harnack across a prime-power shift, paid by a shell.** For a thin strip of `n ≥ 2` and an inner
strip `[log n' − r, r]` starting right of `½ log n`, `θ ≥ 0`, `t ≤ 1` and
`(1 + t) 2Λ(n)/√n ≤ θ λ_sh(n, n')`: `primeStripCharge ≤ θ (T(S_n) − T(S_{n'}))`. -/
theorem primeStripCharge_le_shell {n n' : ℕ} {θ t : ℝ} (hn : 2 ≤ n) (hthin : ThinStrip n r)
    (hc : Real.log n / 2 < Real.log n' - r) (hn'r : Real.log n' - r ≤ r) (hθ0 : 0 ≤ θ)
    (ht1 : t ≤ 1) (hθ : (1 + t) * (2 * vonMangoldtAtom n) ≤ θ * shellFoldConstant n n' r) :
    primeStripCharge F r n t ≤
      θ * (stripBoxEnergy F (Real.log n - r) r - stripBoxEnergy F (Real.log n' - r) r) := by
  obtain ⟨hp, hpr, hr6⟩ := thinStrip_bounds hn hthin
  unfold shellFoldConstant stripFoldConstant at hθ
  set L := Real.log n with hLdef
  set p := L - r with hpdef
  have hL : p + r = L := by rw [hpdef]; ring
  have hr3 : r - p ≤ 2 * p := by linarith
  have hms := sharpMicroFold_shell_ge (p' := Real.log n' - r) hF hFL (by linarith) hpr hL hr3 hr6
    hc hn'r
  have hshift := integral_mul_shift_le_interp hF hFc hodd (r := r) (L := L) (by linarith)
    (by rw [← hpdef]; exact hpr.le) hsupp ht1
  rw [← hpdef] at hshift
  have hw0 := vonMangoldtAtom_nonneg n
  have hα0 : 0 ≤ ∫ x in p..r, reflectedOddPart F L x ^ 2 :=
    intervalIntegral.integral_nonneg hpr.le fun _ _ => sq_nonneg _
  have k1 := mul_le_mul_of_nonneg_left hshift hw0
  have k2 := mul_le_mul_of_nonneg_right hθ hα0
  have k4 := mul_le_mul_of_nonneg_left hms hθ0
  unfold primeStripCharge
  linarith only [k1, k2, k4]

include hF hFc hodd hFL hsupp in
/-- **Union allocation.** Let every `n` of a finite family have a thin strip inside `[p₀, r]`,
`0 < p₀`, `r − p₀ ≤ 1`, and weights `θ_n ≥ 0`, `t_n ≤ 1`, `(1 + t_n) 2Λ(n)/√n ≤ θ_n λ₀(n)`. If
`Σ θ_n ≤ 1`, the atoms are paid by one copy of the surplus of `[p₀, r]`:
`Σ primeStripCharge ≤ T(p₀, r)`. -/
theorem sum_primeStripCharge_le_union (s : Finset ℕ) {p₀ : ℝ} (hp₀ : 0 < p₀) (hp₀r : p₀ ≤ r)
    (hr1 : r - p₀ ≤ 1) (θ t : ℕ → ℝ)
    (hs : ∀ n ∈ s, 2 ≤ n ∧ ThinStrip n r ∧ p₀ ≤ Real.log n - r ∧ 0 ≤ θ n ∧ t n ≤ 1 ∧
      (1 + t n) * (2 * vonMangoldtAtom n) ≤ θ n * stripFoldConstant n r)
    (hθ : ∑ n ∈ s, θ n ≤ 1) :
    ∑ n ∈ s, primeStripCharge F r n (t n) ≤ stripBoxEnergy F p₀ r := by
  have hT0 := stripBoxEnergy_nonneg F hp₀ hp₀r
  calc ∑ n ∈ s, primeStripCharge F r n (t n) ≤ ∑ n ∈ s, θ n * stripBoxEnergy F p₀ r := by
        refine Finset.sum_le_sum fun n hn => ?_
        obtain ⟨h2, hthin, hp, hθ0, ht1, hθn⟩ := hs n hn
        obtain ⟨-, hpr, -⟩ := thinStrip_bounds h2 hthin
        have h := primeStripCharge_le_box hF hFc hodd hFL hsupp h2 hthin hθ0 ht1 hθn
        have hmono := stripBoxEnergy_mono hF hFL (F := F) hp₀ hp hpr.le hr1
        exact h.trans (mul_le_mul_of_nonneg_left hmono hθ0)
    _ = (∑ n ∈ s, θ n) * stripBoxEnergy F p₀ r := (Finset.sum_mul _ _ _).symm
    _ ≤ 1 * stripBoxEnergy F p₀ r := mul_le_mul_of_nonneg_right hθ hT0
    _ = stripBoxEnergy F p₀ r := one_mul _

include hF hFc hodd hFL hsupp in
/-- **Telescoping chain allocation.** Let `n 0, …, n k` have thin strips, `0 ≤ θ_j ≤ 1`, `t_j ≤ 1`,
each strip `j < k` with the next strip starting right of `½ log n_j` and
`(1 + t_j) 2Λ(n_j)/√n_j ≤ θ_j λ_sh(n_j, n_{j+1})`, and the last with
`(1 + t_k) 2Λ(n_k)/√n_k ≤ θ_k λ₀(n_k)`. Then all the atoms are paid by one copy of the surplus of the
outermost strip: `Σ_j primeStripCharge ≤ T(S_{n 0})`. Strip `j` draws only on the shell
`S_{n_j}² \ S_{n_{j+1}}²`; the shells are disjoint. -/
theorem sum_primeStripCharge_le_chain :
    ∀ (k : ℕ) (n : ℕ → ℕ) (θ t : ℕ → ℝ),
      (∀ j ≤ k, 2 ≤ n j ∧ ThinStrip (n j) r ∧ 0 ≤ θ j ∧ θ j ≤ 1 ∧ t j ≤ 1) →
      (∀ j < k, Real.log (n j) / 2 < Real.log (n (j + 1)) - r ∧
        (1 + t j) * (2 * vonMangoldtAtom (n j)) ≤ θ j * shellFoldConstant (n j) (n (j + 1)) r) →
      (1 + t k) * (2 * vonMangoldtAtom (n k)) ≤ θ k * stripFoldConstant (n k) r →
      ∑ j ∈ Finset.range (k + 1), primeStripCharge F r (n j) (t j) ≤
        stripBoxEnergy F (Real.log (n 0) - r) r := by
  intro k
  induction k with
  | zero =>
    intro n θ t hthin _ hlast
    obtain ⟨hn, hth, hθ0, hθ1, ht1⟩ := hthin 0 le_rfl
    obtain ⟨hp, hpr, -⟩ := thinStrip_bounds hn hth
    rw [Finset.sum_range_one]
    have h := primeStripCharge_le_box hF hFc hodd hFL hsupp hn hth hθ0 ht1 hlast
    have hT0 := stripBoxEnergy_nonneg F (by linarith : 0 < Real.log (n 0) - r) hpr.le
    nlinarith
  | succ k ih =>
    intro n θ t hthin hshell hlast
    rw [Finset.sum_range_succ']
    have htail := ih (fun j => n (j + 1)) (fun j => θ (j + 1)) (fun j => t (j + 1))
      (fun j hj => hthin (j + 1) (by omega)) (fun j hj => hshell (j + 1) (by omega)) hlast
    obtain ⟨hn, hth, hθ0, hθ1, ht1⟩ := hthin 0 (by omega)
    obtain ⟨hc, hθs⟩ := hshell 0 (by omega)
    obtain ⟨-, hth1, -⟩ := hthin 1 (by omega)
    obtain ⟨hp, hpr, hr6⟩ := thinStrip_bounds hn hth
    have hn'r : Real.log (n 1) - r ≤ r := by linarith [hth1.1]
    have h := primeStripCharge_le_shell hF hFc hodd hFL hsupp hn hth hc hn'r hθ0 ht1 hθs
    have hmono := stripBoxEnergy_mono hF hFL (F := F) (by linarith : 0 < Real.log (n 0) - r)
      (by linarith [hth.1] : Real.log (n 0) - r ≤ Real.log (n (0 + 1)) - r) hn'r (by linarith)
    have hsh : θ 0 * (stripBoxEnergy F (Real.log (n 0) - r) r -
        stripBoxEnergy F (Real.log (n 1) - r) r) ≤
        stripBoxEnergy F (Real.log (n 0) - r) r - stripBoxEnergy F (Real.log (n 1) - r) r := by
      have h0 : 0 ≤ stripBoxEnergy F (Real.log (n 0) - r) r -
          stripBoxEnergy F (Real.log (n 1) - r) r := by linarith
      nlinarith
    linarith

end Allocation

/-! ### The atoms of `23` and `25` share one strip -/

/-- `3.1345 < log 23 < 3.1364`: `log 24 = 3 log 2 + log 3` and `−1/23 ≤ log(23/24) ≤ −1/24`. -/
theorem log_twentyThree_bounds : 31345 / 10000 < Real.log 23 ∧ Real.log 23 < 31364 / 10000 := by
  have l2 := Real.log_two_gt_d9
  have l2' := Real.log_two_lt_d9
  have l3 := log_three_bounds
  have e : Real.log 23 = 3 * Real.log 2 + Real.log 3 + Real.log (23 / 24) := by
    rw [Real.log_div (by norm_num) (by norm_num), show (24 : ℝ) = 2 ^ 3 * 3 by norm_num,
      Real.log_mul (by norm_num) (by norm_num), Real.log_pow]
    push_cast; ring
  have h1 := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 23 / 24 by norm_num)
  have h2 := Real.one_sub_inv_le_log_of_pos (show (0 : ℝ) < 23 / 24 by norm_num)
  rw [show (1 : ℝ) - (23 / 24)⁻¹ = -(1 / 23) by norm_num] at h2
  rw [e]
  constructor <;> linarith

/-- `Λ(23)/√23 = log 23/√23 ≤ 0.654`. -/
theorem vonMangoldtAtom_twentyThree_le : vonMangoldtAtom 23 ≤ 654 / 1000 := by
  unfold vonMangoldtAtom
  rw [if_pos (by norm_num), ArithmeticFunction.vonMangoldt_apply_prime (by norm_num : Nat.Prime 23)]
  have hs : (47958 / 10000 : ℝ) ≤ Real.sqrt ((23 : ℕ) : ℝ) := by
    rw [Real.le_sqrt (by norm_num) (by norm_num)]; norm_num
  have hl := log_twentyThree_bounds.2
  push_cast at hs ⊢
  rw [div_le_iff₀ (by linarith)]
  nlinarith

/-- `Λ(25)/√25 = log 5 / 5`. -/
theorem vonMangoldtAtom_twentyFive : vonMangoldtAtom 25 = Real.log 5 / 5 := by
  unfold vonMangoldtAtom
  rw [if_pos (by norm_num), show (25 : ℕ) = 5 ^ 2 by norm_num,
    ArithmeticFunction.vonMangoldt_apply_pow (by norm_num),
    ArithmeticFunction.vonMangoldt_apply_prime (by norm_num : Nat.Prime 5)]
  have hs : Real.sqrt (((5 ^ 2 : ℕ) : ℝ)) = 5 := by
    rw [show (((5 ^ 2 : ℕ) : ℝ)) = (5 : ℝ) ^ 2 by push_cast; ring]
    exact Real.sqrt_sq (by norm_num)
  rw [hs]
  push_cast
  ring

/-- **The shell constant of `23` around `25`.** For `½ log 25 < r ≤ ½ log 25 + 1/250`:
`λ_sh(23, 25) ≥ 1.4 ≥ 2Λ(23)/√23`. The strip of `23` has `η ≤ 0.0462`, `p ≥ 1.521`, and the strip of
`25` starts `c ≥ 0.0372` right of `½ log 23` with width `r − p' ≤ 0.008`. -/
theorem shellFoldConstant_twentyThree_twentyFive {r : ℝ} (hr : Real.log 25 / 2 < r)
    (hr' : r ≤ Real.log 25 / 2 + 1 / 250) : 7 / 5 ≤ shellFoldConstant 23 25 r := by
  obtain ⟨a1, a2⟩ := log_twentyThree_bounds
  obtain ⟨f1, f2⟩ := log_five_bounds
  have e25 : Real.log 25 = 2 * Real.log 5 := by
    rw [show (25 : ℝ) = 5 ^ 2 by norm_num, Real.log_pow]; norm_num
  unfold shellFoldConstant stripFoldConstant
  push_cast
  rw [e25] at hr hr' ⊢
  set a := Real.log 23 with ha
  set b := Real.log 5 with hb
  -- the strip of `23`
  have hp : 1521 / 1000 ≤ a - r := by linarith
  have hη0 : 0 ≤ (r - (a - r)) / 2 := by linarith
  have hη : (r - (a - r)) / 2 ≤ 462 / 10000 := by linarith
  have hηp : (r - (a - r)) / 2 / (a - r) ≤ 304 / 10000 := by
    rw [div_le_iff₀ (by linarith)]; linarith
  have hη2 : 3 * ((r - (a - r)) / 2) ^ 2 ≤ 65 / 10000 := by nlinarith
  -- the inner strip of `25`
  have hc : 372 / 10000 ≤ 2 * b - r - a / 2 := by linarith
  have hd0 : 0 ≤ r - (2 * b - r) := by linarith
  have hd : r - (2 * b - r) ≤ 8 / 1000 := by linarith
  have hq : (2 + (r - (a - r)) / 2 / 2) / (2 * b - r - a / 2) ≤ 544 / 10 := by
    rw [div_le_iff₀ (by linarith)]; linarith
  have hloss : (r - (2 * b - r)) * ((2 + (r - (a - r)) / 2 / 2) / (2 * b - r - a / 2) + 1) ≤
      8 / 1000 * (544 / 10 + 1) :=
    mul_le_mul hd (by linarith) (by positivity) (by norm_num)
  linarith

section TwentyThreeTwentyFive

variable {F : ℝ → ℝ} {K r : ℝ} (hF : Continuous F) (hFc : HasCompactSupport F)
  (hodd : ∀ x, F (-x) = -F x) (hFL : ∀ a b, |F a - F b| ≤ K * |a - b|)
  (hsupp : ∀ x, r < |x| → F x = 0)

include hF hFc hodd hFL hsupp in
/-- **The atoms of `23` and `25` share one strip.** For every odd `F` supported in `[−r, r]`,
`½ log 25 < r ≤ ½ log 25 + 1/250`:
`2Λ(23)/√23 ∫ F F(· + log 23) + 2Λ(25)/5 ∫ F F(· + log 25) + (16/25) ∫_{log 25 − r}^{r} F²
≤ 2 stripSurplus F (log 23 − r) r`. Both strips are thin, but `2Λ(23)/√23 + 2Λ(25)/5 > 1.95` exceeds
the sharp micro-fold constant, so the boxes cannot be shared by weights; the shell
`S_23² \ S_25²` pays the atom of `23`, and `7/10` of the box of `25` pays twice the atom of `25`. -/
theorem primeStripCharge_twentyThree_twentyFive_le (hr : Real.log 25 / 2 < r)
    (hr' : r ≤ Real.log 25 / 2 + 1 / 250) :
    2 * (vonMangoldtAtom 23 * ∫ x, F x * F (x + Real.log 23)) +
        2 * (vonMangoldtAtom 25 * ∫ x, F x * F (x + Real.log 25)) +
          16 / 25 * ∫ x in (Real.log 25 - r)..r, F x ^ 2 ≤
      2 * stripSurplus F (Real.log 23 - r) r := by
  obtain ⟨a1, a2⟩ := log_twentyThree_bounds
  obtain ⟨f1, f2⟩ := log_five_bounds
  have e25 : Real.log 25 = 2 * Real.log 5 := by
    rw [show (25 : ℝ) = 5 ^ 2 by norm_num, Real.log_pow]; norm_num
  have c23 : ((23 : ℕ) : ℝ) = 23 := by norm_num
  have c25 : ((25 : ℕ) : ℝ) = 25 := by norm_num
  have hth23 : ThinStrip 23 r := by
    unfold ThinStrip; rw [c23]; constructor <;> linarith
  have hth25 : ThinStrip 25 r := by
    unfold ThinStrip; rw [c25]; constructor <;> linarith
  -- the atom of `23` from the shell around the strip of `25`
  have hΛ23 := vonMangoldtAtom_twentyThree_le
  have hsh := shellFoldConstant_twentyThree_twentyFive hr hr'
  have h23 := primeStripCharge_le_shell hF hFc hodd hFL hsupp (n := 23) (n' := 25) (θ := 1) (t := 0)
    (by norm_num) hth23 (by rw [c23, c25]; linarith) (by rw [c25]; linarith) zero_le_one
    zero_le_one (by linarith)
  -- twice the atom of `25` from `7/10` of its box
  have hΛ25 := vonMangoldtAtom_twentyFive
  have hlam25 : (1 + 1) * (2 * vonMangoldtAtom 25) ≤ 7 / 10 * stripFoldConstant 25 r := by
    unfold stripFoldConstant
    rw [hΛ25, c25]
    rw [e25] at hr hr' ⊢
    have hp : 16 / 10 ≤ 2 * Real.log 5 - r := by linarith
    have hη0 : 0 ≤ (r - (2 * Real.log 5 - r)) / 2 := by linarith
    have hη : (r - (2 * Real.log 5 - r)) / 2 ≤ 1 / 250 := by linarith
    have hηp : (r - (2 * Real.log 5 - r)) / 2 / (2 * Real.log 5 - r) ≤ 1 / 400 := by
      rw [div_le_iff₀ (by linarith)]; linarith
    have hη2 : 3 * ((r - (2 * Real.log 5 - r)) / 2) ^ 2 ≤ 1 / 10000 := by nlinarith
    linarith
  have h25 := primeStripCharge_le_box hF hFc hodd hFL hsupp (n := 25) (θ := 7 / 10) (t := 1)
    (by norm_num) hth25 (by norm_num) le_rfl hlam25
  -- the two boxes are nested
  obtain ⟨hp23, hpr23, -⟩ := thinStrip_bounds (by norm_num) hth23
  obtain ⟨hp25, hpr25, -⟩ := thinStrip_bounds (by norm_num) hth25
  rw [c23] at hp23 hpr23
  rw [c25] at hp25 hpr25
  have hT25 := stripBoxEnergy_nonneg F (by linarith : 0 < Real.log 25 - r) hpr25.le
  have hT := integral_strip_eq_two_mul_stripSurplus hF hFL (by linarith : 0 < Real.log 23 - r)
    hpr23.le (by linarith)
  have hS : 0 ≤ ∫ x in (Real.log 25 - r)..r, F x ^ 2 :=
    intervalIntegral.integral_nonneg hpr25.le fun _ _ => sq_nonneg _
  have hgain : 16 / 25 * ∫ x in (Real.log 25 - r)..r, F x ^ 2 ≤
      2 * vonMangoldtAtom 25 * 1 * ∫ x in (Real.log 25 - r)..r, F x ^ 2 := by
    refine mul_le_mul_of_nonneg_right ?_ hS
    rw [hΛ25]; linarith
  unfold primeStripCharge at h23 h25
  rw [c23, c25] at h23
  rw [c25] at h25
  unfold stripBoxEnergy at h23 h25 hT25
  rw [← hT]
  linarith

end TwentyThreeTwentyFive

end GaloisForLFunctions.ArithmeticIncidencePositivity

end
