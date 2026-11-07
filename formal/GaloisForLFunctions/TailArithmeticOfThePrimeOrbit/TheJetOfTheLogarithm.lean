import GaloisForLFunctions.PrimeTorusTheory.IteratedDifferencesOfTheLogarithm

/-!
# The jet of the logarithm moves

On a block `x + h a`, `0 ≤ a < M`, the phase `t log(x + h a)/2π` is a polynomial phase of degree `k ≈ log t/log x` up to a
small error; its binomial coefficients are `β_j = t Δ_h^j log(x)/2π`. A *single* polynomial phase of degree `k` can save
as little as `2/(k+1)` (`TheFloorOfAPolynomialPhase`): `C(a, 2^m − 1)/2` sits on the binomial denominators. Why is
`t log n` not such a phase?

* **The jet is a function of one variable** (`fwdDiff_iter_log_dilate`). `Δ_h^j log(x) = Δ_1^j log(x/h)` for `j ≥ 1`:
  multiplication by `h` adds `log h`, which every difference kills. So the `k` coefficients of every block are the values
  of one curve `u ↦ (t Δ_1^j log u/2π)_j` at `u = x/h`; a generic polynomial phase has `k` free coefficients.
* **The jet moves at every step** (`logDiffMass_sub_succ`). `|Δ^{j+1} log x| − |Δ^{j+1} log(x+1)| = |Δ^{j+2} log x|`,
  which is at least `(j+1)!/(x+j+2)^{j+2}`. The coefficient strictly decreases along consecutive blocks, by a definite
  amount: it cannot stay on a denominator.
* **Exotic blocks are isolated** (`card_exotic_le`). On `[X, X + H]` the positions at which the coefficient
  `B_j(x) = t|Δ^{j+1} log x|/2π` is within `η` of `c + ℤ` number at most
  `(t j!/(2πX^{j+1}) + 2)(2η · 2π(X+H+j+2)^{j+2}/(t (j+1)!) + 1)`. When the coefficient is of size `1` and
  `H ≍ X/j`, this is `O(η H + 1)`: the binomial-denominator obstruction occupies a proportion `O(η)` of the blocks.

So the ceiling `2/(k+1)` is a ceiling for one block, not for a family of blocks. What a saving past Vinogradov's degree has
to use is exactly this: the coefficient vector moves along a fixed curve, monotonically, as the block moves. The general
counting statement (`card_near_lattice_le`) holds for every sequence decreasing by at least `μ` per step.
-/

open Finset Real
open scoped fwdDiff

namespace GaloisForLFunctions.TailArithmeticOfThePrimeOrbit

noncomputable section

/-! ## Sequences that move meet a lattice rarely -/

/-- A sequence decreasing by at least `μ` per step drops by `μ` times the distance. -/
theorem le_sub_of_step {f : ℕ → ℝ} {a b : ℕ} {μ : ℝ} (hstep : ∀ n, a ≤ n → n < b → μ ≤ f n - f (n + 1)) :
    ∀ d n, a ≤ n → n + d ≤ b → μ * d ≤ f n - f (n + d) := by
  intro d
  induction d with
  | zero => intro n _ _; simp
  | succ d ih =>
    intro n hn hnd
    have h1 := ih n hn (by omega)
    have h2 := hstep (n + d) (by omega) (by omega)
    push_cast
    rw [show n + (d + 1) = n + d + 1 by omega]
    linarith

/-- **A moving sequence meets a lattice rarely.** If `f` decreases by at least `μ > 0` per step on `[a, b]`, then the
`n ∈ [a, b]` with `f n` within `η` of `c + ℤ` number at most `(f a − f b + 2)(2η/μ + 1)`. -/
theorem card_near_lattice_le {f : ℕ → ℝ} {a b : ℕ} (hab : a ≤ b) {μ η : ℝ} (hμ : 0 < μ) (hη : 0 ≤ η)
    (hstep : ∀ n, a ≤ n → n < b → μ ≤ f n - f (n + 1)) (c : ℝ) :
    (((Icc a b).filter fun n => ∃ m : ℤ, |f n - c - m| ≤ η).card : ℝ) ≤ (f a - f b + 2) * (2 * η / μ + 1) := by
  classical
  set S := (Icc a b).filter fun n => ∃ m : ℤ, |f n - c - m| ≤ η with hS
  set g : ℕ → ℤ := fun n => ⌈f n - c - η⌉ with hg
  have hmono : ∀ n n', a ≤ n → n ≤ n' → n' ≤ b → f n' ≤ f n := fun n n' hn hnn' hn' => by
    have := le_sub_of_step hstep (n' - n) n hn (by omega)
    rw [show n + (n' - n) = n' by omega] at this
    have h0 : 0 ≤ μ * ((n' - n : ℕ) : ℝ) := by positivity
    linarith
  -- `g n` is a witness of nearness.
  have hgw : ∀ n ∈ S, |f n - c - g n| ≤ η := by
    intro n hn
    obtain ⟨m, hm⟩ := (Finset.mem_filter.mp hn).2
    have h1 : f n - c - η ≤ (g n : ℝ) := Int.le_ceil _
    have h2 : g n ≤ m := Int.ceil_le.mpr (by linarith [(abs_le.mp hm).2])
    have h3 : (g n : ℝ) ≤ m := by exact_mod_cast h2
    rw [abs_le]
    constructor <;> linarith [(abs_le.mp hm).1]
  -- Each fiber is an interval of length at most `2η/μ`.
  set F : ℕ := ⌊2 * η / μ⌋₊ + 1 with hF
  have hfiber : ∀ m ∈ S.image g, (S.filter fun n => g n = m).card ≤ F := by
    intro m _
    set Sm := S.filter fun n => g n = m
    rcases Sm.eq_empty_or_nonempty with h | hne
    · rw [h, Finset.card_empty]; exact Nat.zero_le _
    set n₀ := Sm.min' hne
    have hn₀ : n₀ ∈ Sm := Finset.min'_mem _ _
    have hsub : Sm ⊆ Icc n₀ (n₀ + ⌊2 * η / μ⌋₊) := by
      intro n hn
      have hle : n₀ ≤ n := Finset.min'_le _ _ hn
      refine Finset.mem_Icc.mpr ⟨hle, ?_⟩
      obtain ⟨hnS, hgn⟩ := Finset.mem_filter.mp hn
      obtain ⟨hn₀S, hgn₀⟩ := Finset.mem_filter.mp hn₀
      have hn₀ab := Finset.mem_Icc.mp (Finset.mem_filter.mp hn₀S).1
      have hnab := Finset.mem_Icc.mp (Finset.mem_filter.mp hnS).1
      have hdrop := le_sub_of_step hstep (n - n₀) n₀ hn₀ab.1 (by omega)
      rw [show n₀ + (n - n₀) = n by omega] at hdrop
      have hw1 := hgw n hnS
      have hw2 := hgw n₀ hn₀S
      rw [hgn] at hw1
      rw [hgn₀] at hw2
      have hclose : f n₀ - f n ≤ 2 * η := by
        linarith [(abs_le.mp hw1).1, (abs_le.mp hw2).2]
      have hd : ((n - n₀ : ℕ) : ℝ) ≤ 2 * η / μ := by
        rw [le_div_iff₀ hμ]
        linarith
      have := Nat.le_floor hd
      omega
    calc Sm.card ≤ (Icc n₀ (n₀ + ⌊2 * η / μ⌋₊)).card := Finset.card_le_card hsub
      _ = F := by rw [Nat.card_Icc]; omega
  -- The image lies in an interval of integers.
  have himage : S.image g ⊆ Finset.Icc (g b) (g a) := by
    intro m hm
    obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp hm
    have hnab := Finset.mem_Icc.mp (Finset.mem_filter.mp hn).1
    refine Finset.mem_Icc.mpr ⟨Int.ceil_mono ?_, Int.ceil_mono ?_⟩
    · linarith [hmono n b hnab.1 hnab.2 le_rfl]
    · linarith [hmono a n le_rfl hnab.1 hnab.2]
  have hcard_img : ((S.image g).card : ℝ) ≤ f a - f b + 2 := by
    have h1 := Finset.card_le_card himage
    rw [Int.card_Icc] at h1
    have h2 : ((Int.toNat (g a + 1 - g b) : ℕ) : ℝ) ≤ f a - f b + 2 := by
      have hga : (g a : ℝ) < f a - c - η + 1 := Int.ceil_lt_add_one _
      have hgb : f b - c - η ≤ (g b : ℝ) := Int.le_ceil _
      rcases le_or_gt (g a + 1 - g b) 0 with hneg | hpos
      · rw [Int.toNat_of_nonpos hneg]
        have := hmono a b le_rfl hab le_rfl
        push_cast
        linarith
      · have e : ((Int.toNat (g a + 1 - g b) : ℕ) : ℝ) = ((g a + 1 - g b : ℤ) : ℝ) := by
          rw [← Int.cast_natCast, Int.toNat_of_nonneg hpos.le]
        rw [e]
        push_cast
        linarith
    calc ((S.image g).card : ℝ) ≤ ((Int.toNat (g a + 1 - g b) : ℕ) : ℝ) := by exact_mod_cast h1
      _ ≤ _ := h2
  have hmain := Finset.card_le_mul_card_image S F hfiber
  have hF' : (F : ℝ) ≤ 2 * η / μ + 1 := by
    rw [hF]
    push_cast
    linarith [Nat.floor_le (by positivity : 0 ≤ 2 * η / μ)]
  have h0 : (0 : ℝ) ≤ ((S.image g).card : ℝ) := Nat.cast_nonneg _
  calc (S.card : ℝ) ≤ (F : ℝ) * (S.image g).card := by exact_mod_cast hmain
    _ ≤ (2 * η / μ + 1) * (f a - f b + 2) := mul_le_mul hF' hcard_img h0 (by positivity)
    _ = (f a - f b + 2) * (2 * η / μ + 1) := by ring

/-! ## The jet of the logarithm -/

theorem fwdDiff_iter_const_eq_zero (h : ℝ) {n : ℕ} (hn : 1 ≤ n) (g : ℝ) :
    (fwdDiff h)^[n] (fun _ : ℝ => g) = fun _ => 0 := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have h0 : fwdDiff h (fun _ : ℝ => (0 : ℝ)) = fun _ => 0 := by funext x; simp [fwdDiff]
  have hg : fwdDiff h (fun _ : ℝ => g) = fun _ => 0 := by funext x; simp [fwdDiff]
  rw [Function.iterate_succ_apply, hg]
  exact Function.iterate_fixed h0 m

/-- **The jet is a function of `x/h`.** -/
theorem fwdDiff_iter_log_dilate {h x : ℝ} (hh : 0 < h) (hx : 0 < x) {n : ℕ} (hn : 1 ≤ n) :
    (fwdDiff h)^[n] Real.log x = (fwdDiff (1 : ℝ))^[n] Real.log (x / h) := by
  rw [fwdDiff_iter_eq_sum_shift, fwdDiff_iter_eq_sum_shift]
  have hconst : ∑ k ∈ range (n + 1), (((-1 : ℤ) ^ (n - k) * n.choose k : ℤ) : ℝ) = 0 := by
    have h1 := fwdDiff_iter_eq_sum_shift (h := h) (fun _ : ℝ => (1 : ℝ)) n 0
    rw [fwdDiff_iter_const_eq_zero h hn] at h1
    simp only [zsmul_eq_mul, mul_one] at h1
    exact h1.symm
  have hterm : ∀ k ∈ range (n + 1), Real.log (x + k • h) = Real.log h + Real.log (x / h + k • (1 : ℝ)) := by
    intro k _
    rw [nsmul_eq_mul, nsmul_eq_mul, mul_one, ← Real.log_mul hh.ne' (by positivity)]
    congr 1
    field_simp
  simp only [zsmul_eq_mul]
  rw [Finset.sum_congr rfl fun k hk => by rw [hterm k hk]]
  simp only [mul_add, Finset.sum_add_distrib, ← Finset.sum_mul, hconst, zero_mul, zero_add]

/-- The mass `|Δ^{j+1} log x| = ∫₀¹ j!/Π_{i≤j}(x + u + i) du`. -/
def logDiffMass (j : ℕ) (x : ℝ) : ℝ := ∫ u in (0 : ℝ)..1, PrimeTorusTheory.diffKernel j (x + u)

theorem logDiffMass_nonneg (j : ℕ) {x : ℝ} (hx : 0 < x) : 0 ≤ logDiffMass j x :=
  intervalIntegral.integral_nonneg (by norm_num) fun u hu =>
    (PrimeTorusTheory.diffKernel_pos (by linarith [hu.1])).le

theorem abs_fwdDiff_iter_log_eq (j : ℕ) {x : ℝ} (hx : 0 < x) :
    |(fwdDiff (1 : ℝ))^[j + 1] Real.log x| = logDiffMass j x := by
  rw [PrimeTorusTheory.fwdDiff_iter_log hx, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul]
  exact abs_of_nonneg (logDiffMass_nonneg j hx)

/-- **The jet moves at every step.** -/
theorem logDiffMass_sub_succ (j : ℕ) {x : ℝ} (hx : 0 < x) :
    logDiffMass j x - logDiffMass j (x + 1) = logDiffMass (j + 1) x := by
  have hx1 : 0 < x + 1 := by linarith
  have hstep : (fwdDiff (1 : ℝ))^[j + 1 + 1] Real.log x =
      (fwdDiff (1 : ℝ))^[j + 1] Real.log (x + 1) - (fwdDiff (1 : ℝ))^[j + 1] Real.log x := by
    rw [Function.iterate_succ_apply']
    rfl
  rw [PrimeTorusTheory.fwdDiff_iter_log (j := j + 1) hx, PrimeTorusTheory.fwdDiff_iter_log (j := j) hx1,
    PrimeTorusTheory.fwdDiff_iter_log (j := j) hx] at hstep
  have hsq : ((-1 : ℝ) ^ j) * (-1) ^ j = 1 := by rw [← mul_pow]; norm_num
  unfold logDiffMass
  linear_combination ((-1 : ℝ) ^ j) * hstep +
    ((∫ u in (0 : ℝ)..1, PrimeTorusTheory.diffKernel (j + 1) (x + u)) +
      (∫ u in (0 : ℝ)..1, PrimeTorusTheory.diffKernel j (x + 1 + u)) -
      (∫ u in (0 : ℝ)..1, PrimeTorusTheory.diffKernel j (x + u))) * hsq

theorem le_logDiffMass (j : ℕ) {x : ℝ} (hx : 0 < x) : (j.factorial : ℝ) / (x + j + 1) ^ (j + 1) ≤ logDiffMass j x := by
  rw [← abs_fwdDiff_iter_log_eq j hx]
  exact PrimeTorusTheory.le_abs_fwdDiff_iter_log hx

theorem logDiffMass_le (j : ℕ) {x : ℝ} (hx : 0 < x) : logDiffMass j x ≤ (j.factorial : ℝ) / x ^ (j + 1) := by
  rw [← abs_fwdDiff_iter_log_eq j hx]
  exact PrimeTorusTheory.abs_fwdDiff_iter_log_le hx

/-- **Exotic blocks are isolated.** -/
theorem card_exotic_le {t : ℝ} (ht : 0 < t) (j : ℕ) {X H : ℕ} (hX : 1 ≤ X) (c : ℝ) {η : ℝ} (hη : 0 ≤ η) :
    (((Icc X (X + H)).filter fun x => ∃ m : ℤ, |t * logDiffMass j x / (2 * π) - c - m| ≤ η).card : ℝ) ≤
      (t * j.factorial / (2 * π * (X : ℝ) ^ (j + 1)) + 2) *
        (2 * η * (2 * π * ((X : ℝ) + H + j + 2) ^ (j + 2) / (t * (j + 1).factorial)) + 1) := by
  set f : ℕ → ℝ := fun n => t * logDiffMass j n / (2 * π) with hf
  set μ : ℝ := t * (j + 1).factorial / (2 * π * ((X : ℝ) + H + j + 2) ^ (j + 2)) with hμ
  have hX0 : (0 : ℝ) < X := by exact_mod_cast hX
  have hμ0 : 0 < μ := by rw [hμ]; positivity
  have hstep : ∀ n, X ≤ n → n < X + H → μ ≤ f n - f (n + 1) := by
    intro n hn hnH
    have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
    have hsub := logDiffMass_sub_succ j hn0
    have hlow := le_logDiffMass (j + 1) hn0
    have hcast : ((n + 1 : ℕ) : ℝ) = (n : ℝ) + 1 := by push_cast; ring
    have hfd : f n - f (n + 1) = t * logDiffMass (j + 1) n / (2 * π) := by
      simp only [hf, hcast]
      rw [← sub_div, ← mul_sub, hsub]
    rw [hfd, hμ]
    have hbig : (n : ℝ) + (j + 1 : ℕ) + 1 ≤ (X : ℝ) + H + j + 2 := by
      have : (n : ℝ) ≤ X + H := by exact_mod_cast (by omega : n ≤ X + H)
      push_cast
      linarith
    have hpow : ((n : ℝ) + (j + 1 : ℕ) + 1) ^ (j + 1 + 1) ≤ ((X : ℝ) + H + j + 2) ^ (j + 2) :=
      pow_le_pow_left₀ (by positivity) hbig _
    have hk : ((j + 1).factorial : ℝ) / ((X : ℝ) + H + j + 2) ^ (j + 2) ≤ logDiffMass (j + 1) n :=
      le_trans (div_le_div_of_nonneg_left (by positivity) (by positivity) hpow) hlow
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    rw [div_le_iff₀ (by positivity)] at hk
    nlinarith [Real.pi_pos]
  have h := card_near_lattice_le (f := f) (by omega : X ≤ X + H) hμ0 hη hstep c
  have hfa : f X ≤ t * j.factorial / (2 * π * (X : ℝ) ^ (j + 1)) := by
    simp only [hf]
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have := logDiffMass_le j hX0
    rw [le_div_iff₀ (by positivity)] at this
    nlinarith [Real.pi_pos]
  have hfb : 0 ≤ f (X + H) := by
    simp only [hf]
    have : (0 : ℝ) < ((X + H : ℕ) : ℝ) := by exact_mod_cast (by omega : 0 < X + H)
    have := logDiffMass_nonneg j this
    positivity
  have hdiv : 2 * η / μ = 2 * η * (2 * π * ((X : ℝ) + H + j + 2) ^ (j + 2) / (t * (j + 1).factorial)) := by
    rw [hμ, div_div_eq_mul_div]
    ring
  rw [hdiv] at h
  have hpos : 0 ≤ 2 * η * (2 * π * ((X : ℝ) + H + j + 2) ^ (j + 2) / (t * (j + 1).factorial)) + 1 := by
    positivity
  calc _ ≤ (f X - f (X + H) + 2) *
        (2 * η * (2 * π * ((X : ℝ) + H + j + 2) ^ (j + 2) / (t * (j + 1).factorial)) + 1) := h
    _ ≤ _ := mul_le_mul_of_nonneg_right (by linarith) hpos

end

end GaloisForLFunctions.TailArithmeticOfThePrimeOrbit
