import GaloisForLFunctions.HeckeKreinToeplitz.APurePointSpectrumIsThinAtMostFrequencies
import GaloisForLFunctions.HeckeKreinToeplitz.TheWeilKernelIsKreinLangerOnTheFiniteStratum
import GaloisForLFunctions.HeckeKreinToeplitz.OneGridHidesTwoGridsDecide
import GaloisForLFunctions.ArithmeticCountingPositivity.NearMaximalGapsDoNotForceWeilPositivity
import GaloisForLFunctions.RHTower.WeilPhiDoobPrimeAtoms
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.TheFrobeniusSpanIsTheTowerOfTheScalingSurface
import GaloisForLFunctions.RenormalizedArithmeticPotentialTheory.EveryFiniteFlipSetHasAnExactResolutionThreshold

/-!
# On the finite stratum every flip has infinite index

Flip the sign of `Λ` at the odd powers of one prime `p` (`primeFlipWeight p`), keep the pole and
Gamma terms of `ζ`, and form the Weil kernel of a real test `f` on the Hecke lattice
(`weightKernel`). If `f` is supported in `[−a, a]` with `2a ≤ log p`, then on the tower of `p` the
twin differs from `ζ` by one explicit term (`weightKernel_flip_tower`):

`K_ω(p^d) = K_ζ(p^d) + 2 log p ‖f‖² p^{−|d|/2} [d odd]`.

The added kernel has Toeplitz symbol of the sign of `cos θ`: it is negative on blocks modulated
near `θ = π`, with energy `≍ −L` on a block of length `L`. Its decay `p^{−|d|/2}` is that of the
archimedean tail: after the sign gauge, the flip is the Gamma factor read at odd lags.

On the finite stratum `K_ζ` is a pure-point positive-definite kernel (the on-line zeros) plus
finitely many hyperbolic pairs. The pure-point part is thin near most frequencies
(`exists_frequency_thin`), the pairs cost one linear condition each, and well-separated blocks do
not interact. So the twin has at least `n − #(right zeros)` negative squares for every `n`.

**Main theorem** (`negIndex_zetaKernel_eq_top_or_flip`): `ζ` and any of its single-prime flips
never both have finite index. A finite-index ceiling for `ζ` is selective against every flip, and
the twin's index grows linearly in the length of the tower window.
-/

open Complex Finset Filter Topology
open scoped ComplexConjugate Real
open Zeta23
open GaloisForLFunctions.HTGeometry
open GaloisForLFunctions.ArithmeticCastelnuovoSeveri (cx realTests rightZeros cx_contDiff
  cx_hasCompactSupport translate_contDiff translate_hasCompactSupport)
open GaloisForLFunctions.ArithmeticCastelnuovoSeveri renaming translate → shiftTest
open GaloisForLFunctions.SquareRootThreshold (TemperedConfig temperedConfig_zetaZeroConfig)
open GaloisForLFunctions.RenormalizedArithmeticPotentialTheory (finiteFlip finiteFlip_prime_pow
  finiteFlip_eq_one_of_coprime)
open GaloisForLFunctions.ArithmeticCountingPositivity (primeFlipWeight)

noncomputable section

namespace GaloisForLFunctions.HeckeKreinToeplitz

/-! ### The Weil kernel of a weight -/

/-- The Weil kernel of a weight `λ` on the Hecke lattice: the explicit-formula functional (pole and
Gamma terms of `ζ`, prime weights `λ`) of a real test against its Hecke translates. -/
def weightKernel (lam : ℕ → ℝ) (f : ℝ → ℝ) (u : HeckeLattice) : ℂ :=
  RHTower.weilFullFunctional lam (EF.weilTest (cx f) (shiftTest (scale heckeLogScale u) (cx f)))

/-- For `Λ` the weight kernel is the orbit kernel of the zeros of `ζ` (explicit formula). -/
theorem weightKernel_vonMangoldt {f : ℝ → ℝ} (hf : f ∈ realTests) :
    weightKernel (fun n => (ArithmeticFunction.vonMangoldt n : ℝ)) f = orbitKernel zetaZeroConfig f := by
  funext u
  exact (RHTower.zeta_W_eq_weilFullFunctional_mixed (cx_contDiff hf.1) (cx_hasCompactSupport hf.2)
    (translate_contDiff (cx_contDiff hf.1) _) (translate_hasCompactSupport (cx_hasCompactSupport hf.2) _)).symm

/-- The point `p^d` of the tower of `p`. -/
def towerPt {p : ℕ} (hp : p.Prime) (d : ℤ) : HeckeLattice := primeElt hp ^ d

theorem scale_towerPt {p : ℕ} (hp : p.Prime) (d : ℤ) :
    scale heckeLogScale (towerPt hp d) = d * Real.log p := by
  rw [towerPt, scale_zpow, scale_primeElt]

theorem towerPt_inv_mul {p : ℕ} (hp : p.Prime) (d e : ℤ) :
    (towerPt hp d)⁻¹ * towerPt hp e = towerPt hp (e - d) := by
  rw [towerPt, towerPt, towerPt, ← zpow_neg, ← zpow_add, neg_add_eq_sub]

/-! ### The autocorrelation of the test -/

/-- The Weil test of `f` against its translate by `s` is the autocorrelation read at `x + s`. -/
theorem weilTest_shift_eq_crossCorr (f : ℝ → ℝ) (s x : ℝ) :
    EF.weilTest (cx f) (shiftTest s (cx f)) x = (RHTower.crossCorr f f (x + s) : ℂ) := by
  have h := ArithmeticCastelnuovoSeveri.weilTest_translate 0 s (cx f) (cx f) x
  have h0 : shiftTest 0 (cx f) = cx f := funext fun v => by
    simp [ArithmeticCastelnuovoSeveri.translate]
  rw [h0, show x - (0 - s) = x + s by ring] at h
  rw [h]
  exact RHTower.weilTest_real_crossCorr_eq f f (x + s)

/-- The autocorrelation of a test supported in `[−a, a]` vanishes at lags `|y| ≥ 2a`. -/
theorem crossCorr_eq_zero_of_support {f : ℝ → ℝ} {a : ℝ} (ha : ∀ u, a ≤ |u| → f u = 0) {y : ℝ}
    (hy : 2 * a ≤ |y|) : RHTower.crossCorr f f y = 0 := by
  unfold RHTower.crossCorr
  refine MeasureTheory.integral_eq_zero_of_ae (Filter.Eventually.of_forall fun t => ?_)
  change f t * f (t - y) = 0
  rcases le_or_gt a |t| with ht | ht
  · rw [ha t ht, zero_mul]
  · have hty : a ≤ |t - y| := by
      have h := abs_sub_abs_le_abs_sub y t
      rw [abs_sub_comm] at h
      linarith
    rw [ha (t - y) hty, mul_zero]

/-! ### The flip on its own tower -/

/-- The jump of the `p`-flip on the tower of `p`: `2 log p ‖f‖² p^{−|d|/2}` at odd `d`. -/
def flipJump (p : ℕ) (f : ℝ → ℝ) (d : ℤ) : ℝ :=
  if Odd d then 2 * Real.log p * RHTower.crossCorr f f 0 / Real.sqrt p ^ d.natAbs else 0

/-- The flipped coefficient is nonzero only at prime powers of `p`. -/
theorem eq_pow_of_flip_ne_zero {p n : ℕ} (hp : p.Prime)
    (h : (1 - finiteFlip {p} n) * (ArithmeticFunction.vonMangoldt n : ℝ) ≠ 0) :
    ∃ m, 1 ≤ m ∧ n = p ^ m := by
  have hΛ : (ArithmeticFunction.vonMangoldt n : ℝ) ≠ 0 := right_ne_zero_of_mul h
  have hpn : p ∣ n := by
    by_contra hpn
    rw [finiteFlip_eq_one_of_coprime fun q hq => by
      rw [Finset.mem_singleton] at hq; subst hq; exact hpn, sub_self, zero_mul] at h
    exact h rfl
  obtain ⟨q, m, hq, hm, rfl⟩ :=
    (isPrimePow_nat_iff _).mp (ArithmeticFunction.vonMangoldt_ne_zero_iff.mp hΛ)
  have hpq : p = q := (Nat.prime_dvd_prime_iff_eq hp hq).mp (hp.dvd_of_dvd_pow hpn)
  exact ⟨m, hm, by rw [hpq]⟩

/-- **The flip on its tower.** For a test supported in `[−a, a]` with `2a ≤ log p`, the twin kernel
on `p^d` is `ζ`'s kernel plus `flipJump p f d`. -/
theorem weightKernel_flip_tower {p : ℕ} (hp : p.Prime) {f : ℝ → ℝ} {a : ℝ}
    (ha : ∀ u, a ≤ |u| → f u = 0) (hap : 2 * a ≤ Real.log p) (d : ℤ) :
    weightKernel (primeFlipWeight p) f (towerPt hp d) =
      weightKernel (fun n => (ArithmeticFunction.vonMangoldt n : ℝ)) f (towerPt hp d) +
        (flipJump p f d : ℂ) := by
  classical
  set ℓ := Real.log p
  have hℓ : 0 < ℓ := Real.log_pos (by exact_mod_cast hp.one_lt)
  set s : ℝ := d * ℓ
  set k := EF.weilTest (cx f) (shiftTest (scale heckeLogScale (towerPt hp d)) (cx f))
  have hk : ∀ x, k x = (RHTower.crossCorr f f (x + s) : ℂ) := fun x => by
    simp only [k]; rw [weilTest_shift_eq_crossCorr, scale_towerPt]
  -- prime-part terms of a weight
  let T : (ℕ → ℝ) → ℕ → ℂ := fun lam n =>
    ((if 2 ≤ n then lam n / Real.sqrt n else 0 : ℝ) : ℂ) * (k (Real.log n) + k (-Real.log n))
  -- the terms vanish beyond `exp(|s| + 2a)`
  set N₀ : ℕ := ⌈Real.exp (|s| + 2 * a)⌉₊
  have hfar : ∀ n : ℕ, N₀ ≤ n → k (Real.log n) + k (-Real.log n) = 0 := by
    intro n hn
    have hn0 : (0 : ℝ) < n := lt_of_lt_of_le (Real.exp_pos _) ((Nat.le_ceil _).trans
      (by exact_mod_cast hn))
    have hlog : |s| + 2 * a ≤ Real.log n := by
      rw [Real.le_log_iff_exp_le hn0]
      exact (Nat.le_ceil _).trans (by exact_mod_cast hn)
    have h1 : 2 * a ≤ |Real.log n + s| := by
      have := neg_abs_le s
      exact le_trans (by linarith) (le_abs_self _)
    have h2 : 2 * a ≤ |-Real.log n + s| := by
      have h := neg_le_abs (-Real.log n + s)
      linarith [le_abs_self s]
    rw [hk, hk, crossCorr_eq_zero_of_support ha h1, crossCorr_eq_zero_of_support ha h2]
    simp
  have hsum : ∀ lam : ℕ → ℝ, Summable (T lam) := fun lam =>
    summable_of_ne_finset_zero (s := range N₀) fun n hn => by
      have := hfar n (by simpa using hn)
      simp only [T, this, mul_zero]
  -- reduce to the prime parts
  have hpart : RHTower.WeilSpectral.primePart (fun n => (ArithmeticFunction.vonMangoldt n : ℝ)) k -
      RHTower.WeilSpectral.primePart (primeFlipWeight p) k = (flipJump p f d : ℂ) := by
    change ∑' n, T _ n - ∑' n, T _ n = _
    rw [← (hsum _).tsum_sub (hsum _)]
    -- the difference of the weights
    have hdiff : ∀ n : ℕ, T (fun n => (ArithmeticFunction.vonMangoldt n : ℝ)) n -
        T (primeFlipWeight p) n = ((if 2 ≤ n then (1 - finiteFlip {p} n) *
          (ArithmeticFunction.vonMangoldt n : ℝ) / Real.sqrt n else 0 : ℝ) : ℂ) *
          (k (Real.log n) + k (-Real.log n)) := fun n => by
      simp only [T, primeFlipWeight]
      split_ifs <;> push_cast <;> ring
    rw [tsum_congr hdiff, tsum_eq_single (p ^ d.natAbs)]
    · -- the surviving term
      rcases Int.even_or_odd d with hev | hodd
      · have hnot : ¬ Odd d := Int.not_odd_iff_even.mpr hev
        rw [flipJump, if_neg hnot]
        have hfl : finiteFlip {p} (p ^ d.natAbs) = 1 := by
          rw [finiteFlip_prime_pow hp, if_pos (Finset.mem_singleton_self p),
            Even.neg_one_pow (Int.natAbs_even.mpr hev)]
        simp [hfl]
      · have hd0 : d ≠ 0 := by rintro rfl; exact absurd hodd (by decide)
        have hna : 1 ≤ d.natAbs := Int.natAbs_pos.mpr hd0
        have h2 : 2 ≤ p ^ d.natAbs := hp.two_le.trans (Nat.le_self_pow (by omega) p)
        have hfl : finiteFlip {p} (p ^ d.natAbs) = -1 := by
          rw [finiteFlip_prime_pow hp, if_pos (Finset.mem_singleton_self p),
            Odd.neg_one_pow (Int.natAbs_odd.mpr hodd)]
        have hΛ : (ArithmeticFunction.vonMangoldt (p ^ d.natAbs) : ℝ) = ℓ := by
          rw [ArithmeticFunction.vonMangoldt_apply_pow (by omega),
            ArithmeticFunction.vonMangoldt_apply_prime hp]
        have hsq : Real.sqrt ((p ^ d.natAbs : ℕ) : ℝ) = Real.sqrt p ^ d.natAbs := by
          push_cast
          have hx : ((p : ℝ)) ^ d.natAbs = (Real.sqrt p ^ d.natAbs) ^ 2 := by
            rw [← pow_mul, mul_comm, pow_mul, Real.sq_sqrt (Nat.cast_nonneg _)]
          rw [hx, Real.sqrt_sq (pow_nonneg (Real.sqrt_nonneg _) _)]
        -- one of the two lags is `0`, the other `2|d| ℓ`
        have hlogn : Real.log ((p ^ d.natAbs : ℕ) : ℝ) = d.natAbs * ℓ := by
          push_cast; rw [Real.log_pow]
        have hsum2 : k (Real.log ((p ^ d.natAbs : ℕ) : ℝ)) +
            k (-Real.log ((p ^ d.natAbs : ℕ) : ℝ)) = (RHTower.crossCorr f f 0 : ℂ) := by
          rw [hk, hk, hlogn]
          have hfar2 : 2 * a ≤ |2 * d * ℓ| := by
            rw [abs_mul, abs_mul, abs_two, abs_of_pos hℓ]
            have : (1 : ℝ) ≤ |(d : ℝ)| := by
              rw [← Int.cast_abs]; exact_mod_cast Int.one_le_abs hd0
            nlinarith
          rcases lt_or_gt_of_ne hd0 with hneg | hpos
          · have hab : (d.natAbs : ℝ) = -d := by
              rw [Nat.cast_natAbs, Int.cast_abs, abs_of_neg (by exact_mod_cast hneg)]
            rw [hab, show -(d : ℝ) * ℓ + s = 0 by simp only [s]; ring,
              show -(-(d : ℝ) * ℓ) + s = 2 * d * ℓ by simp only [s]; ring,
              crossCorr_eq_zero_of_support ha hfar2]
            simp
          · have hab : (d.natAbs : ℝ) = d := by
              rw [Nat.cast_natAbs, Int.cast_abs, abs_of_pos (by exact_mod_cast hpos)]
            rw [hab, show (d : ℝ) * ℓ + s = 2 * d * ℓ by simp only [s]; ring,
              show -((d : ℝ) * ℓ) + s = 0 by simp only [s]; ring,
              crossCorr_eq_zero_of_support ha hfar2]
            simp
        rw [if_pos h2, hfl, hΛ, hsum2, flipJump, if_pos hodd, hsq, ← Complex.ofReal_mul]
        congr 1
        simp only [ℓ]
        ring
    · -- every other term vanishes
      intro n hn
      by_cases h2 : 2 ≤ n
      swap
      · simp [h2]
      by_cases hc : (1 - finiteFlip {p} n) * (ArithmeticFunction.vonMangoldt n : ℝ) = 0
      · simp [hc]
      obtain ⟨m, hm, rfl⟩ := eq_pow_of_flip_ne_zero hp hc
      have hmd : m ≠ d.natAbs := fun h => hn (by rw [h])
      have hlogn : Real.log ((p ^ m : ℕ) : ℝ) = m * ℓ := by push_cast; rw [Real.log_pow]
      have hz1 : RHTower.crossCorr f f (m * ℓ + s) = 0 := by
        refine crossCorr_eq_zero_of_support ha ?_
        have hne : (m : ℤ) + d ≠ 0 := by
          intro h; apply hmd; omega
        have h1 : (1 : ℝ) ≤ |(((m : ℤ) + d : ℤ) : ℝ)| := by
          rw [← Int.cast_abs]; exact_mod_cast Int.one_le_abs hne
        rw [show (m : ℝ) * ℓ + s = (((m : ℤ) + d : ℤ) : ℝ) * ℓ by simp only [s]; push_cast; ring,
          abs_mul, abs_of_pos hℓ]
        nlinarith
      have hz2 : RHTower.crossCorr f f (-(m * ℓ) + s) = 0 := by
        refine crossCorr_eq_zero_of_support ha ?_
        have hne : d - (m : ℤ) ≠ 0 := by
          intro h; apply hmd; omega
        have h1 : (1 : ℝ) ≤ |((d - (m : ℤ) : ℤ) : ℝ)| := by
          rw [← Int.cast_abs]; exact_mod_cast Int.one_le_abs hne
        rw [show -((m : ℝ) * ℓ) + s = ((d - (m : ℤ) : ℤ) : ℝ) * ℓ by simp only [s]; push_cast; ring,
          abs_mul, abs_of_pos hℓ]
        nlinarith
      rw [hk, hk, hlogn, hz1, hz2]
      simp
  unfold weightKernel
  rw [RHTower.WeilSpectral.weilFullFunctional_eq_parts,
    RHTower.WeilSpectral.weilFullFunctional_eq_parts, ← hpart]
  ring


/-! ### The flip block -/

/-- For odd `d`, `cos(dθ) ≤ −1 + |d| δ` when `|θ − π| ≤ δ`. -/
theorem cos_odd_mul_le {θ δ : ℝ} (hθ : |θ - π| ≤ δ) {d : ℤ} (hd : Odd d) :
    Real.cos (d * θ) ≤ -1 + d.natAbs * δ := by
  obtain ⟨m, rfl⟩ := odd_iff_exists_bit1.mp hd
  set φ := θ - π
  have h1 : Real.cos (((2 * m + 1 : ℤ) : ℝ) * θ) = -Real.cos (((2 * m + 1 : ℤ) : ℝ) * φ) := by
    rw [show ((2 * m + 1 : ℤ) : ℝ) * θ = ((2 * m + 1 : ℤ) : ℝ) * φ + π + (m : ℤ) * (2 * π) by
      simp only [φ]; push_cast; ring, Real.cos_add_int_mul_two_pi, Real.cos_add_pi]
  have h2 : 1 - Real.cos (((2 * m + 1 : ℤ) : ℝ) * φ) ≤ |((2 * m + 1 : ℤ) : ℝ) * φ| := by
    have := Real.abs_cos_sub_cos_le (((2 * m + 1 : ℤ) : ℝ) * φ) 0
    rw [Real.cos_zero, sub_zero, abs_sub_comm] at this
    exact (le_abs_self _).trans this
  have h3 : |((2 * m + 1 : ℤ) : ℝ) * φ| ≤ ((2 * m + 1 : ℤ).natAbs : ℝ) * δ := by
    rw [abs_mul, Nat.cast_natAbs, Int.cast_abs]
    exact mul_le_mul_of_nonneg_left hθ (abs_nonneg _)
  rw [h1]; linarith

/-- A row sum over `|l' − l|` is at most twice the sum over `j < L`. -/
theorem sum_range_natAbs_sub_le {h : ℕ → ℝ} (hh : ∀ j, 0 ≤ h j) {L l : ℕ} (hl : l < L) :
    ∑ l' ∈ range L, h ((l' : ℤ) - l).natAbs ≤ 2 * ∑ j ∈ range L, h j := by
  classical
  rw [← sum_filter_add_sum_filter_not (range L) (fun l' => l ≤ l'), two_mul]
  refine add_le_add ?_ ?_
  · calc ∑ l' ∈ (range L).filter (fun l' => l ≤ l'), h ((l' : ℤ) - l).natAbs
        = ∑ l' ∈ (range L).filter (fun l' => l ≤ l'), h (l' - l) :=
          sum_congr rfl fun l' hl' => by
            have := (mem_filter.mp hl').2
            congr 1; omega
      _ = ∑ j ∈ ((range L).filter (fun l' => l ≤ l')).image (fun l' => l' - l), h j :=
          (sum_image fun a ha b hb hab => by
            have := (mem_filter.mp ha).2; have := (mem_filter.mp hb).2
            omega).symm
      _ ≤ ∑ j ∈ range L, h j := by
          refine sum_le_sum_of_subset_of_nonneg (fun j hj => ?_) fun j _ _ => hh j
          obtain ⟨l', hl', rfl⟩ := mem_image.mp hj
          have := mem_range.mp (mem_filter.mp hl').1
          exact mem_range.mpr (by omega)
  · calc ∑ l' ∈ (range L).filter (fun l' => ¬ l ≤ l'), h ((l' : ℤ) - l).natAbs
        = ∑ l' ∈ (range L).filter (fun l' => ¬ l ≤ l'), h (l - l') :=
          sum_congr rfl fun l' hl' => by
            have := (mem_filter.mp hl').2
            congr 1; omega
      _ = ∑ j ∈ ((range L).filter (fun l' => ¬ l ≤ l')).image (fun l' => l - l'), h j :=
          (sum_image fun a ha b hb hab => by
            have := (mem_filter.mp ha).2; have := (mem_filter.mp hb).2
            omega).symm
      _ ≤ ∑ j ∈ range L, h j := by
          refine sum_le_sum_of_subset_of_nonneg (fun j hj => ?_) fun j _ _ => hh j
          obtain ⟨l', hl', rfl⟩ := mem_image.mp hj
          have h1 := mem_range.mp (mem_filter.mp hl').1
          have h2 := (mem_filter.mp hl').2
          exact mem_range.mpr (by omega)

/-- **The odd Poisson block.** For `0 < r < 1`, `L ≥ 4` and `|θ − π| ≤ (1 − r)²/8`, the Toeplitz
form of `d ↦ r^{|d|} [d odd]` on the block `(e^{ilθ})_{l<L}` is at most `−L r/2`. -/
theorem oddPoisson_block_le {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1) {L : ℕ} (hL : 4 ≤ L) {θ : ℝ}
    (hθ : |θ - π| ≤ (1 - r) ^ 2 / 8) :
    ∑ l ∈ range L, ∑ l' ∈ range L, (if Odd ((l' : ℤ) - l) then
      Real.cos ((((l' : ℤ) - l : ℤ) : ℝ) * θ) * r ^ ((l' : ℤ) - l).natAbs else 0) ≤
        -(L * r / 2) := by
  set δ := (1 - r) ^ 2 / 8
  have hδ : 0 ≤ δ := by positivity
  set g : ℤ → ℝ := fun d => if Odd d then r ^ d.natAbs else 0
  set q : ℕ → ℝ := fun j => j * r ^ j
  have hq : ∀ j, 0 ≤ q j := fun j => by positivity
  -- termwise bound
  have hterm : ∀ l l' : ℕ, (if Odd ((l' : ℤ) - l) then
      Real.cos ((((l' : ℤ) - l : ℤ) : ℝ) * θ) * r ^ ((l' : ℤ) - l).natAbs else 0) ≤
        -g ((l' : ℤ) - l) + δ * q ((l' : ℤ) - l).natAbs := by
    intro l l'
    simp only [g, q]
    split_ifs with hodd
    · have hc := cos_odd_mul_le hθ hodd
      have hp : 0 ≤ r ^ ((l' : ℤ) - l).natAbs := by positivity
      nlinarith
    · have : 0 ≤ δ * (((((l' : ℤ) - l).natAbs : ℕ) : ℝ) * r ^ ((l' : ℤ) - l).natAbs) := by positivity
      linarith
  -- the neighbours carry `(L − 1) r`
  have hneg : ((L : ℝ) - 1) * r ≤ ∑ l ∈ range L, ∑ l' ∈ range L, g ((l' : ℤ) - l) := by
    obtain ⟨K, rfl⟩ : ∃ K, L = K + 1 := ⟨L - 1, by omega⟩
    have hrow : ∀ l ∈ range (K + 1), (if l + 1 < K + 1 then r else 0) ≤
        ∑ l' ∈ range (K + 1), g ((l' : ℤ) - l) := by
      intro l _
      have hg0 : ∀ l' ∈ range (K + 1), 0 ≤ g ((l' : ℤ) - l) := fun l' _ => by
        simp only [g]; split_ifs <;> positivity
      split_ifs with h
      · have h1 := single_le_sum hg0 (mem_range.mpr h)
        have hg1 : g (((l + 1 : ℕ) : ℤ) - l) = r := by
          simp only [g]
          rw [show ((l + 1 : ℕ) : ℤ) - l = 1 by push_cast; ring, if_pos odd_one]
          simp
        rwa [hg1] at h1
      · exact sum_nonneg hg0
    have hsum : ∑ l ∈ range (K + 1), (if l + 1 < K + 1 then r else 0) = K * r := by
      rw [Finset.sum_range_succ, if_neg (by omega), add_zero,
        sum_congr rfl fun l hl => if_pos (by have := mem_range.mp hl; omega), sum_const,
        card_range, nsmul_eq_mul]
    calc (((K + 1 : ℕ) : ℝ) - 1) * r = K * r := by push_cast; ring
      _ = _ := hsum.symm
      _ ≤ _ := sum_le_sum hrow
  -- the detuning costs at most `δ L · 2r/(1 − r)²`
  have hpos : ∑ l ∈ range L, ∑ l' ∈ range L, q ((l' : ℤ) - l).natAbs ≤
      L * (2 * (r / (1 - r) ^ 2)) := by
    have hnorm : ‖r‖ < 1 := by rw [Real.norm_eq_abs, abs_of_pos hr0]; exact hr1
    have hsumm : Summable q := by
      simpa [q, pow_one] using summable_pow_mul_geometric_of_norm_lt_one (R := ℝ) 1 hnorm
    have htsum : ∑' j, q j = r / (1 - r) ^ 2 := tsum_coe_mul_geometric_of_norm_lt_one hnorm
    have hrow : ∀ l ∈ range L, ∑ l' ∈ range L, q ((l' : ℤ) - l).natAbs ≤ 2 * (r / (1 - r) ^ 2) :=
      fun l hl => (sum_range_natAbs_sub_le hq (mem_range.mp hl)).trans (by
        rw [← htsum]
        exact mul_le_mul_of_nonneg_left (hsumm.sum_le_tsum _ fun j _ => hq j) (by norm_num))
    calc _ ≤ ∑ l ∈ range L, 2 * (r / (1 - r) ^ 2) := sum_le_sum hrow
      _ = _ := by rw [sum_const, card_range, nsmul_eq_mul]
  have hδbound : δ * (L * (2 * (r / (1 - r) ^ 2))) = L * r / 4 := by
    have h1r : (1 - r) ≠ 0 := by linarith
    simp only [δ]; field_simp; ring
  have hL4 : (4 : ℝ) ≤ L := by exact_mod_cast hL
  calc _ ≤ ∑ l ∈ range L, ∑ l' ∈ range L, (-g ((l' : ℤ) - l) + δ * q ((l' : ℤ) - l).natAbs) :=
        sum_le_sum fun l _ => sum_le_sum fun l' _ => hterm l l'
    _ = -(∑ l ∈ range L, ∑ l' ∈ range L, g ((l' : ℤ) - l)) +
        δ * ∑ l ∈ range L, ∑ l' ∈ range L, q ((l' : ℤ) - l).natAbs := by
        simp only [sum_add_distrib, sum_neg_distrib, mul_sum]
    _ ≤ -(((L : ℝ) - 1) * r) + δ * (L * (2 * (r / (1 - r) ^ 2))) := by
        gcongr
    _ ≤ -(L * r / 2) := by rw [hδbound]; nlinarith


/-! ### Block families on the tower -/

/-- The exponents `kG + l` of `n` blocks of length `L` spaced by `G`. -/
def blockExp (G : ℕ) {n L : ℕ} (b : Fin n × Fin L) : ℤ := (b.1 : ℤ) * G + (b.2 : ℕ)

/-- The tower points `p^{kG + l}` of the blocks. -/
def blockPt {p : ℕ} (hp : p.Prime) (G : ℕ) {n L : ℕ} (b : Fin n × Fin L) : HeckeLattice :=
  towerPt hp (blockExp G b)

/-- The block vector: `a_k e^{i l θ₀}` on block `k`. -/
def blockVec (n L : ℕ) (θ₀ : ℝ) : (Fin n → ℂ) →ₗ[ℂ] (Fin n × Fin L → ℂ) where
  toFun a b := a b.1 * cexp (I * θ₀) ^ (b.2 : ℕ)
  map_add' a a' := by funext b; simp [add_mul]
  map_smul' t a := by funext b; simp [mul_assoc]

theorem blockVec_apply (n L : ℕ) (θ₀ : ℝ) (a : Fin n → ℂ) (b : Fin n × Fin L) :
    blockVec n L θ₀ a b = a b.1 * cexp (I * θ₀) ^ (b.2 : ℕ) := rfl

theorem blockVec_injective {n L : ℕ} (hL : 0 < L) (θ₀ : ℝ) :
    Function.Injective (blockVec n L θ₀) := by
  rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
  intro a ha
  funext k
  have h := congrFun (LinearMap.mem_ker.mp ha) (k, ⟨0, hL⟩)
  simpa [blockVec_apply] using h

/-- The amplitude of a block vector at a frequency factors through the Dirichlet block. -/
theorem blockAmp_eq (G : ℕ) {n L : ℕ} (θ₀ θ : ℝ) (a : Fin n → ℂ) :
    ∑ b : Fin n × Fin L, blockVec n L θ₀ a b * cexp (-(I * θ) * (blockExp G b : ℝ)) =
      (∑ k, a k * cexp (-(I * θ) * ((((k : ℤ) * G : ℤ) : ℝ) : ℂ))) * dirichletBlock L (θ₀ - θ) := by
  rw [dirichletBlock, Fintype.sum_prod_type, sum_mul]
  refine sum_congr rfl fun k _ => ?_
  rw [mul_assoc, ← Fin.sum_univ_eq_sum_range (fun l : ℕ => cexp (I * ((θ₀ - θ : ℝ) : ℂ)) ^ l) L,
    Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [blockVec_apply, blockExp]
  have : cexp (I * θ₀) ^ (l : ℕ) * cexp (-(I * θ) * ((((k : ℤ) * G + (l : ℕ) : ℤ)) : ℝ)) =
      cexp (-(I * θ) * (((k : ℤ) * G : ℤ) : ℝ)) * cexp (I * ((θ₀ - θ : ℝ) : ℂ)) ^ (l : ℕ) := by
    rw [← Complex.exp_nat_mul, ← Complex.exp_nat_mul, ← Complex.exp_add, ← Complex.exp_add]
    congr 1
    push_cast
    ring
  rw [mul_assoc, this]
  push_cast

/-- **Pure-point part on a block family.** If `K(p^e) = Σ_i W_i e^{−i θ_i e}` with absolutely
summable `W` of nonnegative real part, the form of `K` on a block vector is at most
`n Σ_k |a_k|² Σ_i Re W_i |D_L(θ_i − θ₀)|²`. -/
theorem re_blockSum_pp_le {ι' : Type*} {W : ι' → ℂ} (hW : Summable fun i => ‖W i‖)
    (hWre : ∀ i, 0 ≤ (W i).re) (θ : ι' → ℝ) (G : ℕ) {n L : ℕ} (θ₀ : ℝ) (a : Fin n → ℂ) :
    (∑ b : Fin n × Fin L, ∑ b' : Fin n × Fin L, conj (blockVec n L θ₀ a b) *
        (∑' i, W i * cexp (-(I * θ i) * ((blockExp G b' - blockExp G b : ℤ) : ℝ))) *
          blockVec n L θ₀ a b').re ≤
      n * (∑ k, ‖a k‖ ^ 2) * ∑' i, (W i).re * ‖dirichletBlock L (θ i - θ₀)‖ ^ 2 := by
  set c := blockVec n L θ₀ a
  set A : ι' → ℂ := fun i => ∑ b, c b * cexp (-(I * θ i) * (blockExp G b : ℝ))
  have hE : ∀ i (b b' : Fin n × Fin L), cexp (-(I * θ i) * ((blockExp G b' - blockExp G b : ℤ) : ℝ)) =
      conj (cexp (-(I * θ i) * (blockExp G b : ℝ))) * cexp (-(I * θ i) * (blockExp G b' : ℝ)) := by
    intro i b b'
    rw [← Complex.exp_conj, ← Complex.exp_add]
    congr 1
    simp only [map_mul, map_neg, Complex.conj_I, Complex.conj_ofReal]
    push_cast
    ring
  have hsumm : ∀ (b b' : Fin n × Fin L), Summable fun i =>
      conj (c b) * (W i * cexp (-(I * θ i) * ((blockExp G b' - blockExp G b : ℤ) : ℝ))) * c b' := by
    intro b b'
    refine Summable.of_norm_bounded ((hW.mul_left (‖c b‖ * ‖c b'‖))) fun i => ?_
    rw [norm_mul, norm_mul, norm_mul, Complex.norm_conj, show
      ‖cexp (-(I * θ i) * ((blockExp G b' - blockExp G b : ℤ) : ℝ))‖ = 1 by
        rw [show -(I * θ i) * (((blockExp G b' - blockExp G b : ℤ) : ℝ) : ℂ) =
          ((-(θ i * (blockExp G b' - blockExp G b : ℤ)) : ℝ) : ℂ) * I by push_cast; ring]
        exact Complex.norm_exp_ofReal_mul_I _]
    nlinarith [norm_nonneg (c b), norm_nonneg (c b'), norm_nonneg (W i)]
  -- interchange the finite sums with the zero sum
  have hswap : ∑ b, ∑ b', conj (c b) *
        (∑' i, W i * cexp (-(I * θ i) * ((blockExp G b' - blockExp G b : ℤ) : ℝ))) * c b' =
      ∑' i, W i * ((Complex.normSq (A i) : ℝ) : ℂ) := by
    calc _ = ∑ b, ∑ b', ∑' i, conj (c b) *
            (W i * cexp (-(I * θ i) * ((blockExp G b' - blockExp G b : ℤ) : ℝ))) * c b' :=
          sum_congr rfl fun b _ => sum_congr rfl fun b' _ => by rw [tsum_mul_right, tsum_mul_left]
      _ = ∑ b, ∑' i, ∑ b', conj (c b) *
            (W i * cexp (-(I * θ i) * ((blockExp G b' - blockExp G b : ℤ) : ℝ))) * c b' :=
          sum_congr rfl fun b _ => (Summable.tsum_finsetSum fun b' _ => hsumm b b').symm
      _ = ∑' i, ∑ b, ∑ b', conj (c b) *
            (W i * cexp (-(I * θ i) * ((blockExp G b' - blockExp G b : ℤ) : ℝ))) * c b' :=
          (Summable.tsum_finsetSum fun b _ => summable_sum fun b' _ => hsumm b b').symm
      _ = _ := tsum_congr fun i => by
          rw [Complex.normSq_eq_conj_mul_self, map_sum, sum_mul_sum, mul_sum]
          refine sum_congr rfl fun b _ => ?_
          rw [mul_sum]
          refine sum_congr rfl fun b' _ => ?_
          rw [hE i b b', map_mul]
          ring
  -- the amplitude bound
  have hA : ∀ i, Complex.normSq (A i) ≤ n * (∑ k, ‖a k‖ ^ 2) * ‖dirichletBlock L (θ i - θ₀)‖ ^ 2 := by
    intro i
    have hAeq : A i = (∑ k, a k * cexp (-(I * θ i) * ((((k : ℤ) * G : ℤ) : ℝ) : ℂ))) *
        dirichletBlock L (θ₀ - θ i) := blockAmp_eq G θ₀ (θ i) a
    have hnk : ‖∑ k, a k * cexp (-(I * θ i) * ((((k : ℤ) * G : ℤ) : ℝ) : ℂ))‖ ≤ ∑ k, ‖a k‖ := by
      refine (norm_sum_le _ _).trans (sum_le_sum fun k _ => ?_)
      rw [norm_mul, show -(I * θ i) * ((((k : ℤ) * G : ℤ) : ℝ) : ℂ) =
        ((-(θ i * (((k : ℤ) * G : ℤ) : ℝ))) : ℝ) * I by push_cast; ring,
        Complex.norm_exp_ofReal_mul_I, mul_one]
    have hcs : (∑ k, ‖a k‖) ^ 2 ≤ n * ∑ k, ‖a k‖ ^ 2 := by
      have := sq_sum_le_card_mul_sum_sq (s := (univ : Finset (Fin n))) (f := fun k => ‖a k‖)
      simpa using this
    rw [Complex.normSq_eq_norm_sq, hAeq, norm_mul,
      show θ₀ - θ i = -(θ i - θ₀) by ring, norm_dirichletBlock_neg, mul_pow]
    exact mul_le_mul_of_nonneg_right ((pow_le_pow_left₀ (norm_nonneg _) hnk 2).trans hcs)
      (by positivity)
  have hAbd : ∀ i, Complex.normSq (A i) ≤ n * (∑ k, ‖a k‖ ^ 2) * (L : ℝ) ^ 2 := fun i =>
    (hA i).trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _)
      (norm_dirichletBlock_le_card L _) 2) (by positivity))
  have hsumW : Summable fun i => W i * ((Complex.normSq (A i) : ℝ) : ℂ) :=
    Summable.of_norm_bounded (hW.mul_right (n * (∑ k, ‖a k‖ ^ 2) * (L : ℝ) ^ 2)) fun i => by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Complex.normSq_nonneg _)]
      exact mul_le_mul_of_nonneg_left (hAbd i) (norm_nonneg _)
  have hre_le : ∀ i, |(W i).re| ≤ ‖W i‖ := fun i => Complex.abs_re_le_norm _
  have hsumR : Summable fun i => (W i).re * ‖dirichletBlock L (θ i - θ₀)‖ ^ 2 :=
    Summable.of_norm_bounded (hW.mul_right ((L : ℝ) ^ 2)) fun i => by
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (pow_nonneg (norm_nonneg _) 2)]
      exact mul_le_mul (hre_le i) (pow_le_pow_left₀ (norm_nonneg _)
        (norm_dirichletBlock_le_card L _) 2) (by positivity) (norm_nonneg _)
  rw [hswap, Complex.re_tsum hsumW]
  simp only [Complex.re_mul_ofReal]
  rw [← tsum_mul_left]
  refine Summable.tsum_le_tsum (fun i => ?_) ?_ (hsumR.mul_left _)
  · calc (W i).re * Complex.normSq (A i)
        ≤ (W i).re * (n * (∑ k, ‖a k‖ ^ 2) * ‖dirichletBlock L (θ i - θ₀)‖ ^ 2) :=
          mul_le_mul_of_nonneg_left (hA i) (hWre i)
      _ = _ := by ring
  · exact Summable.of_norm_bounded (hW.mul_right (n * (∑ k, ‖a k‖ ^ 2) * (L : ℝ) ^ 2)) fun i => by
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (Complex.normSq_nonneg _)]
      exact mul_le_mul (hre_le i) (hAbd i) (Complex.normSq_nonneg _) (norm_nonneg _)

end GaloisForLFunctions.HeckeKreinToeplitz
