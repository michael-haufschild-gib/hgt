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

end GaloisForLFunctions.HeckeKreinToeplitz
