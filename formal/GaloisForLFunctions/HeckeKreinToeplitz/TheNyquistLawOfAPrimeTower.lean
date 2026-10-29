import GaloisForLFunctions.HeckeKreinToeplitz.OnePrimeTowerCountsTheDistinctFrobeniusValues

/-!
# The Nyquist law of a prime tower

What one prime can hide, at bounded height. Two zeros alias on the tower of `p` iff
`p^{ρ−½} = p^{ρ'−½}`, i.e. they have the same real part and their ordinates differ by a multiple
of `2π/log p` (`re_eq_and_im_sub_eq_of_frobEig_eq`). The tower samples the ordinate at the Nyquist
spacing `2π/log p`.

**Window law** (`card_le_mul_card_image_frobEig`). Among zeros whose ordinates lie in a window of
length `H`, each Frobenius value is shared by at most `⌊H log p/2π⌋ + 1` of them.

**One prime sees a fixed fraction** (`card_le_mul_iSup_negIndex_towerKernel`). For `ζ`, any finite
set of right zeros with ordinates in a window of length `H` has at most `⌊H log p/2π⌋ + 1` times as
many elements as the index on the tower of `p` (supremum over generators). At height `T`, so with
`H = 2T`, one prime hides at most a factor `⌊T log p/π⌋ + 1`.

**Nyquist** (`card_le_iSup_negIndex_towerKernel_of_window`). In a window of length below
`2π/log p` the tower of `p` sees every right zero. For `p = 2` the window length is
`2π/log 2 ≈ 9.06`.
-/

open Complex Finset
open scoped Real
open Zeta23
open GaloisForLFunctions.ArithmeticCastelnuovoSeveri (frobEig outerEig rightZeros)

noncomputable section

namespace GaloisForLFunctions.HeckeKreinToeplitz

/-- Two zeros alias at scale `ℓ` iff `ℓ(τ − τ') ∈ 2πiℤ`. -/
theorem frobEig_eq_frobEig_iff {ℓ : ℝ} {τ τ' : ℂ} :
    frobEig ℓ τ = frobEig ℓ τ' ↔ ∃ n : ℤ, ℓ * (τ - τ') = n * (2 * π * I) := by
  rw [frobEig, frobEig, Complex.exp_eq_exp_iff_exists_int]
  refine exists_congr fun n => ?_
  constructor <;> intro h <;> linear_combination h

/-- Aliased zeros have the same real part and ordinates `2π/ℓ`-apart. -/
theorem re_eq_and_im_sub_eq_of_frobEig_eq {ℓ : ℝ} (hℓ : 0 < ℓ) {τ τ' : ℂ}
    (h : frobEig ℓ τ = frobEig ℓ τ') : ∃ n : ℤ, τ.re = τ'.re ∧ τ.im - τ'.im = n * (2 * π / ℓ) := by
  obtain ⟨n, hn⟩ := frobEig_eq_frobEig_iff.mp h
  have hre := congrArg Complex.re hn
  have him := congrArg Complex.im hn
  simp only [mul_re, mul_im, ofReal_re, ofReal_im, sub_re, sub_im, intCast_re, intCast_im,
    I_re, I_im, zero_mul, sub_zero, mul_zero, mul_one, add_zero, re_ofNat, im_ofNat] at hre him
  refine ⟨n, ?_, ?_⟩
  · have : ℓ * (τ.re - τ'.re) = 0 := by linarith
    have := (mul_eq_zero.mp this).resolve_left hℓ.ne'
    linarith
  · field_simp
    linarith

/-- Points of one lattice coset `γ₀ + hℤ` (with a common real part) in an interval of length `H`
number at most `⌊H/h⌋ + 1`. -/
theorem card_le_of_im_sub_mem_lattice {S : Finset ℂ} {h H a : ℝ} (hh : 0 < h)
    (hS : ∀ τ ∈ S, ∀ τ' ∈ S, ∃ n : ℤ, τ.re = τ'.re ∧ τ.im - τ'.im = n * h)
    (hwin : ∀ τ ∈ S, a ≤ τ.im ∧ τ.im ≤ a + H) : S.card ≤ ⌊H / h⌋₊ + 1 := by
  rcases S.eq_empty_or_nonempty with rfl | hne
  · simp
  obtain ⟨τ₀, hτ₀, hmin⟩ := S.exists_min_image (fun τ => τ.im) hne
  have key : ∀ τ ∈ S, ∃ k : ℕ, τ = τ₀ + (k * h : ℝ) * I ∧ k ≤ ⌊H / h⌋₊ := fun τ hτ => by
    obtain ⟨n, hre, him⟩ := hS τ hτ τ₀ hτ₀
    have hn0 : 0 ≤ (n : ℝ) := by
      have := hmin τ hτ
      by_contra hn
      push Not at hn
      nlinarith
    have hn0' : 0 ≤ n := by exact_mod_cast hn0
    refine ⟨n.toNat, ?_, Nat.le_floor ?_⟩
    · have hc : ((n.toNat : ℕ) : ℝ) = n := by exact_mod_cast Int.toNat_of_nonneg hn0'
      apply Complex.ext <;> simp [hc, hre]; linarith
    · have hc : ((n.toNat : ℕ) : ℝ) = n := by exact_mod_cast Int.toNat_of_nonneg hn0'
      rw [hc, le_div_iff₀ hh]
      linarith [(hwin τ hτ).2, (hwin τ₀ hτ₀).1]
  choose! k hk using key
  have hinj : Set.InjOn k S := fun τ hτ τ' hτ' e => by rw [(hk τ hτ).1, (hk τ' hτ').1, e]
  calc S.card = (S.image k).card := (card_image_of_injOn hinj).symm
    _ ≤ (range (⌊H / h⌋₊ + 1)).card := card_le_card fun m hm => by
        obtain ⟨τ, hτ, rfl⟩ := mem_image.mp hm
        exact mem_range.mpr (Nat.lt_succ_of_le (hk τ hτ).2)
    _ = _ := card_range _

/-- **The window law.** In an ordinate window of length `H`, each value `p^{τ−½}` is shared by at
most `⌊Hℓ/2π⌋ + 1` zeros. -/
theorem card_le_mul_card_image_frobEig {ℓ : ℝ} (hℓ : 0 < ℓ) {S : Finset ℂ} {a H : ℝ}
    (hwin : ∀ τ ∈ S, a ≤ τ.im ∧ τ.im ≤ a + H) :
    S.card ≤ (⌊H * ℓ / (2 * π)⌋₊ + 1) * (S.image (frobEig ℓ)).card := by
  classical
  refine card_le_mul_card_image S _ fun b _ => ?_
  have hh : 0 < 2 * π / ℓ := by positivity
  have := card_le_of_im_sub_mem_lattice (S := S.filter fun τ => frobEig ℓ τ = b) hh
    (fun τ hτ τ' hτ' => re_eq_and_im_sub_eq_of_frobEig_eq hℓ
      (((mem_filter.mp hτ).2).trans ((mem_filter.mp hτ').2).symm))
    fun τ hτ => hwin τ (mem_filter.mp hτ).1
  rwa [div_div_eq_mul_div] at this

/-- **One prime sees a fixed fraction of the right zeros in every window.** -/
theorem card_le_mul_iSup_negIndex_towerKernel {p : ℕ} (hp : p.Prime) {S : Finset ℂ}
    (hS : (S : Set ℂ) ⊆ rightZeros zetaZeroConfig) {a H : ℝ}
    (hwin : ∀ τ ∈ S, a ≤ τ.im ∧ τ.im ≤ a + H) :
    (S.card : ℕ∞) ≤ ((⌊H * Real.log p / (2 * π)⌋₊ + 1 : ℕ) : ℕ∞) *
      ⨆ (g : ℝ → ℂ) (_ : ContDiff ℝ 2 g ∧ HasCompactSupport g),
        negIndex (towerKernel (fun n => (ArithmeticFunction.vonMangoldt n : ℝ)) g (Real.log p)) := by
  classical
  rw [iSup_negIndex_towerKernel_eq_outerEig hp]
  have hℓ : 0 < Real.log p := Real.log_pos (by exact_mod_cast hp.one_lt)
  have himg : ((S.image (frobEig (Real.log p)) : Finset ℂ).card : ℕ∞) ≤
      (outerEig zetaZeroConfig (Real.log p)).encard := by
    rw [← Set.encard_coe_eq_coe_finsetCard, coe_image]
    exact Set.encard_le_encard (Set.image_mono hS)
  calc (S.card : ℕ∞)
      ≤ (((⌊H * Real.log p / (2 * π)⌋₊ + 1) * (S.image (frobEig (Real.log p))).card : ℕ) : ℕ∞) :=
        Nat.cast_le.mpr (card_le_mul_card_image_frobEig hℓ hwin)
    _ ≤ _ := by
        push_cast
        exact mul_le_mul_right (by exact_mod_cast himg) _

/-- **Nyquist.** In an ordinate window of length below `2π/log p`, the tower of `p` sees every right
zero of `ζ`. -/
theorem card_le_iSup_negIndex_towerKernel_of_window {p : ℕ} (hp : p.Prime) {S : Finset ℂ}
    (hS : (S : Set ℂ) ⊆ rightZeros zetaZeroConfig) {a H : ℝ} (hH : H * Real.log p < 2 * π)
    (hwin : ∀ τ ∈ S, a ≤ τ.im ∧ τ.im ≤ a + H) :
    (S.card : ℕ∞) ≤ ⨆ (g : ℝ → ℂ) (_ : ContDiff ℝ 2 g ∧ HasCompactSupport g),
        negIndex (towerKernel (fun n => (ArithmeticFunction.vonMangoldt n : ℝ)) g (Real.log p)) := by
  have h := card_le_mul_iSup_negIndex_towerKernel hp hS hwin
  rwa [Nat.floor_eq_zero.mpr ((div_lt_one (by positivity)).mpr hH), zero_add, Nat.cast_one,
    one_mul] at h

end GaloisForLFunctions.HeckeKreinToeplitz
