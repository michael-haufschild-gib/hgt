import GaloisForLFunctions.RHTower.Sieve.GuthMaynardKeyPropTraceBound
import GaloisForLFunctions.RHTower.Sieve.GuthMaynardKeyPropExponentAlgebra
import GaloisForLFunctions.RHTower.Sieve.GuthMaynardTheoremOneOneFromKeyProp

/-!
# Guth–Maynard Proposition 3.1 from the bounds for `S₂` and `S₃`

`keyProp_of_S_bounds`: for a smooth bump `w` (`0 ≤ w ≤ 1`, support `[1,2]`, `w = 1` on
`[6/5, 9/5]`), Proposition 3.1 (`KeyPropBound w`) follows from

* Proposition 6.1 with `j = 4` and some `k ≥ 2` (`PropSixOneBound w 4 k`; the paper's choice is
  `j = k = 4`): `|S₂| ⪅ N²|W|² + TN|W|^{2−1/j} + N²|W|^{2−3/(4k)}T^{1/(2k)}`;
* Proposition 11.2 (`PropElevenTwoBound w`):
  `|S₃| ⪅ T²|W|^{3/2} + T|W|N^{3−2σ} + T|W|²N^{3/2−σ} + T^{9/8}|W|^{29/16}N^{3/2−σ}` for `N ≥ T^{3/4}`.

Everything else is unconditional: Propositions 4.6 and 5.1 and the expansion (5.5) for `ζ`
(`card_cube_mul_le_of_trace`), the translation of the interval `[T₀, T₀ + T]` to `[0, T]`
(`smoothedDyadicPoly_add`), and the exponent algebra of §12 (`le_keyBound_of_cubic`, `j = 4`,
`k ≥ 2`, `T = N^{6/5}`).  `cglStandardBump` is an explicit admissible bump (a mathlib `ContDiffBump` centred at
`3/2` with radii `3/10`, `1/2`), so `guthMaynardLargeValuesBound_of_S_bounds` gives Theorem 1.1 from
the two inputs.
-/

set_option autoImplicit false

open Finset Complex

namespace RHTower.GuthMaynard

open RHTower.Sieve

noncomputable section

/-! ### The two inputs -/

/-- **Guth–Maynard, Proposition 6.1** (`prpstn:S2`) with exponents `j, k ≥ 1` (`j = k` in the paper):
for `W` `T^ε`-separated in `[0, T]`, `T ≥ 2`, `1 ≤ N ≤ T`:
`|S₂| ≤ C T^ε (N²|W|² + T N |W|^{2−1/j} + N² |W|^{2−3/(4k)} T^{1/(2k)})`. -/
def PropSixOneBound (w : CGLRealSmoothBump) (j k : ℕ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 ≤ C ∧ ∀ (T N : ℝ) (W : Finset ℝ), 2 ≤ T → 1 ≤ N → N ≤ T →
    (∀ t ∈ W, t ∈ Set.Icc 0 T) → IsSeparated (T ^ ε) W →
    ‖gmS2 w N W‖ ≤ C * T ^ ε * ((W.card : ℝ) ^ (2 : ℝ) * N ^ (2 : ℝ) +
      T * N * (W.card : ℝ) ^ (2 - 1 / (j : ℝ)) +
      N ^ (2 : ℝ) * (W.card : ℝ) ^ (2 - 3 / (4 * (k : ℝ))) * T ^ (1 / (2 * (k : ℝ))))

/-- **Guth–Maynard, Proposition 11.2** (`prpstn:S3`): for `T ≥ 2`, `T^{3/4} ≤ N ≤ T`,
`|b_n| ≤ 1` and `W` `T^ε`-separated in `[0, T]` with `|Σ_{N<n≤2N} b_n n^{it}| ≥ N^σ` on `W`:
`|S₃| ≤ C T^ε (T²|W|^{3/2} + T|W|N^{3−2σ} + T|W|²N^{3/2−σ} + T^{9/8}|W|^{29/16}N^{3/2−σ})`. -/
def PropElevenTwoBound (w : CGLRealSmoothBump) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 ≤ C ∧ ∀ (N : ℕ) (σ T : ℝ) (b : ℕ → ℂ) (W : Finset ℝ),
    2 ≤ T → T ^ (3 / 4 : ℝ) ≤ N → (N : ℝ) ≤ T → (∀ n, ‖b n‖ ≤ 1) →
    (∀ t ∈ W, t ∈ Set.Icc 0 T) → IsSeparated (T ^ ε) W →
    (∀ t ∈ W, (N : ℝ) ^ σ ≤ ‖dyadicPoly N b t‖) →
    ‖allNonzeroCubicSum w.toCGLSmoothBump W N‖ ≤ C * T ^ ε *
      (T ^ (2 : ℝ) * (W.card : ℝ) ^ (3 / 2 : ℝ) + T * W.card * (N : ℝ) ^ (3 - 2 * σ) +
        T * (W.card : ℝ) ^ (2 : ℝ) * (N : ℝ) ^ (3 / 2 - σ) +
        T ^ (9 / 8 : ℝ) * (W.card : ℝ) ^ (29 / 16 : ℝ) * (N : ℝ) ^ (3 / 2 - σ))

/-! ### Translation and the trivial range -/

/-- Shifting `t` by `T₀` twists the coefficients by `n^{iT₀}`. -/
theorem smoothedDyadicPoly_add (w : CGLSmoothBump) (N : ℕ) (b : ℕ → ℂ) (s T₀ : ℝ) :
    smoothedDyadicPoly w N b (s + T₀) =
      smoothedDyadicPoly w N (fun n => b n * Complex.exp (Complex.I * T₀ * Real.log n)) s := by
  unfold smoothedDyadicPoly
  refine sum_congr rfl fun n _ => ?_
  have e : Complex.exp (Complex.I * ((s + T₀ : ℝ) : ℂ) * Real.log n) =
      Complex.exp (Complex.I * T₀ * Real.log n) * Complex.exp (Complex.I * s * Real.log n) := by
    rw [← Complex.exp_add]; congr 1; push_cast; ring
  rw [e]
  ring

/-- The smoothed polynomial of a unit bump is the plain polynomial of `w(n/N) b_n`. -/
theorem smoothedDyadicPoly_eq_dyadicPoly (w : CGLSmoothBump) (N : ℕ) (b : ℕ → ℂ) (t : ℝ) :
    smoothedDyadicPoly w N b t = dyadicPoly N (fun n => w.value ((n : ℝ) / N) * b n) t := rfl

/-- **Proposition 3.1 for `N ≤ 4`**: `|W| ≤ 17 ≤ 32 T N^{(12−20σ)/5}` for `σ ≤ 4/5`. -/
theorem card_le_of_small_keyLength {N : ℕ} (hN : 1 ≤ N) (hN4 : N ≤ 4) {σ T₀ ε : ℝ} (hε : 0 < ε)
    (hσ : σ ≤ 8 / 10) {W : Finset ℝ} (hW : ∀ t ∈ W, T₀ ≤ t ∧ t ≤ T₀ + (N : ℝ) ^ (6 / 5 : ℝ))
    (hsep : IsSeparated (((N : ℝ) ^ (6 / 5 : ℝ)) ^ ε) W) :
    (W.card : ℝ) ≤ 32 * ((N : ℝ) ^ (6 / 5 : ℝ)) ^ ε *
      ((N : ℝ) ^ (6 / 5 : ℝ) * (N : ℝ) ^ ((12 - 20 * σ) / 5)) := by
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hN0 : (0 : ℝ) < N := by linarith
  have hT1 : 1 ≤ (N : ℝ) ^ (6 / 5 : ℝ) := Real.one_le_rpow hN1 (by norm_num)
  have hTε : 1 ≤ ((N : ℝ) ^ (6 / 5 : ℝ)) ^ ε := Real.one_le_rpow hT1 hε.le
  -- `T ≤ 16`
  have hT16 : (N : ℝ) ^ (6 / 5 : ℝ) ≤ 16 := by
    have h4 : (N : ℝ) ≤ 4 := by exact_mod_cast hN4
    calc (N : ℝ) ^ (6 / 5 : ℝ) ≤ (N : ℝ) ^ ((2 : ℕ) : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le hN1 (by norm_num)
      _ = (N : ℝ) ^ 2 := Real.rpow_natCast _ 2
      _ ≤ 16 := by nlinarith
  have hcard : (W.card : ℝ) ≤ 17 := by
    have h := card_le_of_separated (u := id) one_pos (by linarith)
      (fun a ha b hb hab => hTε.trans (hsep a ha b hb hab)) hW
    simp only [div_one] at h
    linarith
  -- `T N^{(12−20σ)/5} ≥ N^{2/5} ≥ 1`
  have hprod : 1 ≤ (N : ℝ) ^ (6 / 5 : ℝ) * (N : ℝ) ^ ((12 - 20 * σ) / 5) := by
    rw [← Real.rpow_add hN0]
    exact Real.one_le_rpow hN1 (by linarith)
  have hx : (0 : ℝ) ≤ ((N : ℝ) ^ (6 / 5 : ℝ)) ^ ε := by linarith
  nlinarith [mul_le_mul hTε hprod zero_le_one hx]

/-! ### Proposition 3.1 -/

/-- **Guth–Maynard, Proposition 3.1, from Propositions 6.1 (`j = 4`, `k ≥ 2`) and 11.2.** -/
theorem keyProp_of_S_bounds (w : CGLUnitRealSmoothBump) {k : ℕ} (hk : 2 ≤ k)
    (hS2 : PropSixOneBound w.toCGLRealSmoothBump 4 k)
    (hS3 : PropElevenTwoBound w.toCGLRealSmoothBump) :
    KeyPropBound w.toCGLSmoothBump := by
  classical
  intro ε hε
  obtain ⟨C₀, hC₀, h0⟩ := card_cube_mul_le_of_trace w hε
  obtain ⟨C₂, hC₂, h2⟩ := hS2 ε hε
  obtain ⟨C₃, hC₃, h3⟩ := hS3 ε hε
  obtain ⟨D, hD⟩ : ∃ D : ℝ, D = C₀ * (2 + C₂ + C₃) := ⟨_, rfl⟩
  have hD0 : 0 ≤ D := by rw [hD]; positivity
  refine ⟨8 * max 1 (8 * D) + 32, by positivity, ?_⟩
  intro N σ T₀ b W hN hσ1 hσ2 hb hW hsep hbig
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hN0 : (0 : ℝ) < N := by linarith
  obtain ⟨T, hT⟩ : ∃ T : ℝ, T = (N : ℝ) ^ (6 / 5 : ℝ) := ⟨_, rfl⟩
  have hT1 : 1 ≤ T := hT ▸ Real.one_le_rpow hN1 (by norm_num)
  have hTε : 1 ≤ T ^ ε := Real.one_le_rpow hT1 hε.le
  have hkey0 : 0 ≤ (N : ℝ) ^ (6 / 5 : ℝ) * (N : ℝ) ^ ((12 - 20 * σ) / 5) := by positivity
  rcases le_or_gt N 4 with hN4 | hN5
  · have h := card_le_of_small_keyLength hN hN4 hε hσ2 hW hsep
    rw [← hT] at h ⊢
    have : 0 ≤ 8 * max 1 (8 * D) * T ^ ε * ((N : ℝ) ^ (6 / 5 : ℝ) * (N : ℝ) ^ ((12 - 20 * σ) / 5)) := by
      positivity
    nlinarith
  -- translate `W` to `[0, T]`
  have hN5' : (5 : ℝ) ≤ N := by exact_mod_cast hN5
  have hNT : (N : ℝ) ≤ T := by
    rw [hT]
    calc (N : ℝ) = (N : ℝ) ^ (1 : ℝ) := (Real.rpow_one _).symm
      _ ≤ (N : ℝ) ^ (6 / 5 : ℝ) := Real.rpow_le_rpow_of_exponent_le hN1 (by norm_num)
  obtain ⟨W', hW'⟩ : ∃ W' : Finset ℝ, W' = W.image fun t => t - T₀ := ⟨_, rfl⟩
  have hcardW : W'.card = W.card := by
    rw [hW']; exact Finset.card_image_of_injective _ fun a b h => by simpa using h
  have hW'mem : ∀ t ∈ W', t ∈ Set.Icc 0 T := fun t ht => by
    rw [hW'] at ht
    obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp ht
    have := hW s hs
    rw [← hT] at this
    exact ⟨by linarith, by linarith⟩
  have hsep' : IsSeparated (T ^ ε) W' := fun a ha c hc hac => by
    rw [hW'] at ha hc
    obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp ha
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hc
    have hsu : s ≠ u := fun h => hac (by rw [h])
    rw [show s - T₀ - (u - T₀) = s - u by ring, hT]
    exact hsep s hs u hu hsu
  obtain ⟨b', hb'⟩ : ∃ b' : ℕ → ℂ,
      b' = fun n => b n * Complex.exp (Complex.I * T₀ * Real.log n) := ⟨_, rfl⟩
  have hb'1 : ∀ n, ‖b' n‖ ≤ 1 := fun n => by
    rw [hb', norm_mul, norm_exp_mul_log, mul_one]; exact hb n
  have hbig' : ∀ t ∈ W', (N : ℝ) ^ σ ≤ ‖smoothedDyadicPoly w.toCGLSmoothBump N b' t‖ := by
    intro t ht
    rw [hW'] at ht
    obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp ht
    rw [hb', ← smoothedDyadicPoly_add, sub_add_cancel]
    exact hbig s hs
  -- Propositions 4.6 + 5.1, then 6.1 and 11.2
  have hcube := h0 N σ T b' W' hN (by linarith) hNT hb'1 hW'mem hsep' hbig'
  have hS2' := h2 T N W' (by linarith) hN1 hNT hW'mem hsep'
  have hT34 : T ^ (3 / 4 : ℝ) ≤ N := by
    rw [hT, ← Real.rpow_mul hN0.le]
    calc (N : ℝ) ^ ((6 / 5 : ℝ) * (3 / 4)) ≤ (N : ℝ) ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le hN1 (by norm_num)
      _ = N := Real.rpow_one _
  have hb''1 : ∀ n : ℕ, ‖w.toCGLSmoothBump.value ((n : ℝ) / N) * b' n‖ ≤ 1 := fun n => by
    rw [norm_mul]
    exact mul_le_one₀ (w.norm_le_one _) (norm_nonneg _) (hb'1 n)
  have hS3' := h3 N σ T (fun n : ℕ => w.toCGLSmoothBump.value ((n : ℝ) / N) * b' n) W' (by linarith)
    hT34 hNT hb''1 hW'mem hsep' (fun t ht => by
      rw [← smoothedDyadicPoly_eq_dyadicPoly]; exact hbig' t ht)
  rw [hcardW] at hcube hS2' hS3'
  -- the cubic inequality in the shape of `cubicRHS`
  obtain ⟨x, hx⟩ : ∃ x : ℝ, x = W.card := ⟨_, rfl⟩
  rw [← hx] at hcube hS2' hS3'
  have hx0 : 0 ≤ x := hx ▸ Nat.cast_nonneg _
  have hxx : x ≤ x ^ (2 : ℝ) * (N : ℝ) ^ (2 : ℝ) := by
    rw [Real.rpow_two, Real.rpow_two]
    rcases Nat.eq_zero_or_pos W.card with h0' | hpos
    · rw [hx, h0']; simp
    · have hx1 : 1 ≤ x := by rw [hx]; exact_mod_cast hpos
      nlinarith [mul_le_mul hx1 hx1 zero_le_one hx0, one_le_pow₀ (n := 2) hN1]
  have hc1 : (N : ℝ) ^ 3 ≤ T ^ ε * (N : ℝ) ^ (3 : ℝ) := by
    rw [show (N : ℝ) ^ (3 : ℝ) = (N : ℝ) ^ 3 from Real.rpow_natCast _ 3]
    exact le_mul_of_one_le_left (by positivity) hTε
  -- the four groups of terms of `cubicRHS`
  have t1 := Real.rpow_nonneg hN0.le (3 : ℝ)
  have t2 : 0 ≤ x ^ (2 : ℝ) * (N : ℝ) ^ (2 : ℝ) := by positivity
  have t3 : 0 ≤ T * N * x ^ (2 - 1 / ((4 : ℕ) : ℝ)) := by positivity
  have t4 : 0 ≤ (N : ℝ) ^ (2 : ℝ) * x ^ (2 - 3 / (4 * (k : ℝ))) *
      T ^ (1 / (2 * (k : ℝ))) := by positivity
  have t5 : 0 ≤ T ^ (2 : ℝ) * x ^ (3 / 2 : ℝ) := by positivity
  have t6 : 0 ≤ T * x * (N : ℝ) ^ (3 - 2 * σ) := by positivity
  have t7 : 0 ≤ T * x ^ (2 : ℝ) * (N : ℝ) ^ (3 / 2 - σ) := by positivity
  have t8 : 0 ≤ T ^ (9 / 8 : ℝ) * x ^ (29 / 16 : ℝ) * (N : ℝ) ^ (3 / 2 - σ) := by positivity
  obtain ⟨Q, hQ⟩ : ∃ Q, Q = cubicRHS x N T σ 4 k := ⟨_, rfl⟩
  have hQ1 : (N : ℝ) ^ (3 : ℝ) ≤ Q := by rw [hQ]; unfold cubicRHS; linarith
  have hQ2 : x ^ (2 : ℝ) * (N : ℝ) ^ (2 : ℝ) ≤ Q := by rw [hQ]; unfold cubicRHS; linarith
  have hQS2 : x ^ (2 : ℝ) * (N : ℝ) ^ (2 : ℝ) + T * N * x ^ (2 - 1 / ((4 : ℕ) : ℝ)) +
      (N : ℝ) ^ (2 : ℝ) * x ^ (2 - 3 / (4 * (k : ℝ))) * T ^ (1 / (2 * (k : ℝ))) ≤ Q := by
    rw [hQ]; unfold cubicRHS; linarith
  have hQS3 : T ^ (2 : ℝ) * x ^ (3 / 2 : ℝ) + T * x * (N : ℝ) ^ (3 - 2 * σ) +
      T * x ^ (2 : ℝ) * (N : ℝ) ^ (3 / 2 - σ) +
      T ^ (9 / 8 : ℝ) * x ^ (29 / 16 : ℝ) * (N : ℝ) ^ (3 / 2 - σ) ≤ Q := by
    rw [hQ]; unfold cubicRHS; linarith
  have hTε0 : 0 ≤ T ^ ε := by linarith
  have hS2Q : ‖gmS2 w.toCGLRealSmoothBump N W'‖ ≤ C₂ * (T ^ ε * Q) := by
    refine hS2'.trans ?_
    rw [mul_assoc]; exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hQS2 hTε0) hC₂
  have hS3Q : ‖allNonzeroCubicSum w.toCGLSmoothBump W' N‖ ≤ C₃ * (T ^ ε * Q) := by
    refine hS3'.trans ?_
    rw [mul_assoc]; exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hQS3 hTε0) hC₃
  have hN3Q : (N : ℝ) ^ 3 ≤ T ^ ε * Q := hc1.trans (mul_le_mul_of_nonneg_left hQ1 hTε0)
  have hxQ : x ≤ T ^ ε * Q := hxx.trans ((le_mul_of_one_le_left t2 hTε).trans
    (mul_le_mul_of_nonneg_left hQ2 hTε0))
  have hrhs : C₀ * ((N : ℝ) ^ 3 + ‖gmS2 w.toCGLRealSmoothBump N W'‖ +
      ‖allNonzeroCubicSum w.toCGLSmoothBump W' N‖ + x) ≤ D * T ^ ε * cubicRHS x N T σ 4 k := by
    rw [← hQ, hD]
    calc C₀ * ((N : ℝ) ^ 3 + ‖gmS2 w.toCGLRealSmoothBump N W'‖ +
          ‖allNonzeroCubicSum w.toCGLSmoothBump W' N‖ + x)
        ≤ C₀ * (T ^ ε * Q + C₂ * (T ^ ε * Q) + C₃ * (T ^ ε * Q) + T ^ ε * Q) := by gcongr
      _ = C₀ * (2 + C₂ + C₃) * T ^ ε * Q := by ring
  have hcube' : x ^ (3 : ℝ) * (N : ℝ) ^ (6 * σ - 3) ≤ (D * T ^ ε) * cubicRHS x N T σ 4 k := by
    rw [show x ^ (3 : ℝ) = x ^ 3 from Real.rpow_natCast x 3]
    exact hcube.trans hrhs
  rw [hT] at hcube'
  have hfinal := le_keyBound_of_cubic hx0 hN1 hσ1 hσ2 hk (by positivity) hcube'
  rw [← hT] at hfinal
  -- `max(1, 8 D T^ε) ≤ max(1, 8D) T^ε`
  have hmax : max 1 (8 * (D * T ^ ε)) ≤ max 1 (8 * D) * T ^ ε := by
    refine max_le (one_le_mul_of_one_le_of_one_le (le_max_left _ _) hTε) ?_
    rw [← mul_assoc]
    exact mul_le_mul_of_nonneg_right (le_max_right _ _) hTε0
  rw [← hx, ← hT]
  calc x ≤ 8 * max 1 (8 * (D * T ^ ε)) * (T * (N : ℝ) ^ ((12 - 20 * σ) / 5)) :=
        hfinal
    _ ≤ 8 * (max 1 (8 * D) * T ^ ε) * (T * (N : ℝ) ^ ((12 - 20 * σ) / 5)) := by
        gcongr
    _ = 8 * max 1 (8 * D) * T ^ ε * (T * (N : ℝ) ^ ((12 - 20 * σ) / 5)) := by
        ring
    _ ≤ (8 * max 1 (8 * D) + 32) * T ^ ε *
          (T * (N : ℝ) ^ ((12 - 20 * σ) / 5)) := by
        gcongr
        linarith

/-! ### An admissible bump and Theorem 1.1 -/

/-- The mathlib bump centred at `3/2` with radii `3/10` and `1/2`. -/
def standardContDiffBump : ContDiffBump (3 / 2 : ℝ) := ⟨3 / 10, 1 / 2, by norm_num, by norm_num⟩

/-- **An admissible Guth–Maynard bump**: smooth, real, `0 ≤ w ≤ 1`, supported in `[1, 2]`,
`w = 1` on `[6/5, 9/5]`. -/
def cglStandardBump : CGLUnitRealSmoothBump where
  value x := ((standardContDiffBump : ℝ → ℝ) x : ℂ)
  compactSupport := standardContDiffBump.hasCompactSupport.comp_left (g := Complex.ofReal)
    Complex.ofReal_zero
  smooth := Complex.ofRealCLM.contDiff.comp standardContDiffBump.contDiff
  outside_support x hx := by
    have hns : x ∉ Function.support (standardContDiffBump : ℝ → ℝ) := by
      rw [standardContDiffBump.support_eq, Real.ball_eq_Ioo]
      intro h
      simp only [standardContDiffBump, Set.mem_Ioo] at h
      exact hx ⟨by linarith [h.1], by linarith [h.2]⟩
    rw [Function.notMem_support.mp hns, Complex.ofReal_zero]
  plateau x hx := by
    have hmem : x ∈ Metric.closedBall (3 / 2 : ℝ) standardContDiffBump.rIn := by
      rw [Real.closedBall_eq_Icc]
      simp only [standardContDiffBump]
      exact ⟨by linarith [hx.1], by linarith [hx.2]⟩
    rw [standardContDiffBump.one_of_mem_closedBall hmem, Complex.ofReal_one]
  imaginary_zero x := Complex.ofReal_im _
  nonnegative x := by rw [Complex.ofReal_re]; exact standardContDiffBump.nonneg
  norm_le_one x := by
    rw [Complex.norm_real, Real.norm_of_nonneg standardContDiffBump.nonneg]
    exact standardContDiffBump.le_one

/-- **Theorem 1.1 from Propositions 6.1 (`j = 4`, `k ≥ 2`) and 11.2** for the standard bump. -/
theorem guthMaynardLargeValuesBound_of_S_bounds {k : ℕ} (hk : 2 ≤ k)
    (hS2 : PropSixOneBound cglStandardBump.toCGLRealSmoothBump 4 k)
    (hS3 : PropElevenTwoBound cglStandardBump.toCGLRealSmoothBump) :
    GuthMaynardLargeValuesBound :=
  guthMaynardLargeValuesBound_of_keyProp (keyProp_of_S_bounds cglStandardBump hk hS2 hS3)

end

end RHTower.GuthMaynard
