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

/-! ### (12.1) as a statement, and its proof from the `S`-bounds -/

/-- **Guth–Maynard (12.1)** (`eq:FullBound`) with exponents `j, k` (`j = k` in the paper): for
`T ≥ 2`, `T^{3/4} ≤ N ≤ T`, `|b_n| ≤ 1` and a `T^ε`-separated set `W ⊂ [T₀, T₀ + T]` with
`|Σ_{N<n≤2N} w(n/N) b_n n^{it}| ≥ N^σ` on `W`: `|W| ≤ C T^ε · fullBound N T σ j k`. -/
def FullBoundStatement (w : CGLSmoothBump) (j k : ℕ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 ≤ C ∧ ∀ (N : ℕ) (σ T T₀ : ℝ) (b : ℕ → ℂ) (W : Finset ℝ),
    2 ≤ T → T ^ (3 / 4 : ℝ) ≤ N → (N : ℝ) ≤ T → (∀ n, ‖b n‖ ≤ 1) →
    (∀ t ∈ W, T₀ ≤ t ∧ t ≤ T₀ + T) → IsSeparated (T ^ ε) W →
    (∀ t ∈ W, (N : ℝ) ^ σ ≤ ‖smoothedDyadicPoly w N b t‖) →
    (W.card : ℝ) ≤ C * T ^ ε * fullBound N T σ j k

/-- Translating `W ⊂ [T₀, T₀ + T]` to `[0, T]` keeps its size and separation; the large values
pass to the coefficients `b_n n^{iT₀}`. -/
theorem exists_translate_largeValues (w : CGLSmoothBump) {N : ℕ} {b : ℕ → ℂ} {W : Finset ℝ}
    {T₀ T δ σ : ℝ} (hW : ∀ t ∈ W, T₀ ≤ t ∧ t ≤ T₀ + T) (hsep : IsSeparated δ W)
    (hbig : ∀ t ∈ W, (N : ℝ) ^ σ ≤ ‖smoothedDyadicPoly w N b t‖) :
    ∃ (W' : Finset ℝ) (b' : ℕ → ℂ), W'.card = W.card ∧ (∀ t ∈ W', t ∈ Set.Icc 0 T) ∧
      IsSeparated δ W' ∧ (∀ n, ‖b' n‖ = ‖b n‖) ∧
      ∀ t ∈ W', (N : ℝ) ^ σ ≤ ‖smoothedDyadicPoly w N b' t‖ := by
  classical
  refine ⟨W.image fun t => t - T₀, fun n => b n * Complex.exp (Complex.I * T₀ * Real.log n),
    Finset.card_image_of_injective _ fun a c h => by simpa using h, ?_, ?_, ?_, ?_⟩
  · intro t ht
    obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp ht
    have := hW s hs
    exact ⟨by linarith, by linarith⟩
  · intro a ha c hc hac
    obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp ha
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hc
    have hsu : s ≠ u := fun h => hac (by rw [h])
    rw [show s - T₀ - (u - T₀) = s - u by ring]
    exact hsep s hs u hu hsu
  · intro n; rw [norm_mul, norm_exp_mul_log, mul_one]
  · intro t ht
    obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp ht
    rw [← smoothedDyadicPoly_add, sub_add_cancel]
    exact hbig s hs

/-- **(12.1) on `[0, T]`, `T ≥ 5`, from Propositions 6.1 and 11.2.**  Propositions 4.6, 5.1 and
(5.5) (`card_cube_mul_le_of_trace`) give `|W|³N^{6σ−3} ≤ C₀(N³ + |S₂| + |S₃| + |W|)`; the two
inputs turn the right-hand side into `D T^ε · cubicRHS`, and `le_fullBound_of_cubic` rearranges. -/
theorem card_le_fullBound_of_S_bounds (w : CGLUnitRealSmoothBump) {j k : ℕ} (hj : 1 ≤ j)
    (hk : 1 ≤ k) (hS2 : PropSixOneBound w.toCGLRealSmoothBump j k)
    (hS3 : PropElevenTwoBound w.toCGLRealSmoothBump) {ε : ℝ} (hε : 0 < ε) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (N : ℕ) (σ T : ℝ) (b : ℕ → ℂ) (W : Finset ℝ),
      5 ≤ T → T ^ (3 / 4 : ℝ) ≤ N → (N : ℝ) ≤ T → (∀ n, ‖b n‖ ≤ 1) →
      (∀ t ∈ W, t ∈ Set.Icc 0 T) → IsSeparated (T ^ ε) W →
      (∀ t ∈ W, (N : ℝ) ^ σ ≤ ‖smoothedDyadicPoly w.toCGLSmoothBump N b t‖) →
      (W.card : ℝ) ≤ K * T ^ ε * fullBound N T σ j k := by
  classical
  obtain ⟨C₀, hC₀, h0⟩ := card_cube_mul_le_of_trace w hε
  obtain ⟨C₂, hC₂, h2⟩ := hS2 ε hε
  obtain ⟨C₃, hC₃, h3⟩ := hS3 ε hε
  obtain ⟨D, hD⟩ : ∃ D : ℝ, D = C₀ * (2 + C₂ + C₃) := ⟨_, rfl⟩
  have hD0 : 0 ≤ D := by rw [hD]; positivity
  refine ⟨max 1 (8 * D), le_trans zero_le_one (le_max_left _ _), ?_⟩
  intro N σ T b W hT5 hT34 hNT hb hW hsep hbig
  have hT0 : 0 < T := by linarith
  have hT1 : 1 ≤ T := by linarith
  have hTε : 1 ≤ T ^ ε := Real.one_le_rpow hT1 hε.le
  have hTε0 : 0 ≤ T ^ ε := by linarith
  have hN1 : (1 : ℝ) ≤ N := (Real.one_le_rpow hT1 (by norm_num)).trans hT34
  have hN0 : (0 : ℝ) < N := by linarith
  have hN : 1 ≤ N := by exact_mod_cast hN1
  -- Propositions 4.6 + 5.1, then 6.1 and 11.2
  have hcube := h0 N σ T b W hN hT5 hNT hb hW hsep hbig
  have hS2' := h2 T N W (by linarith) hN1 hNT hW hsep
  have hb''1 : ∀ n : ℕ, ‖w.toCGLSmoothBump.value ((n : ℝ) / N) * b n‖ ≤ 1 := fun n => by
    rw [norm_mul]
    exact mul_le_one₀ (w.norm_le_one _) (norm_nonneg _) (hb n)
  have hS3' := h3 N σ T (fun n : ℕ => w.toCGLSmoothBump.value ((n : ℝ) / N) * b n) W (by linarith)
    hT34 hNT hb''1 hW hsep (fun t ht => by
      rw [← smoothedDyadicPoly_eq_dyadicPoly]; exact hbig t ht)
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
  have t1 := Real.rpow_nonneg hN0.le (3 : ℝ)
  have t2 : 0 ≤ x ^ (2 : ℝ) * (N : ℝ) ^ (2 : ℝ) := by positivity
  have t3 : 0 ≤ T * N * x ^ (2 - 1 / (j : ℝ)) := by positivity
  have t4 : 0 ≤ (N : ℝ) ^ (2 : ℝ) * x ^ (2 - 3 / (4 * (k : ℝ))) * T ^ (1 / (2 * (k : ℝ))) := by
    positivity
  have t5 : 0 ≤ T ^ (2 : ℝ) * x ^ (3 / 2 : ℝ) := by positivity
  have t6 : 0 ≤ T * x * (N : ℝ) ^ (3 - 2 * σ) := by positivity
  have t7 : 0 ≤ T * x ^ (2 : ℝ) * (N : ℝ) ^ (3 / 2 - σ) := by positivity
  have t8 : 0 ≤ T ^ (9 / 8 : ℝ) * x ^ (29 / 16 : ℝ) * (N : ℝ) ^ (3 / 2 - σ) := by positivity
  obtain ⟨Q, hQ⟩ : ∃ Q, Q = cubicRHS x N T σ j k := ⟨_, rfl⟩
  have hQ1 : (N : ℝ) ^ (3 : ℝ) ≤ Q := by rw [hQ]; unfold cubicRHS; linarith
  have hQ2 : x ^ (2 : ℝ) * (N : ℝ) ^ (2 : ℝ) ≤ Q := by rw [hQ]; unfold cubicRHS; linarith
  have hQS2 : x ^ (2 : ℝ) * (N : ℝ) ^ (2 : ℝ) + T * N * x ^ (2 - 1 / (j : ℝ)) +
      (N : ℝ) ^ (2 : ℝ) * x ^ (2 - 3 / (4 * (k : ℝ))) * T ^ (1 / (2 * (k : ℝ))) ≤ Q := by
    rw [hQ]; unfold cubicRHS; linarith
  have hQS3 : T ^ (2 : ℝ) * x ^ (3 / 2 : ℝ) + T * x * (N : ℝ) ^ (3 - 2 * σ) +
      T * x ^ (2 : ℝ) * (N : ℝ) ^ (3 / 2 - σ) +
      T ^ (9 / 8 : ℝ) * x ^ (29 / 16 : ℝ) * (N : ℝ) ^ (3 / 2 - σ) ≤ Q := by
    rw [hQ]; unfold cubicRHS; linarith
  have hS2Q : ‖gmS2 w.toCGLRealSmoothBump N W‖ ≤ C₂ * (T ^ ε * Q) := by
    refine hS2'.trans ?_
    rw [mul_assoc]; exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hQS2 hTε0) hC₂
  have hS3Q : ‖allNonzeroCubicSum w.toCGLSmoothBump W N‖ ≤ C₃ * (T ^ ε * Q) := by
    refine hS3'.trans ?_
    rw [mul_assoc]; exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hQS3 hTε0) hC₃
  have hN3Q : (N : ℝ) ^ 3 ≤ T ^ ε * Q := hc1.trans (mul_le_mul_of_nonneg_left hQ1 hTε0)
  have hxQ : x ≤ T ^ ε * Q := hxx.trans ((le_mul_of_one_le_left t2 hTε).trans
    (mul_le_mul_of_nonneg_left hQ2 hTε0))
  have hrhs : C₀ * ((N : ℝ) ^ 3 + ‖gmS2 w.toCGLRealSmoothBump N W‖ +
      ‖allNonzeroCubicSum w.toCGLSmoothBump W N‖ + x) ≤ D * T ^ ε * cubicRHS x N T σ j k := by
    rw [← hQ, hD]
    calc C₀ * ((N : ℝ) ^ 3 + ‖gmS2 w.toCGLRealSmoothBump N W‖ +
          ‖allNonzeroCubicSum w.toCGLSmoothBump W N‖ + x)
        ≤ C₀ * (T ^ ε * Q + C₂ * (T ^ ε * Q) + C₃ * (T ^ ε * Q) + T ^ ε * Q) := by gcongr
      _ = C₀ * (2 + C₂ + C₃) * T ^ ε * Q := by ring
  have hcube' : x ^ (3 : ℝ) * (N : ℝ) ^ (6 * σ - 3) ≤ (D * T ^ ε) * cubicRHS x N T σ j k := by
    rw [show x ^ (3 : ℝ) = x ^ 3 from Real.rpow_natCast x 3]
    exact hcube.trans hrhs
  have hfinal := le_fullBound_of_cubic hx0 hN0 hT0 hj hk (by positivity) hcube'
  -- `max(1, 8 D T^ε) ≤ max(1, 8D) T^ε`
  have hmax : max 1 (8 * (D * T ^ ε)) ≤ max 1 (8 * D) * T ^ ε := by
    refine max_le (one_le_mul_of_one_le_of_one_le (le_max_left _ _) hTε) ?_
    rw [← mul_assoc]
    exact mul_le_mul_of_nonneg_right (le_max_right _ _) hTε0
  have hF0 : 0 ≤ fullBound N T σ j k := by unfold fullBound; positivity
  rw [← hx]
  exact hfinal.trans (mul_le_mul_of_nonneg_right hmax hF0)

/-- `|D_N(t)| ≤ N` for a unit bump and `|b_n| ≤ 1`. -/
theorem norm_smoothedDyadicPoly_le (w : CGLUnitRealSmoothBump) {N : ℕ} {b : ℕ → ℂ}
    (hb : ∀ n, ‖b n‖ ≤ 1) (t : ℝ) : ‖smoothedDyadicPoly w.toCGLSmoothBump N b t‖ ≤ N := by
  rw [smoothedDyadicPoly_eq_dyadicPoly]
  exact norm_dyadicPoly_le (fun n => by
    rw [norm_mul]; exact mul_le_one₀ (w.norm_le_one _) (norm_nonneg _) (hb n)) t

/-- **(12.1) from Propositions 6.1 (exponents `j, k`) and 11.2.** -/
theorem fullBoundStatement_of_S_bounds (w : CGLUnitRealSmoothBump) {j k : ℕ} (hj : 1 ≤ j)
    (hk : 1 ≤ k) (hS2 : PropSixOneBound w.toCGLRealSmoothBump j k)
    (hS3 : PropElevenTwoBound w.toCGLRealSmoothBump) :
    FullBoundStatement w.toCGLSmoothBump j k := by
  classical
  intro ε hε
  obtain ⟨K, hK, hmain⟩ := card_le_fullBound_of_S_bounds w hj hk hS2 hS3 hε
  refine ⟨K + 6, by positivity, ?_⟩
  intro N σ T T₀ b W hT hT34 hNT hb hW hsep hbig
  have hT1 : 1 ≤ T := by linarith
  have hTε : 1 ≤ T ^ ε := Real.one_le_rpow hT1 hε.le
  have hN1 : (1 : ℝ) ≤ N := (Real.one_le_rpow hT1 (by norm_num)).trans hT34
  have hN0 : (0 : ℝ) < N := by linarith
  have hF0 : 0 ≤ fullBound N T σ j k := by unfold fullBound; positivity
  rcases le_or_gt 5 T with hT5 | hT5
  · obtain ⟨W', b', hcard, hW', hsep', hb', hbig'⟩ := exists_translate_largeValues _ hW hsep hbig
    have h := hmain N σ T b' W' hT5 hT34 hNT (fun n => (hb' n).trans_le (hb n)) hW' hsep' hbig'
    rw [hcard] at h
    refine h.trans ?_
    have : 0 ≤ T ^ ε * fullBound N T σ j k := by positivity
    nlinarith
  -- `T < 5`: `|W| ≤ T + 1 ≤ 6` and `fullBound ≥ N^{2−2σ} ≥ 1`
  rcases W.eq_empty_or_nonempty with he | ⟨t₀, ht₀⟩
  · rw [he, card_empty, Nat.cast_zero]; positivity
  have hcard : (W.card : ℝ) ≤ 6 := by
    have h := card_le_of_separated (u := id) one_pos (by linarith)
      (fun a ha c hc hac => hTε.trans (hsep a ha c hc hac)) hW
    simp only [div_one] at h
    linarith
  -- `N ≥ 2`, so `σ ≤ 1`
  have hN2 : (1 : ℝ) < N := by
    refine lt_of_lt_of_le ?_ hT34
    exact Real.one_lt_rpow (by linarith) (by norm_num)
  have hσ : σ ≤ 1 := by
    have h := (hbig t₀ ht₀).trans (norm_smoothedDyadicPoly_le w hb t₀)
    rw [← Real.rpow_le_rpow_left_iff hN2, Real.rpow_one]
    exact h
  have hF1 : 1 ≤ fullBound N T σ j k := by
    have h1 : 1 ≤ (N : ℝ) ^ (2 - 2 * σ) := Real.one_le_rpow hN1 (by linarith)
    unfold fullBound
    have := Real.rpow_nonneg hN0.le (5 - 6 * σ)
    have : 0 ≤ T ^ ((j : ℝ) / (j + 1)) * (N : ℝ) ^ ((4 - 6 * σ) * ((j : ℝ) / (j + 1))) := by
      positivity
    have : 0 ≤ (N : ℝ) ^ ((5 - 6 * σ) * (4 * (k : ℝ) / (4 * k + 3))) *
      T ^ (2 / (4 * (k : ℝ) + 3)) := by positivity
    have : 0 ≤ T ^ (4 / 3 : ℝ) * (N : ℝ) ^ (2 - 4 * σ) := by positivity
    have : 0 ≤ T ^ (1 / 2 : ℝ) * (N : ℝ) ^ (3 - 4 * σ) := by positivity
    have : 0 ≤ T * (N : ℝ) ^ (9 / 2 - 7 * σ) := by positivity
    have : 0 ≤ T ^ (18 / 19 : ℝ) * (N : ℝ) ^ (72 / 19 - 112 * σ / 19) := by positivity
    linarith
  have h6 : (6 : ℝ) ≤ (K + 6) * T ^ ε * fullBound N T σ j k := by
    have : (1 : ℝ) ≤ T ^ ε * fullBound N T σ j k := one_le_mul_of_one_le_of_one_le hTε hF1
    nlinarith
  linarith

/-! ### Proposition 3.1 -/

/-- **Guth–Maynard, Proposition 3.1, from (12.1)** with `j = 4`, `k ≥ 2`, `T = N^{6/5}`. -/
theorem keyProp_of_fullBound {w : CGLSmoothBump} {k : ℕ} (hk : 2 ≤ k)
    (hFB : FullBoundStatement w 4 k) : KeyPropBound w := by
  intro ε hε
  obtain ⟨C, hC, h⟩ := hFB ε hε
  refine ⟨8 * C + 32, by positivity, ?_⟩
  intro N σ T₀ b W hN hσ1 hσ2 hb hW hsep hbig
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hN0 : (0 : ℝ) < N := by linarith
  have hT1 : 1 ≤ (N : ℝ) ^ (6 / 5 : ℝ) := Real.one_le_rpow hN1 (by norm_num)
  have hTε : 1 ≤ ((N : ℝ) ^ (6 / 5 : ℝ)) ^ ε := Real.one_le_rpow hT1 hε.le
  have hkey0 : 0 ≤ (N : ℝ) ^ (6 / 5 : ℝ) * (N : ℝ) ^ ((12 - 20 * σ) / 5) := by positivity
  rcases le_or_gt N 4 with hN4 | hN5
  · have h := card_le_of_small_keyLength hN hN4 hε hσ2 hW hsep
    have : 0 ≤ 8 * C * ((N : ℝ) ^ (6 / 5 : ℝ)) ^ ε *
        ((N : ℝ) ^ (6 / 5 : ℝ) * (N : ℝ) ^ ((12 - 20 * σ) / 5)) := by positivity
    nlinarith
  have hN5' : (5 : ℝ) ≤ N := by exact_mod_cast hN5
  have hNT : (N : ℝ) ≤ (N : ℝ) ^ (6 / 5 : ℝ) := by
    calc (N : ℝ) = (N : ℝ) ^ (1 : ℝ) := (Real.rpow_one _).symm
      _ ≤ (N : ℝ) ^ (6 / 5 : ℝ) := Real.rpow_le_rpow_of_exponent_le hN1 (by norm_num)
  have hT34 : ((N : ℝ) ^ (6 / 5 : ℝ)) ^ (3 / 4 : ℝ) ≤ N := by
    rw [← Real.rpow_mul hN0.le]
    calc (N : ℝ) ^ ((6 / 5 : ℝ) * (3 / 4)) ≤ (N : ℝ) ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le hN1 (by norm_num)
      _ = N := Real.rpow_one _
  have hbound := h N σ ((N : ℝ) ^ (6 / 5 : ℝ)) T₀ b W (by linarith) hT34 hNT hb hW hsep hbig
  have hf := fullBound_le_keyBound hN1 hσ1 hσ2 hk
  calc (W.card : ℝ) ≤ C * ((N : ℝ) ^ (6 / 5 : ℝ)) ^ ε * fullBound N ((N : ℝ) ^ (6 / 5 : ℝ)) σ 4 k :=
        hbound
    _ ≤ C * ((N : ℝ) ^ (6 / 5 : ℝ)) ^ ε *
          (8 * ((N : ℝ) ^ (6 / 5 : ℝ) * (N : ℝ) ^ ((12 - 20 * σ) / 5))) := by gcongr
    _ ≤ (8 * C + 32) * ((N : ℝ) ^ (6 / 5 : ℝ)) ^ ε *
          ((N : ℝ) ^ (6 / 5 : ℝ) * (N : ℝ) ^ ((12 - 20 * σ) / 5)) := by
        have : 0 ≤ ((N : ℝ) ^ (6 / 5 : ℝ)) ^ ε *
            ((N : ℝ) ^ (6 / 5 : ℝ) * (N : ℝ) ^ ((12 - 20 * σ) / 5)) := by positivity
        nlinarith

/-- **Guth–Maynard, Proposition 3.1, from Propositions 6.1 (`j = 4`, `k ≥ 2`) and 11.2.** -/
theorem keyProp_of_S_bounds (w : CGLUnitRealSmoothBump) {k : ℕ} (hk : 2 ≤ k)
    (hS2 : PropSixOneBound w.toCGLRealSmoothBump 4 k)
    (hS3 : PropElevenTwoBound w.toCGLRealSmoothBump) :
    KeyPropBound w.toCGLSmoothBump :=
  keyProp_of_fullBound hk (fullBoundStatement_of_S_bounds w (by norm_num) (by omega) hS2 hS3)

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
