import GaloisForLFunctions.RHTower.Sieve.GuthMaynardHeathBrownBlocks
import GaloisForLFunctions.RHTower.Sieve.MatomakiTeravainenErrorGrowth
import GaloisForLFunctions.RHTower.Sieve.GuthMaynardEnergyDiscreteThirdMoment

set_option autoImplicit false

/-!
# Guth–Maynard Lemma 11.5 and Lemma 1.5: the discrete second moment of `R`

For a finite family of real labels `(y_p)_{p ∈ P}` put `R_y(v) = Σ_{p ∈ P} v^{i y_p}`
(`R = R_{id}` on `W`). Expanding both squares gives the exact duality

`Σ_{n₁,n₂ ∈ S} |R_y(n₁/n₂)|² = Σ_{p,q ∈ P} |Σ_{n ∈ S} n^{i(y_p − y_q)}|²`   (`S ⊆ ℕ_{>0}`).

With `P = W` the discrete second moment of `R` is Heath-Brown's pair sum, so a per-block
Heath-Brown bound `HeathBrownBlockBound M T K` gives **Lemma 11.5** on every `S ⊆ (M, 2M+1]`
(`sum_normSq_lagSum_le_of_blockBound`; the extra point costs `2|W|²`):
`Σ_{n₁,n₂ ∈ S} |R(n₁/n₂)|² ≤ (2K + 2)(|W|² M + |W| M² + |W|^{5/4} T^{1/2} M)`.
* `guthMaynard_lemma115`: every `M ≥ 1`, over the full statement `HeathBrownPairSumBound`;
* `guthMaynard_lemma115_short`: `M ≤ T^{1/4}`, unconditional (corpus short-block theorem).

**Lemma 1.5** (`guthMaynard_lemma15`, unconditional for `T^{2/3} ≤ N ≤ T`) follows from Lemma 11.4,
`|R| ≤ |W|` and Lemma 11.5 at `M = N` from the corpus long-block theorem; the third Heath-Brown
term is absorbed there (`|W|^{5/4} T^{1/2} N ≤ |W|² N + |W| N²`), giving
`E(W) ⪅ |W|³ N^{1−2σ} + |W|² N^{2−2σ}` (the paper's `σ > 1/2` is not used).
-/

open MeasureTheory Set Finset ComplexConjugate

namespace RHTower.GuthMaynard

noncomputable section

/-! ### The labelled lag sum and the duality identity -/

/-- `R_y(v) = Σ_{p ∈ P} v^{i y_p}`; `labelledLagSum W id = lagSum W`. -/
def labelledLagSum {ι : Type*} (P : Finset ι) (y : ι → ℝ) (v : ℝ) : ℂ :=
  ∑ p ∈ P, Complex.exp (Complex.I * y p * Real.log v)

theorem labelledLagSum_id (W : Finset ℝ) (v : ℝ) : labelledLagSum W id v = lagSum W v := rfl

/-- `|R_y(v)|² = Σ_{p,q} v^{i(y_p − y_q)}`. -/
theorem normSq_labelledLagSum_eq {ι : Type*} (P : Finset ι) (y : ι → ℝ) (v : ℝ) :
    ((‖labelledLagSum P y v‖ ^ 2 : ℝ) : ℂ) =
      ∑ p ∈ P, ∑ q ∈ P, Complex.exp (Complex.I * (y p - y q) * Real.log v) := by
  push_cast
  rw [← Complex.mul_conj', labelledLagSum, map_sum, sum_mul_sum]
  refine sum_congr rfl fun p _ => sum_congr rfl fun q _ => ?_
  rw [← Complex.exp_conj, ← Complex.exp_add]
  congr 1
  simp only [map_mul, Complex.conj_I, Complex.conj_ofReal]
  ring

/-- `|Σ_{n∈S} n^{iz}|² = Σ_{n₁,n₂} (n₁/n₂)^{iz}` for `S ⊆ ℕ_{>0}`. -/
theorem normSq_sum_exp_log_eq {S : Finset ℕ} (hS : ∀ n ∈ S, 0 < n) (z : ℝ) :
    ((‖∑ n ∈ S, Complex.exp (Complex.I * z * Real.log n)‖ ^ 2 : ℝ) : ℂ) =
      ∑ n₁ ∈ S, ∑ n₂ ∈ S, Complex.exp (Complex.I * z * Real.log ((n₁ : ℝ) / n₂)) := by
  rw [Complex.ofReal_pow, ← Complex.mul_conj', map_sum, sum_mul_sum]
  exact sum_congr rfl fun n₁ h₁ => sum_congr rfl fun n₂ h₂ =>
    exp_mul_conj_exp_log (hS n₁ h₁) (hS n₂ h₂) z

/-- **Duality.** `Σ_{n₁,n₂ ∈ S} |R_y(n₁/n₂)|² = Σ_{p,q ∈ P} |Σ_{n ∈ S} n^{i(y_p − y_q)}|²`. -/
theorem sum_normSq_labelledLagSum_eq {ι : Type*} (P : Finset ι) (y : ι → ℝ) {S : Finset ℕ}
    (hS : ∀ n ∈ S, 0 < n) :
    ∑ n₁ ∈ S, ∑ n₂ ∈ S, ‖labelledLagSum P y ((n₁ : ℝ) / n₂)‖ ^ 2 =
      ∑ p ∈ P, ∑ q ∈ P,
        ‖∑ n ∈ S, Complex.exp (Complex.I * (y p - y q) * Real.log n)‖ ^ 2 := by
  apply Complex.ofReal_injective
  simp only [Complex.ofReal_sum]
  simp_rw [normSq_labelledLagSum_eq, ← Complex.ofReal_sub, normSq_sum_exp_log_eq hS]
  refine (sum_congr rfl fun n₁ _ => sum_comm).trans ?_
  refine sum_comm.trans ?_
  refine sum_congr rfl fun p _ => ?_
  refine (sum_congr rfl fun n₁ _ => sum_comm).trans ?_
  exact sum_comm

/-! ### Heath-Brown on a block with one extra point -/

/-- **Heath-Brown on `S ⊆ (M, 2M+1]`.** From the per-block bound at `M`: for `|a_n| ≤ 1` and
`1`-separated `𝒯 ⊆ [T₀, T₀ + T]`,
`Σ_{t₁,t₂} |Σ_{n∈S} a_n n^{i(t₁−t₂)}|² ≤ (2K + 2)(|𝒯|²M + |𝒯|M² + |𝒯|^{5/4}T^{1/2}M)`.
(The possible extra point `2M + 1` costs `2|𝒯|² ≤ 2|𝒯|²M`.) -/
theorem pairSum_le_of_blockBound {M : ℕ} {T K : ℝ} (hHB : HeathBrownBlockBound M T K)
    (hT : 0 ≤ T) (hM : 1 ≤ M) {S : Finset ℕ} (hS : S ⊆ Finset.Ioc M (2 * M + 1)) {a : ℕ → ℂ}
    (ha : ∀ n, ‖a n‖ ≤ 1) {𝒯 : Finset ℝ} {T₀ : ℝ} (h𝒯 : ∀ t ∈ 𝒯, T₀ ≤ t ∧ t ≤ T₀ + T)
    (hsep : IsSeparated 1 𝒯) :
    ∑ t₁ ∈ 𝒯, ∑ t₂ ∈ 𝒯,
        ‖∑ n ∈ S, a n * Complex.exp (Complex.I * (t₁ - t₂) * Real.log n)‖ ^ 2
      ≤ (2 * K + 2) * heathBrownMajorant 𝒯.card M T := by
  classical
  set a' : ℕ → ℂ := fun n => if n ∈ S then a n else 0
  have ha' : ∀ n, ‖a' n‖ ≤ 1 := fun n => by
    simp only [a']; split_ifs
    · exact ha n
    · simp
  -- split off the top point `2M + 1`
  have hsplit : ∀ u : ℂ, ∑ n ∈ S, a n * Complex.exp (Complex.I * u * Real.log n) =
      ∑ n ∈ Finset.Ioc M (2 * M), a' n * Complex.exp (Complex.I * u * Real.log n) +
        a' (2 * M + 1) * Complex.exp (Complex.I * u * Real.log ((2 * M + 1 : ℕ) : ℝ)) := by
    intro u
    rw [← Finset.sum_Ioc_succ_top (by omega)
      (fun n => a' n * Complex.exp (Complex.I * u * Real.log n))]
    simp only [a', ite_mul, zero_mul]
    rw [sum_ite_mem, Finset.inter_eq_right.mpr hS]
  have htop : ∀ u : ℂ, ‖a' (2 * M + 1) *
      Complex.exp (Complex.I * u * Real.log ((2 * M + 1 : ℕ) : ℝ))‖ ^ 2 ≤
        ‖Complex.exp (Complex.I * u * Real.log ((2 * M + 1 : ℕ) : ℝ))‖ ^ 2 := by
    intro u
    rw [norm_mul]
    refine pow_le_pow_left₀ (by positivity) ?_ 2
    exact mul_le_of_le_one_left (norm_nonneg _) (ha' _)
  have hX : (0 : ℝ) ≤ 𝒯.card := Nat.cast_nonneg _
  have hM0 : (0 : ℝ) ≤ M := Nat.cast_nonneg _
  have hM1 : (1 : ℝ) ≤ M := by exact_mod_cast hM
  have hblock := hHB 𝒯 a' T₀ ha' h𝒯 hsep
  have hsq : (𝒯.card : ℝ) ^ 2 ≤ heathBrownMajorant 𝒯.card M T := by
    unfold heathBrownMajorant
    have h1 : (𝒯.card : ℝ) ^ 2 ≤ (𝒯.card : ℝ) ^ 2 * M := le_mul_of_one_le_right (by positivity) hM1
    have : 0 ≤ (𝒯.card : ℝ) * (M : ℝ) ^ 2 := by positivity
    have : 0 ≤ (𝒯.card : ℝ) ^ (5 / 4 : ℝ) * T ^ (1 / 2 : ℝ) * M := by positivity
    linarith
  calc ∑ t₁ ∈ 𝒯, ∑ t₂ ∈ 𝒯,
        ‖∑ n ∈ S, a n * Complex.exp (Complex.I * (t₁ - t₂) * Real.log n)‖ ^ 2
      ≤ ∑ t₁ ∈ 𝒯, ∑ t₂ ∈ 𝒯,
          (2 * ‖∑ n ∈ Finset.Ioc M (2 * M), a' n *
              Complex.exp (Complex.I * (t₁ - t₂) * Real.log n)‖ ^ 2 + 2 * 1) := by
        refine sum_le_sum fun t₁ _ => sum_le_sum fun t₂ _ => ?_
        rw [hsplit]
        refine (Sieve.norm_add_sq_le_two _ _).trans ?_
        have := htop ((t₁ : ℂ) - t₂)
        have e : ‖Complex.exp (Complex.I * ((t₁ : ℂ) - t₂) *
            Real.log ((2 * M + 1 : ℕ) : ℝ))‖ = 1 := by
          rw [← Complex.ofReal_sub, norm_exp_mul_log]
        rw [e, one_pow] at this
        linarith
    _ = 2 * (∑ t₁ ∈ 𝒯, ∑ t₂ ∈ 𝒯, ‖∑ n ∈ Finset.Ioc M (2 * M), a' n *
              Complex.exp (Complex.I * (t₁ - t₂) * Real.log n)‖ ^ 2) + 2 * (𝒯.card : ℝ) ^ 2 := by
        simp only [sum_add_distrib, mul_sum, sum_const, nsmul_eq_mul]
        ring
    _ ≤ 2 * (K * heathBrownMajorant 𝒯.card M T) + 2 * heathBrownMajorant 𝒯.card M T := by
        gcongr
    _ = (2 * K + 2) * heathBrownMajorant 𝒯.card M T := by ring

/-! ### Lemma 11.5 -/

/-- **Lemma 11.5 from a per-block bound**: under `HeathBrownBlockBound M T K`, for every
`1`-separated `W ⊆ [T₀, T₀ + T]` and `S ⊆ (M, 2M+1]`,
`Σ_{n₁,n₂ ∈ S} |R(n₁/n₂)|² ≤ (2K + 2)(|W|² M + |W| M² + |W|^{5/4} T^{1/2} M)`. -/
theorem sum_normSq_lagSum_le_of_blockBound {M : ℕ} {T K : ℝ} (hHB : HeathBrownBlockBound M T K)
    (hT : 0 ≤ T) (hM : 1 ≤ M) {S : Finset ℕ} (hS : S ⊆ Finset.Ioc M (2 * M + 1)) {W : Finset ℝ}
    {T₀ : ℝ} (hW : ∀ t ∈ W, T₀ ≤ t ∧ t ≤ T₀ + T) (hsep : IsSeparated 1 W) :
    ∑ n₁ ∈ S, ∑ n₂ ∈ S, ‖lagSum W ((n₁ : ℝ) / n₂)‖ ^ 2 ≤
      (2 * K + 2) * heathBrownMajorant W.card M T := by
  have h0 : (0 : ℕ) ∉ S := fun h => by have := (mem_Ioc.mp (hS h)).1; omega
  rw [Sieve.sum_normSq_lagSum_eq_hbPairSum W h0, Sieve.hbPairSum_eq_sum_exp]
  have := pairSum_le_of_blockBound hHB hT hM hS (a := fun _ => 1) (fun _ => by simp) hW hsep
  simpa only [one_mul] using this

/-- **Guth–Maynard Lemma 11.5**, for every block length (assembly over `HeathBrownPairSumBound`):
for every `ε > 0` there is `C ≥ 0` such that for every `1`-separated `W ⊆ [T₀, T₀ + T]`
(`T ≥ 2`), every `M ≥ 1` and every `S ⊆ (M, 2M+1]` (in particular `S = (M, 2M]`),
`Σ_{n₁,n₂ ∈ S} |R(n₁/n₂)|² ≤ C T^ε (|W|² M + |W| M² + |W|^{5/4} T^{1/2} M)`. -/
theorem guthMaynard_lemma115 (hHB : HeathBrownPairSumBound) {ε : ℝ} (hε : 0 < ε) :
    ∃ C, 0 ≤ C ∧ ∀ (W : Finset ℝ) (M : ℕ) (S : Finset ℕ) (T T₀ : ℝ),
      2 ≤ T → 1 ≤ M → S ⊆ Finset.Ioc M (2 * M + 1) → (∀ t ∈ W, T₀ ≤ t ∧ t ≤ T₀ + T) →
      IsSeparated 1 W →
      ∑ n₁ ∈ S, ∑ n₂ ∈ S, ‖lagSum W ((n₁ : ℝ) / n₂)‖ ^ 2 ≤
        C * T ^ ε * heathBrownMajorant W.card M T := by
  obtain ⟨C, hC, h⟩ := hHB.blockBound hε
  refine ⟨2 * C + 2, by positivity, fun W M S T T₀ hT hM hS hW hsep => ?_⟩
  have hTε : 1 ≤ T ^ ε := Real.one_le_rpow (by linarith) hε.le
  refine (sum_normSq_lagSum_le_of_blockBound (h M T hT hM) (by linarith) hM hS hW hsep).trans ?_
  have h0 := heathBrownMajorant_nonneg (X := (W.card : ℝ)) (M := (M : ℝ)) (T := T)
    (Nat.cast_nonneg _) (Nat.cast_nonneg _) (by linarith)
  have : 2 * (C * T ^ ε) + 2 ≤ (2 * C + 2) * T ^ ε := by nlinarith
  exact mul_le_mul_of_nonneg_right this h0

/-- **Guth–Maynard Lemma 11.5 for blocks `M ≤ T^{1/4}`, unconditionally** (Heath-Brown's theorem
for short blocks, `exists_heathBrownBlockBound_short`): for every `ε > 0` there is `C ≥ 0` such
that for every `1`-separated `W ⊆ [T₀, T₀ + T]` (`T ≥ 2`), `1 ≤ M ≤ T^{1/4}` and
`S ⊆ (M, 2M+1]`, `Σ_{n₁,n₂ ∈ S} |R(n₁/n₂)|² ≤ C T^ε (|W|² M + |W| M² + |W|^{5/4} T^{1/2} M)`. -/
theorem guthMaynard_lemma115_short {ε : ℝ} (hε : 0 < ε) :
    ∃ C, 0 ≤ C ∧ ∀ (W : Finset ℝ) (M : ℕ) (S : Finset ℕ) (T T₀ : ℝ),
      2 ≤ T → 1 ≤ M → (M : ℝ) ≤ T ^ (1 / 4 : ℝ) → S ⊆ Finset.Ioc M (2 * M + 1) →
      (∀ t ∈ W, T₀ ≤ t ∧ t ≤ T₀ + T) → IsSeparated 1 W →
      ∑ n₁ ∈ S, ∑ n₂ ∈ S, ‖lagSum W ((n₁ : ℝ) / n₂)‖ ^ 2 ≤
        C * T ^ ε * heathBrownMajorant W.card M T := by
  obtain ⟨C, hC, h⟩ := exists_heathBrownBlockBound_short hε
  refine ⟨2 * C + 2, by positivity, fun W M S T T₀ hT hM hMT hS hW hsep => ?_⟩
  have hTε : 1 ≤ T ^ ε := Real.one_le_rpow (by linarith) hε.le
  refine (sum_normSq_lagSum_le_of_blockBound (h M T hT hM hMT) (by linarith) hM hS hW
    hsep).trans ?_
  have h0 := heathBrownMajorant_nonneg (X := (W.card : ℝ)) (M := (M : ℝ)) (T := T)
    (Nat.cast_nonneg _) (Nat.cast_nonneg _) (by linarith)
  have : 2 * (C * T ^ ε) + 2 ≤ (2 * C + 2) * T ^ ε := by nlinarith
  exact mul_le_mul_of_nonneg_right this h0

/-! ### Lemma 1.5 -/

/-- The third Heath-Brown term is absorbed for `N ≥ T^{2/3}`:
`|W|^{5/4} T^{1/2} N ≤ |W|² N + |W| N²`. -/
theorem third_term_le_of_twoThirds {X N T : ℝ} (hX : 0 ≤ X) (hT : 0 ≤ T)
    (hN : T ^ (2 / 3 : ℝ) ≤ N) :
    X ^ (5 / 4 : ℝ) * T ^ (1 / 2 : ℝ) * N ≤ X ^ 2 * N + X * N ^ 2 := by
  have hN0 : 0 ≤ N := le_trans (by positivity) hN
  -- `T^{1/2} = (T^{2/3})^{3/4} ≤ N^{3/4}`
  have hT12 : T ^ (1 / 2 : ℝ) ≤ N ^ (3 / 4 : ℝ) := by
    have : T ^ (1 / 2 : ℝ) = (T ^ (2 / 3 : ℝ)) ^ (3 / 4 : ℝ) := by
      rw [← Real.rpow_mul hT]; norm_num
    rw [this]
    exact Real.rpow_le_rpow (by positivity) hN (by norm_num)
  set x := X ^ ((1 : ℝ) / 4)
  set ν := N ^ ((1 : ℝ) / 4)
  have hx0 : 0 ≤ x := by positivity
  have hν0 : 0 ≤ ν := by positivity
  have eX : X = x ^ 4 := by rw [← Real.rpow_mul_natCast hX]; norm_num
  have eN : N = ν ^ 4 := by rw [← Real.rpow_mul_natCast hN0]; norm_num
  have eX5 : X ^ (5 / 4 : ℝ) = x ^ 5 := by rw [← Real.rpow_mul_natCast hX]; norm_num
  have eN3 : N ^ (3 / 4 : ℝ) = ν ^ 3 := by rw [← Real.rpow_mul_natCast hN0]; norm_num
  calc X ^ (5 / 4 : ℝ) * T ^ (1 / 2 : ℝ) * N ≤ X ^ (5 / 4 : ℝ) * N ^ (3 / 4 : ℝ) * N := by
        gcongr
    _ = x ^ 5 * ν ^ 7 := by rw [eX5, eN3, eN]; ring
    _ ≤ x ^ 8 * ν ^ 4 + x ^ 4 * ν ^ 8 := by
        rcases le_total x ν with h | h
        · have : x ^ 5 * ν ^ 7 ≤ x ^ 4 * ν ^ 8 := by
            have := mul_le_mul_of_nonneg_left h (by positivity : 0 ≤ x ^ 4 * ν ^ 7)
            nlinarith
          nlinarith [pow_nonneg hx0 8, pow_nonneg hν0 4]
        · have h3 : ν ^ 3 ≤ x ^ 3 := pow_le_pow_left₀ hν0 h 3
          have : x ^ 5 * ν ^ 7 ≤ x ^ 8 * ν ^ 4 := by
            have := mul_le_mul_of_nonneg_left h3 (by positivity : 0 ≤ x ^ 5 * ν ^ 4)
            nlinarith
          nlinarith [pow_nonneg hx0 4, pow_nonneg hν0 8]
    _ = X ^ 2 * N + X * N ^ 2 := by rw [eX, eN]; ring

/-- **Guth–Maynard Lemma 1.5**, unconditionally (Heath-Brown's theorem for long blocks,
`exists_heathBrownBlockBound_long`): for every `ε > 0` there is `C ≥ 0` such that for `T ≥ 2`,
`T^{2/3} ≤ N ≤ T`, `|b_n| ≤ 1` and every `1`-separated `W ⊆ [T₀, T₀ + T]` with `|D(t)| ≥ N^σ` on
`W`: `E(W) ≤ C T^ε (|W|³ N^{1−2σ} + |W|² N^{2−2σ})`. -/
theorem guthMaynard_lemma15 {ε : ℝ} (hε : 0 < ε) :
    ∃ C, 0 ≤ C ∧ ∀ (N : ℕ) (b : ℕ → ℂ) (σ : ℝ) (W : Finset ℝ) (T T₀ : ℝ),
      2 ≤ T → T ^ (2 / 3 : ℝ) ≤ N → (N : ℝ) ≤ T → (∀ n, ‖b n‖ ≤ 1) →
      (∀ t ∈ W, T₀ ≤ t ∧ t ≤ T₀ + T) → IsSeparated 1 W →
      (∀ t ∈ W, (N : ℝ) ^ σ ≤ ‖dyadicDirichletPoly N b t‖) →
      (additiveEnergy W : ℝ) ≤
        C * T ^ ε * ((W.card : ℝ) ^ 3 * (N : ℝ) ^ (1 - 2 * σ) +
          (W.card : ℝ) ^ 2 * (N : ℝ) ^ (2 - 2 * σ)) := by
  obtain ⟨C₀, hC₀, hlong⟩ := exists_heathBrownBlockBound_long hε
  set C := 2 * C₀ + 2
  have hC : 0 ≤ C := by positivity
  refine ⟨2 * energyThirdMomentConst * C, by
    have := energyThirdMomentConst_nonneg; positivity,
    fun N b σ W T T₀ hT hNT hNle hb hW hsep hD => ?_⟩
  have hN : 1 ≤ N := by
    have : (1 : ℝ) ≤ N := (Real.one_le_rpow (by linarith) (by norm_num)).trans hNT
    exact_mod_cast this
  have hTε : 1 ≤ T ^ ε := Real.one_le_rpow (by linarith) hε.le
  have h115 : ∑ n₁ ∈ Finset.Ioc N (2 * N), ∑ n₂ ∈ Finset.Ioc N (2 * N),
      ‖lagSum W ((n₁ : ℝ) / n₂)‖ ^ 2 ≤ C * T ^ ε * heathBrownMajorant W.card N T := by
    refine (sum_normSq_lagSum_le_of_blockBound (hlong N T hT hNT hNle) (by linarith) hN
      (Finset.Ioc_subset_Ioc_right (by omega)) hW hsep).trans ?_
    have h0 := heathBrownMajorant_nonneg (X := (W.card : ℝ)) (M := (N : ℝ)) (T := T)
      (Nat.cast_nonneg _) (Nat.cast_nonneg _) (by linarith)
    have : 2 * (C₀ * T ^ ε) + 2 ≤ C * T ^ ε := by simp only [C]; nlinarith
    exact mul_le_mul_of_nonneg_right this h0
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hT0 : (0 : ℝ) ≤ T := by linarith
  set X : ℝ := (W.card : ℝ)
  have hX : 0 ≤ X := Nat.cast_nonneg _
  have hE := additiveEnergy_le_discreteThirdMoment hN hb hsep hD
  -- `|R|³ ≤ |W| |R|²`
  have hcube : ∑ n₁ ∈ Finset.Ioc N (2 * N), ∑ n₂ ∈ Finset.Ioc N (2 * N),
      ‖lagSum W ((n₁ : ℝ) / n₂)‖ ^ 3 ≤
        X * ∑ n₁ ∈ Finset.Ioc N (2 * N), ∑ n₂ ∈ Finset.Ioc N (2 * N),
          ‖lagSum W ((n₁ : ℝ) / n₂)‖ ^ 2 := by
    rw [mul_sum]
    refine sum_le_sum fun n₁ _ => ?_
    rw [mul_sum]
    refine sum_le_sum fun n₂ _ => ?_
    have h := norm_lagSum_le W ((n₁ : ℝ) / n₂)
    have h0 := norm_nonneg (lagSum W ((n₁ : ℝ) / n₂))
    calc ‖lagSum W ((n₁ : ℝ) / n₂)‖ ^ 3 = ‖lagSum W ((n₁ : ℝ) / n₂)‖ *
          ‖lagSum W ((n₁ : ℝ) / n₂)‖ ^ 2 := by ring
      _ ≤ X * ‖lagSum W ((n₁ : ℝ) / n₂)‖ ^ 2 := by gcongr
  have hsq := h115
  have habs : heathBrownMajorant X N T ≤ 2 * (X ^ 2 * N + X * (N : ℝ) ^ 2) := by
    unfold heathBrownMajorant
    have := third_term_le_of_twoThirds hX hT0 hNT
    linarith
  have hpow1 : (N : ℝ) ^ (-2 * σ) * N = (N : ℝ) ^ (1 - 2 * σ) := by
    rw [show (1 - 2 * σ) = -2 * σ + 1 by ring, Real.rpow_add hN0, Real.rpow_one]
  have hpow2 : (N : ℝ) ^ (-2 * σ) * (N : ℝ) ^ 2 = (N : ℝ) ^ (2 - 2 * σ) := by
    rw [show (2 - 2 * σ) = -2 * σ + (2 : ℕ) by push_cast; ring, Real.rpow_add hN0,
      Real.rpow_natCast]
  have hK := energyThirdMomentConst_nonneg
  have hc : 0 ≤ (N : ℝ) ^ (-2 * σ) := by positivity
  have hTε : 0 ≤ T ^ ε := by positivity
  calc (additiveEnergy W : ℝ)
      ≤ energyThirdMomentConst * (N : ℝ) ^ (-2 * σ) * (X * (C * T ^ ε *
          heathBrownMajorant X N T)) := by
        refine hE.trans (mul_le_mul_of_nonneg_left (hcube.trans ?_) (by positivity))
        exact mul_le_mul_of_nonneg_left hsq hX
    _ ≤ energyThirdMomentConst * (N : ℝ) ^ (-2 * σ) * (X * (C * T ^ ε *
          (2 * (X ^ 2 * N + X * (N : ℝ) ^ 2)))) := by gcongr
    _ = 2 * energyThirdMomentConst * C * T ^ ε * (X ^ 3 * ((N : ℝ) ^ (-2 * σ) * N) +
          X ^ 2 * ((N : ℝ) ^ (-2 * σ) * (N : ℝ) ^ 2)) := by ring
    _ = _ := by rw [hpow1, hpow2]

end

end RHTower.GuthMaynard
