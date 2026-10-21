import GaloisForLFunctions.RHTower.Sieve.GuthMaynardTheoremOneOneClassicalBound
import GaloisForLFunctions.RHTower.ChenGuptaLiSmoothBump
import GaloisForLFunctions.RHTower.Sieve.JutilaDensityLemma41
import GaloisForLFunctions.RHTower.Sieve.HeathBrownPairSumUnitBlock
import GaloisForLFunctions.RHTower.ZetaZeroDensitySeparatedSelection

/-!
# Proposition 3.1 of Guth–Maynard and the pieces of the reduction of Theorem 1.1

`KeyPropBound w` is Guth–Maynard's Proposition 3.1 (`prpstn:KeyProp`) for the smooth bump `w`
(support `[1, 2]`, `w = 1` on `[6/5, 9/5]`): for `σ ∈ [7/10, 8/10]`, `|b_n| ≤ 1`, and a
`T^ε`-separated set `W` in an interval of length `T = N^{6/5}` on which
`|Σ_{N<n≤2N} w(n/N) b_n n^{it}| ≥ N^σ`,

`|W| ≤ C_ε T^ε · T N^{(12−20σ)/5}`.

(The paper writes the loss as `N^{o_ε(1)}`; taking the separation exponent and the loss exponent
equal is equivalent, since a `T^ε`-separated set is `T^{ε'}`-separated for every `ε' ≤ ε`.)

The two reduction steps proved here, unconditionally given `KeyPropBound w`:

* `card_le_of_keyPropBound`: a `1`-separated set in an interval of length `T ≥ M/2` on which the
  smoothed polynomial of length `M` exceeds `V ∈ [M^{7/10}, M^{4/5}]` has
  `|W| ≤ C_ε T^ε (T + M^{6/5}) M^{12/5} V⁻⁴`.  Mechanism: `σ = log_M V`; a maximal
  `M^{6ε/5}`-separated subset keeps a `1/(2M^{6ε/5}+1)` share of `W`; it is cut into
  `⌊T/M^{6/5}⌋ + 1` windows of length `M^{6/5}`, each bounded by Proposition 3.1.
* `exists_two_plateau_pieces`: for `N ≥ 6`, `(N, 2N]` is the disjoint union of two pieces lying in
  the plateaus `[6N_i/5, 9N_i/5]` of `w(·/N_i)` for `N₁ = ⌊(5N+5)/6⌋`, `N₂ = ⌊(10N+8)/9⌋`; on such
  a piece the smoothed polynomial of the restricted coefficients is the plain partial sum
  (`smoothedDyadicPoly_indicator`).
-/

set_option autoImplicit false

open Finset Complex

namespace RHTower.GuthMaynard

open RHTower.Sieve

noncomputable section

/-- The smoothed polynomial `D_N(t) = Σ_{N<n≤2N} w(n/N) b_n n^{it}` of Proposition 3.1. -/
def smoothedDyadicPoly (w : CGLSmoothBump) (N : ℕ) (b : ℕ → ℂ) (t : ℝ) : ℂ :=
  ∑ n ∈ Ioc N (2 * N), w.value ((n : ℝ) / N) * b n * Complex.exp (Complex.I * t * Real.log n)

/-- **Guth–Maynard, Proposition 3.1**, with `T = N^{6/5}` and `T^{o(1)}` written as `C_ε T^ε`:
for `σ ∈ [7/10, 8/10]`, `|b_n| ≤ 1` and `W` a `T^ε`-separated set in `[T₀, T₀ + T]` with
`|D_N(t)| ≥ N^σ` on `W`, `|W| ≤ C T^ε · T N^{(12−20σ)/5}`. -/
def KeyPropBound (w : CGLSmoothBump) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 ≤ C ∧ ∀ (N : ℕ) (σ T₀ : ℝ) (b : ℕ → ℂ) (W : Finset ℝ),
    1 ≤ N → 7 / 10 ≤ σ → σ ≤ 8 / 10 → (∀ n, ‖b n‖ ≤ 1) →
    (∀ t ∈ W, T₀ ≤ t ∧ t ≤ T₀ + (N : ℝ) ^ (6 / 5 : ℝ)) →
    IsSeparated (((N : ℝ) ^ (6 / 5 : ℝ)) ^ ε) W →
    (∀ t ∈ W, (N : ℝ) ^ σ ≤ ‖smoothedDyadicPoly w N b t‖) →
    (W.card : ℝ) ≤
      C * ((N : ℝ) ^ (6 / 5 : ℝ)) ^ ε * ((N : ℝ) ^ (6 / 5 : ℝ) * (N : ℝ) ^ ((12 - 20 * σ) / 5))

/-! ### Thinning to a `s`-separated subset -/

/-- A `1`-separated set has a `s`-separated subset (`s ≥ 1`) carrying a `1/(2s+1)` share. -/
theorem exists_separated_subset_of_isSeparated {W : Finset ℝ} (hW : IsSeparated 1 W) {s : ℝ}
    (hs : 0 < s) :
    ∃ S ⊆ W, IsSeparated s S ∧ (W.card : ℝ) ≤ (2 * s + 1) * S.card := by
  classical
  have hwin : ∀ u : ℝ, ((W.filter fun z => |z / s - u| ≤ 1).card : ℝ) ≤ 2 * s + 1 := by
    intro u
    have hfe : W.filter (fun z => |z / s - u| ≤ 1) = W.filter (fun z => |s * u - z| ≤ s) := by
      refine Finset.filter_congr fun z _ => ?_
      have e : |s * u - z| = s * |z / s - u| := by
        rw [show s * u - z = -(s * (z / s - u)) by field_simp; ring, abs_neg, abs_mul,
          abs_of_pos hs]
      rw [e, mul_le_iff_le_one_right hs]
    rw [hfe]
    exact card_filter_abs_sub_le hW (s * u) hs.le
  obtain ⟨S, hSW, hSsep, hcard⟩ := RHTower.exists_separated_subset_card_le W (fun z => z / s) hwin
  refine ⟨S, hSW, fun a ha b hb hab => ?_, hcard⟩
  have h1 := hSsep a ha b hb hab
  have e : |a - b| = s * |a / s - b / s| := by
    rw [show a - b = s * (a / s - b / s) by field_simp, abs_mul, abs_of_pos hs]
  rw [e]
  nlinarith

/-! ### Proposition 3.1 on an interval of any length -/

/-- `M^{(12−20σ)/5} = M^{12/5} / V⁴` when `M^σ = V`. -/
theorem rpow_keyExponent_eq {M V σ : ℝ} (hM : 0 < M) (hσ : M ^ σ = V) :
    M ^ ((12 - 20 * σ) / 5) = M ^ (12 / 5 : ℝ) / V ^ 4 := by
  rw [show (12 - 20 * σ) / 5 = 12 / 5 - σ * 4 by ring, Real.rpow_sub hM, Real.rpow_mul hM.le, hσ]
  norm_num

/-- **Proposition 3.1 on an interval of length `T`.**  Given `KeyPropBound w`: for `M ≥ 2`,
`M ≤ 2T`, `|c_n| ≤ 1`, `W ⊂ [T₀, T₀ + T]` `1`-separated with `|D_M(t)| ≥ V` on `W` and
`M^{7/10} ≤ V ≤ M^{4/5}`: `|W| ≤ C T^ε (T + M^{6/5}) M^{12/5} / V⁴`. -/
theorem card_le_of_keyPropBound {w : CGLSmoothBump} (hkey : KeyPropBound w) {ε : ℝ}
    (hε : 0 < ε) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (M : ℕ) (T T₀ V : ℝ) (c : ℕ → ℂ) (W : Finset ℝ),
      2 ≤ M → (M : ℝ) ≤ 2 * T → (∀ n, ‖c n‖ ≤ 1) → (∀ t ∈ W, T₀ ≤ t ∧ t ≤ T₀ + T) →
      IsSeparated 1 W → (M : ℝ) ^ (7 / 10 : ℝ) ≤ V → V ≤ (M : ℝ) ^ (4 / 5 : ℝ) →
      (∀ t ∈ W, V ≤ ‖smoothedDyadicPoly w M c t‖) →
      (W.card : ℝ) ≤ C * T ^ ε * ((T + (M : ℝ) ^ (6 / 5 : ℝ)) * (M : ℝ) ^ (12 / 5 : ℝ) / V ^ 4) := by
  classical
  obtain ⟨K, hK0, hK⟩ := hkey (5 * ε / 12) (by positivity)
  refine ⟨3 * K * 2 ^ ε, by positivity, ?_⟩
  intro M T T₀ V c W hM hMT hc hW hsep hlo hhi hbig
  have hM1 : (1 : ℝ) < M := by exact_mod_cast (by omega : 1 < M)
  have hM0 : (0 : ℝ) < M := by linarith
  have hT : 0 < T := by linarith
  have hV : 0 < V := lt_of_lt_of_le (Real.rpow_pos_of_pos hM0 _) hlo
  -- the window length `L = M^{6/5}` and the thinning scale `s = L^{5ε/12}`
  obtain ⟨L, hL⟩ : ∃ L : ℝ, L = (M : ℝ) ^ (6 / 5 : ℝ) := ⟨_, rfl⟩
  have hL1 : 1 ≤ L := hL ▸ Real.one_le_rpow hM1.le (by norm_num)
  have hL0 : 0 < L := by linarith
  obtain ⟨s, hs⟩ : ∃ s : ℝ, s = L ^ (5 * ε / 12) := ⟨_, rfl⟩
  have hs1 : 1 ≤ s := hs ▸ Real.one_le_rpow hL1 (by positivity)
  have hs0 : 0 < s := by linarith
  -- the exponent `σ = log_M V`
  obtain ⟨σ, hσdef⟩ : ∃ σ : ℝ, σ = Real.logb M V := ⟨_, rfl⟩
  have hσ : (M : ℝ) ^ σ = V := hσdef ▸ Real.rpow_logb hM0 hM1.ne' hV
  have hσ1 : 7 / 10 ≤ σ := hσdef ▸ (Real.le_logb_iff_rpow_le hM1 hV).2 hlo
  have hσ2 : σ ≤ 8 / 10 :=
    hσdef ▸ (Real.logb_le_iff_le_rpow hM1 hV).2 (by rw [show (8 / 10 : ℝ) = 4 / 5 by norm_num]; exact hhi)
  obtain ⟨X, hX⟩ : ∃ X : ℝ, X = (M : ℝ) ^ ((12 - 20 * σ) / 5) := ⟨_, rfl⟩
  have hX0 : 0 ≤ X := hX ▸ (Real.rpow_pos_of_pos hM0 _).le
  -- thinning
  obtain ⟨S, hSW, hSsep, hWS⟩ := exists_separated_subset_of_isSeparated hsep hs0
  -- windows of length `L`, each bounded by Proposition 3.1
  have hspread : ∀ x ∈ S, ∀ y ∈ S, |x - y| ≤ T := fun x hx y hy => by
    have h1 := hW x (hSW hx); have h2 := hW y (hSW hy)
    rw [abs_le]; constructor <;> linarith
  have hlocal : ∀ S' ⊆ S, (∀ x ∈ S', ∀ y ∈ S', |x - y| ≤ L) →
      (S'.card : ℝ) ≤ K * L ^ (5 * ε / 12) * (L * X) := by
    intro S' hS' hdiam
    rcases S'.eq_empty_or_nonempty with he | hne
    · rw [he, card_empty, Nat.cast_zero]; positivity
    have hin : ∀ t ∈ S', S'.min' hne ≤ t ∧ t ≤ S'.min' hne + (M : ℝ) ^ (6 / 5 : ℝ) := by
      intro t ht
      refine ⟨Finset.min'_le S' t ht, ?_⟩
      have := (abs_le.mp (hdiam t ht _ (Finset.min'_mem S' hne))).2
      rw [← hL]; linarith
    have hsep' : IsSeparated (((M : ℝ) ^ (6 / 5 : ℝ)) ^ (5 * ε / 12)) S' := by
      rw [← hL, ← hs]
      exact fun a ha b hb hab => hSsep a (hS' ha) b (hS' hb) hab
    have h := hK M σ (S'.min' hne) c S' (by omega) hσ1 hσ2 hc hin hsep'
      (fun t ht => by rw [hσ]; exact hbig t (hSW (hS' ht)))
    rw [← hL, ← hX] at h
    exact h
  have hScard := card_le_of_finset_window_bound hL0 (by positivity) hspread hlocal
  -- assembly: `|W| ≤ 3 s |S|`, `|S| ≤ (T/L + 1) K L^{5ε/12} L X`
  have hfloor : ((⌊T / L⌋₊ : ℕ) : ℝ) * L ≤ T := by
    have := Nat.floor_le (div_nonneg hT.le hL0.le)
    calc ((⌊T / L⌋₊ : ℕ) : ℝ) * L ≤ T / L * L := mul_le_mul_of_nonneg_right this hL0.le
      _ = T := by field_simp
  have hS2 : (S.card : ℝ) ≤ K * L ^ (5 * ε / 12) * (T + L) * X := by
    refine hScard.trans ?_
    have hKL : 0 ≤ K * L ^ (5 * ε / 12) := by positivity
    calc ((⌊T / L⌋₊ : ℝ) + 1) * (K * L ^ (5 * ε / 12) * (L * X))
        = K * L ^ (5 * ε / 12) * ((⌊T / L⌋₊ : ℝ) * L + L) * X := by ring
      _ ≤ K * L ^ (5 * ε / 12) * (T + L) * X := by
        gcongr
  -- `s · L^{5ε/12} = M^ε ≤ (2T)^ε`
  have hpow : s * L ^ (5 * ε / 12) = (M : ℝ) ^ ε := by
    rw [hs, ← Real.rpow_add hL0, hL, ← Real.rpow_mul hM0.le]
    congr 1; ring
  have hMε : (M : ℝ) ^ ε ≤ 2 ^ ε * T ^ ε := by
    rw [← Real.mul_rpow (by norm_num) hT.le]
    exact Real.rpow_le_rpow hM0.le hMT hε.le
  have hXeq : X = (M : ℝ) ^ (12 / 5 : ℝ) / V ^ 4 := hX ▸ rpow_keyExponent_eq hM0 hσ
  have hWS' : (W.card : ℝ) ≤ 3 * s * S.card := hWS.trans
    (mul_le_mul_of_nonneg_right (by linarith) (Nat.cast_nonneg _))
  have hTL : 0 ≤ (T + L) * X := by positivity
  calc (W.card : ℝ) ≤ 3 * s * S.card := hWS'
    _ ≤ 3 * s * (K * L ^ (5 * ε / 12) * (T + L) * X) :=
        mul_le_mul_of_nonneg_left hS2 (by positivity)
    _ = 3 * K * (s * L ^ (5 * ε / 12)) * ((T + L) * X) := by ring
    _ ≤ 3 * K * (2 ^ ε * T ^ ε) * ((T + L) * X) := by
        rw [hpow]; gcongr
    _ = 3 * K * 2 ^ ε * T ^ ε * ((T + (M : ℝ) ^ (6 / 5 : ℝ)) * (M : ℝ) ^ (12 / 5 : ℝ) / V ^ 4) := by
        rw [hXeq, hL]; ring

/-! ### Splitting `(N, 2N]` into two plateau pieces -/

/-- On a piece `P` of `(M, 2M]` inside the plateau `[6M/5, 9M/5]` the smoothed polynomial of the
coefficients restricted to `P` is the plain partial sum over `P`. -/
theorem smoothedDyadicPoly_indicator (w : CGLSmoothBump) {M : ℕ} {P : Finset ℕ}
    (hP : ∀ n ∈ P, M < n ∧ n ≤ 2 * M ∧ 6 * M ≤ 5 * n ∧ 5 * n ≤ 9 * M) (b : ℕ → ℂ) (t : ℝ) :
    smoothedDyadicPoly w M (fun n => if n ∈ P then b n else 0) t =
      ∑ n ∈ P, b n * Complex.exp (Complex.I * t * Real.log n) := by
  classical
  unfold smoothedDyadicPoly
  have hsub : P ⊆ Ioc M (2 * M) := fun n hn =>
    Finset.mem_Ioc.mpr ⟨(hP n hn).1, (hP n hn).2.1⟩
  rw [← Finset.sum_subset hsub fun n _ hn => by simp [hn]]
  refine sum_congr rfl fun n hn => ?_
  obtain ⟨h1, -, h3, h4⟩ := hP n hn
  have hM : (0 : ℝ) < M := by exact_mod_cast (by omega : 0 < M)
  have h3' : (6 : ℝ) * M ≤ 5 * n := by exact_mod_cast h3
  have h4' : (5 : ℝ) * n ≤ 9 * M := by exact_mod_cast h4
  have hplat : w.value ((n : ℝ) / M) = 1 := w.plateau _ ⟨by rw [le_div_iff₀ hM]; linarith,
    by rw [div_le_iff₀ hM]; linarith⟩
  dsimp only
  rw [if_pos hn, hplat, one_mul]

/-- **Two plateau pieces.**  For `N ≥ 6`, `(N, 2N] = P₁ ⊔ P₂` with `P_i` inside the plateau of
`w(·/N_i)`, `N₁ = ⌊(5N+5)/6⌋`, `N₂ = ⌊(10N+8)/9⌋`, and `5N ≤ 6N_i`, `N_i ≤ 2N`, `N_i ≥ 2`. -/
theorem exists_two_plateau_pieces {N : ℕ} (hN : 6 ≤ N) :
    ∃ N₁ N₂ : ℕ, ∃ P₁ P₂ : Finset ℕ, Ioc N (2 * N) = P₁ ∪ P₂ ∧ Disjoint P₁ P₂ ∧
      (∀ n ∈ P₁, N₁ < n ∧ n ≤ 2 * N₁ ∧ 6 * N₁ ≤ 5 * n ∧ 5 * n ≤ 9 * N₁) ∧
      (∀ n ∈ P₂, N₂ < n ∧ n ≤ 2 * N₂ ∧ 6 * N₂ ≤ 5 * n ∧ 5 * n ≤ 9 * N₂) ∧
      5 * N ≤ 6 * N₁ ∧ N₁ ≤ 2 * N ∧ 5 * N ≤ 6 * N₂ ∧ N₂ ≤ 2 * N ∧ 2 ≤ N₁ ∧ 2 ≤ N₂ := by
  classical
  refine ⟨(5 * N + 5) / 6, (10 * N + 8) / 9, (Ioc N (2 * N)).filter (fun n => 5 * n ≤ 9 * ((5 * N + 5) / 6)),
    (Ioc N (2 * N)).filter (fun n => ¬ 5 * n ≤ 9 * ((5 * N + 5) / 6)), ?_, ?_, ?_, ?_, ?_⟩
  · exact (Finset.filter_union_filter_not_eq _ _).symm
  · exact Finset.disjoint_filter_filter_not _ _ _
  · intro n hn
    simp only [Finset.mem_filter, Finset.mem_Ioc] at hn
    omega
  · intro n hn
    simp only [Finset.mem_filter, Finset.mem_Ioc] at hn
    omega
  · omega

end

end RHTower.GuthMaynard
