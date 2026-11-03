import GaloisForLFunctions.GrowingWindowsOfSpecZ.TheSchurParametersOfSpecZ

/-!
# The lattice reads the primes causally

Let `λ` be any prime weight and `κ^λ(d) = W_λ(φ, φ(· + dh))` the Weil sequence of a bump `φ`
supported in `[−r, 0]` with the weights `λ` in place of `Λ` (`weilSeqW`; `λ = Λ` is `weilSeq`).
The prime part of `κ^λ(d)` is `−Σ_n λ(n)n^{−1/2}(k_d(log n) + k_d(−log n))`, where
`k_d(x) = ∫ φ(u)φ(u − x + dh) du` is the **lattice lag** (`latticeLag`), and `k_d(x) = 0` unless
`|x − dh| ≤ r` (`latticeLag_eq_zero`).

* **Locality** (`weilSeqW_congr`): `κ^λ(d)` reads only the weights of `n` with `log n ≤ |dh| + r`.
* **Causality** (`levinson_weilSeqW_congr`): the margin `E_n` and the predictor of size `n` read only
  the prime powers `m ≤ e^{nh + r}`: the lattice canonical system is causal in the primes.
* **A kick is one Schur parameter** (`weilSeqW_single_kick`, `schurParam_single_kick`). Changing the
  weight of one prime power `n₀` changes `κ(d)` by `−δλ(n₀)n₀^{−1/2}(k_d(log n₀) + k_d(−log n₀))`.
  At the lattice stage `m` with `mh + r < log n₀` the margins, predictors and frozen predictions up to
  size `m` are unchanged, and the Schur parameter `β_m` moves by exactly
  `−δλ(n₀)n₀^{−1/2}k_{m+1}(log n₀)`. The arithmetic enters the evolution only as these kicks; the
  prime-free sequence `κ^0` is the free evolution of the archimedean place and the pole.
-/

noncomputable section

open MeasureTheory Set Filter Topology Finset Complex Zeta23

namespace GaloisForLFunctions.GrowingWindowsOfSpecZ

open ArithmeticCastelnuovoSeveri

variable {φ : ℝ → ℝ} {h r : ℝ}

/-- The **Weil sequence with prime weights `λ`**: `κ^λ(d) = Re W_λ(φ, φ(· + dh))`. -/
def weilSeqW (lam : ℕ → ℝ) (φ : ℝ → ℝ) (h : ℝ) (d : ℤ) : ℝ :=
  (RHTower.weilFullFunctional lam (EF.weilTest (cx φ) (cx (latticeTranslate φ h d)))).re

theorem weilSeqW_vonMangoldt (φ : ℝ → ℝ) (h : ℝ) :
    weilSeqW (fun n => (ArithmeticFunction.vonMangoldt n : ℝ)) φ h = weilSeq φ h := rfl

/-- The **lattice lag** `k_d(x) = ∫ φ(u)φ(u − x + dh) du`: the correlation that a jump of length `x`
sees between `φ` and its translate to the site `d`. -/
def latticeLag (φ : ℝ → ℝ) (h : ℝ) (d : ℤ) (x : ℝ) : ℝ := ∫ u, φ u * φ (u - x + d * h)

theorem weilTest_latticeTranslate (φ : ℝ → ℝ) (h : ℝ) (d : ℤ) (x : ℝ) :
    EF.weilTest (cx φ) (cx (latticeTranslate φ h d)) x = (latticeLag φ h d x : ℂ) := by
  rw [RHTower.WeilSpectral.weilTest_apply, latticeLag, ← integral_complex_ofReal]
  refine integral_congr_ae (Eventually.of_forall fun u => ?_)
  simp only [cx, latticeTranslate, Complex.conj_ofReal, Complex.ofReal_mul]

/-- The lattice lag vanishes outside the band `|x − dh| ≤ r`. -/
theorem latticeLag_eq_zero (hφ : ∀ y, y ∉ Icc (-r) 0 → φ y = 0) (d : ℤ) {x : ℝ}
    (hx : r < |x - d * h|) : latticeLag φ h d x = 0 := by
  have hz : (fun u => φ u * φ (u - x + d * h)) = fun _ => 0 := by
    funext u
    by_cases hu : u ∈ Icc (-r) 0
    · rw [hφ (u - x + d * h) fun hm => ?_, mul_zero]
      have : |x - d * h| ≤ r := by
        rw [abs_le]; constructor <;> linarith [hu.1, hu.2, hm.1, hm.2]
      linarith
    · rw [hφ u hu, zero_mul]
  rw [latticeLag, hz, integral_zero]

/-- The full Weil functional does not see weights at nodes where the test vanishes. -/
theorem weilFullFunctional_congr_of_vanish {lam lam' : ℕ → ℝ} {k : ℝ → ℂ}
    (hk : ∀ n : ℕ, 2 ≤ n → lam n ≠ lam' n → k (Real.log n) = 0 ∧ k (-Real.log n) = 0) :
    RHTower.weilFullFunctional lam k = RHTower.weilFullFunctional lam' k := by
  unfold RHTower.weilFullFunctional
  congr 2
  refine tsum_congr fun n => ?_
  by_cases hn : 2 ≤ n
  · by_cases he : lam n = lam' n
    · rw [he]
    · obtain ⟨h1, h2⟩ := hk n hn he
      rw [h1, h2, add_zero, mul_zero, mul_zero]
  · rw [if_neg hn, if_neg hn]

/-- `log n` beyond `|dh| + r` puts both lags `±log n` outside the band of the site `d`. -/
theorem latticeLag_log_eq_zero (hφ : ∀ y, y ∉ Icc (-r) 0 → φ y = 0) (d : ℤ) {n : ℕ}
    (hn : |(d : ℝ) * h| + r < Real.log n) :
    latticeLag φ h d (Real.log n) = 0 ∧ latticeLag φ h d (-Real.log n) = 0 := by
  have hb := neg_abs_le ((d : ℝ) * h)
  have ha := le_abs_self ((d : ℝ) * h)
  refine ⟨latticeLag_eq_zero hφ d ?_, latticeLag_eq_zero hφ d ?_⟩
  · exact lt_of_lt_of_le (by linarith) (le_abs_self _)
  · exact lt_of_lt_of_le (by linarith) (neg_le_abs _)

/-- **Locality.** `κ^λ(d)` reads only the weights of the `n` with `log n ≤ |dh| + r`. -/
theorem weilSeqW_congr (hφ : ∀ y, y ∉ Icc (-r) 0 → φ y = 0) {lam lam' : ℕ → ℝ} {d : ℤ}
    (hlam : ∀ m : ℕ, 2 ≤ m → Real.log m ≤ |(d : ℝ) * h| + r → lam m = lam' m) :
    weilSeqW lam φ h d = weilSeqW lam' φ h d := by
  unfold weilSeqW
  rw [weilFullFunctional_congr_of_vanish fun n hn hne => ?_]
  have hlog : |(d : ℝ) * h| + r < Real.log n := by
    by_contra hc; exact hne (hlam n hn (not_lt.mp hc))
  obtain ⟨h1, h2⟩ := latticeLag_log_eq_zero hφ d hlog
  rw [weilTest_latticeTranslate, weilTest_latticeTranslate, h1, h2]
  exact ⟨Complex.ofReal_zero, Complex.ofReal_zero⟩

/-- **Causality.** The margin and predictor of size `n` read only the prime powers `m ≤ e^{nh + r}`. -/
theorem levinson_weilSeqW_congr (hφ : ∀ y, y ∉ Icc (-r) 0 → φ y = 0) (hh : 0 ≤ h)
    {lam lam' : ℕ → ℝ} {n : ℕ}
    (hlam : ∀ m : ℕ, 2 ≤ m → Real.log m ≤ n * h + r → lam m = lam' m) :
    levinson (weilSeqW lam φ h) n = levinson (weilSeqW lam' φ h) n :=
  levinson_congr n fun d hd => weilSeqW_congr hφ fun m hm hlog => hlam m hm (by
    have hdn : (d : ℝ) ≤ n := by exact_mod_cast hd
    have : |((d : ℤ) : ℝ) * h| = (d : ℝ) * h := by
      rw [abs_of_nonneg (by push_cast; positivity)]; push_cast; ring
    rw [this] at hlog
    nlinarith)

/-- **One kick.** If `λ` and `λ'` differ only at the prime power `n₀ ≥ 2`, then
`κ^λ(d) − κ^{λ'}(d) = −((λ(n₀) − λ'(n₀))/√n₀)(k_d(log n₀) + k_d(−log n₀))`. -/
theorem weilSeqW_single_kick (hφ : ∀ y, y ∉ Icc (-r) 0 → φ y = 0) {lam lam' : ℕ → ℝ} {n₀ : ℕ}
    (hn₀ : 2 ≤ n₀) (hlam : ∀ m : ℕ, m ≠ n₀ → lam m = lam' m) (d : ℤ) :
    weilSeqW lam φ h d - weilSeqW lam' φ h d =
      -((lam n₀ - lam' n₀) / Real.sqrt n₀) *
        (latticeLag φ h d (Real.log n₀) + latticeLag φ h d (-Real.log n₀)) := by
  set k := EF.weilTest (cx φ) (cx (latticeTranslate φ h d))
  set N := ⌈Real.exp (|(d : ℝ) * h| + r)⌉₊
  -- the prime terms vanish beyond `N`
  have hbig : ∀ n : ℕ, N < n → k (Real.log n) = 0 ∧ k (-Real.log n) = 0 := fun n hn => by
    have hN : Real.exp (|(d : ℝ) * h| + r) < n := lt_of_le_of_lt (Nat.le_ceil _) (by exact_mod_cast hn)
    have hlog : |(d : ℝ) * h| + r < Real.log n := by
      rw [Real.lt_log_iff_exp_lt (lt_trans (Real.exp_pos _) hN)]; exact hN
    obtain ⟨h1, h2⟩ := latticeLag_log_eq_zero hφ d hlog
    simp only [k, weilTest_latticeTranslate, h1, h2, Complex.ofReal_zero, and_self]
  set c : (ℕ → ℝ) → ℕ → ℂ := fun l n =>
    ((if 2 ≤ n then l n / Real.sqrt n else 0 : ℝ) : ℂ) * (k (Real.log n) + k (-Real.log n))
  have hfin : ∀ l : ℕ → ℝ, ∑' n : ℕ, c l n = ∑ n ∈ range (N + 1), c l n := fun l =>
    tsum_eq_sum fun n hn => by
      have hn' : N < n := by simpa using hn
      obtain ⟨h1, h2⟩ := hbig n hn'
      simp only [c, h1, h2, add_zero, mul_zero]
  have hdiff : ∑ n ∈ range (N + 1), c lam n - ∑ n ∈ range (N + 1), c lam' n =
      c lam n₀ - c lam' n₀ := by
    rw [← sum_sub_distrib]
    refine sum_eq_single n₀ (fun n _ hne => ?_) (fun hn => ?_)
    · simp only [c, hlam n hne, sub_self]
    · have hn' : N < n₀ := by simpa using hn
      obtain ⟨h1, h2⟩ := hbig n₀ hn'
      simp only [c, h1, h2, add_zero, mul_zero, sub_self]
  have hk1 : k (Real.log n₀) = (latticeLag φ h d (Real.log n₀) : ℂ) :=
    weilTest_latticeTranslate φ h d _
  have hk2 : k (-Real.log n₀) = (latticeLag φ h d (-Real.log n₀) : ℂ) :=
    weilTest_latticeTranslate φ h d _
  unfold weilSeqW
  simp only [RHTower.weilFullFunctional]
  rw [← Complex.sub_re]
  have e : ∀ (P G : ℂ) (S S' : ℂ), P - S + G - (P - S' + G) = -(S - S') := fun _ _ _ _ => by ring
  rw [e, show (∑' n : ℕ, ((if 2 ≤ n then lam n / Real.sqrt n else 0 : ℝ) : ℂ) *
        (k (Real.log n) + k (-Real.log n))) = ∑' n : ℕ, c lam n from rfl,
    show (∑' n : ℕ, ((if 2 ≤ n then lam' n / Real.sqrt n else 0 : ℝ) : ℂ) *
        (k (Real.log n) + k (-Real.log n))) = ∑' n : ℕ, c lam' n from rfl,
    hfin, hfin, hdiff]
  simp only [c, if_pos hn₀, hk1, hk2]
  simp only [Complex.neg_re, Complex.sub_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    Complex.add_re, Complex.add_im, zero_mul, sub_zero]
  ring

/-- **A kick moves one Schur parameter.** If `λ` and `λ'` differ only at the prime power `n₀`, and the
lattice stage `m` satisfies `mh + r < log n₀`, then the evolutions agree up to size `m` (margins,
predictors, frozen predictions), and `β_m` moves by `−δλ(n₀)n₀^{−1/2}k_{m+1}(log n₀)`. -/
theorem schurParam_single_kick (hφ : ∀ y, y ∉ Icc (-r) 0 → φ y = 0) (hh : 0 < h)
    {lam lam' : ℕ → ℝ} {n₀ : ℕ} (hn₀ : 2 ≤ n₀) (hlam : ∀ m : ℕ, m ≠ n₀ → lam m = lam' m)
    {m : ℕ} (hm : (m : ℝ) * h + r < Real.log n₀) :
    levinson (weilSeqW lam φ h) m = levinson (weilSeqW lam' φ h) m ∧
      schurParam (weilSeqW lam φ h) m - schurParam (weilSeqW lam' φ h) m =
        -((lam n₀ - lam' n₀) / Real.sqrt n₀) * latticeLag φ h ((m : ℤ) + 1) (Real.log n₀) := by
  -- the frozen data `κ(0), …, κ(m)` do not see `n₀`
  have hagree : ∀ d : ℕ, d ≤ m → weilSeqW lam φ h d = weilSeqW lam' φ h d := fun d hd =>
    weilSeqW_congr hφ fun k _ hk => by
      by_cases hkn : k = n₀
      · subst hkn
        have hdm : (d : ℝ) ≤ m := by exact_mod_cast hd
        have : |((d : ℤ) : ℝ) * h| = (d : ℝ) * h := by
          rw [abs_of_nonneg (by push_cast; positivity)]; push_cast; ring
        rw [this] at hk
        nlinarith
      · exact hlam k hkn
  have hlev : levinson (weilSeqW lam φ h) m = levinson (weilSeqW lam' φ h) m :=
    levinson_congr m hagree
  refine ⟨hlev, ?_⟩
  rw [schurParam_eq, schurParam_eq]
  simp only [levinsonPred]
  rw [hlev]
  have hfp : frozenPrediction (weilSeqW lam φ h) m (levinson (weilSeqW lam' φ h) m).2 =
      frozenPrediction (weilSeqW lam' φ h) m (levinson (weilSeqW lam' φ h) m).2 := by
    unfold frozenPrediction
    congr 1
    refine sum_congr rfl fun k _ => ?_
    have hk : (k : ℕ) < m := k.isLt
    have := hagree ((k : ℕ) + 1) (by omega)
    push_cast at this
    rw [this]
  rw [hfp]
  have hkick := weilSeqW_single_kick (h := h) hφ hn₀ hlam ((m : ℤ) + 1)
  have hneg : latticeLag φ h ((m : ℤ) + 1) (-Real.log n₀) = 0 := by
    refine latticeLag_eq_zero hφ _ ?_
    have hlogpos : 0 < Real.log n₀ := Real.log_pos (by exact_mod_cast hn₀)
    have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    rw [abs_of_neg (by push_cast; nlinarith)]
    push_cast
    nlinarith
  rw [hneg, add_zero] at hkick
  linarith

end GaloisForLFunctions.GrowingWindowsOfSpecZ
