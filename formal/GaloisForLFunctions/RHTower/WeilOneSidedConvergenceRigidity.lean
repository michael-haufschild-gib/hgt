import GaloisForLFunctions.RHTower.LogWindowPrimeNumberTheorem
import GaloisForLFunctions.RHTower.WeilFullConeCompactness
import GaloisForLFunctions.RHTower.WeilAbsoluteConvergenceRigidity
import GaloisForLFunctions.HTGeometry.SubexponentialSqrtSummable

/-!
# One-sided convergence rigidity of the Weil cone

**Theorem.** Let `lam` be full-cone Weil-positive.
- `eq_vonMangoldt_of_weilPositiveFull_of_summable_excess_div`: if
  `Σ_n max(lam(n) − Λ(n), 0)/n < ∞`, then `lam(n) = Λ(n)` for every `n ≥ 2`.
- `eq_vonMangoldt_of_weilPositiveFull_of_summable_deficit_div`: the same conclusion holds if
  `Σ_n max(Λ(n) − lam(n), 0)/n < ∞`.

So every Weil-positive `lam ≠ Λ` has both its excess and its deficit over `Λ` non-summable
against `1/n`.

**Proof.** Put `d = lam − Λ` on `n ≥ 2`, let `ρ` be the autocorrelation of a nonnegative bump,
and set `φ(x) = ρ(x) e^{x/2}`. The harmonic log-windows `W(L) = Σ_n d(n) φ(log n − L)/n` equal
`e^{−L/2}(S_L(lam) − S_L(Λ))`. Window pinning bounds `S_L(lam)`, and the smoothed prime number
theorem bounds `S_L(Λ)`, each around `2P₊P₋ cosh(L/2)`. Hence
`|W(L)| ≪ e^{−L/2} + e^{−√L/1920000}`, which is summable along `L = kδ`
(`summable_abs_windows`).
- Since `φ ≥ c₀ > 0` on `[−δ/2, δ/2]`, the translates `φ(· − kδ)` cover every `log n`. Each
  point lies in at most `⌊1/δ⌋ + 1` of their supports.
- Writing `d⁻ = d⁺ − d` window by window gives
  `c₀ Σ d⁻(n)/n ≤ (⌊1/δ⌋ + 1) sup φ · Σ d⁺(n)/n + Σ_k |W(kδ)|`
  (`summable_abs_div_of_windows`).
- Therefore `Σ |d(n)|/n < ∞`, and absolute-convergence rigidity at `s = 1` finishes.
-/

noncomputable section

open MeasureTheory Set Filter Topology
open scoped Real

namespace RHTower.WeilOneSided

/-! ## One-sided to two-sided transfer -/

theorem sum_range_eq_of_vanish {f : ℕ → ℝ} {N₀ N : ℕ} (hN : N₀ ≤ N)
    (hf : ∀ n, N₀ ≤ n → f n = 0) :
    ∑ n ∈ Finset.range N, f n = ∑ n ∈ Finset.range N₀, f n :=
  (Finset.sum_subset (Finset.range_subset_range.mpr hN) fun n _ hn' =>
    hf n (by simpa using hn')).symm

/-- A profile supported in `[−½, ½]` has `Σ_n f(n) φ(log n − L)/n` independent of the cutoff
`N ≥ e^{L+1}`. -/
theorem sum_range_profile_eq {φ : ℝ → ℝ} (hφs : ∀ x, 1 / 2 < |x| → φ x = 0) (f : ℕ → ℝ) (L : ℝ)
    {N : ℕ} (hN : ⌈Real.exp (L + 1)⌉₊ ≤ N) :
    ∑ n ∈ Finset.range N, f n * φ (Real.log n - L) / n =
      ∑ n ∈ Finset.range ⌈Real.exp (L + 1)⌉₊, f n * φ (Real.log n - L) / n := by
  refine sum_range_eq_of_vanish hN fun n hn => ?_
  have h1 : Real.exp (L + 1) ≤ n := (Nat.ceil_le.mp hn)
  have hn0 : (0 : ℝ) < n := lt_of_lt_of_le (Real.exp_pos _) h1
  have h2 : L + 1 ≤ Real.log n := (Real.le_log_iff_exp_le hn0).mpr h1
  rw [hφs _ (by rw [abs_of_pos (by linarith)]; linarith), mul_zero, zero_div]

/-- Each point lies in the supports of at most `⌊1/δ⌋ + 1` translates `φ(· − kδ)`. -/
theorem sum_range_profile_le {φ : ℝ → ℝ} {H δ : ℝ} (hδ : 0 < δ) (hφH : ∀ x, φ x ≤ H)
    (hφs : ∀ x, 1 / 2 < |x| → φ x = 0) (hH0 : 0 ≤ H) (u : ℝ) (K : ℕ) :
    ∑ k ∈ Finset.range K, φ (u - k * δ) ≤ H * (⌊1 / δ⌋₊ + 1) := by
  set a := ⌈(u - 1 / 2) / δ⌉₊ with ha
  set m := ⌊1 / δ⌋₊ with hm
  set S := (Finset.range K).filter (fun k : ℕ => |u - k * δ| ≤ 1 / 2) with hS
  have hsub : S ⊆ Finset.Icc a (a + m) := by
    intro k hk
    rw [hS, Finset.mem_filter, abs_le] at hk
    obtain ⟨-, hk1, hk2⟩ := hk
    rw [Finset.mem_Icc]
    have hl : (u - 1 / 2) / δ ≤ k := by rw [div_le_iff₀ hδ]; linarith
    have hr : (k : ℝ) ≤ (u + 1 / 2) / δ := by rw [le_div_iff₀ hδ]; linarith
    have hak : a ≤ k := Nat.ceil_le.mpr hl
    refine ⟨hak, ?_⟩
    have hac : (u - 1 / 2) / δ ≤ a := Nat.le_ceil _
    have hdiff : (u + 1 / 2) / δ - (u - 1 / 2) / δ = 1 / δ := by field_simp; ring
    have hkm : ((k - a : ℕ) : ℝ) ≤ 1 / δ := by
      rw [Nat.cast_sub hak]; linarith
    have := Nat.le_floor hkm
    omega
  have hcard : (S.card : ℝ) ≤ m + 1 := by
    have h := Finset.card_le_card hsub
    rw [Nat.card_Icc, show a + m + 1 - a = m + 1 by omega] at h
    exact_mod_cast h
  calc ∑ k ∈ Finset.range K, φ (u - k * δ) = ∑ k ∈ S, φ (u - k * δ) := by
        rw [hS, Finset.sum_filter]
        refine Finset.sum_congr rfl fun k _ => ?_
        split_ifs with h
        · rfl
        · exact hφs _ (not_le.mp h)
    _ ≤ ∑ _k ∈ S, H := Finset.sum_le_sum fun k _ => hφH _
    _ = H * S.card := by rw [Finset.sum_const, nsmul_eq_mul, mul_comm]
    _ ≤ H * (m + 1) := mul_le_mul_of_nonneg_left hcard hH0

/-- **One-sided to two-sided transfer at weight `1/n`.** Let `φ ≥ 0` be bounded by `H`, supported
in `[−½, ½]`, with `φ ≥ c₀ > 0` on `[−δ/2, δ/2]`. If the harmonic log-windows
`W_k = Σ_n d(n) φ(log n − kδ)/n` are absolutely summable in `k` and `Σ_n max(d(n), 0)/n < ∞`, then
`Σ_n |d(n)|/n < ∞`. -/
theorem summable_abs_div_of_windows {φ : ℝ → ℝ} {H δ c₀ : ℝ} (hδ : 0 < δ) (hc₀ : 0 < c₀)
    (hφ0 : ∀ x, 0 ≤ φ x) (hφH : ∀ x, φ x ≤ H) (hφs : ∀ x, 1 / 2 < |x| → φ x = 0)
    (hφc : ∀ x, |x| ≤ δ / 2 → c₀ ≤ φ x) (d : ℕ → ℝ)
    (hW : Summable fun k : ℕ => |∑ n ∈ Finset.range ⌈Real.exp (k * δ + 1)⌉₊,
      d n * φ (Real.log n - k * δ) / n|)
    (hpos : Summable fun n : ℕ => max (d n) 0 / n) :
    Summable fun n : ℕ => |d n| / n := by
  set dm : ℕ → ℝ := fun n => max (-d n) 0 with hdm
  set dp : ℕ → ℝ := fun n => max (d n) 0 with hdp
  have hdm0 : ∀ n, 0 ≤ dm n := fun n => le_max_right _ _
  have hdp0 : ∀ n, 0 ≤ dp n := fun n => le_max_right _ _
  have hsplit : ∀ n, dm n = dp n - d n := fun n => by
    simp only [hdm, hdp]
    rcases le_total (d n) 0 with h | h
    · rw [max_eq_left (by linarith), max_eq_right h]; ring
    · rw [max_eq_right (by linarith), max_eq_left h]; ring
  have hH0 : 0 ≤ H := (hφ0 0).trans (hφH 0)
  set R := H * (⌊1 / δ⌋₊ + 1) with hR
  have hR0 : 0 ≤ R := by positivity
  set W : ℕ → ℝ := fun k => ∑ n ∈ Finset.range ⌈Real.exp (k * δ + 1)⌉₊,
    d n * φ (Real.log n - k * δ) / n with hWdef
  set SP := ∑' n, dp n / n with hSP
  set SW := ∑' k, |W k| with hSW
  have hneg : Summable fun n : ℕ => dm n / n := by
    refine summable_of_sum_range_le (c := (R * SP + SW) / c₀)
      (fun n => div_nonneg (hdm0 n) (Nat.cast_nonneg n)) fun N => ?_
    set K := ⌊Real.log N / δ + 1 / 2⌋₊ + 1 with hK
    set Ns := max N ⌈Real.exp (K * δ + 1)⌉₊ with hNs
    have hterm : ∀ n ∈ Finset.range N, dm n / n ≤
        (∑ k ∈ Finset.range K, dm n * φ (Real.log n - k * δ) / n) / c₀ := by
      intro n hn
      rw [Finset.mem_range] at hn
      rcases Nat.eq_zero_or_pos n with rfl | hn1
      · simp
      have hn0 : (0 : ℝ) < n := by exact_mod_cast hn1
      have hlog0 : 0 ≤ Real.log n := Real.log_nonneg (by exact_mod_cast hn1)
      set k₀ := ⌊Real.log n / δ + 1 / 2⌋₊ with hk₀
      have hx0 : 0 ≤ Real.log n / δ + 1 / 2 := by positivity
      have hk1 := Nat.floor_le hx0
      have hk2 := Nat.lt_floor_add_one (Real.log n / δ + 1 / 2)
      rw [← hk₀] at hk1 hk2
      have hloc : |Real.log n - k₀ * δ| ≤ δ / 2 := by
        have e1 : (k₀ : ℝ) * δ ≤ Real.log n + δ / 2 := by
          have := mul_le_mul_of_nonneg_right hk1 hδ.le
          rw [add_mul, div_mul_cancel₀ _ hδ.ne'] at this; linarith
        have e2 : Real.log n - δ / 2 < (k₀ : ℝ) * δ := by
          have := mul_lt_mul_of_pos_right hk2 hδ
          rw [add_mul, add_mul, div_mul_cancel₀ _ hδ.ne'] at this; linarith
        rw [abs_le]; constructor <;> linarith
      have hk₀K : k₀ ∈ Finset.range K := by
        rw [Finset.mem_range, hK, Nat.lt_succ_iff]
        refine Nat.floor_le_floor ?_
        have : Real.log n ≤ Real.log N :=
          Real.log_le_log hn0 (by exact_mod_cast hn.le)
        have : Real.log n / δ ≤ Real.log N / δ := div_le_div_of_nonneg_right this hδ.le
        linarith
      have hsingle : dm n * φ (Real.log n - k₀ * δ) / n ≤
          ∑ k ∈ Finset.range K, dm n * φ (Real.log n - k * δ) / n :=
        Finset.single_le_sum (f := fun k : ℕ => dm n * φ (Real.log n - k * δ) / n)
          (fun k _ => div_nonneg (mul_nonneg (hdm0 n) (hφ0 _)) hn0.le) hk₀K
      rw [le_div_iff₀ hc₀]
      calc dm n / n * c₀ ≤ dm n * φ (Real.log n - k₀ * δ) / n := by
            rw [div_mul_eq_mul_div]
            exact div_le_div_of_nonneg_right
              (mul_le_mul_of_nonneg_left (hφc _ hloc) (hdm0 n)) hn0.le
        _ ≤ _ := hsingle
    have hNN : N ≤ Ns := le_max_left _ _
    have hcov : ∀ k ∈ Finset.range K, ⌈Real.exp (k * δ + 1)⌉₊ ≤ Ns := by
      intro k hk
      rw [Finset.mem_range] at hk
      refine le_trans (Nat.ceil_mono (Real.exp_le_exp.mpr ?_)) (le_max_right _ _)
      have : (k : ℝ) ≤ K := by exact_mod_cast hk.le
      nlinarith
    have hwin : ∀ k ∈ Finset.range K,
        ∑ n ∈ Finset.range N, dm n * φ (Real.log n - k * δ) / n ≤
          ∑ n ∈ Finset.range Ns, (dp n / n) * φ (Real.log n - k * δ) + |W k| := by
      intro k hk
      have hmono : ∑ n ∈ Finset.range N, dm n * φ (Real.log n - k * δ) / n ≤
          ∑ n ∈ Finset.range Ns, dm n * φ (Real.log n - k * δ) / n :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_subset_range.mpr hNN)
          fun n _ _ => div_nonneg (mul_nonneg (hdm0 n) (hφ0 _)) (Nat.cast_nonneg n)
      have hWk : ∑ n ∈ Finset.range Ns, d n * φ (Real.log n - k * δ) / n = W k :=
        sum_range_profile_eq hφs d (k * δ) (hcov k hk)
      have hexp : ∑ n ∈ Finset.range Ns, dm n * φ (Real.log n - k * δ) / n =
          ∑ n ∈ Finset.range Ns, (dp n / n) * φ (Real.log n - k * δ) -
            ∑ n ∈ Finset.range Ns, d n * φ (Real.log n - k * δ) / n := by
        rw [← Finset.sum_sub_distrib]
        refine Finset.sum_congr rfl fun n _ => ?_
        rw [hsplit]; ring
      rw [hexp, hWk] at hmono
      linarith [neg_abs_le (W k)]
    calc ∑ n ∈ Finset.range N, dm n / n
        ≤ ∑ n ∈ Finset.range N,
            (∑ k ∈ Finset.range K, dm n * φ (Real.log n - k * δ) / n) / c₀ :=
          Finset.sum_le_sum hterm
      _ = (∑ k ∈ Finset.range K,
            ∑ n ∈ Finset.range N, dm n * φ (Real.log n - k * δ) / n) / c₀ := by
          rw [← Finset.sum_div, Finset.sum_comm]
      _ ≤ (∑ k ∈ Finset.range K,
            (∑ n ∈ Finset.range Ns, (dp n / n) * φ (Real.log n - k * δ) + |W k|)) / c₀ :=
          div_le_div_of_nonneg_right (Finset.sum_le_sum hwin) hc₀.le
      _ = ((∑ n ∈ Finset.range Ns, (dp n / n) * ∑ k ∈ Finset.range K,
              φ (Real.log n - k * δ)) + ∑ k ∈ Finset.range K, |W k|) / c₀ := by
          rw [Finset.sum_add_distrib, Finset.sum_comm]
          simp_rw [Finset.mul_sum]
      _ ≤ (R * SP + SW) / c₀ := by
          refine div_le_div_of_nonneg_right (add_le_add ?_ ?_) hc₀.le
          · calc ∑ n ∈ Finset.range Ns, (dp n / n) * ∑ k ∈ Finset.range K,
                  φ (Real.log n - k * δ)
                ≤ ∑ n ∈ Finset.range Ns, (dp n / n) * R :=
                  Finset.sum_le_sum fun n _ => mul_le_mul_of_nonneg_left
                    (sum_range_profile_le hδ hφH hφs hH0 _ K)
                    (div_nonneg (hdp0 n) (Nat.cast_nonneg n))
              _ = R * ∑ n ∈ Finset.range Ns, dp n / n := by
                  rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun n _ => mul_comm _ _
              _ ≤ R * SP := mul_le_mul_of_nonneg_left
                  (hpos.sum_le_tsum _ fun n _ => div_nonneg (hdp0 n) (Nat.cast_nonneg n)) hR0
          · exact hW.sum_le_tsum _ fun k _ => abs_nonneg _
  refine (hpos.add hneg).congr fun n => ?_
  simp only [hdm]
  rw [← add_div]
  congr 1
  rcases le_total (d n) 0 with h | h
  · rw [max_eq_right h, max_eq_left (by linarith), abs_of_nonpos h]; ring
  · rw [max_eq_left h, max_eq_right (by linarith), abs_of_nonneg h]; ring

/-! ## The harmonic windows of a Weil-positive sequence -/

/-- The harmonic profile `φ(x) = ρ(x) e^{x/2}`. -/
def harmonicProfile (g : ℝ → ℝ) (x : ℝ) : ℝ := autoCorr g x * Real.exp (x / 2)

theorem exp_mul_windowValue_eq {g : ℝ → ℝ} (hsupp : ∀ u, 1 / 4 < |u| → g u = 0) {L : ℝ}
    (hL : 1 ≤ L) (n : ℕ) :
    Real.exp (-(L / 2)) * windowValue g L n = harmonicProfile g (Real.log n - L) / n := by
  rw [windowValue_eq_logWindow hsupp hL, logWindow, harmonicProfile]
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · have h1 : autoCorr g (-L) = 0 :=
      autoCorr_eq_zero hsupp (by rw [abs_neg, abs_of_pos (by linarith)]; linarith)
    simp [h1]
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  set ℓ := Real.log n with hℓ
  have hnℓ : (n : ℝ) = Real.exp ℓ := (Real.exp_log hn0).symm
  rw [hnℓ, eq_div_iff (Real.exp_pos _).ne']
  have e : Real.exp (-(L / 2)) * Real.exp (-ℓ / 2) * Real.exp ℓ = Real.exp ((ℓ - L) / 2) := by
    rw [← Real.exp_add, ← Real.exp_add]; ring_nf
  linear_combination (autoCorr g (ℓ - L)) * e

/-- The harmonic window of `lam` (restricted to `n ≥ 2`) is `e^{−L/2} S_L(lam)`. -/
theorem sum_harmonicProfile_eq_windowSum {g : ℝ → ℝ} (hg : ContDiff ℝ 2 g)
    (hgc : HasCompactSupport g) (hsupp : ∀ u, 1 / 4 < |u| → g u = 0) (lam : ℕ → ℝ) {L : ℝ}
    (hL : 1 ≤ L) {N : ℕ} (hN : Real.exp (L + 1) ≤ N) :
    ∑ n ∈ Finset.range N, (if 2 ≤ n then lam n else 0) * harmonicProfile g (Real.log n - L) / n =
      Real.exp (-(L / 2)) * windowSum hg hgc hsupp lam L := by
  rw [windowSum_eq_sum hg hgc hsupp lam (M := N) (by rw [abs_of_pos (by linarith)]; exact hN),
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun n _ => ?_
  split_ifs with h
  · rw [mul_div_assoc, ← exp_mul_windowValue_eq hsupp hL n]; ring
  · simp

/-- Window pinning and the smoothed prime number theorem together: the windows of `lam − Λ` are
`O(1 + e^{L/2} e^{−√L/1920000})`, uniformly over the Weil cone. -/
theorem exists_abs_windowSum_sub_vonMangoldt_le {g : ℝ → ℝ} (hg : ContDiff ℝ 2 g)
    (hgc : HasCompactSupport g) (hsupp : ∀ u, 1 / 4 < |u| → g u = 0) :
    ∃ C L₀ : ℝ, 0 ≤ C ∧ ∀ lam : ℕ → ℝ, WeilPositiveFull lam → ∀ L, L₀ ≤ L →
      |windowSum hg hgc hsupp (fun n => lam n - ArithmeticFunction.vonMangoldt n) L| ≤
        C * (1 + Real.exp (L / 2) * Real.exp (-(Real.sqrt L / 1920000))) := by
  obtain ⟨Cp, hCp⟩ := exists_abs_windowSum_sub_le hg hgc hsupp
  obtain ⟨C', L₀, hC'⟩ := exists_abs_windowSum_vonMangoldt_sub_le hg hgc hsupp
  have hC'0 : 0 ≤ C' := by
    have h := hC' L₀ le_rfl
    have hpos : 0 < 1 + Real.exp (L₀ / 2) * Real.exp (-(Real.sqrt L₀ / 1920000)) := by positivity
    by_contra hneg
    have : C' * (1 + Real.exp (L₀ / 2) * Real.exp (-(Real.sqrt L₀ / 1920000))) < 0 :=
      mul_neg_of_neg_of_pos (not_le.mp hneg) hpos
    linarith [abs_nonneg (windowSum hg hgc hsupp
      (fun n => (ArithmeticFunction.vonMangoldt n : ℝ)) L₀ -
        2 * (∫ u, g u * Real.exp (-u / 2)) * (∫ u, g u * Real.exp (u / 2)) *
          Real.cosh (L₀ / 2))]
  refine ⟨|Cp| + C', L₀, by positivity, fun lam hW L hL => ?_⟩
  have h1 := hCp lam hW L
  have h2 := hC' L hL
  rw [← windowSum_sub]
  have hE : 0 ≤ Real.exp (L / 2) * Real.exp (-(Real.sqrt L / 1920000)) := by positivity
  have hCp' : Cp ≤ |Cp| * (1 + Real.exp (L / 2) * Real.exp (-(Real.sqrt L / 1920000))) := by
    nlinarith [le_abs_self Cp, abs_nonneg Cp, mul_nonneg (abs_nonneg Cp) hE]
  set main := 2 * (∫ u, g u * Real.exp (-u / 2)) * (∫ u, g u * Real.exp (u / 2)) *
    Real.cosh (L / 2) with hmain
  calc |windowSum hg hgc hsupp lam L -
        windowSum hg hgc hsupp (fun n => (ArithmeticFunction.vonMangoldt n : ℝ)) L|
      ≤ |windowSum hg hgc hsupp lam L - main| +
        |main - windowSum hg hgc hsupp (fun n => (ArithmeticFunction.vonMangoldt n : ℝ)) L| :=
        abs_sub_le _ _ _
    _ = |windowSum hg hgc hsupp lam L - main| +
        |windowSum hg hgc hsupp (fun n => (ArithmeticFunction.vonMangoldt n : ℝ)) L - main| := by
        rw [abs_sub_comm main]
    _ ≤ Cp + C' * (1 + Real.exp (L / 2) * Real.exp (-(Real.sqrt L / 1920000))) := add_le_add h1 h2
    _ ≤ (|Cp| + C') * (1 + Real.exp (L / 2) * Real.exp (-(Real.sqrt L / 1920000))) := by
        rw [add_mul]; linarith

/-- The restriction `d(n) = lam(n) − Λ(n)` for `n ≥ 2`, and `0` for `n < 2`. -/
def coneDeviation (lam : ℕ → ℝ) (n : ℕ) : ℝ :=
  if 2 ≤ n then lam n - ArithmeticFunction.vonMangoldt n else 0

/-- **A profile with summable harmonic windows.** There is one profile `φ ≥ 0`, bounded,
supported in `[−½, ½]`, with `φ ≥ c₀ > 0` on `[−δ/2, δ/2]`, such that every full-cone
Weil-positive `lam` has absolutely summable harmonic windows `Σ_n d(n) φ(log n − kδ)/n`. -/
theorem exists_profile_summable_windows :
    ∃ (φ : ℝ → ℝ) (H δ c₀ : ℝ), 0 < δ ∧ 0 < c₀ ∧ (∀ x, 0 ≤ φ x) ∧ (∀ x, φ x ≤ H) ∧
      (∀ x, 1 / 2 < |x| → φ x = 0) ∧ (∀ x, |x| ≤ δ / 2 → c₀ ≤ φ x) ∧
      ∀ lam : ℕ → ℝ, WeilPositiveFull lam →
        Summable fun k : ℕ => |∑ n ∈ Finset.range ⌈Real.exp (k * δ + 1)⌉₊,
          coneDeviation lam n * φ (Real.log n - k * δ) / n| := by
  set g := narrowG 0 with hgdef
  have hg := contDiff_narrowG 0
  have hgc := hasCompactSupport_narrowG 0
  have hsupp := narrowG_supp 0
  have hg0 : ∀ u, 0 ≤ g u := fun u => (narrowBump 0).nonneg
  obtain ⟨Kρ, Hρ, hK0, hH0, hK, hH, hcont⟩ := exists_autoCorr_constants hg hgc
  set φ := harmonicProfile g with hφdef
  have hφ0 : ∀ x, 0 ≤ φ x := fun x => mul_nonneg (autoCorr_nonneg_of_nonneg hg0 x) (Real.exp_pos _).le
  have hφs : ∀ x, 1 / 2 < |x| → φ x = 0 := fun x hx => by
    rw [hφdef, harmonicProfile, autoCorr_eq_zero hsupp hx, zero_mul]
  have hφH : ∀ x, φ x ≤ Hρ * Real.exp (1 / 4) := by
    intro x
    rcases le_or_gt |x| (1 / 2) with hx | hx
    · have hx2 : x / 2 ≤ 1 / 4 := by linarith [le_abs_self x]
      exact mul_le_mul ((le_abs_self _).trans (hH x)) (Real.exp_le_exp.mpr hx2)
        (Real.exp_pos _).le hH0
    · rw [hφs x hx]; positivity
  have hφc : Continuous φ := by
    rw [hφdef]; unfold harmonicProfile; fun_prop
  have hφ00 : 0 < φ 0 := by
    rw [hφdef, harmonicProfile, zero_div, Real.exp_zero, mul_one]
    exact autoCorr_narrowG_zero_pos 0
  obtain ⟨η, hη, hηφ⟩ := Metric.continuousAt_iff.mp hφc.continuousAt (φ 0 / 2) (by positivity)
  have hloc : ∀ x, |x| ≤ η / 2 → φ 0 / 2 ≤ φ x := by
    intro x hx
    have hd : dist x 0 < η := by rw [Real.dist_eq, sub_zero]; linarith
    have := hηφ hd
    rw [Real.dist_eq] at this
    linarith [neg_abs_le (φ x - φ 0)]
  obtain ⟨C, L₀, hC0, hC⟩ := exists_abs_windowSum_sub_vonMangoldt_le hg hgc hsupp
  refine ⟨φ, Hρ * Real.exp (1 / 4), η, φ 0 / 2, hη, by positivity, hφ0, hφH, hφs, hloc,
    fun lam hW => ?_⟩
  set b : ℕ → ℝ := fun k => C * Real.exp (k * (-(η / 2))) +
    C * Real.exp (-(Real.sqrt η / 1920000 * Real.sqrt k)) with hb
  have hbs : Summable b :=
    ((Real.summable_exp_nat_mul_iff.mpr (by linarith)).mul_left C).add
      ((GaloisForLFunctions.HTGeometry.summable_exp_neg_mul_sqrt
        (a := Real.sqrt η / 1920000) (by positivity)).mul_left C)
  refine Summable.of_norm_bounded_eventually hbs ?_
  rw [Nat.cofinite_eq_atTop, Filter.eventually_atTop]
  refine ⟨⌈max L₀ 1 / η⌉₊, fun k hk => ?_⟩
  have hkη : max L₀ 1 ≤ k * η := by
    have := Nat.ceil_le.mp hk
    rwa [div_le_iff₀ hη] at this
  have hL1 : 1 ≤ (k : ℝ) * η := (le_max_right _ _).trans hkη
  have hLL : L₀ ≤ (k : ℝ) * η := (le_max_left _ _).trans hkη
  rw [Real.norm_eq_abs, abs_abs]
  have hid := sum_harmonicProfile_eq_windowSum hg hgc hsupp
    (fun n => lam n - ArithmeticFunction.vonMangoldt n) hL1
    (N := ⌈Real.exp (k * η + 1)⌉₊) (Nat.le_ceil _)
  have hcd : ∀ n, coneDeviation lam n * φ (Real.log n - k * η) / n =
      (if 2 ≤ n then lam n - ArithmeticFunction.vonMangoldt n else 0) *
        harmonicProfile g (Real.log n - k * η) / n := fun n => rfl
  simp_rw [hcd]
  rw [hid, abs_mul, abs_of_pos (Real.exp_pos _)]
  have hw := hC lam hW _ hLL
  have hsq : Real.sqrt (k * η) = Real.sqrt k * Real.sqrt η :=
    Real.sqrt_mul (Nat.cast_nonneg k) η
  have e1 : Real.exp (-(k * η / 2)) * Real.exp (k * η / 2) = 1 := by
    rw [← Real.exp_add]; simp
  calc Real.exp (-(k * η / 2)) *
        |windowSum hg hgc hsupp (fun n => lam n - ArithmeticFunction.vonMangoldt n) (k * η)|
      ≤ Real.exp (-(k * η / 2)) *
          (C * (1 + Real.exp (k * η / 2) * Real.exp (-(Real.sqrt (k * η) / 1920000)))) :=
        mul_le_mul_of_nonneg_left hw (Real.exp_pos _).le
    _ = C * Real.exp (-(k * η / 2)) +
          C * (Real.exp (-(k * η / 2)) * Real.exp (k * η / 2)) *
            Real.exp (-(Real.sqrt (k * η) / 1920000)) := by ring
    _ = b k := by
        have a1 : -((k : ℝ) * η / 2) = k * -(η / 2) := by ring
        have a2 : -(Real.sqrt k * Real.sqrt η / 1920000) =
            -(Real.sqrt η / 1920000 * Real.sqrt k) := by ring
        simp only [hb]
        rw [e1, hsq, a1, a2]; ring

/-! ## One-sided convergence rigidity -/

/-- A full-cone Weil-positive sequence whose excess or deficit over `Λ` is summable against `1/n`
has `Σ_n |lam(n) − Λ(n)|/n < ∞`. -/
theorem summable_abs_sub_div_of_one_sided {lam : ℕ → ℝ} (hW : WeilPositiveFull lam)
    (hs : (Summable fun n : ℕ => max (coneDeviation lam n) 0 / n) ∨
      Summable fun n : ℕ => max (-coneDeviation lam n) 0 / n) :
    Summable fun n : ℕ => |lam n - ArithmeticFunction.vonMangoldt n| * (n : ℝ)⁻¹ := by
  obtain ⟨φ, H, δ, c₀, hδ, hc₀, hφ0, hφH, hφs, hφc, hwin⟩ := exists_profile_summable_windows
  have hd : Summable fun n : ℕ => |coneDeviation lam n| / n := by
    rcases hs with hs | hs
    · exact summable_abs_div_of_windows hδ hc₀ hφ0 hφH hφs hφc _ (hwin lam hW) hs
    · have h := summable_abs_div_of_windows hδ hc₀ hφ0 hφH hφs hφc
        (fun n => -coneDeviation lam n) ((hwin lam hW).congr fun k => by
          rw [← abs_neg, ← Finset.sum_neg_distrib]
          congr 1
          refine Finset.sum_congr rfl fun n _ => ?_
          ring) hs
      exact h.congr fun n => by rw [abs_neg]
  refine (summable_nat_add_iff 2).mp (((summable_nat_add_iff 2).mpr hd).congr fun n => ?_)
  rw [coneDeviation, if_pos (by omega), div_eq_mul_inv]

/-- **One-sided convergence rigidity (excess).** A full-cone Weil-positive `lam` with
`Σ_n max(lam(n) − Λ(n), 0)/n < ∞` equals `Λ` on `n ≥ 2`. -/
theorem eq_vonMangoldt_of_weilPositiveFull_of_summable_excess_div {lam : ℕ → ℝ}
    (hW : WeilPositiveFull lam)
    (hs : Summable fun n : ℕ => max (lam n - ArithmeticFunction.vonMangoldt n) 0 / n) :
    ∀ n, 2 ≤ n → lam n = ArithmeticFunction.vonMangoldt n := by
  refine WeilAbscissa.eq_vonMangoldt_of_weilPositiveFull_of_summable_div hW
    (summable_abs_sub_div_of_one_sided hW (Or.inl (hs.of_nonneg_of_le
      (fun n => div_nonneg (le_max_right _ _) (Nat.cast_nonneg n)) fun n => ?_)))
  unfold coneDeviation
  split_ifs
  · exact le_rfl
  · rw [max_self, zero_div]; exact div_nonneg (le_max_right _ _) (Nat.cast_nonneg n)

/-- **One-sided convergence rigidity (deficit).** A full-cone Weil-positive `lam` with
`Σ_n max(Λ(n) − lam(n), 0)/n < ∞` equals `Λ` on `n ≥ 2`. -/
theorem eq_vonMangoldt_of_weilPositiveFull_of_summable_deficit_div {lam : ℕ → ℝ}
    (hW : WeilPositiveFull lam)
    (hs : Summable fun n : ℕ => max (ArithmeticFunction.vonMangoldt n - lam n) 0 / n) :
    ∀ n, 2 ≤ n → lam n = ArithmeticFunction.vonMangoldt n := by
  refine WeilAbscissa.eq_vonMangoldt_of_weilPositiveFull_of_summable_div hW
    (summable_abs_sub_div_of_one_sided hW (Or.inr (hs.of_nonneg_of_le
      (fun n => div_nonneg (le_max_right _ _) (Nat.cast_nonneg n)) fun n => ?_)))
  unfold coneDeviation
  split_ifs
  · rw [neg_sub]
  · rw [neg_zero, max_self, zero_div]; exact div_nonneg (le_max_right _ _) (Nat.cast_nonneg n)

/-- **RH as a Weil-positive system with harmonically summable excess.** RH holds iff some
full-cone Weil-positive `lam` has `Σ_n max(lam(n) − Λ(n), 0)/n < ∞`; such a `lam` equals `Λ`. -/
theorem riemannHypothesis_iff_exists_weilPositiveFull_summable_excess_div :
    RiemannHypothesis ↔ ∃ lam : ℕ → ℝ, WeilPositiveFull lam ∧
      Summable fun n : ℕ => max (lam n - ArithmeticFunction.vonMangoldt n) 0 / n := by
  constructor
  · intro hRH
    refine ⟨_, riemannHypothesis_iff_weilPositiveFull_vonMangoldt.mp hRH, ?_⟩
    simp only [sub_self, max_self, zero_div]
    exact summable_zero
  · rintro ⟨lam, hW, hs⟩
    have h := eq_vonMangoldt_of_weilPositiveFull_of_summable_excess_div hW hs
    refine riemannHypothesis_iff_weilPositiveFull_vonMangoldt.mpr fun f hf hfc => ?_
    rw [weilFullFunctional_congr (lam' := lam) (fun n hn => (h n hn).symm)]
    exact hW f hf hfc

/-- **RH as a Weil-positive system with harmonically summable deficit.** RH holds iff some
full-cone Weil-positive `lam` has `Σ_n max(Λ(n) − lam(n), 0)/n < ∞`; such a `lam` equals `Λ`. -/
theorem riemannHypothesis_iff_exists_weilPositiveFull_summable_deficit_div :
    RiemannHypothesis ↔ ∃ lam : ℕ → ℝ, WeilPositiveFull lam ∧
      Summable fun n : ℕ => max (ArithmeticFunction.vonMangoldt n - lam n) 0 / n := by
  constructor
  · intro hRH
    refine ⟨_, riemannHypothesis_iff_weilPositiveFull_vonMangoldt.mp hRH, ?_⟩
    simp only [sub_self, max_self, zero_div]
    exact summable_zero
  · rintro ⟨lam, hW, hs⟩
    have h := eq_vonMangoldt_of_weilPositiveFull_of_summable_deficit_div hW hs
    refine riemannHypothesis_iff_weilPositiveFull_vonMangoldt.mpr fun f hf hfc => ?_
    rw [weilFullFunctional_congr (lam' := lam) (fun n hn => (h n hn).symm)]
    exact hW f hf hfc

/-! ## Density of the two sign sets -/

/-- On `n ≥ 2`, a one-signed part of the deviation is bounded on its sign set by the box
`|lam(n) − Λ(n)| ≤ √n (2 log n + C)`: `max(σ(lam − Λ)(n), 0)/n ≤ (2 + C)(1 + log n)/√n`. -/
theorem max_div_le_of_box {x C : ℝ} (hC0 : 0 ≤ C) {n : ℕ} (hn : 2 ≤ n)
    (hbox : |x / Real.sqrt n| ≤ 2 * Real.log n + C) :
    max x 0 / n ≤ (2 + C) * (if 0 < x then (1 + Real.log n) / Real.sqrt n else 0) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hs : 0 < Real.sqrt n := Real.sqrt_pos.mpr hn0
  have hlog : 0 ≤ Real.log n := Real.log_natCast_nonneg n
  split_ifs with h
  · rw [max_eq_left h.le]
    have hsq : (n : ℝ) = Real.sqrt n * Real.sqrt n := (Real.mul_self_sqrt hn0.le).symm
    have hx : x / Real.sqrt n ≤ 2 * Real.log n + C := (le_abs_self _).trans hbox
    calc x / n = (x / Real.sqrt n) / Real.sqrt n := by rw [div_div, ← hsq]
      _ ≤ (2 * Real.log n + C) / Real.sqrt n := div_le_div_of_nonneg_right hx hs.le
      _ ≤ (2 + C) * ((1 + Real.log n) / Real.sqrt n) := by
          rw [mul_div_assoc']
          exact div_le_div_of_nonneg_right (by nlinarith) hs.le
  · rw [max_eq_right (not_lt.mp h), zero_div, mul_zero]

/-- **The excess set of a second cone point is dense.** If `lam` is full-cone Weil-positive and
`Σ_{n : lam(n) > Λ(n)} (1 + log n)/√n < ∞`, then `lam = Λ` on `n ≥ 2`. -/
theorem eq_vonMangoldt_of_weilPositiveFull_of_summable_excess_support {lam : ℕ → ℝ}
    (hW : WeilPositiveFull lam)
    (hS : Summable fun n : ℕ => if (ArithmeticFunction.vonMangoldt n : ℝ) < lam n then
      (1 + Real.log n) / Real.sqrt n else 0) :
    ∀ n, 2 ≤ n → lam n = ArithmeticFunction.vonMangoldt n := by
  obtain ⟨C, hC0, hC⟩ := RHTower.WeilExcess.exists_abs_weilDeviation_le hW
  refine eq_vonMangoldt_of_weilPositiveFull_of_summable_excess_div hW
    ((summable_nat_add_iff 2).mp (Summable.of_nonneg_of_le
      (fun n => div_nonneg (le_max_right _ _) (Nat.cast_nonneg _)) (fun n => ?_)
      (((summable_nat_add_iff 2).mpr hS).mul_left (2 + C))))
  have hn2 : 2 ≤ n + 2 := by omega
  have hbox := hC (n + 2)
  rw [RHTower.WeilExcess.weilDeviation, if_pos hn2] at hbox
  have h := max_div_le_of_box hC0 hn2 hbox
  simp only [sub_pos] at h
  exact h

/-- **The deficit set of a second cone point is dense.** If `lam` is full-cone Weil-positive and
`Σ_{n : lam(n) < Λ(n)} (1 + log n)/√n < ∞`, then `lam = Λ` on `n ≥ 2`. -/
theorem eq_vonMangoldt_of_weilPositiveFull_of_summable_deficit_support {lam : ℕ → ℝ}
    (hW : WeilPositiveFull lam)
    (hS : Summable fun n : ℕ => if lam n < (ArithmeticFunction.vonMangoldt n : ℝ) then
      (1 + Real.log n) / Real.sqrt n else 0) :
    ∀ n, 2 ≤ n → lam n = ArithmeticFunction.vonMangoldt n := by
  obtain ⟨C, hC0, hC⟩ := RHTower.WeilExcess.exists_abs_weilDeviation_le hW
  refine eq_vonMangoldt_of_weilPositiveFull_of_summable_deficit_div hW
    ((summable_nat_add_iff 2).mp (Summable.of_nonneg_of_le
      (fun n => div_nonneg (le_max_right _ _) (Nat.cast_nonneg _)) (fun n => ?_)
      (((summable_nat_add_iff 2).mpr hS).mul_left (2 + C))))
  have hn2 : 2 ≤ n + 2 := by omega
  have hbox := hC (n + 2)
  rw [RHTower.WeilExcess.weilDeviation, if_pos hn2, ← abs_neg, ← neg_div, neg_sub] at hbox
  have h := max_div_le_of_box hC0 hn2 hbox
  simp only [sub_pos] at h
  exact h

end RHTower.WeilOneSided
