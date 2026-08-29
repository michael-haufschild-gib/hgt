import GaloisForLFunctions.RHTower.HardyZWindowMean
import GaloisForLFunctions.RHTower.HardyDyadicWindowTheorem

/-!
# A polynomial census of critical-line zeros

Partition the dyadic block `[T, 2T]` into `K = ⌊T^{1/8}⌋` windows.  The dyadic second moment
puts total mass at least `T/4` into the windows; light windows — mass below `T/(8K)` — carry
at most `T/8` in total; and each window's mass is at most `√(H·F)` by Cauchy–Schwarz against
the window fourth moment.  On a heavy window the subwindow mean bound `O(T^{3/4})` loses to
the mass cubed, and the fourth-moment sign-change detector produces a critical-line zero
inside the window.  Distinct windows give distinct ordinates up to a factor two (adjacent
windows can share an endpoint), and each new ordinate adds one to the critical-line census.
Hence `N₀(T)` grows at least like `T^{1/16}/(1+log T)²`, unconditionally — a polynomial
strengthening of the logarithmic Hardy census.
-/

open Set MeasureTheory Complex Finset

namespace RHTower

noncomputable section

/-! ## The abstract window pigeonhole -/

set_option maxHeartbeats 1600000 in
/-- **Heavy-window pigeonhole.**  If the dyadic second moment of Hardy's `Z` is at least
`T/4`, every window of the `K`-partition has fourth moment at most `M4` and first moment at
most `ME` in modulus, and `ME² M4` loses to the cube of the heaviness threshold `T/(8K)`,
then a family of windows of total weight at least `T/8` — each carrying a critical-line
zero — exists. -/
private theorem exists_heavyFinset {T : ℝ} {K : ℕ} (hK1 : 1 ≤ K) (hT0 : 0 < T)
    {M4 ME : ℝ} (hM4 : 0 < M4)
    (hC : T / 4 ≤ ∫ τ in T..(2 * T), (hardyZ τ) ^ 2)
    (h4 : ∀ k : ℕ, k < K →
      (∫ τ in (T + k * (T / K))..(T + ((k + 1 : ℕ) : ℝ) * (T / K)), (hardyZ τ) ^ 4) ≤ M4)
    (hE : ∀ k : ℕ, k < K →
      |∫ τ in (T + k * (T / K))..(T + ((k + 1 : ℕ) : ℝ) * (T / K)), hardyZ τ| ≤ ME)
    (hgap : ME ^ 2 * M4 < (T / (8 * K)) ^ 3) :
    ∃ S : Finset ℕ,
      (∀ k ∈ S, k < K ∧ ∃ τ, ((T + k * (T / K) ≤ τ ∧ τ ≤ T + ((k + 1 : ℕ) : ℝ) * (T / K)) ∧
        riemannZeta (linePt τ) = 0)) ∧
      T / 8 ≤ (S.card : ℝ) * Real.sqrt ((T / K) * M4) := by
  classical
  have hKR0 : (0 : ℝ) < (K : ℝ) := by exact_mod_cast hK1
  have hTK0 : (0 : ℝ) < T / K := by positivity
  set a : ℕ → ℝ := fun k => T + k * (T / K) with hadef
  have ha_le : ∀ k : ℕ, a k ≤ a (k + 1) := by
    intro k
    rw [hadef]
    dsimp only
    push_cast
    nlinarith [hTK0]
  set m : ℕ → ℝ := fun k => ∫ τ in (a k)..(a (k + 1)), (hardyZ τ) ^ 2 with hmdef
  have hm0 : ∀ k : ℕ, 0 ≤ m k := by
    intro k
    rw [hmdef]
    exact intervalIntegral.integral_nonneg (ha_le k) (fun u _ => sq_nonneg _)
  have hpart : ∑ k ∈ range K, m k = ∫ τ in T..(2 * T), (hardyZ τ) ^ 2 := by
    have h := intervalIntegral.sum_integral_adjacent_intervals
      (f := fun τ => (hardyZ τ) ^ 2) (μ := volume)
      (a := fun k : ℕ => T + k * (T / K)) (n := K)
      (fun k _ => ((continuous_hardyZ.pow 2).intervalIntegrable _ _))
    have hz : T + ((0 : ℕ) : ℝ) * (T / K) = T := by push_cast; ring
    have hK' : T + (K : ℝ) * (T / K) = 2 * T := by field_simp; ring
    rw [hz, hK'] at h
    simp only [hmdef, hadef]
    exact h
  set Θ : ℝ := T / (8 * K) with hΘdef
  have hΘ0 : (0 : ℝ) < Θ := by positivity
  set S : Finset ℕ := (range K).filter (fun k => Θ ≤ m k) with hSdef
  have hSmem : ∀ k ∈ S, k < K ∧ Θ ≤ m k := fun k hk =>
    ⟨Finset.mem_range.mp (Finset.mem_filter.mp hk).1, (Finset.mem_filter.mp hk).2⟩
  refine ⟨S, fun k hk => ⟨(hSmem k hk).1, ?_⟩, ?_⟩
  · -- the sign-change detector on a heavy window
    have hkK := (hSmem k hk).1
    have hΘm := (hSmem k hk).2
    have hΘm' : Θ ≤ ∫ τ in (a k)..(a (k + 1)), (hardyZ τ) ^ 2 := by
      simpa only [hmdef] using hΘm
    have hgap' : (∫ τ in (a k)..(a (k + 1)), hardyZ τ) ^ 2 * M4 < Θ ^ 3 := by
      have h2 := hE k hkK
      have h3 : |∫ τ in (a k)..(a (k + 1)), hardyZ τ| ≤ ME := by
        rw [hadef]
        dsimp only
        exact h2
      have h4' := abs_le.mp h3
      have h1 : (∫ τ in (a k)..(a (k + 1)), hardyZ τ) ^ 2 ≤ ME ^ 2 := by
        nlinarith [h4'.1, h4'.2]
      have h5 : (∫ τ in (a k)..(a (k + 1)), hardyZ τ) ^ 2 * M4 ≤ ME ^ 2 * M4 :=
        mul_le_mul_of_nonneg_right h1 hM4.le
      calc (∫ τ in (a k)..(a (k + 1)), hardyZ τ) ^ 2 * M4 ≤ ME ^ 2 * M4 := h5
        _ < (T / (8 * K)) ^ 3 := hgap
        _ = Θ ^ 3 := by rw [hΘdef]
    have h4' : (∫ τ in (a k)..(a (k + 1)), (hardyZ τ) ^ 4) ≤ M4 := by
      have h := h4 k hkK
      rw [hadef]
      dsimp only
      exact h
    obtain ⟨τ, hτ, hz⟩ := exists_riemannZeta_line_zero_of_hardyZ_fourth_moment_gap
      (α := a k) (β := a (k + 1)) (S := Θ) (F := M4) (ha_le k) hΘ0 hΘm' h4' hgap'
    refine ⟨τ, ⟨?_, ?_⟩, hz⟩
    · have h := hτ.1
      rw [hadef] at h
      exact h
    · have h := hτ.2
      rw [hadef] at h
      exact h
  · -- the weight lower bound
    have hlight : ∑ k ∈ (range K).filter (fun k => ¬ Θ ≤ m k), m k ≤ T / 8 := by
      have h1 : ∀ k ∈ (range K).filter (fun k => ¬ Θ ≤ m k), m k ≤ Θ := by
        intro k hk
        have := (Finset.mem_filter.mp hk).2
        linarith [lt_of_not_ge this]
      have h2 := Finset.sum_le_card_nsmul _ _ _ h1
      rw [nsmul_eq_mul] at h2
      have h3 : (((range K).filter (fun k => ¬ Θ ≤ m k)).card : ℝ) ≤ (K : ℝ) := by
        exact_mod_cast le_trans (Finset.card_filter_le _ _)
          (le_of_eq (Finset.card_range K))
      have h4' : (((range K).filter (fun k => ¬ Θ ≤ m k)).card : ℝ) * Θ ≤ (K : ℝ) * Θ :=
        mul_le_mul_of_nonneg_right h3 hΘ0.le
      have h5 : (K : ℝ) * Θ = T / 8 := by
        rw [hΘdef]
        field_simp
      linarith
    have hheavy : T / 8 ≤ ∑ k ∈ S, m k := by
      have h := Finset.sum_filter_add_sum_filter_not (range K) (fun k => Θ ≤ m k) m
      have hC' : T / 4 ≤ ∑ k ∈ range K, m k := by
        rw [hpart]
        exact hC
      rw [hSdef]
      linarith [hlight, hC', h]
    have hcap : ∀ k ∈ S, m k ≤ Real.sqrt ((T / K) * M4) := by
      intro k hk
      have hkK := (hSmem k hk).1
      have hlen : a (k + 1) - a k = T / K := by
        rw [hadef]
        dsimp only
        push_cast
        ring
      have hle := ha_le k
      have hf : MeasureTheory.IntegrableOn (fun τ => (hardyZ τ) ^ 2)
          (Set.Ioc (a k) (a (k + 1))) MeasureTheory.volume :=
        (continuous_hardyZ.pow 2).integrableOn_Ioc
      have hf2 : MeasureTheory.IntegrableOn (fun τ => ((hardyZ τ) ^ 2) ^ 2)
          (Set.Ioc (a k) (a (k + 1))) MeasureTheory.volume := by
        have h : MeasureTheory.IntegrableOn (fun τ => (hardyZ τ) ^ 4)
            (Set.Ioc (a k) (a (k + 1))) MeasureTheory.volume :=
          (continuous_hardyZ.pow 4).integrableOn_Ioc
        exact MeasureTheory.IntegrableOn.congr_fun h (fun τ _ => by ring)
          measurableSet_Ioc
      have h2 := GaloisForLFunctions.HTGeometry.sq_integral_le_length_mul hle hf hf2
      have hcongr : (∫ τ in Set.Ioc (a k) (a (k + 1)), ((hardyZ τ) ^ 2) ^ 2)
          = ∫ τ in Set.Ioc (a k) (a (k + 1)), (hardyZ τ) ^ 4 := by
        apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioc
        intro τ _
        ring
      rw [hcongr, hlen] at h2
      have hIoc1 : (∫ τ in (a k)..(a (k + 1)), (hardyZ τ) ^ 2)
          = ∫ τ in Set.Ioc (a k) (a (k + 1)), (hardyZ τ) ^ 2 :=
        intervalIntegral.integral_of_le hle
      have hIoc2 : (∫ τ in (a k)..(a (k + 1)), (hardyZ τ) ^ 4)
          = ∫ τ in Set.Ioc (a k) (a (k + 1)), (hardyZ τ) ^ 4 :=
        intervalIntegral.integral_of_le hle
      have h4w : (∫ τ in Set.Ioc (a k) (a (k + 1)), (hardyZ τ) ^ 4) ≤ M4 := by
        rw [← hIoc2]
        have h := h4 k hkK
        rw [hadef]
        dsimp only
        exact h
      have hHF : (m k) ^ 2 ≤ (T / K) * M4 := by
        have h7 : (T / K) * (∫ τ in Set.Ioc (a k) (a (k + 1)), (hardyZ τ) ^ 4)
            ≤ (T / K) * M4 :=
          mul_le_mul_of_nonneg_left h4w hTK0.le
        have h8 : m k = ∫ τ in Set.Ioc (a k) (a (k + 1)), (hardyZ τ) ^ 2 := by
          rw [hmdef]
          dsimp only
          exact hIoc1
        rw [h8]
        linarith [h2, h7]
      have hmk0 := hm0 k
      calc m k = Real.sqrt ((m k) ^ 2) := (Real.sqrt_sq hmk0).symm
        _ ≤ Real.sqrt ((T / K) * M4) := Real.sqrt_le_sqrt hHF
    have hsum := Finset.sum_le_card_nsmul S m _ hcap
    rw [nsmul_eq_mul] at hsum
    linarith [hheavy]

/-! ## The window fourth-moment budget -/

private theorem window_fourth_le {T : ℝ} {K : ℕ} (hK1 : 1 ≤ K) (hT0 : 0 < T)
    {M4 : ℝ} (hdyadic : (∫ τ in T..(2 * T), (hardyZ τ) ^ 4) ≤ M4) :
    ∀ k : ℕ, k < K →
      (∫ τ in (T + k * (T / K))..(T + ((k + 1 : ℕ) : ℝ) * (T / K)), (hardyZ τ) ^ 4)
        ≤ M4 := by
  intro k hkK
  have hKR0 : (0 : ℝ) < (K : ℝ) := by exact_mod_cast hK1
  have hTK0 : (0 : ℝ) < T / K := by positivity
  have hk1K : ((k : ℝ) + 1) ≤ (K : ℝ) := by exact_mod_cast hkK
  refine le_trans (intervalIntegral.integral_mono_interval
    (c := T) (d := 2 * T) ?_ ?_ ?_
    (Filter.Eventually.of_forall fun u => ?_)
    ((continuous_hardyZ.pow 4).intervalIntegrable _ _)) hdyadic
  · have h0 : (0 : ℝ) ≤ (k : ℝ) * (T / K) := by positivity
    linarith
  · push_cast
    nlinarith [hTK0]
  · push_cast
    have h1 : ((k : ℝ) + 1) * (T / K) ≤ (K : ℝ) * (T / K) :=
      mul_le_mul_of_nonneg_right hk1K hTK0.le
    have h2 : (K : ℝ) * (T / K) = T := by field_simp
    linarith
  · positivity

/-! ## Distinct ordinates from distinct windows -/

private theorem exists_distinct_ordinates {T : ℝ} {K : ℕ} (hT0 : 0 < T) (hK1 : 1 ≤ K)
    (S : Finset ℕ)
    (hzero : ∀ k ∈ S, k < K ∧ ∃ τ, ((T + k * (T / K) ≤ τ ∧
      τ ≤ T + ((k + 1 : ℕ) : ℝ) * (T / K)) ∧ riemannZeta (linePt τ) = 0)) :
    ∃ τS : Finset ℝ, (∀ τ ∈ τS, T < τ ∧ τ ≤ 2 * T ∧ riemannZeta (linePt τ) = 0) ∧
      S.card ≤ 2 * τS.card + 1 := by
  classical
  have hKR0 : (0 : ℝ) < (K : ℝ) := by exact_mod_cast hK1
  have hTK0 : (0 : ℝ) < T / K := by positivity
  set P : ℕ → ℝ → Prop := fun k τ =>
    (T + k * (T / K) ≤ τ ∧ τ ≤ T + ((k + 1 : ℕ) : ℝ) * (T / K)) ∧
      riemannZeta (linePt τ) = 0 with hPdef
  set g : ℕ → ℝ := fun k => if h : ∃ τ, P k τ then h.choose else 0 with hgdef
  have hg : ∀ k ∈ S, P k (g k) := by
    intro k hk
    have hex : ∃ τ, P k τ := (hzero k hk).2
    rw [hgdef]
    dsimp only
    rw [dif_pos hex]
    exact hex.choose_spec
  set S' : Finset ℕ := S.erase 0 with hS'def
  refine ⟨S'.image g, ?_, ?_⟩
  · intro τ hτ
    obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hτ
    have hkS : k ∈ S := Finset.mem_of_mem_erase hk
    have hk0 : k ≠ 0 := Finset.ne_of_mem_erase hk
    have hk1 : 1 ≤ k := Nat.one_le_iff_ne_zero.mpr hk0
    have hkK : k < K := (hzero k hkS).1
    obtain ⟨⟨hlow, hhigh⟩, hz⟩ := hg k hkS
    refine ⟨?_, ?_, hz⟩
    · have h1 : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk1
      nlinarith [hTK0]
    · have hk1K : ((k : ℝ) + 1) ≤ (K : ℝ) := by exact_mod_cast hkK
      have h1 : ((k : ℝ) + 1) * (T / K) ≤ (K : ℝ) * (T / K) :=
        mul_le_mul_of_nonneg_right hk1K hTK0.le
      have h2 : (K : ℝ) * (T / K) = T := by field_simp
      push_cast at hhigh
      linarith
  · have hfiber : ∀ b ∈ S'.image g, (S'.filter (fun k => g k = b)).card ≤ 2 := by
      intro b hb
      set fib : Finset ℕ := S'.filter (fun k => g k = b) with hfibdef
      by_cases hne : fib.Nonempty
      · set k₀ : ℕ := fib.min' hne with hk₀def
        have hsub : fib ⊆ Finset.Icc k₀ (k₀ + 1) := by
          intro k hkfib
          rw [Finset.mem_Icc]
          refine ⟨Finset.min'_le fib k hkfib, ?_⟩
          have hk₀fib : k₀ ∈ fib := Finset.min'_mem fib hne
          have hk₀S : k₀ ∈ S := Finset.mem_of_mem_erase (Finset.mem_filter.mp hk₀fib).1
          have hkS : k ∈ S := Finset.mem_of_mem_erase (Finset.mem_filter.mp hkfib).1
          have hgk₀ : g k₀ = b := (Finset.mem_filter.mp hk₀fib).2
          have hgk : g k = b := (Finset.mem_filter.mp hkfib).2
          obtain ⟨⟨hlow₀, hhigh₀⟩, _⟩ := hg k₀ hk₀S
          obtain ⟨⟨hlowk, hhighk⟩, _⟩ := hg k hkS
          have hcross : T + (k : ℝ) * (T / K) ≤ T + ((k₀ : ℝ) + 1) * (T / K) := by
            push_cast at hhigh₀
            calc T + (k : ℝ) * (T / K) ≤ g k := hlowk
              _ = b := hgk
              _ = g k₀ := hgk₀.symm
              _ ≤ T + ((k₀ : ℝ) + 1) * (T / K) := hhigh₀
          have hcross' : (k : ℝ) * (T / K) ≤ ((k₀ : ℝ) + 1) * (T / K) := by linarith
          have h2 : (k : ℝ) ≤ (k₀ : ℝ) + 1 := le_of_mul_le_mul_right hcross' hTK0
          exact_mod_cast h2
        calc fib.card ≤ (Finset.Icc k₀ (k₀ + 1)).card := Finset.card_le_card hsub
          _ = 2 := by rw [Nat.card_Icc]; omega
      · rw [Finset.not_nonempty_iff_eq_empty] at hne
        rw [hne]
        norm_num
    have hcard2 := Finset.card_le_mul_card_image S' 2 hfiber
    have hcard1 : S.card ≤ S'.card + 1 := by
      rw [hS'def]
      by_cases h0 : (0 : ℕ) ∈ S
      · rw [Finset.card_erase_of_mem h0]
        omega
      · rw [Finset.erase_eq_self.mpr h0]
        omega
    omega

/-! ## Iterated square roots and the polylogarithm bound -/

private theorem sqrt_sq_chain {r : ℝ} (hr : 0 ≤ r) :
    Real.sqrt (Real.sqrt (Real.sqrt (Real.sqrt (r ^ 16)))) = r := by
  have h1 : (r ^ 16 : ℝ) = (r ^ 8) ^ 2 := by ring
  have h2 : (r ^ 8 : ℝ) = (r ^ 4) ^ 2 := by ring
  have h3 : (r ^ 4 : ℝ) = (r ^ 2) ^ 2 := by ring
  rw [h1, Real.sqrt_sq (by positivity), h2, Real.sqrt_sq (by positivity), h3,
    Real.sqrt_sq (by positivity), Real.sqrt_sq hr]

private theorem one_add_log_pow_four_le_sixteenth {T : ℝ} (hT : 1 ≤ T) :
    (1 + Real.log T) ^ 4
      ≤ 21381376 * Real.sqrt (Real.sqrt (Real.sqrt (Real.sqrt T))) := by
  have hT0 : (0 : ℝ) < T := by linarith
  set N : ℝ := Real.sqrt (Real.sqrt T) with hN
  have hN1 : 1 ≤ N := by
    rw [hN, show (1 : ℝ) = Real.sqrt (Real.sqrt 1) by simp]
    exact Real.sqrt_le_sqrt (Real.sqrt_le_sqrt hT)
  have hlogN : Real.log N = Real.log T / 4 := by
    rw [hN, Real.log_sqrt (Real.sqrt_nonneg T), Real.log_sqrt hT0.le]
    ring
  have hlog0 : 0 ≤ Real.log T := Real.log_nonneg hT
  have hquarter : (1 + Real.log T) ^ 4 ≤ 256 * (1 + Real.log N) ^ 4 := by
    have h1 : 1 + Real.log T ≤ 4 * (1 + Real.log N) := by
      rw [hlogN]
      linarith
    have h2 : (1 + Real.log T) ^ 4 ≤ (4 * (1 + Real.log N)) ^ 4 :=
      pow_le_pow_left₀ (by linarith) h1 4
    calc (1 + Real.log T) ^ 4 ≤ (4 * (1 + Real.log N)) ^ 4 := h2
      _ = 256 * (1 + Real.log N) ^ 4 := by ring
  have hbase := one_add_log_pow_four_le hN1
  calc (1 + Real.log T) ^ 4 ≤ 256 * (1 + Real.log N) ^ 4 := hquarter
    _ ≤ 256 * (83521 * Real.sqrt (Real.sqrt N)) := by
        nlinarith [Real.sqrt_nonneg (Real.sqrt N)]
    _ = 21381376 * Real.sqrt (Real.sqrt (Real.sqrt (Real.sqrt T))) := by
        rw [hN]
        ring

/-! ## The numeric gap for the `⌊T^{1/8}⌋`-window partition -/

set_option maxHeartbeats 3200000 in
private theorem numeric_gap {T CE CF : ℝ} (_hCE : 0 ≤ CE) (hCF : 0 ≤ CF)
    (hTD : (512 * 21381376 * (CE ^ 2 + 1) * (CF + 1) + 74000 ^ 2 * (CF + 1)
      + 21381376 + 5) ^ 16 ≤ T) :
    (CE * (Real.sqrt T * Real.sqrt (Real.sqrt T))) ^ 2
        * ((CF + 1) * T * (1 + Real.log T) ^ 4)
      < (T / (8 * (⌊Real.sqrt (Real.sqrt (Real.sqrt T))⌋₊ : ℝ))) ^ 3 := by
  set D : ℝ := 512 * 21381376 * (CE ^ 2 + 1) * (CF + 1) + 74000 ^ 2 * (CF + 1)
      + 21381376 + 4 with hDdef
  have hD4 : (4 : ℝ) ≤ D := by
    rw [hDdef]
    nlinarith [sq_nonneg CE, hCF]
  have hTD' : (D + 1) ^ 16 ≤ T := by
    have : D + 1 = 512 * 21381376 * (CE ^ 2 + 1) * (CF + 1) + 74000 ^ 2 * (CF + 1)
        + 21381376 + 5 := by rw [hDdef]; ring
    rw [this]
    exact hTD
  have hT0 : (0 : ℝ) < T := by
    have h1 : (0 : ℝ) < (D + 1) ^ 16 := by positivity
    linarith
  have hT1 : (1 : ℝ) ≤ T := by
    have h1 : (1 : ℝ) ≤ (D + 1) ^ 16 := one_le_pow₀ (by linarith)
    linarith
  set s1 : ℝ := Real.sqrt T with hs1def
  set s2 : ℝ := Real.sqrt s1 with hs2def
  set s3 : ℝ := Real.sqrt s2 with hs3def
  set s4 : ℝ := Real.sqrt s3 with hs4def
  have hs1sq : s1 ^ 2 = T := by rw [hs1def, Real.sq_sqrt hT0.le]
  have hs2sq : s2 ^ 2 = s1 := by rw [hs2def, Real.sq_sqrt (Real.sqrt_nonneg T)]
  have hs3sq : s3 ^ 2 = s2 := by rw [hs3def, Real.sq_sqrt (Real.sqrt_nonneg s1)]
  have hs4sq : s4 ^ 2 = s3 := by rw [hs4def, Real.sq_sqrt (Real.sqrt_nonneg s2)]
  have hs40 : 0 ≤ s4 := Real.sqrt_nonneg _
  have hs4D : D + 1 ≤ s4 := by
    have hmono : Real.sqrt (Real.sqrt (Real.sqrt (Real.sqrt ((D + 1) ^ 16)))) ≤ s4 := by
      rw [hs4def, hs3def, hs2def, hs1def]
      exact Real.sqrt_le_sqrt (Real.sqrt_le_sqrt (Real.sqrt_le_sqrt
        (Real.sqrt_le_sqrt hTD')))
    rwa [sqrt_sq_chain (by linarith : (0 : ℝ) ≤ D + 1)] at hmono
  have hs4pos : (0 : ℝ) < s4 := by linarith
  have hs3pos : (0 : ℝ) < s3 := by nlinarith [hs4sq]
  have hs2pos : (0 : ℝ) < s2 := by nlinarith [hs3sq]
  have hs1pos : (0 : ℝ) < s1 := by nlinarith [hs2sq]
  set K : ℕ := ⌊s3⌋₊ with hKdef
  have hKle : (K : ℝ) ≤ s3 := Nat.floor_le hs3pos.le
  have hK1 : 1 ≤ K := Nat.le_floor (by
    exact_mod_cast (by nlinarith [hs4sq, hs4D, hD4] : (1 : ℝ) ≤ s3))
  have hKR0 : (0 : ℝ) < (K : ℝ) := by exact_mod_cast hK1
  -- the key coefficient inequality
  have hlog4 := one_add_log_pow_four_le_sixteenth hT1
  rw [← hs1def, ← hs2def, ← hs3def, ← hs4def] at hlog4
  have hkey : 512 * (K : ℝ) ^ 3 * CE ^ 2 * (CF + 1) * (1 + Real.log T) ^ 4 < s1 := by
    have hK3 : (K : ℝ) ^ 3 ≤ s3 ^ 3 := pow_le_pow_left₀ hKR0.le hKle 3
    have hs3s1 : s3 ^ 4 = s1 := by
      rw [show s3 ^ 4 = (s3 ^ 2) ^ 2 by ring, hs3sq, hs2sq]
    have h1 : 512 * (K : ℝ) ^ 3 * CE ^ 2 * (CF + 1) * (1 + Real.log T) ^ 4
        ≤ 512 * s3 ^ 3 * CE ^ 2 * (CF + 1) * (21381376 * s4) := by
      have hb1 : (0 : ℝ) ≤ 512 * CE ^ 2 * (CF + 1) := by positivity
      have hb3 : (0 : ℝ) ≤ (1 + Real.log T) ^ 4 := by positivity
      have hstep1 : (K : ℝ) ^ 3 * (1 + Real.log T) ^ 4
          ≤ s3 ^ 3 * (1 + Real.log T) ^ 4 :=
        mul_le_mul_of_nonneg_right hK3 hb3
      have hstep2 : s3 ^ 3 * (1 + Real.log T) ^ 4 ≤ s3 ^ 3 * (21381376 * s4) :=
        mul_le_mul_of_nonneg_left hlog4 (pow_nonneg hs3pos.le 3)
      have hstep4 := mul_le_mul_of_nonneg_left (le_trans hstep1 hstep2) hb1
      calc 512 * (K : ℝ) ^ 3 * CE ^ 2 * (CF + 1) * (1 + Real.log T) ^ 4
          = (512 * CE ^ 2 * (CF + 1)) * ((K : ℝ) ^ 3 * (1 + Real.log T) ^ 4) := by ring
        _ ≤ (512 * CE ^ 2 * (CF + 1)) * (s3 ^ 3 * (21381376 * s4)) := hstep4
        _ = 512 * s3 ^ 3 * CE ^ 2 * (CF + 1) * (21381376 * s4) := by ring
    have h2 : 512 * s3 ^ 3 * CE ^ 2 * (CF + 1) * (21381376 * s4) < s1 := by
      rw [← hs3s1]
      have hexp : s3 ^ 4 = s3 ^ 3 * (s4 * s4) := by
        rw [show s3 ^ 4 = s3 ^ 3 * s3 by ring, ← hs4sq]
        ring
      rw [hexp]
      have hfactor : 512 * s3 ^ 3 * CE ^ 2 * (CF + 1) * (21381376 * s4)
          = (512 * 21381376 * CE ^ 2 * (CF + 1)) * s4 * s3 ^ 3 := by ring
      rw [hfactor]
      have hcoef : 512 * 21381376 * CE ^ 2 * (CF + 1) < s4 := by
        have h3 : 512 * 21381376 * CE ^ 2 * (CF + 1)
            ≤ 512 * 21381376 * (CE ^ 2 + 1) * (CF + 1) := by nlinarith
        rw [hDdef] at hs4D
        nlinarith [sq_nonneg 74000, hCF]
      have h5 : (512 * 21381376 * CE ^ 2 * (CF + 1)) * s4 < s4 * s4 :=
        mul_lt_mul_of_pos_right hcoef hs4pos
      have h6 := mul_lt_mul_of_pos_right h5 (pow_pos hs3pos 3)
      calc (512 * 21381376 * CE ^ 2 * (CF + 1)) * s4 * s3 ^ 3
          < s4 * s4 * s3 ^ 3 := h6
        _ = s3 ^ 3 * (s4 * s4) := by ring
    linarith
  -- the mean square value
  have hmean : (CE * (s1 * s2)) ^ 2 = CE ^ 2 * (T * s1) := by
    rw [mul_pow, mul_pow, hs1sq, hs2sq]
  -- assemble
  have hΘcube : (T / (8 * (K : ℝ))) ^ 3 = T ^ 3 / (512 * (K : ℝ) ^ 3) := by
    rw [div_pow]
    congr 1
    ring
  have hmain : (CE * (s1 * s2)) ^ 2 * ((CF + 1) * T * (1 + Real.log T) ^ 4)
      < (T / (8 * (K : ℝ))) ^ 3 := by
    rw [hmean, hΘcube, lt_div_iff₀ (by positivity : (0 : ℝ) < 512 * (K : ℝ) ^ 3)]
    have hT3 : T ^ 3 = T ^ 2 * s1 ^ 2 := by rw [hs1sq]; ring
    rw [hT3]
    have hlhs : CE ^ 2 * (T * s1) * ((CF + 1) * T * (1 + Real.log T) ^ 4)
        * (512 * (K : ℝ) ^ 3)
        = (512 * (K : ℝ) ^ 3 * CE ^ 2 * (CF + 1) * (1 + Real.log T) ^ 4)
          * (s1 * T ^ 2) := by ring
    rw [hlhs]
    have hstep := mul_lt_mul_of_pos_right hkey (mul_pos hs1pos (pow_pos hT0 2))
    calc (512 * (K : ℝ) ^ 3 * CE ^ 2 * (CF + 1) * (1 + Real.log T) ^ 4) * (s1 * T ^ 2)
        < s1 * (s1 * T ^ 2) := hstep
      _ = T ^ 2 * s1 ^ 2 := by ring
  exact hmain

/-! ## The polynomial zero count -/

set_option maxHeartbeats 3200000 in
/-- **Polynomially many distinct critical-line zero ordinates in every dyadic block.**
Unconditionally, at least `c · T^{1/16}/(1+log T)²` distinct ordinates `τ ∈ (T, 2T]` carry
critical-line zeros `ζ(1/2 + iτ) = 0`, for all large `T`. -/
theorem exists_many_distinct_line_zeros_dyadic :
    ∃ c : ℝ, 0 < c ∧ ∃ T₁ : ℝ, 1 ≤ T₁ ∧ ∀ T : ℝ, T₁ ≤ T →
      ∃ τS : Finset ℝ, (∀ τ ∈ τS, T < τ ∧ τ ≤ 2 * T ∧ riemannZeta (linePt τ) = 0) ∧
        c * Real.sqrt (Real.sqrt (Real.sqrt (Real.sqrt T))) / (1 + Real.log T) ^ 2
          ≤ (τS.card : ℝ) := by
  classical
  obtain ⟨TC, hTC0, hC⟩ := exists_le_integral_hardyZ_sq
  obtain ⟨CF, hCF, hF⟩ := exists_integral_hardyZ_pow_four_dyadic_real_le
  obtain ⟨CE, hCE, hE⟩ := exists_abs_integral_hardyZ_window_le
  set D : ℝ := 512 * 21381376 * (CE ^ 2 + 1) * (CF + 1) + 74000 ^ 2 * (CF + 1)
      + 21381376 + 4 with hDdef
  have hD4 : (4 : ℝ) ≤ D := by
    rw [hDdef]
    nlinarith [sq_nonneg CE, hCF]
  refine ⟨1 / (48 * (Real.sqrt (CF + 1) + 1)), by positivity,
    max (max TC 16) ((D + 1) ^ 16), ?_, fun T hT => ?_⟩
  · refine le_trans ?_ (le_max_right _ _)
    calc (1 : ℝ) = 1 ^ 16 := by norm_num
      _ ≤ (D + 1) ^ 16 := pow_le_pow_left₀ (by norm_num) (by linarith) 16
  have hT16 : (16 : ℝ) ≤ T := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hT
  have hTTC : TC ≤ T := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hT
  have hTD : (D + 1) ^ 16 ≤ T := le_trans (le_max_right _ _) hT
  have hT0 : (0 : ℝ) < T := by linarith
  have hT1 : (1 : ℝ) ≤ T := by linarith
  set s1 : ℝ := Real.sqrt T with hs1def
  set s2 : ℝ := Real.sqrt s1 with hs2def
  set s3 : ℝ := Real.sqrt s2 with hs3def
  set s4 : ℝ := Real.sqrt s3 with hs4def
  have hs1sq : s1 ^ 2 = T := by rw [hs1def, Real.sq_sqrt hT0.le]
  have hs2sq : s2 ^ 2 = s1 := by rw [hs2def, Real.sq_sqrt (Real.sqrt_nonneg T)]
  have hs3sq : s3 ^ 2 = s2 := by rw [hs3def, Real.sq_sqrt (Real.sqrt_nonneg s1)]
  have hs4sq : s4 ^ 2 = s3 := by rw [hs4def, Real.sq_sqrt (Real.sqrt_nonneg s2)]
  have hs40 : 0 ≤ s4 := Real.sqrt_nonneg _
  have hs4D : D + 1 ≤ s4 := by
    have hmono : Real.sqrt (Real.sqrt (Real.sqrt (Real.sqrt ((D + 1) ^ 16)))) ≤ s4 := by
      rw [hs4def, hs3def, hs2def, hs1def]
      exact Real.sqrt_le_sqrt (Real.sqrt_le_sqrt (Real.sqrt_le_sqrt
        (Real.sqrt_le_sqrt hTD)))
    rwa [sqrt_sq_chain (by linarith : (0 : ℝ) ≤ D + 1)] at hmono
  have hs4pos : (0 : ℝ) < s4 := by linarith
  have hs3pos : (0 : ℝ) < s3 := by nlinarith [hs4sq]
  have hs32 : (2 : ℝ) ≤ s3 := by nlinarith [hs4sq, hs4D, hD4]
  set K : ℕ := ⌊s3⌋₊ with hKdef
  have hKle : (K : ℝ) ≤ s3 := Nat.floor_le hs3pos.le
  have hK1 : 1 ≤ K := Nat.le_floor (by exact_mod_cast (by linarith : (1 : ℝ) ≤ s3))
  have hKR0 : (0 : ℝ) < (K : ℝ) := by exact_mod_cast hK1
  have hKge : s3 / 2 ≤ (K : ℝ) := by
    have h1 : s3 < (K : ℝ) + 1 := Nat.lt_floor_add_one s3
    have h2 : (1 : ℝ) ≤ (K : ℝ) := by exact_mod_cast hK1
    linarith
  have hTK0 : (0 : ℝ) < T / K := by positivity
  -- the three inputs of the pigeonhole
  have hCdyadic := hC T hTTC
  set M4 : ℝ := (CF + 1) * T * (1 + Real.log T) ^ 4 with hM4def
  have hlogT0 : 0 ≤ Real.log T := Real.log_nonneg hT1
  have hM40 : 0 < M4 := by
    rw [hM4def]
    have h1 : (0 : ℝ) < 1 + Real.log T := by linarith
    positivity
  have hM4dyadic : (∫ τ in T..(2 * T), (hardyZ τ) ^ 4) ≤ M4 := by
    refine le_trans (hF (by linarith)) ?_
    rw [hM4def]
    have h1 : (0 : ℝ) ≤ T * (1 + Real.log T) ^ 4 := by positivity
    nlinarith
  have h4win := window_fourth_le hK1 hT0 hM4dyadic
  have hEwin : ∀ k : ℕ, k < K →
      |∫ τ in (T + k * (T / K))..(T + ((k + 1 : ℕ) : ℝ) * (T / K)), hardyZ τ|
        ≤ CE * (Real.sqrt T * Real.sqrt (Real.sqrt T)) := by
    intro k hkK
    have hk1K : ((k : ℝ) + 1) ≤ (K : ℝ) := by exact_mod_cast hkK
    refine hE hT16 ?_ ?_ ?_
    · have h0 : (0 : ℝ) ≤ (k : ℝ) * (T / K) := by positivity
      linarith
    · push_cast
      nlinarith [hTK0]
    · push_cast
      have h1 : ((k : ℝ) + 1) * (T / K) ≤ (K : ℝ) * (T / K) :=
        mul_le_mul_of_nonneg_right hk1K hTK0.le
      have h2 : (K : ℝ) * (T / K) = T := by field_simp
      linarith
  have hgap : (CE * (Real.sqrt T * Real.sqrt (Real.sqrt T))) ^ 2 * M4
      < (T / (8 * (K : ℝ))) ^ 3 := by
    have h := numeric_gap hCE hCF (T := T) (by
      have : D + 1 = 512 * 21381376 * (CE ^ 2 + 1) * (CF + 1) + 74000 ^ 2 * (CF + 1)
          + 21381376 + 5 := by rw [hDdef]; ring
      rw [← this]
      exact hTD)
    rw [hM4def, ← hs1def, ← hs2def]
    rw [← hs1def, ← hs2def, ← hs3def, ← hKdef] at h
    exact h
  obtain ⟨S, hSzero, hScount⟩ := exists_heavyFinset hK1 hT0 hM40 hCdyadic h4win hEwin hgap
  obtain ⟨τS, hτSmem, hτScard⟩ := exists_distinct_ordinates hT0 hK1 S hSzero
  refine ⟨τS, hτSmem, ?_⟩
  -- the counting arithmetic
  have hcap : Real.sqrt ((T / K) * M4)
      ≤ Real.sqrt (CF + 1) * T * (1 + Real.log T) ^ 2 / Real.sqrt (K : ℝ) := by
    have hval : (Real.sqrt (CF + 1) * T * (1 + Real.log T) ^ 2 / Real.sqrt (K : ℝ)) ^ 2
        = (T / K) * M4 := by
      rw [hM4def, div_pow, mul_pow, mul_pow, Real.sq_sqrt (by linarith : (0 : ℝ) ≤ CF + 1),
        Real.sq_sqrt hKR0.le]
      have h1 : ((1 + Real.log T) ^ 2) ^ 2 = (1 + Real.log T) ^ 4 := by ring
      rw [h1, div_mul_eq_mul_div]
      congr 1
      ring
    have heq : Real.sqrt ((T / K) * M4)
        = Real.sqrt (CF + 1) * T * (1 + Real.log T) ^ 2 / Real.sqrt (K : ℝ) := by
      rw [← hval, Real.sqrt_sq (by positivity)]
    exact le_of_eq heq
  have hsK0 : (0 : ℝ) < Real.sqrt (K : ℝ) := Real.sqrt_pos.mpr hKR0
  have hcount : s4 ≤ 16 * (S.card : ℝ) * Real.sqrt (CF + 1) * (1 + Real.log T) ^ 2 := by
    have h2 : T / 8 ≤ (S.card : ℝ)
        * (Real.sqrt (CF + 1) * T * (1 + Real.log T) ^ 2 / Real.sqrt (K : ℝ)) := by
      refine le_trans hScount ?_
      exact mul_le_mul_of_nonneg_left hcap (by positivity)
    have h3 : (T / 8) * Real.sqrt (K : ℝ)
        ≤ (S.card : ℝ) * (Real.sqrt (CF + 1) * T * (1 + Real.log T) ^ 2) := by
      have h4 := mul_le_mul_of_nonneg_right h2 hsK0.le
      have h5 : (S.card : ℝ)
          * (Real.sqrt (CF + 1) * T * (1 + Real.log T) ^ 2 / Real.sqrt (K : ℝ))
          * Real.sqrt (K : ℝ)
          = (S.card : ℝ) * (Real.sqrt (CF + 1) * T * (1 + Real.log T) ^ 2) := by
        field_simp
      linarith [h5 ▸ h4]
    have hs4K : s4 / 2 ≤ Real.sqrt (K : ℝ) := by
      have h4 : (s4 / 2) ^ 2 ≤ (K : ℝ) := by
        have h5 : (s4 / 2) ^ 2 = s3 / 4 := by rw [← hs4sq]; ring
        rw [h5]
        linarith [hKge]
      have h6 := Real.sqrt_le_sqrt h4
      rwa [Real.sqrt_sq (by positivity)] at h6
    have h7 : (T / 8) * (s4 / 2)
        ≤ (S.card : ℝ) * (Real.sqrt (CF + 1) * T * (1 + Real.log T) ^ 2) := by
      have h8 : (T / 8) * (s4 / 2) ≤ (T / 8) * Real.sqrt (K : ℝ) :=
        mul_le_mul_of_nonneg_left hs4K (by positivity)
      linarith
    nlinarith [hT0, h7]
  have hcardcast : (S.card : ℝ) ≤ 2 * (τS.card : ℝ) + 1 := by exact_mod_cast hτScard
  have hlog2pos : (0 : ℝ) < (1 + Real.log T) ^ 2 := by positivity
  have hs4bound : s4 ≤ (32 * (τS.card : ℝ) + 16)
      * (Real.sqrt (CF + 1) * (1 + Real.log T) ^ 2) := by
    have hb : (0 : ℝ) ≤ Real.sqrt (CF + 1) * (1 + Real.log T) ^ 2 := by positivity
    nlinarith [hcount, hcardcast]
  have hlogsq : (1 + Real.log T) ^ 2 ≤ 4624 * Real.sqrt s4 := by
    have h1 := one_add_log_pow_four_le_sixteenth hT1
    rw [← hs1def, ← hs2def, ← hs3def, ← hs4def] at h1
    have h3 : (4624 * Real.sqrt s4) ^ 2 = 21381376 * s4 := by
      rw [mul_pow, Real.sq_sqrt hs40]
      norm_num
    have h2 : ((1 + Real.log T) ^ 2) ^ 2 ≤ (4624 * Real.sqrt s4) ^ 2 := by
      rw [h3]
      calc ((1 + Real.log T) ^ 2) ^ 2 = (1 + Real.log T) ^ 4 := by ring
        _ ≤ 21381376 * s4 := h1
    calc (1 + Real.log T) ^ 2
        = Real.sqrt (((1 + Real.log T) ^ 2) ^ 2) := (Real.sqrt_sq (by positivity)).symm
      _ ≤ Real.sqrt ((4624 * Real.sqrt s4) ^ 2) := Real.sqrt_le_sqrt h2
      _ = 4624 * Real.sqrt s4 := Real.sqrt_sq (by positivity)
  have himg1 : (1 : ℝ) ≤ (τS.card : ℝ) := by
    by_contra h0
    have h0lt : (τS.card : ℝ) < 1 := not_le.mp h0
    have h0' : τS.card = 0 := by
      by_contra h1
      have h2 : 1 ≤ τS.card := Nat.one_le_iff_ne_zero.mpr h1
      have h3 : (1 : ℝ) ≤ (τS.card : ℝ) := by exact_mod_cast h2
      linarith only [h0lt, h3]
    have hz : ((τS.card : ℕ) : ℝ) = 0 := by exact_mod_cast h0'
    rw [hz] at hs4bound
    have hsq4pos : (0 : ℝ) < Real.sqrt s4 := Real.sqrt_pos.mpr hs4pos
    have h2 : Real.sqrt s4 * Real.sqrt s4 = s4 := Real.mul_self_sqrt hs40
    have hsCF0 : (0 : ℝ) ≤ Real.sqrt (CF + 1) := Real.sqrt_nonneg _
    have h1 : s4 ≤ 16 * Real.sqrt (CF + 1) * (4624 * Real.sqrt s4) := by
      have hstep : Real.sqrt (CF + 1) * (1 + Real.log T) ^ 2
          ≤ Real.sqrt (CF + 1) * (4624 * Real.sqrt s4) :=
        mul_le_mul_of_nonneg_left hlogsq hsCF0
      calc s4 ≤ (32 * 0 + 16) * (Real.sqrt (CF + 1) * (1 + Real.log T) ^ 2) := hs4bound
        _ = 16 * (Real.sqrt (CF + 1) * (1 + Real.log T) ^ 2) := by ring
        _ ≤ 16 * (Real.sqrt (CF + 1) * (4624 * Real.sqrt s4)) := by
            linarith only [hstep]
        _ = 16 * Real.sqrt (CF + 1) * (4624 * Real.sqrt s4) := by ring
    have h3 : Real.sqrt s4 ≤ 73984 * Real.sqrt (CF + 1) := by
      have hcross : Real.sqrt s4 * Real.sqrt s4
          ≤ (73984 * Real.sqrt (CF + 1)) * Real.sqrt s4 := by
        calc Real.sqrt s4 * Real.sqrt s4 = s4 := h2
          _ ≤ 16 * Real.sqrt (CF + 1) * (4624 * Real.sqrt s4) := h1
          _ = (73984 * Real.sqrt (CF + 1)) * Real.sqrt s4 := by ring
      exact le_of_mul_le_mul_right hcross hsq4pos
    have hCFsq : Real.sqrt (CF + 1) * Real.sqrt (CF + 1) = CF + 1 :=
      Real.mul_self_sqrt (by linarith)
    have h4 : s4 ≤ 73984 ^ 2 * (CF + 1) := by
      have h5 : Real.sqrt s4 * Real.sqrt s4
          ≤ (73984 * Real.sqrt (CF + 1)) * (73984 * Real.sqrt (CF + 1)) :=
        mul_le_mul h3 h3 (Real.sqrt_nonneg _) (by positivity)
      calc s4 = Real.sqrt s4 * Real.sqrt s4 := h2.symm
        _ ≤ (73984 * Real.sqrt (CF + 1)) * (73984 * Real.sqrt (CF + 1)) := h5
        _ = 73984 ^ 2 * (Real.sqrt (CF + 1) * Real.sqrt (CF + 1)) := by ring
        _ = 73984 ^ 2 * (CF + 1) := by rw [hCFsq]
    rw [hDdef] at hs4D
    have hpos1 : (0 : ℝ) ≤ 512 * 21381376 * (CE ^ 2 + 1) * (CF + 1) := by positivity
    have hgap2 : 73984 ^ 2 * (CF + 1) ≤ 74000 ^ 2 * (CF + 1) := by
      linarith only [hCF]
    linarith only [hs4D, h4, hpos1, hgap2]
  have hfin : s4 ≤ 48 * (τS.card : ℝ)
      * ((Real.sqrt (CF + 1) + 1) * (1 + Real.log T) ^ 2) := by
    have hb : (0 : ℝ) ≤ Real.sqrt (CF + 1) * (1 + Real.log T) ^ 2 := by positivity
    have h1 : (32 * (τS.card : ℝ) + 16) * (Real.sqrt (CF + 1) * (1 + Real.log T) ^ 2)
        ≤ 48 * (τS.card : ℝ) * (Real.sqrt (CF + 1) * (1 + Real.log T) ^ 2) := by
      have h2 : 32 * (τS.card : ℝ) + 16 ≤ 48 * (τS.card : ℝ) := by
        linarith only [himg1]
      exact mul_le_mul_of_nonneg_right h2 hb
    have h3 : 48 * (τS.card : ℝ) * (Real.sqrt (CF + 1) * (1 + Real.log T) ^ 2)
        ≤ 48 * (τS.card : ℝ) * ((Real.sqrt (CF + 1) + 1) * (1 + Real.log T) ^ 2) := by
      have h4 : Real.sqrt (CF + 1) * (1 + Real.log T) ^ 2
          ≤ (Real.sqrt (CF + 1) + 1) * (1 + Real.log T) ^ 2 := by
        have h5 : (Real.sqrt (CF + 1) + 1) * (1 + Real.log T) ^ 2
            = Real.sqrt (CF + 1) * (1 + Real.log T) ^ 2 + (1 + Real.log T) ^ 2 := by
          ring
        rw [h5]
        linarith only [hlog2pos]
      exact mul_le_mul_of_nonneg_left h4 (by positivity)
    linarith only [hs4bound, h1, h3]
  rw [div_le_iff₀ hlog2pos]
  have hkey2 : 1 / (48 * (Real.sqrt (CF + 1) + 1)) * s4
      ≤ 1 / (48 * (Real.sqrt (CF + 1) + 1))
        * (48 * (τS.card : ℝ) * ((Real.sqrt (CF + 1) + 1) * (1 + Real.log T) ^ 2)) :=
    mul_le_mul_of_nonneg_left hfin (by positivity)
  have hne : (48 : ℝ) * (Real.sqrt (CF + 1) + 1) ≠ 0 := by positivity
  have hsimp : 1 / (48 * (Real.sqrt (CF + 1) + 1))
      * (48 * (τS.card : ℝ) * ((Real.sqrt (CF + 1) + 1) * (1 + Real.log T) ^ 2))
      = (τS.card : ℝ) * (1 + Real.log T) ^ 2 := by
    field_simp
  rw [hsimp] at hkey2
  exact hkey2

end

end RHTower

namespace RHTower

noncomputable section

/-! ## Injection into the critical-line census -/

set_option maxHeartbeats 800000 in
/-- Distinct ordinates in `(T, 2T]` carrying critical-line zeros inject into the census
difference between heights `2T` and `T`. -/
theorem xiPosCriticalZeroCount_add_card_le {T : ℝ} (hT0 : 0 < T) (τS : Finset ℝ)
    (hmem : ∀ τ ∈ τS, T < τ ∧ τ ≤ 2 * T ∧ riemannZeta (linePt τ) = 0) :
    xiPosCriticalZeroCount T + τS.card ≤ xiPosCriticalZeroCount (2 * T) := by
  classical
  set A : Finset ℂ := (stripFinsetPos T).filter (fun z => z.re = 1 / 2) with hA
  set B : Finset ℂ := (stripFinsetPos (2 * T)).filter (fun z => z.re = 1 / 2) with hB
  set C : Finset ℂ := τS.image linePt with hCdef
  have hxiz : ∀ τ ∈ τS, xi (linePt τ) = 0 := by
    intro τ hτ
    rw [xi_line_eq_zero_iff_hardyZ]
    have hnorm := norm_riemannZeta_line_eq_abs_hardyZ τ
    rw [(hmem τ hτ).2.2, norm_zero] at hnorm
    exact abs_eq_zero.mp hnorm.symm
  have hCB : C ⊆ B := by
    intro z hz
    rw [hCdef, Finset.mem_image] at hz
    obtain ⟨τ, hτ, rfl⟩ := hz
    rw [hB, Finset.mem_filter, mem_stripFinsetPos]
    obtain ⟨h1, h2, _⟩ := hmem τ hτ
    refine ⟨⟨linePt_re_pos τ, linePt_re_lt_one τ, ?_, ?_, hxiz τ hτ⟩, linePt_re τ⟩
    · rw [linePt_im]; linarith
    · rw [linePt_im]; exact h2
  have hAB : A ⊆ B :=
    Finset.filter_subset_filter _ (stripFinsetPos_subset (by linarith))
  have hdisj : Disjoint A C := by
    rw [Finset.disjoint_right]
    intro z hz
    rw [hCdef, Finset.mem_image] at hz
    obtain ⟨τ, hτ, rfl⟩ := hz
    rw [hA, Finset.mem_filter, mem_stripFinsetPos]
    rintro ⟨⟨_, _, _, him, _⟩, _⟩
    rw [linePt_im] at him
    linarith [(hmem τ hτ).1]
  have hcardC : C.card = τS.card := by
    rw [hCdef]
    refine Finset.card_image_of_injOn ?_
    intro a _ b _ hab
    have h := congrArg Complex.im hab
    rwa [linePt_im, linePt_im] at h
  have hCcount : C.card ≤ ∑ z ∈ C, (analyticOrderAt xi z).toNat := by
    have h1 : ∀ z ∈ C, 1 ≤ (analyticOrderAt xi z).toNat := by
      intro z hz
      rw [hCdef, Finset.mem_image] at hz
      obtain ⟨τ, hτ, rfl⟩ := hz
      exact Nat.one_le_iff_ne_zero.mpr (xi_order_toNat_ne_zero (hxiz τ hτ))
    calc C.card = ∑ _z ∈ C, 1 := by rw [Finset.sum_const, smul_eq_mul, mul_one]
      _ ≤ ∑ z ∈ C, (analyticOrderAt xi z).toNat := Finset.sum_le_sum h1
  have hunion : ∑ z ∈ A ∪ C, (analyticOrderAt xi z).toNat
      = ∑ z ∈ A, (analyticOrderAt xi z).toNat + ∑ z ∈ C, (analyticOrderAt xi z).toNat :=
    Finset.sum_union hdisj
  have hmono : ∑ z ∈ A ∪ C, (analyticOrderAt xi z).toNat
      ≤ ∑ z ∈ B, (analyticOrderAt xi z).toNat :=
    Finset.sum_le_sum_of_subset (Finset.union_subset hAB hCB)
  rw [xiPosCriticalZeroCount, xiPosCriticalZeroCount, ← hA, ← hB]
  omega

/-- **The critical-line census difference grows polynomially.**  Unconditionally, the number
of critical-line zeros of `xi` with ordinate in `(T, 2T]`, counted with multiplicity, is at
least `c · T^{1/16} / (1 + log T)²` for all large `T`. -/
theorem exists_sixteenthRoot_le_xiPosCriticalZeroCount_sub :
    ∃ c : ℝ, 0 < c ∧ ∃ T₁ : ℝ, 1 ≤ T₁ ∧ ∀ T : ℝ, T₁ ≤ T →
      c * Real.sqrt (Real.sqrt (Real.sqrt (Real.sqrt T))) / (1 + Real.log T) ^ 2
        ≤ (xiPosCriticalZeroCount (2 * T) : ℝ) - (xiPosCriticalZeroCount T : ℝ) := by
  obtain ⟨c, hc, T₁, hT₁, h⟩ := exists_many_distinct_line_zeros_dyadic
  refine ⟨c, hc, T₁, hT₁, fun T hT => ?_⟩
  obtain ⟨τS, hmemS, hcard⟩ := h T hT
  have hT0 : (0 : ℝ) < T := by linarith
  have hinj := xiPosCriticalZeroCount_add_card_le hT0 τS hmemS
  have hcast : (xiPosCriticalZeroCount T : ℝ) + (τS.card : ℝ)
      ≤ (xiPosCriticalZeroCount (2 * T) : ℝ) := by exact_mod_cast hinj
  linarith [hcard, hcast]

set_option maxHeartbeats 800000 in
/-- **A polynomial lower bound for the critical-line census.**  Unconditionally, the number of
critical-line zeros of `xi` with ordinate in `(0, T]`, counted with multiplicity, is at least
`c · T^{1/16} / (1 + log T)²` for all large `T` — a polynomial strengthening of the
logarithmic Hardy census. -/
theorem exists_sixteenthRoot_le_xiPosCriticalZeroCount :
    ∃ c : ℝ, 0 < c ∧ ∃ T₁ : ℝ, 1 ≤ T₁ ∧ ∀ T : ℝ, T₁ ≤ T →
      c * Real.sqrt (Real.sqrt (Real.sqrt (Real.sqrt T))) / (1 + Real.log T) ^ 2
        ≤ (xiPosCriticalZeroCount T : ℝ) := by
  obtain ⟨c, hc, T₁, hT₁, h⟩ := exists_sixteenthRoot_le_xiPosCriticalZeroCount_sub
  refine ⟨c / 2, by positivity, max (2 * T₁) 2, ?_, fun T hT => ?_⟩
  · have h1 := le_max_right (2 * T₁) 2
    linarith
  have hT2 : (2 : ℝ) ≤ T := le_trans (le_max_right _ _) hT
  have hT20 : (0 : ℝ) < T / 2 := by linarith
  have hhalf : T₁ ≤ T / 2 := by
    have h1 := le_trans (le_max_left (2 * T₁) 2) hT
    linarith
  have hspec := h (T / 2) hhalf
  rw [show 2 * (T / 2) = T by ring] at hspec
  have hl1 : (0 : ℝ) ≤ Real.log (T / 2) := Real.log_nonneg (by linarith)
  have hl2 : Real.log (T / 2) ≤ Real.log T := Real.log_le_log hT20 (by linarith)
  have hp1 : (0 : ℝ) < 1 + Real.log (T / 2) := by linarith
  have hp2 : (0 : ℝ) < 1 + Real.log T := by linarith
  have hlogc : (1 + Real.log (T / 2)) ^ 2 ≤ (1 + Real.log T) ^ 2 :=
    pow_le_pow_left₀ hp1.le (by linarith) 2
  have hchain : Real.sqrt (Real.sqrt (Real.sqrt (Real.sqrt T)))
      ≤ 2 * Real.sqrt (Real.sqrt (Real.sqrt (Real.sqrt (T / 2)))) := by
    set u : ℝ := Real.sqrt (Real.sqrt (Real.sqrt (Real.sqrt (T / 2)))) with hu
    have hu0 : 0 ≤ u := Real.sqrt_nonneg _
    have h1 : u ^ 2 = Real.sqrt (Real.sqrt (Real.sqrt (T / 2))) := by
      rw [hu, Real.sq_sqrt (Real.sqrt_nonneg _)]
    have h2 : (u ^ 2) ^ 2 = Real.sqrt (Real.sqrt (T / 2)) := by
      rw [h1, Real.sq_sqrt (Real.sqrt_nonneg _)]
    have h3 : ((u ^ 2) ^ 2) ^ 2 = Real.sqrt (T / 2) := by
      rw [h2, Real.sq_sqrt (Real.sqrt_nonneg _)]
    have h4 : (((u ^ 2) ^ 2) ^ 2) ^ 2 = T / 2 := by
      rw [h3, Real.sq_sqrt hT20.le]
    have h5 : u ^ 16 = T / 2 := by
      have h6 : u ^ 16 = (((u ^ 2) ^ 2) ^ 2) ^ 2 := by ring
      rw [h6, h4]
    have hTle : T ≤ (2 * u) ^ 16 := by
      have h7 : (2 * u) ^ 16 = 65536 * u ^ 16 := by ring
      rw [h7, h5]
      linarith
    have hmono2 : Real.sqrt (Real.sqrt (Real.sqrt (Real.sqrt T)))
        ≤ Real.sqrt (Real.sqrt (Real.sqrt (Real.sqrt ((2 * u) ^ 16)))) :=
      Real.sqrt_le_sqrt (Real.sqrt_le_sqrt (Real.sqrt_le_sqrt (Real.sqrt_le_sqrt hTle)))
    rwa [sqrt_sq_chain (by positivity : (0 : ℝ) ≤ 2 * u)] at hmono2
  have hlogsq1 : (0 : ℝ) < (1 + Real.log T) ^ 2 := pow_pos hp2 2
  have hlogsq2 : (0 : ℝ) < (1 + Real.log (T / 2)) ^ 2 := pow_pos hp1 2
  have hfinal : c / 2 * Real.sqrt (Real.sqrt (Real.sqrt (Real.sqrt T)))
      / (1 + Real.log T) ^ 2
      ≤ c * Real.sqrt (Real.sqrt (Real.sqrt (Real.sqrt (T / 2))))
        / (1 + Real.log (T / 2)) ^ 2 := by
    rw [div_le_div_iff₀ hlogsq1 hlogsq2]
    have hprod : Real.sqrt (Real.sqrt (Real.sqrt (Real.sqrt T)))
        * (1 + Real.log (T / 2)) ^ 2
        ≤ (2 * Real.sqrt (Real.sqrt (Real.sqrt (Real.sqrt (T / 2)))))
          * (1 + Real.log T) ^ 2 :=
      mul_le_mul hchain hlogc hlogsq2.le (by positivity)
    have hscale := mul_le_mul_of_nonneg_left hprod (by positivity : (0 : ℝ) ≤ c / 2)
    calc c / 2 * Real.sqrt (Real.sqrt (Real.sqrt (Real.sqrt T)))
          * (1 + Real.log (T / 2)) ^ 2
        = c / 2 * (Real.sqrt (Real.sqrt (Real.sqrt (Real.sqrt T)))
          * (1 + Real.log (T / 2)) ^ 2) := by ring
      _ ≤ c / 2 * ((2 * Real.sqrt (Real.sqrt (Real.sqrt (Real.sqrt (T / 2)))))
          * (1 + Real.log T) ^ 2) := hscale
      _ = c * Real.sqrt (Real.sqrt (Real.sqrt (Real.sqrt (T / 2))))
          * (1 + Real.log T) ^ 2 := by ring
  have hcnn : (0 : ℝ) ≤ (xiPosCriticalZeroCount (T / 2) : ℝ) := Nat.cast_nonneg _
  calc c / 2 * Real.sqrt (Real.sqrt (Real.sqrt (Real.sqrt T))) / (1 + Real.log T) ^ 2
      ≤ c * Real.sqrt (Real.sqrt (Real.sqrt (Real.sqrt (T / 2))))
        / (1 + Real.log (T / 2)) ^ 2 := hfinal
    _ ≤ (xiPosCriticalZeroCount T : ℝ) - (xiPosCriticalZeroCount (T / 2) : ℝ) := hspec
    _ ≤ (xiPosCriticalZeroCount T : ℝ) := by linarith

end

end RHTower

namespace RHTower

noncomputable section

/-! ## Cauchy–Schwarz counting over the heavy windows

The per-window mass cap `m_k ≤ √(H·M4)` wastes the fourth moment: summing the caps over the
heavy set and applying Cauchy–Schwarz to the *sum* instead gives `(T/8)² ≤ |S| · H · M4`,
a quadratically stronger count.  With the trivial window mean this lifts the census exponent
from `T^{1/16}` to `T^{1/6}`, the ceiling of this route. -/

set_option maxHeartbeats 1600000 in
/-- **Heavy-window pigeonhole with Cauchy–Schwarz counting.**  If the dyadic second moment is
at least `T/4`, the dyadic fourth moment is at most `M4`, and every window mean is at most
`ME` with `ME² M4` losing to the cube of the heaviness threshold, then a family of windows —
each carrying a critical-line zero — exists with `(T/8)² ≤ |S| · (T/K) · M4`. -/
private theorem exists_heavyFinset_sq {T : ℝ} {K : ℕ} (hK1 : 1 ≤ K) (hT0 : 0 < T)
    {M4 ME : ℝ} (hM4 : 0 < M4)
    (hC : T / 4 ≤ ∫ τ in T..(2 * T), (hardyZ τ) ^ 2)
    (h4tot : (∫ τ in T..(2 * T), (hardyZ τ) ^ 4) ≤ M4)
    (hE : ∀ k : ℕ, k < K →
      |∫ τ in (T + k * (T / K))..(T + ((k + 1 : ℕ) : ℝ) * (T / K)), hardyZ τ| ≤ ME)
    (hgap : ME ^ 2 * M4 < (T / (8 * K)) ^ 3) :
    ∃ S : Finset ℕ,
      (∀ k ∈ S, k < K ∧ ∃ τ, ((T + k * (T / K) ≤ τ ∧ τ ≤ T + ((k + 1 : ℕ) : ℝ) * (T / K)) ∧
        riemannZeta (linePt τ) = 0)) ∧
      (T / 8) ^ 2 ≤ (S.card : ℝ) * ((T / K) * M4) := by
  classical
  have hKR0 : (0 : ℝ) < (K : ℝ) := by exact_mod_cast hK1
  have hTK0 : (0 : ℝ) < T / K := by positivity
  have h4win := window_fourth_le hK1 hT0 h4tot
  set a : ℕ → ℝ := fun k => T + k * (T / K) with hadef
  have ha_le : ∀ k : ℕ, a k ≤ a (k + 1) := by
    intro k
    rw [hadef]
    dsimp only
    push_cast
    nlinarith [hTK0]
  set m : ℕ → ℝ := fun k => ∫ τ in (a k)..(a (k + 1)), (hardyZ τ) ^ 2 with hmdef
  set m4 : ℕ → ℝ := fun k => ∫ τ in (a k)..(a (k + 1)), (hardyZ τ) ^ 4 with hm4def
  have hm0 : ∀ k : ℕ, 0 ≤ m k := by
    intro k
    rw [hmdef]
    exact intervalIntegral.integral_nonneg (ha_le k) (fun u _ => sq_nonneg _)
  have hm40' : ∀ k : ℕ, 0 ≤ m4 k := by
    intro k
    rw [hm4def]
    exact intervalIntegral.integral_nonneg (ha_le k) (fun u _ => by positivity)
  have hpart : ∑ k ∈ range K, m k = ∫ τ in T..(2 * T), (hardyZ τ) ^ 2 := by
    have h := intervalIntegral.sum_integral_adjacent_intervals
      (f := fun τ => (hardyZ τ) ^ 2) (μ := volume)
      (a := fun k : ℕ => T + k * (T / K)) (n := K)
      (fun k _ => ((continuous_hardyZ.pow 2).intervalIntegrable _ _))
    have hz : T + ((0 : ℕ) : ℝ) * (T / K) = T := by push_cast; ring
    have hK' : T + (K : ℝ) * (T / K) = 2 * T := by field_simp; ring
    rw [hz, hK'] at h
    simp only [hmdef, hadef]
    exact h
  have hpart4 : ∑ k ∈ range K, m4 k = ∫ τ in T..(2 * T), (hardyZ τ) ^ 4 := by
    have h := intervalIntegral.sum_integral_adjacent_intervals
      (f := fun τ => (hardyZ τ) ^ 4) (μ := volume)
      (a := fun k : ℕ => T + k * (T / K)) (n := K)
      (fun k _ => ((continuous_hardyZ.pow 4).intervalIntegrable _ _))
    have hz : T + ((0 : ℕ) : ℝ) * (T / K) = T := by push_cast; ring
    have hK' : T + (K : ℝ) * (T / K) = 2 * T := by field_simp; ring
    rw [hz, hK'] at h
    simp only [hm4def, hadef]
    exact h
  set Θ : ℝ := T / (8 * K) with hΘdef
  have hΘ0 : (0 : ℝ) < Θ := by positivity
  set S : Finset ℕ := (range K).filter (fun k => Θ ≤ m k) with hSdef
  have hSmem : ∀ k ∈ S, k < K ∧ Θ ≤ m k := fun k hk =>
    ⟨Finset.mem_range.mp (Finset.mem_filter.mp hk).1, (Finset.mem_filter.mp hk).2⟩
  refine ⟨S, fun k hk => ⟨(hSmem k hk).1, ?_⟩, ?_⟩
  · -- the sign-change detector on a heavy window
    have hkK := (hSmem k hk).1
    have hΘm := (hSmem k hk).2
    have hΘm' : Θ ≤ ∫ τ in (a k)..(a (k + 1)), (hardyZ τ) ^ 2 := by
      simpa only [hmdef] using hΘm
    have hgap' : (∫ τ in (a k)..(a (k + 1)), hardyZ τ) ^ 2 * M4 < Θ ^ 3 := by
      have h2 := hE k hkK
      have h3 : |∫ τ in (a k)..(a (k + 1)), hardyZ τ| ≤ ME := by
        rw [hadef]
        dsimp only
        exact h2
      have h4' := abs_le.mp h3
      have h1 : (∫ τ in (a k)..(a (k + 1)), hardyZ τ) ^ 2 ≤ ME ^ 2 := by
        nlinarith [h4'.1, h4'.2]
      have h5 : (∫ τ in (a k)..(a (k + 1)), hardyZ τ) ^ 2 * M4 ≤ ME ^ 2 * M4 :=
        mul_le_mul_of_nonneg_right h1 hM4.le
      calc (∫ τ in (a k)..(a (k + 1)), hardyZ τ) ^ 2 * M4 ≤ ME ^ 2 * M4 := h5
        _ < (T / (8 * K)) ^ 3 := hgap
        _ = Θ ^ 3 := by rw [hΘdef]
    have h4' : (∫ τ in (a k)..(a (k + 1)), (hardyZ τ) ^ 4) ≤ M4 := by
      have h := h4win k hkK
      rw [hadef]
      dsimp only
      exact h
    obtain ⟨τ, hτ, hz⟩ := exists_riemannZeta_line_zero_of_hardyZ_fourth_moment_gap
      (α := a k) (β := a (k + 1)) (S := Θ) (F := M4) (ha_le k) hΘ0 hΘm' h4' hgap'
    refine ⟨τ, ⟨?_, ?_⟩, hz⟩
    · have h := hτ.1
      rw [hadef] at h
      exact h
    · have h := hτ.2
      rw [hadef] at h
      exact h
  · -- the Cauchy–Schwarz weight bound
    have hlight : ∑ k ∈ (range K).filter (fun k => ¬ Θ ≤ m k), m k ≤ T / 8 := by
      have h1 : ∀ k ∈ (range K).filter (fun k => ¬ Θ ≤ m k), m k ≤ Θ := by
        intro k hk
        have := (Finset.mem_filter.mp hk).2
        linarith [lt_of_not_ge this]
      have h2 := Finset.sum_le_card_nsmul _ _ _ h1
      rw [nsmul_eq_mul] at h2
      have h3 : (((range K).filter (fun k => ¬ Θ ≤ m k)).card : ℝ) ≤ (K : ℝ) := by
        exact_mod_cast le_trans (Finset.card_filter_le _ _)
          (le_of_eq (Finset.card_range K))
      have h4' : (((range K).filter (fun k => ¬ Θ ≤ m k)).card : ℝ) * Θ ≤ (K : ℝ) * Θ :=
        mul_le_mul_of_nonneg_right h3 hΘ0.le
      have h5 : (K : ℝ) * Θ = T / 8 := by
        rw [hΘdef]
        field_simp
      linarith
    have hheavy : T / 8 ≤ ∑ k ∈ S, m k := by
      have h := Finset.sum_filter_add_sum_filter_not (range K) (fun k => Θ ≤ m k) m
      have hC' : T / 4 ≤ ∑ k ∈ range K, m k := by
        rw [hpart]
        exact hC
      rw [hSdef]
      linarith [hlight, hC', h]
    have hsq : ∀ k ∈ S, (m k) ^ 2 ≤ (T / K) * m4 k := by
      intro k hk
      have hle := ha_le k
      have hlen : a (k + 1) - a k = T / K := by
        rw [hadef]
        dsimp only
        push_cast
        ring
      have hf : MeasureTheory.IntegrableOn (fun τ => (hardyZ τ) ^ 2)
          (Set.Ioc (a k) (a (k + 1))) MeasureTheory.volume :=
        (continuous_hardyZ.pow 2).integrableOn_Ioc
      have hf2 : MeasureTheory.IntegrableOn (fun τ => ((hardyZ τ) ^ 2) ^ 2)
          (Set.Ioc (a k) (a (k + 1))) MeasureTheory.volume := by
        have h : MeasureTheory.IntegrableOn (fun τ => (hardyZ τ) ^ 4)
            (Set.Ioc (a k) (a (k + 1))) MeasureTheory.volume :=
          (continuous_hardyZ.pow 4).integrableOn_Ioc
        exact MeasureTheory.IntegrableOn.congr_fun h (fun τ _ => by ring)
          measurableSet_Ioc
      have h2 := GaloisForLFunctions.HTGeometry.sq_integral_le_length_mul hle hf hf2
      have hcongr : (∫ τ in Set.Ioc (a k) (a (k + 1)), ((hardyZ τ) ^ 2) ^ 2)
          = ∫ τ in Set.Ioc (a k) (a (k + 1)), (hardyZ τ) ^ 4 := by
        apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioc
        intro τ _
        ring
      rw [hcongr, hlen] at h2
      have hIoc1 : (∫ τ in (a k)..(a (k + 1)), (hardyZ τ) ^ 2)
          = ∫ τ in Set.Ioc (a k) (a (k + 1)), (hardyZ τ) ^ 2 :=
        intervalIntegral.integral_of_le hle
      have hIoc2 : (∫ τ in (a k)..(a (k + 1)), (hardyZ τ) ^ 4)
          = ∫ τ in Set.Ioc (a k) (a (k + 1)), (hardyZ τ) ^ 4 :=
        intervalIntegral.integral_of_le hle
      have h8 : m k = ∫ τ in Set.Ioc (a k) (a (k + 1)), (hardyZ τ) ^ 2 := by
        rw [hmdef]
        dsimp only
        exact hIoc1
      have h9 : m4 k = ∫ τ in Set.Ioc (a k) (a (k + 1)), (hardyZ τ) ^ 4 := by
        rw [hm4def]
        dsimp only
        exact hIoc2
      rw [h8, h9]
      exact h2
    have hCS := Finset.sum_mul_sq_le_sq_mul_sq S (fun _ => (1 : ℝ)) m
    simp only [one_mul, one_pow] at hCS
    rw [Finset.sum_const, nsmul_eq_mul, mul_one] at hCS
    have hsum2 : ∑ k ∈ S, (m k) ^ 2 ≤ (T / K) * ∑ k ∈ S, m4 k := by
      calc ∑ k ∈ S, (m k) ^ 2 ≤ ∑ k ∈ S, (T / K) * m4 k := Finset.sum_le_sum hsq
        _ = (T / K) * ∑ k ∈ S, m4 k := by rw [Finset.mul_sum]
    have hsub4 : ∑ k ∈ S, m4 k ≤ ∑ k ∈ range K, m4 k := by
      refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun i _ _ => hm40' i)
      rw [hSdef]
      exact Finset.filter_subset _ _
    have htot : ∑ k ∈ S, m4 k ≤ M4 := by
      rw [hpart4] at hsub4
      linarith [h4tot]
    have hTsq : (T / 8) ^ 2 ≤ (∑ k ∈ S, m k) ^ 2 := by
      have h0 : (0 : ℝ) ≤ T / 8 := by positivity
      exact pow_le_pow_left₀ h0 hheavy 2
    have hcard0 : (0 : ℝ) ≤ (S.card : ℝ) := Nat.cast_nonneg _
    calc (T / 8) ^ 2 ≤ (∑ k ∈ S, m k) ^ 2 := hTsq
      _ ≤ (S.card : ℝ) * ∑ k ∈ S, (m k) ^ 2 := hCS
      _ ≤ (S.card : ℝ) * ((T / K) * ∑ k ∈ S, m4 k) :=
          mul_le_mul_of_nonneg_left hsum2 hcard0
      _ ≤ (S.card : ℝ) * ((T / K) * M4) := by
          have h1 : (T / K) * ∑ k ∈ S, m4 k ≤ (T / K) * M4 :=
            mul_le_mul_of_nonneg_left htot hTK0.le
          exact mul_le_mul_of_nonneg_left h1 hcard0

set_option maxHeartbeats 1600000 in
/-- The moment gap for the sign-change detector follows from the key coefficient inequality
`512 K³ CE² (CF+1) (1+log T)⁴ < √T`. -/
private theorem gap_of_key {T CE CF : ℝ} {K : ℕ} (hT0 : 0 < T) (hK1 : 1 ≤ K)
    (hkey : 512 * (K : ℝ) ^ 3 * CE ^ 2 * (CF + 1) * (1 + Real.log T) ^ 4 < Real.sqrt T) :
    (CE * (Real.sqrt T * Real.sqrt (Real.sqrt T))) ^ 2
        * ((CF + 1) * T * (1 + Real.log T) ^ 4)
      < (T / (8 * (K : ℝ))) ^ 3 := by
  have hKR0 : (0 : ℝ) < (K : ℝ) := by exact_mod_cast hK1
  have hs1pos : (0 : ℝ) < Real.sqrt T := Real.sqrt_pos.mpr hT0
  have hs1sq : Real.sqrt T ^ 2 = T := Real.sq_sqrt hT0.le
  have hs2sq : Real.sqrt (Real.sqrt T) ^ 2 = Real.sqrt T :=
    Real.sq_sqrt (Real.sqrt_nonneg T)
  have hmean : (CE * (Real.sqrt T * Real.sqrt (Real.sqrt T))) ^ 2
      = CE ^ 2 * (T * Real.sqrt T) := by
    rw [mul_pow, mul_pow, hs1sq, hs2sq]
  have hΘcube : (T / (8 * (K : ℝ))) ^ 3 = T ^ 3 / (512 * (K : ℝ) ^ 3) := by
    rw [div_pow]
    congr 1
    ring
  rw [hmean, hΘcube, lt_div_iff₀ (by positivity : (0 : ℝ) < 512 * (K : ℝ) ^ 3)]
  have hT3 : T ^ 3 = T ^ 2 * Real.sqrt T ^ 2 := by rw [hs1sq]; ring
  rw [hT3]
  have hlhs : CE ^ 2 * (T * Real.sqrt T) * ((CF + 1) * T * (1 + Real.log T) ^ 4)
      * (512 * (K : ℝ) ^ 3)
      = (512 * (K : ℝ) ^ 3 * CE ^ 2 * (CF + 1) * (1 + Real.log T) ^ 4)
        * (Real.sqrt T * T ^ 2) := by ring
  rw [hlhs]
  have hstep := mul_lt_mul_of_pos_right hkey (mul_pos hs1pos (pow_pos hT0 2))
  calc (512 * (K : ℝ) ^ 3 * CE ^ 2 * (CF + 1) * (1 + Real.log T) ^ 4)
        * (Real.sqrt T * T ^ 2)
      < Real.sqrt T * (Real.sqrt T * T ^ 2) := hstep
    _ = T ^ 2 * Real.sqrt T ^ 2 := by ring

/-! ## Iterated square roots as real powers -/

private theorem nested_four_sqrt_eq_rpow {T : ℝ} (hT0 : 0 ≤ T) :
    Real.sqrt (Real.sqrt (Real.sqrt (Real.sqrt T))) = T ^ ((1 : ℝ) / 16) := by
  have h1 : Real.sqrt T = T ^ ((1 : ℝ) / 2) := Real.sqrt_eq_rpow T
  have h2 : Real.sqrt (Real.sqrt T) = T ^ ((1 : ℝ) / 4) := by
    rw [h1, Real.sqrt_eq_rpow, ← Real.rpow_mul hT0]
    congr 1
    norm_num
  have h3 : Real.sqrt (Real.sqrt (Real.sqrt T)) = T ^ ((1 : ℝ) / 8) := by
    rw [h2, Real.sqrt_eq_rpow, ← Real.rpow_mul hT0]
    congr 1
    norm_num
  rw [h3, Real.sqrt_eq_rpow, ← Real.rpow_mul hT0]
  congr 1
  norm_num

private theorem log_sq_le_rpow {T : ℝ} (hT1 : 1 ≤ T) :
    (1 + Real.log T) ^ 2 ≤ 4624 * T ^ ((1 : ℝ) / 32) := by
  have hT0 : (0 : ℝ) < T := by linarith
  have h4 := one_add_log_pow_four_le_sixteenth hT1
  rw [nested_four_sqrt_eq_rpow hT0.le] at h4
  have hval : Real.sqrt (21381376 * T ^ ((1 : ℝ) / 16)) = 4624 * T ^ ((1 : ℝ) / 32) := by
    rw [show (21381376 : ℝ) = 4624 ^ 2 by norm_num,
      Real.sqrt_mul (by positivity) _,
      Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 4624),
      Real.sqrt_eq_rpow, ← Real.rpow_mul hT0.le]
    congr 2
    norm_num
  calc (1 + Real.log T) ^ 2
      = Real.sqrt (((1 + Real.log T) ^ 2) ^ 2) := (Real.sqrt_sq (by positivity)).symm
    _ ≤ Real.sqrt (21381376 * T ^ ((1 : ℝ) / 16)) := Real.sqrt_le_sqrt (by
        calc ((1 + Real.log T) ^ 2) ^ 2 = (1 + Real.log T) ^ 4 := by ring
          _ ≤ 21381376 * T ^ ((1 : ℝ) / 16) := h4)
    _ = 4624 * T ^ ((1 : ℝ) / 32) := hval

end

end RHTower

namespace RHTower

noncomputable section

set_option maxHeartbeats 3200000 in
/-- **Sixth-root many distinct critical-line ordinates.**  Unconditionally, at least
`c · T^{1/6} / (1 + log T)⁶` distinct ordinates in `(T, 2T]` carry critical-line zeros
`ζ(1/2 + iτ) = 0`, for all large `T`. -/
theorem exists_many_distinct_line_zeros_dyadic_sixth :
    ∃ c : ℝ, 0 < c ∧ ∃ T₁ : ℝ, 1 ≤ T₁ ∧ ∀ T : ℝ, T₁ ≤ T →
      ∃ τS : Finset ℝ, (∀ τ ∈ τS, T < τ ∧ τ ≤ 2 * T ∧ riemannZeta (linePt τ) = 0) ∧
        c * T ^ ((1 : ℝ) / 6) / (1 + Real.log T) ^ 6 ≤ (τS.card : ℝ) := by
  classical
  obtain ⟨TC, hTC0, hC⟩ := exists_le_integral_hardyZ_sq
  obtain ⟨CF, hCF, hF⟩ := exists_integral_hardyZ_pow_four_dyadic_real_le
  obtain ⟨CE, hCE, hE⟩ := exists_abs_integral_hardyZ_window_le
  set D0 : ℝ := 512 * (CE ^ 2 + 1) * (CF + 1) + 8 with hD0def
  have hD08 : (8 : ℝ) ≤ D0 := by
    rw [hD0def]
    nlinarith [sq_nonneg CE, hCF]
  have hD0pos : (0 : ℝ) < D0 := by linarith only [hD08]
  set Y : ℝ := 9248 * D0 + 384 * D0 * (CF + 1) * 4624 ^ 3 + 2 with hYdef
  have hY2 : (2 : ℝ) ≤ Y := by
    rw [hYdef]
    nlinarith [hD08, hCF, mul_nonneg (le_of_lt hD0pos) hCF]
  clear_value D0 Y
  refine ⟨1 / (384 * D0 * (CF + 1) + 1), one_div_pos.mpr (by
      nlinarith [hD08, hCF, mul_nonneg (le_of_lt hD0pos) hCF]),
    max (max TC 16) (Y ^ 96), ?_, fun T hT => ?_⟩
  · refine le_trans ?_ (le_max_right _ _)
    exact one_le_pow₀ (by linarith only [hY2])
  have hT16 : (16 : ℝ) ≤ T := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hT
  have hTTC : TC ≤ T := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hT
  have hTY : Y ^ 96 ≤ T := le_trans (le_max_right _ _) hT
  have hT0 : (0 : ℝ) < T := by linarith only [hT16]
  have hT1 : (1 : ℝ) ≤ T := by linarith only [hT16]
  have hL1 : (1 : ℝ) ≤ 1 + Real.log T := by
    have := Real.log_nonneg hT1
    linarith
  have hL0 : (0 : ℝ) < 1 + Real.log T := by linarith
  -- the 96th-root device
  have hroot : Y ≤ T ^ ((1 : ℝ) / 96) := by
    have h1 : ((Y ^ 96 : ℝ)) ^ ((1 : ℝ) / 96) ≤ T ^ ((1 : ℝ) / 96) :=
      Real.rpow_le_rpow (by positivity) hTY (by norm_num)
    have h2 : ((Y ^ 96 : ℝ)) ^ ((1 : ℝ) / 96) = Y := by
      rw [← Real.rpow_natCast Y 96,
        ← Real.rpow_mul (by linarith only [hY2] : (0 : ℝ) ≤ Y),
        show ((96 : ℕ) : ℝ) * ((1 : ℝ) / 96) = 1 by norm_num, Real.rpow_one]
    linarith only [h1, h2.symm.le, h2.le]
  have hpow13 : (T ^ ((1 : ℝ) / 96)) ^ (13 : ℕ) = T ^ ((13 : ℝ) / 96) := by
    rw [← Real.rpow_natCast (T ^ ((1 : ℝ) / 96)) 13, ← Real.rpow_mul hT0.le]
    congr 1
    norm_num
  have hpow7 : (T ^ ((1 : ℝ) / 96)) ^ (7 : ℕ) = T ^ ((7 : ℝ) / 96) := by
    rw [← Real.rpow_natCast (T ^ ((1 : ℝ) / 96)) 7, ← Real.rpow_mul hT0.le]
    congr 1
    norm_num
  have hLsq : (1 + Real.log T) ^ 2 ≤ 4624 * T ^ ((1 : ℝ) / 32) := log_sq_le_rpow hT1
  -- the window count K
  set x : ℝ := T ^ ((1 : ℝ) / 6) / (D0 * (1 + Real.log T) ^ 2) with hxdef
  have hDL2pos : (0 : ℝ) < D0 * (1 + Real.log T) ^ 2 := mul_pos hD0pos (pow_pos hL0 2)
  have hx0 : 0 < x := by
    rw [hxdef]
    exact div_pos (Real.rpow_pos_of_pos hT0 _) hDL2pos
  have hx2 : (2 : ℝ) ≤ x := by
    have h13 : Y ≤ T ^ ((13 : ℝ) / 96) := by
      have ha : Y ^ 1 ≤ Y ^ 13 := pow_le_pow_right₀ (by linarith only [hY2]) (by norm_num)
      have hb : Y ^ 13 ≤ (T ^ ((1 : ℝ) / 96)) ^ 13 :=
        pow_le_pow_left₀ (by linarith only [hY2]) hroot 13
      rw [pow_one] at ha
      calc Y ≤ Y ^ 13 := ha
        _ ≤ (T ^ ((1 : ℝ) / 96)) ^ 13 := hb
        _ = T ^ ((13 : ℝ) / 96) := hpow13
    have hsplit : T ^ ((13 : ℝ) / 96) * T ^ ((1 : ℝ) / 32) = T ^ ((1 : ℝ) / 6) := by
      rw [← Real.rpow_add hT0]
      congr 1
      norm_num
    have h5 : 2 * (D0 * (1 + Real.log T) ^ 2) ≤ 9248 * D0 * T ^ ((1 : ℝ) / 32) := by
      have h6 := mul_le_mul_of_nonneg_left hLsq
        (by linarith only [hD0pos] : (0 : ℝ) ≤ 2 * D0)
      calc 2 * (D0 * (1 + Real.log T) ^ 2)
          = 2 * D0 * (1 + Real.log T) ^ 2 := by ring
        _ ≤ 2 * D0 * (4624 * T ^ ((1 : ℝ) / 32)) := h6
        _ = 9248 * D0 * T ^ ((1 : ℝ) / 32) := by ring
    have h7 : 9248 * D0 * T ^ ((1 : ℝ) / 32) ≤ T ^ ((1 : ℝ) / 6) := by
      have h8 : 9248 * D0 ≤ Y := by
        rw [hYdef]
        nlinarith [hD08, hCF, mul_nonneg (le_of_lt hD0pos) hCF]
      have h9 : 9248 * D0 * T ^ ((1 : ℝ) / 32)
          ≤ T ^ ((13 : ℝ) / 96) * T ^ ((1 : ℝ) / 32) :=
        mul_le_mul_of_nonneg_right (le_trans h8 h13) (Real.rpow_nonneg hT0.le _)
      rw [hsplit] at h9
      exact h9
    rw [hxdef, le_div_iff₀ hDL2pos]
    calc 2 * (D0 * (1 + Real.log T) ^ 2) ≤ 9248 * D0 * T ^ ((1 : ℝ) / 32) := h5
      _ ≤ T ^ ((1 : ℝ) / 6) := h7
  set K : ℕ := ⌊x⌋₊ with hKdef
  have hK1 : 1 ≤ K := Nat.le_floor (by exact_mod_cast (by linarith only [hx2] : (1 : ℝ) ≤ x))
  have hKR0 : (0 : ℝ) < (K : ℝ) := by exact_mod_cast hK1
  have hKne : (K : ℝ) ≠ 0 := ne_of_gt hKR0
  have hKle : (K : ℝ) ≤ x := Nat.floor_le hx0.le
  have hKge : x / 2 ≤ (K : ℝ) := by
    have h1 : x < (K : ℝ) + 1 := Nat.lt_floor_add_one x
    have h2 : (1 : ℝ) ≤ (K : ℝ) := by exact_mod_cast hK1
    linarith only [h1, h2, hx2]
  have hTK0 : (0 : ℝ) < T / K := div_pos hT0 hKR0
  have hxK : x ≤ 2 * (K : ℝ) := by linarith only [hKge]
  have hxval : T ^ ((1 : ℝ) / 6) = x * (D0 * (1 + Real.log T) ^ 2) := by
    rw [hxdef, div_mul_cancel₀ _ (ne_of_gt hDL2pos)]
  -- the key coefficient inequality
  have hkey : 512 * (K : ℝ) ^ 3 * CE ^ 2 * (CF + 1) * (1 + Real.log T) ^ 4
      < Real.sqrt T := by
    have hKx : (K : ℝ) * (D0 * (1 + Real.log T) ^ 2) ≤ T ^ ((1 : ℝ) / 6) := by
      rw [hxval]
      exact mul_le_mul_of_nonneg_right hKle (le_of_lt hDL2pos)
    have hcube : ((K : ℝ) * (D0 * (1 + Real.log T) ^ 2)) ^ 3 ≤ T ^ ((1 : ℝ) / 2) := by
      have h1 : ((K : ℝ) * (D0 * (1 + Real.log T) ^ 2)) ^ 3 ≤ (T ^ ((1 : ℝ) / 6)) ^ 3 :=
        pow_le_pow_left₀ (le_of_lt (mul_pos hKR0 hDL2pos)) hKx 3
      have h2 : (T ^ ((1 : ℝ) / 6)) ^ (3 : ℕ) = T ^ ((1 : ℝ) / 2) := by
        rw [← Real.rpow_natCast (T ^ ((1 : ℝ) / 6)) 3, ← Real.rpow_mul hT0.le]
        congr 1
        norm_num
      calc ((K : ℝ) * (D0 * (1 + Real.log T) ^ 2)) ^ 3
          ≤ (T ^ ((1 : ℝ) / 6)) ^ 3 := h1
        _ = T ^ ((1 : ℝ) / 2) := h2
    have hcoef : 512 * CE ^ 2 * (CF + 1) < D0 ^ 3 * (1 + Real.log T) ^ 2 := by
      have h1 : 512 * CE ^ 2 * (CF + 1) + 8 ≤ D0 := by
        rw [hD0def]
        nlinarith [sq_nonneg CE, hCF]
      have h2 : D0 ≤ D0 ^ 3 := by nlinarith [hD08]
      have h4 : (1 : ℝ) ≤ (1 + Real.log T) ^ 2 := by nlinarith [hL1]
      have h3 : D0 ^ 3 ≤ D0 ^ 3 * (1 + Real.log T) ^ 2 := by
        calc D0 ^ 3 = D0 ^ 3 * 1 := (mul_one _).symm
          _ ≤ D0 ^ 3 * (1 + Real.log T) ^ 2 :=
              mul_le_mul_of_nonneg_left h4 (le_of_lt (pow_pos hD0pos 3))
      linarith only [h1, h2, h3]
    have hmul : 512 * (K : ℝ) ^ 3 * CE ^ 2 * (CF + 1) * (1 + Real.log T) ^ 4
        < (K : ℝ) ^ 3 * (D0 ^ 3 * (1 + Real.log T) ^ 2) * (1 + Real.log T) ^ 4 := by
      have hpos : (0 : ℝ) < (K : ℝ) ^ 3 * (1 + Real.log T) ^ 4 :=
        mul_pos (pow_pos hKR0 3) (pow_pos hL0 4)
      calc 512 * (K : ℝ) ^ 3 * CE ^ 2 * (CF + 1) * (1 + Real.log T) ^ 4
          = (512 * CE ^ 2 * (CF + 1)) * ((K : ℝ) ^ 3 * (1 + Real.log T) ^ 4) := by ring
        _ < (D0 ^ 3 * (1 + Real.log T) ^ 2) * ((K : ℝ) ^ 3 * (1 + Real.log T) ^ 4) :=
            mul_lt_mul_of_pos_right hcoef hpos
        _ = (K : ℝ) ^ 3 * (D0 ^ 3 * (1 + Real.log T) ^ 2) * (1 + Real.log T) ^ 4 := by
            ring
    rw [Real.sqrt_eq_rpow]
    calc 512 * (K : ℝ) ^ 3 * CE ^ 2 * (CF + 1) * (1 + Real.log T) ^ 4
        < (K : ℝ) ^ 3 * (D0 ^ 3 * (1 + Real.log T) ^ 2) * (1 + Real.log T) ^ 4 := hmul
      _ = ((K : ℝ) * (D0 * (1 + Real.log T) ^ 2)) ^ 3 := by ring
      _ ≤ T ^ ((1 : ℝ) / 2) := hcube
  have hgap := gap_of_key hT0 hK1 hkey
  set M4 : ℝ := (CF + 1) * T * (1 + Real.log T) ^ 4 with hM4def
  have hM40 : 0 < M4 := by
    rw [hM4def]
    exact mul_pos (mul_pos (by linarith only [hCF] : (0 : ℝ) < CF + 1) hT0)
      (pow_pos hL0 4)
  have hCdyadic := hC T hTTC
  have hM4dyadic : (∫ τ in T..(2 * T), (hardyZ τ) ^ 4) ≤ M4 := by
    refine le_trans (hF (by linarith)) ?_
    rw [hM4def]
    have h1 : (0 : ℝ) ≤ T * (1 + Real.log T) ^ 4 := by positivity
    nlinarith
  have hEwin : ∀ k : ℕ, k < K →
      |∫ τ in (T + k * (T / K))..(T + ((k + 1 : ℕ) : ℝ) * (T / K)), hardyZ τ|
        ≤ CE * (Real.sqrt T * Real.sqrt (Real.sqrt T)) := by
    intro k hkK
    have hk1K : ((k : ℝ) + 1) ≤ (K : ℝ) := by exact_mod_cast hkK
    refine hE hT16 ?_ ?_ ?_
    · have h0 : (0 : ℝ) ≤ (k : ℝ) * (T / K) := by positivity
      linarith
    · push_cast
      nlinarith [hTK0]
    · push_cast
      have h1 : ((k : ℝ) + 1) * (T / K) ≤ (K : ℝ) * (T / K) :=
        mul_le_mul_of_nonneg_right hk1K hTK0.le
      have h2 : (K : ℝ) * (T / K) = T := by field_simp
      linarith
  obtain ⟨S, hSzero, hScount⟩ :=
    exists_heavyFinset_sq hK1 hT0 hM40 hCdyadic hM4dyadic hEwin hgap
  obtain ⟨τS, hτSmem, hτScard⟩ := exists_distinct_ordinates hT0 hK1 S hSzero
  refine ⟨τS, hτSmem, ?_⟩
  -- the counting arithmetic
  have hcard : (K : ℝ) ≤ 64 * (S.card : ℝ) * (CF + 1) * (1 + Real.log T) ^ 4 := by
    have h1 : (T / 8) ^ 2 * (K : ℝ) ≤ (S.card : ℝ) * ((T / K) * M4) * (K : ℝ) :=
      mul_le_mul_of_nonneg_right hScount hKR0.le
    have h2 : (S.card : ℝ) * ((T / K) * M4) * (K : ℝ) = (S.card : ℝ) * (T * M4) := by
      field_simp
    have h3 : (T / 8) ^ 2 * (K : ℝ) = T ^ 2 * ((K : ℝ) / 64) := by ring
    rw [h2, h3] at h1
    have h4 : (S.card : ℝ) * (T * M4)
        = T ^ 2 * ((S.card : ℝ) * (CF + 1) * (1 + Real.log T) ^ 4) := by
      rw [hM4def]
      ring
    rw [h4] at h1
    have h5 := le_of_mul_le_mul_left h1 (pow_pos hT0 2)
    linarith only [h5]
  have himg1 : (1 : ℝ) ≤ (τS.card : ℝ) := by
    by_contra h0
    have h0lt : (τS.card : ℝ) < 1 := not_le.mp h0
    have h0' : τS.card = 0 := by
      by_contra h1
      have h2 : 1 ≤ τS.card := Nat.one_le_iff_ne_zero.mpr h1
      have h3 : (1 : ℝ) ≤ (τS.card : ℝ) := by exact_mod_cast h2
      linarith only [h0lt, h3]
    have h1 : (S.card : ℝ) ≤ 2 * (τS.card : ℝ) + 1 := by exact_mod_cast hτScard
    have h1' : ((τS.card : ℕ) : ℝ) = 0 := by exact_mod_cast h0'
    rw [h1'] at h1
    have hS1 : (S.card : ℝ) ≤ 1 := by linarith only [h1]
    have hK64 : (K : ℝ) ≤ 64 * (CF + 1) * (1 + Real.log T) ^ 4 := by
      have hpos : (0 : ℝ) ≤ 64 * ((CF + 1) * (1 + Real.log T) ^ 4) :=
        mul_nonneg (by norm_num)
          (mul_nonneg (by linarith only [hCF]) (le_of_lt (pow_pos hL0 4)))
      have h4 := mul_le_mul_of_nonneg_right hS1 hpos
      calc (K : ℝ) ≤ 64 * (S.card : ℝ) * (CF + 1) * (1 + Real.log T) ^ 4 := hcard
        _ = (S.card : ℝ) * (64 * ((CF + 1) * (1 + Real.log T) ^ 4)) := by ring
        _ ≤ 1 * (64 * ((CF + 1) * (1 + Real.log T) ^ 4)) := h4
        _ = 64 * (CF + 1) * (1 + Real.log T) ^ 4 := by ring
    have hxb : x ≤ 128 * (CF + 1) * (1 + Real.log T) ^ 4 := by
      calc x ≤ 2 * (K : ℝ) := hxK
        _ ≤ 2 * (64 * (CF + 1) * (1 + Real.log T) ^ 4) := by linarith only [hK64]
        _ = 128 * (CF + 1) * (1 + Real.log T) ^ 4 := by ring
    have hT6 : T ^ ((1 : ℝ) / 6) ≤ 128 * D0 * (CF + 1) * (1 + Real.log T) ^ 6 := by
      have h2 := mul_le_mul_of_nonneg_right hxb (le_of_lt hDL2pos)
      calc T ^ ((1 : ℝ) / 6) = x * (D0 * (1 + Real.log T) ^ 2) := hxval
        _ ≤ 128 * (CF + 1) * (1 + Real.log T) ^ 4 * (D0 * (1 + Real.log T) ^ 2) := h2
        _ = 128 * D0 * (CF + 1) * (1 + Real.log T) ^ 6 := by ring
    have hL6 : (1 + Real.log T) ^ 6 ≤ 4624 ^ 3 * T ^ ((3 : ℝ) / 32) := by
      have ha : ((1 + Real.log T) ^ 2) ^ 3 ≤ (4624 * T ^ ((1 : ℝ) / 32)) ^ 3 :=
        pow_le_pow_left₀ (le_of_lt (pow_pos hL0 2)) hLsq 3
      have hb : ((1 + Real.log T) ^ 2) ^ 3 = (1 + Real.log T) ^ 6 := by ring
      have hc : (4624 * T ^ ((1 : ℝ) / 32)) ^ 3
          = 4624 ^ 3 * (T ^ ((1 : ℝ) / 32)) ^ 3 := by ring
      have hd : (T ^ ((1 : ℝ) / 32)) ^ (3 : ℕ) = T ^ ((3 : ℝ) / 32) := by
        rw [← Real.rpow_natCast (T ^ ((1 : ℝ) / 32)) 3, ← Real.rpow_mul hT0.le]
        congr 1
        norm_num
      rw [hb, hc, hd] at ha
      exact ha
    have hcomb : T ^ ((1 : ℝ) / 6)
        ≤ (128 * D0 * (CF + 1) * 4624 ^ 3) * T ^ ((3 : ℝ) / 32) := by
      have hpos : (0 : ℝ) ≤ 128 * D0 * (CF + 1) :=
        mul_nonneg (mul_nonneg (by norm_num) (le_of_lt hD0pos))
          (by linarith only [hCF])
      calc T ^ ((1 : ℝ) / 6) ≤ 128 * D0 * (CF + 1) * (1 + Real.log T) ^ 6 := hT6
        _ ≤ 128 * D0 * (CF + 1) * (4624 ^ 3 * T ^ ((3 : ℝ) / 32)) :=
            mul_le_mul_of_nonneg_left hL6 hpos
        _ = (128 * D0 * (CF + 1) * 4624 ^ 3) * T ^ ((3 : ℝ) / 32) := by ring
    have hsplit2 : T ^ ((7 : ℝ) / 96) * T ^ ((3 : ℝ) / 32) = T ^ ((1 : ℝ) / 6) := by
      rw [← Real.rpow_add hT0]
      congr 1
      norm_num
    have h7 : T ^ ((7 : ℝ) / 96) ≤ 128 * D0 * (CF + 1) * 4624 ^ 3 := by
      have h8 := hcomb
      rw [← hsplit2] at h8
      exact le_of_mul_le_mul_right h8 (Real.rpow_pos_of_pos hT0 _)
    have h9 : Y ≤ T ^ ((7 : ℝ) / 96) := by
      have ha : Y ^ 1 ≤ Y ^ 7 := pow_le_pow_right₀ (by linarith only [hY2]) (by norm_num)
      have hb : Y ^ 7 ≤ (T ^ ((1 : ℝ) / 96)) ^ 7 :=
        pow_le_pow_left₀ (by linarith only [hY2]) hroot 7
      rw [pow_one] at ha
      calc Y ≤ Y ^ 7 := ha
        _ ≤ (T ^ ((1 : ℝ) / 96)) ^ 7 := hb
        _ = T ^ ((7 : ℝ) / 96) := hpow7
    have h10 : 128 * D0 * (CF + 1) * 4624 ^ 3 + 2 ≤ Y := by
      rw [hYdef]
      linarith only [hD08,
        mul_nonneg (mul_nonneg (le_of_lt hD0pos) hCF)
          (by norm_num : (0 : ℝ) ≤ 4624 ^ 3),
        mul_nonneg (le_of_lt hD0pos) (by norm_num : (0 : ℝ) ≤ 4624 ^ 3)]
    linarith only [h7, h9, h10]
  have hcard3 : (S.card : ℝ) ≤ 3 * (τS.card : ℝ) := by
    have h1 : (S.card : ℝ) ≤ 2 * (τS.card : ℝ) + 1 := by exact_mod_cast hτScard
    linarith only [h1, himg1]
  have hxbound : x ≤ 384 * (τS.card : ℝ) * (CF + 1) * (1 + Real.log T) ^ 4 := by
    have hpos : (0 : ℝ) ≤ 64 * ((CF + 1) * (1 + Real.log T) ^ 4) :=
      mul_nonneg (by norm_num)
        (mul_nonneg (by linarith only [hCF]) (le_of_lt (pow_pos hL0 4)))
    have h3 := mul_le_mul_of_nonneg_right hcard3 hpos
    have h2 : 64 * (S.card : ℝ) * (CF + 1) * (1 + Real.log T) ^ 4
        ≤ 64 * (3 * (τS.card : ℝ)) * (CF + 1) * (1 + Real.log T) ^ 4 := by
      calc 64 * (S.card : ℝ) * (CF + 1) * (1 + Real.log T) ^ 4
          = (S.card : ℝ) * (64 * ((CF + 1) * (1 + Real.log T) ^ 4)) := by ring
        _ ≤ 3 * (τS.card : ℝ) * (64 * ((CF + 1) * (1 + Real.log T) ^ 4)) := h3
        _ = 64 * (3 * (τS.card : ℝ)) * (CF + 1) * (1 + Real.log T) ^ 4 := by ring
    calc x ≤ 2 * (K : ℝ) := hxK
      _ ≤ 2 * (64 * (S.card : ℝ) * (CF + 1) * (1 + Real.log T) ^ 4) := by
          linarith only [hcard]
      _ ≤ 2 * (64 * (3 * (τS.card : ℝ)) * (CF + 1) * (1 + Real.log T) ^ 4) := by
          linarith only [h2]
      _ = 384 * (τS.card : ℝ) * (CF + 1) * (1 + Real.log T) ^ 4 := by ring
  have hfinal2 : T ^ ((1 : ℝ) / 6)
      ≤ 384 * D0 * (CF + 1) * (τS.card : ℝ) * (1 + Real.log T) ^ 6 := by
    have h2 := mul_le_mul_of_nonneg_right hxbound (le_of_lt hDL2pos)
    calc T ^ ((1 : ℝ) / 6) = x * (D0 * (1 + Real.log T) ^ 2) := hxval
      _ ≤ 384 * (τS.card : ℝ) * (CF + 1) * (1 + Real.log T) ^ 4
          * (D0 * (1 + Real.log T) ^ 2) := h2
      _ = 384 * D0 * (CF + 1) * (τS.card : ℝ) * (1 + Real.log T) ^ 6 := by ring
  rw [div_le_iff₀ (pow_pos hL0 6), div_mul_eq_mul_div, one_mul,
    div_le_iff₀ (by nlinarith [hD08, hCF, mul_nonneg (le_of_lt hD0pos) hCF] :
      (0 : ℝ) < 384 * D0 * (CF + 1) + 1)]
  have hcl : (0 : ℝ) ≤ (τS.card : ℝ) * (1 + Real.log T) ^ 6 :=
    mul_nonneg (Nat.cast_nonneg _) (le_of_lt (pow_pos hL0 6))
  calc T ^ ((1 : ℝ) / 6)
      ≤ 384 * D0 * (CF + 1) * (τS.card : ℝ) * (1 + Real.log T) ^ 6 := hfinal2
    _ ≤ (τS.card : ℝ) * (1 + Real.log T) ^ 6 * (384 * D0 * (CF + 1) + 1) := by
        linarith only [hcl]

/-- **Sixth-root census difference.**  Unconditionally, the number of critical-line zeros of
`xi` with ordinate in `(T, 2T]`, counted with multiplicity, is at least
`c · T^{1/6} / (1 + log T)⁶` for all large `T`. -/
theorem exists_sixthRoot_le_xiPosCriticalZeroCount_sub :
    ∃ c : ℝ, 0 < c ∧ ∃ T₁ : ℝ, 1 ≤ T₁ ∧ ∀ T : ℝ, T₁ ≤ T →
      c * T ^ ((1 : ℝ) / 6) / (1 + Real.log T) ^ 6
        ≤ (xiPosCriticalZeroCount (2 * T) : ℝ) - (xiPosCriticalZeroCount T : ℝ) := by
  obtain ⟨c, hc, T₁, hT₁, h⟩ := exists_many_distinct_line_zeros_dyadic_sixth
  refine ⟨c, hc, T₁, hT₁, fun T hT => ?_⟩
  obtain ⟨τS, hmemS, hcard⟩ := h T hT
  have hT0 : (0 : ℝ) < T := by linarith
  have hinj := xiPosCriticalZeroCount_add_card_le hT0 τS hmemS
  have hcast : (xiPosCriticalZeroCount T : ℝ) + (τS.card : ℝ)
      ≤ (xiPosCriticalZeroCount (2 * T) : ℝ) := by exact_mod_cast hinj
  linarith only [hcard, hcast]

set_option maxHeartbeats 800000 in
/-- **A sixth-root lower bound for the critical-line census.**  Unconditionally, the number
of critical-line zeros of `xi` with ordinate in `(0, T]`, counted with multiplicity, is at
least `c · T^{1/6} / (1 + log T)⁶` for all large `T` — the ceiling of the window-pigeonhole
route with the trivial `T^{3/4}` window mean. -/
theorem exists_sixthRoot_le_xiPosCriticalZeroCount :
    ∃ c : ℝ, 0 < c ∧ ∃ T₁ : ℝ, 1 ≤ T₁ ∧ ∀ T : ℝ, T₁ ≤ T →
      c * T ^ ((1 : ℝ) / 6) / (1 + Real.log T) ^ 6 ≤ (xiPosCriticalZeroCount T : ℝ) := by
  obtain ⟨c, hc, T₁, hT₁, h⟩ := exists_sixthRoot_le_xiPosCriticalZeroCount_sub
  refine ⟨c / 2, by positivity, max (2 * T₁) 2, ?_, fun T hT => ?_⟩
  · have h1 := le_max_right (2 * T₁) 2
    linarith
  have hT2 : (2 : ℝ) ≤ T := le_trans (le_max_right _ _) hT
  have hT20 : (0 : ℝ) < T / 2 := by linarith
  have hT0 : (0 : ℝ) < T := by linarith
  have hhalf : T₁ ≤ T / 2 := by
    have h1 := le_trans (le_max_left (2 * T₁) 2) hT
    linarith
  have hspec := h (T / 2) hhalf
  rw [show 2 * (T / 2) = T by ring] at hspec
  have hl1 : (0 : ℝ) ≤ Real.log (T / 2) := Real.log_nonneg (by linarith)
  have hl2 : Real.log (T / 2) ≤ Real.log T := Real.log_le_log hT20 (by linarith)
  have hp1 : (0 : ℝ) < 1 + Real.log (T / 2) := by linarith
  have hp2 : (0 : ℝ) < 1 + Real.log T := by linarith
  have hlogc : (1 + Real.log (T / 2)) ^ 6 ≤ (1 + Real.log T) ^ 6 :=
    pow_le_pow_left₀ hp1.le (by linarith) 6
  have hchain : T ^ ((1 : ℝ) / 6) ≤ 2 * (T / 2) ^ ((1 : ℝ) / 6) := by
    have h1 : T ≤ 64 * (T / 2) := by linarith
    have h2 : T ^ ((1 : ℝ) / 6) ≤ ((64 : ℝ) * (T / 2)) ^ ((1 : ℝ) / 6) :=
      Real.rpow_le_rpow hT0.le h1 (by norm_num)
    have h3 : ((64 : ℝ) * (T / 2)) ^ ((1 : ℝ) / 6)
        = (64 : ℝ) ^ ((1 : ℝ) / 6) * (T / 2) ^ ((1 : ℝ) / 6) :=
      Real.mul_rpow (by norm_num) hT20.le
    have h4 : (64 : ℝ) ^ ((1 : ℝ) / 6) = 2 := by
      rw [show (64 : ℝ) = 2 ^ (6 : ℕ) by norm_num, ← Real.rpow_natCast 2 6,
        ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2),
        show ((6 : ℕ) : ℝ) * ((1 : ℝ) / 6) = 1 by norm_num, Real.rpow_one]
    rw [h3, h4] at h2
    exact h2
  have hfinal : c / 2 * T ^ ((1 : ℝ) / 6) / (1 + Real.log T) ^ 6
      ≤ c * (T / 2) ^ ((1 : ℝ) / 6) / (1 + Real.log (T / 2)) ^ 6 := by
    have hq1 : (0 : ℝ) < (1 + Real.log T) ^ 6 := pow_pos hp2 6
    have hq2 : (0 : ℝ) < (1 + Real.log (T / 2)) ^ 6 := pow_pos hp1 6
    rw [div_le_div_iff₀ hq1 hq2]
    have hprod : T ^ ((1 : ℝ) / 6) * (1 + Real.log (T / 2)) ^ 6
        ≤ (2 * (T / 2) ^ ((1 : ℝ) / 6)) * (1 + Real.log T) ^ 6 :=
      mul_le_mul hchain hlogc hq2.le (by positivity)
    have hscale := mul_le_mul_of_nonneg_left hprod
      (by positivity : (0 : ℝ) ≤ c / 2)
    calc c / 2 * T ^ ((1 : ℝ) / 6) * (1 + Real.log (T / 2)) ^ 6
        = c / 2 * (T ^ ((1 : ℝ) / 6) * (1 + Real.log (T / 2)) ^ 6) := by ring
      _ ≤ c / 2 * ((2 * (T / 2) ^ ((1 : ℝ) / 6)) * (1 + Real.log T) ^ 6) := hscale
      _ = c * (T / 2) ^ ((1 : ℝ) / 6) * (1 + Real.log T) ^ 6 := by ring
  have hcnn : (0 : ℝ) ≤ (xiPosCriticalZeroCount (T / 2) : ℝ) := Nat.cast_nonneg _
  calc c / 2 * T ^ ((1 : ℝ) / 6) / (1 + Real.log T) ^ 6
      ≤ c * (T / 2) ^ ((1 : ℝ) / 6) / (1 + Real.log (T / 2)) ^ 6 := hfinal
    _ ≤ (xiPosCriticalZeroCount T : ℝ) - (xiPosCriticalZeroCount (T / 2) : ℝ) := hspec
    _ ≤ (xiPosCriticalZeroCount T : ℝ) := by linarith only [hcnn]

end

end RHTower
