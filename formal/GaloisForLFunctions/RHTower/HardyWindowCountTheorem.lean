import GaloisForLFunctions.RHTower.HardyZWindowMean
import GaloisForLFunctions.RHTower.HardyDyadicWindowTheorem

/-!
# A polynomial census of critical-line zeros

Partition the dyadic block `[T, 2T]` into `K = ⌊T^{1/8}⌋` windows.  The dyadic second moment
puts total mass at least `T/4` into the windows; light windows — mass below `T/(8K)` — carry
at most `T/8` in total; and each window's mass is at most `√(H·F)` by Cauchy–Schwarz against
the dyadic fourth moment.  So polynomially many windows are heavy.  On a heavy window the
subwindow mean bound `O(T^{3/4})` loses to the mass cubed, and the fourth-moment sign-change
detector produces a critical-line zero inside the window.  Distinct windows give distinct
ordinates up to a factor two (windows can share an endpoint), and each new ordinate adds at
least one to the critical-line census.  Hence the census `N₀` grows at least like
`T^{1/16}/(1+log T)²` — a polynomial strengthening of the logarithmic Hardy census,
unconditional.
-/

open Set MeasureTheory Complex Finset

namespace RHTower

noncomputable section

/-! ## Window partition of the dyadic second moment -/

private theorem window_partition (T : ℝ) (K : ℕ) :
    ∑ k ∈ range K, ∫ τ in (T + k * (T / K))..(T + ((k : ℕ) + 1 : ℕ) * (T / K)),
        (hardyZ τ) ^ 2
      = ∫ τ in (T + ((0 : ℕ) : ℝ) * (T / K))..(T + (K : ℝ) * (T / K)), (hardyZ τ) ^ 2 := by
  exact intervalIntegral.sum_integral_adjacent_intervals
    (f := fun τ => (hardyZ τ) ^ 2) (μ := volume)
    (a := fun k : ℕ => T + k * (T / K)) (n := K)
    (fun k _ => ((continuous_hardyZ.pow 2).intervalIntegrable _ _))

/-! ## Iterated square roots -/

private theorem sqrt_sq_chain {r : ℝ} (hr : 0 ≤ r) :
    Real.sqrt (Real.sqrt (Real.sqrt (Real.sqrt (r ^ 16)))) = r := by
  have h1 : (r ^ 16 : ℝ) = (r ^ 8) ^ 2 := by ring
  have h2 : (r ^ 8 : ℝ) = (r ^ 4) ^ 2 := by ring
  have h3 : (r ^ 4 : ℝ) = (r ^ 2) ^ 2 := by ring
  rw [h1, Real.sqrt_sq (by positivity), h2, Real.sqrt_sq (by positivity), h3,
    Real.sqrt_sq (by positivity), Real.sqrt_sq hr]

/-- `(1 + log T)⁴ ≤ 21381376 · T^{1/16}` for `T ≥ 1`. -/
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

/-! ## Many distinct critical-line zeros in a dyadic block -/

set_option maxHeartbeats 12800000 in
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
  set D : ℝ := 512 * 21381376 * (CE ^ 2 + 1) * (CF + 1)
      + 74000 ^ 2 * (CF + 1) + 21381376 + 4 with hDdef
  have hD4 : (4 : ℝ) ≤ D := by
    rw [hDdef]
    nlinarith [sq_nonneg CE, hCF]
  refine ⟨1 / (48 * (Real.sqrt (CF + 1) + 1)), by positivity,
    max (max TC 16) ((D + 1) ^ 16), ?_, fun T hT => ?_⟩
  · refine le_trans ?_ (le_max_right _ _)
    have : (1 : ℝ) ≤ D + 1 := by linarith
    calc (1 : ℝ) = 1 ^ 16 := by norm_num
      _ ≤ (D + 1) ^ 16 := pow_le_pow_left₀ (by norm_num) this 16
  have hT16 : (16 : ℝ) ≤ T := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hT
  have hTTC : TC ≤ T := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hT
  have hTD : (D + 1) ^ 16 ≤ T := le_trans (le_max_right _ _) hT
  have hT0 : (0 : ℝ) < T := by linarith
  have hT1 : (1 : ℝ) ≤ T := by linarith
  -- iterated square roots of the height
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
  have hs2pos : (0 : ℝ) < s2 := by nlinarith [hs3sq]
  have hs1pos : (0 : ℝ) < s1 := by nlinarith [hs2sq]
  have hs32 : (2 : ℝ) ≤ s3 := by nlinarith [hs4sq, hs4D, hD4]
  -- the window count
  set K : ℕ := ⌊s3⌋₊ with hKdef
  have hKle : (K : ℝ) ≤ s3 := Nat.floor_le hs3pos.le
  have hK1 : 1 ≤ K := Nat.le_floor (by exact_mod_cast (by linarith : (1 : ℝ) ≤ s3))
  have hK0 : K ≠ 0 := Nat.one_le_iff_ne_zero.mp hK1
  have hKR0 : (0 : ℝ) < (K : ℝ) := by exact_mod_cast hK1
  have hKge : s3 / 2 ≤ (K : ℝ) := by
    have h1 : s3 < (K : ℝ) + 1 := Nat.lt_floor_add_one s3
    have h2 : (1 : ℝ) ≤ (K : ℝ) := by exact_mod_cast hK1
    linarith
  set H : ℝ := T / K with hHdef
  have hH0 : (0 : ℝ) < H := by positivity
  -- windows and masses
  set a : ℕ → ℝ := fun k => T + k * (T / K) with hadef
  have hTK0 : (0 : ℝ) < T / K := by positivity
  have ha_le : ∀ k : ℕ, a k ≤ a (k + 1) := by
    intro k
    rw [hadef]
    dsimp only
    push_cast
    nlinarith [hTK0]
  have ha_ge : ∀ k : ℕ, T ≤ a k := by
    intro k
    rw [hadef]
    dsimp only
    have h0 : (0 : ℝ) ≤ (k : ℝ) * (T / K) := by positivity
    linarith
  have ha_K : a K = 2 * T := by
    rw [hadef]
    dsimp only
    field_simp
    ring
  have ha_mono : ∀ j k : ℕ, j ≤ k → a j ≤ a k := by
    intro j k hjk
    rw [hadef]
    dsimp only
    have : (j : ℝ) ≤ (k : ℝ) := by exact_mod_cast hjk
    nlinarith [hT0, hKR0]
  have ha_le2T : ∀ k : ℕ, k ≤ K → a k ≤ 2 * T := by
    intro k hk
    rw [← ha_K]
    exact ha_mono k K hk
  set m : ℕ → ℝ := fun k => ∫ τ in (a k)..(a (k + 1)), (hardyZ τ) ^ 2 with hmdef
  have hm0 : ∀ k : ℕ, 0 ≤ m k := by
    intro k
    rw [hmdef]
    exact intervalIntegral.integral_nonneg (ha_le k) (fun u _ => sq_nonneg _)
  -- the partition of the dyadic second moment
  have hpart : ∑ k ∈ range K, m k = ∫ τ in T..(2 * T), (hardyZ τ) ^ 2 := by
    have h := window_partition T K
    have hz : T + ((0 : ℕ) : ℝ) * (T / K) = T := by push_cast; ring
    have hK' : T + (K : ℝ) * (T / K) = 2 * T := by field_simp; ring
    rw [hz, hK'] at h
    simp only [hmdef, hadef]
    exact h
  have hCT : T / 4 ≤ ∫ τ in T..(2 * T), (hardyZ τ) ^ 2 := hC T hTTC
  -- the fourth-moment budget
  set F4 : ℝ := (CF + 1) * T * (1 + Real.log T) ^ 4 with hF4def
  have hlog0 : 0 ≤ Real.log T := Real.log_nonneg hT1
  have hF40 : 0 < F4 := by
    rw [hF4def]
    have : (0 : ℝ) < 1 + Real.log T := by linarith
    positivity
  have hF4dyadic : (∫ t in T..(2 * T), (hardyZ t) ^ 4) ≤ F4 := by
    refine le_trans (hF (by linarith)) ?_
    rw [hF4def]
    have h1 : (0 : ℝ) ≤ T * (1 + Real.log T) ^ 4 := by positivity
    nlinarith
  have hF4w : ∀ k : ℕ, k < K → (∫ τ in (a k)..(a (k + 1)), (hardyZ τ) ^ 4) ≤ F4 := by
    intro k hk
    refine le_trans (intervalIntegral.integral_mono_interval (ha_ge k) (ha_le k)
      (ha_le2T (k + 1) hk) (Filter.Eventually.of_forall fun u => sq_nonneg ((hardyZ u) ^ 2)
        |>.trans (le_of_eq (by ring)))
      ((continuous_hardyZ.pow 4).intervalIntegrable _ _)) hF4dyadic
  -- the heavy windows
  set Θ : ℝ := T / (8 * K) with hΘdef
  have hΘ0 : (0 : ℝ) < Θ := by positivity
  set heavy : Finset ℕ := (range K).filter (fun k => Θ ≤ m k) with hheavydef
  have hlightsum : ∑ k ∈ (range K).filter (fun k => ¬ Θ ≤ m k), m k ≤ T / 8 := by
    have h1 : ∀ k ∈ (range K).filter (fun k => ¬ Θ ≤ m k), m k ≤ Θ := by
      intro k hk
      have := (Finset.mem_filter.mp hk).2
      linarith [lt_of_not_ge this]
    have h2 := Finset.sum_le_card_nsmul _ _ _ h1
    have h3 : (((range K).filter (fun k => ¬ Θ ≤ m k)).card : ℝ) ≤ (K : ℝ) := by
      exact_mod_cast le_trans (Finset.card_filter_le _ _) (le_of_eq (Finset.card_range K))
    rw [nsmul_eq_mul] at h2
    have h4 : (((range K).filter (fun k => ¬ Θ ≤ m k)).card : ℝ) * Θ ≤ (K : ℝ) * Θ :=
      mul_le_mul_of_nonneg_right h3 hΘ0.le
    have h5 : (K : ℝ) * Θ = T / 8 := by
      rw [hΘdef]
      field_simp
    linarith
  have hheavysum : T / 8 ≤ ∑ k ∈ heavy, m k := by
    have h := Finset.sum_filter_add_sum_filter_not (range K) (fun k => Θ ≤ m k) m
    rw [hheavydef]
    have := hpart
    linarith [hlightsum, hCT]
  -- the mass cap per window
  have hcap : ∀ k ∈ heavy, m k ≤ Real.sqrt (CF + 1) * T * (1 + Real.log T) ^ 2
      / Real.sqrt (K : ℝ) := by
    intro k hk
    have hkK : k < K := Finset.mem_range.mp (Finset.mem_filter.mp hk).1
    -- Cauchy–Schwarz on the window
    have hsq : (m k) ^ 2 ≤ H * ∫ τ in (a k)..(a (k + 1)), (hardyZ τ) ^ 4 := by
      have hlen : a (k + 1) - a k = H := by
        rw [hadef, hHdef]
        dsimp only
        push_cast
        ring
      have hle := ha_le k
      have hf : MeasureTheory.IntegrableOn (fun τ => (hardyZ τ) ^ 2)
          (Set.Ioc (a k) (a (k + 1))) MeasureTheory.volume :=
        (continuous_hardyZ.pow 2).integrableOn_Ioc
      have hf2 : MeasureTheory.IntegrableOn (fun τ => ((hardyZ τ) ^ 2) ^ 2)
          (Set.Ioc (a k) (a (k + 1))) MeasureTheory.volume := by
        have := (continuous_hardyZ.pow 4).integrableOn_Ioc
          (a := a k) (b := a (k + 1))
        apply this.congr_fun _ measurableSet_Ioc
        intro τ _
        ring
      have h2 := GaloisForLFunctions.HTGeometry.sq_integral_le_length_mul hle hf hf2
      have hIoc1 : (∫ τ in (a k)..(a (k + 1)), (hardyZ τ) ^ 2)
          = ∫ τ in Set.Ioc (a k) (a (k + 1)), (hardyZ τ) ^ 2 :=
        intervalIntegral.integral_of_le hle
      have hIoc2 : (∫ τ in (a k)..(a (k + 1)), (hardyZ τ) ^ 4)
          = ∫ τ in Set.Ioc (a k) (a (k + 1)), (hardyZ τ) ^ 4 :=
        intervalIntegral.integral_of_le hle
      have hcongr : (∫ τ in Set.Ioc (a k) (a (k + 1)), ((hardyZ τ) ^ 2) ^ 2)
          = ∫ τ in Set.Ioc (a k) (a (k + 1)), (hardyZ τ) ^ 4 := by
        apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioc
        intro τ _
        ring
      rw [hcongr, hlen] at h2
      simp only [hmdef]
      rw [hIoc1, hIoc2]
      linarith [h2]
    have h4w := hF4w k hkK
    have hHF : (m k) ^ 2 ≤ H * F4 :=
      le_trans hsq (mul_le_mul_of_nonneg_left h4w hH0.le)
    have hval : H * F4 = (Real.sqrt (CF + 1) * T * (1 + Real.log T) ^ 2
        / Real.sqrt (K : ℝ)) ^ 2 := by
      rw [hHdef, hF4def]
      rw [div_pow, mul_pow, mul_pow, Real.sq_sqrt (by linarith : (0 : ℝ) ≤ CF + 1),
        Real.sq_sqrt hKR0.le]
      have h1 : ((1 + Real.log T) ^ 2) ^ 2 = (1 + Real.log T) ^ 4 := by ring
      rw [h1]
      field_simp
    have hrhs0 : 0 ≤ Real.sqrt (CF + 1) * T * (1 + Real.log T) ^ 2
        / Real.sqrt (K : ℝ) := by positivity
    nlinarith [hm0 k, hHF, hval ▸ hHF]
  have hheavymem : ∀ k ∈ heavy, k < K ∧ Θ ≤ m k := fun k hk =>
    ⟨Finset.mem_range.mp (Finset.mem_filter.mp hk).1, (Finset.mem_filter.mp hk).2⟩
  clear_value s1 s2 s3 s4 K Θ H F4 a m heavy
  -- polynomially many heavy windows
  have hcount : s4 ≤ 16 * (heavy.card : ℝ) * Real.sqrt (CF + 1) * (1 + Real.log T) ^ 2 := by
    have h1 := Finset.sum_le_card_nsmul heavy m _ hcap
    rw [nsmul_eq_mul] at h1
    have h2 : T / 8 ≤ (heavy.card : ℝ) *
        (Real.sqrt (CF + 1) * T * (1 + Real.log T) ^ 2 / Real.sqrt (K : ℝ)) :=
      le_trans hheavysum h1
    have hsK0 : (0 : ℝ) < Real.sqrt (K : ℝ) := Real.sqrt_pos.mpr hKR0
    have h3 : (T / 8) * Real.sqrt (K : ℝ)
        ≤ (heavy.card : ℝ) * (Real.sqrt (CF + 1) * T * (1 + Real.log T) ^ 2) := by
      have := mul_le_mul_of_nonneg_right h2 hsK0.le
      rw [div_mul_eq_mul_div, mul_div_assoc] at this
      calc (T / 8) * Real.sqrt (K : ℝ)
          ≤ (heavy.card : ℝ) * (Real.sqrt (CF + 1) * T * (1 + Real.log T) ^ 2
              * Real.sqrt (K : ℝ) / Real.sqrt (K : ℝ)) := by
            have h5 : Real.sqrt (CF + 1) * T * (1 + Real.log T) ^ 2 / Real.sqrt (K : ℝ)
                * Real.sqrt (K : ℝ)
                = Real.sqrt (CF + 1) * T * (1 + Real.log T) ^ 2
                  * Real.sqrt (K : ℝ) / Real.sqrt (K : ℝ) := by ring
            calc (T / 8) * Real.sqrt (K : ℝ)
                ≤ (heavy.card : ℝ) *
                    (Real.sqrt (CF + 1) * T * (1 + Real.log T) ^ 2 / Real.sqrt (K : ℝ))
                    * Real.sqrt (K : ℝ) :=
                  mul_le_mul_of_nonneg_right h2 hsK0.le
              _ = (heavy.card : ℝ) * (Real.sqrt (CF + 1) * T * (1 + Real.log T) ^ 2
                    * Real.sqrt (K : ℝ) / Real.sqrt (K : ℝ)) := by ring
        _ = (heavy.card : ℝ) * (Real.sqrt (CF + 1) * T * (1 + Real.log T) ^ 2) := by
            rw [mul_div_assoc, div_self (ne_of_gt hsK0), mul_one]
    -- `√K ≥ s4/2`
    have hs4K : s4 / 2 ≤ Real.sqrt (K : ℝ) := by
      have h4 : (s4 / 2) ^ 2 ≤ (K : ℝ) := by
        have : (s4 / 2) ^ 2 = s3 / 4 := by rw [← hs4sq]; ring
        rw [this]
        linarith [hKge]
      have := Real.sqrt_le_sqrt h4
      rwa [Real.sqrt_sq (by positivity)] at this
    have h6 : (T / 8) * (s4 / 2) ≤ (T / 8) * Real.sqrt (K : ℝ) :=
      mul_le_mul_of_nonneg_left hs4K (by positivity)
    have h7 : (T / 8) * (s4 / 2)
        ≤ (heavy.card : ℝ) * (Real.sqrt (CF + 1) * T * (1 + Real.log T) ^ 2) := by
      linarith
    nlinarith [hT0, h7]
  -- every heavy window contains a critical-line zero
  have hzero : ∀ k ∈ heavy, ∃ τ, ((a k ≤ τ ∧ τ ≤ a (k + 1)) ∧
      riemannZeta (linePt τ) = 0) := by
    intro k hk
    have hkK : k < K := (hheavymem k hk).1
    have hΘm : Θ ≤ m k := (hheavymem k hk).2
    have hΘm' : Θ ≤ ∫ τ in (a k)..(a (k + 1)), (hardyZ τ) ^ 2 := by
      simpa only [hmdef] using hΘm
    -- the first-moment gap on the window
    have hmean := hE hT16 (ha_ge k) (ha_le k) (ha_le2T (k + 1) hkK)
    have hmeansq : (∫ τ in (a k)..(a (k + 1)), hardyZ τ) ^ 2 ≤ CE ^ 2 * (T * s1) := by
      have hM := abs_le.mp hmean
      have h1 := sq_le_sq' hM.1 hM.2
      have h2 : (CE * (Real.sqrt T * Real.sqrt (Real.sqrt T))) ^ 2
          = CE ^ 2 * (T * s1) := by
        rw [mul_pow, mul_pow, Real.sq_sqrt hT0.le]
        rw [← hs1def, ← hs2def, Real.sq_sqrt hs1pos.le]
      linarith [h2 ▸ h1]
    have hgap : (∫ τ in (a k)..(a (k + 1)), hardyZ τ) ^ 2 * F4 < Θ ^ 3 := by
      -- `Θ³ = T³/(512 K³)`, and `512 K³ CE² (CF+1) (1+log T)⁴ < s1`
      have hΘcube : Θ ^ 3 = T ^ 3 / (512 * (K : ℝ) ^ 3) := by
        rw [hΘdef]
        field_simp
        ring
      have hK3 : (K : ℝ) ^ 3 ≤ s3 ^ 3 := pow_le_pow_left₀ hKR0.le hKle 3
      have hs3s1 : s3 ^ 4 = s1 := by
        rw [show s3 ^ 4 = (s3 ^ 2) ^ 2 by ring, hs3sq, hs2sq]
      have hlog4 := one_add_log_pow_four_le_sixteenth hT1
      have hkey : 512 * (K : ℝ) ^ 3 * CE ^ 2 * (CF + 1) * (1 + Real.log T) ^ 4 < s1 := by
        have h1 : 512 * (K : ℝ) ^ 3 * CE ^ 2 * (CF + 1) * (1 + Real.log T) ^ 4
            ≤ 512 * s3 ^ 3 * CE ^ 2 * (CF + 1) * (21381376 * s4) := by
          have hb1 : (0 : ℝ) ≤ 512 * CE ^ 2 * (CF + 1) := by positivity
          have hb2 : (0 : ℝ) ≤ (K : ℝ) ^ 3 := by positivity
          have hb3 : (0 : ℝ) ≤ (1 + Real.log T) ^ 4 := by positivity
          have hb4 : (0 : ℝ) ≤ 21381376 * s4 := by positivity
          nlinarith [hK3, hlog4, mul_nonneg hb1 hb2, pow_nonneg hs3pos.le 3]
        have h2 : 512 * s3 ^ 3 * CE ^ 2 * (CF + 1) * (21381376 * s4) < s1 := by
          rw [← hs3s1]
          have hs3s4 : s3 = s4 ^ 2 := hs4sq.symm
          have hexp : s3 ^ 4 = s3 ^ 3 * (s4 * s4) := by
            rw [show s3 ^ 4 = s3 ^ 3 * s3 by ring, hs3s4]
            ring
          rw [hexp]
          have hfactor : 512 * s3 ^ 3 * CE ^ 2 * (CF + 1) * (21381376 * s4)
              = (512 * 21381376 * CE ^ 2 * (CF + 1)) * s4 * s3 ^ 3 := by ring
          rw [hfactor]
          have hcoef : 512 * 21381376 * CE ^ 2 * (CF + 1) < s4 := by
            have : 512 * 21381376 * CE ^ 2 * (CF + 1)
                ≤ 512 * 21381376 * (CE ^ 2 + 1) * (CF + 1) := by nlinarith
            rw [hDdef] at hs4D
            nlinarith [sq_nonneg 74000, hCF]
          have hpos : (0 : ℝ) < s4 * s3 ^ 3 := by positivity
          nlinarith [pow_pos hs3pos 3, hs4pos]
        linarith
      -- assemble the strict inequality
      have hchain : (∫ τ in (a k)..(a (k + 1)), hardyZ τ) ^ 2 * F4
          ≤ CE ^ 2 * (T * s1) * F4 :=
        mul_le_mul_of_nonneg_right hmeansq hF40.le
      have hfin : CE ^ 2 * (T * s1) * F4 < T ^ 3 / (512 * (K : ℝ) ^ 3) := by
        rw [lt_div_iff₀ (by positivity : (0 : ℝ) < 512 * (K : ℝ) ^ 3), hF4def]
        have hT3 : T ^ 3 = T ^ 2 * s1 ^ 2 := by rw [hs1sq]; ring
        rw [hT3]
        have hlhs : CE ^ 2 * (T * s1) * ((CF + 1) * T * (1 + Real.log T) ^ 4)
            * (512 * (K : ℝ) ^ 3)
            = (512 * (K : ℝ) ^ 3 * CE ^ 2 * (CF + 1) * (1 + Real.log T) ^ 4)
              * (s1 * T ^ 2) := by ring
        rw [hlhs]
        have hstep := mul_lt_mul_of_pos_right hkey
          (mul_pos hs1pos (pow_pos hT0 2))
        nlinarith [hstep]
      rw [hΘcube]
      exact lt_of_le_of_lt hchain hfin
    obtain ⟨τ, hτ, hz⟩ := exists_riemannZeta_line_zero_of_hardyZ_fourth_moment_gap
      (α := a k) (β := a (k + 1)) (S := Θ) (F := F4) (ha_le k) hΘ0 hΘm'
      (hF4w k hkK) hgap
    exact ⟨τ, ⟨hτ.1, hτ.2⟩, hz⟩
  -- select one zero per heavy window, away from the left edge
  set heavy' : Finset ℕ := heavy.erase 0 with hheavy'def
  set g : ℕ → ℝ := fun k =>
    if h : ∃ τ, ((a k ≤ τ ∧ τ ≤ a (k + 1)) ∧ riemannZeta (linePt τ) = 0)
    then h.choose else 0 with hgdef
  have hg : ∀ k ∈ heavy, (a k ≤ g k ∧ g k ≤ a (k + 1)) ∧
      riemannZeta (linePt (g k)) = 0 := by
    intro k hk
    have hex := hzero k hk
    rw [hgdef]
    dsimp only
    rw [dif_pos hex]
    exact hex.choose_spec
  refine ⟨heavy'.image g, ?_, ?_⟩
  · intro τ hτ
    obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hτ
    have hkheavy : k ∈ heavy := Finset.mem_of_mem_erase hk
    have hk0 : k ≠ 0 := Finset.ne_of_mem_erase hk
    have hk1 : 1 ≤ k := Nat.one_le_iff_ne_zero.mpr hk0
    have hkK : k < K := (hheavymem k hkheavy).1
    obtain ⟨⟨hlow, hhigh⟩, hz⟩ := hg k hkheavy
    refine ⟨?_, ?_, hz⟩
    · have h1 : T + 1 * (T / K) ≤ a k := by
        rw [hadef]
        dsimp only
        have : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk1
        nlinarith [hT0, hKR0]
      have h2 : (0 : ℝ) < T / K := by positivity
      linarith
    · exact le_trans hhigh (ha_le2T (k + 1) hkK)
  · -- the cardinality lower bound
    have hfiber : ∀ b ∈ heavy'.image g, (heavy'.filter (fun k => g k = b)).card ≤ 2 := by
      intro b hb
      set fib : Finset ℕ := heavy'.filter (fun k => g k = b) with hfibdef
      by_cases hne : fib.Nonempty
      · set k₀ : ℕ := fib.min' hne with hk₀def
        have hsub : fib ⊆ Finset.Icc k₀ (k₀ + 1) := by
          intro k hkfib
          rw [Finset.mem_Icc]
          refine ⟨Finset.min'_le fib k hkfib, ?_⟩
          have hk₀fib : k₀ ∈ fib := Finset.min'_mem fib hne
          have hk₀heavy : k₀ ∈ heavy := Finset.mem_of_mem_erase
            (Finset.mem_filter.mp hk₀fib).1
          have hkheavy : k ∈ heavy := Finset.mem_of_mem_erase
            (Finset.mem_filter.mp hkfib).1
          have hgk₀ : g k₀ = b := (Finset.mem_filter.mp hk₀fib).2
          have hgk : g k = b := (Finset.mem_filter.mp hkfib).2
          obtain ⟨⟨hlow₀, hhigh₀⟩, _⟩ := hg k₀ hk₀heavy
          obtain ⟨⟨hlowk, hhighk⟩, _⟩ := hg k hkheavy
          -- the common value lies in both windows
          have hcross : a k ≤ a (k₀ + 1) := by
            calc a k ≤ g k := hlowk
              _ = b := hgk
              _ = g k₀ := hgk₀.symm
              _ ≤ a (k₀ + 1) := hhigh₀
          rw [hadef] at hcross
          dsimp only at hcross
          have hcross' : (k : ℝ) * (T / K) ≤ ((k₀ : ℝ) + 1) * (T / K) := by
            push_cast at hcross
            linarith
          have h2 : (k : ℝ) ≤ (k₀ : ℝ) + 1 := (mul_le_mul_right hTK0).mp hcross'
          exact_mod_cast h2
        calc fib.card ≤ (Finset.Icc k₀ (k₀ + 1)).card := Finset.card_le_card hsub
          _ = 2 := by rw [Nat.card_Icc]; omega
      · rw [Finset.not_nonempty_iff_eq_empty] at hne
        rw [hne]
        norm_num
    have hcard2 := Finset.card_le_mul_card_image heavy' 2 hfiber
    have hcard1 : heavy.card - 1 ≤ heavy'.card := by
      rw [hheavy'def]
      by_cases h0 : (0 : ℕ) ∈ heavy
      · rw [Finset.card_erase_of_mem h0]
      · rw [Finset.erase_eq_of_not_mem h0]
        omega
    -- assemble the count
    have hcardnat : heavy.card ≤ 2 * (heavy'.image g).card + 1 := by
      have h2 := hcard2
      omega
    have hcardcast : (heavy.card : ℝ) ≤ 2 * ((heavy'.image g).card : ℝ) + 1 := by
      exact_mod_cast hcardnat
    have hlog2pos : (0 : ℝ) < (1 + Real.log T) ^ 2 := by positivity
    have hsCF0 : (0 : ℝ) ≤ Real.sqrt (CF + 1) := Real.sqrt_nonneg _
    have hs4bound : s4 ≤ (32 * ((heavy'.image g).card : ℝ) + 16)
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
      have h5 : (0 : ℝ) ≤ 4624 * Real.sqrt s4 := by positivity
      calc (1 + Real.log T) ^ 2
          = Real.sqrt (((1 + Real.log T) ^ 2) ^ 2) := (Real.sqrt_sq (by positivity)).symm
        _ ≤ Real.sqrt ((4624 * Real.sqrt s4) ^ 2) := Real.sqrt_le_sqrt h2
        _ = 4624 * Real.sqrt s4 := Real.sqrt_sq h5
    have himg1 : 1 ≤ (heavy'.image g).card := by
      by_contra h0
      push_neg at h0
      have h0' : (heavy'.image g).card = 0 := by omega
      have hz : (((heavy'.image g).card : ℕ) : ℝ) = 0 := by exact_mod_cast h0'
      rw [hz] at hs4bound
      have h1 : s4 ≤ 16 * Real.sqrt (CF + 1) * (4624 * Real.sqrt s4) := by
        nlinarith [hlogsq]
      have hsq4pos : (0 : ℝ) < Real.sqrt s4 := Real.sqrt_pos.mpr hs4pos
      have h2 : Real.sqrt s4 * Real.sqrt s4 = s4 := Real.mul_self_sqrt hs40
      have h3 : Real.sqrt s4 ≤ 73984 * Real.sqrt (CF + 1) := by
        nlinarith
      have hCFsq : Real.sqrt (CF + 1) * Real.sqrt (CF + 1) = CF + 1 :=
        Real.mul_self_sqrt (by linarith)
      have h4 : s4 ≤ 73984 ^ 2 * (CF + 1) := by
        nlinarith
      rw [hDdef] at hs4D
      nlinarith [sq_nonneg CE, hCF]
    have himgR : (1 : ℝ) ≤ ((heavy'.image g).card : ℝ) := by exact_mod_cast himg1
    have hfin : s4 ≤ 48 * ((heavy'.image g).card : ℝ)
        * ((Real.sqrt (CF + 1) + 1) * (1 + Real.log T) ^ 2) := by
      have h1 : 32 * ((heavy'.image g).card : ℝ) + 16
          ≤ 48 * ((heavy'.image g).card : ℝ) := by linarith
      have hb : (0 : ℝ) ≤ Real.sqrt (CF + 1) * (1 + Real.log T) ^ 2 := by positivity
      have h2 : s4 ≤ 48 * ((heavy'.image g).card : ℝ)
          * (Real.sqrt (CF + 1) * (1 + Real.log T) ^ 2) := by
        nlinarith [hs4bound]
      nlinarith [himgR, hlog2pos]
    rw [div_le_iff₀ hlog2pos]
    have hc48 : (0 : ℝ) < 48 * (Real.sqrt (CF + 1) + 1) := by positivity
    have hinv : 1 / (48 * (Real.sqrt (CF + 1) + 1)) * (48 * (Real.sqrt (CF + 1) + 1)) = 1 := by
      field_simp
    nlinarith [hfin, hc48, mul_pos hc48 hlog2pos]

end

end RHTower
