import GaloisForLFunctions.RHTower.HardyWindowCountTheorem

/-!
# The sixth-root critical-line census

Cauchy–Schwarz over the heavy windows replaces the per-window mass cap of the
`T^{1/16}` census: `(Σ_S m_k)² ≤ |S| · Σ_S m_k²` with `m_k² ≤ H·m4_k` and the window
fourth moments summing to the dyadic fourth moment gives `(T/8)² ≤ |S| · H · M4`, so the
heavy count is linear in the window count `K` rather than `√K`.  The sign-change gap
tolerates `K` up to `T^{1/6}/polylog`, and with `K = ⌊T^{1/6}/(D₀(1+log T)²)⌋` the census
reaches `N₀(T) ≥ c · T^{1/6}/(1+log T)⁶` — the ceiling of the window-pigeonhole route
against the trivial `T^{3/4}` window mean.
-/

open Set MeasureTheory Complex Finset

namespace RHTower

noncomputable section

/-! ## Cauchy–Schwarz counting over the heavy windows

The per-window mass cap `m_k ≤ √(H·M4)` wastes the fourth moment: summing the caps over the
heavy set and applying Cauchy–Schwarz to the *sum* instead gives `(T/8)² ≤ |S| · H · M4`,
a quadratically stronger count.  With the trivial window mean this lifts the census exponent
from `T^{1/16}` to `T^{1/6}`, the ceiling of this route. -/

/-- **Heavy-window pigeonhole with Cauchy–Schwarz counting.**  If the dyadic second moment is
at least `T/4`, the dyadic fourth moment is at most `M4`, and every window mean is at most
`ME` with `ME² M4` losing to the cube of the heaviness threshold, then a family of windows —
each carrying a critical-line zero — exists with `(T/8)² ≤ |S| · (T/K) · M4`. -/
theorem exists_heavyFinset_sq {T : ℝ} {K : ℕ} (hK1 : 1 ≤ K) (hT0 : 0 < T)
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

theorem log_sq_le_rpow {T : ℝ} (hT1 : 1 ≤ T) :
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

private theorem no_small_x_sixth {T D0 CF Y : ℝ} (hT0 : 0 < T) (hCF : 0 ≤ CF)
    (hD0pos : 0 < D0) (hD08 : 8 ≤ D0) (hY2 : 2 ≤ Y)
    (hroot : Y ≤ T ^ ((1 : ℝ) / 96))
    (hLsq : (1 + Real.log T) ^ 2 ≤ 4624 * T ^ ((1 : ℝ) / 32))
    (hL0 : 0 < 1 + Real.log T)
    (hYdef : Y = 9248 * D0 + 384 * D0 * (CF + 1) * 4624 ^ 3 + 2)
    (hpow7 : (T ^ ((1 : ℝ) / 96)) ^ (7 : ℕ) = T ^ ((7 : ℝ) / 96))
    (hT6 : T ^ ((1 : ℝ) / 6) ≤ 128 * D0 * (CF + 1) * (1 + Real.log T) ^ 6) :
    False := by
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

private theorem sixth_final_count {T D0 CF Y x M4 : ℝ} {K : ℕ}
    {S : Finset ℕ} {τS : Finset ℝ}
    (hT0 : 0 < T) (hT1 : 1 ≤ T) (hCF : 0 ≤ CF)
    (hD0pos : 0 < D0) (hD08 : 8 ≤ D0) (hY2 : 2 ≤ Y)
    (hroot : Y ≤ T ^ ((1 : ℝ) / 96))
    (hLsq : (1 + Real.log T) ^ 2 ≤ 4624 * T ^ ((1 : ℝ) / 32))
    (hYdef : Y = 9248 * D0 + 384 * D0 * (CF + 1) * 4624 ^ 3 + 2)
    (hpow7 : (T ^ ((1 : ℝ) / 96)) ^ (7 : ℕ) = T ^ ((7 : ℝ) / 96))
    (hM4def : M4 = (CF + 1) * T * (1 + Real.log T) ^ 4)
    (hDL2pos : 0 < D0 * (1 + Real.log T) ^ 2)
    (hxK : x ≤ 2 * (K : ℝ))
    (hxval : T ^ ((1 : ℝ) / 6) = x * (D0 * (1 + Real.log T) ^ 2))
    (hKR0 : (0 : ℝ) < (K : ℝ)) (hKne : (K : ℝ) ≠ 0)
    (hScount : (T / 8) ^ 2 ≤ (S.card : ℝ) * ((T / K) * M4))
    (hτScard : S.card ≤ 2 * τS.card + 1) :
    1 / (384 * D0 * (CF + 1) + 1) * T ^ ((1 : ℝ) / 6) / (1 + Real.log T) ^ 6
      ≤ (τS.card : ℝ) := by
  have hlog0 : (0 : ℝ) ≤ Real.log T := Real.log_nonneg hT1
  have hL1 : (1 : ℝ) ≤ 1 + Real.log T := by linarith only [hlog0]
  have hL0 : (0 : ℝ) < 1 + Real.log T := by linarith only [hL1]
  -- the counting arithmetic
  have hcard : (K : ℝ) ≤ 64 * (S.card : ℝ) * (CF + 1) * (1 + Real.log T) ^ 4 := by
    have h1 : (T / 8) ^ 2 * (K : ℝ) ≤ (S.card : ℝ) * ((T / K) * M4) * (K : ℝ) :=
      mul_le_mul_of_nonneg_right hScount hKR0.le
    have h2 : (S.card : ℝ) * ((T / K) * M4) * (K : ℝ) = (S.card : ℝ) * (T * M4) := by
      have hTK : T / K * (K : ℝ) = T := div_mul_cancel₀ T hKne
      calc (S.card : ℝ) * ((T / K) * M4) * (K : ℝ)
          = (S.card : ℝ) * M4 * (T / K * (K : ℝ)) := by ring
        _ = (S.card : ℝ) * M4 * T := by rw [hTK]
        _ = (S.card : ℝ) * (T * M4) := by ring
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
    exact no_small_x_sixth hT0 hCF hD0pos hD08 hY2 hroot hLsq hL0 hYdef hpow7 hT6
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
      have h2 : D0 ≤ D0 ^ 3 := by
        have hh : (0 : ℝ) ≤ D0 * (D0 - 1) * (D0 + 1) :=
          mul_nonneg (mul_nonneg (by linarith only [hD08]) (by linarith only [hD08]))
            (by linarith only [hD08])
        nlinarith [hh]
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
    linarith only [h1]
  have hEwin : ∀ k : ℕ, k < K →
      |∫ τ in (T + k * (T / K))..(T + ((k + 1 : ℕ) : ℝ) * (T / K)), hardyZ τ|
        ≤ CE * (Real.sqrt T * Real.sqrt (Real.sqrt T)) := by
    intro k hkK
    have hk1K : ((k : ℝ) + 1) ≤ (K : ℝ) := by exact_mod_cast hkK
    refine hE hT16 ?_ ?_ ?_
    · have h0 : (0 : ℝ) ≤ (k : ℝ) * (T / K) :=
        mul_nonneg (Nat.cast_nonneg k) hTK0.le
      linarith only [h0]
    · push_cast
      linarith only [hTK0]
    · push_cast
      have h1 : ((k : ℝ) + 1) * (T / K) ≤ (K : ℝ) * (T / K) :=
        mul_le_mul_of_nonneg_right hk1K hTK0.le
      have h2 : (K : ℝ) * (T / K) = T := by field_simp
      linarith only [h1, h2.le, h2.ge]
  obtain ⟨S, hSzero, hScount⟩ :=
    exists_heavyFinset_sq hK1 hT0 hM40 hCdyadic hM4dyadic hEwin hgap
  obtain ⟨τS, hτSmem, hτScard⟩ := exists_distinct_ordinates hT0 hK1 S hSzero
  refine ⟨τS, hτSmem, ?_⟩
  exact sixth_final_count hT0 hT1 hCF hD0pos hD08 hY2 hroot hLsq hYdef hpow7
    hM4def hDL2pos hxK hxval hKR0 hKne hScount hτScard


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
