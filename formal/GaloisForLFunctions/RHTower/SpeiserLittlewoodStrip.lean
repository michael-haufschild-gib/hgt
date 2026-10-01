import GaloisForLFunctions.RHTower.SpeiserLocalDisk
import GaloisForLFunctions.RHTower.Sieve.ZetaLittlewoodRegionAbs

/-!
# A Littlewood-width zero-free strip for `ζ'` next to the imaginary axis

**Theorem** (`exists_deriv_riemannZeta_ne_zero_littlewood_strip`). There are `c, T₀ > 0` such that
`ζ'(s) ≠ 0` whenever `Im s ≥ T₀` and `0 < Re s < c · log log (Im s) / log (Im s)`.

**Proof.**
- By the local Speiser theorem (`exists_xi_zero_disk_of_deriv_riemannZeta_eq_zero`), a zero of `ζ'`
  at `s` lies in the Speiser disk of a zero `ρ` of `ξ`. So `|Im ρ − Im s| < 1/2`, and one of
  `ρ`, `1 − ρ̄` has real part at least `1 − Re s`.
- That zero of `ζ` would violate Littlewood's zero-free region
  `Re > 1 − c log log |γ| / log |γ|` (`Sieve.exists_littlewood_zero_free_region_abs`).
-/

open Complex

namespace RHTower

noncomputable section

/-- For large `t`, `log log (t/2) ≥ (1/2) log log t`. -/
theorem eventually_half_loglog_le_loglog_half :
    ∀ᶠ t : ℝ in Filter.atTop, Real.log (Real.log t) / 2 ≤ Real.log (Real.log (t / 2)) := by
  have hL := Real.tendsto_log_atTop.eventually_ge_atTop (16 : ℝ)
  filter_upwards [hL, Filter.eventually_ge_atTop (4 : ℝ)] with t hlog ht4
  have ht0 : 0 < t := by linarith
  have hl2 : Real.log (t / 2) = Real.log t - Real.log 2 := Real.log_div ht0.ne' (by norm_num)
  have hlog2 : Real.log 2 < 1 := by have := Real.log_two_lt_d9; linarith
  -- `log t − log 2 ≥ √(log t)` since `log t ≥ 16`
  have hsq : Real.sqrt (Real.log t) ≤ Real.log (t / 2) := by
    rw [hl2]
    have hs : Real.sqrt (Real.log t) ≤ Real.log t / 4 := by
      rw [Real.sqrt_le_left (by positivity)]
      nlinarith
    linarith
  have hsqpos : 0 < Real.sqrt (Real.log t) := Real.sqrt_pos.mpr (by linarith)
  have := Real.log_le_log hsqpos hsq
  rw [Real.log_sqrt (by linarith)] at this
  linarith

/-- **Littlewood-width strip for `ζ'`.** -/
theorem exists_deriv_riemannZeta_ne_zero_littlewood_strip :
    ∃ c T₀ : ℝ, 0 < c ∧ ∀ s : ℂ, T₀ ≤ s.im → 0 < s.re →
      s.re < c * Real.log (Real.log s.im) / Real.log s.im → deriv riemannZeta s ≠ 0 := by
  obtain ⟨c, T, hc, hT3, hreg⟩ := Sieve.exists_littlewood_zero_free_region_abs
  obtain ⟨T₁, hT₁⟩ := Filter.eventually_atTop.mp eventually_half_loglog_le_loglog_half
  have hL := Filter.eventually_atTop.mp
    (Real.tendsto_log_atTop.eventually_ge_atTop ((c + 4) ^ 2 + 16 : ℝ))
  obtain ⟨T₂, hT₂⟩ := hL
  refine ⟨c / 4, max (max (T + 1) (T₁ + 1)) (max T₂ 1000), by positivity, ?_⟩
  intro s hs h0 h1 hd
  set t := s.im with ht
  have htT : T + 1 ≤ t := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hs
  have htT₁ : T₁ + 1 ≤ t := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hs
  have htT₂ : T₂ ≤ t := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hs
  have ht1000 : 1000 ≤ t := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hs
  have hlogt : (c + 4) ^ 2 + 16 ≤ Real.log t := hT₂ t htT₂
  have hlogt16 : 16 ≤ Real.log t := by nlinarith [sq_nonneg (c + 4)]
  have hloglog : 0 < Real.log (Real.log t) := Real.log_pos (by linarith)
  -- `Re s < 1/2`
  have hs12 : s.re < 1 / 2 := by
    set L := Real.log t with hLdef
    have hL0 : 0 < L := by nlinarith
    have hsqL : c + 4 ≤ Real.sqrt L := by
      rw [Real.le_sqrt (by linarith) hL0.le]; nlinarith
    have hLL : Real.log L ≤ 2 * Real.sqrt L := by
      have h := Real.log_le_sub_one_of_pos (Real.sqrt_pos.mpr hL0)
      rw [Real.log_sqrt hL0.le] at h
      linarith
    have hsq : Real.sqrt L * Real.sqrt L = L := Real.mul_self_sqrt hL0.le
    have hkey : c / 4 * Real.log L / L < 1 / 2 := by
      rw [div_lt_iff₀ hL0]
      have hc0 : 0 ≤ c / 4 := by positivity
      have h1' : c / 4 * Real.log L ≤ c / 4 * (2 * Real.sqrt L) :=
        mul_le_mul_of_nonneg_left hLL hc0
      nlinarith [Real.sqrt_nonneg L]
    linarith
  obtain ⟨ρ, hρ, hρ0, hρ1, hdisk⟩ :=
    exists_xi_zero_disk_of_deriv_riemannZeta_eq_zero h0 hs12 (by linarith) hd
  -- the ordinate of `ρ` is within `1/2` of `t`
  have hsq : (s.re - 1 / 2) ^ 2 ≤ (ρ.re - 1 / 2) ^ 2 := by nlinarith [sq_nonneg (t - ρ.im)]
  have hγ : |t - ρ.im| < 1 / 2 := by
    have : (ρ.re - 1 / 2) ^ 2 < 1 / 4 := by nlinarith
    have hq : (t - ρ.im) ^ 2 < 1 / 4 := by nlinarith [sq_nonneg (s.re - 1 / 2)]
    rw [← sq_lt_sq₀ (abs_nonneg _) (by norm_num), sq_abs]; linarith
  obtain ⟨hγ1, hγ2⟩ := abs_lt.mp hγ
  have hγpos : 0 < ρ.im := by linarith
  have habsγ : |ρ.im| = ρ.im := abs_of_pos hγpos
  have hdist : 1 / 2 - s.re ≤ |ρ.re - 1 / 2| := by
    have := sq_le_sq.mp hsq
    rw [abs_of_neg (by linarith : s.re - 1 / 2 < 0)] at this
    linarith
  -- the Littlewood width at `Im ρ` dominates the strip width at `t`
  have hwidth : c / 4 * Real.log (Real.log t) / Real.log t ≤
      c * Real.log (Real.log |ρ.im|) / Real.log |ρ.im| := by
    rw [habsγ]
    have hlo : t / 2 ≤ ρ.im := by linarith
    have hhi : ρ.im ≤ 2 * t := by linarith
    have hlogγ_le : Real.log ρ.im ≤ 2 * Real.log t := by
      have := Real.log_le_log hγpos hhi
      rw [Real.log_mul (by norm_num) (by linarith)] at this
      have hl2 : Real.log 2 < 1 := by have := Real.log_two_lt_d9; linarith
      linarith
    have hlogγ_pos : 0 < Real.log ρ.im := Real.log_pos (by linarith)
    have hll : Real.log (Real.log t) / 2 ≤ Real.log (Real.log ρ.im) := by
      have h1' := hT₁ t (by linarith)
      have h2' : Real.log (Real.log (t / 2)) ≤ Real.log (Real.log ρ.im) := by
        apply Real.log_le_log
        · exact Real.log_pos (by linarith)
        · exact Real.log_le_log (by linarith) hlo
      linarith
    rw [div_le_div_iff₀ (by linarith) hlogγ_pos]
    have hc4 : 0 ≤ c / 4 := by positivity
    nlinarith [mul_le_mul_of_nonneg_left hll (le_of_lt hc), mul_le_mul_of_nonneg_left hlogγ_le
      (mul_nonneg hc4 hloglog.le)]
  -- a zero of `ζ` with real part at least `1 − Re s`
  obtain ⟨b, hb, hbre, hbim⟩ : ∃ w : ℂ, riemannZeta w = 0 ∧ 1 - s.re ≤ w.re ∧ w.im = ρ.im ∧
      w.re ≤ 1 := by
    have hρne1 : ρ ≠ 1 := fun h => by rw [h, Complex.one_re] at hρ1; exact lt_irrefl 1 hρ1
    rcases le_or_gt (1 / 2) ρ.re with h | h
    · refine ⟨ρ, (xi_eq_zero_iff hρ0 hρne1).mp hρ, ?_, rfl, hρ1.le⟩
      rw [abs_of_nonneg (by linarith)] at hdist; linarith
    · set w := 1 - (starRingEnd ℂ) ρ with hw
      have hwre : w.re = 1 - ρ.re := by rw [hw]; simp
      have hwim : w.im = ρ.im := by rw [hw]; simp
      have hxw : xi w = 0 := by rw [hw, xi_one_sub, xi_conj, hρ, map_zero]
      have hw0 : 0 < w.re := by rw [hwre]; linarith
      have hw1 : w ≠ 1 := fun h' => by rw [h', Complex.one_re] at hwre; linarith
      refine ⟨w, (xi_eq_zero_iff hw0 hw1).mp hxw, ?_, hwim, by rw [hwre]; linarith⟩
      rw [abs_of_neg (by linarith)] at hdist; rw [hwre]; linarith
  obtain ⟨hbim', hbre1⟩ := hbim
  have hbT : T ≤ |b.im| := by rw [hbim', habsγ]; linarith
  have hlt : 1 - c * Real.log (Real.log |b.im|) / Real.log |b.im| < b.re := by
    rw [hbim']; linarith
  apply hreg b.re b.im hbT hbre1 hlt
  have : (b.re : ℂ) + (b.im : ℂ) * Complex.I = b := Complex.re_add_im b
  rw [this]; exact hb

end

end RHTower
