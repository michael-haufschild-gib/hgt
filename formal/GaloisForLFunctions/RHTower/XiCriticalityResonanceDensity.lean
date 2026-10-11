import GaloisForLFunctions.RHTower.ZetaCriticalNonRigidDensity
import GaloisForLFunctions.RHTower.XiCriticalityLocalRigidity

/-!
# Lossless ports are critical on a positive proportion of the spectrum

**Theorem** (`exists_eventually_card_critical_resonances_ge`). Let `E` be strict lower Pólya, nonzero
on `ℝ`, with `Re E = Ξ` on `ℝ`. There are `c, C > 0` such that for all large `T`, every finite set
of complex numbers containing all zeros `z` of `E` with `3T^{1/2} − 1 ≤ Re z ≤ T + 1` and
`−C/log T ≤ Im z ≤ 0` has at least `c T log T` elements. Since `N(T) ≍ T log T`, a positive
proportion of all resonances lies within the critical depth `C/log T`.

**Proof.**
- `E` forces RH, so the non-rigid heights have measure `> 10⁻¹⁷ T`
  (`eventually_volume_nonRigidHeights_gt`).
- Off the extended bad set (the Selberg polynomial is `≤ Θ` at the 19 grid points `t + 2jτ₂`,
  `|j| ≤ 9`, at both scales; measure `O(T/B₁²)`), count control gives a zero within `τ₂` of every
  grid point. So all gaps within `14τ₂` of `t` are `< 4τ₂`.
- A non-rigid index `k` near such `t` then has `γ_k, γ_{k+2}` within `16τ₂` of `t`. By
  `rigidAt_of_local_resonance_free`, `E` has a zero in the box of half-width `17τ₂ + m` around
  `t`, with depth `≤ h`, where `m = h = 2 · 10⁶⁰/log T`.
- So the non-rigid good heights are covered by intervals of length `2(17τ₂ + m)` around those
  zeros, which bounds their number from below.
-/

noncomputable section

open Complex Filter Topology Set MeasureTheory

namespace RHTower

/-- **No gap of length `4τ₂` within `14τ₂` of `t`** when every grid point `t + 2jτ₂`, `|j| ≤ 9`,
has a zero within `τ₂`. -/
theorem ordinateGap_lt_of_gridExt {t τ₂ : ℝ} (hτ₂ : 0 < τ₂)
    (hgrid : ∀ j : ℤ, |j| ≤ 9 → ∃ n, |xiOrderedPositiveOrdinate n - (t + 2 * j * τ₂)| < τ₂)
    {m : ℕ} (hm : |xiOrderedPositiveOrdinate m - t| ≤ 14 * τ₂) : ordinateGap m < 4 * τ₂ := by
  by_contra hcon
  push Not at hcon
  set γ := xiOrderedPositiveOrdinate with hγ
  set j : ℤ := ⌈(γ m + τ₂ - t) / (2 * τ₂)⌉ with hj
  have hj1 : (γ m + τ₂ - t) / (2 * τ₂) ≤ j := Int.le_ceil _
  have hj2 : (j : ℝ) < (γ m + τ₂ - t) / (2 * τ₂) + 1 := Int.ceil_lt_add_one _
  rw [div_le_iff₀ (by positivity)] at hj1
  rw [← sub_lt_iff_lt_add, lt_div_iff₀ (by positivity)] at hj2
  rw [abs_le] at hm
  have h3 : (-7 : ℝ) < j := by
    by_contra h; push Not at h
    have : (j : ℝ) * (2 * τ₂) ≤ -7 * (2 * τ₂) := mul_le_mul_of_nonneg_right h (by positivity)
    linarith
  have h4 : (j : ℝ) < 9 := by
    by_contra h; push Not at h
    have : 9 * (2 * τ₂) ≤ (j : ℝ) * (2 * τ₂) := mul_le_mul_of_nonneg_right h (by positivity)
    linarith
  have hjabs : |j| ≤ 9 := by
    have h3' : (-7 : ℤ) < j := by exact_mod_cast h3
    have h4' : j < 9 := by exact_mod_cast h4
    rw [abs_le]; constructor <;> omega
  obtain ⟨n, hn⟩ := hgrid j hjabs
  rw [abs_lt] at hn
  have hlo : γ m < γ n := by linarith
  have hhi : γ n < γ (m + 1) := by
    have : γ (m + 1) = γ m + ordinateGap m := by simp [ordinateGap, hγ]
    linarith
  rcases le_or_gt n m with hnm | hnm
  · linarith [xiOrderedPositiveOrdinate_monotone hnm]
  · linarith [xiOrderedPositiveOrdinate_monotone (show m + 1 ≤ n by omega)]

/-- The extended bad heights: `t ∈ [A, B]` with `‖D‖ > Θ` at some grid point `t + 2jτ₂`,
`|j| ≤ 9`, at scale `τ₁` or `τ₂`. -/
def criticalBadSetExt (x τ₁ τ₂ Θ A B : ℝ) : Set ℝ :=
  Icc A B ∩ {t | ∃ j : ℤ, |j| ≤ 9 ∧
    (Θ < ‖selbergVonMangoldtPoly x (narrowPoint τ₁ (t + 2 * j * τ₂))‖ ∨
      Θ < ‖selbergVonMangoldtPoly x (narrowPoint τ₂ (t + 2 * j * τ₂))‖)}

/-- **The extended bad set is small.** -/
theorem volume_criticalBadSetExt_le {x τ₁ τ₂ Θ A B : ℝ} (hx : 1 < x) (hτ₁ : 0 < τ₁)
    (hτ₁₂ : τ₁ ≤ τ₂) (hτ₂1 : τ₂ ≤ 1) (hΘ : 0 < Θ) (hAB : A ≤ B) :
    volume (criticalBadSetExt x τ₁ τ₂ Θ A B) ≤ ENNReal.ofReal (38 *
      ((B - A + 8 * selbergPolyLength x * (1 + Real.log (selbergPolyLength x))) * (5 / τ₁ ^ 2) /
        Θ ^ 2)) := by
  set E := (B - A + 8 * selbergPolyLength x * (1 + Real.log (selbergPolyLength x))) *
    (5 / τ₁ ^ 2) with hE
  have hτ₂ : 0 < τ₂ := hτ₁.trans_le hτ₁₂
  have hlen : 0 ≤ B - A + 8 * selbergPolyLength x * (1 + Real.log (selbergPolyLength x)) := by
    have h1 := Real.log_natCast_nonneg (selbergPolyLength x)
    have h2 : (0 : ℝ) ≤ selbergPolyLength x := Nat.cast_nonneg _
    nlinarith
  have hpiece : ∀ τ : ℝ, 0 < τ → τ₁ ≤ τ → τ ≤ 1 → ∀ s : ℝ,
      volume (Icc A B ∩ {t | Θ < ‖selbergVonMangoldtPoly x (narrowPoint τ (t + s))‖}) ≤
        ENNReal.ofReal (E / Θ ^ 2) := by
    intro τ hτ hτ₁τ hτ1 s
    refine (GaloisForLFunctions.HTGeometry.volume_Icc_inter_lt_norm_le
      (continuous_selbergVonMangoldtPoly_narrow hx τ s) hAB hΘ).trans
      (ENNReal.ofReal_le_ofReal ?_)
    gcongr
    refine (integral_normSq_selbergNarrow_shift_le hx hτ hτ1 hAB s).trans ?_
    rw [hE]
    gcongr
  have hsub : criticalBadSetExt x τ₁ τ₂ Θ A B ⊆ ⋃ j ∈ Finset.Icc (-9 : ℤ) 9,
      ((Icc A B ∩ {t | Θ < ‖selbergVonMangoldtPoly x (narrowPoint τ₁ (t + 2 * j * τ₂))‖}) ∪
        (Icc A B ∩ {t | Θ < ‖selbergVonMangoldtPoly x (narrowPoint τ₂ (t + 2 * j * τ₂))‖})) := by
    rintro t ⟨ht, j, hj, hj'⟩
    rw [Set.mem_iUnion₂]
    refine ⟨j, by rw [Finset.mem_Icc]; exact abs_le.mp hj, ?_⟩
    rcases hj' with h | h
    · exact Or.inl ⟨ht, h⟩
    · exact Or.inr ⟨ht, h⟩
  refine (measure_mono hsub).trans ((measure_biUnion_finset_le _ _).trans ?_)
  calc ∑ j ∈ Finset.Icc (-9 : ℤ) 9, volume
        ((Icc A B ∩ {t | Θ < ‖selbergVonMangoldtPoly x (narrowPoint τ₁ (t + 2 * j * τ₂))‖}) ∪
          (Icc A B ∩ {t | Θ < ‖selbergVonMangoldtPoly x (narrowPoint τ₂ (t + 2 * j * τ₂))‖}))
      ≤ ∑ _j ∈ Finset.Icc (-9 : ℤ) 9, (ENNReal.ofReal (E / Θ ^ 2) + ENNReal.ofReal (E / Θ ^ 2)) :=
        Finset.sum_le_sum fun j _ => (measure_union_le _ _).trans
          (add_le_add (hpiece τ₁ hτ₁ le_rfl (hτ₁₂.trans hτ₂1) _) (hpiece τ₂ hτ₂ hτ₁₂ hτ₂1 _))
    _ = ENNReal.ofReal (38 * (E / Θ ^ 2)) := by
        rw [Finset.sum_const, show (Finset.Icc (-9 : ℤ) 9).card = 19 by rfl,
          ← ENNReal.ofReal_add (by positivity) (by positivity), nsmul_eq_mul,
          show ((19 : ℕ) : ENNReal) = ENNReal.ofReal 19 by simp,
          ← ENNReal.ofReal_mul (by norm_num)]
        congr 1; ring


/-- **Good extended heights have a zero near every grid point.** -/
theorem exists_ordinate_near_gridExt {T x t : ℝ} (hT1 : 1 ≤ T) (hL : 10 ^ 25 ≤ Real.log T)
    (hlx : Real.log x = Real.log T / 20)
    (hA : 3 * T ^ (1 / 2 : ℝ) + 1 / 2 ≤ t) (hBt : t ≤ T - 1 / 2)
    (hV : ∀ p, 3 * T ^ (1 / 2 : ℝ) - 1 ≤ p → p ≤ T + 1 → ∀ τ, 0 < τ → τ ≤ 1 / 2 →
      |narrowMass τ p - τ * Real.log (p / (2 * Real.pi)) / 2| ≤
        τ * ‖selbergVonMangoldtPoly x (narrowPoint τ p)‖ +
          2 * Real.exp (-(τ * Real.log x)) / (Real.log x * τ) * narrowMass τ p + 2 * τ +
          4 * τ * lorentzMassW (p / 2) p)
    (hW : ∀ p, 3 * T ^ (1 / 2 : ℝ) - 1 ≤ p → lorentzMassW (p / 2) p ≤ 1 / 4)
    (hgood : t ∉ criticalBadSetExt x (10 ^ 13 / Real.log T) (32 * 10 ^ 13 / Real.log T)
      ((Real.log T / 2 - 1) / 80) (3 * T ^ (1 / 2 : ℝ) + 1 / 2) (T - 1 / 2)) :
    ∀ j : ℤ, |j| ≤ 9 → ∃ n, |xiOrderedPositiveOrdinate n -
      (t + 2 * j * (32 * 10 ^ 13 / Real.log T))| < 32 * 10 ^ 13 / Real.log T := by
  set L := Real.log T with hLdef
  have hL0 : 0 < L := lt_of_lt_of_le (by norm_num) hL
  have hs := crit_rpow_half_ge hT1 hL
  have hτ₂s : 32 * 10 ^ 13 / L ≤ 1 / 10 ^ 10 := by
    rw [div_le_iff₀ hL0]; nlinarith
  have hτ₁s : (10 : ℝ) ^ 13 / L ≤ 1 / 10 ^ 10 := by
    rw [div_le_iff₀ hL0]; nlinarith
  have ht2 : 2 ≤ t := by nlinarith
  have hℓ1 := crit_log_ge hT1 (show 3 * T ^ (1 / 2 : ℝ) ≤ t by linarith)
  rw [← hLdef] at hℓ1
  intro j hj
  have hj' : |(j : ℝ)| ≤ 9 := by exact_mod_cast hj
  have hp : |t + 2 * j * (32 * 10 ^ 13 / L) - t| ≤ 1 := by
    rw [show t + 2 * j * (32 * 10 ^ 13 / L) - t = 2 * j * (32 * 10 ^ 13 / L) by ring, abs_mul,
      abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2), abs_of_pos (div_pos (by norm_num) hL0)]
    have : 2 * |(j : ℝ)| * (32 * 10 ^ 13 / L) ≤ 2 * 9 * (1 / 10 ^ 10) := by gcongr
    linarith
  have hp' := hp
  rw [abs_le] at hp'
  have hp1 : 3 * T ^ (1 / 2 : ℝ) - 1 ≤ t + 2 * j * (32 * 10 ^ 13 / L) := by linarith
  have hp2 : t + 2 * j * (32 * 10 ^ 13 / L) ≤ T + 1 := by linarith
  have hD : ‖selbergVonMangoldtPoly x (narrowPoint (10 ^ 13 / L) (t + 2 * j * (32 * 10 ^ 13 / L)))‖
        ≤ (L / 2 - 1) / 80 ∧
      ‖selbergVonMangoldtPoly x (narrowPoint (32 * 10 ^ 13 / L) (t + 2 * j * (32 * 10 ^ 13 / L)))‖
        ≤ (L / 2 - 1) / 80 := by
    by_contra hcon
    rw [not_and_or] at hcon
    push Not at hcon
    exact hgood ⟨⟨hA, hBt⟩, j, hj, hcon⟩
  have hC1 := countControl_critical_point hL hlx le_rfl rfl ht2 hp hℓ1
    (hV _ hp1 hp2 _ (by positivity) (by linarith)) (hW _ hp1) hD.1
  have hC2 := countControl_critical_point hL hlx (by norm_num) rfl ht2 hp hℓ1
    (hV _ hp1 hp2 _ (by positivity) (by linarith)) (hW _ hp1) hD.2
  set u := Real.log (t / (2 * Real.pi)) / L with hu
  have huL : u * L = Real.log (t / (2 * Real.pi)) := by rw [hu]; field_simp
  have hu0 : 0 < u := by rw [hu]; apply div_pos _ hL0; nlinarith
  have hnum := crit_hnum hL0 hu0
  rw [huL] at hnum
  refine exists_ordinate_near_of_countControl (by positivity) (by gcongr; norm_num)
    (by linarith) (by nlinarith) hnum hC1 hC2

/-- **A non-rigid good height has a critical resonance nearby.** -/
theorem exists_resonance_near_of_not_rigidAt {E : ℂ → ℂ} (hE : StrictLowerPolyaClass E)
    (hrep : ∀ t : ℝ, Xi t = (E t).re) (hne : ∀ t : ℝ, E t ≠ 0) {T t : ℝ} {k : ℕ}
    (hL : 10 ^ 25 ≤ Real.log T)
    (hgrid : ∀ j : ℤ, |j| ≤ 9 → ∃ n, |xiOrderedPositiveOrdinate n -
      (t + 2 * j * (32 * 10 ^ 13 / Real.log T))| < 32 * 10 ^ 13 / Real.log T)
    (hk : |xiOrderedPositiveOrdinate k - t| ≤ 8 * (32 * 10 ^ 13 / Real.log T))
    (hnr : ¬ RigidAt (10 ^ 60 / Real.log T) k) :
    ∃ z : ℂ, E z = 0 ∧ |z.re - t| ≤ 17 * (32 * 10 ^ 13 / Real.log T) + 2 * 10 ^ 60 / Real.log T ∧
      -(2 * 10 ^ 60 / Real.log T) ≤ z.im ∧ z.im ≤ 0 := by
  set L := Real.log T with hLdef
  have hL0 : 0 < L := lt_of_lt_of_le (by norm_num) hL
  set τ₂ : ℝ := 32 * 10 ^ 13 / L with hτ₂
  have hτ₂0 : 0 < τ₂ := by positivity
  set γ := xiOrderedPositiveOrdinate with hγ
  have hg0 := ordinateGap_lt_of_gridExt hτ₂0 hgrid (m := k) (by linarith [hk])
  rw [abs_le] at hk
  have hk1 : γ (k + 1) = γ k + ordinateGap k := by simp [ordinateGap, hγ]
  have hk2 : γ (k + 2) = γ (k + 1) + ordinateGap (k + 1) := by simp [ordinateGap, hγ]
  have hgk0 := ordinateGap_nonneg k
  have hgk1 := ordinateGap_nonneg (k + 1)
  have hg1 := ordinateGap_lt_of_gridExt hτ₂0 hgrid (m := k + 1)
    (by rw [abs_le]; constructor <;> linarith)
  by_contra hcon
  apply hnr
  have hfree : ∀ z : ℂ, (γ k - τ₂) - 2 * 10 ^ 60 / L ≤ z.re →
      z.re ≤ (γ (k + 2) + τ₂) + 2 * 10 ^ 60 / L → -(2 * 10 ^ 60 / L) ≤ z.im → z.im ≤ 0 →
      E z ≠ 0 := by
    intro z h1 h2 h3 h4 hz
    refine hcon ⟨z, hz, ?_, h3, h4⟩
    rw [abs_le]; constructor <;> linarith
  have hR := rigidAt_of_local_resonance_free hE hrep hne (h := 2 * 10 ^ 60 / L)
    (m := 2 * 10 ^ 60 / L) (by positivity) (by positivity) (by linarith) hfree
    (by linarith : γ k - τ₂ ≤ γ k) (by linarith : γ (k + 2) ≤ γ (k + 2) + τ₂)
  rwa [min_self, show 2 * 10 ^ 60 / L / 2 = 10 ^ 60 / L by ring] at hR


/-- Intervals of length `2R` around a finite set of points cover a set of measure
`≤ |F| · 2R`. -/
theorem volume_le_of_cover_finset {S : Set ℝ} {F : Finset ℂ} {R : ℝ}
    (hcover : S ⊆ ⋃ z ∈ F, Icc (z.re - R) (z.re + R)) :
    volume S ≤ ENNReal.ofReal (F.card * (2 * R)) := by
  refine (measure_mono hcover).trans ((measure_biUnion_finset_le _ _).trans (le_of_eq ?_))
  have e : ∀ z : ℂ, volume (Icc (z.re - R) (z.re + R)) = ENNReal.ofReal (2 * R) := by
    intro z; rw [Real.volume_Icc]; congr 1; ring
  rw [Finset.sum_congr rfl fun z _ => e z, Finset.sum_const, nsmul_eq_mul,
    ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]

/-- The extended bad set at the critical constants has measure `≤ T/10¹⁸`. -/
theorem volume_criticalBadSetExt_le_critical {T x : ℝ} (hT1 : 1 ≤ T)
    (hL : 10 ^ 25 ≤ Real.log T) (hx1 : 1 < x)
    (hlen : (T - 1 / 2) - (3 * T ^ (1 / 2 : ℝ) + 1 / 2) +
      8 * selbergPolyLength x * (1 + Real.log (selbergPolyLength x)) ≤ 2 * T) :
    volume (criticalBadSetExt x (10 ^ 13 / Real.log T) (32 * 10 ^ 13 / Real.log T)
      ((Real.log T / 2 - 1) / 80) (3 * T ^ (1 / 2 : ℝ) + 1 / 2) (T - 1 / 2)) ≤
      ENNReal.ofReal (T / 10 ^ 18) := by
  set L := Real.log T with hLdef
  have hL0 : 0 < L := lt_of_lt_of_le (by norm_num) hL
  set τ₁ : ℝ := 10 ^ 13 / L with hτ₁
  set τ₂ : ℝ := 32 * 10 ^ 13 / L with hτ₂
  set Θ : ℝ := (L / 2 - 1) / 80 with hΘ
  set A := 3 * T ^ (1 / 2 : ℝ) + 1 / 2 with hA
  set B := T - 1 / 2 with hB
  have hs := crit_rpow_half_ge hT1 hL
  have hsq : T ^ (1 / 2 : ℝ) * T ^ (1 / 2 : ℝ) = T := by
    rw [← Real.rpow_add (by linarith)]; norm_num
  have hAB : A ≤ B := by rw [hA, hB]; nlinarith
  have hτ₁0 : 0 < τ₁ := by positivity
  have hτ₁₂ : τ₁ ≤ τ₂ := by rw [hτ₁, hτ₂]; gcongr; norm_num
  have hτ₂1 : τ₂ ≤ 1 := by rw [hτ₂, div_le_one hL0]; linarith
  have hΘ0 : 0 < Θ := by rw [hΘ]; nlinarith
  have hΘL : L / 200 ≤ Θ := by rw [hΘ]; nlinarith
  set len := B - A + 8 * selbergPolyLength x * (1 + Real.log (selbergPolyLength x)) with hlendef
  refine (volume_criticalBadSetExt_le hx1 hτ₁0 hτ₁₂ hτ₂1 hΘ0 hAB).trans
    (ENNReal.ofReal_le_ofReal ?_)
  have hlen0 : 0 ≤ len := by
    have h1 := Real.log_natCast_nonneg (selbergPolyLength x)
    have h2 : (0 : ℝ) ≤ selbergPolyLength x := Nat.cast_nonneg _
    rw [hlendef]; nlinarith
  have hτΘ : 10 ^ 13 / 200 ≤ τ₁ * Θ := by
    have : τ₁ * (L / 200) = 10 ^ 13 / 200 := by rw [hτ₁]; field_simp
    rw [← this]; exact mul_le_mul_of_nonneg_left hΘL hτ₁0.le
  have e1 : 38 * (len * (5 / τ₁ ^ 2) / Θ ^ 2) = 190 * len / (τ₁ * Θ) ^ 2 := by field_simp; ring
  rw [e1]
  have h3 : 190 * len / (τ₁ * Θ) ^ 2 ≤ 190 * len / (10 ^ 13 / 200) ^ 2 := by gcongr
  have h4 : 190 * len / (10 ^ 13 / 200) ^ 2 = 190 * 40000 * len / 10 ^ 26 := by
    field_simp; ring
  have hlenT : len ≤ 2 * T := hlen
  rw [h4] at h3
  have : 190 * 40000 * len / 10 ^ 26 ≤ T / 10 ^ 18 := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]; nlinarith
  linarith

/-- The final count arithmetic. -/
theorem card_ge_of_volume_bounds {T L R : ℝ} {n : ℕ} (hT : 0 < T) (hL : 0 < L) (hR0 : 0 < R)
    (hR : R ≤ 3 * 10 ^ 60 / L) (h : T / 10 ^ 17 < n * (2 * R) + T / 10 ^ 18) :
    T * L / 10 ^ 79 ≤ n := by
  have hc : T * L / 10 ^ 79 * (2 * R) ≤ T / 10 ^ 17 - T / 10 ^ 18 := by
    have h1 : T * L / 10 ^ 79 * (2 * R) ≤ T * L / 10 ^ 79 * (2 * (3 * 10 ^ 60 / L)) := by
      gcongr
    have h2 : T * L / 10 ^ 79 * (2 * (3 * 10 ^ 60 / L)) = 6 * T / 10 ^ 19 := by
      field_simp; ring
    rw [h2] at h1
    have : 6 * T / 10 ^ 19 ≤ T / 10 ^ 17 - T / 10 ^ 18 := by
      rw [div_sub_div _ _ (by positivity) (by positivity), div_le_div_iff₀ (by positivity)
        (by positivity)]
      nlinarith
    linarith
  by_contra hlt
  push Not at hlt
  have : (n : ℝ) * (2 * R) < T * L / 10 ^ 79 * (2 * R) :=
    mul_lt_mul_of_pos_right hlt (by positivity)
  linarith

/-- **Critical resonances have positive density.** -/
theorem eventually_card_critical_resonances_ge {E : ℂ → ℂ} (hE : StrictLowerPolyaClass E)
    (hrep : ∀ t : ℝ, Xi t = (E t).re) (hne : ∀ t : ℝ, E t ≠ 0) :
    ∀ᶠ T : ℝ in atTop, ∀ F : Finset ℂ,
      (∀ z : ℂ, E z = 0 → 3 * T ^ (1 / 2 : ℝ) - 1 ≤ z.re → z.re ≤ T + 1 →
        -(2 * 10 ^ 60 / Real.log T) ≤ z.im → z.im ≤ 0 → z ∈ F) →
      T * Real.log T / 10 ^ 79 ≤ F.card := by
  have hRH := riemannHypothesis_of_strictLowerPolya_realization hE hrep
  have hzero : ∀ q : XiZeroCopy, (q.1 : ℂ).re = 1 / 2 := fun q =>
    riemannHypothesis_iff_xi_zero_re_eq_half.mp hRH _ (xi_xiZeroCopy_eq_zero q)
  filter_upwards [eventually_volume_nonRigidHeights_gt hRH,
    Real.tendsto_log_atTop.eventually_ge_atTop (10 ^ 25), eventually_ge_atTop (2 : ℝ),
    eventually_narrowMass_bound, eventually_lorentzMassW_le, eventually_selbergLength_le,
    Real.tendsto_log_atTop.eventually_ge_atTop (10 ^ 61)]
    with T hN hL hT2 hV hW hlen hL61 F hF
  have hT1 : 1 ≤ T := by linarith
  have hT0 : 0 < T := by linarith
  have hL0 : 0 < Real.log T := lt_of_lt_of_le (by norm_num) hL
  have hx1 : 1 < T ^ (1 / 20 : ℝ) := Real.one_lt_rpow (by linarith) (by norm_num)
  have hlx : Real.log (T ^ (1 / 20 : ℝ)) = Real.log T / 20 := by rw [Real.log_rpow hT0]; ring
  have hV' := hV fun q _ _ => hzero q
  set R := 17 * (32 * 10 ^ 13 / Real.log T) + 2 * 10 ^ 60 / Real.log T with hR
  have hRle : R ≤ 3 * 10 ^ 60 / Real.log T := by
    rw [hR]
    have : 17 * (32 * 10 ^ 13 / Real.log T) ≤ 10 ^ 60 / Real.log T := by
      rw [mul_div_assoc']
      exact div_le_div_of_nonneg_right (by norm_num) hL0.le
    have e : 3 * 10 ^ 60 / Real.log T = 10 ^ 60 / Real.log T + 2 * 10 ^ 60 / Real.log T := by
      ring
    linarith
  have hR1 : R ≤ 1 / 2 := by
    refine hRle.trans ?_
    rw [div_le_iff₀ hL0]
    nlinarith
  have hcover : (Icc (3 * T ^ (1 / 2 : ℝ) + 1 / 2) (T - 1 / 2) ∩
      nonRigidHeights (10 ^ 60 / Real.log T) (32 * 10 ^ 13 / Real.log T)) \
        criticalBadSetExt (T ^ (1 / 20 : ℝ)) (10 ^ 13 / Real.log T) (32 * 10 ^ 13 / Real.log T)
          ((Real.log T / 2 - 1) / 80) (3 * T ^ (1 / 2 : ℝ) + 1 / 2) (T - 1 / 2) ⊆
      ⋃ z ∈ F, Icc (z.re - R) (z.re + R) := by
    rintro t ⟨⟨htI, k, hk, hnr⟩, htB⟩
    have hgrid := exists_ordinate_near_gridExt hT1 hL hlx htI.1 htI.2 hV' hW htB
    obtain ⟨z, hz, hzre, hzim1, hzim2⟩ :=
      exists_resonance_near_of_not_rigidAt hE hrep hne hL hgrid hk hnr
    rw [abs_le] at hzre
    have hzF : z ∈ F := hF z hz (by linarith [htI.1]) (by linarith [htI.2]) hzim1 hzim2
    rw [Set.mem_iUnion₂]
    exact ⟨z, hzF, by constructor <;> linarith⟩
  have hvolS := volume_le_of_cover_finset hcover
  have hvolB := volume_criticalBadSetExt_le_critical hT1 hL hx1 hlen
  have hNle := (measure_mono (μ := volume) (Set.subset_sdiff_union
    (Icc (3 * T ^ (1 / 2 : ℝ) + 1 / 2) (T - 1 / 2) ∩
      nonRigidHeights (10 ^ 60 / Real.log T) (32 * 10 ^ 13 / Real.log T))
    (criticalBadSetExt (T ^ (1 / 20 : ℝ)) (10 ^ 13 / Real.log T) (32 * 10 ^ 13 / Real.log T)
      ((Real.log T / 2 - 1) / 80) (3 * T ^ (1 / 2 : ℝ) + 1 / 2) (T - 1 / 2)))).trans
    (measure_union_le _ _)
  have htot := hN.trans_le (hNle.trans (add_le_add hvolS hvolB))
  rw [← ENNReal.ofReal_add (by positivity) (by positivity)] at htot
  exact card_ge_of_volume_bounds hT0 hL0 (by positivity) hRle
    ((ENNReal.ofReal_lt_ofReal_iff (by positivity)).mp htot)

end RHTower
