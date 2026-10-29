import GaloisForLFunctions.RHTower.HeatFlowNearADeepXiZero
import GaloisForLFunctions.RHTower.DeBruijnNonrealCountAntitone
import GaloisForLFunctions.RHTower.XiCosineShiftDefectPersistence

/-!
# Deep off-line zeros are counted by the heat flow

**Theorem** (`exists_card_deep_le_mul_nonrealZeroCount`).  For `0 < δ ≤ 1/2` there is `C` such
that for all large `X`, every `0 < t ≤ δ²/(C log⁴ X)` and every finite set `F` of zero copies of `ξ`
with ordinates in `[X, 2X]` and `|β − 1/2| ≥ δ`,

  `#F ≤ C log X · N(t)`,   `N(t)` = the number of nonreal zeros of `H_t` (`nonrealZeroCount`).

**Corollary** (`polylog_deep_density_of_polynomial_nonrealZeroCount`).  If `N(t) ≤ A t^{−a}` for
small `t`, then the zeros with `|β − 1/2| ≥ δ` and ordinate in `[X, 2X]` number
`O((log X)^{4a+1})`: a polynomial bound on the de Bruijn–Newman nonreal count forces a
polylogarithmic density of the deep off-line zeros.

**Proof.**  Fix a deep zero `ρ₀`, `T = Im ρ₀`, and factor `ξ = P·g` near `c = 2 + iT`
(`exists_xi_cofactor_near_ordinate`): `M ≤ C log T` zeros with multiplicity, `‖g′/g‖ ≤ K`.
* A radius `r ∈ [δ/4, δ/2]` keeps every zero of the ball at distance `≥ d = δ/(8(M+1))` from the
  circle `|s − ρ₀| = r` (`exists_radius_avoiding`).
* On that circle `Σ m_ρ/‖s − ρ‖ ≤ M/d`, so `‖H_t − Ξ‖ < ‖Ξ‖` once
  `t ≤ 1/(1000 A²)`, `A = M/d + K + log(T + 1) + 3 ≍ log² T/δ`
  (`norm_riemannHeat_sub_XiC_lt`).  Rouché gives a zero of `H_t` within `δ/2` of the zero of `Ξ`,
  hence a nonreal one (`exists_nonreal_riemannHeat_zero_near`).
* Assigning to each copy such a zero, every fibre lies within ordinate distance `1`, so has at most
  `C log X` members (`exists_card_near_xi_zeros_le`), and distinct images are distinct nonreal
  zeros.
-/

open Complex Metric Filter Set
open GaloisForLFunctions.HTGeometry

namespace RHTower.DeBruijn

noncomputable section

/-! ## Choosing the radius -/

/-- Among the radii `δ/4 + kδ/(4(M+1))`, `0 ≤ k ≤ M+1`, one stays at distance `δ/(8(M+1))` from
every point of a set of at most `M` reals. -/
theorem exists_radius_avoiding {δ : ℝ} (hδ : 0 < δ) (D : Finset ℝ) {M : ℕ} (hD : D.card ≤ M) :
    ∃ r : ℝ, δ / 4 ≤ r ∧ r ≤ δ / 2 ∧ ∀ x ∈ D, δ / (8 * (M + 1)) ≤ |r - x| := by
  classical
  set h : ℝ := δ / (4 * (M + 1)) with hh
  set d : ℝ := δ / (8 * (M + 1)) with hd
  have hM1 : (0 : ℝ) < M + 1 := by positivity
  have hh0 : 0 < h := by positivity
  have hdh : 2 * d = h := by rw [hd, hh]; field_simp; ring
  set rad : ℕ → ℝ := fun k => δ / 4 + k * h with hrad
  set B : Finset ℕ := (Finset.range (M + 2)).filter (fun k => ∃ x ∈ D, |rad k - x| < d) with hB
  have hsub : B ⊆ D.biUnion (fun x => (Finset.range (M + 2)).filter (fun k => |rad k - x| < d)) := by
    intro k hk
    rw [hB, Finset.mem_filter] at hk
    obtain ⟨x, hx, hkx⟩ := hk.2
    exact Finset.mem_biUnion.mpr ⟨x, hx, Finset.mem_filter.mpr ⟨hk.1, hkx⟩⟩
  have hfib : ∀ x ∈ D, ((Finset.range (M + 2)).filter (fun k => |rad k - x| < d)).card ≤ 1 := by
    intro x _
    refine Finset.card_le_one.mpr fun k hk j hj => ?_
    rw [Finset.mem_filter] at hk hj
    have hkj : |rad k - rad j| < h := by
      calc |rad k - rad j| = |(rad k - x) - (rad j - x)| := by ring_nf
        _ ≤ |rad k - x| + |rad j - x| := abs_sub _ _
        _ < d + d := add_lt_add hk.2 hj.2
        _ = h := by linarith
    have hdiff : rad k - rad j = ((k : ℝ) - j) * h := by rw [hrad]; ring
    rw [hdiff, abs_mul, abs_of_pos hh0] at hkj
    have hlt : |(k : ℝ) - j| < 1 := by nlinarith
    have : (k : ℤ) = j := by
      have h1 : |((k : ℤ) - j : ℤ)| < 1 := by exact_mod_cast hlt
      have := abs_lt.mp h1
      omega
    exact_mod_cast this
  have hcardB : B.card ≤ M := by
    calc B.card ≤ (D.biUnion _).card := Finset.card_le_card hsub
      _ ≤ ∑ x ∈ D, ((Finset.range (M + 2)).filter (fun k => |rad k - x| < d)).card :=
          Finset.card_biUnion_le
      _ ≤ ∑ _x ∈ D, 1 := Finset.sum_le_sum hfib
      _ = D.card := by simp
      _ ≤ M := hD
  have hex : ∃ k ∈ Finset.range (M + 2), k ∉ B := by
    by_contra hall
    push Not at hall
    have : Finset.range (M + 2) ⊆ B := fun k hk => hall k hk
    have := Finset.card_le_card this
    rw [Finset.card_range] at this
    omega
  obtain ⟨k, hk, hkB⟩ := hex
  have hkM : (k : ℝ) ≤ M + 1 := by
    have := Finset.mem_range.mp hk
    exact_mod_cast (by omega : k ≤ M + 1)
  refine ⟨rad k, ?_, ?_, fun x hx => ?_⟩
  · have : 0 ≤ (k : ℝ) * h := by positivity
    rw [hrad]; linarith
  · have : (k : ℝ) * h ≤ (M + 1) * h := mul_le_mul_of_nonneg_right hkM hh0.le
    have hMh : ((M : ℝ) + 1) * h = δ / 4 := by rw [hh]; field_simp
    rw [hrad]; linarith
  · by_contra hlt
    push Not at hlt
    exact hkB (Finset.mem_filter.mpr ⟨hk, x, hx, hlt⟩)

/-! ## One deep zero -/

theorem half_add_I_mul_spectral (ρ : ℂ) : 1 / 2 + I * ((ρ - 1 / 2) * (-I)) = ρ := by
  ring_nf; rw [I_sq]; ring

/-- **A nonreal zero of `H_t` near a deep zero of `ξ`.**  With the cofactor data of
`exists_xi_cofactor_near_ordinate` at `T = Im ρ₀`, `M = Σ m_ρ`, and
`t ≤ 1/(1000 (8M(M+1)/δ + K + log(T + 1) + 3)²)`, the heat flow `H_t` has a nonreal zero within
`δ/2` of the zero `(ρ₀ − 1/2)(−i)` of `Ξ`. -/
theorem exists_nonreal_riemannHeat_zero_near {T : ℝ} (hT : 201 ≤ T) {Z : Finset ℂ}
    {m : ℂ → ℕ} {g : ℂ → ℂ} {K : ℝ} (hK0 : 0 ≤ K) (hm1 : ∀ ρ ∈ Z, 1 ≤ m ρ)
    (hzeroZ : ∀ z ∈ ball ((2 : ℂ) + (T : ℂ) * I) 12, xi z = 0 ↔ z ∈ Z)
    (hg : AnalyticOnNhd ℂ g (ball ((2 : ℂ) + (T : ℂ) * I) 12))
    (hg0 : ∀ z ∈ ball ((2 : ℂ) + (T : ℂ) * I) 12, g z ≠ 0)
    (heq : EqOn xi (fun z => (∏ ρ ∈ Z, (z - ρ) ^ m ρ) * g z) (ball ((2 : ℂ) + (T : ℂ) * I) 12))
    (hK : ∀ s ∈ ball ((2 : ℂ) + (T : ℂ) * I) 11, ‖deriv g s / g s‖ ≤ K)
    {δ : ℝ} (hδ : 0 < δ) (hδ2 : δ ≤ 1 / 2) {ρ₀ : ℂ} (hρ₀ : xi ρ₀ = 0) (him : ρ₀.im = T)
    (hdepth : δ ≤ |ρ₀.re - 1 / 2|) {t : ℝ} (ht : 0 < t)
    (htA : t ≤ 1 / (1000 * (8 * ((∑ ρ ∈ Z, m ρ : ℕ) : ℝ) * (((∑ ρ ∈ Z, m ρ : ℕ) : ℝ) + 1) / δ
      + K + Real.log (T + 1) + 3) ^ 2)) :
    ∃ w : ℂ, ‖w - (ρ₀ - 1 / 2) * (-I)‖ < δ / 2 ∧ riemannHeat t w = 0 ∧ w.im ≠ 0 := by
  classical
  set c : ℂ := (2 : ℂ) + (T : ℂ) * I with hcdef
  set ζ : ℂ := (ρ₀ - 1 / 2) * (-I) with hζ
  set M : ℕ := ∑ ρ ∈ Z, m ρ with hMdef
  set d : ℝ := δ / (8 * (M + 1)) with hd
  have hd0 : 0 < d := by positivity
  have hσζ : 1 / 2 + I * ζ = ρ₀ := half_add_I_mul_spectral ρ₀
  have hXiζ : XiC ζ = 0 := by rw [XiC_eq_xi, hσζ, hρ₀]
  have hre1 : ρ₀.re < 1 := by
    by_contra h
    exact xi_ne_zero_of_one_le_re (not_lt.mp h) hρ₀
  have hre0 : 0 < ρ₀.re := by
    by_contra h
    have h1 : xi (1 - ρ₀) = 0 := by rw [xi_one_sub, hρ₀]
    exact xi_ne_zero_of_one_le_re (by simp only [Complex.sub_re, Complex.one_re]; linarith) h1
  have hρc : ‖ρ₀ - c‖ < 2 := by
    have : ρ₀ - c = ((ρ₀.re - 2 : ℝ) : ℂ) := by
      apply Complex.ext <;> simp [hcdef, him]
    rw [this, Complex.norm_real, Real.norm_eq_abs, abs_of_neg (by linarith)]
    linarith
  have hcardZ : Z.card ≤ M := by
    rw [hMdef, Finset.card_eq_sum_ones]
    exact Finset.sum_le_sum hm1
  obtain ⟨r, hr1, hr2, hrD⟩ := exists_radius_avoiding hδ (Z.image fun ρ => ‖ρ - ρ₀‖)
    (Finset.card_image_le.trans hcardZ)
  have hr0 : 0 < r := by linarith
  have hr4 : r ≤ 1 / 4 := by linarith
  -- the comparison on the circle
  have hbd : ∀ z ∈ sphere ζ r, ‖riemannHeat t z - XiC z‖ < ‖XiC z‖ := by
    intro z hz
    have hzζ : ‖z - ζ‖ = r := by simpa [dist_eq_norm] using hz
    set sz : ℂ := 1 / 2 + I * z with hsz
    have hszρ : ‖sz - ρ₀‖ = r := by rw [← hσζ, norm_half_add_I_mul_sub, hzζ]
    have hdist : ∀ ρ ∈ Z, d ≤ ‖sz - ρ‖ := by
      intro ρ hρ
      have h1 := hrD _ (Finset.mem_image_of_mem _ hρ)
      have h2 := abs_norm_sub_norm_le (sz - ρ₀) (ρ - ρ₀)
      rw [show sz - ρ₀ - (ρ - ρ₀) = sz - ρ by ring, hszρ] at h2
      linarith
    have hZ : ∀ ρ ∈ Z, sz ≠ ρ := fun ρ hρ heq' => by
      have := hdist ρ hρ; rw [heq', sub_self, norm_zero] at this; linarith
    have hS : ∑ ρ ∈ Z, (m ρ : ℝ) / ‖sz - ρ‖ ≤ (M : ℝ) / d := by
      calc ∑ ρ ∈ Z, (m ρ : ℝ) / ‖sz - ρ‖ ≤ ∑ ρ ∈ Z, (m ρ : ℝ) / d :=
            Finset.sum_le_sum fun ρ hρ =>
              div_le_div_of_nonneg_left (Nat.cast_nonneg _) hd0 (hdist ρ hρ)
        _ = (M : ℝ) / d := by rw [← Finset.sum_div, hMdef]; push_cast; rfl
    have hMd : (M : ℝ) / d = 8 * (M : ℝ) * ((M : ℝ) + 1) / δ := by
      rw [hd]; field_simp
    have hzc : sz ∈ ball c (5 / 2) := by
      rw [mem_ball, dist_eq_norm]
      calc ‖sz - c‖ ≤ ‖sz - ρ₀‖ + ‖ρ₀ - c‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
        _ < 5 / 2 := by rw [hszρ]; linarith
    have hζre : ζ.re = T := by rw [hζ]; simp [him]
    have hszim : sz.im = z.re := by rw [hsz]; simp
    have hzre : |z.re - T| ≤ r := by
      have := Complex.abs_re_le_norm (z - ζ)
      rw [Complex.sub_re, hζre, hzζ] at this
      exact this
    have hX : 200 ≤ sz.im := by rw [hszim]; linarith [(abs_le.mp hzre).1]
    have hXT : sz.im ≤ T + 1 := by rw [hszim]; linarith [(abs_le.mp hzre).2]
    have hlog : Real.log sz.im ≤ Real.log (T + 1) := Real.log_le_log (by linarith) hXT
    have hlog0 : 0 ≤ Real.log sz.im := Real.log_nonneg (by linarith)
    have hS0 : 0 ≤ ∑ ρ ∈ Z, (m ρ : ℝ) / ‖sz - ρ‖ := Finset.sum_nonneg fun _ _ => by positivity
    have hAz : ∑ ρ ∈ Z, (m ρ : ℝ) / ‖sz - ρ‖ + K + Real.log sz.im + 3
        ≤ 8 * (M : ℝ) * ((M : ℝ) + 1) / δ + K + Real.log (T + 1) + 3 := by
      rw [← hMd]; linarith
    have hAz1 : 1 ≤ ∑ ρ ∈ Z, (m ρ : ℝ) / ‖sz - ρ‖ + K + Real.log sz.im + 3 := by linarith
    have htz : t ≤ 1 / (1000 * (∑ ρ ∈ Z, (m ρ : ℝ) / ‖sz - ρ‖ + K + Real.log sz.im + 3) ^ 2) := by
      refine htA.trans ?_
      have hsq : (∑ ρ ∈ Z, (m ρ : ℝ) / ‖sz - ρ‖ + K + Real.log sz.im + 3) ^ 2
          ≤ (8 * (M : ℝ) * ((M : ℝ) + 1) / δ + K + Real.log (T + 1) + 3) ^ 2 :=
        pow_le_pow_left₀ (by linarith) hAz 2
      have hpos : 0 < 1000 * (∑ ρ ∈ Z, (m ρ : ℝ) / ‖sz - ρ‖ + K + Real.log sz.im + 3) ^ 2 := by
        positivity
      exact one_div_le_one_div_of_le hpos (by linarith)
    exact norm_riemannHeat_sub_XiC_lt rfl (hg.mono (ball_subset_ball (by norm_num)))
      (fun z hz => hg0 z (ball_subset_ball (by norm_num) hz))
      (heq.mono (ball_subset_ball (by norm_num))) hK hK0
      (fun s hs h0 => (hzeroZ s (ball_subset_ball (by norm_num) hs)).mp h0) hzc hZ hX ht htz
  obtain ⟨w, hw, hw0⟩ := exists_zero_mem_ball_of_norm_sub_lt XiC_differentiable
    (differentiable_riemannHeat ht.le) hr0 hbd (mem_ball_self hr0) hXiζ
  have hwζ : ‖w - ζ‖ < r := by simpa [dist_eq_norm] using hw
  refine ⟨w, by linarith, hw0, fun him0 => ?_⟩
  have hζim : ζ.im = -(ρ₀.re - 1 / 2) := by rw [hζ]; simp
  have h1 := Complex.abs_im_le_norm (w - ζ)
  rw [Complex.sub_im, him0, hζim] at h1
  have : |(0 : ℝ) - -(ρ₀.re - 1 / 2)| = |ρ₀.re - 1 / 2| := by rw [zero_sub, neg_neg]
  rw [this] at h1
  linarith

/-! ## Counting -/

/-- The size of the comparison exponent: `8M(M+1)/δ + K + log(T+1) + 3 ≤ C′ L²/δ`. -/
theorem comparison_exponent_le {C₀ L δ M K Λ : ℝ} (hC₀ : 0 ≤ C₀) (hL : 1 ≤ L) (hδ : 0 < δ)
    (hδ1 : δ ≤ 1) (hM0 : 0 ≤ M) (hM : M ≤ 2 * C₀ * L) (hK : K ≤ 2 * C₀ * L) (hΛ : Λ ≤ 2 * L) :
    8 * M * (M + 1) / δ + K + Λ + 3 ≤ (16 * C₀ * (2 * C₀ + 1) + 2 * C₀ + 5) * L ^ 2 / δ := by
  have hL0 : 0 ≤ L := by linarith
  have hM1 : M + 1 ≤ (2 * C₀ + 1) * L := by nlinarith
  have h8 : 8 * M * (M + 1) ≤ 16 * C₀ * (2 * C₀ + 1) * L ^ 2 := by
    have := mul_le_mul hM hM1 (by linarith) (by positivity)
    nlinarith
  have hrest : K + Λ + 3 ≤ (2 * C₀ + 5) * L ^ 2 := by nlinarith
  have hrest' : (2 * C₀ + 5) * L ^ 2 ≤ (2 * C₀ + 5) * L ^ 2 / δ := by
    rw [le_div_iff₀ hδ]
    have : 0 ≤ (2 * C₀ + 5) * L ^ 2 := by positivity
    nlinarith
  have hdiv : 8 * M * (M + 1) / δ ≤ 16 * C₀ * (2 * C₀ + 1) * L ^ 2 / δ :=
    div_le_div_of_nonneg_right h8 hδ.le
  have : (16 * C₀ * (2 * C₀ + 1) + 2 * C₀ + 5) * L ^ 2 / δ
      = 16 * C₀ * (2 * C₀ + 1) * L ^ 2 / δ + (2 * C₀ + 5) * L ^ 2 / δ := by ring
  rw [this]
  linarith

/-- Distinct nonreal zeros of `H_t` are counted by `N(t)`. -/
theorem card_le_nonrealZeroCount {t : ℝ} (ht : 0 < t) {S : Finset ℂ}
    (hS : ∀ w ∈ S, riemannHeat t w = 0 ∧ w.im ≠ 0) : S.card ≤ nonrealZeroCount t := by
  rw [nonrealZeroCount_eq ht, Finset.card_eq_sum_ones]
  calc ∑ _w ∈ S, 1 ≤ ∑ w ∈ S, zeroMult (riemannHeat t) w :=
        Finset.sum_le_sum fun w hw => one_le_zeroMult_riemannHeat ht.le (hS w hw).1
    _ ≤ _ := Finset.sum_le_sum_of_subset fun w hw => by
        rw [Set.Finite.mem_toFinset]; exact hS w hw

theorem log_le_two_log_of_le_sq {X y : ℝ} (hy : 0 < y) (hyX : y ≤ X ^ 2) :
    Real.log y ≤ 2 * Real.log X := by
  calc Real.log y ≤ Real.log (X ^ 2) := Real.log_le_log hy hyX
    _ = 2 * Real.log X := by rw [Real.log_pow]; norm_num

/-- The time threshold: if `A ≤ C′L²/δ` and `t ≤ δ²/((1000C′² + 2C₁)L⁴)` then
`t ≤ 1/(1000 A²)`. -/
theorem le_one_div_thousand_sq {A C' C₁ L δ t : ℝ} (hA0 : 0 < A) (hA : A ≤ C' * L ^ 2 / δ)
    (hC'0 : 0 < C') (hC₁ : 0 ≤ C₁) (hL : 1 ≤ L) (hδ : 0 < δ)
    (ht : t ≤ δ ^ 2 / ((1000 * C' ^ 2 + 2 * C₁) * L ^ 4)) : t ≤ 1 / (1000 * A ^ 2) := by
  refine ht.trans ?_
  have hL4 : 0 < L ^ 4 := by positivity
  have hsq : A ^ 2 ≤ (C' * L ^ 2 / δ) ^ 2 := pow_le_pow_left₀ hA0.le hA 2
  have hexp : (C' * L ^ 2 / δ) ^ 2 = C' ^ 2 * L ^ 4 / δ ^ 2 := by field_simp
  rw [hexp] at hsq
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  have h1 : 1000 * A ^ 2 * δ ^ 2 ≤ 1000 * C' ^ 2 * L ^ 4 := by
    have := mul_le_mul_of_nonneg_right hsq (sq_nonneg δ)
    rw [div_mul_cancel₀ _ (by positivity)] at this
    linarith
  have h2 : 0 ≤ 2 * C₁ * L ^ 4 := by positivity
  linarith

theorem le_sq_of_le_two_mul_add_one {X y : ℝ} (hX : 3 ≤ X) (hy : y ≤ 2 * X + 1) : y ≤ X ^ 2 := by
  nlinarith

/-- **Deep off-line zeros are counted by the heat flow.**  For `0 < δ ≤ 1/2` there is `C > 0` such
that for large `X`, `0 < t ≤ δ²/(C log⁴ X)`, and every finite set `F` of zero copies of `ξ` with
ordinates in `[X, 2X]` and `|β − 1/2| ≥ δ`: `#F ≤ C log X · N(t)`. -/
theorem exists_card_deep_le_mul_nonrealZeroCount {δ : ℝ} (hδ : 0 < δ) (hδ2 : δ ≤ 1 / 2) :
    ∃ C : ℝ, 0 < C ∧ ∃ X₀ : ℝ, ∀ X : ℝ, X₀ ≤ X → ∀ t : ℝ, 0 < t →
      t ≤ δ ^ 2 / (C * Real.log X ^ 4) →
      ∀ F : Finset XiZeroCopy, (∀ q ∈ F, X ≤ (q.1 : ℂ).im ∧ (q.1 : ℂ).im ≤ 2 * X ∧
        δ ≤ |(q.1 : ℂ).re - 1 / 2|) →
        (F.card : ℝ) ≤ C * Real.log X * nonrealZeroCount t := by
  classical
  obtain ⟨C₀, hC₀0, hA1ev⟩ := exists_xi_cofactor_near_ordinate
  obtain ⟨C₁, hC₁0, hlocev⟩ := exists_card_near_xi_zeros_le
  obtain ⟨T₀, hT₀⟩ := Filter.eventually_atTop.mp hA1ev
  obtain ⟨T₁, hT₁⟩ := Filter.eventually_atTop.mp hlocev
  set C' : ℝ := 16 * C₀ * (2 * C₀ + 1) + 2 * C₀ + 5 with hC'
  have hC'0 : 0 < C' := by positivity
  refine ⟨1000 * C' ^ 2 + 2 * C₁, by positivity, max (max T₀ (T₁ + 1)) 204, ?_⟩
  intro X hX t ht htX F hF
  have hm0 := le_max_left T₀ (T₁ + 1)
  have hm1' := le_max_right T₀ (T₁ + 1)
  have hm2 := le_max_left (max T₀ (T₁ + 1)) 204
  have hm3 := le_max_right (max T₀ (T₁ + 1)) 204
  have hX204 : 204 ≤ X := by linarith
  have hXT₀ : T₀ ≤ X := by linarith
  have hXT₁ : T₁ + 1 ≤ X := by linarith
  have hX1 : 1 ≤ X := by linarith
  have hX3 : 3 ≤ X := by linarith
  set L : ℝ := Real.log X with hLdef
  have hL1 : 1 ≤ L := by
    rw [hLdef, ← Real.log_exp 1]
    exact Real.log_le_log (Real.exp_pos 1) (by have := Real.exp_one_lt_d9; linarith)
  -- a nonreal zero of `H_t` near every copy
  have hnear : ∀ q ∈ F, ∃ w : ℂ, ‖w - ((q.1 : ℂ) - 1 / 2) * (-I)‖ < δ / 2 ∧
      riemannHeat t w = 0 ∧ w.im ≠ 0 := by
    intro q hq
    obtain ⟨hqX, hq2X, hqδ⟩ := hF q hq
    obtain ⟨Z, m, g, hZball, hm1, hzeroZ, hMbound, hg, hg0, heq, hK⟩ :=
      hT₀ (q.1 : ℂ).im (by linarith)
    have hlogT : Real.log (q.1 : ℂ).im ≤ 2 * L :=
      log_le_two_log_of_le_sq (by linarith) (le_sq_of_le_two_mul_add_one hX3 (by linarith))
    have hlogT0 : 0 ≤ Real.log (q.1 : ℂ).im := Real.log_nonneg (by linarith)
    have hlogT1 : Real.log ((q.1 : ℂ).im + 1) ≤ 2 * L :=
      log_le_two_log_of_le_sq (by linarith) (le_sq_of_le_two_mul_add_one hX3 (by linarith))
    have hlogT10 : 0 ≤ Real.log ((q.1 : ℂ).im + 1) := Real.log_nonneg (by linarith)
    have hCT : C₀ * Real.log (q.1 : ℂ).im ≤ 2 * C₀ * L := by
      have := mul_le_mul_of_nonneg_left hlogT hC₀0.le
      linarith
    have hM0 : (0 : ℝ) ≤ ((∑ ρ ∈ Z, m ρ : ℕ) : ℝ) := Nat.cast_nonneg _
    have hMle : ((∑ ρ ∈ Z, m ρ : ℕ) : ℝ) ≤ 2 * C₀ * L := hMbound.trans hCT
    have hA := comparison_exponent_le hC₀0.le hL1 hδ (by linarith) hM0 hMle hCT hlogT1
    have hpos1 : 0 ≤ 8 * ((∑ ρ ∈ Z, m ρ : ℕ) : ℝ) * (((∑ ρ ∈ Z, m ρ : ℕ) : ℝ) + 1) / δ := by
      positivity
    have hpos2 : 0 ≤ C₀ * Real.log (q.1 : ℂ).im := by positivity
    have hA0 : 0 < 8 * ((∑ ρ ∈ Z, m ρ : ℕ) : ℝ) * (((∑ ρ ∈ Z, m ρ : ℕ) : ℝ) + 1) / δ
        + C₀ * Real.log (q.1 : ℂ).im + Real.log ((q.1 : ℂ).im + 1) + 3 := by linarith
    have htX' : t ≤ δ ^ 2 / ((1000 * C' ^ 2 + 2 * C₁) * L ^ 4) := by
      rw [mul_comm (1000 * C' ^ 2 + 2 * C₁) (L ^ 4)] at htX ⊢; exact htX
    have htA := le_one_div_thousand_sq hA0 hA hC'0 hC₁0.le hL1 hδ htX'
    exact exists_nonreal_riemannHeat_zero_near (T := (q.1 : ℂ).im) (by linarith) hpos2 hm1
      hzeroZ hg hg0 heq hK hδ hδ2 (xi_eq_zero_of_mem_divisor_support q.1) rfl hqδ ht htA
  choose! W hW using hnear
  set S : Finset ℂ := F.image W with hS
  have hScard : (S.card : ℝ) ≤ nonrealZeroCount t := by
    have := card_le_nonrealZeroCount ht (S := S) fun w hw => by
      obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hw
      exact ⟨(hW q hq).2.1, (hW q hq).2.2⟩
    exact_mod_cast this
  -- the ordinate of a copy is within `1/4` of the real part of its zero of `H_t`
  have hclose : ∀ q ∈ F, |(q.1 : ℂ).im - (W q).re| ≤ 1 := by
    intro q hq
    have h1 := Complex.abs_re_le_norm (W q - ((q.1 : ℂ) - 1 / 2) * (-I))
    have hre : (W q - ((q.1 : ℂ) - 1 / 2) * (-I)).re = (W q).re - (q.1 : ℂ).im := by
      simp; ring
    rw [hre] at h1
    have h2 := (hW q hq).1
    have h3 : |(W q).re - (q.1 : ℂ).im| ≤ 1 := by linarith
    rwa [abs_sub_comm] at h3
  -- each fibre has at most `2 C₁ L` members
  have hfib : ∀ w ∈ S, ((F.filter fun q => W q = w).card : ℝ) ≤ 2 * C₁ * L := by
    intro w hw
    obtain ⟨q₀, hq₀, rfl⟩ := Finset.mem_image.mp hw
    obtain ⟨hq0X, hq02X, _⟩ := hF q₀ hq₀
    have hc0 := abs_le.mp (hclose q₀ hq₀)
    have hwre1 : X - 1 ≤ (W q₀).re := by linarith [hc0.2]
    have hwre2 : (W q₀).re ≤ 2 * X + 1 := by linarith [hc0.1]
    have hcount := hT₁ (W q₀).re (by linarith) (F.filter fun q => W q = W q₀) fun q hq => by
      obtain ⟨hqF, hqw⟩ := Finset.mem_filter.mp hq
      rw [← hqw]; exact hclose q hqF
    have hlog : Real.log (W q₀).re ≤ 2 * L :=
      log_le_two_log_of_le_sq (by linarith) (le_sq_of_le_two_mul_add_one hX3 hwre2)
    calc ((F.filter fun q => W q = W q₀).card : ℝ) ≤ C₁ * Real.log (W q₀).re := hcount
      _ ≤ C₁ * (2 * L) := mul_le_mul_of_nonneg_left hlog hC₁0.le
      _ = 2 * C₁ * L := by ring
  have hFcard : (F.card : ℝ) ≤ 2 * C₁ * L * S.card := by
    have h := Finset.card_eq_sum_card_image W F
    have : (F.card : ℝ) = ∑ w ∈ S, ((F.filter fun q => W q = w).card : ℝ) := by
      rw [hS]; exact_mod_cast h
    rw [this]
    calc ∑ w ∈ S, ((F.filter fun q => W q = w).card : ℝ) ≤ ∑ _w ∈ S, 2 * C₁ * L :=
          Finset.sum_le_sum hfib
      _ = 2 * C₁ * L * S.card := by rw [Finset.sum_const, nsmul_eq_mul]; ring
  have hN0 : (0 : ℝ) ≤ nonrealZeroCount t := Nat.cast_nonneg _
  have hCL : 0 ≤ 2 * C₁ * L := by positivity
  have hextra : 0 ≤ 1000 * C' ^ 2 * L * nonrealZeroCount t := by positivity
  calc (F.card : ℝ) ≤ 2 * C₁ * L * S.card := hFcard
    _ ≤ 2 * C₁ * L * nonrealZeroCount t := mul_le_mul_of_nonneg_left hScard hCL
    _ ≤ (1000 * C' ^ 2 + 2 * C₁) * L * nonrealZeroCount t := by linarith

/-- **Rung two forces polylogarithmic deep density.**  If the de Bruijn–Newman nonreal count grows
at most polynomially, `N(t) ≤ A t^{−a}` for `0 < t ≤ t₀`, then for every `0 < δ ≤ 1/2` the zero
copies of `ξ` with `|β − 1/2| ≥ δ` and ordinate in `[X, 2X]` number `O((log X)^{4a+1})`. -/
theorem polylog_deep_density_of_polynomial_nonrealZeroCount {A a t₀ : ℝ} (hA : 0 ≤ A)
    (ht₀ : 0 < t₀)
    (hN : ∀ t : ℝ, 0 < t → t ≤ t₀ → (nonrealZeroCount t : ℝ) ≤ A * t ^ (-a))
    {δ : ℝ} (hδ : 0 < δ) (hδ2 : δ ≤ 1 / 2) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ X₀ : ℝ, ∀ X : ℝ, X₀ ≤ X →
      ∀ F : Finset XiZeroCopy, (∀ q ∈ F, X ≤ (q.1 : ℂ).im ∧ (q.1 : ℂ).im ≤ 2 * X ∧
        δ ≤ |(q.1 : ℂ).re - 1 / 2|) →
        (F.card : ℝ) ≤ C * Real.log X ^ (4 * a + 1) := by
  obtain ⟨C, hC0, X₁, hX₁⟩ := exists_card_deep_le_mul_nonrealZeroCount hδ hδ2
  set B : ℝ := max 1 (δ ^ 2 / (C * t₀)) with hB
  refine ⟨C * A * (C / δ ^ 2) ^ a, by positivity, max (max X₁ (Real.exp B)) 1, ?_⟩
  intro X hX F hF
  have hXX₁ : X₁ ≤ X := (le_max_left _ _).trans ((le_max_left _ _).trans hX)
  have hXB : Real.exp B ≤ X := (le_max_right _ _).trans ((le_max_left _ _).trans hX)
  set L : ℝ := Real.log X with hLdef
  have hLB : B ≤ L := by
    rw [hLdef, ← Real.log_exp B]
    exact Real.log_le_log (Real.exp_pos B) hXB
  have hL1 : 1 ≤ L := (le_max_left _ _).trans hLB
  have hL0 : 0 < L := by linarith
  set t : ℝ := δ ^ 2 / (C * L ^ 4) with htdef
  have ht : 0 < t := by positivity
  have htt₀ : t ≤ t₀ := by
    have hL4 : L ≤ L ^ 4 := by
      have : 1 ≤ L ^ 3 := one_le_pow₀ hL1
      nlinarith
    have hq : δ ^ 2 / (C * t₀) ≤ L ^ 4 := ((le_max_right _ _).trans hLB).trans hL4
    rw [htdef, div_le_iff₀ (by positivity)]
    rw [div_le_iff₀ (by positivity)] at hq
    nlinarith
  have hcount := hX₁ X hXX₁ t ht le_rfl F hF
  have hNt := hN t ht htt₀
  have hrpow : t ^ (-a) = (C / δ ^ 2) ^ a * L ^ (4 * a) := by
    rw [htdef, Real.rpow_neg (by positivity), Real.div_rpow (by positivity) (by positivity),
      inv_div, Real.mul_rpow (by positivity) (by positivity),
      Real.div_rpow (by positivity) (by positivity)]
    have h4 : (L ^ 4 : ℝ) ^ a = L ^ (4 * a) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hL0.le]; norm_num
    rw [h4]
    field_simp
  calc (F.card : ℝ) ≤ C * L * nonrealZeroCount t := hcount
    _ ≤ C * L * (A * t ^ (-a)) := by gcongr
    _ = C * A * (C / δ ^ 2) ^ a * (L ^ (4 * a) * L) := by rw [hrpow]; ring
    _ = C * A * (C / δ ^ 2) ^ a * L ^ (4 * a + 1) := by
        rw [Real.rpow_add hL0, Real.rpow_one]

end

end RHTower.DeBruijn
