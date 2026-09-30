import GaloisForLFunctions.RHTower.SelbergNearLineZeroDensity
import GaloisForLFunctions.RHTower.ZetaLineLogMeanLittlewoodBudget
import GaloisForLFunctions.RHTower.XiHadamardSignDensity
import GaloisForLFunctions.RHTower.XiHorizontalSliceDensityFromMeanSquare

/-!
# Zeros right of a fixed vertical line are `o(T)`, and the Hadamard sign holds almost everywhere on it

The Littlewood count behind the Selberg-type density accepts any horizontal shift `δ`: with the
mollified mean square on `Re s = ½ + a/log U` bounded by `(1 + r_A(a))·length`, `r_A(a) → 0`,

  `2π δ · #{ρ : Re ρ ≥ ½ + a/log U + δ} ≤ (length/2) r_A(a) + K log U`

on the windows `[T₁, T₂] ⊂ [U/4, U/2]` (`exists_zeroCount_fixedShift_le`).  Choosing `a` with
`r_A(a)` small, for every `σ > ½` the zeros with `Re ρ ≥ σ` in such a window number at most
`ε (T₂ − T₁)` for all large `U` (`eventually_zeroCount_fixedSigma_le`).

On the line `Re s = σ`, the Hadamard sign `Re(ξ'/ξ)(s) ≥ 0` fails at `σ + it` only if a zero `ρ`
with `Re ρ ≥ σ` has `|Im ρ − t| < ½` (disk criterion, normalised by the functional equation), so the
failure set in `[T₁ + 1, T₂ − 1]` has measure at most `ε (T₂ − T₁)`
(`eventually_volume_hadamardFail_line_le`): **on every vertical line `Re s = σ > ½` the Hadamard-sign
receiver of RH holds at almost every height.**
-/

noncomputable section

open Complex Filter Topology Set Metric MeasureTheory

namespace RHTower

/-- The Littlewood count at one scale with a fixed shift. -/
theorem fixedShift_count_le_of_meanSquare {N : ℕ} {L a A C K₀ T₁ T₂ δ : ℝ} (hA : 0 ≤ A)
    (hK₀ : 0 ≤ K₀) (hL : 1 ≤ L) (hN2 : 2 ≤ N) (hT12 : T₁ < T₂) (hT₂L : T₂ ≤ Real.exp L)
    (hT₁0 : 0 < T₁) {count : ℝ}
    (hmain : 2 * Real.pi * (δ * count) ≤
      (T₂ - T₁) / 2 * Real.log ((T₂ - T₁) * (1 + selbergNearLineRate A a) / (T₂ - T₁)) + C +
        K₀ * (Real.log T₂ + Real.log ((N : ℝ) ^ (5 : ℕ)))) (hC : 0 ≤ C)
    (hlogN : Real.log N ≤ L / 100) :
    2 * Real.pi * (δ * count) ≤ (T₂ - T₁) / 2 * selbergNearLineRate A a + (C + 2 * K₀) * L := by
  refine hmain.trans ?_
  have hT0 : 0 < T₂ - T₁ := by linarith
  have hrate := selbergNearLineRate_nonneg hA a
  have hlog1 : Real.log ((T₂ - T₁) * (1 + selbergNearLineRate A a) / (T₂ - T₁)) ≤
      selbergNearLineRate A a := by
    rw [mul_div_cancel_left₀ _ hT0.ne']
    have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 1 + selbergNearLineRate A a by linarith)
    linarith
  have hlogT₂ : Real.log T₂ ≤ L := by
    have := Real.log_le_log (by linarith) hT₂L
    rwa [Real.log_exp] at this
  have hlogMb : Real.log ((N : ℝ) ^ (5 : ℕ)) ≤ L := by
    rw [Real.log_pow]
    push_cast
    have : 0 ≤ Real.log (N : ℝ) := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ N))
    linarith
  have h1 : (T₂ - T₁) / 2 * Real.log ((T₂ - T₁) * (1 + selbergNearLineRate A a) / (T₂ - T₁)) ≤
      (T₂ - T₁) / 2 * selbergNearLineRate A a :=
    mul_le_mul_of_nonneg_left hlog1 (by linarith)
  have h2 : C + K₀ * (Real.log T₂ + Real.log ((N : ℝ) ^ (5 : ℕ))) ≤ (C + 2 * K₀) * L := by
    have := mul_le_mul_of_nonneg_left (add_le_add hlogT₂ hlogMb) hK₀
    nlinarith
  linarith

/-- **The Littlewood count with a fixed horizontal shift.** -/
theorem exists_zeroCount_fixedShift_le :
    ∃ A K : ℝ, 0 < A ∧ 0 ≤ K ∧ ∀ δ : ℝ, 0 < δ → ∀ a : ℝ, 1 ≤ a → ∀ᶠ U in atTop,
      ∃ T₁ ∈ Ioo (U / 4) (U / 4 + 1), ∃ T₂ ∈ Ioo (U / 2 - 1) (U / 2),
        ∀ Z : Finset ℂ,
          (∀ z : ℂ, z ∈ Z ↔ z ∈ (uIcc (1 / 2 : ℝ) (15 / 2) ×ℂ uIcc T₁ T₂) ∧ riemannZeta z = 0) →
          2 * Real.pi * (δ *
            ∑ w ∈ Z.filter (fun w => 1 / 2 + a / Real.log U + δ ≤ w.re),
              ((analyticOrderAt riemannZeta w).toNat : ℝ)) ≤
            (T₂ - T₁) / 2 * selbergNearLineRate A a + K * Real.log U := by
  obtain ⟨C, K₀, hC, hK₀, hcons⟩ := exists_zetaZeroDensity_scale_le_of_mollified_meanSquare_wide
  obtain ⟨Cf, hCf, htail⟩ := exists_eventually_integral_hbMollifiedTail_rightShift_le
  refine ⟨max 400000 (3 * Cf), C + 2 * K₀, by positivity, by positivity, fun δ hδ a ha => ?_⟩
  filter_upwards [htail a (by linarith), eventually_ge_atTop (Real.exp (max 500 (2 * a + 2)))]
    with U htailU hUL₀
  have hU0 : 0 < U := lt_of_lt_of_le (Real.exp_pos _) hUL₀
  have hL := Real.log_le_log (Real.exp_pos _) hUL₀
  rw [Real.log_exp] at hL
  obtain ⟨L, hLdef⟩ : ∃ L : ℝ, L = Real.log U := ⟨_, rfl⟩
  have hUexp : U = Real.exp L := by rw [hLdef, Real.exp_log hU0]
  rw [← hLdef] at hL
  subst hUexp
  simp only [Real.log_exp] at htailU ⊢
  have hL500 : 500 ≤ L := le_trans (le_max_left _ _) hL
  have hLa : 2 * a + 2 ≤ L := le_trans (le_max_right _ _) hL
  obtain ⟨-, hHU, -, -, hU160, -⟩ := nearLine_scale_facts hL500
  have hU100 : Real.exp L ^ ((1 : ℝ) / 100) = Real.exp (L / 100) := by
    rw [← Real.exp_mul]; ring_nf
  have hU99 : Real.exp L ^ ((99 : ℝ) / 100) = Real.exp (99 / 100 * L) := by
    rw [← Real.exp_mul]; ring_nf
  have hNle := ZetaGateProductAFE.mollN_le (Real.exp_pos L).le
  have hNgt := ZetaGateProductAFE.mollN_gt (Real.exp L)
  rw [hU100] at hNle hNgt
  obtain ⟨hN2, -, -, -, -, -⟩ := nearLine_length_facts hL500 hNle hNgt
  have hlogN_le : Real.log (ZetaGateProductAFE.mollN (Real.exp L) : ℝ) ≤ L / 100 := by
    have := Real.log_le_log (by exact_mod_cast (by omega : 0 < ZetaGateProductAFE.mollN
      (Real.exp L))) hNle
    rwa [Real.log_exp] at this
  obtain ⟨T₁, hT₁, T₂, hT₂, hE1, hE2⟩ := exists_admissible_heights_hbMollifier hN2
    (A₁ := Real.exp L / 4) (B₁ := Real.exp L / 4 + 1) (A₂ := Real.exp L / 2 - 1)
    (B₂ := Real.exp L / 2) (by linarith) (by linarith) (by linarith) (by linarith)
  refine ⟨T₁, hT₁, T₂, hT₂, fun Z hZ => ?_⟩
  have hT₁₂ : T₁ ≤ T₂ := by linarith [hT₁.2, hT₂.1]
  have hT12 : T₁ < T₂ := by linarith [hT₁.2, hT₂.1]
  have hlen : Real.exp (99 / 100 * L) ≤ T₂ - T₁ := by linarith [hT₁.2, hT₂.1]
  have hf := htailU T₁ T₂ hT₁.1.le hT₁₂ hT₂.2.le
  rw [hU99] at hf
  have hMsq := integral_normSq_zetaHb_rightShift_le (by linarith) hCf hL500 hLa hNle hNgt
    (by linarith [hT₁.1]) hT₁₂ hlen hf
  have hL0 : 0 < L := by linarith
  have hσ₀a : 1 / 4 ≤ 1 / 2 + a / L := by
    have : 0 < a / L := div_pos (by linarith) hL0
    linarith
  have hσ₀b : 1 / 2 + a / L < 2 := by
    have : a / L ≤ 1 := by rw [div_le_one hL0]; linarith
    linarith
  have hmem : ∀ x ∈ Icc (1 / 2 + a / L) (15 / 2 : ℝ), x ∈ Icc (1 / 4 : ℝ) (15 / 2) :=
    fun x hx => ⟨le_trans hσ₀a hx.1, hx.2⟩
  have hNN : (1 : ℝ) ≤ ((ZetaGateProductAFE.mollN (Real.exp L) : ℕ) : ℝ) ^ (5 : ℕ) :=
    one_le_pow₀ (by exact_mod_cast (by omega : 1 ≤ ZetaGateProductAFE.mollN (Real.exp L)))
  have hmain := hcons (hbCoeff (ZetaGateProductAFE.mollN (Real.exp L)))
    (ZetaGateProductAFE.mollN (Real.exp L)) (by omega) (hbCoeff_one hN2)
    (fun n hn => norm_hbCoeff_le hN2 hn) (fun n _ => conj_hbCoeff _ n) _ hNN
    (sum_norm_hbCoeff_mul_rpow_le hN2) (1 / 2 + a / L) T₁ T₂ _
    hσ₀a hσ₀b (by linarith [hT₁.1]) hT12
    (fun x hx => (hE1 x (hmem x hx)).1) (fun x hx => (hE2 x (hmem x hx)).1)
    (fun x hx => (hE1 x (hmem x hx)).2) (fun x hx => (hE2 x (hmem x hx)).2)
    hMsq Z hZ δ hδ.le
  exact fixedShift_count_le_of_meanSquare (by positivity) hK₀.le (by linarith) hN2 hT12
    (by linarith [hT₂.2, Real.exp_pos L]) (by linarith [hT₁.1]) hmain hC.le hlogN_le

/-- Zeros of `ζ` other than the pole have multiplicity at least one. -/
theorem one_le_toNat_analyticOrderAt_riemannZeta {w : ℂ} (hw1 : w ≠ 1) (hw : riemannZeta w = 0) :
    1 ≤ (analyticOrderAt riemannZeta w).toNat := by
  have hdiff : DifferentiableOn ℂ riemannZeta {s : ℂ | s ≠ 1} :=
    fun s hs => (differentiableAt_riemannZeta hs).differentiableWithinAt
  have han : AnalyticAt ℂ riemannZeta w := hdiff.analyticAt (isOpen_ne.mem_nhds hw1)
  obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp (analyticOrderAt_riemannZeta_ne_top_of_ne_one hw1)
  have hn0 : n ≠ 0 := by
    rintro rfl
    exact (han.analyticOrderAt_eq_zero.mp (by rw [← hn]; rfl)) hw
  rw [← hn, ENat.toNat_coe]
  omega

/-- **Zeros right of a fixed vertical line are `o(T)`.** For every `σ > ½` and `ε > 0`, for all
large `U` the window `[T₁, T₂] ⊂ [U/4, U/2]` of the Littlewood count contains zeros with `Re ρ ≥ σ`
of total multiplicity at most `ε (T₂ − T₁)`. -/
theorem eventually_zeroCount_fixedSigma_le {σ ε : ℝ} (hσ : 1 / 2 < σ) (hε : 0 < ε) :
    ∀ᶠ U in atTop, ∃ T₁ ∈ Ioo (U / 4) (U / 4 + 1), ∃ T₂ ∈ Ioo (U / 2 - 1) (U / 2),
      ∀ Z : Finset ℂ,
        (∀ z : ℂ, z ∈ Z ↔ z ∈ (uIcc (1 / 2 : ℝ) (15 / 2) ×ℂ uIcc T₁ T₂) ∧ riemannZeta z = 0) →
        ∑ w ∈ Z.filter (fun w => σ ≤ w.re), ((analyticOrderAt riemannZeta w).toNat : ℝ)
          ≤ ε * (T₂ - T₁) := by
  obtain ⟨A, K, hA, hK, hcount⟩ := exists_zeroCount_fixedShift_le
  obtain ⟨δ, hδdef⟩ : ∃ δ : ℝ, δ = (σ - 1 / 2) / 2 := ⟨_, rfl⟩
  have hδ : 0 < δ := by rw [hδdef]; linarith
  have hπδε : 0 < Real.pi * δ * ε := by positivity
  obtain ⟨a₁, ha₁⟩ := eventually_atTop.mp
    ((tendsto_selbergNearLineRate A).eventually (ge_mem_nhds hπδε))
  obtain ⟨a, hadef⟩ : ∃ a : ℝ, a = max a₁ 1 := ⟨_, rfl⟩
  have ha1 : 1 ≤ a := hadef ▸ le_max_right _ _
  have hra : selbergNearLineRate A a ≤ Real.pi * δ * ε := ha₁ a (hadef ▸ le_max_left _ _)
  have hlogsmall : ∀ᶠ U in atTop,
      K * Real.log U ≤ Real.pi * δ * ε * (U / 8) ∧ a / Real.log U ≤ δ ∧ 16 ≤ U := by
    have h1 : Tendsto (fun U : ℝ => Real.log U / U) atTop (nhds 0) := by
      have := Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero
      simpa using this
    have h2 : ∀ᶠ U in atTop, Real.log U / U ≤ Real.pi * δ * ε / (8 * (K + 1)) :=
      h1.eventually (ge_mem_nhds (by positivity))
    filter_upwards [h2, Real.tendsto_log_atTop.eventually_ge_atTop (a / δ),
      eventually_ge_atTop (16 : ℝ)] with U hU hlog hU16
    have hU0 : 0 < U := by linarith
    have hlogU0 : 0 < Real.log U := Real.log_pos (by linarith)
    refine ⟨?_, ?_, hU16⟩
    · rw [div_le_div_iff₀ hU0 (by positivity)] at hU
      have hlog0 : 0 ≤ Real.log U := hlogU0.le
      nlinarith [hπδε]
    · rw [div_le_iff₀ hlogU0]
      rw [div_le_iff₀ hδ] at hlog
      linarith
  filter_upwards [hcount δ hδ a ha1, hlogsmall] with U hU hsm
  obtain ⟨hKlog, haL, hU16⟩ := hsm
  obtain ⟨T₁, hT₁, T₂, hT₂, hc⟩ := hU
  refine ⟨T₁, hT₁, T₂, hT₂, fun Z hZ => ?_⟩
  have h := hc Z hZ
  have hlen : U / 8 ≤ T₂ - T₁ := by linarith [hT₁.2, hT₂.1]
  have hsub : Z.filter (fun w => σ ≤ w.re) ⊆
      Z.filter (fun w => 1 / 2 + a / Real.log U + δ ≤ w.re) := by
    intro w hw
    rw [Finset.mem_filter] at hw ⊢
    refine ⟨hw.1, ?_⟩
    have : 1 / 2 + a / Real.log U + δ ≤ σ := by rw [hδdef] at haL ⊢; linarith
    linarith [hw.2]
  have hmono := Finset.sum_le_sum_of_subset_of_nonneg hsub
    (f := fun w => ((analyticOrderAt riemannZeta w).toNat : ℝ)) fun w _ _ => Nat.cast_nonneg _
  set S := ∑ w ∈ Z.filter (fun w => σ ≤ w.re), ((analyticOrderAt riemannZeta w).toNat : ℝ)
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun w _ => Nat.cast_nonneg _
  have hlen0 : 0 ≤ T₂ - T₁ := by linarith
  have h1 : (T₂ - T₁) / 2 * selbergNearLineRate A a ≤ (T₂ - T₁) / 2 * (Real.pi * δ * ε) :=
    mul_le_mul_of_nonneg_left hra (by linarith)
  have h2 : K * Real.log U ≤ Real.pi * δ * ε * (T₂ - T₁) :=
    hKlog.trans (mul_le_mul_of_nonneg_left hlen hπδε.le)
  have h3 : 2 * Real.pi * (δ * S) ≤ 2 * Real.pi * (δ * (ε * (T₂ - T₁))) := by
    have := mul_le_mul_of_nonneg_left hmono (show 0 ≤ 2 * Real.pi * δ by positivity)
    nlinarith [Real.pi_pos]
  have h4 : 0 < 2 * Real.pi * δ := by positivity
  have h5 : 2 * Real.pi * δ * S ≤ 2 * Real.pi * δ * (ε * (T₂ - T₁)) := by linarith
  exact le_of_mul_le_mul_left h5 h4

/-- **The Hadamard sign holds at almost every height of every vertical line `Re s = σ > ½`.**
For every `ε > 0`, for all large `U` the heights `t ∈ [T₁ + 1, T₂ − 1]` of the window at which
`ξ(σ + it) = 0` or `Re(ξ'/ξ)(σ + it) < 0` have measure at most `ε (T₂ − T₁)`. -/
theorem eventually_volume_hadamardFail_line_le {σ ε : ℝ} (hσ : 1 / 2 < σ) (hε : 0 < ε) :
    ∀ᶠ U in atTop, ∃ T₁ ∈ Ioo (U / 4) (U / 4 + 1), ∃ T₂ ∈ Ioo (U / 2 - 1) (U / 2),
      volume {t : ℝ | t ∈ Icc (T₁ + 1) (T₂ - 1) ∧
        ¬ (xi ((σ : ℂ) + (t : ℂ) * I) ≠ 0 ∧ 0 ≤ (logDeriv xi ((σ : ℂ) + (t : ℂ) * I)).re)}
        ≤ ENNReal.ofReal (ε * (T₂ - T₁)) := by
  classical
  filter_upwards [eventually_zeroCount_fixedSigma_le hσ hε, eventually_ge_atTop (100 : ℝ)]
    with U hU hU100
  obtain ⟨T₁, hT₁, T₂, hT₂, hc⟩ := hU
  refine ⟨T₁, hT₁, T₂, hT₂, ?_⟩
  have hT₁20 : 20 ≤ T₁ := by linarith [hT₁.1]
  have hT12 : T₁ < T₂ := by linarith [hT₁.2, hT₂.1]
  obtain ⟨Z, hZ⟩ := exists_zetaRectangleZeros_finset hT₁20 hT12
  set Zσ := Z.filter (fun w => σ ≤ w.re)
  have hsub : {t : ℝ | t ∈ Icc (T₁ + 1) (T₂ - 1) ∧
      ¬ (xi ((σ : ℂ) + (t : ℂ) * I) ≠ 0 ∧ 0 ≤ (logDeriv xi ((σ : ℂ) + (t : ℂ) * I)).re)} ⊆
      ⋃ ρ ∈ Zσ, Icc (ρ.im - 1 / 2) (ρ.im + 1 / 2) := by
    intro t ⟨ht, hfail⟩
    set s : ℂ := (σ : ℂ) + (t : ℂ) * I with hs
    have hsre : s.re = σ := by simp [hs]
    have hsim : s.im = t := by simp [hs]
    have ht0 : 0 ≤ t := by linarith [ht.1]
    obtain ⟨ρ, hρ, hρs⟩ := DeBruijn.exists_boxZero_of_hadamard_fail (V := t)
      (by rw [hsre]; exact hσ) (by rw [hsim]; exact ht0) (by rw [hsim]) hfail
    rw [mem_boxFinsetLe] at hρ
    obtain ⟨hρ1, hρ2, -, -, hρ0⟩ := hρ
    simp only [DeBruijn.hadamardRect, mem_preimage, Complex.measurableEquivRealProd_apply,
      mem_prod, mem_Ioc, mem_Icc] at hρs
    rw [hsre, hsim] at hρs
    obtain ⟨⟨-, hσρ⟩, hlo, hhi⟩ := hρs
    have hζ : riemannZeta ρ = 0 := by
      have hne : ρ ≠ 1 := by intro h; rw [h] at hρ2; simp at hρ2
      exact (xi_eq_zero_iff (by linarith) hne).mp hρ0
    have hZρ : ρ ∈ Z := by
      rw [hZ, Complex.mem_reProdIm, Set.uIcc_of_le (by norm_num), Set.uIcc_of_le hT12.le]
      refine ⟨⟨⟨by linarith, by linarith⟩, ⟨by linarith [ht.1], by linarith [ht.2]⟩⟩, hζ⟩
    refine mem_iUnion₂.mpr ⟨ρ, Finset.mem_filter.mpr ⟨hZρ, hσρ⟩, ?_⟩
    exact ⟨by linarith, by linarith⟩
  have hcard : (Zσ.card : ℝ) ≤ ∑ w ∈ Zσ, ((analyticOrderAt riemannZeta w).toNat : ℝ) := by
    rw [Finset.card_eq_sum_ones, Nat.cast_sum]
    refine Finset.sum_le_sum fun w hw => ?_
    obtain ⟨hwZ, hwσ⟩ := Finset.mem_filter.mp hw
    obtain ⟨hwbox, hw0⟩ := (hZ w).mp hwZ
    have hw1 : w ≠ 1 := by
      intro h
      rw [h] at hwbox
      rw [Complex.mem_reProdIm, Set.uIcc_of_le hT12.le] at hwbox
      simp at hwbox
      linarith [hwbox.2.1]
    exact_mod_cast one_le_toNat_analyticOrderAt_riemannZeta hw1 hw0
  calc volume {t : ℝ | t ∈ Icc (T₁ + 1) (T₂ - 1) ∧
        ¬ (xi ((σ : ℂ) + (t : ℂ) * I) ≠ 0 ∧ 0 ≤ (logDeriv xi ((σ : ℂ) + (t : ℂ) * I)).re)}
      ≤ volume (⋃ ρ ∈ Zσ, Icc (ρ.im - 1 / 2) (ρ.im + 1 / 2)) := measure_mono hsub
    _ ≤ ∑ ρ ∈ Zσ, volume (Icc (ρ.im - 1 / 2) (ρ.im + 1 / 2)) := measure_biUnion_finset_le _ _
    _ = ∑ ρ ∈ Zσ, ENNReal.ofReal 1 := by
        refine Finset.sum_congr rfl fun ρ _ => ?_
        rw [Real.volume_Icc]
        congr 1
        ring
    _ = ENNReal.ofReal (Zσ.card : ℝ) := by
        rw [Finset.sum_const, ENNReal.ofReal_one, nsmul_eq_mul, mul_one, ENNReal.ofReal_natCast]
    _ ≤ ENNReal.ofReal (ε * (T₂ - T₁)) := ENNReal.ofReal_le_ofReal (hcard.trans (hc Z hZ))

namespace DeBruijn

variable {f : ℂ → ℂ}

/-- **Vertical monotonicity above a height.** If every zero `ζ` of `f` has `|Im ζ| ≤ y₀` or
`(Im ζ)² ≤ (Re ζ − x)²`, then `y ↦ ‖f(x + iy)‖` is nondecreasing on `y ≥ y₀`. -/
theorem monotoneOn_norm_vertical_Ici {C : ℝ} (hC : 0 ≤ C) (hf : AnalyticOnNhd ℂ f univ)
    (hf0 : f 0 ≠ 0) (heven : ∀ z, f (-z) = f z)
    (hconj : ∀ z, f ((starRingEnd ℂ) z) = (starRingEnd ℂ) (f z))
    (hbound : ∀ z : ℂ, ‖f z‖ ≤ Real.exp (C * (1 + ‖z‖) * Real.log (2 + ‖z‖)))
    {x y₀ : ℝ} (hy₀ : 0 ≤ y₀)
    (hloc : ∀ ζ, f ζ = 0 → ζ.im ^ 2 ≤ y₀ ^ 2 ∨ ζ.im ^ 2 ≤ (ζ.re - x) ^ 2) :
    MonotoneOn (fun y : ℝ => ‖f ((x : ℂ) + I * y)‖) (Ici y₀) := by
  intro y₁ hy₁ y₂ hy₂ h12
  simp only [mem_Ici] at hy₁ hy₂
  rcases eq_or_lt_of_le h12 with h | h
  · rw [h]
  simp only
  by_cases hz1 : f ((x : ℂ) + I * y₁) = 0
  · rw [hz1, norm_zero]; exact norm_nonneg _
  have hz2 : f ((x : ℂ) + I * y₂) ≠ 0 := by
    intro h0
    rcases hloc _ h0 with hc | hc <;> simp at hc <;> nlinarith
  set z : ℂ := (x : ℂ) + I * ((y₁ + y₂) / 2 : ℝ) with hz
  set lam : ℝ := (y₂ - y₁) / 2 with hlam
  have hzm : z - lam * I = (x : ℂ) + I * y₁ := by rw [hz, hlam]; push_cast; ring
  have hzp : z + lam * I = (x : ℂ) + I * y₂ := by rw [hz, hlam]; push_cast; ring
  have hzre : z.re = x := by simp [hz]
  have hzim : z.im = (y₁ + y₂) / 2 := by simp [hz]
  have h := norm_sub_shift_le_local hC hf hf0 heven hconj hbound (lam := lam) (z := z)
    (by rw [hlam]; linarith) (by rw [hzim]; linarith)
    (fun ζ hζ => by
      rw [hzre, hzim]
      rcases hloc ζ hζ with hc | hc
      · nlinarith [sq_nonneg ((y₁ + y₂) / 2), sq_nonneg lam, sq_nonneg (ζ.re - x)]
      · nlinarith [sq_nonneg ((y₁ + y₂) / 2), sq_nonneg lam])
    (by rw [hzm]; exact hz1) (by rw [hzp]; exact hz2)
  rwa [hzm, hzp] at h

theorem monotoneOn_norm_xi_vertical_Ici {x y₀ : ℝ} (hy₀ : 0 ≤ y₀)
    (hloc : ∀ ζ, riemannHeat 0 ζ = 0 → ζ.im ^ 2 ≤ y₀ ^ 2 ∨ ζ.im ^ 2 ≤ (ζ.re - x) ^ 2) :
    MonotoneOn (fun y : ℝ => ‖riemannHeat 0 ((x : ℂ) + I * y)‖) (Ici y₀) := by
  obtain ⟨C, hC, hbound⟩ := (riemannKernel_superExp.mul_exp_sq le_rfl).exists_envelope
  exact monotoneOn_norm_vertical_Ici hC (riemannHeat_analytic le_rfl) (riemannHeat_zero_ne le_rfl)
    (riemannHeat_neg le_rfl) (riemannHeat_conj le_rfl) hbound hy₀ hloc

/-- A zero of `Ξ` obstructing monotonicity above `y₀` at `x ≥ 0` gives a zero `ρ` of `ξ` with
`Re ρ > ½ + y₀` and `|Im ρ − x| < Re ρ − ½`. -/
theorem exists_xiZero_of_obstruct {x y₀ : ℝ} (hx : 0 ≤ x) {ζ : ℂ} (hζ : riemannHeat 0 ζ = 0)
    (hy : y₀ ^ 2 < ζ.im ^ 2) (hlt : (ζ.re - x) ^ 2 < ζ.im ^ 2) (hy₀ : 0 ≤ y₀) :
    ∃ ρ : ℂ, xi ρ = 0 ∧ 1 / 2 + y₀ < ρ.re ∧ ρ.re < 1 ∧ |ρ.im - x| < ρ.re - 1 / 2 := by
  -- reflect to `Re ζ ≥ 0`
  obtain ⟨ζ₁, hζ₁, hlt₁, hy₁, hre₁⟩ : ∃ ζ₁ : ℂ, riemannHeat 0 ζ₁ = 0 ∧
      (ζ₁.re - x) ^ 2 < ζ₁.im ^ 2 ∧ y₀ ^ 2 < ζ₁.im ^ 2 ∧ 0 ≤ ζ₁.re := by
    by_cases h : 0 ≤ ζ.re
    · exact ⟨ζ, hζ, hlt, hy, h⟩
    · rw [not_le] at h
      refine ⟨-(starRingEnd ℂ ζ), ?_, ?_, ?_, ?_⟩
      · rw [riemannHeat_neg le_rfl, riemannHeat_conj le_rfl, hζ, map_zero]
      · simp only [Complex.neg_re, Complex.conj_re, Complex.neg_im, Complex.conj_im, neg_neg]
        have : (-ζ.re - x) ^ 2 ≤ (ζ.re - x) ^ 2 := by nlinarith
        linarith
      · simpa using hy
      · simp only [Complex.neg_re, Complex.conj_re]
        linarith
  -- conjugate to `Im ζ < 0`
  obtain ⟨ζ₂, hζ₂, hlt₂, hy₂, him₂⟩ : ∃ ζ₂ : ℂ, riemannHeat 0 ζ₂ = 0 ∧
      (ζ₂.re - x) ^ 2 < ζ₂.im ^ 2 ∧ y₀ ^ 2 < ζ₂.im ^ 2 ∧ ζ₂.im < 0 := by
    have hne : ζ₁.im ≠ 0 := by
      intro h
      rw [h] at hlt₁
      nlinarith [sq_nonneg (ζ₁.re - x)]
    rcases lt_or_gt_of_ne hne with h | h
    · exact ⟨ζ₁, hζ₁, hlt₁, hy₁, h⟩
    · refine ⟨starRingEnd ℂ ζ₁, ?_, ?_, ?_, ?_⟩
      · rw [riemannHeat_conj le_rfl, hζ₁, map_zero]
      · simpa using hlt₁
      · simpa using hy₁
      · simp only [Complex.conj_im]
        linarith
  have hρ : xi (1 / 2 + I * ζ₂) = 0 := by rw [← riemannHeat_zero]; exact hζ₂
  have hρre : (1 / 2 + I * ζ₂).re = 1 / 2 - ζ₂.im := by simp; ring
  have hρim : (1 / 2 + I * ζ₂).im = ζ₂.re := by simp
  have hy' : y₀ < -ζ₂.im := by nlinarith
  have h := sq_lt_sq.mp hlt₂
  rw [abs_of_neg him₂] at h
  refine ⟨1 / 2 + I * ζ₂, hρ, by rw [hρre]; linarith, xi_zero_re_lt_one hρ, ?_⟩
  rw [hρre, hρim]
  have : 1 / 2 - ζ₂.im - 1 / 2 = -ζ₂.im := by ring
  rw [this]
  exact h

end DeBruijn

/-- **Vertical monotonicity above every positive height holds at almost every abscissa.** For
`0 < y₀` and `ε > 0`, for all large `U` the abscissae `x ∈ [T₁ + 1, T₂ − 1]` of the window at which
`y ↦ |Ξ(x + iy)|` fails to be nondecreasing on `y ≥ y₀` have measure at most `ε (T₂ − T₁)`. -/
theorem eventually_volume_monotoneFail_Ici_le {y₀ ε : ℝ} (hy₀ : 0 < y₀) (hε : 0 < ε) :
    ∀ᶠ U in atTop, ∃ T₁ ∈ Ioo (U / 4) (U / 4 + 1), ∃ T₂ ∈ Ioo (U / 2 - 1) (U / 2),
      volume {x : ℝ | x ∈ Icc (T₁ + 1) (T₂ - 1) ∧
        ¬ MonotoneOn (fun y : ℝ => ‖DeBruijn.riemannHeat 0 ((x : ℂ) + I * y)‖) (Ici y₀)}
        ≤ ENNReal.ofReal (ε * (T₂ - T₁)) := by
  classical
  have hσ : (1 : ℝ) / 2 < 1 / 2 + y₀ := by linarith
  filter_upwards [eventually_zeroCount_fixedSigma_le hσ hε, eventually_ge_atTop (100 : ℝ)]
    with U hU hU100
  obtain ⟨T₁, hT₁, T₂, hT₂, hc⟩ := hU
  refine ⟨T₁, hT₁, T₂, hT₂, ?_⟩
  have hT₁20 : 20 ≤ T₁ := by linarith [hT₁.1]
  have hT12 : T₁ < T₂ := by linarith [hT₁.2, hT₂.1]
  obtain ⟨Z, hZ⟩ := exists_zetaRectangleZeros_finset hT₁20 hT12
  set Zσ := Z.filter (fun w => 1 / 2 + y₀ ≤ w.re)
  have hsub : {x : ℝ | x ∈ Icc (T₁ + 1) (T₂ - 1) ∧
      ¬ MonotoneOn (fun y : ℝ => ‖DeBruijn.riemannHeat 0 ((x : ℂ) + I * y)‖) (Ici y₀)} ⊆
      ⋃ ρ ∈ Zσ, Icc (ρ.im - 1 / 2) (ρ.im + 1 / 2) := by
    intro x ⟨hx, hfail⟩
    have hx0 : 0 ≤ x := by linarith [hx.1]
    have hbad : ∃ ζ, DeBruijn.riemannHeat 0 ζ = 0 ∧ y₀ ^ 2 < ζ.im ^ 2 ∧ (ζ.re - x) ^ 2 < ζ.im ^ 2 := by
      by_contra hno
      apply hfail
      refine DeBruijn.monotoneOn_norm_xi_vertical_Ici hy₀.le fun ζ hζ => ?_
      by_contra hc
      rw [not_or, not_le, not_le] at hc
      exact hno ⟨ζ, hζ, hc.1, hc.2⟩
    obtain ⟨ζ, hζ, hy, hlt⟩ := hbad
    obtain ⟨ρ, hρ0, hρ1, hρ2, hρx⟩ := DeBruijn.exists_xiZero_of_obstruct hx0 hζ hy hlt hy₀.le
    have hζρ : riemannZeta ρ = 0 := by
      have hne : ρ ≠ 1 := by intro h; rw [h] at hρ2; simp at hρ2
      exact (xi_eq_zero_iff (by linarith) hne).mp hρ0
    have hρx' := abs_lt.mp hρx
    have hZρ : ρ ∈ Z := by
      rw [hZ, Complex.mem_reProdIm, Set.uIcc_of_le (by norm_num), Set.uIcc_of_le hT12.le]
      refine ⟨⟨⟨by linarith, by linarith⟩, ⟨by linarith [hx.1], by linarith [hx.2]⟩⟩, hζρ⟩
    refine mem_iUnion₂.mpr ⟨ρ, Finset.mem_filter.mpr ⟨hZρ, hρ1.le⟩, ?_⟩
    exact ⟨by linarith, by linarith⟩
  have hcard : (Zσ.card : ℝ) ≤ ∑ w ∈ Zσ, ((analyticOrderAt riemannZeta w).toNat : ℝ) := by
    rw [Finset.card_eq_sum_ones, Nat.cast_sum]
    refine Finset.sum_le_sum fun w hw => ?_
    obtain ⟨hwZ, -⟩ := Finset.mem_filter.mp hw
    obtain ⟨hwbox, hw0⟩ := (hZ w).mp hwZ
    have hw1 : w ≠ 1 := by
      intro h
      rw [h] at hwbox
      rw [Complex.mem_reProdIm, Set.uIcc_of_le hT12.le] at hwbox
      simp at hwbox
      linarith [hwbox.2.1]
    exact_mod_cast one_le_toNat_analyticOrderAt_riemannZeta hw1 hw0
  calc volume {x : ℝ | x ∈ Icc (T₁ + 1) (T₂ - 1) ∧
        ¬ MonotoneOn (fun y : ℝ => ‖DeBruijn.riemannHeat 0 ((x : ℂ) + I * y)‖) (Ici y₀)}
      ≤ volume (⋃ ρ ∈ Zσ, Icc (ρ.im - 1 / 2) (ρ.im + 1 / 2)) := measure_mono hsub
    _ ≤ ∑ ρ ∈ Zσ, volume (Icc (ρ.im - 1 / 2) (ρ.im + 1 / 2)) := measure_biUnion_finset_le _ _
    _ = ∑ ρ ∈ Zσ, ENNReal.ofReal 1 := by
        refine Finset.sum_congr rfl fun ρ _ => ?_
        rw [Real.volume_Icc]
        congr 1
        ring
    _ = ENNReal.ofReal (Zσ.card : ℝ) := by
        rw [Finset.sum_const, ENNReal.ofReal_one, nsmul_eq_mul, mul_one, ENNReal.ofReal_natCast]
    _ ≤ ENNReal.ofReal (ε * (T₂ - T₁)) := ENNReal.ofReal_le_ofReal (hcard.trans (hc Z hZ))

end RHTower
