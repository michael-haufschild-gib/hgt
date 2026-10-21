import GaloisForLFunctions.SquareRootThreshold.ZetaCoherentCoresAddUp

/-!
# Near-top zeros of `ζ` are visible below an explicit height

(docstring to be completed)
-/

open MeasureTheory Complex Set Filter Topology
open scoped Real ComplexConjugate

noncomputable section

namespace GaloisForLFunctions.SquareRootThreshold

open Zeta23 _root_.RHTower

/-- The relative perturbation `τ = (1 + (4κ₀/V + ρ) 2(P + 1)V/(Gκ₀))^P − 1` of the eliminated factors
over a core of radius `≤ ρ` behind a gap `G`. -/
def coreFactorPerturbation (P : ℕ) (κ₀ V ρ G : ℝ) : ℝ :=
  (1 + (4 * κ₀ / V + ρ) * (2 * (P + 1) * V) / (G * κ₀)) ^ P - 1

/-- **The eliminated core keeps the record.** Let the loose members `y ∈ S_L` satisfy
`|x_y² − θ²| ≥ ρ₁ε` (`x_z = z − s`, `θ = z* − s ≥ 0` real), let the core `C ∋ z*` have radius `ρ₀`
with `ρ₀(2θ + ρ₀) ≤ t₀ρ₁ε`, `(1 + t₀)^{|S_L|} − 1 ≤ τ`, `ρ₀V ≤ ρV ≤ 1`, be coherent with the record
and carry mass `((1 + τ)2ρV + τ) Σ_C |D_c| ≤ |D*|/2`. Then
`|Σ_C D_c Π_{S_L}(x_y² − x_c²) K_m(x_c)| ≥ |D*| (ρ₁ε)^{|S_L|} K_m(θ)/2`. -/
theorem eliminated_core_ge {SL C : Finset ℂ} {z₁ s : ℂ} (hz₁C : z₁ ∈ C) (D : ℂ → ℂ) (m : ℕ)
    {V θ ρ₀ ρ₁ ε t₀ τ ρV : ℝ} (hV : 0 < V) (hθs : z₁ - s = (θ : ℂ)) (hθ : 0 ≤ θ)
    (hρ₀ : 0 ≤ ρ₀) (hρ₁ε : 0 < ρ₁ * ε)
    (hloose : ∀ y ∈ SL, ρ₁ * ε ≤ ‖(y - s) ^ 2 - (z₁ - s) ^ 2‖)
    (hcore : ∀ c ∈ C, ‖c - z₁‖ ≤ ρ₀) (hgap : ρ₀ * (2 * θ + ρ₀) ≤ t₀ * (ρ₁ * ε))
    (hτ : (1 + t₀) ^ SL.card - 1 ≤ τ) (hρV : ρ₀ * V ≤ ρV) (hρV1 : ρV ≤ 1)
    (hcoh : ∀ c ∈ C, 0 ≤ (D c * conj (D z₁)).re)
    (hmass : ((1 + τ) * (2 * ρV) + τ) * ∑ c ∈ C, ‖D c‖ ≤ ‖D z₁‖ / 2) :
    ‖D z₁‖ * (ρ₁ * ε) ^ SL.card * ‖fejerPowWin m V (θ : ℂ)‖ / 2 ≤
      ‖∑ c ∈ C, D c * (∏ y ∈ SL, ((y - s) ^ 2 - (c - s) ^ 2)) * fejerPowWin m V (c - s)‖ := by
  classical
  have ht₀ : 0 ≤ t₀ := by
    by_contra h
    push Not at h
    have h1 := mul_neg_of_neg_of_pos h hρ₁ε
    have h2 : 0 ≤ ρ₀ * (2 * θ + ρ₀) := by positivity
    linarith only [h1, h2, hgap]
  have hpow : 1 ≤ (1 + t₀) ^ SL.card := one_le_pow₀ (by linarith only [ht₀])
  have hτ0 : 0 ≤ τ := by linarith only [hpow, hτ]
  set F : ℂ → ℂ := fun c => ∏ y ∈ SL, ((y - s) ^ 2 - (c - s) ^ 2) with hFdef
  have hF₁low : (ρ₁ * ε) ^ SL.card ≤ ‖F z₁‖ := by
    calc (ρ₁ * ε) ^ SL.card = ∏ _y ∈ SL, (ρ₁ * ε) := (Finset.prod_const _).symm
      _ ≤ ∏ y ∈ SL, ‖(y - s) ^ 2 - (z₁ - s) ^ 2‖ :=
          Finset.prod_le_prod (fun _ _ => hρ₁ε.le) hloose
      _ = ‖F z₁‖ := (norm_prod _ _).symm
  have hF₁ : F z₁ ≠ 0 := norm_pos_iff.mp (lt_of_lt_of_le (pow_pos hρ₁ε _) hF₁low)
  -- over the core the eliminated factors move by the relative amount `τ`
  have hFc : ∀ c ∈ C, ‖F c - F z₁‖ ≤ τ * ‖F z₁‖ := fun c hc => by
    have h := norm_prod_sub_prod_le SL (fun y => (y - s) ^ 2 - (c - s) ^ 2)
      (fun y => (y - s) ^ 2 - (z₁ - s) ^ 2) ht₀ fun y hy => by
        have e : ((y - s) ^ 2 - (c - s) ^ 2) - ((y - s) ^ 2 - (z₁ - s) ^ 2) =
            (z₁ - c) * (2 * (θ : ℂ) + (c - z₁)) := by rw [← hθs]; ring
        rw [e, norm_mul]
        have h1 : ‖z₁ - c‖ ≤ ρ₀ := by rw [norm_sub_rev]; exact hcore c hc
        have h2 : ‖2 * (θ : ℂ) + (c - z₁)‖ ≤ 2 * θ + ρ₀ := by
          refine (norm_add_le _ _).trans ?_
          have : ‖2 * (θ : ℂ)‖ = 2 * θ := by
            rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hθ]; norm_num
          rw [this]; linarith only [hcore c hc]
        calc ‖z₁ - c‖ * ‖2 * (θ : ℂ) + (c - z₁)‖ ≤ ρ₀ * (2 * θ + ρ₀) :=
              mul_le_mul h1 h2 (norm_nonneg _) hρ₀
          _ ≤ t₀ * (ρ₁ * ε) := hgap
          _ ≤ t₀ * ‖(y - s) ^ 2 - (z₁ - s) ^ 2‖ := mul_le_mul_of_nonneg_left (hloose y hy) ht₀
    exact h.trans (mul_le_mul_of_nonneg_right hτ (norm_nonneg _))
  -- and the kernels by the relative amount `2ρV`
  obtain ⟨t, ht⟩ : ∃ t : ℝ, t = ‖fejerPowWin m V (θ : ℂ)‖ := ⟨_, rfl⟩
  rw [← ht]
  have ht0 : 0 ≤ t := by rw [ht]; exact norm_nonneg _
  have hKr : fejerPowWin m V (θ : ℂ) = (t : ℂ) := by
    rw [ht]; exact fejerPowWin_ofReal_eq_norm hV.le _ _
  have hKc : ∀ c ∈ C, ‖fejerPowWin m V (c - s) - t‖ ≤ 2 * ρV * t := fun c hc => by
    have e : (c - s) - (θ : ℂ) = c - z₁ := by rw [← hθs]; ring
    have h3 := (mul_le_mul_of_nonneg_right (hcore c hc) hV.le).trans hρV
    have hcV : ‖(c - s) - (θ : ℂ)‖ * V ≤ 1 := by rw [e]; exact h3.trans hρV1
    have h := norm_fejerPowWin_sub_ofReal_le hV.le m θ hcV
    rw [e, hKr, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ht0] at h
    have h4 : 2 * (‖c - z₁‖ * V) ≤ 2 * ρV := by linarith only [h3]
    calc ‖fejerPowWin m V (c - s) - t‖ ≤ 2 * ‖c - z₁‖ * V * t := h
      _ = 2 * (‖c - z₁‖ * V) * t := by ring
      _ ≤ 2 * ρV * t := mul_le_mul_of_nonneg_right h4 ht0
  rcases ht0.eq_or_lt with h0 | htpos
  · rw [← h0]; simp
  have hFK : ∀ c ∈ C, ‖F c * fejerPowWin m V (c - s) - F z₁ * t‖ ≤
      ((1 + τ) * (2 * ρV) + τ) * ‖F z₁‖ * t :=
    fun c hc => norm_mul_sub_mul_le ht0 hτ0 (hFc c hc) (hKc c hc)
  have hcs := norm_core_sum_ge hz₁C D F (fun c => fejerPowWin m V (c - s)) htpos hF₁ hcoh hFK hmass
  have h5 := mul_le_mul_of_nonneg_left hF₁low (mul_nonneg (norm_nonneg (D z₁)) ht0)
  calc ‖D z₁‖ * (ρ₁ * ε) ^ SL.card * t / 2 ≤ ‖F z₁‖ * t * ‖D z₁‖ / 2 := by linarith only [h5]
    _ ≤ _ := hcs

/-- `ρ₀(2κ/V + ρ₀) ≤ t₀ · Gρ₀ · κ₀/(2(P + 1)V)` for `t₀ = (4κ₀/V + ρ) 2(P + 1)V/(Gκ₀)`. -/
theorem core_gap_arith {ρ₀ ρ G κ κ₀ V P : ℝ} (hρ₀ : 0 ≤ ρ₀) (hρ₀ρ : ρ₀ ≤ ρ) (hG : 0 < G)
    (hκ₀ : 0 < κ₀) (hV : 0 < V) (hP : 0 ≤ P) (hκ : κ ≤ 2 * κ₀) :
    ρ₀ * (2 * (κ / V) + ρ₀) ≤ (4 * κ₀ / V + ρ) * (2 * (P + 1) * V) / (G * κ₀) *
      (G * ρ₀ * (κ₀ / (2 * (P + 1) * V))) := by
  have e : (4 * κ₀ / V + ρ) * (2 * (P + 1) * V) / (G * κ₀) * (G * ρ₀ * (κ₀ / (2 * (P + 1) * V))) =
      ρ₀ * (4 * κ₀ / V + ρ) := by
    have : (P + 1) ≠ 0 := by linarith only [hP]
    field_simp
  rw [e]
  refine mul_le_mul_of_nonneg_left ?_ hρ₀
  have : 2 * (κ / V) ≤ 4 * κ₀ / V := by
    rw [mul_div_assoc', div_le_div_iff_of_pos_right hV]; linarith only [hκ]
  linarith only [this, hρ₀ρ]

/-- `a ≤ b`, `X ≥ 0`, `(b/2) X ≤ B` and `2B < aX` are incompatible. -/
theorem visible_final_arith {a b Vm rn B : ℝ} (hab : a ≤ b) (hX : 0 ≤ Vm * rn)
    (hb : b / 2 * (Vm * rn) ≤ B) (hmain : 2 * B < a * Vm * rn) : False := by
  have := mul_le_mul_of_nonneg_right hab hX
  linarith

/-- **Near-top zeros are visible.** Let `½ + z₀` be a zero right of the line at height `γ₀ ≥ T_w`,
`1/V`-near the top, `Γ = recordHeightEnvelope w γ₀`, `P ≥ 80 log(180Γ)`. Let `k ≥ 1`, `κ₀ ≥ 1`,
`2κ₀/V ≤ δ₀/16`, `V ≥ π(k + P)`, `Vδ₀/8 ≥ 4π(k + P)`, the record-depth condition, `H₀ > 0` as in
`zeta_isolated_twins_cannot_hide`, and a core scale `ρ > 0` and gap `G ≥ 1` with `ρV ≤ 1`, `wρ ≤ 1`,
`8w e^{w/2} J_w ρ ≤ H₀`, `ρ ≤ δ₀/16`,
`((1 + τ)·2ρV + τ)(P + 1)·80 log(180(Γ + 1))(e^{w/2}B_w)² ≤ a_w²/(4e)` (`τ = coreFactorPerturbation`),
and for every `p ≤ P`
`2 B(p) < (ρκ₀/(2(P + 1)G^P))^p V^{2k+p+1} (δ₀/8)^{2k+1}` (`clusterCollapseBound`). Then some difference
test of the bump modulated to `γ₀` is Weil negative at a lag `v ∈ [0, V]`. -/
theorem zeta_near_top_visible {w : ℝ} (hw : 0 < w) {z₀ : ℂ}
    (hz₀ : (1 / 2 + z₀) ∈ zetaZeroConfig.carrier) (hre₀ : 0 < z₀.re)
    (hTw : nearTopHeight w ≤ z₀.im) {V : ℝ} (hV : 0 < V)
    (htop : ∀ ρ ∈ zetaZeroConfig.carrier, ρ.re - 1 / 2 ≤ z₀.re + 1 / V) {P : ℕ}
    (hP : 80 * Real.log (180 * recordHeightEnvelope w z₀.im) ≤ P)
    {κ₀ : ℝ} {k : ℕ} (hk : 1 ≤ k) (hκ₀ : 1 ≤ κ₀)
    (hV2 : 2 * Real.log (160 * Real.log (180 * recordHeightEnvelope w z₀.im) *
        (Real.exp (w / 2) * scaledBumpDecay w) ^ 2 / centerAmplitude w ^ 2) ≤ z₀.re * V)
    (hκV : 2 * κ₀ / V ≤ z₀.re / 16) (hVk : π * (k + P : ℕ) ≤ V)
    (hVr : 4 * π * (k + P : ℕ) ≤ V * (z₀.re / 8)) {H₀ : ℝ} (hH₀ : 0 < H₀)
    (hH : H₀ ^ 2 ≤ centerAmplitude w ^ 2 / (2 * Real.exp 1) /
        (40 * Real.log (180 * recordHeightEnvelope w z₀.im)) -
      (Real.exp (w / 2) * scaledBumpDecay w) ^ 2 / (1 + z₀.im) ^ 4)
    (hK : (Real.exp (w / 2) * scaledBumpDecay w) ^ 2 / (1 + z₀.im) ^ 4 ≤ H₀ ^ 2 / 16)
    {ρ G : ℝ} (hρ : 0 < ρ) (hG : 1 ≤ G) (hρV : ρ * V ≤ 1) (hρw : w * ρ ≤ 1)
    (hρL : 8 * w * Real.exp (w / 2) * bumpMass w * ρ ≤ H₀) (hρr : ρ ≤ z₀.re / 16)
    (hη : ((1 + coreFactorPerturbation P κ₀ V ρ G) * (2 * (ρ * V)) +
        coreFactorPerturbation P κ₀ V ρ G) * ((P + 1) * (80 * Real.log (180 *
          (recordHeightEnvelope w z₀.im + 1)) * (Real.exp (w / 2) * scaledBumpDecay w) ^ 2)) ≤
      centerAmplitude w ^ 2 / (2 * Real.exp 1) / 2)
    (hmain : ∀ p : ℕ, p ≤ P → 2 * clusterCollapseBound w z₀.im κ₀ k p <
      (ρ * κ₀ / (2 * (P + 1) * G ^ P)) ^ p * V ^ (2 * k + p + 1) * (z₀.re / 8) ^ (2 * k + 1)) :
    ∃ v ∈ Icc (0 : ℝ) V, (zetaZeroConfig.W (twoBump (modScaledBump w z₀.im) v (-1))
      (twoBump (modScaledBump w z₀.im) v (-1))).re < 0 := by
  by_contra hneg
  push Not at hneg
  classical
  set b := modScaledBump w z₀.im with hbdef
  set D := evenCoeff zetaZeroConfig b with hDdef
  set Γ := recordHeightEnvelope w z₀.im with hΓdef
  set r : ℝ := z₀.re / 8 with hr
  have hpos₀ : 0 < z₀.im := lt_of_lt_of_le (by unfold nearTopHeight; positivity) hTw
  have hstrip := zetaZeroConfig.strip _ hz₀
  have hre₀1' : z₀.re ≤ 1 / 2 := by
    have e : (1 / 2 + z₀).re = 1 / 2 + z₀.re := by simp
    linarith [hstrip.2]
  have hr0 : 0 < r := by rw [hr]; positivity
  have hr1 : r ≤ 1 := by rw [hr]; linarith [hre₀1']
  have hmem : ∀ x : ℂ, D x ≠ 0 → (1 / 2 + x) ∈ zetaZeroConfig.carrier := fun x hx => by
    rcases mem_of_evenCoeff_ne_zero hx with h | h
    · exact h
    · have := conj_mem_zetaZeroConfig h
      have e : conj (1 / 2 + conj x) = 1 / 2 + x := by apply Complex.ext <;> simp
      rwa [e] at this
  have htop' : ∀ z, D z ≠ 0 → z.re ≤ z₀.re + 1 / V := fun z hz => by
    have := htop _ (hmem z hz)
    have e : (1 / 2 + z).re = 1 / 2 + z.re := by simp
    linarith
  obtain ⟨z₁, hz₁, hre₁, hlow, hup, hD₁, hrec⟩ :=
    near_top_record_facts hw hV hz₀ hre₀ hTw htop' hV2
  have hκ₀0 : 0 < κ₀ := by linarith
  have h2κ : 2 * κ₀ / V ≤ r / 2 := by rw [hr]; linarith
  -- the companions of the record, independent of the depth
  set R₀ : ℝ := r + 2 * κ₀ / V with hR₀
  set T : Finset ℂ := (finite_evenCoeff_ball zetaZeroConfig b z₁ R₀).toFinset.erase z₁ with hT
  have hTbox : ∀ z ∈ T, (1 / 2 + z) ∈ zetaZeroConfig.carrier ∧ |(1 / 2 + z).im| ≤ Γ + 1 ∧
      1 / 2 + z₀.re / 4 ≤ (1 / 2 + z).re := fun z hz => by
    rw [hT, Finset.mem_erase, Set.Finite.mem_toFinset] at hz
    obtain ⟨-, hDz, hzr⟩ := hz
    refine ⟨hmem z hDz, ?_, ?_⟩
    · have e : (1 / 2 + z).im = z.im := by simp
      rw [e]
      have := Complex.abs_im_le_norm (z - z₁)
      rw [Complex.sub_im] at this
      have := abs_sub_abs_le_abs_sub z.im z₁.im
      have : R₀ ≤ 1 := by rw [hR₀]; linarith
      linarith
    · have e : (1 / 2 + z).re = 1 / 2 + z.re := by simp
      rw [e]
      have := Complex.abs_re_le_norm (z - z₁)
      rw [Complex.sub_re] at this
      have := neg_abs_le (z.re - z₁.re)
      have : R₀ ≤ z₀.re / 4 := by rw [hR₀, hr]; linarith
      linarith
  have hTcard : T.card ≤ P := by
    have h4 : 4 ≤ |z₁.im| := four_le_abs_im_of_evenCoeff_zeta hz₁
    have hloc := card_exponent_window_le (b := b) h4 T fun z hz => by
      rw [hT, Finset.mem_erase, Set.Finite.mem_toFinset] at hz
      obtain ⟨-, hDz, hzr⟩ := hz
      refine ⟨hDz, ?_⟩
      have := Complex.abs_im_le_norm (z - z₁)
      rw [Complex.sub_im] at this
      have : R₀ ≤ 1 := by rw [hR₀]; linarith
      linarith
    have hlog : Real.log (180 * |z₁.im|) ≤ Real.log (180 * Γ) :=
      Real.log_le_log (by linarith) (by linarith)
    have : (T.card : ℝ) ≤ P := by linarith
    exact_mod_cast this
  -- a depth avoiding the mirror points of all companions
  obtain ⟨κ, hκ1, hκ2, hmirror⟩ := exists_depth_avoiding_mirrors T z₁ hTcard hκ₀0 hV
  set ε : ℝ := κ₀ / (2 * (P + 1) * V) with hε
  have hκ0 : 0 < κ := by linarith
  have hκV' : κ / V ≤ 2 * κ₀ / V := div_le_div_of_nonneg_right hκ2 hV.le
  set s : ℂ := ((z₁.re - κ / V : ℝ) : ℂ) + z₁.im * I with hs
  have hz₁s : ‖z₁ - s‖ = κ / V := by
    have : z₁ - s = ((κ / V : ℝ) : ℂ) := by apply Complex.ext <;> simp [hs]
    rw [this, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (div_pos hκ0 hV)]
  set S : Finset ℂ := (finite_evenCoeff_ball zetaZeroConfig b s r).toFinset with hS
  have hz₁S : z₁ ∈ S := by
    rw [hS, Set.Finite.mem_toFinset]; exact ⟨hz₁, by rw [hz₁s]; linarith⟩
  have hSr : ∀ z ∈ S, ‖z - s‖ ≤ r := fun z hz => by
    rw [hS, Set.Finite.mem_toFinset] at hz; exact hz.2
  have hiso : ∀ z, z ∉ S → D z ≠ 0 → r ≤ ‖z - s‖ := fun z hz hDz => by
    rw [hS, Set.Finite.mem_toFinset] at hz
    by_contra h; push Not at h; exact hz ⟨hDz, h.le⟩
  have hST : S.erase z₁ ⊆ T := fun z hz => by
    rw [Finset.mem_erase] at hz
    have hzS := hz.2
    rw [hS, Set.Finite.mem_toFinset] at hzS
    rw [hT, Finset.mem_erase, Set.Finite.mem_toFinset]
    refine ⟨hz.1, hzS.1, ?_⟩
    have h1 := norm_sub_le_norm_sub_add_norm_sub z s z₁
    rw [norm_sub_rev s z₁, hz₁s] at h1
    have := hSr z hz.2
    rw [hR₀]; linarith
  have hrσ : r ≤ z₁.re - κ / V := by rw [hr] at h2κ ⊢; linarith
  -- the empty annulus splits the companions into a core and loose members
  obtain ⟨j, hjP, hann⟩ := exists_empty_annulus T z₁ hTcard hρ hG
  obtain ⟨ρ₀, hρ₀⟩ : ∃ ρ₀ : ℝ, ρ₀ = ρ / G ^ (j + 1) := ⟨_, rfl⟩
  obtain ⟨ρ₁, hρ₁⟩ : ∃ ρ₁ : ℝ, ρ₁ = ρ / G ^ j := ⟨_, rfl⟩
  rw [← hρ₀, ← hρ₁] at hann
  have hG0 : 0 < G := by linarith only [hG]
  have hρ₀0 : 0 < ρ₀ := by rw [hρ₀]; positivity
  have hρ₀ρ : ρ₀ ≤ ρ := by rw [hρ₀]; exact div_le_self hρ.le (one_le_pow₀ hG)
  have hρ₁ρ₀ : ρ₁ = G * ρ₀ := by rw [hρ₁, hρ₀, pow_succ]; field_simp
  have hρ₁P : ρ / G ^ P ≤ ρ₁ := by
    rw [hρ₁]; exact div_le_div_of_nonneg_left hρ.le (by positivity) (pow_le_pow_right₀ hG hjP)
  obtain ⟨SL, hSL⟩ : ∃ SL : Finset ℂ, SL = (S.erase z₁).filter fun z => ρ₁ < ‖z - z₁‖ :=
    ⟨_, rfl⟩
  have hSLmem : ∀ z, z ∈ SL ↔ (z ≠ z₁ ∧ z ∈ S) ∧ ρ₁ < ‖z - z₁‖ := fun z => by
    rw [hSL, Finset.mem_filter, Finset.mem_erase]
  have hSLS : SL ⊆ S := fun z hz => ((hSLmem z).mp hz).1.2
  have hSLT : SL ⊆ T := fun z hz => hST (Finset.mem_erase.mpr ((hSLmem z).mp hz).1)
  have hpP : SL.card ≤ P := (Finset.card_le_card hSLT).trans hTcard
  have hpP' : ((k + SL.card : ℕ) : ℝ) ≤ (k + P : ℕ) := by exact_mod_cast (by omega : k + SL.card ≤ k + P)
  have hPE := zeta_partial_elimination_le (contDiff_modScaledBump_two w _)
    (modScaledBump_support hw _) hneg hz₁ hrec hκ0 hr0 hr1 hrσ hk S SL hSLS hSr hiso
    (le_trans (mul_le_mul_of_nonneg_left hpP' Real.pi_pos.le) hVk)
    (le_trans (mul_le_mul_of_nonneg_left hpP' (by positivity)) hVr)
  rw [← hs] at hPE
  have hz₁C : z₁ ∈ S.filter fun z => z ∉ SL :=
    Finset.mem_filter.mpr ⟨hz₁S, fun h => ((hSLmem z₁).mp h).1.1 rfl⟩
  have hcρ₀ : ∀ c ∈ S.filter (fun z => z ∉ SL), ‖c - z₁‖ ≤ ρ₀ := fun c hc => by
    obtain ⟨hcS, hcL⟩ := Finset.mem_filter.mp hc
    by_cases hne : c = z₁
    · rw [hne, sub_self, norm_zero]; exact hρ₀0.le
    · rcases hann c (hST (Finset.mem_erase.mpr ⟨hne, hcS⟩)) with h | h
      · exact h
      · exact absurd ((hSLmem c).mpr ⟨⟨hne, hcS⟩, h⟩) hcL
  have hcρ : ∀ c ∈ S.filter (fun z => z ∉ SL), ‖c - z₁‖ ≤ ρ := fun c hc => (hcρ₀ c hc).trans hρ₀ρ
  -- the loose members stay away from the record and from its mirror point
  have hθc : z₁ - s = ((κ / V : ℝ) : ℂ) := by apply Complex.ext <;> simp [hs]
  have hε0' : 0 < ε := by rw [hε]; positivity
  have hρ₁0 : 0 < ρ₁ := by rw [hρ₁ρ₀]; positivity
  have hbig : ∀ y ∈ SL, ρ₁ * ε ≤ ‖(y - s) ^ 2 - (z₁ - s) ^ 2‖ := fun y hy => by
    have e : (y - s) ^ 2 - (z₁ - s) ^ 2 = (y - z₁) * ((y - z₁) + ((2 * κ / V : ℝ) : ℂ)) := by
      have e1 : y - s = (y - z₁) + ((κ / V : ℝ) : ℂ) := by rw [← hθc]; ring
      rw [e1, hθc]; push_cast; ring
    rw [e, norm_mul]
    exact mul_le_mul ((hSLmem y).mp hy).2.le (hmirror y (hSLT hy)) hε0'.le (norm_nonneg _)
  -- the core is coherent with the record
  have hγ₀1 : 1 ≤ z₀.im := le_trans (by
    unfold nearTopHeight
    have : 0 ≤ 700000 * (Real.exp (w / 2) * scaledBumpDecay w) ^ 2 / centerAmplitude w ^ 2 := by
      positivity
    linarith only [this]) hTw
  have hDS : ∀ c ∈ S, D c ≠ 0 := fun c hc => by
    rw [hS, Set.Finite.mem_toFinset] at hc; exact hc.1
  have hJ0 : 0 ≤ bumpMass w := integral_nonneg fun u => abs_nonneg _
  have hcoh : ∀ c ∈ S.filter (fun z => z ∉ SL), 0 ≤ (D c * conj (D z₁)).re := fun c hc => by
    have hcS := (Finset.mem_filter.mp hc).1
    have hcz := hcρ c hc
    exact re_twin_mul_conj_nonneg hw hγ₀1 (hmem z₁ hz₁) (hmem c (hDS c hcS)) hlow
      (by linarith only [hcz, hρr, hre₀1']) hH₀ hup hD₁ hH hK
      (le_trans (mul_le_mul_of_nonneg_left hcz (mul_nonneg (by positivity) hJ0)) hρL)
      (le_trans (mul_le_mul_of_nonneg_left hcz hw.le) hρw)
  -- the mass of the core
  obtain ⟨Dm, hDm⟩ : ∃ Dm : ℝ,
      Dm = 80 * Real.log (180 * (Γ + 1)) * (Real.exp (w / 2) * scaledBumpDecay w) ^ 2 := ⟨_, rfl⟩
  rw [← hDm] at hη
  have hDc : ∀ c ∈ S.filter (fun z => z ∉ SL), ‖D c‖ ≤ Dm := fun c hc => by
    have hcS := (Finset.mem_filter.mp hc).1
    refine (norm_evenCoeff_modScaledBump_le_log hw z₀.im (hDS c hcS)).trans ?_
    have h4 := four_le_abs_im_of_evenCoeff_zeta (hDS c hcS)
    have himc : |c.im| ≤ Γ + 1 := by
      have h1 := Complex.abs_im_le_norm (c - z₁)
      rw [Complex.sub_im] at h1
      have h2 := abs_sub_abs_le_abs_sub c.im z₁.im
      have h3 := hcρ c hc
      linarith only [h1, h2, h3, hup, hρr, hre₀1']
    have h5 : Real.log (180 * |c.im|) ≤ Real.log (180 * (Γ + 1)) :=
      Real.log_le_log (by linarith only [h4]) (by linarith only [himc])
    rw [hDm]
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h5 (by norm_num)) (by positivity)
  have hCcard : (S.filter fun z => z ∉ SL).card ≤ P + 1 :=
    (Finset.card_filter_le _ _).trans (by
      rw [← Finset.card_erase_add_one hz₁S]
      exact Nat.succ_le_succ ((Finset.card_le_card hST).trans hTcard))
  have hsumD : ∑ c ∈ S.filter (fun z => z ∉ SL), ‖D c‖ ≤ (P + 1) * Dm := by
    have h := Finset.sum_le_card_nsmul _ (fun c => ‖D c‖) Dm hDc
    rw [nsmul_eq_mul] at h
    have hD0 : 0 ≤ Dm := le_trans (norm_nonneg _) (hDc z₁ hz₁C)
    have hc : ((S.filter fun z => z ∉ SL).card : ℝ) ≤ P + 1 := by exact_mod_cast hCcard
    exact h.trans (mul_le_mul_of_nonneg_right hc hD0)
  -- the perturbation over the core
  obtain ⟨t₀, ht₀⟩ : ∃ t₀ : ℝ, t₀ = (4 * κ₀ / V + ρ) * (2 * (P + 1) * V) / (G * κ₀) := ⟨_, rfl⟩
  have ht₀0 : 0 ≤ t₀ := by rw [ht₀]; positivity
  have hτ : (1 + t₀) ^ SL.card - 1 ≤ coreFactorPerturbation P κ₀ V ρ G := by
    rw [coreFactorPerturbation, ← ht₀]
    have := pow_le_pow_right₀ (by linarith only [ht₀0] : (1 : ℝ) ≤ 1 + t₀) hpP
    linarith only [this]
  have hτ0 : 0 ≤ coreFactorPerturbation P κ₀ V ρ G := by
    have := one_le_pow₀ (n := SL.card) (by linarith only [ht₀0] : (1 : ℝ) ≤ 1 + t₀)
    linarith only [this, hτ]
  have hmass : ((1 + coreFactorPerturbation P κ₀ V ρ G) * (2 * (ρ * V)) +
      coreFactorPerturbation P κ₀ V ρ G) * ∑ c ∈ S.filter (fun z => z ∉ SL), ‖D c‖ ≤
        ‖D z₁‖ / 2 := by
    have hη0 : 0 ≤ (1 + coreFactorPerturbation P κ₀ V ρ G) * (2 * (ρ * V)) +
        coreFactorPerturbation P κ₀ V ρ G := by positivity
    have h1 := mul_le_mul_of_nonneg_left hsumD hη0
    linarith only [h1, hη, hD₁]
  have hgap : ρ₀ * (2 * (κ / V) + ρ₀) ≤ t₀ * (ρ₁ * ε) := by
    rw [ht₀, hρ₁ρ₀, hε]
    exact core_gap_arith hρ₀0.le hρ₀ρ hG0 hκ₀0 hV (Nat.cast_nonneg P) hκ2
  have hθ0 : 0 < κ / V := div_pos hκ0 hV
  have hcore_ge := eliminated_core_ge hz₁C D (k + SL.card) hV hθc hθ0.le hρ₀0.le
    (mul_pos hρ₁0 hε0') hbig hcρ₀ hgap hτ (mul_le_mul_of_nonneg_right hρ₀ρ hV.le) hρV hcoh hmass
  have hcol := hcore_ge.trans hPE
  -- the arithmetic of `zeta_near_top_cluster_collapse` with `Π|y − z*|` replaced by `ρ₁^p/2`
  obtain ⟨p, hp⟩ : ∃ p : ℕ, p = SL.card := ⟨_, rfl⟩
  rw [← hp] at hcol hpP
  obtain ⟨L, hL⟩ : ∃ L : ℝ, L = Real.log (180 * (|z₁.im| + 6)) := ⟨_, rfl⟩
  obtain ⟨LΓ, hLΓ⟩ : ∃ LΓ : ℝ, LΓ = Real.log (180 * (Γ + 6)) := ⟨_, rfl⟩
  obtain ⟨Q, hQ⟩ : ∃ Q : ℝ, Q = (κ ^ 2 + 4 * π ^ 2 * ((k + p : ℕ) : ℝ) ^ 2) ^ (k + p) := ⟨_, rfl⟩
  obtain ⟨Q₂, hQ₂⟩ : ∃ Q₂ : ℝ, Q₂ = (4 * κ₀ ^ 2 + 4 * π ^ 2 * ((k + p : ℕ) : ℝ) ^ 2) ^ (k + p) :=
    ⟨_, rfl⟩
  obtain ⟨u, hu⟩ : ∃ u : ℝ, u = (2 * (k + p)).factorial * (π / V) ^ (2 * (k + p)) := ⟨_, rfl⟩
  have hu0 : 0 < u := by
    rw [hu]; exact mul_pos (Nat.cast_pos.mpr (Nat.factorial_pos _)) (pow_pos (div_pos Real.pi_pos hV) _)
  have hbase : ∀ t : ℝ, 0 < t → 0 < t ^ 2 + 4 * π ^ 2 * ((k + p : ℕ) : ℝ) ^ 2 := fun t ht =>
    add_pos_of_pos_of_nonneg (pow_pos ht 2)
      (mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg π)) (sq_nonneg _))
  have hQ0 : 0 < Q := by rw [hQ]; exact pow_pos (hbase κ hκ0) _
  have hKlow : u * (Real.exp κ - 1) * V ^ (2 * (k + p) + 1) / (κ * Q) ≤
      ‖fejerPowWin (k + p) V ((κ / V : ℝ) : ℂ)‖ := by
    refine le_trans (le_of_eq ?_) (norm_fejerPowWin_ofReal_ge hV (k + p) hθ0)
    have hVne : V ≠ 0 := hV.ne'
    have hκne : κ ≠ 0 := hκ0.ne'
    have e : (κ / V) ^ 2 + (2 * π * ((k + p : ℕ) : ℝ) / V) ^ 2 =
        (κ ^ 2 + 4 * π ^ 2 * ((k + p : ℕ) : ℝ) ^ 2) / V ^ 2 := by
      field_simp; ring
    rw [e, div_mul_cancel₀ κ hVne, hu, hQ, div_pow, div_pow, ← pow_mul V 2 (k + p), pow_succ]
    field_simp
  rw [← hu] at hcol
  have hMW := mass_le_of_record_height hw hpos₀ hlow
  rw [← hL] at hMW hcol
  have hL0 : 0 ≤ L := by
    rw [hL]; exact Real.log_nonneg (by have := abs_nonneg z₁.im; linarith only [this])
  have hLL : L ≤ LΓ := by
    rw [hL, hLΓ]
    exact Real.log_le_log (by have := abs_nonneg z₁.im; positivity) (by linarith only [hup])
  have hκ1' : 1 ≤ κ := hκ₀.trans hκ1
  have hΞ := xi_ratio_le hw hκ1' hD₁ hL0 hMW
  have hQQ : κ * Q ≤ 2 * κ₀ * Q₂ := by
    have hq : Q ≤ Q₂ := by
      rw [hQ, hQ₂]
      refine pow_le_pow_left₀ (hbase κ hκ0).le ?_ _
      have h2 : κ ^ 2 ≤ (2 * κ₀) ^ 2 := pow_le_pow_left₀ hκ0.le hκ2 2
      have e : (2 * κ₀) ^ 2 = 4 * κ₀ ^ 2 := by ring
      linarith only [h2, e]
    exact mul_le_mul hκ2 hq hQ0.le (by linarith only [hκ₀0])
  have hA0 := twinTightConstant_nonneg hw
  have hE : 0 < Real.exp κ - 1 := by linarith only [Real.add_one_lt_exp hκ0.ne', hκ0]
  have hc0 : (0 : ℝ) ≤ (8 / 3) ^ p * (4 / 3) ^ k :=
    mul_nonneg (pow_nonneg (by norm_num) _) (pow_nonneg (by norm_num) _)
  have hPr0 : 0 ≤ ρ₁ ^ p / 2 := by positivity
  have hcol' : ‖D z₁‖ * (ρ₁ ^ p / 2) * ε ^ p * ‖fejerPowWin (k + p) V ((κ / V : ℝ) : ℂ)‖ ≤
      u * ((8 / 3) ^ p * (4 / 3) ^ k *
        (4 * |2 * (lagStructure zetaZeroConfig b 0).re| + 4 * (∑' z : ℂ, ‖D z‖) +
          3840 * L * ‖D z₁‖ * Real.exp κ) / r ^ (2 * k + 1)) :=
    le_trans (le_of_eq (by rw [mul_pow]; ring)) hcol
  have hfin := cluster_log_arith (D := ‖D z₁‖) (u := u) (E := Real.exp κ - 1)
    (norm_pos_iff.mpr hz₁) hu0 hE hε0'.le hPr0 hr0 hV (mul_pos hκ0 hQ0) hcol' hKlow hΞ hc0 hQQ
    (mul_nonneg hA0 hL0) (p := p) (m := 2 * (k + p) + 1) (k := k)
  have e : ε ^ p * V ^ (2 * (k + p) + 1) = (κ₀ / (2 * (P + 1))) ^ p * V ^ (2 * k + p + 1) := by
    have hVne : V ≠ 0 := hV.ne'
    rw [hε, show 2 * (k + p) + 1 = (2 * k + p + 1) + p by ring, pow_add, div_pow, div_pow, mul_pow]
    field_simp
  have hQ₂0 : 0 ≤ Q₂ := by
    rw [hQ₂]
    have : 0 < 4 * κ₀ ^ 2 + 4 * π ^ 2 * ((k + p : ℕ) : ℝ) ^ 2 := by
      have := hbase (2 * κ₀) (by linarith only [hκ₀0])
      have e : (2 * κ₀) ^ 2 = 4 * κ₀ ^ 2 := by ring
      linarith only [this, e]
    exact (pow_pos this _).le
  have h1 : twinTightConstant w * L ≤ twinTightConstant w * LΓ := mul_le_mul_of_nonneg_left hLL hA0
  have h2 : 0 ≤ (8 / 3) ^ p * (4 / 3) ^ k * (2 * κ₀ * Q₂) :=
    mul_nonneg hc0 (mul_nonneg (by linarith only [hκ₀0]) hQ₂0)
  have hb : (ρ₁ ^ p * (κ₀ / (2 * (P + 1))) ^ p) / 2 * (V ^ (2 * k + p + 1) * r ^ (2 * k + 1)) ≤
      clusterCollapseBound w z₀.im κ₀ k p :=
    calc (ρ₁ ^ p * (κ₀ / (2 * (P + 1))) ^ p) / 2 * (V ^ (2 * k + p + 1) * r ^ (2 * k + 1))
        = ρ₁ ^ p / 2 * (ε ^ p * V ^ (2 * (k + p) + 1)) * r ^ (2 * k + 1) := by rw [e]; ring
      _ = ρ₁ ^ p / 2 * ε ^ p * V ^ (2 * (k + p) + 1) * r ^ (2 * k + 1) := by ring
      _ ≤ (8 / 3) ^ p * (4 / 3) ^ k * (2 * κ₀ * Q₂) * (twinTightConstant w * L) := hfin
      _ ≤ (8 / 3) ^ p * (4 / 3) ^ k * (2 * κ₀ * Q₂) * (twinTightConstant w * LΓ) :=
          mul_le_mul_of_nonneg_left h1 h2
      _ = clusterCollapseBound w z₀.im κ₀ k p := by
          rw [clusterCollapseBound, ← hΓdef, ← hLΓ, ← hQ₂]; ring
  -- the gap ladder bounds the loose radius from below
  have hab : (ρ * κ₀ / (2 * (P + 1) * G ^ P)) ^ p ≤ ρ₁ ^ p * (κ₀ / (2 * (P + 1))) ^ p := by
    rw [← mul_pow]
    have e2 : ρ * κ₀ / (2 * (P + 1) * G ^ P) = ρ / G ^ P * (κ₀ / (2 * (P + 1))) := by
      field_simp
    refine pow_le_pow_left₀ (by positivity) ?_ p
    rw [e2]
    exact mul_le_mul_of_nonneg_right hρ₁P (by positivity)
  exact visible_final_arith hab (by positivity) hb (hmain p hpP)

end GaloisForLFunctions.SquareRootThreshold
