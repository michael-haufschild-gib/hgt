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
  set p := (S.erase z₁).card with hp
  have hpP : p ≤ P := (Finset.card_le_card hST).trans hTcard
  have hpP' : ((k + p : ℕ) : ℝ) ≤ (k + P : ℕ) := by exact_mod_cast (by omega : k + p ≤ k + P)
  have hrσ : r ≤ z₁.re - κ / V := by rw [hr] at h2κ ⊢; linarith
  -- the empty annulus
  obtain ⟨j, hjP, hann⟩ := exists_empty_annulus T z₁ hTcard hρ hG
  set ρ₀ : ℝ := ρ / G ^ (j + 1) with hρ₀
  set ρ₁ : ℝ := ρ / G ^ j with hρ₁
  have hG0 : 0 < G := by linarith
  have hρ₀0 : 0 < ρ₀ := by rw [hρ₀]; positivity
  have hρ₀ρ : ρ₀ ≤ ρ := by
    rw [hρ₀]; exact div_le_self hρ.le (one_le_pow₀ hG)
  have hρ₁ρ₀ : ρ₁ = G * ρ₀ := by rw [hρ₁, hρ₀, pow_succ]; field_simp
  have hρ₁P : ρ / G ^ P ≤ ρ₁ := by
    rw [hρ₁]; exact div_le_div_of_nonneg_left hρ.le (by positivity) (pow_le_pow_right₀ hG hjP)
  -- loose members and the core
  set SL := (S.erase z₁).filter fun z => ρ₁ < ‖z - z₁‖ with hSLdef
  set p := SL.card with hp
  have hSLS : SL ⊆ S := fun z hz => Finset.mem_of_mem_erase (Finset.mem_filter.mp hz).1
  have hSLT : SL ⊆ T := fun z hz => hST (Finset.mem_filter.mp hz).1
  have hpP : p ≤ P := (Finset.card_le_card hSLT).trans hTcard
  have hpP' : ((k + p : ℕ) : ℝ) ≤ (k + P : ℕ) := by exact_mod_cast (by omega : k + p ≤ k + P)
  have hrσ : r ≤ z₁.re - κ / V := by rw [hr] at h2κ ⊢; linarith
  have hPE := zeta_partial_elimination_le (contDiff_modScaledBump_two w _)
    (modScaledBump_support hw _) hneg hz₁ hrec hκ0 hr0 hr1 hrσ hk S SL hSLS hSr hiso
    (le_trans (mul_le_mul_of_nonneg_left hpP' Real.pi_pos.le) hVk)
    (le_trans (mul_le_mul_of_nonneg_left hpP' (by positivity)) hVr)
  rw [← hs, ← hp] at hPE
  set C := S.filter fun z => z ∉ SL with hC
  have hz₁C : z₁ ∈ C := Finset.mem_filter.mpr ⟨hz₁S, fun h =>
    (Finset.mem_erase.mp (Finset.mem_filter.mp h).1).1 rfl⟩
  have hcore : ∀ c ∈ C, c ≠ z₁ → ‖c - z₁‖ ≤ ρ₀ := fun c hc hne => by
    have hcS := (Finset.mem_filter.mp hc).1
    have hcT : c ∈ T := hST (Finset.mem_erase.mpr ⟨hne, hcS⟩)
    rcases hann c hcT with h | h
    · exact h
    · exact absurd (Finset.mem_filter.mpr ⟨Finset.mem_erase.mpr ⟨hne, hcS⟩, h⟩)
        (Finset.mem_filter.mp hc).2
  have hcρ : ∀ c ∈ C, ‖c - z₁‖ ≤ ρ := fun c hc => by
    by_cases hne : c = z₁
    · rw [hne, sub_self, norm_zero]; exact hρ.le
    · exact (hcore c hc hne).trans hρ₀ρ
  -- the factors of the eliminated loose members
  have hθc : z₁ - s = ((κ / V : ℝ) : ℂ) := by apply Complex.ext <;> simp [hs]
  set F : ℂ → ℂ := fun c => ∏ y ∈ SL, ((y - s) ^ 2 - (c - s) ^ 2) with hFdef
  have hfac : ∀ y : ℂ, (y - s) ^ 2 - (z₁ - s) ^ 2 = (y - z₁) * ((y - z₁) + ((2 * κ / V : ℝ) : ℂ)) :=
    fun y => by
      have e : y - s = (y - z₁) + ((κ / V : ℝ) : ℂ) := by rw [← hθc]; ring
      rw [e, hθc]; push_cast; ring
  have hε0' : 0 < ε := by rw [hε]; positivity
  have hρ₁0 : 0 < ρ₁ := by rw [hρ₁]; positivity
  have hbig : ∀ y ∈ SL, ρ₁ * ε ≤ ‖(y - s) ^ 2 - (z₁ - s) ^ 2‖ := fun y hy => by
    rw [hfac, norm_mul]
    have h1 : ρ₁ < ‖y - z₁‖ := (Finset.mem_filter.mp hy).2
    exact mul_le_mul h1.le (hmirror y (hSLT hy)) hε0'.le (norm_nonneg _)
  have hF₁ : F z₁ ≠ 0 := by
    rw [hFdef]
    exact Finset.prod_ne_zero_iff.mpr fun y hy =>
      norm_pos_iff.mp (lt_of_lt_of_le (mul_pos hρ₁0 hε0') (hbig y hy))
  have hF₁low : (ρ₁ * ε) ^ p ≤ ‖F z₁‖ := by
    rw [hFdef, norm_prod, hp, ← Finset.prod_const]
    exact Finset.prod_le_prod (fun _ _ => (mul_pos hρ₁0 hε0').le) hbig
  -- over the core the factors and the kernels move little
  set t₀ : ℝ := (4 * κ₀ / V + ρ) * (2 * (P + 1) * V) / (G * κ₀) with ht₀
  have ht₀0 : 0 ≤ t₀ := by rw [ht₀]; positivity
  have hcρ₀ : ∀ c ∈ C, ‖c - z₁‖ ≤ ρ₀ := fun c hc => by
    by_cases hne : c = z₁
    · rw [hne, sub_self, norm_zero]; exact hρ₀0.le
    · exact hcore c hc hne
  have hfacc : ∀ c ∈ C, ∀ y ∈ SL, ‖((y - s) ^ 2 - (c - s) ^ 2) - ((y - s) ^ 2 - (z₁ - s) ^ 2)‖ ≤
      t₀ * ‖(y - s) ^ 2 - (z₁ - s) ^ 2‖ := fun c hc y hy => by
    have e : ((y - s) ^ 2 - (c - s) ^ 2) - ((y - s) ^ 2 - (z₁ - s) ^ 2) =
        (z₁ - c) * ((z₁ - s) + (c - s)) := by ring
    rw [e, norm_mul]
    have h1 : ‖z₁ - c‖ ≤ ρ₀ := by rw [norm_sub_rev]; exact hcρ₀ c hc
    have h2 : ‖(z₁ - s) + (c - s)‖ ≤ 2 * κ / V + ρ₀ := by
      have e2 : (z₁ - s) + (c - s) = 2 * (z₁ - s) + (c - z₁) := by ring
      rw [e2]
      refine (norm_add_le _ _).trans ?_
      rw [norm_mul, hz₁s]
      have : ‖(2 : ℂ)‖ = 2 := by norm_num
      rw [this]
      have := hcρ₀ c hc
      have e3 : 2 * (κ / V) = 2 * κ / V := by ring
      linarith
    have h3 : t₀ * (ρ₁ * ε) = ρ₀ * (4 * κ₀ / V + ρ) := by
      rw [ht₀, hρ₁ρ₀, hε]; field_simp
    have h4 : 2 * κ / V + ρ₀ ≤ 4 * κ₀ / V + ρ := by
      have : 2 * κ / V ≤ 4 * κ₀ / V := by
        rw [div_le_div_iff_of_pos_right hV]; linarith
      linarith
    calc ‖z₁ - c‖ * ‖(z₁ - s) + (c - s)‖ ≤ ρ₀ * (2 * κ / V + ρ₀) :=
          mul_le_mul h1 h2 (norm_nonneg _) hρ₀0.le
      _ ≤ ρ₀ * (4 * κ₀ / V + ρ) := mul_le_mul_of_nonneg_left h4 hρ₀0.le
      _ = t₀ * (ρ₁ * ε) := h3.symm
      _ ≤ t₀ * ‖(y - s) ^ 2 - (z₁ - s) ^ 2‖ := mul_le_mul_of_nonneg_left (hbig y hy) ht₀0
  set τ := coreFactorPerturbation P κ₀ V ρ G with hτ
  have hτ0 : 0 ≤ τ := by
    rw [hτ, coreFactorPerturbation, ← ht₀]
    have := one_le_pow₀ (n := P) (by linarith : (1 : ℝ) ≤ 1 + t₀); linarith
  have hFc : ∀ c ∈ C, ‖F c - F z₁‖ ≤ τ * ‖F z₁‖ := fun c hc => by
    have h := norm_prod_sub_prod_le SL (fun y => (y - s) ^ 2 - (c - s) ^ 2)
      (fun y => (y - s) ^ 2 - (z₁ - s) ^ 2) ht₀0 (hfacc c hc)
    refine h.trans (mul_le_mul_of_nonneg_right ?_ (norm_nonneg _))
    rw [hτ, coreFactorPerturbation, ← ht₀]
    have := pow_le_pow_right₀ (by linarith : (1 : ℝ) ≤ 1 + t₀) hpP
    linarith
  set t : ℝ := ‖fejerPowWin (k + p) V ((κ / V : ℝ) : ℂ)‖ with ht
  have hKθ : fejerPowWin (k + p) V (z₁ - s) = (t : ℂ) := by
    rw [hθc, ht]; exact fejerPowWin_ofReal_eq_norm hV.le _ _
  have hKc : ∀ c ∈ C, ‖fejerPowWin (k + p) V (c - s) - t‖ ≤ 2 * (ρ * V) * t := fun c hc => by
    have e : (c - s) - ((κ / V : ℝ) : ℂ) = c - z₁ := by rw [← hθc]; ring
    have hcV : ‖(c - s) - ((κ / V : ℝ) : ℂ)‖ * V ≤ 1 := by
      rw [e]; exact le_trans (mul_le_mul_of_nonneg_right (hcρ c hc) hV.le) hρV
    have h := norm_fejerPowWin_sub_ofReal_le hV.le (k + p) (κ / V) hcV
    have hKr : fejerPowWin (k + p) V ((κ / V : ℝ) : ℂ) = (t : ℂ) := by
      rw [ht]; exact fejerPowWin_ofReal_eq_norm hV.le _ _
    rw [e, hKr, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)] at h
    have h2 : 2 * ‖c - z₁‖ * V * t ≤ 2 * (ρ * V) * t := by
      have := mul_le_mul_of_nonneg_right (hcρ c hc) hV.le
      have ht0 : 0 ≤ t := norm_nonneg _
      nlinarith
    exact h.trans h2
  set η : ℝ := (1 + τ) * (2 * (ρ * V)) + τ with hηdef
  have hFK : ∀ c ∈ C, ‖F c * fejerPowWin (k + p) V (c - s) - F z₁ * t‖ ≤ η * ‖F z₁‖ * t :=
    fun c hc => norm_mul_sub_mul_le (norm_nonneg _) hτ0 (hFc c hc) (hKc c hc)
  -- the core is coherent with the record
  have hγ₀1 : 1 ≤ z₀.im := le_trans (by
    unfold nearTopHeight
    have : 0 ≤ 700000 * (Real.exp (w / 2) * scaledBumpDecay w) ^ 2 / centerAmplitude w ^ 2 := by
      positivity
    linarith) hTw
  have hDS : ∀ c ∈ S, D c ≠ 0 := fun c hc => by
    rw [hS, Set.Finite.mem_toFinset] at hc; exact hc.1
  have hJ0 : 0 ≤ bumpMass w := integral_nonneg fun u => abs_nonneg _
  have hcoh : ∀ c ∈ C, 0 ≤ (D c * conj (D z₁)).re := fun c hc => by
    by_cases hne : c = z₁
    · rw [hne, Complex.mul_conj, Complex.normSq_eq_norm_sq, Complex.ofReal_re]; positivity
    · have hcS := (Finset.mem_filter.mp hc).1
      have hcz := hcρ c hc
      exact re_twin_mul_conj_nonneg hw hγ₀1 (hmem z₁ hz₁) (hmem c (hDS c hcS)) hlow
        (by linarith) hH₀ hup hD₁ hH hK
        (le_trans (mul_le_mul_of_nonneg_left hcz (mul_nonneg (by positivity) hJ0)) hρL)
        (le_trans (mul_le_mul_of_nonneg_left hcz hw.le) hρw)
  -- the mass of the core
  set Dmax : ℝ := 80 * Real.log (180 * (Γ + 1)) * (Real.exp (w / 2) * scaledBumpDecay w) ^ 2
    with hDmax
  have hDc : ∀ c ∈ C, ‖D c‖ ≤ Dmax := fun c hc => by
    have hcS := (Finset.mem_filter.mp hc).1
    refine (norm_evenCoeff_modScaledBump_le_log hw z₀.im (hDS c hcS)).trans ?_
    have h4 := four_le_abs_im_of_evenCoeff_zeta (hDS c hcS)
    have himc : |c.im| ≤ Γ + 1 := by
      have := Complex.abs_im_le_norm (c - z₁); rw [Complex.sub_im] at this
      have := abs_sub_abs_le_abs_sub c.im z₁.im
      have := hcρ c hc
      linarith
    have : Real.log (180 * |c.im|) ≤ Real.log (180 * (Γ + 1)) :=
      Real.log_le_log (by linarith) (by linarith)
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left this (by norm_num)) (by positivity)
  have hCcard : C.card ≤ P + 1 := by
    have hsub : C ⊆ insert z₁ T := fun c hc => by
      by_cases hne : c = z₁
      · rw [hne]; exact Finset.mem_insert_self _ _
      · exact Finset.mem_insert_of_mem (hST (Finset.mem_erase.mpr ⟨hne, (Finset.mem_filter.mp hc).1⟩))
    exact (Finset.card_le_card hsub).trans ((Finset.card_insert_le _ _).trans (by omega))
  have hsumD : ∑ c ∈ C, ‖D c‖ ≤ (P + 1) * Dmax := by
    have h := Finset.sum_le_card_nsmul C (fun c => ‖D c‖) Dmax hDc
    rw [nsmul_eq_mul] at h
    have hD0 : 0 ≤ Dmax := le_trans (norm_nonneg _) (hDc z₁ hz₁C)
    have : (C.card : ℝ) ≤ P + 1 := by exact_mod_cast hCcard
    nlinarith
  have hη0 : 0 ≤ η := by rw [hηdef]; positivity
  have hηsum : η * ∑ c ∈ C, ‖D c‖ ≤ ‖D z₁‖ / 2 := by
    have h1 := mul_le_mul_of_nonneg_left hsumD hη0
    have h2 : η * ((P + 1) * Dmax) ≤ centerAmplitude w ^ 2 / (2 * Real.exp 1) / 2 := by
      rw [hηdef, hτ, hDmax]; exact hη
    linarith
  -- the record kernel is positive
  have hθ0 : 0 < κ / V := div_pos hκ0 hV
  have ht0 : 0 < t := by
    have h := norm_fejerPowWin_ofReal_ge hV (k + p) hθ0
    refine lt_of_lt_of_le ?_ h
    have : 0 < (Real.exp (κ / V * V) - 1) / (κ / V) := by
      rw [div_mul_cancel₀ κ hV.ne']
      exact div_pos (by linarith [Real.add_one_lt_exp hκ0.ne']) hθ0
    positivity
  have hcs := norm_core_sum_ge hz₁C D F (fun c => fejerPowWin (k + p) V (c - s)) ht0 hF₁ hcoh
    (fun c hc => by have := hFK c hc; simpa using this) hηsum
  have hcol : ‖D z₁‖ * (‖F z₁‖ / 2) * 1 ^ 0 * t ≤
      (2 * (k + p)).factorial * (π / V) ^ (2 * (k + p)) *
        ((8 / 3) ^ p * (4 / 3) ^ k *
          (4 * |2 * (lagStructure zetaZeroConfig b 0).re| +
            4 * (∑' z : ℂ, ‖D z‖) +
            3840 * Real.log (180 * (|z₁.im| + 6)) * ‖D z₁‖ * Real.exp κ) / r ^ (2 * k + 1)) := by
    refine le_trans (le_of_eq (by ring)) (hcs.trans ?_)
    exact hPE
  sorry

end GaloisForLFunctions.SquareRootThreshold
