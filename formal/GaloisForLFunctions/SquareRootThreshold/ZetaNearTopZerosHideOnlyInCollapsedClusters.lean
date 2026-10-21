import GaloisForLFunctions.SquareRootThreshold.ZetaAttainedTopIsVisibleAtALogarithmicLag

/-!
# Near-top zeros of `ζ` hide only in collapsed clusters

The full elimination of `ZetaAttainedTopIsVisibleAtALogarithmicLag` applies at every near-top zero,
attained or not. It turns the twin law and the dipole law into one statement about the cluster of
zeros around the Legendre record.

**Collapse** (`zeta_near_top_cluster_collapse`). Let `½ + z₀` be a zero right of the line at height
`γ₀ ≥ T_w`, `1/V`-near the top, `P ≥ 80 log(180Γ)` (the local zero count), and let the difference tests of the bump modulated to `γ₀` be Weil nonnegative on
`[0, V]`. For `k ≥ 1`, `κ₀ ≥ 1`, `r = δ₀/8`, `2κ₀/V ≤ δ₀/16`, `Vr ≥ 4π(k + P)` and the record-depth
condition, the record `z*` has a cluster `C` of `p ≤ P` zeros — all zeros within `r − 2κ₀/V` of `z*`,
none beyond `r + 2κ₀/V` — with
`Π_{z ∈ C}|z − z*| ≤ B(p) (2(P + 1)/κ₀)^p / (V^{2k+p+1} r^{2k+1})`,
`B(p) = (8/3)^p (4/3)^k 2κ₀ (4κ₀² + 4π²(k+p)²)^{k+p} A_w log(180(Γ + 6))` (`clusterCollapseBound`;
`cluster_log_arith` is the arithmetic).

For `p = 0` the inequality says `V^{2k+1} r^{2k+1} ≤ B(0)`, false for large `V`: the cluster is not
empty, which is the twin law. For `p ≥ 1`, with `Vr ≍ k + P`, the geometric mean
`(Π|z − z*|)^{1/p}` is at most `O_w((P/κ₀)(k + P)²/(κ₀V)) λ^{−2k/p}`: the companions of a hidden record
sit, on geometric average, exponentially close to it in `k/p`. Hiding at a near-top zero up to lag `V`
requires an approximate multiple zero of multiplicity `p + 1`, `p ≤ P ≍ log γ₀`, at geometric radius
`e^{−c Vδ₀/p}`, or one of the escapes (`V < V_w(z₀)`).
-/

open MeasureTheory Complex Set Filter Topology
open scoped Real ComplexConjugate

noncomputable section

namespace GaloisForLFunctions.SquareRootThreshold

open Zeta23 _root_.RHTower

/-- The cluster bound
`B(p) = (8/3)^p (4/3)^k 2κ₀ (4κ₀² + 4π²(k+p)²)^{k+p} A_w log(180(Γ + 6))`. -/
def clusterCollapseBound (w γ₀ κ₀ : ℝ) (k p : ℕ) : ℝ :=
  (8 / 3) ^ p * (4 / 3) ^ k * (2 * κ₀) * (4 * κ₀ ^ 2 + 4 * π ^ 2 * (k + p : ℕ) ^ 2) ^ (k + p) *
    twinTightConstant w * Real.log (180 * (recordHeightEnvelope w γ₀ + 6))

/-- The arithmetic of the collapse, keeping the product of distances. -/
theorem cluster_log_arith {D Pr ε K u Ξ V r κ Q Q₂ κ₀ A L E c : ℝ} {p m k : ℕ}
    (hD : 0 < D) (hu : 0 < u) (hE : 0 < E) (hε : 0 ≤ ε) (hPr : 0 ≤ Pr) (hr : 0 < r) (hV : 0 < V)
    (hκQ : 0 < κ * Q)
    (hcol : D * Pr * ε ^ p * K ≤ u * (c * Ξ / r ^ (2 * k + 1)))
    (hK : u * E * V ^ m / (κ * Q) ≤ K) (hΞ : Ξ ≤ A * L * (D * E))
    (hc : 0 ≤ c) (hQ : κ * Q ≤ 2 * κ₀ * Q₂) (hAL : 0 ≤ A * L) :
    Pr * ε ^ p * V ^ m * r ^ (2 * k + 1) ≤ c * (2 * κ₀ * Q₂) * (A * L) := by
  have hK0 : 0 ≤ u * E * V ^ m / (κ * Q) := by positivity
  have hεp : 0 ≤ ε ^ p := by positivity
  have h1 : D * Pr * ε ^ p * (u * E * V ^ m / (κ * Q)) ≤ D * Pr * ε ^ p * K :=
    mul_le_mul_of_nonneg_left hK (by positivity)
  have h2 : u * (c * Ξ / r ^ (2 * k + 1)) ≤ u * (c * (A * L * (D * E)) / r ^ (2 * k + 1)) := by
    gcongr
  have h3 := (h1.trans hcol).trans h2
  have hr0 : 0 < r ^ (2 * k + 1) := by positivity
  have e1 : D * Pr * ε ^ p * (u * E * V ^ m / (κ * Q)) =
      (u * D * E) * (Pr * ε ^ p * V ^ m / (κ * Q)) := by ring
  have e2 : u * (c * (A * L * (D * E)) / r ^ (2 * k + 1)) =
      (u * D * E) * (c * (A * L) / r ^ (2 * k + 1)) := by ring
  rw [e1, e2] at h3
  have h4 := le_of_mul_le_mul_left h3 (by positivity)
  rw [div_le_div_iff₀ hκQ hr0] at h4
  calc Pr * ε ^ p * V ^ m * r ^ (2 * k + 1) ≤ c * (A * L) * (κ * Q) := h4
    _ ≤ c * (A * L) * (2 * κ₀ * Q₂) := by gcongr
    _ = _ := by ring

/-- **Near-top zeros hide only in collapsed clusters.** Let `½ + z₀` be a zero right of the line at
height `γ₀ ≥ T_w`, `1/V`-near the top, let `P ≥ 80 log(180Γ)`, and let the difference tests of the bump modulated to `γ₀` be
Weil nonnegative on `[0, V]`. Let `k ≥ 1`, `κ₀ ≥ 1`, `r = δ₀/8`, `2κ₀/V ≤ δ₀/16`,
`V ≥ π(k + P)`, `Vr ≥ 4π(k + P)` and `V δ₀ ≥ 2 log(160 log(180Γ)(e^{w/2}B_w)²/a_w²)`. Then the
Legendre record `z*` has a cluster `C` of `p ≤ P` zeros, containing every zero within
`r − 2κ₀/V` of `z*` and contained in the disc of radius `r + 2κ₀/V`, with
`Π_{z ∈ C}|z − z*| (κ₀/(2(P + 1)))^p V^{2k+p+1} r^{2k+1} ≤ B(p)` (`clusterCollapseBound`). -/
theorem zeta_near_top_cluster_collapse {w : ℝ} (hw : 0 < w) {z₀ : ℂ}
    (hz₀ : (1 / 2 + z₀) ∈ zetaZeroConfig.carrier) (hre₀ : 0 < z₀.re)
    (hTw : nearTopHeight w ≤ z₀.im)
    {V : ℝ} (hV : 0 < V)
    (htop : ∀ ρ ∈ zetaZeroConfig.carrier, ρ.re - 1 / 2 ≤ z₀.re + 1 / V)
    (hneg : ∀ v ∈ Icc (0 : ℝ) V, 0 ≤ (zetaZeroConfig.W (twoBump (modScaledBump w z₀.im) v (-1))
      (twoBump (modScaledBump w z₀.im) v (-1))).re) {P : ℕ}
    (hP : 80 * Real.log (180 * recordHeightEnvelope w z₀.im) ≤ P)
    {κ₀ : ℝ} {k : ℕ} (hk : 1 ≤ k) (hκ₀ : 1 ≤ κ₀)
    (hV2 : 2 * Real.log (160 * Real.log (180 * recordHeightEnvelope w z₀.im) *
        (Real.exp (w / 2) * scaledBumpDecay w) ^ 2 / centerAmplitude w ^ 2) ≤ z₀.re * V)
    (hκV : 2 * κ₀ / V ≤ z₀.re / 16) (hVk : π * (k + P : ℕ) ≤ V)
    (hVr : 4 * π * (k + P : ℕ) ≤ V * (z₀.re / 8)) :
    ∃ z₁ : ℂ, evenCoeff zetaZeroConfig (modScaledBump w z₀.im) z₁ ≠ 0 ∧ z₀.re / 2 ≤ z₁.re ∧
      |z₁.im| ≤ recordHeightEnvelope w z₀.im ∧
      (∀ z, evenCoeff zetaZeroConfig (modScaledBump w z₀.im) z ≠ 0 → 0 < z.re →
        ‖evenCoeff zetaZeroConfig (modScaledBump w z₀.im) z‖ * Real.exp (z.re * V) ≤
          ‖evenCoeff zetaZeroConfig (modScaledBump w z₀.im) z₁‖ * Real.exp (z₁.re * V)) ∧
      ∃ C : Finset ℂ, z₁ ∉ C ∧ C.card ≤ P ∧
        (∀ z ∈ C, evenCoeff zetaZeroConfig (modScaledBump w z₀.im) z ≠ 0 ∧
          ‖z - z₁‖ ≤ z₀.re / 8 + 2 * κ₀ / V) ∧
        (∀ z, z ≠ z₁ → evenCoeff zetaZeroConfig (modScaledBump w z₀.im) z ≠ 0 →
          ‖z - z₁‖ ≤ z₀.re / 8 - 2 * κ₀ / V → z ∈ C) ∧
        (∏ z ∈ C, ‖z - z₁‖) * (κ₀ / (2 * (P + 1))) ^ C.card * V ^ (2 * k + C.card + 1) *
            (z₀.re / 8) ^ (2 * k + 1) ≤ clusterCollapseBound w z₀.im κ₀ k C.card := by
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
  refine ⟨z₁, hz₁, hre₁, hup, hrec, ?_⟩
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
  have hεz : ∀ z ∈ S.erase z₁, ε ≤ ‖(z - s) + ((κ / V : ℝ) : ℂ)‖ := fun z hz => by
    have e : (z - s) + ((κ / V : ℝ) : ℂ) = (z - z₁) + ((2 * κ / V : ℝ) : ℂ) := by
      apply Complex.ext
      · simp [hs]; ring
      · simp [hs]
    rw [e]; exact hmirror z (hST hz)
  have hε0 : 0 ≤ ε := by rw [hε]; positivity
  have hcol := zeta_full_cluster_collapse (contDiff_modScaledBump_two w _)
    (modScaledBump_support hw _) hneg hz₁ hrec hκ0 hr0 hr1 hrσ hk S hz₁S hSr hiso
    (le_trans (mul_le_mul_of_nonneg_left hpP' Real.pi_pos.le) hVk)
    (le_trans (mul_le_mul_of_nonneg_left hpP' (by positivity)) hVr) hε0 hεz
  rw [← hp] at hcol
  -- the cluster and its bound
  refine ⟨S.erase z₁, Finset.notMem_erase z₁ S, hpP, fun z hz => ?_, fun z hz1 hDz hzr => ?_, ?_⟩
  · have hzS := (Finset.mem_erase.mp hz).2
    rw [hS, Set.Finite.mem_toFinset] at hzS
    refine ⟨hzS.1, ?_⟩
    have h1 := norm_sub_le_norm_sub_add_norm_sub z s z₁
    rw [norm_sub_rev s z₁, hz₁s] at h1
    linarith [hzS.2]
  · refine Finset.mem_erase.mpr ⟨hz1, ?_⟩
    rw [hS, Set.Finite.mem_toFinset]
    refine ⟨hDz, ?_⟩
    have h1 := norm_sub_le_norm_sub_add_norm_sub z z₁ s
    rw [hz₁s] at h1
    linarith
  rw [← hp]
  obtain ⟨L, hL⟩ : ∃ L : ℝ, L = Real.log (180 * (|z₁.im| + 6)) := ⟨_, rfl⟩
  obtain ⟨LΓ, hLΓ⟩ : ∃ LΓ : ℝ, LΓ = Real.log (180 * (Γ + 6)) := ⟨_, rfl⟩
  have hθ0 : 0 < κ / V := div_pos hκ0 hV
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
  have hK : u * (Real.exp κ - 1) * V ^ (2 * (k + p) + 1) / (κ * Q) ≤
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
  have hPr0 : 0 ≤ ∏ z ∈ S.erase z₁, ‖z - z₁‖ := Finset.prod_nonneg fun _ _ => norm_nonneg _
  have hfin := cluster_log_arith (D := ‖D z₁‖) (u := u) (E := Real.exp κ - 1)
    (norm_pos_iff.mpr hz₁) hu0 hE hε0 hPr0 hr0 hV (mul_pos hκ0 hQ0) hcol hK hΞ hc0 hQQ
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
  calc (∏ z ∈ S.erase z₁, ‖z - z₁‖) * (κ₀ / (2 * (P + 1))) ^ p * V ^ (2 * k + p + 1) * r ^ (2 * k + 1)
      = (∏ z ∈ S.erase z₁, ‖z - z₁‖) * ε ^ p * V ^ (2 * (k + p) + 1) * r ^ (2 * k + 1) := by
        rw [mul_assoc (∏ z ∈ S.erase z₁, ‖z - z₁‖), ← e]; ring
    _ ≤ (8 / 3) ^ p * (4 / 3) ^ k * (2 * κ₀ * Q₂) * (twinTightConstant w * L) := hfin
    _ ≤ (8 / 3) ^ p * (4 / 3) ^ k * (2 * κ₀ * Q₂) * (twinTightConstant w * LΓ) :=
        mul_le_mul_of_nonneg_left h1 h2
    _ = clusterCollapseBound w z₀.im κ₀ k p := by
        rw [clusterCollapseBound, ← hΓdef, ← hLΓ, ← hQ₂]; ring

end GaloisForLFunctions.SquareRootThreshold
