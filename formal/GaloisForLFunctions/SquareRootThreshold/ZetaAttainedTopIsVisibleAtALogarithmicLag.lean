import GaloisForLFunctions.SquareRootThreshold.ZetaNearTopClustersCollapseBeyondTheThreshold

/-!
# An attained top of `ζ` is visible at a lag logarithmic in the separation

`ZetaAttainedTopIsVisibleAtAnExplicitLag` makes an attained top visible at a lag `O(1/g)` in the
separation `g` of the zeros near the top, through the twin radius. The full elimination of
`ZetaNearTopClustersCollapseBeyondTheThreshold` lowers this to `O(P log(P/g))`, `P ≍ log γ₀` the
local zero count: a cluster can hide the record only by an exponentially small geometric mean
radius, and the zeros near an attained top are finitely many and `g`-separated.

* **Finiteness** (`finite_evenCoeff_ball`, `exists_box_count_and_separation`). Finitely many
  exponents lie in a disc; the zeros in a box `|Im ρ| ≤ H`, `Re ρ ≥ ½ + d` number at most some `P`
  and keep a positive distance `g`.
* **Mirror points** (`exists_depth_avoiding_mirrors`). Among the `P + 1` depths
  `κ₀(1 + j/(P + 1))`, each companion spoils at most one; so some `κ ∈ [κ₀, 2κ₀]` keeps every
  `|(z − z*) + 2κ/V| ≥ κ₀/(2(P + 1)V)`.
* **Full elimination** (`zeta_full_cluster_collapse`). Eliminating every companion within `r` of
  `s = z* − κ/V`:
  `|D(z*)| Π|z − z*| ε^p |K_{k+p}(κ/V)| ≤ (2(k+p))!(π/V)^{2(k+p)} (8/3)^p (4/3)^k Ξ/r^{2k+1}`.
* **The record of a near-top zero** (`near_top_record_facts`, `mass_le_of_record_height`,
  `xi_ratio_le`): `|D(z*)| ≥ a_w²/(2e)`, `γ₀/2 ≤ |Im z*| ≤ Γ`, `Re z* ≥ Re z₀/2`, and
  `Ξ ≤ A_w L |D(z*)|(e^κ − 1)`.
* **Logarithmic lag** (`zeta_attained_top_visible_log`). For a zero `½ + z₀` of largest real part
  `½ + δ₀` at height `γ₀ ≥ T_w`, with `P ≥ 80 log(180Γ)` and separation `g` in the box near the top, the
  modulated family has a negative difference test at a lag `v ≤ V` as soon as `2κ₀/V ≤ δ₀/16`,
  `V δ₀/8 ≥ 4π(k + P)`, `V δ₀ ≥ 2 log(160 log(180Γ)(e^{w/2}B_w)²/a_w²)` and, for every `p ≤ P`,
  `(8/3)^p (4/3)^k 2κ₀ (4κ₀² + 4π²(k+p)²)^{k+p} A_w log(180(Γ + 6)) < (gκ₀/(2(P+1)))^p V^{2k+p+1} (δ₀/8)^{2k+1}`.

In the last condition `V` enters with the exponent `2k + p + 1` and `g` only with `p ≤ P`; with
`Vδ₀ ≍ k + P` it holds once `k ≳ P log(P/g)`. The first negative lag of an attained top is therefore
`O_w((log γ₀ · log(log γ₀/g) + log log γ₀)/δ₀)`: logarithmic in the separation, against `O(1/g)`
before.
-/

open MeasureTheory Complex Set Filter Topology
open scoped Real ComplexConjugate

noncomputable section

namespace GaloisForLFunctions.SquareRootThreshold

open Zeta23 _root_.RHTower

/-- Finitely many exponents lie in each closed disc. -/
theorem finite_evenCoeff_ball (Z : ZeroConfig) (b : ℝ → ℂ) (s : ℂ) (r : ℝ) :
    {z : ℂ | evenCoeff Z b z ≠ 0 ∧ ‖z - s‖ ≤ r}.Finite := by
  have h1 := (Z.finite_window (s.im - r - 1) (s.im + r)).image fun ρ : ℂ => ρ - 1 / 2
  have h2 := (Z.finite_window (-s.im - r - 1) (-s.im + r)).image fun ρ : ℂ => conj (ρ - 1 / 2)
  refine (h1.union h2).subset fun z hz => ?_
  have hz' : evenCoeff Z b z ≠ 0 ∧ ‖z - s‖ ≤ r := hz
  have him : |z.im - s.im| ≤ r := by
    have := Complex.abs_im_le_norm (z - s); rw [Complex.sub_im] at this; linarith [hz'.2]
  rw [abs_le] at him
  rcases mem_of_evenCoeff_ne_zero hz'.1 with h | h
  · refine Or.inl ⟨1 / 2 + z, ⟨h, ?_⟩, by simp⟩
    have : (1 / 2 + z).im = z.im := by simp
    exact ⟨by linarith, by linarith⟩
  · refine Or.inr ⟨1 / 2 + conj z, ⟨h, ?_⟩, by simp⟩
    have : (1 / 2 + conj z).im = -z.im := by simp
    exact ⟨by linarith, by linarith⟩

/-- **A depth avoiding every mirror point.** For a finite set `T` of at most `P` points, `κ₀ > 0` and
`V > 0`, some depth `κ ∈ [κ₀, 2κ₀]` keeps `|(z − z₁) + 2κ/V| ≥ κ₀/(2(P + 1)V)` for every `z ∈ T`. -/
theorem exists_depth_avoiding_mirrors (T : Finset ℂ) (z₁ : ℂ) {P : ℕ} (hP : T.card ≤ P)
    {κ₀ V : ℝ} (hκ₀ : 0 < κ₀) (hV : 0 < V) :
    ∃ κ : ℝ, κ₀ ≤ κ ∧ κ ≤ 2 * κ₀ ∧
      ∀ z ∈ T, κ₀ / (2 * (P + 1) * V) ≤ ‖(z - z₁) + ((2 * κ / V : ℝ) : ℂ)‖ := by
  classical
  set ε : ℝ := κ₀ / (2 * (P + 1) * V) with hε
  set κj : ℕ → ℝ := fun j => κ₀ * (1 + j / (P + 1)) with hκj
  set bad : ℂ → Finset ℕ := fun z => (Finset.range (P + 1)).filter fun j =>
    ‖(z - z₁) + ((2 * κj j / V : ℝ) : ℂ)‖ < ε with hbad
  -- each point spoils at most one grid depth
  have hone : ∀ z, (bad z).card ≤ 1 := fun z => by
    rw [Finset.card_le_one]
    intro i hi j hj
    rw [hbad, Finset.mem_filter] at hi hj
    by_contra hij
    have h1 : ‖((2 * κj i / V : ℝ) : ℂ) - ((2 * κj j / V : ℝ) : ℂ)‖ < 2 * ε := by
      have := norm_sub_le ((z - z₁) + ((2 * κj i / V : ℝ) : ℂ)) ((z - z₁) + ((2 * κj j / V : ℝ) : ℂ))
      rw [show (z - z₁) + ((2 * κj i / V : ℝ) : ℂ) - ((z - z₁) + ((2 * κj j / V : ℝ) : ℂ)) =
        ((2 * κj i / V : ℝ) : ℂ) - ((2 * κj j / V : ℝ) : ℂ) by ring] at this
      linarith [hi.2, hj.2]
    rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs] at h1
    have hdiff : 2 * κj i / V - 2 * κj j / V = 2 * κ₀ * ((i : ℝ) - j) / ((P + 1) * V) := by
      rw [hκj]; field_simp; ring
    rw [hdiff, abs_div, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 * κ₀),
      abs_of_pos (by positivity : (0 : ℝ) < (P + 1) * V)] at h1
    have hij' : (1 : ℝ) ≤ |(i : ℝ) - j| := by
      have : (i : ℤ) ≠ j := by exact_mod_cast hij
      have := Int.one_le_abs (sub_ne_zero.mpr this)
      exact_mod_cast this
    rw [div_lt_iff₀ (by positivity), hε] at h1
    have : 2 * κ₀ ≤ 2 * κ₀ * |(i : ℝ) - j| := le_mul_of_one_le_right (by positivity) hij'
    have e : 2 * (κ₀ / (2 * (P + 1) * V)) * ((P + 1) * V) = κ₀ := by field_simp
    linarith
  -- fewer bad depths than grid depths
  have hcard : (T.biUnion bad).card < (Finset.range (P + 1)).card := by
    calc (T.biUnion bad).card ≤ ∑ z ∈ T, (bad z).card := Finset.card_biUnion_le
      _ ≤ ∑ _z ∈ T, 1 := Finset.sum_le_sum fun z _ => hone z
      _ = T.card := by simp
      _ < (Finset.range (P + 1)).card := by rw [Finset.card_range]; omega
  obtain ⟨j, hj, hjb⟩ : ∃ j ∈ Finset.range (P + 1), j ∉ T.biUnion bad := by
    by_contra h
    push Not at h
    exact absurd (Finset.card_le_card (fun j hj => h j hj)) (not_le.mpr hcard)
  have hjP : (j : ℝ) ≤ P := by
    have := Finset.mem_range.mp hj; exact_mod_cast Nat.lt_succ_iff.mp this
  refine ⟨κj j, ?_, ?_, fun z hz => ?_⟩
  · rw [hκj]; have : (0 : ℝ) ≤ j / (P + 1) := by positivity
    nlinarith
  · rw [hκj]
    have : (j : ℝ) / (P + 1) ≤ 1 := by rw [div_le_one (by positivity)]; linarith
    nlinarith
  · by_contra h
    push Not at h
    exact hjb (Finset.mem_biUnion.mpr ⟨z, hz, Finset.mem_filter.mpr ⟨hj, h⟩⟩)

/-- **Full elimination.** Under the hypotheses of `zeta_cluster_collapse`, eliminate every
companion of the record in `S`; if `|(z − s) + κ/V| ≥ ε` for every companion, then with
`p = |S| − 1`:
`|D(z*)| Π_{z ≠ z*}|z − z*| ε^p |K_{k+p}(κ/V)| ≤ (2(k+p))!(π/V)^{2(k+p)} (8/3)^p (4/3)^k Ξ/r^{2k+1}`. -/
theorem zeta_full_cluster_collapse {b : ℝ → ℂ} (hb : ContDiff ℝ 2 b) {w : ℝ}
    (hbs : ∀ u, b u ≠ 0 → |u| ≤ w) {V : ℝ}
    (hm : ∀ v ∈ Icc (0 : ℝ) V, 0 ≤ (zetaZeroConfig.W (twoBump b v (-1)) (twoBump b v (-1))).re)
    {z₁ : ℂ} (hz₁ : evenCoeff zetaZeroConfig b z₁ ≠ 0)
    (hrec : ∀ z : ℂ, evenCoeff zetaZeroConfig b z ≠ 0 → 0 < z.re →
      ‖evenCoeff zetaZeroConfig b z‖ * Real.exp (z.re * V) ≤
        ‖evenCoeff zetaZeroConfig b z₁‖ * Real.exp (z₁.re * V))
    {κ r : ℝ} (hκ : 0 < κ) (hr : 0 < r) (hr1 : r ≤ 1) (hrσ : r ≤ z₁.re - κ / V) {k : ℕ}
    (hk : 1 ≤ k) (S : Finset ℂ) (hz₁S : z₁ ∈ S)
    (hSr : ∀ z ∈ S, ‖z - ((z₁.re - κ / V : ℝ) + z₁.im * I)‖ ≤ r)
    (hiso : ∀ z, z ∉ S → evenCoeff zetaZeroConfig b z ≠ 0 →
      r ≤ ‖z - ((z₁.re - κ / V : ℝ) + z₁.im * I)‖)
    (hV : π * (k + (S.erase z₁).card : ℕ) ≤ V) (hVr : 4 * π * (k + (S.erase z₁).card : ℕ) ≤ V * r)
    {ε : ℝ} (hε0 : 0 ≤ ε)
    (hε : ∀ z ∈ S.erase z₁, ε ≤ ‖(z - ((z₁.re - κ / V : ℝ) + z₁.im * I)) + ((κ / V : ℝ) : ℂ)‖) :
    ‖evenCoeff zetaZeroConfig b z₁‖ * (∏ z ∈ S.erase z₁, ‖z - z₁‖) * ε ^ (S.erase z₁).card *
        ‖fejerPowWin (k + (S.erase z₁).card) V ((κ / V : ℝ) : ℂ)‖ ≤
      (2 * (k + (S.erase z₁).card)).factorial * (π / V) ^ (2 * (k + (S.erase z₁).card)) *
        ((8 / 3) ^ (S.erase z₁).card * (4 / 3) ^ k *
          (4 * |2 * (lagStructure zetaZeroConfig b 0).re| +
            4 * (∑' z : ℂ, ‖evenCoeff zetaZeroConfig b z‖) +
            3840 * Real.log (180 * (|z₁.im| + 6)) * ‖evenCoeff zetaZeroConfig b z₁‖ *
              Real.exp κ) / r ^ (2 * k + 1)) := by
  classical
  set D := evenCoeff zetaZeroConfig b with hDdef
  set s : ℂ := ((z₁.re - κ / V : ℝ) : ℂ) + z₁.im * I with hs
  set SL := S.erase z₁ with hSL
  set p := SL.card with hp
  set M : ℝ := 2 * (lagStructure zetaZeroConfig b 0).re with hM
  set W : ℝ := ∑' z : ℂ, ‖D z‖ with hW
  set L : ℝ := Real.log (180 * (|z₁.im| + 6)) with hL
  set Ξ : ℝ := 4 * |M| + 4 * W + 3840 * L * ‖D z₁‖ * Real.exp κ with hΞ
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hV0 : 0 < V := lt_of_lt_of_le (by positivity) hV
  have hW0 : 0 ≤ W := tsum_nonneg fun z => norm_nonneg _
  have hL0 : 0 ≤ L := Real.log_nonneg (by nlinarith [abs_nonneg z₁.im])
  have hΞ0 : 0 ≤ Ξ := by rw [hΞ]; positivity
  have hσ : 0 < z₁.re - κ / V := lt_of_lt_of_le hr hrσ
  set x : ℂ → ℂ := fun z => z - s with hx
  have hA : ∀ m' : ℕ, k ≤ m' → m' ≤ k + p → ‖elimSeq V S D x [] m'‖ ≤
      (2 * m').factorial * (π / V) ^ (2 * m') * ((4 / 3) ^ m' * Ξ / r ^ (2 * m' + 1)) := by
    intro m' h1 h2
    have hm1 : 1 ≤ m' := le_trans hk h1
    have hm'r : (m' : ℝ) ≤ (k + p : ℕ) := by exact_mod_cast h2
    have hcl := zeta_powCluster_le hb hbs (j := m') hm1 (by nlinarith [Real.pi_pos]) hm hz₁ hrec hκ
      hσ hr (by linarith) (by nlinarith [Real.pi_pos]) S hiso
    have hbr := clusterBracket_le (j := m') hm1 (M := M) (W := W) (D := ‖D z₁‖) (κ := κ) z₁.im hW0
      (norm_nonneg _) hr hr1 hrσ
    have e : elimSeq V S D x [] m' = ∑ z ∈ S, D z * fejerPowWin m' V (z - s) := by
      simp [elimSeq, hx]
    rw [e]
    refine hcl.trans ?_
    refine mul_le_mul_of_nonneg_left (le_trans (le_of_eq ?_) hbr) (by positivity)
    rfl
  set ys : List ℂ := SL.toList.map fun z => x z ^ 2 with hys
  have hlen : ys.length = p := by rw [hys, List.length_map, Finset.length_toList]
  have hysr : ∀ y ∈ ys, ‖y‖ ≤ r ^ 2 := by
    intro y hy
    rw [hys, List.mem_map] at hy
    obtain ⟨z, hz, rfl⟩ := hy
    rw [Finset.mem_toList, hSL, Finset.mem_erase] at hz
    rw [norm_pow]
    exact pow_le_pow_left₀ (norm_nonneg _) (hSr z hz.2) 2
  have hΦ := norm_elimSeq_le hV0 hr hΞ0 S D x ys k hysr (by rw [hlen]; exact hVr)
    (fun m' h1 h2 => hA m' h1 (by rw [hlen] at h2; exact h2))
  rw [hlen] at hΦ
  have hz₁L : z₁ ∉ SL := Finset.notMem_erase z₁ S
  have hdecomp := elimSeq_eq_record_add V S SL D x hz₁S hz₁L k
  rw [← hys] at hdecomp
  -- nothing is left besides the record
  have hR : (S.filter fun z => z ∉ SL).erase z₁ = ∅ := by
    ext z
    simp only [Finset.mem_erase, Finset.mem_filter, hSL, Finset.notMem_empty, iff_false, not_and]
    intro h1 h2 h3
    exact h3 h1 h2
  rw [hR, Finset.sum_empty, add_zero] at hdecomp
  have hx₁ : x z₁ = ((κ / V : ℝ) : ℂ) := by
    simp only [hx]; apply Complex.ext <;> simp [hs]
  -- the record factor
  have hprod : (∏ z ∈ SL, ‖z - z₁‖) * ε ^ p ≤ ‖∏ z' ∈ SL, (x z' ^ 2 - x z₁ ^ 2)‖ := by
    rw [norm_prod, hp, ← Finset.prod_const, ← Finset.prod_mul_distrib]
    refine Finset.prod_le_prod (fun _ _ => by positivity) fun z hz => ?_
    have e : x z ^ 2 - x z₁ ^ 2 = (z - z₁) * (x z + ((κ / V : ℝ) : ℂ)) := by
      rw [hx₁]; simp only [hx]
      have : z₁ - s = ((κ / V : ℝ) : ℂ) := by apply Complex.ext <;> simp [hs]
      linear_combination (z - s + ((κ / V : ℝ) : ℂ)) * this
    rw [e, norm_mul]
    exact mul_le_mul_of_nonneg_left (hε z hz) (norm_nonneg _)
  have hrecn := congrArg norm hdecomp
  rw [norm_mul, norm_mul, hx₁] at hrecn
  rw [hx₁] at hprod
  calc ‖D z₁‖ * (∏ z ∈ SL, ‖z - z₁‖) * ε ^ p * ‖fejerPowWin (k + p) V ((κ / V : ℝ) : ℂ)‖
      = ‖D z₁‖ * ((∏ z ∈ SL, ‖z - z₁‖) * ε ^ p) * ‖fejerPowWin (k + p) V ((κ / V : ℝ) : ℂ)‖ := by
        ring
    _ ≤ ‖D z₁‖ * ‖∏ z' ∈ SL, (x z' ^ 2 - ((κ / V : ℝ) : ℂ) ^ 2)‖ *
          ‖fejerPowWin (k + p) V ((κ / V : ℝ) : ℂ)‖ := by gcongr
    _ = ‖elimSeq V S D x ys k‖ := hrecn.symm
    _ ≤ _ := hΦ

/-! ### The loud record of a near-top zero -/

/-- **Where the loud record sits.** For a near-top zero above `T_w` the Legendre record of the
modulated family has `|D(z*)| ≥ a_w²/(2e)`, `γ₀/2 ≤ |Im z*| ≤ Γ`, and depth `Re z* ≥ Re z₀/2` once
`V Re z₀ ≥ 2 log(160 log(180Γ)(e^{w/2}B_w)²/a_w²)`. -/
theorem near_top_record_facts {w V : ℝ} (hw : 0 < w) (hV : 0 < V) {z₀ : ℂ}
    (hz₀ : (1 / 2 + z₀) ∈ zetaZeroConfig.carrier) (hre₀ : 0 < z₀.re)
    (hTw : nearTopHeight w ≤ z₀.im)
    (htop : ∀ z, evenCoeff zetaZeroConfig (modScaledBump w z₀.im) z ≠ 0 → z.re ≤ z₀.re + 1 / V)
    (hV2 : 2 * Real.log (160 * Real.log (180 * recordHeightEnvelope w z₀.im) *
        (Real.exp (w / 2) * scaledBumpDecay w) ^ 2 / centerAmplitude w ^ 2) ≤ z₀.re * V) :
    ∃ z₁ : ℂ, evenCoeff zetaZeroConfig (modScaledBump w z₀.im) z₁ ≠ 0 ∧ z₀.re / 2 ≤ z₁.re ∧
      z₀.im / 2 ≤ |z₁.im| ∧ |z₁.im| ≤ recordHeightEnvelope w z₀.im ∧
      centerAmplitude w ^ 2 / (2 * Real.exp 1) ≤
        ‖evenCoeff zetaZeroConfig (modScaledBump w z₀.im) z₁‖ ∧
      ∀ z, evenCoeff zetaZeroConfig (modScaledBump w z₀.im) z ≠ 0 → 0 < z.re →
        ‖evenCoeff zetaZeroConfig (modScaledBump w z₀.im) z‖ * Real.exp (z.re * V) ≤
          ‖evenCoeff zetaZeroConfig (modScaledBump w z₀.im) z₁‖ * Real.exp (z₁.re * V) := by
  have hpos₀ : 0 < z₀.im := lt_of_lt_of_le (by unfold nearTopHeight; positivity) hTw
  obtain ⟨hΓ, hsmall⟩ := nearTopHeight_conditions hw hTw
  obtain ⟨z₁, hz₁, hre₁, hD₁, hrec⟩ := exists_loud_record_of_near_top hw hV hz₀ hre₀ hpos₀ hΓ htop
  set D := evenCoeff zetaZeroConfig (modScaledBump w z₀.im) with hDdef
  set K₀ := (Real.exp (w / 2) * scaledBumpDecay w) ^ 2 with hK₀
  set a := centerAmplitude w with ha
  set Γ := recordHeightEnvelope w z₀.im with hΓdef
  have ha0 : 0 < a := centerAmplitude_pos hw
  have hK0 : 0 ≤ K₀ := by positivity
  have hε : 0 < a ^ 2 / (2 * Real.exp 1) := by positivity
  have hup : |z₁.im| ≤ Γ := abs_im_le_of_norm_evenCoeff_modScaledBump_ge hw hpos₀.le hε hz₁ hD₁
  have hlow : z₀.im / 2 ≤ |z₁.im| :=
    half_le_abs_im_of_norm_evenCoeff_modScaledBump_ge hw hpos₀ hz₁ hD₁ hsmall
  have h4 : 4 ≤ |z₁.im| := four_le_abs_im_of_evenCoeff_zeta hz₁
  refine ⟨z₁, hz₁, ?_, hlow, hup, hD₁, hrec⟩
  have hD₀ : a ^ 2 / 2 ≤ ‖D z₀‖ := by
    have := norm_evenCoeff_modScaledBump_center_ge hw hz₀ hre₀ hpos₀
    rw [show 4 * w * (Real.exp (-(w / 2)) * (∫ u, weilBump u)) = a from rfl] at this
    linarith
  have hD₀ne : D z₀ ≠ 0 := fun h => by rw [h, norm_zero] at hD₀; nlinarith
  have hDmax : ‖D z₁‖ ≤ 80 * Real.log (180 * Γ) * K₀ := by
    refine (norm_evenCoeff_modScaledBump_le_log hw z₀.im hz₁).trans ?_
    have : Real.log (180 * |z₁.im|) ≤ Real.log (180 * Γ) :=
      Real.log_le_log (by linarith) (by linarith)
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left this (by norm_num)) hK0
  have h1 := hrec z₀ hD₀ne hre₀
  have hD1pos : 0 < ‖D z₁‖ := norm_pos_iff.mpr hz₁
  have hq : 0 < 160 * Real.log (180 * Γ) * K₀ / a ^ 2 := by
    have : 0 < 80 * Real.log (180 * Γ) * K₀ := lt_of_lt_of_le hD1pos hDmax
    have : 0 < 160 * Real.log (180 * Γ) * K₀ := by linarith
    positivity
  have h2 : Real.exp ((z₀.re - z₁.re) * V) ≤ 160 * Real.log (180 * Γ) * K₀ / a ^ 2 := by
    have hE0 := Real.exp_pos (z₀.re * V)
    have hE1 := Real.exp_pos (z₁.re * V)
    have e : Real.exp ((z₀.re - z₁.re) * V) = Real.exp (z₀.re * V) / Real.exp (z₁.re * V) := by
      rw [← Real.exp_sub]; ring_nf
    rw [e, div_le_iff₀ hE1]
    have : a ^ 2 / 2 * Real.exp (z₀.re * V) ≤ 80 * Real.log (180 * Γ) * K₀ * Real.exp (z₁.re * V) :=
      calc a ^ 2 / 2 * Real.exp (z₀.re * V) ≤ ‖D z₀‖ * Real.exp (z₀.re * V) :=
            mul_le_mul_of_nonneg_right hD₀ hE0.le
        _ ≤ ‖D z₁‖ * Real.exp (z₁.re * V) := h1
        _ ≤ _ := mul_le_mul_of_nonneg_right hDmax hE1.le
    rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
    nlinarith
  have h3 := Real.log_le_log (Real.exp_pos _) h2
  rw [Real.log_exp] at h3
  nlinarith

/-- The mass terms of the family modulated to `γ₀`, seen from a record at height `≥ γ₀/2`:
`|M| + W ≤ 32(e^{w/2}B_w)²(C + 1) L`, `L = log(180(|Im z*| + 6))`. -/
theorem mass_le_of_record_height {w : ℝ} (hw : 0 < w) {γ₀ : ℝ} (hγ₀ : 0 < γ₀) {y : ℝ}
    (hy : γ₀ / 2 ≤ |y|) :
    |2 * (lagStructure zetaZeroConfig (modScaledBump w γ₀) 0).re| +
        ∑' z : ℂ, ‖evenCoeff zetaZeroConfig (modScaledBump w γ₀) z‖ ≤
      32 * (Real.exp (w / 2) * scaledBumpDecay w) ^ 2 * (xiLineTwoLogDerivConstant + 1) *
        Real.log (180 * (|y| + 6)) := by
  set K₀ := (Real.exp (w / 2) * scaledBumpDecay w) ^ 2 with hK₀
  set C := xiLineTwoLogDerivConstant with hC
  set L := Real.log (180 * (|y| + 6)) with hL
  have hK0 : 0 ≤ K₀ := by positivity
  have hC0 : 0 ≤ C := xiLineTwoLogDerivConstant_nonneg
  have hL1 : 1 ≤ L := by
    rw [hL, Real.le_log_iff_exp_le (by positivity)]
    have : Real.exp 1 ≤ 3 := by linarith [Real.exp_one_lt_d9]
    nlinarith [abs_nonneg y]
  have hcL : Real.log (|γ₀| + 4) ≤ L := by
    rw [abs_of_pos hγ₀, hL]
    exact Real.log_le_log (by positivity) (by linarith)
  have hW := tsum_norm_evenCoeff_modScaledBump_le hw γ₀
  have hMW := abs_two_re_lagStructure_zero_le zetaZeroConfig temperedConfig_zetaZeroConfig
    (contDiff_modScaledBump_two w γ₀) (modScaledBump_support hw γ₀)
  rw [← hK₀, ← hC] at hW
  have h1 : 16 * K₀ * (C + Real.log (|γ₀| + 4)) ≤ 16 * K₀ * (C + L) :=
    mul_le_mul_of_nonneg_left (by linarith) (by positivity)
  have h2 : C + L ≤ (C + 1) * L := by have := mul_le_mul_of_nonneg_left hL1 hC0; linarith
  have h3 : 16 * K₀ * (C + L) ≤ 16 * K₀ * ((C + 1) * L) :=
    mul_le_mul_of_nonneg_left h2 (by positivity)
  linarith

/-- `Ξ/(|D|(e^κ − 1)) ≤ A_w L` for `κ ≥ 1`, `|D| ≥ a_w²/(2e)` and `|M| + W ≤ 32(e^{w/2}B_w)²(C + 1)L`. -/
theorem xi_ratio_le {w : ℝ} (hw : 0 < w) {M W D κ L : ℝ} (hκ : 1 ≤ κ)
    (hD : centerAmplitude w ^ 2 / (2 * Real.exp 1) ≤ D) (hL : 0 ≤ L)
    (hMW : |M| + W ≤ 32 * (Real.exp (w / 2) * scaledBumpDecay w) ^ 2 *
      (xiLineTwoLogDerivConstant + 1) * L) :
    4 * |M| + 4 * W + 3840 * L * D * Real.exp κ ≤ twinTightConstant w * L * (D * (Real.exp κ - 1)) := by
  set K₀ := (Real.exp (w / 2) * scaledBumpDecay w) ^ 2 with hK₀
  set C := xiLineTwoLogDerivConstant with hC
  set a := centerAmplitude w with ha
  have ha0 : 0 < a := centerAmplitude_pos hw
  have hK0 : 0 ≤ K₀ := by positivity
  have hC0 : 0 ≤ C := xiLineTwoLogDerivConstant_nonneg
  have hE := Real.exp_pos 1
  have he1 : 0 < Real.exp 1 - 1 := by linarith [Real.add_one_lt_exp (one_ne_zero (α := ℝ))]
  have hE1 : Real.exp 1 - 1 ≤ Real.exp κ - 1 := by linarith [Real.exp_le_exp.mpr hκ]
  have hε0 : 0 < a ^ 2 / (2 * Real.exp 1) := by positivity
  have hD0 : 0 < D := lt_of_lt_of_le hε0 hD
  have hratio : Real.exp κ ≤ 8 / 5 * (Real.exp κ - 1) := by
    have : (8 : ℝ) / 3 ≤ Real.exp 1 := by linarith [Real.exp_one_gt_d9]
    linarith
  -- the mass part
  have hm1 : 4 * |M| + 4 * W ≤ 256 * Real.exp 1 * K₀ * (C + 1) / ((Real.exp 1 - 1) * a ^ 2) * L *
      (D * (Real.exp κ - 1)) := by
    have h1 : (a ^ 2 / (2 * Real.exp 1)) * (Real.exp 1 - 1) ≤ D * (Real.exp κ - 1) :=
      mul_le_mul hD hE1 he1.le hD0.le
    have e : 256 * Real.exp 1 * K₀ * (C + 1) / ((Real.exp 1 - 1) * a ^ 2) * L *
        ((a ^ 2 / (2 * Real.exp 1)) * (Real.exp 1 - 1)) = 4 * (32 * K₀ * (C + 1) * L) := by
      field_simp; ring
    have h2 : 0 ≤ 256 * Real.exp 1 * K₀ * (C + 1) / ((Real.exp 1 - 1) * a ^ 2) * L := by positivity
    have := mul_le_mul_of_nonneg_left h1 h2
    linarith
  have hm2 : 3840 * L * D * Real.exp κ ≤ 6144 * L * (D * (Real.exp κ - 1)) := by
    have := mul_le_mul_of_nonneg_left hratio (show 0 ≤ 3840 * L * D by positivity)
    linarith
  rw [twinTightConstant, ← hK₀, ← hC, ← ha]
  nlinarith

/-! ### Attained tops at a logarithmic lag -/

/-- The arithmetic of the collapse at an attained top. -/
theorem attained_log_arith {D Pr ε K u Ξ g V r κ Q Q₂ κ₀ A L E c : ℝ} {p m k : ℕ}
    (hD : 0 < D) (hu : 0 < u) (hE : 0 < E) (hε : 0 ≤ ε) (hg : 0 ≤ g) (hr : 0 < r) (hV : 0 < V)
    (hκQ : 0 < κ * Q)
    (hcol : D * Pr * ε ^ p * K ≤ u * (c * Ξ / r ^ (2 * k + 1)))
    (hPr : g ^ p ≤ Pr) (hK : u * E * V ^ m / (κ * Q) ≤ K) (hΞ : Ξ ≤ A * L * (D * E))
    (hc : 0 ≤ c) (hQ : κ * Q ≤ 2 * κ₀ * Q₂) (hAL : 0 ≤ A * L) :
    g ^ p * ε ^ p * V ^ m * r ^ (2 * k + 1) ≤ c * (2 * κ₀ * Q₂) * (A * L) := by
  have hK0 : 0 ≤ u * E * V ^ m / (κ * Q) := by positivity
  have hgp : 0 ≤ g ^ p := by positivity
  have hεp : 0 ≤ ε ^ p := by positivity
  have hPr0 : 0 ≤ Pr := hgp.trans hPr
  have h1 : D * g ^ p * ε ^ p * (u * E * V ^ m / (κ * Q)) ≤ D * Pr * ε ^ p * K :=
    mul_le_mul (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hPr hD.le) hεp) hK hK0
      (by positivity)
  have h2 : u * (c * Ξ / r ^ (2 * k + 1)) ≤ u * (c * (A * L * (D * E)) / r ^ (2 * k + 1)) := by
    gcongr
  have h3 := (h1.trans hcol).trans h2
  have hr0 : 0 < r ^ (2 * k + 1) := by positivity
  have e1 : D * g ^ p * ε ^ p * (u * E * V ^ m / (κ * Q)) =
      (u * D * E) * (g ^ p * ε ^ p * V ^ m / (κ * Q)) := by ring
  have e2 : u * (c * (A * L * (D * E)) / r ^ (2 * k + 1)) =
      (u * D * E) * (c * (A * L) / r ^ (2 * k + 1)) := by ring
  rw [e1, e2] at h3
  have h4 := le_of_mul_le_mul_left h3 (by positivity)
  rw [div_le_div_iff₀ hκQ hr0] at h4
  calc g ^ p * ε ^ p * V ^ m * r ^ (2 * k + 1) ≤ c * (A * L) * (κ * Q) := h4
    _ ≤ c * (A * L) * (2 * κ₀ * Q₂) := by gcongr
    _ = _ := by ring

/-- **An attained top is visible at a lag logarithmic in the separation.** Let `½ + z₀` be a zero of
largest real part `½ + δ₀` at height `γ₀ ≥ T_w`, `Γ = recordHeightEnvelope w γ₀`, let
`P ≥ 80 log(180Γ)` (the local zero count), and let the zeros in the box `|Im ρ| ≤ Γ + 1`,
`Re ρ ≥ ½ + δ₀/4` keep mutual distance `≥ g`. Let
`k ≥ 1`, `κ₀ ≥ 1`, `r = δ₀/8`, `2κ₀/V ≤ δ₀/16`, `V ≥ π(k + P)`, `Vr ≥ 4π(k + P)`,
`V δ₀ ≥ 2 log(160 log(180Γ)(e^{w/2}B_w)²/a_w²)`, and for every `p ≤ P`
`(8/3)^p (4/3)^k 2κ₀ (4κ₀² + 4π²(k+p)²)^{k+p} A_w log(180(Γ + 6))
  < (g κ₀/(2(P + 1)))^p V^{2k+p+1} r^{2k+1}`.
Then some difference test of the bump modulated to `γ₀` is Weil negative at a lag `v ∈ [0, V]`. -/
theorem zeta_attained_top_visible_log {w : ℝ} (hw : 0 < w) {z₀ : ℂ}
    (hz₀ : (1 / 2 + z₀) ∈ zetaZeroConfig.carrier) (hre₀ : 0 < z₀.re)
    (hTw : nearTopHeight w ≤ z₀.im)
    (htop : ∀ ρ ∈ zetaZeroConfig.carrier, ρ.re - 1 / 2 ≤ z₀.re) {P : ℕ}
    (hP : 80 * Real.log (180 * recordHeightEnvelope w z₀.im) ≤ P)
    {g : ℝ} (hg : 0 < g)
    (hsep : ∀ ρ ∈ zetaZeroConfig.carrier, ∀ ρ' ∈ zetaZeroConfig.carrier, ρ ≠ ρ' →
      |ρ.im| ≤ recordHeightEnvelope w z₀.im + 1 → |ρ'.im| ≤ recordHeightEnvelope w z₀.im + 1 →
      1 / 2 + z₀.re / 4 ≤ ρ.re → 1 / 2 + z₀.re / 4 ≤ ρ'.re → g ≤ ‖ρ - ρ'‖)
    {V κ₀ : ℝ} {k : ℕ} (hk : 1 ≤ k) (hκ₀ : 1 ≤ κ₀) (hV : 0 < V)
    (hV2 : 2 * Real.log (160 * Real.log (180 * recordHeightEnvelope w z₀.im) *
        (Real.exp (w / 2) * scaledBumpDecay w) ^ 2 / centerAmplitude w ^ 2) ≤ z₀.re * V)
    (hκV : 2 * κ₀ / V ≤ z₀.re / 16) (hVk : π * (k + P : ℕ) ≤ V)
    (hVr : 4 * π * (k + P : ℕ) ≤ V * (z₀.re / 8))
    (hmain : ∀ p : ℕ, p ≤ P → (8 / 3) ^ p * (4 / 3) ^ k * (2 * κ₀) *
      (4 * κ₀ ^ 2 + 4 * π ^ 2 * (k + p : ℕ) ^ 2) ^ (k + p) * twinTightConstant w *
        Real.log (180 * (recordHeightEnvelope w z₀.im + 6)) <
      (g * κ₀ / (2 * (P + 1))) ^ p * V ^ (2 * k + p + 1) * (z₀.re / 8) ^ (2 * k + 1)) :
    ∃ v ∈ Icc (0 : ℝ) V, (zetaZeroConfig.W (twoBump (modScaledBump w z₀.im) v (-1))
      (twoBump (modScaledBump w z₀.im) v (-1))).re < 0 := by
  classical
  by_contra hneg
  push Not at hneg
  set b := modScaledBump w z₀.im with hbdef
  set D := evenCoeff zetaZeroConfig b with hDdef
  set Γ := recordHeightEnvelope w z₀.im with hΓdef
  set r : ℝ := z₀.re / 8 with hr
  have hpos₀ : 0 < z₀.im := lt_of_lt_of_le (by unfold nearTopHeight; positivity) hTw
  have hstrip := zetaZeroConfig.strip _ hz₀
  have hre₀1 : z₀.re ≤ 1 / 2 := by
    have e : (1 / 2 + z₀).re = 1 / 2 + z₀.re := by simp
    linarith [hstrip.2]
  have hr0 : 0 < r := by rw [hr]; positivity
  have hr1 : r ≤ 1 := by rw [hr]; linarith
  have hmem : ∀ x : ℂ, D x ≠ 0 → (1 / 2 + x) ∈ zetaZeroConfig.carrier := fun x hx => by
    rcases mem_of_evenCoeff_ne_zero hx with h | h
    · exact h
    · have := conj_mem_zetaZeroConfig h
      have e : conj (1 / 2 + conj x) = 1 / 2 + x := by apply Complex.ext <;> simp
      rwa [e] at this
  have htop' : ∀ z, D z ≠ 0 → z.re ≤ z₀.re + 1 / V := fun z hz => by
    have := htop _ (hmem z hz)
    have e : (1 / 2 + z).re = 1 / 2 + z.re := by simp
    have : 0 < 1 / V := one_div_pos.mpr hV
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
  -- lower bounds for the record factor
  obtain ⟨L, hL⟩ : ∃ L : ℝ, L = Real.log (180 * (|z₁.im| + 6)) := ⟨_, rfl⟩
  obtain ⟨LΓ, hLΓ⟩ : ∃ LΓ : ℝ, LΓ = Real.log (180 * (Γ + 6)) := ⟨_, rfl⟩
  have hz₁box : |(1 / 2 + z₁).im| ≤ Γ + 1 ∧ 1 / 2 + z₀.re / 4 ≤ (1 / 2 + z₁).re := by
    have e1 : (1 / 2 + z₁).im = z₁.im := by simp
    have e2 : (1 / 2 + z₁).re = 1 / 2 + z₁.re := by simp
    rw [e1, e2]
    exact ⟨by linarith only [hup], by linarith only [hre₁, hre₀]⟩
  have hPr : g ^ p ≤ ∏ z ∈ S.erase z₁, ‖z - z₁‖ := by
    rw [hp, ← Finset.prod_const]
    refine Finset.prod_le_prod (fun _ _ => hg.le) fun z hz => ?_
    have hb := hTbox z (hST hz)
    have hne : (1 / 2 + z) ≠ 1 / 2 + z₁ := fun h => (Finset.mem_erase.mp hz).1 (by simpa using h)
    have := hsep _ hb.1 _ (hmem z₁ hz₁) hne hb.2.1 hz₁box.1 hb.2.2 hz₁box.2
    rwa [show (1 / 2 + z) - (1 / 2 + z₁) = z - z₁ by ring] at this
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
  have hfin := attained_log_arith (D := ‖D z₁‖) (u := u) (E := Real.exp κ - 1)
    (norm_pos_iff.mpr hz₁) hu0 hE hε0 hg.le hr0 hV (mul_pos hκ0 hQ0) hcol hPr hK hΞ hc0
    hQQ (mul_nonneg hA0 hL0) (p := p) (m := 2 * (k + p) + 1) (k := k)
  have hcmp := hmain p hpP
  rw [← hQ₂, ← hLΓ] at hcmp
  have e : g ^ p * ε ^ p * V ^ (2 * (k + p) + 1) =
      (g * κ₀ / (2 * (P + 1))) ^ p * V ^ (2 * k + p + 1) := by
    have hVne : V ≠ 0 := hV.ne'
    rw [hε, show 2 * (k + p) + 1 = (2 * k + p + 1) + p by ring, pow_add, div_pow, div_pow, mul_pow]
    field_simp
    rw [mul_pow]
  have hfin' : (g * κ₀ / (2 * (P + 1))) ^ p * V ^ (2 * k + p + 1) * r ^ (2 * k + 1) ≤
      (8 / 3) ^ p * (4 / 3) ^ k * (2 * κ₀) * Q₂ * twinTightConstant w * LΓ := by
    rw [← e]
    refine hfin.trans ?_
    have h1 : twinTightConstant w * L ≤ twinTightConstant w * LΓ := mul_le_mul_of_nonneg_left hLL hA0
    have h2 : 0 ≤ (8 / 3) ^ p * (4 / 3) ^ k * (2 * κ₀ * Q₂) := by
      have hQ₂0 : 0 ≤ Q₂ := by
        rw [hQ₂]
        have : 0 < 4 * κ₀ ^ 2 + 4 * π ^ 2 * ((k + p : ℕ) : ℝ) ^ 2 := by
          have := hbase (2 * κ₀) (by linarith only [hκ₀0])
          have e : (2 * κ₀) ^ 2 = 4 * κ₀ ^ 2 := by ring
          linarith only [this, e]
        exact (pow_pos this _).le
      exact mul_nonneg hc0 (mul_nonneg (by linarith only [hκ₀0]) hQ₂0)
    calc (8 / 3) ^ p * (4 / 3) ^ k * (2 * κ₀ * Q₂) * (twinTightConstant w * L)
        ≤ (8 / 3) ^ p * (4 / 3) ^ k * (2 * κ₀ * Q₂) * (twinTightConstant w * LΓ) :=
          mul_le_mul_of_nonneg_left h1 h2
      _ = _ := by ring
  linarith only [hfin', hcmp]

/-- **The data of an attained top exist.** The zeros of `ζ` in the box `|Im ρ| ≤ H`, `Re ρ ≥ ½ + d`
are finitely many and keep a positive mutual distance: there are `P` and `g > 0` as in
`zeta_attained_top_visible_log`. -/
theorem exists_box_count_and_separation (H d : ℝ) :
    ∃ P : ℕ, ∃ g > 0, (∀ F : Finset ℂ, (∀ ρ ∈ F, ρ ∈ zetaZeroConfig.carrier ∧ |ρ.im| ≤ H ∧
        1 / 2 + d ≤ ρ.re) → F.card ≤ P) ∧
      ∀ ρ ∈ zetaZeroConfig.carrier, ∀ ρ' ∈ zetaZeroConfig.carrier, ρ ≠ ρ' →
        |ρ.im| ≤ H → |ρ'.im| ≤ H → 1 / 2 + d ≤ ρ.re → 1 / 2 + d ≤ ρ'.re → g ≤ ‖ρ - ρ'‖ := by
  classical
  have hfin := zetaZeroConfig.finite_window (-|H| - 1) |H|
  obtain ⟨g, hg, hsep⟩ := exists_separation_in_box H d
  refine ⟨hfin.toFinset.card, g, hg, fun F hF => Finset.card_le_card fun ρ hρ => ?_, hsep⟩
  obtain ⟨h1, h2, -⟩ := hF ρ hρ
  rw [Set.Finite.mem_toFinset]
  refine ⟨h1, ?_, (le_abs_self _).trans (h2.trans (le_abs_self H))⟩
  linarith [neg_abs_le ρ.im, abs_nonneg H, le_abs_self H]

end GaloisForLFunctions.SquareRootThreshold
