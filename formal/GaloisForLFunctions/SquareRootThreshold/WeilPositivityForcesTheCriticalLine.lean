import GaloisForLFunctions.SquareRootThreshold.ExponentialGrowthRateOfExponentialSums

/-!
# Every off-line zero is visible at a finite aperture

For a tempered configuration, any zero off the critical line makes the Weil form negative on
some compactly supported `C²` test (`offLine_visible`). The off-line zeros need not be finite in
number, and their real parts need not attain their supremum.

* **Mechanism** (`exists_minor_fails_of_top`). Fix a height `γ` carrying a zero right of the line
  and let `t₀` be the rightmost zero at that height with nonzero weight `q_{t₀}` for a bump `b`.
  If every two-point minor of `b` held, the off-line exponential sum
  `Σ_t q_t e^{(δ_t + iγ_t)v}` would stay bounded for `v ≥ 0`. Its exponent `δ_{t₀} + iγ` is
  rightmost on its horizontal line, and local finiteness separates that line from the others.
  A bounded exponential sum has no such pole (`eq_zero_of_norm_tsum_exp_le`), so `q_{t₀} = 0`,
  a contradiction.
* **Weil criterion for configurations** (`weil_nonneg_iff_onLine`). A tempered configuration is
  Weil positive on all compactly supported `C²` tests iff all its zeros lie on the critical line.
* **Hodge criterion** (`hodgeIndex_forall_iff`). The Hodge index holds at every level iff every
  zero is on the line or at `s = 0, 1`. With the polar-free bump the weight at height `γ`
  vanishes only for the zero `1`, so any other off-line zero violates the Hodge index at a finite
  level (`offLine_not_hodgeIndex`).
* **For `ζ`** (`zeta_weil_nonneg_iff_onLine`, `zeta_hodgeIndex_forall_iff_onLine`). The
  nontrivial zeros form a tempered configuration avoiding `0, 1`: RH is equivalent to zero-side
  Weil positivity, and to the Hodge index at every level.

The zero side alone carries the criterion; the prime side and the explicit formula play no role.
The aperture is finite but not quantified here. Finite off-line sets have the explicit uniform
aperture of `finiteOffLine_visible`.
-/

open MeasureTheory Complex Set Filter Topology
open scoped Real ComplexConjugate

noncomputable section

namespace GaloisForLFunctions.SquareRootThreshold

open Zeta23 _root_.RHTower

/-- **Separation of heights.** Around any height `γ` there is a band `|Im ρ − γ| < η` in which every
zero lies exactly at height `γ`. -/
theorem exists_sep_height (Z : ZeroConfig) (γ : ℝ) :
    ∃ η : ℝ, 0 < η ∧ ∀ ρ ∈ Z.carrier, |ρ.im - γ| < η → ρ.im = γ := by
  classical
  set S := (Z.finite_window (γ - 1) (γ + 1)).toFinset with hS
  set G := insert (1 : ℝ) ((S.filter fun ρ => ρ.im ≠ γ).image fun ρ => |ρ.im - γ|) with hG
  have hGne : G.Nonempty := Finset.insert_nonempty _ _
  refine ⟨G.min' hGne, ?_, fun ρ hρ hlt => ?_⟩
  · rcases Finset.mem_insert.mp (G.min'_mem hGne) with h | h
    · rw [h]; exact one_pos
    obtain ⟨ρ, hρ, h⟩ := Finset.mem_image.mp h
    rw [← h]
    exact abs_pos.mpr (sub_ne_zero.mpr (Finset.mem_filter.mp hρ).2)
  · by_contra hne
    have h1 : G.min' hGne ≤ 1 := G.min'_le _ (Finset.mem_insert_self _ _)
    have hlt1 : |ρ.im - γ| < 1 := hlt.trans_le h1
    have hmem : ρ ∈ S := by
      rw [hS, Set.Finite.mem_toFinset]
      refine ⟨hρ, ?_, ?_⟩ <;> linarith [(abs_lt.mp hlt1).1, (abs_lt.mp hlt1).2]
    have := G.min'_le |ρ.im - γ| (Finset.mem_insert_of_mem
      (Finset.mem_image.mpr ⟨ρ, Finset.mem_filter.mpr ⟨hmem, hne⟩, rfl⟩))
    linarith

/-- At each height a finite set of zeros right of the line; any nonempty subfamily cut out by a
predicate has a rightmost member. -/
theorem exists_top_at_height (Z : ZeroConfig) {t : ℂ} (ht : t ∈ rightZeros Z) (P : ℂ → Prop)
    (hP : P t) : ∃ t₀ ∈ rightZeros Z, t₀.im = t.im ∧ P t₀ ∧
      ∀ t' ∈ rightZeros Z, t'.im = t.im → P t' → t'.re ≤ t₀.re := by
  classical
  set F := (Z.finite_window (t.im - 1) t.im).toFinset.filter
    fun z => 1 / 2 < z.re ∧ z.im = t.im ∧ P z with hF
  have hmem : ∀ z ∈ rightZeros Z, z.im = t.im → P z → z ∈ F := fun z hz him hPz => by
    rw [hF, Finset.mem_filter, Set.Finite.mem_toFinset]
    exact ⟨⟨hz.1, by linarith, by linarith⟩, hz.2, him, hPz⟩
  obtain ⟨t₀, ht₀, hmax⟩ := Finset.exists_max_image F (fun z => z.re) ⟨t, hmem t ht rfl hP⟩
  rw [hF, Finset.mem_filter, Set.Finite.mem_toFinset] at ht₀
  exact ⟨t₀, ⟨ht₀.1.1, ht₀.2.1⟩, ht₀.2.2.1, ht₀.2.2.2,
    fun t' ht' him hPt' => hmax t' (hmem t' ht' him hPt')⟩

/-- **A top zero forces exponentially growing minors.** Let `t₀` be the rightmost zero right of the
line at its height among those with nonzero weight, with nonzero weight itself, and let
`0 ≤ σ < Re t₀ − ½`. For every `K` some lag `v ≥ 0` has
`|S(v) + conj S(−v)| > 2 Re S(0) + K e^{σv}`. -/
theorem exists_minor_gt_of_top (Z : ZeroConfig) (hZ : TemperedConfig Z) {b : ℝ → ℂ}
    (hb : ContDiff ℝ 2 b) {w : ℝ} (hbs : ∀ u, b u ≠ 0 → |u| ≤ w) {t₀ : ℂ}
    (ht₀ : t₀ ∈ rightZeros Z) (hq₀ : offLineWeight b (Z.mult t₀) t₀ ≠ 0)
    (htop : ∀ t ∈ rightZeros Z, t.im = t₀.im → offLineWeight b (Z.mult t) t ≠ 0 → t.re ≤ t₀.re)
    {σ : ℝ} (hσ0 : 0 ≤ σ) (hσ : σ < t₀.re - 1 / 2) (K : ℝ) :
    ∃ v : ℝ, 0 ≤ v ∧ 2 * (lagStructure Z b 0).re + K * Real.exp (σ * v) <
      ‖lagStructure Z b v + conj (lagStructure Z b (-v))‖ := by
  classical
  have hbc : HasCompactSupport b := hasCompactSupport_of_support_subset_abs hbs
  by_contra hcon
  push Not at hcon
  set q : ℂ → ℂ := fun t => offLineWeight b (Z.mult t) t with hq
  set M := onLineMassOf Z b with hM
  have hM0 : 0 ≤ M := tsum_nonneg fun ρ => by split_ifs <;> positivity
  set Q := ∑' t : rightZeros Z, ‖q t‖ with hQ
  have hQ0 : 0 ≤ Q := tsum_nonneg fun _ => norm_nonneg _
  set K' := 2 * M + 3 * Q + |K| with hK'def
  have hbound : ∀ v : ℝ, 0 ≤ v → ‖∑' t : rightZeros Z, q t *
      (Real.exp (((t : ℂ).re - 1 / 2) * v) : ℂ) * cexp (I * (t : ℂ).im * v)‖ ≤
        K' * Real.exp (σ * v) := by
    intro v hv
    obtain ⟨h1, -, h3⟩ := rightZeros_minor_bounds Z hZ hb hbs hv
    have h0 := (abs_le.mp h3).2
    have hc := hcon v hv
    have he : 1 ≤ Real.exp (σ * v) := Real.one_le_exp (mul_nonneg hσ0 hv)
    have hK : K * Real.exp (σ * v) ≤ |K| * Real.exp (σ * v) :=
      mul_le_mul_of_nonneg_right (le_abs_self K) (Real.exp_pos _).le
    have hA : ‖∑' t : rightZeros Z, q t *
        (Real.exp (((t : ℂ).re - 1 / 2) * v) : ℂ) * cexp (I * (t : ℂ).im * v)‖ ≤
          2 * M + 3 * Q + |K| * Real.exp (σ * v) := by
      have hQe : ∑' t : rightZeros Z, ‖offLineWeight b (Z.mult t) t‖ = Q := rfl
      have hMe : onLineMassOf Z b = M := rfl
      have hAe : ‖∑' t : rightZeros Z, offLineWeight b (Z.mult t) t *
          (Real.exp (((t : ℂ).re - 1 / 2) * v) : ℂ) * cexp (I * (t : ℂ).im * v)‖ =
          ‖∑' t : rightZeros Z, q t *
            (Real.exp (((t : ℂ).re - 1 / 2) * v) : ℂ) * cexp (I * (t : ℂ).im * v)‖ := rfl
      rw [hQe, hMe, hAe] at h1
      rw [hQe, hMe] at h0
      have hKe : 0 ≤ |K| * Real.exp (σ * v) := by positivity
      linarith
    calc _ ≤ 2 * M + 3 * Q + |K| * Real.exp (σ * v) := hA
      _ ≤ (2 * M + 3 * Q) * Real.exp (σ * v) + |K| * Real.exp (σ * v) := by
          have : 0 ≤ 2 * M + 3 * Q := by positivity
          nlinarith
      _ = K' * Real.exp (σ * v) := by rw [hK'def]; ring
  have hsum0 : Summable fun t : rightZeros Z => lagTerm Z b 0 t := by
    have hF : Summable (Z.carrier.indicator (lagTerm Z b 0)) :=
      summable_subtype_iff_indicator.mp (summable_lagStructure Z hZ hb hbs 0)
    exact summable_subtype_iff_indicator.mpr (summable_indicator_of_subset (fun z hz => hz.1) hF)
  have hqs : Summable fun t : rightZeros Z => ‖q t‖ := by
    refine hsum0.norm.congr fun t => ?_
    rw [lagTerm_eq_weight hb.continuous hbc, norm_mul, norm_mul]
    simp only [Complex.ofReal_zero, mul_zero, Complex.exp_zero, Real.exp_zero, Complex.ofReal_one,
      norm_one, mul_one]
    rfl
  -- the exponential sum over the zeros of nonzero weight
  haveI : Countable (rightZeros Z) := ((carrier_countable Z).mono fun z hz => hz.1).to_subtype
  set S : Set (rightZeros Z) := {t | q t ≠ 0} with hS
  set lam : S → ℂ := fun t => (((t.1 : ℂ).re - 1 / 2 : ℝ) : ℂ) + I * ((t.1 : ℂ).im : ℂ) with hlamdef
  have hlre : ∀ t : S, (lam t).re = (t.1 : ℂ).re - 1 / 2 := fun t => by simp [hlamdef]
  have hlim : ∀ t : S, (lam t).im = (t.1 : ℂ).im := fun t => by simp [hlamdef]
  have hlamA : ∀ t : S, (lam t).re ≤ 1 / 2 := fun t => by
    rw [hlre]
    linarith [(Z.strip _ t.1.2.1).2]
  set t₁ : S := ⟨⟨t₀, ht₀⟩, hq₀⟩ with ht₁
  obtain ⟨η, hη, hsepZ⟩ := exists_sep_height Z t₀.im
  have hK'' : ∀ v : ℝ, 0 ≤ v →
      ‖∑' t : S, q t * cexp (lam t * v)‖ ≤ K' * Real.exp (σ * v) := by
    intro v hv
    have hsupp : Function.support (fun t : rightZeros Z => q t * cexp
        (((((t : ℂ).re - 1 / 2 : ℝ) : ℂ) + I * ((t : ℂ).im : ℂ)) * v)) ⊆ S := fun t ht h0 =>
      ht (by simp only [h0, zero_mul])
    rw [tsum_subtype_eq_of_support_subset hsupp]
    refine le_of_eq_of_le (congrArg norm (tsum_congr fun t => ?_)) (hbound v hv)
    rw [add_mul, Complex.exp_add, ← Complex.ofReal_mul, ← Complex.ofReal_exp]
    ring_nf
  have hq0 := eq_zero_of_norm_tsum_exp_le_exp (lam := lam) (q := fun t : S => q t)
    ((hqs.comp_injective Subtype.val_injective)) hlamA t₁ (by rw [hlre]; exact hσ)
    (fun t him => by
      rw [hlre, hlre]
      rw [hlim, hlim] at him
      have := htop t.1 t.1.2 him t.2
      linarith)
    (fun t hl => by
      have hre := congrArg Complex.re hl
      have him := congrArg Complex.im hl
      rw [hlre, hlre] at hre
      rw [hlim, hlim] at him
      exact Subtype.ext (Subtype.ext (Complex.ext (by linarith) him)))
    hη (fun t hlt => by
      rw [hlim, hlim] at hlt ⊢
      exact hsepZ _ t.1.2.1 hlt) hK''
  exact hq₀ hq0

/-- **A top zero breaks a two-point minor.** If `t₀` is the rightmost zero right of the line at its
height among those with nonzero weight, and its own weight is nonzero, some two-point minor of `b`
fails. -/
theorem exists_minor_fails_of_top (Z : ZeroConfig) (hZ : TemperedConfig Z) {b : ℝ → ℂ}
    (hb : ContDiff ℝ 2 b) {w : ℝ} (hbs : ∀ u, b u ≠ 0 → |u| ≤ w) {t₀ : ℂ}
    (ht₀ : t₀ ∈ rightZeros Z) (hq₀ : offLineWeight b (Z.mult t₀) t₀ ≠ 0)
    (htop : ∀ t ∈ rightZeros Z, t.im = t₀.im → offLineWeight b (Z.mult t) t ≠ 0 → t.re ≤ t₀.re) :
    ∃ v : ℝ, 0 ≤ v ∧
      2 * (lagStructure Z b 0).re < ‖lagStructure Z b v + conj (lagStructure Z b (-v))‖ := by
  obtain ⟨v, hv, h⟩ := exists_minor_gt_of_top Z hZ hb hbs ht₀ hq₀ htop le_rfl
    (by linarith [ht₀.2]) 0
  exact ⟨v, hv, by simpa using h⟩

theorem contDiff_modScaledBump_two (w γ : ℝ) : ContDiff ℝ 2 (modScaledBump w γ) :=
  (contDiff_modScaledBump w γ).of_le (by norm_num)

theorem modScaledBump_support {w : ℝ} (hw : 0 < w) (γ : ℝ) :
    ∀ u, modScaledBump w γ u ≠ 0 → |u| ≤ w := fun u hu => by
  by_contra h
  push Not at h
  exact hu (modScaledBump_eq_zero hw h.le)

theorem scaledBumpPolarFree_support {w : ℝ} (hw : 0 < w) (γ : ℝ) :
    ∀ u, scaledBumpPolarFree w γ u ≠ 0 → |u| ≤ w := fun u hu => by
  by_contra h
  push Not at h
  exact hu (scaledBumpPolarFree_eq_zero hw h)

theorem paperFT_scaledBumpPolarFree_half {w : ℝ} (hw : 0 < w) (γ : ℝ) :
    paperFT (scaledBumpPolarFree w γ) (I / 2) = 0 ∧ paperFT (scaledBumpPolarFree w γ) (-(I / 2)) = 0 := by
  have hpol : ∀ z : ℂ, z ^ 2 + 1 / 4 = 0 → paperFT (scaledBumpPolarFree w γ) z = 0 := fun z hz => by
    rw [paperFT_scaledBumpPolarFree hw, hz, neg_zero, zero_mul]
  exact ⟨hpol _ (by ring_nf; rw [Complex.I_sq]; ring), hpol _ (by ring_nf; rw [Complex.I_sq]; ring)⟩

/-- A zero off the line gives a zero right of the line, other than `1` when it is not `0` or `1`. -/
theorem exists_rightZero_of_offLine (Z : ZeroConfig) {ρ : ℂ} (hρ : ρ ∈ Z.carrier)
    (hre : ρ.re ≠ 1 / 2) : ∃ t ∈ rightZeros Z, (ρ ≠ 0 → ρ ≠ 1 → t ≠ 1) := by
  rcases lt_or_gt_of_ne hre with h | h
  · refine ⟨reflect ρ, ⟨Z.reflect_mem ρ hρ, by simp [reflect]; linarith⟩, fun h0 _ he => h0 ?_⟩
    rw [← Zeta23.reflect_reflect ρ, he]
    simp [reflect]
  · exact ⟨ρ, ⟨hρ, h⟩, fun _ h1 => h1⟩

/-- **An off-line zero breaks a modulated minor.** A tempered configuration with a zero off the
critical line has a height `γ` and a lag `v ≥ 0` at which the two-point minor of `κ` modulated to
`γ` fails. -/
theorem exists_minor_fails_modScaledBump (Z : ZeroConfig) (hZ : TemperedConfig Z) {ρ : ℂ}
    (hρ : ρ ∈ Z.carrier) (hre : ρ.re ≠ 1 / 2) :
    ∃ γ v : ℝ, 0 ≤ v ∧ 2 * (lagStructure Z (modScaledBump 1 γ) 0).re <
      ‖lagStructure Z (modScaledBump 1 γ) v + conj (lagStructure Z (modScaledBump 1 γ) (-v))‖ := by
  obtain ⟨t, ht, -⟩ := exists_rightZero_of_offLine Z hρ hre
  have hqne : ∀ t' ∈ rightZeros Z, t'.im = t.im →
      offLineWeight (modScaledBump 1 t.im) (Z.mult t') t' ≠ 0 := fun t' ht' him => by
    have hm := Z.one_le_mult t' ht'.1
    rw [offLineWeight, him]
    exact mul_ne_zero (Nat.cast_ne_zero.mpr (by omega))
      (pairWeight_modScaledBump_ne_zero one_pos _ _)
  obtain ⟨t₀, ht₀, him₀, -, htop⟩ := exists_top_at_height Z ht (fun _ => True) trivial
  obtain ⟨v, hv, hgt⟩ := exists_minor_fails_of_top Z hZ (contDiff_modScaledBump_two 1 t.im)
    (modScaledBump_support one_pos t.im) ht₀ (hqne t₀ ht₀ him₀)
    fun t' ht' him' _ => htop t' ht' (him'.trans him₀) trivial
  exact ⟨t.im, v, hv, hgt⟩

/-- **Every off-line zero is visible.** A tempered configuration with a zero off the critical line
has a compactly supported `C²` test with `Re W(f, f) < 0`. -/
theorem offLine_visible (Z : ZeroConfig) (hZ : TemperedConfig Z) {ρ : ℂ} (hρ : ρ ∈ Z.carrier)
    (hre : ρ.re ≠ 1 / 2) : ∃ f : ℝ → ℂ, ContDiff ℝ 2 f ∧ HasCompactSupport f ∧ (Z.W f f).re < 0 := by
  obtain ⟨γ, v, hv, hgt⟩ := exists_minor_fails_modScaledBump Z hZ hρ hre
  obtain ⟨f, hf, hfs, hneg⟩ := exists_visible_of_lagStructure Z hZ (contDiff_modScaledBump_two 1 γ)
    (modScaledBump_support one_pos γ) hv hgt
  exact ⟨f, hf, isCompact_Icc.of_isClosed_subset (isClosed_tsupport f) hfs, hneg⟩

/-- **Weil criterion for configurations.** A tempered configuration has `Re W(f, f) ≥ 0` for all
compactly supported `C²` tests iff all its zeros lie on the critical line. -/
theorem weil_nonneg_iff_onLine (Z : ZeroConfig) (hZ : TemperedConfig Z) :
    (∀ f : ℝ → ℂ, ContDiff ℝ 2 f → HasCompactSupport f → 0 ≤ (Z.W f f).re) ↔
      ∀ ρ ∈ Z.carrier, ρ.re = 1 / 2 := by
  refine ⟨fun hW ρ hρ => ?_, fun hon f _ _ => weil_nonneg_of_onLine Z hon f⟩
  by_contra hre
  obtain ⟨f, hf, hfc, hneg⟩ := offLine_visible Z hZ hρ hre
  exact absurd (hW f hf hfc) (not_le.mpr hneg)

/-- **An off-line zero other than `0, 1` breaks a polar-free minor.** There are a height `γ` and a
lag `v ≥ 0` at which the two-point minor of the polar-free bump modulated to `γ` fails. -/
theorem exists_minor_fails_polarFree (Z : ZeroConfig) (hZ : TemperedConfig Z) {ρ : ℂ}
    (hρ : ρ ∈ Z.carrier) (hre : ρ.re ≠ 1 / 2) (h0 : ρ ≠ 0) (h1 : ρ ≠ 1) :
    ∃ γ v : ℝ, 0 ≤ v ∧ 2 * (lagStructure Z (scaledBumpPolarFree 1 γ) 0).re <
      ‖lagStructure Z (scaledBumpPolarFree 1 γ) v +
        conj (lagStructure Z (scaledBumpPolarFree 1 γ) (-v))‖ := by
  obtain ⟨t, ht, ht1⟩ := exists_rightZero_of_offLine Z hρ hre
  have ht1 := ht1 h0 h1
  have hqt : offLineWeight (scaledBumpPolarFree 1 t.im) (Z.mult t) t ≠ 0 := by
    have hm := Z.one_le_mult t ht.1
    refine mul_ne_zero (Nat.cast_ne_zero.mpr (by omega))
      (pairWeight_polarFree_ne_zero one_pos (by linarith [ht.2]) ?_)
    rintro ⟨hi, hd⟩
    exact ht1 (Complex.ext (by simp; linarith) (by simpa using hi))
  obtain ⟨t₀, ht₀, him₀, hq₀, htop⟩ := exists_top_at_height Z ht
    (fun z => offLineWeight (scaledBumpPolarFree 1 t.im) (Z.mult z) z ≠ 0) hqt
  obtain ⟨v, hv, hgt⟩ := exists_minor_fails_of_top Z hZ (contDiff_scaledBumpPolarFree 1 t.im)
    (scaledBumpPolarFree_support one_pos t.im) ht₀ hq₀
    fun t' ht' him' hq' => htop t' ht' (him'.trans him₀) hq'
  exact ⟨t.im, v, hv, hgt⟩

/-- **Every off-line zero other than `0, 1` violates the Hodge index** at some finite level. -/
theorem offLine_not_hodgeIndex (Z : ZeroConfig) (hZ : TemperedConfig Z) {ρ : ℂ}
    (hρ : ρ ∈ Z.carrier) (hre : ρ.re ≠ 1 / 2) (h0 : ρ ≠ 0) (h1 : ρ ≠ 1) :
    ∃ a : ℝ, ¬ HodgeIndexAtLevel Z a := by
  obtain ⟨γ, v, hv, hgt⟩ := exists_minor_fails_polarFree Z hZ hρ hre h0 h1
  obtain ⟨hp, hn⟩ := paperFT_scaledBumpPolarFree_half one_pos γ
  exact ⟨v / 2 + 1, not_hodgeIndex_of_polarFree_minor Z hZ (contDiff_scaledBumpPolarFree 1 γ)
    (scaledBumpPolarFree_support one_pos γ) hp hn hv hgt le_rfl⟩

/-- **Hodge criterion for configurations.** A tempered configuration satisfies the Hodge index at
every level iff each of its zeros is on the critical line or at `s = 0, 1`. -/
theorem hodgeIndex_forall_iff (Z : ZeroConfig) (hZ : TemperedConfig Z) :
    (∀ a, HodgeIndexAtLevel Z a) ↔ ∀ ρ ∈ Z.carrier, ρ.re = 1 / 2 ∨ ρ = 0 ∨ ρ = 1 := by
  refine ⟨fun hH ρ hρ => ?_, fun hon a => hodgeIndex_of_onLine_or_poles Z hon a⟩
  by_contra hcon
  push Not at hcon
  obtain ⟨a, ha⟩ := offLine_not_hodgeIndex Z hZ hρ hcon.1 hcon.2.1 hcon.2.2
  exact ha (hH a)

/-- **For `ζ`.** The zero-side Weil form of the nontrivial zeros is nonnegative on all compactly
supported `C²` tests iff every nontrivial zero lies on the critical line. -/
theorem zeta_weil_nonneg_iff_onLine :
    (∀ f : ℝ → ℂ, ContDiff ℝ 2 f → HasCompactSupport f → 0 ≤ (zetaZeroConfig.W f f).re) ↔
      ∀ ρ ∈ zetaZeroConfig.carrier, ρ.re = 1 / 2 :=
  weil_nonneg_iff_onLine _ temperedConfig_zetaZeroConfig

/-- **For `ζ`, the Hodge index.** It holds at every level iff every nontrivial zero lies on the
critical line (`ζ` has no zero at `0` or `1`). -/
theorem zeta_hodgeIndex_forall_iff_onLine :
    (∀ a, HodgeIndexAtLevel zetaZeroConfig a) ↔ ∀ ρ ∈ zetaZeroConfig.carrier, ρ.re = 1 / 2 := by
  rw [hodgeIndex_forall_iff _ temperedConfig_zetaZeroConfig]
  refine ⟨fun h ρ hρ => ?_, fun h ρ hρ => Or.inl (h ρ hρ)⟩
  have hstrip : 0 < ρ.re ∧ ρ.re < 1 := hρ.2
  rcases h ρ hρ with h | rfl | rfl
  · exact h
  · simp at hstrip
  · simp at hstrip

end GaloisForLFunctions.SquareRootThreshold
