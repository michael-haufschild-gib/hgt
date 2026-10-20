import GaloisForLFunctions.SquareRootThreshold.InghamInequalityForSeparatedSpectra

/-!
# Resolution of the Weil form at a finite aperture

The Weil form determines a tempered configuration (`eq_of_weil_eq`), but through tests of
unbounded aperture. For on-line configurations with separated heights a finite aperture suffices,
and the threshold is exactly half the Nyquist aperture of the separation.

* **Resolution** (`eq_of_weil_eq_of_separated`). Two tempered configurations with all their zeros
  on the critical line, whose union has `g`-separated heights, and whose Weil forms agree on every
  `C²` test supported in `[−a, a]` with `a > π/(2g)`, are equal.
* **Sharpness** (`lattice_resolution_sharp`). The double lattice `{½ + 2πik/L}` and the simple
  lattice `{½ + πik/L}` are distinct on-line configurations of the same density with
  `π/L`-separated union. Their Weil forms agree on every test supported in `[−L/2, L/2]`, which
  is the aperture `π/(2g)` for `g = π/L`. So the resolution aperture of `g`-separated on-line
  configurations is exactly `π/(2g)`.

Proof of resolution. The two-bump tests at lags `|v| ≤ V` lie in the aperture, so the signed lag
structure `Σ_ρ c_ρ |h_γ(γ_ρ)|² e^{iγ_ρ v}` vanishes on `[−V, V]`. Its finite truncations are
uniformly small there, and Ingham's inequality (`ingham_inequality`) controls the coefficients of
a truncation by its mean square once `Vg > π`.
-/

open MeasureTheory Complex Set Filter Topology
open scoped Real ComplexConjugate

noncomputable section

namespace GaloisForLFunctions.SquareRootThreshold

open Zeta23 _root_.RHTower

/-- **Resolution of the Weil form.** Two tempered on-line configurations with `g`-separated union
and equal Weil forms on all `C²` tests supported in `[−a, a]`, `a > π/(2g)`, are equal. -/
theorem eq_of_weil_eq_of_separated (Z Z' : ZeroConfig) (hZ : TemperedConfig Z)
    (hZ' : TemperedConfig Z') (hon : ∀ ρ ∈ Z.carrier, ρ.re = 1 / 2)
    (hon' : ∀ ρ ∈ Z'.carrier, ρ.re = 1 / 2) {g : ℝ} (hg : 0 < g)
    (hsep : ∀ ρ ∈ Z.carrier ∪ Z'.carrier, ∀ ρ' ∈ Z.carrier ∪ Z'.carrier, ρ ≠ ρ' →
      g ≤ |ρ.im - ρ'.im|)
    {a : ℝ} (ha : π / (2 * g) < a)
    (hW : ∀ f : ℝ → ℂ, ContDiff ℝ 2 f → tsupport f ⊆ Icc (-a) a → Z.W f f = Z'.W f f) :
    Z.carrier = Z'.carrier ∧ ∀ ρ ∈ Z.carrier, Z.mult ρ = Z'.mult ρ := by
  classical
  set w := (a - π / (2 * g)) / 2 with hw
  have hw0 : 0 < w := by rw [hw]; linarith
  set V := 2 * (a - w) with hV
  have hπg : 0 < π / (2 * g) := by positivity
  have hV0 : 0 < V := by rw [hV, hw]; linarith
  have hVg : π < V * g := by
    have hV' : π / g < V := by
      rw [hV, hw, show π / g = 2 * (π / (2 * g)) by field_simp]
      linarith
    rwa [div_lt_iff₀ hg] at hV'
  refine eq_of_multDiff_eq_zero fun ρ₀ => ?_
  by_contra hc
  set γ := ρ₀.im with hγ
  set b := modScaledBump w γ with hbdef
  have hb : ContDiff ℝ 2 b := contDiff_modScaledBump_two w γ
  have hbs := modScaledBump_support hw0 γ
  have hbc : HasCompactSupport b := hasCompactSupport_of_support_subset_abs hbs
  set c := multDiff Z Z' with hcdef
  have hcoff : ∀ z, z.re ≠ 1 / 2 → c z = 0 := fun z hz => by
    by_contra hcz
    rcases mem_carrier_of_multDiff_ne_zero hcz with h | h
    · exact hz (hon z h)
    · exact hz (hon' z h)
  set G : ℂ → ℂ := fun z => c z * ((‖paperFT b z.im‖ ^ 2 : ℝ) : ℂ) with hG
  have hterm : ∀ (v : ℝ) (z : ℂ), coefTerm c b v z = G z * cexp (I * z.im * v) := by
    intro v z
    by_cases hz : z.re = 1 / 2
    · rw [coefTerm_onLine hb.continuous hbc c hz]
    · rw [coefTerm, hG]
      simp only
      rw [hcoff z hz]
      ring
  have hE : ∀ (z : ℂ) (α : ℝ), ‖cexp (I * z.im * α)‖ = 1 := fun z α => by
    rw [show I * (z.im : ℂ) * (α : ℂ) = ((z.im * α : ℝ) : ℂ) * I by push_cast; ring]
    exact Complex.norm_exp_ofReal_mul_I _
  have hGs : Summable fun z => ‖G z‖ :=
    ((lagStructure_sub_eq Z Z' hZ hZ' hb hbs 0).1.norm).congr fun z => by rw [hterm]; simp
  -- the signed lag structure vanishes on `[−V, V]`
  have hD : ∀ v ∈ Icc (-V) V, ∑' z, G z * cexp (I * z.im * v) = 0 := by
    intro v hv
    have hva : (((2 : ℕ) : ℝ) - 1) / 2 * |v| + w ≤ a := by
      have := abs_le.mpr hv
      push_cast
      rw [hV] at this
      linarith
    have hpol := lagStructure_eq_of_weil_twoBump_eq_at Z Z' hZ hZ' hb hbs |v| fun τ _ =>
      hW _ (contDiff_bumpTest hb |v| ![1, τ])
        (tsupport_bumpTest_subset hbs (abs_nonneg v) hva ![1, τ])
    have hS : lagStructure Z b v = lagStructure Z' b v := by
      rcases le_or_gt 0 v with h | h
      · rw [abs_of_nonneg h] at hpol
        exact hpol.1
      · rw [abs_of_neg h, neg_neg] at hpol
        exact hpol.2
    rw [← tsum_congr (hterm v), ← (lagStructure_sub_eq Z Z' hZ hZ' hb hbs v).2, hS, sub_self]
  -- the weight at `ρ₀`
  have hκ : paperFT b γ ≠ 0 := by
    have hmod : paperFT b γ = paperFT (scaledBump w) (((0 : ℝ) : ℂ) * I) := by
      rw [hbdef, show paperFT (modScaledBump w γ) γ = paperFT (scaledBump w) ((γ : ℂ) - γ) from
        paperFT_modulate (scaledBump w) γ γ]
      simp
    rw [hmod]
    intro h
    have := norm_paperFT_scaledBump_I_mul_ge hw0 0
    rw [h, norm_zero] at this
    have hpos : 0 < 4 * w * (Real.exp (-(w * |(0 : ℝ)|)) * ∫ u, weilBump u) := by
      have := weilBump.integral_pos (μ := MeasureTheory.volume)
      positivity
    linarith
  have hG₀ : G ρ₀ ≠ 0 := by
    refine mul_ne_zero hc ?_
    exact_mod_cast (pow_pos (norm_pos_iff.mpr hκ) 2).ne'
  set A := inghamConst V g * ‖G ρ₀‖ ^ 2 with hA
  have hA0 : 0 < A := mul_pos (inghamConst_pos hV0 hVg) (pow_pos (norm_pos_iff.mpr hG₀) 2)
  set ε := Real.sqrt (A / (4 * V + 1)) with hε
  have hε0 : 0 < ε := Real.sqrt_pos.mpr (by positivity)
  have hε2 : 2 * V * ε ^ 2 < A := by
    rw [hε, Real.sq_sqrt (by positivity), mul_div_assoc', div_lt_iff₀ (by positivity)]
    nlinarith
  -- a finite truncation with small tail
  obtain ⟨s, hs₀, hstail⟩ : ∃ s : Finset ℂ, ρ₀ ∈ s ∧ ∑' x : {x // x ∉ s}, ‖G x‖ < ε := by
    have h := (tendsto_tsum_compl_atTop_zero (fun z => ‖G z‖)).eventually (gt_mem_nhds hε0)
    obtain ⟨s, hs⟩ := (h.and (eventually_ge_atTop {ρ₀})).exists
    exact ⟨s, hs.2 (Finset.mem_singleton_self _), hs.1⟩
  set F := s.filter fun z => G z ≠ 0 with hF
  have hρ₀F : ρ₀ ∈ F := Finset.mem_filter.mpr ⟨hs₀, hG₀⟩
  have hsmall : ∀ α ∈ Icc (-V) V, ‖∑ z ∈ F, G z * cexp (I * z.im * α)‖ ≤ ε := by
    intro α hα
    have hsum : Summable fun z => G z * cexp (I * z.im * α) :=
      Summable.of_norm_bounded hGs fun z => by rw [norm_mul, hE z α, mul_one]
    have hsplit := hsum.sum_add_tsum_subtype_compl s
    rw [hD α hα] at hsplit
    have hFs : ∑ z ∈ F, G z * cexp (I * z.im * α) = ∑ z ∈ s, G z * cexp (I * z.im * α) := by
      rw [hF, Finset.sum_filter]
      refine Finset.sum_congr rfl fun z _ => ?_
      split_ifs with h
      · rfl
      · push Not at h
        rw [h, zero_mul]
    have htn : Summable fun x : {x // x ∉ s} => ‖G x‖ :=
      hGs.comp_injective Subtype.val_injective
    rw [hFs, show ∑ z ∈ s, G z * cexp (I * z.im * α) =
      -∑' x : {x // x ∉ s}, G x * cexp (I * (x : ℂ).im * α) by linear_combination hsplit, norm_neg]
    refine (norm_tsum_le_tsum_norm ?_).trans (le_of_eq_of_le ?_ hstail.le)
    · exact htn.congr fun x => (show ‖G x * cexp (I * ((x : ℂ).im : ℂ) * α)‖ = ‖G x‖ by
        rw [norm_mul, hE, mul_one]).symm
    · exact tsum_congr fun x => show ‖G x * cexp (I * ((x : ℂ).im : ℂ) * α)‖ = ‖G x‖ by
        rw [norm_mul, hE, mul_one]
  -- Ingham on the truncation
  have hIng := ingham_inequality (ι := F) (fun z => (z : ℂ).im) (fun z => G z) hg hV0 hVg
    (fun r t hrt => by
      have hr := (Finset.mem_filter.mp r.2).2
      have ht := (Finset.mem_filter.mp t.2).2
      exact hsep r (mem_carrier_of_multDiff_ne_zero (left_ne_zero_of_mul hr))
        t (mem_carrier_of_multDiff_ne_zero (left_ne_zero_of_mul ht)) fun h => hrt (Subtype.ext h))
  have hrw : ∀ α : ℝ, ∑ r : F, G r * cexp (I * (((r : ℂ).im : ℝ) : ℂ) * α) =
      ∑ z ∈ F, G z * cexp (I * z.im * α) := fun α =>
    Finset.sum_coe_sort F (fun z => G z * cexp (I * z.im * α))
  simp_rw [hrw] at hIng
  have hint : ∫ α in -V..V, ‖∑ z ∈ F, G z * cexp (I * z.im * α)‖ ^ 2 ≤ 2 * V * ε ^ 2 := by
    have hcont : Continuous fun α : ℝ => ‖∑ z ∈ F, G z * cexp (I * z.im * α)‖ ^ 2 := by fun_prop
    calc ∫ α in -V..V, ‖∑ z ∈ F, G z * cexp (I * z.im * α)‖ ^ 2
        ≤ ∫ _α in -V..V, ε ^ 2 := intervalIntegral.integral_mono_on (by linarith)
          (hcont.intervalIntegrable _ _) intervalIntegrable_const fun α hα =>
            pow_le_pow_left₀ (norm_nonneg _) (hsmall α hα) 2
      _ = 2 * V * ε ^ 2 := by rw [intervalIntegral.integral_const, smul_eq_mul]; ring
  have hsq : ‖G ρ₀‖ ^ 2 ≤ ∑ r : F, ‖G r‖ ^ 2 := by
    rw [Finset.sum_coe_sort F (fun z => ‖G z‖ ^ 2)]
    exact Finset.single_le_sum (f := fun z => ‖G z‖ ^ 2) (fun _ _ => by positivity) hρ₀F
  have : A ≤ 2 * V * ε ^ 2 := by
    calc A = inghamConst V g * ‖G ρ₀‖ ^ 2 := rfl
      _ ≤ inghamConst V g * ∑ r : F, ‖G r‖ ^ 2 :=
          mul_le_mul_of_nonneg_left hsq (inghamConst_pos hV0 hVg).le
      _ ≤ _ := hIng.trans hint
  linarith

/-- The on-line lattice `{½ + πik/L}` with simple zeros. -/
def simpleHalfLatticeConfig {L : ℝ} (hL : 0 < L) : ZeroConfig :=
  { onLineLatticeConfig (mul_pos two_pos hL) with
    mult := fun _ => 1
    one_le_mult := fun _ _ => le_rfl
    mult_reflect := fun _ _ => rfl }

theorem temperedConfig_simpleHalfLatticeConfig {L : ℝ} (hL : 0 < L) :
    TemperedConfig (simpleHalfLatticeConfig hL) := by
  obtain ⟨c, hc⟩ := hasSum_lattice_weight (mul_pos two_pos hL) 0 1
  exact ⟨c, by simpa [simpleHalfLatticeConfig, onLineLatticeConfig] using hc⟩

/-- Below its Nyquist aperture `L` the simple half-spacing lattice has Weil form `2L⟨f, g⟩`. -/
theorem W_simpleHalfLatticeConfig {L : ℝ} (hL : 0 < L) {f g : ℝ → ℂ} (hf : ContDiff ℝ 2 f)
    (hg : Continuous g) (hfs : tsupport f ⊆ Icc (-L) L) (hgs : tsupport g ⊆ Icc (-L) L) :
    (simpleHalfLatticeConfig hL).W f g = 2 * L * ∫ t, f t * conj (g t) := by
  have h2L : (0 : ℝ) < 2 * L := mul_pos two_pos hL
  have hL2 : 2 * L / 2 = L := by ring
  have hW := W_onLineLatticeConfig_of_le_nyquist h2L hf hg (by rwa [hL2]) (by rwa [hL2])
  have hhalf : (simpleHalfLatticeConfig hL).W f g = (1 / 2 : ℂ) * (onLineLatticeConfig h2L).W f g := by
    rw [ZeroConfig.W, ZeroConfig.W, ← tsum_mul_left]
    refine tsum_congr fun ρ => ?_
    simp only [ZeroConfig.Wsummand, simpleHalfLatticeConfig, onLineLatticeConfig]
    push_cast
    ring
  rw [hhalf, hW]
  push_cast
  ring

/-- **Sharpness of the resolution.** The double lattice `{½ + 2πik/L}` and the simple lattice
`{½ + πik/L}` are distinct tempered on-line configurations whose union is `π/L`-separated, and
their Weil forms agree on every `C²` test supported in `[−L/2, L/2]`. -/
theorem lattice_resolution_sharp {L : ℝ} (hL : 0 < L) :
    TemperedConfig (onLineLatticeConfig hL) ∧ TemperedConfig (simpleHalfLatticeConfig hL) ∧
    (∀ ρ ∈ (onLineLatticeConfig hL).carrier, ρ.re = 1 / 2) ∧
    (∀ ρ ∈ (simpleHalfLatticeConfig hL).carrier, ρ.re = 1 / 2) ∧
    (∀ ρ ∈ (onLineLatticeConfig hL).carrier ∪ (simpleHalfLatticeConfig hL).carrier,
      ∀ ρ' ∈ (onLineLatticeConfig hL).carrier ∪ (simpleHalfLatticeConfig hL).carrier,
        ρ ≠ ρ' → π / L ≤ |ρ.im - ρ'.im|) ∧
    (onLineLatticeConfig hL).carrier ≠ (simpleHalfLatticeConfig hL).carrier ∧
    ∀ f : ℝ → ℂ, ContDiff ℝ 2 f → tsupport f ⊆ Icc (-(L / 2)) (L / 2) →
      (onLineLatticeConfig hL).W f f = (simpleHalfLatticeConfig hL).W f f := by
  have hπL : 0 < π / L := by positivity
  -- every point of the union is `½ + i m π/L`
  have hform : ∀ ρ ∈ (onLineLatticeConfig hL).carrier ∪ (simpleHalfLatticeConfig hL).carrier,
      ρ.re = 1 / 2 ∧ ∃ m : ℤ, ρ.im = m * (π / L) := by
    rintro ρ (⟨k, rfl⟩ | ⟨k, rfl⟩)
    · refine ⟨by simp [verticalLatticePoint], 2 * k, ?_⟩
      simp only [verticalLatticePoint]
      push_cast
      field_simp
    · refine ⟨by simp [verticalLatticePoint], k, ?_⟩
      simp only [verticalLatticePoint]
      field_simp
  refine ⟨temperedConfig_onLineLatticeConfig hL, temperedConfig_simpleHalfLatticeConfig hL,
    fun ρ hρ => (hform ρ (Or.inl hρ)).1, fun ρ hρ => (hform ρ (Or.inr hρ)).1, ?_, ?_, ?_⟩
  · intro ρ hρ ρ' hρ' hne
    obtain ⟨hre, m, hm⟩ := hform ρ hρ
    obtain ⟨hre', m', hm'⟩ := hform ρ' hρ'
    have hmm : m ≠ m' := fun h => hne (Complex.ext (by rw [hre, hre']) (by rw [hm, hm', h]))
    have h1 : (1 : ℝ) ≤ |(m : ℝ) - m'| := by
      have : (1 : ℤ) ≤ |m - m'| := Int.one_le_abs (sub_ne_zero.mpr hmm)
      exact_mod_cast this
    rw [hm, hm', ← sub_mul, abs_mul, abs_of_pos hπL]
    nlinarith
  · intro h
    have hmem : verticalLatticePoint (2 * L) 0 1 ∈ (simpleHalfLatticeConfig hL).carrier := ⟨1, rfl⟩
    rw [← h] at hmem
    obtain ⟨k, hk⟩ := hmem
    have him := congrArg Complex.im hk
    simp only [verticalLatticePoint, Int.cast_one, one_mul] at him
    have h2 : ((2 * k - 1 : ℤ) : ℝ) * (π / L) = 0 := by
      push_cast
      linear_combination him
    rcases mul_eq_zero.mp h2 with h3 | h3
    · have : (2 * k - 1 : ℤ) = 0 := by exact_mod_cast h3
      omega
    · exact absurd h3 hπL.ne'
  · intro f hf hfs
    rw [W_onLineLatticeConfig_of_le_nyquist hL hf hf.continuous hfs hfs,
      W_simpleHalfLatticeConfig hL hf hf.continuous
        (hfs.trans (Icc_subset_Icc (by linarith) (by linarith)))
        (hfs.trans (Icc_subset_Icc (by linarith) (by linarith)))]

end GaloisForLFunctions.SquareRootThreshold
