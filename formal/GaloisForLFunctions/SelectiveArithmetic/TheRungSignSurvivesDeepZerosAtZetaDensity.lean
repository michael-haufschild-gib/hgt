import GaloisForLFunctions.ZeroConfigurationGeometry.TheZetaDensityBackgroundHasBoundedTrace
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.TemperedConfigurationPontryaginLaw
import GaloisForLFunctions.RHTower.ClusterRobustHodgeExclusion
import GaloisForLFunctions.WindowVisibilityLaw.OnsetApertureAndPositivityDictionary

/-!
# A positive window at zeta density can contain infinitely many deep zeros

An off-line lattice is positive below its Nyquist aperture, at any depth. Adding
the critical projection of zeta's divisor preserves positivity and gives zeta's
leading ordinate density: the extra count is only linear in the height.
The configuration depends on the chosen aperture.
-/

open Complex Filter Topology Set MeasureTheory
open Zeta23
open _root_.RHTower
open _root_.RHTower.LocalCountFalsifier
open GaloisForLFunctions.SquareRootThreshold
open GaloisForLFunctions.ZeroConfigurationGeometry

noncomputable section

namespace GaloisForLFunctions.SelectiveArithmetic

/-- For one tempered configuration, positivity along any unbounded aperture law
is equivalent to every zero lying on the critical line. -/
theorem onLine_iff_positive_along_unbounded_apertures {Z : ZeroConfig}
    (hZ : TemperedConfig Z) {r : ℝ → ℝ} (hr : Tendsto r atTop atTop) :
    (∀ ρ ∈ Z.carrier, ρ.re = 1 / 2) ↔
      ∀ᶠ T : ℝ in atTop, WindowVisibilityLaw.WindowPositiveAt Z (r T) := by
  constructor
  · intro hon
    exact Eventually.of_forall fun _ f _ _ =>
      SquareRootThreshold.re_W_nonneg_of_onLine Z hon f
  · intro hpos
    apply (WindowVisibilityLaw.onsetAperture_eq_top_iff_onLine hZ).mp
    cases he : WindowVisibilityLaw.onsetAperture Z with
    | bot =>
      have h := WindowVisibilityLaw.zero_le_onsetAperture Z
      rw [he] at h
      exact False.elim (by simpa using h)
    | top => rfl
    | coe b =>
      obtain ⟨T, hT, hTr⟩ := (hpos.and (hr.eventually_ge_atTop (max b 0 + 1))).exists
      have hr0 : 0 ≤ r T := by linarith only [hTr, le_max_right b 0]
      have hle := WindowVisibilityLaw.le_onsetAperture_of_windowPositiveAt hr0 hT
      rw [he, EReal.coe_le_coe_iff] at hle
      exfalso
      linarith only [hle, hTr, le_max_left b 0]

/-- The off-line lattice contributes only a linear number of zeros. -/
theorem offLineLattice_count_le_linear {L δ : ℝ} (hL : 0 < L)
    (hδ : 0 < δ) (hδ' : δ ≤ 1 / 2) {T : ℝ} (hT : 0 ≤ T) :
    ((offLineLatticeConfig hL hδ hδ').N 0 T : ℝ) ≤ (L / Real.pi + 2) * (T + 1) := by
  let Z := offLineLatticeConfig hL hδ hδ'
  let m := ⌊T⌋₊ + 1
  have hTm : T ≤ (m : ℝ) := by
    simpa only [m, Nat.cast_add, Nat.cast_one] using (Nat.lt_floor_add_one T).le
  have hmT : (m : ℝ) ≤ T + 1 := by
    dsimp [m]
    push_cast
    linarith only [Nat.floor_le hT]
  have hN (U : ℝ) : Z.N 0 U = Z.Nd 0 U := by
    unfold ZeroConfig.N ZeroConfig.Nd
    exact finsum_one
  have hmono : Z.Nd 0 T ≤ Z.Nd 0 (m : ℝ) := by
    apply Set.ncard_le_ncard _ (Z.finite_window 0 m)
    intro z hz
    exact ⟨hz.1, hz.2.1, hz.2.2.trans hTm⟩
  have hwin := Nd_le_sum_unit_N Z 0 m
  simp only [zero_add] at hwin
  have hsum : (∑ j ∈ Finset.range m, (Z.N j (j + 1) : ℝ)) ≤
      (m : ℝ) * (L / Real.pi + 2) := by
    calc
      _ ≤ ∑ _j ∈ Finset.range m, (L / Real.pi + 2) :=
        Finset.sum_le_sum fun j _ => offLineLatticeConfig_N_le hL hδ hδ' j
      _ = _ := by simp; ring
  have hbound : (Z.N 0 T : ℝ) ≤ (m : ℝ) * (L / Real.pi + 2) := by
    rw [hN]
    have hc : (Z.Nd 0 T : ℝ) ≤ ∑ j ∈ Finset.range m, (Z.N j (j + 1) : ℝ) := by
      exact_mod_cast hmono.trans hwin
    exact hc.trans hsum
  exact hbound.trans (by
    have hm := mul_le_mul_of_nonneg_right hmT (by positivity : 0 ≤ L / Real.pi + 2)
    nlinarith only [hm])

/-- Every fixed aperture admits zeta-density configurations with unbounded deep zeros.
The excess count is explicitly `O(T)`, hence smaller than the zeta main term. -/
theorem exists_zetaDensity_positive_window_deep_zeros {a δ : ℝ}
    (ha : 0 < a) (hδ : 0 < δ) (hδ' : δ ≤ 1 / 2) :
    ∃ (Z : ZeroConfig) (A C : ℝ), TemperedConfig Z ∧ 1 ≤ A ∧ 0 < C ∧
      (∀ t : ℝ, (Z.N t (t + 1) : ℝ) ≤ A * Real.log (|t| + 3)) ∧
      (∀ T : ℝ, 0 ≤ T →
        |(Z.N 0 T : ℝ) - (zetaZeroConfig.N 0 T : ℝ)| ≤ C * (T + 1)) ∧
      (∀ f : ℝ → ℂ, ContDiff ℝ 2 f → tsupport f ⊆ Icc (-a) a → 0 ≤ (Z.W f f).re) ∧
      ∀ T : ℝ, ∃ ρ ∈ Z.carrier, ρ.re = 1 / 2 + δ ∧ T ≤ ρ.im := by
  let L := 2 * a + 1
  have hL1 : 1 ≤ L := by dsimp [L]; linarith only [ha]
  have hL : 0 < L := zero_lt_one.trans_le hL1
  let Z₀ := offLineLatticeConfig hL hδ hδ'
  let Z := superpose Z₀ zetaDensityBackground
  have hoff : ∀ ρ ∈ Z₀.carrier, ρ.re ≠ 1 / 2 := by
    rintro _ (⟨k, rfl⟩ | ⟨k, rfl⟩) h
    all_goals simp only [verticalLatticePoint] at h; linarith only [h, hδ]
  have hd := disjoint_zetaDensityBackground_of_offLine hoff
  have ht₀ := temperedConfig_offLineLatticeConfig hL hδ hδ'
  have ht := temperedConfig_superpose hd ht₀ zetaDensityBackground_tempered
  obtain ⟨A, hA, hcount⟩ := Zeta23.RvM.zetaZeroConfig_local_count
  let C := L / Real.pi + 2
  have hC : 0 < C := by dsimp [C]; positivity
  have hlat := offLineLattice_masks_at_linear_level hL1 hδ hδ'
  refine ⟨Z, C + A, C, ht, by linarith only [hC, hA], hC, ?_, ?_, ?_, ?_⟩
  · intro t
    change ((superpose Z₀ zetaDensityBackground).N t (t + 1) : ℝ) ≤ _
    rw [N_add_zetaDensityBackground, Nat.cast_add, add_mul]
    exact add_le_add (hlat.1 t) (hcount t)
  · intro T hT
    change |((superpose Z₀ zetaDensityBackground).N 0 T : ℝ) - _| ≤ _
    rw [N_add_zetaDensityBackground, Nat.cast_add, add_sub_cancel_right,
      abs_of_nonneg (Nat.cast_nonneg _)]
    exact offLineLattice_count_le_linear hL hδ hδ' hT
  · intro f hf hs
    have hfc := hasCompactSupport_of_tsupport_subset_Icc hs
    have he : Z.W f f = Z₀.W f f + zetaDensityBackground.W f f :=
      (hasSum_Wsummand_superpose hd
        (ArithmeticCastelnuovoSeveri.summable_Wsummand Z₀ ht₀ hf hfc hf hfc).hasSum
        (ArithmeticCastelnuovoSeveri.summable_Wsummand zetaDensityBackground
          zetaDensityBackground_tempered hf hfc hf hfc).hasSum).tsum_eq
    rw [he, Complex.add_re]
    exact add_nonneg
      ((offLineLattice_weil_positive_iff hL hδ hδ' a).mpr
        (by dsimp [L]; linarith) f hf hs)
      (weil_nonneg_of_onLine zetaDensityBackground (criticalProjectionConfig_onLine zetaZeroConfig) f)
  · intro T
    obtain ⟨ρ, hρ, hre, him⟩ := hlat.2.2.1 T
    exact ⟨ρ, Or.inl hρ, hre, him⟩

end GaloisForLFunctions.SelectiveArithmetic
