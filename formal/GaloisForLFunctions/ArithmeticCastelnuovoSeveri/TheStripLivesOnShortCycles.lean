import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.OneSidedLefschetzBoundsAtOnePrimeAreTheStrip
import GaloisForLFunctions.SquareRootThreshold.ZetaWeilPositivityThroughApertureThreeTenths

/-!
# The strip lives on short cycles

The tests that break a one-sided Lefschetz bound can be taken of arbitrarily small support.
Dilation `u ↦ g(μu)` divides frequencies by `μ` and keeps the sparsity sums finite, so the killing
tests live in `[−η/2, η/2]` (`exists_test_killing_deep_zeros_small`), and a two-term rotation with
shift `η/2` keeps the support in `[−η, η]` (`tsupport_twoTermTest_subset`).

* **Short tests at one scale** (`deepSparse_exists_short_test_oneSided`,
  `deepSparse_oneSided_iff_short`): for a deep-sparse configuration the one-sided law at one scale
  holds on the tests supported in `[−η, η]`, for every `η > 0`.
* **For `ζ`** (`zeta_width_le_iff_oneSided_short`, `zeta_riemannHypothesis_iff_oneSided_short`):
  at one prime, RH holds iff every test supported in `[−η, η]` satisfies
  `ε Re W(T_{p^m} g, g) ≤ W(g, g)`.
* **Two windows** (`towerMoment_zero_twoWindow`, `re_W_twoWindow`,
  `zeta_riemannHypothesis_iff_twoWindows`): `c_{−m} = conj c_m` (`towerMoment_neg`), so the Weil
  norm of `g − T_v g` is `2(Re W(g, g) − Re W(T_v g, g))`; RH holds iff Weil's form is nonnegative
  on every difference `g − T_{p^m} g` of a test supported in `[−η, η]` and its `p^m`-translate.
* **Local positivity, global defect** (`zeta_twoWindows_local_global`): Hecke translates are Weil
  isometries (`towerMoment_translate_zero`), so for `η ≤ 3/10` each window is Weil positive,
  `Re W(T_v g, T_v g) ≥ ∫|g|²/5000`; RH fails iff for some nonzero such `g` the two windows `g` and
  `T_{p^m} g` have `Re W(g − T_{p^m} g, g − T_{p^m} g) < 0`.

Hodge index for `ζ` splits into a local part, positivity on short cycles, which holds, and a
Lefschetz part, the one-sided bound for the correspondences `T_{p^m}` of one prime on those cycles,
which is all of RH.
-/

open Complex Filter Topology Set MeasureTheory
open scoped ComplexConjugate Classical
open Zeta23 GaloisForLFunctions.HTGeometry
open GaloisForLFunctions.SquareRootThreshold (TemperedConfig temperedConfig_zetaZeroConfig
  zetaZeroWidth abs_re_sub_half_le_zetaZeroWidth)

noncomputable section

namespace GaloisForLFunctions.ArithmeticCastelnuovoSeveri

/-! ### 1. Short two-term tests -/

theorem tsupport_translate (v : ℝ) (g : ℝ → ℂ) :
    tsupport (translate v g) = (fun u => u - v) ⁻¹' tsupport g :=
  tsupport_comp_eq_preimage g (Homeomorph.subRight v)

/-- A two-term test of a test supported in `[−η, η]` with shift `v ≥ 0` lives in `[−η, η + v]`. -/
theorem tsupport_twoTermTest_subset {g : ℝ → ℂ} {η : ℝ} (hgs : tsupport g ⊆ Icc (-η) η) (c : ℂ)
    {v : ℝ} (hv : 0 ≤ v) : tsupport (twoTermTest g c v) ⊆ Icc (-η) (η + v) := by
  refine (tsupport_add g (c • translate v g)).trans (Set.union_subset ?_ ?_)
  · exact hgs.trans (Icc_subset_Icc le_rfl (by linarith))
  · refine (tsupport_smul_subset_right (fun _ => c) (translate v g)).trans ?_
    rw [tsupport_translate]
    intro u hu
    have h := hgs hu
    exact ⟨by linarith [h.1], by linarith [h.2]⟩

/-! ### 2. Short tests break one-sided bounds -/

/-- **A short test breaks a one-sided bound at one scale.** For a deep-sparse configuration, a
right zero `ρ`, a scale `ℓ > 0`, a sign `ε = ±1` and `η > 0`, a test supported in `[−η, η]` has
`ε Re c_m > C R^m` for some `m`, for every `C` and `0 ≤ R < |β_ρ|`. -/
theorem deepSparse_exists_short_test_oneSided (Z : ZeroConfig) (hZ : TemperedConfig Z)
    (hsp : DeepSparse Z) {ρ : ℂ} (hρ : ρ ∈ rightZeros Z) {ℓ : ℝ} (hℓ : 0 < ℓ) {ε : ℝ}
    (hε : ε = 1 ∨ ε = -1) {η : ℝ} (hη : 0 < η) :
    ∃ g : ℝ → ℂ, ContDiff ℝ 2 g ∧ tsupport g ⊆ Icc (-η) η ∧ ∀ C R : ℝ, 0 ≤ R →
      R < ‖frobEig ℓ ρ‖ → ∃ m : ℕ, C * R ^ m < ε * (towerMoment Z g ℓ m).re := by
  have hσ : 1 / 2 < 1 / 2 + (ρ.re - 1 / 2) / 2 := by linarith [hρ.2]
  obtain ⟨g, hg, hgs, hkill, hkeep⟩ :=
    exists_test_killing_deep_zeros_small Z hsp hσ {ρ} (fun τ hτ => by
      rw [Set.mem_singleton_iff.mp hτ]; exact hρ) (half_pos hη)
  have hgc : HasCompactSupport g := isCompact_Icc.of_isClosed_subset (isClosed_tsupport g) hgs
  obtain ⟨u, hu⟩ := exists_twoTermTest_oneSided Z hZ hρ hℓ hε hg hgc hkill hkeep (half_pos hη)
  refine ⟨_, twoTermTest_contDiff hg _ _, ?_, hu⟩
  refine (tsupport_twoTermTest_subset hgs _ (half_pos hη).le).trans (Icc_subset_Icc ?_ ?_) <;>
    linarith

/-- **The one-sided law on short tests.** For a deep-sparse configuration, `ℓ > 0`, a sign
`ε = ±1`, `R ≥ 1` and `η > 0`: every test supported in `[−η, η]` has `ε Re c_m = O(R^m)` iff every
outer eigenvalue has modulus at most `R`. -/
theorem deepSparse_oneSided_iff_short (Z : ZeroConfig) (hZ : TemperedConfig Z)
    (hsp : DeepSparse Z) {ℓ : ℝ} (hℓ : 0 < ℓ) {ε : ℝ} (hε : ε = 1 ∨ ε = -1) {R : ℝ}
    (hR : 1 ≤ R) {η : ℝ} (hη : 0 < η) :
    (∀ ρ ∈ rightZeros Z, ‖frobEig ℓ ρ‖ ≤ R) ↔ ∀ g : ℝ → ℂ, ContDiff ℝ 2 g →
      tsupport g ⊆ Icc (-η) η → ∃ C, ∀ m : ℕ, ε * (towerMoment Z g ℓ m).re ≤ C * R ^ m := by
  constructor
  · intro hdom g hg hgs
    exact (deepSparse_oneSided_iff Z hZ hsp hℓ hε hR).mp hdom g hg
      (isCompact_Icc.of_isClosed_subset (isClosed_tsupport g) hgs)
  · intro h ρ hρ
    by_contra hlt
    push Not at hlt
    obtain ⟨g, hg, hgs, hgrow⟩ := deepSparse_exists_short_test_oneSided Z hZ hsp hρ hℓ hε hη
    obtain ⟨C, hC⟩ := h g hg hgs
    obtain ⟨m, hm⟩ := hgrow C R (by linarith) hlt
    exact absurd (hC m) (not_le.mpr hm)

/-- **One-sided bounds on short tests at one prime are the zero-free strip.** For a prime `p`, a
sign `ε = ±1`, `θ ≥ 0` and `η > 0`: the zero width of `ζ` is at most `θ` iff every test supported
in `[−η, η]` satisfies `ε Re W(T_{p^m} g, g) = O(p^{θm})`. -/
theorem zeta_width_le_iff_oneSided_short {p : ℕ} (hp : p.Prime) {ε : ℝ} (hε : ε = 1 ∨ ε = -1)
    {θ : ℝ} (hθ : 0 ≤ θ) {η : ℝ} (hη : 0 < η) :
    zetaZeroWidth ≤ θ ↔ ∀ g : ℝ → ℂ, ContDiff ℝ 2 g → tsupport g ⊆ Icc (-η) η →
      ∃ C, ∀ m : ℕ, ε * (towerMoment zetaZeroConfig g (Real.log p) m).re ≤
        C * ((p : ℝ) ^ θ) ^ m := by
  have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast hp.one_lt.le
  have hR : 1 ≤ (p : ℝ) ^ θ := Real.one_le_rpow hp1 hθ
  rw [← deepSparse_oneSided_iff_short _ temperedConfig_zetaZeroConfig deepSparse_zeta
    (Real.log_pos (by exact_mod_cast hp.one_lt)) hε hR hη, zeta_forall_norm_frobEig_le_iff hp hR]
  constructor
  · exact fun hw => Real.rpow_le_rpow_of_exponent_le hp1 hw
  · intro h
    by_contra hlt
    push Not at hlt
    have hp1' : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
    exact absurd h (not_le.mpr (Real.rpow_lt_rpow_of_exponent_lt hp1' hlt))

/-- **One-sided Weil inequalities on short tests at one prime decide RH.** For a prime `p`, a sign
`ε = ±1` and `η > 0`: RH holds iff every test supported in `[−η, η]` satisfies
`ε Re W(T_{p^m} g, g) ≤ W(g, g)` for all `m`. -/
theorem zeta_riemannHypothesis_iff_oneSided_short {p : ℕ} (hp : p.Prime) {ε : ℝ}
    (hε : ε = 1 ∨ ε = -1) {η : ℝ} (hη : 0 < η) :
    RiemannHypothesis ↔ ∀ g : ℝ → ℂ, ContDiff ℝ 2 g → tsupport g ⊆ Icc (-η) η → ∀ m : ℕ,
      ε * (towerMoment zetaZeroConfig g (Real.log p) m).re ≤
        (towerMoment zetaZeroConfig g (Real.log p) 0).re := by
  constructor
  · intro hRH g hg hgs
    exact (zeta_riemannHypothesis_iff_oneSided_onePrime hp hε).mp hRH g hg
      (isCompact_Icc.of_isClosed_subset (isClosed_tsupport g) hgs)
  · intro h
    have hw : zetaZeroWidth ≤ 0 := (zeta_width_le_iff_oneSided_short hp hε le_rfl hη).mpr
      fun g hg hgs => ⟨(towerMoment zetaZeroConfig g (Real.log p) 0).re, fun m => by
        rw [Real.rpow_zero, one_pow, mul_one]; exact h g hg hgs m⟩
    rw [← rightZeros_zeta_eq_empty_iff]
    refine Set.eq_empty_iff_forall_notMem.mpr fun ρ hρ => ?_
    have := (le_abs_self _).trans (abs_re_sub_half_le_zetaZeroWidth hρ.1)
    linarith [hρ.2]

/-! ### 3. Two windows -/

/-- **Reflection conjugates the Lefschetz sequence**: `c_{−m} = conj c_m`. -/
theorem towerMoment_neg (Z : ZeroConfig) (g : ℝ → ℂ) (ℓ : ℝ) (m : ℤ) :
    towerMoment Z g ℓ (-m) = conj (towerMoment Z g ℓ m) := by
  rw [towerMoment, towerMoment, Complex.conj_tsum]
  conv_lhs => rw [← (reflectEquiv Z).tsum_eq]
  refine tsum_congr fun τ => ?_
  have hrefl : frobEig ℓ ((reflectCarrier Z τ : Z.carrier) : ℂ) = (conj (frobEig ℓ τ))⁻¹ :=
    frobEig_reflect ℓ τ
  simp only [reflectEquiv_apply, reflectCarrier_reflectCarrier, hrefl, map_mul, map_zpow₀,
    Complex.conj_conj, inv_zpow', neg_neg]
  ring

/-- Weil's form on the diagonal is the `0`-th Lefschetz moment. -/
theorem W_self_eq_towerMoment_zero (Z : ZeroConfig) (hZ : TemperedConfig Z) {g : ℝ → ℂ}
    (hg : ContDiff ℝ 2 g) (hgc : HasCompactSupport g) (ℓ : ℝ) :
    Z.W g g = towerMoment Z g ℓ 0 := by
  refine (W_eq_inner Z hZ ⟨g, hg, hgc⟩ ⟨g, hg, hgc⟩).trans ?_
  rw [lp.inner_eq_tsum, towerMoment]
  refine tsum_congr fun τ => ?_
  simp only [RCLike.inner_apply', reflectVec_apply, zeroMap_apply, zpow_zero, mul_one]
  ring

/-- **Hecke translates are Weil isometries**: `W(T_v g, T_v g) = W(g, g)` on the zero side, since
`e^{iγv} conj(e^{iγ̄v}) = 1`. -/
theorem towerMoment_translate_zero (Z : ZeroConfig) (g : ℝ → ℂ) (ℓ v : ℝ) :
    towerMoment Z (translate v g) ℓ 0 = towerMoment Z g ℓ 0 := by
  simp only [towerMoment, zpow_zero, mul_one]
  refine tsum_congr fun τ => ?_
  have e : gammaOf ((reflectCarrier Z τ : Z.carrier) : ℂ) = conj (gammaOf τ) := gammaOf_reflect _
  have h : cexp (I * gammaOf τ * v) * conj (cexp (I * conj (gammaOf τ) * v)) = 1 := by
    rw [← Complex.exp_conj, ← Complex.exp_add]
    convert Complex.exp_zero using 2
    simp only [map_mul, Complex.conj_I, Complex.conj_conj, Complex.conj_ofReal]
    ring
  rw [zeroCoord_translate, zeroCoord_translate, e, map_mul]
  linear_combination (zeroCoord Z g τ * conj (zeroCoord Z g (reflectCarrier Z τ))) * h

/-- **The Weil norm of two windows.** `W(g − T_{mℓ} g, g − T_{mℓ} g) = 2c_0 − c_m − c_{−m}`: the
two-term factor `(1 − e^{iγv}) conj(1 − e^{iγ̄v})` is `2 − β^m − β^{−m}`. -/
theorem towerMoment_zero_twoWindow (Z : ZeroConfig) (hZ : TemperedConfig Z) {g : ℝ → ℂ}
    (hg : ContDiff ℝ 2 g) (hgc : HasCompactSupport g) {ℓ : ℝ} (hℓ : 0 < ℓ) (m : ℕ) :
    towerMoment Z (g - translate (m * ℓ) g) ℓ 0 =
      2 * towerMoment Z g ℓ 0 - towerMoment Z g ℓ m - towerMoment Z g ℓ (-m) := by
  have e : g - translate (m * ℓ) g = twoTermTest g (-1) (m * ℓ) := by
    funext u
    simp [twoTermTest, sub_eq_add_neg]
  have hs : ∀ k : ℤ, Summable fun τ : Z.carrier =>
      zeroCoord Z g τ * conj (zeroCoord Z g (reflectCarrier Z τ)) * frobEig ℓ τ ^ k := fun k =>
    (summable_towerMoment_term Z hZ hg hgc hℓ k).of_norm
  have hterm : ∀ τ : Z.carrier,
      zeroCoord Z (twoTermTest g (-1) (m * ℓ)) τ *
          conj (zeroCoord Z (twoTermTest g (-1) (m * ℓ)) (reflectCarrier Z τ)) *
            frobEig ℓ τ ^ (0 : ℤ) =
        2 * (zeroCoord Z g τ * conj (zeroCoord Z g (reflectCarrier Z τ)) *
            frobEig ℓ τ ^ (0 : ℤ)) -
          zeroCoord Z g τ * conj (zeroCoord Z g (reflectCarrier Z τ)) * frobEig ℓ τ ^ (m : ℤ) -
          zeroCoord Z g τ * conj (zeroCoord Z g (reflectCarrier Z τ)) *
            frobEig ℓ τ ^ (-(m : ℤ)) := by
    intro τ
    have hI := I_mul_gammaOf (τ : ℂ)
    have ha : cexp (I * gammaOf τ * ((m * ℓ : ℝ) : ℂ)) = frobEig ℓ τ ^ (m : ℤ) := by
      rw [frobEig, ← Complex.exp_int_mul]
      congr 1
      push_cast
      linear_combination ((m : ℂ) * ℓ) * hI
    have hb : conj (cexp (I * conj (gammaOf τ) * ((m * ℓ : ℝ) : ℂ))) =
        frobEig ℓ τ ^ (-(m : ℤ)) := by
      rw [← Complex.exp_conj, frobEig, ← Complex.exp_int_mul]
      congr 1
      simp only [map_mul, Complex.conj_I, Complex.conj_conj, Complex.conj_ofReal]
      push_cast
      linear_combination (-((m : ℂ) * ℓ)) * hI
    have hne : frobEig ℓ τ ^ (m : ℤ) ≠ 0 := zpow_ne_zero _ (frobEig_ne_zero ℓ τ)
    rw [weight_twoTermTest Z hg.continuous hgc, map_add, map_one, map_mul, map_neg, map_one, ha, hb,
      zpow_neg, zpow_zero]
    field_simp
    ring
  rw [e]
  simp only [towerMoment]
  rw [tsum_congr hterm, Summable.tsum_sub (((hs 0).mul_left 2).sub (hs m)) (hs (-m)),
    Summable.tsum_sub ((hs 0).mul_left 2) (hs m), tsum_mul_left]

/-- `Re W(g − T_{mℓ} g, g − T_{mℓ} g) = 2(Re c_0 − Re c_m)`. -/
theorem re_W_twoWindow (Z : ZeroConfig) (hZ : TemperedConfig Z) {g : ℝ → ℂ}
    (hg : ContDiff ℝ 2 g) (hgc : HasCompactSupport g) {ℓ : ℝ} (hℓ : 0 < ℓ) (m : ℕ) :
    (Z.W (g - translate (m * ℓ) g) (g - translate (m * ℓ) g)).re =
      2 * ((towerMoment Z g ℓ 0).re - (towerMoment Z g ℓ m).re) := by
  have hG : ContDiff ℝ 2 (g - translate (m * ℓ) g) := hg.sub (translate_contDiff hg _)
  have hGc : HasCompactSupport (g - translate (m * ℓ) g) :=
    hgc.sub (translate_hasCompactSupport hgc _)
  have h2 : ((2 : ℂ) * towerMoment Z g ℓ 0).re = 2 * (towerMoment Z g ℓ 0).re := by simp
  rw [W_self_eq_towerMoment_zero Z hZ hG hGc ℓ, towerMoment_zero_twoWindow Z hZ hg hgc hℓ m,
    towerMoment_neg, Complex.sub_re, Complex.sub_re, Complex.conj_re, h2]
  ring

/-- **Two short windows decide RH.** For a prime `p` and `η > 0`: RH holds iff Weil's form of `ζ`
is nonnegative on every difference `g − T_{p^m} g` of a test supported in `[−η, η]` and its
`p^m`-translate. -/
theorem zeta_riemannHypothesis_iff_twoWindows {p : ℕ} (hp : p.Prime) {η : ℝ} (hη : 0 < η) :
    RiemannHypothesis ↔ ∀ g : ℝ → ℂ, ContDiff ℝ 2 g → tsupport g ⊆ Icc (-η) η → ∀ m : ℕ,
      0 ≤ (zetaZeroConfig.W (g - translate (m * Real.log p) g)
        (g - translate (m * Real.log p) g)).re := by
  have hℓ : 0 < Real.log p := Real.log_pos (by exact_mod_cast hp.one_lt)
  rw [zeta_riemannHypothesis_iff_oneSided_short hp (Or.inl rfl) hη]
  refine forall_congr' fun g => imp_congr_right fun hg => imp_congr_right fun hgs =>
    forall_congr' fun m => ?_
  rw [re_W_twoWindow _ temperedConfig_zetaZeroConfig hg
    (isCompact_Icc.of_isClosed_subset (isClosed_tsupport g) hgs) hℓ m, one_mul]
  constructor <;> intro h <;> linarith

/-- **Local positivity, global defect.** For a prime `p` and `0 < η ≤ 3/10`, every test `g`
supported in `[−η, η]` has Weil-positive windows, `Re W(T_v g, T_v g) ≥ (1/5000) ∫ |g|²` for every
shift `v`; RH fails iff some such `g ≠ 0` has `Re W(g − T_{p^m} g, g − T_{p^m} g) < 0` for some
`m`. -/
theorem zeta_twoWindows_local_global {p : ℕ} (hp : p.Prime) {η : ℝ} (hη : 0 < η)
    (hη' : η ≤ 3 / 10) :
    (∀ g : ℝ → ℂ, ContDiff ℝ 2 g → tsupport g ⊆ Icc (-η) η → ∀ v : ℝ,
      1 / 5000 * ∫ u, ‖g u‖ ^ 2 ≤ (zetaZeroConfig.W (translate v g) (translate v g)).re) ∧
    (¬ RiemannHypothesis ↔ ∃ g : ℝ → ℂ, ContDiff ℝ 2 g ∧ tsupport g ⊆ Icc (-η) η ∧
      0 < ∫ u, ‖g u‖ ^ 2 ∧ ∃ m : ℕ, (zetaZeroConfig.W (g - translate (m * Real.log p) g)
        (g - translate (m * Real.log p) g)).re < 0) := by
  have hℓ : 0 < Real.log p := Real.log_pos (by exact_mod_cast hp.one_lt)
  refine ⟨fun g hg hgs v => ?_, ?_⟩
  · have hgc : HasCompactSupport g := isCompact_Icc.of_isClosed_subset (isClosed_tsupport g) hgs
    rw [W_self_eq_towerMoment_zero _ temperedConfig_zetaZeroConfig (translate_contDiff hg v)
      (translate_hasCompactSupport hgc v) 1, towerMoment_translate_zero,
      ← W_self_eq_towerMoment_zero _ temperedConfig_zetaZeroConfig hg hgc 1]
    exact SquareRootThreshold.zetaZeroConfig_re_W_ge_of_aperture_le_threeTenths hg
      (hgs.trans (Icc_subset_Icc (by linarith) hη'))
  rw [zeta_riemannHypothesis_iff_twoWindows hp hη]
  constructor
  · intro h
    push Not at h
    obtain ⟨g, hg, hgs, m, hm⟩ := h
    refine ⟨g, hg, hgs, ?_, m, hm⟩
    have hgc : HasCompactSupport g := isCompact_Icc.of_isClosed_subset (isClosed_tsupport g) hgs
    rw [re_W_twoWindow _ temperedConfig_zetaZeroConfig hg hgc hℓ m] at hm
    -- `g ≠ 0`, else every Lefschetz moment vanishes
    obtain ⟨x, hx⟩ : ∃ x, g x ≠ 0 := by
      by_contra h0
      push Not at h0
      have hz : ∀ k : ℤ, towerMoment zetaZeroConfig g (Real.log p) k = 0 := fun k => by
        simp [towerMoment, zeroCoord, paperFT, h0]
      rw [hz, hz] at hm
      simp at hm
    have hcont : Continuous fun u => ‖g u‖ ^ 2 := (continuous_norm.comp hg.continuous).pow 2
    have hsupp : HasCompactSupport fun u => ‖g u‖ ^ 2 :=
      hgc.comp_left (g := fun z : ℂ => ‖z‖ ^ 2) (by simp)
    exact hcont.integral_pos_of_hasCompactSupport_nonneg_nonzero hsupp (fun u => sq_nonneg _)
      (x := x) (pow_pos (norm_pos_iff.mpr hx) 2).ne'
  · rintro ⟨g, hg, hgs, -, m, hm⟩ h
    exact absurd (h g hg hgs m) (not_le.mpr hm)

end GaloisForLFunctions.ArithmeticCastelnuovoSeveri

end
