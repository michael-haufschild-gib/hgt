/-
# The concrete cover annulus and inverse-Böttcher data for the disconnected deck

Discharges the analytic hypotheses that `DeckAnnulus.monoF_step_from_inverse` /
`DeckAnnulus.exists_rotInvariant_a2` consume.  The cover is the value annulus `U = {R' < ‖ξ‖}` (`ξ`
plays the rôle of the `2ⁿ`-th root of `φ_{c₁}`), and `ψ₁ = φ_{c₁}^{-1}` is the far-field inverse Böttcher
(`FarFieldUnivalence`).  Combining the far-field inverse with the far-field surjectivity
(`FarFieldSurjective.exists_far_preimage`) gives, on `U`:

* `ψ₁` analytic at `ξ^{2ⁿ}` (the value `ξ^{2ⁿ}` is `φ_{c₁}(z)` for a far-field `z`, where `ψ₁` is the
  analytic local inverse);
* `ψ₁(ξ^{2ⁿ}) ∈ escapeOpen c₂` (the base point `z` is far for `c₁`, hence — once the radius beats
  `max 2 ‖c₂‖` — also in `c₂`'s escape set: the two-parameter far-field overlap).

Plus the topology of the exterior annulus: open, preconnected (via `exp` of a half-plane), nonempty,
infinite, and rotation-invariant.  Axiom-clean.
-/
import GaloisForLFunctions.Bottcher.DeckAnnulus
import GaloisForLFunctions.Bottcher.FarFieldUnivalence
import GaloisForLFunctions.Bottcher.FarFieldSurjective
import GaloisForLFunctions.Bottcher.PolyAsymptotic
import Mathlib.Algebra.Polynomial.Bivariate
import Mathlib.RingTheory.Polynomial.Resultant.Basic

open Filter Topology Set Complex

namespace Bottcher

/-- **The exterior annulus `{R' < ‖ξ‖}` is preconnected.**  It is the continuous image of the convex
half-plane `{w | log R' < w.re}` under `exp` (`‖exp w‖ = exp w.re`, and `exp` is onto `ℂ∖{0}`), hence
preconnected.  The carrier `U` of the dyadic deck is connected, so `meroField U` is a field. -/
theorem isPreconnected_exterior {R' : ℝ} (hR' : 0 < R') :
    IsPreconnected {ξ : ℂ | R' < ‖ξ‖} := by
  have hset : {ξ : ℂ | R' < ‖ξ‖} = Complex.exp '' {w : ℂ | Real.log R' < w.re} := by
    ext ξ
    simp only [Set.mem_setOf_eq, Set.mem_image]
    constructor
    · intro hξ
      refine ⟨Complex.log ξ, ?_, Complex.exp_log (by intro h; rw [h, norm_zero] at hξ; linarith)⟩
      rw [Complex.log_re]
      exact (Real.log_lt_log_iff hR' (lt_trans hR' hξ)).mpr hξ
    · rintro ⟨w, hw, rfl⟩
      rw [Complex.norm_exp]
      calc R' = Real.exp (Real.log R') := (Real.exp_log hR').symm
        _ < Real.exp w.re := Real.exp_lt_exp.mpr hw
  rw [hset]
  exact ((convex_halfSpace_re_gt (Real.log R')).isPreconnected).image _
    Complex.continuous_exp.continuousOn

/-- **The exterior annulus is open.** -/
theorem isOpen_exterior {R' : ℝ} : IsOpen {ξ : ℂ | R' < ‖ξ‖} :=
  isOpen_lt continuous_const continuous_norm

/-- **The exterior annulus is nonempty** (it contains the real point `R'+1`). -/
theorem nonempty_exterior {R' : ℝ} (hR' : 0 < R') : ({ξ : ℂ | R' < ‖ξ‖}).Nonempty :=
  ⟨((R' + 1 : ℝ) : ℂ), by
    show R' < ‖((R' + 1 : ℝ) : ℂ)‖
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith)]; linarith⟩

/-- **The exterior annulus is infinite** (it contains the injective sequence `n ↦ R'+1+n`). -/
theorem infinite_exterior {R' : ℝ} (hR' : 0 < R') : ({ξ : ℂ | R' < ‖ξ‖}).Infinite := by
  refine Set.infinite_of_injective_forall_mem
    (f := fun n : ℕ => ((R' + 1 + (n : ℝ) : ℝ) : ℂ)) ?_ ?_
  · intro a b hab
    simp only at hab
    have h : R' + 1 + (a : ℝ) = R' + 1 + (b : ℝ) := Complex.ofReal_inj.mp hab
    exact Nat.cast_injective (show (a : ℝ) = (b : ℝ) by linarith)
  · intro n
    show R' < ‖((R' + 1 + (n : ℝ) : ℝ) : ℂ)‖
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
    have : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    linarith

/-- **The exterior annulus is rotation-invariant** under any unit-modulus `ζ₀`. -/
theorem mapsTo_rotation_exterior {ζ₀ : ℂ} (hζ : ‖ζ₀‖ = 1) {R' : ℝ} :
    Set.MapsTo (rotation ζ₀) {ξ : ℂ | R' < ‖ξ‖} {ξ : ℂ | R' < ‖ξ‖} := by
  intro ξ hξ
  show R' < ‖rotation ζ₀ ξ‖
  rw [rotation, norm_mul, hζ, one_mul]
  exact hξ

/-- **The concrete cover-annulus + inverse-Böttcher data.**  For a far-field radius `R` (large enough
for the `c₁` inverse Böttcher and beating `max 2 ‖c₂‖`), a surjectivity threshold `B`, and a cover
radius `R'` with `R'^{2ⁿ} > B`, the far-field inverse `ψ₁ = φ_{c₁}^{-1}` satisfies, on the cover annulus
`{R' < ‖ξ‖}`, the two analytic hypotheses of `exists_rotInvariant_a2`: `ψ₁` is analytic at `ξ^{2ⁿ}` and
`ψ₁(ξ^{2ⁿ}) ∈ escapeOpen c₂`.  (The inequalities are satisfiable for every `c₁, c₂, n`: take `R` large,
then `B > 2R` large, then `R' = B + 1`.)  This is the inverse-Böttcher analyticity + the two-parameter
far-field overlap, discharged. -/
theorem exists_cover_annulus_data (c₁ c₂ : ℂ) (n : ℕ) {R B R' : ℝ}
    (hR1 : 2 * max 2 ‖c₁‖ < R) (hR2 : 16 * ‖c₁‖ < R ^ 2) (hRc₂ : max 2 ‖c₂‖ < R)
    (hB_far1 : 768 * ‖c₁‖ + 64 ≤ B ^ 2) (hB_far2 : 8 * max 2 ‖c₁‖ < B) (hBR : 2 * R < B)
    (hBpos : 0 < B) (hR'pos : 0 < R') (hR'B : B < R' ^ (2 ^ n)) :
    ∃ ψ₁ : ℂ → ℂ,
      (∀ ξ ∈ {ξ : ℂ | R' < ‖ξ‖}, AnalyticAt ℂ ψ₁ (ξ ^ (2 ^ n))) ∧
      (∀ ξ ∈ {ξ : ℂ | R' < ‖ξ‖}, ψ₁ (ξ ^ (2 ^ n)) ∈ escapeOpen c₂) := by
  obtain ⟨ψ₁, hψleft, hψan, _hψright⟩ := exists_analytic_inverse_far (c := c₁) hR1 hR2
  have key : ∀ ξ : ℂ, R' < ‖ξ‖ → ∃ z, R < ‖z‖ ∧ bottcherCoord c₁ z = ξ ^ (2 ^ n) := by
    intro ξ hξR'
    have hwnorm : ‖ξ ^ (2 ^ n)‖ = ‖ξ‖ ^ (2 ^ n) := by rw [norm_pow]
    have hwB : B < ‖ξ ^ (2 ^ n)‖ := by
      rw [hwnorm]
      exact lt_of_lt_of_le hR'B (pow_le_pow_left₀ (le_of_lt hR'pos) (le_of_lt hξR') (2 ^ n))
    have hwfar1 : 768 * ‖c₁‖ + 64 < ‖ξ ^ (2 ^ n)‖ ^ 2 :=
      lt_of_le_of_lt hB_far1 (by nlinarith [hBpos, hwB])
    have hwfar2 : 8 * max 2 ‖c₁‖ < ‖ξ ^ (2 ^ n)‖ := lt_trans hB_far2 hwB
    obtain ⟨z, hz, hbz⟩ := exists_far_preimage (c := c₁) hwfar1 hwfar2
    have hzR : R < ‖z‖ := by
      have h1 : B / 2 ≤ ‖z‖ := le_trans (by linarith [hwB]) hz
      linarith [hBR]
    exact ⟨z, hzR, hbz⟩
  refine ⟨ψ₁, ?_, ?_⟩
  · intro ξ hξ
    obtain ⟨z, hzR, hbz⟩ := key ξ hξ
    rw [← hbz]; exact hψan z hzR
  · intro ξ hξ
    obtain ⟨z, hzR, hbz⟩ := key ξ hξ
    have hψw : ψ₁ (ξ ^ (2 ^ n)) = z := by rw [← hbz]; exact hψleft z hzR
    rw [hψw]
    show max 2 ‖c₂‖ < ‖z‖
    exact lt_trans hRc₂ hzR

/-- **The deck-invariant base projection `p₀(ξ) = ψ₁(ξ^{2ⁿ})` as an analytic germ on `U`.**  This is
the base coordinate `z` read on the cover (`z = φ_{c₁}^{-1}(ξ^{2ⁿ})`), through which `ℂ(z)` embeds into
`meroField U` via `ratfuncToMeroVia p₀`.  Analytic wherever `ψ₁` is analytic at `ξ^{2ⁿ}` (the
`exists_cover_annulus_data` hypothesis). -/
theorem exists_projection_p0 {U : Set ℂ} {ψ₁ : ℂ → ℂ} {n : ℕ}
    (hψan : ∀ ξ ∈ U, AnalyticAt ℂ ψ₁ (ξ ^ (2 ^ n))) :
    ∃ p₀ : analyticSubring U,
      (p₀ : Germ (𝓟 U) ℂ) = ↑(fun ξ => ψ₁ (ξ ^ (2 ^ n))) := by
  set pw : ℂ → ℂ := fun ξ => ξ ^ (2 ^ n) with hpw
  have han : AnalyticOnNhd ℂ (fun ξ => ψ₁ (pw ξ)) U := by
    intro ξ hξ
    have h1 : AnalyticAt ℂ pw ξ := analyticAt_id.pow (2 ^ n)
    have h2 : AnalyticAt ℂ ψ₁ (pw ξ) := hψan ξ hξ
    exact h2.comp h1
  exact ⟨⟨(↑(fun ξ => ψ₁ (pw ξ)) : Germ (𝓟 U) ℂ), fun ξ => ψ₁ (pw ξ), han, rfl⟩, rfl⟩

/-- **The base projection is deck-invariant:** `p₀∘(×ζ₀) = p₀` for `ζ₀^{2ⁿ} = 1` — so the deck fixes
`ℂ(z)` (the `hfix` hypothesis of `precompMeroEquiv_ratfuncToMeroVia_fix`, discharging the `hK` clause). -/
theorem p0_rotation_invariant {U : Set ℂ} {ψ₁ : ℂ → ℂ} {ζ₀ : ℂ} {n : ℕ}
    (hζ : ζ₀ ^ (2 ^ n) = 1) :
    ∀ y ∈ U, (fun ξ => ψ₁ (ξ ^ (2 ^ n))) (rotation ζ₀ y)
      = (fun ξ => ψ₁ (ξ ^ (2 ^ n))) y :=
  pow_comp_rotation_invariant (h := ψ₁) hζ U

end Bottcher

namespace Bottcher

/-- **Inverse-annulus `monoF` step with projection-base fixing constructed.**  This discharges the
`hK` input of `monoF_step_from_inverse` for the natural cover projection
`p₀(ξ) = ψ₁(ξ^(2^n))`: if `ζ₀^(2^n)=1`, the deck rotation fixes `p₀`, hence fixes the whole embedded
`ℂ(z)` base from `ratfuncToMeroVia`.  The output includes the constructed projection germ, identity
cover coordinate `a₁ = ξ`, genuine second coordinate `a₂ = φ_{c₂}(ψ₁(ξ^(2^n)))`, and the resulting
`RatFunc ℂ`-linear monodromy witness. -/
theorem monoF_step_from_inverse_projectionBase {c₂ : ℂ} {U : Set ℂ} {ψ₁ : ℂ → ℂ}
    {ζ₀ : ℂ} {n : ℕ}
    (hUo : IsOpen U) (hUc : IsPreconnected U) (hUne : U.Nonempty)
    (hpInf : ((fun ξ => ψ₁ (ξ ^ (2 ^ n))) '' U).Infinite)
    (hrot : Set.MapsTo (rotation ζ₀) U U) (hrot' : Set.MapsTo (rotation ζ₀⁻¹) U U)
    (hζ0 : ζ₀ ≠ 0) (hζpow : ζ₀ ^ (2 ^ n) = 1) (d : ℕ) (hord : d < orderOf ζ₀)
    (hψan : ∀ ξ ∈ U, AnalyticAt ℂ ψ₁ (ξ ^ (2 ^ n)))
    (hcont : ∀ ξ ∈ U, ψ₁ (ξ ^ (2 ^ n)) ∈ escapeOpen c₂) :
    ∃ (p₀ : analyticSubring U)
      (hp0 : (p₀ : Germ (𝓟 U) ℂ) = ↑(fun ξ => ψ₁ (ξ ^ (2 ^ n))))
      (a₁ a₂ : analyticSubring U),
      (a₁ : Germ (𝓟 U) ℂ) = ↑(id : ℂ → ℂ) ∧
      (a₂ : Germ (𝓟 U) ℂ) = ↑(fun ξ => bottcherCoord c₂ (ψ₁ (ξ ^ (2 ^ n)))) ∧
      (letI : IsDomain (analyticSubring U) := isDomain_analyticSubring U hUo hUc hUne
       letI : Algebra (RatFunc ℂ) (meroField U) :=
        (ratfuncToMeroVia p₀ hp0 hpInf hUo hUc hUne).toAlgebra
       ∃ (σ : meroField U ≃ₐ[RatFunc ℂ] meroField U) (ζ : meroField U) (m : ℕ),
        d < m ∧ orderOf ζ = m ∧
        σ (algebraMap (analyticSubring U) (meroField U) a₂)
          = algebraMap (analyticSubring U) (meroField U) a₂ ∧
        σ ζ = ζ ∧
        σ (algebraMap (analyticSubring U) (meroField U) a₁)
          = ζ * algebraMap (analyticSubring U) (meroField U) a₁) := by
  obtain ⟨p₀, hp0⟩ := exists_projection_p0 (U := U) (ψ₁ := ψ₁) (n := n) hψan
  let a₁ : analyticSubring U :=
    ⟨(↑(id : ℂ → ℂ) : Germ (𝓟 U) ℂ), id, analyticOnNhd_id, rfl⟩
  have ha₁ : (a₁ : Germ (𝓟 U) ℂ) = ↑(id : ℂ → ℂ) := rfl
  haveI := isDomain_analyticSubring U hUo hUc hUne
  letI : Algebra (RatFunc ℂ) (meroField U) :=
    (ratfuncToMeroVia p₀ hp0 hpInf hUo hUc hUne).toAlgebra
  have hpfix : precompAnalytic
      (analyticOnNhd_deckRot (liftUniformization_id U) hrot)
      (mapsTo_deckRot (liftUniformization_id U) hrot) p₀ = p₀ := by
    apply Subtype.ext
    rw [precompAnalytic_coe, hp0, Germ.coe_compTendsto, Germ.coe_eq]
    exact eventually_principal.mpr (fun y hy => by
      simpa [deckRot] using p0_rotation_invariant (U := U) (ψ₁ := ψ₁) (ζ₀ := ζ₀) (n := n)
        hζpow y hy)
  have hK : ∀ k : RatFunc ℂ, precompMeroEquiv
        (analyticOnNhd_deckRot (liftUniformization_id U) hrot)
        (analyticOnNhd_deckRot (liftUniformization_id U) hrot')
        (mapsTo_deckRot (liftUniformization_id U) hrot)
        (mapsTo_deckRot (liftUniformization_id U) hrot')
        (eqOn_deckRot_comp hζ0 (liftUniformization_id U) hrot')
        (eqOn_deckRot_comp' hζ0 (liftUniformization_id U) hrot)
        hUo hUc hUne (algebraMap (RatFunc ℂ) (meroField U) k)
        = algebraMap (RatFunc ℂ) (meroField U) k := by
    intro k
    simpa using! precompMeroEquiv_ratfuncToMeroVia_fix
      (analyticOnNhd_deckRot (liftUniformization_id U) hrot)
      (analyticOnNhd_deckRot (liftUniformization_id U) hrot')
      (mapsTo_deckRot (liftUniformization_id U) hrot)
      (mapsTo_deckRot (liftUniformization_id U) hrot')
      (eqOn_deckRot_comp hζ0 (liftUniformization_id U) hrot')
      (eqOn_deckRot_comp' hζ0 (liftUniformization_id U) hrot)
      hUo hUc hUne hp0 hpInf hpfix k
  obtain ⟨a₂, σ, ζ, m, ha₂, hm, hζord, hfix, hζfix, hscale⟩ :=
    monoF_step_from_inverse (K := RatFunc ℂ) (c₂ := c₂) (U := U) (ψ₁ := ψ₁) (ζ₀ := ζ₀) (n := n)
      hUo hUc hUne hrot hrot' hζ0 hζpow d hord hψan hcont a₁ ha₁ hK
  refine ⟨p₀, hp0, a₁, a₂, ha₁, ha₂, ?_⟩
  exact ⟨σ, ζ, m, hm, hζord, hfix, hζfix, hscale⟩

end Bottcher

namespace Bottcher

/-- **The inverse-annulus projection has infinite image.**  If the far-field inverse satisfies
`φ_{c₁}(ψ₁(ξ^(2^n))) = ξ^(2^n)` on the exterior cover annulus, then the projection
`p₀(ξ)=ψ₁(ξ^(2^n))` takes infinitely many values.  This discharges the infinitude condition needed to
embed the projection base `ℂ(z)` by `ratfuncToMeroVia`. -/
theorem projection_image_infinite_exterior {c₁ : ℂ} {ψ₁ : ℂ → ℂ} {n : ℕ} {R' : ℝ}
    (hR'pos : 0 < R')
    (hproj : ∀ ξ ∈ {ξ : ℂ | R' < ‖ξ‖}, bottcherCoord c₁ (ψ₁ (ξ ^ (2 ^ n))) = ξ ^ (2 ^ n)) :
    ((fun ξ => ψ₁ (ξ ^ (2 ^ n))) '' {ξ : ℂ | R' < ‖ξ‖}).Infinite := by
  refine Set.infinite_of_injective_forall_mem
    (f := fun k : ℕ => ψ₁ ((((R' + 1 + (k : ℝ) : ℝ) : ℂ)) ^ (2 ^ n))) ?_ ?_
  · intro a b hab
    let ξa : ℂ := ((R' + 1 + (a : ℝ) : ℝ) : ℂ)
    let ξb : ℂ := ((R' + 1 + (b : ℝ) : ℝ) : ℂ)
    have hξa : R' < ‖ξa‖ := by
      dsimp [ξa]
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
      have ha : (0 : ℝ) ≤ a := Nat.cast_nonneg a
      linarith
    have hξb : R' < ‖ξb‖ := by
      dsimp [ξb]
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
      have hb : (0 : ℝ) ≤ b := Nat.cast_nonneg b
      linarith
    have hbott := congrArg (bottcherCoord c₁) hab
    have hpowc : ξa ^ (2 ^ n) = ξb ^ (2 ^ n) := by
      rw [hproj ξa hξa, hproj ξb hξb] at hbott
      exact hbott
    have hpowr : (R' + 1 + (a : ℝ)) ^ (2 ^ n) = (R' + 1 + (b : ℝ)) ^ (2 ^ n) := by
      apply Complex.ofReal_inj.mp
      simpa [ξa, ξb, Complex.ofReal_pow] using hpowc
    have hN : 2 ^ n ≠ 0 := pow_ne_zero n (by norm_num : (2 : ℕ) ≠ 0)
    have hbase : R' + 1 + (a : ℝ) = R' + 1 + (b : ℝ) := by
      exact (pow_left_inj₀ (by positivity) (by positivity) hN).mp hpowr
    exact Nat.cast_injective (show (a : ℝ) = (b : ℝ) by linarith)
  · intro k
    refine ⟨(((R' + 1 + (k : ℝ) : ℝ) : ℂ)), ?_, rfl⟩
    show R' < ‖((R' + 1 + (k : ℝ) : ℝ) : ℂ)‖
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
    have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    linarith

/-- **Concrete cover-annulus inverse data with projection infinitude.**  This strengthens
`exists_cover_annulus_data`: besides analyticity of `ψ₁` at `ξ^(2^n)` and containment of the projected
base point in `escapeOpen c₂`, it records the inverse identity
`φ_{c₁}(ψ₁(ξ^(2^n))) = ξ^(2^n)` and the resulting infinite image of the deck-invariant projection
`p₀(ξ)=ψ₁(ξ^(2^n))`. -/
theorem exists_cover_annulus_data_with_projection (c₁ c₂ : ℂ) (n : ℕ) {R B R' : ℝ}
    (hR1 : 2 * max 2 ‖c₁‖ < R) (hR2 : 16 * ‖c₁‖ < R ^ 2) (hRc₂ : max 2 ‖c₂‖ < R)
    (hB_far1 : 768 * ‖c₁‖ + 64 ≤ B ^ 2) (hB_far2 : 8 * max 2 ‖c₁‖ < B) (hBR : 2 * R < B)
    (hBpos : 0 < B) (hR'pos : 0 < R') (hR'B : B < R' ^ (2 ^ n)) :
    ∃ ψ₁ : ℂ → ℂ,
      (∀ ξ ∈ {ξ : ℂ | R' < ‖ξ‖}, AnalyticAt ℂ ψ₁ (ξ ^ (2 ^ n))) ∧
      (∀ ξ ∈ {ξ : ℂ | R' < ‖ξ‖}, ψ₁ (ξ ^ (2 ^ n)) ∈ escapeOpen c₂) ∧
      (∀ ξ ∈ {ξ : ℂ | R' < ‖ξ‖}, bottcherCoord c₁ (ψ₁ (ξ ^ (2 ^ n))) = ξ ^ (2 ^ n)) ∧
      ((fun ξ => ψ₁ (ξ ^ (2 ^ n))) '' {ξ : ℂ | R' < ‖ξ‖}).Infinite := by
  obtain ⟨ψ₁, hψleft, hψan, _hψright⟩ := exists_analytic_inverse_far (c := c₁) hR1 hR2
  have key : ∀ ξ : ℂ, R' < ‖ξ‖ → ∃ z, R < ‖z‖ ∧ bottcherCoord c₁ z = ξ ^ (2 ^ n) := by
    intro ξ hξR'
    have hwnorm : ‖ξ ^ (2 ^ n)‖ = ‖ξ‖ ^ (2 ^ n) := by rw [norm_pow]
    have hwB : B < ‖ξ ^ (2 ^ n)‖ := by
      rw [hwnorm]
      exact lt_of_lt_of_le hR'B (pow_le_pow_left₀ (le_of_lt hR'pos) (le_of_lt hξR') (2 ^ n))
    have hwfar1 : 768 * ‖c₁‖ + 64 < ‖ξ ^ (2 ^ n)‖ ^ 2 :=
      lt_of_le_of_lt hB_far1 (by nlinarith [hBpos, hwB])
    have hwfar2 : 8 * max 2 ‖c₁‖ < ‖ξ ^ (2 ^ n)‖ := lt_trans hB_far2 hwB
    obtain ⟨z, hz, hbz⟩ := exists_far_preimage (c := c₁) hwfar1 hwfar2
    have hzR : R < ‖z‖ := by
      have h1 : B / 2 ≤ ‖z‖ := le_trans (by linarith [hwB]) hz
      linarith [hBR]
    exact ⟨z, hzR, hbz⟩
  have hψan' : ∀ ξ ∈ {ξ : ℂ | R' < ‖ξ‖}, AnalyticAt ℂ ψ₁ (ξ ^ (2 ^ n)) := by
    intro ξ hξ
    obtain ⟨z, hzR, hbz⟩ := key ξ hξ
    rw [← hbz]
    exact hψan z hzR
  have hcont' : ∀ ξ ∈ {ξ : ℂ | R' < ‖ξ‖}, ψ₁ (ξ ^ (2 ^ n)) ∈ escapeOpen c₂ := by
    intro ξ hξ
    obtain ⟨z, hzR, hbz⟩ := key ξ hξ
    have hψw : ψ₁ (ξ ^ (2 ^ n)) = z := by
      rw [← hbz]
      exact hψleft z hzR
    rw [hψw]
    show max 2 ‖c₂‖ < ‖z‖
    exact lt_trans hRc₂ hzR
  have hproj : ∀ ξ ∈ {ξ : ℂ | R' < ‖ξ‖}, bottcherCoord c₁ (ψ₁ (ξ ^ (2 ^ n))) = ξ ^ (2 ^ n) := by
    intro ξ hξ
    obtain ⟨z, hzR, hbz⟩ := key ξ hξ
    have hψw : ψ₁ (ξ ^ (2 ^ n)) = z := by
      rw [← hbz]
      exact hψleft z hzR
    rw [hψw]
    exact hbz
  exact ⟨ψ₁, hψan', hcont', hproj, projection_image_infinite_exterior hR'pos hproj⟩

end Bottcher

namespace Bottcher

/-- **Concrete exterior-annulus `monoF` step with projection base constructed.**  This packages the
far-field inverse-Böttcher annulus, the infinite projection image, and projection-base deck fixing into
one usable statement.  The only remaining parameters are the explicit radius inequalities and the
chosen dyadic deck multiplier; no `hK`, `hpInf`, topology, analyticity, or containment hypotheses are
left for callers to supply. -/
theorem monoF_step_from_concrete_cover_annulus_projectionBase (c₁ c₂ : ℂ) (n d : ℕ) {R B R' : ℝ}
    (hR1 : 2 * max 2 ‖c₁‖ < R) (hR2 : 16 * ‖c₁‖ < R ^ 2) (hRc₂ : max 2 ‖c₂‖ < R)
    (hB_far1 : 768 * ‖c₁‖ + 64 ≤ B ^ 2) (hB_far2 : 8 * max 2 ‖c₁‖ < B) (hBR : 2 * R < B)
    (hBpos : 0 < B) (hR'pos : 0 < R') (hR'B : B < R' ^ (2 ^ n))
    {ζ₀ : ℂ} (hζnorm : ‖ζ₀‖ = 1) (hζ0 : ζ₀ ≠ 0) (hζpow : ζ₀ ^ (2 ^ n) = 1)
    (hord : d < orderOf ζ₀) :
    ∃ (ψ₁ : ℂ → ℂ)
      (hpInf : ((fun ξ => ψ₁ (ξ ^ (2 ^ n))) '' {ξ : ℂ | R' < ‖ξ‖}).Infinite)
      (p₀ : analyticSubring {ξ : ℂ | R' < ‖ξ‖})
      (hp0 : (p₀ : Germ (𝓟 {ξ : ℂ | R' < ‖ξ‖}) ℂ) = ↑(fun ξ => ψ₁ (ξ ^ (2 ^ n))))
      (a₁ a₂ : analyticSubring {ξ : ℂ | R' < ‖ξ‖}),
      (a₁ : Germ (𝓟 {ξ : ℂ | R' < ‖ξ‖}) ℂ) = ↑(id : ℂ → ℂ) ∧
      (a₂ : Germ (𝓟 {ξ : ℂ | R' < ‖ξ‖}) ℂ) =
        ↑(fun ξ => bottcherCoord c₂ (ψ₁ (ξ ^ (2 ^ n)))) ∧
      (letI : IsDomain (analyticSubring {ξ : ℂ | R' < ‖ξ‖}) :=
        isDomain_analyticSubring {ξ : ℂ | R' < ‖ξ‖} isOpen_exterior
          (isPreconnected_exterior hR'pos) (nonempty_exterior hR'pos)
       letI : Algebra (RatFunc ℂ) (meroField {ξ : ℂ | R' < ‖ξ‖}) :=
        (ratfuncToMeroVia p₀ hp0 hpInf isOpen_exterior
          (isPreconnected_exterior hR'pos) (nonempty_exterior hR'pos)).toAlgebra
       ∃ (σ : meroField {ξ : ℂ | R' < ‖ξ‖} ≃ₐ[RatFunc ℂ] meroField {ξ : ℂ | R' < ‖ξ‖})
          (ζ : meroField {ξ : ℂ | R' < ‖ξ‖}) (m : ℕ),
        d < m ∧ orderOf ζ = m ∧
        σ (algebraMap (analyticSubring {ξ : ℂ | R' < ‖ξ‖}) (meroField {ξ : ℂ | R' < ‖ξ‖}) a₂)
          = algebraMap (analyticSubring {ξ : ℂ | R' < ‖ξ‖}) (meroField {ξ : ℂ | R' < ‖ξ‖}) a₂ ∧
        σ ζ = ζ ∧
        σ (algebraMap (analyticSubring {ξ : ℂ | R' < ‖ξ‖}) (meroField {ξ : ℂ | R' < ‖ξ‖}) a₁)
          = ζ * algebraMap (analyticSubring {ξ : ℂ | R' < ‖ξ‖}) (meroField {ξ : ℂ | R' < ‖ξ‖}) a₁) := by
  obtain ⟨ψ₁, hψan, hcont, _hproj, hpInf⟩ :=
    exists_cover_annulus_data_with_projection c₁ c₂ n hR1 hR2 hRc₂ hB_far1 hB_far2 hBR
      hBpos hR'pos hR'B
  have hζinvnorm : ‖ζ₀⁻¹‖ = 1 := by
    rw [norm_inv, hζnorm, inv_one]
  obtain ⟨p₀, hp0, a₁, a₂, ha₁, ha₂, hmono⟩ :=
    monoF_step_from_inverse_projectionBase (c₂ := c₂) (U := {ξ : ℂ | R' < ‖ξ‖})
      (ψ₁ := ψ₁) (ζ₀ := ζ₀) (n := n)
      isOpen_exterior (isPreconnected_exterior hR'pos) (nonempty_exterior hR'pos) hpInf
      (mapsTo_rotation_exterior hζnorm) (mapsTo_rotation_exterior hζinvnorm)
      hζ0 hζpow d hord hψan hcont
  exact ⟨ψ₁, hpInf, p₀, hp0, a₁, a₂, ha₁, ha₂, hmono⟩

end Bottcher

namespace Bottcher

/-- **Concrete exterior-annulus `monoF` step with the dyadic multiplier chosen.**  For bound `d`, use
level `d+1` and the primitive multiplier `exp(2πi/2^(d+1))`.  The unit norm, nonzero, root-of-unity,
and order bounds are all proved here, so callers no longer provide any deck-multiplier hypotheses. -/
theorem monoF_step_from_concrete_cover_annulus_dyadic (c₁ c₂ : ℂ) (d : ℕ) {R B R' : ℝ}
    (hR1 : 2 * max 2 ‖c₁‖ < R) (hR2 : 16 * ‖c₁‖ < R ^ 2) (hRc₂ : max 2 ‖c₂‖ < R)
    (hB_far1 : 768 * ‖c₁‖ + 64 ≤ B ^ 2) (hB_far2 : 8 * max 2 ‖c₁‖ < B) (hBR : 2 * R < B)
    (hBpos : 0 < B) (hR'pos : 0 < R') (hR'B : B < R' ^ (2 ^ (d + 1))) :
    ∃ (ψ₁ : ℂ → ℂ)
      (hpInf : ((fun ξ => ψ₁ (ξ ^ (2 ^ (d + 1)))) '' {ξ : ℂ | R' < ‖ξ‖}).Infinite)
      (p₀ : analyticSubring {ξ : ℂ | R' < ‖ξ‖})
      (hp0 : (p₀ : Germ (𝓟 {ξ : ℂ | R' < ‖ξ‖}) ℂ) = ↑(fun ξ => ψ₁ (ξ ^ (2 ^ (d + 1)))))
      (a₁ a₂ : analyticSubring {ξ : ℂ | R' < ‖ξ‖}),
      (a₁ : Germ (𝓟 {ξ : ℂ | R' < ‖ξ‖}) ℂ) = ↑(id : ℂ → ℂ) ∧
      (a₂ : Germ (𝓟 {ξ : ℂ | R' < ‖ξ‖}) ℂ) =
        ↑(fun ξ => bottcherCoord c₂ (ψ₁ (ξ ^ (2 ^ (d + 1))))) ∧
      (letI : IsDomain (analyticSubring {ξ : ℂ | R' < ‖ξ‖}) :=
        isDomain_analyticSubring {ξ : ℂ | R' < ‖ξ‖} isOpen_exterior
          (isPreconnected_exterior hR'pos) (nonempty_exterior hR'pos)
       letI : Algebra (RatFunc ℂ) (meroField {ξ : ℂ | R' < ‖ξ‖}) :=
        (ratfuncToMeroVia p₀ hp0 hpInf isOpen_exterior
          (isPreconnected_exterior hR'pos) (nonempty_exterior hR'pos)).toAlgebra
       ∃ (σ : meroField {ξ : ℂ | R' < ‖ξ‖} ≃ₐ[RatFunc ℂ] meroField {ξ : ℂ | R' < ‖ξ‖})
          (ζ : meroField {ξ : ℂ | R' < ‖ξ‖}) (m : ℕ),
        d < m ∧ orderOf ζ = m ∧
        σ (algebraMap (analyticSubring {ξ : ℂ | R' < ‖ξ‖}) (meroField {ξ : ℂ | R' < ‖ξ‖}) a₂)
          = algebraMap (analyticSubring {ξ : ℂ | R' < ‖ξ‖}) (meroField {ξ : ℂ | R' < ‖ξ‖}) a₂ ∧
        σ ζ = ζ ∧
        σ (algebraMap (analyticSubring {ξ : ℂ | R' < ‖ξ‖}) (meroField {ξ : ℂ | R' < ‖ξ‖}) a₁)
          = ζ * algebraMap (analyticSubring {ξ : ℂ | R' < ‖ξ‖}) (meroField {ξ : ℂ | R' < ‖ξ‖}) a₁) := by
  let n : ℕ := d + 1
  let ζ₀ : ℂ := Complex.exp (2 * (Real.pi : ℂ) * Complex.I / ((2 ^ n : ℕ) : ℂ))
  have hζnorm : ‖ζ₀‖ = 1 := by
    dsimp [ζ₀]
    have hprim := Complex.isPrimitiveRoot_exp (2 ^ n) (pow_ne_zero n (by norm_num : (2 : ℕ) ≠ 0))
    exact hprim.norm'_eq_one (pow_ne_zero n (by norm_num : (2 : ℕ) ≠ 0))
  have hζ0 : ζ₀ ≠ 0 := by
    dsimp [ζ₀]
    exact Complex.exp_ne_zero _
  have hζpow : ζ₀ ^ (2 ^ n) = 1 := by
    have horder : orderOf ζ₀ = 2 ^ n := by
      dsimp [ζ₀]
      exact orderOf_dyadicRoot n
    calc
      ζ₀ ^ (2 ^ n) = ζ₀ ^ orderOf ζ₀ := by rw [horder]
      _ = 1 := pow_orderOf_eq_one ζ₀
  have hord : d < orderOf ζ₀ := by
    dsimp [ζ₀, n]
    rw [orderOf_dyadicRoot]
    exact lt_trans (Nat.lt_succ_self d) Nat.lt_two_pow_self
  exact monoF_step_from_concrete_cover_annulus_projectionBase (c₁ := c₁) (c₂ := c₂) (n := n) (d := d)
    hR1 hR2 hRc₂ hB_far1 hB_far2 hBR hBpos hR'pos hR'B hζnorm hζ0 hζpow hord

end Bottcher

namespace Bottcher

/-- Radius inequalities needed for the concrete exterior-annulus inverse data. -/
def coverAnnulusRadiusIneqs (c₁ c₂ : ℂ) (n : ℕ) (R B R' : ℝ) : Prop :=
  2 * max 2 ‖c₁‖ < R ∧ 16 * ‖c₁‖ < R ^ 2 ∧ max 2 ‖c₂‖ < R ∧
  768 * ‖c₁‖ + 64 ≤ B ^ 2 ∧ 8 * max 2 ‖c₁‖ < B ∧ 2 * R < B ∧
  0 < B ∧ 0 < R' ∧ B < R' ^ (2 ^ n)

/-- **The cover-annulus radii exist with no caller-supplied bounds.**  Pick large natural numbers for
`R`, then `B`, then `R'`; the square and power bounds follow from choosing each larger than `1` and
larger than the preceding thresholds. -/
theorem exists_cover_annulus_radii (c₁ c₂ : ℂ) (n : ℕ) :
    ∃ R B R' : ℝ, coverAnnulusRadiusIneqs c₁ c₂ n R B R' := by
  let TR : ℝ := max (2 * max 2 ‖c₁‖) (max (16 * ‖c₁‖) (max (max 2 ‖c₂‖) 1))
  obtain ⟨NR, hNR⟩ := exists_nat_gt TR
  let R : ℝ := (NR : ℝ)
  have hR1 : 2 * max 2 ‖c₁‖ < R := lt_of_le_of_lt (by dsimp [TR]; exact le_max_left _ _) hNR
  have hR16 : 16 * ‖c₁‖ < R := lt_of_le_of_lt (by dsimp [TR]; exact le_trans (le_max_left _ _) (le_max_right _ _)) hNR
  have hRc₂ : max 2 ‖c₂‖ < R := lt_of_le_of_lt (by
    dsimp [TR]
    exact le_trans (le_max_left _ _) (le_trans (le_max_right _ _) (le_max_right _ _))) hNR
  have hRgt1 : 1 < R := lt_of_le_of_lt (by
    dsimp [TR]
    exact le_trans (le_max_right _ _) (le_trans (le_max_right _ _) (le_max_right _ _))) hNR
  have hR2 : 16 * ‖c₁‖ < R ^ 2 := by
    have hRsq : R < R ^ 2 := by
      simpa using (lt_self_pow₀ hRgt1 (by norm_num : (1 : ℕ) < 2))
    exact lt_trans hR16 hRsq
  let TB : ℝ := max (8 * max 2 ‖c₁‖) (max (2 * R) (max (768 * ‖c₁‖ + 64) 1))
  obtain ⟨NB, hNB⟩ := exists_nat_gt TB
  let B : ℝ := (NB : ℝ)
  have hB8 : 8 * max 2 ‖c₁‖ < B := lt_of_le_of_lt (by dsimp [TB]; exact le_max_left _ _) hNB
  have hBR : 2 * R < B := lt_of_le_of_lt (by dsimp [TB]; exact le_trans (le_max_left _ _) (le_max_right _ _)) hNB
  have hBbig : 768 * ‖c₁‖ + 64 < B := lt_of_le_of_lt (by
    dsimp [TB]
    exact le_trans (le_max_left _ _) (le_trans (le_max_right _ _) (le_max_right _ _))) hNB
  have hBgt1 : 1 < B := lt_of_le_of_lt (by
    dsimp [TB]
    exact le_trans (le_max_right _ _) (le_trans (le_max_right _ _) (le_max_right _ _))) hNB
  have hBpos : 0 < B := lt_trans zero_lt_one hBgt1
  have hBsq : 768 * ‖c₁‖ + 64 ≤ B ^ 2 := by
    have hBs : B < B ^ 2 := by
      simpa using (lt_self_pow₀ hBgt1 (by norm_num : (1 : ℕ) < 2))
    exact le_of_lt (lt_trans hBbig hBs)
  let TRp : ℝ := max B 1
  obtain ⟨NRp, hNRp⟩ := exists_nat_gt TRp
  let R' : ℝ := (NRp : ℝ)
  have hBltR' : B < R' := lt_of_le_of_lt (by dsimp [TRp]; exact le_max_left _ _) hNRp
  have hR'gt1 : 1 < R' := lt_of_le_of_lt (by dsimp [TRp]; exact le_max_right _ _) hNRp
  have hR'pos : 0 < R' := lt_trans zero_lt_one hR'gt1
  have hR'B : B < R' ^ (2 ^ n) := by
    have hle : R' ≤ R' ^ (2 ^ n) :=
      le_self_pow₀ (le_of_lt hR'gt1) (pow_ne_zero n (by norm_num : (2 : ℕ) ≠ 0))
    exact lt_of_lt_of_le hBltR' hle
  exact ⟨R, B, R', hR1, hR2, hRc₂, hBsq, hB8, hBR, hBpos, hR'pos, hR'B⟩

/-- The constructed `monoF` output on a positive exterior annulus. -/
def concreteAnnulusMonoFOutput (c₂ : ℂ) (n d : ℕ) (R' : ℝ) (hR'pos : 0 < R') : Prop :=
  ∃ (ψ₁ : ℂ → ℂ)
    (hpInf : ((fun ξ => ψ₁ (ξ ^ (2 ^ n))) '' {ξ : ℂ | R' < ‖ξ‖}).Infinite)
    (p₀ : analyticSubring {ξ : ℂ | R' < ‖ξ‖})
    (hp0 : (p₀ : Germ (𝓟 {ξ : ℂ | R' < ‖ξ‖}) ℂ) = ↑(fun ξ => ψ₁ (ξ ^ (2 ^ n))))
    (a₁ a₂ : analyticSubring {ξ : ℂ | R' < ‖ξ‖}),
    (a₁ : Germ (𝓟 {ξ : ℂ | R' < ‖ξ‖}) ℂ) = ↑(id : ℂ → ℂ) ∧
    (a₂ : Germ (𝓟 {ξ : ℂ | R' < ‖ξ‖}) ℂ) =
      ↑(fun ξ => bottcherCoord c₂ (ψ₁ (ξ ^ (2 ^ n)))) ∧
    (letI : IsDomain (analyticSubring {ξ : ℂ | R' < ‖ξ‖}) :=
      isDomain_analyticSubring {ξ : ℂ | R' < ‖ξ‖} isOpen_exterior
        (isPreconnected_exterior hR'pos) (nonempty_exterior hR'pos)
     letI : Algebra (RatFunc ℂ) (meroField {ξ : ℂ | R' < ‖ξ‖}) :=
      (ratfuncToMeroVia p₀ hp0 hpInf isOpen_exterior
        (isPreconnected_exterior hR'pos) (nonempty_exterior hR'pos)).toAlgebra
     ∃ (σ : meroField {ξ : ℂ | R' < ‖ξ‖} ≃ₐ[RatFunc ℂ] meroField {ξ : ℂ | R' < ‖ξ‖})
        (ζ : meroField {ξ : ℂ | R' < ‖ξ‖}) (m : ℕ),
      d < m ∧ orderOf ζ = m ∧
      σ (algebraMap (analyticSubring {ξ : ℂ | R' < ‖ξ‖}) (meroField {ξ : ℂ | R' < ‖ξ‖}) a₂)
        = algebraMap (analyticSubring {ξ : ℂ | R' < ‖ξ‖}) (meroField {ξ : ℂ | R' < ‖ξ‖}) a₂ ∧
      σ ζ = ζ ∧
      σ (algebraMap (analyticSubring {ξ : ℂ | R' < ‖ξ‖}) (meroField {ξ : ℂ | R' < ‖ξ‖}) a₁)
        = ζ * algebraMap (analyticSubring {ξ : ℂ | R' < ‖ξ‖}) (meroField {ξ : ℂ | R' < ‖ξ‖}) a₁)

/-- **Constructed exterior-annulus `monoF` step, with no caller-supplied radius or multiplier data.**
For every bound `d`, the radii are chosen, the dyadic multiplier is chosen, and the resulting
projection-base `monoF` witness is produced. -/
theorem exists_constructed_cover_annulus_monoF_step (c₁ c₂ : ℂ) (d : ℕ) :
    ∃ (R B R' : ℝ) (hR'pos : 0 < R'),
      coverAnnulusRadiusIneqs c₁ c₂ (d + 1) R B R' ∧
      concreteAnnulusMonoFOutput c₂ (d + 1) d R' hR'pos := by
  obtain ⟨R, B, R', hR1, hR2, hRc₂, hBsq, hB8, hBR, hBpos, hR'pos, hR'B⟩ :=
    exists_cover_annulus_radii c₁ c₂ (d + 1)
  refine ⟨R, B, R', hR'pos, ?_, ?_⟩
  · exact ⟨hR1, hR2, hRc₂, hBsq, hB8, hBR, hBpos, hR'pos, hR'B⟩
  · exact monoF_step_from_concrete_cover_annulus_dyadic c₁ c₂ d
      hR1 hR2 hRc₂ hBsq hB8 hBR hBpos hR'pos hR'B

end Bottcher

namespace Bottcher

/-- **Uniform exterior-annulus radii for all dyadic depths.**  The far-field radii `R,B` and the
exterior cover radius `R'` can be chosen once so that the annulus inequalities hold for every level
`d+1`.  Thus the annulus carrier `{ξ | R' < ‖ξ‖}` need not be re-picked as the dyadic order grows. -/
theorem exists_cover_annulus_radii_uniform_dyadic (c₁ c₂ : ℂ) :
    ∃ R B R' : ℝ, 1 < R' ∧ ∀ d : ℕ, coverAnnulusRadiusIneqs c₁ c₂ (d + 1) R B R' := by
  obtain ⟨R, B, R0, hR1, hR2, hRc₂, hBsq, hB8, hBR, hBpos, hR0pos, hR0B⟩ :=
    exists_cover_annulus_radii c₁ c₂ 1
  let R' : ℝ := max R0 1 + 1
  have hR'gt1 : 1 < R' := by
    dsimp [R']
    have hle : (1 : ℝ) ≤ max R0 1 := le_max_right _ _
    linarith
  have hR'pos : 0 < R' := lt_trans zero_lt_one hR'gt1
  have hR0leR' : R0 ≤ R' := by
    dsimp [R']
    have hle : R0 ≤ max R0 1 := le_max_left _ _
    linarith
  have hR0B2 : B < R0 ^ 2 := by
    simpa using hR0B
  have hR0sq_le_R'sq : R0 ^ 2 ≤ R' ^ 2 :=
    pow_le_pow_left₀ (le_of_lt hR0pos) hR0leR' 2
  refine ⟨R, B, R', hR'gt1, fun d => ?_⟩
  have htwole : 2 ≤ 2 ^ (d + 1) := by
    simpa using (Nat.pow_le_pow_right (n := 2) (by norm_num)
      (Nat.succ_le_succ (Nat.zero_le d)))
  have hR'pow : R' ^ 2 ≤ R' ^ (2 ^ (d + 1)) :=
    pow_le_pow_right₀ (le_of_lt hR'gt1) htwole
  have hBR' : B < R' ^ (2 ^ (d + 1)) :=
    lt_of_lt_of_le (lt_of_lt_of_le hR0B2 hR0sq_le_R'sq) hR'pow
  exact ⟨hR1, hR2, hRc₂, hBsq, hB8, hBR, hBpos, hR'pos, hBR'⟩

/-- **Uniform exterior-annulus `monoF` steps.**  With one fixed exterior carrier radius `R'`, every
order bound `d` has the constructed projection-base `monoF` witness at dyadic level `d+1`.  The
projection and pulled-back second coordinate still vary with the level, but the annulus carrier does
not. -/
theorem exists_uniform_cover_annulus_monoF_steps (c₁ c₂ : ℂ) :
    ∃ (R B R' : ℝ) (hR'pos : 0 < R'),
      (∀ d : ℕ, coverAnnulusRadiusIneqs c₁ c₂ (d + 1) R B R') ∧
      ∀ d : ℕ, concreteAnnulusMonoFOutput c₂ (d + 1) d R' hR'pos := by
  obtain ⟨R, B, R', hR'gt1, hall⟩ := exists_cover_annulus_radii_uniform_dyadic c₁ c₂
  have hR'pos : 0 < R' := lt_trans zero_lt_one hR'gt1
  refine ⟨R, B, R', hR'pos, hall, fun d => ?_⟩
  obtain ⟨hR1, hR2, hRc₂, hBsq, hB8, hBR, hBpos, _hR'pos, hR'B⟩ := hall d
  exact monoF_step_from_concrete_cover_annulus_dyadic c₁ c₂ d
    hR1 hR2 hRc₂ hBsq hB8 hBR hBpos hR'pos hR'B

end Bottcher

namespace Bottcher

/-- **Uniform exterior-annulus inverse data with a fixed inverse branch.**  The far-field inverse
`ψ₁ = φ_{c₁}^{-1}` is chosen once from the fixed radius `R`; the same exterior carrier and the same
`ψ₁` then work for every dyadic depth.  Only the finite projection `ξ ↦ ψ₁(ξ^(2^(d+1)))` changes with
`d`. -/
theorem exists_uniform_cover_annulus_data_with_fixed_inverse_projection (c₁ c₂ : ℂ) :
    ∃ (R B R' : ℝ) (_hR'pos : 0 < R') (ψ₁ : ℂ → ℂ),
      (∀ d : ℕ, coverAnnulusRadiusIneqs c₁ c₂ (d + 1) R B R') ∧
      ∀ d : ℕ,
        (∀ ξ ∈ {ξ : ℂ | R' < ‖ξ‖}, AnalyticAt ℂ ψ₁ (ξ ^ (2 ^ (d + 1)))) ∧
        (∀ ξ ∈ {ξ : ℂ | R' < ‖ξ‖}, ψ₁ (ξ ^ (2 ^ (d + 1))) ∈ escapeOpen c₂) ∧
        (∀ ξ ∈ {ξ : ℂ | R' < ‖ξ‖},
          bottcherCoord c₁ (ψ₁ (ξ ^ (2 ^ (d + 1)))) = ξ ^ (2 ^ (d + 1))) ∧
        ((fun ξ => ψ₁ (ξ ^ (2 ^ (d + 1)))) '' {ξ : ℂ | R' < ‖ξ‖}).Infinite := by
  obtain ⟨R, B, R', hR'gt1, hall⟩ := exists_cover_annulus_radii_uniform_dyadic c₁ c₂
  have hR'pos : 0 < R' := lt_trans zero_lt_one hR'gt1
  obtain ⟨hR1, hR2, _hRc₂0, _hB_far10, _hB_far20, _hBR0, _hBpos0,
      _hR'pos0, _hR'B0⟩ := hall 0
  obtain ⟨ψ₁, hψleft, hψan, _hψright⟩ := exists_analytic_inverse_far (c := c₁) hR1 hR2
  refine ⟨R, B, R', hR'pos, ψ₁, hall, fun d => ?_⟩
  obtain ⟨_hR1, _hR2, hRc₂, hB_far1, hB_far2, hBR, hBpos, _hR'pos, hR'B⟩ := hall d
  let n : ℕ := d + 1
  have hR'B_n : B < R' ^ (2 ^ n) := by simpa [n] using hR'B
  have key : ∀ ξ : ℂ, R' < ‖ξ‖ → ∃ z, R < ‖z‖ ∧ bottcherCoord c₁ z = ξ ^ (2 ^ n) := by
    intro ξ hξR'
    have hwnorm : ‖ξ ^ (2 ^ n)‖ = ‖ξ‖ ^ (2 ^ n) := by rw [norm_pow]
    have hwB : B < ‖ξ ^ (2 ^ n)‖ := by
      rw [hwnorm]
      exact lt_of_lt_of_le hR'B_n (pow_le_pow_left₀ (le_of_lt hR'pos) (le_of_lt hξR') (2 ^ n))
    have hwfar1 : 768 * ‖c₁‖ + 64 < ‖ξ ^ (2 ^ n)‖ ^ 2 :=
      lt_of_le_of_lt hB_far1 (by nlinarith [hBpos, hwB])
    have hwfar2 : 8 * max 2 ‖c₁‖ < ‖ξ ^ (2 ^ n)‖ := lt_trans hB_far2 hwB
    obtain ⟨z, hz, hbz⟩ := exists_far_preimage (c := c₁) hwfar1 hwfar2
    have hzR : R < ‖z‖ := by
      have h1 : B / 2 ≤ ‖z‖ := le_trans (by linarith [hwB]) hz
      linarith [hBR]
    exact ⟨z, hzR, hbz⟩
  have hψan' : ∀ ξ ∈ {ξ : ℂ | R' < ‖ξ‖}, AnalyticAt ℂ ψ₁ (ξ ^ (2 ^ n)) := by
    intro ξ hξ
    obtain ⟨z, hzR, hbz⟩ := key ξ hξ
    rw [← hbz]
    exact hψan z hzR
  have hcont' : ∀ ξ ∈ {ξ : ℂ | R' < ‖ξ‖}, ψ₁ (ξ ^ (2 ^ n)) ∈ escapeOpen c₂ := by
    intro ξ hξ
    obtain ⟨z, hzR, hbz⟩ := key ξ hξ
    have hψw : ψ₁ (ξ ^ (2 ^ n)) = z := by
      rw [← hbz]
      exact hψleft z hzR
    rw [hψw]
    show max 2 ‖c₂‖ < ‖z‖
    exact lt_trans hRc₂ hzR
  have hproj : ∀ ξ ∈ {ξ : ℂ | R' < ‖ξ‖},
      bottcherCoord c₁ (ψ₁ (ξ ^ (2 ^ n))) = ξ ^ (2 ^ n) := by
    intro ξ hξ
    obtain ⟨z, hzR, hbz⟩ := key ξ hξ
    have hψw : ψ₁ (ξ ^ (2 ^ n)) = z := by
      rw [← hbz]
      exact hψleft z hzR
    rw [hψw]
    exact hbz
  have hpInf : ((fun ξ => ψ₁ (ξ ^ (2 ^ n))) '' {ξ : ℂ | R' < ‖ξ‖}).Infinite :=
    projection_image_infinite_exterior hR'pos hproj
  exact ⟨by simpa [n] using hψan', by simpa [n] using hcont', by simpa [n] using hproj,
    by simpa [n] using hpInf⟩

end Bottcher

namespace Bottcher

/-- **Projection image contains every high Böttcher-value far-field point.**
If `ψ₁` is a left inverse to `φ_{c₁}` on `{‖z‖ > R}` and `z` is far enough with
`R'^N < ‖φ_{c₁}(z)‖`, then choosing an `N`-th root `ξ` of `φ_{c₁}(z)` puts `ξ` in the exterior annulus
and sends it back to `z` under the annulus projection `ξ ↦ ψ₁(ξ^N)`. This is the concrete image-side
lemma needed for the pullback-transcendence route. -/
theorem mem_projection_image_of_far_bottcher_value {c₁ z : ℂ} {ψ₁ : ℂ → ℂ} {R R' : ℝ} {N : ℕ}
    (hNpos : 0 < N)
    (hψleft : ∀ w, R < ‖w‖ → ψ₁ (bottcherCoord c₁ w) = w)
    (hzR : R < ‖z‖) (hzval : R' ^ N < ‖bottcherCoord c₁ z‖) :
    z ∈ (fun ξ => ψ₁ (ξ ^ N)) '' {ξ : ℂ | R' < ‖ξ‖} := by
  obtain ⟨ξ, hξpow⟩ := IsAlgClosed.exists_pow_nat_eq (bottcherCoord c₁ z) hNpos
  have hξann : R' < ‖ξ‖ := by
    by_contra hle
    push Not at hle
    have hpow_le : ‖ξ‖ ^ N ≤ R' ^ N := pow_le_pow_left₀ (norm_nonneg ξ) hle N
    have hval_le : ‖bottcherCoord c₁ z‖ ≤ R' ^ N := by
      rw [← hξpow, norm_pow]
      exact hpow_le
    exact not_lt_of_ge hval_le hzval
  refine ⟨ξ, hξann, ?_⟩
  change ψ₁ (ξ ^ N) = z
  rw [hξpow]
  exact hψleft z hzR

end Bottcher

namespace Bottcher

/-- **Uniform fixed-inverse annulus data with an explicit image lower set.**
This strengthens `exists_uniform_cover_annulus_data_with_fixed_inverse_projection` by retaining the
left-inverse identity for the same `ψ₁` and exposing the usable image fact: for every dyadic level,
all far-field points whose `c₁` Böttcher value has norm above `R'^(2^(d+1))` lie in the projection
image of the exterior annulus. -/
theorem exists_uniform_cover_annulus_data_with_fixed_inverse_projection_and_image (c₁ c₂ : ℂ) :
    ∃ (R B R' : ℝ) (_hR'pos : 0 < R') (ψ₁ : ℂ → ℂ),
      (∀ d : ℕ, coverAnnulusRadiusIneqs c₁ c₂ (d + 1) R B R') ∧
      (∀ z, R < ‖z‖ → ψ₁ (bottcherCoord c₁ z) = z) ∧
      ∀ d : ℕ,
        (∀ ξ ∈ {ξ : ℂ | R' < ‖ξ‖}, AnalyticAt ℂ ψ₁ (ξ ^ (2 ^ (d + 1)))) ∧
        (∀ ξ ∈ {ξ : ℂ | R' < ‖ξ‖}, ψ₁ (ξ ^ (2 ^ (d + 1))) ∈ escapeOpen c₂) ∧
        (∀ ξ ∈ {ξ : ℂ | R' < ‖ξ‖},
          bottcherCoord c₁ (ψ₁ (ξ ^ (2 ^ (d + 1)))) = ξ ^ (2 ^ (d + 1))) ∧
        ((fun ξ => ψ₁ (ξ ^ (2 ^ (d + 1)))) '' {ξ : ℂ | R' < ‖ξ‖}).Infinite ∧
        (∀ z, R < ‖z‖ → R' ^ (2 ^ (d + 1)) < ‖bottcherCoord c₁ z‖ →
          z ∈ (fun ξ => ψ₁ (ξ ^ (2 ^ (d + 1)))) '' {ξ : ℂ | R' < ‖ξ‖}) := by
  obtain ⟨R, B, R', hR'gt1, hall⟩ := exists_cover_annulus_radii_uniform_dyadic c₁ c₂
  have hR'pos : 0 < R' := lt_trans zero_lt_one hR'gt1
  obtain ⟨hR1, hR2, _hRc₂0, _hB_far10, _hB_far20, _hBR0, _hBpos0,
      _hR'pos0, _hR'B0⟩ := hall 0
  obtain ⟨ψ₁, hψleft, hψan, _hψright⟩ := exists_analytic_inverse_far (c := c₁) hR1 hR2
  refine ⟨R, B, R', hR'pos, ψ₁, hall, hψleft, fun d => ?_⟩
  obtain ⟨_hR1, _hR2, hRc₂, hB_far1, hB_far2, hBR, hBpos, _hR'pos, hR'B⟩ := hall d
  let n : ℕ := d + 1
  have hR'B_n : B < R' ^ (2 ^ n) := by simpa [n] using hR'B
  have key : ∀ ξ : ℂ, R' < ‖ξ‖ → ∃ z, R < ‖z‖ ∧ bottcherCoord c₁ z = ξ ^ (2 ^ n) := by
    intro ξ hξR'
    have hwnorm : ‖ξ ^ (2 ^ n)‖ = ‖ξ‖ ^ (2 ^ n) := by rw [norm_pow]
    have hwB : B < ‖ξ ^ (2 ^ n)‖ := by
      rw [hwnorm]
      exact lt_of_lt_of_le hR'B_n (pow_le_pow_left₀ (le_of_lt hR'pos) (le_of_lt hξR') (2 ^ n))
    have hwfar1 : 768 * ‖c₁‖ + 64 < ‖ξ ^ (2 ^ n)‖ ^ 2 :=
      lt_of_le_of_lt hB_far1 (by nlinarith [hBpos, hwB])
    have hwfar2 : 8 * max 2 ‖c₁‖ < ‖ξ ^ (2 ^ n)‖ := lt_trans hB_far2 hwB
    obtain ⟨z, hz, hbz⟩ := exists_far_preimage (c := c₁) hwfar1 hwfar2
    have hzR : R < ‖z‖ := by
      have h1 : B / 2 ≤ ‖z‖ := le_trans (by linarith [hwB]) hz
      linarith [hBR]
    exact ⟨z, hzR, hbz⟩
  have hψan' : ∀ ξ ∈ {ξ : ℂ | R' < ‖ξ‖}, AnalyticAt ℂ ψ₁ (ξ ^ (2 ^ n)) := by
    intro ξ hξ
    obtain ⟨z, hzR, hbz⟩ := key ξ hξ
    rw [← hbz]
    exact hψan z hzR
  have hcont' : ∀ ξ ∈ {ξ : ℂ | R' < ‖ξ‖}, ψ₁ (ξ ^ (2 ^ n)) ∈ escapeOpen c₂ := by
    intro ξ hξ
    obtain ⟨z, hzR, hbz⟩ := key ξ hξ
    have hψw : ψ₁ (ξ ^ (2 ^ n)) = z := by
      rw [← hbz]
      exact hψleft z hzR
    rw [hψw]
    show max 2 ‖c₂‖ < ‖z‖
    exact lt_trans hRc₂ hzR
  have hproj : ∀ ξ ∈ {ξ : ℂ | R' < ‖ξ‖},
      bottcherCoord c₁ (ψ₁ (ξ ^ (2 ^ n))) = ξ ^ (2 ^ n) := by
    intro ξ hξ
    obtain ⟨z, hzR, hbz⟩ := key ξ hξ
    have hψw : ψ₁ (ξ ^ (2 ^ n)) = z := by
      rw [← hbz]
      exact hψleft z hzR
    rw [hψw]
    exact hbz
  have hpInf : ((fun ξ => ψ₁ (ξ ^ (2 ^ n))) '' {ξ : ℂ | R' < ‖ξ‖}).Infinite :=
    projection_image_infinite_exterior hR'pos hproj
  have himage : ∀ z, R < ‖z‖ → R' ^ (2 ^ n) < ‖bottcherCoord c₁ z‖ →
      z ∈ (fun ξ => ψ₁ (ξ ^ (2 ^ n))) '' {ξ : ℂ | R' < ‖ξ‖} := by
    intro z hzR hzval
    exact mem_projection_image_of_far_bottcher_value
      (c₁ := c₁) (ψ₁ := ψ₁) (R := R) (R' := R') (N := 2 ^ n)
      (pow_pos (by norm_num : (0 : ℕ) < 2) n) hψleft hzR hzval
  exact ⟨by simpa [n] using hψan', by simpa [n] using hcont', by simpa [n] using hproj,
    by simpa [n] using hpInf, by simpa [n] using himage⟩

end Bottcher

namespace Bottcher

/-- **A pulled-back algebraic relation descends to the projection image.**
If `q(z,Y)` vanishes after substituting `z = ψ₁(ξ^N)` and
`Y = φ_{c₂}(ψ₁(ξ^N))` on the exterior annulus, then the original relation vanishes at every point in
the projection image. This is the function-level descent step for the pulled-back transcendence bridge. -/
theorem eqOn_eval₂_bottcher_on_projection_image_of_pullback
    {c₂ : ℂ} {ψ₁ : ℂ → ℂ} {N : ℕ} {R' : ℝ} (q : Polynomial (Polynomial ℂ))
    (hrel : Set.EqOn
      (fun ξ => q.eval₂ (Polynomial.evalRingHom (ψ₁ (ξ ^ N)))
        (bottcherCoord c₂ (ψ₁ (ξ ^ N)))) 0 {ξ : ℂ | R' < ‖ξ‖}) :
    Set.EqOn (fun z => q.eval₂ (Polynomial.evalRingHom z) (bottcherCoord c₂ z)) 0
      ((fun ξ => ψ₁ (ξ ^ N)) '' {ξ : ℂ | R' < ‖ξ‖}) := by
  rintro z ⟨ξ, hξ, rfl⟩
  exact hrel hξ

/-- **Pulled-back relation descends to the explicit high-value far-field subset.**
Combining `mem_projection_image_of_far_bottcher_value` with
`eqOn_eval₂_bottcher_on_projection_image_of_pullback`: on every far-field point whose `c₁` Böttcher
value is large enough to admit an annulus root, a relation vanishing on the annulus pullback gives the
same relation for the genuine `z`-plane `φ_{c₂}`. -/
theorem eqOn_eval₂_bottcher_on_far_high_values_of_pullback
    {c₁ c₂ : ℂ} {ψ₁ : ℂ → ℂ} {R R' : ℝ} {N : ℕ} (q : Polynomial (Polynomial ℂ))
    (hNpos : 0 < N)
    (hψleft : ∀ z, R < ‖z‖ → ψ₁ (bottcherCoord c₁ z) = z)
    (hrel : Set.EqOn
      (fun ξ => q.eval₂ (Polynomial.evalRingHom (ψ₁ (ξ ^ N)))
        (bottcherCoord c₂ (ψ₁ (ξ ^ N)))) 0 {ξ : ℂ | R' < ‖ξ‖}) :
    Set.EqOn (fun z => q.eval₂ (Polynomial.evalRingHom z) (bottcherCoord c₂ z)) 0
      {z : ℂ | R < ‖z‖ ∧ R' ^ N < ‖bottcherCoord c₁ z‖} := by
  intro z hz
  exact eqOn_eval₂_bottcher_on_projection_image_of_pullback (c₂ := c₂) (ψ₁ := ψ₁)
    (N := N) (R' := R') q hrel
    (mem_projection_image_of_far_bottcher_value (c₁ := c₁) (ψ₁ := ψ₁) (R := R) (R' := R')
      (N := N) hNpos hψleft hz.1 hz.2)

end Bottcher

namespace Bottcher
open Polynomial

/-- **Projection-base bivariate eval-germ identity.**
Evaluating `q ∈ ℂ[z][Y]` at an analytic projection germ `p₀` and an analytic coordinate `a` gives the
concrete germ `ξ ↦ q(p₀(ξ), a(ξ))`. This is the `ratfuncToMeroVia` analogue of
`eval₂_polyToAnalytic_val`. -/
theorem eval₂_polyToAnalyticVia_val {U : Set ℂ} {p₀ a : analyticSubring U} {f₀ g : ℂ → ℂ}
    (hp0 : (p₀ : Germ (𝓟 U) ℂ) = ↑f₀)
    (ha : (a : Germ (𝓟 U) ℂ) = ↑g) (q : Polynomial (Polynomial ℂ)) :
    ((q.eval₂ (polyToAnalyticVia U p₀) a : analyticSubring U) : Germ (𝓟 U) ℂ)
      = ↑(fun ξ => q.eval₂ (Polynomial.evalRingHom (f₀ ξ)) (g ξ)) := by
  rw [show ((q.eval₂ (polyToAnalyticVia U p₀) a : analyticSubring U) : Germ (𝓟 U) ℂ)
        = (analyticSubring U).subtype (q.eval₂ (polyToAnalyticVia U p₀) a) from rfl]
  rw [Polynomial.eval₂_eq_sum, Polynomial.sum_def]
  simp only [map_sum, map_mul, map_pow]
  rw [show (↑(fun ξ => q.eval₂ (Polynomial.evalRingHom (f₀ ξ)) (g ξ)) : Germ (𝓟 U) ℂ)
      = ↑(fun ξ => ∑ i ∈ q.support, (q.coeff i).eval (f₀ ξ) * (g ξ) ^ i : ℂ → ℂ) from by
        congr 1
        funext ξ
        simp [Polynomial.eval₂_eq_sum, Polynomial.sum_def]]
  rw [show ((fun ξ => ∑ i ∈ q.support, (q.coeff i).eval (f₀ ξ) * (g ξ) ^ i : ℂ → ℂ) :
        Germ (𝓟 U) ℂ)
      = ∑ i ∈ q.support,
          ((fun ξ => (q.coeff i).eval (f₀ ξ) * (g ξ) ^ i : ℂ → ℂ) : Germ (𝓟 U) ℂ) from by
        rw [show ((fun ξ => ∑ i ∈ q.support, (q.coeff i).eval (f₀ ξ) * (g ξ) ^ i : ℂ → ℂ) :
            Germ (𝓟 U) ℂ)
          = Germ.coeRingHom (𝓟 U)
              (fun ξ => ∑ i ∈ q.support, (q.coeff i).eval (f₀ ξ) * (g ξ) ^ i) from rfl]
        rw [show (fun ξ => ∑ i ∈ q.support, (q.coeff i).eval (f₀ ξ) * (g ξ) ^ i)
          = ∑ i ∈ q.support, (fun ξ => (q.coeff i).eval (f₀ ξ) * (g ξ) ^ i) from by
            funext ξ
            rw [Finset.sum_apply]]
        rw [map_sum]
        apply Finset.sum_congr rfl
        intro i _hi
        rfl]
  apply Finset.sum_congr rfl
  intro i _hi
  rw [show (analyticSubring U).subtype (polyToAnalyticVia U p₀ (q.coeff i))
      = ((polyToAnalyticVia U p₀ (q.coeff i) : analyticSubring U) : Germ (𝓟 U) ℂ) from rfl]
  rw [polyToAnalyticVia_coe p₀ hp0 (q.coeff i)]
  change (↑(fun z => (q.coeff i).eval (f₀ z)) : Germ (𝓟 U) ℂ) * (a : Germ (𝓟 U) ℂ) ^ i =
      ↑(fun ξ => (q.coeff i).eval (f₀ ξ) * (g ξ) ^ i)
  rw [ha]
  rw [← Germ.coe_pow]
  rw [← Germ.coe_mul]
  rfl

end Bottcher

namespace Bottcher
open Polynomial Filter

/-- **Polynomial projection-base field relation gives a concrete pulled-back relation.**
If a `ℂ[z][Y]` relation evaluates to zero in `meroField U` after embedding `ℂ[z]` via the projection
`p₀` and substituting the analytic coordinate `a`, then the value-function
`ξ ↦ q(p₀(ξ), a(ξ))` vanishes on `U`. -/
theorem eqOn_pullback_eval₂_of_eval₂_polyToMeroVia_zero {U : Set ℂ}
    (hUo : IsOpen U) (hUc : IsPreconnected U) (hUne : U.Nonempty)
    {p₀ a : analyticSubring U} {f₀ g : ℂ → ℂ}
    (hp0 : (p₀ : Germ (𝓟 U) ℂ) = ↑f₀)
    (ha : (a : Germ (𝓟 U) ℂ) = ↑g) (q : Polynomial (Polynomial ℂ))
    (hzero : q.eval₂ (polyToMeroVia p₀)
        (algebraMap (analyticSubring U) (meroField U) a) = 0) :
    Set.EqOn (fun ξ => q.eval₂ (Polynomial.evalRingHom (f₀ ξ)) (g ξ)) 0 U := by
  haveI := isDomain_analyticSubring U hUo hUc hUne
  have hzero' : algebraMap (analyticSubring U) (meroField U)
      (q.eval₂ (polyToAnalyticVia U p₀) a) = 0 := by
    have heq : q.eval₂ (polyToMeroVia p₀)
        (algebraMap (analyticSubring U) (meroField U) a)
        = algebraMap (analyticSubring U) (meroField U)
            (q.eval₂ (polyToAnalyticVia U p₀) a) := by
      rw [show polyToMeroVia p₀ =
          (algebraMap (analyticSubring U) (meroField U)).comp (polyToAnalyticVia U p₀) from rfl]
      exact (Polynomial.hom_eval₂ q (polyToAnalyticVia U p₀)
        (algebraMap (analyticSubring U) (meroField U)) a).symm
    rwa [← heq]
  rw [meroField_algebraMap_eq_zero_iff U hUo hUc hUne] at hzero'
  have hval := eval₂_polyToAnalyticVia_val (U := U) hp0 ha q
  rw [hzero', ZeroMemClass.coe_zero] at hval
  have hgerm : (↑(fun ξ => q.eval₂ (Polynomial.evalRingHom (f₀ ξ)) (g ξ)) : Germ (𝓟 U) ℂ)
      = 0 := hval.symm
  rw [← Germ.coe_zero, Germ.coe_eq] at hgerm
  exact fun ξ hξ => eventually_principal.mp hgerm ξ hξ

end Bottcher

namespace Bottcher
open Polynomial Filter

/-- **Projection-base field relation descends to the far high-value z-domain.**
This composes the meromorphic field-to-function bridge with the annulus projection image lemma. A
polynomial relation over `ℂ(p₀)` that vanishes for the pulled-back coordinate
`a(ξ)=φ_{c₂}(ψ₁(ξ^N))` forces the original relation `q(z,φ_{c₂}(z))=0` on every far-field point whose
`φ_{c₁}` value admits an exterior-annulus `N`-th root. -/
theorem eqOn_eval₂_bottcher_on_far_high_values_of_eval₂_polyToMeroVia_zero
    {c₁ c₂ : ℂ} {ψ₁ : ℂ → ℂ} {R R' : ℝ} {N : ℕ}
    (hR'pos : 0 < R') (hNpos : 0 < N)
    (hψleft : ∀ z, R < ‖z‖ → ψ₁ (bottcherCoord c₁ z) = z)
    {p₀ a : analyticSubring {ξ : ℂ | R' < ‖ξ‖}}
    (hp0 : (p₀ : Germ (𝓟 {ξ : ℂ | R' < ‖ξ‖}) ℂ) = ↑(fun ξ => ψ₁ (ξ ^ N)))
    (ha : (a : Germ (𝓟 {ξ : ℂ | R' < ‖ξ‖}) ℂ) =
      ↑(fun ξ => bottcherCoord c₂ (ψ₁ (ξ ^ N))))
    (q : Polynomial (Polynomial ℂ))
    (hzero : q.eval₂ (polyToMeroVia p₀)
        (algebraMap (analyticSubring {ξ : ℂ | R' < ‖ξ‖})
          (meroField {ξ : ℂ | R' < ‖ξ‖}) a) = 0) :
    Set.EqOn (fun z => q.eval₂ (Polynomial.evalRingHom z) (bottcherCoord c₂ z)) 0
      {z : ℂ | R < ‖z‖ ∧ R' ^ N < ‖bottcherCoord c₁ z‖} := by
  have hrel := eqOn_pullback_eval₂_of_eval₂_polyToMeroVia_zero
    isOpen_exterior (isPreconnected_exterior hR'pos) (nonempty_exterior hR'pos)
    hp0 ha q hzero
  exact eqOn_eval₂_bottcher_on_far_high_values_of_pullback
    (c₁ := c₁) (c₂ := c₂) (ψ₁ := ψ₁) (R := R) (R' := R') (N := N)
    q hNpos hψleft hrel

end Bottcher

namespace Bottcher
open Polynomial Filter

/-- **Pulled-back `φ₂` transcendence from no relation on the far high-value z-domain.**
For the exterior annulus projection `p₀(ξ)=ψ₁(ξ^N)` and coordinate
`a(ξ)=φ_{c₂}(ψ₁(ξ^N))`, algebraicity of `a` over the projection-base copy of `ℂ(z)` would produce a
nonzero polynomial relation `q(z,φ_{c₂}(z))=0` on the explicit far high-value subset. Thus any
function-level obstruction on that subset proves the exact `hGtr` needed by the annulus route. -/
theorem transcendental_pullback_bottcher_of_no_far_high_relation
    {c₁ c₂ : ℂ} {ψ₁ : ℂ → ℂ} {R R' : ℝ} {N : ℕ}
    (hR'pos : 0 < R') (hNpos : 0 < N)
    (hψleft : ∀ z, R < ‖z‖ → ψ₁ (bottcherCoord c₁ z) = z)
    {p₀ a : analyticSubring {ξ : ℂ | R' < ‖ξ‖}}
    (hp0 : (p₀ : Germ (𝓟 {ξ : ℂ | R' < ‖ξ‖}) ℂ) = ↑(fun ξ => ψ₁ (ξ ^ N)))
    (hpInf : ((fun ξ => ψ₁ (ξ ^ N)) '' {ξ : ℂ | R' < ‖ξ‖}).Infinite)
    (ha : (a : Germ (𝓟 {ξ : ℂ | R' < ‖ξ‖}) ℂ) =
      ↑(fun ξ => bottcherCoord c₂ (ψ₁ (ξ ^ N))))
    (hno : ∀ q : Polynomial (Polynomial ℂ), q ≠ 0 →
      ¬ Set.EqOn (fun z => q.eval₂ (Polynomial.evalRingHom z) (bottcherCoord c₂ z)) 0
        {z : ℂ | R < ‖z‖ ∧ R' ^ N < ‖bottcherCoord c₁ z‖}) :
    letI : IsDomain (analyticSubring {ξ : ℂ | R' < ‖ξ‖}) :=
      isDomain_analyticSubring {ξ : ℂ | R' < ‖ξ‖} isOpen_exterior
        (isPreconnected_exterior hR'pos) (nonempty_exterior hR'pos)
    letI : Algebra (RatFunc ℂ) (meroField {ξ : ℂ | R' < ‖ξ‖}) :=
      (ratfuncToMeroVia p₀ hp0 hpInf isOpen_exterior
        (isPreconnected_exterior hR'pos) (nonempty_exterior hR'pos)).toAlgebra
    Transcendental (RatFunc ℂ)
      (algebraMap (analyticSubring {ξ : ℂ | R' < ‖ξ‖})
        (meroField {ξ : ℂ | R' < ‖ξ‖}) a) := by
  let U : Set ℂ := {ξ : ℂ | R' < ‖ξ‖}
  have hUo : IsOpen U := isOpen_exterior
  have hUc : IsPreconnected U := isPreconnected_exterior hR'pos
  have hUne : U.Nonempty := nonempty_exterior hR'pos
  haveI : IsDomain (analyticSubring U) := isDomain_analyticSubring U hUo hUc hUne
  letI algK : Algebra (RatFunc ℂ) (meroField U) :=
    (ratfuncToMeroVia p₀ hp0 hpInf hUo hUc hUne).toAlgebra
  letI algA : Algebra (Polynomial ℂ) (meroField U) := (polyToMeroVia p₀).toAlgebra
  haveI hst : IsScalarTower (Polynomial ℂ) (RatFunc ℂ) (meroField U) := by
    apply IsScalarTower.of_algebraMap_eq
    intro p
    show polyToMeroVia p₀ p = ratfuncToMeroVia p₀ hp0 hpInf hUo hUc hUne
      (algebraMap (Polynomial ℂ) (RatFunc ℂ) p)
    rw [show ratfuncToMeroVia p₀ hp0 hpInf hUo hUc hUne
        (algebraMap (Polynomial ℂ) (RatFunc ℂ) p) = polyToMeroVia p₀ p
      from IsFractionRing.lift_algebraMap (polyToMeroVia_injective p₀ hp0 hpInf hUo hUc hUne) p]
  show ¬ IsAlgebraic (RatFunc ℂ) (algebraMap (analyticSubring U) (meroField U) a)
  rw [← IsFractionRing.isAlgebraic_iff (Polynomial ℂ) (RatFunc ℂ) (meroField U)]
  rintro ⟨q, hq0, hqe⟩
  apply hno q hq0
  rw [aeval_def] at hqe
  have halg : (algebraMap (Polynomial ℂ) (meroField U)) = polyToMeroVia p₀ := rfl
  rw [halg] at hqe
  exact eqOn_eval₂_bottcher_on_far_high_values_of_eval₂_polyToMeroVia_zero
    (c₁ := c₁) (c₂ := c₂) (ψ₁ := ψ₁) (R := R) (R' := R') (N := N)
    hR'pos hNpos hψleft hp0 ha q hqe

end Bottcher

namespace Bottcher
open Polynomial Filter

/-- **Generic transition-function transcendence bridge.**
For an analytic coordinate `p₀` represented by `f₀` and an analytic function `a` represented by `g`,
transcendence of `a` over the projection-base copy of `RatFunc ℂ` follows from the concrete
function-level statement that no nonzero `q ∈ ℂ[f₀][Y]` vanishes as `q(f₀ x, g x)` on `U`.

This is the algebraic core of the direct far-value route: take `f₀(w)=w` and
`g(w)=φ_{c₂}(ψ₁(w))`, rather than passing through a finite root cover where degrees multiply. -/
theorem transcendental_of_no_eval₂_relation_via {U : Set ℂ}
    (hUo : IsOpen U) (hUc : IsPreconnected U) (hUne : U.Nonempty)
    {p₀ a : analyticSubring U} {f₀ g : ℂ → ℂ}
    (hp0 : (p₀ : Germ (𝓟 U) ℂ) = ↑f₀)
    (hpInf : (f₀ '' U).Infinite)
    (ha : (a : Germ (𝓟 U) ℂ) = ↑g)
    (hno : ∀ q : Polynomial (Polynomial ℂ), q ≠ 0 →
      ¬ Set.EqOn (fun x => q.eval₂ (Polynomial.evalRingHom (f₀ x)) (g x)) 0 U) :
    letI : IsDomain (analyticSubring U) := isDomain_analyticSubring U hUo hUc hUne
    letI : Algebra (RatFunc ℂ) (meroField U) :=
      (ratfuncToMeroVia p₀ hp0 hpInf hUo hUc hUne).toAlgebra
    Transcendental (RatFunc ℂ) (algebraMap (analyticSubring U) (meroField U) a) := by
  haveI : IsDomain (analyticSubring U) := isDomain_analyticSubring U hUo hUc hUne
  letI algK : Algebra (RatFunc ℂ) (meroField U) :=
    (ratfuncToMeroVia p₀ hp0 hpInf hUo hUc hUne).toAlgebra
  letI algA : Algebra (Polynomial ℂ) (meroField U) := (polyToMeroVia p₀).toAlgebra
  haveI hst : IsScalarTower (Polynomial ℂ) (RatFunc ℂ) (meroField U) := by
    apply IsScalarTower.of_algebraMap_eq
    intro p
    show polyToMeroVia p₀ p = ratfuncToMeroVia p₀ hp0 hpInf hUo hUc hUne
      (algebraMap (Polynomial ℂ) (RatFunc ℂ) p)
    rw [show ratfuncToMeroVia p₀ hp0 hpInf hUo hUc hUne
        (algebraMap (Polynomial ℂ) (RatFunc ℂ) p) = polyToMeroVia p₀ p
      from IsFractionRing.lift_algebraMap (polyToMeroVia_injective p₀ hp0 hpInf hUo hUc hUne) p]
  show ¬ IsAlgebraic (RatFunc ℂ) (algebraMap (analyticSubring U) (meroField U) a)
  rw [← IsFractionRing.isAlgebraic_iff (Polynomial ℂ) (RatFunc ℂ) (meroField U)]
  rintro ⟨q, hq0, hqe⟩
  apply hno q hq0
  rw [aeval_def] at hqe
  have halg : (algebraMap (Polynomial ℂ) (meroField U)) = polyToMeroVia p₀ := rfl
  rw [halg] at hqe
  exact eqOn_pullback_eval₂_of_eval₂_polyToMeroVia_zero hUo hUc hUne hp0 ha q hqe

end Bottcher

namespace Bottcher
open Polynomial Filter

/-- **Direct far-value transition transcendence.**
On an exterior value annulus, if `ψ₁` is analytic there and lands in the `c₂` escape set, the transition
function `H(w)=φ_{c₂}(ψ₁(w))` is an analytic germ over the identity coordinate `w`. Its transcendence
over `ℂ(w)` is reduced to the concrete function-level no-relation statement for `q(w,H(w))`.

This is the finite-cover bypass: it keeps the first variable as the actual far Böttcher value `w`, so
relations do not become `P(ξ^N,H)` and no `N * degree` obstruction appears. -/
theorem exists_value_transition_transcendental_of_no_relation
    {c₂ : ℂ} {ψ₁ : ℂ → ℂ} {R' : ℝ} (hR'pos : 0 < R')
    (hψan : ∀ w ∈ {w : ℂ | R' < ‖w‖}, AnalyticAt ℂ ψ₁ w)
    (hcont : ∀ w ∈ {w : ℂ | R' < ‖w‖}, ψ₁ w ∈ escapeOpen c₂)
    (hno : ∀ q : Polynomial (Polynomial ℂ), q ≠ 0 →
      ¬ Set.EqOn (fun w => q.eval₂ (Polynomial.evalRingHom w) (bottcherCoord c₂ (ψ₁ w)))
        0 {w : ℂ | R' < ‖w‖}) :
    ∃ (p₀ : analyticSubring {w : ℂ | R' < ‖w‖})
      (hp0 : (p₀ : Germ (𝓟 {w : ℂ | R' < ‖w‖}) ℂ) = ↑(id : ℂ → ℂ))
      (hpInf : ((id : ℂ → ℂ) '' {w : ℂ | R' < ‖w‖}).Infinite)
      (a : analyticSubring {w : ℂ | R' < ‖w‖}),
      (a : Germ (𝓟 {w : ℂ | R' < ‖w‖}) ℂ) =
        ↑(fun w => bottcherCoord c₂ (ψ₁ w)) ∧
      (letI : IsDomain (analyticSubring {w : ℂ | R' < ‖w‖}) :=
        isDomain_analyticSubring {w : ℂ | R' < ‖w‖} isOpen_exterior
          (isPreconnected_exterior hR'pos) (nonempty_exterior hR'pos)
       letI : Algebra (RatFunc ℂ) (meroField {w : ℂ | R' < ‖w‖}) :=
        (ratfuncToMeroVia p₀ hp0 hpInf isOpen_exterior
          (isPreconnected_exterior hR'pos) (nonempty_exterior hR'pos)).toAlgebra
       Transcendental (RatFunc ℂ)
        (algebraMap (analyticSubring {w : ℂ | R' < ‖w‖})
          (meroField {w : ℂ | R' < ‖w‖}) a)) := by
  let U : Set ℂ := {w : ℂ | R' < ‖w‖}
  let p₀ : analyticSubring U :=
    ⟨(↑(id : ℂ → ℂ) : Germ (𝓟 U) ℂ), id, analyticOnNhd_id, rfl⟩
  have hp0 : (p₀ : Germ (𝓟 U) ℂ) = ↑(id : ℂ → ℂ) := rfl
  have hpInf : ((id : ℂ → ℂ) '' U).Infinite := by
    have hid : ((id : ℂ → ℂ) '' U) = U := by
      ext w; simp
    rw [hid]
    exact infinite_exterior hR'pos
  obtain ⟨a, ha⟩ := exists_rotInvariant_a2 (c₂ := c₂) (U := U) (ψ₁ := ψ₁) (n := 0)
    (by simpa [U] using hψan) (by simpa [U] using hcont)
  have haH : (a : Germ (𝓟 U) ℂ) = ↑(fun w => bottcherCoord c₂ (ψ₁ w)) := by
    simpa using ha
  have htr := transcendental_of_no_eval₂_relation_via
    (U := U) isOpen_exterior (isPreconnected_exterior hR'pos) (nonempty_exterior hR'pos)
    (p₀ := p₀) (a := a) (f₀ := id) (g := fun w => bottcherCoord c₂ (ψ₁ w))
    hp0 hpInf haH (by simpa [U] using hno)
  exact ⟨by simpa [U] using p₀, by simpa [U] using hp0, by simpa [U] using hpInf,
    by simpa [U] using a, by simpa [U] using haH, by simpa [U] using htr⟩

end Bottcher

namespace Bottcher
open Polynomial Filter

/-- **Pointwise square-defect identity for the far-value transition.**
Let `H(w)=φ_{c₂}(ψ₁(w))` and suppose `ψ₁` is a left inverse to `φ_{c₁}` on the relevant far points and
`φ_{c₁}(ψ₁ w)=w`. Then the failure of `H` to conjugate squaring is exactly the difference between
reading `φ_{c₂}` at the two quadratic images with parameters `c₁` and `c₂`:
`H(w²)-H(w)² = φ₂(z²+c₁)-φ₂(z²+c₂)`, where `z=ψ₁(w)`.

This is the concrete asymptotic/valuation hook for the direct transition route. -/
theorem value_transition_square_defect_at
    {c₁ c₂ w : ℂ} {ψ₁ : ℂ → ℂ} {R : ℝ}
    (hψleft : ∀ z, R < ‖z‖ → ψ₁ (bottcherCoord c₁ z) = z)
    (hproj : bottcherCoord c₁ (ψ₁ w) = w)
    (hzqR : R < ‖quadratic c₁ (ψ₁ w)‖)
    (hc₁z : ‖c₁‖ ≤ ‖ψ₁ w‖) (hc₂z : ‖c₂‖ ≤ ‖ψ₁ w‖) (hz2 : 2 < ‖ψ₁ w‖) :
    bottcherCoord c₂ (ψ₁ (w ^ 2)) - (bottcherCoord c₂ (ψ₁ w)) ^ 2 =
      bottcherCoord c₂ (quadratic c₁ (ψ₁ w)) - bottcherCoord c₂ (quadratic c₂ (ψ₁ w)) := by
  have hφsq : bottcherCoord c₁ (quadratic c₁ (ψ₁ w)) = w ^ 2 := by
    rw [bottcherCoord_quadratic hc₁z hz2, hproj]
  have hψsq : ψ₁ (w ^ 2) = quadratic c₁ (ψ₁ w) := by
    rw [← hφsq]
    exact hψleft (quadratic c₁ (ψ₁ w)) hzqR
  have hφ₂sq : bottcherCoord c₂ (quadratic c₂ (ψ₁ w)) = (bottcherCoord c₂ (ψ₁ w)) ^ 2 :=
    bottcherCoord_quadratic hc₂z hz2
  rw [hψsq, ← hφ₂sq]

end Bottcher

namespace Bottcher
open Polynomial Filter

/-- **Exact transferred-dynamics identity for the far-value transition.**
For `H(w)=φ_{c₂}(ψ₁(w))`, the transported `c₂` map
`T(w)=φ_{c₁}((ψ₁ w)^(2 : ℕ)+c₂)` satisfies `H(T(w))=H(w)^(2 : ℕ)` whenever all points are in the far inverse domain.
This is stronger than the square-defect asymptotic: it is the exact conjugacy relation to use in the
value-transition route. -/
theorem value_transition_conj_transferred_quadratic_at
    {c₁ c₂ w : ℂ} {ψ₁ : ℂ → ℂ} {R : ℝ}
    (hψleft : ∀ z, R < ‖z‖ → ψ₁ (bottcherCoord c₁ z) = z)
    (hzqR : R < ‖quadratic c₂ (ψ₁ w)‖)
    (hc₂z : ‖c₂‖ ≤ ‖ψ₁ w‖) (hz2 : 2 < ‖ψ₁ w‖) :
    bottcherCoord c₂ (ψ₁ (bottcherCoord c₁ (quadratic c₂ (ψ₁ w)))) =
      (bottcherCoord c₂ (ψ₁ w)) ^ 2 := by
  have hψT : ψ₁ (bottcherCoord c₁ (quadratic c₂ (ψ₁ w))) = quadratic c₂ (ψ₁ w) :=
    hψleft (quadratic c₂ (ψ₁ w)) hzqR
  rw [hψT]
  exact bottcherCoord_quadratic hc₂z hz2

end Bottcher

namespace Bottcher
open Polynomial Filter

/-- **Push an algebraic relation through a semiconjugacy.**
If `q(x,H x)` vanishes on `V`, `T` maps `U` into `V`, and `H(T x)=H x^(2 : ℕ)` on `U`, then the pushed
relation `q(T x, H x^(2 : ℕ))` vanishes on `U`. This is the function-level algebraic transfer used before
eliminating `H` to get an algebraic relation for the transported map `T`. -/
theorem eqOn_transition_relation_of_eqOn_relation_and_conj
    {U V : Set ℂ} {H T : ℂ → ℂ} (q : Polynomial (Polynomial ℂ))
    (hTmaps : Set.MapsTo T U V)
    (hrel : Set.EqOn (fun x => q.eval₂ (Polynomial.evalRingHom x) (H x)) (fun _ => (0 : ℂ)) V)
    (hconj : ∀ x ∈ U, H (T x) = (H x) ^ 2) :
    Set.EqOn (fun x => q.eval₂ (Polynomial.evalRingHom (T x)) ((H x) ^ 2)) (fun _ => (0 : ℂ)) U := by
  intro x hx
  have h : q.eval₂ (Polynomial.evalRingHom (T x)) (H (T x)) = 0 := hrel (hTmaps hx)
  rwa [hconj x hx] at h

end Bottcher

namespace Bottcher
open Polynomial Filter

/-- A common root prevents two one-variable polynomials over a field from being coprime. -/
lemma not_isCoprime_of_common_root {K : Type*} [Field K]
    {f g : K[X]} {a : K} (hf : f.eval a = 0) (hg : g.eval a = 0) :
    ¬ IsCoprime f g := by
  rintro ⟨u, v, huv⟩
  have h := congrArg (fun p : K[X] => p.eval a) huv
  simp [eval_add, eval_mul, hf, hg] at h

/-- A common root forces the resultant to vanish, provided the pair is not both zero. -/
lemma resultant_eq_zero_of_common_root {K : Type*} [Field K]
    {f g : K[X]} {a : K} (hf : f.eval a = 0) (hg : g.eval a = 0)
    (hfg : f ≠ 0 ∨ g ≠ 0) :
    Polynomial.resultant f g = 0 := by
  rw [Polynomial.resultant_eq_zero_iff]
  exact ⟨hfg, not_isCoprime_of_common_root hf hg⟩

/-- A common root also kills any fixed-size Sylvester resultant whose sizes dominate the specialized
degrees. This is the form needed after evaluating a universal resultant, where the matrix size is fixed
before specialization. -/
lemma resultant_eq_zero_of_common_root_of_natDegree_le {K : Type*} [Field K]
    {f g : K[X]} {a : K} {m n : ℕ}
    (hfroot : f.eval a = 0) (hgroot : g.eval a = 0)
    (hfg : f ≠ 0 ∨ g ≠ 0)
    (hm : f.natDegree ≤ m) (hn : g.natDegree ≤ n) :
    Polynomial.resultant f g m n = 0 := by
  obtain ⟨km, rfl⟩ := exists_add_of_le hm
  obtain ⟨kn, rfl⟩ := exists_add_of_le hn
  rw [Polynomial.resultant_add_left_deg, Polynomial.resultant_add_right_deg]
  · simp [resultant_eq_zero_of_common_root hfroot hgroot hfg]
  · exact le_rfl
  · exact le_rfl

/-- The `q(W,Y)` member of the universal elimination pair, viewed as a polynomial in `Y` with
coefficients in `ℂ[W][Z]`. -/
noncomputable def transitionResultantLeft (q : Polynomial (Polynomial ℂ)) :
    Polynomial (Polynomial (Polynomial ℂ)) :=
  q.map (Polynomial.C : Polynomial ℂ →+* Polynomial (Polynomial ℂ))

/-- The `q(Z,Y²)` member of the universal elimination pair, viewed as a polynomial in `Y` with
coefficients in `ℂ[W][Z]`. -/
noncomputable def transitionResultantRight (q : Polynomial (Polynomial ℂ)) :
    Polynomial (Polynomial (Polynomial ℂ)) :=
  (q.map (Polynomial.mapRingHom (Polynomial.C : ℂ →+* Polynomial ℂ))).comp (Polynomial.X ^ 2)

/-- The universal bivariate resultant `Res_Y(q(W,Y), q(Z,Y²))`. -/
noncomputable def transitionResultant (q : Polynomial (Polynomial ℂ)) : Polynomial (Polynomial ℂ) :=
  Polynomial.resultant (transitionResultantLeft q) (transitionResultantRight q)
    (transitionResultantLeft q).natDegree (transitionResultantRight q).natDegree

lemma eval_bivar_C_left (p : Polynomial ℂ) (x z : ℂ) :
    Polynomial.eval₂ (Polynomial.evalRingHom x) z (Polynomial.C p : Polynomial (Polynomial ℂ)) =
      p.eval x := by
  simp [Polynomial.eval₂_C]

lemma eval_bivar_map_C_right (p : Polynomial ℂ) (x z : ℂ) :
    Polynomial.eval₂ (Polynomial.evalRingHom x) z (p.map (Polynomial.C : ℂ →+* Polynomial ℂ)) =
      p.eval z := by
  simpa [Polynomial.eval₂_evalRingHom] using Polynomial.evalEval_map_C x z p

lemma map_transitionResultantLeft_eval (q : Polynomial (Polynomial ℂ)) (x z : ℂ) :
    (transitionResultantLeft q).map (Polynomial.eval₂RingHom (Polynomial.evalRingHom x) z) =
      q.map (Polynomial.evalRingHom x) := by
  rw [transitionResultantLeft, Polynomial.map_map]
  congr 1
  ext a <;> simp

lemma map_transitionResultantRight_eval (q : Polynomial (Polynomial ℂ)) (x z : ℂ) :
    (transitionResultantRight q).map (Polynomial.eval₂RingHom (Polynomial.evalRingHom x) z) =
      (q.map (Polynomial.evalRingHom z)).comp (Polynomial.X ^ 2) := by
  rw [transitionResultantRight, Polynomial.map_comp, Polynomial.map_pow, Polynomial.map_X,
    Polynomial.map_map]
  congr 1
  ext a
  simp [eval_bivar_map_C_right]

lemma eval_transitionResultant (q : Polynomial (Polynomial ℂ)) (x z : ℂ) :
    (transitionResultant q).eval₂ (Polynomial.evalRingHom x) z =
      Polynomial.resultant (q.map (Polynomial.evalRingHom x))
        ((q.map (Polynomial.evalRingHom z)).comp (Polynomial.X ^ 2))
        (transitionResultantLeft q).natDegree (transitionResultantRight q).natDegree := by
  rw [transitionResultant]
  change (Polynomial.eval₂RingHom (Polynomial.evalRingHom x) z)
      (Polynomial.resultant (transitionResultantLeft q) (transitionResultantRight q)
        (transitionResultantLeft q).natDegree (transitionResultantRight q).natDegree) = _
  rw [← Polynomial.resultant_map_map (φ := Polynomial.eval₂RingHom (Polynomial.evalRingHom x) z)]
  rw [map_transitionResultantLeft_eval, map_transitionResultantRight_eval]

/-- Evaluation after substituting the parabola `Z = W² + d`. -/
lemma eval_quadratic_substitution (R : Polynomial (Polynomial ℂ)) (d x : ℂ) :
    (R.eval (Polynomial.X ^ 2 + Polynomial.C d)).eval x =
      R.eval₂ (Polynomial.evalRingHom x) (x ^ 2 + d) := by
  rw [Polynomial.eval₂_eq_eval_map]
  induction R using Polynomial.induction_on' with
  | add p q hp hq => simp [hp, hq]
  | monomial n a => simp [Polynomial.eval_monomial]

/-- If `R(W,W²+d)` has infinitely many roots, then it is the zero polynomial. -/
lemma quadratic_substitution_zero_of_infinite_roots (R : Polynomial (Polynomial ℂ)) (d : ℂ)
    (h : Set.Infinite {x : ℂ | R.eval₂ (Polynomial.evalRingHom x) (x ^ 2 + d) = 0}) :
    R.eval (Polynomial.X ^ 2 + Polynomial.C d) = 0 := by
  apply Polynomial.eq_zero_of_infinite_isRoot
  refine h.mono ?_
  intro x hx
  rw [Set.mem_setOf_eq, Polynomial.IsRoot.def, eval_quadratic_substitution]
  exact hx

/-- Vanishing after the substitution `Z = W²+d` is exactly divisibility by `Z-(W²+d)`. -/
lemma quadratic_factor_of_quadratic_substitution_zero (R : Polynomial (Polynomial ℂ)) (d : ℂ)
    (h : R.eval (Polynomial.X ^ 2 + Polynomial.C d) = 0) :
    Polynomial.X - Polynomial.C (Polynomial.X ^ 2 + Polynomial.C d) ∣ R := by
  rw [Polynomial.dvd_iff_isRoot, Polynomial.IsRoot.def]
  exact h

/-- Infinite pointwise vanishing on the parabola `Z=W²+d` forces the corresponding bivariate factor. -/
lemma quadratic_factor_of_eval₂_quadratic_eq_zero_on_infinite
    (R : Polynomial (Polynomial ℂ)) (d : ℂ)
    (h : Set.Infinite {x : ℂ | R.eval₂ (Polynomial.evalRingHom x) (x ^ 2 + d) = 0}) :
    Polynomial.X - Polynomial.C (Polynomial.X ^ 2 + Polynomial.C d) ∣ R := by
  exact quadratic_factor_of_quadratic_substitution_zero R d
    (quadratic_substitution_zero_of_infinite_roots R d h)

/-- The explicit bivariate factor for the parabola `Z = W²+d`. -/
noncomputable def quadraticRelationFactor (d : ℂ) : Polynomial (Polynomial ℂ) :=
  Polynomial.X - Polynomial.C (Polynomial.X ^ 2 + Polynomial.C d)

lemma eval_quadraticRelationFactor (d w z : ℂ) :
    (quadraticRelationFactor d).eval₂ (Polynomial.evalRingHom w) z = z - (w ^ 2 + d) := by
  rw [quadraticRelationFactor, Polynomial.eval₂_sub, Polynomial.eval₂_X, Polynomial.eval₂_C]
  change z - (Polynomial.X ^ 2 + Polynomial.C d).eval w = z - (w ^ 2 + d)
  simp

/-- **Scaled-remainder bridge to the exact shifted-parabola factor.**
After exact division by `Z-(W²+d)`, the only obstruction is the univariate remainder
`R(W,W²+d)`.  If that remainder is smaller than its own leading scale along the Böttcher ray,
then the remainder is zero, hence the shifted-parabola factor divides `R`. -/
theorem quadratic_factor_of_bottcher_scaled_quadratic_remainder_zero
    (R : Polynomial (Polynomial ℂ)) (d c : ℂ)
    (hsmall : Tendsto
      (fun t : ℝ => ((t : ℂ)⁻¹) ^
        (R.eval (Polynomial.X ^ 2 + Polynomial.C d)).natDegree *
          (R.eval (Polynomial.X ^ 2 + Polynomial.C d)).eval (bottcherCoord c (t : ℂ))) atTop
      (𝓝 0)) :
    quadraticRelationFactor d ∣ R := by
  simpa [quadraticRelationFactor] using
    (quadratic_factor_of_quadratic_substitution_zero R d
      (polynomial_eq_zero_of_bottcher_scaled_eval_tendsto_zero c
        (R.eval (Polynomial.X ^ 2 + Polynomial.C d)) hsmall))

lemma monic_quadraticRelationFactor (d : ℂ) : (quadraticRelationFactor d).Monic := by
  rw [quadraticRelationFactor]
  exact Polynomial.monic_X_sub_C (Polynomial.X ^ 2 + Polynomial.C d)

lemma natDegree_quadraticRelationFactor (d : ℂ) : (quadraticRelationFactor d).natDegree = 1 := by
  rw [quadraticRelationFactor]
  exact Polynomial.natDegree_X_sub_C (Polynomial.X ^ 2 + Polynomial.C d)

/-- Dividing by the parabola factor strictly lowers degree in the transported variable. -/
lemma quotient_natDegree_lt_of_quadratic_factor
    {R Q : Polynomial (Polynomial ℂ)} {d : ℂ}
    (hR : R ≠ 0) (hQeq : R = quadraticRelationFactor d * Q) :
    Q.natDegree < R.natDegree := by
  have hQ : Q ≠ 0 := by
    intro hzero
    rw [hQeq, hzero, mul_zero] at hR
    exact hR rfl
  rw [hQeq]
  have hdeg := (monic_quadraticRelationFactor d).natDegree_mul' hQ
  rw [hdeg, natDegree_quadraticRelationFactor]
  exact Nat.lt_add_of_pos_left Nat.zero_lt_one

/-- If a relation has the parabola factor, then away from `T(w)=w²+d` the quotient is still a
relation. This is the factor-stripping step for a minimal-degree no-relation argument. -/
lemma exists_lower_relation_on_nonparabola_of_factor_relation
    {U : Set ℂ} {T : ℂ → ℂ} {R : Polynomial (Polynomial ℂ)} {d : ℂ}
    (hfac : quadraticRelationFactor d ∣ R)
    (hrel : Set.EqOn (fun w => R.eval₂ (Polynomial.evalRingHom w) (T w)) (fun _ => (0 : ℂ)) U) :
    ∃ Q : Polynomial (Polynomial ℂ), R = quadraticRelationFactor d * Q ∧
      Set.EqOn (fun w => Q.eval₂ (Polynomial.evalRingHom w) (T w)) (fun _ => (0 : ℂ))
        {w : ℂ | w ∈ U ∧ T w ≠ w ^ 2 + d} := by
  rcases hfac with ⟨Q, hQ⟩
  refine ⟨Q, hQ, ?_⟩
  intro w hw
  have h := hrel hw.1
  rw [hQ] at h
  have hprod : (T w - (w ^ 2 + d)) * Q.eval₂ (Polynomial.evalRingHom w) (T w) = 0 := by
    simpa [Polynomial.eval₂_mul, eval_quadraticRelationFactor] using h
  exact (mul_eq_zero.mp hprod).resolve_left (sub_ne_zero.mpr hw.2)

/-- Choose a minimal-degree nonzero transported relation, if any exists. The supplied descent
contradiction for minimal relations then rules out all nonzero relations. -/
theorem no_relation_of_minimal_counterexample_descent
    {U : Set ℂ} {T : ℂ → ℂ}
    (hdesc : ∀ R : Polynomial (Polynomial ℂ), R ≠ 0 →
      Set.EqOn (fun w => R.eval₂ (Polynomial.evalRingHom w) (T w)) (fun _ => (0 : ℂ)) U →
      (∀ Q : Polynomial (Polynomial ℂ), Q ≠ 0 →
        Set.EqOn (fun w => Q.eval₂ (Polynomial.evalRingHom w) (T w)) (fun _ => (0 : ℂ)) U →
        R.natDegree ≤ Q.natDegree) → False) :
    ∀ R : Polynomial (Polynomial ℂ), R ≠ 0 →
      ¬ Set.EqOn (fun w => R.eval₂ (Polynomial.evalRingHom w) (T w)) (fun _ => (0 : ℂ)) U := by
  classical
  intro R hR0 hRrel
  let P : ℕ → Prop := fun n => ∃ Q : Polynomial (Polynomial ℂ), Q ≠ 0 ∧
    Set.EqOn (fun w => Q.eval₂ (Polynomial.evalRingHom w) (T w)) (fun _ => (0 : ℂ)) U ∧
    Q.natDegree = n
  have hP : ∃ n, P n := ⟨R.natDegree, R, hR0, hRrel, rfl⟩
  let n := Nat.find hP
  have hn : P n := Nat.find_spec hP
  rcases hn with ⟨Q, hQ0, hQrel, hQdeg⟩
  have hmin : ∀ S : Polynomial (Polynomial ℂ), S ≠ 0 →
      Set.EqOn (fun w => S.eval₂ (Polynomial.evalRingHom w) (T w)) (fun _ => (0 : ℂ)) U →
      Q.natDegree ≤ S.natDegree := by
    intro S hS0 hSrel
    have hPS : P S.natDegree := ⟨S, hS0, hSrel, rfl⟩
    rw [hQdeg]
    exact Nat.find_min' hP hPS
  exact hdesc Q hQ0 hQrel hmin

/-- Minimal-degree contradiction for the parabola-factor descent.

If `R` is a nonzero relation of minimal transported-variable degree, every relation has the
parabola factor, and quotient relations on the non-parabola locus extend back to `U`, then `R` cannot
exist. This packages the induction core of the transported-map no-relation argument. -/
theorem false_of_minimal_relation_and_quadratic_factor_descent
    {U : Set ℂ} {T : ℂ → ℂ} {R : Polynomial (Polynomial ℂ)} {d : ℂ}
    (hR0 : R ≠ 0)
    (hrel : Set.EqOn (fun w => R.eval₂ (Polynomial.evalRingHom w) (T w)) (fun _ => (0 : ℂ)) U)
    (hmin : ∀ Q : Polynomial (Polynomial ℂ), Q ≠ 0 →
      Set.EqOn (fun w => Q.eval₂ (Polynomial.evalRingHom w) (T w)) (fun _ => (0 : ℂ)) U →
      R.natDegree ≤ Q.natDegree)
    (hfac : quadraticRelationFactor d ∣ R)
    (hext : ∀ Q : Polynomial (Polynomial ℂ),
      Set.EqOn (fun w => Q.eval₂ (Polynomial.evalRingHom w) (T w)) (fun _ => (0 : ℂ))
        {w : ℂ | w ∈ U ∧ T w ≠ w ^ 2 + d} →
      Set.EqOn (fun w => Q.eval₂ (Polynomial.evalRingHom w) (T w)) (fun _ => (0 : ℂ)) U) :
    False := by
  obtain ⟨Q, hRQ, hQrelSub⟩ :=
    exists_lower_relation_on_nonparabola_of_factor_relation hfac hrel
  have hQ0 : Q ≠ 0 := by
    intro hzero
    rw [hRQ, hzero, mul_zero] at hR0
    exact hR0 rfl
  have hQrel :
      Set.EqOn (fun w => Q.eval₂ (Polynomial.evalRingHom w) (T w)) (fun _ => (0 : ℂ)) U :=
    hext Q hQrelSub
  have hle : R.natDegree ≤ Q.natDegree := hmin Q hQ0 hQrel
  have hlt : Q.natDegree < R.natDegree := quotient_natDegree_lt_of_quadratic_factor hR0 hRQ
  exact Nat.lt_irrefl Q.natDegree (lt_of_lt_of_le hlt hle)

/-- Direct no-relation criterion from the parabola-factor descent.

To use this for the transported Böttcher map, the remaining analytic work is exactly:
1. any nonzero relation on `U` forces the factor `Z-(W²+d)`;
2. the non-parabola locus is determining for polynomial relations. -/
theorem no_relation_of_quadratic_factor_descent
    {U : Set ℂ} {T : ℂ → ℂ} {d : ℂ}
    (hfac : ∀ R : Polynomial (Polynomial ℂ), R ≠ 0 →
      Set.EqOn (fun w => R.eval₂ (Polynomial.evalRingHom w) (T w)) (fun _ => (0 : ℂ)) U →
      quadraticRelationFactor d ∣ R)
    (hext : ∀ Q : Polynomial (Polynomial ℂ),
      Set.EqOn (fun w => Q.eval₂ (Polynomial.evalRingHom w) (T w)) (fun _ => (0 : ℂ))
        {w : ℂ | w ∈ U ∧ T w ≠ w ^ 2 + d} →
      Set.EqOn (fun w => Q.eval₂ (Polynomial.evalRingHom w) (T w)) (fun _ => (0 : ℂ)) U) :
    ∀ R : Polynomial (Polynomial ℂ), R ≠ 0 →
      ¬ Set.EqOn (fun w => R.eval₂ (Polynomial.evalRingHom w) (T w)) (fun _ => (0 : ℂ)) U := by
  exact no_relation_of_minimal_counterexample_descent
    (fun R hR0 hrel hmin =>
      false_of_minimal_relation_and_quadratic_factor_descent hR0 hrel hmin (hfac R hR0 hrel) hext)

/-- If a relation in arbitrary coordinates `(A x, B x)` has the parabola factor, then away from
`B x = A x²+d` the quotient is still a relation. -/
lemma exists_lower_relation_on_nonparabola_of_factor_relation_eval₂
    {α : Type*} {U : Set α} {A B : α → ℂ} {R : Polynomial (Polynomial ℂ)} {d : ℂ}
    (hfac : quadraticRelationFactor d ∣ R)
    (hrel : Set.EqOn (fun x => R.eval₂ (Polynomial.evalRingHom (A x)) (B x))
      (fun _ => (0 : ℂ)) U) :
    ∃ Q : Polynomial (Polynomial ℂ), R = quadraticRelationFactor d * Q ∧
      Set.EqOn (fun x => Q.eval₂ (Polynomial.evalRingHom (A x)) (B x)) (fun _ => (0 : ℂ))
        {x : α | x ∈ U ∧ B x ≠ (A x) ^ 2 + d} := by
  rcases hfac with ⟨Q, hQ⟩
  refine ⟨Q, hQ, ?_⟩
  intro x hx
  have h := hrel hx.1
  rw [hQ] at h
  have hprod : (B x - ((A x) ^ 2 + d)) *
      Q.eval₂ (Polynomial.evalRingHom (A x)) (B x) = 0 := by
    simpa [Polynomial.eval₂_mul, eval_quadraticRelationFactor] using h
  exact (mul_eq_zero.mp hprod).resolve_left (sub_ne_zero.mpr hx.2)

/-- Minimal-counterexample no-relation descent for arbitrary coordinate functions `(A,B)`. -/
theorem no_relation_of_minimal_counterexample_descent_eval₂
    {α : Type*} {U : Set α} {A B : α → ℂ}
    (hdesc : ∀ R : Polynomial (Polynomial ℂ), R ≠ 0 →
      Set.EqOn (fun x => R.eval₂ (Polynomial.evalRingHom (A x)) (B x)) (fun _ => (0 : ℂ)) U →
      (∀ Q : Polynomial (Polynomial ℂ), Q ≠ 0 →
        Set.EqOn (fun x => Q.eval₂ (Polynomial.evalRingHom (A x)) (B x)) (fun _ => (0 : ℂ)) U →
        R.natDegree ≤ Q.natDegree) → False) :
    ∀ R : Polynomial (Polynomial ℂ), R ≠ 0 →
      ¬ Set.EqOn (fun x => R.eval₂ (Polynomial.evalRingHom (A x)) (B x)) (fun _ => (0 : ℂ)) U := by
  classical
  intro R hR0 hRrel
  let P : ℕ → Prop := fun n => ∃ Q : Polynomial (Polynomial ℂ), Q ≠ 0 ∧
    Set.EqOn (fun x => Q.eval₂ (Polynomial.evalRingHom (A x)) (B x)) (fun _ => (0 : ℂ)) U ∧
    Q.natDegree = n
  have hP : ∃ n, P n := ⟨R.natDegree, R, hR0, hRrel, rfl⟩
  let n := Nat.find hP
  have hn : P n := Nat.find_spec hP
  rcases hn with ⟨Q, hQ0, hQrel, hQdeg⟩
  have hmin : ∀ S : Polynomial (Polynomial ℂ), S ≠ 0 →
      Set.EqOn (fun x => S.eval₂ (Polynomial.evalRingHom (A x)) (B x)) (fun _ => (0 : ℂ)) U →
      Q.natDegree ≤ S.natDegree := by
    intro S hS0 hSrel
    have hPS : P S.natDegree := ⟨S, hS0, hSrel, rfl⟩
    rw [hQdeg]
    exact Nat.find_min' hP hPS
  exact hdesc Q hQ0 hQrel hmin

/-- Minimal-degree contradiction for arbitrary coordinate functions `(A,B)` once every relation has
the shifted-parabola factor and the non-parabola quotient relation extends back to `U`. -/
theorem false_of_minimal_relation_and_quadratic_factor_descent_eval₂
    {α : Type*} {U : Set α} {A B : α → ℂ} {R : Polynomial (Polynomial ℂ)} {d : ℂ}
    (hR0 : R ≠ 0)
    (hrel : Set.EqOn (fun x => R.eval₂ (Polynomial.evalRingHom (A x)) (B x))
      (fun _ => (0 : ℂ)) U)
    (hmin : ∀ Q : Polynomial (Polynomial ℂ), Q ≠ 0 →
      Set.EqOn (fun x => Q.eval₂ (Polynomial.evalRingHom (A x)) (B x))
        (fun _ => (0 : ℂ)) U →
      R.natDegree ≤ Q.natDegree)
    (hfac : quadraticRelationFactor d ∣ R)
    (hext : ∀ Q : Polynomial (Polynomial ℂ),
      Set.EqOn (fun x => Q.eval₂ (Polynomial.evalRingHom (A x)) (B x)) (fun _ => (0 : ℂ))
        {x : α | x ∈ U ∧ B x ≠ (A x) ^ 2 + d} →
      Set.EqOn (fun x => Q.eval₂ (Polynomial.evalRingHom (A x)) (B x))
        (fun _ => (0 : ℂ)) U) :
    False := by
  obtain ⟨Q, hRQ, hQrelSub⟩ :=
    exists_lower_relation_on_nonparabola_of_factor_relation_eval₂ hfac hrel
  have hQ0 : Q ≠ 0 := by
    intro hzero
    rw [hRQ, hzero, mul_zero] at hR0
    exact hR0 rfl
  have hQrel :
      Set.EqOn (fun x => Q.eval₂ (Polynomial.evalRingHom (A x)) (B x))
        (fun _ => (0 : ℂ)) U :=
    hext Q hQrelSub
  have hle : R.natDegree ≤ Q.natDegree := hmin Q hQ0 hQrel
  have hlt : Q.natDegree < R.natDegree := quotient_natDegree_lt_of_quadratic_factor hR0 hRQ
  exact Nat.lt_irrefl Q.natDegree (lt_of_lt_of_le hlt hle)

/-- Direct no-relation criterion from shifted-parabola factor descent for arbitrary coordinate
functions `(A,B)`. -/
theorem no_relation_of_quadratic_factor_descent_eval₂
    {α : Type*} {U : Set α} {A B : α → ℂ} {d : ℂ}
    (hfac : ∀ R : Polynomial (Polynomial ℂ), R ≠ 0 →
      Set.EqOn (fun x => R.eval₂ (Polynomial.evalRingHom (A x)) (B x))
        (fun _ => (0 : ℂ)) U →
      quadraticRelationFactor d ∣ R)
    (hext : ∀ Q : Polynomial (Polynomial ℂ),
      Set.EqOn (fun x => Q.eval₂ (Polynomial.evalRingHom (A x)) (B x)) (fun _ => (0 : ℂ))
        {x : α | x ∈ U ∧ B x ≠ (A x) ^ 2 + d} →
      Set.EqOn (fun x => Q.eval₂ (Polynomial.evalRingHom (A x)) (B x))
        (fun _ => (0 : ℂ)) U) :
    ∀ R : Polynomial (Polynomial ℂ), R ≠ 0 →
      ¬ Set.EqOn (fun x => R.eval₂ (Polynomial.evalRingHom (A x)) (B x))
        (fun _ => (0 : ℂ)) U := by
  exact no_relation_of_minimal_counterexample_descent_eval₂
    (fun R hR0 hrel hmin =>
      false_of_minimal_relation_and_quadratic_factor_descent_eval₂
        hR0 hrel hmin (hfac R hR0 hrel) hext)

/-- No-transported-relation criterion where the remaining analytic input is exactly the scaled
vanishing of the shifted-parabola univariate remainder on the Böttcher real ray. -/
theorem no_relation_of_bottcher_scaled_quadratic_remainder_descent
    {U : Set ℂ} {T : ℂ → ℂ} {d c : ℂ}
    (hsmall : ∀ R : Polynomial (Polynomial ℂ), R ≠ 0 →
      Set.EqOn (fun w => R.eval₂ (Polynomial.evalRingHom w) (T w)) (fun _ => (0 : ℂ)) U →
      Tendsto
        (fun t : ℝ => ((t : ℂ)⁻¹) ^
          (R.eval (Polynomial.X ^ 2 + Polynomial.C d)).natDegree *
            (R.eval (Polynomial.X ^ 2 + Polynomial.C d)).eval (bottcherCoord c (t : ℂ))) atTop
        (𝓝 0))
    (hext : ∀ Q : Polynomial (Polynomial ℂ),
      Set.EqOn (fun w => Q.eval₂ (Polynomial.evalRingHom w) (T w)) (fun _ => (0 : ℂ))
        {w : ℂ | w ∈ U ∧ T w ≠ w ^ 2 + d} →
      Set.EqOn (fun w => Q.eval₂ (Polynomial.evalRingHom w) (T w)) (fun _ => (0 : ℂ)) U) :
    ∀ R : Polynomial (Polynomial ℂ), R ≠ 0 →
      ¬ Set.EqOn (fun w => R.eval₂ (Polynomial.evalRingHom w) (T w)) (fun _ => (0 : ℂ)) U := by
  refine no_relation_of_quadratic_factor_descent ?_ hext
  intro R hR0 hrel
  exact quadratic_factor_of_bottcher_scaled_quadratic_remainder_zero R d c
    (hsmall R hR0 hrel)

/-- No-relation criterion where the factor is supplied by infinitely many zeros on the asymptotic
parabola `Z=W²+d`. This is the form targeted by the transferred-quadratic asymptotic. -/
theorem no_relation_of_infinite_parabola_roots_and_quadratic_factor_descent
    {U : Set ℂ} {T : ℂ → ℂ} {d : ℂ}
    (hroots : ∀ R : Polynomial (Polynomial ℂ), R ≠ 0 →
      Set.EqOn (fun w => R.eval₂ (Polynomial.evalRingHom w) (T w)) (fun _ => (0 : ℂ)) U →
      Set.Infinite {x : ℂ | R.eval₂ (Polynomial.evalRingHom x) (x ^ 2 + d) = 0})
    (hext : ∀ Q : Polynomial (Polynomial ℂ),
      Set.EqOn (fun w => Q.eval₂ (Polynomial.evalRingHom w) (T w)) (fun _ => (0 : ℂ))
        {w : ℂ | w ∈ U ∧ T w ≠ w ^ 2 + d} →
      Set.EqOn (fun w => Q.eval₂ (Polynomial.evalRingHom w) (T w)) (fun _ => (0 : ℂ)) U) :
    ∀ R : Polynomial (Polynomial ℂ), R ≠ 0 →
      ¬ Set.EqOn (fun w => R.eval₂ (Polynomial.evalRingHom w) (T w)) (fun _ => (0 : ℂ)) U := by
  refine no_relation_of_quadratic_factor_descent ?_ hext
  intro R hR0 hrel
  rw [quadraticRelationFactor]
  exact quadratic_factor_of_eval₂_quadratic_eq_zero_on_infinite R d (hroots R hR0 hrel)

/-- Same no-relation criterion on a domain where `T` is pointwise not the asymptotic parabola. -/
theorem no_relation_of_infinite_parabola_roots_and_everywhere_nonparabola
    {U : Set ℂ} {T : ℂ → ℂ} {d : ℂ}
    (hroots : ∀ R : Polynomial (Polynomial ℂ), R ≠ 0 →
      Set.EqOn (fun w => R.eval₂ (Polynomial.evalRingHom w) (T w)) (fun _ => (0 : ℂ)) U →
      Set.Infinite {x : ℂ | R.eval₂ (Polynomial.evalRingHom x) (x ^ 2 + d) = 0})
    (hne : ∀ w ∈ U, T w ≠ w ^ 2 + d) :
  ∀ R : Polynomial (Polynomial ℂ), R ≠ 0 →
      ¬ Set.EqOn (fun w => R.eval₂ (Polynomial.evalRingHom w) (T w)) (fun _ => (0 : ℂ)) U := by
  refine no_relation_of_infinite_parabola_roots_and_quadratic_factor_descent hroots ?_
  intro Q hQ w hw
  exact hQ ⟨hw, hne w hw⟩

/-- Remainder decomposition after substituting the parabola `Z=W²+d`:
`R(W,Z) = R(W,W²+d) + (Z-(W²+d)) A(W,Z)`. -/
lemma exists_quadratic_substitution_remainder (R : Polynomial (Polynomial ℂ)) (d : ℂ) :
    ∃ A : Polynomial (Polynomial ℂ),
      R = Polynomial.C (R.eval (Polynomial.X ^ 2 + Polynomial.C d)) +
        quadraticRelationFactor d * A := by
  have hdvd :
      quadraticRelationFactor d ∣ R - Polynomial.C (R.eval (Polynomial.X ^ 2 + Polynomial.C d)) := by
    rw [quadraticRelationFactor]
    exact Polynomial.X_sub_C_dvd_sub_C_eval
  rcases hdvd with ⟨A, hA⟩
  refine ⟨A, ?_⟩
  rw [← hA]
  abel

lemma eval₂_quadratic_substitution_remainder (R A : Polynomial (Polynomial ℂ)) (d w z : ℂ)
    (hA : R = Polynomial.C (R.eval (Polynomial.X ^ 2 + Polynomial.C d)) +
        quadraticRelationFactor d * A) :
    R.eval₂ (Polynomial.evalRingHom w) z =
      (R.eval (Polynomial.X ^ 2 + Polynomial.C d)).eval w +
        (z - (w ^ 2 + d)) * A.eval₂ (Polynomial.evalRingHom w) z := by
  conv_lhs => rw [hA]
  rw [Polynomial.eval₂_add, Polynomial.eval₂_mul, eval_quadraticRelationFactor]
  congr 1
  simp [Polynomial.eval₂_C]

/-- Exact-division analytic handoff.  If `R` is exactly decomposed as
`R(W,Z)=R(W,W²+d)+(Z-W²-d)Q(W,Z)`, an eventual transported relation plus a scaled estimate for the
defect times `Q` gives the exact shifted-parabola factor. -/
theorem quadratic_factor_of_bottcher_relation_and_scaled_defect_quotient_zero
    {c c₂ d : ℂ} (R Q : Polynomial (Polynomial ℂ))
    (hdecomp : R = Polynomial.C (R.eval (Polynomial.X ^ 2 + Polynomial.C d)) +
        quadraticRelationFactor d * Q)
    (hrel : ∀ᶠ t : ℝ in atTop,
      R.eval₂ (Polynomial.evalRingHom (bottcherCoord c (t : ℂ)))
        (bottcherCoord c (quadratic c₂ (t : ℂ))) = 0)
    (hdefsmall : Tendsto
      (fun t : ℝ => ((t : ℂ)⁻¹) ^
        (R.eval (Polynomial.X ^ 2 + Polynomial.C d)).natDegree *
          ((bottcherCoord c (quadratic c₂ (t : ℂ)) -
              ((bottcherCoord c (t : ℂ)) ^ 2 + d)) *
            Q.eval₂ (Polynomial.evalRingHom (bottcherCoord c (t : ℂ)))
              (bottcherCoord c (quadratic c₂ (t : ℂ))))) atTop (𝓝 0)) :
    quadraticRelationFactor d ∣ R := by
  refine quadratic_factor_of_bottcher_scaled_quadratic_remainder_zero R d c ?_
  have hneg : Tendsto
      (fun t : ℝ => -(((t : ℂ)⁻¹) ^
        (R.eval (Polynomial.X ^ 2 + Polynomial.C d)).natDegree *
          ((bottcherCoord c (quadratic c₂ (t : ℂ)) -
              ((bottcherCoord c (t : ℂ)) ^ 2 + d)) *
            Q.eval₂ (Polynomial.evalRingHom (bottcherCoord c (t : ℂ)))
              (bottcherCoord c (quadratic c₂ (t : ℂ)))))) atTop (𝓝 0) := by
    simpa using hdefsmall.neg
  refine hneg.congr' ?_
  filter_upwards [hrel] with t ht
  have heval := eval₂_quadratic_substitution_remainder R Q d
    (bottcherCoord c (t : ℂ)) (bottcherCoord c (quadratic c₂ (t : ℂ))) hdecomp
  have hrem :
      (R.eval (Polynomial.X ^ 2 + Polynomial.C d)).eval (bottcherCoord c (t : ℂ)) =
        -((bottcherCoord c (quadratic c₂ (t : ℂ)) -
            ((bottcherCoord c (t : ℂ)) ^ 2 + d)) *
          Q.eval₂ (Polynomial.evalRingHom (bottcherCoord c (t : ℂ)))
            (bottcherCoord c (quadratic c₂ (t : ℂ)))) := by
    rw [ht] at heval
    have hadd :
        (R.eval (Polynomial.X ^ 2 + Polynomial.C d)).eval (bottcherCoord c (t : ℂ)) +
          (bottcherCoord c (quadratic c₂ (t : ℂ)) -
              ((bottcherCoord c (t : ℂ)) ^ 2 + d)) *
            Q.eval₂ (Polynomial.evalRingHom (bottcherCoord c (t : ℂ)))
              (bottcherCoord c (quadratic c₂ (t : ℂ))) = 0 := by
      simpa using heval.symm
    calc
      (R.eval (Polynomial.X ^ 2 + Polynomial.C d)).eval (bottcherCoord c (t : ℂ))
          = (R.eval (Polynomial.X ^ 2 + Polynomial.C d)).eval (bottcherCoord c (t : ℂ)) +
              (bottcherCoord c (quadratic c₂ (t : ℂ)) -
                  ((bottcherCoord c (t : ℂ)) ^ 2 + d)) *
                Q.eval₂ (Polynomial.evalRingHom (bottcherCoord c (t : ℂ)))
                  (bottcherCoord c (quadratic c₂ (t : ℂ))) -
              (bottcherCoord c (quadratic c₂ (t : ℂ)) -
                  ((bottcherCoord c (t : ℂ)) ^ 2 + d)) *
                Q.eval₂ (Polynomial.evalRingHom (bottcherCoord c (t : ℂ)))
                  (bottcherCoord c (quadratic c₂ (t : ℂ))) := by ring
      _ = -((bottcherCoord c (quadratic c₂ (t : ℂ)) -
              ((bottcherCoord c (t : ℂ)) ^ 2 + d)) *
            Q.eval₂ (Polynomial.evalRingHom (bottcherCoord c (t : ℂ)))
              (bottcherCoord c (quadratic c₂ (t : ℂ)))) := by rw [hadd]; ring
  rw [hrem]
  ring

/-- **Pointwise resultant obstruction from a semiconjugacy.**
If `q(x,H x)=0` on `V` and `H(T x)=H x^(2 : ℕ)` on `U`, then for each `x ∈ U` the two one-variable
polynomials `q(x,Y)` and `q(T x,Y^(2 : ℕ))` have the common root `H x`. Therefore their resultant vanishes.

The extra nonzero-pair hypothesis is exactly the harmless algebraic side condition needed by
`resultant_eq_zero_iff`; it is separated so later work can prove it from the particular nonzero
relation `q`. -/
theorem eqOn_resultant_transition_relation_of_eqOn_relation_and_conj
    {U V : Set ℂ} {H T : ℂ → ℂ} (q : Polynomial (Polynomial ℂ))
    (hUsub : U ⊆ V) (hTmaps : Set.MapsTo T U V)
    (hrel : Set.EqOn (fun x => q.eval₂ (Polynomial.evalRingHom x) (H x)) (fun _ => (0 : ℂ)) V)
    (hconj : ∀ x ∈ U, H (T x) = (H x) ^ 2)
    (hnz : ∀ x ∈ U,
      q.map (Polynomial.evalRingHom x) ≠ 0 ∨
        (q.map (Polynomial.evalRingHom (T x))).comp (Polynomial.X ^ 2) ≠ 0) :
    Set.EqOn (fun x => Polynomial.resultant
      (q.map (Polynomial.evalRingHom x))
      ((q.map (Polynomial.evalRingHom (T x))).comp (Polynomial.X ^ 2)))
      (fun _ => (0 : ℂ)) U := by
  intro x hx
  have hq₁ : (q.map (Polynomial.evalRingHom x)).eval (H x) = 0 := by
    simpa [Polynomial.eval₂_eq_eval_map] using hrel (hUsub hx)
  have hbase : q.eval₂ (Polynomial.evalRingHom (T x)) ((H x) ^ 2) = 0 :=
    eqOn_transition_relation_of_eqOn_relation_and_conj q hTmaps hrel hconj hx
  have hq₂ :
      ((q.map (Polynomial.evalRingHom (T x))).comp (Polynomial.X ^ 2)).eval (H x) = 0 := by
    simpa [Polynomial.eval_comp, Polynomial.eval₂_eq_eval_map] using hbase
  exact resultant_eq_zero_of_common_root hq₁ hq₂ (hnz x hx)

/-- **Universal resultant relation from a semiconjugacy.**
The bivariate polynomial `transitionResultant q = Res_Y(q(W,Y), q(Z,Y²))` vanishes on `(x,T x)` when
`q(x,H x)=0` and `H(T x)=H x²`. The proof uses fixed-size resultants, so specialization of leading
coefficients is harmless. -/
theorem eqOn_transitionResultant_of_eqOn_relation_and_conj
    {U V : Set ℂ} {H T : ℂ → ℂ} (q : Polynomial (Polynomial ℂ))
    (hUsub : U ⊆ V) (hTmaps : Set.MapsTo T U V)
    (hrel : Set.EqOn (fun x => q.eval₂ (Polynomial.evalRingHom x) (H x)) (fun _ => (0 : ℂ)) V)
    (hconj : ∀ x ∈ U, H (T x) = (H x) ^ 2)
    (hnz : ∀ x ∈ U,
      q.map (Polynomial.evalRingHom x) ≠ 0 ∨
        (q.map (Polynomial.evalRingHom (T x))).comp (Polynomial.X ^ 2) ≠ 0) :
    Set.EqOn (fun x => (transitionResultant q).eval₂ (Polynomial.evalRingHom x) (T x))
      (fun _ => (0 : ℂ)) U := by
  intro x hx
  change (transitionResultant q).eval₂ (Polynomial.evalRingHom x) (T x) = 0
  rw [eval_transitionResultant]
  have hq₁ : (q.map (Polynomial.evalRingHom x)).eval (H x) = 0 := by
    simpa [Polynomial.eval₂_eq_eval_map] using hrel (hUsub hx)
  have hbase : q.eval₂ (Polynomial.evalRingHom (T x)) ((H x) ^ 2) = 0 :=
    eqOn_transition_relation_of_eqOn_relation_and_conj q hTmaps hrel hconj hx
  have hq₂ : ((q.map (Polynomial.evalRingHom (T x))).comp (Polynomial.X ^ 2)).eval (H x) = 0 := by
    simpa [Polynomial.eval_comp, Polynomial.eval₂_eq_eval_map] using hbase
  have hm : (q.map (Polynomial.evalRingHom x)).natDegree ≤ (transitionResultantLeft q).natDegree := by
    rw [← map_transitionResultantLeft_eval q x (T x)]
    exact Polynomial.natDegree_map_le
  have hn : ((q.map (Polynomial.evalRingHom (T x))).comp (Polynomial.X ^ 2)).natDegree ≤
      (transitionResultantRight q).natDegree := by
    rw [← map_transitionResultantRight_eval q x (T x)]
    exact Polynomial.natDegree_map_le
  exact resultant_eq_zero_of_common_root_of_natDegree_le hq₁ hq₂ (hnz x hx) hm hn

/-- **Eliminated relation for the transported map.**
Suppose `q(x,H x)=0`, `H(T x)=H x^(2 : ℕ)`, and `R(W,Z)` is an eliminant for the pair of equations
`q(W,Y)=0`, `q(Z,Y^(2 : ℕ))=0`. Then `R(x,T x)=0` on `U`. This isolates the next algebraic task: construct a
nonzero `R` by resultants/elimination from a nonzero relation `q` for `H`. -/
theorem eqOn_eliminated_transition_relation_of_relation_and_conj
    {U V : Set ℂ} {H T : ℂ → ℂ} (q R : Polynomial (Polynomial ℂ))
    (hUsub : U ⊆ V) (hTmaps : Set.MapsTo T U V)
    (hrel : Set.EqOn (fun x => q.eval₂ (Polynomial.evalRingHom x) (H x)) (fun _ => (0 : ℂ)) V)
    (hconj : ∀ x ∈ U, H (T x) = (H x) ^ 2)
    (helim : ∀ x y z : ℂ,
      q.eval₂ (Polynomial.evalRingHom x) y = 0 →
      q.eval₂ (Polynomial.evalRingHom z) (y ^ 2) = 0 →
      R.eval₂ (Polynomial.evalRingHom x) z = 0) :
    Set.EqOn (fun x => R.eval₂ (Polynomial.evalRingHom x) (T x)) (fun _ => (0 : ℂ)) U := by
  intro x hx
  have hq₁ : q.eval₂ (Polynomial.evalRingHom x) (H x) = 0 := hrel (hUsub hx)
  have hq₂ : q.eval₂ (Polynomial.evalRingHom (T x)) ((H x) ^ 2) = 0 :=
    eqOn_transition_relation_of_eqOn_relation_and_conj q hTmaps hrel hconj hx
  exact helim x (H x) (T x) hq₁ hq₂

end Bottcher

namespace Bottcher
open Polynomial Filter

/-- **No relation for `H` from eliminants and no relation for the transported map.**
This is the exact algebraic reduction suggested by the semiconjugacy route: an algebraic relation for
`H` plus elimination produces a nonzero algebraic relation for `T`; therefore a no-relation theorem for
`T` rules out the original relation for `H`. -/
theorem no_transition_relation_of_eliminants_and_no_transported_relation
    {U V : Set ℂ} {H T : ℂ → ℂ}
    (hUsub : U ⊆ V) (hTmaps : Set.MapsTo T U V)
    (hconj : ∀ x ∈ U, H (T x) = (H x) ^ 2)
    (helims : ∀ q : Polynomial (Polynomial ℂ), q ≠ 0 →
      ∃ R : Polynomial (Polynomial ℂ), R ≠ 0 ∧
        ∀ x y z : ℂ,
          q.eval₂ (Polynomial.evalRingHom x) y = 0 →
          q.eval₂ (Polynomial.evalRingHom z) (y ^ 2) = 0 →
          R.eval₂ (Polynomial.evalRingHom x) z = 0)
    (hnoT : ∀ R : Polynomial (Polynomial ℂ), R ≠ 0 →
      ¬ Set.EqOn (fun x => R.eval₂ (Polynomial.evalRingHom x) (T x)) (fun _ => (0 : ℂ)) U) :
    ∀ q : Polynomial (Polynomial ℂ), q ≠ 0 →
      ¬ Set.EqOn (fun x => q.eval₂ (Polynomial.evalRingHom x) (H x)) (fun _ => (0 : ℂ)) V := by
  intro q hq hrel
  obtain ⟨R, hR0, hR⟩ := helims q hq
  exact hnoT R hR0
    (eqOn_eliminated_transition_relation_of_relation_and_conj q R hUsub hTmaps hrel hconj hR)

end Bottcher

namespace Bottcher
open Polynomial Filter

/-- **Pull a transported-map relation back to the original far `z` coordinate.**
For `T(w)=φ_{c₁}((ψ₁ w)^(2 : ℕ)+c₂)`, a relation `R(w,T(w))=0` on a value annulus gives the relation
`R(φ_{c₁}(z), φ_{c₁}(z²+c₂))=0` at every far point whose `φ_{c₁}` value lies in that annulus. -/
theorem eqOn_transported_relation_pullback_to_z
    {c₁ c₂ : ℂ} {ψ₁ : ℂ → ℂ} {Rfar R' : ℝ} (R : Polynomial (Polynomial ℂ))
    (hψleft : ∀ z, Rfar < ‖z‖ → ψ₁ (bottcherCoord c₁ z) = z)
    (hrel : Set.EqOn
      (fun w => R.eval₂ (Polynomial.evalRingHom w)
        (bottcherCoord c₁ (quadratic c₂ (ψ₁ w)))) (fun _ => (0 : ℂ))
      {w : ℂ | R' < ‖w‖}) :
    Set.EqOn
      (fun z => R.eval₂ (Polynomial.evalRingHom (bottcherCoord c₁ z))
        (bottcherCoord c₁ (quadratic c₂ z))) (fun _ => (0 : ℂ))
      {z : ℂ | Rfar < ‖z‖ ∧ R' < ‖bottcherCoord c₁ z‖} := by
  intro z hz
  have h := hrel (show bottcherCoord c₁ z ∈ {w : ℂ | R' < ‖w‖} from hz.2)
  simpa [hψleft z hz.1] using h

end Bottcher

namespace Bottcher
open Polynomial Filter

/-- **From a transition relation to a pulled-back transported relation.**
A relation for `H(w)=φ₂(ψ₁(w))`, together with an eliminant for `q(W,Y), q(Z,Y²)` and the exact
semiconjugacy of the transported map, yields a concrete far-field relation
`R(φ₁(z), φ₁(z²+c₂))=0`. This is the reduction target for the remaining rigidity/asymptotic step. -/
theorem eqOn_transported_z_relation_of_transition_relation_and_eliminant
    {c₁ c₂ : ℂ} {ψ₁ : ℂ → ℂ} {Rfar R' : ℝ}
    (q R : Polynomial (Polynomial ℂ))
    (hψleft : ∀ z, Rfar < ‖z‖ → ψ₁ (bottcherCoord c₁ z) = z)
    (hTmaps : Set.MapsTo
      (fun w => bottcherCoord c₁ (quadratic c₂ (ψ₁ w)))
      {w : ℂ | R' < ‖w‖} {w : ℂ | R' < ‖w‖})
    (hconj : ∀ w ∈ {w : ℂ | R' < ‖w‖},
      bottcherCoord c₂ (ψ₁ (bottcherCoord c₁ (quadratic c₂ (ψ₁ w)))) =
        (bottcherCoord c₂ (ψ₁ w)) ^ 2)
    (hrel : Set.EqOn
      (fun w => q.eval₂ (Polynomial.evalRingHom w) (bottcherCoord c₂ (ψ₁ w)))
      (fun _ => (0 : ℂ)) {w : ℂ | R' < ‖w‖})
    (helim : ∀ x y z : ℂ,
      q.eval₂ (Polynomial.evalRingHom x) y = 0 →
      q.eval₂ (Polynomial.evalRingHom z) (y ^ 2) = 0 →
      R.eval₂ (Polynomial.evalRingHom x) z = 0) :
    Set.EqOn
      (fun z => R.eval₂ (Polynomial.evalRingHom (bottcherCoord c₁ z))
        (bottcherCoord c₁ (quadratic c₂ z))) (fun _ => (0 : ℂ))
      {z : ℂ | Rfar < ‖z‖ ∧ R' < ‖bottcherCoord c₁ z‖} := by
  have hTR : Set.EqOn
      (fun w => R.eval₂ (Polynomial.evalRingHom w)
        (bottcherCoord c₁ (quadratic c₂ (ψ₁ w)))) (fun _ => (0 : ℂ))
      {w : ℂ | R' < ‖w‖} := by
    exact eqOn_eliminated_transition_relation_of_relation_and_conj
      (U := {w : ℂ | R' < ‖w‖}) (V := {w : ℂ | R' < ‖w‖})
      (H := fun w => bottcherCoord c₂ (ψ₁ w))
      (T := fun w => bottcherCoord c₁ (quadratic c₂ (ψ₁ w)))
      q R (fun _ h => h) hTmaps hrel hconj helim
  exact eqOn_transported_relation_pullback_to_z
    (c₁ := c₁) (c₂ := c₂) (ψ₁ := ψ₁) (Rfar := Rfar) (R' := R') R hψleft hTR

end Bottcher

namespace Bottcher
open Polynomial Filter

/-- **Pulled-back transported relation gives a weighted coefficient obstruction.**
A relation `R(φ₁(z), φ₁(z²+c₂))=0` on the far pullback domain restricts to the positive real ray;
the Böttcher real-ray Laurent extraction then forces the top weighted coefficient slice of `R` to vanish. -/
theorem weighted_top_zero_of_transported_pullback_relation
    {c₁ c₂ : ℂ} {Rfar R' : ℝ} (R : Polynomial (Polynomial ℂ)) {W : ℕ}
    (hweight : ∀ j : Fin (R.natDegree + 1),
      ∀ i : Fin ((R.coeff (j : ℕ)).natDegree + 1), (i : ℕ) + 2 * (j : ℕ) ≤ W)
    (hrel : Set.EqOn
      (fun z => R.eval₂ (Polynomial.evalRingHom (bottcherCoord c₁ z))
        (bottcherCoord c₁ (quadratic c₂ z))) (fun _ => (0 : ℂ))
      {z : ℂ | Rfar < ‖z‖ ∧ R' < ‖bottcherCoord c₁ z‖}) :
    ∑ s : Sigma (fun j : Fin (R.natDegree + 1) => Fin ((R.coeff (j : ℕ)).natDegree + 1)),
      (if (s.2 : ℕ) + 2 * (s.1 : ℕ) = W then
        (R.coeff (s.1 : ℕ)).coeff (s.2 : ℕ) else 0) = 0 := by
  refine bottcher_weighted_top_sum_zero_of_polynomial_eventual_relation c₁ c₂ R hweight ?_
  filter_upwards [eventually_real_mem_bottcher_pullback_far c₁ Rfar R'] with t ht
  exact hrel ht

end Bottcher

namespace Bottcher
open Polynomial Filter

/-- **Transition relation plus eliminant gives the weighted obstruction.**
This composes the semiconjugacy/elimination reduction with the real-ray Laurent extraction: any algebraic
relation for the far-value transition `H(w)=φ₂(ψ₁ w)` produces an eliminant `R`, and the pulled-back
relation forces the top weighted coefficient slice of `R` to vanish. -/
theorem weighted_top_zero_of_transition_relation_and_eliminant
    {c₁ c₂ : ℂ} {ψ₁ : ℂ → ℂ} {Rfar R' : ℝ}
    (q R : Polynomial (Polynomial ℂ)) {W : ℕ}
    (hweight : ∀ j : Fin (R.natDegree + 1),
      ∀ i : Fin ((R.coeff (j : ℕ)).natDegree + 1), (i : ℕ) + 2 * (j : ℕ) ≤ W)
    (hψleft : ∀ z, Rfar < ‖z‖ → ψ₁ (bottcherCoord c₁ z) = z)
    (hTmaps : Set.MapsTo
      (fun w => bottcherCoord c₁ (quadratic c₂ (ψ₁ w)))
      {w : ℂ | R' < ‖w‖} {w : ℂ | R' < ‖w‖})
    (hconj : ∀ w ∈ {w : ℂ | R' < ‖w‖},
      bottcherCoord c₂ (ψ₁ (bottcherCoord c₁ (quadratic c₂ (ψ₁ w)))) =
        (bottcherCoord c₂ (ψ₁ w)) ^ 2)
    (hrel : Set.EqOn
      (fun w => q.eval₂ (Polynomial.evalRingHom w) (bottcherCoord c₂ (ψ₁ w)))
      (fun _ => (0 : ℂ)) {w : ℂ | R' < ‖w‖})
    (helim : ∀ x y z : ℂ,
      q.eval₂ (Polynomial.evalRingHom x) y = 0 →
      q.eval₂ (Polynomial.evalRingHom z) (y ^ 2) = 0 →
      R.eval₂ (Polynomial.evalRingHom x) z = 0) :
    ∑ s : Sigma (fun j : Fin (R.natDegree + 1) => Fin ((R.coeff (j : ℕ)).natDegree + 1)),
      (if (s.2 : ℕ) + 2 * (s.1 : ℕ) = W then
        (R.coeff (s.1 : ℕ)).coeff (s.2 : ℕ) else 0) = 0 := by
  exact weighted_top_zero_of_transported_pullback_relation (c₁ := c₁) (c₂ := c₂)
    (Rfar := Rfar) (R' := R') R hweight
    (eqOn_transported_z_relation_of_transition_relation_and_eliminant
      (c₁ := c₁) (c₂ := c₂) (ψ₁ := ψ₁) (Rfar := Rfar) (R' := R')
      q R hψleft hTmaps hconj hrel helim)

end Bottcher

namespace Bottcher
open Polynomial Filter

/-- The weighted-homogeneous polynomial with monomials `a_k W^{I_k} Z^{J_k}`. -/
noncomputable def weightedHomogeneousPoly {ι : Type*} [Fintype ι]
    (a : ι → ℂ) (I J : ι → ℕ) : Polynomial (Polynomial ℂ) :=
  ∑ k : ι, Polynomial.C (Polynomial.C (a k) * (Polynomial.X : Polynomial ℂ) ^ I k) *
    (Polynomial.X : Polynomial (Polynomial ℂ)) ^ J k

/-- A weighted-homogeneous polynomial of total weight `W` whose coefficients sum to zero is divisible by
`Z-W²`. Algebraically this is `H(1,1)=0` upgraded to the top-parabola factor for a weighted-homogeneous
slice. -/
lemma quadratic_factor_of_weightedHomogeneous_sum_zero {ι : Type*} [Fintype ι]
    {a : ι → ℂ} {I J : ι → ℕ} {W : ℕ}
    (hweight : ∀ k : ι, I k + 2 * J k = W)
    (hsum : ∑ k : ι, a k = 0) :
    quadraticRelationFactor 0 ∣ weightedHomogeneousPoly a I J := by
  apply quadratic_factor_of_quadratic_substitution_zero
  rw [weightedHomogeneousPoly]
  simp only [Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow,
    Polynomial.eval_X]
  calc
    ∑ x : ι, (Polynomial.C (a x) * (Polynomial.X : Polynomial ℂ) ^ I x) *
        ((Polynomial.X : Polynomial ℂ) ^ 2 + Polynomial.C 0) ^ J x
        = ∑ x : ι, Polynomial.C (a x) * (Polynomial.X : Polynomial ℂ) ^ W := by
          refine Finset.sum_congr rfl ?_
          intro k _
          simp only [Polynomial.C_0, add_zero]
          rw [← pow_mul, mul_assoc, ← pow_add]
          rw [hweight k]
    _ = Polynomial.C (∑ x : ι, a x) * (Polynomial.X : Polynomial ℂ) ^ W := by
          rw [← Finset.sum_mul]
          simp
    _ = 0 := by rw [hsum]; simp

end Bottcher

namespace Bottcher
open Polynomial Filter

/-- If all monomials have weight at most `W` and the top-weight coefficient sum vanishes, then the
weighted-homogeneous polynomial formed from only the top-weight terms is divisible by `Z-W²`. -/
lemma quadratic_factor_of_weightedHomogeneous_top_sum_zero {ι : Type*} [Fintype ι]
    {a : ι → ℂ} {I J : ι → ℕ} {W : ℕ}
    (hweight : ∀ k : ι, I k + 2 * J k ≤ W)
    (hsum : ∑ k : ι, (if I k + 2 * J k = W then a k else 0) = 0) :
    quadraticRelationFactor 0 ∣
      weightedHomogeneousPoly (fun k => if I k + 2 * J k = W then a k else 0) I J := by
  apply quadratic_factor_of_quadratic_substitution_zero
  rw [weightedHomogeneousPoly]
  simp only [Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow,
    Polynomial.eval_X]
  calc
    ∑ x : ι, (Polynomial.C (if I x + 2 * J x = W then a x else 0) *
        (Polynomial.X : Polynomial ℂ) ^ I x) *
        ((Polynomial.X : Polynomial ℂ) ^ 2 + Polynomial.C 0) ^ J x
        = ∑ x : ι, Polynomial.C (if I x + 2 * J x = W then a x else 0) *
            (Polynomial.X : Polynomial ℂ) ^ W := by
          refine Finset.sum_congr rfl ?_
          intro k _
          by_cases hk : I k + 2 * J k = W
          · simp only [hk, ↓reduceIte, Polynomial.C_0, add_zero]
            rw [← pow_mul, mul_assoc, ← pow_add, hk]
          · have hlt : I k + 2 * J k < W := Nat.lt_of_le_of_ne (hweight k) hk
            simp [hk]
    _ = Polynomial.C (∑ x : ι, (if I x + 2 * J x = W then a x else 0)) *
          (Polynomial.X : Polynomial ℂ) ^ W := by
          rw [← Finset.sum_mul]
          simp
    _ = 0 := by rw [hsum]; simp

end Bottcher

namespace Bottcher
open Polynomial Filter

/-- The weighted-degree-`W` top slice of a bivariate polynomial `R(W,Z)`, using weights
`wt(W)=1`, `wt(Z)=2`. -/
noncomputable def weightedTopSlice (R : Polynomial (Polynomial ℂ)) (W : ℕ) :
    Polynomial (Polynomial ℂ) :=
  weightedHomogeneousPoly
    (ι := Sigma (fun j : Fin (R.natDegree + 1) => Fin ((R.coeff (j : ℕ)).natDegree + 1)))
    (fun s => if (s.2 : ℕ) + 2 * (s.1 : ℕ) = W then
      (R.coeff (s.1 : ℕ)).coeff (s.2 : ℕ) else 0)
    (fun s => (s.2 : ℕ)) (fun s => (s.1 : ℕ))

/-- A transported pullback relation forces the weighted top slice of `R` to have the top parabola
factor `Z-W²`. -/
theorem quadratic_factor_weightedTopSlice_of_transported_pullback_relation
    {c₁ c₂ : ℂ} {Rfar R' : ℝ} (R : Polynomial (Polynomial ℂ)) {W : ℕ}
    (hweight : ∀ j : Fin (R.natDegree + 1),
      ∀ i : Fin ((R.coeff (j : ℕ)).natDegree + 1), (i : ℕ) + 2 * (j : ℕ) ≤ W)
    (hrel : Set.EqOn
      (fun z => R.eval₂ (Polynomial.evalRingHom (bottcherCoord c₁ z))
        (bottcherCoord c₁ (quadratic c₂ z))) (fun _ => (0 : ℂ))
      {z : ℂ | Rfar < ‖z‖ ∧ R' < ‖bottcherCoord c₁ z‖}) :
    quadraticRelationFactor 0 ∣ weightedTopSlice R W := by
  dsimp [weightedTopSlice]
  apply quadratic_factor_of_weightedHomogeneous_top_sum_zero
  · intro s
    exact hweight s.1 s.2
  · exact weighted_top_zero_of_transported_pullback_relation (c₁ := c₁) (c₂ := c₂)
      (Rfar := Rfar) (R' := R') R hweight hrel

/-- A transition relation plus eliminant forces the eliminant's weighted top slice to have the top
parabola factor `Z-W²`. -/
theorem quadratic_factor_weightedTopSlice_of_transition_relation_and_eliminant
    {c₁ c₂ : ℂ} {ψ₁ : ℂ → ℂ} {Rfar R' : ℝ}
    (q R : Polynomial (Polynomial ℂ)) {W : ℕ}
    (hweight : ∀ j : Fin (R.natDegree + 1),
      ∀ i : Fin ((R.coeff (j : ℕ)).natDegree + 1), (i : ℕ) + 2 * (j : ℕ) ≤ W)
    (hψleft : ∀ z, Rfar < ‖z‖ → ψ₁ (bottcherCoord c₁ z) = z)
    (hTmaps : Set.MapsTo
      (fun w => bottcherCoord c₁ (quadratic c₂ (ψ₁ w)))
      {w : ℂ | R' < ‖w‖} {w : ℂ | R' < ‖w‖})
    (hconj : ∀ w ∈ {w : ℂ | R' < ‖w‖},
      bottcherCoord c₂ (ψ₁ (bottcherCoord c₁ (quadratic c₂ (ψ₁ w)))) =
        (bottcherCoord c₂ (ψ₁ w)) ^ 2)
    (hrel : Set.EqOn
      (fun w => q.eval₂ (Polynomial.evalRingHom w) (bottcherCoord c₂ (ψ₁ w)))
      (fun _ => (0 : ℂ)) {w : ℂ | R' < ‖w‖})
    (helim : ∀ x y z : ℂ,
      q.eval₂ (Polynomial.evalRingHom x) y = 0 →
      q.eval₂ (Polynomial.evalRingHom z) (y ^ 2) = 0 →
      R.eval₂ (Polynomial.evalRingHom x) z = 0) :
    quadraticRelationFactor 0 ∣ weightedTopSlice R W := by
  dsimp [weightedTopSlice]
  apply quadratic_factor_of_weightedHomogeneous_top_sum_zero
  · intro s
    exact hweight s.1 s.2
  · exact weighted_top_zero_of_transition_relation_and_eliminant (c₁ := c₁) (c₂ := c₂)
      (ψ₁ := ψ₁) (Rfar := Rfar) (R' := R') q R hweight hψleft hTmaps hconj hrel helim

end Bottcher

namespace Bottcher
open Polynomial Filter

/-- Pulled-back transported relation with a tail whose real-ray weighted scaling tends to zero. -/
theorem weighted_top_zero_of_transported_pullback_relation_with_scaled_tail
    {c₁ c₂ : ℂ} {Rfar R' : ℝ} (R : Polynomial (Polynomial ℂ)) {W : ℕ} {Tail : ℂ → ℂ}
    (hweight : ∀ j : Fin (R.natDegree + 1),
      ∀ i : Fin ((R.coeff (j : ℕ)).natDegree + 1), (i : ℕ) + 2 * (j : ℕ) ≤ W)
    (hTail : Tendsto (fun t : ℝ => ((t : ℂ)⁻¹) ^ W * Tail (t : ℂ)) atTop (𝓝 0))
    (hrel : Set.EqOn
      (fun z => R.eval₂ (Polynomial.evalRingHom (bottcherCoord c₁ z))
        (bottcherCoord c₁ (quadratic c₂ z)) + Tail z) (fun _ => (0 : ℂ))
      {z : ℂ | Rfar < ‖z‖ ∧ R' < ‖bottcherCoord c₁ z‖}) :
    ∑ s : Sigma (fun j : Fin (R.natDegree + 1) => Fin ((R.coeff (j : ℕ)).natDegree + 1)),
      (if (s.2 : ℕ) + 2 * (s.1 : ℕ) = W then
        (R.coeff (s.1 : ℕ)).coeff (s.2 : ℕ) else 0) = 0 := by
  refine bottcher_weighted_top_sum_zero_of_polynomial_eventual_relation_with_scaled_tail
    c₁ c₂ R hweight hTail ?_
  filter_upwards [eventually_real_mem_bottcher_pullback_far c₁ Rfar R'] with t ht
  exact hrel ht

/-- A transported pullback relation with a vanishing scaled tail still forces the weighted top slice of
`R` to have the top parabola factor `Z-W²`. -/
theorem quadratic_factor_weightedTopSlice_of_transported_pullback_relation_with_scaled_tail
    {c₁ c₂ : ℂ} {Rfar R' : ℝ} (R : Polynomial (Polynomial ℂ)) {W : ℕ} {Tail : ℂ → ℂ}
    (hweight : ∀ j : Fin (R.natDegree + 1),
      ∀ i : Fin ((R.coeff (j : ℕ)).natDegree + 1), (i : ℕ) + 2 * (j : ℕ) ≤ W)
    (hTail : Tendsto (fun t : ℝ => ((t : ℂ)⁻¹) ^ W * Tail (t : ℂ)) atTop (𝓝 0))
    (hrel : Set.EqOn
      (fun z => R.eval₂ (Polynomial.evalRingHom (bottcherCoord c₁ z))
        (bottcherCoord c₁ (quadratic c₂ z)) + Tail z) (fun _ => (0 : ℂ))
      {z : ℂ | Rfar < ‖z‖ ∧ R' < ‖bottcherCoord c₁ z‖}) :
    quadraticRelationFactor 0 ∣ weightedTopSlice R W := by
  dsimp [weightedTopSlice]
  apply quadratic_factor_of_weightedHomogeneous_top_sum_zero
  · intro s
    exact hweight s.1 s.2
  · exact weighted_top_zero_of_transported_pullback_relation_with_scaled_tail
      (c₁ := c₁) (c₂ := c₂) (Rfar := Rfar) (R' := R') R hweight hTail hrel

end Bottcher

namespace Bottcher
open Polynomial Filter

/-- Subtracting a shifted parabola factor converts an exact relation for `R` into a relation for the
remainder with the explicit defect tail. -/
lemma eqOn_remainder_tail_of_shifted_factor
    {U : Set ℂ} {A B : ℂ → ℂ} {R R₁ Q : Polynomial (Polynomial ℂ)} {d : ℂ}
    (hdecomp : R = R₁ + quadraticRelationFactor d * Q)
    (hrel : Set.EqOn (fun z => R.eval₂ (Polynomial.evalRingHom (A z)) (B z)) (fun _ => (0 : ℂ)) U) :
    Set.EqOn
      (fun z => R₁.eval₂ (Polynomial.evalRingHom (A z)) (B z) +
        (B z - (A z ^ 2 + d)) * Q.eval₂ (Polynomial.evalRingHom (A z)) (B z))
      (fun _ => (0 : ℂ)) U := by
  intro z hz
  have h := hrel hz
  change R.eval₂ (Polynomial.evalRingHom (A z)) (B z) = 0 at h
  rw [hdecomp, Polynomial.eval₂_add, Polynomial.eval₂_mul, eval_quadraticRelationFactor] at h
  change R₁.eval₂ (Polynomial.evalRingHom (A z)) (B z) +
      (B z - (A z ^ 2 + d)) * Q.eval₂ (Polynomial.evalRingHom (A z)) (B z) = 0
  exact h

/-- The shifted-factor subtraction specialized to the pulled-back transported Böttcher relation. -/
lemma eqOn_transported_remainder_tail_of_shifted_factor
    {c₁ c₂ : ℂ} {Rfar R' : ℝ} {R R₁ Q : Polynomial (Polynomial ℂ)}
    (hdecomp : R = R₁ + quadraticRelationFactor (c₂ - c₁) * Q)
    (hrel : Set.EqOn
      (fun z => R.eval₂ (Polynomial.evalRingHom (bottcherCoord c₁ z))
        (bottcherCoord c₁ (quadratic c₂ z))) (fun _ => (0 : ℂ))
      {z : ℂ | Rfar < ‖z‖ ∧ R' < ‖bottcherCoord c₁ z‖}) :
    Set.EqOn
      (fun z => R₁.eval₂ (Polynomial.evalRingHom (bottcherCoord c₁ z))
          (bottcherCoord c₁ (quadratic c₂ z)) +
        (bottcherCoord c₁ (quadratic c₂ z) - ((bottcherCoord c₁ z) ^ 2 + (c₂ - c₁))) *
          Q.eval₂ (Polynomial.evalRingHom (bottcherCoord c₁ z))
            (bottcherCoord c₁ (quadratic c₂ z)))
      (fun _ => (0 : ℂ))
      {z : ℂ | Rfar < ‖z‖ ∧ R' < ‖bottcherCoord c₁ z‖} := by
  exact eqOn_remainder_tail_of_shifted_factor
    (U := {z : ℂ | Rfar < ‖z‖ ∧ R' < ‖bottcherCoord c₁ z‖})
    (A := fun z => bottcherCoord c₁ z)
    (B := fun z => bottcherCoord c₁ (quadratic c₂ z))
    (R := R) (R₁ := R₁) (Q := Q) (d := c₂ - c₁) hdecomp hrel

end Bottcher

namespace Bottcher
open Polynomial Filter

/-- The transported quadratic defect times any weighted-bounded polynomial is a vanishing scaled tail. -/
theorem tendsto_scaled_transported_defect_mul_eval_zero
    (c₁ c₂ : ℂ) (Q : Polynomial (Polynomial ℂ)) {W : ℕ}
    (hweight : ∀ j : Fin (Q.natDegree + 1),
      ∀ i : Fin ((Q.coeff (j : ℕ)).natDegree + 1), (i : ℕ) + 2 * (j : ℕ) ≤ W) :
    Tendsto (fun t : ℝ => ((t : ℂ)⁻¹) ^ W *
      ((bottcherCoord c₁ (quadratic c₂ (t : ℂ)) -
          ((bottcherCoord c₁ (t : ℂ)) ^ 2 + (c₂ - c₁))) *
        Q.eval₂ (Polynomial.evalRingHom (bottcherCoord c₁ (t : ℂ)))
          (bottcherCoord c₁ (quadratic c₂ (t : ℂ))))) atTop (𝓝 0) := by
  have hdef : Tendsto (fun t : ℝ => bottcherCoord c₁ (quadratic c₂ (t : ℂ)) -
        (bottcherCoord c₁ (t : ℂ)) ^ 2 - (c₂ - c₁)) atTop (𝓝 0) := by
    have hbase := (tendsto_transferred_quadratic_minus_square_along_real_bottcher_ray c₁ c₂).sub
      (tendsto_const_nhds (x := c₂ - c₁))
    simpa using hbase
  have hQ := bottcher_weighted_scaled_eval_tendsto_top_sum c₁ c₂ Q hweight
  have hprod := hdef.mul hQ
  convert hprod using 1
  · funext t
    ring_nf
  · ring_nf

end Bottcher

namespace Bottcher
open Polynomial Filter

/-- One shifted-factor descent step: after subtracting `(Z-W²-(c₂-c₁)) Q` from an exact transported
relation, the remainder has a vanishing scaled defect tail, so its weighted top slice again has the
factor `Z-W²`. This is the formal core of the defect-twisted descent suggested by the Grok pass. -/
theorem quadratic_factor_weightedTopSlice_of_shifted_factor_remainder
    {c₁ c₂ : ℂ} {Rfar R' : ℝ} {R R₁ Q : Polynomial (Polynomial ℂ)} {W WQ : ℕ}
    (hdecomp : R = R₁ + quadraticRelationFactor (c₂ - c₁) * Q)
    (hweightR₁ : ∀ j : Fin (R₁.natDegree + 1),
      ∀ i : Fin ((R₁.coeff (j : ℕ)).natDegree + 1), (i : ℕ) + 2 * (j : ℕ) ≤ W)
    (hweightQ : ∀ j : Fin (Q.natDegree + 1),
      ∀ i : Fin ((Q.coeff (j : ℕ)).natDegree + 1), (i : ℕ) + 2 * (j : ℕ) ≤ WQ)
    (hleWQ : WQ ≤ W)
    (hrel : Set.EqOn
      (fun z => R.eval₂ (Polynomial.evalRingHom (bottcherCoord c₁ z))
        (bottcherCoord c₁ (quadratic c₂ z))) (fun _ => (0 : ℂ))
      {z : ℂ | Rfar < ‖z‖ ∧ R' < ‖bottcherCoord c₁ z‖}) :
    quadraticRelationFactor 0 ∣ weightedTopSlice R₁ W := by
  let Tail : ℂ → ℂ := fun z =>
    (bottcherCoord c₁ (quadratic c₂ z) - ((bottcherCoord c₁ z) ^ 2 + (c₂ - c₁))) *
      Q.eval₂ (Polynomial.evalRingHom (bottcherCoord c₁ z))
        (bottcherCoord c₁ (quadratic c₂ z))
  have htailWQ : Tendsto (fun t : ℝ => ((t : ℂ)⁻¹) ^ WQ * Tail (t : ℂ)) atTop (𝓝 0) := by
    simpa [Tail, quadratic] using
      tendsto_scaled_transported_defect_mul_eval_zero c₁ c₂ Q hweightQ
  have htailW : Tendsto (fun t : ℝ => ((t : ℂ)⁻¹) ^ W * Tail (t : ℂ)) atTop (𝓝 0) := by
    obtain ⟨k, rfl⟩ := exists_add_of_le hleWQ
    rw [show WQ + k = WQ + k by rfl]
    have hinvpow : Tendsto (fun t : ℝ => ((t : ℂ)⁻¹) ^ k) atTop (𝓝 (0 ^ k)) :=
      tendsto_inv_ofReal_atTop_bottcher.pow k
    have hbounded : Tendsto (fun t : ℝ => ((t : ℂ)⁻¹) ^ k) atTop (𝓝 (0 ^ k)) := hinvpow
    have hmul := htailWQ.mul hbounded
    convert hmul using 1
    · funext t
      rw [pow_add]
      ring_nf
    · ring_nf
  refine quadratic_factor_weightedTopSlice_of_transported_pullback_relation_with_scaled_tail
    (c₁ := c₁) (c₂ := c₂) (Rfar := Rfar) (R' := R') (R := R₁) (W := W)
    (Tail := Tail) hweightR₁ htailW ?_
  simpa [Tail] using eqOn_transported_remainder_tail_of_shifted_factor
    (c₁ := c₁) (c₂ := c₂) (Rfar := Rfar) (R' := R')
    (R := R) (R₁ := R₁) (Q := Q) hdecomp hrel

end Bottcher

namespace Bottcher
open Polynomial Filter

/-- Coefficient extraction for a finite weighted-homogeneous polynomial.  This is the algebraic
injectivity step behind top-weight descent: once we know a top slice is zero as a polynomial, each
individual bidegree coefficient in that slice is zero. -/
lemma coeff_coeff_weightedHomogeneousPoly {ι : Type*} [Fintype ι]
    (a : ι → ℂ) (I J : ι → ℕ) (i j : ℕ) :
    ((weightedHomogeneousPoly a I J).coeff j).coeff i =
      ∑ k : ι, if I k = i ∧ J k = j then a k else 0 := by
  classical
  rw [weightedHomogeneousPoly]
  calc
    (((∑ k : ι, Polynomial.C ((Polynomial.C (a k) * (Polynomial.X : Polynomial ℂ) ^ I k : Polynomial ℂ)) *
          (Polynomial.X : Polynomial (Polynomial ℂ)) ^ J k).coeff j).coeff i)
        = (∑ k : ι, (((Polynomial.C ((Polynomial.C (a k) * (Polynomial.X : Polynomial ℂ) ^ I k : Polynomial ℂ)) *
          (Polynomial.X : Polynomial (Polynomial ℂ)) ^ J k).coeff j).coeff i)) := by
            rw [Polynomial.finsetSum_coeff, Polynomial.finsetSum_coeff]
    _ = ∑ k : ι, if I k = i ∧ J k = j then a k else 0 := by
      apply Finset.sum_congr rfl
      intro k _
      rw [Polynomial.coeff_C_mul_X_pow]
      by_cases hJ : J k = j
      · rw [if_pos hJ.symm]
        rw [Polynomial.coeff_C_mul_X_pow]
        by_cases hI : I k = i
        · rw [if_pos hI.symm]
          simp [hI, hJ]
        · have hI' : ¬ i = I k := by intro h; exact hI h.symm
          rw [if_neg hI']
          simp [hI]
      · have hJ' : ¬ j = J k := by intro h; exact hJ h.symm
        rw [if_neg hJ']
        simp [hJ]

/-- The coefficient of the concrete weighted top slice is the original coefficient if the bidegree has
weight exactly `W`, and zero otherwise. -/
lemma coeff_coeff_weightedTopSlice_self (R : Polynomial (Polynomial ℂ)) (W : ℕ)
    (j : Fin (R.natDegree + 1)) (i : Fin ((R.coeff (j : ℕ)).natDegree + 1)) :
    ((weightedTopSlice R W).coeff (j : ℕ)).coeff (i : ℕ) =
      if (i : ℕ) + 2 * (j : ℕ) = W then (R.coeff (j : ℕ)).coeff (i : ℕ) else 0 := by
  classical
  rw [weightedTopSlice, coeff_coeff_weightedHomogeneousPoly]
  rw [Finset.sum_eq_single (Sigma.mk j i)]
  · simp
  · intro b _ hne
    rcases b with ⟨j', i'⟩
    by_cases hJ : (j' : ℕ) = (j : ℕ)
    · have hj' : j' = j := Fin.ext hJ
      subst hj'
      by_cases hI : (i' : ℕ) = (i : ℕ)
      · have hi' : i' = i := Fin.ext hI
        subst hi'
        exact (hne rfl).elim
      · simp [hI]
    · simp [hJ]
  · intro hmem
    exact (hmem (Finset.mem_univ _)).elim

/-- If a concrete weighted top slice is zero, then every original coefficient of exact weight `W`
inside the defining finite box is zero. -/
lemma coeff_eq_zero_of_weightedTopSlice_eq_zero (R : Polynomial (Polynomial ℂ)) {W : ℕ}
    (hzero : weightedTopSlice R W = 0)
    (j : Fin (R.natDegree + 1)) (i : Fin ((R.coeff (j : ℕ)).natDegree + 1))
    (hwt : (i : ℕ) + 2 * (j : ℕ) = W) :
    (R.coeff (j : ℕ)).coeff (i : ℕ) = 0 := by
  have hcoeff := congrArg (fun P : Polynomial (Polynomial ℂ) => (P.coeff (j : ℕ)).coeff (i : ℕ)) hzero
  change ((weightedTopSlice R W).coeff (j : ℕ)).coeff (i : ℕ) = 0 at hcoeff
  rw [coeff_coeff_weightedTopSlice_self, hwt] at hcoeff
  simpa using hcoeff

end Bottcher

namespace Bottcher
open Polynomial Filter

/-- Support expansion of a bivariate polynomial evaluation: outer support in `Z`, inner support in `W`.
This is the support-indexed replacement for rectangular `natDegree` boxes in the descent. -/
lemma eval₂_eq_sum_support_coeff (R : Polynomial (Polynomial ℂ)) (A B : ℂ) :
    R.eval₂ (Polynomial.evalRingHom A) B =
      ∑ j ∈ R.support, ∑ i ∈ (R.coeff j).support,
        (R.coeff j).coeff i * A ^ i * B ^ j := by
  rw [Polynomial.eval₂_eq_sum, Polynomial.sum_def]
  refine Finset.sum_congr rfl ?_
  intro j _
  change (R.coeff j).eval A * B ^ j = ∑ i ∈ (R.coeff j).support,
    (R.coeff j).coeff i * A ^ i * B ^ j
  rw [Polynomial.eval_eq_sum, Polynomial.sum_def]
  rw [Finset.sum_mul]

/-- The sigma-indexed support top sum is the same as the nested support top sum. -/
lemma support_sigma_top_sum_eq (R : Polynomial (Polynomial ℂ)) (W : ℕ) :
    (∑ s : Sigma (fun j : {j // j ∈ R.support} => {i // i ∈ (R.coeff (j : ℕ)).support}),
      (if (s.2 : ℕ) + 2 * (s.1 : ℕ) = W then
        (R.coeff (s.1 : ℕ)).coeff (s.2 : ℕ) else 0)) =
    ∑ j ∈ R.support, ∑ i ∈ (R.coeff j).support,
      (if i + 2 * j = W then (R.coeff j).coeff i else 0) := by
  classical
  rw [Fintype.sum_sigma]
  symm
  rw [Finset.sum_subtype R.support (by intro j; rfl)]
  apply Finset.sum_congr rfl
  intro j _
  rw [Finset.sum_subtype (R.coeff (j : ℕ)).support (by intro i; rfl)]

/-- The sigma-indexed support raw monomial sum is the polynomial evaluation. -/
lemma support_sigma_raw_sum_eq (R : Polynomial (Polynomial ℂ)) (A B : ℂ) :
    (∑ s : Sigma (fun j : {j // j ∈ R.support} => {i // i ∈ (R.coeff (j : ℕ)).support}),
      (R.coeff (s.1 : ℕ)).coeff (s.2 : ℕ) * A ^ (s.2 : ℕ) * B ^ (s.1 : ℕ)) =
    R.eval₂ (Polynomial.evalRingHom A) B := by
  classical
  rw [eval₂_eq_sum_support_coeff]
  rw [Fintype.sum_sigma]
  symm
  rw [Finset.sum_subtype R.support (by intro j; rfl)]
  apply Finset.sum_congr rfl
  intro j _
  rw [Finset.sum_subtype (R.coeff (j : ℕ)).support (by intro i; rfl)]

/-- Support-indexed Böttcher weighted top extraction with a scaled tail.  The weight hypothesis ranges
only over actual nonzero monomials, which is the form needed for an iterated top-weight descent. -/
theorem bottcher_weighted_support_top_sum_zero_of_eventual_relation_with_scaled_tail
    (c₁ c₂ : ℂ) (R : Polynomial (Polynomial ℂ)) {W : ℕ} {Tail : ℝ → ℂ}
    (hweight : ∀ j ∈ R.support, ∀ i ∈ (R.coeff j).support, i + 2 * j ≤ W)
    (hTail : Tendsto (fun t : ℝ => ((t : ℂ)⁻¹) ^ W * Tail t) atTop (𝓝 0))
    (hrel : ∀ᶠ t : ℝ in atTop,
      R.eval₂ (Polynomial.evalRingHom (bottcherCoord c₁ (t : ℂ)))
        (bottcherCoord c₁ (quadratic c₂ (t : ℂ))) + Tail t = 0) :
    ∑ j ∈ R.support, ∑ i ∈ (R.coeff j).support,
      (if i + 2 * j = W then (R.coeff j).coeff i else 0) = 0 := by
  classical
  have htop := bottcher_weighted_top_sum_zero_of_raw_eventual_relation_with_scaled_tail c₁ c₂
    (ι := Sigma (fun j : {j // j ∈ R.support} => {i // i ∈ (R.coeff (j : ℕ)).support}))
    (W := W)
    (a := fun s => (R.coeff (s.1 : ℕ)).coeff (s.2 : ℕ))
    (I := fun s => (s.2 : ℕ)) (J := fun s => (s.1 : ℕ)) ?_ hTail ?_
  · rw [support_sigma_top_sum_eq] at htop
    exact htop
  · intro s
    exact hweight (s.1 : ℕ) s.1.property (s.2 : ℕ) s.2.property
  · filter_upwards [hrel] with t ht
    rw [support_sigma_raw_sum_eq]
    exact ht

end Bottcher

namespace Bottcher
open Polynomial Filter

/-- The support-indexed weighted top slice of `R`, using only actual nonzero monomials. -/
noncomputable def weightedSupportTopSlice (R : Polynomial (Polynomial ℂ)) (W : ℕ) :
    Polynomial (Polynomial ℂ) :=
  weightedHomogeneousPoly
    (ι := Sigma (fun j : {j // j ∈ R.support} => {i // i ∈ (R.coeff (j : ℕ)).support}))
    (fun s => if (s.2 : ℕ) + 2 * (s.1 : ℕ) = W then
      (R.coeff (s.1 : ℕ)).coeff (s.2 : ℕ) else 0)
    (fun s => (s.2 : ℕ)) (fun s => (s.1 : ℕ))

/-- All actual monomials of `R` have weighted degree at most `W`. -/
def weightedSupportBelow (R : Polynomial (Polynomial ℂ)) (W : ℕ) : Prop :=
  ∀ j ∈ R.support, ∀ i ∈ (R.coeff j).support, i + 2 * j ≤ W

/-- Coefficient extraction for the support-indexed top slice. -/
lemma coeff_coeff_weightedSupportTopSlice_self (R : Polynomial (Polynomial ℂ)) (W : ℕ)
    {j i : ℕ} (hj : j ∈ R.support) (hi : i ∈ (R.coeff j).support) :
    ((weightedSupportTopSlice R W).coeff j).coeff i =
      if i + 2 * j = W then (R.coeff j).coeff i else 0 := by
  classical
  rw [weightedSupportTopSlice, coeff_coeff_weightedHomogeneousPoly]
  rw [Finset.sum_eq_single (Sigma.mk ⟨j, hj⟩ ⟨i, hi⟩)]
  · simp
  · intro b _ hne
    rcases b with ⟨j', i'⟩
    by_cases hJ : (j' : ℕ) = j
    · subst hJ
      by_cases hI : (i' : ℕ) = i
      · subst hI
        exact (hne rfl).elim
      · simp [hI]
    · simp [hJ]
  · intro hmem
    exact (hmem (Finset.mem_univ _)).elim

/-- If the support-indexed top slice is zero, every actual monomial of exact top weight has zero
coefficient. -/
lemma coeff_eq_zero_of_weightedSupportTopSlice_eq_zero (R : Polynomial (Polynomial ℂ)) {W : ℕ}
    (hzero : weightedSupportTopSlice R W = 0)
    {j i : ℕ} (hj : j ∈ R.support) (hi : i ∈ (R.coeff j).support)
    (hwt : i + 2 * j = W) :
    (R.coeff j).coeff i = 0 := by
  have hcoeff := congrArg (fun P : Polynomial (Polynomial ℂ) => (P.coeff j).coeff i) hzero
  change ((weightedSupportTopSlice R W).coeff j).coeff i = 0 at hcoeff
  rw [coeff_coeff_weightedSupportTopSlice_self R W hj hi, hwt] at hcoeff
  simpa using hcoeff

/-- If the support-indexed top slice is zero, the actual support bound strictly drops by one. -/
lemma weightedSupportBelow_pred_of_topSlice_zero (R : Polynomial (Polynomial ℂ)) {W : ℕ}
    (hbelow : weightedSupportBelow R W)
    (hzero : weightedSupportTopSlice R W = 0) :
    weightedSupportBelow R (W - 1) := by
  intro j hj i hi
  have hle := hbelow j hj i hi
  have hne : i + 2 * j ≠ W := by
    intro hwt
    have hcz := coeff_eq_zero_of_weightedSupportTopSlice_eq_zero R hzero hj hi hwt
    exact (Polynomial.mem_support_iff.mp hi) hcz
  have hlt : i + 2 * j < W := Nat.lt_of_le_of_ne hle hne
  omega

end Bottcher

namespace Bottcher
open Polynomial Filter

/-- Böttcher divided weighted polynomial evaluation has a finite top-weight limit over actual support. -/
theorem bottcher_weighted_support_scaled_eval_tendsto_top_sum
    (c₁ c₂ : ℂ) (R : Polynomial (Polynomial ℂ)) {W : ℕ}
    (hweight : weightedSupportBelow R W) :
    Tendsto (fun t : ℝ => ((t : ℂ)⁻¹) ^ W *
      R.eval₂ (Polynomial.evalRingHom (bottcherCoord c₁ (t : ℂ)))
        (bottcherCoord c₁ (quadratic c₂ (t : ℂ)))) atTop
      (𝓝 (∑ j ∈ R.support, ∑ i ∈ (R.coeff j).support,
        (if i + 2 * j = W then (R.coeff j).coeff i else 0))) := by
  classical
  have hdiv := weighted_sum_tendsto_top_filter
    (l := (atTop : Filter ℝ))
    (W := W)
    (a := fun s : Sigma (fun j : {j // j ∈ R.support} => {i // i ∈ (R.coeff (j : ℕ)).support}) =>
      (R.coeff (s.1 : ℕ)).coeff (s.2 : ℕ))
    (I := fun s : Sigma (fun j : {j // j ∈ R.support} => {i // i ∈ (R.coeff (j : ℕ)).support}) =>
      (s.2 : ℕ))
    (J := fun s : Sigma (fun j : {j // j ∈ R.support} => {i // i ∈ (R.coeff (j : ℕ)).support}) =>
      (s.1 : ℕ))
    (x := fun t : ℝ => ((t : ℂ)⁻¹))
    (P := fun t : ℝ => bottcherCoord c₁ (t : ℂ) / (t : ℂ))
    (Q := fun t : ℝ => bottcherCoord c₁ (quadratic c₂ (t : ℂ)) / ((t : ℂ) ^ 2))
    (fun s => hweight (s.1 : ℕ) s.1.property (s.2 : ℕ) s.2.property)
    tendsto_inv_ofReal_atTop_bottcher (tendsto_bottcherCoord_real_div_atTop c₁)
    (tendsto_transferred_quadratic_real_div_sq_atTop c₁ c₂)
  rw [support_sigma_top_sum_eq] at hdiv
  refine hdiv.congr' ?_
  filter_upwards with t
  rw [← support_sigma_raw_sum_eq]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl ?_
  intro s _
  exact (weighted_scale_term_identity (z := (t : ℂ))
    (A := bottcherCoord c₁ (t : ℂ))
    (B := bottcherCoord c₁ (quadratic c₂ (t : ℂ)))
    (a := (R.coeff (s.1 : ℕ)).coeff (s.2 : ℕ))
    (i := (s.2 : ℕ)) (j := (s.1 : ℕ)) (W := W)
    (hweight (s.1 : ℕ) s.1.property (s.2 : ℕ) s.2.property))

end Bottcher

namespace Bottcher
open Polynomial Filter

/-- A pulled-back transported relation with a scaled tail forces the support-indexed top coefficient sum
of `R` to vanish. -/
theorem weighted_support_top_zero_of_transported_pullback_relation_with_scaled_tail
    {c₁ c₂ : ℂ} {Rfar R' : ℝ} (R : Polynomial (Polynomial ℂ)) {W : ℕ} {Tail : ℂ → ℂ}
    (hweight : weightedSupportBelow R W)
    (hTail : Tendsto (fun t : ℝ => ((t : ℂ)⁻¹) ^ W * Tail (t : ℂ)) atTop (𝓝 0))
    (hrel : Set.EqOn
      (fun z => R.eval₂ (Polynomial.evalRingHom (bottcherCoord c₁ z))
        (bottcherCoord c₁ (quadratic c₂ z)) + Tail z) (fun _ => (0 : ℂ))
      {z : ℂ | Rfar < ‖z‖ ∧ R' < ‖bottcherCoord c₁ z‖}) :
    ∑ j ∈ R.support, ∑ i ∈ (R.coeff j).support,
      (if i + 2 * j = W then (R.coeff j).coeff i else 0) = 0 := by
  refine bottcher_weighted_support_top_sum_zero_of_eventual_relation_with_scaled_tail
    c₁ c₂ R hweight hTail ?_
  filter_upwards [eventually_real_mem_bottcher_pullback_far c₁ Rfar R'] with t ht
  exact hrel ht

/-- A support-indexed transported pullback relation with a vanishing scaled tail forces the support top
slice of `R` to have the top parabola factor `Z-W²`. -/
theorem quadratic_factor_weightedSupportTopSlice_of_transported_pullback_relation_with_scaled_tail
    {c₁ c₂ : ℂ} {Rfar R' : ℝ} (R : Polynomial (Polynomial ℂ)) {W : ℕ} {Tail : ℂ → ℂ}
    (hweight : weightedSupportBelow R W)
    (hTail : Tendsto (fun t : ℝ => ((t : ℂ)⁻¹) ^ W * Tail (t : ℂ)) atTop (𝓝 0))
    (hrel : Set.EqOn
      (fun z => R.eval₂ (Polynomial.evalRingHom (bottcherCoord c₁ z))
        (bottcherCoord c₁ (quadratic c₂ z)) + Tail z) (fun _ => (0 : ℂ))
      {z : ℂ | Rfar < ‖z‖ ∧ R' < ‖bottcherCoord c₁ z‖}) :
    quadraticRelationFactor 0 ∣ weightedSupportTopSlice R W := by
  dsimp [weightedSupportTopSlice]
  apply quadratic_factor_of_weightedHomogeneous_top_sum_zero
  · intro s
    exact hweight (s.1 : ℕ) s.1.property (s.2 : ℕ) s.2.property
  · rw [support_sigma_top_sum_eq]
    exact weighted_support_top_zero_of_transported_pullback_relation_with_scaled_tail
      (c₁ := c₁) (c₂ := c₂) (Rfar := Rfar) (R' := R') R hweight hTail hrel

/-- The transported quadratic defect times any support-bounded polynomial is a vanishing scaled tail. -/
theorem tendsto_scaled_transported_defect_mul_eval_zero_support
    (c₁ c₂ : ℂ) (Q : Polynomial (Polynomial ℂ)) {W : ℕ}
    (hweight : weightedSupportBelow Q W) :
    Tendsto (fun t : ℝ => ((t : ℂ)⁻¹) ^ W *
      ((bottcherCoord c₁ (quadratic c₂ (t : ℂ)) -
          ((bottcherCoord c₁ (t : ℂ)) ^ 2 + (c₂ - c₁))) *
        Q.eval₂ (Polynomial.evalRingHom (bottcherCoord c₁ (t : ℂ)))
          (bottcherCoord c₁ (quadratic c₂ (t : ℂ))))) atTop (𝓝 0) := by
  have hdef : Tendsto (fun t : ℝ => bottcherCoord c₁ (quadratic c₂ (t : ℂ)) -
        (bottcherCoord c₁ (t : ℂ)) ^ 2 - (c₂ - c₁)) atTop (𝓝 0) := by
    have hbase := (tendsto_transferred_quadratic_minus_square_along_real_bottcher_ray c₁ c₂).sub
      (tendsto_const_nhds (x := c₂ - c₁))
    simpa using hbase
  have hQ := bottcher_weighted_support_scaled_eval_tendsto_top_sum c₁ c₂ Q hweight
  have hprod := hdef.mul hQ
  convert hprod using 1
  · funext t
    ring_nf
  · ring_nf

/-- The transported quadratic defect has one extra inverse-power of decay.  Thus a support-weight
`W` quotient produces a vanishing tail already at scale `W-1`. -/
theorem tendsto_scaled_transported_defect_mul_eval_zero_support_pred
    (c₁ c₂ : ℂ) (Q : Polynomial (Polynomial ℂ)) {W : ℕ}
    (hweight : weightedSupportBelow Q W) :
    Tendsto (fun t : ℝ => ((t : ℂ)⁻¹) ^ (W - 1) *
      ((bottcherCoord c₁ (quadratic c₂ (t : ℂ)) -
          ((bottcherCoord c₁ (t : ℂ)) ^ 2 + (c₂ - c₁))) *
        Q.eval₂ (Polynomial.evalRingHom (bottcherCoord c₁ (t : ℂ)))
          (bottcherCoord c₁ (quadratic c₂ (t : ℂ))))) atTop (𝓝 0) := by
  cases W with
  | zero =>
      simpa using tendsto_scaled_transported_defect_mul_eval_zero_support
        (c₁ := c₁) (c₂ := c₂) (Q := Q) (W := 0) hweight
  | succ W =>
      have hdef := tendsto_real_mul_transported_quadratic_defect_atTop c₁ c₂
      have hQ := bottcher_weighted_support_scaled_eval_tendsto_top_sum
        (c₁ := c₁) (c₂ := c₂) (R := Q) (W := W + 1) hweight
      have hprod := hdef.mul hQ
      have heq :
          (fun t : ℝ =>
            (t : ℂ) *
              (bottcherCoord c₁ (quadratic c₂ (t : ℂ)) -
                (bottcherCoord c₁ (t : ℂ) ^ 2 + (c₂ - c₁))) *
                (((t : ℂ)⁻¹) ^ (W + 1) *
                  Q.eval₂ (Polynomial.evalRingHom (bottcherCoord c₁ (t : ℂ)))
                    (bottcherCoord c₁ (quadratic c₂ (t : ℂ))))) =ᶠ[atTop]
            (fun t : ℝ => ((t : ℂ)⁻¹) ^ W *
              ((bottcherCoord c₁ (quadratic c₂ (t : ℂ)) -
                  (bottcherCoord c₁ (t : ℂ) ^ 2 + (c₂ - c₁))) *
                Q.eval₂ (Polynomial.evalRingHom (bottcherCoord c₁ (t : ℂ)))
                  (bottcherCoord c₁ (quadratic c₂ (t : ℂ))))) := by
        filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
        have htne : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt ht)
        let E : ℂ := bottcherCoord c₁ (quadratic c₂ (t : ℂ)) -
          (bottcherCoord c₁ (t : ℂ) ^ 2 + (c₂ - c₁))
        let V : ℂ := Q.eval₂ (Polynomial.evalRingHom (bottcherCoord c₁ (t : ℂ)))
          (bottcherCoord c₁ (quadratic c₂ (t : ℂ)))
        have hpows : (t : ℂ) * ((t : ℂ)⁻¹) ^ (W + 1) = ((t : ℂ)⁻¹) ^ W := by
          rw [pow_succ]
          have hcancel : (t : ℂ) * (t : ℂ)⁻¹ = 1 := mul_inv_cancel₀ htne
          calc
            (t : ℂ) * (((t : ℂ)⁻¹) ^ W * (t : ℂ)⁻¹)
                = ((t : ℂ) * (t : ℂ)⁻¹) * ((t : ℂ)⁻¹) ^ W := by ring
            _ = 1 * ((t : ℂ)⁻¹) ^ W := by rw [hcancel]
            _ = ((t : ℂ)⁻¹) ^ W := by rw [one_mul]
        change (t : ℂ) * E * (((t : ℂ)⁻¹) ^ (W + 1) * V) =
          ((t : ℂ)⁻¹) ^ W * (E * V)
        calc
          (t : ℂ) * E * (((t : ℂ)⁻¹) ^ (W + 1) * V)
              = ((t : ℂ) * ((t : ℂ)⁻¹) ^ (W + 1)) * (E * V) := by ring
          _ = ((t : ℂ)⁻¹) ^ W * (E * V) := by rw [hpows]
      simpa [inv_pow] using hprod.congr' heq

/-- Exact shifted division closes immediately when the quotient's support weight is no larger than
the univariate shifted-remainder degree.  This is the algebraic/asymptotic boundary of the current
route: beyond this inequality, one needs stronger decay of the transported defect. -/
theorem quadratic_factor_of_bottcher_relation_and_weightedSupport_quotient_le_remainder_degree
    {c₁ c₂ : ℂ} (R Q : Polynomial (Polynomial ℂ)) {WQ : ℕ}
    (hdecomp : R =
      Polynomial.C (R.eval (Polynomial.X ^ 2 + Polynomial.C (c₂ - c₁))) +
        quadraticRelationFactor (c₂ - c₁) * Q)
    (hrel : ∀ᶠ t : ℝ in atTop,
      R.eval₂ (Polynomial.evalRingHom (bottcherCoord c₁ (t : ℂ)))
        (bottcherCoord c₁ (quadratic c₂ (t : ℂ))) = 0)
    (hweightQ : weightedSupportBelow Q WQ)
    (hle : WQ ≤ (R.eval (Polynomial.X ^ 2 + Polynomial.C (c₂ - c₁))).natDegree) :
    quadraticRelationFactor (c₂ - c₁) ∣ R := by
  refine quadratic_factor_of_bottcher_relation_and_scaled_defect_quotient_zero
    (c := c₁) (c₂ := c₂) (d := c₂ - c₁) R Q hdecomp hrel ?_
  have htailWQ := tendsto_scaled_transported_defect_mul_eval_zero_support c₁ c₂ Q hweightQ
  obtain ⟨k, hk⟩ := exists_add_of_le hle
  have hinvpow : Tendsto (fun t : ℝ => ((t : ℂ)⁻¹) ^ k) atTop (𝓝 (0 ^ k)) :=
    tendsto_inv_ofReal_atTop_bottcher.pow k
  have hmul := htailWQ.mul hinvpow
  rw [hk]
  convert hmul using 1
  · funext t
    rw [pow_add]
    ring_nf
  · ring_nf

/-- Exact shifted division closes when the quotient support weight is at most one more than the
univariate shifted-remainder degree.  The extra unit comes from the proved `o(1/t)` transported-defect
estimate. -/
theorem quadratic_factor_of_bottcher_relation_and_weightedSupport_quotient_le_remainder_degree_succ
    {c₁ c₂ : ℂ} (R Q : Polynomial (Polynomial ℂ)) {WQ : ℕ}
    (hdecomp : R =
      Polynomial.C (R.eval (Polynomial.X ^ 2 + Polynomial.C (c₂ - c₁))) +
        quadraticRelationFactor (c₂ - c₁) * Q)
    (hrel : ∀ᶠ t : ℝ in atTop,
      R.eval₂ (Polynomial.evalRingHom (bottcherCoord c₁ (t : ℂ)))
        (bottcherCoord c₁ (quadratic c₂ (t : ℂ))) = 0)
    (hweightQ : weightedSupportBelow Q WQ)
    (hle : WQ ≤ (R.eval (Polynomial.X ^ 2 + Polynomial.C (c₂ - c₁))).natDegree + 1) :
    quadraticRelationFactor (c₂ - c₁) ∣ R := by
  refine quadratic_factor_of_bottcher_relation_and_scaled_defect_quotient_zero
    (c := c₁) (c₂ := c₂) (d := c₂ - c₁) R Q hdecomp hrel ?_
  have htailPred := tendsto_scaled_transported_defect_mul_eval_zero_support_pred
    (c₁ := c₁) (c₂ := c₂) (Q := Q) (W := WQ) hweightQ
  have hle' : WQ - 1 ≤ (R.eval (Polynomial.X ^ 2 + Polynomial.C (c₂ - c₁))).natDegree := by
    omega
  obtain ⟨k, hk⟩ := exists_add_of_le hle'
  have hinvpow : Tendsto (fun t : ℝ => ((t : ℂ)⁻¹) ^ k) atTop (𝓝 (0 ^ k)) :=
    tendsto_inv_ofReal_atTop_bottcher.pow k
  have hmul := htailPred.mul hinvpow
  rw [hk]
  convert hmul using 1
  · funext t
    rw [pow_add]
    ring_nf
  · ring_nf

/-- Far-field no-relation criterion from exact shifted division plus a quotient-weight bound.
The remaining non-formalized content of this route is isolated in `hquot`: every pulled-back
transported relation admits an exact shifted quotient whose support weight is bounded by the degree of
the univariate shifted-parabola remainder plus one. -/
theorem no_relation_of_far_bottcher_exact_division_weightedSupport_quotient_descent
    {c₁ c₂ : ℂ} {Rfar R' : ℝ}
    (hquot : ∀ R : Polynomial (Polynomial ℂ), R ≠ 0 →
      Set.EqOn
        (fun z => R.eval₂ (Polynomial.evalRingHom (bottcherCoord c₁ z))
          (bottcherCoord c₁ (quadratic c₂ z))) (fun _ => (0 : ℂ))
        {z : ℂ | Rfar < ‖z‖ ∧ R' < ‖bottcherCoord c₁ z‖} →
      ∃ Q : Polynomial (Polynomial ℂ), ∃ WQ : ℕ,
        R = Polynomial.C (R.eval (Polynomial.X ^ 2 + Polynomial.C (c₂ - c₁))) +
            quadraticRelationFactor (c₂ - c₁) * Q ∧
          weightedSupportBelow Q WQ ∧
          WQ ≤ (R.eval (Polynomial.X ^ 2 + Polynomial.C (c₂ - c₁))).natDegree + 1)
    (hext : ∀ Q : Polynomial (Polynomial ℂ),
      Set.EqOn
        (fun z => Q.eval₂ (Polynomial.evalRingHom (bottcherCoord c₁ z))
          (bottcherCoord c₁ (quadratic c₂ z))) (fun _ => (0 : ℂ))
        {z : ℂ | z ∈ {z : ℂ | Rfar < ‖z‖ ∧ R' < ‖bottcherCoord c₁ z‖} ∧
          bottcherCoord c₁ (quadratic c₂ z) ≠ (bottcherCoord c₁ z) ^ 2 + (c₂ - c₁)} →
      Set.EqOn
        (fun z => Q.eval₂ (Polynomial.evalRingHom (bottcherCoord c₁ z))
          (bottcherCoord c₁ (quadratic c₂ z))) (fun _ => (0 : ℂ))
        {z : ℂ | Rfar < ‖z‖ ∧ R' < ‖bottcherCoord c₁ z‖}) :
    ∀ R : Polynomial (Polynomial ℂ), R ≠ 0 →
      ¬ Set.EqOn
        (fun z => R.eval₂ (Polynomial.evalRingHom (bottcherCoord c₁ z))
          (bottcherCoord c₁ (quadratic c₂ z))) (fun _ => (0 : ℂ))
        {z : ℂ | Rfar < ‖z‖ ∧ R' < ‖bottcherCoord c₁ z‖} := by
  refine no_relation_of_quadratic_factor_descent_eval₂ (U :=
    {z : ℂ | Rfar < ‖z‖ ∧ R' < ‖bottcherCoord c₁ z‖})
    (A := fun z => bottcherCoord c₁ z)
    (B := fun z => bottcherCoord c₁ (quadratic c₂ z)) (d := c₂ - c₁) ?_ hext
  intro R hR0 hrel
  obtain ⟨Q, WQ, hdecomp, hweightQ, hle⟩ := hquot R hR0 hrel
  refine quadratic_factor_of_bottcher_relation_and_weightedSupport_quotient_le_remainder_degree_succ
    (c₁ := c₁) (c₂ := c₂) (R := R) (Q := Q) (WQ := WQ)
    hdecomp ?_ hweightQ hle
  filter_upwards [eventually_real_mem_bottcher_pullback_far c₁ Rfar R'] with t ht
  exact hrel ht

/-- Support-indexed shifted-factor descent step.  After subtracting
`(Z-W²-(c₂-c₁)) Q` from an exact transported relation, the remainder has a vanishing scaled defect tail;
therefore its support top slice again has the factor `Z-W²`. -/
theorem quadratic_factor_weightedSupportTopSlice_of_shifted_factor_remainder
    {c₁ c₂ : ℂ} {Rfar R' : ℝ} {R R₁ Q : Polynomial (Polynomial ℂ)} {W WQ : ℕ}
    (hdecomp : R = R₁ + quadraticRelationFactor (c₂ - c₁) * Q)
    (hweightR₁ : weightedSupportBelow R₁ W)
    (hweightQ : weightedSupportBelow Q WQ)
    (hleWQ : WQ ≤ W)
    (hrel : Set.EqOn
      (fun z => R.eval₂ (Polynomial.evalRingHom (bottcherCoord c₁ z))
        (bottcherCoord c₁ (quadratic c₂ z))) (fun _ => (0 : ℂ))
      {z : ℂ | Rfar < ‖z‖ ∧ R' < ‖bottcherCoord c₁ z‖}) :
    quadraticRelationFactor 0 ∣ weightedSupportTopSlice R₁ W := by
  let Tail : ℂ → ℂ := fun z =>
    (bottcherCoord c₁ (quadratic c₂ z) - ((bottcherCoord c₁ z) ^ 2 + (c₂ - c₁))) *
      Q.eval₂ (Polynomial.evalRingHom (bottcherCoord c₁ z))
        (bottcherCoord c₁ (quadratic c₂ z))
  have htailWQ : Tendsto (fun t : ℝ => ((t : ℂ)⁻¹) ^ WQ * Tail (t : ℂ)) atTop (𝓝 0) := by
    simpa [Tail, quadratic] using
      tendsto_scaled_transported_defect_mul_eval_zero_support c₁ c₂ Q hweightQ
  have htailW : Tendsto (fun t : ℝ => ((t : ℂ)⁻¹) ^ W * Tail (t : ℂ)) atTop (𝓝 0) := by
    obtain ⟨k, rfl⟩ := exists_add_of_le hleWQ
    rw [show WQ + k = WQ + k by rfl]
    have hinvpow : Tendsto (fun t : ℝ => ((t : ℂ)⁻¹) ^ k) atTop (𝓝 (0 ^ k)) :=
      tendsto_inv_ofReal_atTop_bottcher.pow k
    have hmul := htailWQ.mul hinvpow
    convert hmul using 1
    · funext t
      rw [pow_add]
      ring_nf
    · ring_nf
  refine quadratic_factor_weightedSupportTopSlice_of_transported_pullback_relation_with_scaled_tail
    (c₁ := c₁) (c₂ := c₂) (Rfar := Rfar) (R' := R') (R := R₁) (W := W)
    (Tail := Tail) hweightR₁ htailW ?_
  simpa [Tail] using eqOn_transported_remainder_tail_of_shifted_factor
    (c₁ := c₁) (c₂ := c₂) (Rfar := Rfar) (R' := R')
    (R := R) (R₁ := R₁) (Q := Q) hdecomp hrel

end Bottcher

namespace Bottcher
open Polynomial Filter

/-- One usable support-descent iteration after a shifted top cancellation has been chosen.
If `R = R₁ + (Z-W²-(c₂-c₁))Q`, the chosen subtraction kills the current support top slice of `R₁`,
and the defect tail from `Q` is small at the next scale, then the actual support bound drops and the
next support top slice of `R₁` again has the top parabola factor. -/
theorem weightedSupport_descent_step_after_shifted_top_cancel
    {c₁ c₂ : ℂ} {Rfar R' : ℝ} {R R₁ Q : Polynomial (Polynomial ℂ)} {W WQ : ℕ}
    (hdecomp : R = R₁ + quadraticRelationFactor (c₂ - c₁) * Q)
    (hweightR₁W : weightedSupportBelow R₁ W)
    (htopzero : weightedSupportTopSlice R₁ W = 0)
    (hweightQ : weightedSupportBelow Q WQ)
    (hleQ : WQ ≤ W - 1)
    (hrel : Set.EqOn
      (fun z => R.eval₂ (Polynomial.evalRingHom (bottcherCoord c₁ z))
        (bottcherCoord c₁ (quadratic c₂ z))) (fun _ => (0 : ℂ))
      {z : ℂ | Rfar < ‖z‖ ∧ R' < ‖bottcherCoord c₁ z‖}) :
    weightedSupportBelow R₁ (W - 1) ∧
      quadraticRelationFactor 0 ∣ weightedSupportTopSlice R₁ (W - 1) := by
  have hbelowPred : weightedSupportBelow R₁ (W - 1) :=
    weightedSupportBelow_pred_of_topSlice_zero R₁ hweightR₁W htopzero
  exact ⟨hbelowPred,
    quadratic_factor_weightedSupportTopSlice_of_shifted_factor_remainder
      (c₁ := c₁) (c₂ := c₂) (Rfar := Rfar) (R' := R')
      (R := R) (R₁ := R₁) (Q := Q) (W := W - 1) (WQ := WQ)
      hdecomp hbelowPred hweightQ hleQ hrel⟩

end Bottcher

namespace Bottcher
open Polynomial Filter

/-- The finite geometric quotient for `Z^j - W^(2j)` by `Z-W²`, with inner variable `W` and outer
variable `Z`. -/
noncomputable def parabolaGeomQuotient (j : ℕ) : Polynomial (Polynomial ℂ) :=
  ∑ m ∈ Finset.range j,
    Polynomial.C ((Polynomial.X : Polynomial ℂ) ^ (2 * m)) *
      (Polynomial.X : Polynomial (Polynomial ℂ)) ^ (j - 1 - m)

lemma parabolaGeomQuotient_succ (j : ℕ) :
    parabolaGeomQuotient (j + 1) =
      (Polynomial.X : Polynomial (Polynomial ℂ)) ^ j +
        Polynomial.C ((Polynomial.X : Polynomial ℂ) ^ 2) * parabolaGeomQuotient j := by
  classical
  rw [parabolaGeomQuotient]
  rw [Finset.sum_range_succ']
  rw [parabolaGeomQuotient]
  simp only [mul_zero, pow_zero, Polynomial.C_1, one_mul, tsub_zero]
  rw [add_comm]
  congr 1
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl ?_
  intro m hm
  have hmle : m ≤ j - 1 := by
    have : m < j := Finset.mem_range.mp hm
    omega
  rw [← mul_assoc, ← Polynomial.C_mul]
  congr 1
  · rw [← pow_add]
    congr 1
    ring_nf
  · congr 1
    omega

/-- `(Z-W²)` times the finite geometric quotient equals `Z^j-W^(2j)`. -/
lemma quadraticRelationFactor_mul_parabolaGeomQuotient (j : ℕ) :
    quadraticRelationFactor 0 * parabolaGeomQuotient j =
      (Polynomial.X : Polynomial (Polynomial ℂ)) ^ j -
        Polynomial.C ((Polynomial.X : Polynomial ℂ) ^ (2 * j)) := by
  induction j with
  | zero =>
      simp [parabolaGeomQuotient, quadraticRelationFactor]
  | succ j ih =>
      rw [parabolaGeomQuotient_succ]
      rw [mul_add]
      rw [← mul_assoc]
      rw [mul_comm (quadraticRelationFactor 0) (Polynomial.C ((Polynomial.X : Polynomial ℂ) ^ 2))]
      rw [mul_assoc]
      rw [ih]
      rw [quadraticRelationFactor]
      simp only [Polynomial.C_0, add_zero]
      ring_nf
      rw [← Polynomial.C_mul, ← pow_add]

end Bottcher

namespace Bottcher
open Polynomial Filter

/-- Explicit quotient for a finite weighted-homogeneous polynomial by the top parabola `Z-W²`.
Each monomial contributes `a W^i * (Z^j-W^(2j))/(Z-W²)`. -/
noncomputable def weightedHomogeneousParabolaQuotient {ι : Type*} [Fintype ι]
    (a : ι → ℂ) (I J : ι → ℕ) : Polynomial (Polynomial ℂ) :=
  ∑ k : ι, Polynomial.C (Polynomial.C (a k) * (Polynomial.X : Polynomial ℂ) ^ I k) *
    parabolaGeomQuotient (J k)

/-- The explicit weighted-homogeneous quotient divides the top slice whenever all monomials have the
same weight and the coefficient sum is zero. -/
lemma quadraticRelationFactor_mul_weightedHomogeneousParabolaQuotient {ι : Type*} [Fintype ι]
    {a : ι → ℂ} {I J : ι → ℕ} {W : ℕ}
    (hweight : ∀ k : ι, I k + 2 * J k = W)
    (hsum : ∑ k : ι, a k = 0) :
    quadraticRelationFactor 0 * weightedHomogeneousParabolaQuotient a I J =
      weightedHomogeneousPoly a I J := by
  classical
  rw [weightedHomogeneousParabolaQuotient, weightedHomogeneousPoly]
  rw [Finset.mul_sum]
  calc
    (∑ x : ι, quadraticRelationFactor 0 *
        (Polynomial.C (Polynomial.C (a x) * (Polynomial.X : Polynomial ℂ) ^ I x) *
          parabolaGeomQuotient (J x)))
        = ∑ x : ι, Polynomial.C (Polynomial.C (a x) * (Polynomial.X : Polynomial ℂ) ^ I x) *
            ((Polynomial.X : Polynomial (Polynomial ℂ)) ^ J x -
              Polynomial.C ((Polynomial.X : Polynomial ℂ) ^ (2 * J x))) := by
          refine Finset.sum_congr rfl ?_
          intro k _
          rw [← mul_assoc]
          rw [mul_comm (quadraticRelationFactor 0)
            (Polynomial.C (Polynomial.C (a k) * (Polynomial.X : Polynomial ℂ) ^ I k))]
          rw [mul_assoc]
          rw [quadraticRelationFactor_mul_parabolaGeomQuotient]
    _ = (∑ x : ι, Polynomial.C (Polynomial.C (a x) * (Polynomial.X : Polynomial ℂ) ^ I x) *
            (Polynomial.X : Polynomial (Polynomial ℂ)) ^ J x) -
          (∑ x : ι, Polynomial.C (Polynomial.C (a x) * (Polynomial.X : Polynomial ℂ) ^ I x) *
              Polynomial.C ((Polynomial.X : Polynomial ℂ) ^ (2 * J x))) := by
          rw [← Finset.sum_sub_distrib]
          apply Finset.sum_congr rfl
          intro k _
          ring
    _ = (∑ x : ι, Polynomial.C (Polynomial.C (a x) * (Polynomial.X : Polynomial ℂ) ^ I x) *
            (Polynomial.X : Polynomial (Polynomial ℂ)) ^ J x) := by
          have hvanish : (∑ x : ι, Polynomial.C (Polynomial.C (a x) * (Polynomial.X : Polynomial ℂ) ^ I x) *
              Polynomial.C ((Polynomial.X : Polynomial ℂ) ^ (2 * J x))) = 0 := by
            calc
              (∑ x : ι, Polynomial.C (Polynomial.C (a x) * (Polynomial.X : Polynomial ℂ) ^ I x) *
                  Polynomial.C ((Polynomial.X : Polynomial ℂ) ^ (2 * J x)))
                  = ∑ x : ι, Polynomial.C (Polynomial.C (a x) * (Polynomial.X : Polynomial ℂ) ^ W) := by
                    refine Finset.sum_congr rfl ?_
                    intro k _
                    rw [← Polynomial.C_mul]
                    congr 1
                    rw [mul_assoc, ← pow_add, hweight k]
              _ = Polynomial.C (∑ x : ι, Polynomial.C (a x) * (Polynomial.X : Polynomial ℂ) ^ W) := by
                    simp
              _ = Polynomial.C (Polynomial.C (∑ x : ι, a x) * (Polynomial.X : Polynomial ℂ) ^ W) := by
                    congr 1
                    rw [← Finset.sum_mul]
                    simp
              _ = 0 := by rw [hsum]; simp
          rw [hvanish, sub_zero]

end Bottcher

namespace Bottcher
open Polynomial Filter

/-- The explicit parabola quotient is itself a weighted-homogeneous finite sum indexed by pairs
`(k,m)` with `m < J k`. -/
lemma weightedHomogeneousParabolaQuotient_eq_sigma {ι : Type*} [Fintype ι]
    (a : ι → ℂ) (I J : ι → ℕ) :
    weightedHomogeneousParabolaQuotient a I J =
      weightedHomogeneousPoly
        (ι := Sigma (fun k : ι => Fin (J k)))
        (fun s => a s.1)
        (fun s => I s.1 + 2 * (s.2 : ℕ))
        (fun s => J s.1 - 1 - (s.2 : ℕ)) := by
  classical
  rw [weightedHomogeneousParabolaQuotient, weightedHomogeneousPoly]
  rw [Fintype.sum_sigma]
  refine Finset.sum_congr rfl ?_
  intro k _
  rw [parabolaGeomQuotient]
  rw [Fin.sum_univ_eq_sum_range (fun m : ℕ =>
    Polynomial.C (Polynomial.C (a k) * (Polynomial.X : Polynomial ℂ) ^ (I k + 2 * m)) *
      (Polynomial.X : Polynomial (Polynomial ℂ)) ^ (J k - 1 - m)) (J k)]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl ?_
  intro m _
  rw [← mul_assoc, ← Polynomial.C_mul]
  congr 1
  rw [mul_assoc, ← pow_add]

/-- Every monomial in the explicit quotient has weight `W-2` when the source monomials have weight `W`. -/
lemma weightedHomogeneousParabolaQuotient_sigma_weight {ι : Type*} [Fintype ι]
    {I J : ι → ℕ} {W : ℕ}
    (hweight : ∀ k : ι, I k + 2 * J k = W)
    (s : Sigma (fun k : ι => Fin (J k))) :
    (I s.1 + 2 * (s.2 : ℕ)) + 2 * (J s.1 - 1 - (s.2 : ℕ)) = W - 2 := by
  have hslt : (s.2 : ℕ) < J s.1 := s.2.isLt
  have hw := hweight s.1
  omega

end Bottcher

namespace Bottcher
open Polynomial Filter

/-- Actual support monomial index for `R`: outer exponent `j` and inner exponent `i`, both in support. -/
abbrev weightedSupportIndex (R : Polynomial (Polynomial ℂ)) :=
  Sigma (fun j : {j // j ∈ R.support} => {i // i ∈ (R.coeff (j : ℕ)).support})

/-- The explicit quotient of the support top slice by `Z-W²`, indexed only by exact top-weight support
monomials. -/
noncomputable def weightedSupportTopQuotient (R : Polynomial (Polynomial ℂ)) (W : ℕ) :
    Polynomial (Polynomial ℂ) :=
  weightedHomogeneousParabolaQuotient
    (ι := {s : weightedSupportIndex R // (s.2 : ℕ) + 2 * (s.1 : ℕ) = W})
    (fun s => (R.coeff (s.1.1 : ℕ)).coeff (s.1.2 : ℕ))
    (fun s => (s.1.2 : ℕ))
    (fun s => (s.1.1 : ℕ))

/-- The support top slice is the weighted homogeneous polynomial over the exact-top support subtype. -/
lemma weightedSupportTopSlice_eq_topSubtype (R : Polynomial (Polynomial ℂ)) (W : ℕ) :
    weightedSupportTopSlice R W =
      weightedHomogeneousPoly
        (ι := {s : weightedSupportIndex R // (s.2 : ℕ) + 2 * (s.1 : ℕ) = W})
        (fun s => (R.coeff (s.1.1 : ℕ)).coeff (s.1.2 : ℕ))
        (fun s => (s.1.2 : ℕ))
        (fun s => (s.1.1 : ℕ)) := by
  classical
  let p : weightedSupportIndex R → Prop := fun s => (s.2 : ℕ) + 2 * (s.1 : ℕ) = W
  let term : weightedSupportIndex R → Polynomial (Polynomial ℂ) := fun s =>
    Polynomial.C (Polynomial.C ((R.coeff (s.1 : ℕ)).coeff (s.2 : ℕ)) *
      (Polynomial.X : Polynomial ℂ) ^ (s.2 : ℕ)) *
      (Polynomial.X : Polynomial (Polynomial ℂ)) ^ (s.1 : ℕ)
  rw [weightedSupportTopSlice, weightedHomogeneousPoly, weightedHomogeneousPoly]
  change (∑ k : weightedSupportIndex R,
      Polynomial.C (Polynomial.C (if p k then (R.coeff (k.1 : ℕ)).coeff (k.2 : ℕ) else 0) *
        (Polynomial.X : Polynomial ℂ) ^ (k.2 : ℕ)) *
        (Polynomial.X : Polynomial (Polynomial ℂ)) ^ (k.1 : ℕ)) =
    ∑ k : {s : weightedSupportIndex R // p s}, term k.1
  rw [← Finset.sum_subtype (Finset.univ.filter p) (by intro s; simp [p]) term]
  rw [Finset.sum_filter]
  refine Finset.sum_congr rfl ?_
  intro s _
  by_cases hs : p s
  · simp [term, p, hs]
  · simp [term, p, hs]

/-- The exact-top support-subtype coefficient sum equals the nested support top sum. -/
lemma weightedSupportTopSubtype_sum_eq (R : Polynomial (Polynomial ℂ)) (W : ℕ) :
    (∑ s : {s : weightedSupportIndex R // (s.2 : ℕ) + 2 * (s.1 : ℕ) = W},
      (R.coeff (s.1.1 : ℕ)).coeff (s.1.2 : ℕ)) =
    ∑ j ∈ R.support, ∑ i ∈ (R.coeff j).support,
      (if i + 2 * j = W then (R.coeff j).coeff i else 0) := by
  classical
  let p : weightedSupportIndex R → Prop := fun s => (s.2 : ℕ) + 2 * (s.1 : ℕ) = W
  let coeffTerm : weightedSupportIndex R → ℂ := fun s => (R.coeff (s.1 : ℕ)).coeff (s.2 : ℕ)
  rw [← support_sigma_top_sum_eq]
  change (∑ s : {s : weightedSupportIndex R // p s}, coeffTerm s.1) =
    ∑ s : weightedSupportIndex R, if p s then coeffTerm s else 0
  rw [← Finset.sum_subtype (Finset.univ.filter p) (by intro s; simp [p]) coeffTerm]
  rw [Finset.sum_filter]

/-- Explicit support-top quotient identity.  The quotient is constructed from exact top-weight support
monomials; the only hypothesis is the scalar top coefficient sum vanishing. -/
lemma quadraticRelationFactor_mul_weightedSupportTopQuotient (R : Polynomial (Polynomial ℂ)) {W : ℕ}
    (hsum : ∑ j ∈ R.support, ∑ i ∈ (R.coeff j).support,
      (if i + 2 * j = W then (R.coeff j).coeff i else 0) = 0) :
    quadraticRelationFactor 0 * weightedSupportTopQuotient R W = weightedSupportTopSlice R W := by
  classical
  rw [weightedSupportTopQuotient]
  rw [quadraticRelationFactor_mul_weightedHomogeneousParabolaQuotient]
  · rw [weightedSupportTopSlice_eq_topSubtype]
  · intro s
    exact s.property
  · rw [weightedSupportTopSubtype_sum_eq]
    exact hsum

end Bottcher

namespace Bottcher
open Polynomial Filter

/-- If every exact-weight coefficient is zero, the support top slice is the zero polynomial. -/
lemma weightedSupportTopSlice_eq_zero_of_coeff_eq_zero (R : Polynomial (Polynomial ℂ)) {W : ℕ}
    (hzero : ∀ j i : ℕ, i + 2 * j = W → (R.coeff j).coeff i = 0) :
    weightedSupportTopSlice R W = 0 := by
  classical
  rw [weightedSupportTopSlice, weightedHomogeneousPoly]
  apply Finset.sum_eq_zero
  intro s _
  by_cases hs : (s.2 : ℕ) + 2 * (s.1 : ℕ) = W
  · simp [hs, hzero (s.1 : ℕ) (s.2 : ℕ) hs]
  · simp [hs]

end Bottcher

namespace Bottcher
open Polynomial Filter

/-- The explicit support top quotient has no monomial of the old top weight `W`; its expanded terms all
have weight `W-2`. -/
lemma coeff_weightedSupportTopQuotient_eq_zero_of_weight_eq
    (R : Polynomial (Polynomial ℂ)) {W i j : ℕ} (hW : 2 ≤ W)
    (hij : i + 2 * j = W) :
    ((weightedSupportTopQuotient R W).coeff j).coeff i = 0 := by
  classical
  rw [weightedSupportTopQuotient, weightedHomogeneousParabolaQuotient_eq_sigma,
    coeff_coeff_weightedHomogeneousPoly]
  apply Finset.sum_eq_zero
  intro s _
  by_cases hs :
      ((s.1.1.2 : ℕ) + 2 * (s.2 : ℕ) = i ∧
        (s.1.1.1 : ℕ) - 1 - (s.2 : ℕ) = j)
  · have hterm := weightedHomogeneousParabolaQuotient_sigma_weight
      (ι := {s : weightedSupportIndex R // (s.2 : ℕ) + 2 * (s.1 : ℕ) = W})
      (I := fun s => (s.1.2 : ℕ))
      (J := fun s => (s.1.1 : ℕ))
      (W := W)
      (fun s => s.property) s
    have htarget : ((s.1.1.2 : ℕ) + 2 * (s.2 : ℕ)) +
        2 * ((s.1.1.1 : ℕ) - 1 - (s.2 : ℕ)) = W := by
      rw [hs.1, hs.2, hij]
    have hneq : W - 2 ≠ W := by omega
    exact (hneq (hterm.symm.trans htarget)).elim
  · simp [hs]

end Bottcher

namespace Bottcher
open Polynomial Filter

/-- At exact weight `W`, the support top slice has exactly the same coefficient as the original
polynomial. -/
lemma coeff_weightedSupportTopSlice_of_weight_eq (R : Polynomial (Polynomial ℂ)) {W i j : ℕ}
    (hij : i + 2 * j = W) :
    ((weightedSupportTopSlice R W).coeff j).coeff i = (R.coeff j).coeff i := by
  classical
  by_cases hj : j ∈ R.support
  · by_cases hi : i ∈ (R.coeff j).support
    · rw [coeff_coeff_weightedSupportTopSlice_self R W hj hi, hij]
      simp
    · have hcoeff : (R.coeff j).coeff i = 0 := Polynomial.notMem_support_iff.mp hi
      rw [hcoeff]
      rw [weightedSupportTopSlice_eq_topSubtype, coeff_coeff_weightedHomogeneousPoly]
      apply Finset.sum_eq_zero
      intro s _
      by_cases hmatch : (s.1.2 : ℕ) = i ∧ (s.1.1 : ℕ) = j
      · exfalso
        exact hi (by simpa [hmatch.1, hmatch.2] using s.1.2.property)
      · simp [hmatch]
  · have hcoeffOuter : R.coeff j = 0 := Polynomial.notMem_support_iff.mp hj
    rw [hcoeffOuter]
    simp only [Polynomial.coeff_zero]
    rw [weightedSupportTopSlice_eq_topSubtype, coeff_coeff_weightedHomogeneousPoly]
    apply Finset.sum_eq_zero
    intro s _
    by_cases hmatch : (s.1.2 : ℕ) = i ∧ (s.1.1 : ℕ) = j
    · exfalso
      exact hj (by simpa [hmatch.2] using s.1.1.property)
    · simp [hmatch]

end Bottcher

namespace Bottcher
open Polynomial Filter

lemma quadraticRelationFactor_eq_zero_sub_const (d : ℂ) :
    quadraticRelationFactor d = quadraticRelationFactor 0 - Polynomial.C (Polynomial.C d) := by
  rw [quadraticRelationFactor]
  change (Polynomial.X : Polynomial (Polynomial ℂ)) - Polynomial.C ((Polynomial.X : Polynomial ℂ) ^ 2 + Polynomial.C d) =
    ((Polynomial.X : Polynomial (Polynomial ℂ)) - Polynomial.C ((Polynomial.X : Polynomial ℂ) ^ 2 + Polynomial.C 0)) - Polynomial.C (Polynomial.C d)
  simp only [Polynomial.C_0, add_zero, Polynomial.C_add]
  abel

/-- Subtracting the shifted explicit top quotient kills the current support top slice.  The unshifted
part cancels `weightedSupportTopSlice R W`; the extra constant shift is invisible at weight `W` because
the quotient has weight `W-2`. -/
lemma weightedSupportTopSlice_shifted_topQuotient_remainder_zero
    (R : Polynomial (Polynomial ℂ)) {W : ℕ} (d : ℂ) (hW : 2 ≤ W)
    (hsum : ∑ j ∈ R.support, ∑ i ∈ (R.coeff j).support,
      (if i + 2 * j = W then (R.coeff j).coeff i else 0) = 0) :
    weightedSupportTopSlice
      (R - quadraticRelationFactor d * weightedSupportTopQuotient R W) W = 0 := by
  classical
  let Q := weightedSupportTopQuotient R W
  have hprod : quadraticRelationFactor 0 * Q = weightedSupportTopSlice R W := by
    simpa [Q] using quadraticRelationFactor_mul_weightedSupportTopQuotient R hsum
  apply weightedSupportTopSlice_eq_zero_of_coeff_eq_zero
  intro j i hij
  have hprodCoeff := congrArg (fun P : Polynomial (Polynomial ℂ) => (P.coeff j).coeff i) hprod
  have htopCoeff := coeff_weightedSupportTopSlice_of_weight_eq R hij
  have hQzero := coeff_weightedSupportTopQuotient_eq_zero_of_weight_eq R hW hij
  change ((R - quadraticRelationFactor d * Q).coeff j).coeff i = 0
  rw [quadraticRelationFactor_eq_zero_sub_const]
  rw [sub_mul]
  simp only [Polynomial.coeff_sub]
  rw [show ((quadraticRelationFactor 0 * Q).coeff j).coeff i = (R.coeff j).coeff i by
    simpa using hprodCoeff.trans htopCoeff]
  rw [show ((Polynomial.C (Polynomial.C d) * Q).coeff j).coeff i = d * (Q.coeff j).coeff i by
    rw [Polynomial.coeff_C_mul]
    simp]
  rw [show (Q.coeff j).coeff i = 0 by simpa [Q] using hQzero]
  ring

end Bottcher

namespace Bottcher
open Polynomial Filter

/-- From an exact transported relation, construct the explicit shifted top quotient and a remainder whose
current support top slice is zero. This is the concrete finite-algebra descent constructor. -/
theorem exists_shifted_topQuotient_remainder_zero_of_transported_relation
    {c₁ c₂ : ℂ} {Rfar R' : ℝ} (R : Polynomial (Polynomial ℂ)) {W : ℕ}
    (hW : 2 ≤ W)
    (hweight : weightedSupportBelow R W)
    (hrel : Set.EqOn
      (fun z => R.eval₂ (Polynomial.evalRingHom (bottcherCoord c₁ z))
        (bottcherCoord c₁ (quadratic c₂ z))) (fun _ => (0 : ℂ))
      {z : ℂ | Rfar < ‖z‖ ∧ R' < ‖bottcherCoord c₁ z‖}) :
    ∃ R₁ Q : Polynomial (Polynomial ℂ),
      R = R₁ + quadraticRelationFactor (c₂ - c₁) * Q ∧
      Q = weightedSupportTopQuotient R W ∧
      weightedSupportTopSlice R₁ W = 0 := by
  classical
  let Q := weightedSupportTopQuotient R W
  let R₁ := R - quadraticRelationFactor (c₂ - c₁) * Q
  have hsum : ∑ j ∈ R.support, ∑ i ∈ (R.coeff j).support,
      (if i + 2 * j = W then (R.coeff j).coeff i else 0) = 0 := by
    refine weighted_support_top_zero_of_transported_pullback_relation_with_scaled_tail
      (c₁ := c₁) (c₂ := c₂) (Rfar := Rfar) (R' := R') (R := R) (W := W)
      (Tail := fun _ => (0 : ℂ)) hweight ?_ ?_
    · simp
    · intro z hz
      simpa using hrel hz
  refine ⟨R₁, Q, ?_, rfl, ?_⟩
  · dsimp [R₁]
    abel
  · dsimp [R₁, Q]
    exact weightedSupportTopSlice_shifted_topQuotient_remainder_zero R (c₂ - c₁) hW hsum

end Bottcher

namespace Bottcher
open Polynomial Filter

/-- A support weight bound forces all coefficients above that weight to vanish. -/
lemma coeff_eq_zero_of_weightedSupportBelow (R : Polynomial (Polynomial ℂ)) {W i j : ℕ}
    (hbelow : weightedSupportBelow R W) (hlt : W < i + 2 * j) :
    (R.coeff j).coeff i = 0 := by
  by_contra hne
  have hi : i ∈ (R.coeff j).support := Polynomial.mem_support_iff.mpr hne
  have hj : j ∈ R.support := by
    refine Polynomial.mem_support_iff.mpr ?_
    intro hz
    rw [hz] at hne
    exact hne rfl
  have hle := hbelow j hj i hi
  omega

/-- Coefficient vanishing above weight `W` gives the support weight bound. -/
lemma weightedSupportBelow_of_coeff_eq_zero_gt (R : Polynomial (Polynomial ℂ)) {W : ℕ}
    (hzero : ∀ j i : ℕ, W < i + 2 * j → (R.coeff j).coeff i = 0) :
    weightedSupportBelow R W := by
  intro j _ i hi
  by_contra hnot
  have hlt : W < i + 2 * j := Nat.lt_of_not_ge hnot
  have hz := hzero j i hlt
  exact (Polynomial.mem_support_iff.mp hi) hz

/-- The explicit support top quotient has no coefficient above weight `W-2`. -/
lemma coeff_weightedSupportTopQuotient_eq_zero_of_weight_gt
    (R : Polynomial (Polynomial ℂ)) {W i j : ℕ} (hlt : W - 2 < i + 2 * j) :
    ((weightedSupportTopQuotient R W).coeff j).coeff i = 0 := by
  classical
  rw [weightedSupportTopQuotient, weightedHomogeneousParabolaQuotient_eq_sigma,
    coeff_coeff_weightedHomogeneousPoly]
  apply Finset.sum_eq_zero
  intro s _
  by_cases hs :
      ((s.1.1.2 : ℕ) + 2 * (s.2 : ℕ) = i ∧
        (s.1.1.1 : ℕ) - 1 - (s.2 : ℕ) = j)
  · have hterm := weightedHomogeneousParabolaQuotient_sigma_weight
      (ι := {s : weightedSupportIndex R // (s.2 : ℕ) + 2 * (s.1 : ℕ) = W})
      (I := fun s => (s.1.2 : ℕ))
      (J := fun s => (s.1.1 : ℕ))
      (W := W)
      (fun s => s.property) s
    have htarget : ((s.1.1.2 : ℕ) + 2 * (s.2 : ℕ)) +
        2 * ((s.1.1.1 : ℕ) - 1 - (s.2 : ℕ)) = i + 2 * j := by
      rw [hs.1, hs.2]
    omega
  · simp [hs]

/-- The explicit support top quotient is support-bounded by `W-2`. -/
lemma weightedSupportBelow_weightedSupportTopQuotient
    (R : Polynomial (Polynomial ℂ)) (W : ℕ) :
    weightedSupportBelow (weightedSupportTopQuotient R W) (W - 2) := by
  apply weightedSupportBelow_of_coeff_eq_zero_gt
  intro j i hlt
  exact coeff_weightedSupportTopQuotient_eq_zero_of_weight_gt R hlt

end Bottcher

namespace Bottcher
open Polynomial Filter

/-- The support top slice has no coefficient above weight `W`. -/
lemma coeff_weightedSupportTopSlice_eq_zero_of_weight_gt
    (R : Polynomial (Polynomial ℂ)) {W i j : ℕ} (hlt : W < i + 2 * j) :
    ((weightedSupportTopSlice R W).coeff j).coeff i = 0 := by
  classical
  rw [weightedSupportTopSlice_eq_topSubtype, coeff_coeff_weightedHomogeneousPoly]
  apply Finset.sum_eq_zero
  intro s _
  by_cases hs : ((s.1.2 : ℕ) = i ∧ (s.1.1 : ℕ) = j)
  · have htop : (s.1.2 : ℕ) + 2 * (s.1.1 : ℕ) = W := s.property
    omega
  · simp [hs]

/-- The shifted explicit top-quotient remainder is still support-bounded by the old weight `W`. -/
lemma weightedSupportBelow_shifted_topQuotient_remainder
    (R : Polynomial (Polynomial ℂ)) {W : ℕ} (d : ℂ)
    (hbelow : weightedSupportBelow R W)
    (hsum : ∑ j ∈ R.support, ∑ i ∈ (R.coeff j).support,
      (if i + 2 * j = W then (R.coeff j).coeff i else 0) = 0) :
    weightedSupportBelow (R - quadraticRelationFactor d * weightedSupportTopQuotient R W) W := by
  classical
  let Q := weightedSupportTopQuotient R W
  have hprod : quadraticRelationFactor 0 * Q = weightedSupportTopSlice R W := by
    simpa [Q] using quadraticRelationFactor_mul_weightedSupportTopQuotient R hsum
  apply weightedSupportBelow_of_coeff_eq_zero_gt
  intro j i hlt
  have hRzero := coeff_eq_zero_of_weightedSupportBelow R hbelow hlt
  have hprodCoeff := congrArg (fun P : Polynomial (Polynomial ℂ) => (P.coeff j).coeff i) hprod
  have htopZero := coeff_weightedSupportTopSlice_eq_zero_of_weight_gt R hlt
  have hQzero : (Q.coeff j).coeff i = 0 := by
    apply coeff_weightedSupportTopQuotient_eq_zero_of_weight_gt R
    omega
  change ((R - quadraticRelationFactor d * Q).coeff j).coeff i = 0
  rw [quadraticRelationFactor_eq_zero_sub_const]
  rw [sub_mul]
  simp only [Polynomial.coeff_sub]
  rw [hRzero]
  rw [show ((quadraticRelationFactor 0 * Q).coeff j).coeff i = 0 by
    simpa using hprodCoeff.trans htopZero]
  rw [show ((Polynomial.C (Polynomial.C d) * Q).coeff j).coeff i = 0 by
    rw [Polynomial.coeff_C_mul]
    rw [Polynomial.coeff_C_mul]
    rw [hQzero]
    simp]
  ring

end Bottcher

namespace Bottcher
open Polynomial Filter

/-- One explicit support-weight descent step from an exact transported relation.  It constructs the
shifted top quotient, proves the quotient has weight at most `W-2`, proves the remainder has dropped to
weight at most `W-1`, and proves the next top slice already has the top parabola factor. -/
theorem exists_shifted_topQuotient_descent_step_of_transported_relation
    {c₁ c₂ : ℂ} {Rfar R' : ℝ} (R : Polynomial (Polynomial ℂ)) {W : ℕ}
    (hW : 2 ≤ W)
    (hweight : weightedSupportBelow R W)
    (hrel : Set.EqOn
      (fun z => R.eval₂ (Polynomial.evalRingHom (bottcherCoord c₁ z))
        (bottcherCoord c₁ (quadratic c₂ z))) (fun _ => (0 : ℂ))
      {z : ℂ | Rfar < ‖z‖ ∧ R' < ‖bottcherCoord c₁ z‖}) :
    ∃ R₁ Q : Polynomial (Polynomial ℂ),
      R = R₁ + quadraticRelationFactor (c₂ - c₁) * Q ∧
      Q = weightedSupportTopQuotient R W ∧
      weightedSupportBelow Q (W - 2) ∧
      weightedSupportBelow R₁ (W - 1) ∧
      quadraticRelationFactor 0 ∣ weightedSupportTopSlice R₁ (W - 1) := by
  classical
  let Q := weightedSupportTopQuotient R W
  let R₁ := R - quadraticRelationFactor (c₂ - c₁) * Q
  have hsum : ∑ j ∈ R.support, ∑ i ∈ (R.coeff j).support,
      (if i + 2 * j = W then (R.coeff j).coeff i else 0) = 0 := by
    refine weighted_support_top_zero_of_transported_pullback_relation_with_scaled_tail
      (c₁ := c₁) (c₂ := c₂) (Rfar := Rfar) (R' := R') (R := R) (W := W)
      (Tail := fun _ => (0 : ℂ)) hweight ?_ ?_
    · simp
    · intro z hz
      simpa using hrel hz
  have hdecomp : R = R₁ + quadraticRelationFactor (c₂ - c₁) * Q := by
    dsimp [R₁]
    abel
  have htopzero : weightedSupportTopSlice R₁ W = 0 := by
    dsimp [R₁, Q]
    exact weightedSupportTopSlice_shifted_topQuotient_remainder_zero R (c₂ - c₁) hW hsum
  have hR₁W : weightedSupportBelow R₁ W := by
    dsimp [R₁, Q]
    exact weightedSupportBelow_shifted_topQuotient_remainder R (c₂ - c₁) hweight hsum
  have hQ : weightedSupportBelow Q (W - 2) := by
    dsimp [Q]
    exact weightedSupportBelow_weightedSupportTopQuotient R W
  have hle : W - 2 ≤ W - 1 := by omega
  have hstep := weightedSupport_descent_step_after_shifted_top_cancel
    (c₁ := c₁) (c₂ := c₂) (Rfar := Rfar) (R' := R')
    (R := R) (R₁ := R₁) (Q := Q) (W := W) (WQ := W - 2)
    hdecomp hR₁W htopzero hQ hle hrel
  refine ⟨R₁, Q, hdecomp, rfl, hQ, hstep.1, hstep.2⟩

end Bottcher

namespace Bottcher
open Polynomial Filter

/-- **Uniform fixed-inverse annulus transcendence bridge.**  The fixed inverse branch supplied by
`exists_uniform_cover_annulus_data_with_fixed_inverse_projection_and_image` gives, at each dyadic depth,
the exact projection-base transcendence witness for the pulled-back coordinate
`ξ ↦ φ_{c₂}(ψ₁(ξ^(2^(d+1))))`, provided the corresponding far high-value `z`-domain admits no nonzero
polynomial relation `q(z,φ_{c₂}(z))`.  This is the faithful root-coordinate bridge: it keeps the
annulus coordinate `ξ` and uses the projection-image transfer rather than pretending the annulus
projection is a left inverse to the iterate-coordinate cover. -/
theorem exists_uniform_cover_annulus_transcendental_pullback_of_no_far_high_relation
    (c₁ c₂ : ℂ) :
    ∃ (R B R' : ℝ) (hR'pos : 0 < R') (ψ₁ : ℂ → ℂ),
      (∀ d : ℕ, coverAnnulusRadiusIneqs c₁ c₂ (d + 1) R B R') ∧
      (∀ z, R < ‖z‖ → ψ₁ (bottcherCoord c₁ z) = z) ∧
      ∀ d : ℕ,
        (∀ q : Polynomial (Polynomial ℂ), q ≠ 0 →
          ¬ Set.EqOn (fun z => q.eval₂ (Polynomial.evalRingHom z) (bottcherCoord c₂ z)) 0
            {z : ℂ | R < ‖z‖ ∧ R' ^ (2 ^ (d + 1)) < ‖bottcherCoord c₁ z‖}) →
        ∃ (p₀ : analyticSubring {ξ : ℂ | R' < ‖ξ‖})
          (hp0 : (p₀ : Germ (𝓟 {ξ : ℂ | R' < ‖ξ‖}) ℂ) =
            ↑(fun ξ => ψ₁ (ξ ^ (2 ^ (d + 1)))))
          (hpInf : ((fun ξ => ψ₁ (ξ ^ (2 ^ (d + 1)))) '' {ξ : ℂ | R' < ‖ξ‖}).Infinite)
          (a₂ : analyticSubring {ξ : ℂ | R' < ‖ξ‖}),
            (a₂ : Germ (𝓟 {ξ : ℂ | R' < ‖ξ‖}) ℂ) =
              ↑(fun ξ => bottcherCoord c₂ (ψ₁ (ξ ^ (2 ^ (d + 1))))) ∧
            (letI : IsDomain (analyticSubring {ξ : ℂ | R' < ‖ξ‖}) :=
              isDomain_analyticSubring {ξ : ℂ | R' < ‖ξ‖} isOpen_exterior
                (isPreconnected_exterior hR'pos) (nonempty_exterior hR'pos)
             letI : Algebra (RatFunc ℂ) (meroField {ξ : ℂ | R' < ‖ξ‖}) :=
              (ratfuncToMeroVia p₀ hp0 hpInf isOpen_exterior
                (isPreconnected_exterior hR'pos) (nonempty_exterior hR'pos)).toAlgebra
             Transcendental (RatFunc ℂ)
              (algebraMap (analyticSubring {ξ : ℂ | R' < ‖ξ‖})
                (meroField {ξ : ℂ | R' < ‖ξ‖}) a₂)) := by
  obtain ⟨R, B, R', hR'pos, ψ₁, hall, hψleft, hdata⟩ :=
    exists_uniform_cover_annulus_data_with_fixed_inverse_projection_and_image c₁ c₂
  refine ⟨R, B, R', hR'pos, ψ₁, hall, hψleft, fun d hno => ?_⟩
  let U : Set ℂ := {ξ : ℂ | R' < ‖ξ‖}
  let N : ℕ := 2 ^ (d + 1)
  obtain ⟨hψan, hcont, _hproj, hpInf, _himage⟩ := hdata d
  obtain ⟨p₀, hp0⟩ := exists_projection_p0 (U := U) (ψ₁ := ψ₁) (n := d + 1) (by
    simpa [U] using hψan)
  obtain ⟨a₂, ha₂⟩ := exists_rotInvariant_a2 (c₂ := c₂) (U := U) (ψ₁ := ψ₁) (n := d + 1)
    (by simpa [U] using hψan) (by simpa [U] using hcont)
  have hNpos : 0 < N := by
    dsimp [N]
    exact pow_pos (by norm_num : (0 : ℕ) < 2) (d + 1)
  have htr := transcendental_pullback_bottcher_of_no_far_high_relation
    (c₁ := c₁) (c₂ := c₂) (ψ₁ := ψ₁) (R := R) (R' := R') (N := N)
    hR'pos hNpos hψleft (p₀ := p₀) (a := a₂) hp0
    (by simpa [U, N] using hpInf) (by simpa [U, N] using ha₂)
    (by simpa [N] using hno)
  refine ⟨by simpa [U] using p₀, by simpa [U, N] using hp0,
    by simpa [U, N] using hpInf, by simpa [U] using a₂,
    by simpa [U, N] using ha₂, ?_⟩
  simpa [U, N] using htr

end Bottcher

namespace Bottcher
open Polynomial Filter

/-- **Far-field no-relation criterion with pointwise nonparabola instead of extension.**  The general
exact-division criterion needs an extension hypothesis from the non-parabola locus back to the full
far-field carrier.  If the transported quadratic defect is pointwise nonzero on that carrier, the
non-parabola locus is the whole carrier, so the extension hypothesis is automatic. -/
theorem no_relation_of_far_bottcher_exact_division_weightedSupport_quotient_descent_nonparabola
    {c₁ c₂ : ℂ} {Rfar R' : ℝ}
    (hquot : ∀ R : Polynomial (Polynomial ℂ), R ≠ 0 →
      Set.EqOn
        (fun z => R.eval₂ (Polynomial.evalRingHom (bottcherCoord c₁ z))
          (bottcherCoord c₁ (quadratic c₂ z))) (fun _ => (0 : ℂ))
        {z : ℂ | Rfar < ‖z‖ ∧ R' < ‖bottcherCoord c₁ z‖} →
      ∃ Q : Polynomial (Polynomial ℂ), ∃ WQ : ℕ,
        R = Polynomial.C (R.eval (Polynomial.X ^ 2 + Polynomial.C (c₂ - c₁))) +
            quadraticRelationFactor (c₂ - c₁) * Q ∧
          weightedSupportBelow Q WQ ∧
          WQ ≤ (R.eval (Polynomial.X ^ 2 + Polynomial.C (c₂ - c₁))).natDegree + 1)
    (hne : ∀ z ∈ {z : ℂ | Rfar < ‖z‖ ∧ R' < ‖bottcherCoord c₁ z‖},
      bottcherCoord c₁ (quadratic c₂ z) ≠ (bottcherCoord c₁ z) ^ 2 + (c₂ - c₁)) :
    ∀ R : Polynomial (Polynomial ℂ), R ≠ 0 →
      ¬ Set.EqOn
        (fun z => R.eval₂ (Polynomial.evalRingHom (bottcherCoord c₁ z))
          (bottcherCoord c₁ (quadratic c₂ z))) (fun _ => (0 : ℂ))
        {z : ℂ | Rfar < ‖z‖ ∧ R' < ‖bottcherCoord c₁ z‖} := by
  refine no_relation_of_far_bottcher_exact_division_weightedSupport_quotient_descent
    (c₁ := c₁) (c₂ := c₂) (Rfar := Rfar) (R' := R') hquot ?_
  intro Q hQ z hz
  exact hQ ⟨hz, hne z hz⟩

end Bottcher

namespace Bottcher
open Polynomial Filter

/-- Support weight bounds are monotone in the bound. -/
theorem weightedSupportBelow_mono {R : Polynomial (Polynomial ℂ)} {W W' : ℕ}
    (h : weightedSupportBelow R W) (hle : W ≤ W') : weightedSupportBelow R W' := by
  intro j hj i hi
  exact le_trans (h j hj i hi) hle

/-- Every bivariate polynomial has a finite support-weight bound.  This support-indexed form avoids
rectangular degree boxes and is the bookkeeping input for finite weighted descent. -/
theorem exists_weightedSupportBelow (R : Polynomial (Polynomial ℂ)) :
    ∃ W : ℕ, weightedSupportBelow R W := by
  classical
  let inner : ℕ → ℕ := fun j => ((R.coeff j).support.sum fun i => i + 2 * j)
  let W : ℕ := R.support.sum inner
  refine ⟨W, ?_⟩
  intro j hj i hi
  have hinner : i + 2 * j ≤ inner j := by
    dsimp [inner]
    exact Finset.single_le_sum (s := (R.coeff j).support) (f := fun i => i + 2 * j)
      (fun _ _ => Nat.zero_le _) hi
  have houter : inner j ≤ W := by
    dsimp [W]
    exact Finset.single_le_sum (s := R.support) (f := inner)
      (fun _ _ => Nat.zero_le _) hj
  exact le_trans hinner houter

/-- Exact quadratic-substitution remainder with an explicit finite support-weight bound for the
quotient.  This packages `exists_quadratic_substitution_remainder` with the support-indexed finite bound
needed by the asymptotic descent lemmas. -/
theorem exists_quadratic_substitution_remainder_with_weightedSupportBound
    (R : Polynomial (Polynomial ℂ)) (d : ℂ) :
    ∃ Q : Polynomial (Polynomial ℂ), ∃ WQ : ℕ,
      R = Polynomial.C (R.eval (Polynomial.X ^ 2 + Polynomial.C d)) +
          quadraticRelationFactor d * Q ∧
        weightedSupportBelow Q WQ := by
  obtain ⟨Q, hQ⟩ := exists_quadratic_substitution_remainder R d
  obtain ⟨WQ, hWQ⟩ := exists_weightedSupportBelow Q
  exact ⟨Q, WQ, hQ, hWQ⟩

end Bottcher

namespace Bottcher

/-- **Cover-annulus radii with a caller-supplied lower bound for `R`.**
This is the bounded-below variant of `exists_cover_annulus_radii`: the far-field radius can be chosen
past any real threshold `L`, while preserving all annulus inequalities. -/
theorem exists_cover_annulus_radii_with_R_gt (c₁ c₂ : ℂ) (n : ℕ) (L : ℝ) :
    ∃ R B R' : ℝ, L < R ∧ coverAnnulusRadiusIneqs c₁ c₂ n R B R' := by
  let TR : ℝ := max L (max (2 * max 2 ‖c₁‖) (max (16 * ‖c₁‖) (max (max 2 ‖c₂‖) 1)))
  obtain ⟨NR, hNR⟩ := exists_nat_gt TR
  let R : ℝ := (NR : ℝ)
  have hLR : L < R := lt_of_le_of_lt (by dsimp [TR]; exact le_max_left _ _) hNR
  have hR1 : 2 * max 2 ‖c₁‖ < R := lt_of_le_of_lt (by
    dsimp [TR]
    exact le_trans (le_max_left _ _) (le_max_right _ _)) hNR
  have hR16 : 16 * ‖c₁‖ < R := lt_of_le_of_lt (by
    dsimp [TR]
    exact le_trans (le_max_left _ _)
      (le_trans (le_max_right _ _) (le_max_right _ _))) hNR
  have hRc₂ : max 2 ‖c₂‖ < R := lt_of_le_of_lt (by
    dsimp [TR]
    exact le_trans (le_max_left _ _)
      (le_trans (le_max_right _ _) (le_trans (le_max_right _ _) (le_max_right _ _)))) hNR
  have hRgt1 : 1 < R := lt_of_le_of_lt (by
    dsimp [TR]
    exact le_trans (le_max_right _ _)
      (le_trans (le_max_right _ _) (le_trans (le_max_right _ _) (le_max_right _ _)))) hNR
  have hR2 : 16 * ‖c₁‖ < R ^ 2 := by
    have hRsq : R < R ^ 2 := by
      simpa using (lt_self_pow₀ hRgt1 (by norm_num : (1 : ℕ) < 2))
    exact lt_trans hR16 hRsq
  let TB : ℝ := max (8 * max 2 ‖c₁‖) (max (2 * R) (max (768 * ‖c₁‖ + 64) 1))
  obtain ⟨NB, hNB⟩ := exists_nat_gt TB
  let B : ℝ := (NB : ℝ)
  have hB8 : 8 * max 2 ‖c₁‖ < B := lt_of_le_of_lt (by dsimp [TB]; exact le_max_left _ _) hNB
  have hBR : 2 * R < B := lt_of_le_of_lt (by dsimp [TB]; exact le_trans (le_max_left _ _) (le_max_right _ _)) hNB
  have hBbig : 768 * ‖c₁‖ + 64 < B := lt_of_le_of_lt (by
    dsimp [TB]
    exact le_trans (le_max_left _ _) (le_trans (le_max_right _ _) (le_max_right _ _))) hNB
  have hBgt1 : 1 < B := lt_of_le_of_lt (by
    dsimp [TB]
    exact le_trans (le_max_right _ _) (le_trans (le_max_right _ _) (le_max_right _ _))) hNB
  have hBpos : 0 < B := lt_trans zero_lt_one hBgt1
  have hBsq : 768 * ‖c₁‖ + 64 ≤ B ^ 2 := by
    have hBs : B < B ^ 2 := by
      simpa using (lt_self_pow₀ hBgt1 (by norm_num : (1 : ℕ) < 2))
    exact le_of_lt (lt_trans hBbig hBs)
  let TRp : ℝ := max B 1
  obtain ⟨NRp, hNRp⟩ := exists_nat_gt TRp
  let R' : ℝ := (NRp : ℝ)
  have hBltR' : B < R' := lt_of_le_of_lt (by dsimp [TRp]; exact le_max_left _ _) hNRp
  have hR'gt1 : 1 < R' := lt_of_le_of_lt (by dsimp [TRp]; exact le_max_right _ _) hNRp
  have hR'pos : 0 < R' := lt_trans zero_lt_one hR'gt1
  have hR'B : B < R' ^ (2 ^ n) := by
    have hle : R' ≤ R' ^ (2 ^ n) :=
      le_self_pow₀ (le_of_lt hR'gt1) (pow_ne_zero n (by norm_num : (2 : ℕ) ≠ 0))
    exact lt_of_lt_of_le hBltR' hle
  exact ⟨R, B, R', hLR, hR1, hR2, hRc₂, hBsq, hB8, hBR, hBpos, hR'pos, hR'B⟩

/-- **Uniform dyadic cover-annulus radii with a caller-supplied lower bound for `R`.** -/
theorem exists_cover_annulus_radii_uniform_dyadic_with_R_gt (c₁ c₂ : ℂ) (L : ℝ) :
    ∃ R B R' : ℝ, L < R ∧ 1 < R' ∧
      ∀ d : ℕ, coverAnnulusRadiusIneqs c₁ c₂ (d + 1) R B R' := by
  obtain ⟨R, B, R0, hLR, hR1, hR2, hRc₂, hBsq, hB8, hBR, hBpos, hR0pos, hR0B⟩ :=
    exists_cover_annulus_radii_with_R_gt c₁ c₂ 1 L
  let R' : ℝ := max R0 1 + 1
  have hR'gt1 : 1 < R' := by
    dsimp [R']
    have hle : (1 : ℝ) ≤ max R0 1 := le_max_right _ _
    linarith
  have hR'pos : 0 < R' := lt_trans zero_lt_one hR'gt1
  have hR0leR' : R0 ≤ R' := by
    dsimp [R']
    have hle : R0 ≤ max R0 1 := le_max_left _ _
    linarith
  have hR0B2 : B < R0 ^ 2 := by
    simpa using hR0B
  have hR0sq_le_R'sq : R0 ^ 2 ≤ R' ^ 2 :=
    pow_le_pow_left₀ (le_of_lt hR0pos) hR0leR' 2
  refine ⟨R, B, R', hLR, hR'gt1, fun d => ?_⟩
  have htwole : 2 ≤ 2 ^ (d + 1) := by
    simpa using (Nat.pow_le_pow_right (n := 2) (by norm_num)
      (Nat.succ_le_succ (Nat.zero_le d)))
  have hR'pow : R' ^ 2 ≤ R' ^ (2 ^ (d + 1)) :=
    pow_le_pow_right₀ (le_of_lt hR'gt1) htwole
  have hBR' : B < R' ^ (2 ^ (d + 1)) :=
    lt_of_lt_of_le (lt_of_lt_of_le hR0B2 hR0sq_le_R'sq) hR'pow
  exact ⟨hR1, hR2, hRc₂, hBsq, hB8, hBR, hBpos, hR'pos, hBR'⟩

end Bottcher

namespace Bottcher

/-- **Uniform fixed-inverse annulus data with an explicit lower bound for `R`.**
This is the lower-bound variant of
`exists_uniform_cover_annulus_data_with_fixed_inverse_projection_and_image`: the far-field inverse
branch and projection-image facts are built with `R` chosen beyond an arbitrary threshold `L`. -/
theorem exists_uniform_cover_annulus_data_with_fixed_inverse_projection_and_image_with_R_gt
    (c₁ c₂ : ℂ) (L : ℝ) :
    ∃ (R B R' : ℝ) (_hR'pos : 0 < R') (ψ₁ : ℂ → ℂ),
      L < R ∧
      (∀ d : ℕ, coverAnnulusRadiusIneqs c₁ c₂ (d + 1) R B R') ∧
      (∀ z, R < ‖z‖ → ψ₁ (bottcherCoord c₁ z) = z) ∧
      ∀ d : ℕ,
        (∀ ξ ∈ {ξ : ℂ | R' < ‖ξ‖}, AnalyticAt ℂ ψ₁ (ξ ^ (2 ^ (d + 1)))) ∧
        (∀ ξ ∈ {ξ : ℂ | R' < ‖ξ‖}, ψ₁ (ξ ^ (2 ^ (d + 1))) ∈ escapeOpen c₂) ∧
        (∀ ξ ∈ {ξ : ℂ | R' < ‖ξ‖},
          bottcherCoord c₁ (ψ₁ (ξ ^ (2 ^ (d + 1)))) = ξ ^ (2 ^ (d + 1))) ∧
        ((fun ξ => ψ₁ (ξ ^ (2 ^ (d + 1)))) '' {ξ : ℂ | R' < ‖ξ‖}).Infinite ∧
        (∀ z, R < ‖z‖ → R' ^ (2 ^ (d + 1)) < ‖bottcherCoord c₁ z‖ →
          z ∈ (fun ξ => ψ₁ (ξ ^ (2 ^ (d + 1)))) '' {ξ : ℂ | R' < ‖ξ‖}) := by
  obtain ⟨R, B, R', hLR, hR'gt1, hall⟩ :=
    exists_cover_annulus_radii_uniform_dyadic_with_R_gt c₁ c₂ L
  have hR'pos : 0 < R' := lt_trans zero_lt_one hR'gt1
  obtain ⟨hR1, hR2, _hRc₂0, _hB_far10, _hB_far20, _hBR0, _hBpos0,
      _hR'pos0, _hR'B0⟩ := hall 0
  obtain ⟨ψ₁, hψleft, hψan, _hψright⟩ := exists_analytic_inverse_far (c := c₁) hR1 hR2
  refine ⟨R, B, R', hR'pos, ψ₁, hLR, hall, hψleft, fun d => ?_⟩
  obtain ⟨_hR1, _hR2, hRc₂, hB_far1, hB_far2, hBR, hBpos, _hR'pos, hR'B⟩ := hall d
  let n : ℕ := d + 1
  have hR'B_n : B < R' ^ (2 ^ n) := by simpa [n] using hR'B
  have key : ∀ ξ : ℂ, R' < ‖ξ‖ → ∃ z, R < ‖z‖ ∧ bottcherCoord c₁ z = ξ ^ (2 ^ n) := by
    intro ξ hξR'
    have hwnorm : ‖ξ ^ (2 ^ n)‖ = ‖ξ‖ ^ (2 ^ n) := by rw [norm_pow]
    have hwB : B < ‖ξ ^ (2 ^ n)‖ := by
      rw [hwnorm]
      exact lt_of_lt_of_le hR'B_n (pow_le_pow_left₀ (le_of_lt hR'pos) (le_of_lt hξR') (2 ^ n))
    have hwfar1 : 768 * ‖c₁‖ + 64 < ‖ξ ^ (2 ^ n)‖ ^ 2 :=
      lt_of_le_of_lt hB_far1 (by nlinarith [hBpos, hwB])
    have hwfar2 : 8 * max 2 ‖c₁‖ < ‖ξ ^ (2 ^ n)‖ := lt_trans hB_far2 hwB
    obtain ⟨z, hz, hbz⟩ := exists_far_preimage (c := c₁) hwfar1 hwfar2
    have hzR : R < ‖z‖ := by
      have h1 : B / 2 ≤ ‖z‖ := le_trans (by linarith [hwB]) hz
      linarith [hBR]
    exact ⟨z, hzR, hbz⟩
  have hψan' : ∀ ξ ∈ {ξ : ℂ | R' < ‖ξ‖}, AnalyticAt ℂ ψ₁ (ξ ^ (2 ^ n)) := by
    intro ξ hξ
    obtain ⟨z, hzR, hbz⟩ := key ξ hξ
    rw [← hbz]
    exact hψan z hzR
  have hcont' : ∀ ξ ∈ {ξ : ℂ | R' < ‖ξ‖}, ψ₁ (ξ ^ (2 ^ n)) ∈ escapeOpen c₂ := by
    intro ξ hξ
    obtain ⟨z, hzR, hbz⟩ := key ξ hξ
    have hψw : ψ₁ (ξ ^ (2 ^ n)) = z := by
      rw [← hbz]
      exact hψleft z hzR
    rw [hψw]
    show max 2 ‖c₂‖ < ‖z‖
    exact lt_trans hRc₂ hzR
  have hproj : ∀ ξ ∈ {ξ : ℂ | R' < ‖ξ‖},
      bottcherCoord c₁ (ψ₁ (ξ ^ (2 ^ n))) = ξ ^ (2 ^ n) := by
    intro ξ hξ
    obtain ⟨z, hzR, hbz⟩ := key ξ hξ
    have hψw : ψ₁ (ξ ^ (2 ^ n)) = z := by
      rw [← hbz]
      exact hψleft z hzR
    rw [hψw]
    exact hbz
  have hpInf : ((fun ξ => ψ₁ (ξ ^ (2 ^ n))) '' {ξ : ℂ | R' < ‖ξ‖}).Infinite :=
    projection_image_infinite_exterior hR'pos hproj
  have himage : ∀ z, R < ‖z‖ → R' ^ (2 ^ n) < ‖bottcherCoord c₁ z‖ →
      z ∈ (fun ξ => ψ₁ (ξ ^ (2 ^ n))) '' {ξ : ℂ | R' < ‖ξ‖} := by
    intro z hzR hzval
    exact mem_projection_image_of_far_bottcher_value
      (c₁ := c₁) (ψ₁ := ψ₁) (R := R) (R' := R') (N := 2 ^ n)
      (pow_pos (by norm_num : (0 : ℕ) < 2) n) hψleft hzR hzval
  exact ⟨by simpa [n] using hψan', by simpa [n] using hcont', by simpa [n] using hproj,
    by simpa [n] using hpInf, by simpa [n] using himage⟩

end Bottcher

namespace Bottcher

/-- **The far high-value Böttcher set is nonempty.**
This is the nonempty form of `eventually_real_mem_bottcher_pullback_far`: the positive real ray is
eventually far in both source norm and Böttcher-value norm. -/
theorem far_high_bottcher_value_nonempty (c : ℂ) (Rfar Λ : ℝ) :
    ({z : ℂ | Rfar < ‖z‖ ∧ Λ < ‖bottcherCoord c z‖}).Nonempty := by
  obtain ⟨T, hT⟩ := eventually_atTop.mp (eventually_real_mem_bottcher_pullback_far c Rfar Λ)
  let t : ℝ := max T 0
  refine ⟨(t : ℂ), ?_⟩
  have htT : T ≤ t := by dsimp [t]; exact le_max_left _ _
  exact hT t htT

/-- **The far high-value Böttcher set is infinite.**
A tail of the positive real ray lies in the set, and real points on that tail are injectively indexed
by `ℕ`. -/
theorem far_high_bottcher_value_infinite (c : ℂ) (Rfar Λ : ℝ) :
    ({z : ℂ | Rfar < ‖z‖ ∧ Λ < ‖bottcherCoord c z‖}).Infinite := by
  obtain ⟨T, hT⟩ := eventually_atTop.mp (eventually_real_mem_bottcher_pullback_far c Rfar Λ)
  let M : ℝ := max T 0
  refine Set.infinite_of_injective_forall_mem
    (f := fun k : ℕ => ((M + (k : ℝ) : ℝ) : ℂ)) ?_ ?_
  · intro a b hab
    have hreal : M + (a : ℝ) = M + (b : ℝ) := Complex.ofReal_inj.mp hab
    exact Nat.cast_injective (show (a : ℝ) = (b : ℝ) by linarith)
  · intro k
    have hge : T ≤ M + (k : ℝ) := by
      have hTM : T ≤ M := by dsimp [M]; exact le_max_left _ _
      have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
      linarith
    exact hT (M + (k : ℝ)) hge

end Bottcher

namespace Bottcher

/-- **Far inverse values land back in the far source exterior.**
If a value `w` lies beyond the dyadic Böttcher-value threshold, the fixed far inverse is a source
point beyond `R` and projects back to `w`. -/
theorem far_inverse_maps_value_exterior_to_far_high
    {c : ℂ} {ψ : ℂ → ℂ} {R B R' : ℝ} {N : ℕ}
    (hNpos : 0 < N)
    (hψleft : ∀ z, R < ‖z‖ → ψ (bottcherCoord c z) = z)
    (hB_far1 : 768 * ‖c‖ + 64 ≤ B ^ 2) (hB_far2 : 8 * max 2 ‖c‖ < B)
    (hBR : 2 * R < B) (hBpos : 0 < B)
    (hR'B : B < R' ^ N) :
    ∀ w : ℂ, R' ^ N < ‖w‖ → R < ‖ψ w‖ ∧ bottcherCoord c (ψ w) = w := by
  intro w hw
  obtain ⟨ξ, hξpow⟩ := IsAlgClosed.exists_pow_nat_eq w hNpos
  have hξann : R' < ‖ξ‖ := by
    by_contra hle
    push Not at hle
    have hpow_le : ‖ξ‖ ^ N ≤ R' ^ N := pow_le_pow_left₀ (norm_nonneg ξ) hle N
    have hval_le : ‖w‖ ≤ R' ^ N := by
      rw [← hξpow, norm_pow]
      exact hpow_le
    exact not_lt_of_ge hval_le hw
  have hwB : B < ‖w‖ := lt_trans hR'B hw
  have hwfar1 : 768 * ‖c‖ + 64 < ‖w‖ ^ 2 :=
    lt_of_le_of_lt hB_far1 (by nlinarith [hBpos, hwB])
  have hwfar2 : 8 * max 2 ‖c‖ < ‖w‖ := lt_trans hB_far2 hwB
  obtain ⟨z, hzhalf, hbz⟩ := exists_far_preimage (c := c) (w := w) hwfar1 hwfar2
  have hzR : R < ‖z‖ := by
    have hBhalf : B / 2 < ‖w‖ / 2 := by linarith
    exact lt_of_lt_of_le (lt_of_lt_of_le (by linarith [hBR]) (le_of_lt hBhalf)) hzhalf
  have hψw : ψ w = z := by
    rw [← hbz]
    exact hψleft z hzR
  rw [hψw]
  exact ⟨hzR, hbz⟩

/-- **The far high-value Böttcher set is preconnected from the fixed inverse.**
It is the continuous image of the connected exterior under the inverse branch, using the exact
projection identity on the far value exterior. -/
theorem isPreconnected_far_high_bottcher_value_of_inverse
    {c : ℂ} {ψ : ℂ → ℂ} {R R' : ℝ} {N : ℕ}
    (hR'pos : 0 < R') (hNpos : 0 < N)
    (hψleft : ∀ z, R < ‖z‖ → ψ (bottcherCoord c z) = z)
    (hψan : ∀ ξ ∈ {ξ : ℂ | R' < ‖ξ‖}, AnalyticAt ℂ ψ (ξ ^ N))
    (hpre : ∀ w : ℂ, R' ^ N < ‖w‖ → R < ‖ψ w‖ ∧ bottcherCoord c (ψ w) = w) :
    IsPreconnected {z : ℂ | R < ‖z‖ ∧ R' ^ N < ‖bottcherCoord c z‖} := by
  let V : Set ℂ := {w : ℂ | R' ^ N < ‖w‖}
  have hVpre : IsPreconnected V := isPreconnected_exterior (pow_pos hR'pos N)
  have hψcont : ContinuousOn ψ V := by
    intro w hw
    obtain ⟨ξ, hξpow⟩ := IsAlgClosed.exists_pow_nat_eq w hNpos
    have hξann : R' < ‖ξ‖ := by
      by_contra hle
      push Not at hle
      have hpow_le : ‖ξ‖ ^ N ≤ R' ^ N := pow_le_pow_left₀ (norm_nonneg ξ) hle N
      have hval_le : ‖w‖ ≤ R' ^ N := by
        rw [← hξpow, norm_pow]
        exact hpow_le
      exact not_lt_of_ge hval_le hw
    simpa [hξpow] using (hψan ξ hξann).continuousAt.continuousWithinAt
  have himage : ψ '' V = {z : ℂ | R < ‖z‖ ∧ R' ^ N < ‖bottcherCoord c z‖} := by
    ext z
    constructor
    · rintro ⟨w, hw, rfl⟩
      exact ⟨(hpre w hw).1, by rw [(hpre w hw).2]; exact hw⟩
    · intro hz
      refine ⟨bottcherCoord c z, hz.2, ?_⟩
      exact hψleft z hz.1
  rw [← himage]
  exact hVpre.image ψ hψcont

end Bottcher

namespace Bottcher

/-- **Radius-package form of far high-value preconnectedness.**
For a fixed inverse branch analytic on the exterior annulus at level `2 ^ n`, the annulus radius
inequalities make the far high-value Böttcher set preconnected. -/
theorem isPreconnected_far_high_bottcher_value_of_coverAnnulusRadiusIneqs
    {c₁ c₂ : ℂ} {n : ℕ} {R B R' : ℝ} {ψ₁ : ℂ → ℂ}
    (h : coverAnnulusRadiusIneqs c₁ c₂ n R B R')
    (hψleft : ∀ z, R < ‖z‖ → ψ₁ (bottcherCoord c₁ z) = z)
    (hψan : ∀ ξ ∈ {ξ : ℂ | R' < ‖ξ‖}, AnalyticAt ℂ ψ₁ (ξ ^ (2 ^ n))) :
    IsPreconnected {z : ℂ | R < ‖z‖ ∧ R' ^ (2 ^ n) < ‖bottcherCoord c₁ z‖} := by
  obtain ⟨_hR1, _hR2, _hRc₂, hB_far1, hB_far2, hBR, hBpos, hR'pos, hR'B⟩ := h
  have hNpos : 0 < 2 ^ n := pow_pos (by norm_num : (0 : ℕ) < 2) n
  have hpre : ∀ w : ℂ, R' ^ (2 ^ n) < ‖w‖ →
      R < ‖ψ₁ w‖ ∧ bottcherCoord c₁ (ψ₁ w) = w :=
    far_inverse_maps_value_exterior_to_far_high
      (c := c₁) (ψ := ψ₁) (R := R) (B := B) (R' := R') (N := 2 ^ n)
      hNpos hψleft hB_far1 hB_far2 hBR hBpos hR'B
  exact isPreconnected_far_high_bottcher_value_of_inverse
    (c := c₁) (ψ := ψ₁) (R := R) (R' := R') (N := 2 ^ n)
    hR'pos hNpos hψleft hψan hpre

end Bottcher
