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
    simpa using precompMeroEquiv_ratfuncToMeroVia_fix
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
