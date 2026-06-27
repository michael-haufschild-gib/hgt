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
