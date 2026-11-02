import GaloisForLFunctions.CohomologyOfWindowsOfSpecZ.TheWindowDatum
import GaloisForLFunctions.LatticeSectionTheory.WindowJumpCounts.SinglePrimeWindowJumpGraphAndObstructions

/-!
# Windows up to `log 2 + 1/50` carry at most one negative square

LST (`weilPair_ge_of_evenPoleMoment_zero_past_primeTwo`) proves that Weil's form is coercive on smooth
tests in `(−a, a)`, `2a ≤ log 2 + 1/50`, whose even pole moment `∫ F cosh(x/2)` vanishes. Read on
windows:

* **Coercivity on the cosh hyperplane** (`weilQuad_ge_of_coshOrthogonal`): a smooth window test of
  length `A < log 2 + 1/50` whose centred test has vanishing even pole moment has
  `Q(H) ≥ ‖H‖²/1000`.
* **At most one negative square** (`not_negative_plane`): no plane of smooth window tests of such a
  length is negative definite. The whole prime-free window, and the first-prime windows up to
  `log 2 + 1/50`, have window index at most one in the smooth class: the only possible negative
  direction is transverse to the cosh hyperplane, an even direction carrying the cosh pole moment.

* **The cosh capacity criterion** (`coshCapacity_criterion`): fix one smooth window test `e` with
  nonzero centred cosh moment. Then Weil's form is nonnegative on all smooth window tests of length
  `A` iff `Q(e) ≥ 0` and `B(h, e)² ≤ Q(h)Q(e)` for every `h` on the cosh hyperplane, where `B` is
  Weil's pairing and `Q` is coercive on the hyperplane. Positivity below `log 2 + 1/50` is the
  statement that the energy of one even direction dominates its coupling to a coercive hyperplane.

So below `log 2 + 1/50` positivity is a single scalar condition (the cosh capacity of one even
direction), and that direction is the open core of the prime-free window and of the beginning of
the first prime.
-/

noncomputable section

open MeasureTheory Set Filter Topology Zeta23

namespace GaloisForLFunctions.CohomologyOfWindowsOfSpecZ

open SpacingScaleHarmonicAnalysis ArithmeticCriticalityTheory

variable {A : ℝ} {H : ℝ → ℝ}

/-- The test of a window of length `A` centred at the origin, `u ↦ H(u − A/2)`. -/
def centred (A : ℝ) (H : ℝ → ℝ) : ℝ → ℝ := fun u => H (u - A / 2)

/-- The even pole moment of a centred combination is linear. -/
theorem evenPoleMoment_centred_comb {H₁ H₂ : ℝ → ℝ} (h₁ : IsWindowTest A H₁) (h₂ : IsWindowTest A H₂)
    (α β : ℝ) :
    evenPoleMoment (centred A fun u => α * H₁ u + β * H₂ u) =
      α * evenPoleMoment (centred A H₁) + β * evenPoleMoment (centred A H₂) := by
  have hc : Continuous fun x : ℝ => Real.cosh (x / 2) := by fun_prop
  have i₁ : Integrable fun x => centred A H₁ x * Real.cosh (x / 2) :=
    ((h₁.continuous.comp (continuous_sub_right _)).mul hc).integrable_of_hasCompactSupport
      ((h₁.hasCompactSupport.comp_homeomorph (Homeomorph.subRight (A / 2))).mul_right)
  have i₂ : Integrable fun x => centred A H₂ x * Real.cosh (x / 2) :=
    ((h₂.continuous.comp (continuous_sub_right _)).mul hc).integrable_of_hasCompactSupport
      ((h₂.hasCompactSupport.comp_homeomorph (Homeomorph.subRight (A / 2))).mul_right)
  unfold evenPoleMoment
  rw [← integral_const_mul, ← integral_const_mul, ← integral_add (i₁.const_mul α) (i₂.const_mul β)]
  congr 1; funext x; simp only [centred]; ring

/-- **Coercivity on the cosh hyperplane**: for `0 ≤ A < log 2 + 1/50`, a smooth window test whose
centred even pole moment vanishes has `Q(H) ≥ ‖H‖²/1000`. -/
theorem weilQuad_ge_of_coshOrthogonal (hA0 : 0 ≤ A) (hA : A < Real.log 2 + 1 / 50)
    (hH : IsWindowTest A H) (hsm : ContDiff ℝ (⊤ : ℕ∞) H)
    (hC : evenPoleMoment (centred A H) = 0) :
    (1 / 1000 : ℝ) * (∫ u, H u ^ 2) ≤ weilQuad H := by
  set a := (A + (Real.log 2 + 1 / 50)) / 4 with ha_def
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have ha0 : 0 < a := by rw [ha_def]; linarith
  have haA : A / 2 < a := by rw [ha_def]; linarith
  have h2a : 2 * a ≤ Real.log 2 + 1 / 50 := by rw [ha_def]; linarith
  have hGv : ∀ y, y ∉ Icc (-(A / 2)) (A / 2) → centred A H y = 0 := fun y hy => by
    refine hH.vanish _ fun hm => hy ⟨?_, ?_⟩ <;> linarith [hm.1, hm.2]
  have hGsm : ContDiff ℝ (⊤ : ℕ∞) (centred A H) := hsm.comp (contDiff_id.sub contDiff_const)
  have hGc : HasCompactSupport (centred A H) :=
    HasCompactSupport.intro (isCompact_Icc (a := -(A / 2)) (b := A / 2)) hGv
  have hts : tsupport (centred A H) ⊆ Ioo (-a) a := by
    have h1 : tsupport (centred A H) ⊆ Icc (-(A / 2)) (A / 2) := by
      refine closure_minimal (fun y hy => ?_) isClosed_Icc
      by_contra hn
      exact hy (hGv y hn)
    exact h1.trans fun y hy => ⟨by linarith [hy.1], by linarith [hy.2]⟩
  have h := LatticeSectionTheory.WindowJumpCounts.weilPair_ge_of_evenPoleMoment_zero_past_primeTwo
    hGsm hGc ha0 hts h2a hC
  have hQ : ArithmeticCastelnuovoSeveri.weilPair (centred A H) (centred A H) = weilQuad H := by
    show weilQuad (centred A H) = weilQuad H
    exact weilQuad_comp_sub H (A / 2)
  have hL : ∫ u, centred A H u ^ 2 = ∫ u, H u ^ 2 :=
    integral_sub_right_eq_self (fun u => H u ^ 2) (A / 2)
  rwa [hQ, hL] at h

/-- **At most one negative square**: for `0 ≤ A < log 2 + 1/50`, no plane spanned by two smooth
window tests is negative definite for Weil's form. -/
theorem not_negative_plane (hA0 : 0 ≤ A) (hA : A < Real.log 2 + 1 / 50) {H₁ H₂ : ℝ → ℝ}
    (h₁ : IsWindowTest A H₁) (h₂ : IsWindowTest A H₂) (s₁ : ContDiff ℝ (⊤ : ℕ∞) H₁)
    (s₂ : ContDiff ℝ (⊤ : ℕ∞) H₂) :
    ¬ ∀ α β : ℝ, (α, β) ≠ (0, 0) → weilQuad (fun u => α * H₁ u + β * H₂ u) < 0 := by
  intro hneg
  set ℓ₁ := evenPoleMoment (centred A H₁)
  set ℓ₂ := evenPoleMoment (centred A H₂)
  -- a nonzero combination on the cosh hyperplane
  obtain ⟨α, β, hne, hℓ⟩ : ∃ α β : ℝ, (α, β) ≠ (0, 0) ∧ α * ℓ₁ + β * ℓ₂ = 0 := by
    by_cases h0 : ℓ₁ = 0
    · exact ⟨1, 0, by simp, by rw [h0]; ring⟩
    · exact ⟨ℓ₂, -ℓ₁, fun h => h0 (by simpa using congrArg Prod.snd h), by ring⟩
  have hF : IsWindowTest A fun u => α * H₁ u + β * H₂ u :=
    ⟨(contDiff_const.mul h₁.contDiff).add (contDiff_const.mul h₂.contDiff), fun y hy => by
      rw [h₁.vanish y hy, h₂.vanish y hy]; ring⟩
  have hFs : ContDiff ℝ (⊤ : ℕ∞) fun u => α * H₁ u + β * H₂ u :=
    (contDiff_const.mul s₁).add (contDiff_const.mul s₂)
  have hC : evenPoleMoment (centred A fun u => α * H₁ u + β * H₂ u) = 0 := by
    rw [evenPoleMoment_centred_comb h₁ h₂]; exact hℓ
  have hpos := weilQuad_ge_of_coshOrthogonal hA0 hA hF hFs hC
  have hM : 0 ≤ ∫ u, (α * H₁ u + β * H₂ u) ^ 2 := integral_nonneg fun u => sq_nonneg _
  linarith [hneg α β hne]

/-! ### The cosh capacity criterion -/

/-- Weil's form along a line: `Q(h + te) = Q(h) + 2t B(h, e) + t² Q(e)`. -/
theorem weilQuad_add_smul {h e : ℝ → ℝ} (hh : h ∈ ArithmeticCastelnuovoSeveri.realTests)
    (he : e ∈ ArithmeticCastelnuovoSeveri.realTests) (t : ℝ) :
    weilQuad (fun u => h u + t * e u) = weilQuad h +
      2 * t * ArithmeticCastelnuovoSeveri.weilPair h e + t ^ 2 * weilQuad e := by
  have hte : t • e ∈ ArithmeticCastelnuovoSeveri.realTests :=
    ArithmeticCastelnuovoSeveri.realTests.smul_mem t he
  have hsum : h + t • e ∈ ArithmeticCastelnuovoSeveri.realTests :=
    ArithmeticCastelnuovoSeveri.realTests.add_mem hh hte
  have hfun : (fun u => h u + t * e u) = h + t • e := by
    funext u; simp [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  rw [hfun]
  show ArithmeticCastelnuovoSeveri.weilPair (h + t • e) (h + t • e) =
    ArithmeticCastelnuovoSeveri.weilPair h h + 2 * t * ArithmeticCastelnuovoSeveri.weilPair h e +
      t ^ 2 * ArithmeticCastelnuovoSeveri.weilPair e e
  rw [ArithmeticCastelnuovoSeveri.weilPair_add_left hh hte hsum,
    ArithmeticCastelnuovoSeveri.weilPair_smul_left,
    ArithmeticCastelnuovoSeveri.weilPair_comm h, ArithmeticCastelnuovoSeveri.weilPair_comm e,
    ArithmeticCastelnuovoSeveri.weilPair_add_left hh hte hh,
    ArithmeticCastelnuovoSeveri.weilPair_add_left hh hte he,
    ArithmeticCastelnuovoSeveri.weilPair_smul_left, ArithmeticCastelnuovoSeveri.weilPair_smul_left,
    ArithmeticCastelnuovoSeveri.weilPair_comm e h]
  ring

/-- **The cosh capacity criterion.** For `0 ≤ A < log 2 + 1/50` and a smooth window test `e` with
nonzero centred cosh moment, Weil's form is nonnegative on smooth window tests of length `A` iff
`Q(e) ≥ 0` and `B(h, e)² ≤ Q(h)Q(e)` for every smooth window test `h` on the cosh hyperplane. -/
theorem coshCapacity_criterion (hA0 : 0 ≤ A) (hA : A < Real.log 2 + 1 / 50) {e : ℝ → ℝ}
    (he : IsWindowTest A e) (hes : ContDiff ℝ (⊤ : ℕ∞) e)
    (hℓ : evenPoleMoment (centred A e) ≠ 0) :
    (∀ H : ℝ → ℝ, IsWindowTest A H → ContDiff ℝ (⊤ : ℕ∞) H → 0 ≤ weilQuad H) ↔
      0 ≤ weilQuad e ∧ ∀ h : ℝ → ℝ, IsWindowTest A h → ContDiff ℝ (⊤ : ℕ∞) h →
        evenPoleMoment (centred A h) = 0 →
          ArithmeticCastelnuovoSeveri.weilPair h e ^ 2 ≤ weilQuad h * weilQuad e := by
  have heT : e ∈ ArithmeticCastelnuovoSeveri.realTests := ⟨he.contDiff, he.hasCompactSupport⟩
  constructor
  · intro hpos
    refine ⟨hpos e he hes, fun h hh hhs _ => ?_⟩
    have hhT : h ∈ ArithmeticCastelnuovoSeveri.realTests := ⟨hh.contDiff, hh.hasCompactSupport⟩
    have hq : ∀ t : ℝ, 0 ≤ weilQuad e * (t * t) +
        2 * ArithmeticCastelnuovoSeveri.weilPair h e * t + weilQuad h := fun t => by
      have hwin : IsWindowTest A fun u => h u + t * e u :=
        ⟨hh.contDiff.add (contDiff_const.mul he.contDiff), fun y hy => by
          rw [hh.vanish y hy, he.vanish y hy]; ring⟩
      have := hpos _ hwin (hhs.add (contDiff_const.mul hes))
      rw [weilQuad_add_smul hhT heT t] at this
      linarith
    have hd := discrim_le_zero hq
    unfold discrim at hd
    nlinarith
  · rintro ⟨hQe, hcap⟩ H hH hHs
    set ℓe := evenPoleMoment (centred A e)
    set t := evenPoleMoment (centred A H) / ℓe
    -- the component of `H` on the cosh hyperplane
    set h : ℝ → ℝ := fun u => 1 * H u + (-t) * e u with hh_def
    have hh : IsWindowTest A h :=
      ⟨(contDiff_const.mul hH.contDiff).add (contDiff_const.mul he.contDiff), fun y hy => by
        simp only [hh_def]; rw [hH.vanish y hy, he.vanish y hy]; ring⟩
    have hhs : ContDiff ℝ (⊤ : ℕ∞) h := (contDiff_const.mul hHs).add (contDiff_const.mul hes)
    have hhC : evenPoleMoment (centred A h) = 0 := by
      have ht : t * evenPoleMoment (centred A e) = evenPoleMoment (centred A H) :=
        div_mul_cancel₀ _ hℓ
      rw [hh_def, evenPoleMoment_centred_comb hH he]
      linarith [ht]
    have hhT : h ∈ ArithmeticCastelnuovoSeveri.realTests := ⟨hh.contDiff, hh.hasCompactSupport⟩
    have hQh : 0 ≤ weilQuad h := by
      have := weilQuad_ge_of_coshOrthogonal hA0 hA hh hhs hhC
      have hM : 0 ≤ ∫ u, h u ^ 2 := integral_nonneg fun u => sq_nonneg _
      linarith
    have hH_eq : H = fun u => h u + t * e u := by
      funext u; simp only [hh_def]; ring
    have hc := hcap h hh hhs hhC
    rw [hH_eq, weilQuad_add_smul hhT heT t]
    set B := ArithmeticCastelnuovoSeveri.weilPair h e
    rcases hQe.lt_or_eq with hpos | hzero
    · have key : weilQuad e * (weilQuad h + 2 * t * B + t ^ 2 * weilQuad e) =
          (t * weilQuad e + B) ^ 2 + (weilQuad h * weilQuad e - B ^ 2) := by ring
      have : 0 ≤ weilQuad e * (weilQuad h + 2 * t * B + t ^ 2 * weilQuad e) := by
        rw [key]; nlinarith [sq_nonneg (t * weilQuad e + B)]
      exact nonneg_of_mul_nonneg_right (by linarith) hpos
    · rw [← hzero, mul_zero] at hc
      have hB : B = 0 := by nlinarith [sq_nonneg B]
      rw [hB, ← hzero]; nlinarith

end GaloisForLFunctions.CohomologyOfWindowsOfSpecZ
