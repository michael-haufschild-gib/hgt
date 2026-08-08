import GaloisForLFunctions.HTGeometry.EndpointRemainderBound
import GaloisForLFunctions.HTGeometry.NormalisedEndpointIdentity
import GaloisForLFunctions.HTGeometry.RemainderRatioVanishing
import GaloisForLFunctions.HTGeometry.JetFreeNonvanishing
import GaloisForLFunctions.HTGeometry.EndpointJetSum

/-!
# A nonreal factorial slope forces formal hypertranscendence

Assembling the layers: a formal power series whose coefficients have a complex factorial slope
`aₙ = C Λⁿ Γ(1+αn)(1+O(e^{-cn}))` with `Re α > 0` and `Im α ≠ 0` satisfies no nonzero algebraic
differential equation with polynomial coefficients.
-/

open MvPolynomial PowerSeries Filter Topology

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {a : ℕ → ℂ} {α Λ Cc : ℂ} {c : ℝ}

/-- A cutoff beyond a prescribed offset with a prescribed linear gain. -/
theorem exists_cutoff {r : ℝ} (hr : 0 < r) (q₀ : ℕ) (D : ℝ) :
    ∃ R : ℕ, 2 ≤ R ∧ q₀ < R ∧ D < r * ((R : ℝ) - (q₀ : ℝ)) := by
  refine ⟨max 2 (q₀ + ⌈D / r⌉₊ + 2), le_max_left _ _, ?_, ?_⟩
  · have : q₀ + ⌈D / r⌉₊ + 2 ≤ max 2 (q₀ + ⌈D / r⌉₊ + 2) := le_max_right _ _
    omega
  · have hge : (q₀ : ℝ) + (⌈D / r⌉₊ : ℝ) + 2 ≤ ((max 2 (q₀ + ⌈D / r⌉₊ + 2) : ℕ) : ℝ) := by
      have hn : q₀ + ⌈D / r⌉₊ + 2 ≤ max 2 (q₀ + ⌈D / r⌉₊ + 2) := le_max_right _ _
      exact_mod_cast hn
    have hceil : D / r ≤ (⌈D / r⌉₊ : ℝ) := Nat.le_ceil _
    have hkey : D / r + 2 ≤ ((max 2 (q₀ + ⌈D / r⌉₊ + 2) : ℕ) : ℝ) - (q₀ : ℝ) := by linarith
    have hmul : r * (D / r + 2) ≤ r * (((max 2 (q₀ + ⌈D / r⌉₊ + 2) : ℕ) : ℝ) - (q₀ : ℝ)) :=
      mul_le_mul_of_nonneg_left hkey (le_of_lt hr)
    have hval : r * (D / r + 2) = D + 2 * r := by
      field_simp
    rw [hval] at hmul
    linarith

/-- The coefficient sequence is eventually nonzero. -/
theorem eventually_coeff_ne_zero (hyp : FactorialSlope a α Λ Cc c) :
    ∀ᶠ M : ℕ in atTop, a M ≠ 0 := by
  filter_upwards [eventually_slopeNorm_ne_zero hyp] with M hM
  intro hc
  refine hM ?_
  rw [slopeNorm, hc, zero_div]

/-- **The nonreal factorial slope theorem.**  A power series whose coefficients have a complex
factorial slope with nonzero imaginary part satisfies no nonzero algebraic differential equation
over the polynomials. -/
theorem aeval_formalJets_ne_zero (hyp : FactorialSlope a α Λ Cc c) (him : α.im ≠ 0)
    (m : ℕ) (P : MvPolynomial (Fin (m + 2)) ℂ) (hP : P ≠ 0) :
    aeval (formalJetsOver m (PowerSeries.mk a)) P ≠ 0 := by
  classical
  intro hzero
  set jets := formalJetsOver m (PowerSeries.mk a) with hjets
  have hgX : jets 0 = PowerSeries.X := formalJetsOver_zero m _
  have hr : (0 : ℝ) < α.re := hyp.re_pos
  have h𝔞 : 0 < slopeRatio α Λ := slopeRatio_pos hyp.lam_ne
  have hα : α ≠ 0 := by
    intro hc
    rw [hc] at hr
    simp at hr
  -- a minimal relation with a jet separant
  obtain ⟨Q, hQne, hQ0, j₀, hj₀ne, hj₀⟩ :=
    exists_annihilator_with_nonvanishing_jet_pderiv (0 : Fin (m + 2)) jets hgX ⟨P, hP, hzero⟩
  obtain ⟨j₁, hj₁⟩ : ∃ j₁ : Fin (m + 1), j₀ = j₁.succ :=
    ⟨j₀.pred hj₀ne, (Fin.succ_pred _ _).symm⟩
  -- a nonzero coefficient of the separant
  obtain ⟨q₀, hq₀⟩ : ∃ q : ℕ, PowerSeries.coeff q (aeval jets (pderiv j₀ Q)) ≠ 0 := by
    by_contra hc
    refine hj₀ (PowerSeries.ext fun q => ?_)
    have hq := not_exists.mp hc q
    simpa using hq
  -- the constants
  obtain ⟨B, cc, hccnn, hrem⟩ := exists_endpoint_remainder_bound hyp m Q
  obtain ⟨B', K, hK, henv⟩ := exists_slope_envelope hyp
  obtain ⟨R, hR2, hRq, hRbig⟩ := exists_cutoff hr q₀ ((B : ℝ) + (B' : ℝ))
  -- the chirp data
  set cf : Fin (m + 1) → ℕ → ℂ := fun j q =>
    PowerSeries.coeff q (aeval jets (pderiv j.succ Q)) with hcf
  set A : Fin (m + 1) × Fin R → ℂ := fun jq => endpointCoeff α Λ cf jq with hA
  set ρ : Fin (m + 1) × Fin R → ℝ := fun jq => endpointExponent α jq with hρ
  set kk : Fin (m + 1) × Fin R → ℤ := fun jq => endpointFreq jq with hkk
  set ε : Fin (m + 1) × Fin R → ℕ → ℂ := fun jq M =>
    slopeShiftDefect a α Λ (endpointShift jq) ((jq.1 : ℕ)) M with hε
  -- the distinguished pair has a nonzero coefficient
  set jq₀ : Fin (m + 1) × Fin R := (j₁, ⟨q₀, hRq⟩) with hjq₀
  have hAne : A jq₀ ≠ 0 := by
    simp only [hA, endpointCoeff]
    refine mul_ne_zero (mul_ne_zero ?_ (pow_ne_zero _ hyp.lam_ne)) ?_
    · rw [hcf, hjq₀]
      simpa [hj₁] using hq₀
    · rw [Complex.cpow_def_of_ne_zero hα]
      exact Complex.exp_ne_zero _
  -- the maximal exponent
  obtain ⟨smax, ⟨jqm, hjqmA, hjqmρ⟩, hmaxle⟩ :=
    exists_max_exponent_of_ne_zero (A := A) (ρ := ρ) (i₀ := jq₀) hAne
  have hsmaxbig : ((B : ℝ) + (B' : ℝ)) < smax := by
    have h1 : ρ jq₀ ≤ smax := hmaxle jq₀ hAne
    have h2 : α.re * ((endpointShift jq₀ : ℕ) : ℝ) ≤ ρ jq₀ := le_endpointExponent jq₀
    have h3 : R - q₀ ≤ endpointShift jq₀ := sub_le_endpointShift jq₀
    have h3R : ((R : ℝ) - (q₀ : ℝ)) ≤ ((endpointShift jq₀ : ℕ) : ℝ) := by
      have hcast : (((R - q₀ : ℕ)) : ℝ) = (R : ℝ) - (q₀ : ℝ) := by
        have : q₀ ≤ R := le_of_lt hRq
        push_cast [Nat.cast_sub this]
        ring
      have := (Nat.cast_le (α := ℝ)).mpr h3
      rw [hcast] at this
      exact this
    nlinarith
  refine hjqmA ?_
  refine chirp_coeff_eq_zero_of_tendsto (t := α.im) him (ρ := ρ) (k := kk) (A := A) (ε := ε)
    (smax := smax) ?_ hmaxle ?_ ?_ jqm hjqmρ
  · intro i₁ i₂ h₁ h₂ hk
    refine endpoint_pair_separation (α := α) i₁ i₂ ?_ hk
    show ρ i₁ = ρ i₂
    rw [h₁, h₂]
  · intro jq
    exact tendsto_slopeShiftDefect hyp (endpointShift jq) ((jq.1 : ℕ))
  · -- the normalised remainder vanishes
    have hEbound : ∀ M : ℕ, R ≤ M →
        ‖PowerSeries.coeff (M + R) (aeval (fun i => lowPart M (jets i)) Q)‖
          ≤ (cc * ((((2 ^ R * R.factorial : ℕ)) : ℝ)) ^ α.re * slopeRatio α Λ ^ R)
            * (((M + R : ℕ) : ℝ) + 1) ^ B * facEnv α.re (slopeRatio α Λ) M :=
      fun M hM => hrem R M hM
    have hc₁nn : (0 : ℝ)
        ≤ cc * ((((2 ^ R * R.factorial : ℕ)) : ℝ)) ^ α.re * slopeRatio α Λ ^ R := by
      have h1 : (0 : ℝ) ≤ ((((2 ^ R * R.factorial : ℕ)) : ℝ)) ^ α.re := by positivity
      positivity
    have hratio := tendsto_remainder_ratio (r := α.re) (𝔞 := slopeRatio α Λ) h𝔞
      (E := fun M => PowerSeries.coeff (M + R) (aeval (fun i => lowPart M (jets i)) Q))
      (A := fun M => ‖a M‖) (B := B) (B' := B') (R := R) hc₁nn hK hEbound
      (fun M hM => (henv M hM).2) (fun M => norm_nonneg _) hsmaxbig
    rw [tendsto_zero_iff_norm_tendsto_zero]
    refine squeeze_zero' (Eventually.of_forall fun M => norm_nonneg _) ?_ hratio
    filter_upwards [eventually_ge_atTop (max R 1), eventually_coeff_ne_zero hyp] with M hM haM
    have hRM : R ≤ M := le_trans (le_max_left _ _) hM
    have hM1 : 1 ≤ M := le_trans (le_max_right _ _) hM
    have hid := coeff_aeval_div_eq_chirp_sum hyp (m := m) (R := R) (M := M) hR2 hRM hM1 haM Q
    rw [hQ0, map_zero, zero_div, Nat.add_sub_cancel] at hid
    simp only [hA, hρ, hkk, hε]
    have hsum : (∑ jq : Fin (m + 1) × Fin R,
        chirpTerm α.im (endpointExponent α jq) (endpointFreq jq) (endpointCoeff α Λ cf jq)
          (Real.log M) * slopeShiftDefect a α Λ (endpointShift jq) ((jq.1 : ℕ)) M)
        = -(PowerSeries.coeff (M + R) (aeval (fun i => lowPart M (jets i)) Q) / a M) := by
      linear_combination -hid
    rw [hsum, norm_div, norm_neg, norm_div, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (Real.exp_pos _), div_div]

end

end GaloisForLFunctions.HTGeometry
