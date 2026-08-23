import GaloisForLFunctions.RHTower.ReflectedGammaQuartetMultiplicity

open Complex

namespace RHTower

noncomputable section

/-- The reflected-Gamma/Cosh relocation family in the paper's uncentered `s` coordinate. -/
def transverseRelocationCarrier (beta a : ℝ) (s : ℂ) : ℂ :=
  reflectedGammaQuartetCarrier beta a (s - (1 / 2 : ℂ))

/-- Every uncentered transverse-relocation carrier is entire. -/
theorem transverseRelocationCarrier_analyticOnNhd (beta a : ℝ) :
    AnalyticOnNhd ℂ (transverseRelocationCarrier beta a) Set.univ := by
  intro s _
  apply (reflectedGammaQuartetCarrier_analyticOnNhd beta a).comp_sub (1 / 2 : ℂ)
  refine ⟨s - (1 / 2 : ℂ), by simp, 1 / 2, by simp, ?_⟩
  ring

/-- The uncentered carrier has exact functional equation `F (1 - s) = F s`. -/
theorem transverseRelocationCarrier_one_sub (beta a : ℝ) (s : ℂ) :
    transverseRelocationCarrier beta a (1 - s) = transverseRelocationCarrier beta a s := by
  unfold transverseRelocationCarrier
  rw [show 1 - s - (1 / 2 : ℂ) = -(s - (1 / 2 : ℂ)) by ring,
    reflectedGammaQuartetCarrier_neg]

/-- The uncentered carrier satisfies Schwarz reflection. -/
theorem transverseRelocationCarrier_conj (beta a : ℝ) (s : ℂ) :
    transverseRelocationCarrier beta a (starRingEnd ℂ s) =
      starRingEnd ℂ (transverseRelocationCarrier beta a s) := by
  calc
    transverseRelocationCarrier beta a (starRingEnd ℂ s) =
        reflectedGammaQuartetCarrier beta a
          (starRingEnd ℂ (s - (1 / 2 : ℂ))) := by
            unfold transverseRelocationCarrier
            have hhalf : (starRingEnd ℂ) ((1 / 2 : ℂ)) = 1 / 2 := by
              have htwo : (starRingEnd ℂ) (2 : ℂ) = 2 := by
                rw [show (2 : ℂ) = ((2 : ℝ) : ℂ) by norm_num]
                exact Complex.conj_ofReal 2
              norm_num [map_div₀, htwo]
            rw [map_sub, hhalf]
    _ = starRingEnd ℂ (reflectedGammaQuartetCarrier beta a (s - (1 / 2 : ℂ))) :=
      reflectedGammaQuartetCarrier_conj beta a (s - (1 / 2 : ℂ))
    _ = starRingEnd ℂ (transverseRelocationCarrier beta a s) := rfl

/-- In the undisplaced family, every zero lies on the critical line. -/
theorem transverseRelocationCarrier_zero_re_eq_half
    {beta : ℝ} {s : ℂ} (hs : transverseRelocationCarrier beta 0 s = 0) :
    s.re = 1 / 2 := by
  have hcenter : (s - (1 / 2 : ℂ)).re = 0 :=
    reflectedGammaQuartetCarrier_zero_re_eq_zero hs
  have hre : s.re - 1 / 2 = 0 := by simpa using hcenter
  linarith

/-- A nonzero Cosh displacement creates a zero away from the critical line. -/
theorem transverseRelocationCarrier_offCritical_cosh_zero
    {beta a : ℝ} (ha : a ≠ 0) {z : ℂ} (hz : coshQuartetEnvelope a z = 0) :
    transverseRelocationCarrier beta a (z + (1 / 2 : ℂ)) = 0 ∧
      (z + (1 / 2 : ℂ)).re ≠ 1 / 2 := by
  have hfull := reflectedGammaQuartetCarrier_offCentral_cosh_zero (beta := beta) ha hz
  constructor
  · unfold transverseRelocationCarrier
    convert hfull.1 using 1
    ring_nf
  · intro h
    apply hfull.2
    have hre : z.re + 1 / 2 = 1 / 2 := by simpa using h
    linarith

/-- Transverse displacement preserves the complete support of zero ordinates. -/
theorem transverseRelocationCarrier_zero_im_iff_zero_im
    (beta a b y : ℝ) :
    (∃ s : ℂ, transverseRelocationCarrier beta a s = 0 ∧ s.im = y) ↔
      ∃ s : ℂ, transverseRelocationCarrier beta b s = 0 ∧ s.im = y := by
  constructor
  · rintro ⟨s, hs, him⟩
    obtain ⟨w, hw, hwim⟩ :=
      (reflectedGammaQuartetCarrier_zero_im_iff_zero_im beta a b y).mp
        ⟨s - (1 / 2 : ℂ), hs, by simpa using him⟩
    refine ⟨w + (1 / 2 : ℂ), ?_, ?_⟩
    · unfold transverseRelocationCarrier
      convert hw using 1
      ring_nf
    · simpa using hwim
  · rintro ⟨s, hs, him⟩
    obtain ⟨w, hw, hwim⟩ :=
      (reflectedGammaQuartetCarrier_zero_im_iff_zero_im beta b a y).mp
        ⟨s - (1 / 2 : ℂ), hs, by simpa using him⟩
    refine ⟨w + (1 / 2 : ℂ), ?_, ?_⟩
    · unfold transverseRelocationCarrier
      convert hw using 1
      ring_nf
    · simpa using hwim

end

end RHTower
