import GaloisForLFunctions.RHTower.XiGaussianCertifiedPhaseDecay
import GaloisForLFunctions.RHTower.XiGaussianCriticalBandRank
import GaloisForLFunctions.RHTower.XiCriticalGaussianMaxNodeFloor

/-!
# Testing the complete phase ceiling against the improved critical-node floor

At every order at least two, the largest selected distinct critical squared
node exceeds the certified phase gap. The resulting full-form estimate is
unconditional, but its phase ceiling eventually exceeds its positive floor.
This is a failure of this particular comparison, not a lower bound on actual
phase debt and not a negative witness for the Xi form.
-/

open scoped Real BigOperators
open Complex Filter Topology
noncomputable section

namespace RHTower

/-- The improved critical-node floor and whole-phase ceiling give a coefficient-uniform
comparison at every positive time. The actual selected node rate exceeds the phase gap. -/
theorem exists_xiHeatHankelForm_maxNode_certifiedPhase_comparison (n : ℕ) :
    ∃ c : ℝ, 0 < c ∧ ∃ L : ℝ, xiGaussianCertifiedPhaseGap < L ∧
      (∃ q : XiZeroCopy, (xiSpectralPoint q).im = 0 ∧ L = (xiSpectralPoint q).re ^ 2) ∧
      (∀ (a : ℕ → ℝ) (t : {t : ℝ // 0 < t}),
        c * Real.exp (-(L * (t : ℝ))) * (∑ j ∈ Finset.range (n + 2), a j ^ 2) ≤
          xiGaussianRealChannelEnergy
            (∑ j ∈ Finset.range (n + 2), Polynomial.C (a j) * Polynomial.X ^ j) t) ∧
      ∀ (a : ℕ → ℝ) (s : {s : ℝ // 0 < s})
        (t : {t : {t : ℝ // 0 < t} // (s : ℝ) ≤ (t : ℝ)}),
        (c * Real.exp (-(L * (t.1 : ℝ))) -
          Real.exp (-(((t.1 : ℝ) - (s : ℝ)) * xiGaussianCertifiedPhaseGap)) *
            xiGaussianCoefficientAnchorAt (n + 2) s) *
              (∑ j ∈ Finset.range (n + 2), a j ^ 2) ≤ xiHeatHankelForm (n + 2) a t.1 := by
  obtain ⟨γ, q, iMax, c, hc, hinj, hq, hmax, _, hfloor⟩ :=
    exists_xiGaussianRealChannel_maxNode_floor (n + 1)
  let i₀ : Fin (n + 2) := ⟨0, by omega⟩
  let i₁ : Fin (n + 2) := ⟨1, by omega⟩
  have hL : xiGaussianCertifiedPhaseGap < γ iMax ^ 2 := by
    by_contra h
    have hle := not_lt.mp h
    apply not_exists_two_criticalSquares_in_certifiedPhaseBand
    refine ⟨q i₀, q i₁, ?_, ?_, ?_, ?_, ?_⟩
    · rw [(hq i₀).2, Complex.ofReal_im]
    · rw [(hq i₁).2, Complex.ofReal_im]
    · rw [(hq i₀).2, (hq i₁).2, Complex.ofReal_re, Complex.ofReal_re]
      intro he
      have hi : i₀ = i₁ := by
        apply hinj
        change (γ i₀ : ℂ) ^ 2 = (γ i₁ : ℂ) ^ 2
        exact_mod_cast he
      have hval := congrArg Fin.val hi
      change (0 : ℕ) = 1 at hval
      exact Nat.zero_ne_one hval
    · rw [(hq i₀).2, Complex.ofReal_re]
      exact (hmax i₀).trans hle
    · rw [(hq i₁).2, Complex.ofReal_re]
      exact (hmax i₁).trans hle
  refine ⟨c, hc, γ iMax ^ 2, hL, ⟨q iMax, ?_, ?_⟩, hfloor, ?_⟩
  · rw [(hq iMax).2, Complex.ofReal_im]
  · rw [(hq iMax).2, Complex.ofReal_re]
  · intro a s t
    have hf := hfloor a t.1
    have hd := xiGaussianImaginaryChannel_le_certified_anchorAt (n + 2) a s t
    have he := xiGaussianTrace_eq_realChannel_sub_imaginary
      (∑ j ∈ Finset.range (n + 2), Polynomial.C (a j) * Polynomial.X ^ j) t.1
    rw [xiPolynomialGaussianHeatTraceReal_rangeSum t.1.property] at he
    nlinarith only [hf, hd, he]

/-- For any faster-decaying proposed floor, the certified whole-phase ceiling exceeds that
floor at arbitrarily late times. This theorem compares estimates, not actual channel signs. -/
theorem exists_certifiedPhaseCeiling_exceeds_faster_floor (n : ℕ)
    (c : {c : ℝ // 0 < c}) (L : {L : ℝ // xiGaussianCertifiedPhaseGap < L})
    (s : {s : ℝ // 0 < s}) (T : ℝ) :
    ∃ t : {t : {t : ℝ // 0 < t} // (s : ℝ) ≤ (t : ℝ)}, T < (t.1 : ℝ) ∧
      (c : ℝ) * Real.exp (-((L : ℝ) * (t.1 : ℝ))) <
        Real.exp (-(((t.1 : ℝ) - (s : ℝ)) * xiGaussianCertifiedPhaseGap)) *
          xiGaussianCoefficientAnchorAt (n + 1) s := by
  let C := xiGaussianCoefficientAnchorAt (n + 1) s
  let k := Real.exp ((s : ℝ) * xiGaussianCertifiedPhaseGap) * C
  have hC : 0 < C := xiGaussianCoefficientAnchorAt_pos n s
  have hk : 0 < k := mul_pos (Real.exp_pos _) hC
  have hrate : 0 < (L : ℝ) - xiGaussianCertifiedPhaseGap := sub_pos.mpr L.property
  have hlim : Tendsto (fun x : ℝ => Real.exp (-((L : ℝ) - xiGaussianCertifiedPhaseGap) * x))
      atTop (nhds 0) := by
    simpa only [Real.rpow_zero, one_mul] using
      tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 0
        ((L : ℝ) - xiGaussianCertifiedPhaseGap) hrate
  have hev := hlim.eventually (gt_mem_nhds (div_pos hk c.property))
  obtain ⟨x, hx, hxs, hxT⟩ :=
    (hev.and ((eventually_ge_atTop (s : ℝ)).and (eventually_gt_atTop T))).exists
  let t : {t : {t : ℝ // 0 < t} // (s : ℝ) ≤ (t : ℝ)} :=
    ⟨⟨x, s.property.trans_le hxs⟩, hxs⟩
  refine ⟨t, hxT, ?_⟩
  have hsmall : (c : ℝ) * Real.exp (-((L : ℝ) - xiGaussianCertifiedPhaseGap) * x) < k := by
    have h := (lt_div_iff₀ c.property).mp hx
    simpa only [mul_comm] using h
  calc
    _ = ((c : ℝ) * Real.exp (-((L : ℝ) - xiGaussianCertifiedPhaseGap) * x)) *
        Real.exp (-(xiGaussianCertifiedPhaseGap * x)) := by
      rw [mul_assoc, ← Real.exp_add]
      congr 2
      dsimp only [t]
      ring
    _ < k * Real.exp (-(xiGaussianCertifiedPhaseGap * x)) :=
      mul_lt_mul_of_pos_right hsmall (Real.exp_pos _)
    _ = _ := by
      change (Real.exp ((s : ℝ) * xiGaussianCertifiedPhaseGap) * C) *
        Real.exp (-(xiGaussianCertifiedPhaseGap * x)) =
          Real.exp (-((x - (s : ℝ)) * xiGaussianCertifiedPhaseGap)) * C
      rw [mul_right_comm, ← Real.exp_add]
      congr 2
      ring

/-- Complete three-by-three comparison, including the total channel and every cross term.
Its positive floor has an actual critical-node rate strictly above the certified phase gap. -/
theorem exists_xiHeatThirdQuadratic_maxNode_certifiedPhase_comparison :
    ∃ c₀ : ℝ, 0 < c₀ ∧ ∃ L : ℝ, xiGaussianCertifiedPhaseGap < L ∧
      ∀ (a b c : ℝ) (s : {s : ℝ // 0 < s})
        (t : {t : {t : ℝ // 0 < t} // (s : ℝ) ≤ (t : ℝ)}),
        (c₀ * Real.exp (-(L * (t.1 : ℝ))) -
          Real.exp (-(((t.1 : ℝ) - (s : ℝ)) * xiGaussianCertifiedPhaseGap)) *
            xiGaussianCoefficientAnchorAt 3 s) * (a ^ 2 + b ^ 2 + c ^ 2) ≤
              xiHeatThirdQuadratic a b c t.1 := by
  obtain ⟨c₀, hc₀, L, hL, _, _, hbound⟩ :=
    exists_xiHeatHankelForm_maxNode_certifiedPhase_comparison 1
  refine ⟨c₀, hc₀, L, hL, ?_⟩
  intro a b c s t
  rw [xiHeatThirdQuadratic_eq_hankel]
  simpa [Finset.sum_range_succ] using
    hbound (fun n => if n = 0 then a else if n = 1 then b else c) s t

end RHTower
