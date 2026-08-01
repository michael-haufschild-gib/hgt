import GaloisForLFunctions.RHTower.SoninStrictApertureCurvature
import GaloisForLFunctions.RHTower.SoninApertureFlagChain

/-!
# The aperture flag law is strictly subadditive

Refining an aperture flag loses exactly the sum of the successive coupling energies, and those
couplings are not all zero.  So the flag law is a strict inequality, not an identity: refinement
genuinely destroys residual trace rather than merely redistributing it.
-/

noncomputable section

set_option maxHeartbeats 1000000

namespace RHTower

open Filter ContinuousLinearMap
open scoped Topology

/-- A three-step flag through a prescribed triple, extended by unit steps. -/
def soninTripleFlag (a b c : ℝ) : ℕ → ℝ := fun i =>
  if i = 0 then a else if i = 1 then b else c + ((i - 2 : ℕ) : ℝ)

@[simp] theorem soninTripleFlag_zero (a b c : ℝ) : soninTripleFlag a b c 0 = a := rfl

@[simp] theorem soninTripleFlag_one (a b c : ℝ) : soninTripleFlag a b c 1 = b := rfl

@[simp] theorem soninTripleFlag_two (a b c : ℝ) : soninTripleFlag a b c 2 = c := by
  simp [soninTripleFlag]

theorem soninTripleFlag_strict (a b c : ℝ) (hab : a < b) (hbc : b < c) (i : ℕ) :
    soninTripleFlag a b c i < soninTripleFlag a b c (i + 1) := by
  match i with
  | 0 => simpa using hab
  | 1 => simpa using hbc
  | (n + 2) =>
      have h1 : soninTripleFlag a b c (n + 2) = c + ((n : ℕ) : ℝ) := by
        simp [soninTripleFlag]
      have h2 : soninTripleFlag a b c (n + 3) = c + ((n + 1 : ℕ) : ℝ) := by
        simp [soninTripleFlag]
      rw [h1, h2]
      push_cast
      linarith

/-- **Strict flag law.**  There is an actual flag and dilation scale at which refining the aperture
flag strictly decreases the residual trace. -/
theorem exists_strict_soninApertureResidualTrace_chain
    (a b c : ℝ) (ha : 0 < a) (hab : a < b) (hbc : b < c) :
    ∃ (r : ℝ) (hr : 1 < r),
      c < r * a ∧
      (soninApertureResidualTrace a c r hr).re <
        ∑ i ∈ Finset.range 2,
          (soninApertureResidualTrace (soninTripleFlag a b c i)
            (soninTripleFlag a b c (i + 1)) r hr).re := by
  have hb : 0 < b := ha.trans hab
  have hq1 : a < (a + b) / 2 := by linarith
  have hq2 : (a + b) / 2 < b := by linarith
  obtain ⟨r, hr, hcr, hne⟩ := exists_scale_soninApertureCoupling_ne_zero a b c ha hb hab hbc
    ((a + b) / 2) hq1 hq2
  refine ⟨r, hr, hcr, ?_⟩
  have hchain := re_soninApertureResidualTrace_chain hr (soninTripleFlag a b c)
    (by simpa using ha) (soninTripleFlag_strict a b c hab hbc) 2 (by norm_num)
    (by simpa using hcr)
  have hZ : evenSoninApertureSuccessiveLayerTransition
      (soninTripleFlag a b c 0) (soninTripleFlag a b c 1) (soninTripleFlag a b c 2) r hr ≠ 0 := by
    simpa using hne
  have hHS := evenSoninApertureSuccessiveLayerTransition_isHilbertSchmidt ha hab hbc hr hcr
  have hpos : 0 < hsNormSq (evenSoninApertureSuccessiveLayerTransition
      (soninTripleFlag a b c 0) (soninTripleFlag a b c 1)
      (soninTripleFlag a b c 2) r hr) := by
    rcases lt_or_eq_of_le (hsNormSq_nonneg (evenSoninApertureSuccessiveLayerTransition
      (soninTripleFlag a b c 0) (soninTripleFlag a b c 1)
      (soninTripleFlag a b c 2) r hr)) with h | h
    · exact h
    · refine absurd ?_ hZ
      refine (hsNormSq_eq_zero_iff ?_).mp h.symm
      simpa using hHS
  have hsum : ∑ j ∈ Finset.Ico 1 2, hsNormSq (evenSoninApertureSuccessiveLayerTransition
      (soninTripleFlag a b c 0) (soninTripleFlag a b c j)
      (soninTripleFlag a b c (j + 1)) r hr) =
      hsNormSq (evenSoninApertureSuccessiveLayerTransition
        (soninTripleFlag a b c 0) (soninTripleFlag a b c 1)
        (soninTripleFlag a b c 2) r hr) := by
    simp
  rw [hsum] at hchain
  have hac : (soninApertureResidualTrace (soninTripleFlag a b c 0)
      (soninTripleFlag a b c 2) r hr).re = (soninApertureResidualTrace a c r hr).re := by
    simp
  rw [hac] at hchain
  linarith

end RHTower
