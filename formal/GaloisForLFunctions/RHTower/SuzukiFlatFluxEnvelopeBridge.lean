import GaloisForLFunctions.RHTower.SuzukiFlatFluxBlockTail
import GaloisForLFunctions.RHTower.SuzukiFlatPrimitiveFluxAssembly

/-!
# From the extended-norm block envelopes to the real Volterra system

The block estimates are naturally `ℝ≥0∞`-valued and indexed by `ℤ`, because that is where they
carry no summability or integrability hypothesis.  The flat Volterra argument is stated for
nonnegative real sequences indexed by `ℕ`.  This file is the transfer: with the envelopes finite —
which is exactly the statement that the profile is square integrable blockwise — `toReal` turns the
extended-norm value and flux estimates into the two hypotheses of `flat_flux_exponential_decay`,
and the coupled system decays at every rate below the source rate.

Finiteness is not an extra assumption about the mathematics: an infinite envelope makes the
`ℝ≥0∞` estimate vacuous, and `toReal` sends it to zero.
-/

open Filter
open scoped ENNReal NNReal Topology

noncomputable section

namespace GaloisForLFunctions.RHTower

open GaloisForLFunctions.HTGeometry

/-- The real-valued envelope sequence attached to a block sequence. -/
def envelopeSeq (ν : ℝ) (a : ℤ → ℝ≥0∞) (n : ℕ) : ℝ := (expEnvelopeZ ν a (n : ℤ)).toReal

theorem envelopeSeq_nonneg (ν : ℝ) (a : ℤ → ℝ≥0∞) (n : ℕ) : 0 ≤ envelopeSeq ν a n :=
  ENNReal.toReal_nonneg

/-! ## Transfer of the value estimate -/

/-- **The localized value estimate in real form.** -/
theorem envelopeSeq_value_le {ν : ℝ} {f y : ℤ → ℝ≥0∞} {A₀ C₀ δ : ℝ} {n : ℕ}
    (hA₀ : 0 ≤ A₀) (hC₀ : 0 ≤ C₀)
    (hyfin : expEnvelopeZ ν y (n : ℤ) ≠ ⊤)
    (h : expEnvelopeZ ν f (n : ℤ)
      ≤ ENNReal.ofReal (A₀ / n) * expEnvelopeZ ν y (n : ℤ)
        + ENNReal.ofReal (C₀ * Real.exp (-δ * n))) :
    envelopeSeq ν f n ≤ A₀ * (envelopeSeq ν y n / n) + C₀ * Real.exp (-δ * n) := by
  have hnn : (0 : ℝ) ≤ A₀ / n := by positivity
  have hcnn : (0 : ℝ) ≤ C₀ * Real.exp (-δ * n) := by positivity
  have hmul : ENNReal.ofReal (A₀ / n) * expEnvelopeZ ν y (n : ℤ) ≠ ⊤ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top hyfin
  have hmaj : ENNReal.ofReal (A₀ / n) * expEnvelopeZ ν y (n : ℤ)
      + ENNReal.ofReal (C₀ * Real.exp (-δ * n)) ≠ ⊤ :=
    ENNReal.add_ne_top.mpr ⟨hmul, ENNReal.ofReal_ne_top⟩
  have hstep := ENNReal.toReal_mono hmaj h
  rw [ENNReal.toReal_add hmul ENNReal.ofReal_ne_top, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal hnn, ENNReal.toReal_ofReal hcnn] at hstep
  refine hstep.trans (le_of_eq ?_)
  rw [envelopeSeq]
  ring

/-! ## Transfer of the flux estimate -/

/-- **The backward flux estimate in real form.** -/
theorem envelopeSeq_flux_le {ν : ℝ} {f y : ℤ → ℝ≥0∞} {D₀ C₁ δ : ℝ} {n : ℕ}
    (hD₀ : 0 ≤ D₀) (hC₁ : 0 ≤ C₁)
    (hffin : ∀ m : ℤ, expEnvelopeZ ν f m ≠ ⊤)
    (htailfin : (∑' k : ℕ, expEnvelopeZ ν f ((n : ℤ) + (k : ℤ))) ≠ ⊤)
    (h : expEnvelopeZ ν y (n : ℤ)
      ≤ ENNReal.ofReal D₀ * (∑' k : ℕ, expEnvelopeZ ν f ((n : ℤ) + (k : ℤ)))
        + ENNReal.ofReal (C₁ * Real.exp (-δ * n))) :
    envelopeSeq ν y n ≤ D₀ * (∑' k : ℕ, envelopeSeq ν f (n + k)) + C₁ * Real.exp (-δ * n) := by
  have hcnn : (0 : ℝ) ≤ C₁ * Real.exp (-δ * n) := by positivity
  have hmul : ENNReal.ofReal D₀ * (∑' k : ℕ, expEnvelopeZ ν f ((n : ℤ) + (k : ℤ))) ≠ ⊤ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top htailfin
  have hmaj : ENNReal.ofReal D₀ * (∑' k : ℕ, expEnvelopeZ ν f ((n : ℤ) + (k : ℤ)))
      + ENNReal.ofReal (C₁ * Real.exp (-δ * n)) ≠ ⊤ :=
    ENNReal.add_ne_top.mpr ⟨hmul, ENNReal.ofReal_ne_top⟩
  have hstep := ENNReal.toReal_mono hmaj h
  rw [ENNReal.toReal_add hmul ENNReal.ofReal_ne_top, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal hD₀, ENNReal.toReal_ofReal hcnn] at hstep
  have htsum : (∑' k : ℕ, expEnvelopeZ ν f ((n : ℤ) + (k : ℤ))).toReal
      = ∑' k : ℕ, envelopeSeq ν f (n + k) := by
    rw [ENNReal.tsum_toReal_eq (fun k => hffin _)]
    refine tsum_congr fun k => ?_
    rw [envelopeSeq]
    congr 2
  rw [htsum] at hstep
  exact hstep

/-! ## The coupled decay -/

/-- **The flat block system decays exponentially.**  The extended-norm value and flux estimates,
transferred to real sequences, feed the flat Volterra argument. -/
theorem envelopeSeq_exponential_decay {ν : ℝ} {f y : ℤ → ℝ≥0∞} {A₀ C₀ D₀ C₁ δ δ' : ℝ}
    (hA₀ : 0 ≤ A₀) (hC₀ : 0 ≤ C₀) (hD₀ : 0 ≤ D₀) (hC₁ : 0 ≤ C₁)
    (hδ : 0 < δ) (hδ' : 0 < δ') (hlt : δ' < δ)
    (hFflat : SuperpolynomiallyFlat (envelopeSeq ν f))
    (hYflat : SuperpolynomiallyFlat (envelopeSeq ν y))
    (hffin : ∀ m : ℤ, expEnvelopeZ ν f m ≠ ⊤)
    (hyfin : ∀ m : ℤ, expEnvelopeZ ν y m ≠ ⊤)
    (htailfin : ∀ n : ℕ, (∑' k : ℕ, expEnvelopeZ ν f ((n : ℤ) + (k : ℤ))) ≠ ⊤)
    (hvalue : ∀ᶠ n : ℕ in atTop, expEnvelopeZ ν f (n : ℤ)
      ≤ ENNReal.ofReal (A₀ / n) * expEnvelopeZ ν y (n : ℤ)
        + ENNReal.ofReal (C₀ * Real.exp (-δ * n)))
    (hflux : ∀ᶠ n : ℕ in atTop, expEnvelopeZ ν y (n : ℤ)
      ≤ ENNReal.ofReal D₀ * (∑' k : ℕ, expEnvelopeZ ν f ((n : ℤ) + (k : ℤ)))
        + ENNReal.ofReal (C₁ * Real.exp (-δ * n))) :
    ∃ C' : ℝ, (∀ᶠ n : ℕ in atTop, envelopeSeq ν y n ≤ C' * Real.exp (-δ' * n)) ∧
      (∀ᶠ n : ℕ in atTop, envelopeSeq ν f n ≤ C' * Real.exp (-δ' * n)) := by
  refine _root_.RHTower.flat_flux_exponential_decay hA₀ hC₀ hD₀ hC₁ hδ hδ' hlt
    (envelopeSeq_nonneg ν f) (envelopeSeq_nonneg ν y) hFflat hYflat ?_ ?_
  · filter_upwards [hvalue] with n hn
    exact envelopeSeq_value_le hA₀ hC₀ (hyfin (n : ℤ)) hn
  · filter_upwards [hflux] with n hn
    exact envelopeSeq_flux_le hD₀ hC₁ hffin (htailfin n) hn

end GaloisForLFunctions.RHTower
