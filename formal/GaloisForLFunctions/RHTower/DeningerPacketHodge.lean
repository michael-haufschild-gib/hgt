import GaloisForLFunctions.RHTower.DeningerHarmonicCup

/-!
# The packet cup form and the positive Hodge operator

The leafwise gradient of the Poisson extension of a character of frequency `μ` is the mode profile
scaled by `|μ|`, so the radial wedge integral of the gradients of two opposite characters is
`i μ`.  A finite packet of characters stable under frequency reversal therefore carries the
alternating cup form

`Ψ(φ, ψ) = i ∑ ℓ(a) φ_a ψ_{-a}`,

which is nondegenerate whenever every frequency in the packet is nonzero.  The odd operator
`W = i sgn(D)` has square `-1`, and pairing a packet against the `W`-image of its conjugate
reversal returns its boundary norm, a positive number.

* `deningerGradMode_cup` : the radial wedge integral of two opposite gradient modes.
* `deningerPacketCup_eq` : the cup form of a finite packet.
* `deningerHodgeW_sq` : the Hodge operator squares to `-1`.
* `deningerPacketCup_hodge` : the Hodge pairing is the boundary norm.
* `deningerPacketCup_hodge_pos` : and it is strictly positive on a nonzero packet.
-/

namespace RHTower

open MeasureTheory Set

section GradMode

/-- The leafwise gradient of the Poisson extension of a unit character: the mode scaled by the
absolute frequency. -/
noncomputable def deningerGradMode (μ : ℝ) (r : ℝ) : ℂ × ℂ :=
  ((|μ| : ℝ) : ℂ) • deningerMode μ r

/-- **The radial wedge integral of two opposite gradient modes** is `i μ`. -/
theorem deningerGradMode_cup {μ : ℝ} (hμ : μ ≠ 0) :
    (∫ r in Ioi (0 : ℝ),
        deningerCxWedge (deningerGradMode μ r) (deningerGradMode (-μ) r))
      = Complex.I * (μ : ℂ) := by
  have hpt : ∀ r : ℝ,
      deningerCxWedge (deningerGradMode μ r) (deningerGradMode (-μ) r)
        = (((|μ| : ℝ) : ℂ) * ((|μ| : ℝ) : ℂ))
          * deningerCxWedge (deningerMode μ r) (deningerMode (-μ) r) := by
    intro r
    rw [deningerGradMode, deningerGradMode, abs_neg, deningerCxWedge_smul_left,
      deningerCxWedge_smul_right]
    ring
  rw [MeasureTheory.setIntegral_congr_fun measurableSet_Ioi fun r _ => hpt r,
    integral_const_mul, deningerMode_cup hμ]
  have habs : ((|μ| : ℝ) : ℂ) * ((|μ| : ℝ) : ℂ) = (μ : ℂ) * (μ : ℂ) := by
    have h : |μ| * |μ| = μ * μ := abs_mul_abs_self μ
    exact_mod_cast congrArg (fun x : ℝ => (x : ℂ)) h
  have hμc : (μ : ℂ) ≠ 0 := by exact_mod_cast hμ
  rw [habs]
  field_simp

end GradMode

section PacketHodge

variable {ι : Type*}

/-- The odd Hodge operator `W = i sgn(D)` on packet coefficients. -/
noncomputable def deningerHodgeW (ℓ : ι → ℝ) (φ : ι → ℂ) (a : ι) : ℂ :=
  Complex.I * (deningerFreqSign (ℓ a) : ℂ) * φ a

/-- **The Hodge operator squares to `-1`.** -/
theorem deningerHodgeW_sq (ℓ : ι → ℝ) (φ : ι → ℂ) :
    deningerHodgeW ℓ (deningerHodgeW ℓ φ) = fun a => -φ a := by
  funext a
  have hsq : (deningerFreqSign (ℓ a) : ℂ) * (deningerFreqSign (ℓ a) : ℂ) = 1 := by
    exact_mod_cast congrArg (fun x : ℝ => (x : ℂ)) (deningerFreqSign_sq (ℓ a))
  have hI : Complex.I * Complex.I = -1 := by
    rw [← pow_two]
    exact Complex.I_sq
  rw [deningerHodgeW, deningerHodgeW]
  linear_combination (Complex.I * Complex.I * φ a) * hsq + (φ a) * hI

/-- The conjugate reversal of a packet: complex conjugation exchanges opposite frequencies. -/
noncomputable def deningerConjReverse (σ : ι → ι) (φ : ι → ℂ) (a : ι) : ℂ :=
  (starRingEnd ℂ) (φ (σ a))

/-- **The cup form of a finite packet**: the sum over the packet of the radial wedge integrals of
the gradient modes, weighted by the coefficients of the two data. -/
noncomputable def deningerPacketCup (ℓ : ι → ℝ) (σ : ι → ι) (S : Finset ι) (φ ψ : ι → ℂ) : ℂ :=
  ∑ a ∈ S, φ a * ψ (σ a) *
    ∫ r in Ioi (0 : ℝ),
      deningerCxWedge (deningerGradMode (ℓ a) r) (deningerGradMode (ℓ (σ a)) r)

/-- **The cup form is `i ∑ ℓ(a) φ_a ψ_{-a}`**, by the radial wedge integral of the gradient
modes. -/
theorem deningerPacketCup_eq (ℓ : ι → ℝ) (σ : ι → ι) (S : Finset ι) (φ ψ : ι → ℂ)
    (hσℓ : ∀ a, ℓ (σ a) = -ℓ a) (hℓ : ∀ a ∈ S, ℓ a ≠ 0) :
    deningerPacketCup ℓ σ S φ ψ
      = Complex.I * ∑ a ∈ S, (ℓ a : ℂ) * (φ a * ψ (σ a)) := by
  rw [deningerPacketCup, Finset.mul_sum]
  refine Finset.sum_congr rfl fun a ha => ?_
  rw [hσℓ a, deningerGradMode_cup (hℓ a ha)]
  ring

/-- **The Hodge pairing is the boundary norm.**  Pairing a packet against the `W`-image of its
conjugate reversal cancels the two factors of `i` and returns the weighted sum of the squared
coefficients. -/
theorem deningerPacketCup_hodge (ℓ : ι → ℝ) (σ : ι → ι) (S : Finset ι) (φ : ι → ℂ)
    (hσ : ∀ a, σ (σ a) = a) (hσℓ : ∀ a, ℓ (σ a) = -ℓ a) (hℓ : ∀ a ∈ S, ℓ a ≠ 0) :
    deningerPacketCup ℓ σ S φ (deningerHodgeW ℓ (deningerConjReverse σ φ))
      = ((∑ a ∈ S, |ℓ a| * ‖φ a‖ ^ (2 : ℕ) : ℝ) : ℂ) := by
  rw [deningerPacketCup_eq ℓ σ S φ _ hσℓ hℓ]
  have hterm : ∀ a ∈ S,
      (ℓ a : ℂ) * (φ a * deningerHodgeW ℓ (deningerConjReverse σ φ) (σ a))
        = -Complex.I * ((|ℓ a| * ‖φ a‖ ^ (2 : ℕ) : ℝ) : ℂ) := by
    intro a ha
    have hsign : deningerFreqSign (ℓ (σ a)) = -deningerFreqSign (ℓ a) := by
      rw [hσℓ a]
      exact deningerFreqSign_neg (hℓ a ha)
    have habs : (ℓ a : ℂ) * (deningerFreqSign (ℓ a) : ℂ) = ((|ℓ a| : ℝ) : ℂ) := by
      have h := deningerFreqSign_mul_abs (hℓ a ha)
      have h2 : deningerFreqSign (ℓ a) * (deningerFreqSign (ℓ a) * |ℓ a|)
          = deningerFreqSign (ℓ a) * ℓ a := by rw [h]
      rw [← mul_assoc, deningerFreqSign_sq, one_mul] at h2
      have h3 : ((|ℓ a| : ℝ) : ℂ) = ((deningerFreqSign (ℓ a) * ℓ a : ℝ) : ℂ) := by
        exact_mod_cast congrArg (fun x : ℝ => (x : ℂ)) h2
      rw [h3]
      push_cast
      ring
    have hnormSq : φ a * (starRingEnd ℂ) (φ a) = ((‖φ a‖ ^ (2 : ℕ) : ℝ) : ℂ) := by
      rw [Complex.mul_conj]
      norm_cast
      exact Complex.normSq_eq_norm_sq (φ a)
    rw [deningerHodgeW, deningerConjReverse, hσ a, hsign]
    push_cast
    rw [show (ℓ a : ℂ) * (φ a * (Complex.I * -(deningerFreqSign (ℓ a) : ℂ)
          * (starRingEnd ℂ) (φ a)))
        = -Complex.I * (((ℓ a : ℂ) * (deningerFreqSign (ℓ a) : ℂ))
          * (φ a * (starRingEnd ℂ) (φ a))) by ring,
      habs, hnormSq]
    push_cast
    ring
  rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum]
  have hI : Complex.I * -Complex.I = 1 := by
    have : Complex.I * Complex.I = -1 := by
      rw [← pow_two]; exact Complex.I_sq
    linear_combination -this
  rw [← mul_assoc, hI, one_mul]
  push_cast
  ring

/-- **The Hodge pairing is strictly positive on a nonzero packet.**  Every term is nonnegative and
the term of a nonzero coefficient is positive. -/
theorem deningerPacketCup_hodge_pos (ℓ : ι → ℝ) (S : Finset ι) (φ : ι → ℂ)
    (hℓ : ∀ a ∈ S, ℓ a ≠ 0) {b : ι} (hb : b ∈ S) (hφ : φ b ≠ 0) :
    0 < ∑ a ∈ S, |ℓ a| * ‖φ a‖ ^ (2 : ℕ) := by
  have hnonneg : ∀ a ∈ S, 0 ≤ |ℓ a| * ‖φ a‖ ^ (2 : ℕ) := fun a _ => by positivity
  have hposb : 0 < |ℓ b| * ‖φ b‖ ^ (2 : ℕ) := by
    have h1 : 0 < |ℓ b| := abs_pos.mpr (hℓ b hb)
    have h2 : 0 < ‖φ b‖ := norm_pos_iff.mpr hφ
    positivity
  exact Finset.sum_pos' hnonneg ⟨b, hb, hposb⟩

/-- **The cup form is nondegenerate on a finite packet of nonzero frequencies.** -/
theorem deningerPacketCup_nondegenerate (ℓ : ι → ℝ) (σ : ι → ι) (S : Finset ι) (φ : ι → ℂ)
    (hσ : ∀ a, σ (σ a) = a) (hσℓ : ∀ a, ℓ (σ a) = -ℓ a) (hℓ : ∀ a ∈ S, ℓ a ≠ 0)
    (hzero : ∀ ψ : ι → ℂ, deningerPacketCup ℓ σ S φ ψ = 0) :
    ∀ a ∈ S, φ a = 0 := by
  classical
  intro a ha
  have hψ := hzero (fun c => if c = σ a then 1 else 0)
  rw [deningerPacketCup_eq ℓ σ S φ _ hσℓ hℓ] at hψ
  have hsum : ∑ c ∈ S, (ℓ c : ℂ) * (φ c * (if σ c = σ a then 1 else 0))
      = (ℓ a : ℂ) * φ a := by
    rw [Finset.sum_eq_single a]
    · rw [if_pos rfl, mul_one]
    · intro c _ hca
      have hne : σ c ≠ σ a := by
        intro h
        exact hca (by rw [← hσ c, h, hσ a])
      rw [if_neg hne, mul_zero, mul_zero]
    · intro hna
      exact absurd ha hna
  rw [hsum] at hψ
  have hIne : Complex.I ≠ 0 := Complex.I_ne_zero
  have hℓne : (ℓ a : ℂ) ≠ 0 := by exact_mod_cast hℓ a ha
  have := mul_eq_zero.mp hψ
  rcases this with h | h
  · exact absurd h hIne
  · rcases mul_eq_zero.mp h with h' | h'
    · exact absurd h' hℓne
    · exact h'

end PacketHodge

end RHTower
