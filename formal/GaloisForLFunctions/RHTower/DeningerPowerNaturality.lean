import GaloisForLFunctions.RHTower.DeningerPacketHodge

/-!
# Power naturality of the boundary data

The arithmetic power shift multiplies every frequency by a positive factor.  On coefficient data
the induced pullback therefore intertwines the absolute-frequency operator with weight one, and
commutes with the odd Hodge operator, because a positive factor does not change a sign.  The
boundary norm and the cup form of a finite packet both scale by the factor, so the pullback
renormalized by its square root is unitary for the boundary norm.

* `deningerPowerPull_absOp` : the intertwining relation.
* `deningerPowerPull_hodgeW` : the Hodge operator commutes with the pullback.
* `deningerPowerPull_boundaryNormSq` : the boundary norm scales by the factor.
* `deningerPowerPull_unitary` : the renormalized pullback is unitary.
* `deningerPowerPull_packetCup` : the cup form scales by the factor.
-/

namespace RHTower

open MeasureTheory Set

section PowerNaturality

variable {ι : Type*} [DecidableEq ι]

/-- The absolute-frequency operator `A_ℓ` on coefficient data. -/
noncomputable def deningerAbsOp (ℓ : ι → ℝ) (φ : ι → ℂ) (a : ι) : ℂ :=
  ((|ℓ a| : ℝ) : ℂ) * φ a

/-- The power pullback on coefficient data: reindexing by the arithmetic shift, scaled by the
power. -/
noncomputable def deningerPowerPull (q : ℝ) (τ : ι → ι) (φ : ι → ℂ) (a : ι) : ℂ :=
  (q : ℂ) * φ (τ a)

/-- A positive factor does not change the sign of a frequency. -/
theorem deningerFreqSign_mul_pos {c μ : ℝ} (hc : 0 < c) :
    deningerFreqSign (c * μ) = deningerFreqSign μ := by
  rw [deningerFreqSign, deningerFreqSign]
  by_cases h : 0 < μ
  · rw [if_pos h, if_pos (mul_pos hc h)]
  · rw [if_neg h, if_neg]
    intro hcon
    exact h (by nlinarith)

omit [DecidableEq ι] in
/-- **The pullback intertwines the absolute-frequency operator with weight one.**  Pulling back
after applying the operator is the factor times applying the operator after pulling back. -/
theorem deningerPowerPull_absOp (ℓ : ι → ℝ) (q c : ℝ) (τ : ι → ι) (hc : 0 < c)
    (hτ : ∀ a, ℓ (τ a) = c * ℓ a) (φ : ι → ℂ) :
    deningerPowerPull q τ (deningerAbsOp ℓ φ)
      = fun a => (c : ℂ) * deningerAbsOp ℓ (deningerPowerPull q τ φ) a := by
  funext a
  have habs : |ℓ (τ a)| = c * |ℓ a| := by
    rw [hτ a, abs_mul, abs_of_pos hc]
  rw [deningerPowerPull, deningerAbsOp, deningerAbsOp, deningerPowerPull, habs]
  push_cast
  ring

omit [DecidableEq ι] in
/-- **The odd Hodge operator commutes with the pullback**, because the power factor is positive and
so preserves signs. -/
theorem deningerPowerPull_hodgeW (ℓ : ι → ℝ) (q c : ℝ) (τ : ι → ι) (hc : 0 < c)
    (hτ : ∀ a, ℓ (τ a) = c * ℓ a) (φ : ι → ℂ) :
    deningerHodgeW ℓ (deningerPowerPull q τ φ)
      = deningerPowerPull q τ (deningerHodgeW ℓ φ) := by
  funext a
  have hsign : deningerFreqSign (ℓ (τ a)) = deningerFreqSign (ℓ a) := by
    rw [hτ a]
    exact deningerFreqSign_mul_pos hc
  rw [deningerHodgeW, deningerPowerPull, deningerPowerPull, deningerHodgeW, hsign]
  ring

/-- **The boundary norm scales by the power.**  Reindexing the packet by the shift turns the weight
into the shifted weight, and the two factors of the power combine with the weight factor. -/
theorem deningerPowerPull_boundaryNormSq (ℓ : ι → ℝ) (q : ℝ) (τ : ι → ι) (S : Finset ι)
    (hq : 0 < q) (hinj : ∀ x ∈ S, ∀ y ∈ S, τ x = τ y → x = y)
    (hτ : ∀ a, ℓ (τ a) = q * ℓ a) (φ : ι → ℂ) :
    (∑ a ∈ S, |ℓ a| * ‖deningerPowerPull q τ φ a‖ ^ 2)
      = q * ∑ b ∈ S.image τ, |ℓ b| * ‖φ b‖ ^ 2 := by
  rw [Finset.sum_image hinj, Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  have habs : |ℓ (τ a)| = q * |ℓ a| := by
    rw [hτ a, abs_mul, abs_of_pos hq]
  have hnorm : ‖deningerPowerPull q τ φ a‖ ^ 2 = q ^ 2 * ‖φ (τ a)‖ ^ 2 := by
    rw [deningerPowerPull, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hq, mul_pow]
  rw [habs, hnorm]
  ring

/-- **The renormalized pullback is unitary** for the boundary norm. -/
theorem deningerPowerPull_unitary (ℓ : ι → ℝ) (q : ℝ) (τ : ι → ι) (S : Finset ι)
    (hq : 0 < q) (hinj : ∀ x ∈ S, ∀ y ∈ S, τ x = τ y → x = y)
    (hτ : ∀ a, ℓ (τ a) = q * ℓ a) (φ : ι → ℂ) :
    (∑ a ∈ S, |ℓ a| * ‖((Real.sqrt q)⁻¹ : ℂ) * deningerPowerPull q τ φ a‖ ^ 2)
      = ∑ b ∈ S.image τ, |ℓ b| * ‖φ b‖ ^ 2 := by
  have hsqrt : (0 : ℝ) < Real.sqrt q := Real.sqrt_pos.mpr hq
  have hterm : ∀ a : ι, |ℓ a| * ‖((Real.sqrt q)⁻¹ : ℂ) * deningerPowerPull q τ φ a‖ ^ 2
      = q⁻¹ * (|ℓ a| * ‖deningerPowerPull q τ φ a‖ ^ 2) := by
    intro a
    have hnorm : ‖((Real.sqrt q : ℝ) : ℂ)⁻¹‖ = (Real.sqrt q)⁻¹ := by
      rw [norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hsqrt]
    have hsq : ((Real.sqrt q)⁻¹) ^ 2 = q⁻¹ := by
      rw [inv_pow, Real.sq_sqrt (le_of_lt hq)]
    rw [norm_mul, hnorm, mul_pow, hsq]
    ring
  rw [Finset.sum_congr rfl fun a _ => hterm a, ← Finset.mul_sum,
    deningerPowerPull_boundaryNormSq ℓ q τ S hq hinj hτ φ, ← mul_assoc,
    inv_mul_cancel₀ (ne_of_gt hq), one_mul]

/-- **The cup form scales by the power.**  The reversal commutes with the shift, so the reindexed
packet form is the shifted one, with one factor of the power left over. -/
theorem deningerPowerPull_packetCup (ℓ : ι → ℝ) (q : ℝ) (σ τ : ι → ι) (S : Finset ι)
    (hq : 0 < q) (hinj : ∀ x ∈ S, ∀ y ∈ S, τ x = τ y → x = y)
    (hτ : ∀ a, ℓ (τ a) = q * ℓ a) (hcomm : ∀ a, σ (τ a) = τ (σ a))
    (hσℓ : ∀ a, ℓ (σ a) = -ℓ a) (hℓ : ∀ a ∈ S, ℓ a ≠ 0) (φ ψ : ι → ℂ) :
    deningerPacketCup ℓ σ S (deningerPowerPull q τ φ) (deningerPowerPull q τ ψ)
      = (q : ℂ) * deningerPacketCup ℓ σ (S.image τ) φ ψ := by
  have hℓimage : ∀ b ∈ S.image τ, ℓ b ≠ 0 := by
    intro b hb
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hb
    rw [hτ a]
    exact mul_ne_zero (ne_of_gt hq) (hℓ a ha)
  have hsum : ∑ a ∈ S, (ℓ a : ℂ) * (deningerPowerPull q τ φ a * deningerPowerPull q τ ψ (σ a))
      = (q : ℂ) * ∑ a ∈ S, (ℓ (τ a) : ℂ) * (φ (τ a) * ψ (σ (τ a))) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    have hℓτ : ((ℓ (τ a) : ℝ) : ℂ) = (q : ℂ) * ((ℓ a : ℝ) : ℂ) := by
      rw [hτ a]
      push_cast
      ring
    rw [deningerPowerPull, deningerPowerPull, hcomm a, hℓτ]
    ring
  rw [deningerPacketCup_eq ℓ σ S _ _ hσℓ hℓ,
    deningerPacketCup_eq ℓ σ (S.image τ) φ ψ hσℓ hℓimage, Finset.sum_image hinj, hsum]
  ring

end PowerNaturality

end RHTower
