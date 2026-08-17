import GaloisForLFunctions.RHTower.SuzukiMidpointReflectionInstantiation

/-!
# The literal exponential sources and the Cayley scalar

The two half-interval sources are `cosh` and `sinh`, and they are the half-sum and half-difference
of the two exponentials `e^x` and `e^{-x}`.  Bilinearity therefore turns their energies into

`E₀ − O₀ = b(u, v)`,   `E₀ + O₀ = (b(u,u) + b(v,v))/2`,

so the parity Cayley scalar is exactly the cross term over the average energy, `κ₀ = 2 b(u,v) /
(b(u,u) + b(v,v))`.  Midpoint reflection relates the two energies by `e^{2a}` and bounds the cross
term by `e^a b(v,v)`, and those two facts collapse the Cayley scalar to at most `sech a`.

This is `(229)` on the literal sources: no estimate is used beyond Cauchy–Schwarz for a positive
semidefinite form.
-/

noncomputable section

namespace GaloisForLFunctions.RHTower

variable {b : (ℝ → ℝ) → (ℝ → ℝ) → ℝ}

/-- The half-interval even source. -/
def coshSource : ℝ → ℝ := Real.cosh

/-- The half-interval odd source. -/
def sinhSource : ℝ → ℝ := Real.sinh

theorem coshSource_eq : coshSource = (2⁻¹ : ℝ) • (expRise + expDecay) := by
  funext x
  rw [coshSource, Real.cosh_eq, Pi.smul_apply, Pi.add_apply, expRise, expDecay, smul_eq_mul]
  ring

theorem sinhSource_eq : sinhSource = (2⁻¹ : ℝ) • (expRise - expDecay) := by
  funext x
  rw [sinhSource, Real.sinh_eq, Pi.smul_apply, Pi.sub_apply, expRise, expDecay, smul_eq_mul]
  ring

/-! ## The parity energies in terms of the exponentials -/

variable (hadd : ∀ x y z, b (x + y) z = b x z + b y z)
  (hsmul : ∀ (c : ℝ) (x y), b (c • x) y = c * b x y)
  (hsymm : ∀ x y, b x y = b y x)

include hadd hsmul hsymm in
theorem b_expand (φ ψ χ ω : ℝ → ℝ) (c d : ℝ) :
    b (c • (φ + ψ)) (d • (χ + ω))
      = c * d * (b φ χ + b φ ω + b ψ χ + b ψ ω) := by
  have hsmul₂ : ∀ (e : ℝ) (p q : ℝ → ℝ), b p (e • q) = e * b p q := by
    intro e p q
    rw [hsymm, hsmul, hsymm q p]
  have hadd₂ : ∀ p q r : ℝ → ℝ, b p (q + r) = b p q + b p r := by
    intro p q r
    rw [hsymm, hadd, hsymm q p, hsymm r p]
  rw [hsmul, hsmul₂, hadd, hadd₂, hadd₂]
  ring

include hadd hsmul hsymm in
/-- **The parity gap is the cross energy.** -/
theorem parityGap_eq_cross :
    b coshSource coshSource - b sinhSource sinhSource = b expRise expDecay := by
  have hsub : expRise - expDecay = expRise + (-1 : ℝ) • expDecay := by
    funext x
    simp [Pi.sub_apply, Pi.add_apply]
    ring
  rw [coshSource_eq, sinhSource_eq, hsub]
  rw [b_expand hadd hsmul hsymm expRise expDecay expRise expDecay 2⁻¹ 2⁻¹]
  have hkey : b expRise ((-1 : ℝ) • expDecay) = -b expRise expDecay := by
    rw [hsymm, hsmul, hsymm expDecay expRise]
    ring
  have hkey2 : b ((-1 : ℝ) • expDecay) expRise = -b expDecay expRise := by
    rw [hsmul]
    ring
  have hkey3 : b ((-1 : ℝ) • expDecay) ((-1 : ℝ) • expDecay) = b expDecay expDecay := by
    rw [hsmul, hsymm, hsmul, hsymm expDecay expDecay]
    ring
  rw [b_expand hadd hsmul hsymm expRise ((-1 : ℝ) • expDecay) expRise ((-1 : ℝ) • expDecay)
    2⁻¹ 2⁻¹, hkey, hkey2, hkey3, hsymm expDecay expRise]
  ring

include hadd hsmul hsymm in
/-- **The parity sum is the average energy.** -/
theorem paritySum_eq_avg :
    b coshSource coshSource + b sinhSource sinhSource
      = (b expRise expRise + b expDecay expDecay) / 2 := by
  have hsub : expRise - expDecay = expRise + (-1 : ℝ) • expDecay := by
    funext x
    simp [Pi.sub_apply, Pi.add_apply]
    ring
  rw [coshSource_eq, sinhSource_eq, hsub]
  rw [b_expand hadd hsmul hsymm expRise expDecay expRise expDecay 2⁻¹ 2⁻¹]
  have hkey : b expRise ((-1 : ℝ) • expDecay) = -b expRise expDecay := by
    rw [hsymm, hsmul, hsymm expDecay expRise]
    ring
  have hkey2 : b ((-1 : ℝ) • expDecay) expRise = -b expDecay expRise := by
    rw [hsmul]
    ring
  have hkey3 : b ((-1 : ℝ) • expDecay) ((-1 : ℝ) • expDecay) = b expDecay expDecay := by
    rw [hsmul, hsymm, hsmul, hsymm expDecay expDecay]
    ring
  rw [b_expand hadd hsmul hsymm expRise ((-1 : ℝ) • expDecay) expRise ((-1 : ℝ) • expDecay)
    2⁻¹ 2⁻¹, hkey, hkey2, hkey3, hsymm expDecay expRise]
  ring

/-! ## `(229)` on the literal sources -/

include hadd hsmul hsymm in
/-- **`(229)`: the parity Cayley scalar of the literal exponential sources is at most `sech a`.** -/
theorem abs_parityCayley_le_sech {J : ℝ → ℝ → ℝ → ℝ} {a : ℝ}
    (hpsd : ∀ x, 0 ≤ b x x)
    (hJ : ∀ x y, b (J a x) (J a y) = b x y)
    (hrefl : expRise = Real.exp a • J a expDecay)
    (hB : 0 < b expDecay expDecay) :
    |(b coshSource coshSource - b sinhSource sinhSource)
        / (b coshSource coshSource + b sinhSource sinhSource)| ≤ 1 / Real.cosh a := by
  have hgap := parityGap_eq_cross hadd hsmul hsymm (b := b)
  have hsum := paritySum_eq_avg hadd hsmul hsymm (b := b)
  have hA : b expRise expRise = Real.exp (2 * a) * b expDecay expDecay :=
    RHTower.energy_of_reflected (b := b) (J := J a) hsmul hsymm hJ hrefl
  have hD : |b expRise expDecay| ≤ Real.exp a * b expDecay expDecay :=
    RHTower.abs_cross_le_exp_mul (b := b) (J := J a) hsymm hadd hsmul hpsd hJ hrefl
  rw [hgap, hsum, hA]
  have hcosh : 0 < Real.cosh a := Real.cosh_pos a
  have hexp : 0 < Real.exp a := Real.exp_pos a
  have hden : (Real.exp (2 * a) * b expDecay expDecay + b expDecay expDecay) / 2
      = Real.exp a * Real.cosh a * b expDecay expDecay := by
    rw [Real.cosh_eq]
    have h2a : Real.exp (2 * a) = Real.exp a * Real.exp a := by
      rw [← Real.exp_add]
      ring_nf
    have hna : Real.exp a * Real.exp (-a) = 1 := by
      rw [← Real.exp_add]
      simp
    field_simp
    nlinarith [h2a, hna]
  rw [hden]
  rw [abs_div, abs_of_pos (by positivity : (0 : ℝ) < Real.exp a * Real.cosh a * b expDecay expDecay)]
  rw [div_le_div_iff₀ (by positivity) hcosh]
  calc |b expRise expDecay| * Real.cosh a
      ≤ (Real.exp a * b expDecay expDecay) * Real.cosh a :=
        mul_le_mul_of_nonneg_right hD hcosh.le
    _ = 1 * (Real.exp a * Real.cosh a * b expDecay expDecay) := by ring

end GaloisForLFunctions.RHTower
