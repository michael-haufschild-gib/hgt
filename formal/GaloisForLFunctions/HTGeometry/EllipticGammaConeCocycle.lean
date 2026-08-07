import GaloisForLFunctions.HTGeometry.EllipticGammaConeDivisor

/-!
# Periodicity and the mixed cocycle of the elliptic gamma function

The elliptic gamma function `Γ(z) = Φ(a + b - z)/Φ(z)` is `1`-periodic, because every factor of the
cone product is, and its mixed multiplicative coboundary

`C_Γ(z) = Γ(z + a + b) Γ(z) / (Γ(z + a) Γ(z + b))`

is the exponential character `-e(-z)`.  Both statements are consequences of the two shift relations

`Φ(w) = P(w) Φ(w + a)`,   `P(w) = (1 - e(w)) P(w + b)`,   `P(w) = ∏_{k ≥ 0} (1 - e(k b + w))`,

which make every cone product in the numerator and denominator of `C_Γ` cancel against a partner,
leaving only `(1 - e(-z))/(1 - e(z)) = -e(-z)`.

These are the two defining properties of the multiplicative triptic source class: `1`-periodicity
and a mixed coboundary with constant logarithmic derivative.
-/

namespace GaloisForLFunctions.HTGeometry

open Complex

/-! ### Elementary character identities -/

theorem expChar_add (w₁ w₂ : ℂ) : expChar (w₁ + w₂) = expChar w₁ * expChar w₂ := by
  rw [expChar, expChar, expChar, ← Complex.exp_add]
  congr 1
  ring

@[simp]
theorem expChar_zero : expChar 0 = 1 := by simp [expChar]

@[simp]
theorem expChar_one : expChar 1 = 1 := by
  rw [expChar, mul_one]
  exact Complex.exp_two_pi_mul_I

theorem expChar_add_one (w : ℂ) : expChar (w + 1) = expChar w := by
  rw [expChar_add, expChar_one, mul_one]

theorem expChar_neg_mul_self (z : ℂ) : expChar (-z) * expChar z = 1 := by
  rw [← expChar_add]
  simp

theorem one_sub_expChar_neg (z : ℂ) :
    1 - expChar (-z) = -expChar (-z) * (1 - expChar z) := by
  have h := expChar_neg_mul_self z
  linear_combination -h

/-! ### Periodicity -/

theorem coneFactor_periodic (a b : ℂ) (n : ℕ × ℕ) (z : ℂ) :
    coneFactor a b n (z + 1) = coneFactor a b n z := by
  rw [coneFactor, coneFactor]
  congr 1
  rw [show (n.1 : ℂ) * a + (n.2 : ℂ) * b + (z + 1)
      = ((n.1 : ℂ) * a + (n.2 : ℂ) * b + z) + 1 by ring, expChar_add_one]

/-- **The cone product is `1`-periodic.** -/
theorem coneProduct_periodic (a b : ℂ) (z : ℂ) :
    coneProduct a b (z + 1) = coneProduct a b z := by
  rw [coneProduct, coneProduct]
  exact tprod_congr fun n => coneFactor_periodic a b n z

/-- **The elliptic gamma function is `1`-periodic.** -/
theorem ellipticGammaCone_periodic (a b : ℂ) (z : ℂ) :
    ellipticGammaCone a b (z + 1) = ellipticGammaCone a b z := by
  rw [ellipticGammaCone]
  simp only [Pi.div_apply]
  rw [coneProduct_periodic a b z]
  congr 1
  rw [show a + b - (z + 1) = (a + b - z) + (-1 : ℂ) by ring]
  have h := coneProduct_periodic a b (a + b - z + (-1 : ℂ))
  rw [show a + b - z + (-1 : ℂ) + 1 = a + b - z by ring] at h
  exact h.symm

/-! ### The mixed cocycle -/

/-- **The four-fold shift identity.**  Every cone product in the numerator cancels against one in
the denominator, up to the two single-index products, whose ratio is `(1 - e(-z))/(1 - e(z))`. -/
theorem coneProduct_cocycle_identity {a b : ℂ} (ha : 0 < a.im) (hb : 0 < b.im) (z : ℂ) :
    (1 - expChar z) * (coneProduct a b (-z) * coneProduct a b (a + b - z)
        * coneProduct a b (z + a) * coneProduct a b (z + b))
      = (1 - expChar (-z)) * (coneProduct a b (z + a + b) * coneProduct a b z
        * coneProduct a b (b - z) * coneProduct a b (a - z)) := by
  have e1 : coneProduct a b (-z) = singleProduct b (-z) * coneProduct a b (a - z) := by
    have h := coneProduct_shift ha hb (-z)
    rwa [show -z + a = a - z by ring] at h
  have e2 : coneProduct a b (b - z) = singleProduct b (b - z) * coneProduct a b (a + b - z) := by
    have h := coneProduct_shift ha hb (b - z)
    rwa [show b - z + a = a + b - z by ring] at h
  have e3 : coneProduct a b z = singleProduct b z * coneProduct a b (z + a) :=
    coneProduct_shift ha hb z
  have e4 : coneProduct a b (z + b) = singleProduct b (z + b) * coneProduct a b (z + a + b) := by
    have h := coneProduct_shift ha hb (z + b)
    rwa [show z + b + a = z + a + b by ring] at h
  have p1 : singleProduct b (-z) = (1 - expChar (-z)) * singleProduct b (b - z) := by
    have h := singleProduct_shift hb (-z)
    rwa [show -z + b = b - z by ring] at h
  have p2 : singleProduct b z = (1 - expChar z) * singleProduct b (z + b) :=
    singleProduct_shift hb z
  rw [e1, e2, e3, e4, p1, p2]
  ring

/-- **The mixed multiplicative coboundary is the exponential character `-e(-z)`.** -/
theorem coneProduct_mixed_cocycle {a b : ℂ} (ha : 0 < a.im) (hb : 0 < b.im) {z : ℂ}
    (hz : 1 - expChar z ≠ 0) :
    coneProduct a b (-z) * coneProduct a b (a + b - z) * coneProduct a b (z + a)
        * coneProduct a b (z + b)
      = -expChar (-z) * (coneProduct a b (z + a + b) * coneProduct a b z
        * coneProduct a b (b - z) * coneProduct a b (a - z)) := by
  have hid := coneProduct_cocycle_identity ha hb z
  rw [one_sub_expChar_neg z] at hid
  refine mul_left_cancel₀ hz ?_
  rw [hid]
  ring

/-- **The mixed cocycle of the elliptic gamma function**, in ratio form at a point where all four
cone products in the denominator are nonzero. -/
theorem ellipticGammaCone_mixed_cocycle {a b : ℂ} (ha : 0 < a.im) (hb : 0 < b.im) {z : ℂ}
    (hz : 1 - expChar z ≠ 0)
    (h1 : coneProduct a b (z + a + b) ≠ 0) (h2 : coneProduct a b z ≠ 0)
    (h3 : coneProduct a b (b - z) ≠ 0) (h4 : coneProduct a b (a - z) ≠ 0)
    (_h5 : coneProduct a b (z + a) ≠ 0) (_h6 : coneProduct a b (z + b) ≠ 0) :
    ellipticGammaCone a b (z + a + b) * ellipticGammaCone a b z
        / (ellipticGammaCone a b (z + a) * ellipticGammaCone a b (z + b))
      = -expChar (-z) := by
  have hnum := coneProduct_mixed_cocycle ha hb hz
  simp only [ellipticGammaCone, Pi.div_apply]
  rw [show a + b - (z + a + b) = -z by ring, show a + b - (z + a) = b - z by ring,
    show a + b - (z + b) = a - z by ring]
  field_simp
  linear_combination hnum

end GaloisForLFunctions.HTGeometry
