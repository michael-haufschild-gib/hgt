import GaloisForLFunctions.CohomologyOfWindowsOfSpecZ.TheWindowDatum

/-!
# The Frobenius at infinity of a window

The window involution `σ_A H(u) = H(−A − u)` is the Serre duality of the window and an isometry of
Weil's form (`weilQuad_windowInvolution`). On the window transform
`Ĥ(s) = ∫ H(u) e^{(s − ½)u} du`, whose values at the zeros are the zero-side coordinates of `H`, it
acts by the functional-equation reflection with a twist (`windowTransform_windowInvolution`):

`(σ_A H)^(s) = e^{−(s − ½)A} Ĥ(1 − s)`.

* **The fixed line** (`norm_windowMultiplier`, `norm_windowMultiplier_eq_one_iff`): the multiplier
  has modulus `e^{−(Re s − ½)A}`, which is `1` exactly on `Re s = ½` (for `A ≠ 0`). On the critical
  line `σ_A` preserves the modulus of the transform of every real test
  (`norm_windowTransform_windowInvolution_of_re`); off the line it scales the pair `s, 1 − s` by
  `e^{∓(Re s − ½)A}`.
* **The pair products are invariant** (`windowTransform_windowInvolution_mul`):
  `(σĤ)(s)(σĤ)(1 − s) = Ĥ(s)Ĥ(1 − s)`, the Weil summand of a point `s`. This is why `σ_A` is an
  isometry on every datum: the involution itself does not orient, only its multiplier distinguishes
  the line.
-/

noncomputable section

open MeasureTheory Set Complex

namespace GaloisForLFunctions.CohomologyOfWindowsOfSpecZ

/-- The **window transform** `Ĥ(s) = ∫ H(u) e^{(s − ½)u} du`. -/
def windowTransform (H : ℝ → ℝ) (s : ℂ) : ℂ := ∫ u, (H u : ℂ) * cexp ((s - 1 / 2) * u)

/-- The **multiplier** of the window involution, `e^{−(s − ½)A}`. -/
def windowMultiplier (A : ℝ) (s : ℂ) : ℂ := cexp (-((s - 1 / 2) * A))

/-- **The window involution on transforms**: `(σ_A H)^(s) = e^{−(s − ½)A} Ĥ(1 − s)`. -/
theorem windowTransform_windowInvolution (A : ℝ) (H : ℝ → ℝ) (s : ℂ) :
    windowTransform (windowInvolution A H) s = windowMultiplier A s * windowTransform H (1 - s) := by
  unfold windowTransform windowInvolution windowMultiplier
  have h : (fun u : ℝ => ((H (-A - u) : ℝ) : ℂ) * cexp ((s - 1 / 2) * u)) =
      fun u => (fun v : ℝ => (H v : ℂ) * cexp ((s - 1 / 2) * ((-A - v : ℝ) : ℂ))) (-A - u) := by
    funext u; congr 3; push_cast; ring
  rw [h, integral_sub_left_eq_self (fun v : ℝ => (H v : ℂ) * cexp ((s - 1 / 2) * ((-A - v : ℝ) : ℂ)))
    volume (-A), ← integral_const_mul]
  congr 1
  funext v
  rw [mul_left_comm, ← Complex.exp_add]
  congr 2
  push_cast
  ring

/-- The multiplier has modulus `e^{−(Re s − ½)A}`. -/
theorem norm_windowMultiplier (A : ℝ) (s : ℂ) :
    ‖windowMultiplier A s‖ = Real.exp (-((s.re - 1 / 2) * A)) := by
  rw [windowMultiplier, Complex.norm_exp]
  congr 1
  simp

/-- **The fixed line of the window Frobenius at infinity**: for `A ≠ 0` the multiplier is unitary
exactly on `Re s = ½`. -/
theorem norm_windowMultiplier_eq_one_iff {A : ℝ} (hA : A ≠ 0) (s : ℂ) :
    ‖windowMultiplier A s‖ = 1 ↔ s.re = 1 / 2 := by
  rw [norm_windowMultiplier, Real.exp_eq_one_iff, neg_eq_zero, mul_eq_zero, sub_eq_zero]
  simp [hA]

/-- **Pair products are invariant**: `(σĤ)(s)(σĤ)(1 − s) = Ĥ(s)Ĥ(1 − s)`. -/
theorem windowTransform_windowInvolution_mul (A : ℝ) (H : ℝ → ℝ) (s : ℂ) :
    windowTransform (windowInvolution A H) s * windowTransform (windowInvolution A H) (1 - s) =
      windowTransform H s * windowTransform H (1 - s) := by
  rw [windowTransform_windowInvolution, windowTransform_windowInvolution, sub_sub_cancel]
  have hm : windowMultiplier A s * windowMultiplier A (1 - s) = 1 := by
    rw [windowMultiplier, windowMultiplier, ← Complex.exp_add, ← Complex.exp_zero]
    congr 1; ring
  linear_combination (windowTransform H (1 - s) * windowTransform H s) * hm

/-- The transform of a real test commutes with conjugation. -/
theorem windowTransform_conj (H : ℝ → ℝ) (s : ℂ) :
    windowTransform H (starRingEnd ℂ s) = starRingEnd ℂ (windowTransform H s) := by
  unfold windowTransform
  rw [← integral_conj]
  congr 1
  funext u
  rw [map_mul, Complex.conj_ofReal, ← Complex.exp_conj]
  congr 2
  simp only [map_sub, map_mul, Complex.conj_ofReal, map_div₀, map_one, map_ofNat]

/-- **On the critical line the involution preserves the modulus of every real transform.** -/
theorem norm_windowTransform_windowInvolution_of_re (A : ℝ) (H : ℝ → ℝ) {s : ℂ}
    (hs : s.re = 1 / 2) :
    ‖windowTransform (windowInvolution A H) s‖ = ‖windowTransform H s‖ := by
  have hconj : 1 - s = starRingEnd ℂ s := by
    apply Complex.ext <;> simp [hs]; norm_num
  rw [windowTransform_windowInvolution, norm_mul, hconj, windowTransform_conj, Complex.norm_conj,
    norm_windowMultiplier, hs, sub_self, zero_mul, neg_zero, Real.exp_zero, one_mul]

end GaloisForLFunctions.CohomologyOfWindowsOfSpecZ
