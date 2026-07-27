import GaloisForLFunctions.HTGeometry.GammaComplexLatticeCharge

/-!
# Gamma--Meixner alien-charge polarization

The Gamma--Meixner density has two pole-oriented affine Gamma factors
`Γ(a + λs)` and `Γ(a - λs)`.  This module proves the exact finite complex-charge flow between
their symmetric product and chiral quotient.  At lattice frequency `kλ`, the symmetric and chiral
charges are the sine and cosine components of one conserved norm.

At the singular time-zero endpoint, the symmetric charge vanishes while the chiral charge is
`2λ`.  This is the algebraic core of the source-selected Euler endpoint: the intensity becomes
charge-neutral, but the pole-oriented phase retains the complete charge.

No analytic Gamma identity, Borel continuation, hypertranscendence theorem, or limit theorem is
hidden here.
-/

namespace GaloisForLFunctions.HTGeometry

/-- Positive pole-oriented factor `Γ(a + λs)` in a Gamma--Meixner spectral density. -/
def gammaMeixnerPositiveFactor
    (lam : ℂ) (hlam : lam ≠ 0) (a : ℝ) : ComplexAffineGammaFactor where
  slope := lam
  offset := a
  multiplicity := 1
  slope_ne_zero := hlam

/-- Negative pole-oriented factor `Γ(a - λs)` in the symmetric Gamma--Meixner density. -/
def gammaMeixnerSymmetricNegativeFactor
    (lam : ℂ) (hlam : lam ≠ 0) (a : ℝ) : ComplexAffineGammaFactor where
  slope := -lam
  offset := a
  multiplicity := 1
  slope_ne_zero := neg_ne_zero.mpr hlam

/-- Inverse negative factor `Γ(a - λs)⁻¹` in the chiral Gamma--Meixner quotient. -/
def gammaMeixnerChiralNegativeFactor
    (lam : ℂ) (hlam : lam ≠ 0) (a : ℝ) : ComplexAffineGammaFactor where
  slope := -lam
  offset := a
  multiplicity := -1
  slope_ne_zero := neg_ne_zero.mpr hlam

/-- Complex alien charge of the symmetric density
`Γ(a + λs) Γ(a - λs)`. -/
noncomputable def gammaMeixnerSymmetricChargeAt
    (lam : ℂ) (hlam : lam ≠ 0) (a : ℝ) (t : ℂ) : ℂ :=
  complexGammaFactorChargeAt (gammaMeixnerPositiveFactor lam hlam a) t +
    complexGammaFactorChargeAt (gammaMeixnerSymmetricNegativeFactor lam hlam a) t

/-- Complex alien charge of the pole-oriented chiral quotient
`Γ(a + λs) / Γ(a - λs)`. -/
noncomputable def gammaMeixnerChiralChargeAt
    (lam : ℂ) (hlam : lam ≠ 0) (a : ℝ) (t : ℂ) : ℂ :=
  complexGammaFactorChargeAt (gammaMeixnerPositiveFactor lam hlam a) t +
    complexGammaFactorChargeAt (gammaMeixnerChiralNegativeFactor lam hlam a) t

private theorem gammaMeixner_lattice_ratio_pos
    (lam : ℂ) (hlam : lam ≠ 0) (k : ℤ) :
    (k : ℂ) * lam / lam = (k : ℂ) := by
  field_simp

private theorem gammaMeixner_lattice_ratio_neg
    (lam : ℂ) (hlam : lam ≠ 0) (k : ℤ) :
    (k : ℂ) * lam / -lam = ((-k : ℤ) : ℂ) := by
  apply (div_eq_iff (neg_ne_zero.mpr hlam)).2
  rw [Int.cast_neg]
  ring

/-- Exponential form of the symmetric Gamma--Meixner charge. -/
theorem gammaMeixnerSymmetricChargeAt_integer_exp
    (lam : ℂ) (hlam : lam ≠ 0) (a : ℝ) (k : ℤ) (hk : k ≠ 0) :
    gammaMeixnerSymmetricChargeAt lam hlam a ((k : ℂ) * lam) =
      lam * Complex.exp
          (-2 * (Real.pi : ℂ) * Complex.I * (k : ℂ) * (a : ℂ)) -
        lam * Complex.exp
          (2 * (Real.pi : ℂ) * Complex.I * (k : ℂ) * (a : ℂ)) := by
  unfold gammaMeixnerSymmetricChargeAt complexGammaFactorChargeAt
    gammaMeixnerPositiveFactor gammaMeixnerSymmetricNegativeFactor
  rw [if_pos ⟨k, hk, rfl⟩]
  rw [if_pos (show (k : ℂ) * lam ∈ complexGammaIntegerLattice (-lam) by
    refine ⟨-k, neg_ne_zero.mpr hk, ?_⟩
    rw [Int.cast_neg]
    ring)]
  rw [gammaMeixner_lattice_ratio_pos lam hlam k,
    gammaMeixner_lattice_ratio_neg lam hlam k]
  norm_num only [Int.cast_one, Int.cast_neg]
  ring

/-- Exponential form of the chiral Gamma--Meixner charge. -/
theorem gammaMeixnerChiralChargeAt_integer_exp
    (lam : ℂ) (hlam : lam ≠ 0) (a : ℝ) (k : ℤ) (hk : k ≠ 0) :
    gammaMeixnerChiralChargeAt lam hlam a ((k : ℂ) * lam) =
      lam * Complex.exp
          (-2 * (Real.pi : ℂ) * Complex.I * (k : ℂ) * (a : ℂ)) +
        lam * Complex.exp
          (2 * (Real.pi : ℂ) * Complex.I * (k : ℂ) * (a : ℂ)) := by
  unfold gammaMeixnerChiralChargeAt complexGammaFactorChargeAt
    gammaMeixnerPositiveFactor gammaMeixnerChiralNegativeFactor
  rw [if_pos ⟨k, hk, rfl⟩]
  rw [if_pos (show (k : ℂ) * lam ∈ complexGammaIntegerLattice (-lam) by
    refine ⟨-k, neg_ne_zero.mpr hk, ?_⟩
    rw [Int.cast_neg]
    ring)]
  rw [gammaMeixner_lattice_ratio_pos lam hlam k,
    gammaMeixner_lattice_ratio_neg lam hlam k]
  norm_num only [Int.cast_one, Int.cast_neg]
  ring

/-- The symmetric charge is the sine component of the pole polarization. -/
theorem gammaMeixnerSymmetricChargeAt_integer
    (lam : ℂ) (hlam : lam ≠ 0) (a : ℝ) (k : ℤ) (hk : k ≠ 0) :
    gammaMeixnerSymmetricChargeAt lam hlam a ((k : ℂ) * lam) =
      -2 * Complex.I * lam *
        (Real.sin (2 * Real.pi * (k : ℝ) * a) : ℂ) := by
  rw [gammaMeixnerSymmetricChargeAt_integer_exp lam hlam a k hk]
  rw [show -2 * (Real.pi : ℂ) * Complex.I * (k : ℂ) * (a : ℂ) =
      -(2 * (Real.pi : ℂ) * (k : ℂ) * (a : ℂ)) * Complex.I by ring]
  rw [show 2 * (Real.pi : ℂ) * Complex.I * (k : ℂ) * (a : ℂ) =
      (2 * (Real.pi : ℂ) * (k : ℂ) * (a : ℂ)) * Complex.I by ring]
  rw [Complex.ofReal_sin]
  rw [show ((2 * Real.pi * (k : ℝ) * a : ℝ) : ℂ) =
      2 * (Real.pi : ℂ) * (k : ℂ) * (a : ℂ) by push_cast; ring]
  rw [Complex.sin]
  ring_nf
  rw [Complex.I_sq]
  ring

/-- The chiral charge is the cosine component of the pole polarization. -/
theorem gammaMeixnerChiralChargeAt_integer
    (lam : ℂ) (hlam : lam ≠ 0) (a : ℝ) (k : ℤ) (hk : k ≠ 0) :
    gammaMeixnerChiralChargeAt lam hlam a ((k : ℂ) * lam) =
      2 * lam * (Real.cos (2 * Real.pi * (k : ℝ) * a) : ℂ) := by
  rw [gammaMeixnerChiralChargeAt_integer_exp lam hlam a k hk]
  rw [show -2 * (Real.pi : ℂ) * Complex.I * (k : ℂ) * (a : ℂ) =
      -(2 * (Real.pi : ℂ) * (k : ℂ) * (a : ℂ)) * Complex.I by ring]
  rw [show 2 * (Real.pi : ℂ) * Complex.I * (k : ℂ) * (a : ℂ) =
      (2 * (Real.pi : ℂ) * (k : ℂ) * (a : ℂ)) * Complex.I by ring]
  rw [Complex.ofReal_cos]
  rw [show ((2 * Real.pi * (k : ℝ) * a : ℝ) : ℂ) =
      2 * (Real.pi : ℂ) * (k : ℂ) * (a : ℂ) by push_cast; ring]
  rw [Complex.cos]
  ring

/-- **Alien-charge polarization conservation.** At every nonzero lattice frequency, the
norm-squares of the symmetric and chiral charge components sum to the fixed value `4‖λ‖²`. -/
theorem gammaMeixnerCharge_normSq_conservation
    (lam : ℂ) (hlam : lam ≠ 0) (a : ℝ) (k : ℤ) (hk : k ≠ 0) :
    Complex.normSq
          (gammaMeixnerSymmetricChargeAt lam hlam a ((k : ℂ) * lam)) +
        Complex.normSq
          (gammaMeixnerChiralChargeAt lam hlam a ((k : ℂ) * lam)) =
      4 * Complex.normSq lam := by
  rw [gammaMeixnerSymmetricChargeAt_integer lam hlam a k hk,
    gammaMeixnerChiralChargeAt_integer lam hlam a k hk]
  simp only [map_mul, Complex.normSq_ofReal, Complex.normSq_I]
  have htrig := Real.sin_sq_add_cos_sq (2 * Real.pi * (k : ℝ) * a)
  norm_num
  calc
    4 * Complex.normSq lam *
          (Real.sin (2 * Real.pi * (k : ℝ) * a) *
            Real.sin (2 * Real.pi * (k : ℝ) * a)) +
        4 * Complex.normSq lam *
          (Real.cos (2 * Real.pi * (k : ℝ) * a) *
            Real.cos (2 * Real.pi * (k : ℝ) * a)) =
        4 * Complex.normSq lam *
          (Real.sin (2 * Real.pi * (k : ℝ) * a) ^ 2 +
            Real.cos (2 * Real.pi * (k : ℝ) * a) ^ 2) := by ring
    _ = 4 * Complex.normSq lam := by rw [htrig]; ring

/-- Scale-free symmetric charge. Division by `2λ` removes the arbitrary affine coordinate scale
and retains only the pole-polarization component. -/
noncomputable def gammaMeixnerNormalizedSymmetricChargeAt
    (lam : ℂ) (hlam : lam ≠ 0) (a : ℝ) (t : ℂ) : ℂ :=
  gammaMeixnerSymmetricChargeAt lam hlam a t / (2 * lam)

/-- Scale-free chiral charge. -/
noncomputable def gammaMeixnerNormalizedChiralChargeAt
    (lam : ℂ) (hlam : lam ≠ 0) (a : ℝ) (t : ℂ) : ℂ :=
  gammaMeixnerChiralChargeAt lam hlam a t / (2 * lam)

/-- Coordinate-free form of charge conservation: the two normalized polarization components form
a unit vector at every nonzero lattice frequency. -/
theorem gammaMeixnerNormalizedCharge_normSq_add_eq_one
    (lam : ℂ) (hlam : lam ≠ 0) (a : ℝ) (k : ℤ) (hk : k ≠ 0) :
    Complex.normSq
          (gammaMeixnerNormalizedSymmetricChargeAt
            lam hlam a ((k : ℂ) * lam)) +
        Complex.normSq
          (gammaMeixnerNormalizedChiralChargeAt
            lam hlam a ((k : ℂ) * lam)) =
      1 := by
  rw [gammaMeixnerNormalizedSymmetricChargeAt,
    gammaMeixnerNormalizedChiralChargeAt,
    Complex.normSq_div, Complex.normSq_div, ← add_div,
    gammaMeixnerCharge_normSq_conservation lam hlam a k hk]
  have hnorm : Complex.normSq lam ≠ 0 :=
    (Complex.normSq_eq_zero.not).mpr hlam
  rw [show Complex.normSq (2 * lam) = 4 * Complex.normSq lam by
    norm_num only [map_mul, Complex.normSq_ofNat]]
  field_simp

/-- Every finite source packet remains exactly isometric after splitting each amplitude into its
normalized symmetric and chiral Gamma--Meixner charge components. -/
theorem finiteGammaMeixnerNormalizedCharge_isometry
    {d : ℕ} (lam : Fin d → ℂ) (hlam : ∀ i, lam i ≠ 0)
    (weight : Fin d → ℂ) (a : ℝ) (k : ℤ) (hk : k ≠ 0) :
    ∑ i, (Complex.normSq
            (weight i *
              gammaMeixnerNormalizedSymmetricChargeAt
                (lam i) (hlam i) a ((k : ℂ) * lam i)) +
          Complex.normSq
            (weight i *
              gammaMeixnerNormalizedChiralChargeAt
                (lam i) (hlam i) a ((k : ℂ) * lam i))) =
      ∑ i, Complex.normSq (weight i) := by
  apply Finset.sum_congr rfl
  intro i _
  simp only [map_mul]
  rw [← mul_add,
    gammaMeixnerNormalizedCharge_normSq_add_eq_one (lam i) (hlam i) a k hk,
    mul_one]

/-- At the singular time-zero endpoint, every symmetric lattice charge vanishes. -/
theorem gammaMeixnerSymmetricChargeAt_zero_integer
    (lam : ℂ) (hlam : lam ≠ 0) (k : ℤ) (hk : k ≠ 0) :
    gammaMeixnerSymmetricChargeAt lam hlam 0 ((k : ℂ) * lam) = 0 := by
  rw [gammaMeixnerSymmetricChargeAt_integer_exp lam hlam 0 k hk]
  simp

/-- At the same endpoint, the pole-oriented chiral factor retains the full doubled charge. -/
theorem gammaMeixnerChiralChargeAt_zero_integer
    (lam : ℂ) (hlam : lam ≠ 0) (k : ℤ) (hk : k ≠ 0) :
    gammaMeixnerChiralChargeAt lam hlam 0 ((k : ℂ) * lam) = 2 * lam := by
  rw [gammaMeixnerChiralChargeAt_integer_exp lam hlam 0 k hk]
  simp
  ring

theorem gammaMeixnerChiralChargeAt_zero_integer_ne_zero
    (lam : ℂ) (hlam : lam ≠ 0) (k : ℤ) (hk : k ≠ 0) :
    gammaMeixnerChiralChargeAt lam hlam 0 ((k : ℂ) * lam) ≠ 0 := by
  rw [gammaMeixnerChiralChargeAt_zero_integer lam hlam k hk]
  exact mul_ne_zero (by norm_num) hlam

/-- The normalized time-zero endpoint is the pure chiral unit vector `(0,1)`. -/
theorem gammaMeixnerNormalizedChargeAt_zero_integer
    (lam : ℂ) (hlam : lam ≠ 0) (k : ℤ) (hk : k ≠ 0) :
    gammaMeixnerNormalizedSymmetricChargeAt
          lam hlam 0 ((k : ℂ) * lam) = 0 ∧
      gammaMeixnerNormalizedChiralChargeAt
          lam hlam 0 ((k : ℂ) * lam) = 1 := by
  constructor
  · rw [gammaMeixnerNormalizedSymmetricChargeAt,
      gammaMeixnerSymmetricChargeAt_zero_integer lam hlam k hk, zero_div]
  · rw [gammaMeixnerNormalizedChiralChargeAt,
      gammaMeixnerChiralChargeAt_zero_integer lam hlam k hk]
    field_simp

/-- At Gamma--Meixner time `θ`, the first symmetric charge is the sine component
`-2iλ sin(πθ/2)`. -/
theorem gammaMeixnerSymmetricChargeAt_time_slope
    (lam : ℂ) (hlam : lam ≠ 0) (theta : ℝ) :
    gammaMeixnerSymmetricChargeAt lam hlam (theta / 4) lam =
      -2 * Complex.I * lam * (Real.sin (Real.pi * theta / 2) : ℂ) := by
  have h :=
    gammaMeixnerSymmetricChargeAt_integer lam hlam (theta / 4) 1 (by norm_num)
  have hangle :
      2 * Real.pi * (1 : ℝ) * (theta / 4) = Real.pi * theta / 2 := by
    ring
  simpa only [Int.cast_one, one_mul, hangle] using h

/-- Every interior convolution time `0 < θ < 2` has nonzero symmetric charge. Its disappearance
at `θ=0` is therefore a genuine boundary collapse, not charge-neutrality of the interior family. -/
theorem gammaMeixnerSymmetricChargeAt_time_slope_ne_zero
    (lam : ℂ) (hlam : lam ≠ 0) {theta : ℝ}
    (htheta0 : 0 < theta) (htheta2 : theta < 2) :
    gammaMeixnerSymmetricChargeAt lam hlam (theta / 4) lam ≠ 0 := by
  rw [gammaMeixnerSymmetricChargeAt_time_slope lam hlam theta]
  have harg0 : 0 < Real.pi * theta / 2 := by positivity
  have hargpi : Real.pi * theta / 2 < Real.pi := by
    nlinarith [Real.pi_pos]
  have hsin : Real.sin (Real.pi * theta / 2) ≠ 0 :=
    ne_of_gt (Real.sin_pos_of_pos_of_lt_pi harg0 hargpi)
  exact mul_ne_zero
    (mul_ne_zero (mul_ne_zero (by norm_num) Complex.I_ne_zero) hlam)
    (Complex.ofReal_ne_zero.mpr hsin)

end GaloisForLFunctions.HTGeometry
