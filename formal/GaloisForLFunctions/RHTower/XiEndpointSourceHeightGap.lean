import GaloisForLFunctions.RHTower.XiEndpointCompletedValueBound

/-!
# The completed endpoint source creates an explicit Xi height gap

The exact completed prime--Gamma endpoint value is strictly below one half.  Combined with the
endpoint source-height law, this forces every multiplicity copy of every nontrivial Xi zero to
have squared height strictly larger than one.  The conclusion is lifted from multiplicity copies
to the actual Xi divisor and then to arbitrary zeros of `xi`.

In the centered spectral coordinate `XiC z = xi (1 / 2 + z * I)`, the zero height is the real
part of `z`.  Consequently `XiC` is unconditionally zero-free on the closed central slab
`|z.re| <= 1`.  This is a source-pure regularity domain: no zero enumeration, RH assumption,
real-rootedness, anti-Herglotz sign, or limiting measure is used.
-/

open Complex

namespace RHTower

noncomputable section

/-- The explicit endpoint source bound forces every Xi multiplicity copy above squared height
one. -/
theorem xiZeroCopy_one_lt_im_sq (q : XiZeroCopy) :
    1 < (q.1 : ℂ).im ^ (2 : ℕ) := by
  have hCpos : 0 < xiEndpointCompletedCurvature :=
    xiEndpointCompletedCurvature_pos
  have hCinv : 2 < 1 / xiEndpointCompletedCurvature := by
    rw [lt_div_iff₀ hCpos]
    nlinarith [xiEndpointCompletedCurvature_lt_one_half]
  have hheight := xiZeroCopy_im_sq_ge_endpoint_source_inverse_gap q
  linarith

/-- Absolute-height form of the explicit endpoint source gap. -/
theorem xiZeroCopy_one_lt_abs_im (q : XiZeroCopy) :
    1 < |(q.1 : ℂ).im| := by
  have hsq := xiZeroCopy_one_lt_im_sq q
  nlinarith [sq_abs ((q.1 : ℂ).im), abs_nonneg ((q.1 : ℂ).im)]

/-- The same strict squared-height gap on the actual Xi divisor support. -/
theorem xiDivisorSupport_one_lt_im_sq (ρ : XiDivisorSupport) :
    1 < (ρ : ℂ).im ^ (2 : ℕ) := by
  let q : XiZeroCopy := by
    have hpos := xi_divisor_pos_on_support ρ
    have hn : 0 < Int.toNat
        ((MeromorphicOn.divisor xi Set.univ) (ρ : ℂ)) := by
      omega
    exact ⟨ρ, ⟨0, hn⟩⟩
  simpa only [q] using xiZeroCopy_one_lt_im_sq q

/-- The completed endpoint value gives the explicit uniform divisor bound `1 < |Im rho|`. -/
theorem xiDivisorSupport_one_lt_abs_im (ρ : XiDivisorSupport) :
    1 < |(ρ : ℂ).im| := by
  have hsq := xiDivisorSupport_one_lt_im_sq ρ
  nlinarith [sq_abs ((ρ : ℂ).im), abs_nonneg ((ρ : ℂ).im)]

/-- Every zero of `xi`, without choosing a divisor enumeration, satisfies the explicit squared
height gap. -/
theorem one_lt_im_sq_of_xi_eq_zero {ρ : ℂ} (hzero : xi ρ = 0) :
    1 < ρ.im ^ (2 : ℕ) :=
  xiDivisorSupport_one_lt_im_sq
    ⟨ρ, mem_xi_divisor_support_of_eq_zero hzero⟩

/-- Absolute-height form for an arbitrary Xi zero. -/
theorem one_lt_abs_im_of_xi_eq_zero {ρ : ℂ} (hzero : xi ρ = 0) :
    1 < |ρ.im| :=
  xiDivisorSupport_one_lt_abs_im
    ⟨ρ, mem_xi_divisor_support_of_eq_zero hzero⟩

/-- Positive zero-free horizontal band for `xi`, derived from the completed endpoint source. -/
theorem xi_ne_zero_of_abs_im_le_one {ρ : ℂ} (hρ : |ρ.im| ≤ 1) :
    xi ρ ≠ 0 := by
  intro hzero
  exact (not_lt_of_ge hρ) (one_lt_abs_im_of_xi_eq_zero hzero)

/-- In the centered coordinate, the endpoint source creates a zero-free closed vertical slab. -/
theorem XiC_ne_zero_of_abs_re_le_one {z : ℂ} (hz : |z.re| ≤ 1) :
    XiC z ≠ 0 := by
  intro hzero
  have hheight : 1 < |(1 / 2 + z * I).im| := by
    exact one_lt_abs_im_of_xi_eq_zero hzero
  have him : (1 / 2 + z * I).im = z.re := by
    simp [mul_im]
  rw [him] at hheight
  exact (not_lt_of_ge hz) hheight

end

end RHTower
