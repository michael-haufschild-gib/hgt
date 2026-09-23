import GaloisForLFunctions.RHTower.Sieve.ChebyshevTwistLeftEdge
import GaloisForLFunctions.HTGeometry.SectorPowerMassLower

/-!
# The twisted main factor is `2π`

The two halves of the twisted residue are
`twistMainFactor d T τ` on the right line and `-twistMainFactor c T τ` on the left one, and their
sum has to be `2π` in the limit.  Quantitatively, with `T` beating the twist,

```text
‖ twistMainFactor d T τ - twistMainFactor c T τ - 2π ‖
      ≤  2(d-1)/(T-|τ|) + 2(1-c)/(T-|τ|) + 4T|τ|/(T-|τ|)² .
```

Two things are genuinely twisted here.  First, the effective truncation height is `T - |τ|`, not
`T`: the pole sits at height `-τ`, so the contour only surrounds it by that much.  Second, the
imaginary parts no longer cancel term by term — a symmetric truncation in `y` is asymmetric about
the pole — and the logarithm that survives is bounded only by the *relative* asymmetry `4T|τ|`
against the square of the effective height.  Both errors vanish exactly when `T/|τ| → ∞`, which is
the condition under which the twisted Chebyshev sum keeps a main term at all.
-/

namespace RHTower.Sieve

open Complex GaloisForLFunctions.HTGeometry

/-- **The arctangent gap across a symmetric truncation, seen from a positive horizontal offset.**
The gap is `π` up to twice the offset over the effective height `T - |τ|`. -/
theorem abs_arctan_gap_sub_pi_le {α T τ : ℝ} (hα : 0 < α) (hτ : |τ| < T) :
    |(Real.arctan ((T + τ) / α) - Real.arctan ((-T + τ) / α)) - Real.pi|
      ≤ 2 * α / (T - |τ|) := by
  obtain ⟨hlo, hhi⟩ := abs_lt.mp hτ
  have hT0 : (0 : ℝ) < T := lt_of_le_of_lt (abs_nonneg τ) hτ
  have hgap : (0 : ℝ) < T - |τ| := by linarith
  have hup : (0 : ℝ) < T + τ := by linarith
  have hdn : (-T + τ : ℝ) < 0 := by linarith
  have hu : (0 : ℝ) < (T + τ) / α := by positivity
  have hv : ((-T + τ) / α : ℝ) < 0 := div_neg_of_neg_of_pos hdn hα
  have heu : Real.arctan ((T + τ) / α)
      = Real.pi / 2 - Real.arctan (((T + τ) / α)⁻¹) := by
    rw [Real.arctan_inv_of_pos hu]; ring
  have hev : Real.arctan ((-T + τ) / α)
      = -(Real.pi / 2) - Real.arctan (((-T + τ) / α)⁻¹) := by
    rw [Real.arctan_inv_of_neg hv]; ring
  have hiu : (((T + τ) / α)⁻¹ : ℝ) = α / (T + τ) := inv_div _ _
  have hiv : (((-T + τ) / α)⁻¹ : ℝ) = α / (-T + τ) := inv_div _ _
  have hbu : |Real.arctan (α / (T + τ))| ≤ α / (T - |τ|) := by
    refine le_trans (abs_arctan_le_abs _) ?_
    rw [abs_div, abs_of_pos hα, abs_of_pos hup]
    have hle : T - |τ| ≤ T + τ := by
      have := neg_abs_le τ
      linarith
    exact div_le_div_of_nonneg_left hα.le hgap hle
  have hbv : |Real.arctan (α / (-T + τ))| ≤ α / (T - |τ|) := by
    refine le_trans (abs_arctan_le_abs _) ?_
    rw [abs_div, abs_of_pos hα, abs_of_neg hdn]
    have hle : T - |τ| ≤ -(-T + τ) := by
      have := le_abs_self τ
      linarith
    exact div_le_div_of_nonneg_left hα.le hgap hle
  have hkey : (Real.arctan ((T + τ) / α) - Real.arctan ((-T + τ) / α)) - Real.pi
      = -Real.arctan (α / (T + τ)) + Real.arctan (α / (-T + τ)) := by
    rw [heu, hev, hiu, hiv]; ring
  rw [hkey]
  have h1 := abs_le.mp hbu
  have h2 := abs_le.mp hbv
  rw [abs_le]
  constructor
  · have : (2 : ℝ) * α / (T - |τ|) = α / (T - |τ|) + α / (T - |τ|) := by ring
    rw [this]; linarith [h1.1, h1.2, h2.1, h2.2]
  · have : (2 : ℝ) * α / (T - |τ|) = α / (T - |τ|) + α / (T - |τ|) := by ring
    rw [this]; linarith [h1.1, h1.2, h2.1, h2.2]

/-- **The same gap from a negative horizontal offset**, where it is `-π` instead. -/
theorem abs_arctan_gap_add_pi_le {α T τ : ℝ} (hα : α < 0) (hτ : |τ| < T) :
    |(Real.arctan ((T + τ) / α) - Real.arctan ((-T + τ) / α)) + Real.pi|
      ≤ 2 * (-α) / (T - |τ|) := by
  have hα' : (0 : ℝ) < -α := by linarith
  have h := abs_arctan_gap_sub_pi_le hα' hτ
  have e1 : (T + τ) / α = -((T + τ) / (-α)) := by field_simp
  have e2 : (-T + τ) / α = -((-T + τ) / (-α)) := by field_simp
  rw [e1, e2, Real.arctan_neg, Real.arctan_neg]
  have hrw : -Real.arctan ((T + τ) / (-α)) - -Real.arctan ((-T + τ) / (-α)) + Real.pi
      = -((Real.arctan ((T + τ) / (-α)) - Real.arctan ((-T + τ) / (-α))) - Real.pi) := by ring
  rw [hrw, abs_neg]
  exact h

/-- **The logarithmic half of the twisted main factor.**  A symmetric truncation is asymmetric about
the twisted pole; the residual logarithm is the relative asymmetry `4T|τ|` against the square of the
effective height. -/
theorem abs_log_gap_le {α T τ : ℝ} (hτ : |τ| < T) :
    |(Real.log (α ^ (2 : ℕ) + (T + τ) ^ (2 : ℕ)) - Real.log (α ^ (2 : ℕ) + (-T + τ) ^ (2 : ℕ))) / 2|
      ≤ 2 * T * |τ| / (T - |τ|) ^ (2 : ℕ) := by
  have hT0 : (0 : ℝ) < T := lt_of_le_of_lt (abs_nonneg τ) hτ
  have hgap : (0 : ℝ) < T - |τ| := by linarith
  have hsq : (0 : ℝ) < (T - |τ|) ^ (2 : ℕ) := by positivity
  have hup : (T - |τ| : ℝ) ≤ T + τ := by linarith [neg_abs_le τ]
  have hdn : (T - |τ| : ℝ) ≤ -(-T + τ) := by linarith [le_abs_self τ]
  have hpq : ((T - |τ|) ^ (2 : ℕ) : ℝ) ≤ α ^ (2 : ℕ) + (T + τ) ^ (2 : ℕ) := by nlinarith [sq_nonneg α]
  have hqq : ((T - |τ|) ^ (2 : ℕ) : ℝ) ≤ α ^ (2 : ℕ) + (-T + τ) ^ (2 : ℕ) := by nlinarith [sq_nonneg α]
  have hp0 : (0 : ℝ) < α ^ (2 : ℕ) + (T + τ) ^ (2 : ℕ) := lt_of_lt_of_le hsq hpq
  have hq0 : (0 : ℝ) < α ^ (2 : ℕ) + (-T + τ) ^ (2 : ℕ) := lt_of_lt_of_le hsq hqq
  have hdiff : (α ^ (2 : ℕ) + (T + τ) ^ (2 : ℕ)) - (α ^ (2 : ℕ) + (-T + τ) ^ (2 : ℕ)) = 4 * T * τ := by ring
  have habs : |4 * T * τ| = 4 * T * |τ| := by
    rw [abs_mul, abs_mul, abs_of_pos hT0, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 4)]
  have hbound : ∀ p q : ℝ, 0 < p → 0 < q → ((T - |τ|) ^ (2 : ℕ) : ℝ) ≤ q →
      Real.log p - Real.log q ≤ |p - q| / (T - |τ|) ^ (2 : ℕ) := by
    intro p q hp hq hqlow
    have h := Real.log_le_sub_one_of_pos (x := p / q) (by positivity)
    rw [Real.log_div hp.ne' hq.ne'] at h
    have he : p / q - 1 = (p - q) / q := by field_simp
    rw [he] at h
    have h2 : (p - q) / q ≤ |p - q| / q :=
      div_le_div_of_nonneg_right (le_abs_self _) hq.le
    have h3 : |p - q| / q ≤ |p - q| / (T - |τ|) ^ (2 : ℕ) :=
      div_le_div_of_nonneg_left (abs_nonneg _) hsq hqlow
    linarith
  have h1 := hbound (α ^ (2 : ℕ) + (T + τ) ^ (2 : ℕ)) (α ^ (2 : ℕ) + (-T + τ) ^ (2 : ℕ)) hp0 hq0 hqq
  have h2 := hbound (α ^ (2 : ℕ) + (-T + τ) ^ (2 : ℕ)) (α ^ (2 : ℕ) + (T + τ) ^ (2 : ℕ)) hq0 hp0 hpq
  rw [hdiff, habs] at h1
  have hdiff' : (α ^ (2 : ℕ) + (-T + τ) ^ (2 : ℕ)) - (α ^ (2 : ℕ) + (T + τ) ^ (2 : ℕ)) = -(4 * T * τ) := by ring
  rw [hdiff', abs_neg, habs] at h2
  have hkey : |Real.log (α ^ (2 : ℕ) + (T + τ) ^ (2 : ℕ)) - Real.log (α ^ (2 : ℕ) + (-T + τ) ^ (2 : ℕ))|
      ≤ 4 * T * |τ| / (T - |τ|) ^ (2 : ℕ) := abs_le.2 ⟨by linarith, by linarith⟩
  have hhalf : (4 : ℝ) * T * |τ| / (T - |τ|) ^ (2 : ℕ) / 2 = 2 * T * |τ| / (T - |τ|) ^ (2 : ℕ) := by
    ring
  rw [abs_div, abs_two, ← hhalf]
  exact div_le_div_of_nonneg_right hkey (by norm_num)

/-- **The twisted main factor is `2π`, quantitatively.**  Both halves of the residue are needed and
both are computed about the twisted pole; what separates them from `2π` is the offset of each line
from the abscissa and the asymmetry of the truncation about the pole. -/
theorem norm_twistMainFactor_gap_sub_two_pi_le {c d T τ : ℝ} (hc : c < 1) (hd : 1 < d)
    (hτ : |τ| < T) :
    ‖twistMainFactor d T τ - twistMainFactor c T τ - ((2 * Real.pi : ℝ) : ℂ)‖
      ≤ 2 * (d - 1) / (T - |τ|) + 2 * (1 - c) / (T - |τ|)
        + 4 * T * |τ| / (T - |τ|) ^ (2 : ℕ) := by
  have hT0 : (0 : ℝ) < T := lt_of_le_of_lt (abs_nonneg τ) hτ
  have hgap : (0 : ℝ) < T - |τ| := by linarith
  have hre : (twistMainFactor d T τ - twistMainFactor c T τ
        - ((2 * Real.pi : ℝ) : ℂ)).re
      = ((Real.arctan ((T + τ) / (d - 1)) - Real.arctan ((-T + τ) / (d - 1))) - Real.pi)
        - ((Real.arctan ((T + τ) / (c - 1)) - Real.arctan ((-T + τ) / (c - 1))) + Real.pi) := by
    simp only [twistMainFactor, Complex.sub_re, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, Complex.I_re, Complex.I_im]
    ring
  have him : (twistMainFactor d T τ - twistMainFactor c T τ
        - ((2 * Real.pi : ℝ) : ℂ)).im
      = -((Real.log ((d - 1) ^ (2 : ℕ) + (T + τ) ^ (2 : ℕ))
              - Real.log ((d - 1) ^ (2 : ℕ) + (-T + τ) ^ (2 : ℕ))) / 2)
        + ((Real.log ((c - 1) ^ (2 : ℕ) + (T + τ) ^ (2 : ℕ))
              - Real.log ((c - 1) ^ (2 : ℕ) + (-T + τ) ^ (2 : ℕ))) / 2) := by
    simp only [twistMainFactor, Complex.sub_im, Complex.mul_im, Complex.ofReal_re,
      Complex.ofReal_im, Complex.I_re, Complex.I_im]
    ring
  have hd1 : (0 : ℝ) < d - 1 := by linarith
  have hc1 : (c - 1 : ℝ) < 0 := by linarith
  have hA := abs_arctan_gap_sub_pi_le (α := d - 1) hd1 hτ
  have hB := abs_arctan_gap_add_pi_le (α := c - 1) hc1 hτ
  have hC := abs_log_gap_le (α := d - 1) (T := T) (τ := τ) hτ
  have hD := abs_log_gap_le (α := c - 1) (T := T) (τ := τ) hτ
  have hBrw : (2 : ℝ) * (-(c - 1)) / (T - |τ|) = 2 * (1 - c) / (T - |τ|) := by ring
  rw [hBrw] at hB
  have hreb : |(twistMainFactor d T τ - twistMainFactor c T τ - ((2 * Real.pi : ℝ) : ℂ)).re|
      ≤ 2 * (d - 1) / (T - |τ|) + 2 * (1 - c) / (T - |τ|) := by
    rw [hre]
    exact le_trans (abs_sub _ _) (by linarith)
  have himb : |(twistMainFactor d T τ - twistMainFactor c T τ - ((2 * Real.pi : ℝ) : ℂ)).im|
      ≤ 4 * T * |τ| / (T - |τ|) ^ (2 : ℕ) := by
    rw [him]
    refine le_trans (abs_add_le _ _) ?_
    rw [abs_neg]
    have : (4 : ℝ) * T * |τ| / (T - |τ|) ^ (2 : ℕ)
        = 2 * T * |τ| / (T - |τ|) ^ (2 : ℕ) + 2 * T * |τ| / (T - |τ|) ^ (2 : ℕ) := by ring
    rw [this]
    linarith [hC, hD]
  exact le_trans (Complex.norm_le_abs_re_add_abs_im _) (by linarith)

end RHTower.Sieve
