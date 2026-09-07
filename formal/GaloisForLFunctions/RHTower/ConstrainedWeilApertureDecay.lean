import GaloisForLFunctions.RHTower.ConstrainedWeilApertureConstantTerm

/-!
# Decay norms of the normalised ray-term polynomials

For a copy `q` that is *far* from the centre in ordinate (`|Re z_q − γ| ≥ 1` and `|Re z_q + γ| ≥ 1`)
every nonzero sum of two exponents of the `−Θ`-shifted pair polynomial has modulus at least
`m₀ = min 1 (min Θ g)`, where `g` is a positive lower bound for `|Re z_q|` and `|γ|`: the imaginary
parts of such sums are `±2ν₁, ±ν₁, ±2ν₂, ±ν₂, ±2 Re z_q, ±2γ` (all of modulus `≥ min 1 g` up to the
factor `2`), and when the imaginary part vanishes the real part is `−2Θ`.  Together with the
coefficient bounds `‖κ(c)‖, ‖ρ(c)‖ ≤ M e^{|Re c|/4}/‖c‖ ≤ M e^{Θ/4}` (as `‖c‖ ≥ |Im c| ≥ 1`) this gives
`decayNorm (normalizedRayTermPoly Θ γ q) ≤ (8 M e^{Θ/4})² / (4 m₀ ‖z_q‖²)` for far copies, which is
summable over the copies.
-/

open MeasureTheory Complex Set
open GaloisForLFunctions.HTGeometry

namespace RHTower

noncomputable section

theorem norm_ge_of_abs_re {m : ℝ} {x : ℂ} (h : m ≤ |x.re|) : m ≤ ‖x‖ :=
  h.trans (Complex.abs_re_le_norm x)

theorem norm_ge_of_abs_im {m : ℝ} {x : ℂ} (h : m ≤ |x.im|) : m ≤ ‖x‖ :=
  h.trans (Complex.abs_im_le_norm x)

/-- A copy is far from the centre `γ` when both `|Re z_q − γ| ≥ 1` and `|Re z_q + γ| ≥ 1`. -/
def FarFromCentre (γ : ℝ) (q : XiZeroCopy) : Prop :=
  1 ≤ |(xiSpectralPoint q).re - γ| ∧ 1 ≤ |(xiSpectralPoint q).re + γ|

/-- **Exponent-sum lower bound for far copies.**  With `m₀ = min 1 (min Θ g)`, `g ≤ |Re z_q|`,
`g ≤ |γ|`, `|Im z_q| ≤ Θ`, every nonzero sum of two exponents of the shifted pair polynomial has
modulus at least `m₀`. -/
theorem shiftedPairPoly_pairSum_norm_ge {Θ g γ : ℝ} (hΘ : 0 < Θ) (hg : 0 < g) {q : XiZeroCopy}
    (hq : |(xiSpectralPoint q).im| ≤ Θ) (hz : g ≤ |(xiSpectralPoint q).re|) (hγ : g ≤ |γ|)
    (hfar : FarFromCentre γ q) :
    ∀ p ∈ shiftedPairPoly Θ γ q, ∀ r ∈ shiftedPairPoly Θ γ q,
      p.2 + r.2 ≠ 0 → min 1 (min Θ g) ≤ ‖p.2 + r.2‖ := by
  have hc₁ : rayFreq₁ γ q ≠ 0 := by
    intro h
    have := congrArg Complex.im h
    rw [rayFreq₁_im, Complex.zero_im] at this
    have h1 := hfar.1
    rw [this, abs_zero] at h1
    linarith
  have hc₂ : rayFreq₂ γ q ≠ 0 := by
    intro h
    have := congrArg Complex.im h
    rw [rayFreq₂_im, Complex.zero_im] at this
    have h1 := hfar.2
    rw [this, abs_zero] at h1
    linarith
  rw [shiftedPairPoly_explicit Θ γ hc₁ hc₂]
  intro p hp r hr _
  have hm0 : 0 ≤ min 1 (min Θ g) := le_min zero_le_one (le_min hΘ.le hg.le)
  have hm1 : min 1 (min Θ g) ≤ 1 := min_le_left _ _
  have hmΘ : min 1 (min Θ g) ≤ Θ := (min_le_right _ _).trans (min_le_left _ _)
  have hmg : min 1 (min Θ g) ≤ g := (min_le_right _ _).trans (min_le_right _ _)
  have hm1sq : (min 1 (min Θ g)) ^ 2 ≤ 1 := by nlinarith
  have hmgsq : (min 1 (min Θ g)) ^ 2 ≤ g ^ 2 := by nlinarith
  have hb := abs_le.mp hq
  have hν₁sq : 1 ≤ ((xiSpectralPoint q).re - γ) ^ 2 := by
    have := pow_le_pow_left₀ zero_le_one hfar.1 2
    rwa [one_pow, sq_abs] at this
  have hν₂sq : 1 ≤ ((xiSpectralPoint q).re + γ) ^ 2 := by
    have := pow_le_pow_left₀ zero_le_one hfar.2 2
    rwa [one_pow, sq_abs] at this
  have hzsq : g ^ 2 ≤ (xiSpectralPoint q).re ^ 2 := by
    have := pow_le_pow_left₀ hg.le hz 2
    rwa [sq_abs] at this
  have hγsq : g ^ 2 ≤ γ ^ 2 := by
    have := pow_le_pow_left₀ hg.le hγ 2
    rwa [sq_abs] at this
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp hr
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    first
    | exact norm_ge_of_abs_re (by
        simp only [Complex.add_re, Complex.neg_re, Complex.ofReal_re, Complex.zero_re,
          rayFreq₁_re, rayFreq₂_re]
        exact le_abs.mpr (Or.inr (by linarith)))
    | exact norm_ge_of_abs_im ((abs_of_nonneg hm0).symm.le.trans (sq_le_sq.mp (by
        simp only [Complex.add_im, Complex.neg_im, Complex.ofReal_im, rayFreq₁_im, rayFreq₂_im]
        nlinarith [hν₁sq, hν₂sq, hzsq, hγsq, hm1sq, hmgsq])))

end

end RHTower
