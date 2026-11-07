import GaloisForLFunctions.RHTower.ZetaSelfReturnThresholdIsTheDistanceToNonvanishingTargets
import GaloisForLFunctions.RHTower.ZetaSelfReturnThresholdReadsTheVanishingOrder
import GaloisForLFunctions.RHTower.ZetaStrongRecurrenceReceiver

/-!
# The transport count of a zero

Transport moves a zero by a vertical return. A return of strength `m/2` on an isolating disc of radius `r`
puts a zero of `ζ` in the translated disc, and one zero serves returns of measure at most `2r`. So the
returns in `[0, T]` have measure at most `2r` times the number of zeros in the translated strip: **the return
exponent is at most the density exponent.**

In the other direction, the return exponent reads the zero exactly:

* a point of the strip is a zero iff on each disc some tolerance has return exponent below `1`;
* at a zero of order `D` with cofactor `g`, the exponent is below `1` under the tolerance `|g(z₀)| r^D/4`, and
  it is `1` above the tolerance `4·3^D |g(z₀)| r^D`.

So the exponent jumps at a tolerance of size `r^D`. A return at a zero is a scarce event below that
tolerance, and an abundant one above it. Transport by itself therefore produces no contradiction: returns
strong enough to move the zero are as rare as the zeros they move.
-/

open Complex Filter MeasureTheory Metric Set
open RHTower

noncomputable section

namespace GaloisForLFunctions.ArithmeticAuxiliaryDynamics

/-- The returns within `ε` on `K` have exponent at most `θ`. -/
def ReturnExponentLE (K : Set ℂ) (ε θ : ℝ) : Prop :=
  ∃ T₀ : ℝ, ∀ T : ℝ, T₀ ≤ T → volume (zetaReturnSet K ε ∩ Icc 0 T) ≤ ENNReal.ofReal (T ^ θ)

/-- **The transport count.** The returns of strength `m/2` in `[0, T]` on an isolating disc of radius `r` have
measure at most `2r` times the number of zeros in the translated strip. -/
theorem volume_returnSet_le_zeroCount {ρ₀ : ℂ} {r m T : ℝ} (hr : 0 < r)
    (hre : ∀ s ∈ closedBall ρ₀ r, s.re < 1) (hρ₀ : riemannZeta ρ₀ = 0)
    (hm : ∀ z ∈ sphere ρ₀ r, m ≤ ‖riemannZeta z‖) {Z : Finset ℂ}
    (hZ : ∀ w, riemannZeta w = 0 → ρ₀.re - r < w.re → w.re < ρ₀.re + r → ρ₀.im - r < w.im →
      w.im < ρ₀.im + r + T → w ∈ Z) :
    volume (zetaReturnSet (closedBall ρ₀ r) (m / 2) ∩ Icc 0 T) ≤
      ENNReal.ofReal (2 * r * Z.card) := by
  classical
  have hsub : zetaReturnSet (closedBall ρ₀ r) (m / 2) ∩ Icc 0 T ⊆
      ⋃ w ∈ Z, Ioo (w.im - ρ₀.im - r) (w.im - ρ₀.im + r) := by
    rintro τ ⟨hτ, hτ0, hτT⟩
    obtain ⟨z, hz, hzero⟩ := exists_zero_of_mem_zetaReturnSet hr hre hρ₀ hm hτ
    have hzb : ‖z - ρ₀‖ < r := by
      rw [mem_ball, dist_eq_norm] at hz
      exact hz
    have hre' : |z.re - ρ₀.re| < r := by
      have := Complex.abs_re_le_norm (z - ρ₀)
      rw [Complex.sub_re] at this
      linarith
    have him' : |z.im - ρ₀.im| < r := by
      have := Complex.abs_im_le_norm (z - ρ₀)
      rw [Complex.sub_im] at this
      linarith
    obtain ⟨hre1, hre2⟩ := abs_lt.mp hre'
    obtain ⟨him1, him2⟩ := abs_lt.mp him'
    have hwre : (z + τ * I).re = z.re := by simp
    have hwim : (z + τ * I).im = z.im + τ := by simp
    have hw : z + τ * I ∈ Z := hZ _ hzero (by rw [hwre]; linarith) (by rw [hwre]; linarith)
      (by rw [hwim]; linarith) (by rw [hwim]; linarith)
    refine mem_iUnion₂.mpr ⟨_, hw, ?_⟩
    rw [hwim]
    constructor <;> linarith
  refine (measure_mono hsub).trans ((measure_biUnion_finset_le _ _).trans ?_)
  have hvol : ∀ w ∈ Z, volume (Ioo (w.im - ρ₀.im - r) (w.im - ρ₀.im + r)) = ENNReal.ofReal (2 * r) := by
    intro w _
    rw [Real.volume_Ioo]
    congr 1
    ring
  rw [Finset.sum_congr rfl hvol, Finset.sum_const, nsmul_eq_mul, ENNReal.ofReal_mul (by positivity),
    ENNReal.ofReal_natCast, mul_comm]

/-- **The return exponent reads the zero.** A point of the strip is a zero iff on every disc with doubled
closure in the strip some tolerance has return exponent below `1`. -/
theorem riemannZeta_eq_zero_iff_returnExponent {z₀ : ℂ} (h1 : 1 / 2 < z₀.re) (h2 : z₀.re < 1) :
    riemannZeta z₀ = 0 ↔ ∀ r > 0, 1 / 2 < z₀.re - 2 * r → z₀.re + 2 * r < 1 →
      ∃ ε > 0, ∃ θ : ℝ, θ < 1 ∧ ∀ᶠ T : ℝ in atTop,
        volume (zetaReturnSet (closedBall z₀ r) ε ∩ Icc 0 T) ≤ ENNReal.ofReal (T ^ θ) := by
  have h := riemannZeta_ne_zero_iff_zetaReturnSet_not_powerSaving h1 h2
  constructor
  · intro hz r hr hA hB
    by_contra hcon
    refine absurd hz (h.mpr ⟨r, hr, hA, hB, fun ε hε θ hθ => ?_⟩)
    by_contra hnf
    refine hcon ⟨ε, hε, θ, hθ, ?_⟩
    filter_upwards [Filter.not_frequently.mp hnf] with T hT
    exact not_lt.mp hT
  · intro hall
    by_contra hne
    obtain ⟨r, hr, hA, hB, hfreq⟩ := h.mp hne
    obtain ⟨ε, hε, θ, hθ, hev⟩ := hall r hr hA hB
    obtain ⟨T, hT1, hT2⟩ := ((hfreq ε hε θ hθ).and_eventually hev).exists
    exact absurd hT1 (not_lt.mpr hT2)

private lemma not_returnExponentLE_of_density {K : Set ℂ} {ε θ c : ℝ} (hθ : θ < 1) (hc : 0 < c)
    (hev : ∀ᶠ T : ℝ in atTop, ENNReal.ofReal (c * T) ≤ volume (zetaReturnSet K ε ∩ Icc 0 T)) :
    ¬ ReturnExponentLE K ε θ := by
  rintro ⟨T₀, hT₀⟩
  have hgrow : ∀ᶠ T : ℝ in atTop, 2 / c ≤ T ^ (1 - θ) :=
    (tendsto_rpow_atTop (by linarith : 0 < 1 - θ)).eventually_ge_atTop _
  obtain ⟨T, hT1, hT2, hT3, hT4⟩ :=
    (hev.and (hgrow.and ((eventually_ge_atTop T₀).and (eventually_gt_atTop 0)))).exists
  have hle := hT1.trans (hT₀ T hT3)
  have hpow : 0 ≤ T ^ θ := by positivity
  rw [ENNReal.ofReal_le_ofReal_iff hpow] at hle
  have hsplit : T = T ^ θ * T ^ (1 - θ) := by
    rw [← Real.rpow_add hT4]
    simp
  have hθpos : 0 < T ^ θ := Real.rpow_pos_of_pos hT4 _
  have h2 : 2 ≤ c * T ^ (1 - θ) := by
    rw [div_le_iff₀ hc] at hT2
    linarith
  have h3 : c * T = (c * T ^ (1 - θ)) * T ^ θ := by
    conv_lhs => rw [hsplit]
    ring
  rw [h3] at hle
  nlinarith

/-- **The exponent jumps at the scale of the order.** At a zero of order `D`, with cofactor value of size `A`,
for all small `r`: the tolerance `ε < A r^D/4` has exponent below `1`, and for `ε > 4·3^D A r^D` no exponent
below `1` holds. -/
theorem returnExponent_jump {z₀ : ℂ} (hz : riemannZeta z₀ = 0) (h1 : 1 / 2 < z₀.re) (h2 : z₀.re < 1) :
    ∃ (D : ℕ) (A : ℝ), 1 ≤ D ∧ 0 < A ∧ ∃ r₀ > 0, ∀ r : ℝ, 0 < r → r ≤ r₀ → ∀ ε : ℝ,
      (ε < A / 4 * r ^ D → ∃ θ : ℝ, θ < 1 ∧ ReturnExponentLE (closedBall z₀ r) ε θ) ∧
      (4 * 3 ^ D * A * r ^ D < ε → ∀ θ : ℝ, θ < 1 → ¬ ReturnExponentLE (closedBall z₀ r) ε θ) := by
  obtain ⟨g, hg0, hD, _, r₀, hr₀, hall⟩ := zetaReturnSet_volume_dichotomy_at_zero hz h1 h2
  refine ⟨_, ‖g z₀‖, hD, norm_pos_iff.mpr hg0, r₀, hr₀, fun r hr hrr₀ ε => ⟨fun hε => ?_, fun hε θ hθ => ?_⟩⟩
  · obtain ⟨θ, hθ, T₀, hT₀⟩ := (hall r hr hrr₀ ε).1 hε
    exact ⟨θ, hθ, T₀, hT₀⟩
  · obtain ⟨c, hc, hev⟩ := (hall r hr hrr₀ ε).2 hε
    exact not_returnExponentLE_of_density hθ hc hev

end GaloisForLFunctions.ArithmeticAuxiliaryDynamics
