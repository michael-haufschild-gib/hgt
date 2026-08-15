import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Integral.ExpDecay
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-!
# The terminal-ray phase floor, dyadic block summability, and the low germs

Three quantitative facts sit under the terminal analysis of the root-retained carrier.

*The phase never degenerates.*  Adding the jump symbol to the position shifts the phase operator up
whenever the symbol is accretive, so the phase stays above `L − τ/2` uniformly in the frequency:
the derivative bound is never spoiled by a small denominator.

*The dyadic blocks sum.*  A block bound `2^{j(m+1/2−N)}(L+j)^{-N}` is geometric in `j` exactly when
`N > m + 1/2`, so any number of scale derivatives can be taken and the sum still converges — which
is why the terminal profile is smooth without a conormality assumption.

*The low germs are subcritical.*  A germ decaying like `e^{-L}` still has finite weighted mass
against any weight `e^{2σL}` with `σ < 1`, so the low-frequency counterterms enter the projected
equation as ordinary forcing rather than as a new singular contribution.
-/

open MeasureTheory Set
open scoped ENNReal InnerProductSpace

noncomputable section

namespace GaloisForLFunctions.RHTower

/-! ## The phase floor -/

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- **The terminal phase floor.**  With an accretive jump symbol the phase stays above `L − τ`,
uniformly in the frequency.  Feeding in the halved jump and adjacency values gives the card's
`L − ‖T‖/2` floor. -/
theorem phase_floor {u positionTerm jumpTerm adjacencyTerm : H} {L τ : ℝ}
    (hpos : (inner ℂ positionTerm u).re = L * ‖u‖ ^ 2)
    (hjump : 0 ≤ (inner ℂ jumpTerm u).re)
    (hadj : ‖adjacencyTerm‖ ≤ τ * ‖u‖) :
    (L - τ) * ‖u‖ ^ 2
      ≤ (inner ℂ (positionTerm + jumpTerm - adjacencyTerm) u).re := by
  have hadjre : (inner ℂ adjacencyTerm u).re ≤ τ * ‖u‖ * ‖u‖ :=
    le_trans (le_trans (Complex.re_le_norm _) (norm_inner_le_norm (𝕜 := ℂ) adjacencyTerm u))
      (mul_le_mul_of_nonneg_right hadj (norm_nonneg _))
  have hsplit : (inner ℂ (positionTerm + jumpTerm - adjacencyTerm) u).re
      = (inner ℂ positionTerm u).re + (inner ℂ jumpTerm u).re
        - (inner ℂ adjacencyTerm u).re := by
    rw [inner_sub_left, inner_add_left]
    simp [Complex.add_re, Complex.sub_re]
  rw [hsplit, hpos]
  nlinarith [hjump, hadjre, sq_nonneg ‖u‖, norm_nonneg u]

/-! ## Dyadic block summability -/

/-- **The dyadic blocks sum past the loss threshold.**  A gain of `N` integrations by parts beats a
loss of `m + 1/2` derivatives exactly when `N > m + 1/2`, and then the geometric factor controls the
whole sum uniformly on a terminal ray. -/
theorem summable_dyadicBlockBound {C m N L : ℝ} (hC : 0 ≤ C) (hL : 0 < L) (hm : 0 ≤ m)
    (hN : m + 1 / 2 < N) :
    Summable fun j : ℕ => C * (2 : ℝ) ^ ((j : ℝ) * (m + 1 / 2 - N)) * (L + j) ^ (-N) := by
  set δ : ℝ := N - (m + 1 / 2) with hδ
  have hδpos : 0 < δ := by rw [hδ]; linarith
  set ρ : ℝ := (2 : ℝ) ^ (-δ) with hρ
  have hρpos : 0 < ρ := Real.rpow_pos_of_pos (by norm_num) _
  have hρ1 : ρ < 1 := by
    rw [hρ]
    exact Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  have hgeo : Summable fun j : ℕ => C * L ^ (-N) * ρ ^ j :=
    (summable_geometric_of_lt_one hρpos.le hρ1).mul_left _
  refine Summable.of_nonneg_of_le (fun j => ?_) (fun j => ?_) hgeo
  · have : (0 : ℝ) < (L + j) ^ (-N) := Real.rpow_pos_of_pos (by positivity) _
    positivity
  · have hbase : (2 : ℝ) ^ ((j : ℝ) * (m + 1 / 2 - N)) = ρ ^ j := by
      rw [hρ, ← Real.rpow_natCast ((2 : ℝ) ^ (-δ)) j, ← Real.rpow_mul (by norm_num)]
      congr 1
      rw [hδ]
      ring
    have hLj : (L + j) ^ (-N) ≤ L ^ (-N) := by
      refine Real.rpow_le_rpow_of_nonpos hL (le_add_of_nonneg_right (Nat.cast_nonneg j)) ?_
      linarith
    rw [hbase]
    calc C * ρ ^ j * (L + j) ^ (-N) ≤ C * ρ ^ j * L ^ (-N) := by
          refine mul_le_mul_of_nonneg_left hLj ?_
          positivity
      _ = C * L ^ (-N) * ρ ^ j := by ring

/-! ## The low-frequency germs are Gamma-subcritical -/

variable {X : Type*} [NormedAddCommGroup X]

/-- **The low germs are subcritical.**  An `e^{-L}` germ retains finite mass against every weight
`e^{2σL}` with `σ < 1`, so the two low-frequency counterterms enter the projected equation as
ordinary weighted `L²` forcing. -/
theorem lintegral_weighted_sq_expGerm_ne_top {f : ℝ → X} {C σ L₀ : ℝ} (hσ : σ < 1)
    (hf : ∀ L ∈ Ioi L₀, ‖f L‖ ≤ C * Real.exp (-L)) :
    (∫⁻ L in Ioi L₀, ENNReal.ofReal (Real.exp (2 * σ * L)) * ‖f L‖ₑ ^ 2) ≠ ⊤ := by
  have hmaj : ∀ L ∈ Ioi L₀,
      ENNReal.ofReal (Real.exp (2 * σ * L)) * ‖f L‖ₑ ^ 2
        ≤ ENNReal.ofReal (C ^ 2 * Real.exp (-(2 * (1 - σ)) * L)) := by
    intro L hL
    have hbound := hf L hL
    have hnn : (0 : ℝ) ≤ C * Real.exp (-L) := le_trans (norm_nonneg _) hbound
    have hsq : ‖f L‖ ^ 2 ≤ C ^ 2 * Real.exp (-(2 : ℝ) * L) := by
      refine (pow_le_pow_left₀ (norm_nonneg _) hbound 2).trans (le_of_eq ?_)
      rw [mul_pow, ← Real.exp_nat_mul]
      congr 2
      push_cast
      ring
    have hval : Real.exp (2 * σ * L) * (C ^ 2 * Real.exp (-(2 : ℝ) * L))
        = C ^ 2 * Real.exp (-(2 * (1 - σ)) * L) := by
      rw [show C ^ 2 * Real.exp (-(2 * (1 - σ)) * L)
          = C ^ 2 * (Real.exp (2 * σ * L) * Real.exp (-(2 : ℝ) * L)) by
        rw [← Real.exp_add]
        congr 2
        ring]
      ring
    calc ENNReal.ofReal (Real.exp (2 * σ * L)) * ‖f L‖ₑ ^ 2
        = ENNReal.ofReal (Real.exp (2 * σ * L) * ‖f L‖ ^ 2) := by
          rw [ENNReal.ofReal_mul (Real.exp_pos _).le, ← ofReal_norm,
            ← ENNReal.ofReal_pow (norm_nonneg _)]
      _ ≤ ENNReal.ofReal (Real.exp (2 * σ * L) * (C ^ 2 * Real.exp (-(2 : ℝ) * L))) := by
          refine ENNReal.ofReal_le_ofReal ?_
          exact mul_le_mul_of_nonneg_left hsq (Real.exp_pos _).le
      _ = ENNReal.ofReal (C ^ 2 * Real.exp (-(2 * (1 - σ)) * L)) := by rw [hval]
  have hint : IntegrableOn (fun L : ℝ => C ^ 2 * Real.exp (-(2 * (1 - σ)) * L)) (Ioi L₀) volume :=
    (exp_neg_integrableOn_Ioi L₀ (by linarith : (0 : ℝ) < 2 * (1 - σ))).const_mul (C ^ 2)
  have hfin : (∫⁻ L in Ioi L₀,
      ENNReal.ofReal (C ^ 2 * Real.exp (-(2 * (1 - σ)) * L))) ≠ ⊤ := by
    have hnn : ∀ᵐ L ∂(volume.restrict (Ioi L₀)), 0 ≤ C ^ 2 * Real.exp (-(2 * (1 - σ)) * L) := by
      filter_upwards with L
      positivity
    rw [← ofReal_integral_eq_lintegral_ofReal hint hnn]
    exact ENNReal.ofReal_ne_top
  exact ne_top_of_le_ne_top hfin (setLIntegral_mono' measurableSet_Ioi hmaj)

end GaloisForLFunctions.RHTower
