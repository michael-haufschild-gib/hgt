import GaloisForLFunctions.RHTower.XiResolventEffectiveTuranDetection
import GaloisForLFunctions.RHTower.XiResolventSingleMinorCriterion

/-!
# The effective polynomial descent step

The effective Turán detection window instantiated at polynomially weighted moments: for a real
polynomial `P` vanishing at every resolvent point above a level `ℓ`, the even `P`-weighted Turán
minors detect an off-line copy at the level within the explicit window

  `(2S²b⁴/g + b⁴S²/(ℓ² − ρ₂²)) / (Im(u)²·‖P(u)‖⁴)`,   `b = evalRealPolynomialNormBound P 1`.

A real polynomial can vanish on any conjugation-symmetric finite set — a non-real pair `w, w̄`
through the real quadratic `(X − w)(X − w̄)` — so the descent step needs no reality assumption on
the higher copies.

By the index-shift identity `M_{X^n·P}(k) = M_P(k + 2n)`, the finite certificate consists of
*single-minor data*: the `(0,2,1)` Turán minor of `xiPolyMoment` at each of the `N` polynomials
`X^n·P`.  One real inequality per polynomial, with `N` explicit, cleans the level.
-/

open Complex

namespace RHTower

noncomputable section

/-- **The polynomial detection window**: for a real polynomial `P` killing every copy above the
level, any truncation length whose even `P`-weighted Turán minors are all nonnegative is bounded
by the explicit ratio of the configuration constants to the polynomial off-line defect. -/
theorem poly_minor_truncation_le_of_offline_level {X : ℝ} (hX : 0 ≤ X)
    (P : Polynomial ℝ) {ℓ : ℝ} (hℓpos : 0 < ℓ)
    (hPkill : ∀ q, ℓ < ‖xiResolventPoint X q‖ →
      evalRealPolynomial P (xiResolventPoint X q) = 0)
    {ρ₂ : ℝ} (hρ₂0 : 0 ≤ ρ₂) (hρ₂lt : ρ₂ < ℓ)
    (hρ₂bound : ∀ q, ‖xiResolventPoint X q‖ < ℓ → ‖xiResolventPoint X q‖ ≤ ρ₂)
    {S : ℝ} (hS : ∑' q : XiZeroCopy, ‖xiResolventPoint X q‖ ≤ S)
    {g : ℝ} (hg : 0 < g)
    (hgap : ∀ q q' : XiZeroCopy, ‖xiResolventPoint X q‖ = ℓ → ‖xiResolventPoint X q'‖ = ℓ →
      xiResolventPoint X q * xiResolventPoint X q' ≠ (((ℓ : ℝ)) : ℂ) ^ (2 : ℕ) →
      g ≤ ‖(xiResolventPoint X q * xiResolventPoint X q' / (((ℓ : ℝ)) : ℂ) ^ (2 : ℕ)) ^ (2 : ℕ) - 1‖)
    {qh : XiZeroCopy} (hqhℓ : ‖xiResolventPoint X qh‖ = ℓ)
    (hoff : (xiSpectralPoint qh).im ≠ 0)
    (hPqh : evalRealPolynomial P (xiResolventPoint X qh) ≠ 0)
    {N : ℕ} (hminor : ∀ n : ℕ, n < N → 0 ≤ (xiPolyMoment P (2 * n) X *
      xiPolyMoment P (2 * n + 2) X - xiPolyMoment P (2 * n + 1) X ^ (2 : ℕ)).re) :
    (N : ℝ) ≤ (2 * S ^ (2 : ℕ) * evalRealPolynomialNormBound P 1 ^ (4 : ℕ) / g +
      evalRealPolynomialNormBound P 1 ^ (4 : ℕ) * S ^ (2 : ℕ) / (ℓ ^ (2 : ℕ) - ρ₂ ^ (2 : ℕ))) /
      ((xiResolventPoint X qh).im ^ (2 : ℕ) *
        ‖evalRealPolynomial P (xiResolventPoint X qh)‖ ^ (4 : ℕ)) := by
  have hb := even_minor_truncation_le_of_offline_level (X := X) hX
    (Wf := fun q => evalRealPolynomial P (xiResolventPoint X q) ^ (2 : ℕ))
    (BW := evalRealPolynomialNormBound P 1 ^ (2 : ℕ))
    (fun q => by
      show ‖evalRealPolynomial P (xiResolventPoint X q) ^ (2 : ℕ)‖ ≤
        evalRealPolynomialNormBound P 1 ^ (2 : ℕ)
      rw [norm_pow]
      exact pow_le_pow_left₀ (norm_nonneg _)
        (norm_evalRealPolynomial_le P (norm_xiResolventPoint_le_one hX q)) 2)
    (fun q q' hconj => by
      show evalRealPolynomial P (xiResolventPoint X q') ^ (2 : ℕ) =
        (starRingEnd ℂ) (evalRealPolynomial P (xiResolventPoint X q) ^ (2 : ℕ))
      rw [hconj, evalRealPolynomial_conj, ← map_pow])
    hℓpos
    (fun q hq => by
      show evalRealPolynomial P (xiResolventPoint X q) ^ (2 : ℕ) = 0
      rw [hPkill q hq]
      norm_num)
    hρ₂0 hρ₂lt hρ₂bound hS hg hgap hqhℓ hoff (pow_ne_zero 2 hPqh) hminor
  have hnsq : Complex.normSq (evalRealPolynomial P (xiResolventPoint X qh) ^ (2 : ℕ)) =
      ‖evalRealPolynomial P (xiResolventPoint X qh)‖ ^ (4 : ℕ) := by
    rw [← Complex.sq_norm, norm_pow]
    ring
  calc (N : ℝ) ≤ (2 * S ^ (2 : ℕ) * (evalRealPolynomialNormBound P 1 ^ (2 : ℕ)) ^ (2 : ℕ) / g +
        (evalRealPolynomialNormBound P 1 ^ (2 : ℕ)) ^ (2 : ℕ) * S ^ (2 : ℕ) / (ℓ ^ (2 : ℕ) - ρ₂ ^ (2 : ℕ))) /
        ((xiResolventPoint X qh).im ^ (2 : ℕ) *
          Complex.normSq (evalRealPolynomial P (xiResolventPoint X qh) ^ (2 : ℕ))) := hb
    _ = (2 * S ^ (2 : ℕ) * evalRealPolynomialNormBound P 1 ^ (4 : ℕ) / g +
        evalRealPolynomialNormBound P 1 ^ (4 : ℕ) * S ^ (2 : ℕ) / (ℓ ^ (2 : ℕ) - ρ₂ ^ (2 : ℕ))) /
        ((xiResolventPoint X qh).im ^ (2 : ℕ) *
          ‖evalRealPolynomial P (xiResolventPoint X qh)‖ ^ (4 : ℕ)) := by
        rw [hnsq]
        ring

/-- **The single-minor certificate window**: the same bound with the finite data phrased as the
`(0,2,1)` single Turán minor of the polynomials `X^n·P`, `n < N` — one real inequality per
polynomial. -/
theorem poly_single_minor_truncation_le_of_offline_level {X : ℝ} (hX : 0 ≤ X)
    (P : Polynomial ℝ) {ℓ : ℝ} (hℓpos : 0 < ℓ)
    (hPkill : ∀ q, ℓ < ‖xiResolventPoint X q‖ →
      evalRealPolynomial P (xiResolventPoint X q) = 0)
    {ρ₂ : ℝ} (hρ₂0 : 0 ≤ ρ₂) (hρ₂lt : ρ₂ < ℓ)
    (hρ₂bound : ∀ q, ‖xiResolventPoint X q‖ < ℓ → ‖xiResolventPoint X q‖ ≤ ρ₂)
    {S : ℝ} (hS : ∑' q : XiZeroCopy, ‖xiResolventPoint X q‖ ≤ S)
    {g : ℝ} (hg : 0 < g)
    (hgap : ∀ q q' : XiZeroCopy, ‖xiResolventPoint X q‖ = ℓ → ‖xiResolventPoint X q'‖ = ℓ →
      xiResolventPoint X q * xiResolventPoint X q' ≠ (((ℓ : ℝ)) : ℂ) ^ (2 : ℕ) →
      g ≤ ‖(xiResolventPoint X q * xiResolventPoint X q' / (((ℓ : ℝ)) : ℂ) ^ (2 : ℕ)) ^ (2 : ℕ) - 1‖)
    {qh : XiZeroCopy} (hqhℓ : ‖xiResolventPoint X qh‖ = ℓ)
    (hoff : (xiSpectralPoint qh).im ≠ 0)
    (hPqh : evalRealPolynomial P (xiResolventPoint X qh) ≠ 0)
    {N : ℕ} (hminor : ∀ n : ℕ, n < N →
      0 ≤ (xiPolyMoment (Polynomial.X ^ n * P) 0 X *
        xiPolyMoment (Polynomial.X ^ n * P) 2 X -
        xiPolyMoment (Polynomial.X ^ n * P) 1 X ^ (2 : ℕ)).re) :
    (N : ℝ) ≤ (2 * S ^ (2 : ℕ) * evalRealPolynomialNormBound P 1 ^ (4 : ℕ) / g +
      evalRealPolynomialNormBound P 1 ^ (4 : ℕ) * S ^ (2 : ℕ) / (ℓ ^ (2 : ℕ) - ρ₂ ^ (2 : ℕ))) /
      ((xiResolventPoint X qh).im ^ (2 : ℕ) *
        ‖evalRealPolynomial P (xiResolventPoint X qh)‖ ^ (4 : ℕ)) := by
  refine poly_minor_truncation_le_of_offline_level hX P hℓpos hPkill hρ₂0 hρ₂lt hρ₂bound
    hS hg hgap hqhℓ hoff hPqh (fun n hn => ?_)
  have h := hminor n hn
  rw [xiPolyMoment_X_pow_mul, xiPolyMoment_X_pow_mul, xiPolyMoment_X_pow_mul] at h
  have e0 : 0 + 2 * n = 2 * n := by omega
  have e2 : 2 + 2 * n = 2 * n + 2 := by omega
  have e1 : 1 + 2 * n = 2 * n + 1 := by omega
  rw [e0, e2, e1] at h
  exact h

/-- **The finite polynomial jet certificate**: nonnegativity of the single Turán minors at the
`N` polynomials `X^n·P` cleans the level of every copy that `P` does not kill and whose off-line
defect would place its detection window inside the checked range. -/
theorem level_criticalLine_of_poly_single_minors_window {X : ℝ} (hX : 0 ≤ X)
    (P : Polynomial ℝ) {ℓ : ℝ} (hℓpos : 0 < ℓ)
    (hPkill : ∀ q, ℓ < ‖xiResolventPoint X q‖ →
      evalRealPolynomial P (xiResolventPoint X q) = 0)
    {ρ₂ : ℝ} (hρ₂0 : 0 ≤ ρ₂) (hρ₂lt : ρ₂ < ℓ)
    (hρ₂bound : ∀ q, ‖xiResolventPoint X q‖ < ℓ → ‖xiResolventPoint X q‖ ≤ ρ₂)
    {S : ℝ} (hS : ∑' q : XiZeroCopy, ‖xiResolventPoint X q‖ ≤ S)
    {g : ℝ} (hg : 0 < g)
    (hgap : ∀ q q' : XiZeroCopy, ‖xiResolventPoint X q‖ = ℓ → ‖xiResolventPoint X q'‖ = ℓ →
      xiResolventPoint X q * xiResolventPoint X q' ≠ (((ℓ : ℝ)) : ℂ) ^ (2 : ℕ) →
      g ≤ ‖(xiResolventPoint X q * xiResolventPoint X q' / (((ℓ : ℝ)) : ℂ) ^ (2 : ℕ)) ^ (2 : ℕ) - 1‖)
    {N : ℕ} (hminor : ∀ n : ℕ, n < N →
      0 ≤ (xiPolyMoment (Polynomial.X ^ n * P) 0 X *
        xiPolyMoment (Polynomial.X ^ n * P) 2 X -
        xiPolyMoment (Polynomial.X ^ n * P) 1 X ^ (2 : ℕ)).re) :
    ∀ q : XiZeroCopy, ‖xiResolventPoint X q‖ = ℓ →
      evalRealPolynomial P (xiResolventPoint X q) ≠ 0 →
      (2 * S ^ (2 : ℕ) * evalRealPolynomialNormBound P 1 ^ (4 : ℕ) / g +
        evalRealPolynomialNormBound P 1 ^ (4 : ℕ) * S ^ (2 : ℕ) / (ℓ ^ (2 : ℕ) - ρ₂ ^ (2 : ℕ))) /
        ((xiResolventPoint X q).im ^ (2 : ℕ) *
          ‖evalRealPolynomial P (xiResolventPoint X q)‖ ^ (4 : ℕ)) < (N : ℝ) →
      (xiSpectralPoint q).im = 0 := by
  intro q hq hPq hlt
  by_contra hoff
  have hle := poly_single_minor_truncation_le_of_offline_level hX P hℓpos hPkill
    hρ₂0 hρ₂lt hρ₂bound hS hg hgap hq hoff hPq hminor
  linarith

end

end RHTower
