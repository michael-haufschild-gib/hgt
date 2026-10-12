import GaloisForLFunctions.RHTower.XiGaussianHeatWindowFromWeilMargin
import GaloisForLFunctions.RHTower.XiGaussianHeatHankelDeterminantSignLaw
import GaloisForLFunctions.RHTower.PoleVanishingWeilPositivityPrimeTwo

/-!
# At most one negative square in the heat Hankel window `aN ≤ 1/32`

**Theorem** (`eventually_hermNegIndex_heatMomentSection_le_one_of_polarGroundEnergy`).  If the
pole-vanishing ground energy of the restricted Weil form at aperture `A` is positive and
`0 < K < A²/4`, then for all large `n` and every `0 < a ≤ K/n` the heat moment section
`(M_{i+j}(a))_{i,j ≤ n}` has at most one negative eigenvalue: its form is positive definite on the
pole hyperplane `Σ_i x_i (−1/4)^i = 0`.

**Theorem** (`eventually_hermNegIndex_heatMomentSection_le_one_primeTwo`).  Unconditionally, from
the Weil margin `μ₀ ≥ 1/20` at the aperture `A = ½(log 2 + 1/50)`, which already contains the
prime `2`: for all large `n` and every `0 < a ≤ 1/(32 n)`, the section has at most one negative
eigenvalue, and the heat Hankel form is positive on every real polynomial `P ≠ 0` of degree `≤ n`
with `P(−1/4) = 0` (`eventually_re_heatHankel_pos_primeTwo`).

The splitting `hermQuad M x = hermQuad M (Re x) + hermQuad M (Im x)` for a real matrix
(`hermQuad_map_ofReal_eq_add`) reduces complex coefficient vectors to real polynomials.
-/

open scoped Real
open Complex MeasureTheory Set Polynomial Filter Topology Matrix
open GaloisForLFunctions.HTGeometry (leadingMatrix hermQuad hermNegIndex hermPosIndex
  hermNullIndex IsPosDefOn finrank_le_posIndex posIndex_add_negIndex_add_nullIndex)

namespace RHTower

noncomputable section

/-- For a real matrix the Hermitian form splits over the real and imaginary parts. -/
theorem hermQuad_map_ofReal_eq_add {N : ℕ} (B : Matrix (Fin N) (Fin N) ℝ) (x : Fin N → ℂ) :
    hermQuad (B.map fun r : ℝ => (r : ℂ)) x =
      hermQuad (B.map fun r : ℝ => (r : ℂ)) (fun i => ((x i).re : ℂ)) +
        hermQuad (B.map fun r : ℝ => (r : ℂ)) (fun i => ((x i).im : ℂ)) := by
  simp only [hermQuad, dotProduct, mulVec, map_apply, Finset.mul_sum, re_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  simp only [Pi.star_apply, RCLike.star_def, mul_re, mul_im, conj_re, conj_im, ofReal_re,
    ofReal_im]
  ring

theorem hermQuad_zero' {N : ℕ} (H : Matrix (Fin N) (Fin N) ℂ) : hermQuad H 0 = 0 := by
  simp [hermQuad]

/-- **A form positive definite on a hyperplane has at most one negative square.** -/
theorem hermNegIndex_le_one_of_hyperplane {N : ℕ} {H : Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ}
    (hH : H.IsHermitian) (φ : (Fin (N + 1) → ℂ) →ₗ[ℂ] ℂ)
    (hpos : ∀ x, φ x = 0 → x ≠ 0 → 0 < hermQuad H x) : hermNegIndex H ≤ 1 := by
  have hW : IsPosDefOn H (LinearMap.ker φ) := fun x hx hx0 => hpos x hx hx0
  have h1 := finrank_le_posIndex hW
  have h2 := LinearMap.finrank_range_add_finrank_ker φ
  have h3 : Module.finrank ℂ (LinearMap.range φ) ≤ 1 := by
    have := Submodule.finrank_le (LinearMap.range φ)
    rwa [Module.finrank_self] at this
  rw [Module.finrank_fin_fun] at h2
  have h4 := posIndex_add_negIndex_add_nullIndex hH
  rw [Fintype.card_fin] at h4
  omega

/-- The real polynomial with coefficient vector `r`. -/
def heatRealCoeffPoly {N : ℕ} (r : Fin N → ℝ) : ℝ[X] := ∑ i : Fin N, C (r i) * X ^ (i : ℕ)

theorem heatCoeffPoly_ofReal {N : ℕ} (r : Fin N → ℝ) :
    heatCoeffPoly (fun i => ((r i : ℝ) : ℂ)) = (heatRealCoeffPoly r).map (algebraMap ℝ ℂ) := by
  simp [heatCoeffPoly, heatRealCoeffPoly, Polynomial.map_sum]

theorem natDegree_realCoeffPoly_le {n : ℕ} (r : Fin (n + 1) → ℝ) :
    (heatRealCoeffPoly r).natDegree ≤ n := by
  refine natDegree_sum_le_of_forall_le _ _ fun i _ => ?_
  refine (natDegree_C_mul_le _ _).trans ?_
  rw [natDegree_X_pow]
  exact Nat.lt_succ_iff.1 i.2

theorem eval_realCoeffPoly {N : ℕ} (r : Fin N → ℝ) (t : ℝ) :
    (heatRealCoeffPoly r).eval t = ∑ i : Fin N, r i * t ^ (i : ℕ) := by
  simp [heatRealCoeffPoly, eval_finsetSum]

theorem realCoeffPoly_ne_zero {N : ℕ} {r : Fin N → ℝ} (hr : r ≠ 0) : heatRealCoeffPoly r ≠ 0 := by
  intro h
  apply hr
  funext i
  have := congrArg (fun P : ℝ[X] => P.coeff i) h
  simp only [heatRealCoeffPoly, finsetSum_coeff, coeff_C_mul_X_pow, coeff_zero] at this
  rw [Finset.sum_eq_single i (fun j _ hj => by
    rw [if_neg]; exact fun h' => hj (Fin.ext h'.symm)) (by simp)] at this
  simpa using this

/-- The pole functional `x ↦ Σ_i x_i (−1/4)^i`. -/
def poleFunctional (N : ℕ) : (Fin N → ℂ) →ₗ[ℂ] ℂ where
  toFun x := ∑ i : Fin N, x i * (-1 / 4 : ℂ) ^ (i : ℕ)
  map_add' x y := by simp [add_mul, Finset.sum_add_distrib]
  map_smul' c x := by simp [Finset.mul_sum, mul_assoc]

/-- **Real reduction.**  Positivity of the heat Hankel form on real polynomials of degree `≤ n`
vanishing at `−1/4` gives positive definiteness of the `(n+1)`-st section on the pole hyperplane. -/
theorem hermQuad_heatMomentSection_pos_of_real {a : ℝ} (ha : 0 < a) {n : ℕ}
    (hreal : ∀ P : ℝ[X], P.natDegree ≤ n → P.eval (-1 / 4) = 0 → P ≠ 0 →
      0 < (heatHankel a (P.map (algebraMap ℝ ℂ)) (P.map (algebraMap ℝ ℂ))).re)
    (x : Fin (n + 1) → ℂ) (hx : poleFunctional (n + 1) x = 0) (hx0 : x ≠ 0) :
    0 < hermQuad (heatMomentSection a (n + 1)) x := by
  have hsplit := hermQuad_map_ofReal_eq_add (leadingMatrix (heatMomentArray a) (n + 1)) x
  change hermQuad (heatMomentSection a (n + 1)) x = hermQuad (heatMomentSection a (n + 1)) _ +
    hermQuad (heatMomentSection a (n + 1)) _ at hsplit
  have hpart : ∀ r : Fin (n + 1) → ℝ, ∑ i : Fin (n + 1), r i * (-1 / 4 : ℝ) ^ (i : ℕ) = 0 →
      (r = 0 ∧ hermQuad (heatMomentSection a (n + 1)) (fun i => ((r i : ℝ) : ℂ)) = 0) ∨
        0 < hermQuad (heatMomentSection a (n + 1)) (fun i => ((r i : ℝ) : ℂ)) := fun r hr => by
    by_cases h0 : r = 0
    · left
      refine ⟨h0, ?_⟩
      have : (fun i => ((r i : ℝ) : ℂ)) = 0 := by funext i; simp [h0]
      rw [this, hermQuad_zero']
    · right
      rw [hermQuad_heatMomentSection ha (Nat.succ_pos n), heatCoeffPoly_ofReal]
      exact hreal _ (natDegree_realCoeffPoly_le r) (by rw [eval_realCoeffPoly]; exact hr)
        (realCoeffPoly_ne_zero h0)
  have hsum : ∑ i : Fin (n + 1), x i * (-1 / 4 : ℂ) ^ (i : ℕ) = 0 := hx
  have hsum' : ∑ i : Fin (n + 1), x i * (((-1 / 4 : ℝ) ^ (i : ℕ) : ℝ) : ℂ) = 0 := by
    rw [← hsum]
    refine Finset.sum_congr rfl fun i _ => ?_
    push_cast
    ring
  have hre : ∑ i : Fin (n + 1), (x i).re * (-1 / 4 : ℝ) ^ (i : ℕ) = 0 := by
    have := congrArg Complex.re hsum'
    simpa only [Complex.re_sum, Complex.re_mul_ofReal, Complex.zero_re] using this
  have him : ∑ i : Fin (n + 1), (x i).im * (-1 / 4 : ℝ) ^ (i : ℕ) = 0 := by
    have := congrArg Complex.im hsum'
    simpa only [Complex.im_sum, Complex.im_mul_ofReal, Complex.zero_im] using this
  rw [hsplit]
  rcases hpart (fun i => (x i).re) hre with ⟨hr0, hq0⟩ | hpos1
  · rcases hpart (fun i => (x i).im) him with ⟨hi0, -⟩ | hpos2
    · exfalso
      apply hx0
      funext i
      have h1 := congrFun hr0 i
      have h2 := congrFun hi0 i
      simp only [Pi.zero_apply] at h1 h2
      exact Complex.ext h1 h2
    · rw [hq0]; linarith
  · rcases hpart (fun i => (x i).im) him with ⟨-, hq0⟩ | hpos2
    · rw [hq0]; linarith
    · linarith

/-- **At most one negative square in the window `aN ≤ K`, `K < A²/4`.** -/
theorem eventually_hermNegIndex_heatMomentSection_le_one_of_polarGroundEnergy
    {A : SuzukiPositiveAperture} (hμ : 0 < ccmRestrictedWeilPolarGroundEnergy A) {K : ℝ}
    (hK : 0 < K) (hKA : 4 * K < A.1 ^ 2) :
    ∀ᶠ n : ℕ in atTop, ∀ a : ℝ, 0 < a → a ≤ K / n →
      hermNegIndex (heatMomentSection a (n + 1)) ≤ 1 := by
  filter_upwards [eventually_re_heatHankel_pos_of_polarGroundEnergy hμ hK hKA] with n hn a ha haK
  exact hermNegIndex_le_one_of_hyperplane (isHermitian_heatMomentSection a (n + 1))
    (poleFunctional (n + 1))
    (hermQuad_heatMomentSection_pos_of_real ha (hn a ha haK))

theorem sixteen_div_thirtytwo_lt_primeTwoAperture_sq : 4 * (1 / 32 : ℝ) < primeTwoAperture.1 ^ 2 := by
  change 4 * (1 / 32 : ℝ) < ((Real.log 2 + 1 / 50) / 2) ^ 2
  have h := Real.log_two_gt_d9
  nlinarith

theorem ccmRestrictedWeilPolarGroundEnergy_primeTwo_pos :
    0 < ccmRestrictedWeilPolarGroundEnergy primeTwoAperture :=
  lt_of_lt_of_le (by norm_num) one_twentieth_le_ccmRestrictedWeilPolarGroundEnergy_primeTwo

/-- **Unconditional window past the prime `2`.**  For all large `n`, every `0 < a ≤ 1/(32n)` and
every real polynomial `P ≠ 0` of degree `≤ n` with `P(−1/4) = 0`, `Re H_a(P, P) > 0`. -/
theorem eventually_re_heatHankel_pos_primeTwo :
    ∀ᶠ n : ℕ in atTop, ∀ a : ℝ, 0 < a → a ≤ 1 / 32 / n → ∀ P : ℝ[X], P.natDegree ≤ n →
      P.eval (-1 / 4) = 0 → P ≠ 0 →
        0 < (heatHankel a (P.map (algebraMap ℝ ℂ)) (P.map (algebraMap ℝ ℂ))).re :=
  eventually_re_heatHankel_pos_of_polarGroundEnergy ccmRestrictedWeilPolarGroundEnergy_primeTwo_pos
    (by norm_num) sixteen_div_thirtytwo_lt_primeTwoAperture_sq

/-- **Unconditionally at most one negative square for `aN ≤ 1/32`.** -/
theorem eventually_hermNegIndex_heatMomentSection_le_one_primeTwo :
    ∀ᶠ n : ℕ in atTop, ∀ a : ℝ, 0 < a → a ≤ 1 / 32 / n →
      hermNegIndex (heatMomentSection a (n + 1)) ≤ 1 :=
  eventually_hermNegIndex_heatMomentSection_le_one_of_polarGroundEnergy
    ccmRestrictedWeilPolarGroundEnergy_primeTwo_pos (by norm_num)
    sixteen_div_thirtytwo_lt_primeTwoAperture_sq

end

end RHTower
