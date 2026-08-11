import GaloisForLFunctions.RHTower.FiniteExponentialPencilMeanSquare
import GaloisForLFunctions.RHTower.GaussHodgeCoherenceBudget
import GaloisForLFunctions.RHTower.CCMClosedXiConformalKreinLaw

/-!
# Vertical extraction of the Hodge mass at ℓ¹ weights: the truncation exchange is free

The residual open core of the Hodge/seam programme asks for the conjugate-pair diagonal of a
squared explicit formula over the whole divisor.  Extracting a diagonal from a square is a
vertical Cesàro mean; the feared obstruction was the interchange of that mean with the
infinite-divisor closure.  This module proves the interchange unconditionally at ℓ¹ weights:
for any absolutely summable coefficient family on any index, and any unimodular mode family —
with no separation, gap, injectivity, or correlation hypothesis — the Cesàro mean of the
squared pencil converges to the equal-mode pair diagonal.  The proof is dominated convergence
over coefficient pairs against the ℓ¹ × ℓ¹ product, with the scalar geometric Cesàro law
deciding each pair.

Instantiated at the divisor: for every ℓ¹ weight on the Xi copies, the vertical flow at the
ordinates extracts, from the squared weighted Burnol character pencil, the equal-ordinate pair
diagonal — unconditionally, over the full divisor.  The reflected partner `1 - conj ρ` shares
the ordinate of `ρ`, so each reflection pair aggregates inside one mode fiber, and the
reflection-odd `2×2` block of the extracted diagonal is exactly the centered cosh defect
`p^{2Re-1} + p^{1-2Re} - 2` — the Hodge/seam mass density.  The extracted diagonal is
nonnegative, being a limit of mean squares.

What this relocates: the mass-extraction limit exchange is no longer open — it holds at ℓ¹
weights.  The remaining wall is the sourcing of the pencil itself: the vertical mode
`exp(i·Im ρ)` is a conjugate-pair (bilinear) sample of the divisor, not a holomorphic one, so
producing the pencil values from prime-side data is exactly the conjugate-pair input that the
information-gap theorem shows no holomorphic channel supplies.
-/

open Complex Filter Topology
open scoped BigOperators

namespace RHTower

noncomputable section

/-! ## The scalar Cesàro bound -/

/-- The Cesàro mean of a unimodular geometric progression has modulus at most one. -/
theorem norm_cesaro_geom_le_one {w : ℂ} (hw : ‖w‖ = 1) (N : ℕ) :
    ‖((N : ℝ)⁻¹ : ℂ) * ∑ n ∈ Finset.range N, w ^ n‖ ≤ 1 := by
  rw [norm_mul]
  have h1 : ‖∑ n ∈ Finset.range N, w ^ n‖ ≤ N := by
    calc ‖∑ n ∈ Finset.range N, w ^ n‖ ≤ ∑ n ∈ Finset.range N, ‖w ^ n‖ :=
          norm_sum_le _ _
      _ = ∑ _n ∈ Finset.range N, (1 : ℝ) := by
          apply Finset.sum_congr rfl
          intro n _
          rw [norm_pow, hw, one_pow]
      _ = N := by simp
  have h2 : ‖(((N : ℝ)⁻¹ : ℝ) : ℂ)‖ = (N : ℝ)⁻¹ := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · simp
  · have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
    rw [h2]
    calc (N : ℝ)⁻¹ * ‖∑ n ∈ Finset.range N, w ^ n‖ ≤ (N : ℝ)⁻¹ * N :=
          mul_le_mul_of_nonneg_left h1 (by positivity)
      _ = 1 := by field_simp

/-- Two unimodular values agree exactly when their conjugate cross product is one. -/
theorem star_mul_eq_one_iff_eq {x y : ℂ} (hx : ‖x‖ = 1) (hy : ‖y‖ = 1) :
    star x * y = 1 ↔ x = y := by
  constructor
  · intro h
    have hui : x * star x = 1 := by simpa [hx] using Complex.mul_conj' x
    calc x = x * (star x * y) := by rw [h, mul_one]
      _ = (x * star x) * y := by ring
      _ = y := by rw [hui, one_mul]
  · rintro rfl
    simpa [hy] using Complex.conj_mul' y

/-! ## The ℓ¹ limit exchange -/

/-- **ℓ¹ limit exchange, complex form.**  The Cesàro mean of `conj S · S` for an absolutely
summable unimodular pencil over an arbitrary index converges to the equal-mode pair diagonal.
No separation, gap, injectivity, or correlation hypothesis enters: dominated convergence over
coefficient pairs does the whole interchange. -/
theorem tendsto_tsum_pencil_cesaro_star_mul
    {ι : Type*} (c w : ι → ℂ)
    (hc : Summable fun i => ‖c i‖) (hw : ∀ i, ‖w i‖ = 1) :
    Tendsto
      (fun N : ℕ => ((N : ℝ)⁻¹ : ℂ) * ∑ n ∈ Finset.range N,
        star (∑' i, c i * w i ^ n) * (∑' i, c i * w i ^ n))
      atTop
      (nhds (∑' pq : ι × ι,
        if w pq.1 = w pq.2 then star (c pq.1) * c pq.2 else 0)) := by
  classical
  have hbound : Summable fun pq : ι × ι => ‖c pq.1‖ * ‖c pq.2‖ :=
    hc.mul_of_nonneg hc (fun _ => norm_nonneg _) (fun _ => norm_nonneg _)
  have hcn (n : ℕ) : Summable fun i => ‖c i * w i ^ n‖ := by
    refine hc.congr fun i => ?_
    rw [norm_mul, norm_pow, hw i, one_pow, mul_one]
  have hstarn (n : ℕ) : Summable fun i => ‖star (c i * w i ^ n)‖ := by
    simpa only [norm_star] using hcn n
  have hgsum (n : ℕ) : Summable fun pq : ι × ι =>
      star (c pq.1) * c pq.2 * (star (w pq.1) * w pq.2) ^ n := by
    refine hbound.of_norm_bounded fun pq => ?_
    rw [norm_mul, norm_mul, norm_pow, norm_mul, norm_star, norm_star,
      hw pq.1, hw pq.2, one_mul, one_pow, mul_one]
  have hchain (N : ℕ) :
      ((N : ℝ)⁻¹ : ℂ) * ∑ n ∈ Finset.range N,
          star (∑' i, c i * w i ^ n) * (∑' i, c i * w i ^ n) =
        ∑' pq : ι × ι, star (c pq.1) * c pq.2 *
          (((N : ℝ)⁻¹ : ℂ) * ∑ n ∈ Finset.range N, (star (w pq.1) * w pq.2) ^ n) := by
    have hn (n : ℕ) : star (∑' i, c i * w i ^ n) * (∑' i, c i * w i ^ n) =
        ∑' pq : ι × ι, star (c pq.1) * c pq.2 * (star (w pq.1) * w pq.2) ^ n := by
      rw [tsum_star, tsum_mul_tsum_of_summable_norm (hstarn n) (hcn n)]
      apply tsum_congr
      intro pq
      rw [star_mul', star_pow, mul_pow]
      ring
    calc ((N : ℝ)⁻¹ : ℂ) * ∑ n ∈ Finset.range N,
            star (∑' i, c i * w i ^ n) * (∑' i, c i * w i ^ n) =
          ((N : ℝ)⁻¹ : ℂ) * ∑ n ∈ Finset.range N,
            ∑' pq : ι × ι, star (c pq.1) * c pq.2 * (star (w pq.1) * w pq.2) ^ n := by
            congr 1
            exact Finset.sum_congr rfl fun n _ => hn n
      _ = ((N : ℝ)⁻¹ : ℂ) * ∑' pq : ι × ι, ∑ n ∈ Finset.range N,
            star (c pq.1) * c pq.2 * (star (w pq.1) * w pq.2) ^ n := by
            congr 1
            exact (Summable.tsum_finsetSum fun n _ => hgsum n).symm
      _ = ∑' pq : ι × ι, ((N : ℝ)⁻¹ : ℂ) * ∑ n ∈ Finset.range N,
            star (c pq.1) * c pq.2 * (star (w pq.1) * w pq.2) ^ n := by
            rw [tsum_mul_left]
      _ = _ := by
            apply tsum_congr
            intro pq
            rw [Finset.mul_sum, Finset.mul_sum]
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro n _
            ring
  have hpoint (pq : ι × ι) :
      Tendsto (fun N : ℕ => star (c pq.1) * c pq.2 *
          (((N : ℝ)⁻¹ : ℂ) * ∑ n ∈ Finset.range N, (star (w pq.1) * w pq.2) ^ n))
        atTop
        (nhds (if w pq.1 = w pq.2 then star (c pq.1) * c pq.2 else 0)) := by
    have hu : ‖star (w pq.1) * w pq.2‖ = 1 := by
      rw [norm_mul, norm_star, hw pq.1, hw pq.2, one_mul]
    have h := tendsto_const_nhds.mul
      (tendsto_complex_geom_cesaro_of_norm_eq_one (star (w pq.1) * w pq.2) hu)
    have hval : star (c pq.1) * c pq.2 *
        (if star (w pq.1) * w pq.2 = 1 then (1 : ℂ) else 0) =
        if w pq.1 = w pq.2 then star (c pq.1) * c pq.2 else 0 := by
      rw [show (star (w pq.1) * w pq.2 = 1) = (w pq.1 = w pq.2) from
        propext (star_mul_eq_one_iff_eq (hw pq.1) (hw pq.2))]
      split_ifs <;> simp
    rw [← hval]
    exact h
  have hdom : ∀ᶠ N : ℕ in atTop, ∀ pq : ι × ι,
      ‖star (c pq.1) * c pq.2 *
        (((N : ℝ)⁻¹ : ℂ) * ∑ n ∈ Finset.range N, (star (w pq.1) * w pq.2) ^ n)‖ ≤
      ‖c pq.1‖ * ‖c pq.2‖ := by
    refine Eventually.of_forall fun N pq => ?_
    have hu : ‖star (w pq.1) * w pq.2‖ = 1 := by
      rw [norm_mul, norm_star, hw pq.1, hw pq.2, one_mul]
    calc ‖star (c pq.1) * c pq.2 *
          (((N : ℝ)⁻¹ : ℂ) * ∑ n ∈ Finset.range N, (star (w pq.1) * w pq.2) ^ n)‖ =
        ‖c pq.1‖ * ‖c pq.2‖ *
          ‖((N : ℝ)⁻¹ : ℂ) * ∑ n ∈ Finset.range N, (star (w pq.1) * w pq.2) ^ n‖ := by
          rw [norm_mul, norm_mul, norm_star]
      _ ≤ ‖c pq.1‖ * ‖c pq.2‖ * 1 :=
          mul_le_mul_of_nonneg_left (norm_cesaro_geom_le_one hu N)
            (by positivity)
      _ = ‖c pq.1‖ * ‖c pq.2‖ := mul_one _
  have hlim := tendsto_tsum_of_dominated_convergence hbound hpoint hdom
  exact hlim.congr' (Eventually.of_forall fun N => (hchain N).symm)

/-- **ℓ¹ limit exchange, real mean-square form.**  The Cesàro mean of the squared pencil norm
converges to the real part of the equal-mode pair diagonal. -/
theorem tendsto_tsum_pencil_cesaro_norm_sq
    {ι : Type*} (c w : ι → ℂ)
    (hc : Summable fun i => ‖c i‖) (hw : ∀ i, ‖w i‖ = 1) :
    Tendsto
      (fun N : ℕ => (N : ℝ)⁻¹ * ∑ n ∈ Finset.range N,
        ‖∑' i, c i * w i ^ n‖ ^ 2)
      atTop
      (nhds ((∑' pq : ι × ι,
        if w pq.1 = w pq.2 then star (c pq.1) * c pq.2 else 0).re)) := by
  have h := tendsto_tsum_pencil_cesaro_star_mul c w hc hw
  have hre := (Complex.continuous_re.tendsto _).comp h
  refine hre.congr fun N => ?_
  rw [Function.comp_apply, Complex.mul_re]
  have hreN : ((((N : ℝ)⁻¹ : ℝ) : ℂ)).re = (N : ℝ)⁻¹ := by norm_num
  have himN : ((((N : ℝ)⁻¹ : ℝ) : ℂ)).im = 0 := by norm_num
  rw [hreN, himN, zero_mul, sub_zero]
  congr 1
  rw [← Complex.reCLM_apply, map_sum]
  apply Finset.sum_congr rfl
  intro n _
  rw [show star (∑' i, c i * w i ^ n) * (∑' i, c i * w i ^ n) =
      ((‖∑' i, c i * w i ^ n‖ ^ 2 : ℝ) : ℂ) by
    simpa using Complex.conj_mul' (∑' i, c i * w i ^ n)]
  rw [Complex.reCLM_apply, Complex.ofReal_re]

/-- The extracted pair diagonal is nonnegative: it is a limit of mean squares. -/
theorem tsum_pencil_pairDiagonal_re_nonneg
    {ι : Type*} (c w : ι → ℂ)
    (hc : Summable fun i => ‖c i‖) (hw : ∀ i, ‖w i‖ = 1) :
    0 ≤ (∑' pq : ι × ι,
      if w pq.1 = w pq.2 then star (c pq.1) * c pq.2 else 0).re := by
  refine ge_of_tendsto (tendsto_tsum_pencil_cesaro_norm_sq c w hc hw)
    (Eventually.of_forall fun N => ?_)
  have : (0 : ℝ) ≤ ∑ n ∈ Finset.range N, ‖∑' i, c i * w i ^ n‖ ^ 2 :=
    Finset.sum_nonneg fun n _ => sq_nonneg _
  positivity

/-! ## Instantiation at the divisor -/

/-- The vertical mode of a divisor copy: the unit flow phase at its ordinate. -/
def xiZeroCopyVerticalMode (q : XiZeroCopy) : ℂ :=
  Complex.exp ((((q.1 : ℂ)).im : ℂ) * Complex.I)

theorem norm_xiZeroCopyVerticalMode (q : XiZeroCopy) :
    ‖xiZeroCopyVerticalMode q‖ = 1 := by
  rw [xiZeroCopyVerticalMode, Complex.norm_exp]
  simp [Complex.mul_re]

/-- Reflection is horizontal: the reflected point keeps the ordinate. -/
theorem im_one_sub_conj (s : ℂ) : (1 - (starRingEnd ℂ) s).im = s.im := by
  simp

/-- The reflected partner copy shares the vertical mode: each reflection pair aggregates
inside a single mode fiber of the vertical flow. -/
theorem xiZeroCopyVerticalMode_lineConjEquiv (q : XiZeroCopy) :
    xiZeroCopyVerticalMode (xiZeroCopyLineConjEquiv q) = xiZeroCopyVerticalMode q := by
  rw [xiZeroCopyVerticalMode, xiZeroCopyVerticalMode,
    GaloisForLFunctions.RHTower.xiZeroCopyLineConj_support, im_one_sub_conj]

/-- **Vertical extraction over the full divisor at ℓ¹ weights.**  For every absolutely
summable weight family on the Xi copies, the Cesàro mean-square of the weighted Burnol
character pencil under the vertical flow converges to the equal-ordinate pair diagonal.
The truncation half of the mass-extraction limit exchange holds unconditionally over the
whole divisor. -/
theorem tendsto_cesaro_divisorCharPencil_norm_sq {p : ℝ} (hp : 1 < p)
    (v : XiZeroCopy → ℂ) (hv : Summable fun q => ‖v q‖) :
    Tendsto
      (fun N : ℕ => (N : ℝ)⁻¹ * ∑ n ∈ Finset.range N,
        ‖∑' q : XiZeroCopy,
          v q * burnolPrimeCharacter p ((q.1 : ℂ)) * xiZeroCopyVerticalMode q ^ n‖ ^ 2)
      atTop
      (nhds ((∑' pq : XiZeroCopy × XiZeroCopy,
        if xiZeroCopyVerticalMode pq.1 = xiZeroCopyVerticalMode pq.2 then
          star (v pq.1 * burnolPrimeCharacter p ((pq.1.1 : ℂ))) *
            (v pq.2 * burnolPrimeCharacter p ((pq.2.1 : ℂ)))
        else 0).re)) := by
  have hp0 : (0 : ℝ) < p := lt_trans one_pos hp
  have hc : Summable fun q : XiZeroCopy =>
      ‖v q * burnolPrimeCharacter p ((q.1 : ℂ))‖ := by
    refine Summable.of_nonneg_of_le (fun q => norm_nonneg _) ?_
      (hv.mul_right ((p : ℝ) ^ ((1 : ℝ) / 2)))
    intro q
    rw [norm_mul, norm_burnolPrimeCharacter hp0]
    have hstrip := (xiZeroCopy_re_mem_open_unit q).2
    have hle : (p : ℝ) ^ (((q.1 : ℂ)).re - 1 / 2) ≤ (p : ℝ) ^ ((1 : ℝ) / 2) :=
      (Real.rpow_le_rpow_left_iff hp).mpr (by linarith)
    exact mul_le_mul_of_nonneg_left hle (norm_nonneg _)
  exact tendsto_tsum_pencil_cesaro_norm_sq
    (fun q => v q * burnolPrimeCharacter p ((q.1 : ℂ)))
    xiZeroCopyVerticalMode hc norm_xiZeroCopyVerticalMode

/-! ## The extracted diagonal carries the mass -/

/-- **The reflection-odd block of the extracted diagonal is the cosh defect.**  Within one
mode fiber, the `2×2` block of the pair diagonal on a reflection pair, taken with opposite
signs, is exactly the centered cosh defect — the Hodge/seam mass density at that copy. -/
theorem charPair_oddBlock {p : ℝ} (hp : 0 < p) (s : ℂ) :
    star (burnolPrimeCharacter p s) * burnolPrimeCharacter p s +
      star (burnolPrimeCharacter p (1 - (starRingEnd ℂ) s)) *
        burnolPrimeCharacter p (1 - (starRingEnd ℂ) s) -
      star (burnolPrimeCharacter p s) *
        burnolPrimeCharacter p (1 - (starRingEnd ℂ) s) -
      star (burnolPrimeCharacter p (1 - (starRingEnd ℂ) s)) *
        burnolPrimeCharacter p s =
    (((p : ℝ) ^ (2 * s.re - 1) + (p : ℝ) ^ (1 - 2 * s.re) - 2 : ℝ) : ℂ) := by
  have hpC : ((p : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hp.ne'
  have harg : (((p : ℝ) : ℂ)).arg ≠ Real.pi := by
    rw [Complex.arg_ofReal_of_nonneg hp.le]
    exact Real.pi_ne_zero.symm
  have hconj : ∀ wexp : ℂ, star (((p : ℝ) : ℂ) ^ wexp) =
      ((p : ℝ) : ℂ) ^ ((starRingEnd ℂ) wexp) := by
    intro wexp
    have h := Complex.cpow_conj (((p : ℝ) : ℂ)) wexp harg
    rw [Complex.conj_ofReal] at h
    exact h.symm
  have hA : star (burnolPrimeCharacter p s) * burnolPrimeCharacter p s =
      ((((p : ℝ) ^ (2 * s.re - 1) : ℝ)) : ℂ) := by
    rw [show star (burnolPrimeCharacter p s) * burnolPrimeCharacter p s =
        ((‖burnolPrimeCharacter p s‖ ^ 2 : ℝ) : ℂ) by
      simpa using Complex.conj_mul' (burnolPrimeCharacter p s)]
    rw [norm_burnolPrimeCharacter hp s, sq, ← Real.rpow_add hp]
    congr 2
    ring
  have hB : star (burnolPrimeCharacter p (1 - (starRingEnd ℂ) s)) *
      burnolPrimeCharacter p (1 - (starRingEnd ℂ) s) =
      ((((p : ℝ) ^ (1 - 2 * s.re) : ℝ)) : ℂ) := by
    rw [show star (burnolPrimeCharacter p (1 - (starRingEnd ℂ) s)) *
        burnolPrimeCharacter p (1 - (starRingEnd ℂ) s) =
        ((‖burnolPrimeCharacter p (1 - (starRingEnd ℂ) s)‖ ^ 2 : ℝ) : ℂ) by
      simpa using Complex.conj_mul' (burnolPrimeCharacter p (1 - (starRingEnd ℂ) s))]
    rw [norm_burnolPrimeCharacter hp, sq, ← Real.rpow_add hp]
    congr 2
    simp only [Complex.sub_re, Complex.one_re, Complex.conj_re]
    ring
  have hcross : star (burnolPrimeCharacter p s) *
      burnolPrimeCharacter p (1 - (starRingEnd ℂ) s) = 1 := by
    rw [burnolPrimeCharacter, burnolPrimeCharacter, hconj,
      ← Complex.cpow_add _ _ hpC]
    rw [show (starRingEnd ℂ) (s - 1 / 2) + (1 - (starRingEnd ℂ) s - 1 / 2) = 0 by
      rw [map_sub]
      have : (starRingEnd ℂ) (1 / 2 : ℂ) = 1 / 2 := by
        rw [show (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) from by norm_num, Complex.conj_ofReal]
      rw [this]
      ring]
    exact Complex.cpow_zero _
  have hcross' : star (burnolPrimeCharacter p (1 - (starRingEnd ℂ) s)) *
      burnolPrimeCharacter p s = 1 := by
    have h := congrArg star hcross
    rw [star_mul', star_star, star_one] at h
    exact h
  rw [hA, hB, hcross, hcross']
  push_cast
  ring

end

end RHTower
