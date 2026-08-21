import GaloisForLFunctions.RHTower.FiniteOfflineCauchyL2
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Topology.Algebra.Order.Field

/-!
# A self-dual quartet defeats every generic shifted-curvature bound

The degree-four family

`F_{a,γ}(s) = ((z-a)² + γ²)((z+a)² + γ²)`,  `z = s - 1/2`,

satisfies every generic completed-source symmetry — the functional equation `F(1-s) = F(s)`,
Schwarz symmetry, all four zeros inside the open critical strip, unimodularity of the centered
shifted quotient on the critical line, the exact full-shift cocycle, and hence contractivity of the
associated boundary compression — while its anti-causal leakage-curvature corner

`C_{a,γ}(0,0) = 4/a + 4a/(a² + γ²)`

exceeds `8` and blows up as `a → 0⁺`.  No theorem using only those generic data can prove the
`≤ 4` corner bound.

Theorem B reuses the corpus off-line Cauchy-energy stack
(`RHTower.finiteOfflineProfile`, `RHTower.finiteOfflineCauchyEnergy`,
`RHTower.integral_norm_sq_finiteOfflineProfile`), so the boundary energy is the genuine
`∫_{t>0} ‖ℓ(t)‖² dt` and not a re-encoded constant.
-/

namespace RHTower

noncomputable section

open Complex

/-! ## The quartet and its generic symmetries -/

/-- The centered self-dual quartet in the centered variable `z = s - 1/2`. -/
def selfDualQuartetPoly (a gamma : ℝ) (z : ℂ) : ℂ :=
  ((z - (a : ℂ)) ^ 2 + (gamma : ℂ) ^ 2) * ((z + (a : ℂ)) ^ 2 + (gamma : ℂ) ^ 2)

/-- The self-dual quartet as a function of the spectral parameter `s`. -/
def selfDualQuartet (a gamma : ℝ) (s : ℂ) : ℂ :=
  selfDualQuartetPoly a gamma (s - 1 / 2)

theorem selfDualQuartetPoly_even (a gamma : ℝ) (z : ℂ) :
    selfDualQuartetPoly a gamma (-z) = selfDualQuartetPoly a gamma z := by
  unfold selfDualQuartetPoly
  ring

private theorem conj_half : (starRingEnd ℂ) (1 / 2 : ℂ) = 1 / 2 := by
  rw [show ((1 : ℂ) / 2) = ((1 / 2 : ℝ) : ℂ) by norm_num]
  exact Complex.conj_ofReal _

/-- **Functional equation.**  `F(1-s) = F(s)`. -/
theorem selfDualQuartet_functional_equation (a gamma : ℝ) (s : ℂ) :
    selfDualQuartet a gamma (1 - s) = selfDualQuartet a gamma s := by
  unfold selfDualQuartet
  rw [show (1 - s - 1 / 2 : ℂ) = -(s - 1 / 2) by ring, selfDualQuartetPoly_even]

theorem selfDualQuartetPoly_conj (a gamma : ℝ) (z : ℂ) :
    selfDualQuartetPoly a gamma ((starRingEnd ℂ) z) =
      (starRingEnd ℂ) (selfDualQuartetPoly a gamma z) := by
  unfold selfDualQuartetPoly
  simp [map_mul, map_add, map_sub, map_pow, Complex.conj_ofReal]

/-- **Schwarz symmetry.**  `F(conj s) = conj (F s)`. -/
theorem selfDualQuartet_schwarz (a gamma : ℝ) (s : ℂ) :
    selfDualQuartet a gamma ((starRingEnd ℂ) s) =
      (starRingEnd ℂ) (selfDualQuartet a gamma s) := by
  unfold selfDualQuartet
  rw [show ((starRingEnd ℂ) s - 1 / 2 : ℂ) = (starRingEnd ℂ) (s - 1 / 2) by
    rw [map_sub, conj_half]]
  exact selfDualQuartetPoly_conj a gamma _

/-! ## The divisor -/

private theorem block_factor (a gamma : ℝ) (z : ℂ) :
    (z - (a : ℂ)) ^ 2 + (gamma : ℂ) ^ 2 =
      (z - (a : ℂ) - I * (gamma : ℂ)) * (z - (a : ℂ) + I * (gamma : ℂ)) := by
  have hI : (I : ℂ) ^ 2 = -1 := Complex.I_sq
  linear_combination ((gamma : ℂ)) ^ 2 * hI

theorem selfDualQuartetPoly_factor (a gamma : ℝ) (z : ℂ) :
    selfDualQuartetPoly a gamma z =
      (z - (a : ℂ) - I * (gamma : ℂ)) * (z - (a : ℂ) + I * (gamma : ℂ)) *
        ((z + (a : ℂ) - I * (gamma : ℂ)) * (z + (a : ℂ) + I * (gamma : ℂ))) := by
  unfold selfDualQuartetPoly
  rw [block_factor a gamma z]
  have h2 : (z + (a : ℂ)) ^ 2 + (gamma : ℂ) ^ 2 =
      (z + (a : ℂ) - I * (gamma : ℂ)) * (z + (a : ℂ) + I * (gamma : ℂ)) := by
    have hI : (I : ℂ) ^ 2 = -1 := Complex.I_sq
    linear_combination ((gamma : ℂ)) ^ 2 * hI
  rw [h2]

/-- **The exact zero set.**  The quartet vanishes exactly at the four points
`1/2 ± a ± iγ`. -/
theorem selfDualQuartet_eq_zero_iff (a gamma : ℝ) (s : ℂ) :
    selfDualQuartet a gamma s = 0 ↔
      s = 1 / 2 + (a : ℂ) + I * (gamma : ℂ) ∨ s = 1 / 2 + (a : ℂ) - I * (gamma : ℂ) ∨
        s = 1 / 2 - (a : ℂ) + I * (gamma : ℂ) ∨ s = 1 / 2 - (a : ℂ) - I * (gamma : ℂ) := by
  rw [selfDualQuartet, selfDualQuartetPoly_factor, mul_eq_zero, mul_eq_zero, mul_eq_zero]
  constructor
  · rintro ((h | h) | h | h)
    · exact Or.inl (by linear_combination h)
    · exact Or.inr (Or.inl (by linear_combination h))
    · exact Or.inr (Or.inr (Or.inl (by linear_combination h)))
    · exact Or.inr (Or.inr (Or.inr (by linear_combination h)))
  · rintro (h | h | h | h)
    · exact Or.inl (Or.inl (by linear_combination h))
    · exact Or.inl (Or.inr (by linear_combination h))
    · exact Or.inr (Or.inl (by linear_combination h))
    · exact Or.inr (Or.inr (by linear_combination h))

/-- **Strip geometry.**  For `0 < a < 1/2` every zero of the quartet lies in the open critical
strip. -/
theorem selfDualQuartet_zero_mem_strip {a gamma : ℝ} (ha : 0 < a) (ha' : a < 1 / 2)
    {s : ℂ} (hs : selfDualQuartet a gamma s = 0) : 0 < s.re ∧ s.re < 1 := by
  rcases (selfDualQuartet_eq_zero_iff a gamma s).1 hs with h | h | h | h <;>
    rw [h] <;> simp <;> constructor <;> linarith

/-! ## Boundary unimodularity and the full-shift cocycle -/

/-- **Reflected shift identity on the critical line.** -/
theorem selfDualQuartet_shift_conj {a gamma : ℝ} {s : ℂ} (hs : s.re = 1 / 2) (omega : ℝ) :
    selfDualQuartet a gamma (s - (omega : ℂ)) =
      (starRingEnd ℂ) (selfDualQuartet a gamma (s + (omega : ℂ))) := by
  have hz : ((starRingEnd ℂ) (s - 1 / 2)) = -(s - 1 / 2) := by
    apply Complex.ext
    · simp [hs]
    · simp
  unfold selfDualQuartet
  rw [← selfDualQuartetPoly_conj]
  rw [show (s + (omega : ℂ) - 1 / 2 : ℂ) = (s - 1 / 2) + (omega : ℂ) by ring,
    map_add, Complex.conj_ofReal, hz,
    show (-(s - 1 / 2) + (omega : ℂ)) = -((s - 1 / 2) - (omega : ℂ)) by ring,
    selfDualQuartetPoly_even]
  congr 1
  ring

theorem norm_selfDualQuartet_shift {a gamma : ℝ} {s : ℂ} (hs : s.re = 1 / 2) (omega : ℝ) :
    ‖selfDualQuartet a gamma (s - (omega : ℂ))‖ =
      ‖selfDualQuartet a gamma (s + (omega : ℂ))‖ := by
  rw [selfDualQuartet_shift_conj hs omega, RCLike.norm_conj]

/-- The centered shifted quotient `R_ω(s) = F(s-ω)/F(s+ω)`. -/
def selfDualShiftRatio (a gamma omega : ℝ) (s : ℂ) : ℂ :=
  selfDualQuartet a gamma (s - (omega : ℂ)) / selfDualQuartet a gamma (s + (omega : ℂ))

/-- **Boundary unimodularity.**  On the critical line the shifted quotient has modulus one. -/
theorem norm_selfDualShiftRatio_eq_one {a gamma : ℝ} {s : ℂ} (hs : s.re = 1 / 2) (omega : ℝ)
    (hne : selfDualQuartet a gamma (s + (omega : ℂ)) ≠ 0) :
    ‖selfDualShiftRatio a gamma omega s‖ = 1 := by
  rw [selfDualShiftRatio, norm_div, norm_selfDualQuartet_shift hs omega,
    div_self (norm_ne_zero_iff.2 hne)]

/-- Boundary multiplication by the shifted quotient is a pointwise isometry, hence unitary on
`L²` of the critical line; any compression of it is therefore a contraction. -/
theorem norm_mul_selfDualShiftRatio {a gamma : ℝ} {s : ℂ} (hs : s.re = 1 / 2) (omega : ℝ)
    (hne : selfDualQuartet a gamma (s + (omega : ℂ)) ≠ 0) (f : ℂ) :
    ‖selfDualShiftRatio a gamma omega s * f‖ = ‖f‖ := by
  rw [norm_mul, norm_selfDualShiftRatio_eq_one hs omega hne, one_mul]

/-- **The exact full-shift cocycle** `R_{ω+η}(s) = R_ω(s-η) R_η(s+ω)`. -/
theorem selfDualShiftRatio_cocycle (a gamma omega eta : ℝ) (s : ℂ)
    (hmid : selfDualQuartet a gamma (s + (omega : ℂ) - (eta : ℂ)) ≠ 0) :
    selfDualShiftRatio a gamma (omega + eta) s =
      selfDualShiftRatio a gamma omega (s - (eta : ℂ)) *
        selfDualShiftRatio a gamma eta (s + (omega : ℂ)) := by
  unfold selfDualShiftRatio
  push_cast
  rw [show (s - (eta : ℂ) + (omega : ℂ)) = (s + (omega : ℂ) - (eta : ℂ)) by ring,
    show (s - (eta : ℂ) - (omega : ℂ)) = (s - ((omega : ℂ) + (eta : ℂ))) by ring,
    show (s + ((omega : ℂ) + (eta : ℂ))) = (s + (omega : ℂ) + (eta : ℂ)) by ring,
    div_mul_div_comm,
    mul_comm (selfDualQuartet a gamma (s - ((omega : ℂ) + (eta : ℂ))))
      (selfDualQuartet a gamma (s + (omega : ℂ) - (eta : ℂ))),
    mul_div_mul_left _ _ hmid]

/-! ## Theorem B: the curvature corner is unbounded -/

/-- The right-half divisor of the quartet: two simple zeros at displacement `a` and ordinates
`±γ`. -/
def selfDualQuartetOffsets (a : ℝ) : Fin 2 → ℝ := fun _ => a

/-- The two ordinates of the right-half divisor. -/
def selfDualQuartetOrdinates (gamma : ℝ) : Fin 2 → ℝ := ![gamma, -gamma]

/-- Both right-half zeros are simple. -/
def selfDualQuartetMultiplicities : Fin 2 → ℕ := fun _ => 1

/-- **The universal first-order residue profile of the quartet** is `4 e^{-at} cos(γt)`. -/
theorem selfDualQuartetProfile_eq (a gamma : ℝ) (t : ℝ) :
    finiteOfflineProfile (selfDualQuartetOffsets a) (selfDualQuartetOrdinates gamma)
        selfDualQuartetMultiplicities t
      = 4 * Complex.exp (-(a : ℂ) * (t : ℂ)) * Complex.cos ((gamma : ℂ) * (t : ℂ)) := by
  unfold finiteOfflineProfile finiteOfflineMode selfDualQuartetOffsets
    selfDualQuartetOrdinates selfDualQuartetMultiplicities
  rw [Fin.sum_univ_two]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Nat.cast_one, Complex.ofReal_neg]
  rw [Complex.cos]
  rw [show (-(a : ℂ) * (t : ℂ) - I * (gamma : ℂ) * (t : ℂ)) =
      (-(a : ℂ) * (t : ℂ)) + (-((gamma : ℂ) * (t : ℂ) * I)) by ring,
    show (-(a : ℂ) * (t : ℂ) - I * (-(gamma : ℂ)) * (t : ℂ)) =
      (-(a : ℂ) * (t : ℂ)) + ((gamma : ℂ) * (t : ℂ) * I) by ring,
    Complex.exp_add, Complex.exp_add]
  ring_nf

/-- **The exact curvature corner** `C_{a,γ}(0,0) = 4/a + 4a/(a²+γ²)`. -/
theorem selfDualQuartetCornerEnergy_eq {a : ℝ} (ha : 0 < a) (gamma : ℝ) :
    finiteOfflineCauchyEnergy (selfDualQuartetOffsets a) (selfDualQuartetOrdinates gamma)
        selfDualQuartetMultiplicities
      = 4 / a + 4 * a / (a ^ 2 + gamma ^ 2) := by
  have ha0 : a ≠ 0 := ne_of_gt ha
  have hden : a ^ 2 + gamma ^ 2 ≠ 0 := by positivity
  unfold finiteOfflineCauchyEnergy selfDualQuartetOffsets selfDualQuartetOrdinates
    selfDualQuartetMultiplicities transverseCauchyKernel
  rw [Fin.sum_univ_two, Fin.sum_univ_two, Fin.sum_univ_two]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Nat.cast_one, one_mul, mul_one]
  have h1 : (a + a) ^ 2 + (gamma - gamma) ^ 2 = 4 * a ^ 2 := by ring
  have h2 : (a + a) ^ 2 + (gamma - -gamma) ^ 2 = 4 * (a ^ 2 + gamma ^ 2) := by ring
  have h3 : (a + a) ^ 2 + (-gamma - gamma) ^ 2 = 4 * (a ^ 2 + gamma ^ 2) := by ring
  have h4 : (a + a) ^ 2 + (-gamma - -gamma) ^ 2 = 4 * a ^ 2 := by ring
  rw [h1, h2, h3, h4]
  have e1 : (a + a) / (4 * a ^ 2) = 1 / (2 * a) := by
    rw [div_eq_div_iff (by positivity) (by positivity)]; ring
  have e2 : (a + a) / (4 * (a ^ 2 + gamma ^ 2)) = a / (2 * (a ^ 2 + gamma ^ 2)) := by
    rw [div_eq_div_iff (by positivity) (by positivity)]; ring
  rw [e1, e2,
    div_add_div _ _ (by positivity : (2 : ℝ) * a ≠ 0)
      (by positivity : (2 : ℝ) * (a ^ 2 + gamma ^ 2) ≠ 0),
    div_add_div _ _ (by positivity : (2 : ℝ) * (a ^ 2 + gamma ^ 2) ≠ 0)
      (by positivity : (2 : ℝ) * a ≠ 0),
    div_add_div _ _ (by positivity : (2 : ℝ) * a * (2 * (a ^ 2 + gamma ^ 2)) ≠ 0)
      (by positivity : (2 : ℝ) * (a ^ 2 + gamma ^ 2) * (2 * a) ≠ 0),
    div_add_div _ _ (by positivity : a ≠ 0) (by positivity : a ^ 2 + gamma ^ 2 ≠ 0),
    ← mul_div_assoc, div_eq_div_iff (by positivity) (by positivity)]
  ring

/-- **The boundary energy of the quartet's anti-causal profile.** -/
theorem integral_norm_sq_selfDualQuartetProfile {a : ℝ} (ha : 0 < a) (gamma : ℝ) :
    ∫ t in Set.Ioi (0 : ℝ),
        ‖finiteOfflineProfile (selfDualQuartetOffsets a) (selfDualQuartetOrdinates gamma)
          selfDualQuartetMultiplicities t‖ ^ 2
      = 4 / a + 4 * a / (a ^ 2 + gamma ^ 2) := by
  rw [integral_norm_sq_finiteOfflineProfile (a := selfDualQuartetOffsets a)
      (gamma := selfDualQuartetOrdinates gamma) selfDualQuartetMultiplicities (fun _ => ha),
    selfDualQuartetCornerEnergy_eq ha gamma]

/-- **The corner exceeds the four-unit budget by more than a factor two.** -/
theorem selfDualQuartetCornerEnergy_gt_eight {a : ℝ} (ha : 0 < a) (ha' : a < 1 / 2) (gamma : ℝ) :
    8 < 4 / a + 4 * a / (a ^ 2 + gamma ^ 2) := by
  have hden : (0 : ℝ) < a ^ 2 + gamma ^ 2 := by positivity
  have h1 : 8 < 4 / a := by
    rw [lt_div_iff₀ ha]
    linarith
  have h2 : 0 ≤ 4 * a / (a ^ 2 + gamma ^ 2) := by positivity
  linarith

/-- **The corner is unbounded.**  As the transverse displacement tends to zero the curvature corner
tends to infinity, so no uniform bound is available from the generic data. -/
theorem tendsto_selfDualQuartetCornerEnergy_atTop (gamma : ℝ) :
    Filter.Tendsto (fun a : ℝ => 4 / a + 4 * a / (a ^ 2 + gamma ^ 2))
      (nhdsWithin 0 (Set.Ioi (0 : ℝ))) Filter.atTop := by
  have hinv : Filter.Tendsto (fun a : ℝ => 4 * a⁻¹)
      (nhdsWithin 0 (Set.Ioi (0 : ℝ))) Filter.atTop :=
    Filter.Tendsto.const_mul_atTop (by norm_num) tendsto_inv_nhdsGT_zero
  refine Filter.tendsto_atTop_mono' _ ?_ hinv
  filter_upwards [self_mem_nhdsWithin] with a ha
  have ha' : 0 < a := ha
  have hden : (0 : ℝ) < a ^ 2 + gamma ^ 2 := by positivity
  have h2 : 0 ≤ 4 * a / (a ^ 2 + gamma ^ 2) := by positivity
  rw [← div_eq_mul_inv]
  linarith

end

end RHTower
