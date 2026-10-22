import GaloisForLFunctions.RHTower.CCM.CCMLogDiracRankOneDeterminant
import GaloisForLFunctions.RHTower.CCM.CCMCircleDiracZetaDeterminant
import GaloisForLFunctions.RHTower.CCM.CCMPublishedRestrictedWeilMatrix

/-!
# `D_log^{(λ,N)}`: Weil-metric self-adjointness and the regularized determinant

Connes--Consani--Moscovici, *Zeta Spectral Triples*, Theorem 5.10, on the literal finite
restricted-Weil matrix `W` of the centered packet `{-N, …, N}` at aperture `λ = e^a`.

* `ε` is the least eigenvalue of `W` and `T = W - ε` is the Weil metric (positive semidefinite and
  singular).
* For a ground vector `ξ` (`Tξ = 0`) normalized by the boundary functional, `∑ ξ_i = 1`, the
  logarithmic Dirac operator `D_log^{(λ,N)}` is the free circle Dirac operator `d_n = πn/a` with
  its centered block replaced by `A = D - |Dξ⟩⟨η|`, `η = 1`.  `A` is `T`-self-adjoint and kills
  `ξ`; on `ℂ^{2N+1}/ℂξ` its characteristic polynomial is `P_ξ`.
* `det_reg(D_log - z)` is the ζ-regularized product over the spectrum
  `{d_n : |n| > N} ∪ roots(P_ξ)`; for `Im z < 0`

  `det_reg(D_log - z) = -i λ^{-iz} ξ̂(z)`,
  `ξ̂(z) = ∫_{-a}^{a} ∑_i ξ_i e^{i d_i (x+a)} e^{-izx} dx`.

* **Unconditional dichotomy.**  Either the boundary channel meets the ground level, and then the
  canonical normalized ground vector carries all of the above with only real zeros of `ξ̂`; or every
  ground vector is boundary-blind and the odd response channel carries a metric-self-adjoint
  completion with real spectrum.  The published simple-even hypothesis forces the first branch with
  `ξ` the normalized ground vector.
-/

noncomputable section

open Complex Polynomial Matrix MeasureTheory
open scoped ComplexOrder

namespace RHTower

/-! ## Ground energy and Weil metric of the literal matrix -/

theorem ccmPublishedWeilMatrixC_isHermitian (a : ℝ) (N : ℕ) :
    ((ccmPublishedRestrictedWeilMatrix a N).map (algebraMap ℝ ℂ)).IsHermitian :=
  realSymmetric_complexification_isHermitian _ (ccmPublishedRestrictedWeilMatrix_transpose a N)

/-- CCM ground energy `ε(λ,N)`: the least eigenvalue of the literal finite matrix. -/
def ccmPublishedGroundEnergy (a : ℝ) (N : ℕ) : ℝ :=
  Finset.univ.inf' Finset.univ_nonempty (ccmPublishedWeilMatrixC_isHermitian a N).eigenvalues

/-- The Weil metric `T = W - ε` on the centered packet. -/
def ccmPublishedWeilMetric (a : ℝ) (N : ℕ) : Matrix (Fin (2 * N + 1)) (Fin (2 * N + 1)) ℂ :=
  (ccmScalarShift (ccmPublishedRestrictedWeilMatrix a N) (ccmPublishedGroundEnergy a N)).map
    (algebraMap ℝ ℂ)

/-- The Weil metric is positive semidefinite and singular. -/
theorem ccmPublishedWeilMetric_posSemidef_singular (a : ℝ) (N : ℕ) :
    (ccmPublishedWeilMetric a N).PosSemidef ∧
      ∃ k : Fin (2 * N + 1) → ℂ, ccmPublishedWeilMetric a N *ᵥ k = 0 ∧ k ≠ 0 := by
  set Q := ccmPublishedRestrictedWeilMatrix a N
  set QC := Q.map (algebraMap ℝ ℂ)
  have hQC : QC.IsHermitian := ccmPublishedWeilMatrixC_isHermitian a N
  obtain ⟨i0, -, hi0⟩ := Finset.exists_mem_eq_inf' Finset.univ_nonempty hQC.eigenvalues
  set mu := ccmPublishedGroundEnergy a N
  have hmu : mu = hQC.eigenvalues i0 := hi0
  have hmin : ∀ i, mu ≤ hQC.eigenvalues i := fun i => Finset.inf'_le _ (Finset.mem_univ i)
  let U : Matrix (Fin (2 * N + 1)) (Fin (2 * N + 1)) ℂ := hQC.eigenvectorUnitary
  let d : Fin (2 * N + 1) → ℂ := fun i => ((hQC.eigenvalues i - mu : ℝ) : ℂ)
  have hdiag : (Matrix.diagonal d).PosSemidef :=
    Matrix.PosSemidef.diagonal fun i => RCLike.ofReal_nonneg.mpr (sub_nonneg.mpr (hmin i))
  have hspec : QC = U * Matrix.diagonal (fun i => (hQC.eigenvalues i : ℂ)) * Uᴴ := by
    simpa [U, Function.comp_def, Matrix.star_eq_conjTranspose] using hQC.spectral_theorem
  have hUunit : U * Uᴴ = 1 := by
    change (hQC.eigenvectorUnitary : Matrix (Fin (2 * N + 1)) (Fin (2 * N + 1)) ℂ) *
        (hQC.eigenvectorUnitary : Matrix (Fin (2 * N + 1)) (Fin (2 * N + 1)) ℂ)ᴴ = 1
    rw [← Matrix.star_eq_conjTranspose]
    exact Unitary.coe_mul_star_self hQC.eigenvectorUnitary
  have hshift : QC - (mu : ℂ) • (1 : Matrix (Fin (2 * N + 1)) (Fin (2 * N + 1)) ℂ) =
      U * Matrix.diagonal d * Uᴴ := by
    have hdiagShift : Matrix.diagonal (fun i => (hQC.eigenvalues i : ℂ)) -
        (mu : ℂ) • (1 : Matrix (Fin (2 * N + 1)) (Fin (2 * N + 1)) ℂ) = Matrix.diagonal d := by
      ext i j
      by_cases hij : i = j
      · subst j; simp [d]
      · simp [Matrix.diagonal, hij]
    calc QC - (mu : ℂ) • (1 : Matrix (Fin (2 * N + 1)) (Fin (2 * N + 1)) ℂ)
        = U * Matrix.diagonal (fun i => (hQC.eigenvalues i : ℂ)) * Uᴴ -
            U * ((mu : ℂ) • 1) * Uᴴ := by
          rw [← hspec]
          congr 1
          calc (mu : ℂ) • (1 : Matrix (Fin (2 * N + 1)) (Fin (2 * N + 1)) ℂ)
              = (mu : ℂ) • (U * Uᴴ) := by rw [hUunit]
            _ = U * ((mu : ℂ) • 1) * Uᴴ := by simp
      _ = U * (Matrix.diagonal (fun i => (hQC.eigenvalues i : ℂ)) - (mu : ℂ) • 1) * Uᴴ := by
          noncomm_ring
      _ = U * Matrix.diagonal d * Uᴴ := by rw [hdiagShift]
  have hmap : ccmPublishedWeilMetric a N =
      QC - (mu : ℂ) • (1 : Matrix (Fin (2 * N + 1)) (Fin (2 * N + 1)) ℂ) := by
    ext i j
    by_cases hij : i = j
    · subst j; simp [ccmPublishedWeilMetric, ccmScalarShift, Q, QC, mu]
    · simp [ccmPublishedWeilMetric, ccmScalarShift, Q, QC, hij]
  refine ⟨by rw [hmap, hshift]; exact hdiag.mul_mul_conjTranspose_same U, ?_⟩
  let c : Fin (2 * N + 1) → ℂ := ⇑(hQC.eigenvectorBasis i0)
  refine ⟨c, ?_, (WithLp.ofLp_eq_zero 2).ne.mpr (hQC.eigenvectorBasis.orthonormal.ne_zero i0)⟩
  rw [hmap, Matrix.sub_mulVec, hQC.mulVec_eigenvectorBasis, Matrix.smul_mulVec,
    Matrix.one_mulVec, hmu]
  simp [c]

/-- The source/response completion certificate at the true ground energy. -/
theorem ccmPublishedWeilMetric_hasSourceResponseCompletion (a : ℝ) (N : ℕ) :
    HasCCMSourceResponseCompletion (ccmPublishedWeilMetric a N)
      (Matrix.diagonal (fun i => (ccmPublishedCenteredClock N i : ℂ)))
      (fun i => (ccmPublishedCenteredSource a N i : ℂ)) :=
  ccmPublishedRestrictedWeilMatrix_hasSourceResponseCompletion a (ccmPublishedGroundEnergy a N) N
    (ccmPublishedWeilMetric_posSemidef_singular a N).1
    (ccmPublishedWeilMetric_posSemidef_singular a N).2

/-! ## The physical clock and the finite block of `D_log` -/

/-- Physical clock `d_i = πn_i/a` of the centered packet. -/
def ccmPublishedPhysicalClock (a : ℝ) (N : ℕ) (i : Fin (2 * N + 1)) : ℂ :=
  (ccmPublishedCenteredFrequency a N i : ℂ)

theorem ccmPublishedPhysicalClock_eq_smul (a : ℝ) (N : ℕ) (i : Fin (2 * N + 1)) :
    ccmPublishedPhysicalClock a N i =
      ((Real.pi / a : ℝ) : ℂ) * (ccmPublishedCenteredClock N i : ℂ) := by
  unfold ccmPublishedPhysicalClock ccmPublishedCenteredFrequency
  push_cast
  ring

theorem ccmPublishedPhysicalClock_eq_logDirac (a : ℝ) (N : ℕ) (i : Fin (2 * N + 1)) :
    ccmPublishedPhysicalClock a N i =
      ((ccmLogDiracFrequency a (ccmPublishedCenteredMode N i) : ℝ) : ℂ) := by
  rfl

theorem ccmPublishedPhysicalClock_im (a : ℝ) (N : ℕ) (i : Fin (2 * N + 1)) :
    (ccmPublishedPhysicalClock a N i).im = 0 := Complex.ofReal_im _

/-- Finite block `A = D - |Dξ⟩⟨η|` of `D_log^{(λ,N)}`, with `η = 1`. -/
def ccmLogDiracBlock (a : ℝ) (N : ℕ) (ξ : Fin (2 * N + 1) → ℂ) :
    Matrix (Fin (2 * N + 1)) (Fin (2 * N + 1)) ℂ :=
  ccmSourceCompletion (Matrix.diagonal (ccmPublishedPhysicalClock a N)) ξ (fun _ => 1)

theorem ccmLogDiracBlock_eq_smul (a : ℝ) (N : ℕ) (ξ : Fin (2 * N + 1) → ℂ) :
    ccmLogDiracBlock a N ξ = ((Real.pi / a : ℝ) : ℂ) •
      ccmSourceCompletion (Matrix.diagonal fun i => (ccmPublishedCenteredClock N i : ℂ)) ξ
        (fun _ => 1) := by
  ext i j
  simp only [ccmLogDiracBlock, ccmSourceCompletion, Matrix.sub_apply, Matrix.smul_apply,
    Matrix.vecMulVec_apply, Matrix.mulVec_diagonal, Matrix.diagonal_apply,
    ccmPublishedPhysicalClock_eq_smul, smul_eq_mul]
  split_ifs <;> ring

/-- `A` kills the normalized ground vector. -/
theorem ccmLogDiracBlock_mulVec_self (a : ℝ) (N : ℕ) {ξ : Fin (2 * N + 1) → ℂ}
    (hξ : ∑ i, ξ i = 1) : ccmLogDiracBlock a N ξ *ᵥ ξ = 0 :=
  ccmSourceCompletion_mulVec_c _ ξ _ (by simp [dotProduct, hξ])

/-- `T`-self-adjointness transfers from the dimensionless to the physical clock. -/
theorem ccmLogDiracBlock_metricAdjoint (a : ℝ) (N : ℕ) {ξ : Fin (2 * N + 1) → ℂ}
    {T : Matrix (Fin (2 * N + 1)) (Fin (2 * N + 1)) ℂ}
    (h : T * ccmSourceCompletion (Matrix.diagonal fun i => (ccmPublishedCenteredClock N i : ℂ)) ξ
        (fun _ => 1) =
      (ccmSourceCompletion (Matrix.diagonal fun i => (ccmPublishedCenteredClock N i : ℂ)) ξ
        (fun _ => 1))ᴴ * T) :
    T * ccmLogDiracBlock a N ξ = (ccmLogDiracBlock a N ξ)ᴴ * T := by
  rw [ccmLogDiracBlock_eq_smul, Matrix.conjTranspose_smul, Matrix.mul_smul, Matrix.smul_mul, h]
  congr 1
  exact (Complex.conj_ofReal _).symm

/-- `P_ξ` for the physical clock is the rescaled dimensionless one. -/
theorem eval_physical_quotientCharpoly (a : ℝ) (ha : 0 < a) (N : ℕ) (ξ : Fin (2 * N + 1) → ℂ)
    (z : ℂ) :
    (ccmRankOneQuotientCharpoly (ccmPublishedPhysicalClock a N) ξ).eval z =
      ((Real.pi / a : ℝ) : ℂ) ^ (2 * N) *
        (ccmRankOneQuotientCharpoly (fun i => (ccmPublishedCenteredClock N i : ℂ)) ξ).eval
          (z / ((Real.pi / a : ℝ) : ℂ)) := by
  have hr : ((Real.pi / a : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (div_pos Real.pi_pos ha).ne'
  rw [eval_ccmRankOneQuotientCharpoly, eval_ccmRankOneQuotientCharpoly, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hcard : (Finset.univ.erase i).card = 2 * N := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_univ, Fintype.card_fin]
    omega
  have hprod : ∏ j ∈ Finset.univ.erase i, (z - ccmPublishedPhysicalClock a N j) =
      ∏ j ∈ Finset.univ.erase i,
        (((Real.pi / a : ℝ) : ℂ) * (z / ((Real.pi / a : ℝ) : ℂ) -
          (ccmPublishedCenteredClock N j : ℂ))) := by
    refine Finset.prod_congr rfl fun j _ => ?_
    rw [ccmPublishedPhysicalClock_eq_smul]
    field_simp
  rw [hprod, Finset.prod_mul_distrib, Finset.prod_const, hcard]
  ring

/-- Real spectrum of the dimensionless completion gives real roots of the physical `P_ξ`. -/
theorem physical_quotientCharpoly_root_im_eq_zero (a : ℝ) (ha : 0 < a) (N : ℕ)
    {ξ : Fin (2 * N + 1) → ℂ} (hξ : ∑ i, ξ i = 1)
    (hreal : ∀ z : ℂ,
      (ccmSourceCompletion (Matrix.diagonal fun i => (ccmPublishedCenteredClock N i : ℂ)) ξ
        (fun _ => 1)).charpoly.eval z = 0 → z.im = 0)
    {μ : ℂ} (hμ : (ccmRankOneQuotientCharpoly (ccmPublishedPhysicalClock a N) ξ).eval μ = 0) :
    μ.im = 0 := by
  have hr : ((Real.pi / a : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (div_pos Real.pi_pos ha).ne'
  rw [eval_physical_quotientCharpoly a ha N ξ μ] at hμ
  have hroot := (mul_eq_zero.mp hμ).resolve_left (pow_ne_zero _ hr)
  have him := ccmRankOneQuotientCharpoly_root_im_eq_zero _ ξ hξ hreal hroot
  have hdiv : (μ / ((Real.pi / a : ℝ) : ℂ)).im = μ.im / (Real.pi / a) := by
    rw [Complex.div_ofReal_im]
  rw [hdiv] at him
  exact (div_eq_zero_iff.mp him).resolve_right (div_pos Real.pi_pos ha).ne'

/-! ## The packet transform `ξ̂` -/

/-- The centered packet function `ξ(x) = ∑_i ξ_i e^{i d_i (x+a)}` on `[-a, a]`, `x = log u`;
each mode takes the boundary value `1` at both ends. -/
def ccmPublishedPacketFunction (a : ℝ) (N : ℕ) (ξ : Fin (2 * N + 1) → ℂ) (x : ℝ) : ℂ :=
  ∑ i, ξ i * Complex.exp (I * ccmPublishedPhysicalClock a N i * ((x : ℂ) + a))

/-- `ξ̂(z) = ∫_{λ⁻¹}^{λ} ξ(u) u^{-iz} d*u = ∫_{-a}^{a} ξ(x) e^{-izx} dx`. -/
def ccmPublishedPacketTransform (a : ℝ) (N : ℕ) (ξ : Fin (2 * N + 1) → ℂ) (z : ℂ) : ℂ :=
  ∫ x in (-a)..a, ccmPublishedPacketFunction a N ξ x * Complex.exp (-I * z * x)

theorem exp_two_mul_physicalClock (a : ℝ) (ha : 0 < a) (N : ℕ) (i : Fin (2 * N + 1)) :
    Complex.exp (2 * I * ccmPublishedPhysicalClock a N i * a) = 1 := by
  have h : 2 * I * ccmPublishedPhysicalClock a N i * a =
      (ccmPublishedCenteredMode N i : ℂ) * (2 * Real.pi * I) := by
    rw [ccmPublishedPhysicalClock_eq_smul]
    unfold ccmPublishedCenteredClock
    have ha' : (a : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ha.ne'
    push_cast
    field_simp
  rw [h, Complex.exp_int_mul_two_pi_mul_I]

/-- Closed form of `ξ̂` off the clock: `ξ̂(z) = (e^{-iaz} - e^{iaz})/i · ∑_i ξ_i/(d_i - z)`. -/
theorem ccmPublishedPacketTransform_eq (a : ℝ) (ha : 0 < a) (N : ℕ) (ξ : Fin (2 * N + 1) → ℂ)
    {z : ℂ} (hz : ∀ i, ccmPublishedPhysicalClock a N i - z ≠ 0) :
    ccmPublishedPacketTransform a N ξ z =
      (Complex.exp (-I * a * z) - Complex.exp (I * a * z)) / I *
        ∑ i, ξ i / (ccmPublishedPhysicalClock a N i - z) := by
  unfold ccmPublishedPacketTransform ccmPublishedPacketFunction
  have hmode : ∀ i, (∫ x in (-a)..a,
      ξ i * Complex.exp (I * ccmPublishedPhysicalClock a N i * ((x : ℂ) + a)) *
        Complex.exp (-I * z * x)) =
      (Complex.exp (-I * a * z) - Complex.exp (I * a * z)) / I *
        (ξ i / (ccmPublishedPhysicalClock a N i - z)) := by
    intro i
    set d := ccmPublishedPhysicalClock a N i
    have hc : I * (d - z) ≠ 0 := mul_ne_zero I_ne_zero (hz i)
    have hfun : (fun x : ℝ => ξ i * Complex.exp (I * d * ((x : ℂ) + a)) *
        Complex.exp (-I * z * x)) =
        fun x : ℝ => ξ i * Complex.exp (I * d * a) * Complex.exp (I * (d - z) * x) := by
      funext x
      have hexp : I * d * ((x : ℂ) + a) + -I * z * x = I * d * a + I * (d - z) * x := by ring
      rw [mul_assoc (ξ i), ← Complex.exp_add, hexp, Complex.exp_add]
      ring
    rw [hfun, intervalIntegral.integral_const_mul, integral_exp_mul_complex hc]
    have h2 := exp_two_mul_physicalClock a ha N i
    have hsplit1 : Complex.exp (I * d * a) * Complex.exp (I * (d - z) * (a : ℂ)) =
        Complex.exp (-I * a * z) := by
      rw [← Complex.exp_add, show I * d * a + I * (d - z) * a = 2 * I * d * a + -I * a * z by ring,
        Complex.exp_add, h2, one_mul]
    have hsplit2 : Complex.exp (I * d * a) * Complex.exp (I * (d - z) * ((-a : ℝ) : ℂ)) =
        Complex.exp (I * a * z) := by
      rw [← Complex.exp_add]
      congr 1
      push_cast
      ring
    rw [mul_assoc, mul_div_assoc', mul_sub, hsplit1, hsplit2]
    field_simp
  simp_rw [Finset.sum_mul]
  rw [intervalIntegral.integral_finsetSum
      fun i _ => Continuous.intervalIntegrable (by fun_prop) _ _,
    Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => hmode i

/-- `λ^{-iz} = e^{-iaz}` for `λ = e^a`. -/
theorem ofReal_exp_cpow_neg_I_mul (a : ℝ) (z : ℂ) :
    ((Real.exp a : ℝ) : ℂ) ^ (-I * z) = Complex.exp (-I * a * z) := by
  rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr (Real.exp_pos a).ne'),
    Complex.ofReal_exp, Complex.log_exp (by simp [Real.pi_pos]) (by simp [Real.pi_pos.le])]
  congr 1
  ring

/-- `-i λ^{-iz} ξ̂(z) = (1 - λ^{-2iz}) ∑_i ξ_i/(d_i - z)` off the clock. -/
theorem neg_I_mul_cpow_mul_packetTransform (a : ℝ) (ha : 0 < a) (N : ℕ)
    (ξ : Fin (2 * N + 1) → ℂ) {z : ℂ} (hz : ∀ i, ccmPublishedPhysicalClock a N i - z ≠ 0) :
    -I * ((Real.exp a : ℝ) : ℂ) ^ (-I * z) * ccmPublishedPacketTransform a N ξ z =
      (1 - Complex.exp (-2 * I * (a : ℂ) * z)) *
        ∑ i, ξ i / (ccmPublishedPhysicalClock a N i - z) := by
  rw [ccmPublishedPacketTransform_eq a ha N ξ hz, ofReal_exp_cpow_neg_I_mul]
  have h2 : Complex.exp (-2 * I * (a : ℂ) * z) =
      Complex.exp (-I * a * z) * Complex.exp (-I * a * z) := by
    rw [← Complex.exp_add]; congr 1; ring
  have h1 : Complex.exp (-I * a * z) * Complex.exp (I * a * z) = 1 := by
    rw [← Complex.exp_add]; simp
  have hI : I * I⁻¹ = 1 := mul_inv_cancel₀ I_ne_zero
  rw [h2, div_eq_mul_inv]
  linear_combination (-(Complex.exp (-I * a * z) *
      (Complex.exp (-I * a * z) - Complex.exp (I * a * z)) *
        ∑ i, ξ i / (ccmPublishedPhysicalClock a N i - z))) * hI +
    (∑ i, ξ i / (ccmPublishedPhysicalClock a N i - z)) * h1

/-- Zeros of `ξ̂` are real whenever all roots of `P_ξ` are real. -/
theorem ccmPublishedPacketTransform_zero_im_eq_zero (a : ℝ) (ha : 0 < a) (N : ℕ)
    {ξ : Fin (2 * N + 1) → ℂ}
    (hroots : ∀ μ, (ccmRankOneQuotientCharpoly (ccmPublishedPhysicalClock a N) ξ).eval μ = 0 →
      μ.im = 0)
    {z : ℂ} (hzero : ccmPublishedPacketTransform a N ξ z = 0) : z.im = 0 := by
  by_contra him
  have hz : ∀ i, ccmPublishedPhysicalClock a N i - z ≠ 0 := by
    intro i h
    apply him
    have := congrArg Complex.im h
    simp [ccmPublishedPhysicalClock_im] at this
    linarith
  have hz' : ∀ i, z - ccmPublishedPhysicalClock a N i ≠ 0 := fun i h =>
    hz i (by rw [← neg_sub, h, neg_zero])
  rw [ccmPublishedPacketTransform_eq a ha N ξ hz] at hzero
  have hpref : (Complex.exp (-I * a * z) - Complex.exp (I * a * z)) / I ≠ 0 := by
    refine div_ne_zero (sub_ne_zero.mpr fun h => ?_) I_ne_zero
    have hn := congrArg norm h
    rw [Complex.norm_exp, Complex.norm_exp] at hn
    have hre1 : (-I * (a : ℂ) * z).re = a * z.im := by simp [Complex.mul_re]
    have hre2 : (I * (a : ℂ) * z).re = -(a * z.im) := by simp [Complex.mul_re]
    rw [hre1, hre2, Real.exp_eq_exp] at hn
    exact him (by nlinarith [mul_pos ha ha])
  have hsum := (mul_eq_zero.mp hzero).resolve_left hpref
  apply him
  apply hroots
  rw [eval_ccmRankOneQuotientCharpoly_eq_mul_resolvent _ ξ hz']
  have hflip : ∑ i, ξ i / (z - ccmPublishedPhysicalClock a N i) =
      -∑ i, ξ i / (ccmPublishedPhysicalClock a N i - z) := by
    rw [← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun i _ => by rw [← neg_sub, div_neg]
  rw [hflip, hsum, neg_zero, mul_zero]

/-! ## The regularized determinant -/

/-- Spectral zeta function of `D_log - z`: the circle Dirac spectrum with the centered block
replaced by the quotient spectrum `roots(P_ξ)`. -/
def ccmLogDiracSpectralZeta (a : ℝ) (N : ℕ) (ξ : Fin (2 * N + 1) → ℂ) (z s : ℂ) : ℂ :=
  ccmRankOneModifiedZeta (ccmLogDiracZeta a z) (ccmPublishedPhysicalClock a N) ξ z s

/-- **`det_reg(D_log^{(λ,N)} - z) = exp(-ζ'_{D_log - z}(0))`.** -/
def ccmLogDiracRegularizedDeterminant (a : ℝ) (N : ℕ) (ξ : Fin (2 * N + 1) → ℂ) (z : ℂ) : ℂ :=
  Complex.exp (-deriv (ccmLogDiracSpectralZeta a N ξ z) 0)

/-- The centered packet indexes the mode window `{-N, …, N}`. -/
theorem sum_Icc_eq_sum_centeredMode (N : ℕ) (g : ℤ → ℂ) :
    ∑ n ∈ Finset.Icc (-(N : ℤ)) N, g n =
      ∑ i : Fin (2 * N + 1), g (ccmPublishedCenteredMode N i) := by
  symm
  refine Finset.sum_bij (fun i _ => ccmPublishedCenteredMode N i) ?_ ?_ ?_ ?_
  · intro i _
    simp only [Finset.mem_Icc, ccmPublishedCenteredMode]
    omega
  · intro i _ j _ h
    simp only [ccmPublishedCenteredMode] at h
    exact Fin.ext (by omega)
  · intro n hn
    simp only [Finset.mem_Icc] at hn
    refine ⟨⟨(n + N).toNat, by omega⟩, Finset.mem_univ _, ?_⟩
    simp only [ccmPublishedCenteredMode]
    omega
  · intro i _
    rfl

/-- For `Re s > 1` the spectral zeta function of `D_log - z` is the series over its spectrum:
the tail `{d_n : |n| > N}` together with the roots of `P_ξ`. -/
theorem ccmLogDiracSpectralZeta_eq_series (a : ℝ) (ha : 0 < a) (N : ℕ)
    (ξ : Fin (2 * N + 1) → ℂ) {z : ℂ} (hz : z.im < 0) {s : ℂ} (hs : 1 < s.re) :
    ccmLogDiracSpectralZeta a N ξ z s =
      ∑' n : ↑((Finset.Icc (-(N : ℤ)) N : Set ℤ)ᶜ),
          (((ccmLogDiracFrequency a n : ℝ) : ℂ) - z) ^ (-s) +
        ((ccmRankOneQuotientCharpoly (ccmPublishedPhysicalClock a N) ξ).roots.map
          fun μ => (μ - z) ^ (-s)).sum := by
  unfold ccmLogDiracSpectralZeta ccmRankOneModifiedZeta
  rw [ccmLogDiracZeta_eq_tsum ha hz hs,
    ← (summable_ccmLogDiracSpectrum ha hz hs).sum_add_tsum_compl (s := Finset.Icc (-(N : ℤ)) N),
    sum_Icc_eq_sum_centeredMode]
  simp only [ccmPublishedPhysicalClock_eq_logDirac]
  ring

/-- **CCM Theorem 5.10, determinant identity.**  For a normalized vector `ξ` whose quotient
spectrum is real, `det_reg(D_log - z) = -i λ^{-iz} ξ̂(z)` for every `Im z < 0`. -/
theorem ccmLogDiracRegularizedDeterminant_eq (a : ℝ) (ha : 0 < a) (N : ℕ)
    {ξ : Fin (2 * N + 1) → ℂ} (hξ : ∑ i, ξ i = 1)
    (hroots : ∀ μ, (ccmRankOneQuotientCharpoly (ccmPublishedPhysicalClock a N) ξ).eval μ = 0 →
      μ.im = 0)
    {z : ℂ} (hz : z.im < 0) :
    ccmLogDiracRegularizedDeterminant a N ξ z =
      -I * ((Real.exp a : ℝ) : ℂ) ^ (-I * z) * ccmPublishedPacketTransform a N ξ z := by
  have hd : ∀ i, ccmPublishedPhysicalClock a N i - z ≠ 0 := by
    intro i h
    have := congrArg Complex.im h
    simp [ccmPublishedPhysicalClock_im] at this
    linarith
  have hroot' : ∀ μ ∈ (ccmRankOneQuotientCharpoly (ccmPublishedPhysicalClock a N) ξ).roots,
      μ - z ≠ 0 := by
    intro μ hμ h
    have hμ' := hroots μ (Polynomial.isRoot_of_mem_roots hμ)
    have := congrArg Complex.im h
    simp [hμ'] at this
    linarith
  have hZ := hasDerivAt_ccmLogDiracZeta_zero ha hz
  have hdet := exp_neg_deriv_ccmRankOneModifiedZeta hZ (ccmPublishedPhysicalClock a N) ξ hξ
    (by simp) hd hroot'
  have hzeta : ccmLogDiracSpectralZeta a N ξ z =
      ccmRankOneModifiedZeta (ccmLogDiracZeta a z) (ccmPublishedPhysicalClock a N) ξ z := rfl
  rw [ccmLogDiracRegularizedDeterminant, hzeta, hdet,
    neg_I_mul_cpow_mul_packetTransform a ha N ξ hd]
  congr 1
  rw [← hZ.deriv]
  exact exp_neg_deriv_ccmLogDiracZeta_zero ha hz

/-! ## The unconditional theorem and the published simple-even case -/

/-- **CCM Theorem 5.10, unconditional form.**  At every aperture `λ = e^a > 1` and cutoff `N`,
either the boundary channel meets the ground level of the literal matrix, and then a normalized
ground vector `ξ` gives a `T`-self-adjoint `D_log^{(λ,N)}` killing `ξ`, with real quotient
spectrum, only real zeros of `ξ̂`, and `det_reg(D_log - z) = -i λ^{-iz} ξ̂(z)`; or the ground level
is boundary-blind and the odd response channel carries a `T`-self-adjoint completion with real
spectrum. -/
theorem ccmPublished_logDirac_theorem (a : ℝ) (ha : 0 < a) (N : ℕ) :
    (∃ ξ : Fin (2 * N + 1) → ℂ,
        ccmPublishedWeilMetric a N *ᵥ ξ = 0 ∧ ∑ i, ξ i = 1 ∧
        ccmPublishedWeilMetric a N * ccmLogDiracBlock a N ξ =
          (ccmLogDiracBlock a N ξ)ᴴ * ccmPublishedWeilMetric a N ∧
        ccmLogDiracBlock a N ξ *ᵥ ξ = 0 ∧
        (ccmLogDiracBlock a N ξ).charpoly =
          X * ccmRankOneQuotientCharpoly (ccmPublishedPhysicalClock a N) ξ ∧
        (∀ μ, (ccmRankOneQuotientCharpoly (ccmPublishedPhysicalClock a N) ξ).eval μ = 0 →
          μ.im = 0) ∧
        (∀ z, ccmPublishedPacketTransform a N ξ z = 0 → z.im = 0) ∧
        ∀ z, z.im < 0 → ccmLogDiracRegularizedDeterminant a N ξ z =
          -I * ((Real.exp a : ℝ) : ℂ) ^ (-I * z) * ccmPublishedPacketTransform a N ξ z) ∨
    (∃ c : Fin (2 * N + 1) → ℂ,
        ccmPublishedWeilMetric a N *ᵥ c = 0 ∧
        star (fun i => (ccmPublishedCenteredSource a N i : ℂ)) ⬝ᵥ c = 1 ∧
        ccmPublishedWeilMetric a N * ccmSourceCompletion
            (Matrix.diagonal fun i => (ccmPublishedCenteredClock N i : ℂ)) c
            (fun i => (ccmPublishedCenteredSource a N i : ℂ)) =
          (ccmSourceCompletion (Matrix.diagonal fun i => (ccmPublishedCenteredClock N i : ℂ)) c
            (fun i => (ccmPublishedCenteredSource a N i : ℂ)))ᴴ * ccmPublishedWeilMetric a N ∧
        ∀ z, (ccmSourceCompletion (Matrix.diagonal fun i => (ccmPublishedCenteredClock N i : ℂ))
          c (fun i => (ccmPublishedCenteredSource a N i : ℂ))).charpoly.eval z = 0 →
            z.im = 0) := by
  obtain ⟨α, c, hα, hTc, hnorm, hmetric, hreal⟩ :=
    ccmPublishedWeilMetric_hasSourceResponseCompletion a N
  rcases hα with rfl | rfl
  · have hξ : ∑ i, c i = 1 := by simpa [dotProduct] using hnorm
    have hroots := fun μ => physical_quotientCharpoly_root_im_eq_zero a ha N hξ hreal (μ := μ)
    refine Or.inl ⟨c, hTc, hξ, ccmLogDiracBlock_metricAdjoint a N hmetric,
      ccmLogDiracBlock_mulVec_self a N hξ,
      charpoly_ccmSourceCompletion_diagonal _ c hξ, hroots,
      fun z hz => ccmPublishedPacketTransform_zero_im_eq_zero a ha N hroots hz,
      fun z hz => ccmLogDiracRegularizedDeterminant_eq a ha N hξ hroots hz⟩
  · exact Or.inr ⟨c, hTc, hnorm, hmetric, hreal⟩

/-- **CCM Theorem 5.10 under the published hypothesis.**  If the ground level of the literal matrix
lies on the line of a reflection-even vector `v`, then `∑ v ≠ 0` and the normalized vector
`ξ = v/∑ v` carries the full first alternative of `ccmPublished_logDirac_theorem`: the odd source
cannot see `v`, which excludes the response branch. -/
theorem ccmPublished_logDirac_simpleEven (a : ℝ) (ha : 0 < a) (N : ℕ)
    {v : Fin (2 * N + 1) → ℂ}
    (hsimple : ∀ k, ccmPublishedWeilMetric a N *ᵥ k = 0 → ∃ t : ℂ, k = t • v)
    (heven : ∀ i, v (Fin.rev i) = v i) :
    ∑ i, v i ≠ 0 ∧
      let ξ := (∑ i, v i)⁻¹ • v
      ccmPublishedWeilMetric a N * ccmLogDiracBlock a N ξ =
          (ccmLogDiracBlock a N ξ)ᴴ * ccmPublishedWeilMetric a N ∧
        ccmLogDiracBlock a N ξ *ᵥ ξ = 0 ∧
        (∀ z, ccmPublishedPacketTransform a N ξ z = 0 → z.im = 0) ∧
        ∀ z, z.im < 0 → ccmLogDiracRegularizedDeterminant a N ξ z =
          -I * ((Real.exp a : ℝ) : ℂ) ^ (-I * z) * ccmPublishedPacketTransform a N ξ z := by
  have hodd : ∀ i, (ccmPublishedCenteredSource a N (Fin.rev i) : ℂ) =
      -(ccmPublishedCenteredSource a N i : ℂ) := by
    intro i
    have h := ccmPublishedCenteredSource_rev a N i
    simp only [Fin.revPerm_apply] at h
    exact_mod_cast h
  have hblind : star (fun i => (ccmPublishedCenteredSource a N i : ℂ)) ⬝ᵥ v = 0 := by
    have hsum : star (fun i => (ccmPublishedCenteredSource a N i : ℂ)) ⬝ᵥ v =
        -(star (fun i => (ccmPublishedCenteredSource a N i : ℂ)) ⬝ᵥ v) := by
      simp only [dotProduct, Pi.star_apply]
      rw [← Finset.sum_neg_distrib]
      refine (Equiv.sum_comp Fin.revPerm _).symm.trans ?_
      refine Finset.sum_congr rfl fun i _ => ?_
      simp only [Fin.revPerm_apply, hodd, heven, star_neg]
      ring
    have h2 : (2 : ℂ) * (star (fun i => (ccmPublishedCenteredSource a N i : ℂ)) ⬝ᵥ v) = 0 := by
      linear_combination hsum
    exact (mul_eq_zero.mp h2).resolve_left two_ne_zero
  rcases ccmPublished_logDirac_theorem a ha N with
    ⟨ξ, hTξ, hξ, hmet, hkill, -, -, hzeros, hdet⟩ | ⟨c, hTc, hnorm, -, -⟩
  · obtain ⟨t, rfl⟩ := hsimple ξ hTξ
    have hsum : t * ∑ i, v i = 1 := by
      rw [Finset.mul_sum]
      simpa using hξ
    have hv0 : ∑ i, v i ≠ 0 := right_ne_zero_of_mul_eq_one hsum
    have ht : t = (∑ i, v i)⁻¹ := eq_inv_of_mul_eq_one_left hsum
    subst ht
    exact ⟨hv0, hmet, hkill, hzeros, hdet⟩
  · obtain ⟨t, rfl⟩ := hsimple c hTc
    rw [dotProduct_smul, hblind, smul_zero] at hnorm
    exact absurd hnorm zero_ne_one

end RHTower
