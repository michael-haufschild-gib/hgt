import GaloisForLFunctions.RHTower.CCM.CCMCompressedShiftIndependence
import Mathlib.Analysis.InnerProductSpace.Adjoint
import GaloisForLFunctions.RHTower.VonMangoldtLogSummatory

/-!
# The critical prime-shift form is an exact logarithmic position commutator

At a finite aperture the compressed weighted shift `T_{A,h}` is an eigenvector of the commutator
with logarithmic position:

`[X_A, T_{A,h}] = h · T_{A,h}`,

so the orbital length `h = log n` is *produced* by the commutator rather than inserted as an
external normalisation.  Taking adjoints reverses the eigenvalue, so the skew combination
`Z = ∑ c_n (T_n - T_n^*)` has

`[X, Z] = ∑ c_n h_n (T_n + T_n^*)`:

the Hermitian prime contribution, with the unsquared coefficients `Λ(p^k)/(p^k log p^k) = 1/(k p^k)`.

The same file records the exact unitary transport to the unweighted logarithmic carrier and the
exact projection-compressed commutator identity, whose two cross terms are the polarized leakage
Gram of the compression.
-/

noncomputable section

namespace GaloisForLFunctions.RHTower

open Set ArithmeticFunction ContinuousLinearMap

/-! ### The bounded aperture position operator -/

/-- Multiplication by the logarithmic position. -/
def positionMult : (ℝ → ℂ) →ₗ[ℂ] (ℝ → ℂ) where
  toFun f := fun x => (x : ℂ) * f x
  map_add' f g := by funext x; simp [mul_add]
  map_smul' c f := by
    funext x
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    ring

@[simp] theorem positionMult_apply (f : ℝ → ℂ) (x : ℝ) :
    positionMult f x = (x : ℂ) * f x := rfl

/-- **The exact compressed-shift commutator.**  `[X_A, T_{A,h}] = h · T_{A,h}`: the orbital length
is produced by the commutator with logarithmic position. -/
theorem positionMult_compressedShift_commutator (A h : ℝ) :
    positionMult.comp (compressedShift A h) - (compressedShift A h).comp positionMult
      = (h : ℂ) • compressedShift A h := by
  refine LinearMap.ext fun f => ?_
  funext x
  show (x : ℂ) * (compressedShift A h f x) - compressedShift A h (positionMult f) x
      = (h : ℂ) * compressedShift A h f x
  simp only [compressedShift_apply, positionMult_apply]
  by_cases hx : x ∈ Icc (0 : ℝ) A
  · by_cases hxh : x - h ∈ Icc (0 : ℝ) A
    · simp only [if_pos hx, if_pos hxh]
      push_cast
      ring
    · simp only [if_pos hx, if_neg hxh]
      ring
  · simp only [if_neg hx]
    ring

/-! ### The exact unitary transport to the unweighted logarithmic carrier -/

/-- The half-weight transport `W_A f = e^{-x/2} f`. -/
def halfWeightTransport : (ℝ → ℂ) →ₗ[ℂ] (ℝ → ℂ) where
  toFun f := fun x => (Real.exp (-x / 2) : ℂ) * f x
  map_add' f g := by funext x; simp [mul_add]
  map_smul' c f := by
    funext x
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    ring

/-- The inverse half-weight transport. -/
def halfWeightTransportInv : (ℝ → ℂ) →ₗ[ℂ] (ℝ → ℂ) where
  toFun f := fun x => (Real.exp (x / 2) : ℂ) * f x
  map_add' f g := by funext x; simp [mul_add]
  map_smul' c f := by
    funext x
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    ring

/-- The ordinary truncated translation on the aperture. -/
def truncatedTranslation (A h : ℝ) : (ℝ → ℂ) →ₗ[ℂ] (ℝ → ℂ) where
  toFun f := fun x =>
    if x ∈ Icc (0 : ℝ) A then (if x - h ∈ Icc (0 : ℝ) A then f (x - h) else 0) else 0
  map_add' f g := by
    funext x
    simp only [Pi.add_apply]
    split_ifs <;> ring
  map_smul' c f := by
    funext x
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    split_ifs <;> ring

theorem halfWeightTransport_inv (f : ℝ → ℂ) :
    halfWeightTransport (halfWeightTransportInv f) = f := by
  funext x
  show (Real.exp (-x / 2) : ℂ) * ((Real.exp (x / 2) : ℂ) * f x) = f x
  have h : (Real.exp (-x / 2) : ℂ) * (Real.exp (x / 2) : ℂ) = 1 := by
    rw [← Complex.ofReal_mul, ← Real.exp_add, show (-x / 2 + x / 2 : ℝ) = 0 by ring,
      Real.exp_zero, Complex.ofReal_one]
  rw [← mul_assoc, h, one_mul]

/-- **The exact unitary transport.**  Conjugating the weighted compressed shift by the half-weight
transport gives `e^{h/2}` times the ordinary truncated translation. -/
theorem halfWeightTransport_compressedShift (A h : ℝ) :
    halfWeightTransport.comp ((compressedShift A h).comp halfWeightTransportInv)
      = (Real.exp (h / 2) : ℂ) • truncatedTranslation A h := by
  refine LinearMap.ext fun f => ?_
  funext x
  show (Real.exp (-x / 2) : ℂ) *
      (if x ∈ Icc (0 : ℝ) A then
        (Real.exp h : ℂ) * (if x - h ∈ Icc (0 : ℝ) A then
          (Real.exp ((x - h) / 2) : ℂ) * f (x - h) else 0) else 0)
    = (Real.exp (h / 2) : ℂ) *
      (if x ∈ Icc (0 : ℝ) A then (if x - h ∈ Icc (0 : ℝ) A then f (x - h) else 0) else 0)
  by_cases hx : x ∈ Icc (0 : ℝ) A
  · by_cases hxh : x - h ∈ Icc (0 : ℝ) A
    · simp only [if_pos hx, if_pos hxh]
      rw [← mul_assoc, ← mul_assoc, ← Complex.ofReal_mul, ← Complex.ofReal_mul,
        ← Real.exp_add, ← Real.exp_add]
      congr 2
      ring
    · simp only [if_pos hx, if_neg hxh]
      ring
  · simp only [if_neg hx]
    ring

/-- The transport fixes the position operator. -/
theorem halfWeightTransport_positionMult :
    halfWeightTransport.comp (positionMult.comp halfWeightTransportInv) = positionMult := by
  refine LinearMap.ext fun f => ?_
  funext x
  show (Real.exp (-x / 2) : ℂ) * ((x : ℂ) * ((Real.exp (x / 2) : ℂ) * f x)) = (x : ℂ) * f x
  have h : (Real.exp (-x / 2) : ℂ) * (Real.exp (x / 2) : ℂ) = 1 := by
    rw [← Complex.ofReal_mul, ← Real.exp_add, show (-x / 2 + x / 2 : ℝ) = 0 by ring,
      Real.exp_zero, Complex.ofReal_one]
  calc (Real.exp (-x / 2) : ℂ) * ((x : ℂ) * ((Real.exp (x / 2) : ℂ) * f x))
      = ((Real.exp (-x / 2) : ℂ) * (Real.exp (x / 2) : ℂ)) * ((x : ℂ) * f x) := by ring
    _ = (x : ℂ) * f x := by rw [h, one_mul]

/-! ### The unsquared prime-power coefficients -/

/-- **The divided von Mangoldt coefficient.**  `Λ(p^k)/(p^k log p^k) = 1/(k p^k)`: the coefficient
of the finite-aperture Euler logarithm is the unsquared Euler coefficient. -/
theorem vonMangoldt_div_mul_log_prime_pow {p k : ℕ} (hp : p.Prime) (hk : 0 < k) :
    (Λ (p ^ k)) / (((p : ℝ) ^ k) * Real.log ((p : ℝ) ^ k))
      = 1 / ((k : ℝ) * (p : ℝ) ^ k) := by
  have hlogp : 0 < Real.log p := Real.log_pos (by exact_mod_cast hp.one_lt)
  have hp0 : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp.pos
  have hLam : Λ (p ^ k) = Real.log p := by
    rw [ArithmeticFunction.vonMangoldt_apply_pow hk.ne', ArithmeticFunction.vonMangoldt_apply_prime hp]
  have hlogpow : Real.log ((p : ℝ) ^ k) = (k : ℝ) * Real.log (p : ℝ) := by
    rw [Real.log_pow]
  rw [hLam, hlogpow]
  have hpk : (0 : ℝ) < (p : ℝ) ^ k := by positivity
  have hkne : ((k : ℝ)) ≠ 0 := Nat.cast_ne_zero.mpr hk.ne'
  field_simp

/-! ### The adjoint commutator law and the skew Euler logarithm -/

section Adjoint

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem adjoint_mul' (A B : H →L[ℂ] H) : adjoint (A * B) = adjoint B * adjoint A :=
  ContinuousLinearMap.adjoint_comp A B

/-- **The adjoint reverses the commutator eigenvalue.**  If `[X, T] = h T` with `X` self-adjoint and
`h` real, then `[X, T^*] = -h T^*`. -/
theorem adjoint_commutator_of_commutator {X T : H →L[ℂ] H} (hX : adjoint X = X) {h : ℝ}
    (hcomm : X * T - T * X = ((h : ℝ) : ℂ) • T) :
    X * adjoint T - adjoint T * X = (-((h : ℝ) : ℂ)) • adjoint T := by
  have hadj := congrArg adjoint hcomm
  rw [map_sub, adjoint_mul', adjoint_mul', hX, map_smulₛₗ, Complex.conj_ofReal] at hadj
  have : X * adjoint T - adjoint T * X = -(adjoint T * X - X * adjoint T) := by noncomm_ring
  rw [this, hadj, neg_smul]

/-- The skew Euler logarithm of a family of commutator eigenvectors. -/
def skewSum {ι : Type*} (s : Finset ι) (c : ι → ℝ) (T : ι → (H →L[ℂ] H)) : H →L[ℂ] H :=
  ∑ i ∈ s, ((c i : ℝ) : ℂ) • (T i - adjoint (T i))

/-- The skew Euler logarithm is skew-adjoint. -/
theorem adjoint_skewSum {ι : Type*} (s : Finset ι) (c : ι → ℝ) (T : ι → (H →L[ℂ] H)) :
    adjoint (skewSum s c T) = -skewSum s c T := by
  rw [skewSum, map_sum, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_smulₛₗ, Complex.conj_ofReal, map_sub, adjoint_adjoint, ← smul_neg]
  congr 1
  abel

/-- **The commutator of position with the skew Euler logarithm.**  It is the Hermitian
prime contribution, with the coefficients multiplied by the orbital lengths. -/
theorem commutator_skewSum {ι : Type*} (s : Finset ι) (c hh : ι → ℝ) (T : ι → (H →L[ℂ] H))
    {X : H →L[ℂ] H} (hX : adjoint X = X)
    (hcomm : ∀ i ∈ s, X * T i - T i * X = ((hh i : ℝ) : ℂ) • T i) :
    X * skewSum s c T - skewSum s c T * X
      = ∑ i ∈ s, ((c i * hh i : ℝ) : ℂ) • (T i + adjoint (T i)) := by
  rw [skewSum, Finset.mul_sum, Finset.sum_mul, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i hi => ?_
  have h1 := hcomm i hi
  have h2 := adjoint_commutator_of_commutator hX h1
  have hexpand : X * (((c i : ℝ) : ℂ) • (T i - adjoint (T i)))
        - (((c i : ℝ) : ℂ) • (T i - adjoint (T i))) * X
      = ((c i : ℝ) : ℂ) • ((X * T i - T i * X) - (X * adjoint (T i) - adjoint (T i) * X)) := by
    rw [mul_smul_comm, smul_mul_assoc, ← smul_sub]
    congr 1
    noncomm_ring
  rw [hexpand, h1, h2, neg_smul, sub_neg_eq_add, ← smul_add, smul_smul]
  congr 1
  push_cast
  ring

/-! ### The projection-compressed commutator identity -/

/-- **The exact projection-compressed commutator/Gram identity.**  Compressing the commutator of a
self-adjoint operator with a skew-adjoint one by an orthogonal projection produces the internal
commutator plus the polarized cross-boundary leakage Gram. -/
theorem projection_commutator_decomposition {X Z Q : H →L[ℂ] H}
    (hX : adjoint X = X) (hZ : adjoint Z = -Z) (hQ : adjoint Q = Q) (hQ2 : Q * Q = Q) :
    Q * (X * Z - Z * X) * Q
      = ((Q * X * Q) * (Q * Z * Q) - (Q * Z * Q) * (Q * X * Q))
        + adjoint ((1 - Q) * X * Q) * ((1 - Q) * Z * Q)
        + adjoint ((1 - Q) * Z * Q) * ((1 - Q) * X * Q) := by
  have hone : adjoint (1 - Q : H →L[ℂ] H) = 1 - Q := by
    rw [map_sub, hQ]
    congr 1
    exact ContinuousLinearMap.adjoint_id
  have hLX : adjoint ((1 - Q) * X * Q) = Q * X * (1 - Q) := by
    rw [adjoint_mul', adjoint_mul', hQ, hX, hone]
    noncomm_ring
  have hLZ : adjoint ((1 - Q) * Z * Q) = -(Q * Z * (1 - Q)) := by
    rw [adjoint_mul', adjoint_mul', hQ, hZ, hone]
    noncomm_ring
  have hQ1 : (1 - Q) * (1 - Q) = 1 - Q := by
    have h : (1 - Q) * (1 - Q) = 1 - Q - Q + Q * Q := by noncomm_ring
    rw [h, hQ2]
    noncomm_ring
  rw [hLX, hLZ]
  have e1 : (Q * X * Q) * (Q * Z * Q) = Q * X * (Q * Q) * Z * Q := by noncomm_ring
  have e2 : (Q * Z * Q) * (Q * X * Q) = Q * Z * (Q * Q) * X * Q := by noncomm_ring
  have e3 : (Q * X * (1 - Q)) * ((1 - Q) * Z * Q) = Q * X * ((1 - Q) * (1 - Q)) * Z * Q := by
    noncomm_ring
  have e4 : (-(Q * Z * (1 - Q))) * ((1 - Q) * X * Q)
      = -(Q * Z * ((1 - Q) * (1 - Q)) * X * Q) := by noncomm_ring
  rw [e1, e2, e3, e4, hQ2, hQ1]
  noncomm_ring

/-- **The renormalized trace-defect decomposition.**  Every source-compatible renormalized
functional has exactly two degree-one channels: the internal trace anomaly and the polarized
leakage cross. -/
theorem trace_projection_commutator_decomposition {X Z Q : H →L[ℂ] H}
    (τ : (H →L[ℂ] H) →ₗ[ℂ] ℂ)
    (hX : adjoint X = X) (hZ : adjoint Z = -Z) (hQ : adjoint Q = Q) (hQ2 : Q * Q = Q) :
    τ (Q * (X * Z - Z * X) * Q)
      = τ ((Q * X * Q) * (Q * Z * Q) - (Q * Z * Q) * (Q * X * Q))
        + τ (adjoint ((1 - Q) * X * Q) * ((1 - Q) * Z * Q)
            + adjoint ((1 - Q) * Z * Q) * ((1 - Q) * X * Q)) := by
  rw [projection_commutator_decomposition hX hZ hQ hQ2, map_add, map_add, map_add]
  ring

end Adjoint

end GaloisForLFunctions.RHTower
