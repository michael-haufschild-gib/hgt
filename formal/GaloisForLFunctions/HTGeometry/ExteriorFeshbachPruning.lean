import GaloisForLFunctions.HTGeometry.ExteriorFeshbachBlocks

/-!
# The exterior self-energy of a Feshbach pruning

Compressing a resolvent to an aperture deletes every word that leaves the aperture and returns.
Exact elimination of the exterior restores those words as a self-energy `Σ` correcting the pruned
interior operator, and — on a C*-algebra with a self-adjoint generator — that correction is a
positive operator.

The estimates below quantify the correction: with the spectral shift `α` chosen beyond `‖T‖` the
exterior block is invertible by a Neumann series, and the self-energy is bounded by
`‖T‖² / (α − ‖T‖)`.
-/

namespace GaloisForLFunctions.HTGeometry

section Neumann

variable {A : Type*} [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A] [NormOneClass A]

omit [NormedAlgebra ℝ A] in
/-- **Neumann bound.**  A contractive perturbation of the identity has an inverse whose norm is
controlled by the geometric series. -/
theorem norm_inverse_oneSub_le {t : A} (h : ‖t‖ < 1) :
    ‖(↑(Units.oneSub t h)⁻¹ : A)‖ ≤ (1 - ‖t‖)⁻¹ := by
  have hval : (↑(Units.oneSub t h)⁻¹ : A) = ∑' n : ℕ, t ^ n := rfl
  have hg : Summable (fun n : ℕ => ‖t‖ ^ n) := summable_geometric_of_lt_one (norm_nonneg t) h
  have hsum : Summable (fun n : ℕ => ‖t ^ n‖) :=
    hg.of_nonneg_of_le (fun n => norm_nonneg _) (fun n => norm_pow_le t n)
  rw [hval]
  refine le_trans (norm_tsum_le_tsum_norm hsum) ?_
  refine le_trans (hsum.tsum_le_tsum (fun n => norm_pow_le t n) hg) ?_
  rw [tsum_geometric_of_lt_one (norm_nonneg t) h]

variable {a : A} {α : ℝ}

omit [NormedAlgebra ℝ A] [CompleteSpace A] [NormOneClass A] in
private theorem shift_pos (h : ‖a‖ < α) : 0 < α := lt_of_le_of_lt (norm_nonneg a) h

omit [CompleteSpace A] [NormOneClass A] in
private theorem shift_lt_one (h : ‖a‖ < α) : ‖-(α⁻¹ • a)‖ < 1 := by
  have hα := shift_pos h
  rw [norm_neg, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hα)]
  rw [inv_mul_lt_one₀ hα]
  exact h

/-- The inverse of the spectrally shifted element `α • 1 + a`, built from the geometric series. -/
noncomputable def shiftInverse (h : ‖a‖ < α) : A :=
  α⁻¹ • (↑(Units.oneSub (-(α⁻¹ • a)) (shift_lt_one h))⁻¹ : A)

omit [CompleteSpace A] [NormOneClass A] in
private theorem shift_factor (h : ‖a‖ < α) :
    α • (1 : A) + a = α • (1 - -(α⁻¹ • a)) := by
  have hα := (shift_pos h).ne'
  rw [smul_sub, smul_neg, sub_neg_eq_add, smul_smul, mul_inv_cancel₀ hα, one_smul]

omit [NormOneClass A] in
/-- **The shift is invertible from the right.** -/
theorem shiftInverse_mul_right (h : ‖a‖ < α) :
    (α • (1 : A) + a) * shiftInverse h = 1 := by
  have hα := (shift_pos h).ne'
  rw [shift_factor h, shiftInverse, smul_mul_assoc, mul_smul_comm, smul_smul,
    mul_inv_cancel₀ hα, one_smul]
  exact (Units.oneSub (-(α⁻¹ • a)) (shift_lt_one h)).mul_inv

omit [NormOneClass A] in
/-- **The shift is invertible from the left.** -/
theorem shiftInverse_mul_left (h : ‖a‖ < α) :
    shiftInverse h * (α • (1 : A) + a) = 1 := by
  have hα := (shift_pos h).ne'
  rw [shift_factor h, shiftInverse, smul_mul_assoc, mul_smul_comm, smul_smul,
    inv_mul_cancel₀ hα, one_smul]
  exact (Units.oneSub (-(α⁻¹ • a)) (shift_lt_one h)).inv_mul

/-- **The resolvent bound.**  Shifting past the norm of `a` bounds the inverse by the reciprocal of
the gap. -/
theorem norm_shiftInverse_le (h : ‖a‖ < α) : ‖shiftInverse h‖ ≤ (α - ‖a‖)⁻¹ := by
  have hα := shift_pos h
  have hbase := norm_inverse_oneSub_le (shift_lt_one h)
  rw [norm_neg, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hα)] at hbase
  have hkey : (1 - α⁻¹ * ‖a‖)⁻¹ = α * (α - ‖a‖)⁻¹ := by
    have h1 : 1 - α⁻¹ * ‖a‖ = α⁻¹ * (α - ‖a‖) := by field_simp
    rw [h1, mul_inv, inv_inv]
  rw [shiftInverse, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hα)]
  calc α⁻¹ * ‖(↑(Units.oneSub (-(α⁻¹ • a)) (shift_lt_one h))⁻¹ : A)‖
      ≤ α⁻¹ * (1 - α⁻¹ * ‖a‖)⁻¹ :=
        mul_le_mul_of_nonneg_left hbase (le_of_lt (inv_pos.mpr hα))
    _ = (α - ‖a‖)⁻¹ := by rw [hkey, ← mul_assoc, inv_mul_cancel₀ hα.ne', one_mul]

end Neumann

section Feshbach

variable {A : Type*} [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A] [NormOneClass A]
variable {P Q T c f : A} {α : ℝ}

omit [CompleteSpace A] [NormOneClass A] in
/-- A real scalar multiple of the identity is central. -/
theorem smul_one_central (α : ℝ) (x : A) : (α • (1 : A)) * x = x * (α • (1 : A)) := by
  rw [smul_mul_assoc, one_mul, mul_smul_comm, mul_one]

/-- The exterior block `D_α = α I_Q + Q T Q`, lifted to the ambient algebra so that its inverse can
be produced by a Neumann series.  The lift commutes with `Q`, so on the exterior subspace it agrees
with the compressed operator. -/
noncomputable def exteriorBlock (α : ℝ) (Q T : A) : A := α • (1 : A) + Q * T * Q

omit [NormedAlgebra ℝ A] [CompleteSpace A] [NormOneClass A] in
/-- A two-sided compression by contractions does not increase the norm. -/
theorem norm_compress_le (hP : ‖P‖ ≤ 1) (hQ : ‖Q‖ ≤ 1) (T : A) : ‖P * T * Q‖ ≤ ‖T‖ := by
  calc ‖P * T * Q‖ ≤ ‖P * T‖ * ‖Q‖ := norm_mul_le _ _
    _ ≤ (‖P‖ * ‖T‖) * ‖Q‖ := by
        exact mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _)
    _ ≤ (1 * ‖T‖) * 1 := by
        refine mul_le_mul (mul_le_mul_of_nonneg_right hP (norm_nonneg _)) hQ (norm_nonneg _) ?_
        positivity
    _ = ‖T‖ := by ring

omit [NormedAlgebra ℝ A] [CompleteSpace A] [NormOneClass A] in
/-- The exterior compression stays strictly inside the spectral shift. -/
theorem norm_exteriorPart_lt (hQ : ‖Q‖ ≤ 1) (hT : ‖T‖ < α) : ‖Q * T * Q‖ < α :=
  lt_of_le_of_lt (norm_compress_le hQ hQ T) hT

/-- The inverse of the exterior block. -/
noncomputable def exteriorInverse (hQ : ‖Q‖ ≤ 1) (hT : ‖T‖ < α) : A :=
  shiftInverse (norm_exteriorPart_lt hQ hT)

omit [NormOneClass A] in
theorem exteriorBlock_mul_inverse (hQ : ‖Q‖ ≤ 1) (hT : ‖T‖ < α) :
    exteriorBlock α Q T * exteriorInverse hQ hT = 1 :=
  shiftInverse_mul_right (norm_exteriorPart_lt hQ hT)

omit [NormOneClass A] in
theorem inverse_mul_exteriorBlock (hQ : ‖Q‖ ≤ 1) (hT : ‖T‖ < α) :
    exteriorInverse hQ hT * exteriorBlock α Q T = 1 :=
  shiftInverse_mul_left (norm_exteriorPart_lt hQ hT)

/-- **The exterior resolvent bound `(6a)`:** `‖D_α⁻¹‖ ≤ 1/(α − ‖T‖)`. -/
theorem norm_exteriorInverse_le (hQ : ‖Q‖ ≤ 1) (hT : ‖T‖ < α) :
    ‖exteriorInverse hQ hT‖ ≤ (α - ‖T‖)⁻¹ := by
  refine le_trans (norm_shiftInverse_le (norm_exteriorPart_lt hQ hT)) ?_
  have h1 : 0 < α - ‖T‖ := by linarith
  have h2 : α - ‖T‖ ≤ α - ‖Q * T * Q‖ := by
    have := norm_compress_le hQ hQ T; linarith
  exact inv_anti₀ h1 h2

/-- The Feshbach self-energy `Σ_α = P T Q D_α⁻¹ Q T P`. -/
noncomputable def selfEnergy (P : A) (hQ : ‖Q‖ ≤ 1) (hT : ‖T‖ < α) : A :=
  P * T * Q * exteriorInverse hQ hT * (Q * T * P)

/-- **The self-energy bound `(6b)`:** `‖Σ_α‖ ≤ ‖T‖²/(α − ‖T‖)`. -/
theorem norm_selfEnergy_le (hP : ‖P‖ ≤ 1) (hQ : ‖Q‖ ≤ 1) (hT : ‖T‖ < α) :
    ‖selfEnergy P hQ hT‖ ≤ ‖T‖ ^ 2 * (α - ‖T‖)⁻¹ := by
  have h1 : 0 < α - ‖T‖ := by linarith
  have hPTQ : ‖P * T * Q‖ ≤ ‖T‖ := norm_compress_le hP hQ T
  have hQTP : ‖Q * T * P‖ ≤ ‖T‖ := norm_compress_le hQ hP T
  have hD : ‖exteriorInverse hQ hT‖ ≤ (α - ‖T‖)⁻¹ := norm_exteriorInverse_le hQ hT
  calc ‖selfEnergy P hQ hT‖
      ≤ ‖P * T * Q * exteriorInverse hQ hT‖ * ‖Q * T * P‖ := norm_mul_le _ _
    _ ≤ (‖P * T * Q‖ * ‖exteriorInverse hQ hT‖) * ‖Q * T * P‖ :=
        mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _)
    _ ≤ (‖T‖ * (α - ‖T‖)⁻¹) * ‖T‖ := by gcongr
    _ = ‖T‖ ^ 2 * (α - ‖T‖)⁻¹ := by ring

/-- **The renormalized source bound `(7)`:** `‖P T Q D_α⁻¹ f‖ ≤ ‖T‖/(α − ‖T‖) ‖f‖`. -/
theorem norm_source_le (hP : ‖P‖ ≤ 1) (hQ : ‖Q‖ ≤ 1) (hT : ‖T‖ < α) (f : A) :
    ‖P * T * Q * exteriorInverse hQ hT * f‖ ≤ ‖T‖ * (α - ‖T‖)⁻¹ * ‖f‖ := by
  have h1 : 0 < α - ‖T‖ := by linarith
  have hPTQ : ‖P * T * Q‖ ≤ ‖T‖ := norm_compress_le hP hQ T
  have hD : ‖exteriorInverse hQ hT‖ ≤ (α - ‖T‖)⁻¹ := norm_exteriorInverse_le hQ hT
  calc ‖P * T * Q * exteriorInverse hQ hT * f‖
      ≤ ‖P * T * Q * exteriorInverse hQ hT‖ * ‖f‖ := norm_mul_le _ _
    _ ≤ (‖P * T * Q‖ * ‖exteriorInverse hQ hT‖) * ‖f‖ :=
        mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _)
    _ ≤ (‖T‖ * (α - ‖T‖)⁻¹) * ‖f‖ := by gcongr

omit [NormOneClass A] in
/-- **The exterior solve `(5)`:** the exterior component is recovered from the source and the
interior component by inverting the exterior block. -/
theorem exterior_solve (hPQ : P + Q = 1) (hQ2 : Q * Q = Q) (hQ : ‖Q‖ ≤ 1) (hT : ‖T‖ < α)
    (heq : α • c + T * c = f) :
    Q * c = exteriorInverse hQ hT * (Q * f - Q * T * P * c) := by
  have heq' : (α • (1 : A)) * c + T * c = f := by rw [smul_mul_assoc, one_mul]; exact heq
  have hb := feshbach_exterior hPQ hQ2 (α • (1 : A)) (smul_one_central α) heq'
  have hB : exteriorBlock α Q T * (Q * c) = Q * f - Q * T * P * c := by
    rw [exteriorBlock, add_mul, smul_mul_assoc, one_mul]
    rw [smul_mul_assoc, one_mul] at hb
    exact hb
  rw [← hB, ← mul_assoc, inverse_mul_exteriorBlock, one_mul]

omit [NormedAlgebra ℝ A] [CompleteSpace A] [NormOneClass A] in
/-- An element commuting with an invertible element commutes with its inverse. -/
theorem comm_of_comm_inverse {d e x : A} (hde : d * e = 1) (hed : e * d = 1) (h : d * x = x * d) :
    e * x = x * e := by
  calc e * x = e * x * (d * e) := by rw [hde, mul_one]
    _ = e * (x * d) * e := by noncomm_ring
    _ = e * (d * x) * e := by rw [h]
    _ = e * d * x * e := by noncomm_ring
    _ = x * e := by rw [hed, one_mul]

omit [CompleteSpace A] [NormOneClass A] in
/-- The lifted exterior block commutes with the exterior projection. -/
theorem exteriorBlock_comm (hQ2 : Q * Q = Q) :
    exteriorBlock α Q T * Q = Q * exteriorBlock α Q T := by
  rw [exteriorBlock, add_mul, mul_add, smul_mul_assoc, one_mul, mul_smul_comm, mul_one]
  congr 1
  calc Q * T * Q * Q = Q * T * (Q * Q) := by rw [mul_assoc]
    _ = Q * T * Q := by rw [hQ2]
    _ = Q * Q * T * Q := by rw [hQ2]
    _ = Q * (Q * T * Q) := by noncomm_ring

omit [NormOneClass A] in
/-- The exterior resolvent commutes with the exterior projection, so the ambient lift restricts to
the true inverse on the exterior subspace. -/
theorem exteriorInverse_comm (hQ2 : Q * Q = Q) (hQ : ‖Q‖ ≤ 1) (hT : ‖T‖ < α) :
    exteriorInverse hQ hT * Q = Q * exteriorInverse hQ hT :=
  comm_of_comm_inverse (exteriorBlock_mul_inverse hQ hT) (inverse_mul_exteriorBlock hQ hT)
    (exteriorBlock_comm hQ2)

omit [NormOneClass A] in
/-- **The pruned interior equation `(4)`:** eliminating the exterior exactly replaces the compressed
operator `α P + P T P` by `α P + P T P − Σ_α`, with a renormalized two-port source. -/
theorem interior_equation (hPQ : P + Q = 1) (hP2 : P * P = P) (hQ2 : Q * Q = Q)
    (hQ : ‖Q‖ ≤ 1) (hT : ‖T‖ < α) (hQf : Q * f = f) (heq : α • c + T * c = f) :
    (α • P + P * T * P - selfEnergy P hQ hT) * (P * c)
      = -(P * T * Q * exteriorInverse hQ hT * f) := by
  set D := exteriorInverse hQ hT with hDdef
  -- the aperture source has no interior component
  have hPeq : P = 1 - Q := eq_sub_of_add_eq hPQ
  have hPf : P * f = 0 := by rw [hPeq, sub_mul, one_mul, hQf, sub_self]
  -- the interior block equation
  have heq' : (α • (1 : A)) * c + T * c = f := by rw [smul_mul_assoc, one_mul]; exact heq
  have hi := feshbach_interior hPQ hP2 (α • (1 : A)) (smul_one_central α) heq'
  rw [smul_mul_assoc, one_mul, hPf] at hi
  -- substitute the exterior solve into the interior coupling
  have hsolve : Q * c = D * (f - Q * T * P * c) := by
    rw [hDdef, exterior_solve hPQ hQ2 hQ hT heq, hQf]
  have hcouple : P * T * Q * c = P * T * Q * D * f - selfEnergy P hQ hT * c := by
    have hstep : P * T * Q * c = P * T * Q * (Q * c) := by
      calc P * T * Q * c = P * T * (Q * Q) * c := by rw [hQ2]
        _ = P * T * Q * (Q * c) := by noncomm_ring
    rw [hstep, hsolve, selfEnergy, ← hDdef]
    noncomm_ring
  -- the self-energy already carries the interior projection
  have hself : selfEnergy P hQ hT * (P * c) = selfEnergy P hQ hT * c := by
    rw [selfEnergy]
    calc P * T * Q * D * (Q * T * P) * (P * c)
        = P * T * Q * D * (Q * T) * (P * P) * c := by noncomm_ring
      _ = P * T * Q * D * (Q * T) * P * c := by rw [hP2]
      _ = P * T * Q * D * (Q * T * P) * c := by noncomm_ring
  -- assemble
  have hlhs : (α • P + P * T * P - selfEnergy P hQ hT) * (P * c)
      = α • (P * c) + P * T * P * (P * c) - selfEnergy P hQ hT * c := by
    have hPP : P * (P * c) = P * c := by rw [← mul_assoc, hP2]
    rw [sub_mul, add_mul, smul_mul_assoc, hself, hPP]
  rw [hcouple] at hi
  rw [hlhs]
  linear_combination (norm := noncomm_ring) hi

end Feshbach

section Positivity

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
variable {P Q T : A} {α : ℝ}

omit [PartialOrder A] [StarOrderedRing A] in
/-- The lifted exterior block is self-adjoint when the generator and the projection are. -/
theorem isSelfAdjoint_exteriorBlock (hQ : IsSelfAdjoint Q) (hT : IsSelfAdjoint T) :
    IsSelfAdjoint (exteriorBlock α Q T) := by
  rw [IsSelfAdjoint, exteriorBlock, star_add, star_smul, star_one, star_trivial,
    star_mul, star_mul, hQ.star_eq, hT.star_eq]
  congr 1
  noncomm_ring

omit [PartialOrder A] [StarOrderedRing A] in
/-- The inverse of a self-adjoint invertible element is self-adjoint. -/
theorem isSelfAdjoint_inverse {d e : A} (hde : d * e = 1)
    (hd : IsSelfAdjoint d) : IsSelfAdjoint e := by
  have h1 : star e * d = 1 := by
    have h := congrArg star hde
    rwa [star_mul, hd.star_eq, star_one] at h
  show star e = e
  calc star e = star e * (d * e) := by rw [hde, mul_one]
    _ = star e * d * e := by rw [mul_assoc]
    _ = e := by rw [h1, one_mul]

omit [PartialOrder A] [StarOrderedRing A] in
theorem isSelfAdjoint_exteriorInverse (hQs : IsSelfAdjoint Q) (hTs : IsSelfAdjoint T)
    (hQ : ‖Q‖ ≤ 1) (hT : ‖T‖ < α) : IsSelfAdjoint (exteriorInverse hQ hT) :=
  isSelfAdjoint_inverse (exteriorBlock_mul_inverse hQ hT) (isSelfAdjoint_exteriorBlock hQs hTs)

/-- Shifting a self-adjoint element past its norm makes it positive. -/
theorem nonneg_exteriorBlock (hQs : IsSelfAdjoint Q) (hTs : IsSelfAdjoint T)
    (hQ : ‖Q‖ ≤ 1) (hT : ‖T‖ < α) : 0 ≤ exteriorBlock α Q T := by
  have hs : IsSelfAdjoint (Q * T * Q) := by
    rw [IsSelfAdjoint, star_mul, star_mul, hQs.star_eq, hTs.star_eq]
    noncomm_ring
  have hn : ‖Q * T * Q‖ < α := norm_exteriorPart_lt hQ hT
  have h1 := hs.neg_algebraMap_norm_le_self
  have h2 : (0 : A) ≤ algebraMap ℝ A (α - ‖Q * T * Q‖) := algebraMap_nonneg A (by linarith)
  rw [map_sub] at h2
  have hscal : α • (1 : A) = algebraMap ℝ A α := (Algebra.algebraMap_eq_smul_one α).symm
  rw [exteriorBlock, hscal]
  calc (0 : A) ≤ algebraMap ℝ A α - algebraMap ℝ A ‖Q * T * Q‖ := h2
    _ ≤ algebraMap ℝ A α + Q * T * Q := by
        rw [sub_eq_add_neg]
        exact add_le_add le_rfl h1

/-- The exterior resolvent is a positive operator. -/
theorem nonneg_exteriorInverse (hQs : IsSelfAdjoint Q) (hTs : IsSelfAdjoint T)
    (hQ : ‖Q‖ ≤ 1) (hT : ‖T‖ < α) : 0 ≤ exteriorInverse hQ hT := by
  have hsa := isSelfAdjoint_exteriorInverse hQs hTs hQ hT
  have hpos := nonneg_exteriorBlock (α := α) hQs hTs hQ hT
  have hrepr : exteriorInverse hQ hT
      = star (exteriorInverse hQ hT) * exteriorBlock α Q T * exteriorInverse hQ hT := by
    rw [hsa.star_eq, mul_assoc, ← mul_assoc]
    rw [inverse_mul_exteriorBlock, one_mul]
  rw [hrepr]
  exact star_left_conjugate_nonneg hpos _

omit [PartialOrder A] [StarOrderedRing A] in
/-- The self-energy is the conjugate of the exterior resolvent by the exterior-to-interior
coupling. -/
theorem selfEnergy_eq_conjugate (hPs : IsSelfAdjoint P) (hQs : IsSelfAdjoint Q)
    (hTs : IsSelfAdjoint T) (hQ : ‖Q‖ ≤ 1) (hT : ‖T‖ < α) :
    selfEnergy P hQ hT = star (Q * T * P) * exteriorInverse hQ hT * (Q * T * P) := by
  rw [selfEnergy, star_mul, star_mul, hPs.star_eq, hQs.star_eq, hTs.star_eq]
  noncomm_ring

theorem nonneg_selfEnergy (hPs : IsSelfAdjoint P) (hQs : IsSelfAdjoint Q)
    (hTs : IsSelfAdjoint T) (hQ : ‖Q‖ ≤ 1) (hT : ‖T‖ < α) : 0 ≤ selfEnergy P hQ hT := by
  rw [selfEnergy_eq_conjugate hPs hQs hTs hQ hT]
  exact star_left_conjugate_nonneg (nonneg_exteriorInverse hQs hTs hQ hT) _

theorem isSelfAdjoint_selfEnergy (hPs : IsSelfAdjoint P) (hQs : IsSelfAdjoint Q)
    (hTs : IsSelfAdjoint T) (hQ : ‖Q‖ ≤ 1) (hT : ‖T‖ < α) :
    IsSelfAdjoint (selfEnergy P hQ hT) :=
  IsSelfAdjoint.of_nonneg (nonneg_selfEnergy hPs hQs hTs hQ hT)

end Positivity

end GaloisForLFunctions.HTGeometry
