import GaloisForLFunctions.FamilyContinuationTheory.TheQuadraticSymbolsOfTheEisensteinIntegersAreReciprocal

/-!
# The Poisson coefficient splits over coprime moduli

The Poisson coefficient of a periodic function on `O = ℤ[ω]` is its finite Fourier transform
against the trace character `ψ_M(x) = exp(2πi Tr(x/(Mλ)))`. For coprime moduli `M₁, M₂` and a
function `m ↦ F₁(m mod M₁) F₂(m mod M₂)`,

`Σ_{m mod M₁M₂} F₁(m) F₂(m) ψ_{M₁M₂}(hm) = Σ_{x mod M₁} F₁(M₂x) ψ_{M₁}(hx) · Σ_{y mod M₂} F₂(M₁y) ψ_{M₂}(hy)`

(`sum_crt_mul_traceChar`), along the parametrization `m = M₂x + M₁y`: the phase splits exactly,
`ψ_{M₁M₂}(M₂ z) = ψ_{M₁}(z)` (`principalTraceChar_mul_left`), and the cofactor enters only the
argument of each local function. For a multiplicative local function the cofactor becomes a
character value: these are the pair phases of the Poisson coefficients of the cubic-theta probe.
-/

noncomputable section

open scoped BigOperators Classical

namespace GaloisForLFunctions.FamilyContinuationTheory

open MetaplecticMobiusDescent.Eisenstein

/-- `ψ_{cd}(dz) = ψ_c(z)`. -/
theorem principalTraceChar_mul_left (c d : O) [NeZero c] [NeZero d] (z : O) :
    principalTraceChar (c * d) (mul_ne_zero (NeZero.ne c) (NeZero.ne d))
        (Ideal.Quotient.mk _ (d * z)) =
      principalTraceChar c (NeZero.ne c) (Ideal.Quotient.mk _ z) := by
  rw [principalTraceChar_apply, principalTraceChar_apply]
  congr 4
  have hinj := FaithfulSMul.algebraMap_injective O K
  have hc : algebraMap O K c ≠ 0 := fun h => NeZero.ne c (hinj (by rw [h, map_zero]))
  have hd : algebraMap O K d ≠ 0 := fun h => NeZero.ne d (hinj (by rw [h, map_zero]))
  have hl : algebraMap O K traceLambda ≠ 0 := fun h => traceLambda_ne_zero
    (hinj (by rw [h, map_zero]))
  simp only [map_mul]
  field_simp

/-- `ψ_{cd}(cz) = ψ_d(z)`. -/
theorem principalTraceChar_mul_right (c d : O) [NeZero c] [NeZero d] (z : O) :
    principalTraceChar (c * d) (mul_ne_zero (NeZero.ne c) (NeZero.ne d))
        (Ideal.Quotient.mk _ (c * z)) =
      principalTraceChar d (NeZero.ne d) (Ideal.Quotient.mk _ z) := by
  rw [principalTraceChar_apply, principalTraceChar_apply]
  congr 4
  have hinj := FaithfulSMul.algebraMap_injective O K
  have hc : algebraMap O K c ≠ 0 := fun h => NeZero.ne c (hinj (by rw [h, map_zero]))
  have hd : algebraMap O K d ≠ 0 := fun h => NeZero.ne d (hinj (by rw [h, map_zero]))
  have hl : algebraMap O K traceLambda ≠ 0 := fun h => traceLambda_ne_zero
    (hinj (by rw [h, map_zero]))
  simp only [map_mul]
  field_simp

/-- Reduction `O/(cd) → O/(c)`. -/
def reduceLeft (c d : O) : O ⧸ Ideal.span {c * d} →+* O ⧸ Ideal.span {c} :=
  Ideal.Quotient.factor (Ideal.span_singleton_le_span_singleton.mpr (dvd_mul_right c d))

/-- Reduction `O/(cd) → O/(d)`. -/
def reduceRight (c d : O) : O ⧸ Ideal.span {c * d} →+* O ⧸ Ideal.span {d} :=
  Ideal.Quotient.factor (Ideal.span_singleton_le_span_singleton.mpr (dvd_mul_left d c))

/-- **The CRT splitting of a Poisson coefficient.** For coprime `c, d`,
`Σ_{m mod cd} F₁(m) F₂(m) ψ_{cd}(hm) = Σ_{x mod c} F₁(dx) ψ_c(hx) · Σ_{y mod d} F₂(cy) ψ_d(hy)`. -/
theorem sum_crt_mul_traceChar (c d : O) [NeZero c] [NeZero d] (hcd : IsCoprime c d)
    (F₁ : O ⧸ Ideal.span {c} → ℂ) (F₂ : O ⧸ Ideal.span {d} → ℂ) (h : O) :
    ∑ m : O ⧸ Ideal.span {c * d}, F₁ (reduceLeft c d m) * F₂ (reduceRight c d m) *
        principalTraceChar (c * d) (mul_ne_zero (NeZero.ne c) (NeZero.ne d))
          (Ideal.Quotient.mk _ h * m) =
      (∑ x : O ⧸ Ideal.span {c}, F₁ (Ideal.Quotient.mk _ d * x) *
          principalTraceChar c (NeZero.ne c) (Ideal.Quotient.mk _ h * x)) *
        ∑ y : O ⧸ Ideal.span {d}, F₂ (Ideal.Quotient.mk _ c * y) *
          principalTraceChar d (NeZero.ne d) (Ideal.Quotient.mk _ h * y) := by
  haveI : NeZero (c * d) := ⟨mul_ne_zero (NeZero.ne c) (NeZero.ne d)⟩
  rw [← (Fintype.sum_bijective _ (crtParam_bijective c d hcd) (fun p =>
      F₁ (reduceLeft c d (crtParam c d p)) * F₂ (reduceRight c d (crtParam c d p)) *
        principalTraceChar (c * d) _ (Ideal.Quotient.mk _ h * crtParam c d p)) _ fun _ => rfl),
    Fintype.sum_prod_type, Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
  have hl : reduceLeft c d (crtParam c d (x, y)) = Ideal.Quotient.mk _ d * x := by
    simp only [crtParam, reduceLeft, Ideal.Quotient.factor_mk, map_add, map_mul, mk_qrep]
    rw [Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self c), zero_mul, add_zero]
  have hr : reduceRight c d (crtParam c d (x, y)) = Ideal.Quotient.mk _ c * y := by
    simp only [crtParam, reduceRight, Ideal.Quotient.factor_mk, map_add, map_mul, mk_qrep]
    rw [Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self d), zero_mul, zero_add]
  have hphase : principalTraceChar (c * d) (mul_ne_zero (NeZero.ne c) (NeZero.ne d))
      (Ideal.Quotient.mk _ h * crtParam c d (x, y)) =
      principalTraceChar c (NeZero.ne c) (Ideal.Quotient.mk _ h * x) *
        principalTraceChar d (NeZero.ne d) (Ideal.Quotient.mk _ h * y) := by
    have ex : Ideal.Quotient.mk (Ideal.span {c}) (h * qrep x) = Ideal.Quotient.mk _ h * x := by
      rw [map_mul, mk_qrep]
    have ey : Ideal.Quotient.mk (Ideal.span {d}) (h * qrep y) = Ideal.Quotient.mk _ h * y := by
      rw [map_mul, mk_qrep]
    rw [crtParam, ← map_mul, mul_add, map_add, AddChar.map_add_eq_mul,
      show h * (d * qrep (x, y).1) = d * (h * qrep x) by ring,
      show h * (c * qrep (x, y).2) = c * (h * qrep y) by ring,
      principalTraceChar_mul_left, principalTraceChar_mul_right, ex, ey]
  rw [hl, hr, hphase]
  ring

end GaloisForLFunctions.FamilyContinuationTheory
