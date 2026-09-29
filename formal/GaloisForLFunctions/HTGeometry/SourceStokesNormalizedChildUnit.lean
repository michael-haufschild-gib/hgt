import GaloisForLFunctions.RHTower.CommonRadialSubunitHarmonicCompletion
import GaloisForLFunctions.RHTower.RoutePPrimitiveGammaJuliaStokesWallCubicKernelL2Limit
import GaloisForLFunctions.HTGeometry.SourceStokesIntegralNuclearUnit
import GaloisForLFunctions.HTGeometry.CompactObserverTraceBlindness

/-!
# The prime-mixed normalized Stokes child unit

For `d > 0` the normalized cofinal child `N_d = K_d/J(d)` on `ℓ²(Primes)` has the complete prime
matrix `N_d(p, q) = √(π_d(p) π_d(q)) κ(log p, log q)` and factors as `N_d = V_d* V_d` through the
Burnol synthesis `V_d e_p = √π_d(p) v_{log p}` with `‖V_d‖_HS = 1`.  For a signed grade `t ≠ 0`,

`T(t) = sign(t) N_{|t|}`.

* **(SCIN-A)** `T(t)` is self-adjoint, `sign(t) T(t) ≥ 0`, Schatten-one, `tr T(t) = sign t`,
  `‖T(t)‖₁ = 1`, `T(-t) = -T(t)`; its diagonal is `sign(t) π_{|t|}(p)` and every entry is nonzero.
* **(SCIN-B)** on each chamber `t ↦ T(t)` is trace-norm continuous:
  `‖V_d - V_e‖_HS = ‖ψ_d - ψ_e‖`, and `N_d - N_e = V_d*(V_d - V_e) + (V_d - V_e)* V_e` gives
  `‖N_d - N_e‖₁ ≤ 2 ‖V_d - V_e‖_HS`.
* **(SCIN-C)** as `t → 0`, `T(t) → 0` strongly, because `‖N_d e_p‖ ≤ √π_d(p) → 0` and `‖N_d‖ ≤ 1`;
  hence `tr(T(t) C) → 0` for every compact `C`, while `‖T(t)‖₁ = 1` and `tr T(t) → ±1`.
-/

open Filter Topology Set ContinuousLinearMap InnerProductSpace
open scoped ComplexConjugate InnerProductSpace ENNReal

noncomputable section

namespace GaloisForLFunctions.HTGeometry

open _root_.RHTower

/-! ## The normalized child -/

/-- The normalized child `N_d = K_d/J(d)` for `d > 0`, and zero otherwise. -/
def normalizedStokesUnit (d : ℝ) : PrimeHilbert →L[ℂ] PrimeHilbert :=
  if hd : 0 < d then normalizedStokesPrimeOperator hd else 0

theorem normalizedStokesUnit_of_pos {d : ℝ} (hd : 0 < d) :
    normalizedStokesUnit d = normalizedStokesPrimeOperator hd := by
  rw [normalizedStokesUnit, dif_pos hd]

/-- `N_d = V_d* V_d`. -/
theorem normalizedStokesUnit_eq_adjoint_comp {d : ℝ} (hd : 0 < d) :
    normalizedStokesUnit d
      = adjoint (commonRadialPrimeSynthesis ⟨d, hd⟩) ∘L commonRadialPrimeSynthesis ⟨d, hd⟩ := by
  rw [normalizedStokesUnit_of_pos hd, ← commonRadialPrimeReachability_comp_synthesis ⟨d, hd⟩]
  rfl

theorem isPositive_normalizedStokesUnit {d : ℝ} (hd : 0 < d) :
    (normalizedStokesUnit d).IsPositive := by
  rw [normalizedStokesUnit_of_pos hd]
  exact normalizedStokesPrimeOperator_isPositive' ⟨d, hd⟩

theorem memSchattenClass_one_normalizedStokesUnit (d : ℝ) :
    MemSchattenClass 1 (normalizedStokesUnit d) := by
  by_cases hd : 0 < d
  · rw [normalizedStokesUnit_of_pos hd]
    exact normalizedStokesPrimeOperator_memSchattenClass_one' ⟨d, hd⟩
  · rw [normalizedStokesUnit, dif_neg hd]
    exact memSchattenClass_of_hasRankLE one_pos (hasRankLE_zero 0)

theorem opTrace_normalizedStokesUnit {d : ℝ} (hd : 0 < d) :
    opTrace (normalizedStokesUnit d) = 1 := by
  rw [normalizedStokesUnit_of_pos hd]
  exact opTrace_normalizedStokesPrimeOperator ⟨d, hd⟩

theorem traceNorm_normalizedStokesUnit {d : ℝ} (hd : 0 < d) :
    traceNorm PrimeHilbert (normalizedStokesUnit d) = 1 := by
  rw [traceNorm_eq_re_opTrace_of_isPositive (memSchattenClass_one_normalizedStokesUnit d)
    (isPositive_normalizedStokesUnit hd), opTrace_normalizedStokesUnit hd, Complex.one_re]

theorem normalizedStokesUnit_basis_coord {d : ℝ} (hd : 0 < d) (p q : Nat.Primes) :
    (normalizedStokesUnit d (HilbertSchmidt.lpBasis Nat.Primes q) : Nat.Primes → ℂ) p
      = normalizedStokesPrimeKernel d (p, q) := by
  rw [normalizedStokesUnit_of_pos hd]
  exact normalizedStokesPrimeOperator_apply_basis_coordinate ⟨d, hd⟩ p q

/-- **(SCIN.4).**  `N_d(p, q) = √(π_d(p) π_d(q)) κ(log p, log q)`. -/
theorem normalizedStokesPrimeKernel_eq {d : ℝ} (hd : 0 < d) (p q : Nat.Primes) :
    normalizedStokesPrimeKernel d (p, q)
      = ((Real.sqrt (stokesWeight d p * stokesWeight d q)
          * routePPrimitiveGammaJuliaStokesWallCubicKernel (Real.log (p : ℝ))
            (Real.log (q : ℝ)) : ℝ) : ℂ) := by
  have hJ := gammaSewnMobiusApertureStokesOrientedFirstTraceCurrent_pos hd
  have hwp := routePPrimitiveGammaJuliaStokesTransportedPrimeWeight_pos hd p
  have hwq := routePPrimitiveGammaJuliaStokesTransportedPrimeWeight_pos hd q
  rw [normalizedStokesPrimeKernel,
    routePPrimitiveGammaJuliaStokesCofinalChildKernel_eq_wallCubicKernel hd, stokesWeight,
    stokesWeight, routePPrimitiveGammaJuliaStokesWallNormalizedWeight,
    routePPrimitiveGammaJuliaStokesWallNormalizedWeight, ← Complex.ofReal_div]
  congr 1
  rw [Real.sqrt_mul (div_nonneg hwp.le hJ.le), Real.sqrt_div hwp.le, Real.sqrt_div hwq.le]
  have hs : Real.sqrt (gammaSewnMobiusApertureStokesOrientedFirstTraceCurrent d)
      * Real.sqrt (gammaSewnMobiusApertureStokesOrientedFirstTraceCurrent d)
      = gammaSewnMobiusApertureStokesOrientedFirstTraceCurrent d := Real.mul_self_sqrt hJ.le
  have hs0 : 0 < Real.sqrt (gammaSewnMobiusApertureStokesOrientedFirstTraceCurrent d) :=
    Real.sqrt_pos.mpr hJ
  field_simp
  rw [Real.sq_sqrt hJ.le]

theorem wallCubicKernel_log_pos (p q : Nat.Primes) :
    0 < routePPrimitiveGammaJuliaStokesWallCubicKernel (Real.log (p : ℝ)) (Real.log (q : ℝ)) := by
  have hp : 0 < Real.log (p : ℝ) := Real.log_pos (by exact_mod_cast p.prop.one_lt)
  have hq : 0 < Real.log (q : ℝ) := Real.log_pos (by exact_mod_cast q.prop.one_lt)
  rw [routePPrimitiveGammaJuliaStokesWallCubicKernel]
  have := Real.sqrt_pos.mpr hp
  have := Real.sqrt_pos.mpr hq
  positivity

theorem wallCubicKernel_self {a : ℝ} (ha : 0 < a) :
    routePPrimitiveGammaJuliaStokesWallCubicKernel a a = 1 := by
  rw [routePPrimitiveGammaJuliaStokesWallCubicKernel]
  rw [mul_assoc 8, ← mul_pow, Real.mul_self_sqrt ha.le]
  field_simp
  ring

/-! ## The oriented unit -/

/-- **(SCIN.3).**  `T(t) = sign(t) K_{|t|}/J(|t|)`. -/
def stokesCubicUnit (t : ℝ) : PrimeHilbert →L[ℂ] PrimeHilbert :=
  ((Real.sign t : ℝ) : ℂ) • normalizedStokesUnit |t|

theorem abs_sign_of_ne_zero {t : ℝ} (ht : t ≠ 0) : |Real.sign t| = 1 := by
  rcases lt_or_gt_of_ne ht with h | h
  · rw [Real.sign_of_neg h]; norm_num
  · rw [Real.sign_of_pos h]; norm_num

theorem norm_sign_le_one (t : ℝ) : ‖((Real.sign t : ℝ) : ℂ)‖ ≤ 1 := by
  rw [Complex.norm_real, Real.norm_eq_abs]
  rcases lt_trichotomy t 0 with h | h | h
  · rw [Real.sign_of_neg h]; norm_num
  · rw [h, Real.sign_zero]; norm_num
  · rw [Real.sign_of_pos h]; norm_num

/-- **(SCIN.5).**  `T(-t) = -T(t)`. -/
theorem stokesCubicUnit_neg (t : ℝ) : stokesCubicUnit (-t) = -stokesCubicUnit t := by
  rw [stokesCubicUnit, stokesCubicUnit, abs_neg, Real.sign_neg]
  push_cast
  rw [neg_smul]

/-- **(SCIN.5).**  `T(t)* = T(t)`. -/
theorem isSelfAdjoint_stokesCubicUnit (t : ℝ) : IsSelfAdjoint (stokesCubicUnit t) := by
  rw [isSelfAdjoint_iff', stokesCubicUnit, LinearIsometryEquiv.map_smulₛₗ, Complex.conj_ofReal]
  by_cases h : 0 < |t|
  · rw [(isPositive_normalizedStokesUnit h).isSelfAdjoint.adjoint_eq]
  · rw [normalizedStokesUnit, dif_neg h, map_zero]

/-- **(SCIN.5).**  `sign(t) T(t) ≥ 0`. -/
theorem sign_smul_stokesCubicUnit {t : ℝ} (ht : t ≠ 0) :
    ((Real.sign t : ℝ) : ℂ) • stokesCubicUnit t = normalizedStokesUnit |t| ∧
      (normalizedStokesUnit |t|).IsPositive := by
  refine ⟨?_, isPositive_normalizedStokesUnit (abs_pos.mpr ht)⟩
  rw [stokesCubicUnit, smul_smul, ← Complex.ofReal_mul, sign_sq_of_ne_zero ht, Complex.ofReal_one,
    one_smul]

/-- **(SCIN.5).**  `T(t)` is Schatten-one. -/
theorem memSchattenClass_one_stokesCubicUnit (t : ℝ) : MemSchattenClass 1 (stokesCubicUnit t) :=
  memSchattenClass_one_smul (memSchattenClass_one_normalizedStokesUnit _) _

/-- **(SCIN.5).**  `tr T(t) = sign t`. -/
theorem opTrace_stokesCubicUnit {t : ℝ} (ht : t ≠ 0) :
    opTrace (stokesCubicUnit t) = (Real.sign t : ℝ) := by
  rw [stokesCubicUnit, RHTower.opTrace_smul, opTrace_normalizedStokesUnit (abs_pos.mpr ht), mul_one]

/-- **(SCIN.5).**  `‖T(t)‖₁ = 1`. -/
theorem traceNorm_stokesCubicUnit {t : ℝ} (ht : t ≠ 0) :
    traceNorm PrimeHilbert (stokesCubicUnit t) = 1 := by
  rw [stokesCubicUnit, traceNorm_smul, traceNorm_normalizedStokesUnit (abs_pos.mpr ht),
    Complex.norm_real, Real.norm_eq_abs, abs_sign_of_ne_zero ht, one_mul]

/-- **(SCIN.4)–(SCIN.6).**  The complete prime matrix of `T(t)`. -/
theorem stokesCubicUnit_basis_coord {t : ℝ} (ht : t ≠ 0) (p q : Nat.Primes) :
    (stokesCubicUnit t (HilbertSchmidt.lpBasis Nat.Primes q) : Nat.Primes → ℂ) p
      = ((Real.sign t * (Real.sqrt (stokesWeight |t| p * stokesWeight |t| q)
          * routePPrimitiveGammaJuliaStokesWallCubicKernel (Real.log (p : ℝ))
            (Real.log (q : ℝ))) : ℝ) : ℂ) := by
  rw [stokesCubicUnit, smul_apply, lp.coeFn_smul, Pi.smul_apply,
    normalizedStokesUnit_basis_coord (abs_pos.mpr ht), normalizedStokesPrimeKernel_eq
      (abs_pos.mpr ht), smul_eq_mul, ← Complex.ofReal_mul]

/-- **(SCIN.6).**  The diagonal is the unsquared normalized Stokes current `sign(t) π_{|t|}(p)`. -/
theorem stokesCubicUnit_diag {t : ℝ} (ht : t ≠ 0) (p : Nat.Primes) :
    (stokesCubicUnit t (HilbertSchmidt.lpBasis Nat.Primes p) : Nat.Primes → ℂ) p
      = ((Real.sign t * stokesWeight |t| p : ℝ) : ℂ) := by
  rw [stokesCubicUnit_basis_coord ht, Real.sqrt_mul_self (stokesWeight_pos (abs_pos.mpr ht) p).le,
    wallCubicKernel_self (Real.log_pos (by exact_mod_cast p.prop.one_lt)), mul_one]

/-- **(SCIN.4).**  Every entry, including every distinct-prime entry, is nonzero. -/
theorem stokesCubicUnit_basis_coord_ne_zero {t : ℝ} (ht : t ≠ 0) (p q : Nat.Primes) :
    (stokesCubicUnit t (HilbertSchmidt.lpBasis Nat.Primes q) : Nat.Primes → ℂ) p ≠ 0 := by
  have hd := abs_pos.mpr ht
  rw [stokesCubicUnit_basis_coord ht, Ne, Complex.ofReal_eq_zero]
  refine mul_ne_zero ?_ (mul_pos (Real.sqrt_pos.mpr (mul_pos (stokesWeight_pos hd p)
    (stokesWeight_pos hd q))) (wallCubicKernel_log_pos p q)).ne'
  rcases lt_or_gt_of_ne ht with h | h
  · rw [Real.sign_of_neg h]; norm_num
  · rw [Real.sign_of_pos h]; norm_num

/-! ## Trace-norm continuity on each chamber -/

/-- The Burnol synthesis `V_d` (zero off the physical ray is never used). -/
abbrev burnolPrimeSynthesis {d : ℝ} (hd : 0 < d) :
    PrimeHilbert →L[ℂ] CommonRadialSpace :=
  commonRadialPrimeSynthesis ⟨d, hd⟩

theorem norm_commonRadialPrimeField {d : ℝ} (hd : 0 < d) (p : Nat.Primes) :
    ‖commonRadialPrimeField ⟨d, hd⟩ p‖ = Real.sqrt (stokesWeight d p) := by
  rw [← Real.sqrt_sq (norm_nonneg _), norm_sq_commonRadialPrimeField]
  rfl

theorem norm_commonRadialPrimeField_sub {d e : ℝ} (hd : 0 < d) (he : 0 < e) (p : Nat.Primes) :
    ‖commonRadialPrimeField ⟨d, hd⟩ p - commonRadialPrimeField ⟨e, he⟩ p‖
      = |Real.sqrt (stokesWeight d p) - Real.sqrt (stokesWeight e p)| := by
  rw [← norm_commonRadialPrimeField hd, ← norm_commonRadialPrimeField he, commonRadialPrimeField,
    commonRadialPrimeField, ← sub_smul, norm_smul, norm_smul, norm_smul, ← Complex.ofReal_sub,
    Complex.norm_real, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs,
    Real.norm_eq_abs, abs_of_pos (commonRadialPrimeScale_pos _ p),
    abs_of_pos (commonRadialPrimeScale_pos _ p), ← sub_mul, abs_mul, abs_norm]

theorem isHilbertSchmidt_burnolPrimeSynthesis {d : ℝ} (hd : 0 < d) :
    IsHilbertSchmidt (burnolPrimeSynthesis hd) :=
  commonRadialPrimeSynthesis_isHilbertSchmidt _

theorem hsNorm_burnolPrimeSynthesis {d : ℝ} (hd : 0 < d) :
    ContinuousLinearMap.hsNorm (burnolPrimeSynthesis hd) = 1 := by
  rw [ContinuousLinearMap.hsNorm, hsNormSq_commonRadialPrimeSynthesis, Real.sqrt_one]

/-- **(SCIN.8).**  `‖V_d - V_e‖²_HS = ∑_p (√π_d(p) - √π_e(p))² = ‖ψ_d - ψ_e‖²`. -/
theorem hsNormSq_burnolPrimeSynthesis_sub {d e : ℝ} (hd : 0 < d) (he : 0 < e) :
    hsNormSq (burnolPrimeSynthesis hd - burnolPrimeSynthesis he)
      = ‖stokesRay d - stokesRay e‖ ^ 2 := by
  rw [hsNormSq_eq ((isHilbertSchmidt_burnolPrimeSynthesis hd).sub
    (isHilbertSchmidt_burnolPrimeSynthesis he)) (HilbertSchmidt.lpBasis Nat.Primes),
    norm_stokesRay_sub_sq hd he]
  refine tsum_congr fun p => ?_
  rw [sub_apply, commonRadialPrimeSynthesis_basis,
    commonRadialPrimeSynthesis_basis, norm_commonRadialPrimeField_sub hd he, sq_abs]

theorem sq_sqrt_sub_le_abs_sub {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    (Real.sqrt a - Real.sqrt b) ^ 2 ≤ |a - b| := by
  have h1 : |Real.sqrt a - Real.sqrt b| ≤ Real.sqrt a + Real.sqrt b :=
    abs_sub_le_iff.mpr ⟨by linarith [Real.sqrt_nonneg b], by linarith [Real.sqrt_nonneg a]⟩
  have h2 : a - b = (Real.sqrt a - Real.sqrt b) * (Real.sqrt a + Real.sqrt b) := by
    nlinarith [Real.sq_sqrt ha, Real.sq_sqrt hb]
  rw [h2, abs_mul, abs_of_nonneg (add_nonneg (Real.sqrt_nonneg a) (Real.sqrt_nonneg b)),
    ← sq_abs]
  nlinarith [abs_nonneg (Real.sqrt a - Real.sqrt b)]

/-- **(SCIN.8), Hellinger bound.**  `‖V_d - V_e‖²_HS ≤ ∑_p |π_d(p) - π_e(p)|`. -/
theorem hsNormSq_burnolPrimeSynthesis_sub_le {d e : ℝ} (hd : 0 < d) (he : 0 < e) :
    hsNormSq (burnolPrimeSynthesis hd - burnolPrimeSynthesis he)
      ≤ ∑' p, |stokesWeight d p - stokesWeight e p| := by
  have hs : Summable fun p => |stokesWeight d p - stokesWeight e p| :=
    ((summable_stokesWeight hd).sub (summable_stokesWeight he)).abs
  have hle : ∀ p, (Real.sqrt (stokesWeight d p) - Real.sqrt (stokesWeight e p)) ^ 2
      ≤ |stokesWeight d p - stokesWeight e p| := fun p =>
    sq_sqrt_sub_le_abs_sub (stokesWeight_pos hd p).le (stokesWeight_pos he p).le
  rw [hsNormSq_burnolPrimeSynthesis_sub hd he, norm_stokesRay_sub_sq hd he]
  exact (hs.of_nonneg_of_le (fun p => sq_nonneg _) hle).tsum_le_tsum hle hs

theorem hsNorm_burnolPrimeSynthesis_sub {d e : ℝ} (hd : 0 < d) (he : 0 < e) :
    ContinuousLinearMap.hsNorm (burnolPrimeSynthesis hd - burnolPrimeSynthesis he)
      = ‖stokesRay d - stokesRay e‖ := by
  rw [ContinuousLinearMap.hsNorm, hsNormSq_burnolPrimeSynthesis_sub hd he,
    Real.sqrt_sq (norm_nonneg _)]

/-- **Gram difference.**  For Hilbert–Schmidt `V, W : H → K`,
`‖V*V - W*W‖₁ ≤ (‖V‖_HS + ‖W‖_HS) ‖V - W‖_HS`, from `V*V - W*W = V*(V - W) + (V - W)*W`. -/
theorem traceNorm_adjoint_comp_self_sub_le {H K : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] [NormedAddCommGroup K] [InnerProductSpace ℂ K]
    [CompleteSpace K] {V W : H →L[ℂ] K} (hV : IsHilbertSchmidt V) (hW : IsHilbertSchmidt W) :
    traceNorm H (adjoint V ∘L V - adjoint W ∘L W)
      ≤ (ContinuousLinearMap.hsNorm V + ContinuousLinearMap.hsNorm W)
        * ContinuousLinearMap.hsNorm (V - W) := by
  have hD := hV.sub hW
  have hsplit : adjoint V ∘L V - adjoint W ∘L W = adjoint V ∘L (V - W) + adjoint (V - W) ∘L W := by
    rw [map_sub, ContinuousLinearMap.comp_sub, ContinuousLinearMap.sub_comp]
    abel
  have h1 := RHTower.memSchattenClass_one_comp hV.adjoint hD
  have h2 := RHTower.memSchattenClass_one_comp hD.adjoint hW
  rw [hsplit]
  refine (traceNorm_add_le (h1.isCompactOperator one_pos) (h2.isCompactOperator one_pos)
    (h1.one_summable_approxNumber) (h2.one_summable_approxNumber)).trans ?_
  have hA : traceNorm H (adjoint V ∘L (V - W))
      ≤ ContinuousLinearMap.hsNorm (adjoint V) * ContinuousLinearMap.hsNorm (V - W) :=
    tsum_approxNumber_comp_le hV.adjoint hD
  have hB : traceNorm H (adjoint (V - W) ∘L W)
      ≤ ContinuousLinearMap.hsNorm (adjoint (V - W)) * ContinuousLinearMap.hsNorm W :=
    tsum_approxNumber_comp_le hD.adjoint hW
  rw [ContinuousLinearMap.hsNorm, hV.hsNormSq_adjoint, ← ContinuousLinearMap.hsNorm] at hA
  rw [ContinuousLinearMap.hsNorm, hD.hsNormSq_adjoint, ← ContinuousLinearMap.hsNorm] at hB
  linarith

/-- **(SCIN.9).**  `‖N_d - N_e‖₁ ≤ (‖V_d‖_HS + ‖V_e‖_HS) ‖V_d - V_e‖_HS = 2 ‖ψ_d - ψ_e‖`. -/
theorem traceNorm_normalizedStokesUnit_sub_le {d e : ℝ} (hd : 0 < d) (he : 0 < e) :
    traceNorm PrimeHilbert (normalizedStokesUnit d - normalizedStokesUnit e)
      ≤ 2 * ‖stokesRay d - stokesRay e‖ := by
  have h := traceNorm_adjoint_comp_self_sub_le (isHilbertSchmidt_burnolPrimeSynthesis hd)
    (isHilbertSchmidt_burnolPrimeSynthesis he)
  rw [hsNorm_burnolPrimeSynthesis, hsNorm_burnolPrimeSynthesis,
    hsNorm_burnolPrimeSynthesis_sub hd he] at h
  rw [normalizedStokesUnit_eq_adjoint_comp hd, normalizedStokesUnit_eq_adjoint_comp he]
  linarith

/-- **Theorem SCIN-B.**  On each chamber `t ↦ T(t)` is trace-norm continuous. -/
theorem tendsto_traceNorm_stokesCubicUnit_sub {e : ℝ} (he : e ≠ 0) :
    Tendsto (fun t => traceNorm PrimeHilbert (stokesCubicUnit t - stokesCubicUnit e)) (𝓝 e)
      (𝓝 0) := by
  have hae : 0 < |e| := abs_pos.mpr he
  have hray : Tendsto (fun t => stokesRay |t|) (𝓝 e) (𝓝 (stokesRay |e|)) :=
    (tendsto_stokesRay hae).comp (continuous_abs.tendsto e)
  have hup : Tendsto (fun t => 2 * ‖stokesRay |t| - stokesRay |e|‖) (𝓝 e) (𝓝 0) := by
    have := (tendsto_iff_norm_sub_tendsto_zero.mp hray).const_mul 2
    simpa using this
  have hsign : ∀ᶠ t in 𝓝 e, Real.sign t = Real.sign e ∧ t ≠ 0 := by
    rcases lt_or_gt_of_ne he with h | h
    · filter_upwards [gt_mem_nhds h] with t ht
      exact ⟨by rw [Real.sign_of_neg ht, Real.sign_of_neg h], ht.ne⟩
    · filter_upwards [lt_mem_nhds h] with t ht
      exact ⟨by rw [Real.sign_of_pos ht, Real.sign_of_pos h], ht.ne'⟩
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hup
    (Eventually.of_forall fun _ => traceNorm_nonneg _) ?_
  filter_upwards [hsign] with t ht
  have heq : stokesCubicUnit t - stokesCubicUnit e
      = ((Real.sign e : ℝ) : ℂ) • (normalizedStokesUnit |t| - normalizedStokesUnit |e|) := by
    rw [stokesCubicUnit, stokesCubicUnit, ht.1, smul_sub]
  rw [heq, traceNorm_smul, Complex.norm_real, Real.norm_eq_abs, abs_sign_of_ne_zero he, one_mul]
  exact traceNorm_normalizedStokesUnit_sub_le (abs_pos.mpr ht.2) hae

/-! ## Fixed-chart disappearance -/

theorem norm_normalizedStokesUnit_le_one (d : ℝ) : ‖normalizedStokesUnit d‖ ≤ 1 := by
  by_cases hd : 0 < d
  · rw [normalizedStokesUnit_of_pos hd]
    exact norm_normalizedStokesPrimeOperator_le_one hd
  · rw [normalizedStokesUnit, dif_neg hd, norm_zero]
    norm_num

theorem norm_normalizedStokesUnit_basis_le {d : ℝ} (hd : 0 < d) (p : Nat.Primes) :
    ‖normalizedStokesUnit d (HilbertSchmidt.lpBasis Nat.Primes p)‖
      ≤ Real.sqrt (stokesWeight d p) := by
  rw [normalizedStokesUnit_eq_adjoint_comp hd, comp_apply, commonRadialPrimeSynthesis_basis,
    ← norm_commonRadialPrimeField hd]
  refine (le_opNorm _ _).trans ?_
  have h1 : ‖adjoint (burnolPrimeSynthesis hd)‖ ≤ 1 := by
    rw [LinearIsometryEquiv.norm_map]
    refine (opNorm_le_hsNorm (isHilbertSchmidt_burnolPrimeSynthesis hd)).trans ?_
    rw [hsNorm_burnolPrimeSynthesis]
  calc ‖adjoint (commonRadialPrimeSynthesis ⟨d, hd⟩)‖ * ‖commonRadialPrimeField ⟨d, hd⟩ p‖
      ≤ 1 * ‖commonRadialPrimeField ⟨d, hd⟩ p‖ := mul_le_mul_of_nonneg_right h1 (norm_nonneg _)
    _ = _ := one_mul _

theorem lpBasis_eq_lpBasisVec (p : Nat.Primes) :
    (HilbertSchmidt.lpBasis Nat.Primes p : PrimeHilbert) = lpBasisVec p := by
  ext q
  rw [HilbertSchmidt.lpBasis_apply, lpBasisVec]

/-- **(SCIN.10).**  `T(t) → 0` strongly as `t → 0`. -/
theorem tendsto_stokesCubicUnit_apply (x : PrimeHilbert) :
    Tendsto (fun t => stokesCubicUnit t x) (𝓝[≠] 0) (𝓝 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero, Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨F, hF⟩ := (eventually_norm_sub_coordTruncation_lt x (show 0 < ε / 2 by positivity)).exists
  have hfin : Tendsto (fun t : ℝ => ∑ p ∈ F, ‖(x : Nat.Primes → ℂ) p‖
      * Real.sqrt (stokesWeight |t| p)) (𝓝[≠] 0) (𝓝 0) := by
    have h : Tendsto (fun t : ℝ => ∑ p ∈ F, ‖(x : Nat.Primes → ℂ) p‖
        * Real.sqrt (stokesWeight |t| p)) (𝓝[≠] 0)
        (𝓝 (∑ p ∈ F, ‖(x : Nat.Primes → ℂ) p‖ * Real.sqrt 0)) := by
      refine tendsto_finsetSum _ fun p _ => (tendsto_const_nhds).mul ?_
      exact (Real.continuous_sqrt.tendsto 0).comp
        ((tendsto_stokesWeight_zero p).comp tendsto_abs_nhdsNE_zero)
    simpa using h
  filter_upwards [Metric.tendsto_nhds.mp hfin (ε / 2) (by positivity), self_mem_nhdsWithin]
    with t ht htne
  rw [dist_zero_right, Real.norm_eq_abs, abs_of_nonneg (Finset.sum_nonneg fun p _ =>
    mul_nonneg (norm_nonneg _) (Real.sqrt_nonneg _))] at ht
  rw [dist_zero_right, Real.norm_eq_abs, abs_norm]
  have hd : 0 < |t| := abs_pos.mpr htne
  set N := normalizedStokesUnit |t|
  have hsplit : x = (x - coordTruncation F x) + coordTruncation F x := by abel
  have hPF : N (coordTruncation F x) = ∑ p ∈ F, (x : Nat.Primes → ℂ) p • N (lpBasisVec p) := by
    rw [coordTruncation_apply, map_sum]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [lpBasisVec, ← map_smul, ← lp.single_smul, smul_eq_mul, mul_one]
  have hN1 : ‖N (x - coordTruncation F x)‖ ≤ ‖x - coordTruncation F x‖ :=
    (le_opNorm _ _).trans (by
      have := norm_normalizedStokesUnit_le_one |t|
      nlinarith [norm_nonneg (x - coordTruncation F x)])
  have hN2 : ‖N (coordTruncation F x)‖
      ≤ ∑ p ∈ F, ‖(x : Nat.Primes → ℂ) p‖ * Real.sqrt (stokesWeight |t| p) := by
    rw [hPF]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun p _ => ?_)
    rw [norm_smul, ← lpBasis_eq_lpBasisVec]
    exact mul_le_mul_of_nonneg_left (norm_normalizedStokesUnit_basis_le hd p) (norm_nonneg _)
  calc ‖stokesCubicUnit t x‖ ≤ ‖N x‖ := by
        rw [stokesCubicUnit, smul_apply, norm_smul]
        exact (mul_le_of_le_one_left (norm_nonneg _) (norm_sign_le_one t))
    _ = ‖N (x - coordTruncation F x) + N (coordTruncation F x)‖ := by
        rw [← map_add, ← hsplit]
    _ ≤ ‖N (x - coordTruncation F x)‖ + ‖N (coordTruncation F x)‖ := norm_add_le _ _
    _ < ε / 2 + ε / 2 := add_lt_add_of_le_of_lt (hN1.trans hF.le) (hN2.trans_lt ht)
    _ = ε := by ring

theorem traceNorm_stokesCubicUnit_le_one (t : ℝ) :
    traceNorm PrimeHilbert (stokesCubicUnit t) ≤ 1 := by
  rcases eq_or_ne t 0 with rfl | ht
  · rw [stokesCubicUnit, Real.sign_zero, Complex.ofReal_zero, zero_smul, traceNorm_zero]
    norm_num
  · rw [traceNorm_stokesCubicUnit ht]

/-- **(SCIN.11).**  Every compact fixed-chart observer is blind to the unit. -/
theorem tendsto_opTrace_stokesCubicUnit_comp {C : PrimeHilbert →L[ℂ] PrimeHilbert}
    (hC : IsCompactOperator C) :
    Tendsto (fun t => opTrace (stokesCubicUnit t ∘L C)) (𝓝[≠] 0) (𝓝 0) :=
  tendsto_opTrace_comp_of_isCompactOperator stokesCubicUnit memSchattenClass_one_stokesCubicUnit
    traceNorm_stokesCubicUnit_le_one tendsto_stokesCubicUnit_apply hC

/-- **Theorem SCIN-C.**  The trace norm stays one and the one-sided traces are `±1`. -/
theorem stokesCubicUnit_wall :
    (∀ t, t ≠ 0 → traceNorm PrimeHilbert (stokesCubicUnit t) = 1) ∧
      Tendsto (fun t => opTrace (stokesCubicUnit t)) (𝓝[>] 0) (𝓝 1) ∧
      Tendsto (fun t => opTrace (stokesCubicUnit t)) (𝓝[<] 0) (𝓝 (-1)) := by
  refine ⟨fun t ht => traceNorm_stokesCubicUnit ht, ?_, ?_⟩
  · refine tendsto_const_nhds.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with t ht
    rw [opTrace_stokesCubicUnit (ne_of_gt ht), Real.sign_of_pos ht, Complex.ofReal_one]
  · refine tendsto_const_nhds.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with t ht
    rw [opTrace_stokesCubicUnit (ne_of_lt ht), Real.sign_of_neg ht]
    push_cast
    ring

end GaloisForLFunctions.HTGeometry
