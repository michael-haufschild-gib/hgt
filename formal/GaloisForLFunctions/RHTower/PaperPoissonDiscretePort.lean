import GaloisForLFunctions.RHTower.PaperPoissonContinuumPort
import GaloisForLFunctions.HTGeometry.LpDiagonalMultiplier
import GaloisForLFunctions.HTGeometry.HilbertSchmidtMatrix
import GaloisForLFunctions.HTGeometry.DiagonalCompactOperator
import GaloisForLFunctions.HTGeometry.CompactOperatorBoundedBelow

/-!
# The full integer-frequency sampling changes the paper ideal cost

Sampling the native Poisson multiplier at all integers yields a compact operator at every
positive gap, while the actual continuum multiplier never becomes compact. Both operators
have norm one. Positive and negative frequency modes and the zero mode are all retained.
-/

namespace RHTower
noncomputable section
open GaloisForLFunctions GaloisForLFunctions.HTGeometry Filter Classical
open scoped Topology ENNReal NNReal

abbrev PaperPoissonDiscreteSpace := lp (fun _ : ℤ => ℂ) 2

/-- The native symbol sampled on the entire integer-frequency lattice. -/
def paperPoissonDiscretePort (h d : ℝ≥0) :
    PaperPoissonDiscreteSpace →L[ℂ] PaperPoissonDiscreteSpace :=
  _root_.GaloisForLFunctions.lpDiagonalCLM (fun n : ℤ => (paperPoissonSymbol h d n : ℂ)) zero_le_one
    (fun n => norm_paperPoissonSymbol_complex_le h d n)

@[simp] theorem paperPoissonDiscretePort_apply (h d : ℝ≥0)
    (f : PaperPoissonDiscreteSpace) (n : ℤ) :
    paperPoissonDiscretePort h d f n = (paperPoissonSymbol h d n : ℂ) * f n := rfl

theorem paperPoissonDiscretePort_basis (h d : ℝ≥0) (n : ℤ) :
    paperPoissonDiscretePort h d (HilbertSchmidt.lpBasis ℤ n) =
      (paperPoissonSymbol h d n : ℂ) • HilbertSchmidt.lpBasis ℤ n := by
  rw [HilbertSchmidt.lpBasis_apply]
  change _root_.GaloisForLFunctions.lpDiagonalCLM _ _ _ (lp.single 2 n (1 : ℂ)) = _
  rw [_root_.GaloisForLFunctions.lpDiagonalCLM_single]
  ext j
  simp only [lp.single_apply, Pi.single_apply, lp.coeFn_smul, Pi.smul_apply, smul_eq_mul]
  split_ifs with hj
  · subst hj
    simp
  · simp

theorem tendsto_paperPoissonSymbol_int (h d : ℝ≥0) :
    Tendsto (fun n : ℤ => (paperPoissonSymbol h d n : ℂ)) cofinite
      (𝓝 (Complex.ofReal (if d = 0 then 1 else 0))) := by
  have hz : Tendsto (fun n : ℤ => |n|) cofinite atTop := by
    rw [Int.cofinite_eq]
    exact tendsto_sup.mpr ⟨tendsto_abs_atBot_atTop, tendsto_abs_atTop_atTop⟩
  have hr : Tendsto (fun n : ℤ => |(n : ℝ)|) cofinite atTop := by
    refine (tendsto_intCast_atTop_atTop.comp hz).congr fun n => ?_
    simp
  have hlim := Complex.continuous_ofReal.continuousAt.tendsto.comp
    ((tendsto_paperPoissonSymbol_atTop h d).comp hr)
  simpa only [Function.comp_def, paperPoissonSymbol_abs] using hlim

@[simp] theorem paperPoissonDiscretePort_zero_gap (h : ℝ≥0) :
    paperPoissonDiscretePort h 0 = 1 := by
  apply ContinuousLinearMap.ext
  intro f
  change paperPoissonDiscretePort h 0 f = f
  ext n
  simp only [paperPoissonDiscretePort_apply, paperPoissonSymbol_zero_gap,
    Complex.ofReal_one, one_mul]

/-- Every positive gap is compact in this full discrete completion. -/
theorem paperPoissonDiscretePort_compact_iff (h d : ℝ≥0) :
    IsCompactOperator (paperPoissonDiscretePort h d) ↔ d ≠ 0 := by
  constructor
  · intro hc hd
    subst d
    rw [paperPoissonDiscretePort_zero_gap] at hc
    haveI : Finite ℤ := finite_of_orthonormal_eigenvectors_of_le_norm hc
      (HilbertSchmidt.lpBasis ℤ).orthonormal
      (lam := fun _ => (1 : ℂ)) (fun n => by simp)
      (ε := 1) zero_lt_one (fun n => by simp)
    exact not_finite ℤ
  · intro hd
    apply isCompactOperator_of_diag_tendsto_cofinite (HilbertSchmidt.lpBasis ℤ)
      (paperPoissonDiscretePort_basis h d)
    simpa only [if_neg hd, Complex.ofReal_zero, norm_zero] using
      (tendsto_paperPoissonSymbol_int h d).norm

/-- The undamped zero-frequency vector keeps the discrete operator norm equal to one. -/
theorem norm_paperPoissonDiscretePort (h d : ℝ≥0) : ‖paperPoissonDiscretePort h d‖ = 1 := by
  apply le_antisymm
  · exact _root_.GaloisForLFunctions.norm_lpDiagonalCLM_le _ _ _
  · have he : paperPoissonDiscretePort h d (lp.single 2 (0 : ℤ) (1 : ℂ)) =
        lp.single 2 (0 : ℤ) (1 : ℂ) := by
      change _root_.GaloisForLFunctions.lpDiagonalCLM _ _ _ _ = _
      rw [_root_.GaloisForLFunctions.lpDiagonalCLM_single]
      simp only [Int.cast_zero, paperPoissonSymbol_zero_frequency, Complex.ofReal_one]
    have hn := (paperPoissonDiscretePort h d).le_opNorm (lp.single 2 (0 : ℤ) (1 : ℂ))
    rwa [he, lp.norm_single (by norm_num), norm_one, mul_one] at hn

/-- The paper ideal cost jumps when the continuum is replaced by integer frequencies. -/
theorem paperPoissonDiscretePort_traceCost (h d : ℝ≥0) :
    compactOperatorTraceCost PaperPoissonDiscreteSpace (paperPoissonDiscretePort h d) =
      if d = 0 then ∞ else 0 := by
  rw [compactOperatorTraceCost_eq, paperPoissonDiscretePort_compact_iff]
  by_cases hd : d = 0 <;> simp [hd]

/-- Exact source-depth composition also holds on the entire sampled frequency lattice. -/
theorem paperPoissonDiscretePort_compose (h d e : ℝ≥0) :
    paperPoissonDiscretePort h d * paperPoissonDiscretePort (h + d) e =
      paperPoissonDiscretePort h (d + e) := by
  apply ContinuousLinearMap.ext
  intro f
  change paperPoissonDiscretePort h d (paperPoissonDiscretePort (h + d) e f) = _
  ext n
  simp only [paperPoissonDiscretePort_apply]
  rw [← mul_assoc, ← Complex.ofReal_mul, paperPoissonSymbol_compose]

/-- At the actual horizon-to-Xi gap, the two completions have opposite paper costs. -/
theorem paperPoisson_horizon_completion_costs :
    compactOperatorTraceCost PaperPoissonSpace (paperPoissonPort 0 (1 / 2)) = ∞ ∧
      compactOperatorTraceCost PaperPoissonDiscreteSpace
        (paperPoissonDiscretePort 0 (1 / 2)) = 0 ∧
      ‖paperPoissonPort 0 (1 / 2)‖ = 1 ∧ ‖paperPoissonDiscretePort 0 (1 / 2)‖ = 1 := by
  exact ⟨paperPoissonPort_traceCost _ _, by rw [paperPoissonDiscretePort_traceCost]; norm_num,
    norm_paperPoissonPort _ _, norm_paperPoissonDiscretePort _ _⟩

end
end RHTower
