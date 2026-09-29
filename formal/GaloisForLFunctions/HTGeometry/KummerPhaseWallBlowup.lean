import GaloisForLFunctions.HTGeometry.KummerPhaseWallOverlap
import GaloisForLFunctions.HTGeometry.BoundedDiagonalOperatorLp

/-!
# Parabolic wall blowup of the Kummer phase

At aperture `d > 0` the wall coordinate is `x_d(p) = 2d log p`, so the prime Kummer phase
`D_y e_p = p^{iy} e_p` is multiplication by `e^{iτ x_d(p)}` in the wall chart when `y = 2dτ`.
The comoving chart `U_d = (f ↦ f ∘ Q_d) J_d` therefore intertwines `D_{2dτ}` with multiplication by
`e^{iτ Q_d(u)}` on `L²(0, 1)`:

`U_d D_{2dτ} N_d D_{2dτ}* U_d* = M_{d,τ} A_d M_{d,τ}*`.

As `d → 0⁺` these phase-conjugated children converge in trace norm to the quantile transport of the
phase orbit `A_τ = M_τ A M_τ*`: writing `A_d = S_d* S_d`, the syntheses `S_d M_{d,τ}*` converge in
Hilbert–Schmidt norm, because `S_d → S_0` in Hilbert–Schmidt norm and `M_{d,τ} → M_{0,τ}` strongly
(dominated convergence, `Q_d → Q_0` pointwise), and strong convergence of uniformly bounded
factors against a Hilbert–Schmidt operator is Hilbert–Schmidt convergence.
-/

open MeasureTheory Filter Topology Set ProbabilityTheory ContinuousLinearMap
open scoped ENNReal NNReal ComplexConjugate InnerProductSpace

noncomputable section

namespace GaloisForLFunctions.HTGeometry

open _root_.RHTower

local instance isProbabilityMeasure_expMeasure_one_blowup : IsProbabilityMeasure (expMeasure 1) :=
  isProbabilityMeasure_expMeasure one_pos

/-! ## Strong convergence against a Hilbert–Schmidt operator -/

/-- If `B_a → 0` strongly with `‖B_a‖ ≤ C`, then `‖B_a T‖_HS → 0` for every Hilbert–Schmidt `T`. -/
theorem tendsto_hsNormSq_comp_of_tendsto_apply {E F : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] [CompleteSpace E] [NormedAddCommGroup F] [InnerProductSpace ℂ F]
    [CompleteSpace F] {T : E →L[ℂ] F} (hT : IsHilbertSchmidt T) {α : Type*} {l : Filter α}
    {B : α → F →L[ℂ] F} {C : ℝ} (hC : ∀ a, ‖B a‖ ≤ C)
    (hB : ∀ x, Tendsto (fun a => B a x) l (𝓝 0)) :
    Tendsto (fun a => ContinuousLinearMap.hsNormSq (B a ∘L T)) l (𝓝 0) := by
  have h := tendsto_tsum_of_dominated_convergence (𝓕 := l)
    (f := fun a i => ‖B a (T (hsBasis ℂ E i))‖ ^ 2) (g := fun _ => 0)
    (bound := fun i => C ^ 2 * ‖T (hsBasis ℂ E i)‖ ^ 2) ((hT.summable _).mul_left _)
    (fun i => by
      have := ((hB (T (hsBasis ℂ E i))).norm).pow 2
      simpa using this)
    (Eventually.of_forall fun a i => by
      rw [Real.norm_of_nonneg (sq_nonneg _), ← mul_pow]
      exact pow_le_pow_left₀ (norm_nonneg _)
        ((le_opNorm _ _).trans (mul_le_mul_of_nonneg_right (hC a) (norm_nonneg _))) 2)
  simpa [ContinuousLinearMap.hsNormSq] using h

/-! ## Phase multipliers on the real line and in the quantile chart -/

/-- The phase `x ↦ e^{iτx}` relative to a law `μ`. -/
def lawPhase (μ : Measure ℝ) (τ : ℝ) : GaloisForLFunctions.RHTower.UnitModulusL2Phase ℝ μ where
  toFun x := Complex.exp (((τ * x : ℝ) : ℂ) * Complex.I)
  aestronglyMeasurable := (by fun_prop : Continuous fun x : ℝ =>
    Complex.exp (((τ * x : ℝ) : ℂ) * Complex.I)).aestronglyMeasurable
  norm_eq_one := Eventually.of_forall fun x => Complex.norm_exp_ofReal_mul_I _

/-- Multiplication by `e^{iτx}` on `L²(μ)`. -/
def lawPhaseMul (μ : Measure ℝ) (τ : ℝ) : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ :=
  ((lawPhase μ τ).mulUnitary : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ)

theorem phaseMultiplier_eq_lawPhaseMul (τ : ℝ) : phaseMultiplier τ = lawPhaseMul (expMeasure 1) τ :=
  rfl

/-- The quantile phase `u ↦ e^{iτ Q_μ(u)}` on the unit interval. -/
def quantilePhase (μ : Measure ℝ) [IsProbabilityMeasure μ] (τ : ℝ) :
    GaloisForLFunctions.RHTower.UnitModulusL2Phase ℝ (volume.restrict (Ioo (0 : ℝ) 1)) where
  toFun u := Complex.exp (((τ * quantile μ u : ℝ) : ℂ) * Complex.I)
  aestronglyMeasurable := ((by fun_prop : Continuous fun x : ℝ =>
    Complex.exp (((τ * x : ℝ) : ℂ) * Complex.I)).measurable.comp
      (measurable_quantile μ)).aestronglyMeasurable
  norm_eq_one := Eventually.of_forall fun u => Complex.norm_exp_ofReal_mul_I _

/-- Multiplication by `e^{iτ Q_μ(u)}` on `L²(0, 1)`. -/
def quantilePhaseMul (μ : Measure ℝ) [IsProbabilityMeasure μ] (τ : ℝ) :
    Lp ℂ 2 (volume.restrict (Ioo (0 : ℝ) 1)) →L[ℂ] Lp ℂ 2 (volume.restrict (Ioo (0 : ℝ) 1)) :=
  ((quantilePhase μ τ).mulUnitary :
    Lp ℂ 2 (volume.restrict (Ioo (0 : ℝ) 1)) →L[ℂ] Lp ℂ 2 (volume.restrict (Ioo (0 : ℝ) 1)))

theorem norm_quantilePhaseMul_le (μ : Measure ℝ) [IsProbabilityMeasure μ] (τ : ℝ) :
    ‖quantilePhaseMul μ τ‖ ≤ 1 :=
  opNorm_le_bound _ zero_le_one fun f => by
    rw [one_mul, quantilePhaseMul]
    exact le_of_eq ((quantilePhase μ τ).mulUnitary.norm_map f)

/-- **Quantile transport of the phase.**  `U M_τ = M_{μ,τ} U` for `U f = f ∘ Q_μ`. -/
theorem compL2_comp_lawPhaseMul (μ : Measure ℝ) [IsProbabilityMeasure μ] (τ : ℝ) :
    compL2 (measurePreserving_quantile μ) ∘L lawPhaseMul μ τ
      = quantilePhaseMul μ τ ∘L compL2 (measurePreserving_quantile μ) := by
  set hQ := measurePreserving_quantile μ
  ext1 f
  refine Lp.ext ?_
  have h1 := compL2_coeFn hQ (lawPhaseMul μ τ f)
  have h2 : ((lawPhaseMul μ τ f : ℝ → ℂ) ∘ quantile μ) =ᵐ[volume.restrict (Ioo (0 : ℝ) 1)]
      (fun x => Complex.exp (((τ * x : ℝ) : ℂ) * Complex.I) * f x) ∘ quantile μ :=
    ((lawPhase μ τ).mulUnitary_ae f).comp_tendsto hQ.quasiMeasurePreserving.tendsto_ae
  have h3 := (quantilePhase μ τ).mulUnitary_ae (compL2 hQ f)
  have h4 := compL2_coeFn hQ f
  filter_upwards [h1, h2, h3, h4] with u h1 h2 h3 h4
  rw [ContinuousLinearMap.comp_apply, h1, h2, ContinuousLinearMap.comp_apply]
  change _ = ((quantilePhase μ τ).mulUnitary (compL2 hQ f) : ℝ → ℂ) u
  rw [h3]
  change _ = Complex.exp (((τ * quantile μ u : ℝ) : ℂ) * Complex.I) * _
  rw [h4]
  rfl

theorem adjoint_lawPhaseMul_comp_compL2 (μ : Measure ℝ) [IsProbabilityMeasure μ] (τ : ℝ) :
    adjoint (lawPhaseMul μ τ) ∘L adjoint (compL2 (measurePreserving_quantile μ))
      = adjoint (compL2 (measurePreserving_quantile μ)) ∘L adjoint (quantilePhaseMul μ τ) := by
  rw [← ContinuousLinearMap.adjoint_comp, ← ContinuousLinearMap.adjoint_comp,
    compL2_comp_lawPhaseMul]

/-! ## The prime Kummer phase -/

/-- The prime Kummer phase `p^{iy}`. -/
def kummerPhase (y : ℝ) (p : Nat.Primes) : ℂ := ((p : ℕ) : ℂ) ^ ((y : ℂ) * Complex.I)

theorem kummerPhase_eq (y : ℝ) (p : Nat.Primes) :
    kummerPhase y p = Complex.exp (((y * Real.log (p : ℕ) : ℝ) : ℂ) * Complex.I) := by
  have hp : ((p : ℕ) : ℂ) ≠ 0 := by exact_mod_cast p.prop.ne_zero
  have hlog : Complex.log ((p : ℕ) : ℂ) = ((Real.log ((p : ℕ) : ℝ) : ℝ) : ℂ) := by
    rw [← Complex.ofReal_natCast, ← Complex.ofReal_log (Nat.cast_nonneg _)]
  rw [kummerPhase, Complex.cpow_def_of_ne_zero hp, hlog]
  push_cast
  ring_nf

theorem norm_kummerPhase (y : ℝ) (p : Nat.Primes) : ‖kummerPhase y p‖ = 1 := by
  rw [kummerPhase_eq, Complex.norm_exp_ofReal_mul_I]

/-- The Kummer phase operator `D_y e_p = p^{iy} e_p` on `ℓ²(Primes)`. -/
def kummerPhaseOp (y : ℝ) : PrimeHilbert →L[ℂ] PrimeHilbert :=
  LpDiagonal.lpDiag (kummerPhase y) 1 zero_le_one fun p => (norm_kummerPhase y p).le

theorem kummerPhaseOp_basis (y : ℝ) (p : Nat.Primes) :
    kummerPhaseOp y (HilbertSchmidt.lpBasis Nat.Primes p)
      = kummerPhase y p • HilbertSchmidt.lpBasis Nat.Primes p := by
  rw [HilbertSchmidt.lpBasis_apply, kummerPhaseOp, LpDiagonal.lpDiag_single]

/-- At `y = 2dτ` the Kummer phase is the wall-chart phase `e^{iτ x_d(p)}`. -/
theorem kummerPhase_two_mul (d τ : ℝ) (p : Nat.Primes) :
    kummerPhase (2 * d * τ) p
      = Complex.exp (((τ * routePPrimitiveGammaJuliaStokesWallLogCoordinate d p : ℝ) : ℂ) *
          Complex.I) := by
  rw [kummerPhase_eq, routePPrimitiveGammaJuliaStokesWallLogCoordinate]
  congr 2
  push_cast
  ring

/-- `e^{iτx} e_p = e^{iτ x_d(p)} e_p` for the normalized atom `e_p`. -/
theorem lawPhaseMul_wallAtomVector (d τ : ℝ) (p : Nat.Primes) :
    lawPhaseMul (routePPrimitiveGammaJuliaStokesWallHalfLineLaw d) τ (wallAtomVector d p)
      = Complex.exp (((τ * routePPrimitiveGammaJuliaStokesWallLogCoordinate d p : ℝ) : ℂ) *
          Complex.I) • wallAtomVector d p := by
  refine Lp.ext ?_
  filter_upwards [(lawPhase _ τ).mulUnitary_ae (wallAtomVector d p), wallAtomVector_ae d p,
    Lp.coeFn_smul (Complex.exp (((τ * routePPrimitiveGammaJuliaStokesWallLogCoordinate d p : ℝ) :
      ℂ) * Complex.I)) (wallAtomVector d p)] with x h1 h2 h3
  change ((lawPhase _ τ).mulUnitary (wallAtomVector d p) : ℝ → ℂ) x = _
  rw [h1, h3, Pi.smul_apply, h2]
  change Complex.exp (((τ * x : ℝ) : ℂ) * Complex.I) * _ = _
  by_cases hx : x ∈ ({routePPrimitiveGammaJuliaStokesWallLogCoordinate d p} : Set ℝ)
  · rw [Set.mem_singleton_iff.mp hx]
    simp only [smul_eq_mul]
  · rw [Set.indicator_of_notMem hx, smul_zero, mul_zero, smul_zero]

/-- **(SKPM.10).**  `J_d D_{2dτ} = M_τ J_d`: the prime Kummer phase is the wall phase. -/
theorem primeAtomChart_comp_kummerPhaseOp {d : ℝ} (hd : 0 < d) (τ : ℝ) :
    primeAtomChart hd ∘L kummerPhaseOp (2 * d * τ)
      = lawPhaseMul (routePPrimitiveGammaJuliaStokesWallHalfLineLaw d) τ ∘L primeAtomChart hd := by
  refine ContinuousLinearMap.ext_on (s := Set.range (HilbertSchmidt.lpBasis Nat.Primes))
    (Submodule.dense_iff_topologicalClosure_eq_top.mpr
      (HilbertSchmidt.lpBasis Nat.Primes).dense_span) ?_
  rintro _ ⟨p, rfl⟩
  rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply, kummerPhaseOp_basis,
    map_smul, primeAtomChart_basis, kummerPhase_two_mul, lawPhaseMul_wallAtomVector]

/-- **Comoving phase transport.**  `U_d D_{2dτ} = M_{d,τ} U_d`. -/
theorem comovingChart_comp_kummerPhaseOp {d : ℝ} (hd : 0 < d) (τ : ℝ) :
    comovingChart hd ∘L kummerPhaseOp (2 * d * τ)
      = quantilePhaseMul (routePPrimitiveGammaJuliaStokesWallHalfLineLaw d) τ ∘L
          comovingChart hd := by
  rw [comovingChart, ContinuousLinearMap.comp_assoc, primeAtomChart_comp_kummerPhaseOp hd,
    ← ContinuousLinearMap.comp_assoc, compL2_comp_lawPhaseMul, ContinuousLinearMap.comp_assoc]

/-- The phase-conjugated landing `M_{d,τ} A_d M_{d,τ}*`. -/
def phasedLandingOp (d τ : ℝ) :
    Lp ℂ 2 (volume.restrict (Ioo (0 : ℝ) 1)) →L[ℂ] Lp ℂ 2 (volume.restrict (Ioo (0 : ℝ) 1)) :=
  quantilePhaseMul (routePPrimitiveGammaJuliaStokesWallHalfLineLaw d) τ ∘L wallLandingOp d ∘L
    adjoint (quantilePhaseMul (routePPrimitiveGammaJuliaStokesWallHalfLineLaw d) τ)

/-- **(SKPM.10).**  `U_d D_{2dτ} N_d D_{2dτ}* U_d* = M_{d,τ} A_d M_{d,τ}*`. -/
theorem comovingChart_conj_kummerPhase {d : ℝ} (hd : 0 < d) (τ : ℝ) :
    comovingChart hd ∘L (kummerPhaseOp (2 * d * τ) ∘L normalizedStokesUnit d ∘L
        adjoint (kummerPhaseOp (2 * d * τ))) ∘L adjoint (comovingChart hd)
      = phasedLandingOp d τ := by
  have h1 := comovingChart_comp_kummerPhaseOp hd τ
  have h2 : adjoint (kummerPhaseOp (2 * d * τ)) ∘L adjoint (comovingChart hd)
      = adjoint (comovingChart hd) ∘L
          adjoint (quantilePhaseMul (routePPrimitiveGammaJuliaStokesWallHalfLineLaw d) τ) := by
    rw [← ContinuousLinearMap.adjoint_comp, ← ContinuousLinearMap.adjoint_comp, h1]
  calc comovingChart hd ∘L (kummerPhaseOp (2 * d * τ) ∘L normalizedStokesUnit d ∘L
        adjoint (kummerPhaseOp (2 * d * τ))) ∘L adjoint (comovingChart hd)
      = (comovingChart hd ∘L kummerPhaseOp (2 * d * τ)) ∘L normalizedStokesUnit d ∘L
          (adjoint (kummerPhaseOp (2 * d * τ)) ∘L adjoint (comovingChart hd)) := by
        simp only [ContinuousLinearMap.comp_assoc]
    _ = quantilePhaseMul (routePPrimitiveGammaJuliaStokesWallHalfLineLaw d) τ ∘L
          (comovingChart hd ∘L stokesCubicUnit d ∘L adjoint (comovingChart hd)) ∘L
            adjoint (quantilePhaseMul (routePPrimitiveGammaJuliaStokesWallHalfLineLaw d) τ) := by
        rw [h1, h2, stokesCubicUnit_of_pos hd]
        simp only [ContinuousLinearMap.comp_assoc]
    _ = phasedLandingOp d τ := by
        rw [comovingChart_conj_stokesCubicUnit hd, phasedLandingOp]

/-! ## The exponential limit -/

/-- The limit `M_{0,τ} A_0 M_{0,τ}*` is the quantile transport of the phase orbit `A_τ`. -/
theorem quantilePhase_conj_quantileWallOperator (τ : ℝ) :
    quantilePhaseMul (expMeasure 1) τ ∘L quantileWallOperator ∘L
        adjoint (quantilePhaseMul (expMeasure 1) τ)
      = compL2 (measurePreserving_quantile (expMeasure 1)) ∘L phaseWallOperator τ ∘L
          adjoint (compL2 (measurePreserving_quantile (expMeasure 1))) := by
  have hW : (wallKernelOf (expMeasure 1)).op = wallOperator :=
    SqIntKernel.op_congr _ (Eventually.of_forall fun _ => Eventually.of_forall fun _ => rfl)
  rw [← quantileLandingOp_expMeasure_one, quantileLandingOp_eq_conj, hW, phaseWallOperator,
    phaseMultiplier_eq_lawPhaseMul]
  have h1 := compL2_comp_lawPhaseMul (expMeasure 1) τ
  have h2 := adjoint_lawPhaseMul_comp_compL2 (expMeasure 1) τ
  rw [ContinuousLinearMap.comp_assoc (compL2 _), ContinuousLinearMap.comp_assoc wallOperator,
    ContinuousLinearMap.comp_assoc (lawPhaseMul _ _), ContinuousLinearMap.comp_assoc wallOperator,
    h2, ← ContinuousLinearMap.comp_assoc (compL2 _) (lawPhaseMul _ _), h1,
    ContinuousLinearMap.comp_assoc (quantilePhaseMul _ _)]

/-! ## Trace-norm convergence -/

section Convergence

local instance factTwoNeTopBlowup : Fact ((2 : ℝ≥0∞) ≠ ⊤) := ⟨by norm_num⟩

/-- `M_{d,τ} → M_{0,τ}` strongly as `d → 0⁺`. -/
theorem tendsto_quantilePhaseMul_sub_apply (τ : ℝ) (g : Lp ℂ 2 (volume.restrict (Ioo (0 : ℝ) 1))) :
    Tendsto (fun d => (quantilePhaseMul (routePPrimitiveGammaJuliaStokesWallHalfLineLaw d) τ
      - quantilePhaseMul (expMeasure 1) τ) g) (𝓝[>] 0) (𝓝 0) := by
  set φ : ℝ → ℝ → ℂ := fun d u => Complex.exp (((τ *
    quantile (routePPrimitiveGammaJuliaStokesWallHalfLineLaw d) u : ℝ) : ℂ) * Complex.I)
  set φ₀ : ℝ → ℂ := fun u => Complex.exp (((τ * quantile (expMeasure 1) u : ℝ) : ℂ) * Complex.I)
  have hae : ∀ d, ((quantilePhaseMul (routePPrimitiveGammaJuliaStokesWallHalfLineLaw d) τ
      - quantilePhaseMul (expMeasure 1) τ) g : ℝ → ℂ)
        =ᵐ[volume.restrict (Ioo (0 : ℝ) 1)] fun u => (φ d u - φ₀ u) * g u := fun d => by
    filter_upwards [Lp.coeFn_sub
      (quantilePhaseMul (routePPrimitiveGammaJuliaStokesWallHalfLineLaw d) τ g)
      (quantilePhaseMul (expMeasure 1) τ g),
      (quantilePhase (routePPrimitiveGammaJuliaStokesWallHalfLineLaw d) τ).mulUnitary_ae g,
      (quantilePhase (expMeasure 1) τ).mulUnitary_ae g] with u h1 h2 h3
    rw [sub_apply, h1, Pi.sub_apply]
    change ((quantilePhase _ τ).mulUnitary g : ℝ → ℂ) u
      - ((quantilePhase (expMeasure 1) τ).mulUnitary g : ℝ → ℂ) u = _
    rw [h2, h3]
    change φ d u * g u - φ₀ u * g u = _
    ring
  have hg := SqIntKernel.lintegral_enorm_sq_lt_top g
  have hgm : Measurable (g : ℝ → ℂ) := (Lp.stronglyMeasurable g).measurable
  have hφm : ∀ d, Measurable (φ d) := fun d =>
    (by fun_prop : Continuous fun x : ℝ =>
      Complex.exp (((τ * x : ℝ) : ℂ) * Complex.I)).measurable.comp (measurable_quantile _)
  have hφ₀m : Measurable φ₀ :=
    (by fun_prop : Continuous fun x : ℝ =>
      Complex.exp (((τ * x : ℝ) : ℂ) * Complex.I)).measurable.comp (measurable_quantile _)
  have hlint : Tendsto (fun d => ∫⁻ u, ‖(φ d u - φ₀ u) * g u‖ₑ ^ 2
      ∂(volume.restrict (Ioo (0 : ℝ) 1))) (𝓝[>] 0) (𝓝 0) := by
    have h := tendsto_lintegral_filter_of_dominated_convergence (l := 𝓝[>] (0 : ℝ))
      (μ := volume.restrict (Ioo (0 : ℝ) 1)) (f := fun _ => (0 : ℝ≥0∞))
      (F := fun d u => ‖(φ d u - φ₀ u) * g u‖ₑ ^ 2) (fun u => 4 * ‖g u‖ₑ ^ 2)
      (Eventually.of_forall fun d => (((hφm d).sub hφ₀m).mul hgm).enorm.pow_const 2)
      (Eventually.of_forall fun d => Eventually.of_forall fun u => by
        rw [enorm_mul, mul_pow]
        refine mul_le_mul_left ?_ _
        have h2 : ‖φ d u - φ₀ u‖ ≤ 2 := (norm_sub_le _ _).trans (by
          simp only [φ, φ₀, Complex.norm_exp_ofReal_mul_I]; norm_num)
        rw [← ofReal_norm, ← ENNReal.ofReal_pow (norm_nonneg _),
          show (4 : ℝ≥0∞) = ENNReal.ofReal 4 by norm_num]
        exact ENNReal.ofReal_le_ofReal (by nlinarith [norm_nonneg (φ d u - φ₀ u)]))
      (by rw [lintegral_const_mul' _ _ (by norm_num)]; exact ENNReal.mul_ne_top (by norm_num) hg.ne)
      (by
        filter_upwards [ae_restrict_mem measurableSet_Ioo] with u hu
        have hQ := tendsto_wallHalfLineQuantile_nhdsGT_zero hu.1 hu.2
        have hφ : Tendsto (fun d => φ d u) (𝓝[>] 0) (𝓝 (φ₀ u)) :=
          ((by fun_prop : Continuous fun x : ℝ =>
            Complex.exp (((τ * x : ℝ) : ℂ) * Complex.I)).tendsto _).comp hQ
        have h1 : Tendsto (fun d => (φ d u - φ₀ u) * g u) (𝓝[>] 0) (𝓝 0) := by
          have := (hφ.sub_const (φ₀ u)).mul_const (g u)
          simpa using this
        have h0 : Tendsto (fun d => ‖(φ d u - φ₀ u) * g u‖ₑ ^ 2) (𝓝[>] 0)
            (𝓝 (‖(0 : ℂ)‖ₑ ^ 2)) :=
          ((ENNReal.continuous_pow 2).tendsto _).comp ((continuous_enorm.tendsto _).comp h1)
        rw [enorm_zero, zero_pow two_ne_zero] at h0
        exact h0)
    simpa using h
  rw [tendsto_zero_iff_norm_tendsto_zero]
  have hrpow : Tendsto (fun d => (∫⁻ u, ‖(φ d u - φ₀ u) * g u‖ₑ ^ 2
      ∂(volume.restrict (Ioo (0 : ℝ) 1))) ^ ((1 : ℝ) / 2)) (𝓝[>] 0) (𝓝 0) := by
    have := ((ENNReal.continuous_rpow_const (y := (1 : ℝ) / 2)).tendsto 0).comp hlint
    rwa [ENNReal.zero_rpow_of_pos (by norm_num)] at this
  have htoReal := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp hrpow
  rw [ENNReal.toReal_zero] at htoReal
  refine htoReal.congr fun d => ?_
  simp only [Function.comp_apply]
  rw [Lp.norm_def, eLpNorm_congr_ae (hae d), SchurKernel.eLpNorm_two_eq]

/-- The phase-conjugated synthesis `S_d M_{d,τ}*`. -/
def phasedSynthesis (μ : Measure ℝ) [IsProbabilityMeasure μ] (τ : ℝ) :
    Lp ℂ 2 (volume.restrict (Ioo (0 : ℝ) 1)) →L[ℂ] Lp ℂ 2 halfLineMeasure :=
  quantileBurnolSynthesis μ ∘L adjoint (quantilePhaseMul μ τ)

theorem isHilbertSchmidt_phasedSynthesis (μ : Measure ℝ) [IsProbabilityMeasure μ] (τ : ℝ) :
    IsHilbertSchmidt (phasedSynthesis μ τ) :=
  (isHilbertSchmidt_quantileBurnolSynthesis μ).comp_right _

theorem hsNorm_phasedSynthesis_le (μ : Measure ℝ) [IsProbabilityMeasure μ] (τ : ℝ) :
    ContinuousLinearMap.hsNorm (phasedSynthesis μ τ) ≤ 1 := by
  have h := ContinuousLinearMap.hsNormSq_comp_right_le (isHilbertSchmidt_quantileBurnolSynthesis μ)
    (adjoint (quantilePhaseMul μ τ))
  have hn : ‖adjoint (quantilePhaseMul μ τ)‖ ≤ 1 := by
    rw [LinearIsometryEquiv.norm_map]; exact norm_quantilePhaseMul_le μ τ
  have hS := hsNorm_quantileBurnolSynthesis_le μ
  have hS0 := ContinuousLinearMap.hsNorm_nonneg (quantileBurnolSynthesis μ)
  have hsq : ContinuousLinearMap.hsNormSq (quantileBurnolSynthesis μ) ≤ 1 := by
    rw [ContinuousLinearMap.hsNorm] at hS
    rwa [Real.sqrt_le_one] at hS
  rw [ContinuousLinearMap.hsNorm, Real.sqrt_le_one]
  have : ‖adjoint (quantilePhaseMul μ τ)‖ ^ 2 ≤ 1 := by
    nlinarith [norm_nonneg (adjoint (quantilePhaseMul μ τ))]
  have h0 := ContinuousLinearMap.hsNormSq_nonneg (quantileBurnolSynthesis μ)
  calc ContinuousLinearMap.hsNormSq (phasedSynthesis μ τ)
      ≤ ‖adjoint (quantilePhaseMul μ τ)‖ ^ 2 *
          ContinuousLinearMap.hsNormSq (quantileBurnolSynthesis μ) := h
    _ ≤ 1 * 1 := mul_le_mul this hsq h0 zero_le_one
    _ = 1 := one_mul 1

theorem phasedLandingOp_eq_adjoint_comp (d τ : ℝ) :
    phasedLandingOp d τ
      = adjoint (phasedSynthesis (routePPrimitiveGammaJuliaStokesWallHalfLineLaw d) τ) ∘L
        phasedSynthesis (routePPrimitiveGammaJuliaStokesWallHalfLineLaw d) τ := by
  rw [phasedLandingOp, wallLandingOp, quantileLandingOp_eq_adjoint_comp, phasedSynthesis,
    ContinuousLinearMap.adjoint_comp, adjoint_adjoint, ContinuousLinearMap.comp_assoc,
    ContinuousLinearMap.comp_assoc]

theorem quantilePhase_conj_quantileWallOperator_eq_adjoint_comp (τ : ℝ) :
    quantilePhaseMul (expMeasure 1) τ ∘L quantileWallOperator ∘L
        adjoint (quantilePhaseMul (expMeasure 1) τ)
      = adjoint (phasedSynthesis (expMeasure 1) τ) ∘L phasedSynthesis (expMeasure 1) τ := by
  rw [← quantileLandingOp_expMeasure_one, quantileLandingOp_eq_adjoint_comp, phasedSynthesis,
    ContinuousLinearMap.adjoint_comp, adjoint_adjoint, ContinuousLinearMap.comp_assoc,
    ContinuousLinearMap.comp_assoc]

/-- **Theorem D.**  `U_d D_{2dτ} N_d D_{2dτ}* U_d* → U_0 A_τ U_0*` in trace norm as `d → 0⁺`, where
`U_0 f = f ∘ Q_0` is the exponential quantile chart. -/
theorem tendsto_traceNorm_phasedLandingOp_sub (τ : ℝ) :
    Tendsto (fun d => traceNorm (Lp ℂ 2 (volume.restrict (Ioo (0 : ℝ) 1)))
      (phasedLandingOp d τ - compL2 (measurePreserving_quantile (expMeasure 1)) ∘L
        phaseWallOperator τ ∘L adjoint (compL2 (measurePreserving_quantile (expMeasure 1)))))
      (𝓝[>] 0) (𝓝 0) := by
  rw [← quantilePhase_conj_quantileWallOperator]
  set μ : ℝ → Measure ℝ := routePPrimitiveGammaJuliaStokesWallHalfLineLaw
  set S₀ := quantileBurnolSynthesis (expMeasure 1)
  set M₀ := quantilePhaseMul (expMeasure 1) τ
  have hS₀ := isHilbertSchmidt_quantileBurnolSynthesis (expMeasure 1)
  -- the two Hilbert–Schmidt error terms
  have hterm1 := tendsto_hsNorm_wallSynthesis_sub
  have hterm2 : Tendsto (fun d => ContinuousLinearMap.hsNorm
      ((quantilePhaseMul (μ d) τ - M₀) ∘L adjoint S₀)) (𝓝[>] 0) (𝓝 0) := by
    have h := tendsto_hsNormSq_comp_of_tendsto_apply hS₀.adjoint (l := 𝓝[>] (0 : ℝ))
      (B := fun d => quantilePhaseMul (μ d) τ - M₀) (C := 2)
      (fun d => (norm_sub_le _ _).trans (by
        linarith [norm_quantilePhaseMul_le (μ d) τ, norm_quantilePhaseMul_le (expMeasure 1) τ]))
      (tendsto_quantilePhaseMul_sub_apply τ)
    have := (Real.continuous_sqrt.tendsto 0).comp h
    rw [Real.sqrt_zero] at this
    exact this
  have hup : Tendsto (fun d => 2 * (ContinuousLinearMap.hsNorm
      (quantileBurnolSynthesis (μ d) - S₀) + ContinuousLinearMap.hsNorm
        ((quantilePhaseMul (μ d) τ - M₀) ∘L adjoint S₀))) (𝓝[>] 0) (𝓝 0) := by
    have := (hterm1.add hterm2).const_mul 2
    simpa using this
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hup
    (fun _ => traceNorm_nonneg _) fun d => ?_
  set S := quantileBurnolSynthesis (μ d)
  set M := quantilePhaseMul (μ d) τ
  have hS := isHilbertSchmidt_quantileBurnolSynthesis (μ d)
  have hV := isHilbertSchmidt_phasedSynthesis (μ d) τ
  have hV₀ := isHilbertSchmidt_phasedSynthesis (expMeasure 1) τ
  have h := traceNorm_adjoint_comp_self_sub_le hV hV₀
  rw [← phasedLandingOp_eq_adjoint_comp, ← quantilePhase_conj_quantileWallOperator_eq_adjoint_comp]
    at h
  refine h.trans ?_
  have h1 := hsNorm_phasedSynthesis_le (μ d) τ
  have h2 := hsNorm_phasedSynthesis_le (expMeasure 1) τ
  have hsplit : phasedSynthesis (μ d) τ - phasedSynthesis (expMeasure 1) τ
      = (S - S₀) ∘L adjoint M + S₀ ∘L (adjoint M - adjoint M₀) := by
    simp only [phasedSynthesis, ContinuousLinearMap.sub_comp, ContinuousLinearMap.comp_sub]
    abel
  have hA : ContinuousLinearMap.hsNorm ((S - S₀) ∘L adjoint M)
      ≤ ContinuousLinearMap.hsNorm (S - S₀) := by
    have hD := hS.sub hS₀
    have hc := ContinuousLinearMap.hsNormSq_comp_right_le hD (adjoint M)
    have hn : ‖adjoint M‖ ≤ 1 := by
      rw [LinearIsometryEquiv.norm_map]; exact norm_quantilePhaseMul_le (μ d) τ
    have : ‖adjoint M‖ ^ 2 ≤ 1 := by nlinarith [norm_nonneg (adjoint M)]
    have h0 := ContinuousLinearMap.hsNormSq_nonneg (S - S₀)
    exact Real.sqrt_le_sqrt (hc.trans (by nlinarith))
  have hB : ContinuousLinearMap.hsNorm (S₀ ∘L (adjoint M - adjoint M₀))
      = ContinuousLinearMap.hsNorm ((M - M₀) ∘L adjoint S₀) := by
    have hX : IsHilbertSchmidt (S₀ ∘L (adjoint M - adjoint M₀)) := hS₀.comp_right _
    rw [ContinuousLinearMap.hsNorm, ← hX.hsNormSq_adjoint, ContinuousLinearMap.adjoint_comp,
      map_sub, adjoint_adjoint, adjoint_adjoint, ContinuousLinearMap.hsNorm]
  have hsum : ContinuousLinearMap.hsNorm
      (phasedSynthesis (μ d) τ - phasedSynthesis (expMeasure 1) τ)
      ≤ ContinuousLinearMap.hsNorm (S - S₀)
        + ContinuousLinearMap.hsNorm ((M - M₀) ∘L adjoint S₀) := by
    rw [hsplit, ← hB]
    refine (ContinuousLinearMap.hsNorm_add_le ((hS.sub hS₀).comp_right _)
      (hS₀.comp_right _)).trans ?_
    linarith
  have h3 := ContinuousLinearMap.hsNorm_nonneg
    (phasedSynthesis (μ d) τ - phasedSynthesis (expMeasure 1) τ)
  nlinarith

/-- **Theorem D.**  Under the comoving chart the Kummer-phase-conjugated children at `(d, 2dτ)`
are the quantile phase conjugates `M_{d,τ} A_d M_{d,τ}*`, and these converge in trace norm to the
quantile transport of `A_τ`. -/
theorem kummer_parabolic_wall_blowup (τ : ℝ) :
    (∀ (d : ℝ) (hd : 0 < d),
      comovingChart hd ∘L kummerPhaseOp (2 * d * τ)
          = quantilePhaseMul (routePPrimitiveGammaJuliaStokesWallHalfLineLaw d) τ ∘L
            comovingChart hd ∧
        comovingChart hd ∘L (kummerPhaseOp (2 * d * τ) ∘L normalizedStokesUnit d ∘L
          adjoint (kummerPhaseOp (2 * d * τ))) ∘L adjoint (comovingChart hd)
          = phasedLandingOp d τ) ∧
      Tendsto (fun d => traceNorm (Lp ℂ 2 (volume.restrict (Ioo (0 : ℝ) 1)))
        (phasedLandingOp d τ - compL2 (measurePreserving_quantile (expMeasure 1)) ∘L
          phaseWallOperator τ ∘L adjoint (compL2 (measurePreserving_quantile (expMeasure 1)))))
        (𝓝[>] 0) (𝓝 0) :=
  ⟨fun _ hd => ⟨comovingChart_comp_kummerPhaseOp hd τ, comovingChart_conj_kummerPhase hd τ⟩,
    tendsto_traceNorm_phasedLandingOp_sub τ⟩

end Convergence

end GaloisForLFunctions.HTGeometry
