import GaloisForLFunctions.RHTower.ChenGuptaLiClassIILeftIntegrand

open Complex Topology

noncomputable section

namespace RHTower

/-- The Class-II left vertical line varies continuously with its imaginary coordinate. -/
theorem continuous_cglPrimitiveClassILeftLinePoint
    (n : ℕ) (χ : PrimitiveNonprincipalDirichletCharacter n) (τ : ℝ) (H : NNReal)
    (z : CGLPrimitiveClassIWindowZero n χ τ H) :
    Continuous (cglPrimitiveClassILeftLinePoint n χ τ H z) := by
  unfold cglPrimitiveClassILeftLinePoint
  fun_prop

/-- Gamma has no pole along the Class-II left vertical line. -/
theorem continuous_cglPrimitiveClassILeftLineGamma
    (n : ℕ) (χ : PrimitiveNonprincipalDirichletCharacter n) (τ : ℝ) (H : NNReal)
    (z : CGLPrimitiveClassIWindowZero n χ τ H) :
    Continuous fun t : ℝ => Complex.Gamma (cglPrimitiveClassILeftLinePoint n χ τ H z t) := by
  rw [continuous_iff_continuousAt]
  intro t
  apply (Complex.continuousAt_Gamma _ ?_).comp
  · exact (continuous_cglPrimitiveClassILeftLinePoint n χ τ H z).continuousAt
  · intro m hm
    have hre := congrArg Complex.re hm
    simp [cglPrimitiveClassILeftLinePoint] at hre
    have hlt :=
      (cglPrimitiveNonprincipalCriticalStripLZeroOfClassIWindowZero n χ τ H z).lt_one
    change z.1.1.re < 1 at hlt
    have hbeta : z.1.1.re < 1 := hlt
    cases m with
    | zero => linarith [z.2]
    | succ m =>
        have hmone : (1 : ℝ) ≤ (Nat.succ m : ℕ) := by
          exact_mod_cast Nat.succ_le_succ (Nat.zero_le m)
        linarith [z.2, hbeta]

theorem continuous_cglPrimitiveClassILeftLineSmoothing
    (Y n : ℕ) (χ : PrimitiveNonprincipalDirichletCharacter n) (τ : ℝ) (H : NNReal)
    (z : CGLPrimitiveClassIWindowZero n χ τ H) :
    Continuous fun t : ℝ =>
      ((Y + 1 : ℕ) : ℂ) ^ (cglPrimitiveClassILeftLinePoint n χ τ H z t) := by
  rw [continuous_iff_continuousAt]
  intro t
  have hout : ContinuousAt (fun w : ℂ => ((Y + 1 : ℕ) : ℂ) ^ w)
      (cglPrimitiveClassILeftLinePoint n χ τ H z t) :=
    (cglSmoothingWeight_analyticAt Y (cglPrimitiveClassILeftLinePoint n χ τ H z t)).differentiableAt.continuousAt
  have hpath : ContinuousAt (cglPrimitiveClassILeftLinePoint n χ τ H z) t :=
    (continuous_cglPrimitiveClassILeftLinePoint n χ τ H z).continuousAt
  simpa only [Function.comp_def] using
    hout.comp (f := cglPrimitiveClassILeftLinePoint n χ τ H z) hpath

theorem continuous_cglPrimitiveClassILeftLineMollifier
    (X n : ℕ) (χ : PrimitiveNonprincipalDirichletCharacter n) (τ : ℝ) (H : NNReal)
    (z : CGLPrimitiveClassIWindowZero n χ τ H) :
    Continuous fun t : ℝ => zeroDetectionMobiusPolynomial X (n + 1) χ.1.1
      (cglCriticalLinePoint (z.1.1.im + t)).1 := by
  have hpath : Continuous fun t : ℝ => ((cglCriticalLinePoint (z.1.1.im + t)).1 : ℂ) := by
    change Continuous fun t : ℝ => (1 / 2 : ℂ) + ((z.1.1.im + t : ℝ) : ℂ) * I
    fun_prop
  rw [continuous_iff_continuousAt]
  intro t
  have hout : ContinuousAt (zeroDetectionMobiusPolynomial X (n + 1) χ.1.1)
      ((cglCriticalLinePoint (z.1.1.im + t)).1 : ℂ) :=
    continuousAt_zeroDetectionMobiusPolynomial X (n + 1) χ.1.1
      ((cglCriticalLinePoint (z.1.1.im + t)).1 : ℂ)
  have hpathAt : ContinuousAt (fun v : ℝ =>
      ((cglCriticalLinePoint (z.1.1.im + v)).1 : ℂ)) t := hpath.continuousAt
  simpa only [Function.comp_def] using
    hout.comp (f := fun v : ℝ => ((cglCriticalLinePoint (z.1.1.im + v)).1 : ℂ)) hpathAt

/-- The non-L-function factor of the Class-II left-line integrand is continuous. -/
theorem continuous_cglPrimitiveClassILeftLineWeight
    (X n Y : ℕ) (χ : PrimitiveNonprincipalDirichletCharacter n) (τ : ℝ) (H : NNReal)
    (z : CGLPrimitiveClassIWindowZero n χ τ H) :
    Continuous (cglPrimitiveClassILeftLineWeight X n Y χ τ H z) := by
  unfold cglPrimitiveClassILeftLineWeight
  exact ((continuous_cglPrimitiveClassILeftLineSmoothing Y n χ τ H z).mul
    (continuous_cglPrimitiveClassILeftLineGamma n χ τ H z)).mul
      (continuous_cglPrimitiveClassILeftLineMollifier X n χ τ H z)

theorem exists_cglPrimitiveClassILeftLineWeightMaximizer
    (X n Y : ℕ) (χ : PrimitiveNonprincipalDirichletCharacter n) (τ : ℝ) (H : NNReal)
    (z : CGLPrimitiveClassIWindowZero n χ τ H) (B : NNReal) :
    ∃ u : CGLClassIICriticalLineLocalOffset B,
      IsMaxOn (fun v : ℝ => ‖cglPrimitiveClassILeftLineWeight X n Y χ τ H z v‖)
        (CGLClassIICriticalLineLocalOffset B) u := by
  have hcompact : IsCompact (CGLClassIICriticalLineLocalOffset B) := isCompact_Icc
  have hnonempty : (CGLClassIICriticalLineLocalOffset B).Nonempty := by
    refine ⟨0, ?_⟩
    simp [CGLClassIICriticalLineLocalOffset]
  obtain ⟨u, hu, hmax⟩ := hcompact.exists_isMaxOn hnonempty
    (continuous_cglPrimitiveClassILeftLineWeight X n Y χ τ H z).norm.continuousOn
  exact ⟨⟨u, hu⟩, hmax⟩

/-- A selected maximizer for the compact non-L-function envelope. -/
noncomputable def cglPrimitiveClassILeftLineWeightMaximizer
    (X n Y : ℕ) (χ : PrimitiveNonprincipalDirichletCharacter n) (τ : ℝ) (H : NNReal)
    (z : CGLPrimitiveClassIWindowZero n χ τ H) (B : NNReal) :
    CGLClassIICriticalLineLocalOffset B :=
  Classical.choose (exists_cglPrimitiveClassILeftLineWeightMaximizer X n Y χ τ H z B)

/-- Maximum norm of the non-L-function Class-II factor on a finite left segment. -/
def cglPrimitiveClassILeftLineWeightEnvelope
    (X n Y : ℕ) (χ : PrimitiveNonprincipalDirichletCharacter n) (τ : ℝ) (H : NNReal)
    (z : CGLPrimitiveClassIWindowZero n χ τ H) (B : NNReal) : ℝ :=
  ‖cglPrimitiveClassILeftLineWeight X n Y χ τ H z
    (cglPrimitiveClassILeftLineWeightMaximizer X n Y χ τ H z B).1‖

theorem norm_cglPrimitiveClassILeftLineWeight_le_envelope
    (X n Y : ℕ) (χ : PrimitiveNonprincipalDirichletCharacter n) (τ : ℝ) (H : NNReal)
    (z : CGLPrimitiveClassIWindowZero n χ τ H) (B : NNReal)
    (u : CGLClassIICriticalLineLocalOffset B) :
    ‖cglPrimitiveClassILeftLineWeight X n Y χ τ H z u.1‖ ≤
      cglPrimitiveClassILeftLineWeightEnvelope X n Y χ τ H z B := by
  exact (Classical.choose_spec
    (exists_cglPrimitiveClassILeftLineWeightMaximizer X n Y χ τ H z B)) u.2

end RHTower
