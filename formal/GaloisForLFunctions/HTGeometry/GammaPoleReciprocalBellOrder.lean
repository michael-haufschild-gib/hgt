import GaloisForLFunctions.HTGeometry.GammaSimpleZeroBellHorizonAnalytic
import GaloisForLFunctions.HTGeometry.MeromorphicPuncturedRepresentation
import GaloisForLFunctions.HTGeometry.GammaPoleSymbolicTriGrading

/-!
# Reciprocal-Bell compression of Gamma-pole jet orders

A homogeneous differential polynomial in the jets of an inverse analytic
section has a canonical factorization.  Its particle degree becomes a power
of the inverse section, while the remaining normalized jet polynomial passes
through three exact coordinate changes: complete Bell substitution, sign
reflection of the logarithmic jets, and inverse Bell substitution into the
simple-zero covariant frame.

For the factorially normalized Gamma poles, this turns the full analytic
Taylor-cancellation problem inside a homogeneous sector into one polynomial
degree.  Every nonzero sector of particle degree `D` has exact native order
`-(D + E)` on arbitrarily remote poles, where `E` is the total degree of its
reciprocal-Bell covariant transform.  A faithful Fock completion retains all
particle sectors and gives one general value law before any pole-order
selection.  The final results reflect exact top residues to native `z`
derivatives and classify the homogeneous at-most-simple source interface as
precisely scalars and scalar multiples of undifferentiated Gamma.
-/

open Complex Filter Topology MvPolynomial

namespace GaloisForLFunctions

noncomputable section

/-- Negate every raw logarithmic-jet coordinate. -/
def negativeRawJetMap (n : ℕ) :
    MvPolynomial (Fin (n + 1)) ℂ →+* MvPolynomial (Fin (n + 1)) ℂ :=
  diagonalCoordinateMap (fun _ => -1)

/-- Convert a homogeneous jet polynomial of an inverse section into the
covariant simple-zero coordinates of the original section. -/
def reciprocalBellCovariantTransform (n : ℕ) :
    MvPolynomial (Fin (n + 2)) ℂ →+* MvPolynomial (Fin (n + 1)) ℂ :=
  (HTGeometry.bellCoefficientEquiv n).symm.toRingHom.comp
    ((negativeRawJetMap n).comp
      ((bellCoefficientMap n).comp
        (HTGeometry.simpleZeroDehomogenize (n + 1))))

theorem reciprocalBellCovariantTransform_ne_zero_of_isHomogeneous
    {n D : ℕ} {P : MvPolynomial (Fin (n + 2)) ℂ}
    (hP : P.IsHomogeneous D) (hP0 : P ≠ 0) :
    reciprocalBellCovariantTransform n P ≠ 0 := by
  have hdehom : HTGeometry.simpleZeroDehomogenize (n + 1) P ≠ 0 :=
    HTGeometry.simpleZeroDehomogenize_ne_zero_of_isHomogeneous hP hP0
  have hbell : bellCoefficientMap n
      (HTGeometry.simpleZeroDehomogenize (n + 1) P) ≠ 0 :=
    (bellCoefficientMap_injective n).ne hdehom
  have hneg : negativeRawJetMap n
      (bellCoefficientMap n
        (HTGeometry.simpleZeroDehomogenize (n + 1) P)) ≠ 0 :=
    (diagonalCoordinateMap_injective (fun _ : Fin (n + 1) => by norm_num)).ne hbell
  simpa [reciprocalBellCovariantTransform] using
    (HTGeometry.bellCoefficientEquiv n).symm.injective.ne hneg

/-- Evaluate a finite jet polynomial on the reciprocal of a section. -/
def inverseSectionJetEval (S : ℂ → ℂ) (n : ℕ)
    (P : MvPolynomial (Fin (n + 2)) ℂ) (x : ℂ) : ℂ :=
  MvPolynomial.eval
    (fun j : Fin (n + 2) => iteratedDeriv (j : ℕ) (fun z => (S z)⁻¹) x) P

/-- Evaluate a polynomial on the complete simple-zero covariant ratios. -/
def simpleZeroCovariantSectionEval (S : ℂ → ℂ) (n : ℕ)
    (P : MvPolynomial (Fin (n + 1)) ℂ) (x : ℂ) : ℂ :=
  MvPolynomial.eval
    (fun j : Fin (n + 1) =>
      iteratedDeriv ((j : ℕ) + 1) S x / S x) P

theorem eval_simpleZeroDehomogenize
    (n : ℕ) (y : Fin (n + 1) → ℂ)
    (P : MvPolynomial (Fin (n + 2)) ℂ) :
    MvPolynomial.eval y (HTGeometry.simpleZeroDehomogenize (n + 1) P) =
      MvPolynomial.eval (Fin.cases (1 : ℂ) y) P := by
  let lhs : MvPolynomial (Fin (n + 2)) ℂ →+* ℂ :=
    (MvPolynomial.eval y).comp (HTGeometry.simpleZeroDehomogenize (n + 1))
  have hhom : lhs = MvPolynomial.eval (Fin.cases (1 : ℂ) y) := by
    apply MvPolynomial.ringHom_ext
    · intro c
      simp [lhs, HTGeometry.simpleZeroDehomogenize]
    · intro j
      induction j using Fin.cases with
      | zero => simp [lhs, HTGeometry.simpleZeroDehomogenize,
          HTGeometry.simpleZeroBoundaryResidue]
      | succ j => simp [lhs, HTGeometry.simpleZeroDehomogenize,
          HTGeometry.simpleZeroBoundaryResidue]
  exact RingHom.congr_fun hhom P

theorem eval_negativeRawJetMap
    (n : ℕ) (y : Fin (n + 1) → ℂ)
    (P : MvPolynomial (Fin (n + 1)) ℂ) :
    MvPolynomial.eval y (negativeRawJetMap n P) =
      MvPolynomial.eval (fun j => -y j) P := by
  let lhs : MvPolynomial (Fin (n + 1)) ℂ →+* ℂ :=
    (MvPolynomial.eval y).comp (negativeRawJetMap n)
  have hhom : lhs = MvPolynomial.eval (fun j => -y j) := by
    apply MvPolynomial.ringHom_ext
    · intro c
      simp [lhs, negativeRawJetMap, diagonalCoordinateMap]
    · intro j
      simp [lhs, negativeRawJetMap, diagonalCoordinateMap]
  exact RingHom.congr_fun hhom P

theorem iteratedDeriv_logDeriv_inv_eq_neg
    {S : ℂ → ℂ} {x : ℂ} (hS : AnalyticAt ℂ S x) (hS0 : S x ≠ 0)
    (j : ℕ) :
    iteratedDeriv j
        (fun w => deriv (fun z => (S z)⁻¹) w / (S w)⁻¹) x =
      -iteratedDeriv j (fun w => deriv S w / S w) x := by
  have heq :
      (fun w => deriv (fun z => (S z)⁻¹) w / (S w)⁻¹) =ᶠ[𝓝 x]
        (fun w => -(deriv S w / S w)) := by
    filter_upwards [hS.eventually_analyticAt,
      hS.continuousAt.eventually_ne hS0] with w hSw hSw0
    rw [deriv_fun_inv'' hSw.differentiableAt hSw0]
    field_simp [hSw0]
  rw [heq.iteratedDeriv_eq j]
  rw [show (fun w => -(deriv S w / S w)) =
      fun w => (-1 : ℂ) * (deriv S w / S w) by funext w; ring]
  rw [congrFun (iteratedDeriv_const_mul_field (-1 : ℂ)
    (fun w => deriv S w / S w) j) x]
  ring

/-- **Reciprocal Bell homogeneous value law.**  A homogeneous polynomial
in the jets of `S⁻¹` factors into the corresponding power of `S⁻¹` and a
Bell-covariant polynomial in the simple-zero ratios of `S`. -/
theorem inverseSectionJetEval_eq_covariant
    {S : ℂ → ℂ} {x : ℂ} (hS : AnalyticAt ℂ S x) (hS0 : S x ≠ 0)
    {n D : ℕ} {P : MvPolynomial (Fin (n + 2)) ℂ}
    (hP : P.IsHomogeneous D) :
    inverseSectionJetEval S n P x =
      (S x)⁻¹ ^ D * simpleZeroCovariantSectionEval S n
        (reciprocalBellCovariantTransform n P) x := by
  let f : ℂ → ℂ := fun z => (S z)⁻¹
  let H := HTGeometry.simpleZeroDehomogenize (n + 1) P
  let Q := reciprocalBellCovariantTransform n P
  let raw : Fin (n + 1) → ℂ := fun j =>
    iteratedDeriv (j : ℕ) (fun w => deriv S w / S w) x
  let ratios : Fin (n + 1) → ℂ := fun j =>
    iteratedDeriv ((j : ℕ) + 1) f x / f x
  let cov : Fin (n + 1) → ℂ := fun j =>
    iteratedDeriv ((j : ℕ) + 1) S x / S x
  let normalized : Fin (n + 2) → ℂ := Fin.cases (1 : ℂ) ratios
  have hf : AnalyticAt ℂ f x := hS.inv hS0
  have hf0 : f x ≠ 0 := inv_ne_zero hS0
  have hratio (j : Fin (n + 1)) :
      ratios j = MvPolynomial.eval (fun i => -raw i)
        (bellAt n ((j : ℕ) + 1) j.isLt) := by
    have hbell := iteratedDeriv_eq_bellCore_analyticAt hf hf0 ((j : ℕ) + 1)
    have hcancel : iteratedDeriv ((j : ℕ) + 1) f x / f x =
        MvPolynomial.eval
          (fun i : Fin ((j : ℕ) + 1) =>
            iteratedDeriv (i : ℕ) (fun w => deriv f w / f w) x)
          (bellCore ((j : ℕ) + 1)) := by
      rw [hbell]
      exact mul_div_cancel_left₀ _ hf0
    change iteratedDeriv ((j : ℕ) + 1) f x / f x =
      MvPolynomial.eval
        (fun i : Fin (n + 1) =>
          -iteratedDeriv (i : ℕ) (fun w => deriv S w / S w) x)
        (bellAt n ((j : ℕ) + 1) j.isLt)
    rw [hcancel, bellAt, MvPolynomial.eval_rename]
    apply congrArg (fun v => MvPolynomial.eval v (bellCore ((j : ℕ) + 1)))
    funext i
    rw [iteratedDeriv_logDeriv_inv_eq_neg hS hS0]
    rfl
  have hscale := GaloisForLFunctions.isHomogeneous_eval₂_scale hP
    (RingHom.id ℂ) normalized (f x)
  have hscaledJets :
      (fun j : Fin (n + 2) => f x * normalized j) =
        fun j : Fin (n + 2) => iteratedDeriv (j : ℕ) f x := by
    funext j
    induction j using Fin.cases with
    | zero => simp [normalized, f, iteratedDeriv_zero]
    | succ j =>
        simp only [normalized, Fin.cases_succ, ratios, Fin.val_succ]
        exact mul_div_cancel₀ _ hf0
  have hfactor :
      inverseSectionJetEval S n P x =
        f x ^ D * MvPolynomial.eval ratios H := by
    change MvPolynomial.eval
        (fun j : Fin (n + 2) => iteratedDeriv (j : ℕ) f x) P = _
    rw [← hscaledJets]
    rw [show MvPolynomial.eval (fun j => f x * normalized j) P =
        MvPolynomial.eval₂ (RingHom.id ℂ)
          (fun j => f x * normalized j) P by rfl]
    rw [hscale]
    change f x ^ D * MvPolynomial.eval normalized P =
      f x ^ D * MvPolynomial.eval ratios H
    congr 1
    rw [show normalized = Fin.cases (1 : ℂ) ratios by rfl]
    exact (eval_simpleZeroDehomogenize n ratios P).symm
  have hratioEval : MvPolynomial.eval ratios H =
      MvPolynomial.eval raw (negativeRawJetMap n (bellCoefficientMap n H)) := by
    calc
      MvPolynomial.eval ratios H =
          MvPolynomial.eval
            (fun j : Fin (n + 1) => MvPolynomial.eval (fun i => -raw i)
              (bellAt n ((j : ℕ) + 1) j.isLt)) H := by
            apply congrArg (fun v => MvPolynomial.eval v H)
            funext j
            exact hratio j
      _ = MvPolynomial.eval (fun i => -raw i) (bellCoefficientMap n H) := by
            rw [eval_bellCoefficientMap]
      _ = MvPolynomial.eval raw
            (negativeRawJetMap n (bellCoefficientMap n H)) := by
            rw [eval_negativeRawJetMap]
  have hbellQ : bellCoefficientMap n Q =
      negativeRawJetMap n (bellCoefficientMap n H) := by
    rw [show bellCoefficientMap n Q = HTGeometry.bellCoefficientEquiv n Q by
      rw [HTGeometry.bellCoefficientEquiv_apply]]
    simp [Q, H, reciprocalBellCovariantTransform]
  have hrawCov :
      MvPolynomial.eval raw (negativeRawJetMap n (bellCoefficientMap n H)) =
        MvPolynomial.eval cov Q := by
    rw [← hbellQ]
    simpa [raw, cov] using
      (eval_bellCoefficientMap_logDeriv_eq_covariant hS hS0 n Q)
  rw [hfactor, hratioEval, hrawCov]
  rfl

theorem analyticAt_gammaPoleSimpleZeroSection_zero (branch : ℕ) :
    AnalyticAt ℂ (gammaPoleSimpleZeroSection branch) 0 := by
  unfold gammaPoleSimpleZeroSection
  exact (by fun_prop : AnalyticAt ℂ (fun z : ℂ => -z) 0) |>.mul
    ((gammaPoleRegularUnit_analyticAt_zero branch).inv (by
      rw [gammaPoleRegularUnit_zero]
      exact one_ne_zero))

theorem gammaPoleSimpleZeroSection_eventually_ne_zero (branch : ℕ) :
    ∀ᶠ x : ℂ in 𝓝[≠] 0, gammaPoleSimpleZeroSection branch x ≠ 0 := by
  have hUan := gammaPoleRegularUnit_analyticAt_zero branch
  have hUne : ∀ᶠ x : ℂ in 𝓝[≠] 0, gammaPoleRegularUnit branch x ≠ 0 :=
    nhdsWithin_le_nhds (hUan.continuousAt.eventually_ne (by
      rw [gammaPoleRegularUnit_zero]
      exact one_ne_zero))
  filter_upwards [hUne, self_mem_nhdsWithin] with x hUx hx
  have hx0 : x ≠ 0 := by simpa using hx
  simp [gammaPoleSimpleZeroSection, hx0, hUx]

/-- The homogeneous reciprocal Bell factorization holds throughout the
deleted Gamma-pole chart, with every analyticity and nonvanishing condition
discharged. -/
theorem inverseSectionJetEval_gammaPole_eventuallyEq_covariant
    (branch : ℕ) {n D : ℕ} {P : MvPolynomial (Fin (n + 2)) ℂ}
    (hP : P.IsHomogeneous D) :
    inverseSectionJetEval (gammaPoleSimpleZeroSection branch) n P =ᶠ[𝓝[≠] 0]
      (fun x => (gammaPoleSimpleZeroSection branch x)⁻¹ ^ D *
        gammaSimpleZeroCovariantEval branch n
          (reciprocalBellCovariantTransform n P) x) := by
  have hS := analyticAt_gammaPoleSimpleZeroSection_zero branch
  have hSan : ∀ᶠ x : ℂ in 𝓝[≠] 0,
      AnalyticAt ℂ (gammaPoleSimpleZeroSection branch) x :=
    nhdsWithin_le_nhds hS.eventually_analyticAt
  filter_upwards [hSan, gammaPoleSimpleZeroSection_eventually_ne_zero branch]
      with x hSx hSx0
  simpa [simpleZeroCovariantSectionEval] using
    inverseSectionJetEval_eq_covariant hSx hSx0 hP

theorem meromorphicOrderAt_inv_gammaPoleSimpleZeroSection (branch : ℕ) :
    meromorphicOrderAt
        (fun x => (gammaPoleSimpleZeroSection branch x)⁻¹) 0 =
      ((-1 : ℤ) : WithTop ℤ) := by
  have hS := analyticAt_gammaPoleSimpleZeroSection_zero branch
  have hzero : gammaPoleSimpleZeroSection branch 0 = 0 := by
    simp [gammaPoleSimpleZeroSection]
  have hderiv : deriv (gammaPoleSimpleZeroSection branch) 0 ≠ 0 := by
    rw [deriv_gammaPoleSimpleZeroSection_zero]
    exact neg_ne_zero.mpr one_ne_zero
  have horder : analyticOrderAt (gammaPoleSimpleZeroSection branch) 0 = 1 :=
    hS.analyticOrderAt_eq_one_of_zero_deriv_ne_zero hzero hderiv
  change meromorphicOrderAt ((gammaPoleSimpleZeroSection branch)⁻¹) 0 = _
  rw [meromorphicOrderAt_inv, hS.meromorphicOrderAt_eq, horder]
  rfl

/-- **Homogeneous reciprocal-Gamma cofinal order law.**  Every nonzero
homogeneous inverse-section jet packet has exact native order `-(D+E)` on
arbitrarily remote Gamma branches, where `E` is the covariant degree of its
reciprocal Bell transform. -/
theorem exists_cofinal_meromorphicOrderAt_inverseSectionJetEval_gammaPole
    {n D : ℕ} {P : MvPolynomial (Fin (n + 2)) ℂ}
    (hP : P.IsHomogeneous D) (hP0 : P ≠ 0) (B : ℕ) :
    ∃ branch : ℕ, B ≤ branch ∧
      meromorphicOrderAt
          (inverseSectionJetEval (gammaPoleSimpleZeroSection branch) n P) 0 =
        ((-((D + (reciprocalBellCovariantTransform n P).totalDegree : ℕ) : ℤ) : ℤ) :
          WithTop ℤ) := by
  let Q := reciprocalBellCovariantTransform n P
  have hQ : Q ≠ 0 :=
    reciprocalBellCovariantTransform_ne_zero_of_isHomogeneous hP hP0
  obtain ⟨branch, hbranch, hQorder⟩ :=
    exists_cofinal_meromorphicOrderAt_gammaSimpleZeroCovariantEval hQ B
  refine ⟨branch, hbranch, ?_⟩
  have hS := analyticAt_gammaPoleSimpleZeroSection_zero branch
  have hInv : MeromorphicAt
      (fun x => (gammaPoleSimpleZeroSection branch x)⁻¹) 0 :=
    hS.meromorphicAt.inv
  have hCov := meromorphicAt_gammaSimpleZeroCovariantEval branch n Q
  rw [meromorphicOrderAt_congr
    (inverseSectionJetEval_gammaPole_eventuallyEq_covariant branch hP)]
  change meromorphicOrderAt
      (((fun x => (gammaPoleSimpleZeroSection branch x)⁻¹) ^ D) *
        gammaSimpleZeroCovariantEval branch n Q) 0 = _
  rw [meromorphicOrderAt_mul (hInv.pow D) hCov,
    meromorphicOrderAt_pow hInv,
    meromorphicOrderAt_inv_gammaPoleSimpleZeroSection branch,
    hQorder]
  norm_num [Q]
  rw [add_comm]
  have hD : (D : WithTop ℤ) * (-1 : WithTop ℤ) = -(D : WithTop ℤ) := by
    change (((D : ℤ) * (-1 : ℤ) : ℤ) : WithTop ℤ) =
      ((-(D : ℤ) : ℤ) : WithTop ℤ)
    rw [mul_neg_one]
  rw [hD]

/-- Evaluation on the complete jet of the factorially normalized Gamma pole
as a function of its local coordinate. -/
def gammaFactorialJetEval (branch n : ℕ)
    (P : MvPolynomial (Fin (n + 2)) ℂ) (x : ℂ) : ℂ :=
  MvPolynomial.eval
    (fun j : Fin (n + 2) =>
      iteratedDeriv (j : ℕ) (factorialBlowUpZoom Complex.Gamma branch) x) P

/-- The inverse simple-zero section and the actual factorial Gamma zoom have
identical complete finite jets on a deleted neighborhood. -/
theorem gammaFactorialJetEval_eventuallyEq_inverseSectionJetEval
    (branch n : ℕ) (P : MvPolynomial (Fin (n + 2)) ℂ) :
    gammaFactorialJetEval branch n P =ᶠ[𝓝[≠] 0]
      inverseSectionJetEval (gammaPoleSimpleZeroSection branch) n P := by
  have hbase : factorialBlowUpZoom Complex.Gamma branch =ᶠ[𝓝 0]
      (fun x => (gammaPoleSimpleZeroSection branch x)⁻¹) := by
    rw [factorialBlowUpZoom_Gamma_eq_inv_reciprocalGammaFactorialZoom]
    filter_upwards [gammaPoleSimpleZeroSection_eventuallyEq_reciprocalGammaFactorialZoom branch]
      with x hx
    rw [hx]
  have hj : ∀ j : Fin (n + 2),
      iteratedDeriv (j : ℕ) (factorialBlowUpZoom Complex.Gamma branch) =ᶠ[𝓝[≠] 0]
        iteratedDeriv (j : ℕ)
          (fun x => (gammaPoleSimpleZeroSection branch x)⁻¹) := by
    intro j
    exact EventuallyEq.nhdsNE_iteratedDeriv (nhdsWithin_le_nhds hbase) (j : ℕ)
  filter_upwards [Filter.eventually_all.mpr hj] with x hx
  apply congrArg (fun v : Fin (n + 2) → ℂ => MvPolynomial.eval v P)
  funext j
  exact hx j

/-- The actual factorial Gamma packet and its reciprocal-section model have
the same meromorphic order. -/
theorem meromorphicOrderAt_gammaFactorialJetEval_eq_inverseSectionJetEval
    (branch n : ℕ) (P : MvPolynomial (Fin (n + 2)) ℂ) :
    meromorphicOrderAt (gammaFactorialJetEval branch n P) 0 =
      meromorphicOrderAt
        (inverseSectionJetEval (gammaPoleSimpleZeroSection branch) n P) 0 := by
  exact meromorphicOrderAt_congr
    (gammaFactorialJetEval_eventuallyEq_inverseSectionJetEval branch n P)

/-- **Actual homogeneous Gamma-pole order law.**  The cofinal order
`-(D+E)` is realized by the genuine factorially normalized Gamma jets, not
only by the reciprocal-section model. -/
theorem exists_cofinal_meromorphicOrderAt_gammaFactorialJetEval
    {n D : ℕ} {P : MvPolynomial (Fin (n + 2)) ℂ}
    (hP : P.IsHomogeneous D) (hP0 : P ≠ 0) (B : ℕ) :
    ∃ branch : ℕ, B ≤ branch ∧
      meromorphicOrderAt (gammaFactorialJetEval branch n P) 0 =
        ((-((D + (reciprocalBellCovariantTransform n P).totalDegree : ℕ) : ℤ) : ℤ) :
          WithTop ℤ) := by
  obtain ⟨branch, hbranch, horder⟩ :=
    exists_cofinal_meromorphicOrderAt_inverseSectionJetEval_gammaPole hP hP0 B
  refine ⟨branch, hbranch, ?_⟩
  rw [meromorphicOrderAt_gammaFactorialJetEval_eq_inverseSectionJetEval]
  exact horder

/-- Uniform pole cutoff over the complete factorial Gamma-pole tower. -/
def GammaFactorialJetTowerPoleCutoff (n r : ℕ)
    (P : MvPolynomial (Fin (n + 2)) ℂ) : Prop :=
  ∀ branch : ℕ, ((-(r : ℤ) : ℤ) : WithTop ℤ) ≤
    meromorphicOrderAt (gammaFactorialJetEval branch n P) 0

/-- The reciprocal-Bell degree gives a valid pole bound on every branch,
including branches where its top residue happens to vanish. -/
theorem neg_add_reciprocalBellDegree_le_meromorphicOrderAt_gammaFactorialJetEval
    (branch : ℕ) {n D : ℕ} {P : MvPolynomial (Fin (n + 2)) ℂ}
    (hP : P.IsHomogeneous D) :
    ((-((D + (reciprocalBellCovariantTransform n P).totalDegree : ℕ) : ℤ) : ℤ) :
        WithTop ℤ) ≤
      meromorphicOrderAt (gammaFactorialJetEval branch n P) 0 := by
  let Q := reciprocalBellCovariantTransform n P
  have hS := analyticAt_gammaPoleSimpleZeroSection_zero branch
  have hInv : MeromorphicAt
      (fun x => (gammaPoleSimpleZeroSection branch x)⁻¹) 0 :=
    hS.meromorphicAt.inv
  have hCov := meromorphicAt_gammaSimpleZeroCovariantEval branch n Q
  have hQbound : ((-(Q.totalDegree : ℤ) : ℤ) : WithTop ℤ) ≤
      meromorphicOrderAt (gammaSimpleZeroCovariantEval branch n Q) 0 :=
    (gammaSimpleZeroCovariantTowerPoleCutoff_iff Q).mpr le_rfl branch
  rw [meromorphicOrderAt_gammaFactorialJetEval_eq_inverseSectionJetEval]
  rw [meromorphicOrderAt_congr
    (inverseSectionJetEval_gammaPole_eventuallyEq_covariant branch hP)]
  change _ ≤ meromorphicOrderAt
      (((fun x => (gammaPoleSimpleZeroSection branch x)⁻¹) ^ D) *
        gammaSimpleZeroCovariantEval branch n Q) 0
  rw [meromorphicOrderAt_mul (hInv.pow D) hCov,
    meromorphicOrderAt_pow hInv,
    meromorphicOrderAt_inv_gammaPoleSimpleZeroSection branch]
  have hD : (D : WithTop ℤ) * ((-1 : ℤ) : WithTop ℤ) =
      -(D : WithTop ℤ) := by
    change (((D : ℤ) * (-1 : ℤ) : ℤ) : WithTop ℤ) =
      ((-(D : ℤ) : ℤ) : WithTop ℤ)
    rw [mul_neg_one]
  rw [hD]
  calc
    ((-((D + (reciprocalBellCovariantTransform n P).totalDegree : ℕ) : ℤ) : ℤ) :
        WithTop ℤ) =
        ((-(D : ℤ) : ℤ) : WithTop ℤ) +
          ((-(Q.totalDegree : ℤ) : ℤ) : WithTop ℤ) := by
            norm_num [Q]
            rw [add_comm]
    _ ≤ ((-(D : ℤ) : ℤ) : WithTop ℤ) +
          meromorphicOrderAt (gammaSimpleZeroCovariantEval branch n Q) 0 :=
      by simpa [add_comm] using
        (add_le_add_right hQbound (((-(D : ℤ) : ℤ) : WithTop ℤ)))

/-- **Homogeneous Gamma-pole Fock filtration.**  The exact pole cutoff of a
nonzero homogeneous factorial Gamma packet is the sum of particle degree and
reciprocal-Bell covariant degree. -/
theorem gammaFactorialJetTowerPoleCutoff_iff
    {n r D : ℕ} {P : MvPolynomial (Fin (n + 2)) ℂ}
    (hP : P.IsHomogeneous D) (hP0 : P ≠ 0) :
    GammaFactorialJetTowerPoleCutoff n r P ↔
      D + (reciprocalBellCovariantTransform n P).totalDegree ≤ r := by
  constructor
  · intro hcut
    obtain ⟨branch, _, horder⟩ :=
      exists_cofinal_meromorphicOrderAt_gammaFactorialJetEval hP hP0 0
    have hbound := hcut branch
    rw [horder] at hbound
    have hboundInt : -(r : ℤ) ≤
        -((D + (reciprocalBellCovariantTransform n P).totalDegree : ℕ) : ℤ) := by
      exact_mod_cast hbound
    have hdegreeInt :
        (D + (reciprocalBellCovariantTransform n P).totalDegree : ℤ) ≤ r := by
      omega
    exact_mod_cast hdegreeInt
  · intro hdegree branch
    have hcutInt : -(r : ℤ) ≤
        -((D + (reciprocalBellCovariantTransform n P).totalDegree : ℕ) : ℤ) := by
      omega
    have hcut : ((-(r : ℤ) : ℤ) : WithTop ℤ) ≤
        ((-((D + (reciprocalBellCovariantTransform n P).totalDegree : ℕ) : ℤ) : ℤ) :
          WithTop ℤ) := by
      exact_mod_cast hcutInt
    exact hcut.trans
      (neg_add_reciprocalBellDegree_le_meromorphicOrderAt_gammaFactorialJetEval
        branch hP)

def GammaFactorialJetTowerAtMostSimple (n : ℕ)
    (P : MvPolynomial (Fin (n + 2)) ℂ) : Prop :=
  GammaFactorialJetTowerPoleCutoff n 1 P

/-- A nonzero homogeneous factorial Gamma packet has at most simple poles on
the whole tower exactly when its particle-plus-reciprocal-Bell degree is at
most one. -/
theorem gammaFactorialJetTowerAtMostSimple_iff
    {n D : ℕ} {P : MvPolynomial (Fin (n + 2)) ℂ}
    (hP : P.IsHomogeneous D) (hP0 : P ≠ 0) :
    GammaFactorialJetTowerAtMostSimple n P ↔
      D + (reciprocalBellCovariantTransform n P).totalDegree ≤ 1 := by
  exact gammaFactorialJetTowerPoleCutoff_iff hP hP0

/-- Constant-coefficient Gamma jet evaluation in the original `z`
derivative coordinate, viewed along a normalized pole chart. -/
def gammaAffineJetEval (branch n : ℕ)
    (P : MvPolynomial (Fin (n + 2)) ℂ) (x : ℂ) : ℂ :=
  MvPolynomial.eval
    (fun j : Fin (n + 2) => iteratedDeriv (j : ℕ) Complex.Gamma
      (-(branch : ℂ) + reciprocalGammaFactorialScale branch * x)) P

/-- A derivative-weight homogeneous source acquires one common factorial
scale when transported from native `z` derivatives to local-coordinate
derivatives. -/
theorem gammaFactorialJetEval_eq_scale_mul_gammaAffineJetEval
    (branch n : ℕ) {W : ℕ} {P : MvPolynomial (Fin (n + 2)) ℂ}
    (hW : MvPolynomial.IsWeightedHomogeneous
      (fun j : Fin (n + 2) => (j : ℕ)) P W) :
    gammaFactorialJetEval branch n P =
      fun x => reciprocalGammaFactorialScale branch ^ W *
        gammaAffineJetEval branch n P x := by
  funext x
  have hscale := isWeightedHomogeneous_eval₂_scale hW (RingHom.id ℂ)
    (fun j : Fin (n + 2) => iteratedDeriv (j : ℕ) Complex.Gamma
      (-(branch : ℂ) + reciprocalGammaFactorialScale branch * x))
    (reciprocalGammaFactorialScale branch)
  change MvPolynomial.eval
      (fun j : Fin (n + 2) =>
        iteratedDeriv (j : ℕ) (factorialBlowUpZoom Complex.Gamma branch) x) P = _
  rw [show MvPolynomial.eval
      (fun j : Fin (n + 2) =>
        iteratedDeriv (j : ℕ) (factorialBlowUpZoom Complex.Gamma branch) x) P =
      MvPolynomial.eval₂ (RingHom.id ℂ)
        (fun j : Fin (n + 2) =>
          reciprocalGammaFactorialScale branch ^ (j : ℕ) *
            iteratedDeriv (j : ℕ) Complex.Gamma
              (-(branch : ℂ) + reciprocalGammaFactorialScale branch * x)) P by
    apply congrArg (fun v : Fin (n + 2) → ℂ => MvPolynomial.eval v P)
    funext j
    exact iteratedDeriv_factorialBlowUpZoom Complex.Gamma branch (j : ℕ) x]
  rw [hscale]
  rfl

/-- Factorial scaling does not change meromorphic order within a fixed
derivative-weight sector. -/
theorem meromorphicOrderAt_gammaFactorialJetEval_eq_gammaAffineJetEval
    (branch n : ℕ) {W : ℕ} {P : MvPolynomial (Fin (n + 2)) ℂ}
    (hW : MvPolynomial.IsWeightedHomogeneous
      (fun j : Fin (n + 2) => (j : ℕ)) P W) :
    meromorphicOrderAt (gammaFactorialJetEval branch n P) 0 =
      meromorphicOrderAt (gammaAffineJetEval branch n P) 0 := by
  rw [gammaFactorialJetEval_eq_scale_mul_gammaAffineJetEval branch n hW]
  change meromorphicOrderAt
      ((fun _ : ℂ => reciprocalGammaFactorialScale branch ^ W) *
        gammaAffineJetEval branch n P) 0 = _
  rw [meromorphicOrderAt_mul_of_ne_zero analyticAt_const
    (pow_ne_zero W (reciprocalGammaFactorialScale_ne_zero branch))]

/-- Uniform pole cutoff for a constant-coefficient native Gamma-jet sector. -/
def GammaAffineJetTowerPoleCutoff (n r : ℕ)
    (P : MvPolynomial (Fin (n + 2)) ℂ) : Prop :=
  ∀ branch : ℕ, ((-(r : ℤ) : ℤ) : WithTop ℤ) ≤
    meromorphicOrderAt (gammaAffineJetEval branch n P) 0

/-- **Native bihomogeneous Gamma-pole filtration.**  For a source with fixed
particle degree and derivative weight, returning to native `z` derivatives
does not alter the exact `D+E` cutoff law. -/
theorem gammaAffineJetTowerPoleCutoff_iff
    {n r D W : ℕ} {P : MvPolynomial (Fin (n + 2)) ℂ}
    (hD : P.IsHomogeneous D)
    (hW : MvPolynomial.IsWeightedHomogeneous
      (fun j : Fin (n + 2) => (j : ℕ)) P W)
    (hP0 : P ≠ 0) :
    GammaAffineJetTowerPoleCutoff n r P ↔
      D + (reciprocalBellCovariantTransform n P).totalDegree ≤ r := by
  have hpred : GammaAffineJetTowerPoleCutoff n r P ↔
      GammaFactorialJetTowerPoleCutoff n r P := by
    constructor <;> intro h branch
    · rw [meromorphicOrderAt_gammaFactorialJetEval_eq_gammaAffineJetEval
        branch n hW]
      exact h branch
    · rw [← meromorphicOrderAt_gammaFactorialJetEval_eq_gammaAffineJetEval
        branch n hW]
      exact h branch
  rw [hpred]
  exact gammaFactorialJetTowerPoleCutoff_iff hD hP0

def GammaAffineJetTowerAtMostSimple (n : ℕ)
    (P : MvPolynomial (Fin (n + 2)) ℂ) : Prop :=
  GammaAffineJetTowerPoleCutoff n 1 P

theorem gammaAffineJetTowerAtMostSimple_iff
    {n D W : ℕ} {P : MvPolynomial (Fin (n + 2)) ℂ}
    (hD : P.IsHomogeneous D)
    (hW : MvPolynomial.IsWeightedHomogeneous
      (fun j : Fin (n + 2) => (j : ℕ)) P W)
    (hP0 : P ≠ 0) :
    GammaAffineJetTowerAtMostSimple n P ↔
      D + (reciprocalBellCovariantTransform n P).totalDegree ≤ 1 := by
  exact gammaAffineJetTowerPoleCutoff_iff hD hW hP0

/-- The raw logarithmic-jet order law occurs cofinally, with the exact order
read after the inverse Bell coordinate change. -/
theorem exists_cofinal_meromorphicOrderAt_gammaSimpleZeroRawJetEval
    {n : ℕ} {P : MvPolynomial (Fin (n + 1)) ℂ} (hP : P ≠ 0) (B : ℕ) :
    ∃ branch : ℕ, B ≤ branch ∧
      meromorphicOrderAt (gammaSimpleZeroRawJetEval branch n P) 0 =
        ((-(((HTGeometry.bellCoefficientEquiv n).symm P).totalDegree : ℤ) : ℤ) :
          WithTop ℤ) := by
  let Q := (HTGeometry.bellCoefficientEquiv n).symm P
  have hQ : Q ≠ 0 := by
    simpa [Q] using (HTGeometry.bellCoefficientEquiv n).symm.injective.ne hP
  obtain ⟨branch, hbranch, horder⟩ :=
    exists_cofinal_meromorphicOrderAt_gammaSimpleZeroCovariantEval hQ B
  refine ⟨branch, hbranch, ?_⟩
  rw [meromorphicOrderAt_congr
    (gammaSimpleZeroRawJetEval_eventuallyEq_covariant branch n P)]
  simpa [Q] using horder

/-- The faithful particle-number completion of the reciprocal-Bell transform.
The polynomial variable records the power of the reciprocal section; its
coefficients record the covariant simple-zero observables. -/
def reciprocalBellFockTransform (n : ℕ) :
    MvPolynomial (Fin (n + 2)) ℂ →+*
      Polynomial (MvPolynomial (Fin (n + 1)) ℂ) :=
  MvPolynomial.eval₂Hom
    ((Polynomial.C : MvPolynomial (Fin (n + 1)) ℂ →+*
      Polynomial (MvPolynomial (Fin (n + 1)) ℂ)).comp MvPolynomial.C)
    (fun j => Polynomial.X *
      Polynomial.C (reciprocalBellCovariantTransform n (MvPolynomial.X j)))

/-- On one particle-number sector, the Fock transform is exactly the
reciprocal-Bell coefficient placed in that particle degree. -/
theorem reciprocalBellFockTransform_eq_of_isHomogeneous
    {n D : ℕ} {P : MvPolynomial (Fin (n + 2)) ℂ}
    (hP : P.IsHomogeneous D) :
    reciprocalBellFockTransform n P =
      Polynomial.X ^ D *
        Polynomial.C (reciprocalBellCovariantTransform n P) := by
  let f : ℂ →+* Polynomial (MvPolynomial (Fin (n + 1)) ℂ) :=
    (Polynomial.C : MvPolynomial (Fin (n + 1)) ℂ →+*
      Polynomial (MvPolynomial (Fin (n + 1)) ℂ)).comp MvPolynomial.C
  let g : Fin (n + 2) → Polynomial (MvPolynomial (Fin (n + 1)) ℂ) :=
    fun j => Polynomial.C
      (reciprocalBellCovariantTransform n (MvPolynomial.X j))
  have hscale := GaloisForLFunctions.isHomogeneous_eval₂_scale hP f g
    (Polynomial.X : Polynomial (MvPolynomial (Fin (n + 1)) ℂ))
  change MvPolynomial.eval₂ f (fun j => Polynomial.X * g j) P = _ at hscale
  change MvPolynomial.eval₂ f (fun j => Polynomial.X * g j) P = _
  rw [hscale]
  congr 1
  let lhs : MvPolynomial (Fin (n + 2)) ℂ →+*
      Polynomial (MvPolynomial (Fin (n + 1)) ℂ) :=
    MvPolynomial.eval₂Hom f g
  let rhs : MvPolynomial (Fin (n + 2)) ℂ →+*
      Polynomial (MvPolynomial (Fin (n + 1)) ℂ) :=
    (Polynomial.C : MvPolynomial (Fin (n + 1)) ℂ →+*
      Polynomial (MvPolynomial (Fin (n + 1)) ℂ)).comp
        (reciprocalBellCovariantTransform n)
  have hlr : lhs = rhs := by
    apply MvPolynomial.ringHom_ext
    · intro c
      simp [lhs, rhs, f, reciprocalBellCovariantTransform, negativeRawJetMap,
        diagonalCoordinateMap, HTGeometry.simpleZeroDehomogenize]
      symm
      apply (HTGeometry.bellCoefficientEquiv n).injective
      rw [RingEquiv.apply_symm_apply, HTGeometry.bellCoefficientEquiv_apply]
      simp [bellCoefficientMap]
    · intro j
      simp [lhs, rhs, g]
  exact RingHom.congr_fun hlr P

/-- The Fock transform is the direct sum of the reciprocal-Bell transforms
of all particle-number sectors. -/
theorem reciprocalBellFockTransform_eq_sum_homogeneousComponent
    (n : ℕ) (P : MvPolynomial (Fin (n + 2)) ℂ) :
    reciprocalBellFockTransform n P =
      ∑ D ∈ Finset.range (P.totalDegree + 1),
        Polynomial.X ^ D * Polynomial.C
          (reciprocalBellCovariantTransform n
            (MvPolynomial.homogeneousComponent D P)) := by
  conv_lhs => rw [← MvPolynomial.sum_homogeneousComponent P]
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro D hD
  exact reciprocalBellFockTransform_eq_of_isHomogeneous
    (MvPolynomial.homogeneousComponent_isHomogeneous D P)

/-- The leading particle coefficient remembers the top homogeneous source
sector without loss. -/
theorem reciprocalBellFockTransform_coeff_totalDegree
    (n : ℕ) (P : MvPolynomial (Fin (n + 2)) ℂ) :
    (reciprocalBellFockTransform n P).coeff P.totalDegree =
      reciprocalBellCovariantTransform n
        (MvPolynomial.homogeneousComponent P.totalDegree P) := by
  rw [reciprocalBellFockTransform_eq_sum_homogeneousComponent]
  rw [Polynomial.finsetSum_coeff]
  rw [Finset.sum_eq_single P.totalDegree]
  · rw [mul_comm, Polynomial.coeff_C_mul_X_pow]
    simp
  · intro D hD hne
    have hlt : D < P.totalDegree := by
      have hle : D ≤ P.totalDegree := by
        simpa using Nat.le_of_lt_succ (Finset.mem_range.mp hD)
      exact lt_of_le_of_ne hle hne
    rw [mul_comm, Polynomial.coeff_C_mul_X_pow]
    simp [ne_of_gt hlt]
  · simp

/-- Particle completion restores the information lost by dehomogenization:
the reciprocal-Bell Fock transform is injective on every finite jet ring. -/
theorem reciprocalBellFockTransform_injective (n : ℕ) :
    Function.Injective (reciprocalBellFockTransform n) := by
  intro P Q hPQ
  have hzero : reciprocalBellFockTransform n (P - Q) = 0 := by
    rw [map_sub, hPQ, sub_self]
  by_contra hne
  have hsubne : P - Q ≠ 0 := by
    intro hsub
    exact hne (sub_eq_zero.mp hsub)
  have htop : MvPolynomial.homogeneousComponent (P - Q).totalDegree (P - Q) ≠ 0 :=
    HTGeometry.homogeneousComponent_totalDegree_ne_zero hsubne
  have htrans : reciprocalBellCovariantTransform n
      (MvPolynomial.homogeneousComponent (P - Q).totalDegree (P - Q)) ≠ 0 :=
    reciprocalBellCovariantTransform_ne_zero_of_isHomogeneous
      (MvPolynomial.homogeneousComponent_isHomogeneous (P - Q).totalDegree (P - Q))
      htop
  apply htrans
  rw [← reciprocalBellFockTransform_coeff_totalDegree n (P - Q), hzero]
  rfl

/-- **General reciprocal-Bell Fock value law.** Every finite polynomial in
the jets of an inverse analytic section is the evaluation of one faithful
particle/covariant polynomial.  This simultaneously contains all homogeneous
factorizations and retains their cross-sector addition law. -/
theorem inverseSectionJetEval_eq_reciprocalBellFock
    {S : ℂ → ℂ} {x : ℂ} (hS : AnalyticAt ℂ S x) (hS0 : S x ≠ 0)
    (n : ℕ) (P : MvPolynomial (Fin (n + 2)) ℂ) :
    inverseSectionJetEval S n P x =
      Polynomial.eval₂
        (MvPolynomial.eval
          (fun j : Fin (n + 1) =>
            iteratedDeriv ((j : ℕ) + 1) S x / S x))
        (S x)⁻¹ (reciprocalBellFockTransform n P) := by
  let lhs : MvPolynomial (Fin (n + 2)) ℂ →+* ℂ :=
    MvPolynomial.eval₂Hom (RingHom.id ℂ)
      (fun j => iteratedDeriv (j : ℕ) (fun z => (S z)⁻¹) x)
  let coeffEval : MvPolynomial (Fin (n + 1)) ℂ →+* ℂ :=
    MvPolynomial.eval
      (fun j : Fin (n + 1) =>
        iteratedDeriv ((j : ℕ) + 1) S x / S x)
  let rhs : MvPolynomial (Fin (n + 2)) ℂ →+* ℂ :=
    (Polynomial.eval₂RingHom coeffEval (S x)⁻¹).comp
      (reciprocalBellFockTransform n)
  have hlr : lhs = rhs := by
    apply MvPolynomial.ringHom_ext
    · intro c
      simp [lhs, rhs, coeffEval, reciprocalBellFockTransform]
    · intro j
      have hX := inverseSectionJetEval_eq_covariant hS hS0
        (MvPolynomial.isHomogeneous_X (R := ℂ) j)
      simpa [lhs, rhs, coeffEval, reciprocalBellFockTransform,
        inverseSectionJetEval, simpleZeroCovariantSectionEval] using
          hX.trans (mul_comm _ _)
  exact RingHom.congr_fun hlr P

/-- On every normalized Gamma pole chart the general Fock value law has no
remaining analyticity or nonvanishing hypotheses. -/
theorem inverseSectionJetEval_gammaPole_eventuallyEq_reciprocalBellFock
    (branch n : ℕ) (P : MvPolynomial (Fin (n + 2)) ℂ) :
    inverseSectionJetEval (gammaPoleSimpleZeroSection branch) n P =ᶠ[𝓝[≠] 0]
      (fun x => Polynomial.eval₂
        (MvPolynomial.eval
          (fun j : Fin (n + 1) =>
            iteratedDeriv ((j : ℕ) + 1)
              (gammaPoleSimpleZeroSection branch) x /
                gammaPoleSimpleZeroSection branch x))
        (gammaPoleSimpleZeroSection branch x)⁻¹
        (reciprocalBellFockTransform n P)) := by
  have hS := analyticAt_gammaPoleSimpleZeroSection_zero branch
  have hSan : ∀ᶠ x : ℂ in 𝓝[≠] 0,
      AnalyticAt ℂ (gammaPoleSimpleZeroSection branch) x :=
    nhdsWithin_le_nhds hS.eventually_analyticAt
  filter_upwards [hSan, gammaPoleSimpleZeroSection_eventually_ne_zero branch]
      with x hSx hSx0
  exact inverseSectionJetEval_eq_reciprocalBellFock hSx hSx0 n P

/-- The reciprocal Gamma section has normalized residue `-1` at every
factorially scaled pole. -/
theorem tendsto_scale_inv_gammaPoleSimpleZeroSection (branch : ℕ) :
    Tendsto
      (fun x : ℂ => x * (gammaPoleSimpleZeroSection branch x)⁻¹)
      (𝓝[≠] 0) (𝓝 (-1 : ℂ)) := by
  have hUan := gammaPoleRegularUnit_analyticAt_zero branch
  have hUne : ∀ᶠ x : ℂ in 𝓝[≠] 0,
      gammaPoleRegularUnit branch x ≠ 0 :=
    nhdsWithin_le_nhds (hUan.continuousAt.eventually_ne (by
      rw [gammaPoleRegularUnit_zero]
      exact one_ne_zero))
  have hev :
      (fun x : ℂ => x * (gammaPoleSimpleZeroSection branch x)⁻¹) =ᶠ[𝓝[≠] 0]
        (fun x => -gammaPoleRegularUnit branch x) := by
    filter_upwards [self_mem_nhdsWithin, hUne] with x hx hUx
    have hx0 : x ≠ 0 := by simpa using hx
    simp only [gammaPoleSimpleZeroSection]
    field_simp [hx0, hUx]
  have hlim : Tendsto (fun x => -gammaPoleRegularUnit branch x)
      (𝓝[≠] 0) (𝓝 (-1 : ℂ)) := by
    simpa [gammaPoleRegularUnit_zero] using
      hUan.continuousAt.neg.tendsto.mono_left inf_le_left
  exact hlim.congr' hev.symm

/-- **Homogeneous reciprocal-Bell top-residue reflection.**  The exact
normalized Laurent residue of a homogeneous factorial Gamma packet is the
top covariant residue of its reciprocal-Bell transform, multiplied only by
the universal particle sign.  This makes the value hidden behind the
cofinal order theorem explicit. -/
theorem tendsto_pow_add_reciprocalBellDegree_mul_gammaFactorialJetEval
    (branch : ℕ) {n D : ℕ} {P : MvPolynomial (Fin (n + 2)) ℂ}
    (hP : P.IsHomogeneous D) :
    Tendsto
      (fun x : ℂ =>
        x ^ (D + (reciprocalBellCovariantTransform n P).totalDegree) *
          gammaFactorialJetEval branch n P x)
      (𝓝[≠] 0)
      (𝓝 ((-1 : ℂ) ^ D *
        MvPolynomial.eval (gammaSimpleZeroBoundaryResidueValue branch n)
          (MvPolynomial.homogeneousComponent
            (reciprocalBellCovariantTransform n P).totalDegree
            (reciprocalBellCovariantTransform n P)))) := by
  let Q := reciprocalBellCovariantTransform n P
  have hInv := (tendsto_scale_inv_gammaPoleSimpleZeroSection branch).pow D
  have hCov := tendsto_gammaSimpleZeroCovariantEval_topResidue branch n Q
  have hprod := hInv.mul hCov
  apply hprod.congr'
  filter_upwards
      [gammaFactorialJetEval_eventuallyEq_inverseSectionJetEval branch n P,
        inverseSectionJetEval_gammaPole_eventuallyEq_covariant branch hP]
      with x hfactorial hcovariant
  rw [hfactorial, hcovariant]
  dsimp [Q]
  rw [pow_add, mul_pow]
  ring

/-- **Native bihomogeneous top-residue reflection.**  Returning from the
factorial coordinate to native `z` derivatives multiplies the exact
reciprocal-Bell residue by the inverse factorial scale to the derivative
weight, and introduces no further cancellation. -/
theorem tendsto_pow_add_reciprocalBellDegree_mul_gammaAffineJetEval
    (branch : ℕ) {n D W : ℕ} {P : MvPolynomial (Fin (n + 2)) ℂ}
    (hD : P.IsHomogeneous D)
    (hW : MvPolynomial.IsWeightedHomogeneous
      (fun j : Fin (n + 2) => (j : ℕ)) P W) :
    Tendsto
      (fun x : ℂ =>
        x ^ (D + (reciprocalBellCovariantTransform n P).totalDegree) *
          gammaAffineJetEval branch n P x)
      (𝓝[≠] 0)
      (𝓝 ((reciprocalGammaFactorialScale branch)⁻¹ ^ W *
        ((-1 : ℂ) ^ D *
          MvPolynomial.eval (gammaSimpleZeroBoundaryResidueValue branch n)
            (MvPolynomial.homogeneousComponent
              (reciprocalBellCovariantTransform n P).totalDegree
              (reciprocalBellCovariantTransform n P))))) := by
  have hlim :=
    (tendsto_pow_add_reciprocalBellDegree_mul_gammaFactorialJetEval branch hD).const_mul
      ((reciprocalGammaFactorialScale branch)⁻¹ ^ W)
  apply hlim.congr'
  apply Filter.Eventually.of_forall
  intro x
  have hscale := congrFun
    (gammaFactorialJetEval_eq_scale_mul_gammaAffineJetEval branch n hW) x
  have hs := reciprocalGammaFactorialScale_ne_zero branch
  change (reciprocalGammaFactorialScale branch)⁻¹ ^ W *
      (x ^ (D + (reciprocalBellCovariantTransform n P).totalDegree) *
        gammaFactorialJetEval branch n P x) =
    x ^ (D + (reciprocalBellCovariantTransform n P).totalDegree) *
      gammaAffineJetEval branch n P x
  rw [hscale]
  have hcancel : (reciprocalGammaFactorialScale branch)⁻¹ ^ W *
      reciprocalGammaFactorialScale branch ^ W = 1 := by
    rw [← mul_pow, inv_mul_cancel₀ hs, one_pow]
  calc
    (reciprocalGammaFactorialScale branch)⁻¹ ^ W *
          (x ^ (D + (reciprocalBellCovariantTransform n P).totalDegree) *
            (reciprocalGammaFactorialScale branch ^ W *
              gammaAffineJetEval branch n P x)) =
        ((reciprocalGammaFactorialScale branch)⁻¹ ^ W *
          reciprocalGammaFactorialScale branch ^ W) *
            (x ^ (D + (reciprocalBellCovariantTransform n P).totalDegree) *
              gammaAffineJetEval branch n P x) := by ring
    _ = _ := by rw [hcancel, one_mul]

@[simp] theorem reciprocalBellCovariantTransform_C
    (n : ℕ) (c : ℂ) :
    reciprocalBellCovariantTransform n (MvPolynomial.C c) = MvPolynomial.C c := by
  simp [reciprocalBellCovariantTransform, negativeRawJetMap,
    diagonalCoordinateMap, HTGeometry.simpleZeroDehomogenize]
  apply (HTGeometry.bellCoefficientEquiv n).injective
  rw [RingEquiv.apply_symm_apply, HTGeometry.bellCoefficientEquiv_apply]
  simp [bellCoefficientMap]

@[simp] theorem reciprocalBellCovariantTransform_X_zero (n : ℕ) :
    reciprocalBellCovariantTransform n
      (MvPolynomial.X (0 : Fin (n + 2))) = 1 := by
  simp [reciprocalBellCovariantTransform, negativeRawJetMap,
    diagonalCoordinateMap, HTGeometry.simpleZeroDehomogenize,
    HTGeometry.simpleZeroBoundaryResidue]

/-- **Homogeneous source classification at the simple-pole horizon.**  A
nonzero homogeneous factorial Gamma packet has at most simple poles on the
entire tower exactly when it is a scalar or a scalar multiple of the
undifferentiated Gamma carrier. -/
theorem gammaFactorialJetTowerAtMostSimple_iff_constant_or_undifferentiated
    {n D : ℕ} {P : MvPolynomial (Fin (n + 2)) ℂ}
    (hP : P.IsHomogeneous D) (hP0 : P ≠ 0) :
    GammaFactorialJetTowerAtMostSimple n P ↔
      ∃ c : ℂ, P = MvPolynomial.C c ∨
        P = MvPolynomial.C c * MvPolynomial.X (0 : Fin (n + 2)) := by
  constructor
  · intro hcut
    have hdegree := (gammaFactorialJetTowerAtMostSimple_iff hP hP0).mp hcut
    have hDle : D ≤ 1 := by omega
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hDle with hD | hD
    · subst D
      exact ⟨P.coeff 0, Or.inl (HTGeometry.isHomogeneous_zero_eq_C_coeff_zero hP)⟩
    · subst D
      let Q := reciprocalBellCovariantTransform n P
      have hQdegree : Q.totalDegree = 0 := by
        dsimp [Q]
        omega
      have hQeq : Q = MvPolynomial.C (Q.coeff 0) :=
        MvPolynomial.totalDegree_eq_zero_iff_eq_C.mp hQdegree
      refine ⟨Q.coeff 0, Or.inr ?_⟩
      apply reciprocalBellFockTransform_injective n
      rw [reciprocalBellFockTransform_eq_of_isHomogeneous hP,
        reciprocalBellFockTransform_eq_of_isHomogeneous
          (MvPolynomial.isHomogeneous_C_mul_X (Q.coeff 0) (0 : Fin (n + 2)))]
      simp only [pow_one]
      change Polynomial.X * Polynomial.C Q =
        Polynomial.X * Polynomial.C
          (reciprocalBellCovariantTransform n
            (MvPolynomial.C (Q.coeff 0) * MvPolynomial.X (0 : Fin (n + 2))))
      rw [hQeq, map_mul, reciprocalBellCovariantTransform_C,
        reciprocalBellCovariantTransform_X_zero, mul_one]
      simp
  · rintro ⟨c, hc | hc⟩
    · subst P
      have hc0 : c ≠ 0 := by
        intro hzero
        subst c
        exact hP0 (by simp)
      apply (gammaFactorialJetTowerAtMostSimple_iff
        (MvPolynomial.isHomogeneous_C (σ := Fin (n + 2)) c)
        (by simpa using hc0)).mpr
      simp
    · subst P
      have hc0 : c ≠ 0 := by
        intro hzero
        subst c
        exact hP0 (by simp)
      apply (gammaFactorialJetTowerAtMostSimple_iff
        (MvPolynomial.isHomogeneous_C_mul_X c (0 : Fin (n + 2)))
        (mul_ne_zero (MvPolynomial.C_ne_zero.mpr hc0)
          (MvPolynomial.X_ne_zero (R := ℂ) (0 : Fin (n + 2))))).mpr
      simp

/-- The same source-level classification holds in native `z` derivatives
for every fixed derivative-weight sector. -/
theorem gammaAffineJetTowerAtMostSimple_iff_constant_or_undifferentiated
    {n D W : ℕ} {P : MvPolynomial (Fin (n + 2)) ℂ}
    (hD : P.IsHomogeneous D)
    (hW : MvPolynomial.IsWeightedHomogeneous
      (fun j : Fin (n + 2) => (j : ℕ)) P W)
    (hP0 : P ≠ 0) :
    GammaAffineJetTowerAtMostSimple n P ↔
      ∃ c : ℂ, P = MvPolynomial.C c ∨
        P = MvPolynomial.C c * MvPolynomial.X (0 : Fin (n + 2)) := by
  rw [gammaAffineJetTowerAtMostSimple_iff hD hW hP0,
    ← gammaFactorialJetTowerAtMostSimple_iff hD hP0,
    gammaFactorialJetTowerAtMostSimple_iff_constant_or_undifferentiated hD hP0]

end

end GaloisForLFunctions
