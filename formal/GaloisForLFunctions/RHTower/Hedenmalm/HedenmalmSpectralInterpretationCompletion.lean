import GaloisForLFunctions.RHTower.XiHedenmalmBoundaryValueProblem
import GaloisForLFunctions.RHTower.Hedenmalm.HedenmalmThetaSourceUnconditional
import GaloisForLFunctions.HTGeometry.HermitianWittEigenvalueReality

/-!
# Completion of Hedenmalm's spectral-interpretation theorem surface

This module closes the two literal pieces of Hedenmalm's 2026 paper
`Spectral interpretation of Riemann zeta zeros` (`arXiv:2606.17494`) that were not represented
by the normalized boundary-value module.

* Theorems 3.3.1 and 3.3.3 classify the full, unnormalized one-dimensional solution space.  A
  solution with source amplitude `c` is exactly `c * u_alpha`, and the second endpoint holds
  exactly when `c * XiC(alpha) = 0`.
* Theorem 4.2.2 is the algebraic consequence of formal self-adjointness of the operator pair
  `(LD, L)`: nonreal modes are null and distinct real modes are orthogonal after applying `L`.

The module deliberately does not assert the paper's missing premise: a positive source-derived
Hilbert form that makes the concrete Hedenmalm pair self-adjoint on the full eigenfunction domain.
That remains the genuine RH-bearing wall.
-/

open Complex Real MeasureTheory Set Filter Topology
open scoped ComplexConjugate

noncomputable section

namespace RHTower

open GaloisForLFunctions.HTGeometry

/-! ## The complete boundary solution space -/

/-- Hedenmalm's first-order boundary equation with arbitrary source amplitude. -/
def XiHedenmalmBoundaryEquationWithAmplitude (alpha c : ℂ) (u : ℝ → ℂ) : Prop :=
  ∀ x : ℝ, HasDerivAt u
    (-I * alpha * u x + c * (thetaCuspFullSource x : ℂ)) x

/-- The amplitude-parametrized Hedenmalm boundary problem. -/
def XiHedenmalmBoundaryValueProblemWithAmplitude (alpha c : ℂ) (u : ℝ → ℂ) : Prop :=
  XiHedenmalmBoundaryEquationWithAmplitude alpha c u ∧
    Tendsto (xiHedenmalmWeightedBoundaryGauge alpha u) atBot (𝓝 0) ∧
    Tendsto (xiHedenmalmWeightedBoundaryGauge alpha u) atTop (𝓝 0)

theorem xiHedenmalmWeightedBoundaryGauge_eigen_smul
    (alpha c : ℂ) :
    xiHedenmalmWeightedBoundaryGauge alpha
      (fun x => c * xiHedenmalmBoundaryEigenfunction alpha x) =
      fun x => c * xiHedenmalmBoundaryGauge alpha x := by
  funext x
  simp only [xiHedenmalmWeightedBoundaryGauge, xiHedenmalmBoundaryGauge]
  ring

theorem xiHedenmalmWeightedBoundaryGauge_add
    (alpha : ℂ) (u v : ℝ → ℂ) :
    xiHedenmalmWeightedBoundaryGauge alpha (fun x => u x + v x) =
      fun x => xiHedenmalmWeightedBoundaryGauge alpha u x +
        xiHedenmalmWeightedBoundaryGauge alpha v x := by
  funext x
  simp only [xiHedenmalmWeightedBoundaryGauge]
  ring

theorem xiHedenmalmBoundaryEigenfunction_smul_satisfies_equation
    {alpha c : ℂ} (hstrip : |alpha.im| < 1) :
    XiHedenmalmBoundaryEquationWithAmplitude alpha c
      (fun x => c * xiHedenmalmBoundaryEigenfunction alpha x) := by
  intro x
  have h := (hasDerivAt_xiHedenmalmBoundaryEigenfunction hstrip x).const_mul c
  exact h.congr_deriv (by ring)

theorem tendsto_xiHedenmalmBoundaryEigenfunction_smul_gauge_atBot
    (alpha c : ℂ) :
    Tendsto
      (xiHedenmalmWeightedBoundaryGauge alpha
        (fun x => c * xiHedenmalmBoundaryEigenfunction alpha x))
      atBot (𝓝 0) := by
  have hconst : Tendsto (fun _ : ℝ => c) atBot (𝓝 c) := tendsto_const_nhds
  have hbase := tendsto_xiHedenmalmBoundaryGauge_atBot (alpha := alpha)
  have hmul : Tendsto (fun x : ℝ => c * xiHedenmalmBoundaryGauge alpha x)
      atBot (𝓝 (c * 0)) := hconst.mul hbase
  rw [xiHedenmalmWeightedBoundaryGauge_eigen_smul]
  simpa using hmul

theorem xiHedenmalmBoundaryEquationWithAmplitude_unique_of_atBot
    {alpha c : ℂ} (hstrip : |alpha.im| < 1) {u : ℝ → ℂ}
    (hu : XiHedenmalmBoundaryEquationWithAmplitude alpha c u)
    (huBot : Tendsto (xiHedenmalmWeightedBoundaryGauge alpha u) atBot (𝓝 0)) :
    u = fun x => c * xiHedenmalmBoundaryEigenfunction alpha x := by
  let w : ℝ → ℂ := fun x => u x + (1 - c) * xiHedenmalmBoundaryEigenfunction alpha x
  have hw : XiHedenmalmBoundaryEquation alpha w := by
    intro x
    have h := (hu x).add
      ((hasDerivAt_xiHedenmalmBoundaryEigenfunction hstrip x).const_mul (1 - c))
    change HasDerivAt (fun y : ℝ => u y + (1 - c) * xiHedenmalmBoundaryEigenfunction alpha y)
      _ x
    exact h.congr_deriv (by ring)
  have hscaled : Tendsto
      (xiHedenmalmWeightedBoundaryGauge alpha
        (fun x => (1 - c) * xiHedenmalmBoundaryEigenfunction alpha x))
      atBot (𝓝 0) :=
    tendsto_xiHedenmalmBoundaryEigenfunction_smul_gauge_atBot alpha (1 - c)
  have hwBot : Tendsto (xiHedenmalmWeightedBoundaryGauge alpha w) atBot (𝓝 0) := by
    have hsum := huBot.add hscaled
    change Tendsto
      (xiHedenmalmWeightedBoundaryGauge alpha
        (fun x => u x + (1 - c) * xiHedenmalmBoundaryEigenfunction alpha x)) atBot (𝓝 0)
    rw [xiHedenmalmWeightedBoundaryGauge_add]
    simpa using hsum
  have hwEq := xiHedenmalmBoundaryEquation_unique_of_atBot hstrip hw hwBot
  funext x
  have hx := congrFun hwEq x
  dsimp only [w] at hx
  linear_combination hx

theorem tendsto_xiHedenmalmBoundaryEigenfunction_smul_gauge_atTop_iff
    {alpha c : ℂ} (hstrip : |alpha.im| < 1) :
    Tendsto
      (xiHedenmalmWeightedBoundaryGauge alpha
        (fun x => c * xiHedenmalmBoundaryEigenfunction alpha x))
      atTop (𝓝 0) ↔ c * XiC alpha = 0 := by
  rcases eq_or_ne c 0 with rfl | hc
  · rw [xiHedenmalmWeightedBoundaryGauge_eigen_smul]
    simp
  constructor
  · intro htop
    rw [xiHedenmalmWeightedBoundaryGauge_eigen_smul] at htop
    have hinv : Tendsto
        (fun x : ℝ => c⁻¹ * (c * xiHedenmalmBoundaryGauge alpha x))
        atTop (𝓝 (c⁻¹ * 0)) :=
      (tendsto_const_nhds.mul htop)
    have hbase : Tendsto (xiHedenmalmBoundaryGauge alpha) atTop (𝓝 0) := by
      have heq : (fun x : ℝ => c⁻¹ * (c * xiHedenmalmBoundaryGauge alpha x)) =
          xiHedenmalmBoundaryGauge alpha := by
        funext x
        field_simp
      rw [heq] at hinv
      simpa using hinv
    have hXi : XiC alpha = 0 :=
      (tendsto_xiHedenmalmBoundaryGauge_atTop_iff hstrip).mp hbase
    simp [hXi]
  · intro hproduct
    have hXi : XiC alpha = 0 := (mul_eq_zero.mp hproduct).resolve_left hc
    have hbase : Tendsto (xiHedenmalmBoundaryGauge alpha) atTop (𝓝 0) :=
      (tendsto_xiHedenmalmBoundaryGauge_atTop_iff hstrip).mpr hXi
    have hmul : Tendsto (fun x : ℝ => c * xiHedenmalmBoundaryGauge alpha x)
        atTop (𝓝 (c * 0)) := tendsto_const_nhds.mul hbase
    rw [xiHedenmalmWeightedBoundaryGauge_eigen_smul]
    simpa using hmul

theorem existsUnique_xiHedenmalmBoundaryValueProblemWithAmplitude_iff
    {alpha c : ℂ} (hstrip : |alpha.im| < 1) :
    (∃! u : ℝ → ℂ, XiHedenmalmBoundaryValueProblemWithAmplitude alpha c u) ↔
      c * XiC alpha = 0 := by
  constructor
  · rintro ⟨u, hu, -⟩
    have huEq := xiHedenmalmBoundaryEquationWithAmplitude_unique_of_atBot
      hstrip hu.1 hu.2.1
    have htop : Tendsto
        (xiHedenmalmWeightedBoundaryGauge alpha
          (fun x => c * xiHedenmalmBoundaryEigenfunction alpha x)) atTop (𝓝 0) := by
      simpa only [huEq] using hu.2.2
    exact (tendsto_xiHedenmalmBoundaryEigenfunction_smul_gauge_atTop_iff hstrip).mp htop
  · intro hproduct
    refine ⟨fun x => c * xiHedenmalmBoundaryEigenfunction alpha x, ?_, ?_⟩
    · refine ⟨xiHedenmalmBoundaryEigenfunction_smul_satisfies_equation hstrip,
        tendsto_xiHedenmalmBoundaryEigenfunction_smul_gauge_atBot alpha c, ?_⟩
      exact (tendsto_xiHedenmalmBoundaryEigenfunction_smul_gauge_atTop_iff hstrip).mpr hproduct
    · intro u hu
      exact xiHedenmalmBoundaryEquationWithAmplitude_unique_of_atBot
        hstrip hu.1 hu.2.1

/-- The source-normalized explicit boundary eigenfunction is never the zero function. -/
theorem xiHedenmalmBoundaryEigenfunction_ne_zero
    {alpha : ℂ} (hstrip : |alpha.im| < 1) :
    xiHedenmalmBoundaryEigenfunction alpha ≠ 0 := by
  intro hzero
  have hderiv := hasDerivAt_xiHedenmalmBoundaryEigenfunction hstrip 0
  rw [hzero] at hderiv
  have hconst : HasDerivAt (0 : ℝ → ℂ) 0 0 := hasDerivAt_const (x := 0) (c := (0 : ℂ))
  have hsource : (thetaCuspFullSource 0 : ℂ) = 0 := by
    have hEq : -I * alpha * 0 + (thetaCuspFullSource 0 : ℂ) = 0 := by
      calc
        -I * alpha * 0 + (thetaCuspFullSource 0 : ℂ) = deriv (0 : ℝ → ℂ) 0 :=
          hderiv.deriv.symm
        _ = 0 := hconst.deriv
    simpa using hEq
  exact (Complex.ofReal_ne_zero.mpr (HedenmalmThetaSource.thetaCuspFullSource_pos 0).ne') hsource

/-- The unnormalized boundary problem of Hedenmalm's Theorems 3.3.1 and 3.3.3. -/
def XiHedenmalmFullBoundaryValueProblem (alpha : ℂ) (u : ℝ → ℂ) : Prop :=
  ∃ c : ℂ, XiHedenmalmBoundaryValueProblemWithAmplitude alpha c u

/-- Exact full solution-space classification of the two-ended theta boundary problem. -/
theorem xiHedenmalmFullBoundaryValueProblem_iff
    {alpha : ℂ} (hstrip : |alpha.im| < 1) {u : ℝ → ℂ} :
    XiHedenmalmFullBoundaryValueProblem alpha u ↔
      ∃ c : ℂ, c * XiC alpha = 0 ∧
        u = fun x => c * xiHedenmalmBoundaryEigenfunction alpha x := by
  constructor
  · rintro ⟨c, hu⟩
    refine ⟨c, ?_, xiHedenmalmBoundaryEquationWithAmplitude_unique_of_atBot
      hstrip hu.1 hu.2.1⟩
    have hscaled : Tendsto
        (xiHedenmalmWeightedBoundaryGauge alpha
          (fun x => c * xiHedenmalmBoundaryEigenfunction alpha x)) atTop (𝓝 0) := by
      simpa only [xiHedenmalmBoundaryEquationWithAmplitude_unique_of_atBot
        hstrip hu.1 hu.2.1] using hu.2.2
    exact (tendsto_xiHedenmalmBoundaryEigenfunction_smul_gauge_atTop_iff hstrip).mp hscaled
  · rintro ⟨c, hproduct, rfl⟩
    exact ⟨c, ⟨xiHedenmalmBoundaryEigenfunction_smul_satisfies_equation hstrip,
      tendsto_xiHedenmalmBoundaryEigenfunction_smul_gauge_atBot alpha c,
      (tendsto_xiHedenmalmBoundaryEigenfunction_smul_gauge_atTop_iff hstrip).mpr hproduct⟩⟩

/-- Hedenmalm's literal spectral characterization: a nonzero two-ended boundary solution exists
exactly at a completed Xi zero. -/
theorem exists_nonzero_xiHedenmalmFullBoundaryValueProblem_iff
    {alpha : ℂ} (hstrip : |alpha.im| < 1) :
    (∃ u : ℝ → ℂ, XiHedenmalmFullBoundaryValueProblem alpha u ∧ u ≠ 0) ↔ XiC alpha = 0 := by
  constructor
  · rintro ⟨u, hu, hune⟩
    rcases (xiHedenmalmFullBoundaryValueProblem_iff hstrip).mp hu with ⟨c, hc, huEq⟩
    have hcne : c ≠ 0 := by
      intro hczero
      apply hune
      rw [huEq, hczero]
      exact funext fun x => by simp
    exact (mul_eq_zero.mp hc).resolve_left hcne
  · intro hzero
    refine ⟨xiHedenmalmBoundaryEigenfunction alpha, ?_,
      xiHedenmalmBoundaryEigenfunction_ne_zero hstrip⟩
    apply (xiHedenmalmFullBoundaryValueProblem_iff hstrip).mpr
    exact ⟨1, by simp [hzero], by simp⟩

/-! ## Formal self-adjointness of the operator pair -/

/-- Formal self-adjointness of Hedenmalm's operator pair `(LD, L)` on a sesquilinear carrier. -/
def HedenmalmPairFormallySelfAdjoint {V : Type*} [AddCommGroup V] [Module ℂ V]
    (B : ComplexSesquilinearForm V) (LD L : V →ₗ[ℂ] V) : Prop :=
  ∀ u v, B (LD u) (L v) = B (L u) (LD v)

/-- A generalized eigenmode of Hedenmalm's operator pair `(LD, L)`. -/
def IsHedenmalmPairEigenmode {V : Type*} [AddCommGroup V] [Module ℂ V]
    (LD L : V →ₗ[ℂ] V) (alpha : ℂ) (u : V) : Prop :=
  LD u + alpha • L u = 0

theorem hedenmalmPair_null_of_nonreal_mode
    {V : Type*} [AddCommGroup V] [Module ℂ V]
    (B : ComplexSesquilinearForm V) (LD L : V →ₗ[ℂ] V)
    (hself : HedenmalmPairFormallySelfAdjoint B LD L)
    {alpha : ℂ} {u : V} (hu : IsHedenmalmPairEigenmode LD L alpha u)
    (halpha : alpha ≠ starRingEnd ℂ alpha) :
    B (L u) (L u) = 0 := by
  have hLD : LD u = -(alpha • L u) := eq_neg_of_add_eq_zero_left hu
  have hpair := hself u u
  rw [hLD] at hpair
  simp at hpair
  exact hpair.resolve_left halpha

theorem hedenmalmPair_orthogonal_of_spectral_mismatch
    {V : Type*} [AddCommGroup V] [Module ℂ V]
    (B : ComplexSesquilinearForm V) (LD L : V →ₗ[ℂ] V)
    (hself : HedenmalmPairFormallySelfAdjoint B LD L)
    {alpha beta : ℂ} {u v : V}
    (hu : IsHedenmalmPairEigenmode LD L alpha u)
    (hv : IsHedenmalmPairEigenmode LD L beta v)
    (hspectral : alpha ≠ starRingEnd ℂ beta) :
    B (L u) (L v) = 0 := by
  have hLDu : LD u = -(alpha • L u) := eq_neg_of_add_eq_zero_left hu
  have hLDv : LD v = -(beta • L v) := eq_neg_of_add_eq_zero_left hv
  have hpair := hself u v
  rw [hLDu, hLDv] at hpair
  simp at hpair
  exact hpair.resolve_left hspectral

theorem hedenmalmPair_orthogonal_of_distinct_real_modes
    {V : Type*} [AddCommGroup V] [Module ℂ V]
    (B : ComplexSesquilinearForm V) (LD L : V →ₗ[ℂ] V)
    (hself : HedenmalmPairFormallySelfAdjoint B LD L)
    {alpha beta : ℂ} {u v : V}
    (hu : IsHedenmalmPairEigenmode LD L alpha u)
    (hv : IsHedenmalmPairEigenmode LD L beta v)
    (hbeta : beta.im = 0) (hneq : alpha ≠ beta) :
    B (L u) (L v) = 0 := by
  apply hedenmalmPair_orthogonal_of_spectral_mismatch B LD L hself hu hv
  have hstar : starRingEnd ℂ beta = beta := Complex.conj_eq_iff_im.mpr hbeta
  simpa only [hstar] using hneq

/-- A definite form turns Hedenmalm's conditional self-adjointness premise into spectral reality,
provided the `L`-image of the mode is nonzero. -/
theorem hedenmalmPair_spectral_real_of_definite
    {V : Type*} [AddCommGroup V] [Module ℂ V]
    (B : ComplexSesquilinearForm V) (LD L : V →ₗ[ℂ] V)
    (hself : HedenmalmPairFormallySelfAdjoint B LD L)
    (hdefinite : ∀ w : V, B w w = 0 → w = 0)
    {alpha : ℂ} {u : V} (hu : IsHedenmalmPairEigenmode LD L alpha u)
    (hLu : L u ≠ 0) : alpha = starRingEnd ℂ alpha := by
  by_contra halpha
  exact hLu (hdefinite (L u)
    (hedenmalmPair_null_of_nonreal_mode B LD L hself hu halpha))

end RHTower
