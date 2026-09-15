import GaloisForLFunctions.HTGeometry.InfiniteTorusForwardDensity
import GaloisForLFunctions.HTGeometry.LogPrimeExponentialCarrier
import GaloisForLFunctions.HTGeometry.PoissonFormationCharacterization
import GaloisForLFunctions.HTGeometry.WienerFormationBanach
import Mathlib.Analysis.Normed.Algebra.Spectrum

/-!
# Classical second-quantization applications

Giannakis et al., arXiv:2501.07419, Proposition 11 uses dense torus restrictions to identify Fock
observables.  Here the corpus's prime-frequency Kronecker flow gives a closed infinite-dimensional
instance: any future tail of one scalar time trace determines a continuous observable on the full
prime torus.
-/

noncomputable section

namespace GaloisForLFunctions.HTGeometry

/-- Complex version of coefficient uniqueness for absolutely summable power series on the unit
interval.  This supplies the coefficient-separation step needed by the Fock/Wiener application. -/
theorem eq_zero_of_complex_tsum_pow_eq_zero {d : ℕ → ℂ}
    (habs : Summable fun n => ‖d n‖)
    (hzero : ∀ t : ℝ, 0 < t → t ≤ 1 → ∑' n : ℕ, d n * (t : ℂ) ^ n = 0) :
    ∀ k : ℕ, d k = 0 := by
  have habsRe : Summable fun n => |(d n).re| :=
    Summable.of_nonneg_of_le (fun n => abs_nonneg _)
      (fun n => Complex.abs_re_le_norm (d n)) habs
  have habsIm : Summable fun n => |(d n).im| :=
    Summable.of_nonneg_of_le (fun n => abs_nonneg _)
      (fun n => Complex.abs_im_le_norm (d n)) habs
  have hsum (t : ℝ) (ht : 0 ≤ t) (ht1 : t ≤ 1) :
      Summable fun n : ℕ => d n * (t : ℂ) ^ n := by
    refine Summable.of_norm_bounded habs fun n => ?_
    rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ht]
    exact mul_le_of_le_one_right (norm_nonneg _) (pow_le_one₀ ht ht1)
  have hzeroRe : ∀ t : ℝ, 0 < t → t ≤ 1 → ∑' n : ℕ, (d n).re * t ^ n = 0 := by
    intro t ht ht1
    have hre := congrArg Complex.re (hzero t ht ht1)
    rw [Complex.re_tsum (hsum t ht.le ht1)] at hre
    simpa [← Complex.ofReal_pow] using hre
  have hzeroIm : ∀ t : ℝ, 0 < t → t ≤ 1 → ∑' n : ℕ, (d n).im * t ^ n = 0 := by
    intro t ht ht1
    have him := congrArg Complex.im (hzero t ht ht1)
    rw [Complex.im_tsum (hsum t ht.le ht1)] at him
    simpa [← Complex.ofReal_pow] using him
  have hre := eq_zero_of_tsum_pow_eq_zero habsRe hzeroRe
  have him := eq_zero_of_tsum_pow_eq_zero habsIm hzeroIm
  intro k
  exact Complex.ext (hre k) (him k)

/-- **A forward tail determines every continuous observable.**  This is the torus-restriction
injectivity mechanism of Giannakis et al., arXiv:2501.07419, transferred to the corpus's infinite
Kronecker flow. -/
theorem continuousMap_eq_of_eq_on_forwardTail {ι : Type*} [Countable ι] [DecidableEq ι]
    {omega : ι → ℝ} (h : RationallyIndependentSequence omega) (T₀ : ℝ)
    {f g : C(UnitAddTorus ι, ℂ)}
    (hfg : ∀ t : ℝ, T₀ ≤ t → f (clockPhasePoint omega t) = g (clockPhasePoint omega t)) :
    f = g := by
  have heq : (f : UnitAddTorus ι → ℂ) = g :=
    Continuous.ext_on (dense_forwardOrbit h T₀) f.continuous g.continuous fun x hx => by
    obtain ⟨t, ht, rfl⟩ := hx
    exact hfg t ht
  exact ContinuousMap.coe_injective heq

/-- Observation of a continuous prime-torus observable along a prescribed forward tail. -/
def logPrimeForwardTailObservation (T₀ : ℝ) :
    C(UnitAddTorus ℕ, ℂ) → Set.Ici T₀ → ℂ :=
  fun f t => f (clockPhasePoint logPrimeFrequency t.1)

/-- Closed application: restriction to every forward prime-frequency tail is injective on the
entire continuous-observable algebra. -/
theorem logPrimeForwardTailObservation_injective (T₀ : ℝ) :
    Function.Injective (logPrimeForwardTailObservation T₀) := by
  intro f g hfg
  apply continuousMap_eq_of_eq_on_forwardTail rationallyIndependentSequence_logPrimeFrequency T₀
  intro t ht
  exact congr_fun hfg ⟨t, ht⟩

end GaloisForLFunctions.HTGeometry

namespace HTGeometry.WienerAlgebra

variable {R : ℝ} [hR : Fact (0 < R)]

/-- Closed-disc parameter space for continuous characters of the Wiener/Fock algebra. -/
def CharacterPoint (R : ℝ) := {z : ℂ // ‖z‖ ≤ R}

/-- Evaluation at a closed-disc point as an algebra character. -/
noncomputable def evalCharacter (z : CharacterPoint R) : WienerAlgebra R →ₐ[ℂ] ℂ :=
  wienerScaleEvalHom hR.out.le z.property

/-- Gelfand evaluation of a Wiener/Fock packet on its concrete character space. -/
noncomputable def gelfandEvaluation (f : WienerAlgebra R) : CharacterPoint R → ℂ :=
  fun z => evalCharacter z f

/-- Distinct closed-disc points induce distinct characters. -/
theorem evalCharacter_injective : Function.Injective (evalCharacter (R := R)) := by
  intro z w hzw
  apply Subtype.ext
  apply wienerScaleEval_injective_point
  intro f hf
  have hvalue := DFunLike.congr_fun hzw (⟨f, hf⟩ : WienerAlgebra R)
  exact hvalue

/-- Every algebra character of the Wiener/Fock algebra is evaluation at a closed-disc point. -/
theorem evalCharacter_surjective : Function.Surjective (evalCharacter (R := R)) := by
  intro χ
  obtain ⟨z, hz, hχ⟩ := exists_eval_of_continuous_character χ χ.toContinuousLinearMap.continuous
  refine ⟨⟨z, hz⟩, ?_⟩
  apply AlgHom.ext
  intro f
  exact (hχ f).symm

/-- **Exact character-space classification.**  The closed disc and the character spectrum of the
Wiener/Fock Banach algebra are in bijection. -/
theorem evalCharacter_bijective : Function.Bijective (evalCharacter (R := R)) :=
  ⟨evalCharacter_injective, evalCharacter_surjective⟩

/-- **Gelfand separation for Wiener/Fock packets.**  Values at all receiver characters determine
the entire admitted power series. -/
theorem gelfandEvaluation_injective : Function.Injective (gelfandEvaluation (R := R)) := by
  intro f g hfg
  let d : ℕ → ℂ := weightCoord (f - g)
  have habs : Summable fun n => ‖d n‖ := by
    have h := (f - g).admissible
    change Summable (fun n => wienerScaleWeight R (f - g).toSeries n) at h
    simpa only [d, norm_weightCoord] using h
  have hzero : ∀ t : ℝ, 0 < t → t ≤ 1 → ∑' n : ℕ, d n * (t : ℂ) ^ n = 0 := by
    intro t ht ht1
    have hRt : ‖(((R * t : ℝ) : ℂ))‖ ≤ R := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hR.out.le ht.le)]
      exact (mul_le_mul_of_nonneg_left ht1 hR.out.le).trans_eq (mul_one R)
    let z : CharacterPoint R := ⟨((R * t : ℝ) : ℂ), hRt⟩
    have heq : evalCharacter z f = evalCharacter z g := congrFun hfg z
    have heval : wienerScaleEval (f - g).toSeries z.1 = 0 := by
      change evalCharacter z (f - g) = 0
      rw [map_sub]
      exact sub_eq_zero.mpr heq
    rw [wienerScaleEval] at heval
    rw [← heval]
    apply tsum_congr
    intro n
    simp only [d, weightCoord, z, Complex.ofReal_mul, mul_pow]
    ring
  have hd := GaloisForLFunctions.HTGeometry.eq_zero_of_complex_tsum_pow_eq_zero habs hzero
  apply sub_eq_zero.mp
  apply toSeries_injective
  rw [toSeries_zero]
  apply PowerSeries.ext
  intro n
  have hdn := hd n
  simp only [d, weightCoord, mul_eq_zero] at hdn
  rcases hdn with hn | hRpow
  · exact hn
  · exact absurd hRpow (pow_ne_zero n (Complex.ofReal_ne_zero.mpr hR.out.ne'))

/-- Each character has a unique receiver point in the closed disc. -/
theorem existsUnique_receiver (χ : WienerAlgebra R →ₐ[ℂ] ℂ) :
    ∃! z : CharacterPoint R, evalCharacter z = χ :=
  evalCharacter_bijective.existsUnique χ

/-! ## The lifted circle action -/

/-- Rescaling a Wiener/Fock packet by a unit phase preserves every weighted coefficient norm. -/
theorem wienerScaleWeight_rescale_circle (u : Circle) (f : WienerAlgebra R) :
    wienerScaleWeight R (PowerSeries.rescale (u : ℂ) f.toSeries) =
      wienerScaleWeight R f.toSeries := by
  funext n
  rw [wienerScaleWeight, PowerSeries.coeff_rescale, norm_mul, norm_pow,
    Circle.norm_coe, one_pow, one_mul]
  rfl

/-- Unit-phase rescaling preserves Wiener admissibility. -/
theorem wienerScaleAdmissible_rescale_circle (u : Circle) (f : WienerAlgebra R) :
    WienerScaleAdmissible R (PowerSeries.rescale (u : ℂ) f.toSeries) := by
  rw [WienerScaleAdmissible, wienerScaleWeight_rescale_circle]
  exact f.admissible

/-- The second-quantized circle action: degree `n` receives phase `u^n`. -/
noncomputable def phaseRotationHom (u : Circle) :
    WienerAlgebra R →ₐ[ℂ] WienerAlgebra R where
  toFun f :=
    ⟨PowerSeries.rescale (u : ℂ) f.toSeries, wienerScaleAdmissible_rescale_circle u f⟩
  map_one' := by
    apply Subtype.ext
    exact map_one (PowerSeries.rescale (u : ℂ))
  map_mul' f g := by
    apply Subtype.ext
    exact map_mul (PowerSeries.rescale (u : ℂ)) f.toSeries g.toSeries
  map_zero' := by
    apply Subtype.ext
    exact map_zero (PowerSeries.rescale (u : ℂ))
  map_add' f g := by
    apply Subtype.ext
    exact map_add (PowerSeries.rescale (u : ℂ)) f.toSeries g.toSeries
  commutes' c := by
    apply Subtype.ext
    change PowerSeries.rescale (u : ℂ) (PowerSeries.C c) = PowerSeries.C c
    ext n
    cases n <;> simp [PowerSeries.coeff_rescale]

@[simp]
theorem toSeries_phaseRotationHom (u : Circle) (f : WienerAlgebra R) :
    (phaseRotationHom u f).toSeries = PowerSeries.rescale (u : ℂ) f.toSeries :=
  rfl

/-- Coefficient form of the lifted action. -/
theorem coeff_phaseRotationHom (u : Circle) (f : WienerAlgebra R) (n : ℕ) :
    (PowerSeries.coeff n) (phaseRotationHom u f).toSeries =
      (u : ℂ) ^ n * (PowerSeries.coeff n) f.toSeries := by
  rw [toSeries_phaseRotationHom, PowerSeries.coeff_rescale]

/-- The lifted circle action is exactly isometric in the Wiener norm. -/
theorem norm_phaseRotationHom (u : Circle) (f : WienerAlgebra R) :
    ‖phaseRotationHom u f‖ = ‖f‖ := by
  rw [norm_def, norm_def, toSeries_phaseRotationHom, wienerScaleNorm, wienerScaleNorm,
    wienerScaleWeight_rescale_circle]

/-- Circle multiplication is composition of the corresponding lifted algebra actions. -/
theorem phaseRotationHom_mul (u v : Circle) :
    phaseRotationHom (R := R) (u * v) =
      (phaseRotationHom (R := R) v).comp (phaseRotationHom (R := R) u) := by
  apply AlgHom.ext
  intro f
  apply toSeries_injective
  simp only [toSeries_phaseRotationHom, AlgHom.coe_comp, Function.comp_apply, Circle.coe_mul]
  exact (PowerSeries.rescale_rescale f.toSeries (u : ℂ) (v : ℂ)).symm

/-- The lifted circle action as an algebra automorphism. -/
noncomputable def phaseRotationEquiv (u : Circle) :
    WienerAlgebra R ≃ₐ[ℂ] WienerAlgebra R :=
  { phaseRotationHom u with
    invFun := phaseRotationHom u⁻¹
    left_inv := fun f => by
      apply toSeries_injective
      change PowerSeries.rescale ((u⁻¹ : Circle) : ℂ)
        (PowerSeries.rescale (u : ℂ) f.toSeries) = f.toSeries
      rw [PowerSeries.rescale_rescale]
      simp
    right_inv := fun f => by
      apply toSeries_injective
      change PowerSeries.rescale (u : ℂ)
        (PowerSeries.rescale ((u⁻¹ : Circle) : ℂ) f.toSeries) = f.toSeries
      rw [PowerSeries.rescale_rescale]
      simp }

/-- The phase action rotates the concrete receiver point inside the closed disc. -/
def phaseRotatePoint (u : Circle) (z : CharacterPoint R) : CharacterPoint R :=
  ⟨(u : ℂ) * z.1, by
    rw [norm_mul, Circle.norm_coe, one_mul]
    exact z.property⟩

/-- **Koopman covariance.** Evaluating a lifted packet at `z` equals evaluating the original
packet at the classically rotated receiver `u z`. -/
theorem evalCharacter_phaseRotationHom (u : Circle) (z : CharacterPoint R)
    (f : WienerAlgebra R) :
    evalCharacter z (phaseRotationHom u f) = evalCharacter (phaseRotatePoint u z) f := by
  change wienerScaleEval (PowerSeries.rescale (u : ℂ) f.toSeries) z.1 =
    wienerScaleEval f.toSeries ((u : ℂ) * z.1)
  rw [wienerScaleEval, wienerScaleEval]
  apply tsum_congr
  intro n
  rw [PowerSeries.coeff_rescale, mul_pow]
  ring

/-- Gelfand transforms intertwine second-quantized and classical phase rotation. -/
theorem gelfandEvaluation_phaseRotationHom (u : Circle) (f : WienerAlgebra R)
    (z : CharacterPoint R) :
    gelfandEvaluation (phaseRotationHom u f) z =
      gelfandEvaluation f (phaseRotatePoint u z) :=
  evalCharacter_phaseRotationHom u z f

/-- One-parameter Koopman evolution obtained from the exponential circle flow. -/
noncomputable def koopmanEvolution (t : ℝ) :
    WienerAlgebra R ≃ₐ[ℂ] WienerAlgebra R :=
  phaseRotationEquiv (Circle.exp t)

/-- Exact group law for the lifted Koopman evolution. -/
theorem koopmanEvolution_add (s t : ℝ) (f : WienerAlgebra R) :
    koopmanEvolution (s + t) f = koopmanEvolution t (koopmanEvolution s f) := by
  change phaseRotationHom (Circle.exp (s + t)) f =
    phaseRotationHom (Circle.exp t) (phaseRotationHom (Circle.exp s) f)
  rw [Circle.exp_add]
  exact DFunLike.congr_fun (phaseRotationHom_mul (Circle.exp s) (Circle.exp t)) f

/-- The Koopman evolution preserves the Wiener norm at every real time. -/
theorem norm_koopmanEvolution (t : ℝ) (f : WienerAlgebra R) :
    ‖koopmanEvolution t f‖ = ‖f‖ :=
  norm_phaseRotationHom (Circle.exp t) f

end HTGeometry.WienerAlgebra
