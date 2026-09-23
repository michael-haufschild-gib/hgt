import GaloisForLFunctions.HTGeometry.SpectralCollisionFunctional
import GaloisForLFunctions.HTGeometry.SpectralCollisionCovariance

/-!
# The spectral collision of a random Hermitian family

An eigenbasis is not a measurable function of a Hermitian matrix, but the collision it computes is
the pointwise limit of the continuous gap regularizations whenever the spectrum is simple.  A
family whose spectrum is almost surely simple therefore has almost everywhere measurable collision,
bounded by one for a unit state, and Markov's inequality applies to it.

Conjugating a Hermitian matrix by a unitary transports its eigenbasis and preserves its
eigenvalues, so the collision of a conjugated family at a fixed state is the collision of the
original family at the rotated state.
-/

open MeasureTheory Matrix

noncomputable section

namespace GaloisForLFunctions.HTGeometry

set_option linter.unusedSectionVars false

variable {α : Type*} [Fintype α] [DecidableEq α]

section Parseval

theorem spectralCollision_eq_sum_eigenWeight_sq (e : α → α → ℂ) (ψ : α → ℂ) :
    spectralCollision e ψ = ∑ j, eigenWeight e ψ j ^ (2 : ℕ) := rfl

/-- **Parseval.**  The spectral weights of a state sum to its squared length. -/
theorem sum_eigenWeight_eq {H : Matrix α α ℂ} {e : α → α → ℂ} {lam : α → ℝ}
    (hb : IsOrthoEigenBasis H e lam) (ψ : α → ℂ) :
    (∑ j, eigenWeight e ψ j) = ∑ x, ‖ψ x‖ ^ (2 : ℕ) := by
  classical
  have hself : finiteComplexInner ψ ψ = ((∑ x, ‖ψ x‖ ^ (2 : ℕ) : ℝ) : ℂ) := by
    rw [finiteComplexInner, Complex.ofReal_sum]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [Complex.sq_norm, ← Complex.mul_conj]
    ring
  have hexp : finiteComplexInner ψ ψ = ((∑ j, eigenWeight e ψ j : ℝ) : ℂ) := by
    have h1 : finiteComplexInner ψ (∑ j, finiteComplexInner (e j) ψ • e j) =
        finiteComplexInner ψ ψ := by rw [hb.complete ψ]
    rw [← h1, finiteComplexInner_sum_right, Complex.ofReal_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [finiteComplexInner_smul_right, finiteComplexInner_conj_symm ψ (e j), eigenWeight,
      Complex.sq_norm, ← Complex.mul_conj]
  have : ((∑ j, eigenWeight e ψ j : ℝ) : ℂ) = ((∑ x, ‖ψ x‖ ^ (2 : ℕ) : ℝ) : ℂ) := by
    rw [← hexp, hself]
  exact_mod_cast this

theorem spectralCollision_le_one {H : Matrix α α ℂ} {e : α → α → ℂ} {lam : α → ℝ}
    (hb : IsOrthoEigenBasis H e lam) {ψ : α → ℂ} (hψ : (∑ x, ‖ψ x‖ ^ (2 : ℕ)) = 1) :
    spectralCollision e ψ ≤ 1 := by
  have hsum := sum_eigenWeight_eq hb ψ
  rw [hψ] at hsum
  rw [spectralCollision_eq_sum_eigenWeight_sq]
  calc (∑ j, eigenWeight e ψ j ^ (2 : ℕ)) ≤ (∑ j, eigenWeight e ψ j) ^ (2 : ℕ) := by
        rw [sq, Finset.sum_mul_sum]
        refine Finset.sum_le_sum fun j _ => ?_
        rw [sq]
        refine Finset.single_le_sum
          (f := fun k => eigenWeight e ψ j * eigenWeight e ψ k)
          (fun k _ => mul_nonneg (eigenWeight_nonneg e ψ j) (eigenWeight_nonneg e ψ k))
          (Finset.mem_univ j)
    _ = 1 := by rw [hsum, one_pow]

theorem cappedRegCollision_le_one {H : Matrix α α ℂ} {e : α → α → ℂ} {lam : α → ℝ}
    (hb : IsOrthoEigenBasis H e lam) {ψ : α → ℂ} (hψ : (∑ x, ‖ψ x‖ ^ (2 : ℕ)) = 1) (m : ℕ) :
    cappedRegCollision m H ψ ≤ 1 := by
  have h := cappedRegCollision_le_sq hb ψ m
  rw [sum_eigenWeight_eq hb ψ, hψ, one_pow] at h
  exact h

theorem cappedRegCollision_nonneg {H : Matrix α α ℂ} {e : α → α → ℂ} {lam : α → ℝ}
    (hb : IsOrthoEigenBasis H e lam) (ψ : α → ℂ) (m : ℕ) :
    0 ≤ cappedRegCollision m H ψ := by
  refine le_trans ?_ (sum_eigenWeight_sq_le_cappedRegCollision hb ψ m)
  exact Finset.sum_nonneg fun j _ => sq_nonneg _

end Parseval

section Conjugation

/-- **Unitary conjugation transports an eigenbasis.** -/
theorem isOrthoEigenBasis_conj {H : Matrix α α ℂ} {e : α → α → ℂ} {lam : α → ℝ}
    (hb : IsOrthoEigenBasis H e lam) {U : Matrix α α ℂ} (hU : Uᴴ * U = 1) (hU' : U * Uᴴ = 1) :
    IsOrthoEigenBasis (Uᴴ * H * U) (fun j => Uᴴ *ᵥ e j) lam := by
  classical
  have hinner : ∀ u v : α → ℂ, finiteComplexInner (Uᴴ *ᵥ u) (Uᴴ *ᵥ v) =
      finiteComplexInner u v := by
    intro u v
    rw [finiteComplexInner_conjTranspose_mulVec U u (Uᴴ *ᵥ v), Matrix.mulVec_mulVec, hU',
      Matrix.one_mulVec]
  refine ⟨fun j k => by rw [hinner]; exact hb.orth j k, fun j => ?_, fun ψ => ?_⟩
  · have hmat : (Uᴴ * H * U) * Uᴴ = Uᴴ * H := by
      rw [Matrix.mul_assoc, hU', Matrix.mul_one]
    rw [Matrix.mulVec_mulVec, hmat, ← Matrix.mulVec_mulVec, hb.eigen j, Matrix.mulVec_smul]
  · have hmap : ∀ v : α → ℂ, Uᴴ *ᵥ (U *ᵥ v) = v := by
      intro v
      rw [Matrix.mulVec_mulVec, hU, Matrix.one_mulVec]
    have hstep : (∑ j, finiteComplexInner (Uᴴ *ᵥ e j) ψ • (Uᴴ *ᵥ e j)) =
        Uᴴ *ᵥ (∑ j, finiteComplexInner (e j) (U *ᵥ ψ) • e j) := by
      rw [Matrix.mulVec_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [Matrix.mulVec_smul, finiteComplexInner_conjTranspose_mulVec U (e j) ψ]
    rw [hstep, hb.complete (U *ᵥ ψ), hmap]

/-- **The collision does not depend on the chosen eigenbasis at a simple spectrum.**  Both
eigenbases compute the same limit of the gap regularizations. -/
theorem spectralCollision_eq_of_isOrthoEigenBasis {H : Matrix α α ℂ}
    {e e' : α → α → ℂ} {lam lam' : α → ℝ}
    (hb : IsOrthoEigenBasis H e lam) (hinj : Function.Injective lam)
    (hb' : IsOrthoEigenBasis H e' lam') (hinj' : Function.Injective lam') (ψ : α → ℂ) :
    spectralCollision e ψ = spectralCollision e' ψ :=
  tendsto_nhds_unique (tendsto_cappedRegCollision hb ψ hinj)
    (tendsto_cappedRegCollision hb' ψ hinj')

/-- **Conjugation covariance of the collision.**  The collision of the conjugated matrix at a
state is the collision of the original matrix at the rotated state. -/
theorem spectralCollision_conj_eq {H : Matrix α α ℂ} {e e' : α → α → ℂ} {lam lam' : α → ℝ}
    (hb : IsOrthoEigenBasis H e lam) (hinj : Function.Injective lam)
    {U : Matrix α α ℂ} (hU : Uᴴ * U = 1) (hU' : U * Uᴴ = 1)
    (hb' : IsOrthoEigenBasis (Uᴴ * H * U) e' lam') (hinj' : Function.Injective lam')
    (ψ : α → ℂ) :
    spectralCollision e' ψ = spectralCollision e (U *ᵥ ψ) := by
  rw [← spectralCollision_conjTranspose_mulVec U e ψ]
  exact spectralCollision_eq_of_isOrthoEigenBasis hb' hinj'
    (isOrthoEigenBasis_conj hb hU hU') hinj ψ

end Conjugation

section Ensemble

variable {Θ : Type*} [MeasurableSpace Θ]

theorem measurable_matrixPow_entry_comp {Hf : Θ → Matrix α α ℂ}
    (hH : ∀ x y, Measurable fun θ => Hf θ x y) (r : ℕ) (x y : α) :
    Measurable fun θ => ((Hf θ) ^ r) x y := by
  classical
  induction r generalizing x y with
  | zero =>
      simp only [pow_zero, Matrix.one_apply]
      exact measurable_const
  | succ r ih =>
      have hrw : ∀ θ, ((Hf θ) ^ (r + 1)) x y = ∑ z, Hf θ x z * ((Hf θ) ^ r) z y := by
        intro θ
        rw [pow_succ']
        rfl
      simp only [hrw]
      exact Finset.measurable_sum _ fun z _ => (hH x z).mul (ih z y)

theorem measurable_stateMoment_comp {Hf : Θ → Matrix α α ℂ}
    (hH : ∀ x y, Measurable fun θ => Hf θ x y) (ψ : α → ℂ) (r : ℕ) :
    Measurable fun θ => stateMoment (Hf θ) ψ r := by
  classical
  have hrw : ∀ θ, stateMoment (Hf θ) ψ r =
      ∑ x, (starRingEnd ℂ) (ψ x) * ∑ y, ((Hf θ) ^ r) x y * ψ y := by
    intro θ
    rw [stateMoment, finiteComplexInner]
    exact Finset.sum_congr rfl fun x _ => rfl
  simp only [hrw]
  refine Finset.measurable_sum _ fun x _ => measurable_const.mul ?_
  exact Finset.measurable_sum _ fun y _ =>
    (measurable_matrixPow_entry_comp hH r x y).mul measurable_const

theorem measurable_capC_comp {Hf : Θ → Matrix α α ℂ}
    (hH : ∀ x y, Measurable fun θ => Hf θ x y) :
    Measurable fun θ => capC (Hf θ) := by
  classical
  have hfrob : Measurable fun θ => frobSq (Hf θ) := by
    refine Finset.measurable_sum _ fun a _ => Finset.measurable_sum _ fun b _ => ?_
    exact ((hH a b).norm).pow_const 2
  exact measurable_const.add (measurable_const.mul hfrob)

theorem measurable_cappedRegCollision_comp {Hf : Θ → Matrix α α ℂ}
    (hH : ∀ x y, Measurable fun θ => Hf θ x y) (ψ : α → ℂ) (m : ℕ) :
    Measurable fun θ => cappedRegCollision m (Hf θ) ψ := by
  classical
  have hden : Measurable fun θ => (((capC (Hf θ) : ℝ)) : ℂ) :=
    Complex.measurable_ofReal.comp (measurable_capC_comp hH)
  have hC : Measurable fun θ => regCollisionC (capC (Hf θ)) m (Hf θ) ψ := by
    refine Finset.measurable_sum _ fun l _ => ?_
    refine Measurable.mul (measurable_const.mul ((measurable_const.div hden).pow_const l)) ?_
    refine Finset.measurable_sum _ fun i _ => ?_
    exact measurable_const.mul
      ((measurable_stateMoment_comp hH ψ (2 * l - i)).mul (measurable_stateMoment_comp hH ψ i))
  exact Complex.measurable_re.comp hC

/-- **The collision of an almost surely simple-spectrum family is almost everywhere
measurable.** -/
theorem aemeasurable_spectralCollision {μ : Measure Θ} {Hf : Θ → Matrix α α ℂ}
    (hH : ∀ x y, Measurable fun θ => Hf θ x y) (ψ : α → ℂ) {e : Θ → α → α → ℂ} {lam : Θ → α → ℝ}
    (hae : ∀ᵐ θ ∂μ, IsOrthoEigenBasis (Hf θ) (e θ) (lam θ) ∧ Function.Injective (lam θ)) :
    AEMeasurable (fun θ => spectralCollision (e θ) ψ) μ := by
  refine aemeasurable_of_tendsto_metrizable_ae'
    (f := fun m θ => cappedRegCollision m (Hf θ) ψ)
    (fun m => (measurable_cappedRegCollision_comp hH ψ m).aemeasurable) ?_
  filter_upwards [hae] with θ hθ
  exact tendsto_cappedRegCollision hθ.1 ψ hθ.2

theorem integrable_spectralCollision {μ : Measure Θ} [IsFiniteMeasure μ]
    {Hf : Θ → Matrix α α ℂ} (hH : ∀ x y, Measurable fun θ => Hf θ x y)
    {ψ : α → ℂ} (hψ : (∑ x, ‖ψ x‖ ^ (2 : ℕ)) = 1)
    {e : Θ → α → α → ℂ} {lam : Θ → α → ℝ}
    (hae : ∀ᵐ θ ∂μ, IsOrthoEigenBasis (Hf θ) (e θ) (lam θ) ∧ Function.Injective (lam θ)) :
    Integrable (fun θ => spectralCollision (e θ) ψ) μ := by
  refine Integrable.mono' (g := fun _ : Θ => (1 : ℝ)) (integrable_const 1)
    (aemeasurable_spectralCollision hH ψ hae).aestronglyMeasurable ?_
  filter_upwards [hae] with θ hθ
  rw [Real.norm_of_nonneg (spectralCollision_nonneg (e θ) ψ)]
  exact spectralCollision_le_one hθ.1 hψ

/-- **Markov bound for the ensemble collision.**  A family whose mean collision is at most `c₀`
exceeds `L c₀` with probability at most `1 / L`. -/
theorem measureReal_spectralCollision_ge_le {μ : Measure Θ} [IsProbabilityMeasure μ]
    {Hf : Θ → Matrix α α ℂ} (hH : ∀ x y, Measurable fun θ => Hf θ x y)
    {ψ : α → ℂ} (hψ : (∑ x, ‖ψ x‖ ^ (2 : ℕ)) = 1)
    {e : Θ → α → α → ℂ} {lam : Θ → α → ℝ}
    (hae : ∀ᵐ θ ∂μ, IsOrthoEigenBasis (Hf θ) (e θ) (lam θ) ∧ Function.Injective (lam θ))
    {c₀ : ℝ} (hc₀ : 0 < c₀) (hmean : (∫ θ, spectralCollision (e θ) ψ ∂μ) ≤ c₀)
    {L : ℝ} (hL : 0 < L) :
    μ.real {θ | L * c₀ ≤ spectralCollision (e θ) ψ} ≤ 1 / L := by
  have hint := integrable_spectralCollision hH hψ hae
  have hnn : (0 : Θ → ℝ) ≤ᵐ[μ] fun θ => spectralCollision (e θ) ψ :=
    Filter.Eventually.of_forall fun θ => spectralCollision_nonneg (e θ) ψ
  have hmk := mul_meas_ge_le_integral_of_nonneg hnn hint (L * c₀)
  have hpos : 0 < L * c₀ := mul_pos hL hc₀
  have hchain : L * c₀ * μ.real {θ | L * c₀ ≤ spectralCollision (e θ) ψ} ≤ c₀ :=
    le_trans hmk hmean
  rw [le_div_iff₀ hL]
  nlinarith [hchain, hc₀, hpos]

/-- **Conjugation invariance of the mean collision.**  If the family is carried by a
measure-preserving reparametrization onto its conjugate by a unitary, then its mean collision at a
state equals its mean collision at the rotated state. -/
theorem integral_spectralCollision_conj_eq {μ : Measure Θ} [IsProbabilityMeasure μ]
    {Hf : Θ → Matrix α α ℂ} (hH : ∀ x y, Measurable fun θ => Hf θ x y) (ψ : α → ℂ)
    {e : Θ → α → α → ℂ} {lam : Θ → α → ℝ}
    (hae : ∀ᵐ θ ∂μ, IsOrthoEigenBasis (Hf θ) (e θ) (lam θ) ∧ Function.Injective (lam θ))
    {U : Matrix α α ℂ} (hU : Uᴴ * U = 1) (hU' : U * Uᴴ = 1)
    {T : Θ → Θ} (hT : MeasurePreserving T μ μ)
    (hcov : ∀ᵐ θ ∂μ, Hf (T θ) = Uᴴ * Hf θ * U) :
    (∫ θ, spectralCollision (e θ) (U *ᵥ ψ) ∂μ) = ∫ θ, spectralCollision (e θ) ψ ∂μ := by
  classical
  have haeT : ∀ᵐ θ ∂μ,
      IsOrthoEigenBasis (Hf (T θ)) (e (T θ)) (lam (T θ)) ∧ Function.Injective (lam (T θ)) :=
    hT.quasiMeasurePreserving.ae hae
  have hpt : ∀ᵐ θ ∂μ,
      spectralCollision (e (T θ)) ψ = spectralCollision (e θ) (U *ᵥ ψ) := by
    filter_upwards [hae, haeT, hcov] with θ hθ hθT hθcov
    exact spectralCollision_conj_eq hθ.1 hθ.2 hU hU' (hθcov ▸ hθT.1) hθT.2 ψ
  have hmeas : AEStronglyMeasurable (fun θ => spectralCollision (e θ) ψ) μ :=
    (aemeasurable_spectralCollision hH ψ hae).aestronglyMeasurable
  have hcomp : (∫ θ, spectralCollision (e (T θ)) ψ ∂μ) = ∫ θ, spectralCollision (e θ) ψ ∂μ := by
    have hm' : AEStronglyMeasurable (fun θ => spectralCollision (e θ) ψ) (μ.map T) := by
      rw [hT.map_eq]
      exact hmeas
    calc (∫ θ, spectralCollision (e (T θ)) ψ ∂μ)
        = ∫ y, spectralCollision (e y) ψ ∂(μ.map T) :=
          (integral_map hT.measurable.aemeasurable hm').symm
      _ = ∫ θ, spectralCollision (e θ) ψ ∂μ := by rw [hT.map_eq]
  rw [← hcomp]
  exact (integral_congr_ae hpt).symm

end Ensemble

end GaloisForLFunctions.HTGeometry
