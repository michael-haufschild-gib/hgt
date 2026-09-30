import GaloisForLFunctions.RHTower.ThetaTemperedFourierOrbit
import GaloisForLFunctions.RHTower.ThetaTemperedFiniteJetFactorization

/-!
# Physical Fourier correlation on the actual tempered dual

Spatial-jet inversion and exact modulation jets provide an explicit finite
seminorm polynomial. It proves integrability in the existing complete finite
Banach observer. Coordinate evaluation identifies that integral with the actual
product jets. The unconditional finite-jet factorization of every tempered
functional then proves the normalized scalar correlation identity.
-/

open MeasureTheory FourierTransform
open scoped SchwartzMap BoundedContinuousFunction

noncomputable section

namespace RHTower

open GaloisForLFunctions.HTGeometry

private theorem thetaSchwartzDerivCLM_eq_lineDeriv (φ : 𝓢(ℝ, ℂ)) :
    SchwartzMap.derivCLM ℂ ℂ φ = LineDeriv.lineDerivOp (1 : ℝ) φ := by
  ext x
  rw [SchwartzMap.lineDerivOp_apply_eq_fderiv, fderiv_apply_one_eq_deriv]
  rfl

theorem thetaPhysicalFourierCLE_derivCLM_apply (φ : 𝓢(ℝ, ℂ)) (a : ℝ) :
    thetaPhysicalFourierCLE (SchwartzMap.derivCLM ℂ ℂ φ) a =
      (-(Complex.I * (a : ℂ))) * thetaPhysicalFourierCLE φ a := by
  simp only [thetaPhysicalFourierCLE_apply]
  rw [thetaSchwartzDerivCLM_eq_lineDeriv, SchwartzMap.fourier_lineDerivOp_eq]
  change (2 * (Real.pi : ℂ) * Complex.I) *
    (SchwartzMap.smulLeftCLM ℂ (fun x : ℝ => inner ℝ x (1 : ℝ))
      (𝓕 φ) (-a / (2 * Real.pi))) = _
  rw [SchwartzMap.smulLeftCLM_apply_apply (Function.hasTemperateGrowth_inner_left (1 : ℝ)),
    Complex.real_smul]
  have hi (x : ℝ) : inner ℝ x (1 : ℝ) = x := by simp [RCLike.inner_apply]
  rw [hi]
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hc : (2 * (Real.pi : ℂ) * Complex.I) * (((-a / (2 * Real.pi) : ℝ) : ℂ)) =
      -(Complex.I * (a : ℂ)) := by
    push_cast
    field_simp
  calc
    _ = ((2 * (Real.pi : ℂ) * Complex.I) * (((-a / (2 * Real.pi) : ℝ) : ℂ))) *
        (𝓕 φ) (-a / (2 * Real.pi)) := by ring
    _ = _ := by rw [hc]

theorem thetaPhysicalFourierCLE_spatialJet_apply (n : ℕ) (φ : 𝓢(ℝ, ℂ)) (a : ℝ) :
    thetaPhysicalFourierCLE (thetaSchwartzSpatialJetCLM n φ) a =
      (-(Complex.I * (a : ℂ))) ^ n * thetaPhysicalFourierCLE φ a := by
  induction n generalizing φ with
  | zero => simp [thetaSchwartzSpatialJetCLM]
  | succ n ih =>
    change thetaPhysicalFourierCLE
      (thetaSchwartzSpatialJetCLM n (SchwartzMap.derivCLM ℂ ℂ φ)) a = _
    rw [ih, thetaPhysicalFourierCLE_derivCLM_apply, pow_succ]
    ring

theorem thetaPhysicalFourierCLE_spatialJet_inverse_integral
    (n : ℕ) (φ : 𝓢(ℝ, ℂ)) (t : ℝ) :
    iteratedDeriv n (φ : ℝ → ℂ) t = (((2 * Real.pi)⁻¹ : ℝ) : ℂ) *
      ∫ a : ℝ, modulation a t *
        ((-(Complex.I * (a : ℂ))) ^ n * thetaPhysicalFourierCLE φ a) := by
  have h := thetaPhysicalFourierCLE_inversion (thetaSchwartzSpatialJetCLM n φ) t
  rw [thetaSchwartzSpatialJetCLM_apply] at h
  simp_rw [thetaPhysicalFourierCLE_spatialJet_apply] at h
  exact h

private theorem thetaRealModulation_swap (a t : ℝ) : modulation a t = modulation t a := by
  unfold modulation cexpLin
  congr 1
  ring

theorem thetaPhysicalFourierCLE_spatialJet_moment_integrable
    (n : ℕ) (φ : 𝓢(ℝ, ℂ)) (t : ℝ) :
    Integrable (fun a : ℝ => modulation a t *
      ((-(Complex.I * (a : ℂ))) ^ n * thetaPhysicalFourierCLE φ a)) := by
  have h : (fun a : ℝ => modulation a t *
      ((-(Complex.I * (a : ℂ))) ^ n * thetaPhysicalFourierCLE φ a)) =
      (thetaPhysicalModulationCLM t
        (thetaPhysicalFourierCLE (thetaSchwartzSpatialJetCLM n φ)) : ℝ → ℂ) := by
    funext a
    rw [thetaPhysicalModulationCLM_apply, thetaPhysicalFourierCLE_spatialJet_apply,
      thetaRealModulation_swap]
  rw [h]
  exact SchwartzMap.integrable _

/-- The exact Leibniz expansion of every jet of the actual Schwartz modulation. -/
theorem thetaPhysicalModulationCLM_iteratedDeriv_apply
    (n : ℕ) (ψ : 𝓢(ℝ, ℂ)) (a t : ℝ) :
    iteratedDeriv n (thetaPhysicalModulationCLM a ψ) t =
      ∑ j ∈ Finset.range (n + 1),
        (n.choose j : ℂ) * (-(Complex.I * (a : ℂ))) ^ j *
          modulation a t * iteratedDeriv (n - j) ψ t := by
  have heq : (thetaPhysicalModulationCLM a ψ : ℝ → ℂ) =
      fun x => modulation a x * ψ x := by
    funext x
    exact thetaPhysicalModulationCLM_apply a ψ x
  have hm : ContDiffAt ℝ n (modulation a) t :=
    (contDiff_cexpLin (-(Complex.I * (a : ℂ)))).contDiffAt.of_le
      (by exact_mod_cast (show (n : ℕ∞) ≤ ⊤ from le_top))
  have hmul : modulation a * (ψ : ℝ → ℂ) =
      fun x => modulation a x * ψ x := by
    funext x
    rfl
  have h := iteratedDeriv_mul hm (ψ.contDiffAt n)
  rw [hmul] at h
  rw [heq]
  simpa only [modulation, iteratedDeriv_cexpLin, mul_assoc] using h

/-- Each modulated seminorm has a finite, explicit polynomial majorant. -/
theorem thetaPhysicalModulationCLM_seminorm_le
    (k n : ℕ) (ψ : 𝓢(ℝ, ℂ)) (a : ℝ) :
    SchwartzMap.seminorm ℂ k n (thetaPhysicalModulationCLM a ψ) ≤
      ∑ j ∈ Finset.range (n + 1),
        (n.choose j : ℝ) * |a| ^ j * SchwartzMap.seminorm ℂ k (n - j) ψ := by
  apply SchwartzMap.seminorm_le_bound' ℂ k n _ (by positivity)
  intro t
  rw [thetaPhysicalModulationCLM_iteratedDeriv_apply]
  calc
    |t| ^ k * ‖∑ j ∈ Finset.range (n + 1),
        (n.choose j : ℂ) * (-(Complex.I * (a : ℂ))) ^ j *
          modulation a t * iteratedDeriv (n - j) ψ t‖ ≤
        |t| ^ k * ∑ j ∈ Finset.range (n + 1),
          ‖(n.choose j : ℂ) * (-(Complex.I * (a : ℂ))) ^ j *
            modulation a t * iteratedDeriv (n - j) ψ t‖ :=
      mul_le_mul_of_nonneg_left (norm_sum_le _ _) (by positivity)
    _ = ∑ j ∈ Finset.range (n + 1),
        (n.choose j : ℝ) * |a| ^ j *
          (|t| ^ k * ‖iteratedDeriv (n - j) ψ t‖) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j hj
      rw [norm_mul, norm_mul, norm_mul, norm_pow, Complex.norm_natCast,
        norm_neg_I_mul, norm_modulation]
      ring
    _ ≤ ∑ j ∈ Finset.range (n + 1),
        (n.choose j : ℝ) * |a| ^ j * SchwartzMap.seminorm ℂ k (n - j) ψ := by
      apply Finset.sum_le_sum
      intro j hj
      exact mul_le_mul_of_nonneg_left (ψ.le_seminorm' ℂ k (n - j) t) (by positivity)

/-- A finite polynomial majorant using only the original weighted seminorms. -/
def thetaModulationFiniteJetMajorant
    (s : Finset (ℕ × ℕ)) (ψ : 𝓢(ℝ, ℂ)) (a : ℝ) : ℝ :=
  ∑ m : s, ∑ j ∈ Finset.range (m.val.2 + 1),
    (m.val.2.choose j : ℝ) * |a| ^ j *
      SchwartzMap.seminorm ℂ m.val.1 (m.val.2 - j) ψ

/-- The genuine finite Banach observer is bounded by the finite seminorm polynomial. -/
theorem thetaPhysicalModulationCLM_finiteJet_norm_le
    (s : Finset (ℕ × ℕ)) (ψ : 𝓢(ℝ, ℂ)) (a : ℝ) :
    ‖thetaSchwartzFiniteJetCLM s (thetaPhysicalModulationCLM a ψ)‖ ≤
      thetaModulationFiniteJetMajorant s ψ a := by
  unfold thetaModulationFiniteJetMajorant
  apply (pi_norm_le_iff_of_nonneg (by positivity)).2
  intro m
  rw [thetaSchwartzFiniteJetCLM_component_norm]
  apply (thetaPhysicalModulationCLM_seminorm_le m.val.1 m.val.2 ψ a).trans
  exact Finset.single_le_sum
    (f := fun i : s => ∑ j ∈ Finset.range (i.val.2 + 1),
      (i.val.2.choose j : ℝ) * |a| ^ j *
        SchwartzMap.seminorm ℂ i.val.1 (i.val.2 - j) ψ)
    (fun i hi => by positivity) (Finset.mem_univ m)

/-- Every weighted summand of the majorant is integrable against the actual Fourier test. -/
theorem thetaModulationFiniteJetMajorant_fourier_integrable
    (s : Finset (ℕ × ℕ)) (ψ φ : 𝓢(ℝ, ℂ)) :
    Integrable (fun a => ‖thetaPhysicalFourierCLE φ a‖ *
      thetaModulationFiniteJetMajorant s ψ a) := by
  unfold thetaModulationFiniteJetMajorant
  simp_rw [Finset.mul_sum]
  apply integrable_finsetSum Finset.univ
  intro m hm
  apply integrable_finsetSum (Finset.range (m.val.2 + 1))
  intro j hj
  have h := ((thetaPhysicalFourierCLE φ).integrable_pow_mul volume j).const_mul
    (m.val.2.choose j : ℝ)
  have h' := h.mul_const (SchwartzMap.seminorm ℂ m.val.1 (m.val.2 - j) ψ)
  have heq : (fun a : ℝ => ‖thetaPhysicalFourierCLE φ a‖ *
      ((m.val.2.choose j : ℝ) * |a| ^ j *
        SchwartzMap.seminorm ℂ m.val.1 (m.val.2 - j) ψ)) =
      (fun a : ℝ => (m.val.2.choose j : ℝ) *
        (‖a‖ ^ j * ‖thetaPhysicalFourierCLE φ a‖) *
          SchwartzMap.seminorm ℂ m.val.1 (m.val.2 - j) ψ) := by
    funext a
    rw [Real.norm_eq_abs]
    ring
  rw [heq]
  exact h'

/-- This integral lives in the existing complete finite Banach product. -/
theorem thetaPhysicalFourierCLE_modulation_finiteJet_integrable
    (s : Finset (ℕ × ℕ)) (ψ φ : 𝓢(ℝ, ℂ)) :
    Integrable (fun a => thetaPhysicalFourierCLE φ a •
      thetaSchwartzFiniteJetCLM s (thetaPhysicalModulationCLM a ψ)) := by
  letI : SecondCountableTopologyEither ℝ (thetaSchwartzFiniteJetBanach s) :=
    ⟨Or.inl inferInstance⟩
  have hc : Continuous (fun a : ℝ => thetaPhysicalFourierCLE φ a •
      thetaSchwartzFiniteJetCLM s (thetaPhysicalModulationCLM a ψ)) :=
    (thetaPhysicalFourierCLE φ).continuous.smul
      ((thetaSchwartzFiniteJetCLM s).continuous.comp
        (thetaPhysicalModulationCLM_continuous ψ))
  apply (thetaModulationFiniteJetMajorant_fourier_integrable s ψ φ).mono'
    hc.aestronglyMeasurable
  filter_upwards [] with a
  rw [norm_smul]
  exact mul_le_mul_of_nonneg_left
    (thetaPhysicalModulationCLM_finiteJet_norm_le s ψ a) (norm_nonneg _)

/-- Full scalar Leibniz reconstruction, with every moment integrable on the actual source. -/
theorem thetaPhysicalFourierCLE_modulation_jet_inverse
    (n : ℕ) (ψ φ : 𝓢(ℝ, ℂ)) (t : ℝ) :
    iteratedDeriv n (SchwartzMap.smulLeftCLM ℂ (ψ : ℝ → ℂ) φ) t =
      ((↑((2 * Real.pi)⁻¹) : ℂ)) *
        ∫ a : ℝ, thetaPhysicalFourierCLE φ a *
          iteratedDeriv n (thetaPhysicalModulationCLM a ψ) t := by
  let moment (j : ℕ) (a : ℝ) : ℂ :=
    modulation a t * ((-(Complex.I * (a : ℂ))) ^ j * thetaPhysicalFourierCLE φ a)
  let coeff (j : ℕ) : ℂ := (n.choose j : ℂ) * iteratedDeriv (n - j) ψ t
  have hdecomp : (fun a : ℝ => thetaPhysicalFourierCLE φ a *
      iteratedDeriv n (thetaPhysicalModulationCLM a ψ) t) =
      (fun a : ℝ => ∑ j ∈ Finset.range (n + 1), coeff j * moment j a) := by
    funext a
    rw [thetaPhysicalModulationCLM_iteratedDeriv_apply, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    dsimp [coeff, moment]
    ring
  have hI : ∀ j ∈ Finset.range (n + 1),
      Integrable (fun a : ℝ => coeff j * moment j a) := by
    intro j hj
    exact (thetaPhysicalFourierCLE_spatialJet_moment_integrable j φ t).const_mul (coeff j)
  have hproduct : (SchwartzMap.smulLeftCLM ℂ (ψ : ℝ → ℂ) φ : ℝ → ℂ) =
      (φ : ℝ → ℂ) * (ψ : ℝ → ℂ) := by
    funext x
    rw [SchwartzMap.smulLeftCLM_apply_apply ψ.hasTemperateGrowth]
    change ψ x * φ x = φ x * ψ x
    exact mul_comm _ _
  have hjet : iteratedDeriv n (SchwartzMap.smulLeftCLM ℂ (ψ : ℝ → ℂ) φ) t =
      ∑ j ∈ Finset.range (n + 1),
        (n.choose j : ℂ) * iteratedDeriv j φ t * iteratedDeriv (n - j) ψ t := by
    rw [hproduct]
    exact iteratedDeriv_mul (φ.contDiffAt n) (ψ.contDiffAt n)
  rw [hjet, hdecomp, integral_finsetSum _ hI, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  rw [integral_const_mul]
  dsimp [coeff]
  have hmoment := thetaPhysicalFourierCLE_spatialJet_inverse_integral j φ t
  change iteratedDeriv j φ t = (↑((2 * Real.pi)⁻¹) : ℂ) *
    ∫ a : ℝ, moment j a at hmoment
  rw [hmoment]
  ring

/-- Coordinate evaluation identifies the genuine Banach integral with the actual product jets. -/
theorem thetaPhysicalFourierCLE_modulation_finiteJet_inverse
    (s : Finset (ℕ × ℕ)) (ψ φ : 𝓢(ℝ, ℂ)) :
    thetaSchwartzFiniteJetCLM s (SchwartzMap.smulLeftCLM ℂ (ψ : ℝ → ℂ) φ) =
      (↑((2 * Real.pi)⁻¹) : ℂ) •
        ∫ a : ℝ, thetaPhysicalFourierCLE φ a •
          thetaSchwartzFiniteJetCLM s (thetaPhysicalModulationCLM a ψ) := by
  funext m
  apply BoundedContinuousFunction.ext
  intro t
  let ev : thetaSchwartzFiniteJetBanach s →L[ℂ] ℂ :=
    (BoundedContinuousFunction.evalCLM ℂ t).comp (ContinuousLinearMap.proj m)
  have heval (z : thetaSchwartzFiniteJetBanach s) : ev z = z m t := rfl
  have hcomm := ev.integral_comp_comm
    (thetaPhysicalFourierCLE_modulation_finiteJet_integrable s ψ φ)
  have hcomm' : (∫ a : ℝ, thetaPhysicalFourierCLE φ a *
      ((t : ℂ) ^ m.val.1 *
        iteratedDeriv m.val.2 (thetaPhysicalModulationCLM a ψ) t)) =
      (∫ a : ℝ, thetaPhysicalFourierCLE φ a •
        thetaSchwartzFiniteJetCLM s (thetaPhysicalModulationCLM a ψ)) m t := by
    have hevsmul (a : ℝ) : ev (thetaPhysicalFourierCLE φ a •
        thetaSchwartzFiniteJetCLM s (thetaPhysicalModulationCLM a ψ)) =
        thetaPhysicalFourierCLE φ a * ((t : ℂ) ^ m.val.1 *
          iteratedDeriv m.val.2 (thetaPhysicalModulationCLM a ψ) t) := by
      rw [ev.map_smul, heval, thetaSchwartzFiniteJetCLM_apply_apply]
      rfl
    calc
      _ = ∫ a : ℝ, ev (thetaPhysicalFourierCLE φ a •
          thetaSchwartzFiniteJetCLM s (thetaPhysicalModulationCLM a ψ)) := by
        apply integral_congr_ae
        filter_upwards [] with a
        exact (hevsmul a).symm
      _ = ev (∫ a : ℝ, thetaPhysicalFourierCLE φ a •
          thetaSchwartzFiniteJetCLM s (thetaPhysicalModulationCLM a ψ)) := hcomm
      _ = _ := heval _
  rw [thetaSchwartzFiniteJetCLM_apply_apply]
  change (t : ℂ) ^ m.val.1 *
      iteratedDeriv m.val.2 (SchwartzMap.smulLeftCLM ℂ (ψ : ℝ → ℂ) φ) t =
    (↑((2 * Real.pi)⁻¹) : ℂ) *
      (∫ a : ℝ, thetaPhysicalFourierCLE φ a •
        thetaSchwartzFiniteJetCLM s (thetaPhysicalModulationCLM a ψ)) m t
  rw [← hcomm', thetaPhysicalFourierCLE_modulation_jet_inverse]
  have heq : (fun a : ℝ => thetaPhysicalFourierCLE φ a *
      ((t : ℂ) ^ m.val.1 * iteratedDeriv m.val.2 (thetaPhysicalModulationCLM a ψ) t)) =
      (fun a : ℝ => (t : ℂ) ^ m.val.1 *
        (thetaPhysicalFourierCLE φ a * iteratedDeriv m.val.2
          (thetaPhysicalModulationCLM a ψ) t)) := by
    funext a
    ring
  rw [heq, integral_const_mul]
  ring

/-- The arbitrary-functional correlation formula follows from genuine Banach factorization. -/
theorem thetaTempered_physicalFourier_correlation
    (Q : 𝓢'(ℝ, ℂ)) (ψ φ : 𝓢(ℝ, ℂ)) :
    Q (SchwartzMap.smulLeftCLM ℂ (ψ : ℝ → ℂ) φ) =
      (↑((2 * Real.pi)⁻¹) : ℂ) *
        ∫ a : ℝ, thetaPhysicalFourierCLE φ a * Q (thetaPhysicalModulationCLM a ψ) := by
  obtain ⟨s, L, hL⟩ := thetaTempered_exists_finiteJetFactorization Q
  rw [← hL, thetaPhysicalFourierCLE_modulation_finiteJet_inverse,
    L.map_smul, ← L.integral_comp_comm
      (thetaPhysicalFourierCLE_modulation_finiteJet_integrable s ψ φ)]
  congr 1
  apply integral_congr_ae
  filter_upwards [] with a
  rw [L.map_smul, hL]
  rfl

/-- The scalar correlation integrand is genuinely integrable for every tempered functional. -/
theorem thetaTempered_physicalFourier_correlation_integrable
    (Q : 𝓢'(ℝ, ℂ)) (ψ φ : 𝓢(ℝ, ℂ)) :
    Integrable (fun a : ℝ => thetaPhysicalFourierCLE φ a *
      Q (thetaPhysicalModulationCLM a ψ)) := by
  obtain ⟨s, L, hL⟩ := thetaTempered_exists_finiteJetFactorization Q
  have h := L.integrable_comp
    (thetaPhysicalFourierCLE_modulation_finiteJet_integrable s ψ φ)
  simpa only [L.map_smul, hL, smul_eq_mul] using h

end RHTower
