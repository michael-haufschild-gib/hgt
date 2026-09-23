import GaloisForLFunctions.HTGeometry.GoldenRuleAmplitude
import GaloisForLFunctions.HTGeometry.SelfAdjointPropagator
import GaloisForLFunctions.HTGeometry.GoldenRuleLimit

/-!
# The Friedrichs model and Fermi's golden rule

A *Friedrichs model* is the standard rigorous setting for Fermi's golden rule: a normalized bound
state `ψ₀` of a free Hamiltonian `H₀`, of energy `E₀`, coupled to a continuum through a form factor
`v` orthogonal to `ψ₀`.  Here the continuum is realized concretely as `L²(μ)` with `H₀`
multiplication by a bounded measurable energy function `ω`, so no spectral theorem is needed: the
spectral measure of the model *is* the underlying measure.

Everything is a bounded operator, so the Schrödinger propagator is the honest Banach-algebra
exponential `exp (-i t H)` with `H = H₀ + λ V`, `V = |ψ₀⟩⟨v| + |v⟩⟨ψ₀|`.

The file proves, unconditionally:

* `duhamel`: the exact integral equation `U t − U₀ t = −i λ ∫₀ᵗ U₀(t−s) V U s ds`;
* `norm_evol_sub_freeProp_le`: the first-order estimate `‖(U t − U₀ t) ψ₀‖ ≤ |λ| ‖V‖ t`;
* `norm_sub_firstOrder_le`: the second-order remainder `‖(U t − U₀ t) ψ₀ − a t‖ ≤ λ² ‖V‖² t²`,
  where `a t` is the first-order Dyson term, computed in closed form;
* `normSq_firstOrder`: `‖a t‖² = λ² ∫ K t (ω x − E₀) ‖v x‖² dμ`;
* `tendsto_normSq_firstOrder`: **Fermi's golden rule**, `‖a t‖² / t → 2 π λ² ρ(E₀)`.
-/

open MeasureTheory Filter
open scoped InnerProductSpace

noncomputable section

namespace GaloisForLFunctions.HTGeometry

/-- **A Friedrichs model**: a normalized bound state of a bounded free Hamiltonian, coupled to a
continuum through a form factor orthogonal to it. -/
structure FriedrichsModel (α : Type*) [MeasurableSpace α] (μ : Measure α) where
  /-- the free energy function on the continuum labels -/
  energy : α → ℝ
  measurable_energy : Measurable energy
  /-- a uniform bound making the free Hamiltonian bounded -/
  cutoff : ℝ
  cutoff_nonneg : 0 ≤ cutoff
  energy_le : ∀ x, |energy x| ≤ cutoff
  /-- the unperturbed energy of the bound state -/
  level : ℝ
  /-- the bound state -/
  bound : Lp ℂ 2 μ
  /-- the form factor -/
  form : Lp ℂ 2 μ
  norm_bound : ‖bound‖ = 1
  eigen : ∀ᵐ x ∂μ, ((energy x : ℝ) : ℂ) * (bound : α → ℂ) x
      = ((level : ℝ) : ℂ) * (bound : α → ℂ) x
  ortho : (inner ℂ bound form : ℂ) = 0

namespace FriedrichsModel

variable {α : Type*} [MeasurableSpace α] {μ : Measure α} (M : FriedrichsModel α μ)

/-- The free Hamiltonian: multiplication by the energy function. -/
def freeHam : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ :=
  freeHamiltonian M.energy M.measurable_energy M.cutoff_nonneg M.energy_le

/-- The free Schrödinger group. -/
def freeProp (t : ℝ) : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ := freeGroup M.energy M.measurable_energy t

/-- The coupling operator `|ψ₀⟩⟨v| + |v⟩⟨ψ₀|`. -/
def coupling : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ :=
  (innerSL ℂ M.form).smulRight M.bound + (innerSL ℂ M.bound).smulRight M.form

/-- The full Hamiltonian at coupling strength `lam`. -/
def ham (lam : ℝ) : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ := M.freeHam + (lam : ℂ) • M.coupling

/-- The full Schrödinger propagator. -/
def evol (lam t : ℝ) : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ := propagator (M.ham lam) t

/-! ## Elementary properties -/

theorem coupling_apply (f : Lp ℂ 2 μ) :
    M.coupling f = (inner ℂ M.form f : ℂ) • M.bound + (inner ℂ M.bound f : ℂ) • M.form := rfl

theorem isSelfAdjoint_freeHam : IsSelfAdjoint M.freeHam :=
  isSelfAdjoint_freeHamiltonian M.energy M.measurable_energy M.cutoff_nonneg M.energy_le

theorem isSelfAdjoint_coupling : IsSelfAdjoint M.coupling := by
  rw [ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric]
  intro f g
  simp only [ContinuousLinearMap.coe_coe, coupling_apply, inner_add_left, inner_add_right,
    inner_smul_left, inner_smul_right, inner_conj_symm]
  ring

theorem isSelfAdjoint_ham (lam : ℝ) : IsSelfAdjoint (M.ham lam) := by
  refine IsSelfAdjoint.add M.isSelfAdjoint_freeHam ?_
  rw [IsSelfAdjoint, star_smul, M.isSelfAdjoint_coupling.star_eq]
  simp [Complex.conj_ofReal]

theorem coupling_bound : M.coupling M.bound = M.form := by
  rw [coupling_apply]
  have h1 : (inner ℂ M.form M.bound : ℂ) = 0 := by
    rw [← inner_conj_symm, M.ortho, map_zero]
  have h2 : (inner ℂ M.bound M.bound : ℂ) = 1 := by
    rw [inner_self_eq_norm_sq_to_K, M.norm_bound]
    norm_num
  rw [h1, h2, zero_smul, zero_add, one_smul]

theorem freeProp_bound (t : ℝ) :
    M.freeProp t M.bound = Complex.exp (((-(t * M.level) : ℝ) : ℂ) * Complex.I) • M.bound := by
  have hrw : M.freeProp t M.bound = freeGroup M.energy M.measurable_energy t M.bound := rfl
  rw [hrw]
  refine Lp.ext ?_
  filter_upwards [freeGroup_coeFn M.energy M.measurable_energy t M.bound, M.eigen,
    Lp.coeFn_smul (Complex.exp (((-(t * M.level) : ℝ) : ℂ) * Complex.I)) M.bound] with x h1 h2 h3
  rw [h1, h3]
  simp only [Pi.smul_apply, smul_eq_mul]
  rcases eq_or_ne ((M.bound : α → ℂ) x) 0 with hb | hb
  · rw [hb, mul_zero, mul_zero]
  · have hEq : M.energy x = M.level := by
      have := mul_right_cancel₀ hb h2
      exact_mod_cast this
    rw [freeSymbol, hEq]

theorem norm_freeProp_apply (t : ℝ) (f : Lp ℂ 2 μ) : ‖M.freeProp t f‖ = ‖f‖ :=
  norm_freeGroup_apply M.energy M.measurable_energy t f

theorem freeProp_comp (s t : ℝ) : M.freeProp s ∘L M.freeProp t = M.freeProp (s + t) :=
  freeGroup_comp M.energy M.measurable_energy s t

@[simp] theorem freeProp_zero : M.freeProp 0 = 1 := by
  rw [freeProp, freeGroup_zero]
  rfl

theorem hasDerivAt_freeProp (t : ℝ) :
    HasDerivAt M.freeProp ((-Complex.I) • (M.freeHam ∘L M.freeProp t)) t :=
  hasDerivAt_freeGroup M.energy M.measurable_energy M.cutoff_nonneg M.energy_le t

theorem continuous_freeProp : Continuous M.freeProp :=
  continuous_freeGroup M.energy M.measurable_energy M.cutoff_nonneg M.energy_le

theorem freeHam_comm (t : ℝ) : M.freeHam * M.freeProp t = M.freeProp t * M.freeHam :=
  freeHamiltonian_comp_freeGroup M.energy M.measurable_energy M.cutoff_nonneg M.energy_le t

theorem norm_evol_apply (lam t : ℝ) (f : Lp ℂ 2 μ) : ‖M.evol lam t f‖ = ‖f‖ :=
  norm_propagator_apply (M.isSelfAdjoint_ham lam) t f

theorem hasDerivAt_evol (lam t : ℝ) :
    HasDerivAt (M.evol lam) ((-Complex.I) • (M.ham lam ∘L M.evol lam t)) t :=
  hasDerivAt_propagator (M.ham lam) t

@[simp] theorem evol_zero (lam : ℝ) : M.evol lam 0 = 1 := propagator_zero _

theorem continuous_evol (lam : ℝ) : Continuous (M.evol lam) := continuous_propagator _

/-! ## Duhamel's formula -/

/-- The integrand of Duhamel's formula. -/
def duhamelIntegrand (lam t s : ℝ) : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ :=
  (-Complex.I * (lam : ℂ)) • (M.freeProp (t - s) * (M.coupling * M.evol lam s))

theorem continuous_duhamelIntegrand (lam t : ℝ) : Continuous (M.duhamelIntegrand lam t) := by
  unfold duhamelIntegrand
  have hsub : Continuous fun r : ℝ => t - r := by fun_prop
  have h1 : Continuous fun s : ℝ => M.freeProp (t - s) * (M.coupling * M.evol lam s) :=
    (M.continuous_freeProp.comp hsub).mul (continuous_const.mul (M.continuous_evol lam))
  exact h1.const_smul (-Complex.I * (lam : ℂ))

theorem hasDerivAt_duhamel (lam t s : ℝ) :
    HasDerivAt (fun r : ℝ => M.freeProp (t - r) * M.evol lam r) (M.duhamelIntegrand lam t s) s := by
  have hA : HasDerivAt (fun r : ℝ => M.freeProp (t - r))
      (Complex.I • (M.freeHam * M.freeProp (t - s))) s := by
    have h1 : HasDerivAt (fun r : ℝ => t - r) (-1) s := by
      simpa using (hasDerivAt_id s).const_sub t
    have h3 := (M.hasDerivAt_freeProp (t - s)).scomp s h1
    have h4 : ((-1 : ℝ) • ((-Complex.I) • (M.freeHam ∘L M.freeProp (t - s))))
        = Complex.I • (M.freeHam * M.freeProp (t - s)) := by
      rw [neg_one_smul, ← neg_smul, neg_neg]
      rfl
    rw [h4] at h3
    exact h3
  have hB := M.hasDerivAt_evol lam s
  have hmul := hA.mul hB
  have hcomm := M.freeHam_comm (t - s)
  have e1 : (Complex.I • (M.freeHam * M.freeProp (t - s))) * M.evol lam s
      = Complex.I • (M.freeProp (t - s) * M.freeHam * M.evol lam s) := by
    rw [smul_mul_assoc, hcomm]
  have e2 : M.freeProp (t - s) * ((-Complex.I) • (M.ham lam * M.evol lam s))
      = (-Complex.I) • (M.freeProp (t - s) * M.freeHam * M.evol lam s)
        + (-Complex.I * (lam : ℂ)) • (M.freeProp (t - s) * (M.coupling * M.evol lam s)) := by
    rw [ham, mul_smul_comm, add_mul, mul_add, smul_add, ← mul_assoc, smul_mul_assoc,
      mul_smul_comm, smul_smul]
  have key : (Complex.I • (M.freeHam * M.freeProp (t - s))) * M.evol lam s
      + M.freeProp (t - s) * ((-Complex.I) • (M.ham lam * M.evol lam s))
      = M.duhamelIntegrand lam t s := by
    rw [e1, e2, ← add_assoc, ← add_smul]
    simp only [duhamelIntegrand]
    simp
  rw [← key]
  exact hmul

/-- **Duhamel's formula.**  The exact integral equation relating the interacting and free
propagators. -/
theorem duhamel (lam t : ℝ) :
    M.evol lam t - M.freeProp t = ∫ s in (0 : ℝ)..t, M.duhamelIntegrand lam t s := by
  have hderiv : ∀ s ∈ Set.uIcc (0 : ℝ) t,
      HasDerivAt (fun r : ℝ => M.freeProp (t - r) * M.evol lam r)
        (M.duhamelIntegrand lam t s) s := fun s _ => M.hasDerivAt_duhamel lam t s
  have hcont := M.continuous_duhamelIntegrand lam t
  have hfin := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv
    (hcont.intervalIntegrable 0 t)
  rw [hfin]
  simp

theorem duhamel_apply (lam t : ℝ) (f : Lp ℂ 2 μ) :
    M.evol lam t f - M.freeProp t f = ∫ s in (0 : ℝ)..t, (M.duhamelIntegrand lam t s) f := by
  have hcont := M.continuous_duhamelIntegrand lam t
  rw [← ContinuousLinearMap.intervalIntegral_apply (hcont.intervalIntegrable 0 t) f,
    ← M.duhamel lam t]
  simp

omit M in
theorem norm_neg_I_mul_ofReal (lam : ℝ) : ‖(-Complex.I * (lam : ℂ))‖ = |lam| := by
  rw [norm_mul, norm_neg, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs]

theorem norm_duhamelIntegrand_apply_le (lam t s : ℝ) (f : Lp ℂ 2 μ) :
    ‖(M.duhamelIntegrand lam t s) f‖ ≤ |lam| * ‖M.coupling‖ * ‖f‖ := by
  have hval : (M.duhamelIntegrand lam t s) f
      = (-Complex.I * (lam : ℂ)) • (M.freeProp (t - s) (M.coupling (M.evol lam s f))) := rfl
  rw [hval, norm_smul, norm_neg_I_mul_ofReal, M.norm_freeProp_apply]
  calc |lam| * ‖M.coupling (M.evol lam s f)‖
      ≤ |lam| * (‖M.coupling‖ * ‖M.evol lam s f‖) :=
        mul_le_mul_of_nonneg_left (M.coupling.le_opNorm _) (abs_nonneg _)
    _ = |lam| * ‖M.coupling‖ * ‖f‖ := by rw [M.norm_evol_apply]; ring

/-- **First-order estimate.**  The interacting and free evolutions of the bound state separate at
most linearly in time. -/
theorem norm_evol_sub_freeProp_le (lam : ℝ) {t : ℝ} (ht : 0 ≤ t) :
    ‖M.evol lam t M.bound - M.freeProp t M.bound‖ ≤ |lam| * ‖M.coupling‖ * t := by
  rw [M.duhamel_apply lam t M.bound]
  have hb : ∀ s ∈ Set.uIoc (0 : ℝ) t,
      ‖(M.duhamelIntegrand lam t s) M.bound‖ ≤ |lam| * ‖M.coupling‖ := by
    intro s _
    have h := M.norm_duhamelIntegrand_apply_le lam t s M.bound
    rwa [M.norm_bound, mul_one] at h
  have h := intervalIntegral.norm_integral_le_of_norm_le_const hb
  simpa [abs_of_nonneg ht] using h

/-! ## The first-order Dyson term -/

/-- The first-order Dyson term, in closed form. -/
def firstOrder (lam t : ℝ) : Lp ℂ 2 μ :=
  (-Complex.I * (lam : ℂ)) •
    (M.freeProp t (ampOp M.level M.energy M.measurable_energy t M.form))

theorem firstOrder_eq (lam t : ℝ) :
    M.firstOrder lam t
      = ∫ s in (0 : ℝ)..t, (-Complex.I * (lam : ℂ)) •
          (M.freeProp (t - s) (M.coupling (M.freeProp s M.bound))) := by
  have hpt : ∀ s : ℝ,
      (-Complex.I * (lam : ℂ)) • (M.freeProp (t - s) (M.coupling (M.freeProp s M.bound)))
        = (-Complex.I * (lam : ℂ)) •
          (M.freeProp t ((intOp M.level M.energy M.measurable_energy s) M.form)) := by
    intro s
    congr 1
    rw [M.freeProp_bound s, map_smul, M.coupling_bound, map_smul,
      show t - s = t + (-s) by ring, ← M.freeProp_comp t (-s)]
    have hint : (intOp M.level M.energy M.measurable_energy s) M.form
        = Complex.exp (((-(s * M.level) : ℝ) : ℂ) * Complex.I) •
          ((freeGroup M.energy M.measurable_energy (-s)) M.form) := rfl
    rw [hint, map_smul]
    rfl
  have hcong : (∫ s in (0 : ℝ)..t, (-Complex.I * (lam : ℂ)) •
        (M.freeProp (t - s) (M.coupling (M.freeProp s M.bound))))
      = ∫ s in (0 : ℝ)..t, (-Complex.I * (lam : ℂ)) •
          (M.freeProp t ((intOp M.level M.energy M.measurable_energy s) M.form)) :=
    intervalIntegral.integral_congr fun s _ => hpt s
  have hcontint : Continuous fun s : ℝ =>
      (intOp (μ := μ) M.level M.energy M.measurable_energy s) M.form :=
    (continuous_intOp M.level M.energy M.measurable_energy M.cutoff_nonneg M.energy_le).clm_apply
      continuous_const
  rw [hcong, intervalIntegral.integral_smul,
    ContinuousLinearMap.intervalIntegral_comp_comm (M.freeProp t)
      (hcontint.intervalIntegrable 0 t),
    integral_intOp_apply M.level M.energy M.measurable_energy M.cutoff_nonneg M.energy_le t M.form,
    firstOrder]

/-- **The first-order transition probability.**  It is the golden-rule kernel integrated against the
form-factor density. -/
theorem normSq_firstOrder (lam t : ℝ) :
    ‖M.firstOrder lam t‖ ^ (2 : ℕ)
      = lam ^ (2 : ℕ) * ∫ x, goldenRuleKernel t (M.energy x - M.level) * ‖(M.form : α → ℂ) x‖ ^ (2 : ℕ) ∂μ := by
  rw [firstOrder, norm_smul, norm_neg_I_mul_ofReal, M.norm_freeProp_apply, mul_pow, sq_abs,
    norm_sq_ampOp_apply]

/-- **Second-order remainder.**  The true evolution agrees with the first-order Dyson term up to
`λ² ‖V‖² t²`. -/
theorem norm_sub_firstOrder_le (lam : ℝ) {t : ℝ} (ht : 0 ≤ t) :
    ‖M.evol lam t M.bound - M.freeProp t M.bound - M.firstOrder lam t‖
      ≤ lam ^ (2 : ℕ) * ‖M.coupling‖ ^ (2 : ℕ) * t ^ (2 : ℕ) := by
  have hcont1 : Continuous fun s : ℝ => (M.duhamelIntegrand lam t s) M.bound :=
    (M.continuous_duhamelIntegrand lam t).clm_apply continuous_const
  have hcont2 : Continuous fun s : ℝ => (-Complex.I * (lam : ℂ)) •
      (M.freeProp (t - s) (M.coupling (M.freeProp s M.bound))) := by
    have hsub : Continuous fun r : ℝ => t - r := by fun_prop
    have h1 : Continuous fun s : ℝ =>
        M.freeProp (t - s) (M.coupling (M.freeProp s M.bound)) := by
      refine Continuous.clm_apply (M.continuous_freeProp.comp hsub) ?_
      exact M.coupling.continuous.comp (M.continuous_freeProp.clm_apply continuous_const)
    exact h1.const_smul (-Complex.I * (lam : ℂ))
  rw [M.duhamel_apply lam t M.bound, M.firstOrder_eq lam t,
    ← intervalIntegral.integral_sub (hcont1.intervalIntegrable 0 t)
      (hcont2.intervalIntegrable 0 t)]
  have hb : ∀ s ∈ Set.uIoc (0 : ℝ) t,
      ‖(M.duhamelIntegrand lam t s) M.bound
        - (-Complex.I * (lam : ℂ)) • (M.freeProp (t - s) (M.coupling (M.freeProp s M.bound)))‖
      ≤ lam ^ (2 : ℕ) * ‖M.coupling‖ ^ (2 : ℕ) * t := by
    intro s hs
    rw [Set.uIoc_of_le ht] at hs
    have hs0 : 0 ≤ s := le_of_lt hs.1
    have hdiff : (M.duhamelIntegrand lam t s) M.bound
        - (-Complex.I * (lam : ℂ)) • (M.freeProp (t - s) (M.coupling (M.freeProp s M.bound)))
        = (-Complex.I * (lam : ℂ)) • (M.freeProp (t - s)
            (M.coupling (M.evol lam s M.bound - M.freeProp s M.bound))) := by
      have hval : (M.duhamelIntegrand lam t s) M.bound
          = (-Complex.I * (lam : ℂ)) •
            (M.freeProp (t - s) (M.coupling (M.evol lam s M.bound))) := rfl
      rw [hval, ← smul_sub, map_sub, map_sub]
    rw [hdiff, norm_smul, norm_neg_I_mul_ofReal, M.norm_freeProp_apply]
    have h1 : ‖M.coupling (M.evol lam s M.bound - M.freeProp s M.bound)‖
        ≤ ‖M.coupling‖ * (|lam| * ‖M.coupling‖ * s) :=
      le_trans (M.coupling.le_opNorm _)
        (mul_le_mul_of_nonneg_left (M.norm_evol_sub_freeProp_le lam hs0) (norm_nonneg _))
    have h2 : |lam| * ‖M.coupling (M.evol lam s M.bound - M.freeProp s M.bound)‖
        ≤ |lam| * (‖M.coupling‖ * (|lam| * ‖M.coupling‖ * s)) :=
      mul_le_mul_of_nonneg_left h1 (abs_nonneg _)
    have h3 : |lam| * (‖M.coupling‖ * (|lam| * ‖M.coupling‖ * s))
        ≤ lam ^ (2 : ℕ) * ‖M.coupling‖ ^ (2 : ℕ) * t := by
      have hla : |lam| * |lam| = lam ^ (2 : ℕ) := by
        rw [← abs_mul, abs_of_nonneg (mul_self_nonneg lam)]; ring
      have heq : |lam| * (‖M.coupling‖ * (|lam| * ‖M.coupling‖ * s))
          = lam ^ (2 : ℕ) * ‖M.coupling‖ ^ (2 : ℕ) * s := by
        rw [← hla]; ring
      rw [heq]
      exact mul_le_mul_of_nonneg_left hs.2 (by positivity)
    linarith
  have h := intervalIntegral.norm_integral_le_of_norm_le_const hb
  have hfin : lam ^ (2 : ℕ) * ‖M.coupling‖ ^ (2 : ℕ) * t * |t - 0| = lam ^ (2 : ℕ) * ‖M.coupling‖ ^ (2 : ℕ) * t ^ (2 : ℕ) := by
    rw [sub_zero, abs_of_nonneg ht]
    ring
  rw [hfin] at h
  exact h

/-- **The exact transition amplitude out of the initial state agrees with the first-order Dyson
term to second order in the coupling.** -/
theorem abs_norm_sub_norm_firstOrder_le (lam : ℝ) {t : ℝ} (ht : 0 ≤ t) :
    |‖M.evol lam t M.bound - M.freeProp t M.bound‖ - ‖M.firstOrder lam t‖|
      ≤ lam ^ (2 : ℕ) * ‖M.coupling‖ ^ (2 : ℕ) * t ^ (2 : ℕ) :=
  le_trans (abs_norm_sub_norm_le _ _) (M.norm_sub_firstOrder_le lam ht)

/-! ## Fermi's golden rule -/

/-- **Fermi's golden rule.**  If the spectral measure of the form factor has an integrable density
`ρ` continuous at the unperturbed level, the first-order transition probability grows linearly with
rate `2 π λ² ρ(E₀)`. -/
theorem tendsto_normSq_firstOrder (lam : ℝ) {ρ : ℝ → ℝ} (hρ : Integrable ρ (volume : Measure ℝ))
    (hc : ContinuousAt ρ M.level)
    (hdens : ∀ t : ℝ,
      (∫ x, goldenRuleKernel t (M.energy x - M.level) * ‖(M.form : α → ℂ) x‖ ^ (2 : ℕ) ∂μ)
        = ∫ E : ℝ, goldenRuleKernel t (E - M.level) * ρ E) :
    Filter.Tendsto (fun t : ℝ => ‖M.firstOrder lam t‖ ^ (2 : ℕ) / t) Filter.atTop
      (nhds (2 * Real.pi * lam ^ (2 : ℕ) * ρ M.level)) := by
  have heq : ∀ t : ℝ, ‖M.firstOrder lam t‖ ^ (2 : ℕ) / t
      = lam ^ (2 : ℕ) * ((∫ E : ℝ, goldenRuleKernel t (E - M.level) * ρ E) / t) := by
    intro t
    rw [M.normSq_firstOrder lam t, hdens t]
    ring
  have h3 : Filter.Tendsto
      (fun t : ℝ => lam ^ (2 : ℕ) * ((∫ E : ℝ, goldenRuleKernel t (E - M.level) * ρ E) / t))
      Filter.atTop (nhds (lam ^ (2 : ℕ) * (2 * Real.pi * ρ M.level))) :=
    (tendsto_goldenRuleKernel_density hρ hc).const_mul _
  have hval : lam ^ (2 : ℕ) * (2 * Real.pi * ρ M.level) = 2 * Real.pi * lam ^ (2 : ℕ) * ρ M.level := by ring
  rw [← hval]
  exact h3.congr fun t => (heq t).symm

end FriedrichsModel

end GaloisForLFunctions.HTGeometry
