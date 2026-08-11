import GaloisForLFunctions.RHTower.RouteEWeightedHallANOVA

/-!
# Route E physical-fibre coarea and conditional projection

This file constructs the exact finite conditional kernel carried by a physical fibre.  Unlike a
uniform orbit shuffle, the transition uses the original physical law inside every fibre.  Hence it
is simultaneously row stochastic, reversible, stationary, and idempotent, with no comparison
between physical and counting measure.

The same construction gives an exact coarea formula for the projected signed energy, an orthogonal
variance decomposition, and the sharp Cauchy endpoint controlling the signed mean.  These are the
finite algebraic laws needed before specializing the label to a replica product.
-/

namespace RHTower

open scoped BigOperators

noncomputable section

/-- A strictly positive finite physical probability law, an observable, and a surjective fibre
label.  Surjectivity makes every declared fibre physical; strict positivity then makes every fibre
mass nonzero, so no artificial convention at empty cells enters the kernel. -/
structure RouteEPhysicalFibreData (Ω Λ : Type*) [Fintype Ω] [Fintype Λ] where
  mass : Ω → ℝ
  observable : Ω → ℝ
  label : Ω → Λ
  mass_pos : ∀ ω, 0 < mass ω
  mass_sum : ∑ ω, mass ω = 1
  label_surjective : Function.Surjective label

namespace RouteEPhysicalFibreData

variable {Ω Λ : Type*} [Fintype Ω] [Fintype Λ] [DecidableEq Λ]

/-- Physical mass of one label fibre. -/
def fibreMass (D : RouteEPhysicalFibreData Ω Λ) (l : Λ) : ℝ :=
  ∑ ω with D.label ω = l, D.mass ω

/-- Observable moment carried by one label fibre. -/
def fibreMoment (D : RouteEPhysicalFibreData Ω Λ) (l : Λ) : ℝ :=
  ∑ ω with D.label ω = l, D.mass ω * D.observable ω

/-- Conditional observable mean on a physical fibre. -/
def conditionalMean (D : RouteEPhysicalFibreData Ω Λ) (l : Λ) : ℝ :=
  D.fibreMoment l / D.fibreMass l

/-- Conditional projection of the observable back to the physical state space. -/
def projection (D : RouteEPhysicalFibreData Ω Λ) (ω : Ω) : ℝ :=
  D.conditionalMean (D.label ω)

/-- Physical conditional kernel: resample from the original law inside the same fibre. -/
def conditionalKernel (D : RouteEPhysicalFibreData Ω Λ) (ω η : Ω) : ℝ :=
  if D.label ω = D.label η then D.mass η / D.fibreMass (D.label ω) else 0

/-- Squared norm of the conditional projection. -/
def projectedEnergy (D : RouteEPhysicalFibreData Ω Λ) : ℝ :=
  ∑ ω, D.mass ω * D.projection ω ^ 2

/-- Energy lost after conditioning on the fibre label. -/
def residualEnergy (D : RouteEPhysicalFibreData Ω Λ) : ℝ :=
  ∑ ω, D.mass ω * (D.observable ω - D.projection ω) ^ 2

theorem fibreMass_pos (D : RouteEPhysicalFibreData Ω Λ) (l : Λ) :
    0 < D.fibreMass l := by
  classical
  obtain ⟨ω, hω⟩ := D.label_surjective l
  have hmem : ω ∈ (Finset.univ.filter fun η => D.label η = l) := by
    simp [hω]
  have hle : D.mass ω ≤ ∑ η ∈ (Finset.univ.filter fun η => D.label η = l), D.mass η :=
    Finset.single_le_sum (fun η _ => (D.mass_pos η).le) hmem
  exact lt_of_lt_of_le (D.mass_pos ω) (by simpa [fibreMass] using hle)

theorem fibreMass_ne_zero (D : RouteEPhysicalFibreData Ω Λ) (l : Λ) :
    D.fibreMass l ≠ 0 :=
  ne_of_gt (D.fibreMass_pos l)

theorem sum_fibreMass (D : RouteEPhysicalFibreData Ω Λ) :
    ∑ l, D.fibreMass l = 1 := by
  classical
  calc
    (∑ l, D.fibreMass l) = ∑ ω, D.mass ω := by
      simpa only [fibreMass] using
        (Finset.sum_fiberwise (Finset.univ : Finset Ω) D.label D.mass)
    _ = 1 := D.mass_sum

theorem sum_fibreMoment (D : RouteEPhysicalFibreData Ω Λ) :
    ∑ l, D.fibreMoment l = ∑ ω, D.mass ω * D.observable ω := by
  classical
  simpa only [fibreMoment] using
    (Finset.sum_fiberwise (Finset.univ : Finset Ω) D.label
      (fun ω => D.mass ω * D.observable ω))

theorem conditionalKernel_nonneg (D : RouteEPhysicalFibreData Ω Λ) (ω η : Ω) :
    0 ≤ D.conditionalKernel ω η := by
  rw [conditionalKernel]
  split_ifs
  · exact div_nonneg (D.mass_pos η).le (D.fibreMass_pos _).le
  · exact le_rfl

/-- Exact row stochasticity under the physical, rather than uniform, fibre law. -/
theorem conditionalKernel_row_sum (D : RouteEPhysicalFibreData Ω Λ) (ω : Ω) :
    ∑ η, D.conditionalKernel ω η = 1 := by
  classical
  calc
    (∑ η, D.conditionalKernel ω η) =
        (∑ η with D.label η = D.label ω, D.mass η) / D.fibreMass (D.label ω) := by
      unfold conditionalKernel
      rw [Finset.sum_div, Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro η _hη
      by_cases h : D.label η = D.label ω
      · rw [if_pos h.symm, if_pos h]
      · rw [if_neg (Ne.symm h), if_neg h]
    _ = 1 := by
      rw [show (∑ η with D.label η = D.label ω, D.mass η) =
        D.fibreMass (D.label ω) by rfl]
      exact div_self (D.fibreMass_ne_zero _)

/-- Detailed balance is exact because the same physical fibre mass normalizes both directions. -/
theorem conditionalKernel_detailedBalance
    (D : RouteEPhysicalFibreData Ω Λ) (ω η : Ω) :
    D.mass ω * D.conditionalKernel ω η =
      D.mass η * D.conditionalKernel η ω := by
  classical
  by_cases h : D.label ω = D.label η
  · unfold conditionalKernel
    rw [if_pos h, if_pos h.symm]
    rw [h]
    ring
  · unfold conditionalKernel
    rw [if_neg h, if_neg (Ne.symm h)]
    ring

/-- The original physical law is stationary for conditional resampling. -/
theorem conditionalKernel_stationary (D : RouteEPhysicalFibreData Ω Λ) (η : Ω) :
    ∑ ω, D.mass ω * D.conditionalKernel ω η = D.mass η := by
  classical
  calc
    (∑ ω, D.mass ω * D.conditionalKernel ω η) =
        ∑ ω, D.mass η * D.conditionalKernel η ω := by
      apply Finset.sum_congr rfl
      intro ω _hω
      exact D.conditionalKernel_detailedBalance ω η
    _ = D.mass η * ∑ ω, D.conditionalKernel η ω := by rw [Finset.mul_sum]
    _ = D.mass η := by rw [D.conditionalKernel_row_sum]; ring

theorem conditionalKernel_eq_of_same_source_label
    (D : RouteEPhysicalFibreData Ω Λ) {ω ξ : Ω}
    (h : D.label ω = D.label ξ) (η : Ω) :
    D.conditionalKernel ξ η = D.conditionalKernel ω η := by
  classical
  unfold conditionalKernel
  rw [← h]

/-- Conditional resampling is an exact projection kernel. -/
theorem conditionalKernel_idempotent (D : RouteEPhysicalFibreData Ω Λ) (ω η : Ω) :
    ∑ ξ, D.conditionalKernel ω ξ * D.conditionalKernel ξ η =
      D.conditionalKernel ω η := by
  classical
  calc
    (∑ ξ, D.conditionalKernel ω ξ * D.conditionalKernel ξ η) =
        ∑ ξ, D.conditionalKernel ω ξ * D.conditionalKernel ω η := by
      apply Finset.sum_congr rfl
      intro ξ _hξ
      by_cases h : D.label ω = D.label ξ
      · rw [D.conditionalKernel_eq_of_same_source_label h η]
      · simp [conditionalKernel, h]
    _ = (∑ ξ, D.conditionalKernel ω ξ) * D.conditionalKernel ω η := by
      rw [Finset.sum_mul]
    _ = D.conditionalKernel ω η := by rw [D.conditionalKernel_row_sum, one_mul]

/-- Kernel averaging is exactly conditional projection. -/
theorem conditionalKernel_average_observable
    (D : RouteEPhysicalFibreData Ω Λ) (ω : Ω) :
    ∑ η, D.conditionalKernel ω η * D.observable η = D.projection ω := by
  classical
  calc
    (∑ η, D.conditionalKernel ω η * D.observable η) =
        (∑ η with D.label η = D.label ω,
          D.mass η * D.observable η) / D.fibreMass (D.label ω) := by
      unfold conditionalKernel
      rw [Finset.sum_div, Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro η _hη
      by_cases h : D.label η = D.label ω
      · rw [if_pos h.symm, if_pos h]
        ring
      · rw [if_neg (Ne.symm h), if_neg h]
        ring
    _ = D.projection ω := by rfl

/-- A projected observable is fixed pointwise by a second conditional resampling. -/
theorem conditionalKernel_average_projection
    (D : RouteEPhysicalFibreData Ω Λ) (ω : Ω) :
    ∑ η, D.conditionalKernel ω η * D.projection η = D.projection ω := by
  classical
  calc
    (∑ η, D.conditionalKernel ω η * D.projection η) =
        ∑ η, D.conditionalKernel ω η * D.projection ω := by
      apply Finset.sum_congr rfl
      intro η _hη
      by_cases h : D.label ω = D.label η
      · simp only [projection]
        rw [← h]
      · simp [conditionalKernel, h]
    _ = (∑ η, D.conditionalKernel ω η) * D.projection ω := by rw [Finset.sum_mul]
    _ = D.projection ω := by rw [D.conditionalKernel_row_sum, one_mul]

theorem fibre_centered_sum (D : RouteEPhysicalFibreData Ω Λ) (l : Λ) :
    ∑ ω with D.label ω = l,
      D.mass ω * (D.observable ω - D.conditionalMean l) = 0 := by
  classical
  simp_rw [mul_sub]
  rw [Finset.sum_sub_distrib, ← Finset.sum_mul]
  change D.fibreMoment l - D.fibreMass l *
    (D.fibreMoment l / D.fibreMass l) = 0
  field_simp [D.fibreMass_ne_zero l]
  ring

/-- Conditional residuals are orthogonal to every function of the fibre label. -/
theorem projection_orthogonal
    (D : RouteEPhysicalFibreData Ω Λ) (h : Λ → ℝ) :
    ∑ ω, D.mass ω * (D.observable ω - D.projection ω) * h (D.label ω) = 0 := by
  classical
  calc
    (∑ ω, D.mass ω * (D.observable ω - D.projection ω) * h (D.label ω)) =
        ∑ l, ∑ ω with D.label ω = l,
          D.mass ω * (D.observable ω - D.projection ω) * h (D.label ω) :=
      (Finset.sum_fiberwise (Finset.univ : Finset Ω) D.label _).symm
    _ = 0 := by
      apply Finset.sum_eq_zero
      intro l _hl
      calc
        (∑ ω with D.label ω = l,
            D.mass ω * (D.observable ω - D.projection ω) * h (D.label ω)) =
            (∑ ω with D.label ω = l,
              D.mass ω * (D.observable ω - D.conditionalMean l)) * h l := by
          rw [Finset.sum_mul]
          apply Finset.sum_congr rfl
          intro ω hω
          have hlabel := (Finset.mem_filter.mp hω).2
          simp only [projection]
          rw [hlabel]
        _ = 0 := by rw [D.fibre_centered_sum, zero_mul]

/-- The total signed mean is unchanged by conditional projection. -/
theorem mean_projection (D : RouteEPhysicalFibreData Ω Λ) :
    ∑ ω, D.mass ω * D.projection ω =
      ∑ ω, D.mass ω * D.observable ω := by
  have h := D.projection_orthogonal (fun _ => 1)
  simp only [mul_one] at h
  have heq : (∑ ω, D.mass ω * D.observable ω) -
      ∑ ω, D.mass ω * D.projection ω = 0 := by
    rw [← Finset.sum_sub_distrib]
    convert h using 1 <;> apply Finset.sum_congr rfl <;> intro ω _hω <;> ring
  linarith

/-- Exact fibre-coarea expression for conditional signed energy. -/
theorem projectedEnergy_eq_fibreQuotient (D : RouteEPhysicalFibreData Ω Λ) :
    D.projectedEnergy = ∑ l, D.fibreMoment l ^ 2 / D.fibreMass l := by
  classical
  unfold projectedEnergy
  calc
    (∑ ω, D.mass ω * D.projection ω ^ 2) =
        ∑ l, ∑ ω with D.label ω = l, D.mass ω * D.projection ω ^ 2 :=
      (Finset.sum_fiberwise (Finset.univ : Finset Ω) D.label _).symm
    _ = ∑ l, D.fibreMoment l ^ 2 / D.fibreMass l := by
      apply Finset.sum_congr rfl
      intro l _hl
      calc
        (∑ ω with D.label ω = l, D.mass ω * D.projection ω ^ 2) =
            (∑ ω with D.label ω = l,
              D.mass ω * D.conditionalMean l ^ 2) := by
          apply Finset.sum_congr rfl
          intro ω hω
          have hlabel := (Finset.mem_filter.mp hω).2
          simp only [projection]
          rw [hlabel]
        _ = D.fibreMass l * D.conditionalMean l ^ 2 := by
          rw [← Finset.sum_mul]
          rfl
        _ = D.fibreMoment l ^ 2 / D.fibreMass l := by
          unfold conditionalMean
          field_simp [D.fibreMass_ne_zero l]

theorem projectedEnergy_nonneg (D : RouteEPhysicalFibreData Ω Λ) :
    0 ≤ D.projectedEnergy :=
  Finset.sum_nonneg fun ω _hω => mul_nonneg (D.mass_pos ω).le (sq_nonneg _)

theorem residualEnergy_nonneg (D : RouteEPhysicalFibreData Ω Λ) :
    0 ≤ D.residualEnergy :=
  Finset.sum_nonneg fun ω _hω => mul_nonneg (D.mass_pos ω).le (sq_nonneg _)

/-- Exact conditional ANOVA: total observable energy is projected energy plus fibre variance. -/
theorem totalEnergy_eq_projected_add_residual (D : RouteEPhysicalFibreData Ω Λ) :
    (∑ ω, D.mass ω * D.observable ω ^ 2) =
      D.projectedEnergy + D.residualEnergy := by
  have hcross := D.projection_orthogonal D.conditionalMean
  change (∑ ω, D.mass ω * (D.observable ω - D.projection ω) * D.projection ω) = 0
    at hcross
  unfold projectedEnergy residualEnergy
  calc
    (∑ ω, D.mass ω * D.observable ω ^ 2) =
        ∑ ω, (D.mass ω * D.projection ω ^ 2 +
          D.mass ω * (D.observable ω - D.projection ω) ^ 2 +
          2 * (D.mass ω * (D.observable ω - D.projection ω) * D.projection ω)) := by
      apply Finset.sum_congr rfl
      intro ω _hω
      ring
    _ = (∑ ω, D.mass ω * D.projection ω ^ 2) +
          (∑ ω, D.mass ω * (D.observable ω - D.projection ω) ^ 2) +
          2 * ∑ ω,
            D.mass ω * (D.observable ω - D.projection ω) * D.projection ω := by
      rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum]
    _ = _ := by rw [hcross]; ring

/-- Weighted finite Cauchy--Schwarz for the projected signed mean. -/
theorem mean_sq_le_projectedEnergy (D : RouteEPhysicalFibreData Ω Λ) :
    (∑ ω, D.mass ω * D.observable ω) ^ 2 ≤ D.projectedEnergy := by
  classical
  rw [← D.mean_projection]
  let u : Ω → ℝ := fun ω => Real.sqrt (D.mass ω)
  let v : Ω → ℝ := fun ω => Real.sqrt (D.mass ω) * D.projection ω
  have hcs : (∑ ω, u ω * v ω) ^ 2 ≤
      (∑ ω, u ω ^ 2) * ∑ ω, v ω ^ 2 := by
    exact Finset.sum_mul_sq_le_sq_mul_sq (s := (Finset.univ : Finset Ω))
      (f := u) (g := v)
  have hu : ∑ ω, u ω ^ 2 = 1 := by
    simp only [u, Real.sq_sqrt (D.mass_pos _).le]
    exact D.mass_sum
  have hv : ∑ ω, v ω ^ 2 = D.projectedEnergy := by
    unfold projectedEnergy v
    apply Finset.sum_congr rfl
    intro ω _hω
    rw [mul_pow, Real.sq_sqrt (D.mass_pos ω).le]
  have huv : ∑ ω, u ω * v ω = ∑ ω, D.mass ω * D.projection ω := by
    apply Finset.sum_congr rfl
    intro ω _hω
    unfold u v
    rw [← mul_assoc, ← sq]
    rw [Real.sq_sqrt (D.mass_pos ω).le]
  rw [huv, hu, hv, one_mul] at hcs
  exact hcs

/-- Sharp conditional Cauchy endpoint in the form used by Route E. -/
theorem abs_mean_le_sqrt_projectedEnergy (D : RouteEPhysicalFibreData Ω Λ) :
    |∑ ω, D.mass ω * D.observable ω| ≤ Real.sqrt D.projectedEnergy := by
  have hsq := D.mean_sq_le_projectedEnergy
  have hD := D.projectedEnergy_nonneg
  have hsqrt := Real.sqrt_nonneg D.projectedEnergy
  have hsq' : |∑ ω, D.mass ω * D.observable ω| ^ 2 ≤
      (Real.sqrt D.projectedEnergy) ^ 2 := by
    rw [sq_abs, Real.sq_sqrt hD]
    exact hsq
  exact (sq_le_sq₀ (abs_nonneg _) hsqrt).mp hsq'

/-! ## Exact loss under coarsening -/

/-- Replace the observable without changing physical law or fibre partition. -/
def replaceObservable (D : RouteEPhysicalFibreData Ω Λ) (f : Ω → ℝ) :
    RouteEPhysicalFibreData Ω Λ where
  mass := D.mass
  observable := f
  label := D.label
  mass_pos := D.mass_pos
  mass_sum := D.mass_sum
  label_surjective := D.label_surjective

/-- Coarsen a physical fibre label through a surjection. -/
def relabel {Γ : Type*} [Fintype Γ]
    (D : RouteEPhysicalFibreData Ω Λ) (π : Λ → Γ)
    (hπ : Function.Surjective π) : RouteEPhysicalFibreData Ω Γ where
  mass := D.mass
  observable := D.observable
  label := π ∘ D.label
  mass_pos := D.mass_pos
  mass_sum := D.mass_sum
  label_surjective := hπ.comp D.label_surjective

theorem relabel_fibreMoment_projection
    {Γ : Type*} [Fintype Γ] [DecidableEq Γ]
    (D : RouteEPhysicalFibreData Ω Λ) (π : Λ → Γ)
    (hπ : Function.Surjective π) (g : Γ) :
    (D.relabel π hπ).fibreMoment g =
      ((D.replaceObservable D.projection).relabel π hπ).fibreMoment g := by
  classical
  have hortho := D.projection_orthogonal (fun l => if π l = g then 1 else 0)
  have hfiltered :
      (∑ ω with π (D.label ω) = g,
        D.mass ω * (D.observable ω - D.projection ω)) = 0 := by
    rw [Finset.sum_filter]
    simpa only [mul_ite, mul_one, mul_zero] using hortho
  rw [← sub_eq_zero]
  change (∑ ω with π (D.label ω) = g, D.mass ω * D.observable ω) -
      (∑ ω with π (D.label ω) = g, D.mass ω * D.projection ω) = 0
  rw [← Finset.sum_sub_distrib]
  convert hfiltered using 1 <;> apply Finset.sum_congr rfl <;> intro ω _hω <;> ring

theorem relabel_conditionalMean_projection
    {Γ : Type*} [Fintype Γ] [DecidableEq Γ]
    (D : RouteEPhysicalFibreData Ω Λ) (π : Λ → Γ)
    (hπ : Function.Surjective π) (g : Γ) :
    ((D.replaceObservable D.projection).relabel π hπ).conditionalMean g =
      (D.relabel π hπ).conditionalMean g := by
  unfold conditionalMean
  rw [← D.relabel_fibreMoment_projection π hπ g]
  rfl

/-- **Coarsening Pythagoras.**  Coarsening a physical label loses exactly the squared distance
between the fine and coarse conditional means.  This is the finite conditional-variance identity
with every physical weight retained. -/
theorem projectedEnergy_eq_relabel_add_defect
    {Γ : Type*} [Fintype Γ] [DecidableEq Γ]
    (D : RouteEPhysicalFibreData Ω Λ) (π : Λ → Γ)
    (hπ : Function.Surjective π) :
    D.projectedEnergy = (D.relabel π hπ).projectedEnergy +
      ∑ ω, D.mass ω *
        (D.projection ω - (D.relabel π hπ).projection ω) ^ 2 := by
  let P := (D.replaceObservable D.projection).relabel π hπ
  have hmeans : ∀ g, P.conditionalMean g = (D.relabel π hπ).conditionalMean g :=
    D.relabel_conditionalMean_projection π hπ
  have htotal := P.totalEnergy_eq_projected_add_residual
  have hPmass : ∀ ω, P.mass ω = D.mass ω := fun _ => rfl
  have hPobservable : ∀ ω, P.observable ω = D.projection ω := fun _ => rfl
  have hPprojection : ∀ ω, P.projection ω = (D.relabel π hπ).projection ω := by
    intro ω
    unfold projection
    exact hmeans _
  change D.projectedEnergy = (D.relabel π hπ).projectedEnergy +
      ∑ ω, D.mass ω *
        (D.projection ω - (D.relabel π hπ).projection ω) ^ 2
  calc
    D.projectedEnergy = ∑ ω, P.mass ω * P.observable ω ^ 2 := rfl
    _ = P.projectedEnergy + P.residualEnergy := htotal
    _ = (D.relabel π hπ).projectedEnergy +
        ∑ ω, D.mass ω *
          (D.projection ω - (D.relabel π hπ).projection ω) ^ 2 := by
      congr 1
      · unfold projectedEnergy
        apply Finset.sum_congr rfl
        intro ω _hω
        rw [hPmass, hPprojection]
        rfl
      · unfold residualEnergy
        apply Finset.sum_congr rfl
        intro ω _hω
        rw [hPmass, hPobservable, hPprojection]

theorem relabel_projectedEnergy_le
    {Γ : Type*} [Fintype Γ] [DecidableEq Γ]
    (D : RouteEPhysicalFibreData Ω Λ) (π : Λ → Γ)
    (hπ : Function.Surjective π) :
    (D.relabel π hπ).projectedEnergy ≤ D.projectedEnergy := by
  rw [D.projectedEnergy_eq_relabel_add_defect π hπ]
  exact le_add_of_nonneg_right
    (Finset.sum_nonneg fun ω _hω => mul_nonneg (D.mass_pos ω).le (sq_nonneg _))

/-! ## Independent physical extension before coarsening -/

/-- Adjoin one independent physical factor while retaining both the old fibre label and the new
factor.  This is the correct fine sigma-algebra for a convolution step. -/
def independentExtensionData
    {Y : Type*} [Fintype Y]
    (D : RouteEPhysicalFibreData Ω Λ) (factorMass : Y → ℝ)
    (factorMass_pos : ∀ y, 0 < factorMass y)
    (factorMass_sum : ∑ y, factorMass y = 1) :
    RouteEPhysicalFibreData (Ω × Y) (Λ × Y) where
  mass p := D.mass p.1 * factorMass p.2
  observable p := D.observable p.1
  label p := (D.label p.1, p.2)
  mass_pos p := mul_pos (D.mass_pos p.1) (factorMass_pos p.2)
  mass_sum := by
    rw [Fintype.sum_prod_type]
    simp_rw [← Finset.mul_sum, factorMass_sum, mul_one]
    exact D.mass_sum
  label_surjective := by
    rintro ⟨l, y⟩
    obtain ⟨ω, hω⟩ := D.label_surjective l
    exact ⟨(ω, y), by simp [hω]⟩

theorem independentExtension_fibreMass
    {Y : Type*} [Fintype Y] [DecidableEq Y]
    (D : RouteEPhysicalFibreData Ω Λ) (factorMass : Y → ℝ)
    (factorMass_pos : ∀ y, 0 < factorMass y)
    (factorMass_sum : ∑ y, factorMass y = 1) (l : Λ) (y : Y) :
    (D.independentExtensionData factorMass factorMass_pos factorMass_sum).fibreMass (l, y) =
      D.fibreMass l * factorMass y := by
  classical
  let E := D.independentExtensionData factorMass factorMass_pos factorMass_sum
  have hfibre :
      (Finset.univ.filter fun p : Ω × Y => E.label p = (l, y)) =
        (Finset.univ.filter fun ω : Ω => D.label ω = l) ×ˢ ({y} : Finset Y) := by
    ext p
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_product,
      Finset.mem_singleton]
    change ((D.label p.1, p.2) = (l, y)) ↔
      (D.label p.1 = l ∧ p.2 = y)
    exact Prod.ext_iff
  unfold fibreMass
  rw [hfibre, Finset.sum_product]
  simp only [E, independentExtensionData, Finset.sum_singleton]
  rw [← Finset.sum_mul]

theorem independentExtension_fibreMoment
    {Y : Type*} [Fintype Y] [DecidableEq Y]
    (D : RouteEPhysicalFibreData Ω Λ) (factorMass : Y → ℝ)
    (factorMass_pos : ∀ y, 0 < factorMass y)
    (factorMass_sum : ∑ y, factorMass y = 1) (l : Λ) (y : Y) :
    (D.independentExtensionData factorMass factorMass_pos factorMass_sum).fibreMoment (l, y) =
      D.fibreMoment l * factorMass y := by
  classical
  let E := D.independentExtensionData factorMass factorMass_pos factorMass_sum
  have hfibre :
      (Finset.univ.filter fun p : Ω × Y => E.label p = (l, y)) =
        (Finset.univ.filter fun ω : Ω => D.label ω = l) ×ˢ ({y} : Finset Y) := by
    ext p
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_product,
      Finset.mem_singleton]
    change ((D.label p.1, p.2) = (l, y)) ↔
      (D.label p.1 = l ∧ p.2 = y)
    exact Prod.ext_iff
  unfold fibreMoment
  rw [hfibre, Finset.sum_product]
  simp only [E, independentExtensionData, Finset.sum_singleton]
  calc
    (∑ x with D.label x = l, D.mass x * factorMass y * D.observable x) =
        ∑ x with D.label x = l, (D.mass x * D.observable x) * factorMass y := by
      apply Finset.sum_congr rfl
      intro ω _hω
      ring
    _ = (∑ ω with D.label ω = l, D.mass ω * D.observable ω) * factorMass y := by
      rw [Finset.sum_mul]

/-- Retaining the old label and the new independent factor leaves the conditional field unchanged. -/
theorem independentExtension_projection
    {Y : Type*} [Fintype Y] [DecidableEq Y]
    (D : RouteEPhysicalFibreData Ω Λ) (factorMass : Y → ℝ)
    (factorMass_pos : ∀ y, 0 < factorMass y)
    (factorMass_sum : ∑ y, factorMass y = 1) (ω : Ω) (y : Y) :
    (D.independentExtensionData factorMass factorMass_pos factorMass_sum).projection (ω, y) =
      D.projection ω := by
  unfold projection conditionalMean
  change
    (D.independentExtensionData factorMass factorMass_pos factorMass_sum).fibreMoment
        (D.label ω, y) /
      (D.independentExtensionData factorMass factorMass_pos factorMass_sum).fibreMass
        (D.label ω, y) =
      D.fibreMoment (D.label ω) / D.fibreMass (D.label ω)
  rw [D.independentExtension_fibreMoment factorMass factorMass_pos factorMass_sum,
    D.independentExtension_fibreMass factorMass factorMass_pos factorMass_sum]
  have hB : D.fibreMass (D.label ω) ≠ 0 := D.fibreMass_ne_zero _
  have hb : factorMass y ≠ 0 := ne_of_gt (factorMass_pos y)
  field_simp

/-- Independent extension preserves the fine conditional energy exactly. -/
theorem independentExtension_projectedEnergy
    {Y : Type*} [Fintype Y] [DecidableEq Y]
    (D : RouteEPhysicalFibreData Ω Λ) (factorMass : Y → ℝ)
    (factorMass_pos : ∀ y, 0 < factorMass y)
    (factorMass_sum : ∑ y, factorMass y = 1) :
    (D.independentExtensionData factorMass factorMass_pos factorMass_sum).projectedEnergy =
      D.projectedEnergy := by
  classical
  unfold projectedEnergy
  simp_rw [D.independentExtension_projection factorMass factorMass_pos factorMass_sum]
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro ω _hω
  change (∑ y, (D.mass ω * factorMass y) * D.projection ω ^ 2) =
    D.mass ω * D.projection ω ^ 2
  calc
    (∑ y, (D.mass ω * factorMass y) * D.projection ω ^ 2) =
        (D.mass ω * D.projection ω ^ 2) * ∑ y, factorMass y := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro y _hy
      ring
    _ = _ := by rw [factorMass_sum, mul_one]

/-- **Independent-extension coarsening law.**  Appending a physical factor and then forgetting down
to any surjective cell map dissipates exactly the squared reverse-factor discrepancy. -/
theorem independentExtension_projectedEnergy_eq_relabel_add_defect
    {Y Γ : Type*} [Fintype Y] [DecidableEq Y] [Fintype Γ] [DecidableEq Γ]
    (D : RouteEPhysicalFibreData Ω Λ) (factorMass : Y → ℝ)
    (factorMass_pos : ∀ y, 0 < factorMass y)
    (factorMass_sum : ∑ y, factorMass y = 1)
    (π : Λ × Y → Γ) (hπ : Function.Surjective π) :
    D.projectedEnergy =
      ((D.independentExtensionData factorMass factorMass_pos factorMass_sum).relabel π hπ).projectedEnergy +
      ∑ p : Ω × Y, D.mass p.1 * factorMass p.2 *
        (D.projection p.1 -
          ((D.independentExtensionData factorMass factorMass_pos factorMass_sum).relabel π hπ).projection p) ^ 2 := by
  let E := D.independentExtensionData factorMass factorMass_pos factorMass_sum
  have h := E.projectedEnergy_eq_relabel_add_defect π hπ
  rw [D.independentExtension_projectedEnergy factorMass factorMass_pos factorMass_sum] at h
  have hsum :
      (∑ p : Ω × Y, D.mass p.1 * factorMass p.2 *
        (D.projection p.1 - (E.relabel π hπ).projection p) ^ 2) =
      ∑ p : Ω × Y, E.mass p *
        (E.projection p - (E.relabel π hπ).projection p) ^ 2 := by
    apply Finset.sum_congr rfl
    intro p _hp
    rw [D.independentExtension_projection factorMass factorMass_pos factorMass_sum]
    rfl
  change D.projectedEnergy = (E.relabel π hπ).projectedEnergy +
    ∑ p : Ω × Y, D.mass p.1 * factorMass p.2 *
      (D.projection p.1 - (E.relabel π hπ).projection p) ^ 2
  rw [hsum]
  exact h

end RouteEPhysicalFibreData

/-! ## Signed convolution as physical coarsening -/

/-- One finite physical convolution step.  `predecessorMean` is the signed conditional field at the
previous replica depth; `combine` appends one factor and records the next product cell. -/
structure RouteEPhysicalConvolutionStep
    (T Y Z : Type*) [Fintype T] [Fintype Y] [Fintype Z] where
  predecessorMass : T → ℝ
  factorMass : Y → ℝ
  predecessorMean : T → ℝ
  combine : T × Y → Z
  predecessorMass_pos : ∀ t, 0 < predecessorMass t
  factorMass_pos : ∀ y, 0 < factorMass y
  predecessorMass_sum : ∑ t, predecessorMass t = 1
  factorMass_sum : ∑ y, factorMass y = 1
  combine_surjective : Function.Surjective combine

namespace RouteEPhysicalConvolutionStep

variable {T Y Z : Type*} [Fintype T] [Fintype Y] [Fintype Z]
  [Nonempty T] [Nonempty Y] [DecidableEq T] [DecidableEq Y] [DecidableEq Z]

/-- Product physical law before forgetting the predecessor/factor decomposition. -/
def fineData (S : RouteEPhysicalConvolutionStep T Y Z) :
    RouteEPhysicalFibreData (T × Y) (T × Y) where
  mass p := S.predecessorMass p.1 * S.factorMass p.2
  observable p := S.predecessorMean p.1
  label := id
  mass_pos p := mul_pos (S.predecessorMass_pos p.1) (S.factorMass_pos p.2)
  mass_sum := by
    rw [Fintype.sum_prod_type]
    simp only [Prod.fst, Prod.snd]
    simp_rw [← Finset.mul_sum, S.factorMass_sum, mul_one]
    exact S.predecessorMass_sum
  label_surjective := Function.surjective_id

/-- Physical product-cell mass after one convolution step. -/
def successorMass (S : RouteEPhysicalConvolutionStep T Y Z) (z : Z) : ℝ :=
  ∑ p with S.combine p = z, S.predecessorMass p.1 * S.factorMass p.2

/-- Signed product-cell moment after one convolution step. -/
def successorMoment (S : RouteEPhysicalConvolutionStep T Y Z) (z : Z) : ℝ :=
  ∑ p with S.combine p = z,
    S.predecessorMass p.1 * S.factorMass p.2 * S.predecessorMean p.1

/-- Next conditional signed field. -/
def successorMean (S : RouteEPhysicalConvolutionStep T Y Z) (z : Z) : ℝ :=
  S.successorMoment z / S.successorMass z

/-- Conditional signed energy before adjoining the next factor. -/
def predecessorEnergy (S : RouteEPhysicalConvolutionStep T Y Z) : ℝ :=
  ∑ t, S.predecessorMass t * S.predecessorMean t ^ 2

/-- Conditional signed energy after regrouping by the next product cell. -/
def successorEnergy (S : RouteEPhysicalConvolutionStep T Y Z) : ℝ :=
  ∑ z, S.successorMoment z ^ 2 / S.successorMass z

/-- Exact one-step reverse-factor variance. -/
def dissipation (S : RouteEPhysicalConvolutionStep T Y Z) : ℝ :=
  ∑ p, S.predecessorMass p.1 * S.factorMass p.2 *
    (S.predecessorMean p.1 - S.successorMean (S.combine p)) ^ 2

theorem fineData_fibreMass (S : RouteEPhysicalConvolutionStep T Y Z) (p : T × Y) :
    S.fineData.fibreMass p = S.predecessorMass p.1 * S.factorMass p.2 := by
  classical
  unfold RouteEPhysicalFibreData.fibreMass fineData
  change (∑ x with x = p, S.predecessorMass x.1 * S.factorMass x.2) =
    S.predecessorMass p.1 * S.factorMass p.2
  have hfilter : (Finset.univ.filter fun x : T × Y => x = p) = {p} := by
    ext x
    simp
  rw [hfilter, Finset.sum_singleton]

theorem fineData_fibreMoment (S : RouteEPhysicalConvolutionStep T Y Z) (p : T × Y) :
    S.fineData.fibreMoment p =
      S.predecessorMass p.1 * S.factorMass p.2 * S.predecessorMean p.1 := by
  classical
  unfold RouteEPhysicalFibreData.fibreMoment fineData
  change (∑ x with x = p,
    S.predecessorMass x.1 * S.factorMass x.2 * S.predecessorMean x.1) =
      S.predecessorMass p.1 * S.factorMass p.2 * S.predecessorMean p.1
  have hfilter : (Finset.univ.filter fun x : T × Y => x = p) = {p} := by
    ext x
    simp
  rw [hfilter, Finset.sum_singleton]

theorem fineData_projection (S : RouteEPhysicalConvolutionStep T Y Z) (p : T × Y) :
    S.fineData.projection p = S.predecessorMean p.1 := by
  unfold RouteEPhysicalFibreData.projection RouteEPhysicalFibreData.conditionalMean
  change S.fineData.fibreMoment p / S.fineData.fibreMass p = S.predecessorMean p.1
  rw [S.fineData_fibreMoment p, S.fineData_fibreMass p]
  exact mul_div_cancel_left₀ (S.predecessorMean p.1)
    (ne_of_gt (mul_pos (S.predecessorMass_pos p.1) (S.factorMass_pos p.2)))

theorem relabel_fibreMass (S : RouteEPhysicalConvolutionStep T Y Z) (z : Z) :
    (S.fineData.relabel S.combine S.combine_surjective).fibreMass z = S.successorMass z :=
  rfl

theorem relabel_fibreMoment (S : RouteEPhysicalConvolutionStep T Y Z) (z : Z) :
    (S.fineData.relabel S.combine S.combine_surjective).fibreMoment z = S.successorMoment z :=
  rfl

theorem relabel_projection (S : RouteEPhysicalConvolutionStep T Y Z) (p : T × Y) :
    (S.fineData.relabel S.combine S.combine_surjective).projection p =
      S.successorMean (S.combine p) :=
  rfl

theorem fine_projectedEnergy_eq_predecessorEnergy
    (S : RouteEPhysicalConvolutionStep T Y Z) :
    S.fineData.projectedEnergy = S.predecessorEnergy := by
  classical
  unfold RouteEPhysicalFibreData.projectedEnergy predecessorEnergy
  simp_rw [S.fineData_projection]
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro t _ht
  change (∑ y, (S.predecessorMass t * S.factorMass y) * S.predecessorMean t ^ 2) =
    S.predecessorMass t * S.predecessorMean t ^ 2
  calc
    (∑ y, (S.predecessorMass t * S.factorMass y) * S.predecessorMean t ^ 2) =
        (S.predecessorMass t * S.predecessorMean t ^ 2) * ∑ y, S.factorMass y := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro y _hy
      ring
    _ = _ := by rw [S.factorMass_sum, mul_one]

theorem coarse_projectedEnergy_eq_successorEnergy
    (S : RouteEPhysicalConvolutionStep T Y Z) :
    (S.fineData.relabel S.combine S.combine_surjective).projectedEnergy =
      S.successorEnergy := by
  rw [(S.fineData.relabel S.combine S.combine_surjective).projectedEnergy_eq_fibreQuotient]
  unfold successorEnergy
  apply Finset.sum_congr rfl
  intro z _hz
  rw [S.relabel_fibreMoment z, S.relabel_fibreMass z]

/-- **Exact signed-convolution dissipation.**  Conditional signed energy is monotone, and its
one-step loss is exactly the reverse-factor conditional variance. -/
theorem predecessorEnergy_eq_successorEnergy_add_dissipation
    (S : RouteEPhysicalConvolutionStep T Y Z) :
    S.predecessorEnergy = S.successorEnergy + S.dissipation := by
  have h := S.fineData.projectedEnergy_eq_relabel_add_defect
    S.combine S.combine_surjective
  rw [S.fine_projectedEnergy_eq_predecessorEnergy,
    S.coarse_projectedEnergy_eq_successorEnergy] at h
  unfold dissipation
  simp only [S.fineData_projection, S.relabel_projection] at h
  change S.predecessorEnergy = S.successorEnergy +
    ∑ p, S.predecessorMass p.1 * S.factorMass p.2 *
      (S.predecessorMean p.1 - S.successorMean (S.combine p)) ^ 2 at h
  exact h

theorem successorEnergy_le_predecessorEnergy
    (S : RouteEPhysicalConvolutionStep T Y Z) :
    S.successorEnergy ≤ S.predecessorEnergy := by
  rw [S.predecessorEnergy_eq_successorEnergy_add_dissipation]
  exact le_add_of_nonneg_right
    (Finset.sum_nonneg fun p _hp =>
      mul_nonneg (mul_pos (S.predecessorMass_pos p.1) (S.factorMass_pos p.2)).le
        (sq_nonneg _))

theorem dissipation_eq_zero_iff_reverseFactor_constant
    (S : RouteEPhysicalConvolutionStep T Y Z) :
    S.dissipation = 0 ↔
      ∀ p, S.predecessorMean p.1 = S.successorMean (S.combine p) := by
  classical
  unfold dissipation
  rw [Finset.sum_eq_zero_iff_of_nonneg]
  · constructor
    · intro h p
      have hp := h p (Finset.mem_univ p)
      have hmass : 0 < S.predecessorMass p.1 * S.factorMass p.2 :=
        mul_pos (S.predecessorMass_pos p.1) (S.factorMass_pos p.2)
      have hsquare :
          (S.predecessorMean p.1 - S.successorMean (S.combine p)) ^ 2 = 0 := by
        nlinarith
      exact sub_eq_zero.mp (sq_eq_zero_iff.mp hsquare)
    · intro h p _hp
      rw [h p, sub_self, zero_pow (by norm_num : (2 : ℕ) ≠ 0), mul_zero]
  · intro p _hp
    exact mul_nonneg
      (mul_pos (S.predecessorMass_pos p.1) (S.factorMass_pos p.2)).le (sq_nonneg _)

end RouteEPhysicalConvolutionStep

end

end RHTower
