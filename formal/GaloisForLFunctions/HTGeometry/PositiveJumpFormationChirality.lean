import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue

/-!
# Positive-jump formation chirality

The directed relative-entropy asymmetry of an exponentially tilted positive-jump formation is
an integral of one universal kernel

`K(a) = a − 2 + (a + 2) e^{−a}`

against the jump measure.  `K` vanishes only at `0` and has the sign of its argument, so the
asymmetry reconstructs the complete order of the formation parameter: this is an information
chronology, not merely a nonzero local tensor at one law.

Everything here is unconditional integral analysis on an arbitrary measure carried by the positive
jumps; no process, no cumulant expansion, and no differentiation under the integral is used.
-/

open MeasureTheory

namespace GaloisForLFunctions.HTGeometry

/-! ## A positive integral criterion -/

theorem integral_pos_of_ae_pos {α : Type*} [MeasurableSpace α] {μ : Measure α} (hμ : μ ≠ 0)
    {f : α → ℝ} (hf : Integrable f μ) (hpos : ∀ᵐ x ∂μ, 0 < f x) : 0 < ∫ x, f x ∂μ := by
  classical
  set g : α → ℝ := fun x => max (f x) 0 with hg
  have hgf : g =ᵐ[μ] f := by
    filter_upwards [hpos] with x hx
    simp [hg, le_of_lt hx]
  have hgnn : 0 ≤ g := fun x => le_max_right _ _
  have hgint : Integrable g μ := hf.congr hgf.symm
  rw [← integral_congr_ae hgf, integral_pos_iff_support_of_nonneg hgnn hgint]
  have hsub : {x | 0 < f x} ⊆ Function.support g := fun x hx => by
    simp only [Function.mem_support, hg]
    exact ne_of_gt (lt_max_of_lt_left hx)
  have h1 : μ Set.univ ≤ μ {x | 0 < f x} :=
    measure_mono_ae (by filter_upwards [hpos] with x hx using fun _ => hx)
  exact lt_of_lt_of_le (Measure.measure_univ_pos.mpr hμ) (h1.trans (measure_mono hsub))

/-! ## The universal formation kernel -/

/-- The universal positive-jump formation kernel `K(a) = a − 2 + (a+2)e^{−a}`. -/
noncomputable def formationKernel (a : ℝ) : ℝ := a - 2 + (a + 2) * Real.exp (-a)

@[simp] theorem formationKernel_zero : formationKernel 0 = 0 := by
  simp [formationKernel]

theorem hasDerivAt_formationKernel (a : ℝ) :
    HasDerivAt formationKernel (1 - (a + 1) * Real.exp (-a)) a := by
  have h1 : HasDerivAt (fun x : ℝ => x - 2) 1 a := (hasDerivAt_id a).sub_const 2
  have h2 : HasDerivAt (fun x : ℝ => x + 2) 1 a := (hasDerivAt_id a).add_const 2
  have h3 : HasDerivAt (fun x : ℝ => Real.exp (-x)) (-Real.exp (-a)) a := by
    simpa using ((hasDerivAt_id a).neg).exp
  have hsum : HasDerivAt formationKernel
      (1 + (1 * Real.exp (-a) + (a + 2) * -Real.exp (-a))) a := h1.add (h2.mul h3)
  convert hsum using 1
  ring

theorem deriv_formationKernel (a : ℝ) :
    deriv formationKernel a = 1 - (a + 1) * Real.exp (-a) :=
  (hasDerivAt_formationKernel a).deriv

/-- The kernel derivative is strictly positive away from the origin, because `e^a > a + 1`. -/
theorem deriv_formationKernel_pos {a : ℝ} (ha : a ≠ 0) : 0 < deriv formationKernel a := by
  rw [deriv_formationKernel]
  have hlt : a + 1 < Real.exp a := Real.add_one_lt_exp ha
  have hexp : 0 < Real.exp (-a) := Real.exp_pos _
  have : (a + 1) * Real.exp (-a) < Real.exp a * Real.exp (-a) :=
    mul_lt_mul_of_pos_right hlt hexp
  rw [← Real.exp_add, add_neg_cancel, Real.exp_zero] at this
  linarith

theorem continuous_formationKernel : Continuous formationKernel := by
  unfold formationKernel
  fun_prop

/-- **The kernel is strictly positive on the positive jumps.** -/
theorem formationKernel_pos {a : ℝ} (ha : 0 < a) : 0 < formationKernel a := by
  have hmono : StrictMonoOn formationKernel (Set.Ici (0 : ℝ)) := by
    refine strictMonoOn_of_deriv_pos (convex_Ici 0) continuous_formationKernel.continuousOn ?_
    intro x hx
    rw [interior_Ici] at hx
    exact deriv_formationKernel_pos (ne_of_gt hx)
  have := hmono (Set.left_mem_Ici) (Set.mem_Ici.mpr ha.le) ha
  simpa using this

theorem formationKernel_neg {a : ℝ} (ha : a < 0) : formationKernel a < 0 := by
  have hmono : StrictMonoOn formationKernel (Set.Iic (0 : ℝ)) := by
    refine strictMonoOn_of_deriv_pos (convex_Iic 0) continuous_formationKernel.continuousOn ?_
    intro x hx
    rw [interior_Iic] at hx
    exact deriv_formationKernel_pos (ne_of_lt hx)
  have := hmono (Set.mem_Iic.mpr ha.le) (Set.right_mem_Iic) ha
  simpa using this

theorem formationKernel_pos_iff {a : ℝ} : 0 < formationKernel a ↔ 0 < a := by
  constructor
  · intro h
    rcases lt_trichotomy a 0 with ha | ha | ha
    · exact absurd h (not_lt.mpr (formationKernel_neg ha).le)
    · subst ha; simp at h
    · exact ha
  · exact formationKernel_pos

/-- **The exact pointwise chirality identity.**  Two tilted exponentials and their two first
moments recombine into a single kernel evaluation. -/
theorem formationKernel_pointwise (s t x : ℝ) :
    2 * (Real.exp (-(t * x)) - Real.exp (-(s * x)))
        + (t - s) * (x * Real.exp (-(s * x)) + x * Real.exp (-(t * x)))
      = Real.exp (-(s * x)) * formationKernel ((t - s) * x) := by
  have hsplit : Real.exp (-(t * x)) = Real.exp (-(s * x)) * Real.exp (-((t - s) * x)) := by
    rw [← Real.exp_add]; congr 1; ring
  rw [formationKernel, hsplit]
  ring

/-! ## Positive-jump formation data -/

/-- A positive-jump formation datum: a nonzero jump measure carried by `(0, ∞)`, together with the
parameter set on which its two directed formation costs are defined. -/
structure PositiveJumpDatum where
  /-- The Lévy jump measure. -/
  ν : Measure ℝ
  /-- The jump measure is nonzero: the formation is nontrivial. -/
  ν_ne_zero : ν ≠ 0
  /-- The jumps are one sided. -/
  carried : ν {x : ℝ | x ≤ 0} = 0
  /-- The admitted Esscher parameters. -/
  I : Set ℝ
  /-- The log-Laplace integrand is integrable at every admitted parameter. -/
  integrable_exp : ∀ t ∈ I, Integrable (fun x => Real.exp (-(t * x)) - 1) ν
  /-- The first moment integrand is integrable at every admitted parameter. -/
  integrable_mul : ∀ t ∈ I, Integrable (fun x => x * Real.exp (-(t * x))) ν

namespace PositiveJumpDatum

variable (D : PositiveJumpDatum)

/-- The log-Laplace transform of the formation. -/
noncomputable def logLaplace (t : ℝ) : ℝ := ∫ x, (Real.exp (-(t * x)) - 1) ∂D.ν

/-- The first response of the formation. -/
noncomputable def firstMoment (t : ℝ) : ℝ := ∫ x, x * Real.exp (-(t * x)) ∂D.ν

/-- The directed information commutator of two admitted formation parameters, in the exact form
supplied by the two Esscher relative entropies. -/
noncomputable def chirality (s t : ℝ) : ℝ :=
  2 * (D.logLaplace t - D.logLaplace s) + (t - s) * (D.firstMoment s + D.firstMoment t)

theorem ae_pos (D : PositiveJumpDatum) : ∀ᵐ x ∂D.ν, 0 < x := by
  have : D.ν {x : ℝ | ¬ (0 < x)} = 0 := by
    convert D.carried using 2
    ext x; simp [not_lt]
  exact this

/-- **The exact chirality kernel formula.** -/
theorem chirality_eq_integral {s t : ℝ} (hs : s ∈ D.I) (ht : t ∈ D.I) :
    D.chirality s t = ∫ x, Real.exp (-(s * x)) * formationKernel ((t - s) * x) ∂D.ν := by
  have hEs := D.integrable_exp s hs
  have hEt := D.integrable_exp t ht
  have hMs := D.integrable_mul s hs
  have hMt := D.integrable_mul t ht
  have h1 : Integrable (fun x => Real.exp (-(t * x)) - Real.exp (-(s * x))) D.ν := by
    refine (hEt.sub hEs).congr (Filter.Eventually.of_forall fun x => ?_)
    simp only [Pi.sub_apply]
    ring
  have h2 : Integrable (fun x => x * Real.exp (-(s * x)) + x * Real.exp (-(t * x))) D.ν := by
    refine (hMs.add hMt).congr (Filter.Eventually.of_forall fun x => ?_)
    simp only [Pi.add_apply]
  have e1 : ∫ x, (Real.exp (-(t * x)) - Real.exp (-(s * x))) ∂D.ν
      = D.logLaplace t - D.logLaplace s := by
    rw [logLaplace, logLaplace, ← integral_sub hEt hEs]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    ring
  have e2 : ∫ x, (x * Real.exp (-(s * x)) + x * Real.exp (-(t * x))) ∂D.ν
      = D.firstMoment s + D.firstMoment t := integral_add hMs hMt
  calc D.chirality s t
      = 2 * (∫ x, (Real.exp (-(t * x)) - Real.exp (-(s * x))) ∂D.ν)
        + (t - s) * (∫ x, (x * Real.exp (-(s * x)) + x * Real.exp (-(t * x))) ∂D.ν) := by
        rw [e1, e2]; rfl
    _ = ∫ x, (2 * (Real.exp (-(t * x)) - Real.exp (-(s * x)))
        + (t - s) * (x * Real.exp (-(s * x)) + x * Real.exp (-(t * x)))) ∂D.ν := by
        rw [integral_add (h1.const_mul 2) (h2.const_mul (t - s)), integral_const_mul,
          integral_const_mul]
    _ = ∫ x, Real.exp (-(s * x)) * formationKernel ((t - s) * x) ∂D.ν :=
        integral_congr_ae (Filter.Eventually.of_forall fun x => formationKernel_pointwise s t x)

theorem integrable_kernel {s t : ℝ} (hs : s ∈ D.I) (ht : t ∈ D.I) :
    Integrable (fun x => Real.exp (-(s * x)) * formationKernel ((t - s) * x)) D.ν := by
  have hEs := D.integrable_exp s hs
  have hEt := D.integrable_exp t ht
  have hMs := D.integrable_mul s hs
  have hMt := D.integrable_mul t ht
  have h1 : Integrable (fun x => Real.exp (-(t * x)) - Real.exp (-(s * x))) D.ν := by
    refine (hEt.sub hEs).congr (Filter.Eventually.of_forall fun x => ?_)
    simp only [Pi.sub_apply]
    ring
  have h2 : Integrable (fun x => x * Real.exp (-(s * x)) + x * Real.exp (-(t * x))) D.ν := by
    refine (hMs.add hMt).congr (Filter.Eventually.of_forall fun x => ?_)
    simp only [Pi.add_apply]
  refine ((h1.const_mul 2).add (h2.const_mul (t - s))).congr
    (Filter.Eventually.of_forall fun x => ?_)
  simpa using formationKernel_pointwise s t x

/-- **Strict chirality.**  A positive-jump formation orients every admitted ordered pair. -/
theorem chirality_pos {s t : ℝ} (hs : s ∈ D.I) (ht : t ∈ D.I) (hst : s < t) :
    0 < D.chirality s t := by
  rw [D.chirality_eq_integral hs ht]
  refine integral_pos_of_ae_pos D.ν_ne_zero (D.integrable_kernel hs ht) ?_
  filter_upwards [D.ae_pos] with x hx
  exact mul_pos (Real.exp_pos _) (formationKernel_pos (mul_pos (sub_pos.mpr hst) hx))

theorem chirality_self (t : ℝ) : D.chirality t t = 0 := by
  simp [chirality]

theorem chirality_antisymm (s t : ℝ) : D.chirality s t = -D.chirality t s := by
  simp only [chirality]
  ring

theorem chirality_neg {s t : ℝ} (hs : s ∈ D.I) (ht : t ∈ D.I) (hst : t < s) :
    D.chirality s t < 0 := by
  rw [D.chirality_antisymm s t]
  simpa using D.chirality_pos ht hs hst

/-- **Information chronology.**  Directed relative entropy reconstructs the complete order of the
formation parameter. -/
theorem lt_iff_chirality_pos {s t : ℝ} (hs : s ∈ D.I) (ht : t ∈ D.I) :
    s < t ↔ 0 < D.chirality s t := by
  constructor
  · exact D.chirality_pos hs ht
  · intro h
    rcases lt_trichotomy s t with hst | hst | hst
    · exact hst
    · subst hst; rw [D.chirality_self] at h; exact absurd h (lt_irrefl 0)
    · exact absurd h (not_lt.mpr (D.chirality_neg hs ht hst).le)

/-- The third response of the formation. -/
noncomputable def thirdCumulant (t : ℝ) : ℝ := ∫ x, x ^ (3 : ℕ) * Real.exp (-(t * x)) ∂D.ν

/-- **The third response of a positive-jump formation is strictly positive.** -/
theorem thirdCumulant_pos {t : ℝ}
    (hint : Integrable (fun x => x ^ (3 : ℕ) * Real.exp (-(t * x))) D.ν) :
    0 < D.thirdCumulant t := by
  refine integral_pos_of_ae_pos D.ν_ne_zero hint ?_
  filter_upwards [D.ae_pos] with x hx
  exact mul_pos (pow_pos hx 3) (Real.exp_pos _)

end PositiveJumpDatum

end GaloisForLFunctions.HTGeometry
