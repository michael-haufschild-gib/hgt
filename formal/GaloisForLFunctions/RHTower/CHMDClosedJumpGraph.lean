import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import Mathlib.Analysis.InnerProductSpace.ProdL2
import Mathlib.MeasureTheory.Measure.QuasiMeasurePreserving

/-!
# Closed difference graphs for the complete CHMD source

Endpoint nonsingularity makes the literal difference operator closed between source and
edge L2 spaces. Its graph is a complete Hilbert space, and the source projection is injective.
The signed energy retains the negative source mass; adding twice that mass gives exactly the
graph norm squared. The next leaf proves endpoint nonsingularity and the full energy identity
for the actual theta, archimedean and prime measures, without a spectral-gap hypothesis.
-/

open MeasureTheory Set Filter Topology
noncomputable section
namespace RHTower.CHMDClosedJump

variable {X E : Type*} [MeasurableSpace X] [MeasurableSpace E]
variable (μ : Measure X) (κ : Measure E) (left right : E → X)
variable (hl : Measure.QuasiMeasurePreserving left κ μ)
variable (hr : Measure.QuasiMeasurePreserving right κ μ)

abbrev Carrier := WithLp 2 (Lp ℝ 2 μ × Lp ℝ 2 κ)

/-- Literal difference graph on equivalence classes, with no auxiliary edge vectors. -/
def graph : Submodule ℝ (Carrier μ κ) where
  carrier := {p | ∀ᵐ e ∂κ, p.snd e = p.fst (left e) - p.fst (right e)}
  zero_mem' := by
    filter_upwards [Lp.coeFn_zero ℝ 2 κ, hl.ae (Lp.coeFn_zero ℝ 2 μ),
      hr.ae (Lp.coeFn_zero ℝ 2 μ)] with e he hl' hr'
    change (0 : Lp ℝ 2 κ) e = (0 : Lp ℝ 2 μ) (left e) - (0 : Lp ℝ 2 μ) (right e)
    simp only [he, hl', hr', Pi.zero_apply, sub_self]
  add_mem' := by
    intro p q hp hq
    filter_upwards [hp, hq, Lp.coeFn_add p.snd q.snd,
      hl.ae (Lp.coeFn_add p.fst q.fst), hr.ae (Lp.coeFn_add p.fst q.fst)]
      with e he hf ha hb hc
    change (p.snd + q.snd) e = (p.fst + q.fst) (left e) - (p.fst + q.fst) (right e)
    simp only [ha, hb, hc, Pi.add_apply, he, hf]
    ring
  smul_mem' := by
    intro c p hp
    filter_upwards [hp, Lp.coeFn_smul c p.snd, hl.ae (Lp.coeFn_smul c p.fst),
      hr.ae (Lp.coeFn_smul c p.fst)] with e he ha hb hc
    change (c • p.snd) e = (c • p.fst) (left e) - (c • p.fst) (right e)
    simp only [ha, hb, hc, Pi.smul_apply, smul_eq_mul, he, mul_sub]

/-- Strong limits of source and edge functions remain literal differences. -/
theorem isClosed_graph : IsClosed (graph μ κ left right hl hr : Set (Carrier μ κ)) := by
  apply isSeqClosed_iff_isClosed.mp
  intro u p hu hp
  have hsource := ((WithLp.continuous_fst 2 _ _).tendsto p).comp hp
  have hedge := ((WithLp.continuous_snd 2 _ _).tendsto p).comp hp
  obtain ⟨ns, hns, hs⟩ := (tendstoInMeasure_of_tendsto_Lp hsource).exists_seq_tendsto_ae
  obtain ⟨ms, hms, he⟩ :=
    (tendstoInMeasure_of_tendsto_Lp (hedge.comp hns.tendsto_atTop)).exists_seq_tendsto_ae
  have hg : ∀ᵐ e ∂κ, ∀ n : ℕ,
      (u (ns (ms n))).snd e =
        (u (ns (ms n))).fst (left e) - (u (ns (ms n))).fst (right e) :=
    ae_all_iff.mpr fun n => hu (ns (ms n))
  filter_upwards [hl.ae hs, hr.ae hs, he, hg] with e hleft hright hedge' hgraph
  apply tendsto_nhds_unique hedge'
  exact ((hleft.comp hms.tendsto_atTop).sub (hright.comp hms.tendsto_atTop)).congr
    fun n => (hgraph n).symm

instance completeSpace_graph : CompleteSpace (graph μ κ left right hl hr) :=
  (isClosed_graph μ κ left right hl hr).isComplete.completeSpace_coe

/-- Completion cannot create an edge vector with zero underlying source. -/
theorem source_injective : Function.Injective
    (fun p : graph μ κ left right hl hr => p.val.fst) := by
  intro p q hpq
  change p.val.fst = q.val.fst at hpq
  have heq : p.val.snd = q.val.snd := by
    apply Lp.ext
    filter_upwards [p.property, q.property] with e hp hq
    rw [hp, hq, hpq]
  apply Subtype.ext
  apply (WithLp.equiv 2 _).injective
  exact Prod.ext hpq heq

/-- The signed source form keeps the original mass subtraction. -/
def energy (p : graph μ κ left right hl hr) : ℝ := ‖p.val.snd‖ ^ 2 - ‖p.val.fst‖ ^ 2

/-- The shifted signed form is exactly the complete Hilbert graph norm. -/
theorem energy_add_two_mass (p : graph μ κ left right hl hr) :
    energy μ κ left right hl hr p + 2 * ‖p.val.fst‖ ^ 2 = ‖p‖ ^ 2 := by
  change _ = ‖p.val‖ ^ 2
  rw [WithLp.prod_norm_sq_eq_of_L2]
  unfold energy
  ring

theorem energy_ge_neg_mass (p : graph μ κ left right hl hr) :
    -‖p.val.fst‖ ^ 2 ≤ energy μ κ left right hl hr p := by
  unfold energy
  linarith [sq_nonneg ‖p.val.snd‖]

/-- Place an actual source function and its complete difference in the closed graph. -/
def ofFunction (v : X → ℝ) (hv : MemLp v 2 μ)
    (hd : MemLp (fun e => v (left e) - v (right e)) 2 κ) :
    graph μ κ left right hl hr := by
  refine ⟨WithLp.toLp 2 (hv.toLp v, hd.toLp (fun e => v (left e) - v (right e))), ?_⟩
  filter_upwards [hd.coeFn_toLp, hl.ae hv.coeFn_toLp, hr.ae hv.coeFn_toLp] with e he hle hre
  change hd.toLp _ e = hv.toLp _ (left e) - hv.toLp _ (right e)
  rw [he, hle, hre]

theorem norm_toLp_sq {f : X → ℝ} (hf : MemLp f 2 μ) :
    ‖hf.toLp f‖ ^ 2 = ∫ x, f x ^ 2 ∂μ := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [hf.coeFn_toLp] with x hx
  simp [hx, pow_two]

/-- Exact integral realization, including the negative mass term. -/
theorem energy_ofFunction (v : X → ℝ) (hv : MemLp v 2 μ)
    (hd : MemLp (fun e => v (left e) - v (right e)) 2 κ) :
    energy μ κ left right hl hr (ofFunction μ κ left right hl hr v hv hd) =
      (∫ e, (v (left e) - v (right e)) ^ 2 ∂κ) - ∫ x, v x ^ 2 ∂μ := by
  change ‖hd.toLp _‖ ^ 2 - ‖hv.toLp _‖ ^ 2 = _
  rw [norm_toLp_sq, norm_toLp_sq]

end RHTower.CHMDClosedJump
