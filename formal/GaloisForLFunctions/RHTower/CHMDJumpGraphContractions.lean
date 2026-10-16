import GaloisForLFunctions.RHTower.CHMDClosedJumpGraph
import Mathlib.Topology.MetricSpace.Lipschitz
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Normal contractions and bounded truncation in literal jump graphs

Contractions act on the underlying source function and retain its actual edge
differences. Bounded scalar truncations converge in the full graph norm.
-/

open MeasureTheory Set Filter Topology
noncomputable section
namespace RHTower.CHMDClosedJump

variable {X E : Type*} [MeasurableSpace X] [MeasurableSpace E]

/-- Dominated convergence in real L2, with the domination stated for squared error. -/
theorem toLp_tendsto_of_sq_dom {μ : Measure X} {f : ℕ → X → ℝ} {g b : X → ℝ}
    (hf : ∀ n, MemLp (f n) 2 μ) (hg : MemLp g 2 μ) (hb : Integrable b μ)
    (hbound : ∀ n, ∀ᵐ x ∂μ, (f n x - g x) ^ 2 ≤ b x)
    (hlim : ∀ᵐ x ∂μ, Tendsto (fun n => f n x) atTop (𝓝 (g x))) :
    Tendsto (fun n => (hf n).toLp (f n)) atTop (𝓝 (hg.toLp g)) := by
  have hi := tendsto_integral_of_dominated_convergence
    (F := fun n x => (f n x - g x) ^ 2) (f := fun _ => (0 : ℝ)) b
    (fun n => (((hf n).aestronglyMeasurable.sub hg.aestronglyMeasurable).pow 2)) hb
    (fun n => (hbound n).mono fun x hx => by
      simpa only [Real.norm_of_nonneg (sq_nonneg _)] using hx)
    (hlim.mono fun x hx => by
      simpa using (hx.sub (tendsto_const_nhds (x := g x))).pow 2)
  have hs : Tendsto (fun n => ‖(hf n).toLp (f n) - hg.toLp g‖ ^ 2) atTop (𝓝 0) := by
    simpa only [integral_zero, ← MemLp.toLp_sub, norm_toLp_sq, Pi.sub_apply] using hi
  rw [tendsto_iff_norm_sub_tendsto_zero]
  simpa only [Function.comp_def, Real.sqrt_sq (norm_nonneg _), Real.sqrt_zero] using
    (Real.continuous_sqrt.tendsto 0).comp hs

variable (μ : Measure X) (κ : Measure E) (left right : E → X)
variable (hl : Measure.QuasiMeasurePreserving left κ μ)
variable (hr : Measure.QuasiMeasurePreserving right κ μ)

theorem ofFunction_tendsto {v : ℕ → X → ℝ} {w : X → ℝ}
    (hv : ∀ n, MemLp (v n) 2 μ)
    (hd : ∀ n, MemLp (fun e => v n (left e) - v n (right e)) 2 κ)
    (hw : MemLp w 2 μ) (hwd : MemLp (fun e => w (left e) - w (right e)) 2 κ)
    (hs : Tendsto (fun n => (hv n).toLp (v n)) atTop (𝓝 (hw.toLp w)))
    (he : Tendsto (fun n => (hd n).toLp _) atTop (𝓝 (hwd.toLp _))) :
    Tendsto (fun n => ofFunction μ κ left right hl hr (v n) (hv n) (hd n)) atTop
      (𝓝 (ofFunction μ κ left right hl hr w hw hwd)) := by
  rw [tendsto_subtype_rng]
  exact (WithLp.prod_continuous_toLp 2 _ _).continuousAt.tendsto.comp (hs.prodMk_nhds he)

theorem memLp_contracted_difference (p : graph μ κ left right hl hr)
    {F : ℝ → ℝ} (hF : LipschitzWith 1 F) :
    MemLp (fun e => F (p.val.fst (left e)) - F (p.val.fst (right e))) 2 κ := by
  have hm := hF.continuous.measurable.comp (Lp.stronglyMeasurable p.val.fst).measurable
  apply (Lp.memLp p.val.snd).mono
    ((hm.comp hl.measurable).sub (hm.comp hr.measurable)).aestronglyMeasurable
  filter_upwards [p.property] with e he
  rw [he]
  simpa only [Function.comp_apply, Pi.sub_apply, NNReal.coe_one, one_mul] using
    hF.norm_sub_le (p.val.fst (left e)) (p.val.fst (right e))

/-- A scalar normal contraction on the literal graph, including all edges. -/
def contract (p : graph μ κ left right hl hr) {F : ℝ → ℝ}
    (hF : LipschitzWith 1 F) (h0 : F 0 = 0) : graph μ κ left right hl hr :=
  ofFunction μ κ left right hl hr (F ∘ p.val.fst)
    (hF.comp_memLp h0 (Lp.memLp p.val.fst))
    (memLp_contracted_difference μ κ left right hl hr p hF)

theorem contract_source_ae (p : graph μ κ left right hl hr) {F : ℝ → ℝ}
    (hF : LipschitzWith 1 F) (h0 : F 0 = 0) :
    (contract μ κ left right hl hr p hF h0).val.fst =ᵐ[μ] F ∘ p.val.fst :=
  (hF.comp_memLp h0 (Lp.memLp p.val.fst)).coeFn_toLp

theorem contract_edge_ae (p : graph μ κ left right hl hr) {F : ℝ → ℝ}
    (hF : LipschitzWith 1 F) (h0 : F 0 = 0) :
    (contract μ κ left right hl hr p hF h0).val.snd =ᵐ[κ]
      fun e => F (p.val.fst (left e)) - F (p.val.fst (right e)) :=
  (memLp_contracted_difference μ κ left right hl hr p hF).coeFn_toLp

theorem contract_source_norm_le (p : graph μ κ left right hl hr) {F : ℝ → ℝ}
    (hF : LipschitzWith 1 F) (h0 : F 0 = 0) :
    ‖(contract μ κ left right hl hr p hF h0).val.fst‖ ≤ ‖p.val.fst‖ := by
  apply Lp.norm_le_norm_of_ae_le
  filter_upwards [contract_source_ae μ κ left right hl hr p hF h0] with x hx
  rw [hx]
  simpa only [Function.comp_apply, h0, sub_zero, NNReal.coe_one, one_mul] using
    hF.norm_sub_le (p.val.fst x) 0

theorem contract_edge_norm_le (p : graph μ κ left right hl hr) {F : ℝ → ℝ}
    (hF : LipschitzWith 1 F) (h0 : F 0 = 0) :
    ‖(contract μ κ left right hl hr p hF h0).val.snd‖ ≤ ‖p.val.snd‖ := by
  apply Lp.norm_le_norm_of_ae_le
  filter_upwards [contract_edge_ae μ κ left right hl hr p hF h0, p.property] with e he hp
  rw [he, hp]
  simpa only [NNReal.coe_one, one_mul] using hF.norm_sub_le (p.val.fst (left e)) (p.val.fst (right e))

def clip (n : ℕ) (x : ℝ) : ℝ := max (-(n : ℝ)) (min x n)

theorem lipschitz_clip (n : ℕ) : LipschitzWith 1 (clip n) :=
  (LipschitzWith.id.min_const (n : ℝ)).const_max (-(n : ℝ))

theorem clip_zero (n : ℕ) : clip n 0 = 0 := by
  simp only [clip, min_eq_left (Nat.cast_nonneg (α := ℝ) n),
    max_eq_right (neg_nonpos.mpr (Nat.cast_nonneg (α := ℝ) n))]

theorem abs_clip_le (n : ℕ) (x : ℝ) : |clip n x| ≤ n := by
  rw [abs_le]
  exact ⟨le_max_left _ _, max_le (by linarith [Nat.cast_nonneg (α := ℝ) n]) (min_le_right _ _)⟩

theorem clip_tendsto (x : ℝ) : Tendsto (fun n => clip n x) atTop (𝓝 x) := by
  apply tendsto_const_nhds.congr'
  have hlarge : ∀ᶠ n : ℕ in atTop, |x| ≤ (n : ℝ) :=
    tendsto_natCast_atTop_atTop.eventually (eventually_ge_atTop |x|)
  filter_upwards [hlarge] with n hn
  obtain ⟨hlx, hux⟩ := abs_le.mp hn
  simp only [clip, min_eq_left hux, max_eq_right hlx]

def truncate (p : graph μ κ left right hl hr) (n : ℕ) : graph μ κ left right hl hr :=
  contract μ κ left right hl hr p (lipschitz_clip n) (clip_zero n)

theorem truncate_source_bounded (p : graph μ κ left right hl hr) (n : ℕ) :
    ∀ᵐ x ∂μ, |(truncate μ κ left right hl hr p n).val.fst x| ≤ n := by
  filter_upwards [contract_source_ae μ κ left right hl hr p (lipschitz_clip n) (clip_zero n)] with x hx
  unfold truncate
  rw [hx]
  exact abs_clip_le n _

theorem truncate_tendsto (p : graph μ κ left right hl hr) :
    Tendsto (truncate μ κ left right hl hr p) atTop (𝓝 p) := by
  let s := fun n => clip n ∘ p.val.fst
  have hs (n : ℕ) : MemLp (s n) 2 μ := (lipschitz_clip n).comp_memLp (clip_zero n) (Lp.memLp p.val.fst)
  let d := fun n e => clip n (p.val.fst (left e)) - clip n (p.val.fst (right e))
  have hd (n : ℕ) : MemLp (d n) 2 κ := memLp_contracted_difference μ κ left right hl hr p (lipschitz_clip n)
  have hsource : Tendsto (fun n => (hs n).toLp (s n)) atTop (𝓝 p.val.fst) := by
    have h := toLp_tendsto_of_sq_dom hs (Lp.memLp p.val.fst)
      ((Lp.memLp p.val.fst).integrable_sq.const_mul 4) (fun n => ?_)
      (Eventually.of_forall fun x => clip_tendsto (p.val.fst x))
    · simpa only [Lp.toLp_coeFn] using h
    filter_upwards with x
    have hb := (lipschitz_clip n).norm_sub_le (p.val.fst x) 0
    simp only [clip_zero, sub_zero, NNReal.coe_one, one_mul, Real.norm_eq_abs] at hb
    have ha := abs_le.mp hb
    change (clip n (p.val.fst x) - p.val.fst x) ^ 2 ≤ 4 * p.val.fst x ^ 2
    nlinarith [sq_abs (p.val.fst x), le_abs_self (p.val.fst x), neg_abs_le (p.val.fst x)]
  have hedge : Tendsto (fun n => (hd n).toLp (d n)) atTop (𝓝 p.val.snd) := by
    have h := toLp_tendsto_of_sq_dom hd (Lp.memLp p.val.snd)
      ((Lp.memLp p.val.snd).integrable_sq.const_mul 4) (fun n => ?_) ?_
    · simpa only [Lp.toLp_coeFn] using h
    · filter_upwards [p.property] with e he
      have hb := (lipschitz_clip n).norm_sub_le (p.val.fst (left e)) (p.val.fst (right e))
      rw [← he] at hb
      simp only [NNReal.coe_one, one_mul, Real.norm_eq_abs] at hb
      have ha := abs_le.mp hb
      change (d n e - p.val.snd e) ^ 2 ≤ 4 * p.val.snd e ^ 2
      dsimp only [d] at *
      nlinarith [sq_abs (p.val.snd e), le_abs_self (p.val.snd e), neg_abs_le (p.val.snd e)]
    · filter_upwards [p.property] with e he
      rw [he]
      exact (clip_tendsto _).sub (clip_tendsto _)
  rw [tendsto_subtype_rng]
  exact (WithLp.prod_continuous_toLp 2 _ _).continuousAt.tendsto.comp (hsource.prodMk_nhds hedge)

end RHTower.CHMDClosedJump
