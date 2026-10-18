import GaloisForLFunctions.HTGeometry.WeakSequentialCompactness
import Mathlib.Analysis.InnerProductSpace.Projection.Minimal
import Mathlib.Topology.Order.IsLUB
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure

/-!
# Attainment on bounded closed convex Hilbert allocations

The real weak subsequence argument and closed convex separation prove the direct method from closed convex sublevels. Closed measurable fibre constraints in L2 are included for literal allocation carriers.
-/

set_option autoImplicit false
open MeasureTheory Set Filter Topology
open scoped InnerProductSpace
noncomputable section


namespace GaloisForLFunctions.HTGeometry

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  [CompleteSpace H] [TopologicalSpace.SeparableSpace H]

theorem exists_realWeaklyConvergent_subseq_of_bounded
    (u : ℕ → H) (M : ℝ) (hM : ∀ n, ‖u n‖ ≤ M) :
    ∃ w : H, ∃ φ : ℕ → ℕ, StrictMono φ ∧ ‖w‖ ≤ M ∧
      ∀ y : H, Tendsto (fun n => inner ℝ (u (φ n)) y) atTop
        (nhds (inner ℝ w y)) := by
  let d : ℕ → WeakDual ℝ H := fun n =>
    StrongDual.toWeakDual (InnerProductSpace.toDual ℝ H (u n))
  let S : Set (WeakDual ℝ H) :=
    WeakDual.toStrongDual ⁻¹' Metric.closedBall 0 M
  have hd : ∀ n, d n ∈ S := by
    intro n
    change dist (WeakDual.toStrongDual (d n)) 0 ≤ M
    rw [dist_zero_right]
    change ‖InnerProductSpace.toDual ℝ H (u n)‖ ≤ M
    rw [(InnerProductSpace.toDual ℝ H).norm_map]
    exact hM n
  have hfreq : ∃ᶠ n in atTop, d n ∈ S :=
    (Filter.Eventually.of_forall hd).frequently
  obtain ⟨a, ha, φ, hφ, hlim⟩ :=
    (WeakDual.isSeqCompact_closedBall ℝ H 0 M).subseq_of_frequently_in hfreq
  let w : H := (InnerProductSpace.toDual ℝ H).symm
    (WeakDual.toStrongDual a)
  have hw : ‖w‖ ≤ M := by
    have ha' : dist (WeakDual.toStrongDual a) 0 ≤ M := ha
    rw [dist_zero_right] at ha'
    change ‖(InnerProductSpace.toDual ℝ H).symm
      (WeakDual.toStrongDual a)‖ ≤ M
    rwa [(InnerProductSpace.toDual ℝ H).symm.norm_map]
  refine ⟨w, φ, hφ, hw, ?_⟩
  intro y
  have heval := (WeakDual.eval_continuous y).tendsto a |>.comp hlim
  have hwval : inner ℝ w y = a y := by
    change inner ℝ ((InnerProductSpace.toDual ℝ H).symm
      (WeakDual.toStrongDual a)) y = _
    rw [InnerProductSpace.toDual_symm_apply]
    rfl
  rw [hwval]
  convert heval using 1; rfl

omit [TopologicalSpace.SeparableSpace H] in
/-- Closed convex constraints survive weak limits, including eventual membership. -/
theorem mem_closedConvex_of_realWeakTendsto {C : Set H}
    (hne : C.Nonempty) (hc : IsClosed C) (hv : Convex ℝ C)
    {u : ℕ → H} {w : H} (hu : ∀ᶠ n in atTop, u n ∈ C)
    (hw : ∀ y : H, Tendsto (fun n => inner ℝ (u n) y) atTop (𝓝 (inner ℝ w y))) :
    w ∈ C := by
  obtain ⟨p, hp, hmin⟩ := exists_norm_eq_iInf_of_complete_convex hne hc.isComplete hv w
  have hsep := (norm_eq_iInf_iff_real_inner_le_zero hv hp).mp hmin
  have hi : inner ℝ w (w - p) ≤ inner ℝ p (w - p) := by
    apply le_of_tendsto (hw (w - p))
    filter_upwards [hu] with n hn
    have h := hsep (u n) hn
    rw [inner_sub_right, real_inner_comm (u n) (w - p),
      real_inner_comm p (w - p)] at h
    linarith
  have hn : ‖w - p‖ ^ 2 ≤ 0 := by
    rw [← real_inner_self_eq_norm_sq, inner_sub_left]
    linarith
  have hwp : w = p := sub_eq_zero.mp (norm_eq_zero.mp (by nlinarith [norm_nonneg (w - p)]))
  exact hwp.symm ▸ hp

/-- Direct method for bounded Hilbert allocations. Only closed convex sublevels are needed. -/
theorem exists_isMinOn_closedConvex_sublevels
    (C : Set H) (hne : C.Nonempty) (hc : IsClosed C) (hv : Convex ℝ C)
    (M : ℝ) (hM : ∀ x ∈ C, ‖x‖ ≤ M) (F : H → ℝ)
    (hbelow : BddBelow (F '' C))
    (hclosed : ∀ t : ℝ, IsClosed {x | x ∈ C ∧ F x ≤ t})
    (hconvex : ∀ t : ℝ, Convex ℝ {x | x ∈ C ∧ F x ≤ t}) :
    ∃ w ∈ C, IsMinOn F C w := by
  obtain ⟨v, _, hvlim, hvimage⟩ := exists_seq_tendsto_sInf (hne.image F) hbelow
  choose u hu hFu using hvimage
  obtain ⟨w, φ, hφ, _, hw⟩ := exists_realWeaklyConvergent_subseq_of_bounded u M
    (fun n => hM (u n) (hu n))
  have hwC : w ∈ C := mem_closedConvex_of_realWeakTendsto hne hc hv
    (Eventually.of_forall (fun n => hu (φ n))) hw
  have hlim : Tendsto (fun n => F (u (φ n))) atTop (𝓝 (sInf (F '' C))) := by
    simpa only [hFu, Function.comp_def] using hvlim.comp hφ.tendsto_atTop
  have hwF : F w ≤ sInf (F '' C) := by
    apply le_of_forall_gt_imp_ge_of_dense
    intro t ht
    have het : ∀ᶠ n in atTop, F (u (φ n)) ≤ t :=
      (hlim.eventually (eventually_lt_nhds ht)).mono fun _ h => h.le
    have heC : ∀ᶠ n in atTop, u (φ n) ∈ {x | x ∈ C ∧ F x ≤ t} :=
      het.mono fun n hn => ⟨hu (φ n), hn⟩
    have heN : ({x | x ∈ C ∧ F x ≤ t} : Set H).Nonempty := by
      obtain ⟨n, hn⟩ := heC.exists
      exact ⟨u (φ n), hn⟩
    exact (mem_closedConvex_of_realWeakTendsto heN (hclosed t) (hconvex t) heC hw).2
  refine ⟨w, hwC, ?_⟩
  intro x hx
  exact hwF.trans (csInf_le hbelow ⟨x, hx, rfl⟩)

end GaloisForLFunctions.HTGeometry

namespace GaloisForLFunctions.HTGeometry

variable {α E : Type*} [MeasurableSpace α] [NormedAddCommGroup E]

/-- Fibrewise closed constraints form a closed subset of the actual L² space. -/
theorem isClosed_L2_fibreConstraints (μ : Measure α) (K : α → Set E)
    (hK : ∀ x, IsClosed (K x)) :
    IsClosed {u : Lp E 2 μ | ∀ᵐ x ∂μ, u x ∈ K x} := by
  apply IsSeqClosed.isClosed
  intro u v hu huv
  obtain ⟨ns, _, hns⟩ := (tendstoInMeasure_of_tendsto_Lp huv).exists_seq_tendsto_ae
  have hall : ∀ᵐ x ∂μ, ∀ n, u (ns n) x ∈ K x :=
    ae_all_iff.mpr (fun n => hu (ns n))
  filter_upwards [hns, hall] with x hx hux
  exact (hK x).mem_of_tendsto hx (Eventually.of_forall hux)

/-- Nonnegative shares, support and partition equalities may all be imposed fibrewise. -/
theorem convex_L2_fibreConstraints [NormedSpace ℝ E] (μ : Measure α) (K : α → Set E)
    (hK : ∀ x, Convex ℝ (K x)) :
    Convex ℝ {u : Lp E 2 μ | ∀ᵐ x ∂μ, u x ∈ K x} := by
  intro u hu v hv a b ha hb hab
  filter_upwards [hu, hv, Lp.coeFn_add (a • u) (b • v),
    Lp.coeFn_smul a u, Lp.coeFn_smul b v] with x hux hvx hsum hau hbv
  rw [hsum, Pi.add_apply, hau, hbv]
  exact hK x hux hvx ha hb hab

end GaloisForLFunctions.HTGeometry

end
