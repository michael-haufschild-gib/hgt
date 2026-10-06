import GaloisForLFunctions.HTGeometry.SmoothBlockWindow
import Mathlib.MeasureTheory.Measure.Real

/-!
# Controlled shrinking cutoffs for the actual physical cubic

The selected relative cutoff is the corpus block window on `[1+δ,2-δ]`,
with transition width `δ`. Positive derivatives vanish throughout its
plateau; integrating their bounds over only the two edges yields
`∫ |cutoff^(k+1)| ≤ C_k / δ^k`. In particular, first variation is uniform
as the edges shrink. Every cutoff retains the exact support and plateau.

The rescaled family gives physical edges of width `H` on `(N,2N)`.
Its sharp/smooth comparison is attached in ChiPrimeGaussianCubicSharpEdges.
Full Gaussian/logarithmic amplitudes and moving-profile transfer remain
separate analytic obligations.
-/

noncomputable section
open MeasureTheory Set Filter
open scoped Topology ContDiff
open GaloisForLFunctions.HTGeometry
namespace RHTower.BAGTrace

private theorem block_derivative_plateau (k : ℕ) {p q δ x : ℝ}
    (hδ : 0<δ) (hx : x∈Ioo p q) :
    iteratedDeriv (k+1) (blockWindowC p q δ) x=0 := by
  have heq : blockWindowC p q δ =ᶠ[𝓝 x] (fun _ => (1 : ℂ)) := by
    filter_upwards [Ioo_mem_nhds hx.1 hx.2] with t ht
    simp only [blockWindowC,blockWindow_eq_one hδ ht.1.le ht.2.le,Complex.ofReal_one]
  rw [heq.iteratedDeriv_eq,iteratedDeriv_const,if_neg (Nat.succ_ne_zero k)]

private theorem block_derivative_off_edges (k : ℕ) {p q δ x : ℝ}
    (hδ : 0<δ) (hx : x∉Icc (p-δ) p ∪ Icc q (q+δ)) :
    iteratedDeriv (k+1) (blockWindowC p q δ) x=0 := by
  by_cases hfull : x∈Icc (p-δ) (q+δ)
  · apply block_derivative_plateau k hδ
    exact ⟨lt_of_not_ge (fun h => hx (Or.inl ⟨hfull.1,h⟩)),
      lt_of_not_ge (fun h => hx (Or.inr ⟨h,hfull.2⟩))⟩
  · exact iteratedDeriv_blockWindowC_eq_zero (k+1) hδ hfull

private theorem block_derivative_edge_integral (k : ℕ) (p q : ℝ)
    {δ : ℝ} (hδ : 0<δ) :
    (∫ x : ℝ, ‖iteratedDeriv (k+1) (blockWindowC p q δ) x‖) ≤
      2*δ*(blockWindowConst (k+1)/δ^(k+1)) := by
  let E := Icc (p-δ) p ∪ Icc q (q+δ)
  have hE : MeasurableSet E := measurableSet_Icc.union measurableSet_Icc
  have hcompact : IsCompact E := isCompact_Icc.union isCompact_Icc
  have hmeasure : volume.real E≤2*δ := by
    calc volume.real E ≤ volume.real (Icc (p-δ) p)+volume.real (Icc q (q+δ)) :=
        measureReal_union_le _ _
      _ = 2*δ := by
        rw [Real.volume_real_Icc_of_le (by linarith),Real.volume_real_Icc_of_le (by linarith)]
        ring
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (s := E)
    (fun x hx => by rw [block_derivative_off_edges k hδ hx,norm_zero])]
  calc (∫ x : ℝ in E, ‖iteratedDeriv (k+1) (blockWindowC p q δ) x‖)
      ≤ ∫ _ : ℝ in E, blockWindowConst (k+1)/δ^(k+1) :=
        setIntegral_mono_on (integrable_iteratedDeriv_blockWindowC (k+1) hδ).norm.integrableOn
          (integrableOn_const hcompact.measure_lt_top.ne) hE
          (fun x _ => norm_iteratedDeriv_blockWindowC_le (k+1) p q hδ x)
    _ = volume.real E*(blockWindowConst (k+1)/δ^(k+1)) := by
      rw [setIntegral_const,smul_eq_mul]
    _ ≤ _ := mul_le_mul_of_nonneg_right hmeasure
      (div_nonneg (blockWindowConst_nonneg _) (pow_nonneg hδ.le _))

/-- Explicit relative cutoff with two shrinking transition zones. -/
def bagCubicControlledCutoff (δ : ℝ) : ℝ→ℝ := blockWindow (1+δ) (2-δ) δ

/-- Exact support, plateau and range of the selected relative family. -/
theorem bagCubicControlledCutoff_properties (δ : {r : ℝ // r∈Ioo (0 : ℝ) (1/2)}) :
    ContDiff ℝ ∞ (bagCubicControlledCutoff δ.1) ∧
    HasCompactSupport (bagCubicControlledCutoff δ.1) ∧
    (∀x : ℝ, bagCubicControlledCutoff δ.1 x∈Icc (0 : ℝ) 1) ∧
    (∀x : ℝ, x∉Ioo (1 : ℝ) 2 → bagCubicControlledCutoff δ.1 x=0) ∧
    (∀x∈Icc (1+δ.1) (2-δ.1),bagCubicControlledCutoff δ.1 x=1) := by
  refine ⟨contDiff_blockWindow _ _ _,hasCompactSupport_blockWindow δ.2.1,
    fun x => ⟨blockWindow_nonneg _ _ _ _,blockWindow_le_one _ _ _ _⟩,?_,?_⟩
  · intro x hx
    rcases le_or_gt x 1 with h | h
    · apply blockWindow_eq_zero_of_le δ.2.1
      linarith only [h]
    · apply blockWindow_eq_zero_of_ge δ.2.1
      have hh : 2≤x := le_of_not_gt (fun hx2 => hx ⟨h,hx2⟩)
      linarith only [hh]
  · intro x hx
    exact blockWindow_eq_one δ.2.1 hx.1 hx.2

/-- Positive-order derivative mass is supported only on the two edges.
The order-one budget is uniform in their width. -/
theorem bagCubicControlledCutoff_derivative_budgets (k : ℕ) :
    ∃ C : ℝ, 0<C ∧ ∀ δ : {r : ℝ // r∈Ioo (0 : ℝ) (1/2)},
      Integrable (fun x : ℝ => ‖iteratedDeriv (k+1) (bagCubicControlledCutoff δ.1) x‖) ∧
      (∫ x : ℝ, ‖iteratedDeriv (k+1) (bagCubicControlledCutoff δ.1) x‖) ≤ C/δ.1^k := by
  refine ⟨1+2*blockWindowConst (k+1),by nlinarith [blockWindowConst_nonneg (k+1)],?_⟩
  intro δ
  have heq (x : ℝ) : ‖iteratedDeriv (k+1) (bagCubicControlledCutoff δ.1) x‖ =
      ‖iteratedDeriv (k+1) (blockWindowC (1+δ.1) (2-δ.1) δ.1) x‖ := by
    rw [iteratedDeriv_blockWindowC,Complex.norm_real]
    rfl
  have hf := (integrable_iteratedDeriv_blockWindowC (k+1)
    (p := 1+δ.1) (q := 2-δ.1) δ.2.1).norm
  refine ⟨hf.congr (Filter.Eventually.of_forall (fun x => (heq x).symm)),?_⟩
  simp_rw [heq]
  calc (∫ x : ℝ, ‖iteratedDeriv (k+1) (blockWindowC (1+δ.1) (2-δ.1) δ.1) x‖)
      ≤ 2*δ.1*(blockWindowConst (k+1)/δ.1^(k+1)) :=
        block_derivative_edge_integral k _ _ δ.2.1
    _ = (2*blockWindowConst (k+1))/δ.1^k := by
      rw [pow_succ]
      field_simp [δ.2.1.ne']
    _ ≤ _ := div_le_div_of_nonneg_right (by linarith) (pow_nonneg δ.2.1.le _)

/-- Physical cutoff with band scale N and absolute edge width H. -/
def bagCubicControlledBandCutoff (N H : ℝ) (x : ℝ) : ℝ :=
  bagCubicControlledCutoff (H/N) (x/N)

/-- Every admissible physical band has the exact selected smooth cutoff. -/
theorem bagCubicControlledBandCutoff_properties
    (N : {r : ℝ // 0<r}) (H : {r : ℝ // r∈Ioo (0 : ℝ) (N.1/2)}) :
    ContDiff ℝ ∞ (bagCubicControlledBandCutoff N.1 H.1) ∧
    HasCompactSupport (bagCubicControlledBandCutoff N.1 H.1) ∧
    (∀x : ℝ, bagCubicControlledBandCutoff N.1 H.1 x∈Icc (0 : ℝ) 1) ∧
    (∀x : ℝ, x∉Ioo N.1 (2*N.1) → bagCubicControlledBandCutoff N.1 H.1 x=0) ∧
    (∀x∈Icc (N.1+H.1) (2*N.1-H.1),bagCubicControlledBandCutoff N.1 H.1 x=1) := by
  let δ : {r : ℝ // r∈Ioo (0 : ℝ) (1/2)} :=
    ⟨H.1/N.1,div_pos H.2.1 N.2,(div_lt_iff₀ N.2).mpr (by linarith only [H.2.2])⟩
  obtain ⟨hc,_,hr,hz,ho⟩ := bagCubicControlledCutoff_properties δ
  have hzero (x : ℝ) (hx : x∉Ioo N.1 (2*N.1)) :
      bagCubicControlledBandCutoff N.1 H.1 x=0 := by
    apply hz
    intro hh
    apply hx
    exact ⟨by simpa using (lt_div_iff₀ N.2).mp hh.1,
      (div_lt_iff₀ N.2).mp hh.2⟩
  refine ⟨hc.comp (contDiff_id.div_const _),?_,fun x => hr (x/N.1),hzero,?_⟩
  · apply HasCompactSupport.of_support_subset_isCompact isCompact_Icc
    intro x hx
    by_contra hh
    apply hx
    exact hzero x (fun h => hh ⟨h.1.le,h.2.le⟩)
  · intro x hx
    apply ho
    constructor
    · change 1+H.1/N.1≤x/N.1
      calc 1+H.1/N.1=(N.1+H.1)/N.1 := by field_simp [N.2.ne']
           _≤x/N.1 := div_le_div_of_nonneg_right hx.1 N.2.le
    · change x/N.1≤2-H.1/N.1
      calc x/N.1≤(2*N.1-H.1)/N.1 := div_le_div_of_nonneg_right hx.2 N.2.le
           _=2-H.1/N.1 := by field_simp [N.2.ne']

end RHTower.BAGTrace
