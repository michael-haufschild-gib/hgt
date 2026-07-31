import GaloisForLFunctions.HTGeometry.CompactAbelianHaar

/-!
# Convolution with a continuous kernel on a compact abelian group

Convolution against a continuous kernel smooths an integrable function into a continuous one, with
a modulus of continuity that depends only on the kernel and on the `L¹` size of the function.  That
uniform modulus is what later makes the convolution operator compact.

The elementary input is a tube-lemma form of uniform continuity: on a compact group, a continuous
function has, for each `ε`, a single neighbourhood `V` of `0` with `‖k (x + v) - k x‖ < ε` for every
`x` and every `v ∈ V`.
-/

open MeasureTheory TopologicalSpace

namespace GaloisForLFunctions

namespace CompactAbelian

noncomputable section

variable {G : Type*} [TopologicalSpace G] [AddCommGroup G] [IsTopologicalAddGroup G]
  [CompactSpace G] [T2Space G] [MeasurableSpace G] [BorelSpace G]

omit [T2Space G] [MeasurableSpace G] [BorelSpace G] in
/-- **Uniform continuity on a compact group.**  One neighbourhood of the origin works at every
point. -/
theorem exists_nhds_zero_norm_sub_lt (k : G → ℂ) (hk : Continuous k) {ε : ℝ} (hε : 0 < ε) :
    ∃ V ∈ nhds (0 : G), ∀ x : G, ∀ v ∈ V, ‖k (x + v) - k x‖ < ε := by
  set W : Set (G × G) := {p : G × G | ‖k (p.1 + p.2) - k p.1‖ < ε} with hW
  have hWopen : IsOpen W := by
    have hcont : Continuous fun p : G × G => ‖k (p.1 + p.2) - k p.1‖ :=
      ((hk.comp (continuous_fst.add continuous_snd)).sub (hk.comp continuous_fst)).norm
    exact isOpen_lt hcont continuous_const
  have hsub : (Set.univ : Set G) ×ˢ ({0} : Set G) ⊆ W := by
    rintro ⟨x, v⟩ ⟨-, hv⟩
    have hv0 : v = 0 := hv
    simp [hW, hv0, hε]
  obtain ⟨U, V, -, hVopen, hUuniv, hVzero, hUV⟩ :=
    generalized_tube_lemma isCompact_univ isCompact_singleton hWopen hsub
  refine ⟨V, hVopen.mem_nhds (hVzero rfl), fun x v hv => ?_⟩
  have hmem : (x, v) ∈ U ×ˢ V := Set.mk_mem_prod (hUuniv (Set.mem_univ x)) hv
  exact hUV hmem

/-- Convolution of a function with a kernel on a compact abelian group. -/
def convFun (k u : G → ℂ) (x : G) : ℂ := ∫ y, u y * k (x - y) ∂(haarProb G)

omit [T2Space G] in
theorem integrable_mul_kernel {k u : G → ℂ} (hk : Continuous k) {C : ℝ} (hC : ∀ z, ‖k z‖ ≤ C)
    (hu : Integrable u (haarProb G)) (x : G) :
    Integrable (fun y => u y * k (x - y)) (haarProb G) := by
  have h : Integrable (fun y => k (x - y) * u y) (haarProb G) :=
    hu.bdd_mul (c := C) (hk.comp (continuous_const.sub continuous_id)).aestronglyMeasurable
      (Filter.Eventually.of_forall fun y => hC _)
  refine h.congr (Filter.Eventually.of_forall fun y => ?_)
  ring

omit [T2Space G] in
/-- The convolution is bounded by the sup norm of the kernel times the `L¹` size of the function. -/
theorem norm_convFun_le {k u : G → ℂ} (hk : Continuous k) {C : ℝ} (hC : ∀ z, ‖k z‖ ≤ C)
    (hu : Integrable u (haarProb G)) (x : G) :
    ‖convFun k u x‖ ≤ C * ∫ y, ‖u y‖ ∂(haarProb G) := by
  have hCnonneg : 0 ≤ C := le_trans (norm_nonneg _) (hC 0)
  calc ‖convFun k u x‖ ≤ ∫ y, ‖u y * k (x - y)‖ ∂(haarProb G) :=
        norm_integral_le_integral_norm _
    _ ≤ ∫ y, C * ‖u y‖ ∂(haarProb G) := by
        refine integral_mono (integrable_mul_kernel hk hC hu x).norm (hu.norm.const_mul C) ?_
        intro y
        simp only [norm_mul]
        exact (mul_le_mul_of_nonneg_left (hC _) (norm_nonneg (u y))).trans_eq (mul_comm _ _)
    _ = C * ∫ y, ‖u y‖ ∂(haarProb G) := integral_const_mul _ _

omit [T2Space G] in
/-- **The uniform modulus of continuity of a convolution.** -/
theorem norm_convFun_sub_le {k u : G → ℂ} (hk : Continuous k) {C : ℝ} (hC : ∀ z, ‖k z‖ ≤ C)
    (hu : Integrable u (haarProb G)) {ε : ℝ} {V : Set G}
    (hV : ∀ x : G, ∀ v ∈ V, ‖k (x + v) - k x‖ < ε) {x x' : G} (hxx' : x - x' ∈ V) :
    ‖convFun k u x - convFun k u x'‖ ≤ ε * ∫ y, ‖u y‖ ∂(haarProb G) := by
  have hi1 := integrable_mul_kernel hk hC hu x
  have hi2 := integrable_mul_kernel hk hC hu x'
  have hsub : convFun k u x - convFun k u x'
      = ∫ y, (u y * k (x - y) - u y * k (x' - y)) ∂(haarProb G) := by
    rw [convFun, convFun, ← integral_sub hi1 hi2]
  rw [hsub]
  calc ‖∫ y, (u y * k (x - y) - u y * k (x' - y)) ∂(haarProb G)‖
      ≤ ∫ y, ‖u y * k (x - y) - u y * k (x' - y)‖ ∂(haarProb G) :=
        norm_integral_le_integral_norm _
    _ ≤ ∫ y, ε * ‖u y‖ ∂(haarProb G) := by
        refine integral_mono (hi1.sub hi2).norm (hu.norm.const_mul ε) ?_
        intro y
        have hk' : ‖k (x - y) - k (x' - y)‖ ≤ ε := by
          have hx : x - y = (x' - y) + (x - x') := by abel
          rw [hx]
          exact le_of_lt (hV (x' - y) (x - x') hxx')
        calc ‖u y * k (x - y) - u y * k (x' - y)‖
            = ‖u y‖ * ‖k (x - y) - k (x' - y)‖ := by rw [← mul_sub, norm_mul]
          _ ≤ ‖u y‖ * ε := mul_le_mul_of_nonneg_left hk' (norm_nonneg _)
          _ = ε * ‖u y‖ := mul_comm _ _
    _ = ε * ∫ y, ‖u y‖ ∂(haarProb G) := integral_const_mul _ _

omit [T2Space G] in
/-- The convolution of an integrable function with a continuous kernel is continuous. -/
theorem continuous_convFun {k u : G → ℂ} (hk : Continuous k) {C : ℝ} (hC : ∀ z, ‖k z‖ ≤ C)
    (hu : Integrable u (haarProb G)) : Continuous (convFun k u) := by
  set L : ℝ := ∫ y, ‖u y‖ ∂(haarProb G) with hLdef
  have hL : (0 : ℝ) ≤ L := integral_nonneg fun y => norm_nonneg _
  refine continuous_iff_continuousAt.mpr fun x => ?_
  refine Metric.tendsto_nhds.mpr fun ε hε => ?_
  obtain ⟨V, hVmem, hVlt⟩ :=
    exists_nhds_zero_norm_sub_lt k hk (ε := ε / (2 * (L + 1))) (by positivity)
  have hnbhd : {x' : G | x - x' ∈ V} ∈ nhds x := by
    have hcont : ContinuousAt (fun x' : G => x - x') x :=
      (continuous_const.sub continuous_id).continuousAt
    exact hcont.preimage_mem_nhds (by simpa using hVmem)
  filter_upwards [hnbhd] with x' hx'
  have hb := norm_convFun_sub_le hk hC hu hVlt hx'
  have hfrac : ε / (2 * (L + 1)) * L < ε := by
    rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
    nlinarith [hε, hL]
  rw [dist_eq_norm, ← norm_neg, neg_sub]
  exact lt_of_le_of_lt hb hfrac

end

end CompactAbelian

end GaloisForLFunctions
