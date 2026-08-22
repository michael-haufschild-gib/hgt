import GaloisForLFunctions.RHTower.ConnesFracCommutator

/-!
# The two-sided power tail

Infrastructure for §VII (42) of

  A. Connes, *Trace formula in noncommutative geometry and the zeros of the Riemann zeta
  function*, arXiv:math/9811068.

The commutator of §VII (46) vanishes off `X_Λ = {|x| ≥ Λ − 1}` and is bounded there by
`c |x|^{-p}` with `p = α + m` as large as one likes.  To integrate that majorant over the whole
line one needs the *two-sided* power tail: its integrability and its exact value.

The negative half is obtained from the positive one by the reflection `x ↦ -x`, which preserves
Lebesgue measure; the transfer lemma is stated for an arbitrary even function since it is used
twice.
-/

open MeasureTheory Real Set Filter Topology

namespace GaloisForLFunctions.RHTower

noncomputable section

/-- Integrability of an even function transfers from the right tail to the left tail. -/
theorem connes_integrableOn_Iio_neg_of_even {f : ℝ → ℝ} (hf : ∀ x : ℝ, f (-x) = f x) {R : ℝ}
    (h : IntegrableOn f (Ioi R) volume) : IntegrableOn f (Iio (-R)) volume := by
  have hemb : MeasurableEmbedding (fun x : ℝ => -x) :=
    (Homeomorph.neg ℝ).isClosedEmbedding.measurableEmbedding
  have hpre : (fun x : ℝ => -x) ⁻¹' Iio (-R) = Ioi R := by
    ext x
    simp only [Set.mem_preimage, Set.mem_Iio, Set.mem_Ioi, neg_lt_neg_iff]
  have hmap : (volume : Measure ℝ).restrict (Iio (-R))
      = ((volume : Measure ℝ).restrict (Ioi R)).map (fun x : ℝ => -x) := by
    rw [← hpre, ← Measure.restrict_map measurable_neg measurableSet_Iio,
      Measure.map_neg_eq_self]
  rw [IntegrableOn, hmap, hemb.integrable_map_iff]
  exact h.congr (Filter.Eventually.of_forall fun x => (hf x).symm)

/-- The two-sided power tail set. -/
theorem connes_absTail_measurableSet (R : ℝ) : MeasurableSet {x : ℝ | R ≤ |x|} :=
  measurableSet_le measurable_const measurable_abs

theorem connes_absTail_eq_union {R : ℝ} (hR : 0 < R) :
    {x : ℝ | R ≤ |x|} = Iic (-R) ∪ Ici R := by
  ext x
  simp only [Set.mem_setOf_eq, Set.mem_union, Set.mem_Iic, Set.mem_Ici]
  constructor
  · intro h
    rcases abs_cases x with ⟨he, _⟩ | ⟨he, _⟩
    · right; linarith [he ▸ h]
    · left; linarith [he ▸ h]
  · rintro (h | h)
    · rw [abs_of_nonpos (by linarith)]
      linarith
    · rw [abs_of_nonneg (by linarith)]
      linarith

/-- **The two-sided power tail is integrable.** -/
theorem connes_absRpow_tail_integrable {p : ℝ} (hp : 1 < p) {R : ℝ} (hR : 0 < R) :
    IntegrableOn (fun x : ℝ => |x| ^ (-p)) {x : ℝ | R ≤ |x|} volume := by
  have heven : ∀ x : ℝ, (fun x : ℝ => |x| ^ (-p)) (-x) = (fun x : ℝ => |x| ^ (-p)) x := by
    intro x
    simp only [abs_neg]
  have hIoi : IntegrableOn (fun x : ℝ => |x| ^ (-p)) (Ioi R) volume := by
    have hbase : IntegrableOn (fun x : ℝ => x ^ (-p)) (Ioi R) volume :=
      integrableOn_Ioi_rpow_of_lt (by linarith) hR
    refine hbase.congr_fun (fun x hx => ?_) measurableSet_Ioi
    have hx0 : (0 : ℝ) < x := lt_trans hR hx
    rw [abs_of_pos hx0]
  have hIio : IntegrableOn (fun x : ℝ => |x| ^ (-p)) (Iio (-R)) volume :=
    connes_integrableOn_Iio_neg_of_even heven hIoi
  have hIci : IntegrableOn (fun x : ℝ => |x| ^ (-p)) (Ici R) volume := by
    refine hIoi.congr_set_ae ?_
    exact (MeasureTheory.Ioi_ae_eq_Ici (a := R)).symm
  have hIic : IntegrableOn (fun x : ℝ => |x| ^ (-p)) (Iic (-R)) volume := by
    refine hIio.congr_set_ae ?_
    exact (MeasureTheory.Iio_ae_eq_Iic (a := (-R))).symm
  rw [connes_absTail_eq_union hR]
  exact hIic.union hIci

/-- **The two-sided power tail integral.** -/
theorem connes_absRpow_tail_value {p : ℝ} (hp : 1 < p) {R : ℝ} (hR : 0 < R) :
    (∫ x : ℝ, Set.indicator {x : ℝ | R ≤ |x|} (fun x : ℝ => |x| ^ (-p)) x)
      = 2 * (R ^ (1 - p) / (p - 1)) := by
  have hfold : (∫ x : ℝ, Set.indicator {x : ℝ | R ≤ |x|} (fun x : ℝ => |x| ^ (-p)) x)
      = 2 * ∫ s in Ioi (0 : ℝ), Set.indicator (Ici R) (fun s : ℝ => s ^ (-p)) s := by
    have hcongr : (fun x : ℝ => Set.indicator {x : ℝ | R ≤ |x|} (fun x : ℝ => |x| ^ (-p)) x)
        = fun x : ℝ => (fun s : ℝ => Set.indicator (Ici R) (fun s : ℝ => s ^ (-p)) s) |x| := by
      funext x
      show Set.indicator {x : ℝ | R ≤ |x|} (fun x : ℝ => |x| ^ (-p)) x
        = Set.indicator (Ici R) (fun s : ℝ => s ^ (-p)) |x|
      by_cases hx : R ≤ |x|
      · rw [Set.indicator_of_mem (show x ∈ {x : ℝ | R ≤ |x|} from hx),
          Set.indicator_of_mem (Set.mem_Ici.mpr hx)]
      · rw [Set.indicator_of_notMem (show x ∉ {x : ℝ | R ≤ |x|} from hx),
          Set.indicator_of_notMem (show |x| ∉ Ici R from by simpa using hx)]
    rw [hcongr]
    exact integral_comp_abs (f := fun s : ℝ => Set.indicator (Ici R) (fun s : ℝ => s ^ (-p)) s)
  have hhalf : (∫ s in Ioi (0 : ℝ), Set.indicator (Ici R) (fun s : ℝ => s ^ (-p)) s)
      = ∫ s in Ioi R, s ^ (-p) := by
    rw [MeasureTheory.integral_indicator measurableSet_Ici,
      Measure.restrict_restrict measurableSet_Ici]
    have hset : Ici R ∩ Ioi (0 : ℝ) = Ici R := by
      ext s
      simp only [Set.mem_inter_iff, Set.mem_Ici, Set.mem_Ioi]
      exact ⟨fun h => h.1, fun h => ⟨h, lt_of_lt_of_le hR h⟩⟩
    rw [hset]
    exact (MeasureTheory.setIntegral_congr_set
      (MeasureTheory.Ioi_ae_eq_Ici (a := R))).symm
  have hval : (∫ s in Ioi R, s ^ (-p)) = R ^ (1 - p) / (p - 1) := by
    rw [integral_Ioi_rpow_of_lt (by linarith) hR]
    have h1 : (-p + 1 : ℝ) = -(p - 1) := by ring
    rw [h1, div_neg, neg_div, neg_neg, show -(p - 1) = 1 - p by ring]
  rw [hfold, hhalf, hval]

end

end GaloisForLFunctions.RHTower
