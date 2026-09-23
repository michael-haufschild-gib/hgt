import GaloisForLFunctions.HTGeometry.ConstitutiveFormationCompletionExchange
import Mathlib.Topology.Instances.AddCircle.DenseSubgroup

/-!
# Sharp calibrations of the formation/completion exchange

Finite-depth exchange of formation with completion needs a compact carrier and continuous
formations.  Each hypothesis is shown load-bearing by an explicit countermodel.

* Noncompact carrier: on the closed ray `[1, ∞)` the single continuous formation `x ↦ 1/(1+x²)`
  already breaks depth-one exchange at the limit `0`.
* Discontinuous formation: on `ℝ` a formation that is `1` at the origin and `0` elsewhere carries
  the completed input to a law outside the completion of the formed input.
-/

namespace GaloisForLFunctions.HTGeometry

open Filter Topology

/-! ## Compactness is load-bearing -/

/-- The noncompact witness formation. -/
noncomputable def noncompactCalibrationFormation : Unit → ℝ → ℝ := fun _ x => 1 / (1 + x ^ (2 : ℕ))

theorem tendsto_noncompactCalibrationFormation :
    Tendsto (fun n : ℕ => noncompactCalibrationFormation () ((n : ℝ) + 1)) atTop (𝓝 0) := by
  have hden : Tendsto (fun n : ℕ => 1 + ((n : ℝ) + 1) ^ (2 : ℕ)) atTop atTop := by
    refine tendsto_atTop_mono (fun n => ?_) tendsto_natCast_atTop_atTop
    have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    nlinarith
  have hinv := hden.inv_tendsto_atTop
  simpa [noncompactCalibrationFormation, one_div, Pi.inv_def] using hinv

theorem noncompactCalibration_mem_closure :
    (0 : ℝ) ∈ closure (boundedFormationReach noncompactCalibrationFormation 1 (Set.Ici 1)) := by
  refine mem_closure_of_tendsto tendsto_noncompactCalibrationFormation ?_
  filter_upwards with n
  refine mem_boundedFormationReach.mpr ⟨[()], by simp, ?_⟩
  refine ⟨(n : ℝ) + 1, ?_, rfl⟩
  have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  simp only [Set.mem_Ici]
  linarith

theorem noncompactCalibration_notMem :
    (0 : ℝ) ∉ boundedFormationReach noncompactCalibrationFormation 1 (closure (Set.Ici 1)) := by
  rw [isClosed_Ici.closure_eq]
  intro hmem
  obtain ⟨w, hlen, hw⟩ := mem_boundedFormationReach.mp hmem
  rcases w with _ | ⟨u, rest⟩
  · simp only [runFormations_nil, Set.mem_Ici] at hw
    linarith
  · rcases rest with _ | ⟨v, rest2⟩
    · obtain ⟨x, hx, hval⟩ := hw
      simp only [Set.mem_Ici] at hx
      have hpos : (0 : ℝ) < 1 / (1 + x ^ (2 : ℕ)) := by positivity
      have hval' : (1 : ℝ) / (1 + x ^ (2 : ℕ)) = 0 := hval
      linarith [hval' ▸ hpos]
    · simp at hlen

/-- **Compactness is load-bearing.**  On a noncompact carrier a single continuous formation
already breaks depth-one exchange: the completion of the formed set meets a law that the formation
of the completed set misses. -/
theorem noncompact_depthOne_completionExchange_fails :
    (0 : ℝ) ∈ closure (boundedFormationReach noncompactCalibrationFormation 1 (Set.Ici 1)) \
      boundedFormationReach noncompactCalibrationFormation 1 (closure (Set.Ici 1)) :=
  ⟨noncompactCalibration_mem_closure, noncompactCalibration_notMem⟩

/-! ## Continuity is load-bearing -/

/-- The discontinuous witness formation. -/
noncomputable def discontinuousCalibrationFormation : Unit → ℝ → ℝ :=
  fun _ x => if x = 0 then 1 else 0

/-- The input whose completion adds the origin. -/
noncomputable def discontinuousCalibrationInput : Set ℝ := Set.range fun n : ℕ => 1 / ((n : ℝ) + 2)

theorem zero_mem_closure_discontinuousCalibrationInput :
    (0 : ℝ) ∈ closure discontinuousCalibrationInput := by
  have hden : Tendsto (fun n : ℕ => (n : ℝ) + 2) atTop atTop := by
    refine tendsto_atTop_mono (fun n => ?_) tendsto_natCast_atTop_atTop
    linarith
  have htend : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 2)) atTop (𝓝 0) := by
    simpa [one_div, Pi.inv_def] using hden.inv_tendsto_atTop
  refine mem_closure_of_tendsto htend ?_
  filter_upwards with n
  exact ⟨n, rfl⟩

theorem discontinuousCalibration_mem_image :
    (1 : ℝ) ∈ boundedFormationReach discontinuousCalibrationFormation 1
      (closure discontinuousCalibrationInput) := by
  refine mem_boundedFormationReach.mpr ⟨[()], by simp, ?_⟩
  refine ⟨0, zero_mem_closure_discontinuousCalibrationInput, ?_⟩
  simp [discontinuousCalibrationFormation]

theorem discontinuousCalibration_subset :
    boundedFormationReach discontinuousCalibrationFormation 1 discontinuousCalibrationInput
      ⊆ Set.Iic (1 / 2 : ℝ) := by
  intro y hy
  obtain ⟨w, hlen, hw⟩ := mem_boundedFormationReach.mp hy
  rcases w with _ | ⟨u, rest⟩
  · obtain ⟨n, hn⟩ := hw
    have hn2 : (2 : ℝ) ≤ (n : ℝ) + 2 := by
      have : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
      linarith
    simp only [Set.mem_Iic, ← hn]
    exact one_div_le_one_div_of_le (by norm_num) hn2
  · rcases rest with _ | ⟨v, rest2⟩
    · obtain ⟨x, hx, hval⟩ := hw
      obtain ⟨n, hn⟩ := hx
      have hxne : x ≠ 0 := by
        rw [← hn]
        positivity
      have hval' : (if x = 0 then (1 : ℝ) else 0) = y := hval
      rw [if_neg hxne] at hval'
      simp only [Set.mem_Iic, ← hval']
      norm_num
    · simp at hlen

theorem discontinuousCalibration_notMem_closure :
    (1 : ℝ) ∉ closure (boundedFormationReach discontinuousCalibrationFormation 1
      discontinuousCalibrationInput) := by
  intro hmem
  have h1 : (1 : ℝ) ∈ Set.Iic (1 / 2 : ℝ) :=
    (isClosed_Iic.closure_subset_iff.mpr discontinuousCalibration_subset) hmem
  simp only [Set.mem_Iic] at h1
  linarith

/-- **Continuity is load-bearing.**  A discontinuous formation carries the completed input to a
law outside the completion of the formed input, so exchange fails at depth one in the reverse
direction. -/
theorem discontinuous_depthOne_completionExchange_fails :
    (1 : ℝ) ∈ boundedFormationReach discontinuousCalibrationFormation 1
        (closure discontinuousCalibrationInput) \
      closure (boundedFormationReach discontinuousCalibrationFormation 1
        discontinuousCalibrationInput) :=
  ⟨discontinuousCalibration_mem_image, discontinuousCalibration_notMem_closure⟩

end GaloisForLFunctions.HTGeometry

namespace GaloisForLFunctions.HTGeometry

open Filter Topology

/-! ## Unbounded depth is necessary but not sufficient -/

theorem setImage_iterate {X : Type*} (f : X → X) (k : ℕ) (A : Set X) :
    (fun S : Set X => f '' S)^[k] A = f^[k] '' A := by
  induction k generalizing A with
  | zero => simp
  | succ k ih =>
      rw [Function.iterate_succ_apply, ih, Function.iterate_succ, Set.image_comp]

/-- On a one-generator signature a formation word acts by iteration of its generator. -/
theorem runFormations_unit {X : Type*} (φ : Unit → X → X) (w : List Unit) (A : Set X) :
    runFormations (imageFormation φ) w A = (φ ())^[w.length] '' A := by
  have hfold : ∀ (v : List Unit) (B : Set X),
      runFormations (imageFormation φ) v B = (fun S : Set X => φ () '' S)^[v.length] B := by
    intro v
    induction v with
    | nil => intro B; rfl
    | cons u rest ih =>
        intro B
        cases u
        rw [runFormations, List.foldl_cons, ← runFormations, ih, List.length_cons,
          Function.iterate_succ_apply]
        rfl
  rw [hfold, setImage_iterate]

/-- The saturation of a one-generator signature is the union of the iterated images. -/
theorem formationSaturation_unit {X : Type*} (φ : Unit → X → X) (A : Set X) :
    formationSaturation φ A = ⋃ k : ℕ, (φ ())^[k] '' A := by
  ext x
  simp only [mem_formationSaturation, Set.mem_iUnion]
  constructor
  · rintro ⟨w, hw⟩
    exact ⟨w.length, by rwa [runFormations_unit] at hw⟩
  · rintro ⟨k, hk⟩
    refine ⟨List.replicate k (), ?_⟩
    rw [runFormations_unit, List.length_replicate]
    exact hk

/-- The witness formation for depth insufficiency. -/
noncomputable def depthCalibrationFormation : Unit → ℝ → ℝ := fun _ x => x / (1 + x)

theorem depthCalibrationFormation_iterate_zero (k : ℕ) :
    (depthCalibrationFormation ())^[k] 0 = 0 := by
  induction k with
  | zero => simp
  | succ k ih => rw [Function.iterate_succ_apply', ih, depthCalibrationFormation]; norm_num

theorem depthCalibrationFormation_iterate_one (k : ℕ) :
    (depthCalibrationFormation ())^[k] 1 = 1 / ((k : ℝ) + 1) := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [Function.iterate_succ_apply', ih, depthCalibrationFormation]
      have hk : (0 : ℝ) < (k : ℝ) + 1 := by positivity
      push_cast
      field_simp

theorem depthCalibration_saturation :
    formationSaturation depthCalibrationFormation ({0, 1} : Set ℝ)
      = insert 0 (Set.range fun k : ℕ => 1 / ((k : ℝ) + 1)) := by
  rw [formationSaturation_unit]
  ext x
  simp only [Set.mem_iUnion, Set.mem_image, Set.mem_insert_iff, Set.mem_range,
    Set.mem_singleton_iff]
  constructor
  · rintro ⟨k, y, hy, rfl⟩
    rcases hy with rfl | rfl
    · exact Or.inl (depthCalibrationFormation_iterate_zero k)
    · exact Or.inr ⟨k, (depthCalibrationFormation_iterate_one k).symm⟩
  · rintro (rfl | ⟨k, rfl⟩)
    · exact ⟨0, 0, Or.inl rfl, rfl⟩
    · exact ⟨k, 1, Or.inr rfl, depthCalibrationFormation_iterate_one k⟩

theorem tendsto_depthCalibration_tail :
    Tendsto (fun k : ℕ => 1 / ((k : ℝ) + 1)) atTop (𝓝 0) := by
  have hden : Tendsto (fun k : ℕ => (k : ℝ) + 1) atTop atTop := by
    refine tendsto_atTop_mono (fun k => ?_) tendsto_natCast_atTop_atTop
    linarith
  simpa [one_div, Pi.inv_def] using hden.inv_tendsto_atTop

theorem isClosed_depthCalibration_saturation :
    IsClosed (formationSaturation depthCalibrationFormation ({0, 1} : Set ℝ)) := by
  rw [depthCalibration_saturation]
  exact (tendsto_depthCalibration_tail.isCompact_insert_range).isClosed

theorem depthCalibration_saturation_infinite :
    (formationSaturation depthCalibrationFormation ({0, 1} : Set ℝ)).Infinite := by
  rw [depthCalibration_saturation]
  refine Set.Infinite.mono (Set.subset_insert _ _) ?_
  refine Set.infinite_range_of_injective (fun a b hab => ?_)
  have ha : (0 : ℝ) < (a : ℝ) + 1 := by positivity
  have hb : (0 : ℝ) < (b : ℝ) + 1 := by positivity
  field_simp at hab
  have : (a : ℝ) = (b : ℝ) := by linarith
  exact_mod_cast this

/-- **Unbounded depth is necessary but not sufficient.**  From a two-law start the formation
`x ↦ x/(1+x)` produces infinitely many laws, so no finite depth exhausts the saturation; yet the
saturation is already closed and the completion boundary is empty. -/
theorem unbounded_depth_not_sufficient :
    (formationSaturation depthCalibrationFormation ({0, 1} : Set ℝ)).Infinite ∧
      formationCompletionBoundary depthCalibrationFormation ({0, 1} : Set ℝ) = ∅ := by
  refine ⟨depthCalibration_saturation_infinite, ?_⟩
  have hclosed : closure (formationSaturation depthCalibrationFormation ({0, 1} : Set ℝ))
      = formationSaturation depthCalibrationFormation ({0, 1} : Set ℝ) :=
    isClosed_depthCalibration_saturation.closure_eq
  have hA : closure ({0, 1} : Set ℝ) = ({0, 1} : Set ℝ) :=
    (Set.toFinite _).isClosed.closure_eq
  rw [formationCompletionBoundary, hclosed, hA, Set.sdiff_self]

end GaloisForLFunctions.HTGeometry

namespace GaloisForLFunctions.HTGeometry

open Filter Topology

/-! ## A compact system with nonempty completion boundary -/

/-- The two-generator rotation system on the circle: one generator rotates forward by `α`, the
other backward, so its formation words realize exactly the `ℤ`-orbit. -/
def rotationCalibrationFormation (α : ℝ) : Bool → AddCircle (1 : ℝ) → AddCircle (1 : ℝ) :=
  fun b x => if b then x - ((α : ℝ) : AddCircle (1 : ℝ)) else x + ((α : ℝ) : AddCircle (1 : ℝ))

theorem rotationCalibration_run (α : ℝ) (w : List Bool) :
    ∃ n : ℤ, runFormations (imageFormation (rotationCalibrationFormation α)) w
        ({0} : Set (AddCircle (1 : ℝ)))
      = {n • ((α : ℝ) : AddCircle (1 : ℝ))} := by
  induction w using List.reverseRecOn with
  | nil => exact ⟨0, by simp⟩
  | append_singleton rest b ih =>
      obtain ⟨n, hn⟩ := ih
      have hstep : runFormations (imageFormation (rotationCalibrationFormation α)) (rest ++ [b])
          ({0} : Set (AddCircle (1 : ℝ)))
          = imageFormation (rotationCalibrationFormation α) b
            (runFormations (imageFormation (rotationCalibrationFormation α)) rest
              ({0} : Set (AddCircle (1 : ℝ)))) := by
        simp [runFormations, List.foldl_append]
      cases b with
      | false =>
          refine ⟨n + 1, ?_⟩
          rw [hstep, hn]
          simp only [imageFormation, Set.image_singleton, rotationCalibrationFormation,
            Bool.false_eq_true, if_false]
          rw [add_one_zsmul]
      | true =>
          refine ⟨n - 1, ?_⟩
          rw [hstep, hn]
          simp only [imageFormation, Set.image_singleton, rotationCalibrationFormation, if_true]
          rw [sub_one_zsmul, sub_eq_add_neg]

theorem rotationCalibration_replicate (α : ℝ) (k : ℕ) :
    runFormations (imageFormation (rotationCalibrationFormation α)) (List.replicate k false)
        ({0} : Set (AddCircle (1 : ℝ)))
      = {(k : ℤ) • ((α : ℝ) : AddCircle (1 : ℝ))} := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [List.replicate_succ', runFormations, List.foldl_append]
      show imageFormation (rotationCalibrationFormation α) false
        (runFormations (imageFormation (rotationCalibrationFormation α))
          (List.replicate k false) {0}) = _
      rw [ih]
      simp only [imageFormation, Set.image_singleton,
        rotationCalibrationFormation, Bool.false_eq_true, if_false]
      rw [show ((k + 1 : ℕ) : ℤ) = (k : ℤ) + 1 by push_cast; ring, add_one_zsmul]

theorem rotationCalibration_replicate_neg (α : ℝ) (k : ℕ) :
    runFormations (imageFormation (rotationCalibrationFormation α)) (List.replicate k true)
        ({0} : Set (AddCircle (1 : ℝ)))
      = {(-(k : ℤ)) • ((α : ℝ) : AddCircle (1 : ℝ))} := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [List.replicate_succ', runFormations, List.foldl_append]
      show imageFormation (rotationCalibrationFormation α) true
        (runFormations (imageFormation (rotationCalibrationFormation α))
          (List.replicate k true) {0}) = _
      rw [ih]
      simp only [imageFormation, Set.image_singleton, rotationCalibrationFormation, if_true]
      rw [show (-((k + 1 : ℕ) : ℤ)) = (-(k : ℤ)) - 1 by push_cast; ring, sub_one_zsmul,
        sub_eq_add_neg]

theorem rotationCalibration_saturation (α : ℝ) :
    formationSaturation (rotationCalibrationFormation α) ({0} : Set (AddCircle (1 : ℝ)))
      = Set.range (fun n : ℤ => n • ((α : ℝ) : AddCircle (1 : ℝ))) := by
  ext x
  simp only [mem_formationSaturation, Set.mem_range]
  constructor
  · rintro ⟨w, hw⟩
    obtain ⟨n, hn⟩ := rotationCalibration_run α w
    rw [hn, Set.mem_singleton_iff] at hw
    exact ⟨n, hw.symm⟩
  · rintro ⟨n, rfl⟩
    rcases le_or_gt 0 n with hn | hn
    · refine ⟨List.replicate n.toNat false, ?_⟩
      rw [rotationCalibration_replicate]
      simp [Int.toNat_of_nonneg hn]
    · refine ⟨List.replicate (-n).toNat true, ?_⟩
      rw [rotationCalibration_replicate_neg]
      simp [Int.toNat_of_nonneg (by omega : (0:ℤ) ≤ -n)]

theorem rotationCalibration_dense {α : ℝ} (hα : Irrational α) :
    closure (formationSaturation (rotationCalibrationFormation α)
      ({0} : Set (AddCircle (1 : ℝ)))) = Set.univ := by
  rw [rotationCalibration_saturation]
  have hirr : Irrational (α / 1) := by simpa using hα
  have hdense : DenseRange (fun n : ℤ => n • ((α : ℝ) : AddCircle (1 : ℝ))) :=
    (AddCircle.denseRange_zsmul_coe_iff).mpr hirr
  exact hdense.closure_eq

theorem rotationCalibration_half_notMem {α : ℝ} (hα : Irrational α) :
    (((α / 2 : ℝ)) : AddCircle (1 : ℝ)) ∉
      formationSaturation (rotationCalibrationFormation α) ({0} : Set (AddCircle (1 : ℝ))) := by
  rw [rotationCalibration_saturation]
  rintro ⟨n, hn⟩
  have hval : (((n : ℝ) * α : ℝ) : AddCircle (1 : ℝ)) = ((α / 2 : ℝ) : AddCircle (1 : ℝ)) := by
    rw [← hn]
    simp
  have hzero : (((n : ℝ) * α - α / 2 : ℝ) : AddCircle (1 : ℝ)) = 0 := by
    have hsub : (((n : ℝ) * α : ℝ) : AddCircle (1 : ℝ)) - ((α / 2 : ℝ) : AddCircle (1 : ℝ)) = 0 := by
      rw [hval, sub_self]
    simpa using hsub
  obtain ⟨m, hm⟩ := (AddCircle.coe_eq_zero_iff (1 : ℝ)).mp hzero
  have hm' : α * ((n : ℝ) - 1 / 2) = (m : ℝ) := by
    have h := hm
    simp only [zsmul_eq_mul, mul_one] at h
    rw [h]
    ring
  have hne : ((n : ℝ) - 1 / 2) ≠ 0 := by
    intro h
    have hcast : ((2 * n : ℤ) : ℝ) = ((1 : ℤ) : ℝ) := by
      push_cast
      linarith
    have h3 : (2 * n : ℤ) = 1 := by exact_mod_cast hcast
    omega
  have hrat : α = (m : ℝ) / ((n : ℝ) - 1 / 2) := by
    rw [eq_div_iff hne]
    exact hm'
  exact hα ⟨(m : ℚ) / ((n : ℚ) - 1 / 2), by
    rw [hrat]
    push_cast
    ring⟩

/-- **A compact finite system with nonempty completion boundary.**  On the circle, the
two-generator rotation system by an irrational angle has a dense but proper `ℤ`-orbit from a single
starting law, so completing the saturation produces laws that no finite formation word reaches. -/
theorem rotationCalibration_completionBoundary_nonempty {α : ℝ} (hα : Irrational α) :
    (formationCompletionBoundary (rotationCalibrationFormation α)
      ({0} : Set (AddCircle (1 : ℝ)))).Nonempty := by
  refine ⟨((α / 2 : ℝ) : AddCircle (1 : ℝ)), ?_, ?_⟩
  · rw [rotationCalibration_dense hα]
    trivial
  · rw [(Set.toFinite ({0} : Set (AddCircle (1 : ℝ)))).isClosed.closure_eq]
    exact rotationCalibration_half_notMem hα

end GaloisForLFunctions.HTGeometry
