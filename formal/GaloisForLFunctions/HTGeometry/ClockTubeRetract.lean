import GaloisForLFunctions.HTGeometry.ClockTubeSlice
import GaloisForLFunctions.HTGeometry.ClockStripIteratedContinuity

/-!
# The retraction onto a tube, and joint continuity of the transverse Laplacian

The Cauchy representation of a second derivative is continuous in the point and the parameter
together, and on a strip that statement is already available. Transporting it to a tube needs the
family to be defined for every parameter, not only for parameters in the tube; the retraction which
clamps every coordinate into the closed tube supplies that, and inside the tube it is the identity.

With it, the second partial derivative along a coordinate is continuous in the parameter and the
point of the tube together — which is what the iteration needs in order to integrate the step
operator.
-/

namespace GaloisForLFunctions.HTGeometry

open Set Complex Metric

variable {k : ℕ}

/-- The retraction of the several-variable space onto the closed tube of half-width `ρ`. -/
noncomputable def tubeRetract (ρ : ℝ) (z : Fin k → ℂ) : Fin k → ℂ :=
  fun i => stripRetract ρ (z i)

theorem continuous_tubeRetract (ρ : ℝ) : Continuous (tubeRetract (k := k) ρ) :=
  continuous_pi fun i => (continuous_stripRetract ρ).comp (continuous_apply i)

theorem abs_tubeRetract_im_le {ρ : ℝ} (hρ : 0 ≤ ρ) (z : Fin k → ℂ) (i : Fin k) :
    |(tubeRetract ρ z i).im| ≤ ρ :=
  abs_stripRetract_im_le hρ (z i)

theorem tubeRetract_eq_self {ρ : ℝ} {z : Fin k → ℂ} (hz : ∀ i, |(z i).im| ≤ ρ) :
    tubeRetract ρ z = z :=
  funext fun i => stripRetract_eq_self (hz i)

/-- The retracted point, with one coordinate replaced by a point of the larger strip, lies in the
larger tube. -/
theorem update_tubeRetract_mem_tube {ρ ρ' : ℝ} (hρ : ρ < ρ') (hρ0 : 0 ≤ ρ) (z : Fin k → ℂ)
    (i : Fin k) {ζ : ℂ} (hζ : ζ ∈ imStrip ρ') :
    Function.update (tubeRetract ρ z) i ζ ∈ tube k ρ' := by
  intro j
  by_cases hj : j = i
  · subst hj
    rw [Function.update_self]
    exact mem_imStrip.mp hζ
  · rw [Function.update_of_ne hj]
    exact lt_of_le_of_lt (abs_tubeRetract_im_le hρ0 z j) hρ

/-- **The second partial derivative along a coordinate is continuous in the parameter and the point
of the tube together.** -/
theorem continuousAt_cpartial_cpartial_of_tube {P : Type*} [TopologicalSpace P] {ρ ρ' : ℝ}
    (hρ : ρ < ρ') (hρ0 : 0 ≤ ρ) {W : P → (Fin k → ℂ) → ℂ}
    (hWc : ContinuousOn (fun q : P × (Fin k → ℂ) => W q.1 q.2) (univ ×ˢ tube k ρ'))
    (hWd : ∀ p : P, SliceHolo (W p) ρ') (i : Fin k)
    {q : P × (Fin k → ℂ)} (hq : q.2 ∈ tube k ρ) :
    ContinuousAt (fun q' : P × (Fin k → ℂ) => cpartial i (cpartial i (W q'.1)) q'.2) q := by
  classical
  set W' : P × (Fin k → ℂ) → ℂ → ℂ :=
    fun p ζ => W p.1 (Function.update (tubeRetract ρ p.2) i ζ) with hW'
  have hmaps : ∀ r : (P × (Fin k → ℂ)) × ℂ, r.2 ∈ imStrip ρ' →
      ((r.1.1, Function.update (tubeRetract ρ r.1.2) i r.2) : P × (Fin k → ℂ))
        ∈ univ ×ˢ tube k ρ' :=
    fun r hr => ⟨mem_univ _, update_tubeRetract_mem_tube hρ hρ0 r.1.2 i hr⟩
  have hcontmap : Continuous fun r : (P × (Fin k → ℂ)) × ℂ =>
      ((r.1.1, Function.update (tubeRetract ρ r.1.2) i r.2) : P × (Fin k → ℂ)) := by
    refine (continuous_fst.comp continuous_fst).prodMk ?_
    refine continuous_pi fun j => ?_
    by_cases hj : j = i
    · subst hj
      simpa using continuous_snd
    · simp only [Function.update_of_ne hj]
      exact ((continuous_stripRetract ρ).comp
        ((continuous_apply j).comp (continuous_snd.comp continuous_fst)))
  have hW'c : ContinuousOn (fun r : (P × (Fin k → ℂ)) × ℂ => W' r.1 r.2)
      (univ ×ˢ imStrip ρ') := by
    intro r hr
    have hmem : ((r.1.1, Function.update (tubeRetract ρ r.1.2) i r.2) : P × (Fin k → ℂ))
        ∈ univ ×ˢ tube k ρ' := hmaps r hr.2
    have hbase : ContinuousAt (fun q : P × (Fin k → ℂ) => W q.1 q.2)
        ((r.1.1, Function.update (tubeRetract ρ r.1.2) i r.2)) :=
      hWc.continuousAt ((isOpen_univ.prod (isOpen_tube k ρ')).mem_nhds hmem)
    exact (hbase.comp (x := r)
      (f := fun r' : (P × (Fin k → ℂ)) × ℂ =>
        ((r'.1.1, Function.update (tubeRetract ρ r'.1.2) i r'.2) : P × (Fin k → ℂ)))
      hcontmap.continuousAt).continuousWithinAt
  have hW'd : ∀ p : P × (Fin k → ℂ), DifferentiableOn ℂ (W' p) (imStrip ρ') := by
    intro p
    refine hWd p.1 (tubeRetract ρ p.2) ?_ i
    intro j
    exact lt_of_le_of_lt (abs_tubeRetract_im_le hρ0 p.2 j) hρ
  have hbase := continuousAt_deriv_deriv_of_strip (P := P × (Fin k → ℂ)) hρ hρ0 hW'c hW'd
    (q := ((q.1, q.2), q.2 i)) (mem_imStrip.mpr (hq i))
  have hshift : ContinuousAt
      (fun q' : P × (Fin k → ℂ) => (((q'.1, q'.2), q'.2 i) : (P × (Fin k → ℂ)) × ℂ)) q :=
    (continuous_id.prodMk ((continuous_apply i).comp continuous_snd)).continuousAt
  have hcomp := hbase.comp (x := q)
    (f := fun q' : P × (Fin k → ℂ) => (((q'.1, q'.2), q'.2 i) : (P × (Fin k → ℂ)) × ℂ)) hshift
  refine hcomp.congr ?_
  refine Filter.eventuallyEq_of_mem
    (((isOpen_tube k ρ).preimage continuous_snd).mem_nhds hq) fun q' hq' => ?_
  have hret : tubeRetract ρ q'.2 = q'.2 := tubeRetract_eq_self fun j => le_of_lt (hq' j)
  show deriv (deriv (W' (q'.1, q'.2))) (q'.2 i)
      = cpartial i (cpartial i (W q'.1)) q'.2
  rw [cpartial_cpartial_eq, hW']
  simp only [hret]

/-- **The first partial derivative along a coordinate is continuous in the parameter and the point of
the tube together.** -/
theorem continuousAt_cpartial_of_tube {P : Type*} [TopologicalSpace P] {ρ ρ' : ℝ}
    (hρ : ρ < ρ') (hρ0 : 0 ≤ ρ) {W : P → (Fin k → ℂ) → ℂ}
    (hWc : ContinuousOn (fun q : P × (Fin k → ℂ) => W q.1 q.2) (univ ×ˢ tube k ρ'))
    (hWd : ∀ p : P, SliceHolo (W p) ρ') (i : Fin k)
    {q : P × (Fin k → ℂ)} (hq : q.2 ∈ tube k ρ) :
    ContinuousAt (fun q' : P × (Fin k → ℂ) => cpartial i (W q'.1) q'.2) q := by
  classical
  set W' : P × (Fin k → ℂ) → ℂ → ℂ :=
    fun p ζ => W p.1 (Function.update (tubeRetract ρ p.2) i ζ) with hW'
  have hmaps : ∀ r : (P × (Fin k → ℂ)) × ℂ, r.2 ∈ imStrip ρ' →
      ((r.1.1, Function.update (tubeRetract ρ r.1.2) i r.2) : P × (Fin k → ℂ))
        ∈ univ ×ˢ tube k ρ' :=
    fun r hr => ⟨mem_univ _, update_tubeRetract_mem_tube hρ hρ0 r.1.2 i hr⟩
  have hcontmap : Continuous fun r : (P × (Fin k → ℂ)) × ℂ =>
      ((r.1.1, Function.update (tubeRetract ρ r.1.2) i r.2) : P × (Fin k → ℂ)) := by
    refine (continuous_fst.comp continuous_fst).prodMk ?_
    refine continuous_pi fun j => ?_
    by_cases hj : j = i
    · subst hj
      simpa using continuous_snd
    · simp only [Function.update_of_ne hj]
      exact ((continuous_stripRetract ρ).comp
        ((continuous_apply j).comp (continuous_snd.comp continuous_fst)))
  have hW'c : ContinuousOn (fun r : (P × (Fin k → ℂ)) × ℂ => W' r.1 r.2)
      (univ ×ˢ imStrip ρ') := by
    intro r hr
    have hmem : ((r.1.1, Function.update (tubeRetract ρ r.1.2) i r.2) : P × (Fin k → ℂ))
        ∈ univ ×ˢ tube k ρ' := hmaps r hr.2
    have hbase : ContinuousAt (fun q : P × (Fin k → ℂ) => W q.1 q.2)
        ((r.1.1, Function.update (tubeRetract ρ r.1.2) i r.2)) :=
      hWc.continuousAt ((isOpen_univ.prod (isOpen_tube k ρ')).mem_nhds hmem)
    exact (hbase.comp (x := r)
      (f := fun r' : (P × (Fin k → ℂ)) × ℂ =>
        ((r'.1.1, Function.update (tubeRetract ρ r'.1.2) i r'.2) : P × (Fin k → ℂ)))
      hcontmap.continuousAt).continuousWithinAt
  have hW'd : ∀ p : P × (Fin k → ℂ), DifferentiableOn ℂ (W' p) (imStrip ρ') := by
    intro p
    refine hWd p.1 (tubeRetract ρ p.2) ?_ i
    intro j
    exact lt_of_le_of_lt (abs_tubeRetract_im_le hρ0 p.2 j) hρ
  have hbase := continuousAt_deriv_of_strip (P := P × (Fin k → ℂ)) hρ hρ0 hW'c hW'd
    (q := ((q.1, q.2), q.2 i)) (mem_imStrip.mpr (hq i))
  have hshift : ContinuousAt
      (fun q' : P × (Fin k → ℂ) => (((q'.1, q'.2), q'.2 i) : (P × (Fin k → ℂ)) × ℂ)) q :=
    (continuous_id.prodMk ((continuous_apply i).comp continuous_snd)).continuousAt
  have hcomp := hbase.comp (x := q)
    (f := fun q' : P × (Fin k → ℂ) => (((q'.1, q'.2), q'.2 i) : (P × (Fin k → ℂ)) × ℂ)) hshift
  refine hcomp.congr ?_
  refine Filter.eventuallyEq_of_mem
    (((isOpen_tube k ρ).preimage continuous_snd).mem_nhds hq) fun q' hq' => ?_
  have hret : tubeRetract ρ q'.2 = q'.2 := tubeRetract_eq_self fun j => le_of_lt (hq' j)
  show deriv (W' (q'.1, q'.2)) (q'.2 i) = cpartial i (W q'.1) q'.2
  rw [cpartial, hW']
  simp only [hret]

/-- **A point of an open tube has a strictly smaller tube around it**: the finitely many
coordinates have a largest imaginary part, and it is still below the half-width. -/
theorem exists_inner_radius {ρ : ℝ} (hρ : 0 < ρ) {z : Fin k → ℂ} (hz : z ∈ tube k ρ) :
    ∃ ρ₁ : ℝ, 0 ≤ ρ₁ ∧ ρ₁ < ρ ∧ z ∈ tube k ρ₁ := by
  classical
  set M : ℝ := Finset.univ.fold max 0 (fun i : Fin k => |(z i).im|) with hM
  have hM0 : (0 : ℝ) ≤ M := by
    rw [hM]
    exact (Finset.le_fold_max 0).mpr (Or.inl le_rfl)
  have hMlt : M < ρ := by
    rw [hM]
    exact (Finset.fold_max_lt ρ).mpr ⟨hρ, fun i _ => hz i⟩
  refine ⟨(M + ρ) / 2, by linarith, by linarith, fun i => ?_⟩
  have hle : |(z i).im| ≤ M := by
    rw [hM]
    exact (Finset.le_fold_max _).mpr (Or.inr ⟨i, Finset.mem_univ i, le_rfl⟩)
  linarith

/-! ## The double integral over a tube -/

/-- **The double integral of a family continuous on a tube is continuous on the smaller tube.** -/
theorem continuousAt_iteratedIntegral_of_tube {ρ ρ₁ : ℝ} (hρ₁ : ρ₁ < ρ) (hρ₁0 : 0 ≤ ρ₁)
    {G : ℝ → ℝ → (Fin k → ℂ) → ℂ}
    (hG : ContinuousOn (fun r : (ℝ × ℝ) × (Fin k → ℂ) => G r.1.1 r.1.2 r.2)
      (univ ×ˢ tube k ρ))
    {q : (ℝ × ℝ) × (Fin k → ℂ)} (hq : q.2 ∈ tube k ρ₁) :
    ContinuousAt (fun r : (ℝ × ℝ) × (Fin k → ℂ) =>
      ∫ s in (0 : ℝ)..r.1.1, ∫ t in (0 : ℝ)..r.1.2, G s t r.2) q := by
  classical
  have hmaps : ∀ z : Fin k → ℂ, tubeRetract ρ₁ z ∈ tube k ρ :=
    fun z j => lt_of_le_of_lt (abs_tubeRetract_im_le hρ₁0 z j) hρ₁
  have hGret : Continuous fun r : (ℝ × ℝ) × (Fin k → ℂ) =>
      G r.1.1 r.1.2 (tubeRetract ρ₁ r.2) := by
    have hmap : Continuous fun r : (ℝ × ℝ) × (Fin k → ℂ) =>
        ((r.1, tubeRetract ρ₁ r.2) : (ℝ × ℝ) × (Fin k → ℂ)) :=
      continuous_fst.prodMk ((continuous_tubeRetract ρ₁).comp continuous_snd)
    exact hG.comp_continuous hmap fun r => ⟨mem_univ _, hmaps r.2⟩
  have hcont := continuous_iteratedIntegral
    (G := fun s t z => G s t (tubeRetract ρ₁ z)) hGret
  refine (hcont.continuousAt).congr ?_
  refine Filter.eventuallyEq_of_mem
    (((isOpen_tube k ρ₁).preimage continuous_snd).mem_nhds hq) fun r hr => ?_
  have hrz : tubeRetract ρ₁ r.2 = r.2 := tubeRetract_eq_self fun j => le_of_lt (hr j)
  show (∫ s in (0 : ℝ)..r.1.1, ∫ t in (0 : ℝ)..r.1.2, G s t (tubeRetract ρ₁ r.2))
    = ∫ s in (0 : ℝ)..r.1.1, ∫ t in (0 : ℝ)..r.1.2, G s t r.2
  rw [hrz]

/-- **The inner integral of a family continuous on a tube is continuous on the smaller tube**,
jointly in the remaining null coordinate and the point. -/
theorem continuousAt_innerIntegral_of_tube {ρ ρ₁ η : ℝ} (hρ₁ : ρ₁ < ρ) (hρ₁0 : 0 ≤ ρ₁)
    {H : ℝ → ℝ → (Fin k → ℂ) → ℂ}
    (hH : ContinuousOn (fun r : (ℝ × ℝ) × (Fin k → ℂ) => H r.1.1 r.1.2 r.2)
      (univ ×ˢ tube k ρ))
    {q : ℝ × (Fin k → ℂ)} (hq : q.2 ∈ tube k ρ₁) :
    ContinuousAt (fun r : ℝ × (Fin k → ℂ) => ∫ t in (0 : ℝ)..η, H r.1 t r.2) q := by
  classical
  have hmaps : ∀ z : Fin k → ℂ, tubeRetract ρ₁ z ∈ tube k ρ :=
    fun z j => lt_of_le_of_lt (abs_tubeRetract_im_le hρ₁0 z j) hρ₁
  have hHret : Continuous fun r : (ℝ × ℝ) × (Fin k → ℂ) =>
      H r.1.1 r.1.2 (tubeRetract ρ₁ r.2) := by
    have hmap : Continuous fun r : (ℝ × ℝ) × (Fin k → ℂ) =>
        ((r.1, tubeRetract ρ₁ r.2) : (ℝ × ℝ) × (Fin k → ℂ)) :=
      continuous_fst.prodMk ((continuous_tubeRetract ρ₁).comp continuous_snd)
    exact hH.comp_continuous hmap fun r => ⟨mem_univ _, hmaps r.2⟩
  have hcont : Continuous fun r : ℝ × (Fin k → ℂ) =>
      ∫ t in (0 : ℝ)..η, H r.1 t (tubeRetract ρ₁ r.2) := by
    refine intervalIntegral.continuous_parametric_intervalIntegral_of_continuous
      (f := fun (r : ℝ × (Fin k → ℂ)) (t : ℝ) => H r.1 t (tubeRetract ρ₁ r.2)) ?_
      continuous_const
    exact hHret.comp (((continuous_fst.comp continuous_fst).prodMk continuous_snd).prodMk
      (continuous_snd.comp continuous_fst))
  refine (hcont.continuousAt).congr ?_
  refine Filter.eventuallyEq_of_mem
    (((isOpen_tube k ρ₁).preimage continuous_snd).mem_nhds hq) fun r hr => ?_
  have hrz : tubeRetract ρ₁ r.2 = r.2 := tubeRetract_eq_self fun j => le_of_lt (hr j)
  show (∫ t in (0 : ℝ)..η, H r.1 t (tubeRetract ρ₁ r.2))
    = ∫ t in (0 : ℝ)..η, H r.1 t r.2
  rw [hrz]

end GaloisForLFunctions.HTGeometry
