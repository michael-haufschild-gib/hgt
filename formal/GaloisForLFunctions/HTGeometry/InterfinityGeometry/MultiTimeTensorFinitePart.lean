import GaloisForLFunctions.HTGeometry.InterfinityGeometry.SpectralCutObstruction
import GaloisForLFunctions.HTGeometry.InterfinityGeometry.MultiTimeIntegrability

/-!
# The tensor finite part and its face lattice

The tensor finite part of `d` independent times pairs a tensor chart against the product of the
one-dimensional finite parts.  Applying the difference of transport and identity in every
coordinate returns the tensor source pairing, so the cubical source cochain is an iterated
finite-part coboundary at every admissible observer, and the alternating sum of the face orbits
computes that iterated difference.

A face orbit tends to zero exactly when every one of its times lies above its own cut: with all
`a_j > 0` each factor of a nonempty face vanishes in the limit, while a single deficient
coordinate makes its own singleton face diverge.
-/

namespace GaloisForLFunctions.HTGeometry.Interfinity

open MeasureTheory Set Filter Topology

noncomputable section

variable {d : ℕ}

/-! ## Two chart witnesses -/

/-- The linear chart. -/
def ChartFun.linear : ChartFun where
  toFun := fun s => s
  continuousOn' := continuousOn_id
  exists_bound := ⟨1, zero_le_one, fun s hs => by
      rw [abs_of_nonneg hs.1]
      exact hs.2, fun s hs => by
      simp only [sub_zero, one_mul]
      exact le_of_eq (abs_of_nonneg hs.1)⟩

@[simp] theorem ChartFun.linear_toFun (s : ℝ) : ChartFun.linear.toFun s = s := rfl

theorem integral_rpow_Ioo_unit {a : ℝ} (ha : -1 < a) :
    (∫ s in Ioo (0 : ℝ) 1, s ^ a) = 1 / (a + 1) := by
  have hane : a + 1 ≠ 0 := by linarith
  rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le zero_le_one,
    integral_rpow (Or.inl ha), Real.one_rpow, Real.zero_rpow hane]
  ring

/-- The linear chart pairs nontrivially with every admissible finite part. -/
theorem finitePart_linear {a : ℝ} (ha : -1 < a) :
    finitePart 1 a ChartFun.linear = 1 / (a + 1) := by
  have hint : (∫ s in Ioo (0 : ℝ) 1, ChartFun.linear.toFun s * s ^ (a - 1)) = 1 / (a + 1) := by
    rw [← integral_rpow_Ioo_unit ha]
    refine setIntegral_congr_fun measurableSet_Ioo fun s hs => ?_
    show s * s ^ (a - 1) = s ^ a
    exact rpow_succ_split hs.1 a
  rcases lt_or_ge 0 a with hpos | hnonpos
  · rw [finitePart, if_pos hpos, hint, one_mul]
  · rw [finitePart, if_neg (not_lt.2 hnonpos)]
    have hsub : (∫ s in Ioo (0 : ℝ) 1,
        (ChartFun.linear.toFun s - ChartFun.linear.toFun 0) * s ^ (a - 1)) = 1 / (a + 1) := by
      rw [← hint]
      refine setIntegral_congr_fun measurableSet_Ioo fun s _ => ?_
      show (s - 0) * s ^ (a - 1) = s * s ^ (a - 1)
      ring
    rw [hsub]
    rcases eq_or_ne a 0 with rfl | hne
    · simp
    · rw [if_neg hne]
      show (1 : ℝ) * (1 / (a + 1) + 0 / a) = 1 / (a + 1)
      rw [zero_div, add_zero, one_mul]

theorem finitePart_linear_ne_zero {a : ℝ} (ha : -1 < a) :
    finitePart 1 a ChartFun.linear ≠ 0 := by
  rw [finitePart_linear ha]
  have : (0 : ℝ) < a + 1 := by linarith
  positivity

/-! ## Transport as a total operation -/

/-- Transport by a time clamped to the future. -/
def ChartFun.evolve (V : ℝ) (h : ChartFun) : ChartFun :=
  ChartFun.transport (max V 0) (le_max_right V 0) h

theorem finitePart_congr (c a : ℝ) {h h' : ChartFun} (hEq : h.toFun = h'.toFun) :
    finitePart c a h = finitePart c a h' := by
  rw [finitePart, finitePart, hEq]

theorem finitePart_evolve (c a : ℝ) {V : ℝ} (hV : 0 ≤ V) (h : ChartFun) :
    finitePart c a (ChartFun.evolve V h) = finitePart c a (ChartFun.transport V hV h) := by
  refine finitePart_congr c a ?_
  funext s
  show Real.exp (-(max V 0 * s)) * h.toFun s = Real.exp (-(V * s)) * h.toFun s
  rw [max_eq_left hV]

/-! ## The tensor finite part -/

/-- The tensor finite part on tensor charts. -/
def tensorFinitePart (c : ℝ) (a : Fin d → ℝ) (h : Fin d → ChartFun) : ℝ :=
  c * ∏ j, finitePart 1 (a j) (h j)

/-- The orbit of the tensor finite part under the times of a face. -/
def tensorFaceOrbit (c : ℝ) (a : Fin d → ℝ) (J : Finset (Fin d)) (V : Fin d → ℝ)
    (h : Fin d → ChartFun) : ℝ :=
  c * ∏ j, finitePart 1 (a j) (if j ∈ J then ChartFun.evolve (V j) (h j) else h j)

@[simp] theorem tensorFaceOrbit_empty (c : ℝ) (a : Fin d → ℝ) (V : Fin d → ℝ)
    (h : Fin d → ChartFun) : tensorFaceOrbit c a ∅ V h = tensorFinitePart c a h := by
  rw [tensorFaceOrbit, tensorFinitePart]
  congr 1

/-- **The cubical source cochain is an iterated finite-part coboundary.**  Applying the difference
of transport and identity in every coordinate returns the tensor source pairing. -/
theorem tensor_iterated_coboundary (c : ℝ) {a : Fin d → ℝ} (ha : ∀ j, -1 < a j) {V : Fin d → ℝ}
    (hV : ∀ j, 0 ≤ V j) (h : Fin d → ChartFun) :
    (c * ∏ j, (finitePart 1 (a j) (ChartFun.evolve (V j) (h j)) - finitePart 1 (a j) (h j))) =
      c * ∏ j, sourcePairing 1 (a j) (V j) (h j) := by
  congr 1
  refine Finset.prod_congr rfl fun j _ => ?_
  rw [finitePart_evolve 1 (a j) (hV j) (h j)]
  exact finitePart_transport_sub 1 (ha j) (hV j) (h j)

/-- The iterated difference expands as the alternating sum over the face lattice. -/
theorem tensor_iterated_difference_eq_alternating_sum (c : ℝ) (a : Fin d → ℝ) (V : Fin d → ℝ)
    (h : Fin d → ChartFun) :
    (c * ∏ j, (finitePart 1 (a j) (ChartFun.evolve (V j) (h j)) - finitePart 1 (a j) (h j))) =
      ∑ J ∈ (Finset.univ : Finset (Fin d)).powerset,
        (-1 : ℝ) ^ ((Finset.univ \ J).card) * tensorFaceOrbit c a J V h := by
  classical
  set x : Fin d → ℝ := fun j => finitePart 1 (a j) (ChartFun.evolve (V j) (h j)) with hx
  set y : Fin d → ℝ := fun j => finitePart 1 (a j) (h j) with hy
  have hexp : (∏ j, (x j - y j)) =
      ∑ J ∈ (Finset.univ : Finset (Fin d)).powerset,
        (∏ j ∈ J, x j) * ∏ j ∈ Finset.univ \ J, (-(y j)) := by
    have h1 : (∏ j, (x j + -(y j))) =
        ∑ J ∈ (Finset.univ : Finset (Fin d)).powerset,
          (∏ j ∈ J, x j) * ∏ j ∈ Finset.univ \ J, (-(y j)) := Finset.prod_add _ _ _
    simpa [sub_eq_add_neg] using h1
  have hfactor : ∀ J : Finset (Fin d),
      (∏ j, if j ∈ J then x j else y j) = (∏ j ∈ J, x j) * ∏ j ∈ Finset.univ \ J, y j := by
    intro J
    rw [Finset.prod_ite]
    congr 1
    · exact Finset.prod_congr (by ext j; simp) fun _ _ => rfl
    · exact Finset.prod_congr (by ext j; simp) fun _ _ => rfl
  have hneg : ∀ J : Finset (Fin d),
      (∏ j ∈ Finset.univ \ J, (-(y j))) =
        (-1 : ℝ) ^ ((Finset.univ \ J).card) * ∏ j ∈ Finset.univ \ J, y j := by
    intro J
    rw [Finset.prod_neg]
  rw [hexp, Finset.mul_sum]
  refine Finset.sum_congr rfl fun J _ => ?_
  rw [tensorFaceOrbit, hneg J]
  have hprod : (∏ j, finitePart 1 (a j) (if j ∈ J then ChartFun.evolve (V j) (h j) else h j)) =
      ∏ j, if j ∈ J then x j else y j := by
    refine Finset.prod_congr rfl fun j _ => ?_
    by_cases hj : j ∈ J <;> simp [hj, hx, hy]
  rw [hprod, hfactor J]
  ring

/-- The tensor source pairing is the cubical integral of the source cochain. -/
theorem tensor_sourcePairing_eq_cube (a V : Fin d → ℝ) (h : Fin d → ChartFun) :
    (∫ s, (∏ j, laplaceCochain (V j) (s j) * (h j).toFun (s j) * s j ^ (a j - 1))
        ∂(cubeMeasure d)) = ∏ j, sourcePairing 1 (a j) (V j) (h j) := by
  have hval := integral_fintype_prod_eq_prod (𝕜 := ℝ)
    (μ := fun _ : Fin d => volume.restrict (Ioo (0 : ℝ) 1))
    (fun j u => laplaceCochain (V j) u * (h j).toFun u * u ^ (a j - 1))
  rw [hval]
  exact Finset.prod_congr rfl fun j _ => by rw [sourcePairing, one_mul]

/-! ## Face stability -/

/-- The transported factor above the cut. -/
theorem tendsto_finitePart_evolve {a : ℝ} (ha : 0 < a) (h : ChartFun) :
    Tendsto (fun V : ℝ => finitePart 1 a (ChartFun.evolve V h)) atTop (𝓝 0) := by
  have hmain := tendsto_transported_finitePart 1 ha h
  refine hmain.congr' ?_
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with V hV
  rw [finitePart_evolve 1 a hV h, finitePart_transport_of_pos 1 ha hV h]

theorem tendsto_pi_diagonal :
    Tendsto (fun t : ℝ => (fun _ : Fin d => t)) atTop (Filter.pi fun _ : Fin d => atTop) := by
  refine tendsto_pi.2 fun _ => tendsto_id

/-- **Face stability above every cut.**  When every coordinate is above its own cut, every
nonempty face orbit tends to zero. -/
theorem tendsto_tensorFaceOrbit (c : ℝ) {a : Fin d → ℝ} (ha : ∀ j, 0 < a j)
    {J : Finset (Fin d)} (hJ : J.Nonempty) (h : Fin d → ChartFun) :
    Tendsto (fun V : Fin d → ℝ => tensorFaceOrbit c a J V h)
      (Filter.pi fun _ : Fin d => atTop) (𝓝 0) := by
  classical
  set L : Fin d → ℝ := fun j => if j ∈ J then 0 else finitePart 1 (a j) (h j) with hL
  have hfac : ∀ j : Fin d, Tendsto
      (fun V : Fin d → ℝ => finitePart 1 (a j) (if j ∈ J then ChartFun.evolve (V j) (h j)
        else h j)) (Filter.pi fun _ : Fin d => atTop) (𝓝 (L j)) := by
    intro j
    by_cases hj : j ∈ J
    · have hproj : Tendsto (fun V : Fin d → ℝ => V j) (Filter.pi fun _ : Fin d => atTop) atTop :=
        tendsto_eval_pi (fun _ : Fin d => (atTop : Filter ℝ)) j
      have := (tendsto_finitePart_evolve (ha j) (h j)).comp hproj
      simp only [hL, if_pos hj]
      simpa [Function.comp_def, if_pos hj] using this
    · simp only [hL, if_neg hj]
      exact tendsto_const_nhds
  have hprod : Tendsto (fun V : Fin d → ℝ =>
      ∏ j, finitePart 1 (a j) (if j ∈ J then ChartFun.evolve (V j) (h j) else h j))
      (Filter.pi fun _ : Fin d => atTop) (𝓝 (∏ j, L j)) :=
    tendsto_finsetProd _ fun j _ => hfac j
  obtain ⟨k, hk⟩ := hJ
  have hLzero : (∏ j, L j) = 0 :=
    Finset.prod_eq_zero (Finset.mem_univ k) (by simp [hL, if_pos hk])
  rw [hLzero] at hprod
  have := hprod.const_mul c
  simpa [tensorFaceOrbit] using this

/-- **No face stability below a cut.**  A single deficient coordinate makes its own singleton face
orbit diverge, for the tensor chart which is constant there and linear elsewhere. -/
theorem not_tendsto_tensorFaceOrbit {c : ℝ} (hc : c ≠ 0) {a : Fin d → ℝ} (ha : ∀ j, -1 < a j)
    {k : Fin d} (ha0 : a k ≤ 0) (L : ℝ) :
    ¬ Tendsto (fun V : Fin d → ℝ => tensorFaceOrbit c a {k} V
        (fun j => if j = k then ChartFun.const 1 else ChartFun.linear))
      (Filter.pi fun _ : Fin d => atTop) (𝓝 L) := by
  classical
  set h : Fin d → ChartFun := fun j => if j = k then ChartFun.const 1 else ChartFun.linear with hh
  set C : ℝ := ∏ j ∈ Finset.univ.erase k, finitePart 1 (a j) (h j) with hC
  have hCne : C ≠ 0 := by
    rw [hC]
    refine Finset.prod_ne_zero_iff.2 fun j hj => ?_
    have hjk : j ≠ k := (Finset.mem_erase.1 hj).1
    rw [hh]
    simp only [if_neg hjk]
    exact finitePart_linear_ne_zero (ha j)
  intro hcon
  have hdiag := hcon.comp (tendsto_pi_diagonal (d := d))
  have hrewrite : ∀ t : ℝ, 0 ≤ t →
      tensorFaceOrbit c a {k} (fun _ => t) h =
        (c * C) * (cutIntegral (a k) t + (if a k = 0 then 0 else 1 / a k)) := by
    intro t ht
    rw [tensorFaceOrbit, Finset.prod_eq_prod_sdiff_singleton_mul (Finset.mem_univ k)]
    have hother : ∀ j ∈ Finset.univ \ ({k} : Finset (Fin d)),
        finitePart 1 (a j) (if j ∈ ({k} : Finset (Fin d)) then ChartFun.evolve t (h j) else h j) =
          finitePart 1 (a j) (h j) := by
      intro j hj
      have hjk : j ∉ ({k} : Finset (Fin d)) := (Finset.mem_sdiff.1 hj).2
      rw [if_neg hjk]
    rw [Finset.prod_congr rfl hother]
    have hCeq : (∏ j ∈ Finset.univ \ ({k} : Finset (Fin d)), finitePart 1 (a j) (h j)) = C := by
      rw [hC]
      congr 1
      ext j
      simp [Finset.mem_sdiff, Finset.mem_erase, and_comm]
    rw [hCeq, if_pos (Finset.mem_singleton_self k)]
    have hhk : h k = ChartFun.const 1 := by rw [hh]; simp
    rw [hhk, finitePart_evolve 1 (a k) ht (ChartFun.const 1),
      finitePart_const_transport 1 ha0 ht]
    ring
  have hlim : Tendsto (fun t : ℝ =>
      (c * C) * (cutIntegral (a k) t + (if a k = 0 then 0 else 1 / a k))) atTop (𝓝 L) := by
    refine hdiag.congr' ?_
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
    show tensorFaceOrbit c a {k} (fun _ => t) h = _
    exact hrewrite t ht
  exact not_tendsto_finitePart_of_nonpos (mul_ne_zero hc hCne) (ha k) ha0 L hlim

/-- **The face-stable region is the open polyhedron.**  Face stability of every nonempty face is
equivalent to every coordinate lying above its own cut. -/
theorem tensorFaceStable_iff (c : ℝ) (hc : c ≠ 0) {a : Fin d → ℝ} (ha : ∀ j, -1 < a j) :
    (∀ (J : Finset (Fin d)), J.Nonempty → ∀ h : Fin d → ChartFun,
      Tendsto (fun V : Fin d → ℝ => tensorFaceOrbit c a J V h)
        (Filter.pi fun _ : Fin d => atTop) (𝓝 0)) ↔ ∀ j, 0 < a j := by
  constructor
  · intro hstable j
    by_contra hcon
    have ha0 : a j ≤ 0 := not_lt.1 hcon
    exact not_tendsto_tensorFaceOrbit hc ha ha0 0
      (hstable {j} ⟨j, Finset.mem_singleton_self j⟩ _)
  · intro hpos J hJ h
    exact tendsto_tensorFaceOrbit c hpos hJ h

end

end GaloisForLFunctions.HTGeometry.Interfinity
