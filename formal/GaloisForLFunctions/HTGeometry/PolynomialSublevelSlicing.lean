import GaloisForLFunctions.HTGeometry.PolynomialLineSlice

/-!
# Slicing a multivariate sublevel set

Choosing a direction where the top homogeneous form does not vanish turns the restriction of a
polynomial to every line in that direction into a one-variable polynomial of the full degree with
one and the same leading coefficient.  Fubini in the sheared coordinates then bounds the measure of
a sublevel set by the transverse measure times the one-variable bound.

The shear itself only costs the first coordinate of the direction: the parametrisation
`(x', t) ↦ (0, x') + t v` pushes the product measure to `|v₀|` times Lebesgue measure, because it is
a translation in the transverse coordinates followed by a dilation in the line parameter.
-/

open MeasureTheory Set
open scoped ENNReal

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {m : ℕ}



theorem exists_support_degree_eq (p : MvPolynomial (Fin m) ℝ) (hp : p ≠ 0) :
    ∃ u ∈ p.support, Finsupp.degree u = p.totalDegree := by
  have hne : p.support.Nonempty := MvPolynomial.support_nonempty.mpr hp
  obtain ⟨u, hu, heq⟩ := Finset.exists_mem_eq_sup p.support hne (fun s => s.sum fun _ e => e)
  refine ⟨u, hu, ?_⟩
  rw [MvPolynomial.totalDegree, heq]
  rfl

private theorem homogeneousComponent_totalDegree_ne_zero (p : MvPolynomial (Fin m) ℝ) (hp : p ≠ 0) :
    MvPolynomial.homogeneousComponent p.totalDegree p ≠ 0 := by
  obtain ⟨u, hu, hdeg⟩ := exists_support_degree_eq p hp
  intro h
  have hcoeff : MvPolynomial.coeff u p ≠ 0 := MvPolynomial.mem_support_iff.mp hu
  refine hcoeff ?_
  have hco := MvPolynomial.coeff_homogeneousComponent p.totalDegree p u
  rw [h, MvPolynomial.coeff_zero, if_pos hdeg] at hco
  exact hco.symm

theorem exists_direction (p : MvPolynomial (Fin (m + 1)) ℝ) (hp : p ≠ 0) :
    ∃ v : Fin (m + 1) → ℝ, v 0 ≠ 0 ∧
      MvPolynomial.eval v (MvPolynomial.homogeneousComponent p.totalDegree p) ≠ 0 := by
  classical
  set H := MvPolynomial.homogeneousComponent p.totalDegree p with hH
  have hHne : H ≠ 0 := homogeneousComponent_totalDegree_ne_zero p hp
  have hQ : H * MvPolynomial.X 0 ≠ 0 := mul_ne_zero hHne (MvPolynomial.X_ne_zero _)
  obtain ⟨v, hv⟩ : ∃ v : Fin (m + 1) → ℝ, MvPolynomial.eval v (H * MvPolynomial.X 0) ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hQ (MvPolynomial.funext fun v => by rw [hcon v, map_zero])
  rw [map_mul, MvPolynomial.eval_X] at hv
  exact ⟨v, right_ne_zero_of_mul hv, left_ne_zero_of_mul hv⟩

theorem natDegree_lineSlice_le {d : ℕ} (p : MvPolynomial (Fin m) ℝ) (hp : p.totalDegree ≤ d)
    (v x : Fin m → ℝ) : (lineSlice p v x).natDegree ≤ d := by
  classical
  have hsum : lineSlice p v x
      = ∑ u ∈ p.support, lineSlice (MvPolynomial.monomial u (MvPolynomial.coeff u p)) v x := by
    conv_lhs => rw [lineSlice, ← MvPolynomial.support_sum_monomial_coeff p]
    rw [map_sum]
    rfl
  rw [hsum]
  refine Polynomial.natDegree_sum_le_of_forall_le _ _ fun u hu => ?_
  refine le_trans (natDegree_lineSlice_monomial_le u _ v x) ?_
  have := MvPolynomial.le_totalDegree hu
  rw [degree_eq_sum]
  exact le_trans this hp

theorem natDegree_lineSlice_eq {d : ℕ} (p : MvPolynomial (Fin m) ℝ) (hp : p.totalDegree ≤ d)
    (v x : Fin m → ℝ)
    (hc : MvPolynomial.eval v (MvPolynomial.homogeneousComponent d p) ≠ 0) :
    (lineSlice p v x).natDegree = d :=
  Polynomial.natDegree_eq_of_le_of_coeff_ne_zero (natDegree_lineSlice_le p hp v x)
    (by rw [coeff_lineSlice p hp v x]; exact hc)

theorem leadingCoeff_lineSlice {d : ℕ} (p : MvPolynomial (Fin m) ℝ) (hp : p.totalDegree ≤ d)
    (v x : Fin m → ℝ)
    (hc : MvPolynomial.eval v (MvPolynomial.homogeneousComponent d p) ≠ 0) :
    (lineSlice p v x).leadingCoeff = MvPolynomial.eval v (MvPolynomial.homogeneousComponent d p) := by
  rw [Polynomial.leadingCoeff, natDegree_lineSlice_eq p hp v x hc, coeff_lineSlice p hp v x]

theorem lineSlice_ne_zero {d : ℕ} (p : MvPolynomial (Fin m) ℝ) (hp : p.totalDegree ≤ d)
    (v x : Fin m → ℝ)
    (hc : MvPolynomial.eval v (MvPolynomial.homogeneousComponent d p) ≠ 0) :
    lineSlice p v x ≠ 0 := by
  intro h
  apply hc
  rw [← coeff_lineSlice p hp v x, h, Polynomial.coeff_zero]

open MeasureTheory in
/-- **The sliced sublevel bound.**  Along every line in a direction where the top form does not
vanish, the polynomial is a one-variable polynomial of the full degree with the same leading
coefficient, so its sublevel set on each line is short and the total measure of the sheared sublevel
set is at most the transverse measure times that length. -/
theorem volume_prod_sublevel_le {d k : ℕ} (hd : 0 < d) (p : MvPolynomial (Fin m) ℝ)
    (hp : p.totalDegree ≤ d) (v : Fin m → ℝ)
    (hc : MvPolynomial.eval v (MvPolynomial.homogeneousComponent d p) ≠ 0)
    {ε : ℝ} (hε : 0 ≤ ε) (b : (Fin k → ℝ) → (Fin m → ℝ)) (hb : Continuous b)
    (S : Set (Fin k → ℝ)) (hS : MeasurableSet S) :
    (volume : Measure ((Fin k → ℝ) × ℝ))
        {q | q.1 ∈ S ∧ |MvPolynomial.eval (fun i => b q.1 i + q.2 * v i) p| ≤ ε}
      ≤ volume S * ENNReal.ofReal (2 * d *
          (ε / |MvPolynomial.eval v (MvPolynomial.homogeneousComponent d p)|) ^ ((1 : ℝ) / d)) := by
  classical
  set c := MvPolynomial.eval v (MvPolynomial.homogeneousComponent d p) with hcdef
  set B : ℝ := 2 * d * (ε / |c|) ^ ((1 : ℝ) / d) with hB
  have hcont : Continuous fun q : (Fin k → ℝ) × ℝ =>
      MvPolynomial.eval (fun i => b q.1 i + q.2 * v i) p := by
    refine (MvPolynomial.continuous_eval p).comp ?_
    refine continuous_pi fun i => ?_
    exact (((continuous_apply i).comp hb).comp continuous_fst).add
      (continuous_snd.mul continuous_const)
  have hmeas : MeasurableSet {q : (Fin k → ℝ) × ℝ |
      q.1 ∈ S ∧ |MvPolynomial.eval (fun i => b q.1 i + q.2 * v i) p| ≤ ε} := by
    refine MeasurableSet.inter ?_ ?_
    · exact hS.preimage measurable_fst
    · exact measurableSet_le (hcont.abs.measurable) measurable_const
  rw [Measure.volume_eq_prod, Measure.prod_apply hmeas]
  have hslice : ∀ x' : Fin k → ℝ,
      volume (Prod.mk x' ⁻¹' {q : (Fin k → ℝ) × ℝ |
          q.1 ∈ S ∧ |MvPolynomial.eval (fun i => b q.1 i + q.2 * v i) p| ≤ ε})
        ≤ S.indicator (fun _ => ENNReal.ofReal B) x' := by
    intro x'
    by_cases hx : x' ∈ S
    · rw [Set.indicator_of_mem hx]
      have hpre : (Prod.mk x' ⁻¹' {q : (Fin k → ℝ) × ℝ |
          q.1 ∈ S ∧ |MvPolynomial.eval (fun i => b q.1 i + q.2 * v i) p| ≤ ε})
          = {t : ℝ | |(lineSlice p v (b x')).eval t| ≤ ε} := by
        ext t
        simp only [Set.mem_preimage, Set.mem_setOf_eq, hx, true_and, lineSlice_eval]
      rw [hpre]
      have hne : lineSlice p v (b x') ≠ 0 := lineSlice_ne_zero p hp v (b x') hc
      have hdeg : (lineSlice p v (b x')).natDegree = d := natDegree_lineSlice_eq p hp v (b x') hc
      have hlead : (lineSlice p v (b x')).leadingCoeff = c :=
        leadingCoeff_lineSlice p hp v (b x') hc
      have := volume_polynomial_sublevel_le (lineSlice p v (b x')) hne (by rw [hdeg]; exact hd) hε
      rw [hdeg, hlead] at this
      exact this
    · rw [Set.indicator_of_notMem hx]
      have hpre : (Prod.mk x' ⁻¹' {q : (Fin k → ℝ) × ℝ |
          q.1 ∈ S ∧ |MvPolynomial.eval (fun i => b q.1 i + q.2 * v i) p| ≤ ε}) = ∅ := by
        ext t
        simp [hx]
      rw [hpre, measure_empty]
  calc (∫⁻ x', volume (Prod.mk x' ⁻¹' {q : (Fin k → ℝ) × ℝ |
        q.1 ∈ S ∧ |MvPolynomial.eval (fun i => b q.1 i + q.2 * v i) p| ≤ ε}))
      ≤ ∫⁻ x', S.indicator (fun _ => ENNReal.ofReal B) x' := lintegral_mono hslice
    _ = ENNReal.ofReal B * volume S := by
        rw [lintegral_indicator_const hS]
    _ = volume S * ENNReal.ofReal B := by rw [mul_comm]



theorem cons_eq_psi (v : Fin (m + 1) → ℝ) (q : (Fin m → ℝ) × ℝ) :
    Fin.cons 0 q.1 + q.2 • v = Fin.cons (q.2 * v 0) (q.1 + q.2 • Fin.tail v) := by
  funext i
  refine Fin.cases ?_ ?_ i
  · simp
  · intro j
    simp [Fin.tail, Pi.add_apply]

theorem psi_measurePreserving :
    MeasurePreserving (fun q : ℝ × (Fin m → ℝ) => Fin.cons q.1 q.2)
      (volume : Measure (ℝ × (Fin m → ℝ))) (volume : Measure (Fin (m + 1) → ℝ)) := by
  have h := (volume_preserving_piFinSuccAbove (fun _ : Fin (m + 1) => ℝ) 0).symm
    (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (m + 1) => ℝ) 0)
  have hfun : (fun q : ℝ × (Fin m → ℝ) => Fin.cons q.1 q.2)
      = ⇑(MeasurableEquiv.piFinSuccAbove (fun _ : Fin (m + 1) => ℝ) 0).symm := by
    funext q
    simp [MeasurableEquiv.piFinSuccAbove, Fin.consEquiv]
  rw [hfun]
  exact h

theorem volume_shear_preimage (v : Fin (m + 1) → ℝ) (hv : v 0 ≠ 0)
    (A : Set (Fin (m + 1) → ℝ)) (hA : MeasurableSet A) :
    (volume : Measure ((Fin m → ℝ) × ℝ)) {q | Fin.cons 0 q.1 + q.2 • v ∈ A}
      = ENNReal.ofReal |(v 0)⁻¹| * volume A := by
  classical
  set Ψ : ℝ × (Fin m → ℝ) → (Fin (m + 1) → ℝ) := fun q => Fin.cons q.1 q.2 with hΨ
  have hΨmp : MeasurePreserving Ψ volume volume := psi_measurePreserving
  have hΨmeas : Measurable Ψ := hΨmp.measurable
  set B : Set (ℝ × (Fin m → ℝ)) := Ψ ⁻¹' A with hB
  have hBmeas : MeasurableSet B := hA.preimage hΨmeas
  have hBvol : volume B = volume A := hΨmp.measure_preimage hA.nullMeasurableSet
  have hset : {q : (Fin m → ℝ) × ℝ | Fin.cons 0 q.1 + q.2 • v ∈ A}
      = {q : (Fin m → ℝ) × ℝ | (q.2 * v 0, q.1 + q.2 • Fin.tail v) ∈ B} := by
    ext q
    simp only [Set.mem_setOf_eq, hB, Set.mem_preimage, hΨ]
    rw [cons_eq_psi v q]
  have hmeas : MeasurableSet {q : (Fin m → ℝ) × ℝ |
      (q.2 * v 0, q.1 + q.2 • Fin.tail v) ∈ B} := by
    refine hBmeas.preimage ?_
    refine Measurable.prodMk ?_ ?_
    · exact measurable_snd.mul_const _
    · exact measurable_fst.add (measurable_snd.smul_const _)
  rw [hset, Measure.volume_eq_prod, Measure.prod_apply_symm hmeas]
  have hslice : ∀ t : ℝ,
      (volume : Measure (Fin m → ℝ)) ((fun x' => (x', t)) ⁻¹' {q : (Fin m → ℝ) × ℝ |
          (q.2 * v 0, q.1 + q.2 • Fin.tail v) ∈ B})
        = volume (Prod.mk (t * v 0) ⁻¹' B) := by
    intro t
    have hpre : ((fun x' => (x', t)) ⁻¹' {q : (Fin m → ℝ) × ℝ |
        (q.2 * v 0, q.1 + q.2 • Fin.tail v) ∈ B})
        = (fun x' : Fin m → ℝ => x' + t • Fin.tail v) ⁻¹' (Prod.mk (t * v 0) ⁻¹' B) := by
      ext x'
      simp [Set.mem_preimage]
    rw [hpre, measure_preimage_add_right]
  simp_rw [hslice]
  set g : ℝ → ℝ≥0∞ := fun s => volume (Prod.mk s ⁻¹' B) with hg
  have hgmeas : Measurable g := measurable_measure_prodMk_left hBmeas
  have hmul : ∫⁻ t : ℝ, g (t * v 0) = ∫⁻ t : ℝ, g (v 0 * t) := by
    refine lintegral_congr fun t => ?_
    rw [mul_comm]
  rw [hmul, ← lintegral_map hgmeas (measurable_const_mul (v 0)), Real.map_volume_mul_left hv,
    lintegral_smul_measure]
  rw [show (∫⁻ s : ℝ, g s) = volume B from (Measure.prod_apply hBmeas).symm, hBvol, smul_eq_mul]

end

end GaloisForLFunctions.HTGeometry
