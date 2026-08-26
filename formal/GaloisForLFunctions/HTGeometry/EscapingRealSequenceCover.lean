import GaloisForLFunctions.HTGeometry.PaddedSequenceOfDivisor
import GaloisForLFunctions.HTGeometry.AnalyticImageFinitenessComplex

/-!
# Enumerating a locally finite real set by an escaping injective sequence

Every subset of `ℝ` with finite intersection with each symmetric bounded interval embeds into an
injective sequence whose absolute values tend to infinity.  Finite sets are padded by a disjoint
arithmetic tail beyond all their points; infinite sets are enumerated through their countable
subtype.  This gives discrete real divisors the exact input shape required by the Herglotz
real-level regularizer.
-/

open Complex Filter Set Topology

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- A locally finite real set is covered by an injective sequence escaping in absolute value. -/
theorem exists_injective_escaping_real_sequence_cover
    {S : Set ℝ}
    (hlocal : ∀ R : ℝ, {x : S | |(x : ℝ)| ≤ R}.Finite) :
    ∃ atoms : ℕ → ℝ, Function.Injective atoms ∧
      Tendsto (fun n => |atoms n|) atTop atTop ∧ S ⊆ Set.range atoms := by
  classical
  have hcount : S.Countable := by
    exact Set.countable_coe_iff.mp <| countable_of_locallyFiniteNorm
      (p := fun x : S => ((x : ℝ) : ℂ)) (by
          intro R
          simpa [Complex.norm_real, Real.norm_eq_abs] using hlocal R)
  by_cases hfinite : S.Finite
  · letI : Fintype S := hfinite.fintype
    let e : Fin (Fintype.card S) ≃ S := (Fintype.equivFin S).symm
    let M : ℝ := (∑ x : S, |(x : ℝ)|) + 1
    let atoms : ℕ → ℝ := fun n =>
      if hn : n < Fintype.card S then (e ⟨n, hn⟩).1 else M + n
    have hMpos : 0 < M := by
      dsimp [M]
      positivity
    have hmember_lt_M (x : S) : |(x : ℝ)| < M := by
      have hxle : |(x : ℝ)| ≤ ∑ y : S, |(y : ℝ)| :=
        Finset.single_le_sum (s := Finset.univ) (f := fun y : S => |(y : ℝ)|)
          (fun y _ => abs_nonneg (y : ℝ)) (Finset.mem_univ x)
      dsimp [M]
      linarith
    have hinj : Function.Injective atoms := by
      intro n m hnm
      by_cases hn : n < Fintype.card S
      · by_cases hm : m < Fintype.card S
        · dsimp only [atoms] at hnm
          rw [dif_pos hn, dif_pos hm] at hnm
          exact congrArg Fin.val (e.injective (Subtype.ext hnm))
        · have hhead : |(e ⟨n, hn⟩).1| < M := hmember_lt_M _
          have htail : M ≤ M + (m : ℝ) :=
            le_add_of_nonneg_right (Nat.cast_nonneg m)
          have heq : (e ⟨n, hn⟩).1 = M + (m : ℝ) := by
            dsimp only [atoms] at hnm
            rw [dif_pos hn, dif_neg hm] at hnm
            exact hnm
          rw [heq, abs_of_nonneg (hMpos.le.trans htail)] at hhead
          linarith
      · by_cases hm : m < Fintype.card S
        · have hhead : |(e ⟨m, hm⟩).1| < M := hmember_lt_M _
          have htail : M ≤ M + (n : ℝ) :=
            le_add_of_nonneg_right (Nat.cast_nonneg n)
          have heq : M + (n : ℝ) = (e ⟨m, hm⟩).1 := by
            dsimp only [atoms] at hnm
            rw [dif_neg hn, dif_pos hm] at hnm
            exact hnm
          rw [← heq, abs_of_nonneg (hMpos.le.trans htail)] at hhead
          linarith
        · have heq : M + (n : ℝ) = M + (m : ℝ) := by
            dsimp only [atoms] at hnm
            rw [dif_neg hn, dif_neg hm] at hnm
            exact hnm
          exact_mod_cast (add_left_cancel heq)
    refine ⟨atoms, hinj, ?_, ?_⟩
    · rw [Filter.tendsto_atTop_atTop]
      intro R
      obtain ⟨N, hN⟩ := exists_nat_ge R
      refine ⟨max (Fintype.card S) N, fun n hn => ?_⟩
      have hncard : ¬ n < Fintype.card S := by omega
      have hnN : N ≤ n := le_trans (le_max_right _ _) hn
      have hnonneg : 0 ≤ M + (n : ℝ) := by positivity
      dsimp only [atoms]
      rw [dif_neg hncard, abs_of_nonneg hnonneg]
      exact hN.trans ((Nat.cast_le.mpr hnN).trans
        (le_add_of_nonneg_left hMpos.le))
    · intro x hx
      let xs : S := ⟨x, hx⟩
      let j : Fin (Fintype.card S) := e.symm xs
      refine ⟨j.val, ?_⟩
      have hj : j.val < Fintype.card S := j.isLt
      dsimp only [atoms]
      rw [dif_pos hj]
      change (e j).1 = x
      simp [j, xs]
  · have hinfinite : S.Infinite := hfinite
    letI : Encodable S := hcount.toEncodable
    letI : Infinite S := Set.infinite_coe_iff.mpr hinfinite
    letI : Denumerable S := Denumerable.ofEncodableOfInfinite S
    let e : ℕ ≃ S := (Denumerable.eqv S).symm
    let atoms : ℕ → ℝ := fun n => (e n).1
    have hinj : Function.Injective atoms := by
      intro n m h
      exact e.injective (Subtype.ext h)
    refine ⟨atoms, hinj, ?_, ?_⟩
    · rw [Filter.tendsto_atTop_atTop]
      intro R
      have hF : {n : ℕ | |atoms n| ≤ R}.Finite := by
        simpa [atoms] using
          (hlocal R).preimage (Set.injOn_of_injective e.injective)
      have hev := hF.eventually_cofinite_notMem
      rw [Nat.cofinite_eq_atTop, Filter.eventually_atTop] at hev
      obtain ⟨N, hN⟩ := hev
      exact ⟨N, fun n hn => (lt_of_not_ge (hN n hn)).le⟩
    · intro x hx
      let xs : S := ⟨x, hx⟩
      refine ⟨e.symm xs, ?_⟩
      simp [atoms, xs]

/-- Restriction of a complex analytic germ to the real line is real analytic. -/
theorem analyticAt_comp_ofReal {F : ℂ → ℂ} {x : ℝ}
    (hF : AnalyticAt ℂ F (x : ℂ)) :
    AnalyticAt ℝ (fun t : ℝ => F (t : ℂ)) x := by
  exact AnalyticAt.comp (x := x) (g := F) (f := fun t : ℝ => ((t : ℂ)))
    hF.restrictScalars (Complex.ofRealCLM.analyticAt x)

/-- Real zeros of a complex function analytic through the whole real axis are locally finite,
provided one real value is nonzero. -/
theorem finite_realZeros_bounded_of_analyticAt_ofReal
    {F : ℂ → ℂ} (hF : ∀ x : ℝ, AnalyticAt ℂ F (x : ℂ))
    {x₀ : ℝ} (hF₀ : F (x₀ : ℂ) ≠ 0) (R : ℝ) :
    {x : {x : ℝ // F (x : ℂ) = 0} | |(x : ℝ)| ≤ R}.Finite := by
  let f : ℝ → ℂ := fun x => F (x : ℂ)
  have hf : AnalyticOnNhd ℝ f Set.univ := fun x _ => analyticAt_comp_ofReal (hF x)
  have hfin : (Set.Icc (-|R|) |R| ∩ f ⁻¹' {0}).Finite :=
    finite_zeros_of_analyticOnNhd_complex isPreconnected_univ hf
      (Set.mem_univ x₀) hF₀ isCompact_Icc (Set.subset_univ _)
  have hpre : ((fun x : {x : ℝ // F (x : ℂ) = 0} => (x : ℝ)) ⁻¹'
      (Set.Icc (-|R|) |R| ∩ f ⁻¹' {0})).Finite :=
    hfin.preimage (Set.injOn_of_injective Subtype.val_injective)
  apply hpre.subset
  intro x hx
  refine ⟨?_, ?_⟩
  · exact abs_le.mp (le_trans hx (le_abs_self R))
  · exact x.property

/-- The real zero divisor of a nontrivial function analytic through the real axis is covered by an
injective escaping sequence. -/
theorem exists_injective_escaping_realZero_sequence
    {F : ℂ → ℂ} (hF : ∀ x : ℝ, AnalyticAt ℂ F (x : ℂ))
    {x₀ : ℝ} (hF₀ : F (x₀ : ℂ) ≠ 0) :
    ∃ atoms : ℕ → ℝ, Function.Injective atoms ∧
      Tendsto (fun n => |atoms n|) atTop atTop ∧
        {x : ℝ | F (x : ℂ) = 0} ⊆ Set.range atoms := by
  let Z : Set ℝ := {x | F (x : ℂ) = 0}
  obtain ⟨atoms, hinj, hescape, hcover⟩ :=
    exists_injective_escaping_real_sequence_cover
      (S := Z) (finite_realZeros_bounded_of_analyticAt_ofReal hF hF₀)
  exact ⟨atoms, hinj, hescape, hcover⟩

end

end GaloisForLFunctions.HTGeometry
