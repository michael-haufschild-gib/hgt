import GaloisForLFunctions.HTGeometry.CofiniteTailGramPolarization

open Filter Topology Set
open scoped BigOperators

namespace GaloisForLFunctions.HTGeometry

noncomputable section

def sourceMarkedGibbsWeight {P : Type*}
    (base energy : P → ℝ) (k : ℕ) (p : P) : ℝ :=
  base p * Real.exp ((k : ℝ) * energy p)

def sourceMarkedGibbsPartition {P : Type*}
    (base energy : P → ℝ) (k : ℕ) : ℝ :=
  ∑' p, sourceMarkedGibbsWeight base energy k p

theorem summable_sourceMarkedGibbsWeight
    {P : Type*} (base energy : P → ℝ) (radius : ℝ) (k : ℕ)
    (hbase : ∀ p, 0 ≤ base p) (hsum : Summable base)
    (hupper : ∀ p, energy p ≤ radius) :
    Summable (sourceMarkedGibbsWeight base energy k) := by
  refine Summable.of_nonneg_of_le
    (f := fun p => base p * Real.exp ((k : ℝ) * radius)) ?_ ?_ ?_
  · intro p
    exact mul_nonneg (hbase p) (Real.exp_pos _).le
  · intro p
    apply mul_le_mul_of_nonneg_left _ (hbase p)
    apply Real.exp_le_exp.mpr
    exact mul_le_mul_of_nonneg_left (hupper p) (Nat.cast_nonneg k)
  · simpa only [sourceMarkedGibbsWeight] using
      hsum.mul_right (Real.exp ((k : ℝ) * radius))

theorem sourceMarkedGibbsPartition_le_mass_mul_exp
    {P : Type*} (base energy : P → ℝ) (radius : ℝ) (k : ℕ)
    (hbase : ∀ p, 0 ≤ base p) (hsum : Summable base)
    (hupper : ∀ p, energy p ≤ radius) :
    sourceMarkedGibbsPartition base energy k ≤
      (∑' p, base p) * Real.exp ((k : ℝ) * radius) := by
  unfold sourceMarkedGibbsPartition
  calc
    (∑' p, sourceMarkedGibbsWeight base energy k p) ≤
        ∑' p, base p * Real.exp ((k : ℝ) * radius) :=
      (summable_sourceMarkedGibbsWeight base energy radius k hbase hsum hupper).tsum_le_tsum
        (fun p => by
          apply mul_le_mul_of_nonneg_left _ (hbase p)
          apply Real.exp_le_exp.mpr
          exact mul_le_mul_of_nonneg_left (hupper p) (Nat.cast_nonneg k))
        (hsum.mul_right _)
    _ = (∑' p, base p) * Real.exp ((k : ℝ) * radius) := tsum_mul_right

theorem sourceMarkedGibbsPartition_pos
    {P : Type*} [Nonempty P] (base energy : P → ℝ) (radius : ℝ) (k : ℕ)
    (hbase : ∀ p, 0 < base p) (hsum : Summable base)
    (hupper : ∀ p, energy p ≤ radius) :
    0 < sourceMarkedGibbsPartition base energy k := by
  let p : P := Classical.choice inferInstance
  have hterm : 0 < sourceMarkedGibbsWeight base energy k p :=
    mul_pos (hbase p) (Real.exp_pos _)
  have hle := (summable_sourceMarkedGibbsWeight base energy radius k
    (fun q => (hbase q).le) hsum hupper).le_tsum p
    (fun q _ => mul_nonneg (hbase q).le (Real.exp_pos _).le)
  exact hterm.trans_le hle

theorem tendsto_sourceMarkedGibbsPartition_log_div_cold
    {P : Type*} [Nonempty P]
    (base energy : P → ℝ) (radius : ℝ)
    (hbase : ∀ p, 0 < base p) (hsum : Summable base)
    (hupper : ∀ p, energy p ≤ radius)
    (happroach : ∀ a : ℝ, a < radius → ∃ p, a < energy p) :
    Tendsto
      (fun k : ℕ => Real.log (sourceMarkedGibbsPartition base energy k) / (k : ℝ))
      atTop (nhds radius) := by
  have hmassPos : 0 < ∑' p, base p := by
    let p : P := Classical.choice inferInstance
    exact hsum.tsum_pos (fun q => (hbase q).le) p (hbase p)
  rw [tendsto_order]
  constructor
  · intro a ha
    obtain ⟨p, hpa⟩ := happroach a ha
    let w : ℝ := base p
    let d : ℝ := energy p
    have hw : 0 < w := by simpa only [w] using hbase p
    have hfixed : Tendsto (fun k : ℕ => Real.log w / (k : ℝ)) atTop (nhds 0) :=
      tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
    have hsmall : ∀ᶠ k : ℕ in atTop,
        a < d + Real.log w / (k : ℝ) := by
      have hgap : a - d < 0 := by simpa only [d] using sub_neg.mpr hpa
      filter_upwards [(tendsto_order.1 hfixed).1 (a - d) hgap] with k hk
      linarith
    have hkOne : ∀ᶠ k : ℕ in atTop, 1 ≤ k := eventually_ge_atTop 1
    filter_upwards [hsmall, hkOne] with k hk hk1
    have htermle : w * Real.exp ((k : ℝ) * d) ≤
        sourceMarkedGibbsPartition base energy k := by
      have hle := (summable_sourceMarkedGibbsWeight base energy radius k
        (fun q => (hbase q).le) hsum hupper).le_tsum p
        (fun q _ => mul_nonneg (hbase q).le (Real.exp_pos _).le)
      simpa only [sourceMarkedGibbsPartition, sourceMarkedGibbsWeight, w, d] using hle
    have htermPos : 0 < w * Real.exp ((k : ℝ) * d) :=
      mul_pos hw (Real.exp_pos _)
    have hlogle := Real.log_le_log htermPos htermle
    have hkpos : 0 < (k : ℝ) := by exact_mod_cast hk1
    have hnormalized :
        d + Real.log w / (k : ℝ) ≤
          Real.log (sourceMarkedGibbsPartition base energy k) / (k : ℝ) := by
      rw [Real.log_mul hw.ne' (Real.exp_ne_zero _), Real.log_exp] at hlogle
      rw [le_div_iff₀ hkpos]
      calc
        (d + Real.log w / (k : ℝ)) * (k : ℝ) =
            Real.log w + (k : ℝ) * d := by field_simp; ring
        _ ≤ Real.log (sourceMarkedGibbsPartition base energy k) := hlogle
    exact hk.trans_le hnormalized
  · intro b hb
    have hfixed : Tendsto
        (fun k : ℕ => Real.log (∑' p, base p) / (k : ℝ))
        atTop (nhds 0) :=
      tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
    have hsmall : ∀ᶠ k : ℕ in atTop,
        Real.log (∑' p, base p) / (k : ℝ) < b - radius :=
      (tendsto_order.1 hfixed).2 _ (sub_pos.mpr hb)
    have hkOne : ∀ᶠ k : ℕ in atTop, 1 ≤ k := eventually_ge_atTop 1
    filter_upwards [hsmall, hkOne] with k hk hk1
    have hZpos : 0 < sourceMarkedGibbsPartition base energy k :=
      sourceMarkedGibbsPartition_pos base energy radius k hbase hsum hupper
    have hZupper := sourceMarkedGibbsPartition_le_mass_mul_exp
      base energy radius k (fun p => (hbase p).le) hsum hupper
    have hlogle := Real.log_le_log hZpos hZupper
    have hkpos : 0 < (k : ℝ) := by exact_mod_cast hk1
    have hnormalized :
        Real.log (sourceMarkedGibbsPartition base energy k) / (k : ℝ) ≤
          radius + Real.log (∑' p, base p) / (k : ℝ) := by
      rw [Real.log_mul hmassPos.ne' (Real.exp_ne_zero _), Real.log_exp] at hlogle
      rw [div_le_iff₀ hkpos]
      calc
        Real.log (sourceMarkedGibbsPartition base energy k) ≤
            Real.log (∑' p, base p) + (k : ℝ) * radius := hlogle
        _ = (radius + Real.log (∑' p, base p) / (k : ℝ)) * (k : ℝ) := by
          field_simp
          ring
    exact hnormalized.trans_lt (by linarith)

/-- Unit-phase coefficient packets remain square-summable against every summable nonnegative
coordinate metric. -/
theorem summable_cofiniteWeightedGramTerm_of_phase
    {J P : Type*} [Fintype J] [DecidableEq P]
    (c : J → P → ℂ) (weight : P → ℝ) (F : Finset P) (q : J → ℂ)
    (hphase : ∀ j p, ‖c j p‖ = 1)
    (hweight : ∀ p, 0 ≤ weight p) (hwsum : Summable weight) :
    Summable fun p => if p ∈ F then 0
      else weight p * ‖∑ j, q j * c j p‖ ^ (2 : ℕ) := by
  let Q : ℝ := ∑ j, ‖q j‖
  let g : P → ℝ := fun p => if p ∈ F then 0
    else weight p * ‖∑ j, q j * c j p‖ ^ (2 : ℕ)
  have hdom : Summable fun p => weight p * Q ^ (2 : ℕ) :=
    hwsum.mul_right (Q ^ (2 : ℕ))
  change Summable g
  refine Summable.of_nonneg_of_le (f := fun p => weight p * Q ^ (2 : ℕ)) (g := g) ?_ ?_ hdom
  · intro p
    by_cases hpF : p ∈ F
    · simp [g, hpF]
    · simpa only [g, hpF, ↓reduceIte] using
        mul_nonneg (hweight p) (sq_nonneg ‖∑ j, q j * c j p‖)
  · intro p
    by_cases hpF : p ∈ F
    · simp only [g, hpF, ↓reduceIte]
      exact mul_nonneg (hweight p) (sq_nonneg Q)
    · simp only [g, hpF, ↓reduceIte]
      apply mul_le_mul_of_nonneg_left _ (hweight p)
      have hnorm : ‖∑ j, q j * c j p‖ ≤ Q := by
        calc
          ‖∑ j, q j * c j p‖ ≤ ∑ j, ‖q j * c j p‖ := norm_sum_le _ _
          _ = ∑ j, ‖q j‖ := by
            apply Finset.sum_congr rfl
            intro j _
            rw [norm_mul, hphase, mul_one]
          _ = Q := rfl
      have hQ : 0 ≤ Q := Finset.sum_nonneg fun _ _ => norm_nonneg _
      nlinarith [norm_nonneg (∑ j, q j * c j p)]

/-- Every source-marked positive Gibbs temperature induces the same cofinite Gram radical whenever
the two weighted energies converge.  No phase or differential-independence hypothesis is needed. -/
theorem cofiniteWeightedGramEnergy_sourceMarkedGibbs_zero_iff_change_temperature
    {J P : Type*} [Fintype J] [DecidableEq P]
    (c : J → P → ℂ) (base energy : P → ℝ) (radius : ℝ)
    (hbase : ∀ p, 0 < base p) (_hsum : Summable base)
    (_hupper : ∀ p, energy p ≤ radius)
    (k l : ℕ) (F : Finset P) (q : J → ℂ)
    (hsummablek : Summable fun p => if p ∈ F then 0 else
      sourceMarkedGibbsWeight base energy k p * ‖∑ j, q j * c j p‖ ^ (2 : ℕ))
    (hsummablel : Summable fun p => if p ∈ F then 0 else
      sourceMarkedGibbsWeight base energy l p * ‖∑ j, q j * c j p‖ ^ (2 : ℕ)) :
    cofiniteWeightedGramEnergy c (sourceMarkedGibbsWeight base energy k) F q = 0 ↔
      cofiniteWeightedGramEnergy c (sourceMarkedGibbsWeight base energy l) F q = 0 := by
  apply cofiniteWeightedGramEnergy_zero_iff_change_weight
  · intro p
    exact mul_pos (hbase p) (Real.exp_pos _)
  · intro p
    exact mul_pos (hbase p) (Real.exp_pos _)
  · exact hsummablek
  · exact hsummablel

/-- Unit-phase coefficient packets automatically satisfy the convergence condition in the
temperature-invariance theorem. -/
theorem cofiniteWeightedGramEnergy_sourceMarkedGibbs_zero_iff_change_temperature_of_phase
    {J P : Type*} [Fintype J] [DecidableEq P]
    (c : J → P → ℂ) (base energy : P → ℝ) (radius : ℝ)
    (hphase : ∀ j p, ‖c j p‖ = 1)
    (hbase : ∀ p, 0 < base p) (hsum : Summable base)
    (hupper : ∀ p, energy p ≤ radius)
    (k l : ℕ) (F : Finset P) (q : J → ℂ) :
    cofiniteWeightedGramEnergy c (sourceMarkedGibbsWeight base energy k) F q = 0 ↔
      cofiniteWeightedGramEnergy c (sourceMarkedGibbsWeight base energy l) F q = 0 := by
  apply cofiniteWeightedGramEnergy_sourceMarkedGibbs_zero_iff_change_temperature
    c base energy radius hbase hsum hupper k l F q
  · apply summable_cofiniteWeightedGramTerm_of_phase c _ F q hphase
    · intro p
      exact mul_nonneg (hbase p).le (Real.exp_pos _).le
    · exact summable_sourceMarkedGibbsWeight base energy radius k
        (fun p => (hbase p).le) hsum hupper
  · apply summable_cofiniteWeightedGramTerm_of_phase c _ F q hphase
    · intro p
      exact mul_nonneg (hbase p).le (Real.exp_pos _).le
    · exact summable_sourceMarkedGibbsWeight base energy radius l
        (fun p => (hbase p).le) hsum hupper

/-- Tail independence is equivalent to strict positivity at every temperature, and already to
strict positivity at one temperature.  Gibbs temperature therefore cannot create or destroy a
coefficient relation. -/
theorem sourceMarkedGibbs_phase_strict_one_iff_every_temperature
    {J P : Type*} [Fintype J] [DecidableEq P]
    (c : J → P → ℂ) (base energy : P → ℝ) (radius : ℝ)
    (hphase : ∀ j p, ‖c j p‖ = 1)
    (hbase : ∀ p, 0 < base p) (hsum : Summable base)
    (hupper : ∀ p, energy p ≤ radius) :
    (∃ k : ℕ,
      CofiniteWeightedGramStrict c (sourceMarkedGibbsWeight base energy k)) ↔
      ∀ k : ℕ,
        CofiniteWeightedGramStrict c (sourceMarkedGibbsWeight base energy k) := by
  constructor
  · rintro ⟨k, hk⟩ l
    have htail : TailCoefficientIndependent c :=
      (tailCoefficientIndependent_iff_cofiniteWeightedGramStrict_of_phase
        c (sourceMarkedGibbsWeight base energy k) hphase
        (fun p => mul_pos (hbase p) (Real.exp_pos _))
        (summable_sourceMarkedGibbsWeight base energy radius k
          (fun p => (hbase p).le) hsum hupper)).mpr hk
    exact (tailCoefficientIndependent_iff_cofiniteWeightedGramStrict_of_phase
      c (sourceMarkedGibbsWeight base energy l) hphase
      (fun p => mul_pos (hbase p) (Real.exp_pos _))
      (summable_sourceMarkedGibbsWeight base energy radius l
        (fun p => (hbase p).le) hsum hupper)).mp htail
  · intro h
    exact ⟨0, h 0⟩

/-- **Source-marked isoradical--tropical splitting law.**  A positive Gibbs deformation of a
unit-phase coefficient packet has two orthogonal outputs.  Its cofinite Gram radical is independent
of temperature, while its normalized logarithmic partition converges to the marked support radius.
Thus temperature moves inside a fixed coefficient-matroid stratum and tropicalizes only the source
scale. -/
theorem sourceMarkedGibbs_phase_radical_freeEnergy_split
    {J P : Type*} [Fintype J] [DecidableEq P] [Nonempty P]
    (c : J → P → ℂ) (base energy : P → ℝ) (radius : ℝ)
    (hphase : ∀ j p, ‖c j p‖ = 1)
    (hbase : ∀ p, 0 < base p) (hsum : Summable base)
    (hupper : ∀ p, energy p ≤ radius)
    (happroach : ∀ a : ℝ, a < radius → ∃ p, a < energy p) :
    (∀ k l : ℕ, ∀ F : Finset P, ∀ q : J → ℂ,
      cofiniteWeightedGramEnergy c (sourceMarkedGibbsWeight base energy k) F q = 0 ↔
        cofiniteWeightedGramEnergy c (sourceMarkedGibbsWeight base energy l) F q = 0) ∧
      Tendsto
        (fun k : ℕ =>
          Real.log (sourceMarkedGibbsPartition base energy k) / (k : ℝ))
        atTop (nhds radius) := by
  refine ⟨?_, tendsto_sourceMarkedGibbsPartition_log_div_cold
    base energy radius hbase hsum hupper happroach⟩
  intro k l F q
  exact cofiniteWeightedGramEnergy_sourceMarkedGibbs_zero_iff_change_temperature_of_phase
    c base energy radius hphase hbase hsum hupper k l F q

/-- Signed prime-Dirichlet orientation packets are unit-phase, so their entire positive Gibbs ray
has a fixed cofinite radical and the same tropical source-scale conclusion. -/
theorem sourceMarkedGibbs_primeOrientation_radical_freeEnergy_split
    {J P : Type*} [Fintype J] [DecidableEq P] [Nonempty P]
    (orientation : J → P → Bool) (base energy : P → ℝ) (radius : ℝ)
    (hbase : ∀ p, 0 < base p) (hsum : Summable base)
    (hupper : ∀ p, energy p ≤ radius)
    (happroach : ∀ a : ℝ, a < radius → ∃ p, a < energy p) :
    (∀ k l : ℕ, ∀ F : Finset P, ∀ q : J → ℂ,
      cofiniteWeightedGramEnergy
          (fun j p => primeDirichletSign (orientation j p))
          (sourceMarkedGibbsWeight base energy k) F q = 0 ↔
        cofiniteWeightedGramEnergy
          (fun j p => primeDirichletSign (orientation j p))
          (sourceMarkedGibbsWeight base energy l) F q = 0) ∧
      Tendsto
        (fun k : ℕ =>
          Real.log (sourceMarkedGibbsPartition base energy k) / (k : ℝ))
        atTop (nhds radius) := by
  exact sourceMarkedGibbs_phase_radical_freeEnergy_split
    (fun j p => primeDirichletSign (orientation j p)) base energy radius
    (by
      intro j p
      cases h : orientation j p <;> norm_num [primeDirichletSign, h])
    hbase hsum hupper happroach

end

end GaloisForLFunctions.HTGeometry
