import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.OccupationProbabilities.SplitDomain

/-! # Abscissa and boundary of an individual divisor split -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.ShellMixing

/-- Real parts where the two-copy wave has finite mass. -/
def realSplitDomain (v : MissingWave) := {x : ℝ | finiteSplit v (x:ℂ)}

/-- Infimum of the real parts with finite output. -/
def splitAbscissa (v : MissingWave) := sInf (realSplitDomain v)

theorem finiteSplit_mono_re {v : MissingWave} {s t : ℂ} (h : t.re ≤ s.re)
    (ht : finiteSplit v t) : finiteSplit v s := by
  apply (finiteSplit_iff_law v s).mpr
  exact ((finiteSplit_iff_law v t).mp ht).of_nonneg_of_le
    (fun k => mul_nonneg (Real.exp_pos _).le ((exteriorLaw v).property.1 _))
    (fun k => mul_le_mul_of_nonneg_right (shellMass_antitone_re h _) ((exteriorLaw v).property.1 _))

private theorem half_mem (v : MissingWave) : (1/2:ℝ) ∈ realSplitDomain v :=
  (forall_finiteSplit_iff ((1/2:ℝ):ℂ)).mpr le_rfl v

private theorem lower_bound (v : MissingWave) : ∀ x ∈ realSplitDomain v, 0 ≤ x :=
  fun x hx => ((exists_finiteSplit_iff (x:ℂ)).mp ⟨v,hx⟩).le

theorem splitAbscissa_bounds (v : MissingWave) : 0 ≤ splitAbscissa v ∧ splitAbscissa v ≤ 1/2 :=
  ⟨le_csInf ⟨_,half_mem v⟩ (lower_bound v),csInf_le ⟨0,lower_bound v⟩ (half_mem v)⟩

/-- Every point strictly to the right is admitted. At equality the single boundary reading settles convergence for the whole vertical line. -/
theorem finiteSplit_iff_abscissa (v : MissingWave) (s : ℂ) :
    finiteSplit v s ↔ splitAbscissa v < s.re ∨
      splitAbscissa v = s.re ∧ finiteSplit v ((splitAbscissa v:ℝ):ℂ) := by
  constructor
  · intro hs
    have hm : s.re ∈ realSplitDomain v := finiteSplit_mono_re (s := (s.re:ℂ)) (t := s) le_rfl hs
    have h : splitAbscissa v ≤ s.re := csInf_le ⟨0,lower_bound v⟩ hm
    rcases h.lt_or_eq with hh|hh
    · exact Or.inl hh
    · exact Or.inr ⟨hh,finiteSplit_mono_re (show s.re ≤ splitAbscissa v from hh.ge) hs⟩
  · rintro (h|⟨he,hb⟩)
    · obtain ⟨x,hx,hxs⟩ := exists_lt_of_csInf_lt (show (realSplitDomain v).Nonempty from ⟨_,half_mem v⟩) h
      exact finiteSplit_mono_re (t := (x:ℂ)) hxs.le hx
    · exact finiteSplit_mono_re (t := ((splitAbscissa v:ℝ):ℂ)) he.le hb

/-- Exactly the two endpoint rules imposed by normalization and infinite mean label. -/
theorem splitBoundary_constraints (v : MissingWave) :
    (finiteSplit v ((splitAbscissa v:ℝ):ℂ) → 0 < splitAbscissa v) ∧
    (¬ finiteSplit v ((splitAbscissa v:ℝ):ℂ) → splitAbscissa v < 1/2) := by
  refine ⟨fun h => (exists_finiteSplit_iff _).mp ⟨v,h⟩,fun h => lt_of_not_ge (fun hh => ?_)⟩
  exact h ((forall_finiteSplit_iff _).mpr hh v)

open Filter Topology in
theorem splitAbscissa_of_germ {v w : MissingWave} {z : ℂ} (hz : 0 < z.re)
    (hg : omissionPartition v =ᶠ[𝓝 z] omissionPartition w) : splitAbscissa v = splitAbscissa w := by
  apply congrArg sInf
  ext x
  change finiteSplit v (x:ℂ) ↔ finiteSplit w (x:ℂ)
  rw [finiteSplit_iff_law,finiteSplit_iff_law,(omission_germ_iff_probability v w hz).mp hg]

#print axioms finiteSplit_mono_re
#print axioms splitAbscissa_bounds
#print axioms finiteSplit_iff_abscissa
#print axioms splitBoundary_constraints
#print axioms splitAbscissa_of_germ

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.ShellMixing
