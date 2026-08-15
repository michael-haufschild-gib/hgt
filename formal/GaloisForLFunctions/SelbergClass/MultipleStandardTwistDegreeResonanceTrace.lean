import GaloisForLFunctions.HTGeometry.KroneckerWeylDensity

/-!
# Degree-tangent finite resonance traces

For a finite two-index residue fibre, the polar-hyperplane tangent flow has
frequency `dG * log m - dF * log n`.  This module proves its exact Bohr zero
mode: it selects `m ^ dG = n ^ dF`, and, for equal positive degrees, exactly
the diagonal.  It is deliberately finite-dimensional; it does not assert an
unbounded trace of a meromorphically continued regular part.
-/

open Filter Topology

namespace GaloisForLFunctions.SelbergClass

noncomputable section

/-- Fourier frequency of the polar-hyperplane tangent flow for a pair of
positive Dirichlet indices. -/
def tangentFrequency (dF dG : ℝ) (m n : ℕ) : ℝ :=
  dG * Real.log (m : ℝ) - dF * Real.log (n : ℝ)

/-- Zero weighted tangent frequency is exactly the degree-resonance equation.
The positivity assumptions exclude the artificial `log 0` case; the public
positive-natural version below supplies them definitionally. -/
theorem tangentFrequency_eq_zero_iff_rpow_eq
    {dF dG : ℝ} {m n : ℕ} (hm : 0 < m) (hn : 0 < n) :
    tangentFrequency dF dG m n = 0 ↔ (m : ℝ) ^ dG = (n : ℝ) ^ dF := by
  constructor
  · intro h
    rw [tangentFrequency] at h
    have hlog : dG * Real.log (m : ℝ) = dF * Real.log (n : ℝ) := sub_eq_zero.mp h
    rw [Real.rpow_def_of_pos (by exact_mod_cast hm),
      Real.rpow_def_of_pos (by exact_mod_cast hn)]
    exact congrArg Real.exp (by simpa [mul_comm] using hlog)
  · intro h
    rw [tangentFrequency]
    rw [Real.rpow_def_of_pos (by exact_mod_cast hm),
      Real.rpow_def_of_pos (by exact_mod_cast hn)] at h
    apply sub_eq_zero.mpr
    simpa [mul_comm] using Real.exp_injective h

/-- At equal positive degree, degree resonance is the usual diagonal. -/
theorem tangentFrequency_equal_degree_eq_zero_iff
    {d : ℝ} {m n : ℕ} (hd : 0 < d) (hm : 0 < m) (hn : 0 < n) :
    tangentFrequency d d m n = 0 ↔ m = n := by
  rw [tangentFrequency_eq_zero_iff_rpow_eq hm hn]
  constructor
  · intro h
    have hm0 : (m : ℝ) ∈ Set.Ici 0 := by
      change 0 ≤ (m : ℝ)
      exact_mod_cast (Nat.zero_le m)
    have hn0 : (n : ℝ) ∈ Set.Ici 0 := by
      change 0 ≤ (n : ℝ)
      exact_mod_cast (Nat.zero_le n)
    have hcast : (m : ℝ) = (n : ℝ) :=
      (Real.strictMonoOn_rpow_Ici_of_exponent_pos hd).injOn hm0 hn0 h
    exact_mod_cast hcast
  · rintro rfl
    rfl

/-- Finite Fourier sum carried by the polar-hyperplane tangent flow. -/
def weightedTangentFlow (dF dG : ℝ) (c : ℕ × ℕ → ℂ)
    (s : Finset (ℕ × ℕ)) : ℝ → ℂ :=
  fun t => ∑ x ∈ s, c x * expChar (tangentFrequency dF dG x.1 x.2) t

/-- The finite weighted tangent trace retains precisely degree-resonant pairs. -/
theorem bohrMean_weightedTangentFlow_degree_resonance
    (dF dG : ℝ) (c : ℕ × ℕ → ℂ) (s : Finset (ℕ × ℕ))
    (hpos : ∀ x ∈ s, 0 < x.1 ∧ 0 < x.2) :
    bohrMean (weightedTangentFlow dF dG c s) =
      ∑ x ∈ s.filter (fun x => (x.1 : ℝ) ^ dG = (x.2 : ℝ) ^ dF), c x := by
  have hfilter : s.filter (fun x => tangentFrequency dF dG x.1 x.2 = 0) =
      s.filter (fun x => (x.1 : ℝ) ^ dG = (x.2 : ℝ) ^ dF) :=
    Finset.filter_congr fun x hx =>
      tangentFrequency_eq_zero_iff_rpow_eq (hpos x hx).1 (hpos x hx).2
  change bohrMean (fun t => ∑ x ∈ s,
    c x * expChar (tangentFrequency dF dG x.1 x.2) t) = _
  rw [bohrMean_sum_expChar, ← Finset.sum_filter, hfilter]

/-- The equal-degree finite tangent trace retains precisely diagonal pairs. -/
theorem bohrMean_weightedTangentFlow_equal_degree
    (d : ℝ) (hd : 0 < d) (c : ℕ × ℕ → ℂ) (s : Finset (ℕ × ℕ))
    (hpos : ∀ x ∈ s, 0 < x.1 ∧ 0 < x.2) :
    bohrMean (weightedTangentFlow d d c s) =
      ∑ x ∈ s.filter (fun x => x.1 = x.2), c x := by
  have hfilter : s.filter (fun x => tangentFrequency d d x.1 x.2 = 0) =
      s.filter (fun x => x.1 = x.2) :=
    Finset.filter_congr fun x hx =>
      tangentFrequency_equal_degree_eq_zero_iff hd (hpos x hx).1 (hpos x hx).2
  change bohrMean (fun t => ∑ x ∈ s,
    c x * expChar (tangentFrequency d d x.1 x.2) t) = _
  rw [bohrMean_sum_expChar, ← Finset.sum_filter, hfilter]

/-- Positive-index version of the finite weighted tangent flow. -/
def positiveWeightedTangentFlow (dF dG : ℝ) (c : ℕ+ × ℕ+ → ℂ)
    (s : Finset (ℕ+ × ℕ+)) : ℝ → ℂ :=
  fun t => ∑ x ∈ s, c x * expChar (tangentFrequency dF dG x.1 x.2) t

/-- The positive-index tangent trace needs no external positivity premise. -/
theorem bohrMean_positiveWeightedTangentFlow_degree_resonance
    (dF dG : ℝ) (c : ℕ+ × ℕ+ → ℂ) (s : Finset (ℕ+ × ℕ+)) :
    bohrMean (positiveWeightedTangentFlow dF dG c s) =
      ∑ x ∈ s.filter (fun x => ((x.1 : ℕ) : ℝ) ^ dG = ((x.2 : ℕ) : ℝ) ^ dF), c x := by
  have hfilter : s.filter (fun x => tangentFrequency dF dG x.1 x.2 = 0) =
      s.filter (fun x => ((x.1 : ℕ) : ℝ) ^ dG = ((x.2 : ℕ) : ℝ) ^ dF) :=
    Finset.filter_congr fun x _ =>
      tangentFrequency_eq_zero_iff_rpow_eq x.1.pos x.2.pos
  change bohrMean (fun t => ∑ x ∈ s,
    c x * expChar (tangentFrequency dF dG x.1 x.2) t) = _
  rw [bohrMean_sum_expChar, ← Finset.sum_filter, hfilter]

/-- For positive indices and equal positive degrees, the tangent trace is an
unconditional finite diagonal projector. -/
theorem bohrMean_positiveWeightedTangentFlow_equal_degree
    (d : ℝ) (hd : 0 < d) (c : ℕ+ × ℕ+ → ℂ) (s : Finset (ℕ+ × ℕ+)) :
    bohrMean (positiveWeightedTangentFlow d d c s) =
      ∑ x ∈ s.filter (fun x => x.1 = x.2), c x := by
  have hfilter : s.filter (fun x => tangentFrequency d d x.1 x.2 = 0) =
      s.filter (fun x => x.1 = x.2) :=
    Finset.filter_congr fun x _ => by
      constructor
      · intro h
        apply Subtype.ext
        exact (tangentFrequency_equal_degree_eq_zero_iff hd x.1.pos x.2.pos).mp h
      · intro h
        exact (tangentFrequency_equal_degree_eq_zero_iff hd x.1.pos x.2.pos).mpr
          (congrArg Subtype.val h)
  change bohrMean (fun t => ∑ x ∈ s,
    c x * expChar (tangentFrequency d d x.1 x.2) t) = _
  rw [bohrMean_sum_expChar, ← Finset.sum_filter, hfilter]

end

end GaloisForLFunctions.SelbergClass
