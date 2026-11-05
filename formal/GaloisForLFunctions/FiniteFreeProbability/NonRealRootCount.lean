import GaloisForLFunctions.FiniteFreeProbability.AlmostAllJensenRootsAreReal

/-!
# The number of non-real roots of `R_d(Ξ)` is monotone in the degree

`N_d = #{non-real roots of R_d(Ξ)}`, with multiplicity. Since `R_{d+1}' = (d + 1) R_d` and the polynomials
are real, Rolle gives `N_d ≤ N_{d+1}`: a non-real root, once present, persists in every higher degree. With
R38, `N_d` is a nondecreasing sequence with `N_d = o(d)`; RH is `N_d = 0` for all `d`.
-/

open Polynomial Filter Topology Complex
open GaloisForLFunctions.HTGeometry RHTower

namespace FiniteFreeProbability

noncomputable section

/-- A real polynomial has as many real roots, with multiplicity, as its complexification. -/
theorem filter_im_eq_zero_roots_map (P : ℝ[X]) :
    (P.map (algebraMap ℝ ℂ)).roots.filter (fun z => ¬ z.im ≠ 0) =
      P.roots.map fun x : ℝ => (x : ℂ) := by
  classical
  ext z
  by_cases hz : z.im = 0
  · have hzr : z = ((z.re : ℝ) : ℂ) := Complex.ext (by simp) (by simp [hz])
    have hcount : Multiset.count z ((P.map (algebraMap ℝ ℂ)).roots.filter
        (fun z => ¬ z.im ≠ 0)) = Multiset.count z (P.map (algebraMap ℝ ℂ)).roots :=
      Multiset.count_filter_of_pos (by simpa using hz)
    rw [hcount, count_roots]
    conv_rhs => rw [hzr]
    rw [Multiset.count_map_eq_count' _ _ ofReal_injective, count_roots]
    conv_lhs => rw [hzr]
    exact (eq_rootMultiplicity_map (f := algebraMap ℝ ℂ) (algebraMap ℝ ℂ).injective z.re).symm
  · have h1 : z ∉ (P.map (algebraMap ℝ ℂ)).roots.filter (fun z => ¬ z.im ≠ 0) := fun h =>
      (Multiset.mem_filter.1 h).2 hz
    have h2 : z ∉ P.roots.map fun x : ℝ => (x : ℂ) := fun h => by
      obtain ⟨x, _, rfl⟩ := Multiset.mem_map.1 h
      exact hz (ofReal_im x)
    rw [Multiset.count_eq_zero_of_notMem h1, Multiset.count_eq_zero_of_notMem h2]

/-- The number of non-real roots of a real polynomial of degree `d` is `d` minus its number of real
roots. -/
theorem card_nonreal_roots_map (P : ℝ[X]) :
    Multiset.card ((P.map (algebraMap ℝ ℂ)).roots.filter fun z => z.im ≠ 0) + Multiset.card P.roots =
      P.natDegree := by
  have hsplit := Multiset.filter_add_not (fun x : ℂ => x.im ≠ 0) (P.map (algebraMap ℝ ℂ)).roots
  have hcard := congrArg Multiset.card hsplit
  have hdeg : Multiset.card (P.map (algebraMap ℝ ℂ)).roots = P.natDegree := by
    rw [← (IsAlgClosed.splits (P.map (algebraMap ℝ ℂ))).natDegree_eq_card_roots,
      natDegree_map_eq_of_injective (algebraMap ℝ ℂ).injective]
  rw [Multiset.card_add, filter_im_eq_zero_roots_map, Multiset.card_map, hdeg] at hcard
  exact hcard

/-- The real polynomial `R_d(Ξ)`. -/
abbrev xiJensenReal (d : ℕ) : ℝ[X] := jensenReverse (realTaylorCoeff XiC) d

theorem constantCoeff_mk_realTaylorCoeff :
    PowerSeries.constantCoeff (PowerSeries.mk (realTaylorCoeff XiC)) ≠ 0 := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_mk]
  intro h
  have hc := constantCoeff_xiSeries
  rw [xiSeries, ← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_mk, h] at hc
  exact XiC_zero_ne (by simpa using hc.symm)

theorem xiJensenReal_eq (d : ℕ) :
    xiJensenReal d = jensenRev d (PowerSeries.mk (realTaylorCoeff XiC)) :=
  (jensenRev_mk_eq_jensenReverse _ _).symm

theorem natDegree_xiJensenReal (d : ℕ) : (xiJensenReal d).natDegree = d := by
  rw [xiJensenReal_eq]
  exact natDegree_jensenRev constantCoeff_mk_realTaylorCoeff

/-- Rolle: the real root count grows by at most one per degree. -/
theorem card_roots_xiJensenReal_succ_le (d : ℕ) :
    Multiset.card (xiJensenReal (d + 1)).roots ≤ Multiset.card (xiJensenReal d).roots + 1 := by
  have hR := card_roots_le_derivative (xiJensenReal (d + 1))
  have hd : derivative (xiJensenReal (d + 1)) = C ((d : ℝ) + 1) * xiJensenReal d := by
    rw [xiJensenReal_eq, xiJensenReal_eq]
    exact derivative_jensenRev d _
  rwa [hd, roots_C_mul _ (by positivity : ((d : ℝ) + 1) ≠ 0)] at hR

/-- **The non-real root count of `R_d(Ξ)` is nondecreasing in `d`.** -/
theorem card_nonreal_roots_le_succ (d : ℕ) :
    Multiset.card ((jensenRev d xiSeries).roots.filter fun z => z.im ≠ 0) ≤
      Multiset.card ((jensenRev (d + 1) xiSeries).roots.filter fun z => z.im ≠ 0) := by
  have h1 := card_nonreal_roots_map (xiJensenReal d)
  have h2 := card_nonreal_roots_map (xiJensenReal (d + 1))
  rw [natDegree_xiJensenReal] at h1 h2
  rw [jensenRev_xiSeries, jensenRev_xiSeries]
  have h3 := card_roots_xiJensenReal_succ_le d
  simp only [xiJensenReal] at h1 h2 h3
  omega

end

end FiniteFreeProbability

#print axioms FiniteFreeProbability.card_nonreal_roots_le_succ
