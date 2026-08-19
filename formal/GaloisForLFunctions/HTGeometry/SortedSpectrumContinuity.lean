/-
# Continuity of the sorted spectrum of a Hermitian family

The canonical eigenvalue tuple of a Hermitian matrix is a choice, and choices need not vary
continuously.  Its increasing rearrangement does: the eigenvalue energy bounds the spectrum
uniformly along any convergent sequence, so every subsequence has a convergent sub-subsequence,
its limit is monotone, and its power sums are the limits of the real traces of the powers -- hence
the eigenvalue power sums of the limit matrix.  Monotone tuples with equal power sums are equal, so
the limit is forced and the whole sequence converges.

This gives a canonical *measurable* spectral coordinate on any continuous Hermitian family, which
is what a phase built from the spectrum needs before it can be integrated.

Main results:
* `sortedTuple`, `monotone_sortedTuple`, `sum_pow_sortedTuple` — the increasing rearrangement.
* `eq_of_monotone_of_sum_pow_eq` — monotone tuples with equal power sums coincide.
* `sum_pow_eigenvalues_eq_trace_pow_re` — the eigenvalue power sums are the real power traces.
* `continuous_sortedTuple_eigenvalues` — **the sorted spectrum of a continuous Hermitian family is
  continuous**.
* `measurable_sortedTuple_eigenvalues` — hence measurable.
-/
import GaloisForLFunctions.HTGeometry.SpectralEnsembleEigenvalueBound
import GaloisForLFunctions.HTGeometry.MultisetNewtonSolve

open Filter Topology Set

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {D : ℕ}

/-- The increasing rearrangement of a real tuple. -/
def sortedTuple (a : Fin D → ℝ) : Fin D → ℝ := a ∘ Tuple.sort a

theorem monotone_sortedTuple (a : Fin D → ℝ) : Monotone (sortedTuple a) := Tuple.monotone_sort a

theorem sum_pow_sortedTuple (a : Fin D → ℝ) (p : ℕ) :
    ∑ i, (sortedTuple a i) ^ p = ∑ i, (a i) ^ p :=
  Equiv.sum_comp (Tuple.sort a) fun x => (a x) ^ p

theorem abs_sortedTuple_le {a : Fin D → ℝ} {C : ℝ} (h : ∀ i, |a i| ≤ C) (i : Fin D) :
    |sortedTuple a i| ≤ C := h _

/-- **Monotone tuples with equal power sums coincide.** -/
theorem eq_of_monotone_of_sum_pow_eq {a b : Fin D → ℝ}
    (ha : Monotone a) (hb : Monotone b)
    (h : ∀ p : ℕ, ∑ i, (a i) ^ p = ∑ i, (b i) ^ p) : a = b := by
  have hmul : Multiset.map a Finset.univ.val = Multiset.map b Finset.univ.val := by
    refine multiset_eq_of_powerSum_eq fun p => ?_
    rw [Multiset.map_map, Multiset.map_map]
    exact h p
  have hA : Multiset.map a Finset.univ.val = (↑(List.ofFn a) : Multiset ℝ) := by
    simp [List.ofFn_eq_map]
  have hB : Multiset.map b Finset.univ.val = (↑(List.ofFn b) : Multiset ℝ) := by
    simp [List.ofFn_eq_map]
  have hcoe : (↑(List.ofFn a) : Multiset ℝ) = ↑(List.ofFn b) := by rw [← hA, ← hB, hmul]
  exact List.ofFn_injective (List.Perm.eq_of_sortedLE
    (List.sortedLE_ofFn_iff.mpr ha) (List.sortedLE_ofFn_iff.mpr hb) (Multiset.coe_eq_coe.mp hcoe))

/-- The eigenvalue power sums of a Hermitian matrix are the real traces of its powers. -/
theorem sum_pow_eigenvalues_eq_trace_pow_re {H : Matrix (Fin D) (Fin D) ℂ} (hH : H.IsHermitian)
    (k : ℕ) : ∑ i, (hH.eigenvalues i) ^ k = ((H ^ k).trace).re := by
  rw [trace_pow_eq_sum_eigenvalues_pow hH k, Complex.re_sum]
  exact Finset.sum_congr rfl fun i _ => by rw [← Complex.ofReal_pow, Complex.ofReal_re]

/-- **The sorted spectrum of a continuous Hermitian family is continuous.** -/
theorem continuous_sortedTuple_eigenvalues {X : Type*} [TopologicalSpace X]
    [FirstCountableTopology X] {F : X → Matrix (Fin D) (Fin D) ℂ} (hF : Continuous F)
    (hHerm : ∀ x, (F x).IsHermitian) :
    Continuous (fun x => sortedTuple (hHerm x).eigenvalues) := by
  have hcontTr : ∀ p : ℕ, Continuous (fun x => (((F x) ^ p).trace).re) := by
    intro p
    refine Complex.continuous_re.comp ?_
    refine continuous_finsetSum _ fun i _ => ?_
    exact (continuous_apply i).comp ((continuous_apply i).comp (hF.pow p))
  have hsumpow : ∀ (x : X) (p : ℕ),
      ∑ i, (sortedTuple (hHerm x).eigenvalues i) ^ p = (((F x) ^ p).trace).re := by
    intro x p
    rw [sum_pow_sortedTuple, sum_pow_eigenvalues_eq_trace_pow_re]
  refine continuous_iff_continuousAt.mpr fun x₀ => ?_
  refine Filter.tendsto_of_subseq_tendsto ?_
  intro ns hns
  have htr2 : Tendsto (fun n => (((F (ns n)) ^ 2).trace).re) atTop
      (𝓝 ((((F x₀) ^ 2).trace).re)) := ((hcontTr 2).tendsto x₀).comp hns
  obtain ⟨B₀, hB₀⟩ := htr2.bddAbove_range
  set B : ℝ := max B₀ 0 with hBdef
  have hbound : ∀ (n : ℕ) (i : Fin D),
      |sortedTuple (hHerm (ns n)).eigenvalues i| ≤ Real.sqrt B := by
    intro n i
    refine abs_sortedTuple_le (fun j => ?_) i
    have h1 : (((F (ns n)) ^ 2).trace).re ≤ B :=
      le_trans (hB₀ ⟨n, rfl⟩) (le_max_left _ _)
    exact le_trans (abs_eigenvalues_le_sqrt_trace_sq_re (hHerm (ns n)) j) (Real.sqrt_le_sqrt h1)
  set K : Set (Fin D → ℝ) :=
    Set.univ.pi (fun _ : Fin D => Set.Icc (-Real.sqrt B) (Real.sqrt B)) with hKdef
  have hK : IsCompact K := isCompact_univ_pi fun _ => isCompact_Icc
  have hmemK : ∀ n : ℕ, (fun x => sortedTuple (hHerm x).eigenvalues) (ns n) ∈ K :=
    fun n i _ => abs_le.mp (hbound n i)
  obtain ⟨Lstar, _, φ, hφ, hconv⟩ := hK.tendsto_subseq hmemK
  refine ⟨φ, ?_⟩
  have hcoord : ∀ i : Fin D,
      Tendsto (fun n => sortedTuple (hHerm (ns (φ n))).eigenvalues i) atTop (𝓝 (Lstar i)) :=
    fun i => ((continuous_apply i).tendsto Lstar).comp hconv
  have hmonoL : Monotone Lstar := by
    intro i j hij
    exact le_of_tendsto_of_tendsto' (hcoord i) (hcoord j)
      fun n => monotone_sortedTuple _ hij
  have hpow : ∀ p : ℕ,
      ∑ i, (Lstar i) ^ p = ∑ i, (sortedTuple (hHerm x₀).eigenvalues i) ^ p := by
    intro p
    have hc : Continuous (fun v : Fin D → ℝ => ∑ i, (v i) ^ p) :=
      continuous_finsetSum _ fun i _ => (continuous_apply i).pow p
    have hlhs : Tendsto (fun n => ∑ i, (sortedTuple (hHerm (ns (φ n))).eigenvalues i) ^ p)
        atTop (𝓝 (∑ i, (Lstar i) ^ p)) := (hc.tendsto Lstar).comp hconv
    have hrhs : Tendsto (fun n => ∑ i, (sortedTuple (hHerm (ns (φ n))).eigenvalues i) ^ p)
        atTop (𝓝 ((((F x₀) ^ p).trace).re)) := by
      refine Filter.Tendsto.congr (fun n => (hsumpow (ns (φ n)) p).symm) ?_
      exact ((hcontTr p).tendsto x₀).comp (hns.comp hφ.tendsto_atTop)
    rw [tendsto_nhds_unique hlhs hrhs, hsumpow x₀ p]
  have hLeq : Lstar = sortedTuple (hHerm x₀).eigenvalues :=
    eq_of_monotone_of_sum_pow_eq hmonoL (monotone_sortedTuple _) hpow
  have hfin : Tendsto (fun n => sortedTuple (hHerm (ns (φ n))).eigenvalues) atTop
      (𝓝 (sortedTuple (hHerm x₀).eigenvalues)) := hLeq ▸ hconv
  exact hfin

/-- The sorted spectrum of a continuous Hermitian family is measurable. -/
theorem measurable_sortedTuple_eigenvalues {X : Type*} [TopologicalSpace X]
    [FirstCountableTopology X] [MeasurableSpace X] [OpensMeasurableSpace X]
    {F : X → Matrix (Fin D) (Fin D) ℂ} (hF : Continuous F)
    (hHerm : ∀ x, (F x).IsHermitian) :
    Measurable (fun x => sortedTuple (hHerm x).eigenvalues) :=
  (continuous_sortedTuple_eigenvalues hF hHerm).measurable

end

end GaloisForLFunctions.HTGeometry
