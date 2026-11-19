import GaloisForLFunctions.FiniteFreeProbability.EulerRootFilters
import GaloisForLFunctions.FiniteFreeProbability.NonRealRootCount
import GaloisForLFunctions.FiniteFreeProbability.FiniteFreeDeBruijnNewman
import GaloisForLFunctions.HTGeometry.HeatEscapeNonreal
import GaloisForLFunctions.«arithmetic-positivity-theory».Jensen.XiStrictRoots

/-!
# Cofinal Euler-filtered Xi Jensen tests

Differentiating an anchored Euler filter raises its integer weight by one.
Descending from degree `d+m` to a fixed degree `d` therefore raises even
the smallest available weight by `m`. After scalar normalization the filters
at the lower degree tend coefficientwise to the identity. A persistent
nonreal root at one degree defeats every choice of one positive integer
weight at every sufficiently large degree.
-/

open Polynomial Filter Topology RHTower
open GaloisForLFunctions.HTGeometry

namespace FiniteFreeProbability

noncomputable section

/-- Differentiation raises the anchor weight exactly once. -/
theorem derivative_eulerFilter (s : ℕ) (p : ℝ[X]) :
    derivative (eulerFilter s p) = eulerFilter (s+1) (derivative p) := by
  ext j
  simp only [coeff_derivative, eulerFilter_coeff, Nat.cast_succ]
  ring

private theorem filter_scalar (s : ℕ) (c : ℝ) (p : ℝ[X]) :
    eulerFilter s (C c*p) = C c*eulerFilter s p := by
  ext j
  simp only [eulerFilter_coeff, coeff_C_mul]
  ring

/-- Joint descent in degree and ascent in weight on the actual unshifted Xi ladder. -/
theorem derivative_filtered_xiJensen (s d : ℕ) :
    derivative (eulerFilter s (xiJensenReal (d+1))) =
      C ((d : ℝ)+1)*eulerFilter (s+1) (xiJensenReal d) := by
  rw [derivative_eulerFilter, xiJensenReal_eq, derivative_jensenRev, filter_scalar, xiJensenReal_eq]

private theorem descent_one {s d : ℕ} (h : (eulerFilter s (xiJensenReal (d+1))).Splits) :
    (eulerFilter (s+1) (xiJensenReal d)).Splits := by
  have hd := splits_laguerreShift h 0
  simp only [laguerreShift, map_zero, zero_mul, sub_zero, derivative_filtered_xiJensen] at hd
  exact (splits_mul_iff_right (C_ne_zero.mpr (by positivity)) (Polynomial.Splits.C _)).mp hd

private theorem descent (d m s : ℕ) (h : (eulerFilter s (xiJensenReal (d+m))).Splits) :
    (eulerFilter (s+m) (xiJensenReal d)).Splits := by
  induction m generalizing s with
  | zero => exact h
  | succ m ih =>
    have hl : (eulerFilter (s+1) (xiJensenReal (d+m))).Splits := descent_one h
    simpa [Nat.add_right_comm, Nat.add_assoc, Nat.add_comm] using ih (s+1) hl

private def normalizedFilter (p : ℝ[X]) (s : ℕ) :=
  C (((s : ℝ)+1)⁻¹) * eulerFilter s p

/-- At any fixed polynomial, unbounded anchor weight recovers every coefficient. -/
private theorem normalized_coeff_limit (p : ℝ[X]) (j : ℕ) :
    Tendsto (fun s => (normalizedFilter p s).coeff j) atTop (𝓝 (p.coeff j)) := by
  have hinv : Tendsto (fun s : ℕ => (j : ℝ)/((s : ℝ)+1)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop)
  have he (s : ℕ) : (normalizedFilter p s).coeff j = (1+(j : ℝ)/((s : ℝ)+1))*p.coeff j := by
    rw [normalizedFilter, coeff_C_mul, eulerFilter_coeff]
    field_simp
    <;> ring
  simp_rw [he]
  simpa using ((tendsto_const_nhds (x := (1 : ℝ))).add hinv).mul_const (p.coeff j)

private theorem filtered_eventually_bad {p : ℝ[X]} (h : ¬ p.Splits) :
    ∀ᶠ s : ℕ in atTop, ¬ (eulerFilter s p).Splits := by
  have hp : p ≠ 0 := by rintro rfl; exact h (Polynomial.Splits.of_natDegree_le_one (by simp))
  have hbad := _root_.HTGeometry.eventually_not_splits_of_coeff_limit
    (p := normalizedFilter p) (q := p) (N := p.natDegree)
    (fun s => (natDegree_C_mul_le _ _).trans (eulerFilter_natDegree s p).le)
    le_rfl hp (normalized_coeff_limit p) h
  filter_upwards [hbad] with s hs
  exact fun hf => hs ((Polynomial.Splits.C _).mul hf)

/-- A failure at one unfiltered degree forces failure at all large degrees simultaneously
for every positive integer anchor, including degree-dependent anchors. -/
theorem cofinal_filter_obstruction (d : ℕ) :
    (xiJensenReal d).Splits ∨ ∀ᶠ n : ℕ in atTop, ∀ s : ℕ, ¬ (eulerFilter s (xiJensenReal n)).Splits := by
  by_cases h : (xiJensenReal d).Splits
  · exact Or.inl h
  right
  obtain ⟨M, hM⟩ := eventually_atTop.mp (filtered_eventually_bad h)
  filter_upwards [eventually_ge_atTop (d+M)] with n hn
  intro s hs
  obtain ⟨m, hm⟩ : ∃ m, n = d+m := ⟨n-d, by omega⟩
  subst n
  exact hM (s+m) (by omega) (descent d m s hs)

/-- In each tested degree the anchor may be chosen after inspecting the polynomial. -/
theorem riemannHypothesis_iff_cofinal_eulerFilter :
    RiemannHypothesis ↔ ∃ᶠ d : ℕ in atTop, ∃ s : ℕ, (eulerFilter s (xiJensenReal d)).Splits := by
  constructor
  · intro hRH
    apply Frequently.of_forall
    intro d
    refine ⟨0, ?_⟩
    have h := eulerFilter_real_root_gain 0 (xiJensenReal d)
    have h0 := (JensenStrict.jensenReverse_splits (riemannHypothesis_iff_laguerrePolya_XiC.mp hRH)
      XiC_conj d).natDegree_eq_card_roots
    have h1 := Polynomial.card_roots' (eulerFilter 0 (xiJensenReal d))
    rw [splits_iff_card_roots, eulerFilter_natDegree]
    rw [eulerFilter_natDegree] at h1
    omega
  · intro h
    apply riemannHypothesis_iff_frequently_splits_jensenPoly_XiC.mpr
    apply Frequently.of_forall
    intro d
    rcases cofinal_filter_obstruction d with hs | hbad
    · rw [← reflect_jensenReverse]
      exact Splits.reflect hs (natDegree_jensenReverse_le _ _)
    · obtain ⟨n, ⟨s, hs⟩, hn⟩ := (h.and_eventually hbad).exists
      exact (hn s hs).elim

#print axioms cofinal_filter_obstruction
#print axioms riemannHypothesis_iff_cofinal_eulerFilter

end

end FiniteFreeProbability
