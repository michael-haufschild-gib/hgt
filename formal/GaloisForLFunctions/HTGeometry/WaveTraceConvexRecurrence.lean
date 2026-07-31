import GaloisForLFunctions.HTGeometry.WaveTraceSpectrum
import GaloisForLFunctions.HTGeometry.CofinalConvexRecurrence

/-!
# Convex recurrence of the wave-trace hierarchy

Monomial weights assemble the wave traces of one spectrum into a finite vector path. Every
linear observable of that path is again a wave trace, of the polynomial whose coefficients
are the observable's coordinates, and a nonzero observable produces a nonzero polynomial.

Hence sign escape of every nonzero polynomial weight upgrades automatically to escape from
every closed half-space, and the convex recurrence law applies: after every time, at most
`K + 1` distinct times carry a positive probability weight annihilating the first `K`
regularized wave traces simultaneously.
-/

open Filter Set Topology

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- Coordinate expansion of a linear observable on a finite product. -/
theorem apply_eq_sum_single {K : ℕ} (f : (Fin K → ℝ) →L[ℝ] ℝ) (x : Fin K → ℝ) :
    f x = ∑ j, x j * f (Pi.single j 1) := by
  classical
  have hx : x = ∑ j, x j • Pi.single j (1 : ℝ) := by
    funext i
    simp [Pi.single_apply, Finset.sum_ite_eq]
  conv_lhs => rw [hx]
  rw [map_sum]
  simp

/-- The polynomial assembled from the coordinates of a linear observable. -/
def observablePolynomial {K : ℕ} (f : (Fin K → ℝ) →L[ℝ] ℝ) : Polynomial ℝ :=
  ∑ j : Fin K, f (Pi.single j 1) • (Polynomial.X ^ (j : ℕ) : Polynomial ℝ)

theorem coeff_observablePolynomial {K : ℕ} (f : (Fin K → ℝ) →L[ℝ] ℝ) (j : Fin K) :
    (observablePolynomial f).coeff (j : ℕ) = f (Pi.single j 1) := by
  classical
  rw [observablePolynomial, Polynomial.finsetSum_coeff]
  rw [Finset.sum_eq_single j]
  · rw [Polynomial.coeff_smul, Polynomial.coeff_X_pow, if_pos rfl, smul_eq_mul, mul_one]
  · intro i _ hij
    have hne : ((j : ℕ)) ≠ ((i : ℕ)) := fun h => hij (Fin.ext h.symm)
    rw [Polynomial.coeff_smul, Polynomial.coeff_X_pow, if_neg hne, smul_zero]
  · intro h
    exact absurd (Finset.mem_univ j) h

theorem observablePolynomial_ne_zero {K : ℕ} {f : (Fin K → ℝ) →L[ℝ] ℝ} (hf : f ≠ 0) :
    observablePolynomial f ≠ 0 := by
  intro hzero
  apply hf
  ext x
  rw [apply_eq_sum_single f x]
  refine Finset.sum_eq_zero fun j _ => ?_
  have : f (Pi.single j 1) = 0 := by
    rw [← coeff_observablePolynomial f j, hzero, Polynomial.coeff_zero]
  simp [this]

namespace WaveSpectrum

variable {G : Type*} (S : WaveSpectrum G)

/-- The finite vector of regularized wave traces with monomial weights. -/
def tracePath (K : ℕ) (t : ℝ) : Fin K → ℝ :=
  fun j => S.realWaveTrace (Polynomial.X ^ (j : ℕ)) t

/-- Every nonzero polynomial weight drives its wave trace strictly negative after every
time. -/
def CofinalWaveSignEscape : Prop :=
  ∀ P : Polynomial ℝ, P ≠ 0 → ∀ T : ℝ, ∃ t, T < t ∧ S.realWaveTrace P t < 0

/-- Every linear observable of the trace path is the wave trace of the assembled
polynomial. -/
theorem apply_tracePath {K : ℕ} (f : (Fin K → ℝ) →L[ℝ] ℝ) (t : ℝ) :
    f (S.tracePath K t) = S.realWaveTrace (observablePolynomial f) t := by
  rw [apply_eq_sum_single f (S.tracePath K t), observablePolynomial, S.realWaveTrace_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [S.realWaveTrace_smul, tracePath]
  ring

/-- Sign escape for polynomial weights upgrades to escape from every closed half-space. -/
theorem cofinalHalfSpaceEscape_tracePath (h : S.CofinalWaveSignEscape) (K : ℕ) :
    CofinalHalfSpaceEscape (S.tracePath K) := by
  intro f hf T
  obtain ⟨t, ht, hlt⟩ := h (observablePolynomial f) (observablePolynomial_ne_zero hf) T
  exact ⟨t, ht, by rw [S.apply_tracePath f t]; exact hlt⟩

/-- **Cofinal convex recurrence of the wave-trace hierarchy.** After every time, at most
`K + 1` distinct later times carry a positive probability weight annihilating the first `K`
regularized wave traces exactly. -/
theorem exists_cofinal_positive_quadrature_waveTrace
    (h : S.CofinalWaveSignEscape) (K : ℕ) (T : ℝ) :
    ∃ (nodes : Finset ℝ) (w : ℝ → ℝ),
      nodes.Nonempty ∧
      nodes.card ≤ K + 1 ∧
      (∀ t ∈ nodes, T < t) ∧
      (∀ t ∈ nodes, 0 < w t) ∧
      (∑ t ∈ nodes, w t) = 1 ∧
      ∀ j : Fin K, (∑ t ∈ nodes, w t * S.realWaveTrace (Polynomial.X ^ (j : ℕ)) t) = 0 := by
  obtain ⟨nodes, w, hne, hcard, hT, hpos, hsum, hcomb⟩ :=
    exists_cofinal_positive_quadrature (S.cofinalHalfSpaceEscape_tracePath h K) T
  refine ⟨nodes, w, hne, ?_, hT, hpos, hsum, ?_⟩
  · have hrank : Module.finrank ℝ (Fin K → ℝ) = K := by simp
    rwa [hrank] at hcard
  · intro j
    have := congrFun hcomb j
    simpa [tracePath, Finset.sum_apply, smul_eq_mul] using this

end WaveSpectrum

end

end GaloisForLFunctions.HTGeometry
