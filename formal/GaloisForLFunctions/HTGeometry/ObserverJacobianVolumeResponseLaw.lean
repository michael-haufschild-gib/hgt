import GaloisForLFunctions.HTGeometry.ObserverJacobianActiveMinorGaussianLaw

/-!
# Active-minor probabilities for observer volume

Diagonal spectral responses scale rows of an observer. Cauchy--Binet retains
every active minor, so volume can be controlled geometrically without choosing
one minor or paying the number of row subsets.
-/

open scoped BigOperators

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- Rowwise response of a fixed real observer. -/
def scaleObserverRows {N v : ℕ} (J : Fin N → Fin v → ℝ)
    (g : Fin N → ℝ) : Fin N → Fin v → ℝ :=
  fun a i => g a * J a i

/-- Cauchy--Binet weights normalized by the unscaled observer volume. -/
def observerActiveMinorWeight {N v : ℕ} (J : Fin N → Fin v → ℝ)
    (s : Set.powersetCard (Fin N) v) : ℝ :=
  observerActiveMinor J s ^ 2 / (observerJacobianGram J).det

theorem observerActiveMinor_scaleObserverRows {N v : ℕ}
    (J : Fin N → Fin v → ℝ) (g : Fin N → ℝ)
    (s : Set.powersetCard (Fin N) v) :
    observerActiveMinor (scaleObserverRows J g) s =
      (∏ j : Fin v, g (Set.powersetCard.ofFinEmbEquiv.symm s j)) *
        observerActiveMinor J s := by
  rw [observerActiveMinor_eq_det_activeMatrix,
    observerActiveMinor_eq_det_activeMatrix]
  have hmatrix : observerActiveMatrix (scaleObserverRows J g) s =
      observerActiveMatrix J s *
        Matrix.diagonal (fun j => g (Set.powersetCard.ofFinEmbEquiv.symm s j)) := by
    ext i j
    simp only [observerActiveMatrix, scaleObserverRows, Matrix.of_apply,
      Matrix.mul_diagonal]
    exact mul_comm _ _
  rw [hmatrix, Matrix.det_mul, Matrix.det_diagonal, mul_comm]

theorem observerActiveMinorWeight_nonneg {N v : ℕ}
    (J : Fin N → Fin v → ℝ) (s : Set.powersetCard (Fin N) v) :
    0 ≤ observerActiveMinorWeight J s :=
  div_nonneg (sq_nonneg _) (det_observerJacobianGram_nonneg J)

theorem sum_observerActiveMinorWeight {N v : ℕ}
    (J : Fin N → Fin v → ℝ) (hJ : (observerJacobianGram J).det ≠ 0) :
    ∑ s, observerActiveMinorWeight J s = 1 := by
  simp only [observerActiveMinorWeight, ← Finset.sum_div,
    ← det_observerJacobianGram_eq_sum_activeMinor_sq, div_self hJ]

/-- Normalized squared volume is the arithmetic mean of all squared minor
responses under the unscaled Cauchy--Binet probability law. -/
theorem det_scaleObserverRows_div_eq_weighted_minor_response {N v : ℕ}
    (J : Fin N → Fin v → ℝ) (g : Fin N → ℝ) :
    (observerJacobianGram (scaleObserverRows J g)).det /
        (observerJacobianGram J).det =
      ∑ s : Set.powersetCard (Fin N) v,
        observerActiveMinorWeight J s *
          (∏ j : Fin v, g (Set.powersetCard.ofFinEmbEquiv.symm s j)) ^ 2 := by
  rw [det_observerJacobianGram_eq_sum_activeMinor_sq, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro s _
  rw [observerActiveMinor_scaleObserverRows]
  simp only [observerActiveMinorWeight, mul_pow]
  ring

/-- Keeping all minors removes the combinatorial loss of selecting just one. -/
theorem weighted_geometric_minor_response_le_det_ratio {N v : ℕ}
    (J : Fin N → Fin v → ℝ) (hJ : (observerJacobianGram J).det ≠ 0)
    (g : Fin N → ℝ) :
    (∏ s : Set.powersetCard (Fin N) v,
      ((∏ j : Fin v, g (Set.powersetCard.ofFinEmbEquiv.symm s j)) ^ 2) ^
        observerActiveMinorWeight J s) ≤
      (observerJacobianGram (scaleObserverRows J g)).det /
        (observerJacobianGram J).det := by
  rw [det_scaleObserverRows_div_eq_weighted_minor_response]
  exact Real.geom_mean_le_arith_mean_weighted Finset.univ
    (observerActiveMinorWeight J)
    (fun s => (∏ j : Fin v, g (Set.powersetCard.ofFinEmbEquiv.symm s j)) ^ 2)
    (fun s _ => observerActiveMinorWeight_nonneg J s)
    (sum_observerActiveMinorWeight J hJ) (fun s _ => sq_nonneg _)

/-- Probability assigned to one row occurrence in a random active minor. -/
def observerVolumeIncidenceWeight {N v : ℕ}
    (J : Fin N → Fin v → ℝ)
    (a : Set.powersetCard (Fin N) v × Fin v) : ℝ :=
  observerActiveMinorWeight J a.1 / v

theorem observerVolumeIncidenceWeight_nonneg {N v : ℕ}
    (J : Fin N → Fin v → ℝ)
    (a : Set.powersetCard (Fin N) v × Fin v) :
    0 ≤ observerVolumeIncidenceWeight J a :=
  div_nonneg (observerActiveMinorWeight_nonneg J a.1) (Nat.cast_nonneg v)

theorem sum_observerVolumeIncidenceWeight {N v : ℕ}
    (hv : 0 < v) (J : Fin N → Fin v → ℝ)
    (hJ : (observerJacobianGram J).det ≠ 0) :
    ∑ a, observerVolumeIncidenceWeight J a = 1 := by
  have hvR : (v : ℝ) ≠ 0 := by exact_mod_cast hv.ne'
  rw [Fintype.sum_prod_type]
  have hinner (s : Set.powersetCard (Fin N) v) :
      (∑ j : Fin v, observerVolumeIncidenceWeight J (s, j)) =
        observerActiveMinorWeight J s := by
    simp only [observerVolumeIncidenceWeight, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    field_simp
  simp_rw [hinner]
  exact sum_observerActiveMinorWeight J hJ

/-- Average log response under the active-minor row-occurrence law. -/
def observerVolumeLogResponse {N v : ℕ}
    (J : Fin N → Fin v → ℝ) (g : Fin N → ℝ) : ℝ :=
  ∑ a : Set.powersetCard (Fin N) v × Fin v,
    observerVolumeIncidenceWeight J a *
      Real.log (g (Set.powersetCard.ofFinEmbEquiv.symm a.1 a.2))

theorem mul_observerVolumeLogResponse {N v : ℕ}
    (hv : 0 < v) (J : Fin N → Fin v → ℝ) (g : Fin N → ℝ) :
    (v : ℝ) * observerVolumeLogResponse J g =
      ∑ s : Set.powersetCard (Fin N) v,
        observerActiveMinorWeight J s *
          ∑ j : Fin v, Real.log (g (Set.powersetCard.ofFinEmbEquiv.symm s j)) := by
  have hvR : (v : ℝ) ≠ 0 := by exact_mod_cast hv.ne'
  simp only [observerVolumeLogResponse, Fintype.sum_prod_type,
    observerVolumeIncidenceWeight, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro s _
  apply Finset.sum_congr rfl
  intro j _
  field_simp

/-- The normalized observer volume dominates the geometric mean of its
spectral row responses. There is no active-minor counting factor. -/
theorem exp_observerVolumeLogResponse_le_det_ratio {N v : ℕ}
    (hv : 0 < v) (J : Fin N → Fin v → ℝ)
    (hJ : (observerJacobianGram J).det ≠ 0)
    (g : Fin N → ℝ) (hg : ∀ a, 0 < g a) :
    Real.exp (2 * (v : ℝ) * observerVolumeLogResponse J g) ≤
      (observerJacobianGram (scaleObserverRows J g)).det /
        (observerJacobianGram J).det := by
  let z : Set.powersetCard (Fin N) v → ℝ := fun s =>
    (∏ j : Fin v, g (Set.powersetCard.ofFinEmbEquiv.symm s j)) ^ 2
  have hz (s : Set.powersetCard (Fin N) v) : 0 < z s :=
    sq_pos_of_pos (Finset.prod_pos fun j _ => hg _)
  have hjensen := convexOn_exp.map_sum_le
    (t := Finset.univ) (w := observerActiveMinorWeight J)
    (p := fun s => Real.log (z s))
    (fun s _ => observerActiveMinorWeight_nonneg J s)
    (sum_observerActiveMinorWeight J hJ)
    (fun s _ => Set.mem_univ (Real.log (z s)))
  simp only [smul_eq_mul, Real.exp_log (hz _)] at hjensen
  have hlogs :
      (∑ s, observerActiveMinorWeight J s * Real.log (z s)) =
        2 * ((v : ℝ) * observerVolumeLogResponse J g) := by
    rw [mul_observerVolumeLogResponse hv, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro s _
    rw [show Real.log (z s) = 2 *
        ∑ j : Fin v, Real.log (g (Set.powersetCard.ofFinEmbEquiv.symm s j)) by
      change Real.log ((∏ j : Fin v,
        g (Set.powersetCard.ofFinEmbEquiv.symm s j)) ^ 2) = _
      rw [Real.log_pow, Real.log_prod (fun j _ => (hg _).ne')]
      norm_num]
    ring
  rw [hlogs] at hjensen
  simpa only [← mul_assoc, det_scaleObserverRows_div_eq_weighted_minor_response,
    z] using hjensen

end

end GaloisForLFunctions.HTGeometry


