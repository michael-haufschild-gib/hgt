import GaloisForLFunctions.CriticalArithmeticCorrelationTheory.MacroscopicOverlapSpectralAssembly

/-!
# Finite Ramanujan coordinates transfer spectral floors

A family of symmetric matrices is spectrally confined when each bounded-energy unit vector
has a fixed positive amount of mass in finitely many Ramanujan coordinates. If those vectors
are also norm quasimodes, every strict lower bound for their limiting energies transfers to
the entire matrix. The argument applies to linear combinations of the prime and complete Weil
operators, even when their individual spectral projections do not commute.
-/

noncomputable section
open Filter Topology Finset
open scoped RealInnerProductSpace

namespace GaloisForLFunctions.CriticalArithmeticCorrelationTheory
open RenormalizedArithmeticPotentialTheory

private theorem finite_matrix_residuals_small
    {A : (N : ℕ) → Matrix (PrimeHorizonIndex N) (PrimeHorizonIndex N) ℝ} {E : ℕ → ℝ}
    (hq : ∀ m : ℕ, 0 < m → Tendsto (fun N : ℕ =>
      ‖Matrix.toEuclideanLin (A N) (normalizedRamanujanHorizonVector m N) -
        E m • normalizedRamanujanHorizonVector m N‖) atTop (𝓝 0))
    {ε : ℝ} (hε : 0 < ε) (S : Finset ℕ) (hS : ∀ m ∈ S, 0 < m) :
    ∀ᶠ N : ℕ in atTop, ∀ m ∈ S,
      ‖Matrix.toEuclideanLin (A N) (normalizedRamanujanHorizonVector m N) -
        E m • normalizedRamanujanHorizonVector m N‖ ≤ ε := by
  induction S using Finset.induction_on with
  | empty => exact Eventually.of_forall fun N m hm => False.elim (notMem_empty m hm)
  | @insert m S _ ih =>
      filter_upwards [(hq m (hS m (mem_insert_self m S))).eventually (ge_mem_nhds hε),
        ih fun k hk => hS k (mem_insert_of_mem hk)] with N hmN hSN
      intro k hk
      rcases mem_insert.mp hk with rfl | hkS
      · exact hmN
      · exact hSN k hkS

/-- Finite coordinate capture excludes every eigenvalue strictly below the quasimode floor. -/
theorem eventually_matrix_energy_ge_of_ramanujan_certificates
    {A : (N : ℕ) → Matrix (PrimeHorizonIndex N) (PrimeHorizonIndex N) ℝ}
    (hA : ∀ N, (A N).IsHermitian) {E : ℕ → ℝ}
    (hq : ∀ m : ℕ, 0 < m → Tendsto (fun N : ℕ =>
      ‖Matrix.toEuclideanLin (A N) (normalizedRamanujanHorizonVector m N) -
        E m • normalizedRamanujanHorizonVector m N‖) atTop (𝓝 0))
    {e b : ℝ} (hfloor : ∀ m : ℕ, 0 < m → e ≤ E m) (hb : b < e)
    (hcert : ∃ S : Finset ℕ, (∀ m ∈ S, 0 < m) ∧
      ∀ᶠ N : ℕ in atTop, ∀ x : EuclideanSpace ℝ (PrimeHorizonIndex N),
        ‖x‖ = 1 → ⟪Matrix.toEuclideanLin (A N) x, x⟫ ≤ b →
          1 / 18 ≤ ∑ m ∈ S, ⟪x, normalizedRamanujanHorizonVector m N⟫ ^ 2) :
    ∀ᶠ N : ℕ in atTop, ∀ x : EuclideanSpace ℝ (PrimeHorizonIndex N),
      b * ‖x‖ ^ 2 ≤ ⟪Matrix.toEuclideanLin (A N) x, x⟫ := by
  let δ := e - b
  have hδ : 0 < δ := sub_pos.mpr hb
  obtain ⟨S, hS, hc⟩ := hcert
  let ε := δ / (6 * ((S.card : ℝ) + 1))
  have hcard : 0 ≤ (S.card : ℝ) := Nat.cast_nonneg _
  have hε : 0 < ε := div_pos hδ (by positivity)
  have hcost : (S.card : ℝ) * ε ^ 2 / δ ^ 2 < 1 / 18 := by
    have heq : (S.card : ℝ) * ε ^ 2 / δ ^ 2 =
        (S.card : ℝ) / (36 * ((S.card : ℝ) + 1) ^ 2) := by
      dsimp only [ε]
      field_simp [hδ.ne', show (S.card : ℝ) + 1 ≠ 0 by positivity]
      ring
    rw [heq, div_lt_iff₀ (by positivity)]
    nlinarith only [hcard, sq_nonneg (S.card : ℝ)]
  filter_upwards [hc, finite_matrix_residuals_small hq hε S hS] with N hcN hrN
  have heigen : ∀ i, b ≤ (hA N).eigenvalues i := by
    intro i
    by_contra hi
    have hi' : (hA N).eigenvalues i < b := lt_of_not_ge hi
    let x := (hA N).eigenvectorBasis i
    have hnorm : ‖x‖ = 1 := by
      have h : ⟪x, x⟫ = (1 : ℝ) := by
        simpa only [ite_true] using
          (orthonormal_iff_ite.mp (hA N).eigenvectorBasis.orthonormal) i i
      rw [real_inner_self_eq_norm_sq] at h
      nlinarith only [h, norm_nonneg x]
    have hlo : ∀ j, b ≤ (hA N).eigenvalues j → ⟪x, (hA N).eigenvectorBasis j⟫ = 0 := by
      intro j hj
      have hij : i ≠ j := by
        intro hij
        subst j
        exact (not_le_of_gt hi') hj
      simpa only [if_neg hij] using
        (orthonormal_iff_ite.mp (hA N).eigenvectorBasis.orthonormal) i j
    have henergy : ⟪Matrix.toEuclideanLin (A N) x, x⟫ ≤ b := by
      simpa only [hnorm, one_pow, mul_one] using
        HTGeometry.hermitianEnergy_le_of_support (hA N) b x hlo
    have hmass := hcN x hnorm henergy
    have hsum : (∑ m ∈ S, ⟪x, normalizedRamanujanHorizonVector m N⟫ ^ 2) ≤
        (S.card : ℝ) * ε ^ 2 / δ ^ 2 := by
      have hterm : ∀ m ∈ S,
          ⟪x, normalizedRamanujanHorizonVector m N⟫ ^ 2 ≤ ε ^ 2 / δ ^ 2 := by
        intro m hm
        have hE := hfloor m (hS m hm)
        have hgap : δ ≤ E m - b := by dsimp only [δ]; linarith only [hE]
        have hgt : b < E m := by linarith only [hgap, hδ]
        have hlow := HTGeometry.inner_sq_le_residual_sq_div_upper_gap_sq (hA N) b (E m)
          hgt x (normalizedRamanujanHorizonVector m N) hnorm hlo
        have hrsq := mul_self_le_mul_self (norm_nonneg _) (hrN m hm)
        have hgsq := mul_self_le_mul_self hδ.le hgap
        rw [← sq, ← sq] at hrsq hgsq
        calc
          _ ≤ _ := hlow
          _ ≤ ε ^ 2 / (E m - b) ^ 2 := div_le_div_of_nonneg_right hrsq (sq_nonneg _)
          _ ≤ ε ^ 2 / δ ^ 2 :=
            div_le_div_of_nonneg_left (sq_nonneg ε) (sq_pos_of_pos hδ) hgsq
      simpa only [sum_const, nsmul_eq_mul, mul_div_assoc] using sum_le_sum hterm
    linarith only [hmass, hsum, hcost]
  intro x
  rw [HTGeometry.hermitianEnergy_eq_sum (hA N),
    ← (hA N).eigenvectorBasis.sum_sq_inner_left x, mul_sum]
  exact sum_le_sum fun i _ => mul_le_mul_of_nonneg_right (heigen i) (sq_nonneg _)

#print axioms eventually_matrix_energy_ge_of_ramanujan_certificates

end GaloisForLFunctions.CriticalArithmeticCorrelationTheory
