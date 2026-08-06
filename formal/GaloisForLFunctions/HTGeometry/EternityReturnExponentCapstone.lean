import GaloisForLFunctions.HTGeometry.PresentedOrbitDimensionEternity
import GaloisForLFunctions.HTGeometry.IntegerTorusReturnVolume
import GaloisForLFunctions.HTGeometry.FrequencyLatticeBasis
import GaloisForLFunctions.HTGeometry.AnchoredProjectiveReturnDensityLaw

/-!
# Every local return exponent inside every Hamiltonian neighbourhood

The gaps of a finite spectrum are integer combinations of a rationally independent frequency basis,
and the integer matrix expressing them has an integer left inverse.  Its rows therefore span the
rational coordinate space of the basis, which is exactly the hypothesis the return-volume law needs:
the pulled-back anchored return target on the presenting torus has Haar volume of order `ε` to the
presenting dimension, so the logarithmic return exponent is that dimension.

Combined with the commuting perturbation of prescribed temporal dimension, every Hamiltonian has,
inside every uniform bounded-horizon tube, a neighbour whose local return exponent is any
prescribed value `1, …, D-1`.
-/

open Filter MeasureTheory Set Topology
open scoped Matrix Matrix.Norms.L2Operator BigOperators

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- Integer rows with an integer left inverse span the rational coordinate space. -/
theorem span_rows_eq_top_of_leftInverse {d : Type*} [Fintype d] {k : Type*} [Fintype k]
    [DecidableEq k] (M : d → k → ℤ) (A : k → d → ℤ)
    (hA : ∀ j j', (∑ i, A j i * M i j') = if j = j' then 1 else 0) :
    Submodule.span ℚ (Set.range fun i : d => ((fun j => (M i j : ℚ)) : k → ℚ)) = ⊤ := by
  classical
  set S : Set (k → ℚ) := Set.range fun i : d => ((fun j => (M i j : ℚ)) : k → ℚ) with hS
  have hsingle : ∀ j : k, (Pi.single j (1 : ℚ) : k → ℚ) ∈ Submodule.span ℚ S := by
    intro j
    have hsum : (Pi.single j (1 : ℚ) : k → ℚ)
        = ∑ i : d, (A j i : ℚ) • ((fun j' => (M i j' : ℚ)) : k → ℚ) := by
      funext j'
      have hval : (∑ i : d, (A j i : ℚ) • ((fun j' => (M i j' : ℚ)) : k → ℚ)) j'
          = ((∑ i : d, A j i * M i j' : ℤ) : ℚ) := by
        push_cast
        simp [Finset.sum_apply]
      rw [hval, hA j j', Pi.single_apply]
      by_cases hjj : j = j'
      · subst hjj
        simp
      · rw [if_neg hjj, if_neg (fun h => hjj h.symm)]
        norm_num
    rw [hsum]
    refine Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ ?_
    exact Submodule.subset_span ⟨i, rfl⟩
  refine Submodule.eq_top_iff'.mpr fun x => ?_
  have hx : x = ∑ j : k, x j • (Pi.single j (1 : ℚ) : k → ℚ) := by
    funext j'
    have hval : (∑ j : k, x j • (Pi.single j (1 : ℚ) : k → ℚ)) j'
        = ∑ j : k, x j * (Pi.single j (1 : ℚ) : k → ℚ) j' := by
      simp [Finset.sum_apply]
    rw [hval]
    rw [Finset.sum_eq_single j']
    · simp
    · intro j _ hj
      rw [Pi.single_apply, if_neg (fun h => hj h.symm), mul_zero]
    · intro hj
      exact absurd (Finset.mem_univ j') hj
  rw [hx]
  exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (hsingle j)

variable {n : ℕ}

/-- **Corollary 3: every Hamiltonian neighbourhood contains every local return exponent.**  For
every prescribed temporal dimension `k` and every uniform bounded-horizon tube, a commuting
simple-spectrum Hermitian neighbour has its gaps presented by an integer character matrix over a
`k`-dimensional frequency basis, and the pulled-back anchored return target on the presenting torus
has logarithmic Haar exponent exactly `k`. -/
theorem exists_isHermitian_commuting_returnExponent_uniform_horizon {k : ℕ} (hk : 0 < k)
    (hkn : k ≤ n) (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) (hA : A.IsHermitian) {T η : ℝ}
    (hT : 0 < T) (hη : 0 < η) :
    ∃ (B : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) (E' : Fin (n + 1) → ℝ) (gamma : Fin k → ℝ)
      (M : Fin n → Fin k → ℤ),
      B.IsHermitian ∧ B * A = A * B ∧ Function.Injective E' ∧
        (∀ t : ℝ, |t| ≤ T → ‖unitaryEvolution B t - unitaryEvolution A t‖ < η) ∧
        (∀ i : Fin n, E' i.succ - E' 0 = ∑ j, (M i j : ℝ) * gamma j) ∧
        Tendsto (fun ε : ℝ => Real.log
            ((finiteTorusHaarProbabilityMeasure (Fin k) : Measure (UnitAddTorus (Fin k)))
              (integerReturnPreimage M ε)).toReal / Real.log ε)
          (𝓝[>] 0) (𝓝 (k : ℝ)) := by
  obtain ⟨B, E', hherm, hcomm, hinj, hconj, hrank, hclose⟩ :=
    exists_isHermitian_commuting_gapRank_uniform_horizon hk hkn A hA hT hη
  obtain ⟨k', gamma, M, Aint, -, -, -, hM, hAM, hk'⟩ :=
    exists_frequency_integer_basis (fun i : Fin n => E' i.succ - E' 0)
  have hkk : k' = k := hk'.trans hrank
  subst hkk
  refine ⟨B, E', gamma, M, hherm, hcomm, hinj, hclose, hM, ?_⟩
  have hspan := span_rows_eq_top_of_leftInverse M Aint hAM
  simpa using tendsto_log_integerReturnPreimage_div_log_of_span M hspan

/-! ### The maximal-rank exact return law -/

/-- A square integer matrix with an integer left inverse is nonsingular. -/
theorem det_ne_zero_of_leftInverse {k : ℕ} (M : Fin k → Fin k → ℤ) (A : Fin k → Fin k → ℤ)
    (hA : ∀ j j', (∑ i, A j i * M i j') = if j = j' then 1 else 0) :
    (Matrix.of M).det ≠ 0 := by
  have hmul : (Matrix.of A) * (Matrix.of M) = 1 := by
    ext j j'
    rw [Matrix.mul_apply, Matrix.one_apply]
    simpa using hA j j'
  intro hdet
  have hone : (1 : ℤ) = 0 := by
    have h := congrArg Matrix.det hmul
    rw [Matrix.det_mul, hdet, mul_zero, Matrix.det_one] at h
    exact h.symm
  exact one_ne_zero hone

/-- **Corollary 3 `(6)` for a maximal-rank neighbour.**  At maximal temporal dimension the presenting
character matrix is unimodular, so the pulled-back anchored chord target keeps the exact
coordinate-torus law: its Haar measure is `(2 arcsin(ε/2)/π)` to the number of gaps. -/
theorem exists_isHermitian_commuting_maximalReturnLaw_uniform_horizon (hn : 0 < n)
    (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) (hA : A.IsHermitian) {T η : ℝ}
    (hT : 0 < T) (hη : 0 < η) :
    ∃ (B : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) (E' : Fin (n + 1) → ℝ) (gamma : Fin n → ℝ)
      (M : Fin n → Fin n → ℤ),
      B.IsHermitian ∧ B * A = A * B ∧ Function.Injective E' ∧
        (∀ t : ℝ, |t| ≤ T → ‖unitaryEvolution B t - unitaryEvolution A t‖ < η) ∧
        (∀ i : Fin n, E' i.succ - E' 0 = ∑ j, (M i j : ℝ) * gamma j) ∧
        ∀ ε : ℝ, 0 ≤ ε → ε < 2 →
          (finiteTorusHaarProbabilityMeasure (Fin n) :
              MeasureTheory.Measure (UnitAddTorus (Fin n)))
              (torusIntegerHom M ⁻¹' anchoredProjectiveReturnTarget ε)
            = ENNReal.ofReal (2 * Real.arcsin (ε / 2) / Real.pi) ^ n := by
  obtain ⟨B, E', hherm, hcomm, hinj, hconj, hrank, hclose⟩ :=
    exists_isHermitian_commuting_gapRank_uniform_horizon (k := n) hn (le_refl n) A hA hT hη
  obtain ⟨k', gamma, M, Aint, -, -, -, hM, hAM, hk'⟩ :=
    exists_frequency_integer_basis (fun i : Fin n => E' i.succ - E' 0)
  have hkk : k' = n := hk'.trans hrank
  subst hkk
  have hdet : (Matrix.of M).det ≠ 0 := det_ne_zero_of_leftInverse M Aint hAM
  refine ⟨B, E', gamma, M, hherm, hcomm, hinj, hclose, hM, fun ε hε0 hε2 => ?_⟩
  have hmeas : MeasurableSet (anchoredProjectiveReturnTarget (d := Fin k') ε) :=
    (isClosed_anchoredProjectiveReturnTarget ε).measurableSet
  have h : (finiteTorusHaarProbabilityMeasure (Fin k') :
        MeasureTheory.Measure (UnitAddTorus (Fin k')))
        (torusIntegerHom M ⁻¹' anchoredProjectiveReturnTarget ε)
      = (finiteTorusHaarProbabilityMeasure (Fin k') :
        MeasureTheory.Measure (UnitAddTorus (Fin k'))) (anchoredProjectiveReturnTarget ε) :=
    measure_preimage_torusIntegerHom (N := Matrix.of M) hdet hmeas
  rw [h, finiteTorusHaarProbabilityMeasure_anchoredProjectiveReturnTarget hε0 hε2,
    Fintype.card_fin]

end

end GaloisForLFunctions.HTGeometry
