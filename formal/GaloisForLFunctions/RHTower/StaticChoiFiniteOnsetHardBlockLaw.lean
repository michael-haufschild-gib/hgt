import GaloisForLFunctions.RHTower.StaticChoiForwardSpectralDimensionLaw
import GaloisForLFunctions.RHTower.StaticChoiQuantitativeHardGapLaw

open scoped BigOperators
open Set GaloisForLFunctions.HTGeometry

noncomputable section

namespace RHTower

/-- A positive (not shift-invariant) speed scale for the full spectral Choi representative. -/
def staticChoiSpeed {d : ℕ} (energy : Fin d → ℝ) : ℝ :=
  (∑ i, |energy i|) + 1

theorem staticChoiSpeed_pos {d : ℕ} (energy : Fin d → ℝ) :
    0 < staticChoiSpeed energy := by
  unfold staticChoiSpeed
  positivity

/-- Hilbert-space speed bound for the normalized full spectral Choi representative. -/
theorem norm_staticSpectralChoiVector_time_sub_le
    {d : ℕ} (hd : 0 < d) (energy : Fin d → ℝ) (t u : ℝ) :
    ‖staticSpectralChoiVector d t energy - staticSpectralChoiVector d u energy‖ ≤
      staticChoiSpeed energy * |t - u| := by
  let S := staticChoiSpeed energy
  have hS : 0 < S := staticChoiSpeed_pos energy
  have hphase (i : Fin d) :
      ‖finiteObserverHamiltonianVertexPhase t energy i -
          finiteObserverHamiltonianVertexPhase u energy i‖ ≤ S * |t - u| := by
    unfold finiteObserverHamiltonianVertexPhase
    have hbase := norm_exp_ofReal_mul_I_sub_le (t * energy i) (u * energy i)
    have hi : |energy i| ≤ S := by
      have hsum : |energy i| ≤ ∑ j, |energy j| :=
        Finset.single_le_sum (fun j _ => abs_nonneg (energy j)) (Finset.mem_univ i)
      dsimp [S, staticChoiSpeed]
      linarith
    have hbound : |t * energy i - u * energy i| ≤ S * |t - u| := by
      rw [show t * energy i - u * energy i = (t - u) * energy i by ring,
        abs_mul, mul_comm]
      exact mul_le_mul_of_nonneg_right hi (abs_nonneg _)
    simpa [mul_comm] using hbase.trans hbound
  have hR : 0 ≤ S * |t - u| := mul_nonneg hS.le (abs_nonneg _)
  rw [← sq_le_sq₀ (norm_nonneg _) hR]
  rw [EuclideanSpace.norm_sq_eq, Fintype.sum_prod_type]
  have hrow (i : Fin d) :
      (∑ j : Fin d,
        ‖(staticSpectralChoiVector d t energy -
            staticSpectralChoiVector d u energy).ofLp (i, j)‖ ^ 2) ≤
        (S * |t - u|) ^ 2 / d := by
    rw [Finset.sum_eq_single i]
    · simp only [PiLp.sub_apply, staticSpectralChoiVector,
        fullUniformPhaseChoiVector_apply, if_pos]
      rw [fourier_finiteHamiltonianAddCirclePhase,
        fourier_finiteHamiltonianAddCirclePhase, ← mul_sub, norm_mul, mul_pow]
      have hdR : (0 : ℝ) < d := by exact_mod_cast hd
      rw [norm_inv, Complex.norm_real, Real.norm_of_nonneg (Real.sqrt_nonneg _),
        inv_pow, Real.sq_sqrt hdR.le, div_eq_inv_mul]
      have hp := hphase i
      have hsq := (sq_le_sq₀ (norm_nonneg _) hR).2 hp
      have hDinv : 0 ≤ (d : ℝ)⁻¹ := by positivity
      simpa using mul_le_mul_of_nonneg_left hsq hDinv
    · intro j _ hji
      simp [staticSpectralChoiVector, fullUniformPhaseChoiVector_apply, Ne.symm hji]
    · simp
  calc
    (∑ i : Fin d, ∑ j : Fin d,
      ‖(staticSpectralChoiVector d t energy -
          staticSpectralChoiVector d u energy).ofLp (i, j)‖ ^ 2)
      ≤ ∑ _i : Fin d, (S * |t - u|) ^ 2 / d :=
        Finset.sum_le_sum fun i _ => hrow i
    _ = (S * |t - u|) ^ 2 := by
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      field_simp

/-- Pure-state trace distance along a static spectral Choi orbit is Lipschitz in physical time. -/
theorem pureStateTraceDistance_staticSpectralChoiVector_time_le
    {d : ℕ} (hd : 0 < d) (energy : Fin d → ℝ) (t u : ℝ) :
    pureStateTraceDistance (staticSpectralChoiVector d t energy)
        (staticSpectralChoiVector d u energy) ≤
      staticChoiSpeed energy * |t - u| := by
  exact (pureStateTraceDistance_le_norm_sub _ _
    (staticSpectralChoiVector_norm hd t energy)
    (staticSpectralChoiVector_norm hd u energy)).trans
      (norm_staticSpectralChoiVector_time_sub_le hd energy t u)

/-- **Finite-onset continuous hard block.** A finite-window spectral-dimension budget first
produces one forward hard time. The explicit Choi speed thickens it into a continuous hard block
against the complete padded circuit dictionary, beginning no later than `2T`. -/
theorem exists_forward_pureChoiCircuitHardBlock_of_spectralDimensionBudget
    {d : ℕ} (hd : 0 < d)
    {gate : Type*} [Fintype gate] {energy : Fin d → ℝ}
    (hmax : MaximallyProjectiveEnergy energy)
    (s : ℕ)
    (target : PaddedCircuitWord gate s → EuclideanSpace ℂ (Fin d × Fin d))
    (htarget : ∀ w, ‖target w‖ = 1)
    (n : ℕ) (hn : 0 < n) {T δ epsn epsw : ℝ}
    (hT : 0 < T) (hδ : 0 < δ) (hepsn : 0 ≤ epsn)
    (hgap : epsn < epsw) (hepswOne : epsw ≤ 1)
    (hbudget :
      (Fintype.card gate : ℝ) ^ (s + 1) *
          ((n.factorial : ℝ) * (d : ℝ)⁻¹ ^ n +
            (((2 * n + 1) ^ replicaNearActionRank energy n δ : ℕ) : ℝ) *
              ((n.factorial : ℝ) * (d : ℝ)⁻¹ ^ n) +
            min 1 (T * δ)⁻¹) <
        (1 - epsw ^ 2) ^ n) :
    ∃ u ∈ Set.Ioc 0 (2 * T),
      ∀ t ∈ Set.Icc u (u + (epsw - epsn) / staticChoiSpeed energy),
        ∀ w, epsn < pureStateTraceDistance
          (staticSpectralChoiVector d t energy) (target w) := by
  have hepsw : 0 ≤ epsw := le_trans hepsn (le_of_lt hgap)
  obtain ⟨u, hu, hhard⟩ :=
    exists_forward_directAdaptivePaddedCircuitHardTime_of_spectralDimensionBudget
      hd hmax s target htarget n hn hT hδ hepsw hepswOne hbudget
  refine ⟨u, hu, ?_⟩
  intro t ht w
  have hfar : epsw < pureStateTraceDistance
      (staticSpectralChoiVector d u energy) (target w) := by
    simpa [staticChoiTargetCaptureSet] using hhard w
  have hspeed : 0 < staticChoiSpeed energy := staticChoiSpeed_pos energy
  have htu : |t - u| = t - u := abs_of_nonneg (sub_nonneg.mpr ht.1)
  have hmove : pureStateTraceDistance
      (staticSpectralChoiVector d u energy)
      (staticSpectralChoiVector d t energy) ≤ epsw - epsn := by
    refine (pureStateTraceDistance_staticSpectralChoiVector_time_le hd energy u t).trans ?_
    rw [abs_sub_comm, htu]
    have hlen : t - u ≤ (epsw - epsn) / staticChoiSpeed energy := by linarith [ht.2]
    rw [le_div_iff₀ hspeed] at hlen
    nlinarith
  have htri := pureStateTraceDistance_triangle
    (staticSpectralChoiVector d u energy)
    (staticSpectralChoiVector d t energy)
    (target w)
    (staticSpectralChoiVector_norm hd u energy)
    (staticSpectralChoiVector_norm hd t energy)
    (htarget w)
  nlinarith

end RHTower
