import GaloisForLFunctions.CompletedArithmeticForms.GammaSuccessorReserve
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspAllRankNativeTail

/-!
# Quantitative successor reserve of the complete native theta tail

The balanced complete source has an explicit positive Schur limit at every fixed rank
and shift. The constant is the exact Gamma-model successor payment. A cofinal factor-two
lower bound follows with the literal infinite theta remainder retained. The threshold
depends on rank and shift; compact-source compensation remains a separate obligation.
-/

noncomputable section

open Finset Matrix Filter Topology

namespace GaloisForLFunctions.CompletedArithmeticForms

open HTGeometry _root_.RHTower _root_.RHTower.ThetaCuspGaussianLimit

/-- Actual native signed moments in the first-atom mass and Gaussian scale coordinates. -/
def nativeBalancedMoment (s : ℕ) (x : ℝ) (k : ℕ) : ℝ :=
  thetaCuspNativeScaledEvenJet (k + s) x

/-- Exact Schur reserve of the balanced complete source, including its mixed head entries. -/
def nativeBalancedSuccessor (N s : ℕ) (x : ℝ) : ℝ :=
  finiteHankelSuccessorSchur (nativeBalancedMoment s x) N

/-- The all-order limiting reserve, with factorial growth and its exact shift dependence. -/
def nativeGammaReserve (N s : ℕ) : ℝ :=
  gaussianMoment s * (16 : ℝ) ^ (2 * N) * (N.factorial : ℝ) *
    gammaShapeMoment ((s : ℝ) + 1 / 2) N

private theorem gaussianMoment_shift (s k : ℕ) :
    gaussianMoment (k + s) =
      scaledGammaMoment (gaussianMoment s) 16 ((s : ℝ) + 1 / 2) k := by
  rw [Nat.add_comm k s]
  simp only [gaussianMoment, scaledGammaMoment, pow_add, gammaShapeMoment_add]
  rw [add_comm (1 / 2 : ℝ) (s : ℝ)]
  ring

private theorem gaussianMoment_pos' (s : ℕ) : 0 < gaussianMoment s := by
  exact mul_pos (pow_pos (by positivity) s) (gammaShapeMoment_pos (by positivity) s)

theorem nativeGammaReserve_pos (N s : ℕ) : 0 < nativeGammaReserve N s := by
  have hg := gaussianMoment_pos' s
  have hf : (0 : ℝ) < (N.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos N
  have hr := gammaShapeMoment_pos (show (0 : ℝ) < (s : ℝ) + 1 / 2 by positivity) N
  unfold nativeGammaReserve
  positivity

/-- Every balanced complete-source entry tends to its literal scaled Gamma moment. -/
theorem nativeBalancedMoment_tendsto (s k : ℕ) :
    Tendsto (fun x : ℝ => nativeBalancedMoment s x k) atTop
      (𝓝 (scaledGammaMoment (gaussianMoment s) 16 ((s : ℝ) + 1 / 2) k)) := by
  simpa only [nativeBalancedMoment, profile_signed_even_jet, gaussianMoment_shift] using
    native_scaled_jet_tendsto (k + s)

private theorem nativeBalancedHead_posDef_eventually (N s : ℕ) :
    ∀ᶠ x : ℝ in atTop, (finiteHankelMatrix (nativeBalancedMoment s x) N).PosDef := by
  have hh (x : ℝ) : (finiteHankelMatrix (nativeBalancedMoment s x) N).IsHermitian := by
    rw [Matrix.IsHermitian]
    ext i j
    simp [finiteHankelMatrix, add_comm]
  apply posDef_eventually_of_tendsto
    (scaledGammaHankel_posDef (gaussianMoment_pos' s)
      (show (0 : ℝ) < 16 by positivity)
      (show (0 : ℝ) < (s : ℝ) + 1 / 2 by positivity) N)
    (Filter.Eventually.of_forall hh)
  intro i j
  exact nativeBalancedMoment_tendsto s (i.val + j.val)

private theorem nativeBalancedHead_det_tendsto (N s : ℕ) :
    Tendsto (fun x : ℝ => (finiteHankelMatrix (nativeBalancedMoment s x) N).det)
      atTop (𝓝 (finiteHankelMatrix
        (scaledGammaMoment (gaussianMoment s) 16 ((s : ℝ) + 1 / 2)) N).det) := by
  have hentry : Tendsto (fun x : ℝ => finiteHankelMatrix (nativeBalancedMoment s x) N) atTop
      (𝓝 (finiteHankelMatrix (scaledGammaMoment (gaussianMoment s) 16 ((s : ℝ) + 1 / 2)) N)) :=
    tendsto_pi_nhds.mpr fun i => tendsto_pi_nhds.mpr fun j =>
      nativeBalancedMoment_tendsto s (i.val + j.val)
  have hc : Continuous (Matrix.det : Matrix (Fin N) (Fin N) ℝ → ℝ) := continuous_id.matrix_det
  exact hc.continuousAt.tendsto.comp hentry

/-- The complete tail retains half the entire Gamma head and spends at most half more. -/
theorem nativeBalancedHead_relative_posDef_eventually (N s : ℕ) :
    let G := finiteHankelMatrix
      (scaledGammaMoment (gaussianMoment s) 16 ((s : ℝ) + 1 / 2)) N
    ∀ᶠ x : ℝ in atTop,
      (finiteHankelMatrix (nativeBalancedMoment s x) N - (1 / 2 : ℝ) • G).PosDef ∧
      ((3 / 2 : ℝ) • G - finiteHankelMatrix (nativeBalancedMoment s x) N).PosDef := by
  let G := finiteHankelMatrix
    (scaledGammaMoment (gaussianMoment s) 16 ((s : ℝ) + 1 / 2)) N
  have hG := scaledGammaHankel_posDef (gaussianMoment_pos' s)
    (show (0 : ℝ) < 16 by positivity) (show (0 : ℝ) < (s : ℝ) + 1 / 2 by positivity) N
  have hhalf : ((1 / 2 : ℝ) • G).PosDef := hG.smul (by positivity)
  have hlo : ∀ᶠ x : ℝ in atTop,
      (finiteHankelMatrix (nativeBalancedMoment s x) N - (1 / 2 : ℝ) • G).PosDef := by
    have hh (x : ℝ) :
        (finiteHankelMatrix (nativeBalancedMoment s x) N - (1 / 2 : ℝ) • G).IsHermitian := by
      rw [Matrix.IsHermitian]
      ext i j
      simp [G, finiteHankelMatrix, add_comm]
    apply posDef_eventually_of_tendsto hhalf (Filter.Eventually.of_forall hh)
    intro i j
    change Tendsto (fun x => nativeBalancedMoment s x (i.val + j.val) -
      (1 / 2 : ℝ) * G i j) atTop (𝓝 ((1 / 2 : ℝ) * G i j))
    have h := (nativeBalancedMoment_tendsto s (i.val + j.val)).sub
      (tendsto_const_nhds (x := (1 / 2 : ℝ) * G i j))
    have he : G i j - (1 / 2 : ℝ) * G i j = (1 / 2 : ℝ) * G i j := by ring
    change Tendsto (fun x => nativeBalancedMoment s x (i.val + j.val) -
      (1 / 2 : ℝ) * G i j) atTop (𝓝 (G i j - (1 / 2 : ℝ) * G i j)) at h
    rwa [he] at h
  have hhi : ∀ᶠ x : ℝ in atTop,
      ((3 / 2 : ℝ) • G - finiteHankelMatrix (nativeBalancedMoment s x) N).PosDef := by
    have hh (x : ℝ) :
        ((3 / 2 : ℝ) • G - finiteHankelMatrix (nativeBalancedMoment s x) N).IsHermitian := by
      rw [Matrix.IsHermitian]
      ext i j
      simp [G, finiteHankelMatrix, add_comm]
    apply posDef_eventually_of_tendsto hhalf (Filter.Eventually.of_forall hh)
    intro i j
    change Tendsto (fun x => (3 / 2 : ℝ) * G i j -
      nativeBalancedMoment s x (i.val + j.val)) atTop (𝓝 ((1 / 2 : ℝ) * G i j))
    have h := (tendsto_const_nhds (x := (3 / 2 : ℝ) * G i j)).sub
      (nativeBalancedMoment_tendsto s (i.val + j.val))
    have he : (3 / 2 : ℝ) * G i j - G i j = (1 / 2 : ℝ) * G i j := by ring
    exact he ▸ h
  exact hlo.and hhi

/-- The complete native successor has the exact Gamma reserve at every fixed order and shift. -/
theorem nativeBalancedSuccessor_tendsto (N s : ℕ) :
    Tendsto (nativeBalancedSuccessor N s) atTop (𝓝 (nativeGammaReserve N s)) := by
  have hhead := scaledGammaHankel_posDef (gaussianMoment_pos' s)
    (show (0 : ℝ) < 16 by positivity) (show (0 : ℝ) < (s : ℝ) + 1 / 2 by positivity) N
  have hmodel :
      (finiteHankelMatrix (scaledGammaMoment (gaussianMoment s) 16 ((s : ℝ) + 1 / 2)) (N + 1)).det /
        (finiteHankelMatrix (scaledGammaMoment (gaussianMoment s) 16 ((s : ℝ) + 1 / 2)) N).det =
          nativeGammaReserve N s := by
    rw [finiteHankelMatrix_succ_det_eq_schur hhead,
      mul_div_cancel_left₀ _ hhead.det_pos.ne',
      scaledGamma_successorSchur (gaussianMoment_pos' s) (by positivity) (by positivity)]
    rfl
  have hlim := (nativeBalancedHead_det_tendsto (N + 1) s).div
    (nativeBalancedHead_det_tendsto N s) hhead.det_pos.ne'
  rw [hmodel] at hlim
  apply hlim.congr'
  filter_upwards [nativeBalancedHead_posDef_eventually N s] with x hx
  change (finiteHankelMatrix (nativeBalancedMoment s x) (N + 1)).det /
    (finiteHankelMatrix (nativeBalancedMoment s x) N).det = nativeBalancedSuccessor N s x
  rw [finiteHankelMatrix_succ_det_eq_schur hx, mul_div_cancel_left₀ _ hx.det_pos.ne']
  rfl

/-- A concrete relative reserve for the literal native tail; the horizon depends on rank and shift. -/
theorem nativeBalancedSuccessor_eventual_bounds (N s : ℕ) :
    ∀ᶠ x : ℝ in atTop,
      nativeGammaReserve N s / 2 ≤ nativeBalancedSuccessor N s x ∧
        nativeBalancedSuccessor N s x ≤ 3 * nativeGammaReserve N s / 2 := by
  have hC := nativeGammaReserve_pos N s
  have hlim := nativeBalancedSuccessor_tendsto N s
  have hlo : nativeGammaReserve N s / 2 < nativeGammaReserve N s := by linarith only [hC]
  have hhi : nativeGammaReserve N s < 3 * nativeGammaReserve N s / 2 := by linarith only [hC]
  filter_upwards [hlim.eventually (lt_mem_nhds hlo), hlim.eventually (gt_mem_nhds hhi)]
    with x hxlo hxhi
  exact ⟨hxlo.le, hxhi.le⟩

/-- The actual tail has an exact relative successor limit, independent of mass and dilation. -/
theorem nativeBalancedSuccessor_relative_tendsto (N s : ℕ) :
    Tendsto (fun x : ℝ => nativeBalancedSuccessor N s x /
        nativeBalancedMoment s x (2 * N)) atTop
      (𝓝 ((N.factorial : ℝ) / gammaShapeMoment ((s : ℝ) + 1 / 2 + N) N)) := by
  have hg := gaussianMoment_pos' s
  have hr : (0 : ℝ) < (s : ℝ) + 1 / 2 := by positivity
  have hm : 0 < scaledGammaMoment (gaussianMoment s) 16 ((s : ℝ) + 1 / 2) (2 * N) := by
    unfold scaledGammaMoment
    exact mul_pos (mul_pos hg (pow_pos (by positivity) _)) (gammaShapeMoment_pos hr _)
  have he : nativeGammaReserve N s /
      scaledGammaMoment (gaussianMoment s) 16 ((s : ℝ) + 1 / 2) (2 * N) =
        (N.factorial : ℝ) / gammaShapeMoment ((s : ℝ) + 1 / 2 + N) N := by
    have h := scaledGamma_successorSchur_div_diagonal hg (show (0 : ℝ) < 16 by positivity) hr N
    rw [scaledGamma_successorSchur hg (by positivity) hr] at h
    exact h
  rw [← he]
  exact (nativeBalancedSuccessor_tendsto N s).div
    (nativeBalancedMoment_tendsto s (2 * N)) hm.ne'

/-- A quantitative degeneration law: the fraction of the new diagonal decreases exponentially. -/
theorem nativeBalancedSuccessor_relative_eventually_le (N s : ℕ) :
    ∀ᶠ x : ℝ in atTop, nativeBalancedSuccessor N s x /
      nativeBalancedMoment s x (2 * N) ≤ 2 * (2 / 3 : ℝ) ^ N := by
  have hbound := gamma_successor_relative_reserve_le
    (show (1 / 2 : ℝ) ≤ (s : ℝ) + 1 / 2 by
      linarith only [(Nat.cast_nonneg s : (0 : ℝ) ≤ s)]) N
  have hpos : (0 : ℝ) < (2 / 3 : ℝ) ^ N := by positivity
  have hstrict : (N.factorial : ℝ) / gammaShapeMoment ((s : ℝ) + 1 / 2 + N) N <
      2 * (2 / 3 : ℝ) ^ N := by linarith only [hbound, hpos]
  filter_upwards [(nativeBalancedSuccessor_relative_tendsto N s).eventually
    (gt_mem_nhds hstrict)] with x hx
  exact hx.le

/-- Every positive diagonal-relative tolerance is eventually undershot at some finite rank. -/
theorem exists_native_rank_relative_reserve_lt (s : ℕ) {δ : ℝ} (hδ : 0 < δ) :
    ∃ N : ℕ, ∀ᶠ x : ℝ in atTop, nativeBalancedSuccessor N s x /
      nativeBalancedMoment s x (2 * N) < δ := by
  have hpow := tendsto_pow_atTop_nhds_zero_of_lt_one
    (show (0 : ℝ) ≤ 2 / 3 by positivity) (show (2 / 3 : ℝ) < 1 by norm_num)
  have hlim : Tendsto (fun N : ℕ => 2 * (2 / 3 : ℝ) ^ N) atTop (𝓝 0) := by
    simpa only [mul_zero] using hpow.const_mul 2
  obtain ⟨N, hN⟩ := (hlim.eventually (gt_mem_nhds hδ)).exists
  refine ⟨N, ?_⟩
  filter_upwards [nativeBalancedSuccessor_relative_eventually_le N s] with x hx
  exact hx.trans_lt hN

/-- No positive fraction of the diagonal survives uniformly over native-tail successor rank. -/
theorem not_native_rank_uniform_relative_reserve (s : ℕ) :
    ¬ ∃ δ : ℝ, 0 < δ ∧ ∀ N : ℕ, ∀ᶠ x : ℝ in atTop,
      δ ≤ nativeBalancedSuccessor N s x / nativeBalancedMoment s x (2 * N) := by
  rintro ⟨δ, hδ, hbound⟩
  obtain ⟨N, hN⟩ := exists_native_rank_relative_reserve_lt s hδ
  obtain ⟨x, hxlo, hxhi⟩ := ((hbound N).and hN).exists
  exact not_lt_of_ge hxlo hxhi

#print axioms nativeBalancedSuccessor_tendsto
#print axioms nativeBalancedSuccessor_eventual_bounds
#print axioms nativeBalancedHead_relative_posDef_eventually
#print axioms nativeBalancedSuccessor_relative_tendsto
#print axioms nativeBalancedSuccessor_relative_eventually_le
#print axioms not_native_rank_uniform_relative_reserve

end GaloisForLFunctions.CompletedArithmeticForms
