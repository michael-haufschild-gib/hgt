import GaloisForLFunctions.HTGeometry.TwoLocalStarSpectralJetFrame

/-!
# One analytic spectral chart detects every balanced real covector

The bounded ternary diagonal reference has simple spectrum. Its matrix-space analytic
eigenvalue branches restrict to the explicit two-local star roots as joint germs in all
couplings. Product-neighborhood locality then transfers the mixed response derivatives,
their exact Parseval frame identity, and their order-`n+1` detection bound to one chart.

This is a local spectral certificate. It does not bound the measure of approximate
circuit tubes, global fibre multiplicity, or the return-excised incidence action.
-/

open scoped BigOperators Matrix.Norms.Elementwise
open Filter Topology

namespace GaloisForLFunctions.HTGeometry

noncomputable section

noncomputable local instance starChartBoolCubeFintype
    {I : Type*} [Fintype I] : Fintype (I → Bool) := Fintype.ofFinite _

/-- The common simple diagonal matrix, independent of spin and spectral covector. -/
def commonReferenceSpectralMatrix (n : ℕ) :
    Matrix (Fin n → Bool) (Fin n → Bool) ℂ :=
  Matrix.diagonal fun x => (starJetReferenceEnergy n x : ℂ)

/-- One analytic eigenvalue branch on matrix space for each common-base label. -/
def commonReferenceSpectralBranch (n : ℕ) (x : Fin n → Bool) :
    Matrix (Fin n → Bool) (Fin n → Bool) ℂ → ℂ :=
  Classical.choose (simpleDiagonalMatrix_eigenvalueBranch
    (fun y => (starJetReferenceEnergy n y : ℂ))
    (Complex.ofReal_injective.comp (starJetReferenceEnergy_injective n)) x)

theorem commonReferenceSpectralBranch_spec (n : ℕ) (x : Fin n → Bool) :
    AnalyticAt ℂ (commonReferenceSpectralBranch n x) (commonReferenceSpectralMatrix n) ∧
    commonReferenceSpectralBranch n x (commonReferenceSpectralMatrix n) =
      (starJetReferenceEnergy n x : ℂ) ∧
    ∀ᶠ H in 𝓝 (commonReferenceSpectralMatrix n),
      matrixCharpolyRelation (H, commonReferenceSpectralBranch n x H) = 0 :=
  Classical.choose_spec (simpleDiagonalMatrix_eigenvalueBranch
    (fun y => (starJetReferenceEnergy n y : ℂ))
    (Complex.ofReal_injective.comp (starJetReferenceEnergy_injective n)) x)

/-- Spectator contribution to a star-slice energy. -/
def commonReferenceStarMean {n : ℕ} (i : Fin n) (z : qubitEnvironment n i) : ℝ :=
  ∑ j : {j : Fin n // j ≠ i}, starJetReferenceField n j * (if z j then -1 else 1)

/-- The full real star slice, reindexed in the common computational basis. -/
def commonReferenceStarMatrix {n : ℕ} (i : Fin n)
    (q : ({j : Fin n // j ≠ i} → ℝ) × ℝ) :
    Matrix (Fin n → Bool) (Fin n → Bool) ℂ :=
  (blockSplitMatrix (commonReferenceStarMean i)
    (twoLocalStarGap (starJetReferenceField n i) q.1) (q.2 : ℂ)).submatrix
      (edgeEquiv i).symm (edgeEquiv i).symm

/-- Explicit roots on the joint coupling space, with common-base labels. -/
def commonReferenceStarRoot {n : ℕ} (i : Fin n) (x : Fin n → Bool)
    (q : ({j : Fin n // j ≠ i} → ℝ) × ℝ) : ℝ :=
  blockSplitRoot (commonReferenceStarMean i)
    (twoLocalStarGap (starJetReferenceField n i) q.1)
      ((edgeEquiv i).symm x) q.2

@[simp] theorem commonReferenceStarRoot_at_zero {n : ℕ} (i : Fin n)
    (x : Fin n → Bool) :
    commonReferenceStarRoot i x 0 = starJetReferenceEnergy n x := by
  simpa only [commonReferenceStarRoot, Prod.fst_zero, Prod.snd_zero,
    Equiv.apply_symm_apply] using!
    commonReferenceStarRoot_zero n i ((edgeEquiv i).symm x)

@[simp] theorem commonReferenceStarMatrix_zero {n : ℕ} (i : Fin n) :
    commonReferenceStarMatrix i 0 = commonReferenceSpectralMatrix n := by
  classical
  have he (p : Fin 2 × qubitEnvironment n i) :
      blockEnergy (commonReferenceStarMean i)
        (twoLocalStarGap (starJetReferenceField n i) 0) p =
          starJetReferenceEnergy n (edgeEquiv i p) := by
    rw [← blockSplitRoot_zero_eq _ _ (by
      intro z
      simpa [twoLocalStarGap] using (starJetReferenceField_pos_le_one n i).1)]
    exact commonReferenceStarRoot_zero n i p
  ext x y
  simp only [commonReferenceStarMatrix, Prod.fst_zero, Prod.snd_zero,
    Complex.ofReal_zero, blockSplitMatrix_zero, Matrix.submatrix_apply,
    commonReferenceSpectralMatrix, Matrix.diagonal_apply]
  by_cases h : x = y
  · subst y
    simp [he]
  · have h' : (edgeEquiv i).symm x ≠ (edgeEquiv i).symm y :=
      fun heq => h ((edgeEquiv i).symm.injective heq)
    simp [h, h']

theorem continuous_commonReferenceStarMatrix {n : ℕ} (i : Fin n) :
    Continuous (commonReferenceStarMatrix i) := by
  classical
  apply continuous_pi
  intro x
  apply continuous_pi
  intro y
  change Continuous fun q : ({j : Fin n // j ≠ i} → ℝ) × ℝ =>
    blockSplitMatrix (commonReferenceStarMean i)
    (twoLocalStarGap (starJetReferenceField n i) q.1) (q.2 : ℂ)
      ((edgeEquiv i).symm x) ((edgeEquiv i).symm y)
  generalize (edgeEquiv i).symm x = p
  generalize (edgeEquiv i).symm y = p'
  rcases p with ⟨a, z⟩
  rcases p' with ⟨b, z'⟩
  by_cases hz : z = z'
  · subst z'
    simp only [blockSplitMatrix, Matrix.blockDiagonal_apply_eq]
    fin_cases a <;> fin_cases b <;> dsimp [splitBlock, twoLocalStarGap] <;> fun_prop
  · simp only [blockSplitMatrix, Matrix.blockDiagonal_apply, if_neg hz]
    exact continuous_const

theorem continuous_commonReferenceStarRoot {n : ℕ} (i : Fin n)
    (x : Fin n → Bool) : Continuous (commonReferenceStarRoot i x) := by
  unfold commonReferenceStarRoot blockSplitRoot twoLocalStarGap
  fun_prop

theorem matrixCharpolyRelation_commonReferenceStarRoot {n : ℕ} (i : Fin n)
    (x : Fin n → Bool) (q : ({j : Fin n // j ≠ i} → ℝ) × ℝ) :
    matrixCharpolyRelation
      (commonReferenceStarMatrix i q, (commonReferenceStarRoot i x q : ℂ)) = 0 := by
  unfold commonReferenceStarMatrix commonReferenceStarRoot
  rw [matrixCharpolyRelation_submatrix_equiv]
  exact matrixCharpolyRelation_blockSplitRoot _ _ _ _

/-- Joint-germ identification: the same matrix-space chart gives every star-slice root.
The neighborhood is in all real couplings, not only the transverse axis. -/
theorem commonReferenceSpectralBranch_star_germ {n : ℕ} (i : Fin n) :
    ∀ᶠ q : ({j : Fin n // j ≠ i} → ℝ) × ℝ in 𝓝 0,
      ∀ x : Fin n → Bool,
        commonReferenceSpectralBranch n x (commonReferenceStarMatrix i q) =
          (commonReferenceStarRoot i x q : ℂ) := by
  classical
  apply Filter.eventually_all.mpr
  intro x
  obtain ⟨ha, hb, hr⟩ := commonReferenceSpectralBranch_spec n x
  have hH : Tendsto (commonReferenceStarMatrix i) (𝓝 0)
      (𝓝 (commonReferenceSpectralMatrix n)) := by
    simpa only [commonReferenceStarMatrix_zero] using
      (continuous_commonReferenceStarMatrix i).tendsto 0
  have hs : Tendsto (fun q =>
      commonReferenceSpectralBranch n x (commonReferenceStarMatrix i q)) (𝓝 0)
        (𝓝 (starJetReferenceEnergy n x : ℂ)) := by
    simpa only [Function.comp_def, hb] using! ha.continuousAt.tendsto.comp hH
  have ht : Tendsto (fun q => (commonReferenceStarRoot i x q : ℂ)) (𝓝 0)
      (𝓝 (starJetReferenceEnergy n x : ℂ)) := by
    simpa only [Function.comp_def, commonReferenceStarRoot_at_zero] using!
      (Complex.continuous_ofReal.comp (continuous_commonReferenceStarRoot i x)).tendsto 0
  exact simpleDiagonalMatrix_root_germs_unique
    (fun y => (starJetReferenceEnergy n y : ℂ))
    (Complex.ofReal_injective.comp (starJetReferenceEnergy_injective n)) x
    hH hs ht (hH.eventually hr)
    (Filter.Eventually.of_forall fun q => matrixCharpolyRelation_commonReferenceStarRoot i x q)

/-- A real covector applied to the single matrix-space spectral chart. -/
def commonReferenceChartAction {n : ℕ} (k : (Fin n → Bool) → ℝ)
    (H : Matrix (Fin n → Bool) (Fin n → Bool) ℂ) : ℝ :=
  ∑ x, k x * (commonReferenceSpectralBranch n x H).re

theorem commonReferenceChartAction_star_germ {n : ℕ}
    (k : (Fin n → Bool) → ℝ) (i : Fin n) :
    (fun q : ({j : Fin n // j ≠ i} → ℝ) × ℝ =>
      commonReferenceChartAction k (commonReferenceStarMatrix i q)) =ᶠ[𝓝 0]
        (fun q => commonReferenceRealStarAction k i q.1 q.2) := by
  filter_upwards [commonReferenceSpectralBranch_star_germ i] with q hq
  unfold commonReferenceChartAction
  simp_rw [hq, Complex.ofReal_re]
  rw [← (edgeEquiv i).sum_comp]
  simp only [commonReferenceStarRoot, Equiv.symm_apply_apply]
  rfl

/-- Equality of joint germs preserves transverse curvature as a coupling germ. -/
private theorem transverse_secondDeriv_germ {I : Type*} [Fintype I]
    {f g : ((I → ℝ) × ℝ) → ℝ} (h : f =ᶠ[𝓝 0] g) :
    (fun c => deriv (deriv (fun u => f (c, u))) 0) =ᶠ[𝓝 (0 : I → ℝ)]
      (fun c => deriv (deriv (fun u => g (c, u))) 0) := by
  obtain ⟨U, hU, V, hV, hUV⟩ := mem_nhds_prod_iff.mp h
  filter_upwards [hU] with c hc
  have hcEq : (fun u => f (c, u)) =ᶠ[𝓝 (0 : ℝ)] (fun u => g (c, u)) := by
    filter_upwards [hV] with u hu
    exact hUV ⟨hc, hu⟩
  exact hcEq.deriv.deriv_eq

/-- Literal mixed derivatives of the one common analytic chart coincide with the explicit
star-response derivatives. No matching of jets is assumed. -/
theorem commonReferenceChartAction_star_jet {n : ℕ}
    (k : (Fin n → Bool) → ℝ) (i : Fin n) (S : Finset {j : Fin n // j ≠ i}) :
    orderedStarCouplingDeriv S.toList
      (fun c => deriv (deriv (fun u =>
        commonReferenceChartAction k (commonReferenceStarMatrix i (c, u)))) 0) 0 =
    orderedStarCouplingDeriv S.toList
      (fun c => deriv (deriv (commonReferenceRealStarAction k i c)) 0) 0 := by
  exact orderedStarCouplingDeriv_congr S.toList
    (transverse_secondDeriv_germ (commonReferenceChartAction_star_germ k i))

/-- Compensated mixed spectral derivatives of a single chart on matrix space. -/
def commonReferenceChartJet {n : ℕ} (k : (Fin n → Bool) → ℝ)
    (B : Finset (Fin n)) : ℝ :=
  if h : B.Nonempty then
    let i := B.min' h
    let S := B.subtype (fun j => j ≠ i)
    orderedStarCouplingDeriv S.toList
      (fun c => deriv (deriv (fun u =>
        commonReferenceChartAction k (commonReferenceStarMatrix i (c, u)))) 0) 0 /
      commonReferenceStarJetAmplifier i S
  else 0

theorem commonReferenceChartJet_eq {n : ℕ} (k : (Fin n → Bool) → ℝ)
    (B : Finset (Fin n)) :
    commonReferenceChartJet k B = commonReferenceSpectralJet k B := by
  unfold commonReferenceChartJet commonReferenceSpectralJet
  split_ifs with h
  · dsimp only
    rw [commonReferenceChartAction_star_jet]
  · rfl

/-- Exact frame identity for the constructed common analytic spectral chart.
The missing constant mode is precisely the global spectral-shift covector. -/
theorem commonReferenceChartJet_parseval (n : ℕ) (k : (Fin n → Bool) → ℝ) :
    (∑ B : Finset (Fin n), commonReferenceChartJet k B ^ (2 : ℕ)) +
      (∑ x, k x) ^ (2 : ℕ) = (2 : ℝ) ^ n * ∑ x, k x ^ (2 : ℕ) := by
  simp_rw [commonReferenceChartJet_eq]
  exact commonReferenceSpectralJet_parseval n k

/-- Every nonzero balanced real covector is detected to order at most `n+1` by the same
analytic spectral chart, with an explicit Euclidean lower bound. -/
theorem commonReferenceChartAction_balanced_detection (n : ℕ)
    (k : (Fin n → Bool) → ℝ) (hbalance : ∑ x, k x = 0) (hk : k ≠ 0) :
    ∃ (i : Fin n) (S : Finset {j : Fin n // j ≠ i}),
      S.card + 2 ≤ n + 1 ∧ Real.sqrt (∑ x, k x ^ (2 : ℕ)) ≤
        |orderedStarCouplingDeriv S.toList
          (fun c => deriv (deriv (fun u =>
            commonReferenceChartAction k (commonReferenceStarMatrix i (c, u)))) 0) 0| := by
  obtain ⟨i, S, horder, hbound⟩ :=
    balanced_real_character_commonBase_starJet_detection n k hbalance hk
  exact ⟨i, S, horder, by simpa only [commonReferenceChartAction_star_jet] using hbound⟩

private theorem orderedStarCouplingDeriv_zero {I : Type*} [DecidableEq I]
    (sites : List I) (c : I → ℝ) :
    orderedStarCouplingDeriv sites (fun _ => 0) c = 0 := by
  induction sites generalizing c with
  | nil => rfl
  | cons i sites ih =>
    simp only [orderedStarCouplingDeriv, ih, deriv_const]

/-- No nonzero balanced real spectral relation can be constant on all two-local star germs
through the common base. This rules out exact local spectral flatness, not approximate tubes. -/
theorem commonReferenceChartAction_not_flat (n : ℕ)
    (k : (Fin n → Bool) → ℝ) (hbalance : ∑ x, k x = 0) (hk : k ≠ 0) :
    ∃ i : Fin n, ¬ (fun q : ({j : Fin n // j ≠ i} → ℝ) × ℝ =>
      commonReferenceChartAction k (commonReferenceStarMatrix i q)) =ᶠ[𝓝 0]
        (fun _ => commonReferenceChartAction k (commonReferenceSpectralMatrix n)) := by
  classical
  by_contra hn
  push Not at hn
  obtain ⟨i, S, _, hbound⟩ := commonReferenceChartAction_balanced_detection n k hbalance hk
  have hd : deriv (fun _ : ℝ =>
      commonReferenceChartAction k (commonReferenceSpectralMatrix n)) = fun _ => 0 := by
    funext t
    exact deriv_const t _
  have hsecond : deriv (deriv (fun _ : ℝ =>
      commonReferenceChartAction k (commonReferenceSpectralMatrix n))) 0 = 0 := by
    rw [hd]
    exact deriv_const 0 0
  have hcurv := transverse_secondDeriv_germ (hn i)
  have hzero := orderedStarCouplingDeriv_congr S.toList hcurv
  simp only [hsecond, orderedStarCouplingDeriv_zero] at hzero
  rw [hzero, abs_zero] at hbound
  obtain ⟨x, hx⟩ := Function.ne_iff.mp hk
  have hpos : 0 < ∑ y, k y ^ (2 : ℕ) :=
    Finset.sum_pos' (fun y _ => sq_nonneg (k y))
      ⟨x, Finset.mem_univ x, sq_pos_of_ne_zero hx⟩
  exact (not_le_of_gt (Real.sqrt_pos.mpr hpos)) hbound

end
end GaloisForLFunctions.HTGeometry
