import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.AccuracyScales.TenthPlateau.CutConditionedTransport
import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.AccuracyScales.TenthPlateau.MatchgateRankThreeEscape
import GaloisForLFunctions.HTGeometry.Quantum.CircuitSynthesis.ProductFormulas.SymmetricBonds.Step
import GaloisForLFunctions.HTGeometry.Quantum.CircuitSynthesis.LocalErrors.Commutator
import GaloisForLFunctions.HTGeometry.ContinuousKernelFredholmDeterminant
import GaloisForLFunctions.HTGeometry.TotalDegreePolynomialCircuitReplicaHilbertLaw
import GaloisForLFunctions.HTGeometry.HistogramCentralizerDimension
import GaloisForLFunctions.HTGeometry.GaussianQuotientFusionCapital
import Mathlib.LinearAlgebra.Vandermonde

/-! # Non-linear determinantal and polynomial circuit barriers vs. brickwork Strang survival

This module replaces linear-span replica projections onto `S_sub(r, s)` with non-linear
determinantal and homogeneous polynomial equations on Choi tensors of `TwoQubitCircuit N`, and
pairs them with the exact `1`D brickwork double-commutator simulation barrier on `Ω_rk3(n, η)`:

1. **Cut-crossing bipartite Choi determinantal barriers and all-to-all saturation:**
   - `crossCut_choiMinor_eq_zero` and `crossCut_choiMinor_le_projectiveCircuitApprox`: for every
     bipartition `S ⊆ Fin N` and every `C : TwoQubitCircuit N` with `crossCutGateCount S C ≤ k`
     (independent of total gate count), every `m × m` (`m > 4^k`) orthonormal bipartite Choi
     minor vanishes identically on `z • C.eval` and bounds the projective operator-norm distance
     from below with constant `1`:
     `‖(normalizedChoiSubmatrix S V_L V_R U.val).det‖ ≤ ‖U.val - z • (C.eval : Register N)‖`.
   - `no_nontrivial_choiMinor_above_cutCeiling` and `exists_allToAll_circuit_choiMinor_ne_zero`:
     for unrestricted all-to-all circuits, every `m × m` Choi minor with `m > 4^(min |S| |Sᶜ|)`
     vanishes on all operators, while `q = min |S| |Sᶜ| ≤ N / 2` disjoint cross-cut fermionic-SWAP
     gates already achieve nonzero `4^q × 4^q` orthonormal Choi minor determinant at gate count `q`.
2. **Polynomial-degree homogeneous Choi annihilators past `choose(2N, 2)`:**
   - `exists_homogeneous_choiAnnihilator_of_carrier_lt_multiset` and
     `polynomial_degree_choiAnnihilator_past_matchgate`: whenever
     `(N * N)^s * (r * s + s * 16).choose (s * 16) < (2^N + r - 1).choose r` (in particular at
     `s = N * (2 * N - 1) + 1` and explicit polynomial degree `r = 192 * N * Nat.log 2 N` for all
     `N ≥ 64`), every Hamiltonian `H` with maximally projective spectrum admits a unit-norm
     homogeneous degree-`r` Choi polynomial vanishing identically on all projective `s`-gate
     circuits, non-identically-zero along `t ↦ exp(-i t H)`, and obeying
     `‖P_H(exp(-i t H))‖ ≤ r * orbitCircuitDistance H s t`.
3. **Brickwork double-commutator Strang survival on `Ω_rk3(n, η)`:**
   - `norm_strang_doubleCommutator_le` and `norm_strang_pow_doubleCommutator_le`: unconditional
     `C*`-algebraic Strang double-commutator bound
     `‖exp((h / 2) • X) * exp(h • Y) * exp((h / 2) • X) - exp(h • (X + Y))‖ ≤
        (1 / 2) * (‖[X, [X, Y]]‖ + ‖[Y, [Y, X]]‖) * h^3`.
   - `strang_brickwork_pathHamiltonian_approx` and `gaussian_rk3_strang_onset_survival`: `N = n + 2`
     symmetric parity-bond sweeps use strictly fewer than `N * (2 * N - 1)` gates and keep
     `orbitCircuitDistance H (N * (2 * N - 1)) t < 1 / 10` whenever
     `(130 * max 1 R)^3 * t^3 ≤ n + 2` throughout `Ω_rk3(n, η) ∩ {‖x‖_∞ ≤ R}`. -/

open Set Filter MeasureTheory ProbabilityTheory Real Topology Matrix NormedSpace
open scoped Matrix.Norms.L2Operator ENNReal NNReal ComplexConjugate BigOperators
namespace GaloisForLFunctions.HTGeometry.AccuracyScales.TenthPlateau
open SharpOccupation SharpOccupation.FiniteRecords MaximumIntervals
noncomputable section

private abbrev Config (N : ℕ) := Fin N → Bool
private abbrev UGroup (N : ℕ) := Matrix.unitaryGroup (Config N) ℂ
private abbrev CutPair {N : ℕ} (S : Finset (Fin N)) := (S → Bool) × (S → Bool)

/-! ## Section 1: Abstract low-rank matrix Hadamard barrier and bipartite Choi minors -/

section AbstractRankHadamard

private theorem mulVec_eq_zero_of_det_ne_zero {ι : Type*} [Fintype ι] [DecidableEq ι]
    {M : Matrix ι ι ℂ} (hdet : M.det ≠ 0) {v : ι → ℂ} (hmul : M *ᵥ v = 0) : v = 0 := by
  have hunit : IsUnit M.det := isUnit_iff_ne_zero.mpr hdet
  calc v = (1 : Matrix ι ι ℂ) *ᵥ v := (Matrix.one_mulVec v).symm
    _ = (M⁻¹ * M) *ᵥ v := by rw [Matrix.nonsing_inv_mul M hunit]
    _ = M⁻¹ *ᵥ (M *ᵥ v) := (Matrix.mulVec_mulVec v M⁻¹ M).symm
    _ = 0 := by rw [hmul, Matrix.mulVec_zero]

/-- If `G : Matrix (Fin m) (Fin m) ℂ` factors as `P * Q` through `Fin r` with `r < m`, then `Gᴴ`
annihilates a unit Euclidean vector `w₀` and `G.det = 0`. -/
private theorem exists_unit_ker_conjTranspose_and_det_eq_zero {r m : ℕ} (hrm : r < m)
    {G : Matrix (Fin m) (Fin m) ℂ} (P : Matrix (Fin m) (Fin r) ℂ) (Q : Matrix (Fin r) (Fin m) ℂ)
    (hG : G = P * Q) :
    G.det = 0 ∧ ∃ w₀ : EuclideanSpace ℂ (Fin m), ‖w₀‖ = 1 ∧
      (∀ j : Fin m, ∑ i : Fin m, star (G i j) * w₀ i = 0) := by
  let L : EuclideanSpace ℂ (Fin m) →ₗ[ℂ] (Fin r → ℂ) :=
    { toFun := fun w k => ∑ i : Fin m, star (P i k) * w i
      map_add' := fun u v => funext fun k => by simp [mul_add, Finset.sum_add_distrib]
      map_smul' := fun c u => funext fun k => by
        simp only [RingHom.id_apply, Pi.smul_apply, WithLp.ofLp_smul, smul_eq_mul, Finset.mul_sum]
        exact Finset.sum_congr rfl fun i _ => by ring }
  have hker_ne : LinearMap.ker L ≠ ⊥ := by
    intro hbot
    have hinj : Function.Injective L := LinearMap.ker_eq_bot.mp hbot
    have hle := LinearMap.finrank_le_finrank_of_injective hinj
    rw [finrank_euclideanSpace_fin, Module.finrank_fin_fun] at hle
    omega
  obtain ⟨v, hv_mem, hv_ne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hker_ne
  have hv_norm_pos : 0 < ‖v‖ := norm_pos_iff.mpr hv_ne
  let w₀ : EuclideanSpace ℂ (Fin m) := (‖v‖⁻¹ : ℂ) • v
  have hw₀_norm : ‖w₀‖ = 1 := by
    dsimp only [w₀]
    rw [norm_smul, norm_inv, Complex.norm_real, Real.norm_of_nonneg hv_norm_pos.le,
      inv_mul_cancel₀ hv_norm_pos.ne']
  have hw₀_ker : L w₀ = 0 := by
    dsimp only [w₀]
    rw [map_smul, LinearMap.mem_ker.mp hv_mem, smul_zero]
  have hw₀_G (j : Fin m) : ∑ i : Fin m, star (G i j) * w₀ i = 0 := by
    rw [hG]
    calc ∑ i : Fin m, star ((P * Q) i j) * w₀ i
        = ∑ i : Fin m, ∑ k : Fin r, star (Q k j) * (star (P i k) * w₀ i) := by
            refine Finset.sum_congr rfl fun i _ => ?_
            rw [Matrix.mul_apply, star_sum, Finset.sum_mul]
            exact Finset.sum_congr rfl fun k _ => by rw [star_mul, mul_assoc]
      _ = ∑ k : Fin r, star (Q k j) * ∑ i : Fin m, star (P i k) * w₀ i := by
            rw [Finset.sum_comm]
            exact Finset.sum_congr rfl fun k _ => (Finset.mul_sum _ _ _).symm
      _ = 0 := Finset.sum_eq_zero fun k _ => by
            have hk : (∑ i : Fin m, star (P i k) * w₀ i) = 0 := by
              simpa [L] using congrFun hw₀_ker k
            rw [hk, mul_zero]
  have hdet0 : G.det = 0 := by
    by_contra hdet_ne
    have hdet_ct : Gᴴ.det ≠ 0 := by rw [Matrix.det_conjTranspose]; exact star_ne_zero.mpr hdet_ne
    have hmul0 : Gᴴ *ᵥ (fun i => w₀ i) = 0 := funext fun j => by
      simpa [Matrix.mulVec, dotProduct, Matrix.conjTranspose_apply] using hw₀_G j
    have hw0_eq : (fun i => w₀ i) = 0 := mulVec_eq_zero_of_det_ne_zero hdet_ct hmul0
    have hnorm0 : ‖w₀‖ = 0 := by
      have hw0' : w₀ = 0 := WithLp.ext (funext fun i => congrFun hw0_eq i)
      rw [hw0', norm_zero]
    linarith only [hw₀_norm, hnorm0]
  exact ⟨hdet0, w₀, hw₀_norm, hw₀_G⟩

/-- Abstract Frobenius-Hadamard determinant inequality: if `G₀ : Matrix (Fin m) (Fin m) ℂ` factors
through `Fin r` with `r < m` and `U_mat : Matrix (Fin m) (Fin m) ℂ` satisfies
`∑ i j, ‖U_mat i j‖^2 ≤ 1`, then `‖U_mat.det‖ ≤ ε` whenever `∑ i j, ‖(U_mat - G₀) i j‖^2 ≤ ε^2`. -/
private theorem det_le_frob_sub_of_rank_lt {r m : ℕ} (hrm : r < m)
    (U_mat G₀ : Matrix (Fin m) (Fin m) ℂ)
    (P : Matrix (Fin m) (Fin r) ℂ) (Q : Matrix (Fin r) (Fin m) ℂ) (hG₀ : G₀ = P * Q)
    (hU_frob : (∑ i : Fin m, ∑ j : Fin m, ‖U_mat i j‖ ^ 2) ≤ 1)
    {ε : ℝ} (hε : 0 ≤ ε)
    (hdiff_frob : (∑ i : Fin m, ∑ j : Fin m, ‖(U_mat - G₀) i j‖ ^ 2) ≤ ε ^ 2) :
    ‖U_mat.det‖ ≤ ε := by
  have hm_pos : 0 < m := Nat.lt_of_le_of_lt (Nat.zero_le r) hrm
  let i₀ : Fin m := ⟨0, hm_pos⟩
  obtain ⟨_, w₀, hw₀_norm, hw₀_ker⟩ := exists_unit_ker_conjTranspose_and_det_eq_zero hrm P Q hG₀
  have horth_sub : Orthonormal ℂ (({i₀} : Set (Fin m)).restrict fun _ : Fin m => w₀) := by
    rw [orthonormal_iff_ite]
    intro a b
    have ha : a.1 = i₀ := Set.mem_singleton_iff.mp a.2
    have hb : b.1 = i₀ := Set.mem_singleton_iff.mp b.2
    have hab : a = b := Subtype.ext (ha.trans hb.symm)
    subst hab
    simp only [↓reduceIte, Set.restrict_apply]
    rw [inner_self_eq_norm_sq_to_K, hw₀_norm]; norm_num
  have hdim_m : Module.finrank ℂ (EuclideanSpace ℂ (Fin m)) = Fintype.card (Fin m) := by simp
  obtain ⟨b, hb_eq⟩ := horth_sub.exists_orthonormalBasis_extension_of_card_eq hdim_m
  have hb0 : b i₀ = w₀ := hb_eq i₀ (Set.mem_singleton i₀)
  let W : Matrix (Fin m) (Fin m) ℂ := fun i k => (b k) i
  have hW_unit : W ∈ Matrix.unitaryGroup (Fin m) ℂ := by
    rw [Matrix.mem_unitaryGroup_iff']
    ext j k
    rw [Matrix.star_eq_conjTranspose, Matrix.mul_apply, Matrix.one_apply]
    have hin := b.orthonormal.inner_eq_ite j k
    rw [EuclideanSpace.inner_eq_star_dotProduct] at hin
    simpa [dotProduct, W, Matrix.conjTranspose_apply, mul_comm] using hin
  have hW_det_norm : ‖W.det‖ = 1 := by
    have h1 := congrArg (fun M : Matrix (Fin m) (Fin m) ℂ => ‖M.det‖)
      (Matrix.mem_unitaryGroup_iff.mp hW_unit)
    rw [Matrix.det_mul, Matrix.star_eq_conjTranspose, Matrix.det_conjTranspose,
      norm_mul, Complex.norm_conj, Matrix.det_one, norm_one] at h1
    nlinarith only [h1, norm_nonneg W.det, sq_nonneg (‖W.det‖ - 1)]
  let B_mat : Matrix (Fin m) (Fin m) ℂ := U_matᴴ * W
  have hB_det : ‖B_mat.det‖ = ‖U_mat.det‖ := by
    dsimp only [B_mat]
    rw [Matrix.det_mul, Matrix.det_conjTranspose, norm_mul, Complex.norm_conj, hW_det_norm, mul_one]
  have hcol_bound (A : Matrix (Fin m) (Fin m) ℂ) (v : EuclideanSpace ℂ (Fin m)) (hv : ‖v‖ = 1) :
      ‖(WithLp.toLp 2 (fun j : Fin m => ∑ i : Fin m, star (A i j) * v i) :
        EuclideanSpace ℂ (Fin m))‖ ^ 2 ≤ ∑ i : Fin m, ∑ j : Fin m, ‖A i j‖ ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq]
    have hcs (j : Fin m) :
        ‖∑ i : Fin m, star (A i j) * v i‖ ^ 2 ≤ ∑ i : Fin m, ‖A i j‖ ^ 2 := by
      let a_vec : EuclideanSpace ℂ (Fin m) := WithLp.toLp 2 (fun i => A i j)
      have hin : (∑ i : Fin m, star (A i j) * v i) = inner ℂ a_vec v := by
        rw [EuclideanSpace.inner_eq_star_dotProduct]
        simp [dotProduct, a_vec, mul_comm]
      rw [hin]
      calc ‖inner ℂ a_vec v‖ ^ 2
          ≤ (‖a_vec‖ * ‖v‖) ^ 2 :=
            pow_le_pow_left₀ (norm_nonneg _) (norm_inner_le_norm a_vec v) 2
        _ = ‖a_vec‖ ^ 2 := by rw [hv, mul_one]
        _ = ∑ i : Fin m, ‖A i j‖ ^ 2 := by rw [EuclideanSpace.norm_sq_eq]; rfl
    exact (Finset.sum_le_sum fun j _ => hcs j).trans_eq (Finset.sum_comm)
  have hcol_i₀ :
      ‖(WithLp.toLp 2 (fun j : Fin m => B_mat j i₀) : EuclideanSpace ℂ (Fin m))‖ ≤ ε := by
    have heq_col (j : Fin m) : B_mat j i₀ = ∑ i : Fin m, star ((U_mat - G₀) i j) * w₀ i := by
      dsimp only [B_mat, W]
      rw [Matrix.mul_apply]
      simp_rw [Matrix.conjTranspose_apply, hb0, Matrix.sub_apply, star_sub, sub_mul]
      rw [Finset.sum_sub_distrib, hw₀_ker j, sub_zero]
    simp_rw [heq_col]
    have hsq := (hcol_bound (U_mat - G₀) w₀ hw₀_norm).trans hdiff_frob
    rw [← sq_abs ε, abs_of_nonneg hε] at hsq
    exact (sq_le_sq₀ (norm_nonneg _) hε).mp hsq
  have hcol_other (k : Fin m) :
      ‖(WithLp.toLp 2 (fun j : Fin m => B_mat j k) : EuclideanSpace ℂ (Fin m))‖ ≤ 1 := by
    have heq_col (j : Fin m) : B_mat j k = ∑ i : Fin m, star (U_mat i j) * (b k) i := by
      dsimp only [B_mat, W]
      rw [Matrix.mul_apply]; simp [Matrix.conjTranspose_apply]
    simp_rw [heq_col]
    have hsq := (hcol_bound U_mat (b k) (b.orthonormal.1 k)).trans hU_frob
    exact (sq_le_one_iff₀ (norm_nonneg _)).mp hsq
  rw [← hB_det]
  refine (ContinuousKernelFredholm.complex_hadamard_column_bound B_mat).trans ?_
  rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ i₀)]
  have hrest : (∏ k ∈ Finset.univ.erase i₀,
      ‖(WithLp.toLp 2 (fun j : Fin m => B_mat j k) : EuclideanSpace ℂ (Fin m))‖) ≤ 1 := by
    calc _ ≤ ∏ _k ∈ Finset.univ.erase i₀, (1 : ℝ) :=
          Finset.prod_le_prod (fun _ _ => norm_nonneg _) (fun k _ => hcol_other k)
      _ = 1 := Finset.prod_const_one
  nlinarith only [hcol_i₀, hrest, hε,
    Finset.prod_nonneg (s := Finset.univ.erase i₀) fun k _ =>
      norm_nonneg (WithLp.toLp 2 (fun j : Fin m => B_mat j k) : EuclideanSpace ℂ (Fin m))]

end AbstractRankHadamard

/-- Merge configurations on `S` and `Sᶜ` into a full register configuration `Config N`. -/
def mergeSplitConfig {N : ℕ} (S : Finset (Fin N))
    (u : S → Bool) (v : (Sᶜ : Finset (Fin N)) → Bool) : Config N :=
  fun i => if hi : i ∈ S then u ⟨i, hi⟩ else v ⟨i, Finset.mem_compl.mpr hi⟩

private def splitConfigEquiv {N : ℕ} (S : Finset (Fin N)) :
    Config N ≃ (S → Bool) × ((Sᶜ : Finset (Fin N)) → Bool) where
  toFun x := (fun i => x i.1, fun i => x i.1)
  invFun uv := mergeSplitConfig S uv.1 uv.2
  left_inv x := funext fun i => by dsimp [mergeSplitConfig]; split_ifs <;> rfl
  right_inv := fun ⟨u, v⟩ => Prod.ext
    (funext fun ⟨i, hi⟩ => by simp [mergeSplitConfig, hi])
    (funext fun ⟨i, hi⟩ => by simp [mergeSplitConfig, Finset.mem_compl.mp hi])

/-- Normalized bipartite Choi reshaping `2^{-N/2} M_{(u_1, v_1), (u_2, v_2)}` across `(S, Sᶜ)`. -/
def normalizedBipartiteChoi {N : ℕ} (S : Finset (Fin N)) (M : Register N) :
    Matrix (CutPair S) (CutPair (Sᶜ : Finset (Fin N))) ℂ :=
  fun p q => ((Real.sqrt ((2 : ℝ) ^ N) : ℝ) : ℂ)⁻¹ *
    M (mergeSplitConfig S p.1 q.1) (mergeSplitConfig S p.2 q.2)

/-- Projected `m × m` bipartite Choi submatrix with left probes `V_L` and right probes `V_R`. -/
def normalizedChoiSubmatrix {N m : ℕ} (S : Finset (Fin N))
    (V_L : Fin m → CutPair S → ℂ)
    (V_R : Fin m → CutPair (Sᶜ : Finset (Fin N)) → ℂ)
    (M : Register N) : Matrix (Fin m) (Fin m) ℂ :=
  fun i j => ∑ p : CutPair S, ∑ q : CutPair (Sᶜ : Finset (Fin N)),
    star (V_L i p) * star (V_R j q) * normalizedBipartiteChoi S M p q

private theorem mul_mergeSplitConfig_of_supported {N : ℕ} (S : Finset (Fin N))
    {X Y : Register N} (hX : IsSiteSupported S X) (hY : IsSiteSupported Sᶜ Y)
    (p : CutPair S) (q : CutPair (Sᶜ : Finset (Fin N))) :
    (X * Y) (mergeSplitConfig S p.1 q.1) (mergeSplitConfig S p.2 q.2) =
      X (mergeSplitConfig S p.1 (fun _ => false)) (mergeSplitConfig S p.2 (fun _ => false)) *
      Y (mergeSplitConfig S (fun _ => false) q.1) (mergeSplitConfig S (fun _ => false) q.2) := by
  rw [Matrix.mul_apply]
  let z₀ : Config N := mergeSplitConfig S p.2 q.1
  rw [Finset.sum_eq_single z₀]
  · congr 1
    · exact hX.2 _ _ _ _
        (fun i hi => by simp [mergeSplitConfig, hi])
        (fun i hi => by simp [z₀, mergeSplitConfig, hi])
        (fun i hi => by simp [z₀, mergeSplitConfig, hi])
        (fun i hi => by simp [mergeSplitConfig, hi])
    · exact hY.2 _ _ _ _
        (fun i hi => by have hni := Finset.mem_compl.mp hi; simp [z₀, mergeSplitConfig, hni])
        (fun i hi => by have hni := Finset.mem_compl.mp hi; simp [mergeSplitConfig, hni])
        (fun i hi => by
          have hiS : i ∈ S := Classical.not_not.mp (mt Finset.mem_compl.mpr hi)
          simp [z₀, mergeSplitConfig, hiS])
        (fun i hi => by
          have hiS : i ∈ S := Classical.not_not.mp (mt Finset.mem_compl.mpr hi)
          simp [mergeSplitConfig, hiS])
  · intro z _ hzne
    by_cases hXz : ∀ i ∉ S, (mergeSplitConfig S p.1 q.1) i = z i
    · have hYz : ∃ i ∉ (Sᶜ : Finset (Fin N)), z i ≠ (mergeSplitConfig S p.2 q.2) i := by
        by_contra hall
        push Not at hall
        apply hzne
        funext i
        by_cases hiS : i ∈ S
        · have h1 := hall i (by simpa using hiS)
          simpa [z₀, mergeSplitConfig, hiS] using h1
        · have h1 := hXz i hiS
          simpa [z₀, mergeSplitConfig, hiS] using h1.symm
      rw [hY.1 z _ hYz, mul_zero]
    · push Not at hXz
      rw [hX.1 _ z hXz, zero_mul]
  · intro h; exact (h (Finset.mem_univ z₀)).elim

private theorem choiSubmatrix_factors_of_hasBipartiteOperatorRank {N r m : ℕ} (S : Finset (Fin N))
    (V_L : Fin m → CutPair S → ℂ) (V_R : Fin m → CutPair (Sᶜ : Finset (Fin N)) → ℂ)
    {M : Register N} (hrank : HasBipartiteOperatorRank S r M) :
    ∃ (P : Matrix (Fin m) (Fin r) ℂ) (Q : Matrix (Fin r) (Fin m) ℂ),
      normalizedChoiSubmatrix S V_L V_R M = P * Q := by
  obtain ⟨X, Y, hX, hY, rfl⟩ := hrank
  let cN : ℂ := ((Real.sqrt ((2 : ℝ) ^ N) : ℝ) : ℂ)⁻¹
  let fL (i : Fin m) (k : Fin r) (p : CutPair S) : ℂ :=
    star (V_L i p) * X k (mergeSplitConfig S p.1 (fun _ => false)) (mergeSplitConfig S p.2 (fun _ => false))
  let fR (j : Fin m) (k : Fin r) (q : CutPair (Sᶜ : Finset (Fin N))) : ℂ :=
    star (V_R j q) * Y k (mergeSplitConfig S (fun _ => false) q.1) (mergeSplitConfig S (fun _ => false) q.2)
  let P : Matrix (Fin m) (Fin r) ℂ := Matrix.of fun i k => cN * ∑ p : CutPair S, fL i k p
  let Q : Matrix (Fin r) (Fin m) ℂ := Matrix.of fun k j => ∑ q : CutPair (Sᶜ : Finset (Fin N)), fR j k q
  refine ⟨P, Q, ?_⟩
  ext i j
  rw [normalizedChoiSubmatrix, Matrix.mul_apply]
  have hentry (p : CutPair S) (q : CutPair (Sᶜ : Finset (Fin N))) :
      star (V_L i p) * star (V_R j q) * normalizedBipartiteChoi S (∑ k : Fin r, X k * Y k) p q =
        ∑ k : Fin r, (cN * fL i k p) * fR j k q := by
    unfold normalizedBipartiteChoi
    rw [Matrix.sum_apply]
    simp_rw [mul_mergeSplitConfig_of_supported S (hX _) (hY _)]
    rw [Finset.mul_sum, Finset.mul_sum]
    exact Finset.sum_congr rfl fun k _ => by dsimp only [cN, fL, fR]; ring
  simp_rw [hentry]
  simp_rw [Finset.sum_comm (s := (Finset.univ : Finset (CutPair (Sᶜ : Finset (Fin N)))))
    (t := (Finset.univ : Finset (Fin r)))]
  rw [Finset.sum_comm (s := (Finset.univ : Finset (CutPair S)))
    (t := (Finset.univ : Finset (Fin r)))]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp only [P, Q, Matrix.of_apply]
  rw [Finset.mul_sum, Finset.sum_mul]
  exact Finset.sum_congr rfl fun p _ => by rw [Finset.mul_sum]

private theorem normalizedBipartiteChoi_frob_eq {N : ℕ} (S : Finset (Fin N)) (M : Register N) :
    (∑ p : CutPair S, ∑ q : CutPair (Sᶜ : Finset (Fin N)), ‖normalizedBipartiteChoi S M p q‖ ^ 2) =
      ((2 : ℝ) ^ N)⁻¹ * ∑ x : Config N, ∑ y : Config N, ‖M x y‖ ^ 2 := by
  have hpow_pos : (0 : ℝ) < (2 : ℝ) ^ N := by positivity
  have hnorm_c : ‖(((Real.sqrt ((2 : ℝ) ^ N) : ℝ) : ℂ)⁻¹)‖ ^ 2 = ((2 : ℝ) ^ N)⁻¹ := by
    rw [norm_inv, Complex.norm_real, Real.norm_of_nonneg (Real.sqrt_nonneg _),
      inv_pow, Real.sq_sqrt hpow_pos.le]
  have hterm (p : CutPair S) (q : CutPair (Sᶜ : Finset (Fin N))) :
      ‖normalizedBipartiteChoi S M p q‖ ^ 2 =
        ((2 : ℝ) ^ N)⁻¹ * ‖M (mergeSplitConfig S p.1 q.1) (mergeSplitConfig S p.2 q.2)‖ ^ 2 := by
    unfold normalizedBipartiteChoi
    rw [norm_mul, mul_pow, hnorm_c]
  simp_rw [hterm, ← Finset.mul_sum]
  congr 1
  let pairEqv : (CutPair S × CutPair (Sᶜ : Finset (Fin N))) ≃ (Config N × Config N) :=
    Equiv.prodProdProdComm.trans (((splitConfigEquiv S).symm).prodCongr ((splitConfigEquiv S).symm))
  rw [← Fintype.sum_prod_type',
    ← Fintype.sum_prod_type' (f := fun x y : Config N => ‖M x y‖ ^ 2)]
  exact Equiv.sum_comp pairEqv fun xy => ‖M xy.1 xy.2‖ ^ 2

private theorem register_frob_le_card_mul_opNorm_sq {N : ℕ} (X : Register N) :
    (∑ x : Config N, ∑ y : Config N, ‖X x y‖ ^ 2) ≤ ((2 : ℝ) ^ N) * ‖X‖ ^ 2 := by
  rw [Finset.sum_comm]
  have hcol (y : Config N) : (∑ x : Config N, ‖X x y‖ ^ 2) ≤ ‖X‖ ^ 2 := by
    let e_y : EuclideanSpace ℂ (Config N) := PiLp.single 2 y 1
    have he_norm : ‖e_y‖ = 1 := by simp [e_y]
    have hact : ‖(WithLp.toLp 2 (X *ᵥ e_y.ofLp) : EuclideanSpace ℂ (Config N))‖ ≤ ‖X‖ := by
      have hle := Matrix.l2_opNorm_mulVec X e_y
      rwa [he_norm, mul_one] at hle
    have hsq : ‖(WithLp.toLp 2 (X *ᵥ e_y.ofLp) : EuclideanSpace ℂ (Config N))‖ ^ 2 ≤ ‖X‖ ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) hact 2
    rw [EuclideanSpace.norm_sq_eq] at hsq
    refine le_trans ?_ hsq
    refine Finset.sum_le_sum fun x _ => ?_
    have hxy : (X *ᵥ e_y.ofLp) x = X x y := by
      simp [Matrix.mulVec, dotProduct, e_y, PiLp.single_apply]
    rw [WithLp.ofLp_toLp, hxy]
  calc (∑ y : Config N, ∑ x : Config N, ‖X x y‖ ^ 2)
      ≤ ∑ _y : Config N, ‖X‖ ^ 2 := Finset.sum_le_sum fun y _ => hcol y
    _ = ((2 : ℝ) ^ N) * ‖X‖ ^ 2 := by simp [Fintype.card_fin, Fintype.card_bool]

private theorem normalizedChoiSubmatrix_frob_le {N m : ℕ} (S : Finset (Fin N))
    (V_L : Fin m → CutPair S → ℂ)
    (V_R : Fin m → CutPair (Sᶜ : Finset (Fin N)) → ℂ)
    (hVL : ∀ i j : Fin m, (∑ p : CutPair S, star (V_L i p) * V_L j p) = if i = j then 1 else 0)
    (hVR : ∀ i j : Fin m,
      (∑ q : CutPair (Sᶜ : Finset (Fin N)), star (V_R i q) * V_R j q) = if i = j then 1 else 0)
    (M : Register N) :
    (∑ i : Fin m, ∑ j : Fin m, ‖normalizedChoiSubmatrix S V_L V_R M i j‖ ^ 2) ≤
      ((2 : ℝ) ^ N)⁻¹ * ∑ x : Config N, ∑ y : Config N, ‖M x y‖ ^ 2 := by
  let Dom := CutPair S × CutPair (Sᶜ : Finset (Fin N))
  let ψ : (Fin m × Fin m) → EuclideanSpace ℂ Dom :=
    fun ij => WithLp.toLp 2 (fun pq : Dom => V_L ij.1 pq.1 * V_R ij.2 pq.2)
  have horth : Orthonormal ℂ ψ := by
    rw [orthonormal_iff_ite]
    rintro ⟨i₁, j₁⟩ ⟨i₂, j₂⟩
    rw [EuclideanSpace.inner_eq_star_dotProduct]
    change (∑ pq : Dom, (V_L i₂ pq.1 * V_R j₂ pq.2) * star (V_L i₁ pq.1 * V_R j₁ pq.2)) = _
    rw [Fintype.sum_prod_type]
    have hprod : (∑ p : CutPair S, ∑ q : CutPair (Sᶜ : Finset (Fin N)),
        (V_L i₂ p * V_R j₂ q) * star (V_L i₁ p * V_R j₁ q)) =
        (∑ p : CutPair S, star (V_L i₁ p) * V_L i₂ p) *
        (∑ q : CutPair (Sᶜ : Finset (Fin N)), star (V_R j₁ q) * V_R j₂ q) := by
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl fun p _ => ?_
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun q _ => by rw [star_mul]; ring
    rw [hprod, hVL i₁ i₂, hVR j₁ j₂]
    by_cases hi : i₁ = i₂ <;> by_cases hj : j₁ = j₂ <;> simp [hi, hj]
  let Φ : EuclideanSpace ℂ Dom :=
    WithLp.toLp 2 (fun pq : Dom => normalizedBipartiteChoi S M pq.1 pq.2)
  have hbessel := horth.sum_inner_products_le (s := Finset.univ) Φ
  have hin_eq (i j : Fin m) :
      ‖inner ℂ (ψ (i, j)) Φ‖ ^ 2 = ‖normalizedChoiSubmatrix S V_L V_R M i j‖ ^ 2 := by
    congr 1
    rw [EuclideanSpace.inner_eq_star_dotProduct]
    unfold normalizedChoiSubmatrix
    rw [← Fintype.sum_prod_type]
    congr 1
    refine Finset.sum_congr rfl fun pq _ => ?_
    dsimp [ψ, Φ]
    rw [star_mul]; ring
  rw [Fintype.sum_prod_type] at hbessel
  simp_rw [hin_eq] at hbessel
  have hΦ_sq : ‖Φ‖ ^ 2 = ∑ p : CutPair S, ∑ q : CutPair (Sᶜ : Finset (Fin N)),
      ‖normalizedBipartiteChoi S M p q‖ ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq, Fintype.sum_prod_type]; rfl
  exact hbessel.trans (hΦ_sq.le.trans_eq (normalizedBipartiteChoi_frob_eq S M))

/-- Boolean test whether a two-qubit gate on wires `(a, b)` crosses the cut `(S, Sᶜ)`. -/
def gateCrossesCut {N : ℕ} (S : Finset (Fin N)) (a b : Fin N) : Bool :=
  decide (a ∈ S) != decide (b ∈ S)

/-- Number of elementary two-qubit gates in `C` that have one wire in `S` and one wire in `Sᶜ`. -/
def crossCutGateCount {N : ℕ} (S : Finset (Fin N)) (C : TwoQubitCircuit N) : ℕ :=
  (Finset.univ.filter fun r : Fin C.gateCount =>
    gateCrossesCut S (C.architecture.sites r).1 (C.architecture.sites r).2).card

private theorem lift_supported_pair {N : ℕ} (a b : Fin N) (hab : a ≠ b)
    (B : Matrix (Bool × Bool) (Bool × Bool) ℂ) :
    IsSiteSupported ({a, b} : Finset (Fin N)) (twoQubitLiftMatrix a b hab B) := by
  let I := {i : Fin N // i ≠ a ∧ i ≠ b}
  let rest (x : Config N) := fun i : I => x i.val
  have entry (x y : Config N) : twoQubitLiftMatrix a b hab B x y =
      B (x a, x b) (y a, y b) * (1 : Matrix (I → Bool) (I → Bool) ℂ) (rest x) (rest y) := rfl
  refine ⟨?_, ?_⟩
  · rintro x y ⟨i, hi, hxy⟩
    have he : rest x ≠ rest y := fun h => hxy (congrFun h ⟨i, by simpa using hi⟩)
    rw [entry, Matrix.one_apply_ne he, mul_zero]
  · intro x y x' y' hx hy ho ho'
    have hr (v w : Config N) (h : ∀ i, i ∉ ({a, b} : Finset (Fin N)) → v i = w i) :
        rest v = rest w := funext fun i => h i.val (by simpa using i.property)
    rw [entry, entry, hr x y ho, hr x' y' ho', Matrix.one_apply_eq, Matrix.one_apply_eq,
      hx a (by simp), hx b (by simp), hy a (by simp), hy b (by simp)]

private theorem hasBipartiteOperatorRank_singleGate_sameSide {N : ℕ} (S : Finset (Fin N))
    (a b : Fin N) (hab : a ≠ b) (B : Matrix (Bool × Bool) (Bool × Bool) ℂ)
    (hsame : gateCrossesCut S a b = false) :
    HasBipartiteOperatorRank S 1 (twoQubitLiftMatrix a b hab B) := by
  unfold gateCrossesCut at hsame
  by_cases ha : a ∈ S
  · have hb : b ∈ S := by simp [ha] at hsame; exact hsame
    have hsub : ({a, b} : Finset (Fin N)) ⊆ S := fun i hi => by
      rcases Finset.mem_insert.mp hi with rfl | hi'
      · exact ha
      · exact Finset.mem_singleton.mp hi' ▸ hb
    refine ⟨fun _ => twoQubitLiftMatrix a b hab B, fun _ => 1,
      fun _ => (lift_supported_pair a b hab B).mono hsub,
      fun _ => IsSiteSupported.one Sᶜ, ?_⟩
    simp
  · have hb : b ∉ S := by simp [ha] at hsame; exact hsame
    have hsub : ({a, b} : Finset (Fin N)) ⊆ Sᶜ := fun i hi => by
      rw [Finset.mem_compl]
      rcases Finset.mem_insert.mp hi with rfl | hi'
      · exact ha
      · exact Finset.mem_singleton.mp hi' ▸ hb
    refine ⟨fun _ => 1, fun _ => twoQubitLiftMatrix a b hab B,
      fun _ => IsSiteSupported.one S,
      fun _ => (lift_supported_pair a b hab B).mono hsub, ?_⟩
    simp

private def fin4EquivBoolPair : Fin 4 ≃ Bool × Bool where
  toFun i := match i with
    | ⟨0, _⟩ => (false, false)
    | ⟨1, _⟩ => (false, true)
    | ⟨2, _⟩ => (true, false)
    | ⟨3, _⟩ => (true, true)
  invFun p := match p with
    | (false, false) => 0
    | (false, true) => 1
    | (true, false) => 2
    | (true, true) => 3
  left_inv i := by fin_cases i <;> rfl
  right_inv := fun ⟨a, b⟩ => by cases a <;> cases b <;> rfl

private theorem hasBipartiteOperatorRank_singleGate_cross {N : ℕ} (S : Finset (Fin N))
    (a b : Fin N) (hab : a ≠ b) (B : Matrix (Bool × Bool) (Bool × Bool) ℂ)
    (hcross : gateCrossesCut S a b = true) :
    HasBipartiteOperatorRank S 4 (twoQubitLiftMatrix a b hab B) := by
  unfold gateCrossesCut at hcross
  obtain ⟨eqv4⟩ : Nonempty (Fin 4 ≃ Bool × Bool) := ⟨fin4EquivBoolPair⟩
  by_cases ha : a ∈ S
  · have hb : b ∉ S := by simp [ha] at hcross; exact hcross
    let X_ab (uv : Bool × Bool) : Register N := fun x y =>
      if x a = uv.1 ∧ y a = uv.2 ∧ (∀ i ≠ a, x i = y i) then 1 else 0
    let Y_ab (uv : Bool × Bool) : Register N := fun x y =>
      if ∀ i ≠ b, x i = y i then B (uv.1, x b) (uv.2, y b) else 0
    have hX_supp (uv : Bool × Bool) : IsSiteSupported S (X_ab uv) := by
      refine IsSiteSupported.mono (Finset.singleton_subset_iff.mpr ha) ⟨?_, ?_⟩
      · rintro x y ⟨i, hi, hne⟩
        have hia : i ≠ a := by simpa using hi
        dsimp only [X_ab]; rw [if_neg]; rintro ⟨_, _, hall⟩; exact hne (hall i hia)
      · intro x y x' y' hx hy ho ho'
        dsimp only [X_ab]
        have hxa : x a = x' a := hx a (Finset.mem_singleton_self a)
        have hya : y a = y' a := hy a (Finset.mem_singleton_self a)
        have hall_iff : (∀ i ≠ a, x i = y i) ↔ (∀ i ≠ a, x' i = y' i) :=
          ⟨fun _ i hia => ho' i (by simpa using hia), fun _ i hia => ho i (by simpa using hia)⟩
        by_cases hc : x a = uv.1 ∧ y a = uv.2 ∧ (∀ i ≠ a, x i = y i)
        · rw [if_pos hc, if_pos ⟨hxa ▸ hc.1, hya ▸ hc.2.1, hall_iff.mp hc.2.2⟩]
        · rw [if_neg hc, if_neg (fun hc' => hc ⟨hxa.symm ▸ hc'.1, hya.symm ▸ hc'.2.1, hall_iff.mpr hc'.2.2⟩)]
    have hY_supp (uv : Bool × Bool) : IsSiteSupported Sᶜ (Y_ab uv) := by
      refine IsSiteSupported.mono (Finset.singleton_subset_iff.mpr (Finset.mem_compl.mpr hb)) ⟨?_, ?_⟩
      · rintro x y ⟨i, hi, hne⟩
        have hib : i ≠ b := by simpa using hi
        dsimp only [Y_ab]; rw [if_neg]; intro hall; exact hne (hall i hib)
      · intro x y x' y' hx hy ho ho'
        dsimp only [Y_ab]
        have hxb : x b = x' b := hx b (Finset.mem_singleton_self b)
        have hyb : y b = y' b := hy b (Finset.mem_singleton_self b)
        have hall_iff : (∀ i ≠ b, x i = y i) ↔ (∀ i ≠ b, x' i = y' i) :=
          ⟨fun _ i hib => ho' i (by simpa using hib), fun _ i hib => ho i (by simpa using hib)⟩
        by_cases hc : ∀ i ≠ b, x i = y i
        · rw [if_pos hc, if_pos (hall_iff.mp hc), hxb, hyb]
        · rw [if_neg hc, if_neg (mt hall_iff.mpr hc)]
    refine ⟨fun k => X_ab (eqv4 k), fun k => Y_ab (eqv4 k),
      fun k => hX_supp _, fun k => hY_supp _, ?_⟩
    dsimp only
    rw [Equiv.sum_comp eqv4 (fun uv => X_ab uv * Y_ab uv)]
    ext x z
    rw [Matrix.sum_apply]
    let uv₀ : Bool × Bool := (x a, z a)
    rw [Finset.sum_eq_single uv₀]
    · rw [Matrix.mul_apply]
      let y₀ : Config N := Function.update x a (z a)
      rw [Finset.sum_eq_single y₀]
      · have hXy : X_ab uv₀ x y₀ = 1 := by
          dsimp only [X_ab, y₀, uv₀]
          rw [if_pos ⟨rfl, Function.update_self a (z a) x,
            fun i hia => (Function.update_of_ne hia (z a) x).symm⟩]
        rw [hXy, one_mul]
        dsimp only [Y_ab, y₀, uv₀]
        have hyb : Function.update x a (z a) b = x b := Function.update_of_ne hab.symm (z a) x
        rw [hyb]
        let I := {i : Fin N // i ≠ a ∧ i ≠ b}
        have hentry : twoQubitLiftMatrix a b hab B x z =
            B (x a, x b) (z a, z b) *
              (1 : Matrix (I → Bool) (I → Bool) ℂ) (fun i => x i.1) (fun i => z i.1) := rfl
        rw [hentry]
        by_cases hall : ∀ i ≠ b, Function.update x a (z a) i = z i
        · rw [if_pos hall]
          have hrest_eq : (fun i : I => x i.1) = (fun i : I => z i.1) := funext fun i => by
            have h1 := hall i.1 i.2.2
            rwa [Function.update_of_ne i.2.1] at h1
          rw [hrest_eq, Matrix.one_apply_eq, mul_one]
        · rw [if_neg hall]
          have hrest_ne : (fun i : I => x i.1) ≠ (fun i : I => z i.1) := by
            intro heq; apply hall; intro i hib
            by_cases hia : i = a
            · subst hia; simp
            · exact congrFun heq ⟨i, hia, hib⟩
          rw [Matrix.one_apply_ne hrest_ne, mul_zero]
      · intro y _ hyne
        dsimp only [X_ab, uv₀]
        split_ifs with hc
        · exfalso; apply hyne; funext i
          by_cases hia : i = a
          · subst hia; simpa [y₀] using hc.2.1
          · simpa [y₀, hia] using (hc.2.2 i hia).symm
        · exact zero_mul _
      · intro h; exact (h (Finset.mem_univ y₀)).elim
    · intro uv _ huv_ne
      rw [Matrix.mul_apply]
      refine Finset.sum_eq_zero fun y _ => ?_
      dsimp only [X_ab, Y_ab]
      split_ifs with h1 h2
      · exfalso; apply huv_ne
        have hyza : y a = z a := h2 a hab
        exact Prod.ext h1.1.symm (hyza.symm.trans h1.2.1).symm
      · exact mul_zero _
      · exact zero_mul _
      · exact zero_mul _
    · intro h; exact (h (Finset.mem_univ uv₀)).elim
  · have hb : b ∈ S := by simp [ha] at hcross; exact hcross
    let X_ba (uv : Bool × Bool) : Register N := fun x y =>
      if x b = uv.1 ∧ y b = uv.2 ∧ (∀ i ≠ b, x i = y i) then 1 else 0
    let Y_ba (uv : Bool × Bool) : Register N := fun x y =>
      if ∀ i ≠ a, x i = y i then B (x a, uv.1) (y a, uv.2) else 0
    have hX_supp (uv : Bool × Bool) : IsSiteSupported S (X_ba uv) := by
      refine IsSiteSupported.mono (Finset.singleton_subset_iff.mpr hb) ⟨?_, ?_⟩
      · rintro x y ⟨i, hi, hne⟩
        have hib : i ≠ b := by simpa using hi
        dsimp only [X_ba]; rw [if_neg]; rintro ⟨_, _, hall⟩; exact hne (hall i hib)
      · intro x y x' y' hx hy ho ho'
        dsimp only [X_ba]
        have hxb : x b = x' b := hx b (Finset.mem_singleton_self b)
        have hyb : y b = y' b := hy b (Finset.mem_singleton_self b)
        have hall_iff : (∀ i ≠ b, x i = y i) ↔ (∀ i ≠ b, x' i = y' i) :=
          ⟨fun _ i hib => ho' i (by simpa using hib), fun _ i hib => ho i (by simpa using hib)⟩
        by_cases hc : x b = uv.1 ∧ y b = uv.2 ∧ (∀ i ≠ b, x i = y i)
        · rw [if_pos hc, if_pos ⟨hxb ▸ hc.1, hyb ▸ hc.2.1, hall_iff.mp hc.2.2⟩]
        · rw [if_neg hc, if_neg (fun hc' => hc ⟨hxb.symm ▸ hc'.1, hyb.symm ▸ hc'.2.1, hall_iff.mpr hc'.2.2⟩)]
    have hY_supp (uv : Bool × Bool) : IsSiteSupported Sᶜ (Y_ba uv) := by
      refine IsSiteSupported.mono (Finset.singleton_subset_iff.mpr (Finset.mem_compl.mpr ha)) ⟨?_, ?_⟩
      · rintro x y ⟨i, hi, hne⟩
        have hia : i ≠ a := by simpa using hi
        dsimp only [Y_ba]; rw [if_neg]; intro hall; exact hne (hall i hia)
      · intro x y x' y' hx hy ho ho'
        dsimp only [Y_ba]
        have hxa : x a = x' a := hx a (Finset.mem_singleton_self a)
        have hya : y a = y' a := hy a (Finset.mem_singleton_self a)
        have hall_iff : (∀ i ≠ a, x i = y i) ↔ (∀ i ≠ a, x' i = y' i) :=
          ⟨fun _ i hia => ho' i (by simpa using hia), fun _ i hia => ho i (by simpa using hia)⟩
        by_cases hc : ∀ i ≠ a, x i = y i
        · rw [if_pos hc, if_pos (hall_iff.mp hc), hxa, hya]
        · rw [if_neg hc, if_neg (mt hall_iff.mpr hc)]
    refine ⟨fun k => X_ba (eqv4 k), fun k => Y_ba (eqv4 k),
      fun k => hX_supp _, fun k => hY_supp _, ?_⟩
    dsimp only
    rw [Equiv.sum_comp eqv4 (fun uv => X_ba uv * Y_ba uv)]
    ext x z
    rw [Matrix.sum_apply]
    let uv₀ : Bool × Bool := (x b, z b)
    rw [Finset.sum_eq_single uv₀]
    · rw [Matrix.mul_apply]
      let y₀ : Config N := Function.update x b (z b)
      rw [Finset.sum_eq_single y₀]
      · have hXy : X_ba uv₀ x y₀ = 1 := by
          dsimp only [X_ba, y₀, uv₀]
          rw [if_pos ⟨rfl, Function.update_self b (z b) x,
            fun i hib => (Function.update_of_ne hib (z b) x).symm⟩]
        rw [hXy, one_mul]
        dsimp only [Y_ba, y₀, uv₀]
        have hya : Function.update x b (z b) a = x a := Function.update_of_ne hab (z b) x
        rw [hya]
        let I := {i : Fin N // i ≠ a ∧ i ≠ b}
        have hentry : twoQubitLiftMatrix a b hab B x z =
            B (x a, x b) (z a, z b) *
              (1 : Matrix (I → Bool) (I → Bool) ℂ) (fun i => x i.1) (fun i => z i.1) := rfl
        rw [hentry]
        by_cases hall : ∀ i ≠ a, Function.update x b (z b) i = z i
        · rw [if_pos hall]
          have hrest_eq : (fun i : I => x i.1) = (fun i : I => z i.1) := funext fun i => by
            have h1 := hall i.1 i.2.1
            rwa [Function.update_of_ne i.2.2] at h1
          rw [hrest_eq, Matrix.one_apply_eq, mul_one]
        · rw [if_neg hall]
          have hrest_ne : (fun i : I => x i.1) ≠ (fun i : I => z i.1) := by
            intro heq; apply hall; intro i hia
            by_cases hib : i = b
            · subst hib; simp
            · exact congrFun heq ⟨i, hia, hib⟩
          rw [Matrix.one_apply_ne hrest_ne, mul_zero]
      · intro y _ hyne
        dsimp only [X_ba, uv₀]
        split_ifs with hc
        · exfalso; apply hyne; funext i
          by_cases hib : i = b
          · subst hib; simpa [y₀] using hc.2.1
          · simpa [y₀, hib] using (hc.2.2 i hib).symm
        · exact zero_mul _
      · intro h; exact (h (Finset.mem_univ y₀)).elim
    · intro uv _ huv_ne
      rw [Matrix.mul_apply]
      refine Finset.sum_eq_zero fun y _ => ?_
      dsimp only [X_ba, Y_ba]
      split_ifs with h1 h2
      · exfalso; apply huv_ne
        have hyzb : y b = z b := h2 b hab.symm
        exact Prod.ext h1.1.symm (hyzb.symm.trans h1.2.1).symm
      · exact mul_zero _
      · exact zero_mul _
      · exact zero_mul _
    · intro h; exact (h (Finset.mem_univ uv₀)).elim

/-- Every `C : TwoQubitCircuit N` has bipartite operator rank at most `4^(crossCutGateCount S C)`
across `(S, Sᶜ)`, regardless of how many gates act inside `S` or inside `Sᶜ`. -/
theorem hasBipartiteOperatorRank_of_crossCutGateCount {N : ℕ} (S : Finset (Fin N))
    (C : TwoQubitCircuit N) :
    HasBipartiteOperatorRank S (4 ^ crossCutGateCount S C) (C.eval : Register N) := by
  let p (r : Fin C.gateCount) : Bool :=
    gateCrossesCut S (C.architecture.sites r).1 (C.architecture.sites r).2
  let g (r : Fin C.gateCount) : UGroup N := C.architecture.gateLift r (C.gates r)
  have hg_val (r : Fin C.gateCount) : (g r).val =
      twoQubitLiftMatrix (C.architecture.sites r).1 (C.architecture.sites r).2
        (C.architecture.distinct r) (specialUnitaryAsUnitary (C.gates r)).val := by
    ext x y
    simp only [g, TwoQubitArchitecture.gateLift, twoQubitLift, twoQubitLiftMatrix,
      unitaryGroupReindex_coe, Quantum.tensorGate_val, OneMemClass.coe_one,
      Matrix.kronecker, Matrix.reindex_apply, Matrix.submatrix_apply]
  have hlist : ∀ L : List (Fin C.gateCount),
      HasBipartiteOperatorRank S (4 ^ (L.filter p).length) ((L.map g).prod : Register N) := by
    intro L
    induction L with
    | nil =>
        simp only [List.filter_nil, List.length_nil, pow_zero, List.map_nil, List.prod_nil,
          OneMemClass.coe_one]
        exact ⟨fun _ => 1, fun _ => 1, fun _ => IsSiteSupported.one S,
          fun _ => IsSiteSupported.one Sᶜ, by simp⟩
    | cons r tail ih =>
        simp only [List.map_cons, List.prod_cons, Submonoid.coe_mul, hg_val r]
        by_cases hcross : p r = true
        · simp only [List.filter_cons_of_pos hcross, List.length_cons, pow_succ']
          exact (hasBipartiteOperatorRank_singleGate_cross S _ _ (C.architecture.distinct r)
            _ hcross).mul ih
        · have hfalse : p r = false := Bool.eq_false_iff.mpr hcross
          simp only [List.filter_cons_of_neg hcross]
          have hmul := (hasBipartiteOperatorRank_singleGate_sameSide S _ _
            (C.architecture.distinct r) _ hfalse).mul ih
          rwa [one_mul] at hmul
  let L₀ : List (Fin C.gateCount) := (List.ofFn fun r : Fin C.gateCount => r).reverse
  have hprod_eq : ((L₀.map g).prod : Register N) = (C.eval : Register N) := by
    dsimp only [L₀]
    rw [List.map_reverse, List.map_ofFn, Function.comp_def]
    rfl
  have hnodup : (L₀.filter p).Nodup :=
    (List.nodup_reverse.mpr (List.nodup_ofFn.mpr Function.injective_id)).filter p
  have hfinset : (L₀.filter p).toFinset = Finset.univ.filter (fun r => p r = true) := by
    ext r
    simp [L₀]
  have hlen_eq : (L₀.filter p).length = crossCutGateCount S C := by
    rw [← List.toFinset_card_of_nodup hnodup, hfinset]
    rfl
  rw [← hprod_eq, ← hlen_eq]
  exact hlist L₀

private theorem hasBipartiteOperatorRank_smul {N r : ℕ} {S : Finset (Fin N)} {M : Register N}
    (z : ℂ) (h : HasBipartiteOperatorRank S r M) :
    HasBipartiteOperatorRank S r (z • M) := by
  obtain ⟨X, Y, hX, hY, rfl⟩ := h
  refine ⟨fun k => z • X k, Y, fun k => ?_, hY, ?_⟩
  · refine ⟨fun x y hdiff => by simp [(hX k).1 x y hdiff],
      fun x y x' y' hx hy ho ho' => by simp [(hX k).2 x y x' y' hx hy ho ho']⟩
  · rw [Finset.smul_sum]
    exact Finset.sum_congr rfl fun k _ => (Matrix.smul_mul z (X k) (Y k)).symm

/-- Homogeneous degree-`(4^k + 1)` determinantal circuit equation: for every `C : TwoQubitCircuit N`
with `crossCutGateCount S C ≤ k` (even if `C.gateCount` is arbitrarily large), every `m × m`
projected bipartite Choi minor (`m > 4^k`) vanishes identically on `z • C.eval` for all `z ∈ ℂ`. -/
theorem crossCut_choiMinor_eq_zero {N k m : ℕ} (S : Finset (Fin N))
    (hm : 4 ^ k < m)
    (V_L : Fin m → CutPair S → ℂ)
    (V_R : Fin m → CutPair (Sᶜ : Finset (Fin N)) → ℂ)
    (C : TwoQubitCircuit N) (hcross : crossCutGateCount S C ≤ k) (z : ℂ) :
    (normalizedChoiSubmatrix S V_L V_R (z • (C.eval : Register N))).det = 0 := by
  have hrank : HasBipartiteOperatorRank S (4 ^ k) (z • (C.eval : Register N)) :=
    HasBipartiteOperatorRank.mono (Nat.pow_le_pow_right (by decide) hcross)
      (hasBipartiteOperatorRank_smul z (hasBipartiteOperatorRank_of_crossCutGateCount S C))
  obtain ⟨P, Q, hPQ⟩ := choiSubmatrix_factors_of_hasBipartiteOperatorRank S V_L V_R hrank
  exact (exists_unit_ker_conjTranspose_and_det_eq_zero hm P Q hPQ).1

/-- Constant-`1` determinantal operator-norm approximation floor for cut-bounded circuits: for every
unitary `U ∈ U(2^N)`, every `C : TwoQubitCircuit N` with `crossCutGateCount S C ≤ k`, every `z ∈ ℂ`,
and every orthonormal probe pair `(V_L, V_R)` of size `m > 4^k` (in particular `m = 4^k + 1`),
`‖(normalizedChoiSubmatrix S V_L V_R U.val).det‖ ≤ ‖U.val - z • (C.eval : Register N)‖`. -/
theorem crossCut_choiMinor_le_projectiveCircuitApprox {N k m : ℕ} (S : Finset (Fin N))
    (hm : 4 ^ k < m)
    (V_L : Fin m → CutPair S → ℂ)
    (V_R : Fin m → CutPair (Sᶜ : Finset (Fin N)) → ℂ)
    (hVL : ∀ i j : Fin m, (∑ p : CutPair S, star (V_L i p) * V_L j p) = if i = j then 1 else 0)
    (hVR : ∀ i j : Fin m,
      (∑ q : CutPair (Sᶜ : Finset (Fin N)), star (V_R i q) * V_R j q) = if i = j then 1 else 0)
    (U : UGroup N) (C : TwoQubitCircuit N) (hcross : crossCutGateCount S C ≤ k) (z : ℂ) :
    ‖(normalizedChoiSubmatrix S V_L V_R U.val).det‖ ≤
      ‖U.val - z • (C.eval : Register N)‖ := by
  have hrank : HasBipartiteOperatorRank S (4 ^ k) (z • (C.eval : Register N)) :=
    HasBipartiteOperatorRank.mono (Nat.pow_le_pow_right (by decide) hcross)
      (hasBipartiteOperatorRank_smul z (hasBipartiteOperatorRank_of_crossCutGateCount S C))
  obtain ⟨P, Q, hPQ⟩ := choiSubmatrix_factors_of_hasBipartiteOperatorRank S V_L V_R hrank
  have hsub_eq : normalizedChoiSubmatrix S V_L V_R U.val -
      normalizedChoiSubmatrix S V_L V_R (z • (C.eval : Register N)) =
      normalizedChoiSubmatrix S V_L V_R (U.val - z • (C.eval : Register N)) := by
    ext i j
    unfold normalizedChoiSubmatrix normalizedBipartiteChoi
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun q _ => ?_
    rw [Matrix.sub_apply]; ring
  have hU_frob : (∑ i : Fin m, ∑ j : Fin m, ‖normalizedChoiSubmatrix S V_L V_R U.val i j‖ ^ 2) ≤ 1 := by
    refine (normalizedChoiSubmatrix_frob_le S V_L V_R hVL hVR U.val).trans ?_
    have h1 := register_frob_le_card_mul_opNorm_sq U.val
    have hU_norm : ‖U.val‖ = 1 := CStarRing.norm_of_mem_unitary U.2
    rw [hU_norm, one_pow, mul_one] at h1
    calc ((2 : ℝ) ^ N)⁻¹ * ∑ x : Config N, ∑ y : Config N, ‖U.val x y‖ ^ 2
        ≤ ((2 : ℝ) ^ N)⁻¹ * ((2 : ℝ) ^ N) :=
          mul_le_mul_of_nonneg_left h1 (inv_nonneg.mpr (by positivity))
      _ = 1 := inv_mul_cancel₀ (by positivity)
  have hdiff_frob : (∑ i : Fin m, ∑ j : Fin m,
      ‖(normalizedChoiSubmatrix S V_L V_R U.val -
        normalizedChoiSubmatrix S V_L V_R (z • (C.eval : Register N))) i j‖ ^ 2) ≤
      ‖U.val - z • (C.eval : Register N)‖ ^ 2 := by
    rw [hsub_eq]
    refine (normalizedChoiSubmatrix_frob_le S V_L V_R hVL hVR _).trans ?_
    calc ((2 : ℝ) ^ N)⁻¹ * ∑ x : Config N, ∑ y : Config N,
          ‖(U.val - z • (C.eval : Register N)) x y‖ ^ 2
        ≤ ((2 : ℝ) ^ N)⁻¹ * (((2 : ℝ) ^ N) * ‖U.val - z • (C.eval : Register N)‖ ^ 2) :=
          mul_le_mul_of_nonneg_left (register_frob_le_card_mul_opNorm_sq _) (inv_nonneg.mpr (by positivity))
      _ = ‖U.val - z • (C.eval : Register N)‖ ^ 2 := by
          rw [← mul_assoc, inv_mul_cancel₀ (by positivity), one_mul]
  exact det_le_frob_sub_of_rank_lt hm _ _ P Q hPQ hU_frob (norm_nonneg _) hdiff_frob

/-- All-to-all cut-rank ceiling triviality: for every `m > 4^(min |S| |Sᶜ|)`, **every** `m × m`
projected Choi minor vanishes identically on **all** matrices `M : Register N` (including every
unitary `exp(-i t H)`), so pure cut-determinantal equations cannot exceed rank `4^(min |S| |Sᶜ|)`. -/
theorem no_nontrivial_choiMinor_above_cutCeiling {N m : ℕ} (S : Finset (Fin N))
    (hm : 4 ^ min S.card Sᶜ.card < m)
    (V_L : Fin m → CutPair S → ℂ)
    (V_R : Fin m → CutPair (Sᶜ : Finset (Fin N)) → ℂ)
    (M : Register N) :
    (normalizedChoiSubmatrix S V_L V_R M).det = 0 := by
  obtain ⟨P, Q, hPQ⟩ := choiSubmatrix_factors_of_hasBipartiteOperatorRank S V_L V_R
    (universal_bipartiteOperatorRank_ceiling S M)
  exact (exists_unit_ker_conjTranspose_and_det_eq_zero hm P Q hPQ).1

private def fSwapIntPair : Matrix (Bool × Bool) (Bool × Bool) ℤ :=
  fun p q => if p.1 = q.2 ∧ p.2 = q.1 then (if p.1 && p.2 then -1 else 1) else 0

private theorem fSwapIntPair_mul_self : fSwapIntPair * fSwapIntPair = 1 := by
  ext ⟨a₁, b₁⟩ ⟨a₂, b₂⟩
  rw [Matrix.mul_apply, Fintype.sum_prod_type]
  cases a₁ <;> cases b₁ <;> cases a₂ <;> cases b₂ <;>
    simp [fSwapIntPair, Bool.sum_bool]

private theorem fSwapIntPair_det :
    (Matrix.reindex fin4EquivBoolPair.symm fin4EquivBoolPair.symm fSwapIntPair).det = 1 := by
  rw [Matrix.det_fin_four]
  simp [fSwapIntPair, fin4EquivBoolPair]

private def fSwapMatrix : Matrix (Bool × Bool) (Bool × Bool) ℂ :=
  fun p q => if p.1 = q.2 ∧ p.2 = q.1 then (if p.1 && p.2 then -1 else 1) else 0

private theorem fSwapMatrix_mem_specialUnitary :
    fSwapMatrix ∈ Matrix.specialUnitaryGroup (Bool × Bool) ℂ := by
  have hfSwap_eq : fSwapMatrix = fSwapIntPair.map (Int.castRingHom ℂ) := by
    ext ⟨a₁, b₁⟩ ⟨a₂, b₂⟩
    cases a₁ <;> cases b₁ <;> cases a₂ <;> cases b₂ <;> simp [fSwapMatrix, fSwapIntPair]
  have hstar : star fSwapMatrix = fSwapMatrix := by
    rw [Matrix.star_eq_conjTranspose]
    ext ⟨a₁, b₁⟩ ⟨a₂, b₂⟩
    cases a₁ <;> cases b₁ <;> cases a₂ <;> cases b₂ <;> simp [fSwapMatrix]
  have hmul_self : fSwapMatrix * fSwapMatrix = 1 := by
    rw [hfSwap_eq, ← Matrix.map_mul, fSwapIntPair_mul_self]
    exact Matrix.map_one (Int.castRingHom ℂ) (map_zero _) (map_one _)
  rw [Matrix.mem_specialUnitaryGroup_iff]
  refine ⟨?_, ?_⟩
  · rw [Matrix.mem_unitaryGroup_iff', hstar]
    exact hmul_self
  · rw [← Matrix.det_reindex_self fin4EquivBoolPair.symm fSwapMatrix, hfSwap_eq]
    change ((Matrix.reindex fin4EquivBoolPair.symm fin4EquivBoolPair.symm fSwapIntPair).map
      (Int.castRingHom ℂ)).det = 1
    rw [← RingHom.map_det, fSwapIntPair_det, map_one]

private def fSwapSpecialUnitary : Matrix.specialUnitaryGroup (Bool × Bool) ℂ :=
  ⟨fSwapMatrix, fSwapMatrix_mem_specialUnitary⟩

private theorem prod_disjoint_fSwap_apply {N q : ℕ}
    (a b : Fin q → Fin N)
    (hab : ∀ k, a k ≠ b k)
    (ha_inj : Function.Injective a) (hb_inj : Function.Injective b)
    (hdisj : ∀ k l, a k ≠ b l) :
    ∃ C : TwoQubitCircuit N, C.gateCount = q ∧
      ∀ x y : Config N,
        (C.eval : Register N) x y =
          (if ∀ i, (∀ k, i ≠ a k) → (∀ k, i ≠ b k) → x i = y i then 1 else 0) *
            ∏ k : Fin q, fSwapMatrix (x (a k), x (b k)) (y (a k), y (b k)) := by
  induction q with
  | zero =>
      refine ⟨TwoQubitCircuit.one N, by simp [TwoQubitCircuit.one], fun x y => ?_⟩
      simp only [TwoQubitCircuit.one_eval, Submonoid.coe_one, Finset.univ_eq_empty,
        Finset.prod_empty, mul_one, Matrix.one_apply]
      by_cases hxy : x = y
      · subst hxy; simp
      · rw [if_neg hxy, if_neg]
        intro hall; apply hxy; funext i
        exact hall i (fun k => Fin.elim0 k) (fun k => Fin.elim0 k)
  | succ q ih =>
      obtain ⟨C_tail, hlen_tail, heval_tail⟩ := ih
        (fun k => a k.succ) (fun k => b k.succ)
        (fun k => hab k.succ)
        (fun _ _ h => Fin.succ_injective _ (ha_inj h))
        (fun _ _ h => Fin.succ_injective _ (hb_inj h))
        (fun k l => hdisj k.succ l.succ)
      let C₀ := TwoQubitCircuit.singleOn (a 0) (b 0) (hab 0) fSwapSpecialUnitary
      let C : TwoQubitCircuit N := C₀.mul C_tail
      have hgate_C : C.gateCount = q + 1 := by
        dsimp only [C]
        rw [TwoQubitCircuit.mul_gateCount]
        have h0 : C₀.gateCount = 1 := rfl
        rw [h0, hlen_tail]; omega
      have heval_C : (C.eval : Register N) = (C₀.eval : Register N) * (C_tail.eval : Register N) := by
        dsimp only [C]
        rw [TwoQubitCircuit.mul_eval, Submonoid.coe_mul]
      have hC₀_entry (u v : Config N) :
          (C₀.eval : Register N) u v =
            fSwapMatrix (u (a 0), u (b 0)) (v (a 0), v (b 0)) *
              if ∀ i, i ≠ a 0 → i ≠ b 0 → u i = v i then 1 else 0 := by
        dsimp only [C₀]
        rw [TwoQubitCircuit.singleOn_eval]
        let I := {i : Fin N // i ≠ a 0 ∧ i ≠ b 0}
        change fSwapMatrix (u (a 0), u (b 0)) (v (a 0), v (b 0)) *
          (1 : Matrix (I → Bool) (I → Bool) ℂ) (fun i => u i.1) (fun i => v i.1) = _
        congr 1
        by_cases hall : ∀ i, i ≠ a 0 → i ≠ b 0 → u i = v i
        · rw [if_pos hall]
          have heq : (fun i : I => u i.1) = (fun i : I => v i.1) :=
            funext fun i => hall i.1 i.2.1 i.2.2
          rw [heq, Matrix.one_apply_eq]
        · rw [if_neg hall]
          have hne : (fun i : I => u i.1) ≠ (fun i : I => v i.1) := by
            intro heq; apply hall; intro i h1 h2; exact congrFun heq ⟨i, h1, h2⟩
          rw [Matrix.one_apply_ne hne]
      refine ⟨C, hgate_C, fun x y => ?_⟩
      rw [heval_C, Matrix.mul_apply, Fin.prod_univ_succ]
      let z₁ : Config N := Function.update (Function.update x (a 0) (x (b 0))) (b 0) (x (a 0))
      have hz₁_a0 : z₁ (a 0) = x (b 0) := by
        dsimp [z₁]; rw [Function.update_of_ne (hab 0), Function.update_self]
      have hz₁_b0 : z₁ (b 0) = x (a 0) := by dsimp [z₁]; rw [Function.update_self]
      have hz₁_rest : ∀ i, i ≠ a 0 → i ≠ b 0 → x i = z₁ i := fun i h1 h2 => by
        dsimp [z₁]; rw [Function.update_of_ne h2, Function.update_of_ne h1]
      rw [Finset.sum_eq_single z₁]
      · rw [hC₀_entry x z₁, if_pos hz₁_rest, mul_one, heval_tail z₁ y]
        have hak_ne_a0 (k : Fin q) : a k.succ ≠ a 0 := fun h => Fin.succ_ne_zero k (ha_inj h)
        have hak_ne_b0 (k : Fin q) : a k.succ ≠ b 0 := hdisj k.succ 0
        have hbk_ne_a0 (k : Fin q) : b k.succ ≠ a 0 := (hdisj 0 k.succ).symm
        have hbk_ne_b0 (k : Fin q) : b k.succ ≠ b 0 := fun h => Fin.succ_ne_zero k (hb_inj h)
        have hprod_eq : (∏ k : Fin q, fSwapMatrix (z₁ (a k.succ), z₁ (b k.succ))
            (y (a k.succ), y (b k.succ))) =
            ∏ k : Fin q, fSwapMatrix (x (a k.succ), x (b k.succ)) (y (a k.succ), y (b k.succ)) :=
          Finset.prod_congr rfl fun k _ => by
            rw [← hz₁_rest (a k.succ) (hak_ne_a0 k) (hak_ne_b0 k),
              ← hz₁_rest (b k.succ) (hbk_ne_a0 k) (hbk_ne_b0 k)]
        rw [hprod_eq]
        have hf_z₁ : fSwapMatrix (x (a 0), x (b 0)) (z₁ (a 0), z₁ (b 0)) =
            if x (a 0) && x (b 0) then (-1 : ℂ) else 1 := by
          rw [hz₁_a0, hz₁_b0]; simp [fSwapMatrix]
        rw [hf_z₁]
        by_cases h0_match : x (a 0) = y (b 0) ∧ x (b 0) = y (a 0)
        · have hf_y : fSwapMatrix (x (a 0), x (b 0)) (y (a 0), y (b 0)) =
              if x (a 0) && x (b 0) then (-1 : ℂ) else 1 := by
            unfold fSwapMatrix; rw [if_pos h0_match]
          rw [hf_y]
          have hrest_iff : (∀ i, (∀ k : Fin q, i ≠ a k.succ) → (∀ k : Fin q, i ≠ b k.succ) → z₁ i = y i) ↔
              (∀ i, (∀ k : Fin (q + 1), i ≠ a k) → (∀ k : Fin (q + 1), i ≠ b k) → x i = y i) := by
            constructor
            · intro h i ha_all hb_all
              rw [hz₁_rest i (ha_all 0) (hb_all 0)]
              exact h i (fun k => ha_all k.succ) (fun k => hb_all k.succ)
            · intro h i ha' hb'
              by_cases hia0 : i = a 0
              · subst hia0; rw [hz₁_a0, h0_match.2]
              · by_cases hib0 : i = b 0
                · subst hib0; rw [hz₁_b0, h0_match.1]
                · rw [← hz₁_rest i hia0 hib0]
                  exact h i (fun k => Fin.cases hia0 ha' k) (fun k => Fin.cases hib0 hb' k)
          by_cases hr : ∀ i, (∀ k : Fin (q + 1), i ≠ a k) → (∀ k : Fin (q + 1), i ≠ b k) → x i = y i
          · rw [if_pos hr, if_pos (hrest_iff.mpr hr), one_mul, mul_one]
          · rw [if_neg hr, if_neg (mt hrest_iff.mp hr), zero_mul, mul_zero, zero_mul]
        · have hf_y0 : fSwapMatrix (x (a 0), x (b 0)) (y (a 0), y (b 0)) = 0 := by
            unfold fSwapMatrix; rw [if_neg h0_match]
          have htail_if0 : ¬ (∀ i, (∀ k : Fin q, i ≠ a k.succ) →
              (∀ k : Fin q, i ≠ b k.succ) → z₁ i = y i) := by
            intro hall; apply h0_match
            have h1 := hall (a 0) (fun k => (hak_ne_a0 k).symm) (fun k => (hbk_ne_a0 k).symm)
            have h2 := hall (b 0) (fun k => (hak_ne_b0 k).symm) (fun k => (hbk_ne_b0 k).symm)
            rw [hz₁_a0] at h1; rw [hz₁_b0] at h2
            exact ⟨h2, h1⟩
          rw [hf_y0, if_neg htail_if0]; ring
      · intro z _ hzne
        rw [hC₀_entry x z]
        by_cases hrest_z : ∀ i, i ≠ a 0 → i ≠ b 0 → x i = z i
        · have hnot_swap : ¬ (x (a 0) = z (b 0) ∧ x (b 0) = z (a 0)) := by
            rintro ⟨h1, h2⟩; apply hzne; funext i
            by_cases hia0 : i = a 0
            · subst hia0; rw [hz₁_a0, h2]
            · by_cases hib0 : i = b 0
              · subst hib0; rw [hz₁_b0, h1]
              · rw [← hrest_z i hia0 hib0, hz₁_rest i hia0 hib0]
          have hf0 : fSwapMatrix (x (a 0), x (b 0)) (z (a 0), z (b 0)) = 0 := by
            unfold fSwapMatrix; rw [if_neg hnot_swap]
          rw [hf0, zero_mul, zero_mul]
        · rw [if_neg hrest_z, mul_zero, zero_mul]
      · intro h; exact (h (Finset.mem_univ z₁)).elim

/-- All-to-all cut-rank saturation at `q = min |S| |Sᶜ| ≤ N / 2`: across **every** cut `S ⊆ Fin N`,
there exist an explicit `q`-gate `TwoQubitCircuit N` (`q ≤ N / 2`) and orthonormal probe families
`V_L, V_R` of maximal possible dimension `m = 4^(min |S| |Sᶜ|)` on which the projected bipartite
Choi minor is **strictly nonzero**. Together with `no_nontrivial_choiMinor_above_cutCeiling`, no
cut-determinantal equation can separate all-to-all `TwoQubitCircuit N` above gate count `N / 2`. -/
theorem exists_allToAll_circuit_choiMinor_ne_zero {N : ℕ} (S : Finset (Fin N)) :
    let q := min S.card Sᶜ.card
    q ≤ N / 2 ∧
    ∃ (C : TwoQubitCircuit N)
      (V_L : Fin (4 ^ q) → CutPair S → ℂ)
      (V_R : Fin (4 ^ q) → CutPair (Sᶜ : Finset (Fin N)) → ℂ),
      C.gateCount = q ∧
      (∀ i j : Fin (4 ^ q), (∑ p : CutPair S, star (V_L i p) * V_L j p) = if i = j then 1 else 0) ∧
      (∀ i j : Fin (4 ^ q),
        (∑ p : CutPair (Sᶜ : Finset (Fin N)), star (V_R i p) * V_R j p) = if i = j then 1 else 0) ∧
      (normalizedChoiSubmatrix S V_L V_R (C.eval : Register N)).det ≠ 0 := by
  classical
  intro q
  have hsum_card : S.card + Sᶜ.card = N := by
    simpa only [Fintype.card_fin] using Finset.card_add_card_compl S
  have hq_half : q ≤ N / 2 := by dsimp [q]; omega
  refine ⟨hq_half, ?_⟩
  have hqS : q ≤ Fintype.card S := by rw [Fintype.card_coe]; exact min_le_left _ _
  have hqSc : q ≤ Fintype.card (Sᶜ : Finset (Fin N)) := by
    rw [Fintype.card_coe]; exact min_le_right _ _
  obtain ⟨embS⟩ : Nonempty (Fin q ↪ S) :=
    ⟨(Fin.castLEEmb hqS).trans (Fintype.equivFin S).symm.toEmbedding⟩
  obtain ⟨embSc⟩ : Nonempty (Fin q ↪ (Sᶜ : Finset (Fin N))) :=
    ⟨(Fin.castLEEmb hqSc).trans (Fintype.equivFin (Sᶜ : Finset (Fin N))).symm.toEmbedding⟩
  let a : Fin q → Fin N := fun k => (embS k).1
  let b : Fin q → Fin N := fun k => (embSc k).1
  have ha_inj : Function.Injective a := fun _ _ h => embS.injective (Subtype.ext h)
  have hb_inj : Function.Injective b := fun _ _ h => embSc.injective (Subtype.ext h)
  have hdisj : ∀ k l, a k ≠ b l := fun k l h =>
    (Finset.mem_compl.mp (embSc l).2) (h ▸ (embS k).2)
  have hab : ∀ k, a k ≠ b k := fun k => hdisj k k
  obtain ⟨C, hgate, heval⟩ := prod_disjoint_fSwap_apply a b hab ha_inj hb_inj hdisj
  have hcard_sub : Fintype.card ((Fin q → Bool) × (Fin q → Bool)) = 4 ^ q := by
    have hc : Fintype.card ((Fin q → Bool) × (Fin q → Bool)) = 2 ^ q * 2 ^ q := by simp
    rw [hc, ← pow_add, show q + q = 2 * q by omega, pow_mul]; norm_num
  obtain ⟨eqvSub⟩ : Nonempty (Fin (4 ^ q) ≃ (Fin q → Bool) × (Fin q → Bool)) :=
    ⟨(finCongr hcard_sub.symm).trans (Fintype.equivFin _).symm⟩
  obtain ⟨padS, hpadS_at, hpadS_off⟩ : ∃ padS : (Fin q → Bool) → S → Bool,
      (∀ u k, padS u (embS k) = u k) ∧
      (∀ u s, (¬ ∃ k, embS k = s) → padS u s = false) := by
    refine ⟨fun u s => if h : ∃ k : Fin q, embS k = s then u h.choose else false,
      fun u k => ?_, fun u s hs => dif_neg hs⟩
    have hex : ∃ l : Fin q, embS l = embS k := ⟨k, rfl⟩
    rw [dif_pos hex, embS.injective hex.choose_spec]
  obtain ⟨padSc, hpadSc_at, hpadSc_off⟩ :
      ∃ padSc : (Fin q → Bool) → (Sᶜ : Finset (Fin N)) → Bool,
      (∀ v k, padSc v (embSc k) = v k) ∧
      (∀ v s, (¬ ∃ k, embSc k = s) → padSc v s = false) := by
    refine ⟨fun v s => if h : ∃ k : Fin q, embSc k = s then v h.choose else false,
      fun v k => ?_, fun v s hs => dif_neg hs⟩
    have hex : ∃ l : Fin q, embSc l = embSc k := ⟨k, rfl⟩
    rw [dif_pos hex, embSc.injective hex.choose_spec]
  have hpadS_inj : Function.Injective padS := fun u₁ u₂ h =>
    funext fun k => by rw [← hpadS_at u₁ k, ← hpadS_at u₂ k, h]
  have hpadSc_inj : Function.Injective padSc := fun v₁ v₂ h =>
    funext fun k => by rw [← hpadSc_at v₁ k, ← hpadSc_at v₂ k, h]
  obtain ⟨φL, hφL_def⟩ : ∃ φL : Fin (4 ^ q) → CutPair S,
      ∀ idx, φL idx = (padS (eqvSub idx).1, padS (eqvSub idx).2) := ⟨_, fun _ => rfl⟩
  obtain ⟨φR, hφR_def⟩ : ∃ φR : Fin (4 ^ q) → CutPair (Sᶜ : Finset (Fin N)),
      ∀ idx, φR idx = (padSc (eqvSub idx).2, padSc (eqvSub idx).1) := ⟨_, fun _ => rfl⟩
  have hφL_inj : Function.Injective φL := fun i j h => by
    rw [hφL_def, hφL_def] at h
    exact eqvSub.injective (Prod.ext (hpadS_inj (Prod.mk.inj h).1) (hpadS_inj (Prod.mk.inj h).2))
  have hφR_inj : Function.Injective φR := fun i j h => by
    rw [hφR_def, hφR_def] at h
    exact eqvSub.injective (Prod.ext (hpadSc_inj (Prod.mk.inj h).2) (hpadSc_inj (Prod.mk.inj h).1))
  obtain ⟨V_L, hVL_def⟩ : ∃ V_L : Fin (4 ^ q) → CutPair S → ℂ,
      ∀ i p, V_L i p = if p = φL i then 1 else 0 := ⟨_, fun _ _ => rfl⟩
  obtain ⟨V_R, hVR_def⟩ : ∃ V_R : Fin (4 ^ q) → CutPair (Sᶜ : Finset (Fin N)) → ℂ,
      ∀ j p, V_R j p = if p = φR j then 1 else 0 := ⟨_, fun _ _ => rfl⟩
  have hVL_orth (i j : Fin (4 ^ q)) :
      (∑ p : CutPair S, star (V_L i p) * V_L j p) = if i = j then 1 else 0 := by
    rw [Finset.sum_eq_single (φL i)]
    · rw [hVL_def, hVL_def, if_pos rfl, star_one, one_mul]
      by_cases hij : i = j
      · subst hij; simp
      · rw [if_neg (fun h => hij (hφL_inj h)), if_neg hij]
    · intro p _ hp; rw [hVL_def, if_neg hp, star_zero, zero_mul]
    · intro h; exact (h (Finset.mem_univ _)).elim
  have hVR_orth (i j : Fin (4 ^ q)) :
      (∑ p : CutPair (Sᶜ : Finset (Fin N)), star (V_R i p) * V_R j p) = if i = j then 1 else 0 := by
    rw [Finset.sum_eq_single (φR i)]
    · rw [hVR_def, hVR_def, if_pos rfl, star_one, one_mul]
      by_cases hij : i = j
      · subst hij; simp
      · rw [if_neg (fun h => hij (hφR_inj h)), if_neg hij]
    · intro p _ hp; rw [hVR_def, if_neg hp, star_zero, zero_mul]
    · intro h; exact (h (Finset.mem_univ _)).elim
  refine ⟨C, V_L, V_R, hgate, hVL_orth, hVR_orth, ?_⟩
  let cN : ℂ := ((Real.sqrt ((2 : ℝ) ^ N) : ℝ) : ℂ)⁻¹
  have hcN_ne : cN ≠ 0 := by
    dsimp [cN]
    exact inv_ne_zero (Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr (by positivity)).ne')
  have hdiag_eq : normalizedChoiSubmatrix S V_L V_R (C.eval : Register N) =
      Matrix.diagonal (fun i : Fin (4 ^ q) =>
        cN * ∏ k : Fin q, if (eqvSub i).1 k && (eqvSub i).2 k then (-1 : ℂ) else 1) := by
    ext i j
    unfold normalizedChoiSubmatrix
    rw [Finset.sum_eq_single (φL i)]
    · rw [Finset.sum_eq_single (φR j)]
      · rw [hVL_def, hVR_def, if_pos rfl, if_pos rfl, star_one, one_mul, one_mul]
        unfold normalizedBipartiteChoi
        change cN * (C.eval : Register N)
          (mergeSplitConfig S (φL i).1 (φR j).1) (mergeSplitConfig S (φL i).2 (φR j).2) = _
        rw [heval]
        let x := mergeSplitConfig S (φL i).1 (φR j).1
        let y := mergeSplitConfig S (φL i).2 (φR j).2
        have hxa (k : Fin q) : x (a k) = (eqvSub i).1 k := by
          dsimp only [x, mergeSplitConfig, a]
          rw [dif_pos (embS k).2, hφL_def]; exact hpadS_at _ k
        have hxb (k : Fin q) : x (b k) = (eqvSub j).2 k := by
          dsimp only [x, mergeSplitConfig, b]
          have hnb : (embSc k).1 ∉ S := Finset.mem_compl.mp (embSc k).2
          rw [dif_neg hnb, hφR_def]; exact hpadSc_at _ k
        have hya (k : Fin q) : y (a k) = (eqvSub i).2 k := by
          dsimp only [y, mergeSplitConfig, a]
          rw [dif_pos (embS k).2, hφL_def]; exact hpadS_at _ k
        have hyb (k : Fin q) : y (b k) = (eqvSub j).1 k := by
          dsimp only [y, mergeSplitConfig, b]
          have hnb : (embSc k).1 ∉ S := Finset.mem_compl.mp (embSc k).2
          rw [dif_neg hnb, hφR_def]; exact hpadSc_at _ k
        by_cases hij : i = j
        · subst hij
          rw [Matrix.diagonal_apply_eq]
          have hrest_xy : ∀ w, (∀ k, w ≠ a k) → (∀ k, w ≠ b k) → x w = y w := by
            intro w hwa hwb
            by_cases hwS : w ∈ S
            · have hne_emb : ¬ ∃ k : Fin q, embS k = ⟨w, hwS⟩ := by
                rintro ⟨k, hk⟩; exact hwa k (congrArg Subtype.val hk).symm
              dsimp only [x, y, mergeSplitConfig]
              rw [dif_pos hwS, dif_pos hwS, hφL_def, hpadS_off _ _ hne_emb, hpadS_off _ _ hne_emb]
            · have hwSc : w ∈ (Sᶜ : Finset (Fin N)) := Finset.mem_compl.mpr hwS
              have hne_emb : ¬ ∃ k : Fin q, embSc k = ⟨w, hwSc⟩ := by
                rintro ⟨k, hk⟩; exact hwb k (congrArg Subtype.val hk).symm
              dsimp only [x, y, mergeSplitConfig]
              rw [dif_neg hwS, dif_neg hwS, hφR_def, hpadSc_off _ _ hne_emb, hpadSc_off _ _ hne_emb]
          rw [if_pos hrest_xy, one_mul]
          congr 1
          refine Finset.prod_congr rfl fun k _ => ?_
          rw [hxa k, hxb k, hya k, hyb k]
          simp [fSwapMatrix]
        · rw [Matrix.diagonal_apply_ne _ hij]
          have hne_uv : eqvSub i ≠ eqvSub j := fun h => hij (eqvSub.injective h)
          have hex_k : ∃ k : Fin q,
              (eqvSub i).1 k ≠ (eqvSub j).1 k ∨ (eqvSub i).2 k ≠ (eqvSub j).2 k := by
            by_contra hall; push Not at hall; apply hne_uv
            exact Prod.ext (funext fun k => (hall k).1) (funext fun k => (hall k).2)
          obtain ⟨k₀, hk₀⟩ := hex_k
          have hprod0 : (∏ k : Fin q, fSwapMatrix (x (a k), x (b k)) (y (a k), y (b k))) = 0 := by
            refine Finset.prod_eq_zero (Finset.mem_univ k₀) ?_
            rw [hxa k₀, hxb k₀, hya k₀, hyb k₀]
            unfold fSwapMatrix
            rw [if_neg]
            rintro ⟨h1, h2⟩
            rcases hk₀ with hne1 | hne2
            · exact hne1 h1
            · exact hne2 h2.symm
          rw [hprod0, mul_zero, mul_zero]
      · intro q' _ hq'; rw [hVR_def, if_neg hq', star_zero, mul_zero, zero_mul]
      · intro h; exact (h (Finset.mem_univ _)).elim
    · intro p _ hp
      refine Finset.sum_eq_zero fun q' _ => ?_
      rw [hVL_def, if_neg hp, star_zero, zero_mul, zero_mul]
    · intro h; exact (h (Finset.mem_univ _)).elim
  rw [hdiag_eq, Matrix.det_diagonal]
  refine Finset.prod_ne_zero_iff.mpr fun i _ => mul_ne_zero hcN_ne ?_
  refine Finset.prod_ne_zero_iff.mpr fun k _ => ?_
  split_ifs <;> norm_num

/-! ## Section 2: Polynomial-degree homogeneous Choi annihilators past `choose(2N, 2)` -/

private theorem finrank_replicaTargetSpan_atMost_totalDegree_le {N s : ℕ} (hN : 1 ≤ N) (r : ℕ) :
    Module.finrank ℂ (replicaTargetSpan r
      (fun C : {C : TwoQubitCircuit N // C.gateCount ≤ s} =>
        matrixNormalizedChoi (C.val.eval : Register N))) ≤
      (N * N) ^ s * (r * s + s * 16).choose (s * 16) := by
  let q₀ : Fin N := ⟨0, hN⟩
  let pos : {C : TwoQubitCircuit N // C.gateCount ≤ s} →
      TwoQubitCircuit.twoQubitCircuitArchitectureIndex N s :=
    fun C k => if hk : k.val < C.val.gateCount then C.val.reversePosition ⟨k.val, hk⟩ else (q₀, q₀)
  let G : {C : TwoQubitCircuit N // C.gateCount ≤ s} → Fin s → Register N :=
    fun C k => if hk : k.val < C.val.gateCount then C.val.reverseGate ⟨k.val, hk⟩ else 1
  have hG : ∀ C k, TwoQubitCircuit.IsTwoQubitGate (pos C k).1 (pos C k).2 (G C k) := by
    intro C k
    by_cases hk : k.val < C.val.gateCount
    · dsimp only [pos, G]; rw [dif_pos hk, dif_pos hk]
      exact C.val.reverseGate_isTwoQubitGate ⟨k.val, hk⟩
    · dsimp only [pos, G]; rw [dif_neg hk, dif_neg hk]
      exact TwoQubitCircuit.isTwoQubitGate_one q₀ q₀
  have hpad {m : ℕ} (f : Fin m → Register N) :
      ∀ {s' : ℕ}, m ≤ s' →
        (List.ofFn (fun k : Fin s' => if hk : k.val < m then f ⟨k.val, hk⟩ else 1)).prod =
          (List.ofFn f).prod := by
    intro s' hms
    induction s', hms using Nat.le_induction with
    | base =>
        have hfn : (fun k : Fin m => if hk : k.val < m then f ⟨k.val, hk⟩ else 1) = f :=
          funext fun k => dif_pos k.isLt
        rw [hfn]
    | succ d _ ih =>
        have hlast : ¬ (Fin.last d).val < m := by rw [Fin.val_last]; omega
        rw [List.ofFn_succ', List.prod_concat, dif_neg hlast, mul_one]
        exact ih
  have htarget : (fun (C : {C : TwoQubitCircuit N // C.gateCount ≤ s})
      (p : Config N × Config N) =>
        (List.ofFn (G C)).prod p.1 p.2 / Real.sqrt (Fintype.card (Config N))) =
      fun C => matrixNormalizedChoi (C.val.eval : Register N) := by
    funext C p
    have hprod : (List.ofFn (G C)).prod = (C.val.eval : Register N) :=
      (hpad C.val.reverseGate C.property).trans C.val.reverseGate_prod_eq_eval
    rw [hprod]; rfl
  rw [← htarget]
  exact TwoQubitCircuit.finrank_replicaTargetSpan_twoQubitCircuitChoi_complete_totalDegree_le
    pos G hG r

private theorem exists_step_vandermonde_det_ne_zero {M : ℕ}
    (ω : Fin M → ℝ) (hinj : Function.Injective ω) :
    ∃ δ : ℝ, 0 < δ ∧
      (Matrix.vandermonde fun j : Fin M =>
        Complex.exp (-(Complex.I * ((δ * ω j : ℝ) : ℂ)))).det ≠ 0 := by
  let S : ℝ := 1 + ∑ j : Fin M, |ω j|
  have hS_pos : 0 < S := by
    have hsum : 0 ≤ ∑ j : Fin M, |ω j| := Finset.sum_nonneg fun _ _ => abs_nonneg _
    linarith only [hsum]
  let δ : ℝ := 1 / S
  have hδ_pos : 0 < δ := div_pos one_pos hS_pos
  refine ⟨δ, hδ_pos, ?_⟩
  let z : Fin M → ℂ := fun j => Complex.exp (-(Complex.I * ((δ * ω j : ℝ) : ℂ)))
  have hz_inj : Function.Injective z := by
    intro j₁ j₂ hzeq
    by_contra hne
    have hdiff_ne : ω j₁ - ω j₂ ≠ 0 := sub_ne_zero.mpr (hinj.ne hne)
    rw [Complex.exp_eq_exp_iff_exists_int] at hzeq
    obtain ⟨m, hm⟩ := hzeq
    have him := congrArg Complex.im hm
    simp only [Complex.neg_im, Complex.mul_im, Complex.I_re, Complex.I_im, Complex.ofReal_re,
      Complex.ofReal_im, zero_mul, one_mul, add_zero, Complex.add_im,
      Complex.intCast_im, Complex.intCast_re] at him
    have hrel : δ * (ω j₂ - ω j₁) = (m : ℝ) * (2 * Real.pi) := by
      have him2 : -(δ * ω j₁) = -(δ * ω j₂) + (m : ℝ) * (2 * Real.pi) := by
        simpa [mul_assoc, mul_comm, mul_left_comm] using him
      linarith only [him2]
    have habs_lhs : |δ * (ω j₂ - ω j₁)| < 2 := by
      rw [abs_mul, abs_of_pos hδ_pos]
      have h1 : |ω j₂ - ω j₁| ≤ |ω j₂| + |ω j₁| := abs_sub _ _
      have h2 : |ω j₂| + |ω j₁| < 2 * S := by
        have hj₁ : |ω j₁| ≤ ∑ j : Fin M, |ω j| :=
          Finset.single_le_sum (fun _ _ => abs_nonneg _) (Finset.mem_univ j₁)
        have hj₂ : |ω j₂| ≤ ∑ j : Fin M, |ω j| :=
          Finset.single_le_sum (fun _ _ => abs_nonneg _) (Finset.mem_univ j₂)
        dsimp [S]; linarith only [hj₁, hj₂]
      dsimp [δ]; rw [one_div, inv_mul_lt_iff₀ hS_pos]; exact h1.trans_lt h2
    rcases eq_or_ne m 0 with rfl | hm_ne
    · simp only [Int.cast_zero, zero_mul] at hrel
      exact hdiff_ne (neg_eq_zero.mp (by nlinarith only [hrel, hδ_pos]))
    · have hm_ge : (1 : ℝ) ≤ |(m : ℝ)| := by
        have h1 : (1 : ℤ) ≤ |m| := Int.one_le_abs hm_ne
        exact_mod_cast h1
      have hpi_gt : (3 : ℝ) < Real.pi := Real.pi_gt_three
      have habs_rhs : 6 < |(m : ℝ) * (2 * Real.pi)| := by
        rw [abs_mul, abs_of_pos (by positivity)]
        nlinarith only [hm_ge, hpi_gt]
      rw [hrel] at habs_lhs
      linarith only [habs_lhs, habs_rhs]
  rw [Matrix.det_vandermonde]
  refine Finset.prod_ne_zero_iff.mpr fun i _ => Finset.prod_ne_zero_iff.mpr fun j hj => ?_
  exact sub_ne_zero.mpr (hz_inj.ne (Finset.mem_Ioi.mp hj).ne')

private theorem finrank_maximallyProjective_replicaOrbit_ge_of_spectral {N : ℕ}
    (U_orb : ℝ → Register N) (V : UGroup N) (E : Config N → ℝ)
    (hspec : ∀ t : ℝ, U_orb t =
      V.val * Matrix.diagonal (fun a => Complex.exp (-(Complex.I * (t * E a)))) * star V.val)
    (hmax : MaximallyProjectiveEnergy E) (r : ℕ) :
    (2 ^ N + r - 1).choose r ≤
      Module.finrank ℂ (Submodule.span ℂ (Set.range fun t : ℝ =>
        finitePureTensorPowerEuclidean r (matrixNormalizedChoi (U_orb t)))) := by
  classical
  let Orbit := Submodule.span ℂ (Set.range fun t : ℝ =>
    finitePureTensorPowerEuclidean r (matrixNormalizedChoi (U_orb t)))
  let hist (m : Sym (Config N) r) : Config N → ℕ := fun x => m.val.count x
  have hhist_mem (m : Sym (Config N) r) : hist m ∈ (Finset.univ : Finset (Config N)).piAntidiag r := by
    rw [Finset.mem_piAntidiag]
    refine ⟨?_, fun _ _ => Finset.mem_univ _⟩
    dsimp [hist]
    rw [Finset.sum_multiset_count_of_subset _ _ (fun _ _ => Finset.mem_univ _), m.2]
  have hhist_inj : Function.Injective hist := fun m₁ m₂ h =>
    Subtype.ext (Multiset.ext.mpr fun x => congrFun h x)
  have hex_rep (m : Sym (Config N) r) :
      ∃ α : Fin r → Config N, orderedReplicaMultiplicity α = hist m := by
    have hcard_eq := card_fiber_orderedReplicaMultiplicity (hhist_mem m)
    have hpos : 0 < (Finset.univ.filter fun α : Fin r → Config N =>
        orderedReplicaMultiplicity α = hist m).card := by
      rw [hcard_eq]
      exact Nat.multinomial_pos _ _
    obtain ⟨α, hα⟩ := Finset.card_pos.mp hpos
    exact ⟨α, (Finset.mem_filter.mp hα).2⟩
  choose rep hrep using hex_rep
  let M_card := Fintype.card (Sym (Config N) r)
  obtain ⟨eqvS⟩ : Nonempty (Sym (Config N) r ≃ Fin M_card) := ⟨Fintype.equivFin (Sym (Config N) r)⟩
  let ω : Fin M_card → ℝ := fun i => collectiveReplicaEnergy E (rep (eqvS.symm i))
  have hω_inj : Function.Injective ω := fun i₁ i₂ h => by
    have heq := (collectiveReplicaEnergy_eq_iff_multiplicity_eq hmax
      (rep (eqvS.symm i₁)) (rep (eqvS.symm i₂))).mp h
    rw [hrep (eqvS.symm i₁), hrep (eqvS.symm i₂)] at heq
    exact eqvS.symm.injective (hhist_inj heq)
  obtain ⟨δ, _, hdet_van⟩ := exists_step_vandermonde_det_ne_zero ω hω_inj
  let singleConj (A : Config N × Config N → ℂ) (x : Config N) : ℂ :=
    ∑ u : Config N, ∑ v : Config N, star (V.val u x) * A (u, v) * V.val v x
  have hsingle_evol (t : ℝ) (x : Config N) :
      singleConj (matrixNormalizedChoi (U_orb t)) x =
        Complex.exp (-(Complex.I * ((t * E x : ℝ) : ℂ))) /
          Real.sqrt (Fintype.card (Config N)) := by
    dsimp only [singleConj, matrixNormalizedChoi]
    simp_rw [div_eq_mul_inv, ← mul_assoc, ← Finset.sum_mul]
    congr 1
    have hmat : (star V.val * U_orb t * V.val) x x =
        ∑ u : Config N, ∑ v : Config N, star (V.val u x) * U_orb t u v * V.val v x := by
      rw [Matrix.mul_apply]
      simp_rw [Matrix.mul_apply, Finset.sum_mul, Matrix.star_eq_conjTranspose,
        Matrix.conjTranspose_apply, mul_assoc]
      rw [Finset.sum_comm]
    rw [← hmat, hspec t]
    have hcancel : star V.val * (V.val * Matrix.diagonal
        (fun a => Complex.exp (-(Complex.I * (t * E a)))) * star V.val) * V.val =
        Matrix.diagonal (fun a => Complex.exp (-(Complex.I * (t * E a)))) := by
      calc star V.val * (V.val * Matrix.diagonal _ * star V.val) * V.val
          = (star V.val * V.val) * Matrix.diagonal _ * (star V.val * V.val) := by
              simp only [mul_assoc]
        _ = Matrix.diagonal _ := by rw [V.2.1, one_mul, mul_one]
    rw [hcancel, Matrix.diagonal_apply_eq]; push_cast; rfl
  let c_scale : ℂ := (((Real.sqrt (Fintype.card (Config N)) : ℝ) : ℂ) ^ r)
  let readMap : Orbit →ₗ[ℂ] (Fin M_card → ℂ) :=
    { toFun := fun Φ i => c_scale *
        ∑ p : Fin r → Config N × Config N,
          (∏ a : Fin r, star (V.val (p a).1 (rep (eqvS.symm i) a)) *
            V.val (p a).2 (rep (eqvS.symm i) a)) * Φ.1 p
      map_add' := fun Φ₁ Φ₂ => funext fun i => by
        simp [mul_add, Finset.sum_add_distrib]
      map_smul' := fun c Φ => funext fun i => by
        simp only [RingHom.id_apply, Pi.smul_apply, Submodule.coe_smul_of_tower, WithLp.ofLp_smul,
          smul_eq_mul, Finset.mul_sum]
        exact Finset.sum_congr rfl fun p _ => by ring }
  have hread_orbit (t : ℝ) :
      readMap ⟨finitePureTensorPowerEuclidean r (matrixNormalizedChoi (U_orb t)),
        Submodule.subset_span (Set.mem_range_self t)⟩ =
        fun i => Complex.exp (-(Complex.I * ((t * ω i : ℝ) : ℂ))) := by
    funext i
    dsimp only [readMap, LinearMap.coe_mk, AddHom.coe_mk]
    have hprod_sum : (∑ p : Fin r → Config N × Config N,
        (∏ a : Fin r, star (V.val (p a).1 (rep (eqvS.symm i) a)) *
          V.val (p a).2 (rep (eqvS.symm i) a)) *
          (finitePureTensorPowerEuclidean r (matrixNormalizedChoi (U_orb t))) p) =
        ∏ a : Fin r, singleConj (matrixNormalizedChoi (U_orb t)) (rep (eqvS.symm i) a) := by
      simp only [finitePureTensorPowerEuclidean, finitePureTensorPower, WithLp.ofLp_toLp,
        ← Finset.prod_mul_distrib]
      rw [← Fintype.prod_sum]
      refine Finset.prod_congr rfl fun a _ => ?_
      rw [Fintype.sum_prod_type]
      dsimp only [singleConj]
      refine Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun v _ => by ring
    rw [hprod_sum]
    simp_rw [hsingle_evol t]
    rw [Finset.prod_div_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    have hc_ne : c_scale ≠ 0 :=
      pow_ne_zero r (Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr
        (Nat.cast_pos.mpr Fintype.card_pos)).ne')
    dsimp only [c_scale]
    rw [mul_div_cancel₀ _ hc_ne, ← Complex.exp_sum]
    congr 1
    dsimp [ω, collectiveReplicaEnergy]
    push_cast
    rw [Finset.mul_sum, Finset.mul_sum]
    exact Finset.sum_congr rfl fun a _ => by ring
  let sampleOrb : Fin M_card → Orbit := fun k =>
    ⟨finitePureTensorPowerEuclidean r (matrixNormalizedChoi (U_orb ((k : ℕ) * δ))),
      Submodule.subset_span (Set.mem_range_self _)⟩
  have hli_sample : LinearIndependent ℂ sampleOrb := by
    refine LinearIndependent.of_comp readMap ?_
    rw [Fintype.linearIndependent_iff]
    intro c hc
    let z : Fin M_card → ℂ := fun i => Complex.exp (-(Complex.I * ((δ * ω i : ℝ) : ℂ)))
    have hvan_mul : (Matrix.vandermonde z) *ᵥ c = 0 := by
      ext i
      have hi := congrFun hc i
      simp only [Pi.zero_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at hi
      rw [Matrix.mulVec, dotProduct, Pi.zero_apply, ← hi]
      refine Finset.sum_congr rfl fun k _ => ?_
      have hk := congrFun (hread_orbit ((k : ℕ) * δ)) i
      dsimp only [sampleOrb]
      rw [hk, Matrix.vandermonde_apply, mul_comm (c k)]
      congr 1
      dsimp only [z]
      rw [← Complex.exp_nat_mul]
      congr 1; push_cast; ring
    have hc0 := mulVec_eq_zero_of_det_ne_zero hdet_van hvan_mul
    exact fun k => congrFun hc0 k
  have hcard_sym : M_card = (2 ^ N + r - 1).choose r := by
    dsimp [M_card]
    rw [Sym.card_sym_eq_choose]
    have hc : Fintype.card (Config N) = 2 ^ N := by simp [Config]
    rw [hc]
  rw [← hcard_sym]
  exact hli_sample.fintype_card_le_finrank

private theorem finrank_maximallyProjective_replicaOrbit_ge {N : ℕ}
    (H : selfAdjoint (Register N))
    (hmax : MaximallyProjectiveEnergy H.2.isHermitian.eigenvalues) (r : ℕ) :
    (2 ^ N + r - 1).choose r ≤
      Module.finrank ℂ (Submodule.span ℂ (Set.range fun t : ℝ =>
        finitePureTensorPowerEuclidean r
          (matrixNormalizedChoi (unitaryEvolution H.val t)))) :=
  finrank_maximallyProjective_replicaOrbit_ge_of_spectral
    (unitaryEvolution H.val)
    (hermitianEigenbasisUnitary H.2.isHermitian)
    H.2.isHermitian.eigenvalues
    (unitaryEvolution_spectral H.2.isHermitian)
    hmax r

private theorem norm_pureTensorPower_sub_le {ι : Type*} [Fintype ι] :
    ∀ (r : ℕ) (u v : EuclideanSpace ℂ ι), ‖u‖ = 1 → ‖v‖ = 1 →
      ‖finitePureTensorPowerEuclidean r u.ofLp - finitePureTensorPowerEuclidean r v.ofLp‖ ≤
        (r : ℝ) * ‖u - v‖
  | 0, u, v, _, _ => by
      have h0 : finitePureTensorPowerEuclidean 0 u.ofLp =
          finitePureTensorPowerEuclidean 0 v.ofLp := by
        ext x; simp [finitePureTensorPowerEuclidean, finitePureTensorPower]
      rw [h0, sub_self, norm_zero, Nat.cast_zero, zero_mul]
  | r + 1, u, v, hu, hv => by
      let u_r := finitePureTensorPowerEuclidean r u.ofLp
      let v_r := finitePureTensorPowerEuclidean r v.ofLp
      have hu_r_norm : ‖u_r‖ = 1 := by
        have hsq := norm_sq_finitePureTensorPowerEuclidean_eq_pow r u.ofLp
        have hu_sq : (∑ i : ι, ‖u.ofLp i‖ ^ 2) = 1 := by
          rw [← EuclideanSpace.norm_sq_eq, hu, one_pow]
        rw [hu_sq, one_pow] at hsq
        nlinarith only [hsq, norm_nonneg u_r, sq_nonneg (‖u_r‖ - 1)]
      have hv_r_norm : ‖v_r‖ = 1 := by
        have hsq := norm_sq_finitePureTensorPowerEuclidean_eq_pow r v.ofLp
        have hv_sq : (∑ i : ι, ‖v.ofLp i‖ ^ 2) = 1 := by
          rw [← EuclideanSpace.norm_sq_eq, hv, one_pow]
        rw [hv_sq, one_pow] at hsq
        nlinarith only [hsq, norm_nonneg v_r, sq_nonneg (‖v_r‖ - 1)]
      let mid : EuclideanSpace ℂ (Fin (r + 1) → ι) :=
        WithLp.toLp 2 (fun f => u.ofLp (f 0) * v_r.ofLp (fun k => f k.succ))
      have htri : ‖finitePureTensorPowerEuclidean (r + 1) u.ofLp -
          finitePureTensorPowerEuclidean (r + 1) v.ofLp‖ ≤
          ‖finitePureTensorPowerEuclidean (r + 1) u.ofLp - mid‖ +
          ‖mid - finitePureTensorPowerEuclidean (r + 1) v.ofLp‖ :=
        norm_sub_le_norm_sub_add_norm_sub _ mid _
      have hcons_sum {g : (Fin (r + 1) → ι) → ℝ} :
          (∑ f : Fin (r + 1) → ι, g f) = ∑ i : ι, ∑ tail : Fin r → ι, g (Fin.cons i tail) := by
        rw [← Equiv.sum_comp (Fin.consEquiv fun _ : Fin (r + 1) => ι) g, Fintype.sum_prod_type]
        rfl
      have h1_sq : ‖finitePureTensorPowerEuclidean (r + 1) u.ofLp - mid‖ ^ 2 =
          ‖u_r - v_r‖ ^ 2 := by
        rw [EuclideanSpace.norm_sq_eq, hcons_sum]
        have hterm (i : ι) (tail : Fin r → ι) :
            ‖(finitePureTensorPowerEuclidean (r + 1) u.ofLp - mid).ofLp (Fin.cons i tail)‖ ^ 2 =
              ‖u.ofLp i‖ ^ 2 * ‖(u_r - v_r).ofLp tail‖ ^ 2 := by
          simp only [WithLp.ofLp_sub, Pi.sub_apply, finitePureTensorPowerEuclidean,
            finitePureTensorPower, WithLp.ofLp_toLp, mid, Fin.prod_univ_succ, Fin.cons_zero,
            Fin.cons_succ]
          rw [← mul_sub, norm_mul, mul_pow]
        simp_rw [hterm, ← Finset.mul_sum, ← Finset.sum_mul, ← EuclideanSpace.norm_sq_eq,
          hu, one_pow, one_mul]
      have h2_sq : ‖mid - finitePureTensorPowerEuclidean (r + 1) v.ofLp‖ ^ 2 = ‖u - v‖ ^ 2 := by
        rw [EuclideanSpace.norm_sq_eq, hcons_sum]
        have hterm (i : ι) (tail : Fin r → ι) :
            ‖(mid - finitePureTensorPowerEuclidean (r + 1) v.ofLp).ofLp (Fin.cons i tail)‖ ^ 2 =
              ‖(u - v).ofLp i‖ ^ 2 * ‖v_r.ofLp tail‖ ^ 2 := by
          simp only [WithLp.ofLp_sub, Pi.sub_apply, finitePureTensorPowerEuclidean,
            finitePureTensorPower, WithLp.ofLp_toLp, mid, Fin.prod_univ_succ, Fin.cons_zero,
            Fin.cons_succ]
          rw [← sub_mul, norm_mul, mul_pow]
        simp_rw [hterm, ← Finset.mul_sum, ← Finset.sum_mul, ← EuclideanSpace.norm_sq_eq,
          hv_r_norm, one_pow, mul_one]
      have h1 : ‖finitePureTensorPowerEuclidean (r + 1) u.ofLp - mid‖ = ‖u_r - v_r‖ := by
        nlinarith only [h1_sq, norm_nonneg (finitePureTensorPowerEuclidean (r + 1) u.ofLp - mid),
          norm_nonneg (u_r - v_r),
          sq_nonneg (‖finitePureTensorPowerEuclidean (r + 1) u.ofLp - mid‖ - ‖u_r - v_r‖)]
      have h2 : ‖mid - finitePureTensorPowerEuclidean (r + 1) v.ofLp‖ = ‖u - v‖ := by
        nlinarith only [h2_sq, norm_nonneg (mid - finitePureTensorPowerEuclidean (r + 1) v.ofLp),
          norm_nonneg (u - v),
          sq_nonneg (‖mid - finitePureTensorPowerEuclidean (r + 1) v.ofLp‖ - ‖u - v‖)]
      have hih := norm_pureTensorPower_sub_le r u v hu hv
      push_cast
      linarith only [htri, h1, h2, hih]

private theorem exists_unit_orthogonal_of_not_mem {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] (K : Submodule ℂ E) [K.HasOrthogonalProjection]
    {v₀ : E} (hv₀ : v₀ ∉ K) :
    ∃ W : E, ‖W‖ = 1 ∧ (∀ u ∈ K, inner ℂ W u = 0) ∧ inner ℂ W v₀ ≠ 0 := by
  let w_raw : E := v₀ - (K.starProjection v₀ : E)
  have hw_raw_orth : w_raw ∈ Kᗮ := Submodule.sub_starProjection_mem_orthogonal v₀
  have hw_raw_ne : w_raw ≠ 0 := by
    intro h0
    have heq : v₀ = (K.starProjection v₀ : E) := sub_eq_zero.mp h0
    exact hv₀ (heq ▸ (K.starProjection v₀).2)
  have hw_raw_pos : 0 < ‖w_raw‖ := norm_pos_iff.mpr hw_raw_ne
  let W : E := (‖w_raw‖⁻¹ : ℂ) • w_raw
  have hW_norm : ‖W‖ = 1 := by
    dsimp only [W]
    rw [norm_smul, norm_inv, Complex.norm_real, Real.norm_of_nonneg hw_raw_pos.le,
      inv_mul_cancel₀ hw_raw_pos.ne']
  have hW_orth : W ∈ Kᗮ := Kᗮ.smul_mem _ hw_raw_orth
  have hW_van : ∀ u ∈ K, inner ℂ W u = 0 := fun u hu => (Submodule.mem_orthogonal K W).mp hW_orth u hu
  have hW_v₀ : inner ℂ W v₀ ≠ 0 := by
    have hv₀_split : v₀ = w_raw + (K.starProjection v₀ : E) := by dsimp [w_raw]; abel
    rw [hv₀_split, inner_add_right, hW_van _ (K.starProjection v₀).2, add_zero]
    dsimp only [W]
    rw [inner_smul_left, inner_self_eq_norm_sq_to_K, Complex.conj_ofReal]
    intro h0
    have hre := congrArg Complex.re h0
    simp only [Complex.mul_re, Complex.inv_re, Complex.ofReal_re, Complex.ofReal_im,
      Complex.normSq_ofReal, Complex.zero_re] at hre
    have h1 : (‖w_raw‖⁻¹ : ℂ) * ((‖w_raw‖ : ℂ) ^ 2) ≠ 0 :=
      mul_ne_zero (inv_ne_zero (Complex.ofReal_ne_zero.mpr hw_raw_pos.ne'))
        (pow_ne_zero 2 (Complex.ofReal_ne_zero.mpr hw_raw_pos.ne'))
    exact h1 h0
  exact ⟨W, hW_norm, hW_van, hW_v₀⟩

/-- Homogeneous degree-`r` Choi polynomial evaluation `P_W(M) = ⟨W, Φ_M^{⊗ r}⟩`. -/
def evalHomogeneousChoiPoly {N r : ℕ}
    (W : EuclideanSpace ℂ (Fin r → Config N × Config N)) (M : Register N) : ℂ :=
  inner ℂ W (finitePureTensorPowerEuclidean r (matrixNormalizedChoi M))

/-- Universal homogeneous Choi polynomial barrier: whenever
`(N * N)^s * (r * s + s * 16).choose (s * 16) < (2^N + r - 1).choose r`, every self-adjoint `H`
with maximally projective spectrum admits a unit-norm homogeneous degree-`r` Choi polynomial `W`
that vanishes identically on **every** projective `s`-gate circuit (`∀ C, C.gateCount ≤ s → ∀ z,
evalHomogeneousChoiPoly W (z • C.eval) = 0`), is nonzero along `t ↦ exp(-i t H)`, and obeys the
quantitative operator-norm Lipschitz bound
`‖evalHomogeneousChoiPoly W (unitaryEvolution H.val t)‖ ≤ r * orbitCircuitDistance H s t`. -/
theorem exists_homogeneous_choiAnnihilator_of_carrier_lt_multiset {N s r : ℕ}
    (hN : 1 ≤ N) (hr : 1 ≤ r)
    (H : selfAdjoint (Register N))
    (hmax : MaximallyProjectiveEnergy H.2.isHermitian.eigenvalues)
    (hdim : (N * N) ^ s * (r * s + s * 16).choose (s * 16) < (2 ^ N + r - 1).choose r) :
    ∃ W : EuclideanSpace ℂ (Fin r → Config N × Config N),
      ‖W‖ = 1 ∧
      (∀ (C : TwoQubitCircuit N), C.gateCount ≤ s → ∀ z : ℂ,
        evalHomogeneousChoiPoly W (z • (C.eval : Register N)) = 0) ∧
      (∃ t₀ : ℝ, evalHomogeneousChoiPoly W (unitaryEvolution H.val t₀) ≠ 0) ∧
      (∀ t : ℝ,
        ‖evalHomogeneousChoiPoly W (unitaryEvolution H.val t)‖ ≤
          (r : ℝ) * orbitCircuitDistance H s t) := by
  let S_circ := replicaTargetSpan r
    (fun C : {C : TwoQubitCircuit N // C.gateCount ≤ s} =>
      matrixNormalizedChoi (C.val.eval : Register N))
  let Orbit := Submodule.span ℂ (Set.range fun t : ℝ =>
    finitePureTensorPowerEuclidean r (matrixNormalizedChoi (unitaryEvolution H.val t)))
  have hfin_circ := finrank_replicaTargetSpan_atMost_totalDegree_le (s := s) hN r
  have hfin_orb := finrank_maximallyProjective_replicaOrbit_ge H hmax r
  have hnot_le : ¬ Orbit ≤ S_circ := by
    intro hle
    have hfr := Submodule.finrank_mono hle
    omega
  have hex_t : ∃ t₀ : ℝ,
      finitePureTensorPowerEuclidean r (matrixNormalizedChoi (unitaryEvolution H.val t₀)) ∉ S_circ := by
    by_contra hall; push Not at hall
    exact hnot_le (Submodule.span_le.mpr (by rintro _ ⟨t, rfl⟩; exact hall t))
  obtain ⟨t₀, ht₀_not⟩ := hex_t
  obtain ⟨W, hW_norm, hW_orth, hnonzero_t₀⟩ := exists_unit_orthogonal_of_not_mem S_circ ht₀_not
  have hvanish (C : TwoQubitCircuit N) (hC : C.gateCount ≤ s) (z : ℂ) :
      evalHomogeneousChoiPoly W (z • (C.eval : Register N)) = 0 := by
    unfold evalHomogeneousChoiPoly
    have hsmul : finitePureTensorPowerEuclidean r (matrixNormalizedChoi (z • (C.eval : Register N))) =
        (z ^ r) • finitePureTensorPowerEuclidean r (matrixNormalizedChoi (C.eval : Register N)) := by
      ext p
      simp only [finitePureTensorPowerEuclidean, finitePureTensorPower, matrixNormalizedChoi,
        Matrix.smul_apply, smul_eq_mul, mul_div_assoc, PiLp.smul_apply, WithLp.ofLp_toLp,
        Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    rw [hsmul]
    exact hW_orth _ (S_circ.smul_mem (z ^ r)
      (Submodule.subset_span (Set.mem_range_self (⟨C, hC⟩ : {C : TwoQubitCircuit N // C.gateCount ≤ s}))))
  refine ⟨W, hW_norm, hvanish, ⟨t₀, hnonzero_t₀⟩, fun t => ?_⟩
  refine le_of_forall_pos_le_add fun ε hε => ?_
  have hr_pos : (0 : ℝ) < r := by exact_mod_cast hr
  have hC_ne : (phaseCircuitMatrixImageAtMost N s).Nonempty :=
    ⟨(1 : ℂ) • ((TwoQubitCircuit.one N).eval : Register N),
      mem_phaseCircuitMatrixImageAtMost_iff.mpr ⟨1, norm_one, TwoQubitCircuit.one N, Nat.zero_le _, rfl⟩⟩
  obtain ⟨M_c, hM_mem, hM_lt⟩ := (Metric.infDist_lt_iff hC_ne).mp
    (lt_add_of_pos_right (orbitCircuitDistance H s t) (div_pos hε hr_pos))
  obtain ⟨z, hz, C, hC, rfl⟩ := mem_phaseCircuitMatrixImageAtMost_iff.mp hM_mem
  rw [dist_eq_norm] at hM_lt
  have hvan_M : evalHomogeneousChoiPoly W (z • (C.eval : Register N)) = 0 := hvanish C hC z
  have hsub_eval : evalHomogeneousChoiPoly W (unitaryEvolution H.val t) =
      inner ℂ W (finitePureTensorPowerEuclidean r
          (matrixNormalizedChoi (unitaryEvolution H.val t)) -
        finitePureTensorPowerEuclidean r
          (matrixNormalizedChoi (z • (C.eval : Register N)))) := by
    rw [inner_sub_right, ← evalHomogeneousChoiPoly, ← evalHomogeneousChoiPoly, hvan_M, sub_zero]
  let u_c : EuclideanSpace ℂ (Config N × Config N) :=
    WithLp.toLp 2 (matrixNormalizedChoi (unitaryEvolution H.val t))
  let v_c : EuclideanSpace ℂ (Config N × Config N) :=
    WithLp.toLp 2 (matrixNormalizedChoi (z • (C.eval : Register N)))
  have hunit_norm {A : Register N} (hA : A ∈ unitary (Register N)) :
      ‖(WithLp.toLp 2 (matrixNormalizedChoi A) : EuclideanSpace ℂ (Config N × Config N))‖ = 1 := by
    have hsq : ‖(WithLp.toLp 2 (matrixNormalizedChoi A) : EuclideanSpace ℂ _)‖ ^ 2 = 1 := by
      rw [EuclideanSpace.norm_sq_eq, Fintype.sum_prod_type]
      unfold matrixNormalizedChoi
      have hcard_pos : (0 : ℝ) < Fintype.card (Config N) := Nat.cast_pos.mpr Fintype.card_pos
      have hterm (x y : Config N) :
          ‖A x y / Real.sqrt (Fintype.card (Config N))‖ ^ 2 =
            ‖A x y‖ ^ 2 / Fintype.card (Config N) := by
        rw [norm_div, Complex.norm_real, Real.norm_of_nonneg (Real.sqrt_nonneg _),
          div_pow, Real.sq_sqrt hcard_pos.le]
      simp_rw [hterm, ← Finset.sum_div]
      have hsum_col (x : Config N) : (∑ y : Config N, ‖A x y‖ ^ 2) = 1 := by
        have h1 := congrFun (congrFun (Unitary.mem_iff.mp hA).2 x) x
        rw [Matrix.star_eq_conjTranspose, Matrix.mul_apply, Matrix.one_apply_eq] at h1
        have h2 : ((∑ y : Config N, ‖A x y‖ ^ 2 : ℝ) : ℂ) = 1 := by
          rw [← h1, Complex.ofReal_sum]
          refine Finset.sum_congr rfl fun y _ => ?_
          rw [Matrix.conjTranspose_apply, Complex.star_def, Complex.conj_mul', mul_comm]
        exact_mod_cast h2
      simp_rw [hsum_col, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one,
        div_self hcard_pos.ne']
    nlinarith only [hsq, norm_nonneg (WithLp.toLp 2 (matrixNormalizedChoi A) : EuclideanSpace ℂ _),
      sq_nonneg (‖(WithLp.toLp 2 (matrixNormalizedChoi A) : EuclideanSpace ℂ _)‖ - 1)]
  have hu_norm : ‖u_c‖ = 1 := hunit_norm (unitaryEvolution_mem_unitary H.2 t)
  have hv_norm : ‖v_c‖ = 1 := by
    refine hunit_norm ?_
    rw [Unitary.mem_iff]
    have hC_u := Unitary.mem_iff.mp C.eval.2
    have hzz : star z * z = 1 := by
      rw [Complex.star_def, Complex.conj_mul', ← Complex.ofReal_one]
      congr 1; nlinarith only [hz]
    constructor <;> simp [star_smul, smul_smul, hzz, mul_comm z, hC_u.1, hC_u.2]
  have hchoi_diff : ‖u_c - v_c‖ ≤ ‖unitaryEvolution H.val t - z • (C.eval : Register N)‖ := by
    have hsq : ‖u_c - v_c‖ ^ 2 ≤ ‖unitaryEvolution H.val t - z • (C.eval : Register N)‖ ^ 2 := by
      rw [EuclideanSpace.norm_sq_eq, Fintype.sum_prod_type]
      let X := unitaryEvolution H.val t - z • (C.eval : Register N)
      have hcard_eq : (Fintype.card (Config N) : ℝ) = (2 : ℝ) ^ N := by simp [Config]
      have hterm (x y : Config N) :
          ‖(u_c - v_c).ofLp (x, y)‖ ^ 2 = ((2 : ℝ) ^ N)⁻¹ * ‖X x y‖ ^ 2 := by
        dsimp [u_c, v_c, matrixNormalizedChoi, X]
        rw [← sub_div, norm_div, Complex.norm_real, Real.norm_of_nonneg (Real.sqrt_nonneg _),
          div_pow, Real.sq_sqrt (by positivity), hcard_eq, div_eq_inv_mul]
      simp_rw [hterm, ← Finset.mul_sum]
      calc ((2 : ℝ) ^ N)⁻¹ * ∑ x : Config N, ∑ y : Config N, ‖X x y‖ ^ 2
          ≤ ((2 : ℝ) ^ N)⁻¹ * (((2 : ℝ) ^ N) * ‖X‖ ^ 2) :=
            mul_le_mul_of_nonneg_left (register_frob_le_card_mul_opNorm_sq X) (inv_nonneg.mpr (by positivity))
        _ = ‖X‖ ^ 2 := by rw [← mul_assoc, inv_mul_cancel₀ (by positivity), one_mul]
    exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp hsq
  rw [hsub_eval]
  calc ‖inner ℂ W (finitePureTensorPowerEuclidean r u_c.ofLp -
        finitePureTensorPowerEuclidean r v_c.ofLp)‖
      ≤ ‖W‖ * ‖finitePureTensorPowerEuclidean r u_c.ofLp -
          finitePureTensorPowerEuclidean r v_c.ofLp‖ := norm_inner_le_norm _ _
    _ ≤ 1 * ((r : ℝ) * ‖u_c - v_c‖) := by
        rw [hW_norm]
        exact mul_le_mul_of_nonneg_left (norm_pureTensorPower_sub_le r u_c v_c hu_norm hv_norm) zero_le_one
    _ ≤ (r : ℝ) * ‖unitaryEvolution H.val t - z • (C.eval : Register N)‖ := by
        rw [one_mul]; exact mul_le_mul_of_nonneg_left hchoi_diff hr_pos.le
    _ ≤ (r : ℝ) * orbitCircuitDistance H s t + ε := by
        have hm := mul_lt_mul_of_pos_left hM_lt hr_pos
        rw [mul_add, mul_div_cancel₀ ε hr_pos.ne'] at hm
        exact hm.le

private theorem choose_totalDegree_le_pow (r s : ℕ) :
    (r * s + s * 16).choose (s * 16) ≤ (r + 16) ^ (s * 16) := by
  rcases eq_or_ne s 0 with rfl | hs_ne
  · simp
  rcases eq_or_ne r 0 with rfl | hr_ne
  · simp
  let m := r * s
  let k := s * 16
  have hm_pos : (0 : ℝ) < m := by
    dsimp [m]; exact_mod_cast Nat.mul_pos (Nat.pos_of_ne_zero hr_ne) (Nat.pos_of_ne_zero hs_ne)
  have hk_pos : (0 : ℝ) < k := by
    dsimp [k]; exact_mod_cast Nat.mul_pos (Nat.pos_of_ne_zero hs_ne) (by decide)
  let x : ℝ := (k : ℝ) / (m : ℝ)
  have hx_pos : 0 < x := div_pos hk_pos hm_pos
  have hbinom : ((m + k).choose k : ℝ) * x ^ k ≤ (1 + x) ^ (m + k) := by
    rw [add_comm (1 : ℝ) x, add_pow]
    have hmem : k ∈ Finset.range (m + k + 1) := Finset.mem_range.mpr (by omega)
    refine le_trans ?_ (Finset.single_le_sum (fun j _ => by positivity) hmem)
    simp [mul_comm]
  have h1x_pow : (1 + x) ^ (m + k) / x ^ k =
      (1 + (k : ℝ) / (m : ℝ)) ^ m * (1 + (m : ℝ) / (k : ℝ)) ^ k := by
    rw [pow_add, mul_div_assoc]
    congr 1
    rw [← div_pow]
    congr 1
    dsimp [x]; field_simp [hm_pos.ne', hk_pos.ne']; ring
  have hexp_bound : (1 + (k : ℝ) / (m : ℝ)) ^ m ≤ (3 : ℝ) ^ k := by
    calc (1 + (k : ℝ) / (m : ℝ)) ^ m
        ≤ (Real.exp ((k : ℝ) / (m : ℝ))) ^ m :=
          pow_le_pow_left₀ (by positivity) (by linarith [Real.add_one_le_exp ((k : ℝ) / (m : ℝ))]) m
      _ = Real.exp (k : ℝ) := by
          rw [← Real.exp_nat_mul]; congr 1; field_simp [hm_pos.ne']
      _ = (Real.exp 1) ^ k := by rw [← Real.exp_nat_mul, mul_one]
      _ ≤ (3 : ℝ) ^ k :=
          pow_le_pow_left₀ (Real.exp_nonneg 1) (Real.exp_one_lt_d9.le.trans (by norm_num)) k
  have hmk_eq : (m : ℝ) / (k : ℝ) = (r : ℝ) / 16 := by
    have hs_real_ne : (s : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hs_ne
    dsimp [m, k]; push_cast; field_simp [hs_real_ne]
  have hreal_le : ((m + k).choose k : ℝ) ≤ ((r + 16 : ℕ) : ℝ) ^ k := by
    have hle1 : ((m + k).choose k : ℝ) ≤ (1 + x) ^ (m + k) / x ^ k :=
      (le_div_iff₀ (pow_pos hx_pos k)).mpr hbinom
    rw [h1x_pow, hmk_eq] at hle1
    refine hle1.trans ?_
    calc (1 + (k : ℝ) / (m : ℝ)) ^ m * (1 + (r : ℝ) / 16) ^ k
        ≤ (3 : ℝ) ^ k * (1 + (r : ℝ) / 16) ^ k :=
          mul_le_mul_of_nonneg_right hexp_bound (by positivity)
      _ = (3 * (1 + (r : ℝ) / 16)) ^ k := (mul_pow _ _ k).symm
      _ ≤ ((r + 16 : ℕ) : ℝ) ^ k := by
          refine pow_le_pow_left₀ (by positivity) ?_ k
          push_cast; linarith
  exact_mod_cast hreal_le

private theorem prod_range_add_eq_factorial_mul_choose {D : ℕ} (hD : 1 ≤ D) :
    ∀ k : ℕ, (∏ i ∈ Finset.range k, (D + i)) = k.factorial * (D + k - 1).choose k
  | 0 => by simp
  | 1 => by simp [Nat.add_sub_cancel]
  | m + 2 => by
      rw [Finset.prod_range_succ, prod_range_add_eq_factorial_mul_choose hD (m + 1)]
      have h1 : D + (m + 1) - 1 = D + m := by omega
      have h2 : D + (m + 2) - 1 = D + m + 1 := by omega
      rw [h1, h2, mul_assoc]
      have hch := Nat.succ_mul_choose_eq (D + m) (m + 1)
      have hmul : (D + m).choose (m + 1) * (D + (m + 1)) =
          (m + 2) * (D + m + 1).choose (m + 2) := by
        calc (D + m).choose (m + 1) * (D + (m + 1))
            = (D + m + 1) * (D + m).choose (m + 1) := by ring
          _ = (D + m + 1).choose (m + 2) * (m + 2) := hch.symm
          _ = (m + 2) * (D + m + 1).choose (m + 2) := by ring
      rw [hmul, ← mul_assoc, Nat.factorial_succ (m + 1)]
      ring

private theorem div_pow_le_choose_multiset {D r : ℕ} (hD : 1 ≤ D) :
    (D / r) ^ r ≤ (D + r - 1).choose r := by
  rcases eq_or_ne r 0 with rfl | hr_ne
  · simp
  have hprod_le : (D / r) ^ r * r.factorial ≤ ∏ i ∈ Finset.range r, (D + i) := by
    have hfac : (D / r) ^ r * r.factorial = ∏ i ∈ Finset.range r, ((D / r) * (i + 1)) := by
      rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_range]
      congr 1
      clear hD hr_ne D
      induction r with
      | zero => simp
      | succ k ih => rw [Finset.prod_range_succ, ← ih, Nat.factorial_succ, mul_comm (k + 1)]
    rw [hfac]
    refine Finset.prod_le_prod' fun i hi => ?_
    have hi_le : i + 1 ≤ r := Finset.mem_range.mp hi
    calc (D / r) * (i + 1)
        ≤ (D / r) * r := Nat.mul_le_mul_left _ hi_le
      _ ≤ D := Nat.div_mul_le_self D r
      _ ≤ D + i := Nat.le_add_right D i
  rw [prod_range_add_eq_factorial_mul_choose hD r, mul_comm r.factorial] at hprod_le
  exact Nat.le_of_mul_le_mul_right hprod_le (Nat.factorial_pos r)

private theorem nat_lt_two_pow_sub_three : ∀ L : ℕ, 6 ≤ L → L < 2 ^ (L - 3)
  | L, hL => by
      obtain ⟨d, rfl⟩ : ∃ d, L = d + 6 := ⟨L - 6, by omega⟩
      clear hL
      induction d with
      | zero => decide
      | succ d ih =>
          have heq1 : d + 1 + 6 - 3 = (d + 6 - 3) + 1 := by omega
          rw [heq1, pow_succ]
          omega

private theorem three_mul_two_log_add_six_le : ∀ N : ℕ, 64 ≤ N → 3 * (2 * Nat.log 2 N + 6) ≤ N := by
  intro N hN
  let L := Nat.log 2 N
  have hL6 : 6 ≤ L := Nat.le_log_of_pow_le (by decide) (by norm_num; exact hN)
  have hpow_le : 2 ^ L ≤ N := Nat.pow_log_le_self 2 (by omega)
  suffices hpow_bound : 3 * (2 * L + 6) ≤ 2 ^ L by
    exact hpow_bound.trans hpow_le
  obtain ⟨d, rfl⟩ : ∃ d, L = d + 6 := ⟨L - 6, by omega⟩
  clear hL6 hpow_le L hN N
  induction d with
  | zero => decide
  | succ d ih =>
      have heq : d + 1 + 6 = (d + 6) + 1 := by omega
      rw [heq, pow_succ]
      omega

/-- Explicit polynomial-degree (`r = 192 * N * ⌊log₂ N⌋ = O(N log N)`) homogeneous Choi
annihilator strictly past the `choose(2N, 2) = N * (2 * N - 1)` matchgate barrier for all `N ≥ 64`. -/
theorem polynomial_degree_choiAnnihilator_past_matchgate {N : ℕ} (hN : 64 ≤ N)
    (H : selfAdjoint (Register N))
    (hmax : MaximallyProjectiveEnergy H.2.isHermitian.eigenvalues) :
    let s := N * (2 * N - 1) + 1
    let r := 192 * N * Nat.log 2 N
    ∃ W : EuclideanSpace ℂ (Fin r → Config N × Config N),
      ‖W‖ = 1 ∧
      (∀ (C : TwoQubitCircuit N), C.gateCount ≤ s → ∀ z : ℂ,
        evalHomogeneousChoiPoly W (z • (C.eval : Register N)) = 0) ∧
      (∃ t₀ : ℝ, evalHomogeneousChoiPoly W (unitaryEvolution H.val t₀) ≠ 0) ∧
      (∀ t : ℝ,
        ‖evalHomogeneousChoiPoly W (unitaryEvolution H.val t)‖ ≤
          (r : ℝ) * orbitCircuitDistance H s t) := by
  intro s r
  let L := Nat.log 2 N
  have hL6 : 6 ≤ L := Nat.le_log_of_pow_le (by decide) (by norm_num; exact hN)
  have hr_pos : 1 ≤ r := by dsimp [r, L]; nlinarith only [hN, hL6]
  refine exists_homogeneous_choiAnnihilator_of_carrier_lt_multiset (by omega) hr_pos H hmax ?_
  have hs_le : s ≤ 2 * N ^ 2 := by
    dsimp [s]
    have h1 : N * (2 * N - 1) + 1 ≤ N * (2 * N - 1) + N := by omega
    have h2 : N * (2 * N - 1) + N = 2 * N ^ 2 := by
      cases N with
      | zero => omega
      | succ k => ring_nf; omega
    omega
  have hN_lt : N < 2 ^ (L + 1) := Nat.lt_pow_succ_log_self (by decide) N
  have hL_pow : L < 2 ^ (L - 3) := nat_lt_two_pow_sub_three L hL6
  have hr_plus_lt : r + 16 ≤ 2 ^ (2 * L + 6) := by
    have hr_lt : 192 * N * L < 2 ^ (2 * L + 6) := by
      have heq_exp : 2 * L + 6 = 8 + (L + 1) + (L - 3) := by omega
      rw [heq_exp, pow_add, pow_add, show 2 ^ 8 = 256 by decide, mul_assoc]
      calc 192 * (N * L) ≤ 256 * (N * L) := Nat.mul_le_mul_right _ (by decide)
        _ < 256 * (2 ^ (L + 1) * 2 ^ (L - 3)) :=
            Nat.mul_lt_mul_of_pos_left (Nat.mul_lt_mul'' hN_lt hL_pow) (by decide)
    have hmod_le : r < 2 ^ (2 * L + 6) := hr_lt
    have hdvd1 : 64 ∣ r := ⟨3 * N * L, by dsimp [r]; ring⟩
    have hdvd2 : 64 ∣ 2 ^ (2 * L + 6) := by
      rw [pow_add, show 2 ^ 6 = 64 by decide, mul_comm]
      exact dvd_mul_right 64 _
    obtain ⟨a, ha⟩ := hdvd1
    obtain ⟨b, hb⟩ := hdvd2
    rw [ha, hb] at hmod_le ⊢
    have hab : a + 1 ≤ b := Nat.succ_le_of_lt (Nat.lt_of_mul_lt_mul_left hmod_le)
    nlinarith only [hab]
  have h3_log : 3 * (2 * L + 6) ≤ N := three_mul_two_log_add_six_le N hN
  have hdiv_ge : 2 ^ (N - (2 * L + 6)) ≤ 2 ^ N / r := by
    have hr_le : r ≤ 2 ^ (2 * L + 6) := (Nat.le_add_right r 16).trans hr_plus_lt
    have hmul_le : 2 ^ (N - (2 * L + 6)) * r ≤ 2 ^ N := by
      calc 2 ^ (N - (2 * L + 6)) * r
          ≤ 2 ^ (N - (2 * L + 6)) * 2 ^ (2 * L + 6) := Nat.mul_le_mul_left _ hr_le
        _ = 2 ^ (N - (2 * L + 6) + (2 * L + 6)) := (pow_add 2 _ _).symm
        _ = 2 ^ N := by congr 1; omega
    exact (Nat.le_div_iff_mul_le hr_pos).mpr hmul_le
  have h23 : 2 * N ≤ 3 * (N - (2 * L + 6)) := by omega
  have hlhs_le : (N * N) ^ s * (r * s + s * 16).choose (s * 16) ≤
      2 ^ ((68 * L + 196) * N ^ 2) := by
    calc (N * N) ^ s * (r * s + s * 16).choose (s * 16)
        ≤ (N * N) ^ s * (r + 16) ^ (s * 16) :=
          Nat.mul_le_mul_left _ (choose_totalDegree_le_pow r s)
      _ ≤ (2 ^ (L + 1) * 2 ^ (L + 1)) ^ s * (2 ^ (2 * L + 6)) ^ (s * 16) :=
          Nat.mul_le_mul
            (Nat.pow_le_pow_left (Nat.mul_le_mul hN_lt.le hN_lt.le) s)
            (Nat.pow_le_pow_left hr_plus_lt (s * 16))
      _ = 2 ^ ((2 * L + 2) * s + (2 * L + 6) * (s * 16)) := by
          rw [← pow_add, ← pow_mul, ← pow_mul, ← pow_add]
          congr 2; ring
      _ = 2 ^ ((34 * L + 98) * s) := by congr 1; ring
      _ ≤ 2 ^ ((34 * L + 98) * (2 * N ^ 2)) :=
          Nat.pow_le_pow_right (by decide) (Nat.mul_le_mul_left _ hs_le)
      _ = 2 ^ ((68 * L + 196) * N ^ 2) := by congr 1; ring
  have hrhs_ge : 2 ^ (128 * L * N ^ 2) ≤ (2 ^ N + r - 1).choose r := by
    have hexp_le : 128 * L * N ^ 2 ≤ (N - (2 * L + 6)) * r := by
      dsimp [r]
      calc 128 * L * N ^ 2 = 64 * L * N * (2 * N) := by ring
        _ ≤ 64 * L * N * (3 * (N - (2 * L + 6))) := Nat.mul_le_mul_left _ h23
        _ = (N - (2 * L + 6)) * (192 * N * L) := by ring
    calc 2 ^ (128 * L * N ^ 2)
        ≤ 2 ^ ((N - (2 * L + 6)) * r) := Nat.pow_le_pow_right (by decide) hexp_le
      _ = (2 ^ (N - (2 * L + 6))) ^ r := pow_mul 2 _ r
      _ ≤ (2 ^ N / r) ^ r := Nat.pow_le_pow_left hdiv_ge r
      _ ≤ (2 ^ N + r - 1).choose r := div_pow_le_choose_multiset (Nat.one_le_pow N 2 (by decide))
  have hexp_strict : (68 * L + 196) * N ^ 2 < 128 * L * N ^ 2 := by
    have hN2_pos : 0 < N ^ 2 := by positivity
    exact Nat.mul_lt_mul_of_pos_right (by omega) hN2_pos
  exact lt_of_le_of_lt hlhs_le
    (lt_of_lt_of_le (Nat.pow_lt_pow_right (by decide) hexp_strict) hrhs_ge)

/-! ## Section 3: Brickwork double-commutator Strang compiler and survival on `Ω_rk3(n, η)` -/

section AbstractStrang

variable {A : Type*} [CStarAlgebra A]

private theorem half_smul_add_half_smul (a : A) :
    (1 / 2 : ℝ) • a + (1 / 2 : ℝ) • a = a := by
  rw [← add_smul]; norm_num

private theorem flow_mem_unitary (x : A) (hx : x ∈ skewAdjoint A) (s : ℝ) :
    exp (s • x) ∈ unitary A :=
  exp_mem_unitary_of_mem_skewAdjoint (skewAdjoint.smul_mem s hx)

private theorem exp_mul_exp_neg_eq_one (x : A) (s : ℝ) :
    exp (s • x) * exp ((-s) • x) = 1 := by
  rw [← exp_add_of_commute ((Commute.refl x).smul_left s |>.smul_right (-s)),
    ← add_smul, add_neg_cancel, zero_smul, exp_zero]

private theorem exp_neg_mul_exp_eq_one (x : A) (s : ℝ) :
    exp ((-s) • x) * exp (s • x) = 1 := by
  rw [← exp_add_of_commute ((Commute.refl x).smul_left (-s) |>.smul_right s),
    ← add_smul, neg_add_cancel, zero_smul, exp_zero]

private theorem hasDerivAt_exp_smul_linear (x : A) (a b s : ℝ) :
    HasDerivAt (fun r : ℝ => exp ((a + b * r) • x)) (b • (exp ((a + b * s) • x) * x)) s := by
  have hd : HasDerivAt (fun r : ℝ => a + b * r) b s := by
    simpa using (hasDerivAt_const s a).add ((hasDerivAt_id s).const_mul b)
  simpa [Function.comp_def] using (hasDerivAt_exp_smul_const x (a + b * s)).scomp s hd

private theorem norm_conj_exp_sub_linear_le (z w : A) (hz : z ∈ skewAdjoint A)
    (t : ℝ) (ht : 0 ≤ t) :
    ‖exp (t • z) * w * exp ((-t) • z) - w - t • (z * w - w * z)‖ ≤
      ‖z * (z * w - w * z) - (z * w - w * z) * z‖ * t ^ 2 := by
  let cm := z * w - w * z
  let f (s : ℝ) := exp (s • z) * w * exp ((-s) • z) - w - s • cm
  let g (s : ℝ) := (exp (s • z) * cm - cm * exp (s • z)) * exp ((-s) • z)
  have hf_deriv (s : ℝ) : HasDerivAt f (g s) s := by
    have hd1 := hasDerivAt_exp_smul_const' z s
    have hd2 : HasDerivAt (fun r : ℝ => exp ((-r) • z)) ((-1 : ℝ) • (exp ((-s) • z) * z)) s := by
      simpa using hasDerivAt_exp_smul_linear z 0 (-1) s
    have hd_conj := (hd1.mul_const w).fun_mul hd2
    have hd_lin : HasDerivAt (fun r : ℝ => r • cm) cm s := by
      simpa using (hasDerivAt_id s).smul_const cm
    have hd := (hd_conj.sub_const w).sub hd_lin
    convert hd using 1
    dsimp [g, cm]
    have hcomm_z : exp ((-s) • z) * z = z * exp ((-s) • z) :=
      ((Commute.refl z).smul_left (-s)).exp_left
    have hcomm_pos : z * exp (s • z) = exp (s • z) * z :=
      ((Commute.refl z).smul_right s).exp_right
    have hmul1 : exp (s • z) * exp ((-s) • z) = 1 := exp_mul_exp_neg_eq_one z s
    rw [neg_one_smul, mul_neg, hcomm_z]
    calc z * exp (s • z) * w * exp ((-s) • z) + -(exp (s • z) * w * (z * exp ((-s) • z))) -
          (z * w - w * z)
        = z * exp (s • z) * w * exp ((-s) • z) - exp (s • z) * w * z * exp ((-s) • z) -
            (z * w - w * z) * (exp (s • z) * exp ((-s) • z)) := by
            rw [hmul1, mul_one]; simp only [mul_assoc, sub_eq_add_neg]
      _ = (exp (s • z) * (z * w - w * z) - (z * w - w * z) * exp (s • z)) * exp ((-s) • z) := by
            rw [hcomm_pos]
            simp only [sub_mul, mul_sub, mul_assoc]; abel
  have hbound (s : ℝ) (hs : s ∈ Set.Ico 0 t) :
      ‖g s‖ ≤ ‖z * cm - cm * z‖ * t := by
    dsimp only [g]
    rw [CStarRing.norm_mul_mem_unitary _ (flow_mem_unitary z hz (-s))]
    exact (norm_exp_mul_sub_mul_exp_le_commutator z cm hz s hs.1).trans
      (mul_le_mul_of_nonneg_left hs.2.le (norm_nonneg _))
  have he := norm_image_sub_le_of_norm_deriv_le_segment'
    (fun s _ => (hf_deriv s).hasDerivWithinAt) hbound t ⟨ht, le_rfl⟩
  have hf0 : f 0 = 0 := by simp [f]
  rw [hf0, sub_zero] at he
  simpa [f, cm, sq, mul_assoc] using he

/-- Unconditional `C*`-algebraic symmetric Strang double-commutator error bound: for any
skew-adjoint `x, y ∈ A` and any step `h ≥ 0` (with **no** smallness hypothesis on `h * (‖x‖ + ‖y‖)`),
`‖exp((h / 2) • x) * exp(h • y) * exp((h / 2) • x) - exp(h • (x + y))‖ ≤
  (1 / 2) * (‖[x, [x, y]]‖ + ‖[y, [y, x]]‖) * h^3`. -/
theorem norm_strang_doubleCommutator_le (x y : A)
    (hx : x ∈ skewAdjoint A) (hy : y ∈ skewAdjoint A) (h : ℝ) (hh : 0 ≤ h) :
    ‖exp ((h / 2) • x) * exp (h • y) * exp ((h / 2) • x) - exp (h • (x + y))‖ ≤
      (1 / 2) * (‖x * (x * y - y * x) - (x * y - y * x) * x‖ +
        ‖y * (y * x - x * y) - (y * x - x * y) * y‖) * h ^ 3 := by
  have hxy : x + y ∈ skewAdjoint A := (skewAdjoint A).add_mem hx hy
  let f (s : ℝ) := exp ((h - s) • (x + y)) * exp ((s / 2) • x) * exp (s • y) * exp ((s / 2) • x)
  let F_rem (s : ℝ) : A :=
    (exp ((s / 2) • x) * y * exp ((-(s / 2)) • x) - y) +
      (1 / 2 : ℝ) • (exp ((s / 2) • x) *
        (exp (s • y) * x * exp ((-s) • y) - x) * exp ((-(s / 2)) • x))
  let g (s : ℝ) : A :=
    exp ((h - s) • (x + y)) * F_rem s * exp ((s / 2) • x) * exp (s • y) * exp ((s / 2) • x)
  have hf_deriv (s : ℝ) : HasDerivAt f (g s) s := by
    have hd0 : HasDerivAt (fun r : ℝ => exp ((h - r) • (x + y)))
        (-(exp ((h - s) • (x + y)) * (x + y))) s := by
      have h1 := hasDerivAt_exp_smul_linear (x + y) h (-1) s
      rw [neg_one_smul] at h1
      simpa [sub_eq_add_neg, mul_comm] using h1
    have hd1 : HasDerivAt (fun r : ℝ => exp ((r / 2) • x))
        ((1 / 2 : ℝ) • (exp ((s / 2) • x) * x)) s := by
      have h1 := hasDerivAt_exp_smul_linear x 0 (1 / 2) s
      simpa [div_eq_inv_mul, mul_comm] using h1
    have hd2 := hasDerivAt_exp_smul_const y s
    have hd := ((hd0.fun_mul hd1).fun_mul hd2).fun_mul hd1
    convert hd using 1
    dsimp only [g, F_rem]
    have hx_comm : exp ((s / 2) • x) * x = x * exp ((s / 2) • x) :=
      ((Commute.refl x).smul_left (s / 2)).exp_left
    have hy_comm : exp (s • y) * y = y * exp (s • y) :=
      ((Commute.refl y).smul_left s).exp_left
    have hinv_x : exp ((-(s / 2)) • x) * exp ((s / 2) • x) = 1 := exp_neg_mul_exp_eq_one x (s / 2)
    have hinv_y : exp ((-s) • y) * exp (s • y) = 1 := exp_neg_mul_exp_eq_one y s
    let E_xy := exp ((h - s) • (x + y))
    let E_x := exp ((s / 2) • x)
    let E_y := exp (s • y)
    change E_xy * ((E_x * y * exp ((-(s / 2)) • x) - y) +
        (1 / 2 : ℝ) • (E_x * (E_y * x * exp ((-s) • y) - x) * exp ((-(s / 2)) • x))) *
        E_x * E_y * E_x =
      ((-(E_xy * (x + y)) * E_x + E_xy * ((1 / 2 : ℝ) • (E_x * x))) * E_y +
        (E_xy * E_x) * (E_y * y)) * E_x + (E_xy * E_x * E_y) * ((1 / 2 : ℝ) • (E_x * x))
    have hmid : ((E_x * y * exp ((-(s / 2)) • x) - y) +
        (1 / 2 : ℝ) • (E_x * (E_y * x * exp ((-s) • y) - x) * exp ((-(s / 2)) • x))) *
        E_x * E_y =
        (E_x * (y * E_y) - y * (E_x * E_y)) +
          ((1 / 2 : ℝ) • (E_x * (E_y * x)) - (1 / 2 : ℝ) • (x * (E_x * E_y))) := by
      rw [add_mul, add_mul, sub_mul, sub_mul, Algebra.smul_mul_assoc, Algebra.smul_mul_assoc,
        mul_assoc (E_x * y) (exp ((-(s / 2)) • x)) E_x, hinv_x, mul_one,
        mul_assoc (E_x * (E_y * x * exp ((-s) • y) - x)) (exp ((-(s / 2)) • x)) E_x, hinv_x, mul_one,
        mul_sub E_x, sub_mul,
        mul_assoc E_x (E_y * x * exp ((-s) • y)) E_y,
        mul_assoc (E_y * x) (exp ((-s) • y)) E_y, hinv_y, mul_one,
        show E_x * x = x * E_x from hx_comm, smul_sub]
      simp only [mul_assoc]
    have hlhs_assoc : E_xy * ((E_x * y * exp ((-(s / 2)) • x) - y) +
        (1 / 2 : ℝ) • (E_x * (E_y * x * exp ((-s) • y) - x) * exp ((-(s / 2)) • x))) *
        E_x * E_y * E_x =
        E_xy * (((E_x * y * exp ((-(s / 2)) • x) - y) +
          (1 / 2 : ℝ) • (E_x * (E_y * x * exp ((-s) • y) - x) * exp ((-(s / 2)) • x))) *
          E_x * E_y) * E_x := by
      simp only [mul_assoc]
    rw [hlhs_assoc, hmid, show E_y * y = y * E_y from hy_comm, show E_x * x = x * E_x from hx_comm]
    simp only [mul_add, add_mul, mul_sub, sub_mul, neg_mul,
      Algebra.mul_smul_comm, Algebra.smul_mul_assoc, mul_assoc]
    rw [← half_smul_add_half_smul (E_xy * (x * (E_x * (E_y * E_x))))]
    abel
  have hbound (s : ℝ) (hs : s ∈ Set.Ico 0 h) :
      ‖g s‖ ≤ (1 / 2) * (‖x * (x * y - y * x) - (x * y - y * x) * x‖ +
        ‖y * (y * x - x * y) - (y * x - x * y) * y‖) * h ^ 2 := by
    have hs0 : 0 ≤ s := hs.1
    have hsh : s ≤ h := hs.2.le
    dsimp only [g]
    rw [CStarRing.norm_mul_mem_unitary _ (flow_mem_unitary x hx (s / 2)),
      CStarRing.norm_mul_mem_unitary _ (flow_mem_unitary y hy s),
      CStarRing.norm_mul_mem_unitary _ (flow_mem_unitary x hx (s / 2)),
      CStarRing.norm_mem_unitary_mul _ (flow_mem_unitary (x + y) hxy (h - s))]
    let A₁ := exp ((s / 2) • x) * y * exp ((-(s / 2)) • x) - y - (s / 2) • (x * y - y * x)
    let A₂ := (1 / 2 : ℝ) • (exp ((s / 2) • x) *
      (exp (s • y) * x * exp ((-s) • y) - x - s • (y * x - x * y)) * exp ((-(s / 2)) • x))
    let A₃ := (s / 2) • (exp ((s / 2) • x) * (y * x - x * y) * exp ((-(s / 2)) • x) - (y * x - x * y))
    have hF_split : F_rem s = A₁ + A₂ + A₃ := by
      dsimp only [F_rem, A₁, A₂, A₃]
      rw [mul_sub (exp ((s / 2) • x)), sub_mul, Algebra.mul_smul_comm, Algebra.smul_mul_assoc,
        smul_sub, smul_smul, show (1 / 2 : ℝ) * s = s / 2 by ring, smul_sub]
      have hcomm_anti : (s / 2) • (x * y - y * x) + (s / 2) • (y * x - x * y) = 0 := by
        rw [← smul_add, show (x * y - y * x) + (y * x - x * y) = 0 by abel, smul_zero]
      calc (exp ((s / 2) • x) * y * exp ((-(s / 2)) • x) - y) +
            (1 / 2 : ℝ) • (exp ((s / 2) • x) * (exp (s • y) * x * exp ((-s) • y) - x) *
              exp ((-(s / 2)) • x))
          = (exp ((s / 2) • x) * y * exp ((-(s / 2)) • x) - y) +
              (1 / 2 : ℝ) • (exp ((s / 2) • x) * (exp (s • y) * x * exp ((-s) • y) - x) *
                exp ((-(s / 2)) • x)) -
              ((s / 2) • (x * y - y * x) + (s / 2) • (y * x - x * y)) := by
            rw [hcomm_anti, sub_zero]
        _ = _ := by abel
    have hA₁ : ‖A₁‖ ≤ (1 / 4) * ‖x * (x * y - y * x) - (x * y - y * x) * x‖ * s ^ 2 := by
      have h1 := norm_conj_exp_sub_linear_le x y hx (s / 2) (half_nonneg hs0)
      dsimp only [A₁]
      linarith only [h1]
    have hA₂ : ‖A₂‖ ≤ (1 / 2) * ‖y * (y * x - x * y) - (y * x - x * y) * y‖ * s ^ 2 := by
      dsimp only [A₂]
      rw [norm_smul, Real.norm_of_nonneg (by norm_num),
        CStarRing.norm_mul_mem_unitary _ (flow_mem_unitary x hx (-(s / 2))),
        CStarRing.norm_mem_unitary_mul _ (flow_mem_unitary x hx (s / 2))]
      have h1 := norm_conj_exp_sub_linear_le y x hy s hs0
      linarith only [h1]
    have hA₃ : ‖A₃‖ ≤ (1 / 4) * ‖x * (x * y - y * x) - (x * y - y * x) * x‖ * s ^ 2 := by
      dsimp only [A₃]
      rw [norm_smul, Real.norm_of_nonneg (half_nonneg hs0)]
      have hunit_eq : exp ((s / 2) • x) * (y * x - x * y) * exp ((-(s / 2)) • x) - (y * x - x * y) =
          (exp ((s / 2) • x) * (y * x - x * y) - (y * x - x * y) * exp ((s / 2) • x)) *
            exp ((-(s / 2)) • x) := by
        rw [sub_mul, mul_assoc (y * x - x * y), exp_mul_exp_neg_eq_one x (s / 2), mul_one]
      rw [hunit_eq, CStarRing.norm_mul_mem_unitary _ (flow_mem_unitary x hx (-(s / 2)))]
      have h1 := norm_exp_mul_sub_mul_exp_le_commutator x (y * x - x * y) hx (s / 2) (half_nonneg hs0)
      have hnorm_eq : ‖x * (y * x - x * y) - (y * x - x * y) * x‖ =
          ‖x * (x * y - y * x) - (x * y - y * x) * x‖ := by
        rw [← norm_neg]
        congr 1; simp only [mul_sub, sub_mul, mul_assoc]; abel
      rw [hnorm_eq] at h1
      nlinarith only [h1, hs0]
    have hs_sq_le : s ^ 2 ≤ h ^ 2 := pow_le_pow_left₀ hs0 hsh 2
    rw [hF_split]
    have htri := (norm_add_le (A₁ + A₂) A₃).trans (add_le_add (norm_add_le A₁ A₂) le_rfl)
    have hsum_s : ‖A₁‖ + ‖A₂‖ + ‖A₃‖ ≤
        (1 / 2) * (‖x * (x * y - y * x) - (x * y - y * x) * x‖ +
          ‖y * (y * x - x * y) - (y * x - x * y) * y‖) * s ^ 2 := by
      linarith only [hA₁, hA₂, hA₃]
    exact htri.trans (hsum_s.trans (mul_le_mul_of_nonneg_left hs_sq_le (by positivity)))
  have he := norm_image_sub_le_of_norm_deriv_le_segment'
    (fun s _ => (hf_deriv s).hasDerivWithinAt) hbound h ⟨hh, le_rfl⟩
  have hf0 : f 0 = exp (h • (x + y)) := by simp [f]
  have hfh : f h = exp ((h / 2) • x) * exp (h • y) * exp ((h / 2) • x) := by simp [f]
  rw [hf0, hfh] at he
  calc ‖exp ((h / 2) • x) * exp (h • y) * exp ((h / 2) • x) - exp (h • (x + y))‖
      ≤ (1 / 2) * (‖x * (x * y - y * x) - (x * y - y * x) * x‖ +
          ‖y * (y * x - x * y) - (y * x - x * y) * y‖) * h ^ 2 * (h - 0) := he
    _ = (1 / 2) * (‖x * (x * y - y * x) - (x * y - y * x) * x‖ +
          ‖y * (y * x - x * y) - (y * x - x * y) * y‖) * h ^ 3 := by ring

/-- Repeated `m`-step symmetric Strang double-commutator error bound in any `C*`-algebra `A`. -/
theorem norm_strang_pow_doubleCommutator_le (x y : A)
    (hx : x ∈ skewAdjoint A) (hy : y ∈ skewAdjoint A)
    (t : ℝ) (ht : 0 ≤ t) (m : ℕ) (hm : 0 < m) :
    ‖(exp ((t / (2 * (m : ℝ))) • x) * exp ((t / (m : ℝ)) • y) *
        exp ((t / (2 * (m : ℝ))) • x)) ^ m - exp (t • (x + y))‖ ≤
      (1 / 2) * (‖x * (x * y - y * x) - (x * y - y * x) * x‖ +
        ‖y * (y * x - x * y) - (y * x - x * y) * y‖) * t ^ 3 / (m : ℝ) ^ 2 := by
  let h := t / (m : ℝ)
  have hm_pos : (0 : ℝ) < m := by exact_mod_cast hm
  have hh0 : 0 ≤ h := div_nonneg ht hm_pos.le
  have hh2 : t / (2 * (m : ℝ)) = h / 2 := by dsimp [h]; ring
  rw [hh2]
  let S := exp ((h / 2) • x) * exp (h • y) * exp ((h / 2) • x)
  let E := exp (h • (x + y))
  have hS_u : S ∈ unitary A :=
    mul_mem (mul_mem (flow_mem_unitary x hx (h / 2)) (flow_mem_unitary y hy h))
      (flow_mem_unitary x hx (h / 2))
  have hE_u : E ∈ unitary A := flow_mem_unitary (x + y) ((skewAdjoint A).add_mem hx hy) h
  have hE_pow : E ^ m = exp (t • (x + y)) := by
    dsimp [E, h]; rw [exp_real_smul_pow]; congr 2; field_simp [hm_pos.ne']
  rw [← hE_pow]
  calc ‖S ^ m - E ^ m‖
      ≤ (m : ℝ) * ‖S - E‖ := unitary_pow_norm_sub_pow_le S E hS_u hE_u m
    _ ≤ (m : ℝ) * ((1 / 2) * (‖x * (x * y - y * x) - (x * y - y * x) * x‖ +
          ‖y * (y * x - x * y) - (y * x - x * y) * y‖) * h ^ 3) :=
        mul_le_mul_of_nonneg_left (norm_strang_doubleCommutator_le x y hx hy h hh0) hm_pos.le
    _ = (1 / 2) * (‖x * (x * y - y * x) - (x * y - y * x) * x‖ +
          ‖y * (y * x - x * y) - (y * x - x * y) * y‖) * t ^ 3 / (m : ℝ) ^ 2 := by
        dsimp [h]; field_simp [hm_pos.ne']

end AbstractStrang

section BrickworkStrang

local instance (N : ℕ) : CStarAlgebra (Register N) where

private theorem shorter_parity_fin (m : ℕ) :
    ∃ S : Finset (Fin m), 2 * S.card ≤ m ∧
      (∀ i ∈ S, ∀ j ∈ S, i.val % 2 = j.val % 2) ∧
      (∀ i ∈ Sᶜ, ∀ j ∈ Sᶜ, i.val % 2 = j.val % 2) := by
  classical
  let E := Finset.univ.filter (fun i : Fin m => i.val % 2 = 0)
  have he (i : Fin m) : i ∈ E ↔ i.val % 2 = 0 := by simp [E]
  have ev : ∀ i ∈ E, ∀ j ∈ E, i.val % 2 = j.val % 2 := fun i hi j hj =>
    ((he i).mp hi).trans ((he j).mp hj).symm
  have od : ∀ i ∈ Eᶜ, ∀ j ∈ Eᶜ, i.val % 2 = j.val % 2 := by
    intro i hi j hj
    have hi' := (he i).not.mp (Finset.mem_compl.mp hi)
    have hj' := (he j).not.mp (Finset.mem_compl.mp hj)
    omega
  have hcard : E.card + Eᶜ.card = m := by
    simpa only [Fintype.card_fin] using Finset.card_add_card_compl E
  by_cases h : 2 * E.card ≤ m
  · exact ⟨E, h, ev, od⟩
  · exact ⟨Eᶜ, by omega, od, by simpa only [compl_compl] using ev⟩

private theorem onsite_termBond_mem_endpoints {n : ℕ} (v : Fin (n + 2)) (q : Fin 3) :
    v ∈ ({(BondCoordinates.termBond (.inl (v, q) : PathLabel n)).castSucc,
      (BondCoordinates.termBond (.inl (v, q) : PathLabel n)).succ} : Finset (Fin (n + 2))) := by
  classical
  let e := BondCoordinates.termBond (.inl (v, 0) : PathLabel n)
  have hq_eq : BondCoordinates.termBond (.inl (v, q) : PathLabel n) = e := rfl
  rw [hq_eq]
  by_contra hv_not
  let u₀ : PathShell n := PiLp.single 2 (.inl (v, 0)) 1
  obtain ⟨B₀, hB₀⟩ := BondCoordinates.exists_local_blocks u₀
  have hsum_eq := hB₀ e
  have hrhs : (∑ l : PathLabel n,
      if BondCoordinates.termBond l = e then ((u₀ l : ℝ) : ℂ) • finitePauliMatrix (pathWord l) else 0) =
      finitePauliMatrix (pathWord (.inl (v, 0))) := by
    rw [Finset.sum_eq_single (.inl (v, 0))]
    · have hu1 : u₀ (.inl (v, 0)) = 1 := by simp [u₀, PiLp.single_apply]
      rw [if_pos rfl, hu1, Complex.ofReal_one, one_smul]
    · intro l _ hl_ne
      have hu0 : u₀ l = 0 := by simp [u₀, PiLp.single_apply, hl_ne]
      split_ifs <;> simp [hu0]
    · intro h; exact (h (Finset.mem_univ _)).elim
  rw [hrhs] at hsum_eq
  have hsupp := lift_supported_pair e.castSucc e.succ (BondProducts.endpoints_ne e) (B₀ e).val
  rw [hsum_eq] at hsupp
  let x₀ : Config (n + 2) := fun _ => false
  let y₀ : Config (n + 2) := Function.update x₀ v true
  have hzero := hsupp.1 x₀ y₀ ⟨v, hv_not, by simp [x₀, y₀]⟩
  have hnonzero : finitePauliMatrix (pathWord (.inl (v, 0))) x₀ y₀ = 1 := by
    change (∏ i : Fin (n + 2), boolPauliOptionEntry (onsiteWord v 0 i) (x₀ i, y₀ i)) = 1
    rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ v)]
    have hv_val : boolPauliOptionEntry (onsiteWord v 0 v) (x₀ v, y₀ v) = 1 := by
      simp [onsiteWord, x₀, y₀, boolPauliOptionEntry, boolPauliOption, finiteQubitPauli]
    have hrest_val : (∏ i ∈ Finset.univ.erase v,
        boolPauliOptionEntry (onsiteWord v 0 i) (x₀ i, y₀ i)) = 1 :=
      Finset.prod_eq_one fun i hi => by
        have hne : i ≠ v := Finset.ne_of_mem_erase hi
        simp [onsiteWord, hne, x₀, y₀, boolPauliOptionEntry, boolPauliOption]
    rw [hv_val, hrest_val, one_mul]
  rw [hnonzero] at hzero
  exact one_ne_zero hzero

private theorem card_filter_termBond_le_fifteen {n : ℕ} (e : Fin (n + 1)) :
    (Finset.univ.filter fun l : PathLabel n => BondCoordinates.termBond l = e).card ≤ 15 := by
  classical
  let S_inl : Finset (PathLabel n) :=
    (({e.castSucc, e.succ} : Finset (Fin (n + 2))) ×ˢ (Finset.univ : Finset (Fin 3))).map
      ⟨Sum.inl, Sum.inl_injective⟩
  let S_inr : Finset (PathLabel n) :=
    (({e} : Finset (Fin (n + 1))) ×ˢ (Finset.univ : Finset (Fin 3 × Fin 3))).map
      ⟨Sum.inr, Sum.inr_injective⟩
  have hsub : (Finset.univ.filter fun l : PathLabel n => BondCoordinates.termBond l = e) ⊆
      S_inl ∪ S_inr := by
    intro l hl
    have htb : BondCoordinates.termBond l = e := (Finset.mem_filter.mp hl).2
    rcases l with ⟨v, q⟩ | ⟨e', pq⟩
    · apply Finset.mem_union_left
      rw [Finset.mem_map]
      refine ⟨(v, q), Finset.mem_product.mpr ⟨?_, Finset.mem_univ q⟩, rfl⟩
      have hmem := onsite_termBond_mem_endpoints v q
      rwa [htb] at hmem
    · apply Finset.mem_union_right
      rw [Finset.mem_map]
      dsimp [BondCoordinates.termBond] at htb
      exact ⟨(e', pq), Finset.mem_product.mpr ⟨Finset.mem_singleton.mpr htb, Finset.mem_univ pq⟩, rfl⟩
  have hc_inl : S_inl.card ≤ 6 := by
    dsimp [S_inl]
    rw [Finset.card_map, Finset.card_product, Finset.card_univ, Fintype.card_fin]
    have hc2 : ({e.castSucc, e.succ} : Finset (Fin (n + 2))).card ≤ 2 := Finset.card_insert_le _ _
    omega
  have hc_inr : S_inr.card = 9 := by
    dsimp [S_inr]
    rw [Finset.card_map, Finset.card_product, Finset.card_singleton, Finset.card_univ,
      Fintype.card_prod, Fintype.card_fin]
  exact (Finset.card_le_card hsub).trans ((Finset.card_union_le _ _).trans (by omega))

private theorem bond_generator_commute_of_dist_ge_two {n : ℕ} {e f : Fin (n + 1)}
    (hdist : e.val + 2 ≤ f.val ∨ f.val + 2 ≤ e.val)
    (B D : selfAdjoint BondCoordinates.LocalMatrix) :
    Commute (BondProducts.Symmetric.generator e B) (BondProducts.Symmetric.generator f D) := by
  have dis : Disjoint ({e.castSucc, e.succ} : Finset (Fin (n + 2))) {f.castSucc, f.succ} := by
    apply Finset.disjoint_left.mpr
    intro i hi hj
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj
    rcases hi with rfl | rfl <;> rcases hj with hj | hj <;>
      have he := congrArg Fin.val hj <;> simp only [Fin.val_castSucc, Fin.val_succ] at he <;> omega
  exact ((commute_of_isSiteSupported_disjoint dis
    (lift_supported_pair _ _ (BondProducts.endpoints_ne e) B.val)
    (lift_supported_pair _ _ (BondProducts.endpoints_ne f) D.val)).smul_left _).smul_right _

private theorem card_close_bonds_le {m d : ℕ} (c : ℕ) :
    (Finset.univ.filter fun j : Fin m => j.val ≤ c + d ∧ c ≤ j.val + d).card ≤ 2 * d + 1 := by
  let S_nat : Finset ℕ := Finset.Icc (c - d) (c + d)
  have hsub : (Finset.univ.filter fun j : Fin m => j.val ≤ c + d ∧ c ≤ j.val + d).image Fin.val ⊆
      S_nat := by
    intro k hk
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hk
    have hcond := (Finset.mem_filter.mp hj).2
    exact Finset.mem_Icc.mpr ⟨by omega, hcond.1⟩
  have hinj : Function.Injective (Fin.val : Fin m → ℕ) := Fin.ext
  rw [← Finset.card_image_of_injective _ hinj]
  refine (Finset.card_le_card hsub).trans ?_
  dsimp [S_nat]
  rw [Nat.card_Icc]
  omega

private theorem norm_bond_doubleCommutator_le {n : ℕ}
    (Z : Fin (n + 1) → Register (n + 2))
    {B_max : ℝ} (hB0 : 0 ≤ B_max) (hZ_norm : ∀ e, ‖Z e‖ ≤ B_max)
    (hZ_comm : ∀ e f : Fin (n + 1), (e.val + 2 ≤ f.val ∨ f.val + 2 ≤ e.val) → Commute (Z e) (Z f))
    (A_set B_set : Finset (Fin (n + 1))) :
    let X := ∑ e ∈ A_set, Z e
    let Y := ∑ f ∈ B_set, Z f
    ‖X * (X * Y - Y * X) - (X * Y - Y * X) * X‖ ≤ 60 * ((n + 1 : ℕ) : ℝ) * B_max ^ 3 := by
  intro X Y
  have htrilinear : X * (X * Y - Y * X) - (X * Y - Y * X) * X =
      ∑ e ∈ A_set, ∑ f ∈ B_set, ∑ e' ∈ A_set,
        (Z e' * (Z e * Z f - Z f * Z e) - (Z e * Z f - Z f * Z e) * Z e') := by
    dsimp only [X, Y]
    have hXY : (∑ e ∈ A_set, Z e) * (∑ f ∈ B_set, Z f) - (∑ f ∈ B_set, Z f) * (∑ e ∈ A_set, Z e) =
        ∑ e ∈ A_set, ∑ f ∈ B_set, (Z e * Z f - Z f * Z e) := by
      rw [Finset.sum_mul, Finset.mul_sum]
      simp_rw [Finset.mul_sum, Finset.sum_mul]
      rw [Finset.sum_comm (s := B_set), ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun e _ => (Finset.sum_sub_distrib _ _).symm
    rw [hXY, Finset.sum_mul, Finset.mul_sum]
    simp_rw [Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm (t := A_set)]
    refine Finset.sum_congr rfl fun e _ => ?_
    rw [Finset.sum_comm (t := B_set), ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun f _ => (Finset.sum_sub_distrib _ _).symm
  rw [htrilinear]
  have hsingle_term (e f e' : Fin (n + 1)) :
      ‖Z e' * (Z e * Z f - Z f * Z e) - (Z e * Z f - Z f * Z e) * Z e'‖ ≤ 4 * B_max ^ 3 := by
    have hcm : ‖Z e * Z f - Z f * Z e‖ ≤ 2 * B_max ^ 2 := by
      calc ‖Z e * Z f - Z f * Z e‖
          ≤ ‖Z e * Z f‖ + ‖Z f * Z e‖ := norm_sub_le _ _
        _ ≤ ‖Z e‖ * ‖Z f‖ + ‖Z f‖ * ‖Z e‖ := add_le_add (norm_mul_le _ _) (norm_mul_le _ _)
        _ ≤ B_max * B_max + B_max * B_max :=
            add_le_add (mul_le_mul (hZ_norm e) (hZ_norm f) (norm_nonneg _) hB0)
              (mul_le_mul (hZ_norm f) (hZ_norm e) (norm_nonneg _) hB0)
        _ = 2 * B_max ^ 2 := by ring
    calc ‖Z e' * (Z e * Z f - Z f * Z e) - (Z e * Z f - Z f * Z e) * Z e'‖
        ≤ ‖Z e'‖ * ‖Z e * Z f - Z f * Z e‖ + ‖Z e * Z f - Z f * Z e‖ * ‖Z e'‖ :=
          (norm_sub_le _ _).trans (add_le_add (norm_mul_le _ _) (norm_mul_le _ _))
      _ ≤ B_max * (2 * B_max ^ 2) + (2 * B_max ^ 2) * B_max :=
          add_le_add (mul_le_mul (hZ_norm e') hcm (norm_nonneg _) hB0)
            (mul_le_mul hcm (hZ_norm e') (norm_nonneg _) (by positivity))
      _ = 4 * B_max ^ 3 := by ring
  have hper_e (e : Fin (n + 1)) :
      ‖∑ f ∈ B_set, ∑ e' ∈ A_set,
        (Z e' * (Z e * Z f - Z f * Z e) - (Z e * Z f - Z f * Z e) * Z e')‖ ≤ 60 * B_max ^ 3 := by
    let Nf := Finset.univ.filter fun f : Fin (n + 1) => f.val ≤ e.val + 1 ∧ e.val ≤ f.val + 1
    let Ne' := Finset.univ.filter fun e' : Fin (n + 1) => e'.val ≤ e.val + 2 ∧ e.val ≤ e'.val + 2
    refine (norm_sum_le _ _).trans ?_
    have hf_vanish (f : Fin (n + 1)) (hf_not : f ∉ Nf) :
        ‖∑ e' ∈ A_set, (Z e' * (Z e * Z f - Z f * Z e) - (Z e * Z f - Z f * Z e) * Z e')‖ = 0 := by
      have hdist : e.val + 2 ≤ f.val ∨ f.val + 2 ≤ e.val := by
        simp only [Nf, Finset.mem_filter, Finset.mem_univ, true_and] at hf_not
        omega
      have h0 : Z e * Z f - Z f * Z e = 0 := sub_eq_zero.mpr (hZ_comm e f hdist).eq
      simp [h0]
    have hsum_f_le : (∑ f ∈ B_set, ‖∑ e' ∈ A_set,
        (Z e' * (Z e * Z f - Z f * Z e) - (Z e * Z f - Z f * Z e) * Z e')‖) ≤
        ∑ f ∈ Nf, ‖∑ e' ∈ A_set,
          (Z e' * (Z e * Z f - Z f * Z e) - (Z e * Z f - Z f * Z e) * Z e')‖ := by
      rw [← Finset.sum_filter_add_sum_filter_not B_set (fun f => f ∈ Nf)]
      have h2 : (∑ f ∈ B_set.filter (fun f => f ∉ Nf), ‖∑ e' ∈ A_set,
          (Z e' * (Z e * Z f - Z f * Z e) - (Z e * Z f - Z f * Z e) * Z e')‖) = 0 :=
        Finset.sum_eq_zero fun f hf => hf_vanish f (Finset.mem_filter.mp hf).2
      rw [h2, add_zero]
      exact Finset.sum_le_sum_of_subset_of_nonneg
        (fun f hf => (Finset.mem_filter.mp hf).2) (fun _ _ _ => norm_nonneg _)
    refine hsum_f_le.trans ?_
    have hinner_f (f : Fin (n + 1)) (hf : f ∈ Nf) :
        ‖∑ e' ∈ A_set, (Z e' * (Z e * Z f - Z f * Z e) - (Z e * Z f - Z f * Z e) * Z e')‖ ≤
          20 * B_max ^ 3 := by
      have hf_cond := (Finset.mem_filter.mp hf).2
      refine (norm_sum_le _ _).trans ?_
      have he'_vanish (e' : Fin (n + 1)) (he'_not : e' ∉ Ne') :
          ‖Z e' * (Z e * Z f - Z f * Z e) - (Z e * Z f - Z f * Z e) * Z e'‖ = 0 := by
        simp only [Ne', Finset.mem_filter, Finset.mem_univ, true_and] at he'_not
        have hd_e : e'.val + 2 ≤ e.val ∨ e.val + 2 ≤ e'.val := by omega
        have hd_f : e'.val + 2 ≤ f.val ∨ f.val + 2 ≤ e'.val := by omega
        have hc1 := hZ_comm e' e hd_e
        have hc2 := hZ_comm e' f hd_f
        have hcomm_sub : Commute (Z e') (Z e * Z f - Z f * Z e) :=
          (hc1.mul_right hc2).sub_right (hc2.mul_right hc1)
        rw [sub_eq_zero.mpr hcomm_sub.eq, norm_zero]
      rw [← Finset.sum_filter_add_sum_filter_not A_set (fun e' => e' ∈ Ne')]
      have h2 : (∑ e' ∈ A_set.filter (fun e' => e' ∉ Ne'),
          ‖Z e' * (Z e * Z f - Z f * Z e) - (Z e * Z f - Z f * Z e) * Z e'‖) = 0 :=
        Finset.sum_eq_zero fun e' he' => he'_vanish e' (Finset.mem_filter.mp he').2
      rw [h2, add_zero]
      calc (∑ e' ∈ A_set.filter (fun e' => e' ∈ Ne'),
            ‖Z e' * (Z e * Z f - Z f * Z e) - (Z e * Z f - Z f * Z e) * Z e'‖)
          ≤ ∑ e' ∈ Ne',
              ‖Z e' * (Z e * Z f - Z f * Z e) - (Z e * Z f - Z f * Z e) * Z e'‖ :=
            Finset.sum_le_sum_of_subset_of_nonneg
              (fun e' he' => (Finset.mem_filter.mp he').2) (fun _ _ _ => norm_nonneg _)
        _ ≤ ∑ _e' ∈ Ne', (4 * B_max ^ 3) :=
            Finset.sum_le_sum fun e' _ => hsingle_term e f e'
        _ = (Ne'.card : ℝ) * (4 * B_max ^ 3) := by simp
        _ ≤ 5 * (4 * B_max ^ 3) := by
            have hc5 : Ne'.card ≤ 5 := card_close_bonds_le e.val (d := 2)
            exact mul_le_mul_of_nonneg_right (by exact_mod_cast hc5) (by positivity)
        _ = 20 * B_max ^ 3 := by ring
    calc (∑ f ∈ Nf, ‖∑ e' ∈ A_set,
            (Z e' * (Z e * Z f - Z f * Z e) - (Z e * Z f - Z f * Z e) * Z e')‖)
        ≤ ∑ _f ∈ Nf, (20 * B_max ^ 3) := Finset.sum_le_sum hinner_f
      _ = (Nf.card : ℝ) * (20 * B_max ^ 3) := by simp
      _ ≤ 3 * (20 * B_max ^ 3) := by
          have hc3 : Nf.card ≤ 3 := card_close_bonds_le e.val (d := 1)
          exact mul_le_mul_of_nonneg_right (by exact_mod_cast hc3) (by positivity)
      _ = 60 * B_max ^ 3 := by ring
  calc ‖∑ e ∈ A_set, ∑ f ∈ B_set, ∑ e' ∈ A_set,
        (Z e' * (Z e * Z f - Z f * Z e) - (Z e * Z f - Z f * Z e) * Z e')‖
      ≤ ∑ e ∈ A_set, ‖∑ f ∈ B_set, ∑ e' ∈ A_set,
          (Z e' * (Z e * Z f - Z f * Z e) - (Z e * Z f - Z f * Z e) * Z e')‖ := norm_sum_le _ _
    _ ≤ ∑ _e ∈ A_set, (60 * B_max ^ 3) := Finset.sum_le_sum fun e _ => hper_e e
    _ = (A_set.card : ℝ) * (60 * B_max ^ 3) := by simp
    _ ≤ ((n + 1 : ℕ) : ℝ) * (60 * B_max ^ 3) := by
        have hcard_le : A_set.card ≤ n + 1 := (Finset.card_le_univ A_set).trans_eq (Fintype.card_fin _)
        exact mul_le_mul_of_nonneg_right (by exact_mod_cast hcard_le) (by positivity)
    _ = 60 * ((n + 1 : ℕ) : ℝ) * B_max ^ 3 := by ring

/-- Brickwork double-commutator Strang compiler on `PathShell n` (`N = n + 2`): `N` symmetric
parity-bond sweeps use **strictly fewer than `N * (2 * N - 1) = choose(2N, 2)`** two-qubit gates and
approximate `unitaryEvolution (pathHamiltonian u) t` within projective operator-norm error
`≤ 202500 * M^3 * t^3 / (n + 2)` whenever `∀ l, |u l| ≤ M` (`M ≥ 0`, `t ≥ 0`). -/
theorem strang_brickwork_pathHamiltonian_approx {n : ℕ} (u : PathShell n)
    {M : ℝ} (hM0 : 0 ≤ M) (hu : ∀ l : PathLabel n, |u l| ≤ M)
    {t : ℝ} (ht0 : 0 ≤ t) :
    ∃ z : ℂ, ‖z‖ = 1 ∧ ∃ C : TwoQubitCircuit (n + 2),
      C.gateCount < (n + 2) * (2 * (n + 2) - 1) ∧
      ‖unitaryEvolution (pathHamiltonian u) t - z • (C.eval : Register (n + 2))‖ ≤
        202500 * M ^ 3 * t ^ 3 / ((n + 2 : ℕ) : ℝ) := by
  classical
  obtain ⟨B, hB_loc⟩ := BondCoordinates.exists_local_blocks u
  have hB_sum : pathHamiltonian u =
      ∑ e : Fin (n + 1), twoQubitLiftMatrix e.castSucc e.succ (BondProducts.endpoints_ne e) (B e).val := by
    simp only [hB_loc, Finset.sum_comm (s := Finset.univ (α := Fin (n + 1)))
      (t := Finset.univ (α := PathLabel n)), Finset.sum_ite_eq, Finset.mem_univ, if_true,
      pathHamiltonian_eq_sum]
  obtain ⟨S, hS_card, hS_par, hSc_par⟩ := shorter_parity_fin (n + 1)
  let Z (e : Fin (n + 1)) := BondProducts.Symmetric.generator e (B e)
  let X := ∑ e ∈ S, Z e
  let Y := ∑ f ∈ Sᶜ, Z f
  have hsum_XY : X + Y = (-Complex.I) • pathHamiltonian u := by
    dsimp only [X, Y, Z, BondProducts.Symmetric.generator]
    rw [Finset.sum_add_sum_compl, hB_sum, Finset.smul_sum]
  have hX_skew : X ∈ skewAdjoint (Register (n + 2)) :=
    (skewAdjoint _).sum_mem fun e _ => BondProducts.Symmetric.generator_skew e (B e)
  have hY_skew : Y ∈ skewAdjoint (Register (n + 2)) :=
    (skewAdjoint _).sum_mem fun e _ => BondProducts.Symmetric.generator_skew e (B e)
  have hZ_norm (e : Fin (n + 1)) : ‖Z e‖ ≤ 15 * M := by
    dsimp only [Z, BondProducts.Symmetric.generator]
    rw [norm_smul, norm_neg, Complex.norm_I, one_mul, hB_loc e, ← Finset.sum_filter]
    refine (norm_sum_le _ _).trans ?_
    calc (∑ l ∈ Finset.univ.filter (fun l => BondCoordinates.termBond l = e),
            ‖((u l : ℝ) : ℂ) • finitePauliMatrix (pathWord l)‖)
        ≤ ∑ _l ∈ Finset.univ.filter (fun l => BondCoordinates.termBond l = e), M := by
          refine Finset.sum_le_sum fun l _ => ?_
          rw [norm_smul, Complex.norm_real, Real.norm_eq_abs]
          have hp_u : finitePauliMatrix (pathWord l) ∈ unitary (Register (n + 2)) := by
            rw [Unitary.mem_iff, star_eq_conjTranspose, (finitePauliMatrix_isHermitian _).eq]
            exact ⟨finitePauliMatrix_mul_self _, finitePauliMatrix_mul_self _⟩
          rw [CStarRing.norm_of_mem_unitary hp_u, mul_one]
          exact hu l
      _ = ((Finset.univ.filter (fun l => BondCoordinates.termBond l = e)).card : ℝ) * M := by simp
      _ ≤ 15 * M := mul_le_mul_of_nonneg_right
          (by exact_mod_cast card_filter_termBond_le_fifteen e) hM0
  have hcomm_XXY := norm_bond_doubleCommutator_le Z (by positivity) hZ_norm
    (fun e f h => bond_generator_commute_of_dist_ge_two h (B e) (B f)) S Sᶜ
  have hcomm_YYX := norm_bond_doubleCommutator_le Z (by positivity) hZ_norm
    (fun e f h => bond_generator_commute_of_dist_ge_two h (B e) (B f)) Sᶜ S
  let m : ℕ := n + 2
  have hm_pos : 0 < m := by dsimp [m]; omega
  let h := t / (m : ℝ)
  have ha_layer := BondProducts.Symmetric.compile_layer B S hS_par (h / 2)
  have hb_layer := BondProducts.Symmetric.compile_layer B Sᶜ hSc_par h
  have hstep_approx := LocalPatches.approx_product
    (exp_mem_unitary_of_mem_skewAdjoint (skewAdjoint.smul_mem (h / 2) hX_skew))
    (LocalPatches.approx_product
      (exp_mem_unitary_of_mem_skewAdjoint (skewAdjoint.smul_mem h hY_skew)) ha_layer hb_layer)
    ha_layer
  obtain ⟨z₁, hz₁, C₁, hC₁_size, hC₁_err⟩ := hstep_approx
  have hstep_exact : exp ((h / 2) • X) * exp (h • Y) * exp ((h / 2) • X) =
      z₁ • (C₁.eval : Register (n + 2)) :=
    sub_eq_zero.mp (norm_le_zero_iff.mp (by simpa only [zero_add] using hC₁_err))
  refine ⟨z₁ ^ m, by simp [norm_pow, hz₁], C₁.pow m, ?_, ?_⟩
  · rw [TwoQubitCircuit.pow_gateCount]
    have hcard_compl : S.card + Sᶜ.card = n + 1 := by
      simpa only [Fintype.card_fin] using Finset.card_add_card_compl S
    have h1 : C₁.gateCount ≤ (n + 1) + (n + 1) / 2 := by omega
    have h2 : (n + 1) + (n + 1) / 2 < 2 * (n + 2) - 1 := by omega
    dsimp [m]
    exact Nat.mul_lt_mul_of_pos_left (lt_of_le_of_lt h1 h2) (by omega)
  · have hpow_err := norm_strang_pow_doubleCommutator_le X Y hX_skew hY_skew t ht0 m hm_pos
    have hh2 : t / (2 * (m : ℝ)) = h / 2 := by dsimp [h]; ring
    rw [hh2, hstep_exact, smul_pow, ← TwoQubitCircuit.pow_eval_coe, hsum_XY,
      norm_sub_rev] at hpow_err
    change ‖unitaryEvolution (pathHamiltonian u) t - z₁ ^ m • ((C₁.pow m).eval : Register (n + 2))‖ ≤ _ at hpow_err ⊢
    refine hpow_err.trans ?_
    have hsum_comm : ‖X * (X * Y - Y * X) - (X * Y - Y * X) * X‖ +
        ‖Y * (Y * X - X * Y) - (Y * X - X * Y) * Y‖ ≤
        405000 * ((n + 1 : ℕ) : ℝ) * M ^ 3 := by
      calc _ ≤ 60 * ((n + 1 : ℕ) : ℝ) * (15 * M) ^ 3 + 60 * ((n + 1 : ℕ) : ℝ) * (15 * M) ^ 3 :=
            add_le_add hcomm_XXY hcomm_YYX
        _ = 405000 * ((n + 1 : ℕ) : ℝ) * M ^ 3 := by ring
    have hm_pos_r : (0 : ℝ) < m := by exact_mod_cast hm_pos
    have hn_le : ((n + 1 : ℕ) : ℝ) ≤ (m : ℝ) := by dsimp [m]; push_cast; linarith
    calc (1 / 2) * (‖X * (X * Y - Y * X) - (X * Y - Y * X) * X‖ +
            ‖Y * (Y * X - X * Y) - (Y * X - X * Y) * Y‖) * t ^ 3 / (m : ℝ) ^ 2
        ≤ (1 / 2) * (405000 * ((n + 1 : ℕ) : ℝ) * M ^ 3) * t ^ 3 / (m : ℝ) ^ 2 := by
            gcongr
      _ ≤ (1 / 2) * (405000 * (m : ℝ) * M ^ 3) * t ^ 3 / (m : ℝ) ^ 2 := by
            gcongr
      _ = 202500 * M ^ 3 * t ^ 3 / ((n + 2 : ℕ) : ℝ) := by
            dsimp [m]; field_simp [hm_pos_r.ne']; ring

private theorem gaussianReal_abs_gt_le {R : ℝ} (hR : 0 ≤ R) :
    (gaussianReal 0 1).real {x : ℝ | R < |x|} ≤ 2 * Real.exp (-(R ^ 2 / 2)) := by
  have hsub : {x : ℝ | R < |x|} ⊆ Set.Iic (-R) ∪ Set.Ici R := by
    intro x hx
    rw [Set.mem_setOf_eq, lt_abs] at hx
    rcases hx with hpos | hneg
    · exact Or.inr hpos.le
    · exact Or.inl (by linarith only [hneg])
  have hsymm : gaussianReal 0 1 (Set.Ici R) = gaussianReal 0 1 (Set.Iic (-R)) := by
    have hmp : MeasurePreserving Neg.neg (gaussianReal 0 1) (gaussianReal 0 1) := by
      refine ⟨measurable_neg, ?_⟩
      have h1 := gaussianReal_map_neg (0 : ℝ) (1 : ℝ≥0)
      simpa using h1
    have hpre : Neg.neg ⁻¹' Set.Iic (-R) = Set.Ici R := by
      ext x; simp [Set.mem_Iic, Set.mem_Ici]; constructor <;> intro h <;> linarith
    rw [← hpre, hmp.measure_preimage measurableSet_Iic.nullMeasurableSet]
  have htail := gaussianReal_Iic_neg_le hR
  have hmeas_le : gaussianReal 0 1 {x : ℝ | R < |x|} ≤
      ENNReal.ofReal (2 * Real.exp (-(R ^ 2 / 2))) := by
    calc gaussianReal 0 1 {x : ℝ | R < |x|}
        ≤ gaussianReal 0 1 (Set.Iic (-R) ∪ Set.Ici R) := measure_mono hsub
      _ ≤ gaussianReal 0 1 (Set.Iic (-R)) + gaussianReal 0 1 (Set.Ici R) := measure_union_le _ _
      _ = gaussianReal 0 1 (Set.Iic (-R)) + gaussianReal 0 1 (Set.Iic (-R)) := by rw [hsymm]
      _ ≤ ENNReal.ofReal (Real.exp (-(R ^ 2 / 2))) + ENNReal.ofReal (Real.exp (-(R ^ 2 / 2))) :=
          add_le_add htail htail
      _ = ENNReal.ofReal (2 * Real.exp (-(R ^ 2 / 2))) := by
          rw [← ENNReal.ofReal_add (Real.exp_nonneg _) (Real.exp_nonneg _), two_mul]
  have hreal := ENNReal.toReal_mono ENNReal.ofReal_ne_top hmeas_le
  rwa [ENNReal.toReal_ofReal (by positivity), ← Measure.real_def] at hreal

private theorem pi_gaussian_linf_compl_le {ι : Type*} [Fintype ι] {R : ℝ} (hR0 : 0 ≤ R) :
    let μ := Measure.pi fun _ : ι => gaussianReal 0 1
    MeasurableSet {x : ι → ℝ | ∀ i : ι, |x i| ≤ R} ∧
      μ.real {x : ι → ℝ | ∀ i : ι, |x i| ≤ R}ᶜ ≤
        2 * (Fintype.card ι : ℝ) * Real.exp (-(R ^ 2 / 2)) := by
  intro μ
  haveI : IsProbabilityMeasure μ := by dsimp [μ]; infer_instance
  let Box : Set (ι → ℝ) := {x | ∀ i : ι, |x i| ≤ R}
  have hBox_meas : MeasurableSet Box := by
    have heq : Box = ⋂ i : ι, {x : ι → ℝ | |x i| ≤ R} := by ext x; simp [Box]
    rw [heq]
    exact MeasurableSet.iInter fun i =>
      measurableSet_le (continuous_abs.measurable.comp (measurable_pi_apply i)) measurable_const
  refine ⟨hBox_meas, ?_⟩
  have hcov : Boxᶜ ⊆ ⋃ i : ι, {x : ι → ℝ | R < |x i|} := by
    intro x hx
    rw [Set.mem_compl_iff] at hx
    dsimp [Box] at hx; push Not at hx
    obtain ⟨i, hi⟩ := hx
    exact Set.mem_iUnion.mpr ⟨i, hi⟩
  have hcoord (i : ι) :
      μ.real {x : ι → ℝ | R < |x i|} ≤ 2 * Real.exp (-(R ^ 2 / 2)) := by
    have hmp : MeasurePreserving (Function.eval i) μ (gaussianReal 0 1) :=
      MeasureTheory.measurePreserving_eval (fun _ : ι => gaussianReal 0 1) i
    have hpre : {x : ι → ℝ | R < |x i|} = (Function.eval i) ⁻¹' {y : ℝ | R < |y|} := rfl
    have hm_set : MeasurableSet {y : ℝ | R < |y|} :=
      measurableSet_lt measurable_const continuous_abs.measurable
    rw [hpre, Measure.real_def, hmp.measure_preimage hm_set.nullMeasurableSet, ← Measure.real_def]
    exact gaussianReal_abs_gt_le hR0
  have hunion : μ Boxᶜ ≤ ∑ i : ι, μ {x : ι → ℝ | R < |x i|} :=
    (measure_mono hcov).trans (measure_iUnion_fintype_le _ _)
  have hreal_union := ENNReal.toReal_mono (ENNReal.sum_ne_top.mpr fun _ _ => measure_ne_top _ _) hunion
  rw [ENNReal.toReal_sum (fun _ _ => measure_ne_top _ _), ← Measure.real_def] at hreal_union
  refine hreal_union.trans ?_
  calc (∑ i : ι, μ.real {x : ι → ℝ | R < |x i|})
      ≤ ∑ _i : ι, (2 * Real.exp (-(R ^ 2 / 2))) := Finset.sum_le_sum fun i _ => hcoord i
    _ = 2 * (Fintype.card ι : ℝ) * Real.exp (-(R ^ 2 / 2)) := by simp; ring

private theorem continuous_abs_det_fin_three :
    Continuous fun b : Fin 3 → Fin 3 → ℝ => |(Matrix.of b).det| := by
  simp only [Matrix.det_fin_three, Matrix.of_apply]
  fun_prop

private theorem continuous_onsiteNormSq :
    Continuous (onsiteNormSq : (Fin 3 → ℝ) → ℝ) := by
  simp only [onsiteNormSq, Fin.sum_univ_three]
  fun_prop

/-- High-probability sublinear-time survival past `choose(2N, 2) = (n + 2) * (2 * n + 3)` on the
full-rank non-matchgate event `Ω_rk3(n, η)`: for every `η ∈ [0, 1]` and `R ≥ 1`, on the explicit
sub-event `Ω_rk3(n, η) ∩ {x | ∀ i, |x i| ≤ R}` of Gaussian probability
`≥ 1 - (38 * n + 39) * η^2 - 2 * (12 * n + 15) * exp(-R^2 / 2)`, **every** chain Hamiltonian
`H(x)` satisfies `orbitCircuitDistance H(x) s t < 1 / 10` across all `s ≥ (n + 2) * (2 * n + 3)`
and all `t ≥ 0` with `(130 * R)^3 * t^3 ≤ n + 2` (so `T < tenthPlateauOnset H(x) s` whenever `H(x)`
eventually leaves the `s`-gate `1/10`-neighborhood). -/
theorem gaussian_rk3_strang_onset_survival (n : ℕ) {η R : ℝ}
    (hη0 : 0 ≤ η) (hη1 : η ≤ 1) (hR1 : 1 ≤ R) :
    let μ := Measure.pi fun _ : PrefixIndex n => gaussianReal 0 1
    let E_surv : Set (PrefixIndex n → ℝ) :=
      bondRankThreeFieldEvent n η ∩ {x | ∀ i : PrefixIndex n, |x i| ≤ R}
    1 - ((38 * n + 39 : ℕ) : ℝ) * η ^ 2 -
        2 * ((12 * n + 15 : ℕ) : ℝ) * Real.exp (-(R ^ 2 / 2)) ≤ μ.real E_surv ∧
      ∀ x ∈ E_surv,
        let u : PathShell n := WithLp.toLp 2 (x ∘ (pathCoeffEquiv n).symm)
        let H : selfAdjoint (Register (n + 2)) :=
          ⟨pathHamiltonian u, isSelfAdjoint_pathHamiltonian u⟩
        ∀ s ≥ (n + 2) * (2 * (n + 2) - 1), ∀ T ≥ 0,
          (130 * R) ^ 3 * T ^ 3 ≤ ((n + 2 : ℕ) : ℝ) →
            (∀ t ∈ Icc (0 : ℝ) T, orbitCircuitDistance H s t < 1 / 10) ∧
            ((∃ B ≥ 0, 1 / 10 < orbitCircuitDistance H s B) → T < tenthPlateauOnset H s) := by
  intro μ E_surv
  haveI : IsProbabilityMeasure μ := by dsimp [μ]; infer_instance
  let Box : Set (PrefixIndex n → ℝ) := {x | ∀ i : PrefixIndex n, |x i| ≤ R}
  obtain ⟨hBox_meas, hBox_compl_raw⟩ :=
    pi_gaussian_linf_compl_le (ι := PrefixIndex n) (zero_le_one.trans hR1)
  have hcard_pref : Fintype.card (PrefixIndex n) = 12 * n + 15 := by
    rw [Fintype.card_congr (pathCoeffEquiv n)]
    simp only [PathLabel, Fintype.card_sum, Fintype.card_prod, Fintype.card_fin]
    omega
  have hBox_compl_le : μ.real Boxᶜ ≤
      2 * ((12 * n + 15 : ℕ) : ℝ) * Real.exp (-(R ^ 2 / 2)) := by
    dsimp [μ, Box]
    rwa [hcard_pref] at hBox_compl_raw
  have hrk3_compl := (bondRankThreeFieldEvent_compl_prob_le n hη0).2 hη1
  have hmeas_rk3 : MeasurableSet (bondRankThreeFieldEvent n η) := by
    have heq : bondRankThreeFieldEvent n η =
        (⋂ e : Fin (n + 1), {x | η ^ 3 ≤ |(bondMatrixOfPrefix n x e).det|}) ∩
        (⋂ v : Fin (n + 2), {x | η ^ 2 ≤ onsiteNormSq (onsiteVecOfPrefix n x v)}) := by
      ext x; simp [bondRankThreeFieldEvent]
    rw [heq]
    refine (MeasurableSet.iInter fun e => ?_).inter (MeasurableSet.iInter fun v => ?_)
    · have hcont_entry : Continuous fun x : PrefixIndex n → ℝ =>
          fun p q : Fin 3 => x ((pathCoeffEquiv n).symm (.inr (e, (p, q)))) :=
        continuous_pi fun p => continuous_pi fun q => continuous_apply _
      have hcont : Continuous fun x : PrefixIndex n → ℝ => |(bondMatrixOfPrefix n x e).det| :=
        continuous_abs_det_fin_three.comp hcont_entry
      exact measurableSet_le measurable_const hcont.measurable
    · have hcont_vec : Continuous (onsiteVecOfPrefix n · v) :=
        continuous_pi fun q => continuous_apply _
      have hcont : Continuous fun x : PrefixIndex n → ℝ =>
          onsiteNormSq (onsiteVecOfPrefix n x v) :=
        continuous_onsiteNormSq.comp hcont_vec
      exact measurableSet_le measurable_const hcont.measurable
  have hprob_ge : 1 - ((38 * n + 39 : ℕ) : ℝ) * η ^ 2 -
      2 * ((12 * n + 15 : ℕ) : ℝ) * Real.exp (-(R ^ 2 / 2)) ≤ μ.real E_surv := by
    have hcompl_eq : E_survᶜ = (bondRankThreeFieldEvent n η)ᶜ ∪ Boxᶜ := Set.compl_inter _ _
    have hmeas_E : MeasurableSet E_surv := hmeas_rk3.inter hBox_meas
    have hsum1 : μ.real E_surv + μ.real E_survᶜ = 1 := by
      rw [Measure.real_def, Measure.real_def,
        ← ENNReal.toReal_add (measure_ne_top _ _) (measure_ne_top _ _),
        measure_add_measure_compl hmeas_E, measure_univ, ENNReal.toReal_one]
    have hcompl_ub : μ.real E_survᶜ ≤
        μ.real (bondRankThreeFieldEvent n η)ᶜ + μ.real Boxᶜ := by
      rw [hcompl_eq]
      exact measureReal_union_le _ _
    linarith only [hsum1, hcompl_ub, hrk3_compl, hBox_compl_le]
  refine ⟨hprob_ge, fun x hx => ?_⟩
  intro u H s hs T hT0 hT_cube
  have hu_le (l : PathLabel n) : |u l| ≤ R := by
    dsimp [u]
    exact hx.2 ((pathCoeffEquiv n).symm l)
  have h_all_t : ∀ t ∈ Icc (0 : ℝ) T, orbitCircuitDistance H s t < 1 / 10 := by
    intro t ht
    obtain ⟨z, hz, C, hC_lt, herr⟩ :=
      strang_brickwork_pathHamiltonian_approx u (zero_le_one.trans hR1) hu_le ht.1
    have ht_pow : t ^ 3 ≤ T ^ 3 := pow_le_pow_left₀ ht.1 ht.2 3
    have herr_lt : 202500 * R ^ 3 * t ^ 3 / ((n + 2 : ℕ) : ℝ) < 1 / 10 := by
      have hn_pos : (0 : ℝ) < ((n + 2 : ℕ) : ℝ) := by positivity
      rw [div_lt_iff₀ hn_pos]
      have h1 : (130 * R) ^ 3 * t ^ 3 ≤ (130 * R) ^ 3 * T ^ 3 :=
        mul_le_mul_of_nonneg_left ht_pow (by positivity)
      have h2 : 202500 * R ^ 3 * t ^ 3 ≤ (202500 / 2197000) * ((130 * R) ^ 3 * t ^ 3) := by
        linarith [show 202500 * R ^ 3 * t ^ 3 = (202500 / 2197000) * ((130 * R) ^ 3 * t ^ 3) by ring]
      have h3 : (202500 / 2197000 : ℝ) * ((n + 2 : ℕ) : ℝ) < (1 / 10) * ((n + 2 : ℕ) : ℝ) :=
        mul_lt_mul_of_pos_right (by norm_num) hn_pos
      nlinarith only [h1, h2, h3, hT_cube]
    have hC_le_s : C.gateCount ≤ s := hC_lt.le.trans hs
    have hmem : z • (C.eval : Register (n + 2)) ∈ phaseCircuitMatrixImageAtMost (n + 2) s :=
      mem_phaseCircuitMatrixImageAtMost_iff.mpr ⟨z, hz, C, hC_le_s, rfl⟩
    have hdist_le : orbitCircuitDistance H s t ≤
        ‖unitaryEvolution H.val t - z • (C.eval : Register (n + 2))‖ := by
      unfold orbitCircuitDistance
      rw [← dist_eq_norm]
      exact Metric.infDist_le_dist_of_mem hmem
    exact lt_of_le_of_lt (hdist_le.trans herr) herr_lt
  refine ⟨h_all_t, ?_⟩
  rintro ⟨B, hB0, hB_gt⟩
  by_cases hT_pos : 0 < T
  · exact (tenthPlateauOnset_spec H hT_pos hB0 h_all_t hB_gt).1
  · have hT_eq0 : T = 0 := le_antisymm (not_lt.mp hT_pos) hT0
    subst hT_eq0
    -- Use `r = 1 / (20 * (‖H.val‖ + 1))` or continuity of `orbitCircuitDistance H s` at `0`!
    have hcont : Continuous (orbitCircuitDistance H s) := (orbitCircuitDistance_lipschitz H s).continuous
    have h0_lt : orbitCircuitDistance H s 0 < 1 / 10 := h_all_t 0 ⟨le_rfl, le_rfl⟩
    obtain ⟨δ, hδ_pos, hδ_ball⟩ := Metric.continuousAt_iff.mp hcont.continuousAt
      (1 / 10 - orbitCircuitDistance H s 0) (sub_pos.mpr h0_lt)
    let r₀ := δ / 2
    have hr₀_pos : 0 < r₀ := half_pos hδ_pos
    have hr₀_all : ∀ t ∈ Icc 0 r₀, orbitCircuitDistance H s t < 1 / 10 := by
      intro t ht
      have hdist_t : dist t 0 < δ := by
        rw [Real.dist_eq, sub_zero, abs_of_nonneg ht.1]
        dsimp [r₀]; linarith only [ht.2, hδ_pos]
      have h1 := hδ_ball hdist_t
      rw [Real.dist_eq] at h1
      linarith only [(abs_lt.mp h1).2]
    exact hr₀_pos.trans (tenthPlateauOnset_spec H hr₀_pos hB0 hr₀_all hB_gt).1

#print axioms crossCut_choiMinor_eq_zero
#print axioms crossCut_choiMinor_le_projectiveCircuitApprox
#print axioms no_nontrivial_choiMinor_above_cutCeiling
#print axioms exists_allToAll_circuit_choiMinor_ne_zero
#print axioms exists_homogeneous_choiAnnihilator_of_carrier_lt_multiset
#print axioms polynomial_degree_choiAnnihilator_past_matchgate
#print axioms norm_strang_doubleCommutator_le
#print axioms strang_brickwork_pathHamiltonian_approx
#print axioms gaussian_rk3_strang_onset_survival

end BrickworkStrang

end
end GaloisForLFunctions.HTGeometry.AccuracyScales.TenthPlateau
