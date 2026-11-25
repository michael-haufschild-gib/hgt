import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.AccuracyScales.TenthPlateau.SingleTargetWitness
import GaloisForLFunctions.HTGeometry.FiniteQubitPauliComplexBasis
import GaloisForLFunctions.HTGeometry.PolynomialCircuitReplicaHilbertLaw
import GaloisForLFunctions.HTGeometry.QuenchedReplicaIncidenceCovarianceLaw
import GaloisForLFunctions.HTGeometry.TwoLocalContinuousCircuitFixedErrorHardEpochLaw
import GaloisForLFunctions.HTGeometry.TwoLocalProjectiveTrotterCompilerLaw
import GaloisForLFunctions.HTGeometry.KrylovProjectedCompleteIncidenceLaw
import GaloisForLFunctions.HTGeometry.Quantum.PhysicalCircuitDeletionBound
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.OnsiteOperatorDistance
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.WeakBonds.DisorderTails
import Mathlib.LinearAlgebra.Vandermonde

/-! # Return-excised multi-date Vandermonde and replica-Gram onset laws at 1/10

This module analyzes multi-date Krylov/Vandermonde rank growth and return-excised `r`-replica
Gram bounds modulo `phaseCircuitMatrixImageAtMost N s` on `[0, 2^{O(N)}]` as quenched upper-bound
mechanisms for `τ_s = tenthPlateauOnset H s` (and `τ_P` at `P = nearHilbertContinuousCircuitBudget N`),
establishing both the exact quenched onset law and the exact algebraic, Krylov-causal, and
spatial weak-bond obstructions:

1. **Exact `1`-replica circuit linear-span threshold and Vandermonde saturation:**
   - `trace_allZ_mul_eq_zero_of_lt_half`, `realizes_finitePauliMatrix_of_half_le`,
     `span_phaseCircuitMatrixImage_eq_top_iff`, and
     `four_pow_le_finrank_replicaTargetSpan_of_half_le`:
     for `N ≥ 2`, `Submodule.span ℂ (phaseCircuitMatrixImageAtMost N s) = ⊤ ↔ (N + 1) / 2 ≤ s`.
     Below `(N + 1) / 2`, every `s`-gate circuit leaves at least one wire untouched and is
     Hilbert-Schmidt orthogonal to `Z^{⊗ N}`; at or above `(N + 1) / 2`, every `N`-qubit Pauli
     string lies in `phaseCircuitMatrixImageAtMost N s`, collapsing `1`-replica quotient rank to
     zero and forcing `Module.finrank ℂ (replicaTargetSpan r …) ≥ 4 ^ N` for all `r ≥ 1`.
   - `orbit_vandermonde_span_eq_spectralSpan`: for any simple-spectrum `H` and step
     `0 < τ ≤ π / (‖H‖ + 1)`, the `2^N` arithmetic-progression samples `e^{-i m τ H}`
     (`m : Fin (2^N)`) are `ℂ`-linearly independent and span the entire all-time trajectory space
     `Submodule.span ℂ (range (unitaryEvolution H.val))` of dimension `2^N` (including inside `[0, 1]`).
2. **Quenched multi-date trace-return-excised `r`-replica Gram onset law:**
   - `choiFidelity_ge_of_hasProjectiveCircuitApproximation` and
     `tenthPlateauOnset_lt_of_returnExcised_replicaGram`:
     if `t : Fin M → ℝ` (`1 ≤ M`, `t_a ∈ [0, T]`) satisfies pairwise trace-return excision
     `2^{-N} ‖Tr(U(t_a)* U(t_b))‖ ≤ ρ` for `a ≠ b` and
     `((N * N)^s * (r * s + 1)^(16 s)) * (1 / M + ρ^r) < (199 / 200)^(2 r)` (`N ≥ 1`, `r ≥ 1`),
     then deterministically `1 / (20 * (‖H‖ + 1)) < τ_s(H) < T` and
     `orbitCircuitDistance H s (τ_s(H)) = 1 / 10` without `ε`-nets, single-target capture, or
     boundary-field averaging.
3. **All-`r` Krylov causal barrier and two-cut weak-bond survival floor against `τ_P ≤ 2^{O(N)}`:**
   - `krylov_empiricalBessel_lower_bound` and `no_exponential_replicaGram_exclusion_at_nearHilbert`:
     for every `H`, `r ≥ 1`, `T ≥ 0`, `t : Fin M → [-T, T]`, and degree `K` with
     `η_K = (r ‖H‖ T)^{K+1} / (K+1)! ≤ 1`, the empirical `r`-replica Bessel constant obeys
     `(1 - η_K)^2 ≤ (K + 1) * empiricalReplicaBessel H r t`; consequently, for any fixed `C > 0`,
     eventually in `N`, no `H` (`‖H‖ ≤ C N`), `T ∈ [0, 2^{C N}]`, `M ≥ 1`, `t : Fin M → [0, T]`,
     and `r ≥ 1` can satisfy `N^{2 P} (r P + 1)^{16 P} * empiricalReplicaBessel H r t < (199/200)^{2 r}`.
   - `gaussian_two_cut_vandermonde_returnExcised_tail` and
     `not_integrable_tenthPlateauOnset_pow_eighteen`:
     there exists a size-independent `c > 0` such that eventually in `k` (`N = k + 3`), for every
     `T ≥ 2`, a disorder event of probability at least `c T^{-18}` simultaneously enjoys maximally
     projective simple spectrum with full `2^N` Vandermonde rank on `[0, 1]`, `√2` scalar-return
     excision at some `t₀ ∈ (0, π / 2] ⊆ [0, T]`, and `τ_s(H_N) > T` for all `P / 2 ≤ s ≤ P`;
     consequently `𝔼[|τ_P(H_N)|^{18}] = ∞`. -/

open Set Filter MeasureTheory ProbabilityTheory Real Topology Matrix
open scoped Matrix.Norms.L2Operator ENNReal ComplexConjugate Kronecker BigOperators
namespace GaloisForLFunctions.HTGeometry.AccuracyScales.TenthPlateau
open SharpOccupation SharpOccupation.FiniteRecords MaximumIntervals PrescribedTimes WeakBonds
noncomputable section

private abbrev Config (N : ℕ) := Fin N → Bool
private abbrev UGroup (N : ℕ) := Matrix.unitaryGroup (Config N) ℂ

/-- Normalized Choi state `Φ_A(x, y) = 2^{-N/2} A_{x y}` of an `N`-qubit operator `A`. -/
def matrixNormalizedChoi {N : ℕ} (A : Register N) (p : Config N × Config N) : ℂ :=
  A p.1 p.2 / Real.sqrt (Fintype.card (Config N))

/-- Full-register `Z^{⊗ N}` Pauli label assigning `Z` (`some 2`) to every wire. -/
def allZPauliLabel (N : ℕ) : Fin N → Option (Fin 3) :=
  fun _ => some 2

/-- Full-register `Z^{⊗ N}` Pauli matrix. -/
def allZPauliMatrix (N : ℕ) : Register N :=
  finitePauliMatrix (allZPauliLabel N)

/-- Empirical `r`-replica Bessel constant
`sup_{‖w‖ ≤ 1} M⁻¹ ∑_{a : Fin M} ‖⟨w, Φ_{U(t_a)}^{⊗ r}⟩‖²` of an orbit sample `t : Fin M → ℝ`. -/
def empiricalReplicaBessel {N M : ℕ} (H : selfAdjoint (Register N)) (r : ℕ) (t : Fin M → ℝ) : ℝ :=
  sSup {val : ℝ | ∃ w : EuclideanSpace ℂ (Fin r → Config N × Config N), ‖w‖ ≤ 1 ∧
    val = (1 / (M : ℝ)) * ∑ a : Fin M,
      ‖inner ℂ w (finitePureTensorPowerEuclidean r
        (matrixNormalizedChoi (unitaryEvolution H.val (t a))))‖ ^ 2}

/-! ## Section 1: Exact `1`-replica circuit linear-span threshold -/

private def flipWire {N : ℕ} (w₀ : Fin N) : Equiv.Perm (Config N) where
  toFun x q := if q = w₀ then !(x q) else x q
  invFun x q := if q = w₀ then !(x q) else x q
  left_inv x := by funext q; by_cases hq : q = w₀ <;> simp [hq]
  right_inv x := by funext q; by_cases hq : q = w₀ <;> simp [hq]

private theorem allZPauliMatrix_offDiag {N : ℕ} {x y : Config N} (hxy : x ≠ y) :
    allZPauliMatrix N x y = 0 := by
  obtain ⟨q, hq⟩ : ∃ q : Fin N, x q ≠ y q := by simpa only [Function.ne_iff] using hxy
  change (∏ s : Fin N, boolPauliOptionEntry (some 2) (x s, y s)) = 0
  refine Finset.prod_eq_zero (Finset.mem_univ q) ?_
  cases hx : x q <;> cases hy : y q
  · exact (hq (hx.trans hy.symm)).elim
  · simp [boolPauliOptionEntry, boolPauliOption, finiteQubitPauli]
  · simp [boolPauliOptionEntry, boolPauliOption, finiteQubitPauli]
  · exact (hq (hx.trans hy.symm)).elim

private theorem allZPauliMatrix_diag_flip {N : ℕ} (w₀ : Fin N) (x : Config N) :
    allZPauliMatrix N (flipWire w₀ x) (flipWire w₀ x) = -allZPauliMatrix N x x := by
  change (∏ s : Fin N, boolPauliOptionEntry (some 2) (flipWire w₀ x s, flipWire w₀ x s)) =
    -(∏ s : Fin N, boolPauliOptionEntry (some 2) (x s, x s))
  rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ w₀),
    ← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ w₀)]
  have hrest : (∏ s ∈ Finset.univ.erase w₀,
      boolPauliOptionEntry (some 2) (flipWire w₀ x s, flipWire w₀ x s)) =
      ∏ s ∈ Finset.univ.erase w₀, boolPauliOptionEntry (some 2) (x s, x s) := by
    refine Finset.prod_congr rfl fun s hs => ?_
    have hne : s ≠ w₀ := Finset.ne_of_mem_erase hs
    simp [flipWire, hne]
  have hw₀ : boolPauliOptionEntry (some 2) (flipWire w₀ x w₀, flipWire w₀ x w₀) =
      -boolPauliOptionEntry (some 2) (x w₀, x w₀) := by
    simp only [flipWire, Equiv.coe_fn_mk, if_true]
    cases x w₀ <;> simp [boolPauliOptionEntry, boolPauliOption, finiteQubitPauli]
  rw [hrest, hw₀, neg_mul]

/-- Below `(N + 1) / 2` gates (`2 * s < N`), every matrix `W ∈ phaseCircuitMatrixImageAtMost N s`
is Hilbert-Schmidt orthogonal to `Z^{⊗ N}`, whereas `Tr((Z^{⊗ N})* Z^{⊗ N}) = 2^N`. -/
theorem trace_allZ_mul_eq_zero_of_lt_half {N s : ℕ} (hs : 2 * s < N) :
    (∀ W ∈ phaseCircuitMatrixImageAtMost N s,
      Matrix.trace (star (allZPauliMatrix N) * W) = 0) ∧
    Matrix.trace (star (allZPauliMatrix N) * allZPauliMatrix N) = (2 : ℂ) ^ N := by
  have hZ_star : star (allZPauliMatrix N) = allZPauliMatrix N := by
    rw [star_eq_conjTranspose]
    exact (finitePauliMatrix_isHermitian (allZPauliLabel N)).eq
  refine ⟨?_, ?_⟩
  · rintro W hW
    obtain ⟨c, _, C, hC, rfl⟩ := mem_phaseCircuitMatrixImageAtMost_iff.mp hW
    rw [Matrix.mul_smul, Matrix.trace_smul]
    suffices hC0 : Matrix.trace (star (allZPauliMatrix N) * (C.eval : Register N)) = 0 by
      rw [hC0, smul_zero]
    have hcard_lt : C.touchedSites.card < (Finset.univ : Finset (Fin N)).card := by
      have hle := C.card_touchedSites_le
      simp only [Finset.card_univ, Fintype.card_fin]
      omega
    obtain ⟨w₀, _, hw₀_not⟩ : ∃ w₀ ∈ (Finset.univ : Finset (Fin N)), w₀ ∉ C.touchedSites :=
      Finset.exists_mem_notMem_of_card_lt_card hcard_lt
    have hsupp := (C.isSiteSupported_touchedSites).2
    have hdiag_inv (x : Config N) :
        (C.eval : Register N) (flipWire w₀ x) (flipWire w₀ x) = (C.eval : Register N) x x := by
      refine hsupp (flipWire w₀ x) (flipWire w₀ x) x x ?_ ?_ (fun _ _ => rfl) (fun _ _ => rfl)
      · intro w hw
        have hne : w ≠ w₀ := fun heq => hw₀_not (heq ▸ hw)
        simp [flipWire, hne]
      · intro w hw
        have hne : w ≠ w₀ := fun heq => hw₀_not (heq ▸ hw)
        simp [flipWire, hne]
    have htr_diag : Matrix.trace (star (allZPauliMatrix N) * (C.eval : Register N)) =
        ∑ x : Config N, allZPauliMatrix N x x * (C.eval : Register N) x x := by
      rw [hZ_star, Matrix.trace]
      refine Finset.sum_congr rfl fun x _ => ?_
      rw [Matrix.diag_apply, Matrix.mul_apply]
      refine Finset.sum_eq_single x (fun y _ hyx => ?_) (by simp)
      rw [allZPauliMatrix_offDiag hyx.symm, zero_mul]
    rw [htr_diag]
    set S := ∑ x : Config N, allZPauliMatrix N x x * (C.eval : Register N) x x
    have hneg : S = -S := by
      calc S = ∑ x : Config N,
              allZPauliMatrix N (flipWire w₀ x) (flipWire w₀ x) *
                (C.eval : Register N) (flipWire w₀ x) (flipWire w₀ x) :=
            (Equiv.sum_comp (flipWire w₀) fun x =>
              allZPauliMatrix N x x * (C.eval : Register N) x x).symm
        _ = ∑ x : Config N, -(allZPauliMatrix N x x * (C.eval : Register N) x x) := by
            refine Finset.sum_congr rfl fun x _ => ?_
            rw [allZPauliMatrix_diag_flip w₀ x, hdiag_inv x, neg_mul]
        _ = -S := by rw [Finset.sum_neg_distrib]
    have h2 : (2 : ℂ) * S = 0 := by linear_combination hneg
    exact (mul_eq_zero.mp h2).resolve_left (by norm_num)
  · rw [hZ_star, allZPauliMatrix, finitePauliMatrix_mul_self]
    simp [Matrix.trace]

private theorem boolTwoQubitPauli_mem_unitary (p q : Option (Fin 3)) :
    boolTwoQubitPauli p q ∈ Matrix.unitaryGroup (Bool × Bool) ℂ := by
  have hconj : Matrix.conjTranspose (boolTwoQubitPauli p q) = boolTwoQubitPauli p q := by
    ext ⟨x₁, x₂⟩ ⟨y₁, y₂⟩
    change star (boolPauliOptionEntry p (y₁, x₁) * boolPauliOptionEntry q (y₂, x₂)) =
      boolPauliOptionEntry p (x₁, y₁) * boolPauliOptionEntry q (x₂, y₂)
    rw [star_mul, star_boolPauliOptionEntry_swap, star_boolPauliOptionEntry_swap, mul_comm]
  have hsq : boolTwoQubitPauli p q * boolTwoQubitPauli p q = 1 := by
    change (boolPauliOption p ⊗ₖ boolPauliOption q) *
      (boolPauliOption p ⊗ₖ boolPauliOption q) = 1
    rw [← Matrix.mul_kronecker_mul, boolPauliOption_mul_self, boolPauliOption_mul_self,
      Matrix.one_kronecker_one]
  rw [Matrix.mem_unitaryGroup_iff', star_eq_conjTranspose, hconj]
  exact hsq

private theorem finitePauliMatrix_none_eq_one {σ : Type*} [Fintype σ] [DecidableEq σ] :
    finitePauliMatrix (fun _ : σ => none) = 1 := by
  ext x y
  by_cases hxy : x = y
  · subst hxy
    rw [Matrix.one_apply_eq]
    exact Finset.prod_eq_one fun q _ => by cases x q <;> rfl
  · rw [Matrix.one_apply_ne hxy]
    obtain ⟨q, hq⟩ : ∃ q : σ, x q ≠ y q := by simpa only [Function.ne_iff] using hxy
    refine Finset.prod_eq_zero (Finset.mem_univ q) ?_
    cases hx : x q <;> cases hy : y q <;> first | exact (hq (hx.trans hy.symm)).elim | rfl

private theorem realizes_one_of_twoWireSupport {N : ℕ} (a b : Fin N) (hab : a ≠ b)
    (Q : Fin N → Option (Fin 3)) (hrest : ∀ q : Fin N, q ≠ a → q ≠ b → Q q = none) :
    DiagonalSynthesis.Realizes 1 (finitePauliMatrix Q) := by
  let Uloc : Matrix.unitaryGroup (Bool × Bool) ℂ :=
    ⟨boolTwoQubitPauli (Q a) (Q b), boolTwoQubitPauli_mem_unitary (Q a) (Q b)⟩
  let z := scalarSpecialUnitaryPhase Uloc
  let G := scalarSpecialUnitaryRepresentative Uloc
  have hzunit : star z * z = 1 := scalarSpecialUnitaryPhase_unitary Uloc
  have hznorm : ‖star z‖ = 1 := by
    have hnorm := congrArg norm hzunit
    have hsq : ‖z‖ * ‖z‖ = 1 := by simpa only [norm_mul, norm_star, norm_one] using hnorm
    have hz1 : ‖z‖ = 1 := by nlinarith only [hsq, norm_nonneg z]
    simpa only [norm_star] using hz1
  have hrest_eq : finitePauliMatrix (twoQubitRestPauliLabel Q a b) = 1 := by
    have hlbl : twoQubitRestPauliLabel Q a b = fun _ => none :=
      funext fun q => hrest q.1 q.2.1 q.2.2
    rw [hlbl, finitePauliMatrix_none_eq_one]
  have hreind := reindex_splitTwoQubitConfig_finitePauliMatrix a b hab Q
  rw [hrest_eq] at hreind
  let C := TwoQubitCircuit.singleOn a b hab G
  refine ⟨star z, hznorm, C, le_rfl, ?_⟩
  have hC_eval : (C.eval : Register N) = z • finitePauliMatrix Q := by
    rw [TwoQubitCircuit.singleOn_eval]
    ext x y
    have hxy := congrFun (congrFun hreind
      (splitTwoQubitConfig a b hab x)) (splitTwoQubitConfig a b hab y)
    simp only [Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_apply_apply,
      Matrix.kronecker, Matrix.kroneckerMap_apply] at hxy
    simp only [G, z, Uloc, twoQubitLift, specialUnitaryAsUnitary,
      scalarSpecialUnitaryRepresentative_coe, unitaryGroupReindex_coe,
      Quantum.tensorGate_val, Equiv.symm_symm, Submonoid.coe_one,
      Matrix.kroneckerMap_apply, Matrix.smul_apply, smul_eq_mul]
    rw [hxy]
    ring
  rw [hC_eval, smul_smul, hzunit, one_smul]

private def truncPauliLabel {N : ℕ} (P : Fin N → Option (Fin 3)) (m : ℕ) :
    Fin N → Option (Fin 3) :=
  fun q => if q.val < 2 * m then P q else none

private def slicePauliLabel {N : ℕ} (P : Fin N → Option (Fin 3)) (m : ℕ) :
    Fin N → Option (Fin 3) :=
  fun q => if 2 * m ≤ q.val ∧ q.val < 2 * (m + 1) then P q else none

private theorem truncPauliLabel_mul_slice {N : ℕ} (P : Fin N → Option (Fin 3)) (m : ℕ) :
    finitePauliMatrix (truncPauliLabel P m) * finitePauliMatrix (slicePauliLabel P m) =
      finitePauliMatrix (truncPauliLabel P (m + 1)) := by
  ext x z
  rw [Matrix.mul_apply]
  change (∑ y : Config N,
    (∏ q, boolPauliOptionEntry (truncPauliLabel P m q) (x q, y q)) *
      ∏ q, boolPauliOptionEntry (slicePauliLabel P m q) (y q, z q)) =
    ∏ q, boolPauliOptionEntry (truncPauliLabel P (m + 1) q) (x q, z q)
  simp_rw [← Finset.prod_mul_distrib]
  rw [← Fintype.prod_sum (fun q (b : Bool) =>
    boolPauliOptionEntry (truncPauliLabel P m q) (x q, b) *
      boolPauliOptionEntry (slicePauliLabel P m q) (b, z q))]
  refine Finset.prod_congr rfl fun q _ => ?_
  change (boolPauliOption (truncPauliLabel P m q) *
    boolPauliOption (slicePauliLabel P m q)) (x q) (z q) =
    boolPauliOption (truncPauliLabel P (m + 1) q) (x q) (z q)
  have hnone : boolPauliOption none = 1 := rfl
  by_cases hlt : q.val < 2 * m
  · have hlt' : q.val < 2 * (m + 1) := by omega
    have hnot : ¬ (2 * m ≤ q.val ∧ q.val < 2 * (m + 1)) := by omega
    simp only [truncPauliLabel, slicePauliLabel, if_pos hlt, if_pos hlt', if_neg hnot,
      hnone, mul_one]
  · by_cases hlt' : q.val < 2 * (m + 1)
    · have hmid : 2 * m ≤ q.val ∧ q.val < 2 * (m + 1) := ⟨by omega, hlt'⟩
      simp only [truncPauliLabel, slicePauliLabel, if_neg hlt, if_pos hlt', if_pos hmid,
        hnone, one_mul]
    · have hnot : ¬ (2 * m ≤ q.val ∧ q.val < 2 * (m + 1)) := by omega
      simp only [truncPauliLabel, slicePauliLabel, if_neg hlt, if_neg hlt', if_neg hnot,
        hnone, mul_one]

/-- At or above `(N + 1) / 2` gates (`N ≥ 2`), every `N`-qubit Pauli matrix is realized exactly
up to a global phase and hence belongs to `phaseCircuitMatrixImageAtMost N s`. -/
theorem realizes_finitePauliMatrix_of_half_le {N s : ℕ} (hN : 2 ≤ N)
    (hs : (N + 1) / 2 ≤ s) (P : Fin N → Option (Fin 3)) :
    DiagonalSynthesis.Realizes s (finitePauliMatrix P) ∧
      finitePauliMatrix P ∈ phaseCircuitMatrixImageAtMost N s := by
  have htrunc : ∀ m : ℕ, DiagonalSynthesis.Realizes m (finitePauliMatrix (truncPauliLabel P m)) := by
    intro m
    induction m with
    | zero =>
        have h0 : finitePauliMatrix (truncPauliLabel P 0) = (1 : Register N) := by
          have hlbl : truncPauliLabel P 0 = fun _ => none := by
            funext q; simp [truncPauliLabel]
          rw [hlbl, finitePauliMatrix_none_eq_one]
        rw [h0]
        exact DiagonalSynthesis.Realizes.one N
    | succ m ih =>
        have hslice : DiagonalSynthesis.Realizes 1 (finitePauliMatrix (slicePauliLabel P m)) := by
          by_cases h2 : 2 * m + 1 < N
          · let a : Fin N := ⟨2 * m, by omega⟩
            let b : Fin N := ⟨2 * m + 1, h2⟩
            have hab : a ≠ b := fun h => by
              have hv := congrArg Fin.val h; dsimp [a, b] at hv; omega
            refine realizes_one_of_twoWireSupport a b hab (slicePauliLabel P m) fun q hqa hqb => ?_
            have hv1 : q.val ≠ 2 * m := fun h => hqa (Fin.ext h)
            have hv2 : q.val ≠ 2 * m + 1 := fun h => hqb (Fin.ext h)
            have hnot : ¬ (2 * m ≤ q.val ∧ q.val < 2 * (m + 1)) := by omega
            simp [slicePauliLabel, hnot]
          · by_cases h1 : 2 * m < N
            · have hm_pos : 0 < 2 * m := by omega
              let a : Fin N := ⟨0, by omega⟩
              let b : Fin N := ⟨2 * m, h1⟩
              have hab : a ≠ b := fun h => by
                have hv := congrArg Fin.val h; dsimp [a, b] at hv; omega
              refine realizes_one_of_twoWireSupport a b hab (slicePauliLabel P m) fun q _ hqb => ?_
              have hv2 : q.val ≠ 2 * m := fun h => hqb (Fin.ext h)
              have hq_lt : q.val < N := q.isLt
              have hnot : ¬ (2 * m ≤ q.val ∧ q.val < 2 * (m + 1)) := by omega
              simp [slicePauliLabel, hnot]
            · let a : Fin N := ⟨0, by omega⟩
              let b : Fin N := ⟨1, by omega⟩
              have hab : a ≠ b := fun h => by
                have hv := congrArg Fin.val h; dsimp [a, b] at hv; omega
              refine realizes_one_of_twoWireSupport a b hab (slicePauliLabel P m) fun q _ _ => ?_
              have hq_lt : q.val < N := q.isLt
              have hnot : ¬ (2 * m ≤ q.val ∧ q.val < 2 * (m + 1)) := by omega
              simp [slicePauliLabel, hnot]
        rw [← truncPauliLabel_mul_slice P m]
        exact ih.mul hslice
  let M_half := (N + 1) / 2
  have hfull : truncPauliLabel P M_half = P := by
    funext q
    have hq_lt : q.val < 2 * M_half := by
      have hlt : q.val < N := q.isLt
      dsimp only [M_half]; omega
    simp [truncPauliLabel, hq_lt]
  obtain ⟨z, hz, C, hC, hP⟩ := hfull ▸ htrunc M_half
  have hCs : C.gateCount ≤ s := hC.trans hs
  exact ⟨⟨z, hz, C, hCs, hP⟩,
    mem_phaseCircuitMatrixImageAtMost_iff.mpr ⟨z, hz, C, hCs, hP⟩⟩

/-- Exact `1`-replica circuit linear-span dichotomy (`N ≥ 2`):
`Submodule.span ℂ (phaseCircuitMatrixImageAtMost N s) = ⊤` if and only if `(N + 1) / 2 ≤ s`. -/
theorem span_phaseCircuitMatrixImage_eq_top_iff {N s : ℕ} (hN : 2 ≤ N) :
    Submodule.span ℂ (phaseCircuitMatrixImageAtMost N s) = ⊤ ↔ (N + 1) / 2 ≤ s := by
  constructor
  · intro hspan
    by_contra hlt_not
    have h2s : 2 * s < N := by omega
    obtain ⟨hzero, htr_ne⟩ := trace_allZ_mul_eq_zero_of_lt_half (N := N) (s := s) h2s
    let L : Register N →ₗ[ℂ] ℂ :=
      { toFun := fun M => Matrix.trace (star (allZPauliMatrix N) * M)
        map_add' := fun A B => by rw [Matrix.mul_add, Matrix.trace_add]
        map_smul' := fun c A => by rw [Matrix.mul_smul, Matrix.trace_smul]; rfl }
    have hker : Submodule.span ℂ (phaseCircuitMatrixImageAtMost N s) ≤ LinearMap.ker L := by
      rw [Submodule.span_le]
      intro W hW
      exact hzero W hW
    rw [hspan] at hker
    have h0 : L (allZPauliMatrix N) = 0 := hker Submodule.mem_top
    change Matrix.trace (star (allZPauliMatrix N) * allZPauliMatrix N) = 0 at h0
    rw [htr_ne] at h0
    exact pow_ne_zero N (by norm_num : (2 : ℂ) ≠ 0) h0
  · intro hs
    refine top_unique ?_
    rw [← span_range_finitePauliMatrix (Fin N)]
    refine Submodule.span_mono ?_
    rintro _ ⟨P, rfl⟩
    exact (realizes_finitePauliMatrix_of_half_le hN hs P).2

private theorem finiteComplexInner_pauli_choi {N : ℕ} (P Q : Fin N → Option (Fin 3)) :
    finiteComplexInner (matrixNormalizedChoi (finitePauliMatrix P))
      (matrixNormalizedChoi (finitePauliMatrix Q)) =
      if P = Q then 1 else 0 := by
  unfold finiteComplexInner matrixNormalizedChoi
  have hcard : (Fintype.card (Config N) : ℝ) = (2 : ℝ) ^ N := by
    simp [Config]
  have hD_pos : (0 : ℝ) < (2 : ℝ) ^ N := pow_pos two_pos N
  have hterm (p : Config N × Config N) :
      conj (finitePauliMatrix P p.1 p.2 / Real.sqrt (Fintype.card (Config N))) *
        (finitePauliMatrix Q p.1 p.2 / Real.sqrt (Fintype.card (Config N))) =
        (((2 : ℂ) ^ N)⁻¹) * (star (finitePauliMatrix P p.1 p.2) * finitePauliMatrix Q p.1 p.2) := by
    have hsq : ((Real.sqrt (Fintype.card (Config N)) : ℂ) *
        (Real.sqrt (Fintype.card (Config N)) : ℂ)) = (2 : ℂ) ^ N := by
      norm_cast
      rw [Real.mul_self_sqrt (by rw [hcard]; exact hD_pos.le), hcard]
      norm_cast
    rw [div_eq_mul_inv, div_eq_mul_inv, map_mul, map_inv₀, Complex.conj_ofReal]
    calc star (finitePauliMatrix P p.1 p.2) * (Real.sqrt (Fintype.card (Config N)) : ℂ)⁻¹ *
          (finitePauliMatrix Q p.1 p.2 * (Real.sqrt (Fintype.card (Config N)) : ℂ)⁻¹)
        = (((Real.sqrt (Fintype.card (Config N)) : ℂ) *
            (Real.sqrt (Fintype.card (Config N)) : ℂ))⁻¹) *
            (star (finitePauliMatrix P p.1 p.2) * finitePauliMatrix Q p.1 p.2) := by
            rw [mul_inv]; ring
      _ = (((2 : ℂ) ^ N)⁻¹) * (star (finitePauliMatrix P p.1 p.2) * finitePauliMatrix Q p.1 p.2) := by
            rw [hsq]
  simp_rw [hterm]
  rw [← Finset.mul_sum]
  let e_pair : (Fin N → Bool × Bool) ≃ Config N × Config N :=
    { toFun := fun xy => (fun q => (xy q).1, fun q => (xy q).2)
      invFun := fun p q => (p.1 q, p.2 q)
      left_inv := fun _ => rfl
      right_inv := fun ⟨_, _⟩ => rfl }
  have hsum_eq : (∑ p : Config N × Config N,
      star (finitePauliMatrix P p.1 p.2) * finitePauliMatrix Q p.1 p.2) =
      finitePauliHilbertSchmidt P Q := by
    rw [← Equiv.sum_comp e_pair]
    unfold finitePauliHilbertSchmidt
    refine Finset.sum_congr rfl fun xy _ => ?_
    change star (∏ q, boolPauliOptionEntry (P q) ((e_pair xy).1 q, (e_pair xy).2 q)) *
        (∏ q, boolPauliOptionEntry (Q q) ((e_pair xy).1 q, (e_pair xy).2 q)) = _
    have hpair (q : Fin N) : ((e_pair xy).1 q, (e_pair xy).2 q) = xy q := rfl
    simp_rw [hpair]
    rw [Complex.star_def, map_prod]
    simp_rw [← Complex.star_def]
    rw [← Finset.prod_mul_distrib]
  rw [hsum_eq, finitePauliHilbertSchmidt_eq]
  simp only [Fintype.card_fin]
  by_cases hPQ : P = Q
  · rw [if_pos hPQ, if_pos hPQ, inv_mul_cancel₀ (pow_ne_zero N (by norm_num : (2 : ℂ) ≠ 0))]
  · rw [if_neg hPQ, if_neg hPQ, mul_zero]

/-- At or above `(N + 1) / 2` gates (`N ≥ 2`, `r ≥ 1`), the `4^N` normalized Pauli Choi vectors
form an orthonormal family inside `replicaTargetSpan r` of `s`-gate circuits, forcing
`4 ^ N ≤ Module.finrank ℂ (replicaTargetSpan r …)`. -/
theorem four_pow_le_finrank_replicaTargetSpan_of_half_le {N s r : ℕ}
    (hN : 2 ≤ N) (hs : (N + 1) / 2 ≤ s) (hr : 1 ≤ r) :
    4 ^ N ≤ Module.finrank ℂ (replicaTargetSpan r
      (fun C : {C : TwoQubitCircuit N // C.gateCount ≤ s} =>
        matrixNormalizedChoi (C.val.eval : Register N))) := by
  let S := replicaTargetSpan r
    (fun C : {C : TwoQubitCircuit N // C.gateCount ≤ s} =>
      matrixNormalizedChoi (C.val.eval : Register N))
  let v : (Fin N → Option (Fin 3)) → EuclideanSpace ℂ (Fin r → Config N × Config N) :=
    fun P => finitePureTensorPowerEuclidean r (matrixNormalizedChoi (finitePauliMatrix P))
  have hv_mem (P : Fin N → Option (Fin 3)) : v P ∈ S := by
    obtain ⟨⟨z, hz, C, hC, hP⟩, _⟩ := realizes_finitePauliMatrix_of_half_le hN hs P
    have hsmul : v P = (z ^ r) •
        finitePureTensorPowerEuclidean r (matrixNormalizedChoi (C.eval : Register N)) := by
      ext x
      simp only [v, finitePureTensorPowerEuclidean, finitePureTensorPower,
        matrixNormalizedChoi, hP, Matrix.smul_apply, smul_eq_mul, mul_div_assoc,
        PiLp.smul_apply, WithLp.ofLp_toLp, Finset.prod_mul_distrib, Finset.prod_const,
        Finset.card_univ, Fintype.card_fin]
    rw [hsmul]
    exact Submodule.smul_mem S (z ^ r)
      (Submodule.subset_span (mem_range_self (⟨C, hC⟩ : {C : TwoQubitCircuit N // C.gateCount ≤ s})))
  have hv_orth : Orthonormal ℂ (fun P : Fin N → Option (Fin 3) => (⟨v P, hv_mem P⟩ : S)) := by
    rw [orthonormal_iff_ite]
    intro P Q
    change inner ℂ (v P) (v Q) = if P = Q then 1 else 0
    rw [inner_finitePureTensorPowerEuclidean, finiteComplexInner_pauli_choi]
    by_cases hPQ : P = Q
    · rw [if_pos hPQ, one_pow]
    · rw [if_neg hPQ, zero_pow (by omega)]
  have hli := hv_orth.linearIndependent
  have hcard : Fintype.card (Fin N → Option (Fin 3)) = 4 ^ N := by simp
  rw [← hcard]
  exact hli.fintype_card_le_finrank

/-! ## Section 2: Arithmetic-progression Vandermonde saturation -/

/-- Arithmetic-progression Vandermonde saturation: for any simple-spectrum Hamiltonian `H` and
step `0 < τ ≤ π / (‖H‖ + 1)`, the `2^N` samples `e^{-i m τ H}` (`m : Fin (2^N)`) are
`ℂ`-linearly independent and span the entire all-time trajectory space
`Submodule.span ℂ (range (unitaryEvolution H.val))` of dimension `2^N`. -/
theorem orbit_vandermonde_span_eq_spectralSpan {N : ℕ}
    (H : selfAdjoint (Register N))
    (hinj : Function.Injective H.2.isHermitian.eigenvalues)
    {τ : ℝ} (hτ_pos : 0 < τ) (hτ_le : τ ≤ Real.pi / (‖H.val‖ + 1)) :
    let U_step : Fin (2 ^ N) → Register N :=
      fun m => unitaryEvolution H.val ((m : ℕ) * τ)
    LinearIndependent ℂ U_step ∧
      Submodule.span ℂ (range U_step) = Submodule.span ℂ (range (unitaryEvolution H.val)) ∧
      Module.finrank ℂ (Submodule.span ℂ (range (unitaryEvolution H.val))) = 2 ^ N := by
  intro U_step
  let V := hermitianEigenbasisUnitary H.2.isHermitian
  let E := H.2.isHermitian.eigenvalues
  have hspec : H.val = V.val * Matrix.diagonal (Complex.ofReal ∘ E) * star V.val :=
    H.2.isHermitian.spectral_theorem
  have hE_bound (a : Config N) : |E a| ≤ ‖H.val‖ := by
    have hconj : star V.val * H.val * V.val = Matrix.diagonal (Complex.ofReal ∘ E) := by
      rw [hspec]
      exact star_conj_cancel V.2 _
    have hiso := l2_opNorm_unitary_conj_eq (Unitary.star_mem V.2) H.val
    rw [star_star, hconj] at hiso
    have hent := norm_entry_le_l2_opNorm (Matrix.diagonal (Complex.ofReal ∘ E)) a a
    rw [Matrix.diagonal_apply_eq, Function.comp_apply, Complex.norm_real, Real.norm_eq_abs] at hent
    exact hent.trans_eq hiso
  -- Spectral rank-one projectors P_eig a
  let P_eig : Config N → Register N :=
    fun a => V.val * Matrix.diagonal (Pi.single a (1 : ℂ)) * star V.val
  have hU_decomp (t : ℝ) :
      unitaryEvolution H.val t =
        ∑ a : Config N, Complex.exp (-(Complex.I * (t * E a))) • P_eig a := by
    rw [unitaryEvolution_spectral H.2.isHermitian t]
    have hdiag_sum : Matrix.diagonal (fun a => Complex.exp (-(Complex.I * (t * E a)))) =
        ∑ a : Config N, Complex.exp (-(Complex.I * (t * E a))) •
          Matrix.diagonal (Pi.single a (1 : ℂ)) := by
      ext i j
      rw [Matrix.sum_apply]
      by_cases hij : i = j
      · subst hij
        rw [Matrix.diagonal_apply_eq, Finset.sum_eq_single i]
        · simp [Matrix.diagonal]
        · intro b _ hbi
          simp [Matrix.diagonal, Pi.single_eq_of_ne hbi.symm]
        · simp
      · rw [Matrix.diagonal_apply_ne _ hij]
        refine (Finset.sum_eq_zero fun b _ => ?_).symm
        simp [Matrix.diagonal_apply_ne _ hij]
    rw [hdiag_sum, Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun a _ => ?_
    dsimp only [P_eig]
    rw [Matrix.mul_smul, Matrix.smul_mul]
    rfl
  have hP_li : LinearIndependent ℂ P_eig := by
    rw [Fintype.linearIndependent_iff]
    intro c hc a
    have hconj : star V.val * (∑ b : Config N, c b • P_eig b) * V.val = Matrix.diagonal c := by
      rw [Finset.mul_sum, Finset.sum_mul]
      ext i j
      rw [Matrix.sum_apply]
      have hterm (b : Config N) :
          star V.val * (c b • P_eig b) * V.val = c b • Matrix.diagonal (Pi.single b (1 : ℂ)) := by
        dsimp only [P_eig]
        rw [Matrix.mul_smul, Matrix.smul_mul, star_conj_cancel V.2]
      simp_rw [hterm]
      by_cases hij : i = j
      · subst hij
        rw [Matrix.diagonal_apply_eq, Finset.sum_eq_single i]
        · simp [Matrix.diagonal]
        · intro b _ hbi
          simp [Matrix.diagonal, Pi.single_eq_of_ne hbi.symm]
        · simp
      · rw [Matrix.diagonal_apply_ne _ hij]
        refine Finset.sum_eq_zero fun b _ => ?_
        simp [Matrix.diagonal_apply_ne _ hij]
    rw [hc, Matrix.mul_zero, Matrix.zero_mul] at hconj
    have ha := congrFun (congrFun hconj.symm a) a
    simpa only [Matrix.diagonal_apply_eq, Matrix.zero_apply] using ha
  -- Injectivity of z a = exp(-i τ E a)
  let z : Config N → ℂ := fun a => Complex.exp (-(Complex.I * (τ * E a)))
  have hz_inj : Function.Injective z := by
    intro a b hab
    obtain ⟨n, hn⟩ := Complex.exp_eq_exp_iff_exists_int.mp hab
    have him' : τ * (E b - E a) = (n : ℝ) * (2 * Real.pi) := by
      have hpi_im : (↑n * (2 * ↑Real.pi * Complex.I)).im = (n : ℝ) * (2 * Real.pi) := by
        simp [mul_assoc]
      have h1 := congrArg Complex.im hn
      rw [show (-(Complex.I * (↑τ * ↑(E a)))).im = -(τ * E a) by simp,
        show (-(Complex.I * (↑τ * ↑(E b))) + ↑n * (2 * ↑Real.pi * Complex.I)).im =
          -(τ * E b) + (n : ℝ) * (2 * Real.pi) by rw [Complex.add_im, hpi_im]; simp] at h1
      linarith only [h1]
    have hdiff_le : |E b - E a| ≤ 2 * ‖H.val‖ :=
      (abs_sub (E b) (E a)).trans (by linarith only [hE_bound b, hE_bound a])
    have hden_pos : 0 < ‖H.val‖ + 1 := add_pos_of_nonneg_of_pos (norm_nonneg _) zero_lt_one
    have hprod_lt : |τ * (E b - E a)| < 2 * Real.pi := by
      rw [abs_mul, abs_of_pos hτ_pos]
      have h1 : τ * |E b - E a| ≤ (Real.pi / (‖H.val‖ + 1)) * (2 * ‖H.val‖) :=
        mul_le_mul hτ_le hdiff_le (abs_nonneg _) (div_nonneg Real.pi_pos.le hden_pos.le)
      have h2 : (Real.pi / (‖H.val‖ + 1)) * (2 * ‖H.val‖) < 2 * Real.pi := by
        rw [div_mul_eq_mul_div, div_lt_iff₀ hden_pos]
        nlinarith only [Real.pi_pos, norm_nonneg H.val]
      exact h1.trans_lt h2
    rw [him', abs_mul, abs_of_pos (mul_pos two_pos Real.pi_pos)] at hprod_lt
    have hn_lt : |(n : ℝ)| < 1 := by
      nlinarith only [hprod_lt, mul_pos two_pos Real.pi_pos]
    have hn0_int : n = 0 := by
      have hcast : |(n : ℤ)| < (1 : ℤ) := by exact_mod_cast hn_lt
      obtain ⟨_, _⟩ := abs_lt.mp hcast
      omega
    rw [hn0_int, Int.cast_zero, zero_mul] at him'
    have hsub0 : E b - E a = 0 := (mul_eq_zero.mp him').resolve_left hτ_pos.ne'
    exact hinj (sub_eq_zero.mp hsub0).symm
  -- Reindex Config N by Fin (2^N) and invert Matrix.vandermonde
  let e_cfg : Fin (2 ^ N) ≃ Config N :=
    (finCongr (by simp [Config])).trans (Fintype.equivFin (Config N)).symm
  let v : Fin (2 ^ N) → ℂ := z ∘ e_cfg
  have hv_inj : Function.Injective v := hz_inj.comp e_cfg.injective
  let W := Matrix.vandermonde v
  have hW_det : W.det ≠ 0 := by
    dsimp only [W]
    rw [Matrix.det_vandermonde]
    refine Finset.prod_ne_zero_iff.mpr fun i _ => Finset.prod_ne_zero_iff.mpr fun j hj => ?_
    exact sub_ne_zero.mpr (hv_inj.ne (Finset.mem_Ioi.mp hj).ne')
  have hW_unit : IsUnit W.det := isUnit_iff_ne_zero.mpr hW_det
  have hWW_inv : W * W⁻¹ = 1 := Matrix.mul_nonsing_inv W hW_unit
  have hW_invW : W⁻¹ * W = 1 := Matrix.nonsing_inv_mul W hW_unit
  have hU_step_eq (m : Fin (2 ^ N)) :
      U_step m = ∑ j : Fin (2 ^ N), W j m • P_eig (e_cfg j) := by
    dsimp only [U_step]
    rw [hU_decomp (((m : ℕ) : ℝ) * τ), ← Equiv.sum_comp e_cfg]
    refine Finset.sum_congr rfl fun j _ => ?_
    congr 1
    dsimp only [W]
    rw [Matrix.vandermonde_apply]
    change Complex.exp _ = Complex.exp (-(Complex.I * (↑τ * ↑(E (e_cfg j))))) ^ (m : ℕ)
    rw [← Complex.exp_nat_mul]
    congr 1
    push_cast
    ring
  have hP_in_step (k : Fin (2 ^ N)) :
      P_eig (e_cfg k) = ∑ m : Fin (2 ^ N), W⁻¹ m k • U_step m := by
    simp_rw [hU_step_eq, Finset.smul_sum]
    rw [Finset.sum_comm]
    calc P_eig (e_cfg k)
        = ∑ j : Fin (2 ^ N), (1 : Matrix (Fin (2 ^ N)) (Fin (2 ^ N)) ℂ) j k • P_eig (e_cfg j) := by
            rw [Finset.sum_eq_single k (fun j _ hjk => by simp [Matrix.one_apply_ne hjk]) (by simp)]
            simp
      _ = ∑ j : Fin (2 ^ N), (W * W⁻¹) j k • P_eig (e_cfg j) := by rw [hWW_inv]
      _ = ∑ j : Fin (2 ^ N), ∑ m : Fin (2 ^ N), W⁻¹ m k • W j m • P_eig (e_cfg j) := by
            refine Finset.sum_congr rfl fun j _ => ?_
            rw [Matrix.mul_apply, Finset.sum_smul]
            refine Finset.sum_congr rfl fun m _ => ?_
            rw [smul_smul, mul_comm]
  have hspan_sub1 : Submodule.span ℂ (range U_step) ≤
      Submodule.span ℂ (range (unitaryEvolution H.val)) :=
    Submodule.span_mono (by rintro _ ⟨m, rfl⟩; exact ⟨((m : ℕ) : ℝ) * τ, rfl⟩)
  have hspan_sub2 : Submodule.span ℂ (range (unitaryEvolution H.val)) ≤
      Submodule.span ℂ (range P_eig) := by
    rw [Submodule.span_le]
    rintro _ ⟨t, rfl⟩
    rw [hU_decomp t]
    exact Submodule.sum_mem _ fun a _ =>
      Submodule.smul_mem _ _ (Submodule.subset_span (mem_range_self a))
  have hspan_sub3 : Submodule.span ℂ (range P_eig) ≤ Submodule.span ℂ (range U_step) := by
    rw [Submodule.span_le]
    rintro _ ⟨a, rfl⟩
    have ha : a = e_cfg (e_cfg.symm a) := (e_cfg.apply_symm_apply a).symm
    rw [ha, hP_in_step (e_cfg.symm a)]
    exact Submodule.sum_mem _ fun m _ =>
      Submodule.smul_mem _ _ (Submodule.subset_span (mem_range_self m))
  have hspan_eq : Submodule.span ℂ (range U_step) =
      Submodule.span ℂ (range (unitaryEvolution H.val)) :=
    le_antisymm hspan_sub1 (hspan_sub2.trans hspan_sub3)
  have hspan_P_eq : Submodule.span ℂ (range (unitaryEvolution H.val)) =
      Submodule.span ℂ (range P_eig) :=
    le_antisymm hspan_sub2 (hspan_sub3.trans hspan_sub1)
  have hfinrank : Module.finrank ℂ (Submodule.span ℂ (range (unitaryEvolution H.val))) = 2 ^ N := by
    rw [hspan_P_eq, finrank_span_eq_card hP_li]
    simp [Config]
  have hU_li : LinearIndependent ℂ U_step := by
    rw [Fintype.linearIndependent_iff]
    intro c hc
    have hPe_li : LinearIndependent ℂ (P_eig ∘ e_cfg) := hP_li.comp e_cfg e_cfg.injective
    have hexp : (∑ m : Fin (2 ^ N), c m • U_step m) =
        ∑ j : Fin (2 ^ N), (W *ᵥ c) j • (P_eig ∘ e_cfg) j := by
      simp_rw [hU_step_eq, Finset.smul_sum]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [Matrix.mulVec, dotProduct, Finset.sum_smul]
      refine Finset.sum_congr rfl fun m _ => ?_
      rw [smul_smul, mul_comm]
      rfl
    rw [hexp] at hc
    have hWc0 : W *ᵥ c = 0 := funext (Fintype.linearIndependent_iff.mp hPe_li (W *ᵥ c) hc)
    have hc0 : c = 0 := by
      calc c = (1 : Matrix (Fin (2 ^ N)) (Fin (2 ^ N)) ℂ) *ᵥ c := (Matrix.one_mulVec c).symm
        _ = (W⁻¹ * W) *ᵥ c := by rw [hW_invW]
        _ = W⁻¹ *ᵥ (W *ᵥ c) := (Matrix.mulVec_mulVec c W⁻¹ W).symm
        _ = 0 := by rw [hWc0, Matrix.mulVec_zero]
    exact fun m => congrFun hc0 m
  exact ⟨hU_li, hspan_eq, hfinrank⟩

/-! ## Section 3: Quenched multi-date trace-return-excised `r`-replica Gram onset law -/

private theorem finiteComplexInner_choi_eq_trace {N : ℕ} (A B : Register N) :
    finiteComplexInner (matrixNormalizedChoi A) (matrixNormalizedChoi B) =
      (((Fintype.card (Config N) : ℝ) : ℂ)⁻¹) * Matrix.trace (star A * B) := by
  unfold finiteComplexInner matrixNormalizedChoi
  have hD_pos : (0 : ℝ) < Fintype.card (Config N) := by
    simp [Config]
  have hsq : ((Real.sqrt (Fintype.card (Config N)) : ℂ) *
      (Real.sqrt (Fintype.card (Config N)) : ℂ)) = ((Fintype.card (Config N) : ℝ) : ℂ) := by
    norm_cast
    exact Real.mul_self_sqrt hD_pos.le
  have hterm (p : Config N × Config N) :
      conj (A p.1 p.2 / Real.sqrt (Fintype.card (Config N))) *
        (B p.1 p.2 / Real.sqrt (Fintype.card (Config N))) =
        (((Fintype.card (Config N) : ℝ) : ℂ)⁻¹) * (star (A p.1 p.2) * B p.1 p.2) := by
    rw [div_eq_mul_inv, div_eq_mul_inv, map_mul, map_inv₀, Complex.conj_ofReal]
    calc star (A p.1 p.2) * (Real.sqrt (Fintype.card (Config N)) : ℂ)⁻¹ *
          (B p.1 p.2 * (Real.sqrt (Fintype.card (Config N)) : ℂ)⁻¹)
        = (((Real.sqrt (Fintype.card (Config N)) : ℂ) *
            (Real.sqrt (Fintype.card (Config N)) : ℂ))⁻¹) *
            (star (A p.1 p.2) * B p.1 p.2) := by
            rw [mul_inv]; ring
      _ = (((Fintype.card (Config N) : ℝ) : ℂ)⁻¹) * (star (A p.1 p.2) * B p.1 p.2) := by
            rw [hsq]
  simp_rw [hterm]
  rw [← Finset.mul_sum]
  congr 1
  rw [Fintype.sum_prod_type, Finset.sum_comm, Matrix.trace]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [Matrix.diag_apply, Matrix.mul_apply]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Matrix.star_apply]

private theorem finiteComplexInner_choi_unitary {N : ℕ} {U : Register N}
    (hU : U ∈ unitary (Register N)) :
    finiteComplexInner (matrixNormalizedChoi U) (matrixNormalizedChoi U) = 1 := by
  rw [finiteComplexInner_choi_eq_trace, (Unitary.mem_iff.mp hU).1]
  simp [Matrix.trace, Config]

private theorem norm_sq_choi_le_opNorm_sq {N : ℕ} (X : Register N) :
    ‖WithLp.toLp 2 (matrixNormalizedChoi X)‖ ^ 2 ≤ ‖X‖ ^ 2 := by
  have hcol (j : Config N) : ∑ i : Config N, ‖X i j‖ ^ 2 ≤ ‖X‖ ^ 2 := by
    let ej : EuclideanSpace ℂ (Config N) := EuclideanSpace.single j (1 : ℂ)
    have hej : ‖ej‖ = 1 := by simp [ej]
    have hmul := Matrix.l2_opNorm_mulVec X ej
    rw [hej, mul_one] at hmul
    have hvec : X *ᵥ ej.ofLp = fun i => X i j := by
      funext i
      simp [ej, Matrix.mulVec, dotProduct, Finset.sum_ite_eq']
    let v : EuclideanSpace ℂ (Config N) := (EuclideanSpace.equiv (Config N) ℂ).symm (X *ᵥ ej.ofLp)
    have hv_le : ‖v‖ ^ 2 ≤ ‖X‖ ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) hmul 2
    have hv_eq : ‖v‖ ^ 2 = ∑ i : Config N, ‖X i j‖ ^ 2 := by
      rw [EuclideanSpace.norm_sq_eq]
      refine Finset.sum_congr rfl fun i _ => ?_
      change ‖(X *ᵥ ej.ofLp) i‖ ^ 2 = _
      rw [hvec]
    exact hv_eq ▸ hv_le
  have hD_pos : (0 : ℝ) < Fintype.card (Config N) := by
    simp [Config]
  rw [EuclideanSpace.norm_sq_eq, Fintype.sum_prod_type, Finset.sum_comm]
  have hinner_sum : (∑ j : Config N, ∑ i : Config N,
      ‖(WithLp.toLp 2 (matrixNormalizedChoi X)) (i, j)‖ ^ 2) =
      ((Fintype.card (Config N) : ℝ)⁻¹) * ∑ j : Config N, ∑ i : Config N, ‖X i j‖ ^ 2 := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    change ‖X i j / Real.sqrt (Fintype.card (Config N))‖ ^ 2 = _
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.sqrt_nonneg _), div_pow, Real.sq_sqrt hD_pos.le, div_eq_inv_mul]
  rw [hinner_sum]
  calc ((Fintype.card (Config N) : ℝ)⁻¹) * ∑ j : Config N, ∑ i : Config N, ‖X i j‖ ^ 2
      ≤ ((Fintype.card (Config N) : ℝ)⁻¹) * ∑ _j : Config N, ‖X‖ ^ 2 :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun j _ => hcol j) (inv_nonneg.mpr hD_pos.le)
    _ = ‖X‖ ^ 2 := by
        simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
        field_simp [hD_pos.ne']

/-- Global-phase-invariant operator-to-Choi fidelity floor: if `U ∈ U(2^N)` is `(ε, s)`-affordable
with `0 ≤ 1 - ε² / 2`, some circuit `C` with `C.gateCount ≤ s` achieves normalized Choi fidelity
at least `(1 - ε² / 2)²`. -/
theorem choiFidelity_ge_of_hasProjectiveCircuitApproximation {N s : ℕ}
    {U : Register N} (hU : U ∈ unitary (Register N)) {ε : ℝ}
    (h1 : 0 ≤ 1 - ε ^ 2 / 2)
    (hfit : HasProjectiveCircuitApproximation N ε s U) :
    ∃ C : {C : TwoQubitCircuit N // C.gateCount ≤ s},
      (1 - ε ^ 2 / 2) ^ 2 ≤
        finitePureStateFidelity (matrixNormalizedChoi U)
          (matrixNormalizedChoi (C.val.eval : Register N)) := by
  obtain ⟨z, hz, C, hC, herr⟩ := hfit
  refine ⟨⟨C, hC⟩, ?_⟩
  let u : EuclideanSpace ℂ (Config N × Config N) := WithLp.toLp 2 (matrixNormalizedChoi U)
  let v : EuclideanSpace ℂ (Config N × Config N) :=
    WithLp.toLp 2 (matrixNormalizedChoi (C.eval : Register N))
  have hu_norm : ‖u‖ = 1 := by
    have h := inner_toLp_eq_finiteComplexInner (matrixNormalizedChoi U) (matrixNormalizedChoi U)
    rw [finiteComplexInner_choi_unitary hU, inner_self_eq_norm_sq_to_K] at h
    have hsq : ‖u‖ ^ (2 : ℕ) = 1 := Complex.ofReal_injective (by simpa [u] using h)
    nlinarith only [hsq, norm_nonneg u]
  have hv_norm : ‖v‖ = 1 := by
    have h := inner_toLp_eq_finiteComplexInner
      (matrixNormalizedChoi (C.eval : Register N))
      (matrixNormalizedChoi (C.eval : Register N))
    rw [finiteComplexInner_choi_unitary C.eval.2, inner_self_eq_norm_sq_to_K] at h
    have hsq : ‖v‖ ^ (2 : ℕ) = 1 := Complex.ofReal_injective (by simpa [v] using h)
    nlinarith only [hsq, norm_nonneg v]
  have hdiff_vec : WithLp.toLp 2 (matrixNormalizedChoi (U - z • (C.eval : Register N))) =
      u - z • v := by
    ext p
    simp only [u, v, matrixNormalizedChoi, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul,
      PiLp.sub_apply, PiLp.smul_apply, sub_div, mul_div_assoc]
  have hchoi_le : ‖u - z • v‖ ^ 2 ≤ ε ^ 2 := by
    rw [← hdiff_vec]
    exact (norm_sq_choi_le_opNorm_sq _).trans (pow_le_pow_left₀ (norm_nonneg _) herr 2)
  have hsub_sq : ‖u - z • v‖ ^ 2 = 2 - 2 * (z * inner ℂ u v).re := by
    rw [@norm_sub_sq ℂ _ _ _ _ u (z • v), hu_norm, norm_smul, hz, one_mul, hv_norm,
      inner_smul_right]
    change _ = 2 - 2 * RCLike.re (z * inner ℂ u v)
    ring
  have hre_ge : 1 - ε ^ 2 / 2 ≤ (z * inner ℂ u v).re := by
    linarith only [hchoi_le, hsub_sq]
  have hnorm_ge : 1 - ε ^ 2 / 2 ≤ ‖inner ℂ u v‖ := by
    calc 1 - ε ^ 2 / 2 ≤ (z * inner ℂ u v).re := hre_ge
      _ ≤ ‖z * inner ℂ u v‖ := Complex.re_le_norm _
      _ = ‖inner ℂ u v‖ := by rw [norm_mul, hz, one_mul]
  rw [finitePureStateFidelity, ← inner_toLp_eq_finiteComplexInner]
  exact pow_le_pow_left₀ h1 hnorm_ge 2

private theorem prod_ofFn_pad_one {α : Type*} [Monoid α] {m : ℕ} (f : Fin m → α) :
    ∀ {s : ℕ}, m ≤ s →
      (List.ofFn (fun k : Fin s => if hk : k.val < m then f ⟨k.val, hk⟩ else 1)).prod =
        (List.ofFn f).prod := by
  intro s hms
  induction s, hms using Nat.le_induction with
  | base =>
      have hfn : (fun k : Fin m => if hk : k.val < m then f ⟨k.val, hk⟩ else 1) = f :=
        funext fun k => dif_pos k.isLt
      rw [hfn]
  | succ d hd ih =>
      have hlast : ¬ (Fin.last d).val < m := by rw [Fin.val_last]; omega
      rw [List.ofFn_succ', List.prod_concat, dif_neg hlast, mul_one]
      exact ih

private theorem finrank_replicaTargetSpan_atMost_choi_le {N s : ℕ} (hN : 1 ≤ N) (r : ℕ) :
    Module.finrank ℂ (replicaTargetSpan r
      (fun C : {C : TwoQubitCircuit N // C.gateCount ≤ s} =>
        matrixNormalizedChoi (C.val.eval : Register N))) ≤
      (N * N) ^ s * (r * s + 1) ^ (s * 16) := by
  let q₀ : Fin N := ⟨0, hN⟩
  let pos : {C : TwoQubitCircuit N // C.gateCount ≤ s} →
      TwoQubitCircuit.twoQubitCircuitArchitectureIndex N s :=
    fun C k => if hk : k.val < C.val.gateCount then C.val.reversePosition ⟨k.val, hk⟩ else (q₀, q₀)
  let G : {C : TwoQubitCircuit N // C.gateCount ≤ s} → Fin s → Register N :=
    fun C k => if hk : k.val < C.val.gateCount then C.val.reverseGate ⟨k.val, hk⟩ else 1
  have hG : ∀ C k, TwoQubitCircuit.IsTwoQubitGate (pos C k).1 (pos C k).2 (G C k) := by
    intro C k
    by_cases hk : k.val < C.val.gateCount
    · dsimp only [pos, G]
      rw [dif_pos hk, dif_pos hk]
      exact C.val.reverseGate_isTwoQubitGate ⟨k.val, hk⟩
    · dsimp only [pos, G]
      rw [dif_neg hk, dif_neg hk]
      exact TwoQubitCircuit.isTwoQubitGate_one q₀ q₀
  have htarget : (fun (C : {C : TwoQubitCircuit N // C.gateCount ≤ s})
      (p : Config N × Config N) =>
        (List.ofFn (G C)).prod p.1 p.2 / Real.sqrt (Fintype.card (Config N))) =
      fun C => matrixNormalizedChoi (C.val.eval : Register N) := by
    funext C p
    have hprod : (List.ofFn (G C)).prod = (C.val.eval : Register N) :=
      (prod_ofFn_pad_one C.val.reverseGate C.property).trans C.val.reverseGate_prod_eq_eval
    rw [hprod]
    rfl
  rw [← htarget]
  exact TwoQubitCircuit.finrank_replicaTargetSpan_twoQubitCircuitChoi_complete_le pos G hG r

private theorem dual_bessel_gershgorin_le {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    {M : ℕ} (hM : 1 ≤ M) (v : Fin M → E) (hv : ∀ a, ‖v a‖ = 1)
    {R : ℝ} (hR0 : 0 ≤ R) (hpair : ∀ a b : Fin M, a ≠ b → ‖inner ℂ (v a) (v b)‖ ≤ R)
    (w : E) (hw : ‖w‖ ≤ 1) :
    (1 / (M : ℝ)) * (∑ a : Fin M, ‖inner ℂ w (v a)‖ ^ 2) ≤ 1 / (M : ℝ) + R := by
  have hM_pos : (0 : ℝ) < M := by exact_mod_cast hM
  let z : Fin M → ℂ := fun a => inner ℂ w (v a)
  let S : ℝ := ∑ a : Fin M, ‖z a‖ ^ 2
  have hS_nn : 0 ≤ S := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hinner_eq : inner ℂ w (∑ a : Fin M, conj (z a) • v a) = (S : ℂ) := by
    rw [inner_sum]
    simp_rw [inner_smul_right]
    have hterm (a : Fin M) : conj (z a) * inner ℂ w (v a) = ((‖z a‖ ^ 2 : ℝ) : ℂ) := by
      change conj (z a) * z a = _
      rw [mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq]
    simp_rw [hterm]
    norm_cast
  have hcs_sq : S ^ 2 ≤ ‖∑ a : Fin M, conj (z a) • v a‖ ^ 2 := by
    have hcs := @norm_inner_le_norm ℂ E _ _ _ w (∑ a : Fin M, conj (z a) • v a)
    rw [hinner_eq, Complex.norm_real, Real.norm_of_nonneg hS_nn] at hcs
    have hle : S ≤ ‖∑ a : Fin M, conj (z a) • v a‖ :=
      hcs.trans (mul_le_of_le_one_left (norm_nonneg _) hw)
    exact pow_le_pow_left₀ hS_nn hle 2
  have hgram_le : ‖∑ a : Fin M, conj (z a) • v a‖ ^ 2 ≤ (1 + ((M : ℝ) - 1) * R) * S := by
    have hnorm_sq : ((‖∑ a : Fin M, conj (z a) • v a‖ ^ 2 : ℝ) : ℂ) =
        inner ℂ (∑ a : Fin M, conj (z a) • v a) (∑ b : Fin M, conj (z b) • v b) := by
      rw [inner_self_eq_norm_sq_to_K]; norm_cast
    have hre := congrArg Complex.re hnorm_sq
    simp only [Complex.ofReal_re] at hre
    rw [hre, sum_inner]
    simp_rw [inner_sum, inner_smul_left, inner_smul_right, Complex.conj_conj, Complex.re_sum]
    calc (∑ a : Fin M, ∑ b : Fin M, (z a * (conj (z b) * inner ℂ (v a) (v b))).re)
        ≤ ∑ a : Fin M, ∑ b : Fin M,
            if a = b then ‖z a‖ ^ 2 else R * ((‖z a‖ ^ 2 + ‖z b‖ ^ 2) / 2) := by
          refine Finset.sum_le_sum fun a _ => Finset.sum_le_sum fun b _ => ?_
          by_cases hab : a = b
          · subst hab
            have hva1 : inner ℂ (v a) (v a) = 1 := by
              rw [inner_self_eq_norm_sq_to_K, hv a]; norm_num
            rw [if_pos rfl, hva1, mul_one, Complex.mul_conj, Complex.normSq_eq_norm_sq,
              Complex.ofReal_re]
          · rw [if_neg hab]
            have h1 : (z a * (conj (z b) * inner ℂ (v a) (v b))).re ≤
                (‖z a‖ * ‖z b‖) * R := by
              calc (z a * (conj (z b) * inner ℂ (v a) (v b))).re
                  ≤ ‖z a * (conj (z b) * inner ℂ (v a) (v b))‖ := Complex.re_le_norm _
                _ = (‖z a‖ * ‖z b‖) * ‖inner ℂ (v a) (v b)‖ := by
                    rw [norm_mul, norm_mul, RCLike.norm_conj, mul_assoc]
                _ ≤ (‖z a‖ * ‖z b‖) * R :=
                    mul_le_mul_of_nonneg_left (hpair a b hab) (mul_nonneg (norm_nonneg _) (norm_nonneg _))
            have hamgm : ‖z a‖ * ‖z b‖ ≤ (‖z a‖ ^ 2 + ‖z b‖ ^ 2) / 2 := by
              nlinarith only [sq_nonneg (‖z a‖ - ‖z b‖)]
            exact h1.trans (by
              rw [mul_comm]
              exact mul_le_mul_of_nonneg_left hamgm hR0)
      _ = S + ((M : ℝ) - 1) * (R / 2) * S + ((M : ℝ) - 1) * (R / 2) * S := by
          have hsplit (a : Fin M) :
              (∑ b : Fin M, if a = b then ‖z a‖ ^ 2 else R * ((‖z a‖ ^ 2 + ‖z b‖ ^ 2) / 2)) =
                ‖z a‖ ^ 2 + ∑ b ∈ Finset.univ.erase a,
                  (R / 2 * ‖z a‖ ^ 2 + R / 2 * ‖z b‖ ^ 2) := by
            rw [← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ a), if_pos rfl]
            congr 1
            refine Finset.sum_congr rfl fun b hb => ?_
            rw [if_neg (Finset.ne_of_mem_erase hb).symm]
            ring
          simp_rw [hsplit]
          rw [Finset.sum_add_distrib]
          have herase_card (a : Fin M) : ((Finset.univ.erase a).card : ℝ) = (M : ℝ) - 1 := by
            rw [Finset.card_erase_of_mem (Finset.mem_univ a), Finset.card_univ, Fintype.card_fin,
              Nat.cast_sub hM, Nat.cast_one]
          have hpart1 : (∑ a : Fin M, ∑ b ∈ Finset.univ.erase a,
              (R / 2 * ‖z a‖ ^ 2 + R / 2 * ‖z b‖ ^ 2)) =
              ((M : ℝ) - 1) * (R / 2) * S + ((M : ℝ) - 1) * (R / 2) * S := by
            simp_rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul, herase_card]
            congr 1
            · dsimp only [S]
              rw [Finset.mul_sum]
              refine Finset.sum_congr rfl fun a _ => by ring
            · have herase_sum (a : Fin M) :
                  (∑ b ∈ Finset.univ.erase a, R / 2 * ‖z b‖ ^ 2) =
                    R / 2 * S - R / 2 * ‖z a‖ ^ 2 := by
                have hfull : R / 2 * S = R / 2 * ‖z a‖ ^ 2 +
                    ∑ b ∈ Finset.univ.erase a, R / 2 * ‖z b‖ ^ 2 := by
                  dsimp only [S]
                  rw [Finset.mul_sum, ← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ a)]
                linarith only [hfull]
              simp_rw [herase_sum, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
                Fintype.card_fin, nsmul_eq_mul, ← Finset.mul_sum]
              dsimp only [S]
              ring
          rw [hpart1]
          dsimp only [S]
          ring
      _ = (1 + ((M : ℝ) - 1) * R) * S := by ring
  have hS_le : S ≤ 1 + ((M : ℝ) - 1) * R := by
    by_cases hS0 : S = 0
    · rw [hS0]
      have hM1 : 0 ≤ (M : ℝ) - 1 := sub_nonneg.mpr (by exact_mod_cast hM)
      nlinarith only [hM1, hR0]
    · have hS_pos : 0 < S := lt_of_le_of_ne hS_nn (Ne.symm hS0)
      nlinarith only [hcs_sq, hgram_le, hS_pos]
  have hdiv : (1 / (M : ℝ)) * S ≤ (1 + ((M : ℝ) - 1) * R) / (M : ℝ) := by
    rw [one_div_mul_eq_div]
    exact div_le_div_of_nonneg_right hS_le hM_pos.le
  refine hdiv.trans ?_
  rw [div_le_iff₀ hM_pos]
  have h1 : (1 / (M : ℝ) + R) * (M : ℝ) = 1 + (M : ℝ) * R := by field_simp [hM_pos.ne']
  nlinarith only [h1, hR0]

/-- Deterministic quenched multi-date trace-return-excised `r`-replica Gram onset law:
if `M ≥ 1` sample dates `t_a ∈ [0, T]` satisfy pairwise trace-return excision
`2^{-N} ‖Tr(U(t_a)* U(t_b))‖ ≤ ρ` (`a ≠ b`) and
`((N * N)^s * (r * s + 1)^(16 s)) * (1 / M + ρ^r) < (199 / 200)^(2 r)` (`N ≥ 1`, `r ≥ 1`),
then `1 / (20 * (‖H‖ + 1)) < tenthPlateauOnset H s < T` and
`orbitCircuitDistance H s (tenthPlateauOnset H s) = 1 / 10`. -/
theorem tenthPlateauOnset_lt_of_returnExcised_replicaGram {N s r M : ℕ}
    (hN : 1 ≤ N) (_hr : 1 ≤ r) (hM : 1 ≤ M)
    (H : selfAdjoint (Register N)) {T ρ : ℝ} (_hT0 : 0 ≤ T) (hρ0 : 0 ≤ ρ)
    (t : Fin M → ℝ) (ht_mem : ∀ a : Fin M, t a ∈ Icc 0 T)
    (hexc : ∀ a b : Fin M, a ≠ b →
      ((2 : ℝ) ^ N)⁻¹ * ‖Matrix.trace (star (unitaryEvolution H.val (t a)) *
        unitaryEvolution H.val (t b))‖ ≤ ρ)
    (hgram : (((N * N) ^ s * (r * s + 1) ^ (s * 16) : ℕ) : ℝ) *
      (1 / (M : ℝ) + ρ ^ r) < (199 / 200 : ℝ) ^ (2 * r)) :
    1 / (20 * (‖H.val‖ + 1)) < tenthPlateauOnset H s ∧
      tenthPlateauOnset H s < T ∧
      orbitCircuitDistance H s (tenthPlateauOnset H s) = 1 / 10 := by
  have hnot_all : ¬ ∀ a : Fin M,
      HasProjectiveCircuitApproximation N (1 / 10 : ℝ) s (unitaryEvolution H.val (t a)) := by
    intro hall
    let target : {C : TwoQubitCircuit N // C.gateCount ≤ s} → Config N × Config N → ℂ :=
      fun C => matrixNormalizedChoi (C.val.eval : Register N)
    let S_sub := replicaTargetSpan r target
    let Ψ : Fin M → EuclideanSpace ℂ (Fin r → Config N × Config N) :=
      fun a => finitePureTensorPowerEuclidean r
        (matrixNormalizedChoi (unitaryEvolution H.val (t a)))
    have hΨ_norm (a : Fin M) : ‖Ψ a‖ = 1 :=
      norm_finitePureTensorPowerEuclidean_eq_one r _
        (finiteComplexInner_choi_unitary (unitaryEvolution_mem_unitary H.2 (t a)))
    have hpair (a b : Fin M) (hab : a ≠ b) : ‖inner ℂ (Ψ a) (Ψ b)‖ ≤ ρ ^ r := by
      rw [inner_finitePureTensorPowerEuclidean, finiteComplexInner_choi_eq_trace, norm_pow]
      refine pow_le_pow_left₀ (norm_nonneg _) ?_ r
      have hcard : (Fintype.card (Config N) : ℝ) = (2 : ℝ) ^ N := by simp [Config]
      rw [norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs, hcard,
        abs_of_pos (pow_pos two_pos N)]
      exact hexc a b hab
    have hmass_ge (a : Fin M) :
        (199 / 200 : ℝ) ^ (2 * r) ≤
          replicaTargetProjectionMass r target
            (matrixNormalizedChoi (unitaryEvolution H.val (t a))) := by
      obtain ⟨C, hfid⟩ := choiFidelity_ge_of_hasProjectiveCircuitApproximation
        (unitaryEvolution_mem_unitary H.2 (t a)) (by norm_num) (hall a)
      have h199 : (1 - (1 / 10 : ℝ) ^ 2 / 2) ^ 2 = (199 / 200 : ℝ) ^ 2 := by norm_num
      rw [h199] at hfid
      have htarget_norm : ‖finitePureTensorPowerEuclidean r (target C)‖ ≤ 1 :=
        (norm_finitePureTensorPowerEuclidean_eq_one r _
          (finiteComplexInner_choi_unitary C.val.eval.2)).le
      have hdom := finitePureStateFidelity_pow_le_replicaTargetProjectionMass r target
        (matrixNormalizedChoi (unitaryEvolution H.val (t a))) C htarget_norm
      calc (199 / 200 : ℝ) ^ (2 * r) = ((199 / 200 : ℝ) ^ 2) ^ r := pow_mul _ 2 r
        _ ≤ finitePureStateFidelity (matrixNormalizedChoi (unitaryEvolution H.val (t a)))
              (target C) ^ r := pow_le_pow_left₀ (by norm_num) hfid r
        _ ≤ _ := hdom
    have hM_pos : (0 : ℝ) < M := by exact_mod_cast hM
    have havg_ge : (199 / 200 : ℝ) ^ (2 * r) ≤
        (1 / (M : ℝ)) * ∑ a : Fin M,
          replicaTargetProjectionMass r target
            (matrixNormalizedChoi (unitaryEvolution H.val (t a))) := by
      calc (199 / 200 : ℝ) ^ (2 * r)
          = (1 / (M : ℝ)) * ∑ _a : Fin M, (199 / 200 : ℝ) ^ (2 * r) := by
              simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
              field_simp [hM_pos.ne']
        _ ≤ (1 / (M : ℝ)) * ∑ a : Fin M,
              replicaTargetProjectionMass r target
                (matrixNormalizedChoi (unitaryEvolution H.val (t a))) :=
              mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun a _ => hmass_ge a)
                (one_div_nonneg.mpr hM_pos.le)
    let b_onb := replicaSubspaceOrthonormalBasis r S_sub
    have havg_le : (1 / (M : ℝ)) * ∑ a : Fin M,
        replicaTargetProjectionMass r target
          (matrixNormalizedChoi (unitaryEvolution H.val (t a))) ≤
        (Module.finrank ℂ S_sub : ℝ) * (1 / (M : ℝ) + ρ ^ r) := by
      simp_rw [replicaTargetProjectionMass_eq_sum_coordinate_norm_sq]
      rw [Finset.sum_comm, Finset.mul_sum]
      calc (∑ i : Fin (Module.finrank ℂ S_sub),
            (1 / (M : ℝ)) * ∑ a : Fin M,
              ‖replicaTargetCoordinate r target
                (matrixNormalizedChoi (unitaryEvolution H.val (t a))) i‖ ^ 2)
          ≤ ∑ _i : Fin (Module.finrank ℂ S_sub), (1 / (M : ℝ) + ρ ^ r) := by
            refine Finset.sum_le_sum fun i _ => ?_
            let wi : EuclideanSpace ℂ (Fin r → Config N × Config N) := ((b_onb i : S_sub) : _)
            have hwi_norm : ‖wi‖ ≤ 1 := by
              have h1 : ‖b_onb i‖ = 1 := b_onb.norm_eq_one i
              exact h1.le
            exact dual_bessel_gershgorin_le hM Ψ hΨ_norm (pow_nonneg hρ0 r) hpair wi hwi_norm
        _ = (Module.finrank ℂ S_sub : ℝ) * (1 / (M : ℝ) + ρ ^ r) := by
            simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    have hdim := finrank_replicaTargetSpan_atMost_choi_le (s := s) hN r
    have hdim_real : (Module.finrank ℂ S_sub : ℝ) ≤
        (((N * N) ^ s * (r * s + 1) ^ (s * 16) : ℕ) : ℝ) := by exact_mod_cast hdim
    have htot := havg_ge.trans (havg_le.trans
      (mul_le_mul_of_nonneg_right hdim_real
        (add_nonneg (one_div_nonneg.mpr hM_pos.le) (pow_nonneg hρ0 r))))
    exact hgram.not_ge htot
  push Not at hnot_all
  obtain ⟨a, hnot_a⟩ := hnot_all
  obtain ⟨hlo, hhi_a, _, heq, _⟩ := tenthPlateauOnset_lt_of_not_affordable H (ht_mem a).1 hnot_a
  exact ⟨hlo, hhi_a.trans_le (ht_mem a).2, heq⟩

/-! ## Section 4: All-`r` Krylov causal barrier -/

private def eigSlotVec {N : ℕ} (V : UGroup N) (a : Config N) (p : Config N × Config N) : ℂ :=
  V.val p.1 a * star (V.val p.2 a)

private def eigProdVec {N r : ℕ} (V : UGroup N) (α : Fin r → Config N) :
    EuclideanSpace ℂ (Fin r → Config N × Config N) :=
  WithLp.toLp 2 fun q => ∏ l : Fin r, eigSlotVec V (α l) (q l)

private theorem inner_eigProdVec {N r : ℕ} (V : UGroup N) (α β : Fin r → Config N) :
    inner ℂ (eigProdVec V α) (eigProdVec V β) = if α = β then 1 else 0 := by
  have hslot (a b : Config N) :
      (∑ p : Config N × Config N, conj (eigSlotVec V a p) * eigSlotVec V b p) =
        if a = b then 1 else 0 := by
    rw [Fintype.sum_prod_type]
    have h1 (x y : Config N) :
        conj (eigSlotVec V a (x, y)) * eigSlotVec V b (x, y) =
          (star (V.val x a) * V.val x b) * (V.val y a * star (V.val y b)) := by
      dsimp only [eigSlotVec, Complex.star_def]
      rw [map_mul, Complex.conj_conj]
      ring
    simp_rw [h1, ← Finset.mul_sum, ← Finset.sum_mul]
    have hVV : star V.val * V.val = 1 := (Unitary.mem_iff.mp V.2).1
    have hcol1 : (∑ x : Config N, star (V.val x a) * V.val x b) =
        (star V.val * V.val) a b := by
      rw [Matrix.mul_apply]
      refine Finset.sum_congr rfl fun x _ => by rw [Matrix.star_apply]
    have hcol2 : (∑ y : Config N, V.val y a * star (V.val y b)) =
        (star V.val * V.val) b a := by
      rw [Matrix.mul_apply]
      refine Finset.sum_congr rfl fun y _ => by rw [Matrix.star_apply, mul_comm]
    rw [hcol1, hcol2, hVV]
    by_cases hab : a = b
    · subst hab; simp
    · rw [if_neg hab, Matrix.one_apply_ne hab, zero_mul]
  dsimp only [eigProdVec]
  rw [inner_toLp_eq_finiteComplexInner]
  unfold finiteComplexInner
  have hterm (q : Fin r → Config N × Config N) :
      conj (∏ l : Fin r, eigSlotVec V (α l) (q l)) *
        (∏ l : Fin r, eigSlotVec V (β l) (q l)) =
        ∏ l : Fin r, (conj (eigSlotVec V (α l) (q l)) * eigSlotVec V (β l) (q l)) := by
    rw [map_prod, ← Finset.prod_mul_distrib]
  simp_rw [hterm]
  rw [← Fintype.prod_sum (fun l p => conj (eigSlotVec V (α l) p) * eigSlotVec V (β l) p)]
  simp_rw [hslot]
  by_cases hαβ : α = β
  · subst hαβ
    simp
  · rw [if_neg hαβ]
    obtain ⟨l, hl⟩ : ∃ l : Fin r, α l ≠ β l := by simpa only [Function.ne_iff] using hαβ
    exact Finset.prod_eq_zero (Finset.mem_univ l) (if_neg hl)

private theorem norm_sq_sum_eigProdVec {N r : ℕ} (V : UGroup N)
    (w : (Fin r → Config N) → ℂ) :
    ‖∑ α : Fin r → Config N, w α • eigProdVec V α‖ ^ 2 =
      ∑ α : Fin r → Config N, ‖w α‖ ^ 2 := by
  have h1 : ((‖∑ α : Fin r → Config N, w α • eigProdVec V α‖ ^ 2 : ℝ) : ℂ) =
      inner ℂ (∑ α, w α • eigProdVec V α) (∑ β, w β • eigProdVec V β) := by
    rw [inner_self_eq_norm_sq_to_K]; norm_cast
  rw [sum_inner] at h1
  simp_rw [inner_sum, inner_smul_left, inner_smul_right, inner_eigProdVec] at h1
  have h2 : (∑ α : Fin r → Config N, ∑ β : Fin r → Config N,
      conj (w α) * (w β * if α = β then (1 : ℂ) else 0)) =
      ∑ α : Fin r → Config N, ((‖w α‖ ^ 2 : ℝ) : ℂ) := by
    refine Finset.sum_congr rfl fun α _ => ?_
    rw [Finset.sum_eq_single α
      (fun β _ hβα => by simp [hβα.symm]) (by simp)]
    rw [if_pos rfl, mul_one, mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  rw [h2] at h1
  exact Complex.ofReal_injective (by simpa using h1)

private theorem bddAbove_empiricalReplicaBessel {N M : ℕ}
    (H : selfAdjoint (Register N)) (r : ℕ) (t : Fin M → ℝ) :
    BddAbove {val : ℝ | ∃ w : EuclideanSpace ℂ (Fin r → Config N × Config N), ‖w‖ ≤ 1 ∧
      val = (1 / (M : ℝ)) * ∑ a : Fin M,
        ‖inner ℂ w (finitePureTensorPowerEuclidean r
          (matrixNormalizedChoi (unitaryEvolution H.val (t a))))‖ ^ 2} := by
  refine ⟨1, ?_⟩
  rintro val ⟨w, hw, rfl⟩
  by_cases hM0 : M = 0
  · subst hM0; simp
  · have hM_pos : (0 : ℝ) < M := by exact_mod_cast Nat.pos_of_ne_zero hM0
    have hterm (a : Fin M) :
        ‖inner ℂ w (finitePureTensorPowerEuclidean r
          (matrixNormalizedChoi (unitaryEvolution H.val (t a))))‖ ^ 2 ≤ 1 := by
      have hΨ : ‖finitePureTensorPowerEuclidean r
          (matrixNormalizedChoi (unitaryEvolution H.val (t a)))‖ = 1 :=
        norm_finitePureTensorPowerEuclidean_eq_one r _
          (finiteComplexInner_choi_unitary (unitaryEvolution_mem_unitary H.2 (t a)))
      have hcs := @norm_inner_le_norm ℂ _ _ _ _ w
        (finitePureTensorPowerEuclidean r (matrixNormalizedChoi (unitaryEvolution H.val (t a))))
      rw [hΨ, mul_one] at hcs
      have hle1 : ‖inner ℂ w (finitePureTensorPowerEuclidean r
          (matrixNormalizedChoi (unitaryEvolution H.val (t a))))‖ ≤ 1 := hcs.trans hw
      nlinarith only [hle1, norm_nonneg (inner ℂ w (finitePureTensorPowerEuclidean r
        (matrixNormalizedChoi (unitaryEvolution H.val (t a)))))]
    calc (1 / (M : ℝ)) * ∑ a : Fin M,
          ‖inner ℂ w (finitePureTensorPowerEuclidean r
            (matrixNormalizedChoi (unitaryEvolution H.val (t a))))‖ ^ 2
        ≤ (1 / (M : ℝ)) * ∑ _a : Fin M, (1 : ℝ) :=
          mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun a _ => hterm a)
            (one_div_nonneg.mpr hM_pos.le)
      _ = 1 := by
          simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
          exact one_div_mul_cancel hM_pos.ne'

/-- Universal Taylor-Krylov lower bound on the empirical `r`-replica Bessel constant:
for every `H`, `r ≥ 1`, `M ≥ 1`, `T ≥ 0`, `t : Fin M → [-T, T]`, and degree `K ∈ ℕ` with
`η_K = (r * ‖H‖ * T)^(K + 1) / (K + 1)! ≤ 1`,
`(1 - η_K)^2 ≤ (K + 1) * empiricalReplicaBessel H r t`. -/
theorem krylov_empiricalBessel_lower_bound {N M : ℕ}
    (H : selfAdjoint (Register N)) {r K : ℕ} (hM : 1 ≤ M) {T : ℝ} (hT0 : 0 ≤ T)
    (t : Fin M → ℝ) (ht : ∀ a : Fin M, |t a| ≤ T)
    (hη : ((r : ℝ) * ‖H.val‖ * T) ^ (K + 1) / ((K + 1).factorial : ℝ) ≤ 1) :
    let η := ((r : ℝ) * ‖H.val‖ * T) ^ (K + 1) / ((K + 1).factorial : ℝ)
    (1 - η) ^ 2 ≤ ((K + 1 : ℕ) : ℝ) * empiricalReplicaBessel H r t := by
  intro η
  let V := hermitianEigenbasisUnitary H.2.isHermitian
  let E := H.2.isHermitian.eigenvalues
  have hspec : H.val = V.val * Matrix.diagonal (Complex.ofReal ∘ E) * star V.val :=
    H.2.isHermitian.spectral_theorem
  have hE_bound (a : Config N) : |E a| ≤ ‖H.val‖ := by
    have hconj : star V.val * H.val * V.val = Matrix.diagonal (Complex.ofReal ∘ E) := by
      rw [hspec]; exact star_conj_cancel V.2 _
    have hiso := l2_opNorm_unitary_conj_eq (Unitary.star_mem V.2) H.val
    rw [star_star, hconj] at hiso
    have hent := norm_entry_le_l2_opNorm (Matrix.diagonal (Complex.ofReal ∘ E)) a a
    rw [Matrix.diagonal_apply_eq, Function.comp_apply, Complex.norm_real, Real.norm_eq_abs] at hent
    exact hent.trans_eq hiso
  let Ω : (Fin r → Config N) → ℝ := fun α => ∑ l : Fin r, E (α l)
  have hΩ_bound (α : Fin r → Config N) : |Ω α| ≤ (r : ℝ) * ‖H.val‖ := by
    dsimp only [Ω]
    calc |∑ l : Fin r, E (α l)| ≤ ∑ l : Fin r, |E (α l)| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _l : Fin r, ‖H.val‖ := Finset.sum_le_sum fun l _ => hE_bound (α l)
      _ = (r : ℝ) * ‖H.val‖ := by simp [Finset.sum_const, nsmul_eq_mul]
  let inv_s : ℂ := ((Real.sqrt (Fintype.card (Config N)) : ℂ)⁻¹) ^ r
  have hD_pos : (0 : ℝ) < Fintype.card (Config N) := by
    simp [Config]
  have hinv_s_sq : ‖inv_s‖ ^ 2 = ((Fintype.card (Config N) ^ r : ℕ) : ℝ)⁻¹ := by
    dsimp only [inv_s]
    rw [norm_pow, norm_inv, Complex.norm_real, Real.norm_of_nonneg (Real.sqrt_nonneg _),
      ← pow_mul, mul_comm r 2, pow_mul, inv_pow, Real.sq_sqrt hD_pos.le]
    push_cast
    exact inv_pow (Fintype.card (Config N) : ℝ) r
  let Ψ : ℝ → EuclideanSpace ℂ (Fin r → Config N × Config N) :=
    fun s => finitePureTensorPowerEuclidean r (matrixNormalizedChoi (unitaryEvolution H.val s))
  have hΨ_decomp (s : ℝ) :
      Ψ s = ∑ α : Fin r → Config N,
        (inv_s * Complex.exp (s • ((-Complex.I) • (Ω α : ℂ)))) • eigProdVec V α := by
    ext q
    have hslot_sum (p : Config N × Config N) :
        matrixNormalizedChoi (unitaryEvolution H.val s) p =
          ((Real.sqrt (Fintype.card (Config N)) : ℂ)⁻¹) *
            ∑ c : Config N, Complex.exp (-(Complex.I * (s * E c))) * eigSlotVec V c p := by
      unfold matrixNormalizedChoi
      rw [div_eq_inv_mul]
      congr 1
      have h1 (c : Config N) :
          (V.val * Matrix.diagonal fun i => Complex.exp (-(Complex.I * (s * E i)))) p.1 c =
            V.val p.1 c * Complex.exp (-(Complex.I * (s * E c))) := by
        rw [Matrix.mul_apply, Finset.sum_eq_single c
          (fun b _ hbc => by simp [Matrix.diagonal_apply_ne _ hbc]) (by simp)]
        simp
      rw [unitaryEvolution_spectral H.2.isHermitian s]
      change ((V.val * Matrix.diagonal fun i => Complex.exp (-(Complex.I * (s * E i)))) *
        star V.val) p.1 p.2 = _
      rw [Matrix.mul_apply]
      refine Finset.sum_congr rfl fun c _ => ?_
      rw [h1 c, Matrix.star_apply]
      dsimp only [eigSlotVec]
      ring
    change (∏ l : Fin r, matrixNormalizedChoi (unitaryEvolution H.val s) (q l)) =
      (∑ α : Fin r → Config N,
        (inv_s * Complex.exp (s • ((-Complex.I) • (Ω α : ℂ)))) • eigProdVec V α).ofLp q
    simp_rw [hslot_sum, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ,
      Fintype.card_fin]
    rw [Fintype.prod_sum]
    have hofLp_sum (S : Finset (Fin r → Config N))
        (f : (Fin r → Config N) → EuclideanSpace ℂ (Fin r → Config N × Config N)) :
        (∑ α ∈ S, f α).ofLp q = ∑ α ∈ S, (f α).ofLp q := by
      classical
      induction S using Finset.induction_on with
      | empty => rfl
      | @insert a S ha ih => rw [Finset.sum_insert ha, PiLp.add_apply, ih, Finset.sum_insert ha]
    have hsum_apply :
        (∑ α : Fin r → Config N,
          (inv_s * Complex.exp (s • ((-Complex.I) • (Ω α : ℂ)))) • eigProdVec V α).ofLp q =
        ∑ α : Fin r → Config N,
          (inv_s * Complex.exp (s • ((-Complex.I) • (Ω α : ℂ)))) *
            ∏ l : Fin r, eigSlotVec V (α l) (q l) := by
      rw [hofLp_sum]
      rfl
    rw [hsum_apply, Finset.mul_sum]
    refine Finset.sum_congr rfl fun α _ => ?_
    dsimp only [inv_s, Ω]
    have hexp_prod : (∏ l : Fin r, Complex.exp (-(Complex.I * (s * E (α l))))) =
        Complex.exp (s • ((-Complex.I) • ((∑ l : Fin r, E (α l) : ℝ) : ℂ))) := by
      rw [← Complex.exp_sum]
      congr 1
      simp only [Complex.real_smul, smul_eq_mul, Complex.ofReal_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun l _ => by ring
    rw [Finset.prod_mul_distrib, hexp_prod, mul_assoc]
  -- Krylov basis vectors v_k (0 ≤ k ≤ K)
  let v_kry : Fin (K + 1) → EuclideanSpace ℂ (Fin r → Config N × Config N) :=
    fun k => ∑ α : Fin r → Config N,
      (inv_s * ((-Complex.I) • (Ω α : ℂ)) ^ (k : ℕ)) • eigProdVec V α
  let K_sub : Submodule ℂ (EuclideanSpace ℂ (Fin r → Config N × Config N)) :=
    Submodule.span ℂ (range v_kry)
  have hK_dim : Module.finrank ℂ K_sub ≤ K + 1 := by
    classical
    refine le_trans (finrank_span_le_card _) ?_
    rw [Set.toFinset_range]
    exact Finset.card_image_le.trans (by simp)
  have hproj_ge (a : Fin M) : 1 - η ≤ ‖K_sub.starProjection (Ψ (t a))‖ := by
    let T_vec : EuclideanSpace ℂ (Fin r → Config N × Config N) :=
      ∑ k : Fin (K + 1), (((t a ^ (k : ℕ) / ((k : ℕ).factorial : ℝ) : ℝ) : ℂ)) • v_kry k
    have hT_mem : T_vec ∈ K_sub :=
      Submodule.sum_mem _ fun k _ =>
        Submodule.smul_mem _ _ (Submodule.subset_span (mem_range_self k))
    have hdiff_eq : Ψ (t a) - T_vec =
        ∑ α : Fin r → Config N,
          (inv_s * (NormedSpace.exp (t a • ((-Complex.I) • (Ω α : ℂ))) -
            selfAdjointHamiltonianTaylor (Ω α : ℂ) K (t a))) • eigProdVec V α := by
      have hTay_eq : T_vec = ∑ α : Fin r → Config N,
          (inv_s * selfAdjointHamiltonianTaylor (Ω α : ℂ) K (t a)) • eigProdVec V α := by
        dsimp only [T_vec, v_kry, selfAdjointHamiltonianTaylor, cstarExponentialTaylor]
        simp_rw [Finset.smul_sum]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun α _ => ?_
        rw [← Fin.sum_univ_eq_sum_range, Finset.mul_sum, Finset.sum_smul]
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [smul_smul]
        congr 1
        simp only [Complex.real_smul]
        ring
      rw [hΨ_decomp (t a), hTay_eq, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun α _ => ?_
      rw [← sub_smul, mul_sub, congrFun Complex.exp_eq_exp_ℂ]
    have hrem_α (α : Fin r → Config N) :
        ‖NormedSpace.exp (t a • ((-Complex.I) • (Ω α : ℂ))) -
          selfAdjointHamiltonianTaylor (Ω α : ℂ) K (t a)‖ ≤ η := by
      have hsa : IsSelfAdjoint (Ω α : ℂ) := Complex.conj_ofReal (Ω α)
      have h1 := norm_selfAdjoint_exp_sub_hamiltonianTaylor_le (Ω α : ℂ) hsa K (t a)
      rw [Complex.norm_real, Real.norm_eq_abs] at h1
      have hprod_le : |Ω α| ^ (K + 1) * |t a| ^ (K + 1) ≤ ((r : ℝ) * ‖H.val‖ * T) ^ (K + 1) := by
        rw [← mul_pow]
        exact pow_le_pow_left₀ (mul_nonneg (abs_nonneg _) (abs_nonneg _))
          (mul_le_mul (hΩ_bound α) (ht a) (abs_nonneg _)
            (mul_nonneg (Nat.cast_nonneg r) (norm_nonneg _))) (K + 1)
      exact h1.trans (div_le_div_of_nonneg_right hprod_le (Nat.cast_nonneg _))
    have hη_nn : 0 ≤ η := div_nonneg
      (pow_nonneg (mul_nonneg (mul_nonneg (Nat.cast_nonneg r) (norm_nonneg _)) hT0) _)
      (Nat.cast_nonneg _)
    have hdiff_sq : ‖Ψ (t a) - T_vec‖ ^ 2 ≤ η ^ 2 := by
      rw [hdiff_eq, norm_sq_sum_eigProdVec]
      calc (∑ α : Fin r → Config N,
            ‖inv_s * (NormedSpace.exp (t a • ((-Complex.I) • (Ω α : ℂ))) -
              selfAdjointHamiltonianTaylor (Ω α : ℂ) K (t a))‖ ^ 2)
          ≤ ∑ _α : Fin r → Config N, ‖inv_s‖ ^ 2 * η ^ 2 := by
            refine Finset.sum_le_sum fun α _ => ?_
            rw [norm_mul, mul_pow]
            exact mul_le_mul_of_nonneg_left
              (pow_le_pow_left₀ (norm_nonneg _) (hrem_α α) 2) (sq_nonneg _)
        _ = η ^ 2 := by
            rw [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_fin,
              nsmul_eq_mul, hinv_s_sq, ← mul_assoc,
              mul_inv_cancel₀ (Nat.cast_ne_zero.mpr (pow_ne_zero r (by simp [Config]))), one_mul]
    have hdiff_le : ‖Ψ (t a) - T_vec‖ ≤ η :=
      (sq_le_sq₀ (norm_nonneg _) hη_nn).mp hdiff_sq
    have hproj_dist : ‖Ψ (t a) - K_sub.starProjection (Ψ (t a))‖ ≤ η :=
      (norm_sub_starProjection_le_of_mem K_sub (Ψ (t a)) hT_mem).trans hdiff_le
    have hΨ_norm : ‖Ψ (t a)‖ = 1 :=
      norm_finitePureTensorPowerEuclidean_eq_one r _
        (finiteComplexInner_choi_unitary (unitaryEvolution_mem_unitary H.2 (t a)))
    have htri : ‖Ψ (t a)‖ ≤
        ‖K_sub.starProjection (Ψ (t a))‖ + ‖Ψ (t a) - K_sub.starProjection (Ψ (t a))‖ := by
      simpa only [add_sub_cancel] using
        norm_add_le (K_sub.starProjection (Ψ (t a))) (Ψ (t a) - K_sub.starProjection (Ψ (t a)))
    linarith only [hΨ_norm, htri, hproj_dist]
  have h1_sub_nn : 0 ≤ 1 - η := sub_nonneg.mpr hη
  have hM_pos : (0 : ℝ) < M := by exact_mod_cast hM
  have hbessel_nn : 0 ≤ empiricalReplicaBessel H r t := by
    have h0_mem : (0 : ℝ) ∈ {val : ℝ | ∃ w : EuclideanSpace ℂ (Fin r → Config N × Config N),
        ‖w‖ ≤ 1 ∧ val = (1 / (M : ℝ)) * ∑ a : Fin M,
          ‖inner ℂ w (finitePureTensorPowerEuclidean r
            (matrixNormalizedChoi (unitaryEvolution H.val (t a))))‖ ^ 2} :=
      ⟨0, norm_zero.trans_le zero_le_one, by simp⟩
    exact le_csSup (bddAbove_empiricalReplicaBessel H r t) h0_mem
  let b_kry := stdOrthonormalBasis ℂ K_sub
  have hparseval (a : Fin M) :
      ‖K_sub.starProjection (Ψ (t a))‖ ^ 2 =
        ∑ i : Fin (Module.finrank ℂ K_sub),
          ‖inner ℂ ((b_kry i : K_sub) : EuclideanSpace ℂ (Fin r → Config N × Config N))
            (Ψ (t a))‖ ^ 2 := by
    let p_sub : K_sub := K_sub.orthogonalProjectionOnto (Ψ (t a))
    change ‖p_sub‖ ^ (2 : ℕ) = _
    rw [← b_kry.sum_sq_norm_inner_right p_sub]
    refine Finset.sum_congr rfl fun i _ => ?_
    change ‖inner ℂ (b_kry i) (K_sub.orthogonalProjectionOnto (Ψ (t a)))‖ ^ (2 : ℕ) = _
    rw [K_sub.inner_orthogonalProjectionOnto_eq_of_mem_left]
  have havg_sq : (1 - η) ^ 2 ≤
      (1 / (M : ℝ)) * ∑ a : Fin M, ‖K_sub.starProjection (Ψ (t a))‖ ^ 2 := by
    calc (1 - η) ^ 2 = (1 / (M : ℝ)) * ∑ _a : Fin M, (1 - η) ^ 2 := by
          simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
          field_simp [hM_pos.ne']
      _ ≤ (1 / (M : ℝ)) * ∑ a : Fin M, ‖K_sub.starProjection (Ψ (t a))‖ ^ 2 :=
          mul_le_mul_of_nonneg_left
            (Finset.sum_le_sum fun a _ => pow_le_pow_left₀ h1_sub_nn (hproj_ge a) 2)
            (one_div_nonneg.mpr hM_pos.le)
  have hsum_le : (1 / (M : ℝ)) * ∑ a : Fin M, ‖K_sub.starProjection (Ψ (t a))‖ ^ 2 ≤
      (Module.finrank ℂ K_sub : ℝ) * empiricalReplicaBessel H r t := by
    simp_rw [hparseval]
    rw [Finset.sum_comm, Finset.mul_sum]
    calc (∑ i : Fin (Module.finrank ℂ K_sub),
          (1 / (M : ℝ)) * ∑ a : Fin M,
            ‖inner ℂ ((b_kry i : K_sub) : EuclideanSpace ℂ (Fin r → Config N × Config N))
              (Ψ (t a))‖ ^ 2)
        ≤ ∑ _i : Fin (Module.finrank ℂ K_sub), empiricalReplicaBessel H r t := by
          refine Finset.sum_le_sum fun i _ => ?_
          refine le_csSup (bddAbove_empiricalReplicaBessel H r t) ⟨((b_kry i : K_sub) : _), ?_, rfl⟩
          exact (b_kry.norm_eq_one i).le
      _ = (Module.finrank ℂ K_sub : ℝ) * empiricalReplicaBessel H r t := by
          simp [Finset.sum_const, nsmul_eq_mul]
  exact havg_sq.trans (hsum_le.trans
    (mul_le_mul_of_nonneg_right (by exact_mod_cast hK_dim) hbessel_nn))

private theorem div_three_pow_le_factorial (m : ℕ) :
    ((m : ℝ) / 3) ^ m ≤ (m.factorial : ℝ) := by
  have hsum := Real.sum_le_exp_of_nonneg (Nat.cast_nonneg m) (m + 1)
  have hterm : (m : ℝ) ^ m / (m.factorial : ℝ) ≤
      ∑ i ∈ Finset.range (m + 1), (m : ℝ) ^ i / (i.factorial : ℝ) :=
    Finset.single_le_sum (f := fun i : ℕ => (m : ℝ) ^ i / (i.factorial : ℝ))
      (fun i _ => div_nonneg (pow_nonneg (Nat.cast_nonneg m) i) (Nat.cast_nonneg _))
      (Finset.mem_range.mpr (Nat.lt_succ_self m))
  have hexp_le : Real.exp (m : ℝ) ≤ (3 : ℝ) ^ m := by
    rw [show (m : ℝ) = (m : ℝ) * 1 by ring, Real.exp_nat_mul]
    exact pow_le_pow_left₀ (Real.exp_nonneg 1) (Real.exp_one_lt_d9.le.trans (by norm_num)) m
  have hle : (m : ℝ) ^ m / (m.factorial : ℝ) ≤ (3 : ℝ) ^ m := (hterm.trans hsum).trans hexp_le
  have hfac_pos : (0 : ℝ) < m.factorial := Nat.cast_pos.mpr (Nat.factorial_pos m)
  rw [div_pow, div_le_iff₀ (by positivity)]
  calc (m : ℝ) ^ m = ((m : ℝ) ^ m / (m.factorial : ℝ)) * (m.factorial : ℝ) :=
        (div_mul_cancel₀ _ hfac_pos.ne').symm
    _ ≤ (3 : ℝ) ^ m * (m.factorial : ℝ) := mul_le_mul_of_nonneg_right hle hfac_pos.le
    _ = (m.factorial : ℝ) * (3 : ℝ) ^ m := mul_comm _ _

private theorem quad_bernoulli_nonneg {x : ℝ} (hx : 0 ≤ x) (r : ℕ) :
    (r : ℝ) * ((r : ℝ) - 1) / 2 * x ^ 2 ≤ (1 + x) ^ r := by
  induction r with
  | zero => simp
  | succ r ih =>
      have h1 : 1 + (r : ℝ) * x ≤ (1 + x) ^ r :=
        one_add_mul_le_pow (by linarith only [hx]) r
      have hrhs : (1 + x) ^ (r + 1) = (1 + x) ^ r + x * (1 + x) ^ r := by ring
      have hmul : x * (1 + (r : ℝ) * x) ≤ x * (1 + x) ^ r :=
        mul_le_mul_of_nonneg_left h1 hx
      have hstep : (((r + 1 : ℕ) : ℝ) * (((r + 1 : ℕ) : ℝ) - 1) / 2) * x ^ 2 =
          ((r : ℝ) * ((r : ℝ) - 1) / 2) * x ^ 2 + x * ((r : ℝ) * x) := by
        push_cast; ring
      rw [hrhs, hstep]
      nlinarith only [ih, hmul, hx]

/-- Universal all-`r` Krylov causal barrier at the canonical near-Hilbert budget
`P = nearHilbertContinuousCircuitBudget N`: for any fixed exponential rate `C_exp > 0`,
eventually in `N`, no Hamiltonian `H` with `‖H‖ ≤ C_exp * N`, no horizon `T ∈ [0, 2^(C_exp * N)]`,
no sample count `M ≥ 1`, no dates `t : Fin M → [0, T]`, and no replica order `r ≥ 1` can satisfy
the replica-Gram exclusion inequality
`((N * N)^P * (r * P + 1)^(16 P)) * empiricalReplicaBessel H r t < (199 / 200)^(2 r)`. -/
theorem no_exponential_replicaGram_exclusion_at_nearHilbert {C_exp : ℝ} (hC : 0 < C_exp) :
    ∀ᶠ N : ℕ in atTop,
      let P := nearHilbertContinuousCircuitBudget N
      ∀ (H : selfAdjoint (Register N)) (T : ℝ) (M r : ℕ) (t : Fin M → ℝ),
        ‖H.val‖ ≤ C_exp * (N : ℝ) →
        T ∈ Icc (0 : ℝ) ((2 : ℝ) ^ (C_exp * (N : ℝ))) →
        1 ≤ M → 1 ≤ r →
        (∀ a : Fin M, t a ∈ Icc 0 T) →
        ¬ ((((N * N) ^ P * (r * P + 1) ^ (P * 16) : ℕ) : ℝ) *
            empiricalReplicaBessel H r t < (199 / 200 : ℝ) ^ (2 * r)) := by
  -- P = 2^N / (64 * (N + 1)) eventually exceeds (C_exp + 3) * N + 20
  have hlim1 : Tendsto (fun N : ℕ =>
      (64 * ((N : ℝ) + 1) * ((C_exp + 3) * (N : ℝ) + 21)) / (2 : ℝ) ^ N) atTop (𝓝 0) := by
    have h2 := tendsto_pow_const_div_const_pow_of_one_lt 2 (by norm_num : (1 : ℝ) < 2)
    have h1 := tendsto_pow_const_div_const_pow_of_one_lt 1 (by norm_num : (1 : ℝ) < 2)
    have h0 := tendsto_pow_const_div_const_pow_of_one_lt 0 (by norm_num : (1 : ℝ) < 2)
    have hcomb := ((h2.const_mul (64 * (C_exp + 3))).add
      (h1.const_mul (64 * (C_exp + 3 + 21)))).add (h0.const_mul (64 * 21))
    simp only [mul_zero, add_zero] at hcomb
    refine hcomb.congr fun N => ?_
    rw [pow_one, pow_zero]
    ring
  have hlim2 : Tendsto (fun N : ℕ =>
      (40000 * (24 * C_exp * (N : ℝ) + 4)) / (2 : ℝ) ^ (2 * N)) atTop (𝓝 0) := by
    have h1 := (tendsto_pow_const_div_const_pow_of_one_lt 1 (by norm_num : (1 : ℝ) < 4)).const_mul
      (40000 * 24 * C_exp)
    have h0 := (tendsto_pow_const_div_const_pow_of_one_lt 0 (by norm_num : (1 : ℝ) < 4)).const_mul
      (40000 * 4)
    have hcomb := h1.add h0
    simp only [mul_zero, add_zero] at hcomb
    refine hcomb.congr fun N => ?_
    have h4 : (4 : ℝ) ^ N = (2 : ℝ) ^ (2 * N) := by
      rw [pow_mul]; norm_num
    rw [pow_one, pow_zero, h4]
    ring
  filter_upwards [hlim1.eventually_lt_const zero_lt_one,
    hlim2.eventually_lt_const zero_lt_one,
    eventually_ge_atTop 4] with N hP_dom hpoly_dom hN4
  intro P H T M r t hH_le hT_mem hM hr ht_mem hcontra
  have hP_ge : (C_exp + 3) * (N : ℝ) + 20 ≤ (P : ℝ) := by
    have hmul_lt := (div_lt_iff₀ (pow_pos two_pos N)).mp hP_dom
    rw [one_mul] at hmul_lt
    have hdiv : ((P : ℝ) + 1) * (64 * ((N : ℝ) + 1)) > (2 : ℝ) ^ N := by
      have hnat : 2 ^ N < (64 * (N + 1)) * (P + 1) :=
        Nat.lt_mul_div_succ (2 ^ N) (by positivity)
      have hreal : (2 : ℝ) ^ N < (64 * ((N : ℝ) + 1)) * ((P : ℝ) + 1) := by exact_mod_cast hnat
      linarith only [hreal]
    have hden_pos : (0 : ℝ) < 64 * ((N : ℝ) + 1) := by positivity
    have hlt_P1 : (C_exp + 3) * (N : ℝ) + 21 < (P : ℝ) + 1 := by
      nlinarith only [hmul_lt, hdiv, hden_pos]
    linarith only [hlt_P1]
  have hP_pos : 2 ≤ P := by
    have h20 : (20 : ℝ) ≤ (P : ℝ) := by nlinarith only [hP_ge, hC]
    exact_mod_cast (show (2 : ℝ) ≤ (P : ℝ) by linarith only [h20])
  -- Choose K = ⌊6 * r * ‖H‖ * T⌋₊ so η_K ≤ 1/2
  let X : ℝ := (r : ℝ) * ‖H.val‖ * T
  have hX_nn : 0 ≤ X := mul_nonneg (mul_nonneg (Nat.cast_nonneg r) (norm_nonneg _)) hT_mem.1
  let K : ℕ := ⌊6 * X⌋₊
  have hX_le : X ≤ ((K + 1 : ℕ) : ℝ) / 6 := by
    have hlt : 6 * X < (K : ℝ) + 1 := Nat.lt_floor_add_one (6 * X)
    push_cast
    linarith only [hlt]
  have hη_half : X ^ (K + 1) / ((K + 1).factorial : ℝ) ≤ 1 / 2 := by
    have hpow : X ^ (K + 1) ≤ (((K + 1 : ℕ) : ℝ) / 6) ^ (K + 1) :=
      pow_le_pow_left₀ hX_nn hX_le (K + 1)
    have hsplit : (((K + 1 : ℕ) : ℝ) / 6) ^ (K + 1) =
        (1 / 2 : ℝ) ^ (K + 1) * (((K + 1 : ℕ) / 3 : ℝ) ^ (K + 1)) := by
      rw [← mul_pow]
      congr 1; ring
    have hhalf_pow : (1 / 2 : ℝ) ^ (K + 1) ≤ 1 / 2 := by
      simpa only [pow_one] using pow_le_pow_of_le_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
        (by norm_num) (Nat.succ_pos K)
    have hfac := div_three_pow_le_factorial (K + 1)
    have hnum_le : X ^ (K + 1) ≤ (1 / 2 : ℝ) * ((K + 1).factorial : ℝ) := calc
      X ^ (K + 1) ≤ (((K + 1 : ℕ) : ℝ) / 6) ^ (K + 1) := hpow
      _ = (1 / 2 : ℝ) ^ (K + 1) * (((K + 1 : ℕ) : ℝ) / 3) ^ (K + 1) := hsplit
      _ ≤ (1 / 2 : ℝ) * ((K + 1).factorial : ℝ) :=
          mul_le_mul hhalf_pow hfac (by positivity) (by norm_num)
    have hfac_pos : (0 : ℝ) < (K + 1).factorial := Nat.cast_pos.mpr (Nat.factorial_pos _)
    exact (div_le_iff₀ hfac_pos).mpr hnum_le
  have ht_abs (a : Fin M) : |t a| ≤ T := by
    rw [abs_of_nonneg (ht_mem a).1]; exact (ht_mem a).2
  have hkry := krylov_empiricalBessel_lower_bound (K := K) H hM hT_mem.1 t ht_abs
    (hη_half.trans (by norm_num))
  have h14 : (1 / 4 : ℝ) ≤ (1 - X ^ (K + 1) / ((K + 1).factorial : ℝ)) ^ 2 := by
    nlinarith only [hη_half]
  have hbessel_ge : (1 / 4 : ℝ) ≤ ((K + 1 : ℕ) : ℝ) * empiricalReplicaBessel H r t :=
    h14.trans hkry
  have hK1_le : ((K + 1 : ℕ) : ℝ) ≤ (r : ℝ) * ((6 * C_exp * (N : ℝ)) * (2 : ℝ) ^ (C_exp * (N : ℝ)) + 1) := by
    have hfl : (K : ℝ) ≤ 6 * X := Nat.floor_le (by linarith only [hX_nn])
    have hX_up : X ≤ (r : ℝ) * (C_exp * (N : ℝ)) * (2 : ℝ) ^ (C_exp * (N : ℝ)) := by
      dsimp only [X]
      exact mul_le_mul (mul_le_mul_of_nonneg_left hH_le (Nat.cast_nonneg r)) hT_mem.2
        hT_mem.1 (by positivity)
    have hr1 : (1 : ℝ) ≤ r := by exact_mod_cast hr
    push_cast
    nlinarith only [hfl, hX_up, hr1]
  -- Combine with hcontra
  let D_hilb : ℝ := (((N * N) ^ P * (r * P + 1) ^ (P * 16) : ℕ) : ℝ)
  have hD_pos : 0 < D_hilb := by
    dsimp only [D_hilb]
    exact_mod_cast Nat.mul_pos (pow_pos (Nat.mul_pos (by omega) (by omega)) P)
      (pow_pos (Nat.succ_pos _) _)
  have hprod_lt : D_hilb * (200 / 199 : ℝ) ^ (2 * r) <
      4 * ((K + 1 : ℕ) : ℝ) := by
    have h1 := mul_lt_mul_of_pos_left hcontra (mul_pos (by norm_num : (0 : ℝ) < 4)
      (by exact_mod_cast Nat.succ_pos K : (0 : ℝ) < (K + 1 : ℕ)))
    have h2 : 4 * ((K + 1 : ℕ) : ℝ) * (D_hilb * empiricalReplicaBessel H r t) =
        D_hilb * (4 * (((K + 1 : ℕ) : ℝ) * empiricalReplicaBessel H r t)) := by ring
    rw [h2] at h1
    have h3 : D_hilb * 1 ≤ D_hilb * (4 * (((K + 1 : ℕ) : ℝ) * empiricalReplicaBessel H r t)) :=
      mul_le_mul_of_nonneg_left (by linarith only [hbessel_ge]) hD_pos.le
    have h4 : D_hilb < 4 * ((K + 1 : ℕ) : ℝ) * (199 / 200 : ℝ) ^ (2 * r) :=
      (by linarith only [h3, h1])
    have h5 := mul_lt_mul_of_pos_right h4 (pow_pos (by norm_num : (0 : ℝ) < 200 / 199) (2 * r))
    have hcanc : (199 / 200 : ℝ) ^ (2 * r) * (200 / 199 : ℝ) ^ (2 * r) = 1 := by
      rw [← mul_pow]; norm_num
    simpa only [mul_assoc, hcanc, mul_one] using h5
  have hpoly_bound : 40000 * (24 * C_exp * (N : ℝ) + 4) < (2 : ℝ) ^ (2 * N) := by
    have h := (div_lt_iff₀ (pow_pos two_pos (2 * N))).mp hpoly_dom
    linarith only [h]
  have hRHS_factor : 4 * ((6 * C_exp * (N : ℝ)) * (2 : ℝ) ^ (C_exp * (N : ℝ)) + 1) ≤
      (24 * C_exp * (N : ℝ) + 4) * (2 : ℝ) ^ (C_exp * (N : ℝ)) := by
    have h1_le : (1 : ℝ) ≤ (2 : ℝ) ^ (C_exp * (N : ℝ)) :=
      Real.one_le_rpow (by norm_num) (mul_nonneg hC.le (Nat.cast_nonneg N))
    nlinarith only [h1_le]
  have hcap_lt_powP : 40000 * ((24 * C_exp * (N : ℝ) + 4) * (2 : ℝ) ^ (C_exp * (N : ℝ))) <
      (2 : ℝ) ^ P := by
    calc 40000 * ((24 * C_exp * (N : ℝ) + 4) * (2 : ℝ) ^ (C_exp * (N : ℝ)))
        = (40000 * (24 * C_exp * (N : ℝ) + 4)) * (2 : ℝ) ^ (C_exp * (N : ℝ)) := by ring
      _ < (2 : ℝ) ^ (2 * N) * (2 : ℝ) ^ (C_exp * (N : ℝ)) :=
          mul_lt_mul_of_pos_right hpoly_bound (Real.rpow_pos_of_pos two_pos _)
      _ = (2 : ℝ) ^ ((C_exp + 2) * (N : ℝ)) := by
          rw [← Real.rpow_natCast 2 (2 * N), ← Real.rpow_add two_pos]
          congr 1; push_cast; ring
      _ ≤ (2 : ℝ) ^ (P : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith only [hP_ge])
      _ = (2 : ℝ) ^ P := Real.rpow_natCast 2 P
  by_cases hr_small : r ≤ 2 ^ P
  · -- Small-r regime: D_hilb ≥ 2^(16 P) > 4 (K + 1)
    have hD_ge : (2 : ℝ) ^ (16 * P) ≤ D_hilb * (200 / 199 : ℝ) ^ (2 * r) := by
      have h1 : 2 ^ (P * 16) ≤ (N * N) ^ P * (r * P + 1) ^ (P * 16) := by
        have hNN : 1 ≤ (N * N) ^ P := one_le_pow₀ (Nat.mul_pos (by omega) (by omega))
        have hrP : 2 ≤ r * P + 1 := by
          have : 1 ≤ r * P := Nat.mul_pos hr (by omega)
          omega
        exact (Nat.pow_le_pow_left hrP (P * 16)).trans (Nat.le_mul_of_pos_left _ hNN)
      have h1_real : (2 : ℝ) ^ (16 * P) ≤ D_hilb := by
        dsimp only [D_hilb]
        rw [Nat.mul_comm 16 P]
        exact_mod_cast h1
      have hpow_ge1 : (1 : ℝ) ≤ (200 / 199 : ℝ) ^ (2 * r) := one_le_pow₀ (by norm_num)
      exact h1_real.trans (le_mul_of_one_le_right hD_pos.le hpow_ge1)
    have hRHS_le : 4 * ((K + 1 : ℕ) : ℝ) ≤ (2 : ℝ) ^ (2 * P) := by
      have hr_real : (r : ℝ) ≤ (2 : ℝ) ^ P := by exact_mod_cast hr_small
      have hfac_nn : 0 ≤ (24 * C_exp * (N : ℝ) + 4) * (2 : ℝ) ^ (C_exp * (N : ℝ)) :=
        mul_nonneg (by positivity) (Real.rpow_nonneg two_pos.le _)
      have hfac_le_powP : (24 * C_exp * (N : ℝ) + 4) * (2 : ℝ) ^ (C_exp * (N : ℝ)) ≤ (2 : ℝ) ^ P :=
        by linarith only [hcap_lt_powP, hfac_nn]
      calc 4 * ((K + 1 : ℕ) : ℝ)
          ≤ (r : ℝ) * (4 * ((6 * C_exp * (N : ℝ)) * (2 : ℝ) ^ (C_exp * (N : ℝ)) + 1)) := by
            linarith only [hK1_le]
        _ ≤ (2 : ℝ) ^ P * ((24 * C_exp * (N : ℝ) + 4) * (2 : ℝ) ^ (C_exp * (N : ℝ))) :=
            mul_le_mul hr_real hRHS_factor (by positivity) (pow_nonneg two_pos.le P)
        _ ≤ (2 : ℝ) ^ P * (2 : ℝ) ^ P :=
            mul_le_mul_of_nonneg_left hfac_le_powP (pow_nonneg two_pos.le P)
        _ = (2 : ℝ) ^ (2 * P) := by rw [two_mul, pow_add]
    have hpow_gt : (2 : ℝ) ^ (2 * P) < (2 : ℝ) ^ (16 * P) :=
      pow_lt_pow_right₀ (by norm_num) (by omega)
    linarith only [hD_ge, hprod_lt, hRHS_le, hpow_gt]
  · -- Large-r regime: r > 2^P ≥ 4, quadratic Bernoulli beats linear K + 1 growth
    push Not at hr_small
    have hr_ge4 : 4 ≤ r :=
      (show 4 ≤ 2 ^ P from le_trans (by norm_num : 4 ≤ 2 ^ 2)
        (Nat.pow_le_pow_right (by decide) hP_pos)).trans hr_small.le
    have hD_ge1 : (1 : ℝ) ≤ D_hilb := by
      dsimp only [D_hilb]
      exact_mod_cast (Nat.mul_pos (pow_pos (Nat.mul_pos (by omega) (by omega)) P)
        (pow_pos (Nat.succ_pos _) _))
    have hbern := quad_bernoulli_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 100) r
    have hbase : (1 + 1 / 100 : ℝ) ^ r ≤ (200 / 199 : ℝ) ^ (2 * r) := by
      rw [pow_mul]
      exact pow_le_pow_left₀ (by norm_num) (by norm_num) r
    have hr_sub : (r : ℝ) / 2 ≤ (r : ℝ) - 1 := by
      have : (4 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr_ge4
      linarith only [this]
    have hquad_r : (r : ℝ) * ((2 : ℝ) ^ P / 40000) < (200 / 199 : ℝ) ^ (2 * r) := by
      have hr_gt_pow : (2 : ℝ) ^ P < (r : ℝ) := by exact_mod_cast hr_small
      have hr_pos : (0 : ℝ) < r := by exact_mod_cast (by omega : 0 < r)
      calc (r : ℝ) * ((2 : ℝ) ^ P / 40000)
          < (r : ℝ) * ((r : ℝ) / 40000) :=
            mul_lt_mul_of_pos_left (div_lt_div_of_pos_right hr_gt_pow (by norm_num)) hr_pos
        _ ≤ (r : ℝ) * ((r : ℝ) - 1) / 2 * (1 / 100 : ℝ) ^ 2 := by nlinarith only [hr_sub, hr_pos]
        _ ≤ (1 + 1 / 100 : ℝ) ^ r := hbern
        _ ≤ (200 / 199 : ℝ) ^ (2 * r) := hbase
    have hLHS_gt : (r : ℝ) * ((2 : ℝ) ^ P / 40000) < D_hilb * (200 / 199 : ℝ) ^ (2 * r) :=
      hquad_r.trans_le (le_mul_of_one_le_left (by positivity) hD_ge1)
    have hr_pos : (0 : ℝ) < r := by exact_mod_cast (by omega : 0 < r)
    have hRHS_lt : 4 * ((K + 1 : ℕ) : ℝ) < (r : ℝ) * ((2 : ℝ) ^ P / 40000) := by
      calc 4 * ((K + 1 : ℕ) : ℝ)
          ≤ (r : ℝ) * (4 * ((6 * C_exp * (N : ℝ)) * (2 : ℝ) ^ (C_exp * (N : ℝ)) + 1)) := by
            linarith only [hK1_le]
        _ ≤ (r : ℝ) * ((24 * C_exp * (N : ℝ) + 4) * (2 : ℝ) ^ (C_exp * (N : ℝ))) :=
            mul_le_mul_of_nonneg_left hRHS_factor hr_pos.le
        _ < (r : ℝ) * ((2 : ℝ) ^ P / 40000) :=
            mul_lt_mul_of_pos_left (by linarith only [hcap_lt_powP]) hr_pos
    linarith only [hLHS_gt, hprod_lt, hRHS_lt]

/-! ## Section 5: Two-cut weak-bond survival floor and infinite 18th moment -/

private theorem measurable_first_strict_time {X : Type*} [TopologicalSpace X]
    [MeasurableSpace X] [OpensMeasurableSpace X] (f : X × ℝ → ℝ) (hf : Continuous f) (ε : ℝ) :
    Measurable fun x : X => sInf {t : ℝ | 0 ≤ t ∧ ε < f (x, t)} := by
  refine measurable_of_Iio fun b => ?_
  by_cases hb : b ≤ 0
  · convert MeasurableSet.empty
    ext x
    simp only [mem_preimage, mem_Iio, mem_empty_iff_false, iff_false, not_lt]
    set E := {t : ℝ | 0 ≤ t ∧ ε < f (x, t)}
    by_cases hE : E.Nonempty
    · exact hb.trans (le_csInf hE fun _ ht => ht.1)
    · have hempty : E = ∅ := not_nonempty_iff_eq_empty.mp hE
      rw [hempty, Real.sInf_empty]
      exact hb
  · push Not at hb
    have hsec_x (q : ℝ) : Measurable fun x : X => f (x, q) :=
      (hf.comp (continuous_id.prodMk continuous_const)).measurable
    let hitQ : Set X :=
      ⋃ (q : ℚ) (_ : (0 : ℝ) ≤ (q : ℝ) ∧ (q : ℝ) < b), {x | ε < f (x, (q : ℝ))}
    let emptyQ : Set X :=
      ⋂ (q : ℚ) (_ : (0 : ℝ) ≤ (q : ℝ)), {x | f (x, (q : ℝ)) ≤ ε}
    have hhit_meas : MeasurableSet hitQ :=
      MeasurableSet.iUnion fun q => MeasurableSet.iUnion fun _ =>
        measurableSet_lt measurable_const (hsec_x (q : ℝ))
    have hempty_meas : MeasurableSet emptyQ :=
      MeasurableSet.iInter fun q => MeasurableSet.iInter fun _ =>
        measurableSet_le (hsec_x (q : ℝ)) measurable_const
    have heq : (fun x : X => sInf {t : ℝ | 0 ≤ t ∧ ε < f (x, t)}) ⁻¹' Iio b =
        hitQ ∪ emptyQ := by
      ext x
      simp only [mem_preimage, mem_Iio]
      set E := {t : ℝ | 0 ≤ t ∧ ε < f (x, t)}
      have hcont_t : Continuous (fun t : ℝ => f (x, t)) :=
        hf.comp (continuous_const.prodMk continuous_id)
      by_cases hE : E.Nonempty
      · have hnot_emptyQ : x ∉ emptyQ := by
          intro hall
          obtain ⟨t₀, ht₀0, ht₀_gt⟩ := hE
          obtain ⟨δ, hδ, hnear⟩ := Metric.eventually_nhds_iff.mp
            (hcont_t.neg.continuousAt.eventually_lt_const (neg_lt_neg ht₀_gt))
          obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn (lt_add_of_pos_right t₀ hδ)
          have hq0 : (0 : ℝ) ≤ (q : ℝ) := ht₀0.trans hq1.le
          have hd : dist (q : ℝ) t₀ < δ := by
            rw [Real.dist_eq, abs_of_pos (sub_pos.mpr hq1)]
            linarith only [hq2]
          have hgt_q : ε < f (x, (q : ℝ)) := neg_lt_neg_iff.mp (hnear hd)
          exact hgt_q.not_ge ((mem_iInter₂.mp hall) q hq0)
        constructor
        · intro hlt
          left
          obtain ⟨t₁, ⟨ht₁0, ht₁_gt⟩, ht₁_lt⟩ := exists_lt_of_csInf_lt hE hlt
          obtain ⟨δ, hδ, hnear⟩ := Metric.eventually_nhds_iff.mp
            (hcont_t.neg.continuousAt.eventually_lt_const (neg_lt_neg ht₁_gt))
          have hm : t₁ < min b (t₁ + δ) := lt_min ht₁_lt (lt_add_of_pos_right t₁ hδ)
          obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn hm
          have hq0 : (0 : ℝ) ≤ (q : ℝ) := ht₁0.trans hq1.le
          have hqb : (q : ℝ) < b := hq2.trans_le (min_le_left _ _)
          have hd : dist (q : ℝ) t₁ < δ := by
            rw [Real.dist_eq, abs_of_pos (sub_pos.mpr hq1)]
            have hlt_δ := lt_of_lt_of_le hq2 (min_le_right b (t₁ + δ))
            linarith only [hlt_δ]
          exact mem_iUnion₂.mpr ⟨q, ⟨hq0, hqb⟩, neg_lt_neg_iff.mp (hnear hd)⟩
        · rintro (hhit | hemp)
          · obtain ⟨q, ⟨hq0, hqb⟩, hgt_q⟩ := mem_iUnion₂.mp hhit
            exact (csInf_le (s := E) ⟨0, fun _ ht => ht.1⟩
              (show (q : ℝ) ∈ E from ⟨hq0, hgt_q⟩)).trans_lt hqb
          · exact (hnot_emptyQ hemp).elim
      · have hempty : E = ∅ := not_nonempty_iff_eq_empty.mp hE
        have hin_emptyQ : x ∈ emptyQ :=
          mem_iInter₂.mpr fun q hq0 => le_of_not_gt fun hgt =>
            hE ⟨(q : ℝ), show (q : ℝ) ∈ E from ⟨hq0, hgt⟩⟩
        rw [hempty, Real.sInf_empty]
        exact ⟨fun _ => Or.inr hin_emptyQ, fun _ => hb⟩
    rw [heq]
    exact hhit_meas.union hempty_meas

/-- `tenthPlateauOnset (prefixGenerator n x) s` is Borel measurable in the Gaussian disorder
coordinates `x : PrefixIndex n → ℝ`. -/
theorem measurable_tenthPlateauOnset_prefix (n s : ℕ) :
    Measurable fun x : PrefixIndex n → ℝ => tenthPlateauOnset (prefixGenerator n x) s := by
  have heq : (fun x : PrefixIndex n → ℝ => tenthPlateauOnset (prefixGenerator n x) s) =
      fun x => sInf {t : ℝ | 0 ≤ t ∧ (1 / 10 : ℝ) < pathGateDistance n s x t} := by
    funext x
    unfold tenthPlateauOnset
    congr 1; ext t
    simp only [hasProjectiveCircuitApproximation_iff_infDist, not_le]
    rfl
  rw [heq]
  exact measurable_first_strict_time
    (fun p : (PrefixIndex n → ℝ) × ℝ => pathGateDistance n s p.1 p.2)
    (continuous_distance n s) (1 / 10 : ℝ)

private theorem scalarReturnExcised_of_single_onsite {k : ℕ} (u : PathShell (k + 1))
    (honsite : 3 ≤ |u (.inl (0, 0))|) :
    ∃ t₀ ∈ Ioo (0 : ℝ) (Real.pi / 2),
      ∀ z : ℂ, ‖z‖ = 1 →
        Real.sqrt 2 ≤ ‖unitaryEvolution (pathHamiltonian u) t₀ - z • (1 : Register (k + 3))‖ := by
  let H : selfAdjoint (Register (k + 3)) := ⟨pathHamiltonian u, isSelfAdjoint_pathHamiltonian u⟩
  -- 1. 3 ≤ ‖H.val‖ via product-stabilizer onsite sum
  have hH_ge3 : (3 : ℝ) ≤ ‖H.val‖ := by
    have hdist := signed_onsite_sum_le_pathHamiltonian_dist u 0 (fun _ => 0)
    have hz0 : pathHamiltonian (0 : PathShell (k + 1)) = 0 := (pathHamiltonianLM (k + 1)).map_zero
    rw [hz0, sub_zero] at hdist
    have hsingle : |u (.inl (0, 0)) - (0 : PathShell (k + 1)) (.inl (0, 0))| ≤
        ∑ s : Fin (k + 3), |u (.inl (s, 0)) - (0 : PathShell (k + 1)) (.inl (s, 0))| :=
      Finset.single_le_sum (fun _ _ => abs_nonneg _) (Finset.mem_univ 0)
    have hval : |u (.inl (0, 0)) - (0 : PathShell (k + 1)) (.inl (0, 0))| = |u (.inl (0, 0))| := by
      simp
    exact (honsite.trans_eq hval.symm).trans (hsingle.trans hdist)
  -- 2. Tr(H) = 0
  have htr0 : Matrix.trace H.val = 0 := by
    let x : PrefixIndex (k + 1) → ℝ := fun i => u (pathCoeffEquiv (k + 1) i)
    have hgen : H.val = numberedGenerator (k + 1) x := (numberedGenerator_shell u).symm
    rw [hgen]
    unfold numberedGenerator
    rw [Matrix.trace_sum]
    refine Finset.sum_eq_zero fun l _ => ?_
    rw [Matrix.trace_smul]
    have hne_id : pathWord l ≠ fun _ => none := by
      intro hid
      rcases l with ⟨s, p⟩ | ⟨e, pq⟩
      · have hs := congrFun hid s
        simp [pathWord, onsiteWord] at hs
      · have he := congrFun hid e.castSucc
        simp [pathWord, couplingWord] at he
    rw [finitePauliMatrix_trace_eq_zero_of_ne_identity _ hne_id, smul_zero]
  -- 3. Eigenvalue spread E_max - E_min ≥ 3
  let V := hermitianEigenbasisUnitary H.2.isHermitian
  let E := H.2.isHermitian.eigenvalues
  have hspec : H.val = V.val * Matrix.diagonal (Complex.ofReal ∘ E) * star V.val :=
    H.2.isHermitian.spectral_theorem
  have hsum_E : (∑ c : Config (k + 3), E c) = 0 := by
    have htr_spec : Matrix.trace H.val = ∑ c : Config (k + 3), (E c : ℂ) := by
      rw [hspec, Matrix.trace_mul_comm, ← mul_assoc, (Unitary.mem_iff.mp V.2).1, one_mul,
        Matrix.trace]
      simp [Matrix.diagonal]
    rw [htr0] at htr_spec
    exact Complex.ofReal_injective (by simpa [Complex.ofReal_sum] using htr_spec.symm)
  let c₀ : Config (k + 3) := fun _ => false
  have huniv_ne : (Finset.univ : Finset (Config (k + 3))).Nonempty := ⟨c₀, Finset.mem_univ c₀⟩
  obtain ⟨c_max, _, hc_max⟩ := Finset.exists_max_image Finset.univ E huniv_ne
  obtain ⟨c_min, _, hc_min⟩ := Finset.exists_min_image Finset.univ E huniv_ne
  obtain ⟨c_abs, _, hc_abs⟩ := Finset.exists_max_image Finset.univ (fun c => |E c|) huniv_ne
  have hE_max_nn : 0 ≤ E c_max := by
    by_contra hlt; push Not at hlt
    have hsum_neg : (∑ c : Config (k + 3), E c) < 0 :=
      Finset.sum_neg (fun c _ => (hc_max c (Finset.mem_univ c)).trans_lt hlt) huniv_ne
    linarith only [hsum_E, hsum_neg]
  have hE_min_np : E c_min ≤ 0 := by
    by_contra hgt; push Not at hgt
    have hsum_pos : 0 < ∑ c : Config (k + 3), E c :=
      Finset.sum_pos (fun c _ => hgt.trans_le (hc_min c (Finset.mem_univ c))) huniv_ne
    linarith only [hsum_E, hsum_pos]
  have hH_le_abs : ‖H.val‖ ≤ |E c_abs| := by
    have hiso := l2_opNorm_unitary_conj_eq (Unitary.star_mem V.2) H.val
    have hconj : star V.val * H.val * V.val = Matrix.diagonal (Complex.ofReal ∘ E) := by
      rw [hspec]; exact star_conj_cancel V.2 _
    rw [star_star, hconj] at hiso
    rw [← hiso, ← Matrix.l2_opNorm_toEuclideanCLM]
    refine (Matrix.toEuclideanCLM (n := Config (k + 3)) (𝕜 := ℂ)
      (Matrix.diagonal (Complex.ofReal ∘ E))).opNorm_le_bound (abs_nonneg _) fun ψ => ?_
    have hsq : ‖Matrix.toEuclideanCLM (n := Config (k + 3)) (𝕜 := ℂ)
        (Matrix.diagonal (Complex.ofReal ∘ E)) ψ‖ ^ 2 ≤ (|E c_abs| * ‖ψ‖) ^ 2 := by
      rw [EuclideanSpace.norm_sq_eq, mul_pow, EuclideanSpace.norm_sq_eq, Finset.mul_sum]
      refine Finset.sum_le_sum fun c _ => ?_
      have hcoord : (Matrix.toEuclideanCLM (n := Config (k + 3)) (𝕜 := ℂ)
          (Matrix.diagonal (Complex.ofReal ∘ E)) ψ).ofLp c = (E c : ℂ) * ψ.ofLp c := by
        rw [Matrix.ofLp_toEuclideanCLM, Matrix.mulVec_diagonal]
        rfl
      change ‖(Matrix.toEuclideanCLM (n := Config (k + 3)) (𝕜 := ℂ)
        (Matrix.diagonal (Complex.ofReal ∘ E)) ψ).ofLp c‖ ^ 2 ≤ _
      rw [hcoord, norm_mul, mul_pow, Complex.norm_real, Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_right
        (pow_le_pow_left₀ (abs_nonneg _) (hc_abs c (Finset.mem_univ c)) 2) (sq_nonneg _)
    exact (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (abs_nonneg _) (norm_nonneg _))).mp hsq
  have hgap_ge3 : 3 ≤ E c_max - E c_min := by
    have h3_abs : 3 ≤ |E c_abs| := hH_ge3.trans hH_le_abs
    rcases le_or_gt 0 (E c_abs) with hnn | hneg
    · rw [abs_of_nonneg hnn] at h3_abs
      have hle := hc_max c_abs (Finset.mem_univ c_abs)
      linarith only [h3_abs, hle, hE_min_np]
    · rw [abs_of_neg hneg] at h3_abs
      have hge := hc_min c_abs (Finset.mem_univ c_abs)
      linarith only [h3_abs, hge, hE_max_nn]
  -- 4. Antipodal phase pair at t₀ = π / (E c_max - E c_min) ∈ (0, π / 2)
  let ΔE := E c_max - E c_min
  have hΔE_pos : 0 < ΔE := by linarith only [hgap_ge3]
  let t₀ := Real.pi / ΔE
  have ht₀_pos : 0 < t₀ := div_pos Real.pi_pos hΔE_pos
  have ht₀_lt : t₀ < Real.pi / 2 := by
    dsimp only [t₀]
    exact div_lt_div_of_pos_left Real.pi_pos two_pos (by linarith only [hgap_ge3])
  refine ⟨t₀, ⟨ht₀_pos, ht₀_lt⟩, fun z hz => ?_⟩
  let D_t₀ := Matrix.diagonal fun i => Complex.exp (-(Complex.I * (t₀ * E i)))
  have hconj_t₀ : star V.val * (unitaryEvolution H.val t₀ - z • (1 : Register (k + 3))) * V.val =
      D_t₀ - z • (1 : Register (k + 3)) := by
    rw [unitaryEvolution_spectral H.2.isHermitian t₀]
    change star V.val * (V.val * D_t₀ * star V.val - z • 1) * V.val = _
    rw [Matrix.mul_sub, Matrix.sub_mul, star_conj_cancel V.2, Matrix.mul_smul, Matrix.smul_mul,
      Matrix.mul_one, (Unitary.mem_iff.mp V.2).1]
  have hiso := l2_opNorm_unitary_conj_eq (Unitary.star_mem V.2)
    (unitaryEvolution H.val t₀ - z • (1 : Register (k + 3)))
  rw [star_star, hconj_t₀] at hiso
  rw [← hiso]
  let w₁ : ℂ := Complex.exp (-(Complex.I * (t₀ * E c_max)))
  let w₂ : ℂ := Complex.exp (-(Complex.I * (t₀ * E c_min)))
  have hw₁_norm : ‖w₁‖ = 1 := by
    dsimp only [w₁]
    rw [Complex.norm_exp]
    have hre : (-(Complex.I * (↑t₀ * ↑(E c_max)))).re = 0 := by simp
    rw [hre, Real.exp_zero]
  have hw₂_eq : w₂ = -w₁ := by
    dsimp only [w₁, w₂]
    have harg : -(Complex.I * (↑t₀ * ↑(E c_min))) =
        -(Complex.I * (↑t₀ * ↑(E c_max))) + ↑Real.pi * Complex.I := by
      have htΔ : t₀ * ΔE = Real.pi := div_mul_cancel₀ Real.pi hΔE_pos.ne'
      have hcast : (t₀ : ℂ) * ((E c_max : ℂ) - (E c_min : ℂ)) = (Real.pi : ℂ) := by
        exact_mod_cast htΔ
      linear_combination Complex.I * hcast
    rw [harg, Complex.exp_add, Complex.exp_pi_mul_I, mul_neg, mul_one]
  have he₁ := norm_entry_le_l2_opNorm (D_t₀ - z • (1 : Register (k + 3))) c_max c_max
  have he₂ := norm_entry_le_l2_opNorm (D_t₀ - z • (1 : Register (k + 3))) c_min c_min
  simp only [D_t₀, Matrix.sub_apply, Matrix.diagonal_apply_eq, Matrix.smul_apply,
    Matrix.one_apply_eq, smul_eq_mul, mul_one] at he₁ he₂
  change ‖w₁ - z‖ ≤ _ at he₁
  change ‖w₂ - z‖ ≤ _ at he₂
  rw [hw₂_eq] at he₂
  have hpar : ‖w₁ - z‖ ^ 2 + ‖-w₁ - z‖ ^ 2 = 4 := by
    have h1 : ‖w₁ - z‖ ^ 2 + ‖-w₁ - z‖ ^ 2 = 2 * (‖w₁‖ ^ 2 + ‖z‖ ^ 2) := by
      simp only [Complex.sq_norm, Complex.normSq_apply, Complex.sub_re, Complex.sub_im,
        Complex.neg_re, Complex.neg_im]
      ring
    rw [h1, hw₁_norm, hz]; norm_num
  have hsq_ge2 : 2 ≤ ‖D_t₀ - z • (1 : Register (k + 3))‖ ^ 2 := by
    have h1 := pow_le_pow_left₀ (norm_nonneg _) he₁ 2
    have h2 := pow_le_pow_left₀ (norm_nonneg _) he₂ 2
    linarith only [hpar, h1, h2]
  exact (Real.sqrt_le_iff.mpr ⟨norm_nonneg _, hsq_ge2⟩)

private def cutAndSingleEvent {ι : Type*} (S : Finset ι) (i₀ : ι) (δ : ℝ) : Set (ι → ℝ) :=
  {x : ι → ℝ | (∀ i ∈ S, |x i| ≤ δ) ∧ 3 ≤ |x i₀|}

private theorem measurableSet_cutAndSingleEvent {ι : Type*}
    (S : Finset ι) (i₀ : ι) (δ : ℝ) :
    MeasurableSet (cutAndSingleEvent S i₀ δ) := by
  have h1 : {x : ι → ℝ | ∀ i ∈ S, |x i| ≤ δ} = ⋂ i ∈ S, {x : ι → ℝ | |x i| ≤ δ} := by
    ext x; simp
  have hm1 : MeasurableSet {x : ι → ℝ | ∀ i ∈ S, |x i| ≤ δ} := by
    rw [h1]
    exact MeasurableSet.biInter S.countable_toSet fun i _ =>
      measurableSet_le (continuous_abs.measurable.comp (measurable_pi_apply i)) measurable_const
  have hm2 : MeasurableSet {x : ι → ℝ | 3 ≤ |x i₀|} :=
    measurableSet_le measurable_const (continuous_abs.measurable.comp (measurable_pi_apply i₀))
  exact hm1.inter hm2

private theorem pi_cutAndSingleEvent_floor {ι : Type*} [Fintype ι] [DecidableEq ι]
    (S : Finset ι) (i₀ : ι) (hi₀ : i₀ ∉ S)
    {δ : ℝ} (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1) :
    (2 * gaussianDensityFloor * δ) ^ S.card *
      (gaussianReal 0 1).real (Icc (3 : ℝ) 4) ≤
      (Measure.pi fun _ : ι => gaussianReal 0 1).real (cutAndSingleEvent S i₀ δ) := by
  let γ := gaussianReal 0 1
  let F_coord : ι → Set ℝ :=
    fun i => if i ∈ S then Icc (-δ) δ else if i = i₀ then Icc (3 : ℝ) 4 else univ
  have hsub_event : Set.univ.pi F_coord ⊆ cutAndSingleEvent S i₀ δ := by
    intro x hx
    refine ⟨fun i hi => ?_, ?_⟩
    · have h := hx i (mem_univ i)
      simp only [F_coord, if_pos hi] at h
      exact abs_le.mpr h
    · have h := hx i₀ (mem_univ i₀)
      simp only [F_coord, if_neg hi₀, if_true] at h
      exact h.1.trans (le_abs_self _)
  have hprod_eq : (Measure.pi fun _ : ι => γ).real (Set.univ.pi F_coord) =
      (∏ i ∈ S, γ.real (F_coord i)) * (∏ i ∈ Sᶜ, γ.real (F_coord i)) := by
    rw [Measure.real_def, Measure.pi_pi, ENNReal.toReal_prod,
      ← Finset.prod_mul_prod_compl S (fun i => (γ (F_coord i)).toReal)]
    rfl
  have hcut_prod : (∏ i ∈ S, γ.real (F_coord i)) = γ.real (Icc (-δ) δ) ^ S.card := by
    have h1 : (∏ i ∈ S, γ.real (F_coord i)) = ∏ _i ∈ S, γ.real (Icc (-δ) δ) :=
      Finset.prod_congr rfl fun i hi => by simp [F_coord, hi]
    rw [h1, Finset.prod_const]
  have hS_sub : ({i₀} : Finset ι) ⊆ Sᶜ := by
    intro i hi
    rw [Finset.mem_singleton.mp hi]
    exact Finset.mem_compl.mpr hi₀
  have hcompl_prod : (∏ i ∈ Sᶜ, γ.real (F_coord i)) = γ.real (Icc (3 : ℝ) 4) := by
    rw [← Finset.prod_sdiff hS_sub]
    have hout : (∏ i ∈ Sᶜ \ {i₀}, γ.real (F_coord i)) = 1 := by
      refine Finset.prod_eq_one fun i hi => ?_
      obtain ⟨hi_not_S, hi_not_0⟩ := Finset.mem_sdiff.mp hi
      rw [Finset.mem_compl] at hi_not_S
      rw [Finset.mem_singleton] at hi_not_0
      simp [F_coord, hi_not_S, hi_not_0]
    have hin : (∏ i ∈ ({i₀} : Finset ι), γ.real (F_coord i)) = γ.real (Icc (3 : ℝ) 4) := by
      rw [Finset.prod_singleton]
      simp [F_coord, hi₀]
    rw [hout, hin, one_mul]
  have hlow_enn := ENNReal.toReal_mono (measure_ne_top γ (Icc (-δ) δ)) (gaussianReal_Icc_lower hδ1)
  rw [ENNReal.toReal_ofReal (mul_nonneg gaussianDensityFloor_pos.le (by linarith only [hδ0])),
    ← Measure.real_def] at hlow_enn
  have h1d : 2 * gaussianDensityFloor * δ ≤ γ.real (Icc (-δ) δ) := by linarith only [hlow_enn]
  have hbase_nn : 0 ≤ 2 * gaussianDensityFloor * δ :=
    mul_nonneg (mul_nonneg two_pos.le gaussianDensityFloor_pos.le) hδ0
  have hbox_le : (2 * gaussianDensityFloor * δ) ^ S.card * γ.real (Icc (3 : ℝ) 4) ≤
      (Measure.pi fun _ : ι => γ).real (Set.univ.pi F_coord) := by
    rw [hprod_eq, hcut_prod, hcompl_prod]
    exact mul_le_mul_of_nonneg_right
      (pow_le_pow_left₀ hbase_nn h1d S.card)
      (by rw [Measure.real_def]; exact ENNReal.toReal_nonneg)
  exact hbox_le.trans
    (ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono hsub_event))

/-- Size-independent two-cut weak-bond survival floor (`c T^{-18}`) on realizations simultaneously
satisfying:
1. maximally projective simple spectrum and full `2^N` arithmetic-progression Vandermonde rank
   inside `[0, 1]`,
2. scalar-return distance `≥ √2` at some `t₀ ∈ (0, π / 2) ⊆ [0, T]`, and
3. `T < tenthPlateauOnset H_N s` for every `s` with `P / 2 ≤ s ≤ P` (including `s = P`). -/
theorem gaussian_two_cut_vandermonde_returnExcised_tail :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ k : ℕ in atTop,
      let N := k + 3
      let P := nearHilbertContinuousCircuitBudget N
      ∀ T : ℝ, 2 ≤ T →
        c ≤ T ^ 18 * pathPauliDisorderLaw.real {ω : PathPauliDisorder |
          let u := pathPauliDisorderShell ω (k + 1)
          let H : selfAdjoint (Register N) := ⟨pathHamiltonian u, isSelfAdjoint_pathHamiltonian u⟩
          MaximallyProjectiveEnergy H.2.isHermitian.eigenvalues ∧
          (∃ τ > 0, (∀ m : Fin (2 ^ N), ((m : ℕ) : ℝ) * τ ∈ Icc (0 : ℝ) 1) ∧
            Module.finrank ℂ (Submodule.span ℂ
              (range fun m : Fin (2 ^ N) => unitaryEvolution H.val (((m : ℕ) : ℝ) * τ))) = 2 ^ N) ∧
          (∃ t₀ ∈ Ioc (0 : ℝ) T, ∀ z : ℂ, ‖z‖ = 1 →
            Real.sqrt 2 ≤ ‖unitaryEvolution H.val t₀ - z • (1 : Register N)‖) ∧
          (∀ s : ℕ, P / 2 ≤ s → s ≤ P → T < tenthPlateauOnset H s)} := by
  let γ := gaussianReal 0 1
  have hp_box : 0 < γ.real (Icc (3 : ℝ) 4) :=
    ENNReal.toReal_pos (gaussianReal_Icc_pos (by norm_num : (3 : ℝ) < 4)).ne' (measure_ne_top _ _)
  let c : ℝ := (2 * gaussianDensityFloor) ^ 18 * γ.real (Icc (3 : ℝ) 4) / (1800 : ℝ) ^ 18
  have hc_pos : 0 < c := div_pos
    (mul_pos (pow_pos (mul_pos two_pos gaussianDensityFloor_pos) 18) hp_box)
    (by norm_num)
  refine ⟨c, hc_pos, ?_⟩
  have hent := (tendsto_add_atTop_nat 3).eventually
    eventually_nearHilbertContinuousCircuitEntropy_lt_projectiveBooleanCarrier
  filter_upwards [hent, eventually_ge_atTop 192] with k hentropy hlarge
  intro N P T hT2
  have hT_pos : 0 < T := by linarith only [hT2]
  obtain ⟨a, b, hab, hL, hM, hR, hcost⟩ := exists_affordable_cuts (k + 1) (by omega)
  let i₀ : PrefixIndex (k + 1) := (pathCoeffEquiv (k + 1)).symm (.inl (0, 0))
  have hi₀_not_cut : i₀ ∉ cutSet a b := onsite_not_in_cutSet a b (0, 0)
  let δ := 1 / (1800 * T)
  have hδ_pos : 0 < δ := div_pos zero_lt_one (by linarith only [hT_pos])
  have hδ_le1 : δ ≤ 1 := div_le_one_of_le₀ (by linarith only [hT2]) (by linarith only [hT_pos])
  let Box : Set (PrefixIndex (k + 1) → ℝ) := cutAndSingleEvent (cutSet a b) i₀ δ
  have hBox_meas : MeasurableSet Box := measurableSet_cutAndSingleEvent (cutSet a b) i₀ δ
  have hBox_mass : (2 * gaussianDensityFloor * δ) ^ 18 * γ.real (Icc (3 : ℝ) 4) ≤
      (Measure.pi fun _ : PrefixIndex (k + 1) => γ).real Box := by
    have h := pi_cutAndSingleEvent_floor (cutSet a b) i₀ hi₀_not_cut hδ_pos.le hδ_le1
    rw [cutSet_card hab] at h
    exact h
  -- Push Box forward to pathPauliDisorderLaw and intersect with a.e. maximal projectivity
  let x_map : PathPauliDisorder → PrefixIndex (k + 1) → ℝ :=
    fun ω i => pathPauliDisorderShell ω (k + 1) (pathCoeffEquiv (k + 1) i)
  have hmp := gaussian_pauli_prefix_coordinates_law (k + 1)
  have hpre_mass : pathPauliDisorderLaw.real (x_map ⁻¹' Box) =
      (Measure.pi fun _ : PrefixIndex (k + 1) => γ).real Box :=
    congrArg ENNReal.toReal (hmp.measure_preimage hBox_meas.nullMeasurableSet)
  let TargetEvent : Set PathPauliDisorder := {ω : PathPauliDisorder |
    let u := pathPauliDisorderShell ω (k + 1)
    let H : selfAdjoint (Register N) := ⟨pathHamiltonian u, isSelfAdjoint_pathHamiltonian u⟩
    MaximallyProjectiveEnergy H.2.isHermitian.eigenvalues ∧
    (∃ τ > 0, (∀ m : Fin (2 ^ N), ((m : ℕ) : ℝ) * τ ∈ Icc (0 : ℝ) 1) ∧
      Module.finrank ℂ (Submodule.span ℂ
        (range fun m : Fin (2 ^ N) => unitaryEvolution H.val (((m : ℕ) : ℝ) * τ))) = 2 ^ N) ∧
    (∃ t₀ ∈ Ioc (0 : ℝ) T, ∀ z : ℂ, ‖z‖ = 1 →
      Real.sqrt 2 ≤ ‖unitaryEvolution H.val t₀ - z • (1 : Register N)‖) ∧
    (∀ s : ℕ, P / 2 ≤ s → s ≤ P → T < tenthPlateauOnset H s)}
  have hae_sub : x_map ⁻¹' Box ≤ᵐ[pathPauliDisorderLaw] TargetEvent := by
    filter_upwards [gaussian_path_all_prefixes_maximally_projective] with ω hmax_all
    change ((∀ i ∈ cutSet a b, |x_map ω i| ≤ δ) ∧ 3 ≤ |x_map ω i₀|) → ω ∈ TargetEvent
    rintro ⟨hweak, honsite_x⟩
    let u := pathPauliDisorderShell ω (k + 1)
    let H : selfAdjoint (Register N) := ⟨pathHamiltonian u, isSelfAdjoint_pathHamiltonian u⟩
    have hmax : MaximallyProjectiveEnergy H.2.isHermitian.eigenvalues := hmax_all k
    -- Property 1: Vandermonde rank 2^N inside [0, 1]
    have hvand : ∃ τ > 0, (∀ m : Fin (2 ^ N), ((m : ℕ) : ℝ) * τ ∈ Icc (0 : ℝ) 1) ∧
        Module.finrank ℂ (Submodule.span ℂ
          (range fun m : Fin (2 ^ N) => unitaryEvolution H.val (((m : ℕ) : ℝ) * τ))) = 2 ^ N := by
      have hden_pos : 0 < ((2 ^ N : ℕ) : ℝ) * (‖H.val‖ + 1) :=
        mul_pos (by positivity) (add_pos_of_nonneg_of_pos (norm_nonneg _) zero_lt_one)
      let τ := 1 / (((2 ^ N : ℕ) : ℝ) * (‖H.val‖ + 1))
      have hτ_pos : 0 < τ := div_pos zero_lt_one hden_pos
      have hτ_le_pi : τ ≤ Real.pi / (‖H.val‖ + 1) := by
        have h1_le_D : (1 : ℝ) ≤ ((2 ^ N : ℕ) : ℝ) := by exact_mod_cast Nat.one_le_two_pow
        have h1 : 1 / (((2 ^ N : ℕ) : ℝ) * (‖H.val‖ + 1)) ≤ 1 / (‖H.val‖ + 1) :=
          div_le_div_of_nonneg_left zero_le_one
            (add_pos_of_nonneg_of_pos (norm_nonneg _) zero_lt_one)
            (le_mul_of_one_le_left (add_nonneg (norm_nonneg _) zero_le_one) h1_le_D)
        exact h1.trans (div_le_div_of_nonneg_right
          ((by norm_num : (1 : ℝ) ≤ 3).trans Real.pi_gt_three.le)
          (add_nonneg (norm_nonneg _) zero_le_one))
      obtain ⟨_, hspan_eq, hfinrank⟩ := orbit_vandermonde_span_eq_spectralSpan H hmax.injective
        hτ_pos hτ_le_pi
      refine ⟨τ, hτ_pos, fun m => ⟨mul_nonneg (Nat.cast_nonneg _) hτ_pos.le, ?_⟩, ?_⟩
      · dsimp only [τ]
        rw [mul_one_div, div_le_one hden_pos]
        have hm_le : ((m : ℕ) : ℝ) ≤ ((2 ^ N : ℕ) : ℝ) := by exact_mod_cast m.isLt.le
        have hH1 : 1 ≤ ‖H.val‖ + 1 := le_add_of_nonneg_left (norm_nonneg _)
        exact hm_le.trans (le_mul_of_one_le_right (by positivity) hH1)
      · rw [hspan_eq, hfinrank]
    -- Property 2: Scalar-return excision ≥ √2 at some t₀ ∈ (0, π / 2) ⊆ (0, T]
    have honsite : 3 ≤ |u (.inl (0, 0))| := by
      have hcoord_eq : x_map ω i₀ = u (.inl (0, 0)) := by
        dsimp only [x_map, i₀, u]
        rw [Equiv.apply_symm_apply]
      rwa [hcoord_eq] at honsite_x
    obtain ⟨t₀, ht₀_mem, ht₀_exc⟩ := scalarReturnExcised_of_single_onsite u honsite
    have ht₀_T : t₀ ∈ Ioc 0 T := ⟨ht₀_mem.1, ht₀_mem.2.le.trans
      ((div_le_div_of_nonneg_right Real.pi_lt_four.le two_pos.le).trans
        (by norm_num; exact hT2))⟩
    -- Property 3: T < tenthPlateauOnset H s for all P / 2 ≤ s ≤ P
    let d := 2 ^ N - 1
    let e_fin : Config N ≃ Fin (d + 1) := (Fintype.equivFin _).trans
      (finCongr (by
        simp only [Config, Fintype.card_fun, Fintype.card_fin, Fintype.card_bool]
        have hd : 0 < 2 ^ N := pow_pos (by decide) N
        dsimp [d]; omega))
    obtain ⟨σ, hσ_gt, hσ_eq, _, _, _⟩ := first_circuit_threshold_of_increment e_fin H
      (hmax.comp_equiv e_fin.symm) hentropy T hT_pos.le hcost
      (weak_increment u hab hL hM hR hT_pos hweak)
    have honset_gt (s : ℕ) (hs_lo : P / 2 ≤ s) (hs_hi : s ≤ P) :
        T < tenthPlateauOnset H s := by
      have hearly (t : ℝ) (ht : t ∈ Icc 0 T) : orbitCircuitDistance H s t < 1 / 10 := by
        have habs : |t| ≤ T := by rw [abs_of_nonneg ht.1]; exact ht.2
        obtain ⟨z, hz, C, hC, herr⟩ := weak_increment u hab hL hM hR hT_pos hweak t habs
        have hC_le : C.gateCount ≤ s := hC.trans (by omega)
        have hd := (hasProjectiveCircuitApproximation_iff_infDist _ s (1 / 100 : ℝ)).mp
          ⟨z, hz, C, hC_le, herr⟩
        change orbitCircuitDistance H s t ≤ 1 / 100 at hd
        linarith only [hd]
      have hB_gt : 1 / 10 < orbitCircuitDistance H s σ := by
        have hmono : orbitCircuitDistance H P σ ≤ orbitCircuitDistance H s σ := by
          apply (hasProjectiveCircuitApproximation_iff_infDist _ P _).mp
          obtain ⟨z, hz, C, hC, herr⟩ := (hasProjectiveCircuitApproximation_iff_infDist _ s _).mpr
            (le_rfl : orbitCircuitDistance H s σ ≤ _)
          exact ⟨z, hz, C, hC.trans hs_hi, herr⟩
        rw [hσ_eq] at hmono
        linarith only [hmono]
      exact (tenthPlateauOnset_spec H hT_pos (hT_pos.trans hσ_gt).le hearly hB_gt).1
    exact ⟨hmax, hvand, ⟨t₀, ht₀_T, ht₀_exc⟩, honset_gt⟩
  have hmeas_le : (Measure.pi fun _ : PrefixIndex (k + 1) => γ).real Box ≤
      pathPauliDisorderLaw.real TargetEvent := by
    rw [← hpre_mass]
    exact ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono_ae hae_sub)
  have hc_eq : c = T ^ 18 * ((2 * gaussianDensityFloor * δ) ^ 18 * γ.real (Icc (3 : ℝ) 4)) := by
    dsimp only [c, δ]
    field_simp [hT_pos.ne']
    ring
  rw [hc_eq]
  exact mul_le_mul_of_nonneg_left (hBox_mass.trans hmeas_le) (pow_nonneg hT_pos.le 18)

/-- Infinite `18`th absolute moment of `tenthPlateauOnset H_N s` under the Gaussian Pauli-chain
law for every budget `P / 2 ≤ s ≤ P` (including `s = P = nearHilbertContinuousCircuitBudget N`). -/
theorem not_integrable_tenthPlateauOnset_pow_eighteen :
    ∀ᶠ k : ℕ in atTop,
      let N := k + 3
      let P := nearHilbertContinuousCircuitBudget N
      ∀ s : ℕ, P / 2 ≤ s → s ≤ P →
        ¬ Integrable (fun ω : PathPauliDisorder =>
            |tenthPlateauOnset
              ⟨pathHamiltonian (pathPauliDisorderShell ω (k + 1)),
                isSelfAdjoint_pathHamiltonian (pathPauliDisorderShell ω (k + 1))⟩ s| ^ 18)
          pathPauliDisorderLaw := by
  obtain ⟨c, hc_pos, htail_ev⟩ := gaussian_two_cut_vandermonde_returnExcised_tail
  letI : IsProbabilityMeasure pathPauliDisorderLaw := by unfold pathPauliDisorderLaw; infer_instance
  filter_upwards [htail_ev] with k hk
  intro N P s hs_lo hs_hi
  let x_map : PathPauliDisorder → PrefixIndex (k + 1) → ℝ :=
    fun ω i => pathPauliDisorderShell ω (k + 1) (pathCoeffEquiv (k + 1) i)
  have hmp := gaussian_pauli_prefix_coordinates_law (k + 1)
  let J : PathPauliDisorder → ℝ := fun ω =>
    tenthPlateauOnset
      ⟨pathHamiltonian (pathPauliDisorderShell ω (k + 1)),
        isSelfAdjoint_pathHamiltonian (pathPauliDisorderShell ω (k + 1))⟩ s
  have hJ_eq : J = (fun x => tenthPlateauOnset (prefixGenerator (k + 1) x) s) ∘ x_map := by
    funext ω
    dsimp only [J, Function.comp_apply]
    congr 1
    apply Subtype.ext
    exact (numberedGenerator_shell (pathPauliDisorderShell ω (k + 1))).symm
  have hJ_meas : Measurable J := by
    rw [hJ_eq]
    exact (measurable_tenthPlateauOnset_prefix (k + 1) s).comp hmp.measurable
  refine not_integrable_boundary_moment pathPauliDisorderLaw J hJ_meas 18
    (B := 2) two_pos (p := c / (2 : ℝ) ^ 19) (by positivity) fun a ha => ?_
  have h2a : 2 ≤ a * 2 := by linarith only [ha]
  have hfloor := hk (a * 2) h2a
  have hmono : pathPauliDisorderLaw.real {ω : PathPauliDisorder |
      let u := pathPauliDisorderShell ω (k + 1)
      let H : selfAdjoint (Register N) := ⟨pathHamiltonian u, isSelfAdjoint_pathHamiltonian u⟩
      MaximallyProjectiveEnergy H.2.isHermitian.eigenvalues ∧
      (∃ τ > 0, (∀ m : Fin (2 ^ N), ((m : ℕ) : ℝ) * τ ∈ Icc (0 : ℝ) 1) ∧
        Module.finrank ℂ (Submodule.span ℂ
          (range fun m : Fin (2 ^ N) => unitaryEvolution H.val (((m : ℕ) : ℝ) * τ))) = 2 ^ N) ∧
      (∃ t₀ ∈ Ioc (0 : ℝ) (a * 2), ∀ z : ℂ, ‖z‖ = 1 →
        Real.sqrt 2 ≤ ‖unitaryEvolution H.val t₀ - z • (1 : Register N)‖) ∧
      (∀ s' : ℕ, P / 2 ≤ s' → s' ≤ P → a * 2 < tenthPlateauOnset H s')} ≤
      pathPauliDisorderLaw.real {ω | a * 2 < J ω} :=
    measureReal_mono (fun ω hω => hω.2.2.2 s hs_lo hs_hi) (measure_ne_top _ _)
  have hcomb := hfloor.trans (mul_le_mul_of_nonneg_left hmono (by positivity))
  rw [mul_pow] at hcomb
  have hdiv : c / (2 : ℝ) ^ 19 < a ^ 18 * pathPauliDisorderLaw.real {ω | a * 2 < J ω} := by
    rw [div_lt_iff₀ (by positivity)]
    calc c < 2 * c := by linarith only [hc_pos]
      _ ≤ 2 * (a ^ 18 * 2 ^ 18 * pathPauliDisorderLaw.real {ω | a * 2 < J ω}) := by
          linarith only [hcomb]
      _ = a ^ 18 * pathPauliDisorderLaw.real {ω | a * 2 < J ω} * 2 ^ 19 := by ring
  exact hdiv

#print axioms trace_allZ_mul_eq_zero_of_lt_half
#print axioms realizes_finitePauliMatrix_of_half_le
#print axioms span_phaseCircuitMatrixImage_eq_top_iff
#print axioms four_pow_le_finrank_replicaTargetSpan_of_half_le
#print axioms orbit_vandermonde_span_eq_spectralSpan
#print axioms choiFidelity_ge_of_hasProjectiveCircuitApproximation
#print axioms tenthPlateauOnset_lt_of_returnExcised_replicaGram
#print axioms krylov_empiricalBessel_lower_bound
#print axioms no_exponential_replicaGram_exclusion_at_nearHilbert
#print axioms measurable_tenthPlateauOnset_prefix
#print axioms gaussian_two_cut_vandermonde_returnExcised_tail
#print axioms not_integrable_tenthPlateauOnset_pow_eighteen

end
end GaloisForLFunctions.HTGeometry.AccuracyScales.TenthPlateau
