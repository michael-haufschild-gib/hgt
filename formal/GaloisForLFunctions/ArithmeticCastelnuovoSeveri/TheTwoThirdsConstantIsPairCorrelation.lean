import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.TheFrobeniusSpanDefectCountsTheOuterEigenvalues
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.ArithmeticHodgeIndexSignatureLaw
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.DistinctEffectiveCyclesMeetNonnegatively
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.BezoutEffectivityAndTheBeurlingObstruction
import GaloisForLFunctions.HTGeometry.RiemannGaussian.HermitianRankTrace.Multiplicity
import GaloisForLFunctions.RHTower.PairCorrelationExchangeRate
import GaloisForLFunctions.RHTower.ZetaThreeQuartersReduction
import GaloisForLFunctions.RHTower.Zeta23SimpleCriticalDensity

/-!
# The constant `2/3`: rank–trace inertia has capacity `2 − κ`, and `2/3` is the pair-correlation threshold

In Weil's proof over `𝔽_q`, Riemann–Roch supplies an effectivity on `C × C`, forcing the
Castelnuovo–Severi defect `δ(f, f) = W(f, f)` to be positive semidefinite (`scalingSurface_hodgeIndex_iff`).
By the Pontryagin law (`pontryagin_law_curve`, `pontryagin_law`), the number of negative squares of
the defect is the number `p` of off-line zero pairs `{ρ, 1 − ρ̄}` (`Re ρ > ½`). When Riemann–Roch
effectivity is absent, `p` is not known to vanish; **rank–trace inertia** replaces the global sign
of the defect by the matrix inertia of its real evaluation Gram matrix `Â = P + Q` on a finite
window of probe cycles:

* on-line zeros (`Re ρ = ½`, `v_ρ` real) contribute a positive semidefinite sum `P = Σ m_ρ v_ρ v_ρᵀ`
  of rank at most `s₁ + s₂` and trace at most `N_on`;
* each off-line pair `{ρ, 1 − ρ̄}` contributes a hyperbolic block `2 m_ρ (x_ρ x_ρᵀ − y_ρ y_ρᵀ)` to
  `Q` with at most one positive square (`n₊(Q) ≤ p`) and one negative square (its Hodge defect).

This module proves that the constant `2/3` in the unconditional theorem that `2/3` of the zeros of
`ζ` are simple and on the critical line (`two_thirds_and_pair_correlation_escape`) comes **from the
pair-correlation input at the square-root threshold `λ = 1`, not from the rank–trace form**:

1. **Unique algebraic selection of `c = 2` (`kc_two_weight_identity`, `paramDeficit_of_one_le`,
   `paramDeficit_of_le_one`, `paramDeficit_nonneg_and_eq_zero_iff`).** In the `c`-parameterized
   multiplicity-aware rank–trace inequality `2c tr Â − ‖Â‖_F² ≤ Σ_{on} k_c(m_j) + c² p`, the value
   `c = 2` is the unique parameter for which the double-zero weight `k_c(2)` and the off-line pair
   weight `c²` both equal `2c = 4`, cancelling `2(s₁ + 2s₂ + 2p) ≤ 2N` and isolating `s₁` with unit
   coefficient `k₂(1) − 2 = 1`. For every `κ > 1` and `c ≠ 2`, the `c`-parameterized bound is
   strictly smaller than `2 − κ` by the exact quadratic deficit `(κ − 1)(c − 2)²/2` (for `c ≥ 1`).
2. **The form has capacity `2 − κ`, calibrated to `1` over `𝔽_q` and `≤ 0` on fake curves
   (`unitary_calibration_full_simple`, `fake_curve_frobSq_lower_bound`, `goldenDatum_rankTrace_barrier`).**
   When the normalized trace is `tr Â = N` and the normalized Frobenius norm is `‖Â‖_F² = κ N`, the
   `c = 2` rank–trace form certifies `(2 − κ)N` simple on-line zeros. Over `𝔽_q`, a unitary curve
   datum with `N` simple eigenvalues on an orthonormal contact frame (`doubleZeroBlockData N 0`) has
   `κ = 1`, certifying `2 − 1 = 1` (`100%` simple on-line zeros, Weil's theorem). For a fake curve
   with no simple on-line eigenvalues (`s₁ = 0`, such as `goldenDatum` where `N = 2, p = 1` and the
   Hodge defect is `1`), rank–trace inertia forces `‖Â‖_F² ≥ 4 tr Â − 2N`, hence `κ ≥ 2` and
   `2 − κ ≤ 0`.
3. **Coalescence indistinguishability and exact sharpness at `2 − κ` (`doubleZeroBlockData`,
   `coalescedPairBlockData`, `blockA_coalescedPair_eq_doubleZero`, `rankTrace_tight_at_two_thirds`).**
   A double on-line zero (`m = 2`, contributing `2 v vᵀ` to `P`) and a reflected off-line pair
   coalescing on the critical line (`y_ρ = 0`, contributing `2 x xᵀ` to `Q`) produce the **exact
   same Gram matrix** `blockA` on the probe cycles. For every `s₁, d₂ : ℕ` (`N = s₁ + 2d₂`),
   `doubleZeroBlockData s₁ d₂` (all `N` zeros on the line, `s₁` simple and `d₂` double) and
   `coalescedPairBlockData s₁ d₂` (`s₁` simple zeros on the line and `d₂` coalesced off-line pairs)
   share the identical matrix `diag(1, …, 1, 2, …, 2)` with `tr Â = N`, `‖Â‖_F² = s₁ + 4d₂`, and
   `4 tr Â − ‖Â‖_F² − 2N = s₁ = N_on(coalesced)`. At `s₁ = 4k, d₂ = k` (`N = 6k`), `‖Â‖_F² = (4/3)N`
   (`κ = 4/3`) and `s₁ = N_on = (2/3)N` with exact equality: no theorem from `(N, tr Â, ‖Â‖_F²)` and
   the block inertia can certify a single zero beyond `(2/3)N` when `κ = 4/3`.
4. **Why `κ = 4/3` is the sub-threshold pair-correlation limit, and how pair correlation beyond `1`
   breaks `2/3` (`subthreshold_two_thirds_deficit`, `subthreshold_cert_le_two_thirds`,
   `two_thirds_and_pair_correlation_escape`, `tendsto_certOpt_atTop`).**
   Effective cycles satisfy Bézout positivity (`localPair_nonneg`), but positive cones without
   sections fail Riemann–Roch (`graphCone_not_riemannRoch`), and the local pairing matches the zero
   Gram only for the von Mangoldt weight `Λ` (`one_positive_square_iff_vonMangoldt`). Below the
   square-root threshold `0 < λ ≤ 1` (where only the unconditional prime diagonal `F(α) = α` enters,
   adding `λ/3` to the archimedean self-pairing `1/λ`), `kfun λ = 1/λ + λ/3` satisfies the exact
   identity `2/3 − (2 − kfun λ) = (1 − λ)(3 − λ)/(3λ) ≥ 0`, attaining `2/3` uniquely at `λ = 1`
   (`kfun 1 = 4/3`). Above `λ = 1`, any finite bound `F ≤ B` (`B > 2/3`) on pair correlation beyond
   `1` lowers `κ` below `4/3` and raises the rank–trace yield to `H*(B) = 2/3 + 1/(3(3B − 2)) > 2/3`,
   reaching `≥ 3/4` for `B ≤ 2` (`λ = 4/3`) and `1` for the GUE value `B = 1`.
-/

open Complex Finset Matrix Filter
open scoped BigOperators ComplexOrder Topology
open GaloisForLFunctions.HTGeometry
open RiemannGaussian.HermitianRankTrace
open RiemannGaussian.HermitianRankTrace.Multiplicity
open Zeta23 Zeta23.ZeroSide

noncomputable section

namespace GaloisForLFunctions.ArithmeticCastelnuovoSeveri

/-! ## 1. Calibration over `𝔽_q`: trace and Frobenius norm of the Frobenius span Gram -/

namespace CurveDatum

variable {ι : Type*} [Fintype ι] (D : CurveDatum ι)

/-- The span Gram matrix `D.spanGram n` is Hermitian (real symmetric). -/
theorem spanGram_isHermitian (n : ℕ) : (D.spanGram n).IsHermitian := by
  ext k l
  simp only [conjTranspose_apply, spanGram, RCLike.star_def, Complex.conj_ofReal, Nat.dist_comm]

/-- **Trace of the Frobenius span Gram is adjunction (`n · 2g`).** Each diagonal entry `(k, k)` of
`D.spanGram n` is the lag-zero Lefschetz trace `D.trace 0 = #ι = 2g`. -/
theorem rtrace_spanGram (n : ℕ) :
    RHLinalg.rtrace (D.spanGram n) = (n : ℝ) * (Fintype.card ι : ℝ) := by
  unfold RHLinalg.rtrace spanGram Matrix.trace
  simp [Nat.dist_self, D.trace_zero]

/-- **Frobenius norm of the Frobenius span Gram: adjunction diagonal plus Lefschetz pair correlation.**
On a window of `n` Frobenius graphs, `‖D.spanGram n‖_F²` splits into the diagonal adjunction term
`n · (2g)²` (which after trace normalization `G / (n · 2g)` becomes `1/n`, the `𝔽_q` counterpart of
`1/λ`) and the off-diagonal power-sum correlation `Σ_{k ≠ l} (Tr F^{|k−l|})²` (the `𝔽_q` counterpart
of the prime-comb pair-correlation integral). -/
theorem frobSq_spanGram_eq_diag_add_offDiag (n : ℕ) :
    RHLinalg.frobSq (D.spanGram n) =
      (n : ℝ) * (Fintype.card ι : ℝ) ^ (2 : ℕ) +
        ∑ k : Fin n, ∑ l ∈ Finset.univ.erase k, D.trace (Nat.dist k l) ^ (2 : ℕ) := by
  unfold RHLinalg.frobSq
  rw [(D.spanGram_isHermitian n).eq]
  unfold Matrix.trace
  simp only [diag_apply, mul_apply, spanGram, map_sum, ← Complex.ofReal_mul, RCLike.re_to_complex,
    Complex.ofReal_re, ← sq]
  have hsplit : ∀ k : Fin n,
      ∑ l : Fin n, D.trace (Nat.dist k l) ^ (2 : ℕ) =
        (Fintype.card ι : ℝ) ^ (2 : ℕ) +
          ∑ l ∈ Finset.univ.erase k, D.trace (Nat.dist k l) ^ (2 : ℕ) := by
    intro k
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ k), Nat.dist_self, D.trace_zero]
  simp_rw [hsplit]
  rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

end CurveDatum

/-! ## 2. Algebraic selection of `c = 2` in multiplicity-aware rank–trace inertia -/

/-- **Weight cancellation identity at `c = 2`.** In the multiplicity-aware rank–trace bound
`2c tr Â − ‖Â‖_F² ≤ Σ_{on} k_c(m_j) + c² p`, setting `c = 2` gives `k₂(1) = 3` and `k₂(m) = 4 = 2²`
for `m ≥ 2`, so the total right-hand capacity `3s₁ + 4s₂ + 4p` splits into `s₁` plus twice the
minimum divisor count `s₁ + 2s₂ + 2p ≤ N`. -/
theorem kc_two_weight_identity (s₁ s₂ p N : ℝ) :
    kc 2 1 * s₁ + kc 2 2 * s₂ + (2 : ℝ) ^ (2 : ℕ) * p - 2 * N
      = s₁ - 2 * (N - (s₁ + 2 * s₂ + 2 * p)) := by
  rw [kc_two_one, kc_two_of_two_le le_rfl]
  ring

/-- The polynomial deficit between the `c = 2` capacity `2 − κ` and the `c`-parameterized simple-zero
bound `(2c − κ − c²/2) / (k_c(1) − c²/2)`, written without division as
`(2 − κ)(k_c(1) − c²/2) − (2c − κ − c²/2)`. -/
def paramDeficit (c κ : ℝ) : ℝ :=
  (2 - κ) * (kc c 1 - c ^ (2 : ℕ) / 2) - (2 * c - κ - c ^ (2 : ℕ) / 2)

/-- **Exact parameter-deficit identity for `c ≥ 1`.** For every `c ≥ 1` and every `κ`, the deficit
of the `c`-parameterized rank–trace bound below `2 − κ` is `(κ − 1)(c − 2)² / 2`. -/
theorem paramDeficit_of_one_le {c : ℝ} (hc : 1 ≤ c) (κ : ℝ) :
    paramDeficit c κ = (κ - 1) * (c - 2) ^ (2 : ℕ) / 2 := by
  unfold paramDeficit
  rw [kc_of_le hc]
  ring

/-- **Exact parameter-deficit identity for `c ≤ 1`.** For `c ≤ 1`, `k_c(1) = c²` and the deficit
below `2 − κ` is `(c − 1)² + (κ − 1)(1 − c²/2)`. -/
theorem paramDeficit_of_le_one {c : ℝ} (hc : c ≤ 1) (κ : ℝ) :
    paramDeficit c κ = (c - 1) ^ (2 : ℕ) + (κ - 1) * (1 - c ^ (2 : ℕ) / 2) := by
  unfold paramDeficit
  rw [kc_of_ge hc]
  ring

/-- **No-go for tuning `c`, and uniqueness of `c = 2`.** For every `c ≥ 0` and every normalized
Frobenius constant `κ > 1`, `paramDeficit c κ ≥ 0`, with equality if and only if `c = 2`. Thus no
choice of the rank–trace parameter `c` can improve the simple-zero proportion `2 − κ`. -/
theorem paramDeficit_nonneg_and_eq_zero_iff {c κ : ℝ} (hc : 0 ≤ c) (hκ : 1 < κ) :
    0 ≤ paramDeficit c κ ∧ (paramDeficit c κ = 0 ↔ c = 2) := by
  rcases le_or_gt 1 c with h1 | h1
  · rw [paramDeficit_of_one_le h1]
    refine ⟨div_nonneg (mul_nonneg (by linarith) (sq_nonneg _)) (by norm_num), ?_⟩
    constructor
    · intro h0
      have hmul : (κ - 1) * (c - 2) ^ (2 : ℕ) = 0 := by linarith
      have hsq : (c - 2) ^ (2 : ℕ) = 0 := (mul_eq_zero.mp hmul).resolve_left (by linarith)
      linarith [sq_eq_zero_iff.mp hsq]
    · rintro rfl; ring
  · rw [paramDeficit_of_le_one h1.le]
    have hc2 : c ^ (2 : ℕ) ≤ 1 := by nlinarith
    have hpos : 0 < (c - 1) ^ (2 : ℕ) + (κ - 1) * (1 - c ^ (2 : ℕ) / 2) := by
      have : 0 < (κ - 1) * (1 - c ^ (2 : ℕ) / 2) := mul_pos (by linarith) (by linarith)
      linarith [sq_nonneg (c - 1)]
    exact ⟨hpos.le, ⟨fun h0 => absurd h0 hpos.ne', fun h2 => by linarith⟩⟩

/-! ## 2. Exact extremal configurations and coalescence indistinguishability -/

/-- Coordinate basis vector `e_z` in `ℂ^d`. -/
def unitVec {d : Type*} [DecidableEq d] (z k : d) : ℂ :=
  if k = z then 1 else 0

@[simp]
private lemma star_unitVec {d : Type*} [DecidableEq d] (z : d) :
    star (unitVec z) = unitVec z := by
  ext k
  simp only [Pi.star_apply, unitVec]
  split_ifs <;> simp

private lemma unitVec_mul {d : Type*} [DecidableEq d] (z k l : d) :
    unitVec z k * unitVec z l = if z = k then (if k = l then 1 else 0) else 0 := by
  simp only [unitVec]
  by_cases hzk : z = k
  · subst hzk
    by_cases hkl : z = l
    · subst hkl; simp
    · have hlk : l ≠ z := Ne.symm hkl
      simp [hkl, hlk]
  · have hkz : k ≠ z := Ne.symm hzk
    simp [hzk, hkz]

@[simp]
private lemma unitVec_inl_inr {α β : Type*} [DecidableEq α] [DecidableEq β] (x : α) (y : β) :
    unitVec (Sum.inl x : α ⊕ β) (Sum.inr y) = 0 := by
  simp [unitVec]

@[simp]
private lemma unitVec_inr_inl {α β : Type*} [DecidableEq α] [DecidableEq β] (x : β) (y : α) :
    unitVec (Sum.inr x : α ⊕ β) (Sum.inl y) = 0 := by
  simp [unitVec]

@[simp]
private lemma unitVec_inl_inl {α β : Type*} [DecidableEq α] [DecidableEq β] (x y : α) :
    unitVec (Sum.inl x : α ⊕ β) (Sum.inl y) = unitVec x y := by
  simp [unitVec]

@[simp]
private lemma unitVec_inr_inr {α β : Type*} [DecidableEq α] [DecidableEq β] (x y : β) :
    unitVec (Sum.inr x : α ⊕ β) (Sum.inr y) = unitVec x y := by
  simp [unitVec]

/-- The extremal `ZeroBlockData` configuration with `s₁` simple critical-line zeros and `d₂` double
critical-line zeros on an orthonormal probe frame of size `s₁ + d₂` (no off-line pairs: `p = 0`). -/
def doubleZeroBlockData (s₁ d₂ : ℕ) :
    ZeroBlockData (Fin s₁ ⊕ Fin d₂) (Fin s₁ ⊕ Fin d₂) where
  m := Sum.elim (fun _ => 1) (fun _ => 2)
  one_le_m z := by rcases z with _ | _ <;> simp
  v z := unitVec z
  σ := id
  σ_invol _ := rfl
  m_σ _ := rfl
  v_σ z := (star_unitVec z).symm

/-- The extremal `ZeroBlockData` configuration with `s₁` simple critical-line zeros and `p`
reflected off-line pairs that have coalesced onto the probe frame (`yv = 0`, `xv` orthonormal and
orthogonal to the critical-line frame; `s₂ = 0`). -/
def coalescedPairBlockData (s₁ p : ℕ) :
    ZeroBlockData (Fin s₁ ⊕ (Fin p ⊕ Fin p)) (Fin s₁ ⊕ Fin p) where
  m _ := 1
  one_le_m _ := le_rfl
  v := Sum.elim (fun i => unitVec (Sum.inl i))
    (Sum.elim (fun j => unitVec (Sum.inr j)) (fun j => unitVec (Sum.inr j)))
  σ := Sum.map id (Equiv.sumComm (Fin p) (Fin p))
  σ_invol z := by rcases z with i | (j | j) <;> rfl
  m_σ _ := rfl
  v_σ z := by
    rcases z with i | (j | j) <;> simp [star_unitVec]

/-- Canonical off-line pair representatives for `coalescedPairBlockData s₁ p`: the first copy of
each reflected pair in `Fin p ⊕ Fin p`. -/
def coalescedPairReps (s₁ p : ℕ) : (coalescedPairBlockData s₁ p).PairReps where
  R := Finset.univ.map ⟨fun j : Fin p => Sum.inr (Sum.inl j),
    fun _ _ h => Sum.inl.inj (Sum.inr.inj h)⟩
  off z hz := by
    rcases Finset.mem_map.mp hz with ⟨j, _, rfl⟩
    simp [coalescedPairBlockData]
  σ_not_mem z hz hσ := by
    rcases Finset.mem_map.mp hz with ⟨j, _, rfl⟩
    rcases Finset.mem_map.mp hσ with ⟨j', _, hj'⟩
    simp [coalescedPairBlockData] at hj'
  cover z hz := by
    rcases z with i | (j | j)
    · exact False.elim (hz rfl)
    · exact Or.inl (Finset.mem_map.mpr ⟨j, Finset.mem_univ j, rfl⟩)
    · exact Or.inr (Finset.mem_map.mpr ⟨j, Finset.mem_univ j, rfl⟩)

/-- The canonical diagonal matrix `diag(1, …, 1, 2, …, 2)` (`s₁` ones and `d₂` twos) shared by
`doubleZeroBlockData s₁ d₂` and `coalescedPairBlockData s₁ d₂`. -/
def extremalDiag (s₁ d₂ : ℕ) : Matrix (Fin s₁ ⊕ Fin d₂) (Fin s₁ ⊕ Fin d₂) ℂ :=
  Matrix.diagonal (Sum.elim (fun _ : Fin s₁ => (1 : ℂ)) (fun _ : Fin d₂ => (2 : ℂ)))

/-- The Gram matrix `blockA` of `doubleZeroBlockData s₁ d₂` is `extremalDiag s₁ d₂`. -/
theorem blockA_doubleZeroBlockData (s₁ d₂ : ℕ) :
    (doubleZeroBlockData s₁ d₂).blockA = extremalDiag s₁ d₂ := by
  ext k l
  rw [ZeroBlockData.blockA_apply]
  simp only [doubleZeroBlockData, extremalDiag, diagonal_apply, unitVec_mul, mul_ite, mul_one,
    mul_zero]
  rw [Finset.sum_ite_eq' Finset.univ k]
  simp only [Finset.mem_univ, if_true]
  rcases k with i | j <;> simp

/-- **Coalescence indistinguishability.** The Gram matrix `blockA` of `coalescedPairBlockData s₁ d₂`
(`s₁` simple critical zeros and `d₂` coalesced off-line pairs) is **identical** to the Gram matrix
of `doubleZeroBlockData s₁ d₂` (`s₁` simple critical zeros and `d₂` double critical zeros). No
matrix functional of `blockA` can separate critical-line multiplicity `2` from a coalescing
off-line pair. -/
theorem blockA_coalescedPairBlockData (s₁ d₂ : ℕ) :
    (coalescedPairBlockData s₁ d₂).blockA = extremalDiag s₁ d₂ := by
  ext k l
  rw [ZeroBlockData.blockA_apply]
  simp only [coalescedPairBlockData, Nat.cast_one, one_mul, extremalDiag, diagonal_apply]
  rw [Fintype.sum_sum_type, Fintype.sum_sum_type]
  simp only [Sum.elim_inl, Sum.elim_inr]
  rw [← two_mul]
  rcases k with ik | jk <;> rcases l with il | jl <;>
    simp [unitVec_mul, Finset.sum_ite_eq']

theorem blockA_coalescedPair_eq_doubleZero (s₁ d₂ : ℕ) :
    (coalescedPairBlockData s₁ d₂).blockA = (doubleZeroBlockData s₁ d₂).blockA := by
  rw [blockA_coalescedPairBlockData, blockA_doubleZeroBlockData]

/-- Trace of `extremalDiag s₁ d₂`: `tr Â = s₁ + 2 d₂ = N`. -/
theorem rtrace_extremalDiag (s₁ d₂ : ℕ) :
    RHLinalg.rtrace (extremalDiag s₁ d₂) = (s₁ : ℝ) + 2 * (d₂ : ℝ) := by
  unfold RHLinalg.rtrace extremalDiag
  rw [trace_diagonal, Fintype.sum_sum_type]
  simp [mul_comm]

/-- Squared Frobenius norm of `extremalDiag s₁ d₂`: `‖Â‖_F² = s₁ + 4 d₂ = 2N − s₁`. -/
theorem frobSq_extremalDiag (s₁ d₂ : ℕ) :
    RHLinalg.frobSq (extremalDiag s₁ d₂) = (s₁ : ℝ) + 4 * (d₂ : ℝ) := by
  have hd : (extremalDiag s₁ d₂)ᴴ = extremalDiag s₁ d₂ := by
    ext i j
    simp only [extremalDiag, conjTranspose_apply, diagonal_apply]
    by_cases hij : j = i
    · subst hij; rcases j with _ | _ <;> simp
    · have hji : i ≠ j := Ne.symm hij
      simp [hij, hji]
  unfold RHLinalg.frobSq
  rw [hd]
  unfold extremalDiag
  rw [diagonal_mul_diagonal, trace_diagonal, Fintype.sum_sum_type]
  simp only [Sum.elim_inl, Sum.elim_inr, mul_one, sum_const, card_univ,
    Fintype.card_fin, nsmul_eq_mul, map_add, RCLike.re_to_complex]
  norm_num
  ring

/-- Total zero count of `doubleZeroBlockData s₁ d₂`: `N = s₁ + 2 d₂`, all on the critical line. -/
theorem Ncount_doubleZeroBlockData (s₁ d₂ : ℕ) :
    (doubleZeroBlockData s₁ d₂).Ncount = s₁ + 2 * d₂ ∧
      (doubleZeroBlockData s₁ d₂).Non = s₁ + 2 * d₂ := by
  have hon : (doubleZeroBlockData s₁ d₂).onLine = Finset.univ := by
    ext z; simp [ZeroBlockData.onLine, doubleZeroBlockData]
  constructor
  · unfold ZeroBlockData.Ncount doubleZeroBlockData
    rw [Fintype.sum_sum_type]
    simp [Nat.mul_comm]
  · unfold ZeroBlockData.Non
    rw [hon]
    exact (Fintype.sum_sum_type _).trans (by simp [doubleZeroBlockData, Nat.mul_comm])

/-- Simple critical zero count of `doubleZeroBlockData s₁ d₂` is `s₁`. -/
theorem s₁_doubleZeroBlockData (s₁ d₂ : ℕ) :
    (doubleZeroBlockData s₁ d₂).s₁ = s₁ := by
  unfold ZeroBlockData.s₁ ZeroBlockData.S₁
  have hS : (Finset.univ.filter fun z : Fin s₁ ⊕ Fin d₂ =>
      (doubleZeroBlockData s₁ d₂).σ z = z ∧ (doubleZeroBlockData s₁ d₂).m z = 1) =
      Finset.univ.map ⟨Sum.inl, Sum.inl_injective⟩ := by
    ext z
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_map,
      Function.Embedding.coeFn_mk, doubleZeroBlockData, id_eq]
    rcases z with i | j <;> simp
  rw [hS, Finset.card_map, Finset.card_univ, Fintype.card_fin]

/-- Total, critical-line, simple critical, and off-line pair counts of `coalescedPairBlockData s₁ p`:
`N = s₁ + 2p`, `N_on = s₁`, `s₁ = s₁`, `s₂ = 0`, and `#𝒫 = p`. -/
theorem counts_coalescedPairBlockData (s₁ p : ℕ) :
    (coalescedPairBlockData s₁ p).Ncount = s₁ + 2 * p ∧
      (coalescedPairBlockData s₁ p).Non = s₁ ∧
      (coalescedPairBlockData s₁ p).s₁ = s₁ ∧
      (coalescedPairBlockData s₁ p).s₂ = 0 ∧
      (coalescedPairReps s₁ p).p = p := by
  have hon : (coalescedPairBlockData s₁ p).onLine =
      Finset.univ.map ⟨Sum.inl, Sum.inl_injective⟩ := by
    ext z
    simp only [ZeroBlockData.onLine, Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_map, Function.Embedding.coeFn_mk, coalescedPairBlockData]
    rcases z with i | (j | j) <;> simp
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · unfold ZeroBlockData.Ncount coalescedPairBlockData
    rw [Fintype.sum_sum_type, Fintype.sum_sum_type]
    simp [two_mul]
  · unfold ZeroBlockData.Non
    rw [hon, Finset.sum_map]
    simp [coalescedPairBlockData]
  · unfold ZeroBlockData.s₁ ZeroBlockData.S₁
    have hS : (Finset.univ.filter fun z =>
        (coalescedPairBlockData s₁ p).σ z = z ∧ (coalescedPairBlockData s₁ p).m z = 1) =
        (coalescedPairBlockData s₁ p).onLine := by
      ext z; simp [ZeroBlockData.onLine, coalescedPairBlockData]
    rw [hS, hon, Finset.card_map, Finset.card_univ, Fintype.card_fin]
  · unfold ZeroBlockData.s₂ ZeroBlockData.S₂
    rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro z _; simp [coalescedPairBlockData]
  · unfold ZeroBlockData.PairReps.p coalescedPairReps
    rw [Finset.card_map, Finset.card_univ, Fintype.card_fin]

/-- **Exact tightness of rank–trace inertia for every `(s₁, d₂)` (`2 − κ` capacity law).**
On `extremalDiag s₁ d₂` (`N = s₁ + 2d₂`), the rank–trace functional `4 tr Â − ‖Â‖_F² − 2N` equals `s₁`
identically, matching both the simple critical count of `doubleZeroBlockData s₁ d₂` (where all `N`
zeros lie on the line) and the total critical count `N_on = s₁` of `coalescedPairBlockData s₁ d₂`
(where `2d₂` zeros lie off the line). -/
theorem rankTrace_extremalDiag_exact (s₁ d₂ : ℕ) :
    4 * RHLinalg.rtrace (extremalDiag s₁ d₂) - RHLinalg.frobSq (extremalDiag s₁ d₂) -
      2 * ((s₁ : ℝ) + 2 * (d₂ : ℝ)) = (s₁ : ℝ) := by
  rw [rtrace_extremalDiag, frobSq_extremalDiag]
  ring

/-- **Calibration over `𝔽_q`: orthonormal unitary spectrum gives `κ = 1` and `100%` simple critical zeros.**
When all `N` eigenvalues are simple and on the unit circle (`d₂ = 0`, orthonormal contact frame
`doubleZeroBlockData N 0`), `tr Â = N`, `‖Â‖_F² = N` (`κ = 1`), and rank–trace inertia certifies
`4 tr Â − ‖Â‖_F² − 2N = N` (`2 − κ = 1`, reducing to Weil's full RH + simplicity). -/
theorem unitary_calibration_full_simple (N : ℕ) :
    RHLinalg.rtrace ((doubleZeroBlockData N 0).blockA) = N ∧
      RHLinalg.frobSq ((doubleZeroBlockData N 0).blockA) = N ∧
      4 * RHLinalg.rtrace ((doubleZeroBlockData N 0).blockA) -
        RHLinalg.frobSq ((doubleZeroBlockData N 0).blockA) - 2 * (N : ℝ) = N := by
  rw [blockA_doubleZeroBlockData, rtrace_extremalDiag, frobSq_extremalDiag]
  simp; ring

/-- **Fake curve barrier (`s₁ = 0`).** For any zero-block configuration without simple on-line
zeros (`s₁ = 0`, such as the golden fake curve `goldenDatum` over `𝔽₅`, whose Hodge defect is `1`
and whose `2` eigenvalues form a single outer pair `p = 1`), rank–trace inertia forces
`4 tr Â − 2N ≤ ‖Â‖_F²`. In particular, normalized trace `tr Â = N` forces `‖Â‖_F² ≥ 2N` (`κ ≥ 2`,
certified proportion `2 − κ ≤ 0`), achieved with equality by `coalescedPairBlockData 0 p`. -/
theorem fake_curve_frobSq_lower_bound {ι d : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype d] [DecidableEq d] (D : ZeroBlockData ι d) (Pr : D.PairReps)
    (hs₁ : D.s₁ = 0) {c : ℝ} (hc : 0 < c)
    (hPois : ∀ z ∈ D.onLine, ∑ k, ‖D.v z k‖ ^ 2 ≤ c) :
    4 * RHLinalg.rtrace (D.blockP c + D.blockQ c) - 2 * (D.Ncount : ℝ) ≤
      RHLinalg.frobSq (D.blockP c + D.blockQ c) := by
  have h := D.mult_two Pr hc hPois
  rw [hs₁, Nat.cast_zero] at h
  linarith

/-- For the golden fake curve (`goldenDatum`, `N = 2`, `p = 1`, `s₁ = 0`), the Hodge defect is `1`
and the coalesced off-line pair `coalescedPairBlockData 0 1` has `tr Â = 2 = N`, `‖Â‖_F² = 4 = 2N`
(`κ = 2`), and rank–trace bound `4 tr Â − ‖Â‖_F² − 2N = 0`. -/
theorem goldenDatum_rankTrace_barrier {n : ℕ} (hn : 2 ≤ n) :
    hermNegIndex (goldenDatum.spanGram n) = 1 ∧
      RHLinalg.rtrace ((coalescedPairBlockData 0 1).blockA) = 2 ∧
      RHLinalg.frobSq ((coalescedPairBlockData 0 1).blockA) = 4 ∧
      4 * RHLinalg.rtrace ((coalescedPairBlockData 0 1).blockA) -
        RHLinalg.frobSq ((coalescedPairBlockData 0 1).blockA) -
        2 * ((coalescedPairBlockData 0 1).Ncount : ℝ) = 0 := by
  refine ⟨goldenDatum_negIndex_spanGram hn, ?_, ?_, ?_⟩
  · rw [blockA_coalescedPairBlockData, rtrace_extremalDiag]; norm_num
  · rw [blockA_coalescedPairBlockData, frobSq_extremalDiag]; norm_num
  · rw [blockA_coalescedPairBlockData, rtrace_extremalDiag, frobSq_extremalDiag,
      (counts_coalescedPairBlockData 0 1).1]
    norm_num

/-- **Why the rank–trace form gives `2/3` and no more at `κ = 4/3`.**
For every scale `k ≥ 1`, the `6k`-zero configurations `doubleZeroBlockData (4k) k` (all `6k` zeros
on the critical line, `4k` simple and `k` double) and `coalescedPairBlockData (4k) k` (`4k` simple
zeros on the critical line and `k` coalesced off-line pairs) have the **same** Gram matrix `Â` with:
* `N = 6k`,
* `tr Â = N`,
* `‖Â‖_F² = (4/3) N` (`κ = 4/3`),
* `s₁ = (2/3) N` in both configurations, and `N_on = (2/3) N` in the coalesced-pair configuration.

Thus no theorem from `(N, tr Â, ‖Â‖_F²)` and the block inertia can certify more than `(2/3)N`
simple critical zeros—or even more than `(2/3)N` critical-line zeros—when `‖Â‖_F² = (4/3)N`. -/
theorem rankTrace_tight_at_two_thirds (k : ℕ) :
    let D_mult := doubleZeroBlockData (4 * k) k
    let D_pair := coalescedPairBlockData (4 * k) k
    D_pair.blockA = D_mult.blockA ∧
      D_mult.Ncount = 6 * k ∧
      D_pair.Ncount = 6 * k ∧
      RHLinalg.rtrace D_mult.blockA = (D_mult.Ncount : ℝ) ∧
      RHLinalg.frobSq D_mult.blockA = (4 / 3 : ℝ) * (D_mult.Ncount : ℝ) ∧
      (D_mult.s₁ : ℝ) = (2 / 3 : ℝ) * (D_mult.Ncount : ℝ) ∧
      (D_pair.Non : ℝ) = (2 / 3 : ℝ) * (D_pair.Ncount : ℝ) ∧
      4 * RHLinalg.rtrace D_mult.blockA - RHLinalg.frobSq D_mult.blockA -
        2 * (D_mult.Ncount : ℝ) = (2 / 3 : ℝ) * (D_mult.Ncount : ℝ) := by
  dsimp only
  have hN1 := (Ncount_doubleZeroBlockData (4 * k) k).1
  have hN2 := (counts_coalescedPairBlockData (4 * k) k).1
  have hNon2 := (counts_coalescedPairBlockData (4 * k) k).2.1
  have hs1 := s₁_doubleZeroBlockData (4 * k) k
  refine ⟨blockA_coalescedPair_eq_doubleZero (4 * k) k, by omega, by omega, ?_, ?_, ?_, ?_, ?_⟩
  · rw [blockA_doubleZeroBlockData, rtrace_extremalDiag, hN1]; push_cast; ring
  · rw [blockA_doubleZeroBlockData, frobSq_extremalDiag, hN1]; push_cast; ring
  · rw [hs1, hN1]; push_cast; ring
  · rw [hNon2, hN2]; push_cast; ring
  · rw [blockA_doubleZeroBlockData, rtrace_extremalDiag, frobSq_extremalDiag, hN1]; push_cast; ring

/-- **Simultaneous tightness of the `c = 3` distinct-zero rank–trace bound (`(3/2 − κ/2)N`).**
On the same matrix `extremalDiag s₁ d₂` (`N = s₁ + 2d₂`), the `c = 3` distinct-zero rank–trace
functional `(6 tr Â − ‖Â‖_F² − 3N) / 2` equals `s₁ + d₂` identically, matching the exact number of
distinct zeros `#ι = s₁ + d₂` of `doubleZeroBlockData s₁ d₂` (and `(5/6)N` at `s₁ = 4k, d₂ = k`). -/
theorem rankTrace_three_extremalDiag_exact (s₁ d₂ : ℕ) :
    (6 * RHLinalg.rtrace (extremalDiag s₁ d₂) - RHLinalg.frobSq (extremalDiag s₁ d₂) -
      3 * ((s₁ : ℝ) + 2 * (d₂ : ℝ))) / 2 = (s₁ : ℝ) + (d₂ : ℝ) := by
  rw [rtrace_extremalDiag, frobSq_extremalDiag]
  ring

/-- Every on-line evaluation vector of `coalescedPairBlockData s₁ p` has unit `ℓ²` norm. -/
theorem norm_sq_v_coalescedPairBlockData (s₁ p : ℕ) (z : Fin s₁ ⊕ (Fin p ⊕ Fin p)) :
    ∑ k : Fin s₁ ⊕ Fin p, ‖(coalescedPairBlockData s₁ p).v z k‖ ^ (2 : ℕ) = 1 := by
  have huniv : ∀ w : Fin s₁ ⊕ Fin p, ∑ k : Fin s₁ ⊕ Fin p, ‖unitVec w k‖ ^ (2 : ℕ) = 1 := by
    intro w
    have hterm : ∀ k : Fin s₁ ⊕ Fin p, ‖unitVec w k‖ ^ (2 : ℕ) = if k = w then 1 else 0 := by
      intro k; simp only [unitVec]; split_ifs <;> simp
    simp_rw [hterm]
    simp
  rcases z with i | (j | j)
  · exact huniv (Sum.inl i)
  · exact huniv (Sum.inr j)
  · exact huniv (Sum.inr j)

/-- **Universal matrix-functional barrier (`4 tr Â − ‖Â‖_F² − 2N` is Pareto-optimal).**
Let `Φ` be **any** real-valued functional of the full evaluation Gram matrix `blockA` and the total
zero count `Ncount` (including arbitrary higher moments `tr(blockA^m)`, eigenvalues, or nonlinear
spectral invariants). If `Φ D.blockA D.Ncount ≤ D.Non` holds for every normalized `ZeroBlockData`
configuration `D` on the probe grid `Fin s₁ ⊕ Fin d₂`, then on `extremalDiag s₁ d₂` (`N = s₁ + 2d₂`),
`Φ` cannot exceed the linear rank–trace bound `4 tr Â − ‖Â‖_F² − 2N = s₁`. -/
theorem universal_matrix_functional_barrier (s₁ d₂ : ℕ)
    (Φ : Matrix (Fin s₁ ⊕ Fin d₂) (Fin s₁ ⊕ Fin d₂) ℂ → ℕ → ℝ)
    (hΦ : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (D : ZeroBlockData ι (Fin s₁ ⊕ Fin d₂)),
      (∀ z ∈ D.onLine, ∑ k, ‖D.v z k‖ ^ (2 : ℕ) ≤ 1) →
      Φ D.blockA D.Ncount ≤ (D.Non : ℝ)) :
    Φ (extremalDiag s₁ d₂) (s₁ + 2 * d₂) ≤
      4 * RHLinalg.rtrace (extremalDiag s₁ d₂) - RHLinalg.frobSq (extremalDiag s₁ d₂) -
        2 * ((s₁ : ℝ) + 2 * (d₂ : ℝ)) := by
  have h := hΦ (Fin s₁ ⊕ (Fin d₂ ⊕ Fin d₂)) (coalescedPairBlockData s₁ d₂)
    (fun z _ => (norm_sq_v_coalescedPairBlockData s₁ d₂ z).le)
  rw [blockA_coalescedPairBlockData, (counts_coalescedPairBlockData s₁ d₂).1,
    (counts_coalescedPairBlockData s₁ d₂).2.1, ← rankTrace_extremalDiag_exact s₁ d₂] at h
  exact h

/-- **Universal `2/3` barrier at `κ = 4/3`.** Any functional `Φ(blockA, Ncount)` that is a valid
lower bound on `N_on` (or `s₁`) for all normalized `ZeroBlockData` configurations on
`Fin (4k) ⊕ Fin k` satisfies `Φ ((doubleZeroBlockData (4k) k).blockA) (6k) ≤ (2/3) · (6k)`. -/
theorem universal_matrix_functional_barrier_at_two_thirds (k : ℕ)
    (Φ : Matrix (Fin (4 * k) ⊕ Fin k) (Fin (4 * k) ⊕ Fin k) ℂ → ℕ → ℝ)
    (hΦ : ∀ (ι : Type) [Fintype ι] [DecidableEq ι]
      (D : ZeroBlockData ι (Fin (4 * k) ⊕ Fin k)),
      (∀ z ∈ D.onLine, ∑ k', ‖D.v z k'‖ ^ (2 : ℕ) ≤ 1) →
      Φ D.blockA D.Ncount ≤ (D.Non : ℝ)) :
    Φ ((doubleZeroBlockData (4 * k) k).blockA) (6 * k) ≤ (2 / 3 : ℝ) * (6 * k : ℝ) := by
  have h := universal_matrix_functional_barrier (4 * k) k Φ hΦ
  rw [← blockA_doubleZeroBlockData, show 4 * k + 2 * k = 6 * k by omega,
    blockA_doubleZeroBlockData, rankTrace_extremalDiag_exact] at h
  linarith

/-! ## 4. Where `κ = 4/3` comes from: the sub-threshold pair-correlation identity and escape beyond `2/3` -/

/-- **Sub-threshold pair-correlation identity (`0 < λ ≤ 1`).** Below the square-root threshold
`λ ≤ 1`, where only the archimedean self-pairing `1/λ` (adjunction) and the unconditional
Montgomery–Vaughan prime diagonal `λ/3` enter the Frobenius norm `kfun λ = 1/λ + λ/3`, the
certified proportion `2 − kfun λ` falls short of `2/3` by the exact rational identity
`(1 − λ)(3 − λ) / (3λ)`. -/
theorem subthreshold_two_thirds_deficit {lam : ℝ} (hlam : lam ≠ 0) :
    (2 / 3 : ℝ) - (2 - Zeta23.kfun lam) = (1 - lam) * (3 - lam) / (3 * lam) := by
  unfold Zeta23.kfun
  field_simp
  ring

/-- **Why `2/3` is the unique maximum below the square-root threshold (`0 < λ ≤ 1`).** For every
`0 < λ ≤ 1`, `2 − kfun λ ≤ 2/3`, with equality if and only if `λ = 1` (where `kfun 1 = 4/3`). -/
theorem subthreshold_cert_le_two_thirds {lam : ℝ} (h0 : 0 < lam) (h1 : lam ≤ 1) :
    2 - Zeta23.kfun lam ≤ 2 / 3 ∧
      (2 - Zeta23.kfun lam = 2 / 3 ↔ lam = 1) := by
  have hdef := subthreshold_two_thirds_deficit h0.ne'
  have h3 : 0 < 3 - lam := by linarith
  have hden : 0 < 3 * lam := by positivity
  refine ⟨?_, ?_⟩
  · have hnn : 0 ≤ (1 - lam) * (3 - lam) / (3 * lam) :=
      div_nonneg (mul_nonneg (by linarith) h3.le) hden.le
    linarith
  · constructor
    · intro heq
      have h0' : (1 - lam) * (3 - lam) / (3 * lam) = 0 := by linarith
      have hmul : (1 - lam) * (3 - lam) = 0 := (div_eq_zero_iff.mp h0').resolve_right hden.ne'
      rcases mul_eq_zero.mp hmul with h | h <;> linarith
    · rintro rfl
      unfold Zeta23.kfun
      norm_num

/-- **Arithmetic source requirements: Bézout positivity of effective cycles, failure of Riemann–Roch
for positive cones without sections, and selection of `Λ`.** Disjoint nonnegative tests meet
nonnegatively (`localPair_nonneg`), positive graph cones satisfy `AmpleAxiom` and `BezoutAxiom` even
on the golden fake curve (`goldenDatum_graphCone_ample_and_bezout`) while failing `RiemannRochAxiom`,
and the arithmetic intersection Gram has the spectral signature `posIndex = 1` under RH if and only
if the prime weight is `Λ` (`one_positive_square_iff_vonMangoldt`). -/
theorem arithmetic_source_constraints_for_rankTrace :
    (∀ f g : ℝ → ℝ, ContDiff ℝ 2 f → HasCompactSupport f → (∀ u, 0 ≤ f u) →
      ContDiff ℝ 2 g → HasCompactSupport g → (∀ u, 0 ≤ g u) → (∀ u, f u * g u = 0) →
      0 ≤ (localPair (fun u => (f u : ℂ)) (fun u => (g u : ℂ))).re) ∧
    (∀ (S : Finset ℕ) (k : ℕ), k ∈ S →
      (goldenDatum.windowSurface S).AmpleAxiom (graphCone S) ∧
        (goldenDatum.windowSurface S).BezoutAxiom (graphCone S) ∧
        ¬ (goldenDatum.windowSurface S).RiemannRochAxiom (graphCone S)) ∧
    (∀ lam : ℕ → ℝ,
      (∀ (n : ℕ) (f : Fin n → ℝ → ℂ), (∀ i, ContDiff ℝ 2 (f i)) →
        (∀ i, HasCompactSupport (f i)) → hermPosIndex (intersectionGram lam f) = 1) ↔
      (RiemannHypothesis ∧ ∀ n, 2 ≤ n → lam n = ArithmeticFunction.vonMangoldt n)) :=
  ⟨fun _ _ hf hfc hf0 hg hgc hg0 hfg => localPair_nonneg hf hfc hf0 hg hgc hg0 hfg,
    fun S _ hk => ⟨(goldenDatum_graphCone_ample_and_bezout S).1,
      (goldenDatum_graphCone_ample_and_bezout S).2,
      goldenDatum.graphCone_not_riemannRoch hk⟩,
    one_positive_square_iff_vonMangoldt⟩

/-- **Unconditional `2/3` simple critical zeros for `ζ` (`λ = 1`, `κ = 4/3`), and escape beyond `2/3`
from pair correlation above `λ = 1`.**
1. Unconditionally (at `λ = 1`, `kfun 1 = 4/3`), at least `2/3` of the nontrivial zeros of `ζ` are
   simple and lie on the critical line (`RHTower.two_thirds_simpleCritical_epsilon`).
2. Every finite upper bound `B > 2/3` on the pair-correlation form factor beyond bandwidth `1`
   strictly beats `2/3` by `RHTower.certOpt B − 2/3 = 1 / (3(3B − 2)) > 0`, reaches `≥ 3/4` iff
   `B ≤ 2`, and reaches `1` (`100%`) at the random-matrix value `B = 1`.
3. Under the bandwidth-`4/3` pair-correlation bound `RHTower.PairCorrelationFourThirds` (`κ = 5/4`),
   at least `3/4` of the nontrivial zeros of `ζ` are simple and on the critical line. -/
theorem two_thirds_and_pair_correlation_escape :
    (∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (2 / 3 - ε) * (RHTower.xiPosZeroCount T : ℝ) ≤ RHTower.xiSimpleCriticalZeroCount T) ∧
    (∀ B : ℝ, 2 / 3 < B →
      RHTower.certOpt B - 2 / 3 = 1 / (3 * (3 * B - 2)) ∧ 2 / 3 < RHTower.certOpt B) ∧
    (∀ B : ℝ, 2 / 3 < B → (3 / 4 ≤ RHTower.certOpt B ↔ B ≤ 2)) ∧
    RHTower.certOpt 1 = 1 ∧
    (RHTower.PairCorrelationFourThirds →
      ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀, (3 / 4 - ε) * (Zeta23.Ncount 0 T : ℝ) ≤ Zeta23.N0simple 0 T) :=
  ⟨RHTower.two_thirds_simpleCritical_epsilon,
    fun _ hB => ⟨RHTower.opt_sub_two_thirds hB, RHTower.two_thirds_lt_opt hB⟩,
    fun _ hB => RHTower.opt_ge_three_quarters_iff hB,
    RHTower.certOpt_one,
    RHTower.zeta_three_quarters_simple_of_pair_correlation⟩

/-- **Asymptotic collapse to `2/3` without pair-correlation control (`B → ∞`).** As the upper bound
`B` on the pair-correlation form factor beyond bandwidth `1` tends to `+∞`, the optimal rank–trace
proportion `certOpt B = (2B − 1)/(3B − 2)` converges down to `2/3`. -/
theorem tendsto_certOpt_atTop :
    Tendsto RHTower.certOpt atTop (𝓝 (2 / 3 : ℝ)) := by
  have h : ∀ᶠ B : ℝ in atTop, RHTower.certOpt B = 2 / 3 + 1 / (3 * (3 * B - 2)) := by
    filter_upwards [eventually_gt_atTop (2 / 3 : ℝ)] with B hB
    linarith [RHTower.opt_sub_two_thirds hB]
  have h1 : Tendsto (fun B : ℝ => 3 * (3 * B - 2)) atTop atTop :=
    ((tendsto_id.const_mul_atTop (by norm_num : (0 : ℝ) < 3)).atTop_add tendsto_const_nhds).const_mul_atTop
      (by norm_num : (0 : ℝ) < 3)
  have h2 : Tendsto (fun B : ℝ => (2 / 3 : ℝ) + 1 / (3 * (3 * B - 2))) atTop (𝓝 ((2 / 3 : ℝ) + 0)) :=
    tendsto_const_nhds.add (tendsto_const_nhds.div_atTop h1)
  rw [add_zero] at h2
  exact h2.congr' (h.mono fun _ hB => hB.symm)

end GaloisForLFunctions.ArithmeticCastelnuovoSeveri
