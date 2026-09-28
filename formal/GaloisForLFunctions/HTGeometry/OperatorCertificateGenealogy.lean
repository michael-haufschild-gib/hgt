import GaloisForLFunctions.HTGeometry.CertificatePolarGenealogy

/-!
# Operator-certificate semantic--lineage fusion, unitary gauge and polar energy

Operator-valued conservative repairs on a `d`-dimensional fibre `V = ℂ^d`: invertible certificate
matrices `C_n` (card's `C_{n+1}`), prefix transports `A_0 = 1`, `A_{n+1} = A_n C_n` (OP.4), the
finite genealogy `(G_N x)_n = x_n - C_n x_{n+1}` (OP.5), the semantic packet
`B_N x = ∑ A_n x_n` (OP.6) and the lineage packet `(Q_N v)_n = A_n⁻¹ v` (OP.7).

* **Theorem 2.1:** `G_N` is unitriangular and invertible, `B_N G_N = π₀` (OP.8),
  `G_N Q_N v = (0, …, 0, A_N⁻¹ v)` (OP.9) and `B_N Q_N = (N+1) I` (OP.10).
* **Theorem 3.1:** with Hilbert--Schmidt energies `E_sem = ∑ ‖A_n‖²`, `E_lin = ∑ ‖A_n⁻¹‖²`,
  `E_sem E_lin ≥ d² (N+1)²` (OP.13), with equality exactly when every `A_n` (equivalently every
  certificate) is unitary.
* **Theorem 4.1:** local unitary repair gauges `C'_n = U_n C_n U_{n+1}^*` transport
  `A'_n = U_0 A_n U_n^*` (OP.16), intertwine the genealogies and packets (OP.17)–(OP.18) and leave
  both energies, the uncertainty defect and the equality chamber invariant.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

open Matrix
open scoped InnerProductSpace

variable {d : ℕ}

/-- Prefix transports `A_0 = 1`, `A_{n+1} = A_n C_n` (OP.4). -/
def opPrefix (C : ℕ → Matrix (Fin d) (Fin d) ℂ) : ℕ → Matrix (Fin d) (Fin d) ℂ
  | 0 => 1
  | n + 1 => opPrefix C n * C n

@[simp] theorem opPrefix_zero (C : ℕ → Matrix (Fin d) (Fin d) ℂ) : opPrefix C 0 = 1 := rfl

theorem opPrefix_succ (C : ℕ → Matrix (Fin d) (Fin d) ℂ) (n : ℕ) :
    opPrefix C (n + 1) = opPrefix C n * C n := rfl

section Finite

variable {C : ℕ → Matrix (Fin d) (Fin d) ℂ} (hC : ∀ n, IsUnit (C n))
include hC

theorem opPrefix_isUnit (n : ℕ) : IsUnit (opPrefix C n) := by
  induction n with
  | zero => exact isUnit_one
  | succ n ih => rw [opPrefix_succ]; exact ih.mul (hC n)

theorem opPrefix_mul_inv (n : ℕ) : opPrefix C n * (opPrefix C n)⁻¹ = 1 :=
  Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).mp (opPrefix_isUnit hC n))

theorem opPrefix_inv_mul (n : ℕ) : (opPrefix C n)⁻¹ * opPrefix C n = 1 :=
  Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).mp (opPrefix_isUnit hC n))

/-- `C_n A_{n+1}⁻¹ = A_n⁻¹`. -/
theorem mul_opPrefix_inv_succ (n : ℕ) : C n * (opPrefix C (n + 1))⁻¹ = (opPrefix C n)⁻¹ := by
  rw [opPrefix_succ, Matrix.mul_inv_rev, ← Matrix.mul_assoc,
    Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).mp (hC n)), Matrix.one_mul]

end Finite

/-- The finite operator genealogy `(G_N x)_n = x_n - C_n x_{n+1}` (OP.5). -/
def opFiniteGenealogy (C : ℕ → Matrix (Fin d) (Fin d) ℂ) (N : ℕ) :
    (Fin (N + 1) → Fin d → ℂ) →ₗ[ℂ] (Fin (N + 1) → Fin d → ℂ) where
  toFun x m := x m - if h : (m : ℕ) < N then C m *ᵥ x ⟨m + 1, by omega⟩ else 0
  map_add' x y := by
    funext m; simp only [Pi.add_apply]; split_ifs
    · simp only [Matrix.mulVec_add]; abel
    · simp
  map_smul' r x := by
    funext m; simp only [Pi.smul_apply, RingHom.id_apply]; split_ifs
    · simp [Matrix.mulVec_smul, smul_sub]
    · simp

theorem opFiniteGenealogy_apply (C : ℕ → Matrix (Fin d) (Fin d) ℂ) (N : ℕ)
    (x : Fin (N + 1) → Fin d → ℂ) (m : Fin (N + 1)) :
    opFiniteGenealogy C N x m =
      x m - if h : (m : ℕ) < N then C m *ᵥ x ⟨m + 1, by omega⟩ else 0 := rfl

/-- The strictly upper-triangular part `W_N = 1 - G_N`. -/
def opFiniteWeight (C : ℕ → Matrix (Fin d) (Fin d) ℂ) (N : ℕ) :
    (Fin (N + 1) → Fin d → ℂ) →ₗ[ℂ] (Fin (N + 1) → Fin d → ℂ) :=
  LinearMap.id - opFiniteGenealogy C N

theorem opFiniteWeight_apply (C : ℕ → Matrix (Fin d) (Fin d) ℂ) (N : ℕ)
    (x : Fin (N + 1) → Fin d → ℂ) (m : Fin (N + 1)) :
    opFiniteWeight C N x m = if h : (m : ℕ) < N then C m *ᵥ x ⟨m + 1, by omega⟩ else 0 := by
  show x m - (x m - _) = _
  abel

theorem opFiniteWeight_pow_apply_eq_zero (C : ℕ → Matrix (Fin d) (Fin d) ℂ) (N k : ℕ)
    (x : Fin (N + 1) → Fin d → ℂ) (m : Fin (N + 1)) (hk : N < (m : ℕ) + k) :
    (opFiniteWeight C N ^ k) x m = 0 := by
  induction k generalizing m with
  | zero => omega
  | succ k ih =>
      rw [pow_succ', Module.End.mul_apply, opFiniteWeight_apply]
      split_ifs with h
      · rw [ih ⟨m + 1, by omega⟩ (by simp; omega), Matrix.mulVec_zero]
      · rfl

/-- **Theorem 2.1(1)** `G_N` is invertible (unitriangular). -/
theorem opFiniteGenealogy_isUnit (C : ℕ → Matrix (Fin d) (Fin d) ℂ) (N : ℕ) :
    IsUnit (opFiniteGenealogy C N) := by
  have hnil : IsNilpotent (opFiniteWeight C N) := by
    refine ⟨N + 1, LinearMap.ext fun x => funext fun m => ?_⟩
    rw [opFiniteWeight_pow_apply_eq_zero C N (N + 1) x m (by omega)]
    rfl
  have h := hnil.isUnit_one_sub
  have heq : (1 : Module.End ℂ (Fin (N + 1) → Fin d → ℂ)) - opFiniteWeight C N =
      opFiniteGenealogy C N := by
    rw [opFiniteWeight]; ext x m; simp
  rwa [heq] at h

/-- The semantic packet `B_N x = ∑ A_n x_n` (OP.6). -/
def opSemanticPacket (C : ℕ → Matrix (Fin d) (Fin d) ℂ) (N : ℕ)
    (x : Fin (N + 1) → Fin d → ℂ) : Fin d → ℂ :=
  ∑ m : Fin (N + 1), opPrefix C m *ᵥ x m

/-- The lineage packet `(Q_N v)_n = A_n⁻¹ v` (OP.7). -/
def opLineagePacket (C : ℕ → Matrix (Fin d) (Fin d) ℂ) (N : ℕ) (v : Fin d → ℂ) :
    Fin (N + 1) → Fin d → ℂ :=
  fun m => (opPrefix C m)⁻¹ *ᵥ v

/-- **Theorem 2.1(2)** (OP.8) Semantic conservation `B_N G_N = π₀`. -/
theorem opSemanticPacket_genealogy (C : ℕ → Matrix (Fin d) (Fin d) ℂ) (N : ℕ)
    (x : Fin (N + 1) → Fin d → ℂ) :
    opSemanticPacket C N (opFiniteGenealogy C N x) = x 0 := by
  have key : ∀ M (hM : M ≤ N), ∑ m : Fin (M + 1), opPrefix C m *ᵥ
      opFiniteGenealogy C N x ⟨m, by have := m.isLt; omega⟩ =
        x 0 - if h : M < N then opPrefix C (M + 1) *ᵥ x ⟨M + 1, by omega⟩ else 0 := by
    intro M hM
    induction M with
    | zero =>
        rw [Fin.sum_univ_one, opFiniteGenealogy_apply]
        simp only [Fin.val_zero, Fin.zero_eta, opPrefix_zero, Matrix.one_mulVec]
        split_ifs with h
        · rw [opPrefix_succ, opPrefix_zero, Matrix.one_mul]
        · rfl
    | succ M ih =>
        rw [Fin.sum_univ_castSucc]
        simp only [Fin.val_castSucc, Fin.val_last]
        rw [ih (by omega), opFiniteGenealogy_apply]
        rw [dif_pos (by omega : M < N)]
        by_cases h : M + 1 < N
        · rw [dif_pos h, dif_pos h, Matrix.mulVec_sub, Matrix.mulVec_mulVec,
            ← opPrefix_succ (n := M + 1)]
          abel
        · rw [dif_neg h, dif_neg h, Matrix.mulVec_sub, Matrix.mulVec_zero, sub_zero]
          abel
  have := key N le_rfl
  rw [dif_neg (lt_irrefl N), sub_zero] at this
  rw [← this]
  rfl

/-- **Theorem 2.1(3)** (OP.9) `G_N Q_N v = (0, …, 0, A_N⁻¹ v)`. -/
theorem opFiniteGenealogy_lineagePacket {C : ℕ → Matrix (Fin d) (Fin d) ℂ}
    (hC : ∀ n, IsUnit (C n)) (N : ℕ) (v : Fin d → ℂ) (m : Fin (N + 1)) :
    opFiniteGenealogy C N (opLineagePacket C N v) m =
      if (m : ℕ) = N then (opPrefix C N)⁻¹ *ᵥ v else 0 := by
  rw [opFiniteGenealogy_apply]
  simp only [opLineagePacket]
  by_cases h : (m : ℕ) < N
  · rw [dif_pos h, if_neg h.ne, Matrix.mulVec_mulVec, mul_opPrefix_inv_succ hC, sub_self]
  · have hmN : (m : ℕ) = N := by omega
    rw [dif_neg h, if_pos hmN, sub_zero, hmN]

/-- **Theorem 2.1(4)** (OP.10) Exact fusion `B_N Q_N = (N+1) I`. -/
theorem opSemanticPacket_lineagePacket {C : ℕ → Matrix (Fin d) (Fin d) ℂ}
    (hC : ∀ n, IsUnit (C n)) (N : ℕ) (v : Fin d → ℂ) :
    opSemanticPacket C N (opLineagePacket C N v) = ((N + 1 : ℕ) : ℂ) • v := by
  simp only [opSemanticPacket, opLineagePacket, Matrix.mulVec_mulVec, opPrefix_mul_inv hC,
    Matrix.one_mulVec, Finset.sum_const, Finset.card_univ, Fintype.card_fin]
  rw [← Nat.cast_smul_eq_nsmul ℂ]

/-! ## Theorem 3.1: sharp semantic--lineage uncertainty -/

/-- Squared Hilbert--Schmidt (Frobenius) norm of a matrix. -/
def hsSq (M : Matrix (Fin d) (Fin d) ℂ) : ℝ := ∑ i, ∑ j, ‖M i j‖ ^ 2

/-- Semantic energy `E_sem = ∑_{n ≤ N} ‖A_n‖²_HS` (OP.11). -/
def opSemanticEnergy (C : ℕ → Matrix (Fin d) (Fin d) ℂ) (N : ℕ) : ℝ :=
  ∑ m ∈ Finset.range (N + 1), hsSq (opPrefix C m)

/-- Lineage energy `E_lin = ∑_{n ≤ N} ‖A_n⁻¹‖²_HS` (OP.12). -/
def opLineageEnergy (C : ℕ → Matrix (Fin d) (Fin d) ℂ) (N : ℕ) : ℝ :=
  ∑ m ∈ Finset.range (N + 1), hsSq (opPrefix C m)⁻¹

/-- The flattened semantic packet `(n, i, j) ↦ (A_nᴴ)_{ij}`. -/
def semanticVector (C : ℕ → Matrix (Fin d) (Fin d) ℂ) (N : ℕ) :
    EuclideanSpace ℂ (Fin (N + 1) × Fin d × Fin d) :=
  WithLp.toLp 2 fun p => star (opPrefix C p.1 p.2.2 p.2.1)

/-- The flattened lineage packet `(n, i, j) ↦ (A_n⁻¹)_{ij}`. -/
def lineageVector (C : ℕ → Matrix (Fin d) (Fin d) ℂ) (N : ℕ) :
    EuclideanSpace ℂ (Fin (N + 1) × Fin d × Fin d) :=
  WithLp.toLp 2 fun p => (opPrefix C p.1)⁻¹ p.2.1 p.2.2

theorem sum_fin_range {N : ℕ} (f : ℕ → ℝ) :
    ∑ m : Fin (N + 1), f m = ∑ m ∈ Finset.range (N + 1), f m :=
  Fin.sum_univ_eq_sum_range f (N + 1)

theorem norm_sq_semanticVector (C : ℕ → Matrix (Fin d) (Fin d) ℂ) (N : ℕ) :
    ‖semanticVector C N‖ ^ 2 = opSemanticEnergy C N := by
  rw [EuclideanSpace.norm_eq, Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _),
    opSemanticEnergy, ← sum_fin_range]
  simp only [semanticVector, Fintype.sum_prod_type, norm_star]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [hsSq, Finset.sum_comm]

theorem norm_sq_lineageVector (C : ℕ → Matrix (Fin d) (Fin d) ℂ) (N : ℕ) :
    ‖lineageVector C N‖ ^ 2 = opLineageEnergy C N := by
  rw [EuclideanSpace.norm_eq, Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _),
    opLineageEnergy, ← sum_fin_range]
  simp only [lineageVector, Fintype.sum_prod_type]
  rfl

/-- **(OP.14)** `⟨B_N^*, Q_N⟩_HS = tr(B_N Q_N) = d (N+1)`. -/
theorem inner_semanticVector_lineageVector {C : ℕ → Matrix (Fin d) (Fin d) ℂ}
    (hC : ∀ n, IsUnit (C n)) (N : ℕ) :
    ⟪semanticVector C N, lineageVector C N⟫_ℂ = ((d * (N + 1) : ℕ) : ℂ) := by
  rw [PiLp.inner_apply]
  simp only [semanticVector, lineageVector, Fintype.sum_prod_type, RCLike.inner_apply,
    starRingEnd_apply, star_star]
  have hm : ∀ m : Fin (N + 1), ∑ i : Fin d, ∑ j : Fin d,
      (opPrefix C m)⁻¹ i j * opPrefix C m j i = (d : ℂ) := by
    intro m
    have htr := congrArg Matrix.trace (opPrefix_mul_inv hC m)
    rw [Matrix.trace_one, Fintype.card_fin] at htr
    rw [← htr, Matrix.trace]
    simp only [Matrix.diag, Matrix.mul_apply]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    ring
  rw [Finset.sum_congr rfl fun m _ => hm m, Finset.sum_const, Finset.card_univ, Fintype.card_fin]
  push_cast
  ring

/-- **Theorem 3.1** (OP.13) `E_sem E_lin ≥ d² (N+1)²`. -/
theorem opPolar_uncertainty {C : ℕ → Matrix (Fin d) (Fin d) ℂ} (hC : ∀ n, IsUnit (C n))
    (N : ℕ) :
    ((d * (N + 1) : ℕ) : ℝ) ^ 2 ≤ opSemanticEnergy C N * opLineageEnergy C N := by
  have hcs := norm_inner_le_norm (𝕜 := ℂ) (semanticVector C N) (lineageVector C N)
  rw [inner_semanticVector_lineageVector hC, Complex.norm_natCast] at hcs
  rw [← norm_sq_semanticVector, ← norm_sq_lineageVector, ← mul_pow]
  exact pow_le_pow_left₀ (Nat.cast_nonneg _) hcs 2

theorem opPrefix_eq_star_iff_unitary (A : Matrix (Fin d) (Fin d) ℂ) (hA : IsUnit A) :
    A⁻¹ = star A ↔ A ∈ Matrix.unitaryGroup (Fin d) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff]
  constructor
  · intro h; rw [← h]; exact Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).mp hA)
  · intro h; exact Matrix.inv_eq_right_inv h

/-- **Theorem 3.1, equality chamber:** for `d ≥ 1`, equality in (OP.13) holds exactly when every
prefix transport is unitary. -/
theorem opPolar_uncertainty_eq_iff {C : ℕ → Matrix (Fin d) (Fin d) ℂ} (hC : ∀ n, IsUnit (C n))
    (hd : 0 < d) (N : ℕ) :
    opSemanticEnergy C N * opLineageEnergy C N = ((d * (N + 1) : ℕ) : ℝ) ^ 2 ↔
      ∀ m ≤ N, opPrefix C m ∈ Matrix.unitaryGroup (Fin d) ℂ := by
  set X := semanticVector C N with hXdef
  set Y := lineageVector C N with hYdef
  have hinner : ⟪X, Y⟫_ℂ = ((d * (N + 1) : ℕ) : ℂ) := inner_semanticVector_lineageVector hC N
  let i0 : Fin d := ⟨0, hd⟩
  let p0 : Fin (N + 1) × Fin d × Fin d := (0, i0, i0)
  have hX0 : X p0 = 1 := by
    show star (opPrefix C (0 : Fin (N + 1)) i0 i0) = 1
    simp
  have hY0 : Y p0 = 1 := by
    show (opPrefix C (0 : Fin (N + 1)))⁻¹ i0 i0 = 1
    simp
  have hXne : X ≠ 0 := fun h => by
    have := congrArg (fun z : EuclideanSpace ℂ _ => z p0) h
    simp [hX0] at this
  have hYne : Y ≠ 0 := fun h => by
    have := congrArg (fun z : EuclideanSpace ℂ _ => z p0) h
    simp [hY0] at this
  constructor
  · intro heq m hm
    have hprod : ‖X‖ * ‖Y‖ = ((d * (N + 1) : ℕ) : ℝ) := by
      have h2 : (‖X‖ * ‖Y‖) ^ 2 = ((d * (N + 1) : ℕ) : ℝ) ^ 2 := by
        rw [mul_pow, norm_sq_semanticVector, norm_sq_lineageVector, heq]
      exact (pow_left_inj₀ (by positivity) (Nat.cast_nonneg _) two_ne_zero).mp h2
    have hnorm : ‖⟪X, Y⟫_ℂ‖ = ‖X‖ * ‖Y‖ := by
      rw [hinner, Complex.norm_natCast, hprod]
    obtain ⟨r, -, hr⟩ := (norm_inner_eq_norm_iff hXne hYne).mp hnorm
    have hr1 : r = 1 := by
      have := congrArg (fun z : EuclideanSpace ℂ _ => z p0) hr
      simp only [PiLp.smul_apply, smul_eq_mul] at this
      rw [hY0, hX0, mul_one] at this
      exact this.symm
    rw [hr1, one_smul] at hr
    rw [← opPrefix_eq_star_iff_unitary _ (opPrefix_isUnit hC m)]
    ext i j
    have := congrArg (fun z : EuclideanSpace ℂ _ => z (⟨m, Nat.lt_succ_of_le hm⟩, i, j)) hr
    simpa [X, Y, semanticVector, lineageVector, Matrix.star_apply] using this
  · intro hunit
    have hXY : Y = X := by
      ext p
      have hmem := hunit p.1 (Nat.lt_succ_iff.mp p.1.isLt)
      rw [← opPrefix_eq_star_iff_unitary _ (opPrefix_isUnit hC p.1)] at hmem
      show (opPrefix C p.1)⁻¹ p.2.1 p.2.2 = star (opPrefix C p.1 p.2.2 p.2.1)
      rw [hmem, Matrix.star_apply]
    have hself : ‖X‖ ^ 2 = ((d * (N + 1) : ℕ) : ℝ) := by
      have h := hinner
      rw [hXY, inner_self_eq_norm_sq_to_K] at h
      have h' : ((‖X‖ ^ 2 : ℝ) : ℂ) = (((d * (N + 1) : ℕ) : ℝ) : ℂ) := by
        rw [Complex.ofReal_pow]; push_cast at h ⊢; exact h
      exact Complex.ofReal_injective h'
    rw [← norm_sq_semanticVector, ← norm_sq_lineageVector, ← hXdef, ← hYdef, hXY, hself, sq]

/-- Unitary prefix transports are exactly unitary certificates. -/
theorem opPrefix_unitary_iff {C : ℕ → Matrix (Fin d) (Fin d) ℂ} (N : ℕ) :
    (∀ m ≤ N, opPrefix C m ∈ Matrix.unitaryGroup (Fin d) ℂ) ↔
      ∀ n < N, C n ∈ Matrix.unitaryGroup (Fin d) ℂ := by
  constructor
  · intro h n hn
    have h1 := h n hn.le
    have h2 := h (n + 1) hn
    rw [opPrefix_succ] at h2
    have : C n = star (opPrefix C n) * (opPrefix C n * C n) := by
      rw [← Matrix.mul_assoc, (Matrix.mem_unitaryGroup_iff'.mp h1), Matrix.one_mul]
    rw [this]
    exact Submonoid.mul_mem _ (Unitary.star_mem h1) h2
  · intro h m hm
    induction m with
    | zero => exact Submonoid.one_mem _
    | succ m ih =>
        rw [opPrefix_succ]
        exact Submonoid.mul_mem _ (ih (by omega)) (h m (by omega))

/-! ## Theorem 4.1: repair gauges and invariant work -/

section Gauge

variable (U : ℕ → Matrix (Fin d) (Fin d) ℂ) (hU : ∀ n, U n ∈ Matrix.unitaryGroup (Fin d) ℂ)

/-- **(OP.15)** Gauge-transformed certificates `C'_n = U_n C_n U_{n+1}^*`. -/
def gaugeCert (C : ℕ → Matrix (Fin d) (Fin d) ℂ) : ℕ → Matrix (Fin d) (Fin d) ℂ :=
  fun n => U n * C n * star (U (n + 1))

include hU

theorem unitary_mul_star (n : ℕ) : U n * star (U n) = 1 := Matrix.mem_unitaryGroup_iff.mp (hU n)

theorem star_mul_unitary (n : ℕ) : star (U n) * U n = 1 := Matrix.mem_unitaryGroup_iff'.mp (hU n)

/-- **(OP.16)** `A'_n = U_0 A_n U_n^*`. -/
theorem opPrefix_gaugeCert (C : ℕ → Matrix (Fin d) (Fin d) ℂ) (n : ℕ) :
    opPrefix (gaugeCert U C) n = U 0 * opPrefix C n * star (U n) := by
  induction n with
  | zero => rw [opPrefix_zero, opPrefix_zero, Matrix.mul_one, unitary_mul_star U hU 0]
  | succ n ih =>
      rw [opPrefix_succ, ih, opPrefix_succ, gaugeCert]
      calc U 0 * opPrefix C n * star (U n) * (U n * C n * star (U (n + 1)))
          = U 0 * opPrefix C n * (star (U n) * U n) * C n * star (U (n + 1)) := by
            simp only [Matrix.mul_assoc]
        _ = U 0 * (opPrefix C n * C n) * star (U (n + 1)) := by
            rw [star_mul_unitary U hU n, Matrix.mul_one]; simp only [Matrix.mul_assoc]

theorem gaugeCert_isUnit {C : ℕ → Matrix (Fin d) (Fin d) ℂ} (hC : ∀ n, IsUnit (C n)) (n : ℕ) :
    IsUnit (gaugeCert U C n) := by
  have h1 : IsUnit (U n) := (Matrix.isUnit_iff_isUnit_det _).mpr
    (Matrix.isUnit_det_of_right_inverse (unitary_mul_star U hU n))
  have h2 : IsUnit (star (U (n + 1))) := (Matrix.isUnit_iff_isUnit_det _).mpr
    (Matrix.isUnit_det_of_left_inverse (unitary_mul_star U hU (n + 1)))
  exact (h1.mul (hC n)).mul h2

omit hU in
theorem hsSq_eq_re_trace (M : Matrix (Fin d) (Fin d) ℂ) :
    hsSq M = (Matrix.trace (star M * M)).re := by
  rw [hsSq, Matrix.trace]
  simp only [Matrix.diag, Matrix.mul_apply, Matrix.star_apply, Complex.re_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [RCLike.star_def, ← Complex.normSq_eq_conj_mul_self, Complex.ofReal_re,
    Complex.normSq_eq_norm_sq]

/-- Hilbert--Schmidt energy is invariant under unitary left and right frames. -/
theorem hsSq_unitary_mul_star (i j : ℕ) (M : Matrix (Fin d) (Fin d) ℂ) :
    hsSq (U i * M * star (U j)) = hsSq M := by
  rw [hsSq_eq_re_trace, hsSq_eq_re_trace]
  congr 1
  rw [star_mul, star_mul, star_star]
  calc Matrix.trace (U j * (star M * star (U i)) * (U i * M * star (U j)))
      = Matrix.trace (U j * (star M * (star (U i) * U i) * M) * star (U j)) := by
        simp only [Matrix.mul_assoc]
    _ = Matrix.trace (star (U j) * (U j * (star M * M))) := by
        rw [star_mul_unitary U hU i, Matrix.mul_one, Matrix.trace_mul_comm]
    _ = Matrix.trace (star M * M) := by
        rw [← Matrix.mul_assoc, star_mul_unitary U hU j, Matrix.one_mul]

theorem inv_gauge (i j : ℕ) {M : Matrix (Fin d) (Fin d) ℂ} (hM : IsUnit M) :
    (U i * M * star (U j))⁻¹ = U j * M⁻¹ * star (U i) := by
  apply Matrix.inv_eq_right_inv
  calc U i * M * star (U j) * (U j * M⁻¹ * star (U i))
      = U i * M * (star (U j) * U j) * M⁻¹ * star (U i) := by simp only [Matrix.mul_assoc]
    _ = U i * (M * M⁻¹) * star (U i) := by
        rw [star_mul_unitary U hU j, Matrix.mul_one]; simp only [Matrix.mul_assoc]
    _ = 1 := by
        rw [Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).mp hM), Matrix.mul_one,
          unitary_mul_star U hU i]

/-- **Theorem 4.1** Both polar energies are gauge invariant. -/
theorem opSemanticEnergy_gauge (C : ℕ → Matrix (Fin d) (Fin d) ℂ) (N : ℕ) :
    opSemanticEnergy (gaugeCert U C) N = opSemanticEnergy C N := by
  unfold opSemanticEnergy
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [opPrefix_gaugeCert U hU, hsSq_unitary_mul_star U hU]

theorem opLineageEnergy_gauge {C : ℕ → Matrix (Fin d) (Fin d) ℂ} (hC : ∀ n, IsUnit (C n))
    (N : ℕ) : opLineageEnergy (gaugeCert U C) N = opLineageEnergy C N := by
  unfold opLineageEnergy
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [opPrefix_gaugeCert U hU, inv_gauge U hU _ _ (opPrefix_isUnit hC m),
    hsSq_unitary_mul_star U hU]

/-- **(OP.19)** The uncertainty defect is gauge invariant. -/
theorem opUncertaintyDefect_gauge {C : ℕ → Matrix (Fin d) (Fin d) ℂ} (hC : ∀ n, IsUnit (C n))
    (N : ℕ) :
    opSemanticEnergy (gaugeCert U C) N * opLineageEnergy (gaugeCert U C) N -
        ((d * (N + 1) : ℕ) : ℝ) ^ 2 =
      opSemanticEnergy C N * opLineageEnergy C N - ((d * (N + 1) : ℕ) : ℝ) ^ 2 := by
  rw [opSemanticEnergy_gauge U hU, opLineageEnergy_gauge U hU hC]

/-- The equality chamber is gauge invariant. -/
theorem opPrefix_unitary_gauge_iff (C : ℕ → Matrix (Fin d) (Fin d) ℂ) (n : ℕ) :
    opPrefix (gaugeCert U C) n ∈ Matrix.unitaryGroup (Fin d) ℂ ↔
      opPrefix C n ∈ Matrix.unitaryGroup (Fin d) ℂ := by
  rw [opPrefix_gaugeCert U hU]
  constructor
  · intro h
    have : opPrefix C n = star (U 0) * (U 0 * opPrefix C n * star (U n)) * U n := by
      simp only [← Matrix.mul_assoc, star_mul_unitary U hU 0, Matrix.one_mul]
      rw [Matrix.mul_assoc, star_mul_unitary U hU n, Matrix.mul_one]
    rw [this]
    exact Submonoid.mul_mem _ (Submonoid.mul_mem _ (Unitary.star_mem (hU 0)) h) (hU n)
  · intro h
    exact Submonoid.mul_mem _ (Submonoid.mul_mem _ (hU 0) h) (Unitary.star_mem (hU n))

/-- The block-diagonal frame `D_U x = (U_n x_n)`. -/
def frameDiag (N : ℕ) (x : Fin (N + 1) → Fin d → ℂ) : Fin (N + 1) → Fin d → ℂ :=
  fun m => U m *ᵥ x m

/-- **(OP.17)** `G'_N D_U = D_U G_N`. -/
theorem opFiniteGenealogy_gauge (C : ℕ → Matrix (Fin d) (Fin d) ℂ) (N : ℕ)
    (x : Fin (N + 1) → Fin d → ℂ) :
    opFiniteGenealogy (gaugeCert U C) N (frameDiag U N x) =
      frameDiag U N (opFiniteGenealogy C N x) := by
  funext m
  simp only [frameDiag, opFiniteGenealogy_apply]
  split_ifs with h
  · rw [Matrix.mulVec_sub, gaugeCert, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]
    congr 2
    simp only [Matrix.mul_assoc]
    rw [star_mul_unitary U hU, Matrix.mul_one]
  · rw [sub_zero, sub_zero]

/-- **(OP.18)** `B'_N D_U = U_0 B_N`. -/
theorem opSemanticPacket_gauge (C : ℕ → Matrix (Fin d) (Fin d) ℂ) (N : ℕ)
    (x : Fin (N + 1) → Fin d → ℂ) :
    opSemanticPacket (gaugeCert U C) N (frameDiag U N x) = U 0 *ᵥ opSemanticPacket C N x := by
  simp only [opSemanticPacket, frameDiag, Matrix.mulVec_sum, Matrix.mulVec_mulVec]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [opPrefix_gaugeCert U hU]
  congr 1
  simp only [Matrix.mul_assoc]
  rw [star_mul_unitary U hU, Matrix.mul_one]

/-- **(OP.18)** `D_U^* Q'_N U_0 = Q_N`. -/
theorem opLineagePacket_gauge {C : ℕ → Matrix (Fin d) (Fin d) ℂ} (hC : ∀ n, IsUnit (C n))
    (N : ℕ) (v : Fin d → ℂ) (m : Fin (N + 1)) :
    star (U m) *ᵥ opLineagePacket (gaugeCert U C) N (U 0 *ᵥ v) m = opLineagePacket C N v m := by
  simp only [opLineagePacket, Matrix.mulVec_mulVec]
  rw [opPrefix_gaugeCert U hU, inv_gauge U hU _ _ (opPrefix_isUnit hC m)]
  congr 1
  simp only [← Matrix.mul_assoc]
  rw [star_mul_unitary U hU, Matrix.one_mul, Matrix.mul_assoc, star_mul_unitary U hU,
    Matrix.mul_one]

end Gauge

end

end GaloisForLFunctions.HTGeometry
