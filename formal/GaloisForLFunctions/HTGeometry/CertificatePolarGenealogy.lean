import GaloisForLFunctions.HTGeometry.UnitriangularRepairGenealogyCofinal
import GaloisForLFunctions.HTGeometry.DiagonalEllTwoIndexed
import GaloisForLFunctions.HTGeometry.DiagonalCompactOperator

/-!
# Nonstationary certificate-polar genealogy: uncertainty, admission, critical mirage, dichotomy

A positive bounded certificate stream `a_{n+1} = c n` (`0 < c n ≤ M`) declares the repairs
`e_{n+1} ∼ a_{n+1} e_n`.  Its semantic and lineage profiles are the prefix products
`A_n = ∏_{j<n} c j` and their reciprocals `Q_n = A_n⁻¹` (CP.3).

* **Finite law** (Theorem 2.1): the finite genealogy `G_N = 1 - W_N` on `ℂ^{N+1}` is unitriangular
  and invertible, `b_N G_N = π₀` (CP.6), `G_N q_N = Q_N e_N` with `q_N` the unique normalized interior
  lineage (CP.7), and the sharp polar uncertainty `(∑ A_n²)(∑ Q_n²) ≥ (N+1)²` (CP.8) holds with
  equality exactly for balanced certificates (CP.9).
* **Cofinal admission** (Theorem 3.1): on `ℓ²(ℕ)`, `b G x = x₀`; `b` extends continuously iff
  `A ∈ ℓ²`; `ker G` is `0` or `ℂ Q` according as `Q ∉ ℓ²` or `Q ∈ ℓ²`; the range is always dense;
  the two polar admissions exclude each other; `max(‖b_N‖, ‖q_N‖) ≥ √(N+1)`.
* **Critical mirage** (Theorem 4.1), **exponential-dichotomy chambers** (Theorem 5.1) and the
  **functional-equation polarity** `a ↦ a⁻¹` (§6).
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

open Filter Topology ContinuousLinearMap
open scoped InnerProductSpace ENNReal

/-! ## Polar profiles -/

/-- Semantic profile `A_n = ∏_{j<n} c j` (CP.3). -/
def certProd (c : ℕ → ℝ) (n : ℕ) : ℝ := ∏ j ∈ Finset.range n, c j

/-- Lineage profile `Q_n = A_n⁻¹` (CP.3). -/
def certRecip (c : ℕ → ℝ) (n : ℕ) : ℝ := (certProd c n)⁻¹

@[simp] theorem certProd_zero (c : ℕ → ℝ) : certProd c 0 = 1 := by simp [certProd]

@[simp] theorem certRecip_zero (c : ℕ → ℝ) : certRecip c 0 = 1 := by simp [certRecip]

theorem certProd_succ (c : ℕ → ℝ) (n : ℕ) : certProd c (n + 1) = certProd c n * c n := by
  rw [certProd, Finset.prod_range_succ]; rfl

theorem certProd_pos {c : ℕ → ℝ} (hc : ∀ n, 0 < c n) (n : ℕ) : 0 < certProd c n :=
  Finset.prod_pos fun j _ => hc j

theorem certRecip_pos {c : ℕ → ℝ} (hc : ∀ n, 0 < c n) (n : ℕ) : 0 < certRecip c n :=
  inv_pos.mpr (certProd_pos hc n)

theorem certProd_mul_certRecip {c : ℕ → ℝ} (hc : ∀ n, 0 < c n) (n : ℕ) :
    certProd c n * certRecip c n = 1 :=
  mul_inv_cancel₀ (certProd_pos hc n).ne'

/-- `a_{n+1} Q_{n+1} = Q_n`. -/
theorem certRecip_succ {c : ℕ → ℝ} (hc : ∀ n, 0 < c n) (n : ℕ) :
    c n * certRecip c (n + 1) = certRecip c n := by
  rw [certRecip, certRecip, certProd_succ, mul_inv, ← mul_assoc, mul_comm (c n),
    mul_assoc, mul_inv_cancel₀ (hc n).ne', mul_one]

/-- **(§6) Functional-equation polarity:** certificate inversion exchanges `A` and `Q`. -/
theorem certProd_inv (c : ℕ → ℝ) (n : ℕ) : certProd (fun j => (c j)⁻¹) n = certRecip c n := by
  rw [certRecip, certProd, certProd, Finset.prod_inv_distrib]

theorem certRecip_inv (c : ℕ → ℝ) (n : ℕ) : certRecip (fun j => (c j)⁻¹) n = certProd c n := by
  rw [certRecip, certProd_inv, certRecip, inv_inv]

/-! ## Theorem 2.1: finite formation and sharp polar conservation -/

/-- **(CP.8)** Sharp polar uncertainty `(∑ A_n²)(∑ Q_n²) ≥ (N+1)²`. -/
theorem certPolar_uncertainty {c : ℕ → ℝ} (hc : ∀ n, 0 < c n) (N : ℕ) :
    ((N + 1 : ℕ) : ℝ) ^ 2 ≤
      (∑ n ∈ Finset.range (N + 1), certProd c n ^ 2) *
        ∑ n ∈ Finset.range (N + 1), certRecip c n ^ 2 := by
  have h := Finset.sum_mul_sq_le_sq_mul_sq (Finset.range (N + 1)) (certProd c) (certRecip c)
  have hone : ∑ n ∈ Finset.range (N + 1), certProd c n * certRecip c n = ((N + 1 : ℕ) : ℝ) := by
    rw [Finset.sum_congr rfl fun n _ => certProd_mul_certRecip hc n]
    simp
  rw [hone] at h
  exact h

/-- Lagrange identity for the polar packets. -/
theorem certPolar_lagrange {c : ℕ → ℝ} (hc : ∀ n, 0 < c n) (N : ℕ) :
    2 * ((∑ n ∈ Finset.range (N + 1), certProd c n ^ 2) *
        (∑ n ∈ Finset.range (N + 1), certRecip c n ^ 2) - ((N + 1 : ℕ) : ℝ) ^ 2) =
      ∑ i ∈ Finset.range (N + 1), ∑ j ∈ Finset.range (N + 1),
        (certProd c i * certRecip c j - certProd c j * certRecip c i) ^ 2 := by
  have hone : ∀ n, certProd c n * certRecip c n = 1 := certProd_mul_certRecip hc
  have hN : ((N + 1 : ℕ) : ℝ) = ∑ n ∈ Finset.range (N + 1), certProd c n * certRecip c n := by
    rw [Finset.sum_congr rfl fun n _ => hone n]; simp
  rw [hN, sq (∑ n ∈ Finset.range (N + 1), certProd c n * certRecip c n), Finset.sum_mul_sum,
    Finset.sum_mul_sum]
  have hexp : ∀ i j, (certProd c i * certRecip c j - certProd c j * certRecip c i) ^ 2 =
      certProd c i ^ 2 * certRecip c j ^ 2 + certProd c j ^ 2 * certRecip c i ^ 2 -
        2 * (certProd c i * certRecip c i * (certProd c j * certRecip c j)) := fun i j => by ring
  simp_rw [hexp, Finset.sum_sub_distrib, Finset.sum_add_distrib]
  rw [Finset.sum_comm (f := fun i j => certProd c j ^ 2 * certRecip c i ^ 2)]
  have h2 : ∑ i ∈ Finset.range (N + 1), ∑ j ∈ Finset.range (N + 1),
      2 * (certProd c i * certRecip c i * (certProd c j * certRecip c j)) =
      2 * ∑ i ∈ Finset.range (N + 1), ∑ j ∈ Finset.range (N + 1),
        certProd c i * certRecip c i * (certProd c j * certRecip c j) := by
    simp_rw [Finset.mul_sum]
  rw [h2]
  ring

/-- **(CP.9)** Equality in the polar uncertainty holds exactly for balanced certificates. -/
theorem certPolar_uncertainty_eq_iff {c : ℕ → ℝ} (hc : ∀ n, 0 < c n) (N : ℕ) :
    (∑ n ∈ Finset.range (N + 1), certProd c n ^ 2) *
        (∑ n ∈ Finset.range (N + 1), certRecip c n ^ 2) = ((N + 1 : ℕ) : ℝ) ^ 2 ↔
      ∀ n ≤ N, certProd c n = 1 := by
  constructor
  · intro heq n hn
    have hlag := certPolar_lagrange hc N
    rw [heq, sub_self, mul_zero] at hlag
    have hterm : ∀ i ∈ Finset.range (N + 1), ∀ j ∈ Finset.range (N + 1),
        (certProd c i * certRecip c j - certProd c j * certRecip c i) ^ 2 = 0 := by
      intro i hi j hj
      have hnonneg : ∀ i ∈ Finset.range (N + 1), 0 ≤ ∑ j ∈ Finset.range (N + 1),
          (certProd c i * certRecip c j - certProd c j * certRecip c i) ^ 2 :=
        fun i _ => Finset.sum_nonneg fun j _ => sq_nonneg _
      have hrow := (Finset.sum_eq_zero_iff_of_nonneg hnonneg).mp hlag.symm i hi
      exact (Finset.sum_eq_zero_iff_of_nonneg fun j _ => sq_nonneg _).mp hrow j hj
    have h0 := hterm n (Finset.mem_range.mpr (Nat.lt_succ_of_le hn)) 0
      (Finset.mem_range.mpr (Nat.succ_pos N))
    rw [certRecip_zero, certProd_zero, one_mul, mul_one, sq_eq_zero_iff, sub_eq_zero] at h0
    have hA := certProd_pos hc n
    have hprod := certProd_mul_certRecip hc n
    rw [← h0] at hprod
    have hsq : certProd c n ^ 2 = 1 := by rw [sq]; exact hprod
    nlinarith [sq_nonneg (certProd c n - 1)]
  · intro hbal
    have hQ : ∀ n ≤ N, certRecip c n = 1 := fun n hn => by rw [certRecip, hbal n hn, inv_one]
    have h1 : ∑ n ∈ Finset.range (N + 1), certProd c n ^ 2 =
        ∑ n ∈ Finset.range (N + 1), (1 : ℝ) := Finset.sum_congr rfl fun n hn => by
      rw [hbal n (Nat.lt_succ_iff.mp (Finset.mem_range.mp hn)), one_pow]
    have h2 : ∑ n ∈ Finset.range (N + 1), certRecip c n ^ 2 =
        ∑ n ∈ Finset.range (N + 1), (1 : ℝ) := Finset.sum_congr rfl fun n hn => by
      rw [hQ n (Nat.lt_succ_iff.mp (Finset.mem_range.mp hn)), one_pow]
    rw [h1, h2, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
    push_cast
    ring

theorem certProd_eq_one_iff (c : ℕ → ℝ) (N : ℕ) :
    (∀ n ≤ N, certProd c n = 1) ↔ ∀ j < N, c j = 1 := by
  constructor
  · intro h j hj
    have h1 := h (j + 1) hj
    rw [certProd_succ, h j hj.le, one_mul] at h1
    exact h1
  · intro h n hn
    induction n with
    | zero => simp
    | succ n ih => rw [certProd_succ, ih (by omega), h n (by omega), one_mul]

/-- The finite weighted backward certificate operator `W_N` (CP.4) on `ℂ^{N+1}`. -/
def finiteCertWeight (c : ℕ → ℝ) (N : ℕ) : (Fin (N + 1) → ℂ) →ₗ[ℂ] (Fin (N + 1) → ℂ) where
  toFun x m := if h : (m : ℕ) < N then (c m : ℂ) * x ⟨m + 1, by omega⟩ else 0
  map_add' x y := by
    funext m; simp only [Pi.add_apply]; split_ifs <;> ring
  map_smul' r x := by
    funext m; simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; split_ifs <;> ring

/-- The finite certificate genealogy `G_N = 1 - W_N` (CP.4). -/
def finiteCertGenealogy (c : ℕ → ℝ) (N : ℕ) : (Fin (N + 1) → ℂ) →ₗ[ℂ] (Fin (N + 1) → ℂ) :=
  LinearMap.id - finiteCertWeight c N

/-- **Unitriangularity:** `(G_N x)_m = x_m - a_{m+1} x_{m+1}` (and `(G_N x)_N = x_N`). -/
theorem finiteCertGenealogy_apply (c : ℕ → ℝ) (N : ℕ) (x : Fin (N + 1) → ℂ) (m : Fin (N + 1)) :
    finiteCertGenealogy c N x m =
      x m - if h : (m : ℕ) < N then (c m : ℂ) * x ⟨m + 1, by omega⟩ else 0 := rfl

theorem finiteCertWeight_pow_apply (c : ℕ → ℝ) (N k : ℕ) (x : Fin (N + 1) → ℂ)
    (m : Fin (N + 1)) :
    (finiteCertWeight c N ^ k) x m =
      if h : (m : ℕ) + k ≤ N then
        (∏ j ∈ Finset.range k, (c (m + j) : ℂ)) * x ⟨m + k, by omega⟩ else 0 := by
  induction k generalizing m with
  | zero =>
      have := m.isLt
      simp only [pow_zero, Module.End.one_apply, add_zero, Finset.range_zero, Finset.prod_empty,
        one_mul]
      rw [dif_pos (by omega)]
  | succ k ih =>
      rw [pow_succ', Module.End.mul_apply]
      change (if h : (m : ℕ) < N then (c m : ℂ) *
          ((finiteCertWeight c N ^ k) x) ⟨m + 1, by omega⟩ else 0) = _
      by_cases h1 : (m : ℕ) < N
      · rw [dif_pos h1, ih]
        by_cases h2 : (m : ℕ) + (k + 1) ≤ N
        · rw [dif_pos (by simp; omega), dif_pos h2, Finset.prod_range_succ']
          have : ∀ j ∈ Finset.range k, (c ((m : ℕ) + 1 + j) : ℂ) = c ((m : ℕ) + (j + 1)) :=
            fun j _ => by rw [add_assoc, add_comm 1 j]
          rw [Finset.prod_congr rfl this]
          have hidx : (⟨(m : ℕ) + 1 + k, by omega⟩ : Fin (N + 1)) = ⟨(m : ℕ) + (k + 1), by omega⟩ :=
            Fin.ext (by simp; omega)
          rw [hidx]
          ring_nf
        · rw [dif_neg (by simp; omega), dif_neg h2, mul_zero]
      · rw [dif_neg h1, dif_neg (by omega)]

theorem finiteCertWeight_pow_eq_zero (c : ℕ → ℝ) (N : ℕ) :
    finiteCertWeight c N ^ (N + 1) = 0 := by
  refine LinearMap.ext fun x => funext fun m => ?_
  rw [finiteCertWeight_pow_apply, dif_neg (by omega)]
  rfl

/-- **Theorem 2.1(1)** `G_N` is invertible (unitriangular with nilpotent off-diagonal part). -/
theorem finiteCertGenealogy_isUnit (c : ℕ → ℝ) (N : ℕ) : IsUnit (finiteCertGenealogy c N) :=
  IsNilpotent.isUnit_one_sub ⟨N + 1, finiteCertWeight_pow_eq_zero c N⟩

/-- **Theorem 2.1(2)** (CP.6) Semantic conservation `b_N G_N = π₀`. -/
theorem finiteCertReader_genealogy {c : ℕ → ℝ} (N : ℕ) (x : Fin (N + 1) → ℂ) :
    ∑ m : Fin (N + 1), (certProd c m : ℂ) * finiteCertGenealogy c N x m = x 0 := by
  have key : ∀ M (hM : M ≤ N), ∑ m : Fin (M + 1), (certProd c m : ℂ) *
      finiteCertGenealogy c N x ⟨m, by have := m.isLt; omega⟩ =
        x 0 - if h : M < N then (certProd c (M + 1) : ℂ) * x ⟨M + 1, by omega⟩ else 0 := by
    intro M hM
    induction M with
    | zero =>
        rw [Fin.sum_univ_one, finiteCertGenealogy_apply]
        simp only [Fin.val_zero]
        simp only [Fin.zero_eta]
        split_ifs with h
        · rw [certProd_zero, certProd_succ, certProd_zero, one_mul]; push_cast; ring
        · rw [certProd_zero]; push_cast; ring
    | succ M ih =>
        rw [Fin.sum_univ_castSucc]
        simp only [Fin.val_castSucc, Fin.val_last]
        rw [ih (by omega)]
        rw [finiteCertGenealogy_apply]
        rw [dif_pos (by omega : M < N)]
        by_cases h : M + 1 < N
        · rw [dif_pos h, dif_pos h, certProd_succ (n := M + 1)]
          push_cast
          ring
        · rw [dif_neg h, dif_neg h]
          ring
  have := key N le_rfl
  rw [dif_neg (lt_irrefl N), sub_zero] at this
  rw [← this]

/-- The finite lineage packet `q_N = (Q_0, …, Q_N)` (CP.5). -/
def finiteLineage (c : ℕ → ℝ) (N : ℕ) : Fin (N + 1) → ℂ := fun m => (certRecip c m : ℂ)

/-- **Theorem 2.1(3)** (CP.7) `G_N q_N = Q_N e_N`. -/
theorem finiteCertGenealogy_finiteLineage {c : ℕ → ℝ} (hc : ∀ n, 0 < c n) (N : ℕ)
    (m : Fin (N + 1)) :
    finiteCertGenealogy c N (finiteLineage c N) m =
      if (m : ℕ) = N then (certRecip c N : ℂ) else 0 := by
  rw [finiteCertGenealogy_apply]
  simp only [finiteLineage]
  by_cases h : (m : ℕ) < N
  · rw [dif_pos h, if_neg h.ne, ← Complex.ofReal_mul, certRecip_succ hc, sub_self]
  · have hmN : (m : ℕ) = N := by omega
    rw [dif_neg h, if_pos hmN, sub_zero, hmN]

/-- **Theorem 2.1(3)** uniqueness: the normalized interior lineage is `q_N`. -/
theorem eq_finiteLineage_of_interior {c : ℕ → ℝ} (hc : ∀ n, 0 < c n) (N : ℕ)
    (x : Fin (N + 1) → ℂ) (h0 : x 0 = 1)
    (hint : ∀ m : Fin (N + 1), (m : ℕ) < N → finiteCertGenealogy c N x m = 0) :
    x = finiteLineage c N := by
  have hrec : ∀ n (hn : n ≤ N), x ⟨n, by omega⟩ = (certRecip c n : ℂ) := by
    intro n hn
    induction n with
    | zero => simpa using h0
    | succ n ih =>
        have h := hint ⟨n, by omega⟩ (by simp; omega)
        rw [finiteCertGenealogy_apply] at h
        rw [dif_pos (show n < N by omega), ih (by omega), sub_eq_zero] at h
        have hc0 : (c n : ℂ) ≠ 0 := by exact_mod_cast (hc n).ne'
        have hQ := certRecip_succ hc n
        have hx : x ⟨n + 1, by omega⟩ = (c n : ℂ)⁻¹ * certRecip c n := by
          rw [h]; field_simp
        rw [hx, ← hQ]
        push_cast
        field_simp
  funext m
  have := hrec m (Nat.lt_succ_iff.mp m.isLt)
  simpa [finiteLineage] using this

/-! ## Cofinal certificate genealogy -/

/-- A positive bounded certificate stream (CP.1): `c n = a_{n+1}`, `0 < c n ≤ bound`. -/
structure CertStream where
  c : ℕ → ℝ
  pos : ∀ n, 0 < c n
  bound : ℝ
  le_bound : ∀ n, c n ≤ bound

namespace CertStream

variable (a : CertStream)

theorem norm_coe_le (n : ℕ) : ‖(a.c n : ℂ)‖ ≤ a.bound := by
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (a.pos n)]; exact a.le_bound n

/-- The certificate diagonal `y ↦ (c n y_n)`. -/
def diag : ToeplitzSpace →L[ℂ] ToeplitzSpace :=
  _root_.HTGeometry.ellTwoDiagonal (fun n => (a.c n : ℂ)) a.norm_coe_le

/-- The weighted backward certificate operator `(W x)_n = a_{n+1} x_{n+1}` (CP.10). -/
def weight : ToeplitzSpace →L[ℂ] ToeplitzSpace := a.diag ∘L backOp 1

theorem weight_apply (x : ToeplitzSpace) (n : ℕ) :
    (a.weight x : ℕ → ℂ) n = a.c n * (x : ℕ → ℂ) (n + 1) := by
  show (_root_.HTGeometry.ellTwoDiagonal (fun n => (a.c n : ℂ)) a.norm_coe_le (backOp 1 x)) n = _
  rw [_root_.HTGeometry.ellTwoDiagonal_apply, backOp_apply]

/-- The cofinal certificate genealogy `G = 1 - W` (CP.10). -/
def genealogy : ToeplitzSpace →L[ℂ] ToeplitzSpace := ContinuousLinearMap.id ℂ _ - a.weight

theorem genealogy_apply (x : ToeplitzSpace) (n : ℕ) :
    (a.genealogy x : ℕ → ℂ) n = (x : ℕ → ℂ) n - a.c n * (x : ℕ → ℂ) (n + 1) := by
  show ((x - a.weight x : ToeplitzSpace) : ℕ → ℂ) n = _
  rw [lp.coeFn_sub, Pi.sub_apply, weight_apply]

theorem adjoint_weight_apply_zero (y : ToeplitzSpace) :
    (adjoint a.weight y : ℕ → ℂ) 0 = 0 := by
  rw [weight, adjoint_comp, adjoint_backOp]
  exact shiftOp_one_apply_zero _

theorem adjoint_weight_apply_succ (y : ToeplitzSpace) (n : ℕ) :
    (adjoint a.weight y : ℕ → ℂ) (n + 1) = a.c n * (y : ℕ → ℂ) n := by
  rw [weight, adjoint_comp, adjoint_backOp, ContinuousLinearMap.comp_apply,
    shiftOp_one_apply_succ, diag, _root_.HTGeometry.adjoint_ellTwoDiagonal,
    _root_.HTGeometry.ellTwoDiagonal_apply,
    Complex.conj_ofReal]

/-- **Theorem 3.1(4)** The range of the certificate genealogy is always dense. -/
theorem dense_range_genealogy : Dense (Set.range a.genealogy) := by
  have hker : LinearMap.ker (adjoint a.genealogy : ToeplitzSpace →ₗ[ℂ] ToeplitzSpace) = ⊥ := by
    rw [LinearMap.ker_eq_bot']
    intro y hy
    have hy' : adjoint a.genealogy y = 0 := hy
    have hG : adjoint a.genealogy = ContinuousLinearMap.id ℂ _ - adjoint a.weight := by
      rw [genealogy, map_sub, adjoint_id]
    have hcoord : ∀ n, (y : ℕ → ℂ) n = 0 := by
      intro n
      induction n with
      | zero =>
          have := congrArg (fun z : ToeplitzSpace => (z : ℕ → ℂ) 0) hy'
          simp only [hG, FunLike.coe_sub, Pi.sub_apply, ContinuousLinearMap.id_apply,
            lp.coeFn_sub, adjoint_weight_apply_zero, sub_zero, lp.coeFn_zero,
            Pi.zero_apply] at this
          exact this
      | succ n ih =>
          have := congrArg (fun z : ToeplitzSpace => (z : ℕ → ℂ) (n + 1)) hy'
          simp only [hG, FunLike.coe_sub, Pi.sub_apply, ContinuousLinearMap.id_apply,
            lp.coeFn_sub, adjoint_weight_apply_succ, ih, mul_zero, sub_zero, lp.coeFn_zero,
            Pi.zero_apply] at this
          exact this
    ext n
    rw [hcoord n]; rfl
  have hperp : (LinearMap.range (a.genealogy : ToeplitzSpace →ₗ[ℂ] ToeplitzSpace))ᗮ = ⊥ := by
    rw [ContinuousLinearMap.orthogonal_range]; exact hker
  have hclos : (LinearMap.range
      (a.genealogy : ToeplitzSpace →ₗ[ℂ] ToeplitzSpace)).topologicalClosure = ⊤ := by
    rw [← Submodule.orthogonal_orthogonal_eq_closure, hperp, Submodule.bot_orthogonal_eq_top]
  have h := Submodule.dense_iff_topologicalClosure_eq_top.mpr hclos
  simpa [LinearMap.coe_range] using h

/-- Kernel vectors are multiples of the lineage profile. -/
theorem genealogy_eq_zero_iff (x : ToeplitzSpace) :
    a.genealogy x = 0 ↔ ∀ n, (x : ℕ → ℂ) n = (x : ℕ → ℂ) 0 * certRecip a.c n := by
  constructor
  · intro hx n
    induction n with
    | zero => simp
    | succ n ih =>
        have h := congrArg (fun y : ToeplitzSpace => (y : ℕ → ℂ) n) hx
        simp only [genealogy_apply, lp.coeFn_zero, Pi.zero_apply, sub_eq_zero] at h
        have hc0 : (a.c n : ℂ) ≠ 0 := by exact_mod_cast (a.pos n).ne'
        have hQ := certRecip_succ a.pos n
        rw [ih, ← hQ] at h
        push_cast at h
        have : (a.c n : ℂ) * ((x : ℕ → ℂ) (n + 1) - (x : ℕ → ℂ) 0 * certRecip a.c (n + 1)) = 0 := by
          linear_combination -h
        rcases mul_eq_zero.mp this with h1 | h1
        · exact absurd h1 hc0
        · exact sub_eq_zero.mp h1
  · intro hx
    ext n
    rw [genealogy_apply, hx n, hx (n + 1), lp.coeFn_zero, Pi.zero_apply]
    have hQ := certRecip_succ a.pos n
    rw [← hQ]
    push_cast
    ring

/-- **Theorem 3.1(3)** If `Q ∉ ℓ²` the completed genealogy is injective. -/
theorem ker_genealogy_eq_bot (hQ : ¬ Summable fun n => certRecip a.c n ^ 2) :
    LinearMap.ker (a.genealogy : ToeplitzSpace →ₗ[ℂ] ToeplitzSpace) = ⊥ := by
  rw [LinearMap.ker_eq_bot']
  intro x hx
  have hform := (a.genealogy_eq_zero_iff x).mp hx
  by_cases h0 : (x : ℕ → ℂ) 0 = 0
  · ext n; rw [hform n, h0, zero_mul]; rfl
  · exfalso
    apply hQ
    have hsx : Summable fun n => ‖(x : ℕ → ℂ) n‖ ^ 2 := by
      have := (lp.memℓp x).summable (by norm_num : 0 < (2 : ℝ≥0∞).toReal)
      simpa using this
    refine (hsx.div_const (‖(x : ℕ → ℂ) 0‖ ^ 2)).congr fun n => ?_
    rw [hform n, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (certRecip_pos a.pos n)]
    field_simp [norm_ne_zero_iff.mpr h0]

/-- The lineage profile as an `ℓ²` vector when `Q ∈ ℓ²`. -/
def lineage (hQ : Summable fun n => certRecip a.c n ^ 2) : ToeplitzSpace :=
  ⟨fun n => (certRecip a.c n : ℂ), memℓp_gen (by
    refine hQ.congr fun n => ?_
    simp [Complex.norm_real, abs_of_pos (certRecip_pos a.pos n)])⟩

@[simp] theorem lineage_apply (hQ : Summable fun n => certRecip a.c n ^ 2) (n : ℕ) :
    (a.lineage hQ : ℕ → ℂ) n = (certRecip a.c n : ℂ) := rfl

theorem lineage_ne_zero (hQ : Summable fun n => certRecip a.c n ^ 2) : a.lineage hQ ≠ 0 := by
  intro h
  have := congrArg (fun x : ToeplitzSpace => (x : ℕ → ℂ) 0) h
  simp at this

/-- **Theorem 3.1(3)** If `Q ∈ ℓ²` the kernel is the line `ℂ Q`. -/
theorem ker_genealogy_eq_span (hQ : Summable fun n => certRecip a.c n ^ 2) :
    LinearMap.ker (a.genealogy : ToeplitzSpace →ₗ[ℂ] ToeplitzSpace) = ℂ ∙ a.lineage hQ := by
  apply le_antisymm
  · intro x hx
    have hform := (a.genealogy_eq_zero_iff x).mp hx
    rw [Submodule.mem_span_singleton]
    refine ⟨(x : ℕ → ℂ) 0, ?_⟩
    ext n
    rw [lp.coeFn_smul, Pi.smul_apply, lineage_apply, hform n, smul_eq_mul]
  · rw [Submodule.span_le, Set.singleton_subset_iff]
    show a.genealogy (a.lineage hQ) = 0
    rw [genealogy_eq_zero_iff]
    intro n
    simp

/-- **Theorem 3.1(5)** (CP.14) The two polar admissions exclude each other. -/
theorem not_summable_both :
    ¬ ((Summable fun n => certProd a.c n ^ 2) ∧ Summable fun n => certRecip a.c n ^ 2) := by
  rintro ⟨hA, hQ⟩
  have h := (hA.mul_left 1).tendsto_atTop_zero.mul (hQ.mul_left 1).tendsto_atTop_zero
  rw [mul_zero] at h
  have hone : ∀ n, 1 * certProd a.c n ^ 2 * (1 * certRecip a.c n ^ 2) = 1 := fun n => by
    rw [one_mul, one_mul, ← mul_pow, certProd_mul_certRecip a.pos, one_pow]
  simp_rw [hone] at h
  exact one_ne_zero (tendsto_nhds_unique tendsto_const_nhds h)

/-- **Theorem 3.1(6)** (CP.15a) The larger polar packet has energy at least `N + 1`. -/
theorem le_max_polar_energy (N : ℕ) :
    ((N + 1 : ℕ) : ℝ) ≤ max (∑ n ∈ Finset.range (N + 1), certProd a.c n ^ 2)
      (∑ n ∈ Finset.range (N + 1), certRecip a.c n ^ 2) := by
  have h := certPolar_uncertainty a.pos N
  set P := ∑ n ∈ Finset.range (N + 1), certProd a.c n ^ 2
  set S := ∑ n ∈ Finset.range (N + 1), certRecip a.c n ^ 2
  have hP : 0 ≤ P := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hS : 0 ≤ S := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hm : P * S ≤ max P S ^ 2 := by
    rw [sq]
    exact mul_le_mul (le_max_left _ _) (le_max_right _ _) hS (hP.trans (le_max_left _ _))
  have hmax : 0 ≤ max P S := hP.trans (le_max_left _ _)
  nlinarith [sq_nonneg (((N + 1 : ℕ) : ℝ) - max P S), sq_nonneg (((N + 1 : ℕ) : ℝ) + max P S)]

theorem tendsto_max_polar_energy :
    Tendsto (fun N => max (∑ n ∈ Finset.range (N + 1), certProd a.c n ^ 2)
      (∑ n ∈ Finset.range (N + 1), certRecip a.c n ^ 2)) atTop atTop :=
  tendsto_atTop_mono a.le_max_polar_energy
    (tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1))

/-! ### Admission of the semantic reader -/

/-- **(CP.11)** The algebraic semantic reader `b(x) = ∑ A_n x_n` on finite histories. -/
def reader : (ℕ →₀ ℂ) →ₗ[ℂ] ℂ := Finsupp.linearCombination ℂ fun n => (certProd a.c n : ℂ)

theorem reader_eq_sum_range (l : ℕ →₀ ℂ) {N : ℕ} (hN : l.support ⊆ Finset.range N) :
    a.reader l = ∑ n ∈ Finset.range N, (certProd a.c n : ℂ) * l n := by
  rw [reader, Finsupp.linearCombination_apply, Finsupp.sum_of_support_subset l hN]
  · exact Finset.sum_congr rfl fun n _ => by rw [smul_eq_mul, mul_comm]
  · intro n _; rw [zero_smul]

theorem exists_support_subset_range (l : ℕ →₀ ℂ) : ∃ N, l.support ⊆ Finset.range N :=
  ⟨l.support.sup id + 1, fun _ hn => Finset.mem_range.mpr
    (Nat.lt_succ_of_le (Finset.le_sup (f := id) hn))⟩

/-- **Theorem 3.1(1)** `b G x = x₀` on finitely supported histories. -/
theorem reader_genealogy (l : ℕ →₀ ℂ) {N : ℕ} (hN : l.support ⊆ Finset.range N) :
    ∑ n ∈ Finset.range N, (certProd a.c n : ℂ) * (a.genealogy (finiteHistory l) : ℕ → ℂ) n =
      l 0 := by
  have hlN : l N = 0 := Finsupp.notMem_support_iff.mp fun h =>
    (Finset.mem_range.mp (hN h)).false
  simp_rw [genealogy_apply, finiteHistory_apply]
  have htel := Finset.sum_range_sub' (fun n => (certProd a.c n : ℂ) * l n) N
  rw [hlN, mul_zero, sub_zero, certProd_zero, Complex.ofReal_one, one_mul] at htel
  rw [← htel]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [certProd_succ]
  push_cast
  ring

theorem finiteHistory_single (n : ℕ) :
    finiteHistory (Finsupp.single n (1 : ℂ)) = lp.single 2 n (1 : ℂ) := by
  ext k
  rw [finiteHistory_apply, Finsupp.single_apply, lp.single_apply, Pi.single_apply]
  by_cases h : k = n
  · subst h; simp
  · rw [if_neg (Ne.symm h), if_neg h]

/-- **Theorem 3.1(2)** `b` extends continuously to `ℓ²` exactly when `A ∈ ℓ²`. -/
theorem exists_continuous_reader_iff :
    (∃ f : ToeplitzSpace →L[ℂ] ℂ, ∀ l : ℕ →₀ ℂ, f (finiteHistory l) = a.reader l) ↔
      Summable fun n => certProd a.c n ^ 2 := by
  constructor
  · rintro ⟨f, hf⟩
    set z := (InnerProductSpace.toDual ℂ ToeplitzSpace).symm f
    have hz : ∀ n, (starRingEnd ℂ) ((z : ℕ → ℂ) n) = (certProd a.c n : ℂ) := by
      intro n
      have h1 : f (lp.single 2 n (1 : ℂ)) = ⟪z, lp.single 2 n (1 : ℂ)⟫_ℂ := by
        rw [InnerProductSpace.toDual_symm_apply]
      rw [lp.inner_single_right, RCLike.inner_apply, one_mul] at h1
      have h2 := hf (Finsupp.single n 1)
      rw [finiteHistory_single, reader, Finsupp.linearCombination_single, one_smul] at h2
      rw [← h1, h2]
    have hsz : Summable fun n => ‖(z : ℕ → ℂ) n‖ ^ 2 := by
      have := (lp.memℓp z).summable (by norm_num : 0 < (2 : ℝ≥0∞).toReal)
      simpa using this
    refine hsz.congr fun n => ?_
    rw [← RCLike.norm_conj, hz n, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (certProd_pos a.pos n)]
  · intro hA
    let v : ToeplitzSpace := ⟨fun n => (certProd a.c n : ℂ), memℓp_gen (by
      refine hA.congr fun n => ?_
      simp [Complex.norm_real, abs_of_pos (certProd_pos a.pos n)])⟩
    refine ⟨innerSL ℂ v, fun l => ?_⟩
    obtain ⟨N, hN⟩ := exists_support_subset_range l
    rw [innerSL_apply_apply, lp.inner_eq_tsum, a.reader_eq_sum_range l hN,
      tsum_eq_sum (s := Finset.range N)]
    · refine Finset.sum_congr rfl fun n _ => ?_
      rw [finiteHistory_apply, RCLike.inner_apply]
      show l n * (starRingEnd ℂ) ((certProd a.c n : ℝ) : ℂ) = _
      rw [Complex.conj_ofReal, mul_comm]
    · intro n hn
      rw [finiteHistory_apply, Finsupp.notMem_support_iff.mp (fun h => hn (hN h)),
        inner_zero_right]

/-! ### Theorem 4.1: critical mirage -/

/-- Cumulative lineage energy `L_N = (∑_{n ≤ N} Q_n²)^{1/2}` (CP.16). -/
def lineageEnergy (N : ℕ) : ℝ := Real.sqrt (∑ n ∈ Finset.range (N + 1), certRecip a.c n ^ 2)

theorem lineageEnergy_sq (N : ℕ) :
    a.lineageEnergy N ^ 2 = ∑ n ∈ Finset.range (N + 1), certRecip a.c n ^ 2 :=
  Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _)

theorem one_le_lineageEnergy (N : ℕ) : 1 ≤ a.lineageEnergy N := by
  rw [lineageEnergy, Real.one_le_sqrt]
  calc (1 : ℝ) = certRecip a.c 0 ^ 2 := by simp
    _ ≤ _ := Finset.single_le_sum (f := fun n => certRecip a.c n ^ 2)
        (fun _ _ => sq_nonneg _) (Finset.mem_range.mpr (Nat.succ_pos N))

theorem lineageEnergy_pos (N : ℕ) : 0 < a.lineageEnergy N :=
  lt_of_lt_of_le one_pos (a.one_le_lineageEnergy N)

theorem tendsto_lineageEnergy (hQ : ¬ Summable fun n => certRecip a.c n ^ 2) :
    Tendsto a.lineageEnergy atTop atTop := by
  have h := (not_summable_iff_tendsto_nat_atTop_of_nonneg fun n => sq_nonneg (certRecip a.c n)).mp hQ
  have h2 : Tendsto (fun N => ∑ n ∈ Finset.range (N + 1), certRecip a.c n ^ 2) atTop atTop :=
    h.comp (tendsto_add_atTop_nat 1)
  exact Real.tendsto_sqrt_atTop.comp h2

/-- The normalized approximate lineage `u_N = L_N⁻¹ ∑_{n ≤ N} Q_n e_n` (CP.16). -/
def approxLineage (N : ℕ) : ToeplitzSpace :=
  ((a.lineageEnergy N)⁻¹ : ℂ) •
    ∑ n ∈ Finset.range (N + 1), lp.single 2 n (certRecip a.c n : ℂ)

theorem approxLineage_apply (N k : ℕ) :
    (a.approxLineage N : ℕ → ℂ) k =
      ((a.lineageEnergy N)⁻¹ : ℂ) * if k ≤ N then (certRecip a.c k : ℂ) else 0 := by
  rw [approxLineage, lp.coeFn_smul, Pi.smul_apply, lp.coeFn_sum, Finset.sum_apply, smul_eq_mul]
  congr 1
  simp only [lp.single_apply, Pi.single_apply]
  rw [Finset.sum_ite_eq]
  simp [Finset.mem_range]

theorem norm_sq_sum_single (N : ℕ) (v : ℕ → ℂ) :
    ‖∑ n ∈ Finset.range N, (lp.single 2 n (v n) : ToeplitzSpace)‖ ^ 2 =
      ∑ n ∈ Finset.range N, ‖v n‖ ^ 2 := by
  have hortho : Orthonormal ℂ fun n : ℕ => (lp.single 2 n (1 : ℂ) : ToeplitzSpace) := by
    have h := (_root_.HTGeometry.ellTwoCoordinateBasis ℕ).orthonormal
    convert h using 1
    funext n
    exact (_root_.HTGeometry.ellTwoCoordinateBasis_apply n).symm
  have := norm_sq_sum_smul_orthonormal hortho v (Finset.range N)
  rw [← this]
  congr 2
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [← lp.single_smul, smul_eq_mul, mul_one]

/-- **Theorem 4.1(1)** `‖u_N‖ = 1`. -/
theorem norm_approxLineage (N : ℕ) : ‖a.approxLineage N‖ = 1 := by
  have hsq := norm_sq_sum_single (N + 1) fun n => (certRecip a.c n : ℂ)
  simp only [Complex.norm_real, Real.norm_eq_abs, sq_abs] at hsq
  have hnorm : ‖∑ n ∈ Finset.range (N + 1),
      (lp.single 2 n (certRecip a.c n : ℂ) : ToeplitzSpace)‖ = a.lineageEnergy N := by
    rw [lineageEnergy, ← hsq, Real.sqrt_sq (norm_nonneg _)]
  have hpos := a.lineageEnergy_pos N
  rw [approxLineage, norm_smul, hnorm, norm_inv, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos hpos, inv_mul_cancel₀ hpos.ne']

/-- **Theorem 4.1(2)** (CP.17) `G u_N = (Q_N / L_N) e_N`. -/
theorem genealogy_approxLineage (N : ℕ) :
    a.genealogy (a.approxLineage N) =
      ((certRecip a.c N / a.lineageEnergy N : ℝ) : ℂ) •
        (lp.single 2 N (1 : ℂ) : ToeplitzSpace) := by
  ext k
  rw [genealogy_apply, approxLineage_apply, approxLineage_apply, lp.coeFn_smul, Pi.smul_apply,
    lp.single_apply, Pi.single_apply, smul_eq_mul]
  rcases lt_trichotomy k N with h | h | h
  · rw [if_pos h.le, if_pos (by omega : k + 1 ≤ N), if_neg h.ne, mul_zero]
    have hQ := certRecip_succ a.pos k
    rw [← hQ]
    push_cast
    ring
  · subst h
    rw [if_pos le_rfl, if_neg (by omega), if_pos rfl]
    push_cast
    ring
  · rw [if_neg (by omega), if_neg (by omega), if_neg (by omega)]
    ring

theorem norm_genealogy_approxLineage (N : ℕ) :
    ‖a.genealogy (a.approxLineage N)‖ = certRecip a.c N / a.lineageEnergy N := by
  rw [genealogy_approxLineage, norm_smul, lp.norm_single (by norm_num : (0 : ℝ≥0∞) < 2),
    norm_one, mul_one, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (div_pos (certRecip_pos a.pos N) (a.lineageEnergy_pos N))]

/-- **Theorem 4.1(1)** `u_N` is weakly null. -/
theorem approxLineage_weaklyNull (hQ : ¬ Summable fun n => certRecip a.c n ^ 2)
    (z : ToeplitzSpace) : Tendsto (fun N => ⟪z, a.approxLineage N⟫_ℂ) atTop (𝓝 0) := by
  apply tendsto_inner_lp_of_coord (C := 1) a.approxLineage zero_le_one
    (fun N => (a.norm_approxLineage N).le)
  intro k
  have hinv : Tendsto (fun N => ((a.lineageEnergy N)⁻¹ : ℂ)) atTop (𝓝 0) := by
    have h := (a.tendsto_lineageEnergy hQ).inv_tendsto_atTop
    have := (Complex.continuous_ofReal.tendsto 0).comp h
    rw [Complex.ofReal_zero] at this
    refine this.congr fun N => ?_
    simp
  have := hinv.mul_const (certRecip a.c k : ℂ)
  rw [zero_mul] at this
  refine this.congr' ?_
  filter_upwards [eventually_ge_atTop k] with N hN
  rw [approxLineage_apply, if_pos hN]

/-- The critical mirage hypothesis (CP.15). -/
def IsCriticalMirage : Prop :=
  (¬ Summable fun n => certRecip a.c n ^ 2) ∧
    Tendsto (fun N => certRecip a.c N / a.lineageEnergy N) atTop (𝓝 0)

theorem genealogy_not_boundedBelow_of_mirage (h : a.IsCriticalMirage) :
    ¬ ∃ C > 0, ∀ x, C * ‖x‖ ≤ ‖a.genealogy x‖ := by
  rintro ⟨C, hC, hb⟩
  obtain ⟨N, hN⟩ := (h.2.eventually (gt_mem_nhds hC)).exists
  have := hb (a.approxLineage N)
  rw [a.norm_approxLineage, mul_one, a.norm_genealogy_approxLineage] at this
  linarith

/-- **Theorem 4.1(3)** Under the mirage hypothesis `G` is injective with dense, proper, nonclosed
range. -/
theorem mirage_range (h : a.IsCriticalMirage) :
    Function.Injective a.genealogy ∧ Dense (Set.range a.genealogy) ∧
      Set.range a.genealogy ≠ Set.univ ∧ ¬ IsClosed (Set.range a.genealogy) := by
  have hinj : Function.Injective a.genealogy :=
    LinearMap.ker_eq_bot.mp (a.ker_genealogy_eq_bot h.1)
  have hncl : ¬ IsClosed (Set.range a.genealogy) := by
    intro hcl
    apply a.genealogy_not_boundedBelow_of_mirage h
    rw [exists_pos_mul_norm_le_iff]
    exact ⟨LinearMap.ker_eq_bot.mpr hinj, hcl⟩
  refine ⟨hinj, a.dense_range_genealogy, fun hu => hncl (by rw [hu]; exact isClosed_univ), hncl⟩

/-- **Theorem 4.1(4)–(5)** No compact observer properizes a critical-mirage genealogy. -/
theorem not_jointlyBoundedBelow_of_mirage (h : a.IsCriticalMirage) {Y : Type*}
    [NormedAddCommGroup Y] [NormedSpace ℂ Y] (K : ToeplitzSpace →L[ℂ] Y)
    (hK : IsCompactOperator K) : ¬ JointlyBoundedBelow K a.genealogy := by
  rintro ⟨C, hC, hb⟩
  have hK0 := tendsto_compactOperator_of_weaklyNull K hK a.approxLineage
    (fun N => (a.norm_approxLineage N).le) (a.approxLineage_weaklyNull h.1)
  have hsum : Tendsto (fun N => ‖K (a.approxLineage N)‖ + ‖a.genealogy (a.approxLineage N)‖)
      atTop (𝓝 0) := by
    have h2 : Tendsto (fun N => ‖a.genealogy (a.approxLineage N)‖) atTop (𝓝 0) := by
      simp_rw [a.norm_genealogy_approxLineage]; exact h.2
    have := (tendsto_norm_zero.comp hK0).add h2
    simpa using this
  obtain ⟨N, hN⟩ := (hsum.eventually (gt_mem_nhds hC)).exists
  have := hb (a.approxLineage N)
  rw [a.norm_approxLineage, mul_one] at this
  linarith

/-- Bounded non-square-summable lineage profiles are critical mirages. -/
theorem isCriticalMirage_of_bounded (hQ : ¬ Summable fun n => certRecip a.c n ^ 2) {B : ℝ}
    (hB : ∀ n, certRecip a.c n ≤ B) : a.IsCriticalMirage := by
  refine ⟨hQ, ?_⟩
  have hL := (a.tendsto_lineageEnergy hQ).inv_tendsto_atTop
  have hB0 : 0 ≤ B := (certRecip_pos a.pos 0).le.trans (hB 0)
  refine squeeze_zero (fun N => (div_pos (certRecip_pos a.pos N) (a.lineageEnergy_pos N)).le)
    (fun N => ?_) (by simpa using hL.const_mul B)
  rw [div_eq_mul_inv]
  exact mul_le_mul_of_nonneg_right (hB N) (inv_nonneg.mpr (a.lineageEnergy_pos N).le)

end CertStream

/-! ## Theorem 5.1: exponential-dichotomy chambers -/

/-- Transfer product `P(n,k) = ∏_{j<k} a_{n+j+1}` (CP.19). -/
def certTransfer (c : ℕ → ℝ) (n k : ℕ) : ℝ := ∏ j ∈ Finset.range k, c (n + j)

theorem certTransfer_zero_left (c : ℕ → ℝ) (k : ℕ) : certTransfer c 0 k = certProd c k := by
  simp [certTransfer, certProd]

theorem certTransfer_succ (c : ℕ → ℝ) (n k : ℕ) :
    certTransfer c n (k + 1) = c n * certTransfer c (n + 1) k := by
  rw [certTransfer, Finset.prod_range_succ', mul_comm, add_zero, certTransfer]
  congr 1
  exact Finset.prod_congr rfl fun j _ => by congr 1; omega

theorem certTransfer_succ' (c : ℕ → ℝ) (n k : ℕ) :
    certTransfer c n (k + 1) = certTransfer c n k * c (n + k) := by
  rw [certTransfer, Finset.prod_range_succ]; rfl

/-- **(§6)** Certificate inversion inverts every transfer product, exchanging the stable chamber
(CP.20) of `a` with the unstable chamber (CP.22) of `a⁻¹`. -/
theorem certTransfer_inv (c : ℕ → ℝ) (n k : ℕ) :
    certTransfer (fun j => (c j)⁻¹) n k = (certTransfer c n k)⁻¹ := by
  rw [certTransfer, certTransfer, Finset.prod_inv_distrib]

/-- Neumann inversion from geometric decay of powers. -/
theorem neumann_of_norm_pow_le (T : ToeplitzSpace →L[ℂ] ToeplitzSpace) {C r : ℝ} (hC : 1 ≤ C)
    (hr0 : 0 ≤ r) (hr1 : r < 1) (h : ∀ k, ‖T ^ k‖ ≤ C * r ^ k) :
    (1 - T) * (∑' k, T ^ k) = 1 ∧ (∑' k, T ^ k) * (1 - T) = 1 ∧
      ‖∑' k, T ^ k‖ ≤ 1 + C * r / (1 - r) := by
  have hgeom := summable_geometric_of_lt_one hr0 hr1
  have hs : Summable fun k => T ^ k := Summable.of_norm_bounded (hgeom.mul_left C) h
  have hs1 : Summable fun k => T ^ (k + 1) := (summable_nat_add_iff 1).mpr hs
  have hS0 : ∑' k, T ^ k = 1 + ∑' k, T ^ (k + 1) := by
    rw [hs.tsum_eq_zero_add, pow_zero]
  have hS : ∑' k, T ^ k = 1 + T * ∑' k, T ^ k := by
    calc ∑' k, T ^ k = 1 + ∑' k, T ^ (k + 1) := hS0
      _ = 1 + T * ∑' k, T ^ k := by rw [← hs.tsum_mul_left]; simp_rw [pow_succ']
  have hS' : ∑' k, T ^ k = 1 + (∑' k, T ^ k) * T := by
    calc ∑' k, T ^ k = 1 + ∑' k, T ^ (k + 1) := hS0
      _ = 1 + (∑' k, T ^ k) * T := by rw [← hs.tsum_mul_right]; simp_rw [pow_succ]
  refine ⟨?_, ?_, ?_⟩
  · rw [sub_mul, one_mul]
    nth_rewrite 1 [hS]
    abel
  · rw [mul_sub, mul_one]
    nth_rewrite 1 [hS']
    abel
  · have hnorm1 : Summable fun k => ‖T ^ (k + 1)‖ :=
      Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun k => h (k + 1))
        ((hgeom.mul_left C).comp_injective (add_left_injective 1))
    have hbound : ∑' k, ‖T ^ (k + 1)‖ ≤ C * r / (1 - r) := by
      calc ∑' k, ‖T ^ (k + 1)‖ ≤ ∑' k, C * r ^ (k + 1) :=
            hnorm1.tsum_le_tsum (fun k => h (k + 1))
              ((hgeom.mul_left C).comp_injective (add_left_injective 1))
        _ = C * r / (1 - r) := by
            simp_rw [pow_succ, ← mul_assoc]
            rw [tsum_mul_right, tsum_mul_left, tsum_geometric_of_lt_one hr0 hr1]
            field_simp [(by linarith : (1 - r) ≠ 0)]
    calc ‖∑' k, T ^ k‖ = ‖1 + ∑' k, T ^ (k + 1)‖ := by rw [hs.tsum_eq_zero_add, pow_zero]
      _ ≤ ‖(1 : ToeplitzSpace →L[ℂ] ToeplitzSpace)‖ + ‖∑' k, T ^ (k + 1)‖ := norm_add_le _ _
      _ ≤ 1 + ∑' k, ‖T ^ (k + 1)‖ :=
          add_le_add ContinuousLinearMap.norm_id_le (norm_tsum_le_tsum_norm hnorm1)
      _ ≤ 1 + C * r / (1 - r) := by linarith

/-! ### A generic one-line-kernel repair law -/

section OneLineKernel

variable (G : ToeplitzSpace →L[ℂ] ToeplitzSpace) (g : ToeplitzSpace)

theorem orth_line_decomposition (hg : g ≠ 0) (x : ToeplitzSpace) :
    x - (⟪g, x⟫_ℂ / (‖g‖ ^ 2 : ℝ)) • g ∈ (ℂ ∙ g)ᗮ := by
  rw [Submodule.mem_orthogonal_singleton_iff_inner_right, inner_sub_right, inner_smul_right]
  have hgn : ‖g‖ ≠ 0 := norm_ne_zero_iff.mpr hg
  have hgg : ⟪g, g⟫_ℂ = ((‖g‖ ^ 2 : ℝ) : ℂ) := by
    rw [inner_self_eq_norm_sq_to_K]; norm_cast
  rw [hgg, div_mul_cancel₀ _ (by exact_mod_cast pow_ne_zero 2 hgn), sub_self]

theorem restrict_orth_line_bijective (hg : g ≠ 0) (hsurj : Function.Surjective G)
    (hker : LinearMap.ker (G : ToeplitzSpace →ₗ[ℂ] ToeplitzSpace) = ℂ ∙ g) :
    Function.Bijective (G ∘L (ℂ ∙ g)ᗮ.subtypeL) := by
  constructor
  · intro u v huv
    have huv' : G (u : ToeplitzSpace) = G v := huv
    have hk0 : (u : ToeplitzSpace) - v ∈ LinearMap.ker (G : ToeplitzSpace →ₗ[ℂ] ToeplitzSpace) := by
      show G ((u : ToeplitzSpace) - v) = 0; rw [map_sub, huv', sub_self]
    have hk : (u : ToeplitzSpace) - v ∈ ℂ ∙ g := by rw [hker] at hk0; exact hk0
    have hp : (u : ToeplitzSpace) - v ∈ (ℂ ∙ g)ᗮ := Submodule.sub_mem _ u.2 v.2
    have : (u : ToeplitzSpace) - v ∈ (ℂ ∙ g) ⊓ (ℂ ∙ g)ᗮ := ⟨hk, hp⟩
    rw [Submodule.inf_orthogonal_eq_bot, Submodule.mem_bot, sub_eq_zero] at this
    exact Subtype.ext this
  · intro y
    obtain ⟨x, rfl⟩ := hsurj y
    refine ⟨⟨_, orth_line_decomposition g hg x⟩, ?_⟩
    have hgk : G g = 0 := by
      have : g ∈ LinearMap.ker (G : ToeplitzSpace →ₗ[ℂ] ToeplitzSpace) := by
        rw [hker]; exact Submodule.mem_span_singleton_self g
      exact this
    change G (x - _ • g) = G x
    rw [map_sub, map_smul, hgk, smul_zero, sub_zero]

/-- The bounded inverse of `G` on the orthogonal complement of its kernel line. -/
def orthLineInverse (hg : g ≠ 0) (hsurj : Function.Surjective G)
    (hker : LinearMap.ker (G : ToeplitzSpace →ₗ[ℂ] ToeplitzSpace) = ℂ ∙ g) :
    ToeplitzSpace →L[ℂ] ToeplitzSpace :=
  (ℂ ∙ g)ᗮ.subtypeL ∘L
    ((ContinuousLinearEquiv.ofBijective (G ∘L (ℂ ∙ g)ᗮ.subtypeL)
      (LinearMap.ker_eq_bot.mpr (restrict_orth_line_bijective G g hg hsurj hker).1)
      (LinearMap.range_eq_top.mpr (restrict_orth_line_bijective G g hg hsurj hker).2)).symm :
        ToeplitzSpace →L[ℂ] (ℂ ∙ g)ᗮ)

/-- Exact reconstruction `x = J(G x) + (⟨g, x⟩/‖g‖²) g`. -/
theorem orthLine_reconstruction (hg : g ≠ 0) (hsurj : Function.Surjective G)
    (hker : LinearMap.ker (G : ToeplitzSpace →ₗ[ℂ] ToeplitzSpace) = ℂ ∙ g) (x : ToeplitzSpace) :
    x = orthLineInverse G g hg hsurj hker (G x) + (⟪g, x⟫_ℂ / (‖g‖ ^ 2 : ℝ)) • g := by
  set e := ContinuousLinearEquiv.ofBijective (G ∘L (ℂ ∙ g)ᗮ.subtypeL)
    (LinearMap.ker_eq_bot.mpr (restrict_orth_line_bijective G g hg hsurj hker).1)
    (LinearMap.range_eq_top.mpr (restrict_orth_line_bijective G g hg hsurj hker).2)
  set u : (ℂ ∙ g)ᗮ := ⟨_, orth_line_decomposition g hg x⟩
  have hgk : G g = 0 := by
    have : g ∈ LinearMap.ker (G : ToeplitzSpace →ₗ[ℂ] ToeplitzSpace) := by
      rw [hker]; exact Submodule.mem_span_singleton_self g
    exact this
  have hGu : (G ∘L (ℂ ∙ g)ᗮ.subtypeL) u = G x := by
    change G (x - _ • g) = G x
    rw [map_sub, map_smul, hgk, smul_zero, sub_zero]
  have hJ : orthLineInverse G g hg hsurj hker (G x) = (u : ToeplitzSpace) := by
    change ((e.symm (G x) : (ℂ ∙ g)ᗮ) : ToeplitzSpace) = u
    rw [← hGu]
    change ((e.symm (e u) : (ℂ ∙ g)ᗮ) : ToeplitzSpace) = u
    rw [ContinuousLinearEquiv.symm_apply_apply]
  rw [hJ]
  change x = (x - _ • g) + _
  abel

/-- **(CP.24)** For a surjective genealogy with one-line kernel `ℂ g`, an observer `A` repairs it
exactly when `A g ≠ 0`. -/
theorem jointlyBoundedBelow_iff_of_orthLine {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℂ Y]
    (hg : g ≠ 0) (hsurj : Function.Surjective G)
    (hker : LinearMap.ker (G : ToeplitzSpace →ₗ[ℂ] ToeplitzSpace) = ℂ ∙ g)
    (A : ToeplitzSpace →L[ℂ] Y) : JointlyBoundedBelow A G ↔ A g ≠ 0 := by
  have hgk : G g = 0 := by
    have : g ∈ LinearMap.ker (G : ToeplitzSpace →ₗ[ℂ] ToeplitzSpace) := by
      rw [hker]; exact Submodule.mem_span_singleton_self g
    exact this
  constructor
  · rintro ⟨c, hc, h⟩ hAg
    have := h g
    rw [hAg, hgk, norm_zero, norm_zero, add_zero] at this
    have hgpos : 0 < ‖g‖ := norm_pos_iff.mpr hg
    nlinarith
  · intro hAg
    set J := orthLineInverse G g hg hsurj hker
    have hAgpos : 0 < ‖A g‖ := norm_pos_iff.mpr hAg
    have hgpos : 0 < ‖g‖ := norm_pos_iff.mpr hg
    set C : ℝ := ‖J‖ + ‖g‖ * (1 + ‖A‖ * ‖J‖) / ‖A g‖ with hC
    have hCpos : 0 < C := by positivity
    refine ⟨C⁻¹, inv_pos.mpr hCpos, fun x => ?_⟩
    set t : ℂ := ⟪g, x⟫_ℂ / (‖g‖ ^ 2 : ℝ)
    have hrec := orthLine_reconstruction G g hg hsurj hker x
    have hAx : A x = A (J (G x)) + t • A g := by
      conv_lhs => rw [hrec]
      rw [map_add, map_smul]
    have ht : ‖t‖ * ‖A g‖ ≤ ‖A x‖ + ‖A‖ * ‖J‖ * ‖G x‖ := by
      have h1 : t • A g = A x - A (J (G x)) := by rw [hAx]; abel
      have h2 : ‖A (J (G x))‖ ≤ ‖A‖ * ‖J‖ * ‖G x‖ := by
        calc ‖A (J (G x))‖ ≤ ‖A‖ * ‖J (G x)‖ := A.le_opNorm _
          _ ≤ ‖A‖ * (‖J‖ * ‖G x‖) := mul_le_mul_of_nonneg_left (J.le_opNorm _) (norm_nonneg _)
          _ = _ := by ring
      calc ‖t‖ * ‖A g‖ = ‖t • A g‖ := (norm_smul _ _).symm
        _ = ‖A x - A (J (G x))‖ := by rw [h1]
        _ ≤ ‖A x‖ + ‖A (J (G x))‖ := norm_sub_le _ _
        _ ≤ _ := by linarith
    have hx : ‖x‖ ≤ ‖J‖ * ‖G x‖ + ‖t‖ * ‖g‖ := by
      calc ‖x‖ = ‖J (G x) + t • g‖ := by rw [← hrec]
        _ ≤ ‖J (G x)‖ + ‖t • g‖ := norm_add_le _ _
        _ ≤ ‖J‖ * ‖G x‖ + ‖t‖ * ‖g‖ := by
            rw [norm_smul]; exact add_le_add (J.le_opNorm _) le_rfl
    have htle : ‖t‖ ≤ (‖A x‖ + ‖A‖ * ‖J‖ * ‖G x‖) / ‖A g‖ := by
      rw [le_div_iff₀ hAgpos]; exact ht
    rw [inv_mul_eq_div, div_le_iff₀ hCpos]
    have hGx := norm_nonneg (G x)
    have hAx0 := norm_nonneg (A x)
    have hJ0 := norm_nonneg J
    have hA0 := norm_nonneg A
    have hkey : ‖x‖ ≤ ‖J‖ * ‖G x‖ + (‖A x‖ + ‖A‖ * ‖J‖ * ‖G x‖) / ‖A g‖ * ‖g‖ :=
      hx.trans (add_le_add le_rfl (mul_le_mul_of_nonneg_right htle hgpos.le))
    have hdiff : (‖A x‖ + ‖G x‖) * C -
        (‖J‖ * ‖G x‖ + (‖A x‖ + ‖A‖ * ‖J‖ * ‖G x‖) / ‖A g‖ * ‖g‖) =
        ‖A x‖ * ‖J‖ + (‖A x‖ * ‖g‖ * ‖A‖ * ‖J‖ + ‖G x‖ * ‖g‖) / ‖A g‖ := by
      rw [hC]; field_simp; ring
    have hnn : 0 ≤ ‖A x‖ * ‖J‖ + (‖A x‖ * ‖g‖ * ‖A‖ * ‖J‖ + ‖G x‖ * ‖g‖) / ‖A g‖ := by
      positivity
    linarith

end OneLineKernel

namespace CertStream

variable (a : CertStream)

theorem bound_pos : 0 < a.bound := (a.pos 0).trans_le (a.le_bound 0)

theorem certTransfer_pos (n k : ℕ) : 0 < certTransfer a.c n k :=
  Finset.prod_pos fun _ _ => a.pos _

theorem norm_certTransfer_le (k : ℕ) (n : ℕ) : ‖(certTransfer a.c n k : ℂ)‖ ≤ a.bound ^ k := by
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (a.certTransfer_pos n k), certTransfer]
  calc ∏ j ∈ Finset.range k, a.c (n + j) ≤ ∏ _j ∈ Finset.range k, a.bound :=
        Finset.prod_le_prod (fun _ _ => (a.pos _).le) (fun _ _ => a.le_bound _)
    _ = a.bound ^ k := by simp

/-- The transfer diagonal `x ↦ (P(n,k) x_n)`. -/
def transferDiag (k : ℕ) : ToeplitzSpace →L[ℂ] ToeplitzSpace :=
  _root_.HTGeometry.ellTwoDiagonal (fun n => (certTransfer a.c n k : ℂ)) (a.norm_certTransfer_le k)

theorem weight_pow_eq (k : ℕ) : a.weight ^ k = a.transferDiag k ∘L backOp k := by
  induction k with
  | zero =>
      ext x n
      show (x : ℕ → ℂ) n = (a.transferDiag 0 (backOp 0 x) : ℕ → ℂ) n
      rw [transferDiag, _root_.HTGeometry.ellTwoDiagonal_apply, backOp_apply]
      simp [certTransfer]
  | succ k ih =>
      ext x n
      have hL : ((a.weight ^ (k + 1)) x : ℕ → ℂ) n =
          a.c n * ((a.weight ^ k) x : ℕ → ℂ) (n + 1) := by
        rw [pow_succ']; exact a.weight_apply _ n
      rw [hL, ih]
      show (a.c n : ℂ) * ((certTransfer a.c (n + 1) k : ℂ) * (x : ℕ → ℂ) (n + 1 + k)) =
        (certTransfer a.c n (k + 1) : ℂ) * (x : ℕ → ℂ) (n + (k + 1))
      rw [certTransfer_succ, show n + 1 + k = n + (k + 1) by omega]
      push_cast
      ring

theorem norm_weight_pow_le (k : ℕ) {B : ℝ} (hB0 : 0 ≤ B) (hB : ∀ n, certTransfer a.c n k ≤ B) :
    ‖a.weight ^ k‖ ≤ B := by
  rw [weight_pow_eq]
  have hbound : ∀ n, ‖(certTransfer a.c n k : ℂ)‖ ≤ B := fun n => by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (a.certTransfer_pos n k)]; exact hB n
  have hD : a.transferDiag k =
      _root_.HTGeometry.ellTwoDiagonal (fun n => (certTransfer a.c n k : ℂ)) hbound := by
    ext x n; rfl
  calc ‖a.transferDiag k ∘L backOp k‖ ≤ ‖a.transferDiag k‖ * ‖backOp k‖ := opNorm_comp_le _ _
    _ ≤ B * 1 := by
        rw [hD]
        exact mul_le_mul (_root_.HTGeometry.norm_ellTwoDiagonal_le _ hbound hB0)
          (norm_backOp_le k) (norm_nonneg _) hB0
    _ = B := mul_one B

theorem genealogy_eq_one_sub : a.genealogy = 1 - a.weight := rfl

/-- **Theorem 5.1, stable phase** (CP.20)–(CP.21): uniform contraction of the transfer products
makes `G` boundedly invertible with Neumann inverse `∑ W^k` of norm at most `1 + C r/(1 - r)`,
and the semantic profile is square summable. -/
theorem stable_phase {C r : ℝ} (hC : 1 ≤ C) (hr0 : 0 ≤ r) (hr1 : r < 1)
    (hP : ∀ n k, certTransfer a.c n k ≤ C * r ^ k) :
    a.genealogy * (∑' k, a.weight ^ k) = 1 ∧ (∑' k, a.weight ^ k) * a.genealogy = 1 ∧
      ‖∑' k, a.weight ^ k‖ ≤ 1 + C * r / (1 - r) ∧ Summable fun n => certProd a.c n ^ 2 := by
  have hpow : ∀ k, ‖a.weight ^ k‖ ≤ C * r ^ k := fun k =>
    a.norm_weight_pow_le k (by positivity) (fun n => hP n k)
  obtain ⟨h1, h2, h3⟩ := neumann_of_norm_pow_le a.weight hC hr0 hr1 hpow
  refine ⟨h1, h2, h3, ?_⟩
  have hr2 : r ^ 2 < 1 := pow_lt_one₀ hr0 hr1 two_ne_zero
  refine Summable.of_nonneg_of_le (fun n => sq_nonneg _) (fun n => ?_)
    ((summable_geometric_of_lt_one (by positivity) hr2).mul_left (C ^ 2))
  have hA := hP 0 n
  rw [certTransfer_zero_left] at hA
  have hA0 := certProd_pos a.pos n
  calc certProd a.c n ^ 2 ≤ (C * r ^ n) ^ 2 := pow_le_pow_left₀ hA0.le hA 2
    _ = C ^ 2 * (r ^ 2) ^ n := by ring

theorem stable_phase_isUnit {C r : ℝ} (hC : 1 ≤ C) (hr0 : 0 ≤ r) (hr1 : r < 1)
    (hP : ∀ n k, certTransfer a.c n k ≤ C * r ^ k) : IsUnit a.genealogy := by
  obtain ⟨h1, h2, -, -⟩ := a.stable_phase hC hr0 hr1 hP
  exact ⟨⟨a.genealogy, _, h1, h2⟩, rfl⟩

/-! ### Unstable phase -/

section Unstable

variable {m : ℝ} (hm : 0 < m) (hmc : ∀ n, m ≤ a.c n)
include hm hmc

theorem norm_inv_coe_le (n : ℕ) : ‖((a.c n : ℂ))⁻¹‖ ≤ m⁻¹ := by
  rw [norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (a.pos n)]
  exact inv_anti₀ hm (hmc n)

/-- The inverse certificate diagonal `x ↦ (a_{n+1}⁻¹ x_n)`. -/
def invDiag : ToeplitzSpace →L[ℂ] ToeplitzSpace :=
  _root_.HTGeometry.ellTwoDiagonal (fun n => ((a.c n : ℂ))⁻¹) (a.norm_inv_coe_le hm hmc)

/-- **(CP.25)** The weighted forward right inverse `R e_n = a_{n+1}⁻¹ e_{n+1}`. -/
def forward : ToeplitzSpace →L[ℂ] ToeplitzSpace := shiftOp 1 ∘L a.invDiag hm hmc

theorem forward_apply_zero (x : ToeplitzSpace) : (a.forward hm hmc x : ℕ → ℂ) 0 = 0 :=
  shiftOp_one_apply_zero _

theorem forward_apply_succ (x : ToeplitzSpace) (n : ℕ) :
    (a.forward hm hmc x : ℕ → ℂ) (n + 1) = ((a.c n : ℂ))⁻¹ * (x : ℕ → ℂ) n := by
  show (shiftOp 1 (a.invDiag hm hmc x) : ℕ → ℂ) (n + 1) = _
  rw [shiftOp_one_apply_succ, invDiag, _root_.HTGeometry.ellTwoDiagonal_apply]

theorem weight_mul_forward : a.weight * a.forward hm hmc = 1 := by
  ext x n
  show (a.weight (a.forward hm hmc x) : ℕ → ℂ) n = (x : ℕ → ℂ) n
  rw [weight_apply, forward_apply_succ]
  have hc0 : (a.c n : ℂ) ≠ 0 := by exact_mod_cast (a.pos n).ne'
  field_simp

theorem norm_forward_le : ‖a.forward hm hmc‖ ≤ m⁻¹ := by
  calc ‖a.forward hm hmc‖ ≤ ‖shiftOp 1‖ * ‖a.invDiag hm hmc‖ := opNorm_comp_le _ _
    _ ≤ 1 * m⁻¹ := mul_le_mul (norm_shiftOp_le 1)
        (_root_.HTGeometry.norm_ellTwoDiagonal_le _ _ (inv_pos.mpr hm).le) (norm_nonneg _)
        zero_le_one
    _ = m⁻¹ := one_mul _

theorem norm_inv_certTransfer_le (k n : ℕ) :
    ‖((certTransfer a.c n k : ℂ))⁻¹‖ ≤ m⁻¹ ^ k := by
  rw [norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (a.certTransfer_pos n k),
    certTransfer, ← Finset.prod_inv_distrib]
  calc ∏ j ∈ Finset.range k, (a.c (n + j))⁻¹ ≤ ∏ _j ∈ Finset.range k, m⁻¹ :=
        Finset.prod_le_prod (fun _ _ => (inv_pos.mpr (a.pos _)).le)
          (fun _ _ => inv_anti₀ hm (hmc _))
    _ = m⁻¹ ^ k := by simp

/-- The inverse transfer diagonal `x ↦ (P(n,k)⁻¹ x_n)`. -/
def invTransferDiag (k : ℕ) : ToeplitzSpace →L[ℂ] ToeplitzSpace :=
  _root_.HTGeometry.ellTwoDiagonal (fun n => ((certTransfer a.c n k : ℂ))⁻¹)
    (a.norm_inv_certTransfer_le hm hmc k)

theorem forward_pow_eq (k : ℕ) : a.forward hm hmc ^ k = shiftOp k ∘L a.invTransferDiag hm hmc k := by
  induction k with
  | zero =>
      ext x n
      show (x : ℕ → ℂ) n = (shiftOp 0 (a.invTransferDiag hm hmc 0 x) : ℕ → ℂ) n
      rw [shiftOp_apply, shiftFun_of_le (Nat.zero_le n), invTransferDiag,
        _root_.HTGeometry.ellTwoDiagonal_apply]
      simp [certTransfer]
  | succ k ih =>
      ext x i
      rw [pow_succ']
      show (a.forward hm hmc ((a.forward hm hmc ^ k) x) : ℕ → ℂ) i =
        (shiftOp (k + 1) (a.invTransferDiag hm hmc (k + 1) x) : ℕ → ℂ) i
      rw [ih]
      cases i with
      | zero =>
          rw [forward_apply_zero, shiftOp_apply, shiftFun_of_lt (by omega)]
      | succ j =>
          rw [forward_apply_succ]
          show ((a.c j : ℂ))⁻¹ * shiftFun k (a.invTransferDiag hm hmc k x : ℕ → ℂ) j =
            shiftFun (k + 1) (a.invTransferDiag hm hmc (k + 1) x : ℕ → ℂ) (j + 1)
          by_cases hjk : j < k
          · rw [shiftFun_of_lt hjk, shiftFun_of_lt (by omega), mul_zero]
          · rw [not_lt] at hjk
            rw [shiftFun_of_le hjk, shiftFun_of_le (by omega), invTransferDiag, invTransferDiag,
              _root_.HTGeometry.ellTwoDiagonal_apply, _root_.HTGeometry.ellTwoDiagonal_apply,
              show j + 1 - (k + 1) = j - k by omega, certTransfer_succ',
              show j - k + k = j by omega]
            push_cast
            rw [mul_inv]
            ring

theorem norm_forward_pow_le (k : ℕ) {B : ℝ} (hB0 : 0 ≤ B)
    (hB : ∀ n, (certTransfer a.c n k)⁻¹ ≤ B) : ‖a.forward hm hmc ^ k‖ ≤ B := by
  rw [forward_pow_eq]
  have hbound : ∀ n, ‖((certTransfer a.c n k : ℂ))⁻¹‖ ≤ B := fun n => by
    rw [norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (a.certTransfer_pos n k)]
    exact hB n
  have hD : a.invTransferDiag hm hmc k =
      _root_.HTGeometry.ellTwoDiagonal (fun n => ((certTransfer a.c n k : ℂ))⁻¹) hbound := by
    ext x n; rfl
  calc ‖shiftOp k ∘L a.invTransferDiag hm hmc k‖
      ≤ ‖shiftOp k‖ * ‖a.invTransferDiag hm hmc k‖ := opNorm_comp_le _ _
    _ ≤ 1 * B := by
        rw [hD]
        exact mul_le_mul (norm_shiftOp_le k)
          (_root_.HTGeometry.norm_ellTwoDiagonal_le _ hbound hB0) (norm_nonneg _) zero_le_one
    _ = B := one_mul B

/-- **(CP.26)** `G = -W (1 - R)`. -/
theorem genealogy_eq_neg_weight_mul : a.genealogy = -(a.weight * (1 - a.forward hm hmc)) := by
  rw [genealogy_eq_one_sub, mul_sub, mul_one, weight_mul_forward]
  abel

/-- **Theorem 5.1, unstable phase** (CP.22)–(CP.24): uniform expansion of the transfer products
makes `G` surjective with a bounded right inverse `-R(1-R)⁻¹` of norm at most
`m⁻¹ (1 + C r/(1-r))`, kernel the lineage line `ℂ Q`, and an observer repairs `G` exactly when it
sees `Q`. -/
theorem unstable_phase {C r : ℝ} (hC : 1 ≤ C) (hr0 : 0 ≤ r) (hr1 : r < 1)
    (hP : ∀ n k, (certTransfer a.c n k)⁻¹ ≤ C * r ^ k) :
    ∃ hQ : Summable (fun n => certRecip a.c n ^ 2),
      a.genealogy * (-(a.forward hm hmc * ∑' k, a.forward hm hmc ^ k)) = 1 ∧
      ‖-(a.forward hm hmc * ∑' k, a.forward hm hmc ^ k)‖ ≤ m⁻¹ * (1 + C * r / (1 - r)) ∧
      Function.Surjective a.genealogy ∧
      LinearMap.ker (a.genealogy : ToeplitzSpace →ₗ[ℂ] ToeplitzSpace) = ℂ ∙ a.lineage hQ ∧
      ∀ {Y : Type} [NormedAddCommGroup Y] [NormedSpace ℂ Y] (K : ToeplitzSpace →L[ℂ] Y),
        JointlyBoundedBelow K a.genealogy ↔ K (a.lineage hQ) ≠ 0 := by
  set R := a.forward hm hmc
  have hpow : ∀ k, ‖R ^ k‖ ≤ C * r ^ k := fun k =>
    a.norm_forward_pow_le hm hmc k (by positivity) (fun n => hP n k)
  obtain ⟨h1, h2, h3⟩ := neumann_of_norm_pow_le R hC hr0 hr1 hpow
  set S := ∑' k, R ^ k
  have hQ : Summable fun n => certRecip a.c n ^ 2 := by
    have hr2 : r ^ 2 < 1 := pow_lt_one₀ hr0 hr1 two_ne_zero
    refine Summable.of_nonneg_of_le (fun n => sq_nonneg _) (fun n => ?_)
      ((summable_geometric_of_lt_one (by positivity) hr2).mul_left (C ^ 2))
    have hQn := hP 0 n
    rw [certTransfer_zero_left] at hQn
    calc certRecip a.c n ^ 2 ≤ (C * r ^ n) ^ 2 :=
          pow_le_pow_left₀ (certRecip_pos a.pos n).le hQn 2
      _ = C ^ 2 * (r ^ 2) ^ n := by ring
  have hright : a.genealogy * (-(R * S)) = 1 := by
    have hWR : a.weight * R = 1 := a.weight_mul_forward hm hmc
    calc a.genealogy * (-(R * S)) = a.weight * (1 - R) * (R * S) := by
          rw [a.genealogy_eq_neg_weight_mul hm hmc]; noncomm_ring
      _ = a.weight * R * ((1 - R) * S) := by noncomm_ring
      _ = 1 := by rw [hWR, h1, one_mul]
  have hsurj : Function.Surjective a.genealogy := fun y =>
    ⟨(-(R * S)) y, by
      have := congrArg (fun T : ToeplitzSpace →L[ℂ] ToeplitzSpace => T y) hright
      exact this⟩
  have hker := a.ker_genealogy_eq_span hQ
  refine ⟨hQ, hright, ?_, hsurj, hker, fun K => ?_⟩
  · rw [norm_neg]
    calc ‖R * S‖ ≤ ‖R‖ * ‖S‖ := norm_mul_le _ _
      _ ≤ m⁻¹ * (1 + C * r / (1 - r)) :=
          mul_le_mul (a.norm_forward_le hm hmc) h3 (norm_nonneg _) (inv_pos.mpr hm).le
  · exact jointlyBoundedBelow_iff_of_orthLine a.genealogy (a.lineage hQ) (a.lineage_ne_zero hQ)
      hsurj hker K

end Unstable

/-! ### Mirage instances -/

/-- The stationary critical certificate stream `a_n = 1`. -/
def stationaryCritical : CertStream where
  c := fun _ => 1
  pos := fun _ => one_pos
  bound := 1
  le_bound := fun _ => le_rfl

theorem stationaryCritical_certRecip (n : ℕ) : certRecip stationaryCritical.c n = 1 := by
  simp [certRecip, certProd, stationaryCritical]

/-- Stationary critical certificates are critical mirages. -/
theorem stationaryCritical_isCriticalMirage : stationaryCritical.IsCriticalMirage := by
  refine stationaryCritical.isCriticalMirage_of_bounded ?_ (B := 1) fun n => by
    rw [stationaryCritical_certRecip]
  intro h
  have := h.tendsto_atTop_zero
  simp only [stationaryCritical_certRecip, one_pow] at this
  exact one_ne_zero (tendsto_nhds_unique tendsto_const_nhds this)

theorem sum_pow_ge_integral (N k : ℕ) :
    ((N : ℝ) + 1) ^ (2 * k + 1) / (2 * k + 1) ≤
      ∑ n ∈ Finset.range (N + 1), ((n : ℝ) + 1) ^ (2 * k) := by
  have hmono : MonotoneOn (fun x : ℝ => x ^ (2 * k)) (Set.Icc 0 (0 + ((N + 1 : ℕ) : ℝ))) :=
    fun x hx y _ hxy => pow_le_pow_left₀ hx.1 hxy _
  have h := hmono.integral_le_sum
  rw [integral_pow] at h
  simp only [zero_add, Nat.cast_add, Nat.cast_one, ne_eq, add_eq_zero, one_ne_zero, and_false,
    not_false_eq_true, zero_pow, sub_zero, Nat.cast_mul, Nat.cast_ofNat] at h
  refine le_trans (le_of_eq ?_) (h.trans (le_of_eq ?_))
  · ring_nf
  · refine Finset.sum_congr rfl fun n _ => ?_
    ring_nf

/-- Regular polynomial growth of the lineage profile gives a critical mirage. -/
theorem isCriticalMirage_of_polynomial {c₁ c₂ : ℝ} (hc₁ : 0 < c₁) {k : ℕ}
    (hlow : ∀ n : ℕ, c₁ * ((n : ℝ) + 1) ^ k ≤ certRecip a.c n)
    (hup : ∀ n, certRecip a.c n ≤ c₂ * ((n : ℝ) + 1) ^ k) : a.IsCriticalMirage := by
  have hQlow : ∀ n : ℕ, c₁ ^ 2 * ((n : ℝ) + 1) ^ (2 * k) ≤ certRecip a.c n ^ 2 := fun n => by
    have h := pow_le_pow_left₀ (by positivity) (hlow n) 2
    calc c₁ ^ 2 * ((n : ℝ) + 1) ^ (2 * k) = (c₁ * ((n : ℝ) + 1) ^ k) ^ 2 := by ring
      _ ≤ _ := h
  have hQ : ¬ Summable fun n => certRecip a.c n ^ 2 := by
    intro h
    have ht := h.tendsto_atTop_zero
    have hge : ∀ n, c₁ ^ 2 ≤ certRecip a.c n ^ 2 := fun n =>
      le_trans (by
        have : (1 : ℝ) ≤ ((n : ℝ) + 1) ^ (2 * k) := one_le_pow₀ (by linarith [(n.cast_nonneg : (0 : ℝ) ≤ n)])
        nlinarith [sq_nonneg c₁]) (hQlow n)
    have := ge_of_tendsto ht (Eventually.of_forall hge)
    nlinarith [sq_pos_of_pos hc₁]
  refine ⟨hQ, ?_⟩
  set K : ℝ := c₂ ^ 2 * (2 * k + 1) / c₁ ^ 2
  have hc₂ : 0 ≤ c₂ := by
    have := (certRecip_pos a.pos 0).le.trans (hup 0)
    simpa using this
  have hbound : ∀ N : ℕ, certRecip a.c N / a.lineageEnergy N ≤
      Real.sqrt K * (Real.sqrt ((N : ℝ) + 1))⁻¹ := by
    intro N
    have hL := a.lineageEnergy_pos N
    have hLsq : c₁ ^ 2 * (((N : ℝ) + 1) ^ (2 * k + 1) / (2 * k + 1)) ≤ a.lineageEnergy N ^ 2 := by
      rw [lineageEnergy_sq]
      calc c₁ ^ 2 * (((N : ℝ) + 1) ^ (2 * k + 1) / (2 * k + 1))
          ≤ c₁ ^ 2 * ∑ n ∈ Finset.range (N + 1), ((n : ℝ) + 1) ^ (2 * k) :=
            mul_le_mul_of_nonneg_left (sum_pow_ge_integral N k) (sq_nonneg _)
        _ = ∑ n ∈ Finset.range (N + 1), c₁ ^ 2 * ((n : ℝ) + 1) ^ (2 * k) := Finset.mul_sum _ _ _
        _ ≤ _ := Finset.sum_le_sum fun n _ => hQlow n
    have hQN : certRecip a.c N ^ 2 ≤ c₂ ^ 2 * ((N : ℝ) + 1) ^ (2 * k) := by
      have := pow_le_pow_left₀ (certRecip_pos a.pos N).le (hup N) 2
      calc certRecip a.c N ^ 2 ≤ (c₂ * ((N : ℝ) + 1) ^ k) ^ 2 := this
        _ = _ := by ring
    have hN1 : (0 : ℝ) < (N : ℝ) + 1 := by positivity
    have hsq : (certRecip a.c N / a.lineageEnergy N) ^ 2 ≤ K / ((N : ℝ) + 1) := by
      rw [div_pow, div_le_div_iff₀ (by positivity) hN1]
      have hpow : ((N : ℝ) + 1) ^ (2 * k + 1) = ((N : ℝ) + 1) ^ (2 * k) * ((N : ℝ) + 1) := by
        rw [pow_succ]
      have h2k : (0 : ℝ) < 2 * k + 1 := by positivity
      have hLsq' : c₁ ^ 2 * ((N : ℝ) + 1) ^ (2 * k) * ((N : ℝ) + 1) ≤
          (2 * k + 1) * a.lineageEnergy N ^ 2 := by
        have e : c₁ ^ 2 * ((N : ℝ) + 1) ^ (2 * k) * ((N : ℝ) + 1) =
            (2 * k + 1) * (c₁ ^ 2 * (((N : ℝ) + 1) ^ (2 * k + 1) / (2 * k + 1))) := by
          rw [hpow]; field_simp
        rw [e]
        exact mul_le_mul_of_nonneg_left hLsq h2k.le
      calc certRecip a.c N ^ 2 * ((N : ℝ) + 1)
          ≤ c₂ ^ 2 * ((N : ℝ) + 1) ^ (2 * k) * ((N : ℝ) + 1) :=
            mul_le_mul_of_nonneg_right hQN hN1.le
        _ = c₂ ^ 2 / c₁ ^ 2 * (c₁ ^ 2 * ((N : ℝ) + 1) ^ (2 * k) * ((N : ℝ) + 1)) := by
            field_simp
        _ ≤ c₂ ^ 2 / c₁ ^ 2 * ((2 * k + 1) * a.lineageEnergy N ^ 2) :=
            mul_le_mul_of_nonneg_left hLsq' (by positivity)
        _ = K * a.lineageEnergy N ^ 2 := by rw [show K = c₂ ^ 2 * (2 * k + 1) / c₁ ^ 2 from rfl]; ring
    have hK0 : 0 ≤ K := by positivity
    have hr0 : 0 ≤ certRecip a.c N / a.lineageEnergy N :=
      (div_pos (certRecip_pos a.pos N) hL).le
    calc certRecip a.c N / a.lineageEnergy N
        = Real.sqrt ((certRecip a.c N / a.lineageEnergy N) ^ 2) := (Real.sqrt_sq hr0).symm
      _ ≤ Real.sqrt (K / ((N : ℝ) + 1)) := Real.sqrt_le_sqrt hsq
      _ = Real.sqrt K * (Real.sqrt ((N : ℝ) + 1))⁻¹ := by
          rw [Real.sqrt_div' _ hN1.le, div_eq_mul_inv]
  have hlim : Tendsto (fun N : ℕ => Real.sqrt K * (Real.sqrt ((N : ℝ) + 1))⁻¹) atTop (𝓝 0) := by
    have h : Tendsto (fun N : ℕ => Real.sqrt ((N : ℝ) + 1)) atTop atTop :=
      Real.tendsto_sqrt_atTop.comp (tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds)
    simpa using h.inv_tendsto_atTop.const_mul (Real.sqrt K)
  exact squeeze_zero (fun N => (div_pos (certRecip_pos a.pos N) (a.lineageEnergy_pos N)).le)
    hbound hlim

end CertStream

end

end GaloisForLFunctions.HTGeometry
