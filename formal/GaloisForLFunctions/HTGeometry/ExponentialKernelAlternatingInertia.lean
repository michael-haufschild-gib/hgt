import GaloisForLFunctions.HTGeometry.HaynsworthInertia
import GaloisForLFunctions.HTGeometry.KernelNestedFiniteSectionInertia
import GaloisForLFunctions.HTGeometry.Zeta5AndreiefTransfer
import GaloisForLFunctions.HTGeometry.NavierStokesRealExponentialVandermonde

/-!
# Alternating inertia of real-exponential kernels

For a finite positive measure `μ` carried by a compact interval and strictly increasing real
nodes `x₁ < ⋯ < x_N`, the kernel matrix `K_ij = ∫ e^{u(x_i - x_j)} dμ(u)` satisfies

* `(-1)^{N(N-1)/2} det K > 0` as soon as the support of `μ` has at least `N` points
  (Andréief's identity and the strict sign of real-exponential Vandermonde determinants);
* when `μ` is symmetric, `K` is symmetric with inertia `(⌈N/2⌉, ⌊N/2⌋, 0)`
  (Jacobi's signature rule, obtained from Haynsworth additivity along leading minors).

The Fourier kernel `∫ e^{iu(x_i - x_j)} dμ(u)` is, by contrast, a Gram matrix and positive
semidefinite.  Two index consequences are recorded: a correction of rank `r` lowers the
negative index by at most `r`, and a kernel whose finite sections have unbounded negative
index has no representation in any space whose Hermitian form has finite negative index.
-/

namespace GaloisForLFunctions.HTGeometry

open Matrix MeasureTheory Finset Filter Topology
open NavierStokesRealExponentialVandermonde

noncomputable section

/-! ### Reindexing -/

section Reindex

variable {m n : Type*} [Fintype m] [Fintype n]

theorem hermQuad_submatrix_equiv (A : Matrix n n ℂ) (e : m ≃ n) (x : m → ℂ) :
    hermQuad (A.submatrix e e) x = hermQuad A (x ∘ e.symm) := by
  simp only [hermQuad, dotProduct, mulVec, submatrix_apply, Pi.star_apply, Function.comp_apply]
  congr 1
  rw [← e.sum_comp]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← e.sum_comp]
  simp

theorem hermPosIndex_submatrix_equiv_le (A : Matrix n n ℂ) (e : m ≃ n) :
    hermPosIndex (A.submatrix e e) ≤ hermPosIndex A := by
  obtain ⟨W, hW, hpos⟩ := exists_isPosDefOn_finrank_eq_posIndex (A.submatrix e e)
  let L : (m → ℂ) ≃ₗ[ℂ] (n → ℂ) := LinearEquiv.funCongrLeft ℂ ℂ e.symm
  have hL : ∀ x, L x = x ∘ e.symm := fun x => rfl
  rw [← hW, ← LinearEquiv.finrank_map_eq L W]
  refine finrank_le_posIndex fun y hy hy0 => ?_
  obtain ⟨x, hx, rfl⟩ := Submodule.mem_map.mp hy
  have hx0 : x ≠ 0 := by rintro rfl; exact hy0 (map_zero _)
  rw [LinearEquiv.coe_coe, hL, ← hermQuad_submatrix_equiv]
  exact hpos x hx hx0

/-- The positive index is invariant under reindexing. -/
theorem hermPosIndex_submatrix_equiv (A : Matrix n n ℂ) (e : m ≃ n) :
    hermPosIndex (A.submatrix e e) = hermPosIndex A := by
  refine le_antisymm (hermPosIndex_submatrix_equiv_le A e) ?_
  have h := hermPosIndex_submatrix_equiv_le (A.submatrix e e) e.symm
  rwa [submatrix_submatrix, e.self_comp_symm, submatrix_id_id] at h

/-- The negative index is invariant under reindexing. -/
theorem hermNegIndex_submatrix_equiv (A : Matrix n n ℂ) (e : m ≃ n) :
    hermNegIndex (A.submatrix e e) = hermNegIndex A :=
  hermPosIndex_submatrix_equiv (-A) e

end Reindex

/-! ### Jacobi's signature rule -/

/-- **Haynsworth step along a leading minor.** Adjoining one row and column to a nonsingular
Hermitian leading block adds one negative direction exactly when the ratio of consecutive leading
minors is negative. -/
theorem hermNegIndex_succ_leading {k : ℕ} (A : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ)
    (hA : A.IsHermitian) (h0 : (A.submatrix Fin.castSucc Fin.castSucc).det ≠ 0) :
    hermNegIndex A = hermNegIndex (A.submatrix Fin.castSucc Fin.castSucc) +
      if (A.det / (A.submatrix Fin.castSucc Fin.castSucc).det).re < 0 then 1 else 0 := by
  set A' := A.submatrix Fin.castSucc Fin.castSucc with hA'def
  let e : Fin k ⊕ Fin 1 ≃ Fin (k + 1) := finSumFinEquiv
  set M := A.submatrix e e with hMdef
  set B := M.toBlocks₁₂
  set C := M.toBlocks₂₂
  have hM : M = fromBlocks A' B Bᴴ C := by
    conv_lhs => rw [← fromBlocks_toBlocks M]
    congr 1
    ext i j
    simp only [toBlocks₂₁, B, toBlocks₁₂, of_apply, conjTranspose_apply, M, submatrix_apply]
    exact (hA.apply _ _).symm
  have hA'H : A'.IsHermitian := hA.submatrix _
  have hCH : C.IsHermitian := hA.submatrix (e ∘ Sum.inr)
  have hAu : IsUnit A' := (Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr h0)
  set S := C - Bᴴ * A'⁻¹ * B with hSdef
  have hSH : S.IsHermitian := isHermitian_schurComplement hA'H B hCH
  have hneg : hermNegIndex A = hermNegIndex A' + hermNegIndex S := by
    rw [← hermNegIndex_submatrix_equiv A e, ← hMdef, hM, haynsworth_negIndex hAu hA'H B hCH]
  have hdet : A.det = A'.det * S 0 0 := by
    letI : Invertible A' := Matrix.invertibleOfIsUnitDet A' (isUnit_iff_ne_zero.mpr h0)
    rw [← det_submatrix_equiv_self e A, ← hMdef, hM, det_fromBlocks₁₁, invOf_eq_nonsing_inv,
      Matrix.det_fin_one]
  have hS00 : S 0 0 = A.det / A'.det := by
    rw [hdet]; field_simp
  have hSdiag : S = diagonal (fun _ => ((S 0 0).re : ℂ)) := by
    ext i j
    fin_cases i; fin_cases j
    have h := hSH.coe_re_apply_self 0
    simp only [RCLike.re_to_complex] at h
    simpa using h.symm
  rw [hneg, hSdiag, negIndex_diagonal, ← hS00]
  congr 1
  split_ifs with h
  · simp [h]
  · simp [h]

theorem isHermitian_map_ofReal {n : Type*} {A : Matrix n n ℝ} (hA : A.IsSymm) :
    (A.map ((↑) : ℝ → ℂ)).IsHermitian := by
  ext i j
  simp [conjTranspose_apply, hA.apply j i]

theorem det_map_ofReal {n : Type*} [Fintype n] [DecidableEq n] (A : Matrix n n ℝ) :
    (A.map ((↑) : ℝ → ℂ)).det = (A.det : ℂ) :=
  (RingHom.map_det Complex.ofRealHom A).symm

/-- A nonsingular Hermitian matrix has zero null index. -/
theorem hermNullIndex_eq_zero_of_det_ne_zero {n : Type*} [Fintype n] [DecidableEq n]
    {H : Matrix n n ℂ} (h : H.det ≠ 0) : hermNullIndex H = 0 := by
  rw [hermNullIndex, Submodule.finrank_eq_zero]
  refine LinearMap.ker_eq_bot'.mpr fun v hv => ?_
  by_contra hv0
  exact h (Matrix.exists_mulVec_eq_zero_iff.mp ⟨v, hv0, hv⟩)

/-- **Jacobi's alternating signature rule.** A real symmetric matrix whose leading `k × k` minors
all have sign `(-1)^{k(k-1)/2}` has inertia `(⌈N/2⌉, ⌊N/2⌋, 0)`. -/
theorem inertia_of_alternating_leading_minors {N : ℕ} (A : Matrix (Fin N) (Fin N) ℝ)
    (hA : A.IsSymm)
    (hsign : ∀ k (hk : k ≤ N),
      0 < (-1 : ℝ) ^ (k * (k - 1) / 2) * (A.submatrix (Fin.castLE hk) (Fin.castLE hk)).det) :
    hermNegIndex (A.map ((↑) : ℝ → ℂ)) = N / 2 ∧
      hermPosIndex (A.map ((↑) : ℝ → ℂ)) = (N + 1) / 2 ∧
      hermNullIndex (A.map ((↑) : ℝ → ℂ)) = 0 := by
  have hdetN : A.det ≠ 0 := by
    have h := hsign N le_rfl
    have hid : A.submatrix (Fin.castLE (le_refl N)) (Fin.castLE (le_refl N)) = A := by
      ext i j; rfl
    rw [hid] at h
    intro h0; rw [h0, mul_zero] at h; exact lt_irrefl _ h
  have hnull : hermNullIndex (A.map ((↑) : ℝ → ℂ)) = 0 :=
    hermNullIndex_eq_zero_of_det_ne_zero (by rw [det_map_ofReal]; exact_mod_cast hdetN)
  have hneg : hermNegIndex (A.map ((↑) : ℝ → ℂ)) = N / 2 := by
    induction N with
    | zero =>
        have h := posIndex_add_negIndex_add_nullIndex (isHermitian_map_ofReal hA)
        simp only [Fintype.card_fin] at h
        omega
    | succ N ih =>
        set A' := A.submatrix Fin.castSucc Fin.castSucc with hA'def
        have hA'S : A'.IsSymm := hA.submatrix _
        have hsign' : ∀ k (hk : k ≤ N),
            0 < (-1 : ℝ) ^ (k * (k - 1) / 2) *
              (A'.submatrix (Fin.castLE hk) (Fin.castLE hk)).det := by
          intro k hk
          have h := hsign k (hk.trans (Nat.le_succ N))
          have e : A'.submatrix (Fin.castLE hk) (Fin.castLE hk) =
              A.submatrix (Fin.castLE (hk.trans (Nat.le_succ N)))
                (Fin.castLE (hk.trans (Nat.le_succ N))) := by
            ext i j; rfl
          rwa [e]
        have hdet' : A'.det ≠ 0 := by
          have h := hsign' N le_rfl
          have hid : A'.submatrix (Fin.castLE (le_refl N)) (Fin.castLE (le_refl N)) = A' := by
            ext i j; rfl
          rw [hid] at h
          intro h0; rw [h0, mul_zero] at h; exact lt_irrefl _ h
        have hstep := hermNegIndex_succ_leading (A.map ((↑) : ℝ → ℂ))
          (isHermitian_map_ofReal hA)
          (by
            change (A'.map ((↑) : ℝ → ℂ)).det ≠ 0
            rw [det_map_ofReal]; exact_mod_cast hdet')
        change hermNegIndex (A.map ((↑) : ℝ → ℂ)) = hermNegIndex (A'.map ((↑) : ℝ → ℂ)) + _
          at hstep
        rw [hstep, ih A' hA'S hsign' hdet' (hermNullIndex_eq_zero_of_det_ne_zero (by
          rw [det_map_ofReal]; exact_mod_cast hdet'))]
        have hsubm : (A.map ((↑) : ℝ → ℂ)).submatrix Fin.castSucc Fin.castSucc =
            A'.map ((↑) : ℝ → ℂ) := rfl
        rw [hsubm, det_map_ofReal, det_map_ofReal, ← Complex.ofReal_div, Complex.ofReal_re]
        have hN1 := hsign (N + 1) le_rfl
        have hid : A.submatrix (Fin.castLE (le_refl (N + 1))) (Fin.castLE (le_refl (N + 1))) = A := by
          ext i j; rfl
        rw [hid] at hN1
        have hN := hsign' N le_rfl
        have hid' : A'.submatrix (Fin.castLE (le_refl N)) (Fin.castLE (le_refl N)) = A' := by
          ext i j; rfl
        rw [hid'] at hN
        have hexp : (N + 1) * (N + 1 - 1) / 2 = N * (N - 1) / 2 + N := by
          rw [← Nat.choose_two_right, ← Nat.choose_two_right, Nat.choose_succ_succ',
            Nat.choose_one_right]
          ring
        rw [hexp, pow_add] at hN1
        set ε := (-1 : ℝ) ^ (N * (N - 1) / 2)
        have hε : ε * ε = 1 := by
          rw [← pow_add, ← two_mul, pow_mul]; norm_num
        have hratio : 0 < (-1 : ℝ) ^ N * (A.det / A'.det) := by
          have hε0 : ε ≠ 0 := by
            intro h; rw [h, zero_mul] at hε; exact zero_ne_one hε
          have : (-1 : ℝ) ^ N * (A.det / A'.det) = (ε * (-1) ^ N * A.det) / (ε * A'.det) := by
            rw [mul_assoc ε, mul_div_mul_left _ _ hε0, mul_div_assoc]
          rw [this]; exact div_pos hN1 hN
        rcases Nat.even_or_odd N with hev | hodd
        · rw [hev.neg_one_pow, one_mul] at hratio
          rw [if_neg (not_lt.mpr hratio.le)]
          obtain ⟨r, rfl⟩ := hev; omega
        · rw [hodd.neg_one_pow, neg_one_mul, neg_pos] at hratio
          rw [if_pos hratio]
          obtain ⟨r, rfl⟩ := hodd; omega
  refine ⟨hneg, ?_, hnull⟩
  have h := posIndex_add_negIndex_add_nullIndex (isHermitian_map_ofReal hA)
  simp only [Fintype.card_fin, hneg, hnull] at h
  omega

/-! ### Strict sign of real-exponential Vandermonde determinants -/

private theorem pos_of_segment {f : ℝ → ℝ} (hf : ContinuousOn f (Set.Icc 0 1))
    (hne : ∀ t ∈ Set.Icc (0 : ℝ) 1, f t ≠ 0) (h0 : 0 < f 0) : 0 < f 1 := by
  by_contra h
  obtain ⟨t, ht, hft⟩ := intermediate_value_Icc' zero_le_one hf ⟨not_lt.mp h, h0.le⟩
  exact hne t ht hft

private theorem segment_lt {a₀ a t : ℝ} (h₀ : 0 < a₀) (h : 0 < a) (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    0 < (1 - t) * a₀ + t * a := by
  rcases lt_or_eq_of_le ht.2 with h1 | h1
  · nlinarith [mul_pos (sub_pos.2 h1) h₀, mul_nonneg ht.1 h.le]
  · subst h1; simpa using h

private theorem continuous_det_segment {N : ℕ} (α₀ α y : Fin N → ℝ) :
    Continuous fun t : ℝ =>
      (realExponentialVandermonde (fun j => (1 - t) * α₀ j + t * α j) y).det :=
  Continuous.matrix_det <| continuous_pi fun i => continuous_pi fun j => by
    simp only [realExponentialVandermonde]; fun_prop

private theorem det_segment_endpoints {N : ℕ} (α₀ α y : Fin N → ℝ) :
    (realExponentialVandermonde (fun j => (1 - 0) * α₀ j + 0 * α j) y).det =
        (realExponentialVandermonde α₀ y).det ∧
      (realExponentialVandermonde (fun j => (1 - 1) * α₀ j + 1 * α j) y).det =
        (realExponentialVandermonde α y).det := by
  constructor <;> congr 2 <;> funext j <;> ring

/-- **Strict total positivity of the exponential kernel.** For strictly increasing exponents and
nodes, `det [e^{α_j y_i}] > 0`: the determinant never vanishes on the convex set of ordered
exponents, and at `α_j = j` it is the Vandermonde determinant of the increasing values `e^{y_i}`. -/
theorem det_realExponentialVandermonde_pos {N : ℕ} {α y : Fin N → ℝ} (hα : StrictMono α)
    (hy : StrictMono y) : 0 < (realExponentialVandermonde α y).det := by
  let α₀ : Fin N → ℝ := fun j => ((j : ℕ) : ℝ)
  have h₀ : StrictMono α₀ := fun i j hij => by
    simp only [α₀]; exact_mod_cast hij
  have hbase : 0 < (realExponentialVandermonde α₀ y).det := by
    have e : realExponentialVandermonde α₀ y = vandermonde fun i => Real.exp (y i) := by
      ext i j; simp [realExponentialVandermonde, α₀, vandermonde_apply, Real.exp_nat_mul]
    rw [e, det_vandermonde]
    exact Finset.prod_pos fun i _ => Finset.prod_pos fun j hj =>
      sub_pos.2 (Real.exp_lt_exp.2 (hy (Finset.mem_Ioi.1 hj)))
  obtain ⟨e0, e1⟩ := det_segment_endpoints α₀ α y
  have h := pos_of_segment (continuous_det_segment α₀ α y).continuousOn
    (fun t ht => det_realExponentialVandermonde_ne_zero _ y
      (fun i j hij => by
        have := segment_lt (sub_pos.2 (h₀ hij)) (sub_pos.2 (hα hij)) ht
        linarith) hy)
    (by rw [e0]; exact hbase)
  rwa [e1] at h

/-- `∑_i #{j > i} = N(N-1)/2`. -/
theorem sum_card_Ioi_fin (N : ℕ) : ∑ i : Fin N, (Finset.Ioi i).card = N * (N - 1) / 2 := by
  simp_rw [Fin.card_Ioi]
  rw [Fin.sum_univ_eq_sum_range (fun i => N - 1 - i) N,
    Finset.sum_range_reflect (fun i => i) N]
  have h := Finset.sum_range_id_mul_two N
  generalize N * (N - 1) = T at h ⊢
  omega

/-- Real-exponential Vandermonde determinants with strictly decreasing exponents are nonzero
(reverse the columns). -/
theorem det_realExponentialVandermonde_ne_zero_of_anti {N : ℕ} {β y : Fin N → ℝ}
    (hβ : StrictAnti β) (hy : StrictMono y) : (realExponentialVandermonde β y).det ≠ 0 := by
  have hrev : StrictMono (β ∘ Fin.revPerm) := fun i j hij => by
    simp only [Function.comp_apply, Fin.revPerm_apply]
    exact hβ (Fin.rev_lt_rev.2 hij)
  have h := det_realExponentialVandermonde_ne_zero _ y hrev hy
  have e : realExponentialVandermonde (β ∘ Fin.revPerm) y =
      (realExponentialVandermonde β y).submatrix id Fin.revPerm := rfl
  rw [e, det_permute'] at h
  exact right_ne_zero_of_mul h

/-- For strictly decreasing exponents, `(-1)^{N(N-1)/2} det [e^{β_j y_i}] > 0`. -/
theorem det_realExponentialVandermonde_anti_sign {N : ℕ} {β y : Fin N → ℝ}
    (hβ : StrictAnti β) (hy : StrictMono y) :
    0 < (-1 : ℝ) ^ (N * (N - 1) / 2) * (realExponentialVandermonde β y).det := by
  set ε := (-1 : ℝ) ^ (N * (N - 1) / 2)
  have hε : ε * ε = 1 := by rw [← pow_add, ← two_mul, pow_mul]; norm_num
  let β₀ : Fin N → ℝ := fun j => -((j : ℕ) : ℝ)
  have h₀ : StrictAnti β₀ := fun i j hij => by
    simp only [β₀, neg_lt_neg_iff]; exact_mod_cast hij
  have hbase : 0 < ε * (realExponentialVandermonde β₀ y).det := by
    have e : realExponentialVandermonde β₀ y = vandermonde fun i => Real.exp (-y i) := by
      ext i j
      simp only [realExponentialVandermonde, β₀, vandermonde_apply, ← Real.exp_nat_mul]
      congr 1; ring
    have hprod : ∏ i : Fin N, ∏ j ∈ Finset.Ioi i, (Real.exp (-y j) - Real.exp (-y i)) =
        ε * ∏ i : Fin N, ∏ j ∈ Finset.Ioi i, (Real.exp (-y i) - Real.exp (-y j)) := by
      have : ∀ i : Fin N, ∏ j ∈ Finset.Ioi i, (Real.exp (-y j) - Real.exp (-y i)) =
          (-1) ^ (Finset.Ioi i).card * ∏ j ∈ Finset.Ioi i, (Real.exp (-y i) - Real.exp (-y j)) := by
        intro i
        rw [← Finset.prod_neg]
        exact Finset.prod_congr rfl fun j _ => by ring
      rw [Finset.prod_congr rfl fun i _ => this i, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum,
        sum_card_Ioi_fin]
    rw [e, det_vandermonde, hprod, ← mul_assoc, hε, one_mul]
    exact Finset.prod_pos fun i _ => Finset.prod_pos fun j hj =>
      sub_pos.2 (Real.exp_lt_exp.2 (neg_lt_neg (hy (Finset.mem_Ioi.1 hj))))
  obtain ⟨e0, e1⟩ := det_segment_endpoints β₀ β y
  have h := pos_of_segment (f := fun t =>
      ε * (realExponentialVandermonde (fun j => (1 - t) * β₀ j + t * β j) y).det)
    (continuous_const.mul (continuous_det_segment β₀ β y)).continuousOn
    (fun t ht => mul_ne_zero (by intro h; rw [h, zero_mul] at hε; exact zero_ne_one hε)
      (det_realExponentialVandermonde_ne_zero_of_anti
        (fun i j hij => by
          have := segment_lt (sub_pos.2 (h₀ hij)) (sub_pos.2 (hβ hij)) ht
          linarith) hy))
    (by rw [e0]; exact hbase)
  beta_reduce at h
  rwa [e1] at h

/-- **Sign of the Andréief integrand.** For strictly increasing nodes,
`(-1)^{N(N-1)/2} det[e^{u_j x_i}] det[e^{-u_j x_i}] ≥ 0`, with strict inequality at every
exponent vector with distinct entries. -/
theorem andreief_exp_integrand_sign {N : ℕ} {x : Fin N → ℝ} (hx : StrictMono x)
    (u : Fin N → ℝ) :
    0 ≤ (-1 : ℝ) ^ (N * (N - 1) / 2) * ((realExponentialVandermonde u x).det *
        (realExponentialVandermonde (fun j => -u j) x).det) ∧
      (Function.Injective u → 0 < (-1 : ℝ) ^ (N * (N - 1) / 2) *
        ((realExponentialVandermonde u x).det *
          (realExponentialVandermonde (fun j => -u j) x).det)) := by
  by_cases hu : Function.Injective u
  · set σ := Tuple.sort u
    have hw : StrictMono (u ∘ σ) :=
      (Tuple.monotone_sort u).strictMono_of_injective (hu.comp σ.injective)
    have e1 : realExponentialVandermonde (u ∘ σ) x =
        (realExponentialVandermonde u x).submatrix id σ := rfl
    have e2 : realExponentialVandermonde (fun j => -(u ∘ σ) j) x =
        (realExponentialVandermonde (fun j => -u j) x).submatrix id σ := rfl
    have hs : ((Equiv.Perm.sign σ : ℤ) : ℝ) * ((Equiv.Perm.sign σ : ℤ) : ℝ) = 1 := by
      rw [← Int.cast_mul, ← Units.val_mul, Int.units_mul_self, Units.val_one, Int.cast_one]
    have hpos := mul_pos (det_realExponentialVandermonde_pos hw hx)
      (det_realExponentialVandermonde_anti_sign hw.neg hx)
    rw [e1, e2, det_permute', det_permute'] at hpos
    have key : (-1 : ℝ) ^ (N * (N - 1) / 2) * ((realExponentialVandermonde u x).det *
        (realExponentialVandermonde (fun j => -u j) x).det) =
        ((Equiv.Perm.sign σ : ℤ) : ℝ) * (realExponentialVandermonde u x).det *
          ((-1 : ℝ) ^ (N * (N - 1) / 2) * (((Equiv.Perm.sign σ : ℤ) : ℝ) *
            (realExponentialVandermonde (fun j => -u j) x).det)) := by
      linear_combination (-(-1 : ℝ) ^ (N * (N - 1) / 2) * (realExponentialVandermonde u x).det *
        (realExponentialVandermonde (fun j => -u j) x).det) * hs
    rw [key]
    exact ⟨hpos.le, fun _ => hpos⟩
  · obtain ⟨i, j, hij, hne⟩ := Function.not_injective_iff.mp hu
    have h0 : (realExponentialVandermonde u x).det = 0 :=
      det_zero_of_column_eq hne fun k => by simp [realExponentialVandermonde, hij]
    rw [h0, zero_mul, mul_zero]
    exact ⟨le_rfl, fun h => absurd h hu⟩

/-! ### Exponential kernels of compactly carried measures -/

/-- The real-exponential kernel matrix `K_ij = ∫ e^{u(x_i - x_j)} dμ(u)`. -/
def expKernelMatrix (μ : Measure ℝ) {N : ℕ} (x : Fin N → ℝ) : Matrix (Fin N) (Fin N) ℝ :=
  Matrix.of fun i j => ∫ u, Real.exp (u * (x i - x j)) ∂μ

theorem integrable_exp_mul_of_ae_abs_le {μ : Measure ℝ} [IsFiniteMeasure μ] {b : ℝ}
    (hb : ∀ᵐ u ∂μ, |u| ≤ b) (s : ℝ) : Integrable (fun u => Real.exp (u * s)) μ :=
  Integrable.of_bound (by fun_prop : Continuous fun u : ℝ => Real.exp (u * s)).aestronglyMeasurable
    (Real.exp (b * |s|)) (hb.mono fun u hu => by
      rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      refine Real.exp_le_exp.2 ?_
      calc u * s ≤ |u * s| := le_abs_self _
        _ = |u| * |s| := abs_mul _ _
        _ ≤ b * |s| := mul_le_mul_of_nonneg_right hu (abs_nonneg _))

/-- **Andréief form of the determinant.**
`det K = (1/N!) ∫ det[e^{u_j x_i}] det[e^{-u_j x_i}] dμ^N(u)`. -/
theorem det_expKernelMatrix_eq_integral (μ : Measure ℝ) [IsFiniteMeasure μ] {b : ℝ}
    (hb : ∀ᵐ u ∂μ, |u| ≤ b) {N : ℕ} (x : Fin N → ℝ) :
    (expKernelMatrix μ x).det = 1 / N.factorial * ∫ u : Fin N → ℝ,
      (realExponentialVandermonde u x).det *
        (realExponentialVandermonde (fun j => -u j) x).det ∂(Measure.pi fun _ => μ) := by
  have hmul : ∀ i j (u : ℝ), Real.exp (u * x i) * Real.exp (-u * x j) =
      Real.exp (u * (x i - x j)) := fun i j u => by rw [← Real.exp_add]; ring_nf
  have hK : expKernelMatrix μ x =
      Matrix.of fun i j => ∫ u, Real.exp (u * x i) * Real.exp (-u * x j) ∂μ := by
    ext i j; simp only [expKernelMatrix, of_apply, hmul]
  rw [hK, zeta5_andreief μ (fun i u => Real.exp (u * x i)) (fun j u => Real.exp (-u * x j))
    fun i j => by simpa only [hmul] using integrable_exp_mul_of_ae_abs_le hb (x i - x j)]
  rfl

/-- **Determinant sign.** For a finite measure carried by `[-b,b]` whose support contains at least
`N` points and strictly increasing nodes, `(-1)^{N(N-1)/2} det K > 0`. -/
theorem expKernelMatrix_det_sign (μ : Measure ℝ) [IsFiniteMeasure μ] {b : ℝ}
    (hb : ∀ᵐ u ∂μ, |u| ≤ b) {N : ℕ}
    (hsupp : ∃ c : Fin N → ℝ, Function.Injective c ∧ ∀ i, ∀ r > 0, 0 < μ (Metric.ball (c i) r))
    {x : Fin N → ℝ} (hx : StrictMono x) :
    0 < (-1 : ℝ) ^ (N * (N - 1) / 2) * (expKernelMatrix μ x).det := by
  set ε := (-1 : ℝ) ^ (N * (N - 1) / 2)
  set F : (Fin N → ℝ) → ℝ := fun u => ε * ((realExponentialVandermonde u x).det *
    (realExponentialVandermonde (fun j => -u j) x).det)
  have hFcont : Continuous F := by
    refine continuous_const.mul ((Continuous.matrix_det ?_).mul (Continuous.matrix_det ?_)) <;>
    exact continuous_pi fun i => continuous_pi fun j => by
      simp only [realExponentialVandermonde]; fun_prop
  have hnn : 0 ≤ F := fun u => (andreief_exp_integrand_sign hx u).1
  have hbox : ∀ᵐ u ∂(Measure.pi fun _ : Fin N => μ),
      u ∈ Set.univ.pi fun _ => Set.Icc (-b) b := by
    have h : ∀ i, ∀ᵐ u ∂(Measure.pi fun _ : Fin N => μ), u i ∈ Set.Icc (-b) b := fun i =>
      Measure.tendsto_eval_ae_ae.eventually (hb.mono fun t ht => abs_le.mp ht)
    filter_upwards [ae_all_iff.mpr h] with u hu
    exact fun i _ => hu i
  obtain ⟨C, hC⟩ := (isCompact_univ_pi fun _ : Fin N => isCompact_Icc (a := -b) (b := b)
    ).exists_bound_of_continuousOn hFcont.continuousOn
  have hint : Integrable F (Measure.pi fun _ => μ) :=
    Integrable.of_bound hFcont.aestronglyMeasurable C (hbox.mono fun u hu => hC u hu)
  obtain ⟨c, hc, hball⟩ := hsupp
  obtain ⟨r, hr, hr0⟩ : ∃ r : ℝ, (∀ i j, i ≠ j → 2 * r < |c i - c j|) ∧ 0 < r := by
    have h : ∀ᶠ r in 𝓝[>] (0 : ℝ), ∀ p : Fin N × Fin N, p.1 ≠ p.2 → 2 * r < |c p.1 - c p.2| := by
      rw [Filter.eventually_all]
      intro p
      by_cases hp : p.1 = p.2
      · exact Filter.Eventually.of_forall fun _ h => absurd hp h
      · have hpos : 0 < |c p.1 - c p.2| := abs_pos.2 (sub_ne_zero.2 (hc.ne hp))
        have ht : Tendsto (fun r : ℝ => 2 * r) (𝓝[>] 0) (𝓝 0) := by
          have := ((continuous_const_mul (2 : ℝ)).tendsto 0).mono_left
            (nhdsWithin_le_nhds (s := Set.Ioi (0 : ℝ)))
          simpa using this
        exact (ht.eventually (eventually_lt_nhds hpos)).mono fun r hr _ => hr
    obtain ⟨r, hr1, hr2⟩ := (h.and self_mem_nhdsWithin).exists
    exact ⟨r, fun i j hij => hr1 (i, j) hij, hr2⟩
  have hpos : 0 < ∫ u, F u ∂(Measure.pi fun _ => μ) := by
    rw [integral_pos_iff_support_of_nonneg hnn hint]
    refine lt_of_lt_of_le ?_ (measure_mono (s := Set.univ.pi fun i => Metric.ball (c i) r) ?_)
    · rw [Measure.pi_pi]
      exact pos_iff_ne_zero.2 (Finset.prod_ne_zero_iff.2 fun i _ => (hball i r hr0).ne')
    · intro u hu
      have hinj : Function.Injective u := by
        intro i j hij
        by_contra hne
        have hi := hu i (Set.mem_univ _)
        have hj := hu j (Set.mem_univ _)
        rw [Metric.mem_ball, Real.dist_eq] at hi hj
        have hsum : c i - c j = -(u i - c i) + (u j - c j) := by rw [hij]; ring
        have htri : |c i - c j| ≤ |u i - c i| + |u j - c j| := by
          rw [hsum]; exact (abs_add_le _ _).trans (by rw [abs_neg])
        linarith [hr i j hne]
      exact ((andreief_exp_integrand_sign hx u).2 hinj).ne'
  rw [det_expKernelMatrix_eq_integral μ hb x, ← mul_assoc, mul_comm ε, mul_assoc,
    ← integral_const_mul]
  exact mul_pos (by positivity) hpos

/-- A symmetric measure gives a symmetric kernel. -/
theorem expKernelMatrix_isSymm (μ : Measure ℝ) [μ.IsNegInvariant] {N : ℕ} (x : Fin N → ℝ) :
    (expKernelMatrix μ x).IsSymm := by
  refine Matrix.IsSymm.ext fun i j => ?_
  simp only [expKernelMatrix, of_apply]
  rw [← integral_neg_eq_self (fun u => Real.exp (u * (x i - x j))) μ]
  congr 1; funext u; ring_nf

/-- **Alternating inertia.** For a symmetric finite measure carried by `[-b,b]` whose support
contains at least `N` points and strictly increasing nodes, the exponential kernel has
`⌊N/2⌋` negative and `⌈N/2⌉` positive directions and is nonsingular. -/
theorem expKernelMatrix_inertia (μ : Measure ℝ) [IsFiniteMeasure μ] [μ.IsNegInvariant] {b : ℝ}
    (hb : ∀ᵐ u ∂μ, |u| ≤ b) {N : ℕ}
    (hsupp : ∃ c : Fin N → ℝ, Function.Injective c ∧ ∀ i, ∀ r > 0, 0 < μ (Metric.ball (c i) r))
    {x : Fin N → ℝ} (hx : StrictMono x) :
    hermNegIndex ((expKernelMatrix μ x).map ((↑) : ℝ → ℂ)) = N / 2 ∧
      hermPosIndex ((expKernelMatrix μ x).map ((↑) : ℝ → ℂ)) = (N + 1) / 2 ∧
      hermNullIndex ((expKernelMatrix μ x).map ((↑) : ℝ → ℂ)) = 0 := by
  obtain ⟨c, hc, hball⟩ := hsupp
  exact inertia_of_alternating_leading_minors _ (expKernelMatrix_isSymm μ x) fun k hk =>
    expKernelMatrix_det_sign μ hb (x := x ∘ Fin.castLE hk)
      ⟨c ∘ Fin.castLE hk, hc.comp (Fin.castLE_injective hk), fun i => hball _⟩
      (hx.comp (Fin.strictMono_castLE hk))

open scoped ComplexOrder in
/-- **Fourier contrast.** With imaginary frequencies the kernel `∫ e^{iu(x_i - x_j)} dμ(u)` of any
finite measure is a Gram matrix in `L²(μ)`, hence positive semidefinite. -/
theorem fourierKernelMatrix_posSemidef (μ : Measure ℝ) [IsFiniteMeasure μ] {N : ℕ}
    (x : Fin N → ℝ) :
    (Matrix.of fun i j => ∫ u, Complex.exp (Complex.I * u * (x i - x j)) ∂μ).PosSemidef := by
  have hmem : ∀ i, MemLp (fun u : ℝ => Complex.exp (-(Complex.I * u * x i))) 2 μ := fun i =>
    MemLp.of_bound (by fun_prop : Continuous fun u : ℝ =>
      Complex.exp (-(Complex.I * u * x i))).aestronglyMeasurable 1
      (ae_of_all _ fun u => by
        rw [Complex.norm_exp]
        simp)
  let e : Fin N → Lp ℂ 2 μ := fun i => (hmem i).toLp _
  have he : (Matrix.of fun i j => ∫ u, Complex.exp (Complex.I * u * (x i - x j)) ∂μ) =
      Matrix.gram ℂ e := by
    ext i j
    rw [Matrix.gram_apply, L2.inner_def, of_apply]
    refine integral_congr_ae ?_
    filter_upwards [(hmem i).coeFn_toLp, (hmem j).coeFn_toLp] with u hi hj
    rw [hi, hj, show ∀ a b : ℂ, inner ℂ a b = (starRingEnd ℂ) a * b from
      fun a b => by simp [mul_comm], ← Complex.exp_conj, ← Complex.exp_add]
    congr 1
    simp only [map_neg, map_mul, Complex.conj_I, Complex.conj_ofReal]
    ring
  rw [he]
  exact Matrix.posSemidef_gram ℂ e

/-! ### Finite-rank corrections and finite-index carriers -/

/-- **Rank bound on index repair.** Adding a matrix of rank `r` lowers the negative index by at
most `r`: on the intersection of a maximal negative subspace with the kernel of the correction the
two forms agree. -/
theorem hermNegIndex_le_add_rank {n : Type*} [Fintype n] [DecidableEq n]
    (H B : Matrix n n ℂ) : hermNegIndex H ≤ hermNegIndex (H + B) + B.rank := by
  obtain ⟨W, hW, hneg⟩ := exists_isPosDefOn_finrank_eq_posIndex (-H)
  set K := LinearMap.ker B.mulVecLin
  have hrk : B.rank + Module.finrank ℂ K = Fintype.card n := by
    rw [Matrix.rank, LinearMap.finrank_range_add_finrank_ker, Module.finrank_fintype_fun_eq_card]
  have hsup := Submodule.finrank_sup_add_finrank_inf_eq W K
  have hle : Module.finrank ℂ ↥(W ⊔ K) ≤ Fintype.card n := by
    rw [← Module.finrank_fintype_fun_eq_card (R := ℂ)]; exact Submodule.finrank_le _
  have hinf : Module.finrank ℂ ↥(W ⊓ K) ≤ hermNegIndex (H + B) := by
    refine finrank_le_posIndex fun x hx hx0 => ?_
    have hBx : B *ᵥ x = 0 := hx.2
    have h1 := hneg x hx.1 hx0
    have h2 : hermQuad (-(H + B)) x = hermQuad (-H) x := by
      simp only [hermQuad, Matrix.neg_mulVec, Matrix.add_mulVec, hBx, add_zero]
    rwa [h2]
  change hermPosIndex (-H) ≤ _
  omega

/-- The complexification of a real matrix has complex rank at most its real rank. -/
theorem rank_map_ofReal_le {m n : Type*} [Fintype m] [Fintype n] (A : Matrix m n ℝ) :
    (A.map ((↑) : ℝ → ℂ)).rank ≤ A.rank := by
  classical
  rw [Matrix.rank_eq_finrank_span_cols, Matrix.rank_eq_finrank_span_cols]
  set W := Submodule.span ℝ (Set.range Aᵀ)
  let b := Module.finBasis ℝ W
  let v : Fin (Module.finrank ℝ W) → (m → ℂ) := fun k i => ((b k : m → ℝ) i : ℂ)
  have hsub : Submodule.span ℂ (Set.range (A.map ((↑) : ℝ → ℂ))ᵀ) ≤
      Submodule.span ℂ (Set.range v) := by
    rw [Submodule.span_le]
    rintro _ ⟨j, rfl⟩
    have hj : (⟨Aᵀ j, Submodule.subset_span ⟨j, rfl⟩⟩ : W) =
        ∑ k, b.repr ⟨Aᵀ j, Submodule.subset_span ⟨j, rfl⟩⟩ k • b k := (b.sum_repr _).symm
    have hcol : (A.map ((↑) : ℝ → ℂ))ᵀ j =
        ∑ k, ((b.repr ⟨Aᵀ j, Submodule.subset_span ⟨j, rfl⟩⟩ k : ℝ) : ℂ) • v k := by
      ext i
      have := congrArg (fun w : W => (w : m → ℝ) i) hj
      simp only [Submodule.coe_sum, Submodule.coe_smul, Finset.sum_apply, Pi.smul_apply,
        smul_eq_mul] at this
      simp only [transpose_apply, map_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, v]
      rw [show A i j = Aᵀ j i from rfl, this]
      push_cast
      rfl
    rw [SetLike.mem_coe, hcol]
    exact Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩)
  calc Module.finrank ℂ (Submodule.span ℂ (Set.range (A.map ((↑) : ℝ → ℂ))ᵀ))
      ≤ Module.finrank ℂ (Submodule.span ℂ (Set.range v)) := Submodule.finrank_mono hsub
    _ ≤ Fintype.card (Fin (Module.finrank ℝ W)) := by
        have h := finrank_range_le_card (R := ℂ) v; exact h
    _ = Module.finrank ℝ W := Fintype.card_fin _

/-- **No finite-index carrier.** If the finite sections of a kernel have unbounded negative index,
the kernel is not the Hermitian form of any family of vectors in a space whose negative-definite
subspaces have dimension at most `κ` (a Pontryagin space of index `κ`, for example). -/
theorem no_finite_negIndex_carrier {X : Type*} (K : X → X → ℂ)
    (hK : ∀ κ : ℕ, ∃ (N : ℕ) (z : Fin N → X),
      κ < hermNegIndex (Matrix.of fun i j => K (z i) (z j)))
    {V : Type*} [AddCommGroup V] [Module ℂ V] (B : V →ₗ⋆[ℂ] V →ₗ[ℂ] ℂ) (κ : ℕ)
    (hκ : ∀ W : Submodule ℂ V, (∀ v ∈ W, v ≠ 0 → (B v v).re < 0) →
      Module.finrank ℂ W ≤ κ) :
    ¬ ∃ φ : X → V, ∀ x y, B (φ x) (φ y) = K x y := by
  rintro ⟨φ, hφ⟩
  obtain ⟨N, z, hN⟩ := hK κ
  set H : Matrix (Fin N) (Fin N) ℂ := Matrix.of fun i j => K (z i) (z j)
  obtain ⟨W, hW, hneg⟩ := exists_isPosDefOn_finrank_eq_posIndex (-H)
  let T : (Fin N → ℂ) →ₗ[ℂ] V := Fintype.linearCombination ℂ (fun i => φ (z i))
  have hT : ∀ c, T c = ∑ i, c i • φ (z i) := fun c => Fintype.linearCombination_apply ℂ _ c
  have hform : ∀ c, B (T c) (T c) = star c ⬝ᵥ H *ᵥ c := by
    intro c
    simp only [hT, map_sum, map_smulₛₗ, LinearMap.sum_apply, LinearMap.smul_apply, hφ,
      dotProduct, mulVec, H, of_apply, Pi.star_apply, Finset.mul_sum, smul_eq_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    simp only [RingHom.id_apply, Complex.star_def]
    ring
  have hnegT : ∀ c ∈ W, c ≠ 0 → (B (T c) (T c)).re < 0 := by
    intro c hc hc0
    have h := hneg c hc hc0
    rw [hermQuad_neg] at h
    rw [hform]
    change -(star c ⬝ᵥ H *ᵥ c).re > 0 at h
    linarith
  have hinj : Set.InjOn T W := by
    intro c hc d hd hcd
    by_contra hne
    have hsub : c - d ∈ W := W.sub_mem hc hd
    have h := hnegT (c - d) hsub (sub_ne_zero.mpr hne)
    rw [map_sub, hcd, sub_self, map_zero, Complex.zero_re] at h
    exact lt_irrefl _ h
  have hker : LinearMap.ker (T.domRestrict W) = ⊥ := by
    refine LinearMap.ker_eq_bot'.mpr fun w hw => ?_
    exact Subtype.ext (hinj w.2 W.zero_mem (by simpa using hw))
  have hdim : Module.finrank ℂ (W.map T) = Module.finrank ℂ W := by
    rw [← LinearMap.range_domRestrict]
    exact LinearMap.finrank_range_of_inj (LinearMap.ker_eq_bot.mp hker)
  have hbound := hκ (W.map T) (by
    rintro _ ⟨c, hc, rfl⟩ hv
    exact hnegT c hc (by rintro rfl; exact hv (map_zero T)))
  rw [hdim, hW] at hbound
  exact absurd hbound (not_le.mpr hN)

end

end GaloisForLFunctions.HTGeometry
