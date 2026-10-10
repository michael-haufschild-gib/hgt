import GaloisForLFunctions.HTGeometry.ToeplitzTotalPositivityOrderTwo
import GaloisForLFunctions.HTGeometry.CauchyBinet

/-!
# Toeplitz total positivity of order `k`

For `a : ℕ → ℝ` (extended by zero to `ℤ`) the Toeplitz minor with rows `i` and columns `j` is
`det (a (j c − i r))_{r,c}` (`toeplitzMinor`).  The sequence is `PF_k` (`PFSeq k a`) when every such
minor of order `m ≤ k` with strictly increasing rows and columns is nonnegative.

* `PFSeq.conv`: `PF_k` is closed under the Cauchy product.  The minor of `a ∗ b` is `det (A · B)`
  with `A r l = a (l − i r)`, `B l c = b (j c − l)` (`toeplitzMinor_cauchyConv`).  By the
  symmetrised Cauchy–Binet formula `m! det (A · B) = Σ_f det (A ∘ f) det (f ∘ B)`.  A non-injective
  `f` repeats a column of `A ∘ f`.  An injective `f` is `g ∘ σ⁻¹` with `g` strictly increasing
  (`Tuple.sort`), and both factors pick up `sign σ`.  So every term is a product of two Toeplitz
  minors of `a` and `b` with increasing indices.
* `PFSeq.of_tendsto`: closed under pointwise limits (the determinant is continuous).
* `PFSeq.of_le`, `PFSeq.two_of_turanSeq`: monotone in `k`, and Turán sequences are `PF_2`.
-/

open Finset Filter Topology Matrix

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- The Toeplitz minor of `a` with rows `i` and columns `j`. -/
def toeplitzMinor (a : ℕ → ℝ) (m : ℕ) (i j : Fin m → ℕ) : ℝ :=
  Matrix.det (Matrix.of fun r c => zext a ((j c : ℤ) - i r))

/-- `PF_k`: every Toeplitz minor of order at most `k` with increasing indices is nonnegative. -/
def PFSeq (k : ℕ) (a : ℕ → ℝ) : Prop :=
  ∀ m ≤ k, ∀ i j : Fin m → ℕ, StrictMono i → StrictMono j → 0 ≤ toeplitzMinor a m i j

/-- The extended Cauchy product as a finite sum over a long enough range. -/
theorem zext_cauchyConv_eq_sum (a b : ℕ → ℝ) (x y : ℕ) {N : ℕ} (hN : y < N) :
    zext (cauchyConv a b) ((y : ℤ) - x) =
      ∑ l ∈ range N, zext a ((l : ℤ) - x) * zext b ((y : ℤ) - l) := by
  by_cases hxy : x ≤ y
  · obtain ⟨N', rfl⟩ : ∃ N', N = x + N' := ⟨N - x, by omega⟩
    rw [Finset.sum_range_add]
    have h0 : ∑ l ∈ range x, zext a ((l : ℤ) - x) * zext b ((y : ℤ) - l) = 0 :=
      sum_eq_zero fun l hl => by
        rw [mem_range] at hl
        rw [zext_of_neg a (by omega), zero_mul]
    rw [h0, zero_add, show ((y : ℤ) - x) = ((y - x : ℕ) : ℤ) by push_cast [hxy]; ring, zext_natCast,
      ← sum_zext_eq_cauchyConv a b (n := y - x) (N := N') (by omega)]
    refine sum_congr rfl fun l _ => ?_
    congr 2
    · push_cast; ring
    · push_cast [hxy]; ring
  · rw [zext_of_neg _ (by omega)]
    symm
    refine sum_eq_zero fun l _ => ?_
    by_cases hl : x ≤ l
    · rw [zext_of_neg b (by omega), mul_zero]
    · rw [zext_of_neg a (by omega), zero_mul]

/-- The Toeplitz minor of a Cauchy product is the determinant of a product of two rectangular
Toeplitz blocks. -/
theorem toeplitzMinor_cauchyConv (a b : ℕ → ℝ) (m : ℕ) (i j : Fin m → ℕ) (N : ℕ)
    (hN : ∀ c, j c < N) :
    toeplitzMinor (cauchyConv a b) m i j =
      ((Matrix.of fun r (l : Fin N) => zext a ((l : ℤ) - i r)) *
        (Matrix.of fun (l : Fin N) c => zext b ((j c : ℤ) - l))).det := by
  unfold toeplitzMinor
  congr 1
  ext r c
  simp only [Matrix.mul_apply, Matrix.of_apply]
  rw [zext_cauchyConv_eq_sum a b (i r) (j c) (hN c)]
  exact (Fin.sum_univ_eq_sum_range (fun l => zext a ((l : ℤ) - i r) * zext b ((j c : ℤ) - l)) N).symm

theorem sign_cast_mul_self {m : ℕ} (σ : Equiv.Perm (Fin m)) :
    ((Equiv.Perm.sign σ : ℤ) : ℝ) * ((Equiv.Perm.sign σ : ℤ) : ℝ) = 1 := by
  rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h <;> rw [h] <;> norm_num

namespace PFSeq

variable {k : ℕ} {a b : ℕ → ℝ}

/-- **`PF_k` is closed under the Cauchy product.** -/
theorem conv (ha : PFSeq k a) (hb : PFSeq k b) : PFSeq k (cauchyConv a b) := by
  intro m hm i j hi hj
  set N := (∑ c, j c) + 1 with hNdef
  have hN : ∀ c, j c < N := fun c =>
    Nat.lt_succ_of_le (Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ c))
  rw [toeplitzMinor_cauchyConv a b m i j N hN]
  set A : Matrix (Fin m) (Fin N) ℝ := Matrix.of fun r (l : Fin N) => zext a ((l : ℤ) - i r)
  set B : Matrix (Fin N) (Fin m) ℝ := Matrix.of fun (l : Fin N) c => zext b ((j c : ℤ) - l)
  have hterm : ∀ f : Fin m → Fin N, 0 ≤ (A.submatrix id f).det * (B.submatrix f id).det := by
    intro f
    by_cases hf : Function.Injective f
    · set σ := Tuple.sort f
      set g : Fin m → Fin N := f ∘ σ with hg
      have hgmono : StrictMono g := (Tuple.monotone_sort f).strictMono_of_injective
        (hf.comp σ.injective)
      have hgval : StrictMono fun c => (g c : ℕ) := Fin.val_strictMono.comp hgmono
      have hA : A.submatrix id f = (A.submatrix id g).submatrix id (σ⁻¹ : Equiv.Perm (Fin m)) := by
        ext r c
        simp [hg]
      have hB : B.submatrix f id = (B.submatrix g id).submatrix (σ⁻¹ : Equiv.Perm (Fin m)) id := by
        ext r c
        simp [hg]
      have hAg : (A.submatrix id g).det = toeplitzMinor a m i (fun c => (g c : ℕ)) := rfl
      have hBg : (B.submatrix g id).det = toeplitzMinor b m (fun r => (g r : ℕ)) j := rfl
      rw [hA, hB, Matrix.det_permute', Matrix.det_permute, hAg, hBg]
      have hs := sign_cast_mul_self (σ⁻¹)
      have e : ((Equiv.Perm.sign σ⁻¹ : ℤ) : ℝ) * toeplitzMinor a m i (fun c => (g c : ℕ)) *
          (((Equiv.Perm.sign σ⁻¹ : ℤ) : ℝ) * toeplitzMinor b m (fun r => (g r : ℕ)) j) =
          toeplitzMinor a m i (fun c => (g c : ℕ)) * toeplitzMinor b m (fun r => (g r : ℕ)) j := by
        calc _ = (((Equiv.Perm.sign σ⁻¹ : ℤ) : ℝ) * ((Equiv.Perm.sign σ⁻¹ : ℤ) : ℝ)) *
              (toeplitzMinor a m i (fun c => (g c : ℕ)) *
                toeplitzMinor b m (fun r => (g r : ℕ)) j) := by ring
          _ = _ := by rw [hs, one_mul]
      rw [e]
      exact mul_nonneg (ha m hm i _ hi hgval) (hb m hm _ j hgval hj)
    · obtain ⟨c, c', hcc, hne⟩ : ∃ c c', f c = f c' ∧ c ≠ c' := by
        simp only [Function.Injective, not_forall] at hf
        obtain ⟨c, c', h1, h2⟩ := hf
        exact ⟨c, c', h1, h2⟩
      rw [Matrix.det_zero_of_column_eq hne fun r => by simp [hcc], zero_mul]
  have hsum := Finset.sum_nonneg fun f (_ : f ∈ Finset.univ) => hterm f
  rw [← GaloisForLFunctions.factorial_mul_det_mul A B] at hsum
  have hfac : (0 : ℝ) < ((Nat.factorial m : ℕ) : ℝ) := by exact_mod_cast Nat.factorial_pos m
  exact (mul_nonneg_iff_of_pos_left hfac).1 hsum

/-- **`PF_k` is closed under pointwise limits.** -/
theorem of_tendsto {ι : Type*} {l : Filter ι} [l.NeBot] {F : ι → ℕ → ℝ} {f : ℕ → ℝ}
    (hF : ∀ n, PFSeq k (F n)) (h : ∀ n, Tendsto (fun i => F i n) l (𝓝 (f n))) : PFSeq k f := by
  intro m hm i j hi hj
  have hz : ∀ z : ℤ, Tendsto (fun x => zext (F x) z) l (𝓝 (zext f z)) := fun z => by
    unfold zext
    split_ifs
    exacts [h _, tendsto_const_nhds]
  have hmat : Tendsto (fun x => (Matrix.of fun r c => zext (F x) ((j c : ℤ) - i r) :
      Matrix (Fin m) (Fin m) ℝ)) l (𝓝 (Matrix.of fun r c => zext f ((j c : ℤ) - i r))) :=
    tendsto_pi_nhds.2 fun r => tendsto_pi_nhds.2 fun c => hz _
  have hdet := ((continuous_id.matrix_det).tendsto _).comp hmat
  exact ge_of_tendsto' hdet fun x => hF x m hm i j hi hj

/-- `PF_k` implies `PF_{k'}` for `k' ≤ k`. -/
theorem of_le {k k' : ℕ} (h : k' ≤ k) (ha : PFSeq k a) : PFSeq k' a :=
  fun m hm => ha m (hm.trans h)

/-- **Turán sequences are `PF_2`.** -/
theorem two_of_turanSeq (ha : TuranSeq a) : PFSeq 2 a := by
  intro m hm i j hi hj
  interval_cases m
  · simp [toeplitzMinor, Matrix.det_isEmpty]
  · rw [toeplitzMinor, Matrix.det_unique]
    exact ha.zext_nonneg _
  · rw [toeplitzMinor, Matrix.det_fin_two]
    simp only [Matrix.of_apply]
    have hi01 : i 0 < i 1 := hi (by decide)
    have hj01 : j 0 < j 1 := hj (by decide)
    have h := ha.zext_inner_outer (u := (j 0 : ℤ) - i 1) (x := (j 0 : ℤ) - i 0)
      (y := (j 1 : ℤ) - i 1) (v := (j 1 : ℤ) - i 0) (by omega) (by omega) (by ring)
    linarith [mul_comm (zext a ((j 1 : ℤ) - i 0)) (zext a ((j 0 : ℤ) - i 1))]

end PFSeq

end

end GaloisForLFunctions.HTGeometry
