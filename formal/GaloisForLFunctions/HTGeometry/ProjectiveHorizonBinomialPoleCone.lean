import GaloisForLFunctions.HTGeometry.BihomogeneousHilbertIdentity
import GaloisForLFunctions.HTGeometry.BinomialNodeDeterminant
import GaloisForLFunctions.HTGeometry.ProjectiveHorizonCausticReflection

/-!
# Exact binomial cutoff for projective-horizon pole cones

The leading reciprocal-square jet at a zero of multiplicity `r` is the signed complete-homogeneous
sequence `(-1)^k * choose (2r+k-1) k`.  This module proves the exact finite-width law for every
positive width `p`: its rectangular Toeplitz determinant is nonzero exactly through height `p`.

The proof is computation-free.  Below the cutoff, a unit lower finite-difference transform reduces
the Toeplitz section to a nonsingular binomial-node matrix.  Above the cutoff, the `p`-th finite
difference supplies an explicit nonzero kernel vector.
-/

namespace GaloisForLFunctions.HTGeometry

open Polynomial Matrix

noncomputable section

theorem choosePoly_succ_shift_sub (q : ℕ) :
    (choosePoly (q + 1)).comp (X + C 1) - choosePoly (q + 1) =
      (choosePoly q).comp (X + C 1) := by
  apply Polynomial.eq_of_infinite_eval_eq
  refine (Set.infinite_range_of_injective (Nat.cast_injective (R := ℚ))).mono ?_
  rintro x ⟨j, rfl⟩
  simp only [Set.mem_setOf_eq, Polynomial.eval_sub, Polynomial.eval_comp,
    Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_C]
  rw [show (j : ℚ) + 1 = ((j + 1 : ℕ) : ℚ) by push_cast; ring,
    eval_choosePoly, eval_choosePoly, eval_choosePoly]
  rw [show j + 1 + (q + 1) = (j + q + 1) + 1 by omega,
    show j + (q + 1) = j + q + 1 by omega,
    show j + 1 + q = j + q + 1 by omega,
    Nat.choose_succ_succ]
  push_cast
  simp only [Nat.succ_eq_add_one, Nat.add_comm]
  ring

theorem fwdDiff_eval_choosePoly_succ (q : ℕ) (x : ℚ) :
    fwdDiff 1 (fun y => (choosePoly (q + 1)).eval y) x =
      (choosePoly q).eval (x + 1) := by
  simp only [fwdDiff]
  have h := congrArg (fun P : ℚ[X] => P.eval x) (choosePoly_succ_shift_sub q)
  simpa [Polynomial.eval_sub, Polynomial.eval_comp] using h

theorem fwdDiff_iter_eval_choosePoly_shift (q i : ℕ) (hi : i ≤ q) (a x : ℚ) :
    (fwdDiff 1)^[i] (fun y => (choosePoly q).eval (y + a)) x =
      (choosePoly (q - i)).eval (x + a + i) := by
  induction i generalizing q a with
  | zero => simp
  | succ i ih =>
      have hq : 0 < q := by omega
      obtain ⟨q, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : q ≠ 0)
      rw [Function.iterate_succ_apply]
      have hf : fwdDiff 1 (fun y => (choosePoly (q + 1)).eval (y + a)) =
          fun y => (choosePoly q).eval (y + (a + 1)) := by
        funext y
        calc
          fwdDiff 1 (fun z => (choosePoly (q + 1)).eval (z + a)) y =
              fwdDiff 1 (fun z => (choosePoly (q + 1)).eval z) (y + a) := by
                simp only [fwdDiff]
                (congr 2; ring)
          _ = (choosePoly q).eval (y + a + 1) := fwdDiff_eval_choosePoly_succ q (y + a)
          _ = (choosePoly q).eval (y + (a + 1)) := by (congr 1; ring)
      rw [hf]
      rw [ih (q := q) (a := a + 1) (by omega)]
      have hsub : q + 1 - (i + 1) = q - i := by omega
      rw [hsub]
      congr 1
      push_cast
      ring

theorem eval_choosePoly_neg_eq_zero (q d : ℕ) (hd : 1 ≤ d) (hdq : d ≤ q) :
    (choosePoly q).eval (-(d : ℚ)) = 0 := by
  rw [choosePoly, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_prod]
  simp only [Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_C]
  apply mul_eq_zero_of_right
  rw [Finset.prod_eq_zero (Finset.mem_range.2 (show d - 1 < q by omega))]
  rw [Nat.cast_sub hd]
  push_cast
  ring

/-- Positive complete-homogeneous coefficient in `p` unit variables. -/
def poleConeCoeff (p k : ℕ) : ℚ :=
  (Nat.choose (p + k - 1) (p - 1) : ℚ)

def poleConeToeplitz (p n m : ℕ) : Matrix (Fin m) (Fin m) ℚ :=
  rectangularSchurToeplitz (poleConeCoeff p) n m

def poleConeGeneralizedMatrix (p n m : ℕ) : Matrix (Fin m) (Fin m) ℚ :=
  fun r j => (choosePoly (p - 1)).eval ((n : ℚ) + (r : ℚ) - (j : ℚ))

theorem eval_choosePoly_signed_eq_poleConeCoeff (p n r j : ℕ) (hp : 1 ≤ p)
    (hj : j < p + n + r) :
    (choosePoly (p - 1)).eval ((n : ℚ) + (r : ℚ) - (j : ℚ)) =
      if j ≤ n + r then poleConeCoeff p (n + r - j) else 0 := by
  split_ifs with h
  · have hx : (n : ℚ) + (r : ℚ) - (j : ℚ) = ((n + r - j : ℕ) : ℚ) := by
      rw [Nat.cast_sub h]
      push_cast
      ring
    rw [hx, eval_choosePoly]
    simp only [poleConeCoeff]
    congr 2
    omega
  · have hlt : n + r < j := by omega
    have hx : (n : ℚ) + (r : ℚ) - (j : ℚ) = -((j - (n + r) : ℕ) : ℚ) := by
      rw [Nat.cast_sub (Nat.le_of_lt hlt)]
      push_cast
      ring
    rw [hx, eval_choosePoly_neg_eq_zero]
    · omega
    · omega

theorem poleConeGeneralizedMatrix_eq (p n m : ℕ) (hp : 1 ≤ p) (hm : m ≤ p) :
    poleConeGeneralizedMatrix p n m = poleConeToeplitz p n m := by
  ext r j
  rw [poleConeGeneralizedMatrix, poleConeToeplitz, rectangularSchurToeplitz]
  exact eval_choosePoly_signed_eq_poleConeCoeff p n r j hp (by omega)

/-- Unit lower-triangular row transform which replaces a row by its finite difference. -/
def forwardDifferenceRowMatrix (m : ℕ) : Matrix (Fin m) (Fin m) ℚ :=
  fun r k => if (k : ℕ) ≤ (r : ℕ) then
    (-1 : ℚ) ^ ((r : ℕ) - (k : ℕ)) * (Nat.choose (r : ℕ) (k : ℕ) : ℚ)
  else 0

theorem det_forwardDifferenceRowMatrix (m : ℕ) :
    (forwardDifferenceRowMatrix m).det = 1 := by
  rw [Matrix.det_of_lowerTriangular]
  · simp [forwardDifferenceRowMatrix]
  · intro i j hij
    simp only [forwardDifferenceRowMatrix]
    rw [if_neg]
    simpa using hij

theorem forwardDifferenceRowMatrix_mul_generalized (p n m : ℕ) (hp : 1 ≤ p)
    (hm : m ≤ p) (r j : Fin m) :
    (forwardDifferenceRowMatrix m * poleConeGeneralizedMatrix p n m) r j =
      (choosePoly (p - 1 - (r : ℕ))).eval
        ((n : ℚ) - (j : ℚ) + (r : ℚ)) := by
  rw [Matrix.mul_apply]
  let term : ℕ → ℚ := fun k =>
    (if k ≤ (r : ℕ) then
      (-1 : ℚ) ^ ((r : ℕ) - k) * (Nat.choose (r : ℕ) k : ℚ)
    else 0) *
      (choosePoly (p - 1)).eval ((n : ℚ) + (k : ℚ) - (j : ℚ))
  change (∑ k : Fin m, term (k : ℕ)) = _
  rw [Fin.sum_univ_eq_sum_range]
  have hiter := fwdDiff_iter_eq_sum_shift (1 : ℚ)
    (fun y => (choosePoly (p - 1)).eval (y + ((n : ℚ) - (j : ℚ))))
    (r : ℕ) 0
  rw [fwdDiff_iter_eval_choosePoly_shift (p - 1) (r : ℕ) (by omega)
    ((n : ℚ) - (j : ℚ)) 0] at hiter
  simp only [zero_add, nsmul_eq_mul, mul_one] at hiter
  rw [hiter]
  rw [← Finset.sum_subset (Finset.range_mono (show (r : ℕ) + 1 ≤ m by omega))]
  · apply Finset.sum_congr rfl
    intro k hk
    simp only [Finset.mem_range] at hk
    simp only [term]
    rw [if_pos (by omega)]
    congr 1
    · norm_num
    · congr 1
      ring
  · intro k hkm hkr
    simp only [Finset.mem_range] at hkm hkr
    simp [term, if_neg (show ¬k ≤ (r : ℕ) by omega)]

theorem cast_choose_eq_factorial_ratio (total k : ℕ) (hk : k ≤ total) :
    (Nat.choose total k : ℚ) = (Nat.factorial total : ℚ) /
      ((Nat.factorial k : ℚ) * (Nat.factorial (total - k) : ℚ)) := by
  have h := Nat.choose_mul_factorial_mul_factorial hk
  have hq : (Nat.choose total k : ℚ) * (Nat.factorial k : ℚ) *
      (Nat.factorial (total - k) : ℚ) = (Nat.factorial total : ℚ) := by
    exact_mod_cast h
  apply (eq_div_iff (mul_ne_zero (Nat.cast_ne_zero.2 (Nat.factorial_ne_zero _))
    (Nat.cast_ne_zero.2 (Nat.factorial_ne_zero _)))).2
  simpa [mul_assoc] using hq

theorem choose_shift_factorization (k₀ y i : ℕ) (hi : i ≤ y) :
    (Nat.choose (k₀ + y) (k₀ + i) : ℚ) * (Nat.choose (k₀ + i) k₀ : ℚ) =
      (Nat.choose (k₀ + y) k₀ : ℚ) * (Nat.choose y i : ℚ) := by
  rw [cast_choose_eq_factorial_ratio _ _ (by omega),
    cast_choose_eq_factorial_ratio _ _ (by omega),
    cast_choose_eq_factorial_ratio _ _ (by omega),
    cast_choose_eq_factorial_ratio _ _ hi]
  have h₁ : k₀ + y - (k₀ + i) = y - i := by omega
  have h₂ : k₀ + i - k₀ = i := by omega
  have h₃ : k₀ + y - k₀ = y := by omega
  rw [h₁, h₂, h₃]
  field_simp

theorem choose_shift_factorization_all (k₀ y i : ℕ) :
    (Nat.choose (k₀ + y) (k₀ + i) : ℚ) * (Nat.choose (k₀ + i) k₀ : ℚ) =
      (Nat.choose (k₀ + y) k₀ : ℚ) * (Nat.choose y i : ℚ) := by
  by_cases hi : i ≤ y
  · exact choose_shift_factorization k₀ y i hi
  · have h₁ : Nat.choose (k₀ + y) (k₀ + i) = 0 := Nat.choose_eq_zero_of_lt (by omega)
    have h₂ : Nat.choose y i = 0 := Nat.choose_eq_zero_of_lt (by omega)
    rw [h₁, h₂]
    simp

theorem transformedPoleConeEntry_eq_choose (p n m : ℕ) (_hp : 1 ≤ p) (hn : 1 ≤ n)
    (hm : m ≤ p) (r j : Fin m) :
    (choosePoly (p - 1 - (r : ℕ))).eval
        ((n : ℚ) - (j : ℚ) + (r : ℚ)) =
      (Nat.choose (p + n - (j : ℕ) - 1) (p - 1 - (r : ℕ)) : ℚ) := by
  by_cases h : (j : ℕ) ≤ n + (r : ℕ)
  · have hx : (n : ℚ) - (j : ℚ) + (r : ℚ) =
        ((n + (r : ℕ) - (j : ℕ) : ℕ) : ℚ) := by
      rw [Nat.cast_sub h]
      push_cast
      ring
    rw [hx, eval_choosePoly]
    congr 2
    omega
  · have hlt : n + (r : ℕ) < (j : ℕ) := by omega
    have hx : (n : ℚ) - (j : ℚ) + (r : ℚ) =
        -(((j : ℕ) - (n + (r : ℕ)) : ℕ) : ℚ) := by
      rw [Nat.cast_sub (Nat.le_of_lt hlt)]
      push_cast
      ring
    rw [hx, eval_choosePoly_neg_eq_zero]
    · rw [Nat.choose_eq_zero_of_lt]
      simp
      have hleft : p + n - (j : ℕ) - 1 = p - (j : ℕ) - 1 + n := by omega
      have hright : p - 1 - (r : ℕ) = p - (r : ℕ) - 1 := by omega
      rw [hleft, hright]
      omega
    · omega
    · omega

def reverseFin {m : ℕ} (i : Fin m) : Fin m :=
  ⟨m - 1 - (i : ℕ), by omega⟩

@[simp]
theorem reverseFin_val {m : ℕ} (i : Fin m) :
    (reverseFin i : ℕ) = m - 1 - (i : ℕ) := rfl

@[simp]
theorem reverseFin_reverseFin {m : ℕ} (i : Fin m) : reverseFin (reverseFin i) = i := by
  apply Fin.ext
  simp only [reverseFin_val]
  omega

def poleConeTransformedMatrix (p n m : ℕ) : Matrix (Fin m) (Fin m) ℚ :=
  forwardDifferenceRowMatrix m * poleConeGeneralizedMatrix p n m

theorem poleConeTransformedMatrix_apply (p n m : ℕ) (hp : 1 ≤ p) (hn : 1 ≤ n)
    (hm : m ≤ p) (r j : Fin m) :
    poleConeTransformedMatrix p n m r j =
      (Nat.choose (p + n - (j : ℕ) - 1) (p - 1 - (r : ℕ)) : ℚ) := by
  rw [poleConeTransformedMatrix, forwardDifferenceRowMatrix_mul_generalized p n m hp hm]
  exact transformedPoleConeEntry_eq_choose p n m hp hn hm r j

theorem det_poleConeTransformedMatrix_ne_zero (p n m : ℕ) (hp : 1 ≤ p) (hn : 1 ≤ n)
    (hm : m ≤ p) :
    (poleConeTransformedMatrix p n m).det ≠ 0 := by
  classical
  let k₀ := p - m
  let nodes : Fin m → ℕ := fun j => n + m - 1 - (j : ℕ)
  have hnodes : Function.Injective nodes := by
    intro a b hab
    apply Fin.ext
    simp only [nodes] at hab
    omega
  have hbinom : ((binomNodeMatrix ℚ nodes).transpose).det ≠ 0 := by
    rw [Matrix.det_transpose]
    exact det_binomNodeMatrix_ne_zero hnodes
  intro hdet
  obtain ⟨v, hvne, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.2 hdet
  let w : Fin m → ℚ := fun j => (Nat.choose (k₀ + nodes j) k₀ : ℚ) * v j
  have hw : (binomNodeMatrix ℚ nodes).transpose.mulVec w = 0 := by
    funext i
    have hrow : (∑ j : Fin m, poleConeTransformedMatrix p n m (reverseFin i) j * v j) = 0 := by
      have h := congrFun hv (reverseFin i)
      simpa only [Matrix.mulVec, dotProduct, Pi.zero_apply] using h
    rw [Matrix.mulVec, dotProduct]
    calc
      (∑ j : Fin m, (binomNodeMatrix ℚ nodes).transpose i j * w j) =
          ∑ j : Fin m, poleConeTransformedMatrix p n m (reverseFin i) j *
            (Nat.choose (k₀ + (i : ℕ)) k₀ : ℚ) * v j := by
              apply Finset.sum_congr rfl
              intro j _
              simp only [Matrix.transpose_apply, binomNodeMatrix, Matrix.of_apply, w]
              rw [poleConeTransformedMatrix_apply p n m hp hn hm]
              have htop : p + n - (j : ℕ) - 1 = k₀ + nodes j := by
                simp only [k₀, nodes]
                omega
              have hdegree : p - 1 - (reverseFin i : ℕ) = k₀ + (i : ℕ) := by
                simp only [k₀, reverseFin_val]
                omega
              rw [htop, hdegree]
              rw [choose_shift_factorization_all k₀ (nodes j) (i : ℕ)]
              ring
      _ = (Nat.choose (k₀ + (i : ℕ)) k₀ : ℚ) *
          ∑ j : Fin m, poleConeTransformedMatrix p n m (reverseFin i) j * v j := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro j _
            ring
      _ = 0 := by rw [hrow, mul_zero]
  have hwzero : w = 0 := Matrix.eq_zero_of_mulVec_eq_zero hbinom hw
  apply hvne
  funext j
  have hj := congrFun hwzero j
  simp only [w, Pi.zero_apply] at hj
  exact (mul_eq_zero.mp hj).resolve_left (Nat.cast_ne_zero.2
    (Nat.choose_ne_zero (by omega)))

theorem det_poleConeGeneralizedMatrix_ne_zero (p n m : ℕ) (hp : 1 ≤ p) (hn : 1 ≤ n)
    (hm : m ≤ p) :
    (poleConeGeneralizedMatrix p n m).det ≠ 0 := by
  have htrans := det_poleConeTransformedMatrix_ne_zero p n m hp hn hm
  rw [poleConeTransformedMatrix, Matrix.det_mul, det_forwardDifferenceRowMatrix, one_mul] at htrans
  exact htrans

theorem det_poleConeToeplitz_ne_zero (p n m : ℕ) (hp : 1 ≤ p) (hn : 1 ≤ n)
    (hm : m ≤ p) :
    (poleConeToeplitz p n m).det ≠ 0 := by
  rw [← poleConeGeneralizedMatrix_eq p n m hp hm]
  exact det_poleConeGeneralizedMatrix_ne_zero p n m hp hn hm

theorem fwdDiff_iter_succ_eval_choosePoly_eq_zero (q : ℕ) :
    (fwdDiff (1 : ℚ))^[q + 1] (fun x => (choosePoly q).eval x) = 0 := by
  have h := Polynomial.fwdDiff_iter_degree_eq_factorial (choosePoly q)
  rw [natDegree_choosePoly] at h
  have hd := congrArg (fwdDiff (1 : ℚ)) h
  rw [← Function.iterate_succ_apply' (fwdDiff (1 : ℚ)) q
    (fun x => (choosePoly q).eval x)] at hd
  have hz : fwdDiff (1 : ℚ)
      ((choosePoly q).leadingCoeff • (q.factorial : ℚ → ℚ)) = 0 := by
    funext x
    simp [fwdDiff]
  exact (by simpa [Nat.succ_eq_add_one] using hd.trans hz)

theorem alternating_backward_choosePoly_sum_eq_zero (p : ℕ) (hp : 1 ≤ p) (x : ℚ) :
    ∑ j ∈ Finset.range (p + 1),
      (-1 : ℚ) ^ j * (Nat.choose p j : ℚ) * (choosePoly (p - 1)).eval (x - j) = 0 := by
  let term : ℕ → ℚ := fun j =>
    (-1 : ℚ) ^ j * (Nat.choose p j : ℚ) * (choosePoly (p - 1)).eval (x - j)
  change ∑ j ∈ Finset.range (p + 1), term j = 0
  rw [← Finset.sum_range_reflect term (p + 1)]
  have hsum := fwdDiff_iter_eq_sum_shift (1 : ℚ)
    (fun y => (choosePoly (p - 1)).eval y) p (x - p)
  have hp' : p = (p - 1) + 1 := by omega
  have hleft : (fwdDiff (1 : ℚ))^[p] (fun y => (choosePoly (p - 1)).eval y) (x - p) = 0 := by
    calc
      (fwdDiff (1 : ℚ))^[p] (fun y => (choosePoly (p - 1)).eval y) (x - p) =
          (fwdDiff (1 : ℚ))^[(p - 1) + 1]
            (fun y => (choosePoly (p - 1)).eval y) (x - p) :=
              congrArg (fun t : ℕ => (fwdDiff (1 : ℚ))^[t]
                (fun y => (choosePoly (p - 1)).eval y) (x - p)) hp'
      _ = 0 := by
        simpa using congrFun (fwdDiff_iter_succ_eval_choosePoly_eq_zero (p - 1)) (x - p)
  rw [hleft] at hsum
  simp only [nsmul_eq_mul, mul_one] at hsum
  rw [hsum]
  apply Finset.sum_congr rfl
  intro j hj
  simp only [Finset.mem_range] at hj
  simp only [term]
  have hsub : p + 1 - 1 - j = p - j := by omega
  rw [hsub, Nat.choose_symm (by omega : j ≤ p)]
  norm_num
  have hx : x - ((p - j : ℕ) : ℚ) = x - (p : ℚ) + (j : ℚ) := by
    rw [Nat.cast_sub (by omega)]
    ring
  rw [hx]
  exact Or.inl rfl

def poleConeKernel (p m : ℕ) : Fin m → ℚ := fun j =>
  if (j : ℕ) ≤ p then (-1 : ℚ) ^ (j : ℕ) * (Nat.choose p (j : ℕ) : ℚ) else 0

theorem poleConeKernel_ne_zero (p m : ℕ) (hm : p < m) : poleConeKernel p m ≠ 0 := by
  intro h
  have h₀ := congrFun h ⟨0, by omega⟩
  norm_num [poleConeKernel] at h₀

theorem poleConeToeplitz_apply_eq_eval_choosePoly (p n m : ℕ) (hp : 1 ≤ p) (hn : 1 ≤ n)
    (r j : Fin m) (hj : (j : ℕ) ≤ p) :
    poleConeToeplitz p n m r j =
      (choosePoly (p - 1)).eval ((n : ℚ) + (r : ℚ) - (j : ℚ)) := by
  rw [poleConeToeplitz, rectangularSchurToeplitz]
  exact (eval_choosePoly_signed_eq_poleConeCoeff p n r j hp (by omega)).symm

theorem poleConeToeplitz_mulVec_kernel_eq_zero (p n m : ℕ) (hp : 1 ≤ p) (hn : 1 ≤ n)
    (hm : p < m) :
    (poleConeToeplitz p n m).mulVec (poleConeKernel p m) = 0 := by
  funext r
  rw [Matrix.mulVec, dotProduct]
  let term : ℕ → ℚ := fun j =>
    if hj : j < m then
      poleConeToeplitz p n m r ⟨j, hj⟩ *
        (if j ≤ p then (-1 : ℚ) ^ j * (Nat.choose p j : ℚ) else 0)
    else 0
  change (∑ j : Fin m,
    poleConeToeplitz p n m r j * poleConeKernel p m j) = 0
  have hfin : (∑ j : Fin m,
      poleConeToeplitz p n m r j * poleConeKernel p m j) =
      ∑ j ∈ Finset.range m, term j := by
    calc
      (∑ j : Fin m, poleConeToeplitz p n m r j * poleConeKernel p m j) =
          ∑ j : Fin m, term (j : ℕ) := by
            apply Finset.sum_congr rfl
            intro j _
            simp only [term, poleConeKernel, dif_pos j.isLt]
      _ = ∑ j ∈ Finset.range m, term j := Fin.sum_univ_eq_sum_range term m
  rw [hfin]
  have hsubset : Finset.range (p + 1) ⊆ Finset.range m :=
    Finset.range_mono (by omega)
  have hsupport : (∑ j ∈ Finset.range (p + 1), term j) =
      ∑ j ∈ Finset.range m, term j := by
    apply Finset.sum_subset hsubset
    intro j hjm hjp
    simp only [Finset.mem_range] at hjm hjp
    simp [term, hjm, if_neg (by omega : ¬j ≤ p)]
  rw [← hsupport]
  calc
    (∑ j ∈ Finset.range (p + 1), term j) =
        ∑ j ∈ Finset.range (p + 1),
          (-1 : ℚ) ^ j * (Nat.choose p j : ℚ) *
            (choosePoly (p - 1)).eval (((n : ℚ) + (r : ℚ)) - j) := by
              apply Finset.sum_congr rfl
              intro j hj
              simp only [Finset.mem_range] at hj
              have hjm : j < m := by omega
              have hjp : j ≤ p := by omega
              simp only [term, dif_pos hjm]
              rw [if_pos hjp,
                poleConeToeplitz_apply_eq_eval_choosePoly p n m hp hn r ⟨j, hjm⟩ hjp]
              ring
    _ = 0 := alternating_backward_choosePoly_sum_eq_zero p hp ((n : ℚ) + (r : ℚ))

theorem det_poleConeToeplitz_eq_zero (p n m : ℕ) (hp : 1 ≤ p) (hn : 1 ≤ n)
    (hm : p < m) :
    (poleConeToeplitz p n m).det = 0 := by
  exact Matrix.exists_mulVec_eq_zero_iff.1
    ⟨poleConeKernel p m, poleConeKernel_ne_zero p m hm,
      poleConeToeplitz_mulVec_kernel_eq_zero p n m hp hn hm⟩

theorem poleConeToeplitz_det_ne_zero_iff (p n m : ℕ) (hp : 1 ≤ p) (hn : 1 ≤ n) :
    (poleConeToeplitz p n m).det ≠ 0 ↔ m ≤ p := by
  constructor
  · intro h
    by_contra hm
    exact h (det_poleConeToeplitz_eq_zero p n m hp hn (by omega))
  · exact det_poleConeToeplitz_ne_zero p n m hp hn

theorem poleConeCoeff_eq_choose (p k : ℕ) (hp : 1 ≤ p) :
    poleConeCoeff p k = (Nat.choose (p + k - 1) k : ℚ) := by
  simp only [poleConeCoeff]
  exact_mod_cast (show Nat.choose (p + k - 1) (p - 1) = Nat.choose (p + k - 1) k by
    calc
      Nat.choose (p + k - 1) (p - 1) =
          Nat.choose (p + k - 1) (p + k - 1 - (p - 1)) :=
            (@Nat.choose_symm (p + k - 1) (p - 1) (by omega)).symm
      _ = Nat.choose (p + k - 1) k := by (congr 2; omega))

def signedPoleConeCoeff (p k : ℕ) : ℚ :=
  (-1 : ℚ) ^ k * (Nat.choose (p + k - 1) k : ℚ)

def signedPoleConeToeplitz (p n m : ℕ) : Matrix (Fin m) (Fin m) ℚ :=
  rectangularSchurToeplitz (signedPoleConeCoeff p) n m

theorem signedPoleConeToeplitz_det_eq (p n m : ℕ) (hp : 1 ≤ p) :
    (signedPoleConeToeplitz p n m).det =
      (-1 : ℚ) ^ (m * n) * (poleConeToeplitz p n m).det := by
  have hseq : signedPoleConeCoeff p = fun k => (-1 : ℚ) ^ k * poleConeCoeff p k := by
    funext k
    simp only [signedPoleConeCoeff]
    rw [poleConeCoeff_eq_choose p k hp]
  rw [signedPoleConeToeplitz, hseq]
  exact rectangularSchurToeplitz_det_reflection (poleConeCoeff p) n m

theorem signedPoleConeToeplitz_det_ne_zero_iff (p n m : ℕ) (hp : 1 ≤ p) (hn : 1 ≤ n) :
    (signedPoleConeToeplitz p n m).det ≠ 0 ↔ m ≤ p := by
  rw [signedPoleConeToeplitz_det_eq p n m hp]
  constructor
  · intro h
    exact (poleConeToeplitz_det_ne_zero_iff p n m hp hn).1 (mul_ne_zero_iff.mp h).2
  · intro hm
    exact mul_ne_zero (pow_ne_zero _ (by norm_num))
      ((poleConeToeplitz_det_ne_zero_iff p n m hp hn).2 hm)

def complexSignedPoleConeCoeff (p k : ℕ) : ℂ :=
  (-1 : ℂ) ^ k * (Nat.choose (p + k - 1) k : ℂ)

def complexSignedPoleConeToeplitz (p n m : ℕ) : Matrix (Fin m) (Fin m) ℂ :=
  rectangularSchurToeplitz (complexSignedPoleConeCoeff p) n m

theorem complexSignedPoleConeToeplitz_eq_map (p n m : ℕ) :
    complexSignedPoleConeToeplitz p n m =
      (signedPoleConeToeplitz p n m).map (Rat.castHom ℂ) := by
  ext r j
  simp only [complexSignedPoleConeToeplitz, signedPoleConeToeplitz,
    rectangularSchurToeplitz, Matrix.map_apply]
  split_ifs
  · simp [complexSignedPoleConeCoeff, signedPoleConeCoeff]
  · simp

theorem complexSignedPoleConeToeplitz_det_ne_zero_iff (p n m : ℕ)
    (hp : 1 ≤ p) (hn : 1 ≤ n) :
    (complexSignedPoleConeToeplitz p n m).det ≠ 0 ↔ m ≤ p := by
  rw [complexSignedPoleConeToeplitz_eq_map]
  have hmap : ((signedPoleConeToeplitz p n m).map (Rat.castHom ℂ)).det =
      (Rat.castHom ℂ) (signedPoleConeToeplitz p n m).det := by
    simpa only [RingHom.mapMatrix_apply] using ((Rat.castHom ℂ).map_det
      (signedPoleConeToeplitz p n m)).symm
  rw [hmap, map_ne_zero_iff (Rat.castHom ℂ) Rat.cast_injective]
  exact signedPoleConeToeplitz_det_ne_zero_iff p n m hp hn

end

end GaloisForLFunctions.HTGeometry
