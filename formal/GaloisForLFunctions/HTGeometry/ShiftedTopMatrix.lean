import GaloisForLFunctions.HTGeometry.ShiftedMatrixDegree
import GaloisForLFunctions.HTGeometry.DifferentialOperatorTopCoefficientMatrix

/-!
# The leading matrix measured against a shear

The leading matrix of an operator matrix reads off the coefficient at the top degree.  Against a
shear `k` the top degree of the entry `(i,j)` is `c + k_i − k_j`, an integer which may be negative —
in which case the entry has to vanish, because operator degrees are nonnegative.  Reading the
coefficient at an integer index handles both cases at once.

With that, the leading matrix is multiplicative exactly as in the unsheared case, so the ordered
product of matrices whose shifted degrees are `c m` has shifted leading matrix the ordered product
of theirs.  When that accumulated product never vanishes the growth is *exactly* linear: the plain
matrix degree of the ordered product differs from `∑ c m` by at most the spread of the shear,
uniformly in the length.

* `coeffZ`, `coeffZ_add`, `coeffZ_sum`, `coeffZ_mul`;
* `shiftTopMatrix`, `shiftTopMatrix_mul` — **multiplicativity of the shifted leading matrix**;
* `degree_eq_of_shiftTopMatrix_ne_zero`, `le_matDeg_of_shiftTopMatrix_ne_zero`;
* `shiftDegLE_chainProd`, `shiftTopMatrix_chainProd`;
* `matDeg_chainProd_sub_le` — **exact linear growth against a shear**;
* `shiftTopMatrix_twistedFamily`, `matDeg_twistedChain_sub_le` — the same for a twisted chain.
-/

open scoped Differential

namespace GaloisForLFunctions.HTGeometry

namespace DiffOp

noncomputable section

variable {K : Type u} [Field K] [Differential K]

/-- The coefficient at an integer index; negative indices carry no coefficient. -/
def coeffZ (p : DiffOp K) (n : ℤ) : K := if 0 ≤ n then coeff p n.toNat else 0

theorem coeffZ_of_neg (p : DiffOp K) {n : ℤ} (h : n < 0) : coeffZ p n = 0 := by
  rw [coeffZ, if_neg (by omega)]

@[simp] theorem coeffZ_zero (n : ℤ) : coeffZ (0 : DiffOp K) n = 0 := by
  rw [coeffZ]
  split <;> simp

@[simp] theorem coeffZ_add (p q : DiffOp K) (n : ℤ) :
    coeffZ (p + q) n = coeffZ p n + coeffZ q n := by
  rw [coeffZ, coeffZ, coeffZ]
  split
  · rw [coeff_add]
  · rw [add_zero]

theorem coeffZ_sum {ι : Type*} (s : Finset ι) (f : ι → DiffOp K) (n : ℤ) :
    coeffZ (∑ i ∈ s, f i) n = ∑ i ∈ s, coeffZ (f i) n := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, coeffZ_add, ih]

/-- **The leading coefficient of a product, at integer indices.** -/
theorem coeffZ_mul {p q : DiffOp K} {m n : ℤ} (hp : p ≠ 0 → (degree p : ℤ) ≤ m)
    (hq : q ≠ 0 → (degree q : ℤ) ≤ n) :
    coeffZ (p * q) (m + n) = coeffZ p m * coeffZ q n := by
  rcases eq_or_ne p 0 with rfl | hp0
  · simp
  rcases eq_or_ne q 0 with rfl | hq0
  · simp
  have hm : (degree p : ℤ) ≤ m := hp hp0
  have hn : (degree q : ℤ) ≤ n := hq hq0
  have hm0 : 0 ≤ m := le_trans (Int.natCast_nonneg _) hm
  have hn0 : 0 ≤ n := le_trans (Int.natCast_nonneg _) hn
  have hmn : (m + n).toNat = m.toNat + n.toNat := by omega
  rw [coeffZ, coeffZ, coeffZ, if_pos (by omega), if_pos hm0, if_pos hn0, hmn]
  refine coeff_mul_of_degree_le ?_ ?_
  · omega
  · omega

variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

/-- The leading matrix against a shear. -/
def shiftTopMatrix (k : ι → ℤ) (P : Matrix ι ι (DiffOp K)) (c : ℤ) : Matrix ι ι K :=
  Matrix.of fun i j => coeffZ (P i j) (c + k i - k j)

omit [Fintype ι] [DecidableEq ι] [Nonempty ι] in
@[simp] theorem shiftTopMatrix_apply (k : ι → ℤ) (P : Matrix ι ι (DiffOp K)) (c : ℤ) (i j : ι) :
    shiftTopMatrix k P c i j = coeffZ (P i j) (c + k i - k j) := rfl

omit [DecidableEq ι] [Nonempty ι] in
/-- **The shifted leading matrix is multiplicative.** -/
theorem shiftTopMatrix_mul (k : ι → ℤ) {P Q : Matrix ι ι (DiffOp K)} {c d : ℤ}
    (hP : ShiftDegLE k P c) (hQ : ShiftDegLE k Q d) :
    shiftTopMatrix k (P * Q) (c + d) = shiftTopMatrix k P c * shiftTopMatrix k Q d := by
  ext i j
  have hentry : (P * Q) i j = ∑ l, P i l * Q l j := Matrix.mul_apply
  rw [shiftTopMatrix_apply, hentry, coeffZ_sum]
  rw [Matrix.mul_apply]
  refine Finset.sum_congr rfl fun l _ => ?_
  have hsplit : c + d + k i - k j = (c + k i - k l) + (d + k l - k j) := by ring
  rw [hsplit]
  refine coeffZ_mul (fun h => ?_) (fun h => ?_)
  · have := hP i l h
    linarith
  · have := hQ l j h
    linarith

omit [Fintype ι] [DecidableEq ι] [Nonempty ι] in
theorem degree_eq_of_shiftTopMatrix_ne_zero (k : ι → ℤ) {P : Matrix ι ι (DiffOp K)} {c : ℤ}
    (hP : ShiftDegLE k P c) {i j : ι} (h : shiftTopMatrix k P c i j ≠ 0) :
    (degree (P i j) : ℤ) = c + k i - k j := by
  have hne : P i j ≠ 0 := by
    intro h0
    rw [shiftTopMatrix_apply, h0] at h
    exact h (coeffZ_zero _)
  refine le_antisymm ?_ ?_
  · have := hP i j hne
    linarith
  · rw [shiftTopMatrix_apply, coeffZ] at h
    by_cases hpos : 0 ≤ c + k i - k j
    · rw [if_pos hpos] at h
      have hle : (c + k i - k j).toNat ≤ degree (P i j) := le_degree h
      omega
    · rw [if_neg hpos] at h
      exact absurd rfl h

omit [DecidableEq ι] in
/-- A nonzero shifted leading matrix forces the plain degree up. -/
theorem le_matDeg_of_shiftTopMatrix_ne_zero (k : ι → ℤ) {P : Matrix ι ι (DiffOp K)} {c : ℤ}
    (hP : ShiftDegLE k P c) (h : shiftTopMatrix k P c ≠ 0) :
    c - shearSpread k ≤ (matDeg P : ℤ) := by
  obtain ⟨i, j, hij⟩ : ∃ i j, shiftTopMatrix k P c i j ≠ 0 := by
    by_contra hcon
    refine h ?_
    ext i j
    by_contra hij
    exact hcon ⟨i, j, hij⟩
  have hdeg := degree_eq_of_shiftTopMatrix_ne_zero k hP hij
  have hle : degree (P i j) ≤ matDeg P := degree_le_matDeg P i j
  have hsp : k j - k i ≤ shearSpread k := le_shearSpread k j i
  have : (degree (P i j) : ℤ) ≤ (matDeg P : ℤ) := by exact_mod_cast hle
  linarith

/-! ## Ordered products -/

omit [Nonempty ι] in
theorem shiftDegLE_chainProd (k : ι → ℤ) (B : ℕ → Matrix ι ι (DiffOp K)) (c : ℕ → ℤ)
    (hB : ∀ n, ShiftDegLE k (B n) (c n)) (n : ℕ) :
    ShiftDegLE k (chainProd B n) (∑ m ∈ Finset.range n, c m) := by
  induction n with
  | zero =>
      rw [chainProd]
      simpa using shiftDegLE_one (K := K) k
  | succ n ih =>
      rw [chainProd, Finset.sum_range_succ]
      exact ih.mul (hB n)

omit [Nonempty ι] in
theorem shiftTopMatrix_chainProd (k : ι → ℤ) (B : ℕ → Matrix ι ι (DiffOp K)) (c : ℕ → ℤ)
    (hB : ∀ n, ShiftDegLE k (B n) (c n)) (n : ℕ) :
    shiftTopMatrix k (chainProd B n) (∑ m ∈ Finset.range n, c m)
      = chainProdK (fun m => shiftTopMatrix k (B m) (c m)) n := by
  induction n with
  | zero =>
      rw [chainProd, chainProdK, Finset.sum_range_zero]
      ext i j
      rw [shiftTopMatrix_apply]
      by_cases hij : i = j
      · subst hij
        rw [Matrix.one_apply_eq, Matrix.one_apply_eq, coeffZ, if_pos (by omega)]
        have : (0 + k i - k i).toNat = 0 := by omega
        rw [this, one_def, coeff_mono_self]
      · rw [Matrix.one_apply_ne hij, Matrix.one_apply_ne hij, coeffZ_zero]
  | succ n ih =>
      rw [chainProd, chainProdK, Finset.sum_range_succ,
        shiftTopMatrix_mul k (shiftDegLE_chainProd k B c hB n) (hB n), ih]

/-- **Exact linear growth against a shear.**  If the accumulated shifted leading matrices never
vanish, the matrix degree of the ordered product differs from the sum of the shifted degrees by at
most the spread of the shear, uniformly in the length. -/
theorem matDeg_chainProd_sub_le (k : ι → ℤ) (B : ℕ → Matrix ι ι (DiffOp K)) (c : ℕ → ℤ)
    (hB : ∀ n, ShiftDegLE k (B n) (c n)) (hc : ∀ n, 0 ≤ ∑ m ∈ Finset.range n, c m)
    (hne : ∀ n, chainProdK (fun m => shiftTopMatrix k (B m) (c m)) n ≠ 0) (n : ℕ) :
    |(matDeg (chainProd B n) : ℤ) - ∑ m ∈ Finset.range n, c m| ≤ shearSpread k := by
  have hchain := shiftDegLE_chainProd k B c hB n
  have hupper : (matDeg (chainProd B n) : ℤ) ≤ (∑ m ∈ Finset.range n, c m) + shearSpread k :=
    hchain.matDeg_le (hc n)
  have htop : shiftTopMatrix k (chainProd B n) (∑ m ∈ Finset.range n, c m) ≠ 0 := by
    rw [shiftTopMatrix_chainProd k B c hB n]
    exact hne n
  have hlower := le_matDeg_of_shiftTopMatrix_ne_zero k hchain htop
  rw [abs_le]
  constructor <;> linarith

/-! ## The twisted chain -/

omit [Nonempty ι] in
theorem coeff_iterHom (σ : DiffOp K →+* DiffOp K) (τ : K →+* K)
    (hcoeff : ∀ (p : DiffOp K) (n : ℕ), coeff (σ p) n = τ (coeff p n)) :
    ∀ (m : ℕ) (p : DiffOp K) (n : ℕ), coeff (iterHom σ m p) n = iterHom τ m (coeff p n)
  | 0, p, n => rfl
  | (m + 1), p, n => by
      rw [iterHom, RingHom.comp_apply, hcoeff, iterHom, RingHom.comp_apply, coeff_iterHom σ τ hcoeff]

omit [Nonempty ι] in
theorem coeffZ_iterHom (σ : DiffOp K →+* DiffOp K) (τ : K →+* K)
    (hcoeff : ∀ (p : DiffOp K) (n : ℕ), coeff (σ p) n = τ (coeff p n))
    (m : ℕ) (p : DiffOp K) (z : ℤ) :
    coeffZ (iterHom σ m p) z = iterHom τ m (coeffZ p z) := by
  rw [coeffZ, coeffZ]
  split
  · rw [coeff_iterHom σ τ hcoeff]
  · rw [map_zero]

omit [Fintype ι] [DecidableEq ι] [Nonempty ι] in
theorem shiftTopMatrix_twistedFamily (k : ι → ℤ) (σ : DiffOp K →+* DiffOp K) (τ : K →+* K)
    (hcoeff : ∀ (p : DiffOp K) (n : ℕ), coeff (σ p) n = τ (coeff p n))
    (C : Matrix ι ι (DiffOp K)) (c : ℤ) (m : ℕ) :
    shiftTopMatrix k (twistedFamily σ C m) c
      = twistedFamily τ (shiftTopMatrix k C c) m := by
  ext i j
  rw [shiftTopMatrix_apply, twistedFamily, twistedFamily, Matrix.map_apply, Matrix.map_apply,
    coeffZ_iterHom σ τ hcoeff, shiftTopMatrix_apply]

/-- **Exact linear growth of a twisted chain against a shear.**  If the accumulated shifted leading
matrices of the twisted chain never vanish, the matrix degree of the `n`-fold twisted product
differs from `n·c` by at most the spread of the shear, uniformly in `n`. -/
theorem matDeg_twistedChain_sub_le (k : ι → ℤ) (σ : DiffOp K →+* DiffOp K) (τ : K →+* K)
    (hdeg : ∀ p, degree (σ p) = degree p)
    (hcoeff : ∀ (p : DiffOp K) (n : ℕ), coeff (σ p) n = τ (coeff p n))
    {C : Matrix ι ι (DiffOp K)} {c : ℤ} (hc : 0 ≤ c) (hC : ShiftDegLE k C c)
    (hne : ∀ n, chainProdK (twistedFamily τ (shiftTopMatrix k C c)) n ≠ 0) (n : ℕ) :
    |(matDeg (twistedChain σ C n) : ℤ) - n * c| ≤ shearSpread k := by
  have hiter : ∀ (m : ℕ) (p : DiffOp K), degree (iterHom σ m p) = degree p := by
    intro m
    induction m with
    | zero => exact fun p => rfl
    | succ m ih =>
        intro p
        rw [iterHom, RingHom.comp_apply, hdeg, ih]
  have hB : ∀ m, ShiftDegLE k (twistedFamily σ C m) c := by
    intro m
    rw [twistedFamily]
    exact hC.map (hiter m) (map_zero (iterHom σ m))
  have hsum : ∀ m : ℕ, ∑ _t ∈ Finset.range m, c = (m : ℤ) * c := by
    intro m
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have hne' : ∀ m, chainProdK (fun t => shiftTopMatrix k (twistedFamily σ C t) c) m ≠ 0 := by
    intro m
    have hfun : (fun t => shiftTopMatrix k (twistedFamily σ C t) c)
        = twistedFamily τ (shiftTopMatrix k C c) := by
      funext t
      exact shiftTopMatrix_twistedFamily k σ τ hcoeff C c t
    rw [hfun]
    exact hne m
  have h := matDeg_chainProd_sub_le k (twistedFamily σ C) (fun _ => c) hB
    (fun m => by rw [hsum m]; positivity) hne' n
  rw [hsum n] at h
  rwa [twistedChain_eq_chainProd]

end

end DiffOp

end GaloisForLFunctions.HTGeometry
