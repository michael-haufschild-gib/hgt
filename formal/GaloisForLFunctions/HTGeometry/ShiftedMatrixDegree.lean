import GaloisForLFunctions.HTGeometry.DifferentialOperatorChainDegree
import GaloisForLFunctions.HTGeometry.TwistedMatrixChain

/-!
# The matrix degree measured against a shear

Conjugating an operator matrix by `diag(∂^{k_1}, …, ∂^{k_r})` changes the degree of the entry `(i,j)`
by `k_j − k_i`.  The conjugated matrix need not have entries in the operator ring, but the *bound*
on its degrees does not need the conjugation to be formed:

`ShiftDegLE k P c  :  deg P_{ij} + k_j − k_i ≤ c  for every nonzero entry`.

This is submultiplicative, invariant under a degree-preserving map of the coefficients, and within
the spread of `k` of the plain matrix degree.  The consequence for a twisted chain is the bounded
branch of the phase dichotomy: a shear making the shifted degree vanish forces the degree of the
whole chain to stay bounded by the spread of the shear alone, uniformly in the length.  The
degree-zero case is the shear `k = 0`, so this is strictly stronger.

* `ShiftDegLE`, `ShiftDegLE.mono`, `shiftDegLE_one`;
* `shearSpread`, `le_shearSpread`, `shearSpread_nonneg`;
* `ShiftDegLE.matDeg_le` — the plain degree is controlled by the spread;
* `ShiftDegLE.mul` — **submultiplicativity**;
* `ShiftDegLE.map` — invariance under a degree-preserving map of the entries;
* `shiftDegLE_twistedChain` — **the chain's shifted degree grows at most linearly**;
* `matDeg_twistedChain_le_of_shiftDegLE_zero` — **the bounded branch**;
* `matDeg_twistedChain_le_of_shiftDegLE` — **every shear bounds the growth rate**.
-/

open scoped Differential

namespace GaloisForLFunctions.HTGeometry

namespace DiffOp

noncomputable section

variable {K : Type u} [Field K] [Differential K]
variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

/-- Every nonzero entry has degree at most `c` after the shear `k`. -/
def ShiftDegLE (k : ι → ℤ) (P : Matrix ι ι (DiffOp K)) (c : ℤ) : Prop :=
  ∀ i j, P i j ≠ 0 → (degree (P i j) : ℤ) + k j - k i ≤ c

omit [Fintype ι] [DecidableEq ι] [Nonempty ι] in
theorem ShiftDegLE.mono {k : ι → ℤ} {P : Matrix ι ι (DiffOp K)} {c c' : ℤ} (h : c ≤ c')
    (hP : ShiftDegLE k P c) : ShiftDegLE k P c' :=
  fun i j hij => le_trans (hP i j hij) h

theorem degree_one : degree (1 : DiffOp K) = 0 := by
  refine Nat.le_zero.mp (degree_le_iff.mpr fun m hm => ?_)
  rw [one_def]
  exact coeff_mono_of_ne 1 (by omega)

omit [Fintype ι] [Nonempty ι] in
theorem shiftDegLE_one (k : ι → ℤ) : ShiftDegLE k (1 : Matrix ι ι (DiffOp K)) 0 := by
  intro i j hij
  by_cases h : i = j
  · subst h
    rw [Matrix.one_apply_eq, degree_one]
    simp
  · exact absurd (Matrix.one_apply_ne h) hij

/-- The spread of a shear vector. -/
def shearSpread (k : ι → ℤ) : ℤ :=
  (Finset.univ : Finset (ι × ι)).sup' Finset.univ_nonempty fun q => k q.1 - k q.2

omit [DecidableEq ι] in
theorem le_shearSpread (k : ι → ℤ) (i j : ι) : k i - k j ≤ shearSpread k :=
  Finset.le_sup' (f := fun q : ι × ι => k q.1 - k q.2) (Finset.mem_univ (i, j))

omit [DecidableEq ι] in
theorem shearSpread_nonneg (k : ι → ℤ) : 0 ≤ shearSpread k := by
  obtain ⟨i⟩ := ‹Nonempty ι›
  have := le_shearSpread k i i
  simpa using this

omit [DecidableEq ι] in
/-- **The plain matrix degree is controlled by the shifted one and the spread.** -/
theorem ShiftDegLE.matDeg_le {k : ι → ℤ} {P : Matrix ι ι (DiffOp K)} {c : ℤ} (hc : 0 ≤ c)
    (hP : ShiftDegLE k P c) : (matDeg P : ℤ) ≤ c + shearSpread k := by
  obtain ⟨q, -, hq⟩ := Finset.exists_mem_eq_sup (Finset.univ : Finset ι) Finset.univ_nonempty
    fun i => degVec (P i)
  obtain ⟨j, -, hj⟩ := Finset.exists_mem_eq_sup (Finset.univ : Finset ι) Finset.univ_nonempty
    fun j => degree (P q j)
  have hmat : matDeg P = degree (P q j) := by
    rw [matDeg, hq, degVec, hj]
  rw [hmat]
  by_cases h0 : P q j = 0
  · rw [h0, degree_zero]
    have := shearSpread_nonneg k
    push_cast
    linarith
  · have h1 := hP q j h0
    have h2 := le_shearSpread k q j
    linarith

omit [DecidableEq ι] [Nonempty ι] in
/-- **Submultiplicativity of the shifted degree.** -/
theorem ShiftDegLE.mul {k : ι → ℤ} {P Q : Matrix ι ι (DiffOp K)} {c d : ℤ}
    (hP : ShiftDegLE k P c) (hQ : ShiftDegLE k Q d) : ShiftDegLE k (P * Q) (c + d) := by
  classical
  intro i j hij
  set s : Finset ι := Finset.univ.filter fun l => P i l ≠ 0 ∧ Q l j ≠ 0 with hs
  have hsum : (P * Q) i j = ∑ l ∈ s, P i l * Q l j := by
    rw [Matrix.mul_apply]
    refine (Finset.sum_subset (Finset.filter_subset _ _) ?_).symm
    intro l _ hl
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_and_or, not_not] at hl
    rcases hl with h | h
    · rw [h, zero_mul]
    · rw [h, mul_zero]
  have hne : s.Nonempty := by
    rcases Finset.eq_empty_or_nonempty s with he | he
    · exfalso
      apply hij
      rw [hsum, he, Finset.sum_empty]
    · exact he
  obtain ⟨l, hlmem, hl⟩ := Finset.exists_mem_eq_sup s hne fun l => degree (P i l) + degree (Q l j)
  have hdeg : degree ((P * Q) i j) ≤ degree (P i l) + degree (Q l j) := by
    rw [hsum]
    refine le_trans (degree_sum_le _ _) (Finset.sup_le fun m hm => ?_)
    refine le_trans (degree_mul_le _ _) ?_
    rw [← hl]
    exact Finset.le_sup (f := fun l => degree (P i l) + degree (Q l j)) hm
  have hcast : (degree ((P * Q) i j) : ℤ) ≤ (degree (P i l) : ℤ) + (degree (Q l j) : ℤ) := by
    exact_mod_cast hdeg
  simp only [hs, Finset.mem_filter, Finset.mem_univ, true_and] at hlmem
  have h1 := hP i l hlmem.1
  have h2 := hQ l j hlmem.2
  linarith

omit [Fintype ι] [DecidableEq ι] [Nonempty ι] in
theorem ShiftDegLE.map {k : ι → ℤ} {P : Matrix ι ι (DiffOp K)} {c : ℤ}
    {g : DiffOp K → DiffOp K} (hg : ∀ p, degree (g p) = degree p) (hg0 : g 0 = 0)
    (hP : ShiftDegLE k P c) : ShiftDegLE k (P.map g) c := by
  intro i j hij
  rw [Matrix.map_apply, hg]
  refine hP i j fun h0 => hij ?_
  rw [Matrix.map_apply, h0, hg0]

omit [Nonempty ι] in
/-- **The shifted degree of a twisted chain grows at most linearly.** -/
theorem shiftDegLE_twistedChain (k : ι → ℤ) (σ : DiffOp K →+* DiffOp K)
    (hσ : ∀ p, degree (σ p) = degree p)
    {C : Matrix ι ι (DiffOp K)} {c : ℤ} (hC : ShiftDegLE k C c) (n : ℕ) :
    ShiftDegLE k (twistedChain σ C n) (n * c) := by
  have hiter : ∀ (m : ℕ) (p : DiffOp K), degree (iterHom σ m p) = degree p := by
    intro m
    induction m with
    | zero => exact fun p => rfl
    | succ m ih =>
        intro p
        rw [iterHom, RingHom.comp_apply, hσ, ih]
  induction n with
  | zero =>
      rw [twistedChain]
      have := shiftDegLE_one (K := K) k
      simpa using this
  | succ n ih =>
      rw [twistedChain]
      have hfam : ShiftDegLE k (twistedFamily σ C n) c := by
        rw [twistedFamily]
        exact hC.map (hiter n) (map_zero (iterHom σ n))
      have h := ih.mul hfam
      refine h.mono ?_
      push_cast
      linarith

/-- **The bounded branch of the phase dichotomy.**  A shear making the shifted degree vanish forces
the degree of the whole twisted chain to stay bounded by the spread of the shear. -/
theorem matDeg_twistedChain_le_of_shiftDegLE_zero (k : ι → ℤ) (σ : DiffOp K →+* DiffOp K)
    (hσ : ∀ p, degree (σ p) = degree p)
    {C : Matrix ι ι (DiffOp K)} (hC : ShiftDegLE k C 0) (n : ℕ) :
    (matDeg (twistedChain σ C n) : ℤ) ≤ shearSpread k := by
  have h := shiftDegLE_twistedChain k σ hσ hC n
  rw [mul_zero] at h
  have := h.matDeg_le (le_refl (0 : ℤ))
  simpa using this

/-- **Every shear bounds the growth rate of the twisted chain.**  The degree of the `n`-fold twisted
product is at most `n·c + spread(k)` whenever the shear `k` puts every entry of the generator at
shifted degree `c`.  So the asymptotic rate is at most the shifted degree, for every shear. -/
theorem matDeg_twistedChain_le_of_shiftDegLE (k : ι → ℤ) (σ : DiffOp K →+* DiffOp K)
    (hσ : ∀ p, degree (σ p) = degree p) {C : Matrix ι ι (DiffOp K)} {c : ℤ} (hc : 0 ≤ c)
    (hC : ShiftDegLE k C c) (n : ℕ) :
    (matDeg (twistedChain σ C n) : ℤ) ≤ n * c + shearSpread k := by
  have h := shiftDegLE_twistedChain k σ hσ hC n
  exact h.matDeg_le (by positivity)

end

end DiffOp

end GaloisForLFunctions.HTGeometry
