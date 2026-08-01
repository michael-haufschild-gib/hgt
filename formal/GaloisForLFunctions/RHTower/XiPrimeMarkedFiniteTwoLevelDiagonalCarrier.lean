import GaloisForLFunctions.RHTower.FiniteTwoLevelMomentCarrier

/-!
# Prime-diagonal realization of the exact two-level carrier

The algebraic two-level atoms are placed on the first `N` marked-prime basis vectors.  Their
square roots form a finite-rank positive self-adjoint operator with exact Hilbert--Schmidt energy
`E` and exact fourth energy `F`.  All later marked-prime basis vectors are annihilated, making the
carrier orthogonal to a cofinite RVM/cycle reserve.
-/

open scoped BigOperators InnerProductSpace Nat.Prime

namespace RHTower

noncomputable section

open ContinuousLinearMap

def twoLevelAtomSquared (E F : ℝ) (N k : ℕ) : ℝ :=
  if k = 0 then twoLevelLarge E F N
  else if k < N then twoLevelSmall E F N
  else 0

def twoLevelAtomWeight (E F : ℝ) (N k : ℕ) : ℝ :=
  Real.sqrt (twoLevelAtomSquared E F N k)

theorem sum_range_ite_zero_eq
    (L S : ℝ) {N : ℕ} (hN : 0 < N) :
    ∑ k ∈ Finset.range N, (if k = 0 then L else S) =
      L + ((N : ℝ) - 1) * S := by
  induction N with
  | zero => omega
  | succ N ih =>
      by_cases hN0 : N = 0
      · subst N
        simp
      · have hNpos : 0 < N := Nat.pos_of_ne_zero hN0
        rw [Finset.sum_range_succ, ih hNpos]
        simp [hN0]
        ring

theorem twoLevelAtomSquared_nonneg
    {E F : ℝ} {N k : ℕ} (hE : 0 < E) (hN : 2 ≤ N)
    (hlow : E ^ 2 / N < F) (hhigh : F ≤ E ^ 2) :
    0 ≤ twoLevelAtomSquared E F N k := by
  by_cases hk0 : k = 0
  · simp [twoLevelAtomSquared, hk0,
      (twoLevelLarge_pos hE hN).le]
  · by_cases hkN : k < N
    · simp [twoLevelAtomSquared, hk0, hkN,
        twoLevelSmall_nonneg hE hN hlow hhigh]
    · simp [twoLevelAtomSquared, hk0, hkN]

theorem twoLevelAtomWeight_sq
    {E F : ℝ} {N k : ℕ} (hE : 0 < E) (hN : 2 ≤ N)
    (hlow : E ^ 2 / N < F) (hhigh : F ≤ E ^ 2) :
    twoLevelAtomWeight E F N k ^ 2 =
      twoLevelAtomSquared E F N k := by
  rw [twoLevelAtomWeight]
  exact Real.sq_sqrt
    (twoLevelAtomSquared_nonneg hE hN hlow hhigh)

theorem summable_twoLevelAtomSquared (E F : ℝ) {N : ℕ} (hN : 0 < N) :
    Summable (twoLevelAtomSquared E F N) := by
  apply summable_of_ne_finset_zero (s := Finset.range N)
  intro k hk
  simp only [Finset.mem_range, not_lt] at hk
  have hk0 : k ≠ 0 := by omega
  simp [twoLevelAtomSquared, hk0, hk]

theorem tsum_twoLevelAtomSquared
    {E F : ℝ} {N : ℕ} (hN : 2 ≤ N) :
    ∑' k : ℕ, twoLevelAtomSquared E F N k = E := by
  rw [tsum_eq_sum (s := Finset.range N) (by
    intro k hk
    simp only [Finset.mem_range, not_lt] at hk
    have hk0 : k ≠ 0 := by omega
    simp [twoLevelAtomSquared, hk0, hk])]
  simp_rw [twoLevelAtomSquared]
  have hrange :
      (∑ k ∈ Finset.range N,
        if k = 0 then twoLevelLarge E F N
        else if k < N then twoLevelSmall E F N else 0) =
      ∑ k ∈ Finset.range N,
        if k = 0 then twoLevelLarge E F N
        else twoLevelSmall E F N := by
    apply Finset.sum_congr rfl
    intro k hk
    simp only [Finset.mem_range] at hk
    simp [hk]
  rw [hrange, sum_range_ite_zero_eq _ _ (by omega),
    twoLevel_firstMoment hN]

theorem tsum_twoLevelAtomSquared_sq
    {E F : ℝ} {N : ℕ} (hN : 2 ≤ N)
    (hlow : E ^ 2 / N < F) :
    ∑' k : ℕ, twoLevelAtomSquared E F N k ^ 2 = F := by
  rw [tsum_eq_sum (s := Finset.range N) (by
    intro k hk
    simp only [Finset.mem_range, not_lt] at hk
    have hk0 : k ≠ 0 := by omega
    simp [twoLevelAtomSquared, hk0, hk])]
  have hrange :
      (∑ k ∈ Finset.range N, twoLevelAtomSquared E F N k ^ 2) =
      ∑ k ∈ Finset.range N,
        if k = 0 then twoLevelLarge E F N ^ 2
        else twoLevelSmall E F N ^ 2 := by
    apply Finset.sum_congr rfl
    intro k hk
    simp only [Finset.mem_range] at hk
    simp [twoLevelAtomSquared, hk]
  rw [hrange, sum_range_ite_zero_eq _ _ (by omega),
    twoLevel_secondMoment hN hlow]

def twoLevelPrimeWeight (E F : ℝ) (N : ℕ) (p : Nat.Primes) : ℝ :=
  twoLevelAtomWeight E F N (nthPrimeEquiv.symm p)

theorem summable_twoLevelPrimeWeight_sq
    {E F : ℝ} {N : ℕ} (hE : 0 < E) (hN : 2 ≤ N)
    (hlow : E ^ 2 / N < F) (hhigh : F ≤ E ^ 2) :
    Summable (fun p : Nat.Primes => twoLevelPrimeWeight E F N p ^ 2) := by
  apply nthPrimeEquiv.summable_iff.mp
  simpa [Function.comp_def, twoLevelPrimeWeight,
    twoLevelAtomWeight_sq hE hN hlow hhigh] using
    summable_twoLevelAtomSquared E F (show 0 < N by omega)

theorem tsum_twoLevelPrimeWeight_sq
    {E F : ℝ} {N : ℕ} (hE : 0 < E) (hN : 2 ≤ N)
    (hlow : E ^ 2 / N < F) (hhigh : F ≤ E ^ 2) :
    ∑' p : Nat.Primes, twoLevelPrimeWeight E F N p ^ 2 = E := by
  rw [← nthPrimeEquiv.tsum_eq]
  simpa [twoLevelPrimeWeight,
    twoLevelAtomWeight_sq hE hN hlow hhigh] using
    tsum_twoLevelAtomSquared hN

theorem tsum_twoLevelPrimeWeight_four
    {E F : ℝ} {N : ℕ} (hE : 0 < E) (hN : 2 ≤ N)
    (hlow : E ^ 2 / N < F) (hhigh : F ≤ E ^ 2) :
    ∑' p : Nat.Primes, twoLevelPrimeWeight E F N p ^ 4 = F := by
  rw [← nthPrimeEquiv.tsum_eq]
  have heq :
      (fun k : ℕ => twoLevelAtomWeight E F N k ^ 4) =
        fun k : ℕ => twoLevelAtomSquared E F N k ^ 2 := by
    funext k
    rw [show twoLevelAtomWeight E F N k ^ 4 =
      (twoLevelAtomWeight E F N k ^ 2) ^ 2 by ring,
      twoLevelAtomWeight_sq hE hN hlow hhigh]
  simp only [twoLevelPrimeWeight, Equiv.symm_apply_apply]
  rw [heq, tsum_twoLevelAtomSquared_sq hN hlow]

def twoLevelPrimeDiagonalKernel
    (E F : ℝ) (N : ℕ) (pq : Nat.Primes × Nat.Primes) : ℂ :=
  HilbertSchmidt.diagMul
    (fun p => (twoLevelPrimeWeight E F N p : ℂ)) pq

theorem twoLevelPrimeDiagonalKernel_isHS
    {E F : ℝ} {N : ℕ} (hE : 0 < E) (hN : 2 ≤ N)
    (hlow : E ^ 2 / N < F) (hhigh : F ≤ E ^ 2) :
    HilbertSchmidt.IsHS (twoLevelPrimeDiagonalKernel E F N) := by
  apply HilbertSchmidt.isHS_diagMul_infinite
  exact (summable_twoLevelPrimeWeight_sq hE hN hlow hhigh).congr
    fun p => by
      simp [Complex.norm_real, Real.norm_eq_abs, sq_abs]

def twoLevelPrimeDiagonalOperator
    (E F : ℝ) (N : ℕ)
    (hE : 0 < E) (hN : 2 ≤ N)
    (hlow : E ^ 2 / N < F) (hhigh : F ≤ E ^ 2) :
    RouteKPrimeHilbert →L[ℂ] RouteKPrimeHilbert :=
  HilbertSchmidt.toOperator
    (twoLevelPrimeDiagonalKernel_isHS hE hN hlow hhigh)

theorem twoLevelPrimeDiagonalOperator_isHilbertSchmidt
    {E F : ℝ} {N : ℕ} (hE : 0 < E) (hN : 2 ≤ N)
    (hlow : E ^ 2 / N < F) (hhigh : F ≤ E ^ 2) :
    (twoLevelPrimeDiagonalOperator E F N hE hN hlow hhigh).IsHilbertSchmidt :=
  HilbertSchmidt.isHilbertSchmidt_toOperator
    (twoLevelPrimeDiagonalKernel_isHS hE hN hlow hhigh)

theorem twoLevelPrimeDiagonalOperator_basis
    {E F : ℝ} {N : ℕ} (hE : 0 < E) (hN : 2 ≤ N)
    (hlow : E ^ 2 / N < F) (hhigh : F ≤ E ^ 2)
    (p : Nat.Primes) :
    twoLevelPrimeDiagonalOperator E F N hE hN hlow hhigh
        (routeKPrimeBasis p) =
      (twoLevelPrimeWeight E F N p : ℂ) • routeKPrimeBasis p := by
  apply lp.ext
  funext q
  rw [twoLevelPrimeDiagonalOperator, routeKPrimeBasis,
    HilbertSchmidt.toOperator_single
      (twoLevelPrimeDiagonalKernel_isHS hE hN hlow hhigh)]
  change twoLevelPrimeDiagonalKernel E F N (q, p) =
    ((twoLevelPrimeWeight E F N p : ℂ) •
      (lp.single 2 p 1 : RouteKPrimeHilbert)) q
  rw [lp.coeFn_smul, Pi.smul_apply, smul_eq_mul]
  by_cases hqp : q = p
  · subst q
    simp [twoLevelPrimeDiagonalKernel, HilbertSchmidt.diagMul]
  · simp [twoLevelPrimeDiagonalKernel, HilbertSchmidt.diagMul, hqp]

theorem twoLevelPrimeDiagonalKernel_hsAdjoint
    (E F : ℝ) (N : ℕ) :
    HilbertSchmidt.hsAdjoint (twoLevelPrimeDiagonalKernel E F N) =
      twoLevelPrimeDiagonalKernel E F N := by
  funext pq
  rcases pq with ⟨p, q⟩
  by_cases hpq : p = q
  · subst q
    simp [HilbertSchmidt.hsAdjoint, twoLevelPrimeDiagonalKernel,
      HilbertSchmidt.diagMul]
  · have hqp : q ≠ p := Ne.symm hpq
    simp [HilbertSchmidt.hsAdjoint, twoLevelPrimeDiagonalKernel,
      HilbertSchmidt.diagMul, hpq, hqp]

theorem twoLevelPrimeDiagonalOperator_isSelfAdjoint
    {E F : ℝ} {N : ℕ} (hE : 0 < E) (hN : 2 ≤ N)
    (hlow : E ^ 2 / N < F) (hhigh : F ≤ E ^ 2) :
    IsSelfAdjoint
      (twoLevelPrimeDiagonalOperator E F N hE hN hlow hhigh) := by
  rw [ContinuousLinearMap.isSelfAdjoint_iff',
    twoLevelPrimeDiagonalOperator, HilbertSchmidt.adjoint_toOperator]
  exact HilbertSchmidt.toOperator_congr _ _
    (twoLevelPrimeDiagonalKernel_hsAdjoint E F N)

theorem hsNormSq_twoLevelPrimeDiagonalOperator
    {E F : ℝ} {N : ℕ} (hE : 0 < E) (hN : 2 ≤ N)
    (hlow : E ^ 2 / N < F) (hhigh : F ≤ E ^ 2) :
    hsNormSq (twoLevelPrimeDiagonalOperator E F N hE hN hlow hhigh) = E := by
  rw [twoLevelPrimeDiagonalOperator,
    HilbertSchmidt.hsNormSq_toOperator]
  change
    HilbertSchmidt.hsNormSq
        (HilbertSchmidt.diagMul
          (fun p => (twoLevelPrimeWeight E F N p : ℂ))) = E
  rw [HilbertSchmidt.hsNormSq_diagMul_infinite]
  simpa [Complex.norm_real, Real.norm_eq_abs, sq_abs] using
    tsum_twoLevelPrimeWeight_sq hE hN hlow hhigh

theorem twoLevelPrimeDiagonalOperator_sq_basis
    {E F : ℝ} {N : ℕ} (hE : 0 < E) (hN : 2 ≤ N)
    (hlow : E ^ 2 / N < F) (hhigh : F ≤ E ^ 2)
    (p : Nat.Primes) :
    (twoLevelPrimeDiagonalOperator E F N hE hN hlow hhigh ^ 2)
        (routeKPrimeBasis p) =
      (twoLevelPrimeWeight E F N p ^ 2 : ℂ) • routeKPrimeBasis p := by
  rw [pow_two, mul_apply_eq_comp,
    twoLevelPrimeDiagonalOperator_basis hE hN hlow hhigh,
    map_smul, twoLevelPrimeDiagonalOperator_basis hE hN hlow hhigh,
    smul_smul]
  congr 1
  ring

theorem twoLevelPrimeDiagonalOperator_sq_isHilbertSchmidt
    {E F : ℝ} {N : ℕ} (hE : 0 < E) (hN : 2 ≤ N)
    (hlow : E ^ 2 / N < F) (hhigh : F ≤ E ^ 2) :
    ContinuousLinearMap.IsHilbertSchmidt
      (twoLevelPrimeDiagonalOperator E F N hE hN hlow hhigh ^ 2) := by
  simpa only [pow_two, ContinuousLinearMap.mul_def] using
    (twoLevelPrimeDiagonalOperator_isHilbertSchmidt hE hN hlow hhigh).comp_left
      (twoLevelPrimeDiagonalOperator E F N hE hN hlow hhigh)

theorem hsNormSq_sq_twoLevelPrimeDiagonalOperator
    {E F : ℝ} {N : ℕ} (hE : 0 < E) (hN : 2 ≤ N)
    (hlow : E ^ 2 / N < F) (hhigh : F ≤ E ^ 2) :
    hsNormSq
        (twoLevelPrimeDiagonalOperator E F N hE hN hlow hhigh ^ 2) = F := by
  rw [hsNormSq_eq
    (twoLevelPrimeDiagonalOperator_sq_isHilbertSchmidt hE hN hlow hhigh)
    (HilbertSchmidt.lpBasis Nat.Primes)]
  apply Eq.trans _ (tsum_twoLevelPrimeWeight_four hE hN hlow hhigh)
  apply tsum_congr
  intro p
  rw [HilbertSchmidt.lpBasis_apply]
  change
    ‖(twoLevelPrimeDiagonalOperator E F N hE hN hlow hhigh ^ 2)
      (routeKPrimeBasis p)‖ ^ 2 =
        twoLevelPrimeWeight E F N p ^ 4
  rw [twoLevelPrimeDiagonalOperator_sq_basis hE hN hlow hhigh,
    norm_smul, routeKPrimeBasis, lp.norm_single
      (by norm_num : (0 : ENNReal) < 2), norm_one, mul_one,
    norm_pow, Complex.norm_real, Real.norm_eq_abs,
    sq_abs]
  ring

theorem twoLevelPrimeDiagonalOperator_basis_eq_zero_of_le_index
    {E F : ℝ} {N : ℕ} (hE : 0 < E) (hN : 2 ≤ N)
    (hlow : E ^ 2 / N < F) (hhigh : F ≤ E ^ 2)
    {p : Nat.Primes} (hp : N ≤ nthPrimeEquiv.symm p) :
    twoLevelPrimeDiagonalOperator E F N hE hN hlow hhigh
        (routeKPrimeBasis p) = 0 := by
  rw [twoLevelPrimeDiagonalOperator_basis hE hN hlow hhigh]
  have hp0 : nthPrimeEquiv.symm p ≠ 0 := by omega
  have hpN : ¬ nthPrimeEquiv.symm p < N := by omega
  simp [twoLevelPrimeWeight, twoLevelAtomWeight,
    twoLevelAtomSquared, hp0, hpN]

end

end RHTower
