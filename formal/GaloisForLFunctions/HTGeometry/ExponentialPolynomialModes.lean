import GaloisForLFunctions.HTGeometry.AnseloneKorevaarTranslationRank

/-!
# The characteristic modes of a constant-coefficient operator

`RealConstantCoefficientAnnihilator` proves that a smooth solution of `L(D) g = 0` is *some*
exponential polynomial.  This module identifies **which** one: the frequencies are exactly the roots
of `L` and the polynomial degree at a root is strictly below its multiplicity.

The engine is the block calculus.  Applying `L(D)` to a block `P(x) e^{μ x}` returns a block with
the same frequency,

```text
L(D) (P e^{μ ·}) = (exponentialPolynomialModesBlockOp L μ P) e^{μ ·} ,     exponentialPolynomialModesBlockOp L μ = L (derivative + μ) ,
```

and the top coefficient of `exponentialPolynomialModesBlockOp L μ P` is `L(μ)` times that of `P`, because differentiation
strictly lowers degree.  Three consequences follow at once:

* `blockOp_ne_zero` — a frequency that is not a root of `L` is annihilated only if its polynomial
  vanishes;
* `natDegree_lt_rootMultiplicity_of_blockOp_eq_zero` — at a root, the polynomial degree is below the
  root multiplicity, since factoring out `(X - μ)^m` turns the block operator into `m` derivatives;
* `eq_zero_of_sum_polyExp_eq_zero` — blocks with **distinct** frequencies are linearly independent,
  proved by annihilating every other block with a product of powers of `X - μ` and reading the
  surviving one.

Nothing here is specific to a research target: it is the classical characteristic-mode theorem for
a linear constant-coefficient ODE, in the exact form a symbol reduction needs.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

open scoped BigOperators

/-! ## The shifted polynomial operator -/

/-- The frequency shift `P ↦ P' + μ P` as an endomorphism of `ℂ[X]`. -/
def expShiftLM (μ : ℂ) : Module.End ℂ (Polynomial ℂ) :=
  Polynomial.derivative + μ • LinearMap.id

theorem expShiftLM_apply (μ : ℂ) (P : Polynomial ℂ) :
    expShiftLM μ P = expShiftPoly μ P := rfl

/-- The **block operator**: the action of `L(D)` on the polynomial factor of a block of
frequency `μ`. -/
def exponentialPolynomialModesBlockOp (L : Polynomial ℂ) (μ : ℂ) : Module.End ℂ (Polynomial ℂ) :=
  Polynomial.aeval (expShiftLM μ) L

theorem blockOp_mul (L M : Polynomial ℂ) (μ : ℂ) (P : Polynomial ℂ) :
    exponentialPolynomialModesBlockOp (L * M) μ P = exponentialPolynomialModesBlockOp L μ (exponentialPolynomialModesBlockOp M μ P) := by
  rw [exponentialPolynomialModesBlockOp, map_mul, Module.End.mul_apply]
  rfl

theorem blockOp_XsubC (μ : ℂ) (P : Polynomial ℂ) :
    exponentialPolynomialModesBlockOp (Polynomial.X - Polynomial.C μ) μ P = Polynomial.derivative P := by
  rw [exponentialPolynomialModesBlockOp, map_sub, Polynomial.aeval_X, Polynomial.aeval_C,
    Algebra.algebraMap_eq_smul_one]
  simp only [LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply, expShiftLM_apply,
    expShiftPoly]
  abel

theorem blockOp_XsubC_pow (μ : ℂ) (m : ℕ) (P : Polynomial ℂ) :
    exponentialPolynomialModesBlockOp ((Polynomial.X - Polynomial.C μ) ^ m) μ P = (⇑Polynomial.derivative)^[m] P := by
  induction m generalizing P with
  | zero => simp [exponentialPolynomialModesBlockOp]
  | succ m ih =>
      rw [pow_succ, blockOp_mul, ih, blockOp_XsubC, Function.iterate_succ_apply']
      exact (Function.iterate_succ_apply' _ _ _).symm ▸ rfl

/-! ## The block calculus -/

theorem iteratedDeriv_polyExp (k : ℕ) (P : Polynomial ℂ) (μ : ℂ) :
    iteratedDeriv k (polyExp P μ) = polyExp ((expShiftLM μ ^ k) P) μ := by
  induction k generalizing P with
  | zero => simp
  | succ k ih =>
      have hstep : (expShiftLM μ ^ (k + 1)) P = (expShiftLM μ ^ k) (expShiftPoly μ P) := by
        rw [pow_succ, Module.End.mul_apply, expShiftLM_apply]
      rw [iteratedDeriv_succ', deriv_polyExp, ih, hstep]

/-- **The block rule.**  A constant-coefficient operator maps a block to a block of the same
frequency. -/
theorem realConstCoeffOp_polyExp (L P : Polynomial ℂ) (μ : ℂ) :
    realConstCoeffOp L (polyExp P μ) = polyExp (exponentialPolynomialModesBlockOp L μ P) μ := by
  funext x
  rw [realConstCoeffOp_eq_sum_range, exponentialPolynomialModesBlockOp, Polynomial.aeval_eq_sum_range (x := expShiftLM μ)]
  simp only [iteratedDeriv_polyExp, polyExp, polyExpC, LinearMap.coe_sum, Finset.sum_apply,
    LinearMap.smul_apply, Polynomial.eval_finsetSum, Polynomial.eval_smul, smul_eq_mul,
    Finset.sum_mul]
  exact Finset.sum_congr rfl fun i _ => by ring

/-! ## Degrees under the block operator -/

theorem natDegree_expShiftLM_le (μ : ℂ) (P : Polynomial ℂ) :
    (expShiftLM μ P).natDegree ≤ P.natDegree := by
  rw [expShiftLM_apply, expShiftPoly]
  refine le_trans (Polynomial.natDegree_add_le _ _) ?_
  refine max_le (le_trans (Polynomial.natDegree_derivative_le P) (Nat.sub_le _ _)) ?_
  rw [Polynomial.smul_eq_C_mul]
  exact le_trans (Polynomial.natDegree_mul_le) (by simp)

theorem natDegree_expShiftLM_pow_le (μ : ℂ) (k : ℕ) (P : Polynomial ℂ) :
    ((expShiftLM μ ^ k) P).natDegree ≤ P.natDegree := by
  induction k generalizing P with
  | zero => simp
  | succ k ih =>
      rw [pow_succ, Module.End.mul_apply]
      exact le_trans (ih _) (natDegree_expShiftLM_le μ P)

/-- The top coefficient is multiplied by `μ` at every shift, because differentiation lowers
degree. -/
theorem coeff_expShiftLM_pow (μ : ℂ) (k : ℕ) {d : ℕ} (P : Polynomial ℂ) (hd : P.natDegree ≤ d) :
    ((expShiftLM μ ^ k) P).coeff d = μ ^ k * P.coeff d := by
  induction k generalizing P with
  | zero => simp
  | succ k ih =>
      rw [pow_succ, Module.End.mul_apply]
      rw [ih (expShiftLM μ P) (le_trans (natDegree_expShiftLM_le μ P) hd)]
      have hderiv : (Polynomial.derivative P).coeff d = 0 := by
        rw [Polynomial.coeff_derivative,
          Polynomial.coeff_eq_zero_of_natDegree_lt (by omega), zero_mul]
      rw [expShiftLM_apply, expShiftPoly, Polynomial.coeff_add, hderiv, zero_add,
        Polynomial.coeff_smul, smul_eq_mul]
      ring

/-- **The top coefficient of a block image.** -/
theorem coeff_blockOp (L : Polynomial ℂ) (μ : ℂ) {d : ℕ} (P : Polynomial ℂ)
    (hd : P.natDegree ≤ d) :
    (exponentialPolynomialModesBlockOp L μ P).coeff d = L.eval μ * P.coeff d := by
  rw [exponentialPolynomialModesBlockOp, Polynomial.aeval_eq_sum_range (x := expShiftLM μ)]
  simp only [LinearMap.coe_sum, Finset.sum_apply, LinearMap.smul_apply, Polynomial.finsetSum_coeff,
    Polynomial.coeff_smul, smul_eq_mul]
  rw [Polynomial.eval_eq_sum_range, Finset.sum_mul]
  exact Finset.sum_congr rfl fun i _ => by rw [coeff_expShiftLM_pow μ i P hd]; ring

/-- **A nonroot frequency is not annihilated.** -/
theorem blockOp_ne_zero {L P : Polynomial ℂ} {μ : ℂ} (hL : L.eval μ ≠ 0) (hP : P ≠ 0) :
    exponentialPolynomialModesBlockOp L μ P ≠ 0 := by
  intro h
  have hc := coeff_blockOp L μ P (le_refl P.natDegree)
  rw [h, Polynomial.coeff_zero] at hc
  exact (mul_ne_zero hL (Polynomial.leadingCoeff_ne_zero.mpr hP)) hc.symm

/-! ## Blocks vanish only trivially -/

theorem polyExp_eq_zero_poly (μ : ℂ) : polyExp (0 : Polynomial ℂ) μ = 0 := by
  funext x
  simp [polyExp, polyExpC]

theorem polyExp_eq_zero_iff (P : Polynomial ℂ) (μ : ℂ) : polyExp P μ = 0 ↔ P = 0 := by
  refine ⟨fun h => ?_, fun h => by rw [h, polyExp_eq_zero_poly]⟩
  refine Polynomial.eq_zero_of_infinite_isRoot P ?_
  refine Set.Infinite.mono ?_ (Set.infinite_range_of_injective Complex.ofReal_injective)
  rintro z ⟨x, rfl⟩
  have hx : polyExp P μ x = 0 := by rw [h]; rfl
  simp only [polyExp, polyExpC] at hx
  have := mul_eq_zero.mp hx
  rcases this with h1 | h2
  · exact h1
  · exact absurd h2 (Complex.exp_ne_zero _)

/-! ## Additivity of the operator on smooth families -/

theorem realConstCoeffOp_sum {ι : Type*} (s : Finset ι) (L : Polynomial ℂ) (g : ι → ℝ → ℂ)
    (hg : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (g i)) :
    realConstCoeffOp L (∑ i ∈ s, g i) = ∑ i ∈ s, realConstCoeffOp L (g i) := by
  classical
  set G : ι → smoothSubmodule := fun i => ⟨g i, hg i⟩ with hG
  have hcoe : ((∑ i ∈ s, G i : smoothSubmodule) : ℝ → ℂ) = ∑ i ∈ s, g i := by
    rw [← Submodule.coe_subtype, map_sum]
    rfl
  have hmap : ((Polynomial.aeval smoothDerivLM L) (∑ i ∈ s, G i) : smoothSubmodule)
      = ∑ i ∈ s, (Polynomial.aeval smoothDerivLM L) (G i) := map_sum _ _ _
  have h1 : realConstCoeffOp L (∑ i ∈ s, g i)
      = (((Polynomial.aeval smoothDerivLM L) (∑ i ∈ s, G i) : smoothSubmodule) : ℝ → ℂ) := by
    rw [coe_aeval_smoothDerivLM, hcoe]
  rw [h1, hmap, ← Submodule.coe_subtype, map_sum]
  exact Finset.sum_congr rfl fun i _ => coe_aeval_smoothDerivLM L (G i)

theorem realConstCoeffOp_zero (L : Polynomial ℂ) :
    realConstCoeffOp L (0 : ℝ → ℂ) = 0 := by
  have h := realConstCoeffOp_sum (∅ : Finset ℕ) L (fun _ => (0 : ℝ → ℂ)) (fun _ => contDiff_const)
  simpa using h

/-! ## Independence of distinct frequencies -/

/-- **Blocks with distinct frequencies are independent.**  A vanishing finite sum of blocks with
pairwise distinct frequencies has every polynomial equal to zero. -/
theorem eq_zero_of_sum_polyExp_eq_zero {S : Finset ℂ} {P : ℂ → Polynomial ℂ}
    (h : ∑ μ ∈ S, polyExp (P μ) μ = 0) {ν : ℂ} (hν : ν ∈ S) : P ν = 0 := by
  classical
  set L : Polynomial ℂ :=
    ∏ μ ∈ S.erase ν, (Polynomial.X - Polynomial.C μ) ^ ((P μ).natDegree + 1) with hL
  have hop : ∑ μ ∈ S, polyExp (exponentialPolynomialModesBlockOp L μ (P μ)) μ = 0 := by
    have hsum := realConstCoeffOp_sum S L (fun μ => polyExp (P μ) μ)
      (fun μ => contDiff_polyExp _ _)
    rw [h, realConstCoeffOp_zero] at hsum
    exact (Finset.sum_congr rfl fun κ _ =>
      (realConstCoeffOp_polyExp L (P κ) κ).symm).trans hsum.symm
  have hkill : ∀ μ ∈ S, μ ≠ ν → polyExp (exponentialPolynomialModesBlockOp L μ (P μ)) μ = 0 := by
    intro μ hμS hμν
    have hmem : μ ∈ S.erase ν := Finset.mem_erase.mpr ⟨hμν, hμS⟩
    have hfac : L = (∏ κ ∈ (S.erase ν).erase μ,
        (Polynomial.X - Polynomial.C κ) ^ ((P κ).natDegree + 1))
        * (Polynomial.X - Polynomial.C μ) ^ ((P μ).natDegree + 1) := by
      rw [hL, ← Finset.prod_erase_mul _ _ hmem]
    rw [hfac, blockOp_mul, blockOp_XsubC_pow,
      Polynomial.iterate_derivative_eq_zero (by omega), map_zero, polyExp_eq_zero_poly]
  have hsingle : polyExp (exponentialPolynomialModesBlockOp L ν (P ν)) ν = 0 := by
    rw [← hop]
    exact (Finset.sum_eq_single ν hkill (fun hc => absurd hν hc)).symm
  have hblock : exponentialPolynomialModesBlockOp L ν (P ν) = 0 := (polyExp_eq_zero_iff _ _).mp hsingle
  by_contra hPν
  refine blockOp_ne_zero ?_ hPν hblock
  rw [hL, Polynomial.eval_prod]
  refine Finset.prod_ne_zero_iff.mpr fun μ hμ => ?_
  have hμν : μ ≠ ν := (Finset.mem_erase.mp hμ).1
  simp only [Polynomial.eval_pow, Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C]
  exact pow_ne_zero _ (sub_ne_zero.mpr (Ne.symm hμν))

/-! ## The degree bound at a root -/

theorem iterate_derivative_ne_zero {P : Polynomial ℂ} (hP : P ≠ 0) {m : ℕ}
    (hm : m ≤ P.natDegree) : (⇑Polynomial.derivative)^[m] P ≠ 0 := by
  intro h
  have hc := Polynomial.coeff_iterate_derivative (k := m) P (P.natDegree - m)
  rw [h, Polynomial.coeff_zero] at hc
  have hidx : P.natDegree - m + m = P.natDegree := by omega
  rw [hidx] at hc
  have hfac : (P.natDegree).descFactorial m ≠ 0 := by
    rw [Ne, Nat.descFactorial_eq_zero_iff_lt]
    omega
  have hlead : P.coeff P.natDegree ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hP
  rw [nsmul_eq_mul] at hc
  exact (mul_ne_zero (Nat.cast_ne_zero.mpr hfac) hlead) hc.symm

/-- **The degree at a root is below its multiplicity.** -/
theorem natDegree_lt_rootMultiplicity_of_blockOp_eq_zero {L P : Polynomial ℂ} {μ : ℂ}
    (hL : L ≠ 0) (hP : P ≠ 0) (h : exponentialPolynomialModesBlockOp L μ P = 0) :
    P.natDegree < L.rootMultiplicity μ := by
  by_contra hcon
  rw [not_lt] at hcon
  set m := L.rootMultiplicity μ with hm
  set M := L /ₘ (Polynomial.X - Polynomial.C μ) ^ m with hM
  have hfac : (Polynomial.X - Polynomial.C μ) ^ m * M = L :=
    Polynomial.pow_mul_divByMonic_rootMultiplicity_eq L μ
  have hMev : M.eval μ ≠ 0 := Polynomial.eval_divByMonic_pow_rootMultiplicity_ne_zero μ hL
  have hcomm : L = M * (Polynomial.X - Polynomial.C μ) ^ m := by
    rw [← hfac]; ring
  rw [hcomm, blockOp_mul, blockOp_XsubC_pow] at h
  exact blockOp_ne_zero hMev (iterate_derivative_ne_zero hP hcon) h

/-! ## The block normal form of an exponential polynomial -/

/-- Finite sums of blocks with frequencies in `S`. -/
def blockSpan (S : Finset ℂ) : Submodule ℂ (ℝ → ℂ) where
  carrier := {f : ℝ → ℂ | ∃ P : ℂ → Polynomial ℂ, f = ∑ μ ∈ S, polyExp (P μ) μ}
  add_mem' := by
    rintro f g ⟨P, rfl⟩ ⟨Q, rfl⟩
    refine ⟨fun μ => P μ + Q μ, ?_⟩
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun μ _ => (polyExp_add_poly (P μ) (Q μ) μ).symm
  zero_mem' := ⟨fun _ => 0, by simp [polyExp_eq_zero_poly]⟩
  smul_mem' := by
    rintro c f ⟨P, rfl⟩
    refine ⟨fun μ => c • P μ, ?_⟩
    rw [Finset.smul_sum]
    exact Finset.sum_congr rfl fun μ _ => (polyExp_smul_poly c (P μ) μ).symm

theorem expMonomialSpace_le_blockSpan (N : ℕ) (S : Finset ℂ) :
    expMonomialSpace N S ≤ blockSpan S := by
  classical
  rw [expMonomialSpace, Submodule.span_le]
  rintro u ⟨p, hp, rfl⟩
  simp only [Finset.coe_product, Set.mem_prod, Finset.mem_coe] at hp
  refine ⟨fun μ => if μ = p.2 then Polynomial.X ^ p.1 else 0, ?_⟩
  rw [Finset.sum_eq_single p.2 (fun μ _ hμ => by simp [hμ, polyExp_eq_zero_poly])
    (fun hc => absurd hp.2 hc)]
  simp

/-- **The characteristic-mode theorem.**  A smooth solution of `L(D) g = 0` is a finite sum of
blocks whose frequencies are roots of `L` and whose polynomial degree at each root is strictly below
that root's multiplicity. -/
theorem exists_characteristic_modes {g : ℝ → ℂ} (hg : ContDiff ℝ (⊤ : ℕ∞) g)
    {L : Polynomial ℂ} (hL : L ≠ 0) (hzero : realConstCoeffOp L g = 0) :
    ∃ (S : Finset ℂ) (P : ℂ → Polynomial ℂ),
      g = ∑ μ ∈ S, polyExp (P μ) μ ∧
        ∀ μ ∈ S, P μ ≠ 0 → L.eval μ = 0 ∧ (P μ).natDegree < L.rootMultiplicity μ := by
  classical
  obtain ⟨N, S, hmem⟩ :=
    exists_expMonomialSpace_of_mem_expPolySpace
      (mem_expPolySpace_of_realConstCoeffOp_eq_zero hg hL hzero)
  obtain ⟨P, hP⟩ := expMonomialSpace_le_blockSpan N S hmem
  refine ⟨S, P, hP, ?_⟩
  intro μ hμ hPμ
  have hop : ∑ κ ∈ S, polyExp (exponentialPolynomialModesBlockOp L κ (P κ)) κ = 0 := by
    have hsum := realConstCoeffOp_sum S L (fun κ => polyExp (P κ) κ)
      (fun κ => contDiff_polyExp _ _)
    rw [← hP, hzero] at hsum
    exact (Finset.sum_congr rfl fun κ _ =>
      (realConstCoeffOp_polyExp L (P κ) κ).symm).trans hsum.symm
  have hblock : exponentialPolynomialModesBlockOp L μ (P μ) = 0 := eq_zero_of_sum_polyExp_eq_zero hop hμ
  have hdeg := natDegree_lt_rootMultiplicity_of_blockOp_eq_zero hL hPμ hblock
  refine ⟨?_, hdeg⟩
  have hpos : 0 < L.rootMultiplicity μ := by omega
  exact (Polynomial.rootMultiplicity_pos hL).mp hpos

end

end GaloisForLFunctions.HTGeometry
