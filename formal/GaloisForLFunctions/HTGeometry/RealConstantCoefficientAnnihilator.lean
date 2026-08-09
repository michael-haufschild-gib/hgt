import GaloisForLFunctions.HTGeometry.RealExponentialPolynomial

/-!
# Constant-coefficient annihilators on the real line

A smooth function `g : ℝ → ℂ` is annihilated by the constant-coefficient operator `L(D)` when
`∑ⱼ Lⱼ · g⁽ʲ⁾ ≡ 0`.  Writing `L` in factored form `∏ⱼ (X − λⱼ)^{mⱼ}` and integrating the factors
one at a time identifies the solution space:

* `mem_expPolySpace_of_realConstCoeffOp_eq_zero` — a smooth function killed by a nonzero
  constant-coefficient operator is an exponential polynomial;
* `realConstCoeffOp_of_mem_expPolySpace` — conversely every exponential polynomial is killed by
  such an operator, exhibited as `∏ⱼ (X − λⱼ)^{1+deg Pⱼ}`.

The algebra is carried by `smoothDerivLM`, the differentiation endomorphism of the module
`smoothSubmodule` of smooth functions, so that `Polynomial.aeval` supplies the operator calculus
(in particular the factorization of a product of operators into a composition) for free.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

open scoped BigOperators

/-! ## The module of smooth functions and its differentiation endomorphism -/

/-- The `ℂ`-submodule of `Cⁿ` functions on the real line. -/
def contDiffSubmodule (n : WithTop ℕ∞) : Submodule ℂ (ℝ → ℂ) where
  carrier := {g : ℝ → ℂ | ContDiff ℝ n g}
  add_mem' hf hg := hf.add hg
  zero_mem' := contDiff_const
  smul_mem' c _ hg := hg.const_smul c

theorem mem_contDiffSubmodule {n : WithTop ℕ∞} {g : ℝ → ℂ} :
    g ∈ contDiffSubmodule n ↔ ContDiff ℝ n g := Iff.rfl

/-- The `ℂ`-submodule of smooth functions on the real line. -/
def smoothSubmodule : Submodule ℂ (ℝ → ℂ) := contDiffSubmodule ((⊤ : ℕ∞) : WithTop ℕ∞)

theorem mem_smoothSubmodule {g : ℝ → ℂ} :
    g ∈ smoothSubmodule ↔ ContDiff ℝ (⊤ : ℕ∞) g := Iff.rfl

theorem differentiable_of_mem_smoothSubmodule {g : ℝ → ℂ} (hg : g ∈ smoothSubmodule) :
    Differentiable ℝ g := (contDiff_infty_iff_deriv.mp hg).1

theorem deriv_mem_smoothSubmodule {g : ℝ → ℂ} (hg : g ∈ smoothSubmodule) :
    deriv g ∈ smoothSubmodule := (contDiff_infty_iff_deriv.mp hg).2

/-- Differentiation as an endomorphism of the smooth functions. -/
def smoothDerivLM : smoothSubmodule →ₗ[ℂ] smoothSubmodule where
  toFun g := ⟨deriv (g : ℝ → ℂ), deriv_mem_smoothSubmodule g.2⟩
  map_add' g h := by
    apply Subtype.ext
    funext x
    exact deriv_add ((differentiable_of_mem_smoothSubmodule g.2) x)
      ((differentiable_of_mem_smoothSubmodule h.2) x)
  map_smul' c g := by
    apply Subtype.ext
    funext x
    simpa using deriv_const_smul (hf := (differentiable_of_mem_smoothSubmodule g.2) x) c

theorem smoothDerivLM_coe (g : smoothSubmodule) :
    ((smoothDerivLM g : smoothSubmodule) : ℝ → ℂ) = deriv (g : ℝ → ℂ) := rfl

theorem smoothDerivLM_pow_coe (n : ℕ) (g : smoothSubmodule) :
    (((smoothDerivLM ^ n) g : smoothSubmodule) : ℝ → ℂ) = iteratedDeriv n (g : ℝ → ℂ) := by
  induction n generalizing g with
  | zero => simp [iteratedDeriv_zero]
  | succ n ih =>
      have hpow : (smoothDerivLM ^ (n + 1)) g = (smoothDerivLM ^ n) (smoothDerivLM g) := by
        rw [pow_succ]
        rfl
      rw [hpow, ih, smoothDerivLM_coe, ← iteratedDeriv_succ']

/-! ## The pointwise operator -/

/-- Pointwise application of a constant-coefficient differential operator on the real line. -/
def realConstCoeffOp (L : Polynomial ℂ) (g : ℝ → ℂ) : ℝ → ℂ :=
  fun x => L.sum fun j a => a * iteratedDeriv j g x

theorem realConstCoeffOp_eq_sum_range (L : Polynomial ℂ) (g : ℝ → ℂ) (x : ℝ) :
    realConstCoeffOp L g x
      = ∑ i ∈ Finset.range (L.natDegree + 1), L.coeff i * iteratedDeriv i g x :=
  L.sum_over_range (fun _ => by ring)

/-- **The pointwise operator is the polynomial evaluation of the differentiation
endomorphism.** -/
theorem coe_aeval_smoothDerivLM (L : Polynomial ℂ) (g : smoothSubmodule) :
    (((Polynomial.aeval smoothDerivLM L) g : smoothSubmodule) : ℝ → ℂ)
      = realConstCoeffOp L (g : ℝ → ℂ) := by
  funext x
  rw [realConstCoeffOp_eq_sum_range, Polynomial.aeval_eq_sum_range (x := smoothDerivLM)]
  rw [LinearMap.coe_sum]
  simp only [Finset.sum_apply]
  rw [Submodule.coe_sum]
  simp only [Finset.sum_apply, SetLike.val_smul, LinearMap.smul_apply, Pi.smul_apply,
    smul_eq_mul]
  exact Finset.sum_congr rfl fun i _ => by
    rw [show (((smoothDerivLM ^ i) g : smoothSubmodule) : ℝ → ℂ) x
      = iteratedDeriv i (g : ℝ → ℂ) x from congrFun (smoothDerivLM_pow_coe i g) x]

/-! ## Solutions of a constant-coefficient equation -/

private theorem mem_expPolySpace_aux :
    ∀ n : ℕ, ∀ L : Polynomial ℂ, L.natDegree ≤ n → L ≠ 0 → ∀ g : smoothSubmodule,
      (Polynomial.aeval smoothDerivLM L) g = 0 → (g : ℝ → ℂ) ∈ expPolySpace := by
  intro n
  induction n with
  | zero =>
      intro L hdeg hL g hg
      have hLC : L = Polynomial.C (L.coeff 0) := Polynomial.eq_C_of_natDegree_le_zero hdeg
      have hc0 : L.coeff 0 ≠ 0 := by
        intro h
        exact hL (by rw [hLC, h, map_zero])
      have hgz : L.coeff 0 • g = 0 := by
        have : (Polynomial.aeval smoothDerivLM) L
            = L.coeff 0 • (1 : Module.End ℂ smoothSubmodule) := by
          conv_lhs => rw [hLC]
          rw [Polynomial.aeval_C, Algebra.algebraMap_eq_smul_one]
        rw [this] at hg
        simpa using hg
      have : g = 0 := by
        have := congrArg (fun v => (L.coeff 0)⁻¹ • v) hgz
        simpa [smul_smul, inv_mul_cancel₀ hc0] using this
      rw [this]
      simp
  | succ n ih =>
      intro L hdeg hL g hg
      by_cases hsmall : L.natDegree ≤ n
      · exact ih L hsmall hL g hg
      have hdegpos : 0 < L.natDegree := by omega
      have hdegne : L.degree ≠ 0 := by
        intro h
        have : L.natDegree = 0 := Polynomial.natDegree_eq_zero_iff_degree_le_zero.mpr (le_of_eq h)
        omega
      obtain ⟨lam, hlam⟩ := Complex.isAlgClosed.exists_root L hdegne
      obtain ⟨M, hM⟩ := (Polynomial.dvd_iff_isRoot.mpr hlam)
      have hM0 : M ≠ 0 := by
        intro h
        rw [h, mul_zero] at hM
        exact hL hM
      have hXC0 : (Polynomial.X - Polynomial.C lam) ≠ 0 := Polynomial.X_sub_C_ne_zero lam
      have hdegM : M.natDegree ≤ n := by
        have hmul : L.natDegree = (Polynomial.X - Polynomial.C lam).natDegree + M.natDegree := by
          rw [hM, Polynomial.natDegree_mul hXC0 hM0]
        rw [Polynomial.natDegree_X_sub_C] at hmul
        omega
      -- factor the operator as `M(D) ∘ (D − λ)`
      set h : smoothSubmodule := (Polynomial.aeval smoothDerivLM (Polynomial.X - Polynomial.C lam)) g
        with hhdef
      have hfact : (Polynomial.aeval smoothDerivLM M) h = 0 := by
        rw [hhdef, ← Module.End.mul_apply, ← map_mul]
        rw [show M * (Polynomial.X - Polynomial.C lam) = L by rw [hM]; ring]
        exact hg
      have hhmem : (h : ℝ → ℂ) ∈ expPolySpace := ih M hdegM hM0 h hfact
      have hhcoe : (h : ℝ → ℂ) = deriv (g : ℝ → ℂ) - lam • (g : ℝ → ℂ) := by
        rw [hhdef]
        rw [map_sub, Polynomial.aeval_X, Polynomial.aeval_C, Algebra.algebraMap_eq_smul_one]
        simp [smoothDerivLM_coe]
      obtain ⟨G, hGmem, hGeq⟩ := exists_expPolySpace_solve lam hhmem
      set u : ℝ → ℂ := (g : ℝ → ℂ) - G with hu
      have hudiff : Differentiable ℝ u :=
        (differentiable_of_mem_smoothSubmodule g.2).sub (differentiable_of_mem_expPolySpace hGmem)
      have hderivu : ∀ x, deriv u x = lam * u x := by
        intro x
        have hd : deriv u x = deriv (g : ℝ → ℂ) x - deriv G x := by
          rw [hu]
          exact deriv_sub ((differentiable_of_mem_smoothSubmodule g.2) x)
            ((differentiable_of_mem_expPolySpace hGmem) x)
        have h1 : deriv (g : ℝ → ℂ) x - lam * (g : ℝ → ℂ) x = (h : ℝ → ℂ) x := by
          rw [hhcoe]; simp
        have h2 : deriv G x - lam * G x = (h : ℝ → ℂ) x := by
          rw [← hGeq]; simp
        rw [hd, hu]
        have := h1.trans h2.symm
        simp only [Pi.sub_apply]
        linear_combination this
      have humem : u ∈ expPolySpace := mem_expPolySpace_of_deriv_eq_smul hudiff hderivu
      have : (g : ℝ → ℂ) = u + G := by rw [hu]; abel
      rw [this]
      exact Submodule.add_mem _ humem hGmem

/-- **A smooth function killed by a nonzero constant-coefficient operator is an exponential
polynomial.** -/
theorem mem_expPolySpace_of_realConstCoeffOp_eq_zero {g : ℝ → ℂ}
    (hg : ContDiff ℝ (⊤ : ℕ∞) g) {L : Polynomial ℂ} (hL : L ≠ 0)
    (hzero : realConstCoeffOp L g = 0) : g ∈ expPolySpace := by
  have hgm : g ∈ smoothSubmodule := hg
  have hval : (Polynomial.aeval smoothDerivLM L) (⟨g, hgm⟩ : smoothSubmodule) = 0 := by
    apply Subtype.ext
    rw [coe_aeval_smoothDerivLM]
    simpa using hzero
  exact mem_expPolySpace_aux L.natDegree L le_rfl hL ⟨g, hgm⟩ hval

/-! ## Every exponential polynomial has a constant-coefficient annihilator -/

private theorem aeval_XsubC_pow_block (μ : ℂ) :
    ∀ (k : ℕ) (P : Polynomial ℂ) (h : smoothSubmodule), (h : ℝ → ℂ) = polyExp P μ →
      (((Polynomial.aeval smoothDerivLM ((Polynomial.X - Polynomial.C μ) ^ k)) h :
          smoothSubmodule) : ℝ → ℂ) = polyExp (Polynomial.derivative^[k] P) μ := by
  intro k
  induction k with
  | zero => intro P h hh; simpa using hh
  | succ k ih =>
      intro P h hh
      set h' : smoothSubmodule :=
        (Polynomial.aeval smoothDerivLM (Polynomial.X - Polynomial.C μ)) h with hh'def
      have hh'coe : (h' : ℝ → ℂ) = polyExp (Polynomial.derivative P) μ := by
        have hstep : (h' : ℝ → ℂ) = deriv (h : ℝ → ℂ) - μ • (h : ℝ → ℂ) := by
          rw [hh'def, map_sub, Polynomial.aeval_X, Polynomial.aeval_C,
            Algebra.algebraMap_eq_smul_one]
          simp [smoothDerivLM_coe]
        rw [hstep, hh, deriv_polyExp]
        funext x
        simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, polyExp, polyExpC, shiftPoly,
          Polynomial.eval_add, Polynomial.eval_smul, smul_eq_mul]
        ring
      have hcompose :
          (Polynomial.aeval smoothDerivLM ((Polynomial.X - Polynomial.C μ) ^ (k + 1))) h
            = (Polynomial.aeval smoothDerivLM ((Polynomial.X - Polynomial.C μ) ^ k)) h' := by
        rw [hh'def, ← Module.End.mul_apply, ← map_mul, ← pow_succ]
      rw [hcompose, ih (Polynomial.derivative P) h' hh'coe, Function.iterate_succ_apply]

/-- The functions annihilated by some nonzero constant-coefficient operator. -/
private def annihilatedSpace : Submodule ℂ smoothSubmodule where
  carrier := {g : smoothSubmodule |
    ∃ L : Polynomial ℂ, L ≠ 0 ∧ (Polynomial.aeval smoothDerivLM L) g = 0}
  add_mem' := by
    rintro g h ⟨L, hL, hLg⟩ ⟨M, hM, hMh⟩
    refine ⟨L * M, mul_ne_zero hL hM, ?_⟩
    have h1 : (Polynomial.aeval smoothDerivLM (L * M)) g = 0 := by
      rw [show L * M = M * L by ring, map_mul, Module.End.mul_apply, hLg, map_zero]
    have h2 : (Polynomial.aeval smoothDerivLM (L * M)) h = 0 := by
      rw [map_mul, Module.End.mul_apply, hMh, map_zero]
    rw [map_add, h1, h2, add_zero]
  zero_mem' := ⟨1, one_ne_zero, by simp⟩
  smul_mem' := by
    rintro c g ⟨L, hL, hLg⟩
    exact ⟨L, hL, by rw [map_smul, hLg, smul_zero]⟩

/-- **Every exponential polynomial is killed by a nonzero constant-coefficient operator.**
For a single block `P(x)·e^{μ x}` the operator `(X − μ)^{1 + deg P}` already vanishes on it, and a
finite sum is killed by the product of the block operators. -/
theorem exists_nonzero_realConstCoeffOp_eq_zero_of_mem_expPolySpace {g : ℝ → ℂ}
    (hg : g ∈ expPolySpace) :
    ∃ L : Polynomial ℂ, L ≠ 0 ∧ realConstCoeffOp L g = 0 := by
  have hsub : expPolySpace ≤ Submodule.map smoothSubmodule.subtype annihilatedSpace := by
    rw [expPolySpace]
    refine Submodule.span_le.mpr ?_
    rintro u ⟨p, rfl⟩
    have hmem : polyExp p.1 p.2 ∈ smoothSubmodule := contDiff_polyExp p.1 p.2
    refine ⟨⟨polyExp p.1 p.2, hmem⟩, ?_, rfl⟩
    refine ⟨(Polynomial.X - Polynomial.C p.2) ^ (p.1.natDegree + 1),
      pow_ne_zero _ (Polynomial.X_sub_C_ne_zero p.2), ?_⟩
    apply Subtype.ext
    rw [aeval_XsubC_pow_block p.2 (p.1.natDegree + 1) p.1 ⟨polyExp p.1 p.2, hmem⟩ rfl]
    rw [Polynomial.iterate_derivative_eq_zero (by omega)]
    funext x
    simp [polyExp, polyExpC]
  obtain ⟨v, hv, hveq⟩ := hsub hg
  obtain ⟨L, hL, hLv⟩ := hv
  refine ⟨L, hL, ?_⟩
  have hcoe := congrArg (fun w : smoothSubmodule => (w : ℝ → ℂ)) hLv
  rw [coe_aeval_smoothDerivLM] at hcoe
  have hzero : realConstCoeffOp L (v : ℝ → ℂ) = 0 := by simpa using hcoe
  rwa [show ((v : ℝ → ℂ)) = g from hveq] at hzero

end

end GaloisForLFunctions.HTGeometry
