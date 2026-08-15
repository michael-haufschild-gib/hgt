import GaloisForLFunctions.HTGeometry.ExponentialPolynomialModes

/-!
# The solution space of a constant-coefficient operator has dimension its degree

`ExponentialPolynomialModes` shows that a smooth solution of `L(D) g = 0` is a sum of blocks
`P_μ(x) e^{μ x}` over the roots of `L`, with `deg P_μ` below the multiplicity of `μ`.  Here the
count is made exact: the family

```text
x^k e^{μ x} ,     μ a root of L ,   k < rootMultiplicity μ L ,
```

is a basis of the solution space, so that space has dimension exactly `deg L`.

Independence is the distinct-frequency independence of the previous module, applied after grouping
the family by frequency; the cardinality is `∑_μ rootMultiplicity μ = card L.roots = deg L`, which
holds because `ℂ` is algebraically closed.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

open scoped BigOperators

/-! ## The characteristic modes -/

/-- The characteristic mode `x ↦ x^k e^{μ x}`. -/
def charMode (μ : ℂ) (k : ℕ) : ℝ → ℂ := polyExp (Polynomial.X ^ k) μ

/-- One index for each root of `L`, repeated up to its multiplicity. -/
abbrev CharIndex (L : Polynomial ℂ) : Type :=
  Σ μ : {x : ℂ // x ∈ L.roots.toFinset}, Fin (L.rootMultiplicity μ.1)

/-- The characteristic-mode family of `L`. -/
def charFamily (L : Polynomial ℂ) : CharIndex L → (ℝ → ℂ) :=
  fun p => charMode p.1.1 p.2.1

/-- The span of the characteristic modes. -/
def modeSpace (L : Polynomial ℂ) : Submodule ℂ (ℝ → ℂ) :=
  Submodule.span ℂ (Set.range (charFamily L))

/-! ## Elementary block identities -/

theorem polyExp_finsetSum {ι : Type*} (s : Finset ι) (P : ι → Polynomial ℂ) (μ : ℂ) :
    polyExp (∑ i ∈ s, P i) μ = ∑ i ∈ s, polyExp (P i) μ := by
  funext x
  simp only [polyExp, polyExpC, Polynomial.eval_finsetSum, Finset.sum_apply, Finset.sum_mul]

theorem polyExp_monomial (k : ℕ) (a μ : ℂ) :
    polyExp (Polynomial.monomial k a) μ = a • charMode μ k := by
  funext x
  simp only [polyExp, polyExpC, charMode, Polynomial.eval_monomial, Pi.smul_apply, smul_eq_mul,
    Polynomial.eval_pow, Polynomial.eval_X]
  ring

theorem polyExp_eq_sum_charMode (P : Polynomial ℂ) (μ : ℂ) {N : ℕ} (hN : P.natDegree ≤ N) :
    polyExp P μ = ∑ k ∈ Finset.range (N + 1), P.coeff k • charMode μ k := by
  have hP : P = ∑ k ∈ Finset.range (N + 1), Polynomial.monomial k (P.coeff k) :=
    Polynomial.as_sum_range' P (N + 1) (by omega)
  conv_lhs => rw [hP]
  rw [polyExp_finsetSum]
  exact Finset.sum_congr rfl fun k _ => polyExp_monomial k _ μ

theorem contDiff_charMode (μ : ℂ) (k : ℕ) : ContDiff ℝ (⊤ : ℕ∞) (charMode μ k) :=
  contDiff_polyExp _ _

/-! ## The modes are annihilated -/

theorem blockOp_X_pow_eq_zero {L : Polynomial ℂ} {μ : ℂ} {k : ℕ}
    (hk : k < L.rootMultiplicity μ) :
    blockOp L μ (Polynomial.X ^ k) = 0 := by
  set m := L.rootMultiplicity μ with hm
  have hfac : (Polynomial.X - Polynomial.C μ) ^ m * (L /ₘ (Polynomial.X - Polynomial.C μ) ^ m)
      = L := Polynomial.pow_mul_divByMonic_rootMultiplicity_eq L μ
  have hcomm : L = (L /ₘ (Polynomial.X - Polynomial.C μ) ^ m)
      * (Polynomial.X - Polynomial.C μ) ^ m := by
    rw [mul_comm]
    exact hfac.symm
  rw [hcomm, blockOp_mul, blockOp_XsubC_pow,
    Polynomial.iterate_derivative_eq_zero (by simpa using hk), map_zero]

/-- **Every characteristic mode solves the equation.** -/
theorem realConstCoeffOp_charMode {L : Polynomial ℂ} {μ : ℂ} {k : ℕ}
    (hk : k < L.rootMultiplicity μ) :
    realConstCoeffOp L (charMode μ k) = 0 := by
  rw [charMode, realConstCoeffOp_polyExp, blockOp_X_pow_eq_zero hk, polyExp_eq_zero_poly]

/-! ## Independence of the characteristic family -/

/-- **The characteristic modes are linearly independent.** -/
theorem linearIndependent_charFamily (L : Polynomial ℂ) :
    LinearIndependent ℂ (charFamily L) := by
  classical
  rw [Fintype.linearIndependent_iff]
  intro c hc p
  set C : ℂ → ℕ → ℂ := fun μ k =>
    if h : μ ∈ L.roots.toFinset then
      (if hk : k < L.rootMultiplicity μ then c ⟨⟨μ, h⟩, ⟨k, hk⟩⟩ else 0) else 0 with hC
  set P : ℂ → Polynomial ℂ := fun μ =>
    ∑ k ∈ Finset.range (L.rootMultiplicity μ), Polynomial.monomial k (C μ k) with hP
  have hcC : ∀ (μ : {x : ℂ // x ∈ L.roots.toFinset}) (k : Fin (L.rootMultiplicity μ.1)),
      C μ.1 k.1 = c ⟨μ, k⟩ := by
    intro μ k
    rw [hC]
    simp only [dif_pos μ.2, dif_pos k.2]
  have hblock : ∀ μ : {x : ℂ // x ∈ L.roots.toFinset},
      polyExp (P μ.1) μ.1
        = ∑ k : Fin (L.rootMultiplicity μ.1), c ⟨μ, k⟩ • charFamily L ⟨μ, k⟩ := by
    intro μ
    rw [hP]
    simp only
    rw [polyExp_finsetSum,
      ← Fin.sum_univ_eq_sum_range (fun k => polyExp (Polynomial.monomial k (C μ.1 k)) μ.1)
        (L.rootMultiplicity μ.1)]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [polyExp_monomial, hcC μ k]
    rfl
  have hsum0 : ∑ μ ∈ L.roots.toFinset, polyExp (P μ) μ = 0 := by
    rw [← Finset.sum_coe_sort L.roots.toFinset (fun μ => polyExp (P μ) μ)]
    rw [Finset.sum_congr rfl fun μ _ => hblock μ]
    rw [← hc]
    rw [← Finset.univ_sigma_univ, Finset.sum_sigma]
  obtain ⟨μ, k⟩ := p
  have hPz : P μ.1 = 0 := eq_zero_of_sum_polyExp_eq_zero hsum0 μ.2
  have hcoeff : (P μ.1).coeff k.1 = C μ.1 k.1 := by
    rw [hP]
    simp only [Polynomial.finsetSum_coeff, Polynomial.coeff_monomial]
    rw [Finset.sum_ite_eq' (Finset.range (L.rootMultiplicity μ.1)) k.1 (fun j => C μ.1 j)]
    rw [if_pos (Finset.mem_range.mpr k.2)]
  rw [← hcC μ k, ← hcoeff, hPz, Polynomial.coeff_zero]

/-! ## The cardinality of the characteristic index -/

theorem card_charIndex (L : Polynomial ℂ) :
    Fintype.card (CharIndex L) = L.natDegree := by
  classical
  rw [Fintype.card_sigma]
  simp only [Fintype.card_fin]
  rw [Finset.sum_coe_sort L.roots.toFinset (fun μ => L.rootMultiplicity μ)]
  have hcount : ∀ μ ∈ L.roots.toFinset, L.rootMultiplicity μ = L.roots.count μ :=
    fun μ _ => (Polynomial.count_roots L).symm ▸ rfl
  rw [Finset.sum_congr rfl hcount, Multiset.toFinset_sum_count_eq]
  exact (Polynomial.Splits.natDegree_eq_card_roots (IsAlgClosed.splits L)).symm

/-! ## The dimension of the mode space -/

/-- **The characteristic modes have dimension exactly the degree.** -/
theorem finrank_modeSpace (L : Polynomial ℂ) :
    Module.finrank ℂ (modeSpace L) = L.natDegree := by
  rw [modeSpace, finrank_span_eq_card (linearIndependent_charFamily L), card_charIndex L]

/-! ## The mode space is the solution space -/

theorem realConstCoeffOp_add {L : Polynomial ℂ} {f g : ℝ → ℂ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hg : ContDiff ℝ (⊤ : ℕ∞) g) :
    realConstCoeffOp L (f + g) = realConstCoeffOp L f + realConstCoeffOp L g := by
  have e1 : (((Polynomial.aeval smoothDerivLM L)
        ((⟨f, hf⟩ : smoothSubmodule) + (⟨g, hg⟩ : smoothSubmodule)) : smoothSubmodule) : ℝ → ℂ)
      = realConstCoeffOp L (f + g) :=
    coe_aeval_smoothDerivLM L ((⟨f, hf⟩ : smoothSubmodule) + (⟨g, hg⟩ : smoothSubmodule))
  have e2 : (((Polynomial.aeval smoothDerivLM L) (⟨f, hf⟩ : smoothSubmodule)
        : smoothSubmodule) : ℝ → ℂ) = realConstCoeffOp L f :=
    coe_aeval_smoothDerivLM L (⟨f, hf⟩ : smoothSubmodule)
  have e3 : (((Polynomial.aeval smoothDerivLM L) (⟨g, hg⟩ : smoothSubmodule)
        : smoothSubmodule) : ℝ → ℂ) = realConstCoeffOp L g :=
    coe_aeval_smoothDerivLM L (⟨g, hg⟩ : smoothSubmodule)
  rw [← e1, ← e2, ← e3, map_add]
  rfl

theorem realConstCoeffOp_smul {L : Polynomial ℂ} (a : ℂ) {f : ℝ → ℂ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) :
    realConstCoeffOp L (a • f) = a • realConstCoeffOp L f := by
  have e1 : (((Polynomial.aeval smoothDerivLM L) (a • (⟨f, hf⟩ : smoothSubmodule))
        : smoothSubmodule) : ℝ → ℂ) = realConstCoeffOp L (a • f) :=
    coe_aeval_smoothDerivLM L (a • (⟨f, hf⟩ : smoothSubmodule))
  have e2 : (((Polynomial.aeval smoothDerivLM L) (⟨f, hf⟩ : smoothSubmodule)
        : smoothSubmodule) : ℝ → ℂ) = realConstCoeffOp L f :=
    coe_aeval_smoothDerivLM L (⟨f, hf⟩ : smoothSubmodule)
  rw [← e1, ← e2, map_smul]
  rfl

/-- The smooth solutions of `L(D) g = 0`. -/
def solutionSpace (L : Polynomial ℂ) : Submodule ℂ (ℝ → ℂ) where
  carrier := {g : ℝ → ℂ | ContDiff ℝ (⊤ : ℕ∞) g ∧ realConstCoeffOp L g = 0}
  add_mem' := by
    rintro f g ⟨hf, hf0⟩ ⟨hg, hg0⟩
    exact ⟨hf.add hg, by rw [realConstCoeffOp_add hf hg, hf0, hg0, add_zero]⟩
  zero_mem' := ⟨contDiff_const, realConstCoeffOp_zero L⟩
  smul_mem' := by
    rintro a f ⟨hf, hf0⟩
    exact ⟨hf.const_smul a, by rw [realConstCoeffOp_smul a hf, hf0, smul_zero]⟩

theorem modeSpace_le_solutionSpace (L : Polynomial ℂ) : modeSpace L ≤ solutionSpace L := by
  rw [modeSpace, Submodule.span_le]
  rintro u ⟨p, rfl⟩
  exact ⟨contDiff_charMode _ _, realConstCoeffOp_charMode p.2.2⟩

theorem solutionSpace_le_modeSpace {L : Polynomial ℂ} (hL : L ≠ 0) :
    solutionSpace L ≤ modeSpace L := by
  classical
  rintro g ⟨hg, hg0⟩
  obtain ⟨S, P, hgP, hroot⟩ := exists_characteristic_modes hg hL hg0
  rw [hgP]
  refine Submodule.sum_mem _ fun μ hμ => ?_
  by_cases hPμ : P μ = 0
  · rw [hPμ, polyExp_eq_zero_poly]
    exact Submodule.zero_mem _
  · obtain ⟨hev, hdeg⟩ := hroot μ hμ hPμ
    rw [polyExp_eq_sum_charMode (P μ) μ (le_refl (P μ).natDegree)]
    refine Submodule.sum_mem _ fun k hk => ?_
    refine Submodule.smul_mem _ _ ?_
    refine Submodule.subset_span ?_
    have hkm : k < L.rootMultiplicity μ := by
      rw [Finset.mem_range] at hk
      omega
    have hμroot : μ ∈ L.roots.toFinset := by
      rw [Multiset.mem_toFinset, Polynomial.mem_roots hL]
      exact hev
    exact Set.mem_range.mpr ⟨Sigma.mk ⟨μ, hμroot⟩ ⟨k, hkm⟩, rfl⟩

/-- **The solution space is exactly the span of the characteristic modes.** -/
theorem solutionSpace_eq_modeSpace {L : Polynomial ℂ} (hL : L ≠ 0) :
    solutionSpace L = modeSpace L :=
  le_antisymm (solutionSpace_le_modeSpace hL) (modeSpace_le_solutionSpace L)

/-- **The solution space of a constant-coefficient operator has dimension its degree.** -/
theorem finrank_solutionSpace {L : Polynomial ℂ} (hL : L ≠ 0) :
    Module.finrank ℂ (solutionSpace L) = L.natDegree := by
  rw [solutionSpace_eq_modeSpace hL, finrank_modeSpace L]

end

end GaloisForLFunctions.HTGeometry
