import GaloisForLFunctions.RHTower.SuzukiLatticeMomentBound

/-!
# Finitely supported lattice fields, and the polynomial moment bound

Every field with finite support is in `ℓ²`, and both the coordinate multiplication and the
finite-range adjacency preserve finite support.  So the moment tower of a finitely supported vector
never leaves `ℓ²`, and the first-order identity may be iterated: each step costs at most one factor
of the time, which is the polynomial group estimate `(15)`.
-/

open Finset

noncomputable section

namespace RHTower

variable {P : Type*} [Fintype P] [DecidableEq P]

local notation "H" => lp (fun _ : (P → ℤ) => ℂ) 2

omit [Fintype P] [DecidableEq P] in
theorem memℓp_of_finite_support {f : (P → ℤ) → ℂ} (hf : (Function.support f).Finite) :
    Memℓp f 2 := by
  refine memℓp_gen ?_
  refine summable_of_hasFiniteSupport (Set.Finite.subset hf ?_)
  intro ν hν
  simp only [Function.mem_support] at hν ⊢
  intro hcon
  rw [hcon] at hν
  simp at hν

omit [Fintype P] [DecidableEq P] in
theorem support_posMulField_subset (p : P) (f : (P → ℤ) → ℂ) :
    Function.support (posMulField p f) ⊆ Function.support f := by
  intro ν hν
  simp only [Function.mem_support, posMulField] at hν ⊢
  intro hcon
  rw [hcon, mul_zero] at hν
  exact hν rfl

omit [Fintype P] [DecidableEq P] in
theorem support_adjacencyField_finite {Q : Finset (P → ℤ)} {c : (P → ℤ) → ℂ}
    {f : (P → ℤ) → ℂ} (hf : (Function.support f).Finite) :
    (Function.support (adjacencyField Q c f)).Finite := by
  classical
  refine Set.Finite.subset (Set.Finite.biUnion (Q.finite_toSet)
    (fun q _ => hf.image (fun ν => ν - q))) ?_
  intro ν hν
  simp only [Function.mem_support, adjacencyField] at hν
  by_contra hcon
  refine hν ?_
  refine Finset.sum_eq_zero fun q hq => ?_
  by_cases hz : f (ν + q) = 0
  · rw [hz, mul_zero]
  · exfalso
    refine hcon ?_
    refine Set.mem_biUnion (Finset.mem_coe.mpr hq) ?_
    exact ⟨ν + q, hz, by abel⟩

omit [Fintype P] [DecidableEq P] in
theorem support_latticeAdjacency_finite {Q : Finset (P → ℤ)} {c : (P → ℤ) → ℂ} {ψ : H}
    (hψ : (Function.support ((ψ : H) : (P → ℤ) → ℂ)).Finite) :
    (Function.support ((latticeAdjacency Q c ψ : H) : (P → ℤ) → ℂ)).Finite := by
  have hfun : ((latticeAdjacency Q c ψ : H) : (P → ℤ) → ℂ)
      = adjacencyField Q c ((ψ : H) : (P → ℤ) → ℂ) := by
    funext ν
    exact latticeAdjacency_apply Q c ψ ν
  rw [hfun]
  exact support_adjacencyField_finite hψ

set_option maxHeartbeats 1000000 in
omit [Fintype P] [DecidableEq P] in
/-- **`(15)`: every coordinate moment of the evolution grows at most polynomially in the time.** -/
theorem exists_norm_posPow_exp_le {Q : Finset (P → ℤ)} {c : (P → ℤ) → ℂ}
    (hsa : IsSelfAdjoint (latticeAdjacency Q c)) (p : P) (n : ℕ) (ψ : H)
    (hfin : (Function.support ((ψ : H) : (P → ℤ) → ℂ)).Finite) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : ℝ, ∃ v : H,
      ((v : H) : (P → ℤ) → ℂ)
        = (fun r => ((r p : ℤ) : ℂ) ^ n
            * ((NormedSpace.exp ((-(x : ℂ) * Complex.I) • latticeAdjacency Q c) ψ : H)
                : (P → ℤ) → ℂ) r)
      ∧ ‖v‖ ≤ C * (1 + |x|) ^ n := by
  induction n generalizing ψ with
  | zero =>
    refine ⟨‖ψ‖, norm_nonneg _, fun x => ?_⟩
    refine ⟨NormedSpace.exp ((-(x : ℂ) * Complex.I) • latticeAdjacency Q c) ψ, ?_, ?_⟩
    · funext r
      simp
    · rw [norm_exp_latticeAdjacency_apply hsa x ψ, pow_zero, mul_one]
  | succ k ih =>
    set φ : H := ⟨posMulField p ((ψ : H) : (P → ℤ) → ℂ),
      memℓp_of_finite_support (hfin.subset (support_posMulField_subset p _))⟩ with hφdef
    have hφ : ((φ : H) : (P → ℤ) → ℂ) = posMulField p ((ψ : H) : (P → ℤ) → ℂ) := rfl
    have hφfin : (Function.support ((φ : H) : (P → ℤ) → ℂ)).Finite := by
      rw [hφ]
      exact hfin.subset (support_posMulField_subset p _)
    have hAfin : (Function.support
        ((latticeAdjacency Q (stepWeighted p c) ψ : H) : (P → ℤ) → ℂ)).Finite :=
      support_latticeAdjacency_finite hfin
    obtain ⟨C₁, hC₁, h₁⟩ := ih φ hφfin
    obtain ⟨C₂, hC₂, h₂⟩ := ih (latticeAdjacency Q (stepWeighted p c) ψ) hAfin
    refine ⟨C₁ + C₂, by linarith, fun x => ?_⟩
    obtain ⟨v₁, hv₁, hn₁⟩ := h₁ x
    obtain ⟨v₂, hv₂, hn₂⟩ := h₂ x
    refine ⟨v₁ - (-(x : ℂ) * Complex.I) • v₂, ?_, ?_⟩
    · funext r
      rw [lp.coeFn_sub, Pi.sub_apply, lp.coeFn_smul, Pi.smul_apply, smul_eq_mul,
        congrFun hv₁ r, congrFun hv₂ r]
      have hkey := eval_posMul_exp Q c p (-(x : ℂ) * Complex.I) ψ φ hφ r
      rw [pow_succ]
      rw [show ((r p : ℤ) : ℂ) ^ k * ((NormedSpace.exp
            ((-(x : ℂ) * Complex.I) • latticeAdjacency Q c) φ : H) : (P → ℤ) → ℂ) r
          - (-(x : ℂ) * Complex.I) * (((r p : ℤ) : ℂ) ^ k
            * ((NormedSpace.exp ((-(x : ℂ) * Complex.I) • latticeAdjacency Q c)
                (latticeAdjacency Q (stepWeighted p c) ψ) : H) : (P → ℤ) → ℂ) r)
        = ((r p : ℤ) : ℂ) ^ k * (((NormedSpace.exp
              ((-(x : ℂ) * Complex.I) • latticeAdjacency Q c) φ : H) : (P → ℤ) → ℂ) r
            - (-(x : ℂ) * Complex.I)
              * ((NormedSpace.exp ((-(x : ℂ) * Complex.I) • latticeAdjacency Q c)
                  (latticeAdjacency Q (stepWeighted p c) ψ) : H) : (P → ℤ) → ℂ) r) by ring,
        ← hkey]
      ring
    · have hz : ‖(-(x : ℂ) * Complex.I)‖ = |x| := by
        rw [norm_mul, norm_neg, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs]
      have hstep : ‖v₁ - (-(x : ℂ) * Complex.I) • v₂‖ ≤ ‖v₁‖ + |x| * ‖v₂‖ := by
        refine le_trans (norm_sub_le _ _) ?_
        rw [norm_smul, hz]
      have habs : (0 : ℝ) ≤ |x| := abs_nonneg x
      have hpow : (0 : ℝ) ≤ (1 + |x|) ^ k := by positivity
      calc ‖v₁ - (-(x : ℂ) * Complex.I) • v₂‖ ≤ ‖v₁‖ + |x| * ‖v₂‖ := hstep
        _ ≤ C₁ * (1 + |x|) ^ k + |x| * (C₂ * (1 + |x|) ^ k) := by
            refine add_le_add hn₁ (mul_le_mul_of_nonneg_left hn₂ habs)
        _ ≤ (C₁ + C₂) * (1 + |x|) ^ (k + 1) := by
            rw [pow_succ]
            nlinarith [mul_nonneg hC₂ hpow, mul_nonneg (mul_nonneg hC₁ habs) hpow]

end RHTower
