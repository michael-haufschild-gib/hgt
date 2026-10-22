import GaloisForLFunctions.RHTower.Suzuki.SuzukiLatticeMomentTower

/-!
# `(15)` in sharp form: the moment bound costs exactly the moment order

Peeling one coordinate factor at a time and applying the exact commutator identity, the `n`-th
coordinate moment of the evolution is bounded by `(1+|x|)^n` times a bound for the moments of the
initial field *of order at most `n`*.  Nothing is lost: the binomial transfer never raises the
moment order, so applying this with the weight `⟨r⟩^{-m}` — for which all moments up to order `m`
are bounded by the norm — gives the polynomial group estimate with the sharp exponent `m`.
-/

open Finset

noncomputable section

namespace RHTower

variable {P : Type*} [Fintype P] [DecidableEq P]

local notation "H" => lp (fun _ : (P → ℤ) => ℂ) 2

omit [Fintype P] [DecidableEq P] in
theorem posPowField_succ' (p : P) (j : ℕ) (ψ : (P → ℤ) → ℂ) :
    posPowField p (j + 1) ψ = posPowField p j (posMulField p ψ) := by
  funext r
  rw [posPowField, posPowField, posMulField, pow_succ]
  ring

omit [Fintype P] [DecidableEq P] in
theorem posPowField_sub (p : P) (j : ℕ) (ψ φ : (P → ℤ) → ℂ) :
    posPowField p j (fun r => ψ r - φ r)
      = fun r => posPowField p j ψ r - posPowField p j φ r := by
  funext r
  rw [posPowField, posPowField, posPowField]
  ring

/-- The constant produced by the binomial transfer at order `n`. -/
def transferConst (Q : Finset (P → ℤ)) (c : (P → ℤ) → ℂ) (p : P) (n : ℕ) : ℝ :=
  ∑ i ∈ Finset.range (n + 1), ∑ i' ∈ Finset.range (i + 1), ((i.choose i' : ℕ) : ℝ)
    * ∑ q ∈ Q, ‖stepPowWeighted p (i - i') (stepWeighted p c) q‖

omit [Fintype P] [DecidableEq P] in
theorem transferConst_nonneg (Q : Finset (P → ℤ)) (c : (P → ℤ) → ℂ) (p : P) (n : ℕ) :
    0 ≤ transferConst Q c p n := by
  rw [transferConst]
  refine Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun i' _ => ?_
  positivity

omit [Fintype P] [DecidableEq P] in
theorem le_transferConst (Q : Finset (P → ℤ)) (c : (P → ℤ) → ℂ) (p : P) (n : ℕ)
    {i : ℕ} (hi : i ∈ Finset.range (n + 1)) :
    (∑ i' ∈ Finset.range (i + 1), ((i.choose i' : ℕ) : ℝ)
      * ∑ q ∈ Q, ‖stepPowWeighted p (i - i') (stepWeighted p c) q‖)
      ≤ transferConst Q c p n := by
  rw [transferConst]
  refine Finset.single_le_sum (f := fun i => ∑ i' ∈ Finset.range (i + 1), ((i.choose i' : ℕ) : ℝ)
    * ∑ q ∈ Q, ‖stepPowWeighted p (i - i') (stepWeighted p c) q‖) (fun k _ => ?_) hi
  refine Finset.sum_nonneg fun i' _ => ?_
  positivity

omit [Fintype P] [DecidableEq P] in
theorem posPowField_smul (p : P) (j : ℕ) (a : ℂ) (ψ : (P → ℤ) → ℂ) :
    posPowField p j (fun r => a * ψ r) = fun r => a * posPowField p j ψ r := by
  funext r
  rw [posPowField, posPowField]
  ring

omit [Fintype P] [DecidableEq P] in
/-- **`(15)`, sharp form.**  The `n`-th coordinate moment of the evolution costs exactly `n` powers
of the time, measured against the moments of the initial field of order at most `n`. -/
theorem exists_sharp_moment_bound {Q : Finset (P → ℤ)} {c : (P → ℤ) → ℂ}
    (hsa : IsSelfAdjoint (latticeAdjacency Q c)) (p : P) (n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (x : ℝ) (f : (P → ℤ) → ℂ) (hf : (Function.support f).Finite) (M : ℝ),
      (∀ i ∈ Finset.range (n + 1),
        ‖(l2OfFinSupp (posPowField p i f)
            (hf.subset (support_posPowField_subset p i f)) : H)‖ ≤ M) →
      ∃ v : H, ((v : H) : (P → ℤ) → ℂ) = posPowField p n
          ((NormedSpace.exp ((-(x : ℂ) * Complex.I) • latticeAdjacency Q c)
              (l2OfFinSupp f hf) : H) : (P → ℤ) → ℂ)
        ∧ ‖v‖ ≤ C * (1 + |x|) ^ n * M := by
  induction n with
  | zero =>
    refine ⟨1, zero_le_one, fun x f hf M hM => ?_⟩
    refine ⟨NormedSpace.exp ((-(x : ℂ) * Complex.I) • latticeAdjacency Q c)
      (l2OfFinSupp f hf), ?_, ?_⟩
    · rw [posPowField_zero]
    · rw [norm_exp_latticeAdjacency_apply hsa x, pow_zero, one_mul, one_mul]
      have h0 := hM 0 (Finset.mem_range.mpr (by omega))
      rw [norm_l2OfFinSupp_congr (hf.subset (support_posPowField_subset p 0 f)) hf
        (posPowField_zero p f)] at h0
      exact h0
  | succ k ih =>
    obtain ⟨C, hC, hbound⟩ := ih
    set K : ℝ := transferConst Q c p k with hKdef
    have hK : 0 ≤ K := transferConst_nonneg Q c p k
    refine ⟨C * (1 + K), by positivity, fun x f hf M hM => ?_⟩
    have hM0 : 0 ≤ M := by
      refine le_trans (norm_nonneg _) (hM 0 (Finset.mem_range.mpr (by omega)))
    -- the two branches
    have hf₁ : (Function.support (posMulField p f)).Finite :=
      hf.subset (support_posMulField_subset p f)
    have hf₂ : (Function.support (adjacencyField Q (stepWeighted p c) f)).Finite :=
      support_adjacencyField_finite hf
    have hM₁ : ∀ i ∈ Finset.range (k + 1),
        ‖(l2OfFinSupp (posPowField p i (posMulField p f))
            (hf₁.subset (support_posPowField_subset p i _)) : H)‖ ≤ M := by
      intro i hi
      have heq : posPowField p i (posMulField p f) = posPowField p (i + 1) f :=
        (posPowField_succ' p i f).symm
      have hmem : i + 1 ∈ Finset.range (k + 1 + 1) := by
        rw [Finset.mem_range] at hi ⊢
        omega
      have := hM (i + 1) hmem
      rw [← norm_l2OfFinSupp_congr (hf₁.subset (support_posPowField_subset p i _))
        (hf.subset (support_posPowField_subset p (i + 1) f)) heq] at this
      exact this
    have hM₂ : ∀ i ∈ Finset.range (k + 1),
        ‖(l2OfFinSupp (posPowField p i (adjacencyField Q (stepWeighted p c) f))
            (hf₂.subset (support_posPowField_subset p i _)) : H)‖ ≤ K * M := by
      intro i hi
      have hsub : ∀ i' ∈ Finset.range (i + 1),
          ‖(l2OfFinSupp (posPowField p i' f)
              (hf.subset (support_posPowField_subset p i' f)) : H)‖ ≤ M := by
        intro i' hi'
        refine hM i' ?_
        rw [Finset.mem_range] at hi hi' ⊢
        omega
      have hbase := norm_posPow_adjacencyField_le Q (stepWeighted p c) p i hf M hsub
      have hle := le_transferConst Q c p k hi
      have hfin : ‖(l2OfFinSupp (posPowField p i (adjacencyField Q (stepWeighted p c) f))
          (hf₂.subset (support_posPowField_subset p i _)) : H)‖
          ≤ (∑ i' ∈ Finset.range (i + 1), ((i.choose i' : ℕ) : ℝ)
              * ∑ q ∈ Q, ‖stepPowWeighted p (i - i') (stepWeighted p c) q‖) * M := by
        exact hbase
      exact le_trans hfin (mul_le_mul_of_nonneg_right hle hM0)
    obtain ⟨v₁, hv₁, hn₁⟩ := hbound x (posMulField p f) hf₁ M hM₁
    obtain ⟨v₂, hv₂, hn₂⟩ := hbound x (adjacencyField Q (stepWeighted p c) f) hf₂ (K * M) hM₂
    refine ⟨v₁ - (-(x : ℂ) * Complex.I) • v₂, ?_, ?_⟩
    · have hψ₂ : (latticeAdjacency Q (stepWeighted p c) (l2OfFinSupp f hf) : H)
          = l2OfFinSupp (adjacencyField Q (stepWeighted p c) f) hf₂ := by
        refine lp.ext ?_
        funext ν
        rw [latticeAdjacency_apply, coe_l2OfFinSupp, coe_l2OfFinSupp]
      have hmom := coe_posMul_exp Q c p (-(x : ℂ) * Complex.I) (l2OfFinSupp f hf)
        (l2OfFinSupp (posMulField p f) hf₁) (by rw [coe_l2OfFinSupp, coe_l2OfFinSupp])
      rw [posPowField_succ', hmom, hψ₂]
      funext r
      rw [lp.coeFn_sub, Pi.sub_apply, lp.coeFn_smul, Pi.smul_apply, smul_eq_mul,
        congrFun hv₁ r, congrFun hv₂ r]
      have hsplit : ∀ s : P → ℤ, posPowField p k (fun t =>
          ((NormedSpace.exp ((-(x : ℂ) * Complex.I) • latticeAdjacency Q c)
              (l2OfFinSupp (posMulField p f) hf₁) : H) : (P → ℤ) → ℂ) t
            - (-(x : ℂ) * Complex.I)
              * ((NormedSpace.exp ((-(x : ℂ) * Complex.I) • latticeAdjacency Q c)
                  (l2OfFinSupp (adjacencyField Q (stepWeighted p c) f) hf₂) : H)
                    : (P → ℤ) → ℂ) t) s
          = posPowField p k ((NormedSpace.exp ((-(x : ℂ) * Complex.I) • latticeAdjacency Q c)
              (l2OfFinSupp (posMulField p f) hf₁) : H) : (P → ℤ) → ℂ) s
            - (-(x : ℂ) * Complex.I)
              * posPowField p k ((NormedSpace.exp
                  ((-(x : ℂ) * Complex.I) • latticeAdjacency Q c)
                  (l2OfFinSupp (adjacencyField Q (stepWeighted p c) f) hf₂) : H)
                    : (P → ℤ) → ℂ) s := by
        intro s
        rw [posPowField, posPowField, posPowField]
        ring
      rw [← hsplit r]
      congr 2
    · have hz : ‖(-(x : ℂ) * Complex.I)‖ = |x| := by
        rw [norm_mul, norm_neg, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs]
      have habs : (0 : ℝ) ≤ |x| := abs_nonneg x
      have hpow : (0 : ℝ) ≤ (1 + |x|) ^ k := by positivity
      calc ‖v₁ - (-(x : ℂ) * Complex.I) • v₂‖
          ≤ ‖v₁‖ + |x| * ‖v₂‖ := by
            refine le_trans (norm_sub_le _ _) ?_
            rw [norm_smul, hz]
        _ ≤ C * (1 + |x|) ^ k * M + |x| * (C * (1 + |x|) ^ k * (K * M)) :=
            add_le_add hn₁ (mul_le_mul_of_nonneg_left hn₂ habs)
        _ ≤ C * (1 + K) * (1 + |x|) ^ (k + 1) * M := by
            rw [pow_succ]
            nlinarith [mul_nonneg (mul_nonneg hC hpow) hM0,
              mul_nonneg (mul_nonneg (mul_nonneg hC hpow) hK) hM0,
              mul_nonneg (mul_nonneg (mul_nonneg hC hpow) habs) hM0]

end RHTower
