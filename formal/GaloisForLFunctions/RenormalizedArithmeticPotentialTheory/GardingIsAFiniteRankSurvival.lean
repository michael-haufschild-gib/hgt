import GaloisForLFunctions.RenormalizedArithmeticPotentialTheory.TheCoupledSurvivalLaw

/-!
# Gårding is a finite-rank survival

Weil's form has finitely many negative directions at every aperture (APol, ACS): a Gårding
inequality. In the language of renormalization this is survival with a finite-rank counterterm.

For a real form `A` on `ι → ℝ` and `k ∈ ℕ`:

* **Gårding gives a counterterm** (`survival_of_functionals`): if `A ≥ 0` on the common kernel of `k`
  linear functionals `x ↦ ℓ_i · x`, then `B = Σ_i ℓ_i ℓ_iᵀ` is a positive symmetric counterterm of rank
  `≤ k` whose survival cone is that common kernel.
* **A counterterm gives Gårding** (`functionals_of_survival`): if `A ≥ 0` on the survival cone of a
  positive symmetric `B` of rank `≤ k`, then `A ≥ 0` on the common kernel of `k` functionals spanning
  the range of `B`.
* **The equivalence** (`garding_iff_survival`, `garding_iff_regularized`): `A` is nonnegative on a
  subspace of codimension `≤ k` iff it is nonnegative on the survival cone of a rank-`≤ k` positive
  counterterm, iff `A + sB + εI` is eventually positive definite for every `ε > 0` (RBG
  `quad_nonneg_on_survivalCone_iff`): `A` is the renormalized limit of positive definite forms with a
  counterterm of rank `≤ k`.
* **Negative index** (`finrank_le_of_garding`): then every subspace on which `A` is negative definite
  has dimension at most `k`.

So the Gårding inequalities of the corpus are the finite-rank instances of the survival law: a form
with `k` negative directions is a renormalized positive form whose counterterm has rank `k`, and RH,
`W ≥ 0`, is the statement that the counterterm of Weil's form can be taken to be zero.
-/

noncomputable section

open Finset Matrix

namespace GaloisForLFunctions.RenormalizedArithmeticPotentialTheory

open RenormalizedBiarithmeticGeometry

variable {ι : Type*} [Fintype ι]

/-- `A ≥ 0` on the common kernel of the functionals `x ↦ ℓ_i · x`. -/
def NonnegOnKernel {k : ℕ} (A : Matrix ι ι ℝ) (ℓ : Fin k → ι → ℝ) : Prop :=
  ∀ x : ι → ℝ, (∀ i, ℓ i ⬝ᵥ x = 0) → 0 ≤ quad A x

/-- The counterterm `Σ_i ℓ_i ℓ_iᵀ` of a family of functionals. -/
def functionalCounterterm {k : ℕ} (ℓ : Fin k → ι → ℝ) : Matrix ι ι ℝ :=
  ∑ i, vecMulVec (ℓ i) (ℓ i)

theorem quad_functionalCounterterm {k : ℕ} (ℓ : Fin k → ι → ℝ) (x : ι → ℝ) :
    quad (functionalCounterterm ℓ) x = ∑ i, (ℓ i ⬝ᵥ x) ^ 2 := by
  have h : ∀ (B C : Matrix ι ι ℝ), quad (B + C) x = quad B x + quad C x := fun B C =>
    quad_add B C x
  unfold functionalCounterterm
  induction (univ : Finset (Fin k)) using Finset.induction_on with
  | empty => simp [quad]
  | insert a s ha ih =>
    rw [sum_insert ha, sum_insert ha, h, ih, quad_vecMulVec_self]
    simp [dotProduct]

omit [Fintype ι] in
theorem functionalCounterterm_isSymm {k : ℕ} (ℓ : Fin k → ι → ℝ) :
    (functionalCounterterm ℓ).IsSymm := by
  unfold functionalCounterterm Matrix.IsSymm
  rw [transpose_sum]
  exact sum_congr rfl fun i _ => transpose_vecMulVec _ _

/-- `(Σ ℓ_i ℓ_iᵀ) x = Σ (ℓ_i · x) ℓ_i`. -/
theorem functionalCounterterm_mulVec {k : ℕ} (ℓ : Fin k → ι → ℝ) (x : ι → ℝ) :
    functionalCounterterm ℓ *ᵥ x = ∑ i, (ℓ i ⬝ᵥ x) • ℓ i := by
  unfold functionalCounterterm
  rw [sum_mulVec]
  exact sum_congr rfl fun i _ => vecMulVec_mulVec' _ _ _

theorem rank_functionalCounterterm_le {k : ℕ} (ℓ : Fin k → ι → ℝ) :
    (functionalCounterterm ℓ).rank ≤ k := by
  -- the range lies in the span of the `ℓ_i`
  have hsub : LinearMap.range (functionalCounterterm ℓ).mulVecLin ≤
      Submodule.span ℝ (Set.range ℓ) := by
    rintro _ ⟨x, rfl⟩
    rw [mulVecLin_apply, functionalCounterterm_mulVec]
    exact Submodule.sum_mem _ fun i _ =>
      Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  calc (functionalCounterterm ℓ).rank
      ≤ Module.finrank ℝ (Submodule.span ℝ (Set.range ℓ)) := Submodule.finrank_mono hsub
    _ ≤ Fintype.card (Fin k) := finrank_range_le_card ℓ
    _ = k := Fintype.card_fin k

/-- **Gårding gives a counterterm**: the survival cone of `Σ ℓ_i ℓ_iᵀ` is the common kernel. -/
theorem survival_of_functionals {k : ℕ} {A : Matrix ι ι ℝ} {ℓ : Fin k → ι → ℝ}
    (hA : NonnegOnKernel A ℓ) :
    (functionalCounterterm ℓ).IsSymm ∧ (∀ x, 0 ≤ quad (functionalCounterterm ℓ) x) ∧
      (functionalCounterterm ℓ).rank ≤ k ∧
      ∀ x ∈ survivalCone (functionalCounterterm ℓ), 0 ≤ quad A x := by
  refine ⟨functionalCounterterm_isSymm ℓ, fun x => ?_, rank_functionalCounterterm_le ℓ,
    fun x hx => hA x fun i => ?_⟩
  · rw [quad_functionalCounterterm]; positivity
  · have h0 : ∑ j, (ℓ j ⬝ᵥ x) ^ 2 = 0 := by
      rw [← quad_functionalCounterterm]; exact hx
    have := (sum_eq_zero_iff_of_nonneg fun j _ => sq_nonneg (ℓ j ⬝ᵥ x)).mp h0 i (mem_univ i)
    exact pow_eq_zero_iff (n := 2) (by norm_num) |>.mp this

/-- **A counterterm gives Gårding**: if `A ≥ 0` on the survival cone of a positive symmetric `B` of
rank `≤ k`, then `A ≥ 0` on the common kernel of `k` functionals spanning the range of `B`. -/
theorem functionals_of_survival {k : ℕ} {A B : Matrix ι ι ℝ} (hBs : B.IsSymm)
    (hB : ∀ x, 0 ≤ quad B x) (hrank : B.rank ≤ k)
    (hA : ∀ x ∈ survivalCone B, 0 ≤ quad A x) :
    ∃ ℓ : Fin k → ι → ℝ, NonnegOnKernel A ℓ := by
  classical
  set R := LinearMap.range B.mulVecLin
  set b := Module.finBasis ℝ R
  have hdim : Module.finrank ℝ R ≤ k := hrank
  -- the basis of the range, padded by zeros to `k` vectors
  set ℓ : Fin k → ι → ℝ := fun i =>
    if h : (i : ℕ) < Module.finrank ℝ R then (b ⟨i, h⟩ : ι → ℝ) else 0
  refine ⟨ℓ, fun x hx => hA x ?_⟩
  rw [mem_survivalCone_iff_mulVec_eq_zero hBs hB]
  -- `x` is orthogonal to the range of `B`, hence `B x = 0`
  have horth : ∀ r ∈ R, r ⬝ᵥ x = 0 := by
    intro r hr
    have hsum := congrArg Subtype.val (b.sum_repr ⟨r, hr⟩)
    simp only [Submodule.coe_sum, Submodule.coe_smul] at hsum
    rw [← hsum, sum_dotProduct]
    refine sum_eq_zero fun i _ => ?_
    rw [smul_dotProduct]
    have hi := hx ⟨i, i.2.trans_le hdim⟩
    simp only [ℓ, i.2, dif_pos] at hi
    rw [hi, smul_zero]
  have hBx : B *ᵥ x ⬝ᵥ (B *ᵥ x) = 0 := by
    have h1 := horth (B *ᵥ (B *ᵥ x)) ⟨B *ᵥ x, rfl⟩
    -- `(B (Bx)) · x = (Bx) · (Bᵀ x) = (Bx) · (Bx)`
    rw [dotProduct_comm, dotProduct_mulVec, ← mulVec_transpose, hBs] at h1
    rw [dotProduct_comm] at h1
    exact h1
  exact dotProduct_self_eq_zero.mp hBx

/-- **Gårding is a finite-rank survival.** `A` is nonnegative on the common kernel of `k` functionals
iff it is nonnegative on the survival cone of a positive symmetric counterterm of rank `≤ k`. -/
theorem garding_iff_survival {k : ℕ} (A : Matrix ι ι ℝ) :
    (∃ ℓ : Fin k → ι → ℝ, NonnegOnKernel A ℓ) ↔
      ∃ B : Matrix ι ι ℝ, B.IsSymm ∧ (∀ x, 0 ≤ quad B x) ∧ B.rank ≤ k ∧
        ∀ x ∈ survivalCone B, 0 ≤ quad A x := by
  constructor
  · rintro ⟨ℓ, hℓ⟩
    exact ⟨functionalCounterterm ℓ, survival_of_functionals hℓ⟩
  · rintro ⟨B, hBs, hB, hrank, hA⟩
    exact functionals_of_survival hBs hB hrank hA

/-- **Gårding as a renormalized limit.** `A` is nonnegative on a subspace of codimension `≤ k` iff for a
positive symmetric `B` of rank `≤ k`, `A + sB + εI` is eventually positive semidefinite for every
`ε > 0`: `A` is the renormalized limit of positive forms with a counterterm of rank `≤ k`. -/
theorem garding_iff_regularized [DecidableEq ι] {k : ℕ} (A : Matrix ι ι ℝ) :
    (∃ ℓ : Fin k → ι → ℝ, NonnegOnKernel A ℓ) ↔
      ∃ B : Matrix ι ι ℝ, B.IsSymm ∧ (∀ x, 0 ≤ quad B x) ∧ B.rank ≤ k ∧
        ∀ ε : ℝ, 0 < ε → ∃ s₀ : ℝ, ∀ s, s₀ ≤ s → ∀ x,
          0 ≤ quad A x + s * quad B x + ε * ∑ i, x i ^ 2 := by
  rw [garding_iff_survival]
  constructor
  · rintro ⟨B, hBs, hB, hrank, hA⟩
    refine ⟨B, hBs, hB, hrank, ?_⟩
    have h := (quad_nonneg_on_survivalCone_iff A B hB).mp hA
    simpa using h
  · rintro ⟨B, hBs, hB, hrank, hreg⟩
    refine ⟨B, hBs, hB, hrank, (quad_nonneg_on_survivalCone_iff A B hB).mpr ?_⟩
    simpa using hreg

/-- **Negative index.** If `A ≥ 0` on the common kernel of `k` functionals, every subspace on which `A`
is negative definite has dimension at most `k`. -/
theorem finrank_le_of_garding {k : ℕ} {A : Matrix ι ι ℝ} {ℓ : Fin k → ι → ℝ}
    (hA : NonnegOnKernel A ℓ) (W : Submodule ℝ (ι → ℝ))
    (hW : ∀ x ∈ W, x ≠ 0 → quad A x < 0) : Module.finrank ℝ W ≤ k := by
  -- the functionals are injective on `W`
  let F : W →ₗ[ℝ] (Fin k → ℝ) :=
    { toFun := fun x i => ℓ i ⬝ᵥ (x : ι → ℝ)
      map_add' := fun x y => by funext i; simp [dotProduct_add]
      map_smul' := fun c x => by funext i; simp [dotProduct_smul] }
  have hinj : Function.Injective F := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro x hx
    by_contra hne
    have hx0 : (x : ι → ℝ) ≠ 0 := fun h => hne (Subtype.ext h)
    have hker : ∀ i, ℓ i ⬝ᵥ (x : ι → ℝ) = 0 := fun i => congrFun hx i
    exact absurd (hA x hker) (not_le.mpr (hW x x.2 hx0))
  have h := LinearMap.finrank_le_finrank_of_injective hinj
  simpa using h

end GaloisForLFunctions.RenormalizedArithmeticPotentialTheory
