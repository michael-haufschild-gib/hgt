import GaloisForLFunctions.HTGeometry.IntegralFormationOrderCharge

/-!
# Physical-overlap singular-gauge non-descent

Fix primes `p < q`.  The formation cover `ℕ × Fin 4` maps onto the physical cells `{p,q} × ℕ` by
`λ(e,0) = (p,e)`, `λ(e,1) = (p,e+1)`, `λ(e,2) = (q,e)`, `λ(e,3) = (q,e+1)`, so consecutive packets
share the cells `(p,e+1)` and `(q,e+1)`.  Let `s_e` be the unique positive half-density from the
physical Plücker depth law to the theta first-exit law.

* **(A)** No function `g` on physical cells, bounded or not, satisfies `g(λ(e,i)) = s_e`: the
  overlap would force `s` to be constant, while `s` is unbounded.
* **(B)** The transitions `τ_e = s_{e+1}/s_e` are positive, reconstruct `s_n = s_0 ∏_{e<n} τ_e`,
  satisfy `τ_e = 1 + 1/e + O(e⁻²)` and `e log τ_e → 1`, and their products escape linearly:
  `(∏_{e<n} τ_e)/n → c/s_0 > 0`.
-/

open Filter Topology Set Asymptotics

noncomputable section

namespace GaloisForLFunctions.HTGeometry

open _root_.RHTower _root_.RHTower.HedenmalmThetaSource

/-! ## The formation cover -/

/-- **(POSGND.1).**  Consecutive packets overlap in the cells `(p,e+1)` and `(q,e+1)`. -/
theorem formationCover_overlap (e : ℕ) (p q : Nat.Primes) :
    gammaSewnOrderedPrimeDepthPlucker_cell e p q 1 =
        gammaSewnOrderedPrimeDepthPlucker_cell (e + 1) p q 0 ∧
      gammaSewnOrderedPrimeDepthPlucker_cell e p q 3 =
        gammaSewnOrderedPrimeDepthPlucker_cell (e + 1) p q 2 := by
  simp [gammaSewnOrderedPrimeDepthPlucker_cell]

/-- The cover lands in the physical cells `{p,q} × ℕ`. -/
theorem formationCover_mem_physicalCells (e : ℕ) (p q : Nat.Primes) (i : Fin 4) :
    (gammaSewnOrderedPrimeDepthPlucker_cell e p q i).1 = p ∨
      (gammaSewnOrderedPrimeDepthPlucker_cell e p q i).1 = q := by
  fin_cases i <;> simp [gammaSewnOrderedPrimeDepthPlucker_cell]

variable {p q : Nat.Primes} (hpq : (p : ℕ) < (q : ℕ))
include hpq

/-- **Theorem POSGND-A.**  No function on physical cells descends the half-density:
there is no `g` with `g(λ(e,i)) = s_e` for all `e, i`, whatever its growth. -/
theorem not_exists_physical_descent :
    ¬ ∃ g : Nat.Primes × ℕ → ℝ, ∀ (e : ℕ) (i : Fin 4),
      g (gammaSewnOrderedPrimeDepthPlucker_cell e p q i) = formationHalfDensity p q e := by
  rintro ⟨g, hg⟩
  have hstep : ∀ e, formationHalfDensity p q (e + 1) = formationHalfDensity p q e := fun e => by
    rw [← hg (e + 1) 0, ← (formationCover_overlap e p q).1, hg e 1]
  have hconst : ∀ e, formationHalfDensity p q e = formationHalfDensity p q 0 := by
    intro e
    induction e with
    | zero => rfl
    | succ n ih => rw [hstep n, ih]
  refine not_bddAbove_formationHalfDensity hpq ⟨formationHalfDensity p q 0, ?_⟩
  rintro _ ⟨e, rfl⟩
  exact (hconst e).le

omit hpq in
/-- **(POSGND.3).**  The formation connection `τ_e = s_{e+1}/s_e`. -/
def formationConnection (p q : Nat.Primes) (e : ℕ) : ℝ :=
  formationHalfDensity p q (e + 1) / formationHalfDensity p q e

theorem formationConnection_pos (e : ℕ) : 0 < formationConnection p q e :=
  div_pos (formationHalfDensity_pos hpq _) (formationHalfDensity_pos hpq _)

/-- **(POSGND.4).**  `s_n = s_0 ∏_{e<n} τ_e`. -/
theorem formationHalfDensity_eq_mul_prod (n : ℕ) :
    formationHalfDensity p q n =
      formationHalfDensity p q 0 * ∏ e ∈ Finset.range n, formationConnection p q e := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.prod_range_succ, ← mul_assoc, ← ih, formationConnection,
      mul_div_cancel₀ _ (formationHalfDensity_pos hpq n).ne']

/-- **(POSGND.5).**  `τ_e = 1 + 1/e + O(e⁻²)`. -/
theorem isBigO_formationConnection :
    (fun e : ℕ => formationConnection p q e - (1 + 1 / (e : ℝ))) =O[atTop]
      (fun e : ℕ => ((e : ℝ) ^ 2)⁻¹) :=
  isBigO_formationHalfDensity_ratio hpq

/-- **(POSGND.5).**  `e log τ_e → 1`. -/
theorem tendsto_mul_log_formationConnection :
    Tendsto (fun e : ℕ => (e : ℝ) * Real.log (formationConnection p q e)) atTop (𝓝 1) := by
  have h := (hasFormationResidue_formationHalfDensity hpq).1
  rw [(hasFormationResidue_formationHalfDensity hpq).2] at h
  exact h

/-- **(POSGND.6).**  The trivializing products escape linearly:
`(∏_{e<n} τ_e)/n → c/s_0 > 0`. -/
theorem tendsto_prod_formationConnection_div :
    Tendsto (fun n : ℕ => (∏ e ∈ Finset.range n, formationConnection p q e) / n) atTop
      (𝓝 (formationOrderSlope p q / formationHalfDensity p q 0)) := by
  refine ((tendsto_formationHalfDensity_div hpq).div_const (formationHalfDensity p q 0)).congr
    fun n => ?_
  have h0 := (formationHalfDensity_pos hpq 0).ne'
  rw [formationHalfDensity_eq_mul_prod hpq n]
  field_simp

/-- The trivializing products are unbounded: no bounded physical descent class contains them. -/
theorem not_bddAbove_prod_formationConnection :
    ¬ BddAbove (range fun n : ℕ => ∏ e ∈ Finset.range n, formationConnection p q e) := by
  rintro ⟨C, hC⟩
  refine not_bddAbove_formationHalfDensity hpq ⟨formationHalfDensity p q 0 * C, ?_⟩
  rintro _ ⟨n, rfl⟩
  rw [formationHalfDensity_eq_mul_prod hpq n]
  exact mul_le_mul_of_nonneg_left (hC ⟨n, rfl⟩) (formationHalfDensity_pos hpq 0).le

/-- **Theorem POSGND.**  For primes `p < q`: no function on physical cells descends the
half-density (A); the formation connection `τ_e = s_{e+1}/s_e` is positive, reconstructs `s`,
has `τ_e = 1 + 1/e + O(e⁻²)` and `e log τ_e → 1`, and its trivializing products escape linearly
and unboundedly (B). -/
theorem physical_overlap_singular_gauge_nondescent :
    (¬ ∃ g : Nat.Primes × ℕ → ℝ, ∀ (e : ℕ) (i : Fin 4),
      g (gammaSewnOrderedPrimeDepthPlucker_cell e p q i) = formationHalfDensity p q e) ∧
    (∀ e, 0 < formationConnection p q e) ∧
    (∀ n, formationHalfDensity p q n =
      formationHalfDensity p q 0 * ∏ e ∈ Finset.range n, formationConnection p q e) ∧
    (fun e : ℕ => formationConnection p q e - (1 + 1 / (e : ℝ))) =O[atTop]
      (fun e : ℕ => ((e : ℝ) ^ 2)⁻¹) ∧
    Tendsto (fun e : ℕ => (e : ℝ) * Real.log (formationConnection p q e)) atTop (𝓝 1) ∧
    0 < formationOrderSlope p q / formationHalfDensity p q 0 ∧
    Tendsto (fun n : ℕ => (∏ e ∈ Finset.range n, formationConnection p q e) / n) atTop
      (𝓝 (formationOrderSlope p q / formationHalfDensity p q 0)) ∧
    ¬ BddAbove (range fun n : ℕ => ∏ e ∈ Finset.range n, formationConnection p q e) :=
  ⟨not_exists_physical_descent hpq, formationConnection_pos hpq,
    formationHalfDensity_eq_mul_prod hpq, isBigO_formationConnection hpq,
    tendsto_mul_log_formationConnection hpq,
    div_pos (formationOrderSlope_pos hpq) (formationHalfDensity_pos hpq 0),
    tendsto_prod_formationConnection_div hpq, not_bddAbove_prod_formationConnection hpq⟩

end GaloisForLFunctions.HTGeometry
