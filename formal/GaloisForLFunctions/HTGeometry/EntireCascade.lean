import GaloisForLFunctions.HTGeometry.CascadeSeparationCriterion

/-!
# The cascade of entire compositions

The states of a composition cascade: `F_0 = id` and `F_{k+1} = f_k ∘ F_k`.  Each state is entire when
every constituent is, and the last state of a truncation is the composition of the previous one with
the next constituent — which is the shape every step of the separation argument uses.
-/

open Set

namespace GaloisForLFunctions.HTGeometry

/-- The cascade of compositions `F_0 = id`, `F_{k+1} = f_k ∘ F_k`. -/
def entireCascade (f : ℕ → ℂ → ℂ) : ℕ → ℂ → ℂ
  | 0 => id
  | (n + 1) => fun z => f n (entireCascade f n z)

@[simp] theorem entireCascade_zero (f : ℕ → ℂ → ℂ) : entireCascade f 0 = id := rfl

@[simp] theorem entireCascade_succ (f : ℕ → ℂ → ℂ) (n : ℕ) (z : ℂ) :
    entireCascade f (n + 1) z = f n (entireCascade f n z) := rfl

/-- **Every state is entire.** -/
theorem analyticOnNhd_entireCascade {f : ℕ → ℂ → ℂ}
    (hf : ∀ i : ℕ, AnalyticOnNhd ℂ (f i) Set.univ) (n : ℕ) :
    AnalyticOnNhd ℂ (entireCascade f n) Set.univ := by
  induction n with
  | zero =>
      intro z _
      exact analyticAt_id
  | succ n ih =>
      intro z _
      exact (hf n _ (Set.mem_univ _)).comp (ih z (Set.mem_univ z))

/-- The cascade states indexed by `Fin n`, with `F_i = f_{i} ∘ ⋯ ∘ f_0`. -/
def cascadeFamily (f : ℕ → ℂ → ℂ) (n : ℕ) : Fin n → ℂ → ℂ :=
  fun i => entireCascade f (i.1 + 1)

@[simp] theorem cascadeFamily_apply (f : ℕ → ℂ → ℂ) (n : ℕ) (i : Fin n) (z : ℂ) :
    cascadeFamily f n i z = entireCascade f (i.1 + 1) z := rfl

/-- **Every member of the family is entire.** -/
theorem analyticOnNhd_cascadeFamily {f : ℕ → ℂ → ℂ}
    (hf : ∀ i : ℕ, AnalyticOnNhd ℂ (f i) Set.univ) (n : ℕ) (i : Fin n) :
    AnalyticOnNhd ℂ (cascadeFamily f n i) Set.univ :=
  analyticOnNhd_entireCascade hf _

/-- **The last state of a truncation is a composition.**  Under `Fin.castLE`, the last index of
`Fin (m+1)` names the state `F_{m+1}`, which is `f_m` applied to the previous state. -/
theorem cascadeFamily_castLE_last {f : ℕ → ℂ → ℂ} {n m : ℕ} (hm : m + 1 ≤ n) (z : ℂ) :
    cascadeFamily f n (Fin.castLE hm (Fin.last m)) z
      = f m (entireCascade f m z) := by
  simp [cascadeFamily, Fin.castLE]

/-- The earlier states of a truncation are the earlier cascade states. -/
theorem cascadeFamily_castLE {f : ℕ → ℂ → ℂ} {n m : ℕ} (hm : m + 1 ≤ n) (i : Fin (m + 1))
    (z : ℂ) :
    cascadeFamily f n (Fin.castLE hm i) z = entireCascade f (i.1 + 1) z := by
  simp [cascadeFamily, Fin.castLE]

/-! ## The criterion for the cascade

The separation criterion with the cascade's states substituted, so the composition `f_m ∘ F_m` is
visible in the growth hypothesis rather than hidden behind the truncation map. -/

/-- **Cascade independence with the composition explicit.** -/
theorem polyIndependent_cascadeFamily {f : ℕ → ℂ → ℂ} {n : ℕ}
    (h : ∀ (m : ℕ), m + 1 ≤ n →
      ∀ (S : Finset (Fin (m + 1) → ℕ)) (A : (Fin (m + 1) → ℕ) → Polynomial ℂ) (N : ℕ),
        1 ≤ N → (∀ e ∈ S, e (Fin.last m) ≤ N) →
        (∃ w : ℂ, groupedCoeff S (fun e => (A e).eval w)
          (fun i => entireCascade f (i.1 + 1) w) N ≠ 0) →
        ∃ (z : ℂ) (α β D H L R R₁ Bd Gc B C sh : ℝ) (q : ℕ),
          0 < H ∧ H ≤ 1 ∧ 0 < H ^ q * L ∧ 0 < C ∧
          2 * sh ≤ Real.exp B * C ∧
          H ^ q * L ≤ ‖groupedCoeff S (fun e => (A e).eval z)
            (fun i => entireCascade f (i.1 + 1) z) N‖ ∧
          (∑ e ∈ S, (Real.posLog ‖(A e).eval z‖
            + ∑ i ∈ Finset.univ.erase (Fin.last m), (e i : ℝ)
                * Real.posLog ‖entireCascade f (i.1 + 1) z‖))
            ≤ (S.card : ℝ) * (α + D * β) ∧
          Real.exp B * C - sh ≤ ‖f m (entireCascade f m z)‖ ∧
          (q : ℝ) ≤ (Bd - Gc) / Real.log (R / R₁) ∧
          (S.card : ℝ) * (α + D * β)
              + (N : ℝ) * (((Bd - Gc) / Real.log (R / R₁)) * Real.log (1 / H)
                  + Real.posLog (1 / L))
              + ((N : ℝ) * (S.card : ℝ) + (N : ℝ)) * Real.log 2
            < B + Real.log C - Real.log 2) :
    PolyIndependent (cascadeFamily f n) := by
  refine polyIndependent_of_growth_exponent _ ?_
  intro m hm S A N hN1 hN hex
  simp only [cascadeFamily_castLE] at hex ⊢
  exact h m hm S A N hN1 hN hex

/-! ## The chain rule along the cascade

The derivative of a state is the derivative of the new constituent at the previous state, times the
previous state's derivative.  Iterating this is what expresses every derivative of the last state in
terms of the states and the constituents' derivatives — the step that turns a differential relation
for `F_n` into a polynomial relation among the states. -/

/-- **The chain rule for the cascade.** -/
theorem deriv_entireCascade_succ {f : ℕ → ℂ → ℂ}
    (hf : ∀ i : ℕ, AnalyticOnNhd ℂ (f i) Set.univ) (n : ℕ) (z : ℂ) :
    deriv (entireCascade f (n + 1)) z
      = deriv (f n) (entireCascade f n z) * deriv (entireCascade f n) z := by
  have hinner : HasDerivAt (entireCascade f n) (deriv (entireCascade f n) z) z :=
    ((analyticOnNhd_entireCascade hf n) z (Set.mem_univ z)).differentiableAt.hasDerivAt
  have houter : HasDerivAt (f n) (deriv (f n) (entireCascade f n z)) (entireCascade f n z) :=
    ((hf n) _ (Set.mem_univ _)).differentiableAt.hasDerivAt
  have hcomp : HasDerivAt (fun w => f n (entireCascade f n w))
      (deriv (f n) (entireCascade f n z) * deriv (entireCascade f n) z) z :=
    houter.comp z hinner
  exact hcomp.deriv

/-- The states are differentiable everywhere. -/
theorem differentiable_entireCascade {f : ℕ → ℂ → ℂ}
    (hf : ∀ i : ℕ, AnalyticOnNhd ℂ (f i) Set.univ) (n : ℕ) :
    Differentiable ℂ (entireCascade f n) :=
  fun z => ((analyticOnNhd_entireCascade hf n) z (Set.mem_univ z)).differentiableAt

end GaloisForLFunctions.HTGeometry
