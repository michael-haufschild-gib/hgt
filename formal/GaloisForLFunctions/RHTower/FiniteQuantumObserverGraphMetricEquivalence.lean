import GaloisForLFunctions.RHTower.FiniteQuantumObserverGraphRecurrenceBound

/-!
# Global metric equivalence for finite quantum observers

The coherence graph of a finite matrix-observer family has one canonical
projective coordinate for every nonroot vertex.  This file proves that the
observer's exact Hilbert--Schmidt phase energy is globally and uniformly
multiplicatively equivalent to the sum of squared chords from those vertices
to their component roots.

The constants depend only on the finite observer weights and graph.  They do
not depend on the phase packet.  This uniformity is the geometric input needed
to transfer exact first-return exponents from a canonical relative-phase clock
to every observer with the same coherence graph.
-/

open scoped BigOperators
open SimpleGraph

namespace RHTower

noncomputable section

/-- Sum of squared phase chords from every nonroot vertex to the selected
root of its coherence component. -/
def graphRootChordEnergy {V : Type*} [Fintype V]
    (G : SimpleGraph V) (z : V → ℂ) : ℝ :=
  ∑ v : graphNonRoot G,
    ‖z v.1 - z (graphComponentRoot G (G.connectedComponentMk v.1))‖ ^ (2 : ℕ)

theorem norm_mul_star_sub_one_eq_norm_sub
    (x y : ℂ) (hy : ‖y‖ = 1) :
    ‖x * star y - 1‖ = ‖x - y‖ := by
  have hyunit : y * star y = 1 := by
    change y * (starRingEnd ℂ) y = 1
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hy]
    norm_num
  have hid : x * star y - 1 = (x - y) * star y := by
    rw [sub_mul, hyunit]
  rw [hid, norm_mul, norm_star, hy, mul_one]

theorem finiteQuantumObserverPhaseEnergy_nonneg
    {d : ℕ} {J : Type*} [Fintype J]
    (lam : J → ℝ) (z : Fin d → ℂ)
    (block : J → Fin d → Fin d → ℂ)
    (hlam : ∀ a, 0 ≤ lam a) :
    0 ≤ finiteQuantumObserverPhaseEnergy lam z block := by
  rw [finiteQuantumObserverPhaseEnergy]
  exact Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ =>
    mul_nonneg (finiteObserverUnionWeight_nonneg lam block hlam i j) (sq_nonneg _)

theorem vertexRootChordSq_le_graphRootChordEnergy
    {V : Type*} [Fintype V] (G : SimpleGraph V) (z : V → ℂ) (v : V) :
    ‖z v - z (graphComponentRoot G (G.connectedComponentMk v))‖ ^ (2 : ℕ) ≤
      graphRootChordEnergy G z := by
  classical
  by_cases hv : IsGraphComponentRoot G v
  · have hzero : z v - z (graphComponentRoot G (G.connectedComponentMk v)) = 0 := by
      rw [hv]
      simp
    simp only [hzero, norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
      zero_pow]
    exact Finset.sum_nonneg fun u _ => sq_nonneg _
  · rw [graphRootChordEnergy]
    exact Finset.single_le_sum
      (f := fun u : graphNonRoot G =>
        ‖z u.1 - z (graphComponentRoot G
          (G.connectedComponentMk u.1))‖ ^ (2 : ℕ))
      (fun u _ => sq_nonneg _) (Finset.mem_univ ⟨v, hv⟩)

theorem graphRootChordEnergy_nonneg
    {V : Type*} [Fintype V] (G : SimpleGraph V) (z : V → ℂ) :
    0 ≤ graphRootChordEnergy G z := by
  classical
  rw [graphRootChordEnergy]
  exact Finset.sum_nonneg fun v _ => sq_nonneg _

/-- The complete observer phase energy is bounded above by four times its
total weight times canonical root-chord energy. -/
theorem observerPhaseEnergy_le_rootChordEnergy
    {d : ℕ} {J : Type*} [Fintype J]
    (lam : J → ℝ) (z : Fin d → ℂ)
    (block : J → Fin d → Fin d → ℂ)
    (hlam : ∀ a, 0 ≤ lam a) (hunit : ∀ i, ‖z i‖ = 1) :
    finiteQuantumObserverPhaseEnergy lam z block ≤
      (4 * (∑ i, ∑ j, finiteObserverUnionWeight lam block i j)) *
        graphRootChordEnergy (finiteObserverCoherenceGraph lam block) z := by
  classical
  let G := finiteObserverCoherenceGraph lam block
  let W : ℝ := ∑ i, ∑ j, finiteObserverUnionWeight lam block i j
  rw [finiteQuantumObserverPhaseEnergy]
  calc
    (∑ i, ∑ j, finiteObserverUnionWeight lam block i j *
        ‖finiteQuantumObserverPhase z i j - 1‖ ^ (2 : ℕ)) ≤
        ∑ i, ∑ j, finiteObserverUnionWeight lam block i j *
          (4 * graphRootChordEnergy G z) := by
      apply Finset.sum_le_sum
      intro i _hi
      apply Finset.sum_le_sum
      intro j _hj
      by_cases hij : i = j
      · subst j
        have hphase : finiteQuantumObserverPhase z i i = 1 := by
          rw [finiteQuantumObserverPhase]
          change z i * (starRingEnd ℂ) (z i) = 1
          rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hunit]
          norm_num
        rw [hphase, sub_self, norm_zero, zero_pow (by norm_num), mul_zero]
        exact mul_nonneg
          (finiteObserverUnionWeight_nonneg lam block hlam i i)
          (mul_nonneg (by norm_num) (graphRootChordEnergy_nonneg G z))
      by_cases hw : finiteObserverUnionWeight lam block i j = 0
      · simp [hw]
      · have hwpos : 0 < finiteObserverUnionWeight lam block i j :=
          lt_of_le_of_ne (finiteObserverUnionWeight_nonneg lam block hlam i j)
            (Ne.symm hw)
        apply mul_le_mul_of_nonneg_left _
          (finiteObserverUnionWeight_nonneg lam block hlam i j)
        rw [finiteQuantumObserverPhase,
          norm_mul_star_sub_one_eq_norm_sub _ _ (hunit j)]
        have hadj : G.Adj i j := ⟨hij, Or.inl hwpos⟩
        have hc : G.connectedComponentMk i = G.connectedComponentMk j :=
          ConnectedComponent.connectedComponentMk_eq_of_adj hadj
        let r := graphComponentRoot G (G.connectedComponentMk i)
        have hrj : graphComponentRoot G (G.connectedComponentMk j) = r := by
          simpa only [r] using congrArg (graphComponentRoot G) hc.symm
        have htri : ‖z i - z j‖ ≤ ‖z i - z r‖ + ‖z j - z r‖ := by
          calc
            ‖z i - z j‖ = ‖(z i - z r) - (z j - z r)‖ := by
              congr 1
              ring
            _ ≤ _ := norm_sub_le _ _
        have hi := vertexRootChordSq_le_graphRootChordEnergy G z i
        have hj := vertexRootChordSq_le_graphRootChordEnergy G z j
        change ‖z i - z r‖ ^ (2 : ℕ) ≤ graphRootChordEnergy G z at hi
        rw [hrj] at hj
        have htriSq : ‖z i - z j‖ ^ (2 : ℕ) ≤
            (‖z i - z r‖ + ‖z j - z r‖) ^ (2 : ℕ) :=
          (sq_le_sq₀ (norm_nonneg _)
            (add_nonneg (norm_nonneg _) (norm_nonneg _))).2 htri
        nlinarith [htriSq, sq_nonneg (‖z i - z r‖ - ‖z j - z r‖)]
    _ = (4 * W) * graphRootChordEnergy G z := by
      simp only [W, Finset.mul_sum, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i _hi
      apply Finset.sum_congr rfl
      intro j _hj
      ring
    _ = _ := rfl

theorem edgeChordSq_le_observerPhaseEnergy_mul
    {d : ℕ} {J : Type*} [Fintype J]
    (lam : J → ℝ) (block : J → Fin d → Fin d → ℂ)
    (hlam : ∀ a, 0 ≤ lam a)
    {i j : Fin d}
    (hij : (finiteObserverCoherenceGraph lam block).Adj i j) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (z : Fin d → ℂ), (∀ i, ‖z i‖ = 1) →
        ‖z i - z j‖ ^ (2 : ℕ) ≤
          C * finiteQuantumObserverPhaseEnergy lam z block := by
  classical
  rcases hij.2 with hpos | hpos
  · let w := finiteObserverUnionWeight lam block i j
    refine ⟨1 / w, by dsimp [w]; positivity, ?_⟩
    intro z hunit
    have hterm :
        w * ‖z i - z j‖ ^ (2 : ℕ) ≤
          finiteQuantumObserverPhaseEnergy lam z block := by
      rw [finiteQuantumObserverPhaseEnergy]
      have hj :
          finiteObserverUnionWeight lam block i j *
              ‖finiteQuantumObserverPhase z i j - 1‖ ^ (2 : ℕ) ≤
            ∑ k, finiteObserverUnionWeight lam block i k *
              ‖finiteQuantumObserverPhase z i k - 1‖ ^ (2 : ℕ) :=
        Finset.single_le_sum
          (f := fun k : Fin d => finiteObserverUnionWeight lam block i k *
            ‖finiteQuantumObserverPhase z i k - 1‖ ^ (2 : ℕ))
          (fun k _ => mul_nonneg
            (finiteObserverUnionWeight_nonneg lam block hlam i k)
            (sq_nonneg _)) (Finset.mem_univ j)
      have hi :
          (∑ k, finiteObserverUnionWeight lam block i k *
              ‖finiteQuantumObserverPhase z i k - 1‖ ^ (2 : ℕ)) ≤
            ∑ u, ∑ k, finiteObserverUnionWeight lam block u k *
              ‖finiteQuantumObserverPhase z u k - 1‖ ^ (2 : ℕ) :=
        Finset.single_le_sum
          (f := fun u : Fin d =>
            ∑ k, finiteObserverUnionWeight lam block u k *
              ‖finiteQuantumObserverPhase z u k - 1‖ ^ (2 : ℕ))
          (fun u _ => Finset.sum_nonneg fun k _ => mul_nonneg
            (finiteObserverUnionWeight_nonneg lam block hlam u k)
            (sq_nonneg _)) (Finset.mem_univ i)
      rw [finiteQuantumObserverPhase,
        norm_mul_star_sub_one_eq_norm_sub _ _ (hunit j)] at hj
      exact hj.trans hi
    rw [one_div, inv_mul_eq_div]
    apply (le_div_iff₀ (by simpa only [w] using hpos)).2
    simpa only [mul_comm] using hterm
  · let w := finiteObserverUnionWeight lam block j i
    refine ⟨1 / w, by dsimp [w]; positivity, ?_⟩
    intro z hunit
    have hterm :
        w * ‖z j - z i‖ ^ (2 : ℕ) ≤
          finiteQuantumObserverPhaseEnergy lam z block := by
      rw [finiteQuantumObserverPhaseEnergy]
      have hi :
          finiteObserverUnionWeight lam block j i *
              ‖finiteQuantumObserverPhase z j i - 1‖ ^ (2 : ℕ) ≤
            ∑ k, finiteObserverUnionWeight lam block j k *
              ‖finiteQuantumObserverPhase z j k - 1‖ ^ (2 : ℕ) :=
        Finset.single_le_sum
          (f := fun k : Fin d => finiteObserverUnionWeight lam block j k *
            ‖finiteQuantumObserverPhase z j k - 1‖ ^ (2 : ℕ))
          (fun k _ => mul_nonneg
            (finiteObserverUnionWeight_nonneg lam block hlam j k)
            (sq_nonneg _)) (Finset.mem_univ i)
      have hj :
          (∑ k, finiteObserverUnionWeight lam block j k *
              ‖finiteQuantumObserverPhase z j k - 1‖ ^ (2 : ℕ)) ≤
            ∑ u, ∑ k, finiteObserverUnionWeight lam block u k *
              ‖finiteQuantumObserverPhase z u k - 1‖ ^ (2 : ℕ) :=
        Finset.single_le_sum
          (f := fun u : Fin d =>
            ∑ k, finiteObserverUnionWeight lam block u k *
              ‖finiteQuantumObserverPhase z u k - 1‖ ^ (2 : ℕ))
          (fun u _ => Finset.sum_nonneg fun k _ => mul_nonneg
            (finiteObserverUnionWeight_nonneg lam block hlam u k)
            (sq_nonneg _)) (Finset.mem_univ j)
      rw [finiteQuantumObserverPhase,
        norm_mul_star_sub_one_eq_norm_sub _ _ (hunit i)] at hi
      exact hi.trans hj
    rw [norm_sub_rev, one_div, inv_mul_eq_div]
    apply (le_div_iff₀ (by simpa only [w] using hpos)).2
    simpa only [mul_comm] using hterm

theorem reachableChordSq_le_observerPhaseEnergy_mul
    {d : ℕ} {J : Type*} [Fintype J]
    (lam : J → ℝ) (block : J → Fin d → Fin d → ℂ)
    (hlam : ∀ a, 0 ≤ lam a)
    {i j : Fin d}
    (hij : (finiteObserverCoherenceGraph lam block).Reachable i j) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (z : Fin d → ℂ), (∀ i, ‖z i‖ = 1) →
        ‖z i - z j‖ ^ (2 : ℕ) ≤
          C * finiteQuantumObserverPhaseEnergy lam z block := by
  obtain ⟨p⟩ := hij
  induction p with
  | nil =>
      refine ⟨1, zero_lt_one, ?_⟩
      intro z _hunit
      have henergy :
          0 ≤ finiteQuantumObserverPhaseEnergy lam z block :=
        finiteQuantumObserverPhaseEnergy_nonneg lam z block hlam
      simpa using henergy
  | @cons u v w hadj q ih =>
      obtain ⟨C₁, hC₁, hC₁bound⟩ :=
        edgeChordSq_le_observerPhaseEnergy_mul
          lam block hlam hadj
      obtain ⟨C₂, hC₂, hC₂bound⟩ := ih
      refine ⟨2 * (C₁ + C₂), by positivity, ?_⟩
      intro z hunit
      specialize hC₁bound z hunit
      specialize hC₂bound z hunit
      have htri :
          ‖z u - z w‖ ≤ ‖z u - z v‖ + ‖z v - z w‖ := by
        calc
          ‖z u - z w‖ = ‖(z u - z v) - (z w - z v)‖ := by
            congr 1
            ring
          _ ≤ ‖z u - z v‖ + ‖z w - z v‖ := norm_sub_le _ _
          _ = ‖z u - z v‖ + ‖z v - z w‖ := by
            rw [show ‖z w - z v‖ = ‖z v - z w‖ from norm_sub_rev _ _]
      have htriSq : ‖z u - z w‖ ^ (2 : ℕ) ≤
          (‖z u - z v‖ + ‖z v - z w‖) ^ (2 : ℕ) :=
        (sq_le_sq₀ (norm_nonneg _)
          (add_nonneg (norm_nonneg _) (norm_nonneg _))).2 htri
      have henergy :
          0 ≤ finiteQuantumObserverPhaseEnergy lam z block :=
        finiteQuantumObserverPhaseEnergy_nonneg lam z block hlam
      nlinarith [htriSq,
        sq_nonneg (‖z u - z v‖ - ‖z v - z w‖)]

/-- Canonical component-root energy is bounded by one observer-dependent
constant times exact observer phase energy, uniformly over all unit phases. -/
theorem graphRootChordEnergy_le_observerPhaseEnergy_mul
    {d : ℕ} {J : Type*} [Fintype J]
    (lam : J → ℝ) (block : J → Fin d → Fin d → ℂ)
    (hlam : ∀ a, 0 ≤ lam a) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (z : Fin d → ℂ), (∀ i, ‖z i‖ = 1) →
        graphRootChordEnergy (finiteObserverCoherenceGraph lam block) z ≤
          C * finiteQuantumObserverPhaseEnergy lam z block := by
  classical
  let G := finiteObserverCoherenceGraph lam block
  have hvertex (v : graphNonRoot G) :
      ∃ C : ℝ, 0 < C ∧
        ∀ (z : Fin d → ℂ), (∀ i, ‖z i‖ = 1) →
          ‖z v.1 - z (graphComponentRoot G
            (G.connectedComponentMk v.1))‖ ^ (2 : ℕ) ≤
            C * finiteQuantumObserverPhaseEnergy lam z block := by
    have hcomponent :
        G.connectedComponentMk v.1 =
          G.connectedComponentMk
            (graphComponentRoot G (G.connectedComponentMk v.1)) := by
      symm
      exact connectedComponentMk_graphComponentRoot G _
    exact reachableChordSq_le_observerPhaseEnergy_mul
      lam block hlam (ConnectedComponent.exact hcomponent)
  let C : graphNonRoot G → ℝ := fun v => Classical.choose (hvertex v)
  have hCpos (v : graphNonRoot G) : 0 < C v :=
    (Classical.choose_spec (hvertex v)).1
  have hCbound (v : graphNonRoot G) :
      ∀ (z : Fin d → ℂ), (∀ i, ‖z i‖ = 1) →
        ‖z v.1 - z (graphComponentRoot G
          (G.connectedComponentMk v.1))‖ ^ (2 : ℕ) ≤
          C v * finiteQuantumObserverPhaseEnergy lam z block :=
    (Classical.choose_spec (hvertex v)).2
  refine ⟨1 + ∑ v, C v, by
    have hsum : 0 ≤ ∑ v, C v := Finset.sum_nonneg fun v _ => (hCpos v).le
    linarith, ?_⟩
  intro z hunit
  rw [graphRootChordEnergy]
  calc
    (∑ v : graphNonRoot G,
        ‖z v.1 - z (graphComponentRoot G
          (G.connectedComponentMk v.1))‖ ^ (2 : ℕ)) ≤
        ∑ v : graphNonRoot G,
          C v * finiteQuantumObserverPhaseEnergy lam z block := by
      exact Finset.sum_le_sum fun v _ => hCbound v z hunit
    _ = (∑ v : graphNonRoot G, C v) *
        finiteQuantumObserverPhaseEnergy lam z block := by
      rw [Finset.sum_mul]
    _ ≤ (1 + ∑ v : graphNonRoot G, C v) *
        finiteQuantumObserverPhaseEnergy lam z block := by
      apply mul_le_mul_of_nonneg_right
      · linarith
      · exact finiteQuantumObserverPhaseEnergy_nonneg lam z block hlam

/-- Global two-sided observer/root metric equivalence.  Its constants are
uniform over every unit-phase packet. -/
theorem observerPhaseEnergy_rootChordEnergy_comparable
    {d : ℕ} {J : Type*} [Fintype J]
    (lam : J → ℝ) (block : J → Fin d → Fin d → ℂ)
    (hlam : ∀ a, 0 ≤ lam a) :
    ∃ a b : ℝ, 0 < a ∧ 0 < b ∧
      ∀ (z : Fin d → ℂ), (∀ i, ‖z i‖ = 1) →
        a * graphRootChordEnergy
            (finiteObserverCoherenceGraph lam block) z ≤
          finiteQuantumObserverPhaseEnergy lam z block ∧
        finiteQuantumObserverPhaseEnergy lam z block ≤
          b * graphRootChordEnergy
            (finiteObserverCoherenceGraph lam block) z := by
  obtain ⟨C, hC, hroot⟩ :=
    graphRootChordEnergy_le_observerPhaseEnergy_mul
      lam block hlam
  let W : ℝ := ∑ i, ∑ j, finiteObserverUnionWeight lam block i j
  have hW : 0 ≤ W := by
    dsimp [W]
    exact Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ =>
      finiteObserverUnionWeight_nonneg lam block hlam i j
  refine ⟨1 / C, 1 + 4 * W, by positivity, by positivity, ?_⟩
  intro z hunit
  specialize hroot z hunit
  constructor
  · rw [one_div, inv_mul_eq_div]
    apply (div_le_iff₀ hC).2
    simpa only [mul_comm] using hroot
  · have hupper := observerPhaseEnergy_le_rootChordEnergy
      lam z block hlam hunit
    apply hupper.trans
    apply mul_le_mul_of_nonneg_right
    · dsimp only [W]
      linarith
    · exact graphRootChordEnergy_nonneg _ _

end

end RHTower
