import Mathlib.InformationTheory.KullbackLeibler.ChainRule
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

open MeasureTheory InformationTheory ProbabilityTheory
open scoped ENNReal BigOperators

namespace GaloisForLFunctions.HTGeometry

noncomputable section

section MarginalRepair

variable {X H : Type*} [MeasurableSpace X] [MeasurableSpace H]

/-- Reset the visible marginal while retaining the current conditional recovery law. -/
def marginalRepair (μ : Measure X) (η : Kernel X H) : Measure (X × H) := μ ⊗ₘ η

/-- A marginal reset is an exact KL/Bregman projection. -/
theorem klDiv_marginalRepair_pythagorean
    (μ ν : Measure X) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (κ η : Kernel X H) [IsMarkovKernel κ] [IsMarkovKernel η] :
    klDiv (μ ⊗ₘ κ) (ν ⊗ₘ η) =
      klDiv (μ ⊗ₘ κ) (marginalRepair μ η) +
        klDiv (marginalRepair μ η) (ν ⊗ₘ η) := by
  rw [marginalRepair, klDiv_compProd_eq_add, klDiv_compProd_left]
  ac_rfl

/-- A repair step is Pythagorean relative to a feasible target law. -/
def IsKLRepairStep (target current repaired : Measure X) : Prop :=
  klDiv target current = klDiv target repaired + klDiv repaired current

/-- Two repair steps conserve total formation action exactly. -/
theorem twoStepRepair_conservation
    (target p₀ p₁ p₂ : Measure X)
    (h₀ : IsKLRepairStep target p₀ p₁)
    (h₁ : IsKLRepairStep target p₁ p₂) :
    klDiv target p₀ =
      klDiv target p₂ + klDiv p₂ p₁ + klDiv p₁ p₀ := by
  rw [IsKLRepairStep] at h₀ h₁
  rw [h₀, h₁]

/-- Every finite repair history conserves target divergence as residual divergence plus
accumulated endogenous repair action. -/
theorem repairHistory_conservation
    (target : Measure X) (p : ℕ → Measure X)
    (hstep : ∀ n, IsKLRepairStep target (p n) (p (n + 1))) :
    ∀ N, klDiv target (p 0) =
      klDiv target (p N) + ∑ k ∈ Finset.range N, klDiv (p (k + 1)) (p k) := by
  intro N
  induction N with
  | zero => simp
  | succ N ih =>
      have hs := hstep N
      rw [IsKLRepairStep] at hs
      rw [ih, hs, Finset.sum_range_succ]
      ac_rfl

/-- A recurrent finite repair history with finite target divergence is stationary at every step. -/
theorem repairHistory_cycle_stationary
    (target : Measure X) (p : ℕ → Measure X)
    [IsFiniteMeasure target]
    (hfiniteMeasure : ∀ n, IsFiniteMeasure (p n))
    (hstep : ∀ n, IsKLRepairStep target (p n) (p (n + 1)))
    (N : ℕ) (hcycle : p N = p 0)
    (hfinite : klDiv target (p 0) ≠ ⊤) :
    ∀ k < N, p (k + 1) = p k := by
  have hcons := repairHistory_conservation target p hstep N
  rw [hcycle] at hcons
  have hsumzero : ∑ k ∈ Finset.range N, klDiv (p (k + 1)) (p k) = 0 := by
    apply (ENNReal.add_left_inj hfinite).mp
    simpa [add_comm, add_left_comm, add_assoc] using hcons.symm
  intro k hk
  have hkzero : klDiv (p (k + 1)) (p k) = 0 := by
    exact (Finset.sum_eq_zero_iff_of_nonneg
      (fun i _ => bot_le : ∀ i ∈ Finset.range N, 0 ≤ klDiv (p (i + 1)) (p i))).mp
        hsumzero k (Finset.mem_range.mpr hk)
  letI : IsFiniteMeasure (p (k + 1)) := hfiniteMeasure (k + 1)
  letI : IsFiniteMeasure (p k) := hfiniteMeasure k
  exact klDiv_eq_zero_iff.mp hkzero

/-- A finite two-repair recurrence with finite target divergence is already stationary. -/
theorem twoStepRepair_cycle_stationary
    (target p₀ p₁ p₂ : Measure X)
    [IsFiniteMeasure target] [IsFiniteMeasure p₀]
    [IsFiniteMeasure p₁] [IsFiniteMeasure p₂]
    (h₀ : IsKLRepairStep target p₀ p₁)
    (h₁ : IsKLRepairStep target p₁ p₂)
    (hcycle : p₂ = p₀)
    (hfinite : klDiv target p₀ ≠ ⊤) :
    p₁ = p₀ ∧ p₂ = p₁ := by
  have hcons := twoStepRepair_conservation target p₀ p₁ p₂ h₀ h₁
  rw [hcycle] at hcons
  have hzero : klDiv p₀ p₁ + klDiv p₁ p₀ = 0 := by
    apply (ENNReal.add_left_inj hfinite).mp
    simpa [add_comm, add_left_comm, add_assoc] using hcons.symm
  have hz := add_eq_zero.mp hzero
  have hp01 : p₀ = p₁ := klDiv_eq_zero_iff.mp hz.1
  exact ⟨hp01.symm, hcycle.trans hp01⟩

end MarginalRepair

section RecurrentActionProperness

variable {S : Type*}

/-- A real-valued formation potential splits into the next potential plus generated step action. -/
def IsRealActionRepairStep
    (potential : S → ℝ) (history : ℕ → S) (action : ℕ → ℝ) (n : ℕ) : Prop :=
  potential (history n) = potential (history (n + 1)) + action n

/-- The global potential drop is exactly accumulated generated action along every finite history. -/
theorem realActionRepairHistory_conservation
    (potential : S → ℝ) (history : ℕ → S) (action : ℕ → ℝ)
    (hstep : ∀ n, IsRealActionRepairStep potential history action n) :
    ∀ N, potential (history 0) =
      potential (history N) + ∑ k ∈ Finset.range N, action k := by
  intro N
  induction N with
  | zero => simp
  | succ N ih =>
      have hs := hstep N
      rw [IsRealActionRepairStep] at hs
      rw [ih, hs, Finset.sum_range_succ]
      ring

/-- Cofinal approximate recurrence of a nonnegative exact-action history forces every generated
step action to vanish.  This is the global formation/properness selector. -/
theorem recurrentRealActionRepairHistory_stationary
    (potential : S → ℝ) (history : ℕ → S) (action : ℕ → ℝ)
    (hstep : ∀ n, IsRealActionRepairStep potential history action n)
    (haction : ∀ n, 0 ≤ action n)
    (hrecur : ∀ ε > 0, ∀ K, ∃ N, K ≤ N ∧
      |potential (history N) - potential (history 0)| < ε) :
    ∀ n, action n = 0 := by
  intro k
  by_cases hzero : action k = 0
  · exact hzero
  have hpos : 0 < action k := lt_of_le_of_ne (haction k) (Ne.symm hzero)
  obtain ⟨N, hN, hclose⟩ := hrecur (action k / 2) (half_pos hpos) (k + 1)
  have hcons := realActionRepairHistory_conservation potential history action hstep N
  have hkN : k ∈ Finset.range N :=
    Finset.mem_range.mpr (lt_of_lt_of_le (Nat.lt_succ_self k) hN)
  have hle : action k ≤ ∑ i ∈ Finset.range N, action i :=
    Finset.single_le_sum (fun i _ => haction i) hkN
  have hsum : ∑ i ∈ Finset.range N, action i =
      potential (history 0) - potential (history N) := by
    linarith
  have hdrop : potential (history 0) - potential (history N) < action k / 2 := by
    rw [abs_sub_comm] at hclose
    exact lt_of_le_of_lt (le_abs_self _) hclose
  rw [hsum] at hle
  linarith

end RecurrentActionProperness

section BipartitePotential

variable {I J : Type*} [Fintype I] [Fintype J]

/-- Row and column masses of a finite positive formation packet. -/
def bipartiteRowMass (a : I → J → ℝ) (i : I) : ℝ := ∑ j, a i j

def bipartiteColumnMass (a : I → J → ℝ) (j : J) : ℝ := ∑ i, a i j

/-- Multiplicative repair of one marginal. -/
def bipartiteRowRepair (r : I → ℝ) (a : I → J → ℝ) : I → J → ℝ :=
  fun i j => (r i / bipartiteRowMass a i) * a i j

def bipartiteColumnRepair (c : J → ℝ) (a : I → J → ℝ) : I → J → ℝ :=
  fun i j => (c j / bipartiteColumnMass a j) * a i j

omit [Fintype I] in
/-- Row repair hits its requested marginal exactly. -/
theorem bipartiteRowMass_rowRepair
    (r : I → ℝ) (a : I → J → ℝ)
    (hrow : ∀ i, bipartiteRowMass a i ≠ 0) (i : I) :
    bipartiteRowMass (bipartiteRowRepair r a) i = r i := by
  rw [bipartiteRowMass]
  simp only [bipartiteRowRepair, ← Finset.mul_sum]
  exact div_mul_cancel₀ _ (hrow i)

omit [Fintype I] in
/-- Row-mass failure generates the unique repair inside the multiplicative row-scaling class. -/
theorem bipartiteRowRepair_unique
    (r : I → ℝ) (a b : I → J → ℝ)
    (hrow : ∀ i, bipartiteRowMass a i ≠ 0)
    (hscale : ∃ u : I → ℝ, ∀ i j, b i j = u i * a i j)
    (hmass : ∀ i, bipartiteRowMass b i = r i) :
    b = bipartiteRowRepair r a := by
  rcases hscale with ⟨u, hu⟩
  funext i j
  have hscalar : u i * bipartiteRowMass a i = r i := by
    calc
      u i * bipartiteRowMass a i = ∑ j, u i * a i j := by
        rw [bipartiteRowMass, Finset.mul_sum]
      _ = ∑ j, b i j := Finset.sum_congr rfl (fun j _ => (hu i j).symm)
      _ = bipartiteRowMass b i := by rw [bipartiteRowMass]
      _ = r i := hmass i
  have huval : u i = r i / bipartiteRowMass a i :=
    (eq_div_iff (hrow i)).2 hscalar
  rw [hu, bipartiteRowRepair, huval]

omit [Fintype J] in
/-- Column repair hits its requested marginal exactly. -/
theorem bipartiteColumnMass_columnRepair
    (c : J → ℝ) (a : I → J → ℝ)
    (hcol : ∀ j, bipartiteColumnMass a j ≠ 0) (j : J) :
    bipartiteColumnMass (bipartiteColumnRepair c a) j = c j := by
  rw [bipartiteColumnMass]
  simp only [bipartiteColumnRepair, ← Finset.mul_sum]
  exact div_mul_cancel₀ _ (hcol j)

omit [Fintype J] in
/-- Column-mass failure generates the unique repair inside the multiplicative column-scaling class. -/
theorem bipartiteColumnRepair_unique
    (c : J → ℝ) (a b : I → J → ℝ)
    (hcol : ∀ j, bipartiteColumnMass a j ≠ 0)
    (hscale : ∃ v : J → ℝ, ∀ i j, b i j = v j * a i j)
    (hmass : ∀ j, bipartiteColumnMass b j = c j) :
    b = bipartiteColumnRepair c a := by
  rcases hscale with ⟨v, hv⟩
  funext i j
  have hscalar : v j * bipartiteColumnMass a j = c j := by
    calc
      v j * bipartiteColumnMass a j = ∑ i, v j * a i j := by
        rw [bipartiteColumnMass, Finset.mul_sum]
      _ = ∑ i, b i j := Finset.sum_congr rfl (fun i _ => (hv i j).symm)
      _ = bipartiteColumnMass b j := by rw [bipartiteColumnMass]
      _ = c j := hmass j
  have hvval : v j = c j / bipartiteColumnMass a j :=
    (eq_div_iff (hcol j)).2 hscalar
  rw [hv, bipartiteColumnRepair, hvval]

omit [Fintype I] in
/-- Transposition exchanges the two endogenous repair laws. -/
theorem bipartiteRowRepair_transpose
    (r : I → ℝ) (a : I → J → ℝ) :
    (fun j i => bipartiteRowRepair r a i j) =
      bipartiteColumnRepair r (fun j i => a i j) := by
  rfl

omit [Fintype J] in
theorem bipartiteColumnRepair_transpose
    (c : J → ℝ) (a : I → J → ℝ) :
    (fun j i => bipartiteColumnRepair c a i j) =
      bipartiteRowRepair c (fun j i => a i j) := by
  rfl

/-- Multiplicative formation by left and right logarithmic potentials. -/
def bipartitePotentialForm (w : I → J → ℝ) (x : I → ℝ) (y : J → ℝ) : I → J → ℝ :=
  fun i j => Real.exp (x i + y j) * w i j

/-- Positive quadratic response generated by a bipartite formation packet. -/
def bipartiteFormationEnergy (w : I → J → ℝ) (x : I → ℝ) (y : J → ℝ) : ℝ :=
  ∑ i, ∑ j, w i j * (x i + y j) ^ 2

omit [Fintype I] [Fintype J] in
/-- The global potential gauge does not change formed weights. -/
theorem bipartitePotentialForm_gauge
    (w : I → J → ℝ) (x : I → ℝ) (y : J → ℝ) (c : ℝ) :
    bipartitePotentialForm w (fun i => x i + c) (fun j => y j - c) =
      bipartitePotentialForm w x y := by
  funext i j
  simp [bipartitePotentialForm]

omit [Fintype I] [Fintype J] in
/-- A strictly positive formed packet has no hidden stabilizer beyond global gauge. -/
theorem bipartitePotentialForm_eq_self_iff_gauge
    [Nonempty I] [Nonempty J]
    (w : I → J → ℝ) (hw : ∀ i j, 0 < w i j)
    (x : I → ℝ) (y : J → ℝ) :
    bipartitePotentialForm w x y = w ↔
      ∃ c : ℝ, (∀ i, x i = c) ∧ (∀ j, y j = -c) := by
  classical
  constructor
  · intro hform
    have hsum : ∀ i j, x i + y j = 0 := by
      intro i j
      have hij := congrFun (congrFun hform i) j
      have hexp : Real.exp (x i + y j) = 1 := by
        apply (mul_right_cancel₀ (ne_of_gt (hw i j)))
        simpa [bipartitePotentialForm] using hij
      exact (Real.exp_eq_one_iff _).mp hexp
    let j₀ : J := Classical.choice inferInstance
    refine ⟨-y j₀, ?_, ?_⟩
    · intro i
      linarith [hsum i j₀]
    · intro j
      let i₀ : I := Classical.choice inferInstance
      linarith [hsum i₀ j, hsum i₀ j₀]
  · rintro ⟨c, hx, hy⟩
    funext i j
    simp [bipartitePotentialForm, hx, hy]

/-- The same global gauge leaves formation energy unchanged. -/
theorem bipartiteFormationEnergy_gauge
    (w : I → J → ℝ) (x : I → ℝ) (y : J → ℝ) (c : ℝ) :
    bipartiteFormationEnergy w (fun i => x i + c) (fun j => y j - c) =
      bipartiteFormationEnergy w x y := by
  simp [bipartiteFormationEnergy]

/-- Functional reflection swaps the two potential legs without changing energy. -/
theorem bipartiteFormationEnergy_transpose
    (w : I → J → ℝ) (x : I → ℝ) (y : J → ℝ) :
    bipartiteFormationEnergy (fun j i => w i j) y x =
      bipartiteFormationEnergy w x y := by
  unfold bipartiteFormationEnergy
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [add_comm]

/-- Strictly positive incidence has exactly the one-dimensional global gauge as energy radical. -/
theorem bipartiteFormationEnergy_eq_zero_iff_gauge
    [Nonempty I] [Nonempty J]
    (w : I → J → ℝ) (hw : ∀ i j, 0 < w i j)
    (x : I → ℝ) (y : J → ℝ) :
    bipartiteFormationEnergy w x y = 0 ↔
      ∃ c : ℝ, (∀ i, x i = c) ∧ (∀ j, y j = -c) := by
  classical
  constructor
  · intro hzero
    have hterm : ∀ i j, x i + y j = 0 := by
      intro i j
      have hnonneg : ∀ i j, 0 ≤ w i j * (x i + y j) ^ 2 := by
        intro i j
        exact mul_nonneg (le_of_lt (hw i j)) (sq_nonneg _)
      have hij : w i j * (x i + y j) ^ 2 = 0 := by
        have houter : ∑ i, ∑ j, w i j * (x i + y j) ^ 2 = 0 := hzero
        have hrow : ∑ j, w i j * (x i + y j) ^ 2 = 0 := by
          exact (Finset.sum_eq_zero_iff_of_nonneg (fun k _ =>
            Finset.sum_nonneg (fun l _ => hnonneg k l))).mp houter i (Finset.mem_univ i)
        exact (Finset.sum_eq_zero_iff_of_nonneg (fun l _ => hnonneg i l)).mp hrow j
          (Finset.mem_univ j)
      exact (mul_eq_zero.mp hij).resolve_left (ne_of_gt (hw i j)) |> sq_eq_zero_iff.mp
    let j₀ : J := Classical.choice inferInstance
    refine ⟨-y j₀, ?_, ?_⟩
    · intro i
      linarith [hterm i j₀]
    · intro j
      let i₀ : I := Classical.choice inferInstance
      linarith [hterm i₀ j, hterm i₀ j₀]
  · rintro ⟨c, hx, hy⟩
    simp [bipartiteFormationEnergy, hx, hy]

end BipartitePotential

end

end GaloisForLFunctions.HTGeometry
