import Mathlib.InformationTheory.KullbackLeibler.ChainRule
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Quotient
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Topology.MetricSpace.Bounded
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

section FiniteEntropy

variable {I J : Type*} [Fintype I] [Fintype J]

def bipartiteRelativeEntropy (x a : I → J → ℝ) : ℝ :=
  ∑ i, ∑ j, (x i j * Real.log (x i j / a i j) - x i j + a i j)

private theorem relativeEntropyTerm_eq_klFun
    {x a : ℝ} (ha : a ≠ 0) :
    x * Real.log (x / a) - x + a = a * klFun (x / a) := by
  rw [klFun_apply]
  field_simp
  ring

theorem bipartiteRelativeEntropy_nonneg
    (x a : I → J → ℝ) (hx : ∀ i j, 0 < x i j) (ha : ∀ i j, 0 < a i j) :
    0 ≤ bipartiteRelativeEntropy x a := by
  classical
  unfold bipartiteRelativeEntropy
  exact Finset.sum_nonneg fun i _ ↦ Finset.sum_nonneg fun j _ ↦ by
    rw [relativeEntropyTerm_eq_klFun (ha i j).ne']
    exact mul_nonneg (ha i j).le (klFun_nonneg (div_nonneg (hx i j).le (ha i j).le))

theorem bipartiteRelativeEntropy_eq_zero_iff
    (x a : I → J → ℝ) (hx : ∀ i j, 0 < x i j) (ha : ∀ i j, 0 < a i j) :
    bipartiteRelativeEntropy x a = 0 ↔ x = a := by
  classical
  constructor
  · intro hzero
    funext i j
    have hrow : ∑ j, (x i j * Real.log (x i j / a i j) - x i j + a i j) = 0 := by
      apply (Finset.sum_eq_zero_iff_of_nonneg (fun i _ ↦
        Finset.sum_nonneg fun j _ ↦ ?_)).mp hzero i (Finset.mem_univ i)
      rw [relativeEntropyTerm_eq_klFun (ha _ _).ne']
      exact mul_nonneg (ha _ _).le (klFun_nonneg (div_nonneg (hx _ _).le (ha _ _).le))
    have hterm : x i j * Real.log (x i j / a i j) - x i j + a i j = 0 := by
      apply (Finset.sum_eq_zero_iff_of_nonneg (fun j _ ↦ ?_)).mp hrow j (Finset.mem_univ j)
      rw [relativeEntropyTerm_eq_klFun (ha _ _).ne']
      exact mul_nonneg (ha _ _).le (klFun_nonneg (div_nonneg (hx _ _).le (ha _ _).le))
    rw [relativeEntropyTerm_eq_klFun (ha i j).ne'] at hterm
    have hkl : klFun (x i j / a i j) = 0 :=
      (mul_eq_zero.mp hterm).resolve_left (ha i j).ne'
    have hratio := (klFun_eq_zero_iff (div_nonneg (hx i j).le (ha i j).le)).mp hkl
    exact (div_eq_one_iff_eq (ha i j).ne').mp hratio
  · rintro rfl
    simp [bipartiteRelativeEntropy]

theorem bipartiteRelativeEntropy_transpose (x a : I → J → ℝ) :
    bipartiteRelativeEntropy (fun j i ↦ x i j) (fun j i ↦ a i j) =
      bipartiteRelativeEntropy x a := by
  unfold bipartiteRelativeEntropy
  rw [Finset.sum_comm]

private theorem relativeEntropyTerm_scaling
    {x a u : ℝ} (hx : 0 < x) (ha : 0 < a) (hu : 0 < u) :
    x * Real.log (x / a) - x + a =
      (x * Real.log (x / (u * a)) - x + u * a) +
        (u * a * Real.log ((u * a) / a) - u * a + a) +
          (x - u * a) * Real.log u := by
  have hlogua : Real.log (u * a) = Real.log u + Real.log a :=
    Real.log_mul hu.ne' ha.ne'
  rw [Real.log_div hx.ne' ha.ne', Real.log_div hx.ne' (mul_pos hu ha).ne',
    Real.log_div (mul_pos hu ha).ne' ha.ne', hlogua]
  ring

theorem bipartiteRelativeEntropy_rowScaling_pythagorean
    (x a : I → J → ℝ) (u : I → ℝ)
    (hx : ∀ i j, 0 < x i j) (ha : ∀ i j, 0 < a i j) (hu : ∀ i, 0 < u i)
    (hmass : ∀ i, bipartiteRowMass x i =
      bipartiteRowMass (fun i j ↦ u i * a i j) i) :
    bipartiteRelativeEntropy x a =
      bipartiteRelativeEntropy x (fun i j ↦ u i * a i j) +
        bipartiteRelativeEntropy (fun i j ↦ u i * a i j) a := by
  classical
  unfold bipartiteRelativeEntropy
  calc
    ∑ i, ∑ j, (x i j * Real.log (x i j / a i j) - x i j + a i j) =
        ∑ i, ∑ j, ((x i j * Real.log (x i j / (u i * a i j)) - x i j + u i * a i j) +
          (u i * a i j * Real.log ((u i * a i j) / a i j) - u i * a i j + a i j) +
          (x i j - u i * a i j) * Real.log (u i)) := by
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      exact relativeEntropyTerm_scaling (hx i j) (ha i j) (hu i)
    _ = (∑ i, ∑ j, (x i j * Real.log (x i j / (u i * a i j)) - x i j + u i * a i j)) +
        ∑ i, ∑ j, (u i * a i j * Real.log ((u i * a i j) / a i j) - u i * a i j + a i j) := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i _
      rw [← Finset.sum_add_distrib]
      have hcancel : ∑ j, (x i j - u i * a i j) * Real.log (u i) = 0 := by
        rw [← Finset.sum_mul]
        suffices ∑ j, (x i j - u i * a i j) = 0 by rw [this, zero_mul]
        rw [Finset.sum_sub_distrib]
        simpa [bipartiteRowMass] using sub_eq_zero.mpr (hmass i)
      calc
        ∑ j, ((x i j * Real.log (x i j / (u i * a i j)) - x i j + u i * a i j) +
            (u i * a i j * Real.log ((u i * a i j) / a i j) - u i * a i j + a i j) +
            (x i j - u i * a i j) * Real.log (u i)) =
            (∑ j, ((x i j * Real.log (x i j / (u i * a i j)) - x i j + u i * a i j) +
              (u i * a i j * Real.log ((u i * a i j) / a i j) - u i * a i j + a i j))) +
              ∑ j, (x i j - u i * a i j) * Real.log (u i) := Finset.sum_add_distrib
        _ = _ := by rw [hcancel, add_zero]

theorem bipartiteRelativeEntropy_columnScaling_pythagorean
    (x a : I → J → ℝ) (v : J → ℝ)
    (hx : ∀ i j, 0 < x i j) (ha : ∀ i j, 0 < a i j) (hv : ∀ j, 0 < v j)
    (hmass : ∀ j, bipartiteColumnMass x j =
      bipartiteColumnMass (fun i j ↦ v j * a i j) j) :
    bipartiteRelativeEntropy x a =
      bipartiteRelativeEntropy x (fun i j ↦ v j * a i j) +
        bipartiteRelativeEntropy (fun i j ↦ v j * a i j) a := by
  have h := bipartiteRelativeEntropy_rowScaling_pythagorean
    (x := fun j i ↦ x i j) (a := fun j i ↦ a i j) v
    (fun j i ↦ hx i j) (fun j i ↦ ha i j) hv (by
      intro j
      simpa [bipartiteRowMass, bipartiteColumnMass] using hmass j)
  simpa only [bipartiteRelativeEntropy_transpose] using h

omit [Fintype I] in
theorem bipartiteRowMass_pos [Nonempty J]
    (a : I → J → ℝ) (ha : ∀ i j, 0 < a i j) (i : I) :
    0 < bipartiteRowMass a i := by
  classical
  unfold bipartiteRowMass
  exact Finset.sum_pos (fun j _ ↦ ha i j) Finset.univ_nonempty

omit [Fintype J] in
theorem bipartiteColumnMass_pos [Nonempty I]
    (a : I → J → ℝ) (ha : ∀ i j, 0 < a i j) (j : J) :
    0 < bipartiteColumnMass a j := by
  classical
  unfold bipartiteColumnMass
  exact Finset.sum_pos (fun i _ ↦ ha i j) Finset.univ_nonempty

omit [Fintype I] in
theorem bipartiteRowRepair_pos [Nonempty J]
    (r : I → ℝ) (a : I → J → ℝ)
    (hr : ∀ i, 0 < r i) (ha : ∀ i j, 0 < a i j) :
    ∀ i j, 0 < bipartiteRowRepair r a i j := by
  intro i j
  exact mul_pos (div_pos (hr i) (bipartiteRowMass_pos a ha i)) (ha i j)

omit [Fintype J] in
theorem bipartiteColumnRepair_pos [Nonempty I]
    (c : J → ℝ) (a : I → J → ℝ)
    (hc : ∀ j, 0 < c j) (ha : ∀ i j, 0 < a i j) :
    ∀ i j, 0 < bipartiteColumnRepair c a i j := by
  intro i j
  exact mul_pos (div_pos (hc j) (bipartiteColumnMass_pos a ha j)) (ha i j)

theorem bipartiteRelativeEntropy_rowRepair_pythagorean [Nonempty J]
    (x a : I → J → ℝ) (r : I → ℝ)
    (hx : ∀ i j, 0 < x i j) (ha : ∀ i j, 0 < a i j) (hr : ∀ i, 0 < r i)
    (hmass : ∀ i, bipartiteRowMass x i = r i) :
    bipartiteRelativeEntropy x a =
      bipartiteRelativeEntropy x (bipartiteRowRepair r a) +
        bipartiteRelativeEntropy (bipartiteRowRepair r a) a := by
  apply bipartiteRelativeEntropy_rowScaling_pythagorean
    (u := fun i ↦ r i / bipartiteRowMass a i) x a hx ha
  · intro i
    exact div_pos (hr i) (bipartiteRowMass_pos a ha i)
  · intro i
    rw [hmass i]
    exact (bipartiteRowMass_rowRepair r a
      (fun i ↦ (bipartiteRowMass_pos a ha i).ne') i).symm

theorem bipartiteRelativeEntropy_columnRepair_pythagorean [Nonempty I]
    (x a : I → J → ℝ) (c : J → ℝ)
    (hx : ∀ i j, 0 < x i j) (ha : ∀ i j, 0 < a i j) (hc : ∀ j, 0 < c j)
    (hmass : ∀ j, bipartiteColumnMass x j = c j) :
    bipartiteRelativeEntropy x a =
      bipartiteRelativeEntropy x (bipartiteColumnRepair c a) +
        bipartiteRelativeEntropy (bipartiteColumnRepair c a) a := by
  apply bipartiteRelativeEntropy_columnScaling_pythagorean
    (v := fun j ↦ c j / bipartiteColumnMass a j) x a hx ha
  · intro j
    exact div_pos (hc j) (bipartiteColumnMass_pos a ha j)
  · intro j
    rw [hmass j]
    exact (bipartiteColumnMass_columnRepair c a
      (fun j ↦ (bipartiteColumnMass_pos a ha j).ne') j).symm

def bipartiteProductWitness (r : I → ℝ) (c : J → ℝ) (M : ℝ) : I → J → ℝ :=
  fun i j ↦ r i * c j / M

omit [Fintype I] [Fintype J] in
theorem bipartiteProductWitness_pos
    (r : I → ℝ) (c : J → ℝ) (M : ℝ)
    (hr : ∀ i, 0 < r i) (hc : ∀ j, 0 < c j) (hM : 0 < M) :
    ∀ i j, 0 < bipartiteProductWitness r c M i j := by
  intro i j
  exact div_pos (mul_pos (hr i) (hc j)) hM

omit [Fintype I] in
theorem bipartiteProductWitness_rowMass
    (r : I → ℝ) (c : J → ℝ) (M : ℝ) (hM : M ≠ 0)
    (hcM : ∑ j, c j = M) (i : I) :
    bipartiteRowMass (bipartiteProductWitness r c M) i = r i := by
  classical
  unfold bipartiteRowMass bipartiteProductWitness
  rw [← Finset.sum_div, ← Finset.mul_sum, hcM]
  exact mul_div_cancel_right₀ _ hM

omit [Fintype J] in
theorem bipartiteProductWitness_columnMass
    (r : I → ℝ) (c : J → ℝ) (M : ℝ) (hM : M ≠ 0)
    (hrM : ∑ i, r i = M) (j : J) :
    bipartiteColumnMass (bipartiteProductWitness r c M) j = c j := by
  classical
  unfold bipartiteColumnMass bipartiteProductWitness
  rw [← Finset.sum_div, ← Finset.sum_mul, hrM]
  rw [mul_comm]
  exact mul_div_cancel_right₀ _ hM

def bipartiteAlternatingRepairHistory
    (r : I → ℝ) (c : J → ℝ) (a : I → J → ℝ) : ℕ → I → J → ℝ
  | 0 => a
  | n + 1 =>
      if Even n then
        bipartiteRowRepair r (bipartiteAlternatingRepairHistory r c a n)
      else
        bipartiteColumnRepair c (bipartiteAlternatingRepairHistory r c a n)

@[simp]
theorem bipartiteAlternatingRepairHistory_zero
    (r : I → ℝ) (c : J → ℝ) (a : I → J → ℝ) :
    bipartiteAlternatingRepairHistory r c a 0 = a := rfl

theorem bipartiteAlternatingRepairHistory_succ_of_even
    (r : I → ℝ) (c : J → ℝ) (a : I → J → ℝ) (n : ℕ) (hn : Even n) :
    bipartiteAlternatingRepairHistory r c a (n + 1) =
      bipartiteRowRepair r (bipartiteAlternatingRepairHistory r c a n) := by
  rw [bipartiteAlternatingRepairHistory]
  simp [hn]

theorem bipartiteAlternatingRepairHistory_succ_of_not_even
    (r : I → ℝ) (c : J → ℝ) (a : I → J → ℝ) (n : ℕ) (hn : ¬ Even n) :
    bipartiteAlternatingRepairHistory r c a (n + 1) =
      bipartiteColumnRepair c (bipartiteAlternatingRepairHistory r c a n) := by
  rw [bipartiteAlternatingRepairHistory]
  simp [hn]

theorem bipartiteAlternatingRepairHistory_pos [Nonempty I] [Nonempty J]
    (r : I → ℝ) (c : J → ℝ) (a : I → J → ℝ)
    (hr : ∀ i, 0 < r i) (hc : ∀ j, 0 < c j) (ha : ∀ i j, 0 < a i j) :
    ∀ n i j, 0 < bipartiteAlternatingRepairHistory r c a n i j := by
  intro n
  induction n with
  | zero => exact ha
  | succ n ih =>
      by_cases hn : Even n
      · rw [bipartiteAlternatingRepairHistory_succ_of_even r c a n hn]
        exact bipartiteRowRepair_pos r _ hr ih
      · rw [bipartiteAlternatingRepairHistory_succ_of_not_even r c a n hn]
        exact bipartiteColumnRepair_pos c _ hc ih

theorem bipartiteAlternatingRepairHistory_pythagorean [Nonempty I] [Nonempty J]
    (target : I → J → ℝ) (r : I → ℝ) (c : J → ℝ) (a : I → J → ℝ)
    (htarget : ∀ i j, 0 < target i j) (hr : ∀ i, 0 < r i) (hc : ∀ j, 0 < c j)
    (ha : ∀ i j, 0 < a i j)
    (htargetRow : ∀ i, bipartiteRowMass target i = r i)
    (htargetColumn : ∀ j, bipartiteColumnMass target j = c j) :
    ∀ n, bipartiteRelativeEntropy target (bipartiteAlternatingRepairHistory r c a n) =
      bipartiteRelativeEntropy target (bipartiteAlternatingRepairHistory r c a (n + 1)) +
        bipartiteRelativeEntropy (bipartiteAlternatingRepairHistory r c a (n + 1))
          (bipartiteAlternatingRepairHistory r c a n) := by
  intro n
  by_cases hn : Even n
  · rw [bipartiteAlternatingRepairHistory_succ_of_even r c a n hn]
    exact bipartiteRelativeEntropy_rowRepair_pythagorean target _ r htarget
      (bipartiteAlternatingRepairHistory_pos r c a hr hc ha n) hr htargetRow
  · rw [bipartiteAlternatingRepairHistory_succ_of_not_even r c a n hn]
    exact bipartiteRelativeEntropy_columnRepair_pythagorean target _ c htarget
      (bipartiteAlternatingRepairHistory_pos r c a hr hc ha n) hc htargetColumn

theorem bipartiteAlternatingRepairHistory_conservation [Nonempty I] [Nonempty J]
    (target : I → J → ℝ) (r : I → ℝ) (c : J → ℝ) (a : I → J → ℝ)
    (htarget : ∀ i j, 0 < target i j) (hr : ∀ i, 0 < r i) (hc : ∀ j, 0 < c j)
    (ha : ∀ i j, 0 < a i j)
    (htargetRow : ∀ i, bipartiteRowMass target i = r i)
    (htargetColumn : ∀ j, bipartiteColumnMass target j = c j) :
    ∀ N, bipartiteRelativeEntropy target a =
      bipartiteRelativeEntropy target (bipartiteAlternatingRepairHistory r c a N) +
        ∑ k ∈ Finset.range N,
          bipartiteRelativeEntropy (bipartiteAlternatingRepairHistory r c a (k + 1))
            (bipartiteAlternatingRepairHistory r c a k) := by
  apply realActionRepairHistory_conservation
    (potential := bipartiteRelativeEntropy target)
    (history := bipartiteAlternatingRepairHistory r c a)
    (action := fun k ↦
      bipartiteRelativeEntropy (bipartiteAlternatingRepairHistory r c a (k + 1))
        (bipartiteAlternatingRepairHistory r c a k))
  intro n
  exact bipartiteAlternatingRepairHistory_pythagorean target r c a htarget hr hc ha
    htargetRow htargetColumn n

/-- Accumulated exact information action of the literal alternating row/column repair history. -/
def bipartiteAlternatingRepairAction
    (r : I → ℝ) (c : J → ℝ) (a : I → J → ℝ) (N : ℕ) : ℝ :=
  ∑ k ∈ Finset.range N,
    bipartiteRelativeEntropy (bipartiteAlternatingRepairHistory r c a (k + 1))
      (bipartiteAlternatingRepairHistory r c a k)

/-- Positive repairs make accumulated information action monotone in history length. -/
theorem monotone_bipartiteAlternatingRepairAction [Nonempty I] [Nonempty J]
    (r : I → ℝ) (c : J → ℝ) (a : I → J → ℝ)
    (hr : ∀ i, 0 < r i) (hc : ∀ j, 0 < c j) (ha : ∀ i j, 0 < a i j) :
    Monotone (bipartiteAlternatingRepairAction r c a) := by
  intro m n hmn
  apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hmn)
  intro k _ _
  exact bipartiteRelativeEntropy_nonneg _ _
    (bipartiteAlternatingRepairHistory_pos r c a hr hc ha (k + 1))
    (bipartiteAlternatingRepairHistory_pos r c a hr hc ha k)

/-- Accumulated repair action is bounded by initial divergence from every positive feasible target. -/
theorem bipartiteAlternatingRepairAction_le_initial [Nonempty I] [Nonempty J]
    (target : I → J → ℝ) (r : I → ℝ) (c : J → ℝ) (a : I → J → ℝ)
    (htarget : ∀ i j, 0 < target i j) (hr : ∀ i, 0 < r i) (hc : ∀ j, 0 < c j)
    (ha : ∀ i j, 0 < a i j)
    (htargetRow : ∀ i, bipartiteRowMass target i = r i)
    (htargetColumn : ∀ j, bipartiteColumnMass target j = c j) (N : ℕ) :
    bipartiteAlternatingRepairAction r c a N ≤ bipartiteRelativeEntropy target a := by
  have hcons := bipartiteAlternatingRepairHistory_conservation target r c a htarget hr hc ha
    htargetRow htargetColumn N
  have hresidual : 0 ≤
      bipartiteRelativeEntropy target (bipartiteAlternatingRepairHistory r c a N) :=
    bipartiteRelativeEntropy_nonneg _ _ htarget
      (bipartiteAlternatingRepairHistory_pos r c a hr hc ha N)
  unfold bipartiteAlternatingRepairAction
  linarith

/-- The paper's predeclared product packet is a feasible target for exact global conservation. -/
theorem bipartiteProductWitness_alternatingRepairHistory_conservation
    [Nonempty I] [Nonempty J]
    (r : I → ℝ) (c : J → ℝ) (M : ℝ) (a : I → J → ℝ)
    (hr : ∀ i, 0 < r i) (hc : ∀ j, 0 < c j) (hM : 0 < M)
    (hrM : ∑ i, r i = M) (hcM : ∑ j, c j = M)
    (ha : ∀ i j, 0 < a i j) :
    ∀ N, bipartiteRelativeEntropy (bipartiteProductWitness r c M) a =
      bipartiteRelativeEntropy (bipartiteProductWitness r c M)
          (bipartiteAlternatingRepairHistory r c a N) +
        bipartiteAlternatingRepairAction r c a N := by
  exact bipartiteAlternatingRepairHistory_conservation (bipartiteProductWitness r c M) r c a
    (bipartiteProductWitness_pos r c M hr hc hM) hr hc ha
    (bipartiteProductWitness_rowMass r c M hM.ne' hcM)
    (bipartiteProductWitness_columnMass r c M hM.ne' hrM)

theorem bipartiteAlternatingRepairHistory_cycle_balanced [Nonempty I] [Nonempty J]
    (target : I → J → ℝ) (r : I → ℝ) (c : J → ℝ) (a : I → J → ℝ)
    (htarget : ∀ i j, 0 < target i j) (hr : ∀ i, 0 < r i) (hc : ∀ j, 0 < c j)
    (ha : ∀ i j, 0 < a i j)
    (htargetRow : ∀ i, bipartiteRowMass target i = r i)
    (htargetColumn : ∀ j, bipartiteColumnMass target j = c j)
    (N : ℕ) (hN : 2 ≤ N)
    (hcycle : bipartiteAlternatingRepairHistory r c a N = a) :
    (∀ i, bipartiteRowMass a i = r i) ∧
      (∀ j, bipartiteColumnMass a j = c j) ∧
      ∀ k < N, bipartiteAlternatingRepairHistory r c a (k + 1) =
        bipartiteAlternatingRepairHistory r c a k := by
  let p := bipartiteAlternatingRepairHistory r c a
  have hcyclep : p N = a := hcycle
  have hp : ∀ n i j, 0 < p n i j :=
    bipartiteAlternatingRepairHistory_pos r c a hr hc ha
  have hcons := bipartiteAlternatingRepairHistory_conservation target r c a htarget hr hc ha
    htargetRow htargetColumn N
  have hsumzero : ∑ k ∈ Finset.range N, bipartiteRelativeEntropy (p (k + 1)) (p k) = 0 := by
    change bipartiteRelativeEntropy target a = bipartiteRelativeEntropy target (p N) +
      ∑ k ∈ Finset.range N, bipartiteRelativeEntropy (p (k + 1)) (p k) at hcons
    rw [hcyclep] at hcons
    linarith
  have hstationary : ∀ k < N, p (k + 1) = p k := by
    intro k hk
    have htermzero : bipartiteRelativeEntropy (p (k + 1)) (p k) = 0 := by
      apply (Finset.sum_eq_zero_iff_of_nonneg (fun n _ ↦
        bipartiteRelativeEntropy_nonneg _ _ (hp (n + 1)) (hp n))).mp hsumzero k
      exact Finset.mem_range.mpr hk
    exact (bipartiteRelativeEntropy_eq_zero_iff _ _ (hp (k + 1)) (hp k)).mp htermzero
  have hzeroN : 0 < N := lt_of_lt_of_le (Nat.zero_lt_succ 1) hN
  have honeN : 1 < N := lt_of_lt_of_le (Nat.succ_lt_succ (Nat.zero_lt_succ 0)) hN
  have hrowStationary := hstationary 0 hzeroN
  have hcolStationary := hstationary 1 honeN
  have hrowRepair : bipartiteRowRepair r a = a := by
    simpa [p, bipartiteAlternatingRepairHistory_succ_of_even r c a 0 (by simp)] using
      hrowStationary
  have hcolumnRepair : bipartiteColumnRepair c a = a := by
    have hstep1 : p 2 = bipartiteColumnRepair c (p 1) := by
      simpa [p] using bipartiteAlternatingRepairHistory_succ_of_not_even r c a 1 (by simp)
    rw [hstep1, show p 1 = a by simpa [p] using hrowStationary] at hcolStationary
    exact hcolStationary
  refine ⟨?_, ?_, hstationary⟩
  · intro i
    rw [← hrowRepair]
    exact bipartiteRowMass_rowRepair r a
      (fun i ↦ (bipartiteRowMass_pos a ha i).ne') i
  · intro j
    rw [← hcolumnRepair]
    exact bipartiteColumnMass_columnRepair c a
      (fun j ↦ (bipartiteColumnMass_pos a ha j).ne') j

/-- Any recurrent positive alternating repair history of length at least two is already balanced,
with the product witness supplying feasibility rather than an extra existence premise. -/
theorem bipartiteProductWitness_alternatingRepairHistory_cycle_balanced
    [Nonempty I] [Nonempty J]
    (r : I → ℝ) (c : J → ℝ) (M : ℝ) (a : I → J → ℝ)
    (hr : ∀ i, 0 < r i) (hc : ∀ j, 0 < c j) (hM : 0 < M)
    (hrM : ∑ i, r i = M) (hcM : ∑ j, c j = M)
    (ha : ∀ i j, 0 < a i j) (N : ℕ) (hN : 2 ≤ N)
    (hcycle : bipartiteAlternatingRepairHistory r c a N = a) :
    (∀ i, bipartiteRowMass a i = r i) ∧
      (∀ j, bipartiteColumnMass a j = c j) ∧
      ∀ k < N, bipartiteAlternatingRepairHistory r c a (k + 1) =
        bipartiteAlternatingRepairHistory r c a k := by
  exact bipartiteAlternatingRepairHistory_cycle_balanced
    (bipartiteProductWitness r c M) r c a
    (bipartiteProductWitness_pos r c M hr hc hM) hr hc ha
    (bipartiteProductWitness_rowMass r c M hM.ne' hcM)
    (bipartiteProductWitness_columnMass r c M hM.ne' hrM) N hN hcycle

end FiniteEntropy

section GaugeQuotient

variable {I J : Type*} [Fintype I] [Fintype J]

abbrev BipartitePotentialSpace (I J : Type*) := (I → ℝ) × (J → ℝ)

def bipartiteGaugeVector : BipartitePotentialSpace I J :=
  (fun _ ↦ 1, fun _ ↦ -1)

def bipartiteGaugeSubspace : Submodule ℝ (BipartitePotentialSpace I J) :=
  Submodule.span ℝ {bipartiteGaugeVector (I := I) (J := J)}

def bipartiteEdgeSumLinearMap :
    BipartitePotentialSpace I J →ₗ[ℝ] (I × J → ℝ) where
  toFun p ij := p.1 ij.1 + p.2 ij.2
  map_add' _ _ := by ext; dsimp; ring
  map_smul' _ _ := by ext; simp [mul_add]

omit [Fintype I] [Fintype J] in
theorem bipartiteEdgeSumLinearMap_ker [Nonempty I] [Nonempty J] :
    LinearMap.ker (bipartiteEdgeSumLinearMap (I := I) (J := J)) =
      bipartiteGaugeSubspace (I := I) (J := J) := by
  classical
  ext p
  constructor
  · intro hp
    have hedge : ∀ i j, p.1 i + p.2 j = 0 := by
      intro i j
      change (fun ij : I × J ↦ p.1 ij.1 + p.2 ij.2) = 0 at hp
      exact congrFun hp (i, j)
    let j₀ : J := Classical.choice inferInstance
    refine Submodule.mem_span_singleton.mpr ⟨-p.2 j₀, ?_⟩
    apply Prod.ext
    · funext i
      simp [bipartiteGaugeVector]
      linarith [hedge i j₀]
    · funext j
      let i₀ : I := Classical.choice inferInstance
      simp [bipartiteGaugeVector]
      linarith [hedge i₀ j, hedge i₀ j₀]
  · intro hp
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hp
    ext ij
    simp [bipartiteEdgeSumLinearMap, bipartiteGaugeVector]

def bipartiteQuotientEdgeSum [Nonempty I] [Nonempty J] :
    (BipartitePotentialSpace I J ⧸ bipartiteGaugeSubspace (I := I) (J := J)) →ₗ[ℝ]
      (I × J → ℝ) :=
  (bipartiteGaugeSubspace (I := I) (J := J)).liftQ
    (bipartiteEdgeSumLinearMap (I := I) (J := J))
    (by rw [← bipartiteEdgeSumLinearMap_ker])

omit [Fintype I] [Fintype J] in
theorem bipartiteQuotientEdgeSum_injective [Nonempty I] [Nonempty J] :
    Function.Injective (bipartiteQuotientEdgeSum (I := I) (J := J)) := by
  apply LinearMap.ker_eq_bot.mp
  ext q
  constructor
  · intro hq
    induction q using Submodule.Quotient.induction_on with
    | _ p =>
        change bipartiteQuotientEdgeSum (Submodule.Quotient.mk p) = 0 at hq
        change (Submodule.Quotient.mk p :
          BipartitePotentialSpace I J ⧸ bipartiteGaugeSubspace) = 0
        rw [Submodule.Quotient.mk_eq_zero]
        rw [← bipartiteEdgeSumLinearMap_ker]
        change bipartiteEdgeSumLinearMap p = 0 at hq
        exact hq
  · intro hq
    subst q
    simp

def bipartiteEdgeEnergy (w : I → J → ℝ) (z : I × J → ℝ) : ℝ :=
  ∑ i, ∑ j, w i j * z (i, j) ^ 2

theorem continuous_bipartiteEdgeEnergy (w : I → J → ℝ) :
    Continuous (bipartiteEdgeEnergy w) := by
  unfold bipartiteEdgeEnergy
  fun_prop

theorem bipartiteEdgeEnergy_nonneg
    (w : I → J → ℝ) (hw : ∀ i j, 0 ≤ w i j) (z : I × J → ℝ) :
    0 ≤ bipartiteEdgeEnergy w z := by
  unfold bipartiteEdgeEnergy
  exact Finset.sum_nonneg fun i _ ↦
    Finset.sum_nonneg fun j _ ↦ mul_nonneg (hw i j) (sq_nonneg _)

theorem bipartiteEdgeEnergy_eq_zero_iff
    (w : I → J → ℝ) (hw : ∀ i j, 0 < w i j) (z : I × J → ℝ) :
    bipartiteEdgeEnergy w z = 0 ↔ z = 0 := by
  classical
  constructor
  · intro hzero
    funext ij
    have hrow : ∑ j, w ij.1 j * z (ij.1, j) ^ 2 = 0 := by
      apply (Finset.sum_eq_zero_iff_of_nonneg (fun i _ ↦
        Finset.sum_nonneg fun j _ ↦ mul_nonneg (hw i j).le (sq_nonneg _))).mp hzero
        ij.1 (Finset.mem_univ ij.1)
    have hterm : w ij.1 ij.2 * z ij ^ 2 = 0 := by
      apply (Finset.sum_eq_zero_iff_of_nonneg (fun j _ ↦
        mul_nonneg (hw ij.1 j).le (sq_nonneg _))).mp hrow ij.2 (Finset.mem_univ ij.2)
    exact sq_eq_zero_iff.mp ((mul_eq_zero.mp hterm).resolve_left (hw ij.1 ij.2).ne')
  · rintro rfl
    simp [bipartiteEdgeEnergy]

theorem isCompact_bipartiteEdgeEnergy_sublevel
    (w : I → J → ℝ) (hw : ∀ i j, 0 < w i j) (C : ℝ) :
    IsCompact {z : I × J → ℝ | bipartiteEdgeEnergy w z ≤ C} := by
  classical
  let radius : I × J → ℝ := fun ij ↦ Real.sqrt (max C 0 / w ij.1 ij.2)
  have hbox : IsCompact {z : I × J → ℝ | ∀ ij, z ij ∈ Set.Icc (-radius ij) (radius ij)} :=
    isCompact_pi_infinite fun ij ↦ isCompact_Icc
  apply IsCompact.of_isClosed_subset hbox
  · exact isClosed_le (continuous_bipartiteEdgeEnergy w) continuous_const
  · intro z hz ij
    have htermrow : w ij.1 ij.2 * z ij ^ 2 ≤
        ∑ j, w ij.1 j * z (ij.1, j) ^ 2 :=
      Finset.single_le_sum
        (f := fun j ↦ w ij.1 j * z (ij.1, j) ^ 2)
        (fun j _ ↦ mul_nonneg (hw ij.1 j).le (sq_nonneg _)) (Finset.mem_univ ij.2)
    have hrow : (∑ j, w ij.1 j * z (ij.1, j) ^ 2) ≤ bipartiteEdgeEnergy w z := by
      unfold bipartiteEdgeEnergy
      exact Finset.single_le_sum
        (f := fun i ↦ ∑ j, w i j * z (i, j) ^ 2)
        (fun i _ ↦ Finset.sum_nonneg fun j _ ↦ mul_nonneg (hw i j).le (sq_nonneg _))
        (Finset.mem_univ ij.1)
    have hweighted : w ij.1 ij.2 * z ij ^ 2 ≤ max C 0 :=
      htermrow.trans (hrow.trans (hz.trans (le_max_left C 0)))
    have hsquare : z ij ^ 2 ≤ max C 0 / w ij.1 ij.2 :=
      (le_div_iff₀ (hw ij.1 ij.2)).2 (by simpa [mul_comm] using hweighted)
    have habs : |z ij| ≤ radius ij := by
      exact Real.abs_le_sqrt hsquare
    exact ⟨neg_le_of_abs_le habs, le_of_abs_le habs⟩

def bipartiteQuotientFormationEnergy [Nonempty I] [Nonempty J]
    (w : I → J → ℝ)
    (q : BipartitePotentialSpace I J ⧸ bipartiteGaugeSubspace (I := I) (J := J)) : ℝ :=
  bipartiteEdgeEnergy w (bipartiteQuotientEdgeSum q)

theorem bipartiteQuotientFormationEnergy_mk [Nonempty I] [Nonempty J]
    (w : I → J → ℝ) (x : I → ℝ) (y : J → ℝ) :
    bipartiteQuotientFormationEnergy w
      (Submodule.Quotient.mk (x, y) :
        BipartitePotentialSpace I J ⧸ bipartiteGaugeSubspace) =
      bipartiteFormationEnergy w x y := by
  rfl

theorem bipartiteQuotientFormationEnergy_nonneg [Nonempty I] [Nonempty J]
    (w : I → J → ℝ) (hw : ∀ i j, 0 ≤ w i j)
    (q : BipartitePotentialSpace I J ⧸ bipartiteGaugeSubspace (I := I) (J := J)) :
    0 ≤ bipartiteQuotientFormationEnergy w q :=
  bipartiteEdgeEnergy_nonneg w hw _

theorem bipartiteQuotientFormationEnergy_eq_zero_iff [Nonempty I] [Nonempty J]
    (w : I → J → ℝ) (hw : ∀ i j, 0 < w i j)
    (q : BipartitePotentialSpace I J ⧸ bipartiteGaugeSubspace (I := I) (J := J)) :
    bipartiteQuotientFormationEnergy w q = 0 ↔ q = 0 := by
  rw [bipartiteQuotientFormationEnergy, bipartiteEdgeEnergy_eq_zero_iff w hw]
  constructor
  · intro hq
    apply bipartiteQuotientEdgeSum_injective
    simpa using hq
  · rintro rfl
    simp

theorem isCompact_bipartiteQuotientFormationEnergy_sublevel
    [Nonempty I] [Nonempty J]
    (w : I → J → ℝ) (hw : ∀ i j, 0 < w i j) (C : ℝ) :
    IsCompact {q : BipartitePotentialSpace I J ⧸ bipartiteGaugeSubspace (I := I) (J := J) |
      bipartiteQuotientFormationEnergy w q ≤ C} := by
  classical
  letI : IsClosed (bipartiteGaugeSubspace (I := I) (J := J) :
      Set (BipartitePotentialSpace I J)) :=
    Submodule.closed_of_finiteDimensional _
  have hproper : IsProperMap (bipartiteQuotientEdgeSum (I := I) (J := J)) :=
    (LinearMap.isClosedEmbedding_of_injective
      (LinearMap.ker_eq_bot.mpr bipartiteQuotientEdgeSum_injective)).isProperMap
  exact hproper.isCompact_preimage (isCompact_bipartiteEdgeEnergy_sublevel w hw C)

end GaugeQuotient

end

end GaloisForLFunctions.HTGeometry
