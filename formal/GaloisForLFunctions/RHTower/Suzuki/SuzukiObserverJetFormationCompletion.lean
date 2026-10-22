import GaloisForLFunctions.RHTower.Suzuki.SuzukiObserverJetFormation
import GaloisForLFunctions.HTGeometry.LpSingleSpanDense

/-!
# Sharp observer-jet second-formation completion

Affine observer gauges are classified by discrete curvature. The finite `J₂` chart completes
isometrically as `ℓ¹(Fin 2 ⊕ ℕ)`, its response extends exactly for bounded curvature, and the
operator norm is the maximum of value, slope, and curvature supremum. For the literal completed
Suzuki clock, value and first difference are unbounded while curvature is uniformly bounded.
-/

open scoped BigOperators ENNReal

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- Affine observer gauge. -/
def observerJetAffineGauge (a b : ℝ) (k : ℕ) : ℝ := a + b * k

theorem observerJetCurvature_add_affineGauge
    (rate : ℕ → ℝ) (a b : ℝ) (j : ℕ) :
    observerJetCurvature (rate + observerJetAffineGauge a b) j =
      observerJetCurvature rate j := by
  simp [observerJetCurvature, observerJetAffineGauge]
  ring

theorem observerJetResponse_add_affineGauge
    (q rate : ℕ → ℝ) (N : ℕ) (a b : ℝ) :
    (∑ k ∈ Finset.range (N + 1),
        q k * (rate + observerJetAffineGauge a b) k) -
      (∑ k ∈ Finset.range (N + 1), q k * rate k) =
        a * observerJetMass q N + b * observerJetDrift q N := by
  simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib]
  rw [add_sub_cancel_left]
  unfold observerJetAffineGauge observerJetMass observerJetDrift
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro k _
  ring

theorem observerJetResponse_add_affineGauge_of_moment_free
    (q rate : ℕ → ℝ) (N : ℕ) (a b : ℝ)
    (hmass : observerJetMass q N = 0) (hdrift : observerJetDrift q N = 0) :
    (∑ k ∈ Finset.range (N + 1),
        q k * (rate + observerJetAffineGauge a b) k) =
      ∑ k ∈ Finset.range (N + 1), q k * rate k := by
  have h := observerJetResponse_add_affineGauge q rate N a b
  norm_num [hmass, hdrift] at h
  exact sub_eq_zero.mp h

/-- Curvature is the complete invariant of an observer modulo affine gauges. -/
theorem observerJetCurvature_eq_iff_exists_affineGauge
    (rate₁ rate₂ : ℕ → ℝ) :
    (∀ j, observerJetCurvature rate₂ j = observerJetCurvature rate₁ j) ↔
      ∃ a b : ℝ, rate₂ = rate₁ + observerJetAffineGauge a b := by
  constructor
  · intro hcurv
    let d : ℕ → ℝ := fun k => rate₂ k - rate₁ k
    let a : ℝ := d 0
    let b : ℝ := d 1 - d 0
    have hdcurv : ∀ j, d (j + 2) - 2 * d (j + 1) + d j = 0 := by
      intro j
      have h := hcurv j
      unfold observerJetCurvature at h
      dsimp only [d]
      linarith
    have hform : ∀ k, d k = a + b * k := by
      intro k
      induction k using Nat.twoStepInduction with
      | zero => simp [a]
      | one => simp [a, b]
      | more k hk hk1 =>
          have hrec := hdcurv k
          rw [hk, hk1] at hrec
          push_cast at hrec ⊢
          nlinarith
    refine ⟨a, b, funext fun k => ?_⟩
    have hk := hform k
    change rate₂ k = rate₁ k + observerJetAffineGauge a b k
    unfold observerJetAffineGauge
    dsimp only [d] at hk
    linarith
  · rintro ⟨a, b, rfl⟩ j
    exact observerJetCurvature_add_affineGauge rate₁ a b j

/-- Unit quadrupole `δ_j - 2δ_{j+1} + δ_{j+2}`. -/
def observerJetQuadrupole (j k : ℕ) : ℝ :=
  (if k = j then 1 else 0) - 2 * (if k = j + 1 then 1 else 0) +
    (if k = j + 2 then 1 else 0)

theorem observerJetQuadrupole_response (rate : ℕ → ℝ) (j : ℕ) :
    (∑ k ∈ Finset.range (j + 3), observerJetQuadrupole j k * rate k) =
      observerJetCurvature rate j := by
  simp only [observerJetQuadrupole, sub_mul, add_mul, Finset.sum_add_distrib,
    Finset.sum_sub_distrib]
  simp
  unfold observerJetCurvature
  ring

theorem observerJetQuadrupole_mass_zero (j : ℕ) :
    observerJetMass (observerJetQuadrupole j) (j + 2) = 0 := by
  simp only [observerJetMass, observerJetQuadrupole, Finset.sum_add_distrib,
    Finset.sum_sub_distrib]
  simp
  norm_num

theorem observerJetQuadrupole_drift_zero (j : ℕ) :
    observerJetDrift (observerJetQuadrupole j) (j + 2) = 0 := by
  simp only [observerJetDrift, observerJetQuadrupole, mul_sub, mul_add,
    Finset.sum_add_distrib, Finset.sum_sub_distrib]
  simp
  ring

/-- Mass, drift, and second history determine every charge coordinate through the cutoff. -/
theorem observerJetSecondCoordinates_injective_on_range
    (q₁ q₂ : ℕ → ℝ) (N : ℕ) (hN : 1 ≤ N)
    (hmass : observerJetMass q₁ N = observerJetMass q₂ N)
    (hdrift : observerJetDrift q₁ N = observerJetDrift q₂ N)
    (hhistory : ∀ j, j ≤ N →
      observerJetSecondHistory (observerJetResidual q₁ N) j =
        observerJetSecondHistory (observerJetResidual q₂ N) j) :
    ∀ k, k ≤ N → q₁ k = q₂ k := by
  intro k hk
  rcases k with _ | k
  · have h₁ := observerJetResidual_reconstruct_zero q₁ N
    have h₂ := observerJetResidual_reconstruct_zero q₂ N
    rw [hmass, hdrift, hhistory 0 (by omega)] at h₁
    linarith
  · rcases k with _ | j
    · have h₁ := observerJetResidual_reconstruct_one q₁ N
      have h₂ := observerJetResidual_reconstruct_one q₂ N
      rw [hdrift, hhistory 1 hN, hhistory 0 (by omega)] at h₁
      linarith
    · have h₁ := observerJetResidual_reconstruct_succ_succ q₁ N j
      have h₂ := observerJetResidual_reconstruct_succ_succ q₂ N j
      rw [hhistory (j + 2) hk, hhistory (j + 1) (by omega),
        hhistory j (by omega)] at h₁
      linarith

/-- Algebraic `mass ⊕ drift ⊕ c₀₀` chart carrying the second-formation sum norm. -/
abbrev ObserverJetSecondCoordinates := ℝ × ℝ × (ℕ →₀ ℝ)

def observerJetSecondCoordinateAction (x : ObserverJetSecondCoordinates) : ℝ :=
  |x.1| + |x.2.1| + x.2.2.sum fun _ A => |A|

def observerJetSecondCoordinateResponse
    (rate : ℕ → ℝ) (x : ObserverJetSecondCoordinates) : ℝ :=
  x.1 * rate 0 + x.2.1 * (rate 1 - rate 0) +
    x.2.2.sum fun j A => A * observerJetCurvature rate j

theorem observerJetSecondCoordinateAction_nonneg
    (x : ObserverJetSecondCoordinates) :
    0 ≤ observerJetSecondCoordinateAction x := by
  unfold observerJetSecondCoordinateAction
  exact add_nonneg (add_nonneg (abs_nonneg _) (abs_nonneg _))
    (Finsupp.sum_nonneg fun _ _ => abs_nonneg _)

private theorem abs_observerJetHistoryResponse_le
    (rate : ℕ → ℝ) {C : ℝ} (_hC : 0 ≤ C)
    (hcurv : ∀ j, |observerJetCurvature rate j| ≤ C)
    (A : ℕ →₀ ℝ) :
    |A.sum fun j Aj => Aj * observerJetCurvature rate j| ≤
      C * A.sum fun _ Aj => |Aj| := by
  classical
  change |∑ j ∈ A.support, A j * observerJetCurvature rate j| ≤
    C * ∑ j ∈ A.support, |A j|
  calc
    |∑ j ∈ A.support, A j * observerJetCurvature rate j| ≤
        ∑ j ∈ A.support, |A j * observerJetCurvature rate j| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ j ∈ A.support, C * |A j| := by
      apply Finset.sum_le_sum
      intro j _
      rw [abs_mul, mul_comm]
      exact mul_le_mul_of_nonneg_right (hcurv j) (abs_nonneg _)
    _ = C * ∑ j ∈ A.support, |A j| := by rw [Finset.mul_sum]

/-- Sharp coefficientwise norm classification for the second-formation response on `c₀₀`. -/
theorem observerJetSecondCoordinateResponse_bound_iff
    (rate : ℕ → ℝ) {C : ℝ} (hC : 0 ≤ C) :
    (∀ x : ObserverJetSecondCoordinates,
      |observerJetSecondCoordinateResponse rate x| ≤
        C * observerJetSecondCoordinateAction x) ↔
      |rate 0| ≤ C ∧ |rate 1 - rate 0| ≤ C ∧
        ∀ j, |observerJetCurvature rate j| ≤ C := by
  constructor
  · intro h
    have hmass := h ((1, 0, 0) : ObserverJetSecondCoordinates)
    have hdrift := h ((0, 1, 0) : ObserverJetSecondCoordinates)
    refine ⟨?_, ?_, fun j => ?_⟩
    · simpa [observerJetSecondCoordinateResponse,
        observerJetSecondCoordinateAction] using hmass
    · simpa [observerJetSecondCoordinateResponse,
        observerJetSecondCoordinateAction] using hdrift
    · have hj := h ((0, 0, Finsupp.single j 1) : ObserverJetSecondCoordinates)
      simpa [observerJetSecondCoordinateResponse,
        observerJetSecondCoordinateAction] using hj
  · rintro ⟨hmass, hdrift, hcurv⟩ x
    have hhist := abs_observerJetHistoryResponse_le rate hC hcurv x.2.2
    unfold observerJetSecondCoordinateResponse observerJetSecondCoordinateAction
    calc
      |x.1 * rate 0 + x.2.1 * (rate 1 - rate 0) +
          x.2.2.sum fun j A => A * observerJetCurvature rate j| ≤
        |x.1 * rate 0| + |x.2.1 * (rate 1 - rate 0)| +
          |x.2.2.sum fun j A => A * observerJetCurvature rate j| := by
        exact (abs_add_le _ _).trans
          (add_le_add (abs_add_le _ _) (le_refl _))
      _ ≤ C * |x.1| + C * |x.2.1| +
          C * x.2.2.sum fun _ A => |A| := by
        rw [abs_mul, abs_mul]
        exact add_le_add (add_le_add
          (by nlinarith [mul_le_mul_of_nonneg_left hmass (abs_nonneg x.1)])
          (by nlinarith [mul_le_mul_of_nonneg_left hdrift (abs_nonneg x.2.1)])) hhist
      _ = C * (|x.1| + |x.2.1| + x.2.2.sum fun _ A => |A|) := by ring

def ObserverJetCurvatureUniformlyBounded (rate : ℕ → ℝ) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ j, |observerJetCurvature rate j| ≤ C

/-- Sharp properness classification on the dense second-formation coordinate chart. -/
theorem observerJetSecondCoordinateResponse_bounded_iff
    (rate : ℕ → ℝ) :
    (∃ C : ℝ, 0 ≤ C ∧ ∀ x : ObserverJetSecondCoordinates,
      |observerJetSecondCoordinateResponse rate x| ≤
        C * observerJetSecondCoordinateAction x) ↔
      ObserverJetCurvatureUniformlyBounded rate := by
  constructor
  · rintro ⟨C, hC, hbound⟩
    exact ⟨C, hC,
      (observerJetSecondCoordinateResponse_bound_iff rate hC).mp hbound |>.2.2⟩
  · rintro ⟨K, hK, hcurv⟩
    let C := max |rate 0| (max |rate 1 - rate 0| K)
    have hC : 0 ≤ C := le_trans (abs_nonneg _) (le_max_left _ _)
    refine ⟨C, hC,
      (observerJetSecondCoordinateResponse_bound_iff rate hC).mpr ?_⟩
    exact ⟨le_max_left _ _, (le_max_left _ _).trans (le_max_right _ _),
      fun j => (hcurv j).trans ((le_max_right _ _).trans (le_max_right _ _))⟩

/-- Index set `mass ⊕ drift ⊕ second-history`. -/
abbrev ObserverJetSecondFormationIndex := Fin 2 ⊕ ℕ

/-- Canonical sum-norm completion `ℓ¹(Fin 2 ⊕ ℕ) ≅ ℝ² ⊕₁ ℓ¹`. -/
abbrev ObserverJetSecondFormationCompletion :=
  lp (fun _ : ObserverJetSecondFormationIndex => ℝ) 1

def observerJetSecondCoefficient
    (rate : ℕ → ℝ) : ObserverJetSecondFormationIndex → ℝ
  | Sum.inl i => if i = 0 then rate 0 else rate 1 - rate 0
  | Sum.inr j => observerJetCurvature rate j

@[simp] theorem observerJetSecondCoefficient_mass (rate : ℕ → ℝ) :
    observerJetSecondCoefficient rate (Sum.inl (0 : Fin 2)) = rate 0 := by
  simp [observerJetSecondCoefficient]

@[simp] theorem observerJetSecondCoefficient_drift (rate : ℕ → ℝ) :
    observerJetSecondCoefficient rate (Sum.inl (1 : Fin 2)) = rate 1 - rate 0 := by
  simp [observerJetSecondCoefficient]

@[simp] theorem observerJetSecondCoefficient_history (rate : ℕ → ℝ) (j : ℕ) :
    observerJetSecondCoefficient rate (Sum.inr j) = observerJetCurvature rate j := rfl

theorem observerJetSecondCoefficient_bound
    (rate : ℕ → ℝ) {K : ℝ}
    (hcurv : ∀ j, |observerJetCurvature rate j| ≤ K)
    (i : ObserverJetSecondFormationIndex) :
    |observerJetSecondCoefficient rate i| ≤
      max |rate 0| (max |rate 1 - rate 0| K) := by
  rcases i with i | j
  · fin_cases i
    · exact le_max_left _ _
    · exact (le_max_left _ _).trans (le_max_right _ _)
  · exact (hcurv j).trans ((le_max_right _ _).trans (le_max_right _ _))

theorem observerJetCompletion_hasSum_abs
    (x : ObserverJetSecondFormationCompletion) :
    HasSum (fun i => |(x : ObserverJetSecondFormationIndex → ℝ) i|) ‖x‖ := by
  have h := lp.hasSum_norm
    (E := fun _ : ObserverJetSecondFormationIndex => ℝ) (p := 1) (by norm_num) x
  simpa only [ENNReal.toReal_one, Real.rpow_one, Real.norm_eq_abs] using h

theorem observerJetCompletion_summable_abs
    (x : ObserverJetSecondFormationCompletion) :
    Summable fun i => |(x : ObserverJetSecondFormationIndex → ℝ) i| :=
  (observerJetCompletion_hasSum_abs x).summable

theorem observerJetCompletionResponse_summable
    (rate : ℕ → ℝ) {K : ℝ}
    (hcurv : ∀ j, |observerJetCurvature rate j| ≤ K)
    (x : ObserverJetSecondFormationCompletion) :
    Summable fun i =>
      (x : ObserverJetSecondFormationIndex → ℝ) i * observerJetSecondCoefficient rate i := by
  let C := max |rate 0| (max |rate 1 - rate 0| K)
  refine Summable.of_norm_bounded
    ((observerJetCompletion_summable_abs x).mul_right C) fun i => ?_
  rw [Real.norm_eq_abs, abs_mul]
  exact mul_le_mul_of_nonneg_left
    (observerJetSecondCoefficient_bound rate hcurv i) (abs_nonneg _)

def observerJetCompletionResponse
    (rate : ℕ → ℝ) (x : ObserverJetSecondFormationCompletion) : ℝ :=
  ∑' i, (x : ObserverJetSecondFormationIndex → ℝ) i *
    observerJetSecondCoefficient rate i

theorem abs_observerJetCompletionResponse_le
    (rate : ℕ → ℝ) {K : ℝ}
    (hcurv : ∀ j, |observerJetCurvature rate j| ≤ K)
    (x : ObserverJetSecondFormationCompletion) :
    |observerJetCompletionResponse rate x| ≤
      max |rate 0| (max |rate 1 - rate 0| K) * ‖x‖ := by
  let C := max |rate 0| (max |rate 1 - rate 0| K)
  have hs := observerJetCompletionResponse_summable rate hcurv x
  have hmajor := (observerJetCompletion_summable_abs x).mul_right C
  unfold observerJetCompletionResponse
  calc
    |∑' i, (x : ObserverJetSecondFormationIndex → ℝ) i *
        observerJetSecondCoefficient rate i| ≤
        ∑' i, |(x : ObserverJetSecondFormationIndex → ℝ) i *
          observerJetSecondCoefficient rate i| := by
      simpa only [Real.norm_eq_abs] using norm_tsum_le_tsum_norm hs.norm
    _ ≤ ∑' i, |(x : ObserverJetSecondFormationIndex → ℝ) i| * C := by
      exact Summable.tsum_le_tsum
        (fun i => by
          rw [abs_mul]
          exact mul_le_mul_of_nonneg_left
            (observerJetSecondCoefficient_bound rate hcurv i) (abs_nonneg _))
        hs.norm hmajor
    _ = C * ∑' i, |(x : ObserverJetSecondFormationIndex → ℝ) i| := by
      rw [tsum_mul_right]
      ring
    _ = C * ‖x‖ := by rw [(observerJetCompletion_hasSum_abs x).tsum_eq]

noncomputable def observerJetCompletionResponseLinearMap
    (rate : ℕ → ℝ) {K : ℝ}
    (hcurv : ∀ j, |observerJetCurvature rate j| ≤ K) :
    ObserverJetSecondFormationCompletion →ₗ[ℝ] ℝ where
  toFun := observerJetCompletionResponse rate
  map_add' := fun x y => by
    unfold observerJetCompletionResponse
    rw [← Summable.tsum_add
      (observerJetCompletionResponse_summable rate hcurv x)
      (observerJetCompletionResponse_summable rate hcurv y)]
    apply tsum_congr
    intro i
    rw [lp.coeFn_add]
    simp only [Pi.add_apply]
    ring
  map_smul' := fun c x => by
    unfold observerJetCompletionResponse
    simp only [RingHom.id_apply, smul_eq_mul, ← tsum_mul_left]
    apply tsum_congr
    intro i
    rw [lp.coeFn_smul]
    simp only [Pi.smul_apply, smul_eq_mul]
    ring

noncomputable def observerJetCompletionResponseCLM
    (rate : ℕ → ℝ) {K : ℝ}
    (hcurv : ∀ j, |observerJetCurvature rate j| ≤ K) :
    ObserverJetSecondFormationCompletion →L[ℝ] ℝ :=
  LinearMap.mkContinuous
    (observerJetCompletionResponseLinearMap rate hcurv)
    (max |rate 0| (max |rate 1 - rate 0| K)) fun x => by
      rw [Real.norm_eq_abs]
      exact abs_observerJetCompletionResponse_le rate hcurv x

@[simp] theorem observerJetCompletionResponseCLM_apply
    (rate : ℕ → ℝ) {K : ℝ}
    (hcurv : ∀ j, |observerJetCurvature rate j| ≤ K)
    (x : ObserverJetSecondFormationCompletion) :
    observerJetCompletionResponseCLM rate hcurv x =
      observerJetCompletionResponse rate x := rfl

theorem observerJetCompletionResponse_single
    (rate : ℕ → ℝ) (i : ObserverJetSecondFormationIndex) :
    observerJetCompletionResponse rate
        (lp.single (E := fun _ : ObserverJetSecondFormationIndex => ℝ) 1 i 1) =
      observerJetSecondCoefficient rate i := by
  classical
  unfold observerJetCompletionResponse
  rw [tsum_eq_single i]
  · simp [lp.single_apply]
  · intro i' hi
    simp [lp.single_apply, hi]

/-- The finite coordinate span is dense in the exact `F²` completion. -/
theorem observerJetSecondFormationFiniteChart_dense :
    (Submodule.span ℝ (Set.range fun i : ObserverJetSecondFormationIndex =>
      lp.single (E := fun _ : ObserverJetSecondFormationIndex => ℝ) 1 i (1 : ℝ))).topologicalClosure
        = ⊤ := by
  exact _root_.HTGeometry.span_lp_single_dense ObserverJetSecondFormationIndex

/-- A continuous response on the completion is uniquely determined by its finite chart values. -/
theorem observerJetSecondFormationExtension_unique
    (rate : ℕ → ℝ) (L₁ L₂ : ObserverJetSecondFormationCompletion →L[ℝ] ℝ)
    (h₁ : ∀ i : ObserverJetSecondFormationIndex,
      L₁ (lp.single (E := fun _ : ObserverJetSecondFormationIndex => ℝ) 1 i 1) =
        observerJetSecondCoefficient rate i)
    (h₂ : ∀ i : ObserverJetSecondFormationIndex,
      L₂ (lp.single (E := fun _ : ObserverJetSecondFormationIndex => ℝ) 1 i 1) =
        observerJetSecondCoefficient rate i) :
    L₁ = L₂ := by
  apply ContinuousLinearMap.ext_on
  · rw [Submodule.dense_iff_topologicalClosure_eq_top]
    exact observerJetSecondFormationFiniteChart_dense
  · rintro _ ⟨i, rfl⟩
    rw [h₁ i, h₂ i]

/-- A clock response continuously extends from the finite `J₂` chart. -/
def ObserverJetSecondFormationExtends (rate : ℕ → ℝ) : Prop :=
  ∃ L : ObserverJetSecondFormationCompletion →L[ℝ] ℝ,
    ∀ i : ObserverJetSecondFormationIndex,
      L (lp.single (E := fun _ : ObserverJetSecondFormationIndex => ℝ) 1 i 1) =
        observerJetSecondCoefficient rate i

/-- Exact second-order properness: extension occurs iff curvature is uniformly bounded. -/
theorem observerJetSecondFormationExtends_iff
    (rate : ℕ → ℝ) :
    ObserverJetSecondFormationExtends rate ↔
      ObserverJetCurvatureUniformlyBounded rate := by
  constructor
  · rintro ⟨L, hL⟩
    refine ⟨‖L‖, norm_nonneg _, fun j => ?_⟩
    have h := L.le_opNorm
      (lp.single (E := fun _ : ObserverJetSecondFormationIndex => ℝ) 1 (Sum.inr j) 1)
    rw [hL, observerJetSecondCoefficient_history, lp.norm_single (by norm_num), norm_one,
      mul_one, Real.norm_eq_abs] at h
    exact h
  · rintro ⟨K, _hK, hcurv⟩
    refine ⟨observerJetCompletionResponseCLM rate hcurv, fun i => ?_⟩
    rw [observerJetCompletionResponseCLM_apply,
      observerJetCompletionResponse_single]

noncomputable def observerJetCurvatureSup (rate : ℕ → ℝ) : ℝ :=
  sSup (Set.range fun j => |observerJetCurvature rate j|)

theorem observerJetCurvatureRange_bddAbove
    (rate : ℕ → ℝ) {K : ℝ}
    (hcurv : ∀ j, |observerJetCurvature rate j| ≤ K) :
    BddAbove (Set.range fun j => |observerJetCurvature rate j|) := by
  exact ⟨K, by rintro _ ⟨j, rfl⟩; exact hcurv j⟩

theorem abs_observerJetCurvature_le_sup
    (rate : ℕ → ℝ) {K : ℝ}
    (hcurv : ∀ j, |observerJetCurvature rate j| ≤ K) (j : ℕ) :
    |observerJetCurvature rate j| ≤ observerJetCurvatureSup rate := by
  exact le_csSup (observerJetCurvatureRange_bddAbove rate hcurv) ⟨j, rfl⟩

theorem observerJetCurvatureSup_le
    (rate : ℕ → ℝ) {K : ℝ}
    (hcurv : ∀ j, |observerJetCurvature rate j| ≤ K) :
    observerJetCurvatureSup rate ≤ K := by
  apply csSup_le
  · exact ⟨|observerJetCurvature rate 0|, ⟨0, rfl⟩⟩
  · rintro _ ⟨j, rfl⟩
    exact hcurv j

/-- Exact dual norm: maximum of value, slope, and curvature supremum. -/
theorem norm_observerJetCompletionResponseCLM
    (rate : ℕ → ℝ) {K : ℝ}
    (hcurv : ∀ j, |observerJetCurvature rate j| ≤ K) :
    let S := observerJetCurvatureSup rate
    ‖observerJetCompletionResponseCLM rate
        (abs_observerJetCurvature_le_sup rate hcurv)‖ =
      max |rate 0| (max |rate 1 - rate 0| S) := by
  dsimp only
  let S := observerJetCurvatureSup rate
  have hcurvS : ∀ j, |observerJetCurvature rate j| ≤ S :=
    abs_observerJetCurvature_le_sup rate hcurv
  let L := observerJetCompletionResponseCLM rate hcurvS
  let C := max |rate 0| (max |rate 1 - rate 0| S)
  change ‖L‖ = C
  apply le_antisymm
  · apply L.opNorm_le_bound
    · exact le_trans (abs_nonneg _) (le_max_left _ _)
    · intro x
      rw [Real.norm_eq_abs]
      exact abs_observerJetCompletionResponse_le rate hcurvS x
  · apply max_le
    · have h := L.le_opNorm
        (lp.single (E := fun _ : ObserverJetSecondFormationIndex => ℝ) 1
          (Sum.inl (0 : Fin 2)) 1)
      simpa [L, observerJetCompletionResponse_single] using h
    · apply max_le
      · have h := L.le_opNorm
          (lp.single (E := fun _ : ObserverJetSecondFormationIndex => ℝ) 1
            (Sum.inl (1 : Fin 2)) 1)
        simpa [L, observerJetCompletionResponse_single] using h
      · apply csSup_le
        · exact ⟨|observerJetCurvature rate 0|, ⟨0, rfl⟩⟩
        · rintro _ ⟨j, rfl⟩
          have h := L.le_opNorm
            (lp.single (E := fun _ : ObserverJetSecondFormationIndex => ℝ) 1
              (Sum.inr j) 1)
          simpa [L, observerJetCompletionResponse_single] using h

/-- Closed certificate for affine classification and sharp second-formation properness. -/
theorem observerJetSecondFormationProperness_unconditional :
    (∀ rate : ℕ → ℝ,
      ObserverJetSecondFormationExtends rate ↔
        ObserverJetCurvatureUniformlyBounded rate) ∧
    (∀ rate₁ rate₂ : ℕ → ℝ,
      (∀ j, observerJetCurvature rate₂ j = observerJetCurvature rate₁ j) ↔
        ∃ a b : ℝ, rate₂ = rate₁ + observerJetAffineGauge a b) ∧
    (∀ (rate : ℕ → ℝ) (C : ℝ), 0 ≤ C →
      ((∀ x : ObserverJetSecondCoordinates,
        |observerJetSecondCoordinateResponse rate x| ≤
          C * observerJetSecondCoordinateAction x) ↔
        |rate 0| ≤ C ∧ |rate 1 - rate 0| ≤ C ∧
          ∀ j, |observerJetCurvature rate j| ≤ C)) ∧
    (∀ (rate : ℕ → ℝ) (K : ℝ)
      (hcurv : ∀ j, |observerJetCurvature rate j| ≤ K),
      let S := observerJetCurvatureSup rate
      ‖observerJetCompletionResponseCLM rate
          (abs_observerJetCurvature_le_sup rate hcurv)‖ =
        max |rate 0| (max |rate 1 - rate 0| S)) := by
  refine ⟨observerJetSecondFormationExtends_iff,
    observerJetCurvature_eq_iff_exists_affineGauge, ?_, ?_⟩
  · intro rate C hC
    exact observerJetSecondCoordinateResponse_bound_iff rate hC
  · intro rate K hcurv
    exact norm_observerJetCompletionResponseCLM rate hcurv

end

end GaloisForLFunctions.HTGeometry

namespace GaloisForLFunctions.HTGeometry

noncomputable section

theorem observerJetClockReal_lower {x : ℝ} (hx : 0 ≤ x) :
    x * Real.sqrt (x + 1) / 2 ≤ observerJetClockReal x := by
  have hx1 : 0 ≤ x + 1 := by linarith
  have hs0 : 0 ≤ Real.sqrt x := Real.sqrt_nonneg _
  have hs1 : 0 ≤ Real.sqrt (x + 1) := Real.sqrt_nonneg _
  have hsle : Real.sqrt x ≤ Real.sqrt (x + 1) := Real.sqrt_le_sqrt (by linarith)
  have hgap0 : 0 ≤ observerJetSqrtGap x := (observerJetSqrtGap_pos hx).le
  have hgap := observerJetSqrtGap_mul_sum hx
  have hprod : 1 ≤ observerJetSqrtGap x * (2 * Real.sqrt (x + 1)) := by
    calc
      1 = observerJetSqrtGap x *
          (Real.sqrt (x + 1) + Real.sqrt x) := hgap.symm
      _ ≤ observerJetSqrtGap x * (2 * Real.sqrt (x + 1)) := by
        gcongr
        linarith
  have hsquare : Real.sqrt (x + 1) ^ 2 = x + 1 := Real.sq_sqrt hx1
  have hhalf : (1 : ℝ) / 2 ≤
      observerJetSqrtGap x * Real.sqrt (x + 1) := by nlinarith
  have hmul := mul_le_mul_of_nonneg_left hhalf (mul_nonneg hx hs1)
  calc
    x * Real.sqrt (x + 1) / 2 =
        (x * Real.sqrt (x + 1)) * ((1 : ℝ) / 2) := by ring
    _ ≤ (x * Real.sqrt (x + 1)) *
        (observerJetSqrtGap x * Real.sqrt (x + 1)) := hmul
    _ = x * (Real.sqrt (x + 1) ^ 2) * observerJetSqrtGap x := by ring
    _ = x * (x + 1) * observerJetSqrtGap x := by rw [hsquare]
    _ = observerJetClockReal x := rfl

theorem observerJetClockReal_upper {x : ℝ} (hx : 0 < x) :
    observerJetClockReal x ≤ (x + 1) * Real.sqrt x / 2 := by
  have hx0 : 0 ≤ x := hx.le
  have hx1 : 0 ≤ x + 1 := by linarith
  have hs0 : 0 ≤ Real.sqrt x := Real.sqrt_nonneg _
  have hs1 : 0 ≤ Real.sqrt (x + 1) := Real.sqrt_nonneg _
  have hsle : Real.sqrt x ≤ Real.sqrt (x + 1) := Real.sqrt_le_sqrt (by linarith)
  have hgap0 : 0 ≤ observerJetSqrtGap x := (observerJetSqrtGap_pos hx0).le
  have hgap := observerJetSqrtGap_mul_sum hx0
  have hprod : observerJetSqrtGap x * (2 * Real.sqrt x) ≤ 1 := by
    calc
      observerJetSqrtGap x * (2 * Real.sqrt x) ≤
          observerJetSqrtGap x *
            (Real.sqrt (x + 1) + Real.sqrt x) := by
        gcongr
        linarith
      _ = 1 := hgap
  have hsquare : Real.sqrt x ^ 2 = x := Real.sq_sqrt hx0
  have hhalf : observerJetSqrtGap x * Real.sqrt x ≤ (1 : ℝ) / 2 := by
    nlinarith
  have hmul := mul_le_mul_of_nonneg_left hhalf (mul_nonneg hx1 hs0)
  calc
    observerJetClockReal x = x * (x + 1) * observerJetSqrtGap x := rfl
    _ = (x + 1) * (Real.sqrt x ^ 2) * observerJetSqrtGap x := by
      rw [hsquare]
      ring
    _ = ((x + 1) * Real.sqrt x) *
        (observerJetSqrtGap x * Real.sqrt x) := by ring
    _ ≤ ((x + 1) * Real.sqrt x) * ((1 : ℝ) / 2) := hmul
    _ = (x + 1) * Real.sqrt x / 2 := by ring

theorem observerJetClockReal_firstDifference_lower {x : ℝ} (hx : 1 ≤ x) :
    (x + 1) / (Real.sqrt (x + 2) + Real.sqrt x) ≤
      observerJetClockReal (x + 1) - observerJetClockReal x := by
  have hlower := observerJetClockReal_lower (x := x + 1) (by linarith)
  have hupper := observerJetClockReal_upper (x := x) (by linarith)
  have hlower' : (x + 1) * Real.sqrt (x + 2) / 2 ≤
      observerJetClockReal (x + 1) := by
    convert hlower using 1
    ring
  have hx0 : 0 ≤ x := by linarith
  have hx2 : 0 ≤ x + 2 := by linarith
  have hden : Real.sqrt (x + 2) + Real.sqrt x ≠ 0 := by positivity
  have hsquare0 : Real.sqrt x ^ 2 = x := Real.sq_sqrt hx0
  have hsquare2 : Real.sqrt (x + 2) ^ 2 = x + 2 := Real.sq_sqrt hx2
  have hrational :
      (Real.sqrt (x + 2) - Real.sqrt x) / 2 =
        1 / (Real.sqrt (x + 2) + Real.sqrt x) := by
    field_simp [hden]
    nlinarith
  calc
    (x + 1) / (Real.sqrt (x + 2) + Real.sqrt x) =
        (x + 1) * (1 / (Real.sqrt (x + 2) + Real.sqrt x)) := by ring
    _ = (x + 1) * ((Real.sqrt (x + 2) - Real.sqrt x) / 2) := by
      rw [hrational]
    _ ≤ observerJetClockReal (x + 1) - observerJetClockReal x := by
      nlinarith [hlower']

theorem observerJetClockReal_firstDifference_square_lower
    (n : ℕ) (hn : 1 ≤ n) :
    (n : ℝ) / 3 ≤
      observerJetClockReal ((n : ℝ) ^ 2 + 1) -
        observerJetClockReal ((n : ℝ) ^ 2) := by
  let x : ℝ := (n : ℝ) ^ 2
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hx : 1 ≤ x := by dsimp [x]; nlinarith
  have hdiff := observerJetClockReal_firstDifference_lower hx
  have hsqrtSquare : Real.sqrt x = n := by
    dsimp [x]
    rw [Real.sqrt_sq_eq_abs, abs_of_nonneg]
    positivity
  have hx2le : x + 2 ≤ ((n : ℝ) + 1) ^ 2 := by
    dsimp [x]
    nlinarith
  have hsqrt2 : Real.sqrt (x + 2) ≤ (n : ℝ) + 1 := by
    rw [← Real.sqrt_sq (by positivity : 0 ≤ (n : ℝ) + 1)]
    exact Real.sqrt_le_sqrt hx2le
  have hdenpos : 0 < Real.sqrt (x + 2) + Real.sqrt x := by positivity
  have hdenle : Real.sqrt (x + 2) + Real.sqrt x ≤ 2 * (n : ℝ) + 1 := by
    rw [hsqrtSquare]
    linarith
  have hfrac : (n : ℝ) / 3 ≤
      (x + 1) / (Real.sqrt (x + 2) + Real.sqrt x) := by
    apply (le_div_iff₀ hdenpos).2
    have hmul := mul_le_mul_of_nonneg_left hdenle (by positivity : 0 ≤ (n : ℝ) / 3)
    dsimp [x]
    nlinarith
  exact hfrac.trans hdiff

end

end GaloisForLFunctions.HTGeometry

namespace GaloisForLFunctions.RHTower

open _root_.RHTower
open GaloisForLFunctions.HTGeometry

noncomputable section

theorem completedRieszHarmonicClockRatio_firstDifference_square_lower
    (n : ℕ) (hn : 1 ≤ n) :
    (n : ℝ) / 3 ≤
      completedRieszHarmonicClockRatio (n ^ 2) -
        completedRieszHarmonicClockRatio (n ^ 2 - 1) := by
  rw [completedRieszHarmonicClockRatio_eq_observerJetClockReal,
    completedRieszHarmonicClockRatio_eq_observerJetClockReal]
  push_cast
  have hnpos : 0 < n := by omega
  have hsqpos : 0 < n ^ 2 := pow_pos hnpos 2
  have hsub : n ^ 2 - 1 + 1 = n ^ 2 := Nat.sub_add_cancel hsqpos
  have hcast : ((n ^ 2 - 1 : ℕ) : ℝ) + 1 = (n ^ 2 : ℕ) := by
    exact_mod_cast hsub
  rw [hcast]
  simpa only [Nat.cast_pow, add_comm] using
    observerJetClockReal_firstDifference_square_lower n hn

/-- First differences of the literal harmonic--Riesz clock are unbounded. -/
theorem not_completedRieszHarmonicClockRatio_firstDifference_uniformlyBounded :
    ¬ ∃ C : ℝ, ∀ k : ℕ,
      |completedRieszHarmonicClockRatio (k + 1) -
        completedRieszHarmonicClockRatio k| ≤ C := by
  rintro ⟨C, hC⟩
  have hC0 : 0 ≤ C := (abs_nonneg _).trans (hC 0)
  obtain ⟨n, hn⟩ := exists_nat_gt (3 * C)
  have hn1 : 1 ≤ n := by
    have hnRpos : (0 : ℝ) < n :=
      lt_of_le_of_lt (mul_nonneg (by norm_num) hC0) hn
    have hnpos : 0 < n := by exact_mod_cast hnRpos
    omega
  have hlower := completedRieszHarmonicClockRatio_firstDifference_square_lower n hn1
  have hnpos : 0 < n := by omega
  have hsqpos : 0 < n ^ 2 := pow_pos hnpos 2
  have hsub : n ^ 2 - 1 + 1 = n ^ 2 := Nat.sub_add_cancel hsqpos
  have hbound := hC (n ^ 2 - 1)
  rw [hsub] at hbound
  have hupper := (le_abs_self
    (completedRieszHarmonicClockRatio (n ^ 2) -
      completedRieszHarmonicClockRatio (n ^ 2 - 1))).trans
        hbound
  have hnR : 3 * C < (n : ℝ) := hn
  nlinarith

theorem abs_observerJetCurvature_completedRieszHarmonicClockRatio_le_constant
    (j : ℕ) :
    |observerJetCurvature completedRieszHarmonicClockRatio j| ≤ 13 / 4 := by
  have h := abs_observerJetCurvature_completedRieszHarmonicClockRatio_le j
  have hsqrt : (1 : ℝ) ≤ Real.sqrt (j + 1 : ℕ) := by
    rw [← Real.sqrt_one]
    exact Real.sqrt_le_sqrt (by
      exact_mod_cast Nat.succ_le_succ (Nat.zero_le j))
  calc
    |observerJetCurvature completedRieszHarmonicClockRatio j| ≤
        13 / (4 * Real.sqrt (j + 1 : ℕ)) := h
    _ ≤ 13 / 4 := by
      gcongr
      nlinarith

theorem completedRieszHarmonicClockRatio_curvatureUniformlyBounded :
    ObserverJetCurvatureUniformlyBounded completedRieszHarmonicClockRatio := by
  exact ⟨13 / 4, by norm_num,
    abs_observerJetCurvature_completedRieszHarmonicClockRatio_le_constant⟩

theorem tendsto_completedSourceObserverJetMass_atTop_zero :
    Filter.Tendsto completedSourceObserverJetMass Filter.atTop (nhds 0) := by
  have hpartial := hasSum_completedPrimePolarGammaHarmonicCharge_zero.tendsto_sum_nat
  have hindex : Filter.Tendsto (fun M : ℕ => M - 1) Filter.atTop Filter.atTop := by
    rw [Filter.tendsto_atTop]
    intro b
    filter_upwards [Filter.eventually_ge_atTop (b + 1)] with M hM
    omega
  have hcomp := hpartial.comp hindex
  apply hcomp.congr'
  filter_upwards [Filter.eventually_ge_atTop 2] with M hM
  simp only [Function.comp_apply]
  unfold completedSourceObserverJetMass observerJetMass
  rw [show M - 2 + 1 = M - 1 by omega]

theorem abs_mobiusDivisorSquareRootAbelMoment_div_le_completedSourceObserverJet
    {M : ℕ} (hM : 3 ≤ M) :
    |mobiusDivisorSquareRootAbelMoment M / M| ≤
      (|completedRieszHarmonicClockRatio 0| * |completedSourceObserverJetMass M| +
        |completedRieszHarmonicClockRatio 1 - completedRieszHarmonicClockRatio 0| *
          |completedSourceObserverJetDrift M| +
        (13 / 4) *
          (∑ j ∈ Finset.range (M - 3),
            |completedSourceObserverJetHistory M j| / Real.sqrt (j + 1 : ℕ))) / M := by
  have hraw := abs_mobiusDivisorSquareRootAbelMoment_le_completedSourceObserverJet hM
  have hMpos : (0 : ℝ) < M := by positivity
  rw [abs_div, abs_of_pos hMpos]
  exact div_le_div_of_nonneg_right hraw hMpos.le

/-- Literal minimal additive order two: value and slope escape, while curvature extends. -/
theorem completedRieszHarmonicClockRatio_minimalSecondFormationOrder :
    (¬ FormationClockRateUniformlyBounded completedRieszHarmonicClockRatio) ∧
    (¬ ∃ C : ℝ, ∀ k : ℕ,
      |completedRieszHarmonicClockRatio (k + 1) -
        completedRieszHarmonicClockRatio k| ≤ C) ∧
    ObserverJetCurvatureUniformlyBounded completedRieszHarmonicClockRatio ∧
    ObserverJetSecondFormationExtends completedRieszHarmonicClockRatio := by
  refine ⟨not_completedRieszHarmonicClockRatio_uniformlyBounded,
    not_completedRieszHarmonicClockRatio_firstDifference_uniformlyBounded,
    completedRieszHarmonicClockRatio_curvatureUniformlyBounded, ?_⟩
  exact (observerJetSecondFormationExtends_iff
    completedRieszHarmonicClockRatio).2
      completedRieszHarmonicClockRatio_curvatureUniformlyBounded

/-- Closed literal certificate: order-two clock law, source landing, and exact RH reduction. -/
theorem suzukiObserverJetFormationCompletion_unconditional :
    ((¬ FormationClockRateUniformlyBounded completedRieszHarmonicClockRatio) ∧
      (¬ ∃ C : ℝ, ∀ k : ℕ,
        |completedRieszHarmonicClockRatio (k + 1) -
          completedRieszHarmonicClockRatio k| ≤ C) ∧
      ObserverJetCurvatureUniformlyBounded completedRieszHarmonicClockRatio ∧
      ObserverJetSecondFormationExtends completedRieszHarmonicClockRatio) ∧
    Filter.Tendsto completedSourceObserverJetMass Filter.atTop (nhds 0) ∧
    (∀ M : ℕ, 3 ≤ M →
      mobiusDivisorSquareRootAbelMoment M =
        completedSourceObserverJetMass M * completedRieszHarmonicClockRatio 0 +
          completedSourceObserverJetDrift M *
            (completedRieszHarmonicClockRatio 1 - completedRieszHarmonicClockRatio 0) +
          ∑ j ∈ Finset.range (M - 3),
            completedSourceObserverJetHistory M j *
              observerJetCurvature completedRieszHarmonicClockRatio j) ∧
    (∀ M : ℕ, 3 ≤ M →
      |mobiusDivisorSquareRootAbelMoment M / M| ≤
        (|completedRieszHarmonicClockRatio 0| * |completedSourceObserverJetMass M| +
          |completedRieszHarmonicClockRatio 1 - completedRieszHarmonicClockRatio 0| *
            |completedSourceObserverJetDrift M| +
          (13 / 4) *
            (∑ j ∈ Finset.range (M - 3),
              |completedSourceObserverJetHistory M j| / Real.sqrt (j + 1 : ℕ))) / M) ∧
    (CompletedSourceObserverJetLinearActionBounded → RiemannHypothesis) := by
  refine ⟨completedRieszHarmonicClockRatio_minimalSecondFormationOrder,
    tendsto_completedSourceObserverJetMass_atTop_zero, ?_, ?_,
    riemannHypothesis_of_completedSourceObserverJetLinearActionBounded⟩
  · intro M hM
    exact mobiusDivisorSquareRootAbelMoment_eq_completedSourceObserverJet hM
  · intro M hM
    exact abs_mobiusDivisorSquareRootAbelMoment_div_le_completedSourceObserverJet hM

end

end GaloisForLFunctions.RHTower
