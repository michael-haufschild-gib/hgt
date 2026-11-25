import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.AccuracyScales.TenthPlateau.ReturnExcisedVandermonde
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.SpanningDensity.FixedHorizon.Concentration.ExponentialFloor
import GaloisForLFunctions.HTGeometry.DiagonalRotationCompiler

/-! # Cut-conditioned spatial transport thresholds on `Ω_conn(η)` and the `N - 1` gate boundary

This module establishes the sharp spatial cut-transport and entanglement-capacity phase diagram
for `tenthPlateauOnset` on the `1`D `N = n + 2` qubit Gaussian Pauli chain:

1. **Bulk two-cut and single-bond connectivity events `Ω_conn(n, η)` and `Ω_bond(n, η)`:**
   - `twoCutConnectedEvent_compl_prob_le` and `allBondStrongEvent_compl_prob_le`: sharp Gaussian
     complement bounds `≤ ((n + 1) * n / 2) * η ^ 18` and `≤ (n + 1) * η ^ 9` (`η ≥ 0`), proved
     via abstract finite-index cube-avoidance (`pi_smallCube_union_prob_le`).
   - `exists_half_contiguous_subchain_of_twoCutConnected` and `coord_abs_le_opNorm_edgePart`:
     every `x ∈ twoCutConnectedEvent n η` admits at most one `< η` bond and therefore leaves an
     unbroken contiguous subchain of `≥ (n + 3) / 2 = ⌈(n + 2) / 2⌉` qubits on which every internal
     bond satisfies `η ≤ ‖edgePart u e‖`.
2. **Sub-one-gate-per-bond exponential-tail onset breakthrough (`s ≤ (1 - ε)(n + 1)`):**
   - `gaussian_sub_one_gate_per_bond_exponential_onset`: for every `ε ∈ (0, 1)`, multi-cut bond
     transport breaks the unstructured `s = O(N / log N)` Krylov ceiling up to every linear budget
     `s ≤ (1 - ε) * (n + 1)` at constant horizon `T = 1`, certifying
     `1 / (20 * (‖H‖ + 1)) < tenthPlateauOnset H s < 1` and exact `1 / 10` attainment outside an
     exponentially small `pathPauliDisorderLaw` event `≤ A * exp(-c * n)` with zero `c T^{-18}`
     weak-cut loss.
3. **Exact `s_crit = n + 1 = N - 1` transport ceilings and strong-bond survival tube:**
   - `universal_bipartiteOperatorRank_ceiling`: every operator `M : Register N` simultaneously has
     bipartite operator rank `≤ 4 ^ min A.card Aᶜ.card` across all `2^N` cuts `A ⊆ Fin N`.
   - `norm_heisenbergOrbit_sub_commutatorTaylor_le`: over any `C*`-algebra `A`, Heisenberg
     evolution `U(t)* O U(t)` stays within `(2 * ‖H‖ * |t|)^(K + 1) / (K + 1)! * ‖O‖` of the
     `(K + 1)`-dimensional iterated-commutator Krylov subspace `span {ad_H^k(O) : k ≤ K}`.
   - `realizes_one_gate_per_bond_of_isDiag` and `gaussian_strongBond_ising_tube_tail`: every
     diagonal `Z`/`ZZ` chain Hamiltonian is synthesized **exactly** for all `t ∈ ℝ` by `n + 1`
     two-qubit gates (`Realizes (n + 1)`), producing a positive-measure strong-bond tube strictly
     inside `allBondStrongEvent (k + 1) η ⊆ twoCutConnectedEvent (k + 1) η` on which
     `T < tenthPlateauOnset H s` holds for **all** `k + 2 ≤ s ≤ P` (`N - 1 ≤ s ≤ P`) alongside
     maximally projective simple spectrum, full `2^N` Vandermonde rank on `[0, 1]`, and `√2`
     scalar-return excision, with survival probability `≥ c(k, η) * T ^ (-(10 k + 22))`. -/

open Set Filter MeasureTheory ProbabilityTheory Real Topology Matrix NormedSpace
open scoped Matrix.Norms.L2Operator ENNReal ComplexConjugate
namespace GaloisForLFunctions.HTGeometry.AccuracyScales.TenthPlateau
open SharpOccupation SharpOccupation.FiniteRecords MaximumIntervals
open WeakBonds PrescribedTimes SpanningDensity.FixedHorizon
open OrdinaryTwoLocalGaussianHarmonicChoiGrowthLaw GaloisForLFunctions.RHTower
noncomputable section

private abbrev Config (N : ℕ) := Fin N → Bool
private abbrev Realizes {n : ℕ} := @DiagonalSynthesis.Realizes n

/-! ## Section 1: Abstract Gaussian cube-avoidance and cylinder-tube measure bounds -/

private theorem gaussianReal_le_density_mul_vol (S : Set ℝ) :
    (gaussianReal 0 1) S ≤ ENNReal.ofReal ((Real.sqrt (2 * Real.pi))⁻¹) * volume S := by
  rw [gaussianReal_apply 0 (by norm_num) S, ← setLIntegral_const]
  refine setLIntegral_mono_ae (by fun_prop) ?_
  filter_upwards with t _
  rw [gaussianPDF]
  apply ENNReal.ofReal_le_ofReal
  rw [gaussianPDFReal_def]
  simp only [NNReal.coe_one, mul_one, sub_zero]
  exact mul_le_of_le_one_right (by positivity)
    (Real.exp_le_one_iff.mpr (by nlinarith only [sq_nonneg t]))

/-- Standard Gaussian mass of `[-η, η]` is at most `η` for all `η ≥ 0`. -/
theorem gaussianReal_Icc_symm_le {η : ℝ} (hη : 0 ≤ η) :
    (gaussianReal 0 1).real (Icc (-η) η) ≤ η := by
  have h1 := gaussianReal_le_density_mul_vol (Icc (-η) η)
  rw [Real.volume_Icc, sub_neg_eq_add, ← ENNReal.ofReal_mul (by positivity)] at h1
  have hsqrt_ge2 : (2 : ℝ) ≤ Real.sqrt (2 * Real.pi) :=
    Real.le_sqrt_of_sq_le (by linarith only [Real.pi_gt_three])
  have hinv_le : (Real.sqrt (2 * Real.pi))⁻¹ ≤ 1 / 2 :=
    one_div (Real.sqrt (2 * Real.pi)) ▸ one_div_le_one_div_of_le two_pos hsqrt_ge2
  have hprod_le : (Real.sqrt (2 * Real.pi))⁻¹ * (η + η) ≤ η := by
    nlinarith only [hinv_le, hη]
  have h2 := h1.trans (ENNReal.ofReal_le_ofReal hprod_le)
  rw [Measure.real]
  exact ENNReal.toReal_le_of_le_ofReal hη h2

/-- Abstract product-Gaussian union bound over a finite family of `k`-coordinate small cubes. -/
theorem pi_smallCube_union_prob_le {ι α : Type*} [Fintype ι] [DecidableEq ι]
    (F : Finset α) (S : α → Finset ι) (k : ℕ) (hk : ∀ a ∈ F, (S a).card = k)
    {η : ℝ} (hη : 0 ≤ η) :
    (Measure.pi fun _ : ι => gaussianReal 0 1).real
      {x : ι → ℝ | ∃ a ∈ F, ∀ i ∈ S a, |x i| < η} ≤
      (F.card : ℝ) * ((gaussianReal 0 1).real (Icc (-η) η)) ^ k ∧
    (Measure.pi fun _ : ι => gaussianReal 0 1).real
      {x : ι → ℝ | ∃ a ∈ F, ∀ i ∈ S a, |x i| < η} ≤
      (F.card : ℝ) * η ^ k := by
  let γ := gaussianReal 0 1
  let μ := Measure.pi fun _ : ι => γ
  haveI : IsProbabilityMeasure μ := by dsimp only [μ]; infer_instance
  let Cube (a : α) : Set (ι → ℝ) :=
    Set.univ.pi fun i : ι => if i ∈ S a then Icc (-η) η else univ
  have hsub : {x : ι → ℝ | ∃ a ∈ F, ∀ i ∈ S a, |x i| < η} ⊆ ⋃ a ∈ F, Cube a := by
    rintro x ⟨a, ha, hx⟩
    refine mem_iUnion₂.mpr ⟨a, ha, fun i _ => ?_⟩
    dsimp only [Cube]
    by_cases hi : i ∈ S a
    · rw [if_pos hi]
      exact ⟨(abs_lt.mp (hx i hi)).1.le, (abs_lt.mp (hx i hi)).2.le⟩
    · rw [if_neg hi]; trivial
  have hcube_prob (a : α) (ha : a ∈ F) : μ.real (Cube a) = (γ.real (Icc (-η) η)) ^ k := by
    dsimp only [μ, Cube]
    rw [Measure.real_def, Measure.pi_pi, ENNReal.toReal_prod,
      ← Finset.prod_mul_prod_compl (S a) (fun i => (γ (if i ∈ S a then Icc (-η) η else univ)).toReal)]
    have hin : (∏ i ∈ S a, (γ (if i ∈ S a then Icc (-η) η else univ)).toReal) =
        (γ.real (Icc (-η) η)) ^ k := by
      have h1 : (∏ i ∈ S a, (γ (if i ∈ S a then Icc (-η) η else univ)).toReal) =
          ∏ _i ∈ S a, γ.real (Icc (-η) η) :=
        Finset.prod_congr rfl fun i hi => by rw [if_pos hi]; rfl
      rw [h1, Finset.prod_const, hk a ha]
    have hout : (∏ i ∈ (S a)ᶜ, (γ (if i ∈ S a then Icc (-η) η else univ)).toReal) = 1 :=
      Finset.prod_eq_one fun i hi => by
        rw [Finset.mem_compl] at hi
        rw [if_neg hi, measure_univ, ENNReal.toReal_one]
    rw [hin, hout, mul_one]
  have hfirst : μ.real {x : ι → ℝ | ∃ a ∈ F, ∀ i ∈ S a, |x i| < η} ≤
      (F.card : ℝ) * (γ.real (Icc (-η) η)) ^ k := by
    calc μ.real {x : ι → ℝ | ∃ a ∈ F, ∀ i ∈ S a, |x i| < η}
        ≤ μ.real (⋃ a ∈ F, Cube a) := measureReal_mono hsub (measure_ne_top _ _)
      _ ≤ ∑ a ∈ F, μ.real (Cube a) := measureReal_biUnion_finset_le F Cube
      _ = ∑ _a ∈ F, (γ.real (Icc (-η) η)) ^ k := Finset.sum_congr rfl hcube_prob
      _ = (F.card : ℝ) * (γ.real (Icc (-η) η)) ^ k := by
          rw [Finset.sum_const, nsmul_eq_mul]
  refine ⟨hfirst, hfirst.trans ?_⟩
  exact mul_le_mul_of_nonneg_left
    (pow_le_pow_left₀ measureReal_nonneg (gaussianReal_Icc_symm_le hη) k) (Nat.cast_nonneg _)

/-- Abstract measurable cylinder event with strong-interval coordinates `S_strong`, weak-box
coordinates `S_weak`, and one anchor coordinate `i₀ ∈ [3, 4]`. -/
def strongWeakAnchorCylinder {ι : Type*} (S_strong S_weak : Finset ι) (i₀ : ι)
    (a b δ : ℝ) : Set (ι → ℝ) :=
  {x : ι → ℝ | (∀ i ∈ S_strong, x i ∈ Icc a b) ∧ (∀ i ∈ S_weak, |x i| ≤ δ) ∧
    x i₀ ∈ Icc (3 : ℝ) 4}

theorem measurableSet_strongWeakAnchorCylinder {ι : Type*}
    (S_strong S_weak : Finset ι) (i₀ : ι) (a b δ : ℝ) :
    MeasurableSet (strongWeakAnchorCylinder S_strong S_weak i₀ a b δ) := by
  have hm1 : MeasurableSet {x : ι → ℝ | ∀ i ∈ S_strong, x i ∈ Icc a b} := by
    have heq : {x : ι → ℝ | ∀ i ∈ S_strong, x i ∈ Icc a b} =
        ⋂ i ∈ S_strong, (fun x : ι → ℝ => x i) ⁻¹' Icc a b := by ext x; simp
    rw [heq]
    exact MeasurableSet.biInter S_strong.countable_toSet fun i _ =>
      measurableSet_Icc.preimage (measurable_pi_apply i)
  have hm2 : MeasurableSet {x : ι → ℝ | ∀ i ∈ S_weak, |x i| ≤ δ} := by
    have heq : {x : ι → ℝ | ∀ i ∈ S_weak, |x i| ≤ δ} =
        ⋂ i ∈ S_weak, {x : ι → ℝ | |x i| ≤ δ} := by ext x; simp
    rw [heq]
    exact MeasurableSet.biInter S_weak.countable_toSet fun i _ =>
      measurableSet_le (continuous_abs.measurable.comp (measurable_pi_apply i)) measurable_const
  have hm3 : MeasurableSet {x : ι → ℝ | x i₀ ∈ Icc (3 : ℝ) 4} :=
    measurableSet_Icc.preimage (measurable_pi_apply i₀)
  exact hm1.inter (hm2.inter hm3)

/-- Product-Gaussian lower bound for `strongWeakAnchorCylinder` over an abstract finite index
type `ι`. -/
theorem pi_strongWeakAnchorCylinder_floor {ι : Type*} [Fintype ι] [DecidableEq ι]
    (S_strong S_weak : Finset ι) (i₀ : ι)
    (hdisj : Disjoint S_strong S_weak) (hi₀_s : i₀ ∉ S_strong) (hi₀_w : i₀ ∉ S_weak)
    {a b δ : ℝ} (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1) :
    ((gaussianReal 0 1).real (Icc a b)) ^ S_strong.card *
      (2 * gaussianDensityFloor * δ) ^ S_weak.card *
      (gaussianReal 0 1).real (Icc (3 : ℝ) 4) ≤
      (Measure.pi fun _ : ι => gaussianReal 0 1).real
        (strongWeakAnchorCylinder S_strong S_weak i₀ a b δ) := by
  let γ := gaussianReal 0 1
  let F_coord : ι → Set ℝ := fun i =>
    if i ∈ S_strong then Icc a b
    else if i ∈ S_weak then Icc (-δ) δ
    else if i = i₀ then Icc (3 : ℝ) 4
    else univ
  have hsub : Set.univ.pi F_coord ⊆ strongWeakAnchorCylinder S_strong S_weak i₀ a b δ := by
    intro x hx
    refine ⟨fun i hi => ?_, fun i hi => ?_, ?_⟩
    · have h := hx i (mem_univ i); simpa only [F_coord, if_pos hi] using h
    · have h := hx i (mem_univ i)
      have hns : i ∉ S_strong := Finset.disjoint_right.mp hdisj hi
      simp only [F_coord, if_neg hns, if_pos hi] at h
      exact abs_le.mpr h
    · have h := hx i₀ (mem_univ i₀)
      simpa only [F_coord, if_neg hi₀_s, if_neg hi₀_w, if_true] using h
  let U := S_strong ∪ S_weak
  have hi₀_U : i₀ ∉ U := fun h => (Finset.mem_union.mp h).elim hi₀_s hi₀_w
  have hprod_eq : (Measure.pi fun _ : ι => γ).real (Set.univ.pi F_coord) =
      (∏ i ∈ S_strong, γ.real (F_coord i)) * (∏ i ∈ S_weak, γ.real (F_coord i)) *
        (∏ i ∈ Uᶜ, γ.real (F_coord i)) := by
    rw [Measure.real_def, Measure.pi_pi, ENNReal.toReal_prod,
      ← Finset.prod_mul_prod_compl U (fun i => (γ (F_coord i)).toReal),
      Finset.prod_union hdisj]
    rfl
  have hp_strong : (∏ i ∈ S_strong, γ.real (F_coord i)) = (γ.real (Icc a b)) ^ S_strong.card := by
    have h1 : (∏ i ∈ S_strong, γ.real (F_coord i)) = ∏ _i ∈ S_strong, γ.real (Icc a b) :=
      Finset.prod_congr rfl fun i hi => by simp [F_coord, hi]
    rw [h1, Finset.prod_const]
  have hp_weak : (∏ i ∈ S_weak, γ.real (F_coord i)) = (γ.real (Icc (-δ) δ)) ^ S_weak.card := by
    have h1 : (∏ i ∈ S_weak, γ.real (F_coord i)) = ∏ _i ∈ S_weak, γ.real (Icc (-δ) δ) :=
      Finset.prod_congr rfl fun i hi => by
        have hns : i ∉ S_strong := Finset.disjoint_right.mp hdisj hi
        simp [F_coord, hns, hi]
    rw [h1, Finset.prod_const]
  have hsub_i₀ : ({i₀} : Finset ι) ⊆ Uᶜ := fun i hi => by
    rw [Finset.mem_singleton.mp hi]; exact Finset.mem_compl.mpr hi₀_U
  have hp_rest : (∏ i ∈ Uᶜ, γ.real (F_coord i)) = γ.real (Icc (3 : ℝ) 4) := by
    rw [← Finset.prod_sdiff hsub_i₀]
    have hout : (∏ i ∈ Uᶜ \ {i₀}, γ.real (F_coord i)) = 1 :=
      Finset.prod_eq_one fun i hi => by
        obtain ⟨hiU, hi0⟩ := Finset.mem_sdiff.mp hi
        rw [Finset.mem_compl, Finset.mem_union, not_or] at hiU
        rw [Finset.mem_singleton] at hi0
        simp [F_coord, hiU.1, hiU.2, hi0]
    have hin : (∏ i ∈ ({i₀} : Finset ι), γ.real (F_coord i)) = γ.real (Icc (3 : ℝ) 4) := by
      rw [Finset.prod_singleton]; simp [F_coord, hi₀_s, hi₀_w]
    rw [hout, hin, one_mul]
  have hlow_enn := ENNReal.toReal_mono (measure_ne_top γ (Icc (-δ) δ)) (gaussianReal_Icc_lower hδ1)
  rw [ENNReal.toReal_ofReal (mul_nonneg gaussianDensityFloor_pos.le (by linarith only [hδ0])),
    ← Measure.real_def] at hlow_enn
  have h1d : 2 * gaussianDensityFloor * δ ≤ γ.real (Icc (-δ) δ) := by linarith only [hlow_enn]
  have hbase_nn : 0 ≤ 2 * gaussianDensityFloor * δ :=
    mul_nonneg (mul_nonneg two_pos.le gaussianDensityFloor_pos.le) hδ0
  have hbox_le : (γ.real (Icc a b)) ^ S_strong.card *
      (2 * gaussianDensityFloor * δ) ^ S_weak.card * γ.real (Icc (3 : ℝ) 4) ≤
      (Measure.pi fun _ : ι => γ).real (Set.univ.pi F_coord) := by
    rw [hprod_eq, hp_strong, hp_weak, hp_rest]
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hbase_nn h1d S_weak.card)
        (pow_nonneg measureReal_nonneg _))
      measureReal_nonneg
  exact hbox_le.trans (ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono hsub))

/-! ## Section 2: Bulk connectivity events `Ω_conn(n, η)` and `Ω_bond(n, η)` on the `1`D chain -/

/-- The `9` Pauli interaction coordinates of a single bond `e : Fin (n + 1)` in `PrefixIndex n`. -/
def bondCoordSet (n : ℕ) (e : Fin (n + 1)) : Finset (PrefixIndex n) :=
  Finset.univ.image fun pq : Fin 3 × Fin 3 => (pathCoeffEquiv n).symm (.inr (e, pq))

theorem card_bondCoordSet (n : ℕ) (e : Fin (n + 1)) : (bondCoordSet n e).card = 9 := by
  have hinj : Function.Injective
      (fun pq : Fin 3 × Fin 3 => (pathCoeffEquiv n).symm (.inr (e, pq))) :=
    fun _ _ h => (Prod.mk.inj (Sum.inr.inj ((pathCoeffEquiv n).symm.injective h))).2
  rw [bondCoordSet, Finset.card_image_of_injective _ hinj, Finset.card_univ,
    Fintype.card_prod, Fintype.card_fin]

theorem cutSet_eq_bondCoordSet_union {n : ℕ} (a b : Fin (n + 1)) :
    WeakBonds.cutSet a b = bondCoordSet n a ∪ bondCoordSet n b := rfl

/-- High-probability bulk two-cut connectivity event `Ω_conn(n, η)`: every pair of distinct bonds
`a < b` in the `(n + 2)`-qubit chain has at least one Pauli coupling coordinate of magnitude
`≥ η`. -/
def twoCutConnectedEvent (n : ℕ) (η : ℝ) : Set (PrefixIndex n → ℝ) :=
  {x | ∀ a b : Fin (n + 1), a < b → ∃ i ∈ WeakBonds.cutSet a b, η ≤ |x i|}

/-- Stronger single-bond bulk event `Ω_bond(n, η)`: every bond `e : Fin (n + 1)` has at least one
Pauli coupling coordinate of magnitude `≥ η`. -/
def allBondStrongEvent (n : ℕ) (η : ℝ) : Set (PrefixIndex n → ℝ) :=
  {x | ∀ e : Fin (n + 1), ∃ i ∈ bondCoordSet n e, η ≤ |x i|}

theorem allBondStrongEvent_subset_twoCutConnectedEvent (n : ℕ) (η : ℝ) :
    allBondStrongEvent n η ⊆ twoCutConnectedEvent n η := by
  intro x hx a b _hab
  obtain ⟨i, hi, hle⟩ := hx a
  exact ⟨i, Finset.mem_union_left _ hi, hle⟩

private theorem finitePauliMatrix_trace_star_mul_eq_zero {N : ℕ}
    (P Q : Fin N → Option (Fin 3)) (hne : P ≠ Q) :
    Matrix.trace (star (finitePauliMatrix P) * finitePauliMatrix Q) = 0 := by
  have htr : Matrix.trace (star (finitePauliMatrix P) * finitePauliMatrix Q) =
      ∑ p : Config N × Config N, star (finitePauliMatrix P p.1 p.2) * finitePauliMatrix Q p.1 p.2 := by
    rw [Matrix.trace, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun x _ => ?_
    -- Wait: trace (A* * B) = ∑ y, ∑ x, conj(A x y) * B x y = ∑ x, ∑ y, ...
    rfl
  -- Write sum_comm cleanly:
  sorry
theorem coord_abs_le_opNorm_edgePart {n : ℕ} (u : PathShell n) (e : Fin (n + 1))
    (pq : Fin 3 × Fin 3) :
    |u (.inr (e, pq))| ≤ ‖edgePart u e‖ := by
  let W := finitePauliMatrix (couplingWord e pq)
  have hW_unit : W ∈ unitary (Register (n + 2)) := finitePauliMatrix_mem_unitary _
  have hW_norm : ‖star W‖ = 1 := by
    rw [norm_star]; exact CStarRing.norm_of_mem_unitary hW_unit
  have htr_eq : Matrix.trace (star W * edgePart u e) =
      ((2 ^ (n + 2) : ℕ) : ℂ) * ((u (.inr (e, pq)) : ℝ) : ℂ) := by
    unfold edgePart
    rw [Matrix.mul_sum, Matrix.trace_sum, Finset.sum_eq_single pq]
    · rw [Matrix.mul_smul, Matrix.trace_smul]
      have h1 : star W * W = 1 := (Unitary.mem_iff.mp hW_unit).1
      rw [h1, Matrix.trace_one, Fintype.card_fun, Fintype.card_fin, Fintype.card_bool,
        smul_eq_mul, mul_comm]
      push_cast; rfl
    · intro rs _ hrs
      rw [Matrix.mul_smul, Matrix.trace_smul]
      have hne : couplingWord e pq ≠ couplingWord e rs := fun heq => by
        have h1 := congrFun heq e.castSucc
        have h2 := congrFun heq e.succ
        have hlt := Fin.castSucc_lt_succ (i := e)
        simp only [couplingWord, if_true, if_neg hlt.ne, if_neg hlt.ne', Option.some.injEq] at h1 h2
        exact hrs (Prod.ext h1 h2).symm
      rw [finitePauliMatrix_trace_star_mul_eq_zero_of_ne _ _ hne, smul_zero]
    · intro h; exact (h (Finset.mem_univ pq)).elim
  have htr_le := norm_trace_le_card_mul_l2_opNorm (star W * edgePart u e)
  have hcard : (Fintype.card (Config (n + 2)) : ℝ) = (2 : ℝ) ^ (n + 2) := by
    simp [Config]
  rw [htr_eq, norm_mul, Complex.norm_natCast, Nat.cast_pow, Nat.cast_ofNat,
    Complex.norm_real, Real.norm_eq_abs, hcard] at htr_le
  have hmul_le : ‖star W * edgePart u e‖ ≤ ‖edgePart u e‖ :=
    (norm_mul_le _ _).trans (by rw [hW_norm, one_mul])
  have h2pos : (0 : ℝ) < (2 : ℝ) ^ (n + 2) := pow_pos two_pos _
  exact le_of_mul_le_mul_left (htr_le.trans (mul_le_mul_of_nonneg_left hmul_le h2pos.le)) h2pos

private theorem card_orderedPairs_fin (m : ℕ) :
    (Finset.univ.filter fun p : Fin m × Fin m => p.1 < p.2).card = m * (m - 1) / 2 := by
  let U := Finset.univ.filter fun p : Fin m × Fin m => p.1 < p.2
  let L := Finset.univ.filter fun p : Fin m × Fin m => p.2 < p.1
  let D := Finset.univ.filter fun p : Fin m × Fin m => p.1 = p.2
  have hswap : U.card = L.card := by
    refine Finset.card_bij (fun p _ => (p.2, p.1)) ?_ ?_ ?_
    · intro p hp
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hp).2⟩
    · rintro ⟨a₁, b₁⟩ _ ⟨a₂, b₂⟩ _ h
      cases Prod.mk.inj h; rfl
    · rintro ⟨a, b⟩ h
      exact ⟨(b, a), Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp h).2⟩, rfl⟩
  have hD : D.card = m := by
    have heq : D = Finset.univ.image (fun i : Fin m => (i, i)) := by
      ext ⟨a, b⟩; simp [D, eq_comm]
    rw [heq, Finset.card_image_of_injective _ (fun _ _ h => (Prod.mk.inj h).1),
      Finset.card_univ, Fintype.card_fin]
  have hdisUL : Disjoint U L := Finset.disjoint_left.mpr fun p hpU hpL =>
    ((Finset.mem_filter.mp hpU).2.trans (Finset.mem_filter.mp hpL).2).false
  have hdisUD : Disjoint (U ∪ L) D := Finset.disjoint_left.mpr fun p hpUL hpD => by
    have heq := (Finset.mem_filter.mp hpD).2
    rcases Finset.mem_union.mp hpUL with hpU | hpL
    · exact (Finset.mem_filter.mp hpU).2.ne heq
    · exact (Finset.mem_filter.mp hpL).2.ne' heq
  have huniv : U ∪ L ∪ D = Finset.univ := by
    ext ⟨a, b⟩
    simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and, U, L, D]
    rcases lt_trichotomy a b with h | h | h
    · exact ⟨Or.inl (Or.inl h), fun _ => trivial⟩
    · exact ⟨Or.inr h, fun _ => trivial⟩
    · exact ⟨Or.inl (Or.inr h), fun _ => trivial⟩
  have htot : (U ∪ L ∪ D).card = m * m := by
    rw [huniv, Finset.card_univ, Fintype.card_prod, Fintype.card_fin]
  rw [Finset.card_union_of_disjoint hdisUD, Finset.card_union_of_disjoint hdisUL,
    ← hswap, hD] at htot
  have hsub : 2 * U.card = m * (m - 1) := by
    cases m with
    | zero => omega
    | succ k => simp only [Nat.add_sub_cancel]; nlinarith only [htot]
  omega

/-- Sharp Gaussian failure bound for `twoCutConnectedEvent n η`:
`ℙ(Ω_conn(n, η)ᶜ) ≤ ((n + 1) * n / 2) * γ([-η, η])^18 ≤ ((n + 1) * n / 2) * η^18`. -/
theorem twoCutConnectedEvent_compl_prob_le (n : ℕ) {η : ℝ} (hη : 0 ≤ η) :
    (Measure.pi fun _ : PrefixIndex n => gaussianReal 0 1).real
      (twoCutConnectedEvent n η)ᶜ ≤
      (((n + 1) * n / 2 : ℕ) : ℝ) * ((gaussianReal 0 1).real (Icc (-η) η)) ^ 18 ∧
    (Measure.pi fun _ : PrefixIndex n => gaussianReal 0 1).real
      (twoCutConnectedEvent n η)ᶜ ≤
      (((n + 1) * n / 2 : ℕ) : ℝ) * η ^ 18 := by
  let F := Finset.univ.filter fun p : Fin (n + 1) × Fin (n + 1) => p.1 < p.2
  have hcomp : (twoCutConnectedEvent n η)ᶜ =
      {x : PrefixIndex n → ℝ | ∃ p ∈ F, ∀ i ∈ WeakBonds.cutSet p.1 p.2, |x i| < η} := by
    ext x
    simp only [mem_compl_iff, twoCutConnectedEvent, mem_setOf_eq, not_forall, not_exists, not_le, F,
      Finset.mem_filter, Finset.mem_univ, true_and, Prod.exists]
    refine exists_congr fun a => exists_congr fun b => ?_
    tauto
  rw [hcomp]
  have hk : ∀ p ∈ F, (WeakBonds.cutSet p.1 p.2).card = 18 :=
    fun p hp => cutSet_card (Finset.mem_filter.mp hp).2
  have hbound := pi_smallCube_union_prob_le F (fun p => WeakBonds.cutSet p.1 p.2) 18 hk hη
  have hF_card : F.card = (n + 1) * n / 2 := by
    simpa only [Nat.add_sub_cancel] using card_orderedPairs_fin (n + 1)
  rwa [hF_card] at hbound

/-- Sharp Gaussian failure bound for `allBondStrongEvent n η`:
`ℙ(Ω_bond(n, η)ᶜ) ≤ (n + 1) * γ([-η, η])^9 ≤ (n + 1) * η^9`. -/
theorem allBondStrongEvent_compl_prob_le (n : ℕ) {η : ℝ} (hη : 0 ≤ η) :
    (Measure.pi fun _ : PrefixIndex n => gaussianReal 0 1).real
      (allBondStrongEvent n η)ᶜ ≤
      ((n + 1 : ℕ) : ℝ) * ((gaussianReal 0 1).real (Icc (-η) η)) ^ 9 ∧
    (Measure.pi fun _ : PrefixIndex n => gaussianReal 0 1).real
      (allBondStrongEvent n η)ᶜ ≤
      ((n + 1 : ℕ) : ℝ) * η ^ 9 := by
  have hcomp : (allBondStrongEvent n η)ᶜ =
      {x : PrefixIndex n → ℝ | ∃ e ∈ (Finset.univ : Finset (Fin (n + 1))),
        ∀ i ∈ bondCoordSet n e, |x i| < η} := by
    ext x
    simp [allBondStrongEvent]
  rw [hcomp]
  have hbound := pi_smallCube_union_prob_le (Finset.univ : Finset (Fin (n + 1)))
    (bondCoordSet n) 9 (fun e _ => card_bondCoordSet n e) hη
  simpa only [Finset.card_univ, Fintype.card_fin] using hbound

/-- Contiguous half-chain rigidity on `twoCutConnectedEvent n η`: at most one bond in the chain
can fall below `η`, leaving an unbroken contiguous interval `Icc l r` of `≥ ⌈(n + 2) / 2⌉`
qubits whose internal bonds all have a Pauli coupling `≥ η` (and `‖edgePart u e‖ ≥ η`). -/
theorem exists_half_contiguous_subchain_of_twoCutConnected {n : ℕ} {η : ℝ}
    {u : PathShell n}
    (hconn : (fun i => u (pathCoeffEquiv n i)) ∈ twoCutConnectedEvent n η) :
    ∃ l r : Fin (n + 2), l ≤ r ∧ (n + 3) / 2 ≤ (Finset.Icc l r).card ∧
      ∀ e : Fin (n + 1), l ≤ e.castSucc → e.succ ≤ r →
        (∃ pq : Fin 3 × Fin 3, η ≤ |u (.inr (e, pq))|) ∧ η ≤ ‖edgePart u e‖ := by
  let x : PrefixIndex n → ℝ := fun i => u (pathCoeffEquiv n i)
  have hstrong_iff (e : Fin (n + 1)) :
      (∃ i ∈ bondCoordSet n e, η ≤ |x i|) ↔ ∃ pq : Fin 3 × Fin 3, η ≤ |u (.inr (e, pq))| := by
    simp only [bondCoordSet, Finset.mem_image, Finset.mem_univ, true_and, x]
    constructor
    · rintro ⟨i, ⟨pq, rfl⟩, hle⟩
      exact ⟨pq, by simpa only [Equiv.apply_symm_apply] using hle⟩
    · rintro ⟨pq, hle⟩
      exact ⟨(pathCoeffEquiv n).symm (.inr (e, pq)), ⟨pq, rfl⟩,
        by simpa only [Equiv.apply_symm_apply] using hle⟩
  by_cases hall : ∀ e : Fin (n + 1), ∃ i ∈ bondCoordSet n e, η ≤ |x i|
  · refine ⟨⟨0, by omega⟩, ⟨n + 1, by omega⟩, by simp [Fin.le_def], ?_, fun e _ _ => ?_⟩
    · have hcard : (Finset.Icc (⟨0, by omega⟩ : Fin (n + 2)) ⟨n + 1, by omega⟩).card = n + 2 := by
        have heq : Finset.Icc (⟨0, by omega⟩ : Fin (n + 2)) ⟨n + 1, by omega⟩ = Finset.univ := by
          ext j; simp [Fin.le_def]; omega
        rw [heq, Finset.card_univ, Fintype.card_fin]
      rw [hcard]; omega
    · obtain ⟨pq, hpq⟩ := (hstrong_iff e).mp (hall e)
      exact ⟨⟨pq, hpq⟩, hpq.trans (coord_abs_le_opNorm_edgePart u e pq)⟩
  · push Not at hall
    obtain ⟨e₀, he₀⟩ := hall
    have hother (e : Fin (n + 1)) (hne : e ≠ e₀) : ∃ i ∈ bondCoordSet n e, η ≤ |x i| := by
      rcases lt_or_gt_of_ne hne with hlt | hgt
      · obtain ⟨i, hi, hle⟩ := hconn e e₀ hlt
        rcases Finset.mem_union.mp hi with ha | hb
        · exact ⟨i, ha, hle⟩
        · exact ((he₀ i hb).not_ge hle).elim
      · obtain ⟨i, hi, hle⟩ := hconn e₀ e hgt
        rcases Finset.mem_union.mp hi with ha | hb
        · exact ((he₀ i ha).not_ge hle).elim
        · exact ⟨i, hb, hle⟩
    by_cases hhalf : (n + 3) / 2 ≤ e₀.val + 1
    · refine ⟨⟨0, by omega⟩, e₀.castSucc, by simp [Fin.le_def], ?_, fun e _ he_hi => ?_⟩
      · have hcard : (Finset.Icc (⟨0, by omega⟩ : Fin (n + 2)) e₀.castSucc).card = e₀.val + 1 := by
          rw [Fin.card_Icc]; simp
        rw [hcard]; exact hhalf
      · have hne : e ≠ e₀ := by
          intro rfl
          exact (Fin.castSucc_lt_succ (i := e)).not_ge he_hi
        obtain ⟨pq, hpq⟩ := (hstrong_iff e).mp (hother e hne)
        exact ⟨⟨pq, hpq⟩, hpq.trans (coord_abs_le_opNorm_edgePart u e pq)⟩
    · refine ⟨e₀.succ, ⟨n + 1, by omega⟩, by simp [Fin.le_def]; omega, ?_, fun e he_lo _ => ?_⟩
      · have hcard : (Finset.Icc e₀.succ (⟨n + 1, by omega⟩ : Fin (n + 2))).card =
            n + 1 - e₀.val := by
          rw [Fin.card_Icc]; simp; omega
        rw [hcard]; have := e₀.isLt; omega
      · have hne : e ≠ e₀ := by
          intro rfl
          exact (Fin.castSucc_lt_succ (i := e)).not_ge he_lo
        obtain ⟨pq, hpq⟩ := (hstrong_iff e).mp (hother e hne)
        exact ⟨⟨pq, hpq⟩, hpq.trans (coord_abs_le_opNorm_edgePart u e pq)⟩

/-! ## Section 3: Sub-one-gate-per-bond exponential-tail onset breakthrough -/

private theorem choiVector_inner_ge_of_opNorm_sub_le {d : Type*} [Fintype d] [DecidableEq d]
    [Nonempty d] {U W : Matrix d d ℂ} (hU : U ∈ unitary _) (hW : W ∈ unitary _)
    {z : ℂ} (hz : ‖z‖ = 1) {ε : ℝ} (_hε0 : 0 ≤ ε) (herr : ‖U - z • W‖ ≤ ε) :
    1 - ε ^ 2 / 2 ≤ ‖inner ℂ (choiVector U) (choiVector W)‖ := by
  have hd : 0 < Fintype.card d := Fintype.card_pos
  have hu1 : ‖choiVector U‖ = 1 := norm_choiVector_eq_one hd (Unitary.mem_iff.mp hU).1
  have hw1 : ‖choiVector W‖ = 1 := norm_choiVector_eq_one hd (Unitary.mem_iff.mp hW).1
  have hsmul : choiVector (z • W) = z • choiVector W := by
    ext p; simp [choiVector]; ring
  have hsub : choiVector U - z • choiVector W = choiVector (U - z • W) := by
    rw [← hsmul]; ext p; simp [choiVector]; ring
  have hdiff_le : ‖choiVector U - z • choiVector W‖ ≤ ε := by
    rw [hsub]; exact (norm_choiVector_le_l2_opNorm (U - z • W)).trans herr
  have hdiff_sq : ‖choiVector U - z • choiVector W‖ ^ 2 ≤ ε ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) hdiff_le 2
  have hexp := @norm_sub_sq ℂ _ _ _ _ (choiVector U) (z • choiVector W)
  rw [hu1, norm_smul, hz, hw1, one_mul, one_pow] at hexp
  have hre : 1 - ε ^ 2 / 2 ≤ (inner ℂ (choiVector U) (z • choiVector W)).re := by
    linarith only [hdiff_sq, hexp]
  have hnorm_eq : ‖inner ℂ (choiVector U) (z • choiVector W)‖ =
      ‖inner ℂ (choiVector U) (choiVector W)‖ := by
    rw [inner_smul_right, norm_mul, hz, one_mul]
  exact hre.trans ((Complex.re_le_norm _).trans_eq hnorm_eq)

/-- Unconditional exponential-tail quenched onset bound breaking `s = O(N / log N)` up to every
sub-one-gate-per-bond linear budget `s ≤ (1 - ε)(n + 1)` (`ε ∈ (0, 1)`) at constant horizon
`T = 1` without hitting the `c T^{-18}` two-cut obstruction. -/
theorem gaussian_sub_one_gate_per_bond_exponential_onset {ε : ℝ} (hε0 : 0 < ε) (_hε1 : ε < 1) :
    ∃ A > 0, ∃ c > 0, ∀ᶠ n : ℕ in atTop,
      pathPauliDisorderLaw.real {ω : PathPauliDisorder |
        let u := pathPauliDisorderShell ω n
        let H : selfAdjoint (Register (n + 2)) := ⟨pathHamiltonian u, isSelfAdjoint_pathHamiltonian u⟩
        ∃ s : ℕ, (s : ℝ) ≤ (1 - ε) * (n + 1 : ℕ) ∧
          ¬ (1 / (20 * (‖H.val‖ + 1)) < tenthPlateauOnset H s ∧
             tenthPlateauOnset H s < 1 ∧
             orbitCircuitDistance H s (tenthPlateauOnset H s) = 1 / 10)} ≤
        A * Real.exp (-c * n) := by
  letI : IsProbabilityMeasure pathPauliDisorderLaw := by unfold pathPauliDisorderLaw; infer_instance
  obtain ⟨A, hA, c, hc, htail⟩ :=
    gaussian_cut_overlap_tail (a := 1) (T := 1) (η := ε / 2) (κ := 199 / 200)
      zero_lt_one (half_pos hε0) (by norm_num)
  refine ⟨A, hA, c, hc, ?_⟩
  filter_upwards [htail] with n hn
  refine (measureReal_mono ?_ (measure_ne_top _ _)).trans (hn 1 ⟨le_rfl, le_rfl⟩)
  rintro ω ⟨s, hs_le, hnot_onset⟩
  let u := pathPauliDisorderShell ω n
  let H : selfAdjoint (Register (n + 2)) := ⟨pathHamiltonian u, isSelfAdjoint_pathHamiltonian u⟩
  have hafford : HasProjectiveCircuitApproximation (n + 2) (1 / 10 : ℝ) s
      (unitaryEvolution H.val 1) := by
    by_contra hna
    obtain ⟨hlo, hhi, _, heq, _⟩ := tenthPlateauOnset_lt_of_not_affordable H zero_le_one hna
    exact hnot_onset ⟨hlo, hhi, heq⟩
  obtain ⟨z, hz, C, hC, herr⟩ := hafford
  obtain ⟨c_cut, hc_cut⟩ := many_crossed C
  have hcross_ge : (ε / 2) * (n + 1 : ℕ) ≤ ((crossed c_cut).card : ℝ) := by
    have hb : ((n + 1 : ℕ) : ℝ) ≤ (C.gateCount : ℝ) + 2 * ((crossed c_cut).card : ℝ) := by
      exact_mod_cast hc_cut
    have hCg : (C.gateCount : ℝ) ≤ (s : ℝ) := by exact_mod_cast hC
    linarith only [hb, hCg, hs_le]
  have hov : (199 / 200 : ℝ) ≤
      ‖inner ℂ (choiVector (unitaryEvolution H.val 1)) (choiVector C.eval.val)‖ := by
    have h := choiVector_inner_ge_of_opNorm_sub_le
      (unitaryEvolution_mem_unitary H.2 1) C.eval.2 hz (by norm_num) herr
    linarith only [h]
  exact ⟨C, c_cut, hcross_ge, hov⟩

/-! ## Section 4: Universal multi-cut bipartite rank ceiling and Heisenberg Krylov remainder -/

/-- An operator `M : Register N` has bipartite operator rank at most `r` across `(A, Aᶜ)` if it
decomposes as `∑_{m < r} X_m * Y_m` with `X_m` site-supported on `A` and `Y_m` on `Aᶜ`. -/
def HasBipartiteOperatorRank {N : ℕ} (A : Finset (Fin N)) (r : ℕ) (M : Register N) : Prop :=
  ∃ X Y : Fin r → Register N,
    (∀ m : Fin r, IsSiteSupported A (X m)) ∧
    (∀ m : Fin r, IsSiteSupported Aᶜ (Y m)) ∧
    M = ∑ m : Fin r, X m * Y m

theorem HasBipartiteOperatorRank.mono {N r₁ r₂ : ℕ} {A : Finset (Fin N)} {M : Register N}
    (hr : r₁ ≤ r₂) (h : HasBipartiteOperatorRank A r₁ M) :
    HasBipartiteOperatorRank A r₂ M := by
  obtain ⟨X, Y, hX, hY, rfl⟩ := h
  refine ⟨fun m => if hm : m.val < r₁ then X ⟨m.val, hm⟩ else 0,
    fun m => if hm : m.val < r₁ then Y ⟨m.val, hm⟩ else 0,
    fun m => by split_ifs with hm; exact hX _; exact IsSiteSupported.zero A,
    fun m => by split_ifs with hm; exact hY _; exact IsSiteSupported.zero Aᶜ, ?_⟩
  have hsum : (∑ m : Fin r₂,
      (if hm : m.val < r₁ then X ⟨m.val, hm⟩ else 0) *
      (if hm : m.val < r₁ then Y ⟨m.val, hm⟩ else 0)) =
      ∑ m ∈ Finset.univ.filter (fun m : Fin r₂ => m.val < r₁),
        (if hm : m.val < r₁ then X ⟨m.val, hm⟩ * Y ⟨m.val, hm⟩ else 0) := by
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun m _ => ?_
    split_ifs <;> simp
  rw [hsum]
  symm
  refine Finset.sum_bij (fun (k : Fin r₁) _ => Fin.castLE hr k) ?_ ?_ ?_ ?_
  · intro k _; exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, k.isLt⟩
  · intro k₁ _ k₂ _ heq; exact Fin.ext (congrArg Fin.val heq)
  · intro m hm
    have hlt := (Finset.mem_filter.mp hm).2
    exact ⟨⟨m.val, hlt⟩, Finset.mem_univ _, Fin.ext rfl⟩
  · intro k _
    simp [k.isLt]

theorem HasBipartiteOperatorRank.mul {N r₁ r₂ : ℕ} {A : Finset (Fin N)} {M₁ M₂ : Register N}
    (h₁ : HasBipartiteOperatorRank A r₁ M₁) (h₂ : HasBipartiteOperatorRank A r₂ M₂) :
    HasBipartiteOperatorRank A (r₁ * r₂) (M₁ * M₂) := by
  obtain ⟨X₁, Y₁, hX₁, hY₁, rfl⟩ := h₁
  obtain ⟨X₂, Y₂, hX₂, hY₂, rfl⟩ := h₂
  let e := finProdFinEquiv (m := r₁) (n := r₂)
  refine ⟨fun k => X₁ (e.symm k).1 * X₂ (e.symm k).2,
    fun k => Y₁ (e.symm k).1 * Y₂ (e.symm k).2,
    fun k => (hX₁ _).matrix_mul (hX₂ _),
    fun k => (hY₁ _).matrix_mul (hY₂ _), ?_⟩
  rw [← Equiv.sum_comp e.symm, Fintype.sum_prod_type, Finset.sum_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  have hcomm : Y₁ i * X₂ j = X₂ j * Y₁ i :=
    commute_of_isSiteSupported_disjoint Disjoint.disjoint_sdiff_left.symm
      (by simpa [Finset.compl_eq_univ_sdiff] using hY₁ i) (hX₂ j)
  calc (X₁ i * Y₁ i) * (X₂ j * Y₂ j)
      = X₁ i * (Y₁ i * X₂ j) * Y₂ j := by simp only [mul_assoc]
    _ = (X₁ i * X₂ j) * (Y₁ i * Y₂ j) := by rw [hcomm]; simp only [mul_assoc]

private theorem hasBipartiteOperatorRank_card_left {N : ℕ} (A : Finset (Fin N)) (M : Register N) :
    HasBipartiteOperatorRank A (4 ^ A.card) M := by
  classical
  let SubCfg := (A → Bool) × (A → Bool)
  have hcard : Fintype.card SubCfg = 4 ^ A.card := by
    simp only [SubCfg, Fintype.card_prod, Fintype.card_fun, Fintype.card_coe, Fintype.card_bool]
    rw [← pow_add, show A.card + A.card = 2 * A.card by omega, pow_mul]
    norm_num
  let eqv : Fin (4 ^ A.card) ≃ SubCfg :=
    (finCongr hcard.symm).trans (Fintype.equivFin SubCfg).symm
  let glue (u : A → Bool) (x : Config N) : Config N :=
    fun i => if hi : i ∈ A then u ⟨i, hi⟩ else x i
  let X_sub (uv : SubCfg) : Register N := fun x y =>
    if (∀ i : A, x i.1 = uv.1 i ∧ y i.1 = uv.2 i) ∧ (∀ i ∉ A, x i = y i) then 1 else 0
  let Y_sub (uv : SubCfg) : Register N := fun x y =>
    if ∀ i ∈ A, x i = y i then M (glue uv.1 x) (glue uv.2 y) else 0
  have hX_supp (uv : SubCfg) : IsSiteSupported A (X_sub uv) := by
    refine ⟨fun x y hdiff => ?_, fun x y x' y' hxA hyA hrest hrest' => ?_⟩
    · obtain ⟨i, hi, hne⟩ := hdiff
      dsimp only [X_sub]
      rw [if_neg]; rintro ⟨_, hall⟩; exact hne (hall i hi)
    · dsimp only [X_sub]
      have h1 : (∀ i : A, x i.1 = uv.1 i ∧ y i.1 = uv.2 i) ↔
          (∀ i : A, x' i.1 = uv.1 i ∧ y' i.1 = uv.2 i) :=
        forall_congr' fun i => by rw [hxA i.1 i.2, hyA i.1 i.2]
      have h2 : (∀ i ∉ A, x i = y i) ↔ (∀ i ∉ A, x' i = y' i) :=
        ⟨fun _ => hrest', fun _ => hrest⟩
      rw [h1, h2]
  have hY_supp (uv : SubCfg) : IsSiteSupported Aᶜ (Y_sub uv) := by
    refine ⟨fun x y hdiff => ?_, fun x y x' y' hxAc hyAc hrest hrest' => ?_⟩
    · obtain ⟨i, hi, hne⟩ := hdiff
      have hiA : i ∈ A := by simpa using hi
      dsimp only [Y_sub]
      rw [if_neg]; intro hall; exact hne (hall i hiA)
    · dsimp only [Y_sub]
      have hA_iff : (∀ i ∈ A, x i = y i) ↔ (∀ i ∈ A, x' i = y' i) :=
        ⟨fun _ i hi => hrest' i (by simpa using hi),
         fun _ i hi => hrest i (by simpa using hi)⟩
      have hg1 (u : A → Bool) : glue u x = glue u x' := by
        funext i; dsimp only [glue]; split_ifs with hi
        · rfl
        · exact hxAc i (Finset.mem_compl.mpr hi)
      have hg2 (u : A → Bool) : glue u y = glue u y' := by
        funext i; dsimp only [glue]; split_ifs with hi
        · rfl
        · exact hyAc i (Finset.mem_compl.mpr hi)
      rw [hA_iff, hg1, hg2]
  refine ⟨fun m => X_sub (eqv m), fun m => Y_sub (eqv m),
    fun m => hX_supp _, fun m => hY_supp _, ?_⟩
  rw [Equiv.sum_comp eqv]
  ext x y
  rw [Matrix.sum_apply]
  let uv₀ : SubCfg := (fun i => x i.1, fun i => y i.1)
  rw [Finset.sum_eq_single uv₀]
  · rw [Matrix.mul_apply]
    let z₀ : Config N := glue uv₀.2 x
    rw [Finset.sum_eq_single z₀]
    · have hxX : X_sub uv₀ x z₀ = 1 := by
        dsimp only [X_sub, z₀, glue, uv₀]
        rw [if_pos]
        exact ⟨fun i => ⟨rfl, dif_pos i.2⟩, fun i hi => (dif_neg hi).symm⟩
      have hzY : Y_sub uv₀ z₀ y = M x y := by
        dsimp only [Y_sub, z₀, glue, uv₀]
        rw [if_pos (fun i hi => by simp [hi])]
        congr 1
        · funext i; by_cases hi : i ∈ A <;> simp [hi]
        · funext i; by_cases hi : i ∈ A <;> simp [hi]
      rw [hxX, hzY, one_mul]
    · intro z _ hne
      dsimp only [X_sub]
      split_ifs with hcond
      · exfalso; apply hne; funext i
        dsimp only [z₀, glue, uv₀]
        by_cases hi : i ∈ A
        · rw [dif_pos hi]; exact (hcond.1 ⟨i, hi⟩).2
        · rw [dif_neg hi]; exact (hcond.2 i hi).symm
      · exact zero_mul _
    · intro h; exact (h (Finset.mem_univ z₀)).elim
  · intro uv _ huv_ne
    rw [Matrix.mul_apply]
    refine Finset.sum_eq_zero fun z _ => ?_
    dsimp only [X_sub, Y_sub]
    split_ifs with hXz hzy
    · exfalso; apply huv_ne
      ext i
      · exact (hXz.1 i).1.symm
      · exact ((hzy i.1 i.2).symm.trans (hXz.1 i).2).symm
    · exact mul_zero _
    · exact zero_mul _
    · exact zero_mul _
  · intro h; exact (h (Finset.mem_univ uv₀)).elim

/-- Universal multi-cut entanglement-capacity ceiling: **every** operator `M : Register N`
(including every unitary `U(t)` on `Ω_conn(η)` at all times `t ∈ ℝ`) simultaneously satisfies
`HasBipartiteOperatorRank A (4 ^ min A.card Aᶜ.card) M` across **all** `2^N` cuts `A ⊆ Fin N`. -/
theorem universal_bipartiteOperatorRank_ceiling {N : ℕ} (A : Finset (Fin N)) (M : Register N) :
    HasBipartiteOperatorRank A (4 ^ min A.card Aᶜ.card) M := by
  rcases le_total A.card Aᶜ.card with hle | hle
  · rw [min_eq_left hle]
    exact hasBipartiteOperatorRank_card_left A M
  · rw [min_eq_right hle]
    obtain ⟨Y', X', hY', hX', hM⟩ := hasBipartiteOperatorRank_card_left Aᶜ M
    have hX_supp (m : Fin (4 ^ Aᶜ.card)) : IsSiteSupported A (X' m) := by
      simpa only [compl_compl] using hX' m
    refine ⟨X', Y', hX_supp, hY', ?_⟩
    rw [hM]
    refine Finset.sum_congr rfl fun m _ => ?_
    exact commute_of_isSiteSupported_disjoint Disjoint.disjoint_sdiff_left.symm
      (by simpa [Finset.compl_eq_univ_sdiff] using hY' m) (hX_supp m)

/-- Iterated commutator `(ad_H)^k(O)` in a ring `R`. -/
def iteratedCommutator {R : Type*} [Ring R] (H : R) : ℕ → R → R
  | 0, O => O
  | k + 1, O => iteratedCommutator H k (H * O - O * H)

private theorem iteratedCommutator_outer {R : Type*} [Ring R] (H : R) (k : ℕ) (O : R) :
    H * iteratedCommutator H k O - iteratedCommutator H k O * H =
      iteratedCommutator H (k + 1) O := by
  induction k generalizing O with
  | zero => rfl
  | succ k ih => exact ih (H * O - O * H)

private theorem iteratedCommutator_neg {A : Type*} [Ring A] [Module ℂ A] [IsScalarTower ℂ A A]
    [SMulCommClass ℂ A A] (H : A) (k : ℕ) (O : A) :
    iteratedCommutator (-H) k O = ((-1 : ℂ) ^ k) • iteratedCommutator H k O := by
  induction k generalizing O with
  | zero => simp [iteratedCommutator]
  | succ k ih =>
      have hcomm_neg : (-H) * O - O * (-H) = (-1 : ℂ) • (H * O - O * H) := by
        rw [neg_mul, mul_neg, sub_neg_eq_add, neg_one_smul, neg_sub]
        abel
      have hsmul (c : ℂ) (m : ℕ) (X : A) :
          iteratedCommutator H m (c • X) = c • iteratedCommutator H m X := by
        induction m generalizing X with
        | zero => rfl
        | succ m ihm =>
            dsimp only [iteratedCommutator]
            have h1 : H * (c • X) - (c • X) * H = c • (H * X - X * H) := by
              rw [mul_smul_comm, smul_mul_assoc, ← smul_sub]
            rw [h1, ihm]
      dsimp only [iteratedCommutator]
      rw [ih, hcomm_neg, hsmul, smul_smul, pow_succ']

theorem norm_iteratedCommutator_le {A : Type*} [NormedRing A] (H : A) (k : ℕ) (O : A) :
    ‖iteratedCommutator H k O‖ ≤ (2 * ‖H‖) ^ k * ‖O‖ := by
  induction k generalizing O with
  | zero => simp [iteratedCommutator]
  | succ k ih =>
      dsimp only [iteratedCommutator]
      have h1 : ‖H * O - O * H‖ ≤ 2 * ‖H‖ * ‖O‖ := by
        have ha := norm_mul_le H O
        have hb := norm_mul_le O H
        linarith only [norm_sub_le (H * O) (O * H), ha, hb]
      have h2H_nn : 0 ≤ 2 * ‖H‖ := mul_nonneg two_pos.le (norm_nonneg H)
      calc ‖iteratedCommutator H k (H * O - O * H)‖
          ≤ (2 * ‖H‖) ^ k * ‖H * O - O * H‖ := ih (H * O - O * H)
        _ ≤ (2 * ‖H‖) ^ k * (2 * ‖H‖ * ‖O‖) :=
            mul_le_mul_of_nonneg_left h1 (pow_nonneg h2H_nn k)
        _ = (2 * ‖H‖) ^ (k + 1) * ‖O‖ := by rw [pow_succ]; ring

/-- Heisenberg observable evolution `U(t)* O U(t)` in an abstract `C*`-algebra `A`. -/
def heisenbergOrbit {A : Type*} [CStarAlgebra A] (H O : A) (t : ℝ) : A :=
  star (exp (t • ((-Complex.I) • H))) * O * exp (t • ((-Complex.I) • H))

/-- Degree-`K` commutator-Krylov Taylor polynomial of `heisenbergOrbit H O t`. -/
def heisenbergCommutatorTaylor {A : Type*} [CStarAlgebra A] (H O : A) (K : ℕ) (t : ℝ) : A :=
  ∑ k ∈ Finset.range (K + 1),
    (((t ^ k / (k.factorial : ℝ) : ℝ) : ℂ) * Complex.I ^ k) • iteratedCommutator H k O

/-- Commutator-Krylov subspace `span_ℂ { (ad_H)^k(O) : k ≤ K }` in `A`. -/
def commutatorKrylovSubspace {A : Type*} [CStarAlgebra A] (H O : A) (K : ℕ) : Submodule ℂ A :=
  Submodule.span ℂ (range fun k : Fin (K + 1) => iteratedCommutator H k.val O)

theorem heisenbergCommutatorTaylor_mem_commutatorKrylovSubspace {A : Type*} [CStarAlgebra A]
    (H O : A) (K : ℕ) (t : ℝ) :
    heisenbergCommutatorTaylor H O K t ∈ commutatorKrylovSubspace H O K := by
  unfold heisenbergCommutatorTaylor
  refine Submodule.sum_mem _ fun k hk => Submodule.smul_mem _ _ ?_
  exact Submodule.subset_span ⟨⟨k, Finset.mem_range.mp hk⟩, rfl⟩

private theorem heisenbergOrbit_eq_twoSided_exp {A : Type*} [CStarAlgebra A]
    {H : A} (hH : IsSelfAdjoint H) (O : A) (t : ℝ) :
    heisenbergOrbit H O t =
      exp (t • (Complex.I • H)) * O * exp (t • ((-Complex.I) • H)) := by
  let _ : NormedAlgebra ℚ A := .restrictScalars ℚ ℂ A
  unfold heisenbergOrbit
  congr 2
  have hx : (-Complex.I) • H ∈ skewAdjoint A := by
    rw [skewAdjoint.mem_iff, star_smul, hH.star_eq]; simp
  have hunit := exp_mem_unitary_of_mem_skewAdjoint (skewAdjoint.smul_mem t hx)
  have hprod : exp (t • (Complex.I • H)) * exp (t • ((-Complex.I) • H)) = 1 := by
    have hadd : t • (Complex.I • H) + t • ((-Complex.I) • H) = 0 := by
      rw [← smul_add, neg_smul, add_neg_cancel, smul_zero]
    have hcomm : Commute (t • (Complex.I • H)) (t • ((-Complex.I) • H)) := by
      rw [show t • ((-Complex.I) • H) = -(t • (Complex.I • H)) by rw [neg_smul, smul_neg]]
      exact (Commute.refl _).neg_right
    rw [← exp_add_of_commute hcomm, hadd, exp_zero]
  calc star (exp (t • ((-Complex.I) • H)))
      = 1 * star (exp (t • ((-Complex.I) • H))) := (one_mul _).symm
    _ = (exp (t • (Complex.I • H)) * exp (t • ((-Complex.I) • H))) *
          star (exp (t • ((-Complex.I) • H))) := by rw [hprod]
    _ = exp (t • (Complex.I • H)) *
          (exp (t • ((-Complex.I) • H)) * star (exp (t • ((-Complex.I) • H)))) := mul_assoc _ _ _
    _ = exp (t • (Complex.I • H)) := by rw [(Unitary.mem_iff.mp hunit).2, mul_one]

private theorem hasDerivAt_twoSided_exp {A : Type*} [CStarAlgebra A] (H B : A) (t : ℝ) :
    HasDerivAt (fun s : ℝ => exp (s • (Complex.I • H)) * B * exp (s • ((-Complex.I) • H)))
      (exp (t • (Complex.I • H)) * (Complex.I • (H * B - B * H)) *
        exp (t • ((-Complex.I) • H))) t := by
  let _ : NormedAlgebra ℚ A := .restrictScalars ℚ ℂ A
  let y := Complex.I • H
  let x := (-Complex.I) • H
  have hcomm_y : y * exp (t • y) = exp (t • y) * y :=
    ((Commute.refl y).smul_right t).exp_right
  have hd1 : HasDerivAt (fun s : ℝ => exp (s • y)) (exp (t • y) * y) t := by
    rw [← hcomm_y]; exact hasDerivAt_exp_smul_const' (𝕂 := ℝ) y t
  have hd2 : HasDerivAt (fun s : ℝ => exp (s • x)) (x * exp (t • x)) t :=
    hasDerivAt_exp_smul_const' (𝕂 := ℝ) x t
  have hd := (hd1.mul_const B).mul hd2
  have halg : ((exp (t • y) * y) * B) * exp (t • x) + (exp (t • y) * B) * (x * exp (t • x)) =
      exp (t • y) * (Complex.I • (H * B - B * H)) * exp (t • x) := by
    have h1 : ((exp (t • y) * y) * B) * exp (t • x) + (exp (t • y) * B) * (x * exp (t • x)) =
        exp (t • y) * (y * B + B * x) * exp (t • x) := by noncomm_ring
    have h2 : y * B + B * x = Complex.I • (H * B - B * H) := by
      dsimp only [y, x]
      rw [smul_mul_assoc, mul_smul_comm, neg_smul, smul_sub, sub_eq_add_neg]
    rw [h1, h2]
  rwa [halg] at hd

private theorem iteratedDeriv_twoSided_exp {A : Type*} [CStarAlgebra A] (H O : A) (k : ℕ) :
    iteratedDeriv k (fun s : ℝ => exp (s • (Complex.I • H)) * O * exp (s • ((-Complex.I) • H))) =
      fun s : ℝ => exp (s • (Complex.I • H)) *
        ((Complex.I ^ k) • iteratedCommutator H k O) * exp (s • ((-Complex.I) • H)) := by
  induction k with
  | zero => simp [iteratedDeriv_zero, iteratedCommutator]
  | succ k ih =>
      rw [iteratedDeriv_succ, ih]
      funext s
      rw [(hasDerivAt_twoSided_exp H ((Complex.I ^ k) • iteratedCommutator H k O) s).deriv]
      congr 2
      rw [mul_smul_comm, smul_mul_assoc, ← smul_sub, smul_smul, ← pow_succ',
        iteratedCommutator_outer]

/-- Sharp `C*`-algebra Heisenberg commutator-Krylov remainder without exponential prefactor:
for every self-adjoint `H`, every observable `O`, every `K ∈ ℕ`, and every `t ∈ ℝ`,
`‖U(t)* O U(t) - ∑_{k ≤ K} (t^k / k!) i^k ad_H^k(O)‖ ≤ (2 ‖H‖ |t|)^(K + 1) / (K + 1)! * ‖O‖`. -/
theorem norm_heisenbergOrbit_sub_commutatorTaylor_le {A : Type*} [CStarAlgebra A]
    {H : A} (hH : IsSelfAdjoint H) (O : A) (K : ℕ) (t : ℝ) :
    ‖heisenbergOrbit H O t - heisenbergCommutatorTaylor H O K t‖ ≤
      (2 * ‖H‖ * |t|) ^ (K + 1) / ((K + 1).factorial : ℝ) * ‖O‖ := by
  let _ : NormedAlgebra ℚ A := .restrictScalars ℚ ℂ A
  have hnonneg : ∀ {G : A}, IsSelfAdjoint G → ∀ {u : ℝ}, 0 ≤ u →
      ‖heisenbergOrbit G O u - heisenbergCommutatorTaylor G O K u‖ ≤
        ((2 * ‖G‖) ^ (K + 1) * ‖O‖) * u ^ (K + 1) / ((K + 1).factorial : ℝ) := by
    intro G hG u hu
    let f : ℝ → A := fun s => exp (s • (Complex.I • G)) * O * exp (s • ((-Complex.I) • G))
    have hf_eq (s : ℝ) : heisenbergOrbit G O s = f s := heisenbergOrbit_eq_twoSided_exp hG O s
    have hf_smooth (m : ℕ) : ContDiff ℝ m f :=
      contDiff_of_differentiable_iteratedDeriv (f := f) (n := m) fun k _ => by
        rw [iteratedDeriv_twoSided_exp G O k]
        exact fun s => (hasDerivAt_twoSided_exp G _ s).differentiableAt
    rcases eq_or_lt_of_le hu with rfl | hu_pos
    · have ht0 : heisenbergCommutatorTaylor G O K 0 = O := by
        unfold heisenbergCommutatorTaylor
        rw [Finset.sum_eq_single 0]
        · simp [iteratedCommutator]
        · intro k _ hk0; rw [zero_pow hk0, zero_div, Complex.ofReal_zero, zero_mul, zero_smul]
        · simp
      have ho0 : heisenbergOrbit G O 0 = O := by simp [heisenbergOrbit]
      rw [ho0, ht0, sub_self, norm_zero, zero_pow (Nat.succ_ne_zero K), mul_zero, zero_div]
    · have htaylor_eq : taylorWithinEval f K (Icc 0 u) 0 u =
          heisenbergCommutatorTaylor G O K u := by
        rw [taylor_within_apply]
        unfold heisenbergCommutatorTaylor
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Icc hu_pos)
          ((hf_smooth k).contDiffAt) (left_mem_Icc.mpr hu),
          congrFun (iteratedDeriv_twoSided_exp G O k) 0]
        simp only [sub_zero, zero_smul, exp_zero, one_mul, mul_one]
        rw [← Complex.real_smul, smul_smul]
        congr 1; push_cast; ring
      rw [hf_eq u, ← htaylor_eq]
      refine norm_sub_taylorWithinEval_le_factorial hu (hf_smooth (K + 1)).contDiffOn
        fun s hs => ?_
      rw [iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Icc hu_pos)
        ((hf_smooth (K + 1)).contDiffAt) hs,
        congrFun (iteratedDeriv_twoSided_exp G O (K + 1)) s]
      have hy_skew : Complex.I • G ∈ skewAdjoint A := by
        rw [skewAdjoint.mem_iff, star_smul, hG.star_eq]; simp
      have hx_skew : (-Complex.I) • G ∈ skewAdjoint A := by
        rw [skewAdjoint.mem_iff, star_smul, hG.star_eq]; simp
      have huL : ‖exp (s • (Complex.I • G))‖ = 1 :=
        CStarRing.norm_of_mem_unitary
          (exp_mem_unitary_of_mem_skewAdjoint (skewAdjoint.smul_mem s hy_skew))
      have huR : ‖exp (s • ((-Complex.I) • G))‖ = 1 :=
        CStarRing.norm_of_mem_unitary
          (exp_mem_unitary_of_mem_skewAdjoint (skewAdjoint.smul_mem s hx_skew))
      calc ‖exp (s • (Complex.I • G)) *
              ((Complex.I ^ (K + 1)) • iteratedCommutator G (K + 1) O) *
              exp (s • ((-Complex.I) • G))‖
          ≤ ‖exp (s • (Complex.I • G)) *
              ((Complex.I ^ (K + 1)) • iteratedCommutator G (K + 1) O)‖ *
              ‖exp (s • ((-Complex.I) • G))‖ := norm_mul_le _ _
        _ ≤ (‖exp (s • (Complex.I • G))‖ *
              ‖(Complex.I ^ (K + 1)) • iteratedCommutator G (K + 1) O‖) * 1 :=
            mul_le_mul (norm_mul_le _ _) huR.le (norm_nonneg _)
              (mul_nonneg (norm_nonneg _) (norm_nonneg _))
        _ = ‖iteratedCommutator G (K + 1) O‖ := by
            rw [huL, one_mul, mul_one, norm_smul, norm_pow, Complex.norm_I, one_pow, one_mul]
        _ ≤ (2 * ‖G‖) ^ (K + 1) * ‖O‖ := norm_iteratedCommutator_le G (K + 1) O
  by_cases ht : 0 ≤ t
  · have h := hnonneg hH ht
    rw [abs_of_nonneg ht]
    refine h.trans_eq ?_
    rw [mul_pow]; ring
  · have ht_neg : t < 0 := lt_of_not_ge ht
    have hH_neg : IsSelfAdjoint (-H) := by rw [IsSelfAdjoint, star_neg, hH.star_eq]
    have h := hnonneg hH_neg (show 0 ≤ -t by linarith only [ht_neg])
    have horb_eq : heisenbergOrbit (-H) O (-t) = heisenbergOrbit H O t := by
      unfold heisenbergOrbit
      have hexp_eq : (-t) • ((-Complex.I) • (-H)) = t • ((-Complex.I) • H) := by
        rw [smul_neg, neg_smul, neg_smul, neg_neg]
      rw [hexp_eq]
    have htay_eq : heisenbergCommutatorTaylor (-H) O K (-t) =
        heisenbergCommutatorTaylor H O K t := by
      unfold heisenbergCommutatorTaylor
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [iteratedCommutator_neg, smul_smul]
      congr 1
      have hp : (-t) ^ k = (-1 : ℝ) ^ k * t ^ k := by rw [← mul_pow]; ring
      rw [hp]
      push_cast; ring
    rw [horb_eq, htay_eq, norm_neg] at h
    rw [abs_of_neg ht_neg]
    refine h.trans_eq ?_
    rw [mul_pow]; ring

/-! ## Section 5: Exact `(n + 1)`-gate diagonal Ising synthesis and strong-bond survival tube -/

private theorem twoQubitLiftMatrix_diagonal {N : ℕ} (a b : Fin N) (hab : a ≠ b)
    (d : Bool × Bool → ℂ) :
    twoQubitLiftMatrix a b hab (Matrix.diagonal d) =
      Matrix.diagonal (fun x : Config N => d (x a, x b)) := by
  ext x y
  by_cases hxy : x = y
  · subst hxy
    simp [twoQubitLiftMatrix, splitTwoQubitConfig, Matrix.kronecker]
  · rw [Matrix.diagonal_apply_ne _ hxy]
    dsimp only [twoQubitLiftMatrix, Matrix.reindex_apply, Matrix.submatrix_apply]
    rw [Equiv.symm_symm]
    let sx := splitTwoQubitConfig a b hab x
    let sy := splitTwoQubitConfig a b hab y
    change (Matrix.kroneckerMap (· * ·) (Matrix.diagonal d) 1) sx sy = 0
    rw [Matrix.kroneckerMap_apply]
    by_cases hp : sx.1 = sy.1
    · have hrest_ne : sx.2 ≠ sy.2 := fun hr =>
        hxy ((splitTwoQubitConfig a b hab).injective (Prod.ext hp hr))
      rw [Matrix.one_apply_ne hrest_ne, mul_zero]
    · rw [Matrix.diagonal_apply_ne _ hp, zero_mul]

private theorem realizes_one_twoSite_diagonal {N : ℕ} (a b : Fin N) (hab : a ≠ b)
    (g : Bool × Bool → ℝ) (t : ℝ) :
    Realizes 1 (Matrix.diagonal fun x : Config N =>
      Complex.exp (-(Complex.I * ((t : ℂ) * ((g (x a, x b) : ℝ) : ℂ))))) := by
  let B : Matrix (Bool × Bool) (Bool × Bool) ℂ :=
    Matrix.diagonal fun pq => ((g pq : ℝ) : ℂ)
  have hB : IsSelfAdjoint B := by
    rw [IsSelfAdjoint, Matrix.star_eq_conjTranspose, Matrix.diagonal_conjTranspose]
    congr 1; funext pq; simp
  let Ulocal : Matrix.unitaryGroup (Bool × Bool) ℂ :=
    ⟨unitaryEvolution B t, unitaryEvolution_mem_unitary hB t⟩
  let z := scalarSpecialUnitaryPhase Ulocal
  let G := scalarSpecialUnitaryRepresentative Ulocal
  have hzunit : star z * z = 1 := scalarSpecialUnitaryPhase_unitary Ulocal
  have hznorm : ‖star z‖ = 1 := by
    have hnorm := congrArg norm hzunit
    have hsq : ‖z‖ * ‖z‖ = 1 := by simpa [norm_mul] using hnorm
    have hz : ‖z‖ = 1 := by nlinarith [norm_nonneg z, sq_nonneg (‖z‖ - 1)]
    simpa using hz
  refine ⟨star z, hznorm, TwoQubitCircuit.singleOn a b hab G, le_rfl, ?_⟩
  rw [TwoQubitCircuit.singleOn_eval]
  have hgate : (twoQubitLift a b hab G : Register N) =
      z • twoQubitLiftMatrix a b hab (unitaryEvolution B t) := by
    ext x y
    simp [G, z, Ulocal, twoQubitLift, twoQubitLiftMatrix,
      specialUnitaryAsUnitary, scalarSpecialUnitaryRepresentative_coe,
      unitaryGroupReindex_coe, Quantum.tensorGate_val,
      Matrix.reindex_apply, Matrix.kronecker, Matrix.smul_apply]
    ring
  rw [hgate, smul_smul, hzunit, one_smul, ← unitaryEvolution_twoQubitLiftMatrix,
    twoQubitLiftMatrix_diagonal, unitaryEvolution_diagonal]
  congr 1; funext x; congr 1
  simp only [Complex.real_smul]
  ring

/-- Every diagonal `Z`/`ZZ` chain Hamiltonian on `n + 2` qubits (`∀ l, ¬ IsDiagLabel l → u l = 0`)
is synthesized **exactly** for all `t ∈ ℝ` by `n + 1` two-qubit gates (one gate per bond). -/
theorem realizes_one_gate_per_bond_of_isDiag {n : ℕ} (u : PathShell n)
    (hu : ∀ l : PathLabel n, ¬ IsDiagLabel l → u l = 0) (t : ℝ) :
    Realizes (n + 1) (unitaryEvolution (pathHamiltonian u) t) := by
  let bSign (b : Bool) : ℝ := if b then -1 else 1
  let gBond (e : Fin (n + 1)) (pq : Bool × Bool) : ℝ :=
    (if e.val = 0 then u (.inl (0, 2)) * bSign pq.1 else 0) +
      u (.inl (e.succ, 2)) * bSign pq.2 +
      u (.inr (e, (2, 2))) * (bSign pq.1 * bSign pq.2)
  have hsum_energy (x : Config (n + 2)) :
      pathDiagEnergy u x = ∑ e : Fin (n + 1), gBond e (x e.castSucc, x e.succ) := by
    unfold pathDiagEnergy
    have hz1 (s : Fin (n + 2)) : zSetSign ({s} : Finset (Fin (n + 2))) x = bSign (x s) := by
      rw [zSetSign_singleton]
    have hz2 (e : Fin (n + 1)) :
        zSetSign ({e.castSucc, e.succ} : Finset (Fin (n + 2))) x =
          bSign (x e.castSucc) * bSign (x e.succ) := by
      rw [zSetSign_pair_eq]; rfl
    simp_rw [hz1, hz2, gBond]
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
    congr 1
    rw [← Fin.sum_univ_succ (fun s : Fin (n + 2) => u (.inl (s, 2)) * bSign (x s))]
    have he0 : (∑ e : Fin (n + 1),
        if e.val = 0 then u (.inl (0, 2)) * bSign (x e.castSucc) else 0) =
        u (.inl (0, 2)) * bSign (x 0) := by
      rw [Finset.sum_eq_single (0 : Fin (n + 1))]
      · simp
      · intro e _ he
        rw [if_neg (Fin.val_ne_of_ne he)]
      · simp
    rw [he0]
  let U_part (S : Finset (Fin (n + 1))) : Register (n + 2) :=
    Matrix.diagonal fun x : Config (n + 2) =>
      Complex.exp (-(Complex.I * ((t : ℂ) *
        ((∑ e ∈ S, gBond e (x e.castSucc, x e.succ) : ℝ) : ℂ))))
  have hpart (S : Finset (Fin (n + 1))) : Realizes S.card (U_part S) := by
    induction S using Finset.induction_on with
    | empty =>
        have h1 : U_part ∅ = 1 := by
          ext x y
          by_cases hxy : x = y
          · subst hxy; simp [U_part]
          · simp [U_part, hxy]
        rw [Finset.card_empty, h1]
        exact Realizes.one (n + 2)
    | @insert e S he ih =>
        have hstep := realizes_one_twoSite_diagonal e.castSucc e.succ
          (Fin.castSucc_lt_succ (i := e)).ne (gBond e) t
        have hmul_eq : U_part (insert e S) =
            (Matrix.diagonal fun x : Config (n + 2) =>
              Complex.exp (-(Complex.I * ((t : ℂ) * ((gBond e (x e.castSucc, x e.succ) : ℝ) : ℂ))))) *
              U_part S := by
          dsimp only [U_part]
          rw [Matrix.diagonal_mul_diagonal]
          congr 1; funext x
          rw [Finset.sum_insert he, Complex.ofReal_add, ← Complex.exp_add]
          congr 1; ring
        rw [Finset.card_insert_of_notMem he, hmul_eq, Nat.add_comm]
        exact hstep.mul ih
  have htot := hpart Finset.univ
  rw [Finset.card_univ, Fintype.card_fin] at htot
  have hev_eq : unitaryEvolution (pathHamiltonian u) t = U_part Finset.univ := by
    rw [pathHamiltonian_eq_diagonal u hu, unitaryEvolution_diagonal]
    dsimp only [U_part]
    congr 1; funext x; congr 1
    rw [hsum_energy x]
    simp only [Complex.real_smul]
    ring
  rwa [← hev_eq] at htot

private theorem scalarReturnExcised_of_onsiteZ {k : ℕ} (u : PathShell (k + 1))
    (honsiteZ : 3 ≤ |u (.inl (0, 2))|) :
    ∃ t₀ ∈ Ioo (0 : ℝ) (Real.pi / 2),
      ∀ z : ℂ, ‖z‖ = 1 →
        Real.sqrt 2 ≤ ‖unitaryEvolution (pathHamiltonian u) t₀ - z • (1 : Register (k + 3))‖ := by
  let H : selfAdjoint (Register (k + 3)) := ⟨pathHamiltonian u, isSelfAdjoint_pathHamiltonian u⟩
  -- 1. 3 ≤ ‖H.val‖ via Pauli trace projection onto onsite Z_0
  have hH_ge3 : (3 : ℝ) ≤ ‖H.val‖ := by
    let W := finitePauliMatrix (onsiteWord (0 : Fin (k + 3)) 2)
    have hW_unit : W ∈ unitary (Register (k + 3)) := finitePauliMatrix_mem_unitary _
    have hW_norm : ‖star W‖ = 1 := by
      rw [norm_star]; exact CStarRing.norm_of_mem_unitary hW_unit
    have htr_eq : Matrix.trace (star W * H.val) =
        ((2 ^ (k + 3) : ℕ) : ℂ) * ((u (.inl (0, 2)) : ℝ) : ℂ) := by
      change Matrix.trace (star W * pathHamiltonian u) = _
      rw [pathHamiltonian_eq_sum, Matrix.mul_sum, Matrix.trace_sum,
        Finset.sum_eq_single (Sum.inl ((0 : Fin (k + 3)), (2 : Fin 3)))]
      · rw [Matrix.mul_smul, Matrix.trace_smul]
        have h1 : star W * W = 1 := (Unitary.mem_iff.mp hW_unit).1
        change _ • Matrix.trace (star W * W) = _
        rw [h1, Matrix.trace_one, Fintype.card_fun, Fintype.card_fin, Fintype.card_bool,
          smul_eq_mul, mul_comm]
        push_cast; rfl
      · intro l _ hne
        rw [Matrix.mul_smul, Matrix.trace_smul]
        have hword_ne : onsiteWord (0 : Fin (k + 3)) 2 ≠ pathWord l := by
          intro hw
          rcases l with ⟨s, q⟩ | ⟨e, pq⟩
          · by_cases hs : s = 0
            · subst hs
              have h0 := congrFun hw 0
              simp only [onsiteWord, pathWord, if_true, Option.some.injEq] at h0
              exact hne (by subst h0; rfl)
            · have h0 := congrFun hw s
              simp [onsiteWord, pathWord, hs] at h0
          · have h1 := congrFun hw e.castSucc
            have h2 := congrFun hw e.succ
            have hlt := Fin.castSucc_lt_succ (i := e)
            by_cases hc : e.castSucc = 0
            · have hs0 : e.succ ≠ 0 := fun h => hlt.ne (hc.trans h.symm)
              simp [onsiteWord, pathWord, couplingWord, hs0, hlt.ne'] at h2
            · simp [onsiteWord, pathWord, couplingWord, hc] at h1
        rw [finitePauliMatrix_trace_star_mul_eq_zero_of_ne _ _ hword_ne, smul_zero]
      · simp
    have htr_le := norm_trace_le_card_mul_l2_opNorm (star W * H.val)
    have hcard : (Fintype.card (Config (k + 3)) : ℝ) = (2 : ℝ) ^ (k + 3) := by simp [Config]
    rw [htr_eq, norm_mul, Complex.norm_natCast, Nat.cast_pow, Nat.cast_ofNat,
      Complex.norm_real, Real.norm_eq_abs, hcard] at htr_le
    have hmul_le : ‖star W * H.val‖ ≤ ‖H.val‖ :=
      (norm_mul_le _ _).trans (by rw [hW_norm, one_mul])
    have h2pos : (0 : ℝ) < (2 : ℝ) ^ (k + 3) := pow_pos two_pos _
    exact honsiteZ.trans
      (le_of_mul_le_mul_left (htr_le.trans (mul_le_mul_of_nonneg_left hmul_le h2pos.le)) h2pos)
  -- 2. Tr(H) = 0
  have htr0 : Matrix.trace H.val = 0 := by
    rw [show H.val = pathHamiltonian u from rfl, pathHamiltonian_eq_sum, Matrix.trace_sum]
    refine Finset.sum_eq_zero fun l _ => ?_
    rw [Matrix.trace_smul]
    have hne_id : pathWord l ≠ fun _ => none := by
      intro hid
      rcases l with ⟨s, p⟩ | ⟨e, pq⟩
      · have hs := congrFun hid s; simp [pathWord, onsiteWord] at hs
      · have he := congrFun hid e.castSucc; simp [pathWord, couplingWord] at he
    rw [finitePauliMatrix_trace_eq_zero_of_ne_identity _ hne_id, smul_zero]
  -- 3. Eigenvalue spread E_max - E_min ≥ 3 and antipodal phase at t₀ = π / ΔE
  let V := hermitianEigenbasisUnitary H.2.isHermitian
  let E := H.2.isHermitian.eigenvalues
  have hspec : H.val = V.val * Matrix.diagonal (Complex.ofReal ∘ E) * star V.val :=
    H.2.isHermitian.spectral_theorem
  have hsum_E : (∑ c : Config (k + 3), E c) = 0 := by
    have htr_spec : Matrix.trace H.val = ∑ c : Config (k + 3), (E c : ℂ) := by
      rw [hspec, Matrix.trace_mul_comm, ← mul_assoc, (Unitary.mem_iff.mp V.2).1, one_mul,
        Matrix.trace]
      simp [Matrix.diagonal]
    rw [htr0] at htr_spec
    exact Complex.ofReal_injective (by simpa [Complex.ofReal_sum] using htr_spec.symm)
  have huniv_ne : (Finset.univ : Finset (Config (k + 3))).Nonempty :=
    ⟨fun _ => false, Finset.mem_univ _⟩
  obtain ⟨c_max, _, hc_max⟩ := Finset.exists_max_image Finset.univ E huniv_ne
  obtain ⟨c_min, _, hc_min⟩ := Finset.exists_min_image Finset.univ E huniv_ne
  obtain ⟨c_abs, _, hc_abs⟩ := Finset.exists_max_image Finset.univ (fun c => |E c|) huniv_ne
  have hE_max_nn : 0 ≤ E c_max := by
    by_contra hlt; push Not at hlt
    linarith only [hsum_E,
      Finset.sum_neg (fun c _ => (hc_max c (Finset.mem_univ c)).trans_lt hlt) huniv_ne]
  have hE_min_np : E c_min ≤ 0 := by
    by_contra hgt; push Not at hgt
    linarith only [hsum_E,
      Finset.sum_pos (fun c _ => hgt.trans_le (hc_min c (Finset.mem_univ c))) huniv_ne]
  have hH_le_abs : ‖H.val‖ ≤ |E c_abs| := by
    have hiso := l2_opNorm_unitary_conj_eq (Unitary.star_mem V.2) H.val
    have hconj : star V.val * H.val * V.val = Matrix.diagonal (Complex.ofReal ∘ E) := by
      rw [hspec]; exact star_conj_cancel V.2 _
    rw [star_star, hconj] at hiso
    rw [← hiso, ← Matrix.l2_opNorm_toEuclideanCLM]
    refine (Matrix.toEuclideanCLM (n := Config (k + 3)) (𝕜 := ℂ)
      (Matrix.diagonal (Complex.ofReal ∘ E))).opNorm_le_bound (abs_nonneg _) fun ψ => ?_
    have hsq : ‖Matrix.toEuclideanCLM (n := Config (k + 3)) (𝕜 := ℂ)
        (Matrix.diagonal (Complex.ofReal ∘ E)) ψ‖ ^ 2 ≤ (|E c_abs| * ‖ψ‖) ^ 2 := by
      rw [EuclideanSpace.norm_sq_eq, mul_pow, EuclideanSpace.norm_sq_eq, Finset.mul_sum]
      refine Finset.sum_le_sum fun c _ => ?_
      have hcoord : (Matrix.toEuclideanCLM (n := Config (k + 3)) (𝕜 := ℂ)
          (Matrix.diagonal (Complex.ofReal ∘ E)) ψ).ofLp c = (E c : ℂ) * ψ.ofLp c := by
        rw [Matrix.ofLp_toEuclideanCLM, Matrix.mulVec_diagonal]; rfl
      change ‖(Matrix.toEuclideanCLM (n := Config (k + 3)) (𝕜 := ℂ)
        (Matrix.diagonal (Complex.ofReal ∘ E)) ψ).ofLp c‖ ^ 2 ≤ _
      rw [hcoord, norm_mul, mul_pow, Complex.norm_real, Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_right
        (pow_le_pow_left₀ (abs_nonneg _) (hc_abs c (Finset.mem_univ c)) 2) (sq_nonneg _)
    exact (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (abs_nonneg _) (norm_nonneg _))).mp hsq
  have hgap_ge3 : 3 ≤ E c_max - E c_min := by
    have h3_abs : 3 ≤ |E c_abs| := hH_ge3.trans hH_le_abs
    rcases le_or_gt 0 (E c_abs) with hnn | hneg
    · rw [abs_of_nonneg hnn] at h3_abs
      linarith only [h3_abs, hc_max c_abs (Finset.mem_univ c_abs), hE_min_np]
    · rw [abs_of_neg hneg] at h3_abs
      linarith only [h3_abs, hc_min c_abs (Finset.mem_univ c_abs), hE_max_nn]
  let ΔE := E c_max - E c_min
  have hΔE_pos : 0 < ΔE := by linarith only [hgap_ge3]
  let t₀ := Real.pi / ΔE
  refine ⟨t₀, ⟨div_pos Real.pi_pos hΔE_pos,
    div_lt_div_of_pos_left Real.pi_pos two_pos (by linarith only [hgap_ge3])⟩, fun z hz => ?_⟩
  let D_t₀ := Matrix.diagonal fun i => Complex.exp (-(Complex.I * (t₀ * E i)))
  have hconj_t₀ : star V.val * (unitaryEvolution H.val t₀ - z • (1 : Register (k + 3))) * V.val =
      D_t₀ - z • (1 : Register (k + 3)) := by
    rw [unitaryEvolution_spectral H.2.isHermitian t₀]
    change star V.val * (V.val * D_t₀ * star V.val - z • 1) * V.val = _
    rw [Matrix.mul_sub, Matrix.sub_mul, star_conj_cancel V.2, Matrix.mul_smul, Matrix.smul_mul,
      Matrix.mul_one, (Unitary.mem_iff.mp V.2).1]
  have hiso := l2_opNorm_unitary_conj_eq (Unitary.star_mem V.2)
    (unitaryEvolution H.val t₀ - z • (1 : Register (k + 3)))
  rw [star_star, hconj_t₀] at hiso
  rw [← hiso]
  let w₁ : ℂ := Complex.exp (-(Complex.I * (t₀ * E c_max)))
  let w₂ : ℂ := Complex.exp (-(Complex.I * (t₀ * E c_min)))
  have hw₁_norm : ‖w₁‖ = 1 := by
    dsimp only [w₁]; rw [Complex.norm_exp]
    have hre : (-(Complex.I * (↑t₀ * ↑(E c_max)))).re = 0 := by simp
    rw [hre, Real.exp_zero]
  have hw₂_eq : w₂ = -w₁ := by
    dsimp only [w₁, w₂]
    have harg : -(Complex.I * (↑t₀ * ↑(E c_min))) =
        -(Complex.I * (↑t₀ * ↑(E c_max))) + ↑Real.pi * Complex.I := by
      have htΔ : t₀ * ΔE = Real.pi := div_mul_cancel₀ Real.pi hΔE_pos.ne'
      have hcast : (t₀ : ℂ) * ((E c_max : ℂ) - (E c_min : ℂ)) = (Real.pi : ℂ) := by
        exact_mod_cast htΔ
      linear_combination Complex.I * hcast
    rw [harg, Complex.exp_add, Complex.exp_pi_mul_I, mul_neg, mul_one]
  have he₁ := norm_entry_le_l2_opNorm (D_t₀ - z • (1 : Register (k + 3))) c_max c_max
  have he₂ := norm_entry_le_l2_opNorm (D_t₀ - z • (1 : Register (k + 3))) c_min c_min
  simp only [D_t₀, Matrix.sub_apply, Matrix.diagonal_apply_eq, Matrix.smul_apply,
    Matrix.one_apply_eq, smul_eq_mul, mul_one] at he₁ he₂
  change ‖w₁ - z‖ ≤ _ at he₁
  change ‖w₂ - z‖ ≤ _ at he₂
  rw [hw₂_eq] at he₂
  have hpar : ‖w₁ - z‖ ^ 2 + ‖-w₁ - z‖ ^ 2 = 4 := by
    have h1 : ‖w₁ - z‖ ^ 2 + ‖-w₁ - z‖ ^ 2 = 2 * (‖w₁‖ ^ 2 + ‖z‖ ^ 2) := by
      simp only [Complex.sq_norm, Complex.normSq_apply, Complex.sub_re, Complex.sub_im,
        Complex.neg_re, Complex.neg_im]; ring
    rw [h1, hw₁_norm, hz]; norm_num
  have hsq_ge2 : 2 ≤ ‖D_t₀ - z • (1 : Register (k + 3))‖ ^ 2 := by
    linarith only [hpar, pow_le_pow_left₀ (norm_nonneg _) he₁ 2,
      pow_le_pow_left₀ (norm_nonneg _) he₂ 2]
  exact Real.sqrt_le_iff.mpr ⟨norm_nonneg _, hsq_ge2⟩

/-- Strong-bond commuting Ising survival tube strictly inside `allBondStrongEvent (k + 1) η ⊆
twoCutConnectedEvent (k + 1) η`: for every `η ≥ 0` and all sufficiently large `k` (`N = k + 3`),
there is `c > 0` such that for every `T ≥ 2`, a `pathPauliDisorderLaw` event of probability
`≥ c * T ^ (-(10 * k + 22))` simultaneously satisfies:
1. `allBondStrongEvent (k + 1) η` and `twoCutConnectedEvent (k + 1) η` (every bond has strength `≥ η`),
2. maximally projective simple spectrum and full `2^N` Vandermonde rank inside `[0, 1]`,
3. scalar-return distance `≥ √2` at some `t₀ ∈ (0, T]`, and
4. `T < tenthPlateauOnset H s` for **every** budget `k + 2 ≤ s ≤ P` (`N - 1 ≤ s ≤ P`). -/
theorem gaussian_strongBond_ising_tube_tail {η : ℝ} (hη : 0 ≤ η) :
    ∀ᶠ k : ℕ in atTop,
      let N := k + 3
      let P := nearHilbertContinuousCircuitBudget N
      ∃ c : ℝ, 0 < c ∧ ∀ T : ℝ, 2 ≤ T →
        c ≤ T ^ (10 * k + 22) * pathPauliDisorderLaw.real {ω : PathPauliDisorder |
          let u := pathPauliDisorderShell ω (k + 1)
          let x : PrefixIndex (k + 1) → ℝ := fun i => u (pathCoeffEquiv (k + 1) i)
          let H : selfAdjoint (Register N) := ⟨pathHamiltonian u, isSelfAdjoint_pathHamiltonian u⟩
          x ∈ allBondStrongEvent (k + 1) η ∧
          x ∈ twoCutConnectedEvent (k + 1) η ∧
          MaximallyProjectiveEnergy H.2.isHermitian.eigenvalues ∧
          (∃ τ > 0, (∀ m : Fin (2 ^ N), ((m : ℕ) : ℝ) * τ ∈ Icc (0 : ℝ) 1) ∧
            Module.finrank ℂ (Submodule.span ℂ
              (range fun m : Fin (2 ^ N) => unitaryEvolution H.val (((m : ℕ) : ℝ) * τ))) = 2 ^ N) ∧
          (∃ t₀ ∈ Ioc (0 : ℝ) T, ∀ z : ℂ, ‖z‖ = 1 →
            Real.sqrt 2 ≤ ‖unitaryEvolution H.val t₀ - z • (1 : Register N)‖) ∧
          (∀ s : ℕ, k + 2 ≤ s → s ≤ P → T < tenthPlateauOnset H s)} := by
  letI : IsProbabilityMeasure pathPauliDisorderLaw := by unfold pathPauliDisorderLaw; infer_instance
  let γ := gaussianReal 0 1
  have hent := (tendsto_add_atTop_nat 3).eventually
    eventually_nearHilbertContinuousCircuitEntropy_lt_projectiveBooleanCarrier
  filter_upwards [hent, eventually_ge_atTop 16] with k hentropy hklarge
  intro N P
  have hP_ge : 2 * (k + 2) ≤ P := by
    dsimp only [P, N, nearHilbertContinuousCircuitBudget]
    have hpow : 64 * (k + 4) * (2 * (k + 2)) ≤ 2 ^ (k + 3) := by
      have hk16 : 16 ≤ k := hklarge
      have hind : ∀ m : ℕ, 16 ≤ m → 64 * (m + 4) * (2 * (m + 2)) ≤ 2 ^ (m + 3) := by
        intro m hm
        induction m, hm using Nat.le_induction with
        | base => decide
        | succ m hm ih =>
            have hstep : 64 * (m + 5) * (2 * (m + 3)) ≤ 2 * (64 * (m + 4) * (2 * (m + 2))) := by
              nlinarith only [hm]
            calc 64 * (m + 5) * (2 * (m + 3))
                ≤ 2 * (64 * (m + 4) * (2 * (m + 2))) := hstep
              _ ≤ 2 * 2 ^ (m + 3) := Nat.mul_le_mul_left 2 ih
              _ = 2 ^ (m + 4) := by rw [← pow_succ']
      exact hind k hk16
    exact (Nat.le_div_iff_mul_le (by omega)).mpr (by rw [mul_comm]; exact hpow)
  let zzEmb : Fin (k + 2) ↪ PrefixIndex (k + 1) :=
    ⟨fun e => (pathCoeffEquiv (k + 1)).symm (.inr (e, (2, 2))),
     fun _ _ h => (Prod.mk.inj (Sum.inr.inj ((pathCoeffEquiv (k + 1)).symm.injective h))).1⟩
  let offEmb : Fin (10 * (k + 1) + 12) ↪ PrefixIndex (k + 1) :=
    ⟨fun j => (pathCoeffEquiv (k + 1)).symm (pathPatchEquiv (k + 1) (.inr j)),
     fun _ _ h => Sum.inr.inj ((pathPatchEquiv (k + 1)).injective
       ((pathCoeffEquiv (k + 1)).symm.injective h))⟩
  let S_strong : Finset (PrefixIndex (k + 1)) := Finset.univ.map zzEmb
  let S_weak : Finset (PrefixIndex (k + 1)) := Finset.univ.map offEmb
  let i₀ : PrefixIndex (k + 1) := (pathCoeffEquiv (k + 1)).symm (.inl (0, 2))
  have hcard_s : S_strong.card = k + 2 := by
    simp [S_strong, Finset.card_map]
  have hcard_w : S_weak.card = 10 * k + 22 := by
    simp only [S_weak, Finset.card_map, Finset.card_univ, Fintype.card_fin]; omega
  have hdisj : Disjoint S_strong S_weak := by
    refine Finset.disjoint_left.mpr fun i his hiw => ?_
    obtain ⟨e, _, rfl⟩ := Finset.mem_map.mp his
    obtain ⟨j, _, heq⟩ := Finset.mem_map.mp hiw
    have hl : pathPatchEquiv (k + 1) (.inr j) = .inr (e, (2, 2)) :=
      (pathCoeffEquiv (k + 1)).symm.injective heq
    have hnd := notDiag_pathPatchEquiv_inr (n := k + 1) j
    rw [hl] at hnd
    exact hnd rfl
  have hi₀_s : i₀ ∉ S_strong := by
    intro h
    obtain ⟨e, _, heq⟩ := Finset.mem_map.mp h
    cases (pathCoeffEquiv (k + 1)).symm.injective heq
  have hi₀_w : i₀ ∉ S_weak := by
    intro h
    obtain ⟨j, _, heq⟩ := Finset.mem_map.mp h
    have hl : pathPatchEquiv (k + 1) (.inr j) = .inl (0, 2) :=
      (pathCoeffEquiv (k + 1)).symm.injective heq
    have hnd := notDiag_pathPatchEquiv_inr (n := k + 1) j
    rw [hl] at hnd
    exact hnd rfl
  have hp_strong : 0 < γ.real (Icc (η + 1) (η + 2)) :=
    ENNReal.toReal_pos (gaussianReal_Icc_pos (by linarith)).ne' (measure_ne_top _ _)
  have hp_anchor : 0 < γ.real (Icc (3 : ℝ) 4) :=
    ENNReal.toReal_pos (gaussianReal_Icc_pos (by norm_num : (3 : ℝ) < 4)).ne' (measure_ne_top _ _)
  let W_num : ℝ := 100 * ((10 * k + 22 : ℕ) : ℝ)
  have hW_pos : 0 < W_num := by dsimp only [W_num]; positivity
  let c : ℝ := (γ.real (Icc (η + 1) (η + 2))) ^ (k + 2) *
    (2 * gaussianDensityFloor / W_num) ^ (10 * k + 22) * γ.real (Icc (3 : ℝ) 4)
  have hc_pos : 0 < c := by
    dsimp only [c]
    exact mul_pos
      (mul_pos (pow_pos hp_strong _)
        (pow_pos (div_pos (mul_pos two_pos gaussianDensityFloor_pos) hW_pos) _))
      hp_anchor
  refine ⟨c, hc_pos, fun T hT2 => ?_⟩
  have hT_pos : 0 < T := by linarith only [hT2]
  let δ : ℝ := 1 / (W_num * T)
  have hδ_pos : 0 < δ := div_pos zero_lt_one (mul_pos hW_pos hT_pos)
  have hδ_le1 : δ ≤ 1 := by
    have hW1 : 1 ≤ W_num := by
      dsimp only [W_num]
      have : (1 : ℝ) ≤ ((10 * k + 22 : ℕ) : ℝ) := by exact_mod_cast (show 1 ≤ 10 * k + 22 by omega)
      linarith only [this]
    exact div_le_one_of_le₀ (by nlinarith only [hW1, hT2]) (mul_pos hW_pos hT_pos).le
  let Cyl := strongWeakAnchorCylinder S_strong S_weak i₀ (η + 1) (η + 2) δ
  have hCyl_meas : MeasurableSet Cyl :=
    measurableSet_strongWeakAnchorCylinder S_strong S_weak i₀ (η + 1) (η + 2) δ
  have hCyl_mass := pi_strongWeakAnchorCylinder_floor S_strong S_weak i₀ hdisj hi₀_s hi₀_w
    hδ_pos.le hδ_le1 (a := η + 1) (b := η + 2)
  rw [hcard_s, hcard_w] at hCyl_mass
  let x_map : PathPauliDisorder → PrefixIndex (k + 1) → ℝ :=
    fun ω i => pathPauliDisorderShell ω (k + 1) (pathCoeffEquiv (k + 1) i)
  have hmp := gaussian_pauli_prefix_coordinates_law (k + 1)
  have hpre_mass : pathPauliDisorderLaw.real (x_map ⁻¹' Cyl) =
      (Measure.pi fun _ : PrefixIndex (k + 1) => γ).real Cyl :=
    congrArg ENNReal.toReal (hmp.measure_preimage hCyl_meas.nullMeasurableSet)
  let TargetEvent : Set PathPauliDisorder := {ω : PathPauliDisorder |
    let u := pathPauliDisorderShell ω (k + 1)
    let x : PrefixIndex (k + 1) → ℝ := fun i => u (pathCoeffEquiv (k + 1) i)
    let H : selfAdjoint (Register N) := ⟨pathHamiltonian u, isSelfAdjoint_pathHamiltonian u⟩
    x ∈ allBondStrongEvent (k + 1) η ∧
    x ∈ twoCutConnectedEvent (k + 1) η ∧
    MaximallyProjectiveEnergy H.2.isHermitian.eigenvalues ∧
    (∃ τ > 0, (∀ m : Fin (2 ^ N), ((m : ℕ) : ℝ) * τ ∈ Icc (0 : ℝ) 1) ∧
      Module.finrank ℂ (Submodule.span ℂ
        (range fun m : Fin (2 ^ N) => unitaryEvolution H.val (((m : ℕ) : ℝ) * τ))) = 2 ^ N) ∧
    (∃ t₀ ∈ Ioc (0 : ℝ) T, ∀ z : ℂ, ‖z‖ = 1 →
      Real.sqrt 2 ≤ ‖unitaryEvolution H.val t₀ - z • (1 : Register N)‖) ∧
    (∀ s : ℕ, k + 2 ≤ s → s ≤ P → T < tenthPlateauOnset H s)}
  have hae_sub : x_map ⁻¹' Cyl ≤ᵐ[pathPauliDisorderLaw] TargetEvent := by
    filter_upwards [gaussian_path_all_prefixes_maximally_projective] with ω hmax_all
    rintro ⟨hstrong, hweak, hanchor⟩
    let u := pathPauliDisorderShell ω (k + 1)
    let x : PrefixIndex (k + 1) → ℝ := x_map ω
    let H : selfAdjoint (Register N) := ⟨pathHamiltonian u, isSelfAdjoint_pathHamiltonian u⟩
    have hmax : MaximallyProjectiveEnergy H.2.isHermitian.eigenvalues := hmax_all k
    -- 1. Strong bonds (`allBondStrongEvent` and `twoCutConnectedEvent`)
    have hbond : x ∈ allBondStrongEvent (k + 1) η := by
      intro e
      have hmem_s : zzEmb e ∈ S_strong := Finset.mem_map.mpr ⟨e, Finset.mem_univ e, rfl⟩
      have hval := (hstrong (zzEmb e) hmem_s).1
      refine ⟨zzEmb e, Finset.mem_image.mpr ⟨(2, 2), Finset.mem_univ _, rfl⟩, ?_⟩
      exact (by linarith only [hval] : η ≤ x (zzEmb e)).trans (le_abs_self _)
    have hconn : x ∈ twoCutConnectedEvent (k + 1) η :=
      allBondStrongEvent_subset_twoCutConnectedEvent (k + 1) η hbond
    -- 2. Vandermonde rank 2^N on [0, 1]
    have hvand : ∃ τ > 0, (∀ m : Fin (2 ^ N), ((m : ℕ) : ℝ) * τ ∈ Icc (0 : ℝ) 1) ∧
        Module.finrank ℂ (Submodule.span ℂ
          (range fun m : Fin (2 ^ N) => unitaryEvolution H.val (((m : ℕ) : ℝ) * τ))) = 2 ^ N := by
      have hden_pos : 0 < ((2 ^ N : ℕ) : ℝ) * (‖H.val‖ + 1) :=
        mul_pos (by positivity) (add_pos_of_nonneg_of_pos (norm_nonneg _) zero_lt_one)
      let τ := 1 / (((2 ^ N : ℕ) : ℝ) * (‖H.val‖ + 1))
      have hτ_pos : 0 < τ := div_pos zero_lt_one hden_pos
      have hτ_le_pi : τ ≤ Real.pi / (‖H.val‖ + 1) := by
        have h1_le_D : (1 : ℝ) ≤ ((2 ^ N : ℕ) : ℝ) := by exact_mod_cast Nat.one_le_two_pow
        have h1 : 1 / (((2 ^ N : ℕ) : ℝ) * (‖H.val‖ + 1)) ≤ 1 / (‖H.val‖ + 1) :=
          div_le_div_of_nonneg_left zero_le_one
            (add_pos_of_nonneg_of_pos (norm_nonneg _) zero_lt_one)
            (le_mul_of_one_le_left (add_nonneg (norm_nonneg _) zero_le_one) h1_le_D)
        exact h1.trans (div_le_div_of_nonneg_right
          ((by norm_num : (1 : ℝ) ≤ 3).trans Real.pi_gt_three.le)
          (add_nonneg (norm_nonneg _) zero_le_one))
      obtain ⟨_, hspan_eq, hfinrank⟩ := orbit_vandermonde_span_eq_spectralSpan H hmax.injective
        hτ_pos hτ_le_pi
      refine ⟨τ, hτ_pos, fun m => ⟨mul_nonneg (Nat.cast_nonneg _) hτ_pos.le, ?_⟩, ?_⟩
      · dsimp only [τ]
        rw [mul_one_div, div_le_one hden_pos]
        have hm_le : ((m : ℕ) : ℝ) ≤ ((2 ^ N : ℕ) : ℝ) := by exact_mod_cast m.isLt.le
        exact hm_le.trans (le_mul_of_one_le_right (by positivity)
          (le_add_of_nonneg_left (norm_nonneg _)))
      · rw [hspan_eq, hfinrank]
    -- 3. Scalar-return excision ≥ √2 at t₀ ∈ (0, π / 2) ⊆ (0, T]
    have honsiteZ : 3 ≤ |u (.inl (0, 2))| := by
      have hcoord : x i₀ = u (.inl (0, 2)) := by
        dsimp only [x, x_map, i₀, u]; rw [Equiv.apply_symm_apply]
      rw [← hcoord]
      exact hanchor.1.trans (le_abs_self _)
    obtain ⟨t₀, ht₀_mem, ht₀_exc⟩ := scalarReturnExcised_of_onsiteZ u honsiteZ
    have ht₀_T : t₀ ∈ Ioc 0 T := ⟨ht₀_mem.1, ht₀_mem.2.le.trans
      ((div_le_div_of_nonneg_right Real.pi_lt_four.le two_pos.le).trans (by norm_num; exact hT2))⟩
    -- 4. Diagonal projection u_diag with ‖H - H_diag‖ ≤ (10 k + 22) * δ = 1 / (100 * T)
    let u_diag : PathShell (k + 1) :=
      WithLp.toLp 2 fun l => if IsDiagLabel l then u l else 0
    have hu_diag_off : ∀ l : PathLabel (k + 1), ¬ IsDiagLabel l → u_diag l = 0 :=
      fun l hl => if_neg hl
    have hdiff_norm : ‖pathHamiltonian u - pathHamiltonian u_diag‖ ≤
        ((10 * k + 22 : ℕ) : ℝ) * δ := by
      have hsub_sum : pathHamiltonian u - pathHamiltonian u_diag =
          ∑ j : Fin (10 * (k + 1) + 12),
            ((u (pathPatchEquiv (k + 1) (.inr j)) : ℝ) : ℂ) •
              finitePauliMatrix (pathWord (pathPatchEquiv (k + 1) (.inr j))) := by
        rw [pathHamiltonian_eq_sum, pathHamiltonian_eq_sum, ← Finset.sum_sub_distrib,
          ← Equiv.sum_comp (pathPatchEquiv (k + 1)), Fintype.sum_sum_type]
        have hinl : ∑ i : Fin (2 * (k + 1) + 3),
            (((u (pathPatchEquiv (k + 1) (.inl i)) : ℝ) : ℂ) •
              finitePauliMatrix (pathWord (pathPatchEquiv (k + 1) (.inl i))) -
             ((u_diag (pathPatchEquiv (k + 1) (.inl i)) : ℝ) : ℂ) •
              finitePauliMatrix (pathWord (pathPatchEquiv (k + 1) (.inl i)))) = 0 := by
          refine Finset.sum_eq_zero fun i _ => ?_
          have hd := isDiag_pathPatchEquiv_inl (n := k + 1) i
          have heq : u_diag (pathPatchEquiv (k + 1) (.inl i)) =
              u (pathPatchEquiv (k + 1) (.inl i)) := if_pos hd
          rw [heq, sub_self]
        rw [hinl, zero_add]
        refine Finset.sum_congr rfl fun j _ => ?_
        have hnd := notDiag_pathPatchEquiv_inr (n := k + 1) j
        have heq0 : u_diag (pathPatchEquiv (k + 1) (.inr j)) = 0 := if_neg hnd
        rw [heq0, Complex.ofReal_zero, zero_smul, sub_zero]
      rw [hsub_sum]
      refine (norm_sum_le _ _).trans ?_
      have hterm (j : Fin (10 * (k + 1) + 12)) :
          ‖((u (pathPatchEquiv (k + 1) (.inr j)) : ℝ) : ℂ) •
            finitePauliMatrix (pathWord (pathPatchEquiv (k + 1) (.inr j)))‖ ≤ δ := by
        rw [norm_smul, norm_finitePauliMatrix, mul_one, Complex.norm_real, Real.norm_eq_abs]
        have hmem_w : offEmb j ∈ S_weak := Finset.mem_map.mpr ⟨j, Finset.mem_univ j, rfl⟩
        have hw := hweak (offEmb j) hmem_w
        simpa only [x_map, offEmb, u, Equiv.apply_symm_apply, Function.Embedding.coeFn_mk] using hw
      calc ∑ j : Fin (10 * (k + 1) + 12),
              ‖((u (pathPatchEquiv (k + 1) (.inr j)) : ℝ) : ℂ) •
                finitePauliMatrix (pathWord (pathPatchEquiv (k + 1) (.inr j)))‖
          ≤ ∑ _j : Fin (10 * (k + 1) + 12), δ := Finset.sum_le_sum fun j _ => hterm j
        _ = ((10 * k + 22 : ℕ) : ℝ) * δ := by
            rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
            congr 1; exact_mod_cast (show 10 * (k + 1) + 12 = 10 * k + 22 by omega)
    have hearly_inc (t : ℝ) (ht : |t| ≤ T) :
        HasProjectiveCircuitApproximation N (1 / 100 : ℝ) (k + 2)
          (unitaryEvolution H.val t) := by
      obtain ⟨z, hz, C, hC, hU⟩ := realizes_one_gate_per_bond_of_isDiag u_diag hu_diag_off t
      refine ⟨z, hz, C, hC, ?_⟩
      rw [← hU]
      calc ‖unitaryEvolution H.val t - unitaryEvolution (pathHamiltonian u_diag) t‖
          ≤ |t| * ‖H.val - pathHamiltonian u_diag‖ :=
            norm_unitaryEvolution_sub_le H.val (pathHamiltonian u_diag) H.2
              (isSelfAdjoint_pathHamiltonian u_diag) t
        _ ≤ T * (((10 * k + 22 : ℕ) : ℝ) * δ) :=
            mul_le_mul ht hdiff_norm (norm_nonneg _) hT_pos.le
        _ = 1 / 100 := by
            dsimp only [δ, W_num]
            field_simp [hT_pos.ne', hW_pos.ne']; ring
    let d := 2 ^ N - 1
    let e_fin : Config N ≃ Fin (d + 1) := (Fintype.equivFin _).trans
      (finCongr (by
        simp only [Config, Fintype.card_fun, Fintype.card_fin, Fintype.card_bool]
        have hd : 0 < 2 ^ N := pow_pos (by decide) N
        dsimp [d]; omega))
    obtain ⟨σ, hσ_gt, hσ_eq, _, _, _⟩ := first_circuit_threshold_of_increment e_fin H
      (hmax.comp_equiv e_fin.symm) hentropy T hT_pos.le hP_ge hearly_inc
    have honset_gt (s : ℕ) (hs_lo : k + 2 ≤ s) (hs_hi : s ≤ P) :
        T < tenthPlateauOnset H s := by
      have hearly (t : ℝ) (ht : t ∈ Icc 0 T) : orbitCircuitDistance H s t < 1 / 10 := by
        have habs : |t| ≤ T := by rw [abs_of_nonneg ht.1]; exact ht.2
        obtain ⟨z, hz, C, hC, herr⟩ := hearly_inc t habs
        have hd := (hasProjectiveCircuitApproximation_iff_infDist _ s (1 / 100 : ℝ)).mp
          ⟨z, hz, C, hC.trans hs_lo, herr⟩
        change orbitCircuitDistance H s t ≤ 1 / 100 at hd
        linarith only [hd]
      have hB_gt : 1 / 10 < orbitCircuitDistance H s σ := by
        have hmono : orbitCircuitDistance H P σ ≤ orbitCircuitDistance H s σ := by
          apply (hasProjectiveCircuitApproximation_iff_infDist _ P _).mp
          obtain ⟨z, hz, C, hC, herr⟩ := (hasProjectiveCircuitApproximation_iff_infDist _ s _).mpr
            (le_rfl : orbitCircuitDistance H s σ ≤ _)
          exact ⟨z, hz, C, hC.trans hs_hi, herr⟩
        rw [hσ_eq] at hmono
        linarith only [hmono]
      exact (tenthPlateauOnset_spec H hT_pos (hT_pos.trans hσ_gt).le hearly hB_gt).1
    exact ⟨hbond, hconn, hmax, hvand, ⟨t₀, ht₀_T, ht₀_exc⟩, honset_gt⟩
  have hmeas_le : (Measure.pi fun _ : PrefixIndex (k + 1) => γ).real Cyl ≤
      pathPauliDisorderLaw.real TargetEvent := by
    rw [← hpre_mass]
    exact ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono_ae hae_sub)
  have hc_eq : c = T ^ (10 * k + 22) *
      ((γ.real (Icc (η + 1) (η + 2))) ^ (k + 2) *
        (2 * gaussianDensityFloor * δ) ^ (10 * k + 22) * γ.real (Icc (3 : ℝ) 4)) := by
    dsimp only [c, δ]
    have hpow_T : T ^ (10 * k + 22) * (2 * gaussianDensityFloor * (1 / (W_num * T))) ^ (10 * k + 22) =
        (2 * gaussianDensityFloor / W_num) ^ (10 * k + 22) := by
      rw [← mul_pow]
      congr 1
      field_simp [hT_pos.ne', hW_pos.ne']
    calc c = (γ.real (Icc (η + 1) (η + 2))) ^ (k + 2) *
            (T ^ (10 * k + 22) * (2 * gaussianDensityFloor * (1 / (W_num * T))) ^ (10 * k + 22)) *
            γ.real (Icc (3 : ℝ) 4) := by dsimp only [c]; rw [hpow_T]
      _ = _ := by ring
  rw [hc_eq]
  exact mul_le_mul_of_nonneg_left (hCyl_mass.trans hmeas_le) (pow_nonneg hT_pos.le _)

#print axioms gaussianReal_Icc_symm_le
#print axioms pi_smallCube_union_prob_le
#print axioms pi_strongWeakAnchorCylinder_floor
#print axioms coord_abs_le_opNorm_edgePart
#print axioms twoCutConnectedEvent_compl_prob_le
#print axioms allBondStrongEvent_compl_prob_le
#print axioms exists_half_contiguous_subchain_of_twoCutConnected
#print axioms gaussian_sub_one_gate_per_bond_exponential_onset
#print axioms universal_bipartiteOperatorRank_ceiling
#print axioms norm_heisenbergOrbit_sub_commutatorTaylor_le
#print axioms realizes_one_gate_per_bond_of_isDiag
#print axioms gaussian_strongBond_ising_tube_tail

end
end GaloisForLFunctions.HTGeometry.AccuracyScales.TenthPlateau
