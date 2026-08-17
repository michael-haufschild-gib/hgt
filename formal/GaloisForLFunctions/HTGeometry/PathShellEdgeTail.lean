import GaloisForLFunctions.HTGeometry.SphereBlockTail
import GaloisForLFunctions.HTGeometry.PauliEdgeBlockNorms

/-!
# The weak-cut sector of the path-local Pauli shell

The coefficient space of a path-local Pauli Hamiltonian on `n + 2` qubits carries one onsite label
per site and axis and nine coupling labels per edge, so it has dimension `12(n+2) - 9`.  Each edge
selects a nine-dimensional coordinate block, and the block tail law of the unit shell gives the
exact ninth-power law for the shell probability that one edge is weak.

Since the operator norm of a two-site interaction is squeezed between its coefficient norm and three
times it, the contiguous-cut conductance is small exactly when some edge block is small: one edge
block below `x/3` forces the conductance below `x`, and conductance below `x` forces some edge block
below `x`.  The edge union bound then transfers the ninth-power law to the whole weak-cut sector,
with no independence between edges used anywhere.
-/

open MeasureTheory Metric Set
open scoped Pointwise ENNReal Matrix.Norms.L2Operator

namespace GaloisForLFunctions.HTGeometry

set_option linter.unusedSectionVars false

noncomputable section

section PathShell

variable (n : ℕ)

/-- Coefficient labels of the path-local Pauli shell on `n + 2` qubits: one onsite label per site
and axis, and nine coupling labels per edge. -/
abbrev PathLabel : Type := (Fin (n + 2) × Fin 3) ⊕ (Fin (n + 1) × (Fin 3 × Fin 3))

/-- The coefficient space of the path-local Pauli shell. -/
abbrev PathShell : Type := EuclideanSpace ℝ (PathLabel n)

/-- **`(16)`.**  The coefficient dimension of the path-local shell on `n + 2` qubits. -/
theorem finrank_pathShell : Module.finrank ℝ (PathShell n) = 12 * (n + 2) - 9 := by
  rw [finrank_euclideanSpace]
  simp [Fintype.card_sum, Fintype.card_prod]
  omega

variable {n}

/-- The labels carried by one edge. -/
def IsEdgeLabel (e : Fin (n + 1)) : PathLabel n → Prop
  | Sum.inl _ => False
  | Sum.inr q => q.1 = e

instance decidableIsEdgeLabel (e : Fin (n + 1)) : DecidablePred (IsEdgeLabel e) := fun l =>
  match l with
  | Sum.inl _ => inferInstanceAs (Decidable False)
  | Sum.inr q => inferInstanceAs (Decidable (q.1 = e))

/-- The nine labels of one edge, indexed by the axis pair. -/
def edgeLabel (e : Fin (n + 1)) (ab : Fin 3 × Fin 3) : {l : PathLabel n // IsEdgeLabel e l} :=
  ⟨Sum.inr (e, ab), rfl⟩

theorem edgeLabel_bijective (e : Fin (n + 1)) : Function.Bijective (edgeLabel e) := by
  constructor
  · intro ab cd h
    have := congrArg Subtype.val h
    simpa [edgeLabel, Sum.inr.injEq, Prod.ext_iff] using this
  · rintro ⟨l, hl⟩
    match l with
    | Sum.inl a => exact absurd hl (by simp [IsEdgeLabel])
    | Sum.inr q =>
      refine ⟨q.2, ?_⟩
      have hq : q.1 = e := hl
      rw [edgeLabel]
      congr 1
      rw [← hq]

/-- The axis-pair indexing of the labels of one edge. -/
def edgeLabelEquiv (e : Fin (n + 1)) : (Fin 3 × Fin 3) ≃ {l : PathLabel n // IsEdgeLabel e l} :=
  Equiv.ofBijective _ (edgeLabel_bijective e)

theorem edgeLabelEquiv_apply (e : Fin (n + 1)) (ab : Fin 3 × Fin 3) :
    ((edgeLabelEquiv e ab : {l : PathLabel n // IsEdgeLabel e l}) : PathLabel n)
      = Sum.inr (e, ab) := rfl

/-- The nine coupling coefficients carried by one edge. -/
def edgeCoeff (u : PathShell n) (e : Fin (n + 1)) : Fin 3 × Fin 3 → ℝ :=
  fun ab => u (Sum.inr (e, ab))

/-- The interaction operator across one edge. -/
def edgeOperator (u : PathShell n) (e : Fin (n + 1)) :
    Matrix (FiniteQubitConfiguration Bool) (FiniteQubitConfiguration Bool) ℂ :=
  edgeInteraction (edgeCoeff u e)

/-- The conductance of one edge: the operator norm of its interaction. -/
def edgeConductance (u : PathShell n) (e : Fin (n + 1)) : ℝ := ‖edgeOperator u e‖

/-- **`(22)`.**  The contiguous-cut conductance profile of a shell point. -/
def pathConductance (u : PathShell n) : ℝ :=
  Finset.univ.inf' Finset.univ_nonempty fun e : Fin (n + 1) => edgeConductance u e

theorem pathConductance_le (u : PathShell n) (e : Fin (n + 1)) :
    pathConductance u ≤ edgeConductance u e :=
  Finset.inf'_le _ (Finset.mem_univ e)

theorem exists_edgeConductance_eq (u : PathShell n) :
    ∃ e : Fin (n + 1), edgeConductance u e = pathConductance u := by
  obtain ⟨e, -, he⟩ := Finset.exists_mem_eq_inf' (Finset.univ_nonempty)
    fun e : Fin (n + 1) => edgeConductance u e
  exact ⟨e, he.symm⟩

/-- The edge conductance is squeezed by the coefficient norm of its block. -/
theorem edgeRho_le_edgeConductance (u : PathShell n) (e : Fin (n + 1)) :
    edgeRho (edgeCoeff u e) ≤ edgeConductance u e :=
  le_l2_opNorm_edgeInteraction _

theorem edgeConductance_le_three_mul (u : PathShell n) (e : Fin (n + 1)) :
    edgeConductance u e ≤ 3 * edgeRho (edgeCoeff u e) :=
  l2_opNorm_edgeInteraction_le _

end PathShell

section EdgeSplit

variable {n : ℕ}

/-- The orthogonal splitting of the shell coefficient space along one edge block. -/
def edgeSplit (e : Fin (n + 1)) :
    PathShell n ≃ₗᵢ[ℝ]
      BlockSpace (EuclideanSpace ℝ {l : PathLabel n // IsEdgeLabel e l})
        (EuclideanSpace ℝ {l : PathLabel n // ¬ IsEdgeLabel e l}) :=
  (LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ (Equiv.sumCompl (IsEdgeLabel e)).symm).trans
    (PiLp.sumPiLpEquivProdLpPiLp 2 fun _ : {l : PathLabel n // IsEdgeLabel e l} ⊕
      {l : PathLabel n // ¬ IsEdgeLabel e l} => ℝ)

theorem edgeSplit_fst (e : Fin (n + 1)) (u : PathShell n)
    (i : {l : PathLabel n // IsEdgeLabel e l}) :
    (edgeSplit e u).fst i = u (i : PathLabel n) := by
  rfl

/-- The block norm of the edge split is the coefficient norm of the edge. -/
theorem norm_edgeSplit_fst (e : Fin (n + 1)) (u : PathShell n) :
    ‖(edgeSplit e u).fst‖ = edgeRho (edgeCoeff u e) := by
  rw [EuclideanSpace.norm_eq, edgeRho]
  congr 1
  rw [← Equiv.sum_comp (edgeLabelEquiv e) fun i => ‖(edgeSplit e u).fst i‖ ^ 2]
  refine Finset.sum_congr rfl fun ab _ => ?_
  rw [edgeSplit_fst, edgeLabelEquiv_apply]
  rw [Real.norm_eq_abs, sq_abs]
  rfl

/-- **The nine-dimensional edge block.** -/
theorem finrank_edgeBlock (e : Fin (n + 1)) :
    Module.finrank ℝ (EuclideanSpace ℝ {l : PathLabel n // IsEdgeLabel e l}) = 9 := by
  rw [finrank_euclideanSpace, ← Fintype.card_congr (edgeLabelEquiv e)]
  simp

instance nontrivial_edgeComplement (e : Fin (n + 1)) :
    Nontrivial (EuclideanSpace ℝ {l : PathLabel n // ¬ IsEdgeLabel e l}) := by
  refine ⟨⟨0, EuclideanSpace.single (⟨Sum.inl (0, 0), by simp [IsEdgeLabel]⟩ :
    {l : PathLabel n // ¬ IsEdgeLabel e l}) (1 : ℝ), fun h => ?_⟩⟩
  have hnorm := congrArg (fun v : EuclideanSpace ℝ {l : PathLabel n // ¬ IsEdgeLabel e l} => ‖v‖) h
  simp at hnorm

/-- The shell points whose edge block is small. -/
def edgeSmall (e : Fin (n + 1)) (x : ℝ) : Set (sphere (0 : PathShell n) 1) :=
  {u | edgeRho (edgeCoeff (u : PathShell n) e) ≤ x}

theorem edgeSmall_eq_blockSmallOf (e : Fin (n + 1)) (x : ℝ) :
    edgeSmall e x = blockSmallOf _ _ (edgeSplit e) x := by
  ext u
  show edgeRho (edgeCoeff (u : PathShell n) e) ≤ x ↔ ‖(edgeSplit e (u : PathShell n)).fst‖ ≤ x
  rw [norm_edgeSplit_fst]

end EdgeSplit

section Tail

variable {n : ℕ}

instance nontrivial_pathShell : Nontrivial (PathShell n) := by
  refine ⟨⟨0, EuclideanSpace.single (Sum.inl (0, 0) : PathLabel n) (1 : ℝ), fun h => ?_⟩⟩
  have hnorm := congrArg (fun v : PathShell n => ‖v‖) h
  simp at hnorm

/-- The uniform shell probability of an event of the path-local coefficient shell. -/
def pathShellProb (A : Set (sphere (0 : PathShell n) 1)) : ℝ :=
  (volume.toSphere A).toReal /
    (volume.toSphere (univ : Set (sphere (0 : PathShell n) 1))).toReal

theorem toSphere_pathShell_univ_toReal :
    (volume.toSphere (univ : Set (sphere (0 : PathShell n) 1))).toReal
      = (Module.finrank ℝ (PathShell n) : ℝ) * (volume (ball (0 : PathShell n) 1)).toReal := by
  rw [Measure.toSphere_apply_univ, ENNReal.toReal_mul, ENNReal.toReal_natCast]

theorem toSphere_pathShell_univ_pos :
    0 < (volume.toSphere (univ : Set (sphere (0 : PathShell n) 1))).toReal := by
  rw [toSphere_pathShell_univ_toReal]
  have hrank : (0 : ℝ) < (Module.finrank ℝ (PathShell n) : ℝ) := by
    exact_mod_cast Module.finrank_pos
  have hball : 0 < (volume (ball (0 : PathShell n) 1)).toReal :=
    ENNReal.toReal_pos (ne_of_gt (measure_ball_pos volume 0 one_pos))
      (ne_of_lt measure_ball_lt_top)
  positivity

theorem toSphere_pathShell_ne_top (A : Set (sphere (0 : PathShell n) 1)) :
    volume.toSphere A ≠ ⊤ := by
  refine ne_of_lt (lt_of_le_of_lt (measure_mono (subset_univ A)) ?_)
  rw [Measure.toSphere_apply_univ]
  exact ENNReal.mul_lt_top (ENNReal.natCast_lt_top _) measure_ball_lt_top

theorem pathShellProb_nonneg (A : Set (sphere (0 : PathShell n) 1)) : 0 ≤ pathShellProb A := by
  refine div_nonneg ENNReal.toReal_nonneg ?_
  exact le_of_lt toSphere_pathShell_univ_pos

theorem pathShellProb_mono {A B : Set (sphere (0 : PathShell n) 1)} (hAB : A ⊆ B) :
    pathShellProb A ≤ pathShellProb B := by
  have hnum : (volume.toSphere A).toReal ≤ (volume.toSphere B).toReal :=
    ENNReal.toReal_mono (toSphere_pathShell_ne_top B) (measure_mono hAB)
  have hden := toSphere_pathShell_univ_pos (n := n)
  rw [pathShellProb, pathShellProb]
  gcongr

theorem pathShellProb_iUnion_le (A : Fin (n + 1) → Set (sphere (0 : PathShell n) 1)) :
    pathShellProb (⋃ e, A e) ≤ ∑ e, pathShellProb (A e) := by
  have hle : (volume.toSphere (⋃ e, A e)).toReal ≤ ∑ e, (volume.toSphere (A e)).toReal := by
    have hsum : volume.toSphere (⋃ e, A e) ≤ ∑ e, volume.toSphere (A e) :=
      measure_iUnion_fintype_le _ _
    have htop : (∑ e, volume.toSphere (A e)) ≠ ⊤ :=
      ne_of_lt (ENNReal.sum_lt_top.mpr fun e _ => lt_of_le_of_ne le_top (toSphere_pathShell_ne_top _))
    calc (volume.toSphere (⋃ e, A e)).toReal ≤ (∑ e, volume.toSphere (A e)).toReal :=
          ENNReal.toReal_mono htop hsum
      _ = ∑ e, (volume.toSphere (A e)).toReal :=
          ENNReal.toReal_sum fun e _ => toSphere_pathShell_ne_top _
  have hden := toSphere_pathShell_univ_pos (n := n)
  rw [pathShellProb, show (∑ e, pathShellProb (A e))
      = (∑ e, (volume.toSphere (A e)).toReal) /
        (volume.toSphere (univ : Set (sphere (0 : PathShell n) 1))).toReal from
    (Finset.sum_div _ _ _).symm]
  gcongr

/-- **`(18)`.**  The shell probability that one edge block is weaker than `x` is exactly of order
`x ^ 9`: the exponent is the nine-dimensional edge block, and both constants are positive. -/
theorem exists_edgeSmall_tail_bounds (e : Fin (n + 1)) :
    ∃ C c : ℝ, 0 < c ∧ 0 < C ∧
      (∀ x : ℝ, 0 ≤ x → pathShellProb (edgeSmall e x) ≤ C * x ^ 9) ∧
      (∀ x : ℝ, 0 ≤ x → x ≤ 1 → c * x ^ 9 ≤ pathShellProb (edgeSmall e x)) := by
  obtain ⟨C, c, hc, hC, hupper, hlower⟩ :=
    exists_blockTail_bounds (EuclideanSpace ℝ {l : PathLabel n // IsEdgeLabel e l})
      (EuclideanSpace ℝ {l : PathLabel n // ¬ IsEdgeLabel e l}) (edgeSplit e)
  rw [finrank_edgeBlock e] at hupper hlower
  refine ⟨C, c, hc, hC, ?_, ?_⟩
  · intro x hx
    rw [pathShellProb, edgeSmall_eq_blockSmallOf]
    exact hupper x hx
  · intro x hx0 hx1
    rw [pathShellProb, edgeSmall_eq_blockSmallOf]
    exact hlower x hx0 hx1

/-- One weak edge makes the contiguous-cut conductance weak. -/
theorem edgeSmall_subset_conductanceSmall (e : Fin (n + 1)) {x : ℝ} :
    edgeSmall e (x / 3) ⊆ {u : sphere (0 : PathShell n) 1 | pathConductance (u : PathShell n) ≤ x} := by
  intro u hu
  have hrho : edgeRho (edgeCoeff (u : PathShell n) e) ≤ x / 3 := hu
  have h1 : pathConductance (u : PathShell n) ≤ edgeConductance (u : PathShell n) e :=
    pathConductance_le _ e
  have h2 : edgeConductance (u : PathShell n) e ≤ 3 * edgeRho (edgeCoeff (u : PathShell n) e) :=
    edgeConductance_le_three_mul _ e
  have : pathConductance (u : PathShell n) ≤ x := by linarith
  exact this

/-- Weak conductance forces one weak edge block. -/
theorem conductanceSmall_subset_iUnion {x : ℝ} :
    {u : sphere (0 : PathShell n) 1 | pathConductance (u : PathShell n) ≤ x}
      ⊆ ⋃ e : Fin (n + 1), edgeSmall e x := by
  intro u hu
  have hcond : pathConductance (u : PathShell n) ≤ x := hu
  obtain ⟨e, he⟩ := exists_edgeConductance_eq (u : PathShell n)
  refine mem_iUnion.mpr ⟨e, ?_⟩
  have hrho : edgeRho (edgeCoeff (u : PathShell n) e) ≤ edgeConductance (u : PathShell n) e :=
    edgeRho_le_edgeConductance _ e
  show edgeRho (edgeCoeff (u : PathShell n) e) ≤ x
  rw [he] at hrho
  exact le_trans hrho hcond

/-- **`(23)`.**  The whole weak-cut sector of the path-local shell obeys the same ninth-power law:
its shell probability is bounded above and below by positive constants times `x ^ 9`. -/
theorem exists_pathConductance_tail_bounds :
    ∃ C c : ℝ, 0 < c ∧ 0 < C ∧
      (∀ x : ℝ, 0 ≤ x →
        pathShellProb {u : sphere (0 : PathShell n) 1 | pathConductance (u : PathShell n) ≤ x}
          ≤ C * x ^ 9) ∧
      (∀ x : ℝ, 0 ≤ x → x ≤ 3 →
        c * x ^ 9 ≤
          pathShellProb {u : sphere (0 : PathShell n) 1 | pathConductance (u : PathShell n) ≤ x}) := by
  classical
  choose C c hc hC hupper hlower using fun e : Fin (n + 1) => exists_edgeSmall_tail_bounds e
  refine ⟨∑ e, C e, c 0 / 3 ^ 9, div_pos (hc 0) (by norm_num), ?_, ?_, ?_⟩
  · exact Finset.sum_pos (fun e _ => hC e) Finset.univ_nonempty
  · intro x hx
    calc pathShellProb {u : sphere (0 : PathShell n) 1 | pathConductance (u : PathShell n) ≤ x}
        ≤ pathShellProb (⋃ e : Fin (n + 1), edgeSmall e x) :=
          pathShellProb_mono conductanceSmall_subset_iUnion
      _ ≤ ∑ e, pathShellProb (edgeSmall e x) := pathShellProb_iUnion_le _
      _ ≤ ∑ e, C e * x ^ 9 := Finset.sum_le_sum fun e _ => hupper e x hx
      _ = (∑ e, C e) * x ^ 9 := by rw [Finset.sum_mul]
  · intro x hx0 hx3
    have hx3' : x / 3 ≤ 1 := by linarith
    have hx0' : (0:ℝ) ≤ x / 3 := by linarith
    calc c 0 / 3 ^ 9 * x ^ 9 = c 0 * (x / 3) ^ 9 := by ring
      _ ≤ pathShellProb (edgeSmall 0 (x / 3)) := hlower 0 (x / 3) hx0' hx3'
      _ ≤ pathShellProb {u : sphere (0 : PathShell n) 1 | pathConductance (u : PathShell n) ≤ x} :=
          pathShellProb_mono (edgeSmall_subset_conductanceSmall 0)

end Tail

end

end GaloisForLFunctions.HTGeometry
