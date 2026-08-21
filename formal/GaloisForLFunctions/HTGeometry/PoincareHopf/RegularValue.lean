import GaloisForLFunctions.HTGeometry.PoincareHopf.DegreeIndexSum

/-!
# Nondegenerate zeros and the integrality of the degree

If every zero of a `C²` field in the closure of a bounded open set lies in the set and is
nondegenerate, then the zeros are finitely many: each is isolated by the estimate comparing the
field with its linearization, and the zero set is compact.  Consequently the degree is a finite sum
of signs, hence an integer.
-/

open Matrix Finset Set MeasureTheory

namespace GaloisForLFunctions.HTGeometry.PoincareHopf

variable {n : ℕ} {v : (Fin n → ℝ) → (Fin n → ℝ)} {Ω : Set (Fin n → ℝ)}

/-- **Nondegenerate zeros are finitely many.** -/
theorem finite_zeros (hv : ContDiff ℝ 2 v) (hΩb : Bornology.IsBounded Ω)
    (hZΩ : ∀ x ∈ closure Ω, v x = 0 → x ∈ Ω)
    (hreg : ∀ x ∈ Ω, v x = 0 → (jac v x).det ≠ 0) :
    {x | x ∈ closure Ω ∧ v x = 0}.Finite := by
  classical
  set S := {x | x ∈ closure Ω ∧ v x = 0} with hS
  have hScl : IsClosed S := by
    have h1 : S = closure Ω ∩ v ⁻¹' {0} := by
      ext x; simp [hS, Set.mem_inter_iff]
    rw [h1]
    exact isClosed_closure.inter (isClosed_singleton.preimage hv.continuous)
  have hSc : IsCompact S :=
    Metric.isCompact_of_isClosed_isBounded hScl
      (hΩb.closure.subset (fun x hx => hx.1))
  -- an isolating ball around each zero
  have hnbhd : ∀ p ∈ S, ∃ ε > 0, ∀ x ∈ Metric.ball p ε, x ∈ S → x = p := by
    intro p hp
    have hpΩ : p ∈ Ω := hZΩ p hp.1 hp.2
    obtain ⟨c, _, ε, hεpos, hisol, _, _⟩ :=
      exists_isolating_of_nondegenerate hv hp.2 (hreg p hpΩ hp.2)
    refine ⟨ε, hεpos, fun x hx hxS => ?_⟩
    by_contra hxp
    exact hisol.2 x (Metric.ball_subset_closedBall hx) hxp hxS.2
  choose! ε hεpos hεisol using hnbhd
  obtain ⟨t, hts, htcover⟩ := hSc.elim_nhds_subcover (fun p => Metric.ball p (ε p))
    (fun p hp => Metric.ball_mem_nhds p (hεpos p hp))
  refine Set.Finite.subset t.finite_toSet fun x hx => ?_
  obtain ⟨p, hpt, hxb⟩ := Set.mem_iUnion₂.mp (htcover hx)
  have hxeq := hεisol p (hts p hpt) x hxb hx
  rw [hxeq]
  exact hpt

/-- **Integrality of the degree at a nondegenerate zero set.** -/
theorem exists_int_degree_of_nondegenerate (hv : ContDiff ℝ 2 v) (hΩ : IsOpen Ω)
    (hΩb : Bornology.IsBounded Ω)
    (hZΩ : ∀ x ∈ closure Ω, v x = 0 → x ∈ Ω)
    (hreg : ∀ x ∈ Ω, v x = 0 → (jac v x).det ≠ 0) :
    ∃ k : ℤ, degree v Ω 0 = (k : ℝ) := by
  classical
  have hfin := finite_zeros hv hΩb hZΩ hreg
  set Z := hfin.toFinset with hZ
  have hZmemiff : ∀ x, x ∈ Z ↔ (x ∈ closure Ω ∧ v x = 0) := by
    intro x; rw [hZ, Set.Finite.mem_toFinset]; rfl
  have hZsub : (↑Z : Set (Fin n → ℝ)) ⊆ Ω := by
    intro x hx
    have := (hZmemiff x).mp hx
    exact hZΩ x this.1 this.2
  have hZmem : ∀ x ∈ closure Ω, v x = 0 → x ∈ Z := fun x hx hv0 =>
    (hZmemiff x).mpr ⟨hx, hv0⟩
  have hsum := degree_eq_sum_index hv hΩ hΩb Z hZsub hZmem
  have hind : ∀ p ∈ Z, index v p = if 0 < (jac v p).det then 1 else -1 := by
    intro p hp
    have hpz := (hZmemiff p).mp hp
    exact index_eq_sign_det hv hpz.2 (hreg p (hZsub hp) hpz.2)
  refine ⟨∑ p ∈ Z, (if 0 < (jac v p).det then (1 : ℤ) else -1), ?_⟩
  rw [hsum, Finset.sum_congr rfl hind]
  push_cast
  exact Finset.sum_congr rfl fun p _ => by split <;> simp

end GaloisForLFunctions.HTGeometry.PoincareHopf
