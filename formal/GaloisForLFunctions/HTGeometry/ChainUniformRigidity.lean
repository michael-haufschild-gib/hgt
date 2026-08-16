import GaloisForLFunctions.HTGeometry.ChainShellCentralizer

/-!
# Uniform tangent rigidity along a compact family

On a compact family of chain shell operators with invertible edge couplings and a field-rigid edge,
the constant controlling the distance to the plane spanned by the identity and the operator can be
chosen uniformly.
-/

open Finset Matrix Metric

open scoped Matrix.Norms.Frobenius

noncomputable section

namespace GaloisForLFunctions.HTGeometry

set_option linter.unusedSectionVars false

variable {m : ℕ}

/-- The plane spanned by the identity and a shell operator. -/
def shellPlane (m : ℕ) (p0 : ShellParam m) : Set (ShellMat m) :=
  {B | ∃ lam mu : ℝ, B = lam • shellMap m p0 + mu • (1 : ShellMat m)}

theorem zero_mem_shellPlane (p0 : ShellParam m) : (0 : ShellMat m) ∈ shellPlane m p0 :=
  ⟨0, 0, by simp⟩

theorem shellPlane_nonempty (p0 : ShellParam m) : (shellPlane m p0).Nonempty :=
  ⟨0, zero_mem_shellPlane p0⟩

theorem add_smul_mem_shellPlane (p0 : ShellParam m) {B X : ShellMat m}
    (hB : B ∈ shellPlane m p0) (hX : X ∈ shellPlane m p0) (c : ℝ) :
    B + c • X ∈ shellPlane m p0 := by
  obtain ⟨l1, u1, rfl⟩ := hB
  obtain ⟨l2, u2, rfl⟩ := hX
  refine ⟨l1 + c * l2, u1 + c * u2, ?_⟩
  rw [add_smul, add_smul, smul_add, mul_smul, mul_smul]
  abel

theorem shellPlane_subset_chainShell (p0 : ShellParam m) : shellPlane m p0 ⊆ chainShell m := by
  rintro B ⟨lam, mu, rfl⟩
  exact Submodule.add_mem _ (Submodule.smul_mem _ _ (shellMap_mem_chainShell p0))
    (Submodule.smul_mem _ _ one_mem_chainShell)

theorem commutator_eq_zero_of_mem_shellPlane (p0 : ShellParam m) {B : ShellMat m}
    (hB : B ∈ shellPlane m p0) : shellMap m p0 * B - B * shellMap m p0 = 0 := by
  obtain ⟨lam, mu, rfl⟩ := hB
  rw [Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_smul,
    Matrix.smul_mul, Matrix.mul_one, Matrix.one_mul, sub_self]

theorem continuous_shellMap : Continuous (shellMap m) :=
  (shellMap m).continuous_of_finiteDimensional

/-- The commutator of a shell operator with a member of the shell. -/
def shellCommutator (m : ℕ) (x : ShellParam m × chainShell m) : ℝ :=
  ‖shellMap m x.1 * (x.2 : ShellMat m) - (x.2 : ShellMat m) * shellMap m x.1‖

theorem continuous_shellCommutator : Continuous (shellCommutator m) := by
  refine Continuous.norm (Continuous.sub ?_ ?_)
  · exact (continuous_shellMap.comp continuous_fst).mul
      (continuous_subtype_val.comp continuous_snd)
  · exact (continuous_subtype_val.comp continuous_snd).mul
      (continuous_shellMap.comp continuous_fst)

/-- The compact test set of normalized shell directions transverse to the plane. -/
def shellTestSet (m : ℕ) (S : Set (ShellParam m)) : Set (ShellParam m × chainShell m) :=
  (S ×ˢ Metric.closedBall (0 : chainShell m) 1) ∩
    ⋂ c : ℝ × ℝ, {x | (1 / 2 : ℝ) ≤
      ‖(x.2 : ShellMat m) - (c.1 • shellMap m x.1 + c.2 • (1 : ShellMat m))‖}

theorem isCompact_shellTestSet {S : Set (ShellParam m)} (hS : IsCompact S) :
    IsCompact (shellTestSet m S) := by
  refine IsCompact.inter_right (hS.prod (isCompact_closedBall _ _)) ?_
  refine isClosed_iInter fun c => ?_
  have hcont : Continuous fun x : ShellParam m × chainShell m =>
      ‖(x.2 : ShellMat m) - (c.1 • shellMap m x.1 + c.2 • (1 : ShellMat m))‖ := by
    refine Continuous.norm (Continuous.sub (continuous_subtype_val.comp continuous_snd) ?_)
    exact ((continuous_shellMap.comp continuous_fst).const_smul c.1).add continuous_const
  exact isClosed_le continuous_const hcont


theorem exists_mem_shellTestSet {S : Set (ShellParam m)} {p0 : ShellParam m} (hp0 : p0 ∈ S)
    {A : ShellMat m} (hA : A ∈ chainShell m)
    (hd : 0 < Metric.infDist A (shellPlane m p0)) :
    ∃ A' : chainShell m, (p0, A') ∈ shellTestSet m S ∧
      Metric.infDist A (shellPlane m p0) * shellCommutator m (p0, A') ≤
        ‖shellMap m p0 * A - A * shellMap m p0‖ := by
  classical
  obtain ⟨B, hB, hAB⟩ := (Metric.infDist_lt_iff (shellPlane_nonempty p0)).mp
    (show Metric.infDist A (shellPlane m p0) < 2 * Metric.infDist A (shellPlane m p0) by linarith)
  have hBd : Metric.infDist A (shellPlane m p0) ≤ ‖A - B‖ := by
    have hle : Metric.infDist A (shellPlane m p0) ≤ dist A B :=
      Metric.infDist_le_dist_of_mem hB
    rwa [dist_eq_norm] at hle
  have hABnorm : ‖A - B‖ < 2 * Metric.infDist A (shellPlane m p0) := by
    rwa [dist_eq_norm] at hAB
  have hpos : 0 < ‖A - B‖ := lt_of_lt_of_le hd hBd
  have hmem : A - B ∈ chainShell m :=
    Submodule.sub_mem _ hA (shellPlane_subset_chainShell p0 hB)
  have hnormA' : ‖‖A - B‖⁻¹ • (A - B)‖ = 1 := by
    rw [norm_smul, norm_inv, norm_norm]
    field_simp
  refine ⟨⟨‖A - B‖⁻¹ • (A - B), Submodule.smul_mem _ _ hmem⟩, ⟨⟨hp0, ?_⟩, ?_⟩, ?_⟩
  · rw [Metric.mem_closedBall, dist_zero_right]
    exact le_of_eq hnormA'
  · refine Set.mem_iInter.mpr fun c => ?_
    show (1 / 2 : ℝ) ≤ ‖‖A - B‖⁻¹ • (A - B) - (c.1 • shellMap m p0 + c.2 • (1 : ShellMat m))‖
    have hX : c.1 • shellMap m p0 + c.2 • (1 : ShellMat m) ∈ shellPlane m p0 := ⟨c.1, c.2, rfl⟩
    have hsplit : ‖A - B‖⁻¹ • (A - (B + ‖A - B‖ • (c.1 • shellMap m p0 + c.2 • (1 : ShellMat m))))
        = ‖A - B‖⁻¹ • (A - B) - (c.1 • shellMap m p0 + c.2 • (1 : ShellMat m)) := by
      rw [smul_sub, smul_add, smul_smul, inv_mul_cancel₀ (ne_of_gt hpos), one_smul, smul_sub]
      abel
    have hdist : Metric.infDist A (shellPlane m p0) ≤
        ‖A - (B + ‖A - B‖ • (c.1 • shellMap m p0 + c.2 • (1 : ShellMat m)))‖ := by
      have hle : Metric.infDist A (shellPlane m p0) ≤
          dist A (B + ‖A - B‖ • (c.1 • shellMap m p0 + c.2 • (1 : ShellMat m))) :=
        Metric.infDist_le_dist_of_mem (add_smul_mem_shellPlane p0 hB hX ‖A - B‖)
      rwa [dist_eq_norm] at hle
    rw [← hsplit, norm_smul, norm_inv, norm_norm, inv_mul_eq_div, le_div_iff₀ hpos]
    linarith
  · have hbase : shellMap m p0 * (A - B) - (A - B) * shellMap m p0 =
        shellMap m p0 * A - A * shellMap m p0 := by
      have hzero := commutator_eq_zero_of_mem_shellPlane p0 hB
      rw [Matrix.mul_sub, Matrix.sub_mul]
      rw [show shellMap m p0 * A - shellMap m p0 * B - (A * shellMap m p0 - B * shellMap m p0) =
        (shellMap m p0 * A - A * shellMap m p0) - (shellMap m p0 * B - B * shellMap m p0) by abel,
        hzero, sub_zero]
    have hcomm : shellCommutator m (p0, (⟨‖A - B‖⁻¹ • (A - B),
        Submodule.smul_mem _ _ hmem⟩ : chainShell m)) =
        ‖A - B‖⁻¹ * ‖shellMap m p0 * A - A * shellMap m p0‖ := by
      simp only [shellCommutator]
      rw [Matrix.mul_smul, Matrix.smul_mul, ← smul_sub, hbase, norm_smul, norm_inv, norm_norm]
    rw [hcomm, ← mul_assoc]
    have hfrac : Metric.infDist A (shellPlane m p0) * ‖A - B‖⁻¹ ≤ 1 := by
      rw [← div_eq_mul_inv, div_le_one hpos]
      exact hBd
    calc Metric.infDist A (shellPlane m p0) * ‖A - B‖⁻¹ *
          ‖shellMap m p0 * A - A * shellMap m p0‖
        ≤ 1 * ‖shellMap m p0 * A - A * shellMap m p0‖ :=
          mul_le_mul_of_nonneg_right hfrac (norm_nonneg _)
      _ = _ := one_mul _

/-- **Uniform quantitative tangent rigidity along a compact family.**

On a compact family of chain shell operators with invertible edge couplings and a field-rigid edge,
one constant controls the distance to the plane spanned by the identity and the operator. -/
theorem exists_uniform_gamma (hm : 2 ≤ m) {S : Set (ShellParam m)} (hS : IsCompact S)
    (hJ : ∀ p0 ∈ S, ∀ v : Fin m, IsUnit (Matrix.det (p0.2.2 v)))
    (hRig : ∀ p0 ∈ S, ∃ v0 : Fin m, FieldRigid (p0.2.2 v0)) :
    ∃ γ : ℝ, 0 < γ ∧ ∀ p0 ∈ S, ∀ A ∈ chainShell m,
      γ * Metric.infDist A (shellPlane m p0) ≤
        ‖shellMap m p0 * A - A * shellMap m p0‖ := by
  classical
  by_cases hne : (shellTestSet m S).Nonempty
  · obtain ⟨x0, hx0, hmin⟩ := (isCompact_shellTestSet hS).exists_isMinOn hne
      continuous_shellCommutator.continuousOn
    have hx0S : x0.1 ∈ S := hx0.1.1
    have hx0mem : ∀ c : ℝ × ℝ, (1 / 2 : ℝ) ≤
        ‖(x0.2 : ShellMat m) - (c.1 • shellMap m x0.1 + c.2 • (1 : ShellMat m))‖ := by
      intro c
      exact Set.mem_iInter.mp hx0.2 c
    have hγpos : 0 < shellCommutator m x0 := by
      rcases lt_or_eq_of_le (norm_nonneg (shellMap m x0.1 * (x0.2 : ShellMat m) -
        (x0.2 : ShellMat m) * shellMap m x0.1)) with h | h
      · exact h
      · exfalso
        obtain ⟨v0, hv0⟩ := hRig x0.1 hx0S
        have hcomm : shellMap m x0.1 * (x0.2 : ShellMat m) =
            (x0.2 : ShellMat m) * shellMap m x0.1 :=
          sub_eq_zero.mp (norm_eq_zero.mp h.symm)
        obtain ⟨lam, mu, hlm⟩ :=
          (commute_shellMap_iff hm x0.1 (hJ x0.1 hx0S) v0 hv0 (x0.2).2).mp hcomm
        have := hx0mem (lam, mu)
        rw [show (lam, mu).1 = lam from rfl, show (lam, mu).2 = mu from rfl, ← hlm,
          sub_self, norm_zero] at this
        linarith
    refine ⟨shellCommutator m x0, hγpos, fun p0 hp0 A hA => ?_⟩
    rcases eq_or_lt_of_le (Metric.infDist_nonneg (x := A) (s := shellPlane m p0)) with h | h
    · rw [← h, mul_zero]
      exact norm_nonneg _
    · obtain ⟨A', hA'mem, hA'le⟩ := exists_mem_shellTestSet hp0 hA h
      calc shellCommutator m x0 * Metric.infDist A (shellPlane m p0)
          ≤ shellCommutator m (p0, A') * Metric.infDist A (shellPlane m p0) :=
            mul_le_mul_of_nonneg_right (isMinOn_iff.mp hmin _ hA'mem) Metric.infDist_nonneg
        _ = Metric.infDist A (shellPlane m p0) * shellCommutator m (p0, A') := mul_comm _ _
        _ ≤ _ := hA'le
  · refine ⟨1, one_pos, fun p0 hp0 A hA => ?_⟩
    rcases eq_or_lt_of_le (Metric.infDist_nonneg (x := A) (s := shellPlane m p0)) with h | h
    · rw [← h, mul_zero]
      exact norm_nonneg _
    · obtain ⟨A', hA'mem, -⟩ := exists_mem_shellTestSet hp0 hA h
      exact absurd ⟨_, hA'mem⟩ hne

end GaloisForLFunctions.HTGeometry
