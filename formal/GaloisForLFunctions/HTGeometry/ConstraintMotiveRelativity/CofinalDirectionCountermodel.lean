import GaloisForLFunctions.HTGeometry.ConstraintMotiveRelativity.LatticeDirectionCapacity
import Mathlib

/-!
# Cofinal lattice directions do not force rational verticality

Fix an irrational `α` and let `v` be the unit vector along `(1, α)`.  Choosing rational
approximants whose unit directions converge geometrically to `v`, the increasing chart

`G_N = 1 + ∑_{n < N} u_n ⊗ u_n`

has every increment a positive multiple of `a ⊗ a` for a nonzero integer vector `a`, yet its
bounded-capacity sector is `(ℝ ∙ v)ᗮ`, so its limiting cometric kernel is the irrational line
`ℝ ∙ v`, which meets the integer lattice only in `0`.  Lattice provenance at every finite cutoff
therefore does not force a rational vertical fibre; the finite set of direction types in the
finite marked-direction law is load bearing.
-/

open Filter
open scoped Topology RealInnerProductSpace

namespace HTGeometry.ConstraintMotiveRelativity

section CofinalRotation

/-- The Euclidean plane. -/
abbrev Plane : Type := EuclideanSpace ℝ (Fin 2)

theorem norm_planeVec (t : ℝ) : ‖(!₂[1, t] : Plane)‖ = Real.sqrt (1 + t ^ (2 : ℕ)) := by
  rw [EuclideanSpace.norm_eq]
  simp [Fin.sum_univ_two]

theorem inner_planeVec (a b c d : ℝ) :
    ⟪(!₂[a, b] : Plane), !₂[c, d]⟫ = a * c + b * d := by
  simp [EuclideanSpace.inner_eq_star_dotProduct]
  ring

/-- The unit vector in the direction `(1, t)`. -/
noncomputable def planeDir (t : ℝ) : Plane := (Real.sqrt (1 + t ^ (2 : ℕ)))⁻¹ • !₂[1, t]

theorem sqrt_one_add_sq_pos (t : ℝ) : 0 < Real.sqrt (1 + t ^ (2 : ℕ)) :=
  Real.sqrt_pos.2 (by positivity)

theorem planeDir_norm (t : ℝ) : ‖planeDir t‖ = 1 := by
  have hpos := sqrt_one_add_sq_pos t
  rw [planeDir, norm_smul, norm_planeVec, norm_inv, Real.norm_eq_abs, abs_of_pos hpos,
    inv_mul_cancel₀ (ne_of_gt hpos)]

theorem continuous_planeDir : Continuous planeDir := by
  have h1 : Continuous fun t : ℝ => (!₂[1, t] : Plane) := by fun_prop
  have h2 : Continuous fun t : ℝ => (Real.sqrt (1 + t ^ (2 : ℕ)))⁻¹ := by
    refine Continuous.inv₀ ?_ fun t => ne_of_gt (sqrt_one_add_sq_pos t)
    fun_prop
  exact h2.smul h1

/-- Rational directions approximate any real direction geometrically fast. -/
theorem exists_rat_planeDir (α : ℝ) (n : ℕ) :
    ∃ q : ℚ, ‖planeDir (q : ℝ) - planeDir α‖ < (1 / 2 : ℝ) ^ n := by
  have hpos : (0 : ℝ) < (1 / 2 : ℝ) ^ n := by positivity
  have hcont := continuous_planeDir.continuousAt (x := α)
  have hball : {t : ℝ | ‖planeDir t - planeDir α‖ < (1 / 2 : ℝ) ^ n} ∈ 𝓝 α := by
    have := hcont (Metric.ball_mem_nhds (planeDir α) hpos)
    simpa [Metric.mem_ball, dist_eq_norm, Set.preimage] using this
  obtain ⟨ε, hε, hsub⟩ := Metric.mem_nhds_iff.1 hball
  obtain ⟨q, hq⟩ := exists_rat_near α hε
  exact ⟨q, hsub (by simpa [Metric.mem_ball, Real.dist_eq, abs_sub_comm] using hq)⟩

/-- The chosen rational approximants. -/
noncomputable def rotApprox (α : ℝ) (n : ℕ) : ℚ := Classical.choose (exists_rat_planeDir α n)

theorem rotApprox_spec (α : ℝ) (n : ℕ) :
    ‖planeDir ((rotApprox α n : ℚ) : ℝ) - planeDir α‖ < (1 / 2 : ℝ) ^ n :=
  Classical.choose_spec (exists_rat_planeDir α n)

/-- The cofinally rotating unit directions. -/
noncomputable def rotDir (α : ℝ) (n : ℕ) : Plane := planeDir ((rotApprox α n : ℚ) : ℝ)

theorem rotDir_close (α : ℝ) (n : ℕ) : ‖rotDir α n - planeDir α‖ < (1 / 2 : ℝ) ^ n :=
  rotApprox_spec α n

/-- The cofinally rotating chart `G_N = 1 + ∑_{n < N} u_n ⊗ u_n`. -/
noncomputable def rotGram (α : ℝ) (N : ℕ) : Plane →ₗ[ℝ] Plane :=
  LinearMap.id + ∑ n ∈ Finset.range N, rankOne (rotDir α n)

theorem inner_rotGram (α : ℝ) (N : ℕ) (x : Plane) :
    ⟪rotGram α N x, x⟫ = ‖x‖ ^ (2 : ℕ) + ∑ n ∈ Finset.range N, ⟪rotDir α n, x⟫ ^ (2 : ℕ) := by
  simp only [rotGram, LinearMap.add_apply, LinearMap.id_apply, LinearMap.coe_sum,
    Finset.sum_apply, inner_add_left, sum_inner, inner_rankOne, real_inner_self_eq_norm_sq]

theorem rotGram_symm (α : ℝ) (N : ℕ) (x y : Plane) :
    ⟪rotGram α N x, y⟫ = ⟪x, rotGram α N y⟫ := by
  simp only [rotGram, LinearMap.add_apply, LinearMap.id_apply, LinearMap.coe_sum,
    Finset.sum_apply, inner_add_left, inner_add_right, sum_inner, inner_sum, rankOne_symm]

/-- The cofinally rotating capacity chart. -/
noncomputable def rotChart (α : ℝ) : CapacityChart Plane where
  gram := rotGram α
  gram_symm := rotGram_symm α
  gram_pos := by
    intro N x hx
    rw [inner_rotGram]
    have h1 : 0 < ‖x‖ ^ (2 : ℕ) := by
      have : ‖x‖ ≠ 0 := norm_ne_zero_iff.2 hx
      exact lt_of_le_of_ne (sq_nonneg _) (Ne.symm (pow_ne_zero 2 this))
    have h2 : 0 ≤ ∑ n ∈ Finset.range N, ⟪rotDir α n, x⟫ ^ (2 : ℕ) :=
      Finset.sum_nonneg fun n _ => sq_nonneg _
    linarith
  gram_mono := by
    intro x m n hmn
    show ⟪rotGram α m x, x⟫ ≤ ⟪rotGram α n x, x⟫
    rw [inner_rotGram, inner_rotGram]
    have hsub : Finset.range m ⊆ Finset.range n := fun k hk =>
      Finset.mem_range.2 (lt_of_lt_of_le (Finset.mem_range.1 hk) hmn)
    have := Finset.sum_le_sum_of_subset_of_nonneg hsub
      (fun n _ _ => sq_nonneg ⟪rotDir α n, x⟫)
    linarith

@[simp] theorem rotChart_gram (α : ℝ) (N : ℕ) : (rotChart α).gram N = rotGram α N := rfl

/-- **The bounded-capacity sector is the polar of the limiting irrational direction.** -/
theorem rotChart_boundedCapacity (α : ℝ) :
    (rotChart α).boundedCapacity = (((ℝ ∙ planeDir α))ᗮ : Set Plane) := by
  ext x
  rw [SetLike.mem_coe, Submodule.mem_orthogonal_singleton_iff_inner_right]
  constructor
  · rintro ⟨M, hM⟩
    by_contra hne
    set c : ℝ := ⟪planeDir α, x⟫ with hc
    have hc2 : 0 < c ^ (2 : ℕ) := lt_of_le_of_ne (sq_nonneg _) (Ne.symm (pow_ne_zero 2 hne))
    obtain ⟨n₀, hn₀⟩ : ∃ n₀ : ℕ, ∀ n ≥ n₀, (1 / 2 : ℝ) ^ n * ‖x‖ < |c| / 2 := by
      have hlim : Tendsto (fun n : ℕ => (1 / 2 : ℝ) ^ n * ‖x‖) atTop (𝓝 (0 * ‖x‖)) :=
        ((tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)).mul_const ‖x‖)
      rw [zero_mul] at hlim
      have habs : 0 < |c| / 2 := by
        have : 0 < |c| := abs_pos.2 hne
        linarith
      exact (hlim.eventually (gt_mem_nhds habs)).exists_forall_of_atTop
    have hterm : ∀ n ≥ n₀, c ^ (2 : ℕ) / 4 ≤ ⟪rotDir α n, x⟫ ^ (2 : ℕ) := by
      intro n hn
      have hdiff : |⟪rotDir α n, x⟫ - c| ≤ (1 / 2 : ℝ) ^ n * ‖x‖ := by
        have h1 : ⟪rotDir α n, x⟫ - c = ⟪rotDir α n - planeDir α, x⟫ := by
          rw [inner_sub_left, hc]
        rw [h1, ← Real.norm_eq_abs]
        exact le_trans (norm_inner_le_norm _ _)
          (mul_le_mul_of_nonneg_right (rotDir_close α n).le (norm_nonneg x))
      have hlt := hn₀ n hn
      have habs : |c| / 2 ≤ |⟪rotDir α n, x⟫| := by
        have h2 := abs_sub_abs_le_abs_sub c ⟪rotDir α n, x⟫
        rw [abs_sub_comm c] at h2
        have := abs_sub_comm ⟪rotDir α n, x⟫ c
        nlinarith [abs_nonneg ⟪rotDir α n, x⟫, abs_nonneg c, hdiff, hlt,
          abs_sub_abs_le_abs_sub ⟪rotDir α n, x⟫ c]
      nlinarith [abs_nonneg c, abs_nonneg ⟪rotDir α n, x⟫, sq_abs c,
        sq_abs ⟪rotDir α n, x⟫]
    obtain ⟨N, hN⟩ := exists_nat_gt ((M - ‖x‖ ^ (2 : ℕ)) / (c ^ (2 : ℕ) / 4) + n₀)
    have hbound : ⟪rotGram α (N + n₀) x, x⟫ ≤ M := hM (Set.mem_range_self (N + n₀))
    rw [inner_rotGram] at hbound
    have hsplit : ∑ n ∈ Finset.range (N + n₀), ⟪rotDir α n, x⟫ ^ (2 : ℕ)
        ≥ ∑ n ∈ Finset.Ico n₀ (N + n₀), ⟪rotDir α n, x⟫ ^ (2 : ℕ) := by
      refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun n _ _ => sq_nonneg _)
      intro n hn
      simp only [Finset.mem_Ico] at hn
      simp only [Finset.mem_range]
      exact hn.2
    have hlow : ∑ n ∈ Finset.Ico n₀ (N + n₀), ⟪rotDir α n, x⟫ ^ (2 : ℕ) ≥ (N : ℝ) * (c ^ (2 : ℕ) / 4) := by
      have hcard : (Finset.Ico n₀ (N + n₀)).card = N := by
        rw [Nat.card_Ico]; omega
      calc ∑ n ∈ Finset.Ico n₀ (N + n₀), ⟪rotDir α n, x⟫ ^ (2 : ℕ)
          ≥ ∑ _n ∈ Finset.Ico n₀ (N + n₀), c ^ (2 : ℕ) / 4 :=
            Finset.sum_le_sum fun n hn => hterm n (Finset.mem_Ico.1 hn).1
        _ = (N : ℝ) * (c ^ (2 : ℕ) / 4) := by rw [Finset.sum_const, hcard, nsmul_eq_mul]
    have hNpos : (M - ‖x‖ ^ (2 : ℕ)) / (c ^ (2 : ℕ) / 4) < (N : ℝ) := by
      have : (0 : ℝ) ≤ (n₀ : ℝ) := Nat.cast_nonneg n₀
      linarith
    rw [div_lt_iff₀ (by linarith)] at hNpos
    linarith
  · intro hx
    refine ⟨‖x‖ ^ (2 : ℕ) + ‖x‖ ^ (2 : ℕ) * 2, ?_⟩
    rintro s ⟨N, rfl⟩
    show ⟪rotGram α N x, x⟫ ≤ ‖x‖ ^ (2 : ℕ) + ‖x‖ ^ (2 : ℕ) * 2
    rw [inner_rotGram]
    refine add_le_add le_rfl ?_
    have hterm : ∀ n, ⟪rotDir α n, x⟫ ^ (2 : ℕ) ≤ ‖x‖ ^ (2 : ℕ) * (1 / 4 : ℝ) ^ n := by
      intro n
      have h1 : ⟪rotDir α n, x⟫ = ⟪rotDir α n - planeDir α, x⟫ := by
        rw [inner_sub_left, hx, sub_zero]
      have h2 : |⟪rotDir α n, x⟫| ≤ (1 / 2 : ℝ) ^ n * ‖x‖ := by
        rw [h1, ← Real.norm_eq_abs]
        exact le_trans (norm_inner_le_norm _ _)
          (mul_le_mul_of_nonneg_right (rotDir_close α n).le (norm_nonneg x))
      have hpow : ((1 / 2 : ℝ) ^ n) ^ (2 : ℕ) = (1 / 4 : ℝ) ^ n := by
        rw [← pow_mul, mul_comm, pow_mul]
        norm_num
      have h4 : ⟪rotDir α n, x⟫ ^ (2 : ℕ) ≤ ((1 / 2 : ℝ) ^ n * ‖x‖) ^ (2 : ℕ) := by
        rw [← sq_abs]
        have hnn : (0:ℝ) ≤ |⟪rotDir α n, x⟫| := abs_nonneg _
        nlinarith [h2, hnn]
      have h5 : ((1 / 2 : ℝ) ^ n * ‖x‖) ^ (2 : ℕ) = ‖x‖ ^ (2 : ℕ) * (1 / 4 : ℝ) ^ n := by
        rw [mul_pow, hpow]; ring
      linarith
    have hgeo : ∑ n ∈ Finset.range N, ‖x‖ ^ (2 : ℕ) * (1 / 4 : ℝ) ^ n ≤ ‖x‖ ^ (2 : ℕ) * 2 := by
      rw [← Finset.mul_sum]
      have hsum : ∑ n ∈ Finset.range N, (1 / 4 : ℝ) ^ n ≤ 2 := by
        rw [geom_sum_eq (by norm_num : (1 / 4 : ℝ) ≠ 1)]
        have hle : (0 : ℝ) ≤ ((1 : ℝ) / 4) ^ N := by positivity
        rw [div_le_iff_of_neg (by norm_num : (1 / 4 : ℝ) - 1 < 0)]
        linarith
      nlinarith [sq_nonneg ‖x‖, hsum]
    exact le_trans (Finset.sum_le_sum fun n _ => hterm n) hgeo

/-- **The limiting cometric kernel is the irrational line.** -/
theorem rotChart_ker (α : ℝ) :
    LinearMap.ker (rotChart α).cometricLimit = ℝ ∙ planeDir α := by
  have h := (rotChart α).boundedCapacity_eq_orthogonal
  rw [rotChart_boundedCapacity] at h
  have h3 : ((ℝ ∙ planeDir α))ᗮ = (LinearMap.ker (rotChart α).cometricLimit)ᗮ :=
    SetLike.coe_injective h
  have h4 := congrArg (fun S : Submodule ℝ Plane => Sᗮ) h3
  simpa [Submodule.orthogonal_orthogonal] using h4.symm

/-- **The limiting line is irrational.**  It meets the integer lattice only in the origin. -/
theorem rotChart_line_lattice_trivial {α : ℝ} (hα : Irrational α) (z : Fin 2 → ℤ)
    (hz : (!₂[((z 0 : ℤ) : ℝ), ((z 1 : ℤ) : ℝ)] : Plane) ∈ ℝ ∙ planeDir α) : z = 0 := by
  obtain ⟨t, ht⟩ := Submodule.mem_span_singleton.1 hz
  have hs : (0 : ℝ) < (Real.sqrt (1 + α ^ (2 : ℕ)))⁻¹ := inv_pos.2 (sqrt_one_add_sq_pos α)
  have hval : (!₂[((z 0 : ℤ) : ℝ), ((z 1 : ℤ) : ℝ)] : Plane)
      = (t * (Real.sqrt (1 + α ^ (2 : ℕ)))⁻¹) • (!₂[1, α] : Plane) := by
    rw [← ht, planeDir, smul_smul]
  have h0 : ((z 0 : ℤ) : ℝ) = t * (Real.sqrt (1 + α ^ (2 : ℕ)))⁻¹ := by
    have := congrFun (congrArg (fun y : Plane => (y : Fin 2 → ℝ)) hval) 0
    simpa using this
  have h1 : ((z 1 : ℤ) : ℝ) = t * (Real.sqrt (1 + α ^ (2 : ℕ)))⁻¹ * α := by
    have := congrFun (congrArg (fun y : Plane => (y : Fin 2 → ℝ)) hval) 1
    simpa using this
  have hz0 : z 0 = 0 := by
    by_contra hne
    have hz0R : ((z 0 : ℤ) : ℝ) ≠ 0 := Int.cast_ne_zero.2 hne
    have : α = ((z 1 : ℤ) : ℝ) / ((z 0 : ℤ) : ℝ) := by
      rw [h1, ← h0]
      field_simp
    exact hα ⟨(z 1 : ℚ) / (z 0 : ℚ), by push_cast [this]; ring⟩
  have htz : t * (Real.sqrt (1 + α ^ (2 : ℕ)))⁻¹ = 0 := by rw [← h0, hz0]; simp
  have hz1 : z 1 = 0 := by
    have : ((z 1 : ℤ) : ℝ) = 0 := by rw [h1, htz, zero_mul]
    exact_mod_cast this
  funext i
  fin_cases i <;> simp [hz0, hz1]

section LatticeProvenance

/-- Every rotating direction is a positive multiple of a nonzero integer vector, so every chart
increment has marked lattice provenance at that finite cutoff. -/
theorem rotDir_lattice_provenance (α : ℝ) (n : ℕ) :
    ∃ (a : Fin 2 → ℤ) (c : ℝ), 0 < c ∧ a ≠ 0 ∧
      rankOne (rotDir α n) = c • rankOne (!₂[((a 0 : ℤ) : ℝ), ((a 1 : ℤ) : ℝ)] : Plane) := by
  set q : ℚ := rotApprox α n with hq
  set den : ℤ := (q.den : ℤ) with hden
  set num : ℤ := q.num with hnum
  have hdpos : (0 : ℝ) < (den : ℝ) := by
    rw [hden]
    exact_mod_cast (Nat.cast_pos.2 q.pos : (0 : ℝ) < (q.den : ℝ))
  have hqval : (q : ℝ) = (num : ℝ) / (den : ℝ) := by
    rw [hnum, hden]
    push_cast
    rw [Rat.cast_def]
  set s : ℝ := (Real.sqrt (1 + (q : ℝ) ^ (2 : ℕ)))⁻¹ * ((den : ℝ))⁻¹ with hs
  have hspos : 0 < s := by
    refine mul_pos (inv_pos.2 (sqrt_one_add_sq_pos _)) (inv_pos.2 hdpos)
  have hbase : (!₂[1, (q : ℝ)] : Plane)
      = ((den : ℝ))⁻¹ • (!₂[((den : ℤ) : ℝ), ((num : ℤ) : ℝ)] : Plane) := by
    ext i
    fin_cases i
    · simp [inv_mul_cancel₀ (ne_of_gt hdpos)]
    · simp [hqval, div_eq_inv_mul]
  have hvec : rotDir α n = s • (!₂[((den : ℤ) : ℝ), ((num : ℤ) : ℝ)] : Plane) := by
    rw [rotDir, planeDir, hbase, hs, mul_smul]
  refine ⟨![den, num], s ^ (2 : ℕ), by positivity, ?_, ?_⟩
  · intro hzero
    have : den = 0 := by
      have := congrFun hzero 0
      simpa using this
    rw [this] at hdpos
    simp at hdpos
  · rw [hvec, rankOne_smul]
    congr 2

end LatticeProvenance

end CofinalRotation

end HTGeometry.ConstraintMotiveRelativity
