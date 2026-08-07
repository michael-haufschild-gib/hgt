import GaloisForLFunctions.RHTower.GammaCoPoissonSoninQuadrantSyzygy
import GaloisForLFunctions.RHTower.BurnolCoPoissonSourceDilation

/-!
# Full-quotient flatness of the co-Poisson bonding maps

Both normalized dilations carry the closed co-Poisson source space one aperture step down, so a
vector of the quotient at level `j+2` is already orthogonal to the source space at level `j+1` after
either dilation.  The source correction in the middle projection therefore drops out of both
composite paths, and each of them acts on the quotient at level `j+2` exactly as the projection onto
the quotient at level `j`.  Hence the two paths agree:

`T_j^+ T_{j+1}^- = T_j^- T_{j+1}^+`  on  `Y_{j+2}`.

No completeness theorem for the zero evaluators is used: the identity is an aperture-monotonicity
statement about the source space, not a statement about zeta zeros.
-/

open Complex Real MeasureTheory Set Filter Topology
open scoped InnerProductSpace

noncomputable section

namespace RHTower

variable {a r : ℝ}

/-- On the extended Sonine space the quotient projection is the vector minus its source
projection. -/
theorem burnolCoPoissonQuotientProjection_eq_sub {b : ℝ} (hb : 0 < b) {v : evenSubspace}
    (hv : v ∈ soninExtendedSpace b) :
    burnolCoPoissonQuotientProjection b hb v = v - burnolCoPoissonSourceProjection b v := by
  letI : CompleteSpace (burnolCoPoissonQuotientSpace b) :=
    (isClosed_burnolCoPoissonQuotientSpace hb).completeSpace_coe
  letI : CompleteSpace (burnolCoPoissonSourceSpace b) :=
    (isClosed_burnolCoPoissonSourceSpace b).completeSpace_coe
  change (burnolCoPoissonQuotientSpace b).starProjection v = _
  refine (burnolCoPoissonQuotientSpace b).eq_starProjection_of_mem_of_inner_eq_zero ?_ ?_
  · refine ⟨(soninExtendedSpace b).sub_mem hv
      (burnolCoPoissonSourceSpace_le_soninExtendedSpace hb
        ((burnolCoPoissonSourceSpace b).starProjection_apply_mem v)), ?_⟩
    exact Submodule.sub_starProjection_mem_orthogonal v
  · intro w hw
    have hsub : v - (v - burnolCoPoissonSourceProjection b v) =
        burnolCoPoissonSourceProjection b v := by abel
    rw [hsub]
    exact Submodule.inner_right_of_mem_orthogonal
      (burnolCoPoissonSourceProjection_apply_mem b v) hw.2

/-- The quotient projection is self-adjoint, in the form the composite paths consume. -/
theorem inner_burnolCoPoissonQuotientProjection_swap {b : ℝ} (hb : 0 < b) (x y : evenSubspace) :
    ⟪burnolCoPoissonQuotientProjection b hb x, y⟫_ℂ =
      ⟪x, burnolCoPoissonQuotientProjection b hb y⟫_ℂ := by
  have hE := adjoint_burnolCoPoissonQuotientProjection b hb
  have key := ContinuousLinearMap.adjoint_inner_left
    (burnolCoPoissonQuotientProjection b hb) y x
  rw [hE] at key
  exact key

/-- A quotient vector two apertures up stays orthogonal to the source space after either
dilation. -/
theorem evenDilation_mem_sourceSpace_orthogonal (ha : 0 < a) (hr : 0 < r) (hr1 : 1 ≤ r) (j : ℕ)
    {x : evenSubspace} (hx : x ∈ burnolCoPoissonQuotientSpace (soninAperture a r (j + 2))) :
    evenDilationCLM r hr x ∈ (burnolCoPoissonSourceSpace (soninAperture a r (j + 1)))ᗮ := by
  intro c hc
  have hstep : evenDilationCLM r⁻¹ (inv_pos.mpr hr) c ∈
      burnolCoPoissonSourceSpace (soninAperture a r (j + 2)) := by
    have h := evenInverseDilation_mem_coPoissonSourceSpace
      (soninAperture_pos ha hr (j + 1)) hr1 hc
    rwa [← soninAperture_succ hr (j + 1)] at h
  have hadj : ContinuousLinearMap.adjoint (evenDilationCLM r hr) =
      evenDilationCLM r⁻¹ (inv_pos.mpr hr) := adjoint_evenDilationCLM r hr
  have hkey := ContinuousLinearMap.adjoint_inner_left (evenDilationCLM r hr) x c
  rw [hadj] at hkey
  rw [← hkey]
  exact Submodule.inner_right_of_mem_orthogonal hstep hx.2

theorem evenInverseDilation_mem_sourceSpace_orthogonal (ha : 0 < a) (hr : 0 < r) (hr1 : 1 ≤ r)
    (j : ℕ) {x : evenSubspace}
    (hx : x ∈ burnolCoPoissonQuotientSpace (soninAperture a r (j + 2))) :
    evenDilationCLM r⁻¹ (inv_pos.mpr hr) x ∈
      (burnolCoPoissonSourceSpace (soninAperture a r (j + 1)))ᗮ := by
  intro c hc
  have hstep : evenDilationCLM r hr c ∈
      burnolCoPoissonSourceSpace (soninAperture a r (j + 2)) := by
    have h := evenDilation_mem_coPoissonSourceSpace
      (soninAperture_pos ha hr (j + 1)) hr1 hc
    rwa [← soninAperture_succ hr (j + 1)] at h
  have hadj : ContinuousLinearMap.adjoint (evenDilationCLM r⁻¹ (inv_pos.mpr hr)) =
      evenDilationCLM r hr := by
    rw [adjoint_evenDilationCLM r⁻¹ (inv_pos.mpr hr)]
    congr 1
    exact inv_inv r
  have hkey := ContinuousLinearMap.adjoint_inner_left
    (evenDilationCLM r⁻¹ (inv_pos.mpr hr)) x c
  rw [hadj] at hkey
  rw [← hkey]
  exact Submodule.inner_right_of_mem_orthogonal hstep hx.2

/-- Both composite paths act on the quotient two apertures up as the projection onto the quotient
below. -/
theorem inner_coPoissonQuotientForward_inverse (ha : 0 < a) (hr : 0 < r) (hr1 : 1 ≤ r) (j : ℕ)
    {x : evenSubspace} (hx : x ∈ burnolCoPoissonQuotientSpace (soninAperture a r (j + 2)))
    {f : evenSubspace} (hf : f ∈ burnolCoPoissonQuotientSpace (soninAperture a r j)) :
    ⟪coPoissonQuotientForward a r ha hr j
        (coPoissonQuotientInverse a r ha hr (j + 1) x), f⟫_ℂ = ⟪x, f⟫_ℂ := by
  have hfL : f ∈ soninExtendedSpace (soninAperture a r j) := hf.1
  have hUf : evenDilationCLM r hr f ∈ soninExtendedSpace (soninAperture a r (j + 1)) :=
    evenDilation_mem_soninExtendedSpace_succ ha hr hr1 j hfL
  have hadj : ContinuousLinearMap.adjoint (evenDilationCLM r hr) =
      evenDilationCLM r⁻¹ (inv_pos.mpr hr) := adjoint_evenDilationCLM r hr
  have hmid := burnolCoPoissonQuotientProjection_eq_sub
    (soninAperture_pos ha hr (j + 1)) hUf
  have hunit : ⟪evenDilationCLM r hr x, evenDilationCLM r hr f⟫_ℂ = ⟪x, f⟫_ℂ :=
    (evenDilationUnitary r hr).inner_map_map x f
  have hzero : ⟪evenDilationCLM r hr x,
      burnolCoPoissonSourceProjection (soninAperture a r (j + 1))
        (evenDilationCLM r hr f)⟫_ℂ = 0 := by
    have hmem := burnolCoPoissonSourceProjection_apply_mem (soninAperture a r (j + 1))
      (evenDilationCLM r hr f)
    have horth := evenDilation_mem_sourceSpace_orthogonal ha hr hr1 j hx
    exact Submodule.inner_left_of_mem_orthogonal hmem horth
  rw [coPoissonQuotientForward, ContinuousLinearMap.comp_apply,
    inner_burnolCoPoissonQuotientProjection_left (soninAperture_pos ha hr j) _ hf,
    ← hadj, ContinuousLinearMap.adjoint_inner_left (evenDilationCLM r hr) f
      (coPoissonQuotientInverse a r ha hr (j + 1) x),
    coPoissonQuotientInverse, ContinuousLinearMap.comp_apply,
    inner_burnolCoPoissonQuotientProjection_swap, hmid, inner_sub_right, hzero, sub_zero, hunit]

theorem inner_coPoissonQuotientInverse_forward (ha : 0 < a) (hr : 0 < r) (hr1 : 1 ≤ r) (j : ℕ)
    {x : evenSubspace} (hx : x ∈ burnolCoPoissonQuotientSpace (soninAperture a r (j + 2)))
    {f : evenSubspace} (hf : f ∈ burnolCoPoissonQuotientSpace (soninAperture a r j)) :
    ⟪coPoissonQuotientInverse a r ha hr j
        (coPoissonQuotientForward a r ha hr (j + 1) x), f⟫_ℂ = ⟪x, f⟫_ℂ := by
  have hfL : f ∈ soninExtendedSpace (soninAperture a r j) := hf.1
  have hUf : evenDilationCLM r⁻¹ (inv_pos.mpr hr) f ∈
      soninExtendedSpace (soninAperture a r (j + 1)) :=
    evenInverseDilation_mem_soninExtendedSpace_succ ha hr hr1 j hfL
  have hadj : ContinuousLinearMap.adjoint (evenDilationCLM r⁻¹ (inv_pos.mpr hr)) =
      evenDilationCLM r hr := by
    rw [adjoint_evenDilationCLM r⁻¹ (inv_pos.mpr hr)]
    congr 1
    exact inv_inv r
  have hmid := burnolCoPoissonQuotientProjection_eq_sub
    (soninAperture_pos ha hr (j + 1)) hUf
  have hunit : ⟪evenDilationCLM r⁻¹ (inv_pos.mpr hr) x,
      evenDilationCLM r⁻¹ (inv_pos.mpr hr) f⟫_ℂ = ⟪x, f⟫_ℂ :=
    (evenDilationUnitary r⁻¹ (inv_pos.mpr hr)).inner_map_map x f
  have hzero : ⟪evenDilationCLM r⁻¹ (inv_pos.mpr hr) x,
      burnolCoPoissonSourceProjection (soninAperture a r (j + 1))
        (evenDilationCLM r⁻¹ (inv_pos.mpr hr) f)⟫_ℂ = 0 := by
    have hmem := burnolCoPoissonSourceProjection_apply_mem (soninAperture a r (j + 1))
      (evenDilationCLM r⁻¹ (inv_pos.mpr hr) f)
    have horth := evenInverseDilation_mem_sourceSpace_orthogonal ha hr hr1 j hx
    exact Submodule.inner_left_of_mem_orthogonal hmem horth
  rw [coPoissonQuotientInverse, ContinuousLinearMap.comp_apply,
    inner_burnolCoPoissonQuotientProjection_left (soninAperture_pos ha hr j) _ hf,
    ← hadj, ContinuousLinearMap.adjoint_inner_left (evenDilationCLM r⁻¹ (inv_pos.mpr hr)) f
      (coPoissonQuotientForward a r ha hr (j + 1) x),
    coPoissonQuotientForward, ContinuousLinearMap.comp_apply,
    inner_burnolCoPoissonQuotientProjection_swap, hmid, inner_sub_right, hzero, sub_zero, hunit]

/-- **Full-quotient flatness.**  The two-path commutator vanishes on the whole co-Poisson
quotient. -/
theorem coPoissonQuotientCommutator_eq_zero (ha : 0 < a) (hr : 0 < r) (hr1 : 1 ≤ r) (j : ℕ)
    {x : evenSubspace} (hx : x ∈ burnolCoPoissonQuotientSpace (soninAperture a r (j + 2))) :
    coPoissonQuotientCommutator a r ha hr j x = 0 := by
  have hEq : coPoissonQuotientForward a r ha hr j
      (coPoissonQuotientInverse a r ha hr (j + 1) x) =
      coPoissonQuotientInverse a r ha hr j
        (coPoissonQuotientForward a r ha hr (j + 1) x) := by
    refine eq_of_forall_inner_eq_of_mem
      (K := burnolCoPoissonQuotientSpace (soninAperture a r j))
      (coPoissonQuotientForward_apply_mem a r ha hr j _)
      (coPoissonQuotientInverse_apply_mem a r ha hr j _) ?_
    intro f hf
    rw [inner_coPoissonQuotientForward_inverse ha hr hr1 j hx hf,
      inner_coPoissonQuotientInverse_forward ha hr hr1 j hx hf]
  rw [coPoissonQuotientCommutator]
  simp only [sub_apply, ContinuousLinearMap.comp_apply, hEq, sub_self]

/-- Both composite paths act on the quotient two apertures up as the projection onto the quotient
below. -/
theorem coPoissonQuotientForward_inverse_eq_projection (ha : 0 < a) (hr : 0 < r) (hr1 : 1 ≤ r)
    (j : ℕ) {x : evenSubspace}
    (hx : x ∈ burnolCoPoissonQuotientSpace (soninAperture a r (j + 2))) :
    coPoissonQuotientForward a r ha hr j (coPoissonQuotientInverse a r ha hr (j + 1) x) =
      burnolCoPoissonQuotientProjection (soninAperture a r j) (soninAperture_pos ha hr j) x := by
  refine eq_of_forall_inner_eq_of_mem
    (K := burnolCoPoissonQuotientSpace (soninAperture a r j))
    (coPoissonQuotientForward_apply_mem a r ha hr j _)
    (burnolCoPoissonQuotientProjection_apply_mem _ (soninAperture_pos ha hr j) _) ?_
  intro f hf
  rw [inner_coPoissonQuotientForward_inverse ha hr hr1 j hx hf,
    inner_burnolCoPoissonQuotientProjection_left (soninAperture_pos ha hr j) _ hf]

theorem coPoissonQuotientInverse_forward_eq_projection (ha : 0 < a) (hr : 0 < r) (hr1 : 1 ≤ r)
    (j : ℕ) {x : evenSubspace}
    (hx : x ∈ burnolCoPoissonQuotientSpace (soninAperture a r (j + 2))) :
    coPoissonQuotientInverse a r ha hr j (coPoissonQuotientForward a r ha hr (j + 1) x) =
      burnolCoPoissonQuotientProjection (soninAperture a r j) (soninAperture_pos ha hr j) x := by
  refine eq_of_forall_inner_eq_of_mem
    (K := burnolCoPoissonQuotientSpace (soninAperture a r j))
    (coPoissonQuotientInverse_apply_mem a r ha hr j _)
    (burnolCoPoissonQuotientProjection_apply_mem _ (soninAperture_pos ha hr j) _) ?_
  intro f hf
  rw [inner_coPoissonQuotientInverse_forward ha hr hr1 j hx hf,
    inner_burnolCoPoissonQuotientProjection_left (soninAperture_pos ha hr j) _ hf]

/-- **The source-error syzygy.**  Combining full-quotient flatness with the exact off-divisor
commutator formula, the whole source-error expression vanishes at every regular point. -/
theorem coPoissonSourceErrorSyzygy {w : ℂ} {hlo : 1 / 2 < w.re} {hhi : w.re < 1}
    {ha : 0 < a} {hr : 0 < r} (hr1 : 1 ≤ r) (j : ℕ) :
    ((starRingEnd ℂ) (soninLadderCharacter w r) •
          coPoissonQuotientInverse a r ha hr j
            (coPoissonLadderDefect w hlo hhi a r ha hr (j + 1)) -
        (starRingEnd ℂ) ((soninLadderCharacter w r)⁻¹) •
          coPoissonQuotientForward a r ha hr j
            (coPoissonLadderDefect w hlo hhi a r ha hr (j + 1))) +
      (coPoissonQuotientInverse a r ha hr j
          (coPoissonQuotientForward a r ha hr (j + 1)
            (coPoissonLadderDefect w hlo hhi a r ha hr (j + 2))) -
        coPoissonQuotientForward a r ha hr j
          (coPoissonQuotientInverse a r ha hr (j + 1)
            (coPoissonLadderDefect w hlo hhi a r ha hr (j + 2)))) = 0 := by
  rw [← coPoissonQuotientCommutator_ladderKernel_offDivisor hr1 j]
  exact coPoissonQuotientCommutator_eq_zero ha hr hr1 j
    (coPoissonLadderKernel_mem hlo hhi ha hr (j + 2))

/-! ## Higher coherence: the endpoint operator -/

/-- The composite of a finite word in the two bonding maps, read from the left. -/
def coPoissonWordOp (a r : ℝ) (ha : 0 < a) (hr : 0 < r) :
    List Bool → ℕ → (evenSubspace →L[ℂ] evenSubspace)
  | [], j => burnolCoPoissonQuotientProjection (soninAperture a r j) (soninAperture_pos ha hr j)
  | (b :: ε), j =>
      (if b then coPoissonQuotientForward a r ha hr j
        else coPoissonQuotientInverse a r ha hr j).comp
        (coPoissonWordOp a r ha hr ε (j + 1))

theorem coPoissonWordOp_apply_mem (ha : 0 < a) (hr : 0 < r) (ε : List Bool) (j : ℕ)
    (x : evenSubspace) :
    coPoissonWordOp a r ha hr ε j x ∈ burnolCoPoissonQuotientSpace (soninAperture a r j) := by
  cases ε with
  | nil => exact burnolCoPoissonQuotientProjection_apply_mem _ (soninAperture_pos ha hr j) _
  | cons b ε =>
      rw [coPoissonWordOp, ContinuousLinearMap.comp_apply]
      by_cases hb : b
      · simp only [hb, if_pos]
        exact coPoissonQuotientForward_apply_mem a r ha hr j _
      · simp only [hb, Bool.false_eq_true, if_false]
        exact coPoissonQuotientInverse_apply_mem a r ha hr j _

theorem norm_coPoissonWordOp_apply_le (ha : 0 < a) (hr : 0 < r) (ε : List Bool) (j : ℕ)
    (x : evenSubspace) : ‖coPoissonWordOp a r ha hr ε j x‖ ≤ ‖x‖ := by
  induction ε generalizing j with
  | nil =>
      letI : CompleteSpace (burnolCoPoissonQuotientSpace (soninAperture a r j)) :=
        (isClosed_burnolCoPoissonQuotientSpace (soninAperture_pos ha hr j)).completeSpace_coe
      exact (burnolCoPoissonQuotientSpace (soninAperture a r j)).norm_starProjection_apply_le x
  | cons b ε ih =>
      rw [coPoissonWordOp, ContinuousLinearMap.comp_apply]
      by_cases hb : b
      · simp only [hb, if_pos]
        exact le_trans (norm_coPoissonQuotientForward_apply_le a r ha hr j _) (ih (j + 1))
      · simp only [hb, Bool.false_eq_true, if_false]
        exact le_trans (norm_coPoissonQuotientInverse_apply_le a r ha hr j _) (ih (j + 1))

/-- **Path independence.**  On the co-Poisson quotient the composite depends only on the numbers of
forward and inverse letters, not on their order. -/
theorem coPoissonWordOp_congr_perm (ha : 0 < a) (hr : 0 < r) (hr1 : 1 ≤ r)
    {ε₁ ε₂ : List Bool} (hperm : ε₁.Perm ε₂) :
    ∀ (j : ℕ) (x : evenSubspace),
      x ∈ burnolCoPoissonQuotientSpace (soninAperture a r (j + ε₁.length)) →
      coPoissonWordOp a r ha hr ε₁ j x = coPoissonWordOp a r ha hr ε₂ j x := by
  induction hperm with
  | nil => intro j x _; rfl
  | cons b h ih =>
      intro j x hx
      rw [coPoissonWordOp, coPoissonWordOp, ContinuousLinearMap.comp_apply,
        ContinuousLinearMap.comp_apply]
      congr 1
      refine ih (j + 1) x ?_
      simp only [List.length_cons, ← Nat.add_assoc] at hx
      rwa [Nat.add_right_comm] at hx
  | swap y z ε =>
      intro j x hx
      have hmem : coPoissonWordOp a r ha hr ε (j + 2) x ∈
          burnolCoPoissonQuotientSpace (soninAperture a r (j + 2)) :=
        coPoissonWordOp_apply_mem ha hr ε (j + 2) x
      have hjj : ∀ (u v : Bool) (t : evenSubspace),
          coPoissonWordOp a r ha hr (u :: v :: ε) j t =
            (if u then coPoissonQuotientForward a r ha hr j
              else coPoissonQuotientInverse a r ha hr j)
              ((if v then coPoissonQuotientForward a r ha hr (j + 1)
                else coPoissonQuotientInverse a r ha hr (j + 1))
                (coPoissonWordOp a r ha hr ε (j + 2) t)) := by
        intro u v t
        rw [coPoissonWordOp, coPoissonWordOp, ContinuousLinearMap.comp_apply,
          ContinuousLinearMap.comp_apply]
      rw [hjj z y x, hjj y z x]
      by_cases hy : y <;> by_cases hz : z <;>
        simp only [hy, hz, if_pos, Bool.false_eq_true, if_false]
      · exact (coPoissonQuotientInverse_forward_eq_projection ha hr hr1 j hmem).trans
          (coPoissonQuotientForward_inverse_eq_projection ha hr hr1 j hmem).symm
      · exact (coPoissonQuotientForward_inverse_eq_projection ha hr hr1 j hmem).trans
          (coPoissonQuotientInverse_forward_eq_projection ha hr hr1 j hmem).symm
  | trans h₁ h₂ ih₁ ih₂ =>
      intro j x hx
      rw [ih₁ j x hx, ih₂ j x (by rwa [← h₁.length_eq])]

/-- **The endpoint operator on the boundary section.**  A word acts on the quotient kernel by the
character raised to the difference of its two letter counts. -/
theorem coPoissonWordOp_ladderKernel {w : ℂ} {hlo : 1 / 2 < w.re} {hhi : w.re < 1}
    {ha : 0 < a} {hr : 0 < r} (hr1 : 1 ≤ r)
    (hann : CoPoissonLadderAnnihilator w hlo hhi a r ha hr) (ε : List Bool) (j : ℕ) :
    coPoissonWordOp a r ha hr ε j
        (coPoissonLadderKernel w hlo hhi a r ha hr (j + ε.length)) =
      ((starRingEnd ℂ) (soninLadderCharacter w r)) ^
          ((ε.count true : ℤ) - (ε.count false : ℤ)) •
        coPoissonLadderKernel w hlo hhi a r ha hr j := by
  have hne : ((starRingEnd ℂ) (soninLadderCharacter w r)) ≠ 0 := by
    simpa using soninLadderCharacter_ne_zero hr w
  induction ε generalizing j with
  | nil =>
      simp only [List.length_nil, Nat.add_zero, List.count_nil, Nat.cast_zero, sub_zero,
        zpow_zero, one_smul]
      exact burnolCoPoissonQuotientProjection_eq_self (soninAperture_pos ha hr j)
        (coPoissonLadderKernel_mem hlo hhi ha hr j)
  | cons b ε ih =>
      have hidx : j + (b :: ε).length = (j + 1) + ε.length := by
        simp only [List.length_cons]
        omega
      rw [coPoissonWordOp, ContinuousLinearMap.comp_apply, hidx, ih (j + 1)]
      by_cases hb : b
      · simp only [hb, if_pos, List.count_cons, beq_self_eq_true, Nat.cast_add, Nat.cast_one]
        rw [ContinuousLinearMap.map_smul, coPoissonQuotientForward_ladderKernel hr1 hann j,
          smul_smul, ← zpow_add_one₀ hne]
        congr 2
        push_cast
        norm_num
        omega
      · simp only [hb, Bool.false_eq_true, if_false, List.count_cons, Bool.false_eq_true,
          beq_self_eq_true, if_true, Nat.cast_add, Nat.cast_one]
        rw [ContinuousLinearMap.map_smul, coPoissonQuotientInverse_ladderKernel hr1 hann j,
          smul_smul, map_inv₀, ← zpow_neg_one ((starRingEnd ℂ) (soninLadderCharacter w r)),
          ← zpow_add₀ hne]
        congr 2
        push_cast
        norm_num
        omega

/-- **The anti-diagonal determinant character.**  The endpoint scalar of a word with `p` forward and
`q` inverse letters, compared with its reflected word, is the relative torsion `abs(λ)^2` raised to
`p - q`; it is trivial exactly on the anti-diagonal `p = q`. -/
theorem coPoissonEndpointScalar_ratio {r : ℝ} (hr : 0 < r) (w : ℂ) (p q : ℤ) :
    ‖((starRingEnd ℂ) (soninLadderCharacter w r)) ^ (p - q)‖ /
        ‖((starRingEnd ℂ) (soninLadderCharacter w r)) ^ (q - p)‖ =
      (‖soninLadderCharacter w r‖ ^ (2 : ℤ)) ^ (p - q) := by
  have hpos : 0 < ‖soninLadderCharacter w r‖ := norm_soninLadderCharacter_pos hr w
  have hconj : ‖(starRingEnd ℂ) (soninLadderCharacter w r)‖ = ‖soninLadderCharacter w r‖ :=
    RCLike.norm_conj _
  rw [norm_zpow, norm_zpow, hconj, ← zpow_sub₀ hpos.ne', ← zpow_mul]
  congr 1
  ring

end RHTower
