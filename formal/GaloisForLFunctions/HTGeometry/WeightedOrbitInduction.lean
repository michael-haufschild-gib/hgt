import GaloisForLFunctions.HTGeometry.OrbitInductionEssentialization

/-!
# Weighted orbit induction: norm, reduced gap, and closed range

A bounded scalar amplitude family `a` weights the transported blocks of an orbit induction.  This
module proves the exact operator-norm law `(WOI.3)`, the kernel identification, the transverse
lower bound `(WOI.4)`, and the closed-range classification `(WOI.5)`: the weighted induction has
closed range exactly when the local operator does **and** the amplitudes have a uniform nonzero
gap.  It then develops the finite truncations of the amplitude family, the tail supremum
`tailSup a = ⨅_F ⨆_{i ∉ F} |a i|`, and proves `(WOI.7)`: the essential norm of the weighted
induction is exactly `tailSup a · ‖D‖` whenever the local block is compact.
-/

namespace GaloisForLFunctions.HTGeometry

open Filter RHTower
open scoped ENNReal Topology InnerProductSpace

noncomputable section

section Weighted

variable {I : Type} [Nonempty I] {H K : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

/-- `(WOI.1)`  The transported block scaled by the source amplitude. -/
def weightedBlock (a : I → ℂ) (D : H →L[ℂ] K) (U : I → (H ≃ₗᵢ[ℂ] H))
    (V : I → (K ≃ₗᵢ[ℂ] K)) (i : I) : H →L[ℂ] K := a i • orbitBlock D U V i

omit [Nonempty I] [CompleteSpace H] [CompleteSpace K] in
@[simp] theorem weightedBlock_apply (a : I → ℂ) (D : H →L[ℂ] K) (U : I → (H ≃ₗᵢ[ℂ] H))
    (V : I → (K ≃ₗᵢ[ℂ] K)) (i : I) (x : H) :
    weightedBlock a D U V i x = a i • V i (D ((U i).symm x)) := rfl

omit [Nonempty I] [CompleteSpace H] [CompleteSpace K] in
theorem norm_weightedBlock (a : I → ℂ) (D : H →L[ℂ] K) (U : I → (H ≃ₗᵢ[ℂ] H))
    (V : I → (K ≃ₗᵢ[ℂ] K)) (i : I) :
    ‖weightedBlock a D U V i‖ = ‖a i‖ * ‖D‖ := by
  rw [weightedBlock, norm_smul, norm_orbitBlock]

/-- `(WOI.2)`  The amplitude supremum `‖a‖_∞`. -/
def ampSup (a : I → ℂ) : ℝ := ⨆ i, ‖a i‖

omit [Nonempty I] in
theorem le_ampSup {a : I → ℂ} (hbdd : BddAbove (Set.range fun i => ‖a i‖)) (i : I) :
    ‖a i‖ ≤ ampSup a := le_ciSup hbdd i

theorem ampSup_nonneg {a : I → ℂ} (hbdd : BddAbove (Set.range fun i => ‖a i‖)) :
    0 ≤ ampSup a :=
  le_trans (norm_nonneg _) (le_ampSup hbdd (Classical.arbitrary I))

theorem ampSup_le {a : I → ℂ} {c : ℝ} (h : ∀ i, ‖a i‖ ≤ c) : ampSup a ≤ c :=
  ciSup_le h

/-- `(WOI.1)`  The weighted orbit induction. -/
def weightedInduction (a : I → ℂ) (D : H →L[ℂ] K) (U : I → (H ≃ₗᵢ[ℂ] H))
    (V : I → (K ≃ₗᵢ[ℂ] K)) (hbdd : BddAbove (Set.range fun i => ‖a i‖)) :
    lp (fun _ : I => H) 2 →L[ℂ] lp (fun _ : I => K) 2 :=
  rectangularBlockOperator (E := fun _ : I => H) (F := fun _ : I => K)
    (fun i => weightedBlock a D U V i)
    (mul_nonneg (ampSup_nonneg hbdd) (norm_nonneg D))
    (fun i => by
      rw [norm_weightedBlock]
      exact mul_le_mul_of_nonneg_right (le_ampSup hbdd i) (norm_nonneg D))

omit [CompleteSpace H] [CompleteSpace K] in
@[simp] theorem weightedInduction_apply (a : I → ℂ) (D : H →L[ℂ] K) (U : I → (H ≃ₗᵢ[ℂ] H))
    (V : I → (K ≃ₗᵢ[ℂ] K)) (hbdd : BddAbove (Set.range fun i => ‖a i‖))
    (x : lp (fun _ : I => H) 2) (i : I) :
    weightedInduction a D U V hbdd x i = a i • V i (D ((U i).symm (x i))) := rfl

omit [CompleteSpace H] [CompleteSpace K] in
theorem weightedInduction_single [DecidableEq I] (a : I → ℂ) (D : H →L[ℂ] K)
    (U : I → (H ≃ₗᵢ[ℂ] H)) (V : I → (K ≃ₗᵢ[ℂ] K))
    (hbdd : BddAbove (Set.range fun i => ‖a i‖)) (i : I) (x : H) :
    weightedInduction a D U V hbdd (lp.single 2 i x)
      = lp.single 2 i (weightedBlock a D U V i x) :=
  rectangularBlockOperator_single (E := fun _ : I => H) (F := fun _ : I => K) _ _ _ i x

omit [CompleteSpace H] [CompleteSpace K] in
theorem norm_weightedInduction_le (a : I → ℂ) (D : H →L[ℂ] K) (U : I → (H ≃ₗᵢ[ℂ] H))
    (V : I → (K ≃ₗᵢ[ℂ] K)) (hbdd : BddAbove (Set.range fun i => ‖a i‖)) :
    ‖weightedInduction a D U V hbdd‖ ≤ ampSup a * ‖D‖ := by
  refine LinearMap.mkContinuous_norm_le _
    (mul_nonneg (ampSup_nonneg hbdd) (norm_nonneg D)) ?_
  exact rectangularBlockOperatorLinear_norm_le _ _ _

omit [CompleteSpace H] [CompleteSpace K] in
theorem norm_weightedBlock_le_norm_weightedInduction [DecidableEq I] (a : I → ℂ)
    (D : H →L[ℂ] K) (U : I → (H ≃ₗᵢ[ℂ] H)) (V : I → (K ≃ₗᵢ[ℂ] K))
    (hbdd : BddAbove (Set.range fun i => ‖a i‖)) (i : I) :
    ‖a i‖ * ‖D‖ ≤ ‖weightedInduction a D U V hbdd‖ := by
  rw [← norm_weightedBlock a D U V i]
  refine ContinuousLinearMap.opNorm_le_bound _
    (norm_nonneg (weightedInduction a D U V hbdd)) fun x => ?_
  have h := (weightedInduction a D U V hbdd).le_opNorm (lp.single 2 i x)
  rw [weightedInduction_single a D U V hbdd i x] at h
  have h1 : ‖(lp.single 2 i (weightedBlock a D U V i x) : lp (fun _ : I => K) 2)‖
      = ‖weightedBlock a D U V i x‖ :=
    lp.norm_single (E := fun _ : I => K) (by norm_num) i _
  have h2 : ‖(lp.single 2 i x : lp (fun _ : I => H) 2)‖ = ‖x‖ :=
    lp.norm_single (E := fun _ : I => H) (by norm_num) i x
  rw [h1, h2] at h
  exact h

omit [CompleteSpace H] [CompleteSpace K] in
/-- **Theorem 2.1, `(WOI.3)`.**  The weighted induction has operator norm `‖a‖_∞ ‖D‖`. -/
theorem norm_weightedInduction [DecidableEq I] (a : I → ℂ) (D : H →L[ℂ] K)
    (U : I → (H ≃ₗᵢ[ℂ] H)) (V : I → (K ≃ₗᵢ[ℂ] K))
    (hbdd : BddAbove (Set.range fun i => ‖a i‖)) :
    ‖weightedInduction a D U V hbdd‖ = ampSup a * ‖D‖ := by
  refine le_antisymm (norm_weightedInduction_le a D U V hbdd) ?_
  rcases eq_or_lt_of_le (norm_nonneg D) with hD | hD
  · rw [← hD, mul_zero]
    exact norm_nonneg (weightedInduction a D U V hbdd)
  · rw [← le_div_iff₀ hD]
    refine ampSup_le fun i => ?_
    rw [le_div_iff₀ hD]
    exact norm_weightedBlock_le_norm_weightedInduction a D U V hbdd i

/-! ## The reduced gap and closed range -/

omit [CompleteSpace H] [CompleteSpace K] in
theorem weightedInduction_eq_zero_iff (a : I → ℂ) (D : H →L[ℂ] K) (U : I → (H ≃ₗᵢ[ℂ] H))
    (V : I → (K ≃ₗᵢ[ℂ] K)) (hbdd : BddAbove (Set.range fun i => ‖a i‖)) (ha : ∀ i, a i ≠ 0)
    (ξ : lp (fun _ : I => H) 2) :
    weightedInduction a D U V hbdd ξ = 0 ↔ orbitInduction D U V ξ = 0 := by
  rw [orbitInduction_eq_zero_iff]
  constructor
  · intro h i
    have hi := congrArg (fun y : lp (fun _ : I => K) 2 => (y : ∀ _ : I, K) i) h
    simp only [weightedInduction_apply, lp.coeFn_zero, Pi.zero_apply] at hi
    rcases smul_eq_zero.mp hi with h0 | h0
    · exact absurd h0 (ha i)
    · have : V i (D ((U i).symm ((ξ : ∀ _ : I, H) i))) = V i 0 := by rw [h0, map_zero]
      exact (V i).injective this
  · intro h
    ext i
    simp only [weightedInduction_apply, lp.coeFn_zero, Pi.zero_apply, h i, map_zero, smul_zero]

omit [CompleteSpace H] [CompleteSpace K] in
theorem ker_weightedInduction (a : I → ℂ) (D : H →L[ℂ] K) (U : I → (H ≃ₗᵢ[ℂ] H))
    (V : I → (K ≃ₗᵢ[ℂ] K)) (hbdd : BddAbove (Set.range fun i => ‖a i‖)) (ha : ∀ i, a i ≠ 0) :
    LinearMap.ker (weightedInduction a D U V hbdd : lp (fun _ : I => H) 2 →ₗ[ℂ]
        lp (fun _ : I => K) 2)
      = LinearMap.ker (orbitInduction D U V : lp (fun _ : I => H) 2 →ₗ[ℂ]
        lp (fun _ : I => K) 2) := by
  ext ξ
  simp only [LinearMap.mem_ker, ContinuousLinearMap.coe_coe]
  exact weightedInduction_eq_zero_iff a D U V hbdd ha ξ

omit [CompleteSpace H] [CompleteSpace K] in
theorem norm_weightedInduction_apply_coe (a : I → ℂ) (D : H →L[ℂ] K) (U : I → (H ≃ₗᵢ[ℂ] H))
    (V : I → (K ≃ₗᵢ[ℂ] K)) (hbdd : BddAbove (Set.range fun i => ‖a i‖))
    (ξ : lp (fun _ : I => H) 2) (i : I) :
    ‖(weightedInduction a D U V hbdd ξ : ∀ _ : I, K) i‖
      = ‖a i‖ * ‖D ((U i).symm ((ξ : ∀ _ : I, H) i))‖ := by
  rw [weightedInduction_apply, norm_smul, (V i).norm_map]

omit [CompleteSpace H] [CompleteSpace K] in
/-- `(WOI.4)`  A uniform amplitude gap and a transverse lower bound for `D` give a transverse
lower bound for the weighted induction, with the product constant. -/
theorem le_norm_weightedInduction [DecidableEq I] (a : I → ℂ) (D : H →L[ℂ] K)
    (U : I → (H ≃ₗᵢ[ℂ] H)) (V : I → (K ≃ₗᵢ[ℂ] K))
    (hbdd : BddAbove (Set.range fun i => ‖a i‖)) (ha : ∀ i, a i ≠ 0)
    {α c : ℝ} (hα : 0 ≤ α) (hc : 0 ≤ c) (hamp : ∀ i, α ≤ ‖a i‖)
    (h : ∀ x ∈ (LinearMap.ker (D : H →ₗ[ℂ] K))ᗮ, c * ‖x‖ ≤ ‖D x‖)
    (ξ : lp (fun _ : I => H) 2)
    (hξ : ξ ∈ (LinearMap.ker (weightedInduction a D U V hbdd : lp (fun _ : I => H) 2 →ₗ[ℂ]
      lp (fun _ : I => K) 2))ᗮ) :
    (α * c) * ‖ξ‖ ≤ ‖weightedInduction a D U V hbdd ξ‖ := by
  rw [ker_weightedInduction a D U V hbdd ha] at hξ
  refine lp_le_norm_of_blockwise (by positivity) ξ _ fun i => ?_
  have hmem := coeFn_mem_ker_orthogonal D U V ξ hξ i
  rw [mem_ker_orbitBlock_orthogonal_iff] at hmem
  have hb := h _ hmem
  rw [(U i).symm.norm_map] at hb
  rw [norm_weightedInduction_apply_coe]
  calc α * c * ‖(ξ : ∀ _ : I, H) i‖ = α * (c * ‖(ξ : ∀ _ : I, H) i‖) := by ring
    _ ≤ α * ‖D ((U i).symm ((ξ : ∀ _ : I, H) i))‖ := by
        exact mul_le_mul_of_nonneg_left hb hα
    _ ≤ ‖a i‖ * ‖D ((U i).symm ((ξ : ∀ _ : I, H) i))‖ :=
        mul_le_mul_of_nonneg_right (hamp i) (norm_nonneg _)

omit [CompleteSpace K] in
theorem exists_unit_mem_ker_orthogonal (D : H →L[ℂ] K) (hD : D ≠ 0) :
    ∃ x : H, x ∈ (LinearMap.ker (D : H →ₗ[ℂ] K))ᗮ ∧ ‖x‖ = 1 ∧ D x ≠ 0 := by
  obtain ⟨y, hy⟩ : ∃ y : H, D y ≠ 0 := by
    by_contra h
    push Not at h
    exact hD (ContinuousLinearMap.ext h)
  set K0 : Submodule ℂ H := LinearMap.ker (D : H →ₗ[ℂ] K) with hK0
  have hsplit : K0.starProjection y + K0ᗮ.starProjection y = y :=
    K0.starProjection_add_starProjection_orthogonal y
  have hker : D (K0.starProjection y) = 0 := K0.starProjection_apply_mem y
  have hval : D (K0ᗮ.starProjection y) = D y := by
    have := congrArg D hsplit
    rw [map_add, hker, zero_add] at this
    exact this
  have hmem : K0ᗮ.starProjection y ∈ K0ᗮ := K0ᗮ.starProjection_apply_mem y
  have hne : K0ᗮ.starProjection y ≠ 0 := by
    intro h0
    rw [h0, map_zero] at hval
    exact hy hval.symm
  have hnorm : 0 < ‖K0ᗮ.starProjection y‖ := norm_pos_iff.mpr hne
  refine ⟨((‖K0ᗮ.starProjection y‖⁻¹ : ℝ) : ℂ) • K0ᗮ.starProjection y, ?_, ?_, ?_⟩
  · exact Submodule.smul_mem _ _ hmem
  · rw [norm_smul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (inv_pos.mpr hnorm), inv_mul_cancel₀ hnorm.ne']
  · rw [map_smul, hval]
    simp only [ne_eq, smul_eq_zero, not_or]
    exact ⟨by simpa using hnorm.ne', hy⟩

omit [CompleteSpace K] in
/-- **Theorem 2.1, `(WOI.5)`.**  A transverse lower bound for the weighted induction forces both a
uniform amplitude gap and a transverse lower bound for the local operator. -/
theorem hasTransverseLowerBound_weightedInduction_imp [DecidableEq I] (a : I → ℂ)
    (D : H →L[ℂ] K) (U : I → (H ≃ₗᵢ[ℂ] H)) (V : I → (K ≃ₗᵢ[ℂ] K))
    (hbdd : BddAbove (Set.range fun i => ‖a i‖)) (ha : ∀ i, a i ≠ 0) (hD : D ≠ 0)
    (hT : ContinuousLinearMap.HasTransverseLowerBound (weightedInduction a D U V hbdd)) :
    (∃ α > 0, ∀ i, α ≤ ‖a i‖) ∧ ContinuousLinearMap.HasTransverseLowerBound D := by
  obtain ⟨c, hc, hb⟩ := hT
  have hsingle : ∀ (i : I) (x : H), x ∈ (LinearMap.ker (D : H →ₗ[ℂ] K))ᗮ →
      c * ‖x‖ ≤ ‖a i‖ * ‖D x‖ := by
    intro i x hx
    have hy : (U i x) ∈ (LinearMap.ker (orbitBlock D U V i : H →ₗ[ℂ] K))ᗮ := by
      rw [mem_ker_orbitBlock_orthogonal_iff]
      simpa using hx
    have hmem : (lp.single 2 i (U i x) : lp (fun _ : I => H) 2)
        ∈ (LinearMap.ker (weightedInduction a D U V hbdd : lp (fun _ : I => H) 2 →ₗ[ℂ]
          lp (fun _ : I => K) 2))ᗮ := by
      rw [ker_weightedInduction a D U V hbdd ha]
      exact mem_ker_orbitInduction_orthogonal_single D U V i _ hy
    have h := hb _ hmem
    have h1 : ‖(lp.single 2 i (U i x) : lp (fun _ : I => H) 2)‖ = ‖x‖ := by
      rw [lp.norm_single (E := fun _ : I => H) (by norm_num) i _, (U i).norm_map]
    have h2 : ‖weightedInduction a D U V hbdd (lp.single 2 i (U i x))‖ = ‖a i‖ * ‖D x‖ := by
      rw [weightedInduction_single a D U V hbdd i (U i x)]
      rw [lp.norm_single (E := fun _ : I => K) (by norm_num) i _]
      rw [weightedBlock, smul_apply, norm_smul, orbitBlock_apply,
        LinearIsometryEquiv.symm_apply_apply, (V i).norm_map]
    rw [h1, h2] at h
    exact h
  obtain ⟨x₀, hx₀mem, hx₀norm, hx₀ne⟩ := exists_unit_mem_ker_orthogonal D hD
  have hDx₀ : 0 < ‖D x₀‖ := norm_pos_iff.mpr hx₀ne
  refine ⟨⟨c / ‖D x₀‖, by positivity, fun i => ?_⟩, ?_⟩
  · have h := hsingle i x₀ hx₀mem
    rw [hx₀norm, mul_one] at h
    rw [div_le_iff₀ hDx₀]
    exact h
  · obtain ⟨i₀⟩ := ‹Nonempty I›
    have hai : 0 < ‖a i₀‖ := norm_pos_iff.mpr (ha i₀)
    refine ⟨c / ‖a i₀‖, by positivity, fun x hx => ?_⟩
    have h := hsingle i₀ x hx
    rw [div_mul_eq_mul_div, div_le_iff₀ hai]
    linarith [h]

/-- **Theorem 2.1, `(WOI.5)`.**  The weighted induction has closed range exactly when the local
operator does and the amplitudes have a uniform nonzero gap. -/
theorem isClosed_range_weightedInduction_iff [DecidableEq I] (a : I → ℂ) (D : H →L[ℂ] K)
    (U : I → (H ≃ₗᵢ[ℂ] H)) (V : I → (K ≃ₗᵢ[ℂ] K))
    (hbdd : BddAbove (Set.range fun i => ‖a i‖)) (ha : ∀ i, a i ≠ 0) (hD : D ≠ 0) :
    IsClosed (Set.range (weightedInduction a D U V hbdd))
      ↔ IsClosed (Set.range D) ∧ ∃ α > 0, ∀ i, α ≤ ‖a i‖ := by
  rw [← ContinuousLinearMap.hasTransverseLowerBound_iff_isClosed_range,
    ← ContinuousLinearMap.hasTransverseLowerBound_iff_isClosed_range]
  constructor
  · intro hT
    obtain ⟨hgap, hD'⟩ := hasTransverseLowerBound_weightedInduction_imp a D U V hbdd ha hD hT
    exact ⟨hD', hgap⟩
  · rintro ⟨⟨c, hc, hb⟩, ⟨α, hα, hamp⟩⟩
    exact ⟨α * c, by positivity,
      le_norm_weightedInduction a D U V hbdd ha hα.le hc.le hamp hb⟩

end Weighted

/-! ## Coordinate maps on the Hilbert sum -/

section Coord

variable {J : Type} [DecidableEq J] {G : J → Type*} [∀ j, NormedAddCommGroup (G j)]
  [∀ j, NormedSpace ℂ (G j)]

/-- Coordinate evaluation on the Hilbert sum. -/
def lpEvalCLM (j : J) : lp G 2 →L[ℂ] G j :=
  LinearMap.mkContinuous
    { toFun := fun x => (x : ∀ j, G j) j
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl } 1
    (fun x => by
      simpa using lp.norm_apply_le_norm (E := G) (p := 2) (by norm_num) x j)

omit [DecidableEq J] in
@[simp] theorem lpEvalCLM_apply (j : J) (x : lp G 2) :
    lpEvalCLM j x = (x : ∀ j, G j) j := rfl

/-- The single-coordinate embedding into the Hilbert sum. -/
def lpSingleCLM (j : J) : G j →L[ℂ] lp G 2 :=
  LinearMap.mkContinuous
    { toFun := fun v => lp.single 2 j v
      map_add' := fun v w => lp.single_add (E := G) 2 j v w
      map_smul' := fun c v => lp.single_smul (E := G) 2 j c v } 1
    (fun v => by
      show ‖(lp.single 2 j v : lp G 2)‖ ≤ 1 * ‖v‖
      rw [lp.norm_single (E := G) (by norm_num)]
      simp)

@[simp] theorem lpSingleCLM_apply (j : J) (v : G j) :
    lpSingleCLM j v = lp.single 2 j v := rfl

end Coord

/-! ## Truncation of the amplitudes -/

section Truncation

variable {I : Type} [Nonempty I] [DecidableEq I] {H K : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

/-- The amplitudes truncated to a finite set. -/
def truncAmp (F : Finset I) (a : I → ℂ) : I → ℂ := fun i => if i ∈ F then a i else 0

/-- The amplitudes outside a finite set. -/
def tailAmp (F : Finset I) (a : I → ℂ) : I → ℂ := fun i => if i ∈ F then 0 else a i

omit [Nonempty I] in
theorem norm_truncAmp_le (F : Finset I) (a : I → ℂ) (i : I) : ‖truncAmp F a i‖ ≤ ‖a i‖ := by
  rw [truncAmp]
  by_cases h : i ∈ F <;> simp [h]

omit [Nonempty I] in
theorem norm_tailAmp_le (F : Finset I) (a : I → ℂ) (i : I) : ‖tailAmp F a i‖ ≤ ‖a i‖ := by
  rw [tailAmp]
  by_cases h : i ∈ F <;> simp [h]

omit [Nonempty I] in
theorem bddAbove_truncAmp {a : I → ℂ} (hbdd : BddAbove (Set.range fun i => ‖a i‖))
    (F : Finset I) : BddAbove (Set.range fun i => ‖truncAmp F a i‖) := by
  obtain ⟨M, hM⟩ := hbdd
  refine ⟨M, ?_⟩
  rintro _ ⟨i, rfl⟩
  exact le_trans (norm_truncAmp_le F a i) (hM ⟨i, rfl⟩)

omit [Nonempty I] in
theorem bddAbove_tailAmp {a : I → ℂ} (hbdd : BddAbove (Set.range fun i => ‖a i‖))
    (F : Finset I) : BddAbove (Set.range fun i => ‖tailAmp F a i‖) := by
  obtain ⟨M, hM⟩ := hbdd
  refine ⟨M, ?_⟩
  rintro _ ⟨i, rfl⟩
  exact le_trans (norm_tailAmp_le F a i) (hM ⟨i, rfl⟩)

omit [CompleteSpace H] [CompleteSpace K] in
/-- Subtracting the finite truncation leaves the tail. -/
theorem weightedInduction_sub_trunc (a : I → ℂ) (D : H →L[ℂ] K) (U : I → (H ≃ₗᵢ[ℂ] H))
    (V : I → (K ≃ₗᵢ[ℂ] K)) (hbdd : BddAbove (Set.range fun i => ‖a i‖)) (F : Finset I) :
    weightedInduction a D U V hbdd
        - weightedInduction (truncAmp F a) D U V (bddAbove_truncAmp hbdd F)
      = weightedInduction (tailAmp F a) D U V (bddAbove_tailAmp hbdd F) := by
  refine ContinuousLinearMap.ext fun ξ => ?_
  have hap : (weightedInduction a D U V hbdd
      - weightedInduction (truncAmp F a) D U V (bddAbove_truncAmp hbdd F)) ξ
      = weightedInduction a D U V hbdd ξ
        - weightedInduction (truncAmp F a) D U V (bddAbove_truncAmp hbdd F) ξ :=
    sub_apply _ _ ξ
  rw [hap]
  ext i
  rw [lp.coeFn_sub]
  show a i • V i (D ((U i).symm ((ξ : ∀ _ : I, H) i)))
      - truncAmp F a i • V i (D ((U i).symm ((ξ : ∀ _ : I, H) i)))
    = tailAmp F a i • V i (D ((U i).symm ((ξ : ∀ _ : I, H) i)))
  rw [tailAmp, truncAmp]
  by_cases h : i ∈ F <;> simp [h]

omit [DecidableEq I] [CompleteSpace H] [CompleteSpace K] in
/-- The weighted induction is additive in the amplitude family. -/
theorem weightedInduction_add {a b c : I → ℂ} (D : H →L[ℂ] K) (U : I → (H ≃ₗᵢ[ℂ] H))
    (V : I → (K ≃ₗᵢ[ℂ] K)) (hc : ∀ i, c i = a i + b i)
    (ha : BddAbove (Set.range fun i => ‖a i‖)) (hb : BddAbove (Set.range fun i => ‖b i‖))
    (hcb : BddAbove (Set.range fun i => ‖c i‖)) :
    weightedInduction c D U V hcb
      = weightedInduction a D U V ha + weightedInduction b D U V hb := by
  refine ContinuousLinearMap.ext fun ξ => ?_
  have hap : (weightedInduction a D U V ha + weightedInduction b D U V hb) ξ
      = weightedInduction a D U V ha ξ + weightedInduction b D U V hb ξ := add_apply _ _ ξ
  rw [hap]
  ext i
  rw [lp.coeFn_add]
  show c i • V i (D ((U i).symm ((ξ : ∀ _ : I, H) i)))
    = a i • V i (D ((U i).symm ((ξ : ∀ _ : I, H) i)))
      + b i • V i (D ((U i).symm ((ξ : ∀ _ : I, H) i)))
  rw [hc i, add_smul]

omit [DecidableEq I] [CompleteSpace H] [CompleteSpace K] in
theorem weightedInduction_zero {a : I → ℂ} (D : H →L[ℂ] K) (U : I → (H ≃ₗᵢ[ℂ] H))
    (V : I → (K ≃ₗᵢ[ℂ] K)) (ha0 : ∀ i, a i = 0)
    (ha : BddAbove (Set.range fun i => ‖a i‖)) :
    weightedInduction a D U V ha = 0 := by
  refine ContinuousLinearMap.ext fun ξ => ?_
  ext i
  simp [weightedInduction_apply, ha0 i]

omit [CompleteSpace H] [CompleteSpace K] in
theorem weightedInduction_singleIndex (a : I → ℂ) (D : H →L[ℂ] K) (U : I → (H ≃ₗᵢ[ℂ] H))
    (V : I → (K ≃ₗᵢ[ℂ] K)) (i : I)
    (hs : BddAbove (Set.range fun j => ‖(fun j => if j = i then a i else 0) j‖)) :
    weightedInduction (fun j => if j = i then a i else 0) D U V hs
      = (lpSingleCLM (G := fun _ : I => K) i) ∘L
        ((weightedBlock a D U V i) ∘L (lpEvalCLM (G := fun _ : I => H) i)) := by
  refine ContinuousLinearMap.ext fun ξ => ?_
  ext j
  show (if j = i then a i else 0) • V j (D ((U j).symm ((ξ : ∀ _ : I, H) j)))
    = ((lp.single 2 i (weightedBlock a D U V i ((ξ : ∀ _ : I, H) i)) :
        lp (fun _ : I => K) 2) : ∀ _ : I, K) j
  by_cases hj : j = i
  · subst hj
    rw [if_pos rfl, lp.single_apply_self (E := fun _ : I => K)]
    rfl
  · rw [if_neg hj, lp.single_apply_ne (E := fun _ : I => K) 2 i _ hj, zero_smul]

omit [Nonempty I] [CompleteSpace H] [CompleteSpace K] in
theorem bddAbove_singleIndex (a : I → ℂ) (i : I) :
    BddAbove (Set.range fun j => ‖(fun j => if j = i then a i else 0) j‖) := by
  refine ⟨‖a i‖, ?_⟩
  rintro _ ⟨j, rfl⟩
  by_cases hj : j = i <;> simp [hj]

omit [CompleteSpace H] [CompleteSpace K] in
/-- **Theorem 3.1.**  A finite truncation of the amplitudes gives a compact operator whenever the
local block is compact. -/
theorem isCompactOperator_weightedInduction_trunc (a : I → ℂ) (D : H →L[ℂ] K)
    (U : I → (H ≃ₗᵢ[ℂ] H)) (V : I → (K ≃ₗᵢ[ℂ] K))
    (hbdd : BddAbove (Set.range fun i => ‖a i‖)) (hD : IsCompactOperator D) (F : Finset I) :
    IsCompactOperator
      (weightedInduction (truncAmp F a) D U V (bddAbove_truncAmp hbdd F)) := by
  classical
  induction F using Finset.induction_on with
  | empty =>
      rw [weightedInduction_zero D U V (fun i => by simp [truncAmp])]
      exact isCompactOperator_zero
  | insert i F hiF ih =>
      have hsplit : ∀ j, truncAmp (insert i F) a j
          = (fun j => if j = i then a i else 0) j + truncAmp F a j := by
        intro j
        by_cases hj : j = i
        · subst hj
          simp [truncAmp, hiF]
        · simp [truncAmp, hj, Finset.mem_insert]
      rw [weightedInduction_add D U V hsplit (bddAbove_singleIndex a i)
        (bddAbove_truncAmp hbdd F) (bddAbove_truncAmp hbdd (insert i F))]
      refine IsCompactOperator.add ?_ ih
      have hblk : IsCompactOperator (weightedBlock a D U V i) := by
        have h1 : IsCompactOperator (orbitBlock D U V i) := by
          rw [orbitBlock]
          exact (hD.comp_clm ((U i).symm.toLinearIsometry.toContinuousLinearMap)).clm_comp
            ((V i).toLinearIsometry.toContinuousLinearMap)
        exact h1.smul (a i)
      rw [weightedInduction_singleIndex a D U V i (bddAbove_singleIndex a i)]
      exact (hblk.comp_clm (lpEvalCLM (G := fun _ : I => H) i)).clm_comp
        (lpSingleCLM (G := fun _ : I => K) i)

end Truncation

/-! ## The tail supremum of the amplitudes -/

section TailSup

variable {I : Type} [Nonempty I] [DecidableEq I]

/-- `(WOI.7)`  The tail supremum of the amplitudes: the infimum, over finite sets `F`, of the
supremum of `|a i|` outside `F`. -/
def tailSup (a : I → ℂ) : ℝ := ⨅ F : Finset I, ampSup (tailAmp F a)

theorem bddBelow_tailAmp_range {a : I → ℂ} (hbdd : BddAbove (Set.range fun i => ‖a i‖)) :
    BddBelow (Set.range fun F : Finset I => ampSup (tailAmp F a)) := by
  refine ⟨0, ?_⟩
  rintro _ ⟨F, rfl⟩
  exact ampSup_nonneg (bddAbove_tailAmp hbdd F)

theorem tailSup_le_ampSup_tailAmp {a : I → ℂ} (hbdd : BddAbove (Set.range fun i => ‖a i‖))
    (F : Finset I) : tailSup a ≤ ampSup (tailAmp F a) :=
  ciInf_le (bddBelow_tailAmp_range hbdd) F

theorem tailSup_nonneg {a : I → ℂ} (hbdd : BddAbove (Set.range fun i => ‖a i‖)) :
    0 ≤ tailSup a :=
  le_ciInf fun F => ampSup_nonneg (bddAbove_tailAmp hbdd F)

/-- Outside every finite set the amplitudes come arbitrarily close to the tail supremum. -/
theorem exists_notMem_tailSup_sub_lt {a : I → ℂ} (hbdd : BddAbove (Set.range fun i => ‖a i‖))
    (F : Finset I) {ε : ℝ} (hε : 0 < ε) (hpos : ε ≤ tailSup a) :
    ∃ i, i ∉ F ∧ tailSup a - ε < ‖a i‖ := by
  by_contra hcon
  push Not at hcon
  have hle : ∀ i, ‖tailAmp F a i‖ ≤ tailSup a - ε := by
    intro i
    by_cases hi : i ∈ F
    · rw [tailAmp, if_pos hi, norm_zero]
      linarith
    · rw [tailAmp, if_neg hi]
      exact hcon i hi
  have h1 : ampSup (tailAmp F a) ≤ tailSup a - ε := ampSup_le hle
  have h2 := tailSup_le_ampSup_tailAmp hbdd F
  linarith

/-- The tail supremum vanishes exactly when the amplitudes vanish at infinity, i.e. `a ∈ c₀(I)`. -/
theorem tailSup_eq_zero_iff {a : I → ℂ} (hbdd : BddAbove (Set.range fun i => ‖a i‖)) :
    tailSup a = 0 ↔ ∀ ε : ℝ, 0 < ε → {i : I | ε ≤ ‖a i‖}.Finite := by
  classical
  constructor
  · intro h0 ε hε
    have hlt : tailSup a < ε := by rw [h0]; exact hε
    obtain ⟨F, hrlt⟩ :=
      exists_lt_of_ciInf_lt (f := fun F : Finset I => ampSup (tailAmp F a)) hlt
    refine Set.Finite.subset F.finite_toSet fun i hi => ?_
    by_contra hiF
    have hiF' : i ∉ F := by simpa using hiF
    have : ‖a i‖ ≤ ampSup (tailAmp F a) := by
      have h1 : ‖tailAmp F a i‖ = ‖a i‖ := by rw [tailAmp, if_neg hiF']
      rw [← h1]
      exact le_ampSup (bddAbove_tailAmp hbdd F) i
    exact absurd hi (not_le.mpr (lt_of_le_of_lt this hrlt))
  · intro hfin
    refine le_antisymm ?_ (tailSup_nonneg hbdd)
    refine le_of_forall_pos_le_add fun ε hεpos => ?_
    rw [zero_add]
    set F : Finset I := (hfin ε hεpos).toFinset with hF
    have hle : ∀ i, ‖tailAmp F a i‖ ≤ ε := by
      intro i
      by_cases hi : i ∈ F
      · rw [tailAmp, if_pos hi, norm_zero]
        exact hεpos.le
      · rw [tailAmp, if_neg hi]
        have : i ∉ {j : I | ε ≤ ‖a j‖} := by simpa [hF, Set.Finite.mem_toFinset] using hi
        exact (not_le.mp this).le
    exact le_trans (tailSup_le_ampSup_tailAmp hbdd F) (ampSup_le hle)

end TailSup

/-! ## The essential norm of the weighted induction -/

section EssentialNorm

variable {I : Type} [Nonempty I] [DecidableEq I] {H K : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

/-- The escape vector at one orbit point. -/
def escapeAt (U : I → (H ≃ₗᵢ[ℂ] H)) (x : H) (i : I) : lp (fun _ : I => H) 2 :=
  lp.single 2 i (U i x)

omit [CompleteSpace H] in
omit [Nonempty I] in
theorem norm_escapeAt (U : I → (H ≃ₗᵢ[ℂ] H)) (x : H) (i : I) : ‖escapeAt U x i‖ = ‖x‖ := by
  rw [escapeAt, lp.norm_single (E := fun _ : I => H) (by norm_num), (U i).norm_map]

omit [CompleteSpace H] [CompleteSpace K] in
theorem norm_weightedInduction_escapeAt (a : I → ℂ) (D : H →L[ℂ] K) (U : I → (H ≃ₗᵢ[ℂ] H))
    (V : I → (K ≃ₗᵢ[ℂ] K)) (hbdd : BddAbove (Set.range fun i => ‖a i‖)) (x : H) (i : I) :
    ‖weightedInduction a D U V hbdd (escapeAt U x i)‖ = ‖a i‖ * ‖D x‖ := by
  rw [escapeAt, weightedInduction_single a D U V hbdd i (U i x),
    lp.norm_single (E := fun _ : I => K) (by norm_num), weightedBlock, smul_apply, norm_smul,
    orbitBlock_apply, LinearIsometryEquiv.symm_apply_apply, (V i).norm_map]

omit [CompleteSpace H] in
omit [Nonempty I] in
theorem weaklyNull_single_along {f : ℕ → I} (hf : Function.Injective f) (v : ℕ → H)
    (hv : ∀ n, ‖v n‖ ≤ 1) (z : lp (fun _ : I => H) 2) :
    Filter.Tendsto
      (fun n => ⟪z, (lp.single 2 (f n) (v n) : lp (fun _ : I => H) 2)⟫_ℂ)
      Filter.atTop (nhds 0) := by
  have hsum : Summable fun n : ℕ => ‖(z : ∀ _ : I, H) (f n)‖ ^ 2 :=
    (lp_summable_norm_sq z).comp_injective hf
  have hz2 : Filter.Tendsto (fun n : ℕ => ‖(z : ∀ _ : I, H) (f n)‖ ^ 2)
      Filter.atTop (nhds 0) := hsum.tendsto_atTop_zero
  have hz : Filter.Tendsto (fun n : ℕ => ‖(z : ∀ _ : I, H) (f n)‖)
      Filter.atTop (nhds 0) := by
    have hsqrt := (Real.continuous_sqrt.tendsto 0).comp hz2
    simpa [Function.comp_def, Real.sqrt_sq (norm_nonneg _)] using hsqrt
  refine squeeze_zero_norm (fun n => ?_) (by simpa using hz)
  rw [lp.inner_single_right (𝕜 := ℂ) (G := fun _ : I => H)]
  refine le_trans (norm_inner_le_norm _ _) ?_
  calc ‖(z : ∀ _ : I, H) (f n)‖ * ‖v n‖ ≤ ‖(z : ∀ _ : I, H) (f n)‖ * 1 :=
        mul_le_mul_of_nonneg_left (hv n) (norm_nonneg _)
    _ = ‖(z : ∀ _ : I, H) (f n)‖ := mul_one _

omit [Nonempty I] in
/-- A compact operator is uniformly small on all but finitely many escape vectors. -/
theorem finite_escapeAt_large (U : I → (H ≃ₗᵢ[ℂ] H)) {x : H} (hx : ‖x‖ = 1)
    (C : lp (fun _ : I => H) 2 →L[ℂ] lp (fun _ : I => K) 2) (hC : IsCompactOperator C)
    {ε : ℝ} (hε : 0 < ε) :
    {i : I | ε ≤ ‖C (escapeAt U x i)‖}.Finite := by
  by_contra hinf
  rw [Set.not_finite] at hinf
  set e : ℕ ↪ {i : I // i ∈ {i : I | ε ≤ ‖C (escapeAt U x i)‖}} := hinf.natEmbedding with he
  set f : ℕ → I := fun n => ((e n : {i : I // i ∈ _}) : I) with hf
  have hfinj : Function.Injective f := fun m n h =>
    e.injective (Subtype.ext h)
  have hbound : ∀ n, ‖escapeAt U x (f n)‖ ≤ 1 := fun n => by
    rw [norm_escapeAt, hx]
  have hweak : ∀ z : lp (fun _ : I => H) 2,
      Filter.Tendsto (fun n => ⟪z, escapeAt U x (f n)⟫_ℂ) Filter.atTop (nhds 0) := by
    intro z
    exact weaklyNull_single_along hfinj (fun n => U (f n) x)
      (fun n => by rw [(U (f n)).norm_map, hx]) z
  have hCn : Filter.Tendsto (fun n => C (escapeAt U x (f n))) Filter.atTop (nhds 0) :=
    tendsto_norm_compact_of_weaklyNull C hC _ hbound hweak
  have hnorm : Filter.Tendsto (fun n => ‖C (escapeAt U x (f n))‖) Filter.atTop (nhds 0) := by
    simpa using hCn.norm
  have hge : ∀ n, ε ≤ ‖C (escapeAt U x (f n))‖ := fun n => (e n).2
  have hlim : ε ≤ 0 := ge_of_tendsto hnorm (Filter.Eventually.of_forall hge)
  linarith

/-- `(WOI.7)`, lower bound at one unit vector. -/
theorem le_norm_sub_of_isCompactOperator (a : I → ℂ) (D : H →L[ℂ] K) (U : I → (H ≃ₗᵢ[ℂ] H))
    (V : I → (K ≃ₗᵢ[ℂ] K)) (hbdd : BddAbove (Set.range fun i => ‖a i‖)) {x : H} (hx : ‖x‖ = 1)
    (C : lp (fun _ : I => H) 2 →L[ℂ] lp (fun _ : I => K) 2) (hC : IsCompactOperator C) :
    tailSup a * ‖D x‖ ≤ ‖weightedInduction a D U V hbdd - C‖ := by
  classical
  rcases eq_or_lt_of_le (tailSup_nonneg hbdd) with h0 | hpos
  · rw [← h0, zero_mul]
    exact norm_nonneg (weightedInduction a D U V hbdd - C)
  have key : ∀ ε : ℝ, 0 < ε → ε ≤ tailSup a →
      tailSup a * ‖D x‖ - ε * (‖D x‖ + 1) ≤ ‖weightedInduction a D U V hbdd - C‖ := by
    intro ε hε hle
    have hSfin : {i : I | ε ≤ ‖C (escapeAt U x i)‖}.Finite :=
      finite_escapeAt_large U hx C hC hε
    obtain ⟨i, hiF, hai⟩ := exists_notMem_tailSup_sub_lt hbdd hSfin.toFinset hε hle
    have hiS : i ∉ {i : I | ε ≤ ‖C (escapeAt U x i)‖} := by
      simpa [Set.Finite.mem_toFinset] using hiF
    have hCi : ‖C (escapeAt U x i)‖ < ε := not_le.mp hiS
    have h1 : ‖(weightedInduction a D U V hbdd - C) (escapeAt U x i)‖
        ≤ ‖weightedInduction a D U V hbdd - C‖ * ‖escapeAt U x i‖ :=
      ContinuousLinearMap.le_opNorm _ _
    rw [norm_escapeAt, hx, mul_one] at h1
    have h2 : ‖weightedInduction a D U V hbdd (escapeAt U x i)‖ - ‖C (escapeAt U x i)‖
        ≤ ‖(weightedInduction a D U V hbdd - C) (escapeAt U x i)‖ := by
      simpa using norm_sub_norm_le (weightedInduction a D U V hbdd (escapeAt U x i))
        (C (escapeAt U x i))
    rw [norm_weightedInduction_escapeAt] at h2
    nlinarith [h1, h2, hai, hCi, norm_nonneg (D x)]
  refine le_of_forall_pos_le_add fun δ hδ => ?_
  set ε : ℝ := min (tailSup a) (δ / (‖D x‖ + 1)) with hεdef
  have hDx1 : (0 : ℝ) < ‖D x‖ + 1 := by positivity
  have hεpos : 0 < ε := lt_min hpos (by positivity)
  have hεle : ε ≤ tailSup a := min_le_left _ _
  have hbound : ε * (‖D x‖ + 1) ≤ δ := by
    calc ε * (‖D x‖ + 1) ≤ (δ / (‖D x‖ + 1)) * (‖D x‖ + 1) :=
          mul_le_mul_of_nonneg_right (min_le_right _ _) hDx1.le
      _ = δ := by field_simp
  linarith [key ε hεpos hεle]

/-- `(WOI.7)`, lower bound. -/
theorem le_rectEssentialNorm_weightedInduction (a : I → ℂ) (D : H →L[ℂ] K)
    (U : I → (H ≃ₗᵢ[ℂ] H)) (V : I → (K ≃ₗᵢ[ℂ] K))
    (hbdd : BddAbove (Set.range fun i => ‖a i‖)) :
    tailSup a * ‖D‖ ≤ rectEssentialNorm (weightedInduction a D U V hbdd) := by
  refine le_rectEssentialNorm _ _ fun C hC => ?_
  have h : ‖(((tailSup a : ℝ) : ℂ)) • D‖ ≤ ‖weightedInduction a D U V hbdd - C‖ := by
    refine ContinuousLinearMap.opNorm_le_of_unit_norm
      (norm_nonneg (weightedInduction a D U V hbdd - C)) fun x hx => ?_
    rw [smul_apply, norm_smul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (tailSup_nonneg hbdd)]
    exact le_norm_sub_of_isCompactOperator a D U V hbdd hx C hC
  rwa [norm_smul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (tailSup_nonneg hbdd)] at h

omit [CompleteSpace H] [CompleteSpace K] in
/-- `(WOI.7)`, upper bound. -/
theorem rectEssentialNorm_weightedInduction_le (a : I → ℂ) (D : H →L[ℂ] K)
    (U : I → (H ≃ₗᵢ[ℂ] H)) (V : I → (K ≃ₗᵢ[ℂ] K))
    (hbdd : BddAbove (Set.range fun i => ‖a i‖)) (hD : IsCompactOperator D) :
    rectEssentialNorm (weightedInduction a D U V hbdd) ≤ tailSup a * ‖D‖ := by
  have hF : ∀ F : Finset I, rectEssentialNorm (weightedInduction a D U V hbdd)
      ≤ ampSup (tailAmp F a) * ‖D‖ := by
    intro F
    have hcomp := isCompactOperator_weightedInduction_trunc a D U V hbdd hD F
    have h := rectEssentialNorm_le (weightedInduction a D U V hbdd) _ hcomp
    rw [weightedInduction_sub_trunc a D U V hbdd F,
      norm_weightedInduction (tailAmp F a) D U V (bddAbove_tailAmp hbdd F)] at h
    exact h
  rcases eq_or_lt_of_le (norm_nonneg D) with hD0 | hDpos
  · have hDz : D = 0 := by
      rw [← norm_eq_zero]
      exact hD0.symm
    have h := hF ∅
    rw [hDz] at h ⊢
    simpa using h
  · rw [← div_le_iff₀ hDpos, tailSup]
    refine le_ciInf fun F => ?_
    rw [div_le_iff₀ hDpos]
    exact hF F

/-- **Theorem 3.1, `(WOI.7)`.**  The essential norm of the weighted induction is the tail supremum
of the amplitudes times the local norm. -/
theorem rectEssentialNorm_weightedInduction (a : I → ℂ) (D : H →L[ℂ] K)
    (U : I → (H ≃ₗᵢ[ℂ] H)) (V : I → (K ≃ₗᵢ[ℂ] K))
    (hbdd : BddAbove (Set.range fun i => ‖a i‖)) (hD : IsCompactOperator D) :
    rectEssentialNorm (weightedInduction a D U V hbdd) = tailSup a * ‖D‖ :=
  le_antisymm (rectEssentialNorm_weightedInduction_le a D U V hbdd hD)
    (le_rectEssentialNorm_weightedInduction a D U V hbdd)

/-- **Theorem 3.1, `(WOI.6)`.**  For a nonzero compact local block, the weighted induction is
compact exactly when the amplitudes vanish at infinity. -/
theorem isCompactOperator_weightedInduction_iff (a : I → ℂ) (D : H →L[ℂ] K)
    (U : I → (H ≃ₗᵢ[ℂ] H)) (V : I → (K ≃ₗᵢ[ℂ] K))
    (hbdd : BddAbove (Set.range fun i => ‖a i‖)) (hD : IsCompactOperator D) (hDne : D ≠ 0) :
    IsCompactOperator (weightedInduction a D U V hbdd) ↔ tailSup a = 0 := by
  have hDpos : 0 < ‖D‖ := norm_pos_iff.mpr hDne
  constructor
  · intro hc
    have h0 := rectEssentialNorm_eq_zero_of_isCompactOperator hc
    rw [rectEssentialNorm_weightedInduction a D U V hbdd hD] at h0
    rcases mul_eq_zero.mp h0 with h | h
    · exact h
    · exact absurd h hDpos.ne'
  · intro h0
    refine isCompactOperator_of_rectEssentialNorm_eq_zero ?_
    rw [rectEssentialNorm_weightedInduction a D U V hbdd hD, h0, zero_mul]

end EssentialNorm

end

end GaloisForLFunctions.HTGeometry
