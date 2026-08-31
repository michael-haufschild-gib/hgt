import GaloisForLFunctions.HTGeometry.RectangularVectorDiagonal
import GaloisForLFunctions.HTGeometry.ObserverHorizonStability

/-!
# Orbit induction, essentialization and infinite multiplicity

A bounded operator `D : H → K` transported by two families of unitaries over an index set `I`
assembles into the **orbit induction** `Ind_I(D)` on the Hilbert direct sums.  This module proves
its exact invariants:

* `norm_orbitInduction` `(OI.5)` — the operator norm is unchanged;
* `orbitInduction_eq_zero_iff` `(OI.6)` — the kernel is the blockwise kernel;
* `hasTransverseLowerBound_orbitInduction_iff`, `isClosed_range_orbitInduction_iff` `(OI.7)` — the
  transverse lower bound and closed range are unchanged;
* `orbitInduction_injective_iff`, `orbitInduction_surjective_iff`, `orbitInduction_bijective_iff`
  and `exists_lower_bound_orbitInduction_iff` — Corollary 2.2;
* `rectEssentialNorm_orbitInduction` `(OI.9)` and `isCompactOperator_orbitInduction_iff` `(OI.8)` —
  over an infinite orbit the local norm becomes the global **essential** norm, so a nonzero compact
  local defect becomes a noncompact global one;
* `not_finiteDimensional_ker_orbitInduction`, `not_finiteDimensional_range_orbitInduction` —
  Corollary 4.1, infinite global multiplicity;
* `adjoint_orbitInduction`, `gram_orbitInduction` `(OI.G1)` and
  `rectEssentialNorm_gram_orbitInduction` `(OI.G3)` — Theorem 4.2: the positive Gram operator
  forgets the output unitaries but not the essential class.

The essential norm of a possibly rectangular operator, `rectEssentialNorm`, is developed here; the
corpus `RHTower.essentialNorm` treats endomorphisms only.
-/

namespace GaloisForLFunctions.HTGeometry

open Filter RHTower
open scoped ENNReal Topology InnerProductSpace

noncomputable section

/-! ## The essential norm of a rectangular operator -/

section RectEssential

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F]

/-- The essential norm of a bounded operator between two possibly different spaces: its distance
to the compact operators. -/
def rectEssentialNorm (T : E →L[ℂ] F) : ℝ :=
  sInf {r : ℝ | ∃ C : E →L[ℂ] F, IsCompactOperator C ∧ ‖T - C‖ = r}

theorem rectEssentialNorm_set_nonempty (T : E →L[ℂ] F) :
    {r : ℝ | ∃ C : E →L[ℂ] F, IsCompactOperator C ∧ ‖T - C‖ = r}.Nonempty :=
  ⟨‖T‖, 0, isCompactOperator_zero, by rw [sub_zero]⟩

theorem rectEssentialNorm_set_bddBelow (T : E →L[ℂ] F) :
    BddBelow {r : ℝ | ∃ C : E →L[ℂ] F, IsCompactOperator C ∧ ‖T - C‖ = r} := by
  refine ⟨0, ?_⟩
  rintro r ⟨C, _, rfl⟩
  positivity

theorem rectEssentialNorm_le (T C : E →L[ℂ] F) (hC : IsCompactOperator C) :
    rectEssentialNorm T ≤ ‖T - C‖ :=
  csInf_le (rectEssentialNorm_set_bddBelow T) ⟨C, hC, rfl⟩

theorem rectEssentialNorm_le_norm (T : E →L[ℂ] F) : rectEssentialNorm T ≤ ‖T‖ := by
  simpa using rectEssentialNorm_le T 0 isCompactOperator_zero

theorem le_rectEssentialNorm (T : E →L[ℂ] F) (c : ℝ)
    (h : ∀ C : E →L[ℂ] F, IsCompactOperator C → c ≤ ‖T - C‖) :
    c ≤ rectEssentialNorm T :=
  le_csInf (rectEssentialNorm_set_nonempty T) (by rintro r ⟨C, hC, rfl⟩; exact h C hC)

theorem rectEssentialNorm_nonneg (T : E →L[ℂ] F) : 0 ≤ rectEssentialNorm T :=
  le_rectEssentialNorm T 0 fun _ _ => norm_nonneg _

theorem rectEssentialNorm_eq_zero_of_isCompactOperator {T : E →L[ℂ] F}
    (hT : IsCompactOperator T) : rectEssentialNorm T = 0 :=
  le_antisymm (by simpa using rectEssentialNorm_le T T hT) (rectEssentialNorm_nonneg T)

theorem exists_isCompactOperator_norm_sub_lt {T : E →L[ℂ] F} {ε : ℝ}
    (hε : rectEssentialNorm T < ε) :
    ∃ C : E →L[ℂ] F, IsCompactOperator C ∧ ‖T - C‖ < ε := by
  obtain ⟨r, hr, hlt⟩ := exists_lt_of_csInf_lt (rectEssentialNorm_set_nonempty T) hε
  obtain ⟨C, hC, rfl⟩ := hr
  exact ⟨C, hC, hlt⟩

/-- Compact operators are norm closed, so a vanishing essential norm is compactness. -/
theorem isCompactOperator_of_rectEssentialNorm_eq_zero [CompleteSpace F] {T : E →L[ℂ] F}
    (h : rectEssentialNorm T = 0) : IsCompactOperator T := by
  have hchoice : ∀ n : ℕ, ∃ C : E →L[ℂ] F, IsCompactOperator C ∧ ‖T - C‖ < 1 / (n + 1 : ℝ) := by
    intro n
    refine exists_isCompactOperator_norm_sub_lt ?_
    rw [h]
    positivity
  choose C hCcomp hClt using hchoice
  refine isCompactOperator_of_tendsto (ι := ℕ) (l := Filter.atTop) (F := C) ?_
    (Filter.Eventually.of_forall hCcomp)
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero (fun n => norm_nonneg _) (fun n => ?_)
    tendsto_one_div_add_atTop_nhds_zero_nat
  rw [← norm_neg]
  simpa using (hClt n).le


end RectEssential

/-! ## Orbit induction -/

section OrbitInduction

variable {I : Type} {H K : Type*}
  [NormedAddCommGroup H] [NormedSpace ℂ H]
  [NormedAddCommGroup K] [NormedSpace ℂ K]

/-- `(OI.3)`  The block transported to the orbit point `i`. -/
def orbitBlock (D : H →L[ℂ] K) (U : I → (H ≃ₗᵢ[ℂ] H)) (V : I → (K ≃ₗᵢ[ℂ] K)) (i : I) :
    H →L[ℂ] K :=
  (V i).toLinearIsometry.toContinuousLinearMap ∘L D ∘L
    (U i).symm.toLinearIsometry.toContinuousLinearMap

@[simp] theorem orbitBlock_apply (D : H →L[ℂ] K) (U : I → (H ≃ₗᵢ[ℂ] H))
    (V : I → (K ≃ₗᵢ[ℂ] K)) (i : I) (x : H) :
    orbitBlock D U V i x = V i (D ((U i).symm x)) := rfl

theorem norm_orbitBlock (D : H →L[ℂ] K) (U : I → (H ≃ₗᵢ[ℂ] H)) (V : I → (K ≃ₗᵢ[ℂ] K))
    (i : I) : ‖orbitBlock D U V i‖ = ‖D‖ := by
  refine le_antisymm (ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg D) fun x => ?_)
    (ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun x => ?_)
  · rw [orbitBlock_apply, (V i).norm_map]
    calc ‖D ((U i).symm x)‖ ≤ ‖D‖ * ‖(U i).symm x‖ := D.le_opNorm _
      _ = ‖D‖ * ‖x‖ := by rw [(U i).symm.norm_map]
  · have h := (orbitBlock D U V i).le_opNorm (U i x)
    rw [orbitBlock_apply] at h
    simp only [LinearIsometryEquiv.symm_apply_apply, (V i).norm_map] at h
    rw [(U i).norm_map] at h
    exact h

/-- `(OI.4)`  The orbit-induced operator on the Hilbert direct sum. -/
def orbitInduction (D : H →L[ℂ] K) (U : I → (H ≃ₗᵢ[ℂ] H)) (V : I → (K ≃ₗᵢ[ℂ] K)) :
    lp (fun _ : I => H) 2 →L[ℂ] lp (fun _ : I => K) 2 :=
  rectangularBlockOperator (E := fun _ : I => H) (F := fun _ : I => K)
    (fun i => orbitBlock D U V i) (norm_nonneg D)
    (fun i => (norm_orbitBlock D U V i).le)

@[simp] theorem orbitInduction_apply (D : H →L[ℂ] K) (U : I → (H ≃ₗᵢ[ℂ] H))
    (V : I → (K ≃ₗᵢ[ℂ] K)) (x : lp (fun _ : I => H) 2) (i : I) :
    orbitInduction D U V x i = V i (D ((U i).symm (x i))) := rfl

theorem norm_orbitInduction_le (D : H →L[ℂ] K) (U : I → (H ≃ₗᵢ[ℂ] H))
    (V : I → (K ≃ₗᵢ[ℂ] K)) : ‖orbitInduction D U V‖ ≤ ‖D‖ :=
  LinearMap.mkContinuous_norm_le _ (norm_nonneg D)
    (rectangularBlockOperatorLinear_norm_le _ _ _)

theorem orbitInduction_single [DecidableEq I] (D : H →L[ℂ] K) (U : I → (H ≃ₗᵢ[ℂ] H))
    (V : I → (K ≃ₗᵢ[ℂ] K)) (i : I) (x : H) :
    orbitInduction D U V (lp.single 2 i x) = lp.single 2 i (orbitBlock D U V i x) :=
  rectangularBlockOperator_single (E := fun _ : I => H) (F := fun _ : I => K)
    (fun i => orbitBlock D U V i) (norm_nonneg D)
    (fun i => (norm_orbitBlock D U V i).le) i x

/-- `(OI.5)`  Orbit induction preserves the operator norm exactly. -/
theorem norm_orbitInduction [Nonempty I] (D : H →L[ℂ] K) (U : I → (H ≃ₗᵢ[ℂ] H))
    (V : I → (K ≃ₗᵢ[ℂ] K)) : ‖orbitInduction D U V‖ = ‖D‖ := by
  classical
  refine le_antisymm (norm_orbitInduction_le D U V) ?_
  obtain ⟨i⟩ := ‹Nonempty I›
  rw [← norm_orbitBlock D U V i]
  refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg (orbitInduction D U V)) fun x => ?_
  have h := (orbitInduction D U V).le_opNorm (lp.single 2 i x)
  rw [orbitInduction_single D U V i x] at h
  have h1 : ‖(lp.single 2 i (orbitBlock D U V i x) : lp (fun _ : I => K) 2)‖
      = ‖orbitBlock D U V i x‖ :=
    lp.norm_single (E := fun _ : I => K) (by norm_num) i _
  have h2 : ‖(lp.single 2 i x : lp (fun _ : I => H) 2)‖ = ‖x‖ :=
    lp.norm_single (E := fun _ : I => H) (by norm_num) i x
  rw [h1, h2] at h
  exact h

/-- `(OI.6)`  The kernel of the induced operator is the blockwise kernel. -/
theorem orbitInduction_eq_zero_iff (D : H →L[ℂ] K) (U : I → (H ≃ₗᵢ[ℂ] H))
    (V : I → (K ≃ₗᵢ[ℂ] K)) (x : lp (fun _ : I => H) 2) :
    orbitInduction D U V x = 0 ↔ ∀ i, D ((U i).symm (x i)) = 0 := by
  constructor
  · intro h i
    have := congrArg (fun y : lp (fun _ : I => K) 2 => (y : ∀ _ : I, K) i) h
    simp only [orbitInduction_apply, lp.coeFn_zero, Pi.zero_apply] at this
    have h2 : V i (D ((U i).symm (x i))) = V i 0 := by rw [this, map_zero]
    exact (V i).injective h2
  · intro h
    ext i
    simp [orbitInduction_apply, h i]

end OrbitInduction

/-! ## The Hilbert direct sum -/

section LpNormSq

variable {I : Type} {E : I → Type*} [∀ i, NormedAddCommGroup (E i)]

theorem lp_norm_sq_eq_tsum (x : lp E 2) :
    ‖x‖ ^ 2 = ∑' i, ‖(x : ∀ i, E i) i‖ ^ 2 := by
  have h : ‖x‖ ^ (2 : ℝ) = ∑' i, ‖(x : ∀ i, E i) i‖ ^ (2 : ℝ) := by
    simpa using lp.norm_rpow_eq_tsum (p := 2) (E := E) (by norm_num) x
  rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num] at h
  simpa only [Real.rpow_natCast] using h

theorem lp_summable_norm_sq (x : lp E 2) :
    Summable fun i => ‖(x : ∀ i, E i) i‖ ^ 2 := by
  have h := (lp.memℓp x).summable (p := 2) (by norm_num)
  have hcast : ((2 : ℝ≥0∞).toReal) = ((2 : ℕ) : ℝ) := by norm_num
  simp only [hcast, Real.rpow_natCast] at h
  exact h

theorem lp_le_norm_of_blockwise {I : Type} {E F : I → Type*}
    [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedAddCommGroup (F i)]
    {c : ℝ} (hc : 0 ≤ c) (x : lp E 2) (y : lp F 2)
    (h : ∀ i, c * ‖(x : ∀ i, E i) i‖ ≤ ‖(y : ∀ i, F i) i‖) : c * ‖x‖ ≤ ‖y‖ := by
  have hsq : (c * ‖x‖) ^ 2 ≤ ‖y‖ ^ 2 := by
    rw [mul_pow, lp_norm_sq_eq_tsum, lp_norm_sq_eq_tsum, ← tsum_mul_left]
    refine Summable.tsum_le_tsum (fun i => ?_)
      ((lp_summable_norm_sq x).mul_left _) (lp_summable_norm_sq y)
    have h0 : 0 ≤ c * ‖(x : ∀ i, E i) i‖ := by positivity
    calc c ^ 2 * ‖(x : ∀ i, E i) i‖ ^ 2 = (c * ‖(x : ∀ i, E i) i‖) ^ 2 := by ring
      _ ≤ ‖(y : ∀ i, F i) i‖ ^ 2 := pow_le_pow_left₀ h0 (h i) 2
  have h1 : 0 ≤ c * ‖x‖ := by positivity
  nlinarith [hsq, h1, norm_nonneg y]


end LpNormSq

section OrbitHilbert

variable {I : Type} {H K : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
variable (D : H →L[ℂ] K) (U : I → (H ≃ₗᵢ[ℂ] H)) (V : I → (K ≃ₗᵢ[ℂ] K))

omit [CompleteSpace H] [CompleteSpace K] in
theorem mem_ker_orbitBlock_iff (i : I) (x : H) :
    x ∈ LinearMap.ker (orbitBlock D U V i : H →ₗ[ℂ] K)
      ↔ (U i).symm x ∈ LinearMap.ker (D : H →ₗ[ℂ] K) := by
  simp only [LinearMap.mem_ker, ContinuousLinearMap.coe_coe, orbitBlock_apply]
  constructor
  · intro h
    have : V i (D ((U i).symm x)) = V i 0 := by rw [h, map_zero]
    exact (V i).injective this
  · intro h
    rw [h, map_zero]

omit [CompleteSpace H] [CompleteSpace K] in
theorem mem_ker_orbitBlock_orthogonal_iff (i : I) (x : H) :
    x ∈ (LinearMap.ker (orbitBlock D U V i : H →ₗ[ℂ] K))ᗮ
      ↔ (U i).symm x ∈ (LinearMap.ker (D : H →ₗ[ℂ] K))ᗮ := by
  simp only [Submodule.mem_orthogonal]
  constructor
  · intro h w hw
    have hw' : U i w ∈ LinearMap.ker (orbitBlock D U V i : H →ₗ[ℂ] K) := by
      rw [mem_ker_orbitBlock_iff]
      simpa using hw
    have := h (U i w) hw'
    rwa [← (U i).symm.inner_map_map (U i w) x, LinearIsometryEquiv.symm_apply_apply] at this
  · intro h w hw
    rw [mem_ker_orbitBlock_iff] at hw
    have := h ((U i).symm w) hw
    rwa [(U i).symm.inner_map_map w x] at this

omit [CompleteSpace H] [CompleteSpace K] in
theorem coeFn_mem_ker_orthogonal [DecidableEq I]
    (ξ : lp (fun _ : I => H) 2)
    (hξ : ξ ∈ (LinearMap.ker (orbitInduction D U V : lp (fun _ : I => H) 2 →ₗ[ℂ]
      lp (fun _ : I => K) 2))ᗮ) (i : I) :
    (ξ : ∀ _ : I, H) i ∈ (LinearMap.ker (orbitBlock D U V i : H →ₗ[ℂ] K))ᗮ := by
  rw [Submodule.mem_orthogonal]
  intro v hv
  rw [Submodule.mem_orthogonal] at hξ
  have hsingle : (lp.single 2 i v : lp (fun _ : I => H) 2)
      ∈ LinearMap.ker (orbitInduction D U V : lp (fun _ : I => H) 2 →ₗ[ℂ]
        lp (fun _ : I => K) 2) := by
    simp only [LinearMap.mem_ker, ContinuousLinearMap.coe_coe]
    rw [orbitInduction_single D U V i v]
    rw [LinearMap.mem_ker, ContinuousLinearMap.coe_coe] at hv
    rw [hv]
    ext j
    simp
  have h := hξ _ hsingle
  rwa [lp.inner_single_left (𝕜 := ℂ) i v ξ] at h

omit [CompleteSpace H] [CompleteSpace K] in
theorem norm_orbitInduction_apply_coe (ξ : lp (fun _ : I => H) 2) (i : I) :
    ‖(orbitInduction D U V ξ : ∀ _ : I, K) i‖ = ‖D ((U i).symm ((ξ : ∀ _ : I, H) i))‖ := by
  rw [orbitInduction_apply, (V i).norm_map]

omit [CompleteSpace H] [CompleteSpace K] in
/-- `(OI.7)`  A transverse lower bound for the local operator transfers to the induction. -/
theorem le_norm_orbitInduction_of_le_norm [DecidableEq I] {c : ℝ} (hc : 0 ≤ c)
    (h : ∀ x ∈ (LinearMap.ker (D : H →ₗ[ℂ] K))ᗮ, c * ‖x‖ ≤ ‖D x‖)
    (ξ : lp (fun _ : I => H) 2)
    (hξ : ξ ∈ (LinearMap.ker (orbitInduction D U V : lp (fun _ : I => H) 2 →ₗ[ℂ]
      lp (fun _ : I => K) 2))ᗮ) :
    c * ‖ξ‖ ≤ ‖orbitInduction D U V ξ‖ := by
  have hblk : ∀ i, c * ‖(ξ : ∀ _ : I, H) i‖ ≤ ‖(orbitInduction D U V ξ : ∀ _ : I, K) i‖ := by
    intro i
    have hmem := coeFn_mem_ker_orthogonal D U V ξ hξ i
    rw [mem_ker_orbitBlock_orthogonal_iff] at hmem
    have hb := h _ hmem
    rw [(U i).symm.norm_map] at hb
    rw [norm_orbitInduction_apply_coe]
    exact hb
  have hsq : (c * ‖ξ‖) ^ 2 ≤ ‖orbitInduction D U V ξ‖ ^ 2 := by
    rw [mul_pow, lp_norm_sq_eq_tsum, lp_norm_sq_eq_tsum, ← tsum_mul_left]
    refine Summable.tsum_le_tsum (fun i => ?_)
      ((lp_summable_norm_sq ξ).mul_left _) (lp_summable_norm_sq _)
    have hi := hblk i
    have h0 : 0 ≤ c * ‖(ξ : ∀ _ : I, H) i‖ := by positivity
    calc c ^ 2 * ‖(ξ : ∀ _ : I, H) i‖ ^ 2 = (c * ‖(ξ : ∀ _ : I, H) i‖) ^ 2 := by ring
      _ ≤ ‖(orbitInduction D U V ξ : ∀ _ : I, K) i‖ ^ 2 := pow_le_pow_left₀ h0 hi 2
  have h1 : 0 ≤ c * ‖ξ‖ := by positivity
  nlinarith [hsq, h1, norm_nonneg (orbitInduction D U V ξ)]

omit [CompleteSpace H] [CompleteSpace K] in
theorem mem_ker_orbitInduction_orthogonal_single [DecidableEq I] (i : I) (y : H)
    (hy : y ∈ (LinearMap.ker (orbitBlock D U V i : H →ₗ[ℂ] K))ᗮ) :
    (lp.single 2 i y : lp (fun _ : I => H) 2)
      ∈ (LinearMap.ker (orbitInduction D U V : lp (fun _ : I => H) 2 →ₗ[ℂ]
        lp (fun _ : I => K) 2))ᗮ := by
  rw [Submodule.mem_orthogonal]
  intro η hη
  rw [LinearMap.mem_ker, ContinuousLinearMap.coe_coe, orbitInduction_eq_zero_iff] at hη
  rw [lp.inner_single_right (𝕜 := ℂ) i y η]
  rw [Submodule.mem_orthogonal] at hy
  refine hy _ ?_
  rw [mem_ker_orbitBlock_iff, LinearMap.mem_ker, ContinuousLinearMap.coe_coe]
  exact hη i

omit [CompleteSpace H] [CompleteSpace K] in
/-- `(OI.7)`  Orbit induction preserves the transverse lower bound exactly. -/
theorem hasTransverseLowerBound_orbitInduction_iff [DecidableEq I] [Nonempty I] :
    ContinuousLinearMap.HasTransverseLowerBound (orbitInduction D U V)
      ↔ ContinuousLinearMap.HasTransverseLowerBound D := by
  constructor
  · rintro ⟨c, hc, hbound⟩
    obtain ⟨i⟩ := ‹Nonempty I›
    refine ⟨c, hc, fun x hx => ?_⟩
    have hy : (U i x) ∈ (LinearMap.ker (orbitBlock D U V i : H →ₗ[ℂ] K))ᗮ := by
      rw [mem_ker_orbitBlock_orthogonal_iff]
      simpa using hx
    have h := hbound _ (mem_ker_orbitInduction_orthogonal_single D U V i _ hy)
    rw [orbitInduction_single D U V i (U i x)] at h
    have h1 : ‖(lp.single 2 i (orbitBlock D U V i (U i x)) : lp (fun _ : I => K) 2)‖
        = ‖orbitBlock D U V i (U i x)‖ :=
      lp.norm_single (E := fun _ : I => K) (by norm_num) i _
    have h2 : ‖(lp.single 2 i (U i x) : lp (fun _ : I => H) 2)‖ = ‖U i x‖ :=
      lp.norm_single (E := fun _ : I => H) (by norm_num) i _
    rw [h1, h2, (U i).norm_map] at h
    rwa [orbitBlock_apply, LinearIsometryEquiv.symm_apply_apply, (V i).norm_map] at h
  · rintro ⟨c, hc, hbound⟩
    exact ⟨c, hc, fun ξ hξ => le_norm_orbitInduction_of_le_norm D U V hc.le hbound ξ hξ⟩

/-- `(OI.7)`  The induced range is closed exactly when the local range is closed. -/
theorem isClosed_range_orbitInduction_iff [DecidableEq I] [Nonempty I] :
    IsClosed (Set.range (orbitInduction D U V)) ↔ IsClosed (Set.range D) := by
  rw [← ContinuousLinearMap.hasTransverseLowerBound_iff_isClosed_range,
    ← ContinuousLinearMap.hasTransverseLowerBound_iff_isClosed_range]
  exact hasTransverseLowerBound_orbitInduction_iff D U V

/-! ## Essentialization -/

section Escape

variable [DecidableEq I] [Infinite I]

/-- One transported copy of a vector at each of countably many distinct orbit points. -/
def orbitEscape (U : I → (H ≃ₗᵢ[ℂ] H)) (x : H) (n : ℕ) : lp (fun _ : I => H) 2 :=
  lp.single 2 (Infinite.natEmbedding I n) (U (Infinite.natEmbedding I n) x)

omit [CompleteSpace H] in
theorem norm_orbitEscape (x : H) (n : ℕ) : ‖orbitEscape U x n‖ = ‖x‖ := by
  rw [orbitEscape, lp.norm_single (E := fun _ : I => H) (by norm_num), (U _).norm_map]

omit [CompleteSpace H] in
theorem weaklyNull_orbitEscape (x : H) (z : lp (fun _ : I => H) 2) :
    Tendsto (fun n => ⟪z, orbitEscape U x n⟫_ℂ) atTop (𝓝 0) := by
  have hsum : Summable fun n : ℕ => ‖(z : ∀ _ : I, H) (Infinite.natEmbedding I n)‖ ^ 2 :=
    (lp_summable_norm_sq z).comp_injective (Infinite.natEmbedding I).injective
  have hz2 : Tendsto (fun n : ℕ => ‖(z : ∀ _ : I, H) (Infinite.natEmbedding I n)‖ ^ 2)
      atTop (𝓝 0) := hsum.tendsto_atTop_zero
  have hz : Tendsto (fun n : ℕ => ‖(z : ∀ _ : I, H) (Infinite.natEmbedding I n)‖)
      atTop (𝓝 0) := by
    have hsqrt := (Real.continuous_sqrt.tendsto 0).comp hz2
    simpa [Function.comp_def, Real.sqrt_sq (norm_nonneg _)] using hsqrt
  refine squeeze_zero_norm (fun n => ?_) (by simpa using hz.mul_const ‖x‖)
  rw [orbitEscape, lp.inner_single_right (𝕜 := ℂ)]
  refine le_trans (norm_inner_le_norm _ _) ?_
  rw [(U _).norm_map]

omit [CompleteSpace H] [CompleteSpace K] in
theorem norm_orbitInduction_orbitEscape (x : H) (n : ℕ) :
    ‖orbitInduction D U V (orbitEscape U x n)‖ = ‖D x‖ := by
  rw [orbitEscape, orbitInduction_single D U V]
  rw [lp.norm_single (E := fun _ : I => K) (by norm_num)]
  rw [orbitBlock_apply, LinearIsometryEquiv.symm_apply_apply, (V _).norm_map]

/-- `(OI.9)`  Every compact perturbation of the induced operator is at least as large as the local
operator. -/
theorem norm_le_norm_sub_of_isCompactOperator
    (C : lp (fun _ : I => H) 2 →L[ℂ] lp (fun _ : I => K) 2) (hC : IsCompactOperator C) :
    ‖D‖ ≤ ‖orbitInduction D U V - C‖ := by
  refine ContinuousLinearMap.opNorm_le_of_unit_norm
    (norm_nonneg (orbitInduction D U V - C)) fun x hx => ?_
  have hb : ∀ n, ‖orbitEscape U x n‖ ≤ 1 := fun n => by
    rw [norm_orbitEscape, hx]
  have hCn : Tendsto (fun n => C (orbitEscape U x n)) atTop (𝓝 0) :=
    tendsto_norm_compact_of_weaklyNull C hC _ hb (weaklyNull_orbitEscape U x)
  have hnorm : Tendsto (fun n => ‖C (orbitEscape U x n)‖) atTop (𝓝 0) := by
    simpa using hCn.norm
  have hle : ∀ n, ‖D x‖ - ‖C (orbitEscape U x n)‖ ≤ ‖orbitInduction D U V - C‖ := by
    intro n
    have h1 : ‖(orbitInduction D U V - C) (orbitEscape U x n)‖
        ≤ ‖orbitInduction D U V - C‖ * ‖orbitEscape U x n‖ :=
      ContinuousLinearMap.le_opNorm _ _
    rw [norm_orbitEscape, hx, mul_one] at h1
    have h2 : ‖orbitInduction D U V (orbitEscape U x n)‖ - ‖C (orbitEscape U x n)‖
        ≤ ‖(orbitInduction D U V - C) (orbitEscape U x n)‖ := by
      simpa using norm_sub_norm_le (orbitInduction D U V (orbitEscape U x n))
        (C (orbitEscape U x n))
    rw [norm_orbitInduction_orbitEscape] at h2
    linarith
  have hlim : Tendsto (fun n => ‖D x‖ - ‖C (orbitEscape U x n)‖) atTop (𝓝 ‖D x‖) := by
    simpa using (tendsto_const_nhds (x := ‖D x‖) (f := atTop (α := ℕ))).sub hnorm
  exact le_of_tendsto hlim (Filter.Eventually.of_forall hle)

/-- **Theorem 3.1, `(OI.9)`.**  Orbit induction turns the local norm into the global essential
norm. -/
theorem rectEssentialNorm_orbitInduction :
    rectEssentialNorm (orbitInduction D U V) = ‖D‖ := by
  refine le_antisymm ?_ (le_rectEssentialNorm _ _ fun C hC =>
    norm_le_norm_sub_of_isCompactOperator D U V C hC)
  rw [← norm_orbitInduction D U V]
  exact rectEssentialNorm_le_norm _

/-- **Theorem 3.1, `(OI.8)`.**  The induced operator is compact exactly when the local operator
vanishes. -/
theorem isCompactOperator_orbitInduction_iff :
    IsCompactOperator (orbitInduction D U V) ↔ D = 0 := by
  constructor
  · intro h
    have h0 := rectEssentialNorm_eq_zero_of_isCompactOperator h
    rw [rectEssentialNorm_orbitInduction] at h0
    exact norm_eq_zero.mp h0
  · rintro rfl
    have hzero : orbitInduction (0 : H →L[ℂ] K) U V = 0 := by
      refine ContinuousLinearMap.ext fun ξ => ?_
      have : orbitInduction (0 : H →L[ℂ] K) U V ξ = 0 := by
        ext i
        simp
      simpa using this
    rw [hzero]
    exact isCompactOperator_zero

/-- **Prediction 9.1, `(OI.25)`.**  A nonzero compact one-shell residual, transported unitarily to
infinitely many orthogonal shells, assembles to a residual of essential norm exactly `‖K‖`.  Hence
pointwise Calkin triviality on every shell does not imply global Calkin triviality: the assembled
residual is not compact. -/
theorem shellResidual_essentialNorm (hne : D ≠ 0) :
    rectEssentialNorm (orbitInduction D U V) = ‖D‖
      ∧ 0 < ‖D‖ ∧ ¬ IsCompactOperator (orbitInduction D U V) :=
  ⟨rectEssentialNorm_orbitInduction D U V, norm_pos_iff.mpr hne,
    fun h => hne ((isCompactOperator_orbitInduction_iff D U V).mp h)⟩


/-- **Scope item 6.**  Scaling the local defect scales the global essential norm exactly; approximate
local neutrality is never exact global compactness. -/
theorem rectEssentialNorm_orbitInduction_smul (c : ℂ) :
    rectEssentialNorm (orbitInduction (c • D) U V) = ‖c‖ * ‖D‖ := by
  rw [rectEssentialNorm_orbitInduction, norm_smul]


end Escape

/-! ## Blockwise injectivity, lower bounds and the positive Gram -/

section Classification

omit [CompleteSpace H] [CompleteSpace K] in
/-- **Corollary 2.2 (1)**, kernel side.  Injectivity of the induction is local injectivity. -/
theorem orbitInduction_injective_iff [DecidableEq I] [Nonempty I] :
    Function.Injective (orbitInduction D U V) ↔ Function.Injective D := by
  rw [injective_iff_map_eq_zero, injective_iff_map_eq_zero]
  constructor
  · intro h x hx
    obtain ⟨i⟩ := ‹Nonempty I›
    have hz : orbitInduction D U V (lp.single 2 i (U i x)) = 0 := by
      rw [orbitInduction_single D U V i (U i x), orbitBlock_apply,
        LinearIsometryEquiv.symm_apply_apply, hx, map_zero]
      ext j
      simp
    have := h _ hz
    have hn : ‖(lp.single 2 i (U i x) : lp (fun _ : I => H) 2)‖ = ‖U i x‖ :=
      lp.norm_single (E := fun _ : I => H) (by norm_num) i _
    rw [this, norm_zero, (U i).norm_map] at hn
    exact norm_eq_zero.mp hn.symm
  · intro h ξ hξ
    rw [orbitInduction_eq_zero_iff] at hξ
    ext i
    have := h _ (hξ i)
    have h2 : (U i) ((U i).symm ((ξ : ∀ _ : I, H) i)) = (U i) 0 := by rw [this, map_zero]
    rw [LinearIsometryEquiv.apply_symm_apply, map_zero] at h2
    simpa using h2

omit [CompleteSpace H] [CompleteSpace K] in
/-- **Corollary 2.2 (1)**, `(OI.7)`.  Orbit induction preserves being bounded below. -/
theorem exists_lower_bound_orbitInduction_iff [DecidableEq I] [Nonempty I] :
    (∃ c > 0, ∀ ξ : lp (fun _ : I => H) 2, c * ‖ξ‖ ≤ ‖orbitInduction D U V ξ‖)
      ↔ ∃ c > 0, ∀ x : H, c * ‖x‖ ≤ ‖D x‖ := by
  constructor
  · rintro ⟨c, hc, h⟩
    obtain ⟨i⟩ := ‹Nonempty I›
    refine ⟨c, hc, fun x => ?_⟩
    have hb := h (lp.single 2 i (U i x))
    rw [orbitInduction_single D U V i (U i x)] at hb
    have h1 : ‖(lp.single 2 i (orbitBlock D U V i (U i x)) : lp (fun _ : I => K) 2)‖
        = ‖orbitBlock D U V i (U i x)‖ :=
      lp.norm_single (E := fun _ : I => K) (by norm_num) i _
    have h2 : ‖(lp.single 2 i (U i x) : lp (fun _ : I => H) 2)‖ = ‖U i x‖ :=
      lp.norm_single (E := fun _ : I => H) (by norm_num) i _
    rw [h1, h2, (U i).norm_map, orbitBlock_apply, LinearIsometryEquiv.symm_apply_apply,
      (V i).norm_map] at hb
    exact hb
  · rintro ⟨c, hc, h⟩
    refine ⟨c, hc, fun ξ => ?_⟩
    have hblk : ∀ i, c * ‖(ξ : ∀ _ : I, H) i‖
        ≤ ‖(orbitInduction D U V ξ : ∀ _ : I, K) i‖ := by
      intro i
      have hb := h ((U i).symm ((ξ : ∀ _ : I, H) i))
      rw [(U i).symm.norm_map] at hb
      rw [norm_orbitInduction_apply_coe]
      exact hb
    have hsq : (c * ‖ξ‖) ^ 2 ≤ ‖orbitInduction D U V ξ‖ ^ 2 := by
      rw [mul_pow, lp_norm_sq_eq_tsum, lp_norm_sq_eq_tsum, ← tsum_mul_left]
      refine Summable.tsum_le_tsum (fun i => ?_)
        ((lp_summable_norm_sq ξ).mul_left _) (lp_summable_norm_sq _)
      have h0 : 0 ≤ c * ‖(ξ : ∀ _ : I, H) i‖ := by positivity
      calc c ^ 2 * ‖(ξ : ∀ _ : I, H) i‖ ^ 2 = (c * ‖(ξ : ∀ _ : I, H) i‖) ^ 2 := by ring
        _ ≤ ‖(orbitInduction D U V ξ : ∀ _ : I, K) i‖ ^ 2 := pow_le_pow_left₀ h0 (hblk i) 2
    have h1 : 0 ≤ c * ‖ξ‖ := by positivity
    nlinarith [hsq, h1, norm_nonneg (orbitInduction D U V ξ)]

/-- The adjoint of an orbit induction is the orbit induction of the adjoint with the roles of the
two unitary families exchanged. -/
theorem adjoint_orbitInduction :
    ContinuousLinearMap.adjoint (orbitInduction D U V)
      = orbitInduction (ContinuousLinearMap.adjoint D) V U := by
  refine ((ContinuousLinearMap.eq_adjoint_iff
    (orbitInduction (ContinuousLinearMap.adjoint D) V U) (orbitInduction D U V)).mpr
    fun x y => ?_).symm
  have hsum1 := lp.hasSum_inner (𝕜 := ℂ) (G := fun _ : I => H)
    (orbitInduction (ContinuousLinearMap.adjoint D) V U x) y
  have hsum2 := lp.hasSum_inner (𝕜 := ℂ) (G := fun _ : I => K) x (orbitInduction D U V y)
  refine hsum1.unique (hsum2.congr_fun fun i => ?_)
  show ⟪(orbitInduction (ContinuousLinearMap.adjoint D) V U x : ∀ _ : I, H) i,
        (y : ∀ _ : I, H) i⟫_ℂ
    = ⟪(x : ∀ _ : I, K) i, (orbitInduction D U V y : ∀ _ : I, K) i⟫_ℂ
  rw [orbitInduction_apply, orbitInduction_apply]
  have hU : ⟪U i (ContinuousLinearMap.adjoint D ((V i).symm ((x : ∀ _ : I, K) i))),
      (y : ∀ _ : I, H) i⟫_ℂ
      = ⟪ContinuousLinearMap.adjoint D ((V i).symm ((x : ∀ _ : I, K) i)),
        (U i).symm ((y : ∀ _ : I, H) i)⟫_ℂ := by
    have h := (U i).inner_map_map
      (ContinuousLinearMap.adjoint D ((V i).symm ((x : ∀ _ : I, K) i)))
      ((U i).symm ((y : ∀ _ : I, H) i))
    rw [LinearIsometryEquiv.apply_symm_apply] at h
    exact h
  have hV : ⟪(x : ∀ _ : I, K) i, V i (D ((U i).symm ((y : ∀ _ : I, H) i)))⟫_ℂ
      = ⟪(V i).symm ((x : ∀ _ : I, K) i), D ((U i).symm ((y : ∀ _ : I, H) i))⟫_ℂ := by
    have h := (V i).inner_map_map ((V i).symm ((x : ∀ _ : I, K) i))
      (D ((U i).symm ((y : ∀ _ : I, H) i)))
    rw [LinearIsometryEquiv.apply_symm_apply] at h
    exact h
  rw [hU, hV, ContinuousLinearMap.adjoint_inner_left]

/-- **Theorem 4.2, `(OI.G1)`.**  The positive Gram operator of an orbit induction forgets the
output unitaries entirely. -/
theorem gram_orbitInduction :
    ContinuousLinearMap.adjoint (orbitInduction D U V) ∘L orbitInduction D U V
      = orbitInduction (ContinuousLinearMap.adjoint D ∘L D) U U := by
  rw [adjoint_orbitInduction]
  refine ContinuousLinearMap.ext fun ξ => ?_
  ext i
  show U i (ContinuousLinearMap.adjoint D ((V i).symm
      (V i (D ((U i).symm ((ξ : ∀ _ : I, H) i))))))
    = U i ((ContinuousLinearMap.adjoint D ∘L D) ((U i).symm ((ξ : ∀ _ : I, H) i)))
  rw [LinearIsometryEquiv.symm_apply_apply]
  rfl

/-- **Corollary 2.2 (2)**.  Surjectivity of the induction is local surjectivity. -/
theorem orbitInduction_surjective_iff [DecidableEq I] [Nonempty I] :
    Function.Surjective (orbitInduction D U V) ↔ Function.Surjective D := by
  constructor
  · intro h k
    obtain ⟨i⟩ := ‹Nonempty I›
    obtain ⟨ξ, hξ⟩ := h (lp.single 2 i (V i k))
    refine ⟨(U i).symm ((ξ : ∀ _ : I, H) i), ?_⟩
    have hco := congrArg (fun z : lp (fun _ : I => K) 2 => (z : ∀ _ : I, K) i) hξ
    simp only [orbitInduction_apply] at hco
    rw [show ((lp.single 2 i (V i k) : lp (fun _ : I => K) 2) : ∀ _ : I, K) i = V i k from
      lp.single_apply_self (E := fun _ : I => K) 2 i (V i k)] at hco
    exact (V i).injective hco
  · intro h
    have hrange : LinearMap.range (D : H →ₗ[ℂ] K) = ⊤ := by
      rw [LinearMap.range_eq_top]
      exact h
    obtain ⟨fsymm, _⟩ := ContinuousLinearMap.exists_nonlinearRightInverse_of_surjective D hrange
    intro y
    have hle : ∀ i : I, ‖U i (fsymm ((V i).symm ((y : ∀ _ : I, K) i)))‖
        ≤ (fsymm.nnnorm : ℝ) * ‖(y : ∀ _ : I, K) i‖ := by
      intro i
      rw [(U i).norm_map]
      have hb := fsymm.bound' ((V i).symm ((y : ∀ _ : I, K) i))
      rwa [(V i).symm.norm_map] at hb
    have hmem : Memℓp (fun i => U i (fsymm ((V i).symm ((y : ∀ _ : I, K) i)))) 2 := by
      refine memℓp_gen ?_
      have hy : Summable fun i => ‖(y : ∀ _ : I, K) i‖ ^ (2 : ℝ) :=
        (lp.memℓp y).summable (by norm_num)
      refine Summable.of_nonneg_of_le (fun i => Real.rpow_nonneg (norm_nonneg _) 2) ?_
        (hy.mul_left ((fsymm.nnnorm : ℝ) ^ (2 : ℝ)))
      intro i
      calc ‖U i (fsymm ((V i).symm ((y : ∀ _ : I, K) i)))‖ ^ (2 : ℝ)
          ≤ ((fsymm.nnnorm : ℝ) * ‖(y : ∀ _ : I, K) i‖) ^ (2 : ℝ) :=
            Real.rpow_le_rpow (norm_nonneg _) (hle i) (by norm_num)
        _ = (fsymm.nnnorm : ℝ) ^ (2 : ℝ) * ‖(y : ∀ _ : I, K) i‖ ^ (2 : ℝ) :=
            Real.mul_rpow (by positivity) (norm_nonneg _)
    refine ⟨⟨_, hmem⟩, ?_⟩
    ext i
    show V i (D ((U i).symm (U i (fsymm ((V i).symm ((y : ∀ _ : I, K) i))))))
      = (y : ∀ _ : I, K) i
    rw [LinearIsometryEquiv.symm_apply_apply, fsymm.right_inv',
      LinearIsometryEquiv.apply_symm_apply]

/-- **Corollary 2.2 (3)**.  The induction is bijective exactly when the local operator is. -/
theorem orbitInduction_bijective_iff [DecidableEq I] [Nonempty I] :
    Function.Bijective (orbitInduction D U V) ↔ Function.Bijective D :=
  and_congr (orbitInduction_injective_iff D U V) (orbitInduction_surjective_iff D U V)

end Classification

/-! ## Infinite multiplicity -/

section Multiplicity

theorem not_finiteDimensional_of_orthonormal {W : Type*} [NormedAddCommGroup W]
    [InnerProductSpace ℂ W] (g : ℕ → W) (hg : Orthonormal ℂ g) :
    ¬ FiniteDimensional ℂ W := by
  intro hfin
  have h1 : Cardinal.aleph0 ≤ Module.rank ℂ W := hg.linearIndependent.aleph0_le_rank
  have h2 : Module.rank ℂ W < Cardinal.aleph0 := Module.rank_lt_aleph0 ℂ W
  exact absurd h1 (not_le.mpr h2)

theorem orthonormal_lp_single_const {I : Type} [DecidableEq I] {W : Type*}
    [NormedAddCommGroup W] [InnerProductSpace ℂ W] (f : ℕ ↪ I) (v : ℕ → W)
    (hv : ∀ n, ‖v n‖ = 1) :
    Orthonormal ℂ fun n => (lp.single 2 (f n) (v n) : lp (fun _ : I => W) 2) := by
  constructor
  · intro n
    show ‖(lp.single 2 (f n) (v n) : lp (fun _ : I => W) 2)‖ = 1
    rw [lp.norm_single (E := fun _ : I => W) (by norm_num), hv n]
  · intro n m hnm
    show ⟪(lp.single 2 (f n) (v n) : lp (fun _ : I => W) 2),
        (lp.single 2 (f m) (v m) : lp (fun _ : I => W) 2)⟫_ℂ = 0
    rw [lp.inner_single_left (𝕜 := ℂ) (G := fun _ : I => W) (f n) (v n)]
    have hne : f n ≠ f m := fun h => hnm (f.injective h)
    rw [show ((lp.single 2 (f m) (v m) : lp (fun _ : I => W) 2) : ∀ _ : I, W) (f n) = 0 from
      lp.single_apply_ne (E := fun _ : I => W) 2 (f m) (v m) hne]
    exact inner_zero_right _

end Multiplicity

section OrbitMultiplicity

variable [DecidableEq I] [Infinite I]

omit [CompleteSpace H] in
theorem orthonormal_orbitEscape {x : H} (hx : ‖x‖ = 1) :
    Orthonormal ℂ (orbitEscape U x) :=
  orthonormal_lp_single_const (Infinite.natEmbedding I) _
    (fun n => by rw [(U _).norm_map, hx])

omit [CompleteSpace H] [CompleteSpace K] in
/-- **Corollary 4.1.**  One nonzero local kernel vector generates an infinite-dimensional global
kernel. -/
theorem not_finiteDimensional_ker_orbitInduction {x : H} (hx : ‖x‖ = 1) (hDx : D x = 0) :
    ¬ FiniteDimensional ℂ
      (LinearMap.ker (orbitInduction D U V : lp (fun _ : I => H) 2 →ₗ[ℂ]
        lp (fun _ : I => K) 2)) := by
  have hmem : ∀ n, orbitEscape U x n
      ∈ LinearMap.ker (orbitInduction D U V : lp (fun _ : I => H) 2 →ₗ[ℂ]
        lp (fun _ : I => K) 2) := by
    intro n
    simp only [LinearMap.mem_ker, ContinuousLinearMap.coe_coe]
    refine norm_eq_zero.mp ?_
    rw [norm_orbitInduction_orbitEscape, hDx, norm_zero]
  refine not_finiteDimensional_of_orthonormal
    (fun n => (⟨orbitEscape U x n, hmem n⟩ :
      LinearMap.ker (orbitInduction D U V : lp (fun _ : I => H) 2 →ₗ[ℂ]
        lp (fun _ : I => K) 2))) ?_
  have hon := orthonormal_orbitEscape U hx
  constructor
  · intro n
    exact hon.1 n
  · intro n m hnm
    exact hon.2 hnm

omit [CompleteSpace H] [CompleteSpace K] in
/-- **Corollary 4.1.**  A nonzero local operator generates an infinite-dimensional global range. -/
theorem not_finiteDimensional_range_orbitInduction {x : H} (hDx : D x ≠ 0) :
    ¬ FiniteDimensional ℂ
      (LinearMap.range (orbitInduction D U V : lp (fun _ : I => H) 2 →ₗ[ℂ]
        lp (fun _ : I => K) 2)) := by
  have hrpos : 0 < ‖D x‖ := norm_pos_iff.mpr hDx
  set c : ℂ := ((‖D x‖⁻¹ : ℝ) : ℂ) with hc
  set g : ℕ → lp (fun _ : I => K) 2 := fun n =>
    lp.single 2 (Infinite.natEmbedding I n) (c • (V (Infinite.natEmbedding I n)) (D x)) with hg
  have hon : Orthonormal ℂ g := by
    refine orthonormal_lp_single_const (Infinite.natEmbedding I) _ fun n => ?_
    rw [norm_smul, (V _).norm_map, hc, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (inv_pos.mpr hrpos), inv_mul_cancel₀ hrpos.ne']
  have hmem : ∀ n, g n ∈ LinearMap.range (orbitInduction D U V :
      lp (fun _ : I => H) 2 →ₗ[ℂ] lp (fun _ : I => K) 2) := by
    intro n
    refine ⟨c • orbitEscape U x n, ?_⟩
    rw [ContinuousLinearMap.coe_coe, map_smul, orbitEscape, orbitInduction_single D U V,
      orbitBlock_apply, LinearIsometryEquiv.symm_apply_apply, hg]
    ext j
    by_cases hj : j = Infinite.natEmbedding I n
    · subst hj
      simp
    · simp [hj]
  refine not_finiteDimensional_of_orthonormal
    (fun n => (⟨g n, hmem n⟩ : LinearMap.range (orbitInduction D U V :
      lp (fun _ : I => H) 2 →ₗ[ℂ] lp (fun _ : I => K) 2))) ?_
  constructor
  · intro n
    exact hon.1 n
  · intro n m hnm
    exact hon.2 hnm

/-- **Theorem 4.2, `(OI.G3)`.**  The positive Gram operator of the induction has essential norm
`‖D‖²`. -/
theorem rectEssentialNorm_gram_orbitInduction :
    rectEssentialNorm
        (ContinuousLinearMap.adjoint (orbitInduction D U V) ∘L orbitInduction D U V)
      = ‖D‖ * ‖D‖ := by
  rw [gram_orbitInduction, rectEssentialNorm_orbitInduction,
    ContinuousLinearMap.norm_adjoint_comp_self]

end OrbitMultiplicity

end OrbitHilbert

end

end GaloisForLFunctions.HTGeometry
