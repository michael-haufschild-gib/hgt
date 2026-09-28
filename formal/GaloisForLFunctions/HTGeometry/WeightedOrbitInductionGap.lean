import GaloisForLFunctions.HTGeometry.WeightedOrbitInduction

/-!
# Weighted orbit induction: reduced minimum modulus, semi-Fredholm thresholds, and the Gram

For the weighted orbit induction `Ind_a(D) = ⊕ aᵢ Vᵢ D Uᵢ⁻¹`, zero amplitudes are allowed: their
blocks lie in the kernel.  With the reduced amplitude gap `α_*(a) = inf_{aᵢ ≠ 0} |aᵢ|` this module
proves

* `reducedMinModulus_weightedInduction` `(WOI.4)` — the reduced minimum modulus is exactly
  `γ(Ind_a D) = α_*(a) γ(D)`;
* `isClosed_range_weightedInduction_iff_ampGap` `(WOI.5)` — the range is closed exactly when the
  range of `D` is closed and `α_*(a) > 0`;
* `isUpperSemiFredholm_weightedInduction_iff`, `isLowerSemiFredholm_weightedInduction_iff`,
  `isBoundedFredholm_weightedInduction_iff` — the homogeneous Fredholm thresholds: with all
  amplitudes nonzero over an infinite orbit, the induction is upper semi-Fredholm, lower
  semi-Fredholm, or Fredholm exactly when `D` is bounded below, surjective, or invertible, and
  `α_*(a) > 0`; a nonzero local kernel or cokernel is repeated infinitely;
* `adjoint_weightedInduction` and `gram_weightedInduction` `(WOI.10)` — the positive Gram operator
  is the weighted induction of `D*D` with squared amplitudes, forgetting all output phases.
-/

namespace GaloisForLFunctions.HTGeometry

open Filter RHTower
open scoped ENNReal Topology InnerProductSpace

noncomputable section

/-! ## The reduced amplitude gap -/

section AmpGap

variable {I : Type}

/-- `(WOI.2)`  The reduced amplitude gap `α_*(a) = inf_{aᵢ ≠ 0} |aᵢ|`. -/
def ampGap (a : I → ℂ) : ℝ := ⨅ i : {i : I // a i ≠ 0}, ‖a i‖

theorem ampGap_nonneg (a : I → ℂ) : 0 ≤ ampGap a :=
  Real.iInf_nonneg fun _ => norm_nonneg _

theorem ampGap_le {a : I → ℂ} {i : I} (hi : a i ≠ 0) : ampGap a ≤ ‖a i‖ :=
  ciInf_le ⟨0, by rintro _ ⟨j, rfl⟩; exact norm_nonneg _⟩ (⟨i, hi⟩ : {i : I // a i ≠ 0})

theorem le_ampGap {a : I → ℂ} (hne : ∃ i, a i ≠ 0) {c : ℝ} (h : ∀ i, a i ≠ 0 → c ≤ ‖a i‖) :
    c ≤ ampGap a := by
  obtain ⟨i, hi⟩ := hne
  haveI : Nonempty {i : I // a i ≠ 0} := ⟨⟨i, hi⟩⟩
  exact le_ciInf fun j => h j j.2

theorem ampGap_pos_iff {a : I → ℂ} (hne : ∃ i, a i ≠ 0) :
    0 < ampGap a ↔ ∃ α > 0, ∀ i, a i ≠ 0 → α ≤ ‖a i‖ := by
  constructor
  · intro h
    exact ⟨ampGap a, h, fun i hi => ampGap_le hi⟩
  · rintro ⟨α, hα, h⟩
    exact lt_of_lt_of_le hα (le_ampGap hne h)

/-- With every amplitude nonzero, a positive gap is a uniform lower bound for all amplitudes. -/
theorem ampGap_pos_iff_of_forall_ne [Nonempty I] {a : I → ℂ} (ha : ∀ i, a i ≠ 0) :
    0 < ampGap a ↔ ∃ α > 0, ∀ i, α ≤ ‖a i‖ := by
  obtain ⟨i₀⟩ := ‹Nonempty I›
  rw [ampGap_pos_iff ⟨i₀, ha i₀⟩]
  exact ⟨fun ⟨α, hα, h⟩ => ⟨α, hα, fun i => h i (ha i)⟩,
    fun ⟨α, hα, h⟩ => ⟨α, hα, fun i _ => h i⟩⟩

end AmpGap

/-! ## The reduced minimum modulus -/

section ReducedMinModulus

variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

/-- The reduced minimum modulus `γ(T) = inf {‖T x‖ : x ⊥ ker T, ‖x‖ = 1}`. -/
def reducedMinModulus (T : E →L[ℂ] F) : ℝ :=
  ⨅ x : {x : E // x ∈ (LinearMap.ker (T : E →ₗ[ℂ] F))ᗮ ∧ ‖x‖ = 1}, ‖T x‖

omit [CompleteSpace E] [CompleteSpace F] in
theorem reducedMinModulus_nonneg (T : E →L[ℂ] F) : 0 ≤ reducedMinModulus T :=
  Real.iInf_nonneg fun _ => norm_nonneg _

omit [CompleteSpace E] [CompleteSpace F] in
theorem reducedMinModulus_le {T : E →L[ℂ] F} {x : E}
    (hx : x ∈ (LinearMap.ker (T : E →ₗ[ℂ] F))ᗮ) (hx1 : ‖x‖ = 1) :
    reducedMinModulus T ≤ ‖T x‖ :=
  ciInf_le ⟨0, by rintro _ ⟨y, rfl⟩; exact norm_nonneg _⟩
    (⟨x, hx, hx1⟩ : {x : E // x ∈ (LinearMap.ker (T : E →ₗ[ℂ] F))ᗮ ∧ ‖x‖ = 1})

omit [CompleteSpace E] [CompleteSpace F] in
/-- The reduced minimum modulus is a transverse lower bound. -/
theorem reducedMinModulus_mul_norm_le {T : E →L[ℂ] F} {x : E}
    (hx : x ∈ (LinearMap.ker (T : E →ₗ[ℂ] F))ᗮ) :
    reducedMinModulus T * ‖x‖ ≤ ‖T x‖ := by
  rcases eq_or_ne x 0 with rfl | hx0
  · simp
  have hpos : 0 < ‖x‖ := norm_pos_iff.mpr hx0
  set u : E := ((‖x‖⁻¹ : ℝ) : ℂ) • x with hu
  have hu1 : ‖u‖ = 1 := by
    rw [hu, norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hpos),
      inv_mul_cancel₀ hpos.ne']
  have hum : u ∈ (LinearMap.ker (T : E →ₗ[ℂ] F))ᗮ := Submodule.smul_mem _ _ hx
  have h := reducedMinModulus_le hum hu1
  rw [hu, map_smul, norm_smul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (inv_pos.mpr hpos), inv_mul_eq_div, le_div_iff₀ hpos] at h
  exact h

omit [CompleteSpace F] in
theorem le_reducedMinModulus {T : E →L[ℂ] F} (hT : T ≠ 0) {c : ℝ}
    (h : ∀ x ∈ (LinearMap.ker (T : E →ₗ[ℂ] F))ᗮ, ‖x‖ = 1 → c ≤ ‖T x‖) :
    c ≤ reducedMinModulus T := by
  obtain ⟨x, hx, hx1, -⟩ := exists_unit_mem_ker_orthogonal T hT
  haveI : Nonempty {x : E // x ∈ (LinearMap.ker (T : E →ₗ[ℂ] F))ᗮ ∧ ‖x‖ = 1} :=
    ⟨⟨x, hx, hx1⟩⟩
  exact le_ciInf fun y => h y y.2.1 y.2.2

omit [CompleteSpace F] in
/-- A nonzero operator has a transverse lower bound exactly when its reduced minimum modulus is
positive. -/
theorem hasTransverseLowerBound_iff_reducedMinModulus_pos {T : E →L[ℂ] F} (hT : T ≠ 0) :
    ContinuousLinearMap.HasTransverseLowerBound T ↔ 0 < reducedMinModulus T := by
  constructor
  · rintro ⟨c, hc, hb⟩
    refine lt_of_lt_of_le hc (le_reducedMinModulus hT fun x hx hx1 => ?_)
    have := hb x hx
    rwa [hx1, mul_one] at this
  · intro h
    exact ⟨reducedMinModulus T, h, fun x hx => reducedMinModulus_mul_norm_le hx⟩

/-- **Hilbert closed range.**  A nonzero operator has closed range exactly when its reduced
minimum modulus is positive. -/
theorem isClosed_range_iff_reducedMinModulus_pos {T : E →L[ℂ] F} (hT : T ≠ 0) :
    IsClosed (Set.range T) ↔ 0 < reducedMinModulus T := by
  rw [← ContinuousLinearMap.hasTransverseLowerBound_iff_isClosed_range,
    hasTransverseLowerBound_iff_reducedMinModulus_pos hT]

end ReducedMinModulus

/-! ## The weighted induction with zero amplitudes allowed -/

section Weighted

variable {I : Type} [Nonempty I] {H K : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

omit [CompleteSpace H] [CompleteSpace K] in
/-- Homogeneous orbit induction is the weighted induction with unit amplitudes. -/
theorem weightedInduction_one (D : H →L[ℂ] K) (U : I → (H ≃ₗᵢ[ℂ] H))
    (V : I → (K ≃ₗᵢ[ℂ] K)) (h1 : BddAbove (Set.range fun i => ‖(fun _ : I => (1 : ℂ)) i‖)) :
    weightedInduction (fun _ => 1) D U V h1 = orbitInduction D U V := by
  refine ContinuousLinearMap.ext fun ξ => ?_
  ext i
  simp [orbitInduction_apply]

omit [CompleteSpace H] [CompleteSpace K] in
/-- `(WOI.1)`  The kernel of the weighted induction: zero-amplitude blocks are free, and every
other block lies in the transported local kernel. -/
theorem weightedInduction_eq_zero_iff' (a : I → ℂ) (D : H →L[ℂ] K) (U : I → (H ≃ₗᵢ[ℂ] H))
    (V : I → (K ≃ₗᵢ[ℂ] K)) (hbdd : BddAbove (Set.range fun i => ‖a i‖))
    (ξ : lp (fun _ : I => H) 2) :
    weightedInduction a D U V hbdd ξ = 0
      ↔ ∀ i, a i ≠ 0 → D ((U i).symm ((ξ : ∀ _ : I, H) i)) = 0 := by
  constructor
  · intro h i hai
    have hi := congrArg (fun y : lp (fun _ : I => K) 2 => (y : ∀ _ : I, K) i) h
    simp only [weightedInduction_apply, lp.coeFn_zero, Pi.zero_apply] at hi
    rcases smul_eq_zero.mp hi with h0 | h0
    · exact absurd h0 hai
    · have : V i (D ((U i).symm ((ξ : ∀ _ : I, H) i))) = V i 0 := by rw [h0, map_zero]
      exact (V i).injective this
  · intro h
    ext i
    simp only [weightedInduction_apply, lp.coeFn_zero, Pi.zero_apply]
    by_cases hai : a i = 0
    · rw [hai, zero_smul]
    · rw [h i hai, map_zero, smul_zero]

omit [CompleteSpace H] [CompleteSpace K] in
theorem coeFn_eq_zero_of_mem_ker_weightedInduction_orthogonal (a : I → ℂ) (D : H →L[ℂ] K)
    (U : I → (H ≃ₗᵢ[ℂ] H)) (V : I → (K ≃ₗᵢ[ℂ] K)) (hbdd : BddAbove (Set.range fun i => ‖a i‖))
    {ξ : lp (fun _ : I => H) 2}
    (hξ : ξ ∈ (LinearMap.ker (weightedInduction a D U V hbdd : lp (fun _ : I => H) 2 →ₗ[ℂ]
      lp (fun _ : I => K) 2))ᗮ) {i : I} (hai : a i = 0) :
    (ξ : ∀ _ : I, H) i = 0 := by
  classical
  rw [Submodule.mem_orthogonal] at hξ
  have hmem : (lp.single 2 i ((ξ : ∀ _ : I, H) i) : lp (fun _ : I => H) 2)
      ∈ LinearMap.ker (weightedInduction a D U V hbdd : lp (fun _ : I => H) 2 →ₗ[ℂ]
        lp (fun _ : I => K) 2) := by
    simp only [LinearMap.mem_ker, ContinuousLinearMap.coe_coe]
    rw [weightedInduction_eq_zero_iff']
    intro j hj
    have hji : j ≠ i := fun h => hj (h ▸ hai)
    rw [lp.single_apply, Pi.single_eq_of_ne hji, map_zero, map_zero]
  have h := hξ _ hmem
  rw [lp.inner_single_left] at h
  exact inner_self_eq_zero.mp h

omit [CompleteSpace H] [CompleteSpace K] in
theorem coeFn_mem_ker_orthogonal_of_mem_ker_weightedInduction_orthogonal (a : I → ℂ)
    (D : H →L[ℂ] K) (U : I → (H ≃ₗᵢ[ℂ] H)) (V : I → (K ≃ₗᵢ[ℂ] K))
    (hbdd : BddAbove (Set.range fun i => ‖a i‖)) {ξ : lp (fun _ : I => H) 2}
    (hξ : ξ ∈ (LinearMap.ker (weightedInduction a D U V hbdd : lp (fun _ : I => H) 2 →ₗ[ℂ]
      lp (fun _ : I => K) 2))ᗮ) (i : I) :
    (U i).symm ((ξ : ∀ _ : I, H) i) ∈ (LinearMap.ker (D : H →ₗ[ℂ] K))ᗮ := by
  classical
  rw [Submodule.mem_orthogonal] at hξ ⊢
  intro w hw
  have hDw : D w = 0 := hw
  have hmem : (lp.single 2 i (U i w) : lp (fun _ : I => H) 2)
      ∈ LinearMap.ker (weightedInduction a D U V hbdd : lp (fun _ : I => H) 2 →ₗ[ℂ]
        lp (fun _ : I => K) 2) := by
    simp only [LinearMap.mem_ker, ContinuousLinearMap.coe_coe]
    rw [weightedInduction_eq_zero_iff']
    intro j _
    by_cases hji : j = i
    · subst hji
      rw [lp.single_apply, Pi.single_eq_same, LinearIsometryEquiv.symm_apply_apply, hDw]
    · rw [lp.single_apply, Pi.single_eq_of_ne hji, map_zero, map_zero]
  have h := hξ _ hmem
  rw [lp.inner_single_left] at h
  have hU := (U i).inner_map_map w ((U i).symm ((ξ : ∀ _ : I, H) i))
  rw [LinearIsometryEquiv.apply_symm_apply] at hU
  rw [← hU]
  exact h

omit [CompleteSpace H] [CompleteSpace K] in
theorem single_mem_ker_weightedInduction_orthogonal (a : I → ℂ) (D : H →L[ℂ] K)
    (U : I → (H ≃ₗᵢ[ℂ] H)) (V : I → (K ≃ₗᵢ[ℂ] K)) (hbdd : BddAbove (Set.range fun i => ‖a i‖))
    [DecidableEq I] {i : I} (hai : a i ≠ 0) {x : H}
    (hx : x ∈ (LinearMap.ker (D : H →ₗ[ℂ] K))ᗮ) :
    (lp.single 2 i (U i x) : lp (fun _ : I => H) 2)
      ∈ (LinearMap.ker (weightedInduction a D U V hbdd : lp (fun _ : I => H) 2 →ₗ[ℂ]
        lp (fun _ : I => K) 2))ᗮ := by
  rw [Submodule.mem_orthogonal]
  intro η hη
  simp only [LinearMap.mem_ker, ContinuousLinearMap.coe_coe] at hη
  rw [weightedInduction_eq_zero_iff'] at hη
  rw [lp.inner_single_right]
  have hU := (U i).inner_map_map ((U i).symm ((η : ∀ _ : I, H) i)) x
  rw [LinearIsometryEquiv.apply_symm_apply] at hU
  rw [hU]
  rw [Submodule.mem_orthogonal] at hx
  exact hx _ (hη i hai)

omit [CompleteSpace H] [CompleteSpace K] in
theorem weightedInduction_ne_zero (a : I → ℂ) (D : H →L[ℂ] K) (U : I → (H ≃ₗᵢ[ℂ] H))
    (V : I → (K ≃ₗᵢ[ℂ] K)) (hbdd : BddAbove (Set.range fun i => ‖a i‖)) (hne : ∃ i, a i ≠ 0)
    (hD : D ≠ 0) : weightedInduction a D U V hbdd ≠ 0 := by
  classical
  obtain ⟨i, hai⟩ := hne
  obtain ⟨x, hx⟩ : ∃ x : H, D x ≠ 0 := by
    by_contra h
    push Not at h
    exact hD (ContinuousLinearMap.ext h)
  intro h0
  have h := congrArg (fun T : lp (fun _ : I => H) 2 →L[ℂ] lp (fun _ : I => K) 2 =>
    ‖T (lp.single 2 i (U i x))‖) h0
  simp only [zero_apply, norm_zero] at h
  have hn := norm_weightedInduction_escapeAt a D U V hbdd x i
  rw [escapeAt] at hn
  rw [hn] at h
  rcases mul_eq_zero.mp h with h1 | h1
  · exact hai (norm_eq_zero.mp h1)
  · exact hx (norm_eq_zero.mp h1)

omit [CompleteSpace K] in
/-- **Theorem 2.1, `(WOI.4)`.**  With at least one nonzero amplitude and a nonzero local operator,
the reduced minimum modulus of the weighted induction is exactly `α_*(a) γ(D)`.  Zero-amplitude
blocks are part of the kernel and do not enter the gap. -/
theorem reducedMinModulus_weightedInduction (a : I → ℂ) (D : H →L[ℂ] K)
    (U : I → (H ≃ₗᵢ[ℂ] H)) (V : I → (K ≃ₗᵢ[ℂ] K)) (hbdd : BddAbove (Set.range fun i => ‖a i‖))
    (hne : ∃ i, a i ≠ 0) (hD : D ≠ 0) :
    reducedMinModulus (weightedInduction a D U V hbdd) = ampGap a * reducedMinModulus D := by
  classical
  have hInd := weightedInduction_ne_zero a D U V hbdd hne hD
  apply le_antisymm
  · -- upper bound: test on one transported unit vector in one live block
    have hblock : ∀ i, a i ≠ 0 →
        reducedMinModulus (weightedInduction a D U V hbdd) ≤ ‖a i‖ * reducedMinModulus D := by
      intro i hai
      have hapos : 0 < ‖a i‖ := norm_pos_iff.mpr hai
      rw [mul_comm, ← div_le_iff₀ hapos]
      refine le_reducedMinModulus hD fun x hx hx1 => ?_
      rw [div_le_iff₀ hapos]
      have h := reducedMinModulus_le
        (single_mem_ker_weightedInduction_orthogonal a D U V hbdd hai hx)
        (by rw [lp.norm_single (E := fun _ : I => H) (by norm_num), (U i).norm_map, hx1])
      have hn := norm_weightedInduction_escapeAt a D U V hbdd x i
      rw [escapeAt] at hn
      rw [hn] at h
      linarith
    rcases eq_or_lt_of_le (reducedMinModulus_nonneg D) with h0 | hpos
    · obtain ⟨i, hai⟩ := hne
      have := hblock i hai
      rw [← h0, mul_zero] at this
      rw [← h0, mul_zero]
      exact this
    · rw [← div_le_iff₀ hpos]
      refine le_ampGap hne fun i hai => ?_
      rw [div_le_iff₀ hpos]
      exact hblock i hai
  · -- lower bound: blockwise
    refine le_reducedMinModulus hInd fun ξ hξ hξ1 => ?_
    have hblk : ∀ i, (ampGap a * reducedMinModulus D) * ‖(ξ : ∀ _ : I, H) i‖
        ≤ ‖(weightedInduction a D U V hbdd ξ : ∀ _ : I, K) i‖ := by
      intro i
      rw [norm_weightedInduction_apply_coe]
      by_cases hai : a i = 0
      · rw [coeFn_eq_zero_of_mem_ker_weightedInduction_orthogonal a D U V hbdd hξ hai,
          norm_zero, mul_zero]
        positivity
      · have hmem := coeFn_mem_ker_orthogonal_of_mem_ker_weightedInduction_orthogonal
          a D U V hbdd hξ i
        have hγ := reducedMinModulus_mul_norm_le hmem
        rw [(U i).symm.norm_map] at hγ
        calc ampGap a * reducedMinModulus D * ‖(ξ : ∀ _ : I, H) i‖
            = ampGap a * (reducedMinModulus D * ‖(ξ : ∀ _ : I, H) i‖) := by ring
          _ ≤ ‖a i‖ * ‖D ((U i).symm ((ξ : ∀ _ : I, H) i))‖ :=
            mul_le_mul (ampGap_le hai) hγ
              (mul_nonneg (reducedMinModulus_nonneg D) (norm_nonneg _)) (norm_nonneg _)
    have h := lp_le_norm_of_blockwise
      (mul_nonneg (ampGap_nonneg a) (reducedMinModulus_nonneg D)) ξ _ hblk
    rwa [hξ1, mul_one] at h

/-- **Theorem 2.1, `(WOI.5)`.**  With at least one nonzero amplitude and a nonzero local operator,
the weighted induction has closed range exactly when the local range is closed and the reduced
amplitude gap is positive. -/
theorem isClosed_range_weightedInduction_iff_ampGap (a : I → ℂ) (D : H →L[ℂ] K)
    (U : I → (H ≃ₗᵢ[ℂ] H)) (V : I → (K ≃ₗᵢ[ℂ] K)) (hbdd : BddAbove (Set.range fun i => ‖a i‖))
    (hne : ∃ i, a i ≠ 0) (hD : D ≠ 0) :
    IsClosed (Set.range (weightedInduction a D U V hbdd))
      ↔ IsClosed (Set.range D) ∧ 0 < ampGap a := by
  rw [isClosed_range_iff_reducedMinModulus_pos (weightedInduction_ne_zero a D U V hbdd hne hD),
    isClosed_range_iff_reducedMinModulus_pos hD,
    reducedMinModulus_weightedInduction a D U V hbdd hne hD]
  constructor
  · intro h
    have hg := ampGap_nonneg a
    have hr := reducedMinModulus_nonneg D
    refine ⟨lt_of_le_of_ne hr fun h0 => ?_, lt_of_le_of_ne hg fun h0 => ?_⟩
    · rw [← h0, mul_zero] at h
      exact lt_irrefl _ h
    · rw [← h0, zero_mul] at h
      exact lt_irrefl _ h
  · rintro ⟨h1, h2⟩
    exact mul_pos h2 h1

end Weighted

/-! ## Adjoint and positive Gram -/

section Adjoint

variable {I : Type} [Nonempty I] {H K : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

omit [Nonempty I] in
theorem bddAbove_star_amp {a : I → ℂ} (hbdd : BddAbove (Set.range fun i => ‖a i‖)) :
    BddAbove (Set.range fun i => ‖(fun i => star (a i)) i‖) := by
  simpa [norm_star] using hbdd

omit [Nonempty I] in
theorem bddAbove_normSq_amp {a : I → ℂ} (hbdd : BddAbove (Set.range fun i => ‖a i‖)) :
    BddAbove (Set.range fun i => ‖(fun i => ((‖a i‖ ^ 2 : ℝ) : ℂ)) i‖) := by
  obtain ⟨M, hM⟩ := hbdd
  refine ⟨M ^ 2, ?_⟩
  rintro _ ⟨i, rfl⟩
  have hi : ‖a i‖ ≤ M := hM ⟨i, rfl⟩
  simp only [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg ‖a i‖)]
  exact pow_le_pow_left₀ (norm_nonneg _) hi 2

/-- The adjoint of a weighted induction is the weighted induction of the adjoint, with conjugate
amplitudes and the two unitary families exchanged. -/
theorem adjoint_weightedInduction (a : I → ℂ) (D : H →L[ℂ] K) (U : I → (H ≃ₗᵢ[ℂ] H))
    (V : I → (K ≃ₗᵢ[ℂ] K)) (hbdd : BddAbove (Set.range fun i => ‖a i‖)) :
    ContinuousLinearMap.adjoint (weightedInduction a D U V hbdd)
      = weightedInduction (fun i => star (a i)) (ContinuousLinearMap.adjoint D) V U
          (bddAbove_star_amp hbdd) := by
  refine ((ContinuousLinearMap.eq_adjoint_iff
    (weightedInduction (fun i => star (a i)) (ContinuousLinearMap.adjoint D) V U
      (bddAbove_star_amp hbdd)) (weightedInduction a D U V hbdd)).mpr fun x y => ?_).symm
  have hsum1 := lp.hasSum_inner (𝕜 := ℂ) (G := fun _ : I => H)
    (weightedInduction (fun i => star (a i)) (ContinuousLinearMap.adjoint D) V U
      (bddAbove_star_amp hbdd) x) y
  have hsum2 := lp.hasSum_inner (𝕜 := ℂ) (G := fun _ : I => K) x
    (weightedInduction a D U V hbdd y)
  refine hsum1.unique (hsum2.congr_fun fun i => ?_)
  show ⟪(weightedInduction (fun i => star (a i)) (ContinuousLinearMap.adjoint D) V U
        (bddAbove_star_amp hbdd) x : ∀ _ : I, H) i, (y : ∀ _ : I, H) i⟫_ℂ
    = ⟪(x : ∀ _ : I, K) i, (weightedInduction a D U V hbdd y : ∀ _ : I, K) i⟫_ℂ
  rw [weightedInduction_apply, weightedInduction_apply, inner_smul_left, inner_smul_right]
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
  simp

/-- **`(WOI.10)`.**  The positive Gram operator of a weighted induction is the weighted induction
of the local Gram `D*D`, transported by the input unitaries only, with squared amplitudes
`|aᵢ|²`. -/
theorem gram_weightedInduction (a : I → ℂ) (D : H →L[ℂ] K) (U : I → (H ≃ₗᵢ[ℂ] H))
    (V : I → (K ≃ₗᵢ[ℂ] K)) (hbdd : BddAbove (Set.range fun i => ‖a i‖)) :
    ContinuousLinearMap.adjoint (weightedInduction a D U V hbdd) ∘L weightedInduction a D U V hbdd
      = weightedInduction (fun i => ((‖a i‖ ^ 2 : ℝ) : ℂ))
          (ContinuousLinearMap.adjoint D ∘L D) U U (bddAbove_normSq_amp hbdd) := by
  rw [adjoint_weightedInduction]
  refine ContinuousLinearMap.ext fun ξ => ?_
  ext i
  show star (a i) • U i (ContinuousLinearMap.adjoint D ((V i).symm
      (a i • V i (D ((U i).symm ((ξ : ∀ _ : I, H) i))))))
    = ((‖a i‖ ^ 2 : ℝ) : ℂ) • U i ((ContinuousLinearMap.adjoint D ∘L D)
        ((U i).symm ((ξ : ∀ _ : I, H) i)))
  rw [map_smul, LinearIsometryEquiv.symm_apply_apply, map_smul, map_smul, smul_smul]
  congr 1
  rw [Complex.star_def, Complex.conj_mul']
  push_cast
  ring

/-- **Section 5 (3).**  The Gram operator depends on the amplitudes only through their moduli and
not at all on the output unitaries: output phases and `Vᵢ` disappear. -/
theorem gram_weightedInduction_eq_of_norm_eq {a b : I → ℂ} (hab : ∀ i, ‖a i‖ = ‖b i‖)
    (D : H →L[ℂ] K) (U : I → (H ≃ₗᵢ[ℂ] H)) (V V' : I → (K ≃ₗᵢ[ℂ] K))
    (ha : BddAbove (Set.range fun i => ‖a i‖)) (hb : BddAbove (Set.range fun i => ‖b i‖)) :
    ContinuousLinearMap.adjoint (weightedInduction a D U V ha) ∘L weightedInduction a D U V ha
      = ContinuousLinearMap.adjoint (weightedInduction b D U V' hb)
          ∘L weightedInduction b D U V' hb := by
  rw [gram_weightedInduction, gram_weightedInduction]
  have : (fun i => ((‖a i‖ ^ 2 : ℝ) : ℂ)) = fun i => ((‖b i‖ ^ 2 : ℝ) : ℂ) := by
    funext i
    rw [hab i]
  simp_rw [this]

end Adjoint

/-! ## Homogeneous semi-Fredholm thresholds -/

section Fredholm

variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

/-- Upper semi-Fredholm: closed range and finite-dimensional kernel. -/
def IsUpperSemiFredholm (T : E →L[ℂ] F) : Prop :=
  IsClosed (Set.range T) ∧ FiniteDimensional ℂ (LinearMap.ker (T : E →ₗ[ℂ] F))

/-- Lower semi-Fredholm: closed range and finite-dimensional Hilbert cokernel. -/
def IsLowerSemiFredholm (T : E →L[ℂ] F) : Prop :=
  IsClosed (Set.range T) ∧ FiniteDimensional ℂ (LinearMap.range (T : E →ₗ[ℂ] F))ᗮ

/-- Fredholm: both upper and lower semi-Fredholm. -/
def IsBoundedFredholm (T : E →L[ℂ] F) : Prop :=
  IsUpperSemiFredholm T ∧ IsLowerSemiFredholm T

/-- A bounded operator is bounded below exactly when it is injective with closed range. -/
theorem exists_pos_mul_norm_le_iff (T : E →L[ℂ] F) :
    (∃ c > 0, ∀ x, c * ‖x‖ ≤ ‖T x‖)
      ↔ LinearMap.ker (T : E →ₗ[ℂ] F) = ⊥ ∧ IsClosed (Set.range T) := by
  rw [← ContinuousLinearMap.hasTransverseLowerBound_iff_isClosed_range]
  constructor
  · rintro ⟨c, hc, h⟩
    refine ⟨LinearMap.ker_eq_bot'.mpr fun x hx => ?_, c, hc, fun x _ => h x⟩
    have h1 := h x
    have hx' : T x = 0 := hx
    rw [hx', norm_zero] at h1
    exact norm_eq_zero.mp (le_antisymm
      (by nlinarith [norm_nonneg x] : ‖x‖ ≤ 0) (norm_nonneg x))
  · rintro ⟨hker, c, hc, h⟩
    refine ⟨c, hc, fun x => h x ?_⟩
    rw [hker, Submodule.bot_orthogonal_eq_top]
    exact Submodule.mem_top

/-- An operator is surjective exactly when its range is closed and its adjoint is injective. -/
theorem surjective_iff_isClosed_range_and_ker_adjoint (T : E →L[ℂ] F) :
    Function.Surjective T
      ↔ IsClosed (Set.range T)
        ∧ LinearMap.ker (ContinuousLinearMap.adjoint T : F →ₗ[ℂ] E) = ⊥ := by
  constructor
  · intro hs
    have hr : LinearMap.range (T : E →ₗ[ℂ] F) = ⊤ := LinearMap.range_eq_top.mpr hs
    refine ⟨?_, ?_⟩
    · rw [Set.range_eq_univ.mpr hs]
      exact isClosed_univ
    · rw [← ContinuousLinearMap.orthogonal_range, hr, Submodule.top_orthogonal_eq_bot]
  · rintro ⟨hcl, hker⟩
    rw [← ContinuousLinearMap.orthogonal_range] at hker
    have hclosure : (LinearMap.range (T : E →ₗ[ℂ] F)).topologicalClosure = ⊤ := by
      rw [← Submodule.orthogonal_orthogonal_eq_closure, hker, Submodule.bot_orthogonal_eq_top]
    have hcl' : IsClosed ((LinearMap.range (T : E →ₗ[ℂ] F) : Submodule ℂ F) : Set F) := by
      rw [LinearMap.coe_range, ContinuousLinearMap.coe_coe]
      exact hcl
    rw [IsClosed.submodule_topologicalClosure_eq hcl'] at hclosure
    exact LinearMap.range_eq_top.mp hclosure

/-- A bounded operator is bounded below and surjective exactly when it is bijective. -/
theorem bijective_iff_exists_pos_mul_norm_le_and_surjective (T : E →L[ℂ] F) :
    Function.Bijective T ↔ (∃ c > 0, ∀ x, c * ‖x‖ ≤ ‖T x‖) ∧ Function.Surjective T := by
  constructor
  · rintro ⟨hinj, hsurj⟩
    refine ⟨?_, hsurj⟩
    set e := ContinuousLinearEquiv.ofBijective T (LinearMap.ker_eq_bot.mpr hinj)
      (LinearMap.range_eq_top.mpr hsurj) with he
    refine ⟨(‖(e.symm : F →L[ℂ] E)‖ + 1)⁻¹, by positivity, fun x => ?_⟩
    have hx : x = e.symm (T x) := by
      rw [show T x = e x from rfl, ContinuousLinearEquiv.symm_apply_apply]
    have h1 : ‖x‖ ≤ ‖(e.symm : F →L[ℂ] E)‖ * ‖T x‖ := by
      conv_lhs => rw [hx]
      exact (e.symm : F →L[ℂ] E).le_opNorm (T x)
    have h2 : ‖x‖ ≤ (‖(e.symm : F →L[ℂ] E)‖ + 1) * ‖T x‖ := by
      nlinarith [norm_nonneg (T x)]
    rw [inv_mul_eq_div, div_le_iff₀ (by positivity)]
    linarith
  · rintro ⟨hlow, hsurj⟩
    exact ⟨LinearMap.ker_eq_bot.mp ((exists_pos_mul_norm_le_iff T).mp hlow).1, hsurj⟩

variable {I : Type} [Nonempty I] {H K : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

omit [CompleteSpace H] [CompleteSpace K] in
/-- **Corollary 2.2, infinite repetition of a local kernel.**  Over an infinite orbit with all
amplitudes nonzero, a nonzero local kernel produces an infinite-dimensional global kernel. -/
theorem not_finiteDimensional_ker_weightedInduction [DecidableEq I] [Infinite I] (a : I → ℂ)
    (D : H →L[ℂ] K) (U : I → (H ≃ₗᵢ[ℂ] H)) (V : I → (K ≃ₗᵢ[ℂ] K))
    (hbdd : BddAbove (Set.range fun i => ‖a i‖)) (ha : ∀ i, a i ≠ 0)
    (hker : LinearMap.ker (D : H →ₗ[ℂ] K) ≠ ⊥) :
    ¬ FiniteDimensional ℂ (LinearMap.ker (weightedInduction a D U V hbdd :
      lp (fun _ : I => H) 2 →ₗ[ℂ] lp (fun _ : I => K) 2)) := by
  obtain ⟨x, hx, hx0⟩ := (Submodule.ne_bot_iff _).mp hker
  have hxpos : 0 < ‖x‖ := norm_pos_iff.mpr hx0
  set u : H := ((‖x‖⁻¹ : ℝ) : ℂ) • x with hu
  have hu1 : ‖u‖ = 1 := by
    rw [hu, norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hxpos),
      inv_mul_cancel₀ hxpos.ne']
  have hDu : D u = 0 := by
    have hDx : D x = 0 := hx
    rw [hu, map_smul, hDx, smul_zero]
  rw [ker_weightedInduction a D U V hbdd ha]
  exact not_finiteDimensional_ker_orbitInduction D U V hu1 hDu

omit [CompleteSpace H] [CompleteSpace K] in
theorem finiteDimensional_ker_weightedInduction_iff [DecidableEq I] [Infinite I] (a : I → ℂ)
    (D : H →L[ℂ] K) (U : I → (H ≃ₗᵢ[ℂ] H)) (V : I → (K ≃ₗᵢ[ℂ] K))
    (hbdd : BddAbove (Set.range fun i => ‖a i‖)) (ha : ∀ i, a i ≠ 0) :
    FiniteDimensional ℂ (LinearMap.ker (weightedInduction a D U V hbdd :
      lp (fun _ : I => H) 2 →ₗ[ℂ] lp (fun _ : I => K) 2))
      ↔ LinearMap.ker (D : H →ₗ[ℂ] K) = ⊥ := by
  constructor
  · intro hfin
    by_contra hker
    exact not_finiteDimensional_ker_weightedInduction a D U V hbdd ha hker hfin
  · intro hker
    have hinj : Function.Injective (orbitInduction D U V) :=
      (orbitInduction_injective_iff D U V).mpr (LinearMap.ker_eq_bot.mp hker)
    rw [ker_weightedInduction a D U V hbdd ha,
      show LinearMap.ker (orbitInduction D U V : lp (fun _ : I => H) 2 →ₗ[ℂ]
        lp (fun _ : I => K) 2) = ⊥ from LinearMap.ker_eq_bot.mpr hinj]
    infer_instance

/-- **Corollary 2.2, infinite repetition of a local cokernel.** -/
theorem finiteDimensional_range_orthogonal_weightedInduction_iff [DecidableEq I] [Infinite I]
    (a : I → ℂ) (D : H →L[ℂ] K) (U : I → (H ≃ₗᵢ[ℂ] H)) (V : I → (K ≃ₗᵢ[ℂ] K))
    (hbdd : BddAbove (Set.range fun i => ‖a i‖)) (ha : ∀ i, a i ≠ 0) :
    FiniteDimensional ℂ (LinearMap.range (weightedInduction a D U V hbdd :
      lp (fun _ : I => H) 2 →ₗ[ℂ] lp (fun _ : I => K) 2))ᗮ
      ↔ LinearMap.ker (ContinuousLinearMap.adjoint D : K →ₗ[ℂ] H) = ⊥ := by
  rw [ContinuousLinearMap.orthogonal_range, adjoint_weightedInduction]
  exact finiteDimensional_ker_weightedInduction_iff _ _ V U _ fun i => by
    simpa using ha i

/-- **Corollary 2.2 (1).**  Over an infinite orbit with all amplitudes nonzero, the weighted
induction is upper semi-Fredholm exactly when `D` is bounded below and `α_*(a) > 0`. -/
theorem isUpperSemiFredholm_weightedInduction_iff [DecidableEq I] [Infinite I] (a : I → ℂ)
    (D : H →L[ℂ] K) (U : I → (H ≃ₗᵢ[ℂ] H)) (V : I → (K ≃ₗᵢ[ℂ] K))
    (hbdd : BddAbove (Set.range fun i => ‖a i‖)) (ha : ∀ i, a i ≠ 0) (hD : D ≠ 0) :
    IsUpperSemiFredholm (weightedInduction a D U V hbdd)
      ↔ (∃ c > 0, ∀ x, c * ‖x‖ ≤ ‖D x‖) ∧ 0 < ampGap a := by
  have hne : ∃ i, a i ≠ 0 := let ⟨i⟩ := (inferInstance : Nonempty I); ⟨i, ha i⟩
  rw [IsUpperSemiFredholm, isClosed_range_weightedInduction_iff_ampGap a D U V hbdd hne hD,
    finiteDimensional_ker_weightedInduction_iff a D U V hbdd ha, exists_pos_mul_norm_le_iff]
  tauto

/-- **Corollary 2.2 (2).**  Over an infinite orbit with all amplitudes nonzero, the weighted
induction is lower semi-Fredholm exactly when `D` is surjective and `α_*(a) > 0`. -/
theorem isLowerSemiFredholm_weightedInduction_iff [DecidableEq I] [Infinite I] (a : I → ℂ)
    (D : H →L[ℂ] K) (U : I → (H ≃ₗᵢ[ℂ] H)) (V : I → (K ≃ₗᵢ[ℂ] K))
    (hbdd : BddAbove (Set.range fun i => ‖a i‖)) (ha : ∀ i, a i ≠ 0) (hD : D ≠ 0) :
    IsLowerSemiFredholm (weightedInduction a D U V hbdd)
      ↔ Function.Surjective D ∧ 0 < ampGap a := by
  have hne : ∃ i, a i ≠ 0 := let ⟨i⟩ := (inferInstance : Nonempty I); ⟨i, ha i⟩
  rw [IsLowerSemiFredholm, isClosed_range_weightedInduction_iff_ampGap a D U V hbdd hne hD,
    finiteDimensional_range_orthogonal_weightedInduction_iff a D U V hbdd ha,
    surjective_iff_isClosed_range_and_ker_adjoint]
  tauto

/-- **Corollary 2.2 (3).**  Over an infinite orbit with all amplitudes nonzero, the weighted
induction is Fredholm exactly when `D` is invertible and `α_*(a) > 0`. -/
theorem isBoundedFredholm_weightedInduction_iff [DecidableEq I] [Infinite I] (a : I → ℂ)
    (D : H →L[ℂ] K) (U : I → (H ≃ₗᵢ[ℂ] H)) (V : I → (K ≃ₗᵢ[ℂ] K))
    (hbdd : BddAbove (Set.range fun i => ‖a i‖)) (ha : ∀ i, a i ≠ 0) (hD : D ≠ 0) :
    IsBoundedFredholm (weightedInduction a D U V hbdd)
      ↔ Function.Bijective D ∧ 0 < ampGap a := by
  rw [IsBoundedFredholm, isUpperSemiFredholm_weightedInduction_iff a D U V hbdd ha hD,
    isLowerSemiFredholm_weightedInduction_iff a D U V hbdd ha hD,
    bijective_iff_exists_pos_mul_norm_le_and_surjective]
  tauto

end Fredholm

end

end GaloisForLFunctions.HTGeometry
