import GaloisForLFunctions.CompactHyperbolicSurfaces.HorocyclicSlices

/-!
# Cocompact Fuchsian groups acting freely

A subgroup `Γ ≤ SL(2, ℝ)` is *cocompact and free* (`IsCocompactFree`) if only finitely many `γ`
move `i` within any bounded distance, a compact set meets every orbit, and no `γ ≠ 1` fixes a point
of `ℍ`.  For such `Γ`:

* only finitely many `γ` bring one bounded set within distance `R` of another (`finite_near`), so
  `Γ` is countable;
* displacements `d(z, γz)`, `γ ≠ 1`, are bounded below on compact sets (`exists_dist_smul_ge`);
* **orbit counting:** `#{γ : u(z, γw) ≤ U} ≤ C (1 + U)` uniformly in `z, w` (`exists_card_le`):
  the balls `B(γw, ε)` are disjoint, lie in `B(z, R + ε)`, and `μ B(z, r) ≤ 16 (cosh r − 1)`;
* the lexicographically least orbit point in the compact set gives a measurable fundamental
  domain (`exists_isFundamentalDomain`).
-/

open MeasureTheory Set Filter UpperHalfPlane Metric
open scoped ENNReal MatrixGroups Pointwise

namespace GaloisForLFunctions.CompactHyperbolicSurfaces

open GaloisForLFunctions.HTGeometry

noncomputable section

instance : SMulInvariantMeasure SL(2, ℝ) ℍ volume :=
  ⟨fun g _ hs => SMulInvariantMeasure.measure_preimage_smul (g : GL (Fin 2) ℝ) hs⟩

instance (Γ : Subgroup SL(2, ℝ)) : SMulInvariantMeasure Γ ℍ volume :=
  ⟨fun γ _ hs => SMulInvariantMeasure.measure_preimage_smul (γ : SL(2, ℝ)) hs⟩

/-- A cocompact subgroup of `SL(2, ℝ)` acting freely on `ℍ`. -/
structure IsCocompactFree (Γ : Subgroup SL(2, ℝ)) : Prop where
  finite_dist : ∀ R : ℝ, {γ : Γ | dist I ((γ : SL(2, ℝ)) • I) ≤ R}.Finite
  exists_compact : ∃ K : Set ℍ, IsCompact K ∧ ∀ z : ℍ, ∃ γ : Γ, (γ : SL(2, ℝ)) • z ∈ K
  eq_one_of_smul_eq : ∀ (γ : Γ) (z : ℍ), (γ : SL(2, ℝ)) • z = z → γ = 1

namespace IsCocompactFree

variable {Γ : Subgroup SL(2, ℝ)} (hΓ : IsCocompactFree Γ)
include hΓ

/-- Only finitely many `γ` bring a bounded set `A` within distance `R` of a bounded set `B`. -/
theorem finite_near {A B : Set ℍ} (hA : Bornology.IsBounded A) (hB : Bornology.IsBounded B)
    (R : ℝ) : {γ : Γ | ∃ z ∈ A, ∃ w ∈ B, dist z ((γ : SL(2, ℝ)) • w) ≤ R}.Finite := by
  obtain ⟨D₁, hD₁⟩ := hA.subset_closedBall I
  obtain ⟨D₂, hD₂⟩ := hB.subset_closedBall I
  refine (hΓ.finite_dist (D₁ + R + D₂)).subset ?_
  rintro γ ⟨z, hz, w, hw, hzw⟩
  have h1 : dist z I ≤ D₁ := hD₁ hz
  have h2 : dist w I ≤ D₂ := hD₂ hw
  have h3 : dist ((γ : SL(2, ℝ)) • w) ((γ : SL(2, ℝ)) • I) = dist w I := dist_smul _ _ _
  show dist I ((γ : SL(2, ℝ)) • I) ≤ D₁ + R + D₂
  calc dist I ((γ : SL(2, ℝ)) • I) ≤ dist I z + dist z ((γ : SL(2, ℝ)) • w) +
        dist ((γ : SL(2, ℝ)) • w) ((γ : SL(2, ℝ)) • I) := dist_triangle4 _ _ _ _
    _ ≤ D₁ + R + D₂ := by rw [h3, dist_comm I z]; linarith

theorem countable : Countable Γ := by
  have h : (univ : Set Γ) = ⋃ n : ℕ, {γ : Γ | dist I ((γ : SL(2, ℝ)) • I) ≤ n} := by
    refine (eq_univ_of_forall fun γ => ?_).symm
    obtain ⟨n, hn⟩ := exists_nat_ge (dist I ((γ : SL(2, ℝ)) • I))
    exact mem_iUnion.mpr ⟨n, hn⟩
  have : (univ : Set Γ).Countable := by
    rw [h]; exact countable_iUnion fun n => (hΓ.finite_dist n).countable
  exact countable_univ_iff.mp this

/-- A single `γ ≠ 1` moves the points of a compact set by a uniformly positive amount. -/
theorem exists_dist_smul_ge_of_ne {K : Set ℍ} (hK : IsCompact K) {γ : Γ} (hγ : γ ≠ 1) :
    ∃ ε > 0, ∀ z ∈ K, ε ≤ dist z ((γ : SL(2, ℝ)) • z) := by
  rcases K.eq_empty_or_nonempty with hKe | hKne
  · exact ⟨1, one_pos, fun z hz => by simp [hKe] at hz⟩
  have hc : Continuous fun z : ℍ => dist z ((γ : SL(2, ℝ)) • z) :=
    continuous_id.dist (continuous_const_smul _)
  obtain ⟨z₀, hz₀, hmin⟩ := hK.exists_isMinOn hKne hc.continuousOn
  refine ⟨dist z₀ ((γ : SL(2, ℝ)) • z₀), dist_pos.mpr fun h => hγ ?_, fun z hz => hmin hz⟩
  exact hΓ.eq_one_of_smul_eq γ z₀ h.symm

/-- **Displacement bound.**  On a compact set, every `γ ≠ 1` moves points by at least `ε > 0`. -/
theorem exists_dist_smul_ge {K : Set ℍ} (hK : IsCompact K) :
    ∃ ε > 0, ε ≤ 1 ∧ ∀ z ∈ K, ∀ γ : Γ, γ ≠ 1 → ε ≤ dist z ((γ : SL(2, ℝ)) • z) := by
  have hS := hΓ.finite_near hK.isBounded hK.isBounded 1
  have key : ∀ T : Finset Γ, (∀ γ ∈ T, γ ≠ 1) →
      ∃ ε > 0, ∀ γ ∈ T, ∀ z ∈ K, ε ≤ dist z ((γ : SL(2, ℝ)) • z) := by
    intro T
    induction T using Finset.induction_on with
    | empty => exact fun _ => ⟨1, one_pos, by simp⟩
    | insert γ₀ T _ ih =>
      intro hT
      obtain ⟨ε₁, hε₁, h₁⟩ := ih fun γ hγ => hT γ (Finset.mem_insert_of_mem hγ)
      obtain ⟨ε₀, hε₀, h₀⟩ := hΓ.exists_dist_smul_ge_of_ne hK (hT γ₀ (Finset.mem_insert_self _ _))
      refine ⟨min ε₀ ε₁, lt_min hε₀ hε₁, fun γ hγ z hz => ?_⟩
      rcases Finset.mem_insert.mp hγ with rfl | hγ'
      · exact (min_le_left _ _).trans (h₀ z hz)
      · exact (min_le_right _ _).trans (h₁ γ hγ' z hz)
  obtain ⟨ε, hε, hεT⟩ := key (hS.toFinset.filter (· ≠ 1)) fun γ hγ => (Finset.mem_filter.mp hγ).2
  refine ⟨min ε 1, lt_min hε one_pos, min_le_right _ _, fun z hz γ hγ => ?_⟩
  by_cases hmem : γ ∈ {γ : Γ | ∃ z ∈ K, ∃ w ∈ K, dist z ((γ : SL(2, ℝ)) • w) ≤ 1}
  · exact (min_le_left _ _).trans
      (hεT γ (Finset.mem_filter.mpr ⟨hS.mem_toFinset.mpr hmem, hγ⟩) z hz)
  · have : 1 < dist z ((γ : SL(2, ℝ)) • z) := by
      by_contra h; exact hmem ⟨z, hz, z, hz, not_lt.mp h⟩
    exact (min_le_right _ _).trans this.le

end IsCocompactFree

/-! ### Volumes of balls -/

/-- `d(z, w) ≤ r` iff `u(z, w) ≤ (cosh r − 1)/2`, for `r ≥ 0`. -/
theorem dist_le_iff_pairU_le {z w : ℍ} {r : ℝ} (hr : 0 ≤ r) :
    dist z w ≤ r ↔ pairU z w ≤ (Real.cosh r - 1) / 2 := by
  rw [pairU_eq_cosh]
  constructor
  · intro h
    have : Real.cosh (dist z w) ≤ Real.cosh r :=
      Real.cosh_le_cosh.mpr (by rw [abs_of_nonneg dist_nonneg, abs_of_nonneg hr]; exact h)
    linarith
  · intro h
    have h' : Real.cosh (dist z w) ≤ Real.cosh r := by linarith
    have := Real.cosh_le_cosh.mp h'
    rwa [abs_of_nonneg dist_nonneg, abs_of_nonneg hr] at this

theorem closedBall_eq_setOf_pairU (z : ℍ) {r : ℝ} (hr : 0 ≤ r) :
    closedBall z r = {w : ℍ | pairU z w ≤ (Real.cosh r - 1) / 2} := by
  ext w
  rw [mem_closedBall, dist_comm, mem_setOf_eq, dist_le_iff_pairU_le hr]

/-- Balls of equal radius have equal measure. -/
theorem volume_closedBall_eq (z : ℍ) (r : ℝ) : volume (closedBall z r) = volume (closedBall I r) := by
  obtain ⟨g, rfl⟩ := MulAction.exists_smul_eq SL(2, ℝ) I z
  have : closedBall (g • I) r = g • closedBall I r := (smul_closedBall g I r).symm
  rw [this, measure_smul]

/-- `μ B(z, r) ≤ 16 (cosh r − 1)`. -/
theorem volume_closedBall_le (z : ℍ) {r : ℝ} (hr : 0 ≤ r) :
    volume (closedBall z r) ≤ ENNReal.ofReal (16 * (Real.cosh r - 1)) := by
  rw [volume_closedBall_eq, closedBall_eq_setOf_pairU I hr]
  have h1 : 0 ≤ (Real.cosh r - 1) / 2 := by have := Real.one_le_cosh r; linarith
  calc volume {w : ℍ | pairU I w ≤ (Real.cosh r - 1) / 2}
      ≤ ENNReal.ofReal (32 * ((Real.cosh r - 1) / 2)) := volume_pairU_I_le h1
    _ = ENNReal.ofReal (16 * (Real.cosh r - 1)) := by congr 1; ring

theorem volume_closedBall_pos (z : ℍ) {r : ℝ} (hr : 0 < r) : 0 < volume (closedBall z r) := by
  rw [volume_closedBall_eq, closedBall_eq_setOf_pairU I hr.le]
  refine volume_pairU_I_pos ?_
  have := Real.one_lt_cosh.mpr hr.ne'
  linarith

theorem volume_closedBall_lt_top (z : ℍ) (r : ℝ) : volume (closedBall z r) < ∞ :=
  (isCompact_closedBall z r).measure_lt_top

namespace IsCocompactFree

variable {Γ : Subgroup SL(2, ℝ)} (hΓ : IsCocompactFree Γ)
include hΓ

/-- **Orbit counting.**  There is `C` with `#{γ : u(z, γw) ≤ U} ≤ C (1 + U)` for all `z, w ∈ ℍ`
and `U ≥ 0`; these sets are finite. -/
theorem exists_card_le : ∃ C : ℝ, 0 ≤ C ∧ ∀ (z w : ℍ) (U : ℝ), 0 ≤ U →
    {γ : Γ | pairU z ((γ : SL(2, ℝ)) • w) ≤ U}.Finite ∧
      ({γ : Γ | pairU z ((γ : SL(2, ℝ)) • w) ≤ U}.ncard : ℝ) ≤ C * (1 + U) := by
  obtain ⟨K, hK, hKcov⟩ := hΓ.exists_compact
  obtain ⟨ε, hε, -, hεK⟩ := hΓ.exists_dist_smul_ge hK
  set ρ := ε / 3 with hρ
  have hρ0 : 0 < ρ := by positivity
  set v := (volume (closedBall I ρ)).toReal with hv
  have hvpos : 0 < v := ENNReal.toReal_pos (volume_closedBall_pos I hρ0).ne'
    (volume_closedBall_lt_top I ρ).ne
  refine ⟨64 * Real.exp ρ / v, by positivity, fun z w U hU => ?_⟩
  set R := Real.arcosh (1 + 2 * U) with hR
  have hR0 : 0 ≤ R := Real.arcosh_nonneg (by linarith)
  have hcoshR : Real.cosh R = 1 + 2 * U := Real.cosh_arcosh (by linarith)
  have hset : ∀ w' : ℍ, {γ : Γ | pairU z ((γ : SL(2, ℝ)) • w') ≤ U} =
      {γ : Γ | dist z ((γ : SL(2, ℝ)) • w') ≤ R} := by
    intro w'; ext γ
    rw [mem_setOf_eq, mem_setOf_eq, dist_le_iff_pairU_le hR0, hcoshR]
    constructor <;> intro h <;> linarith
  -- reduce to `w ∈ K`
  obtain ⟨δ, hδ⟩ := hKcov w
  set w' := (δ : SL(2, ℝ)) • w with hw'
  have himage : {γ : Γ | pairU z ((γ : SL(2, ℝ)) • w) ≤ U} =
      (· * δ) '' {γ : Γ | pairU z ((γ : SL(2, ℝ)) • w') ≤ U} := by
    ext γ
    constructor
    · intro h
      refine ⟨γ * δ⁻¹, ?_, by simp⟩
      show pairU z (((γ * δ⁻¹ : Γ) : SL(2, ℝ)) • w') ≤ U
      rw [hw', Subgroup.coe_mul, mul_smul, Subgroup.coe_inv, inv_smul_smul]
      exact h
    · rintro ⟨γ', hγ', rfl⟩
      show pairU z (((γ' * δ : Γ) : SL(2, ℝ)) • w) ≤ U
      rw [Subgroup.coe_mul, mul_smul]
      exact hγ'
  have hfin : {γ : Γ | pairU z ((γ : SL(2, ℝ)) • w') ≤ U}.Finite := by
    rw [hset]
    refine (hΓ.finite_near (isBounded_singleton (x := z)) (isBounded_singleton (x := w')) R).subset ?_
    intro γ hγ
    exact ⟨z, rfl, w', rfl, hγ⟩
  rw [himage]
  refine ⟨hfin.image _, ?_⟩
  rw [ncard_image_of_injective _ (mul_left_injective δ)]
  -- disjoint balls around the orbit points
  set S := hfin.toFinset
  have hdisj : (S : Set Γ).PairwiseDisjoint fun γ => closedBall ((γ : SL(2, ℝ)) • w') ρ := by
    intro γ₁ _ γ₂ _ hne
    refine Set.disjoint_left.mpr fun ξ h₁ h₂ => ?_
    have hne' : γ₁⁻¹ * γ₂ ≠ 1 := fun h => hne (by
      rw [← mul_left_cancel_iff (a := γ₁⁻¹), inv_mul_cancel, h])
    have hlow := hεK w' hδ (γ₁⁻¹ * γ₂) hne'
    have heq : dist w' (((γ₁⁻¹ * γ₂ : Γ) : SL(2, ℝ)) • w') =
        dist ((γ₁ : SL(2, ℝ)) • w') ((γ₂ : SL(2, ℝ)) • w') := by
      rw [← dist_smul (γ₁ : SL(2, ℝ)), Subgroup.coe_mul, mul_smul, Subgroup.coe_inv,
        smul_inv_smul]
    rw [heq] at hlow
    have := dist_triangle_right ((γ₁ : SL(2, ℝ)) • w') ((γ₂ : SL(2, ℝ)) • w') ξ
    rw [mem_closedBall] at h₁ h₂
    linarith
  have hsub : (⋃ γ ∈ S, closedBall ((γ : SL(2, ℝ)) • w') ρ) ⊆ closedBall z (R + ρ) := by
    intro ξ hξ
    obtain ⟨γ, hγ, hξγ⟩ := mem_iUnion₂.mp hξ
    have hγ' : dist z ((γ : SL(2, ℝ)) • w') ≤ R := by
      have := hfin.mem_toFinset.mp hγ
      rw [hset] at this; exact this
    rw [mem_closedBall] at hξγ ⊢
    have := dist_triangle ξ ((γ : SL(2, ℝ)) • w') z
    rw [dist_comm ((γ : SL(2, ℝ)) • w') z] at this
    linarith
  have hmeas : volume (⋃ γ ∈ S, closedBall ((γ : SL(2, ℝ)) • w') ρ) =
      ∑ γ ∈ S, volume (closedBall ((γ : SL(2, ℝ)) • w') ρ) :=
    measure_biUnion_finset hdisj fun _ _ => measurableSet_closedBall
  have hball : ∀ γ ∈ S, volume (closedBall ((γ : SL(2, ℝ)) • w') ρ) = volume (closedBall I ρ) :=
    fun γ _ => volume_closedBall_eq _ _
  rw [Finset.sum_congr rfl hball, Finset.sum_const, nsmul_eq_mul] at hmeas
  have hle : (S.card : ℝ≥0∞) * volume (closedBall I ρ) ≤
      ENNReal.ofReal (16 * (Real.cosh (R + ρ) - 1)) :=
    hmeas ▸ (measure_mono hsub).trans (volume_closedBall_le z (by positivity))
  have hle' : (S.card : ℝ) * v ≤ 16 * (Real.cosh (R + ρ) - 1) := by
    have h2 := ENNReal.toReal_mono ENNReal.ofReal_ne_top hle
    rw [ENNReal.toReal_mul, ENNReal.toReal_natCast,
      ENNReal.toReal_ofReal (by have := Real.one_le_cosh (R + ρ); linarith)] at h2
    exact h2
  have hcosh : Real.cosh (R + ρ) ≤ Real.exp ρ * (2 * (1 + 2 * U)) := by
    calc Real.cosh (R + ρ) ≤ Real.exp (R + ρ) := Real.cosh_le_exp_abs.trans
          (by rw [abs_of_nonneg (by positivity)])
      _ = Real.exp ρ * Real.exp R := by rw [Real.exp_add, mul_comm]
      _ ≤ Real.exp ρ * (2 * Real.cosh R) := by
          refine mul_le_mul_of_nonneg_left ?_ (Real.exp_pos _).le
          rw [Real.cosh_eq]; linarith [Real.exp_pos (-R)]
      _ = Real.exp ρ * (2 * (1 + 2 * U)) := by rw [hcoshR]
  have hncard : ({γ : Γ | pairU z ((γ : SL(2, ℝ)) • w') ≤ U}.ncard : ℝ) = S.card := by
    rw [ncard_eq_toFinset_card _ hfin]
  rw [hncard, div_mul_eq_mul_div, le_div_iff₀ hvpos]
  have hexp := Real.exp_pos ρ
  nlinarith

/-! ### A fundamental domain -/

/-- The lexicographic key `(Re z, Im z)`. -/
def lexKey (z : ℍ) : Lex (ℝ × ℝ) := toLex (z.re, z.im)

theorem lexKey_injective : Function.Injective lexKey := by
  intro z w h
  have h' : (z.re, z.im) = (w.re, w.im) := toLex.injective h
  simp only [Prod.mk.injEq] at h'
  exact UpperHalfPlane.ext (Complex.ext h'.1 h'.2)

theorem measurableSet_lexKey_le {f g : ℍ → ℍ} (hf : Continuous f) (hg : Continuous g) :
    MeasurableSet {z : ℍ | lexKey (f z) ≤ lexKey (g z)} := by
  have h : {z : ℍ | lexKey (f z) ≤ lexKey (g z)} =
      {z | (f z).re < (g z).re} ∪ ({z | (f z).re = (g z).re} ∩ {z | (f z).im ≤ (g z).im}) := by
    ext z
    simp only [lexKey, mem_setOf_eq, mem_union, mem_inter_iff, Prod.Lex.toLex_le_toLex]
  have hre : ∀ {h : ℍ → ℍ}, Continuous h → Measurable fun z => (h z).re :=
    fun hh => (continuous_re.comp hh).measurable
  have him : ∀ {h : ℍ → ℍ}, Continuous h → Measurable fun z => (h z).im :=
    fun hh => (continuous_im.comp hh).measurable
  rw [h]
  exact (measurableSet_lt (hre hf) (hre hg)).union
    ((measurableSet_eq_fun (hre hf) (hre hg)).inter (measurableSet_le (him hf) (him hg)))

/-- The lexicographically least point of each orbit inside `K`. -/
def lexDomain (Γ : Subgroup SL(2, ℝ)) (K : Set ℍ) : Set ℍ :=
  {z ∈ K | ∀ γ : Γ, (γ : SL(2, ℝ)) • z ∈ K → lexKey z ≤ lexKey ((γ : SL(2, ℝ)) • z)}

theorem lexDomain_subset (Γ : Subgroup SL(2, ℝ)) (K : Set ℍ) : lexDomain Γ K ⊆ K := fun _ h => h.1

/-- **A fundamental domain.**  For a compact `K` meeting every orbit, the lexicographically least
orbit points in `K` form a measurable set meeting each orbit exactly once. -/
theorem existsUnique_smul_mem_lexDomain {K : Set ℍ} (hK : IsCompact K)
    (hKcov : ∀ z : ℍ, ∃ γ : Γ, (γ : SL(2, ℝ)) • z ∈ K) (x : ℍ) :
    ∃! γ : Γ, γ • x ∈ lexDomain Γ K := by
  have hS : {γ : Γ | (γ : SL(2, ℝ)) • x ∈ K}.Finite := by
    refine (hΓ.finite_near hK.isBounded (isBounded_singleton (x := x)) 0).subset ?_
    intro γ hγ
    exact ⟨_, hγ, x, rfl, by simp⟩
  obtain ⟨γ₁, hγ₁⟩ := hKcov x
  have hne : hS.toFinset.Nonempty := ⟨γ₁, hS.mem_toFinset.mpr hγ₁⟩
  obtain ⟨γ₀, hγ₀S, hmin⟩ := hS.toFinset.exists_min_image
    (fun γ : Γ => lexKey ((γ : SL(2, ℝ)) • x)) hne
  have hγ₀K : (γ₀ : SL(2, ℝ)) • x ∈ K := hS.mem_toFinset.mp hγ₀S
  refine ⟨γ₀, ⟨hγ₀K, fun γ hγ => ?_⟩, fun γ' hγ' => ?_⟩
  · have hmem : ((γ * γ₀ : Γ) : SL(2, ℝ)) • x ∈ K := by
      rw [Subgroup.coe_mul, mul_smul]; exact hγ
    have := hmin (γ * γ₀) (hS.mem_toFinset.mpr hmem)
    rwa [Subgroup.coe_mul, mul_smul] at this
  · have hγ'F : (γ' : SL(2, ℝ)) • x ∈ lexDomain Γ K := hγ'
    have hγ₀F : (γ₀ : SL(2, ℝ)) • x ∈ lexDomain Γ K := ⟨hγ₀K, fun γ hγ => by
      have hmem : ((γ * γ₀ : Γ) : SL(2, ℝ)) • x ∈ K := by
        rw [Subgroup.coe_mul, mul_smul]; exact hγ
      have := hmin (γ * γ₀) (hS.mem_toFinset.mpr hmem)
      rwa [Subgroup.coe_mul, mul_smul] at this⟩
    have h1 : lexKey ((γ' : SL(2, ℝ)) • x) ≤ lexKey ((γ₀ : SL(2, ℝ)) • x) := by
      have := hγ'F.2 (γ₀ * γ'⁻¹) (by
        rw [Subgroup.coe_mul, mul_smul, Subgroup.coe_inv, inv_smul_smul]; exact hγ₀K)
      rwa [Subgroup.coe_mul, mul_smul, Subgroup.coe_inv, inv_smul_smul] at this
    have h2 : lexKey ((γ₀ : SL(2, ℝ)) • x) ≤ lexKey ((γ' : SL(2, ℝ)) • x) := by
      have := hγ₀F.2 (γ' * γ₀⁻¹) (by
        rw [Subgroup.coe_mul, mul_smul, Subgroup.coe_inv, inv_smul_smul]; exact hγ'F.1)
      rwa [Subgroup.coe_mul, mul_smul, Subgroup.coe_inv, inv_smul_smul] at this
    have heq : (γ' : SL(2, ℝ)) • x = (γ₀ : SL(2, ℝ)) • x := lexKey_injective (le_antisymm h1 h2)
    have hfix : ((γ' * γ₀⁻¹ : Γ) : SL(2, ℝ)) • ((γ₀ : SL(2, ℝ)) • x) = (γ₀ : SL(2, ℝ)) • x := by
      rw [Subgroup.coe_mul, mul_smul, Subgroup.coe_inv, inv_smul_smul, heq]
    have := hΓ.eq_one_of_smul_eq _ _ hfix
    exact mul_inv_eq_one.mp this

theorem measurableSet_lexDomain {K : Set ℍ} (hK : IsCompact K) :
    MeasurableSet (lexDomain Γ K) := by
  haveI := hΓ.countable
  have h : lexDomain Γ K = K ∩ ⋂ γ : Γ, ({z | (γ : SL(2, ℝ)) • z ∈ K}ᶜ ∪
      {z | lexKey (id z) ≤ lexKey ((γ : SL(2, ℝ)) • z)}) := by
    ext z
    simp only [lexDomain, mem_setOf_eq, mem_inter_iff, mem_iInter, mem_union, mem_compl_iff, id]
    constructor
    · rintro ⟨hz, h⟩; exact ⟨hz, fun γ => (em _).elim (fun h' => Or.inr (h γ h')) Or.inl⟩
    · rintro ⟨hz, h⟩; exact ⟨hz, fun γ hγ => (h γ).resolve_left (not_not.mpr hγ)⟩
  rw [h]
  refine hK.isClosed.measurableSet.inter (MeasurableSet.iInter fun γ => ?_)
  exact (hK.isClosed.measurableSet.preimage (continuous_const_smul _).measurable).compl.union
    (measurableSet_lexKey_le continuous_id (continuous_const_smul _))

/-- Every cocompact free group has a measurable fundamental domain inside a compact set. -/
theorem exists_isFundamentalDomain : ∃ F K : Set ℍ, IsCompact K ∧ F ⊆ K ∧ MeasurableSet F ∧
    IsFundamentalDomain Γ F volume := by
  obtain ⟨K, hK, hKcov⟩ := hΓ.exists_compact
  refine ⟨lexDomain Γ K, K, hK, lexDomain_subset Γ K, hΓ.measurableSet_lexDomain hK, ?_⟩
  exact IsFundamentalDomain.mk' (hΓ.measurableSet_lexDomain hK).nullMeasurableSet
    (hΓ.existsUnique_smul_mem_lexDomain hK hKcov)

end IsCocompactFree

end

end GaloisForLFunctions.CompactHyperbolicSurfaces
