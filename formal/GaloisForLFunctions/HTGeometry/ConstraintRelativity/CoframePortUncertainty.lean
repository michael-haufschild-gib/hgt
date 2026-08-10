import Mathlib

/-!
# The completion-port dichotomy of an infinite coframe

The augmentation of a finitely supported coefficient space has a one-dimensional cokernel.  In any
Hausdorff locally convex dense realization, exactly one of two things happens: the augmentation
extends continuously, in which case the closure of the mean-zero coframe is its kernel and the
boundary port is one-dimensional; or it does not, in which case the mean-zero coframe is dense and
the port is erased.

Consequently a divergent unsigned weight family cannot have a convergent net of partial coframe
vectors in a realization retaining the port.
-/

open Filter Topology Metric

open scoped ENNReal NNReal

namespace HTGeometry.ConstraintRelativity

/-! ## The augmentation and the mean-zero coframe -/

section Augmentation

variable (I : Type*)

/-- **Card `(1)`.**  The total-charge augmentation of a finitely supported coefficient family. -/
noncomputable def augmentation : (I →₀ ℂ) →ₗ[ℂ] ℂ := Finsupp.lsum ℂ fun _ => LinearMap.id

@[simp] theorem augmentation_single (i : I) (c : ℂ) :
    augmentation I (Finsupp.single i c) = c := by
  simp [augmentation]

/-- **Card `(1)`.**  The mean-zero coframe. -/
noncomputable def meanZero : Submodule ℂ (I →₀ ℂ) := LinearMap.ker (augmentation I)

variable {I}

theorem mem_meanZero {x : I →₀ ℂ} : x ∈ meanZero I ↔ augmentation I x = 0 := Iff.rfl

theorem augmentation_surjective [Nonempty I] : Function.Surjective (augmentation I) := by
  intro c
  exact ⟨Finsupp.single (Classical.arbitrary I) c, by simp⟩

/-- **Card `(14)`.**  The algebraic port is one-dimensional. -/
noncomputable def portEquiv [Nonempty I] : ((I →₀ ℂ) ⧸ meanZero I) ≃ₗ[ℂ] ℂ :=
  LinearMap.quotKerEquivOfSurjective _ augmentation_surjective

end Augmentation

/-! ## The one-port dichotomy -/

section OnePort

variable {I X : Type*} [AddCommGroup X] [Module ℂ X] [TopologicalSpace X]
  [IsTopologicalAddGroup X] [ContinuousSMul ℂ X]

variable (j : (I →₀ ℂ) →ₗ[ℂ] X)

/-- **Card `(2)`.**  The closure of the realized mean-zero coframe. -/
noncomputable def closedCoframe : Submodule ℂ X :=
  (Submodule.map j (meanZero I)).topologicalClosure

theorem map_meanZero_le_closedCoframe : Submodule.map j (meanZero I) ≤ closedCoframe j := by
  intro y hy
  have hmem : y ∈ closure ((Submodule.map j (meanZero I) : Set X)) := subset_closure hy
  exact hmem

variable {j}

/-- If the augmentation extends continuously, the closed coframe lies in its kernel. -/
theorem closedCoframe_le_ker (ε : X →L[ℂ] ℂ) (hε : ∀ x, ε (j x) = augmentation I x) :
    closedCoframe j ≤ LinearMap.ker (ε : X →ₗ[ℂ] ℂ) := by
  have hle : Submodule.map j (meanZero I) ≤ LinearMap.ker (ε : X →ₗ[ℂ] ℂ) := by
    rintro _ ⟨v, hv, rfl⟩
    show ε (j v) = 0
    rw [hε]
    exact hv
  have hclosed : IsClosed ((LinearMap.ker (ε : X →ₗ[ℂ] ℂ) : Set X)) := by
    have hpre : (LinearMap.ker (ε : X →ₗ[ℂ] ℂ) : Set X) = ε ⁻¹' {0} := rfl
    rw [hpre]
    exact isClosed_singleton.preimage ε.continuous
  exact Submodule.topologicalClosure_minimal _ hle hclosed

/-- If the augmentation extends continuously and the realization is dense, the closed coframe is
exactly its kernel. -/
theorem ker_le_closedCoframe [Nonempty I] (hdense : DenseRange j) (ε : X →L[ℂ] ℂ)
    (hε : ∀ x, ε (j x) = augmentation I x) :
    LinearMap.ker (ε : X →ₗ[ℂ] ℂ) ≤ closedCoframe j := by
  obtain ⟨u, hu⟩ : ∃ u : I →₀ ℂ, augmentation I u = 1 :=
    ⟨Finsupp.single (Classical.arbitrary I) 1, by simp⟩
  set φ : X → X := fun y => y - ε y • j u with hφ
  have hcont : Continuous φ := by
    exact continuous_id.sub ((ε.continuous.smul continuous_const))
  have hsub : φ '' Set.range j ⊆ (Submodule.map j (meanZero I) : Set X) := by
    rintro _ ⟨_, ⟨v, rfl⟩, rfl⟩
    refine ⟨v - augmentation I v • u, ?_, ?_⟩
    · show augmentation I (v - augmentation I v • u) = 0
      rw [map_sub, map_smul, hu, smul_eq_mul, mul_one, sub_self]
    · simp [hφ, hε, map_sub, map_smul]
  intro x hx
  have hxrange : x ∈ closure (Set.range j) := by
    rw [hdense.closure_eq]; trivial
  have himg : φ x ∈ closure ((Submodule.map j (meanZero I) : Set X)) :=
    closure_mono hsub (image_closure_subset_closure_image hcont ⟨x, hxrange, rfl⟩)
  have hxx : φ x = x := by
    have : ε x = 0 := hx
    simp [hφ, this]
  rwa [hxx] at himg

/-- **Card `(3)`.**  With a continuous augmentation the closed coframe is its kernel. -/
theorem closedCoframe_eq_ker [Nonempty I] (hdense : DenseRange j) (ε : X →L[ℂ] ℂ)
    (hε : ∀ x, ε (j x) = augmentation I x) :
    closedCoframe j = LinearMap.ker (ε : X →ₗ[ℂ] ℂ) :=
  le_antisymm (closedCoframe_le_ker ε hε) (ker_le_closedCoframe hdense ε hε)

/-- **Card `(3)`.**  The surviving port is one-dimensional. -/
noncomputable def portQuotientEquiv [Nonempty I] (hdense : DenseRange j) (ε : X →L[ℂ] ℂ)
    (hε : ∀ x, ε (j x) = augmentation I x) (hne : ε ≠ 0) :
    (X ⧸ closedCoframe j) ≃ₗ[ℂ] ℂ := by
  have hsurj : Function.Surjective (ε : X →ₗ[ℂ] ℂ) := by
    obtain ⟨x, hx⟩ : ∃ x, ε x ≠ 0 := by
      by_contra hcon
      refine hne ?_
      ext y
      exact not_not.1 fun h => hcon ⟨y, h⟩
    intro c
    exact ⟨(c / ε x) • x, by simp [map_smul, div_mul_cancel₀ _ hx]⟩
  exact (Submodule.quotEquivOfEq _ _ (closedCoframe_eq_ker hdense ε hε)).trans
    (LinearMap.quotKerEquivOfSurjective _ hsurj)

end OnePort

/-! ## The separation half of the dichotomy -/

section Separation

variable {I X : Type*} [AddCommGroup X] [Module ℂ X] [TopologicalSpace X]
  [IsTopologicalAddGroup X] [ContinuousSMul ℂ X] [Module ℝ X] [IsScalarTower ℝ ℂ X]
  [LocallyConvexSpace ℝ X] [T1Space X] [ContinuousSMul ℝ X]

variable {j : (I →₀ ℂ) →ₗ[ℂ] X}

omit [T1Space X] [ContinuousSMul ℝ X] in
/-- **Card `(4)`, contrapositive.**  If the closed coframe is proper, the augmentation extends to a
nonzero continuous functional. -/
theorem exists_continuous_augmentation [Nonempty I] (hdense : DenseRange j)
    (hproper : closedCoframe j ≠ ⊤) :
    ∃ ε : X →L[ℂ] ℂ, ε ≠ 0 ∧ ∀ x, ε (j x) = augmentation I x := by
  obtain ⟨x₀, hx₀⟩ : ∃ x, x ∉ closedCoframe j := by
    by_contra hcon
    exact hproper (eq_top_iff.2 fun y _ => not_not.1 fun h => hcon ⟨y, h⟩)
  have hconv : Convex ℝ ((closedCoframe j : Set X)) := by
    simpa using (Submodule.restrictScalars ℝ (closedCoframe j)).convex
  obtain ⟨f, c, hfle, hfx⟩ := RCLike.geometric_hahn_banach_closed_point (𝕜 := ℂ)
    hconv (Submodule.isClosed_topologicalClosure (Submodule.map j (meanZero I))) hx₀
  have hvanish : ∀ a ∈ closedCoframe j, f a = 0 := by
    intro a ha
    by_contra hfa
    have hmem : (((c + 1 : ℝ) : ℂ) / f a) • a ∈ closedCoframe j := Submodule.smul_mem _ _ ha
    have := hfle _ hmem
    rw [map_smul, smul_eq_mul, div_mul_cancel₀ _ hfa] at this
    have hlt : c + 1 < c := by simpa using this
    linarith
  obtain ⟨u, hu⟩ : ∃ u : (I →₀ ℂ), augmentation I u = 1 :=
    ⟨Finsupp.single (Classical.arbitrary I) 1, by simp⟩
  have hfj : ∀ v : (I →₀ ℂ), f (j v) = augmentation I v * f (j u) := by
    intro v
    have hmz : v - augmentation I v • u ∈ meanZero I := by
      show augmentation I (v - augmentation I v • u) = 0
      rw [map_sub, map_smul, hu, smul_eq_mul, mul_one, sub_self]
    have h0 : f (j (v - augmentation I v • u)) = 0 :=
      hvanish _ (map_meanZero_le_closedCoframe j ⟨_, hmz, rfl⟩)
    rw [map_sub, map_smul, map_sub, map_smul, smul_eq_mul] at h0
    linear_combination h0
  have hcne : f (j u) ≠ 0 := by
    intro hcon
    have hzero : ∀ y ∈ Set.range j, f y = 0 := by
      rintro _ ⟨v, rfl⟩
      rw [hfj v, hcon, mul_zero]
    have hall : ∀ y : X, f y = 0 := by
      intro y
      have hcl : (Set.range j) ⊆ f ⁻¹' {0} := hzero
      have : y ∈ closure (Set.range j) := by rw [hdense.closure_eq]; trivial
      have hclosed : IsClosed (f ⁻¹' ({0} : Set ℂ)) := isClosed_singleton.preimage f.continuous
      exact hclosed.closure_subset (closure_mono hcl this)
    have h1 : (0:ℝ) < c := by
      have := hfle 0 (Submodule.zero_mem _)
      simpa using this
    have h2 := hfx
    rw [hall x₀] at h2
    simp at h2
    linarith
  refine ⟨(f (j u))⁻¹ • f, ?_, ?_⟩
  · intro hcon
    have := congrArg (fun g : X →L[ℂ] ℂ => g (j u)) hcon
    simp only [smul_apply, smul_eq_mul, zero_apply] at this
    rw [inv_mul_cancel₀ hcne] at this
    exact one_ne_zero this
  · intro v
    simp only [smul_apply, smul_eq_mul]
    rw [hfj v]
    field_simp

omit [T1Space X] [ContinuousSMul ℝ X] in
/-- **Card `(3)`–`(4)`.**  The exact one-port dichotomy. -/
theorem one_port_dichotomy [Nonempty I] (hdense : DenseRange j) :
    (∃ ε : X →L[ℂ] ℂ, ε ≠ 0 ∧ ∀ x, ε (j x) = augmentation I x) ∨ closedCoframe j = ⊤ := by
  by_cases h : closedCoframe j = ⊤
  · exact Or.inr h
  · exact Or.inl (exists_continuous_augmentation hdense h)

end Separation

/-! ## The raw radial drift -/

section RadialDrift

variable {I : Type*}

/-- **Card `(10)`.**  The partial radial vector of a weight family. -/
noncomputable def radialVector (w : I → ℝ) (F : Finset I) : (I →₀ ℂ) :=
  ∑ i ∈ F, Finsupp.single i ((w i : ℝ) : ℂ)

/-- **Card `(11)`.**  Its total charge is the partial sum of the weights. -/
theorem augmentation_radialVector (w : I → ℝ) (F : Finset I) :
    augmentation I (radialVector w F) = ((∑ i ∈ F, w i : ℝ) : ℂ) := by
  simp [radialVector, map_sum]

/-- **Card `(9)`.**  A weight family bounded below by a positive constant on an infinite index set
has unbounded partial charge. -/
theorem not_bddAbove_partialSums [Infinite I] {w : I → ℝ} {c : ℝ} (hc : 0 < c)
    (hw : ∀ i, c ≤ w i) : ¬ BddAbove (Set.range fun F : Finset I => ∑ i ∈ F, w i) := by
  rintro ⟨B, hB⟩
  obtain ⟨n, hn⟩ := exists_nat_gt (B / c)
  obtain ⟨F, hF⟩ := Infinite.exists_subset_card_eq I n
  have h1 : (n : ℝ) * c ≤ ∑ i ∈ F, w i := by
    calc (n : ℝ) * c = ∑ _i ∈ F, c := by rw [Finset.sum_const, hF, nsmul_eq_mul]
      _ ≤ ∑ i ∈ F, w i := Finset.sum_le_sum fun i _ => hw i
  have h2 : ∑ i ∈ F, w i ≤ B := hB ⟨F, rfl⟩
  have h3 : B / c < (n : ℝ) := hn
  rw [div_lt_iff₀ hc] at h3
  linarith

/-- **Card `(12)`.**  The prime logarithms are bounded below by `log 2`. -/
theorem log_prime_ge (p : Nat.Primes) : Real.log 2 ≤ Real.log ((p : ℕ) : ℝ) := by
  refine Real.log_le_log (by norm_num) ?_
  exact_mod_cast p.2.two_le

theorem log_two_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)

/-- **Card `(13)`.**  For nonzero drift the unsigned radial coefficients are bounded below by a
positive constant. -/
theorem radial_coefficient_ge {a : ℝ} (ha : a ≠ 0) (p : Nat.Primes) :
    |1 - (2 : ℝ) ^ (2 * a)| ≤ |1 - (((p : ℕ) : ℝ)) ^ (2 * a)| := by
  have hp2 : (2 : ℝ) ≤ ((p : ℕ) : ℝ) := by exact_mod_cast p.2.two_le
  have hppos : (0 : ℝ) < ((p : ℕ) : ℝ) := by linarith
  rcases lt_or_gt_of_ne ha with hneg | hpos
  · have h2a : 2 * a < 0 := by linarith
    have hmono : (((p : ℕ) : ℝ)) ^ (2 * a) ≤ (2 : ℝ) ^ (2 * a) := by
      have hinv : (2 : ℝ) ^ (-(2 * a)) ≤ (((p : ℕ) : ℝ)) ^ (-(2 * a)) :=
        Real.rpow_le_rpow (by norm_num) hp2 (by linarith)
      have h1 : (0 : ℝ) < (2 : ℝ) ^ (-(2 * a)) := Real.rpow_pos_of_pos (by norm_num) _
      rw [Real.rpow_neg (by norm_num), Real.rpow_neg hppos.le] at hinv
      have h2 : (0 : ℝ) < (((p : ℕ) : ℝ)) ^ (2 * a) := Real.rpow_pos_of_pos hppos _
      have h3 : (0 : ℝ) < (2 : ℝ) ^ (2 * a) := Real.rpow_pos_of_pos (by norm_num) _
      rw [inv_le_inv₀ h3 h2] at hinv
      exact hinv
    have hlt : (2 : ℝ) ^ (2 * a) < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) h2a
    rw [abs_of_pos (by linarith), abs_of_pos (by linarith)]
    linarith
  · have h2a : 0 < 2 * a := by linarith
    have hmono : (2 : ℝ) ^ (2 * a) ≤ (((p : ℕ) : ℝ)) ^ (2 * a) :=
      Real.rpow_le_rpow (by norm_num) hp2 h2a.le
    have hgt : 1 < (2 : ℝ) ^ (2 * a) := Real.one_lt_rpow_iff_of_pos (by norm_num) |>.2
      (Or.inl ⟨by norm_num, h2a⟩)
    rw [abs_of_neg (by linarith), abs_of_neg (by linarith)]
    linarith

theorem radial_coefficient_pos {a : ℝ} (ha : a ≠ 0) : 0 < |1 - (2 : ℝ) ^ (2 * a)| := by
  refine abs_pos.2 (sub_ne_zero.2 fun hcon => ?_)
  have h1 : (2 : ℝ) ^ (2 * a) = 1 := hcon.symm
  have h2 : (2 * a) * Real.log 2 = 0 := by
    rw [← Real.log_rpow (by norm_num : (0:ℝ) < 2), h1, Real.log_one]
  have h3 : 2 * a = 0 := by
    rcases mul_eq_zero.1 h2 with h | h
    · exact h
    · exact absurd h (Real.log_pos (by norm_num)).ne'
  exact ha (by linarith)

end RadialDrift

/-! ## Theorem 3: no convergent raw radial net with a surviving port -/

section RadialNoGo

variable {I X : Type*} [AddCommGroup X] [Module ℂ X] [TopologicalSpace X]
  [IsTopologicalAddGroup X] [ContinuousSMul ℂ X] [Module ℝ X] [IsScalarTower ℝ ℂ X]
  [LocallyConvexSpace ℝ X] [T1Space X] [ContinuousSMul ℝ X]

variable {j : (I →₀ ℂ) →ₗ[ℂ] X}

omit [T1Space X] [ContinuousSMul ℝ X] in
/-- **Theorem 3.**  A Hausdorff locally convex dense realization cannot both retain the port and
carry a convergent net of raw radial vectors of a divergent unsigned weight family. -/
theorem no_convergent_radial_net [Nonempty I] (hdense : DenseRange j)
    (hproper : closedCoframe j ≠ ⊤) {w : I → ℝ} (hw : ∀ i, 0 ≤ w i)
    (hdiv : ¬ BddAbove (Set.range fun F : Finset I => ∑ i ∈ F, w i))
    (L : X) (hconv : Filter.Tendsto (fun F : Finset I => j (radialVector w F)) Filter.atTop
      (nhds L)) : False := by
  classical
  obtain ⟨ε, _, hε⟩ := exists_continuous_augmentation hdense hproper
  have h1 : Filter.Tendsto (fun F : Finset I => ε (j (radialVector w F))) Filter.atTop
      (nhds (ε L)) := (ε.continuous.tendsto L).comp hconv
  have h2 : ∀ F : Finset I, ε (j (radialVector w F)) = ((∑ i ∈ F, w i : ℝ) : ℂ) := by
    intro F
    rw [hε]
    exact augmentation_radialVector w F
  simp only [h2] at h1
  have h3 : Filter.Tendsto (fun F : Finset I => (∑ i ∈ F, w i : ℝ)) Filter.atTop
      (nhds (ε L).re) := by
    have := (Complex.continuous_re.tendsto (ε L)).comp h1
    simpa [Function.comp_def] using this
  have h4 : ∀ᶠ F : Finset I in Filter.atTop,
      (∑ i ∈ F, w i) ∈ Metric.ball ((ε L).re) 1 := h3 (Metric.ball_mem_nhds ((ε L).re) one_pos)
  obtain ⟨F₀, hF₀⟩ := Filter.eventually_atTop.1 h4
  refine hdiv ⟨(ε L).re + 1, ?_⟩
  rintro _ ⟨F, rfl⟩
  have hsub : ∑ i ∈ F, w i ≤ ∑ i ∈ F ∪ F₀, w i :=
    Finset.sum_le_sum_of_subset_of_nonneg Finset.subset_union_left fun i _ _ => hw i
  have hmem := hF₀ (F ∪ F₀) Finset.subset_union_right
  have : |∑ i ∈ F ∪ F₀, w i - (ε L).re| < 1 := by
    simpa [Real.dist_eq] using hmem
  have := abs_lt.1 this
  linarith [this.2]

end RadialNoGo

/-! ## The `ℓ^p` realizations -/

section LpRealization

variable {I : Type*} [DecidableEq I]

/-- `lp.single` as a linear map. -/
noncomputable def lpSingleLM (p : ℝ≥0∞) (i : I) : ℂ →ₗ[ℂ] lp (fun _ : I => ℂ) p where
  toFun := lp.single (E := fun _ : I => ℂ) p i
  map_add' a b := by
    ext k
    by_cases hk : k = i
    · subst hk; simp
    · simp [lp.single_apply, hk]
  map_smul' c a := by
    ext k
    by_cases hk : k = i
    · subst hk; simp
    · simp [lp.single_apply, hk]

/-- **Card `(2)`.**  The canonical realization of the finitely supported coefficients inside
`ℓ^p`. -/
noncomputable def jLp (p : ℝ≥0∞) : (I →₀ ℂ) →ₗ[ℂ] lp (fun _ : I => ℂ) p :=
  Finsupp.lsum ℂ fun i => lpSingleLM p i

@[simp] theorem jLp_single (p : ℝ≥0∞) (i : I) (c : ℂ) :
    jLp p (Finsupp.single i c) = lp.single p i c := by
  simp [jLp, lpSingleLM]

/-- The norm of a uniform finite block in `ℓ^p`. -/
theorem norm_block {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : 0 < p.toReal) (s : Finset I) :
    ‖∑ k ∈ s, lp.single p k (1 : ℂ)‖ = (s.card : ℝ) ^ (1 / p.toReal) := by
  have hsum := lp.norm_sum_single (E := fun _ : I => ℂ) hp (fun _ => (1 : ℂ)) s
  simp only [norm_one, Real.one_rpow, Finset.sum_const, nsmul_eq_mul, mul_one] at hsum
  have hnn : (0 : ℝ) ≤ ‖∑ k ∈ s, lp.single (E := fun _ : I => ℂ) p k (1 : ℂ)‖ :=
    norm_nonneg (∑ k ∈ s, lp.single (E := fun _ : I => ℂ) p k (1 : ℂ))
  calc ‖∑ k ∈ s, lp.single p k (1 : ℂ)‖
      = (‖∑ k ∈ s, lp.single p k (1 : ℂ)‖ ^ p.toReal) ^ (p.toReal)⁻¹ :=
        (Real.rpow_rpow_inv hnn hp.ne').symm
    _ = (s.card : ℝ) ^ (1 / p.toReal) := by rw [hsum, one_div]

/-- **Card `(7)`.**  The uniform mean-zero witness attached to a basis vector. -/
noncomputable def uniformWitness (i : I) (s : Finset I) : (I →₀ ℂ) :=
  Finsupp.single i 1 - ((s.card : ℂ))⁻¹ • ∑ k ∈ s, Finsupp.single k (1 : ℂ)

omit [DecidableEq I] in
theorem uniformWitness_mem_meanZero (i : I) {s : Finset I} (hs : s.Nonempty) :
    uniformWitness i s ∈ meanZero I := by
  have hcard : ((s.card : ℂ)) ≠ 0 := by
    exact_mod_cast (Finset.card_pos.2 hs).ne'
  show augmentation I (uniformWitness i s) = 0
  simp only [uniformWitness, map_sub, map_smul, map_sum, augmentation_single, Finset.sum_const,
    nsmul_eq_mul, mul_one, smul_eq_mul]
  field_simp
  ring


/-- **Card `(8)`.**  The distance from a basis vector to its uniform witness. -/
theorem norm_basis_sub_witness {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : 0 < p.toReal) (i : I)
    (s : Finset I) :
    ‖jLp p (Finsupp.single i 1) - jLp p (uniformWitness i s)‖
      = ((s.card : ℝ))⁻¹ * (s.card : ℝ) ^ (1 / p.toReal) := by
  have hdiff : jLp p (Finsupp.single i 1) - jLp p (uniformWitness i s)
      = ((s.card : ℂ))⁻¹ • ∑ k ∈ s, lp.single p k (1 : ℂ) := by
    rw [uniformWitness, map_sub, map_smul, map_sum]
    simp only [jLp_single]
    abel
  rw [hdiff, norm_smul, norm_block hp, norm_inv, Complex.norm_natCast]

/-- **Card `(15)`.**  For `p > 1` every basis vector lies in the closure of the realized mean-zero
coframe: the algebraic port is nonseparated. -/
theorem basis_mem_closedCoframe [Infinite I] {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : 1 < p.toReal)
    (i : I) :
    jLp p (Finsupp.single i 1) ∈ closedCoframe (jLp p) := by
  have hp0 : 0 < p.toReal := lt_trans one_pos hp
  show jLp p (Finsupp.single i 1)
    ∈ closure ((Submodule.map (jLp p) (meanZero I) : Set (lp (fun _ : I => ℂ) p)))
  rw [Metric.mem_closure_iff]
  intro δ hδ
  set t : ℝ := 1 - 1 / p.toReal with ht
  have htpos : 0 < t := by
    have h1 : 1 / p.toReal < 1 := by rw [div_lt_one hp0]; exact hp
    simp only [ht]
    linarith
  obtain ⟨N, hN⟩ := exists_nat_gt (max 1 ((1 / δ) ^ (1 / t)))
  have hN1 : (1 : ℝ) < N := lt_of_le_of_lt (le_max_left _ _) hN
  have hN2 : ((1 / δ) ^ (1 / t) : ℝ) < N := lt_of_le_of_lt (le_max_right _ _) hN
  have hNpos : (0 : ℝ) < N := by linarith
  have hkey : 1 / δ < (N : ℝ) ^ t := by
    have h1 : (((1 / δ) ^ (1 / t)) : ℝ) ^ t < (N : ℝ) ^ t :=
      Real.rpow_lt_rpow (by positivity) hN2 htpos
    rwa [← Real.rpow_mul (by positivity), one_div_mul_cancel htpos.ne', Real.rpow_one] at h1
  obtain ⟨s, hs⟩ := Infinite.exists_subset_card_eq I N
  have hsne : s.Nonempty := by
    rw [← Finset.card_pos, hs]
    by_contra hcon
    have : (N : ℝ) ≤ 0 := by
      have hN0 : N = 0 := by omega
      simp [hN0]
    linarith
  refine ⟨jLp p (uniformWitness i s), ⟨uniformWitness i s,
    uniformWitness_mem_meanZero i hsne, rfl⟩, ?_⟩
  rw [dist_eq_norm, norm_basis_sub_witness hp0 i s, hs]
  have hrewrite : ((N : ℝ))⁻¹ * (N : ℝ) ^ (1 / p.toReal) = ((N : ℝ) ^ t)⁻¹ := by
    rw [ht, Real.rpow_sub hNpos, Real.rpow_one]
    field_simp
  rw [hrewrite]
  have hpow : (0 : ℝ) < (N : ℝ) ^ t := Real.rpow_pos_of_pos hNpos t
  rw [inv_lt_comm₀ hpow hδ]
  simpa [one_div] using hkey

/-- **Card `(6)`.**  For `p > 1` the mean-zero coframe is dense: the port is erased. -/
theorem closedCoframe_lp_eq_top [Infinite I] {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : 1 < p.toReal)
    (hdense : DenseRange (jLp (I := I) p)) : closedCoframe (jLp (I := I) p) = ⊤ := by
  have hbasis : ∀ x : (I →₀ ℂ), jLp p x ∈ closedCoframe (jLp (I := I) p) := by
    intro x
    induction x using Finsupp.induction with
    | zero => simp
    | single_add a b f _ _ ih =>
      rw [map_add]
      refine Submodule.add_mem _ ?_ ih
      have hsm : Finsupp.single a b = b • Finsupp.single a (1 : ℂ) := by
        rw [Finsupp.smul_single, smul_eq_mul, mul_one]
      rw [hsm, map_smul]
      exact Submodule.smul_mem _ _ (basis_mem_closedCoframe hp a)
  refine eq_top_iff.2 fun y _ => ?_
  have hy : y ∈ closure (Set.range (jLp (I := I) p)) := by rw [hdense.closure_eq]; trivial
  have hsub : Set.range (jLp (I := I) p)
      ⊆ ((closedCoframe (jLp (I := I) p) : Set (lp (fun _ : I => ℂ) p))) := by
    rintro _ ⟨x, rfl⟩
    exact hbasis x
  exact (Submodule.isClosed_topologicalClosure _).closure_subset (closure_mono hsub hy)

/-! ### The `ℓ¹` realization retains the port -/

omit [DecidableEq I] in
theorem summable_lp_one (f : lp (fun _ : I => ℂ) 1) : Summable (fun i => f i) := by
  have h := lp.hasSum_norm (E := fun _ : I => ℂ) (p := 1) (by norm_num) f
  simp only [ENNReal.toReal_one, Real.rpow_one] at h
  exact Summable.of_norm ⟨‖f‖, h⟩

omit [DecidableEq I] in
theorem norm_tsum_le_norm_lp_one (f : lp (fun _ : I => ℂ) 1) : ‖∑' i, f i‖ ≤ ‖f‖ := by
  have h := lp.hasSum_norm (E := fun _ : I => ℂ) (p := 1) (by norm_num) f
  simp only [ENNReal.toReal_one, Real.rpow_one] at h
  calc ‖∑' i, f i‖ ≤ ∑' i, ‖f i‖ := norm_tsum_le_tsum_norm ⟨‖f‖, h⟩
    _ = ‖f‖ := h.tsum_eq

/-- **Card `(5)`.**  The augmentation is continuous on `ℓ¹`. -/
noncomputable def ellOneAugmentation : lp (fun _ : I => ℂ) 1 →L[ℂ] ℂ :=
  LinearMap.mkContinuous
    { toFun := fun f => ∑' i, f i
      map_add' := fun f g => by
        rw [← Summable.tsum_add (summable_lp_one f) (summable_lp_one g)]
        exact tsum_congr fun i => by simp
      map_smul' := fun c f => by
        simp only [RingHom.id_apply, smul_eq_mul, ← tsum_mul_left]
        exact tsum_congr fun i => by simp }
    1 fun f => by simp; exact norm_tsum_le_norm_lp_one f

theorem coeFn_jLp (p : ℝ≥0∞) (x : I →₀ ℂ) (k : I) : (jLp p x) k = x k := by
  classical
  have hx : jLp p x = ∑ i ∈ x.support, lp.single p i (x i) := by
    simp [jLp, Finsupp.lsum_apply, Finsupp.sum, lpSingleLM]
  rw [hx]
  simp only [lp.coeFn_sum, Finset.sum_apply, lp.coeFn_single, Finset.sum_pi_single]
  by_cases hk : k ∈ x.support
  · simp [hk]
  · simp [hk, Finsupp.notMem_support_iff.1 hk]

theorem ellOneAugmentation_jLp (x : I →₀ ℂ) :
    ellOneAugmentation (jLp 1 x) = augmentation I x := by
  classical
  have hcoe : ∀ k, (jLp (I := I) 1 x) k = x k := coeFn_jLp 1 x
  have h1 : ellOneAugmentation (jLp (I := I) 1 x) = ∑' k, (jLp (I := I) 1 x) k := rfl
  rw [h1]
  have h2 : ∑' k, (jLp (I := I) 1 x) k = ∑' k, x k := tsum_congr hcoe
  rw [h2, tsum_eq_sum (s := x.support) (fun k hk => Finsupp.notMem_support_iff.1 hk)]
  simp [augmentation, Finsupp.lsum_apply, Finsupp.sum]

end LpRealization

end HTGeometry.ConstraintRelativity
