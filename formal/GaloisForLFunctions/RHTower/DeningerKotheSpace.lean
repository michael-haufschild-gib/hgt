import GaloisForLFunctions.RHTower.DeningerNuclearTransport

/-!
# Köthe sequence spaces and their weighted `ℓ¹` seminorms

A Köthe datum is an increasing family of positive weights on an index set.  The sequences all of
whose weighted `ℓ¹` sums converge form a vector space, graded by those sums, and the coordinate of
a sequence is controlled by every one of the seminorms.  The standard basis vectors have seminorm
exactly the corresponding weight.

This is the sequence model behind the classical criterion for nuclearity: a Köthe space is nuclear
when each weight is summable against a later one.

* `DeningerKotheData` : an increasing family of positive weights.
* `DeningerKotheCarrier`, `deningerKotheSeminorm` : the space and its seminorms.
* `deningerKotheSeminorm_coord_le`, `deningerKotheSeminorm_delta` : coordinates and basis vectors.
-/

namespace RHTower

section Kothe

variable {𝕜 : Type*} [RCLike 𝕜]

/-- **A Köthe datum**: an increasing family of positive weights on an index set. -/
structure DeningerKotheData (ι : Type) where
  /-- The weights, increasing in the first index. -/
  w : ℕ → ι → ℝ
  /-- Positivity of the weights. -/
  pos : ∀ k i, 0 < w k i
  /-- Monotonicity in the grading. -/
  mono : ∀ k i, w k i ≤ w (k + 1) i

variable {ι : Type} (W : DeningerKotheData ι)

theorem deningerKothe_mono_le (W : DeningerKotheData ι) {k l : ℕ} (h : k ≤ l) (i : ι) :
    W.w k i ≤ W.w l i := by
  induction l with
  | zero =>
      have hk : k = 0 := Nat.le_zero.mp h
      rw [hk]
  | succ l ih =>
      rcases Nat.lt_or_ge k (l + 1) with hlt | hge
      · exact le_trans (ih (Nat.lt_succ_iff.mp hlt)) (W.mono l i)
      · have hkl : k = l + 1 := le_antisymm h hge
        rw [hkl]

/-- **The Köthe space**: the sequences whose weighted `ℓ¹` sums all converge. -/
def DeningerKotheCarrier (𝕜 : Type*) [RCLike 𝕜] {ι : Type} (W : DeningerKotheData ι) :
    Submodule 𝕜 (ι → 𝕜) where
  carrier := {a | ∀ k, Summable fun i => W.w k i * ‖a i‖}
  add_mem' := by
    intro a b ha hb k
    refine Summable.of_nonneg_of_le (fun i => ?_) (fun i => ?_) ((ha k).add (hb k))
    · exact mul_nonneg (W.pos k i).le (norm_nonneg _)
    · calc W.w k i * ‖(a + b) i‖ ≤ W.w k i * (‖a i‖ + ‖b i‖) :=
            mul_le_mul_of_nonneg_left (norm_add_le _ _) (W.pos k i).le
        _ = W.w k i * ‖a i‖ + W.w k i * ‖b i‖ := by ring
  zero_mem' := by
    intro k
    simp
  smul_mem' := by
    intro c a ha k
    have hfun : (fun i => W.w k i * ‖(c • a) i‖) = fun i => ‖c‖ * (W.w k i * ‖a i‖) := by
      funext i
      show W.w k i * ‖c * a i‖ = ‖c‖ * (W.w k i * ‖a i‖)
      rw [norm_mul]
      ring
    rw [hfun]
    exact (ha k).mul_left _

theorem deningerKothe_summable (a : DeningerKotheCarrier 𝕜 W) (k : ℕ) :
    Summable fun i => W.w k i * ‖(a : ι → 𝕜) i‖ := a.2 k

/-- **The `k`-th weighted `ℓ¹` seminorm** of the Köthe space. -/
noncomputable def deningerKotheSeminorm (k : ℕ) : Seminorm 𝕜 (DeningerKotheCarrier 𝕜 W) :=
  Seminorm.ofSMulLE (fun a => ∑' i, W.w k i * ‖(a : ι → 𝕜) i‖)
    (by simp)
    (by
      intro a b
      have hle : ∀ i, W.w k i * ‖((a + b : DeningerKotheCarrier 𝕜 W) : ι → 𝕜) i‖
          ≤ W.w k i * ‖(a : ι → 𝕜) i‖ + W.w k i * ‖(b : ι → 𝕜) i‖ := by
        intro i
        calc W.w k i * ‖((a + b : DeningerKotheCarrier 𝕜 W) : ι → 𝕜) i‖
            ≤ W.w k i * (‖(a : ι → 𝕜) i‖ + ‖(b : ι → 𝕜) i‖) :=
              mul_le_mul_of_nonneg_left (norm_add_le _ _) (W.pos k i).le
          _ = W.w k i * ‖(a : ι → 𝕜) i‖ + W.w k i * ‖(b : ι → 𝕜) i‖ := by ring
      refine le_trans (Summable.tsum_le_tsum hle ?_ ?_) (le_of_eq ?_)
      · exact deningerKothe_summable W (a + b) k
      · exact (deningerKothe_summable W a k).add (deningerKothe_summable W b k)
      · exact (deningerKothe_summable W a k).tsum_add (deningerKothe_summable W b k))
    (by
      intro c a
      have hfun : (fun i => W.w k i * ‖((c • a : DeningerKotheCarrier 𝕜 W) : ι → 𝕜) i‖)
          = fun i => ‖c‖ * (W.w k i * ‖(a : ι → 𝕜) i‖) := by
        funext i
        show W.w k i * ‖c * (a : ι → 𝕜) i‖ = ‖c‖ * (W.w k i * ‖(a : ι → 𝕜) i‖)
        rw [norm_mul]
        ring
      rw [hfun, (deningerKothe_summable W a k).tsum_mul_left])

theorem deningerKotheSeminorm_apply (k : ℕ) (a : DeningerKotheCarrier 𝕜 W) :
    deningerKotheSeminorm W k a = ∑' i, W.w k i * ‖(a : ι → 𝕜) i‖ := rfl

/-- **Every weighted coordinate is bounded by the seminorm.** -/
theorem deningerKotheSeminorm_coord_le (k : ℕ) (a : DeningerKotheCarrier 𝕜 W) (i : ι) :
    W.w k i * ‖(a : ι → 𝕜) i‖ ≤ deningerKotheSeminorm W k a := by
  rw [deningerKotheSeminorm_apply]
  refine (deningerKothe_summable W a k).le_tsum i fun j _ => ?_
  exact mul_nonneg (W.pos k j).le (norm_nonneg _)

/-- **The seminorms increase with the grading.** -/
theorem deningerKotheSeminorm_le {k l : ℕ} (h : k ≤ l) (a : DeningerKotheCarrier 𝕜 W) :
    deningerKotheSeminorm W k a ≤ deningerKotheSeminorm W l a := by
  rw [deningerKotheSeminorm_apply, deningerKotheSeminorm_apply]
  refine Summable.tsum_le_tsum (fun i => ?_) (deningerKothe_summable W a k)
    (deningerKothe_summable W a l)
  exact mul_le_mul_of_nonneg_right (deningerKothe_mono_le W h i) (norm_nonneg _)

/-- The standard basis vector of the Köthe space. -/
noncomputable def deningerKotheDelta [DecidableEq ι] (i : ι) : DeningerKotheCarrier 𝕜 W :=
  ⟨Pi.single i 1, fun k => by
    refine summable_of_ne_finset_zero (s := {i}) fun j hj => ?_
    have hji : j ≠ i := by simpa using hj
    simp [Pi.single_eq_of_ne hji]⟩

@[simp]
theorem deningerKotheDelta_coe [DecidableEq ι] (i : ι) :
    ((deningerKotheDelta (𝕜 := 𝕜) W i : DeningerKotheCarrier 𝕜 W) : ι → 𝕜)
      = Pi.single i 1 := rfl

/-- **The basis vectors have seminorm exactly the weight.** -/
theorem deningerKotheSeminorm_delta [DecidableEq ι] (k : ℕ) (i : ι) :
    deningerKotheSeminorm (𝕜 := 𝕜) W k (deningerKotheDelta W i) = W.w k i := by
  rw [deningerKotheSeminorm_apply]
  have hfun : ∀ j, W.w k j * ‖((deningerKotheDelta (𝕜 := 𝕜) W i :
      DeningerKotheCarrier 𝕜 W) : ι → 𝕜) j‖
      = if j = i then W.w k i else 0 := by
    intro j
    rw [deningerKotheDelta_coe]
    by_cases hj : j = i
    · subst hj
      simp
    · simp [hj]
  rw [tsum_congr hfun, tsum_ite_eq]

/-- The `i`-th coordinate of a Köthe sequence, as a linear functional. -/
def deningerKotheCoeffLinear (i : ι) : DeningerKotheCarrier 𝕜 W →ₗ[𝕜] 𝕜 where
  toFun a := (a : ι → 𝕜) i
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem deningerKotheCoeff_ker (k : ℕ) (i : ι) :
    deningerSeminormKer (deningerKotheSeminorm (𝕜 := 𝕜) W k)
      ≤ LinearMap.ker (deningerKotheCoeffLinear (𝕜 := 𝕜) W i) := by
  intro a ha
  have hzero : deningerKotheSeminorm (𝕜 := 𝕜) W k a = 0 := ha
  have hle := deningerKotheSeminorm_coord_le W k a i
  rw [hzero] at hle
  have hnorm : ‖(a : ι → 𝕜) i‖ = 0 := by
    nlinarith [norm_nonneg ((a : ι → 𝕜) i), W.pos k i]
  exact norm_eq_zero.mp hnorm

/-- **The coordinate functionals of the seminorm quotients**, of norm at most the inverse
weight. -/
noncomputable def deningerKotheCoeff (k : ℕ) (i : ι) :
    DeningerSeminormSpace (deningerKotheSeminorm (𝕜 := 𝕜) W k) →L[𝕜] 𝕜 :=
  LinearMap.mkContinuous
    (Submodule.liftQ (deningerSeminormKer (deningerKotheSeminorm (𝕜 := 𝕜) W k))
      (deningerKotheCoeffLinear W i) (deningerKotheCoeff_ker W k i))
    (W.w k i)⁻¹
    (by
      rintro ⟨a⟩
      show ‖(a : ι → 𝕜) i‖ ≤ (W.w k i)⁻¹ * deningerKotheSeminorm (𝕜 := 𝕜) W k a
      rw [le_inv_mul_iff₀ (W.pos k i)]
      exact deningerKotheSeminorm_coord_le W k a i)

@[simp]
theorem deningerKotheCoeff_mk (k : ℕ) (i : ι) (a : DeningerKotheCarrier 𝕜 W) :
    deningerKotheCoeff (𝕜 := 𝕜) W k i
        (deningerSeminormMk (deningerKotheSeminorm (𝕜 := 𝕜) W k) a)
      = (a : ι → 𝕜) i := rfl

theorem deningerKotheCoeff_norm_le (k : ℕ) (i : ι) :
    ‖deningerKotheCoeff (𝕜 := 𝕜) W k i‖ ≤ (W.w k i)⁻¹ :=
  LinearMap.mkContinuous_norm_le _ (inv_nonneg.mpr (W.pos k i).le) _


/-- **The nuclearity condition for a Köthe datum**: each weight is summable against a later one. -/
def DeningerKotheData.IsNuclear {ι : Type} (W : DeningerKotheData ι) : Prop :=
  ∀ k, ∃ m, k ≤ m ∧ Summable fun i => W.w k i / W.w m i

theorem deningerKothe_partialSum_coord [DecidableEq ι] (a : DeningerKotheCarrier 𝕜 W)
    (S : Finset ι) (j : ι) :
    ((∑ i ∈ S, (a : ι → 𝕜) i • deningerKotheDelta (𝕜 := 𝕜) W i :
        DeningerKotheCarrier 𝕜 W) : ι → 𝕜) j
      = if j ∈ S then (a : ι → 𝕜) j else 0 := by
  classical
  rw [Submodule.coe_sum, Finset.sum_apply]
  by_cases hj : j ∈ S
  · rw [Finset.sum_eq_single j]
    · show ((a : ι → 𝕜) j • (Pi.single j 1 : ι → 𝕜)) j = _
      simp [hj]
    · intro i _ hij
      show ((a : ι → 𝕜) i • (Pi.single i 1 : ι → 𝕜)) j = 0
      simp [Pi.single_eq_of_ne (Ne.symm hij)]
    · intro hns
      exact absurd hj hns
  · rw [Finset.sum_eq_zero, if_neg hj]
    intro i hi
    have hne : j ≠ i := fun h => hj (h ▸ hi)
    show ((a : ι → 𝕜) i • (Pi.single i 1 : ι → 𝕜)) j = 0
    simp [Pi.single_eq_of_ne hne]

/-- **A Köthe sequence is the sum of its coordinates** in every seminorm: the error of a partial
sum is the tail of a convergent series. -/
theorem deningerKothe_hasSum [DecidableEq ι] (k : ℕ) (a : DeningerKotheCarrier 𝕜 W) :
    HasSum (fun i => (a : ι → 𝕜) i •
        deningerSeminormMk (deningerKotheSeminorm (𝕜 := 𝕜) W k) (deningerKotheDelta W i))
      (deningerSeminormMk (deningerKotheSeminorm (𝕜 := 𝕜) W k) a) := by
  classical
  set g : ι → ℝ := fun i => W.w k i * ‖(a : ι → 𝕜) i‖ with hg
  have hgsum : Summable g := deningerKothe_summable W a k
  show Filter.Tendsto (fun S : Finset ι => ∑ i ∈ S, (a : ι → 𝕜) i •
      deningerSeminormMk (deningerKotheSeminorm (𝕜 := 𝕜) W k) (deningerKotheDelta W i))
    Filter.atTop (nhds (deningerSeminormMk (deningerKotheSeminorm (𝕜 := 𝕜) W k) a))
  rw [Metric.tendsto_atTop]
  intro ε hε
  have htail := tendsto_tsum_compl_atTop_zero g
  rw [Metric.tendsto_atTop] at htail
  obtain ⟨S₀, hS₀⟩ := htail ε hε
  refine ⟨S₀, fun S hS => ?_⟩
  have hpart : ∑ i ∈ S, (a : ι → 𝕜) i •
      deningerSeminormMk (deningerKotheSeminorm (𝕜 := 𝕜) W k) (deningerKotheDelta W i)
      = deningerSeminormMk (deningerKotheSeminorm (𝕜 := 𝕜) W k)
        (∑ i ∈ S, (a : ι → 𝕜) i • deningerKotheDelta (𝕜 := 𝕜) W i) := by
    rw [map_sum]
    exact Finset.sum_congr rfl fun i _ => (map_smul _ _ _).symm
  rw [hpart, dist_eq_norm, ← map_sub, deningerSeminormMk_norm, deningerKotheSeminorm_apply]
  have hcoord : ∀ j, W.w k j * ‖(((∑ i ∈ S, (a : ι → 𝕜) i • deningerKotheDelta (𝕜 := 𝕜) W i) - a :
      DeningerKotheCarrier 𝕜 W) : ι → 𝕜) j‖ = ({j | j ∉ S} : Set ι).indicator g j := by
    intro j
    have hval : (((∑ i ∈ S, (a : ι → 𝕜) i • deningerKotheDelta (𝕜 := 𝕜) W i) - a :
        DeningerKotheCarrier 𝕜 W) : ι → 𝕜) j
        = (if j ∈ S then (a : ι → 𝕜) j else 0) - (a : ι → 𝕜) j := by
      rw [Submodule.coe_sub, Pi.sub_apply, deningerKothe_partialSum_coord W a S j]
    rw [hval]
    by_cases hj : j ∈ S
    · simp [hj, Set.indicator_of_notMem]
    · rw [Set.indicator_of_mem (by simpa using hj)]
      simp [hj, hg]
  rw [tsum_congr hcoord, ← tsum_subtype]
  have hnonneg : 0 ≤ ∑' x : {x // x ∉ S}, g x :=
    tsum_nonneg fun x => mul_nonneg (W.pos k x).le (norm_nonneg _)
  have hlt := hS₀ S hS
  rw [Real.dist_eq, sub_zero, abs_of_nonneg hnonneg] at hlt
  exact hlt

/-- **A Köthe space whose weights are summable against later ones is nuclear.**  The comparison
map is the series of rank one maps given by the coordinate functionals and the basis vectors, and
their norms multiply to the summable quotients of weights. -/
theorem deningerKothe_isNuclearSpace [DecidableEq ι] (hW : W.IsNuclear) :
    DeningerIsNuclearSpace (deningerKotheSeminorm (𝕜 := 𝕜) W) := by
  intro k
  obtain ⟨m, hkm, hsum⟩ := hW k
  refine ⟨m, 1, fun a => by rw [one_mul]; exact deningerKotheSeminorm_le W hkm a, ?_⟩
  refine ⟨ι, fun i => deningerKotheCoeff (𝕜 := 𝕜) W m i,
    fun i => deningerSeminormMk (deningerKotheSeminorm (𝕜 := 𝕜) W k) (deningerKotheDelta W i),
    ?_, ?_⟩
  · refine Summable.of_nonneg_of_le (fun i => by positivity) (fun i => ?_) hsum
    rw [deningerSeminormMk_norm, deningerKotheSeminorm_delta]
    calc ‖deningerKotheCoeff (𝕜 := 𝕜) W m i‖ * W.w k i
        ≤ (W.w m i)⁻¹ * W.w k i :=
          mul_le_mul_of_nonneg_right (deningerKotheCoeff_norm_le W m i) (W.pos k i).le
      _ = W.w k i / W.w m i := by
          rw [inv_mul_eq_div, div_eq_div_iff (W.pos m i).ne' (W.pos m i).ne']
  · intro x
    obtain ⟨a, rfl⟩ := deningerSeminormMk_surjective (deningerKotheSeminorm (𝕜 := 𝕜) W m) x
    exact deningerKothe_hasSum W k a

end Kothe

end RHTower
