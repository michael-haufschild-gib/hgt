import GaloisForLFunctions.RHTower.Deninger.DeningerL2Inner

/-!
# Base change for the `L²` inner product

The inner product of two algebraic numbers, computed in an extension, is `[L : K]` times its value
in the base field.  The finite part uses the same support-and-fibration argument as the norm, with
one difference: the summand involves two elements, so its support sits in the union of their
multiplicative supports rather than in a single one.

* `deningerL2InnerFinsumBaseChange` : base change for the finite part.
* `deningerArchPlaceSum_baseChange₂` : the two-variable archimedean base-change law.
* `deningerL2Inner_baseChange` : base change for the inner product.
* `deningerNormalizedL2Inner_baseChange` : independence of the field of definition.
-/

namespace RHTower

open NumberField Module

section InnerBaseChange

variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

private theorem deningerInnerPow_ne_one {t : ℝ} (ht : 0 < t) (ht1 : t ≠ 1) {n : ℕ} (hn : n ≠ 0) :
    t ^ n ≠ 1 := by
  intro h
  have hlog : (n : ℝ) * Real.log t = 0 := by rw [← Real.log_pow, h, Real.log_one]
  have hn' : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn
  have hzero := (mul_eq_zero.mp hlog).resolve_left hn'
  refine ht1 ?_
  have hexp := congrArg Real.exp hzero
  rwa [Real.exp_log ht, Real.exp_zero] at hexp

/-- **Base change for the finite part of the inner product.** -/
theorem deningerL2InnerFinsumBaseChange {x y : K} (hx : x ≠ 0) (hy : y ≠ 0) :
    ∑ᶠ w : FinitePlace L,
        (Real.log (w (algebraMap K L x)) * Real.log (w (algebraMap K L y)))
          / (deningerPlaceDegree w : ℝ)
      = (finrank K L : ℝ)
          * ∑ᶠ v : FinitePlace K,
              (Real.log (v x) * Real.log (v y)) / (deningerPlaceDegree v : ℝ) := by
  classical
  have hxL : algebraMap K L x ≠ 0 := (map_ne_zero (algebraMap K L)).mpr hx
  have hyL : algebraMap K L y ≠ 0 := (map_ne_zero (algebraMap K L)).mpr hy
  set SL : Finset (FinitePlace L) :=
    (FinitePlace.hasFiniteMulSupport hxL).toFinset ∪ (FinitePlace.hasFiniteMulSupport hyL).toFinset
    with hSL
  set SK : Finset (FinitePlace K) :=
    (FinitePlace.hasFiniteMulSupport hx).toFinset ∪ (FinitePlace.hasFiniteMulSupport hy).toFinset
    with hSK
  have hmemSL : ∀ w : FinitePlace L,
      w ∈ SL ↔ (w (algebraMap K L x) ≠ 1 ∨ w (algebraMap K L y) ≠ 1) := by
    intro w
    simp [hSL, Function.mulSupport]
  have hmemSK : ∀ v : FinitePlace K, v ∈ SK ↔ (v x ≠ 1 ∨ v y ≠ 1) := by
    intro v
    simp [hSK, Function.mulSupport]
  have hsubL : Function.support (fun w : FinitePlace L =>
      (Real.log (w (algebraMap K L x)) * Real.log (w (algebraMap K L y)))
        / (deningerPlaceDegree w : ℝ)) ⊆ (SL : Set (FinitePlace L)) := by
    intro w hw
    by_contra hwS
    refine hw ?_
    show (Real.log (w (algebraMap K L x)) * Real.log (w (algebraMap K L y)))
        / (deningerPlaceDegree w : ℝ) = 0
    have hone : w (algebraMap K L x) = 1 := by
      by_contra hne
      exact hwS (Finset.mem_coe.mpr ((hmemSL w).mpr (Or.inl hne)))
    rw [hone, Real.log_one, zero_mul, zero_div]
  have hsubK : Function.support (fun v : FinitePlace K =>
      (Real.log (v x) * Real.log (v y)) / (deningerPlaceDegree v : ℝ))
      ⊆ (SK : Set (FinitePlace K)) := by
    intro v hv
    by_contra hvS
    refine hv ?_
    show (Real.log (v x) * Real.log (v y)) / (deningerPlaceDegree v : ℝ) = 0
    have hone : v x = 1 := by
      by_contra hne
      exact hvS (Finset.mem_coe.mpr ((hmemSK v).mpr (Or.inl hne)))
    rw [hone, Real.log_one, zero_mul, zero_div]
  have hmaps : ∀ w ∈ SL, deningerRestrictPlace (K := K) w ∈ SK := by
    intro w hw
    rcases (hmemSL w).mp hw with h | h
    · refine (hmemSK _).mpr (Or.inl fun hcon => ?_)
      have hval := deningerFinitePlace_apply (K := K) w x
      rw [hcon, one_pow] at hval
      exact h hval
    · refine (hmemSK _).mpr (Or.inr fun hcon => ?_)
      have hval := deningerFinitePlace_apply (K := K) w y
      rw [hcon, one_pow] at hval
      exact h hval
  have hfib : ∀ v ∈ SK, SL.filter (fun w => deningerRestrictPlace (K := K) w = v)
      = deningerPlacesOver (L := L) v := by
    intro v hv
    ext w
    rw [Finset.mem_filter, deningerMem_placesOver]
    refine ⟨fun h => h.2, fun h => ⟨?_, h⟩⟩
    refine (hmemSL w).mpr ?_
    rcases (hmemSK v).mp hv with hvx | hvy
    · refine Or.inl ?_
      have hval := deningerFinitePlace_apply (K := K) w x
      rw [h] at hval
      rw [hval]
      exact deningerInnerPow_ne_one (FinitePlace.pos_iff.mpr hx) hvx
        (deningerLocalDegree_ne_zero (K := K) w)
    · refine Or.inr ?_
      have hval := deningerFinitePlace_apply (K := K) w y
      rw [h] at hval
      rw [hval]
      exact deningerInnerPow_ne_one (FinitePlace.pos_iff.mpr hy) hvy
        (deningerLocalDegree_ne_zero (K := K) w)
  rw [finsum_eq_finsetSum_of_support_subset _ hsubL,
    finsum_eq_finsetSum_of_support_subset _ hsubK,
    ← Finset.sum_fiberwise_of_maps_to hmaps, Finset.mul_sum]
  refine Finset.sum_congr rfl fun v hv => ?_
  rw [hfib v hv, deningerL2FibreSumProd v x y]

/-- Two-variable embedding sums are place sums weighted by multiplicity. -/
theorem deningerEmbeddingSum_eq_placeSum₂ (G : ℝ → ℝ → ℝ) (x y : K) :
    ∑ φ : K →+* ℂ, G ‖φ x‖ ‖φ y‖
      = ∑ w : InfinitePlace K, (w.mult : ℝ) * G (w x) (w y) := by
  classical
  have hmaps : ∀ φ ∈ (Finset.univ : Finset (K →+* ℂ)),
      (InfinitePlace.mk φ) ∈ (Finset.univ : Finset (InfinitePlace K)) :=
    fun _ _ => Finset.mem_univ _
  rw [← Finset.sum_fiberwise_of_maps_to hmaps]
  refine Finset.sum_congr rfl fun w _ => ?_
  have hconst : ∀ φ ∈ Finset.univ.filter (fun φ : K →+* ℂ => InfinitePlace.mk φ = w),
      G ‖φ x‖ ‖φ y‖ = G (w x) (w y) := by
    intro φ hφ
    rw [← (Finset.mem_filter.mp hφ).2]
    rfl
  rw [Finset.sum_congr rfl hconst, Finset.sum_const, InfinitePlace.card_filter_mk_eq,
    nsmul_eq_mul]

/-- **The two-variable archimedean base-change law for embedding sums.** -/
theorem deningerEmbeddingSum_baseChange₂ (G : ℝ → ℝ → ℝ) (x y : K) :
    ∑ ψ : L →+* ℂ, G ‖ψ (algebraMap K L x)‖ ‖ψ (algebraMap K L y)‖
      = (finrank K L : ℝ) * ∑ φ : K →+* ℂ, G ‖φ x‖ ‖φ y‖ := by
  classical
  have hmaps : ∀ ψ ∈ (Finset.univ : Finset (L →+* ℂ)),
      ψ.comp (algebraMap K L) ∈ (Finset.univ : Finset (K →+* ℂ)) := fun _ _ => Finset.mem_univ _
  rw [← Finset.sum_fiberwise_of_maps_to hmaps, Finset.mul_sum]
  refine Finset.sum_congr rfl fun φ _ => ?_
  have hconst : ∀ ψ ∈ Finset.univ.filter (fun ψ : L →+* ℂ => ψ.comp (algebraMap K L) = φ),
      G ‖ψ (algebraMap K L x)‖ ‖ψ (algebraMap K L y)‖ = G ‖φ x‖ ‖φ y‖ := by
    intro ψ hψ
    rw [← (Finset.mem_filter.mp hψ).2]
    rfl
  rw [Finset.sum_congr rfl hconst, Finset.sum_const, deningerEmbeddingFibre_card (L := L) φ,
    nsmul_eq_mul]

/-- **The two-variable archimedean base-change law for place sums.** -/
theorem deningerArchPlaceSum_baseChange₂ (G : ℝ → ℝ → ℝ) (x y : K) :
    ∑ w : InfinitePlace L, (w.mult : ℝ) * G (w (algebraMap K L x)) (w (algebraMap K L y))
      = (finrank K L : ℝ) * ∑ v : InfinitePlace K, (v.mult : ℝ) * G (v x) (v y) := by
  rw [← deningerEmbeddingSum_eq_placeSum₂ G (algebraMap K L x) (algebraMap K L y),
    ← deningerEmbeddingSum_eq_placeSum₂ G x y]
  exact deningerEmbeddingSum_baseChange₂ G x y

/-- **Base change for the `L²` inner product.** -/
theorem deningerL2Inner_baseChange {x y : K} (hx : x ≠ 0) (hy : y ≠ 0) :
    deningerL2Inner (algebraMap K L x) (algebraMap K L y)
      = (finrank K L : ℝ) * deningerL2Inner x y := by
  rw [deningerL2Inner, deningerL2Inner, mul_add,
    ← deningerL2InnerFinsumBaseChange hx hy,
    ← deningerArchPlaceSum_baseChange₂ (fun s t => Real.log s * Real.log t) x y]

/-- **The normalized inner product does not depend on the field of definition.** -/
theorem deningerNormalizedL2Inner_baseChange {x y : K} (hx : x ≠ 0) (hy : y ≠ 0) :
    deningerL2Inner (algebraMap K L x) (algebraMap K L y) / (finrank ℚ L : ℝ)
      = deningerL2Inner x y / (finrank ℚ K : ℝ) := by
  have htower : finrank ℚ L = finrank ℚ K * finrank K L :=
    (Module.finrank_mul_finrank ℚ K L).symm
  have hK : (finrank ℚ K : ℝ) ≠ 0 := by
    have := Module.finrank_pos (R := ℚ) (M := K)
    positivity
  have hKL : (finrank K L : ℝ) ≠ 0 := by
    have := Module.finrank_pos (R := K) (M := L)
    positivity
  rw [deningerL2Inner_baseChange hx hy, htower]
  push_cast
  field_simp

end InnerBaseChange

end RHTower
