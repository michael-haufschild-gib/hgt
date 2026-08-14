import GaloisForLFunctions.HTGeometry.EntireTranslation

/-!
# Dense translation invariance forces a constant

An element of the entire fraction field invariant under a dense set of translations is a constant.

Writing the element as `P / Q`, invariance under a translation `t` gives the entire identity
`P(z)·Q(z+t) = P(z+t)·Q(z)`.  Evaluating at a point where `Q` does not vanish shows that
`P - c·Q` vanishes on the translate of that dense set by the point, and a continuous function
vanishing on a dense set vanishes.

This is the deck-closure input of a complex torus `ℂ^n / Λ`: when the accumulated division points
are dense, no position survives the protocol.
-/

open Filter Topology

namespace GaloisForLFunctions.HTGeometry

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]

theorem exists_ne_zero_of_ne_zero {Q : entireSubring V} (hQ : Q ≠ 0) :
    ∃ z : V, (Q : V → ℂ) z ≠ 0 := by
  by_contra hcon
  simp only [not_exists, not_not] at hcon
  exact hQ (Subtype.ext (funext hcon))

/-- **Dense translation invariance forces a constant.** -/
theorem eq_constEntire_of_dense_translation_invariant {S : Set V} (hS : Dense S)
    {x : EntireField V} (hx : ∀ t ∈ S, fieldTranslateEquiv t x = x) :
    ∃ c : ℂ, x = constEntire V c := by
  classical
  obtain ⟨⟨P, Q⟩, hPQ⟩ := IsLocalization.surj (nonZeroDivisors (entireSubring V)) x
  have hQ0 : (Q : entireSubring V) ≠ 0 := nonZeroDivisors.ne_zero Q.2
  have hQmap : algebraMap (entireSubring V) (EntireField V) (Q : entireSubring V) ≠ 0 := by
    intro h
    exact hQ0 (IsFractionRing.injective (entireSubring V) (EntireField V) (by rw [h, map_zero]))
  have hkey : ∀ t ∈ S, (P : entireSubring V) * entireTranslate t (Q : entireSubring V)
      = entireTranslate t P * (Q : entireSubring V) := by
    intro t ht
    refine IsFractionRing.injective (entireSubring V) (EntireField V) ?_
    have h1 := congrArg (fieldTranslateEquiv t) hPQ
    rw [map_mul, hx t ht, fieldTranslateEquiv_algebraMap, fieldTranslateEquiv_algebraMap] at h1
    have h2 : x * algebraMap (entireSubring V) (EntireField V) (Q : entireSubring V)
          * algebraMap (entireSubring V) (EntireField V) (entireTranslate t (Q : entireSubring V))
        = algebraMap (entireSubring V) (EntireField V) (P : entireSubring V)
          * algebraMap (entireSubring V) (EntireField V)
            (entireTranslate t (Q : entireSubring V)) := by
      rw [hPQ]
    have h3 : x * algebraMap (entireSubring V) (EntireField V)
            (entireTranslate t (Q : entireSubring V))
          * algebraMap (entireSubring V) (EntireField V) (Q : entireSubring V)
        = algebraMap (entireSubring V) (EntireField V) (entireTranslate t P)
          * algebraMap (entireSubring V) (EntireField V) (Q : entireSubring V) := by
      rw [h1]
    rw [map_mul, map_mul]
    calc algebraMap (entireSubring V) (EntireField V) (P : entireSubring V)
          * algebraMap (entireSubring V) (EntireField V)
            (entireTranslate t (Q : entireSubring V))
        = x * algebraMap (entireSubring V) (EntireField V) (Q : entireSubring V)
          * algebraMap (entireSubring V) (EntireField V)
            (entireTranslate t (Q : entireSubring V)) := h2.symm
      _ = x * algebraMap (entireSubring V) (EntireField V)
            (entireTranslate t (Q : entireSubring V))
          * algebraMap (entireSubring V) (EntireField V) (Q : entireSubring V) := by ring
      _ = _ := h3
  have hpt : ∀ t ∈ S, ∀ z : V,
      (P : V → ℂ) z * (Q : V → ℂ) (z + t) = (P : V → ℂ) (z + t) * (Q : V → ℂ) z := by
    intro t ht z
    have := congrArg (fun g : entireSubring V => (g : V → ℂ) z) (hkey t ht)
    simpa using this
  obtain ⟨z₀, hz₀⟩ := exists_ne_zero_of_ne_zero hQ0
  refine ⟨(P : V → ℂ) z₀ / (Q : V → ℂ) z₀, ?_⟩
  set c : ℂ := (P : V → ℂ) z₀ / (Q : V → ℂ) z₀ with hc
  have hzero : ∀ t ∈ S, (P : V → ℂ) (z₀ + t) - c * (Q : V → ℂ) (z₀ + t) = 0 := by
    intro t ht
    have h := hpt t ht z₀
    rw [hc, sub_eq_zero, div_mul_eq_mul_div, eq_div_iff hz₀]
    linear_combination h.symm
  have hdense : Dense ((fun t : V => z₀ + t) '' S) := by
    have hmap : Continuous (fun t : V => z₀ + t) := continuous_const.add continuous_id
    have hsub := image_closure_subset_closure_image (f := fun t : V => z₀ + t) hmap (s := S)
    rw [hS.closure_eq, Set.image_univ] at hsub
    intro w
    exact hsub ⟨w - z₀, by simp⟩
  have hcont : Continuous (fun z : V => (P : V → ℂ) z - c * (Q : V → ℂ) z) := by
    have hPc : Continuous (P : V → ℂ) :=
      (differentiable_of_analyticOnNhd P.2).continuous
    have hQc : Continuous (Q : V → ℂ) :=
      (differentiable_of_analyticOnNhd (Q : entireSubring V).2).continuous
    exact hPc.sub (continuous_const.mul hQc)
  have heq : (fun z : V => (P : V → ℂ) z - c * (Q : V → ℂ) z) = fun _ => 0 := by
    refine Continuous.ext_on hdense hcont continuous_const ?_
    rintro w ⟨t, ht, rfl⟩
    exact hzero t ht
  have hPQfun : (P : entireSubring V) = constEntireRing V c * (Q : entireSubring V) := by
    apply Subtype.ext
    funext z
    have hz := congrFun heq z
    show (P : V → ℂ) z = c * (Q : V → ℂ) z
    linear_combination hz
  have hfinal : x * algebraMap (entireSubring V) (EntireField V) (Q : entireSubring V)
      = constEntire V c * algebraMap (entireSubring V) (EntireField V) (Q : entireSubring V) := by
    rw [hPQ, hPQfun, map_mul]
    rfl
  exact mul_right_cancel₀ hQmap hfinal

end GaloisForLFunctions.HTGeometry
