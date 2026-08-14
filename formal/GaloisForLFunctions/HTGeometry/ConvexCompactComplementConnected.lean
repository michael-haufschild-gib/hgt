import GaloisForLFunctions.HTGeometry.ConvexCarrierCauchyVanishing

/-!
# The complement of a compact convex plane set is preconnected

Polar coordinates present the exterior of a disc as the continuous image of a product of intervals,
so it is preconnected.  Every point outside a compact convex set admits a far centre, and the ray
from that point away from the centre stays outside the set and escapes to infinity; joining each
such ray to the exterior of a fixed disc containing the set exhibits the complement as a union of
preconnected sets through a common point.

* `GaloisForLFunctions.HTGeometry.isPreconnected_norm_gt`;
* `GaloisForLFunctions.HTGeometry.isPreconnected_compl_of_convex_compact`.
-/

noncomputable section

open Complex Set

namespace GaloisForLFunctions.HTGeometry

/-- **The exterior of a disc centred at the origin is preconnected.** -/
theorem isPreconnected_norm_gt {R : ℝ} (hR : 0 ≤ R) : IsPreconnected {z : ℂ | R < ‖z‖} := by
  have hcont : Continuous fun p : ℝ × ℝ => ((p.1 : ℂ) * Complex.exp ((p.2 : ℂ) * Complex.I)) := by
    fun_prop
  have hset : {z : ℂ | R < ‖z‖}
      = (fun p : ℝ × ℝ => ((p.1 : ℂ) * Complex.exp ((p.2 : ℂ) * Complex.I))) ''
        (Set.Ioi R ×ˢ (Set.univ : Set ℝ)) := by
    ext z
    constructor
    · intro hz
      refine ⟨(‖z‖, z.arg), ⟨hz, Set.mem_univ _⟩, ?_⟩
      exact Complex.norm_mul_exp_arg_mul_I z
    · rintro ⟨⟨r, θ⟩, ⟨hr, -⟩, rfl⟩
      have hexp : ‖Complex.exp ((θ : ℂ) * Complex.I)‖ = 1 := by
        rw [Complex.norm_exp]
        simp
      have hrpos : R < r := hr
      rw [Set.mem_setOf_eq, norm_mul, hexp, mul_one, Complex.norm_real,
        Real.norm_of_nonneg (le_trans hR hrpos.le)]
      exact hrpos
  rw [hset]
  exact (isPreconnected_Ioi.prod isPreconnected_univ).image _ hcont.continuousOn

/-- **The complement of a compact convex plane set is preconnected.** -/
theorem isPreconnected_compl_of_convex_compact {K : Set ℂ} (hK : IsCompact K)
    (hconv : Convex ℝ K) : IsPreconnected Kᶜ := by
  obtain ⟨R₀, hR₀⟩ := hK.isBounded.subset_closedBall (0 : ℂ)
  set R : ℝ := max R₀ 0 with hRdef
  have hR : 0 ≤ R := le_max_right _ _
  have hKR : ∀ z ∈ K, ‖z‖ ≤ R := by
    intro z hz
    have := hR₀ hz
    simp only [Metric.mem_closedBall, dist_zero_right] at this
    exact this.trans (le_max_left _ _)
  set A : Set ℂ := {z : ℂ | R < ‖z‖} with hA
  have hAconn : IsPreconnected A := isPreconnected_norm_gt hR
  have hAK : A ⊆ Kᶜ := fun z hz hc => absurd (hKR z hc) (not_le.mpr hz)
  set x₀ : ℂ := ((R + 1 : ℝ) : ℂ) with hx₀def
  have hx₀ : x₀ ∈ A := by
    rw [hA, Set.mem_setOf_eq, hx₀def, Complex.norm_real, Real.norm_of_nonneg (by linarith)]
    linarith
  refine isPreconnected_of_forall x₀ ?_
  intro y hy
  obtain ⟨c, r, hr, hKr, hyr⟩ := exists_far_center hK hconv hy
  have hycpos : 0 < ‖y - c‖ := lt_of_le_of_lt hr hyr
  set ray : Set ℂ := (fun t : ℝ => c + (t : ℂ) * (y - c)) '' Set.Ici (1 : ℝ) with hray
  have hrayK : ray ⊆ Kᶜ := by
    rintro _ ⟨t, ht, rfl⟩ hcon
    have ht' : (1 : ℝ) ≤ t := ht
    have h1 : ‖c + (t : ℂ) * (y - c) - c‖ ≤ r := hKr _ hcon
    have h2 : c + (t : ℂ) * (y - c) - c = (t : ℂ) * (y - c) := by ring
    rw [h2, norm_mul, Complex.norm_real, Real.norm_of_nonneg (by linarith)] at h1
    have h3 : ‖y - c‖ ≤ t * ‖y - c‖ := by nlinarith
    linarith
  have hrayconn : IsPreconnected ray :=
    isPreconnected_Ici.image _ (by fun_prop : Continuous fun t : ℝ =>
      c + (t : ℂ) * (y - c)).continuousOn
  set t₁ : ℝ := max 1 ((R + ‖c‖ + 1) / ‖y - c‖) with ht₁def
  have ht₁ : (1 : ℝ) ≤ t₁ := le_max_left _ _
  have ht₁A : c + (t₁ : ℂ) * (y - c) ∈ A := by
    have hprod : R + ‖c‖ + 1 ≤ t₁ * ‖y - c‖ := by
      have := le_max_right (1 : ℝ) ((R + ‖c‖ + 1) / ‖y - c‖)
      rw [← ht₁def] at this
      calc R + ‖c‖ + 1 = ((R + ‖c‖ + 1) / ‖y - c‖) * ‖y - c‖ := by field_simp
        _ ≤ t₁ * ‖y - c‖ := mul_le_mul_of_nonneg_right this hycpos.le
    have hnorm : ‖(t₁ : ℂ) * (y - c)‖ = t₁ * ‖y - c‖ := by
      rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (by linarith)]
    have hlow : ‖(t₁ : ℂ) * (y - c)‖ - ‖c‖ ≤ ‖c + (t₁ : ℂ) * (y - c)‖ := by
      have := norm_sub_norm_le ((t₁ : ℂ) * (y - c)) (-c)
      simp only [norm_neg, sub_neg_eq_add] at this
      calc ‖(t₁ : ℂ) * (y - c)‖ - ‖c‖ ≤ ‖(t₁ : ℂ) * (y - c) + c‖ := by
            simpa [add_comm] using this
        _ = ‖c + (t₁ : ℂ) * (y - c)‖ := by rw [add_comm]
    rw [hnorm] at hlow
    rw [hA, Set.mem_setOf_eq]
    linarith
  refine ⟨ray ∪ A, Set.union_subset hrayK hAK, Or.inr hx₀, Or.inl ⟨1, Set.self_mem_Ici, by push_cast; ring⟩,
    ?_⟩
  exact IsPreconnected.union _ (Set.mem_image_of_mem _ (Set.mem_Ici.mpr ht₁)) ht₁A hrayconn hAconn

end GaloisForLFunctions.HTGeometry
