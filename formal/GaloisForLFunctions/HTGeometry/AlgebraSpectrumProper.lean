import GaloisForLFunctions.HTGeometry.AlgebraSpectrumClosed

/-!
# Properness of the projection of the complex-point space

Every element of a finite algebra over `ℂ[X]` is integral, so the Cauchy root bound makes its value
at a complex point bounded in terms of the projection.  Over a compact set of parameters the values
are therefore uniformly bounded, and the preimage sits — closed, by `AlgebraSpectrumClosed` — inside
a product of closed discs, which is compact by Tychonoff.

With the local homeomorphism supplied by the chart this gives the covering property, by
`Bottcher.isCoveringMap_of_isProperMap_of_isLocalHomeomorph`.
-/

namespace GaloisForLFunctions.HTGeometry

open Polynomial

noncomputable section

namespace AlgSpec

variable {B : Type*} [CommRing B] [Algebra ℂ[X] B] [Algebra ℂ B] [IsScalarTower ℂ ℂ[X] B]

/-- A monic relation for `b` bounds the value of `b` at a complex point in terms of its
projection. -/
theorem norm_apply_le_of_monic {b : B} {r : ℂ[X][X]} (hr : r.Monic)
    (hb : Polynomial.aeval b r = 0) (χ : AlgSpec B) :
    ‖χ b‖ ≤ max 1 (∑ i ∈ Finset.range r.natDegree, ‖(r.coeff i).eval (proj B χ)‖) := by
  by_cases hd : r.natDegree = 0
  · exfalso
    have h1 : r = 1 := Polynomial.eq_one_of_monic_natDegree_zero hr hd
    rw [h1, map_one] at hb
    have hc := congrArg (fun x : B => χ x) hb
    simp only [map_one, map_zero] at hc
    exact one_ne_zero hc
  have hroot : (biFibre r (proj B χ)).eval (χ b) = 0 := by
    have h := apply_aeval b r χ
    rw [hb, map_zero] at h
    have h2 : biEval r (proj B χ, χ b) = 0 := h.symm
    rw [biEval_eq_eval_biFibre] at h2
    exact h2
  have h := Bottcher.norm_root_le_of_monic (biFibre_monic hr (proj B χ)) hroot
    (by rw [biFibre_natDegree hr]; exact Nat.pos_of_ne_zero hd)
  rw [biFibre_natDegree hr] at h
  simpa [biFibre_coeff] using h

/-- **The projection of the complex-point space is a proper map.**  Every element of a finite
algebra over `ℂ[X]` is integral, so its values are bounded on the preimage of a compact set; the
preimage therefore sits, closed, inside a product of closed discs. -/
theorem isProperMap_proj [Module.Finite ℂ[X] B] : IsProperMap (proj B) := by
  classical
  rw [isProperMap_iff_isCompact_preimage]
  refine ⟨continuous_proj B, ?_⟩
  intro K hK
  rcases K.eq_empty_or_nonempty with hKe | hKne
  · simp [hKe]
  haveI : Algebra.IsIntegral ℂ[X] B := Algebra.IsIntegral.of_finite ℂ[X] B
  have hint : ∀ b : B, IsIntegral ℂ[X] b := fun b => Algebra.IsIntegral.isIntegral b
  set r : B → ℂ[X][X] := fun b => (hint b).choose with hr
  have hrm : ∀ b, (r b).Monic := fun b => (hint b).choose_spec.1
  have hrz : ∀ b, Polynomial.aeval b (r b) = 0 := fun b => by
    have h := (hint b).choose_spec.2
    simpa [Polynomial.aeval_def] using h
  set F : B → ℂ → ℝ := fun b s =>
    max 1 (∑ i ∈ Finset.range (r b).natDegree, ‖((r b).coeff i).eval s‖) with hF
  have hFcont : ∀ b, Continuous (F b) := by
    intro b
    refine continuous_const.max ?_
    exact continuous_finsetSum _ fun i _ => ((r b).coeff i).continuous_aeval.norm
  have hmax : ∀ b, ∃ C : ℝ, ∀ s ∈ K, F b s ≤ C := by
    intro b
    obtain ⟨s₀, _, hs₀⟩ := hK.exists_isMaxOn hKne (hFcont b).continuousOn
    exact ⟨F b s₀, fun s hs => hs₀ hs⟩
  set C : B → ℝ := fun b => (hmax b).choose with hC
  have hCspec : ∀ b, ∀ s ∈ K, F b s ≤ C b := fun b => (hmax b).choose_spec
  have himg : (fun χ : AlgSpec B => (χ : B → ℂ)) '' (proj B ⁻¹' K) =
      (Set.range fun χ : AlgSpec B => (χ : B → ℂ)) ∩
        {φ : B → ℂ | φ (algebraMap ℂ[X] B X) ∈ K} := by
    ext φ
    constructor
    · rintro ⟨χ, hχ, rfl⟩
      exact ⟨⟨χ, rfl⟩, hχ⟩
    · rintro ⟨⟨χ, rfl⟩, hmem⟩
      exact ⟨χ, hmem, rfl⟩
  have hclosed : IsClosed ((fun χ : AlgSpec B => (χ : B → ℂ)) '' (proj B ⁻¹' K)) := by
    rw [himg]
    exact isClosed_range_algSpec_coe.inter (hK.isClosed.preimage (continuous_apply _))
  have hsub : (fun χ : AlgSpec B => (χ : B → ℂ)) '' (proj B ⁻¹' K) ⊆
      Set.univ.pi fun b => Metric.closedBall (0 : ℂ) (C b) := by
    rintro _ ⟨χ, hχ, rfl⟩ b _
    rw [Metric.mem_closedBall, dist_zero_right]
    exact (norm_apply_le_of_monic (hrm b) (hrz b) χ).trans (hCspec b _ hχ)
  have hcomp : IsCompact ((fun χ : AlgSpec B => (χ : B → ℂ)) '' (proj B ⁻¹' K)) :=
    (isCompact_univ_pi fun b => isCompact_closedBall (0 : ℂ) (C b)).of_isClosed_subset
      hclosed hsub
  exact isInducing_coe.isCompact_iff.mpr hcomp

end AlgSpec

end

end GaloisForLFunctions.HTGeometry
