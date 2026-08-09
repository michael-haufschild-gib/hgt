import GaloisForLFunctions.RHTower.FiniteSectionDetectorFloor

/-!
# The finite-section dichotomy: interpolate `1/ζ`, or be obstructed

`FiniteSectionDetectorFloor` reduces a floor for a finite section of the Báez-Duarte problem to one
question: is there a detector combination that annihilates the section but still pairs with the target?
This file answers it, and the answer is an interpolation statement about `ζ`.

Sample the strip at points `ρ₁,…,ρ_M` with `½ < Re ρⱼ < 1`.  The pairings of the detectors with the `N`
generators and with the target are finite vectors, and in a finite-dimensional inner product space a span
is closed, so the duality criterion of `DetectorDuality` becomes exact membership
(`mem_span_range_of_forall_inner_eq_zero`).  Unwinding the coordinates gives

**`interpolates_inv_zeta_or_exists_bdDist_floor` — either the section inverts `ζ` at the sample points,
`(∑ᵢ dᵢ(θᵢ^{ρⱼ} − θᵢ))·ζ(ρⱼ) = 1` for all `j`, or some detector combination certifies the floor
`‖∑ⱼ conj(aⱼ)/ρⱼ‖/‖w‖ ≤ d(θ)` with a nonvanishing numerator.**

Nothing is assumed about `ζ`.  The dichotomy contains the classical zero-based obstruction as the
degenerate case: if `ζ` vanishes at one sample point the interpolation equation reads `0 = 1`, so the
second alternative holds (`bdDist_pos_of_zeta_eq_zero_at_sample`).  The general case is an overdetermined
interpolation problem — `M` equations for `N` unknowns — which is why the distances stay positive, and the
rate at which they can decay is exactly the rate at which the Müntz system `θ^s − θ` can invert `ζ` along
the strip.
-/

open MeasureTheory Set Complex Metric Filter Topology
open scoped InnerProductSpace

noncomputable section

namespace RHTower

/-! ## A finite family spans a closed subspace -/

section FiniteDim

variable {𝕜 H : Type*} [RCLike 𝕜] [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]

/-- **For a finite family the duality criterion gives exact membership.**  The span of finitely many
vectors is closed, so a vector orthogonal to everything orthogonal to the family lies in the span itself —
not merely in its closure. -/
theorem mem_span_range_of_forall_inner_eq_zero {I : Type*} [Finite I] (v : I → H) (x : H)
    (h : ∀ w : H, (∀ i, inner 𝕜 (v i) w = 0) → inner 𝕜 x w = 0) :
    x ∈ Submodule.span 𝕜 (Set.range v) := by
  have _hfin : FiniteDimensional 𝕜 (Submodule.span 𝕜 (Set.range v)) :=
    FiniteDimensional.span_of_finite 𝕜 (Set.finite_range v)
  have hmem : x ∈ (Submodule.span 𝕜 (Set.range v)).topologicalClosure := by
    rw [mem_topologicalClosure_span_iff]
    intro w hw
    rw [inner_eq_zero_symm]
    exact h w fun i => by
      rw [inner_eq_zero_symm]
      exact hw (v i) ⟨i, rfl⟩
  have hclosed : IsClosed ((Submodule.span 𝕜 (Set.range v) : Submodule 𝕜 H) : Set H) :=
    Submodule.closed_of_finiteDimensional _
  have hset : x ∈ closure ((Submodule.span 𝕜 (Set.range v) : Submodule 𝕜 H) : Set H) := by
    rw [← Submodule.topologicalClosure_coe]
    exact hmem
  rwa [hclosed.closure_eq] at hset

/-- **The finite dichotomy.**  Either some vector separates the target from the family, or the target is a
finite linear combination of it. -/
theorem exists_separating_or_mem_span_range {I : Type*} [Finite I] (v : I → H) (x : H) :
    (∃ w : H, (∀ i, inner 𝕜 (v i) w = 0) ∧ inner 𝕜 x w ≠ 0)
      ∨ x ∈ Submodule.span 𝕜 (Set.range v) := by
  by_cases h : ∃ w : H, (∀ i, inner 𝕜 (v i) w = 0) ∧ inner 𝕜 x w ≠ 0
  · exact Or.inl h
  · refine Or.inr (mem_span_range_of_forall_inner_eq_zero v x ?_)
    intro w hw
    by_contra hne
    exact h ⟨w, hw, hne⟩

end FiniteDim

/-! ## The sampled pairings -/

/-- The sampled generator row: the conjugated pairings of the `i`-th generator with the detectors at the
sample points. -/
def sampledGenRow {N M : ℕ} (θ : Fin N → ℝ) (ρ : Fin M → ℂ) (i : Fin N) :
    EuclideanSpace ℂ (Fin M) :=
  WithLp.toLp 2 fun j => (starRingEnd ℂ)
    (-(((θ i : ℝ) : ℂ) ^ ρ j - ((θ i : ℝ) : ℂ)) * (riemannZeta (ρ j) / ρ j))

/-- The sampled target row: the conjugated target pairings `conj (1/ρⱼ)`. -/
def sampledTargetVec {M : ℕ} (ρ : Fin M → ℂ) : EuclideanSpace ℂ (Fin M) :=
  WithLp.toLp 2 fun j => (starRingEnd ℂ) (1 / ρ j)

theorem inner_sampledGenRow {N M : ℕ} (θ : Fin N → ℝ) (ρ : Fin M → ℂ) (i : Fin N)
    (b : EuclideanSpace ℂ (Fin M)) :
    inner ℂ (sampledGenRow θ ρ i) b
      = ∑ j, (-(((θ i : ℝ) : ℂ) ^ ρ j - ((θ i : ℝ) : ℂ)) * (riemannZeta (ρ j) / ρ j)) * b.ofLp j := by
  rw [PiLp.inner_apply]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [RCLike.inner_apply']
  simp [sampledGenRow]

theorem inner_sampledTargetVec {M : ℕ} (ρ : Fin M → ℂ) (b : EuclideanSpace ℂ (Fin M)) :
    inner ℂ (sampledTargetVec ρ) b = ∑ j, (1 / ρ j) * b.ofLp j := by
  rw [PiLp.inner_apply]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [RCLike.inner_apply']
  simp [sampledTargetVec]

/-! ## The dichotomy -/

/-- **Either the section inverts `ζ` at the sample points, or the sample points certify a floor.**

The first alternative is an interpolation problem: `M` equations `(∑ᵢ dᵢ(θᵢ^{ρⱼ} − θᵢ))·ζ(ρⱼ) = 1` for `N`
unknowns.  The second gives an explicit detector combination with a nonvanishing target pairing, hence the
quantitative floor of `bdDist_pos_of_detectorCombination`.  No hypothesis on `ζ` is used. -/
theorem interpolates_inv_zeta_or_exists_bdDist_floor {N M : ℕ} (θ : Fin N → ℝ)
    (hθ : ∀ i, 0 < θ i ∧ θ i ≤ 1) (ρ : Fin M → ℂ) (hρ : ∀ j, 1 / 2 < (ρ j).re)
    (hρ1 : ∀ j, (ρ j).re < 1) :
    (∃ d : Fin N → ℂ, ∀ j, (∑ i, d i * (((θ i : ℝ) : ℂ) ^ ρ j - ((θ i : ℝ) : ℂ)))
        * riemannZeta (ρ j) = 1)
      ∨ ∃ a : Fin M → ℂ, (∑ j, (starRingEnd ℂ) (a j) * (1 / ρ j) ≠ 0) ∧
          ‖∑ j, (starRingEnd ℂ) (a j) * (1 / ρ j)‖ / ‖detectorCombination ρ hρ a‖ ≤ bdDist θ := by
  rcases exists_separating_or_mem_span_range (𝕜 := ℂ) (sampledGenRow θ ρ) (sampledTargetVec ρ) with
    ⟨b, hb, hbsep⟩ | hmem
  · -- a separating vector: read it as detector coefficients
    rw [inner_sampledTargetVec ρ b] at hbsep
    have hsep : ∑ j, (starRingEnd ℂ) ((starRingEnd ℂ) (b.ofLp j)) * (1 / ρ j) ≠ 0 := by
      have hcomm : ∑ j, (starRingEnd ℂ) ((starRingEnd ℂ) (b.ofLp j)) * (1 / ρ j)
          = ∑ j, (1 / ρ j) * b.ofLp j := by
        simp only [RCLike.conj_conj]
        exact Finset.sum_congr rfl fun j _ => mul_comm _ _
      rw [hcomm]
      exact hbsep
    have hann : ∀ i, ∑ j, (starRingEnd ℂ) ((starRingEnd ℂ) (b.ofLp j)) *
        (-(((θ i : ℝ) : ℂ) ^ ρ j - ((θ i : ℝ) : ℂ)) * (riemannZeta (ρ j) / ρ j)) = 0 := by
      intro i
      have h := hb i
      rw [inner_sampledGenRow θ ρ i b] at h
      simp only [RCLike.conj_conj]
      calc ∑ j, b.ofLp j *
            (-(((θ i : ℝ) : ℂ) ^ ρ j - ((θ i : ℝ) : ℂ)) * (riemannZeta (ρ j) / ρ j))
          = ∑ j, (-(((θ i : ℝ) : ℂ) ^ ρ j - ((θ i : ℝ) : ℂ)) * (riemannZeta (ρ j) / ρ j))
              * b.ofLp j := Finset.sum_congr rfl fun j _ => mul_comm _ _
        _ = 0 := h
    exact Or.inr ⟨fun j => (starRingEnd ℂ) (b.ofLp j), hsep,
      (bdDist_pos_of_detectorCombination θ hθ ρ hρ hρ1 _ hann hsep).2⟩
  · -- the target row is a combination of the generator rows: read it as interpolation
    refine Or.inl ?_
    obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).1 hmem
    refine ⟨fun i => -(starRingEnd ℂ) (c i), fun j => ?_⟩
    show (∑ i, -(starRingEnd ℂ) (c i) * (((θ i : ℝ) : ℂ) ^ ρ j - ((θ i : ℝ) : ℂ)))
        * riemannZeta (ρ j) = 1
    have hcoord : (starRingEnd ℂ) (1 / ρ j)
        = ∑ i, c i * (starRingEnd ℂ)
            (-(((θ i : ℝ) : ℂ) ^ ρ j - ((θ i : ℝ) : ℂ)) * (riemannZeta (ρ j) / ρ j)) := by
      have h := congrArg (fun x : EuclideanSpace ℂ (Fin M) => x.ofLp j) hc
      simp only [sampledGenRow, sampledTargetVec] at h
      simpa using h.symm
    have hconj : (1 / ρ j)
        = ∑ i, (starRingEnd ℂ) (c i)
            * (-(((θ i : ℝ) : ℂ) ^ ρ j - ((θ i : ℝ) : ℂ)) * (riemannZeta (ρ j) / ρ j)) := by
      have h := congrArg (starRingEnd ℂ) hcoord
      simpa [map_sum, RCLike.conj_conj] using h
    have hρ0 : ρ j ≠ 0 := by
      have hrj := hρ j
      intro h
      rw [h, Complex.zero_re] at hrj
      norm_num at hrj
    have hfactor : ∑ i, (starRingEnd ℂ) (c i)
          * (-(((θ i : ℝ) : ℂ) ^ ρ j - ((θ i : ℝ) : ℂ)) * (riemannZeta (ρ j) / ρ j))
        = (∑ i, -(starRingEnd ℂ) (c i) * (((θ i : ℝ) : ℂ) ^ ρ j - ((θ i : ℝ) : ℂ)))
            * (riemannZeta (ρ j) / ρ j) := by
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl fun i _ => ?_
      ring
    rw [hfactor] at hconj
    set T : ℂ := ∑ i, -(starRingEnd ℂ) (c i) * (((θ i : ℝ) : ℂ) ^ ρ j - ((θ i : ℝ) : ℂ)) with hT
    field_simp at hconj
    linear_combination -hconj

/-- The classical zero-based obstruction, as the degenerate case of the dichotomy: at a sample point where
`ζ` vanishes the interpolation equation reads `0 = 1`, so the second alternative must hold. -/
theorem bdDist_pos_of_zeta_eq_zero_at_sample {N M : ℕ} (θ : Fin N → ℝ)
    (hθ : ∀ i, 0 < θ i ∧ θ i ≤ 1) (ρ : Fin M → ℂ) (hρ : ∀ j, 1 / 2 < (ρ j).re)
    (hρ1 : ∀ j, (ρ j).re < 1) {j₀ : Fin M} (hzero : riemannZeta (ρ j₀) = 0) :
    ∃ a : Fin M → ℂ, (∑ j, (starRingEnd ℂ) (a j) * (1 / ρ j) ≠ 0) ∧
      ‖∑ j, (starRingEnd ℂ) (a j) * (1 / ρ j)‖ / ‖detectorCombination ρ hρ a‖ ≤ bdDist θ := by
  rcases interpolates_inv_zeta_or_exists_bdDist_floor θ hθ ρ hρ hρ1 with ⟨d, hd⟩ | h
  · exact absurd (hd j₀) (by rw [hzero, mul_zero]; exact zero_ne_one)
  · exact h

end RHTower

end
