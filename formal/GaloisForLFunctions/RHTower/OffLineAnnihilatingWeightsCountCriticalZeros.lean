import GaloisForLFunctions.RHTower.ValueMomentsCannotSeparateReflectedPairs

/-!
# Weights vanishing at the off-line zeros count critical zeros

Let the weight depend linearly on a coefficient vector `x`, `a_x(ρ) = ⟪u_ρ, x⟫`. For
`a_x = ζ' M_x` with a mollifier `M_x` of coefficients `x`, `u_ρ = 0` exactly at multiple zeros.
Each `x` gives a `ZeroValueConfig` (`ofFunctionals`). By mimicry, value moments alone cannot
certify criticality. Removing the off-line pairs costs dimension instead:

* The weights vanishing at both members of all `p` reflected pairs form a subspace `W` of
  codimension at most `2p` (`finrank_le_finrank_offLineAnnihilator_add`).
* On `W` every moment `Σ_ρ F(a(ρ), a(1 − ρ))` with `F(0, 0) = 0` equals the moment of the
  critical zeros alone (`moment_ofFunctionals_eq_critPart`). In particular `S₁ = Σ_crit a(ρ)` and
  `S₂ = Σ_crit |a(ρ)|²`.
* **Robust Conrey–Ghosh–Gonek.** For `x ∈ W`,
  `|S₁(x)|² ≤ #{critical ρ : u_ρ ≠ 0} · Re S₂(x)`
  (`norm_firstMoment_sq_le_card_simple_crit`). That is Cauchy–Schwarz over the simple critical
  zeros.
-/

open Finset InnerProductSpace

noncomputable section

namespace RHTower

namespace ZeroValueConfig

variable {ι κ : Type*}

/-- Cauchy–Schwarz over the support: `|Σ_{i∈s} zᵢ|² ≤ #{i ∈ s : zᵢ ≠ 0} · Σ_{i∈s} |zᵢ|²`. -/
theorem norm_sum_sq_le_card_support_mul (s : Finset ι) (z : ι → ℂ) :
    ‖∑ i ∈ s, z i‖ ^ 2 ≤ #(s.filter fun i => z i ≠ 0) * ∑ i ∈ s, ‖z i‖ ^ 2 := by
  set t := s.filter fun i => z i ≠ 0
  have h1 : ∑ i ∈ s, z i = ∑ i ∈ t, z i := (sum_filter_ne_zero s).symm
  have h2 : ∑ i ∈ s, ‖z i‖ ^ 2 = ∑ i ∈ t, ‖z i‖ ^ 2 := by
    refine (sum_filter_of_ne fun i _ h => ?_).symm
    intro h0
    exact h (by rw [h0, norm_zero]; ring)
  rw [h1, h2]
  calc ‖∑ i ∈ t, z i‖ ^ 2 ≤ (∑ i ∈ t, ‖z i‖) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) (norm_sum_le _ _) 2
    _ ≤ _ := sq_sum_le_card_mul_sum_sq

/-- The critical part of a configuration: the same critical values and no reflected pair. -/
def critPart (C : ZeroValueConfig ι κ) : ZeroValueConfig ι κ := { C with pairs := ∅ }

/-- If both members of every reflected pair carry the value `0`, every moment with
`F(0, 0) = 0` is the moment of the critical part. -/
theorem moment_eq_critPart_moment (C : ZeroValueConfig ι κ) (hl : ∀ j ∈ C.pairs, C.left j = 0)
    (hr : ∀ j ∈ C.pairs, C.right j = 0) (F : ℂ → ℂ → ℂ) (hF : F 0 0 = 0) :
    C.moment F = C.critPart.moment F := by
  have hpairs : ∑ j ∈ C.pairs,
      (F (C.left j) (starRingEnd ℂ (C.right j)) + F (C.right j) (starRingEnd ℂ (C.left j))) = 0 :=
    sum_eq_zero fun j hj => by rw [hl j hj, hr j hj, map_zero, hF, add_zero]
  simp only [moment, critPart, sum_empty, add_zero]
  rw [hpairs, add_zero]

/-- **Robust CGG at the value level.** If both members of every reflected pair carry the value
`0`, then `|S₁|² ≤ #{critical i : a(ρᵢ) ≠ 0} · Re S₂`. -/
theorem norm_firstMoment_sq_le_of_pairs_eq_zero (C : ZeroValueConfig ι κ)
    (hl : ∀ j ∈ C.pairs, C.left j = 0) (hr : ∀ j ∈ C.pairs, C.right j = 0) :
    ‖C.firstMoment‖ ^ 2 ≤ #(C.crit.filter fun i => C.critValue i ≠ 0) * C.secondMoment.re := by
  have hS₁ : C.firstMoment = ∑ i ∈ C.crit, C.critValue i := by
    rw [firstMoment, moment_eq_critPart_moment C hl hr _ rfl]
    simp [moment, critPart]
  have hS₂ : C.secondMoment.re = ∑ i ∈ C.crit, ‖C.critValue i‖ ^ 2 := by
    have hpairs : ∑ j ∈ C.pairs, 2 * (C.left j * starRingEnd ℂ (C.right j)).re = 0 :=
      sum_eq_zero fun j hj => by rw [hl j hj]; simp
    rw [re_secondMoment, hpairs, add_zero]
  rw [hS₁, hS₂]
  exact norm_sum_sq_le_card_support_mul _ _

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]

/-- The values of the linear weight family `x ↦ a_x(ρ) = ⟪u_ρ, x⟫` at the critical zeros
`crit` and at the reflected pairs `(v j, w j)`, `j ∈ pairs`. -/
def ofFunctionals (crit : Finset ι) (u : ι → V) (pairs : Finset κ) (v w : κ → V) (x : V) :
    ZeroValueConfig ι κ where
  crit := crit
  critValue i := ⟪u i, x⟫_ℂ
  pairs := pairs
  left j := ⟪v j, x⟫_ℂ
  right j := ⟪w j, x⟫_ℂ

/-- The weights vanishing at both members of every reflected pair: the orthogonal complement of
the span of the off-line functionals. -/
def offLineAnnihilator (pairs : Finset κ) (v w : κ → V) : Submodule ℂ V :=
  (Submodule.span ℂ (v '' pairs ∪ w '' pairs))ᗮ

theorem inner_eq_zero_of_mem_offLineAnnihilator {pairs : Finset κ} {v w : κ → V} {x : V}
    (hx : x ∈ offLineAnnihilator pairs v w) {j : κ} (hj : j ∈ pairs) :
    ⟪v j, x⟫_ℂ = 0 ∧ ⟪w j, x⟫_ℂ = 0 := by
  rw [offLineAnnihilator, Submodule.mem_orthogonal] at hx
  exact ⟨hx _ (Submodule.subset_span (Or.inl ⟨j, hj, rfl⟩)),
    hx _ (Submodule.subset_span (Or.inr ⟨j, hj, rfl⟩))⟩

/-- Vanishing at `p` reflected pairs costs at most `2p` dimensions. -/
theorem finrank_le_finrank_offLineAnnihilator_add [FiniteDimensional ℂ V] (pairs : Finset κ)
    (v w : κ → V) :
    Module.finrank ℂ V ≤ Module.finrank ℂ (offLineAnnihilator pairs v w) + 2 * #pairs := by
  classical
  set K := Submodule.span ℂ (v '' pairs ∪ w '' pairs)
  have hset : v '' (pairs : Set κ) ∪ w '' pairs =
      ((pairs.image v ∪ pairs.image w : Finset V) : Set V) := by simp
  have hK : Module.finrank ℂ K ≤ 2 * #pairs :=
    calc Module.finrank ℂ K = Set.finrank ℂ ((pairs.image v ∪ pairs.image w : Finset V) : Set V) := by
          rw [Set.finrank, ← hset]
      _ ≤ #(pairs.image v ∪ pairs.image w) := finrank_span_finset_le_card _
      _ ≤ #(pairs.image v) + #(pairs.image w) := card_union_le _ _
      _ ≤ #pairs + #pairs := add_le_add card_image_le card_image_le
      _ = 2 * #pairs := by ring
  have hsum := K.finrank_add_finrank_orthogonal
  change Module.finrank ℂ V ≤ Module.finrank ℂ Kᗮ + 2 * #pairs
  omega

/-- On the off-line annihilator every moment with `F(0, 0) = 0` is the moment of the critical
zeros alone. -/
theorem moment_ofFunctionals_eq_critPart (crit : Finset ι) (u : ι → V) {pairs : Finset κ}
    {v w : κ → V} {x : V} (hx : x ∈ offLineAnnihilator pairs v w) (F : ℂ → ℂ → ℂ)
    (hF : F 0 0 = 0) :
    (ofFunctionals crit u pairs v w x).moment F =
      (ofFunctionals crit u pairs v w x).critPart.moment F :=
  moment_eq_critPart_moment _ (fun _ hj => (inner_eq_zero_of_mem_offLineAnnihilator hx hj).1)
    (fun _ hj => (inner_eq_zero_of_mem_offLineAnnihilator hx hj).2) F hF

/-- **Robust Conrey–Ghosh–Gonek lemma.** For weights vanishing at every off-line zero,
`|S₁|² ≤ #{critical ρ : a(ρ) ≠ 0} · Re S₂`. -/
theorem norm_firstMoment_sq_le_of_mem_offLineAnnihilator (crit : Finset ι) (u : ι → V)
    {pairs : Finset κ} {v w : κ → V} {x : V} (hx : x ∈ offLineAnnihilator pairs v w) :
    ‖(ofFunctionals crit u pairs v w x).firstMoment‖ ^ 2 ≤
      #(crit.filter fun i => ⟪u i, x⟫_ℂ ≠ 0) *
        (ofFunctionals crit u pairs v w x).secondMoment.re :=
  norm_firstMoment_sq_le_of_pairs_eq_zero _
    (fun _ hj => (inner_eq_zero_of_mem_offLineAnnihilator hx hj).1)
    (fun _ hj => (inner_eq_zero_of_mem_offLineAnnihilator hx hj).2)

open Classical in
/-- The robust CGG lemma counting simple critical zeros: for weights vanishing at every off-line
zero, `|S₁|² ≤ #{critical ρ : u_ρ ≠ 0} · Re S₂`. -/
theorem norm_firstMoment_sq_le_card_simple_crit (crit : Finset ι) (u : ι → V)
    {pairs : Finset κ} {v w : κ → V} {x : V} (hx : x ∈ offLineAnnihilator pairs v w) :
    ‖(ofFunctionals crit u pairs v w x).firstMoment‖ ^ 2 ≤
      #(crit.filter fun i => u i ≠ 0) * (ofFunctionals crit u pairs v w x).secondMoment.re := by
  have hS₂ : 0 ≤ (ofFunctionals crit u pairs v w x).secondMoment.re := by
    have hpairs : ∑ j ∈ pairs, 2 * (⟪v j, x⟫_ℂ * starRingEnd ℂ ⟪w j, x⟫_ℂ).re = 0 :=
      sum_eq_zero fun j hj => by rw [(inner_eq_zero_of_mem_offLineAnnihilator hx hj).1]; simp
    rw [re_secondMoment]
    simp only [ofFunctionals]
    rw [hpairs, add_zero]
    exact sum_nonneg fun i _ => sq_nonneg _
  have hcard : (#(crit.filter fun i => ⟪u i, x⟫_ℂ ≠ 0) : ℝ) ≤ #(crit.filter fun i => u i ≠ 0) := by
    refine Nat.cast_le.2 (card_le_card fun i hi => ?_)
    rw [mem_filter] at hi ⊢
    exact ⟨hi.1, fun h0 => hi.2 (by rw [h0, inner_zero_left])⟩
  exact (norm_firstMoment_sq_le_of_mem_offLineAnnihilator crit u hx).trans
    (mul_le_mul_of_nonneg_right hcard hS₂)

end ZeroValueConfig

end RHTower
