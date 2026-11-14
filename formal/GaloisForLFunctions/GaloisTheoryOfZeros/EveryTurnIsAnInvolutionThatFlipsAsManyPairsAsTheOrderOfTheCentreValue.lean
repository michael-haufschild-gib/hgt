import GaloisForLFunctions.GaloisTheoryOfZeros.TheTurnAroundACollisionOfOnePairAtTheCentreFlipsExactlyOnePair
import GaloisForLFunctions.GaloisTheoryOfZeros.TheCentreValueIsTheEquationOfTheSignBranchPoints

/-!
# Every turn is an involution that flips as many pairs as the order of the centre value

Let `τ₀` be a forward time and `k` the order of vanishing of the centre value `c(τ) = H_τ(0)` at
`τ₀`; then `H_τ₀` has a zero of order `2k` at the centre (`k = 0` when `c(τ₀) ≠ 0`).

* **Involution** (`eventually_turn_involution_flip_iff`). For all small `r` the turn of radius
  `r²` around `τ₀` exchanges every zero `z` of `H_{τ₀+r²}` with a zero `z'`, and `z' = −z` exactly
  when `z` is one of the `2k` sheets of the collision at the centre.
* **The number of flips** (`eventually_ncard_turn_flipped`). Exactly `2k` zeros are carried to
  their negatives: the turn flips `k` pairs.
* **The element of the group** (`eventually_exists_turn_mem_forwardMonodromy`). The turn is an
  involution in `G₊(τ₀ + r²)` with `2k` flipped zeros.

So the local monodromy at every forward time is a product of `k` sign flips and of exchanges of
pairs, and the sign of the turn on the zeros is `(−1)^k`: the sign of the zeros is the local
monodromy of the square root of the centre value.

Proof. Far zeros and zeros near a simple zero of `H_τ₀` return. Near a multiple zero `ζ` the
zeros are the sheets `Z_ρ(r)`, and the turn carries `Z_ρ` to `Z_{−ρ}` and back. For `ζ ≠ 0` both
stay near `ζ`, away from `−ζ`, so the turn does not flip them. For `ζ = 0` the functional equation
gives `Z_{−ρ} = −Z_ρ`. The sheets at the centre are distinct, one for each of the `2k` roots of
the Hermite profile.
-/

open Complex Filter Topology Set Metric
open RHTower RHTower.DeBruijn
open GaloisForLFunctions.NodalGeometryOfTheDeBruijnFlow

namespace GaloisForLFunctions.GaloisTheoryOfZeros

set_option autoImplicit false

variable {τ₀ : ℂ} {k : ℕ}

private theorem eq_zero_of_eq_neg_self' {z : ℂ} (h : z = -z) : z = 0 := by
  have h2 : (2 : ℂ) * z = 0 := by linear_combination h
  exact (mul_eq_zero.1 h2).resolve_left two_ne_zero

/-- Every time carries a collision of even order `2k` at the centre; `k = 0` when the centre
value does not vanish. -/
theorem exists_isCollision_center_two_mul (τ₀ : ℂ) : ∃ k, IsCollision τ₀ 0 (2 * k) := by
  by_cases h : complexHeat τ₀ 0 = 0
  · obtain ⟨m, -, ⟨k, hk⟩, hc⟩ := exists_isCollision_center h
    refine ⟨k, ?_⟩
    rw [two_mul, ← hk]
    exact hc
  · exact ⟨0, fun i hi => absurd hi (by omega), by rw [iteratedDeriv_zero]; exact h⟩

/-- The profile of order `m` has `m` roots. -/
theorem ncard_setOf_heatModelFwd_eq_zero (m : ℕ) : {ρ : ℂ | heatModelFwd m ρ = 0}.ncard = m := by
  have hset : {ρ : ℂ | heatModelFwd m ρ = 0} =
      (fun x : ℝ => (x : ℂ)) '' (profileRoots m : Set ℝ) := by
    ext ρ
    simp only [mem_setOf_eq, mem_image, Finset.mem_coe]
    exact heatModelFwd_eq_zero_iff
  rw [hset, Set.ncard_image_of_injective _ Complex.ofReal_injective, Set.ncard_coe_finset,
    card_profileRoots]

/-! ## The sheets at the centre -/

/-- **The turn carries every sheet of the central collision to its negative.** -/
theorem IsCollision.eventually_turn_center_sheets (hcen : IsCollision τ₀ 0 (2 * k)) :
    ∀ᶠ r : ℝ in 𝓝[>] 0, ∀ ρ ∈ {ρ : ℂ | heatModelFwd (2 * k) ρ = 0},
      Transports (turnPath τ₀ r) (collisionZero τ₀ 0 (2 * k) ρ r)
        (-collisionZero τ₀ 0 (2 * k) ρ r) := by
  refine (eventually_all_finite (finite_setOf_heatModelFwd_eq_zero (2 * k))).2 fun ρ hρ => ?_
  have h1 := eventually_nhdsGT_of_exists_Ioo (hcen.exists_transports_turn hρ)
  have h2 : ∀ᶠ r : ℝ in 𝓝[>] 0,
      -collisionZero τ₀ 0 (2 * k) ρ r = collisionZero τ₀ 0 (2 * k) (-ρ) r := by
    have h := collisionZero_reflect hcen hρ
    rw [neg_zero] at h
    exact eventually_nhdsGT_of_exists_Ioo (exists_forall_Ioo_of_eventually
      (P := fun s : ℂ => -collisionZero τ₀ 0 (2 * k) ρ s = collisionZero τ₀ 0 (2 * k) (-ρ) s)
      (h.filter_mono nhdsWithin_le_nhds))
  filter_upwards [h1, h2] with r hr1 hr2
  rw [hr2]
  exact hr1

/-- The sheets of the central collision are distinct for small radii. -/
theorem IsCollision.eventually_injOn_center_sheets (hcen : IsCollision τ₀ 0 (2 * k)) :
    ∀ᶠ r : ℝ in 𝓝[>] 0, Set.InjOn (fun ρ : ℂ => collisionZero τ₀ 0 (2 * k) ρ r)
      {ρ : ℂ | heatModelFwd (2 * k) ρ = 0} := by
  have hfin := finite_setOf_heatModelFwd_eq_zero (2 * k)
  have h : ∀ᶠ r : ℝ in 𝓝[>] 0, ∀ ρ ∈ {ρ : ℂ | heatModelFwd (2 * k) ρ = 0},
      ∀ ρ' ∈ {ρ : ℂ | heatModelFwd (2 * k) ρ = 0}, ρ ≠ ρ' →
        collisionZero τ₀ 0 (2 * k) ρ r ≠ collisionZero τ₀ 0 (2 * k) ρ' r :=
    (eventually_all_finite hfin).2 fun ρ hρ => (eventually_all_finite hfin).2 fun ρ' hρ' => by
      by_cases hne : ρ = ρ'
      · exact Eventually.of_forall fun r h => absurd hne h
      · have h := collisionZero_ne hcen hρ hρ' hne
        exact (eventually_nhdsGT_of_exists_Ioo (exists_forall_Ioo_of_eventually
          (P := fun s : ℂ =>
            collisionZero τ₀ 0 (2 * k) ρ s ≠ collisionZero τ₀ 0 (2 * k) ρ' s) h)).mono
          fun r hr _ => hr
  filter_upwards [h] with r hr ρ hρ ρ' hρ' heq
  by_contra hne
  exact hr ρ hρ ρ' hρ' hne heq

/-! ## The turn on the whole fibre -/

/-- Every zero is a sheet of the central collision, or the turn exchanges it with a zero that is
not its negative. -/
theorem eventually_turn_center_sheet_or_exchange (hτ₀ : 0 < τ₀.re)
    (hcen : IsCollision τ₀ 0 (2 * k)) :
    ∀ᶠ r : ℝ in 𝓝[>] 0, ∀ z : ℂ, complexHeat (τ₀ + (r : ℂ) ^ 2) z = 0 →
      (∃ ρ : ℂ, heatModelFwd (2 * k) ρ = 0 ∧ z = collisionZero τ₀ 0 (2 * k) ρ r) ∨
        ∃ z' : ℂ, Transports (turnPath τ₀ r) z z' ∧ Transports (turnPath τ₀ r) z' z ∧
          z' ≠ -z := by
  obtain ⟨R, hfar⟩ := eventually_turn_transports_self_of_far hτ₀
  refine eventually_forall_zero_of_local (R := max R 1) ?_ fun ζ h0 => ?_
  · -- the far zeros return, and they are not the centre
    filter_upwards [hfar] with r hr z hz hzR
    have hT := hr z hz ((le_max_left _ _).trans hzR)
    refine Or.inr ⟨z, hT, hT, fun h => ?_⟩
    rw [eq_zero_of_eq_neg_self' h, norm_zero] at hzR
    linarith [le_max_right R 1]
  · by_cases hζ : ζ = 0
    · -- near the centre the zeros are the sheets of the central collision
      subst hζ
      obtain ⟨ρ, hρ, hev⟩ := eventually_turn_transports_sheets hcen
      refine ⟨ρ, hρ, hev.mono fun r hr z hz hzero => ?_⟩
      obtain ⟨ρ', hρ', hzeq, -⟩ := hr z hz hzero
      exact Or.inl ⟨ρ', hρ', hzeq⟩
    · have hζn : 0 < ‖ζ‖ / 2 := half_pos (norm_pos_iff.mpr hζ)
      by_cases h1 : deriv (complexHeat τ₀) ζ = 0
      · -- a collision away from the centre: the exchange stays near `ζ`, away from `−ζ`
        obtain ⟨m, -, hc⟩ := exists_isCollision_two_le h0 h1
        obtain ⟨ρ, hρ, hev⟩ := hc.eventually_turn_exchange hζn
        refine ⟨min ρ (‖ζ‖ / 2), lt_min hρ hζn, hev.mono fun r hr z hz hzero => ?_⟩
        obtain ⟨z', hz', hT, hT'⟩ := hr z (ball_subset_ball (min_le_left _ _) hz) hzero
        refine Or.inr ⟨z', hT, hT', fun h => ?_⟩
        have hz2 := ball_subset_ball (min_le_right ρ (‖ζ‖ / 2)) hz
        rw [h] at hz'
        rw [mem_ball, dist_eq_norm] at hz' hz2
        have h3 : ‖(2 : ℂ) * ζ‖ ≤ ‖-z - ζ‖ + ‖z - ζ‖ := by
          have e : (2 : ℂ) * ζ = -((-z - ζ) + (z - ζ)) := by ring
          rw [e, norm_neg]
          exact norm_add_le _ _
        rw [norm_mul, Complex.norm_ofNat] at h3
        linarith
      · -- a simple zero away from the centre: the zeros near it return
        obtain ⟨ρ, hρ, hev⟩ := eventually_turn_transports_self_of_simple h0 h1
        refine ⟨min ρ (‖ζ‖ / 2), lt_min hρ hζn, hev.mono fun r hr z hz hzero => ?_⟩
        have hT := hr z (ball_subset_ball (min_le_left _ _) hz) hzero
        refine Or.inr ⟨z, hT, hT, fun h => ?_⟩
        have hz2 := ball_subset_ball (min_le_right ρ (‖ζ‖ / 2)) hz
        rw [eq_zero_of_eq_neg_self' h, mem_ball, dist_eq_norm, zero_sub, norm_neg] at hz2
        linarith

/-- **Every turn is an involution, and it flips the sheets of the central collision.** Let
`H_τ₀` have a zero of order `2k` at the centre. For all small `r` the turn of radius `r²` around
`τ₀` exchanges every zero `z` of `H_{τ₀+r²}` with a zero `z'`, and `z' = −z` if and only if `z`
is a sheet of the central collision. -/
theorem eventually_turn_involution_flip_iff (hτ₀ : 0 < τ₀.re)
    (hcen : IsCollision τ₀ 0 (2 * k)) :
    ∀ᶠ r : ℝ in 𝓝[>] 0, ∀ z : ℂ, complexHeat (τ₀ + (r : ℂ) ^ 2) z = 0 →
      ∃ z' : ℂ, Transports (turnPath τ₀ r) z z' ∧ Transports (turnPath τ₀ r) z' z ∧
        (z' = -z ↔ ∃ ρ : ℂ, heatModelFwd (2 * k) ρ = 0 ∧
          z = collisionZero τ₀ 0 (2 * k) ρ r) := by
  filter_upwards [eventually_turn_center_sheet_or_exchange hτ₀ hcen,
    hcen.eventually_turn_center_sheets,
    eventually_nhdsGT_of_exists_Ioo (exists_isForwardPath_turnPath hτ₀)] with r hact hsh hγ z hz
  rcases hact z hz with ⟨ρ, hρ, rfl⟩ | ⟨z', hT, hT', hne⟩
  · have hT := hsh ρ hρ
    have hT' := hT.neg
    rw [neg_neg] at hT'
    exact ⟨_, hT, hT', fun _ => ⟨ρ, hρ, rfl⟩, fun _ => rfl⟩
  · refine ⟨z', hT, hT', fun h => absurd h hne, ?_⟩
    rintro ⟨ρ, hρ, rfl⟩
    exact hγ.transports_unique hT (hsh ρ hρ)

/-- **The turn flips `k` pairs.** Let `H_τ₀` have a zero of order `2k` at the centre. For all
small `r` exactly `2k` zeros of `H_{τ₀+r²}` are carried to their negatives by the turn of radius
`r²` around `τ₀`. -/
theorem eventually_ncard_turn_flipped (hτ₀ : 0 < τ₀.re) (hcen : IsCollision τ₀ 0 (2 * k)) :
    ∀ᶠ r : ℝ in 𝓝[>] 0, {z : ℂ | complexHeat (τ₀ + (r : ℂ) ^ 2) z = 0 ∧
      Transports (turnPath τ₀ r) z (-z)}.ncard = 2 * k := by
  filter_upwards [eventually_turn_involution_flip_iff hτ₀ hcen,
    hcen.eventually_turn_center_sheets, hcen.eventually_injOn_center_sheets,
    eventually_nhdsGT_of_exists_Ioo (exists_isForwardPath_turnPath hτ₀)] with r hinv hsh hinj hγ
  have hset : {z : ℂ | complexHeat (τ₀ + (r : ℂ) ^ 2) z = 0 ∧
      Transports (turnPath τ₀ r) z (-z)} =
      (fun ρ : ℂ => collisionZero τ₀ 0 (2 * k) ρ r) '' {ρ : ℂ | heatModelFwd (2 * k) ρ = 0} := by
    ext z
    constructor
    · rintro ⟨hz, hT⟩
      obtain ⟨z', hT', -, hiff⟩ := hinv z hz
      obtain ⟨ρ, hρ, hzρ⟩ := hiff.1 (hγ.transports_unique hT' hT)
      exact ⟨ρ, hρ, hzρ.symm⟩
    · rintro ⟨ρ, hρ, rfl⟩
      have hT := hsh ρ hρ
      refine ⟨?_, hT⟩
      have h := hT.zero_left
      rwa [turnPath_zero] at h
  rw [hset, hinj.ncard_image, ncard_setOf_heatModelFwd_eq_zero]

/-! ## The turn as an element of the group -/

/-- **The turn is an involution of the forward monodromy group with `k` flipped pairs.** Let
`H_τ₀` have a zero of order `2k` at the centre. For all small `r` the transport along the turn of
radius `r²` around `τ₀` is an element `σ` of `G₊(τ₀ + r²)` with `σ² = 1` that carries exactly
`2k` zeros to their negatives. -/
theorem eventually_exists_turn_mem_forwardMonodromy (hτ₀ : 0 < τ₀.re)
    (hcen : IsCollision τ₀ 0 (2 * k)) :
    ∀ᶠ r : ℝ in 𝓝[>] 0, ∃ (hτ₁ : 0 < (τ₀ + (r : ℂ) ^ 2).re)
      (hb₁ : τ₀ + (r : ℂ) ^ 2 ∉ branchTimes),
      ∃ σ ∈ forwardMonodromy (τ₀ + (r : ℂ) ^ 2) hτ₁ hb₁,
        (∀ p, Transports (turnPath τ₀ r) p.1 (σ p).1) ∧ (∀ p, σ (σ p) = p) ∧
          {p | σ p = fibreNeg (τ₀ + (r : ℂ) ^ 2) p}.ncard = 2 * k := by
  filter_upwards [eventually_turn_involution_flip_iff hτ₀ hcen,
    eventually_ncard_turn_flipped hτ₀ hcen,
    eventually_nhdsGT_of_exists_Ioo (exists_isForwardPath_turnPath hτ₀)] with r hinv hcard hγ
  have h00 : (0 : ℝ) ∈ Icc (0 : ℝ) 1 := left_mem_Icc.2 zero_le_one
  have hτ₁ : 0 < (τ₀ + (r : ℂ) ^ 2).re := by
    have h := hγ.re_pos 0 h00
    rwa [turnPath_zero] at h
  have hb₁ : τ₀ + (r : ℂ) ^ 2 ∉ branchTimes := by
    have h := hγ.simple 0 h00
    rwa [turnPath_zero] at h
  obtain ⟨σ, hσ, hact⟩ := hγ.exists_mem_forwardMonodromy (hτ := hτ₁) (hb := hb₁)
    (turnPath_zero τ₀ r) (turnPath_one τ₀ r)
  refine ⟨hτ₁, hb₁, σ, hσ, hact, fun p => ?_, ?_⟩
  · obtain ⟨z', hT, hT', -⟩ := hinv p.1 p.2
    have e1 : (σ p).1 = z' := hγ.transports_unique (hact p) hT
    rw [← e1] at hT'
    exact Subtype.ext (hγ.transports_unique (hact (σ p)) hT')
  · rw [← hcard, ← Set.ncard_image_of_injective _ Subtype.val_injective]
    congr 1
    ext z
    constructor
    · rintro ⟨p, hp, rfl⟩
      have h := hact p
      rw [show σ p = fibreNeg (τ₀ + (r : ℂ) ^ 2) p from hp] at h
      exact ⟨p.2, h⟩
    · rintro ⟨hz, hT⟩
      exact ⟨⟨z, hz⟩, Subtype.ext (hγ.transports_unique (hact ⟨z, hz⟩) hT), rfl⟩

end GaloisForLFunctions.GaloisTheoryOfZeros
