import GaloisForLFunctions.GaloisTheoryOfZeros.TheTurnsGenerateTheForwardMonodromyGroup
import GaloisForLFunctions.GaloisTheoryOfZeros.TheTurnAroundABranchTimeMovesOnlyTheSheetsOfItsCollisions

/-!
# Only a collision off the centre moves a pair

The zeros of `H_τ` come in pairs `{z, −z}`. A multiple zero at the centre `0` is a *central*
collision; its turn exchanges `Z_ρ` with `Z_{−ρ} = −Z_ρ`.

* `pairGroup b`: the permutations of the fibre over `b` that carry every zero `z` to `z` or
  to `−z`.
* `eventually_turn_transports_self_or_neg`: if every multiple zero of `H_τ₀` is at the centre,
  the small turns around `τ₀` carry every zero `z` to `z` or to `−z`.
* **Local theorem** (`loopsIn_pairGroup`). Let `D` be a convex open set of forward times over
  which every multiple zero is at the centre. Every forward loop inside `D` carries every zero
  `z` to `z` or to `−z`: the turns do, and the turns generate.
* **The detector** (`exists_multipleZero_ne_zero_of_transports`). A forward loop inside a
  convex open set `D` of forward times that carries a zero `z` to a zero other than `±z`
  certifies a multiple zero `ζ ≠ 0` at a time of `D`.
* **The criterion** (`forwardMonodromy_preserves_pairs_iff`). The forward monodromy group
  preserves every pair if and only if no multiple zero `ζ ≠ 0` exists at a forward time.
* In that case the group is commutative of exponent two
  (`forwardMonodromy_mul_self_of_central`, `forwardMonodromy_mul_comm_of_central`).
-/

open Complex Set Metric Filter Topology
open RHTower

namespace GaloisForLFunctions.GaloisTheoryOfZeros

noncomputable section
set_option autoImplicit false

variable {b : ℂ}

/-! ## The group of the sign changes -/

/-- The permutations of the fibre over `b` that carry every zero `z` to `z` or to `−z`. -/
def pairGroup (b : ℂ) : Subgroup (Equiv.Perm (Fibre b)) where
  carrier := {σ | ∀ q : Fibre b, (σ q).1 = q.1 ∨ (σ q).1 = -q.1}
  mul_mem' := by
    intro σ σ' hσ hσ' q
    rw [Equiv.Perm.mul_apply]
    rcases hσ (σ' q) with h | h <;> rcases hσ' q with h' | h' <;> rw [h, h']
    · exact Or.inl rfl
    · exact Or.inr rfl
    · exact Or.inr rfl
    · exact Or.inl (neg_neg _)
  one_mem' := fun _ => Or.inl rfl
  inv_mem' := by
    intro σ hσ q
    have e : σ (σ⁻¹ q) = q := σ.apply_symm_apply q
    have h := hσ (σ⁻¹ q)
    rw [e] at h
    rcases h with h | h
    · exact Or.inl h.symm
    · exact Or.inr (by rw [h, neg_neg])

theorem mem_pairGroup {σ : Equiv.Perm (Fibre b)} :
    σ ∈ pairGroup b ↔ ∀ q : Fibre b, (σ q).1 = q.1 ∨ (σ q).1 = -q.1 :=
  Iff.rfl

/-! ## The turn around a time whose collisions are central -/

/-- **A turn around a time whose collisions are central preserves every pair.** A moved zero
is a sheet `Z_ρ` of the collision at the centre, and the opposite sheet is `−Z_ρ`. -/
theorem eventually_turn_transports_self_or_neg {τ₀ : ℂ} (hτ₀ : 0 < τ₀.re)
    (hcen : ∀ ζ : ℂ, complexHeat τ₀ ζ = 0 → deriv (complexHeat τ₀) ζ = 0 → ζ = 0) :
    ∀ᶠ r : ℝ in 𝓝[>] 0, ∀ z : ℂ, complexHeat (τ₀ + (r : ℂ) ^ 2) z = 0 →
      Transports (turnPath τ₀ r) z z ∨ Transports (turnPath τ₀ r) z (-z) := by
  -- a collision of order `≥ 2` at the time `τ₀` is at the centre
  have hzero : ∀ (ζ : ℂ) (m : ℕ), 2 ≤ m → IsCollision τ₀ ζ m → ζ = 0 := fun ζ m hm hc =>
    hcen ζ (by have h := hc.vanish 0 (by omega); rwa [iteratedDeriv_zero] at h)
      (by have h := hc.vanish 1 (by omega); rwa [iteratedDeriv_one] at h)
  by_cases h0 : complexHeat τ₀ 0 = 0
  · obtain ⟨m₀, -, hc₀⟩ := exists_isCollision h0
    -- the reflection law on all sheets of the central collision
    have hrefl : ∀ᶠ r : ℝ in 𝓝[>] 0, ∀ x ∈ profileRoots m₀,
        -collisionZero τ₀ 0 m₀ (x : ℂ) r = collisionZero τ₀ 0 m₀ (-(x : ℂ)) r := by
      refine (Filter.eventually_all_finset _).2 fun x hx => ?_
      have h := collisionZero_reflect hc₀ (heatModelFwd_eq_zero_iff.2 ⟨x, hx, rfl⟩)
      rw [neg_zero] at h
      exact eventually_nhdsGT_of_exists_Ioo (exists_forall_Ioo_of_eventually
        (P := fun s : ℂ =>
          -collisionZero τ₀ 0 m₀ (x : ℂ) s = collisionZero τ₀ 0 m₀ (-(x : ℂ)) s)
        (h.filter_mono nhdsWithin_le_nhds))
    filter_upwards [eventually_turnAction hτ₀, hrefl] with r hact hr z hz
    rcases hact z hz with h | ⟨ζ, m, ρ, hm, hc, hρ, hzeq, hT⟩
    · exact Or.inl h
    · have hζ := hzero ζ m hm hc
      subst hζ
      have hmm : m = m₀ := by
        have h1 := isCollision_iff_analyticOrderAt.1 hc
        have h2 := isCollision_iff_analyticOrderAt.1 hc₀
        rw [h1] at h2
        exact_mod_cast h2
      subst hmm
      obtain ⟨x, hx, rfl⟩ := heatModelFwd_eq_zero_iff.1 hρ
      rw [← hr x hx, ← hzeq] at hT
      exact Or.inr hT
  · filter_upwards [eventually_turnAction hτ₀] with r hact z hz
    rcases hact z hz with h | ⟨ζ, m, ρ, hm, hc, -, -, -⟩
    · exact Or.inl h
    · exfalso
      have hζ := hzero ζ m hm hc
      subst hζ
      exact h0 (by have h := hc.vanish 0 (by omega); rwa [iteratedDeriv_zero] at h)

/-- Over a region whose collisions are central the conjugated turns preserve every pair:
transport along the tail commutes with `z ↦ −z`. -/
theorem turnsIn_pairGroup {D : Set ℂ} (hDpos : ∀ τ ∈ D, 0 < τ.re)
    (hcen : ∀ τ ∈ D, ∀ ζ : ℂ, complexHeat τ ζ = 0 → deriv (complexHeat τ) ζ = 0 → ζ = 0) :
    TurnsIn D b (pairGroup b) := by
  intro p hpD _ ε hε
  obtain ⟨r₀, hr₀, hact⟩ := exists_Ioo_of_eventually_nhdsGT
    (eventually_turn_transports_self_or_neg (hDpos p hpD) (hcen p hpD))
  obtain ⟨r, hr, hrr₀, hrε⟩ : ∃ r : ℝ, 0 < r ∧ r < r₀ ∧ r < ε :=
    ⟨min r₀ ε / 2, half_pos (lt_min hr₀ hε),
      (half_lt_self (lt_min hr₀ hε)).trans_le (min_le_left _ _),
      (half_lt_self (lt_min hr₀ hε)).trans_le (min_le_right _ _)⟩
  refine ⟨r, hr, hrε, fun δ hδ d0 d1 _ hT => ?_⟩
  rw [mem_tailComap, mem_pairGroup]
  intro q
  rw [Equiv.trans_apply, Equiv.trans_apply]
  rcases hact r ⟨hr, hrr₀⟩ _ (hδ.fibreEquiv d0 d1 q).2 with h | h
  · have e1 : hT.fibreEquiv (turnPath_zero p r) (turnPath_one p r) (hδ.fibreEquiv d0 d1 q) =
        hδ.fibreEquiv d0 d1 q := hT.fibreEquiv_eq _ _ h
    exact Or.inl (by rw [e1, Equiv.symm_apply_apply])
  · have hval : (hT.fibreEquiv (turnPath_zero p r) (turnPath_one p r)
        (hδ.fibreEquiv d0 d1 q)).1 = -(hδ.fibreEquiv d0 d1 q).1 :=
      hT.transports_unique (hT.transports_fibreEquiv _ _ _) h
    have hq : hδ.fibreEquiv d0 d1 (fibreNeg b q) =
        hT.fibreEquiv (turnPath_zero p r) (turnPath_one p r) (hδ.fibreEquiv d0 d1 q) :=
      hδ.fibreEquiv_eq d0 d1 (by
        rw [hval]
        exact (hδ.transports_fibreEquiv d0 d1 q).neg)
    have hfin : (hδ.fibreEquiv d0 d1).symm (hT.fibreEquiv (turnPath_zero p r) (turnPath_one p r)
        (hδ.fibreEquiv d0 d1 q)) = fibreNeg b q := (Equiv.symm_apply_eq _).2 hq.symm
    exact Or.inr (congrArg Subtype.val hfin)

/-! ## Loops over a region whose collisions are central -/

/-- **Loops over a region whose collisions are central preserve every pair.** Let `D` be a
convex open set of forward times over which every multiple zero is at the centre. The
transport along a forward loop inside `D` carries every zero `z` to `z` or to `−z`. -/
theorem loopsIn_pairGroup {D : Set ℂ} (hD : Convex ℝ D) (hDo : IsOpen D)
    (hDpos : ∀ τ ∈ D, 0 < τ.re)
    (hcen : ∀ τ ∈ D, ∀ ζ : ℂ, complexHeat τ ζ = 0 → deriv (complexHeat τ) ζ = 0 → ζ = 0) :
    LoopsIn D b (pairGroup b) :=
  loopsIn_of_turnsIn hD hDo hDpos (turnsIn_pairGroup hDpos hcen)

/-- **The detector of a collision off the centre.** A forward loop inside a convex open set
`D` of forward times that carries a zero `z` to a zero other than `z` and `−z` certifies a
multiple zero `ζ ≠ 0` at a time of `D`. -/
theorem exists_multipleZero_ne_zero_of_transports {D : Set ℂ} (hD : Convex ℝ D) (hDo : IsOpen D)
    (hDpos : ∀ τ ∈ D, 0 < τ.re) {γ : ℝ → ℂ} (hγ : IsForwardPath γ) (hloop : γ 1 = γ 0)
    (hγD : ∀ s ∈ Icc (0 : ℝ) 1, γ s ∈ D) {z w : ℂ} (hT : Transports γ z w) (h1 : w ≠ z)
    (h2 : w ≠ -z) :
    ∃ τ ∈ D, ∃ ζ : ℂ, ζ ≠ 0 ∧ complexHeat τ ζ = 0 ∧ deriv (complexHeat τ) ζ = 0 := by
  by_contra hcon
  have hcen : ∀ τ ∈ D, ∀ ζ : ℂ, complexHeat τ ζ = 0 → deriv (complexHeat τ) ζ = 0 → ζ = 0 :=
    fun τ hτ ζ h0 hd => by
      by_contra hζ
      exact hcon ⟨τ, hτ, ζ, hζ, h0, hd⟩
  have hz : complexHeat (γ 0) z = 0 := hT.zero_left
  have hmem := loopsIn_pairGroup (b := γ 0) hD hDo hDpos hcen γ hγ rfl hloop hγD
  have hw : w = (hγ.fibreEquiv rfl hloop ⟨z, hz⟩).1 :=
    hγ.transports_unique hT (hγ.transports_fibreEquiv rfl hloop ⟨z, hz⟩)
  rcases mem_pairGroup.1 hmem ⟨z, hz⟩ with h | h
  · exact h1 (hw.trans h)
  · exact h2 (hw.trans h)

/-! ## The forward monodromy group -/

/-- **The forward monodromy group preserves the pairs exactly when every forward collision is
central.** Every element carries every zero `z` to `z` or to `−z` if and only if no multiple
zero `ζ ≠ 0` exists at a forward time. -/
theorem forwardMonodromy_preserves_pairs_iff (hb₀ : 0 < b.re) (hb : b ∉ branchTimes) :
    (∀ σ ∈ forwardMonodromy b hb₀ hb, ∀ q, σ q = q ∨ σ q = fibreNeg b q) ↔
      ∀ τ ζ : ℂ, 0 < τ.re → complexHeat τ ζ = 0 → deriv (complexHeat τ) ζ = 0 → ζ = 0 := by
  constructor
  · intro h τ ζ hτ h0 hd
    by_contra hζ
    obtain ⟨σ, hσ, q, h1, h2⟩ := exists_mem_forwardMonodromy_moving_pair hτ h0 hd hζ hb₀ hb
    rcases h σ hσ q with h3 | h3
    · exact h1 h3
    · exact h2 h3
  · intro hcen σ hσ q
    obtain ⟨γ, hγ, g0, g1, hT⟩ := mem_forwardMonodromy.1 hσ
    have hσeq : σ = hγ.fibreEquiv g0 g1 :=
      Equiv.ext fun q => (hγ.fibreEquiv_eq g0 g1 (hT q)).symm
    have hmem := loopsIn_pairGroup (b := b) (convex_halfSpace_re_gt 0)
      (isOpen_lt continuous_const Complex.continuous_re) (fun _ h => h)
      (fun τ hτ ζ => hcen τ ζ hτ) γ hγ g0 g1 hγ.re_pos
    rw [← hσeq] at hmem
    rcases mem_pairGroup.1 hmem q with h | h
    · exact Or.inl (Subtype.ext h)
    · exact Or.inr (Subtype.ext h)

/-- Without forward collisions off the centre every forward monodromy is an involution. -/
theorem forwardMonodromy_mul_self_of_central (hb₀ : 0 < b.re) (hb : b ∉ branchTimes)
    (hcen : ∀ τ ζ : ℂ, 0 < τ.re → complexHeat τ ζ = 0 → deriv (complexHeat τ) ζ = 0 → ζ = 0)
    {σ : Equiv.Perm (Fibre b)} (hσ : σ ∈ forwardMonodromy b hb₀ hb) : σ * σ = 1 := by
  refine Equiv.ext fun q => ?_
  rw [Equiv.Perm.mul_apply, Equiv.Perm.one_apply]
  rcases (forwardMonodromy_preserves_pairs_iff hb₀ hb).2 hcen σ hσ q with h | h
  · rw [h, h]
  · have hc := DFunLike.congr_fun (forwardMonodromy_commute_fibreNeg hσ) q
    rw [Equiv.Perm.mul_apply, Equiv.Perm.mul_apply] at hc
    rw [h, hc, h]
    exact Subtype.ext (neg_neg _)

/-- **Without forward collisions off the centre the forward monodromy group is commutative**:
a group of involutions. -/
theorem forwardMonodromy_mul_comm_of_central (hb₀ : 0 < b.re) (hb : b ∉ branchTimes)
    (hcen : ∀ τ ζ : ℂ, 0 < τ.re → complexHeat τ ζ = 0 → deriv (complexHeat τ) ζ = 0 → ζ = 0)
    {σ σ' : Equiv.Perm (Fibre b)} (hσ : σ ∈ forwardMonodromy b hb₀ hb)
    (hσ' : σ' ∈ forwardMonodromy b hb₀ hb) : σ * σ' = σ' * σ := by
  have h1 := forwardMonodromy_mul_self_of_central hb₀ hb hcen hσ
  have h2 := forwardMonodromy_mul_self_of_central hb₀ hb hcen hσ'
  have h3 := forwardMonodromy_mul_self_of_central hb₀ hb hcen
    ((forwardMonodromy b hb₀ hb).mul_mem hσ hσ')
  calc σ * σ' = σ * (σ * σ' * (σ * σ')) * σ' := by rw [h3, mul_one]
    _ = σ * σ * (σ' * σ) * (σ' * σ') := by simp only [mul_assoc]
    _ = σ' * σ := by rw [h1, h2, one_mul, mul_one]

end

end GaloisForLFunctions.GaloisTheoryOfZeros
