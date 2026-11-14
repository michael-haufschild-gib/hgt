import GaloisForLFunctions.GaloisTheoryOfZeros.TheTurnAroundABranchTimeMovesOnlyTheSheetsOfItsCollisions
import GaloisForLFunctions.GaloisTheoryOfZeros.TheForwardMonodromyGroupHasIndexAtMostTwoInTheSignedPermutationsOfFiniteSupport

/-!
# The turn around an isolated double collision off the centre is the exchange of two pairs

Let `τ₀` be a forward time at which `H_τ₀` has a double zero at `ζ₀ ≠ 0`, hence at `−ζ₀`, and no
other multiple zero.

* **The turn** (`eventually_turn_exchange`). For all small `r` the turn of radius `r²` around `τ₀`
  exchanges two zeros `w`, `w'` of `H_{τ₀+r²}` in distinct pairs, exchanges `−w`, `−w'`, and
  fixes every other zero.
* **The group** (`mem_forwardMonodromy_of_isolated_double_collision`). Then at every forward base
  time `b` off the branch times `G₊(b)` contains every permutation of the zeros of `H_b` that
  commutes with `z ↦ −z` and moves finitely many zeros.

So the last sign of the group of the zeros is decided by one forward time with one double
collision off the centre and no other collision.

Proof. The sheets `Z_{±ρ₀}` of the collision at `ζ₀` are exchanged by the turn; they tend to
`ζ₀ ≠ 0`, so they lie in distinct pairs. The sheets at `−ζ₀` are their negatives. The turn fixes
every zero that is not a sheet of a collision at `τ₀`. One exchange in `G₊` gives the whole
group of the signed permutations of finite support.
-/

open Complex Filter Topology Set Metric
open RHTower RHTower.DeBruijn Equiv
open GaloisForLFunctions.NodalGeometryOfTheDeBruijnFlow

namespace GaloisForLFunctions.GaloisTheoryOfZeros

set_option autoImplicit false

variable {τ₀ ζ₀ : ℂ}

/-- The turn around an isolated double collision off the centre, for a profile of order two with
the roots `±ρ₀`. -/
theorem eventually_turn_exchange_of_roots (hτ₀ : 0 < τ₀.re) (hc : IsCollision τ₀ ζ₀ 2)
    (hζ₀ : ζ₀ ≠ 0)
    (honly : ∀ ζ : ℂ, complexHeat τ₀ ζ = 0 → deriv (complexHeat τ₀) ζ = 0 → ζ = ζ₀ ∨ ζ = -ζ₀)
    {ρ₀ : ℂ} (hρp : heatModelFwd 2 ρ₀ = 0) (hρn : heatModelFwd 2 (-ρ₀) = 0)
    (hroots : ∀ ρ' : ℂ, heatModelFwd 2 ρ' = 0 → ρ' = ρ₀ ∨ ρ' = -ρ₀) (hne : ρ₀ ≠ -ρ₀) :
    ∀ᶠ r : ℝ in 𝓝[>] 0, ∃ w w' : ℂ, w' ≠ w ∧ w' ≠ -w ∧
      complexHeat (τ₀ + (r : ℂ) ^ 2) w = 0 ∧
      Transports (turnPath τ₀ r) w w' ∧ Transports (turnPath τ₀ r) w' w ∧
        ∀ z : ℂ, complexHeat (τ₀ + (r : ℂ) ^ 2) z = 0 → z ≠ w → z ≠ -w → z ≠ w' → z ≠ -w' →
          Transports (turnPath τ₀ r) z z := by
  have hc' : IsCollision τ₀ (-ζ₀) 2 := hc.neg
  -- the two sheets at `ζ₀`
  obtain ⟨Zp, hZp⟩ : ∃ Zp : ℂ → ℂ, Zp = collisionZero τ₀ ζ₀ 2 ρ₀ := ⟨_, rfl⟩
  obtain ⟨Zn, hZn⟩ : ∃ Zn : ℂ → ℂ, Zn = collisionZero τ₀ ζ₀ 2 (-ρ₀) := ⟨_, rfl⟩
  -- the sheets at `−ζ₀` are their negatives
  have hreflA : ∀ᶠ r : ℝ in 𝓝[>] 0, -collisionZero τ₀ (-ζ₀) 2 ρ₀ r = Zn r := by
    have h := collisionZero_reflect hc' hρp
    rw [neg_neg, ← hZn] at h
    exact eventually_nhdsGT_of_exists_Ioo (exists_forall_Ioo_of_eventually
      (P := fun s : ℂ => -collisionZero τ₀ (-ζ₀) 2 ρ₀ s = Zn s)
      (h.filter_mono nhdsWithin_le_nhds))
  have hreflB : ∀ᶠ r : ℝ in 𝓝[>] 0, -collisionZero τ₀ (-ζ₀) 2 (-ρ₀) r = Zp r := by
    have h := collisionZero_reflect hc' hρn
    rw [neg_neg, neg_neg, ← hZp] at h
    exact eventually_nhdsGT_of_exists_Ioo (exists_forall_Ioo_of_eventually
      (P := fun s : ℂ => -collisionZero τ₀ (-ζ₀) 2 (-ρ₀) s = Zp s)
      (h.filter_mono nhdsWithin_le_nhds))
  have hdist : ∀ᶠ r : ℝ in 𝓝[>] 0, Zp r ≠ Zn r := by
    have h := collisionZero_ne hc hρp hρn hne
    rw [← hZp, ← hZn] at h
    exact eventually_nhdsGT_of_exists_Ioo (exists_forall_Ioo_of_eventually
      (P := fun s : ℂ => Zp s ≠ Zn s) h)
  -- both sheets tend to `ζ₀ ≠ 0`, so they are not opposite
  have hsep : ∀ᶠ r : ℝ in 𝓝[>] 0, Zn r ≠ -Zp r := by
    have hcont : ContinuousAt (fun s : ℂ => Zn s + Zp s) 0 := by
      rw [hZp, hZn]
      exact (hc.continuousAt_collisionZero hρn).add (hc.continuousAt_collisionZero hρp)
    have h0 : (fun s : ℂ => Zn s + Zp s) 0 ≠ 0 := by
      show Zn 0 + Zp 0 ≠ 0
      rw [hZp, hZn, collisionZero_zero, collisionZero_zero]
      intro h
      have h2 : (2 : ℂ) * ζ₀ = 0 := by linear_combination h
      exact hζ₀ ((mul_eq_zero.1 h2).resolve_left two_ne_zero)
    have h : ∀ᶠ s in 𝓝 (0 : ℂ), Zn s ≠ -Zp s :=
      (hcont.eventually_ne h0).mono fun s hs e => hs (by
        show Zn s + Zp s = 0
        rw [e, neg_add_cancel])
    exact eventually_nhdsGT_of_exists_Ioo (exists_forall_Ioo_of_eventually
      (P := fun s : ℂ => Zn s ≠ -Zp s) (h.filter_mono nhdsWithin_le_nhds))
  have htp : ∀ᶠ r : ℝ in 𝓝[>] 0, Transports (turnPath τ₀ r) (Zp r) (Zn r) := by
    have h := hc.exists_transports_turn hρp
    rw [← hZp, ← hZn] at h
    exact eventually_nhdsGT_of_exists_Ioo h
  have htn : ∀ᶠ r : ℝ in 𝓝[>] 0, Transports (turnPath τ₀ r) (Zn r) (Zp r) := by
    have h := hc.exists_transports_turn hρn
    rw [neg_neg, ← hZp, ← hZn] at h
    exact eventually_nhdsGT_of_exists_Ioo h
  filter_upwards [eventually_turnAction hτ₀, hreflA, hreflB, hdist, hsep, htp, htn] with
    r hact hA hB hr2 hr3 hr4 hr5
  refine ⟨Zp r, Zn r, hr2.symm, hr3, ?_, hr4, hr5, fun z hz n1 n2 n3 n4 => ?_⟩
  · have h := hr4.zero_left
    rwa [turnPath_zero] at h
  · rcases hact z hz with h | ⟨ζ, m, ρ', hm, hcz, hρ', hzeq, -⟩
    · exact h
    · exfalso
      rcases honly ζ
        (by have h := hcz.vanish 0 (by omega); rwa [iteratedDeriv_zero] at h)
        (by have h := hcz.vanish 1 (by omega); rwa [iteratedDeriv_one] at h) with rfl | rfl
      · have hm2 : m = 2 := by
          have h1 := isCollision_iff_analyticOrderAt.1 hcz
          have h2 := isCollision_iff_analyticOrderAt.1 hc
          rw [h1] at h2
          exact_mod_cast h2
        subst hm2
        rcases hroots ρ' hρ' with rfl | rfl
        · rw [← hZp] at hzeq
          exact n1 hzeq
        · rw [← hZn] at hzeq
          exact n3 hzeq
      · have hm2 : m = 2 := by
          have h1 := isCollision_iff_analyticOrderAt.1 hcz
          have h2 := isCollision_iff_analyticOrderAt.1 hc'
          rw [h1] at h2
          exact_mod_cast h2
        subst hm2
        rcases hroots ρ' hρ' with rfl | rfl
        · exact n4 (by rw [hzeq, ← hA, neg_neg])
        · exact n2 (by rw [hzeq, ← hB, neg_neg])

/-- **The turn around an isolated double collision off the centre is the exchange of two
pairs.** Let `H_τ₀` have a double zero at `ζ₀ ≠ 0` and no multiple zero besides `±ζ₀`. For all
small `r` the turn exchanges two zeros `w`, `w'` of `H_{τ₀+r²}` in distinct pairs, and fixes
every zero other than `±w`, `±w'`. -/
theorem eventually_turn_exchange (hτ₀ : 0 < τ₀.re) (hc : IsCollision τ₀ ζ₀ 2) (hζ₀ : ζ₀ ≠ 0)
    (honly : ∀ ζ : ℂ, complexHeat τ₀ ζ = 0 → deriv (complexHeat τ₀) ζ = 0 →
      ζ = ζ₀ ∨ ζ = -ζ₀) :
    ∀ᶠ r : ℝ in 𝓝[>] 0, ∃ w w' : ℂ, w' ≠ w ∧ w' ≠ -w ∧
      complexHeat (τ₀ + (r : ℂ) ^ 2) w = 0 ∧
      Transports (turnPath τ₀ r) w w' ∧ Transports (turnPath τ₀ r) w' w ∧
        ∀ z : ℂ, complexHeat (τ₀ + (r : ℂ) ^ 2) z = 0 → z ≠ w → z ≠ -w → z ≠ w' → z ≠ -w' →
          Transports (turnPath τ₀ r) z z := by
  -- the profile of order two has the roots `±√2`
  obtain ⟨x, hx0, hx⟩ : ∃ x : ℝ, x ≠ 0 ∧ profileRoots 2 = {x, -x} :=
    ⟨Real.sqrt 2, (Real.sqrt_pos.2 two_pos).ne', profileRoots_two⟩
  refine eventually_turn_exchange_of_roots hτ₀ hc hζ₀ honly (ρ₀ := (x : ℂ))
    (heatModelFwd_eq_zero_iff.2 ⟨x, by rw [hx]; exact Finset.mem_insert_self _ _, rfl⟩)
    (heatModelFwd_eq_zero_iff.2 ⟨-x, by
      rw [hx]
      exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _), Complex.ofReal_neg _⟩)
    (fun ρ' h => ?_) fun h => ?_
  · obtain ⟨y, hy, rfl⟩ := heatModelFwd_eq_zero_iff.1 h
    rw [hx, Finset.mem_insert, Finset.mem_singleton] at hy
    rcases hy with rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr (Complex.ofReal_neg _)
  · have h2 : (2 : ℂ) * (x : ℂ) = 0 := by linear_combination h
    rcases mul_eq_zero.1 h2 with h3 | h3
    · exact two_ne_zero h3
    · exact hx0 (Complex.ofReal_eq_zero.1 h3)

/-- **One isolated double collision off the centre gives every signed permutation.** If at some
forward time `τ₀` the family has a double zero at `ζ₀ ≠ 0` and no multiple zero besides `±ζ₀`,
then at every forward base time `b` off the branch times `G₊(b)` contains every permutation of
the zeros of `H_b` that commutes with `z ↦ −z` and moves finitely many zeros. -/
theorem mem_forwardMonodromy_of_isolated_double_collision (hτ₀ : 0 < τ₀.re)
    (hc : IsCollision τ₀ ζ₀ 2) (hζ₀ : ζ₀ ≠ 0)
    (honly : ∀ ζ : ℂ, complexHeat τ₀ ζ = 0 → deriv (complexHeat τ₀) ζ = 0 →
      ζ = ζ₀ ∨ ζ = -ζ₀) {b : ℂ} (hb₀ : 0 < b.re) (hb : b ∉ branchTimes)
    {w : Perm {z : ℂ // complexHeat b z = 0}}
    (hw : ∀ q, w (fibreNeg b q) = fibreNeg b (w q)) (hfin : {q | w q ≠ q}.Finite) :
    w ∈ forwardMonodromy b hb₀ hb := by
  obtain ⟨r₁, hr₁, hfwd⟩ := exists_isForwardPath_turnPath hτ₀
  obtain ⟨r₂, hr₂, hex⟩ :=
    exists_Ioo_of_eventually_nhdsGT (eventually_turn_exchange hτ₀ hc hζ₀ honly)
  have hmin : 0 < min r₁ r₂ := lt_min hr₁ hr₂
  obtain ⟨r, hrI₁, hrI₂⟩ : ∃ r, r ∈ Ioo (0 : ℝ) r₁ ∧ r ∈ Ioo (0 : ℝ) r₂ :=
    ⟨min r₁ r₂ / 2, ⟨by positivity, by linarith [min_le_left r₁ r₂]⟩,
      ⟨by positivity, by linarith [min_le_right r₁ r₂]⟩⟩
  have hγ := hfwd r hrI₁
  obtain ⟨u, u', hne, hne', huz, hT, hT', hfix⟩ := hex r hrI₂
  -- the base time of the turn
  have h00 : (0 : ℝ) ∈ Icc (0 : ℝ) 1 := left_mem_Icc.2 zero_le_one
  have hτ₁ : 0 < (τ₀ + (r : ℂ) ^ 2).re := by
    have h := hγ.re_pos 0 h00
    rwa [turnPath_zero] at h
  have hb₁ : τ₀ + (r : ℂ) ^ 2 ∉ branchTimes := by
    have h := hγ.simple 0 h00
    rwa [turnPath_zero] at h
  have hu'z : complexHeat (τ₀ + (r : ℂ) ^ 2) u' = 0 := by
    have h := hT'.zero_left
    rwa [turnPath_zero] at h
  -- the turn as an element of the group at its base time
  obtain ⟨σ, hσ, hact⟩ := hγ.exists_mem_forwardMonodromy (hτ := hτ₁) (hb := hb₁)
    (turnPath_zero τ₀ r) (turnPath_one τ₀ r)
  have hcomm := forwardMonodromy_commute_fibreNeg hσ
  refine mem_forwardMonodromy_of_exchange_mem_base hb₀ hb hτ₁ hb₁
    (x := ⟨u, huz⟩) (x' := ⟨u', hu'z⟩) (ε := σ)
    (fun h => hne (congrArg Subtype.val h)) (fun h => hne' (congrArg Subtype.val h))
    (Subtype.ext (hγ.transports_unique (hact ⟨u, huz⟩) hT))
    (Subtype.ext (hγ.transports_unique (hact ⟨u', hu'z⟩) hT'))
    (fun y => by
      have h := congrArg (fun g : Perm {z : ℂ // complexHeat (τ₀ + (r : ℂ) ^ 2) z = 0} => g y)
        hcomm
      exact h)
    (fun y k1 k2 k3 k4 => Subtype.ext (hγ.transports_unique (hact y)
      (hfix y.1 y.2 (fun h => k1 (Subtype.ext h)) (fun h => k2 (Subtype.ext h))
        (fun h => k3 (Subtype.ext h)) (fun h => k4 (Subtype.ext h))))) hσ hw hfin

end GaloisForLFunctions.GaloisTheoryOfZeros
