import GaloisForLFunctions.GaloisTheoryOfZeros.TheTurnAroundABranchTimeMovesOnlyTheSheetsOfItsCollisions

/-!
# The turn around a collision of one pair at the centre flips exactly one pair

Let `τ₀` be a forward time at which `H_τ₀` has a zero of order exactly two at the centre: one
pair `±z` collides there. Other collisions may happen at the same time, away from the centre.

**Theorem** (`eventually_turn_involution_one_flip`). For all small `r` the turn of radius `r²`
around `τ₀` exchanges one zero `w ≠ 0` of `H_{τ₀+r²}` with `−w`, and every other zero `z` with a
zero `z' ≠ −z` (possibly `z' = z`). So the turn is an involution of the fibre that carries
exactly one pair to itself with the sign reversed.

At every base time the forward monodromy group contains such an involution
(`exists_mem_forwardMonodromy_involution_one_flip`). It is an odd permutation of the zeros: one
transposition `(w −w)`, and the other exchanges come in the mirror pairs `(z z')(−z −z')`.

Proof. The far zeros return. Around every zero `ζ ≠ 0` of `H_τ₀` in a compact disc take a disc of
radius at most `|ζ|/2`: if `ζ` is simple the zeros near it return; if `ζ` is a collision the zeros
near it are its sheets, the turn carries the sheet `Z_ρ` to `Z_{−ρ}` and back, and both stay in
the disc (`IsCollision.eventually_turn_exchange`), which does not meet its mirror image. Near the
centre the zeros are the two sheets `±w`. The rest of the compact disc carries no zero
(`eventually_forall_zero_of_local`).
-/

open Complex Filter Topology Set Metric
open RHTower RHTower.DeBruijn
open GaloisForLFunctions.NodalGeometryOfTheDeBruijnFlow

namespace GaloisForLFunctions.GaloisTheoryOfZeros

noncomputable section
set_option autoImplicit false

variable {τ₀ : ℂ}

private theorem eq_zero_of_eq_neg_self {z : ℂ} (h : z = -z) : z = 0 := by
  have h2 : (2 : ℂ) * z = 0 := by linear_combination h
  exact (mul_eq_zero.1 h2).resolve_left two_ne_zero

/-! ## From local statements to the whole fibre -/

/-- **A property of the zeros near a time holds on the whole fibre if it holds locally.** If a
property of the zeros of `H_{τ₀+r²}` holds for the zeros beyond a radius `R` and, for every zero
`ζ` of `H_τ₀`, for the zeros in a disc around `ζ`, for all small `r`, then it holds for all zeros
for all small `r`: the rest of the disc of radius `R` carries no zero. -/
theorem eventually_forall_zero_of_local {A : ℝ → ℂ → Prop} {R : ℝ}
    (hfar : ∀ᶠ r : ℝ in 𝓝[>] 0, ∀ z : ℂ, complexHeat (τ₀ + (r : ℂ) ^ 2) z = 0 → R ≤ ‖z‖ → A r z)
    (hloc : ∀ ζ : ℂ, complexHeat τ₀ ζ = 0 → ∃ ρ > 0, ∀ᶠ r : ℝ in 𝓝[>] 0,
      ∀ z ∈ ball ζ ρ, complexHeat (τ₀ + (r : ℂ) ^ 2) z = 0 → A r z) :
    ∀ᶠ r : ℝ in 𝓝[>] 0, ∀ z : ℂ, complexHeat (τ₀ + (r : ℂ) ^ 2) z = 0 → A r z := by
  have hloc' : ∀ ζ : ℂ, ∃ ρ > 0, complexHeat τ₀ ζ = 0 → ∀ᶠ r : ℝ in 𝓝[>] 0,
      ∀ z ∈ ball ζ ρ, complexHeat (τ₀ + (r : ℂ) ^ 2) z = 0 → A r z := by
    intro ζ
    by_cases h0 : complexHeat τ₀ ζ = 0
    · obtain ⟨ρ, hρ, h⟩ := hloc ζ h0
      exact ⟨ρ, hρ, fun _ => h⟩
    · exact ⟨1, one_pos, fun h => absurd h h0⟩
  choose ρ hρ hP using hloc'
  have hfin := finite_zeros_closedBall τ₀ R
  -- outside the discs around the zeros of `H_τ₀`, the disc of radius `R` carries no zero of
  -- `H_τ` for `τ` near `τ₀`
  have hC : IsCompact (closedBall (0 : ℂ) R \
      ⋃ ζ ∈ {ζ : ℂ | ζ ∈ closedBall (0 : ℂ) R ∧ complexHeat τ₀ ζ = 0}, ball ζ (ρ ζ)) :=
    (isCompact_closedBall 0 R).diff (isOpen_biUnion fun _ _ => isOpen_ball)
  have hfree : ∀ᶠ τ in 𝓝 τ₀, ∀ z ∈ closedBall (0 : ℂ) R \
      ⋃ ζ ∈ {ζ : ℂ | ζ ∈ closedBall (0 : ℂ) R ∧ complexHeat τ₀ ζ = 0}, ball ζ (ρ ζ),
      complexHeat τ z ≠ 0 := by
    refine hC.eventually_forall_of_forall_eventually fun z hz => ?_
    have hz0 : complexHeat τ₀ z ≠ 0 := fun h => hz.2
      (mem_biUnion (show z ∈ {ζ : ℂ | ζ ∈ closedBall (0 : ℂ) R ∧ complexHeat τ₀ ζ = 0} from
        ⟨hz.1, h⟩) (mem_ball_self (hρ z)))
    exact continuous_complexHeat.continuousAt.eventually_ne hz0
  have hfree' := (tendsto_add_ofReal_sq τ₀).eventually hfree
  have hnear := (eventually_all_finite hfin).2 fun ζ hζ => hP ζ hζ.2
  filter_upwards [hfar, hfree', hnear] with r hr1 hr2 hr3 z hzero
  by_cases hzR : R ≤ ‖z‖
  · exact hr1 z hzero hzR
  · have hzb : z ∈ closedBall (0 : ℂ) R := mem_closedBall_zero_iff.2 (not_le.1 hzR).le
    by_contra hcon
    refine hr2 z ⟨hzb, fun hmem => hcon ?_⟩ hzero
    obtain ⟨ζ, hζ, hzζ⟩ := mem_iUnion₂.1 hmem
    exact hr3 ζ hζ z hzζ hzero

/-! ## The turn near a collision -/

/-- A profile has finitely many roots. -/
theorem finite_setOf_heatModelFwd_eq_zero (m : ℕ) : {ρ : ℂ | heatModelFwd m ρ = 0}.Finite := by
  have hset : {ρ : ℂ | heatModelFwd m ρ = 0} =
      (fun x : ℝ => (x : ℂ)) '' (profileRoots m : Set ℝ) := by
    ext ρ
    simp only [mem_setOf_eq, mem_image, Finset.mem_coe]
    exact heatModelFwd_eq_zero_iff
  rw [hset]
  exact (Finset.finite_toSet _).image _

/-- **Near a collision the turn exchanges the zeros inside a small disc.** For every `ε > 0`
there is a disc around `ζ` such that for small `r` the turn carries every zero of the disc to a
zero within `ε` of `ζ`, and that zero back. -/
theorem IsCollision.eventually_turn_exchange {ζ : ℂ} {m : ℕ} (hc : IsCollision τ₀ ζ m) {ε : ℝ}
    (hε : 0 < ε) :
    ∃ ρ > 0, ∀ᶠ r : ℝ in 𝓝[>] 0, ∀ z ∈ ball ζ ρ, complexHeat (τ₀ + (r : ℂ) ^ 2) z = 0 →
      ∃ z' ∈ ball ζ ε, Transports (turnPath τ₀ r) z z' ∧ Transports (turnPath τ₀ r) z' z := by
  obtain ⟨ρ, hρ, hev⟩ := eventually_turn_transports_sheets hc
  refine ⟨ρ, hρ, ?_⟩
  have hfin := finite_setOf_heatModelFwd_eq_zero m
  have hneg : ∀ ρ' : ℂ, heatModelFwd m ρ' = 0 → heatModelFwd m (-ρ') = 0 := fun ρ' h => by
    rw [heatModelFwd_neg, h, mul_zero]
  -- the opposite sheet is carried back
  have hback : ∀ᶠ r : ℝ in 𝓝[>] 0, ∀ ρ' ∈ {ρ' : ℂ | heatModelFwd m ρ' = 0},
      Transports (turnPath τ₀ r) (collisionZero τ₀ ζ m (-ρ') r) (collisionZero τ₀ ζ m ρ' r) :=
    (eventually_all_finite hfin).2 fun ρ' hρ' => by
      have h := eventually_nhdsGT_of_exists_Ioo (hc.exists_transports_turn (hneg ρ' hρ'))
      simpa only [neg_neg] using h
  -- the sheets are close to the collision
  have hcast : Tendsto (fun r : ℝ => (r : ℂ)) (𝓝[>] 0) (𝓝 0) := by
    have h := Complex.continuous_ofReal.tendsto 0
    rw [Complex.ofReal_zero] at h
    exact h.mono_left nhdsWithin_le_nhds
  have hclose : ∀ᶠ r : ℝ in 𝓝[>] 0, ∀ ρ' ∈ {ρ' : ℂ | heatModelFwd m ρ' = 0},
      collisionZero τ₀ ζ m (-ρ') r ∈ ball ζ ε :=
    (eventually_all_finite hfin).2 fun ρ' hρ' => by
      have h := (hc.continuousAt_collisionZero (hneg ρ' hρ')).tendsto.comp hcast
      rw [collisionZero_zero] at h
      exact h.eventually (ball_mem_nhds ζ hε)
  filter_upwards [hev, hback, hclose] with r hr1 hr2 hr3 z hz hzero
  obtain ⟨ρ', hρ', rfl, hT⟩ := hr1 z hz hzero
  exact ⟨_, hr3 ρ' hρ', hT, hr2 ρ' hρ'⟩

/-! ## A collision of one pair at the centre -/

/-- **The turn around a collision of one pair at the centre.** Let `H_τ₀` have a zero of order
two at the centre. For all small `r` the turn exchanges one zero `w ≠ 0` of `H_{τ₀+r²}` with
`−w`, and every other zero `z` with a zero `z' ≠ −z`. -/
theorem eventually_turn_involution_one_flip (hτ₀ : 0 < τ₀.re) (hcen : IsCollision τ₀ 0 2) :
    ∀ᶠ r : ℝ in 𝓝[>] 0, ∃ w : ℂ, w ≠ 0 ∧ complexHeat (τ₀ + (r : ℂ) ^ 2) w = 0 ∧
      Transports (turnPath τ₀ r) w (-w) ∧ Transports (turnPath τ₀ r) (-w) w ∧
        ∀ z : ℂ, complexHeat (τ₀ + (r : ℂ) ^ 2) z = 0 → z ≠ w → z ≠ -w →
          ∃ z' : ℂ, Transports (turnPath τ₀ r) z z' ∧ Transports (turnPath τ₀ r) z' z ∧
            z' ≠ -z := by
  -- the profile of order two has the roots `±√2`
  obtain ⟨x, hx0, hx⟩ : ∃ x : ℝ, x ≠ 0 ∧ profileRoots 2 = {x, -x} :=
    ⟨Real.sqrt 2, (Real.sqrt_pos.2 two_pos).ne', profileRoots_two⟩
  have hρp : heatModelFwd 2 (x : ℂ) = 0 :=
    heatModelFwd_eq_zero_iff.2 ⟨x, by rw [hx]; exact Finset.mem_insert_self _ _, rfl⟩
  have hρn : heatModelFwd 2 (-(x : ℂ)) = 0 :=
    heatModelFwd_eq_zero_iff.2 ⟨-x, by
      rw [hx]
      exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _), Complex.ofReal_neg _⟩
  have hroots : ∀ ρ' : ℂ, heatModelFwd 2 ρ' = 0 → ρ' = (x : ℂ) ∨ ρ' = -(x : ℂ) := by
    intro ρ' h
    obtain ⟨y, hy, rfl⟩ := heatModelFwd_eq_zero_iff.1 h
    rw [hx, Finset.mem_insert, Finset.mem_singleton] at hy
    rcases hy with rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr (Complex.ofReal_neg _)
  have hne : (x : ℂ) ≠ -(x : ℂ) := fun h =>
    hx0 (Complex.ofReal_eq_zero.1 (eq_zero_of_eq_neg_self h))
  -- the two sheets at the centre
  obtain ⟨Zp, hZp⟩ : ∃ Zp : ℂ → ℂ, Zp = collisionZero τ₀ 0 2 (x : ℂ) := ⟨_, rfl⟩
  obtain ⟨Zn, hZn⟩ : ∃ Zn : ℂ → ℂ, Zn = collisionZero τ₀ 0 2 (-(x : ℂ)) := ⟨_, rfl⟩
  have hrefl : ∀ᶠ r : ℝ in 𝓝[>] 0, -Zp r = Zn r := by
    have h := collisionZero_reflect hcen hρp
    rw [neg_zero, ← hZp, ← hZn] at h
    exact eventually_nhdsGT_of_exists_Ioo (exists_forall_Ioo_of_eventually
      (P := fun s : ℂ => -Zp s = Zn s) (h.filter_mono nhdsWithin_le_nhds))
  have hdist : ∀ᶠ r : ℝ in 𝓝[>] 0, Zp r ≠ Zn r := by
    have h := collisionZero_ne hcen hρp hρn hne
    rw [← hZp, ← hZn] at h
    exact eventually_nhdsGT_of_exists_Ioo (exists_forall_Ioo_of_eventually
      (P := fun s : ℂ => Zp s ≠ Zn s) h)
  have htp : ∀ᶠ r : ℝ in 𝓝[>] 0, Transports (turnPath τ₀ r) (Zp r) (Zn r) := by
    have h := hcen.exists_transports_turn hρp
    rw [← hZp, ← hZn] at h
    exact eventually_nhdsGT_of_exists_Ioo h
  have htn : ∀ᶠ r : ℝ in 𝓝[>] 0, Transports (turnPath τ₀ r) (Zn r) (Zp r) := by
    have h := hcen.exists_transports_turn hρn
    rw [neg_neg, ← hZp, ← hZn] at h
    exact eventually_nhdsGT_of_exists_Ioo h
  -- every zero is a central sheet, or it is exchanged with a zero that is not its negative
  have hall : ∀ᶠ r : ℝ in 𝓝[>] 0, ∀ z : ℂ, complexHeat (τ₀ + (r : ℂ) ^ 2) z = 0 →
      z = Zp r ∨ z = Zn r ∨ ∃ z' : ℂ, Transports (turnPath τ₀ r) z z' ∧
        Transports (turnPath τ₀ r) z' z ∧ z' ≠ -z := by
    obtain ⟨R, hfar⟩ := eventually_turn_transports_self_of_far hτ₀
    refine eventually_forall_zero_of_local (R := max R 1) ?_ fun ζ h0 => ?_
    · -- the far zeros return, and they are not the centre
      filter_upwards [hfar] with r hr z hz hzR
      have hT := hr z hz ((le_max_left _ _).trans hzR)
      refine Or.inr (Or.inr ⟨z, hT, hT, fun h => ?_⟩)
      rw [eq_zero_of_eq_neg_self h, norm_zero] at hzR
      linarith [le_max_right R 1]
    · by_cases hζ : ζ = 0
      · -- near the centre the zeros are the two sheets
        subst hζ
        obtain ⟨ρ, hρ, hev⟩ := eventually_turn_transports_sheets hcen
        refine ⟨ρ, hρ, hev.mono fun r hr z hz hzero => ?_⟩
        obtain ⟨ρ', hρ', hzeq, -⟩ := hr z hz hzero
        rcases hroots ρ' hρ' with rfl | rfl
        · exact Or.inl (by rw [hZp]; exact hzeq)
        · exact Or.inr (Or.inl (by rw [hZn]; exact hzeq))
      · have hζn : 0 < ‖ζ‖ / 2 := half_pos (norm_pos_iff.mpr hζ)
        by_cases h1 : deriv (complexHeat τ₀) ζ = 0
        · -- a collision away from the centre: the exchange stays near `ζ`, away from `−ζ`
          obtain ⟨m, -, hc⟩ := exists_isCollision_two_le h0 h1
          obtain ⟨ρ, hρ, hev⟩ := hc.eventually_turn_exchange hζn
          refine ⟨min ρ (‖ζ‖ / 2), lt_min hρ hζn, hev.mono fun r hr z hz hzero => ?_⟩
          obtain ⟨z', hz', hT, hT'⟩ := hr z (ball_subset_ball (min_le_left _ _) hz) hzero
          refine Or.inr (Or.inr ⟨z', hT, hT', fun h => ?_⟩)
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
          refine Or.inr (Or.inr ⟨z, hT, hT, fun h => ?_⟩)
          have hz2 := ball_subset_ball (min_le_right ρ (‖ζ‖ / 2)) hz
          rw [eq_zero_of_eq_neg_self h, mem_ball, dist_eq_norm, zero_sub, norm_neg] at hz2
          linarith
  filter_upwards [hall, hrefl, hdist, htp, htn] with r hact hr1 hr2 hr3 hr4
  rw [← hr1] at hr2 hr3 hr4
  refine ⟨Zp r, fun hw => hr2 ?_, ?_, hr3, hr4, fun z hz hzw hzw' => ?_⟩
  · rw [hw, neg_zero]
  · have h := hr3.zero_left
    rwa [turnPath_zero] at h
  · rcases hact z hz with h | h | h
    · exact absurd h hzw
    · exact absurd (h.trans hr1.symm) hzw'
    · exact h

/-- **An involution with exactly one flipped pair is a forward monodromy.** If at some forward
time `τ₀` the family has a zero of order two at the centre, then at every base time the forward
monodromy group contains an involution `σ` with `σp = −p` for one zero `p` and `σq ≠ −q` for
every zero `q ≠ ±p`. -/
theorem exists_mem_forwardMonodromy_involution_one_flip (hτ₀ : 0 < τ₀.re)
    (hcen : IsCollision τ₀ 0 2) {τ : ℂ} (hτ : 0 < τ.re) (hb : τ ∉ branchTimes) :
    ∃ σ ∈ forwardMonodromy τ hτ hb, ∃ p : {z : ℂ // complexHeat τ z = 0},
      σ p = fibreNeg τ p ∧ (∀ q, σ (σ q) = q) ∧
        ∀ q, q ≠ p → q ≠ fibreNeg τ p → σ q ≠ fibreNeg τ q := by
  obtain ⟨r₁, hr₁, hfwd⟩ := exists_isForwardPath_turnPath hτ₀
  obtain ⟨r₂, hr₂, hflip⟩ :=
    exists_Ioo_of_eventually_nhdsGT (eventually_turn_involution_one_flip hτ₀ hcen)
  have hmin : 0 < min r₁ r₂ := lt_min hr₁ hr₂
  obtain ⟨r, hrI₁, hrI₂⟩ : ∃ r, r ∈ Ioo (0 : ℝ) r₁ ∧ r ∈ Ioo (0 : ℝ) r₂ :=
    ⟨min r₁ r₂ / 2, ⟨half_pos hmin, by linarith [min_le_left r₁ r₂]⟩,
      ⟨half_pos hmin, by linarith [min_le_right r₁ r₂]⟩⟩
  have hγ := hfwd r hrI₁
  obtain ⟨w, -, hwz, hTp, hTn, hrest⟩ := hflip r hrI₂
  obtain ⟨δ, hδ, hδ0, hδ1, σ, hσ, hact⟩ :=
    hγ.exists_mem_forwardMonodromy_of_loop (by rw [turnPath_one, turnPath_zero]) hτ hb
  -- `p` is the transport of `w` to the base time
  obtain ⟨z₁, hz₁⟩ := hδ.exists_transports (z₀ := w) (by rw [hδ0, turnPath_zero]; exact hwz)
  have hz₁0 : complexHeat τ z₁ = 0 := by
    have h := hz₁.zero_right
    rwa [hδ1] at h
  obtain ⟨e, he⟩ := hδ.exists_fibreEquiv (hδ0.trans (turnPath_zero τ₀ r)) hδ1
  -- every zero of the base fibre is the transport of a zero of the fibre of the turn
  have hsrc : ∀ q : {z : ℂ // complexHeat τ z = 0}, ∃ z : ℂ,
      complexHeat (τ₀ + (r : ℂ) ^ 2) z = 0 ∧ Transports δ z q.1 := by
    intro q
    have h := he (e.symm q)
    rw [e.apply_symm_apply] at h
    exact ⟨_, (e.symm q).2, h⟩
  -- the turn exchanges every zero with a zero
  have hpair : ∀ z : ℂ, complexHeat (τ₀ + (r : ℂ) ^ 2) z = 0 → ∃ z' : ℂ,
      Transports (turnPath τ₀ r) z z' ∧ Transports (turnPath τ₀ r) z' z ∧
        (z ≠ w → z ≠ -w → z' ≠ -z) := by
    intro z hz
    by_cases hzw : z = w
    · exact ⟨-w, by rw [hzw]; exact hTp, by rw [hzw]; exact hTn, fun h => absurd hzw h⟩
    by_cases hzw' : z = -w
    · exact ⟨w, by rw [hzw']; exact hTn, by rw [hzw']; exact hTp, fun _ h => absurd hzw' h⟩
    · obtain ⟨z', h1, h2, h3⟩ := hrest z hz hzw hzw'
      exact ⟨z', h1, h2, fun _ _ => h3⟩
  refine ⟨σ, hσ, ⟨z₁, hz₁0⟩, Subtype.ext ?_, fun q => ?_, fun q hq hq' hflipq => ?_⟩
  · exact hδ.transports_unique (hact w (-w) hTp ⟨z₁, hz₁0⟩ hz₁) hz₁.neg
  · -- the turn twice is the identity
    obtain ⟨z, hz0, hzq⟩ := hsrc q
    obtain ⟨z', h1, h2, -⟩ := hpair z hz0
    exact Subtype.ext (hδ.transports_unique (hact z' z h2 (σ q) (hact z z' h1 q hzq)) hzq)
  · -- a zero carried to its negative comes from `±w`
    obtain ⟨z, hz0, hzq⟩ := hsrc q
    have hzw : z ≠ w := by
      rintro rfl
      exact hq (Subtype.ext (hδ.transports_unique hzq hz₁))
    have hzw' : z ≠ -w := by
      rintro rfl
      exact hq' (Subtype.ext (hδ.transports_unique hzq hz₁.neg))
    obtain ⟨z', h1, -, h3⟩ := hpair z hz0
    have h4 := hact z z' h1 q hzq
    have h6 : (σ q).1 = -q.1 := congrArg Subtype.val hflipq
    rw [h6] at h4
    exact h3 hzw hzw' (hδ.transports_injective h4 hzq.neg)

end

end GaloisForLFunctions.GaloisTheoryOfZeros
