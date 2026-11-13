import GaloisForLFunctions.GaloisTheoryOfZeros.TheHermiteMonodromyOfACollision
import GaloisForLFunctions.RHTower.XiCosineShiftExceptionalPointCriterion

/-!
# The sheets of a collision are all its zeros

Let `(τ₀, z₀)` be a collision of exact order `m` of the heat family. There is a disc around `z₀` in
which, for every small `s ≠ 0`, the zeros of `H_{τ₀+s²}` are exactly the `m` points
`Z_ρ(s) = z₀ + s y_ρ(s)`, one for each root `ρ` of the Hermite profile, and every one of them is
simple (`exists_ball_zeros_eq_sheets`). In the time variable: at every time `τ ≠ τ₀` near `τ₀` the
disc contains exactly `m` zeros of `H_τ`, all simple (`exists_ball_simple_zeros`).

So near a collision the zeros form an `m`-sheeted cover of the punctured time disc with the sheets
`Z_ρ`. It is unramified, and its monodromy is the reflection `ρ ↦ −ρ`.

Since every zero of the family is a collision of some order, the multiple zeros of the family are
isolated points of `ℂ²` (`discreteTopology_multipleZeros`). Hence the heat cover has countably many
branch points, and at all but countably many complex times every zero is simple
(`countable_branchTimes`).

The proof of the exhaustion counts. The disc carries total multiplicity `m` for `H_τ₀`, and the
count is stable under the small uniform perturbation `H_{τ₀+s²}`. The `m` sheets are distinct zeros
in the disc, so they exhaust the count and each has multiplicity one.
-/

open Complex Filter Topology Set Metric
open RHTower RHTower.DeBruijn GaloisForLFunctions.HTGeometry
open GaloisForLFunctions.NodalGeometryOfTheDeBruijnFlow

namespace GaloisForLFunctions.GaloisTheoryOfZeros

noncomputable section
set_option autoImplicit false

/-- On a closed disc the family at the time `τ₀ + s²` is uniformly close to `H_τ₀` for small `s`. -/
theorem eventually_norm_complexHeat_sub_le (τ₀ c : ℂ) (R : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ s in 𝓝 (0 : ℂ), ∀ z ∈ closedBall c R,
      ‖complexHeat (τ₀ + s ^ 2) z - complexHeat τ₀ z‖ ≤ ε := by
  refine (isCompact_closedBall c R).eventually_forall_of_forall_eventually fun z₁ _ => ?_
  have h1 : Continuous fun q : ℂ × ℂ => complexHeat (τ₀ + q.1 ^ 2) q.2 :=
    continuous_complexHeat.comp (by fun_prop : Continuous fun q : ℂ × ℂ => (τ₀ + q.1 ^ 2, q.2))
  have h2 : Continuous fun q : ℂ × ℂ => complexHeat τ₀ q.2 :=
    continuous_complexHeat.comp (by fun_prop : Continuous fun q : ℂ × ℂ => (τ₀, q.2))
  have hcont : Continuous fun q : ℂ × ℂ =>
      ‖complexHeat (τ₀ + q.1 ^ 2) q.2 - complexHeat τ₀ q.2‖ := (h1.sub h2).norm
  have h0 : ‖complexHeat (τ₀ + (0 : ℂ) ^ 2) z₁ - complexHeat τ₀ z₁‖ < ε := by
    rw [zero_pow two_ne_zero, add_zero, sub_self, norm_zero]
    exact hε
  filter_upwards [(hcont.tendsto ((0 : ℂ), z₁)).eventually (eventually_lt_nhds h0)] with q hq
  exact hq.le

variable {τ₀ z₀ : ℂ} {m : ℕ}

/-- **Exhaustion.** Near a collision of order `m`, for small `s ≠ 0` the zeros of `H_{τ₀+s²}` are
exactly the `m` sheets `Z_ρ(s)`, each of them is simple, and there are `m` of them. At the time
`τ₀` itself the centre is the only zero in the disc. -/
theorem exists_ball_zeros_eq_sheets (hc : IsCollision τ₀ z₀ m) :
    ∃ r > 0, (∀ z ∈ ball z₀ r, complexHeat τ₀ z = 0 → z = z₀) ∧
      ∀ᶠ s in 𝓝[≠] (0 : ℂ),
        (∀ z ∈ ball z₀ r, complexHeat (τ₀ + s ^ 2) z = 0 ↔
          ∃ ρ, heatModelFwd m ρ = 0 ∧ z = collisionZero τ₀ z₀ m ρ s) ∧
        (∀ z ∈ ball z₀ r, complexHeat (τ₀ + s ^ 2) z = 0 →
          deriv (complexHeat (τ₀ + s ^ 2)) z ≠ 0) ∧
        {z | z ∈ ball z₀ r ∧ complexHeat (τ₀ + s ^ 2) z = 0}.ncard = m := by
  classical
  have hf : Differentiable ℂ (complexHeat τ₀) := differentiable_complexHeat τ₀
  have hfin : ∀ z, analyticOrderAt (complexHeat τ₀) z ≠ ⊤ := analyticOrderAt_complexHeat_ne_top τ₀
  have hm : zeroMult (complexHeat τ₀) z₀ = m := by
    rw [zeroMult, isCollision_iff_analyticOrderAt.mp hc, ENat.toNat_coe]
  -- an isolating disc: it carries the multiplicity `m`, and the count is stable
  obtain ⟨r, hr, hiso⟩ := exists_radius_zeroSumBall_eq_zeroMult hf hfin z₀
  obtain ⟨hsph, hcount⟩ := hiso r hr le_rfl
  rw [hm] at hcount
  obtain ⟨ε, hε, hstable⟩ := exists_eps_zeroSumBall_eq hr (by linarith : r < 2 * r) isOpen_univ
    (subset_univ _) hf.differentiableOn hsph
  have huniq : ∀ z ∈ ball z₀ r, complexHeat τ₀ z = 0 → z = z₀ := by
    intro z hz hz0
    by_contra hne
    exact (hiso (dist z z₀) (dist_pos.mpr hne) (mem_ball.mp hz).le).1 z (mem_sphere.mpr rfl) hz0
  refine ⟨r, hr, huniq, ?_⟩
  -- the roots of the profile
  set T : Finset ℂ := (profileRoots m).image fun x : ℝ => (x : ℂ) with hT
  have hTcard : T.card = m := by
    rw [hT, Finset.card_image_of_injective _ Complex.ofReal_injective, card_profileRoots]
  have hTroot : ∀ ρ, ρ ∈ T ↔ heatModelFwd m ρ = 0 := fun ρ => by
    rw [hT, Finset.mem_image, heatModelFwd_eq_zero_iff]
  -- the sheets are zeros, lie in the disc, and are distinct
  have hzero : ∀ᶠ s in 𝓝 (0 : ℂ), ∀ ρ ∈ T,
      complexHeat (τ₀ + s ^ 2) (collisionZero τ₀ z₀ m ρ s) = 0 :=
    (eventually_all_finset T).mpr fun ρ hρ => complexHeat_collisionZero hc ((hTroot ρ).mp hρ)
  have hball : ∀ᶠ s in 𝓝 (0 : ℂ), ∀ ρ ∈ T, collisionZero τ₀ z₀ m ρ s ∈ ball z₀ r :=
    (eventually_all_finset T).mpr fun ρ hρ => by
      have han := (collisionBranch_spec hc ((hTroot ρ).mp hρ)).1.continuousAt
      have hcz : ContinuousAt (fun s => z₀ + s * collisionBranch τ₀ z₀ m ρ s) 0 :=
        continuousAt_const.add (continuousAt_id.mul han)
      have h0 : z₀ + (0 : ℂ) * collisionBranch τ₀ z₀ m ρ 0 = z₀ := by rw [zero_mul, add_zero]
      have hlim := hcz.tendsto
      rw [h0] at hlim
      exact hlim.eventually (ball_mem_nhds z₀ hr)
  have hdist : ∀ᶠ s in 𝓝[≠] (0 : ℂ), ∀ ρ ∈ T, ∀ ρ' ∈ T, ρ ≠ ρ' →
      collisionZero τ₀ z₀ m ρ s ≠ collisionZero τ₀ z₀ m ρ' s :=
    (eventually_all_finset T).mpr fun ρ hρ => (eventually_all_finset T).mpr fun ρ' hρ' => by
      by_cases h : ρ = ρ'
      · exact Eventually.of_forall fun s hne => absurd h hne
      · exact (collisionZero_ne hc ((hTroot ρ).mp hρ) ((hTroot ρ').mp hρ') h).mono
          fun s hs _ => hs
  have hclose := eventually_norm_complexHeat_sub_le τ₀ z₀ (2 * r) hε
  filter_upwards [hzero.filter_mono nhdsWithin_le_nhds, hball.filter_mono nhdsWithin_le_nhds,
    hclose.filter_mono nhdsWithin_le_nhds, hdist] with s hz hb hcl hd
  set F : ℂ → ℂ := complexHeat (τ₀ + s ^ 2) with hF
  have hFd : Differentiable ℂ F := differentiable_complexHeat _
  obtain ⟨hFsph, hFcount⟩ := hstable F hFd.differentiableOn hcl
  rw [hcount] at hFcount
  obtain ⟨Z, hZball, hZzero, hZsum⟩ := exists_zeroSet_zeroSumBall hr (by linarith : r < 2 * r)
    isOpen_univ (subset_univ _) hFd.differentiableOn hFsph
  rw [hFcount] at hZsum
  have hsumN : ∑ z ∈ Z, zeroMult F z = m := by exact_mod_cast hZsum.symm
  have hFfin : ∀ z, analyticOrderAt F z ≠ ⊤ := analyticOrderAt_complexHeat_ne_top _
  -- the `m` sheets exhaust the count
  set W : Finset ℂ := T.image fun ρ => collisionZero τ₀ z₀ m ρ s with hW
  have hWcard : W.card = m := by
    rw [hW, Finset.card_image_of_injOn, hTcard]
    intro ρ hρ ρ' hρ' heq
    by_contra hne
    exact hd ρ hρ ρ' hρ' hne heq
  have hWZ : W ⊆ Z := by
    intro w hw
    obtain ⟨ρ, hρ, rfl⟩ := Finset.mem_image.mp hw
    exact (hZzero _ (hb ρ hρ)).mp (hz ρ hρ)
  have hone : ∀ z ∈ Z, 1 ≤ zeroMult F z := fun z hzZ =>
    one_le_zeroMult_of_eq_zero hFd hFfin ((hZzero z (hZball z hzZ)).mpr hzZ)
  have hZcard : Z.card ≤ m := by
    rw [← hsumN, Finset.card_eq_sum_ones]
    exact Finset.sum_le_sum hone
  have hWeq : W = Z := Finset.eq_of_subset_of_card_le hWZ (by rw [hWcard]; exact hZcard)
  have hcardeq : Z.card = m := by rw [← hWeq, hWcard]
  refine ⟨fun z hzb => ?_, fun z hzb hz0 => ?_, ?_⟩
  · rw [hZzero z hzb, ← hWeq, hW, Finset.mem_image]
    constructor
    · rintro ⟨ρ, hρ, rfl⟩
      exact ⟨ρ, (hTroot ρ).mp hρ, rfl⟩
    · rintro ⟨ρ, hρ, rfl⟩
      exact ⟨ρ, (hTroot ρ).mpr hρ, rfl⟩
  · have hzZ := (hZzero z hzb).mp hz0
    -- the count leaves multiplicity one for each zero
    have hmult : zeroMult F z = 1 := by
      by_contra hne
      have h1 := hone z hzZ
      have hsplit := Finset.sum_erase_add Z (fun w => zeroMult F w) hzZ
      have hrest : (Z.erase z).card ≤ ∑ w ∈ Z.erase z, zeroMult F w := by
        rw [Finset.card_eq_sum_ones]
        exact Finset.sum_le_sum fun w hw => hone w (Finset.mem_of_mem_erase hw)
      have hce := Finset.card_erase_add_one hzZ
      omega
    have hord : analyticOrderAt F z = ((1 : ℕ) : ℕ∞) := by
      rw [← ENat.coe_toNat (hFfin z)]
      exact congrArg (fun n : ℕ => (n : ℕ∞)) hmult
    have h1 := ((analyticOrderAt_eq_nat_iff_iteratedDeriv_eq_zero (hFd.analyticAt z)).mp hord).2
    rwa [iteratedDeriv_one] at h1
  · have hset : {z | z ∈ ball z₀ r ∧ F z = 0} = (Z : Set ℂ) := by
      ext z
      exact ⟨fun h => (hZzero z h.1).mp h.2,
        fun h => ⟨hZball z h, (hZzero z (hZball z h)).mpr h⟩⟩
    rw [hset, Set.ncard_coe_finset, hcardeq]

/-- **The cover near a collision.** At every time `τ ≠ τ₀` near a collision of order `m` the disc
contains exactly `m` zeros of `H_τ`, all simple; at `τ₀` it contains only the centre. -/
theorem exists_ball_simple_zeros (hc : IsCollision τ₀ z₀ m) :
    ∃ r > 0, (∀ z ∈ ball z₀ r, complexHeat τ₀ z = 0 → z = z₀) ∧
      ∀ᶠ τ in 𝓝[≠] τ₀,
        (∀ z ∈ ball z₀ r, complexHeat τ z = 0 → deriv (complexHeat τ) z ≠ 0) ∧
        {z | z ∈ ball z₀ r ∧ complexHeat τ z = 0}.ncard = m := by
  obtain ⟨r, hr, huniq, hev⟩ := exists_ball_zeros_eq_sheets hc
  refine ⟨r, hr, huniq, ?_⟩
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhdsWithin_iff.mp hev
  rw [eventually_nhdsWithin_iff]
  filter_upwards [ball_mem_nhds τ₀ (pow_pos hδ 2)] with τ hτ hne
  -- every nearby time is `τ₀ + s²` with `s` small and nonzero
  obtain ⟨s, hs⟩ := IsAlgClosed.exists_pow_nat_eq (τ - τ₀) (n := 2) two_pos
  have hs0 : s ≠ 0 := by
    rintro rfl
    exact hne (sub_eq_zero.mp (by rw [← hs]; ring))
  have hsδ : ‖s‖ < δ := by
    refine lt_of_pow_lt_pow_left₀ 2 hδ.le ?_
    rw [← norm_pow, hs, ← dist_eq_norm]
    exact hτ
  have hP := hball ⟨mem_ball_zero_iff.mpr hsδ, hs0⟩
  rw [show τ = τ₀ + s ^ 2 by rw [hs]; ring]
  exact ⟨hP.2.1, hP.2.2⟩

/-! ## The branch points of the heat cover -/

/-- The multiple zeros of the heat family: the branch points of the heat cover. -/
def multipleZeros : Set (ℂ × ℂ) :=
  {p | complexHeat p.1 p.2 = 0 ∧ deriv (complexHeat p.1) p.2 = 0}

/-- The branch times: the complex times at which the family has a multiple zero. -/
def branchTimes : Set ℂ := Prod.fst '' multipleZeros

/-- **The branch points are isolated.** Every multiple zero of the family has a neighbourhood in
`ℂ²` that contains no other multiple zero. -/
theorem discreteTopology_multipleZeros : DiscreteTopology multipleZeros := by
  refine discreteTopology_subtype_iff'.mpr fun p hp => ?_
  obtain ⟨τ₀, z₀⟩ := p
  obtain ⟨m, -, hc⟩ := exists_isCollision hp.1
  obtain ⟨r, hr, huniq, hev⟩ := exists_ball_simple_zeros hc
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhdsWithin_iff.mp hev
  refine ⟨ball τ₀ ε ×ˢ ball z₀ r, isOpen_ball.prod isOpen_ball, ?_⟩
  ext q
  obtain ⟨τ, z⟩ := q
  simp only [mem_inter_iff, mem_prod, mem_singleton_iff, Prod.mk.injEq]
  constructor
  · rintro ⟨⟨hτ, hz⟩, hq⟩
    by_cases hτ0 : τ = τ₀
    · subst hτ0
      exact ⟨rfl, huniq z hz hq.1⟩
    · exact absurd hq.2 ((hball ⟨hτ, hτ0⟩).1 z hz hq.1)
  · rintro ⟨rfl, rfl⟩
    exact ⟨⟨mem_ball_self hε, mem_ball_self hr⟩, hp⟩

/-- **The heat cover has countably many branch points.** -/
theorem countable_multipleZeros : multipleZeros.Countable := by
  haveI := discreteTopology_multipleZeros
  exact Set.countable_coe_iff.mp
    (TopologicalSpace.separableSpace_iff_countable.mp inferInstance)

/-- **At all but countably many complex times every zero of the heat family is simple.** -/
theorem countable_branchTimes : branchTimes.Countable :=
  countable_multipleZeros.image _

theorem deriv_complexHeat_ne_zero_of_not_mem_branchTimes {τ z : ℂ} (hτ : τ ∉ branchTimes)
    (hz : complexHeat τ z = 0) : deriv (complexHeat τ) z ≠ 0 :=
  fun h => hτ ⟨(τ, z), ⟨hz, h⟩, rfl⟩

end

end GaloisForLFunctions.GaloisTheoryOfZeros
