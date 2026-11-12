import GaloisForLFunctions.GaloisTheoryOfZeros.TheHermiteMonodromyOfACollision
import GaloisForLFunctions.RHTower.XiCosineShiftExceptionalPointCriterion

/-!
# The sheets of a collision are all its zeros

Let `(t, z₀)` be a collision of exact order `m` of the heat family. There is a disc around `z₀` in
which, for every small `s ≠ 0`, the zeros of `H_{t+s²}` are exactly the `m` points
`Z_ρ(s) = z₀ + s y_ρ(s)`, one for each root `ρ` of the Hermite profile, and every one of them is
simple (`exists_ball_zeros_eq_sheets`).

So near a collision the cover of zeros over the time plane is the `m`-sheeted cover with the sheets
`Z_ρ`. It is unramified away from the collision time, and its monodromy is the reflection
`ρ ↦ −ρ`.

The proof counts. The disc carries total multiplicity `m` for `H_t`, and the count is stable under
the small uniform perturbation `H_{t+s²}`. The `m` sheets are distinct zeros in the disc, so they
exhaust the count and each has multiplicity one.
-/

open Complex Filter Topology Set Metric
open RHTower RHTower.DeBruijn GaloisForLFunctions.HTGeometry
open GaloisForLFunctions.NodalGeometryOfTheDeBruijnFlow

namespace GaloisForLFunctions.GaloisTheoryOfZeros

noncomputable section
set_option autoImplicit false

/-- On a closed disc the family at the time `t + s²` is uniformly close to `H_t` for small `s`. -/
theorem eventually_norm_complexHeat_sub_le (t : ℝ) (c : ℂ) (R : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ s in 𝓝 (0 : ℂ), ∀ z ∈ closedBall c R,
      ‖complexHeat (t + s ^ 2) z - riemannHeat t z‖ ≤ ε := by
  refine (isCompact_closedBall c R).eventually_forall_of_forall_eventually fun z₁ _ => ?_
  have h1 : Continuous fun q : ℂ × ℂ => complexHeat (t + q.1 ^ 2) q.2 :=
    continuous_complexHeat.comp
      (by fun_prop : Continuous fun q : ℂ × ℂ => ((t : ℂ) + q.1 ^ 2, q.2))
  have h2 : Continuous fun q : ℂ × ℂ => riemannHeat t q.2 := by
    rw [show (fun q : ℂ × ℂ => riemannHeat t q.2) = fun q => complexHeat t q.2 from
      funext fun q => (complexHeat_ofReal t q.2).symm]
    exact continuous_complexHeat.comp (by fun_prop : Continuous fun q : ℂ × ℂ => ((t : ℂ), q.2))
  have hcont : Continuous fun q : ℂ × ℂ =>
      ‖complexHeat (t + q.1 ^ 2) q.2 - riemannHeat t q.2‖ := (h1.sub h2).norm
  have h0 : ‖complexHeat (t + (0 : ℂ) ^ 2) z₁ - riemannHeat t z₁‖ < ε := by
    rw [zero_pow two_ne_zero, add_zero, complexHeat_ofReal, sub_self, norm_zero]
    exact hε
  filter_upwards [(hcont.tendsto ((0 : ℂ), z₁)).eventually (eventually_lt_nhds h0)] with q hq
  exact hq.le

variable {t : ℝ} {z₀ : ℂ} {m : ℕ}

/-- **Exhaustion.** Near a collision of order `m`, for small `s ≠ 0` the zeros of `H_{t+s²}` are
exactly the `m` sheets `Z_ρ(s)`, and each of them is simple. -/
theorem exists_ball_zeros_eq_sheets (hc : IsCollision t z₀ m) :
    ∃ r > 0, ∀ᶠ s in 𝓝[≠] (0 : ℂ), ∀ z ∈ ball z₀ r,
      (complexHeat (t + s ^ 2) z = 0 ↔
        ∃ ρ, heatModelFwd m ρ = 0 ∧ z = collisionZero t z₀ m ρ s) ∧
      (complexHeat (t + s ^ 2) z = 0 → deriv (complexHeat (t + s ^ 2)) z ≠ 0) := by
  classical
  have ht := hc.time_nonneg
  have hf : Differentiable ℂ (riemannHeat t) := differentiable_riemannHeat ht
  have hfin : ∀ z, analyticOrderAt (riemannHeat t) z ≠ ⊤ :=
    fun z => analyticOrderAt_riemannHeat_ne_top ht z
  have hm : zeroMult (riemannHeat t) z₀ = m := by
    have hord : analyticOrderAt (riemannHeat t) z₀ = (m : ℕ∞) :=
      (analyticOrderAt_eq_nat_iff_iteratedDeriv_eq_zero (hf.analyticAt z₀)).mpr
        ⟨hc.vanish, hc.top_ne_zero⟩
    rw [zeroMult, hord, ENat.toNat_coe]
  -- an isolating disc: it carries the multiplicity `m`, and the count is stable
  obtain ⟨r, hr, hiso⟩ := exists_radius_zeroSumBall_eq_zeroMult hf hfin z₀
  obtain ⟨hsph, hcount⟩ := hiso r hr le_rfl
  rw [hm] at hcount
  obtain ⟨ε, hε, hstable⟩ := exists_eps_zeroSumBall_eq hr (by linarith : r < 2 * r) isOpen_univ
    (subset_univ _) hf.differentiableOn hsph
  refine ⟨r, hr, ?_⟩
  -- the roots of the profile
  set T : Finset ℂ := (profileRoots m).image fun x : ℝ => (x : ℂ) with hT
  have hTcard : T.card = m := by
    rw [hT, Finset.card_image_of_injective _ Complex.ofReal_injective, card_profileRoots]
  have hTroot : ∀ ρ, ρ ∈ T ↔ heatModelFwd m ρ = 0 := fun ρ => by
    rw [hT, Finset.mem_image, heatModelFwd_eq_zero_iff]
  -- the sheets are zeros, lie in the disc, and are distinct
  have hzero : ∀ᶠ s in 𝓝 (0 : ℂ), ∀ ρ ∈ T,
      complexHeat (t + s ^ 2) (collisionZero t z₀ m ρ s) = 0 :=
    (eventually_all_finset T).mpr fun ρ hρ => complexHeat_collisionZero hc ((hTroot ρ).mp hρ)
  have hball : ∀ᶠ s in 𝓝 (0 : ℂ), ∀ ρ ∈ T, collisionZero t z₀ m ρ s ∈ ball z₀ r :=
    (eventually_all_finset T).mpr fun ρ hρ => by
      have han := (collisionBranch_spec hc ((hTroot ρ).mp hρ)).1.continuousAt
      have hcz : ContinuousAt (fun s => z₀ + s * collisionBranch t z₀ m ρ s) 0 :=
        continuousAt_const.add (continuousAt_id.mul han)
      have h0 : z₀ + (0 : ℂ) * collisionBranch t z₀ m ρ 0 = z₀ := by rw [zero_mul, add_zero]
      have hlim := hcz.tendsto
      rw [h0] at hlim
      exact hlim.eventually (ball_mem_nhds z₀ hr)
  have hdist : ∀ᶠ s in 𝓝[≠] (0 : ℂ), ∀ ρ ∈ T, ∀ ρ' ∈ T, ρ ≠ ρ' →
      collisionZero t z₀ m ρ s ≠ collisionZero t z₀ m ρ' s :=
    (eventually_all_finset T).mpr fun ρ hρ => (eventually_all_finset T).mpr fun ρ' hρ' => by
      by_cases h : ρ = ρ'
      · exact Eventually.of_forall fun s hne => absurd h hne
      · exact (collisionZero_ne hc ((hTroot ρ).mp hρ) ((hTroot ρ').mp hρ') h).mono
          fun s hs _ => hs
  have hclose := eventually_norm_complexHeat_sub_le t z₀ (2 * r) hε
  filter_upwards [hzero.filter_mono nhdsWithin_le_nhds, hball.filter_mono nhdsWithin_le_nhds,
    hclose.filter_mono nhdsWithin_le_nhds, hdist] with s hz hb hcl hd
  set F : ℂ → ℂ := complexHeat ((t : ℂ) + s ^ 2) with hF
  have hFd : Differentiable ℂ F := differentiable_complexHeat _
  obtain ⟨hFsph, hFcount⟩ := hstable F hFd.differentiableOn hcl
  rw [hcount] at hFcount
  obtain ⟨Z, hZball, hZzero, hZsum⟩ := exists_zeroSet_zeroSumBall hr (by linarith : r < 2 * r)
    isOpen_univ (subset_univ _) hFd.differentiableOn hFsph
  rw [hFcount] at hZsum
  have hsumN : ∑ z ∈ Z, zeroMult F z = m := by exact_mod_cast hZsum.symm
  -- `F` does not vanish identically, since it does not vanish on the circle
  have hFfin : ∀ z, analyticOrderAt F z ≠ ⊤ := by
    intro z htop
    have hall := (hFd.differentiableOn.analyticOnNhd isOpen_univ).eqOn_zero_of_preconnected_of_eventuallyEq_zero
      isPreconnected_univ (mem_univ z) (analyticOrderAt_eq_top.mp htop)
    have hw : z₀ + (r : ℂ) ∈ sphere z₀ r := by
      rw [mem_sphere, dist_eq_norm, add_sub_cancel_left, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos hr]
    exact hFsph _ hw (hall (mem_univ _))
  -- the `m` sheets exhaust the count
  set W : Finset ℂ := T.image fun ρ => collisionZero t z₀ m ρ s with hW
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
  intro z hzb
  refine ⟨?_, fun hz0 => ?_⟩
  · rw [hZzero z hzb, ← hWeq, hW, Finset.mem_image]
    constructor
    · rintro ⟨ρ, hρ, rfl⟩
      exact ⟨ρ, (hTroot ρ).mp hρ, rfl⟩
    · rintro ⟨ρ, hρ, rfl⟩
      exact ⟨ρ, (hTroot ρ).mpr hρ, rfl⟩
  · have hzZ := (hZzero z hzb).mp hz0
    have hcardeq : Z.card = m := by rw [← hWeq, hWcard]
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

end

end GaloisForLFunctions.GaloisTheoryOfZeros
