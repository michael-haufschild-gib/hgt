import GaloisForLFunctions.RHTower.Sieve.MatomakiTeravainenRealFinsetHalaszMontgomery
import GaloisForLFunctions.RHTower.Sieve.LogPolyBlockBridge

/-!
# Halász--Montgomery for the dyadic pieces of a `logPoly`

`MatomakiTeravainenRealFinsetHalaszMontgomery.halaszMontgomery_blockPoly_real_finset_explicit`
proves the Halász--Montgomery mean square over a literal separated finite set of real ordinates,
but only on the line `sigma = 1`.  The parameter `sigma` never enters its proof — it is carried
inertly by `inner_dyadicDirRow_blockCoeff` — so the same statement holds for every `sigma`, and the
Möbius bilinear form needs it at `sigma = 0`.

With the `sigma`-general form and the bridge `logPoly_eq_blockPoly_of_subset`, the mean square of a
dyadic piece of an initial-segment `logPoly` over a one-spaced family of frequencies is bounded by
Halász--Montgomery.  The frequency rescaling `w ↦ −2πw` *improves* the separation from `1` to `2π`.

* `halaszMontgomery_blockPoly_real_finset_sigma`;
* `halaszMontgomery_logPoly_finset` — the form the Möbius level-split consumes.
-/

namespace RHTower.Sieve

open Finset
open scoped InnerProductSpace

noncomputable section

/-- **Halász--Montgomery on a literal separated real finite set, at an arbitrary line.** -/
theorem halaszMontgomery_blockPoly_real_finset_sigma
    (N : ℕ) (hN : 1 ≤ N) (c : ℕ → ℂ) (sigma : ℝ)
    {S : Finset ℝ} {delta U T : ℝ}
    (hdelta : 0 < delta) (hU : 0 < U) (hT : 0 ≤ T)
    (hsep : ∀ x ∈ S, ∀ y ∈ S, x ≠ y → delta ≤ |x - y|)
    (hspread : ∀ x ∈ S, ∀ y ∈ S, |x - y| ≤ T)
    (hnear : 3 * U ≤ 4 * Real.pi * (N : ℝ))
    (hlamT : logDyadicLambda N T ≤ 1) :
    ∑ t ∈ S, ‖blockPoly N c sigma t‖ ^ (2 : ℕ) ≤
      ((N : ℝ) + (12 * Real.pi * (N : ℝ) / delta) * (1 + Real.log S.card)
          + (S.card : ℝ) *
            (1 + 214 * Real.sqrt T + 1536 * ((N : ℝ) / Real.sqrt U))) *
        ‖blockCoeff N c sigma‖ ^ (2 : ℕ) := by
  let P := matomakiTeravainenFiniteSeparatedOrdinates S delta hdelta hsep
  have hdiam : ∀ r ∈ Finset.range S.card, ∀ s ∈ Finset.range S.card,
      |RHTower.cglFiniteSeparatedOrdinatesTimeline P s -
        RHTower.cglFiniteSeparatedOrdinatesTimeline P r| ≤ T := by
    intro r hr s hs
    have hrmem := matomakiTeravainenFiniteSeparatedOrdinates_timeline_mem
      S delta hdelta hsep (Finset.mem_range.1 hr)
    have hsmem := matomakiTeravainenFiniteSeparatedOrdinates_timeline_mem
      S delta hdelta hsep (Finset.mem_range.1 hs)
    exact hspread _ hsmem _ hrmem
  have hbase := halaszMontgomery_dyadic_explicit (K := S.card) hN (blockCoeff N c sigma)
    hdelta hU hT (RHTower.cglFiniteSeparatedOrdinatesTimeline_step P) hdiam
    hnear hlamT
  rw [sum_finset_eq_sum_matomakiTeravainenFiniteSeparatedOrdinates_timeline
    S delta hdelta hsep
    (fun t => ‖blockPoly N c sigma t‖ ^ (2 : ℕ))]
  simpa only [inner_dyadicDirRow_blockCoeff] using hbase

/-- **Halász--Montgomery for a `logPoly` supported in a dyadic range**, over a one-spaced family of
frequencies of spread at most `2G`.  The rescaling `w ↦ −2πw` turns one-spacing into `2π`-spacing,
which is why the `delta` of the estimate is `2π` rather than `1`. -/
theorem halaszMontgomery_logPoly_finset
    {N : ℕ} (hN : 1 ≤ N) {s : Finset ℕ} (hs : s ⊆ Finset.Ico N (2 * N)) (a : ℕ → ℂ)
    {P : Finset ℝ} {G U : ℝ} (hG : 0 ≤ G) (hU : 0 < U)
    (hsep : ∀ x ∈ P, ∀ y ∈ P, x ≠ y → (1 : ℝ) ≤ |x - y|)
    (hspread : ∀ x ∈ P, ∀ y ∈ P, |x - y| ≤ 2 * G)
    (hnear : 3 * U ≤ 4 * Real.pi * (N : ℝ))
    (hlamT : logDyadicLambda N (4 * Real.pi * G) ≤ 1) :
    ∑ w ∈ P, ‖logPoly a s w‖ ^ (2 : ℕ) ≤
      ((N : ℝ) + (12 * Real.pi * (N : ℝ) / (2 * Real.pi)) * (1 + Real.log P.card)
          + (P.card : ℝ) *
            (1 + 214 * Real.sqrt (4 * Real.pi * G)
              + 1536 * ((N : ℝ) / Real.sqrt U))) *
        ‖blockCoeff N (blockRestrictCoeff a s) 0‖ ^ (2 : ℕ) := by
  classical
  set S : Finset ℝ := P.image (fun x => -(2 * Real.pi * x)) with hS
  have hpi : (0 : ℝ) < 2 * Real.pi := by positivity
  have hinj : Set.InjOn (fun x : ℝ => -(2 * Real.pi * x)) P := by
    intro x _ y _ hxy
    simp only [neg_inj] at hxy
    exact mul_left_cancel₀ (ne_of_gt hpi) hxy
  have hcard : S.card = P.card := by rw [hS, Finset.card_image_of_injOn hinj]
  have hmem : ∀ y ∈ S, ∃ x ∈ P, y = -(2 * Real.pi * x) := by
    intro y hy
    rw [hS, Finset.mem_image] at hy
    obtain ⟨x, hx, hxy⟩ := hy
    exact ⟨x, hx, hxy.symm⟩
  have hSsep : ∀ y ∈ S, ∀ z ∈ S, y ≠ z → (2 * Real.pi) ≤ |y - z| := by
    intro y hy z hz hyz
    obtain ⟨x, hx, rfl⟩ := hmem y hy
    obtain ⟨u, hu, rfl⟩ := hmem z hz
    have hxu : x ≠ u := fun h => hyz (by rw [h])
    have hsep' := hsep x hx u hu hxu
    have hid : -(2 * Real.pi * x) - -(2 * Real.pi * u) = (2 * Real.pi) * (u - x) := by ring
    rw [hid, abs_mul, abs_of_pos hpi, abs_sub_comm]
    nlinarith [hsep', hpi]
  have hSspread : ∀ y ∈ S, ∀ z ∈ S, |y - z| ≤ 4 * Real.pi * G := by
    intro y hy z hz
    obtain ⟨x, hx, rfl⟩ := hmem y hy
    obtain ⟨u, hu, rfl⟩ := hmem z hz
    have hid : -(2 * Real.pi * x) - -(2 * Real.pi * u) = (2 * Real.pi) * (u - x) := by ring
    rw [hid, abs_mul, abs_of_pos hpi, abs_sub_comm]
    have habs := hspread x hx u hu
    nlinarith [habs, Real.pi_pos, abs_nonneg (x - u)]
  have hT : (0 : ℝ) ≤ 4 * Real.pi * G := by positivity
  have hbase := halaszMontgomery_blockPoly_real_finset_sigma N hN (blockRestrictCoeff a s) 0
    hpi hU hT hSsep hSspread hnear hlamT
  rw [hcard] at hbase
  have hrw : ∑ w ∈ P, ‖logPoly a s w‖ ^ (2 : ℕ)
      = ∑ t ∈ S, ‖blockPoly N (blockRestrictCoeff a s) 0 t‖ ^ (2 : ℕ) := by
    rw [hS, Finset.sum_image (fun x hx y hy h => hinj hx hy h)]
    refine Finset.sum_congr rfl fun w _ => ?_
    rw [logPoly_eq_blockPoly_of_subset hs]
  rw [hrw]
  exact hbase

/-- **The initial-segment mean square over a one-spaced family, by Halász--Montgomery.**  The
dyadic split of `[1, M]` costs one factor `⌊log₂ M⌋ + 1`, and each dyadic piece is bounded by
Halász--Montgomery.  This is the estimate the Möbius level split consumes at every level. -/
theorem sum_normSq_logPoly_Icc_le_halaszMontgomery
    {M : ℕ} (a : ℕ → ℂ) {P : Finset ℝ} {G U : ℝ} (hG : 0 ≤ G) (hU : 0 < U)
    (hsep : ∀ x ∈ P, ∀ y ∈ P, x ≠ y → (1 : ℝ) ≤ |x - y|)
    (hspread : ∀ x ∈ P, ∀ y ∈ P, |x - y| ≤ 2 * G)
    (hnear : ∀ i : ℕ, 3 * U ≤ 4 * Real.pi * ((2 ^ i : ℕ) : ℝ))
    (hlam : ∀ i : ℕ, logDyadicLambda (2 ^ i) (4 * Real.pi * G) ≤ 1) :
    ∑ w ∈ P, ‖logPoly a (Finset.Icc 1 M) w‖ ^ (2 : ℕ)
      ≤ ((Nat.log 2 M + 1 : ℕ) : ℝ) *
          ∑ i ∈ Finset.range (Nat.log 2 M + 1),
            ((((2 ^ i : ℕ) : ℝ)
                + (12 * Real.pi * ((2 ^ i : ℕ) : ℝ) / (2 * Real.pi)) * (1 + Real.log P.card)
                + (P.card : ℝ) * (1 + 214 * Real.sqrt (4 * Real.pi * G)
                    + 1536 * (((2 ^ i : ℕ) : ℝ) / Real.sqrt U)))
              * ‖blockCoeff (2 ^ i) (dyadicSegmentCoeff a M i) 0‖ ^ (2 : ℕ)) := by
  classical
  refine (sum_normSq_logPoly_Icc_le_card_mul_sum_blocks a M P).trans ?_
  refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun i _ => ?_) (by positivity)
  have hNi : 1 ≤ 2 ^ i := Nat.one_le_two_pow
  exact halaszMontgomery_logPoly_finset hNi (dyadicSegmentBlock_subset_Ico M i) a hG hU
    hsep hspread (hnear i) (hlam i)

end

end RHTower.Sieve
