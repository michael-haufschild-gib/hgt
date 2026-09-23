/-
# The u-plane deck-charge classification, and the seam blindness of conjugate pairs

The `2^k`-th-root torsor of the descended function `xiDescent` on a slit-plane region is
classified by a single `μ_{2^k}`-valued observable, the deck charge
`carrierCharge xiDescent k w = exp(2πi · ord_w(xiDescent) / 2^k)`.  This file assembles the
`u`-plane form of that classification and the honest content of the "seam-winding formula".

* **Comparison (s ↔ u).**  Under the descent the charge transports verbatim:
  `carrierCharge xiDescent k ((ρ − 1/2)²) = carrierCharge xi k ρ`
  (`xiDescent_carrierCharge_center_sq`), and it is conjugation-invariant
  (`xiDescent_carrierCharge_conj`).  So the `s`-plane quadrant charge and the `u`-plane
  half-plane charge are literally the same element of `μ_{2^k}`.

* **Classification on half the plane.**  Combining the domain-halving ladder with the
  divisibility face of the charge,
  `RHLadder k ↔ ∀ w ∈ slitPlane, 0 ≤ Im w → carrierCharge xiDescent k w = 1`
  (`rhLadder_iff_xiDescent_carrierCharge_upperHalf`): the whole ladder is the triviality of
  the deck charge at every upper-half slit zero.

* **Seam blindness.**  A finite conjugation-symmetric, fixed-point-free family of `u`-plane
  zeros has **even** total multiplicity (`xiDescent_seam_order_even`), so its rung-`1`
  aggregate charge vanishes (`seam_charge_two_eq_zero`); the exact "seam order = 2 · upper
  order" identity is `seam_order_two_mul`.  This is the reason a symmetric seam detector is
  blind to a compact conjugate-pair island (`P(u) = u² + 1` has zeros `±i` with total order
  `2`): the winding realisation `loopCharge_divisor` reads the *total* order, which reality
  forces to be even, so it cannot see a single odd upper defect.

Every statement reads the order of the *given* descended function; no carrier is constructed
and no loop is integrated — the charge is a constraint invariant, and the winding twin is only
referenced, not the primary object.
-/
import GaloisForLFunctions.RHTower.UPlaneReflection
import GaloisForLFunctions.RHTower.UPlaneLadder
import GaloisForLFunctions.RHTower.CarrierDeckCharge
import GaloisForLFunctions.RHTower.SeamCocycle

namespace RHTower

open Complex Filter Set

/-! ### Comparison of the s-plane quadrant charge and the u-plane half-plane charge -/

/-- **The deck charge transports through the descent.**  At a right-half point `ρ` the `u`-plane
charge of `xiDescent` at the descended point `(ρ − 1/2)²` equals the `s`-plane charge of `ξ` at
`ρ`: the multiplicity is preserved, so the two `μ_{2^k}` values coincide. -/
theorem xiDescent_carrierCharge_center_sq {ρ : ℂ} (hρ : ρ ∈ rightHalf) (k : ℕ) :
    carrierCharge xiDescent k ((ρ - (1 / 2 : ℂ)) ^ (2 : ℕ)) = carrierCharge xi k ρ := by
  unfold carrierCharge
  rw [analyticOrderAt_xiDescent_center_sq hρ]

/-- **Conjugation invariance of the u-plane charge.**  The residual `ℤ/2` symmetry `w ↦ w̄` of the
descent leaves the deck charge unchanged — the `s`-plane conjugation, seen in the `u`-plane. -/
theorem xiDescent_carrierCharge_conj (k : ℕ) (w : ℂ) :
    carrierCharge xiDescent k ((starRingEnd ℂ) w) = carrierCharge xiDescent k w :=
  carrierCharge_conj xiDescent_differentiable xiDescent_conj k w

/-! ### The charge form of the ladder, on half the slit plane -/

/-- **Classification: the ladder is the triviality of the deck charge on the upper half.**
`RHLadder k` holds exactly when the `u`-plane deck charge `carrierCharge xiDescent k` is trivial at
every slit-plane point with `0 ≤ Im w`.  The lower half is covered by conjugation invariance, so a
single `μ_{2^k}`-valued observable on half the plane classifies the whole rung. -/
theorem rhLadder_iff_xiDescent_carrierCharge_upperHalf (k : ℕ) :
    RHLadder k ↔ ∀ w ∈ slitPlane, 0 ≤ w.im → carrierCharge xiDescent k w = 1 := by
  rw [rhLadder_iff_xiDescent_upperHalf]
  constructor
  · intro h w hw hwim
    by_cases hz : xiDescent w = 0
    · exact (carrierCharge_eq_one_iff_enat_dvd (xiDescent_orderAt_ne_top w)).mpr (h w hw hwim hz)
    · exact carrierCharge_eq_one_of_ne_zero xiDescent k hz
  · intro h w hw hwim _
    exact (carrierCharge_eq_one_iff_enat_dvd (xiDescent_orderAt_ne_top w)).mp (h w hw hwim)

/-- The full slit-plane charge form: `RHLadder k` iff the deck charge is trivial at every
slit-plane point. -/
theorem rhLadder_iff_xiDescent_carrierCharge_slitPlane (k : ℕ) :
    RHLadder k ↔ ∀ w ∈ slitPlane, carrierCharge xiDescent k w = 1 := by
  rw [rhLadder_iff_xiDescent_order_dvd_slitPlane]
  constructor
  · intro h w hw
    by_cases hz : xiDescent w = 0
    · exact (carrierCharge_eq_one_iff_enat_dvd (xiDescent_orderAt_ne_top w)).mpr (h w hw hz)
    · exact carrierCharge_eq_one_of_ne_zero xiDescent k hz
  · intro h w hw _
    exact (carrierCharge_eq_one_iff_enat_dvd (xiDescent_orderAt_ne_top w)).mp (h w hw)

/-! ### Seam blindness: a conjugate-pair island reads even total charge -/

/-- **The seam order equals twice the upper order.**  For a finite set `S` closed under conjugation
with no real (fixed) points and a conjugation-invariant weight `ord`, the total weight is twice the
weight of the upper half `{Im w > 0}`: conjugation pairs each upper point with a distinct lower one
of equal weight. -/
theorem seam_order_two_mul {S : Finset ℂ} (ord : ℂ → ℕ)
    (hSconj : ∀ w ∈ S, (starRingEnd ℂ) w ∈ S)
    (hnofix : ∀ w ∈ S, (starRingEnd ℂ) w ≠ w)
    (hord : ∀ w ∈ S, ord ((starRingEnd ℂ) w) = ord w) :
    ∑ w ∈ S, ord w = 2 * ∑ w ∈ S.filter (fun w => 0 < w.im), ord w := by
  classical
  have him_ne : ∀ w ∈ S, w.im ≠ 0 := by
    intro w hw h0
    refine hnofix w hw ?_
    apply Complex.ext
    · rw [Complex.conj_re]
    · rw [Complex.conj_im, h0, neg_zero]
  have hlow_eq : ∑ w ∈ S.filter (fun w => ¬ 0 < w.im), ord w
      = ∑ w ∈ S.filter (fun w => 0 < w.im), ord w := by
    apply Finset.sum_nbij' (i := starRingEnd ℂ) (j := starRingEnd ℂ)
    · intro a ha
      rw [Finset.mem_filter] at ha ⊢
      obtain ⟨haS, hap⟩ := ha
      have hlt : a.im < 0 := lt_of_le_of_ne (not_lt.mp hap) (him_ne a haS)
      exact ⟨hSconj a haS, by rw [Complex.conj_im]; linarith⟩
    · intro b hb
      rw [Finset.mem_filter] at hb ⊢
      obtain ⟨hbS, hbp⟩ := hb
      exact ⟨hSconj b hbS, by rw [Complex.conj_im, not_lt]; linarith⟩
    · intro a _; exact Complex.conj_conj a
    · intro b _; exact Complex.conj_conj b
    · intro a ha
      rw [Finset.mem_filter] at ha
      exact (hord a ha.1).symm
  calc ∑ w ∈ S, ord w
      = ∑ w ∈ S.filter (fun w => 0 < w.im), ord w
        + ∑ w ∈ S.filter (fun w => ¬ 0 < w.im), ord w :=
        (Finset.sum_filter_add_sum_filter_not S _ ord).symm
    _ = ∑ w ∈ S.filter (fun w => 0 < w.im), ord w
        + ∑ w ∈ S.filter (fun w => 0 < w.im), ord w := by rw [hlow_eq]
    _ = 2 * ∑ w ∈ S.filter (fun w => 0 < w.im), ord w := by ring

/-- **The rung-`1` seam charge vanishes.**  For a conjugation-symmetric, fixed-point-free family
with a conjugation-invariant weight, the aggregate mod-`2` deck charge is `0`.  Reality forces the
total order even, so the seam/aggregate detector reads trivially — it is blind to any odd upper
defect. -/
theorem seam_charge_two_eq_zero {S : Finset ℂ} (ord : ℂ → ℕ)
    (hSconj : ∀ w ∈ S, (starRingEnd ℂ) w ∈ S)
    (hnofix : ∀ w ∈ S, (starRingEnd ℂ) w ≠ w)
    (hord : ∀ w ∈ S, ord ((starRingEnd ℂ) w) = ord w) :
    wCharge 2 ((∑ w ∈ S, ord w : ℕ) : ℤ) = 0 := by
  rw [wCharge_eq_zero_iff, Int.natCast_dvd_natCast, seam_order_two_mul ord hSconj hnofix hord]
  exact ⟨_, rfl⟩

/-- **Even total multiplicity of a conjugate-pair family.**  A conjugation-symmetric fixed-point-free
set of zeros has even total order. -/
theorem even_seam_order {S : Finset ℂ} (ord : ℂ → ℕ)
    (hSconj : ∀ w ∈ S, (starRingEnd ℂ) w ∈ S)
    (hnofix : ∀ w ∈ S, (starRingEnd ℂ) w ≠ w)
    (hord : ∀ w ∈ S, ord ((starRingEnd ℂ) w) = ord w) :
    Even (∑ w ∈ S, ord w) := by
  have h := seam_charge_two_eq_zero ord hSconj hnofix hord
  rw [wCharge_eq_zero_iff, Int.natCast_dvd_natCast] at h
  obtain ⟨c, hc⟩ := h
  exact ⟨c, by omega⟩

/-- **Seam blindness for the descended divisor.**  A finite conjugation-symmetric fixed-point-free
family of zeros of `xiDescent` (a conjugate-pair island) has even total multiplicity: the reality
pairing `xiDescent_orderAt_conj` matches upper and lower orders, so the rung-`1` seam charge is `0`.
This is exactly why the naive seam forcing fails — the aggregate cannot detect a single odd upper
defect. -/
theorem xiDescent_seam_order_even {S : Finset ℂ}
    (hSconj : ∀ w ∈ S, (starRingEnd ℂ) w ∈ S)
    (hnofix : ∀ w ∈ S, (starRingEnd ℂ) w ≠ w) :
    Even (∑ w ∈ S, (analyticOrderAt xiDescent w).toNat) :=
  even_seam_order _ hSconj hnofix (fun w _ => by rw [xiDescent_orderAt_conj])

end RHTower
