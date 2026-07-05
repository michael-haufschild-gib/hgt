/-
The square ladder on the slit u-plane (MWM lane, W2 attack — task #130;
doc 19-square-factorization.md).

The window relation's GLOBAL extreme (window = the whole plane). Level `k` of the
RH ladder is equivalent to the existence of one global analytic `2^k`-th root of the
descended function `xiDescent` on `slitPlane`. The critical line is the slit, so
on-line zeros sit OUTSIDE the domain: the root is obstructed exactly by off-line
zeros of insufficient 2-adic depth.

* `rhLadder_iff_root_slitPlane` — `RHLadder k` ⟺ an analytic `2^k`-th root of
  `xiDescent` exists on the slit plane.
* `rhLadder_one_iff_sqrt` — the k = 1 rung (the bridge identity's target (WR_1))
  IS the sentence "`xiDescent` is a square on the slit plane".
* `rh_iff_forall_root_slitPlane` — RH ⟺ the whole root tower exists.

Compared to the half-plane form `rhLadder_iff_root`: the domain is now the FE-quotient
carrier (simply connected, boundary = the critical line as slit), so the k = 1 rung
becomes a divisor-class statement about ONE entire function of order 1/2 — the square
class of its off-slit divisor. Both directions are pure transport along the descent
`u = (s − 1/2)²` (no new root-existence machinery).
-/
import GaloisForLFunctions.RHTower.UPlaneDescent

namespace RHTower

open Complex

/-- The descent of a right-half-plane point lands in the slit plane. -/
theorem center_sq_mem_slitPlane {s : ℂ} (hs : s ∈ rightHalf) :
    (s - 1 / 2) ^ 2 ∈ slitPlane := by
  have hcast : (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) := by norm_num
  refine sq_mem_slitPlane_of_re_pos ?_
  rw [Complex.sub_re, hcast, Complex.ofReal_re]
  have h := mem_rightHalf.mp hs
  linarith

/-- The lift of a slit-plane point lands in the right half-plane. -/
theorem half_add_uSqrt_mem_rightHalf {w : ℂ} (hw : w ∈ slitPlane) :
    (1 / 2 : ℂ) + uSqrt w ∈ rightHalf := by
  have hcast : (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) := by norm_num
  rw [mem_rightHalf, Complex.add_re, hcast, Complex.ofReal_re]
  have := uSqrt_re_pos hw
  linarith

/-- **Ladder ⟺ slit-plane root.**  Level `k` of the RH ladder holds iff `xiDescent`
has a global analytic `2^k`-th root on the slit plane.  On-line zeros lie ON the slit
(outside the domain); only off-line zeros obstruct. -/
theorem rhLadder_iff_root_slitPlane (k : ℕ) :
    RHLadder k ↔
      ∃ g, AnalyticOnNhd ℂ g slitPlane ∧
        ∀ w ∈ slitPlane, g w ^ 2 ^ k = xiDescent w := by
  rw [rhLadder_iff_root]
  constructor
  · rintro ⟨h, hh, hhn⟩
    refine ⟨fun w => h ((1 / 2 : ℂ) + uSqrt w), ?_, ?_⟩
    · intro w hw
      exact AnalyticAt.comp (f := fun w' : ℂ => (1 / 2 : ℂ) + uSqrt w')
        (hh _ (half_add_uSqrt_mem_rightHalf hw))
        (analyticAt_const.add (uSqrt_analyticAt hw))
    · intro w hw
      show h ((1 / 2 : ℂ) + uSqrt w) ^ 2 ^ k = xiDescent w
      rw [hhn _ (half_add_uSqrt_mem_rightHalf hw),
        ← xiDescent_of_ne_zero (slitPlane_ne_zero hw)]
  · rintro ⟨g, hg, hgn⟩
    refine ⟨fun s => g ((s - 1 / 2) ^ 2), ?_, ?_⟩
    · intro s hs
      exact AnalyticAt.comp (f := fun s' : ℂ => (s' - 1 / 2) ^ 2)
        (hg _ (center_sq_mem_slitPlane hs))
        ((analyticAt_id.sub analyticAt_const).pow 2)
    · intro s hs
      show g ((s - 1 / 2) ^ 2) ^ 2 ^ k = xi s
      rw [hgn _ (center_sq_mem_slitPlane hs), ← xi_eq_xiDescent]

/-- **The k = 1 rung is a square statement.**  `RHLadder 1` — the target of the
bridge identity (WR_1) — is exactly: `xiDescent` is the square of an analytic
function on the slit plane. -/
theorem rhLadder_one_iff_sqrt :
    RHLadder 1 ↔
      ∃ g, AnalyticOnNhd ℂ g slitPlane ∧
        ∀ w ∈ slitPlane, g w ^ 2 = xiDescent w := by
  simpa using rhLadder_iff_root_slitPlane 1

/-- **RH ⟺ the full square tower on the slit plane.** -/
theorem rh_iff_forall_root_slitPlane :
    RiemannHypothesis ↔
      ∀ k : ℕ, ∃ g, AnalyticOnNhd ℂ g slitPlane ∧
        ∀ w ∈ slitPlane, g w ^ 2 ^ k = xiDescent w := by
  rw [rh_iff_forall_ladder]
  exact forall_congr' fun k => rhLadder_iff_root_slitPlane k

end RHTower

namespace RHTower

open Complex

/-- **RH ⟺ the coherent dyadic tower of the descended ξ on the slit plane.**  The
slit-plane descent is not just an all-level root sentence: on the star-convex quotient
domain, nonvanishing is exactly the existence of one coherent Kummer tower. -/
theorem rh_iff_xiDescent_coherentTower_slitPlane :
    RiemannHypothesis ↔ Nonempty (CoherentTower xiDescent slitPlane) := by
  have hsc : IsSimplyConnected slitPlane := by
    haveI : ContractibleSpace slitPlane :=
      Complex.starConvex_one_slitPlane.contractibleSpace ⟨(1 : ℂ), Complex.one_mem_slitPlane⟩
    exact SimplyConnectedSpace.ofContractible _
  have hpc : IsPreconnected slitPlane :=
    (Complex.starConvex_one_slitPlane.isPathConnected
      Complex.one_mem_slitPlane).isConnected.isPreconnected
  have hz : ((9 : ℂ) / 4) ∈ slitPlane := by
    norm_num [Complex.mem_slitPlane_iff]
  have hne : xiDescent ((9 : ℂ) / 4) ≠ 0 := by
    rw [show ((9 : ℂ) / 4) = ((2 : ℂ) - 1 / 2) ^ 2 from by norm_num,
      ← xi_eq_xiDescent]
    exact xi_two_ne_zero
  have htower :
      Nonempty (CoherentTower xiDescent slitPlane) ↔
        ∀ w ∈ slitPlane, xiDescent w ≠ 0 :=
    coherentTower_iff_nonvanishing (f := xiDescent) (U := slitPlane)
      Complex.isOpen_slitPlane hsc hpc (fun w hw => xiDescent_analyticAt hw) hz hne
  rw [rh_iff_xiDescent_ne_zero_slitPlane, ← htower]

end RHTower

namespace RHTower

open Complex

/-- **The u-plane coherent tower is exactly the all-level descended divisor constraint.**
This connects the Bottcher-backed slit-plane descent to the U0 Kummer obstruction without
routing through `RiemannHypothesis`: the coherent tower exists precisely when every
slit-plane zero of `xiDescent` has order divisible by every finite dyadic level. -/
theorem xiDescent_coherentTower_slitPlane_iff_all_order_dvd :
    Nonempty (CoherentTower xiDescent slitPlane) ↔
      ∀ k : ℕ, ∀ w ∈ slitPlane, xiDescent w = 0 →
        ((2 ^ k : ℕ) : ℕ∞) ∣ analyticOrderAt xiDescent w := by
  have hsc : IsSimplyConnected slitPlane := by
    haveI : ContractibleSpace slitPlane :=
      Complex.starConvex_one_slitPlane.contractibleSpace ⟨(1 : ℂ), Complex.one_mem_slitPlane⟩
    exact SimplyConnectedSpace.ofContractible _
  have hpc : IsPreconnected slitPlane :=
    (Complex.starConvex_one_slitPlane.isPathConnected
      Complex.one_mem_slitPlane).isConnected.isPreconnected
  have hz : ((9 : ℂ) / 4) ∈ slitPlane := by
    norm_num [Complex.mem_slitPlane_iff]
  have hne : xiDescent ((9 : ℂ) / 4) ≠ 0 := by
    rw [show ((9 : ℂ) / 4) = ((2 : ℂ) - 1 / 2) ^ 2 from by norm_num,
      ← xi_eq_xiDescent]
    exact xi_two_ne_zero
  exact coherentTower_iff_orders_dvd_all_two_powers
    Complex.isOpen_slitPlane hsc hpc (fun w hw => xiDescent_analyticAt hw) hz hne

end RHTower
