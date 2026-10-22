import GaloisForLFunctions.RHTower.Suzuki.SuzukiScrewSmoothTestCriterion
import GaloisForLFunctions.RHTower.Suzuki.SuzukiScrewFirstGapPositivity
import Mathlib.Analysis.Convex.Deriv

/-!
# Suzuki checkpoint event dynamics

This module gives an unconditional event-cell form of Suzuki's source function.  The smooth
archimedean reservoir and the cumulative half-weighted Mangoldt mass reduce the source on each
integer logarithmic cell to a strictly convex potential.  The resulting unique checkpoint has an
exact restricted Legendre--Mangoldt representation; its stationary drawdown is a Bregman
divergence of the reservoir.

Integer cells refine the prime-power cells: zero von Mangoldt weights make the extra cells
algebraically inert while avoiding any separate enumeration of prime powers.
-/

noncomputable section

namespace RHTower

open Filter Topology Set
open GaloisForLFunctions.RHTower

/-- The smooth archimedean reservoir in the decomposition
`Ψ(t) = A(t) - P(t)` on the nonnegative half-line. -/
def suzukiCheckpointReservoir (t : ℝ) : ℝ :=
  4 * (Real.exp (t / 2) + Real.exp (-(t / 2)) - 2)
    + screwLinearCoeff / 2 * t + screwLerchConst - screwLerchTail t

/-- Cumulative half-weighted Mangoldt mass through the integer event `N`. -/
def suzukiCheckpointMass (N : ℕ) : ℝ :=
  ∑ n ∈ Finset.Icc 2 N, screwPrimeWeight n

/-- Logarithmic first moment of the half-weighted Mangoldt mass through `N`. -/
def suzukiCheckpointMoment (N : ℕ) : ℝ :=
  ∑ n ∈ Finset.Icc 2 N, screwPrimeWeight n * Real.log n

/-- Closed integer event cell associated with the history through `N`. -/
def suzukiCheckpointCell (N : ℕ) : Set ℝ :=
  Icc (Real.log (N : ℝ)) (Real.log ((N + 1 : ℕ) : ℝ))

/-- Restricted Legendre integrand: arithmetic cumulative slope minus smooth reservoir. -/
def suzukiCheckpointLegendreCost (N : ℕ) (t : ℝ) : ℝ :=
  suzukiCheckpointMass N * t - suzukiCheckpointReservoir t

/-- Restricted Legendre--Mangoldt conjugate on one integer event cell. -/
def suzukiCheckpointConjugate (N : ℕ) : ℝ :=
  sSup (suzukiCheckpointLegendreCost N '' suzukiCheckpointCell N)

/-- Suzuki's source function is smooth reservoir minus prime loading for `t ≥ 0`. -/
theorem suzukiPsi_eq_checkpointReservoir_sub_screwPrimeSum {t : ℝ} (ht : 0 ≤ t) :
    suzukiPsi t = suzukiCheckpointReservoir t - screwPrimeSum t := by
  rw [suzukiPsi, abs_of_nonneg ht]
  simp only [screwFn, suzukiCheckpointReservoir]
  ring

/-- On the integer event cell `[log N, log (N+1)]`, prime loading is exactly affine.
The potential endpoint term at `N + 1` vanishes, so no primality decision occurs in this identity. -/
theorem screwPrimeSum_eq_checkpoint_affine {N : ℕ} (hN : 2 ≤ N) {t : ℝ}
    (ht : t ∈ Icc (Real.log (N : ℝ)) (Real.log ((N + 1 : ℕ) : ℝ))) :
    screwPrimeSum t = suzukiCheckpointMass N * t - suzukiCheckpointMoment N := by
  classical
  have hNnat : 0 < N := by omega
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hNnat
  have hNp1pos : (0 : ℝ) < ((N + 1 : ℕ) : ℝ) := by positivity
  have hexp : Real.exp t ≤ ((N + 1 : ℕ) : ℝ) := by
    rw [← Real.exp_log hNp1pos]
    exact Real.exp_le_exp.mpr ht.2
  have hfloorR : (⌊Real.exp t⌋₊ : ℝ) ≤ (N + 1 : ℕ) :=
    (Nat.floor_le (Real.exp_pos t).le).trans hexp
  have hfloor : ⌊Real.exp t⌋₊ ≤ N + 1 := by exact_mod_cast hfloorR
  have hcore : ∀ n ∈ Finset.Icc 2 N,
      screwPrimeWeight n * max 0 (t - Real.log n)
        = screwPrimeWeight n * (t - Real.log n) := by
    intro n hn
    have hn' := Finset.mem_Icc.mp hn
    have hnpos : (0 : ℝ) < n := by
      exact_mod_cast (by omega : 0 < n)
    have hnle : (n : ℝ) ≤ N := by exact_mod_cast hn'.2
    have hlog : Real.log n ≤ t :=
      (Real.log_le_log_iff hnpos hNpos).mpr hnle |>.trans ht.1
    rw [max_eq_right (by linarith)]
  have htop : screwPrimeWeight (N + 1) * max 0 (t - Real.log ((N + 1 : ℕ) : ℝ)) = 0 := by
    rw [max_eq_left (by linarith [ht.2]), mul_zero]
  calc
    screwPrimeSum t
        = ∑ n ∈ Finset.Icc 2 (N + 1), screwPrimeWeight n * max 0 (t - Real.log n) :=
          screwPrimeSum_eq_sum_max hfloor
    _ = (∑ n ∈ Finset.Icc 2 N, screwPrimeWeight n * max 0 (t - Real.log n))
          + screwPrimeWeight (N + 1) * max 0 (t - Real.log ((N + 1 : ℕ) : ℝ)) := by
          rw [Finset.sum_Icc_succ_top (by omega : 2 ≤ N + 1)]
    _ = ∑ n ∈ Finset.Icc 2 N, screwPrimeWeight n * (t - Real.log n) := by
          rw [htop, add_zero, Finset.sum_congr rfl hcore]
    _ = suzukiCheckpointMass N * t - suzukiCheckpointMoment N := by
          unfold suzukiCheckpointMass suzukiCheckpointMoment
          rw [Finset.sum_mul, ← Finset.sum_sub_distrib]
          exact Finset.sum_congr rfl fun n _ => by ring

/-- The complete Suzuki source has an exact two-moment expression on every integer event cell. -/
theorem suzukiPsi_eq_checkpoint_affine {N : ℕ} (hN : 2 ≤ N) {t : ℝ}
    (ht : t ∈ Icc (Real.log (N : ℝ)) (Real.log ((N + 1 : ℕ) : ℝ))) :
    suzukiPsi t = suzukiCheckpointReservoir t - suzukiCheckpointMass N * t
      + suzukiCheckpointMoment N := by
  rw [suzukiPsi_eq_checkpointReservoir_sub_screwPrimeSum]
  · rw [screwPrimeSum_eq_checkpoint_affine hN ht]
    ring
  · have hN_one : (1 : ℝ) ≤ N := by exact_mod_cast (by omega : 1 ≤ N)
    exact (Real.log_nonneg hN_one).trans ht.1

/-- Pointwise Legendre--Mangoldt identity on one event cell. -/
theorem suzukiPsi_eq_checkpointMoment_sub_legendreCost {N : ℕ} (hN : 2 ≤ N) {t : ℝ}
    (ht : t ∈ suzukiCheckpointCell N) :
    suzukiPsi t = suzukiCheckpointMoment N - suzukiCheckpointLegendreCost N t := by
  rw [suzukiPsi_eq_checkpoint_affine hN ht]
  unfold suzukiCheckpointLegendreCost
  ring

/-- Derivative of the smooth archimedean reservoir. -/
def suzukiCheckpointReservoirDeriv (t : ℝ) : ℝ :=
  2 * Real.exp (t / 2) - 2 * Real.exp (-(t / 2)) + screwLinearCoeff / 2
    - screwLerchTail₁ t

/-- The reservoir has its explicit first derivative on the positive half-line. -/
theorem hasDerivAt_suzukiCheckpointReservoir {t : ℝ} (ht : 0 < t) :
    HasDerivAt suzukiCheckpointReservoir (suzukiCheckpointReservoirDeriv t) t := by
  have hexp := (((hasDerivAt_exp_half t).fun_add (hasDerivAt_exp_neg_half t)).sub_const
    (2 : ℝ)).const_mul (4 : ℝ)
  have hlin : HasDerivAt (fun r : ℝ => screwLinearCoeff / 2 * r)
      (screwLinearCoeff / 2) t := by
    simpa using (hasDerivAt_id t).const_mul (screwLinearCoeff / 2)
  have htail := (hasDerivAt_screwLerchTail ht).fun_neg
  have h := ((hexp.add hlin).add_const screwLerchConst).add htail
  let F : ℝ → ℝ := fun r =>
    ((4 * (Real.exp (r / 2) + Real.exp (-(r / 2)) - 2)
      + screwLinearCoeff / 2 * r) + screwLerchConst) + -screwLerchTail r
  let d : ℝ := 4 * (Real.exp (t / 2) * (1 / 2)
    + Real.exp (-(t / 2)) * (-(1 / 2))) + screwLinearCoeff / 2 + -screwLerchTail₁ t
  change HasDerivAt F d t at h
  have hF : suzukiCheckpointReservoir = F := by
    funext r
    dsimp [F, suzukiCheckpointReservoir]
    ring
  have hd : d = suzukiCheckpointReservoirDeriv t := by
    dsimp [d, suzukiCheckpointReservoirDeriv]
    ring
  rw [hF]
  exact h.congr_deriv hd

/-- The derivative of the reservoir has curvature equal to Suzuki's regular kernel. -/
theorem hasDerivAt_suzukiCheckpointReservoirDeriv {t : ℝ} (ht : 0 < t) :
    HasDerivAt suzukiCheckpointReservoirDeriv (screwRegularKernel t) t := by
  have h := ((((hasDerivAt_exp_half t).const_mul (2 : ℝ)).sub
    ((hasDerivAt_exp_neg_half t).const_mul (2 : ℝ))).add_const
      (screwLinearCoeff / 2)).sub (hasDerivAt_screwLerchTail₁ ht)
  let F : ℝ → ℝ := fun r =>
    (2 * Real.exp (r / 2) - 2 * Real.exp (-(r / 2)) + screwLinearCoeff / 2)
      - screwLerchTail₁ r
  let d : ℝ := 2 * (Real.exp (t / 2) * (1 / 2))
    - 2 * (Real.exp (-(t / 2)) * (-(1 / 2))) - screwLerchTail₂ t
  change HasDerivAt F d t at h
  have hF : suzukiCheckpointReservoirDeriv = F := by rfl
  have hd : d = screwRegularKernel t := by
    dsimp [d]
    rw [screwRegularKernel_eq_tailForm ht, screwLerchTail₂_eq ht]
    ring
  rw [hF]
  exact h.congr_deriv hd

/-- Every integer event cell lies on the positive-curvature side of the plastic transition. -/
theorem suzukiCheckpointReservoirDeriv_curvature_pos_of_log_two_le {t : ℝ}
    (ht : Real.log 2 ≤ t) : 0 < screwRegularKernel t := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have htpos : 0 < t := hlog2.trans_le ht
  rw [screwRegularKernel_pos_iff_cubic htpos]
  have htwo : (2 : ℝ) ≤ Real.exp t := by
    rw [← Real.exp_log (by norm_num : (0 : ℝ) < 2)]
    exact Real.exp_le_exp.mpr ht
  have hpoly : 0 ≤ (Real.exp t - 2) * (Real.exp t ^ (2 : ℕ) + 2 * Real.exp t + 3) := by
    exact mul_nonneg (by linarith) (by positivity)
  nlinarith [hpoly]

/-- The smooth potential whose restriction is Suzuki's source on the event cell. -/
def suzukiCheckpointPotential (N : ℕ) (t : ℝ) : ℝ :=
  suzukiCheckpointReservoir t - suzukiCheckpointMass N * t + suzukiCheckpointMoment N

/-- First derivative of the event-cell potential. -/
def suzukiCheckpointPotentialDeriv (N : ℕ) (t : ℝ) : ℝ :=
  suzukiCheckpointReservoirDeriv t - suzukiCheckpointMass N

/-- Every integer event cell lies after the first prime event. -/
theorem suzukiCheckpointCell_subset_Ici_log_two {N : ℕ} (hN : 2 ≤ N) :
    suzukiCheckpointCell N ⊆ Ici (Real.log 2) := by
  intro t ht
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have htwole : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hlog : Real.log (2 : ℝ) ≤ Real.log N :=
    (Real.log_le_log_iff (by norm_num) hNpos).mpr htwole
  exact hlog.trans ht.1

/-- The event-cell potential has its displayed derivative on the positive half-line. -/
theorem hasDerivAt_suzukiCheckpointPotential (N : ℕ) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (suzukiCheckpointPotential N) (suzukiCheckpointPotentialDeriv N t) t := by
  have hlin : HasDerivAt (fun r : ℝ => suzukiCheckpointMass N * r)
      (suzukiCheckpointMass N) t := by
    simpa using (hasDerivAt_id t).const_mul (suzukiCheckpointMass N)
  have h := ((hasDerivAt_suzukiCheckpointReservoir ht).sub hlin).add_const
    (suzukiCheckpointMoment N)
  let F : ℝ → ℝ := fun r =>
    suzukiCheckpointReservoir r - suzukiCheckpointMass N * r + suzukiCheckpointMoment N
  let d : ℝ := suzukiCheckpointReservoirDeriv t - suzukiCheckpointMass N
  change HasDerivAt F d t at h
  have hF : suzukiCheckpointPotential N = F := by rfl
  have hd : d = suzukiCheckpointPotentialDeriv N t := by rfl
  rw [hF]
  exact h.congr_deriv hd

/-- The event-cell derivative has curvature equal to the regular Suzuki kernel. -/
theorem hasDerivAt_suzukiCheckpointPotentialDeriv (N : ℕ) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (suzukiCheckpointPotentialDeriv N) (screwRegularKernel t) t := by
  have h := (hasDerivAt_suzukiCheckpointReservoirDeriv ht).sub_const (suzukiCheckpointMass N)
  let F : ℝ → ℝ := fun r => suzukiCheckpointReservoirDeriv r - suzukiCheckpointMass N
  change HasDerivAt F (screwRegularKernel t) t at h
  have hF : suzukiCheckpointPotentialDeriv N = F := by rfl
  rw [hF]
  exact h

/-- The exact second derivative of every event-cell potential is the regular Suzuki kernel. -/
theorem iteratedDeriv_two_suzukiCheckpointPotential (N : ℕ) {t : ℝ} (ht : 0 < t) :
    iteratedDeriv 2 (suzukiCheckpointPotential N) t = screwRegularKernel t := by
  have hIoi : Ioi (0 : ℝ) ∈ 𝓝 t := isOpen_Ioi.mem_nhds ht
  have hderiv : deriv (suzukiCheckpointPotential N) =ᶠ[𝓝 t]
      suzukiCheckpointPotentialDeriv N :=
    Filter.eventuallyEq_of_mem hIoi fun s hs =>
      (hasDerivAt_suzukiCheckpointPotential N hs).deriv
  rw [iteratedDeriv_succ, iteratedDeriv_one, hderiv.deriv_eq,
    (hasDerivAt_suzukiCheckpointPotentialDeriv N ht).deriv]

/-- The event-cell potential is strictly convex. -/
theorem strictConvexOn_suzukiCheckpointPotential {N : ℕ} (hN : 2 ≤ N) :
    StrictConvexOn ℝ (suzukiCheckpointCell N) (suzukiCheckpointPotential N) := by
  apply strictConvexOn_of_deriv2_pos
  · simpa only [suzukiCheckpointCell] using
      (convex_Icc (Real.log (N : ℝ)) (Real.log ((N + 1 : ℕ) : ℝ)))
  · intro t ht
    have htlog : Real.log 2 ≤ t := suzukiCheckpointCell_subset_Ici_log_two hN ht
    have htpos : 0 < t := (Real.log_pos (by norm_num : (1 : ℝ) < 2)).trans_le htlog
    exact (hasDerivAt_suzukiCheckpointPotential N htpos).continuousAt.continuousWithinAt
  · intro t ht
    have htcell : t ∈ suzukiCheckpointCell N := interior_subset ht
    have htlog : Real.log 2 ≤ t := suzukiCheckpointCell_subset_Ici_log_two hN htcell
    have htpos : 0 < t := (Real.log_pos (by norm_num : (1 : ℝ) < 2)).trans_le htlog
    rw [← iteratedDeriv_eq_iterate, iteratedDeriv_two_suzukiCheckpointPotential N htpos]
    exact suzukiCheckpointReservoirDeriv_curvature_pos_of_log_two_le htlog

/-- Suzuki's source is strictly convex on every integer event cell. -/
theorem strictConvexOn_suzukiPsi_checkpointCell {N : ℕ} (hN : 2 ≤ N) :
    StrictConvexOn ℝ (suzukiCheckpointCell N) suzukiPsi := by
  apply (strictConvexOn_suzukiCheckpointPotential hN).congr
  intro t ht
  exact (suzukiPsi_eq_checkpoint_affine hN ht).symm

/-- Exact endpoint update for the source value.  The state uses only the smooth reservoir,
the current cumulative mass, and the logarithmic event displacement. -/
theorem suzukiCheckpoint_endpoint_recurrence {N : ℕ} (hN : 2 ≤ N) :
    suzukiPsi (Real.log ((N + 1 : ℕ) : ℝ)) = suzukiPsi (Real.log (N : ℝ))
      + (suzukiCheckpointReservoir (Real.log ((N + 1 : ℕ) : ℝ))
          - suzukiCheckpointReservoir (Real.log (N : ℝ)))
      - suzukiCheckpointMass N * (Real.log ((N + 1 : ℕ) : ℝ) - Real.log (N : ℝ)) := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hNp1pos : (0 : ℝ) < ((N + 1 : ℕ) : ℝ) := by positivity
  have hNle : (N : ℝ) ≤ ((N + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.le_succ N
  have hlog : Real.log (N : ℝ) ≤ Real.log ((N + 1 : ℕ) : ℝ) :=
    (Real.log_le_log_iff hNpos hNp1pos).mpr hNle
  have hleft := suzukiPsi_eq_checkpoint_affine hN
    (t := Real.log (N : ℝ)) ⟨le_rfl, hlog⟩
  have hright := suzukiPsi_eq_checkpoint_affine hN
    (t := Real.log ((N + 1 : ℕ) : ℝ)) ⟨hlog, le_rfl⟩
  calc
    suzukiPsi (Real.log ((N + 1 : ℕ) : ℝ))
        = suzukiCheckpointReservoir (Real.log ((N + 1 : ℕ) : ℝ))
            - suzukiCheckpointMass N * Real.log ((N + 1 : ℕ) : ℝ) + suzukiCheckpointMoment N := hright
    _ = (suzukiCheckpointReservoir (Real.log (N : ℝ)) - suzukiCheckpointMass N * Real.log (N : ℝ)
            + suzukiCheckpointMoment N)
          + (suzukiCheckpointReservoir (Real.log ((N + 1 : ℕ) : ℝ))
              - suzukiCheckpointReservoir (Real.log (N : ℝ)))
          - suzukiCheckpointMass N * (Real.log ((N + 1 : ℕ) : ℝ) - Real.log (N : ℝ)) := by ring
    _ = suzukiPsi (Real.log (N : ℝ))
          + (suzukiCheckpointReservoir (Real.log ((N + 1 : ℕ) : ℝ))
              - suzukiCheckpointReservoir (Real.log (N : ℝ)))
          - suzukiCheckpointMass N * (Real.log ((N + 1 : ℕ) : ℝ) - Real.log (N : ℝ)) := by rw [← hleft]

/-- Every integer event cell has a genuine source checkpoint: the source function attains its
minimum on the compact cell. -/
theorem exists_suzukiCheckpoint_isMinOn {N : ℕ} (hN : 2 ≤ N) :
    ∃ t ∈ Icc (Real.log (N : ℝ)) (Real.log ((N + 1 : ℕ) : ℝ)),
      IsMinOn suzukiPsi (Icc (Real.log (N : ℝ)) (Real.log ((N + 1 : ℕ) : ℝ))) t := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hNp1pos : (0 : ℝ) < ((N + 1 : ℕ) : ℝ) := by positivity
  have hNle : (N : ℝ) ≤ ((N + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.le_succ N
  have hlog : Real.log (N : ℝ) ≤ Real.log ((N + 1 : ℕ) : ℝ) :=
    (Real.log_le_log_iff hNpos hNp1pos).mpr hNle
  exact isCompact_Icc.exists_isMinOn ⟨Real.log (N : ℝ), le_rfl, hlog⟩
    continuous_suzukiPsi.continuousOn

/-- Each integer event cell has a unique Suzuki checkpoint. -/
theorem existsUnique_suzukiCheckpoint_isMinOn {N : ℕ} (hN : 2 ≤ N) :
    ∃! v, v ∈ suzukiCheckpointCell N ∧
      IsMinOn suzukiPsi (suzukiCheckpointCell N) v := by
  obtain ⟨v, hv, hmin⟩ := exists_suzukiCheckpoint_isMinOn hN
  refine ⟨v, ⟨hv, hmin⟩, ?_⟩
  intro w hw
  exact (strictConvexOn_suzukiPsi_checkpointCell hN).eq_of_isMinOn hmin hw.2 hv hw.1 |>.symm

/-- The source minimizer on an event cell is a maximizer of the restricted Legendre cost. -/
theorem exists_suzukiCheckpoint_isMaxOn_legendreCost {N : ℕ} (hN : 2 ≤ N) :
    ∃ v ∈ suzukiCheckpointCell N,
      IsMaxOn (suzukiCheckpointLegendreCost N) (suzukiCheckpointCell N) v := by
  obtain ⟨v, hv, hmin⟩ := exists_suzukiCheckpoint_isMinOn hN
  refine ⟨v, hv, ?_⟩
  intro x hx
  have hx' := suzukiPsi_eq_checkpointMoment_sub_legendreCost hN hx
  have hv' := suzukiPsi_eq_checkpointMoment_sub_legendreCost hN hv
  have hminvx : suzukiPsi v ≤ suzukiPsi x := (isMinOn_iff.mp hmin) x hx
  calc
    suzukiCheckpointLegendreCost N x = suzukiCheckpointMoment N - suzukiPsi x := by linarith
    _ ≤ suzukiCheckpointMoment N - suzukiPsi v := sub_le_sub_left hminvx _
    _ = suzukiCheckpointLegendreCost N v := by linarith

/-- A maximizer realizes the restricted Legendre--Mangoldt conjugate. -/
theorem suzukiCheckpointConjugate_eq_legendreCost_of_isMaxOn {N : ℕ} {v : ℝ}
    (hv : v ∈ suzukiCheckpointCell N)
    (hmax : IsMaxOn (suzukiCheckpointLegendreCost N) (suzukiCheckpointCell N) v) :
    suzukiCheckpointConjugate N = suzukiCheckpointLegendreCost N v := by
  unfold suzukiCheckpointConjugate
  have hgreat : IsGreatest
      (suzukiCheckpointLegendreCost N '' suzukiCheckpointCell N)
      (suzukiCheckpointLegendreCost N v) := by
    refine ⟨⟨v, hv, rfl⟩, ?_⟩
    rintro x ⟨u, hu, rfl⟩
    exact (isMaxOn_iff.mp hmax) u hu
  exact hgreat.isLUB.csSup_eq (Set.image_nonempty.mpr ⟨v, hv⟩)

/-- Exact restricted Legendre--Mangoldt representation of the event-cell minimum. -/
theorem exists_suzukiCheckpoint_legendre_representation {N : ℕ} (hN : 2 ≤ N) :
    ∃ v ∈ suzukiCheckpointCell N,
      IsMinOn suzukiPsi (suzukiCheckpointCell N) v ∧
        suzukiPsi v = suzukiCheckpointMoment N - suzukiCheckpointConjugate N := by
  obtain ⟨v, hv, hmin⟩ := exists_suzukiCheckpoint_isMinOn hN
  obtain ⟨w, hw, hmax⟩ := exists_suzukiCheckpoint_isMaxOn_legendreCost hN
  have hcosteq : suzukiCheckpointLegendreCost N v = suzukiCheckpointLegendreCost N w := by
    have hvm := suzukiPsi_eq_checkpointMoment_sub_legendreCost hN hv
    have hwm := suzukiPsi_eq_checkpointMoment_sub_legendreCost hN hw
    have hminvw : suzukiPsi v ≤ suzukiPsi w := (isMinOn_iff.mp hmin) w hw
    have hmaxwv : suzukiCheckpointLegendreCost N v ≤ suzukiCheckpointLegendreCost N w :=
      (isMaxOn_iff.mp hmax) v hv
    linarith
  refine ⟨v, hv, hmin, ?_⟩
  rw [suzukiPsi_eq_checkpointMoment_sub_legendreCost hN hv,
    suzukiCheckpointConjugate_eq_legendreCost_of_isMaxOn hw hmax, hcosteq]

/-- Bregman divergence of the checkpoint reservoir. -/
def suzukiCheckpointBregman (u v : ℝ) : ℝ :=
  suzukiCheckpointReservoir u - suzukiCheckpointReservoir v
    - suzukiCheckpointReservoirDeriv v * (u - v)

/-- On one event cell, the exact source difference is the reservoir difference after removing
the cumulative prime slope. -/
theorem suzukiPsi_sub_eq_checkpoint_reservoir_difference {N : ℕ} (hN : 2 ≤ N)
    {u v : ℝ} (hu : u ∈ Icc (Real.log (N : ℝ)) (Real.log ((N + 1 : ℕ) : ℝ)))
    (hv : v ∈ Icc (Real.log (N : ℝ)) (Real.log ((N + 1 : ℕ) : ℝ))) :
    suzukiPsi u - suzukiPsi v = suzukiCheckpointReservoir u - suzukiCheckpointReservoir v
      - suzukiCheckpointMass N * (u - v) := by
  have hu' := suzukiPsi_eq_checkpoint_affine hN hu
  have hv' := suzukiPsi_eq_checkpoint_affine hN hv
  rw [hu', hv']
  ring

/-- At any stationary checkpoint, source drawdown is exactly Bregman divergence. -/
theorem suzukiPsi_sub_eq_checkpointBregman_of_stationary {N : ℕ} (hN : 2 ≤ N)
    {u v : ℝ} (hu : u ∈ Icc (Real.log (N : ℝ)) (Real.log ((N + 1 : ℕ) : ℝ)))
    (hv : v ∈ Icc (Real.log (N : ℝ)) (Real.log ((N + 1 : ℕ) : ℝ)))
    (hstationary : suzukiCheckpointReservoirDeriv v = suzukiCheckpointMass N) :
    suzukiPsi u - suzukiPsi v = suzukiCheckpointBregman u v := by
  rw [suzukiPsi_sub_eq_checkpoint_reservoir_difference hN hu hv, suzukiCheckpointBregman,
    hstationary]

/-- Nonnegativity of every unique event-cell checkpoint. -/
def SuzukiCheckpointNonnegative : Prop :=
  ∀ N : ℕ, 2 ≤ N → ∀ v : ℝ, v ∈ suzukiCheckpointCell N →
    IsMinOn suzukiPsi (suzukiCheckpointCell N) v → 0 ≤ suzukiPsi v

/-- **Checkpoint reduction.**  RH is equivalent to nonnegative margins at every unique
integer event-cell checkpoint.  The prime-free interval is discharged by the unconditional
first-gap positivity theorem; all later points lie in one event cell. -/
theorem riemannHypothesis_iff_suzukiCheckpointNonnegative :
    RiemannHypothesis ↔ SuzukiCheckpointNonnegative := by
  constructor
  · intro hRH N hN v hv _
    have hvlog : Real.log 2 ≤ v := suzukiCheckpointCell_subset_Ici_log_two hN hv
    exact suzukiPsiPointwiseNonnegative_of_riemannHypothesis hRH v
      ((Real.log_pos (by norm_num : (1 : ℝ) < 2)).trans_le hvlog).le
  · intro hcheck
    rw [riemannHypothesis_iff_suzukiPsiPointwiseNonnegative]
    intro t ht
    rcases ht.eq_or_lt with rfl | htpos
    · simpa only [suzukiPsi_zero]
    obtain ⟨t0, htwo, hsmall⟩ := suzuki_theorem_four_one
    rcases lt_or_ge t t0 with hlt | hlarge
    · exact (hsmall t htpos hlt).le
    · let N : ℕ := ⌊Real.exp t⌋₊
      have hlogtwo : Real.log 2 ≤ t := htwo.le.trans hlarge
      have htwoexp : (2 : ℝ) ≤ Real.exp t := by
        rw [← Real.exp_log (by norm_num : (0 : ℝ) < 2)]
        exact Real.exp_le_exp.mpr hlogtwo
      have hNtwo : 2 ≤ N := by
        exact Nat.le_floor htwoexp
      have hNpos : (0 : ℝ) < N := by exact_mod_cast (lt_of_lt_of_le (by omega) hNtwo)
      have hNp1pos : (0 : ℝ) < ((N + 1 : ℕ) : ℝ) := by positivity
      have hfloorle : (N : ℝ) ≤ Real.exp t := Nat.floor_le (Real.exp_pos t).le
      have hfloorlt : Real.exp t < ((N + 1 : ℕ) : ℝ) := by
        simpa only [N, Nat.cast_add, Nat.cast_one] using Nat.lt_floor_add_one (Real.exp t)
      have htcell : t ∈ suzukiCheckpointCell N := by
        constructor
        · exact (Real.log_le_iff_le_exp hNpos).mpr hfloorle
        · exact (Real.le_log_iff_exp_le hNp1pos).mpr hfloorlt.le
      obtain ⟨v, hv, hmin⟩ := exists_suzukiCheckpoint_isMinOn hNtwo
      exact (hcheck N hNtwo v hv hmin).trans ((isMinOn_iff.mp hmin) t htcell)

/-- Explicit scalar checkpoint condition: restricted Legendre--Mangoldt conjugate never exceeds
the corresponding logarithmic prime moment. -/
def SuzukiCheckpointConjugateLeMoment : Prop :=
  ∀ N : ℕ, 2 ≤ N →
    suzukiCheckpointConjugate N ≤ suzukiCheckpointMoment N

/-- Minimizer quantification in the checkpoint criterion is exactly the scalar conjugate--moment
inequality on each integer event cell. -/
theorem suzukiCheckpointNonnegative_iff_conjugateLeMoment :
    SuzukiCheckpointNonnegative ↔ SuzukiCheckpointConjugateLeMoment := by
  constructor
  · intro h N hN
    obtain ⟨v, hv, hmin, hvalue⟩ :=
      exists_suzukiCheckpoint_legendre_representation hN
    have hnonneg := h N hN v hv hmin
    rw [hvalue] at hnonneg
    linarith
  · intro h N hN v hv hmin
    obtain ⟨u, hu, hminu, hvalue⟩ :=
      exists_suzukiCheckpoint_legendre_representation hN
    have hvu : suzukiPsi v ≤ suzukiPsi u :=
      (isMinOn_iff.mp hmin) u hu
    have huv : suzukiPsi u ≤ suzukiPsi v :=
      (isMinOn_iff.mp hminu) v hv
    have heq : suzukiPsi v = suzukiPsi u := le_antisymm hvu huv
    rw [heq, hvalue]
    linarith [h N hN]

/-- **Legendre--Mangoldt scalar criterion.** RH is exactly domination of every restricted
checkpoint conjugate by its literal logarithmic prime moment. -/
theorem riemannHypothesis_iff_suzukiCheckpointConjugateLeMoment :
    RiemannHypothesis ↔ SuzukiCheckpointConjugateLeMoment :=
  riemannHypothesis_iff_suzukiCheckpointNonnegative.trans
    suzukiCheckpointNonnegative_iff_conjugateLeMoment

/-- One weighted running sum of all negative checkpoint conjugate--moment margins exposed through
stage `N`. Multiplication by `N` makes any fixed negative cell force escape to `-∞`. -/
noncomputable def suzukiCheckpointGlobalNegativeSum (N : ℕ) : ℝ :=
  (N : ℝ) * ∑ k ∈ Finset.range (N + 1),
    min (suzukiCheckpointMoment (k + 2) -
      suzukiCheckpointConjugate (k + 2)) 0

/-- The global Suzuki checkpoint negative-sum sequence does not diverge to negative infinity. -/
def SuzukiCheckpointGlobalNegativeSumNondivergent : Prop :=
  ¬ Tendsto suzukiCheckpointGlobalNegativeSum atTop atBot

/-- One-sequence nondivergence already recovers every checkpoint conjugate--moment inequality. -/
theorem suzukiCheckpointGlobalNegativeSumNondivergent_iff_conjugateLeMoment :
    SuzukiCheckpointGlobalNegativeSumNondivergent ↔
      SuzukiCheckpointConjugateLeMoment := by
  constructor
  · intro hglobal N hN
    by_contra hle
    have hneg : suzukiCheckpointMoment N - suzukiCheckpointConjugate N < 0 := by
      linarith
    let k₀ : ℕ := N - 2
    have hk₀ : k₀ + 2 = N := by
      dsimp only [k₀]
      omega
    have hscaled : Tendsto
        (fun n : ℕ => (n : ℝ) *
          (suzukiCheckpointMoment N - suzukiCheckpointConjugate N))
        atTop atBot := by
      simpa only [mul_comm] using
        tendsto_natCast_atTop_atTop.const_mul_atTop_of_neg hneg
    apply hglobal
    rw [tendsto_atBot]
    intro b
    filter_upwards [tendsto_atBot.1 hscaled b, eventually_ge_atTop k₀] with n hn hnk
    have hk₀mem : k₀ ∈ Finset.range (n + 1) := by
      simp only [Finset.mem_range]
      omega
    have hsumErase :
        (∑ k ∈ (Finset.range (n + 1)).erase k₀,
          min (suzukiCheckpointMoment (k + 2) -
            suzukiCheckpointConjugate (k + 2)) 0) ≤ 0 := by
      exact Finset.sum_nonpos fun k hk => min_le_right _ _
    calc
      suzukiCheckpointGlobalNegativeSum n =
          (n : ℝ) *
            ((∑ k ∈ (Finset.range (n + 1)).erase k₀,
              min (suzukiCheckpointMoment (k + 2) -
                suzukiCheckpointConjugate (k + 2)) 0) +
              min (suzukiCheckpointMoment (k₀ + 2) -
                suzukiCheckpointConjugate (k₀ + 2)) 0) := by
        unfold suzukiCheckpointGlobalNegativeSum
        rw [Finset.sum_erase_add _ _ hk₀mem]
      _ ≤ (n : ℝ) *
          min (suzukiCheckpointMoment (k₀ + 2) -
            suzukiCheckpointConjugate (k₀ + 2)) 0 := by
        apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg n)
        exact add_le_of_nonpos_left hsumErase
      _ = (n : ℝ) *
          (suzukiCheckpointMoment N - suzukiCheckpointConjugate N) := by
        rw [hk₀, min_eq_left hneg.le]
      _ ≤ b := hn
  · intro hmargin hlim
    obtain ⟨N, hN⟩ := (tendsto_atBot.1 hlim (-1)).exists
    have hzero : suzukiCheckpointGlobalNegativeSum N = 0 := by
      unfold suzukiCheckpointGlobalNegativeSum
      rw [Finset.sum_eq_zero]
      · norm_num
      · intro k hk
        rw [min_eq_right]
        exact sub_nonneg.mpr (hmargin (k + 2) (by omega))
    rw [hzero] at hN
    norm_num at hN

/-- **One-sequence Suzuki checkpoint criterion.** RH is equivalent to nondivergence of one
weighted scalar running sum of the literal checkpoint conjugate--moment defects. -/
theorem suzukiCheckpointGlobalNegativeSumNondivergent_iff_riemannHypothesis :
    SuzukiCheckpointGlobalNegativeSumNondivergent ↔ RiemannHypothesis :=
  suzukiCheckpointGlobalNegativeSumNondivergent_iff_conjugateLeMoment.trans
    riemannHypothesis_iff_suzukiCheckpointConjugateLeMoment.symm

end RHTower
