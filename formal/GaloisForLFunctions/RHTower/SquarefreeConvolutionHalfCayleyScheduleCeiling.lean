import GaloisForLFunctions.RHTower.SquarefreeConvolutionHalfVitaliNormalityNoGo

/-!
# Prime-scale ceiling for scheduled Cayley--Dirichlet approximants

Pair Cayley degree `kappa N` with Dirichlet cutoff `N`.  Pointwise boundedness at `s = 4/7`
forces the smaller of the two adjacent Cayley degrees at every prime cutoff to remain at most
logarithmic in that prime.  Equivalently, any schedule whose adjacent prime scale is
superlogarithmic cannot make the raw products bounded.

This is the sharp positive survivor of the same-index normality no-go: changing relative scales
is necessary, and this theorem quantifies the maximum viable scale before any arithmetic
cancellation estimate is attempted.
-/

open Complex Filter Metric Set Topology

namespace RHTower

noncomputable section

/-- Cayley approximation degree `kappa N` paired with Dirichlet cutoff `N`. -/
def poleClearedFirstTraceScheduledApprox (kappa : ℕ → ℕ) (N : ℕ) (s : ℂ) : ℂ :=
  poleFactorSqrtApprox (kappa N) s * squarefreeHalfDirichletPartialSum N s /
    squarefreeCarlemanHalfDet s

theorem norm_poleFactorSqrtApprox_cayleyExteriorPoint_geometric
    {N : ℕ} (hN : 3 ≤ N) :
    (5 / 4 : ℝ) ^ (N - 1) / 20 ≤
      ‖poleFactorSqrtApprox N cayleyExteriorPoint‖ := by
  obtain ⟨m, rfl | rfl⟩ := Nat.even_or_odd' N
  · have hm2 : 2 ≤ m := by omega
    obtain ⟨k, hk⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
    subst m
    rw [show 2 * (k + 1) - 1 = 2 * k + 1 by omega,
      show 2 * (k + 1) = 2 * k + 2 by omega]
    exact norm_poleFactorSqrtApprox_cayleyExteriorPoint_even_ge k
  · have hm1 : 1 ≤ m := by omega
    simpa only [Nat.add_sub_cancel] using
      norm_poleFactorSqrtApprox_cayleyExteriorPoint_odd_ge m hm1

theorem scheduled_geometric_mul_norm_partialSum_le
    {kappa : ℕ → ℕ} {N : ℕ} {C : ℝ} (hkappa : 3 ≤ kappa N)
    (hsource : ‖poleClearedFirstTraceScheduledApprox kappa N cayleyExteriorPoint‖ ≤ C) :
    (5 / 4 : ℝ) ^ (kappa N - 1) *
        ‖squarefreeHalfDirichletPartialSum N cayleyExteriorPoint‖ ≤
      20 * C * ‖squarefreeCarlemanHalfDet cayleyExteriorPoint‖ := by
  have hr := norm_poleFactorSqrtApprox_cayleyExteriorPoint_geometric hkappa
  have hdetpos : 0 < ‖squarefreeCarlemanHalfDet cayleyExteriorPoint‖ :=
    norm_pos_iff.mpr (squarefreeCarlemanHalfDet_ne_zero cayleyExteriorPoint)
  have hprod :
      ‖poleFactorSqrtApprox (kappa N) cayleyExteriorPoint‖ *
          ‖squarefreeHalfDirichletPartialSum N cayleyExteriorPoint‖ ≤
        C * ‖squarefreeCarlemanHalfDet cayleyExteriorPoint‖ := by
    rw [poleClearedFirstTraceScheduledApprox, norm_div, norm_mul] at hsource
    exact (div_le_iff₀ hdetpos).mp hsource
  have hscaled :
      ((5 / 4 : ℝ) ^ (kappa N - 1) / 20) *
          ‖squarefreeHalfDirichletPartialSum N cayleyExteriorPoint‖ ≤
        C * ‖squarefreeCarlemanHalfDet cayleyExteriorPoint‖ :=
    le_trans (mul_le_mul_of_nonneg_right hr (norm_nonneg _)) hprod
  nlinarith

/-- Pointwise boundedness forces logarithmic-scale Cayley degree along adjacent prime cutoffs. -/
theorem cayleySchedule_prime_scale_ceiling
    (kappa : ℕ → ℕ) (hkappa : ∀ N, 3 ≤ kappa N)
    (hbound : ∃ C : ℝ, ∀ N,
      ‖poleClearedFirstTraceScheduledApprox kappa N cayleyExteriorPoint‖ ≤ C) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ p : ℕ, p.Prime →
      (5 / 4 : ℝ) ^
          min (kappa p - 1) (kappa (p + 1) - 1) ≤ B * p := by
  obtain ⟨C, hC⟩ := hbound
  have hCnonneg : 0 ≤ C := le_trans (norm_nonneg _) (hC 0)
  let K : ℝ := 20 * C * ‖squarefreeCarlemanHalfDet cayleyExteriorPoint‖
  have hKnonneg : 0 ≤ K := by
    dsimp [K]
    positivity
  have hpartial (N : ℕ) :
      (5 / 4 : ℝ) ^ (kappa N - 1) *
          ‖squarefreeHalfDirichletPartialSum N cayleyExteriorPoint‖ ≤ K := by
    dsimp [K]
    exact scheduled_geometric_mul_norm_partialSum_le (hkappa N) (hC N)
  refine ⟨4 * K, by positivity, ?_⟩
  intro p hp
  let e : ℕ := min (kappa p - 1) (kappa (p + 1) - 1)
  have heleft : e ≤ kappa p - 1 := min_le_left _ _
  have heright : e ≤ kappa (p + 1) - 1 := min_le_right _ _
  have hpowleft : (5 / 4 : ℝ) ^ e ≤ (5 / 4 : ℝ) ^ (kappa p - 1) :=
    pow_le_pow_right₀ (by norm_num) heleft
  have hpowright : (5 / 4 : ℝ) ^ e ≤ (5 / 4 : ℝ) ^ (kappa (p + 1) - 1) :=
    pow_le_pow_right₀ (by norm_num) heright
  have hpbound :
      (5 / 4 : ℝ) ^ e *
          ‖squarefreeHalfDirichletPartialSum p cayleyExteriorPoint‖ ≤ K :=
    le_trans (mul_le_mul_of_nonneg_right hpowleft (norm_nonneg _)) (hpartial p)
  have hsuccbound :
      (5 / 4 : ℝ) ^ e *
          ‖squarefreeHalfDirichletPartialSum (p + 1) cayleyExteriorPoint‖ ≤ K :=
    le_trans (mul_le_mul_of_nonneg_right hpowright (norm_nonneg _)) (hpartial (p + 1))
  have hsucc := squarefreeHalfDirichletPartialSum_succ p cayleyExteriorPoint
  have htermEq :
      LSeries.term squarefreeConvolutionHalf cayleyExteriorPoint p =
        squarefreeHalfDirichletPartialSum (p + 1) cayleyExteriorPoint -
          squarefreeHalfDirichletPartialSum p cayleyExteriorPoint := by
    rw [hsucc]
    ring
  have htri :
      ‖LSeries.term squarefreeConvolutionHalf cayleyExteriorPoint p‖ ≤
        ‖squarefreeHalfDirichletPartialSum (p + 1) cayleyExteriorPoint‖ +
          ‖squarefreeHalfDirichletPartialSum p cayleyExteriorPoint‖ := by
    rw [htermEq]
    exact norm_sub_le _ _
  have htermUpper :
      (5 / 4 : ℝ) ^ e *
          ‖LSeries.term squarefreeConvolutionHalf cayleyExteriorPoint p‖ ≤ 2 * K := by
    calc
      (5 / 4 : ℝ) ^ e *
          ‖LSeries.term squarefreeConvolutionHalf cayleyExteriorPoint p‖ ≤
          (5 / 4 : ℝ) ^ e *
            (‖squarefreeHalfDirichletPartialSum (p + 1) cayleyExteriorPoint‖ +
              ‖squarefreeHalfDirichletPartialSum p cayleyExteriorPoint‖) :=
        mul_le_mul_of_nonneg_left htri (pow_nonneg (by norm_num) _)
      _ = (5 / 4 : ℝ) ^ e *
            ‖squarefreeHalfDirichletPartialSum (p + 1) cayleyExteriorPoint‖ +
          (5 / 4 : ℝ) ^ e *
            ‖squarefreeHalfDirichletPartialSum p cayleyExteriorPoint‖ := by ring
      _ ≤ K + K := add_le_add hsuccbound hpbound
      _ = 2 * K := by ring
  have hlowerTerm :=
    inv_two_mul_natCast_le_norm_squarefreeConvolutionHalf_term_prime p hp
  have hlower :
      (5 / 4 : ℝ) ^ e / (2 * (p : ℝ)) ≤
        (5 / 4 : ℝ) ^ e *
          ‖LSeries.term squarefreeConvolutionHalf cayleyExteriorPoint p‖ := by
    calc
      (5 / 4 : ℝ) ^ e / (2 * (p : ℝ)) =
          (5 / 4 : ℝ) ^ e * (1 / (2 * (p : ℝ))) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hlowerTerm (pow_nonneg (by norm_num) e)
  have hfrac : (5 / 4 : ℝ) ^ e / (2 * (p : ℝ)) ≤ 2 * K :=
    hlower.trans htermUpper
  have hp0 : (0 : ℝ) < 2 * p := by exact_mod_cast (mul_pos (by omega : 0 < 2) hp.pos)
  have hmul := (div_le_iff₀ hp0).mp hfrac
  change (5 / 4 : ℝ) ^ e ≤ (4 * K) * p
  nlinarith

/-- Cayley degree grows too quickly for adjacent prime cutoffs if this ratio diverges. -/
def CayleySchedulePrimeScaleDiverges (kappa : ℕ → ℕ) : Prop :=
  Tendsto (fun N : ℕ =>
    (5 / 4 : ℝ) ^ min (kappa N - 1) (kappa (N + 1) - 1) / N) atTop atTop

theorem not_scheduledApprox_boundedAtExteriorPoint_of_primeScaleDiverges
    (kappa : ℕ → ℕ) (hkappa : ∀ N, 3 ≤ kappa N)
    (hdiv : CayleySchedulePrimeScaleDiverges kappa) :
    ¬ ∃ C : ℝ, ∀ N,
      ‖poleClearedFirstTraceScheduledApprox kappa N cayleyExteriorPoint‖ ≤ C := by
  intro hbound
  obtain ⟨B, hBnonneg, hceiling⟩ :=
    cayleySchedule_prime_scale_ceiling kappa hkappa hbound
  have heventually : ∀ᶠ N : ℕ in atTop,
      B < (5 / 4 : ℝ) ^ min (kappa N - 1) (kappa (N + 1) - 1) / N :=
    hdiv.eventually_gt_atTop B
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp heventually
  obtain ⟨p, hpN, hp⟩ := Nat.exists_infinite_primes N
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hlarge := hN p hpN
  have hsmall :
      (5 / 4 : ℝ) ^ min (kappa p - 1) (kappa (p + 1) - 1) / p ≤ B := by
    exact (div_le_iff₀ hp0).2 (hceiling p hp)
  exact (not_lt_of_ge hsmall) hlarge

end

end RHTower
