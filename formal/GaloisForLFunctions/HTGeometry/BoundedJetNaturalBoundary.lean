import GaloisForLFunctions.HTGeometry.AnalyticODEExistence
import GaloisForLFunctions.HTGeometry.MvPolynomialSmooth
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.Complex.AbsMax
import Mathlib.Analysis.Calculus.Deriv.Prod

/-!
# Bounded jets of an algebraic differential equation continue across the unit circle
-/

namespace GaloisForLFunctions.HTGeometry

open Metric Set Filter

noncomputable section

variable {n : ℕ}

/-- The augmented jet vector `(z, f(z), f'(z), …, f⁽ⁿ⁾(z))`. -/
def odeJet (f : ℂ → ℂ) (n : ℕ) (z : ℂ) : Fin (n + 2) → ℂ :=
  fun i => if (i : ℕ) = 0 then z else iteratedDeriv ((i : ℕ) - 1) f z

theorem odeJet_zero (f : ℂ → ℂ) (n : ℕ) (z : ℂ) : odeJet f n z 0 = z := by
  simp [odeJet]

theorem odeJet_succ (f : ℂ → ℂ) (n : ℕ) (z : ℂ) (i : Fin (n + 2)) (hi : (i : ℕ) ≠ 0) :
    odeJet f n z i = iteratedDeriv ((i : ℕ) - 1) f z := by
  simp [odeJet, hi]

/-- The autonomous companion vector field of the differentiated algebraic equation. -/
def companionVec (n : ℕ) (N S : MvPolynomial (Fin (n + 2)) ℂ) (v : Fin (n + 2) → ℂ) :
    Fin (n + 2) → ℂ :=
  fun i =>
    if (i : ℕ) = 0 then 1
    else if h : (i : ℕ) < n + 1 then v ⟨(i : ℕ) + 1, by omega⟩
    else MvPolynomial.eval v N / MvPolynomial.eval v S

/-! ## The jet solves the companion system -/

private theorem analyticOnNhd_iteratedDeriv {f : ℂ → ℂ} {U : Set ℂ}
    (hf : AnalyticOnNhd ℂ f U) : ∀ j : ℕ, AnalyticOnNhd ℂ (iteratedDeriv j f) U := by
  intro j
  induction j with
  | zero => simpa [iteratedDeriv_zero] using hf
  | succ j ih =>
      rw [iteratedDeriv_succ]
      exact ih.deriv

theorem hasDerivAt_iteratedDeriv {f : ℂ → ℂ} {U : Set ℂ}
    (hf : AnalyticOnNhd ℂ f U) (j : ℕ) {z : ℂ} (hz : z ∈ U) :
    HasDerivAt (iteratedDeriv j f) (iteratedDeriv (j + 1) f z) z := by
  have han := analyticOnNhd_iteratedDeriv hf j z hz
  have hd : DifferentiableAt ℂ (iteratedDeriv j f) z := han.differentiableAt
  rw [iteratedDeriv_succ]
  exact hd.hasDerivAt

/-- The augmented jet of an analytic solution solves the autonomous companion system at every
point where the separant evaluation is nonzero. -/
theorem hasDerivAt_odeJet {f : ℂ → ℂ} {N S : MvPolynomial (Fin (n + 2)) ℂ} {U : Set ℂ}
    (hf : AnalyticOnNhd ℂ f U)
    (hODE : ∀ z ∈ U, MvPolynomial.eval (odeJet f n z) S * iteratedDeriv (n + 1) f z
      = MvPolynomial.eval (odeJet f n z) N)
    {z : ℂ} (hz : z ∈ U) (hSz : MvPolynomial.eval (odeJet f n z) S ≠ 0) :
    HasDerivAt (odeJet f n) (companionVec n N S (odeJet f n z)) z := by
  rw [hasDerivAt_pi]
  intro i
  by_cases h0 : (i : ℕ) = 0
  · have hfun : (fun w : ℂ => odeJet f n w i) = fun w : ℂ => w := by
      funext w
      simp [odeJet, h0]
    have hval : companionVec n N S (odeJet f n z) i = 1 := by
      simp [companionVec, h0]
    rw [hfun, hval]
    exact hasDerivAt_id z
  · by_cases h1 : (i : ℕ) < n + 1
    · have hfun : (fun w : ℂ => odeJet f n w i) = iteratedDeriv ((i : ℕ) - 1) f := by
        funext w
        simp [odeJet, h0]
      have hval : companionVec n N S (odeJet f n z) i
          = iteratedDeriv ((i : ℕ) - 1 + 1) f z := by
        rw [companionVec]
        simp only [h0, if_false, dif_pos h1]
        rw [odeJet_succ f n z ⟨(i : ℕ) + 1, by omega⟩ (by simp)]
        congr 1
        show ((i : ℕ) + 1) - 1 = (i : ℕ) - 1 + 1
        omega
      rw [hfun, hval]
      exact hasDerivAt_iteratedDeriv hf _ hz
    · have hlast : (i : ℕ) = n + 1 := by omega
      have hfun : (fun w : ℂ => odeJet f n w i) = iteratedDeriv n f := by
        funext w
        rw [odeJet_succ f n w i h0, hlast]
        norm_num
      have hval : companionVec n N S (odeJet f n z) i = iteratedDeriv (n + 1) f z := by
        rw [companionVec]
        simp only [h0, if_false, dif_neg h1]
        rw [eq_comm, eq_div_iff hSz, mul_comm]
        exact hODE z hz
      rw [hfun, hval]
      have := hasDerivAt_iteratedDeriv hf n hz
      exact this

/-! ## Analytic and metric properties of the companion field -/

theorem differentiableOn_companionVec (n : ℕ) (N S : MvPolynomial (Fin (n + 2)) ℂ)
    {V : Set (Fin (n + 2) → ℂ)} (hS : ∀ v ∈ V, MvPolynomial.eval v S ≠ 0) :
    DifferentiableOn ℂ (companionVec n N S) V := by
  rw [differentiableOn_pi]
  intro i
  by_cases h0 : (i : ℕ) = 0
  · have hfun : (fun v : Fin (n + 2) → ℂ => companionVec n N S v i) = fun _ => (1 : ℂ) := by
      funext v
      simp [companionVec, h0]
    rw [hfun]
    exact differentiableOn_const 1
  · by_cases h1 : (i : ℕ) < n + 1
    · have hfun : (fun v : Fin (n + 2) → ℂ => companionVec n N S v i)
          = fun v : Fin (n + 2) → ℂ => v ⟨(i : ℕ) + 1, by omega⟩ := by
        funext v
        simp [companionVec, h0, h1]
      rw [hfun]
      exact ((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin (n + 2) => ℂ)
        (⟨(i : ℕ) + 1, by omega⟩ : Fin (n + 2))).differentiable).differentiableOn
    · have hfun : (fun v : Fin (n + 2) → ℂ => companionVec n N S v i)
          = fun v : Fin (n + 2) → ℂ =>
            MvPolynomial.eval v N / MvPolynomial.eval v S := by
        funext v
        simp [companionVec, h0, h1]
      rw [hfun]
      have hN : DifferentiableOn ℂ
          (fun v : Fin (n + 2) → ℂ => MvPolynomial.eval v N) V :=
        (differentiable_mvPolynomial_eval N).differentiableOn
      have hSd : DifferentiableOn ℂ
          (fun v : Fin (n + 2) → ℂ => MvPolynomial.eval v S) V :=
        (differentiable_mvPolynomial_eval S).differentiableOn
      have hfun2 : (fun v : Fin (n + 2) → ℂ =>
          MvPolynomial.eval v N / MvPolynomial.eval v S)
          = fun v : Fin (n + 2) → ℂ =>
            MvPolynomial.eval v N * (MvPolynomial.eval v S)⁻¹ := by
        funext v
        rw [div_eq_mul_inv]
      rw [hfun2]
      exact hN.mul (hSd.inv hS)

/-- A uniform bound and a uniform Lipschitz constant for the companion field on the region where
the state is bounded and the separant evaluation is bounded away from zero. -/
theorem exists_bound_lipschitz_companionVec (n : ℕ) (N S : MvPolynomial (Fin (n + 2)) ℂ)
    (R ε : ℝ) (hε : 0 < ε) :
    ∃ MΦ LΦ : ℝ, 0 ≤ MΦ ∧ 0 ≤ LΦ ∧
      (∀ v : Fin (n + 2) → ℂ, ‖v‖ ≤ R → ε ≤ ‖MvPolynomial.eval v S‖ →
        ‖companionVec n N S v‖ ≤ MΦ) ∧
      (∀ v w : Fin (n + 2) → ℂ, ‖v‖ ≤ R → ‖w‖ ≤ R → ε ≤ ‖MvPolynomial.eval v S‖ →
        ε ≤ ‖MvPolynomial.eval w S‖ →
        ‖companionVec n N S v - companionVec n N S w‖ ≤ LΦ * ‖v - w‖) := by
  obtain ⟨MN, hMN0, hMN⟩ := exists_bound_mvPolynomial_eval N (0 : Fin (n + 2) → ℂ) R
  obtain ⟨MS, hMS0, hMS⟩ := exists_bound_mvPolynomial_eval S (0 : Fin (n + 2) → ℂ) R
  obtain ⟨LN, hLN0, hLN⟩ := exists_lipschitz_mvPolynomial_eval N (0 : Fin (n + 2) → ℂ) R
  obtain ⟨LS, hLS0, hLS⟩ := exists_lipschitz_mvPolynomial_eval S (0 : Fin (n + 2) → ℂ) R
  refine ⟨max (max 1 R) (MN / ε), max 1 ((LN * MS + MN * LS) / ε ^ (2 : ℕ)), ?_, ?_, ?_, ?_⟩
  · exact le_trans (le_trans zero_le_one (le_max_left 1 R)) (le_max_left _ _)
  · exact le_trans zero_le_one (le_max_left _ _)
  · intro v hv hSv
    have hvmem : v ∈ closedBall (0 : Fin (n + 2) → ℂ) R := by
      rw [mem_closedBall_zero_iff]
      exact hv
    refine (pi_norm_le_iff_of_nonneg (by positivity)).mpr fun i => ?_
    by_cases h0 : (i : ℕ) = 0
    · have : companionVec n N S v i = 1 := by simp [companionVec, h0]
      rw [this]
      simp only [norm_one]
      exact le_trans (le_max_left 1 R) (le_max_left _ _)
    · by_cases h1 : (i : ℕ) < n + 1
      · have hval : companionVec n N S v i = v ⟨(i : ℕ) + 1, by omega⟩ := by
          simp [companionVec, h0, h1]
        rw [hval]
        exact le_trans (le_trans (norm_le_pi_norm v _) hv)
          (le_trans (le_max_right 1 R) (le_max_left _ _))
      · have hval : companionVec n N S v i
            = MvPolynomial.eval v N / MvPolynomial.eval v S := by
          simp [companionVec, h0, h1]
        rw [hval, norm_div]
        refine le_trans ?_ (le_max_right _ _)
        have h1' : ‖MvPolynomial.eval v N‖ ≤ MN := hMN v hvmem
        have hSpos : 0 < ‖MvPolynomial.eval v S‖ := lt_of_lt_of_le hε hSv
        rw [div_le_iff₀ hSpos]
        have hmul : MN / ε * ε ≤ MN / ε * ‖MvPolynomial.eval v S‖ :=
          mul_le_mul_of_nonneg_left hSv (by positivity)
        have hMNe : MN / ε * ε = MN := by field_simp
        linarith [h1', hmul, hMNe]
  · intro v w hv hw hSv hSw
    have hvmem : v ∈ closedBall (0 : Fin (n + 2) → ℂ) R := by
      rw [mem_closedBall_zero_iff]; exact hv
    have hwmem : w ∈ closedBall (0 : Fin (n + 2) → ℂ) R := by
      rw [mem_closedBall_zero_iff]; exact hw
    have hLnn : (0 : ℝ) ≤ max 1 ((LN * MS + MN * LS) / ε ^ (2 : ℕ)) :=
      le_trans zero_le_one (le_max_left _ _)
    refine (pi_norm_le_iff_of_nonneg (by positivity)).mpr fun i => ?_
    by_cases h0 : (i : ℕ) = 0
    · have hval : (companionVec n N S v - companionVec n N S w) i = 0 := by
        simp [companionVec, h0]
      rw [hval, norm_zero]
      positivity
    · by_cases h1 : (i : ℕ) < n + 1
      · have hval : (companionVec n N S v - companionVec n N S w) i
            = v ⟨(i : ℕ) + 1, by omega⟩ - w ⟨(i : ℕ) + 1, by omega⟩ := by
          simp [companionVec, h0, h1]
        rw [hval]
        have hle : ‖v ⟨(i : ℕ) + 1, by omega⟩ - w ⟨(i : ℕ) + 1, by omega⟩‖ ≤ ‖v - w‖ := by
          have := norm_le_pi_norm (v - w) (⟨(i : ℕ) + 1, by omega⟩ : Fin (n + 2))
          simpa using this
        refine le_trans hle ?_
        nlinarith [norm_nonneg (v - w), le_max_left (1 : ℝ) ((LN * MS + MN * LS) / ε ^ (2 : ℕ))]
      · have hval : (companionVec n N S v - companionVec n N S w) i
            = MvPolynomial.eval v N / MvPolynomial.eval v S
              - MvPolynomial.eval w N / MvPolynomial.eval w S := by
          simp [companionVec, h0, h1]
        rw [hval]
        have hSv0 : MvPolynomial.eval v S ≠ 0 := by
          intro hc
          rw [hc, norm_zero] at hSv
          linarith
        have hSw0 : MvPolynomial.eval w S ≠ 0 := by
          intro hc
          rw [hc, norm_zero] at hSw
          linarith
        have hkey : MvPolynomial.eval v N / MvPolynomial.eval v S
            - MvPolynomial.eval w N / MvPolynomial.eval w S
            = ((MvPolynomial.eval v N - MvPolynomial.eval w N) * MvPolynomial.eval w S
                - MvPolynomial.eval w N * (MvPolynomial.eval v S - MvPolynomial.eval w S))
              / (MvPolynomial.eval v S * MvPolynomial.eval w S) := by
          field_simp
          ring
        rw [hkey, norm_div, norm_mul]
        have hbN := hLN v hvmem w hwmem
        have hbS := hLS v hvmem w hwmem
        have hMNw : ‖MvPolynomial.eval w N‖ ≤ MN := hMN w hwmem
        have hMSw : ‖MvPolynomial.eval w S‖ ≤ MS := hMS w hwmem
        have hnum : ‖(MvPolynomial.eval v N - MvPolynomial.eval w N) * MvPolynomial.eval w S
              - MvPolynomial.eval w N * (MvPolynomial.eval v S - MvPolynomial.eval w S)‖
            ≤ (LN * MS + MN * LS) * ‖v - w‖ := by
          refine le_trans (norm_sub_le _ _) ?_
          rw [norm_mul, norm_mul]
          have h1' : ‖MvPolynomial.eval v N - MvPolynomial.eval w N‖ *
              ‖MvPolynomial.eval w S‖ ≤ (LN * ‖v - w‖) * MS := by
            refine mul_le_mul hbN hMSw (norm_nonneg _) (by positivity)
          have h2' : ‖MvPolynomial.eval w N‖ *
              ‖MvPolynomial.eval v S - MvPolynomial.eval w S‖ ≤ MN * (LS * ‖v - w‖) := by
            refine mul_le_mul hMNw hbS (norm_nonneg _) hMN0
          nlinarith [h1', h2']
        have hden : ε ^ (2 : ℕ) ≤ ‖MvPolynomial.eval v S‖ * ‖MvPolynomial.eval w S‖ := by
          nlinarith [hε, hSv, hSw]
        have hdenpos : (0 : ℝ) < ‖MvPolynomial.eval v S‖ * ‖MvPolynomial.eval w S‖ := by
          nlinarith [hε, hSv, hSw]
        rw [div_le_iff₀ hdenpos]
        have hnn : (0 : ℝ) ≤ ‖v - w‖ := norm_nonneg _
        have hcoef : (LN * MS + MN * LS) / ε ^ (2 : ℕ) ≤ max 1 ((LN * MS + MN * LS) / ε ^ (2 : ℕ)) :=
          le_max_right _ _
        have hLMnn : (0 : ℝ) ≤ LN * MS + MN * LS := by positivity
        have hε2 : (0 : ℝ) < ε ^ (2 : ℕ) := by positivity
        calc ‖(MvPolynomial.eval v N - MvPolynomial.eval w N) * MvPolynomial.eval w S
              - MvPolynomial.eval w N * (MvPolynomial.eval v S - MvPolynomial.eval w S)‖
            ≤ (LN * MS + MN * LS) * ‖v - w‖ := hnum
          _ = ((LN * MS + MN * LS) / ε ^ (2 : ℕ)) * ‖v - w‖ * ε ^ (2 : ℕ) := by field_simp
          _ ≤ max 1 ((LN * MS + MN * LS) / ε ^ (2 : ℕ)) * ‖v - w‖ *
              (‖MvPolynomial.eval v S‖ * ‖MvPolynomial.eval w S‖) := by
              have hA : ((LN * MS + MN * LS) / ε ^ (2 : ℕ)) * ‖v - w‖
                  ≤ max 1 ((LN * MS + MN * LS) / ε ^ (2 : ℕ)) * ‖v - w‖ :=
                mul_le_mul_of_nonneg_right hcoef hnn
              have hB : (0 : ℝ) ≤ ((LN * MS + MN * LS) / ε ^ (2 : ℕ)) * ‖v - w‖ := by positivity
              nlinarith [hA, hB, hden, hε2]

/-! ## Selecting a good interior point by the maximum modulus principle -/

theorem differentiableOn_odeJet {f : ℂ → ℂ} {U : Set ℂ} (hf : AnalyticOnNhd ℂ f U) :
    DifferentiableOn ℂ (odeJet f n) U := by
  rw [differentiableOn_pi]
  intro i
  by_cases h0 : (i : ℕ) = 0
  · have hfun : (fun z : ℂ => odeJet f n z i) = fun z : ℂ => z := by
      funext z
      simp [odeJet, h0]
    rw [hfun]
    exact differentiableOn_id
  · have hfun : (fun z : ℂ => odeJet f n z i) = iteratedDeriv ((i : ℕ) - 1) f := by
      funext z
      simp [odeJet, h0]
    rw [hfun]
    exact fun z hz => ((analyticOnNhd_iteratedDeriv hf ((i : ℕ) - 1)) z hz)
      |>.differentiableAt.differentiableWithinAt

theorem differentiableOn_evalJet {f : ℂ → ℂ} {U : Set ℂ} (hf : AnalyticOnNhd ℂ f U)
    (P : MvPolynomial (Fin (n + 2)) ℂ) :
    DifferentiableOn ℂ (fun z => MvPolynomial.eval (odeJet f n z) P) U := by
  have hjet := differentiableOn_odeJet (n := n) hf
  have hpoly : DifferentiableOn ℂ (fun v : Fin (n + 2) → ℂ => MvPolynomial.eval v P)
      Set.univ := (differentiable_mvPolynomial_eval P).differentiableOn
  exact hpoly.comp hjet (fun z _ => Set.mem_univ _)

/-- On every circle inside the domain the modulus of a holomorphic function dominates its value
at any interior point.  This replaces the boundary Fatou/F.&M. Riesz step. -/
theorem exists_norm_ge_on_sphere {g : ℂ → ℂ} {R r : ℝ}
    (hg : DifferentiableOn ℂ g (ball (0 : ℂ) R)) {z₀ : ℂ} (hz₀ : ‖z₀‖ < r) (hr : r < R) :
    ∃ z₁ : ℂ, ‖z₁‖ = r ∧ ‖g z₀‖ ≤ ‖g z₁‖ := by
  have hr0 : 0 < r := lt_of_le_of_lt (norm_nonneg z₀) hz₀
  have hcompact : IsCompact (sphere (0 : ℂ) r) := isCompact_sphere 0 r
  have hne : (sphere (0 : ℂ) r).Nonempty := by
    refine ⟨(r : ℂ), ?_⟩
    simp [Complex.norm_real, abs_of_pos hr0]
  have hcont : ContinuousOn (fun z => ‖g z‖) (sphere (0 : ℂ) r) := by
    refine ContinuousOn.norm ?_
    refine hg.continuousOn.mono ?_
    intro z hz
    rw [mem_sphere_iff_norm, sub_zero] at hz
    rw [mem_ball, dist_eq_norm, sub_zero, hz]
    exact hr
  obtain ⟨z₁, hz₁mem, hz₁max⟩ := hcompact.exists_isMaxOn hne hcont
  refine ⟨z₁, by simpa [mem_sphere_iff_norm, sub_zero] using hz₁mem, ?_⟩
  have hsub : closedBall (0 : ℂ) r ⊆ ball (0 : ℂ) R := by
    intro z hz
    rw [mem_closedBall, dist_eq_norm, sub_zero] at hz
    rw [mem_ball, dist_eq_norm, sub_zero]
    linarith
  have hdcc : DiffContOnCl ℂ g (ball (0 : ℂ) r) := by
    refine DiffContOnCl.mk_ball ?_ ?_
    · exact hg.mono (fun z hz => hsub (ball_subset_closedBall hz))
    · exact (hg.mono hsub).continuousOn
  have hfront : frontier (ball (0 : ℂ) r) = sphere (0 : ℂ) r := frontier_ball 0 (ne_of_gt hr0)
  have hbound : ∀ z ∈ frontier (ball (0 : ℂ) r), ‖g z‖ ≤ ‖g z₁‖ := by
    intro z hz
    rw [hfront] at hz
    exact hz₁max hz
  have hz₀mem : z₀ ∈ closure (ball (0 : ℂ) r) := by
    rw [closure_ball 0 (ne_of_gt hr0), mem_closedBall, dist_eq_norm, sub_zero]
    exact le_of_lt hz₀
  exact Complex.norm_le_of_forall_mem_frontier_norm_le isBounded_ball hdcc hbound hz₀mem

/-! ## The continuation theorem -/

/-- **Bounded jets of an algebraic differential equation continue across the unit circle.**
If `f` is holomorphic on the unit disk, its augmented order-`n` jet is bounded there, the
differentiated algebraic relation `S · f⁽ⁿ⁺¹⁾ = N` holds, and the separant evaluation `S` is not
identically zero along the jet, then `f` extends holomorphically to a disk that crosses the unit
circle.  In particular the unit circle is not a natural boundary of `f`. -/
theorem exists_analytic_continuation_of_bounded_jet
    {f : ℂ → ℂ} {N S : MvPolynomial (Fin (n + 2)) ℂ} {M : ℝ}
    (hf : AnalyticOnNhd ℂ f (ball (0 : ℂ) 1))
    (hjet : ∀ z ∈ ball (0 : ℂ) 1, ‖odeJet f n z‖ ≤ M)
    (hODE : ∀ z ∈ ball (0 : ℂ) 1,
      MvPolynomial.eval (odeJet f n z) S * iteratedDeriv (n + 1) f z
        = MvPolynomial.eval (odeJet f n z) N)
    (hSne : ∃ z₀ ∈ ball (0 : ℂ) 1, MvPolynomial.eval (odeJet f n z₀) S ≠ 0) :
    ∃ (z₁ : ℂ) (δ : ℝ), z₁ ∈ ball (0 : ℂ) 1 ∧ 0 < δ ∧ 1 - ‖z₁‖ < δ ∧
      ∃ g : ℂ → ℂ, DifferentiableOn ℂ g (ball z₁ δ) ∧
        ∀ z ∈ ball z₁ δ ∩ ball (0 : ℂ) 1, g z = f z := by
  classical
  obtain ⟨z₀, hz₀, hS0⟩ := hSne
  have hgSdiff : DifferentiableOn ℂ (fun z => MvPolynomial.eval (odeJet f n z) S)
      (ball (0 : ℂ) 1) := differentiableOn_evalJet hf S
  set ε : ℝ := ‖MvPolynomial.eval (odeJet f n z₀) S‖ with hεdef
  have hε0 : 0 < ε := norm_pos_iff.mpr hS0
  have hM0 : 0 ≤ M := le_trans (norm_nonneg _) (hjet z₀ hz₀)
  obtain ⟨LS, hLS0, hLS⟩ :=
    exists_lipschitz_mvPolynomial_eval S (0 : Fin (n + 2) → ℂ) (M + 1)
  set ρ' : ℝ := min 1 (ε / (2 * (LS + 1))) with hρ'def
  have hρ'0 : 0 < ρ' := lt_min one_pos (by positivity)
  have hρ'1 : ρ' ≤ 1 := min_le_left _ _
  obtain ⟨MΦ, LΦ, hMΦ0, hLΦ0, hMΦ, hLΦ⟩ :=
    exists_bound_lipschitz_companionVec n N S (M + 1) (ε / 2) (by positivity)
  set δ : ℝ := min 1 (min (ρ' / (2 * (MΦ + 1))) (1 / (2 * (LΦ + 1)))) with hδdef
  have hδ0 : 0 < δ := lt_min one_pos (lt_min (by positivity) (by positivity))
  have hδ1 : δ ≤ 1 := min_le_left _ _
  have hδM : δ * MΦ < ρ' := by
    have h1 : δ ≤ ρ' / (2 * (MΦ + 1)) := le_trans (min_le_right _ _) (min_le_left _ _)
    have h2 : δ * MΦ ≤ (ρ' / (2 * (MΦ + 1))) * MΦ :=
      mul_le_mul_of_nonneg_right h1 hMΦ0
    have h3 : (ρ' / (2 * (MΦ + 1))) * MΦ < ρ' := by
      rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
      nlinarith [hρ'0, hMΦ0]
    linarith
  have hδL : δ * LΦ < 1 := by
    have h1 : δ ≤ 1 / (2 * (LΦ + 1)) := le_trans (min_le_right _ _) (min_le_right _ _)
    have h2 : δ * LΦ ≤ (1 / (2 * (LΦ + 1))) * LΦ := mul_le_mul_of_nonneg_right h1 hLΦ0
    have h3 : (1 / (2 * (LΦ + 1))) * LΦ < 1 := by
      rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
      nlinarith [hLΦ0]
    linarith
  -- choose the radius
  have hz₀norm : ‖z₀‖ < 1 := by
    have := mem_ball.mp hz₀
    rwa [dist_eq_norm, sub_zero] at this
  set r : ℝ := max ((‖z₀‖ + 1) / 2) (1 - δ / 2) with hrdef
  have hr0 : ‖z₀‖ < r := lt_of_lt_of_le (by linarith) (le_max_left _ _)
  have hr1 : r < 1 := max_lt (by linarith) (by linarith)
  have hr2 : 1 - r < δ := by
    have : 1 - δ / 2 ≤ r := le_max_right _ _
    linarith
  obtain ⟨z₁, hz₁norm, hz₁ge⟩ := exists_norm_ge_on_sphere hgSdiff hr0 hr1
  have hz₁ball : z₁ ∈ ball (0 : ℂ) 1 := by
    rw [mem_ball, dist_eq_norm, sub_zero, hz₁norm]
    exact hr1
  set w₁ : Fin (n + 2) → ℂ := odeJet f n z₁ with hw₁def
  have hw₁norm : ‖w₁‖ ≤ M := hjet z₁ hz₁ball
  have hSz₁ : ε ≤ ‖MvPolynomial.eval w₁ S‖ := hz₁ge
  -- the good region
  have hregion : ∀ v ∈ ball w₁ ρ', ‖v‖ ≤ M + 1 ∧ ε / 2 ≤ ‖MvPolynomial.eval v S‖ := by
    intro v hv
    have hvw : ‖v - w₁‖ < ρ' := by
      have := mem_ball.mp hv
      rwa [dist_eq_norm] at this
    have hvnorm : ‖v‖ ≤ M + 1 := by
      have h1 : ‖v‖ - ‖w₁‖ ≤ ‖v - w₁‖ := norm_sub_norm_le v w₁
      linarith
    refine ⟨hvnorm, ?_⟩
    have hvmem : v ∈ closedBall (0 : Fin (n + 2) → ℂ) (M + 1) := by
      rw [mem_closedBall_zero_iff]
      exact hvnorm
    have hw₁mem : w₁ ∈ closedBall (0 : Fin (n + 2) → ℂ) (M + 1) := by
      rw [mem_closedBall_zero_iff]
      linarith
    have hdiff := hLS v hvmem w₁ hw₁mem
    have hLbound : LS * ‖v - w₁‖ ≤ ε / 2 := by
      have h1 : LS * ‖v - w₁‖ ≤ LS * ρ' := mul_le_mul_of_nonneg_left (le_of_lt hvw) hLS0
      have h2 : LS * ρ' ≤ LS * (ε / (2 * (LS + 1))) :=
        mul_le_mul_of_nonneg_left (min_le_right _ _) hLS0
      have h3 : LS * (ε / (2 * (LS + 1))) ≤ ε / 2 := by
        rw [mul_div_assoc'] at *
        rw [div_le_div_iff₀ (by positivity) (by norm_num)]
        nlinarith [hε0, hLS0]
      linarith
    have hlow : ‖MvPolynomial.eval w₁ S‖ - ‖MvPolynomial.eval v S‖
        ≤ ‖MvPolynomial.eval v S - MvPolynomial.eval w₁ S‖ := by
      have := norm_sub_norm_le (MvPolynomial.eval w₁ S) (MvPolynomial.eval v S)
      rwa [norm_sub_rev] at this
    linarith
  have hSnz : ∀ v ∈ ball w₁ ρ', MvPolynomial.eval v S ≠ 0 := by
    intro v hv hc
    have := (hregion v hv).2
    rw [hc, norm_zero] at this
    linarith
  -- solve the ODE
  have hΦdiff : DifferentiableOn ℂ
      (fun p : ℂ × (Fin (n + 2) → ℂ) => companionVec n N S p.2)
      (ball z₁ (1 : ℝ) ×ˢ ball w₁ ρ') := by
    have h1 : DifferentiableOn ℂ (companionVec n N S) (ball w₁ ρ') :=
      differentiableOn_companionVec n N S hSnz
    exact h1.comp differentiableOn_snd (fun p hp => hp.2)
  obtain ⟨F, hFval, hFmem, hFderiv⟩ := exists_analytic_ode_solution
    (Φ := fun _ : ℂ => fun w : Fin (n + 2) → ℂ => companionVec n N S w)
    (z₁ := z₁) (w₁ := w₁) (ρ := (1 : ℝ)) (ρ' := ρ') (M := MΦ) (L := LΦ) (δ := δ)
    hδ0 hδ1 hMΦ0 hLΦ0 hδM hδL hΦdiff
    (fun z _ w hw => hMΦ w (hregion w hw).1 (hregion w hw).2)
    (fun z _ w hw v hv => hLΦ w v (hregion w hw).1 (hregion v hv).1
      (hregion w hw).2 (hregion v hv).2)
  refine ⟨z₁, δ, hz₁ball, hδ0, by rw [hz₁norm]; exact hr2,
    fun z => F z ⟨1, by omega⟩, ?_, ?_⟩
  · have hFdiff : DifferentiableOn ℂ F (ball z₁ δ) :=
      fun z hz => (hFderiv z hz).differentiableAt.differentiableWithinAt
    exact ((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin (n + 2) => ℂ)
      (⟨1, by omega⟩ : Fin (n + 2))).differentiable.comp_differentiableOn hFdiff)
  · -- identity theorem on the overlap
    have hWconv : Convex ℝ (ball z₁ δ ∩ ball (0 : ℂ) 1) :=
      (convex_ball z₁ δ).inter (convex_ball 0 1)
    have hWopen : IsOpen (ball z₁ δ ∩ ball (0 : ℂ) 1) := isOpen_ball.inter isOpen_ball
    have hz₁W : z₁ ∈ ball z₁ δ ∩ ball (0 : ℂ) 1 := ⟨mem_ball_self hδ0, hz₁ball⟩
    -- both sides are analytic on the overlap
    have hFan : AnalyticOnNhd ℂ F (ball z₁ δ ∩ ball (0 : ℂ) 1) := by
      refine DifferentiableOn.analyticOnNhd ?_ hWopen
      exact fun z hz => (hFderiv z hz.1).differentiableAt.differentiableWithinAt
    have hJan : AnalyticOnNhd ℂ (odeJet f n) (ball z₁ δ ∩ ball (0 : ℂ) 1) := by
      refine DifferentiableOn.analyticOnNhd ?_ hWopen
      exact (differentiableOn_odeJet hf).mono (fun z hz => hz.2)
    -- local agreement near z₁
    have hcontJ : ContinuousAt (odeJet f n) z₁ :=
      ((differentiableOn_odeJet (n := n) hf).differentiableAt
        (isOpen_ball.mem_nhds hz₁ball)).continuousAt
    have hnhds : ∀ᶠ z in nhds z₁, odeJet f n z ∈ ball w₁ ρ' :=
      hcontJ.eventually_mem (isOpen_ball.mem_nhds (mem_ball_self hρ'0))
    have hnhds2 : ∀ᶠ z in nhds z₁, z ∈ ball z₁ δ := isOpen_ball.mem_nhds (mem_ball_self hδ0)
    have hnhds3 : ∀ᶠ z in nhds z₁, z ∈ ball (0 : ℂ) 1 := isOpen_ball.mem_nhds hz₁ball
    obtain ⟨η, hη0, hηsub⟩ := Metric.eventually_nhds_iff.mp (hnhds.and (hnhds2.and hnhds3))
    set η' : ℝ := min η δ with hη'def
    have hη'0 : 0 < η' := lt_min hη0 hδ0
    have hη'ball : ∀ z ∈ ball z₁ η', odeJet f n z ∈ ball w₁ ρ' ∧ z ∈ ball z₁ δ ∧
        z ∈ ball (0 : ℂ) 1 := by
      intro z hz
      refine hηsub ?_
      have := mem_ball.mp hz
      exact lt_of_lt_of_le this (min_le_left _ _)
    have hηL : η' * LΦ < 1 := by
      have h1 : η' ≤ δ := min_le_right _ _
      nlinarith [hLΦ0, hδL, hη'0]
    have hFGloc : ∀ z ∈ ball z₁ η', F z = odeJet f n z :=
      ode_solution_unique (Φ := fun _ : ℂ => fun w : Fin (n + 2) → ℂ => companionVec n N S w)
        (z₁ := z₁) (w₁ := w₁) (ρ' := ρ') (L := LΦ) (δ := η') hη'0 hηL hLΦ0 (le_of_lt hρ'0)
        (fun z _ w hw v hv => hLΦ w v (hregion w hw).1 (hregion v hv).1
          (hregion w hw).2 (hregion v hv).2)
        (fun z hz => hFderiv z (hη'ball z hz).2.1)
        (fun z hz => hasDerivAt_odeJet hf hODE (hη'ball z hz).2.2
          (hSnz _ (hη'ball z hz).1))
        (fun z hz => hFmem z (hη'ball z hz).2.1)
        (fun z hz => (hη'ball z hz).1) (hFval.trans hw₁def)
    have hEq : Set.EqOn F (odeJet f n) (ball z₁ δ ∩ ball (0 : ℂ) 1) := by
      refine hFan.eqOn_of_preconnected_of_eventuallyEq hJan hWconv.isPreconnected hz₁W ?_
      filter_upwards [isOpen_ball.mem_nhds (mem_ball_self hη'0)] with z hz
      exact hFGloc z hz
    intro z hz
    show F z ⟨1, by omega⟩ = f z
    rw [hEq hz]
    show odeJet f n z ⟨1, by omega⟩ = f z
    rw [odeJet_succ f n z ⟨1, by omega⟩ (by simp)]
    norm_num

/-! ## Differentiating the algebraic relation -/

/-- The successor jet index, clamped at the top. -/
def jetSucc (n : ℕ) (i : Fin (n + 2)) : Fin (n + 2) :=
  if h : (i : ℕ) + 1 < n + 2 then ⟨(i : ℕ) + 1, h⟩ else i

/-- The polynomial recording the derivative of the `i`-th jet coordinate, except at the top
index where the derivative is the new coordinate `f⁽ⁿ⁺¹⁾`. -/
private def jetShift (n : ℕ) (i : Fin (n + 2)) : MvPolynomial (Fin (n + 2)) ℂ :=
  if (i : ℕ) = 0 then 1 else if (i : ℕ) ≤ n then MvPolynomial.X (jetSucc n i) else 0

/-- The separant of a differential polynomial in the augmented jet coordinates. -/
def jetSeparant (n : ℕ) (P : MvPolynomial (Fin (n + 2)) ℂ) : MvPolynomial (Fin (n + 2)) ℂ :=
  MvPolynomial.pderiv (Fin.last (n + 1)) P

/-- The numerator produced by differentiating the algebraic relation once. -/
def jetNumerator (n : ℕ) (P : MvPolynomial (Fin (n + 2)) ℂ) : MvPolynomial (Fin (n + 2)) ℂ :=
  -∑ i : Fin (n + 2), MvPolynomial.pderiv i P * jetShift n i

/-- The derivative of the augmented jet. -/
def odeJetDeriv (f : ℂ → ℂ) (n : ℕ) (z : ℂ) : Fin (n + 2) → ℂ :=
  fun i => MvPolynomial.eval (odeJet f n z) (jetShift n i)
    + (if (i : ℕ) = n + 1 then iteratedDeriv (n + 1) f z else 0)

theorem hasDerivAt_odeJet_full {f : ℂ → ℂ} {U : Set ℂ} (hf : AnalyticOnNhd ℂ f U)
    {z : ℂ} (hz : z ∈ U) :
    HasDerivAt (odeJet f n) (odeJetDeriv f n z) z := by
  rw [hasDerivAt_pi]
  intro i
  by_cases h0 : (i : ℕ) = 0
  · have hfun : (fun w : ℂ => odeJet f n w i) = fun w : ℂ => w := by
      funext w
      simp [odeJet, h0]
    have hval : odeJetDeriv f n z i = 1 := by
      simp [odeJetDeriv, jetShift, h0]
    rw [hfun, hval]
    exact hasDerivAt_id z
  · by_cases h1 : (i : ℕ) ≤ n
    · have hfun : (fun w : ℂ => odeJet f n w i) = iteratedDeriv ((i : ℕ) - 1) f := by
        funext w
        simp [odeJet, h0]
      have hval : odeJetDeriv f n z i = iteratedDeriv ((i : ℕ) - 1 + 1) f z := by
        simp only [odeJetDeriv, jetShift, h0, if_false, if_pos h1]
        rw [if_neg (by omega), add_zero, MvPolynomial.eval_X, jetSucc,
          dif_pos (by omega : (i : ℕ) + 1 < n + 2)]
        rw [odeJet_succ f n z ⟨(i : ℕ) + 1, by omega⟩ (by simp)]
        congr 1
        show ((i : ℕ) + 1) - 1 = (i : ℕ) - 1 + 1
        omega
      rw [hfun, hval]
      exact hasDerivAt_iteratedDeriv hf _ hz
    · have hlast : (i : ℕ) = n + 1 := by omega
      have hfun : (fun w : ℂ => odeJet f n w i) = iteratedDeriv n f := by
        funext w
        rw [odeJet_succ f n w i h0, hlast]
        norm_num
      have hval : odeJetDeriv f n z i = iteratedDeriv (n + 1) f z := by
        simp only [odeJetDeriv, jetShift, h0, if_false, if_neg h1, if_pos hlast]
        simp
      rw [hfun, hval]
      exact hasDerivAt_iteratedDeriv hf n hz

/-- **Differentiating the algebraic relation.**  If `P` annihilates the jet on an open set then
`S · f⁽ⁿ⁺¹⁾ = N` there, with `S` the separant and `N` the explicit polynomial numerator. -/
theorem differentiated_relation {f : ℂ → ℂ} {U : Set ℂ} (hU : IsOpen U)
    (hf : AnalyticOnNhd ℂ f U) (P : MvPolynomial (Fin (n + 2)) ℂ)
    (hP : ∀ z ∈ U, MvPolynomial.eval (odeJet f n z) P = 0) {z : ℂ} (hz : z ∈ U) :
    MvPolynomial.eval (odeJet f n z) (jetSeparant n P) * iteratedDeriv (n + 1) f z
      = MvPolynomial.eval (odeJet f n z) (jetNumerator n P) := by
  classical
  have hjet := hasDerivAt_odeJet_full (n := n) hf hz
  have hchain := hasDerivAt_mvPolynomial_eval_comp P hjet
  have hzero : HasDerivAt (fun t => MvPolynomial.eval (odeJet f n t) P) 0 z := by
    have hev : (fun t => MvPolynomial.eval (odeJet f n t) P) =ᶠ[nhds z] fun _ => (0 : ℂ) := by
      filter_upwards [hU.mem_nhds hz] with t ht
      exact hP t ht
    exact (hasDerivAt_const z (0 : ℂ)).congr_of_eventuallyEq hev
  have hsum : (∑ i, MvPolynomial.eval (odeJet f n z) (MvPolynomial.pderiv i P)
      * odeJetDeriv f n z i) = 0 := by
    have := hchain.unique hzero
    exact this
  have hsplit : (∑ i, MvPolynomial.eval (odeJet f n z) (MvPolynomial.pderiv i P)
        * odeJetDeriv f n z i)
      = MvPolynomial.eval (odeJet f n z)
          (∑ i : Fin (n + 2), MvPolynomial.pderiv i P * jetShift n i)
        + MvPolynomial.eval (odeJet f n z) (jetSeparant n P) * iteratedDeriv (n + 1) f z := by
    have hterm : ∀ i : Fin (n + 2),
        MvPolynomial.eval (odeJet f n z) (MvPolynomial.pderiv i P) * odeJetDeriv f n z i
        = MvPolynomial.eval (odeJet f n z) (MvPolynomial.pderiv i P * jetShift n i)
          + (if (i : ℕ) = n + 1 then
              MvPolynomial.eval (odeJet f n z) (MvPolynomial.pderiv i P)
                * iteratedDeriv (n + 1) f z else 0) := by
      intro i
      rw [odeJetDeriv, map_mul]
      by_cases hi : (i : ℕ) = n + 1
      · rw [if_pos hi, if_pos hi]
        ring
      · rw [if_neg hi, if_neg hi]
        ring
    have hfin : (∑ x : Fin (n + 2), if (x : ℕ) = n + 1 then
          MvPolynomial.eval (odeJet f n z) (MvPolynomial.pderiv x P)
            * iteratedDeriv (n + 1) f z else 0)
        = MvPolynomial.eval (odeJet f n z) (jetSeparant n P) * iteratedDeriv (n + 1) f z := by
      rw [Finset.sum_eq_single (Fin.last (n + 1))]
      · rw [if_pos (by simp)]
        rfl
      · intro b _ hb
        rw [if_neg]
        intro hc
        exact hb (Fin.ext (by simpa using hc))
      · intro hc
        exact absurd (Finset.mem_univ _) hc
    rw [Finset.sum_congr rfl (fun i _ => hterm i), Finset.sum_add_distrib, ← map_sum, hfin]
  rw [hsplit] at hsum
  rw [jetNumerator, map_neg]
  linear_combination hsum

/-- **The bounded-jet natural-boundary bridge lemma, separant form.**  A holomorphic function on
the unit disk with a bounded augmented order-`n` jet, annihilated by an algebraic differential
polynomial `P` whose separant does not vanish identically along the jet, extends holomorphically
across the unit circle. -/
theorem exists_analytic_continuation_of_annihilator
    {f : ℂ → ℂ} {P : MvPolynomial (Fin (n + 2)) ℂ} {M : ℝ}
    (hf : AnalyticOnNhd ℂ f (ball (0 : ℂ) 1))
    (hjet : ∀ z ∈ ball (0 : ℂ) 1, ‖odeJet f n z‖ ≤ M)
    (hP : ∀ z ∈ ball (0 : ℂ) 1, MvPolynomial.eval (odeJet f n z) P = 0)
    (hS : ∃ z₀ ∈ ball (0 : ℂ) 1,
      MvPolynomial.eval (odeJet f n z₀) (jetSeparant n P) ≠ 0) :
    ∃ (z₁ : ℂ) (δ : ℝ), z₁ ∈ ball (0 : ℂ) 1 ∧ 0 < δ ∧ 1 - ‖z₁‖ < δ ∧
      ∃ g : ℂ → ℂ, DifferentiableOn ℂ g (ball z₁ δ) ∧
        ∀ z ∈ ball z₁ δ ∩ ball (0 : ℂ) 1, g z = f z :=
  exists_analytic_continuation_of_bounded_jet hf hjet
    (fun z hz => differentiated_relation isOpen_ball hf P hP hz) hS

end

end GaloisForLFunctions.HTGeometry
