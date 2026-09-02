import GaloisForLFunctions.RHTower.SuzukiCausalDepthGammaGraphInverseTraceCollapseNoGo

/-!
# Finite-section naked Gamma graph traces contain no inverse amplification

The infinite graph-metric trace already cancels the unbounded Moore--Penrose inverse. This module
closes the ordinary finite-section escape that drops the metric factor and traces the naked graph
symmetrizer instead. On every finite complex packet, support-inverse cyclicity gives

`Tr((PDP + G D† K) / 2) = Re Tr(DP)`.

The metric `K` and generalized inverse `G` disappear completely. The identity is rank-free and
applies separately to a family with changing dimension and cutoff. Consequently, a sublinear
supported-clock trace cannot be amplified into the linear correction forced by the Suzuki
transition core. Any remaining naked-trace mechanism must already place linear mass in the clock
before inversion, or abandon ordinary cyclic finite-matrix trace through a genuinely noncyclic
renormalization or cutoff anomaly.

No RH premise, Xi-zero location, numerical computation, fixed-rank hypothesis, limiting
interchange, or extra logical assumption occurs.
-/

open Matrix Complex Filter
open scoped Topology
open GaloisForLFunctions.RHTower

namespace RHTower

noncomputable section

/-- Finite-section version of the naked graph semimetric symmetrizer. -/
def finiteSectionNakedGraphSymmetrization
    {n : Type*} [Fintype n]
    (K G P D : Matrix n n ℂ) : Matrix n n ℂ :=
  (1 / 2 : ℂ) • (P * D * P + G * Dᴴ * K)

/-- **Finite-section inverse blindness.** Ordinary cyclic trace of the naked graph symmetrizer is
exactly real supported-clock trace. Neither metric nor generalized inverse survives. Only the
one-sided support-inverse equation, orthogonal-projection idempotence, and self-adjointness are
needed. -/
theorem trace_finiteSectionNakedGraphSymmetrization_eq_re_supportedClock
    {n : Type*} [Fintype n]
    (K G P D : Matrix n n ℂ)
    (hKG : K * G = P) (hP2 : P * P = P) (hPstar : Pᴴ = P) :
    (finiteSectionNakedGraphSymmetrization K G P D).trace =
      ((D * P).trace.re : ℂ) := by
  have hfirst : (P * D * P).trace = (D * P).trace := by
    calc
      (P * D * P).trace = (P * P * D).trace :=
        Matrix.trace_mul_cycle P D P
      _ = (P * D).trace := by rw [hP2]
      _ = (D * P).trace := Matrix.trace_mul_comm P D
  have hinverse : (G * Dᴴ * K).trace = star (D * P).trace := by
    calc
      (G * Dᴴ * K).trace = (K * G * Dᴴ).trace :=
        Matrix.trace_mul_cycle G Dᴴ K
      _ = (P * Dᴴ).trace := by rw [hKG]
      _ = ((D * P)ᴴ).trace := by rw [Matrix.conjTranspose_mul, hPstar]
      _ = star (D * P).trace := Matrix.trace_conjTranspose (D * P)
  rw [finiteSectionNakedGraphSymmetrization, Matrix.trace_smul,
    Matrix.trace_add, hfirst, hinverse]
  change (1 / 2 : ℂ) *
      ((D * P).trace + (starRingEnd ℂ) (D * P).trace) =
    ((D * P).trace.re : ℂ)
  rw [Complex.add_conj]
  push_cast
  have hhalf : (1 / 2 : ℂ) * 2 = 1 := by norm_num
  calc
    (1 / 2 : ℂ) * (2 * ((D * P).trace.re : ℂ)) =
        ((1 / 2 : ℂ) * 2) * ((D * P).trace.re : ℂ) := by ring
    _ = ((D * P).trace.re : ℂ) := by rw [hhalf, one_mul]

/-- Naked graph-trace correction supplied by a varying-rank family of finite sections. -/
def suzukiFiniteSectionNakedGraphTraceCorrection
    (rank : ℕ → ℕ)
    (K G P D : (N : ℕ) → Matrix (Fin (rank N)) (Fin (rank N)) ℂ)
    (N : ℕ) : ℝ :=
  (finiteSectionNakedGraphSymmetrization (K N) (G N) (P N) (D N)).trace.re

/-- Every finite-section naked correction is the supported-clock trace before inversion. -/
theorem suzukiFiniteSectionNakedGraphTraceCorrection_eq_re_supportedClock
    (rank : ℕ → ℕ)
    (K G P D : (N : ℕ) → Matrix (Fin (rank N)) (Fin (rank N)) ℂ)
    (hKG : ∀ N, K N * G N = P N)
    (hP2 : ∀ N, P N * P N = P N)
    (hPstar : ∀ N, (P N)ᴴ = P N)
    (N : ℕ) :
    suzukiFiniteSectionNakedGraphTraceCorrection rank K G P D N =
      ((D N * P N).trace).re := by
  rw [suzukiFiniteSectionNakedGraphTraceCorrection,
    trace_finiteSectionNakedGraphSymmetrization_eq_re_supportedClock
      (K N) (G N) (P N) (D N) (hKG N) (hP2 N) (hPstar N)]
  rfl

/-- **Sharp positive survivor.** If a finite-section naked graph trace semibounds the rectangular
Ward defect, its supported clock already carries the forced linear mass before generalized
inversion. -/
theorem eventually_linear_le_suzukiFiniteSectionSupportedClockTrace_of_Ward_bddBelow
    (rank : ℕ → ℕ)
    (K G P D : (N : ℕ) → Matrix (Fin (rank N)) (Fin (rank N)) ℂ)
    (hKG : ∀ N, K N * G N = P N)
    (hP2 : ∀ N, P N * P N = P N)
    (hPstar : ∀ N, (P N)ᴴ = P N)
    (L lower : ℝ)
    (hlower : ∀ᶠ n : ℕ in atTop,
      lower ≤ suzukiRectangularWardDefect L
        (fun N => suzukiNaturalApertureTransitionCoreCauchyEnergy N -
          suzukiFiniteSectionNakedGraphTraceCorrection rank K G P D N)
        (8 * n)) :
    ∀ᶠ n : ℕ in atTop,
      (n : ℝ) / 576 ≤ ((D (8 * n) * P (8 * n)).trace).re := by
  have hlinear :=
    eventually_linear_le_correction_of_transitionCoreWardDefect_bddBelow
      L (suzukiFiniteSectionNakedGraphTraceCorrection rank K G P D) lower hlower
  filter_upwards [hlinear] with n hn
  rw [suzukiFiniteSectionNakedGraphTraceCorrection_eq_re_supportedClock
    rank K G P D hKG hP2 hPstar] at hn
  exact hn

/-- **Closed CCM--FU producer-class kill.** No varying-rank ordinary finite-matrix
Moore--Penrose/support-inverse trace can amplify a sublinear supported clock into a semibounding
Suzuki correction. The theorem quantifies over every rank schedule, metric, inverse, support,
clock, width, and proposed floor. -/
theorem no_suzukiCausalDepthGammaFiniteSectionNakedGraphInverseOnlyWardProducer :
    ¬ ∃ (rank : ℕ → ℕ)
      (K G P D : (N : ℕ) → Matrix (Fin (rank N)) (Fin (rank N)) ℂ)
      (L lower : ℝ),
      (∀ N, K N * G N = P N) ∧
      (∀ N, P N * P N = P N) ∧
      (∀ N, (P N)ᴴ = P N) ∧
      SuzukiTransitionCoreCorrectionSublinear
        (fun N => ((D N * P N).trace).re) ∧
      ∀ᶠ n : ℕ in atTop,
        lower ≤ suzukiRectangularWardDefect L
          (fun N => suzukiNaturalApertureTransitionCoreCauchyEnergy N -
            suzukiFiniteSectionNakedGraphTraceCorrection rank K G P D N)
          (8 * n) := by
  rintro ⟨rank, K, G, P, D, L, lower, hKG, hP2, hPstar,
    hsublinear, hlower⟩
  apply no_sublinear_transitionCore_rectangularWardProducer
  refine ⟨L, suzukiFiniteSectionNakedGraphTraceCorrection rank K G P D, lower, ?_, hlower⟩
  have hfun : suzukiFiniteSectionNakedGraphTraceCorrection rank K G P D =
      fun N => ((D N * P N).trace).re := by
    funext N
    exact suzukiFiniteSectionNakedGraphTraceCorrection_eq_re_supportedClock
      rank K G P D hKG hP2 hPstar N
  rw [hfun]
  exact hsublinear

end

end RHTower
