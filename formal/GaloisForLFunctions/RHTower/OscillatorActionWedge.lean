import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# The oscillator action cannot be bootstrapped

The even Hermite eigenstate of level `2d` and frequency `T` has momentum moments
`E ξ² = T(2d + 1/2)` and `E ξ⁴ = (3T²/4)(8d² + 4d + 1)`, whose ratio is bounded below by a
universal constant, so Paley--Zygmund puts a universal fraction of its mass beyond half its mean
momentum energy.  Every state of the degree-`N`, time-`t` cone has momentum energy at most
`t(4N + 1)`, so Markov puts only `2t(4N+1)/(T(2d+1/2))` of its mass there.

Once the wedge budget forces `t(N+1) ≤ cT(d+1)` with a small universal `c`, the two mass estimates
are incompatible by a fixed margin, and the two states are a fixed distance apart in `L²`.  The
product `t·deg` is therefore an invariant oscillator action: a purely analytic semigroup argument
cannot transport a fixed-time probe into an arbitrarily small-time wedge.
-/

namespace RHTower

noncomputable section

/-! ## The universal Paley--Zygmund ratio -/

/-- **(24.186)** The ratio of the two momentum moments of the even Hermite eigenstate is bounded
below by `1/3`, uniformly in the level and the frequency. -/
theorem hermiteMomentumRatio_ge {T d : ℝ} (hT : 0 < T) (hd : 0 ≤ d) :
    (1 : ℝ) / 3 ≤ (T * (2 * d + 1 / 2)) ^ (2 : ℕ) / (3 * T ^ (2 : ℕ) / 4 * (8 * d ^ (2 : ℕ) + 4 * d + 1)) := by
  have hden : 0 < 3 * T ^ (2 : ℕ) / 4 * (8 * d ^ (2 : ℕ) + 4 * d + 1) := by positivity
  rw [le_div_iff₀ hden]
  nlinarith [sq_nonneg T, sq_nonneg d, hT, hd, mul_nonneg hd hd]

/-- The Paley--Zygmund mass at level one half, in the form used here. -/
theorem paleyZygmund_half_mass {A B : ℝ} (hA : 0 < A) (hB : 0 < B) (hratio : 1 / 3 ≤ A ^ (2 : ℕ) / B) :
    (1 : ℝ) / 12 ≤ A ^ (2 : ℕ) / (4 * B) := by
  have h : A ^ (2 : ℕ) / (4 * B) = A ^ (2 : ℕ) / B / 4 := by
    field_simp
  rw [h]
  linarith

/-! ## The Markov side of the cone -/

/-- Markov's inequality in the form used: a state whose momentum energy is at most `C` has at most
`2C/A` of its mass beyond `A/2`. -/
theorem markov_mass_le {A C m : ℝ} (hA : 0 < A) (hbound : A / 2 * m ≤ C) : m ≤ 2 * C / A := by
  rw [le_div_iff₀ hA]
  linarith

/-! ## The separation -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- **(24.188) The separation.**  A projection capturing at least `√p` of one vector and at most
`√p/2` of another separates the two by `√p/2`. -/
theorem separation_of_projection (P : E →L[ℝ] E) (hP : ‖P‖ ≤ 1) (f g : E) {p : ℝ}
    (hg : Real.sqrt p ≤ ‖P g‖) (hf : ‖P f‖ ≤ Real.sqrt p / 2) :
    Real.sqrt p / 2 ≤ ‖f - g‖ := by
  have hstep : ‖P g‖ - ‖P f‖ ≤ ‖P g - P f‖ := norm_sub_norm_le _ _
  have hproj : ‖P g - P f‖ = ‖P (g - f)‖ := by
    rw [map_sub]
  have hcontract : ‖P (g - f)‖ ≤ ‖g - f‖ := by
    have hle := P.le_opNorm (g - f)
    have hbound : ‖P‖ * ‖g - f‖ ≤ 1 * ‖g - f‖ :=
      mul_le_mul_of_nonneg_right hP (norm_nonneg _)
    rw [one_mul] at hbound
    linarith
  have hrev : ‖g - f‖ = ‖f - g‖ := norm_sub_rev _ _
  rw [hproj] at hstep
  rw [hrev] at hcontract
  linarith

/-! ## The wedge budget -/

/-- The cone momentum bound compares to the probe momentum with an absolute factor. -/
theorem coneMomentum_le {t T N d c : ℝ} (ht : 0 ≤ t) (hT : 0 < T) (_hN : 0 ≤ N) (hd : 0 ≤ d)
    (hc : 0 ≤ c) (hwedge : t * (N + 1) ≤ c * (T * (d + 1))) :
    t * (4 * N + 1) ≤ 8 * c * (T * (2 * d + 1 / 2)) := by
  have hfour : t * (4 * N + 1) ≤ 4 * (t * (N + 1)) := by nlinarith
  have hprobe : T * (d + 1) ≤ 2 * (T * (2 * d + 1 / 2)) := by nlinarith
  nlinarith [hwedge, hfour, hprobe, hc, hT, hd]

/-- **(24.188) The action bound.**  With the universal constant `c = 1/768` the transported cone
mass beyond half the probe momentum energy is at most a quarter of the probe mass there. -/
theorem transportedMass_le {A C : ℝ} (hA : 0 < A) (hC : C ≤ 8 * (1 / 768) * A) :
    2 * C / A ≤ 1 / 48 := by
  rw [div_le_iff₀ hA]
  linarith

/-- The quarter-mass comparison in the form the separation lemma consumes. -/
theorem sqrt_mass_le {m : ℝ} (hle : m ≤ 1 / 48) :
    Real.sqrt m ≤ Real.sqrt (1 / 12) / 2 := by
  have hquarter : (1 : ℝ) / 48 = (1 / 12) / 4 := by norm_num
  have hstep : Real.sqrt m ≤ Real.sqrt ((1 / 12) / 4) := by
    rw [← hquarter]
    exact Real.sqrt_le_sqrt hle
  have hval : Real.sqrt ((1 / 12 : ℝ) / 4) = Real.sqrt (1 / 12) / 2 := by
    rw [Real.sqrt_div' _ (by norm_num : (0:ℝ) ≤ 4)]
    rw [show Real.sqrt (4 : ℝ) = 2 by
      rw [show (4 : ℝ) = 2 ^ (2 : ℕ) by norm_num, Real.sqrt_sq (by norm_num)]]
  rwa [hval] at hstep

end

end RHTower
