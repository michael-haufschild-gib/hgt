import GaloisForLFunctions.RHTower.PeriodicLSeriesRightAsymptotics
import GaloisForLFunctions.RHTower.ZetaTwistCuspRadius

/-!
# The cusp radius law in degree one and arbitrary conductor

The functional equation of a periodic Dirichlet series relates its values far to
the left to the values of the Fourier-transformed series far to the right.  The
transformed series is dominated by its first non-vanishing term `n₀`, so the
whole left-hand side grows geometrically at rate `N/(2π n₀)`: the conductor `N`
from the functional equation, `2π` from the archimedean factor, and `n₀` from the
dual series.

The two quarter-turn exponentials cannot conspire to cancel the leading terms,
because the four values they take over a period of four vanish simultaneously
only if both dual coefficients at `n₀` vanish — which contradicts the minimality
of `n₀`.  So the growth functional of the factorially normalized shifted values is
exactly `N/(2π n₀)`.
-/

open Complex Filter Topology
open GaloisForLFunctions.HTGeometry
open scoped ENNReal NNReal

namespace RHTower

section DualIndex

variable {N : ℕ} [NeZero N]

/-- The Fourier transform of a non-zero function is non-zero. -/
theorem dft_ne_zero {Φ : ZMod N → ℂ} (hΦ : Φ ≠ 0) : ZMod.dft Φ ≠ 0 := by
  intro h
  refine hΦ (funext fun x => ?_)
  have h2 := ZMod.dft_dft Φ
  rw [h, map_zero] at h2
  have h3 := congrFun h2 (-x)
  simp only [Pi.zero_apply, neg_neg, smul_eq_mul] at h3
  have hN : (N : ℂ) ≠ 0 := NeZero.ne _
  have := (mul_eq_zero.mp h3.symm).resolve_left hN
  simpa using this

/-- The support of the dual series, as a set of positive integers. -/
def dualSupport (Φ : ZMod N → ℂ) : Set ℕ :=
  {n : ℕ | 0 < n ∧ (ZMod.dft Φ ((n : ℕ) : ZMod N) ≠ 0
    ∨ ZMod.dft Φ (-((n : ℕ) : ZMod N)) ≠ 0)}

theorem dualSupport_nonempty {Φ : ZMod N → ℂ} (hΦ : Φ ≠ 0) :
    (dualSupport Φ).Nonempty := by
  obtain ⟨j, hj⟩ : ∃ j : ZMod N, ZMod.dft Φ j ≠ 0 := by
    by_contra hc
    rw [not_exists] at hc
    exact dft_ne_zero hΦ (funext fun j => not_not.mp (hc j))
  by_cases hv : j.val = 0
  · refine ⟨N, NeZero.pos N, Or.inl ?_⟩
    have hjz : j = 0 := by
      have := ZMod.natCast_rightInverse (n := N) j
      rw [hv] at this
      simpa using this.symm
    rw [ZMod.natCast_self, ← hjz]
    exact hj
  · refine ⟨j.val, Nat.pos_of_ne_zero hv, Or.inl ?_⟩
    rw [ZMod.natCast_rightInverse (n := N) j]
    exact hj

/-- The first exponent of the dual series. -/
noncomputable def dualIndex (Φ : ZMod N → ℂ) : ℕ := sInf (dualSupport Φ)

theorem dualIndex_mem {Φ : ZMod N → ℂ} (hΦ : Φ ≠ 0) : dualIndex Φ ∈ dualSupport Φ :=
  Nat.sInf_mem (dualSupport_nonempty hΦ)

theorem dualIndex_pos {Φ : ZMod N → ℂ} (hΦ : Φ ≠ 0) : 0 < dualIndex Φ :=
  (dualIndex_mem hΦ).1

theorem dualIndex_spec {Φ : ZMod N → ℂ} (hΦ : Φ ≠ 0) :
    ZMod.dft Φ ((dualIndex Φ : ℕ) : ZMod N) ≠ 0
      ∨ ZMod.dft Φ (-((dualIndex Φ : ℕ) : ZMod N)) ≠ 0 :=
  (dualIndex_mem hΦ).2

theorem dualIndex_min {Φ : ZMod N → ℂ} {n : ℕ} (hn : 0 < n) (hlt : n < dualIndex Φ) :
    ZMod.dft Φ ((n : ℕ) : ZMod N) = 0 ∧ ZMod.dft Φ (-((n : ℕ) : ZMod N)) = 0 := by
  have hnot : n ∉ dualSupport Φ := fun hc => absurd (Nat.sInf_le hc) (not_le.mpr hlt)
  rw [dualSupport, Set.mem_setOf_eq, not_and_or] at hnot
  rcases hnot with h | h
  · exact absurd hn h
  · rw [not_or, not_not, not_not] at h
    exact h

end DualIndex

section DualSeries

variable {N : ℕ} [NeZero N]

/-- The Fourier-transformed coefficient function reflected through the origin. -/
theorem dft_comp_neg_apply (Φ : ZMod N → ℂ) (j : ZMod N) :
    ZMod.dft (fun x => Φ (-x)) j = ZMod.dft Φ (-j) := by
  rw [ZMod.dft_comp_neg]

/-- **The two dual series both grow at the rate of the dual index.** -/
theorem tendsto_dualP {Φ : ZMod N → ℂ} (hΦ : Φ ≠ 0) (w₀ : ℂ) :
    Tendsto (fun k : ℕ => ((dualIndex Φ : ℕ) : ℂ) ^ (w₀ + (k : ℂ))
        * ZMod.LFunction (ZMod.dft Φ) (w₀ + (k : ℂ))) atTop
      (𝓝 (ZMod.dft Φ ((dualIndex Φ : ℕ) : ZMod N))) := by
  refine tendsto_normalizedLFunction _ (dualIndex_pos hΦ) ?_ w₀
  intro n hn hlt
  exact (dualIndex_min hn hlt).1

theorem tendsto_dualQ {Φ : ZMod N → ℂ} (hΦ : Φ ≠ 0) (w₀ : ℂ) :
    Tendsto (fun k : ℕ => ((dualIndex Φ : ℕ) : ℂ) ^ (w₀ + (k : ℂ))
        * ZMod.LFunction (ZMod.dft fun x => Φ (-x)) (w₀ + (k : ℂ))) atTop
      (𝓝 (ZMod.dft Φ (-((dualIndex Φ : ℕ) : ZMod N)))) := by
  have h := tendsto_normalizedLFunction (ZMod.dft fun x => Φ (-x)) (dualIndex_pos hΦ)
    (fun n hn hlt => by
      rw [dft_comp_neg_apply]
      exact (dualIndex_min hn hlt).2) w₀
  rwa [dft_comp_neg_apply] at h

end DualSeries

section Decomposition

variable {N : ℕ} [NeZero N] {s₀ : ℂ}

/-- The normalized first dual series. -/
noncomputable def dualP (Φ : ZMod N → ℂ) (s₀ : ℂ) (k : ℕ) : ℂ :=
  ((dualIndex Φ : ℕ) : ℂ) ^ (1 - s₀ + (k : ℂ))
    * ZMod.LFunction (ZMod.dft Φ) (1 - s₀ + (k : ℂ))

/-- The normalized reflected dual series. -/
noncomputable def dualQ (Φ : ZMod N → ℂ) (s₀ : ℂ) (k : ℕ) : ℂ :=
  ((dualIndex Φ : ℕ) : ℂ) ^ (1 - s₀ + (k : ℂ))
    * ZMod.LFunction (ZMod.dft fun x => Φ (-x)) (1 - s₀ + (k : ℂ))

theorem tendsto_dualP' {Φ : ZMod N → ℂ} (hΦ : Φ ≠ 0) (s₀ : ℂ) :
    Tendsto (fun k : ℕ => dualP Φ s₀ k) atTop
      (𝓝 (ZMod.dft Φ ((dualIndex Φ : ℕ) : ZMod N))) :=
  tendsto_dualP hΦ (1 - s₀)

theorem tendsto_dualQ' {Φ : ZMod N → ℂ} (hΦ : Φ ≠ 0) (s₀ : ℂ) :
    Tendsto (fun k : ℕ => dualQ Φ s₀ k) atTop
      (𝓝 (ZMod.dft Φ (-((dualIndex Φ : ℕ) : ZMod N)))) :=
  tendsto_dualQ hΦ (1 - s₀)

/-- The bracket of the functional equation, with the geometric factor of the dual
index extracted. -/
noncomputable def dualSum (Φ : ZMod N → ℂ) (s₀ : ℂ) (k : ℕ) : ℂ :=
  Complex.exp ((Real.pi : ℂ) * Complex.I * (1 - s₀ + (k : ℂ)) / 2) * dualP Φ s₀ k
    + Complex.exp (-(Real.pi : ℂ) * Complex.I * (1 - s₀ + (k : ℂ)) / 2) * dualQ Φ s₀ k

/-- The remainder of the functional-equation decomposition. -/
noncomputable def zmodRemainder (Φ : ZMod N → ℂ) (s₀ : ℂ) (k : ℕ) : ℂ :=
  ((N : ℂ) ^ (-s₀) * (2 * (Real.pi : ℂ)) ^ (-(1 - s₀))
      * ((dualIndex Φ : ℕ) : ℂ) ^ (-(1 - s₀)))
    * (Complex.Gamma (1 - s₀ + (k : ℂ)) / Complex.Gamma (1 + (k : ℂ)))
    * dualSum Φ s₀ k

theorem natCast_ne_zero_of_pos {n : ℕ} (hn : 0 < n) : ((n : ℕ) : ℂ) ≠ 0 := by
  exact_mod_cast hn.ne'

/-- **Functional-equation decomposition of the shifted periodic L-function.** -/
theorem zmod_shift_decomposition {Φ : ZMod N → ℂ} (hΦ : Φ ≠ 0)
    (hs : ∀ m : ℕ, s₀ ≠ (m : ℂ)) (k : ℕ) :
    ZMod.LFunction Φ (s₀ - (k : ℂ)) / (Nat.factorial k : ℂ)
      = ((N : ℂ) * (2 * (Real.pi : ℂ))⁻¹ * (((dualIndex Φ : ℕ) : ℂ))⁻¹) ^ k
        * zmodRemainder Φ s₀ k := by
  have hn₀ : ((dualIndex Φ : ℕ) : ℂ) ≠ 0 := natCast_ne_zero_of_pos (dualIndex_pos hΦ)
  have hNC : (N : ℂ) ≠ 0 := NeZero.ne _
  have hfe := ZMod.LFunction_one_sub Φ (s := 1 - s₀ + (k : ℂ))
    (shift_ne_negNat hs k) (Or.inr (shift_ne_one hs k))
  have harg : 1 - (1 - s₀ + (k : ℂ)) = s₀ - (k : ℂ) := by ring
  rw [harg] at hfe
  have hfact : Complex.Gamma (1 + (k : ℂ)) = (Nat.factorial k : ℂ) := by
    rw [add_comm]
    exact Complex.Gamma_nat_eq_factorial k
  have hfactne : Complex.Gamma (1 + (k : ℂ)) ≠ 0 := by
    rw [hfact]
    exact_mod_cast Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero k)
  have hNpow : (N : ℂ) ^ ((1 - s₀ + (k : ℂ)) - 1) = (N : ℂ) ^ k * (N : ℂ) ^ (-s₀) := by
    rw [show ((1 - s₀ + (k : ℂ)) - 1) = (k : ℂ) + -s₀ from by ring,
      Complex.cpow_add _ _ hNC, Complex.cpow_natCast]
  have hn₀pow : ((dualIndex Φ : ℕ) : ℂ) ^ (1 - s₀ + (k : ℂ))
      = ((dualIndex Φ : ℕ) : ℂ) ^ k * ((dualIndex Φ : ℕ) : ℂ) ^ (1 - s₀) := by
    rw [show (1 - s₀ + (k : ℂ)) = (k : ℂ) + (1 - s₀) from by ring,
      Complex.cpow_add _ _ hn₀, Complex.cpow_natCast]
  have hn₀cancel : ((dualIndex Φ : ℕ) : ℂ) ^ (-(1 - s₀))
      * ((dualIndex Φ : ℕ) : ℂ) ^ (1 - s₀) = 1 := by
    rw [← Complex.cpow_add _ _ hn₀, neg_add_cancel, Complex.cpow_zero]
  have hn₀powne : ((dualIndex Φ : ℕ) : ℂ) ^ k ≠ 0 := pow_ne_zero _ hn₀
  have hn₀cne : ((dualIndex Φ : ℕ) : ℂ) ^ (1 - s₀) ≠ 0 :=
    Complex.cpow_ne_zero_iff.mpr (Or.inl hn₀)
  have hn₀nne : ((dualIndex Φ : ℕ) : ℂ) ^ (-(1 - s₀)) ≠ 0 :=
    Complex.cpow_ne_zero_iff.mpr (Or.inl hn₀)
  have hdual : ZMod.LFunction (ZMod.dft Φ) (1 - s₀ + (k : ℂ))
      = (((dualIndex Φ : ℕ) : ℂ) ^ k)⁻¹ * (((dualIndex Φ : ℕ) : ℂ) ^ (1 - s₀))⁻¹
        * dualP Φ s₀ k := by
    rw [dualP, hn₀pow]
    field_simp
  have hdual' : ZMod.LFunction (ZMod.dft fun x => Φ (-x)) (1 - s₀ + (k : ℂ))
      = (((dualIndex Φ : ℕ) : ℂ) ^ k)⁻¹ * (((dualIndex Φ : ℕ) : ℂ) ^ (1 - s₀))⁻¹
        * dualQ Φ s₀ k := by
    rw [dualQ, hn₀pow]
    field_simp
  have htwopi : (2 * (Real.pi : ℂ)) ≠ 0 := two_pi_ne_zero
  rw [hfe, hNpow, two_pi_cpow_shift, hdual, hdual', ← hfact, zmodRemainder, dualSum]
  simp only [Complex.cpow_neg]
  ring

end Decomposition

section RootGrowth

variable {N : ℕ} [NeZero N] {s₀ : ℂ}

theorem exp_neg_quarter_turn :
    Complex.exp (-(Real.pi : ℂ) * Complex.I / 2) = -Complex.I := by
  rw [show (-(Real.pi : ℂ) * Complex.I / 2) = -((Real.pi : ℂ) * Complex.I / 2) from by ring,
    Complex.exp_neg, exp_quarter_turn, Complex.inv_I]

theorem exp_shift_pos (s₀ : ℂ) (k : ℕ) :
    Complex.exp ((Real.pi : ℂ) * Complex.I * (1 - s₀ + (k : ℂ)) / 2)
      = Complex.exp ((Real.pi : ℂ) * Complex.I * (1 - s₀) / 2) * Complex.I ^ k := by
  have hk : Complex.I ^ k = Complex.exp ((k : ℂ) * ((Real.pi : ℂ) * Complex.I / 2)) := by
    rw [Complex.exp_nat_mul, exp_quarter_turn]
  rw [hk, ← Complex.exp_add]
  congr 1
  ring

theorem exp_shift_neg (s₀ : ℂ) (k : ℕ) :
    Complex.exp (-(Real.pi : ℂ) * Complex.I * (1 - s₀ + (k : ℂ)) / 2)
      = Complex.exp (-(Real.pi : ℂ) * Complex.I * (1 - s₀) / 2) * (-Complex.I) ^ k := by
  have hk : (-Complex.I) ^ k
      = Complex.exp ((k : ℂ) * (-(Real.pi : ℂ) * Complex.I / 2)) := by
    rw [Complex.exp_nat_mul, exp_neg_quarter_turn]
  rw [hk, ← Complex.exp_add]
  congr 1
  ring

theorem exists_bound_of_tendsto {f : ℕ → ℂ} {L : ℂ} (h : Tendsto f atTop (𝓝 L)) :
    ∃ C : ℝ, 0 < C ∧ ∀ k, ‖f k‖ ≤ C := by
  obtain ⟨C, hC⟩ := h.norm.bddAbove_range
  exact ⟨max C 1, lt_of_lt_of_le one_pos (le_max_right _ _),
    fun k => le_trans (hC ⟨k, rfl⟩) (le_max_left _ _)⟩

/-- The period-four limit shape of the bracket. -/
noncomputable def dualWave (Φ : ZMod N → ℂ) (s₀ : ℂ) (k : ℕ) : ℂ :=
  Complex.exp ((Real.pi : ℂ) * Complex.I * (1 - s₀) / 2) * Complex.I ^ k
      * ZMod.dft Φ ((dualIndex Φ : ℕ) : ZMod N)
    + Complex.exp (-(Real.pi : ℂ) * Complex.I * (1 - s₀) / 2) * (-Complex.I) ^ k
      * ZMod.dft Φ (-((dualIndex Φ : ℕ) : ZMod N))

theorem dualWave_periodic (Φ : ZMod N → ℂ) (s₀ : ℂ) (k : ℕ) :
    dualWave Φ s₀ (k + 4) = dualWave Φ s₀ k := by
  have h1 : (Complex.I) ^ (k + 4) = Complex.I ^ k := by
    rw [pow_add]
    norm_num [Complex.I_pow_four]
  have h2 : (-Complex.I) ^ (k + 4) = (-Complex.I) ^ k := by
    rw [pow_add, show (-Complex.I) ^ 4 = (Complex.I) ^ 4 from by ring,
      Complex.I_pow_four, mul_one]
  rw [dualWave, dualWave, h1, h2]

theorem exists_norm_dualWave_pos {Φ : ZMod N → ℂ} (hΦ : Φ ≠ 0) (s₀ : ℂ) :
    0 < ‖dualWave Φ s₀ 0‖ ∨ 0 < ‖dualWave Φ s₀ 1‖ := by
  by_contra hcon
  rw [not_or, not_lt, not_lt] at hcon
  obtain ⟨h0, h1⟩ := hcon
  have hz0 : dualWave Φ s₀ 0 = 0 := norm_le_zero_iff.mp h0
  have hz1 : dualWave Φ s₀ 1 = 0 := norm_le_zero_iff.mp h1
  set e := Complex.exp ((Real.pi : ℂ) * Complex.I * (1 - s₀) / 2) with he
  set e' := Complex.exp (-(Real.pi : ℂ) * Complex.I * (1 - s₀) / 2) with he'
  set X := ZMod.dft Φ ((dualIndex Φ : ℕ) : ZMod N) with hX
  set Y := ZMod.dft Φ (-((dualIndex Φ : ℕ) : ZMod N)) with hY
  rw [dualWave, pow_zero, pow_zero, mul_one, mul_one] at hz0
  rw [dualWave, pow_one, pow_one] at hz1
  have hI : Complex.I ≠ 0 := Complex.I_ne_zero
  have hsum : e * X + e' * Y = 0 := hz0
  have hdiff : e * X - e' * Y = 0 := by
    have hstep : (e * Complex.I) * X + (e' * -Complex.I) * Y = 0 := hz1
    have : Complex.I * (e * X - e' * Y) = 0 := by linear_combination hstep
    exact (mul_eq_zero.mp this).resolve_left hI
  have hX0 : e * X = 0 := by linear_combination (hsum + hdiff) / 2
  have hY0 : e' * Y = 0 := by linear_combination (hsum - hdiff) / 2
  have hXz : X = 0 := (mul_eq_zero.mp hX0).resolve_left (Complex.exp_ne_zero _)
  have hYz : Y = 0 := (mul_eq_zero.mp hY0).resolve_left (Complex.exp_ne_zero _)
  rcases dualIndex_spec hΦ with h | h
  · exact h hXz
  · exact h hYz

theorem tendsto_dualSum_sub_dualWave {Φ : ZMod N → ℂ} (hΦ : Φ ≠ 0) (s₀ : ℂ) :
    Tendsto (fun k : ℕ => dualSum Φ s₀ k - dualWave Φ s₀ k) atTop (𝓝 0) := by
  have hP := tendsto_dualP' hΦ s₀
  have hQ := tendsto_dualQ' hΦ s₀
  have hPz : Tendsto (fun k : ℕ =>
      dualP Φ s₀ k - ZMod.dft Φ ((dualIndex Φ : ℕ) : ZMod N)) atTop (𝓝 0) := by
    have := hP.sub (tendsto_const_nhds
      (x := ZMod.dft Φ ((dualIndex Φ : ℕ) : ZMod N)) (f := atTop (α := ℕ)))
    simpa using this
  have hQz : Tendsto (fun k : ℕ =>
      dualQ Φ s₀ k - ZMod.dft Φ (-((dualIndex Φ : ℕ) : ZMod N))) atTop (𝓝 0) := by
    have := hQ.sub (tendsto_const_nhds
      (x := ZMod.dft Φ (-((dualIndex Φ : ℕ) : ZMod N))) (f := atTop (α := ℕ)))
    simpa using this
  rw [tendsto_zero_iff_norm_tendsto_zero] at hPz hQz ⊢
  have hbound : ∀ k : ℕ, ‖dualSum Φ s₀ k - dualWave Φ s₀ k‖
      ≤ ‖Complex.exp ((Real.pi : ℂ) * Complex.I * (1 - s₀) / 2)‖
          * ‖dualP Φ s₀ k - ZMod.dft Φ ((dualIndex Φ : ℕ) : ZMod N)‖
        + ‖Complex.exp (-(Real.pi : ℂ) * Complex.I * (1 - s₀) / 2)‖
          * ‖dualQ Φ s₀ k - ZMod.dft Φ (-((dualIndex Φ : ℕ) : ZMod N))‖ := by
    intro k
    have hrw : dualSum Φ s₀ k - dualWave Φ s₀ k
        = Complex.exp ((Real.pi : ℂ) * Complex.I * (1 - s₀) / 2) * Complex.I ^ k
            * (dualP Φ s₀ k - ZMod.dft Φ ((dualIndex Φ : ℕ) : ZMod N))
          + Complex.exp (-(Real.pi : ℂ) * Complex.I * (1 - s₀) / 2) * (-Complex.I) ^ k
            * (dualQ Φ s₀ k - ZMod.dft Φ (-((dualIndex Φ : ℕ) : ZMod N))) := by
      rw [dualSum, dualWave, exp_shift_pos, exp_shift_neg]
      ring
    rw [hrw]
    refine le_trans (norm_add_le _ _) ?_
    rw [norm_mul, norm_mul, norm_pow, norm_mul, norm_mul, norm_pow, Complex.norm_I,
      one_pow, mul_one, norm_neg, Complex.norm_I, one_pow, mul_one]
  have hlim := (hPz.const_mul ‖Complex.exp ((Real.pi : ℂ) * Complex.I * (1 - s₀) / 2)‖).add
    (hQz.const_mul ‖Complex.exp (-(Real.pi : ℂ) * Complex.I * (1 - s₀) / 2)‖)
  rw [mul_zero, mul_zero, add_zero] at hlim
  exact squeeze_zero (fun k => norm_nonneg _) hbound hlim

theorem exists_bound_norm_dualSum {Φ : ZMod N → ℂ} (hΦ : Φ ≠ 0) (s₀ : ℂ) :
    ∃ C : ℝ, 0 < C ∧ ∀ k : ℕ, ‖dualSum Φ s₀ k‖ ≤ C := by
  obtain ⟨C₁, hC₁pos, hC₁⟩ := exists_bound_of_tendsto (tendsto_dualP' hΦ s₀)
  obtain ⟨C₂, hC₂pos, hC₂⟩ := exists_bound_of_tendsto (tendsto_dualQ' hΦ s₀)
  set e := ‖Complex.exp ((Real.pi : ℂ) * Complex.I * (1 - s₀) / 2)‖ with he
  set e' := ‖Complex.exp (-(Real.pi : ℂ) * Complex.I * (1 - s₀) / 2)‖ with he'
  refine ⟨e * C₁ + e' * C₂ + 1, ?_, fun k => ?_⟩
  · have h1 : 0 ≤ e * C₁ := mul_nonneg (norm_nonneg _) hC₁pos.le
    have h2 : 0 ≤ e' * C₂ := mul_nonneg (norm_nonneg _) hC₂pos.le
    linarith
  · have hrw : dualSum Φ s₀ k
        = Complex.exp ((Real.pi : ℂ) * Complex.I * (1 - s₀) / 2) * Complex.I ^ k
            * dualP Φ s₀ k
          + Complex.exp (-(Real.pi : ℂ) * Complex.I * (1 - s₀) / 2) * (-Complex.I) ^ k
            * dualQ Φ s₀ k := by
      rw [dualSum, exp_shift_pos, exp_shift_neg]
    have hb : ‖dualSum Φ s₀ k‖ ≤ e * ‖dualP Φ s₀ k‖ + e' * ‖dualQ Φ s₀ k‖ := by
      rw [hrw]
      refine le_trans (norm_add_le _ _) ?_
      rw [norm_mul, norm_mul, norm_pow, norm_mul, norm_mul, norm_pow, Complex.norm_I,
        one_pow, mul_one, norm_neg, Complex.norm_I, one_pow, mul_one]
    have h1 : e * ‖dualP Φ s₀ k‖ ≤ e * C₁ :=
      mul_le_mul_of_nonneg_left (hC₁ k) (norm_nonneg _)
    have h2 : e' * ‖dualQ Φ s₀ k‖ ≤ e' * C₂ :=
      mul_le_mul_of_nonneg_left (hC₂ k) (norm_nonneg _)
    linarith

/-- **The bracket has root growth one.** -/
theorem limsup_norm_dualSum_eq_one {Φ : ZMod N → ℂ} (hΦ : Φ ≠ 0) (s₀ : ℂ) :
    limsup (fun k : ℕ => ‖dualSum Φ s₀ k‖ ^ (1 / (k : ℝ))) atTop = 1 := by
  obtain ⟨C, hCpos, hC⟩ := exists_bound_norm_dualSum hΦ s₀
  have hnn : ∀ k : ℕ, (0 : ℝ) ≤ ‖dualSum Φ s₀ k‖ := fun k => norm_nonneg _
  obtain ⟨k₀, hk₀⟩ : ∃ k₀ : ℕ, 0 < ‖dualWave Φ s₀ k₀‖ := by
    rcases exists_norm_dualWave_pos hΦ s₀ with h | h
    · exact ⟨0, h⟩
    · exact ⟨1, h⟩
  have hfreq := GaloisForLFunctions.HTGeometry.frequently_le_of_periodic
    (f := fun k : ℕ => ‖dualWave Φ s₀ k‖) (p := 4) (by norm_num)
    (fun k => by rw [dualWave_periodic Φ s₀ k]) k₀
  have hsmall : ∀ᶠ k in atTop,
      ‖dualSum Φ s₀ k - dualWave Φ s₀ k‖ < ‖dualWave Φ s₀ k₀‖ / 2 := by
    have h := (tendsto_dualSum_sub_dualWave hΦ s₀)
    rw [tendsto_zero_iff_norm_tendsto_zero] at h
    exact h.eventually_lt_const (by linarith)
  have hlb : ∃ᶠ k in atTop, ‖dualWave Φ s₀ k₀‖ / 2 ≤ ‖dualSum Φ s₀ k‖ := by
    refine (hfreq.and_eventually hsmall).mono fun k hk => ?_
    obtain ⟨hw, hs⟩ := hk
    have hge : ‖dualWave Φ s₀ k‖ ≤ ‖dualSum Φ s₀ k‖
        + ‖dualSum Φ s₀ k - dualWave Φ s₀ k‖ := by
      have := norm_sub_le (dualSum Φ s₀ k) (dualSum Φ s₀ k - dualWave Φ s₀ k)
      simpa using this
    linarith
  exact GaloisForLFunctions.HTGeometry.limsup_rpow_inv_eq_one hCpos
    (by linarith : 0 < ‖dualWave Φ s₀ k₀‖ / 2) hnn hC hlb

/-- **The remainder has growth functional one.** -/
theorem hadamardLimsup_zmodRemainder {Φ : ZMod N → ℂ} (hΦ : Φ ≠ 0)
    (hs : ∀ m : ℕ, s₀ ≠ (m : ℂ)) : hadamardLimsup (zmodRemainder Φ s₀) = 1 := by
  have hn₀ : ((dualIndex Φ : ℕ) : ℂ) ≠ 0 := natCast_ne_zero_of_pos (dualIndex_pos hΦ)
  have hNC : (N : ℂ) ≠ 0 := NeZero.ne _
  set Cst : ℝ := ‖(N : ℂ) ^ (-s₀) * (2 * (Real.pi : ℂ)) ^ (-(1 - s₀))
    * ((dualIndex Φ : ℕ) : ℂ) ^ (-(1 - s₀))‖ with hCst
  have hCpos : 0 < Cst := by
    rw [hCst, norm_pos_iff]
    refine mul_ne_zero (mul_ne_zero ?_ ?_) ?_
    · exact Complex.cpow_ne_zero_iff.mpr (Or.inl hNC)
    · exact Complex.cpow_ne_zero_iff.mpr (Or.inl two_pi_ne_zero)
    · exact Complex.cpow_ne_zero_iff.mpr (Or.inl hn₀)
  obtain ⟨C, hCpos', hC⟩ := exists_bound_norm_dualSum hΦ s₀
  have hsplit : ∀ k : ℕ, ‖zmodRemainder Φ s₀ k‖
      = (Cst * ‖Complex.Gamma (1 - s₀ + (k : ℂ)) / Complex.Gamma (1 + (k : ℂ))‖)
        * ‖dualSum Φ s₀ k‖ := by
    intro k
    rw [zmodRemainder, norm_mul, norm_mul, hCst]
  have hconv : Tendsto (fun k : ℕ =>
      (Cst * ‖Complex.Gamma (1 - s₀ + (k : ℂ)) / Complex.Gamma (1 + (k : ℂ))‖)
        ^ (1 / (k : ℝ))) atTop (𝓝 1) := by
    have hprod := (tendsto_const_rpow_inv_nat hCpos).mul (tendsto_gammaQuotient hs)
    rw [one_mul] at hprod
    refine hprod.congr' ?_
    filter_upwards with k
    rw [← Real.mul_rpow hCpos.le (norm_nonneg _)]
  have hnn : ∀ k : ℕ, (0 : ℝ) ≤ ‖dualSum Φ s₀ k‖ := fun k => norm_nonneg _
  have hbbdd : IsBoundedUnder (· ≤ ·) atTop
      (fun k : ℕ => ‖dualSum Φ s₀ k‖ ^ (1 / (k : ℝ))) :=
    GaloisForLFunctions.HTGeometry.isBoundedUnder_rpow_inv hCpos' hnn hC
  have hbnn : ∀ k : ℕ, 0 ≤ ‖dualSum Φ s₀ k‖ ^ (1 / (k : ℝ)) := fun k =>
    Real.rpow_nonneg (hnn k) _
  have hcongr : ∀ k : ℕ, ‖zmodRemainder Φ s₀ k‖ ^ (1 / (k : ℝ))
      = (Cst * ‖Complex.Gamma (1 - s₀ + (k : ℂ)) / Complex.Gamma (1 + (k : ℂ))‖)
          ^ (1 / (k : ℝ))
        * ‖dualSum Φ s₀ k‖ ^ (1 / (k : ℝ)) := by
    intro k
    rw [hsplit k, Real.mul_rpow (by positivity) (hnn k)]
  have hbdd : IsBoundedUnder (· ≤ ·) atTop
      (fun k : ℕ => ‖zmodRemainder Φ s₀ k‖ ^ (1 / (k : ℝ))) := by
    obtain ⟨B, hB⟩ := id hbbdd
    rw [Filter.eventually_map] at hB
    refine ⟨2 * max B 0, ?_⟩
    rw [Filter.eventually_map]
    filter_upwards [hconv.eventually_lt_const (by norm_num : (1 : ℝ) < 2), hB]
      with k h2 hBk
    rw [hcongr k]
    exact mul_le_mul h2.le (le_trans hBk (le_max_left _ _)) (hbnn k) (by norm_num)
  have hlim : limsup (fun k : ℕ => ‖zmodRemainder Φ s₀ k‖ ^ (1 / (k : ℝ))) atTop = 1 := by
    rw [limsup_congr (Filter.Eventually.of_forall hcongr)]
    exact GaloisForLFunctions.HTGeometry.limsup_mul_eq_one_of_tendsto_one hconv hbnn
      hbbdd (limsup_norm_dualSum_eq_one hΦ s₀)
  exact GaloisForLFunctions.HTGeometry.hadamardLimsup_eq_one_of_limsup_eq_one hbdd hlim

/-- **The cusp radius law in degree one and conductor `N`.**  The factorially
normalized shifted values of a periodic L-function grow exactly like
`N/(2π n₀)`, where `n₀` is the first exponent of the dual series. -/
theorem hadamardLimsup_zmodShift {Φ : ZMod N → ℂ} (hΦ : Φ ≠ 0)
    (hs : ∀ m : ℕ, s₀ ≠ (m : ℂ)) :
    hadamardLimsup (fun k : ℕ =>
        ZMod.LFunction Φ (s₀ - (k : ℂ)) / (Nat.factorial k : ℂ))
      = ENNReal.ofReal ((N : ℝ) / (2 * Real.pi * (dualIndex Φ : ℕ))) := by
  have hn₀pos : 0 < dualIndex Φ := dualIndex_pos hΦ
  have hn₀R : (0 : ℝ) < ((dualIndex Φ : ℕ) : ℝ) := by exact_mod_cast hn₀pos
  have hfun : (fun k : ℕ =>
      ZMod.LFunction Φ (s₀ - (k : ℂ)) / (Nat.factorial k : ℂ))
      = fun k : ℕ => ((N : ℂ) * (2 * (Real.pi : ℂ))⁻¹ * (((dualIndex Φ : ℕ) : ℂ))⁻¹) ^ k
        * zmodRemainder Φ s₀ k :=
    funext fun k => zmod_shift_decomposition hΦ hs k
  rw [hfun, hadamardLimsup_geometric, hadamardLimsup_zmodRemainder hΦ hs, mul_one]
  have hnorm : ‖(N : ℂ) * (2 * (Real.pi : ℂ))⁻¹ * (((dualIndex Φ : ℕ) : ℂ))⁻¹‖
      = (N : ℝ) / (2 * Real.pi * ((dualIndex Φ : ℕ) : ℝ)) := by
    rw [norm_mul, norm_mul, norm_inv, norm_inv, Complex.norm_natCast, Complex.norm_natCast]
    have h2pi : ‖(2 * (Real.pi : ℂ))‖ = 2 * Real.pi := by
      simp [abs_of_pos Real.pi_pos]
    rw [h2pi]
    field_simp
  have hcoe : ((‖(N : ℂ) * (2 * (Real.pi : ℂ))⁻¹ * (((dualIndex Φ : ℕ) : ℂ))⁻¹‖₊ : ℝ≥0∞))
      = ENNReal.ofReal ‖(N : ℂ) * (2 * (Real.pi : ℂ))⁻¹ * (((dualIndex Φ : ℕ) : ℂ))⁻¹‖ := by
    rw [ENNReal.ofReal_eq_coe_nnreal (norm_nonneg _)]
    rfl
  rw [hcoe, hnorm]

end RootGrowth

section DirichletCase

variable {N : ℕ} [NeZero N] {s₀ : ℂ}

theorem ne_zero_of_dft_one_ne_zero {Φ : ZMod N → ℂ} (h : ZMod.dft Φ (1 : ZMod N) ≠ 0) :
    Φ ≠ 0 := by
  intro hc
  rw [hc, map_zero] at h
  exact h rfl

/-- If the dual coefficient at one does not vanish, the dual index is one. -/
theorem dualIndex_eq_one {Φ : ZMod N → ℂ} (h : ZMod.dft Φ (1 : ZMod N) ≠ 0) :
    dualIndex Φ = 1 := by
  have hΦ := ne_zero_of_dft_one_ne_zero h
  have hmem : (1 : ℕ) ∈ dualSupport Φ := by
    refine ⟨one_pos, Or.inl ?_⟩
    rw [Nat.cast_one]
    exact h
  have hle : dualIndex Φ ≤ 1 := Nat.sInf_le hmem
  have hge : 1 ≤ dualIndex Φ := dualIndex_pos hΦ
  omega

/-- **The cusp radius law for a conductor-`N` family with non-vanishing dual
coefficient at one.**  The growth constant is `N/(2π)`, matching the cusp gap
`1/N` of the shift spectrum in degree one and conductor `N`. -/
theorem hadamardLimsup_zmodShift_of_dft_one {Φ : ZMod N → ℂ}
    (h : ZMod.dft Φ (1 : ZMod N) ≠ 0) (hs : ∀ m : ℕ, s₀ ≠ (m : ℂ)) :
    hadamardLimsup (fun k : ℕ =>
        ZMod.LFunction Φ (s₀ - (k : ℂ)) / (Nat.factorial k : ℂ))
      = ENNReal.ofReal ((N : ℝ) / (2 * Real.pi)) := by
  rw [hadamardLimsup_zmodShift (ne_zero_of_dft_one_ne_zero h) hs, dualIndex_eq_one h]
  norm_num

end DirichletCase

end RHTower
