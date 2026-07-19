import GaloisForLFunctions.RHTower.CCMPrimePoleDiophantineCoherence
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.NumberTheory.DiophantineApproximation.Basic
import Mathlib.NumberTheory.WellApproximable

/-!
# Finite-place common coherence for CCM prime-pole vectors

Compact recurrence on a finite unit torus supplies one integer clock and a
simultaneous integer approximation at every local scale.  Combined with the
exact CCM Cauchy covariance law, this produces a common coherent unit direction
for every finite family of local-factor Hardy pole spaces, with an explicit
scale-sensitive squared-distance bound.

This is a positive carrier theorem: finite semilocal CCM systems necessarily
possess arbitrarily coherent cross-place pole vectors.
-/

open MeasureTheory Set Metric
open scoped ENNReal Pointwise

noncomputable section

namespace RHTower

theorem exists_fin_unitAddCircle_nsmul_norm_le
    {d : ℕ} (ξ : Fin d → UnitAddCircle) {δ : ℝ} (hδ : 0 < δ) :
    ∃ n : ℕ, 0 < n ∧ ‖n • ξ‖ ≤ δ := by
  let μ : Measure (Fin d → UnitAddCircle) := volume
  let B : Set (Fin d → UnitAddCircle) := closedBall 0 (δ / 2)
  have hrad : 0 < δ / 2 := by positivity
  have hopenpos : 0 < μ (ball 0 (δ / 2)) :=
    isOpen_ball.measure_pos μ (nonempty_ball.mpr hrad)
  have hBpos : 0 < μ B :=
    hopenpos.trans_le (measure_mono ball_subset_closedBall)
  have hBne : μ B ≠ 0 := ne_of_gt hBpos
  have htop : μ univ ≠ ∞ := measure_ne_top μ univ
  obtain ⟨N, hNmass⟩ := ENNReal.exists_nat_mul_gt hBne htop
  have hNpos : 0 < N := by
    by_contra hN
    simp only [Nat.not_lt, Nat.le_zero] at hN
    subst N
    simp at hNmass
  have hbound : μ univ ≤ (N + 1) • μ B := by
    calc
      μ univ ≤ N * μ B := hNmass.le
      _ ≤ (N + 1) * μ B := by
        gcongr
        exact_mod_cast Nat.le_succ N
      _ = (N + 1) • μ B := by simp [nsmul_eq_mul]
  obtain ⟨n, hn, hnorm⟩ :=
    NormedAddCommGroup.exists_norm_nsmul_le (μ := μ) ξ hNpos δ hbound
  exact ⟨n, hn.1, hnorm⟩

/-- Finite-torus recurrence can be forced beyond every prescribed index. -/
theorem exists_fin_unitAddCircle_nsmul_norm_le_of_lt
    {d : ℕ} (ξ : Fin d → UnitAddCircle) {δ : ℝ} (hδ : 0 < δ) (B : ℕ) :
    ∃ n : ℕ, B < n ∧ ‖n • ξ‖ ≤ δ := by
  have hscale : (0 : ℝ) < (B + 1 : ℕ) := by positivity
  obtain ⟨k, hk, hnorm⟩ :=
    exists_fin_unitAddCircle_nsmul_norm_le ξ (div_pos hδ hscale)
  refine ⟨k * (B + 1), ?_, ?_⟩
  · have hk1 : 1 ≤ k := hk
    nlinarith
  · rw [mul_nsmul]
    calc
      ‖(B + 1) • k • ξ‖ ≤ (B + 1 : ℕ) * ‖k • ξ‖ := norm_nsmul_le
      _ ≤ (B + 1 : ℕ) * (δ / (B + 1 : ℕ)) := by
        gcongr
      _ = δ := by
        field_simp

theorem exists_fin_simultaneous_integer_approximation
    {d : ℕ} (α : Fin d → ℝ) {δ : ℝ} (hδ : 0 < δ) :
    ∃ n : ℕ, 0 < n ∧ ∃ r : Fin d → ℤ,
      ∀ i, |(n : ℝ) * α i - r i| ≤ δ := by
  let ξ : Fin d → UnitAddCircle := fun i => (α i : UnitAddCircle)
  obtain ⟨n, hn, hnorm⟩ := exists_fin_unitAddCircle_nsmul_norm_le ξ hδ
  refine ⟨n, hn, fun i => round ((n : ℝ) * α i), ?_⟩
  intro i
  have hi : ‖(n • ξ) i‖ ≤ δ := (norm_le_pi_norm (n • ξ) i).trans hnorm
  simp only [ξ, Pi.smul_apply] at hi
  rw [← AddCircle.coe_nsmul, UnitAddCircle.norm_eq] at hi
  simpa only [nsmul_eq_mul] using hi

/-- Quantitative simultaneous Dirichlet approximation in `d` real
coordinates.  The common denominator is at most `(Q + 1)^d`, and every
coordinate has distance at most `1/(Q+1)` from an integer.

The exponent `d` is the exact pigeonhole cost: the first `(Q+1)^d+1`
multiples are placed in the `(Q+1)^d` product cells cut out by the fractional
parts of the coordinates. -/
theorem exists_fin_simultaneous_integer_approximation_quantitative
    {d Q : ℕ} (α : Fin d → ℝ) :
    ∃ n : ℕ, 0 < n ∧ n ≤ (Q + 1) ^ d ∧ ∃ r : Fin d → ℤ,
      ∀ i, |(n : ℝ) * α i - r i| ≤ 1 / (Q + 1 : ℝ) := by
  let M : ℕ := Q + 1
  have hMpos : 0 < M := by simp [M]
  let Cell := {z : ℤ // z ∈ Finset.Ico (0 : ℤ) M}
  let box : Fin (M ^ d + 1) → (Fin d → Cell) := fun j i =>
    ⟨⌊Int.fract (α i * (j : ℕ)) * M⌋, by
      rw [Finset.mem_Ico]
      constructor
      · exact Int.floor_nonneg.mpr
          (mul_nonneg (Int.fract_nonneg _) (Nat.cast_nonneg M))
      · exact Int.floor_lt.mpr
          (mul_lt_of_lt_one_left (Nat.cast_pos.mpr hMpos)
            (Int.fract_lt_one _))⟩
  have hCellCard : Fintype.card Cell = M := by
    simp [Cell]
  have hcard :
      Fintype.card (Fin d → Cell) < Fintype.card (Fin (M ^ d + 1)) := by
    rw [Fintype.card_pi_const, hCellCard, Fintype.card_fin]
    omega
  obtain ⟨x, y, hxy, hbox⟩ :=
    Fintype.exists_ne_map_eq_of_card_lt box hcard
  have hordered : (x : ℕ) < (y : ℕ) ∨ (y : ℕ) < (x : ℕ) :=
    Nat.lt_or_gt_of_ne (fun h => hxy (Fin.ext h))
  rcases hordered with hlt | hlt
  · let n : ℕ := (y : ℕ) - (x : ℕ)
    let r : Fin d → ℤ := fun i =>
      ⌊α i * (y : ℕ)⌋ - ⌊α i * (x : ℕ)⌋
    refine ⟨n, Nat.sub_pos_of_lt hlt, ?_, r, ?_⟩
    · have hy : (y : ℕ) ≤ M ^ d := Nat.lt_succ_iff.mp y.isLt
      exact (Nat.sub_le (y : ℕ) (x : ℕ)).trans hy
    · intro i
      have hfloor :
          ⌊Int.fract (α i * (x : ℕ)) * M⌋ =
            ⌊Int.fract (α i * (y : ℕ)) * M⌋ := by
        exact congrArg Subtype.val (congrFun hbox i)
      have hunit :
          |Int.fract (α i * (y : ℕ)) * M -
              Int.fract (α i * (x : ℕ)) * M| ≤ 1 :=
        (Int.abs_sub_lt_one_of_floor_eq_floor hfloor.symm).le
      have htarget : |(n : ℝ) * α i - r i| ≤ 1 / (M : ℝ) := by
        apply (le_div_iff₀ (Nat.cast_pos.mpr hMpos)).2
        have hinside :
            ((n : ℝ) * α i - r i) * (M : ℝ) =
              Int.fract (α i * (y : ℕ)) * M -
                Int.fract (α i * (x : ℕ)) * M := by
          simp only [n, r, Int.fract, Nat.cast_sub hlt.le, Int.cast_sub,
            ]
          ring
        calc
          |(n : ℝ) * α i - r i| * (M : ℝ) =
              |(n : ℝ) * α i - r i| * |(M : ℝ)| := by
                exact congrArg (fun z : ℝ => |(n : ℝ) * α i - r i| * z)
                  (abs_of_nonneg (Nat.cast_nonneg M)).symm
          _ = |((n : ℝ) * α i - r i) * (M : ℝ)| := (abs_mul _ _).symm
          _ = |Int.fract (α i * (y : ℕ)) * M -
                Int.fract (α i * (x : ℕ)) * M| := congrArg abs hinside
          _ ≤ 1 := hunit
      simpa only [M, Nat.cast_add, Nat.cast_one] using htarget

  · let n : ℕ := (x : ℕ) - (y : ℕ)
    let r : Fin d → ℤ := fun i =>
      ⌊α i * (x : ℕ)⌋ - ⌊α i * (y : ℕ)⌋
    refine ⟨n, Nat.sub_pos_of_lt hlt, ?_, r, ?_⟩
    · have hx : (x : ℕ) ≤ M ^ d := Nat.lt_succ_iff.mp x.isLt
      exact (Nat.sub_le (x : ℕ) (y : ℕ)).trans hx
    · intro i
      have hfloor :
          ⌊Int.fract (α i * (y : ℕ)) * M⌋ =
            ⌊Int.fract (α i * (x : ℕ)) * M⌋ := by
        exact congrArg Subtype.val (congrFun hbox.symm i)
      have hunit :
          |Int.fract (α i * (x : ℕ)) * M -
              Int.fract (α i * (y : ℕ)) * M| ≤ 1 :=
        (Int.abs_sub_lt_one_of_floor_eq_floor hfloor.symm).le
      have htarget : |(n : ℝ) * α i - r i| ≤ 1 / (M : ℝ) := by
        apply (le_div_iff₀ (Nat.cast_pos.mpr hMpos)).2
        have hinside :
            ((n : ℝ) * α i - r i) * (M : ℝ) =
              Int.fract (α i * (x : ℕ)) * M -
                Int.fract (α i * (y : ℕ)) * M := by
          simp only [n, r, Int.fract, Nat.cast_sub hlt.le, Int.cast_sub,
            ]
          ring
        calc
          |(n : ℝ) * α i - r i| * (M : ℝ) =
              |(n : ℝ) * α i - r i| * |(M : ℝ)| := by
                exact congrArg (fun z : ℝ => |(n : ℝ) * α i - r i| * z)
                  (abs_of_nonneg (Nat.cast_nonneg M)).symm
          _ = |((n : ℝ) * α i - r i) * (M : ℝ)| := (abs_mul _ _).symm
          _ = |Int.fract (α i * (x : ℕ)) * M -
                Int.fract (α i * (y : ℕ)) * M| := congrArg abs hinside
          _ ≤ 1 := hunit
      simpa only [M, Nat.cast_add, Nat.cast_one] using htarget

/-- Quantitative simultaneous recurrence for finitely many angular
frequencies.  One clock `n ≤ (Q+1)^d` brings every phase `n * ω i` within
`2π/(Q+1)` of an integral multiple of `2π`. -/
theorem exists_fin_simultaneous_two_pi_phase_approximation_quantitative
    {d Q : ℕ} (ω : Fin d → ℝ) :
    ∃ n : ℕ, 0 < n ∧ n ≤ (Q + 1) ^ d ∧ ∃ r : Fin d → ℤ,
      ∀ i, |(n : ℝ) * ω i - 2 * Real.pi * r i| ≤
        2 * Real.pi / (Q + 1 : ℝ) := by
  obtain ⟨n, hn, hnQ, r, hr⟩ :=
    exists_fin_simultaneous_integer_approximation_quantitative
      (Q := Q) (fun i => ω i / (2 * Real.pi))
  refine ⟨n, hn, hnQ, r, ?_⟩
  intro i
  have hscale := mul_le_mul_of_nonneg_left (hr i) (show 0 ≤ 2 * Real.pi by positivity)
  have hleft :
      (2 * Real.pi) * |(n : ℝ) * (ω i / (2 * Real.pi)) - r i| =
        |(n : ℝ) * ω i - 2 * Real.pi * r i| := by
    let z : ℝ := (n : ℝ) * (ω i / (2 * Real.pi)) - r i
    have hinside : (2 * Real.pi) * z =
        (n : ℝ) * ω i - 2 * Real.pi * r i := by
      dsimp only [z]
      field_simp [Real.pi_ne_zero]
    calc
      (2 * Real.pi) * |z| = |(2 * Real.pi)| * |z| := by
        exact congrArg (fun u : ℝ => u * |z|)
          (abs_of_nonneg (show 0 ≤ 2 * Real.pi by positivity)).symm
      _ = |(2 * Real.pi) * z| := (abs_mul _ _).symm
      _ = |(n : ℝ) * ω i - 2 * Real.pi * r i| := congrArg abs hinside
  have hright :
      (2 * Real.pi) * (1 / (Q + 1 : ℝ)) =
        2 * Real.pi / (Q + 1 : ℝ) := by ring
  rwa [hleft, hright] at hscale

/-- Delay--resolution separation for simultaneous recurrence.  An arbitrary
clock multiplier `L` costs only the multiplicative factor `L`; the
dimension-dependent factor `(Q+1)^d` pays solely for phase resolution. -/
theorem exists_fin_simultaneous_two_pi_phase_approximation_delayed_quantitative
    {d Q L : ℕ} (ω : Fin d → ℝ) :
    ∃ n : ℕ, L ≤ n ∧ n ≤ L * (Q + 1) ^ d ∧ ∃ r : Fin d → ℤ,
      ∀ i, |(n : ℝ) * ω i - 2 * Real.pi * r i| ≤
        2 * Real.pi / (Q + 1 : ℝ) := by
  obtain ⟨m, hm, hmQ, r, hr⟩ :=
    exists_fin_simultaneous_two_pi_phase_approximation_quantitative
      (Q := Q) (fun i => (L : ℝ) * ω i)
  let n : ℕ := L * m
  refine ⟨n, ?_, ?_, r, ?_⟩
  · dsimp only [n]
    exact Nat.le_mul_of_pos_right L hm
  · dsimp only [n]
    exact Nat.mul_le_mul_left L hmQ
  · intro i
    simpa only [n, Nat.cast_mul, mul_assoc, mul_left_comm, mul_comm] using hr i

/-- Prime-log specialization of the quantitative phase recurrence.  The
bound depends only on the number of exposed prime coordinates, not on their
sizes. -/
theorem exists_fin_primeLog_phase_recurrence_quantitative
    {d Q : ℕ} (p : Fin d → ℕ) :
    ∃ n : ℕ, 0 < n ∧ n ≤ (Q + 1) ^ d ∧ ∃ r : Fin d → ℤ,
      ∀ i, |(n : ℝ) * Real.log (p i) - 2 * Real.pi * r i| ≤
        2 * Real.pi / (Q + 1 : ℝ) :=
  exists_fin_simultaneous_two_pi_phase_approximation_quantitative
    (Q := Q) (fun i => Real.log (p i))

/-- Quantitative recurrence in a cofinal clock annulus.  Multiplying a
`(Q^2+1)^{-1}` recurrence clock by `Q` forces the clock past `Q` while
retaining phase error at most `2π/Q`. -/
theorem exists_fin_simultaneous_two_pi_phase_approximation_annular_quantitative
    {d Q : ℕ} (hQ : 0 < Q) (ω : Fin d → ℝ) :
    ∃ n : ℕ, Q ≤ n ∧ n ≤ Q * (Q ^ 2 + 1) ^ d ∧ ∃ r : Fin d → ℤ,
      ∀ i, |(n : ℝ) * ω i - 2 * Real.pi * r i| ≤
        2 * Real.pi / (Q : ℝ) := by
  obtain ⟨m, hm, hmQ, r, hr⟩ :=
    exists_fin_simultaneous_two_pi_phase_approximation_quantitative
      (Q := Q ^ 2) ω
  let n : ℕ := Q * m
  let r' : Fin d → ℤ := fun i => (Q : ℤ) * r i
  refine ⟨n, ?_, ?_, r', ?_⟩
  · dsimp only [n]
    exact Nat.le_mul_of_pos_right Q hm
  · dsimp only [n]
    exact Nat.mul_le_mul_left Q hmQ
  · intro i
    have hscale :=
      mul_le_mul_of_nonneg_left (hr i) (show 0 ≤ (Q : ℝ) by positivity)
    have hleft :
        (Q : ℝ) * |(m : ℝ) * ω i - 2 * Real.pi * r i| =
          |(n : ℝ) * ω i - 2 * Real.pi * r' i| := by
      have hinside :
          (Q : ℝ) * ((m : ℝ) * ω i - 2 * Real.pi * r i) =
            (n : ℝ) * ω i - 2 * Real.pi * r' i := by
        dsimp only [n, r']
        push_cast
        ring
      calc
        (Q : ℝ) * |(m : ℝ) * ω i - 2 * Real.pi * r i| =
            |(Q : ℝ)| * |(m : ℝ) * ω i - 2 * Real.pi * r i| := by
              rw [abs_of_nonneg (show 0 ≤ (Q : ℝ) by positivity)]
        _ = |(Q : ℝ) * ((m : ℝ) * ω i - 2 * Real.pi * r i)| :=
          (abs_mul _ _).symm
        _ = |(n : ℝ) * ω i - 2 * Real.pi * r' i| := congrArg abs hinside
    have hbudget :
        (Q : ℝ) * (2 * Real.pi / ((Q ^ 2 + 1 : ℕ) : ℝ)) ≤
          2 * Real.pi / (Q : ℝ) := by
      have hQr : 0 < (Q : ℝ) := Nat.cast_pos.mpr hQ
      have hfrac :
          (Q : ℝ) / ((Q : ℝ) ^ 2 + 1) ≤ 1 / (Q : ℝ) := by
        apply (div_le_div_iff₀ (show 0 < (Q : ℝ) ^ 2 + 1 by positivity) hQr).2
        nlinarith
      rw [show ((Q ^ 2 + 1 : ℕ) : ℝ) = (Q : ℝ) ^ 2 + 1 by norm_num]
      calc
        (Q : ℝ) * (2 * Real.pi / ((Q : ℝ) ^ 2 + 1)) =
            (2 * Real.pi) * ((Q : ℝ) / ((Q : ℝ) ^ 2 + 1)) := by ring
        _ ≤ (2 * Real.pi) * (1 / (Q : ℝ)) :=
          mul_le_mul_of_nonneg_left hfrac (by positivity)
        _ = 2 * Real.pi / (Q : ℝ) := by ring
    rw [← hleft]
    exact hscale.trans (by
      simpa only [Nat.cast_add, Nat.cast_pow, Nat.cast_one] using hbudget)

/-- A real phase is at most its distance from an integral `2π` period away
from `1` on the complex unit circle. -/
theorem norm_exp_I_mul_real_sub_one_le_mod_two_pi (x : ℝ) (r : ℤ) :
    ‖Complex.exp (Complex.I * (x : ℂ)) - 1‖ ≤
      |x - 2 * Real.pi * r| := by
  let δ : ℝ := x - 2 * Real.pi * r
  have hexp : Complex.exp (Complex.I * (x : ℂ)) =
      Complex.exp (Complex.I * (δ : ℂ)) := by
    have harg : Complex.I * (x : ℂ) =
        Complex.I * (δ : ℂ) +
          (r : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) := by
      dsimp only [δ]
      push_cast
      ring
    rw [harg, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]
  rw [hexp]
  simpa only [Real.norm_eq_abs, δ] using
    (Real.norm_exp_I_mul_ofReal_sub_one_le (x := δ))

/-- The real part of a unit phase loses at most half the square of its
distance from an integral `2π` period. -/
theorem one_sub_sq_phaseError_div_two_le_re_exp_I_mul_real
    (x e : ℝ) (r : ℤ) (he : 0 ≤ e)
    (hphase : |x - 2 * Real.pi * r| ≤ e) :
    1 - e ^ 2 / 2 ≤ (Complex.exp (Complex.I * (x : ℂ))).re := by
  let δ : ℝ := x - 2 * Real.pi * r
  have hsq : δ ^ 2 ≤ e ^ 2 := by
    have habsSq := (sq_le_sq₀ (abs_nonneg δ) he).2 (by simpa only [δ] using hphase)
    simpa only [sq_abs] using habsSq
  have hexp : Complex.exp (Complex.I * (x : ℂ)) =
      Complex.exp (Complex.I * (δ : ℂ)) := by
    have harg : Complex.I * (x : ℂ) =
        Complex.I * (δ : ℂ) +
          (r : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) := by
      dsimp only [δ]
      push_cast
      ring
    rw [harg, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]
  rw [hexp]
  calc
    1 - e ^ 2 / 2 ≤ 1 - δ ^ 2 / 2 := by linarith
    _ ≤ Real.cos δ := Real.one_sub_sq_div_two_le_cos
    _ = (Complex.exp (Complex.I * (δ : ℂ))).re := by
      rw [mul_comm, Complex.exp_mul_I]
      simp only [Complex.add_re, Complex.cos_ofReal_re, Complex.mul_re,
        Complex.sin_ofReal_re, Complex.sin_ofReal_im, Complex.I_re,
        Complex.I_im, mul_zero, zero_mul, sub_zero, add_zero]

/-- A coordinatewise `2π` phase approximation controls every weighted
Fourier readout by its total variation. -/
theorem weighted_phaseSum_sub_coherent_le_of_phase_approximation
    {d : ℕ} (n : ℕ) (ω : Fin d → ℝ) (w : Fin d → ℂ)
    (r : Fin d → ℤ) (e : ℝ)
    (hphase : ∀ i, |(n : ℝ) * ω i - 2 * Real.pi * r i| ≤ e) :
    ‖(∑ i, w i * Complex.exp
        (Complex.I * (((n : ℝ) * ω i : ℝ) : ℂ))) - ∑ i, w i‖ ≤
      e * ∑ i, ‖w i‖ := by
  rw [← Finset.sum_sub_distrib]
  calc
    ‖∑ i, (w i * Complex.exp
          (Complex.I * (((n : ℝ) * ω i : ℝ) : ℂ)) - w i)‖ ≤
        ∑ i, ‖w i * Complex.exp
          (Complex.I * (((n : ℝ) * ω i : ℝ) : ℂ)) - w i‖ :=
      norm_sum_le _ _
    _ ≤ ∑ i, e * ‖w i‖ := by
      apply Finset.sum_le_sum
      intro i hi
      have hchord := norm_exp_I_mul_real_sub_one_le_mod_two_pi
        ((n : ℝ) * ω i) (r i)
      calc
        ‖w i * Complex.exp
            (Complex.I * (((n : ℝ) * ω i : ℝ) : ℂ)) - w i‖ =
            ‖w i * (Complex.exp
              (Complex.I * (((n : ℝ) * ω i : ℝ) : ℂ)) - 1)‖ := by
                congr 1
                ring
        _ = ‖w i‖ * ‖Complex.exp
              (Complex.I * (((n : ℝ) * ω i : ℝ) : ℂ)) - 1‖ := norm_mul _ _
        _ ≤ ‖w i‖ * |(n : ℝ) * ω i - 2 * Real.pi * r i| :=
          mul_le_mul_of_nonneg_left hchord (norm_nonneg _)
        _ ≤ ‖w i‖ * e :=
          mul_le_mul_of_nonneg_left (hphase i) (norm_nonneg _)
        _ = e * ‖w i‖ := mul_comm _ _
    _ = e * ∑ i, ‖w i‖ := by rw [Finset.mul_sum]

/-- Positivity improves the weighted coherence loss from linear chord error
to quadratic phase error. -/
theorem nonnegative_weighted_phaseSum_norm_floor_of_phase_approximation
    {d : ℕ} (n : ℕ) (ω : Fin d → ℝ) (w : Fin d → ℝ)
    (r : Fin d → ℤ) (e : ℝ) (he : 0 ≤ e)
    (hw : ∀ i, 0 ≤ w i)
    (hphase : ∀ i, |(n : ℝ) * ω i - 2 * Real.pi * r i| ≤ e) :
    (1 - e ^ 2 / 2) * ∑ i, w i ≤
      ‖∑ i, (w i : ℂ) * Complex.exp
        (Complex.I * (((n : ℝ) * ω i : ℝ) : ℂ))‖ := by
  calc
    (1 - e ^ 2 / 2) * ∑ i, w i =
        ∑ i, (1 - e ^ 2 / 2) * w i := by rw [Finset.mul_sum]
    _ ≤ ∑ i, ((w i : ℂ) * Complex.exp
        (Complex.I * (((n : ℝ) * ω i : ℝ) : ℂ))).re := by
      apply Finset.sum_le_sum
      intro i hi
      have hcos := one_sub_sq_phaseError_div_two_le_re_exp_I_mul_real
        ((n : ℝ) * ω i) e (r i) he (hphase i)
      simpa only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
        zero_mul, mul_zero, sub_zero, mul_comm] using
          mul_le_mul_of_nonneg_right hcos (hw i)
    _ = (∑ i, (w i : ℂ) * Complex.exp
        (Complex.I * (((n : ℝ) * ω i : ℝ) : ℂ))).re := by
      exact (Complex.re_sum (s := Finset.univ)
        (fun i => (w i : ℂ) * Complex.exp
          (Complex.I * (((n : ℝ) * ω i : ℝ) : ℂ)))).symm
    _ ≤ ‖∑ i, (w i : ℂ) * Complex.exp
        (Complex.I * (((n : ℝ) * ω i : ℝ) : ℂ))‖ :=
      Complex.re_le_norm _

/-- Quantitative recurrence of an arbitrary finite weighted phase sum.  One
clock of size at most `(Q+1)^d` brings the sum within
`(2π/(Q+1)) * ∑ ‖w_i‖` of its fully coherent value. -/
theorem exists_fin_weighted_phaseSum_recurrence_quantitative
    {d Q : ℕ} (ω : Fin d → ℝ) (w : Fin d → ℂ) :
    ∃ n : ℕ, 0 < n ∧ n ≤ (Q + 1) ^ d ∧
      ‖(∑ i, w i * Complex.exp
          (Complex.I * (((n : ℝ) * ω i : ℝ) : ℂ))) - ∑ i, w i‖ ≤
        (2 * Real.pi / (Q + 1 : ℝ)) * ∑ i, ‖w i‖ := by
  obtain ⟨n, hn, hnQ, r, hr⟩ :=
    exists_fin_simultaneous_two_pi_phase_approximation_quantitative
      (Q := Q) ω
  refine ⟨n, hn, hnQ, ?_⟩
  rw [← Finset.sum_sub_distrib]
  calc
    ‖∑ i, (w i * Complex.exp
          (Complex.I * (((n : ℝ) * ω i : ℝ) : ℂ)) - w i)‖ ≤
        ∑ i, ‖w i * Complex.exp
          (Complex.I * (((n : ℝ) * ω i : ℝ) : ℂ)) - w i‖ :=
      norm_sum_le _ _
    _ ≤ ∑ i, (2 * Real.pi / (Q + 1 : ℝ)) * ‖w i‖ := by
      apply Finset.sum_le_sum
      intro i hi
      have hphase := norm_exp_I_mul_real_sub_one_le_mod_two_pi
        ((n : ℝ) * ω i) (r i)
      calc
        ‖w i * Complex.exp
            (Complex.I * (((n : ℝ) * ω i : ℝ) : ℂ)) - w i‖ =
            ‖w i * (Complex.exp
              (Complex.I * (((n : ℝ) * ω i : ℝ) : ℂ)) - 1)‖ := by
                congr 1
                ring
        _ = ‖w i‖ * ‖Complex.exp
              (Complex.I * (((n : ℝ) * ω i : ℝ) : ℂ)) - 1‖ := norm_mul _ _
        _ ≤ ‖w i‖ * |(n : ℝ) * ω i - 2 * Real.pi * r i| :=
          mul_le_mul_of_nonneg_left hphase (norm_nonneg _)
        _ ≤ ‖w i‖ * (2 * Real.pi / (Q + 1 : ℝ)) :=
          mul_le_mul_of_nonneg_left (hr i) (norm_nonneg _)
        _ = (2 * Real.pi / (Q + 1 : ℝ)) * ‖w i‖ := mul_comm _ _
    _ = (2 * Real.pi / (Q + 1 : ℝ)) * ∑ i, ‖w i‖ := by
      rw [Finset.mul_sum]

/-- The recurrence estimate gives a deterministic capacity floor: by time
`(Q+1)^d`, the phase sum has norm at least the norm of its coherent value,
minus `(2π/(Q+1))` times its total variation. -/
theorem exists_fin_weighted_phaseSum_norm_floor_quantitative
    {d Q : ℕ} (ω : Fin d → ℝ) (w : Fin d → ℂ) :
    ∃ n : ℕ, 0 < n ∧ n ≤ (Q + 1) ^ d ∧
      ‖∑ i, w i‖ - (2 * Real.pi / (Q + 1 : ℝ)) * ∑ i, ‖w i‖ ≤
        ‖∑ i, w i * Complex.exp
          (Complex.I * (((n : ℝ) * ω i : ℝ) : ℂ))‖ := by
  obtain ⟨n, hn, hnQ, hdist⟩ :=
    exists_fin_weighted_phaseSum_recurrence_quantitative (Q := Q) ω w
  refine ⟨n, hn, hnQ, ?_⟩
  have hreverse :
      ‖∑ i, w i‖ -
          ‖∑ i, w i * Complex.exp
            (Complex.I * (((n : ℝ) * ω i : ℝ) : ℂ))‖ ≤
        ‖(∑ i, w i) - ∑ i, w i * Complex.exp
          (Complex.I * (((n : ℝ) * ω i : ℝ) : ℂ))‖ :=
    norm_sub_norm_le _ _
  have hsymm :
      ‖(∑ i, w i) - ∑ i, w i * Complex.exp
          (Complex.I * (((n : ℝ) * ω i : ℝ) : ℂ))‖ =
        ‖(∑ i, w i * Complex.exp
          (Complex.I * (((n : ℝ) * ω i : ℝ) : ℂ))) - ∑ i, w i‖ := by
    rw [norm_sub_rev]
  rw [hsymm] at hreverse
  linarith

/-- Prime-log specialization of weighted quantitative coherence. -/
theorem exists_fin_primeLog_weighted_phaseSum_recurrence_quantitative
    {d Q : ℕ} (p : Fin d → ℕ) (w : Fin d → ℂ) :
    ∃ n : ℕ, 0 < n ∧ n ≤ (Q + 1) ^ d ∧
      ‖(∑ i, w i * Complex.exp
          (Complex.I * (((n : ℝ) * Real.log (p i) : ℝ) : ℂ))) - ∑ i, w i‖ ≤
        (2 * Real.pi / (Q + 1 : ℝ)) * ∑ i, ‖w i‖ :=
  exists_fin_weighted_phaseSum_recurrence_quantitative
    (Q := Q) (fun i => Real.log (p i)) w

/-- Weighted delay--resolution separation.  The source can be rescaled by any
clock multiplier `L` without worsening the phase error or the exponential
dimension cost. -/
theorem exists_fin_weighted_phaseSum_recurrence_delayed_quantitative
    {d Q L : ℕ} (ω : Fin d → ℝ) (w : Fin d → ℂ) :
    ∃ n : ℕ, L ≤ n ∧ n ≤ L * (Q + 1) ^ d ∧
      ‖(∑ i, w i * Complex.exp
          (Complex.I * (((n : ℝ) * ω i : ℝ) : ℂ))) - ∑ i, w i‖ ≤
        (2 * Real.pi / (Q + 1 : ℝ)) * ∑ i, ‖w i‖ := by
  obtain ⟨n, hnL, hn, r, hr⟩ :=
    exists_fin_simultaneous_two_pi_phase_approximation_delayed_quantitative
      (L := L) ω
  exact ⟨n, hnL, hn,
    weighted_phaseSum_sub_coherent_le_of_phase_approximation
      n ω w r (2 * Real.pi / (Q + 1 : ℝ)) hr⟩

/-- Prime-log specialization of weighted delay--resolution separation. -/
theorem exists_fin_primeLog_weighted_phaseSum_recurrence_delayed_quantitative
    {d Q L : ℕ} (p : Fin d → ℕ) (w : Fin d → ℂ) :
    ∃ n : ℕ, L ≤ n ∧ n ≤ L * (Q + 1) ^ d ∧
      ‖(∑ i, w i * Complex.exp
          (Complex.I * (((n : ℝ) * Real.log (p i) : ℝ) : ℂ))) - ∑ i, w i‖ ≤
        (2 * Real.pi / (Q + 1 : ℝ)) * ∑ i, ‖w i‖ :=
  exists_fin_weighted_phaseSum_recurrence_delayed_quantitative
    (L := L) (fun i => Real.log (p i)) w

/-- A cofinal weighted recurrence: the clock is forced beyond `Q`, remains
at most `Q * (Q^2+1)^d`, and the source returns within `(2π/Q)` times its
total variation of full coherence. -/
theorem exists_fin_weighted_phaseSum_recurrence_annular_quantitative
    {d Q : ℕ} (hQ : 0 < Q) (ω : Fin d → ℝ) (w : Fin d → ℂ) :
    ∃ n : ℕ, Q ≤ n ∧ n ≤ Q * (Q ^ 2 + 1) ^ d ∧
      ‖(∑ i, w i * Complex.exp
          (Complex.I * (((n : ℝ) * ω i : ℝ) : ℂ))) - ∑ i, w i‖ ≤
        (2 * Real.pi / (Q : ℝ)) * ∑ i, ‖w i‖ := by
  obtain ⟨n, hnQ, hn, r, hr⟩ :=
    exists_fin_simultaneous_two_pi_phase_approximation_annular_quantitative
      hQ ω
  exact ⟨n, hnQ, hn,
    weighted_phaseSum_sub_coherent_le_of_phase_approximation
      n ω w r (2 * Real.pi / (Q : ℝ)) hr⟩

/-- Prime-log specialization of the cofinal weighted recurrence. -/
theorem exists_fin_primeLog_weighted_phaseSum_recurrence_annular_quantitative
    {d Q : ℕ} (hQ : 0 < Q) (p : Fin d → ℕ) (w : Fin d → ℂ) :
    ∃ n : ℕ, Q ≤ n ∧ n ≤ Q * (Q ^ 2 + 1) ^ d ∧
      ‖(∑ i, w i * Complex.exp
          (Complex.I * (((n : ℝ) * Real.log (p i) : ℝ) : ℂ))) - ∑ i, w i‖ ≤
        (2 * Real.pi / (Q : ℝ)) * ∑ i, ‖w i‖ :=
  exists_fin_weighted_phaseSum_recurrence_annular_quantitative
    hQ (fun i => Real.log (p i)) w

/-- The critical polar mode sampled at a positive integer clock. -/
noncomputable def criticalPrimePolarClock (n : ℕ) : ℂ :=
  (((1 / 2 : ℝ) : ℂ) - Complex.I * (n : ℝ))⁻¹

/-- The critical polar mode is bounded by the reciprocal clock. -/
theorem norm_criticalPrimePolarClock_le_inv_nat {n : ℕ} (hn : 0 < n) :
    ‖criticalPrimePolarClock n‖ ≤ 1 / (n : ℝ) := by
  let z : ℂ := ((1 / 2 : ℝ) : ℂ) - Complex.I * (n : ℝ)
  have hzn : (n : ℝ) ≤ ‖z‖ := by
    have him := Complex.abs_im_le_norm z
    simpa only [z, Complex.sub_im, Complex.ofReal_im, Complex.mul_im,
      Complex.I_re, Complex.I_im, Complex.ofReal_re, zero_sub, zero_mul,
      one_mul, zero_add, abs_neg,
      abs_of_nonneg (show 0 ≤ (n : ℝ) from Nat.cast_nonneg n)] using him
  change ‖z⁻¹‖ ≤ 1 / (n : ℝ)
  rw [norm_inv, one_div]
  exact inv_anti₀ (Nat.cast_pos.mpr hn) hzn

/-- Quadratic delayed prime--polar capacity floor for nonnegative weights.
The phase loss is `2π²/(Q+1)²`, while the independently chosen delay `L`
controls the polar loss by `1/L`. -/
theorem exists_fin_primeLog_nonnegative_phaseSum_polar_floor_delayed_quantitative
    {d Q L : ℕ} (hL : 0 < L) (p : Fin d → ℕ) (w : Fin d → ℝ)
    (hw : ∀ i, 0 ≤ w i) :
    ∃ n : ℕ, L ≤ n ∧ n ≤ L * (Q + 1) ^ d ∧
      ‖(∑ i, (w i : ℂ) * Complex.exp
          (Complex.I * (((n : ℝ) * Real.log (p i) : ℝ) : ℂ))) -
            criticalPrimePolarClock n‖ ≥
        (1 - (2 * Real.pi / (Q + 1 : ℝ)) ^ 2 / 2) * ∑ i, w i -
          1 / (L : ℝ) := by
  obtain ⟨n, hnL, hnTop, r, hr⟩ :=
    exists_fin_simultaneous_two_pi_phase_approximation_delayed_quantitative
      (Q := Q) (L := L) (fun i => Real.log (p i))
  refine ⟨n, hnL, hnTop, ?_⟩
  let S : ℂ := ∑ i, (w i : ℂ) * Complex.exp
    (Complex.I * (((n : ℝ) * Real.log (p i) : ℝ) : ℂ))
  let e : ℝ := 2 * Real.pi / (Q + 1 : ℝ)
  have hsource : (1 - e ^ 2 / 2) * ∑ i, w i ≤ ‖S‖ := by
    simpa only [S, e] using
      nonnegative_weighted_phaseSum_norm_floor_of_phase_approximation
        n (fun i => Real.log (p i)) w r e (by positivity) hw hr
  have hnpos : 0 < n := hL.trans_le hnL
  have hpoleN : ‖criticalPrimePolarClock n‖ ≤ 1 / (n : ℝ) :=
    norm_criticalPrimePolarClock_le_inv_nat hnpos
  have hpoleL : ‖criticalPrimePolarClock n‖ ≤ 1 / (L : ℝ) := by
    exact hpoleN.trans (by
      rw [one_div, one_div]
      exact inv_anti₀ (Nat.cast_pos.mpr hL) (Nat.cast_le.mpr hnL))
  have hSP : ‖S‖ - ‖criticalPrimePolarClock n‖ ≤
      ‖S - criticalPrimePolarClock n‖ :=
    norm_sub_norm_le S (criticalPrimePolarClock n)
  dsimp only [S, e] at hsource hSP ⊢
  linarith

/-- Sharp delayed prime--polar capacity floor.  Phase resolution `Q` and the
polar-decay clock floor `L` enter independently. -/
theorem exists_fin_primeLog_weighted_phaseSum_polar_floor_delayed_quantitative
    {d Q L : ℕ} (hL : 0 < L) (p : Fin d → ℕ) (w : Fin d → ℂ) :
    ∃ n : ℕ, L ≤ n ∧ n ≤ L * (Q + 1) ^ d ∧
      ‖(∑ i, w i * Complex.exp
          (Complex.I * (((n : ℝ) * Real.log (p i) : ℝ) : ℂ))) -
            criticalPrimePolarClock n‖ ≥
        ‖∑ i, w i‖ - (2 * Real.pi / (Q + 1 : ℝ)) * ∑ i, ‖w i‖ -
          1 / (L : ℝ) := by
  obtain ⟨n, hnL, hnTop, hdist⟩ :=
    exists_fin_primeLog_weighted_phaseSum_recurrence_delayed_quantitative
      (L := L) p w
  refine ⟨n, hnL, hnTop, ?_⟩
  let S : ℂ := ∑ i, w i * Complex.exp
    (Complex.I * (((n : ℝ) * Real.log (p i) : ℝ) : ℂ))
  let W : ℂ := ∑ i, w i
  let e : ℝ := (2 * Real.pi / (Q + 1 : ℝ)) * ∑ i, ‖w i‖
  have hWS : ‖W‖ - ‖S‖ ≤ e := by
    have hreverse : ‖W‖ - ‖S‖ ≤ ‖W - S‖ := norm_sub_norm_le W S
    have hsymm : ‖W - S‖ = ‖S - W‖ := norm_sub_rev W S
    exact hreverse.trans (by
      rw [hsymm]
      simpa only [S, W, e] using hdist)
  have hnpos : 0 < n := hL.trans_le hnL
  have hpoleN : ‖criticalPrimePolarClock n‖ ≤ 1 / (n : ℝ) :=
    norm_criticalPrimePolarClock_le_inv_nat hnpos
  have hpoleL : ‖criticalPrimePolarClock n‖ ≤ 1 / (L : ℝ) := by
    exact hpoleN.trans (by
      rw [one_div, one_div]
      exact inv_anti₀ (Nat.cast_pos.mpr hL) (Nat.cast_le.mpr hnL))
  have hSP : ‖S‖ - ‖criticalPrimePolarClock n‖ ≤
      ‖S - criticalPrimePolarClock n‖ :=
    norm_sub_norm_le S (criticalPrimePolarClock n)
  dsimp only [S, W, e] at hWS hSP ⊢
  linarith

/-- Quantitative prime--polar capacity floor in a cofinal annulus.  A finite
weighted prime-log source reaches its coherent value up to phase loss
`(2π/Q) * totalVariation`, while the critical polar mode is simultaneously
at most `1/Q`. -/
theorem exists_fin_primeLog_weighted_phaseSum_polar_floor_annular_quantitative
    {d Q : ℕ} (hQ : 0 < Q) (p : Fin d → ℕ) (w : Fin d → ℂ) :
    ∃ n : ℕ, Q ≤ n ∧ n ≤ Q * (Q ^ 2 + 1) ^ d ∧
      ‖(∑ i, w i * Complex.exp
          (Complex.I * (((n : ℝ) * Real.log (p i) : ℝ) : ℂ))) -
            criticalPrimePolarClock n‖ ≥
        ‖∑ i, w i‖ - (2 * Real.pi / (Q : ℝ)) * ∑ i, ‖w i‖ -
          1 / (Q : ℝ) := by
  obtain ⟨n, hnQ, hnTop, hdist⟩ :=
    exists_fin_primeLog_weighted_phaseSum_recurrence_annular_quantitative
      hQ p w
  refine ⟨n, hnQ, hnTop, ?_⟩
  let S : ℂ := ∑ i, w i * Complex.exp
    (Complex.I * (((n : ℝ) * Real.log (p i) : ℝ) : ℂ))
  let W : ℂ := ∑ i, w i
  let e : ℝ := (2 * Real.pi / (Q : ℝ)) * ∑ i, ‖w i‖
  have hWS : ‖W‖ - ‖S‖ ≤ e := by
    have hreverse : ‖W‖ - ‖S‖ ≤ ‖W - S‖ := norm_sub_norm_le W S
    have hsymm : ‖W - S‖ = ‖S - W‖ := norm_sub_rev W S
    exact hreverse.trans (by
      rw [hsymm]
      simpa only [S, W, e] using hdist)
  have hnpos : 0 < n := hQ.trans_le hnQ
  have hpoleN : ‖criticalPrimePolarClock n‖ ≤ 1 / (n : ℝ) :=
    norm_criticalPrimePolarClock_le_inv_nat hnpos
  have hpoleQ : ‖criticalPrimePolarClock n‖ ≤ 1 / (Q : ℝ) := by
    exact hpoleN.trans (by
      rw [one_div, one_div]
      exact inv_anti₀ (Nat.cast_pos.mpr hQ) (Nat.cast_le.mpr hnQ))
  have hSP : ‖S‖ - ‖criticalPrimePolarClock n‖ ≤
      ‖S - criticalPrimePolarClock n‖ :=
    norm_sub_norm_le S (criticalPrimePolarClock n)
  dsimp only [S, W, e] at hWS hSP ⊢
  linarith

/-- Simultaneous integer approximation with an arbitrarily large common
denominator. -/
theorem exists_fin_simultaneous_integer_approximation_of_lt
    {d : ℕ} (α : Fin d → ℝ) {δ : ℝ} (hδ : 0 < δ) (B : ℕ) :
    ∃ n : ℕ, B < n ∧ ∃ r : Fin d → ℤ,
      ∀ i, |(n : ℝ) * α i - r i| ≤ δ := by
  let ξ : Fin d → UnitAddCircle := fun i => (α i : UnitAddCircle)
  obtain ⟨n, hn, hnorm⟩ := exists_fin_unitAddCircle_nsmul_norm_le_of_lt ξ hδ B
  refine ⟨n, hn, fun i => round ((n : ℝ) * α i), ?_⟩
  intro i
  have hi : ‖(n • ξ) i‖ ≤ δ := (norm_le_pi_norm (n • ξ) i).trans hnorm
  simp only [ξ, Pi.smul_apply] at hi
  rw [← AddCircle.coe_nsmul, UnitAddCircle.norm_eq] at hi
  simpa only [nsmul_eq_mul] using hi

theorem exists_fin_ccmPrimePole_common_coherence
    {d : ℕ} {Lref : ℝ} (href : 0 < Lref)
    (L : Fin d → ℝ) (hL : ∀ i, 0 < L i)
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ n : ℕ, 0 < n ∧ ∃ r : Fin d → ℤ, ∀ i,
      ‖ccmNormalizedPrimePoleVector (L i) (hL i) (r i) -
          ccmNormalizedPrimePoleVector Lref href n‖ ^ 2 ≤
        2 * (2 * Real.pi * (δ / L i)) ^ 2 := by
  obtain ⟨n, hn, r, happrox⟩ :=
    exists_fin_simultaneous_integer_approximation (fun i => L i / Lref) hδ
  refine ⟨n, hn, r, ?_⟩
  intro i
  apply (norm_sub_sq_ccmNormalizedPrimePoleVector_le_frequency_defect
    href (hL i) n (r i)).trans
  have hgap :
      |(r i : ℝ) / L i - (n : ℝ) / Lref| ≤ δ / L i := by
    have heq :
        (r i : ℝ) / L i - (n : ℝ) / Lref =
          -(((n : ℝ) * (L i / Lref) - r i) / L i) := by
      field_simp [href.ne', (hL i).ne']
      ring
    rw [heq, abs_neg, abs_div, abs_of_pos (hL i)]
    exact div_le_div_of_nonneg_right (happrox i) (hL i).le
  have hpi : 0 ≤ 2 * Real.pi := by positivity
  have hscaled :
      |2 * Real.pi * ((r i : ℝ) / L i - (n : ℝ) / Lref)| ≤
        2 * Real.pi * (δ / L i) := by
    rw [abs_mul, abs_of_nonneg hpi]
    exact mul_le_mul_of_nonneg_left hgap hpi
  have hright : 0 ≤ 2 * Real.pi * (δ / L i) :=
    mul_nonneg hpi (div_nonneg hδ.le (hL i).le)
  have hsq := (sq_le_sq₀ (abs_nonneg _) hright).2 hscaled
  rw [sq_abs] at hsq
  exact mul_le_mul_of_nonneg_left hsq (by norm_num)

/-- Cofinal finite-place coherence: the common reference pole index can be
forced beyond any prescribed bound without weakening the defect estimate. -/
theorem exists_fin_ccmPrimePole_cofinal_common_coherence
    {d : ℕ} {Lref : ℝ} (href : 0 < Lref)
    (L : Fin d → ℝ) (hL : ∀ i, 0 < L i)
    {δ : ℝ} (hδ : 0 < δ) (B : ℕ) :
    ∃ n : ℕ, B < n ∧ ∃ r : Fin d → ℤ, ∀ i,
      ‖ccmNormalizedPrimePoleVector (L i) (hL i) (r i) -
          ccmNormalizedPrimePoleVector Lref href n‖ ^ 2 ≤
        2 * (2 * Real.pi * (δ / L i)) ^ 2 := by
  obtain ⟨n, hn, r, happrox⟩ :=
    exists_fin_simultaneous_integer_approximation_of_lt
      (fun i => L i / Lref) hδ B
  refine ⟨n, hn, r, ?_⟩
  intro i
  apply (norm_sub_sq_ccmNormalizedPrimePoleVector_le_frequency_defect
    href (hL i) n (r i)).trans
  have hgap :
      |(r i : ℝ) / L i - (n : ℝ) / Lref| ≤ δ / L i := by
    have heq :
        (r i : ℝ) / L i - (n : ℝ) / Lref =
          -(((n : ℝ) * (L i / Lref) - r i) / L i) := by
      field_simp [href.ne', (hL i).ne']
      ring
    rw [heq, abs_neg, abs_div, abs_of_pos (hL i)]
    exact div_le_div_of_nonneg_right (happrox i) (hL i).le
  have hpi : 0 ≤ 2 * Real.pi := by positivity
  have hscaled :
      |2 * Real.pi * ((r i : ℝ) / L i - (n : ℝ) / Lref)| ≤
        2 * Real.pi * (δ / L i) := by
    rw [abs_mul, abs_of_nonneg hpi]
    exact mul_le_mul_of_nonneg_left hgap hpi
  have hright : 0 ≤ 2 * Real.pi * (δ / L i) :=
    mul_nonneg hpi (div_nonneg hδ.le (hL i).le)
  have hsq := (sq_le_sq₀ (abs_nonneg _) hright).2 hscaled
  rw [sq_abs] at hsq
  exact mul_le_mul_of_nonneg_left hsq (by norm_num)

/-- Prime specialization of finite common coherence.  Every finite family of
prime local factors has arbitrarily coherent normalized CCM pole vectors with
the displayed logarithmic scale loss. -/
theorem exists_fin_prime_ccmPrimePole_common_coherence
    {d pref : ℕ} (hpref : pref.Prime)
    (p : Fin d → ℕ) (hp : ∀ i, (p i).Prime)
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ n : ℕ, 0 < n ∧ ∃ r : Fin d → ℤ, ∀ i,
      ‖ccmNormalizedPrimePoleVector (Real.log (p i))
          (Real.log_pos (by exact_mod_cast (hp i).one_lt)) (r i) -
        ccmNormalizedPrimePoleVector (Real.log pref)
          (Real.log_pos (by exact_mod_cast hpref.one_lt)) n‖ ^ 2 ≤
      2 * (2 * Real.pi * (δ / Real.log (p i))) ^ 2 := by
  exact exists_fin_ccmPrimePole_common_coherence
    (Real.log_pos (by exact_mod_cast hpref.one_lt))
    (fun i => Real.log (p i))
    (fun i => Real.log_pos (by exact_mod_cast (hp i).one_lt)) hδ

end RHTower
