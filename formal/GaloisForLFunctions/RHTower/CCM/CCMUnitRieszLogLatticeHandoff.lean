import GaloisForLFunctions.RHTower.CCM.CCMUnitRieszCoherentOutgoingChargeHankel

/-!
# Integer-log to continuous-aperture handoff for the unit CCM resolvent

The literal completed outgoing HG block is sampled naturally at integer apertures `log N`.
This module proves those samples lose no continuous-ray information: on each cell
`N <= X <= N+1`, the exact Chebyshev integral changes by at most the elementary constant
`log 4 + 5`. Hence any uniform integer-log bound propagates to every `t >= log 2`.

In particular, pole domination of all literal outgoing integer blocks gives a uniform bound on
the full continuous aperture resolvent. No PNT estimate, zero-free region, or RH premise enters.
-/

open Set MeasureTheory Filter Topology

noncomputable section

namespace GaloisForLFunctions.RHTower

open _root_.RHTower

private def criticalMellinHalfWeightIntegrand (y : ℝ) : ℝ :=
  (Chebyshev.psi y - y) * y ^ (-(1 / 2 : ℝ))

private theorem intervalIntegrable_criticalMellinHalfWeightIntegrand
    {a b : ℝ} (ha : 1 ≤ a) (hab : a ≤ b) :
    IntervalIntegrable criticalMellinHalfWeightIntegrand volume a b := by
  have hpsi : IntervalIntegrable (fun y : ℝ => Chebyshev.psi y - y) volume a b :=
    Chebyshev.psi_mono.intervalIntegrable.sub
      (continuous_id.intervalIntegrable (μ := volume) a b)
  have hpow : ContinuousOn (fun y : ℝ => y ^ (-(1 / 2 : ℝ))) (Set.uIcc a b) := by
    apply ContinuousOn.rpow_const continuousOn_id
    intro y hy
    left
    rw [Set.uIcc_of_le hab] at hy
    exact ne_of_gt (zero_lt_one.trans_le (ha.trans hy.1))
  exact hpsi.mul_continuousOn hpow

private theorem abs_criticalMellinHalfWeightIntegrand_le
    {X y : ℝ} (hy : 1 ≤ y) (hyX : y ≤ X) :
    |criticalMellinHalfWeightIntegrand y| ≤ (Real.log 4 + 5) * X := by
  have hpsi0 : 0 ≤ Chebyshev.psi y := Chebyshev.psi_nonneg y
  have hpsi := Chebyshev.psi_le_const_mul_self (show 0 ≤ y by linarith)
  have hC : 0 ≤ Real.log 4 + 5 := by positivity
  have herr : |Chebyshev.psi y - y| ≤ (Real.log 4 + 5) * y := by
    calc
      |Chebyshev.psi y - y| ≤ |Chebyshev.psi y| + |y| := abs_sub _ _
      _ = Chebyshev.psi y + y := by
        rw [abs_of_nonneg hpsi0, abs_of_nonneg (by linarith)]
      _ ≤ (Real.log 4 + 4) * y + y := by gcongr
      _ = (Real.log 4 + 5) * y := by ring
  have hpow0 : 0 ≤ y ^ (-(1 / 2 : ℝ)) := Real.rpow_nonneg (by linarith) _
  have hpow1 : y ^ (-(1 / 2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hy (by norm_num)
  rw [criticalMellinHalfWeightIntegrand, abs_mul, abs_of_nonneg hpow0]
  calc
    |Chebyshev.psi y - y| * y ^ (-(1 / 2 : ℝ)) ≤
        ((Real.log 4 + 5) * y) * 1 := by gcongr
    _ = (Real.log 4 + 5) * y := by ring
    _ ≤ (Real.log 4 + 5) * X := by gcongr

/-- On one integer aperture cell, continuous resolvent differs from left integer sample by at
most one elementary Chebyshev constant. -/
theorem abs_criticalMellinChebyshevResolventSource_log_le_nat_add
    {N : ℕ} {X : ℝ} (hN : 2 ≤ N)
    (hNX : (N : ℝ) ≤ X) (hXN : X ≤ (N : ℝ) + 1) :
    |criticalMellinChebyshevResolventSource (Real.log X)| ≤
      |criticalMellinChebyshevResolventSource (Real.log N)| +
        (Real.log 4 + 5) := by
  have hNreal : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  have hNpos : (0 : ℝ) < N := zero_lt_one.trans_le hNreal
  have hXpos : 0 < X := hNpos.trans_le hNX
  have hlogN : 0 ≤ Real.log N := Real.log_nonneg hNreal
  have hlogX : 0 ≤ Real.log X := Real.log_nonneg (hNreal.trans hNX)
  have hrayN := unitRieszChebyshevRayIntegral_eq_fullResolvent hlogN
  have hrayX := unitRieszChebyshevRayIntegral_eq_fullResolvent hlogX
  rw [Real.exp_log hNpos] at hrayN
  rw [Real.exp_log hXpos] at hrayX
  have hprimeN := unitRieszChebyshevRayIntegral_eq_primeIntegral (Real.log N)
  have hprimeX := unitRieszChebyshevRayIntegral_eq_primeIntegral (Real.log X)
  rw [Real.exp_log hNpos] at hprimeN
  rw [Real.exp_log hXpos] at hprimeX
  have hintN : IntervalIntegrable criticalMellinHalfWeightIntegrand volume 1 (N : ℝ) :=
    intervalIntegrable_criticalMellinHalfWeightIntegrand (a := 1) (b := (N : ℝ)) le_rfl hNreal
  have hintTail : IntervalIntegrable criticalMellinHalfWeightIntegrand volume (N : ℝ) X :=
    intervalIntegrable_criticalMellinHalfWeightIntegrand hNreal hNX
  have hsplit : unitRieszChebyshevRayIntegral (Real.log X) =
      unitRieszChebyshevRayIntegral (Real.log N) +
        ∫ y in (N : ℝ)..X, criticalMellinHalfWeightIntegrand y := by
    rw [hprimeX, hprimeN]
    change (∫ y in (1 : ℝ)..X, criticalMellinHalfWeightIntegrand y) = _
    exact (intervalIntegral.integral_add_adjacent_intervals hintN hintTail).symm
  let T : ℝ := ∫ y in (N : ℝ)..X, criticalMellinHalfWeightIntegrand y
  have hT : |T| ≤ (Real.log 4 + 5) * X := by
    have hraw := intervalIntegral.norm_integral_le_of_norm_le_const
      (f := criticalMellinHalfWeightIntegrand)
      (a := (N : ℝ)) (b := X) (C := (Real.log 4 + 5) * X) (fun y hy => by
        have hy' : y ∈ Set.uIcc (N : ℝ) X := Set.uIoc_subset_uIcc hy
        rw [Set.uIcc_of_le hNX] at hy'
        rw [Real.norm_eq_abs]
        exact abs_criticalMellinHalfWeightIntegrand_le
          (hNreal.trans hy'.1) hy'.2)
    rw [Real.norm_eq_abs] at hraw
    change |T| ≤ _
    calc
      |T| ≤ (Real.log 4 + 5) * X * |X - (N : ℝ)| := hraw
      _ ≤ (Real.log 4 + 5) * X * 1 := by
        gcongr
        rw [abs_of_nonneg (sub_nonneg.mpr hNX)]
        linarith
      _ = (Real.log 4 + 5) * X := by ring
  have hEq : X * criticalMellinChebyshevResolventSource (Real.log X) =
      (N : ℝ) * criticalMellinChebyshevResolventSource (Real.log N) + T := by
    change _ = _ + (∫ y in (N : ℝ)..X, criticalMellinHalfWeightIntegrand y)
    linarith [hrayN, hrayX, hsplit]
  have hformula : criticalMellinChebyshevResolventSource (Real.log X) =
      ((N : ℝ) / X) * criticalMellinChebyshevResolventSource (Real.log N) + T / X := by
    calc
      criticalMellinChebyshevResolventSource (Real.log X) =
          ((N : ℝ) * criticalMellinChebyshevResolventSource (Real.log N) + T) / X := by
        apply (eq_div_iff hXpos.ne').2
        nlinarith [hEq]
      _ = ((N : ℝ) / X) * criticalMellinChebyshevResolventSource (Real.log N) + T / X := by ring
  rw [hformula]
  have hratio0 : 0 ≤ (N : ℝ) / X := div_nonneg (by positivity) hXpos.le
  have hratio1 : (N : ℝ) / X ≤ 1 := (div_le_one hXpos).2 hNX
  have hC : 0 ≤ Real.log 4 + 5 := by positivity
  calc
    |((N : ℝ) / X) * criticalMellinChebyshevResolventSource (Real.log N) + T / X| ≤
        |((N : ℝ) / X) * criticalMellinChebyshevResolventSource (Real.log N)| +
          |T / X| := abs_add_le _ _
    _ = ((N : ℝ) / X) *
          |criticalMellinChebyshevResolventSource (Real.log N)| + |T| / X := by
      rw [abs_mul, abs_of_nonneg hratio0, abs_div, abs_of_pos hXpos]
    _ ≤ |criticalMellinChebyshevResolventSource (Real.log N)| +
          ((Real.log 4 + 5) * X) / X := by
      gcongr
      simpa only [one_mul] using
        (mul_le_mul_of_nonneg_right hratio1
          (abs_nonneg (criticalMellinChebyshevResolventSource (Real.log N))))
    _ = |criticalMellinChebyshevResolventSource (Real.log N)| +
          (Real.log 4 + 5) := by field_simp

/-- Uniform control on integer logarithmic apertures propagates to every real aperture. -/
theorem abs_criticalMellinChebyshevResolventSource_le_of_log_nat_bound
    {B t : ℝ}
    (hB : ∀ N : ℕ, 2 ≤ N →
      |criticalMellinChebyshevResolventSource (Real.log N)| ≤ B)
    (ht : Real.log 2 ≤ t) :
    |criticalMellinChebyshevResolventSource t| ≤ B + (Real.log 4 + 5) := by
  let X : ℝ := Real.exp t
  let N : ℕ := ⌊X⌋₊
  have htwo : (0 : ℝ) < 2 := by norm_num
  have hX2 : (2 : ℝ) ≤ X := by
    rw [show (2 : ℝ) = Real.exp (Real.log 2) by rw [Real.exp_log htwo]]
    exact Real.exp_le_exp.mpr ht
  have hX0 : 0 ≤ X := (Real.exp_pos t).le
  have hN : 2 ≤ N := Nat.le_floor hX2
  have hNX : (N : ℝ) ≤ X := Nat.floor_le hX0
  have hXN : X ≤ (N : ℝ) + 1 := (Nat.lt_floor_add_one X).le
  have hcell := abs_criticalMellinChebyshevResolventSource_log_le_nat_add hN hNX hXN
  have hlogX : Real.log X = t := by
    dsimp only [X]
    exact Real.log_exp t
  rw [hlogX] at hcell
  exact hcell.trans (add_le_add (hB N hN) le_rfl)

/-- All-integer pole domination of literal outgoing HG block gives a continuous-aperture bound.
This is no-loss logarithmic-lattice handoff. -/
theorem abs_criticalMellinChebyshevResolventSource_le_of_outgoingProfile_le_pole
    (hdom : ∀ N : ℕ, 2 ≤ N → ∀ u : ℝ, 0 < u →
      boundaryRelativeTrace (unitRieszCoherentCompletedOutgoingProfile N) u ≤
        boundaryRelativeTrace polePacketProfile u)
    {t : ℝ} (ht : Real.log 2 ≤ t) :
    |criticalMellinChebyshevResolventSource t| ≤
      4 + (Real.log 4 + 5) := by
  apply abs_criticalMellinChebyshevResolventSource_le_of_log_nat_bound
    (B := 4) (t := t) ?_ ht
  intro N hN
  have hsquare :=
    (unitRieszCoherentCompletedOutgoingProfile_le_pole_iff hN).mp (hdom N hN)
  rw [abs_le]
  constructor <;> nlinarith

end GaloisForLFunctions.RHTower
