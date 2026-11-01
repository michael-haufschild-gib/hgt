import GaloisForLFunctions.AdelicKreinGeometry.TowerCoupling.InterTowerCouplingRigidity
import GaloisForLFunctions.AdelicKreinGeometry.EveryPlaceCarriesAPoleSuccessorState
import GaloisForLFunctions.AdelicKreinGeometry.RealPadicApproximation

/-!
# Every p-adic neighborhood carries the whole Weil index

Weak approximation makes every rational p-adic principal-unit group dense
in positive real slopes. Its logarithms therefore retain every spectral
negative square of Weil's correlation. Localizing the dilation variable
at a finite place does not reduce the off-critical zero count.
-/

open Complex Filter Topology
open GaloisForLFunctions.HTGeometry GaloisForLFunctions.HeckeKreinToeplitz
open GaloisForLFunctions.ArithmeticPositiveDuality

noncomputable section

namespace GaloisForLFunctions.AdelicKreinGeometry

variable (p : ℕ) [Fact p.Prime]

/-- Positive rational slopes in a p-adic principal-unit neighborhood. -/
def padicPrincipalUnits (n : ℕ) : Subgroup posUnits where
  carrier := {u | Rat.AbsoluteValue.padic p ((u : ℚˣ) : ℚ) = 1 ∧
    Rat.AbsoluteValue.padic p (((u : ℚˣ) : ℚ) - 1) < ((n : ℝ) + 1)⁻¹}
  one_mem' := by
    change Rat.AbsoluteValue.padic p (1 : ℚ) = 1 ∧
      Rat.AbsoluteValue.padic p ((1 : ℚ) - 1) < ((n : ℝ) + 1)⁻¹
    simp only [map_one, sub_self, map_zero, true_and]
    positivity
  mul_mem' {u v} hu hv := by
    change Rat.AbsoluteValue.padic p (((u : ℚˣ) : ℚ) * ((v : ℚˣ) : ℚ)) = 1 ∧ _
    constructor
    · rw [map_mul, hu.1, hv.1, mul_one]
    · change Rat.AbsoluteValue.padic p (((u : ℚˣ) : ℚ) * ((v : ℚˣ) : ℚ) - 1) < _
      rw [show ((u : ℚˣ) : ℚ) * ((v : ℚˣ) : ℚ) - 1 =
        (((u : ℚˣ) : ℚ) - 1) * ((v : ℚˣ) : ℚ) + (((v : ℚˣ) : ℚ) - 1) by ring]
      apply (isUltra_padic p _ _).trans_lt
      rw [map_mul, hv.1, mul_one]
      exact max_lt hu.2 hv.2
  inv_mem' {u} hu := by
    simp only [Set.mem_setOf_eq, Subgroup.coe_inv, Units.val_inv_eq_inv_val]
    constructor
    · rw [map_inv₀, hu.1, inv_one]
    · change Rat.AbsoluteValue.padic p (((u : ℚˣ) : ℚ)⁻¹ - 1) < _
      rw [show ((u : ℚˣ) : ℚ)⁻¹ - 1 =
        -((((u : ℚˣ) : ℚ) - 1) / ((u : ℚˣ) : ℚ)) by
          field_simp [Units.ne_zero (u : ℚˣ)]; ring]
      rw [map_neg_eq_map, map_div₀, hu.1, div_one]
      exact hu.2

private theorem padic_eq_one_of_near_one {q : ℚ}
    (hq : Rat.AbsoluteValue.padic p (q - 1) < 1) : Rat.AbsoluteValue.padic p q = 1 := by
  have hupper : Rat.AbsoluteValue.padic p q ≤ 1 := by
    have h := isUltra_padic p (q - 1) 1
    rw [sub_add_cancel, map_one] at h
    exact h.trans (max_le hq.le le_rfl)
  apply le_antisymm hupper
  by_contra h
  have hlower := isUltra_padic p (1 - q) q
  rw [sub_add_cancel, map_one, show 1 - q = -(q - 1) by ring,
    map_neg_eq_map] at hlower
  exact (not_lt_of_ge hlower) (max_lt hq (lt_of_not_ge h))

/-- Every p-adic principal-unit group is dense in the positive real slopes. -/
theorem exists_padicPrincipalUnit_near (n : ℕ) {x δ : ℝ} (hx : 0 < x) (hδ : 0 < δ) :
    ∃ u : padicPrincipalUnits p n, |((((u : posUnits) : ℚˣ) : ℚ) : ℝ) - x| < δ := by
  obtain ⟨q, hq, hp⟩ := LocalApproximation.exists_rat_near_real p x 1
    (lt_min hδ hx) (lt_min (by positivity : 0 < ((n : ℝ) + 1)⁻¹) zero_lt_one)
  have hpos : 0 < q := by
    have h := (abs_lt.mp (hq.trans_le (min_le_right _ _))).1
    have : (0 : ℝ) < q := by linarith
    exact_mod_cast this
  let u : posUnits := ⟨Units.mk0 q hpos.ne', hpos⟩
  have hu : u ∈ padicPrincipalUnits p n :=
    ⟨padic_eq_one_of_near_one p (hp.trans_le (min_le_right _ _)),
      hp.trans_le (min_le_left _ _)⟩
  exact ⟨⟨u, hu⟩, hq.trans_le (min_le_left _ _)⟩

/-- Principal units approximate every real logarithmic scale at every p-adic resolution. -/
theorem exists_padicPrincipalUnit_log_near (n : ℕ) (t : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∃ u : padicPrincipalUnits p n, |logPos (u : posUnits) - t| < ε := by
  obtain ⟨δ, hδ, hlog⟩ := Metric.continuousAt_iff.mp
    (Real.continuousAt_log (Real.exp_ne_zero t)) ε hε
  obtain ⟨u, hu⟩ := exists_padicPrincipalUnit_near p n (Real.exp_pos t) hδ
  refine ⟨u, ?_⟩
  have h := hlog (show dist (((((u : posUnits) : ℚˣ) : ℚ)) : ℝ) (Real.exp t) < δ by
    simpa only [Real.dist_eq] using hu)
  simpa only [Real.log_exp, Real.dist_eq, logPos] using h

/-- Every p-adic principal-unit group carries the full Weil negative index. -/
theorem negIndex_ratCorr_padicPrincipalUnits (n : ℕ) :
    negIndex (ratCorr ∘ (padicPrincipalUnits p n).subtype) = negIndex ratCorr := by
  let φ := posUnitsToHecke.comp (padicPrincipalUnits p n).subtype
  have hD : ArithmeticCastelnuovoSeveri.DenseShifts
      (Set.range fun u => scale heckeLogScale (φ u)) := by
    intro t _ ε hε
    obtain ⟨u, hu⟩ := exists_padicPrincipalUnit_log_near p n t hε
    exact ⟨logPos (u : posUnits), ⟨u, rfl⟩, hu⟩
  have h := negIndex_orbitKernel_comp Zeta23.zetaZeroConfig
    SquareRootThreshold.temperedConfig_zetaZeroConfig
    cubicSpline_mem_realTests φ hD
  have he : ratCorr ∘ (padicPrincipalUnits p n).subtype =
      orbitKernel Zeta23.zetaZeroConfig BiScaleUncertainty.ChebyshevGauge.cubicSpline ∘ φ := by
    funext u
    exact ratCorr_eq_zetaKernel u
  rw [he, h, negIndex_ratCorr, negIndex_zetaKernel,
    ArithmeticOrientationGeometry.seenRightZeros_cubicSpline]
  rfl

/-- Every principal-unit neighborhood approximates every global correlation value. -/
theorem exists_padicPrincipalUnit_ratCorr_near (n : ℕ) (u : posUnits)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ v : padicPrincipalUnits p n, ‖ratCorr v - ratCorr u‖ < ε := by
  have hc : Continuous (fun t : ℝ => splineCorr (-t)) :=
    TowerCoupling.continuous_splineCorr.comp continuous_neg
  obtain ⟨δ, hδ, hclose⟩ := Metric.continuousAt_iff.mp (hc.continuousAt (x := logPos u)) ε hε
  obtain ⟨v, hv⟩ := exists_padicPrincipalUnit_log_near p n (logPos u) hδ
  refine ⟨v, ?_⟩
  simpa only [dist_eq_norm, ratCorr] using
    hclose (by simpa only [Real.dist_eq] using hv)

/-- Weil's correlation is nonconstant, witnessed by its nonzero coprime mixed difference. -/
theorem exists_ratCorr_ne_identity : ∃ u : posUnits, ratCorr u ≠ ratCorr 1 := by
  by_contra h
  push Not at h
  obtain ⟨u, _, v, _, huv⟩ := TowerCoupling.exists_coprimeCrossDiff_ratCorr_ne_zero
  apply huv
  simp only [TowerCoupling.coprimeCrossDiff, h]
  ring

/-- A fixed positive oscillation persists at every p-adic resolution. -/
theorem exists_uniform_padic_ratCorr_oscillation :
    ∃ ε : ℝ, 0 < ε ∧ ∀ n : ℕ, ∃ u : padicPrincipalUnits p n,
      ε ≤ ‖ratCorr u - ratCorr 1‖ := by
  obtain ⟨v, hv⟩ := exists_ratCorr_ne_identity
  have hpos : 0 < ‖ratCorr v - ratCorr 1‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hv)
  refine ⟨‖ratCorr v - ratCorr 1‖ / 2, half_pos hpos, fun n => ?_⟩
  obtain ⟨u, hu⟩ := exists_padicPrincipalUnit_ratCorr_near p n v (half_pos hpos)
  refine ⟨u, ?_⟩
  have htri := norm_add_le (ratCorr v - ratCorr u) (ratCorr u - ratCorr 1)
  rw [sub_add_sub_cancel] at htri
  rw [norm_sub_rev (ratCorr v) (ratCorr u)] at htri
  linarith only [htri, hu]

/-- The real Weil correlation has no p-adic modulus of continuity at the identity. -/
theorem not_padic_continuous_ratCorr :
    ¬ (∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ u : posUnits,
      Rat.AbsoluteValue.padic p (((u : ℚˣ) : ℚ) - 1) < δ →
        ‖ratCorr u - ratCorr 1‖ < ε) := by
  intro hc
  obtain ⟨ε, hε, hosc⟩ := exists_uniform_padic_ratCorr_oscillation p
  obtain ⟨δ, hδ, hmod⟩ := hc ε hε
  obtain ⟨n, hn⟩ := exists_nat_one_div_lt hδ
  obtain ⟨u, hu⟩ := hosc n
  have hsmall : Rat.AbsoluteValue.padic p ((((u : posUnits) : ℚˣ) : ℚ) - 1) < δ :=
    u.2.2.trans (by simpa only [one_div] using hn)
  exact (not_lt_of_ge hu) (hmod u hsmall)

end GaloisForLFunctions.AdelicKreinGeometry
