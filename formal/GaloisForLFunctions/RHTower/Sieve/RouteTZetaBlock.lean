import GaloisForLFunctions.RHTower.Sieve.MontgomeryVaughanArbitraryLogPhaseReceiver
import GaloisForLFunctions.RHTower.Sieve.TwistTransfer
import GaloisForLFunctions.RHTower.Sieve.ZetaPartialSumTruncation

/-!
# Route-T bounds for actual zeta blocks

The receiver is written with the positive logarithmic phase.  Zeta contains `n^{-it}`.  Exact
complex-power and conjugation identities transfer the norm bound with no sign loss.
-/

namespace RHTower.Sieve

open scoped ComplexConjugate

noncomputable section

def routeTZetaBlockSum (X X' : ℕ) (σ t : ℝ) : ℂ :=
  ∑ n ∈ Finset.Ioc X X',
    (((n : ℕ) : ℂ) ^ (-((σ : ℂ) + Complex.I * (t : ℂ))))

theorem routeTLogPhase_eq_exp (t : ℝ) (n : ℕ) :
    routeTLogPhase t n =
      Complex.exp (((t * Real.log n : ℝ) : ℂ) * Complex.I) := by
  unfold routeTLogPhase finitePhaseChar
  congr 1
  push_cast
  field_simp [Real.pi_ne_zero]

theorem routeTLogPhase_neg (t : ℝ) (n : ℕ) :
    routeTLogPhase (-t) n = conj (routeTLogPhase t n) := by
  unfold routeTLogPhase
  rw [show -t / (2 * Real.pi) * Real.log n =
      -(t / (2 * Real.pi) * Real.log n) by ring, finitePhaseChar_neg]

theorem natCast_cpow_neg_sigma_add_it_eq_routeTWeight
    {n : ℕ} (hn : 1 ≤ n) (σ t : ℝ) :
    (((n : ℕ) : ℂ) ^ (-((σ : ℂ) + Complex.I * (t : ℂ)))) =
      ((((n : ℕ) : ℝ) ^ (-σ) : ℝ) : ℂ) * routeTLogPhase (-t) n := by
  have hn0 : ((n : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hexponent : -((σ : ℂ) + Complex.I * (t : ℂ)) =
      ((-σ : ℝ) : ℂ) + ((-t : ℝ) : ℂ) * Complex.I := by
    push_cast
    ring
  rw [hexponent, Complex.cpow_add _ _ hn0]
  rw [natCast_cpow_mul_I (-t) hn]
  rw [routeTLogPhase_eq_exp]
  rw [show ((n : ℕ) : ℂ) = (((n : ℕ) : ℝ) : ℂ) by norm_cast,
    ← Complex.ofReal_cpow (Nat.cast_nonneg n) (-σ)]

theorem routeTZetaBlockSum_eq_weighted_negative
    {X X' : ℕ} (hX : 1 ≤ X) (σ t : ℝ) :
    routeTZetaBlockSum X X' σ t =
      routeTLogArbitraryWeightedPartialSum X X' σ (-t) := by
  unfold routeTZetaBlockSum routeTLogArbitraryWeightedPartialSum
  apply Finset.sum_congr rfl
  intro n hn
  exact natCast_cpow_neg_sigma_add_it_eq_routeTWeight (by
    have := (Finset.mem_Ioc.mp hn).1
    omega) σ t

theorem norm_routeTLogArbitraryWeightedPartialSum_neg
    (X X' : ℕ) (σ t : ℝ) :
    ‖routeTLogArbitraryWeightedPartialSum X X' σ (-t)‖ =
      ‖routeTLogArbitraryWeightedPartialSum X X' σ t‖ := by
  have hsum : routeTLogArbitraryWeightedPartialSum X X' σ (-t) =
      conj (routeTLogArbitraryWeightedPartialSum X X' σ t) := by
    unfold routeTLogArbitraryWeightedPartialSum
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro n _hn
    rw [map_mul, routeTLogPhase_neg]
    simp only [Complex.conj_ofReal]
  rw [hsum]
  exact RCLike.norm_conj _

theorem norm_routeTZetaBlockSum_eq_weighted
    {X X' : ℕ} (hX : 1 ≤ X) (σ t : ℝ) :
    ‖routeTZetaBlockSum X X' σ t‖ =
      ‖routeTLogArbitraryWeightedPartialSum X X' σ t‖ := by
  rw [routeTZetaBlockSum_eq_weighted_negative hX]
  exact norm_routeTLogArbitraryWeightedPartialSum_neg X X' σ t

theorem norm_routeTZetaBlockSum_le_explicitQuarticSaving
    {X X' v : ℕ} {σ t : ℝ}
    (hX : 1 ≤ X)
    (hXsize : 2 ^ (routeTLogCentreExponent *
        (routeTLogReceiverDegreeNineConstant *
          (routeTLogRealShellIndex X t + 1) ^ 9 + 1)) ≤ X)
    (hlarge : (((routeTLogRootBase X ^ routeTLogCentreExponent) ^
      (4 * 141) : ℕ) : ℝ) < t)
    (htop : t ≤ (((routeTLogRootBase X ^ routeTLogCentreExponent) ^
      (4 * v) : ℕ) : ℝ))
    (hXX' : X < X') (hX' : X' ≤ 2 * X) (hσ : 0 ≤ σ) :
    ‖routeTZetaBlockSum X X' σ t‖ ≤
      (6912 * X *
        ((((routeTLogRootBase X ^ routeTLogCentreExponent : ℕ) : ℝ)) ^
          (-(1 / (5000000000000000 * (v : ℝ) ^ 4))))) *
        ((((X + 1 : ℕ) : ℝ)) ^ (-σ)) := by
  rw [norm_routeTZetaBlockSum_eq_weighted hX]
  exact norm_routeTLogArbitraryWeightedPartialSum_le_explicitQuarticSaving
    hXsize hlarge htop hXX' hX' hσ

theorem routeTLogRootCell_log_lower
    {X : ℕ} (hX : 1 ≤ X) (hB2 : 2 ≤ routeTLogRootBase X) :
    Real.log X - 200 * Real.log 2 ≤
      Real.log (routeTLogRootBase X ^ routeTLogCentreExponent) := by
  obtain ⟨_hlower, hupper⟩ := routeTLogRootBase_cell hB2
  let B0 := routeTLogRootBase X ^ routeTLogCentreExponent
  have hXpos : (0 : ℝ) < X := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hX)
  have hB0pos : (0 : ℝ) < B0 := by
    exact_mod_cast (pow_pos (by omega : 0 < routeTLogRootBase X)
      routeTLogCentreExponent)
  have hcast : (X : ℝ) ≤ (2 : ℝ) ^ 200 * B0 := by
    exact_mod_cast (by simpa only [B0] using hupper)
  have hlog := Real.log_le_log hXpos hcast
  rw [Real.log_mul (by positivity : (2 : ℝ) ^ 200 ≠ 0) hB0pos.ne',
    Real.log_pow] at hlog
  have h200 : ((200 : ℕ) : ℝ) = (200 : ℝ) := rfl
  have hresult : Real.log X - 200 * Real.log 2 ≤ Real.log B0 := by
    rw [h200] at hlog
    apply sub_le_iff_le_add.mpr
    simpa only [add_comm] using hlog
  rw [show ((B0 : ℕ) : ℝ) =
      ((routeTLogRootBase X : ℝ) ^ routeTLogCentreExponent) by
        simp only [B0, Nat.cast_pow]] at hresult
  exact hresult

theorem routeTLogRootDecay_le_exp
    {X v : ℕ} (hX : 1 ≤ X) (hB2 : 2 ≤ routeTLogRootBase X)
    (hv : 1 ≤ v) :
    ((((routeTLogRootBase X ^ routeTLogCentreExponent : ℕ) : ℝ)) ^
        (-(1 / (5000000000000000 * (v : ℝ) ^ 4)))) ≤
      Real.exp (-(1 / (5000000000000000 * (v : ℝ) ^ 4)) *
        (Real.log X - 200 * Real.log 2)) := by
  let B0 := routeTLogRootBase X ^ routeTLogCentreExponent
  let a : ℝ := 1 / (5000000000000000 * (v : ℝ) ^ 4)
  have hB0pos : (0 : ℝ) < B0 := by
    exact_mod_cast (pow_pos (by omega : 0 < routeTLogRootBase X)
      routeTLogCentreExponent)
  have ha : 0 < a := by
    unfold a
    have : (0 : ℝ) < v := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hv)
    positivity
  have hlog := routeTLogRootCell_log_lower hX hB2
  rw [Real.rpow_def_of_pos hB0pos (-a)]
  apply Real.exp_le_exp.2
  dsimp only [B0, a] at hlog ⊢
  have hcoeff : -(1 / (5000000000000000 * (v : ℝ) ^ 4)) ≤ 0 := by
    exact neg_nonpos.mpr (by positivity)
  have hmul := mul_le_mul_of_nonpos_left hlog hcoeff
  simpa only [Nat.cast_pow, mul_comm] using hmul

theorem routeTZetaWeightFront_le_exp
    {X : ℕ} (hX : 1 ≤ X) {σ : ℝ} (_hσ : 0 ≤ σ) :
    (X : ℝ) * (((X + 1 : ℕ) : ℝ) ^ (-σ)) ≤
      Real.exp ((1 - σ) * Real.log (X + 1)) := by
  have hXp : (0 : ℝ) < (X + 1 : ℕ) := by positivity
  have hweight : 0 ≤ (((X + 1 : ℕ) : ℝ) ^ (-σ)) := Real.rpow_nonneg hXp.le _
  calc
    (X : ℝ) * (((X + 1 : ℕ) : ℝ) ^ (-σ)) ≤
        ((X + 1 : ℕ) : ℝ) * (((X + 1 : ℕ) : ℝ) ^ (-σ)) := by
      gcongr
      exact_mod_cast (Nat.le_succ X)
    _ = (((X + 1 : ℕ) : ℝ) ^ (1 - σ)) := by
      calc
        ((X + 1 : ℕ) : ℝ) * (((X + 1 : ℕ) : ℝ) ^ (-σ)) =
            (((X + 1 : ℕ) : ℝ) ^ (1 : ℝ)) *
              (((X + 1 : ℕ) : ℝ) ^ (-σ)) := by rw [Real.rpow_one]
        _ = (((X + 1 : ℕ) : ℝ) ^ ((1 : ℝ) + (-σ))) :=
          (Real.rpow_add hXp _ _).symm
        _ = (((X + 1 : ℕ) : ℝ) ^ (1 - σ)) := by ring_nf
    _ = Real.exp ((1 - σ) * Real.log (X + 1)) := by
      rw [Real.rpow_def_of_pos hXp]
      congr 1
      push_cast
      ring

/-- Exponential form consumed by zeta growth optimization. -/
theorem norm_routeTZetaBlockSum_le_explicitExponential
    {X X' v : ℕ} {σ t : ℝ}
    (hX : 1 ≤ X)
    (hXsize : 2 ^ (routeTLogCentreExponent *
        (routeTLogReceiverDegreeNineConstant *
          (routeTLogRealShellIndex X t + 1) ^ 9 + 1)) ≤ X)
    (hlarge : (((routeTLogRootBase X ^ routeTLogCentreExponent) ^
      (4 * 141) : ℕ) : ℝ) < t)
    (htop : t ≤ (((routeTLogRootBase X ^ routeTLogCentreExponent) ^
      (4 * v) : ℕ) : ℝ))
    (hXX' : X < X') (hX' : X' ≤ 2 * X) (hσ : 0 ≤ σ) :
    ‖routeTZetaBlockSum X X' σ t‖ ≤
      6912 * Real.exp ((1 - σ) * Real.log (X + 1) -
        (1 / (5000000000000000 * (v : ℝ) ^ 4)) *
          (Real.log X - 200 * Real.log 2)) := by
  have hB2 := routeTLogRootBase_ge_two_of_degreeNine_size hXsize
  have hu : 141 < routeTLogRealShellIndex X t :=
    routeTLogRealShellIndex_ge hB2 hlarge
  have hv : 1 ≤ v := by
    have huv := routeTLogRealShellIndex_le htop
    omega
  have hraw := norm_routeTZetaBlockSum_le_explicitQuarticSaving
    hX hXsize hlarge htop hXX' hX' hσ
  have hfront := routeTZetaWeightFront_le_exp hX hσ
  have hdecay := routeTLogRootDecay_le_exp hX hB2 hv
  calc
    ‖routeTZetaBlockSum X X' σ t‖ ≤
        (6912 * X *
          ((((routeTLogRootBase X ^ routeTLogCentreExponent : ℕ) : ℝ)) ^
            (-(1 / (5000000000000000 * (v : ℝ) ^ 4))))) *
          ((((X + 1 : ℕ) : ℝ)) ^ (-σ)) := hraw
    _ = 6912 *
        ((X : ℝ) * ((((X + 1 : ℕ) : ℝ)) ^ (-σ))) *
        ((((routeTLogRootBase X ^ routeTLogCentreExponent : ℕ) : ℝ)) ^
          (-(1 / (5000000000000000 * (v : ℝ) ^ 4)))) := by ring
    _ ≤ 6912 * Real.exp ((1 - σ) * Real.log (X + 1)) *
        Real.exp (-(1 / (5000000000000000 * (v : ℝ) ^ 4)) *
          (Real.log X - 200 * Real.log 2)) := by gcongr
    _ = 6912 * Real.exp ((1 - σ) * Real.log (X + 1) -
        (1 / (5000000000000000 * (v : ℝ) ^ 4)) *
          (Real.log X - 200 * Real.log 2)) := by
      rw [mul_assoc, ← Real.exp_add]
      congr 2
      ring

end

end RHTower.Sieve
