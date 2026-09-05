import GaloisForLFunctions.RHTower.MobiusLaplaceGammaHankelWall

/-!
Finite coefficient damping in the actual Gamma--Hankel energy.
Paper proof: every frequency overlaps the first one. On a pair (0,k), fixing
the first coefficient cancels its quadratic term in the contraction inequality.
The remaining affine function of that coefficient is bounded for all real
values only if the multiplier at k is also one. Conversely identity contracts.
For the actual Mobius prefix (1,-1), replacing -1 by -q, 0<=q<1,
increases energy by Gamma(r)(1-q)(2/3^r-(1+q)/4^r)>0.
This is a bridge to peripheral contraction rigidity, not a new RH mechanism.
-/

open scoped BigOperators
namespace RHTower
noncomputable section

private def anchoredPair (k : ℕ) (a b : ℝ) (n : ℕ) : ℝ :=
  (if n = 0 then a else 0) + (if n = k then b else 0)

private theorem sum_anchoredPair_mul (k : ℕ) (a b : ℝ) (f : ℕ → ℝ) :
    (∑ n ∈ Finset.range (k+1), anchoredPair k a b n * f n) =
      a * f 0 + b * f k := by
  simp [anchoredPair, add_mul, Finset.sum_add_distrib, ite_mul]

private theorem anchoredPair_energy (k : ℕ) (a b r : ℝ) :
    finiteGammaHankelEnergy (anchoredPair k a b) (k+1) r =
      Real.Gamma r * (a^2 / (2:ℝ)^r +
        2*a*b / ((k+2:ℕ):ℝ)^r + b^2 / ((k+k+2:ℕ):ℝ)^r) := by
  unfold finiteGammaHankelEnergy
  have hinner (m : ℕ) :
      (∑ n ∈ Finset.range (k+1), anchoredPair k a b m * anchoredPair k a b n /
        ((m+n+2:ℕ):ℝ)^r) = anchoredPair k a b m *
          (a / ((m+2:ℕ):ℝ)^r + b / ((m+k+2:ℕ):ℝ)^r) := by
    simp_rw [mul_div_assoc, div_eq_mul_inv, ← Finset.mul_sum]
    rw [sum_anchoredPair_mul]
  simp_rw [hinner]
  rw [sum_anchoredPair_mul]
  simp only [Nat.zero_add, Nat.cast_ofNat]
  ring

/-- The coefficientwise multiplier is contractive on every finite real source section. -/
def GammaHankelDiagonalContractive (r : ℝ) (w : ℕ → ℝ) : Prop :=
  ∀ (a : ℕ → ℝ) (N : ℕ),
    finiteGammaHankelEnergy (fun n => w n * a n) N r ≤ finiteGammaHankelEnergy a N r

/-- Fixing the first integer leaves no nontrivial diagonal contraction. -/
theorem gammaHankel_unital_diagonal_contractive_iff {r : ℝ} (hr : 0 < r)
    (w : ℕ → ℝ) (hw : w 0 = 1) :
    GammaHankelDiagonalContractive r w ↔ ∀ n, w n = 1 := by
  constructor
  · intro h k
    by_cases hk : k = 0
    · simpa [hk] using hw
    by_contra hne
    have hgamma := Real.Gamma_pos_of_pos hr
    have hd : ((k+2:ℕ):ℝ)^r ≠ 0 := ne_of_gt (Real.rpow_pos_of_pos (by positivity) r)
    have he : ((k+k+2:ℕ):ℝ)^r ≠ 0 := ne_of_gt (Real.rpow_pos_of_pos (by positivity) r)
    let a := ((k+2:ℕ):ℝ)^r * (1 - (w k ^ 2 - 1) / ((k+k+2:ℕ):ℝ)^r) /
      (2*(w k-1))
    have hmul : (fun n => w n * anchoredPair k a 1 n) = anchoredPair k a (w k) := by
      funext n
      by_cases hn0 : n = 0
      · subst n
        simp [anchoredPair, hw, Ne.symm hk]
      by_cases hnk : n = k
      · subst n
        simp [anchoredPair, hk]
      · simp [anchoredPair, hn0, hnk]
    have hb := h (anchoredPair k a 1) (k+1)
    rw [hmul, anchoredPair_energy, anchoredPair_energy] at hb
    have hb' := (mul_le_mul_iff_right₀ hgamma).mp hb
    have heq : 2*a*(w k-1) / ((k+2:ℕ):ℝ)^r +
        (w k^2-1) / ((k+k+2:ℕ):ℝ)^r = 1 := by
      dsimp [a]
      field_simp [hd, he, sub_ne_zero.mpr hne]
      ring
    have hbase : 2*a*(w k-1) / ((k+2:ℕ):ℝ)^r +
        (w k^2-1) / ((k+k+2:ℕ):ℝ)^r ≤ 0 := by
      calc
        _ = (a^2/(2:ℝ)^r + 2*a*w k/((k+2:ℕ):ℝ)^r + w k^2/((k+k+2:ℕ):ℝ)^r) -
            (a^2/(2:ℝ)^r + 2*a*1/((k+2:ℕ):ℝ)^r + 1^2/((k+k+2:ℕ):ℝ)^r) := by ring
        _ ≤ 0 := sub_nonpos.mpr hb'
    linarith
  · intro h a N
    simp only [h, one_mul]
    exact le_rfl

private theorem shiftedMobius_zero : shiftedMobiusRealCoefficient 0 = 1 := by
  simp [shiftedMobiusRealCoefficient]

private theorem shiftedMobius_one : shiftedMobiusRealCoefficient 1 = -1 := by
  norm_num [shiftedMobiusRealCoefficient, ArithmeticFunction.moebius_apply_prime Nat.prime_two]

/-- Explicit two-integer expansion for arbitrary real coefficients. -/
theorem finiteGammaHankelEnergy_two (a : ℕ → ℝ) (r : ℝ) :
    finiteGammaHankelEnergy a 2 r = Real.Gamma r *
      (a 0 ^ 2 / (2:ℝ)^r + 2*a 0*a 1 / (3:ℝ)^r + a 1 ^ 2 / (4:ℝ)^r) := by
  simp only [finiteGammaHankelEnergy, Finset.sum_range_succ, Finset.sum_range_zero,
    zero_add, Nat.cast_ofNat]
  ring

/-- Decreasing the second Mobius magnitude destroys some cancellation and strictly raises energy. -/
theorem mobius_two_coefficient_damping_increases_energy {r q : ℝ}
    (hr : 0 < r) (hq1 : q < 1) :
    finiteMobiusGammaHankelEnergy 2 r <
      finiteGammaHankelEnergy (fun n => if n = 0 then 1 else -q) 2 r := by
  have h3 := Real.rpow_pos_of_pos (by norm_num : (0:ℝ)<3) r
  have h4 := Real.rpow_pos_of_pos (by norm_num : (0:ℝ)<4) r
  have h34 : (3:ℝ)^r < (4:ℝ)^r := Real.rpow_lt_rpow (by norm_num) (by norm_num) hr
  have hkernel : 0 < 2/(3:ℝ)^r - (1+q)/(4:ℝ)^r := by
    have hrec : 2/(4:ℝ)^r < 2/(3:ℝ)^r := div_lt_div_of_pos_left (by norm_num) h3 h34
    have hq : (1+q)/(4:ℝ)^r ≤ 2/(4:ℝ)^r :=
      div_le_div_of_nonneg_right (by linarith) h4.le
    linarith
  rw [finiteMobiusGammaHankelEnergy, finiteGammaHankelEnergy_two, finiteGammaHankelEnergy_two,
    shiftedMobius_zero, shiftedMobius_one]
  simp only [ite_true, Nat.one_ne_zero, if_false]
  apply (mul_lt_mul_iff_right₀ (Real.Gamma_pos_of_pos hr)).mpr
  have hpos := mul_pos (sub_pos.mpr hq1) hkernel
  apply sub_pos.mp
  calc
    _ = (1-q)*(2/(3:ℝ)^r-(1+q)/(4:ℝ)^r) := by ring
    _ > 0 := hpos

/-- Literal unsquared Mobius coefficients after Dirichlet-power damping. -/
def mobiusDirichletDampedCoefficient (t : ℝ) (n : ℕ) : ℝ :=
  shiftedMobiusRealCoefficient n * ((n+1:ℕ):ℝ)^(-t)

/-- Positive Dirichlet damping is expansive already on the actual first two integers. -/
theorem mobius_dirichlet_damping_two_energy_gt {r t : ℝ}
    (hr : 0 < r) (ht : 0 < t) :
    finiteMobiusGammaHankelEnergy 2 r <
      finiteGammaHankelEnergy (mobiusDirichletDampedCoefficient t) 2 r := by
  have hq : (2:ℝ)^(-t) < 1 := by
    rw [← Real.rpow_zero (2:ℝ)]
    exact Real.rpow_lt_rpow_of_exponent_lt (by norm_num) (by linarith)
  have h := mobius_two_coefficient_damping_increases_energy hr hq
  rw [finiteGammaHankelEnergy_two] at h ⊢
  simpa [mobiusDirichletDampedCoefficient, shiftedMobius_zero, shiftedMobius_one] using h

end
end RHTower
