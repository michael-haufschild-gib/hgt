import GaloisForLFunctions.RHTower.GaussOnePrimeCriticalResidue

/-!
# One-prime quasi-inner residue rigidity

This module isolates the arithmetic residue scale occurring in the explicit depth-one Gauss
critical model and proves that it determines its real scale parameter on `(1, ∞)`.  In
particular, equality of the explicit residues attached to two primes forces equality of the
primes.  The proof is algebraic and logarithmic: it factors the residue into two positive,
strictly increasing terms.
-/

open Filter Topology Set

namespace RHTower

noncomputable section

/-- Real interpolation of the explicit depth-one Gauss critical residue. -/
def primeQuasiInnerResidueScale (q : ℝ) : ℝ :=
  2 * (q - 1) ^ (4 : ℕ) / (q ^ (2 : ℕ) * Real.log q)

/-- At a prime, the interpolated scale is exactly the depth-one Gauss-channel residue. -/
theorem primeQuasiInnerResidueScale_prime (p : Nat.Primes) :
    primeQuasiInnerResidueScale p =
      GaloisForLFunctions.RHTower.gaussChannelResidue 1 p := by
  rw [gaussChannelResidue_one]
  rfl

/-- The residue scale is positive above the singular endpoint `q = 1`. -/
theorem primeQuasiInnerResidueScale_pos {q : ℝ} (hq : 1 < q) :
    0 < primeQuasiInnerResidueScale q := by
  unfold primeQuasiInnerResidueScale
  exact div_pos
    (mul_pos (by norm_num) (pow_pos (sub_pos.mpr hq) 4))
    (mul_pos (pow_pos (zero_lt_one.trans hq) 2) (Real.log_pos hq))

/-- Algebraic factor in the residue-scale factorization. -/
def primeQuasiInnerAlgebraicFactor (q : ℝ) : ℝ :=
  (q - 1) ^ (3 : ℕ) / q ^ (2 : ℕ)

/-- Logarithmic-mean factor in the residue-scale factorization. -/
def primeQuasiInnerLogMeanFactor (q : ℝ) : ℝ :=
  (q - 1) / Real.log q

/-- Strict lower tangent bound for the logarithm, in the quotient form needed below. -/
theorem primeQuasiInner_sub_div_lt_log {q : ℝ} (hq : 1 < q) :
    (q - 1) / q < Real.log q := by
  have hq0 : 0 < q := zero_lt_one.trans hq
  have hqInvNe : q⁻¹ ≠ 1 := by
    intro h
    have : q = 1 := by
      have hi := congrArg (fun x : ℝ => x⁻¹) h
      simpa [inv_inv] using hi
    exact (ne_of_gt hq) this
  have h := Real.log_lt_sub_one_of_pos (inv_pos.mpr hq0) hqInvNe
  rw [Real.log_inv] at h
  have hqne : q ≠ 0 := ne_of_gt hq0
  have hrewrite : q⁻¹ - 1 = -(q - 1) / q := by
    field_simp [hqne]
    ring
  rw [hrewrite] at h
  have h' : -Real.log q < -((q - 1) / q) := by
    simpa only [neg_div] using h
  exact neg_lt_neg_iff.mp h'

/-- Factorization into algebraic and logarithmic-mean terms. -/
theorem primeQuasiInnerResidueScale_factor (q : ℝ) :
    primeQuasiInnerResidueScale q =
      2 * primeQuasiInnerAlgebraicFactor q * primeQuasiInnerLogMeanFactor q := by
  unfold primeQuasiInnerResidueScale primeQuasiInnerAlgebraicFactor
    primeQuasiInnerLogMeanFactor
  ring

/-- The algebraic factor is strictly increasing above one. -/
theorem primeQuasiInnerAlgebraicFactor_strictMonoOn :
    StrictMonoOn primeQuasiInnerAlgebraicFactor (Set.Ioi 1) := by
  intro q hq r hr hqr
  have hq0 : 0 < q := zero_lt_one.trans hq
  have hr0 : 0 < r := zero_lt_one.trans hr
  have hunitq : 0 < 1 - q⁻¹ := by
    rw [sub_pos, inv_lt_one₀ hq0]
    exact hq
  have hunitr : 0 < 1 - r⁻¹ := by
    rw [sub_pos, inv_lt_one₀ hr0]
    exact hr
  have hinv : r⁻¹ < q⁻¹ := by
    exact (inv_lt_inv₀ hr0 hq0).2 hqr
  have hunit : 1 - q⁻¹ < 1 - r⁻¹ := by linarith
  have hsquare : (1 - q⁻¹) ^ (2 : ℕ) < (1 - r⁻¹) ^ (2 : ℕ) := by nlinarith
  have hsub : q - 1 < r - 1 := by linarith
  have hprod : (q - 1) * (1 - q⁻¹) ^ (2 : ℕ) < (r - 1) * (1 - r⁻¹) ^ (2 : ℕ) := by
    calc
      (q - 1) * (1 - q⁻¹) ^ (2 : ℕ) < (r - 1) * (1 - q⁻¹) ^ (2 : ℕ) :=
        mul_lt_mul_of_pos_right hsub (sq_pos_of_pos hunitq)
      _ < (r - 1) * (1 - r⁻¹) ^ (2 : ℕ) :=
        mul_lt_mul_of_pos_left hsquare (sub_pos.mpr hr)
  have hqne : q ≠ 0 := ne_of_gt hq0
  have hrne : r ≠ 0 := ne_of_gt hr0
  unfold primeQuasiInnerAlgebraicFactor
  rw [show (q - 1) ^ (3 : ℕ) / q ^ (2 : ℕ) = (q - 1) * (1 - q⁻¹) ^ (2 : ℕ) by field_simp [hqne],
    show (r - 1) ^ (3 : ℕ) / r ^ (2 : ℕ) = (r - 1) * (1 - r⁻¹) ^ (2 : ℕ) by field_simp [hrne]]
  exact hprod

/-- The logarithmic-mean factor is strictly increasing above one. -/
theorem primeQuasiInnerLogMeanFactor_strictMonoOn :
    StrictMonoOn primeQuasiInnerLogMeanFactor (Set.Ioi 1) := by
  intro q hq r hr hqr
  have hq0 : 0 < q := zero_lt_one.trans hq
  have hr0 : 0 < r := zero_lt_one.trans hr
  have hratio : 1 < r / q := (one_lt_div hq0).2 hqr
  have hratioNe : r / q ≠ 1 := ne_of_gt hratio
  have hlogRatio : Real.log (r / q) < r / q - 1 :=
    Real.log_lt_sub_one_of_pos (by positivity) hratioNe
  have hqLog := primeQuasiInner_sub_div_lt_log hq
  have hstep1 : (q - 1) * Real.log (r / q) <
      (q - 1) * ((r - q) / q) := by
    have hrewrite : r / q - 1 = (r - q) / q := by field_simp [ne_of_gt hq0]
    rw [hrewrite] at hlogRatio
    exact mul_lt_mul_of_pos_left hlogRatio (sub_pos.mpr hq)
  have hstep2 : (q - 1) * ((r - q) / q) < (r - q) * Real.log q := by
    have h := mul_lt_mul_of_pos_left hqLog (sub_pos.mpr hqr)
    calc
      (q - 1) * ((r - q) / q) = (r - q) * ((q - 1) / q) := by ring
      _ < (r - q) * Real.log q := h
  have hlogAdd : Real.log r = Real.log q + Real.log (r / q) := by
    rw [Real.log_div (ne_of_gt hr0) (ne_of_gt hq0)]
    ring
  have hcross : (q - 1) * Real.log r < (r - 1) * Real.log q := by
    rw [hlogAdd]
    nlinarith [hstep1.trans hstep2]
  unfold primeQuasiInnerLogMeanFactor
  rw [div_lt_div_iff₀ (Real.log_pos hq) (Real.log_pos hr)]
  exact hcross

/-- The explicit one-prime residue scale is strictly increasing above one. -/
theorem strictMonoOn_primeQuasiInnerResidueScale :
    StrictMonoOn primeQuasiInnerResidueScale (Set.Ioi 1) := by
  intro q hq r hr hqr
  rw [primeQuasiInnerResidueScale_factor, primeQuasiInnerResidueScale_factor]
  have hA := primeQuasiInnerAlgebraicFactor_strictMonoOn hq hr hqr
  have hB := primeQuasiInnerLogMeanFactor_strictMonoOn hq hr hqr
  have hAr : 0 < primeQuasiInnerAlgebraicFactor r := by
    unfold primeQuasiInnerAlgebraicFactor
    exact div_pos (pow_pos (sub_pos.mpr hr) 3) (pow_pos (zero_lt_one.trans hr) 2)
  have hBq : 0 < primeQuasiInnerLogMeanFactor q := by
    unfold primeQuasiInnerLogMeanFactor
    exact div_pos (sub_pos.mpr hq) (Real.log_pos hq)
  have hprod :
      primeQuasiInnerAlgebraicFactor q * primeQuasiInnerLogMeanFactor q <
        primeQuasiInnerAlgebraicFactor r * primeQuasiInnerLogMeanFactor r := by
    calc
      primeQuasiInnerAlgebraicFactor q * primeQuasiInnerLogMeanFactor q <
          primeQuasiInnerAlgebraicFactor r * primeQuasiInnerLogMeanFactor q :=
        mul_lt_mul_of_pos_right hA hBq
      _ < primeQuasiInnerAlgebraicFactor r * primeQuasiInnerLogMeanFactor r :=
        mul_lt_mul_of_pos_left hB hAr
  calc
    2 * primeQuasiInnerAlgebraicFactor q * primeQuasiInnerLogMeanFactor q =
        2 * (primeQuasiInnerAlgebraicFactor q * primeQuasiInnerLogMeanFactor q) := by ring
    _ < 2 * (primeQuasiInnerAlgebraicFactor r * primeQuasiInnerLogMeanFactor r) :=
      mul_lt_mul_of_pos_left hprod (by norm_num)
    _ = 2 * primeQuasiInnerAlgebraicFactor r * primeQuasiInnerLogMeanFactor r := by ring

/-- The explicit residue scale is injective on its natural domain. -/
theorem primeQuasiInnerResidueScale_injectiveOn :
    Set.InjOn primeQuasiInnerResidueScale (Set.Ioi 1) :=
  strictMonoOn_primeQuasiInnerResidueScale.injOn

/-- Equality of two residue scales above one is equivalent to equality of their parameters. -/
theorem primeQuasiInnerResidueScale_eq_iff {q r : ℝ} (hq : 1 < q) (hr : 1 < r) :
    primeQuasiInnerResidueScale q = primeQuasiInnerResidueScale r ↔ q = r := by
  constructor
  · exact fun h => primeQuasiInnerResidueScale_injectiveOn hq hr h
  · exact congrArg _

/-- A cubic upper bound controlling the residue at the endpoint `q = 1`. -/
theorem primeQuasiInnerResidueScale_upper {q : ℝ} (hq : 1 < q) :
    primeQuasiInnerResidueScale q ≤ 2 * (q - 1) ^ (3 : ℕ) / q := by
  have hq0 : 0 < q := zero_lt_one.trans hq
  have hB : primeQuasiInnerLogMeanFactor q ≤ q := by
    unfold primeQuasiInnerLogMeanFactor
    rw [div_le_iff₀ (Real.log_pos hq)]
    have hlog := primeQuasiInner_sub_div_lt_log hq
    have hcross := (div_lt_iff₀ hq0).mp hlog
    nlinarith
  have hA : 0 ≤ 2 * primeQuasiInnerAlgebraicFactor q := by
    unfold primeQuasiInnerAlgebraicFactor
    positivity
  rw [primeQuasiInnerResidueScale_factor]
  calc
    2 * primeQuasiInnerAlgebraicFactor q * primeQuasiInnerLogMeanFactor q ≤
        2 * primeQuasiInnerAlgebraicFactor q * q :=
      mul_le_mul_of_nonneg_left hB hA
    _ = 2 * (q - 1) ^ (3 : ℕ) / q := by
      unfold primeQuasiInnerAlgebraicFactor
      field_simp [ne_of_gt hq0]

/-- The algebraic factor alone is a lower bound for the residue scale. -/
theorem primeQuasiInnerResidueScale_lower {q : ℝ} (hq : 1 < q) :
    2 * primeQuasiInnerAlgebraicFactor q ≤ primeQuasiInnerResidueScale q := by
  have hB : 1 ≤ primeQuasiInnerLogMeanFactor q := by
    unfold primeQuasiInnerLogMeanFactor
    rw [le_div_iff₀ (Real.log_pos hq)]
    simpa only [one_mul] using
      (le_of_lt (Real.log_lt_sub_one_of_pos (zero_lt_one.trans hq) (ne_of_gt hq)))
  have hA : 0 ≤ 2 * primeQuasiInnerAlgebraicFactor q := by
    unfold primeQuasiInnerAlgebraicFactor
    positivity
  rw [primeQuasiInnerResidueScale_factor]
  calc
    2 * primeQuasiInnerAlgebraicFactor q =
        2 * primeQuasiInnerAlgebraicFactor q * 1 := by ring
    _ ≤ 2 * primeQuasiInnerAlgebraicFactor q * primeQuasiInnerLogMeanFactor q :=
      mul_le_mul_of_nonneg_left hB hA

/-- A linear lower bound forcing the residue scale to diverge at infinity. -/
theorem primeQuasiInnerResidueScale_linear_lower {q : ℝ} (hq : 1 < q) :
    q - 6 ≤ primeQuasiInnerResidueScale q := by
  have hq0 : 0 < q := zero_lt_one.trans hq
  calc
    q - 6 ≤ 2 * primeQuasiInnerAlgebraicFactor q := by
      unfold primeQuasiInnerAlgebraicFactor
      rw [show 2 * ((q - 1) ^ (3 : ℕ) / q ^ (2 : ℕ)) = (2 * (q - 1) ^ (3 : ℕ)) / q ^ (2 : ℕ) by ring]
      rw [le_div_iff₀ (sq_pos_of_pos hq0)]
      have hcube : 0 < q ^ (3 : ℕ) := pow_pos hq0 3
      nlinarith
    _ ≤ primeQuasiInnerResidueScale q := primeQuasiInnerResidueScale_lower hq

/-- The residue scale tends to zero from above at the endpoint `q = 1`. -/
theorem tendsto_primeQuasiInnerResidueScale_nhdsGT_one :
    Tendsto primeQuasiInnerResidueScale (nhdsWithin 1 (Set.Ioi 1)) (nhds 0) := by
  apply squeeze_zero'
  · filter_upwards [self_mem_nhdsWithin] with q hq
    exact (primeQuasiInnerResidueScale_pos hq).le
  · filter_upwards [self_mem_nhdsWithin] with q hq
    exact primeQuasiInnerResidueScale_upper hq
  · have hcont : ContinuousAt (fun q : ℝ => 2 * (q - 1) ^ (3 : ℕ) / q) 1 := by
      fun_prop (disch := norm_num)
    have hfull : Tendsto (fun q : ℝ => 2 * (q - 1) ^ (3 : ℕ) / q) (nhds 1) (nhds 0) := by
      simpa using hcont.tendsto
    exact hfull.mono_left inf_le_left

/-- The residue scale tends to positive infinity with its scale parameter. -/
theorem tendsto_primeQuasiInnerResidueScale_atTop :
    Tendsto primeQuasiInnerResidueScale atTop atTop := by
  rw [Filter.tendsto_atTop]
  intro b
  filter_upwards [Filter.eventually_ge_atTop (max 2 (b + 6))] with q hq
  have hq1 : 1 < q := lt_of_lt_of_le (by norm_num) ((le_max_left _ _).trans hq)
  have hbq : b + 6 ≤ q := (le_max_right _ _).trans hq
  linarith [primeQuasiInnerResidueScale_linear_lower hq1]

/-- The residue scale is continuous throughout its natural domain. -/
theorem continuousOn_primeQuasiInnerResidueScale :
    ContinuousOn primeQuasiInnerResidueScale (Set.Ioi 1) := by
  intro q hq
  apply ContinuousAt.continuousWithinAt
  have hqne : q ≠ 0 := ne_of_gt (zero_lt_one.trans hq)
  have hlogne : Real.log q ≠ 0 := ne_of_gt (Real.log_pos hq)
  unfold primeQuasiInnerResidueScale
  apply ContinuousAt.div
  · fun_prop
  · exact (continuousAt_id.pow 2).mul (Real.continuousAt_log hqne)
  · exact mul_ne_zero (pow_ne_zero 2 hqne) hlogne

/-- Every positive number occurs as a unique-scale residue value; this theorem supplies existence. -/
theorem exists_primeQuasiInnerResidueScale_eq {y : ℝ} (hy : 0 < y) :
    ∃ q > 1, primeQuasiInnerResidueScale q = y := by
  let δ : ℝ := min 1 (y / 4)
  have hδpos : 0 < δ := by simp [δ, hy]
  have hδone : δ ≤ 1 := min_le_left _ _
  have hδy : δ ≤ y / 4 := min_le_right _ _
  have hδsq : δ ^ (2 : ℕ) ≤ 1 := by nlinarith [sq_nonneg δ]
  have hδcube : δ ^ (3 : ℕ) ≤ δ := by
    nlinarith [mul_nonneg hδpos.le (sub_nonneg.mpr hδsq)]
  let a : ℝ := 1 + δ
  have ha1 : 1 < a := by simp [a, hδpos]
  have ha0 : 0 < a := zero_lt_one.trans ha1
  have ha2 : a ≤ 2 := by dsimp [a]; linarith
  have hRa : primeQuasiInnerResidueScale a < y := by
    calc
      primeQuasiInnerResidueScale a ≤ 2 * (a - 1) ^ (3 : ℕ) / a :=
        primeQuasiInnerResidueScale_upper ha1
      _ = 2 * δ ^ (3 : ℕ) / a := by simp [a]
      _ ≤ 2 * δ ^ (3 : ℕ) := by
        rw [div_le_iff₀ ha0]
        have hnum : 0 ≤ 2 * δ ^ (3 : ℕ) := by positivity
        nlinarith
      _ ≤ 2 * δ := by linarith
      _ < y := by linarith
  let b : ℝ := max 2 (y + 6)
  have hb1 : 1 < b := lt_of_lt_of_le (by norm_num) (le_max_left _ _)
  have hab : a ≤ b := ha2.trans (le_max_left _ _)
  have hyb : y ≤ primeQuasiInnerResidueScale b := by
    have hlinear := primeQuasiInnerResidueScale_linear_lower hb1
    have hthreshold : y + 6 ≤ b := le_max_right _ _
    linarith
  have hcont : ContinuousOn primeQuasiInnerResidueScale (Set.Icc a b) :=
    continuousOn_primeQuasiInnerResidueScale.mono fun q hq => ha1.trans_le hq.1
  obtain ⟨q, hq, hqy⟩ := intermediate_value_Icc hab hcont ⟨hRa.le, hyb⟩
  exact ⟨q, ha1.trans_le hq.1, hqy⟩

/-- The residue scale maps `(1, ∞)` exactly onto `(0, ∞)`. -/
theorem image_primeQuasiInnerResidueScale_Ioi :
    primeQuasiInnerResidueScale '' Set.Ioi 1 = Set.Ioi 0 := by
  apply Set.Subset.antisymm
  · rintro y ⟨q, hq, rfl⟩
    exact primeQuasiInnerResidueScale_pos hq
  · intro y hy
    obtain ⟨q, hq, hqy⟩ := exists_primeQuasiInnerResidueScale_eq hy
    exact ⟨q, hq, hqy⟩

end

end RHTower
