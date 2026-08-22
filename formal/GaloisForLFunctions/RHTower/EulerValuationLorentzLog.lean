import GaloisForLFunctions.RHTower.RationalHurwitzLorentzBoost
import GaloisForLFunctions.HTGeometry.ComplexLogTaylorUniform
import GaloisForLFunctions.RHTower.EulerFisherCurvature
import GaloisForLFunctions.RHTower.CriticalPrimeSourceSchattenIdeal

/-!
# The completed local Euler valuation tower is a Lorentz logarithm

Every prime-power valuation degree of the reflected rational-Hurwitz fibre is a power of one
normalized transfer

```text
T = p^{-1/2 + i t} · B(a·log p),      a = Re ρ − 1/2,  t = Im ρ,
```

whose light-cone eigenvalues are `p^{-(1-ρ)}` and `p^{-conj ρ}`.  Inside the open critical strip
both have modulus below one, so the connected-cycle series `∑_m T^m/m` converges absolutely and
sums to the matrix logarithm `−Log(I − T)`, which in even/odd coordinates is

```text
[[u, v], [v, u]],   u = (f(z₊)+f(z₋))/2,  v = (f(z₊)−f(z₋))/2,  f(z) = −log(1−z).
```

The odd coordinate `v` vanishes exactly on the critical line, so the completed local Euler
logarithm is a faithful critical-line detector even though it exists at every strip point.
-/

namespace RHTower

open Complex Matrix

noncomputable section

/-! ## The two light-cone eigenvalues -/

/-- The `+` light-cone eigenvalue `p^{-(1-ρ)}`. -/
def eulerLightConePlus (p : ℕ) (rho : ℂ) : ℂ := (p : ℂ) ^ (rho - 1)

/-- The `−` light-cone eigenvalue `p^{-conj ρ}`. -/
def eulerLightConeMinus (p : ℕ) (rho : ℂ) : ℂ := (p : ℂ) ^ (-((starRingEnd ℂ) rho))

theorem norm_eulerLightConePlus {p : ℕ} (hp : 0 < p) (rho : ℂ) :
    ‖eulerLightConePlus p rho‖ = (p : ℝ) ^ (rho.re - 1) := by
  have hppos : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp
  rw [eulerLightConePlus, ← Complex.ofReal_natCast,
    Complex.norm_cpow_eq_rpow_re_of_pos hppos]
  simp

theorem norm_eulerLightConeMinus {p : ℕ} (hp : 0 < p) (rho : ℂ) :
    ‖eulerLightConeMinus p rho‖ = (p : ℝ) ^ (-rho.re) := by
  have hppos : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp
  rw [eulerLightConeMinus, ← Complex.ofReal_natCast,
    Complex.norm_cpow_eq_rpow_re_of_pos hppos]
  simp

theorem norm_eulerLightConePlus_lt_one {p : ℕ} (hp : 1 < p) {rho : ℂ} (h1 : rho.re < 1) :
    ‖eulerLightConePlus p rho‖ < 1 := by
  have hp1 : (1 : ℝ) < (p : ℝ) := by exact_mod_cast hp
  rw [norm_eulerLightConePlus (by omega) rho]
  exact Real.rpow_lt_one_of_one_lt_of_neg hp1 (by linarith)

theorem norm_eulerLightConeMinus_lt_one {p : ℕ} (hp : 1 < p) {rho : ℂ} (h0 : 0 < rho.re) :
    ‖eulerLightConeMinus p rho‖ < 1 := by
  have hp1 : (1 : ℝ) < (p : ℝ) := by exact_mod_cast hp
  rw [norm_eulerLightConeMinus (by omega) rho]
  exact Real.rpow_lt_one_of_one_lt_of_neg hp1 (by linarith)

/-! ## The completed local Euler logarithm -/

/-- The even coordinate of the completed local Euler logarithm. -/
def eulerLogEven (p : ℕ) (rho : ℂ) : ℂ :=
  (-Complex.log (1 - eulerLightConePlus p rho)
    + -Complex.log (1 - eulerLightConeMinus p rho)) / 2

/-- The odd (anti-reflection) coordinate of the completed local Euler logarithm. -/
def eulerLogOdd (p : ℕ) (rho : ℂ) : ℂ :=
  (-Complex.log (1 - eulerLightConePlus p rho)
    - -Complex.log (1 - eulerLightConeMinus p rho)) / 2

/-- The two light-cone eigenvalues agree exactly on the critical line. -/
theorem eulerLightCone_eq_iff {p : ℕ} (hp : 1 < p) (rho : ℂ) :
    eulerLightConePlus p rho = eulerLightConeMinus p rho ↔ rho.re = 1 / 2 := by
  have hp1 : (1 : ℝ) < (p : ℝ) := by exact_mod_cast hp
  have hppos : (0 : ℝ) < (p : ℝ) := by linarith
  constructor
  · intro h
    have hn := congrArg norm h
    rw [norm_eulerLightConePlus (by omega), norm_eulerLightConeMinus (by omega)] at hn
    rcases lt_trichotomy (rho.re - 1) (-rho.re) with hlt | heq | hgt
    · exact absurd hn (ne_of_lt (Real.rpow_lt_rpow_left_iff hp1 |>.mpr hlt))
    · linarith
    · exact absurd hn (ne_of_gt (Real.rpow_lt_rpow_left_iff hp1 |>.mpr hgt))
  · intro h
    rw [eulerLightConePlus, eulerLightConeMinus]
    congr 1
    apply Complex.ext
    · simp [Complex.sub_re, h]
      ring
    · simp [Complex.sub_im]

/-- **Equation `(10)`.**  The odd coordinate of the completed local Euler logarithm vanishes
exactly on the critical line. -/
theorem eulerLogOdd_eq_zero_iff {p : ℕ} (hp : 1 < p) {rho : ℂ} (h0 : 0 < rho.re)
    (h1 : rho.re < 1) : eulerLogOdd p rho = 0 ↔ rho.re = 1 / 2 := by
  have hplus : (1 : ℂ) - eulerLightConePlus p rho ≠ 0 := by
    intro hc
    have := norm_eulerLightConePlus_lt_one hp h1
    rw [show eulerLightConePlus p rho = 1 from by linear_combination -hc] at this
    simp at this
  have hminus : (1 : ℂ) - eulerLightConeMinus p rho ≠ 0 := by
    intro hc
    have := norm_eulerLightConeMinus_lt_one hp h0
    rw [show eulerLightConeMinus p rho = 1 from by linear_combination -hc] at this
    simp at this
  constructor
  · intro hv
    have hlog : Complex.log (1 - eulerLightConePlus p rho)
        = Complex.log (1 - eulerLightConeMinus p rho) := by
      have h2 : (-Complex.log (1 - eulerLightConePlus p rho)
          - -Complex.log (1 - eulerLightConeMinus p rho)) = 0 := by
        have := hv
        rw [eulerLogOdd] at this
        field_simp at this
        linear_combination this
      linear_combination -h2
    have hexp := congrArg Complex.exp hlog
    rw [Complex.exp_log hplus, Complex.exp_log hminus] at hexp
    exact (eulerLightCone_eq_iff hp rho).mp (by linear_combination -hexp)
  · intro hre
    rw [eulerLogOdd, (eulerLightCone_eq_iff hp rho).mpr hre]
    ring

/-! ## The normalized prime transfer and its powers -/

/-- The common phase-and-normalization scalar `p^{-1/2 + i t}`. -/
def eulerPhase (p : ℕ) (rho : ℂ) : ℂ := (p : ℂ) ^ (-(1 / 2 : ℂ) + Complex.I * (rho.im : ℂ))

/-- The Lorentz rapidity of the local transfer. -/
def eulerRapidity (p : ℕ) (rho : ℂ) : ℝ := (rho.re - 1 / 2) * Real.log p

/-- The normalized prime transfer `T = p^{-1/2+it} · B(a log p)`. -/
def eulerTransfer (p : ℕ) (rho : ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  (eulerPhase p rho) • (lorentzBoost (eulerRapidity p rho)).map (fun x : ℝ => (x : ℂ))

theorem eulerLightConePlus_eq_phase_mul {p : ℕ} (hp : 0 < p) (rho : ℂ) :
    eulerLightConePlus p rho
      = eulerPhase p rho * ((Real.exp (eulerRapidity p rho) : ℝ) : ℂ) := by
  have hppos : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp
  have hpne : ((p : ℂ)) ≠ 0 := by
    simpa using ne_of_gt hppos
  have hexp : ((Real.exp (eulerRapidity p rho) : ℝ) : ℂ)
      = (p : ℂ) ^ (((rho.re - 1 / 2 : ℝ) : ℂ)) := by
    rw [eulerRapidity, mul_comm, ← Real.rpow_def_of_pos hppos, ← Complex.ofReal_natCast]
    exact Complex.ofReal_cpow hppos.le _
  rw [eulerLightConePlus, eulerPhase, hexp, ← Complex.cpow_add _ _ hpne]
  congr 1
  apply Complex.ext
  · simp [Complex.add_re, Complex.mul_re]
    ring
  · simp [Complex.add_im, Complex.mul_im]

theorem eulerLightConeMinus_eq_phase_mul {p : ℕ} (hp : 0 < p) (rho : ℂ) :
    eulerLightConeMinus p rho
      = eulerPhase p rho * ((Real.exp (-eulerRapidity p rho) : ℝ) : ℂ) := by
  have hppos : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp
  have hpne : ((p : ℂ)) ≠ 0 := by
    simpa using ne_of_gt hppos
  have hexp : ((Real.exp (-eulerRapidity p rho) : ℝ) : ℂ)
      = (p : ℂ) ^ (((-(rho.re - 1 / 2) : ℝ) : ℂ)) := by
    rw [eulerRapidity, show -((rho.re - 1 / 2) * Real.log p) = Real.log p * (-(rho.re - 1 / 2)) by
      ring, ← Real.rpow_def_of_pos hppos, ← Complex.ofReal_natCast]
    exact Complex.ofReal_cpow hppos.le _
  rw [eulerLightConeMinus, eulerPhase, hexp, ← Complex.cpow_add _ _ hpne]
  congr 1
  apply Complex.ext
  · simp [Complex.add_re, Complex.mul_re]
    ring
  · simp [Complex.add_im, Complex.mul_im]

theorem map_ofReal_mul (A B : Matrix (Fin 2) (Fin 2) ℝ) :
    (A * B).map (fun x : ℝ => (x : ℂ))
      = (A.map fun x : ℝ => (x : ℂ)) * (B.map fun x : ℝ => (x : ℂ)) :=
  Matrix.map_mul (f := Complex.ofRealHom)

/-- **Equation `(5)`, degreewise.**  Every valuation degree is a power of one transfer. -/
theorem eulerTransfer_pow (p : ℕ) (rho : ℂ) (m : ℕ) :
    eulerTransfer p rho ^ m
      = (eulerPhase p rho) ^ m •
        (lorentzBoost ((m : ℝ) * eulerRapidity p rho)).map (fun x : ℝ => (x : ℂ)) := by
  induction m with
  | zero =>
      simp only [pow_zero, Nat.cast_zero, zero_mul, lorentzBoost_zero, one_smul]
      exact (Matrix.map_one _ Complex.ofReal_zero Complex.ofReal_one).symm
  | succ m ih =>
      have hstep : (m : ℝ) * eulerRapidity p rho + eulerRapidity p rho
          = ((m + 1 : ℕ) : ℝ) * eulerRapidity p rho := by push_cast; ring
      rw [pow_succ, ih, eulerTransfer, Matrix.smul_mul, Matrix.mul_smul, smul_smul,
        ← map_ofReal_mul, lorentzBoost_mul, hstep, ← pow_succ]

theorem eulerTransfer_pow_entry_offDiagonal (p : ℕ) (rho : ℂ) (m : ℕ) :
    (eulerTransfer p rho ^ m) 0 1
      = (eulerPhase p rho) ^ m * ((Real.sinh ((m : ℝ) * eulerRapidity p rho) : ℝ) : ℂ) := by
  rw [eulerTransfer_pow]
  simp [lorentzBoost]

theorem eulerTransfer_pow_entry_diagonal (p : ℕ) (rho : ℂ) (m : ℕ) :
    (eulerTransfer p rho ^ m) 0 0
      = (eulerPhase p rho) ^ m * ((Real.cosh ((m : ℝ) * eulerRapidity p rho) : ℝ) : ℂ) := by
  rw [eulerTransfer_pow]
  simp [lorentzBoost]

/-! ## The connected-cycle series -/

private theorem ofReal_exp_pow (u : ℝ) (m : ℕ) :
    (((Real.exp u : ℝ) : ℂ)) ^ m = ((Real.exp ((m : ℝ) * u) : ℝ) : ℂ) := by
  rw [← Complex.ofReal_pow, ← Real.exp_nat_mul]

theorem eulerTransfer_offDiagonal_div_eq {p : ℕ} (hp : 0 < p) (rho : ℂ) (m : ℕ) :
    (eulerTransfer p rho ^ m) 0 1 / (m : ℂ)
      = (eulerLightConePlus p rho ^ m / (m : ℂ)
          - eulerLightConeMinus p rho ^ m / (m : ℂ)) / 2 := by
  rw [eulerTransfer_pow_entry_offDiagonal, eulerLightConePlus_eq_phase_mul hp,
    eulerLightConeMinus_eq_phase_mul hp, mul_pow, mul_pow, ofReal_exp_pow, ofReal_exp_pow]
  have hsinh : ((Real.sinh ((m : ℝ) * eulerRapidity p rho) : ℝ) : ℂ)
      = (((Real.exp ((m : ℝ) * eulerRapidity p rho) : ℝ) : ℂ)
        - ((Real.exp (-((m : ℝ) * eulerRapidity p rho)) : ℝ) : ℂ)) / 2 := by
    rw [Real.sinh_eq]
    push_cast
    ring
  rw [hsinh, show ((m : ℝ) * -eulerRapidity p rho) = -((m : ℝ) * eulerRapidity p rho) by ring]
  ring

theorem eulerTransfer_diagonal_div_eq {p : ℕ} (hp : 0 < p) (rho : ℂ) (m : ℕ) :
    (eulerTransfer p rho ^ m) 0 0 / (m : ℂ)
      = (eulerLightConePlus p rho ^ m / (m : ℂ)
          + eulerLightConeMinus p rho ^ m / (m : ℂ)) / 2 := by
  rw [eulerTransfer_pow_entry_diagonal, eulerLightConePlus_eq_phase_mul hp,
    eulerLightConeMinus_eq_phase_mul hp, mul_pow, mul_pow, ofReal_exp_pow, ofReal_exp_pow]
  have hcosh : ((Real.cosh ((m : ℝ) * eulerRapidity p rho) : ℝ) : ℂ)
      = (((Real.exp ((m : ℝ) * eulerRapidity p rho) : ℝ) : ℂ)
        + ((Real.exp (-((m : ℝ) * eulerRapidity p rho)) : ℝ) : ℂ)) / 2 := by
    rw [Real.cosh_eq]
    push_cast
    ring
  rw [hcosh, show ((m : ℝ) * -eulerRapidity p rho) = -((m : ℝ) * eulerRapidity p rho) by ring]
  ring

/-- **Equation `(9)`.**  The odd coordinate is the absolutely convergent connected-cycle sum of the
off-diagonal transfer entries. -/
theorem hasSum_eulerLogOdd {p : ℕ} (hp : 1 < p) {rho : ℂ} (h0 : 0 < rho.re) (h1 : rho.re < 1) :
    HasSum (fun m : ℕ => (eulerTransfer p rho ^ m) 0 1 / (m : ℂ)) (eulerLogOdd p rho) := by
  have hp0 : 0 < p := by omega
  have hpl := Complex.hasSum_taylorSeries_neg_log (norm_eulerLightConePlus_lt_one hp h1)
  have hmi := Complex.hasSum_taylorSeries_neg_log (norm_eulerLightConeMinus_lt_one hp h0)
  have hsum := (hpl.sub hmi).div_const 2
  refine hsum.congr_fun fun m => ?_
  exact eulerTransfer_offDiagonal_div_eq hp0 rho m

/-- The even coordinate as the connected-cycle sum of the diagonal transfer entries. -/
theorem hasSum_eulerLogEven {p : ℕ} (hp : 1 < p) {rho : ℂ} (h0 : 0 < rho.re) (h1 : rho.re < 1) :
    HasSum (fun m : ℕ => (eulerTransfer p rho ^ m) 0 0 / (m : ℂ)) (eulerLogEven p rho) := by
  have hp0 : 0 < p := by omega
  have hpl := Complex.hasSum_taylorSeries_neg_log (norm_eulerLightConePlus_lt_one hp h1)
  have hmi := Complex.hasSum_taylorSeries_neg_log (norm_eulerLightConeMinus_lt_one hp h0)
  have hsum := (hpl.add hmi).div_const 2
  refine hsum.congr_fun fun m => ?_
  exact eulerTransfer_diagonal_div_eq hp0 rho m

/-! ## Spectral radius inside the open strip -/

/-- **Equation `(17)`.**  The larger light-cone modulus is `p^{|a| - 1/2}`. -/
theorem max_norm_eulerLightCone {p : ℕ} (hp : 1 < p) (rho : ℂ) :
    max ‖eulerLightConePlus p rho‖ ‖eulerLightConeMinus p rho‖
      = (p : ℝ) ^ (|rho.re - 1 / 2| - 1 / 2) := by
  have hp1 : (1 : ℝ) < (p : ℝ) := by exact_mod_cast hp
  rw [norm_eulerLightConePlus (by omega), norm_eulerLightConeMinus (by omega)]
  rcases le_or_gt 0 (rho.re - 1 / 2) with hge | hlt
  · rw [abs_of_nonneg hge, max_eq_left]
    · congr 1
      ring
    · exact (Real.rpow_le_rpow_left_iff hp1).mpr (by linarith)
  · rw [abs_of_neg hlt, max_eq_right]
    · congr 1
      ring
    · exact (Real.rpow_le_rpow_left_iff hp1).mpr (by linarith)

/-- The transfer is a strict contraction in the light-cone basis at every open-strip point, so the
completed local Euler logarithm exists off the critical line as well as on it. -/
theorem max_norm_eulerLightCone_lt_one {p : ℕ} (hp : 1 < p) {rho : ℂ} (h0 : 0 < rho.re)
    (h1 : rho.re < 1) :
    max ‖eulerLightConePlus p rho‖ ‖eulerLightConeMinus p rho‖ < 1 := by
  rw [max_norm_eulerLightCone hp]
  have hp1 : (1 : ℝ) < (p : ℝ) := by exact_mod_cast hp
  refine Real.rpow_lt_one_of_one_lt_of_neg hp1 ?_
  rcases le_or_gt 0 (rho.re - 1 / 2) with hge | hlt
  · rw [abs_of_nonneg hge]; linarith
  · rw [abs_of_neg hlt]; linarith

/-! ## Two-sided bounds on the odd coordinate -/

/-- The common modulus scale `p^{|a| - 1/2}`. -/
def eulerConeScale (p : ℕ) (rho : ℂ) : ℝ := (p : ℝ) ^ (|rho.re - 1 / 2| - 1 / 2)

theorem eulerConeScale_pos {p : ℕ} (hp : 1 < p) (rho : ℂ) : 0 < eulerConeScale p rho := by
  exact Real.rpow_pos_of_pos (by exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one hp.le) _

theorem norm_eulerLightConePlus_le_scale {p : ℕ} (hp : 1 < p) (rho : ℂ) :
    ‖eulerLightConePlus p rho‖ ≤ eulerConeScale p rho := by
  have := max_norm_eulerLightCone hp rho
  rw [eulerConeScale, ← this]
  exact le_max_left _ _

theorem norm_eulerLightConeMinus_le_scale {p : ℕ} (hp : 1 < p) (rho : ℂ) :
    ‖eulerLightConeMinus p rho‖ ≤ eulerConeScale p rho := by
  have := max_norm_eulerLightCone hp rho
  rw [eulerConeScale, ← this]
  exact le_max_right _ _

private theorem norm_neg_log_one_sub_sub_self_le {z : ℂ} (hz : ‖z‖ ≤ 1 / 2) :
    ‖-Complex.log (1 - z) - z‖ ≤ ‖z‖ ^ 2 := by
  have hu : ‖(-z)‖ ≤ 1 / 2 := by simpa using hz
  have h := GaloisForLFunctions.HTGeometry.norm_log_one_add_sub_taylor_le' hu (n := 2) le_rfl
  have hsum : ∑ j ∈ Finset.range 2, (-1 : ℂ) ^ (j + 1) * (-z) ^ j / (j : ℂ) = -z := by
    simp [Finset.sum_range_succ]
  rw [hsum, show (1 : ℂ) + -z = 1 - z by ring] at h
  have hrw : -Complex.log (1 - z) - z = -(Complex.log (1 - z) - -z) := by ring
  rw [hrw, norm_neg]
  simpa using h

private theorem norm_neg_log_one_sub_le {z : ℂ} (hz : ‖z‖ ≤ 1 / 2) :
    ‖-Complex.log (1 - z)‖ ≤ ‖z‖ + ‖z‖ ^ 2 := by
  have h := norm_neg_log_one_sub_sub_self_le hz
  calc ‖-Complex.log (1 - z)‖ = ‖z + (-Complex.log (1 - z) - z)‖ := by congr 1; ring
    _ ≤ ‖z‖ + ‖-Complex.log (1 - z) - z‖ := norm_add_le _ _
    _ ≤ ‖z‖ + ‖z‖ ^ 2 := by linarith

/-- **Upper bound.**  The odd coordinate is at most twice the cone scale. -/
theorem norm_eulerLogOdd_le {p : ℕ} (hp : 1 < p) (rho : ℂ)
    (hX : eulerConeScale p rho ≤ 1 / 2) :
    ‖eulerLogOdd p rho‖ ≤ 2 * eulerConeScale p rho := by
  set X := eulerConeScale p rho with hXdef
  have hXpos := eulerConeScale_pos hp rho
  have hplus : ‖eulerLightConePlus p rho‖ ≤ X := norm_eulerLightConePlus_le_scale hp rho
  have hminus : ‖eulerLightConeMinus p rho‖ ≤ X := norm_eulerLightConeMinus_le_scale hp rho
  have hb1 := norm_neg_log_one_sub_le (le_trans hplus hX)
  have hb2 := norm_neg_log_one_sub_le (le_trans hminus hX)
  have hsq1 : ‖eulerLightConePlus p rho‖ ^ 2 ≤ X ^ 2 := by
    nlinarith [norm_nonneg (eulerLightConePlus p rho)]
  have hsq2 : ‖eulerLightConeMinus p rho‖ ^ 2 ≤ X ^ 2 := by
    nlinarith [norm_nonneg (eulerLightConeMinus p rho)]
  have hsplit : ‖eulerLogOdd p rho‖
      ≤ (‖-Complex.log (1 - eulerLightConePlus p rho)‖
        + ‖-Complex.log (1 - eulerLightConeMinus p rho)‖) / 2 := by
    rw [eulerLogOdd, norm_div]
    simp only [Complex.norm_ofNat]
    gcongr
    exact norm_sub_le _ _
  nlinarith

/-! ## The lower bound -/

/-- The smaller modulus scale `p^{-|a| - 1/2}`. -/
def eulerConeCoScale (p : ℕ) (rho : ℂ) : ℝ := (p : ℝ) ^ (-|rho.re - 1 / 2| - 1 / 2)

theorem norm_eulerPhase {p : ℕ} (hp : 0 < p) (rho : ℂ) :
    ‖eulerPhase p rho‖ = (p : ℝ) ^ (-(1 / 2) : ℝ) := by
  have hppos : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp
  rw [eulerPhase, ← Complex.ofReal_natCast, Complex.norm_cpow_eq_rpow_re_of_pos hppos]
  congr 1
  simp [Complex.add_re, Complex.mul_re]

theorem norm_eulerLightCone_sub {p : ℕ} (hp : 1 < p) (rho : ℂ) :
    ‖eulerLightConePlus p rho - eulerLightConeMinus p rho‖
      = eulerConeScale p rho - eulerConeCoScale p rho := by
  have hp0 : 0 < p := by omega
  have hppos : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp0
  have hp1 : (1 : ℝ) < (p : ℝ) := by exact_mod_cast hp
  set a := rho.re - 1 / 2 with hadef
  have hexpu : Real.exp (eulerRapidity p rho) = (p : ℝ) ^ a := by
    rw [eulerRapidity, mul_comm, ← Real.rpow_def_of_pos hppos]
  have hexpnu : Real.exp (-eulerRapidity p rho) = (p : ℝ) ^ (-a) := by
    rw [eulerRapidity, show -(a * Real.log p) = Real.log p * (-a) by ring,
      ← Real.rpow_def_of_pos hppos]
  have hsub : eulerLightConePlus p rho - eulerLightConeMinus p rho
      = eulerPhase p rho * ((((p : ℝ) ^ a - (p : ℝ) ^ (-a) : ℝ)) : ℂ) := by
    rw [eulerLightConePlus_eq_phase_mul hp0, eulerLightConeMinus_eq_phase_mul hp0, hexpu, hexpnu]
    push_cast
    ring
  rw [hsub, norm_mul, norm_eulerPhase hp0, Complex.norm_real, Real.norm_eq_abs]
  have hscale : eulerConeScale p rho = (p : ℝ) ^ (-(1 / 2) : ℝ) * (p : ℝ) ^ |a| := by
    rw [eulerConeScale, ← Real.rpow_add hppos]
    congr 1
    ring
  have hco : eulerConeCoScale p rho = (p : ℝ) ^ (-(1 / 2) : ℝ) * (p : ℝ) ^ (-|a|) := by
    rw [eulerConeCoScale, ← Real.rpow_add hppos]
    congr 1
    ring
  rw [hscale, hco, ← mul_sub]
  congr 1
  rcases le_or_gt 0 a with hge | hlt
  · rw [abs_of_nonneg hge, abs_of_nonneg (by
      have : (p : ℝ) ^ (-a) ≤ (p : ℝ) ^ a := (Real.rpow_le_rpow_left_iff hp1).mpr (by linarith)
      linarith)]
  · rw [abs_of_neg hlt, abs_of_nonpos (by
      have : (p : ℝ) ^ a ≤ (p : ℝ) ^ (-a) := (Real.rpow_le_rpow_left_iff hp1).mpr (by linarith)
      linarith)]
    ring

/-- **Lower bound.**  Away from the critical line the odd coordinate is at least an eighth of the
cone scale, once the scale is small and dominates its companion. -/
theorem le_norm_eulerLogOdd {p : ℕ} (hp : 1 < p) (rho : ℂ)
    (hX : eulerConeScale p rho ≤ 1 / 8)
    (hY : eulerConeCoScale p rho ≤ eulerConeScale p rho / 2) :
    eulerConeScale p rho / 8 ≤ ‖eulerLogOdd p rho‖ := by
  set X := eulerConeScale p rho with hXdef
  have hXpos := eulerConeScale_pos hp rho
  have hplus : ‖eulerLightConePlus p rho‖ ≤ X := norm_eulerLightConePlus_le_scale hp rho
  have hminus : ‖eulerLightConeMinus p rho‖ ≤ X := norm_eulerLightConeMinus_le_scale hp rho
  have hhalf : X ≤ 1 / 2 := by linarith
  have hE1 := norm_neg_log_one_sub_sub_self_le (le_trans hplus hhalf)
  have hE2 := norm_neg_log_one_sub_sub_self_le (le_trans hminus hhalf)
  have hsq1 : ‖eulerLightConePlus p rho‖ ^ 2 ≤ X ^ 2 := by
    nlinarith [norm_nonneg (eulerLightConePlus p rho)]
  have hsq2 : ‖eulerLightConeMinus p rho‖ ^ 2 ≤ X ^ 2 := by
    nlinarith [norm_nonneg (eulerLightConeMinus p rho)]
  have hdiff := norm_eulerLightCone_sub hp rho
  have hid : (2 : ℂ) * eulerLogOdd p rho
      = (eulerLightConePlus p rho - eulerLightConeMinus p rho)
        + ((-Complex.log (1 - eulerLightConePlus p rho) - eulerLightConePlus p rho)
          - (-Complex.log (1 - eulerLightConeMinus p rho) - eulerLightConeMinus p rho)) := by
    rw [eulerLogOdd]
    ring
  have hkey : ‖(2 : ℂ) * eulerLogOdd p rho‖
      ≥ ‖eulerLightConePlus p rho - eulerLightConeMinus p rho‖
        - (‖-Complex.log (1 - eulerLightConePlus p rho) - eulerLightConePlus p rho‖
          + ‖-Complex.log (1 - eulerLightConeMinus p rho) - eulerLightConeMinus p rho‖) := by
    rw [hid]
    have h1 := norm_add_le (eulerLightConePlus p rho - eulerLightConeMinus p rho)
      ((-Complex.log (1 - eulerLightConePlus p rho) - eulerLightConePlus p rho)
        - (-Complex.log (1 - eulerLightConeMinus p rho) - eulerLightConeMinus p rho))
    have h2 := norm_sub_le (-Complex.log (1 - eulerLightConePlus p rho) - eulerLightConePlus p rho)
      (-Complex.log (1 - eulerLightConeMinus p rho) - eulerLightConeMinus p rho)
    have h3 := norm_sub_norm_le (eulerLightConePlus p rho - eulerLightConeMinus p rho)
      (-((-Complex.log (1 - eulerLightConePlus p rho) - eulerLightConePlus p rho)
        - (-Complex.log (1 - eulerLightConeMinus p rho) - eulerLightConeMinus p rho)))
    have h4 : ‖(eulerLightConePlus p rho - eulerLightConeMinus p rho)
        + ((-Complex.log (1 - eulerLightConePlus p rho) - eulerLightConePlus p rho)
          - (-Complex.log (1 - eulerLightConeMinus p rho) - eulerLightConeMinus p rho))‖
        ≥ ‖eulerLightConePlus p rho - eulerLightConeMinus p rho‖
          - ‖(-Complex.log (1 - eulerLightConePlus p rho) - eulerLightConePlus p rho)
            - (-Complex.log (1 - eulerLightConeMinus p rho) - eulerLightConeMinus p rho)‖ := by
      have := norm_le_norm_add_norm_sub' (eulerLightConePlus p rho - eulerLightConeMinus p rho)
        (-((-Complex.log (1 - eulerLightConePlus p rho) - eulerLightConePlus p rho)
          - (-Complex.log (1 - eulerLightConeMinus p rho) - eulerLightConeMinus p rho)))
      simp only [sub_neg_eq_add, norm_neg] at this
      linarith
    linarith
  have hnorm2 : ‖(2 : ℂ) * eulerLogOdd p rho‖ = 2 * ‖eulerLogOdd p rho‖ := by
    rw [norm_mul]
    simp
  rw [hnorm2, hdiff] at hkey
  nlinarith

/-! ## The Gamma--Meixner weight -/

/-- The Gamma--Meixner prime weight `cosh(2 log p)^{-θ/2}`. -/
def gammaMeixnerWeight (theta : ℝ) (p : ℕ) : ℝ :=
  Real.cosh (2 * Real.log p) ^ (-(theta / 2))

theorem cosh_two_log_eq {p : ℕ} (hp : 0 < p) :
    Real.cosh (2 * Real.log p) = ((p : ℝ) ^ (2 : ℝ) + ((p : ℝ) ^ (2 : ℝ))⁻¹) / 2 := by
  have hppos : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp
  have hexp : Real.exp (2 * Real.log p) = (p : ℝ) ^ (2 : ℝ) := by
    rw [Real.rpow_def_of_pos hppos, mul_comm]
  rw [Real.cosh_eq, hexp, Real.exp_neg, hexp]

private theorem cosh_two_log_bounds {p : ℕ} (hp : 1 < p) :
    (p : ℝ) ^ (2 : ℝ) / 2 ≤ Real.cosh (2 * Real.log p) ∧
      Real.cosh (2 * Real.log p) ≤ (p : ℝ) ^ (2 : ℝ) := by
  have hp1 : (1 : ℝ) < (p : ℝ) := by exact_mod_cast hp
  have hppos : (0 : ℝ) < (p : ℝ) := by linarith
  have hsq : (1 : ℝ) ≤ (p : ℝ) ^ (2 : ℝ) := Real.one_le_rpow hp1.le (by norm_num)
  have hsqpos : (0 : ℝ) < (p : ℝ) ^ (2 : ℝ) := by linarith
  rw [cosh_two_log_eq (by omega)]
  constructor
  · have : (0 : ℝ) ≤ ((p : ℝ) ^ (2 : ℝ))⁻¹ := by positivity
    linarith
  · have hinv : ((p : ℝ) ^ (2 : ℝ))⁻¹ ≤ (p : ℝ) ^ (2 : ℝ) := by
      have h1 : ((p : ℝ) ^ (2 : ℝ))⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hsq
      linarith
    linarith

theorem gammaMeixnerWeight_le {p : ℕ} (hp : 1 < p) {theta : ℝ} (hθ : 0 ≤ theta) :
    gammaMeixnerWeight theta p ≤ 2 ^ (theta / 2) * (p : ℝ) ^ (-theta) := by
  have hp1 : (1 : ℝ) < (p : ℝ) := by exact_mod_cast hp
  have hppos : (0 : ℝ) < (p : ℝ) := by linarith
  obtain ⟨hlow, -⟩ := cosh_two_log_bounds hp
  have hpos : (0 : ℝ) < (p : ℝ) ^ (2 : ℝ) / 2 := by positivity
  have hmono := Real.rpow_le_rpow_of_nonpos hpos hlow (by linarith : -(theta / 2) ≤ 0)
  refine le_trans hmono ?_
  rw [Real.div_rpow (by positivity) (by norm_num : (0:ℝ) ≤ 2), ← Real.rpow_mul hppos.le,
    show (2 : ℝ) * -(theta / 2) = -theta by ring,
    Real.rpow_neg (by norm_num : (0:ℝ) ≤ 2), div_eq_mul_inv, inv_inv]
  exact le_of_eq (by ring)

theorem le_gammaMeixnerWeight {p : ℕ} (hp : 1 < p) {theta : ℝ} (hθ : 0 ≤ theta) :
    (p : ℝ) ^ (-theta) ≤ gammaMeixnerWeight theta p := by
  have hp1 : (1 : ℝ) < (p : ℝ) := by exact_mod_cast hp
  have hppos : (0 : ℝ) < (p : ℝ) := by linarith
  obtain ⟨-, hhigh⟩ := cosh_two_log_bounds hp
  have hcoshpos : (0 : ℝ) < Real.cosh (2 * Real.log p) := Real.cosh_pos _
  have hmono := Real.rpow_le_rpow_of_nonpos hcoshpos hhigh (by linarith : -(theta / 2) ≤ 0)
  refine le_trans ?_ hmono
  rw [← Real.rpow_mul hppos.le, show (2 : ℝ) * -(theta / 2) = -theta by ring]

/-! ## The all-prime anti-reflection energy and its exact threshold -/

/-- The prime term of the Gamma--Meixner anti-reflection energy. -/
def eulerAntiReflectionTerm (theta : ℝ) (rho : ℂ) (p : ℕ) : ℝ :=
  4 * (Real.log p) ^ 2 * ‖eulerLogOdd p rho‖ ^ 2 * gammaMeixnerWeight theta p

theorem eulerAntiReflectionTerm_nonneg (theta : ℝ) (rho : ℂ) (p : ℕ) :
    0 ≤ eulerAntiReflectionTerm theta rho p := by
  unfold eulerAntiReflectionTerm gammaMeixnerWeight
  positivity

/-- **On the critical line the whole energy vanishes.** -/
theorem eulerAntiReflectionTerm_eq_zero {p : ℕ} (hp : 1 < p) {rho : ℂ} (h0 : 0 < rho.re)
    (h1 : rho.re < 1) (hre : rho.re = 1 / 2) (theta : ℝ) :
    eulerAntiReflectionTerm theta rho p = 0 := by
  rw [eulerAntiReflectionTerm, (eulerLogOdd_eq_zero_iff hp h0 h1).mpr hre]
  simp

theorem eulerConeScale_sq {p : ℕ} (hp : 1 < p) (rho : ℂ) :
    (eulerConeScale p rho) ^ 2 = (p : ℝ) ^ (2 * |rho.re - 1 / 2| - 1) := by
  have hppos : (0 : ℝ) < (p : ℝ) := by
    exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one hp.le
  rw [eulerConeScale, ← Real.rpow_natCast _ 2, ← Real.rpow_mul hppos.le]
  congr 1
  push_cast
  ring

theorem eulerConeCoScale_eq {p : ℕ} (hp : 1 < p) (rho : ℂ) :
    eulerConeCoScale p rho
      = eulerConeScale p rho * (p : ℝ) ^ (-(2 * |rho.re - 1 / 2|)) := by
  have hppos : (0 : ℝ) < (p : ℝ) := by
    exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one hp.le
  rw [eulerConeCoScale, eulerConeScale, ← Real.rpow_add hppos]
  congr 1
  ring

theorem tendsto_primes_cofinite_atTop :
    Filter.Tendsto (fun p : Nat.Primes => ((p : ℕ) : ℝ)) Filter.cofinite Filter.atTop := by
  have hinj : Function.Injective (fun p : Nat.Primes => (p : ℕ)) := Subtype.val_injective
  have h1 : Filter.Tendsto (fun p : Nat.Primes => (p : ℕ)) Filter.cofinite Filter.cofinite :=
    hinj.tendsto_cofinite
  rw [Nat.cofinite_eq_atTop] at h1
  exact tendsto_natCast_atTop_atTop.comp h1

private theorem tendsto_rpow_neg_atTop_zero {c : ℝ} (hc : c < 0) :
    Filter.Tendsto (fun x : ℝ => x ^ c) Filter.atTop (nhds 0) := by
  have h1 : Filter.Tendsto (fun x : ℝ => c * Real.log x) Filter.atTop Filter.atBot := by
    simpa using (Filter.Tendsto.const_mul_atTop_of_neg hc Real.tendsto_log_atTop)
  have h2 := Real.tendsto_exp_atBot.comp h1
  refine h2.congr' ?_
  filter_upwards [Filter.eventually_gt_atTop (0 : ℝ)] with x hx
  simp [Function.comp, Real.rpow_def_of_pos hx, mul_comm]

theorem abs_re_sub_half_lt {rho : ℂ} (h0 : 0 < rho.re) (h1 : rho.re < 1) :
    |rho.re - 1 / 2| < 1 / 2 := by
  rw [abs_lt]
  constructor <;> linarith

theorem eventually_eulerConeScale_le {rho : ℂ} (h0 : 0 < rho.re) (h1 : rho.re < 1) {ε : ℝ}
    (hε : 0 < ε) : ∀ᶠ p : Nat.Primes in Filter.cofinite, eulerConeScale (p : ℕ) rho ≤ ε := by
  have hc : |rho.re - 1 / 2| - 1 / 2 < 0 := by
    have := abs_re_sub_half_lt h0 h1
    linarith
  have hlim := (tendsto_rpow_neg_atTop_zero hc).comp tendsto_primes_cofinite_atTop
  exact hlim.eventually_le_const hε

theorem eventually_eulerConeCoScale_le {rho : ℂ} (hre : rho.re ≠ 1 / 2) :
    ∀ᶠ p : Nat.Primes in Filter.cofinite,
      eulerConeCoScale (p : ℕ) rho ≤ eulerConeScale (p : ℕ) rho / 2 := by
  have hApos : 0 < |rho.re - 1 / 2| := abs_pos.mpr (sub_ne_zero.mpr hre)
  have hc : -(2 * |rho.re - 1 / 2|) < 0 := by linarith
  have hlim := (tendsto_rpow_neg_atTop_zero hc).comp tendsto_primes_cofinite_atTop
  have hev := hlim.eventually_le_const (by norm_num : (0:ℝ) < 1 / 2)
  have hprime : ∀ᶠ p : Nat.Primes in Filter.cofinite, (1 : ℕ) < (p : ℕ) :=
    Filter.Eventually.of_forall fun p => p.2.one_lt
  filter_upwards [hev, hprime] with p hp hp1
  rw [eulerConeCoScale_eq hp1]
  have hX := eulerConeScale_pos hp1 rho
  simp only [Function.comp_apply] at hp
  nlinarith

theorem eventually_sq_log_ge {c : ℝ} :
    ∀ᶠ p : Nat.Primes in Filter.cofinite, c ≤ (Real.log ((p : ℕ) : ℝ)) ^ 2 := by
  have hlim : Filter.Tendsto (fun p : Nat.Primes => (Real.log ((p : ℕ) : ℝ)) ^ 2)
      Filter.cofinite Filter.atTop := by
    have h1 := Real.tendsto_log_atTop.comp tendsto_primes_cofinite_atTop
    exact (Filter.tendsto_pow_atTop (by norm_num : (2 : ℕ) ≠ 0)).comp h1
  exact hlim.eventually_ge_atTop c

/-- **Equation `(16)`.**  The all-prime Gamma--Meixner anti-reflection energy converges exactly
above the horizontal-displacement threshold `2|Re ρ − 1/2|`. -/
theorem summable_eulerAntiReflectionTerm_iff {rho : ℂ} (h0 : 0 < rho.re) (h1 : rho.re < 1)
    (hre : rho.re ≠ 1 / 2) {theta : ℝ} (hθ : 0 ≤ theta) :
    Summable (fun p : Nat.Primes => eulerAntiReflectionTerm theta rho (p : ℕ))
      ↔ 2 * |rho.re - 1 / 2| < theta := by
  set A := |rho.re - 1 / 2| with hAdef
  have hApos : 0 < A := abs_pos.mpr (sub_ne_zero.mpr hre)
  have hprime : ∀ᶠ p : Nat.Primes in Filter.cofinite, (1 : ℕ) < (p : ℕ) :=
    Filter.Eventually.of_forall fun p => p.2.one_lt
  have hev8 := eventually_eulerConeScale_le h0 h1 (show (0:ℝ) < 1 / 8 by norm_num)
  have hevY := eventually_eulerConeCoScale_le hre
  constructor
  · intro hs
    by_contra hcon
    have hle : theta ≤ 2 * A := not_lt.mp hcon
    refine not_summable_one_div_primes ?_
    refine Summable.of_norm_bounded_eventually hs ?_
    have hlog := eventually_sq_log_ge (c := (16 : ℝ))
    filter_upwards [hev8, hevY, hprime, hlog] with p hX hY hp1 hL
    have hppos : (0 : ℝ) < ((p : ℕ) : ℝ) := by exact_mod_cast Nat.zero_lt_of_lt hp1
    have hpone : (1 : ℝ) < ((p : ℕ) : ℝ) := by exact_mod_cast hp1
    have hXpos := eulerConeScale_pos hp1 rho
    have hlow := le_norm_eulerLogOdd hp1 rho hX hY
    have hwlow := le_gammaMeixnerWeight hp1 hθ
    have hsq : (eulerConeScale (p : ℕ) rho / 8) ^ 2 ≤ ‖eulerLogOdd (p : ℕ) rho‖ ^ 2 := by
      nlinarith [norm_nonneg (eulerLogOdd (p : ℕ) rho)]
    have hXsq := eulerConeScale_sq hp1 rho
    have hexp : ((p : ℕ) : ℝ) ^ (-(1 : ℝ))
        ≤ ((p : ℕ) : ℝ) ^ (2 * A - 1) * ((p : ℕ) : ℝ) ^ (-theta) := by
      rw [← Real.rpow_add hppos]
      exact (Real.rpow_le_rpow_left_iff hpone).mpr (by linarith)
    have hinv : ‖1 / ((p : ℕ) : ℝ)‖ = ((p : ℕ) : ℝ) ^ (-(1 : ℝ)) := by
      rw [Real.rpow_neg_one, Real.norm_eq_abs, abs_of_pos (by positivity), one_div]
    rw [hinv, eulerAntiReflectionTerm]
    rw [← hAdef] at hXsq
    have hwpos : (0 : ℝ) < gammaMeixnerWeight theta (p : ℕ) := by
      unfold gammaMeixnerWeight
      positivity
    have hppow : (0 : ℝ) < ((p : ℕ) : ℝ) ^ (2 * A - 1) := Real.rpow_pos_of_pos hppos _
    have hppowθ : (0 : ℝ) < ((p : ℕ) : ℝ) ^ (-theta) := Real.rpow_pos_of_pos hppos _
    have hval : 4 * (eulerConeScale (p : ℕ) rho / 8) ^ 2
        = (1 / 16) * ((p : ℕ) : ℝ) ^ (2 * A - 1) := by
      have h64 : (eulerConeScale (p : ℕ) rho / 8) ^ 2
          = (eulerConeScale (p : ℕ) rho) ^ 2 / 64 := by ring
      rw [h64, hXsq]
      ring
    calc ((p : ℕ) : ℝ) ^ (-(1 : ℝ))
        ≤ ((p : ℕ) : ℝ) ^ (2 * A - 1) * ((p : ℕ) : ℝ) ^ (-theta) := hexp
      _ = 16 * ((1 / 16) * ((p : ℕ) : ℝ) ^ (2 * A - 1)) * ((p : ℕ) : ℝ) ^ (-theta) := by ring
      _ ≤ (Real.log ((p : ℕ) : ℝ)) ^ 2 * ((1 / 16) * ((p : ℕ) : ℝ) ^ (2 * A - 1))
            * ((p : ℕ) : ℝ) ^ (-theta) := by
          gcongr
      _ = 4 * (Real.log ((p : ℕ) : ℝ)) ^ 2 * (eulerConeScale (p : ℕ) rho / 8) ^ 2
            * ((p : ℕ) : ℝ) ^ (-theta) := by rw [← hval]; ring
      _ ≤ 4 * (Real.log ((p : ℕ) : ℝ)) ^ 2 * ‖eulerLogOdd (p : ℕ) rho‖ ^ 2
            * ((p : ℕ) : ℝ) ^ (-theta) := by
          gcongr
      _ ≤ 4 * (Real.log ((p : ℕ) : ℝ)) ^ 2 * ‖eulerLogOdd (p : ℕ) rho‖ ^ 2
            * gammaMeixnerWeight theta (p : ℕ) := by
          gcongr
  · intro hlt
    set beta := 1 + theta - 2 * A with hbeta
    have hbeta1 : 1 < beta := by rw [hbeta]; linarith
    have hbase : Summable
        (fun p : Nat.Primes => |Real.log ((p : ℕ) : ℝ)| ^ 2 * (((p : ℕ) : ℝ)) ^ (-beta)) := by
      have := summable_abs_log_natCast_pow_mul_rpow_neg 2 beta hbeta1
      exact this.subtype (fun n : ℕ => n.Prime)
    refine Summable.of_norm_bounded_eventually
      (hbase.mul_left (16 * 2 ^ (theta / 2))) ?_
    filter_upwards [hev8, hprime] with p hX hp1
    have hppos : (0 : ℝ) < ((p : ℕ) : ℝ) := by exact_mod_cast Nat.zero_lt_of_lt hp1
    have hXpos := eulerConeScale_pos hp1 rho
    have hXhalf : eulerConeScale (p : ℕ) rho ≤ 1 / 2 := by linarith
    have hup := norm_eulerLogOdd_le hp1 rho hXhalf
    have hwup := gammaMeixnerWeight_le hp1 hθ
    have hsq : ‖eulerLogOdd (p : ℕ) rho‖ ^ 2 ≤ (2 * eulerConeScale (p : ℕ) rho) ^ 2 := by
      nlinarith [norm_nonneg (eulerLogOdd (p : ℕ) rho)]
    have hXsq := eulerConeScale_sq hp1 rho
    have hexp : ((p : ℕ) : ℝ) ^ (2 * A - 1) * ((p : ℕ) : ℝ) ^ (-theta)
        = ((p : ℕ) : ℝ) ^ (-beta) := by
      rw [← Real.rpow_add hppos, hbeta]
      congr 1
      ring
    have hlogabs : |Real.log ((p : ℕ) : ℝ)| ^ 2 = (Real.log ((p : ℕ) : ℝ)) ^ 2 := sq_abs _
    have hnorm : ‖eulerAntiReflectionTerm theta rho (p : ℕ)‖
        = eulerAntiReflectionTerm theta rho (p : ℕ) :=
      Real.norm_of_nonneg (eulerAntiReflectionTerm_nonneg theta rho (p : ℕ))
    rw [hnorm, eulerAntiReflectionTerm, hlogabs]
    rw [← hAdef] at hXsq
    have hlogsq : (0 : ℝ) ≤ (Real.log ((p : ℕ) : ℝ)) ^ 2 := sq_nonneg _
    have hwpos : (0 : ℝ) < gammaMeixnerWeight theta (p : ℕ) := by
      unfold gammaMeixnerWeight
      positivity
    have hppowθ : (0 : ℝ) < ((p : ℕ) : ℝ) ^ (-theta) := Real.rpow_pos_of_pos hppos _
    have htwo : (0 : ℝ) < 2 ^ (theta / 2) := Real.rpow_pos_of_pos (by norm_num) _
    calc 4 * (Real.log ((p : ℕ) : ℝ)) ^ 2 * ‖eulerLogOdd (p : ℕ) rho‖ ^ 2
          * gammaMeixnerWeight theta (p : ℕ)
        ≤ 4 * (Real.log ((p : ℕ) : ℝ)) ^ 2 * (2 * eulerConeScale (p : ℕ) rho) ^ 2
            * gammaMeixnerWeight theta (p : ℕ) := by
          gcongr
      _ ≤ 4 * (Real.log ((p : ℕ) : ℝ)) ^ 2 * (2 * eulerConeScale (p : ℕ) rho) ^ 2
            * (2 ^ (theta / 2) * ((p : ℕ) : ℝ) ^ (-theta)) := by
          gcongr
      _ = 16 * 2 ^ (theta / 2) * ((Real.log ((p : ℕ) : ℝ)) ^ 2
            * (((p : ℕ) : ℝ) ^ (2 * A - 1) * ((p : ℕ) : ℝ) ^ (-theta))) := by
          have h4 : (2 * eulerConeScale (p : ℕ) rho) ^ 2
              = 4 * ((p : ℕ) : ℝ) ^ (2 * A - 1) := by
            rw [show (2 * eulerConeScale (p : ℕ) rho) ^ 2
              = 4 * (eulerConeScale (p : ℕ) rho) ^ 2 by ring, hXsq]
          rw [h4]
          ring
      _ = 16 * 2 ^ (theta / 2) * ((Real.log ((p : ℕ) : ℝ)) ^ 2 * ((p : ℕ) : ℝ) ^ (-beta)) := by
          rw [hexp]

end

end RHTower
