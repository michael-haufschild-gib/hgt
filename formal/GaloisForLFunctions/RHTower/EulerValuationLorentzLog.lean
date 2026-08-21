import GaloisForLFunctions.RHTower.RationalHurwitzLorentzBoost

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

end

end RHTower
