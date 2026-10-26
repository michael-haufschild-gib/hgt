import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.OneProbeSeesEveryOuterEigenvalue
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.TheScalingSurfaceOfACurve

/-!
# The towers of a curve are its base changes

The scaling surface of a curve datum has the zeros `ρ_{i,k}`, `q^{ρ_{i,k} − ½} = β_i`, periodic in
height with period `2π/log q`. Its zeros of a fixed depth have convergence exponent `1`, so the
deep-sparse one-prime law of `OnePrimeSeesTheWholeDefectOfZeta` does not apply; but its real parts
take finitely many values, and one probe sees every tower at every scale
(`curve_exists_probe_tower_law`, via `exists_probe_tower_law_of_wellFounded_at`). What a tower of
scale `ℓ` sees depends only on the folding
`ρ_{i,k} ↦ e^{ℓ(ρ_{i,k} − ½)} = e^{(ℓ/log q)(log β_i + 2πik)}` (`frobEig_zetaZero`).

* **Arithmetic scales** (`outerEig_curveConfig_rat`). At `ℓ = (a/b) log q`, `a, b` coprime, the
  outer eigenvalues are the `b`-th roots of the `β_i^a` outside the unit circle; finitely many.
  At `ℓ = a log q` the tower is the Frobenius span of the base change to `𝔽_{q^a}`
  (`CurveDatum.pow`, `curve_tower_law_baseChange`).
* **Non-arithmetic scales** (`outerEig_curveConfig_infinite`). If `ℓ/log q` is irrational the
  vertical translates of a zero have distinct eigenvalues, so the tower defect is infinite, as for
  the whole scaling surface (`curve_tower_unbounded_iff`).
* **Unitarity** (`curve_unitary_iff_tower_psd`). At every scale one probe's tower is positive on
  every window iff `|β_i| = 1` for all `i`.

So the scales at which a tower of a curve sees a finite defect are exactly the arithmetic ones, and
there the finiteness is resonance: `b` folds of each eigenvalue, the period quotient of
`TheFrobeniusSpanIsTheTowerOfTheScalingSurface` at `b = 1`. A zeta configuration has no period,
and its primes behave like the non-arithmetic scales of a curve.
-/

open Complex Set
open scoped Real ComplexConjugate
open Zeta23 GaloisForLFunctions.HTGeometry
open GaloisForLFunctions.SquareRootThreshold (TemperedConfig)

noncomputable section

namespace GaloisForLFunctions.ArithmeticCastelnuovoSeveri

/-! ### 1. One probe at one scale -/

/-- **One probe at one scale.** If the real parts of the right zeros admit no increasing sequence,
one probe's tower at scale `ℓ` has `n` negative squares on some window iff there are at least `n`
distinct outer eigenvalues at `ℓ`. -/
theorem exists_probe_tower_law_of_wellFounded_at (Z : ZeroConfig) (hZ : TemperedConfig Z)
    (hWF : (Complex.re '' rightZeros Z).WellFoundedOn (· > ·)) {ℓ : ℝ} (hℓ : 0 < ℓ) :
    ∃ g : ℝ → ℂ, ContDiff ℝ 2 g ∧ HasCompactSupport g ∧ ∀ n : ℕ,
      (∃ K : Finset ℤ, n ≤ hermNegIndex (towerGram Z g ℓ K)) ↔
        (n : ℕ∞) ≤ (outerEig Z ℓ).encard := by
  have hR : (rightZeros Z).Countable :=
    (SquareRootThreshold.countable_carrier Z).mono fun _ h => h.1
  set B : Set ℝ := ⋃ b ∈ outerEig Z ℓ, {s : ℝ | frobWeight Z (probe s 0) ℓ b = 0}
  have hB : B.Countable := (hR.image _).biUnion fun b hb => countable_badModulation Z hZ hℓ hb
  obtain ⟨s, hs⟩ : ∃ s, s ∉ B := by
    by_contra h
    push Not at h
    exact Cardinal.not_countable_real (hB.mono fun s _ => h s)
  refine ⟨probe s 0, probe_contDiff s 0, probe_hasCompactSupport s 0, fun n => ?_⟩
  have hvis : visibleSet Z (probe s 0) ℓ = outerEig Z ℓ :=
    Set.ext fun b => ⟨fun hb => hb.1, fun hb => ⟨hb, fun h0 => hs (Set.mem_biUnion hb h0)⟩⟩
  rw [tower_pontryagin_law_of_wellFounded Z hZ (probe_contDiff s 0) (probe_hasCompactSupport s 0)
    hℓ hWF n, hvis]

namespace CurveDatum

variable {ι : Type*} [Fintype ι] (D : CurveDatum ι)

/-! ### 2. Frobenius eigenvalues at every scale -/

/-- At scale `ℓ` the zero `ρ_{i,k}` has eigenvalue `exp((ℓ/log q)(log β_i + 2πik))`. -/
theorem frobEig_zetaZero (ℓ : ℝ) (i : ι) (k : ℤ) :
    frobEig ℓ (D.zetaZero i k) =
      cexp (((ℓ / Real.log D.q : ℝ) : ℂ) * (log (D.β i) + k * (2 * π * I))) := by
  have hl : (Real.log D.q : ℂ) ≠ 0 := by exact_mod_cast D.log_q_pos.ne'
  rw [← D.log_q_mul_zetaZero i k, Complex.ofReal_div, ← mul_assoc, div_mul_cancel₀ _ hl]
  rfl

/-- `exp(a(log β + 2πik)) = β^a`. -/
theorem cexp_natCast_mul_log_add (a : ℕ) {β : ℂ} (hβ : β ≠ 0) (k : ℤ) :
    cexp ((a : ℂ) * (log β + k * (2 * π * I))) = β ^ a := by
  rw [mul_add, Complex.exp_add, Complex.exp_nat_mul, Complex.exp_log hβ, ← mul_assoc,
    show (a : ℂ) * k = ((a * k : ℤ) : ℂ) by push_cast; ring, Complex.exp_int_mul_two_pi_mul_I,
    mul_one]

variable (hD : ∀ i, ‖D.β i‖ ≤ D.sqrtq)

/-- At `ℓ = (a/b) log q` every outer eigenvalue is a `b`-th root of some `β_i^a`, `|β_i| > 1`. -/
theorem outerEig_curveConfig_subset (a b : ℕ) (hb : 0 < b) :
    outerEig (D.curveConfig hD) ((a / b : ℝ) * Real.log D.q) ⊆
      {w | ∃ i, 1 < ‖D.β i‖ ∧ w ^ b = D.β i ^ a} := by
  have hc : (a / b : ℝ) * Real.log D.q / Real.log D.q = a / b :=
    mul_div_cancel_right₀ _ D.log_q_pos.ne'
  have hb' : (b : ℂ) ≠ 0 := by exact_mod_cast hb.ne'
  rintro _ ⟨ρ, ⟨⟨⟨i, k⟩, rfl⟩, hre⟩, rfl⟩
  refine ⟨i, (D.re_zetaZero_gt_iff i k).mp hre, ?_⟩
  rw [D.frobEig_zetaZero, hc, ← Complex.exp_nat_mul]
  have e : (b : ℂ) * (((a / b : ℝ) : ℂ) * (log (D.β i) + k * (2 * π * I))) =
      (a : ℂ) * (log (D.β i) + k * (2 * π * I)) := by
    push_cast
    rw [← mul_assoc, mul_div_cancel₀ _ hb']
  rw [e, cexp_natCast_mul_log_add a (D.β_ne_zero i)]

/-- **Arithmetic scales.** At `ℓ = (a/b) log q` with `a, b` coprime the outer eigenvalues are
exactly the `b`-th roots of the `β_i^a` with `|β_i| > 1`. -/
theorem outerEig_curveConfig_rat {a b : ℕ} (hb : 0 < b) (hab : Nat.Coprime a b) :
    outerEig (D.curveConfig hD) ((a / b : ℝ) * Real.log D.q) =
      {w | ∃ i, 1 < ‖D.β i‖ ∧ w ^ b = D.β i ^ a} := by
  refine (D.outerEig_curveConfig_subset hD a b hb).antisymm ?_
  rintro w ⟨i, hi, hw⟩
  have hβ := D.β_ne_zero i
  have hw0 : w ≠ 0 := by
    rintro rfl
    rw [zero_pow hb.ne'] at hw
    exact pow_ne_zero a hβ hw.symm
  -- `b log w = a log β_i + 2πin`
  obtain ⟨n, hn⟩ : ∃ n : ℤ, (b : ℂ) * log w = a * log (D.β i) + n * (2 * π * I) := by
    have h1 : cexp ((b : ℂ) * log w) = cexp ((a : ℂ) * log (D.β i)) := by
      rw [Complex.exp_nat_mul, Complex.exp_nat_mul, Complex.exp_log hw0, Complex.exp_log hβ, hw]
    exact Complex.exp_eq_exp_iff_exists_int.mp h1
  -- Bézout: the vertical translate `k = u n` folds onto `w`
  obtain ⟨u, v, huv⟩ := Nat.isCoprime_iff_coprime.mpr hab
  have hc : (a / b : ℝ) * Real.log D.q / Real.log D.q = a / b :=
    mul_div_cancel_right₀ _ D.log_q_pos.ne'
  have hb' : (b : ℂ) ≠ 0 := by exact_mod_cast hb.ne'
  have huv' : (u : ℂ) * a + v * b = 1 := by exact_mod_cast huv
  refine ⟨D.zetaZero i (u * n), ⟨⟨⟨i, u * n⟩, rfl⟩, (D.re_zetaZero_gt_iff i _).mpr hi⟩, ?_⟩
  rw [D.frobEig_zetaZero, hc, ← Complex.exp_log hw0]
  refine Complex.exp_eq_exp_iff_exists_int.mpr ⟨-(n * v), ?_⟩
  push_cast
  rw [div_mul_eq_mul_div, div_eq_iff hb']
  linear_combination (-1 : ℂ) * hn + ((n : ℂ) * (2 * π * I)) * huv'

/-- **Non-arithmetic scales.** If `ℓ/log q` is irrational and some eigenvalue lies outside the unit
circle, the vertical translates of one outer zero have distinct eigenvalues: infinitely many. -/
theorem outerEig_curveConfig_infinite {ℓ : ℝ} (hirr : Irrational (ℓ / Real.log D.q))
    (hU : D.outerSpectrum.Nonempty) : (outerEig (D.curveConfig hD) ℓ).Infinite := by
  obtain ⟨z, hz⟩ := hU
  obtain ⟨hzs, hz1⟩ := Finset.mem_filter.mp hz
  obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hzs
  have hinj : Function.Injective fun k : ℤ => frobEig ℓ (D.zetaZero i k) := by
    intro k k' h
    simp only [D.frobEig_zetaZero] at h
    obtain ⟨n, hn⟩ := Complex.exp_eq_exp_iff_exists_int.mp h
    by_contra hne
    set c : ℝ := ℓ / Real.log D.q with hc
    have h2 : ((c * ((k - k' : ℤ) : ℝ) - n : ℝ) : ℂ) * (2 * π * I) = 0 := by
      push_cast
      linear_combination hn
    rcases mul_eq_zero.mp h2 with h3 | h3
    · have h4 : c * ((k - k' : ℤ) : ℝ) = n := by
        have := Complex.ofReal_eq_zero.mp h3
        linarith
      exact (hirr.mul_intCast (sub_ne_zero.mpr hne)).ne_int n h4
    · exact Complex.two_pi_I_ne_zero h3
  refine (Set.infinite_range_of_injective hinj).mono ?_
  rintro _ ⟨k, rfl⟩
  exact ⟨D.zetaZero i k, ⟨⟨⟨i, k⟩, rfl⟩, (D.re_zetaZero_gt_iff i k).mpr hz1⟩, rfl⟩

/-- At a scale with `ℓ/log q` rational the outer eigenvalues are finitely many. -/
theorem outerEig_curveConfig_finite {ℓ : ℝ} (hℓ : 0 < ℓ) (hrat : ¬ Irrational (ℓ / Real.log D.q)) :
    (outerEig (D.curveConfig hD) ℓ).Finite := by
  obtain ⟨r, hr⟩ : ∃ r : ℚ, (r : ℝ) = ℓ / Real.log D.q := by simpa [Irrational] using hrat
  have hr0 : 0 < r := by
    have : (0 : ℝ) < r := by rw [hr]; exact div_pos hℓ D.log_q_pos
    exact_mod_cast this
  have hnum : 0 < r.num := Rat.num_pos.mpr hr0
  have hℓeq : ℓ = ((r.num.natAbs : ℕ) / r.den : ℝ) * Real.log D.q := by
    have h1 : ((r.num.natAbs : ℕ) : ℝ) = (r.num : ℝ) := by
      rw [← Int.cast_natCast, Int.natAbs_of_nonneg hnum.le]
    rw [h1, ← Rat.cast_def, hr, div_mul_cancel₀ _ D.log_q_pos.ne']
  rw [hℓeq]
  refine (Set.finite_iUnion fun i : ι =>
    (Polynomial.nthRoots r.den (D.β i ^ r.num.natAbs)).toFinset.finite_toSet).subset ?_
  intro w hw
  obtain ⟨i, -, hwi⟩ := D.outerEig_curveConfig_subset hD _ _ r.den_pos hw
  exact Set.mem_iUnion.mpr ⟨i, by simpa [Polynomial.mem_nthRoots r.den_pos] using hwi⟩

/-- **Finite towers are arithmetic.** For a datum with an eigenvalue outside the unit circle the
outer eigenvalues at scale `ℓ` are infinitely many iff `ℓ/log q` is irrational. -/
theorem outerEig_curveConfig_infinite_iff (hU : D.outerSpectrum.Nonempty) {ℓ : ℝ}
    (hℓ : 0 < ℓ) :
    (outerEig (D.curveConfig hD) ℓ).Infinite ↔ Irrational (ℓ / Real.log D.q) :=
  ⟨fun h => by
    by_contra hrat
    exact h (D.outerEig_curveConfig_finite hD hℓ hrat),
   fun hirr => D.outerEig_curveConfig_infinite hD hirr hU⟩

/-! ### 3. The towers -/

/-- The real parts of the zeros of a curve take finitely many values. -/
theorem wellFoundedOn_re_rightZeros_curveConfig :
    (Complex.re '' rightZeros (D.curveConfig hD)).WellFoundedOn (· > ·) := by
  refine ((Set.finite_range fun i : ι =>
    1 / 2 + Real.log ‖D.β i‖ / Real.log D.q).subset ?_).wellFoundedOn
  rintro _ ⟨_, ⟨⟨⟨i, k⟩, rfl⟩, -⟩, rfl⟩
  exact ⟨i, (D.re_zetaZero i k).symm⟩

/-- **One probe at every scale.** For a curve datum in the strip and every `ℓ > 0` one probe's
`ℓ`-tower has `n` negative squares on some window iff there are at least `n` distinct outer
eigenvalues at `ℓ`. -/
theorem curve_exists_probe_tower_law {ℓ : ℝ} (hℓ : 0 < ℓ) :
    ∃ g : ℝ → ℂ, ContDiff ℝ 2 g ∧ HasCompactSupport g ∧ ∀ n : ℕ,
      (∃ K : Finset ℤ, n ≤ hermNegIndex (towerGram (D.curveConfig hD) g ℓ K)) ↔
        (n : ℕ∞) ≤ (outerEig (D.curveConfig hD) ℓ).encard :=
  exists_probe_tower_law_of_wellFounded_at _ (D.temperedConfig_curveConfig hD)
    (D.wellFoundedOn_re_rightZeros_curveConfig hD) hℓ

/-- **Non-arithmetic towers see an infinite defect.** For a datum with an eigenvalue outside the
unit circle, one probe's tower at scale `ℓ` has arbitrarily many negative squares iff `ℓ/log q` is
irrational. -/
theorem curve_tower_unbounded_iff (hU : D.outerSpectrum.Nonempty) {ℓ : ℝ} (hℓ : 0 < ℓ) :
    ∃ g : ℝ → ℂ, ContDiff ℝ 2 g ∧ HasCompactSupport g ∧
      ((∀ n : ℕ, ∃ K : Finset ℤ, n ≤ hermNegIndex (towerGram (D.curveConfig hD) g ℓ K)) ↔
        Irrational (ℓ / Real.log D.q)) := by
  obtain ⟨g, hg, hgc, hlaw⟩ := D.curve_exists_probe_tower_law hD hℓ
  refine ⟨g, hg, hgc, ?_⟩
  rw [← D.outerEig_curveConfig_infinite_iff hD hU hℓ, ← Set.encard_eq_top_iff]
  constructor
  · intro h
    by_contra hne
    obtain ⟨m, hm⟩ := ENat.ne_top_iff_exists.mp hne
    have := (hlaw (m + 1)).mp (h (m + 1))
    rw [← hm] at this
    exact absurd (ENat.coe_le_coe.mp this) (by omega)
  · intro h n
    exact (hlaw n).mpr (by rw [h]; exact le_top)

/-- **The base change to `𝔽_{q^a}`**: the curve datum with eigenvalues `β_i^a`. -/
def pow (a : ℕ) (ha : 0 < a) : CurveDatum ι where
  q := D.q ^ a
  one_lt_q := one_lt_pow₀ D.one_lt_q ha.ne'
  β := fun i => D.β i ^ a
  conjPerm := D.conjPerm
  β_conjPerm := fun i => by rw [D.β_conjPerm, map_pow]
  fePerm := D.fePerm
  β_fePerm := fun i => by rw [← mul_pow, D.β_fePerm, one_pow]

/-- At scale `a log q` the outer eigenvalues are the outer spectrum of the base change. -/
theorem coe_outerSpectrum_pow {a : ℕ} (ha : 0 < a) :
    ((D.pow a ha).outerSpectrum : Set ℂ) = outerEig (D.curveConfig hD) (a * Real.log D.q) := by
  have e : (a : ℝ) * Real.log D.q = ((a : ℝ) / ((1 : ℕ) : ℝ)) * Real.log D.q := by
    rw [Nat.cast_one, div_one]
  rw [e, D.outerEig_curveConfig_rat hD one_pos (Nat.coprime_one_right a)]
  ext w
  simp only [outerSpectrum, spectrum, Finset.coe_filter, Finset.mem_image, Finset.mem_univ,
    true_and, Set.mem_setOf_eq, pow_one]
  constructor
  · rintro ⟨⟨i, hi⟩, hw⟩
    refine ⟨i, ?_, hi.symm⟩
    rw [← hi] at hw
    change 1 < ‖D.β i ^ a‖ at hw
    rw [norm_pow] at hw
    exact (one_lt_pow_iff_of_nonneg (norm_nonneg _) ha.ne').mp hw
  · rintro ⟨i, hi, hw⟩
    refine ⟨⟨i, hw.symm⟩, ?_⟩
    rw [hw, norm_pow]
    exact one_lt_pow₀ hi ha.ne'

/-- **The `q^a`-tower is the base change.** One probe's tower of the scaling surface at scale
`a log q` has `n` negative squares on some window iff the Frobenius span of the curve over
`𝔽_{q^a}` has at least `n` negative squares. -/
theorem curve_tower_law_baseChange {a : ℕ} (ha : 0 < a) :
    ∃ g : ℝ → ℂ, ContDiff ℝ 2 g ∧ HasCompactSupport g ∧ ∀ n : ℕ,
      (∃ K : Finset ℤ, n ≤ hermNegIndex (towerGram (D.curveConfig hD) g (a * Real.log D.q) K)) ↔
        n ≤ hermNegIndex ((D.pow a ha).spanGram (Fintype.card ι)) := by
  obtain ⟨g, hg, hgc, hlaw⟩ := D.curve_exists_probe_tower_law hD
    (show (0 : ℝ) < a * Real.log D.q from mul_pos (by exact_mod_cast ha) D.log_q_pos)
  refine ⟨g, hg, hgc, fun n => ?_⟩
  rw [hlaw n, (D.pow a ha).pontryagin_law_curve.2 _ le_rfl, ← D.coe_outerSpectrum_pow hD ha,
    Set.encard_coe_eq_coe_finsetCard, ENat.coe_le_coe]

/-- **Unitarity at every scale.** At every scale `ℓ > 0` one probe's tower is positive on every
window iff every eigenvalue lies on the unit circle. -/
theorem curve_unitary_iff_tower_psd {ℓ : ℝ} (hℓ : 0 < ℓ) :
    ∃ g : ℝ → ℂ, ContDiff ℝ 2 g ∧ HasCompactSupport g ∧
      ((∀ i, ‖D.β i‖ = 1) ↔
        ∀ K : Finset ℤ, hermNegIndex (towerGram (D.curveConfig hD) g ℓ K) = 0) := by
  obtain ⟨g, hg, hgc, hlaw⟩ := D.curve_exists_probe_tower_law hD hℓ
  refine ⟨g, hg, hgc, ?_⟩
  have h1 : (∃ K : Finset ℤ, 1 ≤ hermNegIndex (towerGram (D.curveConfig hD) g ℓ K)) ↔
      ¬ ∀ i, ‖D.β i‖ = 1 := by
    rw [hlaw 1, ← D.nonempty_outerSpectrum_iff, ← D.rightZeros_curveConfig_nonempty_iff hD,
      Nat.cast_one, Set.one_le_encard_iff_nonempty]
    exact Set.image_nonempty
  constructor
  · intro hU K
    by_contra hK
    exact (h1.mp ⟨K, Nat.one_le_iff_ne_zero.mpr hK⟩) hU
  · intro hpsd
    by_contra hU
    obtain ⟨K, hK⟩ := h1.mpr hU
    rw [hpsd K] at hK
    exact absurd hK (by norm_num)

end CurveDatum

end GaloisForLFunctions.ArithmeticCastelnuovoSeveri

end
