import GaloisForLFunctions.HTGeometry.CyclicHeatOrbitCountermodels
import GaloisForLFunctions.HTGeometry.PrimeClockGammaTotality
import GaloisForLFunctions.HTGeometry.LpBoundedMultiplier
import GaloisForLFunctions.RHTower.HighExponentShellZeroFree
import GaloisForLFunctions.HTGeometry.ConstraintFrameRelativity.RamificationBooleanSupport
import GaloisForLFunctions.RHTower.SimultaneousPhaseRecurrence
import GaloisForLFunctions.RHTower.HighExponentShellHypertranscendence

/-!
# The literal Euler-shell heat source

Fix a shell level `m ≥ 1` and `σ > 1`.  On the exponent shell
`A_m = {n ≥ 2 : a_m(n) = 1}` (largest prime exponent exactly `m`) put `L e_n = (log n) e_n` and
`v(n) = n^{-σ/2}/√S_m(σ)`, `S_m(σ) = Σ_{n ∈ A_m} n^{-σ}` (**(OG.38)**).  This is a cyclic heat
source, so the whole orbit-Gramian theory applies, and:

* the complex orbit is the normalized shell series, `⟨v, e^{-zL} v⟩ = S_m(σ+z)/S_m(σ)`
  (**(OG.39)**), and `S_m` is the Dirichlet series of the shell indicator;
* the Gramian has kernel `G(n, k) = (nk)^{-σ/2}/(S_m(σ) log(nk))` (**(OG.40)**);
* the imaginary orbit is norm recurrent: `e^{-i t_r L} v → v` along `t_r → ∞` (**(OG.41)–(OG.42)**);
* the reachability map is injective (**(OG.43)–(OG.46)**): `W h = 0` makes `h` orthogonal to every
  `e^{-t log(2^m p)}`, `p` an odd prime, and cofinite prime clocks are total;
* hence the window control is the unique control of `x_T` and `q_G(x_T) = 1/T` exactly
  (**(OG.47)**).
-/

open MeasureTheory Set Filter Topology Complex
open scoped InnerProductSpace ComplexConjugate ENNReal UpperEndDifferentialInstances
  UpperEndComplexTowerInstances

noncomputable section

namespace GaloisForLFunctions.HTGeometry

open _root_.RHTower

/-! ## The exponent shell -/

/-- The exponent shell `A_m = {n ≥ 2 : a_m(n) = 1}`. -/
abbrev EulerShell (m : ℕ) : Type := {n : ℕ // 2 ≤ n ∧ shellIndicator m n = 1}

local notation "ℓ²A" m => lp (fun _ : EulerShell m => ℂ) 2

/-- For every odd prime `p`, `2^m p ∈ A_m` (`m ≥ 1`). -/
theorem two_pow_mul_prime_mem {m : ℕ} (hm : 1 ≤ m) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    2 ≤ 2 ^ m * p ∧ shellIndicator m (2 ^ m * p) = 1 := by
  refine ⟨?_, (shellIndicator_eq_one_iff m _).2 ⟨fun q hq hdvd => ?_, fun h => ?_⟩⟩
  · calc 2 ≤ 2 ^ m := by
          calc 2 = 2 ^ 1 := by norm_num
            _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm
      _ ≤ 2 ^ m * p := Nat.le_mul_of_pos_right _ hp.pos
  · by_cases hq2 : q = 2
    · subst hq2
      rw [pow_succ] at hdvd
      have h2 : 2 ∣ p := (Nat.mul_dvd_mul_iff_left (by positivity)).1 hdvd
      exact hp2 ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).1 h2).symm
    · have hcop : Nat.Coprime (q ^ (m + 1)) (2 ^ m) :=
        Nat.Coprime.pow _ _ ((Nat.coprime_primes hq Nat.prime_two).2 hq2)
      have h1 : q ^ (m + 1) ∣ p := hcop.dvd_of_dvd_mul_left hdvd
      have hqp : q = p := (Nat.prime_dvd_prime_iff_eq hq hp).1
        ((dvd_pow_self q (Nat.succ_ne_zero m)).trans h1)
      subst hqp
      have := Nat.le_of_dvd hp.pos h1
      have h2 : q ^ 2 ≤ q ^ (m + 1) := Nat.pow_le_pow_right hp.pos (by omega)
      nlinarith [hp.two_le]
  · exact h 2 Nat.prime_two (dvd_mul_right _ _)

theorem infinite_eulerShell {m : ℕ} (hm : 1 ≤ m) : Infinite (EulerShell m) := by
  have hinf : {p : ℕ | p.Prime ∧ p ≠ 2}.Infinite :=
    (Nat.infinite_setOf_prime.sdiff (Set.finite_singleton 2)).mono fun p hp => ⟨hp.1, hp.2⟩
  haveI := hinf.to_subtype
  refine Infinite.of_injective (β := {p : ℕ | p.Prime ∧ p ≠ 2})
    (fun p => ⟨2 ^ m * p, two_pow_mul_prime_mem hm p.2.1 p.2.2⟩) fun p q h => ?_
  have h' : 2 ^ m * (p : ℕ) = 2 ^ m * q := congrArg Subtype.val h
  exact Subtype.ext (Nat.eq_of_mul_eq_mul_left (by positivity) h')

/-! ## The shell series -/

/-- The shell sum `S_m(σ) = Σ_{n ∈ A_m} n^{-σ}`. -/
def eulerShellSum (m : ℕ) (σ : ℝ) : ℝ := ∑' n : EulerShell m, ((n : ℕ) : ℝ) ^ (-σ)

theorem summable_shell (m : ℕ) {σ : ℝ} (hσ : 1 < σ) :
    Summable fun n : EulerShell m => ((n : ℕ) : ℝ) ^ (-σ) :=
  (Real.summable_nat_rpow.2 (by linarith)).comp_injective Subtype.val_injective

theorem eulerShellSum_pos {m : ℕ} (hm : 1 ≤ m) {σ : ℝ} (hσ : 1 < σ) : 0 < eulerShellSum m σ := by
  have h3 := two_pow_mul_prime_mem hm Nat.prime_three (by norm_num)
  refine (summable_shell m hσ).tsum_pos (fun n => by positivity) ⟨2 ^ m * 3, h3⟩ ?_
  positivity

/-- The complex shell series `S_m(s) = Σ_{n ∈ A_m} n^{-s}`. -/
def eulerShellSeries (m : ℕ) (s : ℂ) : ℂ := ∑' n : EulerShell m, ((n : ℕ) : ℂ) ^ (-s)

theorem eulerShellSeries_ofReal (m : ℕ) (σ : ℝ) : eulerShellSeries m σ = (eulerShellSum m σ : ℂ) := by
  rw [eulerShellSeries, eulerShellSum, Complex.ofReal_tsum]
  refine tsum_congr fun n => ?_
  rw [Complex.ofReal_cpow (Nat.cast_nonneg _)]
  push_cast
  rfl

/-- `S_m` is the Dirichlet series of the shell indicator `a_m`. -/
theorem eulerShellSeries_eq_LSeries {m : ℕ} (hm : 1 ≤ m) (s : ℂ) :
    eulerShellSeries m s = LSeries (fun n => complexShellIndicator m n) s := by
  rw [eulerShellSeries]
  change ∑' x : ({n : ℕ | 2 ≤ n ∧ shellIndicator m n = 1} : Set ℕ), ((x : ℕ) : ℂ) ^ (-s) = _
  rw [tsum_subtype {n : ℕ | 2 ≤ n ∧ shellIndicator m n = 1} (fun n : ℕ => (n : ℂ) ^ (-s)), LSeries]
  refine tsum_congr fun n => ?_
  rw [LSeries.term_def, complexShellIndicator_apply]
  by_cases hn : 2 ≤ n ∧ shellIndicator m n = 1
  · rw [Set.indicator_of_mem (show n ∈ {n : ℕ | 2 ≤ n ∧ shellIndicator m n = 1} from hn),
      if_neg (by omega), hn.2, Int.cast_one, Complex.cpow_neg, one_div]
  · rw [Set.indicator_of_notMem (show n ∉ {n : ℕ | 2 ≤ n ∧ shellIndicator m n = 1} from hn)]
    by_cases h0 : n = 0
    · simp [h0]
    · rw [if_neg h0]
      rcases shellIndicator_eq_zero_or_one m n with h | h
      · simp [h]
      · exfalso
        have hn1 : n = 1 := by
          by_contra hne
          exact hn ⟨by omega, h⟩
        rw [hn1, HTGeometry.ConstraintFrameRelativity.shellIndicator_one (by omega : m ≠ 0)] at h
        exact zero_ne_one h

/-! ## The Euler-shell source -/

variable {m : ℕ} (hm : 1 ≤ m) {σ : ℝ} (hσ : 1 < σ)

include hm hσ in
theorem memℓp_shellVector :
    Memℓp (fun n : EulerShell m => ((((n : ℕ) : ℝ) ^ (-σ / 2) / Real.sqrt (eulerShellSum m σ) : ℝ) : ℂ)) 2 := by
  refine memℓp_gen ?_
  have hS := eulerShellSum_pos hm hσ
  refine ((summable_shell m hσ).div_const (eulerShellSum m σ)).congr fun n => ?_
  rw [ENNReal.toReal_ofNat, Real.rpow_two, Complex.norm_real, Real.norm_of_nonneg (by positivity),
    div_pow, Real.sq_sqrt hS.le, ← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg _)]
  norm_num

/-- **(OG.38)** The literal Euler-shell cyclic heat source on `ℓ²(A_m)`. -/
def eulerShellSource : CyclicHeatSource (EulerShell m) where
  lam n := Real.log (n : ℕ)
  gap := Real.log 2
  gap_pos := Real.log_pos one_lt_two
  gap_le n := Real.log_le_log two_pos (by exact_mod_cast n.2.1)
  v := ⟨_, memℓp_shellVector hm hσ⟩
  simple a b h := by
    have ha : (0 : ℝ) < (a : ℕ) := by exact_mod_cast (show 0 < (a : ℕ) by omega)
    have hb : (0 : ℝ) < (b : ℕ) := by exact_mod_cast (show 0 < (b : ℕ) by omega)
    exact Subtype.ext (by exact_mod_cast Real.log_injOn_pos ha hb h)
  proper := by
    have h1 : Tendsto (fun n : EulerShell m => (n : ℕ)) cofinite atTop := by
      rw [← Nat.cofinite_eq_atTop]
      exact Subtype.val_injective.tendsto_cofinite
    exact Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop.comp h1)
  fullSupport n := by
    have hS := eulerShellSum_pos hm hσ
    have hn : (0 : ℝ) < (n : ℕ) := by exact_mod_cast (show 0 < (n : ℕ) by omega)
    change ((((n : ℕ) : ℝ) ^ (-σ / 2) / Real.sqrt (eulerShellSum m σ) : ℝ) : ℂ) ≠ 0
    exact Complex.ofReal_ne_zero.2 (by positivity)

theorem eulerShellSource_v (n : EulerShell m) :
    (eulerShellSource hm hσ).v n =
      ((((n : ℕ) : ℝ) ^ (-σ / 2) / Real.sqrt (eulerShellSum m σ) : ℝ) : ℂ) := rfl

theorem eulerShellSource_lam (n : EulerShell m) :
    (eulerShellSource hm hσ).lam n = Real.log (n : ℕ) := rfl

/-- **(OG.38)** The positive/GNS face: `|v_n|² = n^{-σ}/S_m(σ)`, the square-root shell law. -/
theorem norm_sq_eulerShellSource_v (n : EulerShell m) :
    ‖(eulerShellSource hm hσ).v n‖ ^ 2 = ((n : ℕ) : ℝ) ^ (-σ) / eulerShellSum m σ := by
  have hS := eulerShellSum_pos hm hσ
  rw [eulerShellSource_v, Complex.norm_real, Real.norm_of_nonneg (by positivity), div_pow,
    Real.sq_sqrt hS.le, ← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg _)]
  norm_num

/-- `v` is a unit vector. -/
theorem norm_eulerShellSource_v : ‖(eulerShellSource hm hσ).v‖ = 1 := by
  have hS := eulerShellSum_pos hm hσ
  have h : ‖(eulerShellSource hm hσ).v‖ ^ 2 = 1 := by
    rw [lp_two_norm_sq_eq_tsum]
    simp_rw [norm_sq_eulerShellSource_v]
    rw [tsum_div_const, ← eulerShellSum, div_self hS.ne']
  have := norm_nonneg (eulerShellSource hm hσ).v
  nlinarith [sq_nonneg (‖(eulerShellSource hm hσ).v‖ - 1)]

/-! ## The complex orbit -/

theorem norm_natCast_cpow_le_one {n : ℕ} (hn : 1 ≤ n) {z : ℂ} (hz : 0 ≤ z.re) :
    ‖(n : ℂ) ^ (-z)‖ ≤ 1 := by
  rw [Complex.norm_natCast_cpow_of_pos (by omega), Complex.neg_re]
  exact Real.rpow_le_one_of_one_le_of_nonpos (by exact_mod_cast hn) (by linarith)

/-- The complex semigroup `e^{-zL}`, `Re z ≥ 0`: `e_n ↦ n^{-z} e_n`. -/
def shellPhase (z : ℂ) (hz : 0 ≤ z.re) : (ℓ²A m) →L[ℂ] (ℓ²A m) :=
  LpDiagonal.lpDiag (fun n : EulerShell m => ((n : ℕ) : ℂ) ^ (-z)) 1 zero_le_one fun n =>
    norm_natCast_cpow_le_one (by omega) hz

omit hm in
theorem shellPhase_apply (z : ℂ) (hz : 0 ≤ z.re) (x : ℓ²A m) (n : EulerShell m) :
    shellPhase z hz x n = ((n : ℕ) : ℂ) ^ (-z) * x n :=
  LpDiagonal.lpDiag_coe _ _ _ _ _ _

/-- On the real axis the complex semigroup is the heat semigroup: `n^{-t} = e^{-t log n}`. -/
theorem shellPhase_ofReal {t : ℝ} (ht : 0 ≤ t) :
    shellPhase (t : ℂ) (by simpa using ht) = heatSemigroup (eulerShellSource hm hσ).lam_nonneg t := by
  refine ContinuousLinearMap.ext fun x => lp.ext (funext fun n => ?_)
  rw [shellPhase_apply, heatSemigroup_apply, heatFactor_of_nonneg _ ht, eulerShellSource_lam]
  congr 1
  have hn : (0 : ℝ) < (n : ℕ) := by exact_mod_cast (show 0 < (n : ℕ) by omega)
  rw [← Complex.ofReal_natCast, ← Complex.ofReal_neg, ← Complex.ofReal_cpow hn.le, Real.rpow_def_of_pos hn]
  congr 2
  ring

theorem conj_v_mul_v (n : EulerShell m) :
    starRingEnd ℂ ((eulerShellSource hm hσ).v n) * (eulerShellSource hm hσ).v n =
      ((((n : ℕ) : ℝ) ^ (-σ) / eulerShellSum m σ : ℝ) : ℂ) := by
  rw [Complex.conj_mul', ← Complex.ofReal_pow, norm_sq_eulerShellSource_v]

/-- **(OG.39) The complex orbit.**  `Σ_n |v_n|² n^{-z} = S_m(σ+z)/S_m(σ)` for every `z`. -/
theorem tsum_orbit_eq_eulerShellSeries (z : ℂ) :
    ∑' n : EulerShell m, starRingEnd ℂ ((eulerShellSource hm hσ).v n) * (eulerShellSource hm hσ).v n *
        ((n : ℕ) : ℂ) ^ (-z) = eulerShellSeries m (σ + z) / (eulerShellSum m σ : ℂ) := by
  rw [eulerShellSeries, ← tsum_div_const]
  refine tsum_congr fun n => ?_
  have hn : (0 : ℝ) < (n : ℕ) := by exact_mod_cast (show 0 < (n : ℕ) by omega)
  have hn' : ((n : ℕ) : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
  rw [conj_v_mul_v, Complex.ofReal_div, Complex.ofReal_cpow hn.le, neg_add, Complex.cpow_add _ _ hn']
  push_cast
  ring

/-- **(OG.39) The complex orbit.**  `⟨v, e^{-zL} v⟩ = S_m(σ+z)/S_m(σ)` for `Re z ≥ 0`. -/
theorem inner_v_shellPhase (z : ℂ) (hz : 0 ≤ z.re) :
    ⟪(eulerShellSource hm hσ).v, shellPhase z hz (eulerShellSource hm hσ).v⟫_ℂ =
      eulerShellSeries m (σ + z) / (eulerShellSum m σ : ℂ) := by
  rw [lp.inner_eq_tsum, ← tsum_orbit_eq_eulerShellSeries hm hσ z]
  refine tsum_congr fun n => ?_
  rw [shellPhase_apply, RCLike.inner_apply]
  ring

/-- **(OG.40)** The Euler-shell Gramian kernel `G(n, k) = (nk)^{-σ/2}/(S_m(σ) log(nk))`. -/
theorem inner_single_eulerShellGramian (n k : EulerShell m) :
    ⟪(lp.single 2 n (1 : ℂ) : ℓ²A m), (eulerShellSource hm hσ).orbitGramian (lp.single 2 k 1)⟫_ℂ =
      (((((n : ℕ) : ℝ) * (k : ℕ)) ^ (-σ / 2) / (eulerShellSum m σ * Real.log (((n : ℕ) : ℝ) * (k : ℕ))) : ℝ) : ℂ) := by
  have hn : (0 : ℝ) < (n : ℕ) := by exact_mod_cast (show 0 < (n : ℕ) by omega)
  have hk : (0 : ℝ) < (k : ℕ) := by exact_mod_cast (show 0 < (k : ℕ) by omega)
  have hS := eulerShellSum_pos hm hσ
  have e : ((n : ℕ) : ℝ) ^ (-σ / 2) / Real.sqrt (eulerShellSum m σ) *
      (((k : ℕ) : ℝ) ^ (-σ / 2) / Real.sqrt (eulerShellSum m σ)) /
        (Real.log ((n : ℕ) : ℝ) + Real.log ((k : ℕ) : ℝ)) =
      (((n : ℕ) : ℝ) * (k : ℕ)) ^ (-σ / 2) / (eulerShellSum m σ * Real.log (((n : ℕ) : ℝ) * (k : ℕ))) := by
    rw [Real.mul_rpow hn.le hk.le, Real.log_mul hn.ne' hk.ne', div_mul_div_comm,
      Real.mul_self_sqrt hS.le, div_div]
  rw [HeatSource.inner_single_orbitGramian, eulerShellSource_v, eulerShellSource_v, Complex.conj_ofReal,
    eulerShellSource_lam, eulerShellSource_lam, ← Complex.ofReal_mul, ← Complex.ofReal_div, e]

/-! ## The five organs -/

/-- **Real generation.**  `e^{-tL} v_σ = √(S_m(σ+2t)/S_m(σ)) v_{σ+2t}`: the unnormalized Gibbs
shift `σ ↦ σ + 2t`. -/
theorem heatOrbit_eulerShellSource {t : ℝ} (ht : 0 ≤ t) (hσ' : 1 < σ + 2 * t) :
    (eulerShellSource hm hσ).heatOrbit t =
      ((Real.sqrt (eulerShellSum m (σ + 2 * t) / eulerShellSum m σ) : ℝ) : ℂ) • (eulerShellSource hm hσ').v := by
  refine lp.ext (funext fun n => ?_)
  have hn : (0 : ℝ) < (n : ℕ) := by exact_mod_cast (show 0 < (n : ℕ) by omega)
  have hS := eulerShellSum_pos hm hσ
  have hS' := eulerShellSum_pos hm hσ'
  rw [HeatSource.heatOrbit_apply, heatFactor_of_nonneg _ ht, lp.coeFn_smul, Pi.smul_apply,
    eulerShellSource_v, eulerShellSource_v, eulerShellSource_lam, smul_eq_mul]
  rw [← Complex.ofReal_mul, ← Complex.ofReal_mul]
  congr 1
  have h1 := (Real.sqrt_pos.2 hS).ne'
  have h2 := (Real.sqrt_pos.2 hS').ne'
  rw [Real.sqrt_div' _ hS.le, show -(σ + 2 * t) / 2 = -σ / 2 + -t by ring, Real.rpow_add hn,
    Real.rpow_def_of_pos hn (-t), show Real.log ((n : ℕ) : ℝ) * -t = -(t * Real.log ((n : ℕ) : ℝ)) by
      ring]
  field_simp
  rw [div_self (by rw [mul_comm t 2]; exact h2)]

/-- **Phase.**  `e^{-isL} v` has coordinates `n^{-is} v_n`. -/
theorem shellPhase_imag_apply (s : ℝ) (n : EulerShell m) :
    shellPhase ((s : ℂ) * I) (by simp) (eulerShellSource hm hσ).v n =
      ((n : ℕ) : ℂ) ^ (-((s : ℂ) * I)) * (eulerShellSource hm hσ).v n :=
  shellPhase_apply _ _ _ _

include hm in
/-- **Moment face.**  The derivatives of the shell series are log-clock jets:
`S_m^{(k)}(s) = (-1)^k Σ_n (log n)^k a_m(n) n^{-s}`. -/
theorem iteratedDeriv_eulerShellSeries (k : ℕ) {s : ℂ} (hs : 1 < s.re) :
    iteratedDeriv k (eulerShellSeries m) s =
      (-1) ^ k * LSeries (LSeries.logMul^[k] fun n => complexShellIndicator m n) s := by
  have hfun : eulerShellSeries m = LSeries (fun n => complexShellIndicator m n) :=
    funext (eulerShellSeries_eq_LSeries hm)
  rw [hfun]
  have h := LSeries.abscissaOfAbsConv_le_of_le_const_mul_rpow (f := fun n => complexShellIndicator m n)
    (x := 0) ⟨1, fun n _ => by
      rw [Real.rpow_zero, mul_one, complexShellIndicator_apply]
      rcases shellIndicator_eq_zero_or_one m n with h | h <;> simp [h]⟩
  have h2 : LSeries.abscissaOfAbsConv (fun n => complexShellIndicator m n) ≤ ((1 : ℝ) : EReal) := by
    simpa using h
  exact LSeries_iteratedDeriv k (lt_of_le_of_lt h2 (EReal.coe_lt_coe_iff.2 hs))

include hm in
/-- **HT face.**  The shell Dirichlet series is hypertranscendental over `ℂ(s)` (a single member of
the jointly differentially independent shell family). -/
theorem eulerShell_differentialIndependent :
    DifferentialIndependent upperEndRationalCoordinateField
      (fun _ : Unit => highExponentShellUpperEndCarrier m) :=
  highExponentShellUpperEndCarrier_differentialIndependent (fun _ : Unit => m) (fun _ => hm)
    fun _ _ _ => rfl

/-! ## Imaginary recurrence -/

theorem natCast_cpow_neg_mul_I (n : ℕ) (hn : 0 < n) (t : ℝ) :
    (n : ℂ) ^ (-((t : ℂ) * I)) = bohrChar (Real.log n) t := by
  rw [bohrChar, Complex.cpow_def_of_ne_zero (by exact_mod_cast hn.ne'), ← Complex.natCast_log]
  congr 1
  push_cast
  ring

/-- **(OG.41)** For every `ε > 0` and every time `T` there is `t ≥ T` with `‖e^{-itL} v - v‖ < ε`. -/
theorem exists_recurrence {ε : ℝ} (hε : 0 < ε) (T : ℝ) :
    ∃ t, T ≤ t ∧ ‖shellPhase ((t : ℂ) * I) (by simp) (eulerShellSource hm hσ).v -
      (eulerShellSource hm hσ).v‖ < ε := by
  set v := (eulerShellSource hm hσ).v
  have hδ : 0 < ε ^ 2 / 16 := by positivity
  obtain ⟨F, hF⟩ := ((tendsto_tsum_compl_atTop_zero (fun n : EulerShell m => ‖v n‖ ^ 2)).eventually
    (gt_mem_nhds hδ)).exists
  obtain ⟨t, hTt, ht⟩ := exists_simultaneous_phase_recurrence (fun n : F => Real.log ((n : EulerShell m) : ℕ))
    (by positivity : 0 < ε / 2) T
  refine ⟨t, hTt, ?_⟩
  have hcoord : ∀ n : EulerShell m, (shellPhase ((t : ℂ) * I) (by simp) v - v) n =
      (bohrChar (Real.log (n : ℕ)) t - 1) * v n := fun n => by
    rw [lp.coeFn_sub, Pi.sub_apply, shellPhase_apply,
      natCast_cpow_neg_mul_I _ (show 0 < (n : ℕ) by omega)]
    ring
  have hb2 : ∀ n : EulerShell m, ‖bohrChar (Real.log (n : ℕ)) t - 1‖ ≤ 2 := fun n =>
    (norm_sub_le _ _).trans (by rw [GaloisForLFunctions.norm_bohrChar, norm_one]; norm_num)
  set f : EulerShell m → ℝ := fun n => ‖(bohrChar (Real.log (n : ℕ)) t - 1) * v n‖ ^ 2 with hf
  have hfs : Summable f := by
    refine ((summable_norm_sq_lp v).mul_left 4).of_nonneg_of_le (fun _ => sq_nonneg _) fun n => ?_
    simp only [hf, norm_mul, mul_pow]
    refine mul_le_mul_of_nonneg_right ?_ (sq_nonneg _)
    nlinarith [hb2 n, norm_nonneg (bohrChar (Real.log (n : ℕ)) t - 1)]
  have hsq : ‖shellPhase ((t : ℂ) * I) (by simp) v - v‖ ^ 2 = ∑' n, f n := by
    rw [lp_two_norm_sq_eq_tsum]
    exact tsum_congr fun n => by rw [hcoord]
  have hhead : ∑ n ∈ F, f n ≤ ε ^ 2 / 4 := by
    calc ∑ n ∈ F, f n ≤ ∑ n ∈ F, (ε / 2) ^ 2 * ‖v n‖ ^ 2 := by
          refine Finset.sum_le_sum fun n hn => ?_
          simp only [hf, norm_mul, mul_pow]
          refine mul_le_mul_of_nonneg_right ?_ (sq_nonneg _)
          exact pow_le_pow_left₀ (norm_nonneg _) (ht ⟨n, hn⟩) 2
      _ = (ε / 2) ^ 2 * ∑ n ∈ F, ‖v n‖ ^ 2 := by rw [Finset.mul_sum]
      _ ≤ (ε / 2) ^ 2 * 1 := by
          refine mul_le_mul_of_nonneg_left ?_ (sq_nonneg _)
          calc ∑ n ∈ F, ‖v n‖ ^ 2 ≤ ∑' n, ‖v n‖ ^ 2 :=
                Summable.sum_le_tsum _ (fun _ _ => sq_nonneg _) (summable_norm_sq_lp v)
            _ = ‖v‖ ^ 2 := (lp_two_norm_sq_eq_tsum v).symm
            _ = 1 := by rw [norm_eulerShellSource_v]; norm_num
      _ = ε ^ 2 / 4 := by ring
  have hF' : ∑' n : ↑((F : Set (EulerShell m))ᶜ), ‖v n‖ ^ 2 < ε ^ 2 / 16 := hF
  have htail : ∑' n : ↑((F : Set (EulerShell m))ᶜ), f n ≤
      4 * ∑' n : ↑((F : Set (EulerShell m))ᶜ), ‖v n‖ ^ 2 := by
    rw [← tsum_mul_left]
    refine Summable.tsum_le_tsum (fun n => ?_) (hfs.subtype _)
      (((summable_norm_sq_lp v).subtype _).mul_left 4)
    simp only [hf, norm_mul, mul_pow]
    refine mul_le_mul_of_nonneg_right ?_ (sq_nonneg _)
    nlinarith [hb2 n, norm_nonneg (bohrChar (Real.log ((n : EulerShell m) : ℕ)) t - 1)]
  have hlt : ‖shellPhase ((t : ℂ) * I) (by simp) v - v‖ ^ 2 < ε ^ 2 := by
    rw [hsq, ← hfs.sum_add_tsum_compl (s := F)]
    calc ∑ n ∈ F, f n + ∑' n : ↑((F : Set (EulerShell m))ᶜ), f n
        ≤ ε ^ 2 / 4 + 4 * ∑' n : ↑((F : Set (EulerShell m))ᶜ), ‖v n‖ ^ 2 := add_le_add hhead htail
      _ < ε ^ 2 / 4 + 4 * (ε ^ 2 / 16) := by linarith
      _ < ε ^ 2 := by nlinarith
  exact (pow_lt_pow_iff_left₀ (norm_nonneg _) hε.le two_ne_zero).1 hlt

/-- **(OG.42) Norm recurrence.**  There are times `t_r → ∞` with `e^{-i t_r L} v → v`. -/
theorem exists_recurrent_sequence :
    ∃ t : ℕ → ℝ, Tendsto t atTop atTop ∧
      Tendsto (fun r => shellPhase ((t r : ℂ) * I) (by simp) (eulerShellSource hm hσ).v) atTop
        (𝓝 (eulerShellSource hm hσ).v) := by
  choose t ht hdist using fun r : ℕ => exists_recurrence hm hσ (Nat.one_div_pos_of_nat (n := r)) r
  refine ⟨t, tendsto_atTop_mono ht tendsto_natCast_atTop_atTop, ?_⟩
  rw [tendsto_iff_norm_sub_tendsto_zero]
  exact squeeze_zero (fun _ => norm_nonneg _) (fun r => (hdist r).le)
    tendsto_one_div_add_atTop_nhds_zero_nat

/-! ## Injectivity of the shell reachability map -/

theorem gammaCoherentVector_one_congr {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (h : a = b) :
    gammaCoherentVector 1 ha = gammaCoherentVector 1 hb := by
  subst h
  rfl

theorem gammaCoherentProfile_one_eq (b t : ℝ) :
    gammaCoherentProfile 1 b t = Real.sqrt (2 * b) * Real.exp (-(b * t)) := by
  simp [gammaCoherentProfile]

/-- The damping multiplier `e^{-c t}` (time clipped at `0`). -/
def expDampingMultiplier (c : ℝ) (t : ℝ) : ℂ := (Real.exp (-(c * max t 0)) : ℂ)

theorem measurable_expDampingMultiplier (c : ℝ) : Measurable (expDampingMultiplier c) := by
  unfold expDampingMultiplier
  fun_prop

theorem norm_expDampingMultiplier_le {c : ℝ} (hc : 0 ≤ c) (t : ℝ) : ‖expDampingMultiplier c t‖ ≤ 1 := by
  rw [expDampingMultiplier, Complex.norm_real, Real.norm_of_nonneg (Real.exp_nonneg _), Real.exp_le_one_iff]
  have := mul_nonneg hc (le_max_right t 0)
  linarith

/-- Multiplication by `e^{-c t}` on `L²((0,∞))`. -/
def expDampingOperator {c : ℝ} (hc : 0 ≤ c) : HalfLineL2 →L[ℂ] HalfLineL2 :=
  lpBoundedMulCLM (p := 2) (μ := volume.restrict (Ioi (0 : ℝ))) (measurable_expDampingMultiplier c)
    zero_le_one (norm_expDampingMultiplier_le hc)

/-- `⟨ψ_b, e^{-ct} h⟩ = √(b/(b+c)) ⟨ψ_{b+c}, h⟩`. -/
theorem inner_gammaCoherentVector_expDampingOperator {c b : ℝ} (hc : 0 ≤ c) (hb : 0 < b)
    (h : HalfLineL2) :
    ⟪gammaCoherentVector 1 hb, expDampingOperator hc h⟫_ℂ =
      ((Real.sqrt (2 * b) / Real.sqrt (2 * (b + c)) : ℝ) : ℂ) *
        ⟪gammaCoherentVector 1 (by linarith : 0 < b + c), h⟫_ℂ := by
  have hbc : 0 < b + c := by linarith
  rw [MeasureTheory.L2.inner_def, MeasureTheory.L2.inner_def, ← integral_const_mul]
  refine integral_congr_ae ?_
  filter_upwards [gammaCoherentVector_ae 1 hb, gammaCoherentVector_ae 1 hbc,
    lpBoundedMulCLM_coeFn (p := 2) (μ := volume.restrict (Ioi (0 : ℝ))) (measurable_expDampingMultiplier c)
      zero_le_one (norm_expDampingMultiplier_le hc) h,
    ae_restrict_mem measurableSet_Ioi] with t h1 h2 h3 ht
  change ⟪(gammaCoherentVector 1 hb : ℝ → ℂ) t, (expDampingOperator hc h : ℝ → ℂ) t⟫_ℂ = _
  rw [h1, h2, show (expDampingOperator hc h : ℝ → ℂ) t = expDampingMultiplier c t * (h : ℝ → ℂ) t from h3,
    RCLike.inner_apply, RCLike.inner_apply, Complex.conj_ofReal, Complex.conj_ofReal,
    gammaCoherentProfile_one_eq, gammaCoherentProfile_one_eq, expDampingMultiplier,
    max_eq_left (le_of_lt (show (0 : ℝ) < t from ht))]
  have hs := (Real.sqrt_pos.2 (show 0 < 2 * (b + c) by linarith)).ne'
  have hsC : (Real.sqrt (2 * (b + c)) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hs
  rw [show -((b + c) * t) = -(b * t) + -(c * t) by ring, Real.exp_add]
  push_cast
  field_simp

theorem expDampingOperator_injective {c : ℝ} (hc : 0 ≤ c) : Function.Injective (expDampingOperator hc) := by
  rw [injective_iff_map_eq_zero]
  intro h hh
  have hae := lpBoundedMulCLM_coeFn (p := 2) (μ := volume.restrict (Ioi (0 : ℝ)))
    (measurable_expDampingMultiplier c) zero_le_one (norm_expDampingMultiplier_le hc) h
  change (expDampingOperator hc h : ℝ → ℂ) =ᵐ[_] _ at hae
  rw [hh] at hae
  rw [Lp.eq_zero_iff_ae_eq_zero]
  filter_upwards [hae, Lp.coeFn_zero ℂ 2 (volume.restrict (Ioi (0 : ℝ)))] with t h1 h2
  rw [h2, Pi.zero_apply, eq_comm, mul_eq_zero] at h1
  rcases h1 with h1 | h1
  · exact absurd h1 (Complex.ofReal_ne_zero.2 (Real.exp_pos _).ne')
  · exact h1

/-- **(OG.43)–(OG.46)** The Euler-shell reachability map is injective. -/
theorem heatReachability_injective : Function.Injective (eulerShellSource hm hσ).heatReachability := by
  rw [injective_iff_map_eq_zero]
  intro h hh
  set c := (m : ℝ) * Real.log 2 with hcdef
  have hc : 0 ≤ c := mul_nonneg (Nat.cast_nonneg _) (Real.log_nonneg one_le_two)
  have hcoord : ∀ n : EulerShell m, ⟪gammaCoherentVector 1 ((eulerShellSource hm hσ).lam_pos n), h⟫_ℂ = 0 := by
    intro n
    have h1 := congrArg (fun x : (ℓ²A m) => x n) hh
    simp only [lp.coeFn_zero, Pi.zero_apply] at h1
    rw [HeatSource.heatReachability_apply, HeatSource.heatFrame, inner_smul_left] at h1
    have hne : starRingEnd ℂ (starRingEnd ℂ ((eulerShellSource hm hσ).v n) *
        (((Real.sqrt (2 * (eulerShellSource hm hσ).lam n))⁻¹ : ℝ) : ℂ)) ≠ 0 := by
      rw [map_ne_zero]
      refine mul_ne_zero ((map_ne_zero _).2 ((eulerShellSource hm hσ).fullSupport n)) ?_
      exact Complex.ofReal_ne_zero.2 (inv_ne_zero (Real.sqrt_pos.2
        (by linarith [(eulerShellSource hm hσ).lam_pos n])).ne')
    exact (mul_eq_zero.1 h1).resolve_left hne
  have hg : expDampingOperator hc h = 0 := by
    refine eq_zero_of_forall_inner_gammaCoherentVector_eq_zero 1 {⟨2, Nat.prime_two⟩} _ fun p hp => ?_
    have hp2 : (p : ℕ) ≠ 2 := fun h2 => hp (Finset.mem_singleton.2 (Subtype.ext h2))
    rw [inner_gammaCoherentVector_expDampingOperator hc (primeClock_pos p)]
    set n : EulerShell m := ⟨2 ^ m * p, two_pow_mul_prime_mem hm p.2 hp2⟩
    have hlog : Real.log (p : ℝ) + c = (eulerShellSource hm hσ).lam n := by
      rw [eulerShellSource_lam]
      change Real.log (p : ℝ) + c = Real.log (((2 ^ m * (p : ℕ) : ℕ) : ℝ))
      push_cast
      rw [Real.log_mul (by positivity) (by exact_mod_cast p.2.ne_zero), Real.log_pow, hcdef]
      ring
    rw [gammaCoherentVector_one_congr _ ((eulerShellSource hm hσ).lam_pos n) hlog, hcoord n, mul_zero]
  exact expDampingOperator_injective hc (by rw [hg, map_zero])

/-! ## The exact shell atomic wall -/

/-- **(OG.47)** On the Euler shell the window control is the unique control of `x_T`, so
`q_G(x_T) = 1/T` exactly. -/
theorem orbitCostForm_windowPacket_eq {T : ℝ} (hT : 0 < T) :
    (eulerShellSource hm hσ).orbitCostForm ((eulerShellSource hm hσ).windowPacket T) =
      ENNReal.ofReal (1 / T) := by
  refine le_antisymm ((eulerShellSource hm hσ).orbitCostForm_windowPacket_le hT) ?_
  rw [CyclicHeatSource.orbitCostForm_eq_iInf]
  refine le_iInf₂ fun u hu => ?_
  have hu' : u = windowControl T := heatReachability_injective hm hσ
    (hu.trans ((eulerShellSource hm hσ).windowPacket_eq hT))
  rw [hu', norm_windowControl_sq hT]

end GaloisForLFunctions.HTGeometry
