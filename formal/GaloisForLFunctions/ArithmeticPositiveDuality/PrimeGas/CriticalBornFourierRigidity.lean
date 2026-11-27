import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.CriticalBorn.Classification
import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.PartitionConservationRigidity
import GaloisForLFunctions.MetaplecticMobiusDescent.Detector.SubFarkasZeroFreeHalfPlane
import GaloisForLFunctions.RHTower.ThetaNaturalScheduleEulerOscillation
import GaloisForLFunctions.HTGeometry.DirichletSimultaneousApproximation
import GaloisForLFunctions.RHTower.FractionalPartZeta
import GaloisForLFunctions.RHTower.ZetaZeroAbscissa
import GaloisForLFunctions.RHTower.FermiMellinPhaseProperness
import GaloisForLFunctions.InfiniteRankPurityTheory.TheZerosContainNoClassOfOneFrobenius

/-!
# Off-Critical Fourier Rigidity of `bornLaw`, Functional-Equation Single-Mode Bootstrap, and Sub-Farkas Zero Confinement

For `σ, t ∈ ℝ` and `k ∈ ℤ`, let `bornCoefficient σ t k N` be the `k`-th Fourier mode
`circleMeasureMomentZ (bornLaw σ t N : Measure Circle) k` of the `p^{-2σ}`-weighted prime-phase law
`bornLaw σ t N` on `Circle`. At `σ = 1 / 2` and `t ≠ 0`, `CriticalBorn.nonzero_mode` gives
`bornCoefficient (1 / 2) t k N → 0` for every `k ≠ 0`, whereas `CriticalBorn.haar_iff_half` shows
that weak convergence to `uniform` occurs only at `σ = 1 / 2`.

Attacking `ζ(ρ) = 0 ⟹ ∀ k ≠ 0, bornCoefficient ρ.re t k N → 0` without first setting `Re ρ = 1 / 2`
exposes the exact quantitative Fourier behavior across all three exponent regimes together with a
functional-equation single-mode bootstrap and unconditional Sub-Farkas strip confinement:

1. **Exact subcritical rotating-phasor and Lorentzian modulus law (`0 < σ < 1 / 2`, all `k ∈ ℤ`)**:
   `subcritical_bornCoefficient_rotating_phasor` proves
   `bornCoefficient σ t k N - ((1 - 2σ) / ((1 - 2σ) + i k t)) · (phase t (N + 2))^{-k} → 0`
   as `N → ∞`, so even though `bornCoefficient σ t k N` diverges in phase when `k t ≠ 0`, its norm
   converges unconditionally (`subcritical_norm_bornCoefficient_tendsto`) to the positive Lorentzian
   `(1 - 2σ) / √((1 - 2σ)² + (k t)²) > 0`. In particular, **no single nonzero Fourier mode can
   vanish even along a subsequence** (`subcritical_no_subseq_zero_mode`).
2. **Exact supercritical prime-Dirichlet limit and Dirichlet-pigeonhole high-mode recurrence
   (`σ > 1 / 2`)**: `supercritical_bornCoefficient_tendsto` proves convergence as `N → ∞` to
   `supercriticalModeLimit σ t k = (∑'_{p} p^{-2σ} (phase t p)^{-k}) / (∑'_{p} p^{-2σ})`, and
   `supercritical_exists_high_mode_re_gt` uses simultaneous Dirichlet approximation on finite prime
   prefixes to show that for every `ε > 0` and `K₀ : ℕ` (at **every** `t ∈ ℝ`), arbitrarily high
   modes `k > K₀` satisfy `1 - ε < (supercriticalModeLimit σ t k).re`.
3. **Functional-equation single-mode subsequential bootstrap at `ζ(ρ) = 0` (`rh_iff_single_mode_subseq_self_clock`)**:
   every open-strip zero `ρ` of `riemannZeta` has `ρ.im ≠ 0` (`openStrip_zeta_zero_im_ne_zero`),
   giving a canonical self-clock `t = ρ.im`. Because `ζ(ρ) = 0 ⟹ ζ(1 - ρ) = 0` reflects `(1 / 2, 1)`
   onto `(0, 1 / 2)` where **every** nonzero mode `k₀ ≠ 0` has strict Lorentzian norm floor,
   subsequential vanishing of **one single** nonzero mode `k₀ ≠ 0` at strip zeros unconditionally
   forces full-sequence cancellation of **all** nonzero modes `k ≠ 0` and `RiemannHypothesis`,
   reducing via `SubFarkasZeroFreeHalfPlane` to `2401 / 19200 ≤ Re ρ < 1 / 2` and `|Im ρ| > 169 / 2`.
4. **Unconditional low-ordinate cancellation, Sub-Farkas zero exclusion, and Fermi–Mellin overtone
   contrast (`unconditional_bornCoefficient_zero_below_eightyFour_and_half_and_sub_farkas`,
   `fermiMellin_fundamental_cancels_but_overtones_survive`)**: at every open-strip zero with
   `|Im ρ| ≤ 169 / 2` every nonzero `bornCoefficient` vanishes unconditionally, `riemannZeta` is
   zero-free across all heights outside `[2401 / 19200, 16799 / 19200]`, whereas in the additive
   Fermi–Mellin law `fermiMellinMeasure ρ.re` a zero `ζ(ρ) = 0` cancels `k = ±1` at arbitrary `Re ρ`
   while leaving infinitely many overtones `|k| > K₀` nonzero.
-/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.CriticalBorn

open Filter Finset MeasureTheory Real Complex
open GaloisForLFunctions.HTGeometry
open scoped Topology BigOperators

/-! ### Part 1: Fourier modes of `bornLaw` across general real exponents `σ` -/

private theorem bornWeight_nonneg' (σ : ℝ) (p : ℕ) : 0 ≤ bornWeight σ p :=
  Real.rpow_nonneg (Nat.cast_nonneg p) _

private theorem bornMass_pos' (σ : ℝ) (N : ℕ) : 0 < bornMass σ N := by
  apply sum_pos' (fun p _ => bornWeight_nonneg' σ p)
  exact ⟨2, Nat.mem_primesBelow.mpr ⟨by omega, Nat.prime_two⟩,
    Real.rpow_pos_of_pos (by norm_num) _⟩

/-- The `k`-th circle Fourier mode `∫ z^{-k} d(bornLaw σ t N)` of the `p^{-2σ}`-weighted prime
phase ensemble at clock height `t` and cutoff index `N`. -/
def bornCoefficient (σ t : ℝ) (k : ℤ) (N : ℕ) : ℂ :=
  circleMeasureMomentZ (bornLaw σ t N : Measure Circle) k

/-- Explicit normalized prime-sum representation of `bornCoefficient σ t k N`. -/
theorem bornCoefficient_eq_sum (σ t : ℝ) (k : ℤ) (N : ℕ) :
    bornCoefficient σ t k N =
      (∑ p ∈ primes N, (bornWeight σ p : ℂ) * (phase t p : ℂ) ^ (-k)) / (bornMass σ N : ℂ) := by
  rw [bornCoefficient, circleMeasureMomentZ]
  change (∫ z : Circle, (z : ℂ) ^ (-k) ∂(∑ p ∈ primes N,
    (Real.toNNReal (bornWeight σ p / bornMass σ N)) • Measure.dirac (phase t p))) = _
  rw [integral_finsetSum_measure (fun _ _ =>
    (integrable_dirac (by finiteness)).smul_measure_nnreal), Finset.sum_div]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [integral_smul_nnreal_measure, integral_dirac]
  change ((Real.toNNReal (bornWeight σ p / bornMass σ N) : ℝ) : ℂ) * (phase t p : ℂ) ^ (-k) = _
  rw [Real.coe_toNNReal _ (div_nonneg (bornWeight_nonneg' σ p) (bornMass_pos' σ N).le),
    Complex.ofReal_div]
  ring

theorem bornCoefficient_zero_mode (σ t : ℝ) (N : ℕ) : bornCoefficient σ t 0 N = 1 :=
  circleMeasureMomentZ_zero (bornLaw σ t N : Measure Circle)

theorem bornCoefficient_half (t : ℝ) (k : ℤ) (N : ℕ) :
    bornCoefficient (1 / 2) t k N = coefficient t k N := by
  rw [bornCoefficient, bornLaw_half, moment]

/-- Weak convergence of `bornLaw σ t` to `uniform` is equivalent to cancellation of every nonzero
Fourier mode `k ≠ 0`. -/
theorem tendsto_bornLaw_uniform_iff_forall_nonzero_mode (σ t : ℝ) :
    Tendsto (bornLaw σ t) atTop (𝓝 uniform) ↔
      ∀ k : ℤ, k ≠ 0 → Tendsto (bornCoefficient σ t k) atTop (𝓝 0) := by
  rw [isClosedEmbedding_completeCircleMomentSequence.isEmbedding.tendsto_nhds_iff, tendsto_pi_nhds]
  have haar : ∀ k : ℤ, circleMeasureMomentZ (uniform : Measure Circle) k = if k = 0 then 1 else 0 := by
    intro k
    change circleMeasureMomentZ circleLebesgue k = _
    simp only [circleMeasureMomentZ, integral_circleLebesgue_coe_zpow, neg_eq_zero]
  constructor
  · intro h k hk
    simpa only [completeCircleMomentSequence, haar k, if_neg hk, bornCoefficient] using h k
  · intro h k
    change Tendsto (bornCoefficient σ t k) atTop (𝓝 (circleMeasureMomentZ (uniform : Measure Circle) k))
    rw [haar k]
    by_cases hk : k = 0
    · subst hk
      simp only [bornCoefficient_zero_mode, if_true]
      exact tendsto_const_nhds
    · simpa only [if_neg hk] using h k hk

/-! ### Part 2: Exact subcritical rotating-phasor and Lorentzian modulus law (`0 < σ < 1 / 2`) -/

private theorem bornSummand_eq_cpow (σ t : ℝ) (k : ℤ) {p : ℕ} (hp : 0 < p) :
    (bornWeight σ p : ℂ) * (phase t p : ℂ) ^ (-k) =
      (p : ℂ) ^ (-(((2 * σ : ℝ) : ℂ) - (((k : ℝ) * t : ℝ) : ℂ) * I)) := by
  have hp_pos : (0 : ℝ) < p := Nat.cast_pos.mpr hp
  have hp_ne : (p : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hp.ne'
  rw [bornWeight, Real.rpow_def_of_pos hp_pos, Complex.ofReal_exp, phase, Circle.coe_exp,
    ← Complex.exp_int_mul, ← Complex.exp_add, Complex.cpow_def_of_ne_zero hp_ne]
  have hlog : Complex.log (p : ℂ) = (Real.log (p : ℝ) : ℂ) := by
    rw [← Complex.ofReal_natCast, Complex.ofReal_log hp_pos.le]
  rw [hlog]
  congr 1
  push_cast
  ring

private theorem primes_eq_insert_two_Ioc (N : ℕ) :
    primes N = insert 2 ((Finset.Ioc 2 (N + 2)).filter Nat.Prime) := by
  ext p
  simp only [primes, Nat.mem_primesBelow, mem_insert, mem_filter, mem_Ioc]
  constructor
  · rintro ⟨hlt, hp⟩
    by_cases h2 : p = 2
    · exact Or.inl h2
    · exact Or.inr ⟨⟨by have := hp.two_le; omega, by omega⟩, hp⟩
  · rintro (rfl | ⟨⟨_, hle⟩, hp⟩)
    · exact ⟨by omega, Nat.prime_two⟩
    · exact ⟨by omega, hp⟩

private theorem primeSum_eq_two_add_primeCpowSumIoc (σ t : ℝ) (k : ℤ) (N : ℕ) :
    (∑ p ∈ primes N, (bornWeight σ p : ℂ) * (phase t p : ℂ) ^ (-k)) =
      (2 : ℂ) ^ (-(((2 * σ : ℝ) : ℂ) - (((k : ℝ) * t : ℝ) : ℂ) * I)) +
        _root_.RHTower.primeCpowSumIoc (((2 * σ : ℝ) : ℂ) - (((k : ℝ) * t : ℝ) : ℂ) * I)
          ((N + 2 : ℕ) : ℝ) := by
  set s : ℂ := ((2 * σ : ℝ) : ℂ) - (((k : ℝ) * t : ℝ) : ℂ) * I
  rw [primes_eq_insert_two_Ioc N, Finset.sum_insert (by simp)]
  congr 1
  · exact bornSummand_eq_cpow σ t k (by norm_num)
  · rw [_root_.RHTower.primeCpowSumIoc, Nat.floor_natCast, Finset.sum_filter]
    refine Finset.sum_congr rfl fun p _ => ?_
    by_cases hp : p.Prime
    · rw [if_pos hp, if_pos hp]
      exact bornSummand_eq_cpow σ t k hp.pos
    · rw [if_neg hp, if_neg hp]

private theorem cpow_one_sub_div_rpow (a t : ℝ) (k : ℤ) (N : ℕ) :
    (((N + 2 : ℕ) : ℝ) : ℂ) ^ ((a : ℂ) + (((k : ℝ) * t : ℝ) : ℂ) * I) =
      ((((N + 2 : ℕ) : ℝ) ^ a : ℝ) : ℂ) * (phase t (N + 2) : ℂ) ^ (-k) := by
  set x : ℝ := ((N + 2 : ℕ) : ℝ)
  have hx_pos : 0 < x := by positivity
  have hx_ne : (x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hx_pos.ne'
  rw [Complex.cpow_def_of_ne_zero hx_ne, ← Complex.ofReal_log hx_pos.le,
    Real.rpow_def_of_pos hx_pos, Complex.ofReal_exp, phase, Circle.coe_exp,
    ← Complex.exp_int_mul, ← Complex.exp_add]
  congr 1
  dsimp only [x]
  push_cast
  ring

/-- **Exact subcritical rotating-phasor asymptotic:** for every `0 < σ < 1 / 2`, every clock `t ∈ ℝ`,
and every Fourier index `k ∈ ℤ`, `bornCoefficient σ t k N` tracks the rotating terminal cutoff phase
`((1 - 2σ) / ((1 - 2σ) + i k t)) · (phase t (N + 2))^{-k}` up to `o(1)` as `N → ∞`. -/
theorem subcritical_bornCoefficient_rotating_phasor {σ : ℝ} (hσ0 : 0 < σ) (hσ1 : σ < 1 / 2)
    (t : ℝ) (k : ℤ) :
    Tendsto (fun N : ℕ =>
      bornCoefficient σ t k N -
        (((1 - 2 * σ : ℝ) : ℂ) / (((1 - 2 * σ : ℝ) : ℂ) + (((k : ℝ) * t : ℝ) : ℂ) * I)) *
          (phase t (N + 2) : ℂ) ^ (-k)) atTop (𝓝 0) := by
  set a : ℝ := 1 - 2 * σ with ha_def
  have ha0 : 0 < a := by linarith only [ha_def, hσ1]
  have ha1 : a < 1 := by linarith only [ha_def, hσ0]
  set s : ℂ := ((2 * σ : ℝ) : ℂ) - (((k : ℝ) * t : ℝ) : ℂ) * I with hs_def
  have hs_re : s.re = 2 * σ := by simp [hs_def]
  have hs0 : 0 < s.re := by linarith only [hs_re, hσ0]
  have hs1 : s.re < 1 := by linarith only [hs_re, hσ1]
  have h1s_eq : (1 : ℂ) - s = (a : ℂ) + (((k : ℝ) * t : ℝ) : ℂ) * I := by
    rw [hs_def, ha_def]; push_cast; ring
  have h1s_re : 1 - s.re = a := by linarith only [hs_re, ha_def]
  set c : ℂ := (a : ℂ) / (1 - s)
  let x : ℕ → ℝ := fun N => ((N + 2 : ℕ) : ℝ)
  have hx_top : Tendsto x atTop atTop := by
    simpa only [x, Nat.cast_add, Nat.cast_ofNat] using
      tendsto_atTop_add_const_right atTop (2 : ℝ) tendsto_natCast_atTop_atTop
  have hmain_ioc : Tendsto (fun N : ℕ =>
      ‖_root_.RHTower.primeCpowSumIoc s (x N) -
          (x N : ℂ) ^ (1 - s) / ((1 - s) * (Real.log (x N) : ℂ))‖ *
        (a * Real.log (x N)) / (x N) ^ a) atTop (𝓝 0) := by
    have h0 := (_root_.RHTower.tendsto_primeCpowSumIoc_sub_main hs0 hs1).comp hx_top
    have hm := h0.const_mul a
    rw [mul_zero] at hm
    refine hm.congr fun N => ?_
    dsimp only [Function.comp_apply]
    rw [h1s_re]
    ring
  have htwo_tiny : Tendsto (fun N : ℕ =>
      ‖(2 : ℂ) ^ (-s)‖ * (a * Real.log (x N)) / (x N) ^ a) atTop (𝓝 0) := by
    have hlog := ((isLittleO_log_rpow_atTop ha0).tendsto_div_nhds_zero).comp hx_top
    have hm := hlog.const_mul (‖(2 : ℂ) ^ (-s)‖ * a)
    rw [mul_zero] at hm
    exact hm.congr fun N => by dsimp only [Function.comp_apply]; ring
  let A : ℕ → ℂ := fun N =>
    (∑ p ∈ primes N, (bornWeight σ p : ℂ) * (phase t p : ℂ) ^ (-k)) *
      (((a * Real.log (x N) / (x N) ^ a : ℝ) : ℂ))
  let u : ℕ → ℂ := fun N => c * (phase t (N + 2) : ℂ) ^ (-k)
  let R : ℕ → ℝ := fun N => bornMass σ N * (a * Real.log (x N)) / (x N) ^ a
  have hR_lim : Tendsto R atTop (𝓝 1) := by
    have hm := (powerMass_asymptotic ha0 ha1).comp hx_top
    refine hm.congr fun N => ?_
    dsimp only [Function.comp_apply, R, x]
    have hcut : cutoff ((N + 2 : ℕ) : ℝ) = N := by
      unfold cutoff; rw [Nat.floor_natCast]; omega
    rw [powerMass, hcut, bornMass]
    congr 2
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [bornWeight, show a - 1 = -(2 * σ) by linarith only [ha_def]]
  have hA_sub_u : Tendsto (fun N : ℕ => ‖A N - u N‖) atTop (𝓝 0) := by
    refine squeeze_zero (fun _ => norm_nonneg _) (fun N => ?_) (htwo_tiny.add hmain_ioc |>.trans_eq (by simp))
    have hx_gt1 : 1 < x N := by dsimp only [x]; exact_mod_cast (by omega : 1 < N + 2)
    have hlog_pos : 0 < Real.log (x N) := Real.log_pos hx_gt1
    have hlog_ne : (Real.log (x N) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hlog_pos.ne'
    have hxa_pos : 0 < (x N) ^ a := Real.rpow_pos_of_pos (zero_lt_one.trans hx_gt1) a
    have hxa_ne : (((x N) ^ a : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hxa_pos.ne'
    have hscale_pos : 0 ≤ a * Real.log (x N) / (x N) ^ a := by positivity
    have hu_eq : u N = ((x N : ℂ) ^ (1 - s) / ((1 - s) * (Real.log (x N) : ℂ))) *
        (((a * Real.log (x N) / (x N) ^ a : ℝ) : ℂ)) := by
      dsimp only [u, c, x]
      rw [h1s_eq, cpow_one_sub_div_rpow a t k N, ← h1s_eq, Complex.ofReal_div, Complex.ofReal_mul]
      field_simp [hlog_ne, hxa_ne]
    have hdiff : A N - u N =
        ((2 : ℂ) ^ (-s) +
          (_root_.RHTower.primeCpowSumIoc s (x N) -
            (x N : ℂ) ^ (1 - s) / ((1 - s) * (Real.log (x N) : ℂ)))) *
          (((a * Real.log (x N) / (x N) ^ a : ℝ) : ℂ)) := by
      dsimp only [A]
      rw [primeSum_eq_two_add_primeCpowSumIoc, hu_eq]
      ring
    rw [hdiff, norm_mul, Complex.norm_real, Real.norm_of_nonneg hscale_pos]
    calc ‖(2 : ℂ) ^ (-s) + (_root_.RHTower.primeCpowSumIoc s (x N) -
            (x N : ℂ) ^ (1 - s) / ((1 - s) * (Real.log (x N) : ℂ)))‖ *
            (a * Real.log (x N) / (x N) ^ a)
        ≤ (‖(2 : ℂ) ^ (-s)‖ + ‖_root_.RHTower.primeCpowSumIoc s (x N) -
            (x N : ℂ) ^ (1 - s) / ((1 - s) * (Real.log (x N) : ℂ))‖) *
            (a * Real.log (x N) / (x N) ^ a) :=
          mul_le_mul_of_nonneg_right (norm_add_le _ _) hscale_pos
      _ = ‖(2 : ℂ) ^ (-s)‖ * (a * Real.log (x N)) / (x N) ^ a +
          ‖_root_.RHTower.primeCpowSumIoc s (x N) -
            (x N : ℂ) ^ (1 - s) / ((1 - s) * (Real.log (x N) : ℂ))‖ *
            (a * Real.log (x N)) / (x N) ^ a := by ring
  have hmaj : Tendsto (fun N : ℕ => (‖A N - u N‖ + ‖c‖ * |1 - R N|) / |R N|) atTop (𝓝 0) := by
    have h1R : Tendsto (fun N => |1 - R N|) atTop (𝓝 0) := by
      simpa only [sub_self, abs_zero] using (tendsto_const_nhds (x := (1 : ℝ)) |>.sub hR_lim).abs
    have hnum := hA_sub_u.add (h1R.const_mul ‖c‖)
    have hden : Tendsto (fun N => |R N|) atTop (𝓝 1) := by
      simpa only [abs_one] using hR_lim.abs
    simpa using hnum.div hden one_ne_zero
  rw [tendsto_zero_iff_norm_tendsto_zero]
  refine squeeze_zero (fun _ => norm_nonneg _) (fun N => ?_) hmaj
  have hx_gt1 : 1 < x N := by dsimp only [x]; exact_mod_cast (by omega : 1 < N + 2)
  have hlog_pos : 0 < Real.log (x N) := Real.log_pos hx_gt1
  have hxa_pos : 0 < (x N) ^ a := Real.rpow_pos_of_pos (zero_lt_one.trans hx_gt1) a
  have hsc_ne : (((a * Real.log (x N) / (x N) ^ a : ℝ) : ℂ)) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (div_pos (mul_pos ha0 hlog_pos) hxa_pos).ne'
  have hbm_pos := bornMass_pos' σ N
  have hR_pos : 0 < R N := div_pos (mul_pos hbm_pos (mul_pos ha0 hlog_pos)) hxa_pos
  have hR_ne : (R N : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hR_pos.ne'
  have hquot : bornCoefficient σ t k N = A N / (R N : ℂ) := by
    rw [bornCoefficient_eq_sum]
    dsimp only [A, R]
    have hR_eq : (((bornMass σ N * (a * Real.log (x N)) / (x N) ^ a : ℝ) : ℂ)) =
        (bornMass σ N : ℂ) * (((a * Real.log (x N) / (x N) ^ a : ℝ) : ℂ)) := by
      push_cast; ring
    rw [hR_eq, mul_div_mul_right _ _ hsc_ne]
  have hc_eq : (((1 - 2 * σ : ℝ) : ℂ) / (((1 - 2 * σ : ℝ) : ℂ) + (((k : ℝ) * t : ℝ) : ℂ) * I)) *
      (phase t (N + 2) : ℂ) ^ (-k) = u N := by
    dsimp only [u, c]; rw [h1s_eq, ha_def]
  rw [hquot, hc_eq]
  have halg : A N / (R N : ℂ) - u N = ((A N - u N) + u N * (1 - (R N : ℂ))) / (R N : ℂ) := by
    field_simp [hR_ne]; ring
  have hu_norm : ‖u N‖ = ‖c‖ := by
    dsimp only [u]
    rw [norm_mul, norm_zpow, Circle.norm_coe, one_zpow, mul_one]
  rw [halg, norm_div, Complex.norm_real]
  refine div_le_div_of_nonneg_right ?_ (abs_nonneg _)
  calc ‖(A N - u N) + u N * (1 - (R N : ℂ))‖
      ≤ ‖A N - u N‖ + ‖u N * (1 - (R N : ℂ))‖ := norm_add_le _ _
    _ = ‖A N - u N‖ + ‖c‖ * |1 - R N| := by
        rw [norm_mul, hu_norm, ← Complex.ofReal_one, ← Complex.ofReal_sub,
          Complex.norm_real, Real.norm_eq_abs]

/-- **Exact subcritical Lorentzian modulus law:** for every `0 < σ < 1 / 2`, every `t ∈ ℝ`, and
every `k ∈ ℤ`, `‖bornCoefficient σ t k N‖` converges as `N → ∞` to the strictly positive Lorentzian
`(1 - 2σ) / √((1 - 2σ)² + (k t)²)`. -/
theorem subcritical_norm_bornCoefficient_tendsto {σ : ℝ} (hσ0 : 0 < σ) (hσ1 : σ < 1 / 2)
    (t : ℝ) (k : ℤ) :
    Tendsto (fun N : ℕ => ‖bornCoefficient σ t k N‖) atTop
      (𝓝 ((1 - 2 * σ) / Real.sqrt ((1 - 2 * σ) ^ 2 + ((k : ℝ) * t) ^ 2))) := by
  set a : ℝ := 1 - 2 * σ
  set ω : ℝ := (k : ℝ) * t
  have ha0 : 0 < a := by dsimp only [a]; linarith only [hσ1]
  set c : ℂ := (a : ℂ) / ((a : ℂ) + (ω : ℂ) * I)
  have hc_norm : ‖c‖ = a / Real.sqrt (a ^ 2 + ω ^ 2) := by
    dsimp only [c]
    rw [norm_div, Complex.norm_real, Real.norm_of_nonneg ha0.le]
    congr 1
    rw [Complex.norm_eq_sqrt_sq_add_sq]
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im, I_re, I_im,
      mul_zero, sub_zero, add_zero, Complex.add_im, mul_one, zero_add]
  have hphasor := (subcritical_bornCoefficient_rotating_phasor hσ0 hσ1 t k).norm
  rw [norm_zero] at hphasor
  rw [← hc_norm, ← tendsto_sub_nhds_zero_iff]
  refine squeeze_zero_norm (fun N => ?_) hphasor
  have hu_norm : ‖c * (phase t (N + 2) : ℂ) ^ (-k)‖ = ‖c‖ := by
    rw [norm_mul, norm_zpow, Circle.norm_coe, one_zpow, mul_one]
  rw [Real.norm_eq_abs, ← hu_norm]
  exact abs_norm_sub_norm_le (bornCoefficient σ t k N) (c * (phase t (N + 2) : ℂ) ^ (-k))

/-- Below `σ = 1 / 2`, no Fourier mode `k ∈ ℤ` can vanish along **any** unbounded subsequence of
cutoffs `φ : ℕ → ℕ`. -/
theorem subcritical_no_subseq_zero_mode {σ : ℝ} (hσ0 : 0 < σ) (hσ1 : σ < 1 / 2)
    (t : ℝ) (k : ℤ) {φ : ℕ → ℕ} (hφ : Tendsto φ atTop atTop) :
    ¬ Tendsto (fun j : ℕ => bornCoefficient σ t k (φ j)) atTop (𝓝 0) := by
  intro hzero
  have hnorm0 : Tendsto (fun j : ℕ => ‖bornCoefficient σ t k (φ j)‖) atTop (𝓝 0) := by
    simpa only [norm_zero] using hzero.norm
  have hnormL := (subcritical_norm_bornCoefficient_tendsto hσ0 hσ1 t k).comp hφ
  have heq := tendsto_nhds_unique hnorm0 hnormL
  have hpos : 0 < (1 - 2 * σ) / Real.sqrt ((1 - 2 * σ) ^ 2 + ((k : ℝ) * t) ^ 2) :=
    div_pos (by linarith only [hσ1])
      (Real.sqrt_pos.mpr (add_pos_of_pos_of_nonneg (sq_pos_of_pos (by linarith only [hσ1]))
        (sq_nonneg _)))
  linarith only [heq, hpos]

/-! ### Part 3: Supercritical prime-Dirichlet limit and high-mode Bohr recurrence (`σ > 1 / 2`) -/

/-- Prime-Dirichlet numerator `∑_{p prime} p^{-2σ} (phase t p)^{-k}` in the convergent regime `σ > 1 / 2`. -/
def supercriticalPrimeSum (σ t : ℝ) (k : ℤ) : ℂ :=
  ∑' n : ℕ, if n.Prime then (bornWeight σ n : ℂ) * (phase t n : ℂ) ^ (-k) else 0

/-- Total prime Born mass `P(2σ) = ∑_{p prime} p^{-2σ}` for `σ > 1 / 2`. -/
def supercriticalPrimeMass (σ : ℝ) : ℝ :=
  ∑' n : ℕ, if n.Prime then bornWeight σ n else 0

/-- Limiting `k`-th Fourier mode `P(2σ - i k t) / P(2σ)` of `bornLaw σ t` for `σ > 1 / 2`. -/
def supercriticalModeLimit (σ t : ℝ) (k : ℤ) : ℂ :=
  supercriticalPrimeSum σ t k / (supercriticalPrimeMass σ : ℂ)

private theorem summable_supercritical_weight {σ : ℝ} (hσ : 1 / 2 < σ) :
    Summable (fun n : ℕ => if n.Prime then bornWeight σ n else 0) := by
  have hs : Summable (bornWeight σ) := Real.summable_nat_rpow.mpr (by linarith only [hσ])
  refine Summable.of_nonneg_of_le (fun n => ?_) (fun n => ?_) hs
  · split_ifs <;> [exact bornWeight_nonneg' σ n; exact le_rfl]
  · split_ifs <;> [exact le_rfl; exact bornWeight_nonneg' σ n]

private theorem supercriticalPrimeMass_pos {σ : ℝ} (hσ : 1 / 2 < σ) :
    0 < supercriticalPrimeMass σ := by
  have hs := summable_supercritical_weight hσ
  have h2 : 0 < (if Nat.Prime 2 then bornWeight σ 2 else 0) := by
    rw [if_pos Nat.prime_two]; exact Real.rpow_pos_of_pos (by norm_num) _
  exact hs.tsum_pos (fun n => by split_ifs <;> [exact bornWeight_nonneg' σ n; exact le_rfl]) 2 h2

private theorem summable_supercritical_term {σ : ℝ} (hσ : 1 / 2 < σ) (t : ℝ) (k : ℤ) :
    Summable (fun n : ℕ => if n.Prime then (bornWeight σ n : ℂ) * (phase t n : ℂ) ^ (-k) else 0) := by
  refine Summable.of_norm_bounded (summable_supercritical_weight hσ) fun n => ?_
  split_ifs with hp
  · rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (bornWeight_nonneg' σ n),
      norm_zpow, Circle.norm_coe, one_zpow, mul_one]
  · rw [norm_zero]

/-- Above `σ = 1 / 2`, every Fourier mode `bornCoefficient σ t k N` converges as `N → ∞` to the
prime-Dirichlet quotient `supercriticalModeLimit σ t k`. -/
theorem supercritical_bornCoefficient_tendsto {σ : ℝ} (hσ : 1 / 2 < σ) (t : ℝ) (k : ℤ) :
    Tendsto (bornCoefficient σ t k) atTop (𝓝 (supercriticalModeLimit σ t k)) := by
  have hnum_lim := (summable_supercritical_term hσ t k).hasSum.tendsto_sum_nat.comp
    (tendsto_add_atTop_nat 3)
  have hden_lim := (Complex.continuous_ofReal.tendsto (supercriticalPrimeMass σ)).comp
    ((summable_supercritical_weight hσ).hasSum.tendsto_sum_nat.comp (tendsto_add_atTop_nat 3))
  have hquot := hnum_lim.div hden_lim
    (Complex.ofReal_ne_zero.mpr (supercriticalPrimeMass_pos hσ).ne')
  refine hquot.congr fun N => ?_
  dsimp only [Function.comp_apply]
  rw [bornCoefficient_eq_sum]
  have hprimes_range : primes N = (Finset.range (N + 3)).filter Nat.Prime := by
    ext p; simp [primes, Nat.mem_primesBelow]
  rw [hprimes_range, ← Finset.sum_filter, ← Finset.sum_filter, Complex.ofReal_sum]
  congr 2
  refine Finset.sum_congr rfl fun n _ => ?_
  split_ifs <;> simp

/-- **Supercritical high-mode Bohr recurrence:** for every `σ > 1 / 2`, **every** `t ∈ ℝ`
(with no irrationality hypothesis), every `ε > 0`, and every threshold `K₀ : ℕ`, there exists an
integer mode `k > K₀` whose limiting Fourier coefficient satisfies
`1 - ε < (supercriticalModeLimit σ t k).re` and `‖supercriticalModeLimit σ t k‖ ≤ 1`. -/
theorem supercritical_exists_high_mode_re_gt {σ : ℝ} (hσ : 1 / 2 < σ) (t : ℝ)
    {ε : ℝ} (hε : 0 < ε) (K₀ : ℕ) :
    ∃ k : ℕ, K₀ < k ∧
      1 - ε < (supercriticalModeLimit σ t (k : ℤ)).re ∧
      ‖supercriticalModeLimit σ t (k : ℤ)‖ ≤ 1 := by
  let w : ℕ → ℝ := fun n => if n.Prime then bornWeight σ n else 0
  have hw_nonneg : ∀ n, 0 ≤ w n := fun n => by
    dsimp only [w]; split_ifs <;> [exact bornWeight_nonneg' σ n; exact le_rfl]
  have hw_sum : Summable w := summable_supercritical_weight hσ
  have hM_pos : 0 < supercriticalPrimeMass σ := supercriticalPrimeMass_pos hσ
  set δ : ℝ := min (ε / 2) (1 / 2)
  have hδ_pos : 0 < δ := lt_min (half_pos hε) (by norm_num)
  have hδ_half : δ ≤ 1 / 2 := min_le_right _ _
  have h2δ_le : 2 * δ ≤ ε := by
    have h1 : δ ≤ ε / 2 := min_le_left _ _
    linarith only [h1]
  -- Choose a finite prime prefix `range R` leaving tail mass `< (δ / 2) * M`.
  have htail_lim : Tendsto (fun R : ℕ => supercriticalPrimeMass σ - ∑ n ∈ Finset.range R, w n)
      atTop (𝓝 0) := by
    simpa only [sub_self] using
      (tendsto_const_nhds (x := supercriticalPrimeMass σ)).sub hw_sum.hasSum.tendsto_sum_nat
  obtain ⟨R, hR_tail⟩ := (htail_lim.eventually (gt_mem_nhds (mul_pos (half_pos hδ_pos) hM_pos))).exists
  -- Choose Dirichlet resolution `Q ≥ 1` with `2 * π^2 / Q^2 < δ`.
  let Q : ℕ := ⌈Real.sqrt (2 * Real.pi ^ 2 / δ)⌉₊ + 1
  have hQ1 : 1 ≤ Q := by dsimp only [Q]; omega
  have hQ_bound : 2 * Real.pi ^ 2 / (Q : ℝ) ^ 2 < δ := by
    have hsq_pos : 0 < 2 * Real.pi ^ 2 / δ := div_pos (by positivity) hδ_pos
    have hlt_Q : Real.sqrt (2 * Real.pi ^ 2 / δ) < (Q : ℝ) := by
      dsimp only [Q]
      push_cast
      linarith only [Nat.le_ceil (Real.sqrt (2 * Real.pi ^ 2 / δ))]
    have hsq_lt : 2 * Real.pi ^ 2 / δ < (Q : ℝ) ^ 2 := by
      have h := pow_lt_pow_left₀ hlt_Q (Real.sqrt_nonneg _) two_ne_zero
      rwa [Real.sq_sqrt hsq_pos.le] at h
    have hQ2_pos : 0 < (Q : ℝ) ^ 2 := by positivity
    exact (div_lt_iff₀ hQ2_pos).mpr ((div_lt_iff₀ hδ_pos).mp hsq_lt |>.trans_eq (mul_comm _ _))
  -- Apply Dirichlet simultaneous phase approximation on `Fin R` with step `(K₀ + 1) * t`.
  obtain ⟨q, hq1, _, hcos⟩ := exists_dirichlet_phase (ι := Fin R)
    (fun i => Real.log (i.val : ℝ)) (((K₀ + 1 : ℕ) : ℝ) * t) Q hQ1
  let k : ℕ := q * (K₀ + 1)
  have hk_gt : K₀ < k := by
    have h1 : 1 * (K₀ + 1) ≤ q * (K₀ + 1) := Nat.mul_le_mul_right (K₀ + 1) hq1
    dsimp only [k]; omega
  refine ⟨k, hk_gt, ?_, ?_⟩
  · -- Lower-bound the real part by splitting `ℕ` at `R`.
    let f : ℕ → ℂ := fun n => if n.Prime then (bornWeight σ n : ℂ) * (phase t n : ℂ) ^ (-(k : ℤ)) else 0
    have hf_sum : Summable f := summable_supercritical_term hσ t (k : ℤ)
    have hf_re : ∀ n : ℕ, (f n).re = w n * Real.cos (Real.log (n : ℝ) * ((q : ℝ) * (((K₀ + 1 : ℕ) : ℝ) * t))) := by
      intro n
      dsimp only [f, w]
      split_ifs with hp
      · have hph : (phase t n : ℂ) ^ (-(k : ℤ)) =
            Complex.exp (((Real.log (n : ℝ) * ((q : ℝ) * (((K₀ + 1 : ℕ) : ℝ) * t)) : ℝ) : ℂ) * I) := by
          rw [phase, Circle.coe_exp, ← Complex.exp_int_mul]
          congr 1
          dsimp only [k]
          push_cast
          ring
        rw [hph, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero,
          Complex.exp_ofReal_mul_I_re]
      · simp
    have hre_sum : (supercriticalPrimeSum σ t (k : ℤ)).re = ∑' n : ℕ, (f n).re :=
      Complex.re_tsum hf_sum
    have hf_re_summable : Summable (fun n => (f n).re) := Complex.reCLM.summable hf_sum
    have hsplit_f := (sum_add_tsum_nat_add R hf_re_summable).symm
    have hsplit_w := (sum_add_tsum_nat_add R hw_sum).symm
    have htail_eq : (∑' n : ℕ, w (n + R)) = supercriticalPrimeMass σ - ∑ n ∈ Finset.range R, w n := by
      change _ = (∑' n : ℕ, w n) - _
      linarith only [hsplit_w]
    have hhead_ge : (1 - δ) * (∑ n ∈ Finset.range R, w n) ≤ ∑ n ∈ Finset.range R, (f n).re := by
      rw [Finset.mul_sum]
      refine Finset.sum_le_sum fun n hn => ?_
      rw [hf_re n, mul_comm (1 - δ)]
      refine mul_le_mul_of_nonneg_left ?_ (hw_nonneg n)
      have hc := (hcos ⟨n, Finset.mem_range.mp hn⟩).1
      linarith only [hc, hQ_bound]
    have htail_ge : -(∑' n : ℕ, w (n + R)) ≤ ∑' n : ℕ, (f (n + R)).re := by
      rw [← hw_sum.comp_injective (add_left_injective R) |>.tsum_neg]
      refine (hw_sum.comp_injective (add_left_injective R)).neg.tsum_le_tsum (fun n => ?_)
        (hf_re_summable.comp_injective (add_left_injective R))
      rw [hf_re (n + R)]
      have hc := Real.neg_one_le_cos (Real.log ((n + R : ℕ) : ℝ) * ((q : ℝ) * (((K₀ + 1 : ℕ) : ℝ) * t)))
      nlinarith only [hw_nonneg (n + R), hc]
    set T_rem : ℝ := supercriticalPrimeMass σ - ∑ n ∈ Finset.range R, w n
    have hnum_gt : (1 - ε) * supercriticalPrimeMass σ < (supercriticalPrimeSum σ t (k : ℤ)).re := by
      rw [hre_sum, hsplit_f]
      have hhead_T : (∑ n ∈ Finset.range R, w n) = supercriticalPrimeMass σ - T_rem := by
        dsimp only [T_rem]; ring
      have h1_δ_nonneg : 0 ≤ 1 - δ := by linarith only [hδ_half]
      have hT_nonneg : 0 ≤ T_rem := by
        rw [← htail_eq]
        exact tsum_nonneg fun n => hw_nonneg (n + R)
      calc (1 - ε) * supercriticalPrimeMass σ
          ≤ (1 - 2 * δ) * supercriticalPrimeMass σ :=
            mul_le_mul_of_nonneg_right (by linarith only [h2δ_le]) hM_pos.le
        _ < (1 - δ) * (supercriticalPrimeMass σ - T_rem) - T_rem := by
            have h2T : (2 - δ) * T_rem < δ * supercriticalPrimeMass σ := by
              calc (2 - δ) * T_rem ≤ 2 * T_rem :=
                    mul_le_mul_of_nonneg_right (by linarith only [hδ_pos]) hT_nonneg
                _ < 2 * (δ / 2 * supercriticalPrimeMass σ) :=
                    mul_lt_mul_of_pos_left hR_tail zero_lt_two
                _ = δ * supercriticalPrimeMass σ := by ring
            linarith only [h2T]
        _ ≤ (∑ n ∈ Finset.range R, (f n).re) + ∑' n : ℕ, (f (n + R)).re := by
            rw [← hhead_T, ← htail_eq] at *
            linarith only [hhead_ge, htail_ge]
    rw [supercriticalModeLimit, Complex.div_ofReal_re, lt_div_iff₀ hM_pos]
    exact hnum_gt
  · -- Norm bound `≤ 1` by triangle inequality on `supercriticalPrimeSum`.
    rw [supercriticalModeLimit, norm_div, Complex.norm_real, Real.norm_of_nonneg hM_pos.le,
      div_le_one hM_pos]
    refine tsum_of_norm_bounded hw_sum.hasSum fun n => ?_
    split_ifs with hp
    · rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (bornWeight_nonneg' σ n),
        norm_zpow, Circle.norm_coe, one_zpow, mul_one]
    · rw [norm_zero]; exact hw_nonneg n

/-! ### Part 4: Self-clocked strip zeros, functional-equation single-mode bootstrap, and Sub-Farkas confinement -/

/-- Every zero of `riemannZeta` in the open critical strip `0 < Re ρ < 1` has nonzero ordinate
`ρ.im ≠ 0`, supplying a canonical nonzero self-clock `t = ρ.im`. -/
theorem openStrip_zeta_zero_im_ne_zero (ρ : OpenStrip) (hζ : riemannZeta ρ.val = 0) :
    ρ.val.im ≠ 0 := by
  intro him0
  have hreal : ρ.val = (ρ.val.re : ℂ) := by
    apply Complex.ext <;> simp [him0]
  rw [hreal] at hζ
  exact _root_.RHTower.riemannZeta_ne_zero_of_ofReal_mem_Ioo ρ.property.1 ρ.property.2 hζ

/-- **Functional-equation single-mode subsequential bootstrap and Sub-Farkas reduction:**
for **any single** nonzero Fourier mode `k₀ ∈ ℤ \ {0}`, the following are unconditionally equivalent:
1. `RiemannHypothesis`;
2. **All-mode full-sequence cancellation at every strip zero's self-clock `t = ρ.im`:**
   `∀ ρ : OpenStrip, riemannZeta ρ.val = 0 → ∀ k ≠ 0, Tendsto (bornCoefficient ρ.val.re ρ.val.im k) atTop (𝓝 0)`;
3. **Single-mode subsequential cancellation at every strip zero's self-clock `t = ρ.im`:**
   `∀ ρ : OpenStrip, riemannZeta ρ.val = 0 → ∃ φ : ℕ → ℕ, Tendsto φ atTop atTop ∧ Tendsto (fun j => bornCoefficient ρ.val.re ρ.val.im k₀ (φ j)) atTop (𝓝 0)`;
4. **Left Sub-Farkas above-`84.5` sub-Lorentzian bound for the single mode `k₀`:**
   for every `ρ` with `2401 / 19200 ≤ Re ρ < 1 / 2`, `169 / 2 < |Im ρ|`, and `riemannZeta ρ = 0`,
   some unbounded subsequence `φ` beats `(1 - 2 Re ρ) / √((1 - 2 Re ρ)² + (k₀ Im ρ)²)`. -/
theorem rh_iff_single_mode_subseq_self_clock {k₀ : ℤ} (hk₀ : k₀ ≠ 0) :
    (RiemannHypothesis ↔
      ∀ ρ : OpenStrip, riemannZeta ρ.val = 0 →
        ∀ k : ℤ, k ≠ 0 → Tendsto (bornCoefficient ρ.val.re ρ.val.im k) atTop (𝓝 0)) ∧
    (RiemannHypothesis ↔
      ∀ ρ : OpenStrip, riemannZeta ρ.val = 0 →
        ∃ φ : ℕ → ℕ, Tendsto φ atTop atTop ∧
          Tendsto (fun j : ℕ => bornCoefficient ρ.val.re ρ.val.im k₀ (φ j)) atTop (𝓝 0)) ∧
    (RiemannHypothesis ↔
      ∀ ρ : ℂ, 2401 / 19200 ≤ ρ.re → ρ.re < 1 / 2 → 169 / 2 < |ρ.im| → riemannZeta ρ = 0 →
        ∃ φ : ℕ → ℕ, Tendsto φ atTop atTop ∧
          ∃ c : ℝ, c < (1 - 2 * ρ.re) / Real.sqrt ((1 - 2 * ρ.re) ^ 2 + ((k₀ : ℝ) * ρ.im) ^ 2) ∧
            ∀ᶠ j : ℕ in atTop, ‖bornCoefficient ρ.re ρ.im k₀ (φ j)‖ ≤ c) := by
  have h12 : RiemannHypothesis →
      ∀ ρ : OpenStrip, riemannZeta ρ.val = 0 →
        ∀ k : ℤ, k ≠ 0 → Tendsto (bornCoefficient ρ.val.re ρ.val.im k) atTop (𝓝 0) := by
    intro hRH ρ hζ k hk
    have him_ne := openStrip_zeta_zero_im_ne_zero ρ hζ
    have hhaar1 := (rh_iff_unit_clock.mp hRH) ρ hζ
    have hre_half : ρ.val.re = 1 / 2 := (haar_iff_half ρ.val.re one_ne_zero).mp hhaar1
    rw [hre_half]
    simpa only [bornCoefficient_half] using nonzero_mode ρ.val.im him_ne k hk
  have h23 : (∀ ρ : OpenStrip, riemannZeta ρ.val = 0 →
        ∀ k : ℤ, k ≠ 0 → Tendsto (bornCoefficient ρ.val.re ρ.val.im k) atTop (𝓝 0)) →
      (∀ ρ : OpenStrip, riemannZeta ρ.val = 0 →
        ∃ φ : ℕ → ℕ, Tendsto φ atTop atTop ∧
          Tendsto (fun j : ℕ => bornCoefficient ρ.val.re ρ.val.im k₀ (φ j)) atTop (𝓝 0)) :=
    fun hall ρ hζ => ⟨id, tendsto_id, hall ρ hζ k₀ hk₀⟩
  have h34 : (∀ ρ : OpenStrip, riemannZeta ρ.val = 0 →
        ∃ φ : ℕ → ℕ, Tendsto φ atTop atTop ∧
          Tendsto (fun j : ℕ => bornCoefficient ρ.val.re ρ.val.im k₀ (φ j)) atTop (𝓝 0)) →
      (∀ ρ : ℂ, 2401 / 19200 ≤ ρ.re → ρ.re < 1 / 2 → 169 / 2 < |ρ.im| → riemannZeta ρ = 0 →
        ∃ φ : ℕ → ℕ, Tendsto φ atTop atTop ∧
          ∃ c : ℝ, c < (1 - 2 * ρ.re) / Real.sqrt ((1 - 2 * ρ.re) ^ 2 + ((k₀ : ℝ) * ρ.im) ^ 2) ∧
            ∀ᶠ j : ℕ in atTop, ‖bornCoefficient ρ.re ρ.im k₀ (φ j)‖ ≤ c) := by
    intro hsub ρ hlo hhi _ hζ
    obtain ⟨φ, hφ, hlim⟩ := hsub ⟨ρ, by linarith only [hlo], by linarith only [hhi]⟩ hζ
    set L : ℝ := (1 - 2 * ρ.re) / Real.sqrt ((1 - 2 * ρ.re) ^ 2 + ((k₀ : ℝ) * ρ.im) ^ 2)
    have hL_pos : 0 < L := div_pos (by linarith only [hhi])
      (Real.sqrt_pos.mpr (add_pos_of_pos_of_nonneg (sq_pos_of_pos (by linarith only [hhi]))
        (sq_nonneg _)))
    have hnorm0 : Tendsto (fun j => ‖bornCoefficient ρ.re ρ.im k₀ (φ j)‖) atTop (𝓝 0) := by
      simpa only [norm_zero] using hlim.norm
    refine ⟨φ, hφ, L / 2, half_lt_self hL_pos, ?_⟩
    filter_upwards [hnorm0.eventually (gt_mem_nhds (half_pos hL_pos))] with j hj
    exact hj.le
  have h41 : (∀ ρ : ℂ, 2401 / 19200 ≤ ρ.re → ρ.re < 1 / 2 → 169 / 2 < |ρ.im| → riemannZeta ρ = 0 →
        ∃ φ : ℕ → ℕ, Tendsto φ atTop atTop ∧
          ∃ c : ℝ, c < (1 - 2 * ρ.re) / Real.sqrt ((1 - 2 * ρ.re) ^ 2 + ((k₀ : ℝ) * ρ.im) ^ 2) ∧
            ∀ᶠ j : ℕ in atTop, ‖bornCoefficient ρ.re ρ.im k₀ (φ j)‖ ≤ c) →
      RiemannHypothesis := by
    intro hleft
    rw [_root_.RHTower.riemannHypothesis_iff_riemannZeta_ne_zero_of_mem_upper_strip]
    intro w hw_half hw_one hζw
    have hw_pos : 0 < w.re := by linarith only [hw_half]
    -- First rule out `|w.im| ≤ 169 / 2` unconditionally.
    by_cases him_le : |w.im| ≤ 169 / 2
    · have hw_ne1 : w ≠ 1 := fun he => hw_one.ne (by rw [he, Complex.one_re])
      have hxi : _root_.RHTower.xi w = 0 := (_root_.RHTower.xi_eq_zero_iff hw_pos hw_ne1).mpr hζw
      have hgt := VerifiedHeightRungs.lt_abs_im_of_rhVerifiedThrough
        VerifiedHeightRungs.HadamardBudget.rhVerifiedThrough_oneHundredSixtyNine_halves
        hxi hw_pos hw_one hw_half.ne'
      linarith only [him_le, hgt]
    · -- Above `169 / 2`, confine `w.re ≤ 16799 / 19200` via Stage-1 Sub-Farkas and reflect `ρ := 1 - w`.
      have him_gt : 169 / 2 < |w.im| := lt_of_not_ge him_le
      have hstrip := MetaplecticMobiusDescent.CubicEisenstein.riemannZeta_zero_mem_sub_farkas_strip
        hw_pos hζw
      set ρ : ℂ := 1 - w
      have hρ_re : ρ.re = 1 - w.re := by simp [ρ]
      have hρ_im : |ρ.im| = |w.im| := by
        simp only [ρ, Complex.sub_im, Complex.one_im, zero_sub, abs_neg]
      have hρ_pos : 0 < ρ.re := by linarith only [hρ_re, hw_one]
      have hρ_lo : 2401 / 19200 ≤ ρ.re := by linarith only [hρ_re, hstrip.2]
      have hρ_hi : ρ.re < 1 / 2 := by linarith only [hρ_re, hw_half]
      have hρ_im_gt : 169 / 2 < |ρ.im| := by rwa [hρ_im]
      have hζρ : riemannZeta ρ = 0 :=
        _root_.RHTower.riemannZeta_one_sub_eq_zero_of_mem_openStrip hζw hw_pos hw_one
      obtain ⟨φ, hφ, c, hc_lt, hev_le⟩ := hleft ρ hρ_lo hρ_hi hρ_im_gt hζρ
      have hnormL := (subcritical_norm_bornCoefficient_tendsto hρ_pos hρ_hi ρ.im k₀).comp hφ
      have hev_gt := hnormL.eventually (lt_mem_nhds hc_lt)
      obtain ⟨j, hj_le, hj_gt⟩ := (hev_le.and hev_gt).exists
      dsimp only [Function.comp_apply] at hj_gt
      linarith only [hj_le, hj_gt]
  exact ⟨⟨h12, fun h => h41 (h34 (h23 h))⟩,
    ⟨fun h => h23 (h12 h), fun h => h41 (h34 h)⟩,
    ⟨fun h => h34 (h23 (h12 h)), h41⟩⟩

/-! ### Part 5: Unconditional Fourier cancellation below `84.5`, Sub-Farkas zero-free boundaries, and Fermi–Mellin overtone contrast -/

/-- **Unconditional Fourier-mode cancellation through height `84.5` and Sub-Farkas strip
confinement across all heights:**
1. Every open-strip zero `ρ` of `riemannZeta` with `|Im ρ| ≤ 169 / 2` unconditionally cancels
   **every** nonzero Fourier mode `bornCoefficient ρ.val.re t k` (`k ≠ 0`) at **every** nonzero
   clock `t ≠ 0` (including the self-clock `t = ρ.val.im`), without assuming `Re ρ = 1 / 2`;
2. Unconditionally across **all** heights `Im s ∈ ℝ`, `riemannZeta` has no zeros with
   `0 < Re s < 2401 / 19200` or `16799 / 19200 < Re s` (`2401 / 19200 > 3001 / 24000`,
   `16799 / 19200 < 40535 / 46328 < 20999 / 24000`). -/
theorem unconditional_bornCoefficient_zero_below_eightyFour_and_half_and_sub_farkas :
    (∀ ρ : OpenStrip, |ρ.val.im| ≤ 169 / 2 → riemannZeta ρ.val = 0 →
      ρ.val.im ≠ 0 ∧
      ∀ {t : ℝ}, t ≠ 0 → ∀ {k : ℤ}, k ≠ 0 →
        Tendsto (bornCoefficient ρ.val.re t k) atTop (𝓝 0)) ∧
    (∀ s : ℂ, 0 < s.re → (s.re < 2401 / 19200 ∨ 16799 / 19200 < s.re) → riemannZeta s ≠ 0) := by
  refine ⟨fun ρ him hζ => ?_, fun s hs0 hout => ?_⟩
  · have him_ne := openStrip_zeta_zero_im_ne_zero ρ hζ
    have hs1 : ρ.val ≠ 1 := fun he => ρ.property.2.ne (by rw [he, Complex.one_re])
    have hxi : _root_.RHTower.xi ρ.val = 0 :=
      (_root_.RHTower.xi_eq_zero_iff ρ.property.1 hs1).mpr hζ
    have hre_half : ρ.val.re = 1 / 2 := by
      by_contra hne
      have hgt := VerifiedHeightRungs.lt_abs_im_of_rhVerifiedThrough
        VerifiedHeightRungs.HadamardBudget.rhVerifiedThrough_oneHundredSixtyNine_halves
        hxi ρ.property.1 ρ.property.2 hne
      linarith only [him, hgt]
    refine ⟨him_ne, fun {t} ht {k} hk => ?_⟩
    rw [hre_half]
    simpa only [bornCoefficient_half] using nonzero_mode t ht k hk
  · rcases hout with hlt | hgt
    · exact MetaplecticMobiusDescent.CubicEisenstein.riemannZeta_ne_zero_of_re_lt_sub_farkas_left hs0 hlt
    · exact MetaplecticMobiusDescent.CubicEisenstein.riemannZeta_ne_zero_of_sub_farkas_lt_re hgt

/-- **Additive Fermi–Mellin vs. multiplicative prime-Born contrast at an arbitrary strip zero
(without setting `Re ρ = 1 / 2`):** for **every** `ρ : OpenStrip` with `riemannZeta ρ.val = 0`
(at arbitrary height), in the Fermi–Mellin observer law `fermiMellinMeasure ρ.val.re`:
1. Both fundamental modes `k = 1` and `k = -1` at the self-clock `ρ.val.im` vanish unconditionally;
2. Infinitely many higher harmonic overtones `k ∈ ℤ` (`|k| > K₀`) are strictly nonzero. -/
theorem fermiMellin_fundamental_cancels_but_overtones_survive
    (ρ : OpenStrip) (hζ : riemannZeta ρ.val = 0) :
    (∫ t : ℝ, Complex.exp (((1 : ℤ) * ρ.val.im : ℂ) * (Real.log t : ℂ) * I)
        ∂(_root_.RHTower.fermiMellinMeasure ρ.val.re)) = 0 ∧
    (∫ t : ℝ, Complex.exp (((-1 : ℤ) * ρ.val.im : ℂ) * (Real.log t : ℂ) * I)
        ∂(_root_.RHTower.fermiMellinMeasure ρ.val.re)) = 0 ∧
    ∀ K₀ : ℕ, ∃ k : ℤ, (K₀ : ℤ) < |k| ∧
      (∫ t : ℝ, Complex.exp (((k : ℝ) * ρ.val.im : ℝ) * (Real.log t : ℂ) * I)
        ∂(_root_.RHTower.fermiMellinMeasure ρ.val.re)) ≠ 0 := by
  have hσ0 : 0 < ρ.val.re := ρ.property.1
  have hσ1 : ρ.val.re < 1 := ρ.property.2
  have him_ne : ρ.val.im ≠ 0 := openStrip_zeta_zero_im_ne_zero ρ hζ
  have hρ_eq : (ρ.val.re : ℂ) + (ρ.val.im : ℂ) * I = ρ.val := Complex.re_add_im ρ.val
  have hs1_pos : (ρ.val.re : ℂ) + (ρ.val.im : ℂ) * I ≠ 1 := by
    rw [hρ_eq]; exact fun he => hσ1.ne (by rw [he, Complex.one_re])
  have hs1_neg : (ρ.val.re : ℂ) + ((-ρ.val.im : ℝ) : ℂ) * I ≠ 1 := by
    intro he
    have hre := congrArg Complex.re he
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im, I_re, I_im,
      mul_zero, sub_zero, add_zero, Complex.one_re] at hre
    exact hσ1.ne hre
  have hζ_conj : riemannZeta ((ρ.val.re : ℂ) + ((-ρ.val.im : ℝ) : ℂ) * I) = 0 := by
    have hc : (ρ.val.re : ℂ) + ((-ρ.val.im : ℝ) : ℂ) * I = starRingEnd ℂ ρ.val := by
      apply Complex.ext <;> simp
    rw [hc, riemannZeta_conj, hζ, map_zero]
  refine ⟨?_, ?_, fun K₀ => ?_⟩
  · simpa only [Int.cast_one, one_mul] using
      _root_.RHTower.integral_phase_fermiMellinMeasure_eq_zero hσ0 hs1_pos (by rwa [hρ_eq])
  · simpa only [Int.cast_neg, Int.cast_one, neg_one_mul, Complex.ofReal_neg] using
      _root_.RHTower.integral_phase_fermiMellinMeasure_eq_zero hσ0 hs1_neg hζ_conj
  · have habs_pos : 0 < |ρ.val.im| := abs_pos.mpr him_ne
    have hbase_re0 : 0 < ((ρ.val.re : ℂ)).re := by simpa using hσ0
    have hbase_re1 : ((ρ.val.re : ℂ)).re < 1 := by simpa using hσ1
    obtain ⟨n, hn_ge, hζ_ne⟩ :=
      InfiniteRankPurityTheory.exists_riemannZeta_ne_zero_progression
        hbase_re0 hbase_re1 habs_pos (K₀ + 1)
    let k : ℤ := if 0 ≤ ρ.val.im then n else -n
    have hk_abs : |k| = |n| := by
      dsimp only [k]; split_ifs <;> [rfl; exact abs_neg n]
    have hk_gt : (K₀ : ℤ) < |k| := by
      rw [hk_abs]
      have hcast : ((K₀ + 1 : ℕ) : ℤ) = (K₀ : ℤ) + 1 := by push_cast; rfl
      omega
    have hk_mul : (k : ℝ) * ρ.val.im = (n : ℝ) * |ρ.val.im| := by
      dsimp only [k]
      split_ifs with hnonneg
      · rw [abs_of_nonneg hnonneg]
      · rw [abs_of_neg (lt_of_not_ge hnonneg), Int.cast_neg]; ring
    let s_k : ℂ := (ρ.val.re : ℂ) + (((k : ℝ) * ρ.val.im : ℝ) : ℂ) * I
    have hsk_eq : s_k = (ρ.val.re : ℂ) + (((n : ℝ) * |ρ.val.im| : ℝ) : ℂ) * I := by
      dsimp only [s_k]; rw [hk_mul]
    have hsk_ne1 : s_k ≠ 1 := by
      intro he
      have hre := congrArg Complex.re he
      simp only [s_k, Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im,
        I_re, I_im, mul_zero, sub_zero, add_zero, Complex.one_re] at hre
      exact hσ1.ne hre
    refine ⟨k, hk_gt, ?_⟩
    have hint_eq := _root_.RHTower.integral_phase_fermiMellinMeasure (σ := ρ.val.re)
      (τ := (k : ℝ) * ρ.val.im) hσ0 hsk_ne1
    have hcongr : (∫ t : ℝ, Complex.exp (((k : ℝ) * ρ.val.im : ℝ) * (Real.log t : ℂ) * I)
        ∂(_root_.RHTower.fermiMellinMeasure ρ.val.re)) =
      (Complex.Gamma s_k * (1 - (2 : ℂ) ^ (1 - s_k)) * riemannZeta s_k) /
        ((_root_.RHTower.fermiMellinNormalizer ρ.val.re : ℝ) : ℂ) := hint_eq
    rw [hcongr]
    have hΓ_ne : Complex.Gamma s_k ≠ 0 :=
      Complex.Gamma_ne_zero_of_re_pos (by simp [s_k, hσ0])
    have htwo_ne : (1 : ℂ) - (2 : ℂ) ^ (1 - s_k) ≠ 0 := by
      intro h0
      have h2eq : (2 : ℂ) ^ (1 - s_k) = 1 := (sub_eq_zero.mp h0).symm
      have hnorm := congrArg norm h2eq
      rw [norm_one, Complex.norm_cpow_eq_rpow_re_of_pos zero_lt_two] at hnorm
      have hre_pos : 0 < (1 - s_k).re := by simp [s_k]; linarith only [hσ1]
      have hgt1 : (1 : ℝ) < (2 : ℝ) ^ (1 - s_k).re := Real.one_lt_rpow (by norm_num) hre_pos
      linarith only [hnorm, hgt1]
    have hζk_ne : riemannZeta s_k ≠ 0 := by rwa [hsk_eq]
    have hZ_ne : ((_root_.RHTower.fermiMellinNormalizer ρ.val.re : ℝ) : ℂ) ≠ 0 :=
      Complex.ofReal_ne_zero.mpr (_root_.RHTower.fermiMellinNormalizer_pos hσ0).ne'
    exact div_ne_zero (mul_ne_zero (mul_ne_zero hΓ_ne htwo_ne) hζk_ne) hZ_ne

#print axioms bornCoefficient_eq_sum
#print axioms tendsto_bornLaw_uniform_iff_forall_nonzero_mode
#print axioms subcritical_bornCoefficient_rotating_phasor
#print axioms subcritical_norm_bornCoefficient_tendsto
#print axioms subcritical_no_subseq_zero_mode
#print axioms supercritical_bornCoefficient_tendsto
#print axioms supercritical_exists_high_mode_re_gt
#print axioms openStrip_zeta_zero_im_ne_zero
#print axioms rh_iff_single_mode_subseq_self_clock
#print axioms unconditional_bornCoefficient_zero_below_eightyFour_and_half_and_sub_farkas
#print axioms fermiMellin_fundamental_cancels_but_overtones_survive

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.CriticalBorn
