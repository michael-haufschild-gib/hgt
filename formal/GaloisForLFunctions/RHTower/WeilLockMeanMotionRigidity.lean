import GaloisForLFunctions.RHTower.WeilLowerSpectrumLockRigidity
import GaloisForLFunctions.HTGeometry.BohrUniqueness

/-!
# The mean motion of an almost-periodic lock

Let `G` be a Herglotz producer for the weights `lam` with lower-line lock

`G(1 − s) = V(s) G(s)`,  `V(s) = Σ_j q_j ρ_j^{−(s−½)}`,

with distinct `ρ_j > 0`, `Σ|q_j| max(1, ρ_j^{−1}) < ∞` and `Σ|q_j| |log ρ_j| < ∞`.  On the line
`v(y) = V(½ − iy) = Σ_j q_j e^{iy log ρ_j}` is unimodular for `y > 0`, and its phase velocity is
`Im(v' v̄)`.

**Positivity law** (`lock_meanMotion_nonneg`).  The mean motion of the lock is nonnegative:

`Σ_j |q_j|² log ρ_j ≥ 0`.

**Rigidity** (`lock_meanMotion_rigidity`).  If `Σ_j |q_j|² log ρ_j ≤ 0`, then `lam(n) = Λ(n)` for all
`n ≥ 2`, and the Riemann hypothesis holds.  In particular every lock whose coefficient moduli are
symmetric under `ρ ↦ ρ^{−1}` is trivial (`palindromic_lock_rigidity`), with no condition on the
arithmetic of the frequencies.

**Proof.**
* `|v|² ≡ 1` on `y > 0` gives `Re(v' v̄) = 0`, so `v = v(1) e^{iφ}` with `φ' = Im(v' v̄)`.
* The positivity law for lock phases (`deriv_lock_phase_nonneg`) gives `Im(v' v̄) ≥ 0` on `y > 0`.
* `v' v̄` is an absolutely convergent exponential sum over pairs `(j, k)`, with frequencies
  `log ρ_j − log ρ_k`.  Its window means converge to the diagonal sum `i Σ_j |q_j|² log ρ_j`.
* At mean motion zero, `Im(v' v̄)` is almost periodic, nonnegative everywhere (its negative part
  vanishes on a half-line) and of mean zero, so it vanishes identically
  (`eq_zero_of_bohrMean_eq_zero_of_nonneg`).  Hence the lock is constant, and
  `phase_lock_rigidity` applies.
-/

open Complex Filter Topology Set MeasureTheory
open scoped ComplexConjugate

namespace RHTower

namespace AbelianTwist

open GaloisForLFunctions GaloisForLFunctions.HTGeometry IntegerMassRigidity FractionalMassRigidity
  PhaseLockRigidity HamburgerStability TruncatedRadial RightEdgeKernel FractionalMassTailRigidity

noncomputable section

/-- The lock on the lower critical line, `y ↦ V(½ − iy)`. -/
def lineLock (q : ℕ → ℂ) (ρ : ℕ → ℝ) (y : ℝ) : ℂ :=
  ∑' j, q j * cexp (((Real.log (ρ j) : ℝ) : ℂ) * I * y)

/-- Its termwise derivative. -/
def lineLockDeriv (q : ℕ → ℂ) (ρ : ℕ → ℝ) (y : ℝ) : ℂ :=
  ∑' j, q j * (((Real.log (ρ j) : ℝ) : ℂ) * I) * cexp (((Real.log (ρ j) : ℝ) : ℂ) * I * y)

/-- The phase velocity `Im(v' v̄)`. -/
def lineLockVelocity (q : ℕ → ℂ) (ρ : ℕ → ℝ) (y : ℝ) : ℝ :=
  (lineLockDeriv q ρ y * conj (lineLock q ρ y)).im

theorem norm_cexp_freq_mul_I (r y : ℝ) : ‖cexp ((r : ℂ) * I * y)‖ = 1 := by
  rw [show (r : ℂ) * I * y = ((r * y : ℝ) : ℂ) * I by push_cast; ring]
  exact Complex.norm_exp_ofReal_mul_I _

theorem summable_norm_logWeight {q : ℕ → ℂ} {ρ : ℕ → ℝ}
    (hql : Summable fun j => ‖q j‖ * |Real.log (ρ j)|) :
    Summable fun j => ‖q j * (((Real.log (ρ j) : ℝ) : ℂ) * I)‖ := by
  refine hql.congr fun j => ?_
  rw [norm_mul, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs]

theorem continuous_lineLock {q : ℕ → ℂ} (ρ : ℕ → ℝ) (hqn : Summable fun j => ‖q j‖) :
    Continuous (lineLock q ρ) :=
  continuous_tsum_exp hqn fun j => Real.log (ρ j)

theorem continuous_lineLockDeriv {q : ℕ → ℂ} {ρ : ℕ → ℝ}
    (hql : Summable fun j => ‖q j‖ * |Real.log (ρ j)|) : Continuous (lineLockDeriv q ρ) :=
  continuous_tsum_exp (summable_norm_logWeight hql) fun j => Real.log (ρ j)

theorem continuous_lineLockVelocity {q : ℕ → ℂ} {ρ : ℕ → ℝ} (hqn : Summable fun j => ‖q j‖)
    (hql : Summable fun j => ‖q j‖ * |Real.log (ρ j)|) : Continuous (lineLockVelocity q ρ) :=
  Complex.continuous_im.comp ((continuous_lineLockDeriv hql).mul
    (Complex.continuous_conj.comp (continuous_lineLock ρ hqn)))

theorem hasDerivAt_lineLock {q : ℕ → ℂ} {ρ : ℕ → ℝ} (hqn : Summable fun j => ‖q j‖)
    (hql : Summable fun j => ‖q j‖ * |Real.log (ρ j)|) (y : ℝ) :
    HasDerivAt (lineLock q ρ) (lineLockDeriv q ρ y) y := by
  have hterm : ∀ (j : ℕ) (t : ℝ), HasDerivAt
      (fun t : ℝ => q j * cexp (((Real.log (ρ j) : ℝ) : ℂ) * I * t))
      (q j * (((Real.log (ρ j) : ℝ) : ℂ) * I) * cexp (((Real.log (ρ j) : ℝ) : ℂ) * I * t)) t := by
    intro j t
    have h1 : HasDerivAt (fun t : ℝ => ((Real.log (ρ j) : ℝ) : ℂ) * I * (t : ℂ))
        (((Real.log (ρ j) : ℝ) : ℂ) * I) t := by
      simpa using ((hasDerivAt_id t).ofReal_comp).const_mul (((Real.log (ρ j) : ℝ) : ℂ) * I)
    have h2 := (h1.cexp).const_mul (q j)
    have e : q j * (((Real.log (ρ j) : ℝ) : ℂ) * I) * cexp (((Real.log (ρ j) : ℝ) : ℂ) * I * t) =
        q j * (cexp (((Real.log (ρ j) : ℝ) : ℂ) * I * t) * (((Real.log (ρ j) : ℝ) : ℂ) * I)) := by
      ring
    rw [e]
    exact h2
  have hb : ∀ (j : ℕ) (t : ℝ), ‖q j * (((Real.log (ρ j) : ℝ) : ℂ) * I) *
      cexp (((Real.log (ρ j) : ℝ) : ℂ) * I * t)‖ ≤ ‖q j‖ * |Real.log (ρ j)| := by
    intro j t
    rw [norm_mul, norm_cexp_freq_mul_I, mul_one, norm_mul, norm_mul, Complex.norm_I,
      mul_one, Complex.norm_real, Real.norm_eq_abs]
  have h0 : Summable fun j => q j * cexp (((Real.log (ρ j) : ℝ) : ℂ) * I * ((0 : ℝ) : ℂ)) :=
    Summable.of_norm (hqn.congr fun j => by rw [norm_mul, norm_cexp_freq_mul_I, mul_one])
  exact hasDerivAt_tsum hql hterm hb h0 y

/-- The lock is unimodular on the lower line. -/
theorem norm_lineLock {lam : ℕ → ℝ} {Φ G : ℂ → ℂ}
    (hsl : ∀ σ : ℝ, 1 < σ → Summable fun n : ℕ => |lam n| / (n : ℝ) ^ σ)
    (hΦd : DifferentiableOn ℂ Φ {s : ℂ | 1 / 2 < s.re})
    (hΦre : ∀ s : ℂ, 1 / 2 < s.re → 0 ≤ (Φ s).re)
    (hid : ∀ s : ℂ, 1 < s.re →
      Φ s = zetaArchimedeanDatum s + 1 / (s - 1) - LSeries (lamTwo lam) s)
    (hGc : ∀ s : ℂ, 1 / 2 ≤ s.re → ContinuousAt G s)
    (hGd : ∀ s : ℂ, 1 / 2 < s.re → HasDerivAt G (Φ s * G s) s) (hG2 : G 2 = bigG lam 2)
    {q : ℕ → ℂ} {ρ : ℕ → ℝ} (hρ : ∀ j, 0 < ρ j) (hq : Summable fun j => ‖q j‖ * max 1 (ρ j)⁻¹)
    (hlock : ∀ τ : ℝ, τ < 0 → G (1 - lineS τ) = apLock q ρ (lineS τ) * G (lineS τ))
    {y : ℝ} (hy : 0 < y) : ‖lineLock q ρ y‖ = 1 := by
  rw [lineLock, ← apLock_line q hρ y]
  exact norm_lock_eq_one hsl hΦd hΦre hid hGc hGd hG2 (continuous_apLock hρ hq) hlock hy

/-- A unimodular curve has purely imaginary logarithmic velocity. -/
theorem re_deriv_mul_conj_eq_zero {v : ℝ → ℂ} {v' : ℝ → ℂ} (hv : ∀ t, HasDerivAt v (v' t) t)
    (hunit : ∀ t, 0 < t → ‖v t‖ = 1) {y : ℝ} (hy : 0 < y) : (v' y * conj (v y)).re = 0 := by
  have hN : HasDerivAt (fun t => v t * star (v t)) (v' y * star (v y) + v y * star (v' y)) y :=
    (hv y).mul (hv y).star
  have hconst : HasDerivAt (fun t => v t * star (v t)) 0 y := by
    refine (hasDerivAt_const y (1 : ℂ)).congr_of_eventuallyEq ?_
    filter_upwards [Ioi_mem_nhds hy] with t ht
    have h := hunit t ht
    rw [show star (v t) = conj (v t) from rfl, Complex.mul_conj, Complex.normSq_eq_norm_sq, h]
    norm_num
  have h := hN.unique hconst
  rw [show star (v y) = conj (v y) from rfl, show star (v' y) = conj (v' y) from rfl] at h
  have hre := congrArg Complex.re h
  simp only [Complex.add_re, Complex.mul_re, Complex.conj_re, Complex.conj_im,
    Complex.zero_re] at hre
  simp only [Complex.mul_re, Complex.conj_re, Complex.conj_im]
  linarith

/-- The phase of the lock. -/
def lineLockPhase (q : ℕ → ℂ) (ρ : ℕ → ℝ) (y : ℝ) : ℝ :=
  ∫ t in (1 : ℝ)..y, lineLockVelocity q ρ t

theorem hasDerivAt_lineLockPhase {q : ℕ → ℂ} {ρ : ℕ → ℝ} (hqn : Summable fun j => ‖q j‖)
    (hql : Summable fun j => ‖q j‖ * |Real.log (ρ j)|) (y : ℝ) :
    HasDerivAt (lineLockPhase q ρ) (lineLockVelocity q ρ y) y :=
  ((continuous_lineLockVelocity hqn hql).integral_hasStrictDerivAt 1 y).hasDerivAt

/-- **The lock is `v(1) e^{iφ}` on the lower line.** -/
theorem lineLock_eq_mul_exp_phase {q : ℕ → ℂ} {ρ : ℕ → ℝ} (hqn : Summable fun j => ‖q j‖)
    (hql : Summable fun j => ‖q j‖ * |Real.log (ρ j)|)
    (hunit : ∀ t, 0 < t → ‖lineLock q ρ t‖ = 1) {y : ℝ} (hy : 0 < y) :
    lineLock q ρ y = lineLock q ρ 1 * cexp ((lineLockPhase q ρ y : ℂ) * I) := by
  set v := lineLock q ρ with hvdef
  set v' := lineLockDeriv q ρ with hv'def
  set g := lineLockVelocity q ρ with hgdef
  set φ := lineLockPhase q ρ with hφdef
  have hv : ∀ t, HasDerivAt v (v' t) t := hasDerivAt_lineLock hqn hql
  set H : ℝ → ℂ := fun t => v t * cexp (-((φ t : ℂ) * I)) with hH
  have hφd : ∀ t, HasDerivAt (fun t => -((φ t : ℂ) * I)) (-((g t : ℂ) * I)) t := fun t =>
    (((hasDerivAt_lineLockPhase hqn hql t).ofReal_comp).mul_const I).neg
  have hHd : ∀ t, HasDerivAt H (v' t * cexp (-((φ t : ℂ) * I)) +
      v t * (cexp (-((φ t : ℂ) * I)) * -((g t : ℂ) * I))) t := fun t =>
    (hv t).mul (hφd t).cexp
  -- on `t > 0` the velocity identity `v' = i g v`
  have hvel : ∀ t, 0 < t → v' t = (g t : ℂ) * I * v t := by
    intro t ht
    have hre := re_deriv_mul_conj_eq_zero hv hunit ht
    have hz : v' t * conj (v t) = (g t : ℂ) * I := by
      apply Complex.ext
      · simp [hre]
      · simp [hgdef, lineLockVelocity, hvdef, hv'def]
    have hn : conj (v t) * v t = 1 := by
      rw [mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq, hunit t ht]; norm_num
    calc v' t = v' t * (conj (v t) * v t) := by rw [hn, mul_one]
      _ = (v' t * conj (v t)) * v t := by ring
      _ = (g t : ℂ) * I * v t := by rw [hz]
  have hHc : ∀ x ∈ Ioi (0 : ℝ), ∀ x' ∈ Ioi (0 : ℝ), H x = H x' := by
    intro x hx x' hx'
    refine isOpen_Ioi.is_const_of_deriv_eq_zero isPreconnected_Ioi
      (fun t _ => (hHd t).differentiableAt.differentiableWithinAt) (fun t ht => ?_) hx hx'
    rw [(hHd t).deriv, hvel t ht]
    simp only [Pi.zero_apply]
    ring
  have h1 : H 1 = v 1 := by
    simp [hH, hφdef, lineLockPhase]
  have hy' := hHc y hy 1 (by norm_num : (0 : ℝ) < 1)
  rw [h1] at hy'
  have hexp : cexp (-((φ y : ℂ) * I)) * cexp ((φ y : ℂ) * I) = 1 := by
    rw [← Complex.exp_add]; simp
  calc v y = v y * (cexp (-((φ y : ℂ) * I)) * cexp ((φ y : ℂ) * I)) := by rw [hexp, mul_one]
    _ = H y * cexp ((φ y : ℂ) * I) := by rw [hH]; ring
    _ = v 1 * cexp ((φ y : ℂ) * I) := by rw [hy']

/-- **The phase velocity of a lock is nonnegative.** -/
theorem lineLockVelocity_nonneg {lam : ℕ → ℝ} {Φ G : ℂ → ℂ}
    (hsl : ∀ σ : ℝ, 1 < σ → Summable fun n : ℕ => |lam n| / (n : ℝ) ^ σ)
    (hΦd : DifferentiableOn ℂ Φ {s : ℂ | 1 / 2 < s.re})
    (hΦre : ∀ s : ℂ, 1 / 2 < s.re → 0 ≤ (Φ s).re)
    (hid : ∀ s : ℂ, 1 < s.re →
      Φ s = zetaArchimedeanDatum s + 1 / (s - 1) - LSeries (lamTwo lam) s)
    (hGc : ∀ s : ℂ, 1 / 2 ≤ s.re → ContinuousAt G s)
    (hGd : ∀ s : ℂ, 1 / 2 < s.re → HasDerivAt G (Φ s * G s) s) (hG2 : G 2 = bigG lam 2)
    {q : ℕ → ℂ} {ρ : ℕ → ℝ} (hρ : ∀ j, 0 < ρ j) (hq : Summable fun j => ‖q j‖ * max 1 (ρ j)⁻¹)
    (hql : Summable fun j => ‖q j‖ * |Real.log (ρ j)|)
    (hlock : ∀ τ : ℝ, τ < 0 → G (1 - lineS τ) = apLock q ρ (lineS τ) * G (lineS τ))
    {y : ℝ} (hy : 0 < y) : 0 ≤ lineLockVelocity q ρ y := by
  have hqn : Summable fun j => ‖q j‖ :=
    Summable.of_nonneg_of_le (fun j => norm_nonneg _)
      (fun j => le_mul_of_one_le_right (norm_nonneg _) (le_max_left _ _)) hq
  have hunit : ∀ t, 0 < t → ‖lineLock q ρ t‖ = 1 := fun t ht =>
    norm_lineLock hsl hΦd hΦre hid hGc hGd hG2 hρ hq hlock ht
  set θ : ℝ → ℝ := fun x => lineLockPhase q ρ (2 * x) with hθ
  have hθd : ∀ x, HasDerivAt θ (lineLockVelocity q ρ (2 * x) * 2) x := fun x => by
    have h := (hasDerivAt_lineLockPhase hqn hql (2 * x)).comp x
      ((hasDerivAt_id x).const_mul 2)
    rw [mul_one] at h
    exact h
  have hθderiv : deriv θ = fun x => lineLockVelocity q ρ (2 * x) * 2 :=
    funext fun x => (hθd x).deriv
  have hlock' : ∀ x : ℝ, 0 < x → G (1 - vpt (1 / 2) x) =
      lineLock q ρ 1 * cexp ((θ x : ℂ) * I) * G (vpt (1 / 2) x) := by
    intro x hx
    have h := hlock (-x) (by linarith)
    rw [lineS_neg_eq_vpt] at h
    have hv : vpt (1 / 2) x = 1 / 2 - ((2 * x : ℝ) : ℂ) * I := by unfold vpt; push_cast; ring
    rw [h, hv, apLock_line q hρ (2 * x), ← lineLock,
      lineLock_eq_mul_exp_phase hqn hql hunit (by linarith : (0 : ℝ) < 2 * x)]
  have hd := deriv_lock_phase_nonneg hsl hΦd hΦre hid hGc hGd hG2
    (fun x => (hθd x).differentiableAt) (by
      rw [hθderiv]
      exact ((continuous_lineLockVelocity hqn hql).comp (continuous_const.mul continuous_id)).mul
        continuous_const) hlock' (by linarith : (0 : ℝ) < y / 2)
  rw [hθderiv] at hd
  simp only at hd
  rw [show 2 * (y / 2) = y by ring] at hd
  linarith

/-- The coefficients of `v' v̄` as a double exponential sum. -/
def lockPairCoeff (q : ℕ → ℂ) (ρ : ℕ → ℝ) (z : ℕ × ℕ) : ℂ :=
  q z.1 * (((Real.log (ρ z.1) : ℝ) : ℂ) * I) * conj (q z.2)

/-- The frequencies of `v' v̄`. -/
def lockPairFreq (ρ : ℕ → ℝ) (z : ℕ × ℕ) : ℝ := Real.log (ρ z.1) + -Real.log (ρ z.2) - 0

theorem summable_norm_lockPairCoeff {q : ℕ → ℂ} {ρ : ℕ → ℝ} (hqn : Summable fun j => ‖q j‖)
    (hql : Summable fun j => ‖q j‖ * |Real.log (ρ j)|) :
    Summable fun z => ‖lockPairCoeff q ρ z‖ := by
  have hcc : Summable fun j => ‖conj (q j)‖ := by simpa using hqn
  refine ((summable_norm_logWeight hql).mul_norm hcc).congr fun z => ?_
  rw [lockPairCoeff, norm_mul]

theorem lineLockDeriv_mul_conj {q : ℕ → ℂ} {ρ : ℕ → ℝ} (hqn : Summable fun j => ‖q j‖)
    (hql : Summable fun j => ‖q j‖ * |Real.log (ρ j)|) (y : ℝ) :
    lineLockDeriv q ρ y * conj (lineLock q ρ y) =
      ∑' z, lockPairCoeff q ρ z * cexp ((lockPairFreq ρ z : ℂ) * I * y) := by
  have hcc : Summable fun j => ‖conj (q j)‖ := by simpa using hqn
  have h := tsum_exp_mul_tsum_exp (summable_norm_logWeight hql) hcc
    (fun j => Real.log (ρ j)) (fun j => -Real.log (ρ j)) 0 y
  have e0 : cexp (((-0 : ℝ) : ℂ) * I * y) = 1 := by simp
  rw [e0, mul_one] at h
  rw [lineLockDeriv, lineLock, conj_tsum_exp]
  exact h

theorem lockPairFreq_eq_zero_iff {ρ : ℕ → ℝ} (hρ : ∀ j, 0 < ρ j) (hinj : Function.Injective ρ)
    (z : ℕ × ℕ) : lockPairFreq ρ z = 0 ↔ z.1 = z.2 := by
  constructor
  · intro h
    have h' : Real.log (ρ z.1) = Real.log (ρ z.2) := by simp only [lockPairFreq] at h; linarith
    exact hinj (Real.log_injOn_pos (hρ _) (hρ _) h')
  · intro h; simp [lockPairFreq, h]

theorem tsum_lockPairCoeff_diag {q : ℕ → ℂ} {ρ : ℕ → ℝ} (hρ : ∀ j, 0 < ρ j)
    (hinj : Function.Injective ρ) :
    (∑' z, if lockPairFreq ρ z = 0 then lockPairCoeff q ρ z else 0) =
      ((∑' j, ‖q j‖ ^ 2 * Real.log (ρ j) : ℝ) : ℂ) * I := by
  have hg : Function.Injective (fun j : ℕ => (j, j)) := fun a b h => (Prod.ext_iff.mp h).1
  have hsupp : Function.support (fun z => if lockPairFreq ρ z = 0 then lockPairCoeff q ρ z else 0) ⊆
      Set.range (fun j : ℕ => (j, j)) := by
    intro z hz
    by_contra hno
    apply hz
    have hne : ¬ lockPairFreq ρ z = 0 := by
      rw [lockPairFreq_eq_zero_iff hρ hinj]
      intro h
      exact hno ⟨z.1, Prod.ext rfl h⟩
    simp only [hne, if_false]
  rw [← hg.tsum_eq hsupp]
  have hterm : ∀ j : ℕ, (if lockPairFreq ρ (j, j) = 0 then lockPairCoeff q ρ (j, j) else 0) =
      ((‖q j‖ ^ 2 * Real.log (ρ j) : ℝ) : ℂ) * I := by
    intro j
    rw [if_pos ((lockPairFreq_eq_zero_iff hρ hinj _).mpr rfl), lockPairCoeff]
    rw [show q (j, j).1 * (((Real.log (ρ (j, j).1) : ℝ) : ℂ) * I) * conj (q (j, j).2) =
        (q j * conj (q j)) * (((Real.log (ρ j) : ℝ) : ℂ) * I) by simp only; ring,
      Complex.mul_conj, Complex.normSq_eq_norm_sq]
    push_cast
    ring
  simp only [hterm]
  rw [tsum_mul_right, Complex.ofReal_tsum]

/-- The window means of the phase velocity converge to `Σ_j |q_j|² log ρ_j`. -/
theorem tendsto_mean_lineLockVelocity {q : ℕ → ℂ} {ρ : ℕ → ℝ} (hρ : ∀ j, 0 < ρ j)
    (hinj : Function.Injective ρ) (hqn : Summable fun j => ‖q j‖)
    (hql : Summable fun j => ‖q j‖ * |Real.log (ρ j)|) :
    Tendsto (fun T : ℝ => (1 / T) * ∫ y in (0 : ℝ)..T, lineLockVelocity q ρ y) atTop
      (𝓝 (∑' j, ‖q j‖ ^ 2 * Real.log (ρ j))) := by
  have hcn := summable_norm_lockPairCoeff hqn hql (ρ := ρ)
  have hmean := tendsto_mean_expSum hcn (lockPairFreq ρ)
  rw [tsum_lockPairCoeff_diag hρ hinj] at hmean
  have him := (Complex.continuous_im.tendsto _).comp hmean
  have hval : (((∑' j, ‖q j‖ ^ 2 * Real.log (ρ j) : ℝ) : ℂ) * I).im =
      ∑' j, ‖q j‖ ^ 2 * Real.log (ρ j) := by simp
  rw [hval] at him
  refine him.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with T hT
  have hint : IntervalIntegrable
      (fun y : ℝ => ∑' z, lockPairCoeff q ρ z * cexp ((lockPairFreq ρ z : ℂ) * I * y)) volume 0 T :=
    (continuous_tsum_exp hcn (lockPairFreq ρ)).intervalIntegrable _ _
  have hcomm := (Complex.imCLM).intervalIntegral_comp_comm hint
  have hfun : (fun y : ℝ =>
      Complex.imCLM (∑' z, lockPairCoeff q ρ z * cexp ((lockPairFreq ρ z : ℂ) * I * y)))
      = lineLockVelocity q ρ := by
    funext y
    rw [Complex.imCLM_apply, lineLockVelocity, lineLockDeriv_mul_conj hqn hql]
  rw [hfun] at hcomm
  simp only [Function.comp_apply]
  rw [show (1 / (T : ℂ)) = ((1 / T : ℝ) : ℂ) by push_cast; ring, Complex.im_ofReal_mul,
    ← Complex.imCLM_apply, hcomm]

/-- **Positivity law for almost-periodic locks.**  The mean motion `Σ_j |q_j|² log ρ_j` of the
lock of a Herglotz producer is nonnegative. -/
theorem lock_meanMotion_nonneg {lam : ℕ → ℝ} {Φ G : ℂ → ℂ}
    (hsl : ∀ σ : ℝ, 1 < σ → Summable fun n : ℕ => |lam n| / (n : ℝ) ^ σ)
    (hΦd : DifferentiableOn ℂ Φ {s : ℂ | 1 / 2 < s.re})
    (hΦre : ∀ s : ℂ, 1 / 2 < s.re → 0 ≤ (Φ s).re)
    (hid : ∀ s : ℂ, 1 < s.re →
      Φ s = zetaArchimedeanDatum s + 1 / (s - 1) - LSeries (lamTwo lam) s)
    (hGc : ∀ s : ℂ, 1 / 2 ≤ s.re → ContinuousAt G s)
    (hGd : ∀ s : ℂ, 1 / 2 < s.re → HasDerivAt G (Φ s * G s) s) (hG2 : G 2 = bigG lam 2)
    {q : ℕ → ℂ} {ρ : ℕ → ℝ} (hρ : ∀ j, 0 < ρ j) (hinj : Function.Injective ρ)
    (hq : Summable fun j => ‖q j‖ * max 1 (ρ j)⁻¹)
    (hql : Summable fun j => ‖q j‖ * |Real.log (ρ j)|)
    (hlock : ∀ τ : ℝ, τ < 0 → G (1 - lineS τ) = apLock q ρ (lineS τ) * G (lineS τ)) :
    0 ≤ ∑' j, ‖q j‖ ^ 2 * Real.log (ρ j) := by
  have hqn : Summable fun j => ‖q j‖ :=
    Summable.of_nonneg_of_le (fun j => norm_nonneg _)
      (fun j => le_mul_of_one_le_right (norm_nonneg _) (le_max_left _ _)) hq
  have hpos := fun {y : ℝ} (hy : 0 < y) =>
    lineLockVelocity_nonneg hsl hΦd hΦre hid hGc hGd hG2 hρ hq hql hlock hy
  have h0 : 0 ≤ lineLockVelocity q ρ 0 := by
    have hc := (continuous_lineLockVelocity hqn hql).continuousAt (x := 0)
    refine ge_of_tendsto (hc.tendsto.mono_left (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))) ?_
    filter_upwards [self_mem_nhdsWithin] with y hy
    exact hpos hy
  refine ge_of_tendsto (tendsto_mean_lineLockVelocity hρ hinj hqn hql) ?_
  filter_upwards [eventually_gt_atTop 0] with T hT
  refine mul_nonneg (by positivity) (intervalIntegral.integral_nonneg hT.le fun y hy => ?_)
  rcases eq_or_lt_of_le hy.1 with h | h
  · rw [← h]; exact h0
  · exact hpos h

theorem cexp_mul_I_eq_bohrChar (r y : ℝ) :
    cexp ((r : ℂ) * I * y) = bohrChar (-r) y := by
  unfold bohrChar
  congr 1
  push_cast
  ring

theorem isBohrAlmostPeriodic_tsum_cexp {c : ℕ → ℂ} (hc : Summable fun j => ‖c j‖) (θ : ℕ → ℝ) :
    _root_.HTGeometry.IsBohrAlmostPeriodic fun y : ℝ => ∑' j, c j * cexp ((θ j : ℂ) * I * y) := by
  have h := isBohrAlmostPeriodic_tsum_bohrChar hc fun j => -θ j
  have e : (fun y : ℝ => ∑' j, c j * cexp ((θ j : ℂ) * I * y)) =
      fun y => ∑' j, c j * bohrChar (-θ j) y := by
    funext y
    congr 1
    funext j
    rw [cexp_mul_I_eq_bohrChar]
  rw [e]
  exact h

/-- The phase velocity is almost periodic. -/
theorem isBohrAlmostPeriodic_lineLockVelocity {q : ℕ → ℂ} {ρ : ℕ → ℝ}
    (hqn : Summable fun j => ‖q j‖) (hql : Summable fun j => ‖q j‖ * |Real.log (ρ j)|) :
    _root_.HTGeometry.IsBohrAlmostPeriodic fun y => ((lineLockVelocity q ρ y : ℝ) : ℂ) := by
  have hv : _root_.HTGeometry.IsBohrAlmostPeriodic (lineLock q ρ) :=
    isBohrAlmostPeriodic_tsum_cexp hqn fun j => Real.log (ρ j)
  have hv' : _root_.HTGeometry.IsBohrAlmostPeriodic (lineLockDeriv q ρ) :=
    isBohrAlmostPeriodic_tsum_cexp (summable_norm_logWeight hql) fun j => Real.log (ρ j)
  have hvc := continuous_lineLock ρ hqn
  have hv'c := continuous_lineLockDeriv hql
  have hw := isBohrAlmostPeriodic_mul hv'c hv' (Complex.continuous_conj.comp hvc)
    (isBohrAlmostPeriodic_conj hv)
  have hwc : Continuous fun t => lineLockDeriv q ρ t * conj (lineLock q ρ t) :=
    hv'c.mul (Complex.continuous_conj.comp hvc)
  have hd := isBohrAlmostPeriodic_const_mul (-I / 2)
    (isBohrAlmostPeriodic_sub hwc hw (Complex.continuous_conj.comp hwc)
      (isBohrAlmostPeriodic_conj hw))
  have e : (fun y => ((lineLockVelocity q ρ y : ℝ) : ℂ)) = fun t =>
      -I / 2 * (lineLockDeriv q ρ t * conj (lineLock q ρ t) -
        conj (lineLockDeriv q ρ t * conj (lineLock q ρ t))) := by
    funext t
    set w := lineLockDeriv q ρ t * conj (lineLock q ρ t)
    rw [lineLockVelocity]
    apply Complex.ext
    · simp [w]; ring
    · simp [w]
  rw [e]
  exact hd

theorem isBohrAlmostPeriodic_of_ofReal' {g : ℝ → ℝ}
    (h : _root_.HTGeometry.IsBohrAlmostPeriodic fun u => ((g u : ℝ) : ℂ)) :
    _root_.HTGeometry.IsBohrAlmostPeriodic g := by
  intro ε hε
  obtain ⟨L, hL, hdense⟩ := h ε hε
  refine ⟨L, hL, fun a => ?_⟩
  obtain ⟨τ, hτmem, hτ⟩ := hdense a
  refine ⟨τ, hτmem, fun x => ?_⟩
  have hx := hτ x
  rwa [← Complex.ofReal_sub, Complex.norm_real] at hx

/-- **Locks of mean motion zero are constant; nonpositive mean motion forces the true producer.**
If `Σ_j |q_j|² log ρ_j ≤ 0`, then `lam(n) = Λ(n)` for all `n ≥ 2`, and the Riemann hypothesis
holds. -/
theorem lock_meanMotion_rigidity {lam : ℕ → ℝ} {Φ G : ℂ → ℂ}
    (hsl : ∀ σ : ℝ, 1 < σ → Summable fun n : ℕ => |lam n| / (n : ℝ) ^ σ)
    (hΦd : DifferentiableOn ℂ Φ {s : ℂ | 1 / 2 < s.re})
    (hΦre : ∀ s : ℂ, 1 / 2 < s.re → 0 ≤ (Φ s).re)
    (hid : ∀ s : ℂ, 1 < s.re → Φ s = zetaArchimedeanDatum s + 1 / (s - 1) -
      LSeries (fun n => if 2 ≤ n then (lam n : ℂ) else 0) s)
    (hGc : ∀ s : ℂ, 1 / 2 ≤ s.re → ContinuousAt G s)
    (hGd : ∀ s : ℂ, 1 / 2 < s.re → HasDerivAt G (Φ s * G s) s) (hG2 : G 2 = bigG lam 2)
    {q : ℕ → ℂ} {ρ : ℕ → ℝ} (hρ : ∀ j, 0 < ρ j) (hinj : Function.Injective ρ)
    (hq : Summable fun j => ‖q j‖ * max 1 (ρ j)⁻¹)
    (hql : Summable fun j => ‖q j‖ * |Real.log (ρ j)|)
    (hm : ∑' j, ‖q j‖ ^ 2 * Real.log (ρ j) ≤ 0)
    (hlock : ∀ τ : ℝ, τ < 0 → G (1 - lineS τ) =
      (∑' j, q j * (ρ j : ℂ) ^ (-(lineS τ - 1 / 2))) * G (lineS τ)) :
    (∀ n : ℕ, 2 ≤ n → lam n = ArithmeticFunction.vonMangoldt n) ∧ RiemannHypothesis := by
  have hidT : ∀ s : ℂ, 1 < s.re →
      Φ s = zetaArchimedeanDatum s + 1 / (s - 1) - LSeries (lamTwo lam) s := hid
  have hlockV : ∀ τ : ℝ, τ < 0 → G (1 - lineS τ) = apLock q ρ (lineS τ) * G (lineS τ) := by
    intro τ hτ
    rw [apLock_of_mem q ρ (le_of_eq (lineS_re τ).symm) (by rw [lineS_re]; norm_num)]
    exact hlock τ hτ
  have hqn : Summable fun j => ‖q j‖ :=
    Summable.of_nonneg_of_le (fun j => norm_nonneg _)
      (fun j => le_mul_of_one_le_right (norm_nonneg _) (le_max_left _ _)) hq
  have hm0 : ∑' j, ‖q j‖ ^ 2 * Real.log (ρ j) = 0 :=
    le_antisymm hm (lock_meanMotion_nonneg hsl hΦd hΦre hidT hGc hGd hG2 hρ hinj hq hql hlockV)
  set g := lineLockVelocity q ρ with hgdef
  have hgc : Continuous g := continuous_lineLockVelocity hqn hql
  have hpos : ∀ y : ℝ, 0 < y → 0 ≤ g y := fun y hy =>
    lineLockVelocity_nonneg hsl hΦd hΦre hidT hGc hGd hG2 hρ hq hql hlockV hy
  set gC : ℝ → ℂ := fun y => ((g y : ℝ) : ℂ) with hgC
  have hgCc : Continuous gC := Complex.continuous_ofReal.comp hgc
  have hgCa : _root_.HTGeometry.IsBohrAlmostPeriodic gC :=
    isBohrAlmostPeriodic_lineLockVelocity hqn hql
  -- nonnegativity on the whole line
  have hga : _root_.HTGeometry.IsBohrAlmostPeriodic g := isBohrAlmostPeriodic_of_ofReal' hgCa
  have hnorm : _root_.HTGeometry.IsBohrAlmostPeriodic fun t => ‖gC t‖ :=
    isBohrAlmostPeriodic_norm_real hgCa
  have hdiff := isBohrAlmostPeriodic_sub (hgCc.norm) hnorm hgc hga
  have hzero := _root_.HTGeometry.eq_zero_of_isBohrAlmostPeriodic_of_tendsto_zero hdiff (by
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_gt_atTop 0] with t ht
    simp only [hgC, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hpos t ht), sub_self])
  have hnn : ∀ t, 0 ≤ g t := fun t => by
    have h := hzero t
    simp only [hgC, Complex.norm_real, Real.norm_eq_abs] at h
    have : |g t| = g t := by linarith
    rw [← this]; exact abs_nonneg _
  -- mean zero
  have hmean : bohrMean gC = 0 := by
    refine bohrMean_eq hgCc hgCa ?_
    have ht := (Complex.continuous_ofReal.tendsto _).comp
      (tendsto_mean_lineLockVelocity hρ hinj hqn hql)
    rw [hm0, Complex.ofReal_zero] at ht
    refine ht.congr' ?_
    filter_upwards [eventually_gt_atTop 0] with T hT
    simp only [Function.comp_apply, windowAverage, hgC, intervalIntegral.integral_ofReal]
    rw [Complex.real_smul]
    push_cast
    ring
  have hg0 : ∀ t, g t = 0 := by
    intro t
    have h := eq_zero_of_bohrMean_eq_zero_of_nonneg hgCc hgCa (fun t => by simp [hgC, hnn t])
      (fun t => by simp [hgC]) hmean t
    simpa [hgC] using h
  -- the lock is constant
  have hunit : ∀ t, 0 < t → ‖lineLock q ρ t‖ = 1 := fun t ht =>
    norm_lineLock hsl hΦd hΦre hidT hGc hGd hG2 hρ hq hlockV ht
  have hphase : ∀ y, lineLockPhase q ρ y = 0 := by
    intro y
    simp only [lineLockPhase]
    rw [show (fun t => lineLockVelocity q ρ t) = fun _ => (0 : ℝ) from funext hg0]
    simp
  have hconst : ∀ y : ℝ, 0 < y → lineLock q ρ y = lineLock q ρ 1 := by
    intro y hy
    rw [lineLock_eq_mul_exp_phase hqn hql hunit hy, hphase]
    simp
  set κ := lineLock q ρ 1 with hκ
  have hκ0 : κ ≠ 0 := by
    intro h
    have := hunit 1 one_pos
    rw [← hκ, h, norm_zero] at this
    exact zero_ne_one this
  refine phase_lock_rigidity hsl hΦd hΦre hid hGc hGd hG2 le_rfl (inv_ne_zero hκ0)
    (fun y hy => ?_)
  have hl := hlockV (-(y / 2)) (by linarith)
  have e1 : lineS (-(y / 2)) = 1 / 2 - ((y : ℝ) : ℂ) * I := by rw [lineS_eq]; push_cast; ring
  have e2 : (1 : ℂ) - (1 / 2 - (y : ℂ) * I) = 1 / 2 + (y : ℂ) * I := by ring
  rw [e1, e2, apLock_line q hρ y, ← lineLock, hconst y hy] at hl
  rw [hl, ← mul_assoc, inv_mul_cancel₀ hκ0, one_mul]

/-- **Palindromic locks are trivial.**  If an involution of the frequencies `ρ ↦ ρ^{−1}` preserves
the coefficient moduli, the mean motion vanishes and the lock forces the true producer. -/
theorem palindromic_lock_rigidity {lam : ℕ → ℝ} {Φ G : ℂ → ℂ}
    (hsl : ∀ σ : ℝ, 1 < σ → Summable fun n : ℕ => |lam n| / (n : ℝ) ^ σ)
    (hΦd : DifferentiableOn ℂ Φ {s : ℂ | 1 / 2 < s.re})
    (hΦre : ∀ s : ℂ, 1 / 2 < s.re → 0 ≤ (Φ s).re)
    (hid : ∀ s : ℂ, 1 < s.re → Φ s = zetaArchimedeanDatum s + 1 / (s - 1) -
      LSeries (fun n => if 2 ≤ n then (lam n : ℂ) else 0) s)
    (hGc : ∀ s : ℂ, 1 / 2 ≤ s.re → ContinuousAt G s)
    (hGd : ∀ s : ℂ, 1 / 2 < s.re → HasDerivAt G (Φ s * G s) s) (hG2 : G 2 = bigG lam 2)
    {q : ℕ → ℂ} {ρ : ℕ → ℝ} (hρ : ∀ j, 0 < ρ j) (hinj : Function.Injective ρ)
    (hq : Summable fun j => ‖q j‖ * max 1 (ρ j)⁻¹)
    (hql : Summable fun j => ‖q j‖ * |Real.log (ρ j)|) (σ : ℕ ≃ ℕ)
    (hσρ : ∀ j, ρ (σ j) = (ρ j)⁻¹) (hσq : ∀ j, ‖q (σ j)‖ = ‖q j‖)
    (hlock : ∀ τ : ℝ, τ < 0 → G (1 - lineS τ) =
      (∑' j, q j * (ρ j : ℂ) ^ (-(lineS τ - 1 / 2))) * G (lineS τ)) :
    (∀ n : ℕ, 2 ≤ n → lam n = ArithmeticFunction.vonMangoldt n) ∧ RiemannHypothesis := by
  refine lock_meanMotion_rigidity hsl hΦd hΦre hid hGc hGd hG2 hρ hinj hq hql (le_of_eq ?_) hlock
  have h := σ.tsum_eq fun j => ‖q j‖ ^ 2 * Real.log (ρ j)
  have hneg : (∑' j, ‖q (σ j)‖ ^ 2 * Real.log (ρ (σ j))) =
      -∑' j, ‖q j‖ ^ 2 * Real.log (ρ j) := by
    rw [← tsum_neg]
    congr 1
    funext j
    rw [hσq, hσρ, Real.log_inv]
    ring
  linarith

/-- **Spectra below one** (the almost-periodic case of MUST-1310 through the mean motion). -/
theorem le_one_spectrum_meanMotion_rigidity {lam : ℕ → ℝ} {Φ G : ℂ → ℂ}
    (hsl : ∀ σ : ℝ, 1 < σ → Summable fun n : ℕ => |lam n| / (n : ℝ) ^ σ)
    (hΦd : DifferentiableOn ℂ Φ {s : ℂ | 1 / 2 < s.re})
    (hΦre : ∀ s : ℂ, 1 / 2 < s.re → 0 ≤ (Φ s).re)
    (hid : ∀ s : ℂ, 1 < s.re → Φ s = zetaArchimedeanDatum s + 1 / (s - 1) -
      LSeries (fun n => if 2 ≤ n then (lam n : ℂ) else 0) s)
    (hGc : ∀ s : ℂ, 1 / 2 ≤ s.re → ContinuousAt G s)
    (hGd : ∀ s : ℂ, 1 / 2 < s.re → HasDerivAt G (Φ s * G s) s) (hG2 : G 2 = bigG lam 2)
    {q : ℕ → ℂ} {ρ : ℕ → ℝ} (hρ : ∀ j, 0 < ρ j) (hinj : Function.Injective ρ)
    (hρ1 : ∀ j, ρ j ≤ 1) (hq : Summable fun j => ‖q j‖ * max 1 (ρ j)⁻¹)
    (hql : Summable fun j => ‖q j‖ * |Real.log (ρ j)|)
    (hlock : ∀ τ : ℝ, τ < 0 → G (1 - lineS τ) =
      (∑' j, q j * (ρ j : ℂ) ^ (-(lineS τ - 1 / 2))) * G (lineS τ)) :
    (∀ n : ℕ, 2 ≤ n → lam n = ArithmeticFunction.vonMangoldt n) ∧ RiemannHypothesis :=
  lock_meanMotion_rigidity hsl hΦd hΦre hid hGc hGd hG2 hρ hinj hq hql
    (tsum_nonpos fun j => mul_nonpos_of_nonneg_of_nonpos (sq_nonneg _)
      (Real.log_nonpos (hρ j).le (hρ1 j))) hlock

end

end AbelianTwist

end RHTower
