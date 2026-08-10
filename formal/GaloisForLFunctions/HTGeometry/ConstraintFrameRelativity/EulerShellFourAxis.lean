import GaloisForLFunctions.HTGeometry.ConstraintFrameRelativity.RamificationBooleanSupport
import GaloisForLFunctions.HTGeometry.ConstraintFrameRelativity.FiniteTiltResponse
import GaloisForLFunctions.HTGeometry.ConstraintFrameRelativity.PhaseHistoryDilation

/-!
# The literal Euler-shell four-axis frame

The marked shell stream recovers every prime clock from its own logarithmic prolongation:
`(L^k a_m)(p^m) = (-m log p)^k`, so `log p = -(1/m)(L a_m)(p^m)`.

On a finite prime aperture the clock generator, the phase flow and the Gamma--Rees weight are all
diagonal in the same marked basis, hence commute and restrict strictly; the flow solves
`U'(t) = -i Λ U(t)`.  The Rees weight `ℓ_p = 4p³(log p)²/((p+1)²(p-1)(2p-1))` is asymptotic to
`2(log p)²/p` and tends to zero, so its inverse is cofinally unbounded.

Normalised observation has a nontrivial exchange law: the derivative of `c ↦ (∑ cₙ n^{-σ-it})/Z_c`
in the direction `h` is `Z_c^{-1}(∑ hₙ n^{-σ-it} - H₀(h) C_c(t))`, which for a multiplicative score
`h = c r` is the centred covariance of the score against the phase.

Finally the normalisation wall: matching the physical half-density forces `m σ = 1`, incompatible
with `m ≥ 12` and `σ > 1`.
-/

namespace HTGeometry.ConstraintFrameRelativity

open RHTower

/-! ## Clock recovery from the logarithmic prolongation -/

/-- The `k`-th iterate of the logarithmic coefficient operator is multiplication by `(-log n)^k`. -/
theorem logCoeffOperator_iterate (f : ℕ → ℝ) (n : ℕ) (k : ℕ) :
    (logCoeffOperator)^[k] f n = (-(Real.log n)) ^ k * f n := by
  induction k with
  | zero => simp
  | succ j ih =>
    rw [Function.iterate_succ_apply', logCoeffOperator, ih]
    ring

/-- **The marked shell recovers every prime clock.** -/
theorem shell_clock_recovery {m p : ℕ} (hm : m ≠ 0) (hp : p.Prime) (k : ℕ) :
    (logCoeffOperator)^[k] (fun n => ((unitalShellIndicator m n : ℤ) : ℝ)) (p ^ m)
      = (-((m : ℝ) * Real.log p)) ^ k := by
  have hsq : Squarefree p := hp.squarefree
  have hval : ((unitalShellIndicator m (p ^ m) : ℤ) : ℝ) = 1 := by
    rw [(unitalShellIndicator_pow_self_eq_one_iff hm hp.ne_zero).mpr hsq]
    norm_num
  rw [logCoeffOperator_iterate, hval, mul_one]
  congr 2
  rw [Nat.cast_pow, Real.log_pow]

/-- **The prime clock is the first prolongation.** -/
theorem prime_clock_eq {m p : ℕ} (hm : m ≠ 0) (hp : p.Prime) :
    -(1 / (m : ℝ)) *
        (logCoeffOperator)^[1] (fun n => ((unitalShellIndicator m n : ℤ) : ℝ)) (p ^ m)
      = Real.log p := by
  rw [shell_clock_recovery hm hp 1, pow_one]
  have hm0 : (m : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hm
  field_simp

/-! ## The diagonal four-axis frame on a finite aperture -/

variable {F : Type*} [Fintype F] [DecidableEq F]

/-- The diagonal clock generator. -/
def clockGen (lam : F → ℝ) (x : F → ℂ) (p : F) : ℂ := (lam p : ℂ) * x p

/-- The diagonal phase flow. -/
noncomputable def phaseFlow (lam : F → ℝ) (t : ℝ) (x : F → ℂ) (p : F) : ℂ :=
  Complex.exp ((-(t * lam p) : ℝ) * Complex.I) * x p

/-- The diagonal Gamma--Rees frame. -/
def reesFrame (l : F → ℝ) (x : F → ℂ) (p : F) : ℂ := (l p : ℂ) * x p

omit [Fintype F] [DecidableEq F] in
/-- **The prime-skeleton operators commute.** -/
theorem diagonal_commute (lam l : F → ℝ) (t : ℝ) (x : F → ℂ) :
    clockGen lam (reesFrame l x) = reesFrame l (clockGen lam x)
      ∧ phaseFlow lam t (reesFrame l x) = reesFrame l (phaseFlow lam t x)
      ∧ phaseFlow lam t (clockGen lam x) = clockGen lam (phaseFlow lam t x) := by
  refine ⟨?_, ?_, ?_⟩ <;> funext p <;>
    simp only [clockGen, reesFrame, phaseFlow] <;> ring

omit [Fintype F] [DecidableEq F] in
/-- **Strict aperture naturality.**  Restricting a coordinate diagonal operator to a subaperture is
the diagonal operator of the restricted data. -/
theorem restriction_natural {E : Type*} (ι : E → F) (lam l : F → ℝ) (t : ℝ) (x : F → ℂ) (q : E) :
    clockGen lam x (ι q) = ((lam (ι q) : ℂ)) * x (ι q)
      ∧ phaseFlow lam t x (ι q)
          = Complex.exp ((-(t * lam (ι q)) : ℝ) * Complex.I) * x (ι q)
      ∧ reesFrame l x (ι q) = ((l (ι q) : ℂ)) * x (ι q) :=
  ⟨rfl, rfl, rfl⟩

omit [Fintype F] [DecidableEq F] in
/-- **The phase flow solves the clock equation.** -/
theorem hasDerivAt_phaseFlow (lam : F → ℝ) (x : F → ℂ) (p : F) (t : ℝ) :
    HasDerivAt (fun s : ℝ => phaseFlow lam s x p)
      (-Complex.I * (lam p : ℂ) * phaseFlow lam t x p) t := by
  have hlin : HasDerivAt (fun s : ℝ => ((-(s * lam p) : ℝ) : ℂ)) (-(lam p : ℂ)) t := by
    have h0 : HasDerivAt (fun s : ℝ => s * -(lam p)) (-(lam p)) t := by
      simpa using (hasDerivAt_id t).mul_const (-(lam p))
    have hfun : (fun s : ℝ => s * -(lam p)) = fun s : ℝ => -(s * lam p) := by
      funext s; ring
    rw [hfun] at h0
    simpa using h0.ofReal_comp
  have hmul : HasDerivAt (fun s : ℝ => ((-(s * lam p) : ℝ) : ℂ) * Complex.I)
      (-(lam p : ℂ) * Complex.I) t := hlin.mul_const Complex.I
  have hexp := hmul.cexp
  have hfin := hexp.mul_const (x p)
  refine hfin.congr_deriv ?_
  simp only [phaseFlow]
  ring

/-! ## The Gamma--Rees weight collapses cofinally -/

/-- The literal Gamma--Bockstein/Rees weight. -/
noncomputable def reesWeight (p : ℝ) : ℝ :=
  4 * p ^ 3 * (Real.log p) ^ 2 / ((p + 1) ^ 2 * (p - 1) * (2 * p - 1))

/-- **The rational part of the Rees weight has the exact leading behaviour `2/p`.** -/
theorem tendsto_reesRational :
    Filter.Tendsto (fun p : ℝ => 4 * p ^ 4 / ((p + 1) ^ 2 * (p - 1) * (2 * p - 1)))
      Filter.atTop (nhds 2) := by
  have hrw : ∀ p : ℝ, 2 ≤ p →
      4 * p ^ 4 / ((p + 1) ^ 2 * (p - 1) * (2 * p - 1))
        = 4 / ((1 + p⁻¹) ^ 2 * (1 - p⁻¹) * (2 - p⁻¹)) := by
    intro p hp
    have hp0 : p ≠ 0 := by linarith
    field_simp
  have hinv : Filter.Tendsto (fun p : ℝ => p⁻¹) Filter.atTop (nhds 0) :=
    Filter.Tendsto.inv_tendsto_atTop Filter.tendsto_id
  have hden : Filter.Tendsto
      (fun p : ℝ => (1 + p⁻¹) ^ 2 * (1 - p⁻¹) * (2 - p⁻¹)) Filter.atTop (nhds 2) := by
    have h1 : Filter.Tendsto (fun p : ℝ => (1 + p⁻¹) ^ 2) Filter.atTop (nhds 1) := by
      simpa using (hinv.const_add (1 : ℝ)).pow 2
    have h2 : Filter.Tendsto (fun p : ℝ => (1 : ℝ) - p⁻¹) Filter.atTop (nhds 1) := by
      simpa using (hinv.const_sub (1 : ℝ))
    have h3 : Filter.Tendsto (fun p : ℝ => (2 : ℝ) - p⁻¹) Filter.atTop (nhds 2) := by
      simpa using (hinv.const_sub (2 : ℝ))
    simpa using (h1.mul h2).mul h3
  have hlim : Filter.Tendsto
      (fun p : ℝ => 4 / ((1 + p⁻¹) ^ 2 * (1 - p⁻¹) * (2 - p⁻¹))) Filter.atTop (nhds 2) := by
    have hconst : Filter.Tendsto (fun _ : ℝ => (4 : ℝ)) Filter.atTop (nhds 4) :=
      tendsto_const_nhds
    have h2 := hconst.div hden (by norm_num)
    rw [show (4 : ℝ) / 2 = 2 by norm_num] at h2
    exact h2
  refine hlim.congr' ?_
  filter_upwards [Filter.eventually_ge_atTop (2 : ℝ)] with p hp
  exact (hrw p hp).symm

/-- **The Rees weight tends to zero.** -/
theorem tendsto_reesWeight : Filter.Tendsto reesWeight Filter.atTop (nhds 0) := by
  have hlog : Filter.Tendsto (fun p : ℝ => (Real.log p) ^ 2 / p) Filter.atTop (nhds 0) := by
    simpa using Real.tendsto_pow_log_div_mul_add_atTop 1 0 2 one_ne_zero
  have hprod : Filter.Tendsto
      (fun p : ℝ => (4 * p ^ 4 / ((p + 1) ^ 2 * (p - 1) * (2 * p - 1)))
        * ((Real.log p) ^ 2 / p)) Filter.atTop (nhds 0) := by
    simpa using tendsto_reesRational.mul hlog
  refine hprod.congr' ?_
  filter_upwards [Filter.eventually_ge_atTop (2 : ℝ)] with p hp
  have hp0 : p ≠ 0 := by linarith
  rw [reesWeight]
  field_simp

/-- The Rees weight is strictly positive beyond the first prime. -/
theorem reesWeight_pos {p : ℝ} (hp : 2 ≤ p) : 0 < reesWeight p := by
  have hlog : 0 < Real.log p := Real.log_pos (by linarith)
  have hnum : 0 < 4 * p ^ 3 * (Real.log p) ^ 2 := by positivity
  have h1 : (0 : ℝ) < (p + 1) ^ 2 := pow_pos (by linarith) 2
  have hden : 0 < (p + 1) ^ 2 * (p - 1) * (2 * p - 1) :=
    mul_pos (mul_pos h1 (by linarith)) (by linarith)
  rw [reesWeight]
  exact div_pos hnum hden

/-- **The cofinal Rees frame has no uniformly bounded inverse.** -/
theorem reesWeight_inv_unbounded (M : ℝ) : ∃ p : ℝ, 2 ≤ p ∧ M < (reesWeight p)⁻¹ := by
  set c : ℝ := max M 1 with hc
  have hc1 : (1 : ℝ) ≤ c := le_max_right _ _
  have hcM : M ≤ c := le_max_left _ _
  have hcpos : 0 < c := lt_of_lt_of_le one_pos hc1
  have hlt := tendsto_reesWeight.eventually_lt_const (show (0 : ℝ) < (2 * c)⁻¹ by positivity)
  obtain ⟨p, hp2, hpv⟩ := ((Filter.eventually_ge_atTop (2 : ℝ)).and hlt).exists
  refine ⟨p, hp2, ?_⟩
  have hpos := reesWeight_pos hp2
  have hinv : (2 * c) < (reesWeight p)⁻¹ := by
    rw [lt_inv_comm₀ (by positivity) hpos]
    exact hpv
  nlinarith

/-! ## Recurrent phase orbit with an unbounded clock history -/

/-- The lifted clock history of a single prime axis. -/
noncomputable def clockHistory (p : ℕ) (t : ℝ) : ℝ := -(t * Real.log p)

/-- **The lifted clock history is unbounded.**  The phase orbit is a bounded torus orbit, but its
logarithmic lift grows linearly in time. -/
theorem tendsto_abs_clockHistory {p : ℕ} (hp : p.Prime) :
    Filter.Tendsto (fun t : ℝ => |clockHistory p t|) Filter.atTop Filter.atTop := by
  have hlog : 0 < Real.log p := Real.log_pos (by exact_mod_cast hp.one_lt)
  have hgrow : Filter.Tendsto (fun t : ℝ => t * Real.log p) Filter.atTop Filter.atTop := by
    simpa using Filter.tendsto_id.atTop_mul_const hlog
  refine Filter.tendsto_atTop_mono (fun t => ?_) hgrow
  rw [clockHistory, abs_neg]
  exact le_abs_self _

/-! ## The normalised exchange law -/

/-- An affine Möbius derivative with a general nonzero constant denominator. -/
theorem hasDerivAt_affine_div_gen {A B Z W : ℝ} (hZ : Z ≠ 0) :
    HasDerivAt (fun e : ℝ => (A + e * B) / (Z + e * W)) ((B * Z - A * W) / Z ^ 2) 0 := by
  have h1 : HasDerivAt (fun e : ℝ => A + e * B) B 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).mul_const B).const_add A
  have h2 : HasDerivAt (fun e : ℝ => Z + e * W) W 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).mul_const W).const_add Z
  have hne : Z + (0 : ℝ) * W ≠ 0 := by simpa using hZ
  refine (h1.div h2 hne).congr_deriv ?_
  simp

/-- **The normalisation--phase exchange law.**  Differentiating the normalised observation in a
coefficient direction subtracts the radial component before phase observation. -/
theorem hasDerivAt_normalizedObservation {A B Z W : ℝ} (hZ : Z ≠ 0) :
    HasDerivAt (fun e : ℝ => (A + e * B) / (Z + e * W))
      (Z⁻¹ * (B - (A / Z) * W)) 0 := by
  refine (hasDerivAt_affine_div_gen (A := A) (B := B) (W := W) hZ).congr_deriv ?_
  field_simp

/-- **The covariance form of the exchange law.**  Against a normalised weight the exchange defect
is the fully centred second moment of the score against the phase. -/
theorem exchange_covariance {Ω : Type*} [Fintype Ω] {μ : Ω → ℝ} (hμ : ∑ ω, μ ω = 1)
    (r f : Ω → ℝ) :
    wcov μ r f = wexp μ (fun ω => (r ω - wexp μ r) * (f ω - wexp μ f)) := by
  have hexp : (fun ω => (r ω - wexp μ r) * (f ω - wexp μ f))
      = fun ω => r ω * f ω - (wexp μ r * f ω + wexp μ f * r ω - wexp μ r * wexp μ f) := by
    funext ω; ring
  rw [hexp, wexp_sub, wexp_sub, wexp_add, wexp_const_mul, wexp_const_mul,
    wexp_const hμ (wexp μ r * wexp μ f), wcov]
  ring

/-! ## The normalisation wall -/

/-- **The normalisation wall.**  Matching the physical half-density forces `m σ = 1`, which is
incompatible with a deep shell and a convergent Mellin abscissa. -/
theorem normalization_wall {m : ℕ} (hm : 12 ≤ m) {σ : ℝ} (hσ : 1 < σ) :
    (m : ℝ) * σ ≠ 1 := by
  have hm' : (12 : ℝ) ≤ m := by exact_mod_cast hm
  nlinarith


/-! ## Coefficient streams with all logarithmic moments -/

/-- The unit phase `e^{-i t log n}` of the atom `n`. -/
noncomputable def phaseChar (t : ℝ) (n : ℕ) : ℂ :=
  Complex.exp ((-(t * Real.log n) : ℝ) * Complex.I)

/-- The Dirichlet term `c_n n^{-σ-it}`, written as mass times phase. -/
noncomputable def phaseTerm (c : ℕ → ℝ) (σ : ℝ) (n : ℕ) (t : ℝ) : ℂ :=
  ((c n * (n : ℝ) ^ (-σ) : ℝ) : ℂ) * phaseChar t n

/-- The `k`-th time derivative of the Dirichlet term. -/
noncomputable def phaseTermDeriv (c : ℕ → ℝ) (σ : ℝ) (k n : ℕ) (t : ℝ) : ℂ :=
  ((-(Real.log n) : ℝ) * Complex.I) ^ k * phaseTerm c σ n t

/-- The `k`-th time derivative of the unnormalised Dirichlet series. -/
noncomputable def phaseSum (c : ℕ → ℝ) (σ : ℝ) (k : ℕ) (t : ℝ) : ℂ :=
  ∑' n : ℕ, phaseTermDeriv c σ k n t

/-- The total mass `Z_c = ∑ c_n n^{-σ}`. -/
noncomputable def totalMass (c : ℕ → ℝ) (σ : ℝ) : ℝ := ∑' n : ℕ, c n * (n : ℝ) ^ (-σ)

/-- Membership in the space of coefficient streams all of whose logarithmic moments converge
absolutely. -/
def MomentStream (c : ℕ → ℝ) (σ : ℝ) : Prop :=
  ∀ k : ℕ, Summable fun n : ℕ => |c n| * (n : ℝ) ^ (-σ) * (1 + Real.log n) ^ k

theorem norm_phaseChar (t : ℝ) (n : ℕ) : ‖phaseChar t n‖ = 1 := by
  rw [phaseChar, Complex.norm_exp_ofReal_mul_I]

theorem norm_phaseTermDeriv (c : ℕ → ℝ) (σ : ℝ) (k n : ℕ) (t : ℝ) :
    ‖phaseTermDeriv c σ k n t‖ = (Real.log n) ^ k * (|c n| * (n : ℝ) ^ (-σ)) := by
  have hlog : (0 : ℝ) ≤ Real.log n := Real.log_natCast_nonneg n
  have hrpow : (0 : ℝ) ≤ (n : ℝ) ^ (-σ) := Real.rpow_nonneg (Nat.cast_nonneg n) _
  simp only [phaseTermDeriv, phaseTerm, norm_mul, norm_pow, norm_phaseChar, mul_one,
    Complex.norm_I, Complex.norm_real, Real.norm_eq_abs, abs_neg]
  rw [abs_of_nonneg hlog, abs_of_nonneg hrpow]

/-- Each moment bound dominates the corresponding derivative term. -/
theorem norm_phaseTermDeriv_le (c : ℕ → ℝ) (σ : ℝ) (k n : ℕ) (t : ℝ) :
    ‖phaseTermDeriv c σ k n t‖ ≤ |c n| * (n : ℝ) ^ (-σ) * (1 + Real.log n) ^ k := by
  have hlog : (0 : ℝ) ≤ Real.log n := Real.log_natCast_nonneg n
  have hrpow : (0 : ℝ) ≤ (n : ℝ) ^ (-σ) := Real.rpow_nonneg (Nat.cast_nonneg n) _
  have hmass : (0 : ℝ) ≤ |c n| * (n : ℝ) ^ (-σ) := mul_nonneg (abs_nonneg _) hrpow
  have hpow : (Real.log n) ^ k ≤ (1 + Real.log n) ^ k :=
    pow_le_pow_left₀ hlog (by linarith) k
  rw [norm_phaseTermDeriv, mul_comm]
  exact mul_le_mul_of_nonneg_left hpow hmass

theorem summable_phaseTermDeriv {c : ℕ → ℝ} {σ : ℝ} (hc : MomentStream c σ) (k : ℕ) (t : ℝ) :
    Summable fun n : ℕ => phaseTermDeriv c σ k n t :=
  Summable.of_norm_bounded (hc k) fun n => norm_phaseTermDeriv_le c σ k n t

/-- Each Dirichlet term is differentiable in time, with derivative the next term. -/
theorem hasDerivAt_phaseTermDeriv (c : ℕ → ℝ) (σ : ℝ) (k n : ℕ) (t : ℝ) :
    HasDerivAt (fun s : ℝ => phaseTermDeriv c σ k n s) (phaseTermDeriv c σ (k + 1) n t) t := by
  have h0 : HasDerivAt (fun s : ℝ => s * -(Real.log n)) (-(Real.log n)) t := by
    simpa using (hasDerivAt_id t).mul_const (-(Real.log n))
  have hfun : (fun s : ℝ => s * -(Real.log n)) = fun s : ℝ => -(s * Real.log n) := by
    funext s; ring
  rw [hfun] at h0
  have hlin : HasDerivAt (fun s : ℝ => ((-(s * Real.log n) : ℝ) : ℂ))
      (((-(Real.log n) : ℝ) : ℂ)) t := by
    simpa using h0.ofReal_comp
  have hmul : HasDerivAt (fun s : ℝ => ((-(s * Real.log n) : ℝ) : ℂ) * Complex.I)
      (((-(Real.log n) : ℝ) : ℂ) * Complex.I) t := hlin.mul_const Complex.I
  have hexp := hmul.cexp
  have hfull := ((hexp.const_mul ((c n * (n : ℝ) ^ (-σ) : ℝ) : ℂ)).const_mul
    (((-(Real.log n) : ℝ) * Complex.I) ^ k))
  refine hfull.congr_deriv ?_
  simp only [phaseTermDeriv, phaseTerm, phaseChar, pow_succ]
  ring

/-- **Source intervention commutes with every time derivative.**  The `k`-th time derivative of the
Dirichlet series is the termwise series, for every `k`. -/
theorem hasDerivAt_phaseSum {c : ℕ → ℝ} {σ : ℝ} (hc : MomentStream c σ) (k : ℕ) (t : ℝ) :
    HasDerivAt (fun s : ℝ => phaseSum c σ k s) (phaseSum c σ (k + 1) t) t :=
  hasDerivAt_tsum_of_isPreconnected (hc (k + 1)) isOpen_univ
    (isPreconnected_univ) (fun n y _ => hasDerivAt_phaseTermDeriv c σ k n y)
    (fun n y _ => norm_phaseTermDeriv_le c σ (k + 1) n y) (Set.mem_univ 0)
    (summable_phaseTermDeriv hc k 0) (Set.mem_univ t)

/-! ## The exact normalisation--phase exchange -/

/-- The normalised expectation of an observable against a coefficient stream. -/
noncomputable def streamExp (c : ℕ → ℝ) (σ : ℝ) (f : ℕ → ℂ) : ℂ :=
  ((totalMass c σ : ℝ) : ℂ)⁻¹ * ∑' n : ℕ, ((c n * (n : ℝ) ^ (-σ) : ℝ) : ℂ) * f n

/-- The normalised phase observation `C_c(t)`. -/
noncomputable def normalizedObservation (c : ℕ → ℝ) (σ t : ℝ) : ℂ :=
  streamExp c σ (phaseChar t)

theorem summable_mass {c : ℕ → ℝ} {σ : ℝ} (hc : MomentStream c σ) :
    Summable fun n : ℕ => c n * (n : ℝ) ^ (-σ) := by
  refine Summable.of_norm_bounded (hc 0) fun n => ?_
  have hrpow : (0 : ℝ) ≤ (n : ℝ) ^ (-σ) := Real.rpow_nonneg (Nat.cast_nonneg n) _
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hrpow, pow_zero, mul_one]

theorem summable_phaseTerm {c : ℕ → ℝ} {σ : ℝ} (hc : MomentStream c σ) (t : ℝ) :
    Summable fun n : ℕ => phaseTerm c σ n t := by
  have := summable_phaseTermDeriv hc 0 t
  simpa [phaseTermDeriv] using this

theorem totalMass_add {c h : ℕ → ℝ} {σ : ℝ} (hc : MomentStream c σ) (hh : MomentStream h σ)
    (e : ℝ) : totalMass (fun n => c n + e * h n) σ = totalMass c σ + e * totalMass h σ := by
  have hsplit : ∀ n : ℕ, (c n + e * h n) * (n : ℝ) ^ (-σ)
      = c n * (n : ℝ) ^ (-σ) + e * (h n * (n : ℝ) ^ (-σ)) := fun n => by ring
  rw [totalMass, funext hsplit,
    (summable_mass hc).tsum_add ((summable_mass hh).mul_left e),
    tsum_mul_left, totalMass, totalMass]

theorem phaseSum_add {c h : ℕ → ℝ} {σ : ℝ} (hc : MomentStream c σ) (hh : MomentStream h σ)
    (e t : ℝ) :
    ∑' n : ℕ, phaseTerm (fun n => c n + e * h n) σ n t
      = (∑' n : ℕ, phaseTerm c σ n t) + (e : ℂ) * ∑' n : ℕ, phaseTerm h σ n t := by
  have hsplit : ∀ n : ℕ, phaseTerm (fun n => c n + e * h n) σ n t
      = phaseTerm c σ n t + (e : ℂ) * phaseTerm h σ n t := by
    intro n
    simp only [phaseTerm]
    push_cast
    ring
  rw [funext hsplit, (summable_phaseTerm hc t).tsum_add ((summable_phaseTerm hh t).mul_left _),
    tsum_mul_left]

/-- An affine Möbius derivative with complex numerator and real denominator. -/
theorem hasDerivAt_affine_div_complex {A B : ℂ} {Z W : ℝ} (hZ : Z ≠ 0) :
    HasDerivAt (fun e : ℝ => ((Z + e * W : ℝ) : ℂ)⁻¹ * (A + (e : ℂ) * B))
      ((Z : ℂ)⁻¹ * (B - (W : ℂ) * ((Z : ℂ)⁻¹ * A))) 0 := by
  have hZC : (Z : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hZ
  have h1 : HasDerivAt (fun e : ℝ => A + (e : ℂ) * B) B 0 := by
    have := ((Complex.ofRealCLM.hasDerivAt (x := (0 : ℝ))).mul_const B).const_add A
    simpa using this
  have h2 : HasDerivAt (fun e : ℝ => ((Z + e * W : ℝ) : ℂ)) ((W : ℝ) : ℂ) 0 := by
    have hr : HasDerivAt (fun e : ℝ => Z + e * W) W 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).mul_const W).const_add Z
    simpa using hr.ofReal_comp
  have hne : (((Z + (0 : ℝ) * W : ℝ) : ℂ)) ≠ 0 := by
    simpa using hZC
  have hinv : HasDerivAt (fun e : ℝ => ((Z + e * W : ℝ) : ℂ)⁻¹)
      (-((W : ℝ) : ℂ) / (((Z + (0 : ℝ) * W : ℝ) : ℂ)) ^ 2) 0 := h2.inv hne
  have hprod := hinv.mul h1
  refine hprod.congr_deriv ?_
  push_cast
  rw [zero_mul, add_zero, zero_mul, add_zero]
  field_simp
  ring

/-- **The normalisation--phase exchange law.**  The derivative of the normalised observation in a
coefficient direction subtracts the radial component before phase observation. -/
theorem hasDerivAt_normalizedObservation_stream {c h : ℕ → ℝ} {σ : ℝ}
    (hc : MomentStream c σ) (hh : MomentStream h σ) (hZ : totalMass c σ ≠ 0) (t : ℝ) :
    HasDerivAt (fun e : ℝ => normalizedObservation (fun n => c n + e * h n) σ t)
      (((totalMass c σ : ℝ) : ℂ)⁻¹ *
        ((∑' n : ℕ, phaseTerm h σ n t)
          - ((totalMass h σ : ℝ) : ℂ) * normalizedObservation c σ t)) 0 := by
  have hbase := hasDerivAt_affine_div_complex (A := ∑' n : ℕ, phaseTerm c σ n t)
    (B := ∑' n : ℕ, phaseTerm h σ n t) (Z := totalMass c σ) (W := totalMass h σ) hZ
  have hfun : (fun e : ℝ => normalizedObservation (fun n => c n + e * h n) σ t)
      = fun e : ℝ => ((totalMass c σ + e * totalMass h σ : ℝ) : ℂ)⁻¹ *
          ((∑' n : ℕ, phaseTerm c σ n t) + (e : ℂ) * ∑' n : ℕ, phaseTerm h σ n t) := by
    funext e
    rw [normalizedObservation, streamExp, totalMass_add hc hh e, ← phaseSum_add hc hh e t]
    rfl
  rw [hfun]
  refine hbase.congr_deriv ?_
  rw [normalizedObservation, streamExp]
  rfl

/-- **The covariance form of the exchange.**  A multiplicative score turns the exchange derivative
into the bilinear covariance of the score against the phase. -/
theorem exchange_bilinear (c r : ℕ → ℝ) (σ t : ℝ) :
    ((totalMass c σ : ℝ) : ℂ)⁻¹ *
        ((∑' n : ℕ, phaseTerm (fun n => c n * r n) σ n t)
          - ((totalMass (fun n => c n * r n) σ : ℝ) : ℂ) * normalizedObservation c σ t)
      = streamExp c σ (fun n => (r n : ℂ) * phaseChar t n)
        - streamExp c σ (fun n => (r n : ℂ)) * streamExp c σ (phaseChar t) := by
  have hnum : ∀ n : ℕ, phaseTerm (fun n => c n * r n) σ n t
      = ((c n * (n : ℝ) ^ (-σ) : ℝ) : ℂ) * ((r n : ℂ) * phaseChar t n) := by
    intro n
    simp only [phaseTerm]
    push_cast
    ring
  have hmass : totalMass (fun n => c n * r n) σ = ∑' n : ℕ, (c n * (n : ℝ) ^ (-σ)) * r n := by
    rw [totalMass]
    exact tsum_congr fun n => by ring
  rw [funext hnum, hmass, normalizedObservation, streamExp, streamExp, streamExp]
  have hreal : ((∑' n : ℕ, (c n * (n : ℝ) ^ (-σ)) * r n : ℝ) : ℂ)
      = ∑' n : ℕ, ((c n * (n : ℝ) ^ (-σ) : ℝ) : ℂ) * ((r n : ℝ) : ℂ) := by
    rw [Complex.ofReal_tsum]
    exact tsum_congr fun n => by push_cast; ring
  rw [hreal]
  ring

/-- The space of moment streams is inhabited by every finitely supported stream. -/
theorem momentStream_of_finite_support (c : ℕ → ℝ) (s : Finset ℕ) (hs : ∀ n ∉ s, c n = 0)
    (σ : ℝ) : MomentStream c σ := by
  intro k
  refine summable_of_ne_finset_zero (s := s) fun n hn => ?_
  rw [hs n hn]
  simp

/-! ## The four-axis frame theorem -/

/-- **One literal source, four compatible axes.**  On a finite prime aperture the marked shell
stream recovers every prime clock; the clock generator, the phase flow and the Gamma--Rees frame
are diagonal in the marked basis, hence commute and restrict strictly; the flow solves the clock
equation; the phase orbit returns arbitrarily close to the identity at arbitrarily late times
while its logarithmic lift is unbounded; and the Rees frame has no uniformly bounded inverse. -/
theorem four_axis_frame {m : ℕ} (hm : m ≠ 0) (G : Finset Nat.Primes) {ε T : ℝ}
    (hε : 0 < ε) (hT : 0 < T) {p : ℕ} (hp : p.Prime) (M : ℝ) :
    (∀ k : ℕ, (logCoeffOperator)^[k] (fun n => ((unitalShellIndicator m n : ℤ) : ℝ)) (p ^ m)
        = (-((m : ℝ) * Real.log p)) ^ k)
      ∧ (∀ (lam l : Fin 1 → ℝ) (t : ℝ) (x : Fin 1 → ℂ),
          clockGen lam (reesFrame l x) = reesFrame l (clockGen lam x)
            ∧ phaseFlow lam t (reesFrame l x) = reesFrame l (phaseFlow lam t x)
            ∧ phaseFlow lam t (clockGen lam x) = clockGen lam (phaseFlow lam t x))
      ∧ (∀ (lam : Fin 1 → ℝ) (x : Fin 1 → ℂ) (q : Fin 1) (t : ℝ),
          HasDerivAt (fun s : ℝ => phaseFlow lam s x q)
            (-Complex.I * (lam q : ℂ) * phaseFlow lam t x q) t)
      ∧ (∃ t : ℝ, T ≤ t ∧ ∀ q : G, ‖shellFlow (F := G) m t q - 1‖ < ε)
      ∧ Filter.Tendsto (fun t : ℝ => |clockHistory p t|) Filter.atTop Filter.atTop
      ∧ (∃ q : ℝ, 2 ≤ q ∧ M < (reesWeight q)⁻¹) := by
  refine ⟨fun k => shell_clock_recovery hm hp k, fun lam l t x => diagonal_commute lam l t x,
    fun lam x q t => hasDerivAt_phaseFlow lam x q t, exists_large_return m G hε hT,
    tendsto_abs_clockHistory hp, reesWeight_inv_unbounded M⟩

/-- **The normalisation--phase exchange is the full Theorem 4.1 package.**  Termwise time
differentiation of every order, the exchange derivative, and its covariance form. -/
theorem normalization_exchange {c h r : ℕ → ℝ} {σ : ℝ}
    (hc : MomentStream c σ) (hh : MomentStream h σ) (hZ : totalMass c σ ≠ 0) (t : ℝ) :
    (∀ k : ℕ, HasDerivAt (fun s : ℝ => phaseSum c σ k s) (phaseSum c σ (k + 1) t) t)
      ∧ HasDerivAt (fun e : ℝ => normalizedObservation (fun n => c n + e * h n) σ t)
          (((totalMass c σ : ℝ) : ℂ)⁻¹ *
            ((∑' n : ℕ, phaseTerm h σ n t)
              - ((totalMass h σ : ℝ) : ℂ) * normalizedObservation c σ t)) 0
      ∧ ((totalMass c σ : ℝ) : ℂ)⁻¹ *
          ((∑' n : ℕ, phaseTerm (fun n => c n * r n) σ n t)
            - ((totalMass (fun n => c n * r n) σ : ℝ) : ℂ) * normalizedObservation c σ t)
        = streamExp c σ (fun n => (r n : ℂ) * phaseChar t n)
          - streamExp c σ (fun n => (r n : ℂ)) * streamExp c σ (phaseChar t) :=
  ⟨fun k => hasDerivAt_phaseSum hc k t,
    hasDerivAt_normalizedObservation_stream hc hh hZ t,
    exchange_bilinear c r σ t⟩

end HTGeometry.ConstraintFrameRelativity
