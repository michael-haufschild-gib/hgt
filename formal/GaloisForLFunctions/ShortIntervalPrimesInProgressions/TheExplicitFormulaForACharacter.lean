import GaloisForLFunctions.ShortIntervalPrimesInProgressions.TheZerosOfAPrimitiveLFunction
import GaloisForLFunctions.RHTower.LagExplicitFormula

/-!
# The explicit formula for a primitive character

Let `χ` be a primitive nonprincipal character mod `N`, of parity `a ∈ {0, 1}`, and put
`ψ(X, χ) = Σ_{n ≤ X} χ(n) Λ(n)`, `S(X, χ) = Σ_{n ≤ X} χ(n) Λ(n)/n`. For `X > 1`,

`X S(X, χ) − ψ(X, χ) = −Σ_ρ X^ρ/(ρ(ρ − 1)) + αX + β + γ' log X + O(1/X)`,

the sum over the zeros of `Λ(s, χ)` with multiplicity, absolutely convergent
(`explicitFormula`).

Mechanism, as for `ζ` (`RHTower.lag_explicit_formula`): the Perron integral
`(1/2πi)∫_{(2)} (−L'/L)(s) X^s/(s(s−1)) ds` is evaluated twice. On the Dirichlet side it is
`Σ_n χ(n)Λ(n)(X/n − 1)_+`. On the other side `−L'/L = −Λ'/Λ + Γ_ℝ'/Γ_ℝ(s + a)`, the Hadamard
partial fraction of `Λ'/Λ` and the digamma series turn the integrand into rational terms, each
integrated by residues; the interchange is dominated by `(1+t²)^{−3/4}` and
`Σ_ρ |ρ − 2|^{−3/2} < ∞`. The trivial zeros `−a − 2k ≠ 0` contribute `O(1/X)`, the trivial zero
at `0` of an even character contributes `log X`.
-/

open Complex Filter Topology MeasureTheory
open GaloisForLFunctions.HTGeometry GaloisForLFunctions.EntireZeroDivisor
open ArithmeticFunction (vonMangoldt)

namespace GaloisForLFunctions.ShortIntervalPrimesInProgressions

noncomputable section

variable {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N}

/-! ### The archimedean factor -/

open scoped Classical in
/-- The parity `a = 0` (even) or `1` (odd), so that the gamma factor is `Γ_ℝ(s + a)`. -/
def parity (χ : DirichletCharacter ℂ N) : ℕ := if χ.Even then 0 else 1

omit [NeZero N] in
theorem parity_le_one (χ : DirichletCharacter ℂ N) : parity χ ≤ 1 := by
  classical
  unfold parity; split_ifs <;> norm_num

omit [NeZero N] in
theorem gammaFactor_eq (s : ℂ) : χ.gammaFactor s = Complex.Gammaℝ (s + parity χ) := by
  classical
  unfold parity
  rcases χ.even_or_odd with h | h
  · rw [h.gammaFactor_def, if_pos h]; simp
  · have hne : ¬ χ.Even := fun he => by
      have h1 : χ (-1) = 1 := he
      have h2 : χ (-1) = -1 := h
      rw [h1] at h2
      norm_num at h2
    rw [h.gammaFactor_def, if_neg hne]; simp

/-! ### The twisted von Mangoldt series -/

/-- The twisted von Mangoldt function `χ(n) Λ(n)`. -/
def twistedVM (χ : DirichletCharacter ℂ N) (n : ℕ) : ℂ := χ n * ((vonMangoldt n : ℝ) : ℂ)

omit [NeZero N] in
theorem norm_twistedVM_le (n : ℕ) : ‖twistedVM χ n‖ ≤ vonMangoldt n := by
  rw [twistedVM, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]
  exact mul_le_of_le_one_left ArithmeticFunction.vonMangoldt_nonneg (χ.norm_le_one _)

omit [NeZero N] in
theorem differentiableAt_gammaFactor {s : ℂ} (hs : 0 < s.re) :
    DifferentiableAt ℂ χ.gammaFactor s := by
  have h : χ.gammaFactor = fun w => Complex.Gammaℝ (w + parity χ) := funext gammaFactor_eq
  rw [h]
  have hre : 0 < (s + parity χ).re := by
    rw [add_re, natCast_re]; positivity
  exact ((RHTower.hasDerivAt_Gammaℝ_of_re_pos hre).differentiableAt).comp s
    (differentiableAt_id.add_const _)

omit [NeZero N] in
theorem logDeriv_gammaFactor {s : ℂ} (hs : 0 < s.re) :
    logDeriv χ.gammaFactor s =
      Complex.digamma ((s + parity χ) / 2) / 2 - (Real.log Real.pi : ℂ) / 2 := by
  have h : χ.gammaFactor = Complex.Gammaℝ ∘ (fun w => w + parity χ) := funext gammaFactor_eq
  have hre : 0 < (s + parity χ).re := by
    rw [add_re, natCast_re]; positivity
  rw [h, logDeriv_comp (g := fun w => w + (parity χ : ℂ))
    ((RHTower.hasDerivAt_Gammaℝ_of_re_pos hre).differentiableAt)
    (differentiableAt_id.add_const _)]
  simp only [deriv_add_const, deriv_id'', mul_one]
  exact RHTower.logDeriv_Gammaℝ_digamma hre

/-- `−L'/L` is the twisted von Mangoldt series on `Re s > 1`. -/
theorem lseries_twistedVM_eq {s : ℂ} (hs : 1 < s.re) :
    LSeries (twistedVM χ) s = -logDeriv (DirichletCharacter.LFunction χ) s := by
  have h := DirichletCharacter.LSeries_twist_vonMangoldt_eq χ hs
  have hev : (fun w => LSeries (fun n => χ n) w) =ᶠ[𝓝 s] DirichletCharacter.LFunction χ := by
    filter_upwards [(continuous_re.isOpen_preimage _ isOpen_Ioi).mem_nhds hs] with w hw
    exact (DirichletCharacter.LFunction_eq_LSeries χ hw).symm
  have hval := DirichletCharacter.LFunction_eq_LSeries χ hs
  have h1 : LSeries (twistedVM χ) s =
      LSeries ((fun n : ℕ => χ n) * fun n : ℕ => ((vonMangoldt n : ℝ) : ℂ)) s := rfl
  rw [h1, h, logDeriv_apply, ← hev.deriv_eq, hval, neg_div]

/-- `Λ'/Λ = L'/L + Γ'/Γ` on `Re s > 1`. -/
theorem logDeriv_completed_eq_add (hχ : χ ≠ 1) {s : ℂ} (hs : 1 < s.re) :
    logDeriv (DirichletCharacter.completedLFunction χ) s =
      logDeriv (DirichletCharacter.LFunction χ) s + logDeriv χ.gammaFactor s := by
  have hpos : 0 < s.re := by linarith
  have hev : DirichletCharacter.completedLFunction χ =ᶠ[𝓝 s]
      fun w => DirichletCharacter.LFunction χ w * χ.gammaFactor w := by
    filter_upwards [(continuous_re.isOpen_preimage _ isOpen_Ioi).mem_nhds hpos] with w hw
    rw [completedLFunction_eq_mul hw, mul_comm]
  have hL : DirichletCharacter.LFunction χ s ≠ 0 :=
    DirichletCharacter.LFunction_ne_zero_of_one_le_re χ (Or.inl hχ) hs.le
  have hG : χ.gammaFactor s ≠ 0 := gammaFactor_ne_zero hpos
  rw [logDeriv_apply, hev.deriv_eq, hev.eq_of_nhds, ← logDeriv_apply,
    logDeriv_mul s hL hG ((DirichletCharacter.differentiableAt_LFunction χ s (Or.inl
      (fun h1 => by rw [h1, one_re] at hs; exact lt_irrefl 1 hs)))) (differentiableAt_gammaFactor hpos)]

/-! ### The partial fraction on the line `Re s = 2` -/

/-- The digamma term of index `k`, with the parity shift. -/
def digammaTerm (χ : DirichletCharacter ℂ N) (s : ℂ) (k : ℕ) : ℂ :=
  1 / ((k : ℂ) + 1) - 2 / (s + parity χ + 2 * k)

/-- **The partial fraction of `−L'/L`.** On `Re s = 2`,
`−L'/L(s) = c − Σ_ρ ((s − ρ)⁻¹ + (ρ − 2)⁻¹) + ½ Σ_k (1/(k+1) − 2/(s + a + 2k))`. -/
theorem lseries_lineTwo (hχ : χ ≠ 1) :
    ∃ c : ℂ, ∀ t : ℝ, LSeries (twistedVM χ) (lineTwo t) =
      c - ∑' q : LZero χ, ((lineTwo t - q.point)⁻¹ + (q.point - 2)⁻¹) +
        (1 / 2 : ℂ) * ∑' k : ℕ, digammaTerm χ (lineTwo t) k := by
  obtain ⟨A, hA⟩ := logDeriv_completedLFunction_eq hχ
  refine ⟨-A - (Real.eulerMascheroniConstant : ℂ) / 2 - (Real.log Real.pi : ℂ) / 2, fun t => ?_⟩
  have hre : 1 < (lineTwo t).re := by rw [lineTwo_re]; norm_num
  have hpos : 0 < (lineTwo t).re := by linarith
  have hΛ : DirichletCharacter.completedLFunction χ (lineTwo t) ≠ 0 :=
    completedLFunction_ne_zero_of_one_le_re hχ hre.le
  have hw : 0 < ((lineTwo t + parity χ) / 2).re := by
    rw [div_re, add_re, natCast_re, lineTwo_re]; norm_num; positivity
  have hdig := RHTower.digamma_eq_tsum hw
  have hterms : (fun k : ℕ => 1 / ((k : ℂ) + 1) - 1 / ((lineTwo t + parity χ) / 2 + k)) =
      digammaTerm χ (lineTwo t) := by
    funext k
    unfold digammaTerm
    rw [show (lineTwo t + parity χ) / 2 + (k : ℂ) = (lineTwo t + parity χ + 2 * k) / 2 by ring,
      one_div_div]
  rw [hterms] at hdig
  have hsplit := logDeriv_completed_eq_add hχ hre
  have hL : logDeriv (DirichletCharacter.LFunction χ) (lineTwo t) =
      logDeriv (DirichletCharacter.completedLFunction χ) (lineTwo t) -
        logDeriv χ.gammaFactor (lineTwo t) := by rw [hsplit]; ring
  rw [lseries_twistedVM_eq hre, hL, hA _ hΛ, logDeriv_gammaFactor hpos, hdig]
  ring

/-! ### The Dirichlet side -/

/-- The `n`-th Dirichlet term of the twisted Perron integrand. -/
def twistedTerm (χ : DirichletCharacter ℂ N) (X : ℝ) (n : ℕ) (t : ℝ) : ℂ :=
  LSeries.term (twistedVM χ) (lineTwo t) n * RHTower.lagKernel X t

omit [NeZero N] in
theorem twistedTerm_eq {X : ℝ} (hX : 0 < X) {n : ℕ} (hn : n ≠ 0) (t : ℝ) :
    twistedTerm χ X n t =
      twistedVM χ n * (((X / n : ℝ) : ℂ) ^ lineTwo t / (lineTwo t * (lineTwo t - 1))) := by
  unfold twistedTerm RHTower.lagKernel
  rw [LSeries.term_of_ne_zero hn]
  have hn0 : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
  have hcp : (((X / n : ℝ) : ℂ) ^ lineTwo t) = (X : ℂ) ^ lineTwo t / (n : ℂ) ^ lineTwo t := by
    rw [show (X / n : ℝ) = X * (n : ℝ)⁻¹ by ring, Complex.ofReal_mul,
      Complex.mul_cpow_ofReal_nonneg hX.le (by positivity), Complex.ofReal_inv,
      Complex.ofReal_natCast,
      Complex.inv_cpow _ _ (by rw [← Complex.ofReal_natCast, Complex.arg_ofReal_of_nonneg hn0.le]; exact Real.pi_pos.ne'.symm)]
    exact (div_eq_mul_inv _ _).symm
  rw [hcp]
  ring

omit [NeZero N] in
theorem twistedTerm_zero (X : ℝ) (t : ℝ) : twistedTerm χ X 0 t = 0 := by
  unfold twistedTerm; rw [LSeries.term_zero, zero_mul]

omit [NeZero N] in
theorem integrable_twistedTerm {X : ℝ} (hX : 0 < X) (n : ℕ) :
    Integrable (twistedTerm χ X n) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · have h0 : twistedTerm χ X 0 = fun _ => 0 := funext (twistedTerm_zero X)
    rw [h0]; exact integrable_zero _ _ _
  · have hXn : (0 : ℝ) < X / n := by positivity
    have := (integrable_lineTwo_basic hXn).const_mul (twistedVM χ n)
    refine this.congr (Filter.Eventually.of_forall fun t => ?_)
    rw [twistedTerm_eq hX hn.ne']

omit [NeZero N] in
theorem integral_norm_twistedTerm_le {X : ℝ} (hX : 0 < X) (n : ℕ) :
    ∫ t : ℝ, ‖twistedTerm χ X n t‖ ≤
      ∫ t : ℝ, ‖RHTower.dirichletTerm X n t‖ := by
  refine integral_mono (integrable_twistedTerm hX n).norm
    (RHTower.integrable_dirichletTerm hX n).norm fun t => ?_
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [twistedTerm_zero, RHTower.dirichletTerm_zero]
  · rw [twistedTerm_eq hX hn.ne', RHTower.dirichletTerm_eq hX hn.ne', norm_mul, norm_mul,
      Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]
    exact mul_le_mul_of_nonneg_right (norm_twistedVM_le n) (norm_nonneg _)

omit [NeZero N] in
/-- **The Dirichlet side.** `(1/2π)∫ (−L'/L)(s) X^s/(s(s−1)) dt = Σ_{n≤X} χ(n)Λ(n)(X/n − 1)`. -/
theorem dirichlet_side {X : ℝ} (hX : 1 < X) :
    (1 / (2 * Real.pi) : ℝ) • ∫ t : ℝ, LSeries (twistedVM χ) (lineTwo t) * RHTower.lagKernel X t
      = ∑ n ∈ Finset.Icc 1 ⌊X⌋₊, twistedVM χ n * ((X : ℂ) / n - 1) := by
  have hX0 : 0 < X := by linarith
  have hsum : Summable (fun n : ℕ => ∫ t : ℝ, ‖twistedTerm χ X n t‖) :=
    Summable.of_nonneg_of_le (fun n => integral_nonneg fun t => norm_nonneg _)
      (fun n => integral_norm_twistedTerm_le hX0 n) (RHTower.summable_integral_norm_dirichletTerm hX0)
  have hint : (fun t : ℝ => LSeries (twistedVM χ) (lineTwo t) * RHTower.lagKernel X t)
      = fun t : ℝ => ∑' n : ℕ, twistedTerm χ X n t := by
    funext t
    unfold LSeries twistedTerm
    rw [tsum_mul_right]
  rw [hint, ← integral_tsum_of_summable_integral_norm (integrable_twistedTerm hX0) hsum]
  have hterm : ∀ n : ℕ, (1 / (2 * Real.pi) : ℝ) • ∫ t : ℝ, twistedTerm χ X n t =
      twistedVM χ n * (if 1 < X / n then ((X / n : ℝ) : ℂ) - 1 else 0) := by
    intro n
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp [twistedTerm_zero, twistedVM]
    · have hXn : (0 : ℝ) < X / n := by positivity
      have h := perron_lineTwo_basic hXn
      have hI : ∫ t : ℝ, twistedTerm χ X n t = twistedVM χ n *
          ∫ t : ℝ, ((X / n : ℝ) : ℂ) ^ lineTwo t / (lineTwo t * (lineTwo t - 1)) := by
        rw [← integral_const_mul]
        exact integral_congr_ae (Filter.Eventually.of_forall fun t => twistedTerm_eq hX0 hn.ne' t)
      rw [hI, ← h, Complex.real_smul, Complex.real_smul]
      ring
  rw [RHTower.smul_tsum_eq]
  simp_rw [hterm]
  rw [tsum_eq_sum (s := Finset.Icc 1 ⌊X⌋₊)]
  · refine Finset.sum_congr rfl fun n hn => ?_
    rw [Finset.mem_Icc] at hn
    have hn0 : (0 : ℝ) < n := by exact_mod_cast hn.1
    have hnX : (n : ℝ) ≤ X := (Nat.cast_le.mpr hn.2).trans (Nat.floor_le hX0.le)
    by_cases h : 1 < X / n
    · rw [if_pos h]; push_cast; ring
    · rw [if_neg h]
      have hle : X / n ≤ 1 := not_lt.mp h
      have heq : X / n = 1 := le_antisymm hle (by rw [le_div_iff₀ hn0]; linarith)
      have hXn : (X : ℂ) / n = 1 := by
        have := congrArg (fun r : ℝ => (r : ℂ)) heq
        push_cast at this; exact this
      rw [hXn]; ring
  · intro n hn
    rw [Finset.mem_Icc] at hn
    rcases Nat.eq_zero_or_pos n with rfl | hnpos
    · simp [twistedVM]
    · have hgt : ¬ (1 < X / n) := by
        intro h1
        have hn0 : (0 : ℝ) < n := by exact_mod_cast hnpos
        rw [one_lt_div hn0] at h1
        exact hn ⟨hnpos, Nat.le_floor h1.le⟩
      rw [if_neg hgt, mul_zero]

/-! ### The Mittag-Leffler side: termwise bounds -/

/-- The zero term times the kernel. -/
def zTermL (χ : DirichletCharacter ℂ N) (X : ℝ) (q : LZero χ) (t : ℝ) : ℂ :=
  ((lineTwo t - q.point)⁻¹ + (q.point - 2)⁻¹) * RHTower.lagKernel X t

/-- The digamma term times the kernel. -/
def kTermL (χ : DirichletCharacter ℂ N) (X : ℝ) (k : ℕ) (t : ℝ) : ℂ :=
  digammaTerm χ (lineTwo t) k * RHTower.lagKernel X t

/-- The trivial-zero abscissa `−(a + 2k)`. -/
def trivialPoint (χ : DirichletCharacter ℂ N) (k : ℕ) : ℂ := -((parity χ : ℂ) + 2 * k)

omit [NeZero N] in
theorem trivialPoint_re (k : ℕ) : (trivialPoint χ k).re = -((parity χ : ℝ) + 2 * k) := by
  simp [trivialPoint]

omit [NeZero N] in
theorem trivialPoint_re_lt (k : ℕ) : (trivialPoint χ k).re < 2 := by
  rw [trivialPoint_re]
  have := Nat.cast_nonneg (α := ℝ) (parity χ)
  have := Nat.cast_nonneg (α := ℝ) k
  linarith

omit [NeZero N] in
theorem trivialPoint_ne_one (k : ℕ) : trivialPoint χ k ≠ 1 := by
  intro h
  have := congrArg Complex.re h
  rw [trivialPoint_re, one_re] at this
  have := Nat.cast_nonneg (α := ℝ) (parity χ)
  have := Nat.cast_nonneg (α := ℝ) k
  linarith

omit [NeZero N] in
theorem lineTwo_sub_trivialPoint (k : ℕ) (t : ℝ) :
    lineTwo t - trivialPoint χ k = lineTwo t + parity χ + 2 * k := by
  rw [trivialPoint]; ring

theorem lagKernel_le_two (X : ℝ) (hX : 0 < X) (t : ℝ) :
    ‖RHTower.lagKernel X t‖ ≤ 2 * X ^ 2 / (1 + |t|) ^ 2 := by
  refine (RHTower.norm_lagKernel_le hX t).trans ?_
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith [abs_nonneg t, sq_abs t, sq_nonneg (1 - |t|), sq_nonneg X]

/-- Zero terms: `|(s − ρ)⁻¹ + (ρ − 2)⁻¹| ≤ 2(1+|t|)/(|ρ − 2|(1+|t − γ|))` on the line. -/
theorem norm_zFactorL_le (hχ : χ ≠ 1) (hprim : χ.IsPrimitive) (q : LZero χ) (t : ℝ) :
    ‖(lineTwo t - q.point)⁻¹ + (q.point - 2)⁻¹‖ ≤
      2 * (1 + |t|) / (‖q.point - 2‖ * (1 + |t - q.point.im|)) := by
  have hre := (zero_re_mem hχ hprim q).2
  have hq2 : q.point - 2 ≠ 0 := by
    intro h; have := congrArg Complex.re h; rw [sub_re] at this; norm_num at this; linarith
  have hs : lineTwo t - q.point ≠ 0 := lineTwo_sub_ne_zero (by linarith) t
  have hid : (lineTwo t - q.point)⁻¹ + (q.point - 2)⁻¹ =
      (lineTwo t - 2) / ((lineTwo t - q.point) * (q.point - 2)) := by
    rw [inv_add_inv hs hq2]; congr 1; ring
  rw [hid, norm_div, norm_mul]
  have h1 : ‖lineTwo t - 2‖ ≤ 1 + |t| := by
    rw [show lineTwo t - 2 = (t : ℂ) * I by unfold lineTwo; push_cast; ring, norm_mul,
      Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs]
    linarith
  have h2 : (1 + |t - q.point.im|) / 2 ≤ ‖lineTwo t - q.point‖ := by
    have hw : lineTwo t - q.point = ((2 - q.point.re : ℝ) : ℂ) + ((t - q.point.im : ℝ) : ℂ) * I := by
      apply Complex.ext <;> simp [lineTwo]
    rw [hw, Complex.norm_add_mul_I]
    apply Real.le_sqrt_of_sq_le
    have hre1 : 1 ≤ 2 - q.point.re := by linarith
    nlinarith [abs_nonneg (t - q.point.im), sq_abs (t - q.point.im),
      sq_nonneg (1 - |t - q.point.im|)]
  have hqn : 0 < ‖q.point - 2‖ := norm_pos_iff.mpr hq2
  calc ‖lineTwo t - 2‖ / (‖lineTwo t - q.point‖ * ‖q.point - 2‖)
      ≤ (1 + |t|) / (((1 + |t - q.point.im|) / 2) * ‖q.point - 2‖) := by gcongr
    _ = 2 * (1 + |t|) / (‖q.point - 2‖ * (1 + |t - q.point.im|)) := by field_simp

/-- `|γ|`-control: `‖ρ − 2‖ ≤ 2(1 + |γ|)`. -/
theorem norm_point_sub_two_le (hχ : χ ≠ 1) (hprim : χ.IsPrimitive) (q : LZero χ) :
    ‖q.point - 2‖ ≤ 2 * (1 + |q.point.im|) := by
  have h := Complex.norm_le_abs_re_add_abs_im (q.point - 2)
  have hr := zero_re_mem hχ hprim q
  have habs : |(q.point - 2).re| ≤ 2 := by
    rw [sub_re, abs_le]; norm_num; constructor <;> linarith
  have him : (q.point - 2).im = q.point.im := by simp
  rw [him] at h
  linarith [abs_nonneg q.point.im]

theorem norm_zTermL_le (hχ : χ ≠ 1) (hprim : χ.IsPrimitive) {X : ℝ} (hX : 0 < X) (q : LZero χ)
    (t : ℝ) :
    ‖zTermL χ X q t‖ ≤ (8 * X ^ 2 * ‖q.point - 2‖ ^ (-(3 / 2 : ℝ))) *
      ((1 + t ^ 2) ^ (-(3 / 4 : ℝ)) + (1 + (t - q.point.im) ^ 2) ^ (-(3 / 4 : ℝ))) := by
  unfold zTermL
  rw [norm_mul]
  have hq2 : 0 < ‖q.point - 2‖ := by
    rw [norm_pos_iff]; intro h; have := congrArg Complex.re h
    rw [sub_re] at this; norm_num at this; linarith [(zero_re_mem hχ hprim q).2]
  have h1 := norm_zFactorL_le hχ hprim q t
  have h2 := lagKernel_le_two X hX t
  have h3 := two_centre_majorant q.point.im t
  have h4 : (1 + |q.point.im|) ^ (-(1 / 2 : ℝ)) ≤ Real.sqrt 2 * ‖q.point - 2‖ ^ (-(1 / 2 : ℝ)) := by
    have hle := norm_point_sub_two_le hχ hprim q
    have hA : 0 < (1 + |q.point.im|) ^ (1 / 2 : ℝ) := by positivity
    have hB : 0 < ‖q.point - 2‖ ^ (1 / 2 : ℝ) := Real.rpow_pos_of_pos hq2 _
    have hBA : ‖q.point - 2‖ ^ (1 / 2 : ℝ) ≤ Real.sqrt 2 * (1 + |q.point.im|) ^ (1 / 2 : ℝ) := by
      rw [← Real.sqrt_eq_rpow, ← Real.sqrt_eq_rpow, ← Real.sqrt_mul (by norm_num)]
      exact Real.sqrt_le_sqrt (by linarith)
    rw [Real.rpow_neg (by positivity), Real.rpow_neg hq2.le, ← div_eq_mul_inv, le_div_iff₀ hB,
      inv_mul_eq_div, div_le_iff₀ hA]
    exact hBA
  set M := (1 + t ^ 2) ^ (-(3 / 4 : ℝ)) + (1 + (t - q.point.im) ^ 2) ^ (-(3 / 4 : ℝ))
  have hM : 0 ≤ M := by positivity
  have hrp : ‖q.point - 2‖ ^ (-(3 / 2 : ℝ)) = ‖q.point - 2‖⁻¹ * ‖q.point - 2‖ ^ (-(1 / 2 : ℝ)) := by
    rw [← Real.rpow_neg_one, ← Real.rpow_add hq2]; norm_num
  calc ‖(lineTwo t - q.point)⁻¹ + (q.point - 2)⁻¹‖ * ‖RHTower.lagKernel X t‖
      ≤ (2 * (1 + |t|) / (‖q.point - 2‖ * (1 + |t - q.point.im|))) * (2 * X ^ 2 / (1 + |t|) ^ 2) :=
        mul_le_mul h1 h2 (norm_nonneg _) (by positivity)
    _ = (4 * X ^ 2 / ‖q.point - 2‖) * (1 / ((1 + |t - q.point.im|) * (1 + |t|))) := by
        have : (0 : ℝ) < 1 + |t| := by positivity
        field_simp
        norm_num
    _ ≤ (4 * X ^ 2 / ‖q.point - 2‖) * (Real.sqrt 2 * (1 + |q.point.im|) ^ (-(1 / 2 : ℝ)) * M) := by
        gcongr
    _ ≤ (4 * X ^ 2 / ‖q.point - 2‖) * (Real.sqrt 2 * (Real.sqrt 2 * ‖q.point - 2‖ ^ (-(1 / 2 : ℝ))) * M) := by
        gcongr
    _ = (8 * X ^ 2 * ‖q.point - 2‖ ^ (-(3 / 2 : ℝ))) * M := by
        rw [hrp, show Real.sqrt 2 * (Real.sqrt 2 * ‖q.point - 2‖ ^ (-(1 / 2 : ℝ))) =
          (Real.sqrt 2 * Real.sqrt 2) * ‖q.point - 2‖ ^ (-(1 / 2 : ℝ)) by ring,
          Real.mul_self_sqrt (by norm_num)]
        field_simp
        ring

theorem continuous_zTermL (hχ : χ ≠ 1) (hprim : χ.IsPrimitive) {X : ℝ} (hX : 0 < X)
    (q : LZero χ) : Continuous (zTermL χ X q) := by
  unfold zTermL
  have hre := (zero_re_mem hχ hprim q).2
  refine Continuous.mul (Continuous.add ?_ continuous_const) (RHTower.continuous_lagKernel hX)
  exact Continuous.inv₀ (by unfold lineTwo; fun_prop) (fun t => lineTwo_sub_ne_zero (by linarith) t)

theorem integrable_zTermL (hχ : χ ≠ 1) (hprim : χ.IsPrimitive) {X : ℝ} (hX : 0 < X)
    (q : LZero χ) : Integrable (zTermL χ X q) :=
  ((RHTower.integrable_majorant_shift q.point.im).const_mul _).mono'
    (continuous_zTermL hχ hprim hX q).aestronglyMeasurable
    (Filter.Eventually.of_forall fun t => norm_zTermL_le hχ hprim hX q t)

theorem integral_norm_zTermL_le (hχ : χ ≠ 1) (hprim : χ.IsPrimitive) {X : ℝ} (hX : 0 < X)
    (q : LZero χ) :
    ∫ t : ℝ, ‖zTermL χ X q t‖ ≤ (16 * X ^ 2 * RHTower.majorantMass) *
      ‖zeroCopyPoint (shiftedL χ) q‖ ^ (-(3 / 2 : ℝ)) := by
  have hpt : q.point - 2 = zeroCopyPoint (shiftedL χ) q := by simp [LZero.point]
  calc ∫ t : ℝ, ‖zTermL χ X q t‖
      ≤ ∫ t : ℝ, (8 * X ^ 2 * ‖q.point - 2‖ ^ (-(3 / 2 : ℝ))) *
          ((1 + t ^ 2) ^ (-(3 / 4 : ℝ)) + (1 + (t - q.point.im) ^ 2) ^ (-(3 / 4 : ℝ))) :=
        integral_mono (integrable_zTermL hχ hprim hX q).norm
          ((RHTower.integrable_majorant_shift _).const_mul _) (norm_zTermL_le hχ hprim hX q)
    _ = _ := by
        rw [integral_const_mul, RHTower.integral_majorant_shift, hpt]
        ring

theorem summable_integral_norm_zTermL (hχ : χ ≠ 1) (hprim : χ.IsPrimitive) {X : ℝ} (hX : 0 < X) :
    Summable (fun q : LZero χ => ∫ t : ℝ, ‖zTermL χ X q t‖) :=
  Summable.of_nonneg_of_le (fun _ => integral_nonneg fun _ => norm_nonneg _)
    (fun q => integral_norm_zTermL_le hχ hprim hX q)
    ((summable_norm_rpow_neg hχ (α := 3 / 2) (by norm_num)).mul_left _)

omit [NeZero N] in
/-- Digamma terms: `|1/(k+1) − 2/(s + a + 2k)| ≤ (1+|t|)^{1/2}/(k+1)^{3/2}` on the line. -/
theorem norm_digammaTerm_le (k : ℕ) (t : ℝ) :
    ‖digammaTerm χ (lineTwo t) k‖ ≤ Real.sqrt (1 + |t|) / ((k : ℝ) + 1) ^ (3 / 2 : ℝ) := by
  have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have ha0 : (0 : ℝ) ≤ parity χ := Nat.cast_nonneg _
  have ha1 : (parity χ : ℝ) ≤ 1 := by exact_mod_cast parity_le_one χ
  have hk1 : ((k : ℂ) + 1) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero k
  have hs : lineTwo t + parity χ + 2 * k ≠ 0 := by
    intro h; have := congrArg Complex.re h; simp [lineTwo] at this; linarith
  have hid : digammaTerm χ (lineTwo t) k =
      (lineTwo t + parity χ - 2) / (((k : ℂ) + 1) * (lineTwo t + parity χ + 2 * k)) := by
    unfold digammaTerm
    rw [div_sub_div _ _ hk1 hs]
    congr 1
    ring
  rw [hid, norm_div, norm_mul]
  have h1 : ‖lineTwo t + parity χ - 2‖ ≤ 1 + |t| := by
    rw [show lineTwo t + parity χ - 2 = ((parity χ : ℝ) : ℂ) + t * I by unfold lineTwo; push_cast; ring,
      Complex.norm_add_mul_I, Real.sqrt_le_left (by positivity)]
    nlinarith [abs_nonneg t, sq_abs t]
  have h2 : ‖(k : ℂ) + 1‖ = (k : ℝ) + 1 := by
    rw [show (k : ℂ) + 1 = (((k : ℝ) + 1 : ℝ) : ℂ) by push_cast; ring, Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  have h3 : Real.sqrt (((k : ℝ) + 1) * (1 + |t|)) ≤ ‖lineTwo t + parity χ + 2 * k‖ := by
    rw [show lineTwo t + parity χ + 2 * k = ((2 + parity χ + 2 * k : ℝ) : ℂ) + t * I by
      unfold lineTwo; push_cast; ring, Complex.norm_add_mul_I]
    apply Real.sqrt_le_sqrt
    nlinarith [abs_nonneg t, sq_abs t, sq_nonneg (2 + (parity χ : ℝ) + 2 * k - |t|)]
  rw [h2]
  have hkpos : (0 : ℝ) < (k : ℝ) + 1 := by positivity
  have hsq : 0 < Real.sqrt (((k : ℝ) + 1) * (1 + |t|)) := Real.sqrt_pos.mpr (by positivity)
  calc ‖lineTwo t + parity χ - 2‖ / (((k : ℝ) + 1) * ‖lineTwo t + parity χ + 2 * k‖)
      ≤ (1 + |t|) / (((k : ℝ) + 1) * Real.sqrt (((k : ℝ) + 1) * (1 + |t|))) := by gcongr
    _ = Real.sqrt (1 + |t|) / ((k : ℝ) + 1) ^ (3 / 2 : ℝ) := by
        rw [Real.sqrt_mul hkpos.le, show ((k : ℝ) + 1) ^ (3 / 2 : ℝ) =
          ((k : ℝ) + 1) * Real.sqrt ((k : ℝ) + 1) by
            rw [Real.sqrt_eq_rpow, ← Real.rpow_one_add' hkpos.le (by norm_num)]; norm_num]
        have h1t : (0 : ℝ) < 1 + |t| := by positivity
        have := Real.sq_sqrt h1t.le
        field_simp
        nlinarith [Real.sqrt_nonneg (1 + |t|), Real.sqrt_pos.mpr h1t]

omit [NeZero N] in
theorem norm_kTermL_le {X : ℝ} (hX : 0 < X) (k : ℕ) (t : ℝ) :
    ‖kTermL χ X k t‖ ≤ (2 * X ^ 2 / ((k : ℝ) + 1) ^ (3 / 2 : ℝ)) * (1 + t ^ 2) ^ (-(3 / 4 : ℝ)) := by
  unfold kTermL
  rw [norm_mul]
  have h1 := norm_digammaTerm_le (χ := χ) k t
  have h2 := lagKernel_le_two X hX t
  have ht1 : (0 : ℝ) < 1 + |t| := by positivity
  have hmaj : Real.sqrt (1 + |t|) / (1 + |t|) ^ 2 ≤ (1 + t ^ 2) ^ (-(3 / 4 : ℝ)) := by
    have hle : 1 + t ^ 2 ≤ (1 + |t|) ^ 2 := by nlinarith [abs_nonneg t, sq_abs t]
    have hpow : Real.sqrt (1 + |t|) / (1 + |t|) ^ 2 = ((1 + |t|) ^ 2) ^ (-(3 / 4 : ℝ)) := by
      rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul ht1.le, div_eq_mul_inv,
        ← Real.rpow_neg ht1.le, ← Real.rpow_add ht1]
      norm_num
    rw [hpow]
    exact Real.rpow_le_rpow_of_nonpos (by positivity) hle (by norm_num)
  calc ‖digammaTerm χ (lineTwo t) k‖ * ‖RHTower.lagKernel X t‖
      ≤ (Real.sqrt (1 + |t|) / ((k : ℝ) + 1) ^ (3 / 2 : ℝ)) * (2 * X ^ 2 / (1 + |t|) ^ 2) :=
        mul_le_mul h1 h2 (norm_nonneg _) (by positivity)
    _ = (2 * X ^ 2 / ((k : ℝ) + 1) ^ (3 / 2 : ℝ)) * (Real.sqrt (1 + |t|) / (1 + |t|) ^ 2) := by
        ring
    _ ≤ _ := by gcongr

omit [NeZero N] in
theorem continuous_kTermL {X : ℝ} (hX : 0 < X) (k : ℕ) : Continuous (kTermL χ X k) := by
  unfold kTermL digammaTerm
  have ha0 : (0 : ℝ) ≤ parity χ := Nat.cast_nonneg _
  have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  refine Continuous.mul (Continuous.sub continuous_const (Continuous.div continuous_const
    (by unfold lineTwo; fun_prop) fun t h => ?_)) (RHTower.continuous_lagKernel hX)
  have := congrArg Complex.re h
  simp [lineTwo] at this
  linarith

omit [NeZero N] in
theorem integrable_kTermL {X : ℝ} (hX : 0 < X) (k : ℕ) : Integrable (kTermL χ X k) :=
  (integrable_one_add_sq_rpow_neg_three_quarters.const_mul _).mono'
    (continuous_kTermL hX k).aestronglyMeasurable
    (Filter.Eventually.of_forall fun t => norm_kTermL_le hX k t)

omit [NeZero N] in
theorem summable_integral_norm_kTermL {X : ℝ} (hX : 0 < X) :
    Summable (fun k : ℕ => ∫ t : ℝ, ‖kTermL χ X k t‖) := by
  have hb : Summable (fun k : ℕ => (2 * X ^ 2 * RHTower.majorantMass) *
      (((k : ℝ) + 1) ^ (3 / 2 : ℝ))⁻¹) := by
    have := (summable_nat_add_iff 1).mpr
      ((Real.summable_nat_rpow_inv (p := 3 / 2)).mpr (by norm_num))
    exact (by exact_mod_cast this : Summable fun k : ℕ => (((k : ℝ) + 1) ^ (3 / 2 : ℝ))⁻¹).mul_left _
  refine Summable.of_nonneg_of_le (fun _ => integral_nonneg fun _ => norm_nonneg _) (fun k => ?_) hb
  calc ∫ t : ℝ, ‖kTermL χ X k t‖
      ≤ ∫ t : ℝ, (2 * X ^ 2 / ((k : ℝ) + 1) ^ (3 / 2 : ℝ)) * (1 + t ^ 2) ^ (-(3 / 4 : ℝ)) :=
        integral_mono (integrable_kTermL hX k).norm
          (integrable_one_add_sq_rpow_neg_three_quarters.const_mul _) (norm_kTermL_le hX k)
    _ = _ := by
        rw [integral_const_mul]
        unfold RHTower.majorantMass
        ring

/-! ### Termwise integrals -/

/-- The value of the integrated zero term. -/
def zVal (X : ℝ) (ρ : ℂ) : ℂ := (ρ - 2)⁻¹ * ((X : ℂ) - 1) + (1 / ρ) * (((X : ℂ) ^ ρ - X) / (ρ - 1) - (X - 1))

/-- The value of the integrated digamma term. -/
def kVal (χ : DirichletCharacter ℂ N) (X : ℝ) (k : ℕ) : ℂ :=
  (1 / ((k : ℂ) + 1)) * ((X : ℂ) - 1) - 2 * (if trivialPoint χ k = 0 then (X : ℂ) - 1 - Complex.log X
    else (1 / trivialPoint χ k) * (((X : ℂ) ^ trivialPoint χ k - X) / (trivialPoint χ k - 1) - (X - 1)))

theorem integral_zTermL (hχ : χ ≠ 1) (hprim : χ.IsPrimitive) {X : ℝ} (hX : 1 < X) (q : LZero χ) :
    (1 / (2 * Real.pi) : ℝ) • ∫ t : ℝ, zTermL χ X q t = zVal X q.point := by
  have hX0 : 0 < X := by linarith
  have hre := (zero_re_mem hχ hprim q).2
  have hare : q.point.re < 2 := by linarith
  have ha0 := point_ne_zero hχ hprim q
  have ha1 := point_ne_one hχ hprim q
  have hq2 : q.point - 2 ≠ 0 := by
    intro h; have := congrArg Complex.re h; rw [sub_re] at this; norm_num at this; linarith
  have hsplit : ∀ t : ℝ, zTermL χ X q t = (q.point - 2)⁻¹ * RHTower.lagKernel X t +
      (X : ℂ) ^ lineTwo t / ((lineTwo t - q.point) * lineTwo t * (lineTwo t - 1)) := by
    intro t
    unfold zTermL RHTower.lagKernel
    have h0 := lineTwo_ne_zero t
    have h1 := lineTwo_sub_one_ne_zero t
    have h2 := lineTwo_sub_ne_zero hare t
    field_simp
    ring
  simp_rw [hsplit]
  have hI1 := (RHTower.integrable_lagKernel hX0).const_mul (q.point - 2)⁻¹
  have hI2 : Integrable (fun t : ℝ =>
      (X : ℂ) ^ lineTwo t / ((lineTwo t - q.point) * lineTwo t * (lineTwo t - 1))) := by
    have := ((integrable_lineTwo_shift hare hX0).sub (integrable_lineTwo_basic hX0)).const_mul
      (1 / q.point)
    refine this.congr (Filter.Eventually.of_forall fun t => ?_)
    have h0 := lineTwo_ne_zero t
    have h1 := lineTwo_sub_one_ne_zero t
    have h2 := lineTwo_sub_ne_zero hare t
    simp only [Pi.sub_apply]
    field_simp
    ring
  rw [integral_add hI1 hI2, integral_const_mul, smul_add, ← mul_smul_comm,
    perron_lineTwo_threePole hare ha0 ha1 hX]
  have hb := perron_lineTwo_basic hX0
  rw [if_pos hX] at hb
  unfold RHTower.lagKernel
  rw [hb, zVal]

omit [NeZero N] in
theorem integral_kTermL {X : ℝ} (hX : 1 < X) (k : ℕ) :
    (1 / (2 * Real.pi) : ℝ) • ∫ t : ℝ, kTermL χ X k t = kVal χ X k := by
  have hX0 : 0 < X := by linarith
  set p := trivialPoint χ k with hp
  have hare : p.re < 2 := trivialPoint_re_lt k
  have hsplit : ∀ t : ℝ, kTermL χ X k t = (1 / ((k : ℂ) + 1)) * RHTower.lagKernel X t -
      2 * ((X : ℂ) ^ lineTwo t / ((lineTwo t - p) * lineTwo t * (lineTwo t - 1))) := by
    intro t
    unfold kTermL digammaTerm RHTower.lagKernel
    have h0 := lineTwo_ne_zero t
    have h1 := lineTwo_sub_one_ne_zero t
    have h2 := lineTwo_sub_ne_zero hare t
    have hsp : lineTwo t + parity χ + 2 * k = lineTwo t - p := (lineTwo_sub_trivialPoint k t).symm
    rw [hsp]
    field_simp
  simp_rw [hsplit]
  have hI1 := (RHTower.integrable_lagKernel hX0).const_mul (1 / ((k : ℂ) + 1))
  have hI2 : Integrable (fun t : ℝ =>
      (X : ℂ) ^ lineTwo t / ((lineTwo t - p) * lineTwo t * (lineTwo t - 1))) := by
    have h := (integrable_lineTwo_shift hare hX0).sub (integrable_lineTwo_basic hX0)
    by_cases hp0 : p = 0
    · rw [hp0]
      have h2 := (integrable_lineTwo_sq hX0)
      have := (integrable_lineTwo_basic hX0).sub h2
      refine this.congr (Filter.Eventually.of_forall fun t => ?_)
      have h0 := lineTwo_ne_zero t
      have h1 := lineTwo_sub_one_ne_zero t
      simp only [Pi.sub_apply, sub_zero]
      field_simp
      ring
    · refine (h.const_mul (1 / p)).congr (Filter.Eventually.of_forall fun t => ?_)
      have h0 := lineTwo_ne_zero t
      have h1 := lineTwo_sub_one_ne_zero t
      have h2 := lineTwo_sub_ne_zero hare t
      simp only [Pi.sub_apply]
      field_simp
      ring
  rw [integral_sub hI1 (hI2.const_mul 2), integral_const_mul, integral_const_mul, smul_sub,
    ← mul_smul_comm, ← mul_smul_comm]
  have hb := perron_lineTwo_basic hX0
  rw [if_pos hX] at hb
  unfold RHTower.lagKernel
  rw [hb, kVal]
  by_cases hp0 : p = 0
  · rw [if_pos hp0]
    have hsq := perron_lineTwo_sq hX
    have heq : (fun t : ℝ => (X : ℂ) ^ lineTwo t / ((lineTwo t - p) * lineTwo t * (lineTwo t - 1)))
        = fun t : ℝ => (X : ℂ) ^ lineTwo t / (lineTwo t ^ 2 * (lineTwo t - 1)) := by
      funext t; rw [hp0, sub_zero, sq]
    rw [heq, hsq]
  · rw [if_neg hp0, perron_lineTwo_threePole hare hp0 (trivialPoint_ne_one k) hX]

/-! ### The Mittag-Leffler side -/

theorem countable_LZero (hχ : χ ≠ 1) : Countable (LZero χ) := by
  have hloc := locallyFinite_zeroCopyPoint (analyticOnNhd_shiftedL hχ)
  have huniv : (Set.univ : Set (LZero χ)) =
      ⋃ n : ℕ, {p | ‖zeroCopyPoint (shiftedL χ) p‖ ≤ n} := by
    ext p
    simp only [Set.mem_univ, Set.mem_iUnion, Set.mem_setOf_eq, true_iff]
    exact exists_nat_ge _
  exact Set.countable_univ_iff.mp (huniv ▸ Set.countable_iUnion fun n => (hloc n).countable)

theorem summable_zVal (hχ : χ ≠ 1) (hprim : χ.IsPrimitive) {X : ℝ} (hX : 1 < X) :
    Summable (fun q : LZero χ => zVal X q.point) := by
  have hX0 : 0 < X := by linarith
  refine Summable.of_norm_bounded (g := fun q => (1 / (2 * Real.pi)) * ∫ t : ℝ, ‖zTermL χ X q t‖)
    ((summable_integral_norm_zTermL hχ hprim hX0).mul_left _) fun q => ?_
  rw [← integral_zTermL hχ hprim hX q, norm_smul, Real.norm_eq_abs,
    abs_of_pos (by positivity)]
  exact mul_le_mul_of_nonneg_left (norm_integral_le_integral_norm _) (by positivity)

omit [NeZero N] in
theorem summable_kVal {X : ℝ} (hX : 1 < X) : Summable (fun k : ℕ => kVal χ X k) := by
  have hX0 : 0 < X := by linarith
  refine Summable.of_norm_bounded (g := fun k => (1 / (2 * Real.pi)) * ∫ t : ℝ, ‖kTermL χ X k t‖)
    ((summable_integral_norm_kTermL hX0).mul_left _) fun k => ?_
  rw [← integral_kTermL hX k, norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity)]
  exact mul_le_mul_of_nonneg_left (norm_integral_le_integral_norm _) (by positivity)

/-- **The two evaluations agree.** `X S(X, χ) − ψ(X, χ) = c(X − 1) − Σ_ρ zVal + ½ Σ_k kVal`. -/
theorem explicit_identity (hχ : χ ≠ 1) (hprim : χ.IsPrimitive) :
    ∃ c : ℂ, ∀ X : ℝ, 1 < X →
      ∑ n ∈ Finset.Icc 1 ⌊X⌋₊, twistedVM χ n * ((X : ℂ) / n - 1) =
        c * ((X : ℂ) - 1) - ∑' q : LZero χ, zVal X q.point + (1 / 2 : ℂ) * ∑' k : ℕ, kVal χ X k := by
  obtain ⟨c, hc⟩ := lseries_lineTwo (χ := χ) hχ
  refine ⟨c, fun X hX => ?_⟩
  have hX0 : 0 < X := by linarith
  rw [← dirichlet_side hX]
  have hpt : ∀ t : ℝ, LSeries (twistedVM χ) (lineTwo t) * RHTower.lagKernel X t =
      c * RHTower.lagKernel X t - ∑' q : LZero χ, zTermL χ X q t +
        (1 / 2 : ℂ) * ∑' k : ℕ, kTermL χ X k t := by
    intro t
    rw [hc t]
    unfold zTermL kTermL
    rw [tsum_mul_right, tsum_mul_right]
    ring
  simp_rw [hpt]
  haveI := countable_LZero hχ
  have hA := (RHTower.integrable_lagKernel hX0).const_mul c
  have hTq : Integrable (fun t : ℝ => ∑' q : LZero χ, zTermL χ X q t) :=
    RHTower.integrable_tsum_of_summable_integral_norm'
      (fun q => (continuous_zTermL hχ hprim hX0 q).measurable)
      (integrable_zTermL hχ hprim hX0) (summable_integral_norm_zTermL hχ hprim hX0)
  have hTk : Integrable (fun t : ℝ => ∑' k : ℕ, kTermL χ X k t) :=
    RHTower.integrable_tsum_of_summable_integral_norm' (fun k => (continuous_kTermL hX0 k).measurable)
      (integrable_kTermL hX0) (summable_integral_norm_kTermL hX0)
  rw [integral_add (f := fun t => c * RHTower.lagKernel X t - ∑' q : LZero χ, zTermL χ X q t)
      (g := fun t => (1 / 2 : ℂ) * ∑' k : ℕ, kTermL χ X k t) (hA.sub hTq) (hTk.const_mul _),
    integral_sub (f := fun t => c * RHTower.lagKernel X t)
      (g := fun t => ∑' q : LZero χ, zTermL χ X q t) hA hTq, integral_const_mul,
    integral_const_mul,
    ← integral_tsum_of_summable_integral_norm (integrable_zTermL hχ hprim hX0)
      (summable_integral_norm_zTermL hχ hprim hX0),
    ← integral_tsum_of_summable_integral_norm (integrable_kTermL hX0)
      (summable_integral_norm_kTermL hX0)]
  rw [smul_add, smul_sub, ← mul_smul_comm, ← mul_smul_comm, RHTower.smul_tsum_eq,
    RHTower.smul_tsum_eq]
  have hb := perron_lineTwo_basic hX0
  rw [if_pos hX] at hb
  unfold RHTower.lagKernel
  rw [hb]
  simp_rw [integral_zTermL hχ hprim hX, integral_kTermL hX]

/-! ### Regrouping -/

/-- Two evaluations of an affine family give the summability of both coefficients. -/
theorem summable_affine {ι : Type*} {a b : ι → ℂ} {x₁ x₂ : ℂ} (hx : x₁ ≠ x₂)
    (h₁ : Summable fun i => a i * x₁ + b i) (h₂ : Summable fun i => a i * x₂ + b i) :
    Summable a ∧ Summable b := by
  have hd : x₁ - x₂ ≠ 0 := sub_ne_zero.mpr hx
  have ha : Summable a := ((h₁.sub h₂).div_const (x₁ - x₂)).congr fun i => by
    field_simp; ring
  exact ⟨ha, (h₁.sub (ha.mul_right x₁)).congr fun i => by ring⟩

/-- The `X`-coefficient of an integrated zero term. -/
def uCoef (ρ : ℂ) : ℂ := ((ρ - 2) * (ρ - 1))⁻¹

/-- The constant of an integrated zero term. -/
def vCoef (ρ : ℂ) : ℂ := -2 * (ρ * (ρ - 2))⁻¹

theorem zVal_eq {X : ℝ} (hX : 0 < X) {ρ : ℂ} (h0 : ρ ≠ 0) (h1 : ρ ≠ 1) (h2 : ρ ≠ 2) :
    zVal X ρ = (X : ℂ) ^ ρ / (ρ * (ρ - 1)) + X * uCoef ρ + vCoef ρ := by
  have h1' : ρ - 1 ≠ 0 := sub_ne_zero.mpr h1
  have h2' : ρ - 2 ≠ 0 := sub_ne_zero.mpr h2
  unfold zVal uCoef vCoef
  field_simp
  ring

theorem point_ne_two (hχ : χ ≠ 1) (hprim : χ.IsPrimitive) (q : LZero χ) : q.point ≠ 2 := by
  intro h
  have := (zero_re_mem hχ hprim q).2
  rw [h] at this
  norm_num at this

/-- `Σ_ρ X^ρ/(ρ(ρ − 1))` converges absolutely: cofinitely `|ρ| ≥ |ρ−2|/2`, `|ρ−1| ≥ 3|ρ−2|/4`. -/
theorem summable_cpow_div (hχ : χ ≠ 1) (hprim : χ.IsPrimitive) {X : ℝ} (hX : 1 < X) :
    Summable (fun q : LZero χ => (X : ℂ) ^ q.point / (q.point * (q.point - 1))) := by
  have hX0 : 0 < X := by linarith
  have hev := RHTower.eventually_norm_ge_of_summable_inv_sq (zeroCopyPoint_ne_zero' hχ)
    (summable_inv_sq hχ) (S := 4) (by norm_num)
  refine Summable.of_norm_bounded_eventually
    (g := fun q => (8 / 3 * X) * (1 / ‖zeroCopyPoint (shiftedL χ) q‖ ^ (2 : ℕ)))
    ((summable_inv_sq hχ).mul_left _) ?_
  filter_upwards [hev] with q hq
  set w := zeroCopyPoint (shiftedL χ) q
  have hpt : q.point = w + 2 := rfl
  have hw0 : 0 < ‖w‖ := by linarith
  have hρ : ‖w‖ / 2 ≤ ‖q.point‖ := by
    rw [hpt]
    have := norm_sub_norm_le w (-(2 : ℂ))
    rw [sub_neg_eq_add, norm_neg] at this
    norm_num at this
    linarith
  have hρ1 : 3 * ‖w‖ / 4 ≤ ‖q.point - 1‖ := by
    rw [hpt, show w + 2 - 1 = w - (-1) by ring]
    have := norm_sub_norm_le w (-1 : ℂ)
    rw [norm_neg, norm_one] at this
    linarith
  have hcp : ‖(X : ℂ) ^ q.point‖ ≤ X := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hX0]
    calc X ^ q.point.re ≤ X ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le hX.le (zero_re_mem hχ hprim q).2.le
      _ = X := Real.rpow_one X
  rw [norm_div, norm_mul]
  calc ‖(X : ℂ) ^ q.point‖ / (‖q.point‖ * ‖q.point - 1‖)
      ≤ X / ((‖w‖ / 2) * (3 * ‖w‖ / 4)) := by gcongr
    _ = (8 / 3 * X) * (1 / ‖w‖ ^ (2 : ℕ)) := by field_simp; ring

theorem summable_uv (hχ : χ ≠ 1) (hprim : χ.IsPrimitive) :
    Summable (fun q : LZero χ => uCoef q.point) ∧ Summable (fun q : LZero χ => vCoef q.point) := by
  have hrest : ∀ X : ℝ, 1 < X →
      Summable (fun q : LZero χ => uCoef q.point * X + vCoef q.point) := by
    intro X hX
    refine ((summable_zVal hχ hprim hX).sub (summable_cpow_div hχ hprim hX)).congr fun q => ?_
    rw [zVal_eq (by linarith) (point_ne_zero hχ hprim q) (point_ne_one hχ hprim q)
      (point_ne_two hχ hprim q)]
    ring
  exact summable_affine (x₁ := (2 : ℝ)) (x₂ := (3 : ℝ)) (by norm_num) (hrest 2 (by norm_num))
    (hrest 3 (by norm_num))

/-- The `X`-coefficient of an integrated digamma term. -/
def eCoef (χ : DirichletCharacter ℂ N) (k : ℕ) : ℂ :=
  if trivialPoint χ k = 0 then -1 else 1 / ((k : ℂ) + 1) + 2 / (trivialPoint χ k - 1)

/-- The constant of an integrated digamma term. -/
def fCoef (χ : DirichletCharacter ℂ N) (k : ℕ) : ℂ :=
  if trivialPoint χ k = 0 then 1 else -(1 / ((k : ℂ) + 1)) - 2 / trivialPoint χ k

/-- The `log X`-coefficient: the trivial zero at `0` of an even character. -/
def lCoef (χ : DirichletCharacter ℂ N) (k : ℕ) : ℂ := if trivialPoint χ k = 0 then 2 else 0

/-- The power term of a trivial zero `p ≠ 0`. -/
def gTerm (χ : DirichletCharacter ℂ N) (X : ℝ) (k : ℕ) : ℂ :=
  if trivialPoint χ k = 0 then 0
  else (X : ℂ) ^ trivialPoint χ k / (trivialPoint χ k * (trivialPoint χ k - 1))

omit [NeZero N] in
theorem kVal_eq (X : ℝ) (k : ℕ) :
    kVal χ X k = eCoef χ k * X + fCoef χ k + lCoef χ k * Complex.log X - 2 * gTerm χ X k := by
  unfold kVal eCoef fCoef lCoef gTerm
  have hk1 : ((k : ℂ) + 1) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero k
  by_cases hp : trivialPoint χ k = 0
  · simp only [if_pos hp]
    have hk0 : (k : ℂ) = 0 := by
      have := congrArg Complex.re hp
      rw [trivialPoint_re, zero_re] at this
      have ha := Nat.cast_nonneg (α := ℝ) (parity χ)
      have hk := Nat.cast_nonneg (α := ℝ) k
      have : (k : ℝ) = 0 := by linarith
      exact_mod_cast this
    rw [hk0]; ring
  · simp only [if_neg hp]
    have hp1 : trivialPoint χ k - 1 ≠ 0 := sub_ne_zero.mpr (trivialPoint_ne_one k)
    field_simp
    ring

omit [NeZero N] in
theorem norm_gTerm_le {X : ℝ} (hX : 1 < X) (k : ℕ) :
    ‖gTerm χ X k‖ ≤ X⁻¹ * (1 / ((k : ℝ) + 1) ^ (2 : ℕ)) := by
  have hX0 : 0 < X := by linarith
  unfold gTerm
  split_ifs with hp
  · rw [norm_zero]; positivity
  set r : ℝ := (parity χ : ℝ) + 2 * k with hr
  have hpr : trivialPoint χ k = ((-r : ℝ) : ℂ) := by rw [trivialPoint, hr]; push_cast; ring
  have hr0 : 0 ≤ r := by positivity
  have hnat : 1 ≤ parity χ + 2 * k := by
    by_contra h
    push Not at h
    have ha0 : parity χ = 0 := by omega
    have hk0 : k = 0 := by omega
    apply hp
    rw [trivialPoint, ha0, hk0]
    simp
  have hr1 : 1 ≤ r := by rw [hr]; exact_mod_cast hnat
  have hrk : (k : ℝ) + 1 ≤ r ∨ (k = 0) := by
    rcases Nat.eq_zero_or_pos k with hk | hk
    · exact Or.inr hk
    · left
      have : (1 : ℝ) ≤ k := by exact_mod_cast hk
      have := Nat.cast_nonneg (α := ℝ) (parity χ)
      rw [hr]; linarith
  rw [hpr, norm_div, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hX0, Complex.ofReal_re,
    show ((-r : ℝ) : ℂ) - 1 = ((-(r + 1) : ℝ) : ℂ) by push_cast; ring, Complex.norm_real,
    Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs, abs_neg, abs_neg,
    abs_of_nonneg hr0, abs_of_nonneg (by linarith : (0 : ℝ) ≤ r + 1)]
  have hXr : X ^ (-r) ≤ X⁻¹ := by
    rw [← Real.rpow_neg_one]
    exact Real.rpow_le_rpow_of_exponent_le hX.le (by linarith)
  have hden : ((k : ℝ) + 1) ^ (2 : ℕ) ≤ r * (r + 1) := by
    rcases hrk with h | h
    · nlinarith
    · rw [h]; push_cast; nlinarith
  calc X ^ (-r) / (r * (r + 1)) ≤ X⁻¹ / ((k : ℝ) + 1) ^ (2 : ℕ) := by
        gcongr
    _ = X⁻¹ * (1 / ((k : ℝ) + 1) ^ (2 : ℕ)) := by ring

theorem summable_inv_succ_sq : Summable (fun k : ℕ => 1 / ((k : ℝ) + 1) ^ (2 : ℕ)) := by
  have := (summable_nat_add_iff 1).mpr ((Real.summable_one_div_nat_pow (p := 2)).mpr one_lt_two)
  exact_mod_cast this

omit [NeZero N] in
theorem summable_gTerm {X : ℝ} (hX : 1 < X) : Summable (gTerm χ X) :=
  Summable.of_norm_bounded (summable_inv_succ_sq.mul_left X⁻¹) (norm_gTerm_le hX)

omit [NeZero N] in
theorem summable_lCoef : Summable (lCoef χ) := by
  refine summable_of_ne_finset_zero (s := {0}) fun k hk => ?_
  unfold lCoef
  rw [if_neg]
  intro hp
  have hk0 : k ≠ 0 := by simpa using hk
  have := congrArg Complex.re hp
  rw [trivialPoint_re, zero_re] at this
  have := Nat.cast_nonneg (α := ℝ) (parity χ)
  have : (1 : ℝ) ≤ k := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hk0
  linarith

omit [NeZero N] in
theorem summable_ef : Summable (eCoef χ) ∧ Summable (fCoef χ) := by
  have hrest : ∀ X : ℝ, 1 < X → Summable (fun k : ℕ => eCoef χ k * X + fCoef χ k) := by
    intro X hX
    refine (((summable_kVal (χ := χ) hX).sub ((summable_lCoef (χ := χ)).mul_right
      (Complex.log X))).add ((summable_gTerm (χ := χ) hX).mul_left 2)).congr fun k => ?_
    rw [kVal_eq]
    ring
  exact summable_affine (x₁ := (2 : ℝ)) (x₂ := (3 : ℝ)) (by norm_num) (hrest 2 (by norm_num))
    (hrest 3 (by norm_num))

/-- The coefficient `γ' = ½ Σ_k ℓ_k` of `log X` in the explicit formula (from the trivial zero at
`0` of an even character). -/
def efGamma (χ : DirichletCharacter ℂ N) : ℂ := (1 / 2) * ∑' k, lCoef χ k

/-- The constant `D = Σ_{k ≥ 0} (k+1)^{−2}` of the remainder `D/X` in the explicit formula. -/
def efD : ℝ := ∑' k : ℕ, 1 / ((k : ℝ) + 1) ^ (2 : ℕ)

theorem efD_nonneg : 0 ≤ efD := tsum_nonneg fun k => by positivity

omit [NeZero N] in
/-- `|γ'| ≤ 1`: only the trivial zero `0` of an even character contributes. -/
theorem norm_efGamma_le (χ : DirichletCharacter ℂ N) : ‖efGamma χ‖ ≤ 1 := by
  have h0 : ∀ k : ℕ, k ≠ 0 → lCoef χ k = 0 := by
    intro k hk
    unfold lCoef
    rw [if_neg]
    intro hp
    have := congrArg Complex.re hp
    rw [trivialPoint_re, zero_re] at this
    have := Nat.cast_nonneg (α := ℝ) (parity χ)
    have : (1 : ℝ) ≤ k := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hk
    linarith
  rw [efGamma, tsum_eq_single 0 h0]
  have : ‖lCoef χ 0‖ ≤ 2 := by
    unfold lCoef
    split_ifs <;> simp
  rw [norm_mul]
  calc ‖(1 / 2 : ℂ)‖ * ‖lCoef χ 0‖ ≤ ‖(1 / 2 : ℂ)‖ * 2 := by gcongr
    _ = 1 := by norm_num

/-- `D = ζ(2) ≤ 2`. -/
theorem efD_le_two : efD ≤ 2 := by
  have h := (hasSum_nat_add_iff' 1).mpr hasSum_zeta_two
  have h' : HasSum (fun k : ℕ => 1 / ((k : ℝ) + 1) ^ (2 : ℕ)) (Real.pi ^ 2 / 6) := by
    have e1 : (fun k : ℕ => 1 / ((k : ℝ) + 1) ^ (2 : ℕ))
        = fun n : ℕ => 1 / ((n + 1 : ℕ) : ℝ) ^ 2 := by
      funext k
      push_cast
      ring
    have e2 : Real.pi ^ 2 / 6
        = Real.pi ^ 2 / 6 - ∑ i ∈ Finset.range 1, 1 / ((i : ℕ) : ℝ) ^ 2 := by simp
    rw [e1, e2]
    exact h
  rw [efD, h'.tsum_eq]
  have := Real.pi_lt_d2
  have := Real.pi_pos
  nlinarith

/-- **The explicit formula for a primitive character, with uniform constants.** For `X > 1`,
`X S(X, χ) − ψ(X, χ) = −Σ_ρ X^ρ/(ρ(ρ−1)) + αX + β + γ' log X + Θ(X)` with `γ' = efGamma χ` and
`|Θ(X)| ≤ efD/X`. -/
theorem explicitFormula_uniform (hχ : χ ≠ 1) (hprim : χ.IsPrimitive) :
    ∃ α β : ℂ, ∀ X : ℝ, 1 < X →
      ‖∑ n ∈ Finset.Icc 1 ⌊X⌋₊, twistedVM χ n * ((X : ℂ) / n - 1) +
          ∑' q : LZero χ, (X : ℂ) ^ q.point / (q.point * (q.point - 1)) -
          (α * X + β + efGamma χ * Complex.log X)‖ ≤ efD / X := by
  obtain ⟨c, hc⟩ := explicit_identity hχ hprim
  obtain ⟨hu, hv⟩ := summable_uv hχ hprim
  obtain ⟨he, hf⟩ := summable_ef (χ := χ)
  set D : ℝ := ∑' k : ℕ, 1 / ((k : ℝ) + 1) ^ (2 : ℕ)
  refine ⟨c - ∑' q : LZero χ, uCoef q.point + (1 / 2) * ∑' k, eCoef χ k,
    -c - ∑' q : LZero χ, vCoef q.point + (1 / 2) * ∑' k, fCoef χ k, fun X hX => ?_⟩
  show _ ≤ D / X
  simp only [efGamma]
  have hX0 : 0 < X := by linarith
  have hz : ∑' q : LZero χ, zVal X q.point =
      ∑' q : LZero χ, (X : ℂ) ^ q.point / (q.point * (q.point - 1)) +
        X * ∑' q : LZero χ, uCoef q.point + ∑' q : LZero χ, vCoef q.point := by
    rw [← tsum_mul_left, ← (summable_cpow_div hχ hprim hX).tsum_add (hu.mul_left _),
      ← ((summable_cpow_div hχ hprim hX).add (hu.mul_left _)).tsum_add hv]
    exact tsum_congr fun q => zVal_eq hX0 (point_ne_zero hχ hprim q) (point_ne_one hχ hprim q)
      (point_ne_two hχ hprim q)
  have hk : ∑' k : ℕ, kVal χ X k = (∑' k, eCoef χ k) * X + ∑' k, fCoef χ k +
      (∑' k, lCoef χ k) * Complex.log X - 2 * ∑' k, gTerm χ X k := by
    rw [← tsum_mul_right, ← tsum_mul_right, ← tsum_mul_left,
      ← (he.mul_right _).tsum_add hf, ← ((he.mul_right _).add hf).tsum_add (summable_lCoef.mul_right _),
      ← (((he.mul_right _).add hf).add (summable_lCoef.mul_right _)).tsum_sub
        ((summable_gTerm hX).mul_left 2)]
    exact tsum_congr fun k => kVal_eq X k
  rw [hc X hX, hz, hk]
  have hg : ‖∑' k : ℕ, gTerm χ X k‖ ≤ X⁻¹ * D := by
    refine (norm_tsum_le_tsum_norm (summable_gTerm hX).norm).trans ?_
    rw [← tsum_mul_left]
    exact (summable_gTerm hX).norm.tsum_le_tsum (norm_gTerm_le hX) (summable_inv_succ_sq.mul_left _)
  calc ‖c * ((X : ℂ) - 1) - (∑' q : LZero χ, (X : ℂ) ^ q.point / (q.point * (q.point - 1)) +
          X * ∑' q : LZero χ, uCoef q.point + ∑' q : LZero χ, vCoef q.point) +
        (1 / 2 : ℂ) * ((∑' k, eCoef χ k) * X + ∑' k, fCoef χ k + (∑' k, lCoef χ k) * Complex.log X -
          2 * ∑' k, gTerm χ X k) +
        ∑' q : LZero χ, (X : ℂ) ^ q.point / (q.point * (q.point - 1)) -
        ((c - ∑' q : LZero χ, uCoef q.point + (1 / 2) * ∑' k, eCoef χ k) * X +
          (-c - ∑' q : LZero χ, vCoef q.point + (1 / 2) * ∑' k, fCoef χ k) +
          (1 / 2) * (∑' k, lCoef χ k) * Complex.log X)‖
        = ‖∑' k : ℕ, gTerm χ X k‖ := by
          rw [← norm_neg]; congr 1; ring
    _ ≤ X⁻¹ * D := hg
    _ = D / X := by ring

/-- **The explicit formula for a primitive character.** For `X > 1`,
`X S(X, χ) − ψ(X, χ) = −Σ_ρ X^ρ/(ρ(ρ−1)) + αX + β + γ' log X + Θ(X)`, `|Θ(X)| ≤ D/X`,
with `X S − ψ = Σ_{n ≤ X} χ(n)Λ(n)(X/n − 1)`. -/
theorem explicitFormula (hχ : χ ≠ 1) (hprim : χ.IsPrimitive) :
    ∃ α β γ' : ℂ, ∃ D : ℝ, 0 ≤ D ∧ ∀ X : ℝ, 1 < X →
      ‖∑ n ∈ Finset.Icc 1 ⌊X⌋₊, twistedVM χ n * ((X : ℂ) / n - 1) +
          ∑' q : LZero χ, (X : ℂ) ^ q.point / (q.point * (q.point - 1)) -
          (α * X + β + γ' * Complex.log X)‖ ≤ D / X := by
  obtain ⟨α, β, h⟩ := explicitFormula_uniform hχ hprim
  exact ⟨α, β, efGamma χ, efD, efD_nonneg, h⟩

end

end GaloisForLFunctions.ShortIntervalPrimesInProgressions
