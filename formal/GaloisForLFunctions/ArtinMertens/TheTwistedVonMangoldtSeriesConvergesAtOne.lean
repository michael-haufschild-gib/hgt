import GaloisForLFunctions.ArtinMertens.NewmansAnalyticTheorem
import GaloisForLFunctions.PNTPlus.Wiener

/-!
# The twisted von Mangoldt series converges at `s = 1`

For a nontrivial Dirichlet character `χ` mod `q`,

  `Σ_{n ≤ x} χ(n) Λ(n)/n → −L'(1, χ)/L(1, χ)`   (`tendsto_sum_twist_vonMangoldt_div`).

* **The Laplace transform** (`integral_twistLaplace_eq`): `f(u) = ψ(e^u, χ) e^{−u}`,
  `ψ(x, χ) = Σ_{n ≤ x} χ(n)Λ(n)`, is bounded by `log 4 + 4` (Chebyshev), and for `Re z > 0`
  `∫_0^∞ f(u) e^{−zu} du = L(z + 1, χΛ)/(z + 1)` (`LSeries_eq_mul_integral` and `x = e^u`).
* **Its continuation** (`analyticAt_twistNewmanG`): `L(χΛ, s) = −L'(s, χ)/L(s, χ)` is analytic on
  `Re s ≥ 1`, since `L(s, χ)` is entire and has no zero there.
* **Newman's theorem** gives `∫_1^x ψ(t, χ)/t² dt → −L'(1, χ)/L(1, χ)`; Abel summation
  `Σ_{n ≤ x} χ(n)Λ(n)/n = ψ(x, χ)/x + ∫_1^x ψ(t, χ)/t² dt`; and `ψ(x, χ) = o(x)` by the prime number
  theorem in progressions and the orthogonality `Σ_a χ(a) = 0` (`tendsto_twistPsi_div`).
-/

noncomputable section

open Complex Filter Topology MeasureTheory Set intervalIntegral

namespace GaloisForLFunctions.ArtinMertens

variable {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)

/-- The twisted Chebyshev function `ψ(x, χ) = Σ_{1 ≤ n ≤ x} χ(n)Λ(n)`. -/
def twistPsi (x : ℝ) : ℂ :=
  ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, χ n * (ArithmeticFunction.vonMangoldt n : ℂ)

omit [NeZero q] in
/-- Chebyshev's bound for the twisted Chebyshev function: `‖ψ(x, χ)‖ ≤ (log 4 + 4) x`. -/
theorem norm_twistPsi_le {x : ℝ} (hx : 0 ≤ x) :
    ‖twistPsi χ x‖ ≤ (Real.log 4 + 4) * x := by
  refine (norm_sum_le _ _).trans ?_
  have h1 : ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, ‖χ n * (ArithmeticFunction.vonMangoldt n : ℂ)‖ ≤
      ∑ n ∈ Finset.Icc 0 ⌊x⌋₊, ArithmeticFunction.vonMangoldt n := by
    refine (Finset.sum_le_sum fun n _ => ?_).trans (Finset.sum_le_sum_of_subset_of_nonneg
      (Finset.Icc_subset_Icc_left (Nat.zero_le 1)) fun n _ _ =>
        ArithmeticFunction.vonMangoldt_nonneg)
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]
    exact mul_le_of_le_one_left ArithmeticFunction.vonMangoldt_nonneg (DirichletCharacter.norm_le_one χ _)
  refine h1.trans ?_
  rw [← Chebyshev.psi_eq_sum_Icc]
  exact Chebyshev.psi_le_const_mul_self hx

/-- The Newman function `f(u) = ψ(e^u, χ) e^{−u}`. -/
def twistNewmanF (u : ℝ) : ℂ := twistPsi χ (Real.exp u) * ((Real.exp (-u) : ℝ) : ℂ)

omit [NeZero q] in
theorem norm_twistNewmanF_le (u : ℝ) : ‖twistNewmanF χ u‖ ≤ Real.log 4 + 4 := by
  unfold twistNewmanF
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  have h := norm_twistPsi_le χ (Real.exp_pos u).le
  calc ‖twistPsi χ (Real.exp u)‖ * Real.exp (-u) ≤ (Real.log 4 + 4) * Real.exp u * Real.exp (-u) :=
        mul_le_mul_of_nonneg_right h (Real.exp_pos _).le
    _ = Real.log 4 + 4 := by rw [mul_assoc, ← Real.exp_add, add_neg_cancel, Real.exp_zero, mul_one]

omit [NeZero q] in
theorem measurable_twistNewmanF : Measurable (twistNewmanF χ) := by
  have h1 : Measurable fun u : ℝ => twistPsi χ (Real.exp u) := by
    have : (fun u : ℝ => twistPsi χ (Real.exp u)) = (fun m : ℕ =>
        ∑ n ∈ Finset.Icc 1 m, χ n * (ArithmeticFunction.vonMangoldt n : ℂ)) ∘
          (fun u : ℝ => ⌊Real.exp u⌋₊) := rfl
    rw [this]
    exact measurable_from_nat.comp (Nat.measurable_floor.comp Real.measurable_exp)
  exact h1.mul (Complex.measurable_ofReal.comp (Real.measurable_exp.comp measurable_neg))

/-- The image of `(0, ∞)` under `exp` is `(1, ∞)`. -/
theorem exp_image_Ioi_zero : Real.exp '' Ioi (0 : ℝ) = Ioi 1 := by
  ext t
  constructor
  · rintro ⟨u, hu, rfl⟩
    have := Real.exp_lt_exp.mpr (show (0 : ℝ) < u from hu)
    rwa [Real.exp_zero] at this
  · intro ht
    exact ⟨Real.log t, Real.log_pos ht, Real.exp_log (lt_trans one_pos ht)⟩

/-- `(e^u)^w = e^{uw}` for real `u`. -/
theorem ofReal_exp_cpow (u : ℝ) (w : ℂ) : ((Real.exp u : ℝ) : ℂ) ^ w = cexp ((u : ℂ) * w) := by
  rw [Complex.ofReal_exp, Complex.cpow_def_of_ne_zero (Complex.exp_ne_zero _),
    Complex.log_exp (by simp [Real.pi_pos]) (by simp [Real.pi_pos.le])]

omit [NeZero q] in
/-- **The Laplace transform**: for `Re z > 0`, `∫_0^∞ f(u) e^{−zu} du = L(χΛ, z + 1)/(z + 1)`. -/
theorem integral_twistLaplace_eq {z : ℂ} (hz : 0 < z.re) :
    ∫ u in Ioi (0 : ℝ), twistNewmanF χ u * cexp (-(z * u)) =
      LSeries (fun n => χ n * (ArithmeticFunction.vonMangoldt n : ℂ)) (z + 1) / (z + 1) := by
  have hs : (1 : ℝ) < (z + 1).re := by simp; linarith
  have hz1 : z + 1 ≠ 0 := fun h => by
    have := congrArg Complex.re h; simp at this; linarith
  have hO : (fun n : ℕ => ∑ k ∈ Finset.Icc 1 n, χ k * (ArithmeticFunction.vonMangoldt k : ℂ)) =O[atTop]
      fun n : ℕ => (n : ℝ) ^ (1 : ℝ) := by
    refine Asymptotics.IsBigO.of_bound (Real.log 4 + 4) (Eventually.of_forall fun n => ?_)
    have h := norm_twistPsi_le χ (Nat.cast_nonneg n : (0 : ℝ) ≤ n)
    unfold twistPsi at h
    rw [Nat.floor_natCast] at h
    rw [Real.rpow_one, Real.norm_eq_abs, abs_of_nonneg (Nat.cast_nonneg n)]
    exact h
  have h1 := LSeries_eq_mul_integral (fun n => χ n * (ArithmeticFunction.vonMangoldt n : ℂ))
    zero_le_one hs (DirichletCharacter.LSeriesSummable_twist_vonMangoldt χ hs) hO
  rw [h1, mul_div_cancel_left₀ _ hz1]
  -- the substitution `t = e^u`
  have hsub := integral_image_eq_integral_abs_deriv_smul (s := Ioi (0 : ℝ)) (f := Real.exp)
    (f' := Real.exp) measurableSet_Ioi (fun u _ => (Real.hasDerivAt_exp u).hasDerivWithinAt)
    Real.exp_injective.injOn
    (fun t : ℝ => (∑ k ∈ Finset.Icc 1 ⌊t⌋₊, χ k * (ArithmeticFunction.vonMangoldt k : ℂ)) *
      (t : ℂ) ^ (-(z + 1 + 1)))
  rw [exp_image_Ioi_zero] at hsub
  rw [hsub]
  refine setIntegral_congr_fun measurableSet_Ioi fun u _ => ?_
  simp only [twistNewmanF, twistPsi]
  rw [abs_of_pos (Real.exp_pos u), ofReal_exp_cpow, Complex.real_smul, Complex.ofReal_exp,
    Complex.ofReal_exp]
  have e : cexp (u : ℂ) * cexp ((u : ℂ) * -(z + 1 + 1)) = cexp ((-u : ℝ) : ℂ) * cexp (-(z * u)) := by
    rw [← Complex.exp_add, ← Complex.exp_add]; congr 1; push_cast; ring
  linear_combination (-(∑ n ∈ Finset.Icc 1 ⌊Real.exp u⌋₊,
    χ n * (ArithmeticFunction.vonMangoldt n : ℂ))) * e

/-- The continuation `g(z) = (−L'(z + 1, χ)/L(z + 1, χ))/(z + 1)`. -/
def twistNewmanG (z : ℂ) : ℂ :=
  (-deriv (DirichletCharacter.LFunction χ) (z + 1) / DirichletCharacter.LFunction χ (z + 1)) /
    (z + 1)

/-- For `Re s > 1`: `L(χΛ, s) = −L'(s, χ)/L(s, χ)` with the entire `L`-function. -/
theorem LSeries_twist_vonMangoldt_eq_LFunction {s : ℂ} (hs : 1 < s.re) :
    LSeries (fun n => χ n * (ArithmeticFunction.vonMangoldt n : ℂ)) s =
      -deriv (DirichletCharacter.LFunction χ) s / DirichletCharacter.LFunction χ s := by
  have h := DirichletCharacter.LSeries_twist_vonMangoldt_eq χ hs
  have hev : DirichletCharacter.LFunction χ =ᶠ[𝓝 s] LSeries (fun n => χ n) :=
    Filter.eventually_of_mem ((isOpen_lt continuous_const Complex.continuous_re).mem_nhds hs)
      fun w hw => DirichletCharacter.LFunction_eq_LSeries χ hw
  rw [hev.deriv_eq, DirichletCharacter.LFunction_eq_LSeries χ hs]
  exact h

/-- `g` is analytic at every point of the closed half-plane `Re z ≥ 0`. -/
theorem analyticAt_twistNewmanG (hχ : χ ≠ 1) {z : ℂ} (hz : 0 ≤ z.re) :
    AnalyticAt ℂ (twistNewmanG χ) z := by
  have hdiff := DirichletCharacter.differentiable_LFunction hχ
  have hA : AnalyticOnNhd ℂ (DirichletCharacter.LFunction χ) univ := fun w _ => hdiff.analyticAt w
  have hshift : AnalyticAt ℂ (fun w : ℂ => w + 1) z := analyticAt_id.add analyticAt_const
  have hL : AnalyticAt ℂ (fun w : ℂ => DirichletCharacter.LFunction χ (w + 1)) z :=
    (hA (z + 1) trivial).comp (f := fun w : ℂ => w + 1) hshift
  have hD : AnalyticAt ℂ (fun w : ℂ => deriv (DirichletCharacter.LFunction χ) (w + 1)) z :=
    ((hA.deriv) (z + 1) trivial).comp (f := fun w : ℂ => w + 1) hshift
  have hne : DirichletCharacter.LFunction χ (z + 1) ≠ 0 :=
    DirichletCharacter.LFunction_ne_zero_of_one_le_re χ (Or.inl hχ) (by simp; linarith)
  have hz1 : z + 1 ≠ 0 := fun h => by
    have := congrArg Complex.re h; simp at this; linarith
  exact (hD.neg.div hL hne).div hshift hz1

/-- **Newman's theorem for `χ`**: `∫_0^T ψ(e^u, χ) e^{−u} du → −L'(1, χ)/L(1, χ)`. -/
theorem tendsto_integral_twistNewmanF (hχ : χ ≠ 1) :
    Tendsto (fun T : ℝ => ∫ u in (0 : ℝ)..T, twistNewmanF χ u) atTop
      (𝓝 (-deriv (DirichletCharacter.LFunction χ) 1 / DirichletCharacter.LFunction χ 1)) := by
  have h := newman_analytic_theorem (f := twistNewmanF χ) (B := Real.log 4 + 4)
    (measurable_twistNewmanF χ).aestronglyMeasurable (fun u _ => norm_twistNewmanF_le χ u)
    (g := twistNewmanG χ) (fun z hz => analyticAt_twistNewmanG χ hχ hz)
    (fun z hz => by
      rw [integral_twistLaplace_eq χ hz, twistNewmanG,
        LSeries_twist_vonMangoldt_eq_LFunction χ (by simp; linarith)])
  simpa [twistNewmanG] using h

/-! ### The twisted Chebyshev function is `o(x)` -/

/-- `ψ(N, χ) = Σ_{r < q} χ(r) ψ(N; q, r)`, splitting into residue classes. -/
theorem twistPsi_natCast_eq (N : ℕ) :
    twistPsi χ N = ∑ r ∈ Finset.range q, χ r *
      ((cumsum (fun n => if n % q = r then ArithmeticFunction.vonMangoldt n else 0) (N + 1) : ℝ) :
        ℂ) := by
  have hq : 0 < q := NeZero.pos q
  symm
  calc ∑ r ∈ Finset.range q, χ r *
        ((cumsum (fun n => if n % q = r then ArithmeticFunction.vonMangoldt n else 0) (N + 1) : ℝ) :
          ℂ)
      = ∑ r ∈ Finset.range q, ∑ n ∈ Finset.range (N + 1),
          (if n % q = r then χ r * (ArithmeticFunction.vonMangoldt n : ℂ) else 0) := by
        refine Finset.sum_congr rfl fun r _ => ?_
        unfold cumsum
        rw [Complex.ofReal_sum, Finset.mul_sum]
        refine Finset.sum_congr rfl fun n _ => ?_
        split_ifs <;> simp
    _ = ∑ n ∈ Finset.range (N + 1), ∑ r ∈ Finset.range q,
          (if n % q = r then χ r * (ArithmeticFunction.vonMangoldt n : ℂ) else 0) :=
        Finset.sum_comm
    _ = ∑ n ∈ Finset.range (N + 1), χ n * (ArithmeticFunction.vonMangoldt n : ℂ) := by
        refine Finset.sum_congr rfl fun n _ => ?_
        rw [Finset.sum_ite_eq (Finset.range q) (n % q)
          (fun r => χ r * (ArithmeticFunction.vonMangoldt n : ℂ)),
          if_pos (Finset.mem_range.mpr (Nat.mod_lt n hq)), ZMod.natCast_mod]
    _ = twistPsi χ N := by
        unfold twistPsi
        rw [Nat.floor_natCast, Finset.range_eq_Ico,
          Finset.sum_eq_sum_Ico_succ_bot (Nat.succ_pos N)]
        have hI : Finset.Ico (0 + 1) N.succ = Finset.Icc 1 N := by
          ext n; simp only [Finset.mem_Ico, Finset.mem_Icc]; omega
        rw [hI]
        simp

/-- `Σ_{r < q} χ(r) = 0` for a nontrivial character. -/
theorem sum_range_char_eq_zero (hχ : χ ≠ 1) : ∑ r ∈ Finset.range q, χ r = 0 := by
  have hq : 0 < q := NeZero.pos q
  rw [← MulChar.sum_eq_zero_of_ne_one hχ]
  refine (Finset.sum_nbij (fun x : ZMod q => x.val) (fun x _ => Finset.mem_range.mpr (ZMod.val_lt x))
    (fun x _ y _ h => ZMod.val_injective q h) (fun r hr => ?_)
    (fun x _ => by rw [ZMod.natCast_zmod_val])).symm
  refine ⟨(r : ZMod q), Finset.mem_univ _, ?_⟩
  exact ZMod.val_cast_of_lt (Finset.mem_range.mp hr)

/-- **`ψ(x, χ) = o(x)`** for a nontrivial character, from the prime number theorem in
progressions. -/
theorem tendsto_twistPsi_div (hχ : χ ≠ 1) :
    Tendsto (fun x : ℝ => twistPsi χ x / x) atTop (𝓝 0) := by
  have hq : 0 < q := NeZero.pos q
  -- each residue class, along the integers
  have hclass : ∀ r ∈ Finset.range q, Tendsto (fun N : ℕ => χ r *
      (((cumsum (fun n => if n % q = r then ArithmeticFunction.vonMangoldt n else 0) (N + 1) : ℝ) :
        ℂ) / (N : ℂ))) atTop (𝓝 (χ r * (1 / (q.totient : ℂ)))) := by
    intro r hr
    by_cases hcop : r.Coprime q
    · have h := (WeakPNT_AP hq hcop (Finset.mem_range.mp hr)).comp (tendsto_add_atTop_nat 1)
      have hratio : Tendsto (fun N : ℕ => ((N : ℝ) + 1) / N) atTop (𝓝 1) := by
        have h1 := (tendsto_const_div_atTop_nhds_zero_nat (1 : ℝ)).const_add (1 : ℝ)
        rw [add_zero] at h1
        refine h1.congr' ?_
        filter_upwards [eventually_ge_atTop 1] with N hN
        have : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
        field_simp
      have h2 := (h.mul hratio).ofReal.const_mul (χ r)
      rw [mul_one] at h2
      push_cast at h2
      refine h2.congr' ?_
      filter_upwards [eventually_ge_atTop 1] with N hN
      have : (N : ℂ) ≠ 0 := by exact_mod_cast (by omega : N ≠ 0)
      have : ((N : ℂ) + 1) ≠ 0 := by exact_mod_cast (by omega : N + 1 ≠ 0)
      simp only [Function.comp_apply]
      push_cast
      field_simp
    · have h0 : χ r = 0 := MulChar.map_nonunit χ (fun hu => hcop ((ZMod.isUnit_iff_coprime r q).mp hu))
      simp only [h0, zero_mul]
      exact tendsto_const_nhds
  have hsum := tendsto_finsetSum (Finset.range q) hclass
  rw [← Finset.sum_mul, sum_range_char_eq_zero χ hχ, zero_mul] at hsum
  -- the integers
  have hnat : Tendsto (fun N : ℕ => twistPsi χ N / N) atTop (𝓝 0) := by
    refine hsum.congr fun N => ?_
    rw [twistPsi_natCast_eq, Finset.sum_div]
    exact Finset.sum_congr rfl fun r _ => by ring
  -- the reals: `ψ(x, χ) = ψ(⌊x⌋, χ)`
  have hfl := (hnat.comp (tendsto_nat_floor_atTop (α := ℝ))).mul
    ((tendsto_nat_floor_div_atTop (R := ℝ)).ofReal)
  rw [zero_mul] at hfl
  refine hfl.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with x hx
  have hf1 : 1 ≤ ⌊x⌋₊ := Nat.le_floor (by exact_mod_cast hx)
  have hfC : (⌊x⌋₊ : ℂ) ≠ 0 := by exact_mod_cast (by omega : ⌊x⌋₊ ≠ 0)
  have hxC : (x : ℂ) ≠ 0 := by exact_mod_cast (by linarith : x ≠ 0)
  have hpsi : twistPsi χ (⌊x⌋₊ : ℝ) = twistPsi χ x := by
    unfold twistPsi; rw [Nat.floor_natCast]
  simp only [Function.comp_apply]
  rw [hpsi]
  push_cast
  field_simp

/-! ### Abel summation and the limit -/

/-- The image of `(0, log x]` under `exp` is `(1, x]`. -/
theorem exp_image_Ioc_zero_log {x : ℝ} (hx : 0 < x) :
    Real.exp '' Set.Ioc 0 (Real.log x) = Set.Ioc 1 x := by
  ext t
  constructor
  · rintro ⟨u, hu, rfl⟩
    refine ⟨?_, ?_⟩
    · have := Real.exp_lt_exp.mpr hu.1; rwa [Real.exp_zero] at this
    · have := Real.exp_le_exp.mpr hu.2; rwa [Real.exp_log hx] at this
  · intro ht
    have ht0 : 0 < t := lt_trans one_pos ht.1
    refine ⟨Real.log t, ⟨Real.log_pos ht.1, Real.log_le_log ht0 ht.2⟩, Real.exp_log ht0⟩

omit [NeZero q] in
/-- **Abel summation**: `Σ_{n ≤ x} χ(n)Λ(n)/n = ψ(x, χ)/x + ∫_0^{log x} ψ(e^u, χ) e^{−u} du`. -/
theorem sum_twist_vonMangoldt_div_eq {x : ℝ} (hx : 1 ≤ x) :
    ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, χ n * (ArithmeticFunction.vonMangoldt n : ℂ) / n =
      twistPsi χ x / x + ∫ u in (0 : ℝ)..Real.log x, twistNewmanF χ u := by
  have hx0 : 0 < x := by linarith
  set c : ℕ → ℂ := fun n => χ n * (ArithmeticFunction.vonMangoldt n : ℂ) with hc
  have hc0 : c 0 = 0 := by simp [hc]
  have hder : ∀ t : ℝ, t ≠ 0 → HasDerivAt (fun t : ℝ => ((t : ℂ))⁻¹) (-((t : ℂ) ^ 2)⁻¹) t :=
    fun t ht => by
      have h1 : HasDerivAt (fun t : ℝ => (t : ℂ)) 1 t := (hasDerivAt_id t).ofReal_comp
      have := h1.inv (by exact_mod_cast ht)
      rw [neg_div, one_div] at this
      exact this
  have habel := sum_mul_eq_sub_integral_mul₀ c (f := fun t : ℝ => ((t : ℂ))⁻¹) hc0 x
    (fun t ht => (hder t (by linarith [ht.1])).differentiableAt)
    (by
      refine ContinuousOn.integrableOn_Icc ?_
      refine ContinuousOn.congr (f := fun t : ℝ => -((t : ℂ) ^ 2)⁻¹) ?_ fun t ht =>
        (hder t (by linarith [ht.1])).deriv
      refine ContinuousOn.neg (ContinuousOn.inv₀ (by fun_prop) fun t ht => ?_)
      exact pow_ne_zero 2 (by exact_mod_cast (by linarith [ht.1] : t ≠ 0)))
  -- the summatory function from `0` equals `ψ(t, χ)`
  have hS : ∀ t : ℝ, ∑ k ∈ Finset.Icc 0 ⌊t⌋₊, c k = twistPsi χ t := fun t => by
    unfold twistPsi
    rw [← Finset.sum_Ioc_add_eq_sum_Icc (Nat.zero_le _), hc0, add_zero]
    rfl
  have hlhs : ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, χ n * (ArithmeticFunction.vonMangoldt n : ℂ) / n =
      ∑ k ∈ Finset.Icc 0 ⌊x⌋₊, ((k : ℝ) : ℂ)⁻¹ * c k := by
    rw [← Finset.sum_Ioc_add_eq_sum_Icc (Nat.zero_le _)]
    simp only [hc0, mul_zero, add_zero]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp only [hc]; push_cast; ring
  rw [hlhs, habel, hS]
  -- the integral, after `t = e^u`
  have hint : -(∫ t in Set.Ioc 1 x, deriv (fun t : ℝ => ((t : ℂ))⁻¹) t *
      ∑ k ∈ Finset.Icc 0 ⌊t⌋₊, c k) = ∫ u in (0 : ℝ)..Real.log x, twistNewmanF χ u := by
    rw [intervalIntegral.integral_of_le (Real.log_nonneg hx), ← MeasureTheory.integral_neg]
    have hsub := integral_image_eq_integral_abs_deriv_smul (s := Set.Ioc 0 (Real.log x))
      (f := Real.exp) (f' := Real.exp) measurableSet_Ioc
      (fun u _ => (Real.hasDerivAt_exp u).hasDerivWithinAt) Real.exp_injective.injOn
      (fun t : ℝ => -(deriv (fun t : ℝ => ((t : ℂ))⁻¹) t * ∑ k ∈ Finset.Icc 0 ⌊t⌋₊, c k))
    rw [exp_image_Ioc_zero_log hx0] at hsub
    rw [hsub]
    refine setIntegral_congr_fun measurableSet_Ioc fun u _ => ?_
    rw [(hder (Real.exp u) (Real.exp_pos u).ne').deriv, hS, abs_of_pos (Real.exp_pos u),
      Complex.real_smul]
    unfold twistNewmanF
    rw [Real.exp_neg]
    push_cast
    have : (Complex.exp (u : ℂ)) ≠ 0 := Complex.exp_ne_zero _
    field_simp
  rw [← hint]
  push_cast
  ring

/-- **The twisted von Mangoldt series converges at `s = 1`**: for a nontrivial character `χ`,
`Σ_{n ≤ x} χ(n)Λ(n)/n → −L'(1, χ)/L(1, χ)`. -/
theorem tendsto_sum_twist_vonMangoldt_div (hχ : χ ≠ 1) :
    Tendsto (fun x : ℝ => ∑ n ∈ Finset.Icc 1 ⌊x⌋₊,
      χ n * (ArithmeticFunction.vonMangoldt n : ℂ) / n) atTop
      (𝓝 (-deriv (DirichletCharacter.LFunction χ) 1 / DirichletCharacter.LFunction χ 1)) := by
  have h := (tendsto_twistPsi_div χ hχ).add
    ((tendsto_integral_twistNewmanF χ hχ).comp Real.tendsto_log_atTop)
  rw [zero_add] at h
  refine h.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with x hx
  rw [sum_twist_vonMangoldt_div_eq χ hx]
  rfl

end GaloisForLFunctions.ArtinMertens
