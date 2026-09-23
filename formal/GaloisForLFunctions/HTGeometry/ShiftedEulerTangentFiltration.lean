import GaloisForLFunctions.HTGeometry.ParabolicFatouJetRealization
import GaloisForLFunctions.HTGeometry.VonMangoldtSelfConvolution

/-!
# The shifted Euler quotient tangent filtration

The coefficient of the shifted Euler quotient `zeta(s-w)/zeta(s+w)` at an integer `n` is

```text
c_w(n) = n^w * prod_{p | n} (1 - p^{-2w}).
```

Each local factor has a simple zero at `w = 0` with derivative `2 log p`, so `c_w(n)` carries an
exact flat factor `w^{omega(n)}`, where `omega(n)` counts distinct prime divisors, and its top jet
is `2^{omega(n)} omega(n)! prod_{p | n} log p`.  Every finite transverse tangent is therefore
supported on integers with at most that many distinct prime divisors; the first layer is exactly
twice the von Mangoldt function.

The reflected germ is logarithmically triangular: the transverse jets of
`log F(s-w) - log F(s+w)` are `((-1)^k - 1)` times the `k`-th `s`-derivative, so only odd
derivatives survive; the jets of the quotient depend only on the jets of the logarithm; and when
the logarithm is affine — the case with no higher odd derivatives — the `k`-th jet is the pure
power `(-2 dlogF)^k`.
-/

open scoped BigOperators

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-! ## Extraction of a simple zero -/

/-- An entire function vanishing at the origin factors as `z` times an entire function whose value
at the origin is the derivative. -/
theorem exists_mul_of_apply_eq_zero {f : ℂ → ℂ} (hf : Differentiable ℂ f) (h0 : f 0 = 0) :
    ∃ g : ℂ → ℂ, Differentiable ℂ g ∧ (∀ z, f z = z * g z) ∧ g 0 = deriv f 0 := by
  refine ⟨dslope f 0, ?_, fun z => ?_, dslope_same f 0⟩
  · rw [← differentiableOn_univ]
    exact (Complex.differentiableOn_dslope Filter.univ_mem).mpr hf.differentiableOn
  · have hd := sub_smul_dslope f 0 z
    simp only [sub_zero, smul_eq_mul, h0] at hd
    linear_combination -hd

/-- The top jet of a germ with an exact flat factor of order `m`. -/
theorem iteratedDeriv_pow_mul :
    ∀ {m : ℕ} {g : ℂ → ℂ}, AnalyticAt ℂ g 0 →
      iteratedDeriv m (fun z => z ^ m * g z) 0 = (Nat.factorial m : ℂ) * g 0 := by
  intro m
  induction m with
  | zero => intro g _; simp
  | succ m ih =>
      intro g hg
      have hgd : AnalyticAt ℂ (deriv g) 0 := hg.deriv
      have hderiv : deriv (fun z : ℂ => z ^ (m + 1) * g z) =ᶠ[nhds 0]
          fun z : ℂ => z ^ m * ((m + 1 : ℂ) * g z + z * deriv g z) := by
        filter_upwards [hg.eventually_analyticAt] with z hz
        have hd : HasDerivAt (fun w : ℂ => w ^ (m + 1) * g w)
            (((m + 1 : ℕ) : ℂ) * z ^ m * g z + z ^ (m + 1) * deriv g z) z :=
          (hasDerivAt_pow (m + 1) z).fun_mul hz.differentiableAt.hasDerivAt
        rw [hd.deriv]
        push_cast
        ring
      have hg2 : AnalyticAt ℂ (fun z : ℂ => (m + 1 : ℂ) * g z + z * deriv g z) 0 :=
        (analyticAt_const.fun_mul hg).fun_add (analyticAt_id.fun_mul hgd)
      rw [iteratedDeriv_succ', hderiv.iteratedDeriv_eq m, ih hg2]
      simp [Nat.factorial_succ]
      ring

/-! ## The shifted Euler quotient coefficient -/

/-- `c_ω(n) = n^ω ∏_{p ∣ n} (1 - p^{-2ω})`, written with exponentials so that it is entire. -/
def shiftedEulerCoeff (n : ℕ) (ω : ℂ) : ℂ :=
  Complex.exp (ω * (Real.log n : ℂ)) *
    ∏ p ∈ n.primeFactors, (1 - Complex.exp (-(2 * ω) * (Real.log p : ℂ)))

theorem differentiable_localFactor (L : ℂ) :
    Differentiable ℂ (fun ω : ℂ => 1 - Complex.exp (-(2 * ω) * L)) := by
  fun_prop

theorem localFactor_zero (L : ℂ) : (fun ω : ℂ => 1 - Complex.exp (-(2 * ω) * L)) 0 = 0 := by
  simp

theorem deriv_localFactor (L : ℂ) :
    deriv (fun ω : ℂ => 1 - Complex.exp (-(2 * ω) * L)) 0 = 2 * L := by
  have hd : HasDerivAt (fun ω : ℂ => 1 - Complex.exp (-(2 * ω) * L))
      (-(Complex.exp (-(2 * (0:ℂ)) * L) * (-(2 * 1) * L))) 0 := by
    have h1 : HasDerivAt (fun ω : ℂ => -(2 * ω) * L) (-(2 * 1) * L) 0 := by
      simpa using ((hasDerivAt_id (0:ℂ)).const_mul (2:ℂ)).neg.mul_const L
    simpa using (h1.cexp).const_sub 1
  rw [hd.deriv]
  simp

/-! ## Theorem A: the distinct-prime-support filtration -/

theorem analyticAt_of_differentiable_univariate {g : ℂ → ℂ} (hg : Differentiable ℂ g) (z : ℂ) :
    AnalyticAt ℂ g z :=
  (hg.differentiableOn.analyticOnNhd isOpen_univ) z (Set.mem_univ z)

/-- The exact flat factor of the shifted Euler coefficient: order `ω(n)` with leading value
`2^{ω(n)} ∏_{p ∣ n} log p`. -/
theorem exists_flatFactor_shiftedEulerCoeff (n : ℕ) :
    ∃ g : ℂ → ℂ, AnalyticAt ℂ g 0 ∧
      (∀ ω, shiftedEulerCoeff n ω = ω ^ n.primeFactors.card * g ω) ∧
      g 0 = 2 ^ n.primeFactors.card * ∏ p ∈ n.primeFactors, (Real.log p : ℂ) := by
  classical
  have hchoice : ∀ p : ℕ, ∃ φ : ℂ → ℂ, Differentiable ℂ φ ∧
      (∀ ω, 1 - Complex.exp (-(2 * ω) * (Real.log p : ℂ)) = ω * φ ω) ∧
      φ 0 = 2 * (Real.log p : ℂ) := by
    intro p
    obtain ⟨φ, hφd, hφe, hφ0⟩ := exists_mul_of_apply_eq_zero
      (differentiable_localFactor (Real.log p : ℂ)) (localFactor_zero _)
    exact ⟨φ, hφd, hφe, by rw [hφ0, deriv_localFactor]⟩
  choose φ hφd hφe hφ0 using hchoice
  refine ⟨fun ω => Complex.exp (ω * (Real.log n : ℂ)) * ∏ p ∈ n.primeFactors, φ p ω, ?_, ?_, ?_⟩
  · refine AnalyticAt.fun_mul ?_ ?_
    · exact analyticAt_of_differentiable_univariate
        (Complex.differentiable_exp.comp (differentiable_id.mul_const _)) 0
    · exact Finset.analyticAt_fun_prod _ fun p _ => analyticAt_of_differentiable_univariate (hφd p) 0
  · intro ω
    rw [shiftedEulerCoeff, Finset.prod_congr rfl (fun p _ => hφe p ω), Finset.prod_mul_distrib,
      Finset.prod_const]
    ring
  · simp only [zero_mul, Complex.exp_zero, one_mul]
    rw [Finset.prod_congr rfl (fun p _ => hφ0 p), Finset.prod_mul_distrib, Finset.prod_const]

/-- **Theorem A, vanishing half.**  The `k`-th transverse derivative of the shifted Euler
coefficient vanishes below the number of distinct prime divisors. -/
theorem iteratedDeriv_shiftedEulerCoeff_eq_zero (n : ℕ) {k : ℕ}
    (hk : k < n.primeFactors.card) : iteratedDeriv k (shiftedEulerCoeff n) 0 = 0 := by
  obtain ⟨g, hgan, hge, _⟩ := exists_flatFactor_shiftedEulerCoeff n
  exact iteratedDeriv_eq_zero_of_flat_factor hgan (Filter.Eventually.of_forall hge) hk

/-- **Theorem A, leading half.**  At the exact order `ω(n)` the transverse derivative is
`2^{ω(n)} ω(n)! ∏_{p ∣ n} log p`. -/
theorem iteratedDeriv_shiftedEulerCoeff_card (n : ℕ) :
    iteratedDeriv n.primeFactors.card (shiftedEulerCoeff n) 0
      = 2 ^ n.primeFactors.card * (Nat.factorial n.primeFactors.card : ℂ) *
        ∏ p ∈ n.primeFactors, (Real.log p : ℂ) := by
  obtain ⟨g, hgan, hge, hg0⟩ := exists_flatFactor_shiftedEulerCoeff n
  have heq : shiftedEulerCoeff n =ᶠ[nhds 0] fun z => z ^ n.primeFactors.card * g z :=
    Filter.Eventually.of_forall hge
  rw [heq.iteratedDeriv_eq, iteratedDeriv_pow_mul hgan, hg0]
  ring

/-! ## The first transverse layer is the von Mangoldt function -/

theorem shiftedEulerCoeff_of_primeFactors_empty {n : ℕ} (h : n.primeFactors = ∅) (ω : ℂ) :
    shiftedEulerCoeff n ω = 1 := by
  have hn : n = 0 ∨ n = 1 := Nat.primeFactors_eq_empty.mp h
  rw [shiftedEulerCoeff, h, Finset.prod_empty, mul_one]
  rcases hn with rfl | rfl <;> simp

/-- **The one-prime layer.**  The first transverse derivative of the shifted Euler coefficient is
twice the von Mangoldt function. -/
theorem iteratedDeriv_one_shiftedEulerCoeff (n : ℕ) :
    iteratedDeriv 1 (shiftedEulerCoeff n) 0
      = 2 * ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) := by
  classical
  rcases Nat.lt_trichotomy n.primeFactors.card 1 with hlt | heq | hgt
  · have hempty : n.primeFactors = ∅ := Finset.card_eq_zero.mp (by omega)
    have hnpp : ¬ IsPrimePow n := by
      rw [isPrimePow_iff_card_primeFactors_eq_one]
      omega
    have hc : shiftedEulerCoeff n = fun _ : ℂ => (1 : ℂ) :=
      funext (shiftedEulerCoeff_of_primeFactors_empty hempty)
    rw [hc, ArithmeticFunction.vonMangoldt_apply, if_neg hnpp]
    simp [iteratedDeriv_succ]
  · have hpp : IsPrimePow n := isPrimePow_iff_card_primeFactors_eq_one.mpr heq
    obtain ⟨p, hp⟩ := Finset.card_eq_one.mp heq
    have hmem : n.minFac ∈ n.primeFactors := by
      have h2 : 2 ≤ n := hpp.two_le
      exact Nat.mem_primeFactors.mpr ⟨Nat.minFac_prime (by omega), Nat.minFac_dvd n, by omega⟩
    have hminfac : n.minFac = p := by
      rw [hp] at hmem
      simpa using hmem
    have hkey := iteratedDeriv_shiftedEulerCoeff_card n
    rw [hp] at hkey
    simp only [Finset.card_singleton, Finset.prod_singleton, pow_one, Nat.factorial_one,
      Nat.cast_one, mul_one] at hkey
    rw [hkey, ArithmeticFunction.vonMangoldt_apply, if_pos hpp, hminfac]
  · rw [iteratedDeriv_shiftedEulerCoeff_eq_zero n hgt,
      ArithmeticFunction.vonMangoldt_apply, if_neg ?_]
    · simp
    · rw [isPrimePow_iff_card_primeFactors_eq_one]
      omega

/-! ## Theorem B: the reflected germ is logarithmically triangular -/

theorem iteratedDeriv_comp_const_add :
    ∀ (k : ℕ) {G : ℂ → ℂ}, (∀ z, AnalyticAt ℂ G z) → ∀ s ω : ℂ,
      iteratedDeriv k (fun x => G (s + x)) ω = iteratedDeriv k G (s + ω) := by
  intro k
  induction k with
  | zero => intro G _ s ω; simp
  | succ k ih =>
      intro G hG s ω
      rw [iteratedDeriv_succ', iteratedDeriv_succ']
      have hd : (deriv fun x : ℂ => G (s + x)) = fun x : ℂ => deriv G (s + x) := by
        funext x
        have hinner : HasDerivAt (fun x : ℂ => s + x) 1 x := by
          simpa using (hasDerivAt_id x).const_add s
        have hcomp := (hG (s + x)).differentiableAt.hasDerivAt.comp x hinner
        simpa [Function.comp_def] using hcomp.deriv
      rw [hd]
      exact ih (fun z => (hG z).deriv) s ω

theorem iteratedDeriv_comp_const_sub :
    ∀ (k : ℕ) {G : ℂ → ℂ}, (∀ z, AnalyticAt ℂ G z) → ∀ s ω : ℂ,
      iteratedDeriv k (fun x => G (s - x)) ω = (-1 : ℂ) ^ k * iteratedDeriv k G (s - ω) := by
  intro k
  induction k with
  | zero => intro G _ s ω; simp
  | succ k ih =>
      intro G hG s ω
      rw [iteratedDeriv_succ', iteratedDeriv_succ']
      have hd : (deriv fun x : ℂ => G (s - x)) = fun x : ℂ => -deriv G (s - x) := by
        funext x
        have hinner : HasDerivAt (fun x : ℂ => s - x) (-1) x := by
          simpa using (hasDerivAt_id x).const_sub s
        have hcomp := (hG (s - x)).differentiableAt.hasDerivAt.comp x hinner
        simpa [Function.comp_def] using hcomp.deriv
      rw [hd]
      have hneg : ∀ (m : ℕ) (F : ℂ → ℂ) (y : ℂ),
          iteratedDeriv m (fun x => -F x) y = -iteratedDeriv m F y := by
        intro m F y
        simp
      rw [hneg, ih (fun z => (hG z).deriv) s ω]
      ring

theorem iteratedDeriv_fun_sub :
    ∀ (k : ℕ) {f g : ℂ → ℂ}, (∀ z, AnalyticAt ℂ f z) → (∀ z, AnalyticAt ℂ g z) → ∀ z : ℂ,
      iteratedDeriv k (fun x => f x - g x) z = iteratedDeriv k f z - iteratedDeriv k g z := by
  intro k
  induction k with
  | zero => intro f g _ _ z; simp
  | succ k ih =>
      intro f g hf hg z
      rw [iteratedDeriv_succ', iteratedDeriv_succ', iteratedDeriv_succ']
      have hd : (deriv fun x : ℂ => f x - g x) = fun x : ℂ => deriv f x - deriv g x := by
        funext x
        exact deriv_fun_sub (hf x).differentiableAt (hg x).differentiableAt
      rw [hd]
      exact ih (fun z => (hf z).deriv) (fun z => (hg z).deriv) z

/-- **Theorem B `(5)`.**  Even transverse jets of the reflected logarithm cancel and odd ones
double: the jet of `log F(s-ω) - log F(s+ω)` at `ω = 0` is `((-1)^k - 1)` times the `k`-th
`s`-derivative. -/
theorem iteratedDeriv_reflectedLog {G : ℂ → ℂ} (hG : ∀ z, AnalyticAt ℂ G z) (s : ℂ) (k : ℕ) :
    iteratedDeriv k (fun ω => G (s - ω) - G (s + ω)) 0
      = ((-1 : ℂ) ^ k - 1) * iteratedDeriv k G s := by
  have hsub : ∀ z : ℂ, AnalyticAt ℂ (fun ω : ℂ => G (s - ω)) z := fun z =>
    (hG (s - z)).comp (analyticAt_const.sub analyticAt_id)
  have hadd : ∀ z : ℂ, AnalyticAt ℂ (fun ω : ℂ => G (s + ω)) z := fun z =>
    (hG (s + z)).comp (analyticAt_const.add analyticAt_id)
  rw [iteratedDeriv_fun_sub k hsub hadd 0, iteratedDeriv_comp_const_sub k hG s 0,
    iteratedDeriv_comp_const_add k hG s 0]
  simp
  ring

/-- **Theorem B, triangularity.**  The `k`-jet of the reflected quotient is determined by the
`k`-jet of the logarithm; with `(5)` this means only the odd `s`-derivatives enter. -/
theorem iteratedDeriv_exp_congr_of_flat {L₁ L₂ : ℂ → ℂ} (h₁ : ∀ z, AnalyticAt ℂ L₁ z)
    (h₂ : ∀ z, AnalyticAt ℂ L₂ z) {k : ℕ} {W : ℂ → ℂ} (hW : AnalyticAt ℂ W 0)
    (hflat : ∀ᶠ z in nhds 0, L₁ z - L₂ z = z ^ (k + 1) * W z) {j : ℕ} (hj : j ≤ k) :
    iteratedDeriv j (fun z => Complex.exp (L₁ z)) 0
      = iteratedDeriv j (fun z => Complex.exp (L₂ z)) 0 := by
  obtain ⟨ψ, hψd, hψe, _⟩ := exists_mul_of_apply_eq_zero
    (f := fun w : ℂ => Complex.exp w - 1) (by fun_prop) (by simp)
  have hdiff : ∀ᶠ z in nhds (0 : ℂ),
      Complex.exp (L₁ z) - Complex.exp (L₂ z)
        = z ^ (k + 1) * (Complex.exp (L₂ z) * W z * ψ (L₁ z - L₂ z)) := by
    filter_upwards [hflat] with z hz
    have hfac : Complex.exp (L₁ z) - Complex.exp (L₂ z)
        = Complex.exp (L₂ z) * (Complex.exp (L₁ z - L₂ z) - 1) := by
      rw [Complex.exp_sub]
      field_simp [Complex.exp_ne_zero]
    rw [hfac, hψe (L₁ z - L₂ z), hz]
    ring
  have hWan : AnalyticAt ℂ (fun z : ℂ => Complex.exp (L₂ z) * W z * ψ (L₁ z - L₂ z)) 0 := by
    refine AnalyticAt.fun_mul (AnalyticAt.fun_mul ?_ hW) ?_
    · exact (analyticAt_of_differentiable_univariate Complex.differentiable_exp _).comp (h₂ 0)
    · exact (analyticAt_of_differentiable_univariate hψd _).comp ((h₁ 0).sub (h₂ 0))
  have hzero := iteratedDeriv_eq_zero_of_flat_factor (m := k + 1) (n := j) hWan hdiff (by omega)
  have hexp₁ : ∀ z : ℂ, AnalyticAt ℂ (fun x : ℂ => Complex.exp (L₁ x)) z := fun z =>
    (analyticAt_of_differentiable_univariate Complex.differentiable_exp _).comp (h₁ z)
  have hexp₂ : ∀ z : ℂ, AnalyticAt ℂ (fun x : ℂ => Complex.exp (L₂ x)) z := fun z =>
    (analyticAt_of_differentiable_univariate Complex.differentiable_exp _).comp (h₂ z)
  rw [iteratedDeriv_fun_sub j hexp₁ hexp₂ 0] at hzero
  linear_combination hzero

theorem iteratedDeriv_cexp_const_mul (b : ℂ) :
    ∀ (k : ℕ) (x : ℂ), iteratedDeriv k (fun ω : ℂ => Complex.exp (b * ω)) x
      = b ^ k * Complex.exp (b * x) := by
  intro k
  induction k with
  | zero => intro x; simp
  | succ k ih =>
      intro x
      rw [iteratedDeriv_succ']
      have hd : (deriv fun ω : ℂ => Complex.exp (b * ω))
          = fun ω : ℂ => b * Complex.exp (b * ω) := by
        funext ω
        have h1 : HasDerivAt (fun ω : ℂ => b * ω) b ω := by
          simpa using (hasDerivAt_id ω).const_mul b
        simpa [mul_comm] using (h1.cexp).deriv
      rw [hd]
      have hconst : ∀ (m : ℕ) (F : ℂ → ℂ) (y : ℂ),
          iteratedDeriv m (fun ω => b * F ω) y = b * iteratedDeriv m F y := by
        intro m
        induction m with
        | zero => intro F y; simp
        | succ m ihm =>
            intro F y
            rw [iteratedDeriv_succ', iteratedDeriv_succ']
            have hcm : (deriv fun ω : ℂ => b * F ω) = fun ω : ℂ => b * deriv F ω := by
              funext ω
              exact deriv_const_mul_field b
            rw [hcm, ihm]
      rw [hconst, ih x]
      ring

/-- **Theorem B `(8)`, leading monomial.**  For an affine logarithm — the case in which every
higher odd derivative vanishes — the `k`-th transverse jet of the reflected quotient is the pure
power `(-2 ∂_s log F)^k`. -/
theorem iteratedDeriv_reflectedQuotient_affine (c₀ c₁ s : ℂ) (k : ℕ) :
    iteratedDeriv k
        (fun ω => Complex.exp ((c₀ + c₁ * (s - ω)) - (c₀ + c₁ * (s + ω)))) 0
      = (-2 * c₁) ^ k := by
  have hfun : (fun ω : ℂ => Complex.exp ((c₀ + c₁ * (s - ω)) - (c₀ + c₁ * (s + ω))))
      = fun ω : ℂ => Complex.exp ((-2 * c₁) * ω) := by
    funext ω
    congr 1
    ring
  rw [hfun, iteratedDeriv_cexp_const_mul]
  simp

/-- The prime-power second layer: for `n = p^a` the second transverse derivative is
`4 (a-1) (log p)^(2 : ℕ)`. -/
theorem iteratedDeriv_two_shiftedEulerCoeff_primePow {p a : ℕ} (hp : p.Prime) (ha : 1 ≤ a) :
    iteratedDeriv 2 (shiftedEulerCoeff (p ^ a)) 0
      = 4 * ((a : ℂ) - 1) * (Real.log p : ℂ) ^ (2 : ℕ) := by
  have hfactors : (p ^ a).primeFactors = {p} := by
    rw [Nat.primeFactors_pow _ (by omega), hp.primeFactors]
  have hlog : (Real.log ((p ^ a : ℕ) : ℝ) : ℂ) = (a : ℂ) * (Real.log p : ℂ) := by
    push_cast
    rw [Real.log_pow]
    push_cast
    ring
  have hfun : shiftedEulerCoeff (p ^ a)
      = fun ω : ℂ => Complex.exp (((a : ℂ) * (Real.log p : ℂ)) * ω)
          - Complex.exp ((((a : ℂ) - 2) * (Real.log p : ℂ)) * ω) := by
    funext ω
    rw [shiftedEulerCoeff, hfactors, Finset.prod_singleton, hlog]
    rw [mul_sub, mul_one, ← Complex.exp_add]
    congr 2
    · ring
    · ring
  rw [hfun]
  have han : ∀ (b : ℂ) (z : ℂ), AnalyticAt ℂ (fun ω : ℂ => Complex.exp (b * ω)) z := by
    intro b z
    exact (analyticAt_of_differentiable_univariate Complex.differentiable_exp _).comp
      (analyticAt_const.mul analyticAt_id)
  rw [iteratedDeriv_fun_sub 2 (han _) (han _) 0, iteratedDeriv_cexp_const_mul,
    iteratedDeriv_cexp_const_mul]
  simp
  ring

/-- **The two-prime layer.**  The second transverse derivative of the shifted Euler coefficient is
four times the Dirichlet self-convolution of the von Mangoldt function.  Together with
`iteratedDeriv_one_shiftedEulerCoeff` this identifies both low tangent layers of the shifted Euler
quotient with the classical arithmetic convolutions. -/
theorem iteratedDeriv_two_shiftedEulerCoeff (n : ℕ) :
    iteratedDeriv 2 (shiftedEulerCoeff n) 0
      = 4 * (((ArithmeticFunction.vonMangoldt * ArithmeticFunction.vonMangoldt) n : ℝ) : ℂ) := by
  classical
  rcases lt_trichotomy n.primeFactors.card 1 with hlt | heq1 | hgt
  · have hempty : n.primeFactors = ∅ := Finset.card_eq_zero.mp (by omega)
    have hc : shiftedEulerCoeff n = fun _ : ℂ => (1 : ℂ) :=
      funext (shiftedEulerCoeff_of_primeFactors_empty hempty)
    have hn : n = 0 ∨ n = 1 := Nat.primeFactors_eq_empty.mp hempty
    have hzero : (ArithmeticFunction.vonMangoldt * ArithmeticFunction.vonMangoldt) n = 0 := by
      rcases hn with rfl | rfl
      · simp
      · simp [ArithmeticFunction.mul_apply]
    rw [hc, hzero]
    simp [iteratedDeriv_succ]
  · have hpp : IsPrimePow n := isPrimePow_iff_card_primeFactors_eq_one.mpr heq1
    obtain ⟨p, k, hp, hk, rfl⟩ := (isPrimePow_nat_iff n).mp hpp
    rw [iteratedDeriv_two_shiftedEulerCoeff_primePow hp hk,
      vonMangoldt_mul_self_prime_pow hp hk]
    push_cast
    ring
  · rcases eq_or_lt_of_le (Nat.succ_le_of_lt hgt) with heq2 | hgt2
    · have hcard : n.primeFactors.card = 2 := heq2.symm
      have hkey := iteratedDeriv_shiftedEulerCoeff_card n
      rw [hcard] at hkey
      rw [hkey, vonMangoldt_mul_self_of_card_eq_two hcard]
      push_cast
      ring
    · rw [iteratedDeriv_shiftedEulerCoeff_eq_zero n (by omega),
        vonMangoldt_mul_self_eq_zero_of_three_le (by omega)]
      simp

end

end GaloisForLFunctions.HTGeometry
