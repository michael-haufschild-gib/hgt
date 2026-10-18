import GaloisForLFunctions.BiScaleUncertainty.TwoLagMomentCone

/-!
# Universal Ramanujan Multi-Lag Spectral Calculus & Bi-Scale Additive-Multiplicative Rigidity

This module establishes the **Universal Multi-Lag Spectral Theorem** for finite divisor-sieve
processes and the **Bi-Scale Joint Additive-Multiplicative Rigidity** laws on $\mathbb{N}$.

## Main Results

1. **Universal Ramanujan Spectral Weight & Dirichlet Convolution Inversion (§1):**
   - For every additive lag $h \in \mathbb{N}$ and divisor mode $e \in \mathbb{N}$, the
     **Ramanujan lag weight** `ramanujanLagWeight h e` is defined via Dirichlet convolution on
     `ArithmeticFunction ℝ`:
     $$c_e(h) := (\mathbf{1}_{\cdot \mid h} \cdot \mathrm{id} * \mu)(e)
               = \sum_{d \mid e,\, d \mid h} d \, \mu(e / d).$$
   - By associativity and commutativity of the Dirichlet ring `ArithmeticFunction ℝ` together with
     $\zeta * \mu = 1$, `ramanujanLagWeight h` satisfies the universal divisor-sum inversion law
     (`ramanujanLagWeight_divisor_sum`):
     $$\forall g > 0,\qquad \sum_{e \mid g} c_e(h) = g \, \mathbf{1}_{g \mid h},$$
     and is the **unique** arithmetic weight (`ramanujanLagWeight_unique`) with this property.
   - `ramanujanLagWeight h e` depends on the lag $h$ exclusively through $\gcd(e, h)$
     (`ramanujanLagWeight_eq_of_gcd_eq`).

2. **Exact Recovery of Classical Arithmetic Eigenvalues (§2):**
   - At $h = 0$: `ramanujanLagWeight 0 e = φ(e)` (`ramanujanLagWeight_zero_left`).
   - At $h = 1$: `ramanujanLagWeight 1 e = μ(e)` (`ramanujanLagWeight_one_left`).
   - At $h = 2$: `ramanujanLagWeight 2 e = lagTwoEigenvalue e` (`ramanujanLagWeight_two_left`).
   - Whenever $\gcd(e, h) = 1$: `ramanujanLagWeight h e = μ(e)` (`ramanujanLagWeight_of_coprime`).
   - Whenever $e \mid h$: `ramanujanLagWeight h e = φ(e)` (`ramanujanLagWeight_of_dvd`).
   - At any prime mode $p$: `ramanujanLagWeight h p = if p ∣ h then p - 1 else -1`
     (`ramanujanLagWeight_prime`).

3. **Universal Multi-Lag Spectral Diagonalization & Shift Energy Calculus (§3):**
   - **Theorem (`periodCovariance_eq_ramanujanLagWeight_diagonal`):** For **every** truncation
     $N \in \mathbb{N}$, divisor-weight sequence $c : \mathbb{N} \to \mathbb{R}$, and additive lag
     $h \in \mathbb{N}$, the complete-period centered covariance on $\{1, \dots, N!\}$ is
     simultaneously diagonalized in Selberg divisor coordinates `selbergMultiplesCoord N c e` with
     eigenvalues `ramanujanLagWeight h e`:
     $$\operatorname{periodCovariance}(N, c, h)
       = \sum_{e \in [2, N]} c_e(h) \, \bigl(\operatorname{selbergMultiplesCoord}(N, c, e)\bigr)^2.$$
   - **Shift-Difference Spectral Formula (`periodShiftDifferenceEnergy_eq_spectral`):**
     The complete-period mean-square additive difference at lag $h$ satisfies
     $$\frac{1}{N!} \sum_{k=1}^{N!} \bigl(\operatorname{sieveSeq}(N, c, k + h) -
       \operatorname{sieveSeq}(N, c, k)\bigr)^2
       = 2 \sum_{e \in [2, N]} \bigl(\varphi(e) - c_e(h)\bigr) \,
         \bigl(\operatorname{selbergMultiplesCoord}(N, c, e)\bigr)^2.$$
   - **Universal Lag-1 Spectral Gap (`totient_sub_moebius_ge_one` &
     `periodShiftDifferenceEnergy_one_ge_two_sum_sq`):**
     For every $e \ge 2$, $\varphi(e) - \mu(e) \ge 1$, so the lag-$1$ shift energy dominates twice
     the unweighted $\ell^2$ Selberg coordinate energy and vanishes if and only if all nonconstant
     Selberg coordinates $e \in [2, N]$ vanish (`periodShiftDifferenceEnergy_one_eq_zero_iff`).

4. **Bi-Scale Joint Additive-Multiplicative Rigidity (§4):**
   - **Same-Scale Periodicity-Dilation Rigidity (`periodic_and_scale_invariant_iff_const`):**
     For every integer scale $q \ge 1$, a sequence $f : \mathbb{N} \to \mathbb{R}$ is
     simultaneously additively $q$-periodic ($\forall n,\, f(n + q) = f(n)$) and multiplicatively
     $q$-dilation invariant ($\forall n,\, f(q n) = f(n)$) if and only if $f$ is constant.
   - **Finite-Window Joint Bi-Scale Energy Rigidity (`biScaleJointEnergy_eq_zero_iff_const`):**
     The joint additive-step and multiplicative-dilation quadratic form vanishes on $[1, N]$ if and
     only if $f$ is constant on $[1, N]$.
-/

noncomputable section

open ArithmeticFunction Finset RHTower RHTower.Sieve
open GaloisForLFunctions.BezoutValuationIncidence
open scoped ArithmeticFunction.Moebius ArithmeticFunction.zeta BigOperators

namespace GaloisForLFunctions.BiScaleUncertainty

set_option autoImplicit false

/-! ## §1. Universal Ramanujan Spectral Weight & Dirichlet Convolution Inversion -/

/-- The arithmetic function $d \mapsto d \, \mathbf{1}_{d \mid h}$ (vanishing at $d = 0$). -/
def divisibilityIndicatorArith (h : ℕ) : ArithmeticFunction ℝ :=
  ⟨fun d => if d = 0 then 0 else if d ∣ h then (d : ℝ) else 0, by simp⟩

@[simp]
theorem divisibilityIndicatorArith_apply {h d : ℕ} (hd : 0 < d) :
    divisibilityIndicatorArith h d = if d ∣ h then (d : ℝ) else 0 := by
  simp [divisibilityIndicatorArith, hd.ne']

/-- The **universal Ramanujan lag arithmetic function** $\mathbf{1}_{\cdot \mid h} \cdot \mathrm{id} * \mu$
in the Dirichlet convolution ring `ArithmeticFunction ℝ`. -/
def ramanujanLagArith (h : ℕ) : ArithmeticFunction ℝ :=
  divisibilityIndicatorArith h * (μ : ArithmeticFunction ℝ)

/-- The **universal Ramanujan spectral weight** at additive lag `h` and divisor mode `e`:
$$c_e(h) = \sum_{d \mid e,\, d \mid h} d \, \mu(e / d).$$ -/
def ramanujanLagWeight (h e : ℕ) : ℝ :=
  ramanujanLagArith h e

@[simp]
theorem ramanujanLagWeight_zero_right (h : ℕ) :
    ramanujanLagWeight h 0 = 0 := by
  unfold ramanujanLagWeight
  exact (ramanujanLagArith h).map_zero

/-- Explicit divisor-sum expansion of `ramanujanLagWeight h e`. -/
theorem ramanujanLagWeight_eq_sum_divisors (h e : ℕ) :
    ramanujanLagWeight h e =
      ∑ d ∈ e.divisors, (if d ∣ h then (d : ℝ) else 0) * (μ (e / d) : ℝ) := by
  unfold ramanujanLagWeight ramanujanLagArith
  rw [ArithmeticFunction.mul_apply,
    Nat.sum_divisorsAntidiagonal (f := fun x y => divisibilityIndicatorArith h x * (μ : ArithmeticFunction ℝ) y)]
  refine Finset.sum_congr rfl ?_
  intro d hd
  have hd0 : 0 < d := Nat.pos_of_mem_divisors hd
  simp [divisibilityIndicatorArith, hd0.ne']

@[simp]
theorem ramanujanLagWeight_one_right (h : ℕ) :
    ramanujanLagWeight h 1 = 1 := by
  rw [ramanujanLagWeight_eq_sum_divisors]
  simp

/-- `ramanujanLagWeight h e` depends on the lag `h` exclusively through `Nat.gcd e h`. -/
theorem ramanujanLagWeight_eq_of_gcd_eq {h₁ h₂ e : ℕ}
    (hgcd : Nat.gcd e h₁ = Nat.gcd e h₂) :
    ramanujanLagWeight h₁ e = ramanujanLagWeight h₂ e := by
  rw [ramanujanLagWeight_eq_sum_divisors, ramanujanLagWeight_eq_sum_divisors]
  refine Finset.sum_congr rfl ?_
  intro d hd
  have hde : d ∣ e := (Nat.mem_divisors.mp hd).1
  have h1 : d ∣ h₁ ↔ d ∣ Nat.gcd e h₁ :=
    ⟨fun hh => Nat.dvd_gcd hde hh, fun hg => hg.trans (Nat.gcd_dvd_right e h₁)⟩
  have h2 : d ∣ h₂ ↔ d ∣ Nat.gcd e h₂ :=
    ⟨fun hh => Nat.dvd_gcd hde hh, fun hg => hg.trans (Nat.gcd_dvd_right e h₂)⟩
  have hdvd : d ∣ h₁ ↔ d ∣ h₂ := by rw [h1, h2, hgcd]
  by_cases h : d ∣ h₁
  · rw [if_pos h, if_pos (hdvd.mp h)]
  · rw [if_neg h, if_neg (mt hdvd.mpr h)]

/-- **Universal Möbius Inversion for `ramanujanLagWeight`:**
For every lag `h : ℕ` and positive integer `g > 0`, summing `ramanujanLagWeight h e` over the
divisors of `g` recovers the exact divisibility kernel `if g ∣ h then (g : ℝ) else 0`. -/
theorem ramanujanLagWeight_divisor_sum (h : ℕ) {g : ℕ} (hg : 0 < g) :
    ∑ e ∈ g.divisors, ramanujanLagWeight h e = if g ∣ h then (g : ℝ) else 0 := by
  have hzeta : ∑ e ∈ g.divisors, ramanujanLagWeight h e =
      ((ζ : ArithmeticFunction ℝ) * ramanujanLagArith h) g := by
    rw [ArithmeticFunction.coe_zeta_mul_apply]
    rfl
  rw [hzeta]
  unfold ramanujanLagArith
  have hm : (ζ : ArithmeticFunction ℝ) * (divisibilityIndicatorArith h * (μ : ArithmeticFunction ℝ)) =
      divisibilityIndicatorArith h * ((ζ : ArithmeticFunction ℝ) * (μ : ArithmeticFunction ℝ)) := by
    ring
  rw [hm, ArithmeticFunction.coe_zeta_mul_coe_moebius, mul_one]
  exact divisibilityIndicatorArith_apply hg

/-- **Uniqueness of the Ramanujan Spectral Weight:**
Any weight `w : ℕ → ℝ` satisfying the divisor-sum compatibility relation for a lag `h`
coincides with `ramanujanLagWeight h` on all positive integers. -/
theorem ramanujanLagWeight_unique (h : ℕ) (w : ℕ → ℝ)
    (hw : ∀ g, 0 < g → ∑ e ∈ g.divisors, w e = if g ∣ h then (g : ℝ) else 0)
    {e : ℕ} (he : 0 < e) :
    w e = ramanujanLagWeight h e := by
  let W : ArithmeticFunction ℝ := ⟨fun n => if n = 0 then 0 else w n, by simp⟩
  have hW_zeta : (ζ : ArithmeticFunction ℝ) * W = divisibilityIndicatorArith h := by
    ext g
    by_cases hg : g = 0
    · subst hg
      simp
    · have hg_pos : 0 < g := Nat.pos_of_ne_zero hg
      rw [ArithmeticFunction.coe_zeta_mul_apply, divisibilityIndicatorArith_apply hg_pos,
        ← hw g hg_pos]
      refine Finset.sum_congr rfl ?_
      intro d hd
      have hd0 : d ≠ 0 := (Nat.pos_of_mem_divisors hd).ne'
      simp [W, hd0]
  have hW_eq : W = ramanujanLagArith h := by
    calc
      W = W * 1 := (mul_one W).symm
      _ = W * ((ζ : ArithmeticFunction ℝ) * (μ : ArithmeticFunction ℝ)) := by
        rw [ArithmeticFunction.coe_zeta_mul_coe_moebius]
      _ = ((ζ : ArithmeticFunction ℝ) * W) * (μ : ArithmeticFunction ℝ) := by ring
      _ = ramanujanLagArith h := by rw [hW_zeta]; rfl
  have happly := congrArg (fun (F : ArithmeticFunction ℝ) => F e) hW_eq
  simpa [W, he.ne', ramanujanLagWeight] using happly

/-! ## §2. Exact Recovery of Classical Arithmetic Eigenvalues -/

/-- At lag `h = 0`, `ramanujanLagWeight 0 e` is Euler's totient `φ(e)` for all `e : ℕ`. -/
theorem ramanujanLagWeight_zero_left (e : ℕ) :
    ramanujanLagWeight 0 e = (Nat.totient e : ℝ) := by
  by_cases he : e = 0
  · subst he
    simp
  · symm
    apply ramanujanLagWeight_unique 0 (fun n => (Nat.totient n : ℝ)) _ (Nat.pos_of_ne_zero he)
    intro g _
    simp only [dvd_zero, if_true]
    exact_mod_cast Nat.sum_totient g

/-- At lag `h = 1`, `ramanujanLagWeight 1 e` is the Möbius function `μ(e)` for all `e : ℕ`. -/
theorem ramanujanLagWeight_one_left (e : ℕ) :
    ramanujanLagWeight 1 e = (μ e : ℝ) := by
  by_cases he : e = 0
  · subst he
    simp
  · symm
    apply ramanujanLagWeight_unique 1 (fun n => (μ n : ℝ)) _ (Nat.pos_of_ne_zero he)
    intro g _
    have hmoeb : ∑ d ∈ g.divisors, (μ d : ℝ) = if g = 1 then 1 else 0 := by
      calc
        _ = ((ζ : ArithmeticFunction ℝ) * (μ : ArithmeticFunction ℝ)) g := by
          rw [ArithmeticFunction.coe_zeta_mul_apply]; rfl
        _ = _ := by rw [ArithmeticFunction.coe_zeta_mul_coe_moebius]; rfl
    rw [hmoeb]
    by_cases hg1 : g = 1
    · subst hg1; simp
    · have hndvd : ¬ g ∣ 1 := by rw [Nat.dvd_one]; exact hg1
      simp [hg1, hndvd]

/-- At lag `h = 2`, `ramanujanLagWeight 2 e` coincides with `TwoLagSieve.lagTwoEigenvalue e`
for all `e > 0`. -/
theorem ramanujanLagWeight_two_left {e : ℕ} (he : 0 < e) :
    ramanujanLagWeight 2 e = TwoLagSieve.lagTwoEigenvalue e := by
  symm
  exact ramanujanLagWeight_unique 2 TwoLagSieve.lagTwoEigenvalue
    (fun _ hg => TwoLagSieve.lagTwoEigenvalue_divisor_sum hg) he

/-- Whenever `e` and `h` are coprime (`Nat.Coprime e h`), `ramanujanLagWeight h e = μ(e)`. -/
theorem ramanujanLagWeight_of_coprime {h e : ℕ} (hcop : Nat.Coprime e h) :
    ramanujanLagWeight h e = (μ e : ℝ) := by
  rw [← ramanujanLagWeight_one_left e]
  apply ramanujanLagWeight_eq_of_gcd_eq
  rw [hcop.gcd_eq_one, Nat.gcd_one_right]

/-- Whenever `e ∣ h`, `ramanujanLagWeight h e = φ(e)`. -/
theorem ramanujanLagWeight_of_dvd {h e : ℕ} (hdvd : e ∣ h) :
    ramanujanLagWeight h e = (Nat.totient e : ℝ) := by
  rw [← ramanujanLagWeight_zero_left e]
  apply ramanujanLagWeight_eq_of_gcd_eq
  rw [Nat.gcd_eq_left hdvd, Nat.gcd_zero_right]

/-- For a prime mode `p`, `ramanujanLagWeight h p = p - 1` when `p ∣ h` and `-1` when `¬ p ∣ h`. -/
theorem ramanujanLagWeight_prime {h p : ℕ} (hp : Nat.Prime p) :
    ramanujanLagWeight h p = if p ∣ h then (p : ℝ) - 1 else -1 := by
  by_cases hdvd : p ∣ h
  · rw [if_pos hdvd, ramanujanLagWeight_of_dvd hdvd, Nat.totient_prime hp,
      Nat.cast_sub hp.one_lt.le, Nat.cast_one]
  · have hcop : Nat.Coprime p h := hp.coprime_iff_not_dvd.mpr hdvd
    rw [if_neg hdvd, ramanujanLagWeight_of_coprime hcop,
      ArithmeticFunction.moebius_apply_prime hp]
    norm_num

/-! ## §3. Universal Multi-Lag Spectral Diagonalization & Shift Energy Calculus -/

private theorem sum_row_products_period (S T : Finset ℕ) (c : ℕ → ℝ) (h₁ h₂ : ℕ) :
    (∑ k ∈ T, (∑ a ∈ S, if a ∣ k + h₁ then c a else 0) *
      (∑ b ∈ S, if b ∣ k + h₂ then c b else 0)) =
      ∑ a ∈ S, ∑ b ∈ S, (c a * c b) *
        ((T.filter (fun k => a ∣ k + h₁ ∧ b ∣ k + h₂)).card : ℝ) := by
  simp_rw [Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b _
  have hpoint (k : ℕ) : (if a ∣ k + h₁ then c a else 0) * (if b ∣ k + h₂ then c b else 0) =
      if a ∣ k + h₁ ∧ b ∣ k + h₂ then c a * c b else 0 := by
    by_cases hka : a ∣ k + h₁ <;> by_cases hkb : b ∣ k + h₂ <;> simp [hka, hkb]
  simp_rw [hpoint]
  rw [← Finset.sum_filter]
  simp [mul_comm]

private theorem center_sum_period (T : Finset ℕ) (u v : ℕ → ℝ) (H : ℝ) :
    (∑ k ∈ T, (u k - H) * (v k - H)) =
      (∑ k ∈ T, u k * v k) - H * (∑ k ∈ T, u k) - H * (∑ k ∈ T, v k) + T.card * H ^ 2 := by
  have hpoint (k : ℕ) : (u k - H) * (v k - H) = u k * v k - H * u k - H * v k + H ^ 2 := by ring
  simp_rw [hpoint, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]
  simp

private def lagKernelFormUniversal (N : ℕ) (c : ℕ → ℝ) (h : ℕ) : ℝ :=
  ∑ p ∈ (Finset.Icc 1 N) ×ˢ (Finset.Icc 1 N),
    (if Nat.gcd p.1 p.2 ∣ h then (Nat.gcd p.1 p.2 : ℝ) else 0) *
      (c p.1 / (p.1 : ℝ)) * (c p.2 / (p.2 : ℝ))

private theorem sum_row_products_zero_left (S T : Finset ℕ) (c : ℕ → ℝ) (h : ℕ) :
    (∑ k ∈ T, (∑ a ∈ S, if a ∣ k then c a else 0) *
      (∑ b ∈ S, if b ∣ k + h then c b else 0)) =
      ∑ a ∈ S, ∑ b ∈ S, (c a * c b) *
        ((T.filter (fun k => a ∣ k ∧ b ∣ k + h)).card : ℝ) := by
  have h0 := sum_row_products_period S T c 0 h
  simpa only [Nat.add_zero] using h0

private theorem product_average_eq_lagKernelFormUniversal (N h : ℕ) (c : ℕ → ℝ) :
    (∑ k ∈ Finset.Ioc 0 (Nat.factorial N), sieveSeq N c k * sieveSeq N c (k + h)) /
      (Nat.factorial N : ℝ) = lagKernelFormUniversal N c h := by
  simp_rw [sieveSeq, Finset.sum_filter]
  rw [sum_row_products_zero_left]
  unfold lagKernelFormUniversal
  rw [Finset.sum_product, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro a ha
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro b hb
  obtain ⟨ha, haN⟩ := Finset.mem_Icc.mp ha
  obtain ⟨hb, hbN⟩ := Finset.mem_Icc.mp hb
  have ha0 : (a : ℝ) ≠ 0 := by exact_mod_cast (show a ≠ 0 by omega)
  have hb0 : (b : ℝ) ≠ 0 := by exact_mod_cast (show b ≠ 0 by omega)
  have hL := Nat.lcm_dvd (Nat.dvd_factorial (show 0 < a by omega) haN)
    (Nat.dvd_factorial (show 0 < b by omega) hbN)
  rw [mul_div_assoc,
    TwoLagSieve.joint_density_complete_period (by omega) (by omega) hL (Nat.factorial_pos N)]
  by_cases hg : Nat.gcd a b ∣ h
  · simp only [if_pos hg]
    field_simp
  · simp [hg]

private theorem shifted_sq_average_eq_lagKernelFormUniversal_zero (N h : ℕ) (c : ℕ → ℝ) :
    (∑ k ∈ Finset.Ioc 0 (Nat.factorial N),
      sieveSeq N c (k + h) * sieveSeq N c (k + h)) / (Nat.factorial N : ℝ) =
      lagKernelFormUniversal N c 0 := by
  have hkh : ∀ k, sieveSeq N c (k + h) = ∑ a ∈ Finset.Icc 1 N, if a ∣ k + h then c a else 0 := by
    intro k
    simp [sieveSeq, Finset.sum_filter]
  simp_rw [hkh]
  rw [sum_row_products_period]
  unfold lagKernelFormUniversal
  rw [Finset.sum_product, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro a ha
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro b hb
  obtain ⟨ha, haN⟩ := Finset.mem_Icc.mp ha
  obtain ⟨hb, hbN⟩ := Finset.mem_Icc.mp hb
  have ha0 : (a : ℝ) ≠ 0 := by exact_mod_cast (show a ≠ 0 by omega)
  have hb0 : (b : ℝ) ≠ 0 := by exact_mod_cast (show b ≠ 0 by omega)
  have hL := Nat.lcm_dvd (Nat.dvd_factorial (show 0 < a by omega) haN)
    (Nat.dvd_factorial (show 0 < b by omega) hbN)
  have hL0 : (Nat.lcm a b : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.lcm_pos (show 0 < a by omega) (show 0 < b by omega)).ne'
  have hP0 : (Nat.factorial N : ℝ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos N).ne'
  have hprod : (Nat.gcd a b : ℝ) * (Nat.lcm a b : ℝ) = (a : ℝ) * b := by
    exact_mod_cast Nat.gcd_mul_lcm a b
  have hfilter :
      (Finset.Ioc 0 (Nat.factorial N)).filter (fun k => a ∣ k + h ∧ b ∣ k + h) =
        (Finset.Ioc 0 (Nat.factorial N)).filter (fun k => Nat.lcm a b ∣ k + h) := by
    ext k
    simp [Nat.lcm_dvd_iff]
  rw [hfilter, TwoLagSieve.card_shift_complete_period h hL, Nat.cast_div hL hL0]
  simp only [dvd_zero, if_true]
  field_simp [hL0, hP0, ha0, hb0]
  linear_combination c a * c b * hprod.symm

private theorem periodCovariance_eq_kernel_sub_mean_universal (N h : ℕ) (c : ℕ → ℝ) :
    TwoLagSieve.periodCovariance N c h =
      lagKernelFormUniversal N c h - (finiteHarmonicSum N c) ^ 2 := by
  have hP0 : (Nat.factorial N : ℝ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos N).ne'
  have hsum0 : (∑ k ∈ Finset.Ioc 0 (Nat.factorial N), sieveSeq N c k) =
      (Nat.factorial N : ℝ) * finiteHarmonicSum N c := by
    simpa using TwoLagSieve.sum_sieveSeq_complete_period N 0 c
  unfold TwoLagSieve.periodCovariance
  rw [center_sum_period, hsum0, TwoLagSieve.sum_sieveSeq_complete_period]
  simp only [Nat.card_Ioc, Nat.sub_zero]
  calc
    _ = (∑ k ∈ Finset.Ioc 0 (Nat.factorial N), sieveSeq N c k * sieveSeq N c (k + h)) /
        (Nat.factorial N : ℝ) - (finiteHarmonicSum N c) ^ 2 := by
      field_simp
      ring
    _ = _ := by rw [product_average_eq_lagKernelFormUniversal]

private theorem lagKernelFormUniversal_eq_diagonal (N h : ℕ) (c w : ℕ → ℝ)
    (hw : ∀ g : ℕ, 0 < g → ∑ e ∈ g.divisors, w e = if g ∣ h then (g : ℝ) else 0) :
    lagKernelFormUniversal N c h =
      ∑ e ∈ Finset.Icc 1 N, w e * (selbergMultiplesCoord N c e) ^ 2 := by
  classical
  unfold lagKernelFormUniversal selbergMultiplesCoord
  have hS : ∀ m ∈ Finset.Icc 1 N, 1 ≤ m := fun m hm => (Finset.mem_Icc.mp hm).1
  have hexp : ∀ p ∈ (Finset.Icc 1 N) ×ˢ (Finset.Icc 1 N),
      (if Nat.gcd p.1 p.2 ∣ h then (Nat.gcd p.1 p.2 : ℝ) else 0) *
        (c p.1 / (p.1 : ℝ)) * (c p.2 / (p.2 : ℝ)) =
        ∑ e ∈ (Nat.gcd p.1 p.2).divisors,
          w e * ((c p.1 / (p.1 : ℝ)) * (c p.2 / (p.2 : ℝ))) := by
    intro p hp
    obtain ⟨hp1, _⟩ := Finset.mem_product.mp hp
    rw [← hw _ (Nat.gcd_pos_of_pos_left _ (hS _ hp1)), Finset.sum_mul, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro e _
    ring
  rw [Finset.sum_congr rfl hexp]
  have hmem : ∀ (p : ℕ × ℕ) (e : ℕ),
      p ∈ (Finset.Icc 1 N) ×ˢ (Finset.Icc 1 N) ∧ e ∈ (Nat.gcd p.1 p.2).divisors ↔
        p ∈ ((Finset.Icc 1 N) ×ˢ (Finset.Icc 1 N)).filter (fun q => e ∣ q.1 ∧ e ∣ q.2) ∧
          e ∈ (Finset.Icc 1 N).biUnion Nat.divisors := by
    intro p e
    constructor
    · rintro ⟨hp, he⟩
      obtain ⟨hp1, _⟩ := Finset.mem_product.mp hp
      have hgcd : e ∣ Nat.gcd p.1 p.2 := Nat.dvd_of_mem_divisors he
      have hd1 : e ∣ p.1 := dvd_trans hgcd (Nat.gcd_dvd_left _ _)
      have hd2 : e ∣ p.2 := dvd_trans hgcd (Nat.gcd_dvd_right _ _)
      refine ⟨Finset.mem_filter.mpr ⟨hp, hd1, hd2⟩, Finset.mem_biUnion.mpr ⟨p.1, hp1, ?_⟩⟩
      have hp1_pos := hS _ hp1
      exact Nat.mem_divisors.mpr ⟨hd1, by omega⟩
    · rintro ⟨hpf, -⟩
      obtain ⟨hp, hd1, hd2⟩ := Finset.mem_filter.mp hpf
      obtain ⟨hp1, _⟩ := Finset.mem_product.mp hp
      refine ⟨hp, Nat.mem_divisors.mpr ⟨Nat.dvd_gcd hd1 hd2, ?_⟩⟩
      exact (Nat.gcd_pos_of_pos_left _ (hS _ hp1)).ne'
  rw [Finset.sum_comm' hmem, biUnion_divisors_Icc_eq_Icc]
  refine Finset.sum_congr rfl fun e _ => ?_
  have hfilter : ((Finset.Icc 1 N) ×ˢ (Finset.Icc 1 N)).filter (fun q => e ∣ q.1 ∧ e ∣ q.2) =
      ((Finset.Icc 1 N).filter (fun m => e ∣ m)) ×ˢ ((Finset.Icc 1 N).filter (fun m => e ∣ m)) := by
    ext q
    simp only [Finset.mem_filter, Finset.mem_product]
    tauto
  rw [hfilter, ← Finset.mul_sum, sq, Finset.sum_mul_sum, Finset.sum_product]

/-- **Universal Multi-Lag Spectral Diagonalization Theorem:**
For **every** truncation `N : ℕ`, weight sequence `c : ℕ → ℝ`, and additive lag `h : ℕ`,
the complete-period centered covariance on `1 … N!` is diagonalized by `selbergMultiplesCoord N c`
with eigenvalues `ramanujanLagWeight h e`. -/
theorem periodCovariance_eq_ramanujanLagWeight_diagonal (N : ℕ) (c : ℕ → ℝ) (h : ℕ) :
    TwoLagSieve.periodCovariance N c h =
      ∑ e ∈ Finset.Icc 2 N,
        ramanujanLagWeight h e * (selbergMultiplesCoord N c e) ^ 2 := by
  rw [periodCovariance_eq_kernel_sub_mean_universal,
    lagKernelFormUniversal_eq_diagonal N h c (ramanujanLagWeight h)
      (fun _ hg => ramanujanLagWeight_divisor_sum h hg)]
  rcases N with _ | N
  · simp [finiteHarmonicSum]
  · have hI : Finset.Icc 1 (N + 1) = insert 1 (Finset.Icc 2 (N + 1)) := by
      ext e
      simp only [Finset.mem_insert, Finset.mem_Icc]
      omega
    rw [hI, Finset.sum_insert (by simp), ramanujanLagWeight_one_right, one_mul,
      selbergMultiplesCoord_one_eq_finiteHarmonicSum]
    ring

/-- The complete-period mean-square additive translation difference at lag `h`:
$$\mathcal{E}_{\mathrm{add}}(N, c, h)
  := \frac{1}{N!} \sum_{k=1}^{N!}
     \bigl(\operatorname{sieveSeq}(N, c, k + h) - \operatorname{sieveSeq}(N, c, k)\bigr)^2.$$ -/
def periodShiftDifferenceEnergy (N : ℕ) (c : ℕ → ℝ) (h : ℕ) : ℝ :=
  (∑ k ∈ Finset.Ioc 0 (Nat.factorial N),
    (sieveSeq N c (k + h) - sieveSeq N c k) ^ 2) /
    (Nat.factorial N : ℝ)

/-- Exact covariance identity for the lag-`h` shift difference energy:
$$\mathcal{E}_{\mathrm{add}}(N, c, h)
  = 2\bigl(\operatorname{periodCovariance}(N, c, 0) - \operatorname{periodCovariance}(N, c, h)\bigr).$$ -/
theorem periodShiftDifferenceEnergy_eq_two_sub_periodCovariance (N : ℕ) (c : ℕ → ℝ) (h : ℕ) :
    periodShiftDifferenceEnergy N c h =
      2 * (TwoLagSieve.periodCovariance N c 0 - TwoLagSieve.periodCovariance N c h) := by
  rw [periodCovariance_eq_kernel_sub_mean_universal N 0 c,
    periodCovariance_eq_kernel_sub_mean_universal N h c]
  unfold periodShiftDifferenceEnergy
  have hpoint (k : ℕ) :
      (sieveSeq N c (k + h) - sieveSeq N c k) ^ 2 =
        sieveSeq N c (k + h) * sieveSeq N c (k + h) +
        sieveSeq N c k * sieveSeq N c (k + 0) -
        2 * (sieveSeq N c k * sieveSeq N c (k + h)) := by
    simp only [Nat.add_zero]
    ring
  simp_rw [hpoint, Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum]
  have hdiv :
      (∑ x ∈ Finset.Ioc 0 (Nat.factorial N), sieveSeq N c (x + h) * sieveSeq N c (x + h) +
        ∑ x ∈ Finset.Ioc 0 (Nat.factorial N), sieveSeq N c x * sieveSeq N c (x + 0) -
        2 * ∑ x ∈ Finset.Ioc 0 (Nat.factorial N), sieveSeq N c x * sieveSeq N c (x + h)) /
        (Nat.factorial N : ℝ) =
      (∑ x ∈ Finset.Ioc 0 (Nat.factorial N), sieveSeq N c (x + h) * sieveSeq N c (x + h)) /
        (Nat.factorial N : ℝ) +
      (∑ x ∈ Finset.Ioc 0 (Nat.factorial N), sieveSeq N c x * sieveSeq N c (x + 0)) /
        (Nat.factorial N : ℝ) -
      2 * ((∑ x ∈ Finset.Ioc 0 (Nat.factorial N), sieveSeq N c x * sieveSeq N c (x + h)) /
        (Nat.factorial N : ℝ)) := by
    ring
  rw [hdiv, shifted_sq_average_eq_lagKernelFormUniversal_zero N h c,
    product_average_eq_lagKernelFormUniversal N 0 c,
    product_average_eq_lagKernelFormUniversal N h c]
  ring

/-- **Universal Multi-Lag Translation-Difference Spectral Identity:**
For every truncation `N : ℕ`, weight sequence `c : ℕ → ℝ`, and lag `h : ℕ`,
$$\mathcal{E}_{\mathrm{add}}(N, c, h)
  = 2 \sum_{e \in [2, N]} \bigl(\varphi(e) - \operatorname{ramanujanLagWeight}(h, e)\bigr) \,
    \bigl(\operatorname{selbergMultiplesCoord}(N, c, e)\bigr)^2.$$ -/
theorem periodShiftDifferenceEnergy_eq_spectral (N : ℕ) (c : ℕ → ℝ) (h : ℕ) :
    periodShiftDifferenceEnergy N c h =
      2 * ∑ e ∈ Finset.Icc 2 N,
        ((Nat.totient e : ℝ) - ramanujanLagWeight h e) *
          (selbergMultiplesCoord N c e) ^ 2 := by
  rw [periodShiftDifferenceEnergy_eq_two_sub_periodCovariance,
    periodCovariance_eq_ramanujanLagWeight_diagonal N c 0,
    periodCovariance_eq_ramanujanLagWeight_diagonal N c h,
    ← Finset.sum_sub_distrib]
  congr 1
  refine Finset.sum_congr rfl ?_
  intro e _
  rw [ramanujanLagWeight_zero_left]
  ring

/-- For every integer `e ≥ 2`, `φ(e) - μ(e) ≥ 1`. -/
theorem totient_sub_moebius_ge_one {e : ℕ} (he : 2 ≤ e) :
    (1 : ℝ) ≤ (Nat.totient e : ℝ) - (μ e : ℝ) := by
  by_cases he2 : e = 2
  · subst he2
    rw [Nat.totient_prime Nat.prime_two, ArithmeticFunction.moebius_apply_prime Nat.prime_two]
    norm_num
  · have he3 : 2 < e := by omega
    obtain ⟨k, hk⟩ := Nat.totient_even he3
    have hpos : 0 < Nat.totient e := Nat.totient_pos.mpr (by omega)
    have hphi2 : 2 ≤ Nat.totient e := by omega
    have hphi2r : (2 : ℝ) ≤ (Nat.totient e : ℝ) := by exact_mod_cast hphi2
    rcases ArithmeticFunction.moebius_eq_or e with hm | hm | hm <;>
      · simp only [hm]; push_cast; linarith

/-- **Universal Lag-1 Spectral Gap Inequality:**
The lag-`1` translation-difference energy on `1 … N!` is bounded below by twice the unweighted
sum of squares of all nonconstant Selberg coordinates `e ∈ [2, N]`. -/
theorem periodShiftDifferenceEnergy_one_ge_two_sum_sq (N : ℕ) (c : ℕ → ℝ) :
    2 * (∑ e ∈ Finset.Icc 2 N, (selbergMultiplesCoord N c e) ^ 2) ≤
      periodShiftDifferenceEnergy N c 1 := by
  rw [periodShiftDifferenceEnergy_eq_spectral]
  refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum ?_) (by norm_num)
  intro e he
  have he2 : 2 ≤ e := (Finset.mem_Icc.mp he).1
  rw [ramanujanLagWeight_one_left]
  have hgap := totient_sub_moebius_ge_one he2
  nlinarith [sq_nonneg (selbergMultiplesCoord N c e)]

/-- **Exact Lag-1 Spectral Rigidity (`↔`):**
The lag-`1` translation-difference energy vanishes if and only if every nonconstant Selberg
divisor coordinate `e ∈ [2, N]` vanishes. -/
theorem periodShiftDifferenceEnergy_one_eq_zero_iff (N : ℕ) (c : ℕ → ℝ) :
    periodShiftDifferenceEnergy N c 1 = 0 ↔
      ∀ e ∈ Finset.Icc 2 N, selbergMultiplesCoord N c e = 0 := by
  constructor
  · intro h0 e he
    have hnonneg :
        0 ≤ ∑ d ∈ Finset.Icc 2 N, (selbergMultiplesCoord N c d) ^ 2 :=
      Finset.sum_nonneg (fun d _ => sq_nonneg _)
    have hle := periodShiftDifferenceEnergy_one_ge_two_sum_sq N c
    have hsum0 : ∑ d ∈ Finset.Icc 2 N, (selbergMultiplesCoord N c d) ^ 2 = 0 := by
      linarith
    have hterm0 : (selbergMultiplesCoord N c e) ^ 2 = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg (fun d _ => sq_nonneg _)).mp hsum0 e he
    exact sq_eq_zero_iff.mp hterm0
  · intro hall
    rw [periodShiftDifferenceEnergy_eq_spectral]
    suffices hsum :
        ∑ e ∈ Finset.Icc 2 N,
          ((Nat.totient e : ℝ) - ramanujanLagWeight 1 e) *
            (selbergMultiplesCoord N c e) ^ 2 = 0 by
      rw [hsum, mul_zero]
    refine Finset.sum_eq_zero ?_
    intro e he
    rw [hall e he, sq, mul_zero, mul_zero]

/-! ## §4. Bi-Scale Joint Additive-Multiplicative Rigidity -/

/-- If `f : ℕ → ℝ` is additively `q`-periodic, every multiple `q * n` takes the value `f 0`. -/
theorem periodic_apply_mul_eq_zero {f : ℕ → ℝ} {q : ℕ}
    (hper : ∀ n, f (n + q) = f n) (n : ℕ) :
    f (q * n) = f 0 := by
  induction n with
  | zero => simp
  | succ k ih =>
    have hstep : q * (k + 1) = q * k + q := by ring
    rw [hstep, hper, ih]

/-- **Same-Scale Additive-Multiplicative Rigidity Theorem (`↔`):**
For any integer scale `q : ℕ`, a sequence `f : ℕ → ℝ` is simultaneously additively `q`-periodic
(`∀ n, f (n + q) = f n`) and multiplicatively `q`-dilation invariant (`∀ n, f (q * n) = f n`)
if and only if `f` is constant (`∀ n, f n = f 0`). -/
theorem periodic_and_scale_invariant_iff_const (f : ℕ → ℝ) (q : ℕ) :
    ((∀ n, f (n + q) = f n) ∧ (∀ n, f (q * n) = f n)) ↔ ∀ n, f n = f 0 := by
  constructor
  · rintro ⟨hper, hscale⟩ n
    calc
      f n = f (q * n) := (hscale n).symm
      _ = f 0 := periodic_apply_mul_eq_zero hper n
  · intro hconst
    refine ⟨fun n => by rw [hconst (n + q), hconst n], fun n => by rw [hconst (q * n), hconst n]⟩

/-- The finite-window additive step energy on `[1, N]`:
$$\mathcal{E}_{\mathrm{step}}(N, f) := \sum_{n \in [1, N)} (f(n + 1) - f(n))^2.$$ -/
def additiveStepEnergy (N : ℕ) (f : ℕ → ℝ) : ℝ :=
  ∑ n ∈ Finset.Ico 1 N, (f (n + 1) - f n) ^ 2

/-- The finite-window multiplicative dilation energy across scales `k ∈ [2, K]` on `[1, N]`:
$$\mathcal{E}_{\mathrm{dil}}(K, N, f) := \sum_{k \in [2, K]} \sum_{n \in [1, N/k]} (f(k n) - f(n))^2.$$ -/
def multiplicativeScaleEnergy (K N : ℕ) (f : ℕ → ℝ) : ℝ :=
  ∑ k ∈ Finset.Icc 2 K, ∑ n ∈ Finset.Icc 1 (N / k), (f (k * n) - f n) ^ 2

/-- The joint bi-scale energy on `[1, N]` with dilation horizon `K`:
$$\mathcal{E}_{\mathrm{bi}}(K, N, f)
  := \mathcal{E}_{\mathrm{step}}(N, f) + \mathcal{E}_{\mathrm{dil}}(K, N, f).$$ -/
def biScaleJointEnergy (K N : ℕ) (f : ℕ → ℝ) : ℝ :=
  additiveStepEnergy N f + multiplicativeScaleEnergy K N f

theorem additiveStepEnergy_nonneg (N : ℕ) (f : ℕ → ℝ) :
    0 ≤ additiveStepEnergy N f :=
  Finset.sum_nonneg (fun _ _ => sq_nonneg _)

theorem multiplicativeScaleEnergy_nonneg (K N : ℕ) (f : ℕ → ℝ) :
    0 ≤ multiplicativeScaleEnergy K N f :=
  Finset.sum_nonneg (fun _ _ => Finset.sum_nonneg (fun _ _ => sq_nonneg _))

theorem biScaleJointEnergy_nonneg (K N : ℕ) (f : ℕ → ℝ) :
    0 ≤ biScaleJointEnergy K N f :=
  add_nonneg (additiveStepEnergy_nonneg N f) (multiplicativeScaleEnergy_nonneg K N f)

/-- **Finite-Window Bi-Scale Joint Energy Rigidity (`↔`):**
For every dilation horizon `K : ℕ` and window `N : ℕ`, the joint bi-scale energy
`biScaleJointEnergy K N f` vanishes if and only if `f` is constant on `[1, N]`. -/
theorem biScaleJointEnergy_eq_zero_iff_const (K N : ℕ) (f : ℕ → ℝ) :
    biScaleJointEnergy K N f = 0 ↔ ∀ n ∈ Finset.Icc 1 N, f n = f 1 := by
  constructor
  · intro hzero
    have hstep_nonneg := additiveStepEnergy_nonneg N f
    have hdil_nonneg := multiplicativeScaleEnergy_nonneg K N f
    have hstep0 : additiveStepEnergy N f = 0 := by
      unfold biScaleJointEnergy at hzero
      linarith
    have hstep_term : ∀ m ∈ Finset.Ico 1 N, f (m + 1) = f m := by
      intro m hm
      have hsq0 : (f (m + 1) - f m) ^ 2 = 0 :=
        (Finset.sum_eq_zero_iff_of_nonneg (fun _ _ => sq_nonneg _)).mp hstep0 m hm
      exact sub_eq_zero.mp (sq_eq_zero_iff.mp hsq0)
    have hconst_le : ∀ m, 1 ≤ m → m ≤ N → f m = f 1 := by
      intro m
      induction m with
      | zero => intro hm1 _; omega
      | succ k ih =>
        intro hk1 hkN
        by_cases hk0 : k = 0
        · subst hk0; rfl
        · rw [hstep_term k (Finset.mem_Ico.mpr ⟨by omega, by omega⟩)]
          exact ih (by omega) (by omega)
    intro n hn
    obtain ⟨hn1, hnN⟩ := Finset.mem_Icc.mp hn
    exact hconst_le n hn1 hnN
  · intro hconst
    have hstep0 : additiveStepEnergy N f = 0 := by
      refine Finset.sum_eq_zero ?_
      intro n hn
      obtain ⟨hn1, hnN⟩ := Finset.mem_Ico.mp hn
      rw [hconst (n + 1) (Finset.mem_Icc.mpr ⟨by omega, by omega⟩),
        hconst n (Finset.mem_Icc.mpr ⟨hn1, by omega⟩), sub_self, sq, mul_zero]
    have hdil0 : multiplicativeScaleEnergy K N f = 0 := by
      refine Finset.sum_eq_zero ?_
      intro k hk
      refine Finset.sum_eq_zero ?_
      intro n hn
      obtain ⟨hk2, _⟩ := Finset.mem_Icc.mp hk
      obtain ⟨hn1, hnNk⟩ := Finset.mem_Icc.mp hn
      have hknN : k * n ≤ N := by
        rw [Nat.mul_comm]
        exact (Nat.le_div_iff_mul_le (by omega : 0 < k)).mp hnNk
      have hkn1 : 1 ≤ k * n := by nlinarith
      have hnN : n ≤ N := le_trans (Nat.le_mul_of_pos_left n (by omega : 0 < k)) hknN
      rw [hconst (k * n) (Finset.mem_Icc.mpr ⟨hkn1, hknN⟩),
        hconst n (Finset.mem_Icc.mpr ⟨hn1, hnN⟩), sub_self, sq, mul_zero]
    unfold biScaleJointEnergy
    rw [hstep0, hdil0, add_zero]

end GaloisForLFunctions.BiScaleUncertainty
