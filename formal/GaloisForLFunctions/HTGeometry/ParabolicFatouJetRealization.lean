import Mathlib

/-!
# Zero-residue parabolic finite jets are realized by algebraic germs

Fix `N >= 4` and a normalized zero-residue parabolic jet

```text
h(z) = z + z^(2 : ℕ) + z^(3 : ℕ) + a_4 z^(4 : ℕ) + ... + a_N z^N.
```

There is a polynomial `P` of degree at most `N - 3` with `P(0) = 0` such that the rational Fatou
coordinate `Phi_P(z) = -1/z + P(z)` has an analytic branch `f` of `Phi_P^{-1}(Phi_P + 1)` at the
origin whose Taylor expansion agrees with `h` through order `N`.  The branch is algebraic: it
satisfies the polynomial relation obtained by clearing denominators in the Abel equation.

The mechanism is triangular.  Cleared of denominators by `X h`, the Abel residual is
`(h - X - X h) + X h (P o h - P)`; the base term already vanishes to order four, and adding
`c X^k` to `P` changes the residual by `c X h (h^k - X^k)`, which vanishes to order `k + 3` with
leading coefficient `k`.  Solving one coefficient at a time therefore kills the residual through
order `N`, and the branch is then produced from the analytic local inverse of `1/Phi_P`.

Consequence: finite parabolic jet data cannot certify hypertranscendence of a Fatou coordinate in
the zero-residue class.
-/

open Polynomial

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {h u : Polynomial ℂ}

theorem coeff_zero_pow_of_coeff_zero_eq_one (hu0 : u.coeff 0 = 1) (j : ℕ) :
    (u ^ j).coeff 0 = 1 := by
  induction j with
  | zero => simp
  | succ j ih => rw [pow_succ, Polynomial.mul_coeff_zero, ih, hu0, one_mul]

theorem coeff_one_pow (hu0 : u.coeff 0 = 1) (hu1 : u.coeff 1 = 1) (j : ℕ) :
    (u ^ j).coeff 1 = (j : ℂ) := by
  induction j with
  | zero => simp [Polynomial.coeff_one]
  | succ j ih =>
      rw [pow_succ, Polynomial.mul_coeff_one,
        coeff_zero_pow_of_coeff_zero_eq_one hu0, ih, hu0, hu1]
      push_cast
      ring

/-- The pullback increment of a monomial: `X h (h^j - X^j)` vanishes to order `j+3` and its
leading coefficient there is `j`. -/
theorem X_mul_mul_sub_pow (hfac : h = X * u) (hu0 : u.coeff 0 = 1) (hu1 : u.coeff 1 = 1) (j : ℕ) :
    (X : Polynomial ℂ) ^ (j + 3) ∣ (X * h * (h ^ j - X ^ j)) ∧
      (X * h * (h ^ j - X ^ j)).coeff (j + 3) = (j : ℂ) := by
  have hkey : X * h * (h ^ j - X ^ j) = X ^ (j + 2) * (u * (u ^ j - 1)) := by
    rw [hfac]
    ring
  have hc0 : (u * (u ^ j - 1)).coeff 0 = 0 := by
    rw [Polynomial.mul_coeff_zero, Polynomial.coeff_sub, coeff_zero_pow_of_coeff_zero_eq_one hu0]
    simp
  have hc1 : (u * (u ^ j - 1)).coeff 1 = (j : ℂ) := by
    rw [Polynomial.mul_coeff_one]
    simp only [Polynomial.coeff_sub, coeff_zero_pow_of_coeff_zero_eq_one hu0,
      coeff_one_pow hu0 hu1, Polynomial.coeff_one, hu0, hu1]
    norm_num
  constructor
  · rw [hkey]
    have : (X : Polynomial ℂ) ^ (j + 3) = X ^ (j + 2) * X := by ring
    rw [this]
    refine mul_dvd_mul_left _ ?_
    rw [Polynomial.X_dvd_iff]
    exact hc0
  · rw [hkey, show j + 3 = 1 + (j + 2) by ring, Polynomial.coeff_X_pow_mul]
    exact hc1

/-- The Abel residual of the Fatou coordinate `Φ_P = -1/X + P`, cleared of denominators by `X h`:
`(Φ_P ∘ h - Φ_P - 1) · X h`. -/
def fatouResidual (h P : Polynomial ℂ) : Polynomial ℂ :=
  (h - X - X * h) + X * h * (P.comp h - P)

theorem fatouResidual_add_monomial (h P : Polynomial ℂ) (c : ℂ) (k : ℕ) :
    fatouResidual h (P + C c * X ^ k)
      = fatouResidual h P + C c * (X * h * (h ^ k - X ^ k)) := by
  simp only [fatouResidual, Polynomial.add_comp, Polynomial.mul_comp, Polynomial.C_comp,
    Polynomial.X_comp, Polynomial.pow_comp]
  ring

/-- **Triangular solvability of the finite-jet Abel equation.**  For a normalized zero-residue
parabolic jet there is a polynomial `P` with `P(0) = 0` and `deg P ≤ m - 3` whose Fatou residual
vanishes to order `m + 1`. -/
theorem exists_fatouPolynomial (hfac : h = X * u) (hu0 : u.coeff 0 = 1) (hu1 : u.coeff 1 = 1)
    (hbase : (X : Polynomial ℂ) ^ (4 : ℕ) ∣ (h - X - X * h)) {m : ℕ} (hm : 3 ≤ m) :
    ∃ P : Polynomial ℂ, P.coeff 0 = 0 ∧ P.natDegree ≤ m - 3 ∧
      (X : Polynomial ℂ) ^ (m + 1) ∣ fatouResidual h P := by
  induction m, hm using Nat.le_induction with
  | base =>
      refine ⟨0, by simp, by simp, ?_⟩
      simpa [fatouResidual] using hbase
  | succ m hm ih =>
      obtain ⟨P, hP0, hPdeg, hPdvd⟩ := ih
      have hm2 : ((m : ℂ) - 2) ≠ 0 := by
        intro hcon
        have h2 : (m : ℂ) = 2 := sub_eq_zero.mp hcon
        have : m = 2 := by exact_mod_cast h2
        omega
      set c : ℂ := -(fatouResidual h P).coeff (m + 1) / ((m : ℂ) - 2) with hc
      refine ⟨P + C c * X ^ (m - 2), ?_, ?_, ?_⟩
      · rw [Polynomial.coeff_add, hP0, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow]
        rw [if_neg (by omega)]
        ring
      · refine le_trans (Polynomial.natDegree_add_le _ _) (max_le (by omega) ?_)
        refine le_trans (Polynomial.natDegree_mul_le) ?_
        simp only [Polynomial.natDegree_C, Polynomial.natDegree_X_pow, zero_add]
        omega
      · obtain ⟨hstep_dvd, hstep_coeff⟩ := X_mul_mul_sub_pow hfac hu0 hu1 (m - 2)
        have hidx : (m - 2) + 3 = m + 1 := by omega
        rw [hidx] at hstep_dvd hstep_coeff
        rw [fatouResidual_add_monomial]
        have hcast : (((m - 2 : ℕ)) : ℂ) = (m : ℂ) - 2 := by
          have : (2 : ℕ) ≤ m := by omega
          push_cast [Nat.cast_sub this]
          ring
        rw [hcast] at hstep_coeff
        have hdvd1 : (X : Polynomial ℂ) ^ (m + 1) ∣
            fatouResidual h P + C c * (X * h * (h ^ (m - 2) - X ^ (m - 2))) :=
          dvd_add hPdvd (Dvd.dvd.mul_left hstep_dvd _)
        rw [Polynomial.X_pow_dvd_iff]
        intro d hd
        rcases lt_or_eq_of_le (Nat.lt_succ_iff.mp hd) with hlt | heq
        · exact (Polynomial.X_pow_dvd_iff.mp hdvd1) d hlt
        · rw [heq, Polynomial.coeff_add, Polynomial.coeff_C_mul, hstep_coeff, hc]
          field_simp
          ring

/-! ## The analytic Fatou germ -/

theorem analyticAt_polyEval_parabolicFatouJetRealization (P : Polynomial ℂ) (z : ℂ) :
    AnalyticAt ℂ (fun w : ℂ => Polynomial.eval w P) z := by
  have hd : Differentiable ℂ (fun w : ℂ => Polynomial.eval w P) := fun x =>
    (P.hasDerivAt x).differentiableAt
  exact (hd.differentiableOn.analyticOnNhd isOpen_univ) z (Set.mem_univ z)

/-- The reciprocal Fatou coordinate `1/Φ_P(w) = w / (-1 + w P(w))`, analytic at the origin. -/
def fatouRecip (P : Polynomial ℂ) (w : ℂ) : ℂ := w / (-1 + w * Polynomial.eval w P)

@[simp] theorem fatouRecip_zero (P : Polynomial ℂ) : fatouRecip P 0 = 0 := by
  simp [fatouRecip]

theorem analyticAt_fatouRecip (P : Polynomial ℂ) : AnalyticAt ℂ (fatouRecip P) 0 := by
  have hden : AnalyticAt ℂ (fun w : ℂ => -1 + w * Polynomial.eval w P) 0 :=
    analyticAt_const.add (analyticAt_id.mul (analyticAt_polyEval_parabolicFatouJetRealization P 0))
  have hne : (-1 : ℂ) + 0 * Polynomial.eval 0 P ≠ 0 := by norm_num
  exact analyticAt_id.div hden (by simp)

theorem deriv_fatouRecip (P : Polynomial ℂ) : deriv (fatouRecip P) 0 = -1 := by
  have hid : HasDerivAt (fun w : ℂ => w) (1 : ℂ) 0 := hasDerivAt_id' 0
  have hden : HasDerivAt (fun w : ℂ => -1 + w * Polynomial.eval w P)
      (1 * Polynomial.eval 0 P + 0 * Polynomial.eval 0 (Polynomial.derivative P)) 0 :=
    (hid.fun_mul (P.hasDerivAt 0)).const_add (-1)
  have hne : (-1 : ℂ) + 0 * Polynomial.eval 0 P ≠ 0 := by norm_num
  have hdiv := hid.fun_div hden hne
  show deriv (fun w : ℂ => w / (-1 + w * Polynomial.eval w P)) 0 = -1
  rw [hdiv.deriv]
  norm_num

/-- The Fatou germ: the branch of `Φ_P⁻¹(Φ_P + 1)` tending to `0`. -/
noncomputable def parabolicGerm (P : Polynomial ℂ) (γ : ℂ → ℂ) (z : ℂ) : ℂ :=
  γ (fatouRecip P z / (1 + fatouRecip P z))

theorem analyticAt_fatouShift (P : Polynomial ℂ) :
    AnalyticAt ℂ (fun z : ℂ => fatouRecip P z / (1 + fatouRecip P z)) 0 := by
  refine (analyticAt_fatouRecip P).div (analyticAt_const.add (analyticAt_fatouRecip P)) ?_
  simp

@[simp] theorem fatouShift_zero (P : Polynomial ℂ) :
    (fun z : ℂ => fatouRecip P z / (1 + fatouRecip P z)) 0 = 0 := by
  simp

/-- **Local analytic inverse.**  An analytic map with nonzero derivative has a local analytic
inverse on both sides. -/
theorem exists_localInverse_analytic {g : ℂ → ℂ} {z₀ : ℂ}
    (hgAt : AnalyticAt ℂ g z₀) (hd0 : deriv g z₀ ≠ 0) :
    ∃ γ : ℂ → ℂ, AnalyticAt ℂ γ (g z₀) ∧
      (∀ᶠ z in nhds z₀, γ (g z) = z) ∧ (∀ᶠ w in nhds (g z₀), g (γ w) = w) := by
  have hsd : HasStrictDerivAt g (deriv g z₀) z₀ := hgAt.hasStrictDerivAt
  exact ⟨hsd.localInverse _ _ _ hd0, hgAt.analyticAt_localInverse hd0,
    hsd.eventually_left_inverse hd0, hsd.eventually_right_inverse hd0⟩

/-! ## Flat factors and low-order jets -/

/-- A germ with an explicit flat factor of order `m` has vanishing jets below `m`. -/
theorem iteratedDeriv_eq_zero_of_flat_factor :
    ∀ {n m : ℕ} {f g : ℂ → ℂ}, AnalyticAt ℂ g 0 →
      f =ᶠ[nhds 0] (fun z => z ^ m * g z) → n < m → iteratedDeriv n f 0 = 0 := by
  intro n
  induction n with
  | zero =>
      intro m f g hg hf hn
      rw [iteratedDeriv_zero, hf.eq_of_nhds]
      have : m ≠ 0 := by omega
      simp [zero_pow this]
  | succ n ih =>
      intro m f g hg hf hn
      obtain ⟨m, rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
      have hgd : AnalyticAt ℂ (deriv g) 0 := hg.deriv
      have hderiv : deriv f =ᶠ[nhds 0]
          fun z : ℂ => z ^ m * ((m + 1 : ℂ) * g z + z * deriv g z) := by
        have h1 : deriv f =ᶠ[nhds 0] deriv (fun z : ℂ => z ^ (m + 1) * g z) := hf.deriv
        refine h1.trans ?_
        filter_upwards [hg.eventually_analyticAt] with z hz
        have hd : HasDerivAt (fun w : ℂ => w ^ (m + 1) * g w)
            (((m + 1 : ℕ) : ℂ) * z ^ m * g z + z ^ (m + 1) * deriv g z) z := by
          exact ((hasDerivAt_pow (m + 1) z).fun_mul hz.differentiableAt.hasDerivAt)
        rw [hd.deriv]
        push_cast
        ring
      rw [iteratedDeriv_succ']
      exact ih (analyticAt_const.mul hg |>.add (analyticAt_id.mul hgd)) hderiv (by omega)

/-! ## Polynomial divided differences -/

/-- The divided difference of a polynomial, as an explicit two-variable polynomial expression. -/
def polyDivDiff (P : Polynomial ℂ) (a b : ℂ) : ℂ :=
  ∑ k ∈ Finset.range (P.natDegree + 1),
    P.coeff k * ∑ i ∈ Finset.range k, a ^ i * b ^ (k - 1 - i)

theorem polyDivDiff_spec (P : Polynomial ℂ) (a b : ℂ) :
    Polynomial.eval a P - Polynomial.eval b P = (a - b) * polyDivDiff P a b := by
  rw [Polynomial.eval_eq_sum_range, Polynomial.eval_eq_sum_range, polyDivDiff,
    ← Finset.sum_sub_distrib, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  have hgeo : (∑ i ∈ Finset.range k, a ^ i * b ^ (k - 1 - i)) * (a - b) = a ^ k - b ^ k :=
    geom_sum₂_mul a b k
  calc P.coeff k * a ^ k - P.coeff k * b ^ k
      = P.coeff k * (a ^ k - b ^ k) := by ring
    _ = P.coeff k * ((∑ i ∈ Finset.range k, a ^ i * b ^ (k - 1 - i)) * (a - b)) := by rw [hgeo]
    _ = (a - b) * (P.coeff k * ∑ i ∈ Finset.range k, a ^ i * b ^ (k - 1 - i)) := by ring

theorem analyticAt_polyDivDiff (P : Polynomial ℂ) {A B : ℂ → ℂ} {z₀ : ℂ}
    (hA : AnalyticAt ℂ A z₀) (hB : AnalyticAt ℂ B z₀) :
    AnalyticAt ℂ (fun z => polyDivDiff P (A z) (B z)) z₀ := by
  unfold polyDivDiff
  refine Finset.analyticAt_fun_sum _ fun k _ => analyticAt_const.mul ?_
  exact Finset.analyticAt_fun_sum _ fun i _ => (hA.fun_pow i).mul (hB.fun_pow (k - 1 - i))

/-! ## The realization theorem -/

/-- The denominator of the reciprocal Fatou coordinate. -/
def fatouDen (P : Polynomial ℂ) (w : ℂ) : ℂ := -1 + w * Polynomial.eval w P

@[simp] theorem fatouDen_zero (P : Polynomial ℂ) : fatouDen P 0 = -1 := by simp [fatouDen]

theorem fatouRecip_eq (P : Polynomial ℂ) (w : ℂ) : fatouRecip P w = w / fatouDen P w := rfl

theorem analyticAt_fatouDen (P : Polynomial ℂ) {A : ℂ → ℂ} {z₀ : ℂ} (hA : AnalyticAt ℂ A z₀) :
    AnalyticAt ℂ (fun z => fatouDen P (A z)) z₀ :=
  analyticAt_const.add (hA.mul ((analyticAt_polyEval_parabolicFatouJetRealization P (A z₀)).comp hA))

/-- The cleared-denominator Abel identity for the jet polynomial: the numerator of
`Φ_P ∘ h - Φ_P - 1` is the negative of the Fatou residual. -/
theorem eval_fatouResidual (h P : Polynomial ℂ) (z : ℂ) :
    Polynomial.eval z h * (fatouDen P z + z) - z * fatouDen P (Polynomial.eval z h)
      = -Polynomial.eval z (fatouResidual h P) := by
  simp only [fatouDen, fatouResidual, Polynomial.eval_add, Polynomial.eval_sub,
    Polynomial.eval_mul, Polynomial.eval_X, Polynomial.eval_comp]
  ring

/-- The divided-difference form of the denominator increment. -/
theorem fatouDen_sub (P : Polynomial ℂ) (a b : ℂ) :
    fatouDen P a - fatouDen P b = (a - b) * (a * polyDivDiff P a b + Polynomial.eval b P) := by
  have h := polyDivDiff_spec P a b
  simp only [fatouDen]
  calc -1 + a * Polynomial.eval a P - (-1 + b * Polynomial.eval b P)
      = a * (Polynomial.eval a P - Polynomial.eval b P) + (a - b) * Polynomial.eval b P := by ring
    _ = a * ((a - b) * polyDivDiff P a b) + (a - b) * Polynomial.eval b P := by rw [h]
    _ = (a - b) * (a * polyDivDiff P a b + Polynomial.eval b P) := by ring

/-- **Zero-residue parabolic finite jets are realized by algebraic germs with rational Fatou
coordinate.**  For every normalized zero-residue parabolic jet and every order `N ≥ 4` there is a
polynomial `P` of degree at most `N - 3` with `P(0) = 0` and an analytic germ `f` at the origin
which solves the Abel equation for the rational Fatou coordinate `Φ_P = -1/z + P`, satisfies the
polynomial relation that makes it algebraic, and agrees with the prescribed jet through order
`N`. -/
theorem exists_algebraicFatouGerm {h u : Polynomial ℂ} (hfac : h = Polynomial.X * u)
    (hu0 : u.coeff 0 = 1) (hu1 : u.coeff 1 = 1)
    (hbase : (Polynomial.X : Polynomial ℂ) ^ (4 : ℕ) ∣ (h - Polynomial.X - Polynomial.X * h))
    {N : ℕ} (hN : 4 ≤ N) :
    ∃ (P : Polynomial ℂ) (f : ℂ → ℂ),
      P.coeff 0 = 0 ∧ P.natDegree ≤ N - 3 ∧ AnalyticAt ℂ f 0 ∧ f 0 = 0 ∧
      (∀ᶠ z in nhds (0 : ℂ),
        f z * (1 - z - z * Polynomial.eval z P + z * Polynomial.eval (f z) P) = z) ∧
      (∃ g : ℂ → ℂ, AnalyticAt ℂ g 0 ∧
        (fun z => f z - Polynomial.eval z h) =ᶠ[nhds 0] fun z => z ^ (N + 1) * g z) ∧
      (∀ j ≤ N, iteratedDeriv j (fun z => f z - Polynomial.eval z h) 0 = 0) := by
  classical
  obtain ⟨P, hP0, hPdeg, hPdvd⟩ :=
    exists_fatouPolynomial hfac hu0 hu1 hbase (le_trans (by norm_num) hN)
  obtain ⟨R, hR⟩ := hPdvd
  obtain ⟨γ, hγan, hγleft, hγright⟩ :=
    exists_localInverse_analytic (analyticAt_fatouRecip P) (by rw [deriv_fatouRecip]; norm_num)
  rw [fatouRecip_zero] at hγan hγright
  set F : ℂ → ℂ := parabolicGerm P γ with hF
  set S : ℂ → ℂ := fun z : ℂ => fatouRecip P z / (1 + fatouRecip P z) with hSdef
  have hSan : AnalyticAt ℂ S 0 := analyticAt_fatouShift P
  have hS0 : S 0 = 0 := by rw [hSdef]; simp
  have hγ0 : γ 0 = 0 := by
    have hz := hγleft.self_of_nhds
    rwa [fatouRecip_zero] at hz
  have hFan : AnalyticAt ℂ F 0 := by
    show AnalyticAt ℂ (fun z : ℂ => γ (S z)) 0
    have hγ' : AnalyticAt ℂ γ (S 0) := by rw [hS0]; exact hγan
    have hcomp := hγ'.comp hSan
    simpa [Function.comp_def] using hcomp
  have hF0 : F 0 = 0 := by
    show γ (S 0) = 0
    rw [hS0, hγ0]
  have hHan : AnalyticAt ℂ (fun z : ℂ => Polynomial.eval z h) 0 := analyticAt_polyEval_parabolicFatouJetRealization h 0
  have hH0 : Polynomial.eval (0 : ℂ) h = 0 := by rw [hfac]; simp
  have habel : ∀ᶠ z in nhds (0 : ℂ), fatouRecip P (F z) = S z := by
    have htend : Filter.Tendsto S (nhds 0) (nhds 0) := by
      simpa [hS0] using hSan.continuousAt.tendsto
    exact htend.eventually hγright
  have hden_ne : ∀ {A : ℂ → ℂ}, AnalyticAt ℂ A 0 → A 0 = 0 →
      ∀ᶠ z in nhds (0 : ℂ), fatouDen P (A z) ≠ 0 := by
    intro A hA hA0
    have hcont : ContinuousAt (fun z => fatouDen P (A z)) 0 :=
      (analyticAt_fatouDen P hA).continuousAt
    refine hcont.eventually_ne ?_
    show fatouDen P (A 0) ≠ 0
    rw [hA0, fatouDen_zero]
    norm_num
  have hdz : ∀ᶠ z in nhds (0 : ℂ), fatouDen P z ≠ 0 := hden_ne analyticAt_id rfl
  have hdF : ∀ᶠ z in nhds (0 : ℂ), fatouDen P (F z) ≠ 0 := hden_ne hFan hF0
  have hsum : ∀ᶠ z in nhds (0 : ℂ), fatouDen P z + z ≠ 0 := by
    have hcont : ContinuousAt (fun z : ℂ => fatouDen P z + z) 0 :=
      ((analyticAt_fatouDen P analyticAt_id).add analyticAt_id).continuousAt
    refine hcont.eventually_ne ?_
    show fatouDen P 0 + 0 ≠ 0
    simp
  have hFrel : ∀ᶠ z in nhds (0 : ℂ), F z * (fatouDen P z + z) = z * fatouDen P (F z) := by
    filter_upwards [habel, hdz, hdF, hsum] with z h1 h2 h3 h4
    rw [hSdef] at h1
    simp only [] at h1
    rw [fatouRecip_eq, fatouRecip_eq] at h1
    have e1 : z / fatouDen P z / (1 + z / fatouDen P z) = z / (fatouDen P z + z) := by
      field_simp
    rw [e1] at h1
    exact (div_eq_div_iff h3 h4).mp h1
  set B : ℂ → ℂ := fun z => (fatouDen P z + z) -
    z * (Polynomial.eval z h * polyDivDiff P (Polynomial.eval z h) (F z) +
      Polynomial.eval (F z) P) with hB
  have hBan : AnalyticAt ℂ B 0 := by
    refine ((analyticAt_fatouDen P analyticAt_id).add analyticAt_id).sub
      (analyticAt_id.mul ((hHan.mul (analyticAt_polyDivDiff P hHan hFan)).add ?_))
    exact (analyticAt_polyEval_parabolicFatouJetRealization P (F 0)).comp hFan
  have hB0 : B 0 = -1 := by
    rw [hB]
    simp
  have hBne : ∀ᶠ z in nhds (0 : ℂ), B z ≠ 0 := by
    refine hBan.continuousAt.eventually_ne ?_
    rw [hB0]
    norm_num
  have hkey : ∀ᶠ z in nhds (0 : ℂ),
      (Polynomial.eval z h - F z) * B z = -(z ^ (N + 1) * Polynomial.eval z R) := by
    filter_upwards [hFrel] with z hz
    have hHrel : Polynomial.eval z h * (fatouDen P z + z) -
        z * fatouDen P (Polynomial.eval z h) = -(z ^ (N + 1) * Polynomial.eval z R) := by
      have h1 := eval_fatouResidual h P z
      have hE : Polynomial.eval z (fatouResidual h P) = z ^ (N + 1) * Polynomial.eval z R := by
        rw [hR]; simp
      rw [hE] at h1
      exact h1
    have hdd := fatouDen_sub P (Polynomial.eval z h) (F z)
    show (Polynomial.eval z h - F z) * ((fatouDen P z + z) -
      z * (Polynomial.eval z h * polyDivDiff P (Polynomial.eval z h) (F z) +
        Polynomial.eval (F z) P)) = -(z ^ (N + 1) * Polynomial.eval z R)
    have hexp : (Polynomial.eval z h - F z) * ((fatouDen P z + z) -
        z * (Polynomial.eval z h * polyDivDiff P (Polynomial.eval z h) (F z) +
          Polynomial.eval (F z) P))
        = (Polynomial.eval z h * (fatouDen P z + z) -
              z * fatouDen P (Polynomial.eval z h))
            - (F z * (fatouDen P z + z) - z * fatouDen P (F z))
            + z * ((fatouDen P (Polynomial.eval z h) - fatouDen P (F z)) -
              (Polynomial.eval z h - F z) *
                (Polynomial.eval z h * polyDivDiff P (Polynomial.eval z h) (F z) +
                  Polynomial.eval (F z) P)) := by ring
    rw [hexp, hHrel, hz, hdd]
    ring
  have hgan : AnalyticAt ℂ (fun z : ℂ => Polynomial.eval z R / B z) 0 :=
    (analyticAt_polyEval_parabolicFatouJetRealization R 0).div hBan (by rw [hB0]; norm_num)
  have hgeq : (fun z => F z - Polynomial.eval z h) =ᶠ[nhds 0]
      fun z => z ^ (N + 1) * (Polynomial.eval z R / B z) := by
    filter_upwards [hkey, hBne] with z h1 h2
    show F z - Polynomial.eval z h = z ^ (N + 1) * (Polynomial.eval z R / B z)
    field_simp
    linear_combination -h1
  refine ⟨P, F, hP0, hPdeg, hFan, hF0, ?_, ⟨_, hgan, hgeq⟩, ?_⟩
  · filter_upwards [hFrel] with z hz
    simp only [fatouDen] at hz
    linear_combination -hz
  · intro j hj
    exact iteratedDeriv_eq_zero_of_flat_factor hgan hgeq (by omega)

/-- **Coefficient form of the realization theorem.**  Any polynomial jet normalized as
`z + z^(2 : ℕ) + z^(3 : ℕ) + O(z^(4 : ℕ))` is realized, through order `N`, by an algebraic germ with a rational
Fatou coordinate of degree at most `N - 3`. -/
theorem exists_algebraicFatouGerm_of_coeff {h : Polynomial ℂ}
    (h0 : h.coeff 0 = 0) (h1 : h.coeff 1 = 1) (h2 : h.coeff 2 = 1) (h3 : h.coeff 3 = 1)
    {N : ℕ} (hN : 4 ≤ N) :
    ∃ (P : Polynomial ℂ) (f : ℂ → ℂ),
      P.coeff 0 = 0 ∧ P.natDegree ≤ N - 3 ∧ AnalyticAt ℂ f 0 ∧ f 0 = 0 ∧
      (∀ᶠ z in nhds (0 : ℂ),
        f z * (1 - z - z * Polynomial.eval z P + z * Polynomial.eval (f z) P) = z) ∧
      (∃ g : ℂ → ℂ, AnalyticAt ℂ g 0 ∧
        (fun z => f z - Polynomial.eval z h) =ᶠ[nhds 0] fun z => z ^ (N + 1) * g z) ∧
      (∀ j ≤ N, iteratedDeriv j (fun z => f z - Polynomial.eval z h) 0 = 0) := by
  obtain ⟨u, hu⟩ := Polynomial.X_dvd_iff.mpr h0
  have hu0 : u.coeff 0 = 1 := by
    have : h.coeff 1 = u.coeff 0 := by rw [hu, Polynomial.coeff_X_mul]
    rw [← this, h1]
  have hu1 : u.coeff 1 = 1 := by
    have : h.coeff 2 = u.coeff 1 := by rw [hu, Polynomial.coeff_X_mul]
    rw [← this, h2]
  have hbase : (Polynomial.X : Polynomial ℂ) ^ (4 : ℕ) ∣ (h - Polynomial.X - Polynomial.X * h) := by
    rw [Polynomial.X_pow_dvd_iff]
    intro d hd
    interval_cases d <;>
      simp [Polynomial.coeff_sub, Polynomial.coeff_X_mul, Polynomial.coeff_X, h0, h1, h2, h3]
  exact exists_algebraicFatouGerm hu hu0 hu1 hbase hN

end

end GaloisForLFunctions.HTGeometry
