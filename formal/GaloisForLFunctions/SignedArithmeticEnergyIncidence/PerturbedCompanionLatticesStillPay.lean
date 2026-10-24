import GaloisForLFunctions.SignedArithmeticEnergyIncidence.PaleyWienerSourcesPayAtTheNyquistDensity

/-!
# Perturbed companion lattices still pay

The Nyquist law (`pwCompanions_pay`) is stable under moving the companions.  Let `γ_k` be
companions within `δ` of the lattice `x_k = t₀ + kh`, `A h ≤ π`, and `f` a Paley–Wiener source of
aperture `A`.

* **Derivative samples** (`hasSum_sq_pwDeriv_lattice`, `sq_pwDeriv_lattice_le`): `f'` is the
  source of the density `iξ F`, so on every translate of the lattice
  `Σ_k |f'(s + kh)|² ≤ A² Σ_k |f(x_k)|²`.
* **Moving a companion** (`norm_sq_pwSource_sub_le`): `f(γ_k) − f(x_k) = ∫ f'`, so by
  Cauchy–Schwarz `|f(γ_k) − f(x_k)|² ≤ 2δ ∫_{−δ}^{δ} |f'(x_k + u)|² du`.
* **Summing** (`sum_sq_pwSource_perturbed_sub_le`): over any finite set of companions,
  `Σ_k |f(γ_k) − f(x_k)|² ≤ (2Aδ)² Σ_k |f(x_k)|²`.
* **Payment** (`pwPerturbedCompanions_pay`): if `2Aδ ≤ ε < 1`, then
  `Σ_k |f(γ_k)|² ≥ (1 − ε)² Σ_k |f(x_k)|²` (`norm_add_sq_ge` termwise), and a depth mass `w` at any
  height is paid as soon as `w A³h/(3π) ≤ (1 − ε)²`.

Companion sets need not be lattices: displacements up to `1/(2A)`, half the reciprocal aperture,
keep the Nyquist law with an explicit loss.
-/

open MeasureTheory Complex Set Filter Topology

namespace GaloisForLFunctions.SignedArithmeticEnergyIncidence

noncomputable section
set_option autoImplicit false

variable {F : ℝ → ℂ} {A : ℝ}

/-! ### The derivative as a source -/

/-- `f'` is the Paley–Wiener source of the density `iξ F`. -/
theorem pwDeriv_eq_pwSource (F : ℝ → ℂ) (x : ℝ) :
    pwDeriv F x = pwSource (fun ξ : ℝ => (ξ : ℂ) * I * F ξ) x := rfl

/-- The density `iξ F` has aperture `A` and is in `L²`. -/
theorem memLp_derivDensity (hF : MemLp F 2 volume) (hsupp : ∀ ξ, A ≤ |ξ| → F ξ = 0) :
    MemLp (fun ξ : ℝ => (ξ : ℂ) * I * F ξ) 2 volume ∧
      ∀ ξ, A ≤ |ξ| → (ξ : ℂ) * I * F ξ = 0 := by
  refine ⟨(hF.const_mul ((|A| : ℝ) : ℂ)).of_le
    (((continuous_ofReal.mul continuous_const).aestronglyMeasurable).mul hF.1)
    (ae_of_all _ fun ξ => ?_), fun ξ hξ => by rw [hsupp ξ hξ, mul_zero]⟩
  simp only [norm_mul, Complex.norm_I, Complex.norm_real, Real.norm_eq_abs, mul_one, abs_abs]
  by_cases hξ : A ≤ |ξ|
  · rw [hsupp ξ hξ, norm_zero, mul_zero, mul_zero]
  · push Not at hξ
    exact mul_le_mul_of_nonneg_right (hξ.le.trans (le_abs_self A)) (norm_nonneg _)

/-- `∫ |ξ F|² ≤ A² ∫ |F|²` for a density of aperture `A`. -/
theorem integral_sq_derivDensity_le (hF : MemLp F 2 volume) (hsupp : ∀ ξ, A ≤ |ξ| → F ξ = 0) :
    ∫ ξ : ℝ, ‖(ξ : ℂ) * I * F ξ‖ ^ 2 ≤ A ^ 2 * ∫ ξ : ℝ, ‖F ξ‖ ^ 2 := by
  rw [← integral_const_mul]
  refine integral_mono_of_nonneg (ae_of_all _ fun ξ => sq_nonneg _)
    ((memLp_two_iff_integrable_sq_norm hF.1).mp hF |>.const_mul _) (ae_of_all _ fun ξ => ?_)
  show ‖(ξ : ℂ) * I * F ξ‖ ^ 2 ≤ A ^ 2 * ‖F ξ‖ ^ 2
  rw [norm_mul, norm_mul, Complex.norm_I, Complex.norm_real, Real.norm_eq_abs, mul_one, mul_pow]
  by_cases hξ : A ≤ |ξ|
  · rw [hsupp ξ hξ, norm_zero]; simp
  · push Not at hξ
    exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (abs_nonneg _) hξ.le 2) (sq_nonneg _)

/-- **Derivative samples on any translate of the lattice**:
`Σ_k |f'(s + kh)|² = (2π/h) ∫ |ξF|² ≤ A² (2π/h) ∫ |F|²`. -/
theorem hasSum_sq_pwDeriv_lattice (hF : MemLp F 2 volume) (hsupp : ∀ ξ, A ≤ |ξ| → F ξ = 0)
    {h : ℝ} (hh : 0 < h) (hAh : A * h ≤ Real.pi) (s : ℝ) :
    HasSum (fun k : ℤ => ‖pwDeriv F (s + k * h)‖ ^ 2)
      (2 * Real.pi / h * ∫ ξ : ℝ, ‖(ξ : ℂ) * I * F ξ‖ ^ 2) := by
  obtain ⟨hG, hGs⟩ := memLp_derivDensity hF hsupp
  exact hasSum_sq_pwSource_lattice hG hGs hh hAh s

theorem sq_pwDeriv_lattice_le (hF : MemLp F 2 volume) (hsupp : ∀ ξ, A ≤ |ξ| → F ξ = 0)
    {h : ℝ} (hh : 0 < h) (hAh : A * h ≤ Real.pi) (s : ℝ) (K : Finset ℤ) :
    ∑ k ∈ K, ‖pwDeriv F (s + k * h)‖ ^ 2 ≤ A ^ 2 * (2 * Real.pi / h * ∫ ξ : ℝ, ‖F ξ‖ ^ 2) := by
  have hs := hasSum_sq_pwDeriv_lattice hF hsupp hh hAh s
  refine (sum_le_hasSum K (fun k _ => sq_nonneg _) hs).trans ?_
  have := integral_sq_derivDensity_le hF hsupp
  have h2 : 0 ≤ 2 * Real.pi / h := by positivity
  nlinarith

theorem continuous_pwDeriv (hF : MemLp F 2 volume) (hsupp : ∀ ξ, A ≤ |ξ| → F ξ = 0) :
    Continuous (pwDeriv F) := by
  obtain ⟨hG, hGs⟩ := memLp_derivDensity hF hsupp
  exact continuous_iff_continuousAt.mpr fun x => (hasDerivAt_pwSource hG hGs x).continuousAt

/-! ### Moving one companion -/

/-- Cauchy–Schwarz on an interval: `(∫_a^b g)² ≤ (b − a) ∫_a^b g²` for continuous `g`. -/
theorem sq_intervalIntegral_le {g : ℝ → ℝ} (hg : Continuous g) {a b : ℝ} (hab : a < b) :
    (∫ x in a..b, g x) ^ 2 ≤ (b - a) * ∫ x in a..b, g x ^ 2 := by
  set I₁ := ∫ x in a..b, g x
  set m := I₁ / (b - a)
  have hba : 0 < b - a := by linarith
  have hexp : ∫ x in a..b, (g x - m) ^ 2 =
      (∫ x in a..b, g x ^ 2) - 2 * m * I₁ + m ^ 2 * (b - a) := by
    have e : (fun x => (g x - m) ^ 2) = fun x => (g x ^ 2 - 2 * m * g x) + m ^ 2 := by
      funext x; ring
    rw [e, intervalIntegral.integral_add
      ((by fun_prop : Continuous fun x => g x ^ 2 - 2 * m * g x).intervalIntegrable _ _)
      intervalIntegrable_const, intervalIntegral.integral_sub
      ((by fun_prop : Continuous fun x => g x ^ 2).intervalIntegrable _ _)
      ((by fun_prop : Continuous fun x => 2 * m * g x).intervalIntegrable _ _),
      intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const, smul_eq_mul]
    ring
  have h0 : 0 ≤ ∫ x in a..b, (g x - m) ^ 2 :=
    intervalIntegral.integral_nonneg hab.le fun x _ => sq_nonneg _
  rw [hexp] at h0
  have hm : m * (b - a) = I₁ := by simp only [m]; field_simp
  nlinarith

/-- **Moving one companion**: for `|d| ≤ δ`,
`|f(x + d) − f(x)|² ≤ 2δ ∫_{−δ}^{δ} |f'(x + u)|² du`. -/
theorem norm_sq_pwSource_sub_le (hF : MemLp F 2 volume) (hsupp : ∀ ξ, A ≤ |ξ| → F ξ = 0)
    (x : ℝ) {d δ : ℝ} (hd : |d| ≤ δ) (hδ : 0 < δ) :
    ‖pwSource F (x + d) - pwSource F x‖ ^ 2 ≤
      2 * δ * ∫ u in (-δ)..δ, ‖pwDeriv F (x + u)‖ ^ 2 := by
  have hc := continuous_pwDeriv hF hsupp
  have hcn : Continuous fun y => ‖pwDeriv F y‖ := hc.norm
  have hftc : pwSource F (x + d) - pwSource F x = ∫ y in x..(x + d), pwDeriv F y :=
    (intervalIntegral.integral_eq_sub_of_hasDerivAt (fun y _ => hasDerivAt_pwSource hF hsupp y)
      (hc.intervalIntegrable _ _)).symm
  -- `‖∫_x^{x+d} f'‖ ≤ ∫_{x−δ}^{x+δ} ‖f'‖`
  have hd1 : -δ ≤ d := (abs_le.mp hd).1
  have hd2 : d ≤ δ := (abs_le.mp hd).2
  have hnn : ∀ c₁ c₂, 0 ≤ᵐ[volume.restrict (Ioc c₁ c₂)] fun y => ‖pwDeriv F y‖ :=
    fun _ _ => ae_of_all _ fun _ => norm_nonneg _
  have hle : ‖∫ y in x..(x + d), pwDeriv F y‖ ≤ ∫ y in (x - δ)..(x + δ), ‖pwDeriv F y‖ := by
    refine (intervalIntegral.norm_integral_le_abs_integral_norm).trans ?_
    rcases le_total 0 d with h0 | h0
    · rw [abs_of_nonneg (intervalIntegral.integral_nonneg (by linarith) fun _ _ => norm_nonneg _)]
      exact intervalIntegral.integral_mono_interval (by linarith) (by linarith) (by linarith)
        (hnn _ _) (hcn.intervalIntegrable _ _)
    · rw [intervalIntegral.integral_symm, abs_neg,
        abs_of_nonneg (intervalIntegral.integral_nonneg (by linarith) fun _ _ => norm_nonneg _)]
      exact intervalIntegral.integral_mono_interval (by linarith) (by linarith) (by linarith)
        (hnn _ _) (hcn.intervalIntegrable _ _)
  have hcs := sq_intervalIntegral_le hcn (by linarith : x - δ < x + δ)
  have hshift : ∫ y in (x - δ)..(x + δ), ‖pwDeriv F y‖ ^ 2 =
      ∫ u in (-δ)..δ, ‖pwDeriv F (x + u)‖ ^ 2 := by
    have := intervalIntegral.integral_comp_add_left (fun y => ‖pwDeriv F y‖ ^ 2) x
      (a := -δ) (b := δ)
    rw [this]
    congr 1
  rw [hftc]
  calc ‖∫ y in x..(x + d), pwDeriv F y‖ ^ 2
      ≤ (∫ y in (x - δ)..(x + δ), ‖pwDeriv F y‖) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) hle 2
    _ ≤ (x + δ - (x - δ)) * ∫ y in (x - δ)..(x + δ), ‖pwDeriv F y‖ ^ 2 := hcs
    _ = 2 * δ * ∫ u in (-δ)..δ, ‖pwDeriv F (x + u)‖ ^ 2 := by rw [hshift]; ring

/-! ### Summing over the companions -/

/-- **The displacement energy**: companions `γ_k` within `δ` of `x_k = t₀ + kh` have
`Σ_{k ∈ K} |f(γ_k) − f(x_k)|² ≤ (2Aδ)² (2π/h) ∫ |F|²` for every finite `K`. -/
theorem sum_sq_pwSource_perturbed_sub_le (hF : MemLp F 2 volume)
    (hsupp : ∀ ξ, A ≤ |ξ| → F ξ = 0) {h : ℝ} (hh : 0 < h) (hAh : A * h ≤ Real.pi) (t₀ : ℝ)
    {δ : ℝ} (hδ : 0 < δ) (γ : ℤ → ℝ) (hγ : ∀ k : ℤ, |γ k - (t₀ + k * h)| ≤ δ) (K : Finset ℤ) :
    ∑ k ∈ K, ‖pwSource F (γ k) - pwSource F (t₀ + k * h)‖ ^ 2 ≤
      (2 * A * δ) ^ 2 * (2 * Real.pi / h * ∫ ξ : ℝ, ‖F ξ‖ ^ 2) := by
  set B := A ^ 2 * (2 * Real.pi / h * ∫ ξ : ℝ, ‖F ξ‖ ^ 2)
  have hc := continuous_pwDeriv hF hsupp
  have hterm : ∀ k ∈ K, ‖pwSource F (γ k) - pwSource F (t₀ + k * h)‖ ^ 2 ≤
      2 * δ * ∫ u in (-δ)..δ, ‖pwDeriv F (t₀ + k * h + u)‖ ^ 2 := by
    intro k _
    have h1 := norm_sq_pwSource_sub_le hF hsupp (t₀ + k * h) (d := γ k - (t₀ + k * h)) (hγ k) hδ
    rwa [add_sub_cancel] at h1
  have hint : ∀ k : ℤ, IntervalIntegrable (fun u => ‖pwDeriv F (t₀ + k * h + u)‖ ^ 2) volume
      (-δ) δ := fun k =>
    ((hc.comp (continuous_const.add continuous_id)).norm.pow 2).intervalIntegrable _ _
  have hsum : ∑ k ∈ K, ∫ u in (-δ)..δ, ‖pwDeriv F (t₀ + k * h + u)‖ ^ 2 ≤ 2 * δ * B := by
    rw [← intervalIntegral.integral_finsetSum fun k _ => hint k]
    have hB : ∀ u ∈ Set.Icc (-δ) δ, ∑ k ∈ K, ‖pwDeriv F (t₀ + k * h + u)‖ ^ 2 ≤ B := by
      intro u _
      have := sq_pwDeriv_lattice_le hF hsupp hh hAh (t₀ + u) K
      refine le_trans (le_of_eq (Finset.sum_congr rfl fun k _ => ?_)) this
      congr 3; ring
    calc ∫ u in (-δ)..δ, ∑ k ∈ K, ‖pwDeriv F (t₀ + k * h + u)‖ ^ 2
        ≤ ∫ u in (-δ)..δ, B :=
          intervalIntegral.integral_mono_on (by linarith)
            ((continuous_finsetSum K fun k _ =>
              (hc.comp (continuous_const.add continuous_id)).norm.pow 2).intervalIntegrable _ _)
            intervalIntegrable_const hB
      _ = 2 * δ * B := by rw [intervalIntegral.integral_const, smul_eq_mul]; ring
  calc ∑ k ∈ K, ‖pwSource F (γ k) - pwSource F (t₀ + k * h)‖ ^ 2
      ≤ ∑ k ∈ K, 2 * δ * ∫ u in (-δ)..δ, ‖pwDeriv F (t₀ + k * h + u)‖ ^ 2 :=
        Finset.sum_le_sum hterm
    _ = 2 * δ * ∑ k ∈ K, ∫ u in (-δ)..δ, ‖pwDeriv F (t₀ + k * h + u)‖ ^ 2 := by
        rw [Finset.mul_sum]
    _ ≤ 2 * δ * (2 * δ * B) := mul_le_mul_of_nonneg_left hsum (by linarith)
    _ = (2 * A * δ) ^ 2 * (2 * Real.pi / h * ∫ ξ : ℝ, ‖F ξ‖ ^ 2) := by simp only [B]; ring

/-- `‖a + e‖² ≥ (1 − ε)‖a‖² − (1/ε − 1)‖e‖²` for `0 < ε`. -/
theorem norm_add_sq_ge (a e : ℂ) {ε : ℝ} (hε : 0 < ε) :
    (1 - ε) * ‖a‖ ^ 2 - (1 / ε - 1) * ‖e‖ ^ 2 ≤ ‖a + e‖ ^ 2 := by
  have h1 : |‖a‖ - ‖e‖| ≤ ‖a + e‖ := by
    have := abs_norm_sub_norm_le a (-e); rwa [norm_neg, sub_neg_eq_add] at this
  have h2 : (‖a‖ - ‖e‖) ^ 2 ≤ ‖a + e‖ ^ 2 := by
    rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) h1 2
  have key : (1 - ε) * ‖a‖ ^ 2 - (1 / ε - 1) * ‖e‖ ^ 2 =
      (‖a‖ - ‖e‖) ^ 2 - (ε * ‖a‖ - ‖e‖) ^ 2 / ε := by
    field_simp; ring
  have h3 : 0 ≤ (ε * ‖a‖ - ‖e‖) ^ 2 / ε := div_nonneg (sq_nonneg _) hε.le
  linarith

/-- **Perturbed companion lattices pay**: companions within `δ` of `t₀ + hℤ`, `A h ≤ π`,
`2Aδ ≤ ε < 1`, pay a depth mass `w` at every height `t` whenever `w A³h/(3π) ≤ (1 − ε)²`. -/
theorem pwPerturbedCompanions_pay (hF : MemLp F 2 volume) (hsupp : ∀ ξ, A ≤ |ξ| → F ξ = 0)
    (hA : 0 ≤ A) {h : ℝ} (hh : 0 < h) (hAh : A * h ≤ Real.pi) (t₀ t : ℝ) {δ ε : ℝ}
    (hδ : 0 < δ) (γ : ℤ → ℝ) (hγ : ∀ k : ℤ, |γ k - (t₀ + k * h)| ≤ δ) (hε0 : 0 < ε)
    (hε1 : ε < 1) (hδε : 2 * A * δ ≤ ε) {w : ℝ} (hw : 0 ≤ w)
    (hprice : w * (A ^ 3 * h / (3 * Real.pi)) ≤ (1 - ε) ^ 2) :
    Summable (fun k : ℤ => ‖pwSource F (γ k)‖ ^ 2) ∧
      w * ‖pwDeriv F t‖ ^ 2 ≤ ∑' k : ℤ, ‖pwSource F (γ k)‖ ^ 2 := by
  set S := 2 * Real.pi / h * ∫ ξ : ℝ, ‖F ξ‖ ^ 2
  have hS0 : 0 ≤ S := mul_nonneg (by positivity) (integral_nonneg fun ξ => sq_nonneg _)
  have hlat := hasSum_sq_pwSource_lattice hF hsupp hh hAh t₀
  set a : ℤ → ℂ := fun k => pwSource F (t₀ + k * h)
  set e : ℤ → ℂ := fun k => pwSource F (γ k) - pwSource F (t₀ + k * h)
  have he := sum_sq_pwSource_perturbed_sub_le hF hsupp hh hAh t₀ hδ γ hγ
  have hesum : Summable fun k => ‖e k‖ ^ 2 :=
    summable_of_sum_le (fun k => sq_nonneg _) he
  have heS : ∑' k, ‖e k‖ ^ 2 ≤ ε ^ 2 * S := by
    refine (hesum.tsum_le_of_sum_le he).trans ?_
    have h2 : (2 * A * δ) ^ 2 ≤ ε ^ 2 := pow_le_pow_left₀ (by positivity) hδε 2
    exact mul_le_mul_of_nonneg_right h2 hS0
  have hval : ∀ k, pwSource F (γ k) = a k + e k := fun k => by simp only [a, e]; ring
  -- summability of the perturbed samples
  have hbound : ∀ k, ‖pwSource F (γ k)‖ ^ 2 ≤ 2 * ‖a k‖ ^ 2 + 2 * ‖e k‖ ^ 2 := by
    intro k
    rw [hval k]
    have := norm_add_le (a k) (e k)
    nlinarith [norm_nonneg (a k + e k), norm_nonneg (a k), norm_nonneg (e k),
      sq_nonneg (‖a k‖ - ‖e k‖)]
  have hsum : Summable fun k => ‖pwSource F (γ k)‖ ^ 2 :=
    Summable.of_nonneg_of_le (fun k => sq_nonneg _) hbound
      ((hlat.summable.mul_left 2).add (hesum.mul_left 2))
  refine ⟨hsum, ?_⟩
  -- the lower frame bound `(1 − ε)² S`
  have hlow : (1 - ε) ^ 2 * S ≤ ∑' k, ‖pwSource F (γ k)‖ ^ 2 := by
    have hpt : ∀ k, (1 - ε) * ‖a k‖ ^ 2 - (1 / ε - 1) * ‖e k‖ ^ 2 ≤ ‖pwSource F (γ k)‖ ^ 2 :=
      fun k => by rw [hval k]; exact norm_add_sq_ge (a k) (e k) hε0
    have hs1 : HasSum (fun k => (1 - ε) * ‖a k‖ ^ 2 - (1 / ε - 1) * ‖e k‖ ^ 2)
        ((1 - ε) * S - (1 / ε - 1) * ∑' k, ‖e k‖ ^ 2) :=
      (hlat.mul_left (1 - ε)).sub (hesum.hasSum.mul_left (1 / ε - 1))
    have hle := hasSum_le hpt hs1 hsum.hasSum
    have hc : 0 ≤ 1 / ε - 1 := by
      rw [sub_nonneg, le_div_iff₀ hε0]; linarith
    have := mul_le_mul_of_nonneg_left heS hc
    have e2 : (1 - ε) * S - (1 / ε - 1) * (ε ^ 2 * S) = (1 - ε) ^ 2 * S := by
      field_simp
    linarith
  have hD := norm_sq_pwDeriv_le hF hsupp hA t
  have hh0 : h ≠ 0 := hh.ne'
  have hπ0 : Real.pi ≠ 0 := Real.pi_pos.ne'
  have e : 2 * A ^ 3 / 3 * ∫ ξ : ℝ, ‖F ξ‖ ^ 2 = A ^ 3 * h / (3 * Real.pi) * S := by
    simp only [S]; field_simp
  calc w * ‖pwDeriv F t‖ ^ 2 ≤ w * (A ^ 3 * h / (3 * Real.pi) * S) := by
        rw [← e]; exact mul_le_mul_of_nonneg_left hD hw
    _ = (w * (A ^ 3 * h / (3 * Real.pi))) * S := by ring
    _ ≤ (1 - ε) ^ 2 * S := mul_le_mul_of_nonneg_right hprice hS0
    _ ≤ _ := hlow

end

end GaloisForLFunctions.SignedArithmeticEnergyIncidence
