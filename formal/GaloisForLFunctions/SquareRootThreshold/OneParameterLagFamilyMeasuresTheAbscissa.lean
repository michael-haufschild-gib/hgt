import GaloisForLFunctions.SquareRootThreshold.OneParameterLagFamilyDeterminesTheConfiguration

/-!
# The lag family measures the abscissa of the zeros

Let `Θ = sup Re ρ`. For a generic width `w` the one-parameter family
`f_v = κ_w(t + v/2) − κ_w(t − v/2)` decides more than whether `Θ = ½`
(`onLine_iff_lag_twoBump_nonneg_of_lt_one`): it measures `Θ`. For every `σ ≥ 0`, every zero has
`Re ρ ≤ ½ + σ` iff `Re W(f_v, f_v) ≥ −C e^{σv}` for all large `v`
(`re_le_iff_lag_twoBump_ge_neg_exp`). The negativity of one real function of the lag grows at
exactly the rate `Θ − ½`.

* **Upper rate** (`two_re_lagStructure_le_mul_exp`). `Re W(f_v, f_v) = 2 Re S(0) − 2 Re S(v)`,
  and `2 Re S(v) = Σ_z D(z) e^{zv}` has exponents `Re z = Re ρ − ½`.
* **Lower rate** (`evenCoeff_eq_zero_of_lag_ge_neg_exp`). A bound `−C e^{σv}` gives
  `2 Re S(u) ≤ M e^{σu}` for all `u ≥ 0` (`exists_two_re_lagStructure_le_exp`). A largest real
  exponent `δ* > σ` is isolated by Landau's theorem at level `δ*`
  (`evenCoeff_eq_zero_of_two_re_lagStructure_le_exp`). After the shift by `e^{−σv}` its positive
  coefficient contradicts the one-sided bound under Abel means (`re_le_zero_of_re_tsum_exp_le`).
  Landau at level `σ` then removes every exponent with `Re z > σ`. The merged coefficient
  `(m(ρ) + m(ρ̄)) h_w(γ_ρ)²` of a zero with `Re ρ > ½ + σ` is not zero.

**Prime side.** For `ζ` (`zeta_re_le_iff_lag_primeWindow_ge_neg_exp`) and every primitive
Dirichlet `L(s, χ)` (`dirichlet_re_le_iff_lag_primeWindow_ge_neg_exp`), all but countably many
widths `w ∈ (0, ½ log 2)` satisfy: every zero has `Re ρ ≤ ½ + σ` iff the functional of the prime
window at `X = e^v` is `≥ −C X^σ` for all large `X`. Each quasi-RH half-plane is one growth
condition on one family of dyadic prime windows.
-/

open MeasureTheory Complex Set Filter Topology
open scoped Real ComplexConjugate

noncomputable section

namespace GaloisForLFunctions.SquareRootThreshold

open Zeta23 _root_.RHTower

/-! ### Upper rate -/

/-- `2 Re S(u) ≤ (Σ_z |D(z)|) e^{τu}` for `u ≥ 0` when every exponent has `Re z ≤ τ`. -/
theorem two_re_lagStructure_le_mul_exp (Z : ZeroConfig) (hZ : TemperedConfig Z) {b : ℝ → ℂ}
    (hb : ContDiff ℝ 2 b) {w : ℝ} (hbs : ∀ u, b u ≠ 0 → |u| ≤ w) {τ : ℝ}
    (hτ : ∀ z : ℂ, evenCoeff Z b z ≠ 0 → z.re ≤ τ) {u : ℝ} (hu : 0 ≤ u) :
    2 * (lagStructure Z b u).re ≤ (∑' z : ℂ, ‖evenCoeff Z b z‖) * Real.exp (τ * u) := by
  obtain ⟨hs, he⟩ := two_re_lagStructure_eq Z hZ hb hbs u
  have hD : Summable fun z : ℂ => ‖evenCoeff Z b z‖ := by
    have h0 := (two_re_lagStructure_eq Z hZ hb hbs 0).1.norm
    simp only [Complex.ofReal_zero, mul_zero, Complex.exp_zero, mul_one] at h0
    exact h0
  have hterm : ∀ z : ℂ,
      ‖evenCoeff Z b z * cexp (z * u)‖ ≤ ‖evenCoeff Z b z‖ * Real.exp (τ * u) := fun z => by
    by_cases h0 : evenCoeff Z b z = 0
    · simp [h0]
    rw [norm_mul, Complex.norm_exp]
    refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (norm_nonneg _)
    have : (z * (u : ℂ)).re = z.re * u := by simp
    rw [this]
    exact mul_le_mul_of_nonneg_right (hτ z h0) hu
  calc 2 * (lagStructure Z b u).re ≤ ‖((2 * (lagStructure Z b u).re : ℝ) : ℂ)‖ := by
        rw [Complex.norm_real, Real.norm_eq_abs]; exact le_abs_self _
    _ = ‖∑' z : ℂ, evenCoeff Z b z * cexp (z * u)‖ := by rw [he]
    _ ≤ ∑' z : ℂ, ‖evenCoeff Z b z‖ * Real.exp (τ * u) :=
        (norm_tsum_le_tsum_norm hs.norm).trans (Summable.tsum_le_tsum hterm hs.norm (hD.mul_right _))
    _ = (∑' z : ℂ, ‖evenCoeff Z b z‖) * Real.exp (τ * u) := tsum_mul_right

/-! ### Lower rate -/

/-- **One-sided growth on all lags.** If `Re W ≥ −C e^{σv}` on the difference tests
`b(t + v/2) − b(t − v/2)` at every lag `v ≥ V`, with `σ ≥ 0`, then `2 Re S(u) ≤ M e^{σu}` for all
`u ≥ 0`, with some `M ≥ 0`. -/
theorem exists_two_re_lagStructure_le_exp (Z : ZeroConfig) (hZ : TemperedConfig Z) {b : ℝ → ℂ}
    (hb : ContDiff ℝ 2 b) {w : ℝ} (hbs : ∀ u, b u ≠ 0 → |u| ≤ w) {σ C V : ℝ} (hσ : 0 ≤ σ)
    (hm : ∀ v : ℝ, V ≤ v →
      -(C * Real.exp (σ * v)) ≤ (Z.W (twoBump b v (-1)) (twoBump b v (-1))).re) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ u : ℝ, 0 ≤ u → 2 * (lagStructure Z b u).re ≤ M * Real.exp (σ * u) := by
  set A := 2 * (lagStructure Z b 0).re with hA
  set N := ∑' z : ℂ, ‖evenCoeff Z b z‖ with hN
  have hN0 : 0 ≤ N := tsum_nonneg fun _ => norm_nonneg _
  have hNV : 0 ≤ N * Real.exp (|V| / 2) := mul_nonneg hN0 (Real.exp_pos _).le
  refine ⟨|A| + |C| + N * Real.exp (|V| / 2), by positivity, fun u hu => ?_⟩
  have he1 : 1 ≤ Real.exp (σ * u) := Real.one_le_exp (mul_nonneg hσ hu)
  have hrhs : (|A| + |C| + N * Real.exp (|V| / 2)) * Real.exp (σ * u) =
      |A| * Real.exp (σ * u) + |C| * Real.exp (σ * u) +
        N * Real.exp (|V| / 2) * Real.exp (σ * u) := by ring
  have h1 : |A| ≤ |A| * Real.exp (σ * u) := le_mul_of_one_le_right (abs_nonneg _) he1
  have h2 : C * Real.exp (σ * u) ≤ |C| * Real.exp (σ * u) :=
    mul_le_mul_of_nonneg_right (le_abs_self C) (Real.exp_pos _).le
  have h3 : N * Real.exp (|V| / 2) ≤ N * Real.exp (|V| / 2) * Real.exp (σ * u) :=
    le_mul_of_one_le_right hNV he1
  have h4 : 0 ≤ |C| * Real.exp (σ * u) := mul_nonneg (abs_nonneg _) (Real.exp_pos _).le
  have h5 : 0 ≤ N * Real.exp (|V| / 2) * Real.exp (σ * u) := mul_nonneg hNV (Real.exp_pos _).le
  rw [hrhs]
  rcases le_or_gt V u with hVu | huV
  · have h := hm u hVu
    rw [re_W_lag_eq Z hZ hb hbs] at h
    linarith [le_abs_self A]
  · have h := two_re_lagStructure_le_mul_exp Z hZ hb hbs (τ := 1 / 2)
      (fun z hz => re_le_of_evenCoeff_ne_zero hz) hu
    have h6 : N * Real.exp (1 / 2 * u) ≤ N * Real.exp (|V| / 2) :=
      mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by linarith [le_abs_self V])) hN0
    have h7 : 0 ≤ |A| * Real.exp (σ * u) := mul_nonneg (abs_nonneg _) (Real.exp_pos _).le
    linarith

/-- **No exponent beyond the rate.** Let `Z` be tempered with zeros in `Re ρ < 1` and `σ ≥ 0`. If
`Re W ≥ −C e^{σv}` on the tests `κ_w(t + v/2) − κ_w(t − v/2)` at every lag `v ≥ V`, then
`D(z) = 0` for every exponent with `Re z > σ`. -/
theorem evenCoeff_eq_zero_of_lag_ge_neg_exp (Z : ZeroConfig) (hZ : TemperedConfig Z)
    (hlt : ∀ ρ ∈ Z.carrier, ρ.re < 1) {w : ℝ} (hw : 0 < w) {σ C V : ℝ} (hσ : 0 ≤ σ)
    (hm : ∀ v : ℝ, V ≤ v → -(C * Real.exp (σ * v)) ≤
      (Z.W (twoBump (modScaledBump w 0) v (-1)) (twoBump (modScaledBump w 0) v (-1))).re)
    {z : ℂ} (hz : σ < z.re) : evenCoeff Z (modScaledBump w 0) z = 0 := by
  classical
  set b := modScaledBump w 0 with hbdef
  have hb : ContDiff ℝ 2 b := contDiff_modScaledBump_two w 0
  have hbs := modScaledBump_support hw 0
  obtain ⟨M, hM0, hMb⟩ := exists_two_re_lagStructure_le_exp Z hZ hb hbs hσ hm
  have hhalf : ∀ x : ℂ, evenCoeff Z b x ≠ 0 → x.re < 1 / 2 := fun x hx => by
    rcases mem_of_evenCoeff_ne_zero hx with h | h
    · have := hlt _ h; simp at this; linarith
    · have := hlt _ h; simp at this; linarith
  by_contra hne
  have hσh : σ < 1 / 2 := hz.trans (hhalf z hne)
  -- the real exponents beyond `σ`
  set R := (finite_evenCoeff_line Z b 0).toFinset.filter fun x => σ < x.re with hR
  have hmemR : ∀ x : ℂ, evenCoeff Z b x ≠ 0 → x.im = 0 → σ < x.re → x ∈ R := fun x hx him hre =>
    Finset.mem_filter.mpr ⟨(Set.Finite.mem_toFinset _).mpr ⟨hx, him⟩, hre⟩
  by_cases hRne : R.Nonempty
  · obtain ⟨x₀, hx₀R, hmax⟩ := R.exists_max_image Complex.re hRne
    obtain ⟨hx₀L, hx₀σ⟩ := Finset.mem_filter.mp hx₀R
    obtain ⟨hx₀, hx₀im⟩ := (Set.Finite.mem_toFinset _).mp hx₀L
    -- Landau above `δ* = Re x₀`
    have habove : ∀ y : ℂ, x₀.re < y.re → evenCoeff Z b y = 0 := fun y hy =>
      evenCoeff_eq_zero_of_two_re_lagStructure_le_exp Z hZ hb hbs (hσ.trans hx₀σ.le)
        (hhalf x₀ hx₀) (fun x hx him => by
          by_contra h
          push Not at h
          exact absurd (hmax x (hmemR x hx him (hx₀σ.trans h))) (not_le.mpr h))
        (fun u hu => (hMb u hu).trans (mul_le_mul_of_nonneg_left
          (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hx₀σ.le hu)) hM0)) hy
    -- after the shift by `e^{−σv}`, the positive coefficient at `δ*` contradicts the bound
    set ι : Set ℂ := {z | evenCoeff Z b z ≠ 0} with hι
    haveI : Countable ι := (countable_evenCoeff_support Z b).to_subtype
    have hD0 : Summable fun z : ℂ => ‖evenCoeff Z b z‖ := by
      have h0 := (two_re_lagStructure_eq Z hZ hb hbs 0).1.norm
      simp only [Complex.ofReal_zero, mul_zero, Complex.exp_zero, mul_one] at h0
      exact h0
    have hle : ∀ t : ι, ((t : ℂ) - σ).re ≤ x₀.re - σ := fun t => by
      by_contra h
      have : x₀.re < (t : ℂ).re := by simp at h; linarith
      exact t.2 (habove _ this)
    have hrep : ∀ v : ℝ, 0 ≤ v →
        (∑' t : ι, evenCoeff Z b t * cexp (((t : ℂ) - σ) * v)).re ≤ M := fun v hv => by
      have hsub : Function.support (fun z : ℂ => evenCoeff Z b z * cexp (z * v)) ⊆ ι :=
        fun z hz h0 => hz (show evenCoeff Z b z * cexp (z * v) = 0 by rw [h0, zero_mul])
      have e1 : ∑' t : ι, evenCoeff Z b t * cexp (((t : ℂ) - σ) * v) =
          ((Real.exp (-σ * v) * (2 * (lagStructure Z b v).re) : ℝ) : ℂ) := by
        rw [Complex.ofReal_mul, (two_re_lagStructure_eq Z hZ hb hbs v).2,
          ← tsum_subtype_eq_of_support_subset hsub, ← tsum_mul_left]
        refine tsum_congr fun t => ?_
        rw [Complex.ofReal_exp, mul_left_comm, ← Complex.exp_add]
        congr 2
        push_cast
        ring
      rw [e1, Complex.ofReal_re]
      calc Real.exp (-σ * v) * (2 * (lagStructure Z b v).re)
          ≤ Real.exp (-σ * v) * (M * Real.exp (σ * v)) :=
            mul_le_mul_of_nonneg_left (hMb v hv) (Real.exp_pos _).le
        _ = M := by
            rw [mul_left_comm, ← Real.exp_add, show -σ * v + σ * v = 0 by ring, Real.exp_zero,
              mul_one]
    have hpos := re_evenCoeff_modScaledBump_zero_pos Z hw
      ((mem_of_evenCoeff_ne_zero hx₀).elim id fun h => by
        rwa [show conj x₀ = x₀ from Complex.ext (by simp) (by simp [hx₀im])] at h) hx₀im
    have hnonpos := re_le_zero_of_re_tsum_exp_le (ι := ι) (lam := fun t => (t : ℂ) - σ)
      (q := fun t => evenCoeff Z b t) (hD0.subtype ι) (σ := x₀.re - σ) (by linarith) hle
      ⟨x₀, hx₀⟩ (Complex.ext (by simp) (by simp [hx₀im]))
      (fun t ht => Subtype.ext (sub_left_injective ht)) hrep
    exact absurd hnonpos (not_le.mpr hpos)
  · exact hne (evenCoeff_eq_zero_of_two_re_lagStructure_le_exp Z hZ hb hbs hσ hσh
      (fun x hx him => by
        by_contra h
        push Not at h
        exact hRne ⟨x, hmemR x hx him h⟩) hMb hz)

/-- A zero `ρ` with `h_w(γ_ρ) ≠ 0` leaves a nonzero merged coefficient at `ρ − ½`. -/
theorem evenCoeff_modScaledBump_zero_sub_half_ne_zero (Z : ZeroConfig) {w : ℝ} (hw : 0 < w)
    {ρ : ℂ} (hρ : ρ ∈ Z.carrier) (hg : paperFT (scaledBump w) (gammaOf ρ) ≠ 0) :
    evenCoeff Z (modScaledBump w 0) (ρ - 1 / 2) ≠ 0 := by
  rw [evenCoeff_modScaledBump_zero_eq Z hw, show (1 / 2 + (ρ - 1 / 2) : ℂ) = ρ by ring,
    show -(I * (ρ - 1 / 2)) = gammaOf ρ by rw [gammaOf, Complex.div_I]; ring,
    Set.indicator_of_mem hρ]
  refine mul_ne_zero (fun h1 => ?_) (pow_ne_zero 2 hg)
  have h2 := congrArg Complex.re h1
  have hm : (1 : ℝ) ≤ Z.mult ρ := by exact_mod_cast Z.one_le_mult _ hρ
  by_cases hc : (1 / 2 + conj (ρ - 1 / 2)) ∈ Z.carrier
  · rw [Set.indicator_of_mem hc, Complex.add_re, Complex.natCast_re, Complex.natCast_re,
      Complex.zero_re] at h2
    linarith [(Nat.cast_nonneg (Z.mult (1 / 2 + conj (ρ - 1 / 2))) : (0 : ℝ) ≤ _)]
  · rw [Set.indicator_of_notMem hc, Complex.add_re, Complex.natCast_re, Complex.zero_re] at h2
    linarith

/-! ### The abscissa -/

/-- **The lag family measures the abscissa.** Let `Z` be tempered with zeros in `Re ρ < 1`,
`w > 0` a width whose transform vanishes at no `γ_ρ` of an off-line zero, and `σ ≥ 0`. Every zero
has `Re ρ ≤ ½ + σ` iff `Re W ≥ −C e^{σv}` on the tests `κ_w(t + v/2) − κ_w(t − v/2)` for all
large `v`. -/
theorem re_le_iff_lag_twoBump_ge_neg_exp (Z : ZeroConfig) (hZ : TemperedConfig Z)
    (hlt : ∀ ρ ∈ Z.carrier, ρ.re < 1) {w : ℝ} (hw : 0 < w)
    (hgood : ∀ ρ ∈ Z.carrier, ρ.re ≠ 1 / 2 → paperFT (scaledBump w) (gammaOf ρ) ≠ 0) {σ : ℝ}
    (hσ : 0 ≤ σ) :
    (∀ ρ ∈ Z.carrier, ρ.re ≤ 1 / 2 + σ) ↔ ∃ C V : ℝ, ∀ v : ℝ, V ≤ v → -(C * Real.exp (σ * v)) ≤
      (Z.W (twoBump (modScaledBump w 0) v (-1)) (twoBump (modScaledBump w 0) v (-1))).re := by
  set b := modScaledBump w 0 with hbdef
  have hb : ContDiff ℝ 2 b := contDiff_modScaledBump_two w 0
  have hbs := modScaledBump_support hw 0
  constructor
  · intro hre
    set A := 2 * (lagStructure Z b 0).re with hA
    set N := ∑' z : ℂ, ‖evenCoeff Z b z‖ with hN
    refine ⟨|A| + N, 0, fun v hv => ?_⟩
    have h := two_re_lagStructure_le_mul_exp Z hZ hb hbs (τ := σ) (fun z hz => by
      rcases mem_of_evenCoeff_ne_zero hz with h | h
      · have := hre _ h; simp at this; linarith
      · have := hre _ h; simp at this; linarith) hv
    have he1 : 1 ≤ Real.exp (σ * v) := Real.one_le_exp (mul_nonneg hσ hv)
    have h1 : |A| ≤ |A| * Real.exp (σ * v) := le_mul_of_one_le_right (abs_nonneg _) he1
    rw [re_W_lag_eq Z hZ hb hbs, add_mul]
    linarith [neg_abs_le A]
  · rintro ⟨C, V, hm⟩ ρ hρ
    by_contra hre
    push Not at hre
    exact evenCoeff_modScaledBump_zero_sub_half_ne_zero Z hw hρ (hgood ρ hρ (by linarith))
      (evenCoeff_eq_zero_of_lag_ge_neg_exp Z hZ hlt hw hσ hm (by simp; linarith))

/-! ### Prime side -/

/-- **For `ζ`: each quasi-RH half-plane is one growth condition on the prime windows.** For all
but countably many widths `w ∈ (0, ½ log 2)` and every `σ ≥ 0`, every nontrivial zero of `ζ` has
`Re ρ ≤ ½ + σ` iff the window functional `P_v` of the autocorrelation of
`κ_w(t + v/2) − κ_w(t − v/2)` is `≥ −C e^{σv}` for all large `v`. -/
theorem zeta_re_le_iff_lag_primeWindow_ge_neg_exp :
    ∃ E : Set ℝ, E.Countable ∧ ∀ w : ℝ, 0 < w → 2 * w < Real.log 2 → w ∉ E → ∀ σ : ℝ, 0 ≤ σ →
      ((∀ ρ ∈ zetaZeroConfig.carrier, ρ.re ≤ 1 / 2 + σ) ↔ ∃ C V : ℝ, 0 ≤ V ∧ ∀ v : ℝ, V ≤ v →
        -(C * Real.exp (σ * v)) ≤ (lagPrimeWindowRHS v w (EF.weilTest
          (twoBump (modScaledBump w 0) v (-1)) (twoBump (modScaledBump w 0) v (-1)))).re) := by
  refine ⟨_, countable_bad_widths zetaZeroConfig, fun w hw hw2 hwE σ hσ => ?_⟩
  have hgood : ∀ ρ ∈ zetaZeroConfig.carrier, ρ.re ≠ 1 / 2 →
      paperFT (scaledBump w) (gammaOf ρ) ≠ 0 := fun ρ hρ hre h0 => hwE ⟨hw, ρ, hρ, hre, h0⟩
  have hlt : ∀ ρ ∈ zetaZeroConfig.carrier, ρ.re < 1 := fun ρ hρ => hρ.2.2
  have heq : ∀ v : ℝ, 0 ≤ v → (zetaZeroConfig.W (twoBump (modScaledBump w 0) v (-1))
      (twoBump (modScaledBump w 0) v (-1))).re = (lagPrimeWindowRHS v w (EF.weilTest
        (twoBump (modScaledBump w 0) v (-1)) (twoBump (modScaledBump w 0) v (-1)))).re :=
    fun v hv => by
      rw [zeta_W_eq_literatureRHS (f := twoBump (modScaledBump w 0) v (-1))
        (contDiff_bumpTest (contDiff_modScaledBump_two w 0) v ![1, -1])
        (hasCompactSupport_twoBump (hasCompactSupport_of_support_subset_abs
          (modScaledBump_support hw 0)) v (-1)),
        literatureRHS_twoBump_eq_lagPrimeWindowRHS (modScaledBump_support hw 0) hw2 hv]
  rw [re_le_iff_lag_twoBump_ge_neg_exp _ temperedConfig_zetaZeroConfig hlt hw hgood hσ]
  constructor
  · rintro ⟨C, V, h⟩
    exact ⟨C, max V 0, le_max_right _ _, fun v hv => by
      rw [← heq v ((le_max_right _ _).trans hv)]
      exact h v ((le_max_left _ _).trans hv)⟩
  · rintro ⟨C, V, hV, h⟩
    exact ⟨C, V, fun v hv => by rw [heq v (hV.trans hv)]; exact h v hv⟩

variable {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}

/-- **For Dirichlet `L`-functions: each quasi-GRH half-plane is one growth condition on the
twisted prime windows.** Let `χ` be primitive modulo `q > 1`. For all but countably many widths
`w ∈ (0, ½ log 2)` and every `σ ≥ 0`, every nontrivial zero of `L(s, χ)` has `Re ρ ≤ ½ + σ` iff
the twisted window functional of the autocorrelation of `κ_w(t + v/2) − κ_w(t − v/2)` is
`≥ −C e^{σv}` for all large `v`, real zeros included. -/
theorem dirichlet_re_le_iff_lag_primeWindow_ge_neg_exp (hq : 1 < q) (hprim : χ.IsPrimitive) :
    ∃ E : Set ℝ, E.Countable ∧ ∀ w : ℝ, 0 < w → 2 * w < Real.log 2 → w ∉ E → ∀ σ : ℝ, 0 ≤ σ →
      ((∀ ρ ∈ (ThmE.LZeros (ThmE.LSeam_of hq hprim)).carrier, ρ.re ≤ 1 / 2 + σ) ↔
        ∃ C V : ℝ, 0 ≤ V ∧ ∀ v : ℝ, V ≤ v → -(C * Real.exp (σ * v)) ≤
          (lagPrimeWindowRHSchi (ThmE.parity χ) q (ThmE.coeff χ) v w
            (EF.weilTest (twoBump (modScaledBump w 0) v (-1))
              (twoBump (modScaledBump w 0) v (-1)))).re) := by
  refine ⟨_, countable_bad_widths (ThmE.LZeros (ThmE.LSeam_of hq hprim)),
    fun w hw hw2 hwE σ hσ => ?_⟩
  have hgood : ∀ ρ ∈ (ThmE.LZeros (ThmE.LSeam_of hq hprim)).carrier, ρ.re ≠ 1 / 2 →
      paperFT (scaledBump w) (gammaOf ρ) ≠ 0 := fun ρ hρ hre h0 => hwE ⟨hw, ρ, hρ, hre, h0⟩
  have hlt : ∀ ρ ∈ (ThmE.LZeros (ThmE.LSeam_of hq hprim)).carrier, ρ.re < 1 := fun ρ hρ => by
    have h : 0 < ρ.re ∧ ρ.re < 1 := hρ.2
    exact h.2
  have heq : ∀ v : ℝ, 0 ≤ v → ((ThmE.LZeros (ThmE.LSeam_of hq hprim)).W
      (twoBump (modScaledBump w 0) v (-1)) (twoBump (modScaledBump w 0) v (-1))).re =
        (lagPrimeWindowRHSchi (ThmE.parity χ) q (ThmE.coeff χ) v w
          (EF.weilTest (twoBump (modScaledBump w 0) v (-1))
            (twoBump (modScaledBump w 0) v (-1)))).re := fun v hv => by
    have h := tsum_vonMangoldt_twoBump_eq_window (modScaledBump_support hw 0) hw2 hv
      (-1) (ThmE.coeff χ) fun n => starRingEnd ℂ (ThmE.coeff χ n)
    beta_reduce at h
    rw [LZeros_W_eq_literatureRHSchi hq hprim (f := twoBump (modScaledBump w 0) v (-1))
      (contDiff_bumpTest (contDiff_modScaledBump_two w 0) v ![1, -1])
      (hasCompactSupport_twoBump (hasCompactSupport_of_support_subset_abs
        (modScaledBump_support hw 0)) v (-1)), ThmE.literatureRHSchi, lagPrimeWindowRHSchi, h]
  rw [re_le_iff_lag_twoBump_ge_neg_exp _ (temperedConfig_LZeros hq hprim) hlt hw hgood hσ]
  constructor
  · rintro ⟨C, V, h⟩
    exact ⟨C, max V 0, le_max_right _ _, fun v hv => by
      rw [← heq v ((le_max_right _ _).trans hv)]
      exact h v ((le_max_left _ _).trans hv)⟩
  · rintro ⟨C, V, hV, h⟩
    exact ⟨C, V, fun v hv => by rw [heq v (hV.trans hv)]; exact h v hv⟩

end GaloisForLFunctions.SquareRootThreshold
