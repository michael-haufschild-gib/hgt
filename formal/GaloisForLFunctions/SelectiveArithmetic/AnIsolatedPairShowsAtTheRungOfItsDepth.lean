import GaloisForLFunctions.SquareRootThreshold.IsolatedOffLinePairVisibilityLaw

/-!
# An isolated pair shows at the rung of its depth

The second one-structure fake of the conductor ladder has the functional equation and no Euler
product: the doubled lattice of zeros on the line with the density of a conductor `q`,
`L = ½ log q`, and one reflected pair of depth `δ` (corpus: `isolatedPairConfig`). Its Weil form
at aperture `a ≤ L/2` is nonnegative exactly when `sinh(2δa)/δ ≤ 2L + 2a`.

On the ladder `a = κ log log q` this reads:

* **Below the rung of the depth** (`isolatedPair_nonneg_of_rung`): if `2δκ < 1`, then for
  `log q` large the configuration is Weil-nonnegative at every aperture `a ≤ κ log log q`.
* **Above the rung of the depth** (`isolatedPair_neg_of_rung`): if `2δκ > 1`, then for `log q`
  large it has a negative direction at every aperture `κ log log q ≤ a ≤ ¼ log q`.

* **Positivity on a rung forces companions** (`exists_companion_of_rung`,
  `zeta_companion_of_rung`): in every zero configuration with local count
  `N(t, t+1] ≤ A₀ log(|t| + 3)`, write `m = A₀ log(|γ₀| + 3)` for the mass at a zero
  `ρ₀ = ½ + δ + iγ₀`. If `2δκ > 1` and `log m` is large, Weil positivity at the aperture
  `κ log m` forces a second off-line zero within the ordinate distance `m^κ` of `ρ₀`. For `ζ` the
  mass is the height: positivity at aperture `κ log log |γ₀| + O(1)` excludes every isolated
  zero of depth `δ > 1/(2κ)` at the height `γ₀`.

So a pair of depth `δ` shows at the rung `κ = 1/(2δ)`: the rate at which a saving
`n^{1/2 + δ}` in the contacts pays for the sign on the prime side
(`exists_cancellation_margin`). For `δ = ½`, a pair at `0` and `1`, the rung is `κ = 1`: the
functional equation without the Euler product fails at the aperture `log log q`, where the Euler
product without the functional equation, the Liouville twist, fails too. Beyond the trivial
aperture a statement must use both structures.
-/

open Filter Topology Set
open Zeta23

noncomputable section

namespace GaloisForLFunctions.SelectiveArithmetic

open SquareRootThreshold

/-- For `c > 0`, eventually `B ≤ c log x` and `κ log x ≤ x/4`. -/
theorem eventually_log_budget {c : ℝ} (hc : 0 < c) (B κ : ℝ) :
    ∀ᶠ x : ℝ in atTop, B ≤ c * Real.log x ∧ κ * Real.log x ≤ x / 4 ∧ 1 ≤ x := by
  have h1 : ∀ᶠ x : ℝ in atTop, B / c ≤ Real.log x :=
    Real.tendsto_log_atTop.eventually_ge_atTop (B / c)
  have h2 : (fun x : ℝ => Real.log x) =o[atTop] (id : ℝ → ℝ) := Real.isLittleO_log_id_atTop
  have h3 := (h2.const_mul_left κ).def (by norm_num : (0 : ℝ) < 1 / 4)
  filter_upwards [h1, h3, eventually_ge_atTop (1 : ℝ)] with x hx1 hx3 hx
  refine ⟨?_, ?_, hx⟩
  · have := (div_le_iff₀ hc).mp hx1
    linarith
  · rw [Real.norm_eq_abs, id, Real.norm_eq_abs, abs_of_nonneg (by linarith : (0 : ℝ) ≤ x)]
      at hx3
    have := (le_abs_self _).trans hx3
    linarith

/-- **Below the rung of its depth an isolated pair is invisible.** If `2δκ < 1`, then for `x`
large the lattice of density `L = x/2` with one pair of depth `δ` is Weil-nonnegative at every
aperture `0 < a ≤ κ log x`. -/
theorem isolatedPair_nonneg_of_rung {δ κ : ℝ} (hδ : 0 < δ) (hδ' : δ ≤ 1 / 2)
    (hκ : 2 * δ * κ < 1) :
    ∃ M₀ : ℝ, ∀ (x : ℝ) (hx : 0 < x / 2), M₀ ≤ x → ∀ (γ₀ a : ℝ), 0 < a →
      a ≤ κ * Real.log x → ∀ f : ℝ → ℂ, ContDiff ℝ 2 f → tsupport f ⊆ Icc (-a) a →
        0 ≤ ((isolatedPairConfig hx hδ hδ' γ₀).W f f).re := by
  obtain ⟨M₀, hM₀⟩ := eventually_atTop.mp
    (eventually_log_budget (sub_pos.mpr hκ) (-Real.log (2 * δ)) κ)
  refine ⟨M₀, fun x hx hxM γ₀ a ha hak f hf hfs => ?_⟩
  obtain ⟨h1, h2, hx1⟩ := hM₀ x hxM
  have hx0 : 0 < x := by linarith
  have hlogx : 0 ≤ Real.log x := Real.log_nonneg hx1
  refine isolatedPairConfig_weil_nonneg_of_le_log hx hδ hδ' γ₀ ha (by linarith) ?_ f hf hfs
  -- `2δa ≤ 2δκ log x ≤ log(2δ) + log x = log(4δ · x/2)`
  have hlog : Real.log (4 * δ * (x / 2)) = Real.log (2 * δ) + Real.log x := by
    rw [show 4 * δ * (x / 2) = 2 * δ * x by ring,
      Real.log_mul (by positivity) hx0.ne']
  rw [hlog]
  have h3 : 2 * δ * a ≤ 2 * δ * (κ * Real.log x) :=
    mul_le_mul_of_nonneg_left hak (by positivity)
  nlinarith

/-- **Above the rung of its depth an isolated pair is visible.** If `2δκ > 1`, then for `x`
large the lattice of density `L = x/2` with one pair of depth `δ` has a negative direction at
every aperture `κ log x ≤ a ≤ x/4`. -/
theorem isolatedPair_neg_of_rung {δ κ : ℝ} (hδ : 0 < δ) (hδ' : δ ≤ 1 / 2)
    (hκ : 1 < 2 * δ * κ) :
    ∃ M₀ : ℝ, ∀ (x : ℝ) (hx : 0 < x / 2), M₀ ≤ x → ∀ (γ₀ a : ℝ), κ * Real.log x ≤ a →
      a ≤ x / 4 → ∃ f : ℝ → ℂ, ContDiff ℝ 2 f ∧ tsupport f ⊆ Icc (-a) a ∧
        ((isolatedPairConfig hx hδ hδ' γ₀).W f f).re < 0 := by
  obtain ⟨M₀, hM₀⟩ := eventually_atTop.mp
    (eventually_log_budget (sub_pos.mpr hκ) (Real.log 4) 0)
  refine ⟨max M₀ 2, fun x hx hxM γ₀ a hak hax => ?_⟩
  obtain ⟨h1, -, hx1⟩ := hM₀ x ((le_max_left _ _).trans hxM)
  have hx2 : 2 ≤ x := (le_max_right _ _).trans hxM
  have hx0 : 0 < x := by linarith
  have hlogx : 0 < Real.log x := Real.log_pos (by linarith)
  have hκ0 : 0 < κ := by
    by_contra h
    push Not at h
    nlinarith [mul_nonneg hδ.le (neg_nonneg.mpr h)]
  have ha : 0 < a := lt_of_lt_of_le (mul_pos hκ0 hlogx) hak
  refine exists_re_W_isolatedPairConfig_neg_of_log_le hx hδ hδ' γ₀ ha (by linarith) ?_
  -- `log(4δ(x/2 + a) + 2) ≤ log(4x) ≤ 2δκ log x ≤ 2δa`
  have hle : 4 * δ * (x / 2 + a) + 2 ≤ 4 * x := by nlinarith
  have hlog4 : Real.log (4 * x) = Real.log 4 + Real.log x :=
    Real.log_mul (by norm_num) hx0.ne'
  have h2 : Real.log (4 * δ * (x / 2 + a) + 2) ≤ Real.log 4 + Real.log x := by
    rw [← hlog4]
    exact Real.log_le_log (by positivity) hle
  have h3 : 2 * δ * (κ * Real.log x) ≤ 2 * δ * a :=
    mul_le_mul_of_nonneg_left hak (by positivity)
  nlinarith

/-! ### Positivity on a rung forces companions -/

/-- A polynomial of degree twelve is eventually below an exponential of any positive rate. -/
theorem eventually_pow_twelve_lt_exp (K : ℝ) {c : ℝ} (hc : 0 < c) :
    ∀ᶠ y : ℝ in atTop, K * y ^ 12 < Real.exp (c * y) := by
  have ht := (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 12).comp
    (tendsto_id.const_mul_atTop hc)
  have hpos : 0 < c ^ 12 / (|K| + 1) := by positivity
  filter_upwards [ht.eventually (Iio_mem_nhds hpos), eventually_ge_atTop (0 : ℝ)] with y hy hy0
  have hy' : (c * y) ^ 12 * Real.exp (-(c * y)) < c ^ 12 / (|K| + 1) := hy
  have hexp : 0 < Real.exp (c * y) := Real.exp_pos _
  have hc12 : 0 < c ^ 12 := by positivity
  have hK1 : 0 < |K| + 1 := by positivity
  have h1 : (c * y) ^ 12 < c ^ 12 / (|K| + 1) * Real.exp (c * y) := by
    have h := mul_lt_mul_of_pos_right hy' hexp
    rwa [mul_assoc, ← Real.exp_add, neg_add_cancel, Real.exp_zero, mul_one] at h
  have h2 : c ^ 12 * (y ^ 12 * (|K| + 1)) < c ^ 12 * Real.exp (c * y) := by
    have h := mul_lt_mul_of_pos_right h1 hK1
    have e : c ^ 12 / (|K| + 1) * Real.exp (c * y) * (|K| + 1) = c ^ 12 * Real.exp (c * y) := by
      field_simp
    rw [e, mul_pow] at h
    linarith
  have h3 : y ^ 12 * (|K| + 1) < Real.exp (c * y) := lt_of_mul_lt_mul_left h2 hc12.le
  calc K * y ^ 12 ≤ (|K| + 1) * y ^ 12 :=
        mul_le_mul_of_nonneg_right ((le_abs_self K).trans (by linarith)) (by positivity)
    _ = y ^ 12 * (|K| + 1) := by ring
    _ < Real.exp (c * y) := h3

/-- **Positivity on a rung forces companions.** Let `2δκ > 1`. There is `M₀` such that in every
zero configuration with local count `N(t, t+1] ≤ A₀ log(|t| + 3)`, for every zero
`ρ₀ = ½ + δ + iγ₀` with `log m ≥ M₀`, `m = A₀ log(|γ₀| + 3)`: if the Weil form is nonnegative on
the tests supported in `[−κ log m, κ log m]`, then another off-line zero, different from
`1 − ρ̄₀`, lies within the ordinate distance `e^{κ log m} = m^κ` of `ρ₀`. -/
theorem exists_companion_of_rung {δ κ : ℝ} (hδ : 0 < δ) (hκ : 1 < 2 * δ * κ) :
    ∃ M₀ : ℝ, ∀ (Z : ZeroConfig) {A₀ : ℝ}, 1 ≤ A₀ →
      (∀ t : ℝ, (Z.N t (t + 1) : ℝ) ≤ A₀ * Real.log (|t| + 3)) →
      ∀ {ρ₀ : ℂ}, ρ₀ ∈ Z.carrier → ρ₀.re = 1 / 2 + δ →
        M₀ ≤ Real.log (A₀ * Real.log (|ρ₀.im| + 3)) →
        (∀ f : ℝ → ℂ, ContDiff ℝ 2 f →
          tsupport f ⊆ Icc (-(κ * Real.log (A₀ * Real.log (|ρ₀.im| + 3))))
            (κ * Real.log (A₀ * Real.log (|ρ₀.im| + 3))) → 0 ≤ (Z.W f f).re) →
        ∃ ρ ∈ Z.carrier, ρ ≠ ρ₀ ∧ ρ ≠ reflect ρ₀ ∧
          |ρ.im - ρ₀.im| ≤ Real.exp (κ * Real.log (A₀ * Real.log (|ρ₀.im| + 3))) ∧
          ρ.re ≠ 1 / 2 := by
  have hκ0 : 0 < κ := by
    by_contra h
    push Not at h
    nlinarith [mul_nonneg hδ.le (neg_nonneg.mpr h)]
  obtain ⟨cδ, hcδ⟩ : ∃ cδ : ℝ, cδ = 2 * (21 + δ ^ 2 + 10 * δ) := ⟨_, rfl⟩
  have hcδ0 : 0 < cδ := by rw [hcδ]; positivity
  obtain ⟨y₁, hy₁⟩ := eventually_atTop.mp
    (eventually_pow_twelve_lt_exp (98304 * Real.exp (8 * δ) * cδ ^ 2 * κ ^ 12)
      (sub_pos.mpr hκ))
  refine ⟨max y₁ (max (4 / κ) ((1 / δ + 2) / κ)), fun Z A₀ hA₀ hloc ρ₀ hρ₀ hre hM hpos => ?_⟩
  obtain ⟨m, hm⟩ : ∃ m : ℝ, m = A₀ * Real.log (|ρ₀.im| + 3) := ⟨_, rfl⟩
  rw [← hm] at hM hpos ⊢
  have hlog3 : 1 ≤ Real.log (|ρ₀.im| + 3) := _root_.RHTower.one_le_log_abs_add_three _
  have hm0 : 0 < m := by rw [hm]; positivity
  obtain ⟨y, hy⟩ : ∃ y : ℝ, y = Real.log m := ⟨_, rfl⟩
  rw [← hy] at hM hpos ⊢
  have hmy : m = Real.exp y := by rw [hy, Real.exp_log hm0]
  have hy1 : y₁ ≤ y := (le_max_left _ _).trans hM
  have ha4 : 4 ≤ κ * y := by
    have h := (le_max_left _ _).trans ((le_max_right _ _).trans hM)
    have := (div_le_iff₀ hκ0).mp h
    linarith
  have haδ : 1 / δ + 2 ≤ κ * y := by
    have h := (le_max_right _ _).trans ((le_max_right _ _).trans hM)
    have := (div_le_iff₀ hκ0).mp h
    linarith
  obtain ⟨a, ha⟩ : ∃ a : ℝ, a = κ * y := ⟨_, rfl⟩
  rw [← ha] at ha4 haδ hpos ⊢
  have ha1 : 1 ≤ a := by linarith
  have ha0 : 0 < a := by linarith
  have hz1 : 1 ≤ δ * (a - 2) := by
    have h := mul_le_mul_of_nonneg_left (by linarith : 1 / δ ≤ a - 2) hδ.le
    rwa [mul_one_div_cancel hδ.ne'] at h
  -- the exponentials
  obtain ⟨E2, hE2⟩ : ∃ E2 : ℝ, E2 = Real.exp (2 * δ * a) := ⟨_, rfl⟩
  have hE20 : 0 < E2 := by rw [hE2]; exact Real.exp_pos _
  have h8 : Real.exp (8 * δ) * Real.exp (-(8 * δ)) = 1 := by
    rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
  -- the budget: `98304 e^{8δ} c² a¹² m < e^{2δa}`
  have hstar : 98304 * Real.exp (8 * δ) * (cδ ^ 2 * a ^ 12 * m) < E2 := by
    have h := mul_lt_mul_of_pos_right (hy₁ y hy1) hm0
    have e1 : Real.exp ((2 * δ * κ - 1) * y) * m = E2 := by
      rw [hmy, hE2, ← Real.exp_add, ha]
      congr 1
      ring
    rw [e1] at h
    rw [ha, mul_pow]
    linarith
  -- the size of the test
  have hcosh : Real.cosh (δ * a) ≤ Real.exp (δ * a) := by
    rw [Real.cosh_eq]
    have : Real.exp (-(δ * a)) ≤ Real.exp (δ * a) :=
      Real.exp_le_exp.mpr (by nlinarith [mul_pos hδ ha0])
    linarith
  have hpoly : a ^ 5 + δ ^ 2 * a ^ 5 + 10 * δ * a ^ 4 + 20 * a ^ 3 ≤
      (21 + δ ^ 2 + 10 * δ) * a ^ 5 := by
    have h4 : a ^ 4 ≤ a ^ 5 := pow_le_pow_right₀ ha1 (by norm_num)
    have h3 : a ^ 3 ≤ a ^ 5 := pow_le_pow_right₀ ha1 (by norm_num)
    nlinarith [mul_le_mul_of_nonneg_left h4 (by positivity : (0 : ℝ) ≤ 10 * δ)]
  have hNb0 : 0 ≤ 2 * a * Real.cosh (δ * a) *
      (a ^ 5 + δ ^ 2 * a ^ 5 + 10 * δ * a ^ 4 + 20 * a ^ 3) := by
    have := Real.cosh_pos (δ * a)
    positivity
  have hNb : 2 * a * Real.cosh (δ * a) *
      (a ^ 5 + δ ^ 2 * a ^ 5 + 10 * δ * a ^ 4 + 20 * a ^ 3) ≤
        cδ * a ^ 6 * Real.exp (δ * a) := by
    calc 2 * a * Real.cosh (δ * a) * (a ^ 5 + δ ^ 2 * a ^ 5 + 10 * δ * a ^ 4 + 20 * a ^ 3)
        ≤ 2 * a * Real.exp (δ * a) * ((21 + δ ^ 2 + 10 * δ) * a ^ 5) :=
          mul_le_mul (mul_le_mul_of_nonneg_left hcosh (by positivity)) hpoly (by positivity)
            (by positivity)
      _ = cδ * a ^ 6 * Real.exp (δ * a) := by rw [hcδ]; ring
  have hNbsq : (2 * a * Real.cosh (δ * a) *
      (a ^ 5 + δ ^ 2 * a ^ 5 + 10 * δ * a ^ 4 + 20 * a ^ 3)) ^ 2 ≤ cδ ^ 2 * a ^ 12 * E2 := by
    have h := pow_le_pow_left₀ hNb0 hNb 2
    have e : (cδ * a ^ 6 * Real.exp (δ * a)) ^ 2 = cδ ^ 2 * a ^ 12 * E2 := by
      rw [hE2, show 2 * δ * a = δ * a + δ * a by ring, Real.exp_add]
      ring
    rwa [e] at h
  have hfrac : 1 + Real.exp a / (1 + Real.exp a) ≤ 2 := by
    have : Real.exp a / (1 + Real.exp a) ≤ 1 :=
      (div_le_one (by positivity)).mpr (by linarith)
    linarith
  -- the pair energy of the test
  obtain ⟨Eh, hEh⟩ : ∃ Eh : ℝ, Eh = Real.exp (δ * (a - 2)) := ⟨_, rfl⟩
  have hEh0 : 0 < Eh := by rw [hEh]; exact Real.exp_pos _
  have hsinh : Eh / 4 ≤ Real.sinh (δ * (a - 2 * 1)) := by
    rw [mul_one, Real.sinh_eq, ← hEh]
    have h1 : Real.exp (-(δ * (a - 2))) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
    have h2 : 2 ≤ Eh := by
      rw [hEh]
      linarith [Real.add_one_le_exp (δ * (a - 2))]
    linarith
  have hrpow : (1 : ℝ) ≤ (1 * a) ^ (5 / 2 : ℝ) :=
    Real.one_le_rpow (by linarith) (by norm_num)
  have hPb : Eh ^ 2 / 16 ≤ 1 * (1 * a) ^ (5 / 2 : ℝ) * Real.sinh (δ * (a - 2 * 1)) ^ 2 := by
    have hs2 : (Eh / 4) ^ 2 ≤ Real.sinh (δ * (a - 2 * 1)) ^ 2 :=
      pow_le_pow_left₀ (by positivity) hsinh 2
    have h := mul_le_mul hrpow hs2 (by positivity) (by positivity)
    calc Eh ^ 2 / 16 = 1 * (Eh / 4) ^ 2 := by ring
      _ ≤ (1 * a) ^ (5 / 2 : ℝ) * Real.sinh (δ * (a - 2 * 1)) ^ 2 := h
      _ = 1 * (1 * a) ^ (5 / 2 : ℝ) * Real.sinh (δ * (a - 2 * 1)) ^ 2 := by ring
  have hEh4 : Eh ^ 4 = E2 ^ 2 * Real.exp (-(8 * δ)) := by
    rw [hEh, hE2, ← Real.exp_nat_mul, ← Real.exp_nat_mul, ← Real.exp_add]
    congr 1
    push_cast
    ring
  have hPbsq : E2 ^ 2 * Real.exp (-(8 * δ)) / 128 ≤
      2 * (1 * (1 * a) ^ (5 / 2 : ℝ) * Real.sinh (δ * (a - 2 * 1)) ^ 2) ^ 2 := by
    have h := pow_le_pow_left₀ (by positivity) hPb 2
    have e : (Eh ^ 2 / 16) ^ 2 = Eh ^ 4 / 256 := by ring
    rw [e, hEh4] at h
    linarith
  -- the size condition of the isolation inequality
  have hbig : 384 * A₀ * Real.log (|ρ₀.im| + 3) *
        (2 * a * Real.cosh (δ * a) *
          (a ^ 5 + δ ^ 2 * a ^ 5 + 10 * δ * a ^ 4 + 20 * a ^ 3)) ^ 2 *
        (1 + Real.exp a / (1 + Real.exp a)) <
      2 * (1 * (1 * a) ^ (5 / 2 : ℝ) * Real.sinh (δ * (a - 2 * 1)) ^ 2) ^ 2 := by
    have e0 : 384 * A₀ * Real.log (|ρ₀.im| + 3) = 384 * m := by rw [hm]; ring
    rw [e0]
    have hfrac0 : 0 ≤ 1 + Real.exp a / (1 + Real.exp a) := by positivity
    have hX0 : 0 ≤ cδ ^ 2 * a ^ 12 * m := by positivity
    have h1 : 384 * m * (2 * a * Real.cosh (δ * a) *
          (a ^ 5 + δ ^ 2 * a ^ 5 + 10 * δ * a ^ 4 + 20 * a ^ 3)) ^ 2 *
        (1 + Real.exp a / (1 + Real.exp a)) ≤ 384 * m * (cδ ^ 2 * a ^ 12 * E2) * 2 :=
      mul_le_mul (mul_le_mul_of_nonneg_left hNbsq (by positivity)) hfrac hfrac0 (by positivity)
    have h2 : 384 * m * (cδ ^ 2 * a ^ 12 * E2) * 2 =
        98304 * Real.exp (8 * δ) * (cδ ^ 2 * a ^ 12 * m) *
          (E2 * Real.exp (-(8 * δ)) / 128) := by
      linear_combination (-768 * (cδ ^ 2 * a ^ 12 * m) * E2) * h8
    have h3 : 98304 * Real.exp (8 * δ) * (cδ ^ 2 * a ^ 12 * m) *
          (E2 * Real.exp (-(8 * δ)) / 128) <
        E2 * (E2 * Real.exp (-(8 * δ)) / 128) :=
      mul_lt_mul_of_pos_right hstar (by positivity)
    have h4 : E2 * (E2 * Real.exp (-(8 * δ)) / 128) = E2 ^ 2 * Real.exp (-(8 * δ)) / 128 := by
      ring
    linarith
  exact _root_.RHTower.exists_offLine_companion_of_weil_positive Z hA₀ hloc hpos hρ₀ hδ hre
    (Real.exp_pos a).le zero_lt_one (by linarith) hbig

/-- **Weil positivity of `ζ` on a rung excludes the isolated zeros of its depth.** Let
`2δκ > 1`. There are `A₀ ≥ 1` and `M₀` such that for every zero `ρ₀ = ½ + δ + iγ₀` of `ζ` with
`log m ≥ M₀`, `m = A₀ log(|γ₀| + 3)`: if the Weil form of `ζ` is nonnegative on the tests
supported in `[−κ log m, κ log m]`, another off-line zero lies within `m^κ` of `ρ₀`. -/
theorem zeta_companion_of_rung {δ κ : ℝ} (hδ : 0 < δ) (hκ : 1 < 2 * δ * κ) :
    ∃ A₀ M₀ : ℝ, 1 ≤ A₀ ∧ ∀ ρ₀ ∈ zetaZeroConfig.carrier, ρ₀.re = 1 / 2 + δ →
      M₀ ≤ Real.log (A₀ * Real.log (|ρ₀.im| + 3)) →
      (∀ f : ℝ → ℂ, ContDiff ℝ 2 f →
        tsupport f ⊆ Icc (-(κ * Real.log (A₀ * Real.log (|ρ₀.im| + 3))))
          (κ * Real.log (A₀ * Real.log (|ρ₀.im| + 3))) → 0 ≤ (zetaZeroConfig.W f f).re) →
      ∃ ρ ∈ zetaZeroConfig.carrier, ρ ≠ ρ₀ ∧ ρ ≠ reflect ρ₀ ∧
        |ρ.im - ρ₀.im| ≤ Real.exp (κ * Real.log (A₀ * Real.log (|ρ₀.im| + 3))) ∧
        ρ.re ≠ 1 / 2 := by
  obtain ⟨M₀, hM₀⟩ := exists_companion_of_rung hδ hκ
  obtain ⟨A₀, hA₀, hloc⟩ := Zeta23.RvM.zetaZeroConfig_local_count
  exact ⟨A₀, M₀, hA₀, fun ρ₀ hρ₀ hre hM hpos =>
    hM₀ zetaZeroConfig hA₀ hloc hρ₀ hre hM hpos⟩

end GaloisForLFunctions.SelectiveArithmetic
