import GaloisForLFunctions.ArithmeticOfSquareRootPrecision.TheIntegralityLatticeOfTheHorizon
import GaloisForLFunctions.ArithmeticOfSquareRootPrecision.TheDecidingInputTheorem

/-!
# The integrality exponent is the zero width

Integrality over `ℤ` has two halves at a scale `φ`:

* the **Siegel half** (`SiegelHalf φ`): for all large `n` some integer polynomial of degree `≤ n`
  has Nair integral in `(0, e^{−(n+1) + C φ(n+1)}]` (existence of small auxiliaries);
* the **Liouville half** (`LiouvilleHalf φ`): for all large `n` every positive Nair integral in
  degree `≤ n` is at least `e^{−(n+1) − C φ(n+1)}` (every nonzero value is large).

Because the integrality floor is attained (`isLeast_positive_nairIntegral`), the halves are exactly
the two halves of the count at scale `φ` (`siegelHalf_iff`, `liouvilleHalf_iff`):
`ψ(N) ≥ N − C φ(N)` and `ψ(N) ≤ N + C φ(N)` at integer horizons, and for a monotone scale at all real
`x` (`siegelHalf_iff_lower`, `liouvilleHalf_iff_upper`).

* **Square-root integrality is RH, in each half** (`riemannHypothesis_iff_siegelHalf_sqrtScale`,
  `riemannHypothesis_iff_liouvilleHalf_sqrtScale`).
* **The integrality exponent is `Θ`**: at a power scale `x^θ` both halves hold for `θ > Θ` and both fail
  for `θ < Θ` (`integrality_halves_of_zeroReSup_lt`, `not_siegelHalf_rpow_of_lt_zeroReSup`,
  `not_liouvilleHalf_rpow_of_lt_zeroReSup`); hence `inf {θ : SiegelHalf x^θ} = Θ`, and likewise for
  the Liouville half (`siegelExponent_eq_zeroReSup`, `liouvilleExponent_eq_zeroReSup`).
* **A zero-free strip is integrality at a fixed precision** (`zeroReSup_lt_one_iff_siegelHalf`):
  `Θ < 1` iff the Siegel half holds at some power `θ < 1`.

So the limit of integrality over `ℤ` is not linear: the precision that integer auxiliaries on
`[0, 1]` reach is exactly the zero width, in each half separately. What is open is not the
integrality step but a *certificate* (a ceiling) for a small positive integral.
-/

noncomputable section

open Filter Asymptotics Real Polynomial RHTower Topology

namespace GaloisForLFunctions.ArithmeticOfSquareRootPrecision

/-- The **Siegel half** of integrality at scale `φ`. -/
def SiegelHalf (φ : ℝ → ℝ) : Prop :=
  ∃ C : ℝ, ∀ᶠ n : ℕ in atTop, ∃ P : ℤ[X], P.natDegree ≤ n ∧ 0 < nairIntegral P ∧
    nairIntegral P ≤ exp (-((n + 1 : ℕ) : ℝ) + C * φ (n + 1 : ℕ))

/-- The **Liouville half** of integrality at scale `φ`. -/
def LiouvilleHalf (φ : ℝ → ℝ) : Prop :=
  ∃ C : ℝ, ∀ᶠ n : ℕ in atTop, ∀ P : ℤ[X], P.natDegree ≤ n → 0 < nairIntegral P →
    exp (-((n + 1 : ℕ) : ℝ) - C * φ (n + 1 : ℕ)) ≤ nairIntegral P

/-- `1/lcm(1, …, N) = e^{−ψ(N)}`. -/
theorem one_div_lcmUpto_eq_exp (N : ℕ) :
    1 / (Nat.lcmUpto N : ℕ) = exp (-Chebyshev.psi N) := by
  rw [Chebyshev.psi_eq_log_lcmUpto, Real.exp_neg, Real.exp_log (by exact_mod_cast Nat.lcmUpto_pos N),
    one_div]

/-- **The Siegel half is the lower half of the count at integer horizons.** -/
theorem siegelHalf_iff (φ : ℝ → ℝ) : SiegelHalf φ ↔
    ∃ C : ℝ, ∀ᶠ n : ℕ in atTop,
      ((n + 1 : ℕ) : ℝ) - C * φ (n + 1 : ℕ) ≤ Chebyshev.psi (n + 1 : ℕ) := by
  constructor
  · rintro ⟨C, hC⟩
    refine ⟨C, hC.mono fun n ⟨P, hP, hpos, hle⟩ => ?_⟩
    have h1 := (isLeast_positive_nairIntegral n).2 ⟨P, hP, rfl, hpos⟩
    rw [one_div_lcmUpto_eq_exp] at h1
    have := Real.exp_le_exp.mp (h1.trans hle)
    linarith
  · rintro ⟨C, hC⟩
    refine ⟨C, hC.mono fun n hn => ?_⟩
    obtain ⟨P, hP, hP1⟩ := exists_nairIntegral_eq_inv_lcmUpto n
    refine ⟨P, hP, by rw [hP1]; exact one_div_pos.mpr (by exact_mod_cast Nat.lcmUpto_pos _), ?_⟩
    rw [hP1, one_div_lcmUpto_eq_exp]
    exact Real.exp_le_exp.mpr (by linarith)

/-- **The Liouville half is the upper half of the count at integer horizons.** -/
theorem liouvilleHalf_iff (φ : ℝ → ℝ) : LiouvilleHalf φ ↔
    ∃ C : ℝ, ∀ᶠ n : ℕ in atTop,
      Chebyshev.psi (n + 1 : ℕ) ≤ ((n + 1 : ℕ) : ℝ) + C * φ (n + 1 : ℕ) := by
  constructor
  · rintro ⟨C, hC⟩
    refine ⟨C, hC.mono fun n hn => ?_⟩
    obtain ⟨P, hP, hP1⟩ := exists_nairIntegral_eq_inv_lcmUpto n
    have h := hn P hP (by rw [hP1]; exact one_div_pos.mpr (by exact_mod_cast Nat.lcmUpto_pos _))
    rw [hP1, one_div_lcmUpto_eq_exp] at h
    have := Real.exp_le_exp.mp h
    linarith
  · rintro ⟨C, hC⟩
    refine ⟨C, hC.mono fun n hn P hP hpos => ?_⟩
    have h1 := (isLeast_positive_nairIntegral n).2 ⟨P, hP, rfl, hpos⟩
    rw [one_div_lcmUpto_eq_exp] at h1
    exact (Real.exp_le_exp.mpr (by linarith)).trans h1

/-! ### From integer horizons to real `x` -/

theorem tendsto_succ_cast_atTop : Tendsto (fun n : ℕ => ((n + 1 : ℕ) : ℝ)) atTop atTop :=
  tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1)

/-- A scale is **admissible** if it is monotone and nonnegative on `[1, ∞)` and eventually `≥ 1`. -/
structure AdmissibleScale (φ : ℝ → ℝ) : Prop where
  mono : ∀ x y : ℝ, 1 ≤ x → x ≤ y → φ x ≤ φ y
  nonneg : ∀ x : ℝ, 1 ≤ x → 0 ≤ φ x
  eventually_one_le : ∀ᶠ x in atTop, 1 ≤ φ x

theorem admissibleScale_sqrtScale : AdmissibleScale sqrtScale where
  mono x y hx hxy := by
    unfold sqrtScale
    have hl0 : 0 ≤ Real.log x := Real.log_nonneg hx
    exact mul_le_mul (Real.sqrt_le_sqrt hxy)
      (pow_le_pow_left₀ hl0 (Real.log_le_log (by linarith) hxy) 2) (by positivity)
      (Real.sqrt_nonneg y)
  nonneg x _ := sqrtScale_nonneg x
  eventually_one_le := (eventually_ge_atTop (exp 1)).mono fun _ hx => one_le_sqrtScale hx

theorem admissibleScale_rpow {θ : ℝ} (hθ : 0 ≤ θ) : AdmissibleScale fun x => x ^ θ where
  mono x y hx hxy := Real.rpow_le_rpow (by linarith) hxy hθ
  nonneg x hx := Real.rpow_nonneg (by linarith) θ
  eventually_one_le := (eventually_ge_atTop (1 : ℝ)).mono fun _ hx => Real.one_le_rpow hx hθ

/-- Lower bounds at integer horizons extend to real `x`. -/
theorem lower_real_of_nat {φ : ℝ → ℝ} (hφ : AdmissibleScale φ)
    (h : ∃ C : ℝ, ∀ᶠ n : ℕ in atTop,
      ((n + 1 : ℕ) : ℝ) - C * φ (n + 1 : ℕ) ≤ Chebyshev.psi (n + 1 : ℕ)) :
    ∃ C : ℝ, ∀ᶠ x : ℝ in atTop, -(C * φ x) ≤ Chebyshev.psi x - x := by
  obtain ⟨C, hC⟩ := h
  obtain ⟨N, hN⟩ := eventually_atTop.mp hC
  refine ⟨max C 0 + 1, ?_⟩
  filter_upwards [hφ.eventually_one_le, eventually_ge_atTop ((N : ℝ) + 1)] with x hx1 hxN
  have hx0 : 0 ≤ x := by linarith [(Nat.cast_nonneg N : (0 : ℝ) ≤ N)]
  have hm : N + 1 ≤ ⌊x⌋₊ := Nat.le_floor (by push_cast; linarith)
  obtain ⟨n, hn⟩ : ∃ n, ⌊x⌋₊ = n + 1 := ⟨⌊x⌋₊ - 1, by omega⟩
  have h1 := hN n (by omega)
  have hψ : Chebyshev.psi x = Chebyshev.psi (n + 1 : ℕ) := by
    rw [Chebyshev.psi_eq_psi_coe_floor x, hn]
  have hxm : ((n + 1 : ℕ) : ℝ) ≤ x := by rw [← hn]; exact Nat.floor_le hx0
  have hxm' : x < ((n + 1 : ℕ) : ℝ) + 1 := by rw [← hn]; exact Nat.lt_floor_add_one x
  have hm1 : (1 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by push_cast; linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
  have hφm := hφ.mono _ _ hm1 hxm
  have hφm0 := hφ.nonneg _ hm1
  have hCm : C * φ (n + 1 : ℕ) ≤ max C 0 * φ x :=
    (mul_le_mul_of_nonneg_right (le_max_left C 0) hφm0).trans
      (mul_le_mul_of_nonneg_left hφm (le_max_right C 0))
  rw [hψ]
  nlinarith

/-- Upper bounds at integer horizons extend to real `x`. -/
theorem upper_real_of_nat {φ : ℝ → ℝ} (hφ : AdmissibleScale φ)
    (h : ∃ C : ℝ, ∀ᶠ n : ℕ in atTop,
      Chebyshev.psi (n + 1 : ℕ) ≤ ((n + 1 : ℕ) : ℝ) + C * φ (n + 1 : ℕ)) :
    ∃ C : ℝ, ∀ᶠ x : ℝ in atTop, Chebyshev.psi x - x ≤ C * φ x := by
  obtain ⟨C, hC⟩ := h
  obtain ⟨N, hN⟩ := eventually_atTop.mp hC
  refine ⟨max C 0, ?_⟩
  filter_upwards [eventually_ge_atTop ((N : ℝ) + 1)] with x hxN
  have hx0 : 0 ≤ x := by linarith [(Nat.cast_nonneg N : (0 : ℝ) ≤ N)]
  have hm : N + 1 ≤ ⌊x⌋₊ := Nat.le_floor (by push_cast; linarith)
  obtain ⟨n, hn⟩ : ∃ n, ⌊x⌋₊ = n + 1 := ⟨⌊x⌋₊ - 1, by omega⟩
  have h1 := hN n (by omega)
  have hψ : Chebyshev.psi x = Chebyshev.psi (n + 1 : ℕ) := by
    rw [Chebyshev.psi_eq_psi_coe_floor x, hn]
  have hxm : ((n + 1 : ℕ) : ℝ) ≤ x := by rw [← hn]; exact Nat.floor_le hx0
  have hm1 : (1 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by push_cast; linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
  have hCm : C * φ (n + 1 : ℕ) ≤ max C 0 * φ x :=
    (mul_le_mul_of_nonneg_right (le_max_left C 0) (hφ.nonneg _ hm1)).trans
      (mul_le_mul_of_nonneg_left (hφ.mono _ _ hm1 hxm) (le_max_right C 0))
  rw [hψ]
  linarith

/-- **The Siegel half is the lower half of the count** at an admissible scale. -/
theorem siegelHalf_iff_lower {φ : ℝ → ℝ} (hφ : AdmissibleScale φ) :
    SiegelHalf φ ↔ ∃ C : ℝ, ∀ᶠ x : ℝ in atTop, -(C * φ x) ≤ Chebyshev.psi x - x := by
  rw [siegelHalf_iff]
  refine ⟨lower_real_of_nat hφ, fun ⟨C, hC⟩ => ⟨C, (tendsto_succ_cast_atTop.eventually hC).mono
    fun n hn => by linarith⟩⟩

/-- **The Liouville half is the upper half of the count** at an admissible scale. -/
theorem liouvilleHalf_iff_upper {φ : ℝ → ℝ} (hφ : AdmissibleScale φ) :
    LiouvilleHalf φ ↔ ∃ C : ℝ, ∀ᶠ x : ℝ in atTop, Chebyshev.psi x - x ≤ C * φ x := by
  rw [liouvilleHalf_iff]
  refine ⟨upper_real_of_nat hφ, fun ⟨C, hC⟩ => ⟨C, (tendsto_succ_cast_atTop.eventually hC).mono
    fun n hn => by linarith⟩⟩

/-! ### Square-root integrality -/

/-- **Square-root precise Siegel auxiliaries exist iff RH.** -/
theorem riemannHypothesis_iff_siegelHalf_sqrtScale : RiemannHypothesis ↔ SiegelHalf sqrtScale := by
  rw [siegelHalf_iff_lower admissibleScale_sqrtScale, ← lowerCount_vonMangoldt_iff]
  rfl

/-- **Every positive Nair integral is square-root large iff RH.** -/
theorem riemannHypothesis_iff_liouvilleHalf_sqrtScale :
    RiemannHypothesis ↔ LiouvilleHalf sqrtScale := by
  rw [liouvilleHalf_iff_upper admissibleScale_sqrtScale, ← upperCount_vonMangoldt_iff]
  rfl

/-! ### The integrality exponent -/

/-- **Above the zero width both halves hold.** -/
theorem integrality_halves_of_zeroReSup_lt {θ : ℝ} (hθ : zeroReSup < θ) :
    SiegelHalf (fun x => x ^ θ) ∧ LiouvilleHalf (fun x => x ^ θ) := by
  obtain ⟨C, -, hC⟩ := exists_abs_chebyshevPsi_sub_le_rpow hθ
  have hev : ∀ᶠ n : ℕ in atTop, |Chebyshev.psi (n + 1 : ℕ) - ((n + 1 : ℕ) : ℝ)| ≤
      C * ((n + 1 : ℕ) : ℝ) ^ θ :=
    Eventually.of_forall fun n => hC _ (by push_cast; linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)])
  exact ⟨(siegelHalf_iff _).mpr ⟨C, hev.mono fun n hn => by linarith [(abs_le.mp hn).1]⟩,
    (liouvilleHalf_iff _).mpr ⟨C, hev.mono fun n hn => by linarith [(abs_le.mp hn).2]⟩⟩

/-- Raising the exponent weakens both halves. -/
theorem siegelHalf_rpow_mono {θ θ' : ℝ} (hθ : θ ≤ θ') (h : SiegelHalf fun x => x ^ θ) :
    SiegelHalf fun x => x ^ θ' := by
  rw [siegelHalf_iff] at h ⊢
  obtain ⟨C, hC⟩ := h
  refine ⟨max C 0, hC.mono fun n hn => ?_⟩
  have h1 : (1 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by push_cast; linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
  have := (mul_le_mul_of_nonneg_right (le_max_left C 0) (Real.rpow_nonneg (by linarith) θ)).trans
    (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le h1 hθ) (le_max_right C 0))
  linarith

theorem liouvilleHalf_rpow_mono {θ θ' : ℝ} (hθ : θ ≤ θ') (h : LiouvilleHalf fun x => x ^ θ) :
    LiouvilleHalf fun x => x ^ θ' := by
  rw [liouvilleHalf_iff] at h ⊢
  obtain ⟨C, hC⟩ := h
  refine ⟨max C 0, hC.mono fun n hn => ?_⟩
  have h1 : (1 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by push_cast; linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
  have := (mul_le_mul_of_nonneg_right (le_max_left C 0) (Real.rpow_nonneg (by linarith) θ)).trans
    (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le h1 hθ) (le_max_right C 0))
  linarith

/-- `C x^θ < x^b` eventually for `θ < b`. -/
theorem eventually_mul_rpow_lt_rpow {θ b : ℝ} (hθb : θ < b) (C : ℝ) :
    ∀ᶠ x : ℝ in atTop, C * x ^ θ < x ^ b := by
  have ho := ((rpow_isLittleO_rpow hθb).const_mul_left C).def one_half_pos
  filter_upwards [ho, eventually_gt_atTop (0 : ℝ)] with x h1 hx
  have hxb : 0 < x ^ b := Real.rpow_pos_of_pos hx b
  rw [Real.norm_eq_abs, Real.norm_of_nonneg hxb.le] at h1
  linarith [le_abs_self (C * x ^ θ)]

/-- **Below the zero width the Siegel half fails.** -/
theorem not_siegelHalf_rpow_of_lt_zeroReSup {θ : ℝ} (hθ : θ < zeroReSup) :
    ¬ SiegelHalf fun x => x ^ θ := by
  intro h
  have hΘ := half_le_zeroReSup
  set θ₀ := max θ 0
  have hθ₀ : θ₀ < zeroReSup := max_lt hθ (by linarith)
  obtain ⟨C, hC⟩ := (siegelHalf_iff_lower (admissibleScale_rpow (le_max_right θ 0))).mp
    (siegelHalf_rpow_mono (le_max_left θ 0) h)
  obtain ⟨x, ⟨h1, h2⟩, h3⟩ := ((hC.and (eventually_mul_rpow_lt_rpow (θ := max θ 0)
    (b := (θ₀ + zeroReSup) / 2) (by linarith) C)).and_frequently
    (frequently_chebyshevPsi_sub_lt_neg_rpow (b := (θ₀ + zeroReSup) / 2) (by linarith))).exists
  linarith

/-- **Below the zero width the Liouville half fails.** -/
theorem not_liouvilleHalf_rpow_of_lt_zeroReSup {θ : ℝ} (hθ : θ < zeroReSup) :
    ¬ LiouvilleHalf fun x => x ^ θ := by
  intro h
  have hΘ := half_le_zeroReSup
  set θ₀ := max θ 0
  have hθ₀ : θ₀ < zeroReSup := max_lt hθ (by linarith)
  obtain ⟨C, hC⟩ := (liouvilleHalf_iff_upper (admissibleScale_rpow (le_max_right θ 0))).mp
    (liouvilleHalf_rpow_mono (le_max_left θ 0) h)
  obtain ⟨x, ⟨h1, h2⟩, h3⟩ := ((hC.and (eventually_mul_rpow_lt_rpow (θ := max θ 0)
    (b := (θ₀ + zeroReSup) / 2) (by linarith) C)).and_frequently
    (frequently_rpow_lt_chebyshevPsi_sub (b := (θ₀ + zeroReSup) / 2) (by linarith))).exists
  linarith

/-- The exponent set of a half is `[Θ, ∞)` up to its endpoint. -/
theorem exponent_eq_zeroReSup {S : Set ℝ} (hgt : ∀ θ, zeroReSup < θ → θ ∈ S)
    (hlt : ∀ θ, θ < zeroReSup → θ ∉ S) : sInf S = zeroReSup :=
  csInf_eq_of_forall_ge_of_forall_gt_exists_lt ⟨zeroReSup + 1, hgt _ (by linarith)⟩
    (fun θ hθ => not_lt.mp fun h => hlt θ h hθ)
    (fun w hw => ⟨(zeroReSup + w) / 2, hgt _ (by linarith), by linarith⟩)

/-- **The Siegel exponent is the zero width.** -/
theorem siegelExponent_eq_zeroReSup :
    sInf {θ : ℝ | SiegelHalf fun x => x ^ θ} = zeroReSup :=
  exponent_eq_zeroReSup (fun _ h => (integrality_halves_of_zeroReSup_lt h).1)
    (fun _ h => not_siegelHalf_rpow_of_lt_zeroReSup h)

/-- **The Liouville exponent is the zero width.** -/
theorem liouvilleExponent_eq_zeroReSup :
    sInf {θ : ℝ | LiouvilleHalf fun x => x ^ θ} = zeroReSup :=
  exponent_eq_zeroReSup (fun _ h => (integrality_halves_of_zeroReSup_lt h).2)
    (fun _ h => not_liouvilleHalf_rpow_of_lt_zeroReSup h)

/-- **A zero-free strip is integrality at a fixed precision**: `Θ < 1` iff the Siegel half holds at
some power `θ < 1`. -/
theorem zeroReSup_lt_one_iff_siegelHalf :
    zeroReSup < 1 ↔ ∃ θ : ℝ, θ < 1 ∧ SiegelHalf fun x => x ^ θ := by
  refine ⟨fun h => ⟨(zeroReSup + 1) / 2, by linarith,
    (integrality_halves_of_zeroReSup_lt (by linarith)).1⟩, fun ⟨θ, hθ1, hθ⟩ => ?_⟩
  by_contra hge
  exact not_siegelHalf_rpow_of_lt_zeroReSup (lt_of_lt_of_le hθ1 (not_lt.mp hge)) hθ

/-- The same for the Liouville half. -/
theorem zeroReSup_lt_one_iff_liouvilleHalf :
    zeroReSup < 1 ↔ ∃ θ : ℝ, θ < 1 ∧ LiouvilleHalf fun x => x ^ θ := by
  refine ⟨fun h => ⟨(zeroReSup + 1) / 2, by linarith,
    (integrality_halves_of_zeroReSup_lt (by linarith)).2⟩, fun ⟨θ, hθ1, hθ⟩ => ?_⟩
  by_contra hge
  exact not_liouvilleHalf_rpow_of_lt_zeroReSup (lt_of_lt_of_le hθ1 (not_lt.mp hge)) hθ

end GaloisForLFunctions.ArithmeticOfSquareRootPrecision
