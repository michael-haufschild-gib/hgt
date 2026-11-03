import GaloisForLFunctions.RenormalizedIntersectionTheory.MayerScattering.WindowWeilCorePackets

/-!
# The Hecke-equivariant completion of the window tower

The **completed resonant space** is `𝒦 = ℓ²(upper Mayer resonances)` with the Krein form
`[x, y] = Σ_s x_s conj(y_{s♯})`, `s♯ = ½ − s̄` (`completedKreinForm`); `[x, y] = ⟨Jy, x⟩` for the
unitary involution `J` (`resonantReflection`), so `𝒦` is a Krein space with fundamental symmetry `J`.

* **PM's core space is dense in it** (`coreEmbedding`, `completedKreinForm_coreEmbedding`,
  `denseRange_coreEmbedding`): the coefficient map of the actual scattering-core basis
  `b_s = mayerPeriodCore s` is a dense embedding carrying PM's Krein form to `[·, ·]`; each core is a
  basis vector.
* **The window map** (`windowResonanceMap`): `𝓦_A H = (√m_{2s} Φ_H(s, 1))_s`, the normalized PM
  period of the test at `a = 1` — the coefficient of the boundary-corrected core. It is real-linear and
  **bounded** (`norm_windowResonanceMap_le`): `‖𝓦_A H‖ ≤ 2√5 e^{A/2} √T (‖H‖₁ + ‖H''‖₁)`, `T` the
  tempered zero sum.
* **Exact Krein identity** (`weilQuad_eq_completedKreinForm`): `Q(H) = 2 Re [𝓦_A H, 𝓦_A H]` — an
  identity, not a limit; the finite core packets are the truncations of `𝓦_A H`
  (`coreEmbedding_windowWeilCorePacket`).
* **Hecke** (`windowResonanceMap_heckePull`): for every integer `p ≥ 1` the Mellin translation
  `F_pH = √p H(· + log p)`, which maps stage `A` into stage `A + log p`, acts on `𝒦` by the multiplier
  `(D_p x)_s = p^{1−2s} x_s`; `‖D_p‖ ≤ p` and `[D_p x, D_p y] = p[x, y]`
  (`norm_heckeMultiplier_le`, `completedKreinForm_heckeMultiplier`). At `p = 2` the multiplier is the
  source Hecke operator minus the identity on the completed periods (`lewisHeckeT2_sub_eq_pull`).
* **Reflection** (`windowResonanceMap_windowInvolution`): `𝓦(σ_A H)_s = e^{−A(2s−½)} conj(𝓦 H_{s♯})`:
  window reflection is the conjugate-linear, exponentially twisted Krein reflection.
-/

noncomputable section

open Complex Set Filter Topology Zeta23 MeasureTheory
open scoped ComplexConjugate lp
open GaloisForLFunctions
open CohomologyOfWindowsOfSpecZ ArithmeticCastelnuovoSeveri SpacingScaleHarmonicAnalysis
open ArithmeticPolarization WindowTowerOfSpecZ

namespace GaloisForLFunctions.RenormalizedIntersectionTheory.MayerScattering

/-! ### The completed resonant space -/

/-- The **completed resonant space**: square-summable coefficients on the upper resonances. -/
abbrev ResonantSpace := ℓ²(upperMayerResonances, ℂ)

theorem memℓp_comp_reflect (x : ResonantSpace) :
    Memℓp (fun s => x (reflectUpperResonance s)) 2 := by
  refine (memℓp_gen_iff (by norm_num)).mpr ?_
  exact reflectUpperResonance.summable_iff.mpr ((lp.memℓp x).summable (by norm_num))

/-- The reflection `s ↦ s♯` on coefficients. -/
def resonantReflection (x : ResonantSpace) : ResonantSpace :=
  ⟨fun s => x (reflectUpperResonance s), memℓp_comp_reflect x⟩

theorem resonantReflection_apply (x : ResonantSpace) (s : upperMayerResonances) :
    resonantReflection x s = x (reflectUpperResonance s) := rfl

/-- The **completed Krein form** `[x, y] = Σ_s x_s conj(y_{s♯})`. -/
def completedKreinForm (x y : ResonantSpace) : ℂ :=
  ∑' s, x s * conj (y (reflectUpperResonance s))

/-- `[x, y] = ⟨J y, x⟩`. -/
theorem completedKreinForm_eq_inner (x y : ResonantSpace) :
    completedKreinForm x y = inner ℂ (resonantReflection y) x := by
  rw [lp.inner_eq_tsum, completedKreinForm]
  refine tsum_congr fun s => ?_
  rw [RCLike.inner_apply', resonantReflection_apply, mul_comm]

/-! ### PM's core space -/

theorem memℓp_repr (v : mayerPeriodKreinSpace) :
    Memℓp (fun s => mayerPeriodBasis.repr v s) 2 :=
  memℓp_gen_iff (by norm_num) |>.mpr (summable_of_ne_finset_zero (s := (mayerPeriodBasis.repr v).support)
    fun s hs => by rw [Finsupp.notMem_support_iff.mp hs, norm_zero, Real.zero_rpow (by norm_num)])

/-- The coefficient embedding of PM's core space. -/
def coreEmbedding : mayerPeriodKreinSpace →ₗ[ℂ] ResonantSpace where
  toFun v := ⟨fun s => mayerPeriodBasis.repr v s, memℓp_repr v⟩
  map_add' u v := by ext s; simp
  map_smul' c v := by ext s; simp

theorem coreEmbedding_apply (v : mayerPeriodKreinSpace) (s : upperMayerResonances) :
    coreEmbedding v s = mayerPeriodBasis.repr v s := rfl

/-- **PM's Krein form is the completed Krein form on core vectors.** -/
theorem completedKreinForm_coreEmbedding (u v : mayerPeriodKreinSpace) :
    completedKreinForm (coreEmbedding u) (coreEmbedding v) = mayerKreinForm u v := by
  classical
  rw [mayerKreinForm, mayerKreinPosInner_eq_sum_of_subset (S := (mayerPeriodBasis.repr u).support)
    subset_rfl, completedKreinForm]
  rw [tsum_eq_sum (s := (mayerPeriodBasis.repr u).support) fun s hs => by
    rw [coreEmbedding_apply, Finsupp.notMem_support_iff.mp hs, zero_mul]]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [coreEmbedding_apply, coreEmbedding_apply, repr_mayerKreinReflection]

/-- Every core is a basis vector of the completion. -/
theorem coreEmbedding_basis [DecidableEq upperMayerResonances] (s : upperMayerResonances) :
    coreEmbedding (mayerPeriodBasis s) = lp.single 2 s 1 := by
  ext t
  rw [coreEmbedding_apply, Module.Basis.repr_self, lp.single_apply, Finsupp.single_apply,
    Pi.single_apply]
  by_cases h : t = s
  · subst h; simp
  · rw [if_neg (Ne.symm h), if_neg h]

/-- **PM's core space is dense in the completion.** -/
theorem denseRange_coreEmbedding : DenseRange coreEmbedding := by
  classical
  intro x
  rw [Metric.mem_closure_iff]
  intro ε hε
  have hsum : Tendsto (fun S : Finset upperMayerResonances => ∑ s ∈ S, lp.single 2 s (x s))
      atTop (𝓝 x) := lp.hasSum_single (p := 2) (by norm_num) x
  rw [Metric.tendsto_atTop] at hsum
  obtain ⟨S, hS⟩ := hsum ε hε
  refine ⟨coreEmbedding (∑ s ∈ S, x s • mayerPeriodBasis s), ⟨_, rfl⟩, ?_⟩
  rw [dist_comm]
  have := hS S le_rfl
  convert this using 2
  rw [map_sum]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [map_smul, coreEmbedding_basis, ← lp.single_smul, smul_eq_mul, mul_one]

/-! ### The window map -/

theorem memℓp_windowResonance {A : ℝ} (H : windowTests A) :
    Memℓp (fun s : upperMayerResonances => windowZeroMap A H (upperMayerZero s)) 2 := by
  refine (memℓp_gen_iff (by norm_num)).mpr ?_
  exact ((lp.memℓp (windowZeroMap A H)).summable (by norm_num)).comp_injective
    upperMayerZero_injective

/-- The **window map** into the completed resonant space: the zero coordinates of the test at the
upper resonances. -/
def windowResonanceMap (A : ℝ) : windowTests A →ₗ[ℝ] ResonantSpace where
  toFun H := ⟨fun s => windowZeroMap A H (upperMayerZero s), memℓp_windowResonance H⟩
  map_add' H G := by
    ext s
    simp only [map_add, lp.coeFn_add, Pi.add_apply]
  map_smul' c H := by
    ext s
    simp only [map_smul, lp.coeFn_smul, Pi.smul_apply, RingHom.id_apply]

theorem windowResonanceMap_apply {A : ℝ} (H : windowTests A) (s : upperMayerResonances) :
    windowResonanceMap A H s = windowZeroMap A H (upperMayerZero s) := rfl

/-- The coordinates are the normalized PM periods at `a = 1`. -/
theorem windowResonanceMap_eq_period {A : ℝ} (H : windowTests A) (s : upperMayerResonances) :
    windowResonanceMap A H s =
      (Real.sqrt (zetaZeroConfig.mult (2 * s.1)) : ℂ) * windowMellinPeriod H s.1 1 :=
  windowZeroMap_upperMayerZero H s

/-- The finite core packets of a window test are the truncations of its vector. -/
theorem coreEmbedding_windowWeilCorePacket {A : ℝ} (S : Finset upperMayerResonances)
    (H : windowTests A) (s : upperMayerResonances) :
    coreEmbedding (windowWeilCorePacket S H) s =
      if s ∈ pairedMayerResonances S then windowResonanceMap A H s else 0 := by
  rw [coreEmbedding_apply, repr_windowWeilCorePacket]
  rfl

/-- One reflected product of zero coordinates is a Weil summand. -/
theorem windowZeroMap_mul_conj_reflect {A : ℝ} (H : windowTests A)
    (ρ : zetaZeroConfig.carrier) :
    windowZeroMap A H ρ * conj (windowZeroMap A H (reflectCarrier zetaZeroConfig ρ)) =
      zetaZeroConfig.Wsummand (cx H) (cx H) ρ := by
  have hm := zetaZeroConfig.mult_reflect (ρ : ℂ) ρ.2
  have hsq : (Real.sqrt (zetaZeroConfig.mult ρ) : ℂ) *
      (Real.sqrt (zetaZeroConfig.mult ρ) : ℂ) = (zetaZeroConfig.mult ρ : ℂ) := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt (Nat.cast_nonneg _), Complex.ofReal_natCast]
  change zeroCoord zetaZeroConfig (cx H) ρ *
    conj (zeroCoord zetaZeroConfig (cx H) (reflectCarrier zetaZeroConfig ρ)) = _
  simp only [zeroCoord, reflectCarrier, hm, gammaOf_reflect, map_mul,
    Complex.conj_ofReal, ZeroConfig.Wsummand]
  linear_combination (paperFT (cx H) (gammaOf ρ) *
    conj (paperFT (cx H) (conj (gammaOf ρ)))) * hsq

/-- **The exact Krein identity**: `Q(H) = 2 Re [𝓦H, 𝓦H]` — no limit of finite core sums. -/
theorem weilQuad_eq_completedKreinForm {A : ℝ} (H : windowTests A) :
    weilQuad H = 2 * (completedKreinForm (windowResonanceMap A H) (windowResonanceMap A H)).re := by
  rw [weilQuad_eq_twice_upperMayer_sum H, completedKreinForm]
  congr 2
  refine tsum_congr fun s => ?_
  rw [windowResonanceMap_apply, windowResonanceMap_apply, upperMayerZero_reflect,
    windowZeroMap_mul_conj_reflect]
  rfl

/-! ### Boundedness -/

/-- The tempered zero sum `T = Σ_ρ m_ρ/(1 + |γ_ρ|²)`. -/
def temperedZeroSum : ℝ :=
  ∑' ρ : zetaZeroConfig.carrier, (zetaZeroConfig.mult ρ : ℝ) / (1 + Complex.normSq (gammaOf ρ))

/-- The `W^{2,1}` size `‖H‖₁ + ‖H''‖₁` of a test. -/
def sobolevOne (H : ℝ → ℝ) : ℝ :=
  (∫ u, ‖cx H u‖) + ∫ u, ‖deriv (deriv (cx H)) u‖

theorem norm_zeroCoord_sq_le {A : ℝ} (hA : 0 ≤ A) (H : windowTests A)
    (ρ : zetaZeroConfig.carrier) :
    ‖windowZeroMap A H ρ‖ ^ 2 ≤
      20 * Real.exp A * sobolevOne H ^ 2 *
        ((zetaZeroConfig.mult ρ : ℝ) / (1 + Complex.normSq (gammaOf ρ))) := by
  have hsupp : ∀ u, cx H u ≠ 0 → |u| ≤ A := fun u hu => by
    by_contra h
    apply hu
    have : u ∉ Icc (-A) 0 := fun hm => h (abs_le.mpr ⟨hm.1, by linarith [hm.2]⟩)
    simp [cx, H.2.vanish u this]
  have hdec := RHTower.norm_paperFT_le_decay (cx_contDiff H.2.contDiff) hsupp (gammaOf ρ)
  have him := abs_im_gammaOf_le zetaZeroConfig ρ
  have he : Real.exp (|(gammaOf ρ).im| * A) ≤ Real.exp (A / 2) :=
    Real.exp_le_exp.mpr (by nlinarith)
  set N := sobolevOne H
  have hN : 0 ≤ N := add_nonneg (integral_nonneg fun _ => norm_nonneg _)
    (integral_nonneg fun _ => norm_nonneg _)
  set r := |(gammaOf ρ).re|
  have hr : 0 ≤ r := abs_nonneg _
  have hP : ‖paperFT (cx H) (gammaOf ρ)‖ ≤ Real.exp (A / 2) * (4 * N) / (1 + r) ^ 2 :=
    hdec.trans (div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right he (by positivity)) (by positivity))
  have hnorm : ‖windowZeroMap A H ρ‖ ^ 2 =
      (zetaZeroConfig.mult ρ : ℝ) * ‖paperFT (cx H) (gammaOf ρ)‖ ^ 2 :=
    norm_zeroCoord_sq zetaZeroConfig (cx H) ρ
  have hm : (0 : ℝ) ≤ zetaZeroConfig.mult ρ := Nat.cast_nonneg _
  have hden : 1 + Complex.normSq (gammaOf ρ) ≤ 5 / 4 * (1 + r) ^ 2 := by
    rw [Complex.normSq_apply]
    have h1 : (gammaOf ρ).im * (gammaOf ρ).im ≤ 1 / 4 := by
      have := abs_le.mp him; nlinarith
    have h2 : (gammaOf ρ).re * (gammaOf ρ).re = r ^ 2 := by rw [sq_abs]; ring
    nlinarith
  have hpos : 0 < 1 + Complex.normSq (gammaOf ρ) := by
    have := Complex.normSq_nonneg (gammaOf ρ); linarith
  have hsq : ‖paperFT (cx H) (gammaOf ρ)‖ ^ 2 ≤ (Real.exp (A / 2) * (4 * N)) ^ 2 / (1 + r) ^ 4 := by
    have h0 := norm_nonneg (paperFT (cx H) (gammaOf ρ))
    calc ‖paperFT (cx H) (gammaOf ρ)‖ ^ 2 ≤ (Real.exp (A / 2) * (4 * N) / (1 + r) ^ 2) ^ 2 :=
          pow_le_pow_left₀ h0 hP 2
      _ = _ := by rw [div_pow]; ring
  have hexp : Real.exp (A / 2) ^ 2 = Real.exp A := by
    rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
  have h14 : (1 + r) ^ 2 ≤ (1 + r) ^ 4 := by
    have : 1 ≤ (1 + r) ^ 2 := by nlinarith
    nlinarith
  rw [hnorm]
  calc (zetaZeroConfig.mult ρ : ℝ) * ‖paperFT (cx H) (gammaOf ρ)‖ ^ 2
      ≤ (zetaZeroConfig.mult ρ : ℝ) * ((Real.exp (A / 2) * (4 * N)) ^ 2 / (1 + r) ^ 4) :=
        mul_le_mul_of_nonneg_left hsq hm
    _ ≤ (zetaZeroConfig.mult ρ : ℝ) * ((Real.exp (A / 2) * (4 * N)) ^ 2 /
          ((4 / 5) * (1 + Complex.normSq (gammaOf ρ)))) := by
        refine mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_left (by positivity)
          (by positivity) ?_) hm
        linarith
    _ = 20 * Real.exp A * N ^ 2 *
          ((zetaZeroConfig.mult ρ : ℝ) / (1 + Complex.normSq (gammaOf ρ))) := by
        rw [mul_pow, hexp]
        field_simp
        ring

/-- **The window map is bounded**: `‖𝓦_A H‖² ≤ 20 e^A T ‖H‖²_{W^{2,1}}`. -/
theorem norm_windowResonanceMap_sq_le {A : ℝ} (hA : 0 ≤ A) (H : windowTests A) :
    ‖windowResonanceMap A H‖ ^ 2 ≤ 20 * Real.exp A * temperedZeroSum * sobolevOne H ^ 2 := by
  have hT := SquareRootThreshold.temperedConfig_zetaZeroConfig
  have h2 : (0 : ℝ) < (2 : ENNReal).toReal := by norm_num
  have hn := lp.norm_rpow_eq_tsum h2 (windowResonanceMap A H)
  simp only [ENNReal.toReal_ofNat, Real.rpow_two] at hn
  have hs1 : Summable fun s => ‖windowResonanceMap A H s‖ ^ 2 := by
    have := (memℓp_gen_iff h2).mp (lp.memℓp (windowResonanceMap A H))
    simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using this
  rw [hn]
  set w : zetaZeroConfig.carrier → ℝ := fun ρ =>
    (zetaZeroConfig.mult ρ : ℝ) / (1 + Complex.normSq (gammaOf ρ))
  have hw0 : ∀ ρ, 0 ≤ w ρ := fun ρ => div_nonneg (Nat.cast_nonneg _)
    (by have := Complex.normSq_nonneg (gammaOf ρ); linarith)
  have hsw : Summable (fun s : upperMayerResonances => w (upperMayerZero s)) :=
    hT.comp_injective upperMayerZero_injective
  have hle : ∑' s : upperMayerResonances, ‖windowResonanceMap A H s‖ ^ 2 ≤
      ∑' s : upperMayerResonances, 20 * Real.exp A * sobolevOne H ^ 2 * w (upperMayerZero s) :=
    Summable.tsum_le_tsum (fun s => norm_zeroCoord_sq_le hA H (upperMayerZero s)) hs1
      (hsw.mul_left _)
  refine hle.trans ?_
  rw [tsum_mul_left]
  have hsub : ∑' s : upperMayerResonances, w (upperMayerZero s) ≤ temperedZeroSum :=
    tsum_comp_le_tsum_of_inj hT hw0 upperMayerZero_injective
  have hc : 0 ≤ 20 * Real.exp A * sobolevOne H ^ 2 := by positivity
  nlinarith

/-! ### Hecke -/

/-- The Mellin translation `F_pH = √p H(· + log p)` into the window of length `A + log p`. -/
def heckePull (p : ℕ) (H : ℝ → ℝ) : ℝ → ℝ := fun u => Real.sqrt p * H (u + Real.log p)

theorem heckePull_mem {A : ℝ} {H : ℝ → ℝ} (hH : IsWindowTest A H) {p : ℕ} (hp : 1 ≤ p) :
    IsWindowTest (A + Real.log p) (heckePull p H) := by
  have hl : 0 ≤ Real.log p := Real.log_nonneg (by exact_mod_cast hp)
  refine ⟨contDiff_const.mul (hH.contDiff.comp (contDiff_id.add contDiff_const)), fun u hu => ?_⟩
  have h : u + Real.log p ∉ Icc (-A) 0 := fun hm =>
    hu ⟨by linarith [hm.1], by linarith [hm.2]⟩
  simp only [heckePull]
  rw [hH.vanish _ h, mul_zero]

/-- The pull as a map of window tests. -/
def heckePullTest {A : ℝ} {p : ℕ} (hp : 1 ≤ p) (H : windowTests A) :
    windowTests (A + Real.log p) :=
  ⟨heckePull p H, heckePull_mem H.2 hp⟩

/-- The Mellin multiplier of the pull: `tr(F_pH)(z) = p^{1−z} tr(H)(z)`. -/
theorem tr_heckePull (H : ℝ → ℝ) {p : ℕ} (hp : 1 ≤ p) (z : ℂ) :
    tr (fun u => (heckePull p H u : ℂ)) z = (p : ℂ) ^ (1 - z) * tr (fun u => (H u : ℂ)) z := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp
  have hfun : (fun u => (heckePull p H u : ℂ)) = fun u =>
      (Real.sqrt p : ℂ) * ArithmeticPolarization.translate (-Real.log p) (fun v => (H v : ℂ)) u := by
    funext u
    simp only [heckePull, ArithmeticPolarization.translate, sub_neg_eq_add, Complex.ofReal_mul]
  rw [hfun, tr, paperFT_const_mul]
  change (Real.sqrt p : ℂ) *
    tr (ArithmeticPolarization.translate (-Real.log p) (fun u => (H u : ℂ))) z = _
  rw [tr_translate, ← mul_assoc]
  congr 1
  have hs : (Real.sqrt p : ℂ) = Complex.exp ((Real.log p / 2 : ℝ) : ℂ) := by
    rw [← Complex.ofReal_exp, Real.sqrt_eq_rpow, Real.rpow_def_of_pos hp0]
    congr 2; ring
  rw [hs, ← Complex.exp_add, Complex.cpow_def_of_ne_zero (by exact_mod_cast hp0.ne'),
    ← Complex.ofReal_natCast, ← Complex.ofReal_log hp0.le]
  congr 1
  push_cast
  ring

/-- The pull acts on zero coordinates by `p^{1−ρ}`. -/
theorem windowZeroMap_heckePull {A : ℝ} {p : ℕ} (hp : 1 ≤ p) (H : windowTests A)
    (ρ : zetaZeroConfig.carrier) :
    windowZeroMap (A + Real.log p) (heckePullTest hp H) ρ =
      (p : ℂ) ^ (1 - (ρ : ℂ)) * windowZeroMap A H ρ := by
  change zeroCoord zetaZeroConfig (cx (heckePull p H)) ρ =
    (p : ℂ) ^ (1 - (ρ : ℂ)) * zeroCoord zetaZeroConfig (cx H) ρ
  have h : paperFT (cx (heckePull p H)) (gammaOf ρ) =
      (p : ℂ) ^ (1 - (ρ : ℂ)) * paperFT (cx H) (gammaOf ρ) := tr_heckePull (H : ℝ → ℝ) hp (ρ : ℂ)
  simp only [zeroCoord]
  rw [h]
  ring

/-- The **Hecke multiplier** `(D_p x)_s = p^{1−2s} x_s` on the completed resonant space. -/
def heckeMultiplierFun (p : ℕ) (x : ResonantSpace) (s : upperMayerResonances) : ℂ :=
  (p : ℂ) ^ (1 - 2 * s.1) * x s

theorem norm_heckeMultiplierFun_le {p : ℕ} (hp : 1 ≤ p) (x : ResonantSpace)
    (s : upperMayerResonances) : ‖heckeMultiplierFun p x s‖ ≤ p * ‖x s‖ := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp
  rw [heckeMultiplierFun, norm_mul, Complex.norm_natCast_cpow_of_pos (by omega)]
  refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
  have hre : (1 - 2 * s.1).re ≤ 1 := by
    simp only [Complex.sub_re, Complex.one_re, Complex.mul_re, Complex.re_ofNat,
      Complex.im_ofNat, zero_mul, sub_zero]
    linarith [s.2.2.1]
  calc (p : ℝ) ^ (1 - 2 * s.1).re ≤ (p : ℝ) ^ (1 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hp) hre
    _ = p := Real.rpow_one _

theorem memℓp_heckeMultiplier {p : ℕ} (hp : 1 ≤ p) (x : ResonantSpace) :
    Memℓp (heckeMultiplierFun p x) 2 := by
  refine (memℓp_gen_iff (by norm_num)).mpr ?_
  refine Summable.of_nonneg_of_le (fun s => by positivity) (fun s => ?_)
    (((memℓp_gen_iff (by norm_num)).mp (lp.memℓp x)).mul_left ((p : ℝ) ^ 2))
  simp only [ENNReal.toReal_ofNat, Real.rpow_two]
  have h := norm_heckeMultiplierFun_le hp x s
  have h0 := norm_nonneg (heckeMultiplierFun p x s)
  calc ‖heckeMultiplierFun p x s‖ ^ 2 ≤ (p * ‖x s‖) ^ 2 := pow_le_pow_left₀ h0 h 2
    _ = (p : ℝ) ^ 2 * ‖x s‖ ^ 2 := by ring

/-- The Hecke multiplier as a vector of the completion. -/
def heckeMultiplier {p : ℕ} (hp : 1 ≤ p) (x : ResonantSpace) : ResonantSpace :=
  ⟨heckeMultiplierFun p x, memℓp_heckeMultiplier hp x⟩

/-- **The Mellin translation is the Hecke multiplier**: `𝓦_{A + log p}(F_pH) = D_p 𝓦_A H`. -/
theorem windowResonanceMap_heckePull {A : ℝ} {p : ℕ} (hp : 1 ≤ p) (H : windowTests A) :
    windowResonanceMap (A + Real.log p) (heckePullTest hp H) =
      heckeMultiplier hp (windowResonanceMap A H) := by
  ext s
  change windowZeroMap (A + Real.log p) (heckePullTest hp H) (upperMayerZero s) =
    (p : ℂ) ^ (1 - 2 * s.1) * windowZeroMap A H (upperMayerZero s)
  rw [windowZeroMap_heckePull hp H]
  rfl

/-- **`D_p` is a Krein similitude of factor `p`**: `[D_p x, D_p y] = p[x, y]`. -/
theorem completedKreinForm_heckeMultiplier {p : ℕ} (hp : 1 ≤ p) (x y : ResonantSpace) :
    completedKreinForm (heckeMultiplier hp x) (heckeMultiplier hp y) =
      p * completedKreinForm x y := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp
  have hpc : (p : ℂ) ≠ 0 := by exact_mod_cast hp0.ne'
  rw [completedKreinForm, completedKreinForm, ← tsum_mul_left]
  refine tsum_congr fun s => ?_
  change (p : ℂ) ^ (1 - 2 * s.1) * x s *
      conj ((p : ℂ) ^ (1 - 2 * (reflectUpperResonance s).1) * y (reflectUpperResonance s)) = _
  have hr : (reflectUpperResonance s).1 = riemannMayerReflect s.1 := rfl
  have hconj : conj ((p : ℂ) ^ (1 - 2 * riemannMayerReflect s.1)) = (p : ℂ) ^ (2 * s.1) := by
    have hl : Complex.log (p : ℂ) = ((Real.log p : ℝ) : ℂ) := by
      rw [← Complex.ofReal_natCast, Complex.ofReal_log hp0.le]
    rw [Complex.cpow_def_of_ne_zero hpc, Complex.cpow_def_of_ne_zero hpc, ← Complex.exp_conj,
      map_mul, hl, Complex.conj_ofReal]
    congr 1
    simp only [riemannMayerReflect, map_sub, map_one, map_mul, map_ofNat, map_div₀,
      Complex.conj_conj]
    ring
  rw [hr, map_mul, hconj]
  have hadd : (p : ℂ) ^ (1 - 2 * s.1) * (p : ℂ) ^ (2 * s.1) = p := by
    rw [← Complex.cpow_add _ _ hpc]; simp
  linear_combination (x s * conj (y (reflectUpperResonance s))) * hadd

/-- **`‖D_p x‖ ≤ p‖x‖`**. -/
theorem norm_heckeMultiplier_le {p : ℕ} (hp : 1 ≤ p) (x : ResonantSpace) :
    ‖heckeMultiplier hp x‖ ≤ p * ‖x‖ := by
  have h2 : (0 : ℝ) < (2 : ENNReal).toReal := by norm_num
  have e1 := lp.norm_rpow_eq_tsum h2 (heckeMultiplier hp x)
  have e2 := lp.norm_rpow_eq_tsum h2 x
  simp only [ENNReal.toReal_ofNat, Real.rpow_two] at e1 e2
  have hs1 : Summable fun s => ‖x s‖ ^ 2 := by
    have := (memℓp_gen_iff h2).mp (lp.memℓp x)
    simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using this
  have hs2 : Summable fun s => ‖heckeMultiplier hp x s‖ ^ 2 := by
    have := (memℓp_gen_iff h2).mp (lp.memℓp (heckeMultiplier hp x))
    simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using this
  have hsq : ‖heckeMultiplier hp x‖ ^ 2 ≤ ((p : ℝ) * ‖x‖) ^ 2 := by
    rw [e1, mul_pow, e2, ← tsum_mul_left]
    refine Summable.tsum_le_tsum (fun s => ?_) hs2 (hs1.mul_left _)
    calc ‖heckeMultiplier hp x s‖ ^ 2 ≤ ((p : ℝ) * ‖x s‖) ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) (norm_heckeMultiplierFun_le hp x s) 2
      _ = (p : ℝ) ^ 2 * ‖x s‖ ^ 2 := by ring
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) (by norm_num)).mp hsq

/-- **The source Hecke operator at `2` is the Mellin translation**: on completed periods,
`T₂Φ_H − Φ_H = Φ_{F₂H}`. -/
theorem lewisHeckeT2_sub_eq_pull (H : ℝ → ℝ) {s : ℂ} (hs0 : 0 < s.re) (hs1 : s.re < 1 / 2)
    {a : ℝ} (ha : 0 < a) :
    lewisHeckeT2 s (windowMellinPeriod H s) a - windowMellinPeriod H s a =
      windowMellinPeriod (heckePull 2 H) s a := by
  have : heckePull 2 H = heckeWindowPull H := by
    funext u; simp [heckePull, heckeWindowPull]
  rw [this]
  exact lewisHeckeT2_windowMellinPeriod H hs0 hs1 ha

/-! ### Reflection -/

/-- **Window reflection is the twisted conjugate Krein reflection**:
`𝓦(σ_A H)_s = e^{−A(2s−½)} conj(𝓦 H_{s♯})`. -/
theorem windowResonanceMap_windowInvolution {A : ℝ} (H : windowTests A)
    (Hσ : windowTests A) (hσ : (Hσ : ℝ → ℝ) = windowInvolution A H) (s : upperMayerResonances) :
    windowResonanceMap A Hσ s =
      Complex.exp (-(A : ℂ) * (2 * s.1 - 1 / 2)) *
        conj (windowResonanceMap A H (reflectUpperResonance s)) := by
  have hr : (reflectUpperResonance s).1 = riemannMayerReflect s.1 := rfl
  have hm : zetaZeroConfig.mult (2 * riemannMayerReflect s.1) =
      zetaZeroConfig.mult (2 * s.1) := by
    have e : 2 * riemannMayerReflect s.1 = reflect (2 * s.1) := by
      simp only [riemannMayerReflect, reflect, map_mul, map_ofNat]; ring
    rw [e]
    exact zetaZeroConfig.mult_reflect _ (upperMayerZero s).2
  rw [windowResonanceMap_eq_period, windowResonanceMap_eq_period, hr, hm, hσ,
    windowMellinPeriod_krein_reflection_one A H s.2.2.1 s.2.2.2.1, map_mul, Complex.conj_ofReal]
  ring

end GaloisForLFunctions.RenormalizedIntersectionTheory.MayerScattering
