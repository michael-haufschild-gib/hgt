import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.TemperedConfigurationPontryaginLaw
import GaloisForLFunctions.SquareRootThreshold.WeilPositivityForcesTheCriticalLine
import Mathlib.Analysis.InnerProductSpace.l2Space

/-!
# The Hodge defect counts the zeros right of the line

For a tempered configuration `Z` the largest number of negative squares of the Weil form on a
finite family of compactly supported `C²` tests is **exactly** `#{ρ ∈ Z : Re ρ > ½}` in `ℕ∞`
(`pontryagin_law`), with no finiteness assumption on the zeros. For `ζ`, through the signature law,
the arithmetic intersection form of the scaling surface has `1 + n` positive squares on some
finite family of cycles iff `ζ` has at least `n` zeros right of the critical line
(`zeta_hodgeDefect_iff`); in particular `ζ` has infinitely many zeros off the line iff the Hodge
defect of the scaling surface is unbounded (`zeta_rightZeros_infinite_iff`).

* **Zero-side coordinates.** A test `f` has coordinates `X_τ(f) = √m_τ h_f(γ_τ)` in `ℓ²(Z)`
  (`zeroMap`), and Weil's form is `W(f, g) = ⟨R X(g), X(f)⟩` with `R` the reflection
  `τ ↦ 1 − τ̄` of the coordinates (`W_eq_inner`): a Krein form whose hyperbolic planes are the
  pairs `ρ, 1 − ρ̄`, each with one negative square `e_ρ − e_{1−ρ̄}`.
* **Uniqueness** (`eq_zero_of_tsum_exp_eq_zero`). An absolutely convergent sum
  `Σ_τ q_τ e^{(τ̄ − ½)v}` vanishing for `v ≥ 0` has `q = 0`: at each height the rightmost exponent
  with nonzero coefficient would be a pole of the Laplace transform of the zero function
  (`SquareRootThreshold.eq_zero_of_norm_tsum_exp_le_exp`).
* **Density** (`orthogonal_range_zeroMap`). A vector orthogonal to the coordinates of every probe
  `φ(u − v) e^{isu}` gives such a sum; choosing `s = −Im τ` makes the probe's transform nonzero
  at `γ_τ`, so the vector vanishes. The coordinates of tests are dense in `ℓ²(Z)`.
* **Attainment** (`exists_zeroGram_negIndex_ge`). Approximating `e_ρ − e_{1−ρ̄}` for finitely
  many right zeros `ρ` gives tests whose Gram matrix is within `5ε` of `−2·I`, hence negative
  definite.
-/

open Complex Matrix Finset
open scoped ComplexConjugate lp
open Zeta23 GaloisForLFunctions.HTGeometry
open GaloisForLFunctions.SquareRootThreshold (TemperedConfig temperedConfig_zetaZeroConfig
  exists_sep_height carrier_countable eq_zero_of_norm_tsum_exp_le_exp)

noncomputable section

namespace GaloisForLFunctions.ArithmeticCastelnuovoSeveri

/-! ### Uniqueness of exponential sums over a configuration -/

/-- **Uniqueness.** If `Σ_τ q_τ e^{(τ̄ − ½)v} = 0` for every `v ≥ 0` and `Σ_τ |q_τ| < ∞`, then
every coefficient vanishes. -/
theorem eq_zero_of_tsum_exp_eq_zero (Z : ZeroConfig) {q : Z.carrier → ℂ}
    (hq : Summable fun τ => ‖q τ‖)
    (h : ∀ v : ℝ, 0 ≤ v → ∑' τ, q τ * cexp ((conj (τ : ℂ) - 1 / 2) * v) = 0) (τ₀ : Z.carrier) :
    q τ₀ = 0 := by
  classical
  by_contra hτ₀
  -- the nonzero coefficients at the height of `τ₀` are finitely many: take the rightmost
  have hwin : (Subtype.val ⁻¹' (Z.carrier ∩ {ρ | (τ₀ : ℂ).im - 1 < ρ.im ∧ ρ.im ≤ (τ₀ : ℂ).im}) :
      Set Z.carrier).Finite :=
    (Z.finite_window _ _).preimage Subtype.val_injective.injOn
  set F : Finset Z.carrier :=
    hwin.toFinset.filter fun τ => q τ ≠ 0 ∧ (τ : ℂ).im = (τ₀ : ℂ).im with hF
  have hmemF : ∀ τ : Z.carrier, q τ ≠ 0 → (τ : ℂ).im = (τ₀ : ℂ).im → τ ∈ F := fun τ hq0 him => by
    rw [hF, Finset.mem_filter, Set.Finite.mem_toFinset]
    exact ⟨⟨τ.2, by rw [him]; linarith, by rw [him]⟩, hq0, him⟩
  obtain ⟨t₁, ht₁F, hmax⟩ := F.exists_max_image (fun τ => (τ : ℂ).re)
    ⟨τ₀, hmemF τ₀ hτ₀ rfl⟩
  rw [hF, Finset.mem_filter] at ht₁F
  obtain ⟨-, hq₁, him₁⟩ := ht₁F
  -- the family of nonzero coefficients
  set S : Set Z.carrier := {τ | q τ ≠ 0} with hS
  haveI : Countable Z.carrier := (carrier_countable Z).to_subtype
  set lam : S → ℂ := fun t => conj ((t : Z.carrier) : ℂ) - 1 / 2 with hlam
  have hre : ∀ t : S, (lam t).re = ((t : Z.carrier) : ℂ).re - 1 / 2 := fun t => by simp [hlam]
  have him : ∀ t : S, (lam t).im = -((t : Z.carrier) : ℂ).im := fun t => by simp [hlam]
  obtain ⟨η, hη, hsepZ⟩ := exists_sep_height Z (t₁ : ℂ).im
  have h0 := eq_zero_of_norm_tsum_exp_le_exp (lam := lam) (q := fun t : S => q t)
    (hq.subtype S) (A := 1 / 2) (fun t => by
      rw [hre]; linarith [(Z.strip _ (t : Z.carrier).2).2])
    (σ := (lam ⟨t₁, hq₁⟩).re - 1) ⟨t₁, hq₁⟩ (by linarith)
    (fun t ht => by
      rw [him, him, neg_inj] at ht
      have htF := hmemF t t.2 (ht.trans him₁)
      rw [hre, hre]
      linarith [hmax t htF])
    (fun t ht => by
      have := congrArg conj (sub_left_injective ht)
      simp only [conj_conj] at this
      exact Subtype.ext (Subtype.ext this))
    hη (fun t ht => by
      rw [him, him] at ht ⊢
      have : |((t : Z.carrier) : ℂ).im - (t₁ : ℂ).im| < η := by
        rw [show ((t : Z.carrier) : ℂ).im - (t₁ : ℂ).im =
          -(-((t : Z.carrier) : ℂ).im - -(t₁ : ℂ).im) by ring, abs_neg]
        exact ht
      rw [hsepZ _ (t : Z.carrier).2 this])
    (K := 0) (fun v hv => by
      have hsupp : Function.support (fun τ : Z.carrier => q τ * cexp ((conj (τ : ℂ) - 1 / 2) * v))
          ⊆ S := fun τ hτ h0 => hτ (by simp only [h0, zero_mul])
      have h1 : ∑' t : S, q t * cexp ((conj ((t : Z.carrier) : ℂ) - 1 / 2) * v) = 0 := by
        rw [tsum_subtype_eq_of_support_subset hsupp]
        exact h v hv
      simp only [hlam, h1, norm_zero, zero_mul, le_refl])
  exact hq₁ h0

/-! ### Probes -/

/-- The probe `u ↦ φ(u − v) e^{isu}`: the short bump `φ` translated by `v` and modulated by `s`. -/
def probe (s v : ℝ) : ℝ → ℂ := fun u => bumpTest (1 / 2) (by norm_num) v u * cexp (I * s * u)

theorem probe_contDiff (s v : ℝ) : ContDiff ℝ 2 (probe s v) :=
  (bumpTest_contDiff _ v).mul (Complex.contDiff_exp.comp (contDiff_const.mul
    Complex.ofRealCLM.contDiff))

theorem probe_hasCompactSupport (s v : ℝ) : HasCompactSupport (probe s v) :=
  (bumpTest_hasCompactSupport _ v).mul_right

/-- The probe's transform is the bump's transform shifted by `s`, times the translation phase. -/
theorem paperFT_probe (s v : ℝ) (z : ℂ) :
    paperFT (probe s v) z =
      cexp (I * (z + s) * v) * paperFT (bumpTest (1 / 2) (by norm_num) 0) (z + s) := by
  rw [← paperFT_bumpTest]
  unfold paperFT
  congr 1
  funext u
  simp only [probe]
  rw [mul_assoc, ← Complex.exp_add]
  congr 2
  ring

/-! ### Zero-side coordinates -/

/-- The zero-side coordinates `X_τ(f) = √m_τ h_f(γ_τ)`. -/
def zeroCoord (Z : ZeroConfig) (f : ℝ → ℂ) (τ : Z.carrier) : ℂ :=
  (Real.sqrt (Z.mult τ) : ℂ) * paperFT f (gammaOf τ)

theorem norm_zeroCoord_sq (Z : ZeroConfig) (f : ℝ → ℂ) (τ : Z.carrier) :
    ‖zeroCoord Z f τ‖ ^ 2 = (Z.mult τ : ℝ) * ‖paperFT f (gammaOf τ)‖ ^ 2 := by
  rw [zeroCoord, norm_mul, mul_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs,
    Real.sq_sqrt (Nat.cast_nonneg _)]

theorem memℓp_zeroCoord (Z : ZeroConfig) (hZ : TemperedConfig Z) {f : ℝ → ℂ}
    (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f) : Memℓp (zeroCoord Z f) 2 := by
  refine (memℓp_gen_iff (by norm_num)).mpr ?_
  refine (summable_mult_norm_mul Z hZ hf hfc hf hfc (fun τ => gammaOf τ)
    (abs_im_gammaOf_le Z)).congr fun τ => ?_
  rw [ENNReal.toReal_ofNat, Real.rpow_two, norm_zeroCoord_sq]
  ring

/-- The compactly supported `C²` tests. -/
def testSpace : Submodule ℂ (ℝ → ℂ) where
  carrier := {f | ContDiff ℝ 2 f ∧ HasCompactSupport f}
  add_mem' ha hb := ⟨ha.1.add hb.1, ha.2.add hb.2⟩
  zero_mem' := ⟨contDiff_const, HasCompactSupport.zero⟩
  smul_mem' c _ hf := ⟨hf.1.const_smul c, hf.2.smul_left⟩

theorem paperFT_add {f g : ℝ → ℂ} (hf : Continuous f) (hfc : HasCompactSupport f)
    (hg : Continuous g) (hgc : HasCompactSupport g) (z : ℂ) :
    paperFT (f + g) z = paperFT f z + paperFT g z := by
  have hi : ∀ {k : ℝ → ℂ}, Continuous k → HasCompactSupport k →
      MeasureTheory.Integrable (fun u => k u * cexp (I * z * u)) := fun hk hkc =>
    (hk.mul (by fun_prop)).integrable_of_hasCompactSupport hkc.mul_right
  simp only [paperFT, Pi.add_apply, add_mul]
  exact MeasureTheory.integral_add (hi hf hfc) (hi hg hgc)

theorem paperFT_smul (c : ℂ) (f : ℝ → ℂ) (z : ℂ) : paperFT (c • f) z = c * paperFT f z := by
  simp only [paperFT, Pi.smul_apply, smul_eq_mul, mul_assoc]
  exact MeasureTheory.integral_const_mul c _

/-- **The zero-side map** `f ↦ (√m_τ h_f(γ_τ))_τ` into `ℓ²(Z)`. -/
def zeroMap (Z : ZeroConfig) (hZ : TemperedConfig Z) : testSpace →ₗ[ℂ] ℓ²(Z.carrier, ℂ) where
  toFun f := ⟨zeroCoord Z f, memℓp_zeroCoord Z hZ f.2.1 f.2.2⟩
  map_add' f g := by
    ext τ
    show zeroCoord Z ((f + g : testSpace) : ℝ → ℂ) τ = zeroCoord Z f τ + zeroCoord Z g τ
    rw [Submodule.coe_add, zeroCoord, zeroCoord, zeroCoord,
      paperFT_add f.2.1.continuous f.2.2 g.2.1.continuous g.2.2]
    ring
  map_smul' c f := by
    ext τ
    show zeroCoord Z ((c • f : testSpace) : ℝ → ℂ) τ = c * zeroCoord Z f τ
    rw [Submodule.coe_smul, zeroCoord, zeroCoord, paperFT_smul]
    ring

theorem zeroMap_apply (Z : ZeroConfig) (hZ : TemperedConfig Z) (f : testSpace) (τ : Z.carrier) :
    zeroMap Z hZ f τ = zeroCoord Z f τ := rfl

/-! ### Density -/

theorem zeroCoord_probe (Z : ZeroConfig) (s v : ℝ) (τ : Z.carrier) :
    zeroCoord Z (probe s v) τ = cexp (I * (gammaOf τ + s) * v) * zeroCoord Z (probe s 0) τ := by
  simp only [zeroCoord, paperFT_probe, Complex.ofReal_zero, mul_zero, Complex.exp_zero, one_mul]
  ring

theorem conj_I_mul_gammaOf_add (τ : ℂ) (s v : ℝ) :
    conj (I * (gammaOf τ + s) * v) = (conj τ - 1 / 2) * v + -(I * s * v) := by
  have h : I * gammaOf τ = τ - 1 / 2 := by
    rw [gammaOf, mul_div_assoc', mul_div_cancel_left₀ _ I_ne_zero]
  rw [mul_add, h]
  simp only [map_mul, map_add, map_sub, Complex.conj_I, Complex.conj_ofReal, map_one, map_div₀,
    map_ofNat]
  ring

/-- **Density.** Only `0` is orthogonal to the zero-side coordinates of every test. -/
theorem orthogonal_range_zeroMap (Z : ZeroConfig) (hZ : TemperedConfig Z) :
    (LinearMap.range (zeroMap Z hZ))ᗮ = ⊥ := by
  rw [Submodule.eq_bot_iff]
  intro a ha
  -- `a` is orthogonal to every probe
  have hzero : ∀ s v : ℝ, ∑' τ, conj (zeroCoord Z (probe s v) τ) * a τ = 0 := fun s v => by
    have h := (Submodule.mem_orthogonal _ a).mp ha
      (zeroMap Z hZ ⟨probe s v, probe_contDiff s v, probe_hasCompactSupport s v⟩)
      (LinearMap.mem_range_self _ _)
    rw [lp.inner_eq_tsum] at h
    simpa only [RCLike.inner_apply', zeroMap_apply] using h
  ext τ₀
  rw [lp.coeFn_zero, Pi.zero_apply]
  -- the probe modulated to the height of `τ₀`
  set s : ℝ := -(τ₀ : ℂ).im with hs
  set q : Z.carrier → ℂ := fun τ => conj (zeroCoord Z (probe s 0) τ) * a τ with hq
  have hqs : Summable fun τ => ‖q τ‖ := by
    have h1 := (memℓp_zeroCoord Z hZ (probe_contDiff s 0) (probe_hasCompactSupport s 0)).summable
      (by norm_num : (0 : ℝ) < (2 : ENNReal).toReal)
    have h2 := (lp.memℓp a).summable (by norm_num : (0 : ℝ) < (2 : ENNReal).toReal)
    simp only [ENNReal.toReal_ofNat, Real.rpow_two] at h1 h2
    refine Summable.of_nonneg_of_le (fun τ => norm_nonneg _) (fun τ => ?_) ((h1.add h2).div_const 2)
    simp only [hq, norm_mul, Complex.norm_conj]
    nlinarith [sq_nonneg (‖zeroCoord Z (probe s 0) τ‖ - ‖a τ‖)]
  have hexp : ∀ v : ℝ, 0 ≤ v → ∑' τ, q τ * cexp ((conj (τ : ℂ) - 1 / 2) * v) = 0 := by
    intro v _
    have h := hzero s v
    have hrw : ∀ τ : Z.carrier, conj (zeroCoord Z (probe s v) τ) * a τ =
        cexp (-(I * s * v)) * (q τ * cexp ((conj (τ : ℂ) - 1 / 2) * v)) := fun τ => by
      rw [zeroCoord_probe, map_mul, ← Complex.exp_conj, conj_I_mul_gammaOf_add, Complex.exp_add]
      simp only [hq]
      ring
    rw [tsum_congr hrw, tsum_mul_left] at h
    exact (mul_eq_zero.mp h).resolve_left (Complex.exp_ne_zero _)
  have hq0 := eq_zero_of_tsum_exp_eq_zero Z hqs hexp τ₀
  -- the probe's coordinate at `τ₀` is nonzero
  have hc : zeroCoord Z (probe s 0) τ₀ ≠ 0 := by
    have hm : (0 : ℝ) < Z.mult τ₀ := by exact_mod_cast Z.one_le_mult _ τ₀.2
    rw [zeroCoord, paperFT_probe, Complex.ofReal_zero, mul_zero, Complex.exp_zero, one_mul]
    refine mul_ne_zero (Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr hm).ne')
      (paperFT_bumpTest_zero_ne_zero _ ?_)
    have hz : gammaOf (τ₀ : ℂ) + (s : ℂ) = -(I * (((τ₀ : ℂ).re - 1 / 2 : ℝ) : ℂ)) := by
      rw [gammaOf_eq, hs]
      push_cast
      ring
    have hstrip := Z.strip _ τ₀.2
    rw [hz, norm_neg, norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs]
    have : |(τ₀ : ℂ).re - 1 / 2| ≤ 1 / 2 := by
      rw [abs_le]; constructor <;> linarith [hstrip.1, hstrip.2]
    nlinarith
  simp only [hq] at hq0
  exact (mul_eq_zero.mp hq0).resolve_left ((map_ne_zero _).mpr hc)

/-- Every vector of `ℓ²(Z)` is approximated by the zero-side coordinates of a test. -/
theorem exists_zeroMap_near (Z : ZeroConfig) (hZ : TemperedConfig Z) (x : ℓ²(Z.carrier, ℂ))
    {ε : ℝ} (hε : 0 < ε) : ∃ f : testSpace, ‖zeroMap Z hZ f - x‖ < ε := by
  have hx : x ∈ (LinearMap.range (zeroMap Z hZ)).topologicalClosure := by
    rw [(Submodule.topologicalClosure_eq_top_iff (K := LinearMap.range (zeroMap Z hZ))).mpr
      (orthogonal_range_zeroMap Z hZ)]
    trivial
  rw [← SetLike.mem_coe, Submodule.topologicalClosure_coe, Metric.mem_closure_iff] at hx
  obtain ⟨y, hy1, hy⟩ := hx ε hε
  obtain ⟨f, rfl⟩ := LinearMap.mem_range.mp hy1
  exact ⟨f, by rwa [dist_comm, dist_eq_norm] at hy⟩

/-! ### Weil's form as a Krein form on `ℓ²(Z)` -/

/-- The reflection `τ ↦ 1 − τ̄` of the carrier. -/
def reflectCarrier (Z : ZeroConfig) (τ : Z.carrier) : Z.carrier :=
  ⟨reflect τ, Z.reflect_mem _ τ.2⟩

theorem reflectCarrier_reflectCarrier (Z : ZeroConfig) (τ : Z.carrier) :
    reflectCarrier Z (reflectCarrier Z τ) = τ :=
  Subtype.ext (by simp [reflectCarrier, reflect])

/-- The reflection as a permutation of the carrier. -/
def reflectEquiv (Z : ZeroConfig) : Z.carrier ≃ Z.carrier :=
  ⟨reflectCarrier Z, reflectCarrier Z, reflectCarrier_reflectCarrier Z,
    reflectCarrier_reflectCarrier Z⟩

theorem reflectEquiv_apply (Z : ZeroConfig) (τ : Z.carrier) :
    reflectEquiv Z τ = reflectCarrier Z τ := rfl

theorem memℓp_reflect (Z : ZeroConfig) (x : ℓ²(Z.carrier, ℂ)) :
    Memℓp (fun τ => x (reflectCarrier Z τ)) 2 := by
  refine (memℓp_gen_iff (by norm_num)).mpr ?_
  exact (reflectEquiv Z).summable_iff.mpr ((lp.memℓp x).summable (by norm_num))

/-- The reflection of the coordinates. -/
def reflectVec (Z : ZeroConfig) (x : ℓ²(Z.carrier, ℂ)) : ℓ²(Z.carrier, ℂ) :=
  ⟨fun τ => x (reflectCarrier Z τ), memℓp_reflect Z x⟩

theorem reflectVec_apply (Z : ZeroConfig) (x : ℓ²(Z.carrier, ℂ)) (τ : Z.carrier) :
    reflectVec Z x τ = x (reflectCarrier Z τ) := rfl

theorem reflectVec_add (Z : ZeroConfig) (x y : ℓ²(Z.carrier, ℂ)) :
    reflectVec Z (x + y) = reflectVec Z x + reflectVec Z y := by
  ext τ
  simp only [reflectVec_apply, lp.coeFn_add, Pi.add_apply]

theorem reflectVec_sub (Z : ZeroConfig) (x y : ℓ²(Z.carrier, ℂ)) :
    reflectVec Z (x - y) = reflectVec Z x - reflectVec Z y := by
  ext τ
  simp only [reflectVec_apply, lp.coeFn_sub, Pi.sub_apply]

theorem norm_reflectVec (Z : ZeroConfig) (x : ℓ²(Z.carrier, ℂ)) : ‖reflectVec Z x‖ = ‖x‖ := by
  have h2 : (0 : ℝ) < (2 : ENNReal).toReal := by norm_num
  have h := lp.norm_rpow_eq_tsum h2 (reflectVec Z x)
  have hx := lp.norm_rpow_eq_tsum h2 x
  simp only [reflectVec_apply] at h
  have ht := (reflectEquiv Z).tsum_eq (fun τ => ‖x τ‖ ^ (2 : ENNReal).toReal)
  simp only [reflectEquiv_apply] at ht
  rw [ht, ← hx] at h
  simp only [ENNReal.toReal_ofNat, Real.rpow_two] at h
  rw [← Real.sqrt_sq (norm_nonneg (reflectVec Z x)), h, Real.sqrt_sq (norm_nonneg x)]

theorem reflectVec_single (Z : ZeroConfig) [DecidableEq Z.carrier] (a : Z.carrier) :
    reflectVec Z (lp.single 2 a (1 : ℂ)) = lp.single 2 (reflectCarrier Z a) 1 := by
  ext τ
  simp only [reflectVec_apply, lp.single_apply, Pi.single_apply]
  by_cases h : τ = reflectCarrier Z a
  · subst h
    simp [reflectCarrier_reflectCarrier]
  · have h' : reflectCarrier Z τ ≠ a := fun h'' => h (by rw [← h'', reflectCarrier_reflectCarrier])
    simp [h, h']

/-- **Weil's form is the Krein form** `⟨R X(g), X(f)⟩` of the zero-side coordinates. -/
theorem W_eq_inner (Z : ZeroConfig) (hZ : TemperedConfig Z) (f g : testSpace) :
    Z.W f g = inner ℂ (reflectVec Z (zeroMap Z hZ g)) (zeroMap Z hZ f) := by
  rw [lp.inner_eq_tsum, ZeroConfig.W]
  refine tsum_congr fun τ => ?_
  have hm : Z.mult (reflect (τ : ℂ)) = Z.mult τ := Z.mult_reflect _ τ.2
  have hsq : ((Real.sqrt (Z.mult τ) : ℝ) : ℂ) * (Real.sqrt (Z.mult τ) : ℝ) = (Z.mult τ : ℂ) := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt (Nat.cast_nonneg _), Complex.ofReal_natCast]
  simp only [RCLike.inner_apply', reflectVec_apply, zeroMap_apply, zeroCoord, reflectCarrier,
    hm, gammaOf_reflect, map_mul, Complex.conj_ofReal, ZeroConfig.Wsummand]
  linear_combination (paperFT (↑f) (gammaOf ↑τ) *
    (starRingEnd ℂ) (paperFT (↑g) ((starRingEnd ℂ) (gammaOf ↑τ)))) * hsq.symm

/-! ### Attainment -/

/-- A Gram matrix within `η` of `−2·I` entrywise, with `η · n ≤ 1`, has form `≤ −|x|²`. -/
theorem hermQuad_le_of_near {ι : Type*} [Fintype ι] [DecidableEq ι] (G : Matrix ι ι ℂ) {η : ℝ}
    (hη : η * Fintype.card ι ≤ 1)
    (hG : ∀ i j, ‖G i j - (if i = j then -2 else 0)‖ ≤ η) (x : ι → ℂ) :
    hermQuad G x ≤ -∑ i, ‖x i‖ ^ 2 := by
  rcases isEmpty_or_nonempty ι with hι | ⟨⟨i₀⟩⟩
  · simp [hermQuad, dotProduct]
  have hη0 : 0 ≤ η := (norm_nonneg _).trans (hG i₀ i₀)
  set D : Matrix ι ι ℂ := diagonal fun _ => ((-2 : ℝ) : ℂ) with hD
  set E : Matrix ι ι ℂ := G - D with hE
  have hsplit : hermQuad G x = hermQuad D x + hermQuad E x := by
    have hGDE : G = D + E := by rw [hE]; abel
    rw [hGDE]
    simp only [hermQuad, Matrix.add_mulVec, dotProduct_add, Complex.add_re]
  have hDx : hermQuad D x = -2 * ∑ i, ‖x i‖ ^ 2 := by
    rw [hD, hermQuad_diagonal, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by rw [Complex.normSq_eq_norm_sq]
  have hEij : ∀ i j, ‖E i j‖ ≤ η := fun i j => by
    have hDij : D i j = if i = j then -2 else 0 := by
      simp only [hD, Matrix.diagonal_apply]
      split_ifs <;> push_cast <;> rfl
    rw [hE, Matrix.sub_apply, hDij]
    exact hG i j
  have hEx : hermQuad E x ≤ η * (∑ i, ‖x i‖) ^ 2 := by
    calc hermQuad E x ≤ ‖star x ⬝ᵥ E *ᵥ x‖ := Complex.re_le_norm _
      _ ≤ ∑ i, ‖x i‖ * ∑ j, ‖E i j‖ * ‖x j‖ := by
        simp only [dotProduct, Matrix.mulVec, Pi.star_apply]
        refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
        rw [norm_mul, norm_star]
        exact mul_le_mul_of_nonneg_left ((norm_sum_le _ _).trans
          (Finset.sum_le_sum fun j _ => (norm_mul _ _).le)) (norm_nonneg _)
      _ ≤ ∑ i, ‖x i‖ * ∑ j, η * ‖x j‖ :=
        Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun j _ =>
          mul_le_mul_of_nonneg_right (hEij i j) (norm_nonneg _)) (norm_nonneg _)
      _ = η * (∑ i, ‖x i‖) ^ 2 := by
        simp only [← Finset.mul_sum, ← Finset.sum_mul]
        ring
  have hcs : (∑ i, ‖x i‖) ^ 2 ≤ Fintype.card ι * ∑ i, ‖x i‖ ^ 2 := by
    have := sq_sum_le_card_mul_sum_sq (s := (Finset.univ : Finset ι)) (f := fun i => ‖x i‖)
    simpa [Finset.card_univ] using this
  have hX : 0 ≤ ∑ i, ‖x i‖ ^ 2 := Finset.sum_nonneg fun i _ => by positivity
  have h1 : η * (∑ i, ‖x i‖) ^ 2 ≤ ∑ i, ‖x i‖ ^ 2 := by
    calc η * (∑ i, ‖x i‖) ^ 2 ≤ η * (Fintype.card ι * ∑ i, ‖x i‖ ^ 2) :=
          mul_le_mul_of_nonneg_left hcs hη0
      _ = (η * Fintype.card ι) * ∑ i, ‖x i‖ ^ 2 := by ring
      _ ≤ 1 * ∑ i, ‖x i‖ ^ 2 := mul_le_mul_of_nonneg_right hη hX
      _ = ∑ i, ‖x i‖ ^ 2 := one_mul _
  rw [hsplit, hDx]
  linarith

theorem inner_single_single (Z : ZeroConfig) [DecidableEq Z.carrier] (a c : Z.carrier) :
    inner ℂ (lp.single (E := fun _ : Z.carrier => ℂ) 2 a 1)
      (lp.single (E := fun _ : Z.carrier => ℂ) 2 c 1) = if a = c then 1 else 0 := by
  rw [lp.inner_single_left, lp.single_apply, RCLike.inner_apply', map_one, one_mul,
    Pi.single_apply]

/-- **Attainment.** For any finitely many distinct zeros `ρ_i` right of the line there are
compactly supported `C²` tests on which Weil's form has at least that many negative squares. -/
theorem exists_zeroGram_negIndex_ge (Z : ZeroConfig) (hZ : TemperedConfig Z) {ι : Type*}
    [Fintype ι] [DecidableEq ι] (ρ : ι → ℂ) (hρ : Function.Injective ρ)
    (hR : ∀ i, ρ i ∈ rightZeros Z) :
    ∃ f : ι → ℝ → ℂ, (∀ i, ContDiff ℝ 2 (f i)) ∧ (∀ i, HasCompactSupport (f i)) ∧
      Fintype.card ι ≤ hermNegIndex (zeroGram Z f) := by
  classical
  set r : ι → Z.carrier := fun i => ⟨ρ i, (hR i).1⟩ with hr
  -- the negative vectors `e_ρ − e_{1−ρ̄}` of the Krein form
  set w : ι → ℓ²(Z.carrier, ℂ) := fun i =>
    lp.single 2 (r i) (1 : ℂ) - lp.single 2 (reflectCarrier Z (r i)) 1 with hw
  have hne : ∀ i j, reflectCarrier Z (r j) ≠ r i := fun i j h => by
    have := congrArg (fun t : Z.carrier => (t : ℂ).re) h
    simp only [reflectCarrier, hr, reflect, Complex.sub_re, Complex.one_re, Complex.conj_re] at this
    linarith [(hR i).2, (hR j).2]
  have hrr : ∀ i j, r j = r i ↔ i = j := fun i j =>
    ⟨fun h => (hρ (congrArg Subtype.val h)).symm, fun h => h ▸ rfl⟩
  have hRr : ∀ i j, reflectCarrier Z (r j) = reflectCarrier Z (r i) ↔ i = j := fun i j =>
    ⟨fun h => (hrr i j).mp ((reflectEquiv Z).injective h), fun h => h ▸ rfl⟩
  have hRw : ∀ i j, inner ℂ (reflectVec Z (w j)) (w i) = if i = j then -2 else 0 := by
    intro i j
    simp only [hw, reflectVec_sub, reflectVec_single, reflectCarrier_reflectCarrier, inner_sub_left,
      inner_sub_right, inner_single_single, if_neg (hne i j), if_neg (Ne.symm (hne j i)), hrr,
      hRr]
    split_ifs <;> ring
  have hnw : ∀ i, ‖w i‖ ≤ 2 := fun i => by
    refine (norm_sub_le _ _).trans ?_
    rw [lp.norm_single (by norm_num), lp.norm_single (by norm_num), norm_one]
    norm_num
  -- approximants of the negative vectors
  set k := Fintype.card ι with hk
  set ε : ℝ := 1 / (5 * ((k : ℝ) + 1)) with hε
  have hε0 : 0 < ε := by positivity
  have hε1 : ε ≤ 1 := by
    rw [hε, div_le_one (by positivity)]
    have : (0 : ℝ) ≤ k := Nat.cast_nonneg _
    linarith
  choose g hg using fun i => exists_zeroMap_near Z hZ (w i) hε0
  refine ⟨fun i => (g i : ℝ → ℂ), fun i => (g i).2.1, fun i => (g i).2.2, ?_⟩
  have hentry : ∀ i j, ‖zeroGram Z (fun i => (g i : ℝ → ℂ)) i j - (if i = j then -2 else 0)‖ ≤
      5 * ε := by
    intro i j
    have hGij : zeroGram Z (fun i => (g i : ℝ → ℂ)) i j =
        inner ℂ (reflectVec Z (zeroMap Z hZ (g j))) (zeroMap Z hZ (g i)) := W_eq_inner Z hZ (g i) (g j)
    have hdi : zeroMap Z hZ (g i) = w i + (zeroMap Z hZ (g i) - w i) := by abel
    have hdj : zeroMap Z hZ (g j) = w j + (zeroMap Z hZ (g j) - w j) := by abel
    set ei := zeroMap Z hZ (g i) - w i
    set ej := zeroMap Z hZ (g j) - w j
    have hei : ‖ei‖ < ε := hg i
    have hej : ‖ej‖ < ε := hg j
    rw [hGij, hdi, hdj, reflectVec_add, inner_add_left, inner_add_right, inner_add_right, hRw i j]
    have h1 := (norm_inner_le_norm (𝕜 := ℂ) (reflectVec Z (w j)) ei).trans_eq
      (by rw [norm_reflectVec])
    have h2 := (norm_inner_le_norm (𝕜 := ℂ) (reflectVec Z ej) (w i)).trans_eq
      (by rw [norm_reflectVec])
    have h3 := (norm_inner_le_norm (𝕜 := ℂ) (reflectVec Z ej) ei).trans_eq
      (by rw [norm_reflectVec])
    calc ‖(if i = j then -2 else 0) + inner ℂ (reflectVec Z (w j)) ei +
          (inner ℂ (reflectVec Z ej) (w i) + inner ℂ (reflectVec Z ej) ei) -
            (if i = j then -2 else 0)‖
        = ‖inner ℂ (reflectVec Z (w j)) ei + inner ℂ (reflectVec Z ej) (w i) +
            inner ℂ (reflectVec Z ej) ei‖ := by congr 1; ring
      _ ≤ ‖w j‖ * ‖ei‖ + ‖ej‖ * ‖w i‖ + ‖ej‖ * ‖ei‖ :=
        norm_add₃_le.trans (add_le_add (add_le_add h1 h2) h3)
      _ ≤ 2 * ε + ε * 2 + ε * ε := by
        have := hnw i; have := hnw j
        gcongr
      _ ≤ 5 * ε := by nlinarith
  have hη : 5 * ε * (Fintype.card ι : ℝ) ≤ 1 := by
    rw [← hk, hε]
    have : (0 : ℝ) ≤ k := Nat.cast_nonneg _
    rw [show 5 * (1 / (5 * ((k : ℝ) + 1))) * k = k / (k + 1) by field_simp,
      div_le_one (by positivity)]
    linarith
  have hpd : IsPosDefOn (-(zeroGram Z fun i => (g i : ℝ → ℂ))) ⊤ := fun x _ hx0 => by
    rw [hermQuad_neg]
    obtain ⟨i, hi⟩ := Function.ne_iff.mp hx0
    have hpos : 0 < ∑ i, ‖x i‖ ^ 2 :=
      lt_of_lt_of_le (pow_pos (norm_pos_iff.mpr hi) 2) (Finset.single_le_sum
        (f := fun i => ‖x i‖ ^ 2) (fun i _ => by positivity) (Finset.mem_univ i))
    linarith [hermQuad_le_of_near _ hη hentry x]
  have h1 := finrank_le_posIndex hpd
  rw [finrank_top, Module.finrank_fintype_fun_eq_card] at h1
  rw [hermNegIndex]
  exact h1

/-! ### The law -/

/-- **The Pontryagin law of a tempered configuration.** Weil's form has `n` negative squares on
some family of `n` compactly supported `C²` tests iff the configuration has at least `n` zeros
right of the critical line; together with `negIndex_zeroGram_le_of_tempered`, the largest number of
negative squares is `#{Re ρ > ½}` in `ℕ∞`. -/
theorem pontryagin_law (Z : ZeroConfig) (hZ : TemperedConfig Z) (n : ℕ) :
    (∃ f : Fin n → ℝ → ℂ, (∀ i, ContDiff ℝ 2 (f i)) ∧ (∀ i, HasCompactSupport (f i)) ∧
      n ≤ hermNegIndex (zeroGram Z f)) ↔ (n : ℕ∞) ≤ (rightZeros Z).encard := by
  classical
  constructor
  · rintro ⟨f, hf, hfc, hn⟩
    exact (ENat.coe_le_coe.mpr hn).trans (negIndex_zeroGram_le_of_tempered Z hZ f hf hfc)
  · intro hn
    obtain ⟨t, hts, htn⟩ := Set.exists_subset_encard_eq hn
    have htf : t.Finite := Set.finite_of_encard_eq_coe htn
    have hcard : htf.toFinset.card = n := by
      have h := htf.encard_eq_coe_toFinset_card
      rw [htn] at h
      exact_mod_cast h.symm
    set e := htf.toFinset.equivFin
    set ρ : Fin n → ℂ := fun i => (e.symm (Fin.cast hcard.symm i) : ℂ) with hρdef
    have hρ : Function.Injective ρ := fun i j h =>
      Fin.cast_injective _ (e.symm.injective (Subtype.ext h))
    have hR : ∀ i, ρ i ∈ rightZeros Z := fun i =>
      hts ((Set.Finite.mem_toFinset htf).mp (e.symm (Fin.cast hcard.symm i)).2)
    obtain ⟨f, hf, hfc, hge⟩ := exists_zeroGram_negIndex_ge Z hZ ρ hρ hR
    exact ⟨f, hf, hfc, by simpa using hge⟩

/-- **Kronecker rank one: the Hodge defect is `0` or `∞`.** A tempered configuration invariant
under the vertical translation `ρ ↦ ρ + iP` (the zeros of a lattice system with `log q = 2π/P`)
either has no negative square on any finite family of tests, or arbitrarily many: one zero right of
the line brings all its translates. -/
theorem periodic_pontryagin_dichotomy (Z : ZeroConfig) (hZ : TemperedConfig Z) {P : ℝ}
    (hP : 0 < P) (hper : ∀ ρ ∈ Z.carrier, ρ + I * P ∈ Z.carrier) :
    (∀ (n : ℕ) (f : Fin n → ℝ → ℂ), (∀ i, ContDiff ℝ 2 (f i)) → (∀ i, HasCompactSupport (f i)) →
      hermNegIndex (zeroGram Z f) = 0) ∨
    ∀ n : ℕ, ∃ f : Fin n → ℝ → ℂ, (∀ i, ContDiff ℝ 2 (f i)) ∧ (∀ i, HasCompactSupport (f i)) ∧
      n ≤ hermNegIndex (zeroGram Z f) := by
  rcases (rightZeros Z).eq_empty_or_nonempty with hR | ⟨ρ₀, hρ₀⟩
  · refine Or.inl fun n f hf hfc => ?_
    have h := negIndex_zeroGram_le_of_tempered Z hZ f hf hfc
    rw [hR, Set.encard_empty] at h
    have h0 : hermNegIndex (zeroGram Z f) ≤ 0 := by exact_mod_cast h
    omega
  · refine Or.inr fun n => (pontryagin_law Z hZ n).mpr ?_
    -- all vertical translates of `ρ₀` are zeros right of the line
    have hmem : ∀ k : ℕ, ρ₀ + I * ((k : ℝ) * P) ∈ rightZeros Z := by
      intro k
      induction k with
      | zero => simpa using hρ₀
      | succ k ih =>
        have h := hper _ ih.1
        refine ⟨?_, ?_⟩
        · convert h using 1; push_cast; ring
        · simpa using hρ₀.2
    have hinj : Function.Injective fun k : ℕ => ρ₀ + I * ((k : ℝ) * P) := fun k l hkl => by
      have h1 := congrArg Complex.im hkl
      simp only [Complex.add_im, Complex.mul_im, Complex.mul_re, Complex.I_re, Complex.I_im,
        Complex.ofReal_re, Complex.ofReal_im, zero_mul, one_mul, mul_zero, sub_zero, zero_add,
        add_right_inj] at h1
      have h2 : (k : ℝ) * P = (l : ℝ) * P := by linarith
      exact_mod_cast mul_right_cancel₀ hP.ne' h2
    have hinf : (rightZeros Z).Infinite := Set.infinite_of_injective_forall_mem hinj hmem
    rw [Set.encard_eq_top_iff.mpr hinf]
    exact le_top

/-! ### The scaling surface of `ℤ` -/

/-- **The Hodge defect of the scaling surface of `ℤ` counts the zeros right of the line.** The
arithmetic intersection form has `1 + n` positive squares on the pole plane and some family of `n`
compactly supported `C²` tests iff `ζ` has at least `n` zeros with `Re ρ > ½`. -/
theorem zeta_hodgeDefect_iff (n : ℕ) :
    (∃ f : Fin n → ℝ → ℂ, (∀ i, ContDiff ℝ 2 (f i)) ∧ (∀ i, HasCompactSupport (f i)) ∧
      1 + n ≤ hermPosIndex (intersectionGram (fun k => (ArithmeticFunction.vonMangoldt k : ℝ)) f)) ↔
      (n : ℕ∞) ≤ (rightZeros zetaZeroConfig).encard := by
  rw [← pontryagin_law zetaZeroConfig temperedConfig_zetaZeroConfig n]
  refine exists_congr fun f => ⟨fun ⟨hf, hfc, h⟩ => ⟨hf, hfc, ?_⟩, fun ⟨hf, hfc, h⟩ => ⟨hf, hfc, ?_⟩⟩
  · rw [posIndex_intersectionGram, weilGram_eq_zeroGram f hf hfc] at h
    omega
  · rw [posIndex_intersectionGram, weilGram_eq_zeroGram f hf hfc]
    omega

/-- **`ζ` has infinitely many zeros off the line iff the Hodge defect of its scaling surface is
unbounded.** -/
theorem zeta_rightZeros_infinite_iff :
    (rightZeros zetaZeroConfig).Infinite ↔
      ∀ n : ℕ, ∃ f : Fin n → ℝ → ℂ, (∀ i, ContDiff ℝ 2 (f i)) ∧ (∀ i, HasCompactSupport (f i)) ∧
        1 + n ≤ hermPosIndex (intersectionGram (fun k => (ArithmeticFunction.vonMangoldt k : ℝ)) f) := by
  simp only [zeta_hodgeDefect_iff, ← Set.encard_eq_top_iff]
  constructor
  · intro h n
    rw [h]
    exact le_top
  · intro h
    by_contra hne
    obtain ⟨m, hm⟩ := ENat.ne_top_iff_exists.mp hne
    have := h (m + 1)
    rw [← hm] at this
    norm_cast at this
    omega

end GaloisForLFunctions.ArithmeticCastelnuovoSeveri
