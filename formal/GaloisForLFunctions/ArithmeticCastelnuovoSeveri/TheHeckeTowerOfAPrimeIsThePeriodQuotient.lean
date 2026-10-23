import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.TheHodgeDefectIsCyclic

/-!
# Frobenius at a prime: the Hecke tower of `p` is the period quotient

Over `𝔽_q` the Frobenius span is the scaling surface of the curve modulo the vertical period
`2π/log q`: its defect counts each outer eigenvalue `β = q^{ρ − ½}` once, the scaling surface once per
period (`curveConfig_rightZeros_infinite_iff`). Over `ℚ` every prime gives the same quotient. The
Hecke tower `T_{p^k} g = g(· − k log p)`, `k ∈ ℤ`, of one test has the Toeplitz Gram matrix of the
Lefschetz sequence `W(T_{p^k} g, g)` (`towerGram`), and on the zero side `T_{p^k}` multiplies the
coordinate at `τ` by `β^k`, where `β = p^{τ − ½}` is the **Frobenius eigenvalue** of `τ` at `p`
(`frobEig`, `towerVec_apply`). Zeros differing by a multiple of `2πi/log p` share an eigenvalue.

* **Crude bound** (`negIndex_towerGram_le`). For every tempered configuration and every test, every
  window of the tower has at most as many negative squares as there are distinct eigenvalues
  `p^{ρ − ½}` of zeros right of the line: a combination killing every outer eigenvalue has
  zero-side coordinates vanishing at the right zeros, where the Krein form is nonnegative
  (`re_inner_reflect_self_nonneg`).
* **Class separation** (`classSum_eq_zero_of_orthogonal_tower`). If the outer eigenvalues are
  finitely many, a vector orthogonal to the whole tower has zero sum over every eigenvalue class.
  The off-line classes are annihilated by a polynomial in the shift, and the remaining class is
  extracted by a Cesàro mean (`tsum_ite_eq_zero_of_moments`).
* **The tower Pontryagin law** (`tower_pontryagin_law`). With finitely many outer eigenvalues, the
  largest number of negative squares on the tower is exactly the number of outer eigenvalues `b`
  whose **Frobenius weight** `W_b = Σ_{β(τ) = b} X_τ(g) conj X_{1−τ̄}(g)` (`frobWeight`) is
  nonzero (`visibleEig`). A class with `W_b = 0` is invisible; each other class carries the
  hyperbolic pair `e_b − λ_b e_{1/b̄}` with square `−2|W_b|` (`inner_reflect_eigTarget`).

This covers configurations with finitely many right zeros at every prime and periodic
configurations at the commensurable prime, as over `𝔽_q`. A single prime sees the Hodge defect
only up to the period, the Kronecker-rank-one quotient; two primes see all of it
(`riemannHypothesis_iff_twoPrime_negIndex_eq_zero`).
-/

open Complex Matrix Finset Filter Topology
open scoped ComplexConjugate lp Classical
open Zeta23 GaloisForLFunctions.HTGeometry
open GaloisForLFunctions.SquareRootThreshold (TemperedConfig)

noncomputable section

namespace GaloisForLFunctions.ArithmeticCastelnuovoSeveri

/-! ### Frobenius eigenvalues -/

theorem I_mul_gammaOf (τ : ℂ) : I * gammaOf τ = τ - 1 / 2 := by
  rw [gammaOf, mul_div_assoc', mul_div_cancel_left₀ _ I_ne_zero]

/-- The Frobenius eigenvalue of a zero at scale `ℓ = log p`: `β = e^{ℓ(τ − ½)} = p^{τ − ½}`. -/
def frobEig (ℓ : ℝ) (τ : ℂ) : ℂ := cexp (ℓ * (τ - 1 / 2))

theorem frobEig_ne_zero (ℓ : ℝ) (τ : ℂ) : frobEig ℓ τ ≠ 0 := Complex.exp_ne_zero _

theorem norm_frobEig (ℓ : ℝ) (τ : ℂ) : ‖frobEig ℓ τ‖ = Real.exp (ℓ * (τ.re - 1 / 2)) := by
  rw [frobEig, Complex.norm_exp]
  congr 1
  simp [Complex.mul_re]

/-- The reflection `τ ↦ 1 − τ̄` sends `β` to `1/β̄`. -/
theorem frobEig_reflect (ℓ : ℝ) (τ : ℂ) : frobEig ℓ (reflect τ) = (conj (frobEig ℓ τ))⁻¹ := by
  rw [frobEig, frobEig, ← Complex.exp_conj, ← Complex.exp_neg]
  congr 1
  simp only [reflect, map_mul, map_sub, Complex.conj_ofReal, map_one, map_div₀, map_ofNat]
  ring

theorem one_lt_norm_frobEig_iff {ℓ : ℝ} (hℓ : 0 < ℓ) (τ : ℂ) :
    1 < ‖frobEig ℓ τ‖ ↔ 1 / 2 < τ.re := by
  rw [norm_frobEig, ← Real.exp_zero, Real.exp_lt_exp]
  constructor <;> intro h <;> nlinarith

theorem norm_frobEig_lt_one_iff {ℓ : ℝ} (hℓ : 0 < ℓ) (τ : ℂ) :
    ‖frobEig ℓ τ‖ < 1 ↔ τ.re < 1 / 2 := by
  rw [norm_frobEig, ← Real.exp_zero, Real.exp_lt_exp]
  constructor <;> intro h <;> nlinarith

theorem norm_frobEig_eq_one {ℓ : ℝ} {τ : ℂ} (h : τ.re = 1 / 2) : ‖frobEig ℓ τ‖ = 1 := by
  rw [norm_frobEig, h, sub_self, mul_zero, Real.exp_zero]

theorem reflectCarrier_eq_self {Z : ZeroConfig} {τ : Z.carrier} (h : (τ : ℂ).re = 1 / 2) :
    reflectCarrier Z τ = τ :=
  Subtype.ext (by
    apply Complex.ext
    · norm_num [reflectCarrier, reflect, h]
    · simp [reflectCarrier, reflect])

theorem re_reflectCarrier (Z : ZeroConfig) (τ : Z.carrier) :
    ((reflectCarrier Z τ : Z.carrier) : ℂ).re = 1 - (τ : ℂ).re := by
  simp [reflectCarrier, reflect]

/-! ### The tower -/

/-- The zero-side coordinates of the tower translate `T_{p^k} g`, `ℓ = log p`. -/
def towerVec (Z : ZeroConfig) (hZ : TemperedConfig Z) {g : ℝ → ℂ} (hg : ContDiff ℝ 2 g)
    (hgc : HasCompactSupport g) (ℓ : ℝ) (k : ℤ) : ℓ²(Z.carrier, ℂ) :=
  heckeVec Z hZ hg hgc ((k : ℝ) * ℓ)

/-- On the zero side `T_{p^k}` multiplies the coordinate at `τ` by `β^k`. -/
theorem towerVec_apply (Z : ZeroConfig) (hZ : TemperedConfig Z) {g : ℝ → ℂ}
    (hg : ContDiff ℝ 2 g) (hgc : HasCompactSupport g) (ℓ : ℝ) (k : ℤ) (τ : Z.carrier) :
    towerVec Z hZ hg hgc ℓ k τ = frobEig ℓ τ ^ k * zeroCoord Z g τ := by
  show zeroCoord Z (translate ((k : ℝ) * ℓ) g) τ = _
  rw [zeroCoord_translate, frobEig, ← Complex.exp_int_mul, I_mul_gammaOf]
  congr 2
  push_cast
  ring

/-- The Gram matrix of a finite window `K` of the Hecke tower at scale `ℓ`. -/
def towerGram (Z : ZeroConfig) (g : ℝ → ℂ) (ℓ : ℝ) (K : Finset ℤ) : Matrix K K ℂ :=
  zeroGram Z fun k : K => translate (((k : ℤ) : ℝ) * ℓ) g

/-! ### The Krein form on a window -/

/-- **The Krein form is nonnegative on vectors vanishing at the right zeros.** -/
theorem re_inner_reflect_self_nonneg (Z : ZeroConfig) (Y : ℓ²(Z.carrier, ℂ))
    (hY : ∀ τ : Z.carrier, 1 / 2 < (τ : ℂ).re → Y τ = 0) :
    0 ≤ (inner ℂ (reflectVec Z Y) Y).re := by
  rw [lp.inner_eq_tsum, Complex.re_tsum (lp.summable_inner _ _)]
  refine tsum_nonneg fun τ => ?_
  simp only [RCLike.inner_apply', reflectVec_apply]
  rcases lt_trichotomy (τ : ℂ).re (1 / 2) with h | h | h
  · have hr : 1 / 2 < ((reflectCarrier Z τ : Z.carrier) : ℂ).re := by
      rw [re_reflectCarrier]; linarith
    rw [hY _ hr]; simp
  · rw [reflectCarrier_eq_self h, Complex.conj_mul', ← Complex.ofReal_pow, Complex.ofReal_re]
    positivity
  · rw [hY τ h]; simp

/-- **The quadratic form of a Weil Gram matrix** is the Krein form of the combination with
conjugated coefficients. -/
theorem hermQuad_zeroGram_eq (Z : ZeroConfig) (hZ : TemperedConfig Z) {ι : Type*} [Fintype ι]
    (t : ι → testSpace) (x : ι → ℂ) :
    hermQuad (zeroGram Z fun i => (t i : ℝ → ℂ)) x =
      (inner ℂ (reflectVec Z (∑ i, conj (x i) • zeroMap Z hZ (t i)))
        (∑ i, conj (x i) • zeroMap Z hZ (t i))).re := by
  have h := congrFun (congrFun
    (zeroGram_comb Z hZ t (Matrix.of fun (_ : Unit) i => conj (x i))) ()) ()
  simp only [zeroGram, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.of_apply,
    RCLike.star_def, Complex.conj_conj] at h
  rw [W_eq_inner Z hZ, map_sum] at h
  simp only [map_smul] at h
  rw [h, hermQuad]
  congr 1
  simp only [dotProduct, Matrix.mulVec, zeroGram, Pi.star_apply, RCLike.star_def,
    Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

/-- The coordinates of a combination `Σ_k x̄_k T_{p^k} g`: `X_τ(g) · E(β(τ))`. -/
theorem towerComb_apply (Z : ZeroConfig) (hZ : TemperedConfig Z) {g : ℝ → ℂ}
    (hg : ContDiff ℝ 2 g) (hgc : HasCompactSupport g) (ℓ : ℝ) (K : Finset ℤ) (x : K → ℂ)
    (τ : Z.carrier) :
    (∑ k : K, conj (x k) • zeroMap Z hZ (translateTest hg hgc (((k : ℤ) : ℝ) * ℓ))) τ =
      zeroCoord Z g τ * ∑ k : K, conj (x k) * frobEig ℓ τ ^ (k : ℤ) := by
  rw [lp.coeFn_sum, Finset.sum_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [lp.coeFn_smul, Pi.smul_apply, smul_eq_mul]
  have := towerVec_apply Z hZ hg hgc ℓ k τ
  simp only [towerVec, heckeVec] at this
  rw [this]
  ring

/-- **Crude bound.** A window of the tower has at most as many negative squares as there are
distinct outer eigenvalues `p^{ρ − ½}`. -/
theorem negIndex_towerGram_le (Z : ZeroConfig) (hZ : TemperedConfig Z) {g : ℝ → ℂ}
    (hg : ContDiff ℝ 2 g) (hgc : HasCompactSupport g) (ℓ : ℝ) (K : Finset ℤ) :
    (hermNegIndex (towerGram Z g ℓ K) : ℕ∞) ≤ (frobEig ℓ '' rightZeros Z).encard := by
  by_cases hO : (frobEig ℓ '' rightZeros Z).Finite
  swap
  · rw [Set.Infinite.encard_eq hO]; exact le_top
  set O := hO.toFinset
  rw [hO.encard_eq_coe_toFinset_card]
  refine ENat.coe_le_coe.mpr ?_
  -- evaluation at the outer eigenvalues
  let Ψ : (K → ℂ) →ₗ[ℂ] (O → ℂ) :=
    { toFun := fun x b => ∑ k : K, x k * conj (b : ℂ) ^ (k : ℤ)
      map_add' := fun x y => by
        funext b; simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib]
      map_smul' := fun c x => by
        funext b; simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum,
          mul_assoc] }
  have hker : ∀ x, Ψ x = 0 → 0 ≤ hermQuad (towerGram Z g ℓ K) x := by
    intro x hx
    have hrw : towerGram Z g ℓ K =
        zeroGram Z fun k : K => (translateTest hg hgc (((k : ℤ) : ℝ) * ℓ) : ℝ → ℂ) := rfl
    rw [hrw, hermQuad_zeroGram_eq Z hZ]
    refine re_inner_reflect_self_nonneg Z _ fun τ hτ => ?_
    rw [towerComb_apply]
    have hb : frobEig ℓ τ ∈ O := hO.mem_toFinset.mpr ⟨τ, ⟨τ.2, hτ⟩, rfl⟩
    have h0 := congrFun hx ⟨_, hb⟩
    simp only [Ψ, LinearMap.coe_mk, AddHom.coe_mk, Pi.zero_apply] at h0
    have h1 : ∑ k : K, conj (x k) * frobEig ℓ τ ^ (k : ℤ) =
        conj (∑ k : K, x k * conj (frobEig ℓ τ) ^ (k : ℤ)) := by
      simp only [map_sum, map_mul, map_zpow₀, Complex.conj_conj]
    rw [h1, h0, map_zero, mul_zero]
  obtain ⟨V, hrank, hV⟩ := exists_isPosDefOn_finrank_eq_posIndex (-(towerGram Z g ℓ K))
  have hinj : LinearMap.ker (Ψ.domRestrict V) = ⊥ := by
    rw [LinearMap.ker_eq_bot']
    intro x hx
    by_contra hx0
    have h1 := hV x x.2 (fun h => hx0 (Subtype.ext h))
    rw [hermQuad_neg] at h1
    linarith [hker x hx]
  have h := LinearMap.finrank_le_finrank_of_injective (LinearMap.ker_eq_bot.mp hinj)
  rw [Module.finrank_fintype_fun_eq_card, Fintype.card_coe] at h
  unfold hermNegIndex
  rw [← hrank]
  exact h

/-! ### Frobenius weights -/

/-- The outer Frobenius eigenvalues at scale `ℓ`: `p^{ρ − ½}` for the zeros right of the line. -/
def outerEig (Z : ZeroConfig) (ℓ : ℝ) : Set ℂ := frobEig ℓ '' rightZeros Z

/-- The **Frobenius weight** of an eigenvalue `b`: `W_b = Σ_{β(τ) = b} X_τ(g) conj X_{1−τ̄}(g)`. -/
def frobWeight (Z : ZeroConfig) (g : ℝ → ℂ) (ℓ : ℝ) (b : ℂ) : ℂ :=
  ∑' τ : Z.carrier, if frobEig ℓ τ = b then
    zeroCoord Z g τ * conj (zeroCoord Z g (reflectCarrier Z τ)) else 0

/-- The **visible eigenvalues**: outer eigenvalues of nonzero Frobenius weight. -/
def visibleEig (Z : ZeroConfig) (g : ℝ → ℂ) (ℓ : ℝ) (hO : (outerEig Z ℓ).Finite) : Finset ℂ :=
  hO.toFinset.filter fun b => frobWeight Z g ℓ b ≠ 0

theorem summable_sq_zeroCoord (Z : ZeroConfig) (hZ : TemperedConfig Z) {g : ℝ → ℂ}
    (hg : ContDiff ℝ 2 g) (hgc : HasCompactSupport g) :
    Summable fun τ : Z.carrier => ‖zeroCoord Z g τ‖ ^ 2 := by
  have h := (memℓp_zeroCoord Z hZ hg hgc).summable (by norm_num : (0 : ℝ) < (2 : ENNReal).toReal)
  simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using h

theorem summable_sq_zeroCoord_reflect (Z : ZeroConfig) (hZ : TemperedConfig Z) {g : ℝ → ℂ}
    (hg : ContDiff ℝ 2 g) (hgc : HasCompactSupport g) :
    Summable fun τ : Z.carrier => ‖zeroCoord Z g (reflectCarrier Z τ)‖ ^ 2 :=
  (reflectEquiv Z).summable_iff.mpr (summable_sq_zeroCoord Z hZ hg hgc)

/-- The products `X_τ conj X_{1−τ̄}` are absolutely summable. -/
theorem summable_zeroCoord_mul_reflect (Z : ZeroConfig) (hZ : TemperedConfig Z) {g : ℝ → ℂ}
    (hg : ContDiff ℝ 2 g) (hgc : HasCompactSupport g) :
    Summable fun τ : Z.carrier =>
      ‖zeroCoord Z g τ * conj (zeroCoord Z g (reflectCarrier Z τ))‖ := by
  refine Summable.of_nonneg_of_le (fun τ => norm_nonneg _) (fun τ => ?_)
    (((summable_sq_zeroCoord Z hZ hg hgc).add
      (summable_sq_zeroCoord_reflect Z hZ hg hgc)).div_const 2)
  rw [norm_mul, Complex.norm_conj]
  nlinarith [sq_nonneg (‖zeroCoord Z g τ‖ - ‖zeroCoord Z g (reflectCarrier Z τ)‖)]

/-! ### Class separation -/

/-- The Cesàro mean `A_N(z) = (1/N) Σ_{n<N} z^n`. -/
def cesaro (N : ℕ) (z : ℂ) : ℂ := (N : ℂ)⁻¹ * ∑ n ∈ range N, z ^ n

theorem norm_cesaro_le {z : ℂ} (hz : ‖z‖ ≤ 1) (N : ℕ) : ‖cesaro N z‖ ≤ 1 := by
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · simp [cesaro]
  have hs : ‖∑ n ∈ range N, z ^ n‖ ≤ N := by
    refine (norm_sum_le _ _).trans ?_
    calc ∑ n ∈ range N, ‖z ^ n‖ ≤ ∑ _n ∈ range N, (1 : ℝ) :=
          Finset.sum_le_sum fun n _ => by rw [norm_pow]; exact pow_le_one₀ (norm_nonneg _) hz
      _ = N := by simp
  rw [cesaro, norm_mul, norm_inv, Complex.norm_natCast]
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  calc (N : ℝ)⁻¹ * ‖∑ n ∈ range N, z ^ n‖ ≤ (N : ℝ)⁻¹ * N :=
        mul_le_mul_of_nonneg_left hs (inv_nonneg.mpr hNpos.le)
    _ = 1 := inv_mul_cancel₀ hNpos.ne'

/-- **Cesàro limit**: `A_N(1) = 1` and `A_N(z) → 0` for `|z| ≤ 1`, `z ≠ 1`. -/
theorem tendsto_cesaro {z : ℂ} (hz : ‖z‖ ≤ 1) :
    Tendsto (fun N => cesaro N z) atTop (𝓝 (if z = 1 then 1 else 0)) := by
  split_ifs with h1
  · subst h1
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_ge_atTop 1] with N hN
    have hN0 : (N : ℂ) ≠ 0 := by exact_mod_cast (Nat.one_le_iff_ne_zero.mp hN)
    simp [cesaro, inv_mul_cancel₀ hN0]
  · have hz1 : z - 1 ≠ 0 := sub_ne_zero.mpr h1
    have hbound : ∀ N : ℕ, 1 ≤ N → ‖cesaro N z‖ ≤ 2 / ‖z - 1‖ * (N : ℝ)⁻¹ := by
      intro N hN
      have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
      rw [cesaro, geom_sum_eq h1, norm_mul, norm_div, norm_inv, Complex.norm_natCast]
      have hnum : ‖z ^ N - 1‖ ≤ 2 := by
        refine (norm_sub_le _ _).trans ?_
        rw [norm_pow, norm_one]
        linarith [pow_le_one₀ (norm_nonneg z) hz (n := N)]
      have hpos : 0 < ‖z - 1‖ := norm_pos_iff.mpr hz1
      calc (N : ℝ)⁻¹ * (‖z ^ N - 1‖ / ‖z - 1‖) ≤ (N : ℝ)⁻¹ * (2 / ‖z - 1‖) :=
            mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right hnum hpos.le)
              (inv_nonneg.mpr hNpos.le)
        _ = 2 / ‖z - 1‖ * (N : ℝ)⁻¹ := mul_comm _ _
    have hlim : Tendsto (fun N : ℕ => 2 / ‖z - 1‖ * (N : ℝ)⁻¹) atTop (𝓝 0) := by
      simpa using (tendsto_inv_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul (2 / ‖z - 1‖)
    refine squeeze_zero_norm' ?_ hlim
    filter_upwards [eventually_ge_atTop 1] with N hN using hbound N hN

/-- **Extraction of a class by Cesàro means.** If `Σ_τ r_τ z_τ^n = 0` for every `n ≥ 0`, with
`Σ |r_τ| < ∞` and `|z_τ| ≤ 1` wherever `r_τ ≠ 0`, then the total weight of `z_τ = 1` vanishes. -/
theorem tsum_ite_eq_zero_of_moments {T : Type*} {r z : T → ℂ} (hr : Summable fun τ => ‖r τ‖)
    (hz : ∀ τ, r τ ≠ 0 → ‖z τ‖ ≤ 1) (hm : ∀ n : ℕ, ∑' τ, r τ * z τ ^ n = 0) :
    ∑' τ, (if z τ = 1 then r τ else 0) = 0 := by
  have hsum : ∀ n : ℕ, Summable fun τ => r τ * z τ ^ n := fun n =>
    Summable.of_norm_bounded hr fun τ => by
      by_cases h0 : r τ = 0
      · simp [h0]
      · rw [norm_mul, norm_pow]
        exact mul_le_of_le_one_right (norm_nonneg _) (pow_le_one₀ (norm_nonneg _) (hz τ h0))
  have h0 : ∀ N : ℕ, ∑' τ, r τ * cesaro N (z τ) = 0 := fun N => by
    have e : ∀ τ, r τ * cesaro N (z τ) = (N : ℂ)⁻¹ * ∑ n ∈ range N, r τ * z τ ^ n := fun τ => by
      rw [cesaro, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun n _ => by ring
    simp only [e]
    rw [tsum_mul_left, Summable.tsum_finsetSum fun n _ => hsum n]
    simp [hm]
  have hlim := tendsto_tsum_of_dominated_convergence (𝓕 := atTop)
    (f := fun N τ => r τ * cesaro N (z τ)) (g := fun τ => if z τ = 1 then r τ else 0)
    (bound := fun τ => ‖r τ‖) hr (fun τ => ?_) (Eventually.of_forall fun N τ => ?_)
  · have hc : (fun N => ∑' τ, r τ * cesaro N (z τ)) = fun _ => 0 := funext h0
    rw [hc] at hlim
    exact (tendsto_nhds_unique tendsto_const_nhds hlim).symm
  · by_cases hr0 : r τ = 0
    · simp only [hr0, zero_mul, ite_self]; exact tendsto_const_nhds
    · have h := (tendsto_cesaro (hz τ hr0)).const_mul (r τ)
      convert h using 2
      split_ifs <;> simp
  · by_cases hr0 : r τ = 0
    · simp [hr0]
    · rw [norm_mul]
      exact mul_le_of_le_one_right (norm_nonneg _) (norm_cesaro_le (hz τ hr0) N)

/-- Every off-line point has its conjugate eigenvalue among the conjugates of the outer eigenvalues
and of their reflections. -/
theorem conj_frobEig_mem_offVals (Z : ZeroConfig) {ℓ : ℝ} (hO : (outerEig Z ℓ).Finite)
    (τ : Z.carrier) (hτ : (τ : ℂ).re ≠ 1 / 2) :
    conj (frobEig ℓ τ) ∈
      (hO.toFinset ∪ hO.toFinset.image fun d => (conj d)⁻¹).image (starRingEnd ℂ) := by
  refine Finset.mem_image.mpr ⟨frobEig ℓ τ, ?_, rfl⟩
  rcases lt_or_gt_of_ne hτ with h | h
  · refine Finset.mem_union_right _ (Finset.mem_image.mpr ⟨frobEig ℓ (reflect τ), ?_, ?_⟩)
    · refine hO.mem_toFinset.mpr ⟨reflect τ, ⟨Z.reflect_mem _ τ.2, ?_⟩, rfl⟩
      simp only [reflect, Complex.sub_re, Complex.one_re, Complex.conj_re]; linarith
    · have h' := frobEig_reflect ℓ (reflect (τ : ℂ))
      rw [show reflect (reflect (τ : ℂ)) = τ by simp [reflect]] at h'
      exact h'.symm
  · exact Finset.mem_union_left _ (hO.mem_toFinset.mpr ⟨τ, ⟨τ.2, h⟩, rfl⟩)

/-- **Class separation.** If the outer eigenvalues are finitely many, a vector orthogonal to every
tower translate has zero sum `Σ_{β(τ) = b} conj X_τ(g) a_τ` over every eigenvalue class `b`. -/
theorem classSum_eq_zero_of_orthogonal_tower (Z : ZeroConfig) (hZ : TemperedConfig Z)
    {g : ℝ → ℂ} (hg : ContDiff ℝ 2 g) (hgc : HasCompactSupport g) {ℓ : ℝ} (hℓ : 0 < ℓ)
    (hO : (outerEig Z ℓ).Finite) (a : ℓ²(Z.carrier, ℂ))
    (ha : ∀ k : ℤ, inner ℂ (towerVec Z hZ hg hgc ℓ k) a = 0) (b : ℂ) :
    ∑' τ : Z.carrier, (if frobEig ℓ τ = b then conj (zeroCoord Z g τ) * a τ else 0) = 0 := by
  by_cases hb0 : b = 0
  · simp [hb0, frobEig_ne_zero]
  set q : Z.carrier → ℂ := fun τ => conj (zeroCoord Z g τ) * a τ with hq
  set c : Z.carrier → ℂ := fun τ => conj (frobEig ℓ τ) with hc
  have hc0 : ∀ τ, c τ ≠ 0 := fun τ => (map_ne_zero _).mpr (frobEig_ne_zero ℓ τ)
  have hcn : ∀ τ, ‖c τ‖ = ‖frobEig ℓ τ‖ := fun τ => Complex.norm_conj _
  have hqs : Summable fun τ => ‖q τ‖ := by
    have h2 := (lp.memℓp a).summable (by norm_num : (0 : ℝ) < (2 : ENNReal).toReal)
    simp only [ENNReal.toReal_ofNat, Real.rpow_two] at h2
    refine Summable.of_nonneg_of_le (fun τ => norm_nonneg _) (fun τ => ?_)
      (((summable_sq_zeroCoord Z hZ hg hgc).add h2).div_const 2)
    simp only [hq, norm_mul, Complex.norm_conj]
    nlinarith [sq_nonneg (‖zeroCoord Z g τ‖ - ‖a τ‖)]
  -- `|c_τ| ≤ e^{ℓ/2}`
  have hcb : ∀ τ : Z.carrier, ‖c τ‖ ≤ Real.exp (ℓ / 2) := fun τ => by
    rw [hcn, norm_frobEig, Real.exp_le_exp]
    have := (Z.strip _ τ.2).2
    nlinarith
  have hcb' : ∀ τ : Z.carrier, ‖(c τ)⁻¹‖ ≤ Real.exp (ℓ / 2) := fun τ => by
    rw [norm_inv, hcn, norm_frobEig, ← Real.exp_neg, Real.exp_le_exp]
    have := (Z.strip _ τ.2).1
    nlinarith
  have hpow : ∀ (τ : Z.carrier) (k : ℤ), ‖c τ ^ k‖ ≤ Real.exp (ℓ / 2) ^ k.natAbs := fun τ k => by
    obtain ⟨n, rfl | rfl⟩ := Int.eq_nat_or_neg k
    · rw [zpow_natCast, norm_pow, Int.natAbs_natCast]
      exact pow_le_pow_left₀ (norm_nonneg _) (hcb τ) _
    · rw [_root_.zpow_neg, zpow_natCast, ← inv_pow, norm_pow, Int.natAbs_neg, Int.natAbs_natCast]
      exact pow_le_pow_left₀ (norm_nonneg _) (hcb' τ) _
  have hsumk : ∀ k : ℤ, Summable fun τ => q τ * c τ ^ k := fun k =>
    Summable.of_norm_bounded (hqs.mul_right (Real.exp (ℓ / 2) ^ k.natAbs)) fun τ => by
      rw [norm_mul]; exact mul_le_mul_of_nonneg_left (hpow τ k) (norm_nonneg _)
  -- the moments vanish
  have hm : ∀ k : ℤ, ∑' τ, q τ * c τ ^ k = 0 := fun k => by
    have h := ha k
    rw [lp.inner_eq_tsum] at h
    simpa only [RCLike.inner_apply', towerVec_apply, map_mul, map_zpow₀, hq, hc, mul_comm,
      mul_left_comm, mul_assoc] using h
  -- annihilate the other off-line classes
  set offVals := (hO.toFinset ∪ hO.toFinset.image fun d => (conj d)⁻¹).image (starRingEnd ℂ)
  set c₀ : ℂ := conj b with hc₀
  set P : Polynomial ℂ := ∏ d ∈ offVals.erase c₀, (Polynomial.X - Polynomial.C d)
  have hP0 : P.eval c₀ ≠ 0 := by
    rw [Polynomial.eval_prod, Finset.prod_ne_zero_iff]
    intro d hd
    simp only [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C]
    exact sub_ne_zero.mpr (Ne.symm (Finset.ne_of_mem_erase hd))
  have hPoff : ∀ τ : Z.carrier, (τ : ℂ).re ≠ 1 / 2 → c τ ≠ c₀ → P.eval (c τ) = 0 := by
    intro τ hτ hne
    rw [Polynomial.eval_prod]
    exact Finset.prod_eq_zero (Finset.mem_erase.mpr ⟨hne, conj_frobEig_mem_offVals Z hO τ hτ⟩)
      (by simp)
  have hmP : ∀ k : ℤ, ∑' τ, q τ * P.eval (c τ) * c τ ^ k = 0 := fun k => by
    have e : ∀ τ, q τ * P.eval (c τ) * c τ ^ k =
        ∑ j ∈ range (P.natDegree + 1), P.coeff j * (q τ * c τ ^ ((j : ℤ) + k)) := fun τ => by
      rw [Polynomial.eval_eq_sum_range, Finset.mul_sum, Finset.sum_mul]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [zpow_add₀ (hc0 τ), zpow_natCast]
      ring
    simp only [e]
    rw [Summable.tsum_finsetSum fun j _ => (hsumk _).mul_left _]
    simp [tsum_mul_left, hm]
  -- `P(c_τ)` is bounded
  obtain ⟨B, hB⟩ : ∃ B, ∀ τ : Z.carrier, ‖P.eval (c τ)‖ ≤ B := by
    obtain ⟨B, hB⟩ := (isCompact_closedBall (0 : ℂ) (Real.exp (ℓ / 2))).exists_bound_of_continuousOn
      (P.continuous.continuousOn (s := Metric.closedBall 0 (Real.exp (ℓ / 2))))
    exact ⟨B, fun τ => hB _ (mem_closedBall_zero_iff.mpr (hcb τ))⟩
  set r : Z.carrier → ℂ := fun τ => q τ * P.eval (c τ) with hr
  have hrs : Summable fun τ => ‖r τ‖ :=
    Summable.of_norm_bounded (hqs.mul_right B) fun τ => by
      simp only [hr, norm_mul, norm_norm]
      exact mul_le_mul_of_nonneg_left (hB τ) (norm_nonneg _)
  -- a contributing point is on the line or in the class of `c₀`
  have hcontrib : ∀ τ : Z.carrier, r τ ≠ 0 → (τ : ℂ).re = 1 / 2 ∨ c τ = c₀ := by
    intro τ hτ
    by_contra hcon
    push Not at hcon
    exact hτ (by simp only [hr, hPoff τ hcon.1 hcon.2, mul_zero])
  have hc₀0 : c₀ ≠ 0 := (map_ne_zero _).mpr hb0
  -- the class weight `P(c₀) · Σ_{c_τ = c₀} q_τ` vanishes
  have hclass : ∑' τ, (if c τ = c₀ then r τ else 0) = 0 := by
    rcases le_or_gt 1 ‖c₀‖ with h1 | h1
    · have hzz := tsum_ite_eq_zero_of_moments (r := r) (z := fun τ => c τ / c₀) hrs
        (fun τ hτ => by
          rw [norm_div, div_le_one (norm_pos_iff.mpr hc₀0)]
          rcases hcontrib τ hτ with hon | heq
          · rw [hcn, norm_frobEig_eq_one hon]; exact h1
          · rw [heq])
        (fun n => by
          have e : ∀ τ, r τ * (c τ / c₀) ^ n = (c₀ ^ n)⁻¹ * (q τ * P.eval (c τ) * c τ ^ (n : ℤ)) :=
            fun τ => by
              have := hc0 τ
              rw [div_pow, zpow_natCast]; simp only [hr]; field_simp
          simp only [e, tsum_mul_left, hmP, mul_zero])
      simpa only [div_eq_one_iff_eq hc₀0] using hzz
    · have hzz := tsum_ite_eq_zero_of_moments (r := r) (z := fun τ => c₀ / c τ) hrs
        (fun τ hτ => by
          rw [norm_div, div_le_one (norm_pos_iff.mpr (hc0 τ))]
          rcases hcontrib τ hτ with hon | heq
          · rw [hcn, norm_frobEig_eq_one hon]; exact h1.le
          · rw [heq])
        (fun n => by
          have e : ∀ τ, r τ * (c₀ / c τ) ^ n = c₀ ^ n * (q τ * P.eval (c τ) * c τ ^ (-(n : ℤ))) :=
            fun τ => by
              have := hc0 τ
              rw [div_pow, _root_.zpow_neg, zpow_natCast]; simp only [hr]; field_simp
          simp only [e, tsum_mul_left, hmP, mul_zero])
      have e : ∀ τ, (c₀ / c τ = 1) ↔ (c τ = c₀) := fun τ => by
        rw [div_eq_one_iff_eq (hc0 τ), eq_comm]
      simpa only [e] using hzz
  have hsplit : ∑' τ, (if c τ = c₀ then r τ else 0) =
      P.eval c₀ * ∑' τ, (if c τ = c₀ then q τ else 0) := by
    rw [← tsum_mul_left]
    refine tsum_congr fun τ => ?_
    split_ifs with h
    · simp only [hr, h]; ring
    · simp
  rw [hsplit] at hclass
  have hq0 := (mul_eq_zero.mp hclass).resolve_left hP0
  have e : ∀ τ : Z.carrier, (c τ = c₀) ↔ (frobEig ℓ τ = b) := fun τ => by
    simp only [hc, hc₀]
    exact (starRingEnd ℂ).injective.eq_iff
  simpa only [e, hq] using hq0

/-! ### The hyperbolic pairs of the visible eigenvalues -/

/-- The class indicator `𝟙[β(τ) = b]`. -/
def eigInd (ℓ : ℝ) (b : ℂ) (τ : ℂ) : ℂ := if frobEig ℓ τ = b then 1 else 0

/-- The reflected eigenvalue `b̃ = 1/b̄`. -/
def reflEig (b : ℂ) : ℂ := (conj b)⁻¹

theorem reflEig_reflEig (b : ℂ) : reflEig (reflEig b) = b := by
  simp [reflEig, map_inv₀]

theorem eigInd_reflect (ℓ : ℝ) (b τ : ℂ) : eigInd ℓ b (reflect τ) = eigInd ℓ (reflEig b) τ := by
  simp only [eigInd, frobEig_reflect, reflEig]
  congr 1
  apply propext
  constructor
  · intro h; rw [← h]; simp [map_inv₀]
  · intro h; rw [h]; simp [map_inv₀]

theorem norm_eigInd_le (ℓ : ℝ) (b τ : ℂ) : ‖eigInd ℓ b τ‖ ≤ 1 := by
  unfold eigInd; split_ifs <;> simp

/-- The normalization `1/√|W_b|` of the negative vector of `b`. -/
def eigScale (Z : ZeroConfig) (g : ℝ → ℂ) (ℓ : ℝ) (b : ℂ) : ℂ :=
  ((Real.sqrt ‖frobWeight Z g ℓ b‖ : ℝ) : ℂ)⁻¹

/-- The phase `λ_b = W_b/|W_b|` of the negative vector of `b`. -/
def eigPhase (Z : ZeroConfig) (g : ℝ → ℂ) (ℓ : ℝ) (b : ℂ) : ℂ :=
  frobWeight Z g ℓ b / ((‖frobWeight Z g ℓ b‖ : ℝ) : ℂ)

theorem norm_eigPhase_le (Z : ZeroConfig) (g : ℝ → ℂ) (ℓ : ℝ) (b : ℂ) :
    ‖eigPhase Z g ℓ b‖ ≤ 1 := by
  unfold eigPhase
  rcases eq_or_ne (frobWeight Z g ℓ b) 0 with h | h
  · simp [h]
  · rw [norm_div, Complex.norm_real, norm_norm, div_self (norm_ne_zero_iff.mpr h)]

theorem conj_eigScale_mul_eigScale (Z : ZeroConfig) (g : ℝ → ℂ) (ℓ : ℝ) (b : ℂ) :
    conj (eigScale Z g ℓ b) * eigScale Z g ℓ b = ((‖frobWeight Z g ℓ b‖ : ℝ) : ℂ)⁻¹ := by
  rw [eigScale, map_inv₀, Complex.conj_ofReal, ← mul_inv, ← Complex.ofReal_mul,
    Real.mul_self_sqrt (norm_nonneg _)]

/-- `λ̄ W + λ W̄ = 2|W|` for `W ≠ 0`. -/
theorem conj_eigPhase_mul_add (Z : ZeroConfig) (g : ℝ → ℂ) (ℓ : ℝ) (b : ℂ)
    (hW : frobWeight Z g ℓ b ≠ 0) :
    conj (eigPhase Z g ℓ b) * frobWeight Z g ℓ b + eigPhase Z g ℓ b * conj (frobWeight Z g ℓ b) =
      2 * ((‖frobWeight Z g ℓ b‖ : ℝ) : ℂ) := by
  have hn0 : ((‖frobWeight Z g ℓ b‖ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast norm_ne_zero_iff.mpr hW
  have hWW := Complex.conj_mul' (frobWeight Z g ℓ b)
  have hWW' := Complex.mul_conj' (frobWeight Z g ℓ b)
  rw [eigPhase, map_div₀, Complex.conj_ofReal, div_mul_eq_mul_div, div_mul_eq_mul_div, hWW, hWW',
    ← add_div]
  field_simp
  ring

/-- The coordinate function of the negative vector of `b`:
`X_τ(g) (𝟙[β = b] − λ_b 𝟙[β = 1/b̄]) / √|W_b|`. -/
def eigTargetFun (Z : ZeroConfig) (g : ℝ → ℂ) (ℓ : ℝ) (b : ℂ) (τ : Z.carrier) : ℂ :=
  eigScale Z g ℓ b * zeroCoord Z g τ *
    (eigInd ℓ b τ - eigPhase Z g ℓ b * eigInd ℓ (reflEig b) τ)

theorem memℓp_eigTargetFun (Z : ZeroConfig) (hZ : TemperedConfig Z) {g : ℝ → ℂ}
    (hg : ContDiff ℝ 2 g) (hgc : HasCompactSupport g) (ℓ : ℝ) (b : ℂ) :
    Memℓp (eigTargetFun Z g ℓ b) 2 := by
  refine ((memℓp_zeroCoord Z hZ hg hgc).norm.const_mul (2 * ‖eigScale Z g ℓ b‖)).mono fun τ => ?_
  have h4 : ‖eigInd ℓ b τ - eigPhase Z g ℓ b * eigInd ℓ (reflEig b) τ‖ ≤ 2 := by
    refine (norm_sub_le _ _).trans ?_
    rw [norm_mul]
    nlinarith [norm_eigInd_le ℓ b τ, norm_eigInd_le ℓ (reflEig b) τ, norm_eigPhase_le Z g ℓ b,
      norm_nonneg (eigPhase Z g ℓ b), norm_nonneg (eigInd ℓ (reflEig b) τ)]
  calc ‖eigTargetFun Z g ℓ b τ‖ = ‖eigScale Z g ℓ b‖ * ‖zeroCoord Z g τ‖ *
        ‖eigInd ℓ b τ - eigPhase Z g ℓ b * eigInd ℓ (reflEig b) τ‖ := by
          simp only [eigTargetFun, norm_mul]
    _ ≤ ‖eigScale Z g ℓ b‖ * ‖zeroCoord Z g τ‖ * 2 :=
        mul_le_mul_of_nonneg_left h4 (by positivity)
    _ = 2 * ‖eigScale Z g ℓ b‖ * ‖zeroCoord Z g τ‖ := by ring

/-- The negative vector of an eigenvalue `b`. -/
def eigTarget (Z : ZeroConfig) (hZ : TemperedConfig Z) {g : ℝ → ℂ} (hg : ContDiff ℝ 2 g)
    (hgc : HasCompactSupport g) (ℓ : ℝ) (b : ℂ) : ℓ²(Z.carrier, ℂ) :=
  ⟨eigTargetFun Z g ℓ b, memℓp_eigTargetFun Z hZ hg hgc ℓ b⟩

theorem eigTarget_apply (Z : ZeroConfig) (hZ : TemperedConfig Z) {g : ℝ → ℂ}
    (hg : ContDiff ℝ 2 g) (hgc : HasCompactSupport g) (ℓ : ℝ) (b : ℂ) (τ : Z.carrier) :
    eigTarget Z hZ hg hgc ℓ b τ = eigScale Z g ℓ b * zeroCoord Z g τ *
      (eigInd ℓ b τ - eigPhase Z g ℓ b * eigInd ℓ (reflEig b) τ) := rfl

theorem one_lt_norm_of_mem_outerEig {Z : ZeroConfig} {ℓ : ℝ} (hℓ : 0 < ℓ) {b : ℂ}
    (hb : b ∈ outerEig Z ℓ) : 1 < ‖b‖ := by
  obtain ⟨ρ, hρ, rfl⟩ := hb
  exact (one_lt_norm_frobEig_iff hℓ ρ).mpr hρ.2

theorem norm_reflEig_lt_one {b : ℂ} (hb : 1 < ‖b‖) : ‖reflEig b‖ < 1 := by
  rw [reflEig, norm_inv, Complex.norm_conj]
  exact inv_lt_one_of_one_lt₀ hb

/-- For outer `b, b'` no point lies in the class of `b` and the reflected class of `b'`. -/
theorem eigInd_mul_eigInd_refl (ℓ : ℝ) {b b' : ℂ} (hb : 1 < ‖b‖) (hb' : 1 < ‖b'‖) (τ : ℂ) :
    eigInd ℓ b τ * eigInd ℓ (reflEig b') τ = 0 := by
  unfold eigInd
  split_ifs with h1 h2
  · exfalso
    have := norm_reflEig_lt_one hb'
    rw [← h2, h1] at this
    linarith
  all_goals simp

theorem eigInd_mul_eigInd (ℓ : ℝ) (b b' τ : ℂ) :
    eigInd ℓ b τ * eigInd ℓ b' τ = if b = b' then eigInd ℓ b τ else 0 := by
  unfold eigInd
  by_cases hbb : b = b'
  · subst hbb; split_ifs <;> simp_all
  · rw [if_neg hbb]
    split_ifs with h1 h2
    · exact absurd (h1.symm.trans h2) hbb
    all_goals simp

theorem conj_eigInd (ℓ : ℝ) (b τ : ℂ) : conj (eigInd ℓ b τ) = eigInd ℓ b τ := by
  unfold eigInd; split_ifs <;> simp

theorem eigInd_reflectCarrier (Z : ZeroConfig) (ℓ : ℝ) (b : ℂ) (τ : Z.carrier) :
    eigInd ℓ b ((reflectCarrier Z τ : Z.carrier) : ℂ) = eigInd ℓ (reflEig b) τ :=
  eigInd_reflect ℓ b τ

/-- The reflected coordinates of the negative vector of `b`. -/
theorem eigTarget_reflect (Z : ZeroConfig) (hZ : TemperedConfig Z) {g : ℝ → ℂ}
    (hg : ContDiff ℝ 2 g) (hgc : HasCompactSupport g) (ℓ : ℝ) (b : ℂ) (τ : Z.carrier) :
    eigTarget Z hZ hg hgc ℓ b (reflectCarrier Z τ) =
      eigScale Z g ℓ b * zeroCoord Z g (reflectCarrier Z τ) *
        (eigInd ℓ (reflEig b) τ - eigPhase Z g ℓ b * eigInd ℓ b τ) := by
  rw [eigTarget_apply, eigInd_reflectCarrier, eigInd_reflectCarrier, reflEig_reflEig]

theorem eigInd_mul_eq_ite (ℓ : ℝ) (b τ w : ℂ) :
    eigInd ℓ b τ * w = if frobEig ℓ τ = b then w else 0 := by
  unfold eigInd; split_ifs <;> simp

theorem frobWeight_eq_tsum_eigInd (Z : ZeroConfig) (g : ℝ → ℂ) (ℓ : ℝ) (b : ℂ) :
    frobWeight Z g ℓ b = ∑' τ : Z.carrier,
      eigInd ℓ b τ * (zeroCoord Z g τ * conj (zeroCoord Z g (reflectCarrier Z τ))) := by
  simp only [frobWeight, eigInd_mul_eq_ite]

/-- The reflected-class sum is the conjugate weight: `Σ_{β = 1/b̄} conj X_{1−τ̄} X_τ = conj W_b`. -/
theorem tsum_eigInd_reflEig (Z : ZeroConfig) (g : ℝ → ℂ) (ℓ : ℝ) (b : ℂ) :
    ∑' τ : Z.carrier, eigInd ℓ (reflEig b) τ *
        (conj (zeroCoord Z g (reflectCarrier Z τ)) * zeroCoord Z g τ) =
      conj (frobWeight Z g ℓ b) := by
  rw [frobWeight_eq_tsum_eigInd, Complex.conj_tsum, ← (reflectEquiv Z).tsum_eq]
  refine tsum_congr fun τ => ?_
  simp only [reflectEquiv_apply, eigInd_reflectCarrier, reflEig_reflEig,
    reflectCarrier_reflectCarrier, map_mul, conj_eigInd, Complex.conj_conj]

theorem norm_eigInd_mul_le (ℓ : ℝ) (b τ w : ℂ) : ‖eigInd ℓ b τ * w‖ ≤ ‖w‖ := by
  rw [norm_mul]
  exact mul_le_of_le_one_left (norm_nonneg _) (norm_eigInd_le ℓ b τ)

/-- **The hyperbolic pair of a visible eigenvalue** has Krein square `−2`. -/
theorem inner_reflect_eigTarget_self (Z : ZeroConfig) (hZ : TemperedConfig Z) {g : ℝ → ℂ}
    (hg : ContDiff ℝ 2 g) (hgc : HasCompactSupport g) {ℓ : ℝ} (hℓ : 0 < ℓ)
    (hO : (outerEig Z ℓ).Finite) {b : ℂ} (hb : b ∈ visibleEig Z g ℓ hO) :
    inner ℂ (reflectVec Z (eigTarget Z hZ hg hgc ℓ b)) (eigTarget Z hZ hg hgc ℓ b) = -2 := by
  have hbO : b ∈ outerEig Z ℓ := hO.mem_toFinset.mp (Finset.mem_filter.mp hb).1
  have hW0 : frobWeight Z g ℓ b ≠ 0 := (Finset.mem_filter.mp hb).2
  have hn := one_lt_norm_of_mem_outerEig hℓ hbO
  have hsum := summable_zeroCoord_mul_reflect Z hZ hg hgc
  rw [lp.inner_eq_tsum]
  simp only [RCLike.inner_apply', reflectVec_apply]
  have hterm : ∀ τ : Z.carrier, conj (eigTarget Z hZ hg hgc ℓ b (reflectCarrier Z τ)) *
      eigTarget Z hZ hg hgc ℓ b τ =
      -(conj (eigScale Z g ℓ b) * eigScale Z g ℓ b) *
        (conj (eigPhase Z g ℓ b) * (eigInd ℓ b τ *
            (zeroCoord Z g τ * conj (zeroCoord Z g (reflectCarrier Z τ)))) +
          eigPhase Z g ℓ b * (eigInd ℓ (reflEig b) τ *
            (conj (zeroCoord Z g (reflectCarrier Z τ)) * zeroCoord Z g τ))) := fun τ => by
    have e1 := eigInd_mul_eigInd_refl ℓ hn hn (τ : ℂ)
    have e2 : eigInd ℓ (reflEig b) τ * eigInd ℓ b τ = 0 := by rw [mul_comm]; exact e1
    have e3 : eigInd ℓ b τ * eigInd ℓ b τ = eigInd ℓ b τ := by
      rw [eigInd_mul_eigInd, if_pos rfl]
    have e4 : eigInd ℓ (reflEig b) τ * eigInd ℓ (reflEig b) τ = eigInd ℓ (reflEig b) τ := by
      rw [eigInd_mul_eigInd, if_pos rfl]
    rw [eigTarget_reflect, eigTarget_apply]
    simp only [map_mul, map_sub, conj_eigInd]
    linear_combination
      (conj (eigScale Z g ℓ b) * conj (zeroCoord Z g (reflectCarrier Z τ)) *
          eigScale Z g ℓ b * zeroCoord Z g τ) *
        (e2 + conj (eigPhase Z g ℓ b) * eigPhase Z g ℓ b * e1 - eigPhase Z g ℓ b * e4 -
          conj (eigPhase Z g ℓ b) * e3)
  have hA0 : Summable fun τ : Z.carrier => eigInd ℓ b τ *
      (zeroCoord Z g τ * conj (zeroCoord Z g (reflectCarrier Z τ))) :=
    Summable.of_norm_bounded hsum fun τ => norm_eigInd_mul_le ℓ b τ _
  have hB0 : Summable fun τ : Z.carrier => eigInd ℓ (reflEig b) τ *
      (conj (zeroCoord Z g (reflectCarrier Z τ)) * zeroCoord Z g τ) :=
    Summable.of_norm_bounded hsum fun τ => by
      refine (norm_eigInd_mul_le ℓ _ τ _).trans ?_
      rw [norm_mul, norm_mul, Complex.norm_conj, mul_comm]
  have hA := hA0.mul_left (conj (eigPhase Z g ℓ b))
  have hB := hB0.mul_left (eigPhase Z g ℓ b)
  rw [tsum_congr hterm, tsum_mul_left, hA.tsum_add hB, tsum_mul_left,
    tsum_mul_left, ← frobWeight_eq_tsum_eigInd, tsum_eigInd_reflEig, conj_eigScale_mul_eigScale,
    conj_eigPhase_mul_add Z g ℓ b hW0]
  have hn0 : ((‖frobWeight Z g ℓ b‖ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast norm_ne_zero_iff.mpr hW0
  field_simp

/-- **Distinct outer eigenvalues give Krein-orthogonal pairs.** -/
theorem inner_reflect_eigTarget_ne (Z : ZeroConfig) (hZ : TemperedConfig Z) {g : ℝ → ℂ}
    (hg : ContDiff ℝ 2 g) (hgc : HasCompactSupport g) {ℓ : ℝ} (hℓ : 0 < ℓ)
    {b b' : ℂ} (hbO : b ∈ outerEig Z ℓ) (hbO' : b' ∈ outerEig Z ℓ) (hbb : b ≠ b') :
    inner ℂ (reflectVec Z (eigTarget Z hZ hg hgc ℓ b')) (eigTarget Z hZ hg hgc ℓ b) = 0 := by
  have hn := one_lt_norm_of_mem_outerEig hℓ hbO
  have hn' := one_lt_norm_of_mem_outerEig hℓ hbO'
  rw [lp.inner_eq_tsum]
  simp only [RCLike.inner_apply', reflectVec_apply]
  refine (tsum_congr fun τ => ?_).trans tsum_zero
  have e1 : eigInd ℓ (reflEig b') τ * eigInd ℓ b τ = 0 := by
    rw [mul_comm]; exact eigInd_mul_eigInd_refl ℓ hn hn' τ
  have e2 : eigInd ℓ (reflEig b') τ * eigInd ℓ (reflEig b) τ = 0 := by
    rw [eigInd_mul_eigInd, if_neg]
    intro h
    exact hbb (by rw [← reflEig_reflEig b, ← h, reflEig_reflEig])
  have e3 : eigInd ℓ b' τ * eigInd ℓ b τ = 0 := by rw [eigInd_mul_eigInd, if_neg (Ne.symm hbb)]
  have e4 : eigInd ℓ b' τ * eigInd ℓ (reflEig b) τ = 0 := eigInd_mul_eigInd_refl ℓ hn' hn τ
  rw [eigTarget_reflect, eigTarget_apply]
  simp only [map_mul, map_sub, conj_eigInd]
  linear_combination
    (conj (eigScale Z g ℓ b') * conj (zeroCoord Z g (reflectCarrier Z τ)) *
        eigScale Z g ℓ b * zeroCoord Z g τ) *
      (e1 - eigPhase Z g ℓ b * e2 - conj (eigPhase Z g ℓ b') * e3 +
        conj (eigPhase Z g ℓ b') * eigPhase Z g ℓ b * e4)

/-- The Krein Gram of the negative vectors of the visible eigenvalues is `−2·I`. -/
theorem inner_reflect_eigTarget (Z : ZeroConfig) (hZ : TemperedConfig Z) {g : ℝ → ℂ}
    (hg : ContDiff ℝ 2 g) (hgc : HasCompactSupport g) {ℓ : ℝ} (hℓ : 0 < ℓ)
    (hO : (outerEig Z ℓ).Finite) {b b' : ℂ} (hb : b ∈ visibleEig Z g ℓ hO)
    (hb' : b' ∈ visibleEig Z g ℓ hO) :
    inner ℂ (reflectVec Z (eigTarget Z hZ hg hgc ℓ b')) (eigTarget Z hZ hg hgc ℓ b) =
      if b = b' then -2 else 0 := by
  split_ifs with hbb
  · subst hbb; exact inner_reflect_eigTarget_self Z hZ hg hgc hℓ hO hb
  · exact inner_reflect_eigTarget_ne Z hZ hg hgc hℓ
      (hO.mem_toFinset.mp (Finset.mem_filter.mp hb).1)
      (hO.mem_toFinset.mp (Finset.mem_filter.mp hb').1) hbb

/-! ### The tower Pontryagin law -/

theorem summable_conj_zeroCoord_mul (Z : ZeroConfig) (hZ : TemperedConfig Z) {g : ℝ → ℂ}
    (hg : ContDiff ℝ 2 g) (hgc : HasCompactSupport g) (a : ℓ²(Z.carrier, ℂ)) :
    Summable fun τ : Z.carrier => ‖conj (zeroCoord Z g τ) * a τ‖ := by
  have h2 := (lp.memℓp a).summable (by norm_num : (0 : ℝ) < (2 : ENNReal).toReal)
  simp only [ENNReal.toReal_ofNat, Real.rpow_two] at h2
  refine Summable.of_nonneg_of_le (fun τ => norm_nonneg _) (fun τ => ?_)
    (((summable_sq_zeroCoord Z hZ hg hgc).add h2).div_const 2)
  rw [norm_mul, Complex.norm_conj]
  nlinarith [sq_nonneg (‖zeroCoord Z g τ‖ - ‖a τ‖)]

/-- **The negative vectors lie in the closed span of the tower.** -/
theorem eigTarget_mem_closure (Z : ZeroConfig) (hZ : TemperedConfig Z) {g : ℝ → ℂ}
    (hg : ContDiff ℝ 2 g) (hgc : HasCompactSupport g) {ℓ : ℝ} (hℓ : 0 < ℓ)
    (hO : (outerEig Z ℓ).Finite) (b : ℂ) :
    eigTarget Z hZ hg hgc ℓ b ∈
      (Submodule.span ℂ (Set.range (towerVec Z hZ hg hgc ℓ))).topologicalClosure := by
  rw [← Submodule.orthogonal_orthogonal_eq_closure, Submodule.mem_orthogonal]
  intro a ha
  have hk : ∀ k : ℤ, inner ℂ (towerVec Z hZ hg hgc ℓ k) a = 0 := fun k =>
    (Submodule.mem_orthogonal _ a).mp ha _ (Submodule.subset_span ⟨k, rfl⟩)
  have hc := classSum_eq_zero_of_orthogonal_tower Z hZ hg hgc hℓ hO a hk
  have hq := summable_conj_zeroCoord_mul Z hZ hg hgc a
  rw [← inner_conj_symm, lp.inner_eq_tsum]
  simp only [RCLike.inner_apply']
  have e : ∀ τ : Z.carrier, conj (eigTarget Z hZ hg hgc ℓ b τ) * a τ =
      conj (eigScale Z g ℓ b) * (if frobEig ℓ τ = b then conj (zeroCoord Z g τ) * a τ else 0) -
        conj (eigScale Z g ℓ b) * conj (eigPhase Z g ℓ b) *
          (if frobEig ℓ τ = reflEig b then conj (zeroCoord Z g τ) * a τ else 0) := fun τ => by
    rw [eigTarget_apply, ← eigInd_mul_eq_ite, ← eigInd_mul_eq_ite]
    simp only [map_mul, map_sub, conj_eigInd]
    ring
  have h10 : Summable fun τ : Z.carrier =>
      (if frobEig ℓ τ = b then conj (zeroCoord Z g τ) * a τ else 0) :=
    Summable.of_norm_bounded hq fun τ => by
      split_ifs <;> simp only [norm_zero, norm_nonneg, le_refl]
  have h20 : Summable fun τ : Z.carrier =>
      (if frobEig ℓ τ = reflEig b then conj (zeroCoord Z g τ) * a τ else 0) :=
    Summable.of_norm_bounded hq fun τ => by
      split_ifs <;> simp only [norm_zero, norm_nonneg, le_refl]
  have h1 := h10.mul_left (conj (eigScale Z g ℓ b))
  have h2 := h20.mul_left (conj (eigScale Z g ℓ b) * conj (eigPhase Z g ℓ b))
  rw [tsum_congr e, h1.tsum_sub h2, tsum_mul_left,
    tsum_mul_left, hc b, hc (reflEig b)]
  simp

/-- **The Krein form of a class-killing vector is nonnegative.** If `Y_τ = X_τ(g) E(β(τ))` and every
outer eigenvalue `b` has `E(b) = 0` or `W_b = 0`, then `Re⟨R Y, Y⟩ ≥ 0`: the right zeros contribute
`conj E(1/b̄) E(b) W_b = 0` class by class, the left zeros the conjugate, the on-line zeros `|Y_τ|²`. -/
theorem re_inner_reflect_nonneg_of_classes (Z : ZeroConfig) {g : ℝ → ℂ} {ℓ : ℝ} (hℓ : 0 < ℓ)
    (hO : (outerEig Z ℓ).Finite) (Y : ℓ²(Z.carrier, ℂ)) (E : ℂ → ℂ)
    (hY : ∀ τ, Y τ = zeroCoord Z g τ * E (frobEig ℓ τ))
    (hE : ∀ b ∈ outerEig Z ℓ, E b = 0 ∨ frobWeight Z g ℓ b = 0) :
    0 ≤ (inner ℂ (reflectVec Z Y) Y).re := by
  have hhs : Summable fun τ : Z.carrier => inner ℂ ((reflectVec Z Y) τ) (Y τ) :=
    lp.summable_inner (reflectVec Z Y) Y
  rw [lp.inner_eq_tsum]
  simp only [RCLike.inner_apply', reflectVec_apply] at hhs ⊢
  set h : Z.carrier → ℂ := fun τ => conj (Y (reflectCarrier Z τ)) * Y τ with hh
  set on : Z.carrier → ℂ := fun τ => if (τ : ℂ).re = 1 / 2 then h τ else 0 with hon_def
  set rt : Z.carrier → ℂ := fun τ => if 1 / 2 < (τ : ℂ).re then h τ else 0 with hrt_def
  set lf : Z.carrier → ℂ := fun τ => if (τ : ℂ).re < 1 / 2 then h τ else 0 with hlf_def
  have hon : Summable on := Summable.of_norm_bounded hhs.norm fun τ => by
    simp only [hon_def]; split_ifs <;> simp
  have hrt : Summable rt := Summable.of_norm_bounded hhs.norm fun τ => by
    simp only [hrt_def]; split_ifs <;> simp
  have hlf : Summable lf := Summable.of_norm_bounded hhs.norm fun τ => by
    simp only [hlf_def]; split_ifs <;> simp
  have hsplit : ∀ τ, h τ = on τ + rt τ + lf τ := fun τ => by
    simp only [hon_def, hrt_def, hlf_def]
    rcases lt_trichotomy (τ : ℂ).re (1 / 2) with hlt | heq | hgt
    · rw [if_neg hlt.ne, if_neg (not_lt.mpr hlt.le), if_pos hlt]; ring
    · rw [if_pos heq, if_neg (by rw [heq]; exact lt_irrefl _),
        if_neg (by rw [heq]; exact lt_irrefl _)]; ring
    · rw [if_neg hgt.ne', if_pos hgt, if_neg (not_lt.mpr hgt.le)]; ring
  -- the left part is the conjugate of the right part
  have hleft : ∑' τ, lf τ = conj (∑' τ, rt τ) := by
    rw [Complex.conj_tsum, ← (reflectEquiv Z).tsum_eq]
    refine tsum_congr fun τ => ?_
    simp only [hlf_def, hrt_def, hh, reflectEquiv_apply, re_reflectCarrier,
      reflectCarrier_reflectCarrier]
    by_cases hgt : 1 / 2 < (τ : ℂ).re
    · rw [if_pos (by linarith), if_pos hgt, map_mul, Complex.conj_conj, mul_comm]
    · rw [if_neg (by linarith), if_neg hgt, map_zero]
  -- the right part vanishes class by class
  have hright : ∑' τ, rt τ = 0 := by
    have hpart : ∀ τ, rt τ = ∑ b ∈ hO.toFinset, (if frobEig ℓ τ = b then h τ else 0) := by
      intro τ
      rw [Finset.sum_ite_eq]
      simp only [hrt_def]
      by_cases hgt : 1 / 2 < (τ : ℂ).re
      · rw [if_pos hgt, if_pos (hO.mem_toFinset.mpr ⟨τ, ⟨τ.2, hgt⟩, rfl⟩)]
      · rw [if_neg hgt, if_neg]
        intro hmem
        exact hgt ((one_lt_norm_frobEig_iff hℓ _).mp
          (one_lt_norm_of_mem_outerEig hℓ (hO.mem_toFinset.mp hmem)))
    have hsumb : ∀ b ∈ hO.toFinset, Summable fun τ : Z.carrier =>
        (if frobEig ℓ τ = b then h τ else 0) :=
      fun b _ => Summable.of_norm_bounded hhs.norm fun τ => by split_ifs <;> simp
    rw [tsum_congr hpart, Summable.tsum_finsetSum hsumb]
    refine Finset.sum_eq_zero fun b hb => ?_
    have hcl : ∀ τ : Z.carrier, (if frobEig ℓ τ = b then h τ else 0) =
        conj (E (reflEig b)) * E b * (eigInd ℓ b τ *
          (zeroCoord Z g τ * conj (zeroCoord Z g (reflectCarrier Z τ)))) := fun τ => by
      rw [eigInd_mul_eq_ite]
      split_ifs with hβ
      · simp only [hh, hY]
        rw [show ((reflectCarrier Z τ : Z.carrier) : ℂ) = reflect (τ : ℂ) from rfl,
          frobEig_reflect, hβ]
        simp only [reflEig, map_mul]
        ring
      · simp
    rw [tsum_congr hcl, tsum_mul_left, ← frobWeight_eq_tsum_eigInd]
    rcases hE b (hO.mem_toFinset.mp hb) with h0 | h0
    · rw [h0]; simp
    · rw [h0, mul_zero]
  have hfull : ∑' τ, h τ = ∑' τ, on τ + ∑' τ, rt τ + ∑' τ, lf τ := by
    rw [tsum_congr hsplit, (hon.add hrt).tsum_add hlf, hon.tsum_add hrt]
  rw [hfull, hleft, hright, map_zero, add_zero, add_zero, Complex.re_tsum hon]
  refine tsum_nonneg fun τ => ?_
  simp only [hon_def]
  split_ifs with heq
  · simp only [hh, reflectCarrier_eq_self heq, Complex.conj_mul', ← Complex.ofReal_pow,
      Complex.ofReal_re]
    positivity
  · simp

/-- **Refined bound.** With finitely many outer eigenvalues, a window of the tower has at most as
many negative squares as there are visible eigenvalues: invisible classes contribute nothing. -/
theorem negIndex_towerGram_le_visible (Z : ZeroConfig) (hZ : TemperedConfig Z) {g : ℝ → ℂ}
    (hg : ContDiff ℝ 2 g) (hgc : HasCompactSupport g) {ℓ : ℝ} (hℓ : 0 < ℓ)
    (hO : (outerEig Z ℓ).Finite) (K : Finset ℤ) :
    hermNegIndex (towerGram Z g ℓ K) ≤ (visibleEig Z g ℓ hO).card := by
  let Ψ : (K → ℂ) →ₗ[ℂ] (visibleEig Z g ℓ hO → ℂ) :=
    { toFun := fun x b => ∑ k : K, x k * conj (b : ℂ) ^ (k : ℤ)
      map_add' := fun x y => by
        funext b; simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib]
      map_smul' := fun c x => by
        funext b; simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum,
          mul_assoc] }
  have hker : ∀ x, Ψ x = 0 → 0 ≤ hermQuad (towerGram Z g ℓ K) x := by
    intro x hx
    have hrw : towerGram Z g ℓ K =
        zeroGram Z fun k : K => (translateTest hg hgc (((k : ℤ) : ℝ) * ℓ) : ℝ → ℂ) := rfl
    rw [hrw, hermQuad_zeroGram_eq Z hZ]
    refine re_inner_reflect_nonneg_of_classes Z hℓ hO _
      (fun w => ∑ k : K, conj (x k) * w ^ (k : ℤ))
      (fun τ => towerComb_apply Z hZ hg hgc ℓ K x τ) fun b hb => ?_
    by_cases hvis : b ∈ visibleEig Z g ℓ hO
    · left
      have h0 := congrFun hx ⟨b, hvis⟩
      simp only [Ψ, LinearMap.coe_mk, AddHom.coe_mk, Pi.zero_apply] at h0
      have e : ∑ k : K, conj (x k) * b ^ (k : ℤ) = conj (∑ k : K, x k * conj b ^ (k : ℤ)) := by
        simp only [map_sum, map_mul, map_zpow₀, Complex.conj_conj]
      show ∑ k : K, conj (x k) * b ^ (k : ℤ) = 0
      rw [e, h0, map_zero]
    · right
      by_contra hne
      exact hvis (Finset.mem_filter.mpr ⟨hO.mem_toFinset.mpr hb, hne⟩)
  obtain ⟨V, hrank, hV⟩ := exists_isPosDefOn_finrank_eq_posIndex (-(towerGram Z g ℓ K))
  have hinj : LinearMap.ker (Ψ.domRestrict V) = ⊥ := by
    rw [LinearMap.ker_eq_bot']
    intro x hx
    by_contra hx0
    have h1 := hV x x.2 (fun h => hx0 (Subtype.ext h))
    rw [hermQuad_neg] at h1
    linarith [hker x hx]
  have h := LinearMap.finrank_le_finrank_of_injective (LinearMap.ker_eq_bot.mp hinj)
  rw [Module.finrank_fintype_fun_eq_card, Fintype.card_coe] at h
  unfold hermNegIndex
  rw [← hrank]
  exact h

/-- **Attainment on the tower.** Some window of the tower has as many negative squares as there are
visible eigenvalues. -/
theorem exists_towerGram_negIndex_ge (Z : ZeroConfig) (hZ : TemperedConfig Z) {g : ℝ → ℂ}
    (hg : ContDiff ℝ 2 g) (hgc : HasCompactSupport g) {ℓ : ℝ} (hℓ : 0 < ℓ)
    (hO : (outerEig Z ℓ).Finite) :
    ∃ K : Finset ℤ, (visibleEig Z g ℓ hO).card ≤ hermNegIndex (towerGram Z g ℓ K) := by
  set O := visibleEig Z g ℓ hO
  set t : O → ℓ²(Z.carrier, ℂ) := fun b => eigTarget Z hZ hg hgc ℓ b with ht
  have hRt : ∀ i j : O, inner ℂ (reflectVec Z (t j)) (t i) = if i = j then -2 else 0 := by
    intro i j
    rw [inner_reflect_eigTarget Z hZ hg hgc hℓ hO i.2 j.2]
    simp only [Subtype.ext_iff]
  set M : ℝ := ∑ b : O, ‖t b‖ + 1 with hM
  have hM1 : 1 ≤ M := by
    have : 0 ≤ ∑ b : O, ‖t b‖ := Finset.sum_nonneg fun _ _ => norm_nonneg _
    linarith
  have htM : ∀ b, ‖t b‖ ≤ M := fun b => by
    have := Finset.single_le_sum (f := fun b => ‖t b‖) (fun _ _ => norm_nonneg _)
      (Finset.mem_univ b)
    linarith
  set k := Fintype.card O with hk
  set ε : ℝ := 1 / ((2 * M + 1) * ((k : ℝ) + 1)) with hε
  have hε0 : 0 < ε := by positivity
  have hε1 : ε ≤ 1 := by
    rw [hε, div_le_one (by positivity)]
    have : (0 : ℝ) ≤ k := Nat.cast_nonneg _
    nlinarith
  -- approximants from the closed span of the tower
  have happrox : ∀ b : O, ∃ c : ℤ →₀ ℂ,
      ‖(c.sum fun k a => a • towerVec Z hZ hg hgc ℓ k) - t b‖ < ε := by
    intro b
    have hmem := eigTarget_mem_closure Z hZ hg hgc hℓ hO b
    rw [← SetLike.mem_coe, Submodule.topologicalClosure_coe, Metric.mem_closure_iff] at hmem
    obtain ⟨y, hy, hdist⟩ := hmem ε hε0
    obtain ⟨c, rfl⟩ := Finsupp.mem_span_range_iff_exists_finsupp.mp hy
    exact ⟨c, by rwa [dist_comm, dist_eq_norm] at hdist⟩
  choose c hc using happrox
  set K : Finset ℤ := Finset.univ.biUnion fun b => (c b).support with hK
  refine ⟨K, ?_⟩
  set tt : K → testSpace := fun k => translateTest hg hgc (((k : ℤ) : ℝ) * ℓ) with htt
  set C : Matrix O K ℂ := fun b k => c b k with hC
  set f : O → testSpace := fun b => ∑ k, C b k • tt k with hf
  have hfX : ∀ b, zeroMap Z hZ (f b) = (c b).sum fun k a => a • towerVec Z hZ hg hgc ℓ k := by
    intro b
    simp only [hf, map_sum, map_smul, hC, htt, Finsupp.sum]
    rw [Finset.sum_coe_sort K (fun k => c b k • zeroMap Z hZ (translateTest hg hgc ((k : ℝ) * ℓ)))]
    refine (Finset.sum_subset (fun k hk => Finset.mem_biUnion.mpr ⟨b, Finset.mem_univ _, hk⟩)
      fun k _ hk => ?_).symm
    rw [Finsupp.notMem_support_iff.mp hk, zero_smul]
  have hentry : ∀ i j, ‖zeroGram Z (fun i => (f i : ℝ → ℂ)) i j - (if i = j then -2 else 0)‖ ≤
      (2 * M + 1) * ε := by
    intro i j
    have hGij : zeroGram Z (fun i => (f i : ℝ → ℂ)) i j =
        inner ℂ (reflectVec Z (zeroMap Z hZ (f j))) (zeroMap Z hZ (f i)) :=
      W_eq_inner Z hZ (f i) (f j)
    have hdi : zeroMap Z hZ (f i) = t i + (zeroMap Z hZ (f i) - t i) := by abel
    have hdj : zeroMap Z hZ (f j) = t j + (zeroMap Z hZ (f j) - t j) := by abel
    set ei := zeroMap Z hZ (f i) - t i
    set ej := zeroMap Z hZ (f j) - t j
    have hei : ‖ei‖ < ε := by simp only [ei, hfX]; exact hc i
    have hej : ‖ej‖ < ε := by simp only [ej, hfX]; exact hc j
    rw [hGij, hdi, hdj, reflectVec_add, inner_add_left, inner_add_right, inner_add_right, hRt i j]
    have h1 := (norm_inner_le_norm (𝕜 := ℂ) (reflectVec Z (t j)) ei).trans_eq
      (by rw [norm_reflectVec])
    have h2 := (norm_inner_le_norm (𝕜 := ℂ) (reflectVec Z ej) (t i)).trans_eq
      (by rw [norm_reflectVec])
    have h3 := (norm_inner_le_norm (𝕜 := ℂ) (reflectVec Z ej) ei).trans_eq
      (by rw [norm_reflectVec])
    calc ‖(if i = j then -2 else 0) + inner ℂ (reflectVec Z (t j)) ei +
          (inner ℂ (reflectVec Z ej) (t i) + inner ℂ (reflectVec Z ej) ei) -
            (if i = j then -2 else 0)‖
        = ‖inner ℂ (reflectVec Z (t j)) ei + inner ℂ (reflectVec Z ej) (t i) +
            inner ℂ (reflectVec Z ej) ei‖ := by congr 1; ring
      _ ≤ ‖t j‖ * ‖ei‖ + ‖ej‖ * ‖t i‖ + ‖ej‖ * ‖ei‖ :=
        norm_add₃_le.trans (add_le_add (add_le_add h1 h2) h3)
      _ ≤ M * ε + ε * M + ε * ε := by
        have := htM i; have := htM j
        gcongr
      _ ≤ (2 * M + 1) * ε := by nlinarith
  have hη : (2 * M + 1) * ε * (Fintype.card O : ℝ) ≤ 1 := by
    rw [← hk, hε]
    have : (0 : ℝ) ≤ k := Nat.cast_nonneg _
    rw [show (2 * M + 1) * (1 / ((2 * M + 1) * ((k : ℝ) + 1))) * k = k / (k + 1) by
      field_simp, div_le_one (by positivity)]
    linarith
  have hpd : IsPosDefOn (-(zeroGram Z fun i => (f i : ℝ → ℂ))) ⊤ := fun x _ hx0 => by
    rw [hermQuad_neg]
    obtain ⟨i, hi⟩ := Function.ne_iff.mp hx0
    have hpos : 0 < ∑ i, ‖x i‖ ^ 2 :=
      lt_of_lt_of_le (pow_pos (norm_pos_iff.mpr hi) 2) (Finset.single_le_sum
        (f := fun i => ‖x i‖ ^ 2) (fun i _ => by positivity) (Finset.mem_univ i))
    linarith [hermQuad_le_of_near _ hη hentry x]
  have h1 := finrank_le_posIndex hpd
  rw [finrank_top, Module.finrank_fintype_fun_eq_card] at h1
  have hcomb : zeroGram Z (fun i => (f i : ℝ → ℂ)) = C * towerGram Z g ℓ K * Cᴴ :=
    zeroGram_comb Z hZ tt C
  calc (visibleEig Z g ℓ hO).card = Fintype.card O := (Fintype.card_coe _).symm
    _ ≤ hermNegIndex (zeroGram Z fun i => (f i : ℝ → ℂ)) := h1
    _ = hermNegIndex (C * towerGram Z g ℓ K * Cᴴ) := by rw [hcomb]
    _ ≤ hermNegIndex (towerGram Z g ℓ K) := hermNegIndex_mul_mul_conjTranspose_le C _

/-- **The tower Pontryagin law.** If a tempered configuration has finitely many outer eigenvalues at
scale `ℓ = log p > 0`, the Weil form has `n` negative squares on some window of the Hecke tower
`g(· − k ℓ)` iff at least `n` outer eigenvalues `p^{ρ − ½}` have nonzero Frobenius weight. -/
theorem tower_pontryagin_law (Z : ZeroConfig) (hZ : TemperedConfig Z) {g : ℝ → ℂ}
    (hg : ContDiff ℝ 2 g) (hgc : HasCompactSupport g) {ℓ : ℝ} (hℓ : 0 < ℓ)
    (hO : (outerEig Z ℓ).Finite) (n : ℕ) :
    (∃ K : Finset ℤ, n ≤ hermNegIndex (towerGram Z g ℓ K)) ↔ n ≤ (visibleEig Z g ℓ hO).card := by
  constructor
  · rintro ⟨K, hK⟩
    exact hK.trans (negIndex_towerGram_le_visible Z hZ hg hgc hℓ hO K)
  · intro hn
    obtain ⟨K, hK⟩ := exists_towerGram_negIndex_ge Z hZ hg hgc hℓ hO
    exact ⟨K, hn.trans hK⟩

/-- The visible eigenvalues are at most the distinct outer eigenvalues. -/
theorem card_visibleEig_le (Z : ZeroConfig) (g : ℝ → ℂ) (ℓ : ℝ) (hO : (outerEig Z ℓ).Finite) :
    ((visibleEig Z g ℓ hO).card : ℕ∞) ≤ (outerEig Z ℓ).encard := by
  rw [hO.encard_eq_coe_toFinset_card]
  exact ENat.coe_le_coe.mpr (Finset.card_filter_le _ _)

end GaloisForLFunctions.ArithmeticCastelnuovoSeveri
