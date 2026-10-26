import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.TheStripLivesOnShortCycles

/-!
# One prime sees the defect of every configuration

The negative squares of a window of the tower `g(· − kℓ)` depend on `g` only through its zero-side
coordinates `X(g) ∈ ℓ²(Z)`, and continuously: `T_{kℓ}` acts by the multiplier `β_τ^k`,
`|β_τ| ≤ e^{ℓ/2}`. Strict negativity on finitely many combinations of finitely many tower vectors
therefore survives approximation (`towerGram_negIndex_ge_of_near`), and the zero map has dense range
(`exists_zeroMap_near`). It suffices to find one vector of `ℓ²(Z)` whose tower carries the chosen
eigenvalues; tests follow by density.

* **Interpolation** (`exists_interpolating_coeffs`, `interp_mul_repVec`). For distinct outer
  eigenvalues `b` with representatives `ρ_b`, the vector `Y = Σ_b (e_{ρ_b} + e_{1−ρ̄_b})`
  (`repVec`) has `P(T) Y = Σ_b P(b) e_{ρ_b} + P(b̄⁻¹) e_{1−ρ̄_b}`. Lagrange interpolation at the
  distinct nodes `b, b̄⁻¹` gives `P_b(T) Y = e_{ρ_b} − e_{1−ρ̄_b}` (`kreinNegVec`), the negative
  vectors of the Krein form.
* **One prime sees every configuration** (`exists_test_card_le_towerDefect_of_tempered`,
  `tower_law`, `rightZeros_eq_empty_iff_towers`). For every tempered configuration and every
  scale `ℓ > 0`, some window of the tower of some test has `n` negative squares iff there are at
  least `n` distinct outer eigenvalues `e^{ℓ(ρ − ½)}`. No sparsity, well-foundedness or separation
  enters: Wolff blindness is a property of a fixed test, never of a configuration.
* **One shift decides Hodge index** (`rightZeros_eq_empty_iff_twoWindow`). The coordinates of
  `g − T_v g` are `(1 − e^{(τ−½)v}) X_τ(g)` (`zeroCoord_sub_translate`), a multiplier vanishing
  at no zero off the line; for every `v > 0` a tempered configuration has no zero right of the line
  iff Weil's form is nonnegative on every `g − T_v g`. For `ζ`
  (`zeta_riemannHypothesis_iff_oneShift`): RH holds iff `Re W(T_v g, g) ≤ W(g, g)` for every test,
  at one fixed shift `v > 0`, e.g. `v = log 2`.
-/

open Complex Filter Topology Set
open scoped ComplexConjugate Classical lp Matrix
open Zeta23 GaloisForLFunctions.HTGeometry
open GaloisForLFunctions.SquareRootThreshold (TemperedConfig temperedConfig_zetaZeroConfig)

noncomputable section

namespace GaloisForLFunctions.ArithmeticCastelnuovoSeveri

/-! ### 1. Attainment from approximate targets -/

/-- A pointwise bound `‖f τ‖ ≤ c ‖y τ‖` bounds the `ℓ²` norms. -/
theorem lp_norm_le_of_pointwise {T : Type*} {f y : ℓ²(T, ℂ)} {c : ℝ} (hc : 0 ≤ c)
    (h : ∀ τ, ‖f τ‖ ≤ c * ‖y τ‖) : ‖f‖ ≤ c * ‖y‖ := by
  have h2 : (0 : ℝ) < (2 : ENNReal).toReal := by norm_num
  refine lp.norm_le_of_tsum_le h2 (by positivity) ?_
  rw [Real.mul_rpow hc (norm_nonneg _), lp.norm_rpow_eq_tsum h2 y, ← tsum_mul_left]
  refine Summable.tsum_le_tsum (fun τ => ?_) ((lp.memℓp f).summable h2)
    (((lp.memℓp y).summable h2).mul_left _)
  rw [← Real.mul_rpow hc (norm_nonneg _)]
  exact Real.rpow_le_rpow (norm_nonneg _) (h τ) h2.le

/-- **Attainment from approximate targets.** If `n` vectors `t_i` with Krein Gram `−2 I` and norms
`≤ M` are each within `1/((2M + 1)(n + 1))` of a combination of the tower vectors `T_{kℓ} g`,
`k ∈ K`, the window `K` of the tower has at least `n` negative squares. -/
theorem towerGram_negIndex_ge_of_near (Z : ZeroConfig) (hZ : TemperedConfig Z) {g : ℝ → ℂ}
    (hg : ContDiff ℝ 2 g) (hgc : HasCompactSupport g) (ℓ : ℝ) {ι : Type*} [Fintype ι]
    [DecidableEq ι] (t : ι → ℓ²(Z.carrier, ℂ))
    (hRt : ∀ i j, inner ℂ (reflectVec Z (t j)) (t i) = if i = j then -2 else 0) {M : ℝ}
    (hM : 1 ≤ M) (htM : ∀ i, ‖t i‖ ≤ M) (K : Finset ℤ) (x : ι → ℤ → ℂ)
    (hx : ∀ i, ‖∑ k ∈ K, x i k • towerVec Z hZ hg hgc ℓ k - t i‖ <
      1 / ((2 * M + 1) * ((Fintype.card ι : ℝ) + 1))) :
    Fintype.card ι ≤ hermNegIndex (towerGram Z g ℓ K) := by
  set ε : ℝ := 1 / ((2 * M + 1) * ((Fintype.card ι : ℝ) + 1)) with hε
  have hk : (0 : ℝ) ≤ Fintype.card ι := Nat.cast_nonneg _
  have hM' : 0 < 2 * M + 1 := by linarith
  have hε0 : 0 < ε := by positivity
  have hε1 : ε ≤ 1 := by
    rw [hε, div_le_one (by positivity)]
    nlinarith
  set tt : K → testSpace := fun k => translateTest hg hgc (((k : ℤ) : ℝ) * ℓ) with htt
  set C : Matrix ι K ℂ := fun i k => x i k with hC
  set f : ι → testSpace := fun i => ∑ k, C i k • tt k with hf
  have hfX : ∀ i, zeroMap Z hZ (f i) = ∑ k ∈ K, x i k • towerVec Z hZ hg hgc ℓ k := by
    intro i
    simp only [hf, map_sum, map_smul, hC, htt]
    exact Finset.sum_coe_sort K
      (fun k => x i k • zeroMap Z hZ (translateTest hg hgc ((k : ℝ) * ℓ)))
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
    have hei : ‖ei‖ < ε := by simp only [ei, hfX]; exact hx i
    have hej : ‖ej‖ < ε := by simp only [ej, hfX]; exact hx j
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
      _ ≤ (2 * M + 1) * ε := by nlinarith [mul_le_mul_of_nonneg_left hε1 hε0.le]
  have hη : (2 * M + 1) * ε * (Fintype.card ι : ℝ) ≤ 1 := by
    rw [hε, show (2 * M + 1) * (1 / ((2 * M + 1) * ((Fintype.card ι : ℝ) + 1))) *
        (Fintype.card ι : ℝ) = Fintype.card ι / (Fintype.card ι + 1) by field_simp,
      div_le_one (by positivity)]
    linarith
  have hpd : IsPosDefOn (-(zeroGram Z fun i => (f i : ℝ → ℂ))) ⊤ := fun y _ hy0 => by
    rw [hermQuad_neg]
    obtain ⟨i, hi⟩ := Function.ne_iff.mp hy0
    have hpos : 0 < ∑ i, ‖y i‖ ^ 2 :=
      lt_of_lt_of_le (pow_pos (norm_pos_iff.mpr hi) 2) (Finset.single_le_sum
        (f := fun i => ‖y i‖ ^ 2) (fun i _ => by positivity) (Finset.mem_univ i))
    linarith [hermQuad_le_of_near _ hη hentry y]
  have h1 := finrank_le_posIndex hpd
  rw [finrank_top, Module.finrank_fintype_fun_eq_card] at h1
  have hcomb : zeroGram Z (fun i => (f i : ℝ → ℂ)) = C * towerGram Z g ℓ K * Cᴴ :=
    zeroGram_comb Z hZ tt C
  calc Fintype.card ι ≤ hermNegIndex (zeroGram Z fun i => (f i : ℝ → ℂ)) := h1
    _ = hermNegIndex (C * towerGram Z g ℓ K * Cᴴ) := by rw [hcomb]
    _ ≤ hermNegIndex (towerGram Z g ℓ K) := hermNegIndex_mul_mul_conjTranspose_le C _

/-! ### 2. Negative vectors of the Krein form -/

/-- `e_ρ − e_{1−ρ̄}`: for a right zero `ρ` a vector of Krein norm `−2`. -/
def kreinNegVec (Z : ZeroConfig) (ρ : Z.carrier) : ℓ²(Z.carrier, ℂ) :=
  lp.single 2 ρ (1 : ℂ) - lp.single 2 (reflectCarrier Z ρ) 1

theorem kreinNegVec_apply (Z : ZeroConfig) (ρ τ : Z.carrier) :
    kreinNegVec Z ρ τ = (if τ = ρ then 1 else 0) - if τ = reflectCarrier Z ρ then 1 else 0 := by
  simp only [kreinNegVec, lp.coeFn_sub, Pi.sub_apply, lp.single_apply, Pi.single_apply]

theorem norm_kreinNegVec_le (Z : ZeroConfig) (ρ : Z.carrier) : ‖kreinNegVec Z ρ‖ ≤ 2 := by
  refine (norm_sub_le _ _).trans ?_
  rw [lp.norm_single (by norm_num), lp.norm_single (by norm_num), norm_one]
  norm_num

theorem reflectCarrier_ne_of_re {Z : ZeroConfig} {ρ σ : Z.carrier} (hρ : 1 / 2 < (ρ : ℂ).re)
    (hσ : 1 / 2 < (σ : ℂ).re) : reflectCarrier Z ρ ≠ σ := fun h => by
  have := congrArg (fun t : Z.carrier => (t : ℂ).re) h
  simp only [re_reflectCarrier] at this
  linarith

/-- The Krein Gram of the vectors `e_ρ − e_{1−ρ̄}` of right zeros is `−2 I`. -/
theorem inner_reflect_kreinNegVec (Z : ZeroConfig) {ρ σ : Z.carrier} (hρ : 1 / 2 < (ρ : ℂ).re)
    (hσ : 1 / 2 < (σ : ℂ).re) :
    inner ℂ (reflectVec Z (kreinNegVec Z σ)) (kreinNegVec Z ρ) = if ρ = σ then -2 else 0 := by
  have hRR : reflectCarrier Z σ = reflectCarrier Z ρ ↔ σ = ρ :=
    ⟨fun h => (reflectEquiv Z).injective (by simpa only [reflectEquiv_apply] using h),
      fun h => h ▸ rfl⟩
  simp only [kreinNegVec, reflectVec_sub, reflectVec_single, reflectCarrier_reflectCarrier,
    inner_sub_left, inner_sub_right, inner_single_single, if_neg (reflectCarrier_ne_of_re hσ hρ),
    if_neg (reflectCarrier_ne_of_re hρ hσ).symm, hRR]
  by_cases h : ρ = σ
  · subst h; simp; ring
  · simp [h, Ne.symm h]

/-! ### 3. A vector whose tower carries chosen eigenvalues -/

/-- **Interpolating coefficients.** For finitely many points `b` of modulus `> 1` there are
polynomials `P_b = Σ_{n<N} x_b(n) zⁿ` with `P_b(b') = δ_{bb'}` and `P_b(b̄'⁻¹) = −δ_{bb'}`. -/
theorem exists_interpolating_coeffs (O : Finset ℂ) (hO : ∀ b ∈ O, 1 < ‖b‖) :
    ∃ N : ℕ, ∃ x : O → ℕ → ℂ, ∀ b b' : O,
      ∑ n ∈ Finset.range N, x b n * (b' : ℂ) ^ n = (if b = b' then 1 else 0) ∧
      ∑ n ∈ Finset.range N, x b n * (conj (b' : ℂ))⁻¹ ^ n = (if b = b' then -1 else 0) := by
  set s : Finset ℂ := O ∪ O.image fun b => (conj b)⁻¹ with hs
  have hinj : Set.InjOn (id : ℂ → ℂ) ↑s := Set.injOn_id _
  set r : O → ℂ → ℂ := fun b z =>
    if z = b then 1 else if z = (conj (b : ℂ))⁻¹ then -1 else 0 with hr
  set P : O → Polynomial ℂ := fun b => Lagrange.interpolate s id (r b) with hP
  set N : ℕ := Finset.univ.sup fun b => (P b).natDegree + 1 with hN
  have hNb : ∀ b, (P b).natDegree < N := fun b =>
    Nat.lt_of_lt_of_le (Nat.lt_succ_self _)
      (Finset.le_sup (f := fun b => (P b).natDegree + 1) (Finset.mem_univ b))
  have hev : ∀ b, ∀ z ∈ s, ∑ n ∈ Finset.range N, (P b).coeff n * z ^ n = r b z := by
    intro b z hz
    rw [← Polynomial.eval_eq_sum_range' (hNb b)]
    exact Lagrange.eval_interpolate_at_node (v := id) (r b) hinj hz
  -- the outer nodes `b` and the inner nodes `b̄⁻¹` are distinct
  have hne : ∀ b b' : O, (conj (b' : ℂ))⁻¹ ≠ b := by
    intro b b' h
    have h1 : ‖(conj (b' : ℂ))⁻¹‖ < 1 := by
      rw [norm_inv, Complex.norm_conj]
      exact inv_lt_one_of_one_lt₀ (hO _ b'.2)
    rw [h] at h1
    linarith [hO _ b.2]
  refine ⟨N, fun b => (P b).coeff, fun b b' => ⟨?_, ?_⟩⟩
  · rw [hev b b' (Finset.mem_union_left _ b'.2)]
    simp only [hr]
    by_cases hbb : b = b'
    · subst hbb; simp
    · have h1 : (b' : ℂ) ≠ b := fun h => hbb (Subtype.ext h.symm)
      have h2 : (b' : ℂ) ≠ (conj (b : ℂ))⁻¹ := fun h => hne b' b h.symm
      simp [h1, h2, hbb]
  · rw [hev b ((conj (b' : ℂ))⁻¹) (Finset.mem_union_right _ (Finset.mem_image_of_mem _ b'.2))]
    simp only [hr]
    by_cases hbb : b = b'
    · subst hbb; simp [hne b b]
    · have h1 : (conj (b' : ℂ))⁻¹ ≠ (conj (b : ℂ))⁻¹ := fun h =>
        hbb (Subtype.ext ((RingHom.injective (starRingEnd ℂ)) (inv_inj.mp h)).symm)
      simp [hne b b', h1, hbb]

/-- The vector `Σ_b (e_{ρ_b} + e_{1−ρ̄_b})` of chosen representatives. -/
def repVec (Z : ZeroConfig) {O : Finset ℂ} (r : O → Z.carrier) : ℓ²(Z.carrier, ℂ) :=
  ∑ b : O, (lp.single 2 (r b) (1 : ℂ) + lp.single 2 (reflectCarrier Z (r b)) 1)

theorem repVec_apply (Z : ZeroConfig) {O : Finset ℂ} (r : O → Z.carrier) (τ : Z.carrier) :
    repVec Z r τ = ∑ b : O,
      ((if τ = r b then 1 else 0) + if τ = reflectCarrier Z (r b) then 1 else 0) := by
  simp only [repVec, lp.coeFn_sum, Finset.sum_apply, lp.coeFn_add, Pi.add_apply, lp.single_apply,
    Pi.single_apply]

/-- **The interpolating polynomial of the tower sends `Y` to a negative vector**:
`P_b(β_τ) Y_τ = (e_{ρ_b} − e_{1−ρ̄_b})_τ`. -/
theorem interp_mul_repVec (Z : ZeroConfig) {ℓ : ℝ} {O : Finset ℂ} (r : O → Z.carrier)
    (hr : ∀ b, 1 / 2 < (r b : ℂ).re) (hrb : ∀ b, frobEig ℓ (r b) = b) {N : ℕ}
    {x : O → ℕ → ℂ}
    (hx : ∀ b b' : O, ∑ n ∈ Finset.range N, x b n * (b' : ℂ) ^ n = (if b = b' then 1 else 0) ∧
      ∑ n ∈ Finset.range N, x b n * (conj (b' : ℂ))⁻¹ ^ n = (if b = b' then -1 else 0))
    (b : O) (τ : Z.carrier) :
    (∑ n ∈ Finset.range N, x b n * frobEig ℓ τ ^ n) * repVec Z r τ = kreinNegVec Z (r b) τ := by
  have hne : ∀ b' : O, reflectCarrier Z (r b') ≠ r b' := fun b' =>
    reflectCarrier_ne_of_re (hr b') (hr b')
  have hβ : ∀ b' : O,
      frobEig ℓ ((reflectCarrier Z (r b') : Z.carrier) : ℂ) = (conj (b' : ℂ))⁻¹ := fun b' => by
    rw [show ((reflectCarrier Z (r b') : Z.carrier) : ℂ) = reflect (r b') from rfl,
      frobEig_reflect, hrb]
  have hterm : ∀ b' : O, (∑ n ∈ Finset.range N, x b n * frobEig ℓ τ ^ n) *
      ((if τ = r b' then 1 else 0) + if τ = reflectCarrier Z (r b') then 1 else 0) =
        if b = b' then
          (if τ = r b' then 1 else 0) - (if τ = reflectCarrier Z (r b') then 1 else 0)
        else 0 := by
    intro b'
    by_cases h1 : τ = r b'
    · subst h1
      rw [if_pos rfl, if_neg (hne b').symm, add_zero, mul_one, hrb, (hx b b').1]
      split_ifs <;> simp
    · by_cases h2 : τ = reflectCarrier Z (r b')
      · subst h2
        rw [if_neg h1, if_pos rfl, zero_add, mul_one, hβ, (hx b b').2]
        split_ifs <;> simp
      · simp [h1, h2]
  rw [repVec_apply, Finset.mul_sum, Finset.sum_congr rfl fun b' _ => hterm b', Finset.sum_ite_eq,
    if_pos (Finset.mem_univ b), kreinNegVec_apply]

/-! ### 4. One prime sees the whole defect of every configuration -/

/-- **Every finite set of outer eigenvalues is seen by one window of one tower**, for every
tempered configuration and every scale `ℓ > 0`. -/
theorem exists_test_card_le_towerDefect_of_tempered (Z : ZeroConfig) (hZ : TemperedConfig Z)
    {ℓ : ℝ} (hℓ : 0 < ℓ) (O : Finset ℂ) (hO : ∀ b ∈ O, b ∈ outerEig Z ℓ) :
    ∃ g : ℝ → ℂ, ContDiff ℝ 2 g ∧ HasCompactSupport g ∧
      ∃ K : Finset ℤ, O.card ≤ hermNegIndex (towerGram Z g ℓ K) := by
  have hrep : ∀ b : O, ∃ ρ : Z.carrier, 1 / 2 < (ρ : ℂ).re ∧ frobEig ℓ ρ = b := fun b => by
    obtain ⟨ρ, hρ, he⟩ := hO b b.2
    exact ⟨⟨ρ, hρ.1⟩, hρ.2, he⟩
  choose r hr hrb using hrep
  have hmod : ∀ b ∈ O, 1 < ‖b‖ := fun b hb => by
    obtain ⟨ρ, hρ, rfl⟩ := hO b hb
    exact (one_lt_norm_frobEig_iff hℓ ρ).mpr hρ.2
  obtain ⟨N, x, hx⟩ := exists_interpolating_coeffs O hmod
  have hinj : ∀ b b' : O, r b = r b' ↔ b = b' := fun b b' =>
    ⟨fun h => Subtype.ext (by rw [← hrb b, ← hrb b', h]), fun h => h ▸ rfl⟩
  have hRt : ∀ b b' : O, inner ℂ (reflectVec Z (kreinNegVec Z (r b'))) (kreinNegVec Z (r b)) =
      if b = b' then -2 else 0 := fun b b' => by
    rw [inner_reflect_kreinNegVec Z (hr b) (hr b')]
    simp only [hinj]
  -- a uniform bound for the interpolating polynomials on the strip
  set A : ℝ := ∑ b : O, ∑ n ∈ Finset.range N, ‖x b n‖ * Real.exp (ℓ / 2) ^ n + 1 with hA
  have hA0 : 0 < A := by
    have : 0 ≤ ∑ b : O, ∑ n ∈ Finset.range N, ‖x b n‖ * Real.exp (ℓ / 2) ^ n :=
      Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => by positivity
    linarith
  have hAb : ∀ (b : O) (τ : Z.carrier),
      ‖∑ n ∈ Finset.range N, x b n * frobEig ℓ τ ^ n‖ ≤ A := by
    intro b τ
    have hβ : ‖frobEig ℓ τ‖ ≤ Real.exp (ℓ / 2) := by
      simpa only [Complex.norm_conj] using norm_conj_frobEig_le Z hℓ τ
    calc ‖∑ n ∈ Finset.range N, x b n * frobEig ℓ τ ^ n‖
        ≤ ∑ n ∈ Finset.range N, ‖x b n‖ * Real.exp (ℓ / 2) ^ n := by
          refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun n _ => ?_)
          rw [norm_mul, norm_pow]
          exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hβ n)
            (norm_nonneg _)
      _ ≤ ∑ b : O, ∑ n ∈ Finset.range N, ‖x b n‖ * Real.exp (ℓ / 2) ^ n :=
          Finset.single_le_sum
            (f := fun b : O => ∑ n ∈ Finset.range N, ‖x b n‖ * Real.exp (ℓ / 2) ^ n)
            (fun _ _ => Finset.sum_nonneg fun _ _ => by positivity) (Finset.mem_univ b)
      _ ≤ A := by linarith
  -- approximate the vector of representatives by the coordinates of a test
  set ε : ℝ := 1 / ((2 * 2 + 1) * ((Fintype.card O : ℝ) + 1)) with hε
  have hε0 : 0 < ε := by positivity
  obtain ⟨f, hf⟩ := exists_zeroMap_near Z hZ (repVec Z r) (div_pos hε0 hA0)
  set K : Finset ℤ := (Finset.range N).image fun n : ℕ => (n : ℤ) with hK
  refine ⟨f, f.2.1, f.2.2, K, ?_⟩
  suffices hs : ∀ b : O, ‖∑ k ∈ K, x b k.toNat • towerVec Z hZ f.2.1 f.2.2 ℓ k -
      kreinNegVec Z (r b)‖ < ε by
    have h := towerGram_negIndex_ge_of_near Z hZ f.2.1 f.2.2 ℓ (fun b => kreinNegVec Z (r b))
      hRt (by norm_num : (1 : ℝ) ≤ 2) (fun b => norm_kreinNegVec_le Z (r b)) K
      (fun b k => x b k.toNat) hs
    rwa [Fintype.card_coe] at h
  intro b
  -- the combination `P_b(T_ℓ) f` is `A`-close to the target
  have hcoord : ∀ τ : Z.carrier,
      (∑ k ∈ K, x b k.toNat • towerVec Z hZ f.2.1 f.2.2 ℓ k) τ =
        (∑ n ∈ Finset.range N, x b n * frobEig ℓ τ ^ n) * zeroCoord Z f τ := by
    intro τ
    rw [lp.coeFn_sum, Finset.sum_apply, hK,
      Finset.sum_image fun a _ c _ h => by exact_mod_cast h, Finset.sum_mul]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [lp.coeFn_smul, Pi.smul_apply, smul_eq_mul, towerVec_apply, Int.toNat_natCast,
      zpow_natCast]
    ring
  have hpt : ∀ τ : Z.carrier,
      ‖(∑ k ∈ K, x b k.toNat • towerVec Z hZ f.2.1 f.2.2 ℓ k - kreinNegVec Z (r b)) τ‖ ≤
        A * ‖(zeroMap Z hZ f - repVec Z r) τ‖ := by
    intro τ
    rw [lp.coeFn_sub, Pi.sub_apply, hcoord, ← interp_mul_repVec Z r hr hrb hx b τ, ← mul_sub,
      norm_mul, lp.coeFn_sub, Pi.sub_apply, zeroMap_apply]
    exact mul_le_mul_of_nonneg_right (hAb b τ) (norm_nonneg _)
  calc _ ≤ A * ‖zeroMap Z hZ f - repVec Z r‖ := lp_norm_le_of_pointwise hA0.le hpt
    _ < A * (ε / A) := mul_lt_mul_of_pos_left hf hA0
    _ = ε := by rw [mul_div_cancel₀ _ hA0.ne']

/-- **The one-prime tower law for every tempered configuration.** At every scale `ℓ > 0`, some
window of the tower of some test has `n` negative squares iff there are at least `n` distinct
outer eigenvalues. -/
theorem tower_law (Z : ZeroConfig) (hZ : TemperedConfig Z) {ℓ : ℝ} (hℓ : 0 < ℓ) (n : ℕ) :
    (∃ g : ℝ → ℂ, ContDiff ℝ 2 g ∧ HasCompactSupport g ∧
      ∃ K : Finset ℤ, n ≤ hermNegIndex (towerGram Z g ℓ K)) ↔
      (n : ℕ∞) ≤ (outerEig Z ℓ).encard := by
  constructor
  · rintro ⟨g, hg, hgc, K, hK⟩
    exact (ENat.coe_le_coe.mpr hK).trans (negIndex_towerGram_le Z hZ hg hgc ℓ K)
  · intro hn
    obtain ⟨t, hts, htc⟩ := Set.exists_subset_encard_eq hn
    have htfin : t.Finite := Set.finite_of_encard_eq_coe htc
    obtain ⟨g, hg, hgc, K, hK⟩ := exists_test_card_le_towerDefect_of_tempered Z hZ hℓ
      htfin.toFinset fun b hb => hts (htfin.mem_toFinset.mp hb)
    have hcard : htfin.toFinset.card = n := by
      have := htfin.encard_eq_coe_toFinset_card
      rw [htc] at this
      exact_mod_cast this.symm
    exact ⟨g, hg, hgc, K, hcard ▸ hK⟩

/-- **Hodge index is positivity on the towers of one scale**, for every tempered configuration. -/
theorem rightZeros_eq_empty_iff_towers (Z : ZeroConfig) (hZ : TemperedConfig Z) {ℓ : ℝ}
    (hℓ : 0 < ℓ) : rightZeros Z = ∅ ↔ ∀ g : ℝ → ℂ, ContDiff ℝ 2 g → HasCompactSupport g →
      ∀ K : Finset ℤ, hermNegIndex (towerGram Z g ℓ K) = 0 := by
  constructor
  · intro h0 g hg hgc K
    by_contra hne
    have h1 := (tower_law Z hZ hℓ 1).mp ⟨g, hg, hgc, K, Nat.one_le_iff_ne_zero.mpr hne⟩
    have he : outerEig Z ℓ = ∅ := by simp [outerEig, h0]
    rw [he, Set.encard_empty] at h1
    exact absurd h1 (by norm_num)
  · intro hpsd
    by_contra hne
    obtain ⟨ρ, hρ⟩ := Set.nonempty_iff_ne_empty.mpr hne
    obtain ⟨g, hg, hgc, K, hK⟩ := (tower_law Z hZ hℓ 1).mpr
      (Set.one_le_encard_iff_nonempty.mpr ⟨_, ρ, hρ, rfl⟩)
    have h := hpsd g hg hgc K
    omega

/-! ### 5. One shift decides Hodge index -/

/-- The coordinates of `g − T_v g` are `(1 − e^{(τ−½)v}) X_τ(g)`. -/
theorem zeroCoord_sub_translate (Z : ZeroConfig) {g : ℝ → ℂ} (hg : Continuous g)
    (hgc : HasCompactSupport g) (v : ℝ) (τ : Z.carrier) :
    zeroCoord Z (g - translate v g) τ = (1 - frobEig v τ) * zeroCoord Z g τ := by
  have e : g - translate v g = twoTermTest g (-1) v := by
    funext u
    simp [twoTermTest, sub_eq_add_neg]
  rw [e, zeroCoord_twoTermTest Z hg hgc, I_mul_gammaOf, frobEig, mul_comm ((τ : ℂ) - 1 / 2)]
  ring

/-- `W(T_v g, g)` is the first Lefschetz moment at scale `v`. -/
theorem W_translate_eq_towerMoment (Z : ZeroConfig) (hZ : TemperedConfig Z) {g : ℝ → ℂ}
    (hg : ContDiff ℝ 2 g) (hgc : HasCompactSupport g) (v : ℝ) :
    Z.W (translate v g) g = towerMoment Z g v 1 := by
  refine (W_eq_inner Z hZ (translateTest hg hgc v) ⟨g, hg, hgc⟩).trans ?_
  rw [lp.inner_eq_tsum, towerMoment]
  refine tsum_congr fun τ => ?_
  simp only [RCLike.inner_apply', reflectVec_apply, zeroMap_apply, zpow_one]
  rw [show zeroCoord Z (translateTest hg hgc v : ℝ → ℂ) τ = zeroCoord Z (translate v g) τ from rfl,
    zeroCoord_translate, I_mul_gammaOf, frobEig, mul_comm ((τ : ℂ) - 1 / 2)]
  ring

/-- **One shift decides Hodge index.** For `v > 0` a tempered configuration has no zero right of
the line iff Weil's form is nonnegative on every `g − T_v g`. The multiplier `1 − e^{(τ−½)v}` of
`1 − T_v` vanishes at no zero off the line, so the coordinates of the `g − T_v g` approximate the
negative vector `e_ρ − e_{1−ρ̄}` of any right zero `ρ`. -/
theorem rightZeros_eq_empty_iff_twoWindow (Z : ZeroConfig) (hZ : TemperedConfig Z) {v : ℝ}
    (hv : 0 < v) : rightZeros Z = ∅ ↔ ∀ g : ℝ → ℂ, ContDiff ℝ 2 g → HasCompactSupport g →
      0 ≤ (Z.W (g - translate v g) (g - translate v g)).re := by
  constructor
  · intro h0 g hg hgc
    have hG : ContDiff ℝ 2 (g - translate v g) := hg.sub (translate_contDiff hg v)
    have hGc : HasCompactSupport (g - translate v g) :=
      hgc.sub (translate_hasCompactSupport hgc v)
    rw [show Z.W (g - translate v g) (g - translate v g) = _ from
      W_eq_inner Z hZ ⟨_, hG, hGc⟩ ⟨_, hG, hGc⟩]
    refine re_inner_reflect_self_nonneg Z _ fun τ hτ => ?_
    have hm : (τ : ℂ) ∈ rightZeros Z := ⟨τ.2, hτ⟩
    rw [h0] at hm
    exact absurd hm (Set.notMem_empty _)
  · intro h
    by_contra hne
    obtain ⟨ρ, hρ⟩ := Set.nonempty_iff_ne_empty.mpr hne
    set r : Z.carrier := ⟨ρ, hρ.1⟩ with hrdef
    have hr2 : 1 / 2 < (r : ℂ).re := hρ.2
    have hrr : reflectCarrier Z r ≠ r := reflectCarrier_ne_of_re hr2 hr2
    -- the multiplier `1 − e^{(τ−½)v}` of `1 − T_v`
    have hμ : ∀ τ : Z.carrier, (τ : ℂ).re ≠ 1 / 2 → 1 - frobEig v τ ≠ 0 := by
      intro τ hτ h0
      have h1 : ‖frobEig v τ‖ = 1 := by rw [← sub_eq_zero.mp h0, norm_one]
      rw [norm_frobEig, Real.exp_eq_one_iff] at h1
      rcases mul_eq_zero.mp h1 with h | h
      · linarith
      · exact hτ (by linarith)
    have hμle : ∀ τ : Z.carrier, ‖1 - frobEig v τ‖ ≤ 1 + Real.exp (v / 2) := fun τ => by
      refine (norm_sub_le _ _).trans ?_
      rw [norm_one]
      have := norm_conj_frobEig_le Z hv τ
      rw [Complex.norm_conj] at this
      linarith
    have hμ₁ : 1 - frobEig v r ≠ 0 := hμ r (ne_of_gt hr2)
    have hμ₂ : 1 - frobEig v (reflectCarrier Z r : Z.carrier) ≠ 0 :=
      hμ _ (by rw [re_reflectCarrier]; linarith)
    -- its preimage of the negative vector
    set Y : ℓ²(Z.carrier, ℂ) := (1 - frobEig v r)⁻¹ • lp.single 2 r (1 : ℂ) -
      (1 - frobEig v (reflectCarrier Z r : Z.carrier))⁻¹ • lp.single 2 (reflectCarrier Z r) 1
      with hYdef
    set B : ℝ := 1 + Real.exp (v / 2) with hBdef
    have hB : 0 < B := by positivity
    obtain ⟨f, hf⟩ := exists_zeroMap_near Z hZ Y (show 0 < 1 / (4 * B) by positivity)
    have hG : ContDiff ℝ 2 ((f : ℝ → ℂ) - translate v f) :=
      f.2.1.sub (translate_contDiff f.2.1 v)
    have hGc : HasCompactSupport ((f : ℝ → ℂ) - translate v f) :=
      f.2.2.sub (translate_hasCompactSupport f.2.2 v)
    obtain ⟨e, he_def⟩ : ∃ e : ℓ²(Z.carrier, ℂ),
        e = zeroMap Z hZ ⟨(f : ℝ → ℂ) - translate v f, hG, hGc⟩ - kreinNegVec Z r := ⟨_, rfl⟩
    have hpt : ∀ τ, ‖e τ‖ ≤ B * ‖(zeroMap Z hZ f - Y) τ‖ := by
      intro τ
      have htY : kreinNegVec Z r τ = (1 - frobEig v τ) * Y τ := by
        rw [kreinNegVec_apply, hYdef]
        simp only [lp.coeFn_sub, lp.coeFn_smul, Pi.sub_apply, Pi.smul_apply, smul_eq_mul,
          lp.single_apply, Pi.single_apply]
        by_cases h1 : τ = r
        · have h2 : τ ≠ reflectCarrier Z r := by rw [h1]; exact hrr.symm
          rw [if_pos h1, if_neg h2, h1, mul_one, mul_zero, sub_zero, sub_zero,
            mul_inv_cancel₀ hμ₁]
        · by_cases h2 : τ = reflectCarrier Z r
          · rw [if_neg h1, if_pos h2, h2, mul_zero, zero_sub, mul_one, zero_sub, mul_neg,
              mul_inv_cancel₀ hμ₂]
          · rw [if_neg h1, if_neg h2]
            ring
      have hcoe : ((zeroMap Z hZ f - Y : ℓ²(Z.carrier, ℂ)) : Z.carrier → ℂ) τ =
          zeroCoord Z f τ - Y τ := rfl
      rw [he_def, lp.coeFn_sub, Pi.sub_apply, zeroMap_apply,
        zeroCoord_sub_translate Z f.2.1.continuous f.2.2 v τ, htY, ← mul_sub, norm_mul, hcoe]
      exact mul_le_mul_of_nonneg_right (hμle τ) (norm_nonneg _)
    have he : ‖e‖ < 1 / 4 := by
      calc ‖e‖ ≤ B * ‖zeroMap Z hZ f - Y‖ := lp_norm_le_of_pointwise hB.le hpt
        _ < B * (1 / (4 * B)) := mul_lt_mul_of_pos_left hf hB
        _ = 1 / 4 := by field_simp
    -- the Weil norm of `f − T_v f` is negative
    have hRt : inner ℂ (reflectVec Z (kreinNegVec Z r)) (kreinNegVec Z r) = -2 := by
      rw [inner_reflect_kreinNegVec Z hr2 hr2, if_pos rfl]
    have ht2 : ‖kreinNegVec Z r‖ ≤ 2 := norm_kreinNegVec_le Z r
    have hW := h _ f.2.1 f.2.2
    rw [show Z.W ((f : ℝ → ℂ) - translate v f) ((f : ℝ → ℂ) - translate v f) = _ from
      W_eq_inner Z hZ ⟨_, hG, hGc⟩ ⟨_, hG, hGc⟩] at hW
    have hdec : zeroMap Z hZ ⟨(f : ℝ → ℂ) - translate v f, hG, hGc⟩ = kreinNegVec Z r + e := by
      rw [he_def]; abel
    rw [hdec, reflectVec_add, inner_add_left, inner_add_right, inner_add_right, hRt] at hW
    have h1 := (Complex.re_le_norm _).trans (norm_inner_le_norm (𝕜 := ℂ)
      (reflectVec Z (kreinNegVec Z r)) e)
    have h2 := (Complex.re_le_norm _).trans (norm_inner_le_norm (𝕜 := ℂ) (reflectVec Z e)
      (kreinNegVec Z r))
    have h3 := (Complex.re_le_norm _).trans (norm_inner_le_norm (𝕜 := ℂ) (reflectVec Z e) e)
    rw [norm_reflectVec] at h1 h2 h3
    simp only [Complex.add_re] at hW
    have k1 : ‖kreinNegVec Z r‖ * ‖e‖ ≤ 2 * (1 / 4) :=
      mul_le_mul ht2 he.le (norm_nonneg _) (by norm_num)
    have k3 : ‖e‖ * ‖e‖ ≤ 1 / 4 * (1 / 4) := mul_le_mul he.le he.le (norm_nonneg _) (by norm_num)
    have h2re : ((-2 : ℂ)).re = -2 := by norm_num
    rw [h2re] at hW
    nlinarith [norm_nonneg e, norm_nonneg (kreinNegVec Z r)]

/-- **One shift decides RH.** For any fixed `v > 0`, e.g. `v = log 2`: RH holds iff every test
satisfies `Re W(T_v g, g) ≤ W(g, g)`. -/
theorem zeta_riemannHypothesis_iff_oneShift {v : ℝ} (hv : 0 < v) :
    RiemannHypothesis ↔ ∀ g : ℝ → ℂ, ContDiff ℝ 2 g → HasCompactSupport g →
      (zetaZeroConfig.W (translate v g) g).re ≤ (zetaZeroConfig.W g g).re := by
  rw [← rightZeros_zeta_eq_empty_iff,
    rightZeros_eq_empty_iff_twoWindow _ temperedConfig_zetaZeroConfig hv]
  refine forall_congr' fun g => imp_congr_right fun hg => imp_congr_right fun hgc => ?_
  have h := re_W_twoWindow _ temperedConfig_zetaZeroConfig hg hgc hv 1
  simp only [Nat.cast_one, one_mul] at h
  rw [h, W_translate_eq_towerMoment _ temperedConfig_zetaZeroConfig hg hgc,
    W_self_eq_towerMoment_zero _ temperedConfig_zetaZeroConfig hg hgc v]
  constructor <;> intro h' <;> linarith

end GaloisForLFunctions.ArithmeticCastelnuovoSeveri

end
