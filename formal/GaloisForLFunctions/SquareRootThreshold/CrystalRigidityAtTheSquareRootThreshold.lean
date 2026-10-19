import GaloisForLFunctions.SquareRootThreshold.CrystallineFragilityOfOffLineLattices

/-!
# Crystal rigidity at the square-root threshold

Fix a periodic off-line pattern by its shape: `P` reflected pairs per period, with depths
`d_r ∈ (0, ½]` and relative ordinates `θ_r` (distinct mod `1`). At scale `ℓ` the ordinates are
`(2π/ℓ)(θ_r + j)`, the density is `Pℓ/2π`, and the Nyquist aperture is `Pℓ/2`. By the abstract
Toeplitz law the pattern hides at an aperture `a > (P−1)ℓ/2` only if the modes
`D(m) = Σ_r 2cosh(d_r mℓ) e^{2πiθ_r m}`, `1 ≤ m < P`, satisfy `|D(m)| ≤ D(0) = 2P`.

* **Spectral crystallinity** (`norm_powerSum_le_of_hiding`). At uniform depth `δ`, hiding above
  `(P−1)ℓ/2` forces `|Σ_r e^{2πiθ_r m}| ≤ P / cosh(δmℓ)`: the `m`-th Fourier coefficient of the
  ordinate pattern is exponentially small in `mℓ`.
* **Crystal rigidity** (`uniform_crystal_of_hiding`). If the pattern hides above `(P−1)ℓ/2` at
  unboundedly many scales `ℓ`, all depths are equal and `P(θ_r − θ_{r'}) ∈ ℤ`: the ordinates form
  one coset of the `1/P`-lattice. The deepest pairs dominate every mode as `ℓ → ∞`, so their power
  sums `p_1, …, p_{P−1}` vanish; by Newton's identities fewer than `P` of them cannot do this, and
  `P` of them must be the `P`-th roots of one number.
* **Visibility below the threshold** (`exists_visible_of_not_uniform_crystal`). Every other
  pattern is visible at every aperture `a > (P−1)ℓ/2` for all large `ℓ`, i.e. strictly below the
  square-root threshold `Pℓ/2`.
* **The crystal hides** (`uniform_crystal_hides`): uniform depth and crystalline ordinates hide
  up to `Pℓ/2` at every scale.

So at growing density (`ℓ ≍ log T`) the square-root threshold is reached by exactly one periodic
off-line shape, the uniform crystal.
-/

open MeasureTheory Complex Set Filter Topology
open scoped Real ComplexConjugate

noncomputable section

namespace GaloisForLFunctions.SquareRootThreshold

open Zeta23 _root_.RHTower

/-! ### Newton's identities for vanishing power sums -/

theorem aeval_psum {σ : Type*} [Fintype σ] (z : σ → ℂ) (k : ℕ) :
    MvPolynomial.aeval z (MvPolynomial.psum σ ℂ k) = ∑ i, z i ^ k := by
  simp [MvPolynomial.psum]

/-- **Newton.** If the power sums `p_1, …, p_K` vanish, so do `e_1, …, e_K`. -/
theorem aeval_esymm_eq_zero_of_powerSums {σ : Type*} [Fintype σ] (z : σ → ℂ) {K : ℕ}
    (h : ∀ m, 1 ≤ m → m ≤ K → ∑ i, z i ^ m = 0) {k : ℕ} (hk1 : 1 ≤ k) (hkK : k ≤ K) :
    MvPolynomial.aeval z (MvPolynomial.esymm σ ℂ k) = 0 := by
  have hN := congrArg (MvPolynomial.aeval z) (MvPolynomial.mul_esymm_eq_sum σ ℂ k)
  rw [map_mul, map_natCast, map_mul, map_sum] at hN
  rw [Finset.sum_eq_zero fun a ha => ?_, mul_zero] at hN
  · have hk0 : (k : ℂ) ≠ 0 := by exact_mod_cast (by omega : k ≠ 0)
    exact (mul_eq_zero.mp hN).resolve_left hk0
  · rw [Finset.mem_filter] at ha
    have h2 := Finset.HasAntidiagonal.mem_antidiagonal.mp ha.1
    simp only [map_mul]
    rw [aeval_psum, h a.2 (by omega) (by omega), mul_zero]

theorem aeval_esymm_card {σ : Type*} [Fintype σ] (z : σ → ℂ) :
    MvPolynomial.aeval z (MvPolynomial.esymm σ ℂ (Fintype.card σ)) = ∏ i, z i := by
  rw [MvPolynomial.aeval_esymm_eq_multiset_esymm, Finset.esymm_map_val, ← Finset.card_univ,
    Finset.powersetCard_self, Finset.sum_singleton]

/-- `N` nonzero points never have vanishing power sums `p_1, …, p_N`. -/
theorem not_forall_powerSum_eq_zero {σ : Type*} [Fintype σ] [Nonempty σ] (z : σ → ℂ)
    (hz : ∀ i, z i ≠ 0) : ¬ ∀ m, 1 ≤ m → m ≤ Fintype.card σ → ∑ i, z i ^ m = 0 := by
  intro h
  have := aeval_esymm_eq_zero_of_powerSums z h Fintype.card_pos le_rfl
  rw [aeval_esymm_card] at this
  exact Finset.prod_ne_zero_iff.mpr (fun i _ => hz i) this

/-- **Crystal lemma.** If the power sums `p_1, …, p_{N−1}` of `N` points vanish, the points have one
common `N`-th power. -/
theorem pow_card_eq_of_powerSums {σ : Type*} [Fintype σ] (z : σ → ℂ)
    (h : ∀ m, 1 ≤ m → m < Fintype.card σ → ∑ i, z i ^ m = 0) (i j : σ) :
    z i ^ Fintype.card σ = z j ^ Fintype.card σ := by
  set N := Fintype.card σ with hNdef
  have hN : 0 < N := Fintype.card_pos_iff.mpr ⟨i⟩
  set s : Multiset ℂ := Finset.univ.val.map fun x => -z x with hs
  have hcard : Multiset.card s = N := by simp [hs, hNdef]
  have he : ∀ k, 1 ≤ k → k < N → s.esymm k = 0 := by
    intro k hk1 hkN
    rw [hs, ← MvPolynomial.aeval_esymm_eq_multiset_esymm σ ℂ]
    refine aeval_esymm_eq_zero_of_powerSums _ (K := N - 1) (fun m hm1 hmK => ?_) hk1 (by omega)
    show ∑ i, (-z i) ^ m = 0
    rw [show (∑ i, (-z i) ^ m) = (-1) ^ m * ∑ i, z i ^ m by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ => neg_pow (z i) m,
      h m hm1 (by omega), mul_zero]
  have hev : ∀ x : σ, z x ^ N + s.esymm N = 0 := by
    intro x
    have h0 := congrArg (Polynomial.eval (z x)) (Multiset.prod_X_add_C_eq_sum_esymm s)
    rw [Polynomial.eval_multiset_prod, Polynomial.eval_finsetSum, Multiset.prod_eq_zero] at h0
    · rw [hcard, Finset.sum_eq_add_of_mem 0 N (Finset.mem_range.mpr (by omega))
        (Finset.mem_range.mpr (by omega)) hN.ne] at h0
      · simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X,
          Nat.sub_zero, Nat.sub_self, pow_zero, mul_one] at h0
        rw [show s.esymm 0 = 1 by simp [Multiset.esymm], one_mul] at h0
        exact h0.symm
      · intro k hk hk'
        rw [Finset.mem_range] at hk
        rw [Polynomial.eval_mul, Polynomial.eval_C, he k (by omega) (by omega), zero_mul]
    · rw [Multiset.map_map, Multiset.mem_map]
      refine ⟨-z x, Multiset.mem_map.mpr ⟨x, Finset.mem_univ_val _, rfl⟩, ?_⟩
      simp
  have := (hev i).trans (hev j).symm
  linear_combination this

/-- Converse: `N` distinct points with one common `N`-th power have `p_m = 0` for `0 < m < N`. The
points are all the `N`-th roots of that number, and rotation by `e^{2πi/N}` permutes them. -/
theorem powerSum_eq_zero_of_pow_eq {N : ℕ} (z : Fin N → ℂ) (hinj : Function.Injective z)
    {w : ℂ} (hw : ∀ i, z i ^ N = w) {m : ℕ} (hm1 : 1 ≤ m) (hmN : m < N) :
    ∑ i, z i ^ m = 0 := by
  have hN : 0 < N := by omega
  set T : Finset ℂ := (Polynomial.nthRoots N w).toFinset with hT
  have hmemT : ∀ x, x ∈ T ↔ x ^ N = w := fun x => by
    rw [hT, Multiset.mem_toFinset, Polynomial.mem_nthRoots hN]
  have hRT : Finset.univ.image z = T := by
    refine Finset.eq_of_subset_of_card_le (fun x hx => ?_) ?_
    · obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hx
      exact (hmemT _).mpr (hw i)
    · rw [Finset.card_image_of_injective _ hinj, Finset.card_univ, Fintype.card_fin]
      exact (Multiset.toFinset_card_le _).trans (Polynomial.card_nthRoots N w)
  have hζ := Complex.isPrimitiveRoot_exp N hN.ne'
  set ζ : ℂ := cexp (2 * π * I / N) with hζdef
  have hζ0 : ζ ≠ 0 := Complex.exp_ne_zero _
  have hrot : ∑ x ∈ T, (ζ * x) ^ m = ∑ x ∈ T, x ^ m := by
    refine Finset.sum_nbij' (fun x => ζ * x) (fun x => ζ⁻¹ * x) (fun x hx => ?_) (fun x hx => ?_)
      (fun x _ => ?_) (fun x _ => ?_) (fun x _ => rfl)
    · rw [hmemT] at hx ⊢; rw [mul_pow, hζ.pow_eq_one, one_mul, hx]
    · rw [hmemT] at hx ⊢; rw [mul_pow, inv_pow, hζ.pow_eq_one, inv_one, one_mul, hx]
    · rw [← mul_assoc, inv_mul_cancel₀ hζ0, one_mul]
    · rw [← mul_assoc, mul_inv_cancel₀ hζ0, one_mul]
  have hsum : ∑ i, z i ^ m = ∑ x ∈ T, x ^ m := by
    rw [← hRT, Finset.sum_image fun i _ j _ h => hinj h]
  rw [hsum]
  have h0 : (ζ ^ m - 1) * ∑ x ∈ T, x ^ m = 0 := by
    rw [sub_mul, one_mul, Finset.mul_sum, sub_eq_zero, ← hrot]
    exact Finset.sum_congr rfl fun x _ => (mul_pow ζ x m).symm
  exact (mul_eq_zero.mp h0).resolve_left (sub_ne_zero.mpr (hζ.pow_ne_one_of_pos_of_lt
    (by omega) hmN))

/-! ### Modes of a pattern of fixed shape -/

/-- Offsets of the relative pattern `θ` at scale `ℓ`: the ordinates are `(2π/ℓ)(θ_r + j)`. -/
def scaledOffset (ℓ : ℝ) {P : ℕ} (θ : Fin P → ℝ) : Fin P → ℝ := fun r => 2 * π * θ r / ℓ

theorem scaledOffset_injective {ℓ : ℝ} (hℓ : 0 < ℓ) {P : ℕ} {θ : Fin P → ℝ}
    (hθ : ∀ r r' : Fin P, ∀ j j' : ℤ, θ r + j = θ r' + j' → r = r' ∧ j = j') :
    ∀ r r' : Fin P, ∀ j j' : ℤ, scaledOffset ℓ θ r + j * (2 * π / ℓ) =
      scaledOffset ℓ θ r' + j' * (2 * π / ℓ) → r = r' ∧ j = j' := by
  intro r r' j j' h
  apply hθ r r' j j'
  have hc : (2 * π / ℓ) ≠ 0 := by positivity
  refine mul_left_cancel₀ hc ?_
  simp only [scaledOffset] at h
  linear_combination h

/-- The phase points `z_r = e^{2πiθ_r}` of the relative pattern. -/
def phasePoint {P : ℕ} (θ : Fin P → ℝ) (r : Fin P) : ℂ := cexp (2 * π * I * θ r)

theorem phasePoint_ne_zero {P : ℕ} (θ : Fin P → ℝ) (r : Fin P) : phasePoint θ r ≠ 0 :=
  Complex.exp_ne_zero _

theorem patternSymbol_scaledOffset {ℓ : ℝ} (hℓ : 0 < ℓ) {P : ℕ} (θ d : Fin P → ℝ) (m : ℕ) :
    patternSymbol ℓ (scaledOffset ℓ θ) d m =
      ∑ r, ((2 * Real.cosh (d r * (m * ℓ)) : ℝ) : ℂ) * phasePoint θ r ^ m := by
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [phasePoint, ← Complex.exp_nat_mul, Int.cast_natCast]
  congr 2
  simp only [scaledOffset]
  have : (ℓ : ℂ) ≠ 0 := by exact_mod_cast hℓ.ne'
  push_cast
  field_simp

theorem patternSymbol_zero (ℓ : ℝ) {P : ℕ} (c d : Fin P → ℝ) : patternSymbol ℓ c d 0 = 2 * P := by
  simp only [patternSymbol, Int.cast_zero, zero_mul, mul_zero, Real.cosh_zero, Complex.exp_zero]
  simp [mul_comm]

theorem patternSymbol_neg (ℓ : ℝ) {P : ℕ} (c d : Fin P → ℝ) (m : ℤ) :
    patternSymbol ℓ c d (-m) = conj (patternSymbol ℓ c d m) := by
  rw [patternSymbol, patternSymbol, map_sum]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [map_mul, Complex.conj_ofReal, ← Complex.exp_conj]
  congr 2
  · rw [Int.cast_neg, neg_mul, mul_neg, Real.cosh_neg]
  · simp only [map_mul, Complex.conj_I, Complex.conj_ofReal, map_intCast]
    push_cast
    ring

/-- **Toeplitz minor.** A positive semidefinite Toeplitz form of size `n` with Hermitian symbol
has `|D(m)| ≤ Re D(0)` for `1 ≤ m < n`. -/
theorem norm_le_of_toeplitzForm_nonneg {D : ℤ → ℂ} (hD : ∀ m, D (-m) = conj (D m)) {n : ℕ}
    (hT : ∀ c : Fin n → ℂ, 0 ≤ (toeplitzForm D n c).re) {m : ℕ} (hm1 : 1 ≤ m) (hmn : m < n) :
    ‖D m‖ ≤ (D 0).re := by
  have hm0 : (m : ℤ) ≠ 0 := by exact_mod_cast (by omega : m ≠ 0)
  have key : ∀ w : ℂ, 0 ≤ (1 + ‖w‖ ^ 2) * (D 0).re + 2 * (w * D m).re := by
    intro w
    set c : ℤ → ℂ := fun j => if j = 0 then 1 else if j = m then w else 0 with hc
    have heq : toeplitzForm D n (fun i => c (0 + i)) =
        (1 + ‖w‖ ^ 2) * D 0 + conj w * D (-m) + w * D m := by
      rw [← toeplitzSum_Ico_eq, ← toeplitzSum_subset (S := {0, (m : ℤ)})]
      · exact toeplitzSum_pair hm0 w
      · intro j hj
        simp only [Finset.mem_insert, Finset.mem_singleton] at hj
        rw [Finset.mem_Ico]
        rcases hj with rfl | rfl <;> omega
      · intro j _ hj
        simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hj
        rw [hc]
        simp only
        rw [if_neg hj.1, if_neg hj.2]
    have h1 := hT fun i => c (0 + i)
    rw [heq, hD, ← map_mul, Complex.add_re, Complex.add_re, Complex.conj_re,
      show (1 + (‖w‖ : ℂ) ^ 2) = ((1 + ‖w‖ ^ 2 : ℝ) : ℂ) by push_cast; ring,
      Complex.re_ofReal_mul] at h1
    linarith
  by_cases hDm : D m = 0
  · have := key 0
    rw [hDm, norm_zero]
    simpa using this
  set w : ℂ := -(conj (D m) / ‖D m‖) with hw
  have hwn : ‖w‖ = 1 := by
    rw [hw, norm_neg, norm_div, Complex.norm_conj, Complex.norm_real, norm_norm,
      div_self (norm_ne_zero_iff.mpr hDm)]
  have hwD : (w * D m).re = -‖D m‖ := by
    rw [hw, neg_mul, div_mul_eq_mul_div, ← Complex.normSq_eq_conj_mul_self,
      Complex.normSq_eq_norm_sq]
    rw [show ((‖D m‖ ^ 2 : ℝ) : ℂ) / (‖D m‖ : ℂ) = ((‖D m‖ : ℝ) : ℂ) by
      have : (‖D m‖ : ℂ) ≠ 0 := by exact_mod_cast norm_ne_zero_iff.mpr hDm
      push_cast; field_simp]
    simp
  have := key w
  rw [hwn, hwD] at this
  linarith

/-- **Mode bound.** A pattern hiding at an aperture `a > (P−1)ℓ/2` has `|D(m)| ≤ 2P` for every
mode `1 ≤ m < P`. -/
theorem norm_patternSymbol_le_of_hiding {ℓ : ℝ} (hℓ : 0 < ℓ) {P : ℕ} (c d : Fin P → ℝ)
    (hd0 : ∀ r, 0 < d r) (hd1 : ∀ r, d r ≤ 1 / 2)
    (hc : ∀ r r' : Fin P, ∀ j j' : ℤ, c r + j * (2 * π / ℓ) = c r' + j' * (2 * π / ℓ) →
      r = r' ∧ j = j')
    {a : ℝ} (ha : ((P : ℝ) - 1) * ℓ / 2 < a)
    (h : ∀ f : ℝ → ℂ, ContDiff ℝ 2 f → tsupport f ⊆ Icc (-a) a →
      0 ≤ ((patternConfig hℓ c d hd0 hd1).W f f).re)
    {m : ℕ} (hm1 : 1 ≤ m) (hmP : m < P) : ‖patternSymbol ℓ c d m‖ ≤ 2 * P := by
  have hP1 : (1 : ℝ) ≤ (P : ℝ) - 1 := by
    have : (2 : ℝ) ≤ P := by exact_mod_cast (by omega : 2 ≤ P)
    linarith
  have ha0 : 0 < a := lt_of_lt_of_le' ha (by positivity)
  rw [weil_nonneg_iff_toeplitz_of_lagFormula _ hℓ _
    (fun f hf hfc => W_patternConfig hℓ c d hd0 hd1 hc hf hfc) ha0] at h
  have hn : m < ⌈2 * a / ℓ⌉₊ := by
    refine lt_of_lt_of_le hmP (Nat.le_of_pred_lt ?_)
    rw [Nat.lt_ceil, lt_div_iff₀ hℓ]
    have : ((P - 1 : ℕ) : ℝ) = (P : ℝ) - 1 := by
      rw [Nat.cast_sub (by omega : 1 ≤ P), Nat.cast_one]
    rw [Nat.pred_eq_sub_one, this]
    linarith
  have := norm_le_of_toeplitzForm_nonneg (patternSymbol_neg ℓ c d) h hm1 hn
  rwa [patternSymbol_zero, show (2 * (P : ℂ)).re = 2 * P by simp] at this

/-- **Spectral crystallinity.** At uniform depth `δ`, hiding at an aperture `a > (P−1)ℓ/2` forces
`|Σ_r e^{2πiθ_r m}| ≤ P / cosh(δmℓ)` for `1 ≤ m < P`. -/
theorem norm_powerSum_le_of_hiding {ℓ : ℝ} (hℓ : 0 < ℓ) {P : ℕ} (θ : Fin P → ℝ) {δ : ℝ}
    (hδ0 : 0 < δ) (hδ1 : δ ≤ 1 / 2)
    (hθ : ∀ r r' : Fin P, ∀ j j' : ℤ, θ r + j = θ r' + j' → r = r' ∧ j = j')
    {a : ℝ} (ha : ((P : ℝ) - 1) * ℓ / 2 < a)
    (h : ∀ f : ℝ → ℂ, ContDiff ℝ 2 f → tsupport f ⊆ Icc (-a) a →
      0 ≤ ((patternConfig hℓ (scaledOffset ℓ θ) (fun _ => δ) (fun _ => hδ0)
        (fun _ => hδ1)).W f f).re)
    {m : ℕ} (hm1 : 1 ≤ m) (hmP : m < P) :
    ‖∑ r, phasePoint θ r ^ m‖ ≤ P / Real.cosh (δ * (m * ℓ)) := by
  have hb := norm_patternSymbol_le_of_hiding hℓ _ _ _ _ (scaledOffset_injective hℓ hθ) ha h hm1 hmP
  rw [patternSymbol_scaledOffset hℓ, ← Finset.mul_sum, norm_mul, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos (by positivity)] at hb
  rw [le_div_iff₀ (Real.cosh_pos _)]
  linarith

/-! ### Rigidity -/

/-- `cosh(ux)/cosh(vx) → 0` for `0 ≤ u < v`. -/
theorem tendsto_cosh_div_cosh {u v : ℝ} (hu : 0 ≤ u) (huv : u < v) :
    Tendsto (fun x => Real.cosh (u * x) / Real.cosh (v * x)) atTop (𝓝 0) := by
  have hlim : Tendsto (fun x => 2 * Real.exp ((u - v) * x)) atTop (𝓝 0) := by
    simpa using (Real.tendsto_exp_atBot.comp
      (tendsto_id.const_mul_atTop_of_neg (sub_neg.mpr huv))).const_mul 2
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim
    (Eventually.of_forall fun x => by positivity) ?_
  filter_upwards [eventually_ge_atTop 0] with x hx
  have h1 : Real.cosh (u * x) ≤ Real.exp (u * x) := by
    rw [Real.cosh_eq]
    have : Real.exp (-(u * x)) ≤ Real.exp (u * x) :=
      Real.exp_le_exp.mpr (by nlinarith)
    linarith
  have h2 : Real.exp (v * x) / 2 ≤ Real.cosh (v * x) := by
    rw [Real.cosh_eq]; linarith [Real.exp_pos (-(v * x))]
  rw [div_le_iff₀ (Real.cosh_pos _)]
  calc Real.cosh (u * x) ≤ Real.exp (u * x) := h1
    _ = 2 * Real.exp ((u - v) * x) * (Real.exp (v * x) / 2) := by
      rw [show (u - v) * x = u * x - v * x by ring, Real.exp_sub]; field_simp
    _ ≤ 2 * Real.exp ((u - v) * x) * Real.cosh (v * x) := by gcongr

/-- **Rigidity of bounded modes.** If the modes `Σ_r 2cosh(d_r mℓ) z_r^m`, `1 ≤ m < P`, stay
bounded by `2P` along unboundedly many scales `ℓ`, then all depths are equal and the points
`z_r ≠ 0` have one common `P`-th power. -/
theorem uniform_crystal_of_frequently_bounded_modes {P : ℕ} (d : Fin P → ℝ) (hd0 : ∀ r, 0 < d r)
    (z : Fin P → ℂ) (hz : ∀ r, z r ≠ 0)
    (h : ∃ᶠ ℓ in atTop, ∀ m : ℕ, 1 ≤ m → m < P →
      ‖∑ r, ((2 * Real.cosh (d r * (m * ℓ)) : ℝ) : ℂ) * z r ^ m‖ ≤ 2 * P) :
    (∀ r r', d r = d r') ∧ ∀ r r', z r ^ P = z r' ^ P := by
  rcases Nat.eq_zero_or_pos P with rfl | hP
  · exact ⟨fun r => r.elim0, fun r => r.elim0⟩
  haveI : Nonempty (Fin P) := ⟨⟨0, hP⟩⟩
  set dmax : ℝ := Finset.univ.sup' Finset.univ_nonempty d with hdmax
  have hle : ∀ r, d r ≤ dmax := fun r => Finset.le_sup' d (Finset.mem_univ r)
  set S : Finset (Fin P) := Finset.univ.filter fun r => d r = dmax with hS
  -- the deepest pairs dominate every mode
  have key : ∀ m : ℕ, 1 ≤ m → m < P → ∑ r ∈ S, z r ^ m = 0 := by
    intro m hm1 hmP
    have hm : (0 : ℝ) < m := by exact_mod_cast hm1
    have hdpos : 0 < dmax := lt_of_lt_of_le (hd0 ⟨0, hP⟩) (hle _)
    set G : ℝ → ℂ := fun ℓ => ∑ r, ((Real.cosh (d r * (m * ℓ)) /
      Real.cosh (dmax * (m * ℓ)) : ℝ) : ℂ) * z r ^ m with hG
    have hmℓ : Tendsto (fun ℓ : ℝ => (m : ℝ) * ℓ) atTop atTop := tendsto_id.const_mul_atTop hm
    have hGlim : Tendsto G atTop (𝓝 (∑ r ∈ S, z r ^ m)) := by
      rw [hS, Finset.sum_filter]
      refine tendsto_finsetSum _ fun r _ => ?_
      by_cases hr : d r = dmax
      · rw [if_pos hr]
        have : (fun ℓ : ℝ => ((Real.cosh (d r * (m * ℓ)) / Real.cosh (dmax * (m * ℓ)) : ℝ) : ℂ) *
            z r ^ m) = fun _ => z r ^ m := by
          funext ℓ; rw [hr, div_self (Real.cosh_pos _).ne', Complex.ofReal_one, one_mul]
        rw [this]; exact tendsto_const_nhds
      · rw [if_neg hr, show (0 : ℂ) = ((0 : ℝ) : ℂ) * z r ^ m by simp]
        refine (Complex.continuous_ofReal.tendsto _ |>.comp
          ((tendsto_cosh_div_cosh (hd0 r).le (lt_of_le_of_ne (hle r) hr)).comp hmℓ)).mul_const _
    have hBlim : Tendsto (fun ℓ : ℝ => (P : ℝ) / Real.cosh (dmax * (m * ℓ))) atTop (𝓝 0) := by
      have := ((tendsto_cosh_div_cosh le_rfl hdpos).comp hmℓ).const_mul (P : ℝ)
      simpa [Function.comp_def, div_eq_mul_inv] using this
    by_contra hne
    have hε : 0 < ‖∑ r ∈ S, z r ^ m‖ := norm_pos_iff.mpr hne
    have e1 := hGlim.norm.eventually (lt_mem_nhds (half_lt_self hε))
    have e2 := hBlim.eventually (gt_mem_nhds (half_pos hε))
    obtain ⟨ℓ, hℓ, h1, h2⟩ := (h.and_eventually (e1.and e2)).exists
    have hb := hℓ m hm1 hmP
    have hGeq : G ℓ = ((2 * Real.cosh (dmax * (m * ℓ)))⁻¹ : ℝ) *
        ∑ r, ((2 * Real.cosh (d r * (m * ℓ)) : ℝ) : ℂ) * z r ^ m := by
      rw [hG, Finset.mul_sum]
      refine Finset.sum_congr rfl fun r _ => ?_
      have : Real.cosh (dmax * (m * ℓ)) ≠ 0 := (Real.cosh_pos _).ne'
      push_cast
      field_simp
    have hGb : ‖G ℓ‖ ≤ P / Real.cosh (dmax * (m * ℓ)) := by
      rw [hGeq, norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (by have := Real.cosh_pos (dmax * (m * ℓ)); positivity)]
      rw [mul_comm, ← div_eq_mul_inv, div_le_div_iff₀ (by positivity) (Real.cosh_pos _)]
      nlinarith [Real.cosh_pos (dmax * (m * ℓ))]
    linarith
  -- fewer than `P` deepest pairs are impossible
  have hSfull : S.card = P := by
    by_contra hne
    have hlt : S.card < P := lt_of_le_of_ne ((Finset.card_filter_le _ _).trans
      (by simp)) hne
    obtain ⟨r₀, -, hr₀⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty d
    haveI : Nonempty S := ⟨⟨r₀, by rw [hS, Finset.mem_filter]; exact ⟨Finset.mem_univ _,
      hr₀.symm⟩⟩⟩
    refine not_forall_powerSum_eq_zero (fun i : S => z i) (fun i => hz i) fun m hm1 hmS => ?_
    rw [Fintype.card_coe] at hmS
    rw [Finset.sum_coe_sort S (fun r => z r ^ m)]
    exact key m hm1 (by omega)
  have hall : ∀ r, d r = dmax := by
    have := Finset.filter_card_eq (s := Finset.univ) (p := fun r => d r = dmax)
      (by rw [← hS, hSfull, Finset.card_univ, Fintype.card_fin])
    exact fun r => this r (Finset.mem_univ r)
  have hSuniv : S = Finset.univ := by
    rw [hS]; exact Finset.filter_true_of_mem fun r _ => hall r
  refine ⟨fun r r' => (hall r).trans (hall r').symm, fun r r' => ?_⟩
  have := pow_card_eq_of_powerSums z (fun m hm1 hmP => by
    rw [Fintype.card_fin] at hmP
    have := key m hm1 hmP
    rwa [hSuniv] at this) r r'
  rwa [Fintype.card_fin] at this

/-- Equal `P`-th powers of the phase points mean `P(θ_r − θ_{r'}) ∈ ℤ`. -/
theorem exists_int_of_phasePoint_pow_eq {P : ℕ} (θ : Fin P → ℝ) {r r' : Fin P}
    (h : phasePoint θ r ^ P = phasePoint θ r' ^ P) : ∃ k : ℤ, P * θ r - P * θ r' = k := by
  rw [phasePoint, phasePoint, ← Complex.exp_nat_mul, ← Complex.exp_nat_mul,
    Complex.exp_eq_exp_iff_exists_int] at h
  obtain ⟨k, hk⟩ := h
  refine ⟨k, ?_⟩
  have him := congrArg Complex.im hk
  simp only [Complex.mul_im, Complex.mul_re, Complex.add_im, Complex.natCast_re,
    Complex.natCast_im, Complex.intCast_re, Complex.intCast_im, Complex.ofReal_re,
    Complex.ofReal_im, Complex.I_re, Complex.I_im, Complex.re_ofNat, Complex.im_ofNat] at him
  have hpi := Real.pi_pos
  have : 2 * π * (P * θ r - P * θ r' - k) = 0 := by linarith
  rcases mul_eq_zero.mp this with h0 | h0
  · linarith
  · linarith

/-- The crystal condition gives distinct phase points with one common `P`-th power. -/
theorem phasePoint_pow_eq_of_crystal {P : ℕ} (θ : Fin P → ℝ)
    (hcr : ∀ r r' : Fin P, ∃ k : ℤ, P * θ r - P * θ r' = k) (r r' : Fin P) :
    phasePoint θ r ^ P = phasePoint θ r' ^ P := by
  obtain ⟨k, hk⟩ := hcr r r'
  rw [phasePoint, phasePoint, ← Complex.exp_nat_mul, ← Complex.exp_nat_mul,
    Complex.exp_eq_exp_iff_exists_int]
  refine ⟨k, ?_⟩
  have : (P : ℂ) * θ r = P * θ r' + k := by exact_mod_cast (by linarith : (P : ℝ) * θ r =
    P * θ r' + k)
  linear_combination (2 * π * I) * this

theorem phasePoint_injective {P : ℕ} {θ : Fin P → ℝ}
    (hθ : ∀ r r' : Fin P, ∀ j j' : ℤ, θ r + j = θ r' + j' → r = r' ∧ j = j') :
    Function.Injective (phasePoint θ) := by
  intro r r' h
  rw [phasePoint, phasePoint, Complex.exp_eq_exp_iff_exists_int] at h
  obtain ⟨k, hk⟩ := h
  have him := congrArg Complex.im hk
  simp only [Complex.mul_im, Complex.mul_re, Complex.add_im, Complex.intCast_re,
    Complex.intCast_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
    Complex.re_ofNat, Complex.im_ofNat] at him
  have hpi := Real.pi_pos
  have h2 : 2 * π * (θ r - θ r' - k) = 0 := by linarith
  have h3 : θ r + 0 = θ r' + k := by
    rcases mul_eq_zero.mp h2 with h0 | h0
    · linarith
    · linarith
  exact (hθ r r' 0 k (by exact_mod_cast h3)).1

/-- **Crystal rigidity at the square-root threshold.** A periodic off-line pattern of fixed shape
`(θ, d)` that hides at some aperture `a > (P−1)ℓ/2` at unboundedly many scales `ℓ` has uniform
depth and crystalline ordinates `P(θ_r − θ_{r'}) ∈ ℤ`. -/
theorem uniform_crystal_of_hiding {P : ℕ} (θ d : Fin P → ℝ) (hd0 : ∀ r, 0 < d r)
    (hd1 : ∀ r, d r ≤ 1 / 2)
    (hθ : ∀ r r' : Fin P, ∀ j j' : ℤ, θ r + j = θ r' + j' → r = r' ∧ j = j')
    (h : ∀ ℓ₀ : ℝ, ∃ ℓ : ℝ, ∃ hℓ : 0 < ℓ, ℓ₀ ≤ ℓ ∧ ∃ a : ℝ, ((P : ℝ) - 1) * ℓ / 2 < a ∧
      ∀ f : ℝ → ℂ, ContDiff ℝ 2 f → tsupport f ⊆ Icc (-a) a →
        0 ≤ ((patternConfig hℓ (scaledOffset ℓ θ) d hd0 hd1).W f f).re) :
    (∀ r r', d r = d r') ∧ ∀ r r', ∃ k : ℤ, P * θ r - P * θ r' = k := by
  have hfreq : ∃ᶠ ℓ in atTop, ∀ m : ℕ, 1 ≤ m → m < P →
      ‖∑ r, ((2 * Real.cosh (d r * (m * ℓ)) : ℝ) : ℂ) * phasePoint θ r ^ m‖ ≤ 2 * P := by
    rw [frequently_atTop]
    intro ℓ₀
    obtain ⟨ℓ, hℓ, hℓ₀, a, ha, hhide⟩ := h ℓ₀
    refine ⟨ℓ, hℓ₀, fun m hm1 hmP => ?_⟩
    rw [← patternSymbol_scaledOffset hℓ]
    exact norm_patternSymbol_le_of_hiding hℓ _ d hd0 hd1 (scaledOffset_injective hℓ hθ) ha hhide
      hm1 hmP
  obtain ⟨hd, hz⟩ := uniform_crystal_of_frequently_bounded_modes d hd0 _
    (phasePoint_ne_zero θ) hfreq
  exact ⟨hd, fun r r' => exists_int_of_phasePoint_pow_eq θ (hz r r')⟩

/-- **Visibility below the threshold.** Every periodic off-line pattern other than a uniform
crystal is visible, at all large scales `ℓ`, at every aperture `a > (P−1)ℓ/2`, strictly below
the square-root threshold `Pℓ/2`. -/
theorem exists_visible_of_not_uniform_crystal {P : ℕ} (θ d : Fin P → ℝ) (hd0 : ∀ r, 0 < d r)
    (hd1 : ∀ r, d r ≤ 1 / 2)
    (hθ : ∀ r r' : Fin P, ∀ j j' : ℤ, θ r + j = θ r' + j' → r = r' ∧ j = j')
    (hnot : ¬ ((∀ r r', d r = d r') ∧ ∀ r r', ∃ k : ℤ, P * θ r - P * θ r' = k)) :
    ∃ ℓ₀ : ℝ, ∀ ℓ : ℝ, ∀ hℓ : 0 < ℓ, ℓ₀ ≤ ℓ → ∀ a : ℝ, ((P : ℝ) - 1) * ℓ / 2 < a →
      ∃ f : ℝ → ℂ, ContDiff ℝ 2 f ∧ tsupport f ⊆ Icc (-a) a ∧
        ((patternConfig hℓ (scaledOffset ℓ θ) d hd0 hd1).W f f).re < 0 := by
  by_contra hcon
  push Not at hcon
  exact hnot (uniform_crystal_of_hiding θ d hd0 hd1 hθ hcon)

/-- **The uniform crystal hides.** Uniform depth and crystalline ordinates hide up to the
square-root threshold `Pℓ/2` at every scale `ℓ`. -/
theorem uniform_crystal_hides {P : ℕ} (θ d : Fin P → ℝ) (hd0 : ∀ r, 0 < d r)
    (hd1 : ∀ r, d r ≤ 1 / 2)
    (hθ : ∀ r r' : Fin P, ∀ j j' : ℤ, θ r + j = θ r' + j' → r = r' ∧ j = j')
    (hunif : ∀ r r', d r = d r') (hcr : ∀ r r', ∃ k : ℤ, P * θ r - P * θ r' = k)
    {ℓ : ℝ} (hℓ : 0 < ℓ) {a : ℝ} (ha : 0 < a) (haP : a ≤ P * ℓ / 2) {f : ℝ → ℂ}
    (hf : ContDiff ℝ 2 f) (hfs : tsupport f ⊆ Icc (-a) a) :
    0 ≤ ((patternConfig hℓ (scaledOffset ℓ θ) d hd0 hd1).W f f).re := by
  have hW := weil_nonneg_iff_toeplitz_of_lagFormula (patternConfig hℓ (scaledOffset ℓ θ) d hd0 hd1)
    hℓ _ (fun f hf hfc => W_patternConfig hℓ _ d hd0 hd1 (scaledOffset_injective hℓ hθ) hf hfc) ha
  refine hW.mpr ?_ f hf hfs
  intro c
  set D := patternSymbol ℓ (scaledOffset ℓ θ) d with hD
  have hnP : ⌈2 * a / ℓ⌉₊ ≤ P := by
    rw [Nat.ceil_le, div_le_iff₀ hℓ]; linarith
  -- the modes `0 < |m| < P` vanish
  have hmode : ∀ k : ℕ, 1 ≤ k → k < P → D k = 0 := by
    intro k hk1 hkP
    rw [hD, patternSymbol_scaledOffset hℓ]
    have hdr : ∀ r, d r = d ⟨0, by omega⟩ := fun r => hunif r _
    simp_rw [hdr, ← Finset.mul_sum]
    rw [powerSum_eq_zero_of_pow_eq _ (phasePoint_injective hθ)
      (fun i => phasePoint_pow_eq_of_crystal θ hcr i ⟨0, by omega⟩) hk1 hkP, mul_zero]
  have hzero : ∀ m ∈ (Finset.Ioo (-(⌈2 * a / ℓ⌉₊ : ℤ)) ⌈2 * a / ℓ⌉₊).erase 0, ‖D m‖ = 0 := by
    intro m hm
    rw [Finset.mem_erase, Finset.mem_Ioo] at hm
    obtain ⟨k, rfl | rfl⟩ := Int.eq_nat_or_neg m
    · rw [hmode k (by omega) (by omega), norm_zero]
    · rw [hD, patternSymbol_neg, Complex.norm_conj, ← hD, hmode k (by omega) (by omega),
        norm_zero]
  have hG := re_toeplitzForm_ge D c
  rw [Finset.sum_eq_zero hzero, sub_zero, hD, patternSymbol_zero,
    show (2 * (P : ℂ)).re = 2 * P by simp] at hG
  exact le_trans (by positivity : (0 : ℝ) ≤ 2 * P * ∑ j, ‖c j‖ ^ 2) hG

end GaloisForLFunctions.SquareRootThreshold
