import GaloisForLFunctions.SquareRootThreshold.PeriodicDepthProfileToeplitzLaw

/-!
# Depth profiles are seen through the Fourier modes of `cosh(depth)`

By the Toeplitz law (`profileConfig_weil_nonneg_iff`), a periodic depth profile `d : ℤ/P → [0, ½]`
in a lattice of spacing `2π/L` is seen at aperture `a` only through the values `D(m)`,
`|m| < n = ⌈2aP/L⌉`, of its depth symbol

`D(m) = 2 Σ_r cosh(d_r mL/P) e^{2πirm/P}`,

that is, through the discrete Fourier modes of the **cosh-depth profile** `r ↦ cosh(d_r mL/P)`.
The zero mode is `D(0) = 2P` for every profile; `D(−m) = conj D(m)`.

* **Mode bound** (`norm_depthSymbol_le_of_weil_nonneg`): invisibility at aperture `a` forces
  `|D(m)| ≤ 2P` for every `1 ≤ m < n`.
* **Mode criterion** (`profileConfig_weil_nonneg_of_modes`): if `2 Σ_{1 ≤ m < n} |D(m)| ≤ 2P`, the
  profile is invisible at aperture `a` (Gershgorin for the Toeplitz matrix).
* **First-mode law** (`profileConfig_weil_nonneg_iff_first_mode`): on the aperture range
  `L/(2P) < a ≤ L/P` the profile is invisible **iff** `|Σ_r cosh(d_r L/P) e^{2πir/P}| ≤ P`.
* **Depth-contrast law** (`twoProfile_weil_nonneg_iff`): two interleaved lattices of depths
  `δ₀, δ₁` (period `2`) are invisible on `L/4 < a ≤ L/2` iff `|cosh(δ₀L/2) − cosh(δ₁L/2)| ≤ 2`.

A constant depth has no nonzero mode below `m = P`, so it hides up to the Nyquist aperture `L/2`
whatever its size (the lattice law). What becomes visible below `L/2` is the **variation** of the
depth along the ordinate, weighted exponentially by `cosh`: the alternating profile `(δ, 0)` is
seen at `L/4` as soon as `cosh(δL/2) > 3`.
-/

open MeasureTheory Complex Set Filter Topology
open scoped Real ComplexConjugate

noncomputable section

namespace GaloisForLFunctions.SquareRootThreshold

open Zeta23 _root_.RHTower

/-! ### The zero mode and the symmetry of the symbol -/

theorem depthSymbol_zero (L : ℝ) {P : ℕ} (d : Fin P → ℝ) : depthSymbol L d 0 = 2 * P := by
  simp [depthSymbol]
  ring

theorem depthSymbol_neg (L : ℝ) {P : ℕ} (d : Fin P → ℝ) (m : ℤ) :
    depthSymbol L d (-m) = conj (depthSymbol L d m) := by
  rw [depthSymbol, depthSymbol, map_sum]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [map_mul, Complex.conj_ofReal, ← Complex.exp_conj]
  congr 1
  · rw [Int.cast_neg, neg_mul, mul_neg, Real.cosh_neg]
  · congr 1
    simp only [map_div₀, map_mul, map_ofNat, Complex.conj_ofReal, Complex.conj_I,
      map_intCast, map_natCast]
    push_cast
    ring

/-! ### Two-by-two Toeplitz forms -/

/-- The `2 × 2` Toeplitz form is `D(0)(|c₀|² + |c₁|²) + 2 Re(c₁ conj(c₀) D(1))` when
`D(−1) = conj D(1)`. -/
theorem toeplitzForm_two_re {D : ℤ → ℂ} (hD : D (-1) = conj (D 1)) (c : Fin 2 → ℂ) :
    (toeplitzForm D 2 c).re = (D 0).re * (‖c 0‖ ^ 2 + ‖c 1‖ ^ 2) +
      2 * (c 1 * conj (c 0) * D 1).re := by
  simp only [toeplitzForm, Fin.sum_univ_two, Fin.val_zero, Fin.val_one, Nat.cast_zero,
    Nat.cast_one, sub_self, zero_sub, sub_zero, hD]
  simp only [Complex.add_re, Complex.mul_re, Complex.conj_re, Complex.conj_im, Complex.mul_im,
    ← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
  ring

/-- **The `2 × 2` criterion.** For a Hermitian symbol with real zero mode, the `2 × 2` Toeplitz
form is positive semidefinite iff `|D(1)| ≤ D(0)`. -/
theorem toeplitzForm_two_nonneg_iff {D : ℤ → ℂ} (hD : D (-1) = conj (D 1)) :
    (∀ c : Fin 2 → ℂ, 0 ≤ (toeplitzForm D 2 c).re) ↔ ‖D 1‖ ≤ (D 0).re := by
  constructor
  · intro h
    by_cases h1 : D 1 = 0
    · have := h ![1, 0]
      rw [toeplitzForm_two_re hD] at this
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, norm_one,
        norm_zero, zero_mul, Complex.zero_re, mul_zero, add_zero] at this
      rw [h1, norm_zero]; nlinarith
    · set w : ℂ := -(conj (D 1) / ‖D 1‖) with hw
      have hn : (‖D 1‖ : ℂ) ≠ 0 := by exact_mod_cast norm_ne_zero_iff.mpr h1
      have hwn : ‖w‖ = 1 := by
        rw [hw, norm_neg, norm_div, Complex.norm_conj, Complex.norm_real, norm_norm,
          div_self (norm_ne_zero_iff.mpr h1)]
      have hwD : (w * conj (1 : ℂ) * D 1).re = -‖D 1‖ := by
        rw [map_one, mul_one, hw, neg_mul, div_mul_eq_mul_div, ← Complex.normSq_eq_conj_mul_self,
          Complex.normSq_eq_norm_sq]
        rw [show ((‖D 1‖ ^ 2 : ℝ) : ℂ) / (‖D 1‖ : ℂ) = ((‖D 1‖ : ℝ) : ℂ) by
          push_cast; field_simp]
        simp
      have := h ![1, w]
      rw [toeplitzForm_two_re hD] at this
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, norm_one, hwn, hwD] at this
      nlinarith
  · intro h c
    rw [toeplitzForm_two_re hD]
    have hb : -(‖c 1‖ * ‖c 0‖ * ‖D 1‖) ≤ (c 1 * conj (c 0) * D 1).re := by
      have := Complex.abs_re_le_norm (c 1 * conj (c 0) * D 1)
      rw [norm_mul, norm_mul, Complex.norm_conj] at this
      linarith [neg_abs_le (c 1 * conj (c 0) * D 1).re]
    have h2 : 2 * (‖c 1‖ * ‖c 0‖) ≤ ‖c 0‖ ^ 2 + ‖c 1‖ ^ 2 := by
      nlinarith [sq_nonneg (‖c 0‖ - ‖c 1‖)]
    have h3 : 0 ≤ ‖c 1‖ * ‖c 0‖ := by positivity
    nlinarith [norm_nonneg (D 1)]

/-! ### Necessity of the mode bound and the Gershgorin criterion -/

/-- The Toeplitz sum of a vector supported on two indices `0` and `m ≠ 0`. -/
theorem toeplitzSum_pair {D : ℤ → ℂ} {m : ℤ} (hm : m ≠ 0) (w : ℂ) :
    toeplitzSum D {0, m} (fun j => if j = 0 then 1 else if j = m then w else 0) =
      (1 + ‖w‖ ^ 2) * D 0 + conj w * D (-m) + w * D m := by
  have hm' : (0 : ℤ) ≠ m := hm.symm
  simp only [toeplitzSum, Finset.sum_pair hm', if_neg hm, if_pos, zero_sub, sub_zero,
    sub_self, map_one, one_mul, mul_one]
  rw [← Complex.mul_conj']
  ring

/-- **Mode bound.** If the profile is Weil-nonnegative at aperture `a`, every mode `1 ≤ m < n`,
`n = ⌈2aP/L⌉`, of the depth symbol satisfies `|D(m)| ≤ 2P`. -/
theorem norm_depthSymbol_le_of_weil_nonneg {L : ℝ} (hL : 0 < L) {P : ℕ} (hP : 0 < P)
    (d : Fin P → ℝ) (hd0 : ∀ r, 0 ≤ d r) (hd1 : ∀ r, d r ≤ 1 / 2) {a : ℝ} (ha : 0 < a)
    (h : ∀ f : ℝ → ℂ, ContDiff ℝ 2 f → tsupport f ⊆ Icc (-a) a →
      0 ≤ ((profileConfig hL hP d hd0 hd1).W f f).re) {m : ℕ} (hm1 : 1 ≤ m)
    (hmn : m < ⌈2 * a * P / L⌉₊) : ‖depthSymbol L d m‖ ≤ 2 * P := by
  rw [profileConfig_weil_nonneg_iff hL hP d hd0 hd1 ha] at h
  set n := ⌈2 * a * P / L⌉₊ with hn
  set D := depthSymbol L d with hDdef
  have hm0 : (m : ℤ) ≠ 0 := by exact_mod_cast (by omega : m ≠ 0)
  -- the two-point test vector `e₀ + w eₘ`
  have key : ∀ w : ℂ, 0 ≤ 2 * P * (1 + ‖w‖ ^ 2) + 2 * (w * D m).re := by
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
    have h1 := h fun i => c (0 + i)
    rw [heq, hDdef, depthSymbol_neg, depthSymbol_zero, ← map_mul, Complex.add_re,
      Complex.add_re, Complex.conj_re,
      show (1 + (‖w‖ : ℂ) ^ 2) * (2 * (P : ℂ)) = (((1 + ‖w‖ ^ 2) * (2 * P) : ℝ) : ℂ) by
        push_cast; ring, Complex.ofReal_re] at h1
    linarith
  by_cases hD : D m = 0
  · rw [hD, norm_zero]; positivity
  set w : ℂ := -(conj (D m) / ‖D m‖) with hw
  have hwn : ‖w‖ = 1 := by
    rw [hw, norm_neg, norm_div, Complex.norm_conj, Complex.norm_real, norm_norm,
      div_self (norm_ne_zero_iff.mpr hD)]
  have hwD : (w * D m).re = -‖D m‖ := by
    rw [hw, neg_mul, div_mul_eq_mul_div, ← Complex.normSq_eq_conj_mul_self,
      Complex.normSq_eq_norm_sq]
    rw [show ((‖D m‖ ^ 2 : ℝ) : ℂ) / (‖D m‖ : ℂ) = ((‖D m‖ : ℝ) : ℂ) by
      have : (‖D m‖ : ℂ) ≠ 0 := by exact_mod_cast norm_ne_zero_iff.mpr hD
      push_cast; field_simp]
    simp
  have := key w
  rw [hwn, hwD] at this
  nlinarith

/-- **Gershgorin bound for Toeplitz forms.**
`Re ⟨T c, c⟩ ≥ (Re D(0) − Σ_{0 < |m| < n} |D(m)|) ‖c‖²`. -/
theorem re_toeplitzForm_ge (D : ℤ → ℂ) {n : ℕ} (c : Fin n → ℂ) :
    ((D 0).re - ∑ m ∈ (Finset.Ioo (-(n : ℤ)) n).erase 0, ‖D m‖) * ∑ j, ‖c j‖ ^ 2 ≤
      (toeplitzForm D n c).re := by
  set G := ∑ m ∈ (Finset.Ioo (-(n : ℤ)) n).erase 0, ‖D m‖ with hG
  -- row and column sums of the off-diagonal moduli
  have hrow : ∀ j : Fin n, ∑ j' ∈ Finset.univ.erase j, ‖D ((j : ℤ) - j')‖ ≤ G := by
    intro j
    have hinj : Set.InjOn (fun j' : Fin n => (j : ℤ) - j') (Finset.univ.erase j : Finset _) := by
      intro x _ y _ h
      simp only at h
      exact Fin.ext (by omega)
    rw [← Finset.sum_image (f := fun m => ‖D m‖) hinj]
    refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun _ _ _ => norm_nonneg _
    intro m hm
    simp only [Finset.mem_image, Finset.mem_erase, Finset.mem_univ, and_true] at hm
    obtain ⟨j', hj', rfl⟩ := hm
    have h1 := j.isLt; have h2 := j'.isLt
    have hne : (j : ℕ) ≠ j' := fun h => hj' (Fin.ext h.symm)
    simp only [Finset.mem_erase, Finset.mem_Ioo]
    omega
  have hcol : ∀ j' : Fin n, ∑ j ∈ Finset.univ.erase j', ‖D ((j : ℤ) - j')‖ ≤ G := by
    intro j'
    have hinj : Set.InjOn (fun j : Fin n => (j : ℤ) - j') (Finset.univ.erase j' : Finset _) := by
      intro x _ y _ h
      simp only at h
      exact Fin.ext (by omega)
    rw [← Finset.sum_image (f := fun m => ‖D m‖) hinj]
    refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun _ _ _ => norm_nonneg _
    intro m hm
    simp only [Finset.mem_image, Finset.mem_erase, Finset.mem_univ, and_true] at hm
    obtain ⟨j, hj, rfl⟩ := hm
    have h1 := j.isLt; have h2 := j'.isLt
    have hne : (j : ℕ) ≠ j' := fun h => hj (Fin.ext h)
    simp only [Finset.mem_erase, Finset.mem_Ioo]
    omega
  -- termwise lower bound
  have hterm : ∀ j j' : Fin n, (if j = j' then ‖c j‖ ^ 2 * (D 0).re else
      -((‖c j‖ ^ 2 + ‖c j'‖ ^ 2) / 2 * ‖D ((j : ℤ) - j')‖)) ≤
      (c j * conj (c j') * D ((j : ℤ) - j')).re := by
    intro j j'
    split_ifs with h
    · subst h
      rw [sub_self, Complex.mul_conj, Complex.normSq_eq_norm_sq, Complex.re_ofReal_mul]
    · have hb := Complex.abs_re_le_norm (c j * conj (c j') * D ((j : ℤ) - j'))
      rw [norm_mul, norm_mul, Complex.norm_conj] at hb
      have h2 : ‖c j‖ * ‖c j'‖ ≤ (‖c j‖ ^ 2 + ‖c j'‖ ^ 2) / 2 := by
        nlinarith [sq_nonneg (‖c j‖ - ‖c j'‖)]
      have := mul_le_mul_of_nonneg_right h2 (norm_nonneg (D ((j : ℤ) - j')))
      linarith [neg_abs_le (c j * conj (c j') * D ((j : ℤ) - j')).re]
  have hsum : ∑ j : Fin n, ∑ j' : Fin n, (if j = j' then ‖c j‖ ^ 2 * (D 0).re else
      -((‖c j‖ ^ 2 + ‖c j'‖ ^ 2) / 2 * ‖D ((j : ℤ) - j')‖)) ≤ (toeplitzForm D n c).re := by
    rw [toeplitzForm, Complex.re_sum]
    refine Finset.sum_le_sum fun j _ => ?_
    rw [Complex.re_sum]
    exact Finset.sum_le_sum fun j' _ => hterm j j'
  refine le_trans ?_ hsum
  -- evaluate the lower bound
  have hsplit : ∀ j : Fin n, ∑ j' : Fin n, (if j = j' then ‖c j‖ ^ 2 * (D 0).re else
      -((‖c j‖ ^ 2 + ‖c j'‖ ^ 2) / 2 * ‖D ((j : ℤ) - j')‖)) =
      ‖c j‖ ^ 2 * (D 0).re - (‖c j‖ ^ 2 / 2 * ∑ j' ∈ Finset.univ.erase j, ‖D ((j : ℤ) - j')‖ +
        ∑ j' ∈ Finset.univ.erase j, ‖c j'‖ ^ 2 / 2 * ‖D ((j : ℤ) - j')‖) := by
    intro j
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ j), if_pos rfl, Finset.mul_sum,
      ← Finset.sum_add_distrib, sub_eq_add_neg, ← Finset.sum_neg_distrib]
    congr 1
    refine Finset.sum_congr rfl fun j' hj' => ?_
    rw [if_neg (Finset.ne_of_mem_erase hj').symm]
    ring
  simp_rw [hsplit]
  rw [Finset.sum_sub_distrib, Finset.sum_add_distrib]
  -- the column part, by exchanging the order of summation
  have hswap : ∑ j : Fin n, ∑ j' ∈ Finset.univ.erase j, ‖c j'‖ ^ 2 / 2 * ‖D ((j : ℤ) - j')‖ =
      ∑ j' : Fin n, ‖c j'‖ ^ 2 / 2 * ∑ j ∈ Finset.univ.erase j', ‖D ((j : ℤ) - j')‖ := by
    have h1 : ∀ j : Fin n, ∑ j' ∈ Finset.univ.erase j, ‖c j'‖ ^ 2 / 2 * ‖D ((j : ℤ) - j')‖ =
        ∑ j' : Fin n, if j' = j then 0 else ‖c j'‖ ^ 2 / 2 * ‖D ((j : ℤ) - j')‖ := by
      intro j
      rw [← Finset.sum_erase_add _ _ (Finset.mem_univ j), if_pos rfl, add_zero]
      exact Finset.sum_congr rfl fun j' hj' => by rw [if_neg (Finset.ne_of_mem_erase hj')]
    have h2 : ∀ j' : Fin n, ‖c j'‖ ^ 2 / 2 * ∑ j ∈ Finset.univ.erase j', ‖D ((j : ℤ) - j')‖ =
        ∑ j : Fin n, if j' = j then 0 else ‖c j'‖ ^ 2 / 2 * ‖D ((j : ℤ) - j')‖ := by
      intro j'
      rw [Finset.mul_sum, ← Finset.sum_erase_add _ _ (Finset.mem_univ j'), if_pos rfl, add_zero]
      exact Finset.sum_congr rfl fun j hj => by
        rw [if_neg (Finset.ne_of_mem_erase hj).symm]
    simp_rw [h1, h2]
    exact Finset.sum_comm
  rw [hswap]
  have hA : ∑ j : Fin n, ‖c j‖ ^ 2 / 2 * ∑ j' ∈ Finset.univ.erase j, ‖D ((j : ℤ) - j')‖ ≤
      ∑ j : Fin n, ‖c j‖ ^ 2 / 2 * G :=
    Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_left (hrow j) (by positivity)
  have hB : ∑ j' : Fin n, ‖c j'‖ ^ 2 / 2 * ∑ j ∈ Finset.univ.erase j', ‖D ((j : ℤ) - j')‖ ≤
      ∑ j' : Fin n, ‖c j'‖ ^ 2 / 2 * G :=
    Finset.sum_le_sum fun j' _ => mul_le_mul_of_nonneg_left (hcol j') (by positivity)
  have hC : ∑ j : Fin n, ‖c j‖ ^ 2 * (D 0).re = (D 0).re * ∑ j, ‖c j‖ ^ 2 := by
    rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun j _ => by ring
  have hE : ∑ j : Fin n, ‖c j‖ ^ 2 / 2 * G = G / 2 * ∑ j, ‖c j‖ ^ 2 := by
    rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun j _ => by ring
  rw [hC]
  linarith

/-- **Mode criterion.** If `Σ_{0 < |m| < n} |D(m)| ≤ 2P`, `n = ⌈2aP/L⌉`, the profile is
Weil-nonnegative at aperture `a`. -/
theorem profileConfig_weil_nonneg_of_modes {L : ℝ} (hL : 0 < L) {P : ℕ} (hP : 0 < P)
    (d : Fin P → ℝ) (hd0 : ∀ r, 0 ≤ d r) (hd1 : ∀ r, d r ≤ 1 / 2) {a : ℝ} (ha : 0 < a)
    (hmodes : ∑ m ∈ (Finset.Ioo (-(⌈2 * a * P / L⌉₊ : ℤ)) ⌈2 * a * P / L⌉₊).erase 0,
      ‖depthSymbol L d m‖ ≤ 2 * P) {f : ℝ → ℂ} (hf : ContDiff ℝ 2 f)
    (hfs : tsupport f ⊆ Icc (-a) a) : 0 ≤ ((profileConfig hL hP d hd0 hd1).W f f).re := by
  refine (profileConfig_weil_nonneg_iff hL hP d hd0 hd1 ha).mpr (fun c => ?_) f hf hfs
  refine le_trans ?_ (re_toeplitzForm_ge _ c)
  rw [depthSymbol_zero]
  have : ((2 : ℂ) * P).re = 2 * P := by simp
  rw [this]
  exact mul_nonneg (by linarith) (Finset.sum_nonneg fun j _ => by positivity)

/-! ### The first-mode law -/

/-- **First-mode law.** On the aperture range `L/(2P) < a ≤ L/P` a periodic depth profile is
Weil-nonnegative iff `|Σ_r cosh(d_r L/P) e^{2πir/P}| ≤ P`. -/
theorem profileConfig_weil_nonneg_iff_first_mode {L : ℝ} (hL : 0 < L) {P : ℕ} (hP : 0 < P)
    (d : Fin P → ℝ) (hd0 : ∀ r, 0 ≤ d r) (hd1 : ∀ r, d r ≤ 1 / 2) {a : ℝ}
    (ha1 : L / (2 * P) < a) (ha2 : a ≤ L / P) :
    (∀ f : ℝ → ℂ, ContDiff ℝ 2 f → tsupport f ⊆ Icc (-a) a →
        0 ≤ ((profileConfig hL hP d hd0 hd1).W f f).re) ↔
      ‖∑ r : Fin P, (Real.cosh (d r * (L / P)) : ℂ) * cexp (2 * π * I * r / P)‖ ≤ P := by
  have hPr : (0 : ℝ) < P := by exact_mod_cast hP
  have ha : 0 < a := lt_trans (by positivity) ha1
  have hn : ⌈2 * a * P / L⌉₊ = 2 := by
    rw [Nat.ceil_eq_iff (by norm_num)]
    constructor
    · rw [lt_div_iff₀ hL]
      rw [div_lt_iff₀ (by positivity)] at ha1
      push_cast; nlinarith
    · rw [div_le_iff₀ hL]
      rw [le_div_iff₀ hPr] at ha2
      push_cast; nlinarith
  rw [profileConfig_weil_nonneg_iff hL hP d hd0 hd1 ha, hn,
    toeplitzForm_two_nonneg_iff (by rw [← depthSymbol_neg]),
    depthSymbol_zero]
  have hD1 : depthSymbol L d 1 = 2 * ∑ r : Fin P, (Real.cosh (d r * (L / P)) : ℂ) *
      cexp (2 * π * I * r / P) := by
    rw [depthSymbol, Finset.mul_sum]
    refine Finset.sum_congr rfl fun r _ => ?_
    push_cast
    ring_nf
  rw [hD1, norm_mul, show ((2 : ℂ) * P).re = 2 * P by simp, Complex.norm_two]
  constructor <;> intro h <;> linarith

/-- **Depth-contrast law.** Two interleaved off-line lattices of depths `δ₀` and `δ₁` (the profile
of period `2`) are Weil-nonnegative on the aperture range `L/4 < a ≤ L/2` iff
`|cosh(δ₀L/2) − cosh(δ₁L/2)| ≤ 2`. A uniform depth always hides; depth contrast is seen. -/
theorem twoProfile_weil_nonneg_iff {L : ℝ} (hL : 0 < L) (d : Fin 2 → ℝ) (hd0 : ∀ r, 0 ≤ d r)
    (hd1 : ∀ r, d r ≤ 1 / 2) {a : ℝ} (ha1 : L / 4 < a) (ha2 : a ≤ L / 2) :
    (∀ f : ℝ → ℂ, ContDiff ℝ 2 f → tsupport f ⊆ Icc (-a) a →
        0 ≤ ((profileConfig hL (by norm_num) d hd0 hd1).W f f).re) ↔
      |Real.cosh (d 0 * (L / 2)) - Real.cosh (d 1 * (L / 2))| ≤ 2 := by
  have h := profileConfig_weil_nonneg_iff_first_mode hL (P := 2) (by norm_num) d hd0 hd1
    (a := a) (by norm_num; linarith) (by norm_num; linarith)
  rw [h, Fin.sum_univ_two]
  have he : cexp (2 * π * I * ((1 : Fin 2) : ℕ) / (2 : ℕ)) = -1 := by
    rw [show (2 * π * I * ((1 : Fin 2) : ℕ) / (2 : ℕ) : ℂ) = π * I by
      rw [Fin.val_one]; push_cast; ring,
      Complex.exp_pi_mul_I]
  rw [he, show cexp (2 * π * I * ((0 : Fin 2) : ℕ) / (2 : ℕ)) = 1 by simp]
  rw [show ((Real.cosh (d 0 * (L / (2 : ℕ))) : ℂ) * 1 +
      (Real.cosh (d 1 * (L / (2 : ℕ))) : ℂ) * -1) =
      ((Real.cosh (d 0 * (L / 2)) - Real.cosh (d 1 * (L / 2)) : ℝ) : ℂ) by push_cast; ring,
    Complex.norm_real, Real.norm_eq_abs]
  norm_num

end GaloisForLFunctions.SquareRootThreshold
