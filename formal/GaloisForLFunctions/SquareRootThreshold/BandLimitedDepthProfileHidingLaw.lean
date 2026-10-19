import GaloisForLFunctions.SquareRootThreshold.SmoothDepthProfileHidingLaw
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series

/-!
# Band-limited depth modulations hide up to half the Nyquist aperture

The generic smoothness law (`SmoothDepthProfileHidingLaw`) only controls two derivatives of the
profile and yields a hiding aperture logarithmic in the modulation length. For a **band-limited**
profile the depth symbol is much smaller. Take the cosine modulation of period `P`

`d_r = δ (1 + cos(2πr/P)) / 2 ∈ [0, δ]`.

Every power `d_r^{2n}` is a trigonometric polynomial of degree `2n` in `r`, so its discrete
Fourier coefficient at a frequency `m` with `2n < m ≤ P/2` vanishes
(`sum_cosProfile_pow_mul_root_eq_zero`). Expanding `cosh(v d_r)` and keeping only the Taylor
remainder of order `m` (`cosh_sub_taylor_le`) gives, with `ℓ = L/P`,

`|D(m)| ≤ 2P (e ℓ δ)^m e^{mℓδ}`  for `1 ≤ m ≤ P/2`  (`norm_depthSymbol_cosProfile_le`).

Summing the modes against the Gershgorin criterion: if `q = e ℓδ e^{ℓδ} ≤ 1/3`, i.e. the period
exceeds about `8δL` lattice steps, the modulation is **invisible at every aperture `a ≤ L/4`**
(`cosProfile_weil_nonneg`), half the Nyquist ceiling `L/2`, however deep the modulation is relative
to the background.

So the square-root threshold is not a privilege of uniform lattices: every slow band-limited depth
modulation hides within a factor two of it. The configurations that are seen early are the rough
ones — edges (`O(1/δ)`) and profiles with few derivatives.
-/

open MeasureTheory Complex Set Filter Topology
open scoped Real ComplexConjugate Nat

noncomputable section

namespace GaloisForLFunctions.SquareRootThreshold

open Zeta23 _root_.RHTower

/-! ### Taylor remainder of `cosh` -/

/-- `0 ≤ cosh y − Σ_{n<N} y^{2n}/(2n)! ≤ y^{2N} cosh y / (2N)!` for `y ≥ 0`. -/
theorem cosh_sub_taylor_le {y : ℝ} (hy : 0 ≤ y) (N : ℕ) :
    Real.cosh y - ∑ n ∈ Finset.range N, y ^ (2 * n) / ((2 * n)! : ℝ) ≤
      y ^ (2 * N) * Real.cosh y / ((2 * N)! : ℝ) := by
  have hs := Real.hasSum_cosh y
  have htail := (hs.summable.hasSum).tsum_eq
  rw [← hs.summable.sum_add_tsum_nat_add N] at htail
  have heq : Real.cosh y - ∑ n ∈ Finset.range N, y ^ (2 * n) / ((2 * n)! : ℝ) =
      ∑' j, y ^ (2 * (j + N)) / ((2 * (j + N))! : ℝ) := by
    rw [← hs.tsum_eq, ← hs.summable.sum_add_tsum_nat_add N]
    ring
  rw [heq]
  have hterm : ∀ j : ℕ, y ^ (2 * (j + N)) / ((2 * (j + N))! : ℝ) ≤
      y ^ (2 * N) / ((2 * N)! : ℝ) * (y ^ (2 * j) / ((2 * j)! : ℝ)) := by
    intro j
    have hfac : ((2 * N)! : ℝ) * ((2 * j)! : ℝ) ≤ ((2 * (j + N))! : ℝ) := by
      have h := Nat.factorial_mul_factorial_dvd_factorial_add (2 * N) (2 * j)
      have h' := Nat.le_of_dvd (Nat.factorial_pos _) h
      rw [show 2 * N + 2 * j = 2 * (j + N) by ring] at h'
      exact_mod_cast h'
    rw [div_mul_div_comm, ← pow_add, show 2 * N + 2 * j = 2 * (j + N) by ring]
    gcongr
  have hsum2 : Summable fun j : ℕ => y ^ (2 * N) / ((2 * N)! : ℝ) * (y ^ (2 * j) / ((2 * j)! : ℝ)) :=
    hs.summable.mul_left _
  calc ∑' j, y ^ (2 * (j + N)) / ((2 * (j + N))! : ℝ)
      ≤ ∑' j, y ^ (2 * N) / ((2 * N)! : ℝ) * (y ^ (2 * j) / ((2 * j)! : ℝ)) :=
        (hs.summable.comp_injective (add_left_injective N)).tsum_le_tsum hterm hsum2
    _ = y ^ (2 * N) * Real.cosh y / ((2 * N)! : ℝ) := by
        rw [tsum_mul_left, hs.tsum_eq]; ring

/-! ### The cosine profile and its vanishing Fourier modes -/

/-- The cosine depth modulation `d_r = δ (1 + cos(2πr/P)) / 2`. -/
def cosProfile (δ : ℝ) (P : ℕ) (r : Fin P) : ℝ := δ * (1 + Real.cos (2 * π * r / P)) / 2

theorem cosProfile_nonneg {δ : ℝ} (hδ : 0 ≤ δ) (P : ℕ) (r : Fin P) : 0 ≤ cosProfile δ P r := by
  have := Real.neg_one_le_cos (2 * π * r / P)
  unfold cosProfile; nlinarith

theorem cosProfile_le {δ : ℝ} (hδ : 0 ≤ δ) (P : ℕ) (r : Fin P) : cosProfile δ P r ≤ δ := by
  have := Real.cos_le_one (2 * π * r / P)
  unfold cosProfile; nlinarith

/-- A nontrivial `P`-th root of unity sums to zero over a period. -/
theorem sum_pow_eq_zero_of_root {P : ℕ} {β : ℂ} (hβP : β ^ P = 1) (hβ1 : β ≠ 1) :
    ∑ r : Fin P, β ^ (r : ℕ) = 0 := by
  rw [Fin.sum_univ_eq_sum_range (fun r => β ^ r) P, geom_sum_eq hβ1, hβP, sub_self, zero_div]

/-- The root of unity `ζ = e^{2πi/P}` has no power `ζ^e = 1` with `0 < e < P`. -/
theorem cexp_two_pi_I_div_pow_ne_one {P : ℕ} (hP : 0 < P) {e : ℕ} (he0 : 0 < e) (heP : e < P) :
    cexp (2 * π * I / P) ^ e ≠ 1 := by
  intro h
  have hPr : (0 : ℝ) < P := by exact_mod_cast hP
  have hθ : cexp (2 * π * I / P) ^ e = cexp (I * ((2 * π * e / P : ℝ) : ℂ)) := by
    rw [← Complex.exp_nat_mul]; congr 1; push_cast; ring
  have hn := Complex.norm_exp_I_mul_ofReal_sub_one (2 * π * e / P)
  rw [← hθ, h, sub_self, norm_zero, norm_mul, Real.norm_eq_abs, Real.norm_eq_abs,
    abs_two] at hn
  have he : (e : ℝ) < P := by exact_mod_cast heP
  have he' : (0 : ℝ) < e := by exact_mod_cast he0
  have hs : 0 < Real.sin (2 * π * e / P / 2) := by
    refine Real.sin_pos_of_pos_of_lt_pi (by positivity) ?_
    rw [show 2 * π * (e : ℝ) / P / 2 = π * (e / P) by ring]
    have : (e : ℝ) / P < 1 := (div_lt_one hPr).mpr he
    nlinarith [Real.pi_pos]
  have := abs_pos.mpr hs.ne'
  linarith

/-- **Vanishing modes.** For `2n < m` and `2m ≤ P`, the discrete Fourier coefficient at `m` of
`d_r^{2n}` vanishes: `d_r = (δ/4)(1 + ζ^r)(1 + ζ^{−r})` has degree one in `ζ^r`. -/
theorem sum_cosProfile_pow_mul_root_eq_zero (δ : ℝ) {P : ℕ} (hP : 0 < P) {n m : ℕ}
    (hnm : 2 * n < m) (hmP : 2 * m ≤ P) :
    ∑ r : Fin P, ((cosProfile δ P r : ℝ) : ℂ) ^ (2 * n) * cexp (2 * π * I * r * m / P) = 0 := by
  set ζ : ℂ := cexp (2 * π * I / P) with hζ
  have hPc : (P : ℂ) ≠ 0 := by exact_mod_cast hP.ne'
  have hζP : ζ ^ P = 1 := by
    rw [hζ, ← Complex.exp_nat_mul, show (P : ℂ) * (2 * π * I / P) = 2 * π * I by field_simp]
    exact Complex.exp_two_pi_mul_I
  -- the profile in terms of `ζ^r` and `ζ^{(P-1)r} = ζ^{-r}`
  have hd : ∀ r : Fin P, ((cosProfile δ P r : ℝ) : ℂ) =
      δ / 4 * ((ζ ^ (r : ℕ) + 1) * (ζ ^ ((P - 1) * (r : ℕ)) + 1)) := by
    intro r
    have hw : ζ ^ (r : ℕ) = cexp (I * (2 * π * r / P : ℝ)) := by
      rw [hζ, ← Complex.exp_nat_mul]; congr 1; push_cast; ring
    have hw' : ζ ^ ((P - 1) * (r : ℕ)) = cexp (-(I * (2 * π * r / P : ℝ))) := by
      have hsplit : ζ ^ ((P - 1) * (r : ℕ)) * ζ ^ (r : ℕ) = 1 := by
        rw [← pow_add, show (P - 1) * (r : ℕ) + r = P * r by
          rcases Nat.exists_eq_succ_of_ne_zero hP.ne' with ⟨k, rfl⟩; simp; ring,
          pow_mul, hζP, one_pow]
      rw [eq_inv_of_mul_eq_one_left hsplit, hw, ← Complex.exp_neg]
    rw [hw, hw', cosProfile]
    push_cast
    rw [Complex.cos, show (2 * π * (r : ℂ) / P) * I = I * (2 * π * r / P) by ring,
      show -(2 * π * (r : ℂ) / P) * I = -(I * (2 * π * r / P)) by ring]
    have : cexp (I * (2 * π * r / P)) * cexp (-(I * (2 * π * r / P))) = 1 := by
      rw [← Complex.exp_add, add_neg_cancel, Complex.exp_zero]
    linear_combination (-(δ / 4) : ℂ) * this
  have hroot : ∀ r : Fin P, cexp (2 * π * I * r * m / P) = ζ ^ ((r : ℕ) * m) := by
    intro r; rw [hζ, ← Complex.exp_nat_mul]; congr 1; push_cast; ring
  -- expand into pure powers of `ζ`
  have hexp : ∀ r : Fin P, ((cosProfile δ P r : ℝ) : ℂ) ^ (2 * n) * cexp (2 * π * I * r * m / P) =
      (δ / 4 : ℂ) ^ (2 * n) * ∑ i ∈ Finset.range (2 * n + 1), ∑ j ∈ Finset.range (2 * n + 1),
        (((2 * n).choose i : ℂ) * ((2 * n).choose j : ℂ)) *
          (ζ ^ (i + (P - 1) * j + m)) ^ (r : ℕ) := by
    intro r
    rw [hd, hroot, mul_pow, mul_pow, add_pow, add_pow, Finset.sum_mul_sum, Finset.mul_sum,
      Finset.sum_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum, Finset.sum_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [one_pow, mul_one]
    ring
  simp_rw [hexp]
  rw [← Finset.mul_sum]
  refine mul_eq_zero_of_right _ ?_
  rw [Finset.sum_comm]
  refine Finset.sum_eq_zero fun i hi => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_eq_zero fun j hj => ?_
  rw [← Finset.mul_sum]
  refine mul_eq_zero_of_right _ ?_
  rw [Finset.mem_range] at hi hj
  -- `ζ^{i + (P-1)j + m} = ζ^{i + m - j}` with `0 < i + m - j < P`
  have hred : ζ ^ (i + (P - 1) * j + m) = ζ ^ (i + m - j) := by
    have : i + (P - 1) * j + m = (i + m - j) + P * j := by
      rcases Nat.exists_eq_succ_of_ne_zero hP.ne' with ⟨k, rfl⟩
      simp only [Nat.succ_sub_one]
      have : j ≤ i + m := by omega
      rw [Nat.succ_mul]
      omega
    rw [this, pow_add, pow_mul, hζP, one_pow, mul_one]
  rw [hred]
  refine sum_pow_eq_zero_of_root ?_ (cexp_two_pi_I_div_pow_ne_one hP (by omega) (by omega))
  rw [← pow_mul, mul_comm, pow_mul, hζP, one_pow]

/-! ### The modes of the cosine profile -/

/-- **Mode bound.** For `1 ≤ m ≤ P/2`, `ℓ = L/P` and `e ℓ δ ≤ 1`,
`|D(m)| ≤ 2P (e ℓ δ)^m e^{mℓδ}`. Only the Taylor remainder of `cosh` of order `m` survives the
vanishing of the low modes. -/
theorem norm_depthSymbol_cosProfile_le {L δ : ℝ} (hL : 0 ≤ L) (hδ : 0 ≤ δ) {P : ℕ} (hP : 0 < P)
    {m : ℕ} (hm1 : 1 ≤ m) (hmP : 2 * m ≤ P) (hq : Real.exp 1 * (L / P) * δ ≤ 1) :
    ‖depthSymbol L (cosProfile δ P) m‖ ≤
      2 * P * ((Real.exp 1 * (L / P) * δ) ^ m * Real.exp (m * (L / P) * δ)) := by
  have hPr : (0 : ℝ) < P := by exact_mod_cast hP
  set v : ℝ := m * (L / P) with hv
  have hv0 : 0 ≤ v := by positivity
  set N : ℕ := (m + 1) / 2 with hN
  have hN1 : m ≤ 2 * N := by omega
  have hN2 : 2 * (N - 1) < m := by omega
  -- the Taylor polynomial part has no mode `m`
  have hpoly : ∑ r : Fin P, ((2 * ∑ n ∈ Finset.range N,
      (cosProfile δ P r * v) ^ (2 * n) / ((2 * n)! : ℝ) : ℝ) : ℂ) *
        cexp (2 * π * I * r * m / P) = 0 := by
    have : ∀ r : Fin P, ((2 * ∑ n ∈ Finset.range N,
        (cosProfile δ P r * v) ^ (2 * n) / ((2 * n)! : ℝ) : ℝ) : ℂ) *
          cexp (2 * π * I * r * m / P) = ∑ n ∈ Finset.range N,
            ((2 * v ^ (2 * n) / ((2 * n)! : ℝ) : ℝ) : ℂ) *
              (((cosProfile δ P r : ℝ) : ℂ) ^ (2 * n) * cexp (2 * π * I * r * m / P)) := by
      intro r
      push_cast
      rw [Finset.mul_sum, Finset.sum_mul]
      refine Finset.sum_congr rfl fun n _ => ?_
      rw [mul_pow]
      ring
    simp_rw [this]
    rw [Finset.sum_comm]
    refine Finset.sum_eq_zero fun n hn => ?_
    rw [← Finset.mul_sum, sum_cosProfile_pow_mul_root_eq_zero δ hP (by
      rw [Finset.mem_range] at hn; omega) hmP, mul_zero]
  -- what remains is the Taylor remainder
  have hsplit : depthSymbol L (cosProfile δ P) m = ∑ r : Fin P,
      ((2 * (Real.cosh (cosProfile δ P r * v) - ∑ n ∈ Finset.range N,
        (cosProfile δ P r * v) ^ (2 * n) / ((2 * n)! : ℝ)) : ℝ) : ℂ) *
          cexp (2 * π * I * r * m / P) := by
    rw [depthSymbol]
    simp only [Int.cast_natCast]
    rw [← sub_zero (∑ r : Fin P, _), ← hpoly, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [← sub_mul, ← Complex.ofReal_sub]
    congr 2
    simp only [hv]
    ring
  rw [hsplit]
  have hrem : ∀ r : Fin P, 2 * (Real.cosh (cosProfile δ P r * v) - ∑ n ∈ Finset.range N,
      (cosProfile δ P r * v) ^ (2 * n) / ((2 * n)! : ℝ)) ≤
      2 * ((v * δ) ^ (2 * N) * Real.cosh (v * δ) / ((2 * N)! : ℝ)) := by
    intro r
    have hy0 : 0 ≤ cosProfile δ P r * v := mul_nonneg (cosProfile_nonneg hδ P r) hv0
    have hyle : cosProfile δ P r * v ≤ v * δ := by
      rw [mul_comm]; exact mul_le_mul_of_nonneg_left (cosProfile_le hδ P r) hv0
    have h := cosh_sub_taylor_le hy0 N
    have hmono : (cosProfile δ P r * v) ^ (2 * N) * Real.cosh (cosProfile δ P r * v) ≤
        (v * δ) ^ (2 * N) * Real.cosh (v * δ) := by
      refine mul_le_mul (pow_le_pow_left₀ hy0 hyle _) ?_ (Real.cosh_pos _).le (by positivity)
      rw [Real.cosh_le_cosh, abs_of_nonneg hy0, abs_of_nonneg (by positivity)]; exact hyle
    have : (cosProfile δ P r * v) ^ (2 * N) * Real.cosh (cosProfile δ P r * v) /
        ((2 * N)! : ℝ) ≤ (v * δ) ^ (2 * N) * Real.cosh (v * δ) / ((2 * N)! : ℝ) := by gcongr
    linarith
  have hremnn : ∀ r : Fin P, 0 ≤ 2 * (Real.cosh (cosProfile δ P r * v) - ∑ n ∈ Finset.range N,
      (cosProfile δ P r * v) ^ (2 * n) / ((2 * n)! : ℝ)) := by
    intro r
    have hy0 : 0 ≤ cosProfile δ P r * v := mul_nonneg (cosProfile_nonneg hδ P r) hv0
    have hs := Real.hasSum_cosh (cosProfile δ P r * v)
    have := sum_le_hasSum (Finset.range N) (fun n _ => by positivity) hs
    linarith
  -- the factorial estimate `(vδ)^{2N}/(2N)! ≤ (eℓδ)^m`
  have hfac : (v * δ) ^ (2 * N) / ((2 * N)! : ℝ) ≤ (Real.exp 1 * (L / P) * δ) ^ m := by
    have hm2N : (m : ℝ) ≤ 2 * N := by exact_mod_cast hN1
    have h1 : (v * δ) ^ (2 * N) ≤ ((2 * N : ℕ) * (L / P) * δ) ^ (2 * N) := by
      gcongr
      rw [hv]; push_cast; gcongr
    have h2 : ((2 * N : ℕ) * (L / P) * δ) ^ (2 * N) / ((2 * N)! : ℝ) ≤
        (Real.exp 1 * (L / P) * δ) ^ (2 * N) := by
      have hj := Real.pow_div_factorial_le_exp ((2 * N : ℕ) : ℝ) (by positivity) (2 * N)
      rw [show ((2 * N : ℕ) * (L / P) * δ) ^ (2 * N) =
        ((2 * N : ℕ) : ℝ) ^ (2 * N) * ((L / P) * δ) ^ (2 * N) by ring,
        show (Real.exp 1 * (L / P) * δ) ^ (2 * N) = Real.exp 1 ^ (2 * N) * ((L / P) * δ) ^ (2 * N)
          by ring, ← Real.exp_nat_mul, mul_one, mul_div_right_comm]
      gcongr
    have h3 : (Real.exp 1 * (L / P) * δ) ^ (2 * N) ≤ (Real.exp 1 * (L / P) * δ) ^ m :=
      pow_le_pow_of_le_one (by positivity) hq hN1
    calc (v * δ) ^ (2 * N) / ((2 * N)! : ℝ)
        ≤ ((2 * N : ℕ) * (L / P) * δ) ^ (2 * N) / ((2 * N)! : ℝ) := by gcongr
      _ ≤ _ := h2.trans h3
  have hcosh : Real.cosh (v * δ) ≤ Real.exp (m * (L / P) * δ) := by
    rw [Real.cosh_eq, hv]
    have := Real.exp_le_exp.mpr (show -(m * (L / P) * δ) ≤ m * (L / P) * δ by
      have : 0 ≤ (m : ℝ) * (L / P) * δ := by positivity
      linarith)
    linarith
  calc ‖∑ r : Fin P, ((2 * (Real.cosh (cosProfile δ P r * v) - ∑ n ∈ Finset.range N,
        (cosProfile δ P r * v) ^ (2 * n) / ((2 * n)! : ℝ)) : ℝ) : ℂ) *
          cexp (2 * π * I * r * m / P)‖
      ≤ ∑ r : Fin P, 2 * ((v * δ) ^ (2 * N) * Real.cosh (v * δ) / ((2 * N)! : ℝ)) := by
        refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun r _ => ?_)
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hremnn r),
          show 2 * π * I * ((r : ℕ) : ℂ) * (m : ℂ) / (P : ℂ) =
            ((2 * π * r * m / P : ℝ) : ℂ) * I by push_cast; ring,
          Complex.norm_exp_ofReal_mul_I, mul_one]
        exact hrem r
    _ = 2 * P * ((v * δ) ^ (2 * N) / ((2 * N)! : ℝ) * Real.cosh (v * δ)) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; ring
    _ ≤ 2 * P * ((Real.exp 1 * (L / P) * δ) ^ m * Real.exp (m * (L / P) * δ)) := by
        gcongr

/-! ### Hiding up to half the Nyquist aperture -/

/-- **Band-limited modulations hide.** If `q = e (L/P) δ e^{(L/P)δ} ≤ 1/3` — the period `P` exceeds
about `8δL` lattice steps — the cosine depth modulation is Weil-nonnegative at every aperture
`a ≤ L/4`, half the Nyquist ceiling. -/
theorem cosProfile_weil_nonneg {L δ : ℝ} (hL : 0 < L) {P : ℕ} (hP : 0 < P) (hδ : 0 ≤ δ)
    (hδ' : δ ≤ 1 / 2)
    (hq : Real.exp 1 * (L / P) * δ * Real.exp ((L / P) * δ) ≤ 1 / 3) {a : ℝ} (ha : 0 < a)
    (haL : 4 * a ≤ L) {f : ℝ → ℂ} (hf : ContDiff ℝ 2 f) (hfs : tsupport f ⊆ Icc (-a) a) :
    0 ≤ ((profileConfig hL hP (cosProfile δ P) (cosProfile_nonneg hδ P)
      (fun r => (cosProfile_le hδ P r).trans hδ')).W f f).re := by
  have hPr : (0 : ℝ) < P := by exact_mod_cast hP
  set q : ℝ := Real.exp 1 * (L / P) * δ * Real.exp ((L / P) * δ) with hqdef
  have hq0 : 0 ≤ q := by positivity
  have he1 : Real.exp 1 * (L / P) * δ ≤ 1 := by
    have : 1 ≤ Real.exp ((L / P) * δ) := Real.one_le_exp (by positivity)
    have h0 : 0 ≤ Real.exp 1 * (L / P) * δ := by positivity
    nlinarith
  set n : ℕ := ⌈2 * a * P / L⌉₊ with hn
  have hmode : ∀ j : ℕ, 1 ≤ j → j < n → ‖depthSymbol L (cosProfile δ P) j‖ ≤ 2 * P * q ^ j := by
    intro j hj1 hjn
    have hj : (j : ℝ) < 2 * a * P / L := Nat.lt_ceil.mp hjn
    have h2j : 2 * j ≤ P := by
      have : (2 * j : ℝ) < P := by
        have : 2 * a * P / L ≤ P / 2 := by rw [div_le_iff₀ hL]; nlinarith
        linarith
      have : 2 * j < P := by exact_mod_cast this
      omega
    refine (norm_depthSymbol_cosProfile_le hL.le hδ hP hj1 h2j he1).trans (le_of_eq ?_)
    rw [show (j : ℝ) * (L / P) * δ = j * ((L / P) * δ) by ring, Real.exp_nat_mul, hqdef]
    ring
  have hmodes : ∑ m ∈ (Finset.Ioo (-(n : ℤ)) n).erase 0, ‖depthSymbol L (cosProfile δ P) m‖ ≤
      2 * ∑ j ∈ Finset.Ico 1 n, 2 * P * q ^ j := by
    refine sum_Ioo_erase_zero_le fun m hm => ?_
    simp only [Finset.mem_erase, Finset.mem_Ioo] at hm
    obtain ⟨j, hj⟩ : ∃ j : ℕ, j = m.natAbs := ⟨_, rfl⟩
    have hj1 : 1 ≤ j := by omega
    have hjn : j < n := by omega
    rw [← hj]
    rcases le_or_gt 0 m with hpos | hneg
    · rw [show m = (j : ℤ) by omega]
      exact hmode _ hj1 hjn
    · rw [show m = -(j : ℤ) by omega, depthSymbol_neg, Complex.norm_conj]
      exact hmode _ hj1 hjn
  refine profileConfig_weil_nonneg_of_modes hL hP _ _ _ ha (hmodes.trans ?_) hf hfs
  have hgeom : ∑ j ∈ Finset.Ico 1 n, q ^ j ≤ q ^ 1 / (1 - q) :=
    geom_sum_Ico_le_of_lt_one hq0 (by linarith)
  rw [← Finset.mul_sum]
  calc 2 * (2 * (P : ℝ) * ∑ j ∈ Finset.Ico 1 n, q ^ j) ≤ 2 * (2 * P * (q ^ 1 / (1 - q))) := by
        gcongr
    _ ≤ 2 * (2 * P * (1 / 2)) := by
        have h : q ^ 1 / (1 - q) ≤ 1 / 2 := by
          rw [pow_one, div_le_iff₀ (by linarith)]; linarith
        have := mul_le_mul_of_nonneg_left h (by positivity : (0 : ℝ) ≤ 2 * P)
        linarith
    _ = 2 * P := by ring

end GaloisForLFunctions.SquareRootThreshold
