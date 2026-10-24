import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.TheDegreeFiltrationOfACurveIsItsWindowFiltration
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.TheTowerDefectCountsTheFrobeniusEigenvalues

/-!
# The genus is the aperture of the radical

Over `ℚ` no nonzero compactly supported test has a transform vanishing at every zero
(`InfiniteGenusLaw`): the scaling surface of `ℤ` has no radical among compact tests. Over `𝔽_q`
the radical exists, and its aperture measures the genus. Let `d` be the number of distinct
normalized Frobenius eigenvalues of a curve datum (`d ≤ 2g`), `L = log q`, and
`P(z) = ∏_b (z − b)` its **Frobenius polynomial** (`frobPoly`).

* **Cayley–Hamilton on the scaling surface** (`paperFT_frobPolyTest`, `W_frobPolyTest_left`,
  `W_frobPolyTest_right`). The tower `T_q g = g(· − L)` acts on the zero side by the Frobenius
  eigenvalue, so `P(T_q) g = Σ_k c_k g(· − kL)` has transform `P(e^{izL}) ĝ(z)`, which vanishes at
  every zero: `P(T_q) g` lies in the radical of Weil's form, for every test `g`.
* **No radical below `dL/2`** (`eq_zero_of_paperFT_curve_zeros`). If a test supported in `[−a, a]`,
  `a ≤ dL/2`, has transform vanishing at every zero, Poisson summation along the period of each
  eigenvalue `b` (`hasSum_paperFT_zetaZero`) gives `Σ_m f(s + mL) b^m = 0` for every `s`; the
  samples `f(s + mL)` occupy at most `⌈2a/L⌉ ≤ d` consecutive places, so the polynomial they form
  has `d` distinct roots and fewer than `d` coefficients, and vanishes (Vandermonde).
* **The aperture law** (`exists_radical_test_iff`). A nonzero `C²` test supported in `[−a, a]` with
  transform vanishing at every zero exists iff `a > d log q / 2`.

So the aperture at which the radical opens is `d/2` periods of the scaling flow: finite genus is a
finite radical aperture, and `ℚ`, of infinite genus, has radical aperture `∞`.
-/

open Complex MeasureTheory Finset Polynomial
open scoped Real ComplexConjugate
open Zeta23 GaloisForLFunctions.HTGeometry

noncomputable section

namespace GaloisForLFunctions.ArithmeticCastelnuovoSeveri

/-- A continuous function with `tsupport ⊆ [−a, a]` vanishes off the open interval. -/
theorem mem_Ioo_of_ne_zero {f : ℝ → ℂ} (hf : Continuous f) {a : ℝ}
    (hfs : tsupport f ⊆ Set.Icc (-a) a) {u : ℝ} (hu : f u ≠ 0) : -a < u ∧ u < a := by
  have hmem : ∀ v, f v ≠ 0 → v ∈ Set.Icc (-a) a := fun v hv => hfs (subset_tsupport _ hv)
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp (isOpen_ne_fun hf continuous_const) u hu
  have h1 := hmem (u + ε / 2) (hball (by
    rw [Metric.mem_ball, Real.dist_eq, show u + ε / 2 - u = ε / 2 by ring,
      abs_of_pos (half_pos hε)]
    linarith))
  have h2 := hmem (u - ε / 2) (hball (by
    rw [Metric.mem_ball, Real.dist_eq, show u - ε / 2 - u = -(ε / 2) by ring, abs_neg,
      abs_of_pos (half_pos hε)]
    linarith))
  exact ⟨by linarith [h2.1], by linarith [h1.2]⟩

/-- **Window of a sampled test.** If `tsupport f ⊆ [−a, a]`, the nonzero samples `f(s + jL)` have
`⌈(−a − s)/L⌉ ≤ j < ⌈(−a − s)/L⌉ + ⌈2a/L⌉`. -/
theorem window_of_support {f : ℝ → ℂ} (hf : Continuous f) {a L : ℝ} (hL : 0 < L)
    (hfs : tsupport f ⊆ Set.Icc (-a) a) (s : ℝ) {j : ℤ} (hj : f (s + j * L) ≠ 0) :
    ⌈(-a - s) / L⌉ ≤ j ∧ j < ⌈(-a - s) / L⌉ + ⌈2 * a / L⌉₊ := by
  obtain ⟨h1, h2⟩ := mem_Ioo_of_ne_zero hf hfs hj
  have hlow : (-a - s) / L < j := by rw [div_lt_iff₀ hL]; linarith
  refine ⟨Int.ceil_le.mpr hlow.le, ?_⟩
  have hup : (j : ℝ) < (a - s) / L := by rw [lt_div_iff₀ hL]; linarith
  have hc1 : (-a - s) / L ≤ ⌈(-a - s) / L⌉ := Int.le_ceil _
  have hc2 : 2 * a / L ≤ ⌈2 * a / L⌉₊ := Nat.le_ceil _
  have hsplit : (a - s) / L = (-a - s) / L + 2 * a / L := by ring
  have : (j : ℝ) < (⌈(-a - s) / L⌉ : ℤ) + ((⌈2 * a / L⌉₊ : ℕ) : ℝ) := by linarith
  exact_mod_cast this

/-- **A short sample sequence vanishing at `n` distinct nonzero points vanishes.** If the nonzero
terms of `F : ℤ → ℂ` lie in `[j₀, j₀ + m)` with `m ≤ #B`, `0 ∉ B`, and `Σ_j F(j) b^j = 0` for every
`b ∈ B`, then `F = 0`. -/
theorem eq_zero_of_window_powerSums {F : ℤ → ℂ} {j₀ : ℤ} {m : ℕ}
    (hwin : ∀ j, F j ≠ 0 → j₀ ≤ j ∧ j < j₀ + m) {B : Finset ℂ} (hB0 : ∀ b ∈ B, b ≠ 0)
    (hmB : m ≤ B.card) (hsum : ∀ b ∈ B, ∑' j : ℤ, F j * b ^ j = 0) (j : ℤ) : F j = 0 := by
  classical
  set Q : Polynomial ℂ := ∑ t : Fin m, C (F (j₀ + ((t : ℕ) : ℤ))) * X ^ (t : ℕ) with hQ
  have hdeg : Q.degree < m := degree_sum_fin_lt fun t => F (j₀ + ((t : ℕ) : ℤ))
  have hcoeff : ∀ t : Fin m, Q.coeff t = F (j₀ + ((t : ℕ) : ℤ)) := fun t => by
    rw [hQ, finsetSum_coeff]
    simp only [coeff_C_mul_X_pow]
    rw [Finset.sum_eq_single t (fun t' _ ht' => if_neg (fun h => ht' (Fin.ext h.symm)))
      (by simp)]
    simp
  -- `Q` vanishes on `B`
  have heval : ∀ b ∈ B, Q.eval b = 0 := by
    intro b hb
    have hb0 := hB0 b hb
    have hfin : ∑' j : ℤ, F j * b ^ j =
        ∑ j ∈ (Finset.univ : Finset (Fin m)).image (fun t : Fin m => j₀ + ((t : ℕ) : ℤ)),
          F j * b ^ j :=
      tsum_eq_sum fun j hj => by
        by_contra hne
        have hF : F j ≠ 0 := fun h => hne (by rw [h, zero_mul])
        obtain ⟨h1, h2⟩ := hwin j hF
        exact hj (Finset.mem_image.mpr ⟨⟨(j - j₀).toNat, by omega⟩, Finset.mem_univ _, by
          simp only; omega⟩)
    have himg : ∑ j ∈ (Finset.univ : Finset (Fin m)).image (fun t : Fin m => j₀ + ((t : ℕ) : ℤ)),
        F j * b ^ j =
        ∑ t : Fin m, F (j₀ + ((t : ℕ) : ℤ)) * b ^ (j₀ + ((t : ℕ) : ℤ)) :=
      Finset.sum_image fun t _ t' _ h => Fin.ext (by simpa using h)
    have h0 := hsum b hb
    rw [hfin, himg] at h0
    have hsplit : ∑ t : Fin m, F (j₀ + ((t : ℕ) : ℤ)) * b ^ (j₀ + ((t : ℕ) : ℤ)) =
        b ^ j₀ * Q.eval b := by
      rw [hQ, eval_finsetSum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun t _ => ?_
      rw [eval_mul, eval_C, eval_pow, eval_X, zpow_add₀ hb0, zpow_natCast]
      ring
    rw [hsplit] at h0
    exact (mul_eq_zero.mp h0).resolve_left (zpow_ne_zero _ hb0)
  have hQ0 : Q = 0 := by
    by_contra hne
    have hnat : Q.natDegree < m := (natDegree_lt_iff_degree_lt hne).mpr hdeg
    exact hne (eq_zero_of_natDegree_lt_card_of_eval_eq_zero' Q B heval (hnat.trans_le hmB))
  by_contra hFj
  obtain ⟨h1, h2⟩ := hwin j hFj
  have := hcoeff ⟨(j - j₀).toNat, by omega⟩
  rw [hQ0, coeff_zero] at this
  apply hFj
  rw [show j = j₀ + (((⟨(j - j₀).toNat, by omega⟩ : Fin m) : ℕ) : ℤ) by simp only; omega]
  exact this.symm

namespace CurveDatum

variable {ι : Type*} [Fintype ι] (D : CurveDatum ι) (hD : ∀ i, ‖D.β i‖ ≤ D.sqrtq)

/-! ### The Frobenius polynomial -/

/-- The **Frobenius polynomial** `P(z) = ∏_b (z − b)` over the distinct normalized eigenvalues. -/
def frobPoly : Polynomial ℂ := ∏ b ∈ D.spectrum, (X - C b)

theorem frobPoly_monic : D.frobPoly.Monic :=
  monic_prod_of_monic _ _ fun b _ => monic_X_sub_C b

theorem natDegree_frobPoly : D.frobPoly.natDegree = D.spectrum.card := by
  rw [frobPoly, natDegree_prod_of_monic _ _ fun b _ => monic_X_sub_C b]
  simp

theorem eval_frobPoly_eq_zero {b : ℂ} (hb : b ∈ D.spectrum) : D.frobPoly.eval b = 0 := by
  rw [frobPoly, eval_prod]
  exact Finset.prod_eq_zero hb (by simp)

theorem β_mem_spectrum (i : ι) : D.β i ∈ D.spectrum :=
  Finset.mem_image_of_mem _ (Finset.mem_univ i)

theorem ne_zero_of_mem_spectrum {b : ℂ} (hb : b ∈ D.spectrum) : b ≠ 0 := by
  obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hb
  exact D.β_ne_zero i

/-- The zeros attached to `β_i` have Frobenius eigenvalue `β_i` at the scale `log q`. -/
theorem frobEig_zetaZero (i : ι) (k : ℤ) : frobEig (Real.log D.q) (D.zetaZero i k) = D.β i := by
  rw [frobEig, D.log_q_mul_zetaZero, Complex.exp_add, Complex.exp_log (D.β_ne_zero i),
    Complex.exp_int_mul_two_pi_mul_I, mul_one]

theorem cexp_I_gammaOf_zetaZero (i : ι) (k : ℤ) :
    cexp (I * gammaOf (D.zetaZero i k) * Real.log D.q) = D.β i := by
  rw [I_mul_gammaOf, mul_comm, ← frobEig, D.frobEig_zetaZero]

/-! ### Cayley–Hamilton on the scaling surface -/

/-- `P(T_q) g = Σ_k c_k g(· − k log q)`: the Frobenius polynomial acting on the `q`-tower. -/
def frobPolyTest (g : ℝ → ℂ) : ℝ → ℂ :=
  ∑ k ∈ range (D.frobPoly.natDegree + 1), D.frobPoly.coeff k • translate (k * Real.log D.q) g

theorem frobPolyTest_apply (g : ℝ → ℂ) (t : ℝ) :
    D.frobPolyTest g t = ∑ k ∈ range (D.frobPoly.natDegree + 1),
      D.frobPoly.coeff k * g (t - k * Real.log D.q) := by
  simp [frobPolyTest, Finset.sum_apply, translate]

theorem frobPolyTest_contDiff {g : ℝ → ℂ} (hg : ContDiff ℝ 2 g) :
    ContDiff ℝ 2 (D.frobPolyTest g) := by
  rw [show D.frobPolyTest g = fun t => ∑ k ∈ range (D.frobPoly.natDegree + 1),
    D.frobPoly.coeff k * g (t - k * Real.log D.q) from funext (D.frobPolyTest_apply g)]
  exact ContDiff.sum fun k _ => contDiff_const.mul (hg.comp (contDiff_id.sub contDiff_const))

theorem frobPolyTest_hasCompactSupport {g : ℝ → ℂ} (hgc : HasCompactSupport g) :
    HasCompactSupport (D.frobPolyTest g) := by
  unfold frobPolyTest
  induction (range (D.frobPoly.natDegree + 1)) using Finset.induction_on with
  | empty => simpa using (HasCompactSupport.zero : HasCompactSupport (0 : ℝ → ℂ))
  | insert k s hk ih =>
    rw [Finset.sum_insert hk]
    exact (translate_hasCompactSupport hgc _).smul_left.add ih

/-- **The tower acts on the transform by the Frobenius polynomial**:
`(P(T_q) g)^(z) = P(e^{iz log q}) ĝ(z)`. -/
theorem paperFT_frobPolyTest {g : ℝ → ℂ} (hg : Continuous g) (hgc : HasCompactSupport g)
    (z : ℂ) :
    paperFT (D.frobPolyTest g) z = D.frobPoly.eval (cexp (I * z * Real.log D.q)) * paperFT g z := by
  have h := paperFT_finset_sum (range (D.frobPoly.natDegree + 1))
    (fun k => D.frobPoly.coeff k • translate (k * Real.log D.q) g)
    (fun k _ => (hg.comp (continuous_sub_right _)).const_smul _)
    (fun k _ => (translate_hasCompactSupport hgc _).smul_left) z
  have hfun : D.frobPolyTest g = fun u => ∑ k ∈ range (D.frobPoly.natDegree + 1),
      (D.frobPoly.coeff k • translate (k * Real.log D.q) g) u := by
    funext u
    simp [frobPolyTest, Finset.sum_apply]
  rw [hfun, h, eval_eq_sum_range, Finset.sum_mul]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [paperFT_smul, paperFT_translate, ← Complex.exp_nat_mul,
    show I * z * (((k : ℝ) * Real.log D.q : ℝ) : ℂ) = (k : ℂ) * (I * z * (Real.log D.q : ℂ)) by
      push_cast; ring]
  ring

/-- **Cayley–Hamilton on the scaling surface**: `P(T_q) g` has transform zero at every zero. -/
theorem paperFT_frobPolyTest_zero {g : ℝ → ℂ} (hg : Continuous g) (hgc : HasCompactSupport g)
    {ρ : ℂ} (hρ : ρ ∈ (D.curveConfig hD).carrier) : paperFT (D.frobPolyTest g) (gammaOf ρ) = 0 := by
  obtain ⟨⟨i, k⟩, rfl⟩ := hρ
  rw [D.paperFT_frobPolyTest hg hgc, D.cexp_I_gammaOf_zetaZero,
    D.eval_frobPoly_eq_zero (D.β_mem_spectrum i), zero_mul]

/-- `P(T_q) g` lies in the left radical of Weil's form. -/
theorem W_frobPolyTest_left {g : ℝ → ℂ} (hg : Continuous g) (hgc : HasCompactSupport g)
    (h : ℝ → ℂ) : (D.curveConfig hD).W (D.frobPolyTest g) h = 0 := by
  refine (tsum_congr fun ρ => ?_).trans tsum_zero
  rw [ZeroConfig.Wsummand, D.paperFT_frobPolyTest_zero hD hg hgc ρ.2, mul_zero, zero_mul]

/-- `P(T_q) g` lies in the right radical of Weil's form. -/
theorem W_frobPolyTest_right {g : ℝ → ℂ} (hg : Continuous g) (hgc : HasCompactSupport g)
    (h : ℝ → ℂ) : (D.curveConfig hD).W h (D.frobPolyTest g) = 0 := by
  refine (tsum_congr fun ρ => ?_).trans tsum_zero
  rw [ZeroConfig.Wsummand, ← gammaOf_reflect,
    D.paperFT_frobPolyTest_zero hD hg hgc ((D.curveConfig hD).reflect_mem _ ρ.2), map_zero,
    mul_zero]

/-! ### No radical below `d log q / 2` -/

/-- **Poisson along one eigenvalue.** A test whose transform vanishes at every zero satisfies
`Σ_m f(s + m log q) β_i^m = 0` for every `s`. -/
theorem tsum_sample_mul_pow_eq_zero {f : ℝ → ℂ} (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f)
    (hvan : ∀ ρ ∈ (D.curveConfig hD).carrier, paperFT f (gammaOf ρ) = 0) (i : ι) (s : ℝ) :
    ∑' m : ℤ, f (s + m * Real.log D.q) * D.β i ^ m = 0 := by
  have hL := D.log_q_pos
  have hKc : HasCompactSupport (translate (-s) f) := translate_hasCompactSupport hfc _
  obtain ⟨A, -, hA⟩ := GaloisForLFunctions.SquareRootThreshold.exists_radius_of_hasCompactSupport hKc
  have hKs : ∀ u, translate (-s) f u ≠ 0 → |u| ≤ A := fun u hu => not_lt.mp fun h => hu (hA u h)
  have hP := D.hasSum_paperFT_zetaZero i (translate_contDiff hf (-s)) hKs
  have hzero : (fun k : ℤ => paperFT (translate (-s) f) (gammaOf (D.zetaZero i k))) =
      fun _ => 0 := funext fun k => by
    rw [paperFT_translate, hvan _ ⟨(i, k), rfl⟩, mul_zero]
  rw [hzero] at hP
  have h0 := hP.unique hasSum_zero
  have hval : ∀ m : ℤ, translate (-s) f (m * Real.log D.q) = f (s + m * Real.log D.q) :=
    fun m => by
      simp only [translate]
      congr 1
      ring
  simp only [hval] at h0
  exact (mul_eq_zero.mp h0).resolve_left (by exact_mod_cast hL.ne')

/-- **No radical below `d log q / 2`.** A `C²` test supported in `[−a, a]`, with
`2a ≤ d log q`, whose transform vanishes at every zero of the curve is zero. -/
theorem eq_zero_of_paperFT_curve_zeros {f : ℝ → ℂ} (hf : ContDiff ℝ 2 f) {a : ℝ}
    (hfs : tsupport f ⊆ Set.Icc (-a) a) (ha : 2 * a ≤ D.spectrum.card * Real.log D.q)
    (hvan : ∀ ρ ∈ (D.curveConfig hD).carrier, paperFT f (gammaOf ρ) = 0) (u : ℝ) : f u = 0 := by
  have hL := D.log_q_pos
  have hfc : HasCompactSupport f := RHTower.hasCompactSupport_of_tsupport_subset_Icc hfs
  have hn : ⌈2 * a / Real.log D.q⌉₊ ≤ D.spectrum.card :=
    Nat.ceil_le.mpr (by rw [div_le_iff₀ hL]; exact ha)
  have key := eq_zero_of_window_powerSums (F := fun j : ℤ => f (u + j * Real.log D.q))
    (j₀ := ⌈(-a - u) / Real.log D.q⌉) (m := ⌈2 * a / Real.log D.q⌉₊)
    (fun j hj => window_of_support hf.continuous hL hfs u hj) (B := D.spectrum)
    (fun b hb => D.ne_zero_of_mem_spectrum hb) hn (fun b hb => by
      obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hb
      exact D.tsum_sample_mul_pow_eq_zero hD hf hfc hvan i u) 0
  simpa using key

/-! ### The aperture law -/

/-- **The radical opens at aperture `d log q / 2`.** On the scaling surface of a curve datum in the
strip with `d` distinct eigenvalues, a nonzero `C²` test supported in `[−a, a]` whose transform
vanishes at every zero exists iff `a > d log q / 2`; every such test is in the radical of Weil's
form (`W_frobPolyTest_left`, `W_frobPolyTest_right`). -/
theorem exists_radical_test_iff (a : ℝ) :
    (∃ f : ℝ → ℂ, ContDiff ℝ 2 f ∧ tsupport f ⊆ Set.Icc (-a) a ∧ f ≠ 0 ∧
        ∀ ρ ∈ (D.curveConfig hD).carrier, paperFT f (gammaOf ρ) = 0) ↔
      D.spectrum.card * Real.log D.q / 2 < a := by
  have hL := D.log_q_pos
  set d := D.spectrum.card with hd
  constructor
  · rintro ⟨f, hf, hfs, hf0, hvan⟩
    by_contra hle
    push Not at hle
    exact hf0 (funext fun u => D.eq_zero_of_paperFT_curve_zeros hD hf hfs (by linarith) hvan u)
  · intro ha
    -- a bump of width `w ≤ 2(a − dL/2)`, `w < L`, centred at `−dL/2`
    obtain ⟨w, hw0, hwa, hwL⟩ : ∃ w : ℝ, 0 < w ∧ w ≤ 2 * (a - d * Real.log D.q / 2) ∧
        w < Real.log D.q :=
      ⟨min (2 * (a - d * Real.log D.q / 2)) (Real.log D.q / 2),
        lt_min (by linarith) (by linarith), min_le_left _ _,
        lt_of_le_of_lt (min_le_right _ _) (by linarith)⟩
    have hw2 : 0 < w / 2 := half_pos hw0
    set g₀ : ℝ → ℂ := bumpTest (w / 2) hw2 0 with hg₀
    have hg₀1 : g₀ 0 = 1 := by
      simp only [hg₀, bumpTest, sub_zero]
      rw [(smallBump (w / 2) hw2).one_of_mem_closedBall
        (Metric.mem_closedBall_self (smallBump (w / 2) hw2).rIn_pos.le), Complex.ofReal_one]
    have hg₀z : ∀ u, w / 2 ≤ |u| → g₀ u = 0 := by
      intro u hu
      simp only [hg₀, bumpTest, sub_zero]
      have hr : (smallBump (w / 2) hw2).rOut = w / 2 := rfl
      have hns : u ∉ Function.support (smallBump (w / 2) hw2) := by
        rw [ContDiffBump.support_eq, Metric.mem_ball, Real.dist_eq, sub_zero, hr]
        exact not_lt.mpr hu
      rw [Function.notMem_support.mp hns, Complex.ofReal_zero]
    set g : ℝ → ℂ := translate (-(d * Real.log D.q / 2)) g₀ with hg
    have hgC : ContDiff ℝ 2 g := translate_contDiff (bumpTest_contDiff hw2 0) _
    have hgc : HasCompactSupport g := translate_hasCompactSupport (bumpTest_hasCompactSupport hw2 0) _
    refine ⟨D.frobPolyTest g, D.frobPolyTest_contDiff hgC, ?_, ?_,
      fun ρ hρ => D.paperFT_frobPolyTest_zero hD hgC.continuous hgc hρ⟩
    · -- support in `[−a, a]`
      refine closure_minimal (fun u hu => ?_) isClosed_Icc
      by_contra hout
      apply hu
      rw [D.frobPolyTest_apply]
      refine Finset.sum_eq_zero fun k hk => ?_
      have hk' : (k : ℝ) ≤ d := by
        have := Finset.mem_range.mp hk
        rw [D.natDegree_frobPoly] at this
        exact_mod_cast Nat.lt_succ_iff.mp this
      have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
      rw [hg, translate, hg₀z, mul_zero]
      rw [Set.mem_Icc, not_and_or, not_le, not_le] at hout
      have hkL : (k : ℝ) * Real.log D.q ≤ d * Real.log D.q := mul_le_mul_of_nonneg_right hk' hL.le
      have hkL0 : 0 ≤ (k : ℝ) * Real.log D.q := mul_nonneg hk0 hL.le
      rcases hout with h | h
      · rw [abs_of_neg (by linarith)]; linarith
      · rw [abs_of_pos (by linarith)]; linarith
    · -- nonzero at `dL/2`: only the leading term survives
      intro h0
      have hv := congrFun h0 (d * Real.log D.q / 2)
      rw [D.frobPolyTest_apply, Pi.zero_apply, Finset.sum_eq_single D.frobPoly.natDegree] at hv
      · rw [D.frobPoly_monic.coeff_natDegree, one_mul, hg, translate, D.natDegree_frobPoly, ← hd,
          show (d : ℝ) * Real.log D.q / 2 - d * Real.log D.q - -(d * Real.log D.q / 2) = 0 by ring,
          hg₀1] at hv
        exact one_ne_zero hv
      · intro k hk hkne
        have hk' : k < D.frobPoly.natDegree := lt_of_le_of_ne
          (Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)) hkne
        rw [D.natDegree_frobPoly, ← hd] at hk'
        have hk1 : (k : ℝ) + 1 ≤ d := by exact_mod_cast hk'
        rw [hg, translate, hg₀z, mul_zero]
        rw [show (d : ℝ) * Real.log D.q / 2 - k * Real.log D.q - -(d * Real.log D.q / 2) =
          (d - k) * Real.log D.q by ring, abs_of_pos (by nlinarith)]
        nlinarith
      · intro h
        exact absurd (Finset.mem_range.mpr (Nat.lt_succ_self _)) h

end CurveDatum

end GaloisForLFunctions.ArithmeticCastelnuovoSeveri
