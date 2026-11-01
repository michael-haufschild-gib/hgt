import GaloisForLFunctions.RenormalizedIntersectionTheory.GaussMayerCountableWordTraces
import GaloisForLFunctions.HTGeometry.FredholmDeterminantTracePowers

/-! The signed product of the actual Mayer determinants has only even-word
traces in its local logarithm. The first trace cancels exactly. -/

open Complex Filter Metric Topology
open GaloisForLFunctions.HTGeometry HilbertSchmidt
open GaloisForLFunctions.RenormalizedIntersectionTheory
open MayerFredholm MayerWords
set_option autoImplicit false
noncomputable section
namespace GaloisForLFunctions.RenormalizedIntersectionTheory.MayerOrbitDeterminant

private theorem kernel_power_trace {w : ℂ} (hw : 0 < w.re) (n : ℕ) :
    (∑' i, hsPow (kernel w hw) (n+1) (i,i)) =
      ContinuousLinearMap.opTrace (hilbertOperator w hw ^ (n+2)) := by
  have hc : _root_.RHTower.coordMatrix (lpBasis ℕ) (hilbertOperator w hw) = kernel w hw := by
    funext p
    rw [_root_.RHTower.coordMatrix_apply, lpBasis_apply, lp.inner_single_left]
    simp only [RCLike.inner_apply, map_one, mul_one, lpBasis_apply]
    exact congrFun (matrixOf_hilbertOperator hw) p
  have hT : (hilbertOperator w hw).IsHilbertSchmidt := by
    rw [← toOperator_kernel hw]
    exact isHilbertSchmidt_toOperator (kernel_isHS hw)
  rw [← hc, tsum_diag_hsPow_coordMatrix (lpBasis ℕ) hT n]

/-- Total mass of the summable branch majorant on the convergence half-plane. -/
def digitMass (w : ℂ) : ℝ := ∑' n : ℕ, MayerCutoff.powerBound w *
  ((n+1 : ℕ) : ℝ)^(-w.re)

private theorem hasSum_wordBound {w : ℂ} (hw : 1 < w.re) (k : ℕ) :
    HasSum (wordBound w k) (digitMass w ^ k) := by
  have hd : Summable (fun n : ℕ => MayerCutoff.powerBound w *
      ((n+1 : ℕ) : ℝ)^(-w.re)) :=
    ((summable_nat_add_iff (f := fun n : ℕ => (n : ℝ)^(-w.re)) 1).mpr
      (_root_.RHTower.Sieve.summable_nat_rpow_neg hw)).mul_left _
  induction k with
  | zero => simpa only [wordBound, Fin.prod_univ_zero, pow_zero, Fintype.sum_unique]
      using hasSum_fintype (wordBound w 0)
  | succ k ih =>
      have hp := summable_mul_of_summable_norm hd.norm ih.summable.norm
      have h := (splitWord k).hasSum_iff.mpr (hd.hasSum.mul ih hp)
      change HasSum (fun a : Word (k+1) => wordBound w (k+1) a) _
      simpa only [Function.comp_def, splitWord, Equiv.coe_fn_mk, wordBound,
        Fin.prod_univ_succ, Fin.tail, digitMass, pow_succ'] using h

private theorem digitMass_nonneg (w : ℂ) : 0 ≤ digitMass w :=
  tsum_nonneg fun _ => mul_nonneg (MayerCutoff.powerBound_pos w).le
    (Real.rpow_nonneg (Nat.cast_nonneg _) _)

/-- The Cauchy diagonal gives one trace bound uniform in word length. -/
theorem norm_wordTrace_le {w : ℂ} (hw : 0 < w.re) (k : ℕ) (a : Word (k+1)) :
    ‖wordTrace w k a‖ ≤ (32/7 : ℝ) * wordBound w (k+1) a := by
  let f : ℕ → ℂ := fun j => MayerTrace.traceCoefficient j
    (wordOperator w hw (k+1) a (MayerNuclear.monomial j))
  have hg : Summable (fun j : ℕ => coefficientRadius⁻¹^j * wordBound w (k+1) a) :=
    (summable_geometric_of_lt_one (by norm_num [coefficientRadius])
      (by norm_num [coefficientRadius])).mul_right _
  have hf : Summable (fun j => ‖f j‖) := hg.of_nonneg_of_le (fun _ => norm_nonneg _)
    (norm_word_diagonal_le hw k a)
  calc
    ‖wordTrace w k a‖ = ‖∑' j, f j‖ := congrArg norm (hasSum_word_diagonal hw k a).tsum_eq.symm
    _ ≤ ∑' j, ‖f j‖ := norm_tsum_le_tsum_norm hf
    _ ≤ ∑' j, coefficientRadius⁻¹^j * wordBound w (k+1) a :=
      hf.tsum_le_tsum (norm_word_diagonal_le hw k a) hg
    _ = _ := by
      rw [tsum_mul_right, tsum_geometric_of_lt_one (by norm_num [coefficientRadius])
        (by norm_num [coefficientRadius])]
      norm_num [coefficientRadius]

/-- Absolute convergence of every fixed-length trace fiber, with its digit mass bound. -/
theorem tsum_norm_wordTrace_le {w : ℂ} (hw : 1 < w.re) (k : ℕ) :
    (∑' a : Word (k+1), ‖wordTrace w k a‖) ≤ (32/7 : ℝ) * digitMass w^(k+1) := by
  have hb := (hasSum_wordBound hw (k+1)).summable.mul_left (32/7 : ℝ)
  have ht : Summable (fun a : Word (k+1) => ‖wordTrace w k a‖) :=
    hb.of_nonneg_of_le (fun _ => norm_nonneg _) (norm_wordTrace_le (zero_lt_one.trans hw) k)
  calc
    _ ≤ ∑' a : Word (k+1), (32/7 : ℝ)*wordBound w (k+1) a :=
      ht.tsum_le_tsum (norm_wordTrace_le (zero_lt_one.trans hw) k) hb
    _ = _ := by rw [tsum_mul_left, (hasSum_wordBound hw (k+1)).tsum_eq]

/-- A small spectral parameter makes the entire countable even-word logarithm
absolutely summable, before any primitive-orbit regrouping. -/
theorem summable_norm_evenWordSeries {w z : ℂ} (hw : 1 < w.re)
    (hz : ‖z‖ * digitMass w < 1) :
    Summable (fun p : (Σ n : ℕ, Word (2*n+2)) =>
      ‖z^(2*p.1+2) / ((p.1+1 : ℕ) : ℂ) * wordTrace w (2*p.1+1) p.2‖) := by
  let q := ‖z‖ * digitMass w
  have hq0 : 0 ≤ q := mul_nonneg (norm_nonneg z) (digitMass_nonneg w)
  have hq1 : q < 1 := hz
  have hgeom : Summable (fun n : ℕ => (32/7 : ℝ)*q^(2*n+2)) := by
    have hq2 : q^2 < 1 := GeomFredholm.sq_lt_one hq0 hq1
    have h := (summable_geometric_of_lt_one (sq_nonneg q) hq2).mul_left ((32/7 : ℝ)*q^2)
    exact h.congr fun n => by rw [pow_add, pow_mul]; ring
  have hf (n : ℕ) : Summable (fun a : Word (2*n+2) =>
      ‖z^(2*n+2) / ((n+1 : ℕ) : ℂ) * wordTrace w (2*n+1) a‖) := by
    simp only [norm_mul]
    exact (summable_wordTrace hw (2*n+1)).norm.mul_left _
  apply (summable_sigma_of_nonneg (fun _ => norm_nonneg _)).mpr
  refine ⟨hf, hgeom.of_nonneg_of_le (fun _ => tsum_nonneg fun _ => norm_nonneg _) ?_⟩
  intro n
  simp only [norm_mul, tsum_mul_left]
  have hden : (1 : ℝ) ≤ n+1 := by exact_mod_cast Nat.succ_le_succ (Nat.zero_le n)
  have hquot : ‖z^(2*n+2) / ((n+1 : ℕ) : ℂ)‖ ≤ ‖z‖^(2*n+2) := by
    rw [norm_div, norm_pow, Complex.norm_natCast]
    exact div_le_self (pow_nonneg (norm_nonneg z) _) (by exact_mod_cast hden)
  calc
    _ ≤ ‖z‖^(2*n+2) * ((32/7 : ℝ)*digitMass w^(2*n+2)) :=
      mul_le_mul hquot (tsum_norm_wordTrace_le hw (2*n+1))
        (tsum_nonneg fun _ => norm_nonneg _) (pow_nonneg (norm_nonneg z) _)
    _ = (32/7 : ℝ)*q^(2*n+2) := by dsimp [q]; rw [mul_pow]; ring

/-- The actual fixed-point trace series over all nonempty even Gauss words. -/
def evenWordExponent (w z : ℂ) : ℂ :=
  ∑' n : ℕ, z^(2*n+2) / ((n+1 : ℕ) : ℂ) *
    ∑' a : Word (2*n+2), wordTrace w (2*n+1) a

private theorem parity_exponent {K : ℕ × ℕ → ℂ} (hK : IsHS K)
    (z : ℂ) (hz : ‖z‖ * hsNorm K < 1) :
    fredholmExp K z + fredholmExp K (-z) =
      ∑' n : ℕ, z^(2*n+2) / ((n+1 : ℕ) : ℂ) *
        ∑' i, hsPow K (2*n+1) (i,i) := by
  let f : ℕ → ℂ := fun n =>
    (z^(n+2) + (-z)^(n+2)) / ((n+2 : ℕ) : ℂ) * ∑' i, hsPow K (n+1) (i,i)
  have hm : ‖-z‖ * hsNorm K < 1 := by simpa only [norm_neg] using hz
  have hs : Summable f := ((fredholmExp_summable hK z hz).add
    (fredholmExp_summable hK (-z) hm)).congr fun n => by dsimp [f]; ring
  have hE : Summable (fun n => f (2*n)) :=
    hs.comp_injective (by intro n m h; omega)
  have hO : Summable (fun n => f (2*n+1)) :=
    hs.comp_injective (by intro n m h; change 2*n+1 = 2*m+1 at h; omega)
  have he (n : ℕ) : f (2*n) = z^(2*n+2) / ((n+1 : ℕ) : ℂ) *
      ∑' i, hsPow K (2*n+1) (i,i) := by
    have hn : ((n+1 : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    have hp : (-z)^(2*n+2) = z^(2*n+2) := by
      rw [show 2*n+2 = 2*(n+1) by omega, pow_mul, pow_mul]
      congr 1
      ring
    dsimp only [f]
    rw [hp]
    push_cast
    field_simp
    ring
  have ho (n : ℕ) : f (2*n+1) = 0 := by
    have hp : (-z)^(2*n+1+2) = -z^(2*n+1+2) := by
      rw [show 2*n+1+2 = 2*(n+1)+1 by omega, pow_succ, pow_succ,
        pow_mul, pow_mul]
      ring
    dsimp only [f]
    rw [hp, add_neg_cancel, zero_div, zero_mul]
  calc
    _ = ∑' n, f n := by
      rw [fredholmExp, fredholmExp, ← (fredholmExp_summable hK z hz).tsum_add
        (fredholmExp_summable hK (-z) hm)]
      exact tsum_congr fun n => by dsimp [f]; ring
    _ = (∑' n, f (2*n)) + ∑' n, f (2*n+1) := (tsum_even_add_odd hE hO).symm
    _ = _ := by simp only [he, ho, tsum_zero, add_zero]

/-- On a source-dependent neighborhood of zero, the signed determinant product
is exactly the exponential of the actual even-word trace series. -/
theorem exists_signed_determinant_eq_evenWordExponent {w : ℂ} (hw : 1 < w.re) :
    ∃ r > 0, ∀ z : ℂ, ‖z‖ < r →
      determinant w (zero_lt_one.trans hw) z *
        determinant w (zero_lt_one.trans hw) (-z) = exp (-evenWordExponent w z) := by
  let hw0 := zero_lt_one.trans hw
  obtain ⟨_,r,hr,hrK,he⟩ := isRegularizedDet_entireDet2 (kernel_isHS hw0)
  refine ⟨r,hr,fun z hz => ?_⟩
  have hzm : ‖-z‖ < r := by simpa only [norm_neg] using hz
  have hzK : ‖z‖ * hsNorm (kernel w hw0) < 1 :=
    (mul_le_mul_of_nonneg_right hz.le (hsNorm_nonneg _)).trans_lt hrK
  have hex : fredholmExp (kernel w hw0) z + fredholmExp (kernel w hw0) (-z) =
      evenWordExponent w z := by
    rw [parity_exponent (kernel_isHS hw0) z hzK]
    unfold evenWordExponent
    apply tsum_congr
    intro n
    rw [kernel_power_trace hw0 (2*n), opTrace_power_eq_wordTrace hw (2*n+1)]
  rw [determinant_eq_entireDet2 hw0, determinant_eq_entireDet2 hw0,
    he z (mem_ball_zero_iff.mpr hz), he (-z) (mem_ball_zero_iff.mpr hzm),
    fredholmDet, fredholmDet]
  simp only [← exp_add]
  congr 1
  linear_combination -hex

/-- The same neighborhood supports the literal determinant identity and absolute
summation over the entire countable family of even Gauss words. -/
theorem exists_signed_determinant_and_absolute_evenWordSeries {w : ℂ} (hw : 1 < w.re) :
    ∃ r > 0, ∀ z : ℂ, ‖z‖ < r →
      (Summable (fun p : (Σ n : ℕ, Word (2*n+2)) =>
        ‖z^(2*p.1+2) / ((p.1+1 : ℕ) : ℂ) * wordTrace w (2*p.1+1) p.2‖)) ∧
      determinant w (zero_lt_one.trans hw) z *
        determinant w (zero_lt_one.trans hw) (-z) = exp (-evenWordExponent w z) := by
  obtain ⟨r,hr,he⟩ := exists_signed_determinant_eq_evenWordExponent hw
  have hD : 0 ≤ digitMass w := digitMass_nonneg w
  have hD1 : 0 < 1+digitMass w := by linarith only [hD]
  refine ⟨min r (1/(1+digitMass w)), lt_min hr (div_pos zero_lt_one hD1), fun z hz => ?_⟩
  have hz1 : ‖z‖ < r := hz.trans_le (min_le_left _ _)
  have hz2 : ‖z‖ < 1/(1+digitMass w) := hz.trans_le (min_le_right _ _)
  have hb := (lt_div_iff₀ hD1).mp hz2
  have hzD : ‖z‖*digitMass w < 1 := by nlinarith only [hb,norm_nonneg z]
  exact ⟨summable_norm_evenWordSeries hw hzD,he z hz1⟩

#print axioms norm_wordTrace_le
#print axioms tsum_norm_wordTrace_le
#print axioms summable_norm_evenWordSeries
#print axioms exists_signed_determinant_eq_evenWordExponent
#print axioms exists_signed_determinant_and_absolute_evenWordSeries
end GaloisForLFunctions.RenormalizedIntersectionTheory.MayerOrbitDeterminant
