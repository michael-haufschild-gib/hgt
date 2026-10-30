import GaloisForLFunctions.ArithmeticLorentzianGeometry.TheHodgeIndexIsAGapOnThePoleComplementAndOneScalar

/-!
# Infinitesimal pole cost against the prime defect

The two exact atomic pole rows have a product-square bound of the form
`G² S (D + S)`. Weighted Young's inequality therefore pays the complete
signed pole source with any positive fraction of the prime defect, with a
horizon-independent mass cost at every bounded overlap.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Finset RHTower
namespace GaloisForLFunctions.ArithmeticLorentzianGeometry
open SpacingScaleHarmonicAnalysis ArithmeticElectrostatics RenormalizedArithmeticPotentialTheory

/-- A logarithmic translation multiplies the positive half-Mellin moment by √n. -/
theorem integral_atom_mul_exp_half (g : ℝ → ℝ) {n : ℕ} (hn : 1 ≤ n) :
    (∫ u, g (u - Real.log n) * Real.exp (u / 2)) =
      Real.sqrt n * ∫ v, g v * Real.exp (v / 2) := by
  have hroot : Real.exp (Real.log n / 2) = Real.sqrt n := by
    rw [Real.exp_half, Real.exp_log (by exact_mod_cast hn)]
  have he (u : ℝ) : g (u - Real.log n) * Real.exp (u / 2) =
      Real.sqrt n * (g (u - Real.log n) * Real.exp ((u - Real.log n) / 2)) := by
    rw [← hroot]
    calc
      _ = g (u - Real.log n) *
          Real.exp (Real.log n / 2 + (u - Real.log n) / 2) := by congr 2; ring
      _ = _ := by rw [Real.exp_add]; ring
  simp_rw [he]
  rw [integral_const_mul]
  exact congrArg (fun z : ℝ => Real.sqrt n * z)
    (integral_sub_right_eq_self (fun u => g u * Real.exp (u / 2)) (Real.log n))

/-- The positive pole moment is the atom moment times the exact square-root row. -/
theorem integral_atomicTest_mul_exp_half_eq_sqrt_row {g : ℝ → ℝ} {w : ℝ}
    (hg : Continuous g) (hsupp : ∀ u, u ∉ Set.Icc 0 w → g u = 0)
    (N : ℕ) (x : ℕ → ℝ) :
    (∫ u, atomicTest N x g u * Real.exp (u / 2)) =
      (∫ u, g u * Real.exp (u / 2)) * ∑ n ∈ Icc 1 N, Real.sqrt n * x n := by
  rw [integral_atomicTest_mul (by fun_prop) hg hsupp, mul_sum]
  refine sum_congr rfl fun n hn => ?_
  rw [integral_atom_mul_exp_half g (mem_Icc.mp hn).1]
  ring

/-- Harmonic Cauchy–Schwarz pays the negative pole row by logarithmic coefficient mass. -/
theorem sq_poleFunctional_le_log_mass {N : ℕ} (hN : 3 ≤ N) (x : ℕ → ℝ) :
    (poleFunctional N x) ^ 2 ≤
      (∑ n ∈ Icc 1 N, x n ^ 2) * (2 * Real.log N) := by
  have hL1 : 1 ≤ Real.log N := by
    have h3 : (3 : ℝ) ≤ N := by exact_mod_cast hN
    have he : Real.exp 1 ≤ 3 := le_of_lt (Real.exp_one_lt_d9.trans (by norm_num))
    rw [← Real.log_exp 1]
    exact Real.log_le_log (Real.exp_pos 1) (he.trans h3)
  have h := sum_mul_sq_le_sq_mul_sq (Icc 1 N) x (fun n => 1 / Real.sqrt n)
  have he1 : (∑ n ∈ Icc 1 N, x n * (1 / Real.sqrt n)) = poleFunctional N x := by
    unfold poleFunctional
    simp only [LinearMap.coe_mk, AddHom.coe_mk]
    exact sum_congr rfl fun n _ => by ring
  have he2 : (∑ n ∈ Icc 1 N, (1 / Real.sqrt n) ^ 2) =
      ∑ n ∈ Icc 1 N, (1 : ℝ) / n := by
    refine sum_congr rfl fun n _ => ?_
    rw [div_pow, one_pow, Real.sq_sqrt (Nat.cast_nonneg n)]
  have hharm : (∑ n ∈ Icc 1 N, (1 : ℝ) / n) ≤ 1 + Real.log N := by
    have hh := harmonic_le_one_add_log N
    simp only [_root_.harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast] at hh
    simpa only [one_div] using hh
  rw [he1, he2] at h
  exact h.trans (mul_le_mul_of_nonneg_left (by linarith only [hharm, hL1])
    (sum_nonneg fun n _ => sq_nonneg _))

private theorem sq_atom_pole_product_le {g : ℝ → ℝ} {w : ℝ}
    (hg : Continuous g) (hgc : HasCompactSupport g)
    (hsupp : ∀ u, u ∉ Set.Icc 0 w → g u = 0) (hw : 0 < w) :
    ((∫ u, g u * Real.exp (-(u / 2))) * (∫ u, g u * Real.exp (u / 2))) ^ 2 ≤
      Real.exp w * (w * ∫ u, g u ^ 2) ^ 2 := by
  let L := ∫ u, |g u|
  have hL : 0 ≤ L := integral_nonneg fun u => abs_nonneg _
  have hA : |∫ u, g u * Real.exp (-(u / 2))| ≤ L := by
    have h := abs_integral_shift_mul_le hg hgc hsupp
      (φ := fun u => Real.exp (-(u / 2))) (by fun_prop) (c := 0) (M := 1)
      (fun u hu => by
        rw [abs_of_pos (Real.exp_pos _)]
        apply Real.exp_le_one_iff.mpr
        linarith only [hu.1])
    simpa only [sub_zero, one_mul, mul_one] using h
  have hB : |∫ u, g u * Real.exp (u / 2)| ≤ Real.exp (w / 2) * L := by
    have h := abs_integral_shift_mul_le hg hgc hsupp
      (φ := fun u => Real.exp (u / 2)) (by fun_prop) (c := 0) (M := Real.exp (w / 2))
      (fun u hu => by
        rw [abs_of_pos (Real.exp_pos _)]
        exact Real.exp_le_exp.mpr (by linarith only [hu.2]))
    simpa only [sub_zero, mul_comm] using h
  have hP : |(∫ u, g u * Real.exp (-(u / 2))) * (∫ u, g u * Real.exp (u / 2))| ≤
      Real.exp (w / 2) * L ^ 2 := by
    rw [abs_mul]
    calc
      _ ≤ L * (Real.exp (w / 2) * L) := mul_le_mul hA hB (abs_nonneg _) hL
      _ = _ := by ring
  have hexp : Real.exp (w / 2) ^ 2 = Real.exp w := by
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  calc
    _ = |(∫ u, g u * Real.exp (-(u / 2))) * (∫ u, g u * Real.exp (u / 2))| ^ 2 :=
      (sq_abs _).symm
    _ ≤ (Real.exp (w / 2) * L ^ 2) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) hP 2
    _ = Real.exp w * (L ^ 2) ^ 2 := by rw [mul_pow, hexp]
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (sq_nonneg L) (sq_integral_abs_le hg hsupp hw) 2) (Real.exp_pos w).le

/-- The square of the actual pole product is controlled by mass times prime defect plus mass. -/
theorem sq_poleMoments_le_defect {g : ℝ → ℝ} {w : ℝ}
    (hg : Continuous g) (hgc : HasCompactSupport g)
    (hsupp : ∀ u, u ∉ Set.Icc 0 w → g u = 0) (hw : 0 < w)
    {N : ℕ} (hN : 3 ≤ N) (x : ℕ → ℝ) :
    ((∫ u, atomicTest N x g u * Real.exp (-(u / 2))) *
      (∫ u, atomicTest N x g u * Real.exp (u / 2))) ^ 2 ≤
      2 * hardyConstant * Real.exp w * (w * N) ^ 2 * (∫ u, g u ^ 2) ^ 2 *
        (∑ n ∈ Icc 1 N, x n ^ 2) * (poleDefect N x + ∑ n ∈ Icc 1 N, x n ^ 2) := by
  let S := ∑ n ∈ Icc 1 N, x n ^ 2
  let D := poleDefect N x
  let V := ∑ n ∈ Icc 1 N, Real.sqrt n * x n
  have hS : 0 ≤ S := sum_nonneg fun n _ => sq_nonneg _
  have hD : 0 ≤ D := poleDefect_nonneg N x
  have hlog : 0 < Real.log N := Real.log_pos (by exact_mod_cast (show 1 < N by omega))
  have hH := sq_poleFunctional_le_log_mass hN x
  have hV := sq_vRow_le hN x
  change V ^ 2 ≤ hardyConstant * (N ^ 2 / Real.log N) * (D + S) at hV
  have hrows : (poleFunctional N x) ^ 2 * V ^ 2 ≤
      2 * hardyConstant * N ^ 2 * S * (D + S) := by
    calc
      _ ≤ (S * (2 * Real.log N)) * (hardyConstant * (N ^ 2 / Real.log N) * (D + S)) :=
        mul_le_mul hH hV (sq_nonneg V) (mul_nonneg hS (by positivity))
      _ = _ := by field_simp [hlog.ne']
  rw [integral_atomicTest_mul_exp_neg_half hg hsupp,
    integral_atomicTest_mul_exp_half_eq_sqrt_row hg hsupp]
  calc
    _ = ((∫ u, g u * Real.exp (-(u / 2))) * (∫ u, g u * Real.exp (u / 2))) ^ 2 *
        ((poleFunctional N x) ^ 2 * V ^ 2) := by ring
    _ ≤ (Real.exp w * (w * ∫ u, g u ^ 2) ^ 2) *
        (2 * hardyConstant * N ^ 2 * S * (D + S)) :=
      mul_le_mul (sq_atom_pole_product_le hg hgc hsupp hw) hrows
        (mul_nonneg (sq_nonneg _) (sq_nonneg V)) (by positivity)
    _ = _ := by ring

/-- Weighted Young retains an arbitrary defect coefficient in the complete pole payment. -/
theorem two_mul_abs_poleMoments_le_young {g : ℝ → ℝ} {w ε : ℝ}
    (hg : Continuous g) (hgc : HasCompactSupport g)
    (hsupp : ∀ u, u ∉ Set.Icc 0 w → g u = 0) (hw : 0 < w) (hε : 0 < ε)
    {N : ℕ} (hN : 3 ≤ N) (x : ℕ → ℝ) :
    2 * |(∫ u, atomicTest N x g u * Real.exp (-(u / 2))) *
      (∫ u, atomicTest N x g u * Real.exp (u / 2))| ≤
      (∫ u, g u ^ 2) * (ε * poleDefect N x +
        (ε + 2 * hardyConstant * Real.exp w * (w * N) ^ 2 / ε) * ∑ n ∈ Icc 1 N, x n ^ 2) := by
  let P := (∫ u, atomicTest N x g u * Real.exp (-(u / 2))) *
    (∫ u, atomicTest N x g u * Real.exp (u / 2))
  let G := ∫ u, g u ^ 2
  let S := ∑ n ∈ Icc 1 N, x n ^ 2
  let D := poleDefect N x
  let C := 2 * hardyConstant * Real.exp w * (w * N) ^ 2
  have hG : 0 ≤ G := integral_nonneg fun u => sq_nonneg _
  have hS : 0 ≤ S := sum_nonneg fun n _ => sq_nonneg _
  have hD : 0 ≤ D := poleDefect_nonneg N x
  have hC : 0 ≤ C := by dsimp only [C]; have := hardyConstant_pos; positivity
  have hP : P ^ 2 ≤ C * G ^ 2 * S * (D + S) := sq_poleMoments_le_defect hg hgc hsupp hw hN x
  have hYoung : 4 * C * S * (D + S) ≤ (ε * (D + S) + C / ε * S) ^ 2 := by
    calc
      _ ≤ 4 * C * S * (D + S) + (ε * (D + S) - C / ε * S) ^ 2 :=
        le_add_of_nonneg_right (sq_nonneg _)
      _ = _ := by field_simp [hε.ne']; ring
  have hsq : (2 * |P|) ^ 2 ≤ (G * (ε * (D + S) + C / ε * S)) ^ 2 := by
    calc
      _ = 4 * P ^ 2 := by rw [mul_pow, sq_abs]; norm_num
      _ ≤ 4 * (C * G ^ 2 * S * (D + S)) := mul_le_mul_of_nonneg_left hP (by norm_num)
      _ = G ^ 2 * (4 * C * S * (D + S)) := by ring
      _ ≤ G ^ 2 * (ε * (D + S) + C / ε * S) ^ 2 :=
        mul_le_mul_of_nonneg_left hYoung (sq_nonneg G)
      _ = _ := by ring
  have h := (pow_le_pow_iff_left₀ (by positivity : 0 ≤ 2 * |P|)
    (by positivity : 0 ≤ G * (ε * (D + S) + C / ε * S)) two_ne_zero).mp hsq
  calc
    _ ≤ G * (ε * (D + S) + C / ε * S) := h
    _ = _ := by ring

/-- Uniform mass cost for paying the pole with a prescribed defect fraction. -/
def poleRelativeCost (K ε : ℝ) : ℝ :=
  ε + 2 * hardyConstant * Real.exp 1 * K ^ 2 / ε

/-- At bounded overlap, the pole source is infinitesimally bounded relative to the prime defect. -/
theorem two_mul_abs_poleMoments_le_relative_defect {g : ℝ → ℝ} {w K ε : ℝ}
    (hg : Continuous g) (hgc : HasCompactSupport g)
    (hsupp : ∀ u, u ∉ Set.Icc 0 w → g u = 0) (hw : 0 < w) (hw1 : w ≤ 1)
    (hε : 0 < ε) {N : ℕ} (hN : 3 ≤ N) (hwK : w ≤ K / N) (x : ℕ → ℝ) :
    2 * |(∫ u, atomicTest N x g u * Real.exp (-(u / 2))) *
      (∫ u, atomicTest N x g u * Real.exp (u / 2))| ≤
      (∫ u, g u ^ 2) * (ε * poleDefect N x + poleRelativeCost K ε * ∑ n ∈ Icc 1 N, x n ^ 2) := by
  have hNR : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hK2 : (w * N) ^ 2 ≤ K ^ 2 :=
    pow_le_pow_left₀ (mul_nonneg hw.le hNR.le) ((le_div_iff₀ hNR).mp hwK) 2
  have hC : 2 * hardyConstant * Real.exp w * (w * N) ^ 2 ≤
      2 * hardyConstant * Real.exp 1 * K ^ 2 := by
    have hhardy := hardyConstant_pos
    exact mul_le_mul
      (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hw1) (by positivity))
      hK2 (sq_nonneg _) (by positivity)
  have hcost : ε + 2 * hardyConstant * Real.exp w * (w * N) ^ 2 / ε ≤
      poleRelativeCost K ε :=
    add_le_add le_rfl (div_le_div_of_nonneg_right hC hε.le)
  have hG : 0 ≤ ∫ u, g u ^ 2 := integral_nonneg fun u => sq_nonneg _
  have hS : 0 ≤ ∑ n ∈ Icc 1 N, x n ^ 2 := sum_nonneg fun n _ => sq_nonneg _
  exact (two_mul_abs_poleMoments_le_young hg hgc hsupp hw hε hN x).trans
    (mul_le_mul_of_nonneg_left
      (add_le_add le_rfl (mul_le_mul_of_nonneg_right hcost hS)) hG)

end GaloisForLFunctions.ArithmeticLorentzianGeometry
#print axioms GaloisForLFunctions.ArithmeticLorentzianGeometry.two_mul_abs_poleMoments_le_young
#print axioms GaloisForLFunctions.ArithmeticLorentzianGeometry.two_mul_abs_poleMoments_le_relative_defect
