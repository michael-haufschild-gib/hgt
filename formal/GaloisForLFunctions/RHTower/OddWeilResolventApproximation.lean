import GaloisForLFunctions.RHTower.WeilFullConeHerglotzRightHalfPlane
import GaloisForLFunctions.RHTower.OddSectorAnyPoleWeightJointRigidity
import GaloisForLFunctions.HTGeometry.LorentzianCosineIntegral

/-!
# Compact odd approximation of the mixed resolvent Weil form

Reflecting and subtracting the one-sided exponential approximants gives
compact odd tests. Their mixed Weil forms converge, including the prime
sum, to the explicit spectral resolvent functional `mixedWeilLimit`.
The seed domain `Re a, Re b ≥ 2` supplies common integrable majorants;
no positivity or convergence of the limiting kernel is assumed.
-/

open Complex MeasureTheory Set Filter Topology
open scoped ComplexConjugate
open Zeta23 GaloisForLFunctions.HTGeometry

noncomputable section
namespace RHTower.OddResolvent
open WeilHerglotz

def oddTest (a : ℂ) (j : ℕ) (x : ℝ) : ℂ := testFn a j x - testFn a j (-x)

theorem oddTest_odd (a : ℂ) (j : ℕ) (x : ℝ) : oddTest a j (-x) = -oddTest a j x := by
  simp only [oddTest, neg_neg]
  ring

theorem contDiff_oddTest (a : ℂ) (j : ℕ) : ContDiff ℝ 2 (oddTest a j) :=
  (contDiff_testFn a j).sub ((contDiff_testFn a j).comp contDiff_id.neg)

theorem hasCompactSupport_oddTest (a : ℂ) (j : ℕ) : HasCompactSupport (oddTest a j) :=
  (hasCompactSupport_testFn a j).sub ((hasCompactSupport_testFn a j).comp_homeomorph (Homeomorph.neg ℝ))

theorem integrable_oddTest (a : ℂ) (j : ℕ) : Integrable (oddTest a j) :=
  (contDiff_oddTest a j).continuous.integrable_of_hasCompactSupport (hasCompactSupport_oddTest a j)

theorem majorant_exp_bound {a : ℝ} (ha : 2 ≤ a) (u : ℝ) :
    majorant a u ≤ Real.exp (3 * a) * Real.exp (-2 * |u|) := by
  unfold majorant
  by_cases hu : -1 ≤ u
  · rw [Set.indicator_of_mem (show u ∈ Ici (-1 : ℝ) from hu), ← Real.exp_add, ← Real.exp_add]
    apply Real.exp_le_exp.mpr
    by_cases hu0 : 0 ≤ u
    · rw [abs_of_nonneg hu0]
      nlinarith
    · rw [abs_of_neg (lt_of_not_ge hu0)]
      nlinarith
  · rw [Set.indicator_of_notMem (show u ∉ Ici (-1 : ℝ) from hu)]
    positivity

theorem norm_oddTest_exp_bound {a : ℂ} (ha : 2 ≤ a.re) (j : ℕ) (u : ℝ) :
    ‖oddTest a j u‖ ≤ (2 * Real.exp (3 * a.re)) * Real.exp (-2 * |u|) := by
  have hp := (norm_testFn_le (by linarith : 0 ≤ a.re) j u).trans (majorant_exp_bound ha u)
  have hn := (norm_testFn_le (by linarith : 0 ≤ a.re) j (-u)).trans (majorant_exp_bound ha (-u))
  rw [abs_neg] at hn
  exact (norm_sub_le _ _).trans (by linarith)

theorem paperFT_oddTest (a : ℂ) (j : ℕ) (z : ℂ) :
    paperFT (oddTest a j) z = paperFT (testFn a j) z - paperFT (testFn a j) (-z) := by
  rw [← paperFT_comp_neg]
  unfold oddTest paperFT
  simp only [sub_mul]
  exact integral_sub
    (WeilHerglotz.integrable_mul_cexp ((contDiff_testFn a j).continuous.integrable_of_hasCompactSupport
      (hasCompactSupport_testFn a j)) (hasCompactSupport_testFn a j) z)
    (WeilHerglotz.integrable_mul_cexp
      ((contDiff_testFn a j).continuous.comp continuous_neg |>.integrable_of_hasCompactSupport
        ((hasCompactSupport_testFn a j).comp_homeomorph (Homeomorph.neg ℝ)))
      ((hasCompactSupport_testFn a j).comp_homeomorph (Homeomorph.neg ℝ)) z)

theorem tendsto_paperFT_oddTest {a z : ℂ} (hp : 0 < (a - I * z).re)
    (hm : 0 < (a + I * z).re) :
    Tendsto (fun j => paperFT (oddTest a j) z) atTop
      (𝓝 (1 / (a - I * z) - 1 / (a + I * z))) := by
  simp_rw [paperFT_oddTest]
  exact (tendsto_paperFT_testFn hp).sub
    (by simpa using tendsto_paperFT_testFn (w := a) (z := -z) (by simpa using hm))

theorem oddResolvent_formula {a : ℂ} (ha : 0 < a.re) (r : ℝ) :
    1 / (a - I * (r : ℂ)) - 1 / (a + I * (r : ℂ)) =
      2 * I * r / (a ^ 2 + (r : ℂ) ^ 2) := by
  have hp : a - I * (r : ℂ) ≠ 0 := by
    intro h
    have := congrArg Complex.re h
    simp at this
    linarith
  have hm : a + I * (r : ℂ) ≠ 0 := by
    intro h
    have := congrArg Complex.re h
    simp at this
    linarith
  have hden : a ^ 2 + (r : ℂ) ^ 2 = (a - I * (r : ℂ)) * (a + I * (r : ℂ)) := by
    ring_nf
    rw [I_sq]
    ring
  rw [hden]
  field_simp
  ring

theorem norm_weilTest_le_of_decay {f g : ℝ → ℂ} {C : ℝ} (hC : 0 ≤ C)
    (hf : ∀ t, ‖f t‖ ≤ C * Real.exp (-(2 * |t|)))
    (hg : ∀ t, ‖g t‖ ≤ C * Real.exp (-(2 * |t|))) (x : ℝ) :
    ‖EF.weilTest f g x‖ ≤
      C ^ 2 * (∫ t : ℝ, Real.exp (-((1 / 2) * |t|))) * Real.exp (-((3 / 2) * |x|)) := by
  rw [WeilSpectral.weilTest_apply]
  calc ‖∫ t, f t * conj (g (t - x))‖ ≤ ∫ t, ‖f t * conj (g (t - x))‖ :=
        norm_integral_le_integral_norm _
    _ = crossCorr (fun t => ‖f t‖) (fun t => ‖g t‖) x := by
        simp only [norm_mul, norm_conj, crossCorr]
    _ ≤ |crossCorr (fun t => ‖f t‖) (fun t => ‖g t‖) x| := le_abs_self _
    _ ≤ _ := by
        simpa only [abs_norm, show (2 : ℝ) - 3 / 2 = 1 / 2 by norm_num] using
          EvenSector.abs_crossCorr_le_of_decay (b := 2) (b₁ := 3 / 2)
            (by norm_num) (by norm_num) hC
            (fun t => by simpa only [abs_norm] using hf t)
            (fun t => by simpa only [abs_norm] using hg t) x

theorem normSq_paperFT_testFn_bound {a : ℂ} (ha : 2 ≤ a.re) (j : ℕ) (r : ℝ) :
    ‖paperFT (testFn a j) r‖ ^ 2 ≤ 8 * (1 + a.im ^ 2) / (1 + r ^ 2) := by
  have hp : 0 < a.re := by linarith
  have hden : 0 < ‖a - I * (r : ℂ)‖ := by
    apply norm_pos_iff.mpr
    intro h
    have hh := congrArg Complex.re h
    simp at hh
    linarith
  have hn : ‖a - I * (r : ℂ)‖ ^ 2 = a.re ^ 2 + (r - a.im) ^ 2 := by
    rw [Complex.sq_norm, normSq_sub_I_mul]
  have hlower : 1 + r ^ 2 ≤ 2 * (1 + a.im ^ 2) * ‖a - I * (r : ℂ)‖ ^ 2 := by
    rw [hn]
    nlinarith [sq_nonneg (r - 2 * a.im), sq_nonneg (a.re - 2),
      mul_nonneg (sq_nonneg a.im) (sq_nonneg (r - a.im)),
      mul_nonneg (sq_nonneg a.im) (show 0 ≤ a.re ^ 2 - 4 by nlinarith)]
  have hft := norm_paperFT_testFn_le hp j r
  have hs : ‖paperFT (testFn a j) r‖ ^ 2 ≤ 4 / ‖a - I * (r : ℂ)‖ ^ 2 := by
    simpa only [← sq, div_pow, show (2 : ℝ) ^ 2 = 4 by norm_num] using
      mul_self_le_mul_self (norm_nonneg (paperFT (testFn a j) r)) hft
  apply hs.trans
  apply (div_le_div_iff₀ (sq_pos_of_pos hden) (by positivity : 0 < 1 + r ^ 2)).mpr
  nlinarith

theorem normSq_paperFT_oddTest_bound {a : ℂ} (ha : 2 ≤ a.re) (j : ℕ) (r : ℝ) :
    ‖paperFT (oddTest a j) r‖ ^ 2 ≤ 32 * (1 + a.im ^ 2) / (1 + r ^ 2) := by
  rw [paperFT_oddTest]
  have hp := normSq_paperFT_testFn_bound ha j r
  have hm := normSq_paperFT_testFn_bound ha j (-r)
  simp only [neg_sq, Complex.ofReal_neg] at hm
  have ht := norm_sub_le (paperFT (testFn a j) r) (paperFT (testFn a j) (-r))
  have hn := sq_nonneg (‖paperFT (testFn a j) r‖ - ‖paperFT (testFn a j) (-r)‖)
  have hs := mul_self_le_mul_self (norm_nonneg _) ht
  rw [show 32 * (1 + a.im ^ 2) / (1 + r ^ 2) =
    4 * (8 * (1 + a.im ^ 2) / (1 + r ^ 2)) by ring]
  nlinarith

def mixedCorr (a b : ℂ) (j : ℕ) : ℝ → ℂ := EF.weilTest (oddTest a j) (oddTest b j)

def oddTransform (a z : ℂ) : ℂ := 1 / (a - I * z) - 1 / (a + I * z)

theorem paperFT_mixedCorr (a b : ℂ) (j : ℕ) (z : ℂ) :
    paperFT (mixedCorr a b j) z =
      paperFT (oddTest a j) z * conj (paperFT (oddTest b j) (conj z)) :=
  EF.paperFT_weilTest (contDiff_oddTest a j).continuous (contDiff_oddTest b j).continuous
    (hasCompactSupport_oddTest a j) (hasCompactSupport_oddTest b j) z

theorem tendsto_paperFT_mixedCorr {a b : ℂ} (ha : 0 < a.re) (hb : 0 < b.re) (r : ℝ) :
    Tendsto (fun j => paperFT (mixedCorr a b j) r) atTop
      (𝓝 (oddTransform a r * conj (oddTransform b r))) := by
  have hpa : 0 < (a - I * (r : ℂ)).re := by simpa using ha
  have hma : 0 < (a + I * (r : ℂ)).re := by simpa using ha
  have hpb : 0 < (b - I * (r : ℂ)).re := by simpa using hb
  have hmb : 0 < (b + I * (r : ℂ)).re := by simpa using hb
  simp_rw [paperFT_mixedCorr, Complex.conj_ofReal]
  exact (tendsto_paperFT_oddTest hpa hma).mul
    (Complex.continuous_conj.tendsto _ |>.comp (tendsto_paperFT_oddTest hpb hmb))

theorem norm_paperFT_mixedCorr_bound {a b : ℂ} (ha : 2 ≤ a.re) (hb : 2 ≤ b.re)
    (j : ℕ) (r : ℝ) :
    ‖paperFT (mixedCorr a b j) r‖ ≤
      (16 * (2 + a.im ^ 2 + b.im ^ 2)) * (1 + r ^ 2)⁻¹ := by
  rw [paperFT_mixedCorr, Complex.conj_ofReal, norm_mul, norm_conj]
  have h1 := normSq_paperFT_oddTest_bound ha j r
  have h2 := normSq_paperFT_oddTest_bound hb j r
  have h3 := sq_nonneg (‖paperFT (oddTest a j) r‖ - ‖paperFT (oddTest b j) r‖)
  have he : (16 * (2 + a.im ^ 2 + b.im ^ 2)) * (1 + r ^ 2)⁻¹ =
      (32 * (1 + a.im ^ 2) / (1 + r ^ 2) + 32 * (1 + b.im ^ 2) / (1 + r ^ 2)) / 2 := by ring
  rw [he]
  nlinarith

theorem continuous_paperFT_mixedCorr (a b : ℂ) (j : ℕ) :
    Continuous fun r : ℝ => paperFT (mixedCorr a b j) r := by
  simp_rw [paperFT_mixedCorr, Complex.conj_ofReal]
  exact (continuous_paperFT_real (integrable_oddTest a j)).mul
    (Complex.continuous_conj.comp (continuous_paperFT_real (integrable_oddTest b j)))

theorem tendsto_integral_mixedCorr_weight {a b : ℂ} (ha : 2 ≤ a.re) (hb : 2 ≤ b.re)
    {w : ℝ → ℂ} (hw : Continuous w) (hi : Integrable fun r => (1 + r ^ 2)⁻¹ * ‖w r‖) :
    Tendsto (fun j => ∫ r : ℝ, paperFT (mixedCorr a b j) r * w r) atTop
      (𝓝 (∫ r : ℝ, oddTransform a r * conj (oddTransform b r) * w r)) := by
  let C : ℝ := 16 * (2 + a.im ^ 2 + b.im ^ 2)
  refine tendsto_integral_of_dominated_convergence
    (fun r => C * ((1 + r ^ 2)⁻¹ * ‖w r‖))
    (fun j => ((continuous_paperFT_mixedCorr a b j).mul hw).aestronglyMeasurable)
    (hi.const_mul C) (fun j => Eventually.of_forall fun r => ?_)
    (Eventually.of_forall fun r =>
      (tendsto_paperFT_mixedCorr (by linarith) (by linarith) r).mul_const (w r))
  rw [norm_mul, ← mul_assoc]
  exact mul_le_mul_of_nonneg_right (norm_paperFT_mixedCorr_bound ha hb j r) (norm_nonneg _)

theorem integrable_invQuad_gamma :
    Integrable fun r : ℝ => (1 + r ^ 2)⁻¹ * ‖(EF.gammaBracket r : ℂ)‖ := by
  have hi := (integrable_poissonWeight_mul_re_digamma_half (a := 1)
    (c := 1 / 4) (by norm_num) (by norm_num)).sub
    ((integrable_poissonWeight (a := 1) (by norm_num)).mul_const (Real.log Real.pi))
  have hj : Integrable fun r => (1 + r ^ 2)⁻¹ * EF.gammaBracket r := by
    refine (hi.const_mul Real.pi).congr (Eventually.of_forall fun r => ?_)
    dsimp only [Pi.sub_apply]
    rw [gammaBracket_eq, poissonWeight]
    norm_num only [one_pow]
    field_simp
  refine hj.norm.congr (Eventually.of_forall fun r => ?_)
  dsimp only
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (by positivity : 0 ≤ (1 + r ^ 2)⁻¹),
    Complex.norm_real, Real.norm_eq_abs]

theorem tendsto_arch_mixedCorr {a b : ℂ} (ha : 2 ≤ a.re) (hb : 2 ≤ b.re) :
    Tendsto (fun j => ∫ r : ℝ, paperFT (mixedCorr a b j) r * (EF.gammaBracket r : ℂ)) atTop
      (𝓝 (∫ r : ℝ, oddTransform a r * conj (oddTransform b r) * (EF.gammaBracket r : ℂ))) :=
  tendsto_integral_mixedCorr_weight ha hb
    (Complex.continuous_ofReal.comp continuous_gammaBracket) integrable_invQuad_gamma

theorem exists_norm_mixedCorr_bound {a b : ℂ} (ha : 2 ≤ a.re) (hb : 2 ≤ b.re) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ j x, ‖mixedCorr a b j x‖ ≤ C * Real.exp (-((3 / 2) * |x|)) := by
  let D : ℝ := 2 * Real.exp (3 * a.re) + 2 * Real.exp (3 * b.re)
  have hD : 0 ≤ D := by dsimp [D]; positivity
  refine ⟨D ^ 2 * (∫ t : ℝ, Real.exp (-((1 / 2) * |t|))),
    mul_nonneg (sq_nonneg _) (integral_nonneg fun _ => (Real.exp_pos _).le), fun j x => ?_⟩
  apply norm_weilTest_le_of_decay hD
  · intro t
    have h := norm_oddTest_exp_bound ha j t
    have h0 : 0 ≤ 2 * Real.exp (3 * b.re) * Real.exp (-2 * |t|) := by positivity
    dsimp [D]
    rw [add_mul]
    simpa only [neg_mul] using h.trans (le_add_of_nonneg_right h0)
  · intro t
    have h := norm_oddTest_exp_bound hb j t
    have h0 : 0 ≤ 2 * Real.exp (3 * a.re) * Real.exp (-2 * |t|) := by positivity
    dsimp [D]
    rw [add_mul]
    simpa only [neg_mul] using h.trans (le_add_of_nonneg_left h0)

def mixedSumLimit (a b : ℂ) (x : ℝ) : ℂ :=
  (1 / Real.pi : ℂ) * ∫ r : ℝ, oddTransform a r * conj (oddTransform b r) * (Real.cos (r * x) : ℂ)

theorem integrable_invQuad_cos (x : ℝ) :
    Integrable fun r : ℝ => (1 + r ^ 2)⁻¹ * ‖(Real.cos (r * x) : ℂ)‖ := by
  refine integrable_inv_one_add_sq.mono' (by fun_prop) (Eventually.of_forall fun r => ?_)
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (by positivity : 0 ≤ (1 + r ^ 2)⁻¹), abs_norm,
    Complex.norm_real, Real.norm_eq_abs]
  exact mul_le_of_le_one_right (by positivity) (Real.abs_cos_le_one _)

theorem tendsto_mixedCorr_sum {a b : ℂ} (ha : 2 ≤ a.re) (hb : 2 ≤ b.re) (x : ℝ) :
    Tendsto (fun j => mixedCorr a b j x + mixedCorr a b j (-x)) atTop
      (𝓝 (mixedSumLimit a b x)) := by
  have he : ∀ j, mixedCorr a b j x + mixedCorr a b j (-x) =
      (1 / Real.pi : ℂ) * ∫ r : ℝ, paperFT (mixedCorr a b j) r * (Real.cos (r * x) : ℂ) := by
    intro j
    have hd := EF.weilTest_contDiff (contDiff_oddTest a j) (contDiff_oddTest b j).continuous
      (hasCompactSupport_oddTest a j)
    have hs := EF.weilTest_hasCompactSupport (hasCompactSupport_oddTest a j)
      (hasCompactSupport_oddTest b j)
    exact EF.k_add_k_neg hd.continuous (hd.continuous.integrable_of_hasCompactSupport hs)
      (EF.integrable_fourier_of_contDiff_two hd hs) x
  simp_rw [he]
  exact (tendsto_integral_mixedCorr_weight ha hb (by fun_prop) (integrable_invQuad_cos x)).const_mul _

theorem norm_prime_mixed_le {lam : ℕ → ℝ} {a b : ℂ} {C : ℝ} (hC : 0 ≤ C)
    (hbound : ∀ j x, ‖mixedCorr a b j x‖ ≤ C * Real.exp (-((3 / 2) * |x|))) (j n : ℕ) :
    ‖primeCoeff lam n * (mixedCorr a b j (Real.log n) + mixedCorr a b j (-Real.log n))‖ ≤
      (2 * C) * (|lam n| / (n : ℝ) ^ (2 : ℝ)) := by
  rw [norm_mul, primeCoeff, Complex.norm_real, Real.norm_eq_abs]
  by_cases hn : 2 ≤ n
  · rw [if_pos hn, abs_div, abs_of_nonneg (Real.sqrt_nonneg _)]
    have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
    have h1 := hbound j (Real.log n)
    have h2 := hbound j (-Real.log n)
    rw [abs_neg] at h2
    rw [abs_of_nonneg (Real.log_natCast_nonneg n)] at h1 h2
    have hsum : ‖mixedCorr a b j (Real.log n) + mixedCorr a b j (-Real.log n)‖ ≤
        2 * C * Real.exp (-((3 / 2) * Real.log n)) := (norm_add_le _ _).trans (by linarith)
    calc |lam n| / Real.sqrt n * ‖mixedCorr a b j (Real.log n) + mixedCorr a b j (-Real.log n)‖
        ≤ |lam n| / Real.sqrt n * (2 * C * Real.exp (-((3 / 2) * Real.log n))) :=
          mul_le_mul_of_nonneg_left hsum (by positivity)
      _ = (2 * C) * (|lam n| / (Real.sqrt n * Real.exp ((3 / 2) * Real.log n))) := by
          rw [Real.exp_neg]
          ring
      _ = _ := by rw [sqrt_mul_exp_eq_rpow hn]; norm_num
  · rw [if_neg hn]
    simp only [abs_zero, zero_mul]
    positivity

theorem tendsto_prime_mixed {lam : ℕ → ℝ} (hW : WeilPositiveOddAt 1 lam)
    {a b : ℂ} (ha : 2 ≤ a.re) (hb : 2 ≤ b.re) :
    Tendsto (fun j => ∑' n : ℕ, primeCoeff lam n *
      (mixedCorr a b j (Real.log n) + mixedCorr a b j (-Real.log n))) atTop
      (𝓝 (∑' n : ℕ, primeCoeff lam n * mixedSumLimit a b (Real.log n))) := by
  obtain ⟨C, hC, hc⟩ := exists_norm_mixedCorr_bound ha hb
  have hs := (OddSector.summable_abs_div_rpow_of_weilPositiveOddAt_anyWeight hW
    (σ := 2) (by norm_num)).mul_left (2 * C)
  exact tendsto_tsum_of_dominated_convergence hs
    (fun n => (tendsto_mixedCorr_sum ha hb (Real.log n)).const_mul _)
    (Eventually.of_forall fun j n => norm_prime_mixed_le hC hc j n)

def mixedTransform (a b z : ℂ) : ℂ := oddTransform a z * conj (oddTransform b (conj z))

theorem tendsto_paperFT_mixedCorr_complex {a b z : ℂ}
    (ha : |z.im| < a.re) (hb : |z.im| < b.re) :
    Tendsto (fun j => paperFT (mixedCorr a b j) z) atTop (𝓝 (mixedTransform a b z)) := by
  have hap : 0 < (a - I * z).re := by simp; linarith [(abs_lt.mp ha).1]
  have ham : 0 < (a + I * z).re := by simp; linarith [(abs_lt.mp ha).2]
  have hbp : 0 < (b - I * conj z).re := by simp; linarith [(abs_lt.mp hb).2]
  have hbm : 0 < (b + I * conj z).re := by simp; linarith [(abs_lt.mp hb).1]
  simp_rw [paperFT_mixedCorr]
  exact (tendsto_paperFT_oddTest hap ham).mul
    (Complex.continuous_conj.tendsto _ |>.comp (tendsto_paperFT_oddTest hbp hbm))

def mixedWeilLimit (lam : ℕ → ℝ) (a b : ℂ) : ℂ :=
  mixedTransform a b (I / 2) + mixedTransform a b (-I / 2) -
    ∑' n : ℕ, primeCoeff lam n * mixedSumLimit a b (Real.log n) +
    (1 / (2 * Real.pi) : ℂ) * ∫ r : ℝ,
      oddTransform a r * conj (oddTransform b r) * (EF.gammaBracket r : ℂ)

theorem tendsto_weil_mixed {lam : ℕ → ℝ} (hW : WeilPositiveOddAt 1 lam)
    {a b : ℂ} (ha : 2 ≤ a.re) (hb : 2 ≤ b.re) :
    Tendsto (fun j => weilFullFunctional lam (mixedCorr a b j)) atTop
      (𝓝 (mixedWeilLimit lam a b)) := by
  have hp := tendsto_paperFT_mixedCorr_complex (a := a) (b := b) (z := I / 2)
    (by norm_num; linarith) (by norm_num; linarith)
  have hm := tendsto_paperFT_mixedCorr_complex (a := a) (b := b) (z := -I / 2)
    (by norm_num; linarith) (by norm_num; linarith)
  exact ((hp.add hm).sub (tendsto_prime_mixed hW ha hb)).add
    ((tendsto_arch_mixedCorr ha hb).const_mul _)

end RHTower.OddResolvent
