import GaloisForLFunctions.SurfaceOfSpecZ.TheStepanovSideIsBlindToRealZeros
import GaloisForLFunctions.ZeroConfigurationGeometry.SplineBumpsDecayAtAnExplicitRate
import GaloisForLFunctions.RHTower.ZetaVerticalStripPolynomialBound

/-!
# The trace zeta function at the power degrees

Fix `k ≥ 1` and the box spline `B = U_1^{⋆(r+1)}`. The traces of the smoothed Frobenius graphs of
degree `nᵏ` are `2 Re S(k log n) = Σ_z e_z n^{kz}`, `e_z` the merged spline coefficients of the zeros
`½ + z` (`evenCoeff`). Their Dirichlet series is a sum of shifted zeta functions
(`traceDirichlet_eq`):

  `Σ_{n ≥ 1} 2 Re S(k log n) n^{−s} = Σ_z e_z ζ(s − kz) =: Z_k(s)`,   `Re s > 1 + k/2`,

the analogue of the rationality of the zeta function of a curve over `𝔽_{qᵏ}`: its poles are the
points `1 + kz`, with residue `e_z`. `Z_k` continues analytically to `1 < Re s < 2 + k/2` off these
poles (`differentiableAt_traceZetaOf`) once the spline is smooth enough: if `|ζ(σ + it)| ≤ C|t|^N`
for `|σ| ≤ 3 + k`, `|t| ≥ 1` (`RHTower.exists_bound_norm_riemannZeta_strip`), order `r` with
`N + 2 ≤ 2(r + 1)` makes the series converge locally uniformly. The inputs are the decay
`|B̂(w)|(1 + |w|)^{r+1} ≤ 2^{r+1} e^{(r+1)|Im w|}` (`norm_paperFT_boxSpline_le`) and the tempered
zero count.
-/

open Complex Set Filter Topology
open scoped ComplexConjugate

noncomputable section

namespace GaloisForLFunctions.SurfaceOfSpecZ

open ArithmeticOrientationGeometry ArithmeticCastelnuovoSeveri SquareRootThreshold Zeta23

/-! ### The box spline of order `r` -/

theorem contDiff_boxSpline_two {r : ℕ} (hr : 3 ≤ r) : ContDiff ℝ 2 (boxSpline 1 r) := by
  obtain ⟨k, rfl⟩ : ∃ k, r = k + 1 := ⟨r - 1, by omega⟩
  exact (contDiff_boxSpline one_pos k).of_le (by exact_mod_cast (show 2 ≤ k by omega))

theorem hasCompactSupport_boxSpline (r : ℕ) : HasCompactSupport (boxSpline 1 r) :=
  hasCompactSupport_of_support_subset_abs (boxSpline_support one_pos r)

theorem paperFT_boxSpline_eq (r : ℕ) (w : ℂ) :
    paperFT (boxSpline 1 r) w = sincC w ^ (r + 1) := by
  have h1 : (fun x : ℝ => ((RHTower.WeilDeletion.unif 1 x : ℝ) : ℂ)) = boxTest 1 := by
    funext x
    simp only [RHTower.WeilDeletion.unif, boxTest, Set.indicator]
    split_ifs <;> norm_num
  have h2 := RHTower.WeilDeletion.paperFT_upow 1 r w
  change paperFT (fun x => (RHTower.WeilDeletion.upow 1 r x : ℂ)) w = _
  rw [h2, h1, paperFT_boxTest one_pos, one_mul]

/-- **Decay of the box spline.** `|B̂(w)| (1 + |w|)^{r+1} ≤ 2^{r+1} e^{(r+1)|Im w|}`. -/
theorem norm_paperFT_boxSpline_le (r : ℕ) (w : ℂ) :
    ‖paperFT (boxSpline 1 r) w‖ * (1 + ‖w‖) ^ (r + 1) ≤
      2 ^ (r + 1) * Real.exp ((r + 1) * |w.im|) := by
  rw [paperFT_boxSpline_eq, norm_pow, ← mul_pow]
  have h := ZeroConfigurationGeometry.one_add_mul_norm_sincC_le (δ := 1) one_pos w
  simp only [one_mul] at h
  calc (‖sincC w‖ * (1 + ‖w‖)) ^ (r + 1) ≤ (2 * Real.exp |w.im|) ^ (r + 1) :=
        pow_le_pow_left₀ (by positivity) (by linarith [h]) _
    _ = 2 ^ (r + 1) * Real.exp ((r + 1) * |w.im|) := by
        rw [mul_pow, ← Real.exp_nat_mul]; push_cast; ring_nf

/-- Near the critical line: for `|Im w| ≤ ½` and `y ≤ |w|`, `|B̂(w)| ≤ 2^{r+1} e^{(r+1)/2}/(1 + y)^{r+1}`. -/
theorem norm_paperFT_boxSpline_le' (r : ℕ) {w : ℂ} (hw : |w.im| ≤ 1 / 2) {y : ℝ} (hy0 : 0 ≤ y)
    (hy : y ≤ ‖w‖) :
    ‖paperFT (boxSpline 1 r) w‖ ≤ 2 ^ (r + 1) * Real.exp ((r + 1) / 2) / (1 + y) ^ (r + 1) := by
  have h := norm_paperFT_boxSpline_le r w
  have he : Real.exp ((r + 1) * |w.im|) ≤ Real.exp ((r + 1) / 2) :=
    Real.exp_le_exp.mpr (by nlinarith)
  have hp : (1 + y) ^ (r + 1) ≤ (1 + ‖w‖) ^ (r + 1) :=
    pow_le_pow_left₀ (by linarith) (by linarith) _
  rw [le_div_iff₀ (by positivity)]
  calc ‖paperFT (boxSpline 1 r) w‖ * (1 + y) ^ (r + 1)
      ≤ ‖paperFT (boxSpline 1 r) w‖ * (1 + ‖w‖) ^ (r + 1) :=
        mul_le_mul_of_nonneg_left hp (norm_nonneg _)
    _ ≤ 2 ^ (r + 1) * Real.exp ((r + 1) * |w.im|) := h
    _ ≤ 2 ^ (r + 1) * Real.exp ((r + 1) / 2) := mul_le_mul_of_nonneg_left he (by positivity)

/-! ### The coefficients -/

/-- The multiplicity of `½ + z` as a zero of `ζ`, or `0`. -/
def zeroWeight (z : ℂ) : ℝ :=
  zetaZeroConfig.carrier.indicator (fun ρ => (zetaZeroConfig.mult ρ : ℝ)) (1 / 2 + z)

theorem zeroWeight_nonneg (z : ℂ) : 0 ≤ zeroWeight z :=
  Set.indicator_nonneg (fun _ _ => Nat.cast_nonneg _) _

/-- `A_r = 4^{r+1} e^{r+1}`. -/
def splineConst (r : ℕ) : ℝ := 4 ^ (r + 1) * Real.exp (r + 1)

theorem splineConst_nonneg (r : ℕ) : 0 ≤ splineConst r := by unfold splineConst; positivity

theorem norm_lagCoeff_boxSpline_le {r : ℕ} (hr : 3 ≤ r) (z : ℂ) :
    ‖lagCoeff zetaZeroConfig (boxSpline 1 r) z‖ ≤
      zeroWeight z * splineConst r / (1 + |z.im|) ^ (2 * (r + 1)) := by
  by_cases hz : (1 / 2 + z) ∈ zetaZeroConfig.carrier
  · have hb := contDiff_boxSpline_two hr
    have hbc := hasCompactSupport_boxSpline r
    have hre : |z.re| ≤ 1 / 2 := by
      obtain ⟨-, h0, h1⟩ := hz
      simp at h0 h1
      rw [abs_le]; constructor <;> linarith
    rw [lagCoeff, Set.indicator_of_mem hz, zeroWeight, Set.indicator_of_mem hz, norm_mul,
      EF.paperFT_weilTest hb.continuous hb.continuous hbc hbc, norm_mul, Complex.norm_conj,
      Complex.norm_natCast, gammaOf_half_add]
    have hy0 : 0 ≤ |z.im| := abs_nonneg _
    have hzim : |z.im| ≤ ‖z‖ := Complex.abs_im_le_norm z
    have h1 := norm_paperFT_boxSpline_le' r (w := -(I * z)) (by simpa using hre) hy0
      (by simpa using hzim)
    have h2 := norm_paperFT_boxSpline_le' r (w := conj (-(I * z)))
      (by simpa [map_neg, map_mul, Complex.conj_I] using hre) hy0 (by simpa using hzim)
    have hm : (0 : ℝ) ≤ zetaZeroConfig.mult (1 / 2 + z) := Nat.cast_nonneg _
    have hsplit : (zetaZeroConfig.mult (1 / 2 + z) : ℝ) * splineConst r / (1 + |z.im|) ^ (2 * (r + 1)) =
        zetaZeroConfig.mult (1 / 2 + z) *
          ((2 ^ (r + 1) * Real.exp ((r + 1) / 2) / (1 + |z.im|) ^ (r + 1)) *
            (2 ^ (r + 1) * Real.exp ((r + 1) / 2) / (1 + |z.im|) ^ (r + 1))) := by
      unfold splineConst
      rw [show (4 : ℝ) ^ (r + 1) = 2 ^ (r + 1) * 2 ^ (r + 1) by rw [← mul_pow]; norm_num,
        show Real.exp ((r : ℝ) + 1) = Real.exp ((r + 1) / 2) * Real.exp ((r + 1) / 2) by
          rw [← Real.exp_add]; ring_nf, show 2 * (r + 1) = (r + 1) + (r + 1) by ring, pow_add]
      field_simp
    rw [hsplit]
    exact mul_le_mul_of_nonneg_left (mul_le_mul h1 h2 (norm_nonneg _) (by positivity)) hm
  · rw [lagCoeff, Set.indicator_of_notMem hz, norm_zero, zeroWeight, Set.indicator_of_notMem hz,
      zero_mul, zero_div]

/-- The merged coefficient `e_z = F(z) + conj F(conj z)`. -/
abbrev traceCoeff (r : ℕ) (z : ℂ) : ℂ := evenCoeff zetaZeroConfig (boxSpline 1 r) z

theorem norm_traceCoeff_le {r : ℕ} (hr : 3 ≤ r) (z : ℂ) :
    ‖traceCoeff r z‖ ≤
      (zeroWeight z + zeroWeight (conj z)) * splineConst r / (1 + |z.im|) ^ (2 * (r + 1)) := by
  have h1 := norm_lagCoeff_boxSpline_le hr z
  have h2 := norm_lagCoeff_boxSpline_le hr (conj z)
  rw [Complex.conj_im, abs_neg] at h2
  calc ‖traceCoeff r z‖ ≤ ‖lagCoeff zetaZeroConfig (boxSpline 1 r) z‖ +
        ‖conj (lagCoeff zetaZeroConfig (boxSpline 1 r) (conj z))‖ := norm_add_le _ _
    _ ≤ _ := by
        rw [Complex.norm_conj, add_mul, add_div]
        exact add_le_add h1 h2

/-- The conjugation of `ℂ` as an equivalence. -/
def conjEquiv : ℂ ≃ ℂ := ⟨fun z => conj z, fun z => conj z, fun z => by simp, fun z => by simp⟩

/-- **The tempered count, with the weight `(1 + |Im z|)^{−2}`.** -/
theorem summable_zeroWeight_div :
    Summable fun z : ℂ => (zeroWeight z + zeroWeight (conj z)) / (1 + |z.im|) ^ 2 := by
  set H : ℂ → ℝ := fun z => zetaZeroConfig.carrier.indicator
    (fun ρ => (zetaZeroConfig.mult ρ : ℝ) / (1 + Complex.normSq (gammaOf ρ))) (1 / 2 + z) with hH
  have hHs : Summable H := by
    have h1 : Summable (zetaZeroConfig.carrier.indicator
        fun ρ => (zetaZeroConfig.mult ρ : ℝ) / (1 + Complex.normSq (gammaOf ρ))) :=
      summable_subtype_iff_indicator.mp SquareRootThreshold.temperedConfig_zetaZeroConfig
    have : H = (zetaZeroConfig.carrier.indicator
        fun ρ => (zetaZeroConfig.mult ρ : ℝ) / (1 + Complex.normSq (gammaOf ρ))) ∘
        Equiv.addLeft (1 / 2 : ℂ) := by
      funext z; simp [hH]
    rw [this]
    exact (Equiv.summable_iff _).mpr h1
  have hHc : Summable (fun z => H (conj z)) := (Equiv.summable_iff conjEquiv).mpr hHs
  -- `zeroWeight z / (1 + |Im z|)² ≤ (5/4) H z`
  have hpt : ∀ z : ℂ, zeroWeight z / (1 + |z.im|) ^ 2 ≤ 5 / 4 * H z := by
    intro z
    by_cases hz : (1 / 2 + z) ∈ zetaZeroConfig.carrier
    · have hre : |z.re| ≤ 1 / 2 := by
        obtain ⟨-, h0, h1⟩ := hz
        simp at h0 h1
        rw [abs_le]; constructor <;> linarith
      simp only [zeroWeight, hH, Set.indicator_of_mem hz]
      rw [normSq_gammaOf_half_add, Complex.normSq_apply]
      have hm : (0 : ℝ) ≤ zetaZeroConfig.mult (1 / 2 + z) := Nat.cast_nonneg _
      have hre2 : z.re * z.re ≤ 1 / 4 := by nlinarith [abs_le.mp hre, abs_mul_abs_self z.re]
      have him2 : z.im * z.im = |z.im| ^ 2 := by rw [sq_abs]; ring
      have hpos1 : 0 < (1 + |z.im|) ^ 2 := by positivity
      have hpos2 : 0 < 1 + (z.re * z.re + z.im * z.im) := by nlinarith [mul_self_nonneg z.re]
      rw [div_le_iff₀ hpos1, mul_div_assoc', le_div_iff₀ hpos2] at *
      rw [div_mul_eq_mul_div, le_div_iff₀ hpos2]
      nlinarith [abs_nonneg z.im, mul_nonneg hm (abs_nonneg z.im)]
    · simp only [zeroWeight, hH, Set.indicator_of_notMem hz, zero_div, mul_zero, le_refl]
  refine Summable.of_nonneg_of_le (fun z => by
      have := zeroWeight_nonneg z; have := zeroWeight_nonneg (conj z); positivity)
    (fun z => ?_) ((hHs.add hHc).mul_left (5 / 4))
  have h1 := hpt z
  have h2 := hpt (conj z)
  rw [Complex.conj_im, abs_neg, conj_conj] at h2
  rw [add_div]
  simp only [Pi.add_apply]
  linarith

/-- **Polynomial weights are paid by the spline.** For `N + 2 ≤ 2(r + 1)`,
`Σ_z |e_z| (1 + |Im z|)^N < ∞`. -/
theorem summable_traceCoeff_mul_pow {r N : ℕ} (hr : 3 ≤ r) (hN : N + 2 ≤ 2 * (r + 1)) :
    Summable fun z : ℂ => ‖traceCoeff r z‖ * (1 + |z.im|) ^ N := by
  refine Summable.of_nonneg_of_le (fun _ => by positivity) (fun z => ?_)
    (summable_zeroWeight_div.mul_left (splineConst r))
  have hz := norm_traceCoeff_le hr z
  have hy : (1 : ℝ) ≤ 1 + |z.im| := by linarith [abs_nonneg z.im]
  have hw : 0 ≤ zeroWeight z + zeroWeight (conj z) :=
    add_nonneg (zeroWeight_nonneg _) (zeroWeight_nonneg _)
  have hpow : (1 + |z.im|) ^ N * (1 + |z.im|) ^ 2 ≤ (1 + |z.im|) ^ (2 * (r + 1)) := by
    rw [← pow_add]; exact pow_le_pow_right₀ hy hN
  have hp0 : 0 < (1 + |z.im|) ^ 2 := by positivity
  have hpN : 0 < (1 + |z.im|) ^ (2 * (r + 1)) := by positivity
  calc ‖traceCoeff r z‖ * (1 + |z.im|) ^ N
      ≤ (zeroWeight z + zeroWeight (conj z)) * splineConst r / (1 + |z.im|) ^ (2 * (r + 1)) *
          (1 + |z.im|) ^ N := mul_le_mul_of_nonneg_right hz (by positivity)
    _ ≤ splineConst r * ((zeroWeight z + zeroWeight (conj z)) / (1 + |z.im|) ^ 2) := by
        rw [div_mul_eq_mul_div, div_le_iff₀ hpN, mul_div_assoc', div_mul_eq_mul_div,
          le_div_iff₀ hp0]
        have hA := splineConst_nonneg r
        calc (zeroWeight z + zeroWeight (conj z)) * splineConst r * (1 + |z.im|) ^ N *
              (1 + |z.im|) ^ 2
            = (zeroWeight z + zeroWeight (conj z)) * splineConst r *
                ((1 + |z.im|) ^ N * (1 + |z.im|) ^ 2) := by ring
          _ ≤ (zeroWeight z + zeroWeight (conj z)) * splineConst r *
                (1 + |z.im|) ^ (2 * (r + 1)) :=
              mul_le_mul_of_nonneg_left hpow (mul_nonneg hw hA)
          _ = splineConst r * (zeroWeight z + zeroWeight (conj z)) *
                (1 + |z.im|) ^ (2 * (r + 1)) := by ring

end GaloisForLFunctions.SurfaceOfSpecZ
