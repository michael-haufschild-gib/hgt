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
  rw [h2, h1, paperFT_boxTest one_pos, Complex.ofReal_one, one_mul]

/-- **Decay of the box spline.** `|B̂(w)| (1 + |w|)^{r+1} ≤ 2^{r+1} e^{(r+1)|Im w|}`. -/
theorem norm_paperFT_boxSpline_le (r : ℕ) (w : ℂ) :
    ‖paperFT (boxSpline 1 r) w‖ * (1 + ‖w‖) ^ (r + 1) ≤
      2 ^ (r + 1) * Real.exp ((r + 1) * |w.im|) := by
  rw [paperFT_boxSpline_eq, norm_pow, ← mul_pow]
  have h := ZeroConfigurationGeometry.one_add_mul_norm_sincC_le (δ := 1) one_pos w
  simp only [Complex.ofReal_one, one_mul] at h
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
      ring
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
      have hkey : 1 + (z.re * z.re + z.im * z.im) ≤ 5 / 4 * (1 + |z.im|) ^ 2 := by
        nlinarith [abs_nonneg z.im]
      have hge : 1 ≤ 5 / 4 * (1 + |z.im|) ^ 2 / (1 + (z.re * z.re + z.im * z.im)) := by
        rw [le_div_iff₀ hpos2]; linarith
      rw [div_le_iff₀ hpos1]
      calc (zetaZeroConfig.mult (1 / 2 + z) : ℝ) = zetaZeroConfig.mult (1 / 2 + z) * 1 :=
            (mul_one _).symm
        _ ≤ zetaZeroConfig.mult (1 / 2 + z) *
              (5 / 4 * (1 + |z.im|) ^ 2 / (1 + (z.re * z.re + z.im * z.im))) :=
            mul_le_mul_of_nonneg_left hge hm
        _ = _ := by field_simp
    · simp only [zeroWeight, hH, Set.indicator_of_notMem hz, zero_div, mul_zero, le_refl]
  refine Summable.of_nonneg_of_le (fun z => by
      have := zeroWeight_nonneg z; have := zeroWeight_nonneg (conj z); positivity)
    (fun z => ?_) ((hHs.add hHc).mul_left (5 / 4))
  have h1 := hpt z
  have h2 := hpt (conj z)
  rw [Complex.conj_im, abs_neg] at h2
  rw [add_div]
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

/-! ### The Dirichlet series of the traces -/

/-- The trace zeta function at the degrees `nᵏ` with coefficients `c`: `Σ_z c_z ζ(s − kz)`. -/
def traceZetaOf (c : ℂ → ℂ) (k : ℕ) (s : ℂ) : ℂ := ∑' z : ℂ, c z * riemannZeta (s - k * z)

theorem natCast_add_one_cpow_eq (n : ℕ) (w : ℂ) :
    ((n : ℂ) + 1) ^ w = cexp (Real.log (n + 1) * w) := by
  have hpos : (0 : ℝ) < n + 1 := by positivity
  rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast hpos.ne' : ((n : ℂ) + 1) ≠ 0)]
  congr 1
  rw [show ((n : ℂ) + 1) = ((n + 1 : ℝ) : ℂ) by push_cast; ring, ← Complex.ofReal_log hpos.le]

theorem norm_natCast_add_one_cpow (n : ℕ) (w : ℂ) :
    ‖((n : ℂ) + 1) ^ w‖ = ((n : ℝ) + 1) ^ w.re := by
  have hpos : (0 : ℝ) < n + 1 := by positivity
  rw [show ((n : ℂ) + 1) = ((n + 1 : ℝ) : ℂ) by push_cast; ring,
    Complex.norm_cpow_eq_rpow_re_of_pos hpos]

/-- **The traces at the degrees `nᵏ` have the Dirichlet series `Σ_z e_z ζ(s − kz)`.** -/
theorem traceDirichlet_eq {r : ℕ} (hr : 3 ≤ r) (k : ℕ) {s : ℂ} (hs : 1 + k / 2 < s.re) :
    Summable (fun n : ℕ => ((2 * (lagStructure zetaZeroConfig (boxSpline 1 r)
        (k * Real.log (n + 1))).re : ℝ) : ℂ) * ((n : ℂ) + 1) ^ (-s)) ∧
      ∑' n : ℕ, ((2 * (lagStructure zetaZeroConfig (boxSpline 1 r)
        (k * Real.log (n + 1))).re : ℝ) : ℂ) * ((n : ℂ) + 1) ^ (-s) =
        traceZetaOf (traceCoeff r) k s := by
  have hb := contDiff_boxSpline_two hr
  have hbs := boxSpline_support (r := 1) one_pos r
  have hZ := SquareRootThreshold.temperedConfig_zetaZeroConfig
  set e := traceCoeff r with he
  have hE : Summable fun z => ‖e z‖ := by
    have h0 := (two_re_lagStructure_eq zetaZeroConfig hZ hb hbs 0).1.norm
    simp only [Complex.ofReal_zero, mul_zero, Complex.exp_zero, mul_one] at h0
    exact h0
  set σ' := s.re - k / 2 with hσ'
  have hσ'1 : 1 < σ' := by rw [hσ']; linarith
  set f : ℕ → ℂ → ℂ := fun n z => e z * ((n : ℂ) + 1) ^ (-(s - k * z)) with hf
  have hfn : ∀ n z, ‖f n z‖ ≤ ((n : ℝ) + 1) ^ (-σ') * ‖e z‖ := by
    intro n z
    by_cases hz : e z = 0
    · simp [hf, hz]
    have hre : z.re ≤ 1 / 2 := re_le_of_evenCoeff_ne_zero hz
    simp only [hf, norm_mul, norm_natCast_add_one_cpow]
    rw [mul_comm]
    refine mul_le_mul_of_nonneg_right (Real.rpow_le_rpow_of_exponent_le
      (by linarith [Nat.cast_nonneg (α := ℝ) n]) ?_) (norm_nonneg _)
    simp only [Complex.neg_re, Complex.sub_re, Complex.mul_re, Complex.natCast_re,
      Complex.natCast_im, zero_mul, sub_zero]
    rw [hσ']
    have : (k : ℝ) * z.re ≤ k / 2 := by nlinarith [Nat.cast_nonneg (α := ℝ) k]
    linarith
  have hgeom : Summable fun n : ℕ => ((n : ℝ) + 1) ^ (-σ') := by
    have h1 := (summable_nat_add_iff 1).mpr (Real.summable_nat_rpow_inv.mpr hσ'1)
    refine h1.congr fun n => ?_
    push_cast
    rw [Real.rpow_neg (by positivity)]
  have hprod : Summable fun p : ℕ × ℂ => ((p.1 : ℝ) + 1) ^ (-σ') * ‖e p.2‖ :=
    hgeom.mul_of_nonneg hE (fun _ => by positivity) (fun _ => norm_nonneg _)
  have hF : Summable (Function.uncurry f) :=
    Summable.of_norm_bounded hprod fun p => hfn p.1 p.2
  -- the fibres
  have hn : ∀ n : ℕ, ∑' z, f n z = ((2 * (lagStructure zetaZeroConfig (boxSpline 1 r)
      (k * Real.log (n + 1))).re : ℝ) : ℂ) * ((n : ℂ) + 1) ^ (-s) := by
    intro n
    rw [(two_re_lagStructure_eq zetaZeroConfig hZ hb hbs (k * Real.log (n + 1))).2, ← tsum_mul_right]
    refine tsum_congr fun z => ?_
    simp only [hf]
    rw [natCast_add_one_cpow_eq, natCast_add_one_cpow_eq, mul_assoc, ← Complex.exp_add]
    congr 2
    push_cast
    ring
  have hz : ∀ z : ℂ, ∑' n, f n z = e z * riemannZeta (s - k * z) := by
    intro z
    by_cases hz0 : e z = 0
    · simp [hf, hz0]
    have hre : z.re ≤ 1 / 2 := re_le_of_evenCoeff_ne_zero hz0
    have hres : 1 < (s - k * z).re := by
      simp only [Complex.sub_re, Complex.mul_re, Complex.natCast_re, Complex.natCast_im, zero_mul,
        sub_zero]
      have : (k : ℝ) * z.re ≤ k / 2 := by nlinarith [Nat.cast_nonneg (α := ℝ) k]
      linarith
    rw [zeta_eq_tsum_one_div_nat_add_one_cpow hres, ← tsum_mul_left]
    refine tsum_congr fun n => ?_
    simp only [hf]
    rw [Complex.cpow_neg, one_div]
  refine ⟨(hF.prod).congr hn, ?_⟩
  calc ∑' n : ℕ, ((2 * (lagStructure zetaZeroConfig (boxSpline 1 r)
        (k * Real.log (n + 1))).re : ℝ) : ℂ) * ((n : ℂ) + 1) ^ (-s)
      = ∑' n, ∑' z, f n z := tsum_congr fun n => (hn n).symm
    _ = ∑' z, ∑' n, f n z := hF.tsum_comm.symm
    _ = traceZetaOf (traceCoeff r) k s := tsum_congr hz

/-! ### Continuation off the poles -/

theorem abs_re_le_of_traceCoeff_ne_zero {r : ℕ} {z : ℂ} (hz : traceCoeff r z ≠ 0) :
    |z.re| ≤ 1 / 2 := by
  rcases mem_of_evenCoeff_ne_zero hz with h | h
  · obtain ⟨-, h0, h1⟩ := h
    simp at h0 h1
    rw [abs_le]; constructor <;> linarith
  · obtain ⟨-, h0, h1⟩ := h
    simp at h0 h1
    rw [abs_le]; constructor <;> linarith

/-- Finitely many exponents of the trace lie at bounded height. -/
theorem finite_traceCoeff_height (r : ℕ) (B : ℝ) :
    {z : ℂ | traceCoeff r z ≠ 0 ∧ |z.im| ≤ B}.Finite := by
  have h1 := (zetaZeroConfig.finite_window (-B - 1) B).image fun ρ : ℂ => ρ - 1 / 2
  have h2 := (zetaZeroConfig.finite_window (-B - 1) B).image fun ρ : ℂ => conj (ρ - 1 / 2)
  refine (h1.union h2).subset fun z hz => ?_
  obtain ⟨hz0, hzB⟩ := hz
  have hB := abs_le.mp hzB
  rcases mem_of_evenCoeff_ne_zero hz0 with h | h
  · refine Or.inl ⟨1 / 2 + z, ⟨h, ?_, ?_⟩, by ring⟩ <;> simp <;> linarith
  · refine Or.inr ⟨1 / 2 + conj z, ⟨h, ?_, ?_⟩, by simp⟩ <;> simp <;> linarith

/-- **Continuation of the trace zeta function.** Let `|ζ(σ + it)| ≤ C|t|^N` for `|σ| ≤ 3 + k`,
`|t| ≥ 1`, and `N + 2 ≤ 2(r + 1)`. For coefficients `c` dominated by the spline coefficients,
`Σ_z c_z ζ(s − kz)` is holomorphic at every `s₀` with `1 < Re s₀ < 2 + k/2` that is not one of the
poles `1 + kz`, `c_z ≠ 0`. -/
theorem differentiableAt_traceZetaOf {r N k : ℕ} (hr : 3 ≤ r) (hN : N + 2 ≤ 2 * (r + 1))
    (hk : 1 ≤ k) {C : ℝ} (hC0 : 0 ≤ C)
    (hC : ∀ σ t : ℝ, |σ| ≤ 3 + k → 1 ≤ |t| →
      ‖riemannZeta ((σ : ℂ) + (t : ℂ) * I)‖ ≤ C * |t| ^ N)
    {c : ℂ → ℂ} (hc : ∀ z, ‖c z‖ ≤ ‖traceCoeff r z‖)
    {s₀ : ℂ} (hs1 : 1 < s₀.re) (hs2 : s₀.re < 2 + k / 2)
    (hpole : ∀ z, c z ≠ 0 → s₀ ≠ 1 + k * z) :
    DifferentiableAt ℂ (traceZetaOf c k) s₀ := by
  classical
  have hk' : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hsupp : ∀ z, c z ≠ 0 → traceCoeff r z ≠ 0 := fun z hz h =>
    hz (norm_eq_zero.mp (le_antisymm ((hc z).trans (by rw [h, norm_zero])) (norm_nonneg _)))
  have hre : ∀ z, c z ≠ 0 → |z.re| ≤ 1 / 2 := fun z hz =>
    abs_re_le_of_traceCoeff_ne_zero (hsupp z hz)
  -- the poles near the horizontal line of `s₀`
  set F : Set ℂ := {z | c z ≠ 0 ∧ |(k : ℝ) * z.im - s₀.im| ≤ 2} with hFdef
  have hF : F.Finite := by
    refine (finite_traceCoeff_height r (|s₀.im| + 2)).subset fun z hz => ?_
    obtain ⟨hz0, hzim⟩ := hz
    refine ⟨hsupp z hz0, ?_⟩
    have h1 := abs_le.mp hzim
    have h2 := abs_le.mp (le_refl |s₀.im|)
    have hkz : |(k : ℝ) * z.im| ≤ |s₀.im| + 2 := by
      rw [abs_le]; constructor <;> linarith [neg_abs_le s₀.im, le_abs_self s₀.im]
    rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ k)] at hkz
    calc |z.im| ≤ k * |z.im| := le_mul_of_one_le_left (abs_nonneg _) hk'
      _ ≤ _ := hkz
  -- a radius avoiding them
  obtain ⟨δ, hδ0, hδ1, hδF⟩ : ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 ∧ ∀ z ∈ F, δ ≤ ‖s₀ - (1 + k * z)‖ := by
    rcases F.eq_empty_or_nonempty with hFe | hFne
    · exact ⟨1, one_pos, le_rfl, by simp [hFe]⟩
    · obtain ⟨z₁, hz₁, hmin⟩ := hF.toFinset.exists_min_image (fun z => ‖s₀ - (1 + k * z)‖)
        (by simpa using hFne)
      have hz₁' := hF.mem_toFinset.mp hz₁
      refine ⟨min 1 ‖s₀ - (1 + k * z₁)‖,
        lt_min one_pos (norm_pos_iff.mpr (sub_ne_zero.mpr (hpole z₁ hz₁'.1))),
        min_le_left _ _, fun z hz => (min_le_right _ _).trans (hmin z (hF.mem_toFinset.mpr hz))⟩
  set ε := δ / 2 with hε
  have hε0 : 0 < ε := by positivity
  have hεδ : ε ≤ 1 / 2 := by rw [hε]; linarith
  -- on the closed ball no argument `s − kz` meets the pole of `ζ`
  have hfar : ∀ z, c z ≠ 0 → ∀ s ∈ Metric.closedBall s₀ ε, s - k * z ≠ 1 := by
    intro z hz s hs h
    have hs' : ‖s - s₀‖ ≤ ε := by rwa [Metric.mem_closedBall, dist_eq_norm] at hs
    by_cases hzF : z ∈ F
    · have h1 := hδF z hzF
      have h2 : s₀ - (1 + k * z) = s₀ - s := by rw [← h]; ring
      rw [h2, norm_sub_rev] at h1
      linarith
    · have him : s.im = k * z.im := by
        have := congrArg Complex.im h
        simp at this; linarith
      have h3 : |s.im - s₀.im| ≤ ε := (Complex.abs_im_le_norm (s - s₀)).trans (by simpa using hs')
      apply hzF
      refine ⟨hz, ?_⟩
      rw [← him]
      linarith [abs_le.mp h3]
  -- bounds for the finitely many nearby terms
  have hM : ∀ z ∈ F, ∃ M : ℝ, ∀ s ∈ Metric.closedBall s₀ ε, ‖riemannZeta (s - k * z)‖ ≤ M := by
    intro z hz
    have hcont : ContinuousOn (fun s => riemannZeta (s - k * z)) (Metric.closedBall s₀ ε) := by
      intro s hs
      have hd : DifferentiableAt ℂ (fun s => riemannZeta (s - k * z)) s :=
        (differentiableAt_riemannZeta (hfar z hz.1 s hs)).comp s (differentiableAt_id.sub_const _)
      exact hd.continuousAt.continuousWithinAt
    obtain ⟨M, hM⟩ := (isCompact_closedBall s₀ ε).exists_bound_of_continuousOn hcont
    exact ⟨M, hM⟩
  choose! M hMb using hM
  set K₀ : ℝ := |s₀.im| + 1 + k with hK₀
  have hK₀0 : 0 ≤ K₀ := by positivity
  set u : ℂ → ℝ := fun z => ‖c z‖ * (C * K₀ ^ N * (1 + |z.im|) ^ N) +
    (if z ∈ F then ‖c z‖ * |M z| else 0) with hu
  have hus : Summable u := by
    refine Summable.add ?_ ?_
    · refine Summable.of_nonneg_of_le (fun _ => by positivity) (fun z => ?_)
        ((summable_traceCoeff_mul_pow hr hN).mul_left (C * K₀ ^ N))
      calc ‖c z‖ * (C * K₀ ^ N * (1 + |z.im|) ^ N)
          ≤ ‖traceCoeff r z‖ * (C * K₀ ^ N * (1 + |z.im|) ^ N) :=
            mul_le_mul_of_nonneg_right (hc z) (by positivity)
        _ = C * K₀ ^ N * (‖traceCoeff r z‖ * (1 + |z.im|) ^ N) := by ring
    · exact summable_of_ne_finset_zero (s := hF.toFinset) fun z hz => by
        rw [Set.Finite.mem_toFinset] at hz; simp [hz]
  have hdiff : DifferentiableOn ℂ (traceZetaOf c k) (Metric.ball s₀ ε) := by
    unfold traceZetaOf
    refine differentiableOn_tsum_of_summable_norm hus (fun z => ?_) Metric.isOpen_ball
      (fun z s hs => ?_)
    · by_cases hz : c z = 0
      · simp only [hz, zero_mul]; exact differentiableOn_const _
      · intro s hs
        exact ((differentiableAt_riemannZeta (hfar z hz s (Metric.ball_subset_closedBall hs))).comp s
          (differentiableAt_id.sub (differentiableAt_const _))).const_mul _ |>.differentiableWithinAt
    · have hs' := Metric.ball_subset_closedBall hs
      have hsn : ‖s - s₀‖ ≤ ε := by rwa [Metric.mem_closedBall, dist_eq_norm] at hs'
      by_cases hz : c z = 0
      · simp only [hz, zero_mul, norm_zero]
        exact add_nonneg (by positivity) (by split_ifs <;> positivity)
      by_cases hzF : z ∈ F
      · have h1 := hMb z hzF s hs'
        simp only [hu, if_pos hzF, norm_mul]
        have : ‖c z‖ * ‖riemannZeta (s - k * z)‖ ≤ ‖c z‖ * |M z| :=
          mul_le_mul_of_nonneg_left (h1.trans (le_abs_self _)) (norm_nonneg _)
        have h0 : 0 ≤ ‖c z‖ * (C * K₀ ^ N * (1 + |z.im|) ^ N) := by positivity
        linarith
      · -- far from the line of `s₀`: the strip bound
        have hzF' : 2 < |(k : ℝ) * z.im - s₀.im| := by
          by_contra h; exact hzF ⟨hz, not_lt.mp h⟩
        set w := s - k * z with hw
        have hwim : w.im = s.im - k * z.im := by simp [hw]
        have hwre : w.re = s.re - k * z.re := by simp [hw]
        have him : |s.im - s₀.im| ≤ ε := (Complex.abs_im_le_norm (s - s₀)).trans (by simpa using hsn)
        have hre' : |s.re - s₀.re| ≤ ε := (Complex.abs_re_le_norm (s - s₀)).trans (by simpa using hsn)
        have ht : 1 ≤ |w.im| := by
          rw [hwim]
          have := abs_le.mp him
          rcases le_or_gt 0 ((k : ℝ) * z.im - s₀.im) with h | h
          · rw [abs_of_nonneg h] at hzF'
            rw [abs_of_neg (by linarith)]; linarith
          · rw [abs_of_neg h] at hzF'
            rw [abs_of_pos (by linarith)]; linarith
        have hσ : |w.re| ≤ 3 + k := by
          rw [hwre]
          have h1 := abs_le.mp hre'
          have h2 := abs_le.mp (hre z hz)
          rw [abs_le]; constructor <;> nlinarith
        have hbound := hC w.re w.im hσ ht
        rw [Complex.re_add_im] at hbound
        have hwle : |w.im| ≤ K₀ * (1 + |z.im|) := by
          rw [hwim]
          have h1 := abs_le.mp him
          have h2 : |(k : ℝ) * z.im| = k * |z.im| := by
            rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ k)]
          calc |s.im - k * z.im| ≤ |s.im| + |(k : ℝ) * z.im| := abs_sub _ _
            _ ≤ (|s₀.im| + 1) + k * |z.im| := by
                rw [h2]
                have : |s.im| ≤ |s₀.im| + ε := by
                  calc |s.im| = |(s.im - s₀.im) + s₀.im| := by ring_nf
                    _ ≤ |s.im - s₀.im| + |s₀.im| := abs_add_le _ _
                    _ ≤ |s₀.im| + ε := by linarith
                linarith
            _ ≤ K₀ * (1 + |z.im|) := by
                rw [hK₀]; nlinarith [abs_nonneg z.im, abs_nonneg s₀.im]
        have hpow : |w.im| ^ N ≤ (K₀ * (1 + |z.im|)) ^ N :=
          pow_le_pow_left₀ (abs_nonneg _) hwle N
        simp only [hu, if_neg hzF, add_zero, norm_mul]
        calc ‖c z‖ * ‖riemannZeta w‖ ≤ ‖c z‖ * (C * |w.im| ^ N) :=
              mul_le_mul_of_nonneg_left hbound (norm_nonneg _)
          _ ≤ ‖c z‖ * (C * (K₀ * (1 + |z.im|)) ^ N) :=
              mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hpow hC0) (norm_nonneg _)
          _ = ‖c z‖ * (C * K₀ ^ N * (1 + |z.im|) ^ N) := by rw [mul_pow]; ring
  exact hdiff.differentiableAt (Metric.ball_mem_nhds _ hε0)

/-- **Pointwise convergence** of `Σ_z c_z ζ(s − kz)` for `1 < Re s < 2 + k/2`, under the
hypotheses of `differentiableAt_traceZetaOf`. -/
theorem summable_traceZetaOf_terms {r N k : ℕ} (hr : 3 ≤ r) (hN : N + 2 ≤ 2 * (r + 1))
    (hk : 1 ≤ k) {C : ℝ} (hC0 : 0 ≤ C)
    (hC : ∀ σ t : ℝ, |σ| ≤ 3 + k → 1 ≤ |t| →
      ‖riemannZeta ((σ : ℂ) + (t : ℂ) * I)‖ ≤ C * |t| ^ N)
    {c : ℂ → ℂ} (hc : ∀ z, ‖c z‖ ≤ ‖traceCoeff r z‖)
    {s : ℂ} (hs1 : 1 < s.re) (hs2 : s.re < 2 + k / 2) :
    Summable fun z => c z * riemannZeta (s - k * z) := by
  classical
  have hk' : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hsupp : ∀ z, c z ≠ 0 → traceCoeff r z ≠ 0 := fun z hz h =>
    hz (norm_eq_zero.mp (le_antisymm ((hc z).trans (by rw [h, norm_zero])) (norm_nonneg _)))
  set F : Set ℂ := {z | c z ≠ 0 ∧ |(k : ℝ) * z.im - s.im| < 1} with hFdef
  have hF : F.Finite := by
    refine (finite_traceCoeff_height r (|s.im| + 1)).subset fun z hz => ?_
    obtain ⟨hz0, hzim⟩ := hz
    refine ⟨hsupp z hz0, ?_⟩
    have hkz : |(k : ℝ) * z.im| ≤ |s.im| + 1 := by
      have := abs_le.mp hzim.le
      rw [abs_le]; constructor <;> linarith [neg_abs_le s.im, le_abs_self s.im]
    rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ k)] at hkz
    calc |z.im| ≤ k * |z.im| := le_mul_of_one_le_left (abs_nonneg _) hk'
      _ ≤ _ := hkz
  set K₀ : ℝ := |s.im| + k with hK₀
  set u : ℂ → ℝ := fun z => ‖c z‖ * (C * K₀ ^ N * (1 + |z.im|) ^ N) +
    (if z ∈ F then ‖c z * riemannZeta (s - k * z)‖ else 0) with hu
  have hus : Summable u := by
    refine Summable.add ?_ ?_
    · refine Summable.of_nonneg_of_le (fun _ => by positivity) (fun z => ?_)
        ((summable_traceCoeff_mul_pow hr hN).mul_left (C * K₀ ^ N))
      calc ‖c z‖ * (C * K₀ ^ N * (1 + |z.im|) ^ N)
          ≤ ‖traceCoeff r z‖ * (C * K₀ ^ N * (1 + |z.im|) ^ N) :=
            mul_le_mul_of_nonneg_right (hc z) (by positivity)
        _ = C * K₀ ^ N * (‖traceCoeff r z‖ * (1 + |z.im|) ^ N) := by ring
    · exact summable_of_ne_finset_zero (s := hF.toFinset) fun z hz => by
        rw [Set.Finite.mem_toFinset] at hz; simp [hz]
  refine Summable.of_norm_bounded hus fun z => ?_
  by_cases hz : c z = 0
  · simp only [hz, zero_mul, norm_zero]
    exact add_nonneg (by positivity) (by split_ifs <;> positivity)
  by_cases hzF : z ∈ F
  · simp only [hu, if_pos hzF]
    have h0 : 0 ≤ ‖c z‖ * (C * K₀ ^ N * (1 + |z.im|) ^ N) := by positivity
    linarith
  have hzF' : 1 ≤ |(k : ℝ) * z.im - s.im| := by
    by_contra h; exact hzF ⟨hz, not_le.mp h⟩
  set w := s - k * z with hw
  have hwim : w.im = s.im - k * z.im := by simp [hw]
  have hwre : w.re = s.re - k * z.re := by simp [hw]
  have ht : 1 ≤ |w.im| := by rw [hwim, abs_sub_comm]; exact hzF'
  have hσ : |w.re| ≤ 3 + k := by
    rw [hwre]
    have h2 := abs_le.mp (abs_re_le_of_traceCoeff_ne_zero (hsupp z hz))
    rw [abs_le]; constructor <;> nlinarith
  have hbound := hC w.re w.im hσ ht
  rw [Complex.re_add_im] at hbound
  have hwle : |w.im| ≤ K₀ * (1 + |z.im|) := by
    rw [hwim]
    have h2 : |(k : ℝ) * z.im| = k * |z.im| := by
      rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ k)]
    calc |s.im - k * z.im| ≤ |s.im| + |(k : ℝ) * z.im| := abs_sub _ _
      _ = |s.im| + k * |z.im| := by rw [h2]
      _ ≤ K₀ * (1 + |z.im|) := by rw [hK₀]; nlinarith [abs_nonneg z.im, abs_nonneg s.im]
  have hpow : |w.im| ^ N ≤ (K₀ * (1 + |z.im|)) ^ N := pow_le_pow_left₀ (abs_nonneg _) hwle N
  simp only [hu, if_neg hzF, add_zero, norm_mul]
  calc ‖c z‖ * ‖riemannZeta w‖ ≤ ‖c z‖ * (C * |w.im| ^ N) :=
        mul_le_mul_of_nonneg_left hbound (norm_nonneg _)
    _ ≤ ‖c z‖ * (C * (K₀ * (1 + |z.im|)) ^ N) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hpow hC0) (norm_nonneg _)
    _ = ‖c z‖ * (C * K₀ ^ N * (1 + |z.im|) ^ N) := by rw [mul_pow]; ring

end GaloisForLFunctions.SurfaceOfSpecZ



