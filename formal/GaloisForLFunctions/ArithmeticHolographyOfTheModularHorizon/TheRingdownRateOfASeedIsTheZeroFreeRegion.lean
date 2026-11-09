import GaloisForLFunctions.ArithmeticHolographyOfTheModularHorizon.TheDualSideHasNoSign
import GaloisForLFunctions.ArithmeticHolographyOfTheModularHorizon.OneCavityFunctionSeesEveryResonanceThatAPairSees
import GaloisForLFunctions.BlackHoleRingdown.TheHorocycleRateOfTheCuspEnergy
import GaloisForLFunctions.RHTower.InvZetaAbscissaSubpolynomial

/-!
# The ringdown rate of a seed is the zero-free region

For a seed `F` let `P_F(s) = ∫_𝒟 F · (2u − 1) N(u)`, `u = s − ½`, be its polar transform: entire, equal to
`4s(2s − 1)(s − 1) Λ_F(s)` (`polarTransform_eq_mul`), hence **odd under the functional equation**,
`P_F(1 − s) = −P_F(s)` (`polarTransform_one_sub`), and of **polynomial growth** on `−¼ ≤ Re s ≤ 5/4`
(`exists_polarTransform_poly`). By Phragmén–Lindelöf one exponential bound on the line `Re s = 5/4`,

  `|P_F(5/4 + it)| ≤ D (1 + |t|)^N e^{−π|t|}`,

spreads to the whole strip (`exists_polarTransform_decay`). This is the only seed-specific input.

**The rate.** The Mellin transform of the response is `N_F(s)/ξ(2s) = P_F(s)/(2(s − 1)ξ(2s))`
(`mellin_response_eq`), so `a_F − c e^{−y}`, `c = P_F(1)/(2ξ(2)) = (3/π)∫_𝒟 F`, has Mellin transform
`Ψ(w) = N(w + 1)/w`, `N(s) = P_F(s)/(2ξ(2s)) − cΓ(s)` (`mellin_eq_seedRegPart`). If `ξ` has no zeros right of
`Re z = θ` and `1/ζ` grows polynomially there, `Ψ` is regular on `θ/2 − 1 < Re w < ¼`; Mellin inversion and the
contour shift give

  `|a_F(y) − c| ≤ C y^{1 − θ/2 − ε}`   (`norm_response_sub_le_of_zeroFree`),

for a zero-free half-plane `Re z > Θ` the rate `y^{1 − Θ/2 − ε}` (`response_rate_of_zeroFree`), and under RH the
universal rate `y^{3/4 − ε}` (`response_rate_of_riemannHypothesis`). With the every-seed receiver
(`TheModularMapIsPositionRigid.not_rate_of_seen`) this is the two-sided dictionary between ringdown rates and
zero-free regions for every seed whose completed transform decays like `e^{−π|t|}`.
-/

open Complex MeasureTheory Set Filter Topology Asymptotics
open scoped MatrixGroups UpperHalfPlane

noncomputable section

namespace GaloisForLFunctions.ArithmeticHolographyOfTheModularHorizon

open _root_.RHTower GaloisForLFunctions.HTGeometry GaloisForLFunctions.BlackHoleRingdown
open GaloisForLFunctions.HTGeometry.TestFunctionPerron

variable {F : ℍ → ℂ}

/-! ### The polar transform -/

theorem polarTransform_eq_mul {s : ℂ} (h0 : s ≠ 0) (h1 : s ≠ 1 / 2) (h2 : s ≠ 1) :
    polarTransform F s = 4 * s * (2 * s - 1) * (s - 1) * seedTransform F s := by
  rw [polarTransform_eq h2, numeratorTransform_eq_mul_seedTransform h0 h1]; ring

/-- **The polar transform is odd under the functional equation.** -/
theorem polarTransform_one_sub (hF : IsSeed F) (s : ℂ) : polarTransform F (1 - s) = -polarTransform F s := by
  have hd := differentiable_polarTransform hF
  have hdense : Dense (({0, 1 / 2, 1} : Set ℂ)ᶜ) := (Set.toFinite _).countable.dense_compl ℂ
  have h := Continuous.ext_on hdense (f := fun s => polarTransform F (1 - s))
    (g := fun s => -polarTransform F s) (hd.continuous.comp (continuous_const.sub continuous_id))
    hd.continuous.neg (fun s hs => by
      simp only [mem_compl_iff, mem_insert_iff, mem_singleton_iff, not_or] at hs
      obtain ⟨h0, h1, h2⟩ := hs
      show polarTransform F (1 - s) = -polarTransform F s
      rw [polarTransform_eq_mul (fun h => h2 (by linear_combination -h)) (fun h => h1 (by linear_combination -h))
        (fun h => h0 (by linear_combination -h)), seedTransform_one_sub F h0 h1 h2, polarTransform_eq_mul h0 h1 h2]
      ring)
  exact congrFun h s

/-- The polar numerator is a shape `A₁ Y^{½+u} + A₂ Y^{½−u} + A₃ tail`. -/
theorem polarNumerator_eq_shape (u : ℂ) (x Y : ℝ) :
    polarNumerator u x Y = CuspMS.shape (fun u => (2 * u - 1) * xi (1 + 2 * u)) (fun u => (1 + 2 * u) * xi (2 * u))
      (fun u => (2 * u - 1) * ((1 + 2 * u) * (2 * u))) u x Y := by
  unfold polarNumerator CuspMS.shape; ring

/-- **Polynomial growth in the strip**: `|P_F(s)| ≤ K (1 + |Im s|)^N` on `−¼ ≤ Re s ≤ 5/4`. -/
theorem exists_polarTransform_poly (hF : IsSeed F) :
    ∃ K : ℝ, ∃ N : ℕ, 0 ≤ K ∧ ∀ s : ℂ, -1 / 4 ≤ s.re → s.re ≤ 5 / 4 →
      ‖polarTransform F s‖ ≤ K * (1 + |s.im|) ^ N := by
  obtain ⟨Ct, hCt0, hb⟩ := CuspRSV.exists_shape_bound_uniform (R := 3 / 4) (by norm_num)
  set β := (2 : ℝ) ^ (3 / 4 + 1 / 2 : ℝ) + 2 * Ct
  have hβ : 0 ≤ β := by positivity
  obtain ⟨B, hB⟩ := hF.exists_bound_on_fd zero_le_one hβ (a := 3 / 4 + 1 / 2) (by norm_num)
  obtain ⟨Cξ, Nξ, hCξ, hξ⟩ := CuspRSV.exists_xi_bound_wide
  set Kξ := 6 * Cξ * 2 ^ Nξ + 27
  refine ⟨Kξ * max B 0 * (Real.pi / 3), Nξ + 3, by positivity, fun s h1 h2 => ?_⟩
  set u := s - 1 / 2 with hu
  have hure : u.re = s.re - 1 / 2 := by simp [hu]
  have huim : u.im = s.im := by simp [hu]
  have hure' : |u.re| ≤ 3 / 4 := by rw [hure, abs_le]; constructor <;> linarith
  set X := 1 + |s.im|
  have hX : 1 ≤ X := by simp only [X]; linarith [abs_nonneg s.im]
  have hpow : ∀ k : ℕ, k ≤ Nξ + 3 → X ^ k ≤ X ^ (Nξ + 3) := fun k hk => pow_le_pow_right₀ hX hk
  have hlin : ∀ (a : ℝ) (w : ℂ), w.re = a → |a| ≤ 3 → |w.im| = 2 * |s.im| → ‖w‖ ≤ 3 * X := by
    intro a w hw ha him
    refine (Complex.norm_le_abs_re_add_abs_im w).trans ?_
    rw [hw, him]; simp only [X]; linarith
  have hxi : ∀ w : ℂ, -3 / 2 ≤ w.re → w.re ≤ 5 / 2 → |w.im| = 2 * |s.im| →
      ‖xi w‖ ≤ Cξ * 2 ^ Nξ * X ^ Nξ := by
    intro w hw1 hw2 hwim
    have h := hξ w hw1 hw2
    rw [hwim] at h
    calc _ ≤ Cξ * (1 + 2 * |s.im|) ^ Nξ := h
      _ ≤ Cξ * (2 * X) ^ Nξ := by gcongr; simp only [X]; linarith [abs_nonneg s.im]
      _ = Cξ * 2 ^ Nξ * X ^ Nξ := by rw [mul_pow]; ring
  have hx1 := hxi (1 + 2 * u) (by simp [hure]; linarith) (by simp [hure]; linarith) (by simp [huim, abs_mul])
  have hx2 := hxi (2 * u) (by simp [hure]; linarith) (by simp [hure]; linarith) (by simp [huim, abs_mul])
  have hn1 : ‖2 * u - 1‖ ≤ 3 * X := hlin (2 * s.re - 2) _ (by simp [hure]; ring)
    (by rw [abs_le]; constructor <;> linarith) (by simp [huim, abs_mul])
  have hn2 : ‖1 + 2 * u‖ ≤ 3 * X := hlin (2 * s.re) _ (by simp [hure]; ring)
    (by rw [abs_le]; constructor <;> linarith) (by simp [huim, abs_mul])
  have hn3 : ‖2 * u‖ ≤ 3 * X := hlin (2 * s.re - 1) _ (by simp [hure]; ring)
    (by rw [abs_le]; constructor <;> linarith) (by simp [huim, abs_mul])
  have hA : ‖(2 * u - 1) * xi (1 + 2 * u)‖ + ‖(1 + 2 * u) * xi (2 * u)‖ +
      ‖(2 * u - 1) * ((1 + 2 * u) * (2 * u))‖ ≤ Kξ * X ^ (Nξ + 3) := by
    rw [norm_mul (2 * u - 1) (xi (1 + 2 * u)), norm_mul (1 + 2 * u) (xi (2 * u)),
      norm_mul (2 * u - 1) ((1 + 2 * u) * (2 * u)), norm_mul (1 + 2 * u) (2 * u)]
    have e1 : ‖2 * u - 1‖ * ‖xi (1 + 2 * u)‖ ≤ 3 * Cξ * 2 ^ Nξ * X ^ (Nξ + 3) := by
      calc _ ≤ (3 * X) * (Cξ * 2 ^ Nξ * X ^ Nξ) := by gcongr
        _ = 3 * Cξ * 2 ^ Nξ * X ^ (Nξ + 1) := by ring
        _ ≤ 3 * Cξ * 2 ^ Nξ * X ^ (Nξ + 3) :=
            mul_le_mul_of_nonneg_left (hpow (Nξ + 1) (by omega)) (by positivity)
    have e2 : ‖1 + 2 * u‖ * ‖xi (2 * u)‖ ≤ 3 * Cξ * 2 ^ Nξ * X ^ (Nξ + 3) := by
      calc _ ≤ (3 * X) * (Cξ * 2 ^ Nξ * X ^ Nξ) := by gcongr
        _ = 3 * Cξ * 2 ^ Nξ * X ^ (Nξ + 1) := by ring
        _ ≤ 3 * Cξ * 2 ^ Nξ * X ^ (Nξ + 3) :=
            mul_le_mul_of_nonneg_left (hpow (Nξ + 1) (by omega)) (by positivity)
    have e3 : ‖2 * u - 1‖ * (‖1 + 2 * u‖ * ‖2 * u‖) ≤ 27 * X ^ (Nξ + 3) := by
      calc _ ≤ (3 * X) * ((3 * X) * (3 * X)) := by gcongr
        _ = 27 * X ^ 3 := by ring
        _ ≤ 27 * X ^ (Nξ + 3) := mul_le_mul_of_nonneg_left (hpow 3 (by omega)) (by norm_num)
    have : Kξ * X ^ (Nξ + 3) = 3 * Cξ * 2 ^ Nξ * X ^ (Nξ + 3) + 3 * Cξ * 2 ^ Nξ * X ^ (Nξ + 3) +
        27 * X ^ (Nξ + 3) := by simp only [Kξ]; ring
    linarith
  have hfin : (volume : Measure ℍ) ModularGroup.fd < ⊤ := by
    rw [volume_fd_eq]; exact ENNReal.ofReal_lt_top
  have hpt : ∀ z ∈ ModularGroup.fd, ‖F z * polarNumerator u z.re z.im‖ ≤ Kξ * X ^ (Nξ + 3) * max B 0 := by
    intro z hz
    rw [norm_mul, polarNumerator_eq_shape]
    have hs := hb (fun u => (2 * u - 1) * xi (1 + 2 * u)) (fun u => (1 + 2 * u) * xi (2 * u))
      (fun u => (2 * u - 1) * ((1 + 2 * u) * (2 * u))) u z.re z.im hure' (OddCusp.half_lt_im_of_mem_fd hz).le
    have hBz := hB z hz
    have hpos : 0 ≤ z.im ^ (3 / 4 + 1 / 2 : ℝ) + β := by have := z.im_pos; positivity
    calc ‖F z‖ * ‖CuspMS.shape _ _ _ u z.re z.im‖
        ≤ ‖F z‖ * ((‖(2 * u - 1) * xi (1 + 2 * u)‖ + ‖(1 + 2 * u) * xi (2 * u)‖ +
            ‖(2 * u - 1) * ((1 + 2 * u) * (2 * u))‖) * (z.im ^ (3 / 4 + 1 / 2 : ℝ) + β)) :=
          mul_le_mul_of_nonneg_left hs (norm_nonneg _)
      _ ≤ ‖F z‖ * (Kξ * X ^ (Nξ + 3) * (z.im ^ (3 / 4 + 1 / 2 : ℝ) + β)) := by gcongr
      _ = Kξ * X ^ (Nξ + 3) * (‖F z‖ * (1 * z.im ^ (3 / 4 + 1 / 2 : ℝ) + β)) := by ring
      _ ≤ Kξ * X ^ (Nξ + 3) * max B 0 := by gcongr; exact hBz.trans (le_max_left _ _)
  have h := norm_setIntegral_le_of_norm_le_const hfin hpt
  rw [volume_real_fd] at h
  unfold polarTransform
  calc _ ≤ Kξ * X ^ (Nξ + 3) * max B 0 * (Real.pi / 3) := h
    _ = Kξ * max B 0 * (Real.pi / 3) * X ^ (Nξ + 3) := by ring

/-- **Phragmén–Lindelöf.** An exponential bound on `Re s = 5/4` spreads to the whole strip `−¼ ≤ Re s ≤ 5/4`. -/
theorem exists_polarTransform_decay (hF : IsSeed F)
    (hright : ∃ D : ℝ, ∃ N : ℕ, 0 ≤ D ∧ ∀ s : ℂ, s.re = 5 / 4 → 1 ≤ |s.im| →
      ‖polarTransform F s‖ ≤ D * (1 + |s.im|) ^ N * Real.exp (-(Real.pi * |s.im|))) :
    ∃ C : ℝ, ∃ N : ℕ, 0 ≤ C ∧ ∀ s : ℂ, -1 / 4 ≤ s.re → s.re ≤ 5 / 4 →
      ‖polarTransform F s‖ ≤ C * (1 + |s.im|) ^ N * Real.exp (-(Real.pi * |s.im|)) := by
  have hd := differentiable_polarTransform hF
  obtain ⟨K, Np, hK, hpoly⟩ := exists_polarTransform_poly hF
  obtain ⟨D, Nd, hD, hright⟩ := hright
  have hbox : IsCompact (Icc (-1 / 4 : ℝ) (5 / 4) ×ℂ Icc (-1 : ℝ) 1) :=
    isCompact_Icc.reProdIm isCompact_Icc
  obtain ⟨B₀, hB₀⟩ := hbox.exists_bound_of_continuousOn hd.continuous.continuousOn
  have hB₀0 : 0 ≤ B₀ := (norm_nonneg _).trans (hB₀ 0 (by rw [mem_reProdIm]; norm_num))
  set D' := D + B₀ * Real.exp Real.pi with hD'
  have hD'0 : 0 ≤ D' := by positivity
  have hR : ∀ s : ℂ, s.re = 5 / 4 →
      ‖polarTransform F s‖ ≤ D' * (1 + |s.im|) ^ Nd * Real.exp (-(Real.pi * |s.im|)) := by
    intro s hs
    have hX : 1 ≤ (1 + |s.im|) ^ Nd := one_le_pow₀ (by linarith [abs_nonneg s.im])
    rcases le_or_gt 1 |s.im| with ht | ht
    · calc _ ≤ D * (1 + |s.im|) ^ Nd * Real.exp (-(Real.pi * |s.im|)) := hright s hs ht
        _ ≤ D' * (1 + |s.im|) ^ Nd * Real.exp (-(Real.pi * |s.im|)) := by
            gcongr
            have : 0 ≤ B₀ * Real.exp Real.pi := by positivity
            linarith
    · have hmem : s ∈ Icc (-1 / 4 : ℝ) (5 / 4) ×ℂ Icc (-1 : ℝ) 1 := by
        rw [mem_reProdIm, hs]
        exact ⟨⟨by norm_num, le_rfl⟩, ⟨by linarith [neg_abs_le s.im], by linarith [le_abs_self s.im]⟩⟩
      have he : 1 ≤ Real.exp Real.pi * Real.exp (-(Real.pi * |s.im|)) := by
        rw [← Real.exp_add]; exact Real.one_le_exp (by nlinarith [Real.pi_pos])
      have hE0 : 0 ≤ Real.exp (-(Real.pi * |s.im|)) := (Real.exp_pos _).le
      calc ‖polarTransform F s‖ ≤ B₀ := hB₀ s hmem
        _ ≤ B₀ * Real.exp Real.pi * Real.exp (-(Real.pi * |s.im|)) := by nlinarith
        _ ≤ D' * Real.exp (-(Real.pi * |s.im|)) := by gcongr; linarith
        _ ≤ D' * (1 + |s.im|) ^ Nd * Real.exp (-(Real.pi * |s.im|)) := by
            have : 0 ≤ D' * Real.exp (-(Real.pi * |s.im|)) := by positivity
            nlinarith
  have hL : ∀ s : ℂ, s.re = -1 / 4 →
      ‖polarTransform F s‖ ≤ D' * (1 + |s.im|) ^ Nd * Real.exp (-(Real.pi * |s.im|)) := by
    intro s hs
    have h := hR (1 - s) (by simp [hs]; norm_num)
    rw [polarTransform_one_sub hF, norm_neg] at h
    have him : |(1 - s).im| = |s.im| := by simp
    rwa [him] at h
  have hz3 : ∀ z : ℂ, -1 / 4 ≤ z.re → z + 3 ≠ 0 := fun z hz h => by
    have := congrArg Complex.re h; simp at this; linarith
  have h3' : ∀ z : ℂ, -1 / 4 ≤ z.re → 1 + |z.im| ≤ 2 * ‖z + 3‖ := fun z hz => by
    have h1 := Complex.abs_re_le_norm (z + 3)
    have h2 := Complex.abs_im_le_norm (z + 3)
    have hre : (z + 3).re = z.re + 3 := by simp
    have him : (z + 3).im = z.im := by simp
    rw [hre, abs_of_pos (by linarith)] at h1
    rw [him] at h2
    linarith
  have key : ∀ ε : ℝ, |ε| = 1 → ∀ s : ℂ, -1 / 4 ≤ s.re → s.re ≤ 5 / 4 →
      ‖polarTransform F s‖ * Real.exp (ε * Real.pi * s.im) ≤ D' * 2 ^ Nd * ‖s + 3‖ ^ Nd := by
    intro ε hε s hs1 hs2
    set G : ℂ → ℂ := fun z => polarTransform F z * Complex.exp (-((ε * Real.pi : ℝ) * I) * z) / (z + 3) ^ Nd
      with hG
    have hnG : ∀ z : ℂ, -1 / 4 ≤ z.re →
        ‖G z‖ = ‖polarTransform F z‖ * Real.exp (ε * Real.pi * z.im) / ‖z + 3‖ ^ Nd := by
      intro z hz
      simp only [hG, norm_div, norm_mul, norm_pow, Complex.norm_exp]
      congr 3
      simp [Complex.mul_re]
    have hexp : ∀ y : ℝ, Real.exp (ε * Real.pi * y) ≤ Real.exp (Real.pi * |y|) := fun y => by
      apply Real.exp_le_exp.2
      calc ε * Real.pi * y ≤ |ε * Real.pi * y| := le_abs_self _
        _ = Real.pi * |y| := by rw [abs_mul, abs_mul, hε, abs_of_pos Real.pi_pos, one_mul]
    have hbd : ∀ z : ℂ, (z.re = -1 / 4 ∨ z.re = 5 / 4) → ‖G z‖ ≤ D' * 2 ^ Nd := by
      intro z hz
      have hzre : -1 / 4 ≤ z.re := by
        rcases hz with h | h
        · exact h.symm.le
        · rw [h]; norm_num
      have hP : ‖polarTransform F z‖ ≤ D' * (1 + |z.im|) ^ Nd * Real.exp (-(Real.pi * |z.im|)) := by
        rcases hz with h | h
        · exact hL z h
        · exact hR z h
      have hpos : 0 < ‖z + 3‖ ^ Nd := pow_pos (norm_pos_iff.2 (hz3 z hzre)) _
      rw [hnG z hzre, div_le_iff₀ hpos]
      have h1 : Real.exp (-(Real.pi * |z.im|)) * Real.exp (ε * Real.pi * z.im) ≤ 1 := by
        rw [← Real.exp_add]; apply Real.exp_le_one_iff.2; linarith [hexp z.im, Real.exp_le_exp.1 (hexp z.im)]
      have h2 : (1 + |z.im|) ^ Nd ≤ (2 * ‖z + 3‖) ^ Nd :=
        pow_le_pow_left₀ (by linarith [abs_nonneg z.im]) (h3' z hzre) _
      calc ‖polarTransform F z‖ * Real.exp (ε * Real.pi * z.im) ≤
            D' * (1 + |z.im|) ^ Nd * Real.exp (-(Real.pi * |z.im|)) * Real.exp (ε * Real.pi * z.im) :=
            mul_le_mul_of_nonneg_right hP (Real.exp_pos _).le
        _ = D' * (1 + |z.im|) ^ Nd * (Real.exp (-(Real.pi * |z.im|)) * Real.exp (ε * Real.pi * z.im)) := by
            ring
        _ ≤ D' * (1 + |z.im|) ^ Nd * 1 := by gcongr
        _ ≤ D' * (2 * ‖z + 3‖) ^ Nd := by rw [mul_one]; gcongr
        _ = D' * 2 ^ Nd * ‖z + 3‖ ^ Nd := by rw [mul_pow]; ring
    have hPL := CuspRSV.norm_le_of_strip (f := G) (a := -1 / 4) (b := 5 / 4) (C := D' * 2 ^ Nd) (K := K)
      (L := Np + Real.pi) (by norm_num)
      (fun z hz1 _ => ((hd z).mul ((differentiable_exp.comp (differentiable_id.const_mul _)) z)).div
        ((differentiable_id.add_const _).pow Nd z) (pow_ne_zero _ (hz3 z hz1)))
      (fun z hz1 hz2 => by
        have hpos : 1 ≤ ‖z + 3‖ ^ Nd := one_le_pow₀ (by
          have h := Complex.abs_re_le_norm (z + 3)
          have hre : (z + 3).re = z.re + 3 := by simp
          rw [hre, abs_of_pos (by linarith)] at h
          linarith)
        rw [hnG z hz1, div_le_iff₀ (by linarith)]
        have hP := hpoly z hz1 hz2
        have hy : (1 + |z.im|) ^ Np ≤ Real.exp (Np * |z.im|) := by
          calc (1 + |z.im|) ^ Np ≤ (Real.exp |z.im|) ^ Np :=
                pow_le_pow_left₀ (by linarith [abs_nonneg z.im]) (by linarith [Real.add_one_le_exp |z.im|]) _
            _ = Real.exp (Np * |z.im|) := by rw [← Real.exp_nat_mul]
        have he : Real.exp (Np * |z.im|) * Real.exp (Real.pi * |z.im|) =
            Real.exp ((Np + Real.pi) * |z.im|) := by rw [← Real.exp_add]; ring_nf
        calc ‖polarTransform F z‖ * Real.exp (ε * Real.pi * z.im) ≤
              K * (1 + |z.im|) ^ Np * Real.exp (Real.pi * |z.im|) :=
              mul_le_mul hP (hexp z.im) (Real.exp_pos _).le (by positivity)
          _ ≤ K * Real.exp (Np * |z.im|) * Real.exp (Real.pi * |z.im|) := by gcongr
          _ = K * Real.exp ((Np + Real.pi) * |z.im|) := by rw [mul_assoc, he]
          _ ≤ K * Real.exp ((Np + Real.pi) * |z.im|) * ‖z + 3‖ ^ Nd :=
              le_mul_of_one_le_right (by positivity) hpos)
      (fun z hz => hbd z (Or.inl hz)) (fun z hz => hbd z (Or.inr hz)) hs1 hs2
    rw [hnG s hs1, div_le_iff₀ (pow_pos (norm_pos_iff.2 (hz3 s hs1)) _)] at hPL
    exact hPL
  refine ⟨D' * 2 ^ Nd * (17 / 4) ^ Nd, Nd, by positivity, fun s hs1 hs2 => ?_⟩
  have hs3 : ‖s + 3‖ ≤ 17 / 4 * (1 + |s.im|) := by
    refine (Complex.norm_le_abs_re_add_abs_im _).trans ?_
    have hre : (s + 3).re = s.re + 3 := by simp
    have him : (s + 3).im = s.im := by simp
    rw [hre, him, abs_of_pos (by linarith)]
    nlinarith [abs_nonneg s.im]
  have hs3' : ‖s + 3‖ ^ Nd ≤ (17 / 4) ^ Nd * (1 + |s.im|) ^ Nd := by
    rw [← mul_pow]; exact pow_le_pow_left₀ (norm_nonneg _) hs3 _
  have hε : |(if 0 ≤ s.im then (1 : ℝ) else -1)| = 1 := by split_ifs <;> norm_num
  have h := key _ hε s hs1 hs2
  have hsign : (if 0 ≤ s.im then (1 : ℝ) else -1) * Real.pi * s.im = Real.pi * |s.im| := by
    split_ifs with h0
    · rw [abs_of_nonneg h0]; ring
    · rw [abs_of_neg (not_le.1 h0)]; ring
  rw [hsign] at h
  have hinv : Real.exp (-(Real.pi * |s.im|)) * Real.exp (Real.pi * |s.im|) = 1 := by
    rw [← Real.exp_add]; simp
  calc ‖polarTransform F s‖ =
        ‖polarTransform F s‖ * Real.exp (Real.pi * |s.im|) * Real.exp (-(Real.pi * |s.im|)) := by
        rw [mul_assoc, mul_comm (Real.exp _), hinv, mul_one]
    _ ≤ D' * 2 ^ Nd * ‖s + 3‖ ^ Nd * Real.exp (-(Real.pi * |s.im|)) :=
        mul_le_mul_of_nonneg_right h (Real.exp_pos _).le
    _ ≤ D' * 2 ^ Nd * ((17 / 4) ^ Nd * (1 + |s.im|) ^ Nd) * Real.exp (-(Real.pi * |s.im|)) := by
        gcongr
    _ = D' * 2 ^ Nd * (17 / 4) ^ Nd * (1 + |s.im|) ^ Nd * Real.exp (-(Real.pi * |s.im|)) := by ring

/-! ### The regular part of the Mellin transform -/

/-- `c = P_F(1)/(2ξ(2))`, the limit of the response. -/
def seedRateConst (F : ℍ → ℂ) : ℂ := polarTransform F 1 / (2 * xi 2)

/-- `N(s) = P_F(s)/(2ξ(2s)) − cΓ(s)`. -/
def seedPoleNum (F : ℍ → ℂ) (s : ℂ) : ℂ := polarTransform F s / (2 * xi (2 * s)) - seedRateConst F * Gamma s

/-- `Ψ(w) = N(w + 1)/w`, regularised at `w = 0`. -/
def seedRegPart (F : ℍ → ℂ) (w : ℂ) : ℂ := dslope (seedPoleNum F) 1 (w + 1)

theorem seedPoleNum_one : seedPoleNum F 1 = 0 := by
  simp [seedPoleNum, seedRateConst, Complex.Gamma_one]

theorem seedRegPart_eq {w : ℂ} (hw : w ≠ 0) : seedRegPart F w = seedPoleNum F (w + 1) / w := by
  rw [seedRegPart, dslope_of_ne _ (by simpa using hw), slope_def_field, seedPoleNum_one, sub_zero,
    add_sub_cancel_right]

theorem differentiableOn_seedPoleNum (hF : IsSeed F) {θ : ℝ} (hθ : 0 ≤ θ)
    (hZ : ∀ z : ℂ, θ < z.re → xi z ≠ 0) :
    DifferentiableOn ℂ (seedPoleNum F) {s : ℂ | θ / 2 < s.re} := by
  intro s hs
  have hs' : θ / 2 < s.re := hs
  have hx : 2 * xi (2 * s) ≠ 0 := mul_ne_zero two_ne_zero (hZ _ (by simp; linarith))
  have hΓ : DifferentiableAt ℂ Gamma s := by
    refine Complex.differentiableAt_Gamma s fun m hm => ?_
    have := congrArg Complex.re hm
    simp at this
    have : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    linarith
  have hxi : DifferentiableAt ℂ (fun s : ℂ => 2 * xi (2 * s)) s :=
    ((xi_differentiable.comp (by fun_prop : Differentiable ℂ fun v : ℂ => 2 * v)) s).const_mul 2
  refine DifferentiableAt.differentiableWithinAt ?_
  unfold seedPoleNum
  exact ((differentiable_polarTransform hF s).div hxi hx).sub (hΓ.const_mul _)

theorem differentiableAt_seedRegPart (hF : IsSeed F) {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ < 2)
    (hZ : ∀ z : ℂ, θ < z.re → xi z ≠ 0) {w : ℂ} (hw : θ / 2 - 1 < w.re) :
    DifferentiableAt ℂ (seedRegPart F) w := by
  have hU : IsOpen {s : ℂ | θ / 2 < s.re} := isOpen_lt continuous_const Complex.continuous_re
  have h1 : {s : ℂ | θ / 2 < s.re} ∈ 𝓝 (1 : ℂ) := hU.mem_nhds (by simp; linarith)
  have hd := (Complex.differentiableOn_dslope h1).2 (differentiableOn_seedPoleNum hF hθ0 hZ)
  have hw1 : w + 1 ∈ {s : ℂ | θ / 2 < s.re} := by simp; linarith
  have hdw := (hd _ hw1).differentiableAt (hU.mem_nhds hw1)
  exact hdw.comp w (differentiableAt_id.add_const 1)

/-- **The Mellin transform of `a_F − c e^{−y}` is `Ψ`** on `Re w > 0`. -/
theorem mellin_eq_seedRegPart (hF : IsSeed F) {w : ℂ} (hw : 0 < w.re) :
    mellin (fun y => response F y - seedRateConst F * ((Real.exp (-y) : ℝ) : ℂ)) w = seedRegPart F w := by
  have hs : 1 < (w + 1).re := by simp; linarith
  have hw0 : w ≠ 0 := fun h => by rw [h] at hw; simp at hw
  have hs2 : w + 1 ≠ 1 := fun h => hw0 (by linear_combination h)
  have hA := mellinConvergent_response hF hs
  rw [add_sub_cancel_right] at hA
  have hE := (BlackHoleRingdown.mellinConvergent_exp_neg hw).const_smul (seedRateConst F)
  have hsplit : mellin (fun y => response F y - seedRateConst F * ((Real.exp (-y) : ℝ) : ℂ)) w =
      mellin (response F) w - seedRateConst F * mellin (fun y : ℝ => ((Real.exp (-y) : ℝ) : ℂ)) w := by
    rw [mellin, mellin, mellin, ← integral_const_mul, ← integral_sub hA]
    · refine setIntegral_congr_fun measurableSet_Ioi fun y _ => ?_
      simp only [smul_eq_mul]
      ring
    · refine hE.congr_fun (fun y _ => ?_) measurableSet_Ioi
      simp only [smul_eq_mul]
      ring
  have hM := mellin_response_eq hF hs
  rw [add_sub_cancel_right] at hM
  have hx : xi (2 * (w + 1)) ≠ 0 := BlackHoleRingdown.xi_ne_zero_of_one_lt_re (by simp; linarith)
  rw [hsplit, hM, BlackHoleRingdown.mellin_exp_neg hw, seedRegPart_eq hw0, seedPoleNum, polarTransform_eq hs2,
    Complex.Gamma_add_one w hw0]
  field_simp
  ring

/-! ### Regularity of `Ψ` -/

/-- **`Ψ` is regular** on `θ/2 − 1 < Re w < ¼`: holomorphic, and decaying faster than every power of `|Im w|`
on closed substrips. -/
theorem mellinRegularStrip_seedRegPart (hF : IsSeed F)
    (hdecay : ∃ C : ℝ, ∃ N : ℕ, 0 ≤ C ∧ ∀ s : ℂ, -1 / 4 ≤ s.re → s.re ≤ 5 / 4 →
      ‖polarTransform F s‖ ≤ C * (1 + |s.im|) ^ N * Real.exp (-(Real.pi * |s.im|)))
    {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) (hZ : ∀ z : ℂ, θ < z.re → xi z ≠ 0)
    (hP : ∀ δ : ℝ, 0 < δ → ∀ d : ℝ, ∃ K : ℝ, ∃ N : ℕ, 0 ≤ K ∧ ∀ z : ℂ, θ + δ ≤ z.re →
      z.re ≤ d → 2 ≤ |z.im| → ‖(riemannZeta z)⁻¹‖ ≤ K * |z.im| ^ N) :
    MellinRegularStrip (seedRegPart F) (θ / 2 - 1) (1 / 4) := by
  refine ⟨fun w hw _ => differentiableAt_seedRegPart hF hθ0 (by linarith) hZ hw,
    fun a' b' ha' hb' K => ?_⟩
  have hbox : IsCompact (Icc a' b' ×ℂ Icc (-1 : ℝ) 1) := isCompact_Icc.reProdIm isCompact_Icc
  obtain ⟨B, hB⟩ := hbox.exists_bound_of_continuousOn (f := seedRegPart F) (fun w hw => by
    have hw' : a' ≤ w.re := hw.1.1
    exact (differentiableAt_seedRegPart hF hθ0 (by linarith) hZ (by linarith)).continuousAt
      |>.continuousWithinAt)
  obtain ⟨CP, NP, hCP, hPb⟩ := hdecay
  obtain ⟨CΓi, hCΓi, hΓi⟩ := CuspHRate.exists_norm_inv_Gamma_le (a := a' + 1) (by linarith)
  obtain ⟨CΓ, NΓ, hCΓ, hΓ⟩ := GaloisForLFunctions.HTGeometry.exists_sharp_bound_norm_Gamma_strip
    (a' + 1) (b' + 1)
  obtain ⟨Kz, Nz, hKz, hz⟩ := hP (2 * (a' + 1) - θ) (by linarith) (2 * (b' + 1))
  set c := seedRateConst F
  set N₁ := NP + 1 + Nz
  set C₁ := CP * Real.pi ^ 2 * CΓi * (Kz * 2 ^ Nz)
  set Nn := N₁ + NΓ
  set Cn := C₁ + ‖c‖ * CΓ
  obtain ⟨Ce, hCe, hCe'⟩ := exists_pow_mul_exp_le Nn K
  have hpi2 : 1 ≤ Real.pi ^ 2 := by nlinarith [Real.pi_gt_three]
  have hN : ∀ s : ℂ, a' + 1 ≤ s.re → s.re ≤ b' + 1 → 1 ≤ |s.im| →
      ‖seedPoleNum F s‖ ≤ Cn * (1 + |s.im|) ^ Nn * Real.exp (-(Real.pi * |s.im| / 2)) := by
    intro s h1 h2 ht
    have hs0 : 0 < s.re := by linarith
    have hs1 : s ≠ 1 / 2 := fun h => by rw [h] at ht; norm_num at ht
    set T := s.im
    set X := 1 + |T|
    have hX : 1 ≤ X := by simp only [X]; linarith [abs_nonneg T]
    have hsn : 1 ≤ ‖s‖ := le_trans ht (Complex.abs_im_le_norm s)
    have h2sn : 1 ≤ ‖2 * s - 1‖ := by
      have := Complex.abs_im_le_norm (2 * s - 1)
      have him : (2 * s - 1).im = 2 * T := by simp [T]
      rw [him, abs_mul, abs_two] at this
      linarith
    have hpis : ‖(Real.pi : ℂ) ^ s‖ ≤ Real.pi ^ 2 := by
      rw [norm_cpow_eq_rpow_re_of_pos Real.pi_pos]
      calc Real.pi ^ s.re ≤ Real.pi ^ (2 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le (by linarith [Real.pi_gt_three]) (by linarith)
        _ = Real.pi ^ 2 := by norm_num
    have hζ : ‖(riemannZeta (2 * s))⁻¹‖ ≤ Kz * 2 ^ Nz * X ^ Nz := by
      have h := hz (2 * s) (by simp; linarith) (by simp; linarith) (by simp [abs_mul]; linarith)
      have him : |(2 * s).im| = 2 * |T| := by simp [abs_mul, T]
      rw [him] at h
      calc _ ≤ Kz * (2 * |T|) ^ Nz := h
        _ ≤ Kz * (2 * X) ^ Nz := by gcongr; simp only [X]; linarith
        _ = Kz * 2 ^ Nz * X ^ Nz := by rw [mul_pow]; ring
    have hP' := hPb s (by linarith) (by linarith)
    have hΓi' := hΓi s h1 (by linarith) ht
    have hΓ' := hΓ s h1 h2 ht
    have hxi : ‖(xi (2 * s))⁻¹‖ ≤ Real.pi ^ 2 * (CΓi * X * Real.exp (Real.pi * |T| / 2)) *
        (Kz * 2 ^ Nz * X ^ Nz) := by
      rw [CuspHRate.xi_two_mul_eq_gamma hs0 hs1, mul_inv, mul_inv, mul_inv, mul_inv, norm_mul, norm_mul,
        norm_mul, norm_mul, ← cpow_neg, neg_neg]
      have h1' : ‖s⁻¹‖ ≤ 1 := by rw [norm_inv]; exact inv_le_one_of_one_le₀ hsn
      have h2' : ‖(2 * s - 1)⁻¹‖ ≤ 1 := by rw [norm_inv]; exact inv_le_one_of_one_le₀ h2sn
      calc ‖s⁻¹‖ * ‖(2 * s - 1)⁻¹‖ * ‖(Real.pi : ℂ) ^ s‖ * ‖(Gamma s)⁻¹‖ * ‖(riemannZeta (2 * s))⁻¹‖
          ≤ 1 * 1 * Real.pi ^ 2 * (CΓi * X * Real.exp (Real.pi * |T| / 2)) * (Kz * 2 ^ Nz * X ^ Nz) := by
            gcongr
        _ = _ := by ring
    have hT0 : |T| ^ NΓ ≤ X ^ NΓ := pow_le_pow_left₀ (abs_nonneg _) (by simp only [X]; linarith) _
    have hXN : ∀ k : ℕ, k ≤ Nn → X ^ k ≤ X ^ Nn := fun k hk => pow_le_pow_right₀ hX hk
    have he : Real.exp (-(Real.pi * |T|)) * Real.exp (Real.pi * |T| / 2) =
        Real.exp (-(Real.pi * |T| / 2)) := by rw [← Real.exp_add]; ring_nf
    have hhalf : ‖polarTransform F s / (2 * xi (2 * s))‖ ≤ ‖polarTransform F s‖ * ‖(xi (2 * s))⁻¹‖ := by
      rw [div_eq_mul_inv, mul_inv, norm_mul, norm_mul, norm_inv, show ‖(2 : ℂ)‖ = 2 by norm_num]
      have := norm_nonneg (polarTransform F s)
      have := norm_nonneg (xi (2 * s))⁻¹
      nlinarith
    unfold seedPoleNum
    calc ‖polarTransform F s / (2 * xi (2 * s)) - c * Gamma s‖
        ≤ ‖polarTransform F s / (2 * xi (2 * s))‖ + ‖c * Gamma s‖ := norm_sub_le _ _
      _ ≤ ‖polarTransform F s‖ * ‖(xi (2 * s))⁻¹‖ + ‖c‖ * ‖Gamma s‖ := by
          rw [norm_mul c]; linarith
      _ ≤ (CP * X ^ NP * Real.exp (-(Real.pi * |T|))) *
            (Real.pi ^ 2 * (CΓi * X * Real.exp (Real.pi * |T| / 2)) * (Kz * 2 ^ Nz * X ^ Nz)) +
          ‖c‖ * (CΓ * |T| ^ NΓ * Real.exp (-(Real.pi * |T| / 2))) := by gcongr
      _ = C₁ * X ^ N₁ * (Real.exp (-(Real.pi * |T|)) * Real.exp (Real.pi * |T| / 2)) +
          ‖c‖ * CΓ * |T| ^ NΓ * Real.exp (-(Real.pi * |T| / 2)) := by
          simp only [C₁, N₁]; ring
      _ ≤ C₁ * X ^ Nn * Real.exp (-(Real.pi * |T| / 2)) +
          ‖c‖ * CΓ * X ^ Nn * Real.exp (-(Real.pi * |T| / 2)) := by
          rw [he]
          gcongr
          · exact Nat.le_add_right _ _
          · exact hT0.trans (hXN NΓ (Nat.le_add_left _ _))
      _ = Cn * X ^ Nn * Real.exp (-(Real.pi * |T| / 2)) := by simp only [Cn]; ring
  refine ⟨max (B * 2 ^ K) (Cn * 2 ^ Nn * Ce), fun w h1 h2 => ?_⟩
  have hden : 0 < (1 + w.im ^ 2) ^ K := by positivity
  rcases le_or_gt |w.im| 1 with ht | ht
  · have hmem : w ∈ Icc a' b' ×ℂ Icc (-1 : ℝ) 1 := by
      rw [mem_reProdIm]
      exact ⟨⟨h1, h2⟩, ⟨by linarith [neg_abs_le w.im], by linarith [le_abs_self w.im]⟩⟩
    have hpow : (1 + w.im ^ 2) ^ K ≤ 2 ^ K := by
      apply pow_le_pow_left₀ (by positivity)
      nlinarith [abs_nonneg w.im, sq_abs w.im]
    rw [le_div_iff₀ hden]
    calc ‖seedRegPart F w‖ * (1 + w.im ^ 2) ^ K ≤ B * 2 ^ K := by
          gcongr
          · exact (norm_nonneg _).trans (hB w hmem)
          · exact hB w hmem
      _ ≤ max (B * 2 ^ K) (Cn * 2 ^ Nn * Ce) := le_max_left _ _
  · have hw0 : w ≠ 0 := fun h => by rw [h] at ht; simp at ht; linarith
    have hwn : 1 ≤ ‖w‖ := le_trans ht.le (Complex.abs_im_le_norm w)
    have hNb := hN (w + 1) (by simp; linarith) (by simp; linarith) (by simpa using ht.le)
    simp only [add_im, one_im, add_zero] at hNb
    have hX : 1 + |w.im| ≤ 2 * |w.im| := by linarith
    have hCn : 0 ≤ Cn := by positivity
    have hstep : (1 + |w.im|) ^ Nn ≤ 2 ^ Nn * |w.im| ^ Nn := by
      rw [← mul_pow]; exact pow_le_pow_left₀ (by positivity) hX _
    have hfin := hCe' w.im ht.le
    rw [seedRegPart_eq hw0, norm_div]
    calc ‖seedPoleNum F (w + 1)‖ / ‖w‖ ≤ ‖seedPoleNum F (w + 1)‖ := div_le_self (norm_nonneg _) hwn
      _ ≤ Cn * (1 + |w.im|) ^ Nn * Real.exp (-(Real.pi * |w.im| / 2)) := hNb
      _ ≤ Cn * (2 ^ Nn * |w.im| ^ Nn) * Real.exp (-(Real.pi * |w.im| / 2)) := by gcongr
      _ = Cn * 2 ^ Nn * (|w.im| ^ Nn * Real.exp (-(Real.pi * |w.im| / 2))) := by ring
      _ ≤ Cn * 2 ^ Nn * (Ce / (1 + w.im ^ 2) ^ K) := by gcongr
      _ = Cn * 2 ^ Nn * Ce / (1 + w.im ^ 2) ^ K := by ring
      _ ≤ max (B * 2 ^ K) (Cn * 2 ^ Nn * Ce) / (1 + w.im ^ 2) ^ K := by
          gcongr; exact le_max_right _ _

/-! ### Mellin inversion and the contour shift -/

/-- **The rate from a zero-free half-plane.** For a seed whose polar transform decays like `e^{−π|t|}` on the
strip: if `ξ` has no zeros right of `Re z = θ` and `1/ζ` grows at most polynomially on every strip
`Re z ≥ θ + δ`, then `|a_F(y) − c| ≤ C y^{1 − θ/2 − ε}` on `(0, 1]`. -/
theorem norm_response_sub_le_of_zeroFree (hF : IsSeed F)
    (hdecay : ∃ C : ℝ, ∃ N : ℕ, 0 ≤ C ∧ ∀ s : ℂ, -1 / 4 ≤ s.re → s.re ≤ 5 / 4 →
      ‖polarTransform F s‖ ≤ C * (1 + |s.im|) ^ N * Real.exp (-(Real.pi * |s.im|)))
    {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) (hZ : ∀ z : ℂ, θ < z.re → xi z ≠ 0)
    (hP : ∀ δ : ℝ, 0 < δ → ∀ d : ℝ, ∃ K : ℝ, ∃ N : ℕ, 0 ≤ K ∧ ∀ z : ℂ, θ + δ ≤ z.re →
      z.re ≤ d → 2 ≤ |z.im| → ‖(riemannZeta z)⁻¹‖ ≤ K * |z.im| ^ N)
    {ε : ℝ} (hε : 0 < ε) (hε1 : ε < 1 / 2) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ y : ℝ, 0 < y → y ≤ 1 →
      ‖response F y - seedRateConst F‖ ≤ C * y ^ (1 - θ / 2 - ε) := by
  have hΨ := mellinRegularStrip_seedRegPart hF hdecay hθ0 hθ1 hZ hP
  set c := seedRateConst F with hcdef
  set gf : ℝ → ℂ := fun y => response F y - c * ((Real.exp (-y) : ℝ) : ℂ) with hgf
  set c' : ℝ := θ / 2 - 1 + ε with hc'
  have hc'1 : θ / 2 - 1 < c' := by linarith
  have hc'2 : c' < 1 / 4 := by linarith
  have h0a : θ / 2 - 1 < (1 / 8 : ℝ) := by linarith
  have h0b : (1 / 8 : ℝ) < 1 / 4 := by norm_num
  set K := (1 / (2 * Real.pi)) * ∫ t : ℝ, ‖seedRegPart F ((c' : ℂ) + t * I)‖ with hK
  have hK0 : 0 ≤ K := mul_nonneg (by positivity) (integral_nonneg fun _ => norm_nonneg _)
  refine ⟨K + ‖c‖, by positivity, fun y hy hy1 => ?_⟩
  have hconv : MellinConvergent gf ((1 / 8 : ℝ) : ℂ) := by
    have h1 := mellinConvergent_response hF (s := ((1 / 8 : ℝ) : ℂ) + 1) (by norm_num)
    have h2 := (BlackHoleRingdown.mellinConvergent_exp_neg (w := ((1 / 8 : ℝ) : ℂ)) (by simp)).const_smul c
    rw [add_sub_cancel_right] at h1
    refine (h1.sub h2).congr_fun (fun t _ => ?_) measurableSet_Ioi
    simp only [Pi.sub_apply, hgf, smul_eq_mul]
    ring
  have hline : ∀ t : ℝ, mellin gf (((1 / 8 : ℝ) : ℂ) + t * I) =
      seedRegPart F (((1 / 8 : ℝ) : ℂ) + t * I) := fun t =>
    mellin_eq_seedRegPart hF (by simp)
  have hvert : Complex.VerticalIntegrable (mellin gf) (1 / 8 : ℝ) := by
    refine (hΨ.integrable_line h0a h0b).congr ?_
    exact Eventually.of_forall fun t => (hline t).symm
  have hcont : ContinuousAt gf y :=
    ((continuousOn_response hF).continuousAt (Ioi_mem_nhds hy)).sub (continuousAt_const.mul
      (Complex.continuous_ofReal.comp (Real.continuous_exp.comp continuous_neg)).continuousAt)
  have hinv := mellinInv_mellin_eq (1 / 8 : ℝ) gf hy hconv hvert hcont
  have hinv' : mellinInv (1 / 8 : ℝ) (mellin gf) y = mellinInv (1 / 8 : ℝ) (seedRegPart F) y := by
    unfold mellinInv
    congr 1
    exact integral_congr_ae (Eventually.of_forall fun t => by simp only [hline])
  have hshift := hΨ.mellinInv_eq h0a h0b hc'1 hc'2 hy
  have hbound := norm_mellinInv_le (Ψ := seedRegPart F) c' hy
  have hgy : ‖gf y‖ ≤ K * y ^ (1 - θ / 2 - ε) := by
    rw [← hinv, hinv', hshift]
    refine hbound.trans (le_of_eq ?_)
    rw [hK, show -c' = 1 - θ / 2 - ε by rw [hc']; ring]
    ring
  have hexp : ‖((Real.exp (-y) : ℝ) : ℂ) - 1‖ ≤ y := by
    rw [show ((Real.exp (-y) : ℝ) : ℂ) - 1 = ((Real.exp (-y) - 1 : ℝ) : ℂ) by push_cast; ring,
      Complex.norm_real, Real.norm_eq_abs, abs_of_nonpos (by
        have := Real.exp_le_one_iff.2 (by linarith : -y ≤ 0); linarith)]
    linarith [Real.add_one_le_exp (-y)]
  have hyp : y ≤ y ^ (1 - θ / 2 - ε) := by
    have := Real.rpow_le_rpow_of_exponent_ge hy hy1 (show 1 - θ / 2 - ε ≤ 1 by linarith)
    simpa using this
  have hsplit : response F y - c = gf y + c * (((Real.exp (-y) : ℝ) : ℂ) - 1) := by
    simp only [hgf]
    ring
  rw [hsplit]
  calc ‖gf y + c * (((Real.exp (-y) : ℝ) : ℂ) - 1)‖
      ≤ ‖gf y‖ + ‖c‖ * ‖((Real.exp (-y) : ℝ) : ℂ) - 1‖ := by
        refine (norm_add_le _ _).trans ?_
        rw [norm_mul]
    _ ≤ K * y ^ (1 - θ / 2 - ε) + ‖c‖ * y ^ (1 - θ / 2 - ε) := by
        gcongr
        exact hexp.trans hyp
    _ = (K + ‖c‖) * y ^ (1 - θ / 2 - ε) := by ring

/-- **Under the Riemann hypothesis every such seed rings down at the universal rate** `y^{3/4 − ε}`. -/
theorem response_rate_of_riemannHypothesis (hRH : RiemannHypothesis) (hF : IsSeed F)
    (hdecay : ∃ C : ℝ, ∃ N : ℕ, 0 ≤ C ∧ ∀ s : ℂ, -1 / 4 ≤ s.re → s.re ≤ 5 / 4 →
      ‖polarTransform F s‖ ≤ C * (1 + |s.im|) ^ N * Real.exp (-(Real.pi * |s.im|)))
    {ε : ℝ} (hε : 0 < ε) (hε1 : ε < 1 / 2) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ y : ℝ, 0 < y → y ≤ 1 →
      ‖response F y - seedRateConst F‖ ≤ C * y ^ (3 / 4 - ε) := by
  have hZ : ∀ z : ℂ, 1 / 2 < z.re → xi z ≠ 0 := fun z hz h0 => by
    have := (riemannHypothesis_iff_xi_zero_re_eq_half.1 hRH) z h0
    linarith
  have hP : ∀ δ : ℝ, 0 < δ → ∀ d : ℝ, ∃ K : ℝ, ∃ N : ℕ, 0 ≤ K ∧ ∀ z : ℂ, 1 / 2 + δ ≤ z.re →
      z.re ≤ d → 2 ≤ |z.im| → ‖(riemannZeta z)⁻¹‖ ≤ K * |z.im| ^ N := by
    intro δ hδ d
    obtain ⟨Kb, hKb, -, hbd⟩ := exists_invZeta_shift_data_of_rh hRH (δ := min δ (1 / 2))
      (lt_min hδ (by norm_num)) (by linarith [min_le_right δ (1 / 2)]) one_pos d
    refine ⟨2 * Kb, 1, by positivity, fun z hz1 hz2 hzt => ?_⟩
    have hmem : z ∈ GaloisForLFunctions.HTGeometry.verticalStrip (1 / 2 + min δ (1 / 2)) d :=
      ⟨by linarith [min_le_left δ (1 / 2)], hz2⟩
    have hz1' : z ≠ 1 := fun h => by rw [h] at hzt; simp at hzt; linarith
    have h := hbd z hmem
    rw [Sieve.invZeta_eq_inv hz1', Real.rpow_one] at h
    calc ‖(riemannZeta z)⁻¹‖ ≤ Kb * (2 + |z.im|) := h
      _ ≤ Kb * (2 * |z.im|) := by gcongr; linarith
      _ = 2 * Kb * |z.im| ^ 1 := by ring
  obtain ⟨C, hC, h⟩ := norm_response_sub_le_of_zeroFree hF hdecay (θ := 1 / 2) (by norm_num) (by norm_num)
    hZ hP hε hε1
  refine ⟨C, hC, fun y hy hy1 => ?_⟩
  have := h y hy hy1
  rwa [show (1 : ℝ) - 1 / 2 / 2 - ε = 3 / 4 - ε by ring] at this

/-- **A zero-free half-plane gives the ringdown rate.** If `ζ` has no zeros with `Re z > Θ`, `½ ≤ Θ ≤ 1`, every
seed whose polar transform decays like `e^{−π|t|}` rings down at `y^{1 − Θ/2 − ε}`. -/
theorem response_rate_of_zeroFree (hF : IsSeed F)
    (hdecay : ∃ C : ℝ, ∃ N : ℕ, 0 ≤ C ∧ ∀ s : ℂ, -1 / 4 ≤ s.re → s.re ≤ 5 / 4 →
      ‖polarTransform F s‖ ≤ C * (1 + |s.im|) ^ N * Real.exp (-(Real.pi * |s.im|)))
    {Θ : ℝ} (hΘ : 1 / 2 ≤ Θ) (hΘ1 : Θ ≤ 1) (hzf : ∀ z : ℂ, Θ < z.re → riemannZeta z ≠ 0)
    {ε : ℝ} (hε : 0 < ε) (hε1 : ε < 1 / 2) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ y : ℝ, 0 < y → y ≤ 1 →
      ‖response F y - seedRateConst F‖ ≤ C * y ^ (1 - Θ / 2 - ε) := by
  have hZ : ∀ z : ℂ, Θ < z.re → xi z ≠ 0 := fun z hz h0 =>
    hzf z hz (xi_eq_zero_iff_riemannZeta_eq_zero_and_nontrivial.1 h0).1
  have hP : ∀ δ : ℝ, 0 < δ → ∀ d : ℝ, ∃ K : ℝ, ∃ N : ℕ, 0 ≤ K ∧ ∀ z : ℂ, Θ + δ ≤ z.re →
      z.re ≤ d → 2 ≤ |z.im| → ‖(riemannZeta z)⁻¹‖ ≤ K * |z.im| ^ N := by
    intro δ hδ d
    obtain ⟨Kb, hKb, -, hbd⟩ := exists_invZeta_shift_data_of_zeroFree hΘ hΘ1 hzf (δ := min δ (1 / 2))
      (lt_min hδ (by norm_num)) (by linarith [min_le_right δ (1 / 2)]) one_pos d
    refine ⟨2 * Kb, 1, by positivity, fun z hz1 hz2 hzt => ?_⟩
    have hmem : z ∈ GaloisForLFunctions.HTGeometry.verticalStrip (Θ + min δ (1 / 2)) d :=
      ⟨by linarith [min_le_left δ (1 / 2)], hz2⟩
    have hz1' : z ≠ 1 := fun h => by rw [h] at hzt; simp at hzt; linarith
    have h := hbd z hmem
    rw [Sieve.invZeta_eq_inv hz1', Real.rpow_one] at h
    calc ‖(riemannZeta z)⁻¹‖ ≤ Kb * (2 + |z.im|) := h
      _ ≤ Kb * (2 * |z.im|) := by gcongr; linarith
      _ = 2 * Kb * |z.im| ^ 1 := by ring
  exact norm_response_sub_le_of_zeroFree hF hdecay (by linarith) hΘ1 hZ hP hε hε1

end GaloisForLFunctions.ArithmeticHolographyOfTheModularHorizon
