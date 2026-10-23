import GaloisForLFunctions.RHTower.RiemannKernelTransformConstantInjectivity
import GaloisForLFunctions.RHTower.WeilFullConeExtremePoint

/-!
# Riemann-kernel injectivity seen through mean-zero even tests

For weights `w` with `Σ |w(n)| n^{−2} < ∞` let `T_w(g) = Σ_{n ≥ 2} w(n) n^{−1/2} (g(log n) + g(−log n))`
(`atomPairing`).

**Theorem** (`eq_zero_of_forall_even_meanZero_atomPairing_riemannKernel_eq_zero`).  If
`T_w(Φ ⋆ g) = 0` for every real `C²` compactly supported **even** `g` with `∫ g = 0`, then
`w(n) = 0` for every `n ≥ 2`.

This is the injectivity statement needed in the odd sector.  For an odd test `H`,
`Φ′ ⋆ H = −Φ ⋆ H′` and `H′` is even with `∫ H′ = 0`; conversely every even mean-zero `g` is the
derivative of the odd test `∫₀^x g`.  So vanishing of `T_w(Φ′ ⋆ H)` on all odd `H` is exactly the
hypothesis.  The frequency-zero atom is invisible to these tests, which is why the conclusion needs
`eq_zero_of_riemannKernelTransform_eq_const_of_sq` rather than the homogeneous injectivity.

**Proof.**  `T_w(Φ ⋆ g) = ∫ g G_w` with `G_w = Σ w(n) n^{−1/2}(Φ(· + log n) + Φ(· − log n))`
continuous and even.  Odd tests pair to zero with `G_w`; an even test `φ` differs from
`(∫ φ) ψ` (`ψ` a normalised even bump) by an even mean-zero test.  Hence `∫ φ G_w = (∫ φ) C` for
every smooth compactly supported `φ`, with `C = ∫ ψ G_w`, so `G_w ≡ C`, and the constant injectivity
gives `C = 0` and `w = 0`.
-/

open MeasureTheory Filter Topology Set

namespace RHTower

noncomputable section

private theorem weightKernelTransform_neg (w : ℕ → ℝ) (s : ℝ) :
    weightKernelTransform w (-s) = weightKernelTransform w s := by
  unfold weightKernelTransform
  refine tsum_congr fun n => ?_
  congr 1
  unfold riemannKernelReal
  rw [show -s + Real.log n = -(s - Real.log n) by ring,
    show -s - Real.log n = -(s + Real.log n) by ring, abs_neg, abs_neg]
  ring

/-- An odd integrand integrates to zero. -/
private theorem integral_eq_zero_of_odd {f : ℝ → ℝ} (hf : ∀ x, f (-x) = -f x) : ∫ x, f x = 0 := by
  have h := integral_neg_eq_self f volume
  simp only [hf, integral_neg] at h
  linarith

/-- **Mean-zero even tests detect the weights.** -/
theorem eq_zero_of_forall_even_meanZero_atomPairing_riemannKernel_eq_zero {w : ℕ → ℝ}
    (hw2 : Summable fun n : ℕ => |w n| / (n : ℝ) ^ 2)
    (h : ∀ g : ℝ → ℝ, ContDiff ℝ 2 g → HasCompactSupport g → (∀ x, g (-x) = g x) →
      ∫ x, g x = 0 → atomPairing w (crossCorr riemannKernelReal g) = 0) :
    ∀ n, 2 ≤ n → w n = 0 := by
  set W := weightKernelTransform w with hW
  have hWc : Continuous W := continuous_weightKernelTransform hw2
  have hWe : ∀ s, W (-s) = W s := weightKernelTransform_neg w
  -- a normalised even bump
  set bump : ContDiffBump (0 : ℝ) := ⟨1, 2, by norm_num, by norm_num⟩ with hbump
  set ψ : ℝ → ℝ := bump.normed volume with hψ
  have hψc : ContDiff ℝ 2 ψ := bump.contDiff_normed (n := 2)
  have hψs : HasCompactSupport ψ := bump.hasCompactSupport_normed
  have hψe : ∀ x, ψ (-x) = ψ x := fun x => bump.normed_neg x
  have hψi : ∫ x, ψ x = 1 := bump.integral_normed
  set C := ∫ x, ψ x * W x with hC
  have hint : ∀ g : ℝ → ℝ, Continuous g → HasCompactSupport g →
      Integrable fun x => g x * W x :=
    fun g hg hgc => (hg.mul hWc).integrable_of_hasCompactSupport hgc.mul_right
  -- every smooth compactly supported test pairs with `W` through its mass
  have hkey : ∀ φ : ℝ → ℝ, ContDiff ℝ 2 φ → HasCompactSupport φ →
      ∫ x, φ x * W x = (∫ x, φ x) * C := by
    intro φ hφ hφc
    have hφn : ContDiff ℝ 2 fun x => φ (-x) := hφ.comp contDiff_neg
    have hφnc : HasCompactSupport fun x => φ (-x) := hφc.comp_homeomorph (Homeomorph.neg ℝ)
    have hφi : Integrable φ := hφ.continuous.integrable_of_hasCompactSupport hφc
    have hψint : Integrable ψ := hψc.continuous.integrable_of_hasCompactSupport hψs
    -- the even mean-zero part
    set g : ℝ → ℝ := fun x => (φ x + φ (-x)) / 2 - (∫ y, φ y) * ψ x with hg
    have hgc2 : ContDiff ℝ 2 g := ((hφ.add hφn).div_const 2).sub (contDiff_const.mul hψc)
    have hgs : HasCompactSupport g := by
      have h1 : HasCompactSupport fun x => (φ x + φ (-x)) / 2 :=
        (hφc.add hφnc).comp_left (g := fun y : ℝ => y / 2) (by norm_num)
      have h2 : HasCompactSupport fun x => (∫ y, φ y) * ψ x := hψs.mul_left
      exact h1.sub h2
    have hge : ∀ x, g (-x) = g x := by
      intro x; simp only [hg, neg_neg, hψe]; ring
    have hgi : ∫ x, g x = 0 := by
      have i1 : Integrable fun x => (φ x + φ (-x)) / 2 := (hφi.add (hφi.comp_neg)).div_const 2
      have i2 : Integrable fun x => (∫ y, φ y) * ψ x := hψint.const_mul _
      rw [hg, integral_sub i1 i2, integral_div, integral_add hφi hφi.comp_neg,
        integral_neg_eq_self φ volume, integral_const_mul, hψi]
      ring
    have hgW : ∫ x, g x * W x = 0 := by
      rw [← atomPairing_riemannKernel_eq_integral hw2 hgc2.continuous hgs]
      exact h g hgc2 hgs hge hgi
    -- the odd part pairs to zero
    have hoW : ∫ x, (φ x - φ (-x)) / 2 * W x = 0 :=
      integral_eq_zero_of_odd fun x => by rw [neg_neg, hWe]; ring
    have hφsplit : (fun x => φ x * W x) = fun x =>
        g x * W x + (∫ y, φ y) * (ψ x * W x) + (φ x - φ (-x)) / 2 * W x := by
      funext x; simp only [hg]; ring
    have i1 := hint g hgc2.continuous hgs
    have i2 := (hint ψ hψc.continuous hψs).const_mul (∫ y, φ y)
    have i3 := hint (fun x => (φ x - φ (-x)) / 2)
      ((hφ.continuous.sub hφn.continuous).div_const 2)
      ((hφc.sub hφnc).comp_left (g := fun y : ℝ => y / 2) (by norm_num))
    have j1 := integral_add (i1.add i2) i3
    have j2 := integral_add i1 i2
    simp only [Pi.add_apply] at j1 j2
    rw [hφsplit, j1, j2, integral_const_mul, hgW, hoW, ← hC]
    ring
  -- hence `W` is the constant `C`
  have hconst : ∀ s, W s = C := by
    have hae : ∀ᵐ x ∂(volume : Measure ℝ), W x - C = 0 := by
      refine ae_eq_zero_of_integral_contDiff_smul_eq_zero
        (hWc.sub continuous_const).locallyIntegrable fun φ hφ hφc => ?_
      have hφ2 : ContDiff ℝ 2 φ := hφ.of_le (WithTop.coe_le_coe.mpr le_top)
      have hφi : Integrable φ := hφ2.continuous.integrable_of_hasCompactSupport hφc
      simp only [smul_eq_mul]
      have e : (fun x => φ x * (W x - C)) = fun x => φ x * W x - C * φ x := by
        funext x; ring
      rw [e, integral_sub (hint φ hφ2.continuous hφc) (hφi.const_mul C), integral_const_mul,
        hkey φ hφ2 hφc]
      ring
    have hcont : Continuous fun x => W x - C := hWc.sub continuous_const
    intro s
    have := congrFun ((hcont.ae_eq_iff_eq volume continuous_const).mp hae) s
    linarith
  -- the constant injectivity of the Riemann-kernel transform
  set w' : ℕ → ℝ := fun n => if 2 ≤ n then w n else 0 with hw'
  have hsum' : Summable fun n : ℕ => |w' (n + 1)| / ((n : ℝ) + 1) ^ (2 : ℝ) := by
    have hs := (summable_nat_add_iff 1).mpr hw2
    refine Summable.of_nonneg_of_le (fun _ => by positivity) (fun n => ?_) hs
    rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    simp only [hw']
    split_ifs
    · push_cast; exact le_rfl
    · rw [abs_zero, zero_div]; positivity
  have hG' : ∀ y : ℝ, ∑' n : ℕ, w' (n + 1) / Real.sqrt ((n + 1 : ℕ) : ℝ) *
      (riemannKernelReal (y - Real.log ((n + 1 : ℕ) : ℝ)) +
        riemannKernelReal (y + Real.log ((n + 1 : ℕ) : ℝ))) = C := by
    intro y
    rw [← hconst y, hW, weightKernelTransform, (summable_weightTerm hw2 y).tsum_eq_zero_add]
    simp only [show ¬ (2 ≤ 0) by omega, if_false, zero_mul, zero_add]
    refine tsum_congr fun n => ?_
    simp only [hw']
    split_ifs <;> ring
  obtain ⟨-, hz⟩ := eq_zero_of_riemannKernelTransform_eq_const_of_sq hsum' hG'
  intro n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have := hz m
  simp only [hw', if_pos hn] at this
  exact this

end

end RHTower
