import GaloisForLFunctions.RHTower.HalfWeightForcedZero
import GaloisForLFunctions.ArithmeticHolographyOfTheModularHorizon.ThePairEntriesAreRankinSelbergSeries

/-!
# The Shimura integral of a cusp form

For a Maass cusp form `g` of level one, eigenvalue `λ = ¼ + t²`, with Whittaker coefficients
`a_n(y) = ρ(n) √y K_ν(2π|n|y)`, the **Shimura kernel** `G(z) = g(4z) θ̄(z) y^{1/4}` has the weight-½
transformation law `G(γz) = \overline{j(γ, z)} G(z)` on `Γ₀(4)` (`kernel_smul`): `4γz = γ'(4z)` with
`γ' ∈ SL₂(ℤ)`, and `θ` carries the multiplier `j`. Its translates decay faster than any power of `y`
and `1/y` on `𝒟` (`kernel_hdec`), since `4gz` is an `SL₂(ℤ)`-translate of `(ez + β)/δ` with `eδ = 4`.

Folding against the regularised weight-½ Eisenstein series of level `4`
(`RHTower.HalfWeight.rsFold`) gives

* **holomorphy** of `w ↦ rsFold(G)(w)` on `Re w > 1/4` (`differentiableAt_fold`);
* **unfolding** for `Re w > 7/4`:
  `rsFold(G)(w) = 2 ρ(w) Mel_ν(w − ¼) Σ_{j ≠ 0} ρ(j²)(2πj²)^{−1/2} (8πj²)^{3/4−w}`
  (`fold_eq`), with `ρ(w) = (4w−3)(4w−2)ζ(4w−1)` (`regF`) and
  `Mel_ν(μ) = 2^{μ−1}Γ(μ)Γ(μ+ν)Γ(μ−ν)/Γ(2μ)` (`melC`).

In `s = 2w − ½` the series is `Σ_{n ≥ 1} ρ(n²) n^{−s}` up to `(8π)^{¼−w}`, and `ρ(w)` contains `ζ(2s)`: this is
Shimura's continuation of the symmetric-square series to `Re s > 0`.
-/

open Real Complex Filter Topology MeasureTheory Set UpperHalfPlane
open scoped MatrixGroups ComplexConjugate

noncomputable section

namespace GaloisForLFunctions.ArithmeticHolographyOfTheModularHorizon.Shimura

open _root_.RHTower GaloisForLFunctions.RHTower GaloisForLFunctions.RHTower.HalfWeight
open GaloisForLFunctions.RHTower.SelbergMaassFourier GaloisForLFunctions.RHTower.SelbergMaassMean

/-- The **Shimura kernel** `G(z) = g(4z) θ̄(z) y^{1/4}`. -/
def kernel (g : ℍ → ℂ) (z : ℍ) : ℂ :=
  (g ∘ ofComplex) (4 * (z : ℂ)) * conj (theta z) * ((z.im ^ (1 / 4 : ℝ) : ℝ) : ℂ)

/-- `Mel_ν(μ) = 2^{μ−1} Γ(μ) Γ(μ+ν) Γ(μ−ν) / Γ(2μ)`, the Mellin transform of `K_ν(t) e^{−t}`. -/
def melC (ν μ : ℂ) : ℂ :=
  (2 : ℂ) ^ (μ - 1) * Complex.Gamma μ * Complex.Gamma (μ + ν) * Complex.Gamma (μ - ν) / Complex.Gamma (2 * μ)

/-! ### Bessel bounds for complex order -/

theorem norm_cosh_le (z : ℂ) : ‖Complex.cosh z‖ ≤ Real.cosh z.re := by
  rw [Complex.cosh, Real.cosh_eq, norm_div, Complex.norm_two]
  gcongr
  refine (norm_add_le _ _).trans ?_
  rw [Complex.norm_exp, Complex.norm_exp, Complex.neg_re]

/-- `‖K_ν(s)‖ ≤ √π √(2/s)` for `|Re ν| ≤ ½`. -/
theorem norm_Kb_le_of_re {ν : ℂ} (hν : |ν.re| ≤ 1 / 2) {s : ℝ} (hs : 0 < s) :
    ‖Kb ν s‖ ≤ Real.sqrt Real.pi * Real.sqrt (2 / s) := by
  obtain ⟨hI, hle⟩ := integral_exp_exp_le hs
  refine le_trans ?_ hle
  unfold Kb HTGeometry.modifiedBesselKOrder
  refine norm_integral_le_of_norm_le hI ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
  unfold HTGeometry.besselOrderKernel
  have hu0 : 0 < u := hu
  have hre : (-(s : ℂ) * Complex.cosh (u : ℂ)).re = -s * Real.cosh u := by
    rw [← Complex.ofReal_cosh]; simp
  rw [norm_mul, Complex.norm_exp, hre]
  have hc1 : Real.exp u / 2 ≤ Real.cosh u := by
    rw [Real.cosh_eq]; have := (Real.exp_pos (-u)).le; linarith
  have hc2 : ‖Complex.cosh (ν * (u : ℂ))‖ ≤ Real.exp (u / 2) := by
    refine (norm_cosh_le _).trans ?_
    have hνu : (ν * (u : ℂ)).re = ν.re * u := by simp
    rw [hνu, Real.cosh_eq]
    have h1 : ν.re * u ≤ u / 2 := by nlinarith [le_abs_self ν.re]
    have h2 : -(ν.re * u) ≤ u / 2 := by nlinarith [neg_abs_le ν.re]
    have := Real.exp_le_exp.2 h1
    have := Real.exp_le_exp.2 h2
    linarith
  have hc3 : Real.exp (-s * Real.cosh u) ≤ Real.exp (-(s * Real.exp u / 2)) :=
    Real.exp_le_exp.2 (by nlinarith)
  exact mul_le_mul hc3 hc2 (norm_nonneg _) (Real.exp_pos _).le

theorem norm_Wh_le_of_re {ν : ℂ} (hν : |ν.re| ≤ 1 / 2) {t : ℝ} (ht : 0 < t) :
    ‖Wh ν t‖ ≤ Real.sqrt Real.pi * Real.sqrt 2 := by
  rw [Wh, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
  calc Real.sqrt t * ‖Kb ν t‖ ≤ Real.sqrt t * (Real.sqrt Real.pi * Real.sqrt (2 / t)) :=
        mul_le_mul_of_nonneg_left (norm_Kb_le_of_re hν ht) (Real.sqrt_nonneg _)
    _ = Real.sqrt Real.pi * (Real.sqrt t * Real.sqrt (2 / t)) := by ring
    _ = Real.sqrt Real.pi * Real.sqrt 2 := by
        rw [← Real.sqrt_mul ht.le, mul_div_cancel₀ _ ht.ne']

/-- **One Whittaker mode**: `∫_0^∞ y^{w−7/4} e^{−Ay} W_ν(Ay) dy = A^{3/4−w} Mel_ν(w − ¼)` for
`|Re ν| < Re w − ¼`. -/
theorem integral_mode {ν : ℂ} {A : ℝ} (hA : 0 < A) {w : ℂ} (hw : |ν.re| < (w - 1 / 4).re) :
    ∫ y in Ioi (0 : ℝ), (y : ℂ) ^ (w - 7 / 4) * ((Real.exp (-(A * y)) : ℝ) : ℂ) * Wh ν (A * y) =
      (A : ℂ) ^ (3 / 4 - w) * melC ν (w - 1 / 4) := by
  have hM := integral_Kb_exp_cpow hw
  set f : ℝ → ℂ := fun t => ((t / A : ℝ) : ℂ) ^ (w - 7 / 4) * ((Real.exp (-t) : ℝ) : ℂ) * Wh ν t
  have hsub := MeasureTheory.integral_comp_mul_left_Ioi f 0 hA
  simp only [mul_zero] at hsub
  have e1 : ∀ y : ℝ, f (A * y) = (y : ℂ) ^ (w - 7 / 4) * ((Real.exp (-(A * y)) : ℝ) : ℂ) * Wh ν (A * y) := by
    intro y; simp only [f]; rw [mul_div_cancel_left₀ _ hA.ne']
  simp_rw [e1] at hsub
  rw [hsub]
  have e2 : ∀ t ∈ Ioi (0 : ℝ), f t = (A : ℂ) ^ (-(w - 7 / 4)) *
      (Kb ν t * ((Real.exp (-t) : ℝ) : ℂ) * (t : ℂ) ^ ((w - 1 / 4) - 1)) := by
    intro t ht
    have ht0 : 0 < t := ht
    simp only [f, Wh]
    rw [div_eq_mul_inv, ofReal_cpow_mul_pos ht0 (inv_pos.2 hA), Complex.ofReal_inv,
      Complex.inv_cpow _ _ (by rw [Complex.arg_ofReal_of_nonneg hA.le]; exact Real.pi_ne_zero.symm),
      ← Complex.cpow_neg]
    have hs := sqrt_mul_cpow ht0 (w - 7 / 4)
    rw [show w - 1 / 4 - 1 = w - 7 / 4 + 1 / 2 by ring, ← hs]
    ring
  rw [setIntegral_congr_fun measurableSet_Ioi e2, integral_const_mul, hM, Complex.real_smul,
    Complex.ofReal_inv]
  have hA0 : (A : ℂ) ≠ 0 := by exact_mod_cast hA.ne'
  have e3 : (A : ℂ)⁻¹ * (A : ℂ) ^ (-(w - 7 / 4)) = (A : ℂ) ^ (3 / 4 - w) := by
    rw [← Complex.cpow_neg_one, ← Complex.cpow_add _ _ hA0]; congr 1; ring
  unfold melC
  rw [← e3]
  ring

/-! ### The kernel of a cusp form -/

section Kernel

variable {lam : ℝ} {g : ℍ → ℂ} (hg : g ∈ BlackHoleRingdown.HeckeCusp.cuspSpace lam)
include hg

/-- `g(4γz) = g(4z)` on `Γ₀(4)`: `4γz = γ'(4z)` with `γ' = (a 4b; c/4 d)`. -/
theorem four_smul {γ : SL(2, ℤ)} (hγ : γ ∈ CongruenceSubgroup.Gamma0 4) (z : ℍ) :
    (g ∘ ofComplex) (4 * ((γ • z : ℍ) : ℂ)) = (g ∘ ofComplex) (4 * (z : ℂ)) := by
  have hc : (4 : ℤ) ∣ γ 1 0 := by
    rw [CongruenceSubgroup.Gamma0_mem] at hγ
    have h := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).1 hγ
    exact_mod_cast h
  simp only [Function.comp]
  rw [conjFour_smul γ hc z]
  exact hg.1 _ _

/-- **Transformation law**: `G(γz) = \overline{j(γ, z)} G(z)` on `Γ₀(4)`. -/
theorem kernel_smul {γ : SL(2, ℤ)} (hγ : γ ∈ CongruenceSubgroup.Gamma0 (4 * 1)) (z : ℍ) :
    kernel g (γ • z) = conj (jU γ z) * kernel g z := by
  have hγ4 : γ ∈ CongruenceSubgroup.Gamma0 4 := by simpa using hγ
  have hJ := norm_sq_J hγ4 z
  have hJpos : 0 < ‖J γ z‖ := norm_pos_iff.2 (J_ne_zero γ z)
  have hy := z.im_pos
  have him : (γ • z).im = z.im / ‖J γ z‖ ^ 4 := by
    rw [ModularGroup.im_smul_eq_div_normSq, Complex.normSq_eq_norm_sq, ← hJ]; ring
  have hpow : (γ • z).im ^ (1 / 4 : ℝ) = z.im ^ (1 / 4 : ℝ) / ‖J γ z‖ := by
    rw [him, Real.div_rpow hy.le (by positivity), ← Real.rpow_natCast, ← Real.rpow_mul hJpos.le]
    norm_num
  unfold kernel
  rw [four_smul hg hγ4 z, theta_smul, hpow, jU, map_mul, map_div₀, Complex.conj_ofReal]
  push_cast
  have hJ0 : ((‖J γ z‖ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hJpos.ne'
  field_simp

theorem continuous_four : Continuous fun z : ℍ => (g ∘ ofComplex) (4 * (z : ℂ)) := by
  have hgc : Continuous g := BlackHoleRingdown.HeckeCusp.continuous_of_maass hg.2.1
  refine continuous_iff_continuousAt.2 fun z => ?_
  have h4 : 0 < (4 * (z : ℂ)).im := by simp; exact z.im_pos
  have hof : ContinuousAt (fun z : ℍ => ofComplex (4 * (z : ℂ))) z :=
    ContinuousAt.comp (f := fun z : ℍ => 4 * (z : ℂ)) (g := ofComplex)
      (UpperHalfPlane.contMDiffAt_ofComplex (n := 0) h4).continuousAt
      (continuous_const.mul UpperHalfPlane.continuous_coe).continuousAt
  exact hgc.continuousAt.comp hof

theorem continuous_kernel : Continuous (kernel g) := by
  have hθ : Continuous fun z : ℍ => theta z :=
    continuous_iff_continuousAt.2 fun z =>
      ((differentiableAt_theta z.im_pos).continuousAt).comp UpperHalfPlane.continuous_coe.continuousAt
  have hy : Continuous fun z : ℍ => ((z.im ^ (1 / 4 : ℝ) : ℝ) : ℂ) :=
    Complex.continuous_ofReal.comp (UpperHalfPlane.continuous_im.rpow_const fun z => Or.inl z.im_pos.ne')
  unfold kernel
  exact ((continuous_four hg).mul (Complex.continuous_conj.comp hθ)).mul hy

/-- **Cusp decay of `g(4Az)`**, exponential in `Im z`, for every `A ∈ SL₂(ℤ)`. -/
theorem four_decay (A : SL(2, ℤ)) :
    ∃ C c t₀ : ℝ, 0 ≤ C ∧ 0 < c ∧ 0 < t₀ ∧ ∀ z : ℍ, t₀ ≤ z.im →
      ‖(g ∘ ofComplex) (4 * ((A • z : ℍ) : ℂ))‖ ≤ C * Real.exp (-c * z.im) := by
  obtain ⟨h, e, δ, β, he, hδ, heδ, hH⟩ := hermite_four A
  obtain ⟨D, hD0, hD⟩ := cuspForm_decay hg
  have heδ' : (1 : ℝ) / 4 ≤ (e : ℝ) / δ := by
    have he1 : (1 : ℝ) ≤ e := by exact_mod_cast he
    have hδ4 : (δ : ℝ) ≤ 4 := by
      have : (e : ℝ) * δ = 4 := by exact_mod_cast heδ
      nlinarith
    have hδp : (0 : ℝ) < δ := by exact_mod_cast hδ
    rw [div_le_div_iff₀ (by norm_num) hδp]; nlinarith
  refine ⟨D, Real.pi / 4, 4, hD0, by positivity, by norm_num, fun z hz => ?_⟩
  have hz0 := z.im_pos
  have haff : z.im / 4 ≤ (affPt e δ β he hδ z).im := by
    rw [affPt_im]
    have hδp : (0 : ℝ) < δ := by exact_mod_cast hδ
    calc z.im / 4 = (1 / 4) * z.im := by ring
      _ ≤ (e : ℝ) / δ * z.im := mul_le_mul_of_nonneg_right heδ' hz0.le
      _ = (e : ℝ) * z.im / δ := by ring
  show ‖g (ofComplex (4 * ((A • z : ℍ) : ℂ)))‖ ≤ _
  rw [hH z, hg.1 h]
  have hp := mul_le_mul_of_nonneg_left haff Real.pi_pos.le
  calc ‖g (affPt e δ β he hδ z)‖ ≤ D * Real.exp (-Real.pi * (affPt e δ β he hδ z).im) :=
        hD _ (by linarith)
    _ ≤ D * Real.exp (-(Real.pi / 4) * z.im) :=
        mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 (by linarith)) hD0

/-- A global bound `‖g(4z)‖ ≤ K e^{−c Im z}`. -/
theorem four_global : ∃ K c : ℝ, 0 ≤ K ∧ 0 < c ∧ ∀ z : ℍ,
    ‖(g ∘ ofComplex) (4 * (z : ℂ))‖ ≤ K * Real.exp (-c * z.im) := by
  obtain ⟨C, c, t₀, hC0, hc, ht₀, hdecay⟩ := four_decay hg 1
  obtain ⟨Bf, hBf⟩ := BlackHoleRingdown.HeckeCusp.exists_bound hg
  refine ⟨max C (max Bf 0 * Real.exp (c * t₀)), c, le_max_of_le_left hC0, hc, fun z => ?_⟩
  rcases le_or_gt t₀ z.im with h | h
  · have := hdecay z h
    rw [one_smul] at this
    exact this.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.exp_pos _).le)
  · have h1 := hBf (ofComplex (4 * (z : ℂ)))
    have h2 : Bf ≤ max Bf 0 * Real.exp (c * t₀) * Real.exp (-c * z.im) := by
      rw [mul_assoc, ← Real.exp_add]
      have : 1 ≤ Real.exp (c * t₀ + -c * z.im) := Real.one_le_exp (by nlinarith)
      nlinarith [le_max_left Bf 0, le_max_right Bf 0]
    calc _ ≤ Bf := h1
      _ ≤ max Bf 0 * Real.exp (c * t₀) * Real.exp (-c * z.im) := h2
      _ ≤ _ := mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.exp_pos _).le

/-- **Rapid decay of the translates of `G` on `𝒟`.** -/
theorem kernel_hdec (B : ℝ) (A : SL(2, ℤ)) :
    IntegrableOn (fun w : ℍ => ‖kernel g (A • w)‖ * ((A • w).im ^ B + (A • w).im ^ (-B)))
      ModularGroup.fd := by
  open GaloisForLFunctions.RHTower.SelbergPoincareIntegrability in
  obtain ⟨E, hE1, hE⟩ := im_smul_two_sided A
  obtain ⟨C, c, t₀, hC0, hc, ht₀, hdecay⟩ := four_decay hg A
  obtain ⟨Bf, hBf⟩ := BlackHoleRingdown.HeckeCusp.exists_bound hg
  set K : ℝ := max C (max Bf 0 * Real.exp (c * t₀))
  have hK0 : 0 ≤ K := le_max_of_le_left hC0
  set m : ℝ := |B| + 2
  have hm : 1 < m := by simp only [m]; linarith [abs_nonneg B]
  have hmaj := (SelbergMaassExpDecayCell.maj_integrableOn_fd (σ := m) hm hc).norm.const_mul
    (4 * K * (20 * E) ^ m)
  refine hmaj.mono' ?_ (ae_restrict_of_forall_mem ModularGroup.isClosed_fd.measurableSet fun w hw => ?_)
  · refine Continuous.aestronglyMeasurable ?_
    have hs : Continuous fun w : ℍ => A • w := continuous_smul_sl A
    have him : Continuous fun w : ℍ => (A • w).im := UpperHalfPlane.continuous_im.comp hs
    exact ((continuous_kernel hg).comp hs).norm.mul
      ((him.rpow_const fun w => Or.inl (A • w).im_pos.ne').add
        (him.rpow_const fun w => Or.inl (A • w).im_pos.ne'))
  set t := w.im
  have ht := w.im_pos
  have ht2 := SelbergMaassExpDecayCell.one_le_im_of_mem_fd hw
  set s := (A • w).im
  have hs := (A • w).im_pos
  obtain ⟨hs1, hs2⟩ := hE w hw
  set L : ℝ := 20 * E * t
  have hL1 : 1 ≤ L := by simp only [L]; nlinarith
  have hpow : s ^ B + s ^ (-B) ≤ 2 * L ^ |B| := by
    have := rpow_le_of_mem (B := B) hs hs1 hs2
    have := rpow_le_of_mem (B := -B) hs hs1 hs2
    rw [abs_neg] at this
    linarith
  have hθ : ‖theta ((A • w : ℍ) : ℂ)‖ ≤ 2 * L := by
    have h := norm_theta_le (v := ((A • w : ℍ) : ℂ)) hs
    have h1 : 1 / (π * s) ≤ L := by
      have : 1 / (π * s) ≤ 1 / s := by
        apply one_div_le_one_div_of_le hs; nlinarith [Real.pi_gt_three]
      linarith
    change ‖theta ((A • w : ℍ) : ℂ)‖ ≤ 2 * L
    have : ((A • w : ℍ) : ℂ).im = s := rfl
    rw [this] at h
    linarith
  have hy : s ^ (1 / 4 : ℝ) ≤ L := by
    calc s ^ (1 / 4 : ℝ) ≤ L ^ (1 / 4 : ℝ) := Real.rpow_le_rpow hs.le hs1 (by norm_num)
      _ ≤ L ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hL1 (by norm_num)
      _ = L := Real.rpow_one L
  have hf : ‖(g ∘ ofComplex) (4 * ((A • w : ℍ) : ℂ))‖ ≤ K * Real.exp (-c * t) := by
    rcases le_or_gt t₀ t with h | h
    · exact (hdecay w h).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.exp_pos _).le)
    · have h1 := hBf (ofComplex (4 * ((A • w : ℍ) : ℂ)))
      have h2 : Bf ≤ max Bf 0 * Real.exp (c * t₀) * Real.exp (-c * t) := by
        rw [mul_assoc, ← Real.exp_add]
        have : 1 ≤ Real.exp (c * t₀ + -c * t) := Real.one_le_exp (by nlinarith)
        nlinarith [le_max_left Bf 0, le_max_right Bf 0]
      calc _ ≤ Bf := h1
        _ ≤ max Bf 0 * Real.exp (c * t₀) * Real.exp (-c * t) := h2
        _ ≤ K * Real.exp (-c * t) := mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.exp_pos _).le
  have hG : ‖kernel g (A • w)‖ ≤ K * Real.exp (-c * t) * (2 * L) * L := by
    unfold kernel
    rw [norm_mul, norm_mul, Complex.norm_conj, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (by positivity)]
    exact mul_le_mul (mul_le_mul hf hθ (norm_nonneg _) (by positivity)) hy (by positivity) (by positivity)
  have hmajw : ‖maj m c w‖ = t ^ m * Real.exp (-c * t) := by
    unfold maj
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity), hmajw]
  have hLm : L ^ |B| * L * L = (20 * E) ^ m * t ^ m := by
    rw [← Real.mul_rpow (by positivity) ht.le]
    simp only [L, m]
    rw [Real.rpow_add (by positivity), Real.rpow_two]
    ring
  calc ‖kernel g (A • w)‖ * (s ^ B + s ^ (-B))
      ≤ (K * Real.exp (-c * t) * (2 * L) * L) * (2 * L ^ |B|) :=
        mul_le_mul hG hpow (by positivity) (by positivity)
    _ = 4 * K * (L ^ |B| * L * L) * Real.exp (-c * t) := by ring
    _ = 4 * K * (20 * E) ^ m * (t ^ m * Real.exp (-c * t)) := by rw [hLm]; ring

/-- **Shimura's continuation**: the folded integral of `G` is holomorphic on `Re w > 1/4`. -/
theorem differentiableAt_fold {w : ℂ} (hw : 1 / 4 < w.re) : DifferentiableAt ℂ (rsFold 1 (kernel g)) w :=
  differentiableAt_rsFold 1 (continuous_kernel hg) (fun B c => kernel_hdec hg B (Quotient.out c)) hw

/-- **Integrability on the strip** for `Re w > 7/4`. -/
theorem integrableOn_kernel_strip {w : ℂ} (hw : 7 / 4 < w.re) :
    IntegrableOn (fun z : ℍ => kernel g z * ((z.im : ℝ) : ℂ) ^ w) HTGeometry.modularStrip := by
  obtain ⟨K, c, hK0, hc, hK⟩ := four_global hg
  have hA : MeasurableSet (Ico (0 : ℝ) 1 ×ˢ Ioi (0 : ℝ)) := measurableSet_Ico.prod measurableSet_Ioi
  have hpos : ∀ p ∈ Ico (0 : ℝ) 1 ×ˢ Ioi (0 : ℝ), 0 < p.2 := fun p hp => hp.2
  rw [modularStrip_eq_coord, HTGeometry.UpperHalfPlaneCoordIntegrable.integrableOn_coord_iff hA hpos]
  set f : ℝ → ℝ := fun y => K * (y ^ (w.re - 7 / 4) * Real.exp (-c * y ^ (1 : ℝ)) +
    1 / π * (y ^ (w.re - 11 / 4) * Real.exp (-c * y ^ (1 : ℝ))))
  have hf : IntegrableOn f (Ioi 0) := by
    have h1 := integrableOn_rpow_mul_exp_neg_mul_rpow (p := 1) (s := w.re - 7 / 4) (b := c) (by linarith)
      le_rfl hc
    have h2 := integrableOn_rpow_mul_exp_neg_mul_rpow (p := 1) (s := w.re - 11 / 4) (b := c) (by linarith)
      le_rfl hc
    exact (h1.add (h2.const_mul (1 / π))).const_mul K
  have hprod := (integrable_const (1 : ℝ) (μ := volume.restrict (Ico (0 : ℝ) 1))).mul_prod hf
  rw [IntegrableOn, Measure.volume_eq_prod, ← Measure.prod_restrict]
  refine Integrable.mono' hprod ?_ ?_
  · rw [Measure.prod_restrict, ← Measure.volume_eq_prod]
    refine ContinuousOn.aestronglyMeasurable (fun p hp => ?_) hA
    have hp2 : 0 < p.2 := hp.2
    have hmk : ContinuousWithinAt (fun p : ℝ × ℝ => (ofComplex (⟨p.1, p.2⟩ : ℂ) : ℍ))
        (Ico (0 : ℝ) 1 ×ˢ Ioi 0) p := by
      have e : (fun p : ℝ × ℝ => (⟨p.1, p.2⟩ : ℂ)) = fun p : ℝ × ℝ => (p.1 : ℂ) + (p.2 : ℂ) * Complex.I := by
        funext p; apply Complex.ext <;> simp
      have hc1 : Continuous (fun p : ℝ × ℝ => (⟨p.1, p.2⟩ : ℂ)) := by rw [e]; fun_prop
      have hc2 : ContinuousAt (ofComplex : ℂ → ℍ) (⟨p.1, p.2⟩ : ℂ) :=
        (UpperHalfPlane.contMDiffAt_ofComplex (n := 0) (by simpa using hp2)).continuousAt
      exact (ContinuousAt.comp (x := p) (f := fun p : ℝ × ℝ => (⟨p.1, p.2⟩ : ℂ))
        (g := (ofComplex : ℂ → ℍ)) hc2 hc1.continuousAt).continuousWithinAt
    have hG := ((continuous_kernel hg).continuousAt).comp_continuousWithinAt hmk
    have hy : ContinuousWithinAt (fun p : ℝ × ℝ => ((ofComplex (⟨p.1, p.2⟩ : ℂ) : ℍ).im : ℂ) ^ w)
        (Ico (0 : ℝ) 1 ×ˢ Ioi 0) p := by
      have := (Complex.continuous_ofReal.continuousAt.comp_continuousWithinAt
        (UpperHalfPlane.continuous_im.continuousAt.comp_continuousWithinAt hmk))
      refine this.cpow continuousWithinAt_const ?_
      simp only [Function.comp]
      exact Complex.ofReal_mem_slitPlane.2 (ofComplex (⟨p.1, p.2⟩ : ℂ)).im_pos
    exact (hG.mul hy).div (by fun_prop) (by exact_mod_cast (pow_pos hp2 2).ne')
  · rw [Measure.prod_restrict]
    refine ae_restrict_of_forall_mem hA fun p hp => ?_
    have hp2 : 0 < p.2 := hp.2
    set z : ℍ := ofComplex (⟨p.1, p.2⟩ : ℂ)
    have hz : (z : ℂ) = ⟨p.1, p.2⟩ := ofComplex_mk hp2
    have hzim : z.im = p.2 := by simp [UpperHalfPlane.im, hz]
    simp only [one_mul]
    rw [norm_div, norm_mul, kernel, norm_mul, norm_mul, Complex.norm_conj, Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonneg (by positivity), Complex.norm_cpow_eq_rpow_re_of_pos z.im_pos,
      norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hp2, hzim]
    have hf' := hK z
    rw [hzim] at hf'
    have hθ := norm_theta_le (v := (z : ℂ)) z.im_pos
    have hzim' : (z : ℂ).im = p.2 := by rw [hz]
    rw [hzim'] at hθ
    set y := p.2
    have hy14 : y ^ (1 / 4 : ℝ) * y ^ w.re / y ^ 2 = y ^ (w.re - 7 / 4) := by
      rw [← Real.rpow_add hp2, ← Real.rpow_natCast, ← Real.rpow_sub hp2]; congr 1; push_cast; ring
    have hy11 : y ^ (1 / 4 : ℝ) * y ^ w.re / y ^ 2 / y = y ^ (w.re - 11 / 4) := by
      rw [hy14, ← Real.rpow_sub_one hp2.ne']; congr 1; ring
    simp only [f, Real.rpow_one]
    calc ‖(g ∘ ofComplex) (4 * (z : ℂ))‖ * ‖theta z‖ * y ^ (1 / 4 : ℝ) * y ^ w.re / y ^ 2
        ≤ K * Real.exp (-c * y) * (1 + 1 / (π * y)) * y ^ (1 / 4 : ℝ) * y ^ w.re / y ^ 2 := by
          gcongr
      _ = K * (y ^ (1 / 4 : ℝ) * y ^ w.re / y ^ 2 * Real.exp (-c * y) +
            1 / π * (y ^ (1 / 4 : ℝ) * y ^ w.re / y ^ 2 / y * Real.exp (-c * y))) := by
          field_simp
      _ = _ := by rw [hy11, hy14]

end Kernel

/-! ### The Shimura series -/

section Series

variable {lam : ℝ} {g : ℍ → ℂ} (hg : g ∈ BlackHoleRingdown.HeckeCusp.cuspSpace lam) {ρ : ℤ → ℂ}
  (hρ0 : ρ 0 = 0)
  (hρ : ∀ n : ℤ, ∀ y, 0 < y → BlackHoleRingdown.HeckeCusp.fourierCoeff g n y = ρ n * (Real.sqrt y : ℂ) *
    HTGeometry.modifiedBesselKOrder (2 * Real.pi * |(n : ℝ)| * y) (BlackHoleRingdown.CuspL.nu lam))

/-- The coefficients in the normalization `a_k(y) = ρ_W(k) W_ν(2π|k|y)`, `W_ν(t) = √t K_ν(t)`. -/
def rW (ρ : ℤ → ℂ) (k : ℤ) : ℂ := ρ k / (Real.sqrt (2 * π * |(k : ℝ)|) : ℂ)

/-- The Whittaker modes `a_j(y) = e^{−8πj²y} ρ_W(j²) W_ν(8πj²y)`. -/
def aMode (ν : ℂ) (ρ : ℤ → ℂ) (j : ℤ) (y : ℝ) : ℂ :=
  ((Real.exp (-(8 * π * (j : ℝ) ^ 2 * y)) : ℝ) : ℂ) * (rW ρ (j ^ 2) * Wh ν (8 * π * (j : ℝ) ^ 2 * y))

/-- The Shimura coefficients `ρ_W(j²) (8πj²)^{3/4−w}`, and `0` at `j = 0`. -/
def zCoef (ρ : ℤ → ℂ) (w : ℂ) (j : ℤ) : ℂ :=
  if j = 0 then 0 else rW ρ (j ^ 2) * ((8 * π * (j : ℝ) ^ 2 : ℝ) : ℂ) ^ (3 / 4 - w)

include hρ0 hρ in
/-- The width-one coefficient at `j²` and height `4y` in the `W_ν` normalization. -/
theorem coefficient_sq {y : ℝ} (hy : 0 < y) (j : ℤ) :
    coefficient 1 (j ^ 2) (g ∘ ofComplex) (4 * y) = rW ρ (j ^ 2) * Wh (BlackHoleRingdown.CuspL.nu lam)
      (8 * π * (j : ℝ) ^ 2 * y) := by
  have h := hρ (j ^ 2) (4 * y) (by linarith)
  have e : BlackHoleRingdown.HeckeCusp.fourierCoeff g (j ^ 2) (4 * y) =
      coefficient 1 (j ^ 2) (g ∘ ofComplex) (4 * y) := rfl
  rw [← e, h]
  by_cases hj : j = 0
  · subst hj; simp [rW, hρ0]
  have hj2 : (0 : ℝ) < (j : ℝ) ^ 2 := by
    have : (j : ℝ) ≠ 0 := by exact_mod_cast hj
    positivity
  have habs : |((j ^ 2 : ℤ) : ℝ)| = (j : ℝ) ^ 2 := by push_cast; exact abs_of_pos hj2
  have hs : Real.sqrt (8 * π * (j : ℝ) ^ 2 * y) = Real.sqrt (2 * π * (j : ℝ) ^ 2) * Real.sqrt (4 * y) := by
    rw [← Real.sqrt_mul (by positivity)]; congr 1; ring
  have hs0 : (Real.sqrt (2 * π * (j : ℝ) ^ 2) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.2 (by positivity)).ne'
  rw [rW, Wh, Kb, habs, hs]
  push_cast
  rw [show 2 * π * (j : ℝ) ^ 2 * (4 * y) = 8 * π * (j : ℝ) ^ 2 * y by ring]
  field_simp

include hg hρ0 hρ in
/-- **The zeroth coefficient**: `∫_0^1 g(4z) θ̄(z) dx = Σ_j a_j(y)`. -/
theorem hasSum_zeroth {y : ℝ} (hy : 0 < y) :
    HasSum (fun j : ℤ => aMode (BlackHoleRingdown.CuspL.nu lam) ρ j y)
      (∫ x in (0 : ℝ)..1, (g ∘ ofComplex) (point (4 * x) (4 * y)) * conj (theta (point x y))) := by
  have hy4 : 0 < 4 * y := by linarith
  obtain ⟨C, hC⟩ := BlackHoleRingdown.HeckeCusp.exists_bound hg
  have hB : ∀ x : ℝ, ‖(g ∘ ofComplex) (point x (4 * y))‖ ≤ C := fun x => hC _
  have hc : Continuous fun x : ℝ => (g ∘ ofComplex) (point x (4 * y)) :=
    BlackHoleRingdown.HeckeCusp.continuous_slice hg.2.1 hy4
  have hper : ∀ x : ℝ, (g ∘ ofComplex) (point (x + 1) (4 * y)) = (g ∘ ofComplex) (point x (4 * y)) := by
    intro x
    have hp : point (x + 1) (4 * y) = point x (4 * y) + 1 := by
      apply Complex.ext <;> simp [point]
    rw [hp, BlackHoleRingdown.HeckeCusp.periodic_comp hg _ (by simpa [point] using hy4)]
  have h := hasSum_integral_U_conj_theta' hy hB hc hper
  refine h.congr_fun fun j => ?_
  rw [aMode, coefficient_sq hρ0 hρ hy j]

theorem norm_rW_le {C : ℝ} (hC : ∀ n : ℤ, ‖ρ n‖ ≤ C * Real.sqrt |(n : ℝ)|) (k : ℤ) :
    ‖rW ρ k‖ ≤ C / Real.sqrt (2 * π) := by
  have hC0 : 0 ≤ C := by
    have := hC 1; simp at this; exact (norm_nonneg _).trans this
  rw [rW, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
  by_cases hk : k = 0
  · subst hk; simp; positivity
  have hk0 : (0 : ℝ) < |(k : ℝ)| := abs_pos.2 (by exact_mod_cast hk)
  have hs : Real.sqrt (2 * π * |(k : ℝ)|) = Real.sqrt (2 * π) * Real.sqrt |(k : ℝ)| :=
    Real.sqrt_mul (by positivity) _
  rw [hs, div_le_div_iff₀ (by positivity) (by positivity)]
  calc ‖ρ k‖ * Real.sqrt (2 * π) ≤ C * Real.sqrt |(k : ℝ)| * Real.sqrt (2 * π) :=
        mul_le_mul_of_nonneg_right (hC k) (Real.sqrt_nonneg _)
    _ = C * (Real.sqrt (2 * π) * Real.sqrt |(k : ℝ)|) := by ring

theorem kernel_coord {x y : ℝ} (hy : 0 < y) :
    kernel g (ofComplex (⟨x, y⟩ : ℂ)) = (g ∘ ofComplex) (point (4 * x) (4 * y)) *
      conj (theta (point x y)) * ((y ^ (1 / 4 : ℝ) : ℝ) : ℂ) := by
  have hz := ofComplex_mk (x := x) hy
  have hp : (⟨x, y⟩ : ℂ) = point x y := by apply Complex.ext <;> simp [point]
  have him : (ofComplex (⟨x, y⟩ : ℂ)).im = y := by
    rw [UpperHalfPlane.im, hz]
  unfold kernel
  rw [him, hz, hp]
  congr 3
  simp only [point]; push_cast; ring

include hg hρ0 hρ in
/-- **The horizontal integral** at height `y`: `∫_0^1 G(x+iy) y^{w−2} dx = y^{w−7/4} Σ_j a_j(y)`. -/
theorem inner_integral (w : ℂ) {y : ℝ} (hy : 0 < y) :
    ∫ x in Ico (0 : ℝ) 1, kernel g (ofComplex (⟨x, y⟩ : ℂ)) * ((y : ℝ) : ℂ) ^ w / ((y : ℝ) : ℂ) ^ 2 =
      ((y : ℝ) : ℂ) ^ (w - 7 / 4) * ∑' j : ℤ, aMode (BlackHoleRingdown.CuspL.nu lam) ρ j y := by
  have h := (hasSum_zeroth hg hρ0 hρ hy).tsum_eq
  have hc : ((y ^ (1 / 4 : ℝ) : ℝ) : ℂ) * ((y : ℝ) : ℂ) ^ w / ((y : ℝ) : ℂ) ^ 2 =
      ((y : ℝ) : ℂ) ^ (w - 7 / 4) := by
    have hy0 : ((y : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hy.ne'
    rw [Complex.ofReal_cpow hy.le, ← Complex.cpow_natCast, ← Complex.cpow_add _ _ hy0,
      ← Complex.cpow_sub _ _ hy0]
    congr 1; push_cast; ring
  simp_rw [kernel_coord hy]
  have e : ∀ x : ℝ, (g ∘ ofComplex) (point (4 * x) (4 * y)) * conj (theta (point x y)) *
      ((y ^ (1 / 4 : ℝ) : ℝ) : ℂ) * ((y : ℝ) : ℂ) ^ w / ((y : ℝ) : ℂ) ^ 2 =
      ((g ∘ ofComplex) (point (4 * x) (4 * y)) * conj (theta (point x y))) *
        ((y : ℝ) : ℂ) ^ (w - 7 / 4) := by
    intro x; rw [← hc]; ring
  simp_rw [e]
  rw [integral_mul_const, integral_Ico_eq_integral_Ioc, ← intervalIntegral.integral_of_le zero_le_one,
    ← h, mul_comm]

/-- **The Mellin transform of each mode**, `Re w > ¼`:
`∫_0^∞ y^{w−7/4} a_j(y) dy = ρ_W(j²)(8πj²)^{3/4−w} Mel_ν(w − ¼)`. -/
theorem integral_aMode (j : ℤ) {w : ℂ} (hw : 1 / 4 < w.re) :
    ∫ y in Ioi (0 : ℝ), ((y : ℝ) : ℂ) ^ (w - 7 / 4) * aMode (BlackHoleRingdown.CuspL.nu lam) ρ j y =
      zCoef ρ w j * melC (BlackHoleRingdown.CuspL.nu lam) (w - 1 / 4) := by
  have hν : |(BlackHoleRingdown.CuspL.nu lam).re| < (w - 1 / 4).re := by
    rw [BlackHoleRingdown.CuspL.nu_re, abs_zero]; simp; linarith
  by_cases hj : j = 0
  · subst hj
    simp [aMode, zCoef, rW]
  · have hA : 0 < 8 * π * (j : ℝ) ^ 2 := by
      have : (0 : ℝ) < (j : ℝ) ^ 2 := by
        have : (j : ℝ) ≠ 0 := by exact_mod_cast hj
        positivity
      positivity
    have e : ∀ y : ℝ, ((y : ℝ) : ℂ) ^ (w - 7 / 4) * aMode (BlackHoleRingdown.CuspL.nu lam) ρ j y =
        rW ρ (j ^ 2) * (((y : ℝ) : ℂ) ^ (w - 7 / 4) *
          ((Real.exp (-(8 * π * (j : ℝ) ^ 2 * y)) : ℝ) : ℂ) *
            Wh (BlackHoleRingdown.CuspL.nu lam) (8 * π * (j : ℝ) ^ 2 * y)) := by
      intro y; simp only [aMode]; ring
    simp_rw [e]
    rw [integral_const_mul, integral_mode hA hν, zCoef, if_neg hj]
    ring

/-- **Norm bound for each mode**, `Re w > 3/4`. -/
theorem integral_norm_aMode_le {R : ℝ} (hR : ∀ k : ℤ, ‖rW ρ k‖ ≤ R) (j : ℤ) {w : ℂ} (hw : 3 / 4 < w.re) :
    IntegrableOn (fun y : ℝ => ((y : ℝ) : ℂ) ^ (w - 7 / 4) * aMode (BlackHoleRingdown.CuspL.nu lam) ρ j y)
        (Ioi 0) ∧
    ∫ y in Ioi (0 : ℝ), ‖((y : ℝ) : ℂ) ^ (w - 7 / 4) * aMode (BlackHoleRingdown.CuspL.nu lam) ρ j y‖ ≤
      R * Real.sqrt (2 * π) * Real.Gamma (w.re - 3 / 4) * (8 * π) ^ (3 / 4 - w.re) *
        |(j : ℝ)| ^ (-(2 * w.re - 3 / 2)) := by
  set ν := BlackHoleRingdown.CuspL.nu lam
  have hν : |ν.re| ≤ 1 / 2 := by rw [BlackHoleRingdown.CuspL.nu_re, abs_zero]; norm_num
  have hR0 : 0 ≤ R := (norm_nonneg _).trans (hR 0)
  by_cases hj : j = 0
  · subst hj
    have hz : ∀ y : ℝ, ((y : ℝ) : ℂ) ^ (w - 7 / 4) * aMode ν ρ 0 y = 0 := by
      intro y; simp [aMode, rW]
    simp_rw [hz]
    refine ⟨integrableOn_zero, ?_⟩
    simp only [norm_zero, integral_zero, Int.cast_zero, abs_zero]
    rw [Real.zero_rpow (by linarith)]; simp
  set A : ℝ := 8 * π * (j : ℝ) ^ 2
  have hA : 0 < A := by
    have : (0 : ℝ) < (j : ℝ) ^ 2 := by
      have : (j : ℝ) ≠ 0 := by exact_mod_cast hj
      positivity
    simp only [A]; positivity
  set σ := w.re
  have hmaj := integrableOn_rpow_mul_exp_neg_mul_rpow (p := 1) (s := σ - 7 / 4) (b := A) (by linarith)
    le_rfl hA
  simp only [Real.rpow_one] at hmaj
  have hW : ∀ y ∈ Ioi (0 : ℝ), ‖((y : ℝ) : ℂ) ^ (w - 7 / 4) * aMode ν ρ j y‖ ≤
      R * Real.sqrt (2 * π) * (y ^ (σ - 7 / 4) * Real.exp (-A * y)) := by
    intro y hy
    have hy0 : 0 < y := hy
    rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hy0, aMode, norm_mul, norm_mul,
      Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    have hWb := norm_Wh_le_of_re hν (t := A * y) (by positivity)
    have hs2 : Real.sqrt Real.pi * Real.sqrt 2 = Real.sqrt (2 * π) := by
      rw [← Real.sqrt_mul Real.pi_pos.le]; ring_nf
    rw [hs2] at hWb
    have hre : (w - 7 / 4).re = σ - 7 / 4 := by simp [σ]
    rw [hre, show -(8 * π * (j : ℝ) ^ 2 * y) = -A * y by simp only [A]; ring,
      show 8 * π * (j : ℝ) ^ 2 * y = A * y by simp only [A]]
    calc y ^ (σ - 7 / 4) * (Real.exp (-A * y) * (‖rW ρ (j ^ 2)‖ * ‖Wh ν (A * y)‖))
        ≤ y ^ (σ - 7 / 4) * (Real.exp (-A * y) * (R * Real.sqrt (2 * π))) := by
          apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg hy0.le _)
          apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
          exact mul_le_mul (hR _) hWb (norm_nonneg _) hR0
      _ = _ := by ring
  have hmeas : AEStronglyMeasurable (fun y : ℝ => ((y : ℝ) : ℂ) ^ (w - 7 / 4) * aMode ν ρ j y)
      (volume.restrict (Ioi 0)) := by
    refine ContinuousOn.aestronglyMeasurable (fun y hy => ?_) measurableSet_Ioi
    have hy0 : 0 < y := hy
    refine ContinuousAt.continuousWithinAt ?_
    have hc1 : ContinuousAt (fun y : ℝ => ((y : ℝ) : ℂ) ^ (w - 7 / 4)) y :=
      Complex.continuous_ofReal.continuousAt.cpow continuousAt_const (Complex.ofReal_mem_slitPlane.2 hy0)
    have hc2 : ContinuousAt (fun y : ℝ => Wh ν (8 * π * (j : ℝ) ^ 2 * y)) y :=
      ((hasDerivAt_Wh (by positivity) ν).continuousAt).comp (by fun_prop : Continuous
        fun y : ℝ => 8 * π * (j : ℝ) ^ 2 * y).continuousAt
    simp only [aMode]
    exact hc1.mul ((by fun_prop : Continuous fun y : ℝ =>
      ((Real.exp (-(8 * π * (j : ℝ) ^ 2 * y)) : ℝ) : ℂ)).continuousAt.mul (continuousAt_const.mul hc2))
  have hint : IntegrableOn (fun y : ℝ => ((y : ℝ) : ℂ) ^ (w - 7 / 4) * aMode ν ρ j y) (Ioi 0) :=
    (hmaj.const_mul (R * Real.sqrt (2 * π))).mono' hmeas
      (ae_restrict_of_forall_mem measurableSet_Ioi hW)
  refine ⟨hint, ?_⟩
  calc ∫ y in Ioi (0 : ℝ), ‖((y : ℝ) : ℂ) ^ (w - 7 / 4) * aMode ν ρ j y‖
      ≤ ∫ y in Ioi (0 : ℝ), R * Real.sqrt (2 * π) * (y ^ (σ - 7 / 4) * Real.exp (-A * y)) :=
        setIntegral_mono_on hint.norm (hmaj.const_mul _) measurableSet_Ioi hW
    _ = R * Real.sqrt (2 * π) * ((1 / A) ^ (σ - 3 / 4) * Real.Gamma (σ - 3 / 4)) := by
        rw [integral_const_mul]
        have := Real.integral_rpow_mul_exp_neg_mul_Ioi (a := σ - 3 / 4) (r := A) (by linarith) hA
        rw [show σ - 3 / 4 - 1 = σ - 7 / 4 by ring] at this
        simp_rw [show ∀ y : ℝ, -A * y = -(A * y) by intro y; ring]
        rw [this]
    _ = _ := by
        have hj2 : (j : ℝ) ^ 2 = |(j : ℝ)| ^ (2 : ℝ) := by
          rw [Real.rpow_two, sq_abs]
        rw [one_div, Real.inv_rpow hA.le, ← Real.rpow_neg hA.le]
        simp only [A]
        rw [Real.mul_rpow (by positivity) (sq_nonneg _), hj2, ← Real.rpow_mul (abs_nonneg _)]
        rw [show -(σ - 3 / 4) = 3 / 4 - σ by ring, show (2 : ℝ) * (3 / 4 - σ) = -(2 * σ - 3 / 2) by ring]
        ring

include hg hρ0 hρ in
/-- **The Shimura strip integral** for `Re w > 7/4`:
`∫_{strip} G(z) y^w dμ = (Σ_j ρ_W(j²)(8πj²)^{3/4−w}) Mel_ν(w − ¼)`. -/
theorem strip_integral {w : ℂ} (hw : 7 / 4 < w.re) :
    ∫ z in HTGeometry.modularStrip, kernel g z * ((z.im : ℝ) : ℂ) ^ w =
      (∑' j : ℤ, zCoef ρ w j) * melC (BlackHoleRingdown.CuspL.nu lam) (w - 1 / 4) := by
  obtain ⟨C, hC0, hC⟩ := BlackHoleRingdown.CuspL.exists_coeff_bound hg hρ0 hρ
  have hR := norm_rW_le hC
  have hw34 : 3 / 4 < w.re := by linarith
  have hw14 : 1 / 4 < w.re := by linarith
  rw [HTGeometry.setIntegral_modularStrip_eq_iterated _ (integrableOn_kernel_strip hg hw)]
  have e : ∀ y ∈ Ioi (0 : ℝ), (y ^ 2)⁻¹ • ∫ x in Ico (0 : ℝ) 1,
      kernel g (ofComplex ⟨x, y⟩) * (((ofComplex (⟨x, y⟩ : ℂ)).im : ℝ) : ℂ) ^ w =
      ∑' j : ℤ, ((y : ℝ) : ℂ) ^ (w - 7 / 4) * aMode (BlackHoleRingdown.CuspL.nu lam) ρ j y := by
    intro y hy
    have hy0 : 0 < y := hy
    have him : ∀ x : ℝ, (ofComplex (⟨x, y⟩ : ℂ)).im = y := fun x => by
      rw [UpperHalfPlane.im, ofComplex_mk hy0]
    simp_rw [him]
    have h := inner_integral hg hρ0 hρ w hy0
    rw [integral_div] at h
    rw [tsum_mul_left, ← h, Complex.real_smul, div_eq_inv_mul]
    push_cast; ring
  rw [setIntegral_congr_fun measurableSet_Ioi e,
    ← integral_tsum_of_summable_integral_norm (fun j => (integral_norm_aMode_le hR j hw34).1)]
  · simp_rw [integral_aMode _ hw14]
    exact tsum_mul_right
  · refine Summable.of_nonneg_of_le (fun j => integral_nonneg fun _ => norm_nonneg _)
      (fun j => (integral_norm_aMode_le hR j hw34).2) ?_
    exact (Real.summable_abs_int_rpow (b := 2 * w.re - 3 / 2) (by linarith)).mul_left _

include hg hρ0 hρ in
/-- **Unfolding Shimura's integral**, `Re w > 7/4`: `rsFold(G)(w) = 2 ρ(w) Mel_ν(w − ¼) Σ_j ρ_W(j²)(8πj²)^{3/4−w}`. -/
theorem fold_eq {w : ℂ} (hw : 7 / 4 < w.re) :
    rsFold 1 (kernel g) w =
      2 * regF w * ((∑' j : ℤ, zCoef ρ w j) * melC (BlackHoleRingdown.CuspL.nu lam) (w - 1 / 4)) := by
  rw [rsFold_eq 1 (fun γ hγ z => kernel_smul hg hγ z) (by linarith) (integrableOn_kernel_strip hg hw),
    strip_integral hg hρ0 hρ hw]

end Series

end GaloisForLFunctions.ArithmeticHolographyOfTheModularHorizon.Shimura
