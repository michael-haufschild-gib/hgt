import GaloisForLFunctions.RHTower.DirichletEvenThetaAxisKernel

/-!
# Weil positivity and the conductor of a real quadratic character

Let `χ` be an even real primitive Dirichlet character of conductor `q > 1`, the character of a
real quadratic field.  For `t ∈ ℝ` consider the prime weights `Λ(n)(1 - t + tχ(n))` in the
finite-atom Weil symbol of `ζ`.  The archimedean part stays that of `ζ`.

* **Explicit formula in symbol form** (`integral_weilAtomSymbol_dirichlet`).  For a `C²` test `f`
  supported in `[-a, a]`, `∫ |h_f|² S_{Λχ} = 2π Re W_χ(f) - log q ∫ |h_f|²`, where `W_χ` is the
  zero side of `L(s, χ)`.  For an even character the archimedean symbol of `L(s, χ)` is that of
  `ζ` shifted by the constant `log q`.
* **Exact energy** (`integral_weilAtomSymbol_dirichletMix`).  For a polar-constrained test,
  `∫ |h_f|² S_{Λ(1-t+tχ)} = 2π(1-t) Re W_ζ(f) + t (2π Re W_χ(f) - log q ∫ |h_f|²)`.
* **Double radical tests.**
  - The axis kernel `Φ_χ` of the theta series of `χ` has transform `q^s Λ(s, χ)` with
    `s = ½ + iz` and decays faster than every exponential, so its truncations `Φ_{χ,≤L}` are
    uniformly close to a function in the radical of `L(s, χ)`.
  - The test `g_R = f_R ⋆ Φ_{χ,≤4R}` is built from the truncated radical test `f_R` of `ζ`.
    Both zero sides of `g_R` are `O(R e^{-R/2})` (`exists_norm_W_zeta_dirichletTest_le`,
    `exists_norm_W_dirichlet_dirichletTest_le`).
  - `∫ |h_{g_R}|²` stays bounded below (`exists_integral_normSq_dirichletTest_ge`): the limit
    transform `Φ̂ κ̂₂ Φ̂_χ` is entire and nonzero at `z = -3i/4`, so it does not vanish
    identically on `ℝ`.
* **Theorem** (`dirichletMix_weilAtomSymbol_not_nonneg`).  For every `t > 0` some
  polar-constrained test has negative symbol energy.  At `t = 1/2` the weights are `Λ` on the
  split primes of the real quadratic field and their powers, with half weight on the ramified
  primes; the inert primes are deleted with their odd powers.  The defect is `t log q ∫ |h|²`.
-/

open Complex MeasureTheory Real Set Filter Topology
open scoped ComplexConjugate

noncomputable section
namespace RHTower

open Zeta23

local notation "Φ" => riemannPhiKernel

/-! ### Truncations of a decaying kernel -/

/-- The kernel on `[-L, L]`. -/
def kernelCore (K : ℝ → ℂ) (L : ℝ) : ℝ → ℂ := (Icc (-L) L).indicator K

/-- The kernel beyond `|u| > L`. -/
def kernelTail (K : ℝ → ℂ) (L : ℝ) : ℝ → ℂ := {u : ℝ | L < |u|}.indicator K

section KernelTruncation

variable {K : ℝ → ℂ}

theorem kernelCore_add_kernelTail (K : ℝ → ℂ) (L u : ℝ) :
    kernelCore K L u + kernelTail K L u = K u := by
  unfold kernelCore kernelTail indicator
  by_cases h : L < |u|
  · have : u ∉ Icc (-L) L := fun hm => by have := abs_le.mpr ⟨hm.1, hm.2⟩; linarith
    simp [h, this]
  · push Not at h
    have : u ∈ Icc (-L) L := ⟨(abs_le.mp h).1, (abs_le.mp h).2⟩
    simp [this, not_lt.mpr h]

theorem norm_kernelCore_le (K : ℝ → ℂ) (L u : ℝ) : ‖kernelCore K L u‖ ≤ ‖K u‖ := by
  unfold kernelCore indicator; split_ifs <;> simp

theorem norm_kernelTail_le (K : ℝ → ℂ) (L u : ℝ) : ‖kernelTail K L u‖ ≤ ‖K u‖ := by
  unfold kernelTail indicator; split_ifs <;> simp

theorem integrable_kernelCore_mul_exp (hK : Continuous K) (L : ℝ) (z : ℂ) :
    Integrable (fun u : ℝ => kernelCore K L u * Complex.exp (I * z * u)) := by
  have : (fun u : ℝ => kernelCore K L u * Complex.exp (I * z * u)) =
      (Icc (-L) L).indicator (fun u : ℝ => K u * Complex.exp (I * z * u)) := by
    funext u; unfold kernelCore indicator; split_ifs <;> simp
  rw [this]
  exact ((hK.mul (by fun_prop)).integrableOn_Icc).integrable_indicator measurableSet_Icc

theorem integrable_kernelCore (hK : Continuous K) (L : ℝ) : Integrable (kernelCore K L) := by
  have h := integrable_kernelCore_mul_exp hK L 0
  simpa using h

theorem aestronglyMeasurable_kernelCore (hK : Continuous K) (L : ℝ) :
    AEStronglyMeasurable (kernelCore K L) volume :=
  hK.aestronglyMeasurable.indicator measurableSet_Icc

theorem aestronglyMeasurable_kernelTail (hK : Continuous K) (L : ℝ) :
    AEStronglyMeasurable (kernelTail K L) volume :=
  hK.aestronglyMeasurable.indicator (isOpen_lt continuous_const continuous_abs).measurableSet

variable {C : ℝ}

theorem integrable_norm_kernel_mul_exp_half (hK : Continuous K)
    (hD : ∀ u, ‖K u‖ ≤ C * Real.exp (-|u|)) :
    Integrable (fun u : ℝ => ‖K u‖ * Real.exp (1 / 2 * |u|)) := by
  refine Integrable.mono' ((integrable_exp_neg_mul_abs_modSource (a := 1 / 2)
    (by norm_num)).const_mul C) (hK.norm.mul (by fun_prop)).aestronglyMeasurable
    (Eventually.of_forall fun u => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  calc ‖K u‖ * Real.exp (1 / 2 * |u|) ≤ C * Real.exp (-|u|) * Real.exp (1 / 2 * |u|) :=
        mul_le_mul_of_nonneg_right (hD u) (Real.exp_pos _).le
    _ = C * Real.exp (-(1 / 2) * |u|) := by rw [mul_assoc, ← Real.exp_add]; congr 2; ring

theorem integrable_kernel_mul_exp (hK : Continuous K) (hD : ∀ u, ‖K u‖ ≤ C * Real.exp (-|u|))
    {z : ℂ} (hz : |z.im| ≤ 1 / 2) :
    Integrable (fun u : ℝ => K u * Complex.exp (I * z * u)) := by
  refine Integrable.mono' (integrable_norm_kernel_mul_exp_half hK hD)
    ((hK.mul (by fun_prop)).aestronglyMeasurable) (Eventually.of_forall fun u => ?_)
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_left (norm_cexp_I_mul_le_exp hz u) (norm_nonneg _)

theorem integrable_kernelTail_mul_exp (hK : Continuous K)
    (hD : ∀ u, ‖K u‖ ≤ C * Real.exp (-|u|)) (L : ℝ) {z : ℂ} (hz : |z.im| ≤ 1 / 2) :
    Integrable (fun u : ℝ => kernelTail K L u * Complex.exp (I * z * u)) := by
  have h := (integrable_kernel_mul_exp hK hD hz).sub (integrable_kernelCore_mul_exp hK L z)
  refine h.congr (Eventually.of_forall fun u => ?_)
  simp only [Pi.sub_apply]
  rw [← kernelCore_add_kernelTail K L u]; ring

theorem paperFT_kernelCore_eq (hK : Continuous K) (hD : ∀ u, ‖K u‖ ≤ C * Real.exp (-|u|))
    (L : ℝ) {z : ℂ} (hz : |z.im| ≤ 1 / 2) :
    paperFT (kernelCore K L) z = paperFT K z - paperFT (kernelTail K L) z := by
  unfold paperFT
  rw [← integral_sub (integrable_kernel_mul_exp hK hD hz)
    (integrable_kernelTail_mul_exp hK hD L hz)]
  congr 1; funext u
  rw [← kernelCore_add_kernelTail K L u]; ring

/-- Strip bound for a measurable function dominated by the kernel. -/
theorem norm_paperFT_le_of_norm_le_kernel (hK : Continuous K)
    (hD : ∀ u, ‖K u‖ ≤ C * Real.exp (-|u|)) {g : ℝ → ℂ} (hgm : AEStronglyMeasurable g volume)
    (hg : ∀ u, ‖g u‖ ≤ ‖K u‖) {z : ℂ} (hz : |z.im| ≤ 1 / 2) :
    ‖paperFT g z‖ ≤ ∫ u : ℝ, ‖g u‖ * Real.exp (1 / 2 * |u|) := by
  unfold paperFT
  refine (norm_integral_le_integral_norm _).trans (integral_mono_of_nonneg
    (Eventually.of_forall fun u => norm_nonneg _) ?_ (Eventually.of_forall fun u => ?_))
  · refine Integrable.mono' (integrable_norm_kernel_mul_exp_half hK hD)
      (hgm.norm.mul (by fun_prop : Continuous fun u : ℝ => Real.exp (1 / 2 * |u|)).aestronglyMeasurable)
      (Eventually.of_forall fun u => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact mul_le_mul_of_nonneg_right (hg u) (Real.exp_pos _).le
  · simp only
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left (norm_cexp_I_mul_le_exp hz u) (norm_nonneg _)

theorem norm_paperFT_kernelCore_le (hK : Continuous K) (hD : ∀ u, ‖K u‖ ≤ C * Real.exp (-|u|))
    (L : ℝ) {z : ℂ} (hz : |z.im| ≤ 1 / 2) :
    ‖paperFT (kernelCore K L) z‖ ≤ ∫ u : ℝ, ‖K u‖ * Real.exp (1 / 2 * |u|) := by
  refine (norm_paperFT_le_of_norm_le_kernel hK hD (aestronglyMeasurable_kernelCore hK L)
    (norm_kernelCore_le K L) hz).trans (integral_mono_of_nonneg
      (Eventually.of_forall fun u => by positivity) (integrable_norm_kernel_mul_exp_half hK hD)
      (Eventually.of_forall fun u => ?_))
  exact mul_le_mul_of_nonneg_right (norm_kernelCore_le K L u) (Real.exp_pos _).le

theorem norm_paperFT_kernelTail_le (hK : Continuous K) (hD : ∀ u, ‖K u‖ ≤ C * Real.exp (-|u|))
    (L : ℝ) {z : ℂ} (hz : |z.im| ≤ 1 / 2) :
    ‖paperFT (kernelTail K L) z‖ ≤ ∫ u : ℝ, ‖kernelTail K L u‖ * Real.exp (1 / 2 * |u|) :=
  norm_paperFT_le_of_norm_le_kernel hK hD (aestronglyMeasurable_kernelTail hK L)
    (norm_kernelTail_le K L) hz

/-- **Tail bound.**  `∫_{|u| > L} |K(u)| e^{|u|/2} du ≤ C' e^{-L/4}`. -/
theorem exists_integral_kernelTail_le (hC : 0 ≤ C) (hD : ∀ u, ‖K u‖ ≤ C * Real.exp (-|u|)) :
    ∃ C' : ℝ, 0 ≤ C' ∧ ∀ L : ℝ, 0 ≤ L →
      ∫ u : ℝ, ‖kernelTail K L u‖ * Real.exp (1 / 2 * |u|) ≤ C' * Real.exp (-(L / 4)) := by
  have hint := integrable_exp_neg_mul_abs_modSource (a := 1 / 4) (by norm_num)
  refine ⟨C * ∫ u : ℝ, Real.exp (-(1 / 4) * |u|), mul_nonneg hC
    (integral_nonneg fun _ => (Real.exp_pos _).le), fun L hL => ?_⟩
  have hpt : ∀ u, ‖kernelTail K L u‖ * Real.exp (1 / 2 * |u|) ≤
      Real.exp (-(L / 4)) * (C * Real.exp (-(1 / 4) * |u|)) := by
    intro u
    unfold kernelTail indicator
    split_ifs with h
    · have h' : L < |u| := h
      calc ‖K u‖ * Real.exp (1 / 2 * |u|) ≤ C * Real.exp (-|u|) * Real.exp (1 / 2 * |u|) :=
            mul_le_mul_of_nonneg_right (hD u) (Real.exp_pos _).le
        _ = C * Real.exp (-(1 / 2) * |u|) := by
            rw [mul_assoc, ← Real.exp_add]; congr 2; ring
        _ ≤ C * (Real.exp (-(L / 4)) * Real.exp (-(1 / 4) * |u|)) := by
            gcongr
            rw [← Real.exp_add]; apply Real.exp_le_exp.mpr; linarith
        _ = Real.exp (-(L / 4)) * (C * Real.exp (-(1 / 4) * |u|)) := by ring
    · simp only [norm_zero, zero_mul]; positivity
  calc ∫ u : ℝ, ‖kernelTail K L u‖ * Real.exp (1 / 2 * |u|)
      ≤ ∫ u : ℝ, Real.exp (-(L / 4)) * (C * Real.exp (-(1 / 4) * |u|)) :=
        integral_mono_of_nonneg (Eventually.of_forall fun u => by positivity)
          ((hint.const_mul C).const_mul _) (Eventually.of_forall hpt)
    _ = C * (∫ u : ℝ, Real.exp (-(1 / 4) * |u|)) * Real.exp (-(L / 4)) := by
        rw [integral_const_mul, integral_const_mul]; ring

end KernelTruncation

/-! ### The explicit formula of `L(s, χ)` in symbol form -/

variable {q : ℕ} [NeZero q]

/-- The zeros of `L(s, χ)` in the critical strip, with multiplicities. -/
def dirichletZeros (hq : 1 < q) {χ : DirichletCharacter ℂ q} (hprim : χ.IsPrimitive) :
    ZeroConfig :=
  Zeta23.ThmE.LZeros (Zeta23.ThmE.LSeam_of hq hprim)

omit [NeZero q] in
theorem parity_of_even {χ : DirichletCharacter ℂ q} (heven : χ.Even) :
    Zeta23.ThmE.parity χ = 0 := by
  unfold Zeta23.ThmE.parity; rw [if_pos heven]

omit [NeZero q] in
theorem coeff_of_real {χ : DirichletCharacter ℂ q} (hreal : ∀ a : ZMod q, (χ a).im = 0) (n : ℕ) :
    Zeta23.ThmE.coeff χ n = (((χ (n : ZMod q)).re : ℝ) : ℂ) := by
  unfold Zeta23.ThmE.coeff
  apply Complex.ext <;> simp [hreal]

theorem archimedeanWeilSymbol_div_conductor (Q : ℕ) (hQ : 0 < Q) (τ : ℝ) :
    archimedeanWeilSymbol (τ / (2 * π)) =
      (Complex.digamma (1 / 4 + ((0 : ℕ) : ℂ) / 2 + I * τ / 2)).re +
        Real.log ((Q : ℝ) / π) - Real.log Q := by
  rw [archimedeanWeilSymbol_eq, Real.log_div (by exact_mod_cast hQ.ne') Real.pi_ne_zero]
  have : ((1 / 4 : ℝ) : ℂ) + ((π * (τ / (2 * π)) : ℝ) : ℂ) * I =
      1 / 4 + ((0 : ℕ) : ℂ) / 2 + I * τ / 2 := by
    have hπ : (π : ℝ) ≠ 0 := Real.pi_ne_zero
    rw [show π * (τ / (2 * π)) = τ / 2 by field_simp]
    push_cast; ring
  rw [this]; ring

/-- **Twisted Weil energy = `L(s, χ)` zero side minus the conductor.**  For an even real primitive
character `χ` mod `q > 1` and a `C²` test supported in `[-a, a]`,
`∫ |h_f|² S_{Λχ} = 2π Re W_χ(f) - log q ∫ |h_f|²`. -/
theorem integral_weilAtomSymbol_dirichlet (hq : 1 < q) {χ : DirichletCharacter ℂ q}
    (hprim : χ.IsPrimitive) (heven : χ.Even) (hreal : ∀ a : ZMod q, (χ a).im = 0)
    {a : ℝ} (ha : 0 ≤ a) {f : ℝ → ℂ} (hf : ContDiff ℝ 2 f) (hfs : tsupport f ⊆ Icc (-a) a) :
    ∫ τ : ℝ, ‖paperFT f τ‖ ^ 2 * weilAtomSymbol
        (fun n => ArithmeticFunction.vonMangoldt n * (χ (n : ZMod q)).re)
        ⌊Real.exp (2 * a)⌋₊ (τ / (2 * π)) =
      2 * π * ((dirichletZeros hq hprim).W f f).re - Real.log q * ∫ τ : ℝ, ‖paperFT f τ‖ ^ 2 := by
  obtain ⟨hfc, hkd, hks, hki, hFk⟩ := weilTest_self_data hf hfs
  set k := EF.weilTest f f with hk
  set N := ⌊Real.exp (2 * a)⌋₊ with hN
  obtain ⟨-, hEF⟩ := Zeta23.ThmE.EF_lit_chi_L (q := q) (χ := χ) hq hprim k hkd
    (EF.hasCompactSupport_of_tsupport_subset hks)
  have hW : (dirichletZeros hq hprim).W f f = ∑' ρ : (dirichletZeros hq hprim).carrier,
      ((dirichletZeros hq hprim).mult ρ : ℂ) * paperFT k (gammaOf ρ) := by
    unfold ZeroConfig.W
    congr 1; funext ρ
    simp only [ZeroConfig.Wsummand, hk, EF.paperFT_weilTest hf.continuous hf.continuous hfc hfc,
      mul_assoc]
  have hk0 : ∀ y : ℝ, 2 * a < |y| → k y = 0 := fun y hy =>
    image_eq_zero_of_notMem_tsupport fun hmem => by
      have := hks hmem
      have : |y| ≤ 2 * a := abs_le.mpr ⟨this.1, this.2⟩
      linarith
  have hprime : ∑' n : ℕ, ((ArithmeticFunction.vonMangoldt n / Real.sqrt n : ℝ) : ℂ) *
      (Zeta23.ThmE.coeff χ n * k (Real.log n) +
        (starRingEnd ℂ) (Zeta23.ThmE.coeff χ n) * k (-Real.log n)) =
      ∑ n ∈ Finset.Icc 2 N, ((ArithmeticFunction.vonMangoldt n / Real.sqrt n *
        (χ (n : ZMod q)).re : ℝ) : ℂ) * (k (Real.log n) + k (-Real.log n)) := by
    rw [tsum_eq_sum (s := Finset.Icc 2 N)]
    · refine Finset.sum_congr rfl fun n _ => ?_
      rw [coeff_of_real hreal, Complex.conj_ofReal]; push_cast; ring
    · intro n hn
      rw [Finset.mem_Icc, not_and_or] at hn
      rcases hn with hn | hn
      · have : n = 0 ∨ n = 1 := by omega
        rcases this with rfl | rfl <;> simp
      · push Not at hn
        have hexp : Real.exp (2 * a) < n := (Nat.floor_lt (Real.exp_pos _).le).mp hn
        have hlog : 2 * a < Real.log n := by
          rw [← Real.log_exp (2 * a)]; exact Real.log_lt_log (Real.exp_pos _) hexp
        have hl0 : 0 ≤ Real.log n := le_trans (by linarith) hlog.le
        rw [hk0 _ (by rw [abs_of_nonneg hl0]; exact hlog),
          hk0 _ (by rw [abs_neg, abs_of_nonneg hl0]; exact hlog)]
        simp
  have hq0 : 0 < q := by omega
  have harch : ∫ r : ℝ, paperFT k r * ((((Complex.digamma (1 / 4 + ((0 : ℕ) : ℂ) / 2 +
      I * r / 2)).re + Real.log ((q : ℝ) / π) : ℝ)) : ℂ) =
      ((∫ r : ℝ, ‖paperFT f r‖ ^ 2 * (archimedeanWeilSymbol (r / (2 * π)) + Real.log q) : ℝ) :
        ℂ) := by
    rw [← integral_complex_ofReal]
    congr 1; funext r
    rw [hk, paperFT_weilTest_self_ofReal hf.continuous hfc, archimedeanWeilSymbol_div_conductor q hq0]
    push_cast; ring
  have hEF' : ∑' ρ : (dirichletZeros hq hprim).carrier,
      ((dirichletZeros hq hprim).mult ρ : ℂ) * paperFT k (gammaOf ρ) =
      Zeta23.ThmE.literatureRHSchi (Zeta23.ThmE.parity χ) q (Zeta23.ThmE.coeff χ) k := hEF
  clear hEF
  rw [← hW, Zeta23.ThmE.literatureRHSchi, parity_of_even heven, hprime, harch] at hEF'
  have hEF := hEF'
  have hre := congrArg Complex.re hEF
  simp only [Complex.add_re, Complex.neg_re, Complex.re_sum, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, sub_zero] at hre
  have hdiv : ((1 / (2 * π) : ℂ)).re = 1 / (2 * π) := by
    rw [show (1 / (2 * π) : ℂ) = ((1 / (2 * π) : ℝ) : ℂ) by push_cast; ring, Complex.ofReal_re]
  have hdivim : ((1 / (2 * π) : ℂ)).im = 0 := by
    rw [show (1 / (2 * π) : ℂ) = ((1 / (2 * π) : ℝ) : ℂ) by push_cast; ring, Complex.ofReal_im]
  rw [hdiv, hdivim, zero_mul, sub_zero] at hre
  rw [integral_weilAtomSymbol_eq_arch_sub hf hfs]
  have hI2 : ∫ r : ℝ, ‖paperFT f r‖ ^ 2 * (archimedeanWeilSymbol (r / (2 * π)) + Real.log q) =
      (∫ r : ℝ, ‖paperFT f r‖ ^ 2 * archimedeanWeilSymbol (r / (2 * π))) +
        Real.log q * ∫ r : ℝ, ‖paperFT f r‖ ^ 2 := by
    rw [← integral_const_mul, ← integral_add (integrable_normSq_paperFT_mul_arch hf hfs)
      ((integrable_normSq_paperFT hf hfs).const_mul _)]
    congr 1; funext r; ring
  rw [hI2] at hre
  have hsum : ∑ n ∈ Finset.Icc 2 N, (ArithmeticFunction.vonMangoldt n * (χ (n : ZMod q)).re) /
      Real.sqrt n * (k (Real.log n) + k (-Real.log n)).re =
      ∑ n ∈ Finset.Icc 2 N, (ArithmeticFunction.vonMangoldt n / Real.sqrt n *
        (χ (n : ZMod q)).re) * (k (Real.log n) + k (-Real.log n)).re :=
    Finset.sum_congr rfl fun n _ => by ring
  rw [hsum]
  have hπ : (0 : ℝ) < π := Real.pi_pos
  field_simp at hre ⊢
  simp only [Complex.add_re] at hre ⊢
  linarith

/-! ### The double radical test for `ζ` and `L(s, χ)` -/

theorem exists_dirichletAxisKernel_decay (hq : 1 < q) {χ : DirichletCharacter ℂ q} (hχ : χ ≠ 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ u : ℝ, ‖dirichletAxisKernel χ u‖ ≤ C * Real.exp (-|u|) := by
  obtain ⟨C, hC0, hC⟩ := exists_norm_dirichletAxisKernel_le hq hχ (B := 1) (by norm_num)
  exact ⟨C, hC0, fun u => by simpa using hC u⟩

/-- `g_R = f_R ⋆ Φ_{χ, ≤4R}`: radical for both `ζ` and `L(s, χ)` up to truncation. -/
def dirichletTest (χ : DirichletCharacter ℂ q) (R : ℝ) : ℝ → ℂ :=
  convolution (weilRadicalTest R) (kernelCore (dirichletAxisKernel χ) (4 * R))
    (ContinuousLinearMap.mul ℝ ℂ) volume

theorem contDiff_dirichletTest (χ : DirichletCharacter ℂ q) (R : ℝ) :
    ContDiff ℝ 2 (dirichletTest χ R) :=
  (hasCompactSupport_weilRadicalTest R).contDiff_convolution_left (ContinuousLinearMap.mul ℝ ℂ)
    (n := 2) (contDiff_weilRadicalTest R)
    (integrable_kernelCore (continuous_dirichletAxisKernel χ) _).locallyIntegrable

theorem dirichletTest_eq_zero (χ : DirichletCharacter ℂ q) {R x : ℝ} (hx : 5 * R < |x|) :
    dirichletTest χ R x = 0 := by
  unfold dirichletTest
  rw [convolution_def]
  have : ∀ t : ℝ, (ContinuousLinearMap.mul ℝ ℂ) (weilRadicalTest R t)
      (kernelCore (dirichletAxisKernel χ) (4 * R) (x - t)) = 0 := by
    intro t
    simp only [ContinuousLinearMap.mul_apply']
    by_cases ht : R < |t|
    · rw [weilRadicalTest_eq_zero ht, zero_mul]
    · push Not at ht
      have hxt : 4 * R < |x - t| := by have := abs_sub_abs_le_abs_sub x t; linarith
      have : x - t ∉ Icc (-(4 * R)) (4 * R) := fun hm => by
        have := abs_le.mpr ⟨hm.1, hm.2⟩; linarith
      simp [kernelCore, indicator, this]
  simp [this]

theorem tsupport_dirichletTest (χ : DirichletCharacter ℂ q) (R : ℝ) :
    tsupport (dirichletTest χ R) ⊆ Icc (-(5 * R)) (5 * R) := by
  apply closure_minimal _ isClosed_Icc
  intro x hx
  have h : ¬ 5 * R < |x| := fun h => hx (dirichletTest_eq_zero χ h)
  push Not at h
  exact ⟨(abs_le.mp h).1, (abs_le.mp h).2⟩

theorem paperFT_dirichletTest (χ : DirichletCharacter ℂ q) (R : ℝ) (z : ℂ) :
    paperFT (dirichletTest χ R) z =
      paperFT (weilRadicalTest R) z * paperFT (kernelCore (dirichletAxisKernel χ) (4 * R)) z :=
  paperFT_convolution
    (((contDiff_weilRadicalTest R).continuous.mul (by fun_prop)).integrable_of_hasCompactSupport
      (hasCompactSupport_weilRadicalTest R).mul_right)
    (integrable_kernelCore_mul_exp (continuous_dirichletAxisKernel χ) _ z)

theorem paperFT_dirichletTest_half_I (χ : DirichletCharacter ℂ q) (R : ℝ) :
    paperFT (dirichletTest χ R) (I / 2) = 0 := by
  rw [paperFT_dirichletTest, paperFT_weilRadicalTest_half_I, zero_mul]

theorem paperFT_dirichletTest_neg_half_I (χ : DirichletCharacter ℂ q) (R : ℝ) :
    paperFT (dirichletTest χ R) (-(I / 2)) = 0 := by
  rw [paperFT_dirichletTest, paperFT_weilRadicalTest_neg_half_I, zero_mul]

theorem summable_dirichletZeros (hq : 1 < q) {χ : DirichletCharacter ℂ q} (hprim : χ.IsPrimitive) :
    Summable (fun ρ : (dirichletZeros hq hprim).carrier =>
      ((dirichletZeros hq hprim).mult ρ : ℝ) / (1 + Complex.normSq (gammaOf ρ))) := by
  obtain ⟨A₀, hA₀, hloc⟩ := Zeta23.ThmE.localCountChi hq hprim
  refine WeilEF.zero_sum_inv_sq_gen (dirichletZeros hq hprim) hA₀ fun t => ?_
  have := Zeta23.ThmE.LZeros_N (Zeta23.ThmE.LSeam_of hq hprim) t (t + 1)
  simpa [dirichletZeros, this] using hloc t

/-- The radical decay factor: `‖B̂_R(conj γ)‖ ≤ e^{R/2} R K₀ (1+|Im ρ|)^{-2}` in the strip. -/
theorem norm_paperFT_weilRadicalTest_conj_le {K₀ : ℝ}
    (hK : ∀ L : ℝ, 0 ≤ L →
      4 * ((∫ u : ℝ, ‖weilRadicalTest L u‖) + ∫ u : ℝ, ‖deriv (deriv (weilRadicalTest L)) u‖)
        ≤ L * K₀)
    {R : ℝ} (hR : 0 ≤ R) {ρ : ℂ} (hIm : |(gammaOf ρ).im| ≤ 1 / 2) :
    ‖paperFT (weilRadicalTest R) ((starRingEnd ℂ) (gammaOf ρ))‖ ≤
      Real.exp (R / 2) * (R * K₀) * (1 / (1 + |ρ.im|) ^ 2) := by
  have hIm' : |((starRingEnd ℂ) (gammaOf ρ)).im| ≤ 1 / 2 := by
    rw [Complex.conj_im, abs_neg]; exact hIm
  have h := norm_paperFT_le_decay (contDiff_weilRadicalTest R)
    (fun u hu => by by_contra h; push Not at h; exact hu (weilRadicalTest_eq_zero h))
    ((starRingEnd ℂ) (gammaOf ρ))
  have hre : ((starRingEnd ℂ) (gammaOf ρ)).re = ρ.im := by
    rw [Complex.conj_re, WeilEF.gammaOf_re]
  rw [hre] at h
  refine h.trans ?_
  have he : Real.exp (|((starRingEnd ℂ) (gammaOf ρ)).im| * R) ≤ Real.exp (R / 2) :=
    Real.exp_le_exp.mpr (by nlinarith)
  have hden : 0 < (1 + |ρ.im|) ^ 2 := by positivity
  rw [div_eq_mul_one_div, mul_assoc]
  rw [show Real.exp (R / 2) * (R * K₀) * (1 / (1 + |ρ.im|) ^ 2) =
    Real.exp (R / 2) * (R * K₀ * (1 / (1 + |ρ.im|) ^ 2)) by ring]
  exact mul_le_mul he (mul_le_mul_of_nonneg_right (hK R hR) (by positivity))
    (by positivity) (Real.exp_pos _).le

/-- **The `ζ` zero side of the double radical test decays** like `R e^{-R/2}`. -/
theorem exists_norm_W_zeta_dirichletTest_le (hq : 1 < q) {χ : DirichletCharacter ℂ q}
    (hχ : χ ≠ 1) : ∃ K : ℝ, 0 ≤ K ∧ ∀ R : ℝ, 1 ≤ R →
      ‖zetaZeroConfig.W (dirichletTest χ R) (dirichletTest χ R)‖ ≤
        K * (R * Real.exp (-(R / 2))) := by
  obtain ⟨Cχ, hCχ0, hCχ⟩ := exists_dirichletAxisKernel_decay hq hχ
  have hKc := continuous_dirichletAxisKernel χ
  obtain ⟨K₀, hK₀, hK⟩ := exists_weilRadicalTest_norms_le
  obtain ⟨C₆, hC₆0, hC₆⟩ := exists_superexp_le 6
  set E₀ := 40 * jacobiThetaTailConstant * Real.exp π / (6 * π - 6) with hE₀
  have hE0 : 0 ≤ E₀ := by
    have hM : 0 ≤ jacobiThetaTailConstant := jacobiThetaTailConstant_nonneg
    have hc : 0 < 6 * π - 6 := by nlinarith [Real.pi_gt_three]
    rw [hE₀]; positivity
  set A := Real.exp (3 / 4) * ∫ u : ℝ, ‖weilBumpPolarFree u‖ with hA
  have hA0 : 0 ≤ A := mul_nonneg (Real.exp_pos _).le (integral_nonneg fun _ => norm_nonneg _)
  set Bχ := ∫ u : ℝ, ‖dirichletAxisKernel χ u‖ * Real.exp (1 / 2 * |u|) with hBχ
  have hBχ0 : 0 ≤ Bχ := integral_nonneg fun _ => by positivity
  set SZ := ∑' ρ : zetaZeroConfig.carrier,
    (zetaZeroConfig.mult ρ : ℝ) / (1 + Complex.normSq (gammaOf ρ)) with hSZ
  have hSZ0 : 0 ≤ SZ := tsum_nonneg fun ρ => div_nonneg (Nat.cast_nonneg _)
    (by have := Complex.normSq_nonneg (gammaOf (ρ : ℂ)); linarith)
  refine ⟨5 / 4 * SZ * (E₀ * C₆ * Real.exp (1 / 4) * A * Bχ * (K₀ * Bχ)), by positivity,
    fun R hR => ?_⟩
  have hR0 : 0 ≤ R := by linarith
  set ε := ∫ u : ℝ, ‖riemannPhiTail R u‖ * Real.exp (1 / 2 * |u|) with hε
  have hε0 : 0 ≤ ε := integral_nonneg fun _ => by positivity
  have hεle : ε ≤ E₀ * C₆ * Real.exp (-(R - 1 / 4)) :=
    riemannPhiTail_bound_le E₀ C₆ hE₀ hC₆ hR (by norm_num)
  have h := norm_zeroConfig_W_le_of_pointwise zetaZeroConfig summable_zetaZeroConfig
    (f := dirichletTest χ R) (P := ε * A * Bχ) (Q := Real.exp (R / 2) * (R * K₀) * Bχ)
    (by positivity) (by positivity) ?_ ?_
  · rw [← hSZ] at h
    refine h.trans ?_
    have hexp : Real.exp (-(R - 1 / 4)) * Real.exp (R / 2) =
        Real.exp (1 / 4) * Real.exp (-(R / 2)) := by
      rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring
    calc 5 / 4 * SZ * (ε * A * Bχ * (Real.exp (R / 2) * (R * K₀) * Bχ))
        ≤ 5 / 4 * SZ * ((E₀ * C₆ * Real.exp (-(R - 1 / 4))) * A * Bχ *
            (Real.exp (R / 2) * (R * K₀) * Bχ)) := by gcongr
      _ = 5 / 4 * SZ * (E₀ * C₆ * A * Bχ * (K₀ * Bχ)) * R *
            (Real.exp (-(R - 1 / 4)) * Real.exp (R / 2)) := by ring
      _ = _ := by rw [hexp]; ring
  · intro ρ
    have hmem := ρ.2
    have hstrip' : 0 < (ρ : ℂ).re ∧ (ρ : ℂ).re < 1 := by
      have h : IsNontrivialZero (ρ : ℂ) := hmem
      exact ⟨h.2.1, h.2.2⟩
    have hIm : |(gammaOf (ρ : ℂ)).im| ≤ 1 / 2 := (WeilEF.abs_gammaOf_im_lt hstrip').le
    obtain ⟨hc1, -⟩ := paperFT_riemannPhiCore_at_zero hmem R
    rw [paperFT_dirichletTest, norm_mul, paperFT_weilRadicalTest, hc1, norm_mul, norm_neg]
    exact mul_le_mul (mul_le_mul (norm_paperFT_riemannPhiTail_le (by norm_num) hIm)
      (norm_paperFT_weilBumpPolarFree_le (by linarith)) (norm_nonneg _) hε0)
      (norm_paperFT_kernelCore_le hKc hCχ _ hIm) (norm_nonneg _) (by positivity)
  · intro ρ
    have hmem := ρ.2
    have hstrip' : 0 < (ρ : ℂ).re ∧ (ρ : ℂ).re < 1 := by
      have h : IsNontrivialZero (ρ : ℂ) := hmem
      exact ⟨h.2.1, h.2.2⟩
    have hIm : |(gammaOf (ρ : ℂ)).im| ≤ 1 / 2 := (WeilEF.abs_gammaOf_im_lt hstrip').le
    have hIm' : |((starRingEnd ℂ) (gammaOf (ρ : ℂ))).im| ≤ 1 / 2 := by
      rw [Complex.conj_im, abs_neg]; exact hIm
    rw [paperFT_dirichletTest, norm_mul]
    calc ‖paperFT (weilRadicalTest R) ((starRingEnd ℂ) (gammaOf ρ))‖ *
          ‖paperFT (kernelCore (dirichletAxisKernel χ) (4 * R)) ((starRingEnd ℂ) (gammaOf ρ))‖
        ≤ (Real.exp (R / 2) * (R * K₀) * (1 / (1 + |(ρ : ℂ).im|) ^ 2)) * Bχ :=
          mul_le_mul (norm_paperFT_weilRadicalTest_conj_le hK hR0 hIm)
            (norm_paperFT_kernelCore_le hKc hCχ _ hIm') (norm_nonneg _) (by positivity)
      _ = Real.exp (R / 2) * (R * K₀) * Bχ * (1 / (1 + |(ρ : ℂ).im|) ^ 2) := by ring

/-- **The `L(s, χ)` zero side of the double radical test decays** like `R e^{-R/2}`. -/
theorem exists_norm_W_dirichlet_dirichletTest_le (hq : 1 < q) {χ : DirichletCharacter ℂ q}
    (hχ : χ ≠ 1) (heven : χ.Even) (hprim : χ.IsPrimitive) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ R : ℝ, 1 ≤ R →
      ‖(dirichletZeros hq hprim).W (dirichletTest χ R) (dirichletTest χ R)‖ ≤
        K * (R * Real.exp (-(R / 2))) := by
  obtain ⟨Cχ, hCχ0, hCχ⟩ := exists_dirichletAxisKernel_decay hq hχ
  have hKc := continuous_dirichletAxisKernel χ
  obtain ⟨K₀, hK₀, hK⟩ := exists_weilRadicalTest_norms_le
  obtain ⟨Ct, hCt0, hCt⟩ := exists_integral_kernelTail_le hCχ0 hCχ
  set A := Real.exp (3 / 4) * ∫ u : ℝ, ‖weilBumpPolarFree u‖ with hA
  have hA0 : 0 ≤ A := mul_nonneg (Real.exp_pos _).le (integral_nonneg fun _ => norm_nonneg _)
  set Bχ := ∫ u : ℝ, ‖dirichletAxisKernel χ u‖ * Real.exp (1 / 2 * |u|) with hBχ
  have hBχ0 : 0 ≤ Bχ := integral_nonneg fun _ => by positivity
  set BΦ := ∫ u : ℝ, ‖Φ u‖ * Real.exp (1 / 2 * |u|) with hBΦ
  have hBΦ0 : 0 ≤ BΦ := integral_nonneg fun _ => by positivity
  set S₈ := ∑' ρ : (dirichletZeros hq hprim).carrier,
    ((dirichletZeros hq hprim).mult ρ : ℝ) / (1 + Complex.normSq (gammaOf ρ)) with hS₈
  have hS₈0 : 0 ≤ S₈ := tsum_nonneg fun ρ => div_nonneg (Nat.cast_nonneg _)
    (by have := Complex.normSq_nonneg (gammaOf (ρ : ℂ)); linarith)
  refine ⟨5 / 4 * S₈ * (BΦ * A * Ct * (K₀ * Bχ)), by positivity, fun R hR => ?_⟩
  have hR0 : 0 ≤ R := by linarith
  have htail : ∫ u : ℝ, ‖kernelTail (dirichletAxisKernel χ) (4 * R) u‖ *
      Real.exp (1 / 2 * |u|) ≤ Ct * Real.exp (-R) := by
    have := hCt (4 * R) (by linarith)
    rwa [show 4 * R / 4 = R by ring] at this
  have hstripOf : ∀ ρ : (dirichletZeros hq hprim).carrier,
      0 < (ρ : ℂ).re ∧ (ρ : ℂ).re < 1 := fun ρ => by
    have h : Zeta23.ThmE.IsNontrivialZeroL χ (ρ : ℂ) := ρ.2
    exact ⟨h.2.1, h.2.2⟩
  have h := norm_zeroConfig_W_le_of_pointwise (dirichletZeros hq hprim)
    (summable_dirichletZeros hq hprim)
    (f := dirichletTest χ R) (P := BΦ * A * (Ct * Real.exp (-R)))
    (Q := Real.exp (R / 2) * (R * K₀) * Bχ) (by positivity) (by positivity) ?_ ?_
  · rw [← hS₈] at h
    refine h.trans (le_of_eq ?_)
    have hexp : Real.exp (-R) * Real.exp (R / 2) = Real.exp (-(R / 2)) := by
      rw [← Real.exp_add]; congr 1; ring
    calc 5 / 4 * S₈ * (BΦ * A * (Ct * Real.exp (-R)) * (Real.exp (R / 2) * (R * K₀) * Bχ))
        = 5 / 4 * S₈ * (BΦ * A * Ct * (K₀ * Bχ)) * R * (Real.exp (-R) * Real.exp (R / 2)) := by
          ring
      _ = _ := by rw [hexp]; ring
  · intro ρ
    have hIm : |(gammaOf (ρ : ℂ)).im| ≤ 1 / 2 := (WeilEF.abs_gammaOf_im_lt (hstripOf ρ)).le
    have hzero : paperFT (dirichletAxisKernel χ) (gammaOf ρ) = 0 :=
      paperFT_dirichletAxisKernel_gammaOf_eq_zero hq hχ heven ρ.2
    rw [paperFT_dirichletTest, norm_mul, paperFT_weilRadicalTest, norm_mul,
      paperFT_kernelCore_eq hKc hCχ _ hIm, hzero, zero_sub, norm_neg]
    refine mul_le_mul (mul_le_mul (norm_paperFT_riemannPhiCore_le R hIm)
      (norm_paperFT_weilBumpPolarFree_le (by linarith)) (norm_nonneg _) hBΦ0)
      ((norm_paperFT_kernelTail_le hKc hCχ _ hIm).trans htail) (norm_nonneg _) (by positivity)
  · intro ρ
    have hIm : |(gammaOf (ρ : ℂ)).im| ≤ 1 / 2 := (WeilEF.abs_gammaOf_im_lt (hstripOf ρ)).le
    have hIm' : |((starRingEnd ℂ) (gammaOf (ρ : ℂ))).im| ≤ 1 / 2 := by
      rw [Complex.conj_im, abs_neg]; exact hIm
    rw [paperFT_dirichletTest, norm_mul]
    calc ‖paperFT (weilRadicalTest R) ((starRingEnd ℂ) (gammaOf ρ))‖ *
          ‖paperFT (kernelCore (dirichletAxisKernel χ) (4 * R)) ((starRingEnd ℂ) (gammaOf ρ))‖
        ≤ (Real.exp (R / 2) * (R * K₀) * (1 / (1 + |(ρ : ℂ).im|) ^ 2)) * Bχ :=
          mul_le_mul (norm_paperFT_weilRadicalTest_conj_le hK hR0 hIm)
            (norm_paperFT_kernelCore_le hKc hCχ _ hIm') (norm_nonneg _) (by positivity)
      _ = Real.exp (R / 2) * (R * K₀) * Bχ * (1 / (1 + |(ρ : ℂ).im|) ^ 2) := by ring

/-! ### The limit transform and its mass on the real line -/

/-- The limit transform `G_χ(z) = Φ̂(z) κ̂₂(z) Φ̂_χ(z)` of the double radical tests. -/
def dirichletLimit (χ : DirichletCharacter ℂ q) (z : ℂ) : ℂ :=
  radicalLimit z * paperFT (dirichletAxisKernel χ) z

theorem differentiable_dirichletLimit (hq : 1 < q) {χ : DirichletCharacter ℂ q} (hχ : χ ≠ 1) :
    Differentiable ℂ (dirichletLimit χ) :=
  differentiable_radicalLimit.mul (superExpDecay_dirichletAxisKernel hq hχ).differentiable_paperFT

theorem dirichletLimit_ne_zero (hq : 1 < q) {χ : DirichletCharacter ℂ q} (hχ : χ ≠ 1)
    (heven : χ.Even) : dirichletLimit χ (-(3 / 4 * I)) ≠ 0 := by
  have h := conductorLimit_ne_zero
  unfold conductorLimit at h
  unfold dirichletLimit radicalLimit
  exact mul_ne_zero (left_ne_zero_of_mul h) (paperFT_dirichletAxisKernel_ne_zero hq hχ heven)

/-- The limit transform does not vanish identically on the real line. -/
theorem exists_real_dirichletLimit_ne_zero (hq : 1 < q) {χ : DirichletCharacter ℂ q}
    (hχ : χ ≠ 1) (heven : χ.Even) : ∃ τ₀ : ℝ, dirichletLimit χ τ₀ ≠ 0 := by
  by_contra h
  push Not at h
  have han : AnalyticOnNhd ℂ (dirichletLimit χ) univ :=
    (differentiable_dirichletLimit hq hχ).differentiableOn.analyticOnNhd isOpen_univ
  have hfreq : ∃ᶠ z in 𝓝[≠] (0 : ℂ), dirichletLimit χ z = 0 := by
    have htend : Tendsto (fun t : ℝ => (t : ℂ)) (𝓝[≠] (0 : ℝ)) (𝓝[≠] (0 : ℂ)) := by
      refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _
        ((Complex.continuous_ofReal.tendsto' 0 0 (by simp)).mono_left nhdsWithin_le_nhds) ?_
      filter_upwards [self_mem_nhdsWithin] with t ht
      simpa using ht
    exact htend.frequently (Eventually.frequently (Eventually.of_forall fun t => h t))
  have hzero := han.eqOn_zero_of_preconnected_of_frequently_eq_zero isPreconnected_univ
    (mem_univ 0) hfreq
  exact dirichletLimit_ne_zero hq hχ heven (hzero (mem_univ _))

/-- On the real line the double radical tests converge uniformly to the limit transform. -/
theorem exists_norm_paperFT_dirichletTest_sub_le (hq : 1 < q) {χ : DirichletCharacter ℂ q}
    (hχ : χ ≠ 1) : ∃ K : ℝ, 0 ≤ K ∧ ∀ R : ℝ, 1 ≤ R → ∀ τ : ℝ,
      ‖paperFT (dirichletTest χ R) τ - dirichletLimit χ τ‖ ≤ K * Real.exp (-R) := by
  obtain ⟨Cχ, hCχ0, hCχ⟩ := exists_dirichletAxisKernel_decay hq hχ
  have hKc := continuous_dirichletAxisKernel χ
  obtain ⟨C₆, hC₆0, hC₆⟩ := exists_superexp_le 6
  obtain ⟨Ct, hCt0, hCt⟩ := exists_integral_kernelTail_le hCχ0 hCχ
  set E₀ := 40 * jacobiThetaTailConstant * Real.exp π / (6 * π - 6) with hE₀
  have hE0 : 0 ≤ E₀ := by
    have hM : 0 ≤ jacobiThetaTailConstant := jacobiThetaTailConstant_nonneg
    have hc : 0 < 6 * π - 6 := by nlinarith [Real.pi_gt_three]
    rw [hE₀]; positivity
  set A := Real.exp (3 / 4) * ∫ u : ℝ, ‖weilBumpPolarFree u‖ with hA
  have hA0 : 0 ≤ A := mul_nonneg (Real.exp_pos _).le (integral_nonneg fun _ => norm_nonneg _)
  set Bχ := ∫ u : ℝ, ‖dirichletAxisKernel χ u‖ * Real.exp (1 / 2 * |u|) with hBχ
  have hBχ0 : 0 ≤ Bχ := integral_nonneg fun _ => by positivity
  set BΦ := ∫ u : ℝ, ‖Φ u‖ * Real.exp (1 / 2 * |u|) with hBΦ
  have hBΦ0 : 0 ≤ BΦ := integral_nonneg fun _ => by positivity
  refine ⟨A * (BΦ * Ct + E₀ * C₆ * Real.exp (1 / 4) * Bχ), by positivity, fun R hR τ => ?_⟩
  have hR0 : 0 ≤ R := by linarith
  have hτ : |((τ : ℂ)).im| ≤ 1 / 2 := by simp
  set Tχ := paperFT (kernelTail (dirichletAxisKernel χ) (4 * R)) τ with hTχ
  set Tζ := paperFT (riemannPhiTail R) τ with hTζ
  have hTχb : ‖Tχ‖ ≤ Ct * Real.exp (-R) := by
    refine (norm_paperFT_kernelTail_le hKc hCχ _ hτ).trans ?_
    have := hCt (4 * R) (by linarith)
    rwa [show 4 * R / 4 = R by ring] at this
  have hTζb : ‖Tζ‖ ≤ E₀ * C₆ * Real.exp (1 / 4) * Real.exp (-R) := by
    refine (norm_paperFT_riemannPhiTail_le (by norm_num) hτ).trans
      ((riemannPhiTail_bound_le E₀ C₆ hE₀ hC₆ hR (by norm_num)).trans (le_of_eq ?_))
    rw [mul_assoc (E₀ * C₆), ← Real.exp_add]; congr 2; ring
  have hK : ‖paperFT (dirichletAxisKernel χ) τ‖ ≤ Bχ :=
    norm_paperFT_le_of_norm_le_kernel hKc hCχ hKc.aestronglyMeasurable (fun u => le_rfl) hτ
  have hcoreζ : ‖paperFT (riemannPhiCore R) τ‖ ≤ BΦ := norm_paperFT_riemannPhiCore_le R hτ
  have hκ : ‖paperFT weilBumpPolarFree τ‖ ≤ A :=
    norm_paperFT_weilBumpPolarFree_le (by simp only [Complex.ofReal_im, abs_zero]; norm_num)
  have hΦ : paperFT Φ τ = paperFT (riemannPhiCore R) τ + Tζ := by
    rw [paperFT_riemannPhiCore_eq, paperFT_riemannPhiKernel]; ring
  have hdiff : paperFT (dirichletTest χ R) τ - dirichletLimit χ τ =
      -(paperFT weilBumpPolarFree τ * (paperFT (riemannPhiCore R) τ * Tχ +
        Tζ * paperFT (dirichletAxisKernel χ) τ)) := by
    unfold dirichletLimit radicalLimit
    rw [paperFT_dirichletTest, paperFT_weilRadicalTest, paperFT_kernelCore_eq hKc hCχ _ hτ, hΦ]
    ring
  rw [hdiff, norm_neg, norm_mul]
  calc ‖paperFT weilBumpPolarFree τ‖ * ‖paperFT (riemannPhiCore R) τ * Tχ +
        Tζ * paperFT (dirichletAxisKernel χ) τ‖
      ≤ A * (BΦ * (Ct * Real.exp (-R)) + E₀ * C₆ * Real.exp (1 / 4) * Real.exp (-R) * Bχ) := by
        refine mul_le_mul hκ ((norm_add_le _ _).trans ?_) (norm_nonneg _) hA0
        rw [norm_mul, norm_mul]
        exact add_le_add (mul_le_mul hcoreζ hTχb (norm_nonneg _) hBΦ0)
          (mul_le_mul hTζb hK (norm_nonneg _) (by positivity))
    _ = A * (BΦ * Ct + E₀ * C₆ * Real.exp (1 / 4) * Bχ) * Real.exp (-R) := by ring

/-- **Mass of the double radical tests.**  `∫ |h_{g_R}|² ≥ c > 0` for all large `R`. -/
theorem exists_integral_normSq_dirichletTest_ge (hq : 1 < q) {χ : DirichletCharacter ℂ q}
    (hχ : χ ≠ 1) (heven : χ.Even) : ∃ c R₀ : ℝ, 0 < c ∧ 1 ≤ R₀ ∧
      ∀ R : ℝ, R₀ ≤ R → c ≤ ∫ τ : ℝ, ‖paperFT (dirichletTest χ R) τ‖ ^ 2 := by
  obtain ⟨τ₀, hτ₀⟩ := exists_real_dirichletLimit_ne_zero hq hχ heven
  obtain ⟨K, hK0, hK⟩ := exists_norm_paperFT_dirichletTest_sub_le hq hχ
  set m := ‖dirichletLimit χ τ₀‖ with hm
  have hm0 : 0 < m := norm_pos_iff.mpr hτ₀
  have hcont : ContinuousAt (fun τ : ℝ => dirichletLimit χ τ) τ₀ :=
    ((differentiable_dirichletLimit hq hχ).continuous.comp Complex.continuous_ofReal).continuousAt
  obtain ⟨η, hη0, hη⟩ := Metric.continuousAt_iff.mp hcont (m / 2) (by linarith)
  have hev : ∀ᶠ R in atTop, K * Real.exp (-R) ≤ m / 4 := by
    have ht : Tendsto (fun R : ℝ => K * Real.exp (-R)) atTop (𝓝 0) := by
      simpa using Real.tendsto_exp_neg_atTop_nhds_zero.const_mul K
    exact ht.eventually (ge_mem_nhds (by linarith))
  obtain ⟨R₁, hR₁⟩ := hev.exists_forall_of_atTop
  refine ⟨η * (m / 4) ^ 2, max R₁ 1, by positivity, le_max_right _ _, fun R hR => ?_⟩
  have hR1 : 1 ≤ R := le_trans (le_max_right _ _) hR
  have herr := hR₁ R (le_trans (le_max_left _ _) hR)
  have hlow : ∀ τ ∈ Icc (τ₀ - η / 2) (τ₀ + η / 2),
      (m / 4) ^ 2 ≤ ‖paperFT (dirichletTest χ R) τ‖ ^ 2 := by
    intro τ hτ
    have hd : dist τ τ₀ < η := by
      rw [Real.dist_eq, abs_lt]; constructor <;> linarith [hτ.1, hτ.2]
    have h1 := hη hd
    rw [dist_eq_norm] at h1
    have h2 : m / 2 ≤ ‖dirichletLimit χ τ‖ := by
      have := norm_sub_norm_le (dirichletLimit χ τ₀) (dirichletLimit χ τ)
      rw [norm_sub_rev] at h1
      linarith
    have h3 := (hK R hR1 τ).trans herr
    have h4 : m / 4 ≤ ‖paperFT (dirichletTest χ R) τ‖ := by
      have := norm_sub_norm_le (dirichletLimit χ τ) (paperFT (dirichletTest χ R) τ)
      rw [norm_sub_rev] at h3
      linarith
    exact pow_le_pow_left₀ (by positivity) h4 2
  have hint := integrable_normSq_paperFT (contDiff_dirichletTest χ R) (tsupport_dirichletTest χ R)
  calc η * (m / 4) ^ 2 = ∫ τ in Icc (τ₀ - η / 2) (τ₀ + η / 2), (m / 4) ^ 2 := by
        rw [setIntegral_const]
        simp only [Measure.real, Real.volume_Icc, smul_eq_mul]
        rw [ENNReal.toReal_ofReal (by linarith)]; ring
    _ ≤ ∫ τ in Icc (τ₀ - η / 2) (τ₀ + η / 2), ‖paperFT (dirichletTest χ R) τ‖ ^ 2 :=
        setIntegral_mono_on (integrableOn_const (by simp) (by simp)) hint.integrableOn
          measurableSet_Icc hlow
    _ ≤ ∫ τ : ℝ, ‖paperFT (dirichletTest χ R) τ‖ ^ 2 :=
        setIntegral_le_integral hint (Eventually.of_forall fun _ => by positivity)

/-! ### Tilting the von Mangoldt weights towards a quadratic character -/

omit [NeZero q] in
/-- The weights `Λ(n)(1 - t + tχ(n))` interpolate affinely between `Λ` and `Λχ`. -/
theorem weilAtomSymbol_dirichletMix (χ : DirichletCharacter ℂ q) (t : ℝ) (N : ℕ) (ξ : ℝ) :
    weilAtomSymbol (fun n => ArithmeticFunction.vonMangoldt n *
        (1 - t + t * (χ (n : ZMod q)).re)) N ξ =
      (1 - t) * weilAtomSymbol (fun n => (ArithmeticFunction.vonMangoldt n : ℝ)) N ξ +
        t * weilAtomSymbol (fun n => ArithmeticFunction.vonMangoldt n * (χ (n : ZMod q)).re)
          N ξ := by
  unfold weilAtomSymbol
  have hs : ∑ n ∈ Finset.Icc 2 N, ArithmeticFunction.vonMangoldt n *
      (1 - t + t * (χ (n : ZMod q)).re) *
      (1 / Real.sqrt n) * (2 * Real.cos (2 * π * Real.log n * ξ)) =
      (1 - t) * ∑ n ∈ Finset.Icc 2 N, (ArithmeticFunction.vonMangoldt n : ℝ) *
        (1 / Real.sqrt n) * (2 * Real.cos (2 * π * Real.log n * ξ)) +
      t * ∑ n ∈ Finset.Icc 2 N, ArithmeticFunction.vonMangoldt n * (χ (n : ZMod q)).re *
        (1 / Real.sqrt n) * (2 * Real.cos (2 * π * Real.log n * ξ)) := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun n _ => by ring
  rw [hs]; ring

/-- **Exact energy of the tilted weights.**  For an even real primitive character `χ` mod `q > 1`
and a polar-constrained level-`a` test,
`∫ |h_f|² S_{Λ(1-t+tχ)} = 2π(1-t) Re W_ζ(f) + t (2π Re W_χ(f) - log q ∫ |h_f|²)`. -/
theorem integral_weilAtomSymbol_dirichletMix (hq : 1 < q) {χ : DirichletCharacter ℂ q}
    (hprim : χ.IsPrimitive) (heven : χ.Even) (hreal : ∀ a : ZMod q, (χ a).im = 0)
    {a : ℝ} (ha : 0 ≤ a) {f : ℝ → ℂ}
    (hf : ContDiff ℝ 2 f) (hfs : tsupport f ⊆ Icc (-a) a) (hp : paperFT f (I / 2) = 0)
    (hm : paperFT f (-(I / 2)) = 0) (t : ℝ) :
    ∫ τ : ℝ, ‖paperFT f τ‖ ^ 2 * weilAtomSymbol
        (fun n => ArithmeticFunction.vonMangoldt n * (1 - t + t * (χ (n : ZMod q)).re))
        ⌊Real.exp (2 * a)⌋₊ (τ / (2 * π)) =
      2 * π * (1 - t) * (zetaZeroConfig.W f f).re +
        t * (2 * π * ((dirichletZeros hq hprim).W f f).re -
          Real.log q * ∫ τ : ℝ, ‖paperFT f τ‖ ^ 2) := by
  have hΛ := integrable_normSq_paperFT_mul_weilAtomSymbol hf hfs
  have hχ := integrable_normSq_paperFT_mul_weilAtomSymbol_of hf hfs
    (fun n => ArithmeticFunction.vonMangoldt n * (χ (n : ZMod q)).re)
  have hpt : ∀ τ : ℝ, ‖paperFT f τ‖ ^ 2 * weilAtomSymbol
      (fun n => ArithmeticFunction.vonMangoldt n * (1 - t + t * (χ (n : ZMod q)).re))
      ⌊Real.exp (2 * a)⌋₊ (τ / (2 * π)) =
      (1 - t) * (‖paperFT f τ‖ ^ 2 * weilAtomSymbol
        (fun n => (ArithmeticFunction.vonMangoldt n : ℝ)) ⌊Real.exp (2 * a)⌋₊ (τ / (2 * π))) +
      t * (‖paperFT f τ‖ ^ 2 * weilAtomSymbol
        (fun n => ArithmeticFunction.vonMangoldt n * (χ (n : ZMod q)).re) ⌊Real.exp (2 * a)⌋₊
          (τ / (2 * π))) := by
    intro τ; rw [weilAtomSymbol_dirichletMix]; ring
  rw [integral_congr_ae (Eventually.of_forall hpt), integral_add (hΛ.const_mul _)
    (hχ.const_mul _), integral_const_mul, integral_const_mul,
    integral_weilAtomSymbol_dirichlet hq hprim heven hreal ha hf hfs]
  have hW := zeta_W_eq_integral_weilAtomSymbol_vonMangoldt hf hfs hp hm
  have hWre : (zetaZeroConfig.W f f).re = 1 / (2 * π) * ∫ τ : ℝ, ‖paperFT f τ‖ ^ 2 *
      weilAtomSymbol (fun n => (ArithmeticFunction.vonMangoldt n : ℝ)) ⌊Real.exp (2 * a)⌋₊
        (τ / (2 * π)) := by
    rw [hW, Complex.ofReal_re]
  rw [hWre]
  have hπ : (π : ℝ) ≠ 0 := Real.pi_ne_zero
  field_simp

omit [NeZero q] in
/-- A primitive character of modulus `q > 1` is not trivial. -/
theorem ne_one_of_isPrimitive [NeZero q] (hq : 1 < q) {χ : DirichletCharacter ℂ q}
    (hprim : χ.IsPrimitive) : χ ≠ 1 := by
  rintro rfl
  rw [DirichletCharacter.isPrimitive_def, DirichletCharacter.conductor_one] at hprim
  omega

/-- **Weil positivity fails when the von Mangoldt weights are tilted towards a real quadratic
character.**  Let `χ` be an even real primitive Dirichlet character of conductor `q > 1`.  For every
`t > 0` the weights `Λ(n)(1 - t + tχ(n))` give negative finite-atom Weil symbol energy on some
polar-constrained `C²` test.  At `t = 1/2` these are the von Mangoldt weights on the primes that
split in the real quadratic field of discriminant `q`, with half weight on the ramified primes.

On the tests `f_R ⋆ Φ_{χ, ≤4R}`, radical for both `ζ` and `L(s, χ)`, both zero sides are
`O(R e^{-R/2})` while `∫ |h|² ≥ c`, so the energy is `-t log q ∫ |h|² + o(1)`: the defect is the
logarithm of the conductor. -/
theorem dirichletMix_weilAtomSymbol_not_nonneg (hq : 1 < q) {χ : DirichletCharacter ℂ q}
    (hprim : χ.IsPrimitive) (heven : χ.Even) (hreal : ∀ a : ZMod q, (χ a).im = 0)
    {t : ℝ} (ht : 0 < t) :
    ∃ a : ℝ, 0 ≤ a ∧ ∃ f : ℝ → ℂ, ContDiff ℝ 2 f ∧ tsupport f ⊆ Icc (-a) a ∧
      paperFT f (I / 2) = 0 ∧ paperFT f (-(I / 2)) = 0 ∧
      ∫ τ : ℝ, ‖paperFT f τ‖ ^ 2 * weilAtomSymbol
        (fun n => ArithmeticFunction.vonMangoldt n * (1 - t + t * (χ (n : ZMod q)).re))
        ⌊Real.exp (2 * a)⌋₊ (τ / (2 * π)) < 0 := by
  have hχ := ne_one_of_isPrimitive hq hprim
  obtain ⟨c, R₀, hc, hR₀, hmass⟩ := exists_integral_normSq_dirichletTest_ge hq hχ heven
  obtain ⟨KW, hKW0, hKW⟩ := exists_norm_W_zeta_dirichletTest_le hq hχ
  obtain ⟨KL, hKL0, hKL⟩ := exists_norm_W_dirichlet_dirichletTest_le hq hχ heven hprim
  have hlogq : 0 < Real.log q := Real.log_pos (by exact_mod_cast hq)
  set M := 2 * π * |1 - t| * KW + 2 * π * t * KL with hM
  have hM0 : 0 ≤ M := by positivity
  have hlim : Tendsto (fun R : ℝ => M * (R * Real.exp (-(R / 2)))) atTop (𝓝 0) := by
    have h := (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 1).comp
      (tendsto_id.atTop_div_const (by norm_num : (0 : ℝ) < 2))
    have h2 := (h.const_mul 2).const_mul M
    simp only [mul_zero] at h2
    refine h2.congr fun R => ?_
    simp only [Function.comp_apply, id, pow_one]; ring
  obtain ⟨R, hRsmall, hRbig⟩ := ((hlim.eventually (gt_mem_nhds (by positivity :
    (0 : ℝ) < t * Real.log q * c))).and (eventually_ge_atTop R₀)).exists
  have hR1 : 1 ≤ R := hR₀.trans hRbig
  have hR0 : 0 ≤ R := by linarith
  refine ⟨5 * R, by linarith, dirichletTest χ R, contDiff_dirichletTest χ R,
    tsupport_dirichletTest χ R, paperFT_dirichletTest_half_I χ R,
    paperFT_dirichletTest_neg_half_I χ R, ?_⟩
  rw [integral_weilAtomSymbol_dirichletMix hq hprim heven hreal (by linarith)
    (contDiff_dirichletTest χ R) (tsupport_dirichletTest χ R) (paperFT_dirichletTest_half_I χ R)
    (paperFT_dirichletTest_neg_half_I χ R)]
  have hW1 : (1 - t) * (zetaZeroConfig.W (dirichletTest χ R) (dirichletTest χ R)).re ≤
      |1 - t| * (KW * (R * Real.exp (-(R / 2)))) := by
    refine (le_abs_self _).trans ?_
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left ((Complex.abs_re_le_norm _).trans (hKW R hR1))
      (abs_nonneg _)
  have hW2 : ((dirichletZeros hq hprim).W (dirichletTest χ R) (dirichletTest χ R)).re ≤
      KL * (R * Real.exp (-(R / 2))) :=
    (Complex.re_le_norm _).trans (hKL R hR1)
  have hm := hmass R hRbig
  have hπ : 0 < π := Real.pi_pos
  have key : 2 * π * (1 - t) * (zetaZeroConfig.W (dirichletTest χ R) (dirichletTest χ R)).re +
      t * (2 * π * ((dirichletZeros hq hprim).W (dirichletTest χ R) (dirichletTest χ R)).re) ≤
      M * (R * Real.exp (-(R / 2))) := by
    have h1 := mul_le_mul_of_nonneg_left hW1 (by positivity : (0 : ℝ) ≤ 2 * π)
    have h2 := mul_le_mul_of_nonneg_left hW2 (by positivity : (0 : ℝ) ≤ 2 * π * t)
    rw [hM]
    nlinarith
  have hcq : t * Real.log q * c ≤
      t * (Real.log q * ∫ τ : ℝ, ‖paperFT (dirichletTest χ R) τ‖ ^ 2) := by
    rw [mul_assoc]
    exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hm hlogq.le) ht.le
  nlinarith

end RHTower
